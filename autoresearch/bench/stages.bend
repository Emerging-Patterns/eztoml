# Stage profiler. Not part of the library metric: verify.sh archives without
# autoresearch/. Each stage's strict lets sit in their own def.
import ../../main.bend as Toml

# unwrap a parsed U32, or zero when parse fails
def u32.arg.go(mm: Maybe<&2, U32>) -> U32:
  match mm:
    case Some{n}:
      n
    case None{}:
      0

# parse a decimal U32 from a string
def u32.arg(ss: String) -> U32:
  u32.arg.go(U32.read(ss))

# close the file once the write Result is Unit
def wrote.close(file: File, ok: Unit) -> IO(Unit):
  match ok:
    case Unit{}:
      File.close(file)

# force a write Result, then close the file
def wrote(pair: File & Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  (file, result) = pair
  do IO<Unit>:
    ok : Unit <- IO.pass(Unit, result)
    wrote.close(file, ok)

# after reading text, close the file and return it
def took.after(text: String, closed: Unit) -> String:
  match closed:
    case Unit{}:
      text

# force a read Result, then close the file
def took.text(pair: File & Result<&1, &1, U32 & String, String>) -> IO(String):
  (file, result) = pair
  do IO<String>:
    text : String <- IO.pass(String, result)
    closed : Unit <- File.close(file)
    return took.after(text, closed)

# read n bytes of text after learning the file size
def read.n(pair: File & Result<&1, &1, U32 & String, U32>) -> IO(String):
  (file, result) = pair
  do IO<String>:
    n : U32 <- IO.pass(U32, result)
    p : File & Result<&1, &1, U32 & String, String> <- File.read(file, n)
    took.text(p)

# read a whole file as text
def read.file(path: String) -> IO(String):
  do IO<String>:
    f : File <- IO.try(File, File.open(path, "r"))
    p : File & Result<&1, &1, U32 & String, U32> <- File.size(f)
    read.n(p)

# fold character codes into a wrapping checksum
def text.sum.go(ss: String, +aa: U32) -> U32:
  match ss:
    case SNil{}:
      aa
    case SCon{h, t}:
      text.sum.go(t, ((aa * 131 : U32) + Char.to_u32(h) : U32))

# checksum of a string
def text.sum(ss: String) -> U32:
  text.sum.go(ss, 0)

# length of a string as U32
def text.len.go(ss: String, +nn: U32) -> U32:
  match ss:
    case SNil{}:
      nn
    case SCon{_h, t}:
      text.len.go(t, (nn + 1 : U32))

# U32 length of text
def text.len(ss: String) -> U32:
  text.len.go(ss, 0)

# which side of the tree the counter is walking
type Walk is Data:
  WList{vs: List<&2, Toml.Val>}
  WVal{vv: Toml.Val}

# one value or one list. @unsafe: the two shapes call each other.
@unsafe def nodes.walk(job: Walk) -> U32:
  match job:
    case WList{vs}:
      match vs:
        case []:
          0
        case h <> t:
          (nodes.walk(WVal{h}) + nodes.walk(WList{t}) : U32)
    case WVal{vv}:
      match vv:
        case Toml.VStr{text}:
          (1 + text.len(text) : U32)
        case Toml.VSpan{_src, n}:
          (1 + n : U32)
        case Toml.VInt{_sign, digits}:
          (1 + text.len(digits) : U32)
        case Toml.VFlo{_sign, text}:
          (1 + text.len(text) : U32)
        case Toml.VBool{_bit}:
          1
        case Toml.VWhen{_when}:
          1
        case Toml.VArr{items}:
          (1 + nodes.walk(WList{items}) : U32)
        case Toml.VInl{rows}:
          (1 + nodes.walk(WList{rows}) : U32)
        case Toml.VHead{path, rows}:
          (text.len(path) + nodes.walk(WList{rows}) : U32)
        case Toml.VAot{path, rows}:
          (text.len(path) + nodes.walk(WList{rows}) : U32)
        case Toml.VAots{path, elems}:
          (text.len(path) + nodes.walk(WList{elems}) : U32)
        case Toml.VPair{name, val}:
          (text.len(name) + nodes.walk(WVal{val}) : U32)

# bad-text length plus the tree, so parse cannot be skipped
def nodes.doc(+doc: Toml.Doc) -> U32:
  (text.len(Toml.bad(doc)) + nodes.walk(WList{Toml.root(doc)}) : U32)

# stderr line the outer timer stamps
def say(+name: String, +n: U32) -> IO(Unit):
  IO.print_err(name ++ " " ++ U32.show(n))

# render after parse has been forced
def stage.render(+doc: Toml.Doc) -> IO(Unit):
  +out = Toml.render(doc)
  +n = text.len(out)
  +sum = text.sum(out)
  do IO<Unit>:
    say("render", n)
    say("rsum", sum)

# parse, then render
def stage.parse(+text: String) -> IO(Unit):
  +doc = Toml.parse(text)
  +n = nodes.doc(doc)
  do IO<Unit>:
    say("parse", n)
    stage.render(doc)

# one file: load, then parse, then render. +text is used for the length and the parse
def cmd.stages.go(+text: String) -> IO(Unit):
  +n = text.len(text)
  do IO<Unit>:
    say("bytes", n)
    stage.parse(text)

# one file: load, then parse, then render
def cmd.stages(path: String) -> IO(Unit):
  do IO<Unit>:
    text : String <- read.file(path)
    cmd.stages.go(text)

# fold one parse into the node count
def step.parse(+sum: U32, +text: String) -> U32:
  (sum + nodes.doc(Toml.parse(text)) : U32)

# repeat parse n times, no render
def loop.parse(+text: String, nn: Nat, +sum: U32) -> U32:
  match nn:
    case 0n:
      sum
    case 1n+p:
      loop.parse(text, p, step.parse(sum, text))

# format a timing line
def show.ms(t0: Nat, t1: Nat, +sum: U32, +nn: U32) -> String:
  "MS " ++ Nat.show(Nat.sub(t1, t0)) ++ " SUM " ++ U32.show(sum) ++ " N " ++ U32.show(nn)

# timed parse-only body
def parse.only.after(+text: String, +nn: U32, +kk: Nat) -> IO(Unit):
  do IO<Unit>:
    t0 : Nat <- IO.now()
    sum : U32 = loop.parse(text, kk, 0)
    t1 : Nat <- IO.now()
    IO.print(show.ms(t0, t1, sum, nn))

# timed parse with no render
def cmd.parse.only(path: String, +nn: U32) -> IO(Unit):
  +k = U32.to_nat(nn)
  do IO<Unit>:
    text : String <- read.file(path)
    parse.only.after(text, nn, k)

# die with a message
def die.msg(msg: String) -> IO(Unit):
  IO.die(Unit, 1, msg)

# dispatch parse-only
def run.b.at(zz: Bool, +cmd: String, +aa: String, +bb: String) -> IO(Unit):
  match zz:
    case True{}:
      cmd.parse.only(aa, u32.arg(bb))
    case False{}:
      die.msg("unknown command " ++ cmd)

# try parse-only then fall through
def run.b(+cmd: String, +aa: String, +bb: String) -> IO(Unit):
  run.b.at(String.eq(cmd, "parse-only"), cmd, aa, bb)

# dispatch stages
def run.a.at(zz: Bool, +cmd: String, +aa: String, +bb: String) -> IO(Unit):
  match zz:
    case True{}:
      cmd.stages(aa)
    case False{}:
      run.b(cmd, aa, bb)

# try stages then fall through
def run.a(+cmd: String, +aa: String, +bb: String) -> IO(Unit):
  run.a.at(String.eq(cmd, "stages"), cmd, aa, bb)

# the first three argv strings, empty when missing
def args3(xs: List<String>) -> String & String & String:
  match xs:
    case a <> b <> c <> _t:
      (a, b, c)
    case a <> b <> Nil{}:
      (a, b, "")
    case a <> Nil{}:
      (a, "", "")
    case Nil{}:
      ("", "", "")

# unpack argv and run the named command
def main.go(tri: String & String & String) -> IO(Unit):
  (a, b, c) = tri
  run.a(a, b, c)

# CLI entry
def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    main.go(args3(args))
