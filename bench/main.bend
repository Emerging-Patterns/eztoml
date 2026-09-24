# eztoml vs Rust toml crate bench driver. Native ELF via `bend bench/main.bend`.
# Timed path: load (and for render, parse) outside IO.now; loop only the codec.
import ../eztoml/main.bend as Toml

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
def wrote(pair: File & Result<&1, &1, U32 & String, Unit>) -> IO(Unit):  # noqa: L001 bench harness, outside the spec
  (file, result) = pair
  do IO<Unit>:
    ok : Unit <- IO.pass(Unit, result)
    wrote.close(file, ok)

# write a string to a path
def write.file(path: String, data: String) -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open(path, "w"))
    p : File & Result<&1, &1, U32 & String, Unit> <- File.write(f, data)
    wrote(p)

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

# die with a message
def die.msg(msg: String) -> IO(Unit):
  IO.die(Unit, 1, msg)

# fold character codes into a wrapping checksum
def text.sum.go(ss: String, +aa: U32) -> U32:
  match ss:
    case SNil{}:
      aa
    case SCon{h, t}:
      text.sum.go(t, ((aa * 131 : U32) + Char.to_u32(h) : U32))

# checksum of a string (keeps timed loops from being deleted)
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

# print BAD line for a document (empty why means well-formed)
def show.bad(+doc: Toml.Doc) -> String:
  "BAD " ++ Toml.bad(doc)

# print OK line with checksum of the rendered document
def show.ok(+doc: Toml.Doc) -> String:
  +out = Toml.render(doc)
  "OK SUM " ++ U32.show(text.sum(out)) ++ " BYTES " ++ U32.show(text.len(out))

# choose OK or BAD once emptiness is known
def show.doc.at(ok: Bool, +doc: Toml.Doc) -> String:
  match ok:
    case True{}:
      show.ok(doc)
    case False{}:
      show.bad(doc)

# status line for a parsed document
def show.doc(+doc: Toml.Doc) -> String:
  show.doc.at(String.is_empty(Toml.bad(doc)), doc)

# write when the document is well-formed; else die
def write.render.at(ok: Bool, +path: String, +doc: Toml.Doc) -> IO(Unit):
  match ok:
    case False{}:
      die.msg(Toml.bad(doc))
    case True{}:
      write.file(path, Toml.render(doc))

# write rendered document, or die on the first error
def write.render(+path: String, +doc: Toml.Doc) -> IO(Unit):
  write.render.at(String.is_empty(Toml.bad(doc)), path, doc)

# parse a TOML file and print OK/BAD status
def cmd.parse(src: String) -> IO(Unit):
  do IO<Unit>:
    text : String <- read.file(src)
    IO.print(show.doc(Toml.parse(text)))

# parse a TOML file and write the rendered form
def cmd.render(src: String, dst: String) -> IO(Unit):
  do IO<Unit>:
    text : String <- read.file(src)
    write.render(dst, Toml.parse(text))

# parse then render (eztoml round-trip into dst)
def cmd.rt(src: String, dst: String) -> IO(Unit):
  cmd.render(src, dst)

# fold a well-formed or rejected parse into the checksum
def step.parse.at(ok: Bool, +sum: U32, +doc: Toml.Doc) -> U32:
  match ok:
    case False{}:
      (sum + 1 : U32)
    case True{}:
      (sum + text.len(Toml.render(doc)) : U32)

# fold one parse into a checksum of the rendered length
def step.parse(+sum: U32, +text: String) -> U32:
  +doc = Toml.parse(text)
  step.parse.at(String.is_empty(Toml.bad(doc)), sum, doc)

# repeat parse n times
def loop.parse(+text: String, nn: Nat, +sum: U32) -> U32:
  match nn:
    case 0n:
      sum
    case 1n+p:
      loop.parse(text, p, step.parse(sum, text))

# fold one render into a checksum of its length
def step.render(+sum: U32, +doc: Toml.Doc) -> U32:
  (sum + text.len(Toml.render(doc)) : U32)

# repeat render n times
def loop.render(+doc: Toml.Doc, nn: Nat, +sum: U32) -> U32:
  match nn:
    case 0n:
      sum
    case 1n+p:
      loop.render(doc, p, step.render(sum, doc))

# format a timing line for the harness
def show.ms(t0: Nat, t1: Nat, +sum: U32, +bytes: U32, +nn: U32) -> String:
  "MS " ++ Nat.show(Nat.sub(t1, t0)) ++ " SUM " ++ U32.show(sum) ++ " N " ++ U32.show(nn)
    ++ " BYTES " ++ U32.show(bytes)

# timed parse body once the file text is loaded
def bench.parse.after(+text: String, +nn: U32, +kk: Nat) -> IO(Unit):
  +bytes = text.len(text)
  do IO<Unit>:
    t0 : Nat <- IO.now()
    sum : U32 = loop.parse(text, kk, 0)
    t1 : Nat <- IO.now()
    IO.print(show.ms(t0, t1, sum, bytes, nn))

# timed parse bench: load outside IO.now; loop only parse(+render checksum)
def bench.parse(path: String, +nn: U32) -> IO(Unit):
  +k = U32.to_nat(nn)
  do IO<Unit>:
    text : String <- read.file(path)
    bench.parse.after(text, nn, k)

# time render when the document is well-formed; else die
def bench.render.at(ok: Bool, +doc: Toml.Doc, +bytes: U32, +nn: U32) -> IO(Unit):
  match ok:
    case False{}:
      die.msg(Toml.bad(doc))
    case True{}:
      +k = U32.to_nat(nn)
      do IO<Unit>:
        t0 : Nat <- IO.now()
        sum : U32 = loop.render(doc, k, 0)
        t1 : Nat <- IO.now()
        IO.print(show.ms(t0, t1, sum, bytes, nn))

# timed render bench: load+parse outside IO.now; loop only render
def bench.render.go(+doc: Toml.Doc, +bytes: U32, +nn: U32) -> IO(Unit):
  bench.render.at(String.is_empty(Toml.bad(doc)), doc, bytes, nn)

# after loading text, parse then time render
def bench.render.after(+text: String, +nn: U32) -> IO(Unit):
  bench.render.go(Toml.parse(text), text.len(text), nn)

# load+parse then time render only
def bench.render(path: String, +nn: U32) -> IO(Unit):
  do IO<Unit>:
    text : String <- read.file(path)
    bench.render.after(text, nn)

# fallthrough for unknown commands
def run.e.at(zz: Bool, +cmd: String, _a: String, _b: String, _c: String) -> IO(Unit):
  match zz:
    case True{}:
      IO.print("pong")
    case False{}:
      die.msg("unknown command " ++ cmd)

# dispatch the ping command
def run.e(+cmd: String, +aa: String, +bb: String, +cc: String) -> IO(Unit):
  run.e.at(String.eq(cmd, "ping"), cmd, aa, bb, cc)

# dispatch bench-render
def run.d.at(zz: Bool, +cmd: String, +aa: String, +bb: String, +cc: String) -> IO(Unit):
  match zz:
    case True{}:
      bench.render(aa, u32.arg(bb))
    case False{}:
      run.e(cmd, aa, bb, cc)

# try bench-render then fall through
def run.d(+cmd: String, +aa: String, +bb: String, +cc: String) -> IO(Unit):
  run.d.at(String.eq(cmd, "bench-render"), cmd, aa, bb, cc)

# dispatch bench-parse
def run.c.at(zz: Bool, +cmd: String, +aa: String, +bb: String, +cc: String) -> IO(Unit):
  match zz:
    case True{}:
      bench.parse(aa, u32.arg(bb))
    case False{}:
      run.d(cmd, aa, bb, cc)

# try bench-parse then fall through
def run.c(+cmd: String, +aa: String, +bb: String, +cc: String) -> IO(Unit):
  run.c.at(String.eq(cmd, "bench-parse"), cmd, aa, bb, cc)

# dispatch rt
def run.b.at(zz: Bool, +cmd: String, +aa: String, +bb: String, +cc: String) -> IO(Unit):
  match zz:
    case True{}:
      cmd.rt(aa, bb)
    case False{}:
      run.c(cmd, aa, bb, cc)

# try rt then fall through
def run.b(+cmd: String, +aa: String, +bb: String, +cc: String) -> IO(Unit):
  run.b.at(String.eq(cmd, "rt"), cmd, aa, bb, cc)

# dispatch render
def run.a.at(zz: Bool, +cmd: String, +aa: String, +bb: String, +cc: String) -> IO(Unit):
  match zz:
    case True{}:
      cmd.render(aa, bb)
    case False{}:
      run.b(cmd, aa, bb, cc)

# try render then fall through
def run.a(+cmd: String, +aa: String, +bb: String, +cc: String) -> IO(Unit):
  run.a.at(String.eq(cmd, "render"), cmd, aa, bb, cc)

# dispatch parse
def run.named.at(zz: Bool, +cmd: String, +aa: String, +bb: String, +cc: String) -> IO(Unit):
  match zz:
    case True{}:
      cmd.parse(aa)
    case False{}:
      run.a(cmd, aa, bb, cc)

# try parse then fall through
def run.named(+cmd: String, +aa: String, +bb: String, +cc: String) -> IO(Unit):
  run.named.at(String.eq(cmd, "parse"), cmd, aa, bb, cc)

# the first four argv strings, empty when missing
def args4(xs: List<String>) -> String & String & String & String:  # noqa: L001 bench harness, outside the spec
  match xs:
    case a <> b <> c <> d <> _t:
      (a, b, c, d)
    case a <> b <> c <> Nil{}:
      (a, b, c, "")
    case a <> b <> Nil{}:
      (a, b, "", "")
    case a <> Nil{}:
      (a, "", "", "")
    case Nil{}:
      ("", "", "", "")

# unpack argv and run the named command
def main.go(quad: String & String & String & String) -> IO(Unit):
  (a, b, c, d) = quad
  run.named(a, b, c, d)

# CLI entry: dispatch by the first argv word
def main() -> IO(Unit):  # noqa: L001 bench harness, outside the spec
  do IO<Unit>:
    args : List<String> <- IO.args()
    main.go(args4(args))
