# the walk a header runs along its segments, with bare and quoted segments
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/defs/BareValueGrammar.bend as D1
import ./PickAndDigitSteps.bend as M1
import ./StringEqualsItself.bend as M2
import ./ValueTextReadback.bend as M3

# WP-H: headers read back. A header is read one segment at a time: a bare
# segment's characters are pushed onto the buffer in LHead, a quoted one is
# read by WP0's quoted-segment family at hd = True, and the dot or bracket
# after it pushes the segment onto parts. The closing bracket runs the walk,
# which the law takes as a premise (WP-W's contracts discharge it), and the
# newline returns to the start of a line. Every lemma takes the rest of the
# text as read from every back and qkind, as qs.escs does.

# a scanner inside a header: the segments read so far in parts, newest
# first, and the open bare segment reversed in buf
def wh.st(
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  parts: List<&2, String>,
  buf: List<&2, Char>,
  lex: T.Lex,
  back: T.Lex,
  qkind: T.QKind,
  arrtab: Bool
) -> T.St:
  T.St{"", rows, heads, here, parts, buf, lex, back, qkind, [], T.HNone{}, 0, 0, arrtab,
    False{}}

# in a header, a bare character is no second bracket and so is a key character
def wh.go.bare(
  br: Bool,
  bare: Bool,
  sp: Bool,
  dot: Bool,
  end: Bool,
  qq: Bool,
  lit: Bool,
  hash: Bool,
  st: T.St,
  +xx: U32,
  ebr: {Char.is_eq(Chr{xx}, '[') == br : Bool},
  ebare: {T.bare.at(Chr{xx}) == bare : Bool},
  +ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.lex.head.go(br, bare, sp, dot, end, qq, lit, hash, st, Chr{xx})
  == T.lex.head.ch(st, Chr{xx}) : T.St}:
  match br:
    case True{}:
      Eq.bit.gone(&2, {T.lex.head.go(True{}, bare, sp, dot, end, qq, lit, hash, st, Chr{xx})
        == T.lex.head.ch(st, Chr{xx}) : T.St},
        Eq.refute_char(Chr{xx}, '[', ch => T.bare.at(ch), ebr, ee, {==}))
    case False{}:
      match bare:
        case True{}:
          {==}
        case False{}:
          M2.clash(&2, {T.lex.head.go(False{}, False{}, sp, dot, end, qq, lit, hash, st, Chr{xx})
            == T.lex.head.ch(st, Chr{xx}) : T.St},
            Equal.trans(Bool, False{}, T.bare.at(Chr{xx}), True{},
              Equal.sym(Bool, T.bare.at(Chr{xx}), False{}, ebare), ee))

# after a dot, a bare character is no blank and so starts a bare segment
def wh.dot.bare(
  sp: Bool,
  bare: Bool,
  qq: Bool,
  lit: Bool,
  st: T.St,
  +xx: U32,
  esp: {T.ch.sp(Chr{xx}) == sp : Bool},
  ebare: {T.bare.at(Chr{xx}) == bare : Bool},
  +ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.lex.hdot(sp, bare, qq, lit, st, Chr{xx}) == T.st.push(st, Chr{xx}, T.LHead{}) : T.St}:
  match sp:
    case True{}:
      Eq.bit.gone(&2, {T.lex.hdot(True{}, bare, qq, lit, st, Chr{xx})
        == T.st.push(st, Chr{xx}, T.LHead{}) : T.St},
        M3.or2.no(xx, 32, 9, U32.is_eq(xx, 32), U32.is_eq(xx, 9), {==}, {==}, esp,
          ch => T.bare.at(ch), ee, {==}, {==}))
    case False{}:
      match bare:
        case True{}:
          {==}
        case False{}:
          M2.clash(&2, {T.lex.hdot(False{}, False{}, qq, lit, st, Chr{xx})
            == T.st.push(st, Chr{xx}, T.LHead{}) : T.St},
            Equal.trans(Bool, False{}, T.bare.at(Chr{xx}), True{},
              Equal.sym(Bool, T.bare.at(Chr{xx}), False{}, ebare), ee))

# the rest of the text after the closing bracket: a newline, after a second
# bracket for an array of tables
def wh.tail(arrtab: Bool, rest: String) -> String:
  match arrtab:
    case False{}:
      SCon{'\n', rest}
    case True{}:
      SCon{']', SCon{'\n', rest}}

# the walk a header runs, with what it returns
def wh.Walk(
  arrtab: Bool,
  path: List<&2, String>,
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  rows2: List<&2, T.Val>,
  heads2: List<&2, String>
) -> Type:
  {T.tree.walk(path, T.Tw{rows, D1.header_job(arrtab), [], "", "", heads, False{}}, 0)
    == T.End{rows2, "", heads2} : T.End}

# reversing a list reversed onto acc puts acc's reversal first
def wh.rr(
  t: List<&2, String>,
  +acc: List<&2, String>,
  +ys: List<&2, String>
) -> {List.reverse.go(&2, String, List.reverse.go(&2, String, t, acc), ys)
  == List.reverse.go(&2, String, acc, List.append(&2, String, t, ys)) : List<&2, String>}:
  match t:
    case []:
      {==}
    case +xx <> xs:
      wh.rr(xs, xx <> acc, ys)

# appending nothing to a list of segments leaves it
def wh.lnil(t: List<&2, String>) -> {List.append(&2, String, t, []) == t : List<&2, String>}:
  match t:
    case []:
      {==}
    case +xx <> xs:
      Equal.cong(List<&2, String>, List<&2, String>, zz => xx <> zz,
        List.append(&2, String, xs, []), xs, wh.lnil(xs))

# WP-K3: keys however they are written. A literal quoted segment is read one
# character at a time in the segment's state (LKeyQ for a key, LHeadQ for a
# header, as WP0's qs family takes it by the bit hd) with qkind QLit: every
# character but the apostrophe is pushed as it is, and back never moves, so
# unlike qs these lemmas are plain equations.

# a scanner inside a literal quoted segment, its characters so far reversed
# in buf
def ql(
  hd: Bool,
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  parts: List<&2, String>,
  arrtab: Bool,
  back: T.Lex,
  buf: List<&2, Char>
) -> T.St:
  T.St{"", rows, heads, here, parts, buf, M1.qs.lex(hd), back, T.QLit{}, [], T.HNone{}, 0, 0,
    arrtab, False{}}

# a code point one of two others' is not, when a predicate tells it apart
def kl.no2(
  bb: Bool,
  +xx: U32,
  +k1: U32,
  +k2: U32,
  eb: {Bool.or(U32.is_eq(xx, k1), U32.is_eq(xx, k2)) == bb : Bool},
  +ee: {T.bare.at(Chr{xx}) == True{} : Bool},
  n1: {T.bare.at(Chr{k1}) == False{} : Bool},
  n2: {T.bare.at(Chr{k2}) == False{} : Bool}
) -> {Bool.or(U32.is_eq(xx, k1), U32.is_eq(xx, k2)) == False{} : Bool}:
  match bb:
    case True{}:
      Eq.bit.gone(&2, {Bool.or(U32.is_eq(xx, k1), U32.is_eq(xx, k2)) == False{} : Bool},
        M3.or2.no(xx, k1, k2, U32.is_eq(xx, k1), U32.is_eq(xx, k2), {==}, {==}, eb, ch => T.bare.at(ch), ee,
          n1, n2))
    case False{}:
      eb

# after a dot, a bare character is no blank and no quote, so it starts a
# bare segment
def kd.bare(
  sp: Bool,
  qq: Bool,
  lit: Bool,
  dot: Bool,
  nl: Bool,
  st: T.St,
  +xx: U32,
  esp: {T.ch.sp(Chr{xx}) == sp : Bool},
  eqq: {Char.is_eq(Chr{xx}, '"') == qq : Bool},
  elit: {Char.is_eq(Chr{xx}, '\'') == lit : Bool},
  +ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.lex.kdot.go(sp, qq, lit, dot, nl, st, Chr{xx}) == T.st.push(st, Chr{xx}, T.LKey{}) : T.St}:
  match sp:
    case True{}:
      Eq.bit.gone(&2, {T.lex.kdot.go(True{}, qq, lit, dot, nl, st, Chr{xx})
        == T.st.push(st, Chr{xx}, T.LKey{}) : T.St},
        M3.or2.no(xx, 32, 9, U32.is_eq(xx, 32), U32.is_eq(xx, 9), {==}, {==}, esp,
          ch => T.bare.at(ch), ee, {==}, {==}))
    case False{}:
      match qq:
        case True{}:
          Eq.bit.gone(&2, {T.lex.kdot.go(False{}, True{}, lit, dot, nl, st, Chr{xx})
            == T.st.push(st, Chr{xx}, T.LKey{}) : T.St},
            Eq.refute_char(Chr{xx}, '"', ch => T.bare.at(ch), eqq, ee, {==}))
        case False{}:
          match lit:
            case True{}:
              Eq.bit.gone(&2, {T.lex.kdot.go(False{}, False{}, True{}, dot, nl, st, Chr{xx})
                == T.st.push(st, Chr{xx}, T.LKey{}) : T.St},
                Eq.refute_char(Chr{xx}, '\'', ch => T.bare.at(ch), elit, ee, {==}))
            case False{}:
              Equal.cong(Bool, T.St, bb => T.lex.kdot.bare(bb, dot, nl, st, Chr{xx}), T.bare.at(Chr{xx}),
                True{}, ee)
