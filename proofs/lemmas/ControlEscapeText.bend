# the text render writes for a control character and its escape
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/StringRenderEscapes.bend as L1
import ../../laws/defs/BlankAndControlChars.bend as D1

# CTL: the escape of each control, computed once. Laws.esc runs basic.hex,
# four U32 divisions by 16, so computing a control's escape is the costly
# part of every proof that takes the controls one at a time. ctl.esc.lit
# computes it once per control, as ctl.txt, which reads the escape straight
# off the code point's bits; ctl.esc.all then hands each family that text.

# one lowercase hex digit, from its four bits, low bit first
def ctl.hx(b0: Bool, b1: Bool, b2: Bool, b3: Bool) -> Char:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      '0'
    case True{} False{} False{} False{}:
      '1'
    case False{} True{} False{} False{}:
      '2'
    case True{} True{} False{} False{}:
      '3'
    case False{} False{} True{} False{}:
      '4'
    case True{} False{} True{} False{}:
      '5'
    case False{} True{} True{} False{}:
      '6'
    case True{} True{} True{} False{}:
      '7'
    case False{} False{} False{} True{}:
      '8'
    case True{} False{} False{} True{}:
      '9'
    case False{} True{} False{} True{}:
      'a'
    case True{} True{} False{} True{}:
      'b'
    case False{} False{} True{} True{}:
      'c'
    case True{} False{} True{} True{}:
      'd'
    case False{} True{} True{} True{}:
      'e'
    case True{} True{} True{} True{}:
      'f'

# u00 and two hex digits, the high one first
def ctl.u00(hi: Char, lo: Char) -> String:
  SCon{'u', SCon{'0', SCon{'0', SCon{hi, SCon{lo, SNil{}}}}}}

# what follows the backslash for a code point below 16, from its four bits:
# the five with a letter, and u000 and a digit for the rest
def ctl.txt.lo(b0: Bool, b1: Bool, b2: Bool, b3: Bool) -> String:
  match b0 b1 b2 b3:
    case False{} False{} False{} True{}:
      "b"
    case True{} False{} False{} True{}:
      "t"
    case False{} True{} False{} True{}:
      "n"
    case False{} False{} True{} True{}:
      "f"
    case True{} False{} True{} True{}:
      "r"
    case _ _ _ _:
      ctl.u00('0', ctl.hx(b0, b1, b2, b3))

# below 16, or u00 and both hex digits of the low byte
def ctl.txt.hi(
  high: Bool,
  b0: Bool,
  b1: Bool,
  b2: Bool,
  b3: Bool,
  b4: Bool,
  b5: Bool,
  b6: Bool,
  b7: Bool
) -> String:
  match high:
    case False{}:
      ctl.txt.lo(b0, b1, b2, b3)
    case True{}:
      ctl.u00(ctl.hx(b4, b5, b6, b7), ctl.hx(b0, b1, b2, b3))

# what follows the backslash, read off the low byte
def ctl.tl(uu: U32) -> String:
  match uu:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{+b4, WCon{+b5, WCon{+b6, WCon{+b7, _hi}}}}}}}}}:
      ctl.txt.hi(Bool.or(Bool.or(b4, b5), Bool.or(b6, b7)), b0, b1, b2, b3, b4, b5, b6, b7)

# the text render writes for a control: a backslash, then ctl.tl
def ctl.txt(uu: U32) -> String:
  SCon{'\\', ctl.tl(uu)}

# the escape of each control is ctl.txt: the only place a control's escape
# is computed
def ctl.esc.lit(
  +uu: U32,
  h_c: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == True{} : Bool}
) -> {ctl.txt(uu) == L1.esc(Chr{uu}) : String}:
  Eq.ctl.all(kk => {ctl.txt(kk) == L1.esc(Chr{kk}) : String}, uu, h_c,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==},
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==},
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==},
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==},
    {==})

# a claim about a control and its escape holds for every control once it
# holds for each of the thirty-three at its ctl.txt
def ctl.esc.all(
  -PP: U32 -> String -> Type,
  +uu: U32,
  +h_c: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == True{} : Bool},
  c00: PP(0, ctl.txt(0)),
  c01: PP(1, ctl.txt(1)),
  c02: PP(2, ctl.txt(2)),
  c03: PP(3, ctl.txt(3)),
  c04: PP(4, ctl.txt(4)),
  c05: PP(5, ctl.txt(5)),
  c06: PP(6, ctl.txt(6)),
  c07: PP(7, ctl.txt(7)),
  c08: PP(8, ctl.txt(8)),
  c09: PP(9, ctl.txt(9)),
  c10: PP(10, ctl.txt(10)),
  c11: PP(11, ctl.txt(11)),
  c12: PP(12, ctl.txt(12)),
  c13: PP(13, ctl.txt(13)),
  c14: PP(14, ctl.txt(14)),
  c15: PP(15, ctl.txt(15)),
  c16: PP(16, ctl.txt(16)),
  c17: PP(17, ctl.txt(17)),
  c18: PP(18, ctl.txt(18)),
  c19: PP(19, ctl.txt(19)),
  c20: PP(20, ctl.txt(20)),
  c21: PP(21, ctl.txt(21)),
  c22: PP(22, ctl.txt(22)),
  c23: PP(23, ctl.txt(23)),
  c24: PP(24, ctl.txt(24)),
  c25: PP(25, ctl.txt(25)),
  c26: PP(26, ctl.txt(26)),
  c27: PP(27, ctl.txt(27)),
  c28: PP(28, ctl.txt(28)),
  c29: PP(29, ctl.txt(29)),
  c30: PP(30, ctl.txt(30)),
  c31: PP(31, ctl.txt(31)),
  c127: PP(127, ctl.txt(127))
) -> PP(uu, L1.esc(Chr{uu})):
  %ctl.esc.lit(uu, h_c) : PP(uu, _)
  Eq.ctl.all(kk => PP(kk, ctl.txt(kk)), uu, h_c,
    c00, c01, c02, c03, c04, c05, c06, c07,
    c08, c09, c10, c11, c12, c13, c14, c15,
    c16, c17, c18, c19, c20, c21, c22, c23,
    c24, c25, c26, c27, c28, c29, c30, c31,
    c127)

# Every other character. Each test basic.cls makes answers False.

# a code point a char is not is not equal to it
def neq.go(
  +uu: U32,
  +kk: U32,
  bb: Bool,
  eb: {U32.is_eq(uu, kk) == bb : Bool},
  hn: {Chr{uu} != Chr{kk} : Char}
) -> {bb == False{} : Bool}:
  match bb:
    case False{}:
      {==}
    case True{}:
      Eq.bit.gone(&2, {True{} == False{} : Bool}, hn(Eq.u32_eq(uu, kk, eb)))

# a code point a char is not is not equal to it
def neq.off(
  +uu: U32,
  +kk: U32,
  hn: {Chr{uu} != Chr{kk} : Char}
) -> {U32.is_eq(uu, kk) == False{} : Bool}:
  neq.go(uu, kk, U32.is_eq(uu, kk), {==}, hn)

# a code point that is no control is not a control's
def ctl.off(
  +uu: U32,
  +kk: U32,
  eu: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool},
  ek: {Bool.or(U32.is_lt(kk, 32), U32.is_eq(kk, 127)) == True{} : Bool}
) -> {U32.is_eq(uu, kk) == False{} : Bool}:
  neq.off(uu, kk, ee => Eq.bit.clash(Equal.trans(Bool, False{}, D1.is_ctl(Chr{uu}), True{},
    Equal.sym(Bool, D1.is_ctl(Chr{uu}), False{}, eu),
    Equal.trans(Bool, D1.is_ctl(Chr{uu}), D1.is_ctl(Chr{kk}), True{},
      Equal.cong(Char, Bool, cc => D1.is_ctl(cc), Chr{uu}, Chr{kk}, ee), ek))))

# a code point that passes none of basic.cls's tests is written as itself
def cls.plain(
  +uu: U32,
  e8: {U32.is_eq(uu, 8) == False{} : Bool},
  e9: {U32.is_eq(uu, 9) == False{} : Bool},
  e10: {U32.is_eq(uu, 10) == False{} : Bool},
  e12: {U32.is_eq(uu, 12) == False{} : Bool},
  e13: {U32.is_eq(uu, 13) == False{} : Bool},
  e34: {U32.is_eq(uu, 34) == False{} : Bool},
  e92: {U32.is_eq(uu, 92) == False{} : Bool},
  ec: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool}
) -> {T.basic.cls(uu) == T.BKCh{} : T.BK}:
  %Equal.sym(Bool, U32.is_eq(uu, 8), False{}, e8) : {T.basic.cls.bs(_, uu) == T.BKCh{} : T.BK}
  %Equal.sym(Bool, U32.is_eq(uu, 9), False{}, e9) : {T.basic.cls.tab(_, uu) == T.BKCh{} : T.BK}
  %Equal.sym(Bool, U32.is_eq(uu, 10), False{}, e10) : {T.basic.cls.lf(_, uu) == T.BKCh{} : T.BK}
  %Equal.sym(Bool, U32.is_eq(uu, 12), False{}, e12) : {T.basic.cls.ff(_, uu) == T.BKCh{} : T.BK}
  %Equal.sym(Bool, U32.is_eq(uu, 13), False{}, e13) : {T.basic.cls.cr(_, uu) == T.BKCh{} : T.BK}
  %Equal.sym(Bool, U32.is_eq(uu, 34), False{}, e34) : {T.basic.cls.quote(_, uu) == T.BKCh{} : T.BK}
  %Equal.sym(Bool, U32.is_eq(uu, 92), False{}, e92) : {T.basic.cls.bslash(_, uu) == T.BKCh{} : T.BK}
  %Equal.sym(Bool, Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), False{},
    ec) : {T.basic.cls.hex(_) == T.BKCh{} : T.BK}
  {==}

# The whole string. An output list is kept reversed; its text is read back
# with reverse.

# a list reversed onto what is already there reads as the list reversed, then
# that
def txt.onto(
  xs: List<&2, Char>,
  +acc: List<&2, Char>
) -> {String.from_list(List.reverse.go(&2, Char, xs, acc))
  == String.append(String.from_list(List.reverse.go(&2, Char, xs, [])), String.from_list(acc)) : String}:
  match xs:
    case []:
      {==}
    case +yy <> +ys:
      Equal.trans(String, String.from_list(List.reverse.go(&2, Char, ys, yy <> acc)),
        String.append(String.from_list(List.reverse.go(&2, Char, ys, [])), String.from_list(yy <> acc)),
        String.append(String.from_list(List.reverse.go(&2, Char, ys, [yy])), String.from_list(acc)),
        txt.onto(ys, yy <> acc),
        Equal.sym(String, String.append(String.from_list(List.reverse.go(&2, Char, ys, [yy])), String.from_list(acc)),
          String.append(String.from_list(List.reverse.go(&2, Char, ys, [])), String.from_list(yy <> acc)),
          Equal.trans(String,
            String.append(String.from_list(List.reverse.go(&2, Char, ys, [yy])), String.from_list(acc)),
            String.append(String.append(String.from_list(List.reverse.go(&2, Char, ys, [])), String.from_list([yy])),
              String.from_list(acc)),
            String.append(String.from_list(List.reverse.go(&2, Char, ys, [])),
              String.append(String.from_list([yy]), String.from_list(acc))),
            Equal.cong(String, String, zz => String.append(zz, String.from_list(acc)),
              String.from_list(List.reverse.go(&2, Char, ys, [yy])),
              String.append(String.from_list(List.reverse.go(&2, Char, ys, [])), String.from_list([yy])),
              txt.onto(ys, [yy])),
            Eq.append_assoc(String.from_list(List.reverse.go(&2, Char, ys, [])), String.from_list([yy]),
              String.from_list(acc)))))

# one character of each class written onto an output reads as the output,
# then the character's text
def disp.txt(
  kk: T.BK,
  +cc: Char,
  +uu: U32,
  +out: List<&2, Char>
) -> {String.from_list(List.reverse(&2, Char, T.basic.disp(kk, cc, uu, out)))
  == String.append(String.from_list(List.reverse(&2, Char, out)),
    String.from_list(List.reverse(&2, Char, T.basic.disp(kk, cc, uu, [])))) : String}:
  match kk:
    case T.BKCh{}:
      txt.onto(out, [cc])
    case T.BKEsc{+mark}:
      txt.onto(out, ['\\', mark])
    case T.BKHex{}:
      txt.onto(out, ['\\', 'u', T.hex.char(U32.mod(U32.shrn(uu, 12n), 16)), T.hex.char(U32.mod(U32.shrn(uu, 8n), 16)),
        T.hex.char(U32.mod(U32.shrn(uu, 4n), 16)), T.hex.char(U32.mod(uu, 16))])

# one character written onto an output reads as the output, then its escape
def one.txt(
  +cc: Char,
  +out: List<&2, Char>
) -> {String.from_list(List.reverse(&2, Char, T.basic.one(cc, out)))
  == String.append(String.from_list(List.reverse(&2, Char, out)), L1.esc(cc)) : String}:
  disp.txt(T.basic.cls(Char.to_u32(cc)), cc, Char.to_u32(cc), out)

# a string's characters written onto an output read as the output, then escs
def go.txt(
  ss: String,
  +out: List<&2, Char>
) -> {String.from_list(List.reverse(&2, Char, T.basic.go(String.to_list(ss), out)))
  == String.append(String.from_list(List.reverse(&2, Char, out)), L1.escs(ss)) : String}:
  match ss:
    case SNil{}:
      Equal.sym(String, String.append(String.from_list(List.reverse(&2, Char, out)), SNil{}),
        String.from_list(List.reverse(&2, Char, out)), Eq.append_nil(String.from_list(List.reverse(&2, Char, out))))
    case SCon{+hh, +tt}:
      Equal.trans(String,
        String.from_list(List.reverse(&2, Char, T.basic.go(String.to_list(tt), T.basic.one(hh, out)))),
        String.append(String.from_list(List.reverse(&2, Char, T.basic.one(hh, out))), L1.escs(tt)),
        String.append(String.from_list(List.reverse(&2, Char, out)), String.append(L1.esc(hh), L1.escs(tt))),
        go.txt(tt, T.basic.one(hh, out)),
        Equal.trans(String,
          String.append(String.from_list(List.reverse(&2, Char, T.basic.one(hh, out))), L1.escs(tt)),
          String.append(String.append(String.from_list(List.reverse(&2, Char, out)), L1.esc(hh)), L1.escs(tt)),
          String.append(String.from_list(List.reverse(&2, Char, out)), String.append(L1.esc(hh), L1.escs(tt))),
          Equal.cong(String, String, zz => String.append(zz, L1.escs(tt)),
            String.from_list(List.reverse(&2, Char, T.basic.one(hh, out))),
            String.append(String.from_list(List.reverse(&2, Char, out)), L1.esc(hh)), one.txt(hh, out)),
          Eq.append_assoc(String.from_list(List.reverse(&2, Char, out)), L1.esc(hh), L1.escs(tt))))

# a reversed buffer folded onto a string with SCon is that buffer read in order, then the accumulator
def fold.ord(
  xs: List<&2, Char>,
  +acc: String
) -> {T.buf.str.go(xs, acc) == String.append(String.from_list(List.reverse(&2, Char, xs)), acc) : String}:
  match xs:
    case []:
      {==}
    case +h <> +t:
      Equal.trans(String,
        T.buf.str.go(t, SCon{h, acc}),
        String.append(String.from_list(List.reverse(&2, Char, t)), SCon{h, acc}),
        String.append(String.from_list(List.reverse(&2, Char, h <> t)), acc),
        fold.ord(t, SCon{h, acc}),
        Equal.trans(String,
          String.append(String.from_list(List.reverse(&2, Char, t)), SCon{h, acc}),
          String.append(String.from_list(List.reverse(&2, Char, t)), String.append(String.from_list([h]), acc)),
          String.append(String.from_list(List.reverse.go(&2, Char, t, [h])), acc),
          Equal.cong(String, String, zz => String.append(String.from_list(List.reverse(&2, Char, t)), zz),
            SCon{h, acc}, String.append(String.from_list([h]), acc), {==}),
          Equal.trans(String,
            String.append(String.from_list(List.reverse(&2, Char, t)), String.append(String.from_list([h]), acc)),
            String.append(String.append(String.from_list(List.reverse(&2, Char, t)), String.from_list([h])), acc),
            String.append(String.from_list(List.reverse.go(&2, Char, t, [h])), acc),
            Equal.sym(String,
              String.append(String.append(String.from_list(List.reverse(&2, Char, t)), String.from_list([h])), acc),
              String.append(String.from_list(List.reverse(&2, Char, t)), String.append(String.from_list([h]), acc)),
              Eq.append_assoc(String.from_list(List.reverse(&2, Char, t)), String.from_list([h]), acc)),
            Equal.cong(String, String, zz => String.append(zz, acc),
              String.append(String.from_list(List.reverse(&2, Char, t)), String.from_list([h])),
              String.from_list(List.reverse.go(&2, Char, t, [h])),
              Equal.sym(String,
                String.from_list(List.reverse.go(&2, Char, t, [h])),
                String.append(String.from_list(List.reverse(&2, Char, t)), String.from_list([h])),
                txt.onto(t, [h]))))))

# the fold with an empty accumulator is the reversed buffer read as a string
def fold.nil(
  +xs: List<&2, Char>
) -> {T.buf.str.go(xs, "") == String.from_list(List.reverse(&2, Char, xs)) : String}:
  Equal.trans(String,
    T.buf.str.go(xs, ""),
    String.append(String.from_list(List.reverse(&2, Char, xs)), ""),
    String.from_list(List.reverse(&2, Char, xs)),
    fold.ord(xs, ""),
    Eq.append_nil(String.from_list(List.reverse(&2, Char, xs))))

# key.basic is the quotes around escs
def L1.basic_escs(s):
  Equal.trans(String,
    SCon{'"', String.append(T.buf.str.go(T.basic.go(String.to_list(s), []), ""), "\"")},
    SCon{'"', String.append(String.from_list(List.reverse(&2, Char, T.basic.go(String.to_list(s), []))), "\"")},
    SCon{'"', String.append(L1.escs(s), "\"")},
    Equal.cong(String, String, zz => SCon{'"', String.append(zz, "\"")},
      T.buf.str.go(T.basic.go(String.to_list(s), []), ""),
      String.from_list(List.reverse(&2, Char, T.basic.go(String.to_list(s), []))),
      fold.nil(T.basic.go(String.to_list(s), []))),
    Equal.cong(String, String, zz => String.append("\"", String.append(zz, "\"")),
      String.from_list(List.reverse(&2, Char, T.basic.go(String.to_list(s), []))), L1.escs(s), go.txt(s, [])))

# The span fast path. span.quote copies a span's characters until one needs an
# escape, and then gives up to key.basic.

# a quoting walk that has stopped stays stopped
def push.stop(bb: Bool, hh: Char) -> {T.span.quote.push(bb, T.SqStop{}, hh) == T.SqStop{} : T.SqAcc}:
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# a stopped walk ends with no copy, whatever is left
def sq.stop(src: String, +nn: U32, zz: Bool) -> {T.span.quote.go(src, nn, zz, T.SqStop{}) == T.SqNo{} : T.Sq}:
  match src zz:
    case SNil{} True{}:
      {==}
    case SNil{} False{}:
      {==}
    case SCon{_h, _t} True{}:
      {==}
    case SCon{+hh, +tt} False{}:
      Equal.trans(T.Sq,
        T.span.quote.go(tt, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)),
          T.span.quote.push(T.span.esc(Char.to_u32(hh)), T.SqStop{}, hh)),
        T.span.quote.go(tt, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)), T.SqStop{}), T.SqNo{},
        Equal.cong(T.SqAcc, T.Sq, aa => T.span.quote.go(tt, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)), aa),
          T.span.quote.push(T.span.esc(Char.to_u32(hh)), T.SqStop{}, hh), T.SqStop{},
          push.stop(T.span.esc(Char.to_u32(hh)), hh)),
        sq.stop(tt, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1))))

# the walk's answer on a text: a copy, reversed onto rr, when no character
# needs an escape
def sq.want.step(esc: Bool, more: Unit -> T.Sq) -> T.Sq:
  match esc:
    case True{}:
      T.SqNo{}
    case False{}:
      more(Unit{})

# the walk's answer on a text
def sq.want(ss: String, rr: List<&2, Char>) -> T.Sq:
  match ss:
    case SNil{}:
      T.SqOk{rr}
    case SCon{+hh, tt}:
      sq.want.step(T.span.esc(Char.to_u32(hh)), _u => sq.want(tt, hh <> rr))

# the walk's claim for the rest of a span, one character copied
def sq.Ih(tt: String, +mm: U32, hh: Char, rr: List<&2, Char>) -> Type:
  {T.span.quote.go(tt, mm, U32.is_zero(mm), T.SqRun{hh <> rr})
    == sq.want(T.span.str(tt, mm, U32.is_zero(mm)), hh <> rr) : T.Sq}

# one character of the walk: an escape stops it, anything else is copied
def sq.go.step(
  bb: Bool,
  +hh: Char,
  +tt: String,
  +mm: U32,
  +rr: List<&2, Char>,
  ih: sq.Ih(tt, mm, hh, rr)
) -> {T.span.quote.go(tt, mm, U32.is_zero(mm), T.span.quote.push(bb, T.SqRun{rr}, hh))
  == sq.want.step(bb, _u => sq.want(T.span.str(tt, mm, U32.is_zero(mm)), hh <> rr)) : T.Sq}:
  match bb:
    case True{}:
      sq.stop(tt, mm, U32.is_zero(mm))
    case False{}:
      ih

# the walk over a span answers what its characters give
def sq.go.want(
  src: String,
  +nn: U32,
  zz: Bool,
  +rr: List<&2, Char>
) -> {T.span.quote.go(src, nn, zz, T.SqRun{rr}) == sq.want(T.span.str(src, nn, zz), rr) : T.Sq}:
  match src zz:
    case SNil{} True{}:
      {==}
    case SNil{} False{}:
      {==}
    case SCon{_h, _t} True{}:
      {==}
    case SCon{+hh, +tt} False{}:
      sq.go.step(T.span.esc(Char.to_u32(hh)), hh, tt, U32.sub(nn, 1), rr,
        sq.go.want(tt, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)), hh <> rr))

# a text none of whose characters needs an escape
def plain(ss: String) -> Bool:
  match ss:
    case SNil{}:
      True{}
    case SCon{+hh, tt}:
      Bool.and(Bool.not(T.span.esc(Char.to_u32(hh))), plain(tt))

# a copy when the text is plain, and no copy otherwise
def sq.gate(ok: Bool, rr: List<&2, Char>) -> T.Sq:
  match ok:
    case True{}:
      T.SqOk{rr}
    case False{}:
      T.SqNo{}

# a character that needs no escape passes every test of basic.cls
def esc.no.ctl(
  +uu: U32,
  +ee: {T.span.esc(uu) == False{} : Bool}
) -> {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool}:
  Equal.trans(Bool, Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), Bool.or(False{}, U32.is_eq(uu, 127)), False{},
    Equal.cong(Bool, Bool, xx => Bool.or(xx, U32.is_eq(uu, 127)), U32.is_lt(uu, 32), False{},
      Eq.or.false_left(U32.is_lt(uu, 32),
        Bool.or(U32.is_eq(uu, 34), Bool.or(U32.is_eq(uu, 92), U32.is_eq(uu, 127))), ee)),
    Eq.or.false_right(U32.is_eq(uu, 92), U32.is_eq(uu, 127),
      Eq.or.false_right(U32.is_eq(uu, 34), Bool.or(U32.is_eq(uu, 92), U32.is_eq(uu, 127)),
        Eq.or.false_right(U32.is_lt(uu, 32),
          Bool.or(U32.is_eq(uu, 34), Bool.or(U32.is_eq(uu, 92), U32.is_eq(uu, 127))), ee))))

# a character that needs no escape is written as itself
def one.plain(
  +cc: Char,
  rr: List<&2, Char>,
  +ee: {T.span.esc(Char.to_u32(cc)) == False{} : Bool}
) -> {T.basic.one(cc, rr) == cc <> rr : List<&2, Char>}:
  match cc:
    case Chr{+uu}:
      Equal.cong(T.BK, List<&2, Char>, kk => T.basic.disp(kk, Chr{uu}, uu, rr), T.basic.cls(uu), T.BKCh{},
        cls.plain(uu, ctl.off(uu, 8, esc.no.ctl(uu, ee), {==}), ctl.off(uu, 9, esc.no.ctl(uu, ee), {==}),
          ctl.off(uu, 10, esc.no.ctl(uu, ee), {==}), ctl.off(uu, 12, esc.no.ctl(uu, ee), {==}),
          ctl.off(uu, 13, esc.no.ctl(uu, ee), {==}),
          Eq.or.false_left(U32.is_eq(uu, 34), Bool.or(U32.is_eq(uu, 92), U32.is_eq(uu, 127)),
            Eq.or.false_right(U32.is_lt(uu, 32),
              Bool.or(U32.is_eq(uu, 34), Bool.or(U32.is_eq(uu, 92), U32.is_eq(uu, 127))), ee)),
          Eq.or.false_left(U32.is_eq(uu, 92), U32.is_eq(uu, 127),
            Eq.or.false_right(U32.is_eq(uu, 34), Bool.or(U32.is_eq(uu, 92), U32.is_eq(uu, 127)),
              Eq.or.false_right(U32.is_lt(uu, 32),
                Bool.or(U32.is_eq(uu, 34), Bool.or(U32.is_eq(uu, 92), U32.is_eq(uu, 127))), ee))),
          esc.no.ctl(uu, ee)))

# one character of the answer: an escape gives no copy, and anything else is
# written as itself
def sq.gate.step(
  bb: Bool,
  +hh: Char,
  +tt: String,
  +rr: List<&2, Char>,
  eb: {T.span.esc(Char.to_u32(hh)) == bb : Bool},
  ih: {sq.want(tt, hh <> rr) == sq.gate(plain(tt), T.basic.go(String.to_list(tt), hh <> rr)) : T.Sq}
) -> {sq.want.step(bb, _u => sq.want(tt, hh <> rr))
  == sq.gate(Bool.and(Bool.not(bb), plain(tt)), T.basic.go(String.to_list(tt), T.basic.one(hh, rr))) : T.Sq}:
  match bb:
    case True{}:
      {==}
    case False{}:
      Equal.trans(T.Sq, sq.want(tt, hh <> rr), sq.gate(plain(tt), T.basic.go(String.to_list(tt), hh <> rr)),
        sq.gate(plain(tt), T.basic.go(String.to_list(tt), T.basic.one(hh, rr))), ih,
        Equal.cong(List<&2, Char>, T.Sq, ll => sq.gate(plain(tt), T.basic.go(String.to_list(tt), ll)),
          hh <> rr, T.basic.one(hh, rr),
          Equal.sym(List<&2, Char>, T.basic.one(hh, rr), hh <> rr, one.plain(hh, rr, eb))))

# the answer on a text is basic.go's output when the text is plain
def sq.want.gate(
  ss: String,
  +rr: List<&2, Char>
) -> {sq.want(ss, rr) == sq.gate(plain(ss), T.basic.go(String.to_list(ss), rr)) : T.Sq}:
  match ss:
    case SNil{}:
      {==}
    case SCon{+hh, +tt}:
      sq.gate.step(T.span.esc(Char.to_u32(hh)), hh, tt, rr, {==}, sq.want.gate(tt, hh <> rr))

# a copy is the quotes around the characters written as themselves
def sq.fin(
  bb: Bool,
  +src: String,
  +nn: U32
) -> {T.span.quote.fin(sq.gate(bb, T.basic.go(String.to_list(T.span.str(src, nn, U32.is_zero(nn))), ['"'])), src, nn)
  == T.key.basic(T.span.str(src, nn, U32.is_zero(nn))) : String}:
  match bb:
    case False{}:
      {==}
    case True{}:
      Equal.trans(String,
        T.buf.str.go(T.basic.go(String.to_list(T.span.str(src, nn, U32.is_zero(nn))), ['"']), "\""),
        String.append(String.from_list(List.reverse(&2, Char,
          T.basic.go(String.to_list(T.span.str(src, nn, U32.is_zero(nn))), ['"']))), "\""),
        T.key.basic(T.span.str(src, nn, U32.is_zero(nn))),
        fold.ord(T.basic.go(String.to_list(T.span.str(src, nn, U32.is_zero(nn))), ['"']), "\""),
        Equal.trans(String,
          String.append(String.from_list(List.reverse(&2, Char,
            T.basic.go(String.to_list(T.span.str(src, nn, U32.is_zero(nn))), ['"']))), "\""),
          String.append(String.append("\"", L1.escs(T.span.str(src, nn, U32.is_zero(nn)))), "\""),
          T.key.basic(T.span.str(src, nn, U32.is_zero(nn))),
          Equal.cong(String, String, zz => String.append(zz, "\""),
            String.from_list(List.reverse(&2, Char,
              T.basic.go(String.to_list(T.span.str(src, nn, U32.is_zero(nn))), ['"']))),
            String.append("\"", L1.escs(T.span.str(src, nn, U32.is_zero(nn)))),
            go.txt(T.span.str(src, nn, U32.is_zero(nn)), ['"'])),
          Equal.sym(String, T.key.basic(T.span.str(src, nn, U32.is_zero(nn))),
            String.append("\"", String.append(L1.escs(T.span.str(src, nn, U32.is_zero(nn))), "\"")),
            L1.basic_escs(T.span.str(src, nn, U32.is_zero(nn))))))

# the walk answers what the characters give, which is key.basic's text
def L1.span_quote_basic(src, n):
  Equal.trans(String, T.span.quote(src, n),
    T.span.quote.fin(sq.want(T.span.str(src, n, U32.is_zero(n)), ['"']), src, n),
    T.key.basic(T.span.str(src, n, U32.is_zero(n))),
    Equal.cong(T.Sq, String, qq => T.span.quote.fin(qq, src, n),
      T.span.quote.go(src, n, U32.is_zero(n), T.SqRun{['"']}),
      sq.want(T.span.str(src, n, U32.is_zero(n)), ['"']), sq.go.want(src, n, U32.is_zero(n), ['"'])),
    Equal.trans(String,
      T.span.quote.fin(sq.want(T.span.str(src, n, U32.is_zero(n)), ['"']), src, n),
      T.span.quote.fin(sq.gate(plain(T.span.str(src, n, U32.is_zero(n))),
        T.basic.go(String.to_list(T.span.str(src, n, U32.is_zero(n))), ['"'])), src, n),
      T.key.basic(T.span.str(src, n, U32.is_zero(n))),
      Equal.cong(T.Sq, String, qq => T.span.quote.fin(qq, src, n),
        sq.want(T.span.str(src, n, U32.is_zero(n)), ['"']),
        sq.gate(plain(T.span.str(src, n, U32.is_zero(n))),
          T.basic.go(String.to_list(T.span.str(src, n, U32.is_zero(n))), ['"'])),
        sq.want.gate(T.span.str(src, n, U32.is_zero(n)), ['"'])),
      sq.fin(plain(T.span.str(src, n, U32.is_zero(n))), src, n)))
