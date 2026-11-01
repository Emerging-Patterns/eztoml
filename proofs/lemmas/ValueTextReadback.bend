# the induction showing the text render writes for a value reads back to it
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/BoolReadsBack.bend as L1
import ../../laws/BoolWord.bend as L2
import ../../laws/DateTimeReadExactly.bend as L3
import ../../laws/DefinesEachTableOnce.bend as L4
import ../../laws/FloReadsBack.bend as L5
import ../../laws/FloatReadExactly.bend as L6
import ../../laws/IntReadsBack.bend as L7
import ../../laws/IntegerReadExactly.bend as L8
import ../../laws/PassValue.bend as L9
import ../../laws/ScalarReadsBack.bend as L10
import ../../laws/SealPutsNewestLast.bend as L11
import ../../laws/StringRenderEscapes.bend as L12
import ../../laws/TbOpenAfterSet.bend as L13
import ../../laws/TbRowsAfterSet.bend as L14
import ../../laws/ValueReadsBack.bend as L15
import ../../laws/WalkPutAtHead.bend as L16
import ../../laws/WhenReadsBack.bend as L17
import ../../laws/WordReadsBack.bend as L18
import ../../laws/defs/BareValueGrammar.bend as D1
import ../../laws/defs/DocumentSameness.bend as D2
import ../../laws/defs/KeySegmentSpelling.bend as D3
import ../../laws/defs/PartialDerivationRules.bend as D4
import ../../laws/defs/ScalarReadbackScan.bend as D5
import ../../laws/defs/SealedValues.bend as D6
import ./BareValueScan.bend as M1
import ./BoolWordText.bend as M2
import ./ControlEscapeText.bend as M3
import ./DateClockText.bend as M4
import ./DecimalArithmetic.bend as M5
import ./DigitsNotDelimiters.bend as M6
import ./FailedWalkNameCompare.bend as M7
import ./FreshNamesInRows.bend as M8
import ./HeldCharacterSteps.bend as M9
import ./NavigationWalkFrames.bend as M10
import ./PickAndDigitSteps.bend as M11
import ./PrefixAndTake.bend as M12
import ./ReorderedTableNames.bend as M13
import ./SealNewestLast.bend as M14
import ./ShortTextBounds.bend as M15
import ./StringEqualsItself.bend as M16
import ./TableLookupAfterSet.bend as M17
import ./ValuePassText.bend as M18

# a buffer the body was pushed onto reads back as the body, then what follows
def ml.rev(
  xs: String,
  acc: List<&2, Char>,
  tail: String
) -> {T.buf.str.go(M8.rev.onto(xs, acc), tail) == T.buf.str.go(acc, String.append(xs, tail))
  : String}:
  match xs:
    case SNil{}:
      {==}
    case SCon{hh, tt}:
      ml.rev(tt, hh <> acc, tail)

# a code point that is one of two a predicate fails fails it too
def or2.no(
  +xx: U32,
  +k1: U32,
  +k2: U32,
  aa: Bool,
  bb: Bool,
  ea: {U32.is_eq(xx, k1) == aa : Bool},
  eb: {U32.is_eq(xx, k2) == bb : Bool},
  ee: {Bool.or(aa, bb) == True{} : Bool},
  pp: Char -> Bool,
  yes: {pp(Chr{xx}) == True{} : Bool},
  n1: {pp(Chr{k1}) == False{} : Bool},
  n2: {pp(Chr{k2}) == False{} : Bool}
) -> Empty:
  match aa:
    case True{}:
      Eq.refute_char(Chr{xx}, Chr{k1}, pp, ea, yes, n1)
    case False{}:
      Eq.refute_char(Chr{xx}, Chr{k2}, pp, Equal.trans(Bool, U32.is_eq(xx, k2), bb, True{},
        eb, ee), yes, n2)

# the top-level dispatch sends a bare-key character to a new key
def key.top(
  sp: Bool,
  nl: Bool,
  hash: Bool,
  br: Bool,
  qq: Bool,
  lit: Bool,
  bare: Bool,
  st: T.St,
  +xx: U32,
  esp: {T.ch.sp(Chr{xx}) == sp : Bool},
  enl: {T.ch.nl(Chr{xx}) == nl : Bool},
  ehash: {Char.is_eq(Chr{xx}, '#') == hash : Bool},
  ebr: {Char.is_eq(Chr{xx}, '[') == br : Bool},
  eqq: {Char.is_eq(Chr{xx}, '"') == qq : Bool},
  elit: {Char.is_eq(Chr{xx}, '\'') == lit : Bool},
  ebare: {T.bare.at(Chr{xx}) == bare : Bool},
  +ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.lex.top.go(sp, nl, hash, br, qq, lit, bare, st, Chr{xx})
  == T.st.push(st, Chr{xx}, T.LKey{}) : T.St}:
  match sp:
    case True{}:
      Eq.bit.gone(&2, {T.lex.top.go(True{}, nl, hash, br, qq, lit, bare, st, Chr{xx})
        == T.st.push(st, Chr{xx}, T.LKey{}) : T.St},
        or2.no(xx, 32, 9, U32.is_eq(xx, 32), U32.is_eq(xx, 9), {==}, {==}, esp,
          ch => T.bare.at(ch), ee, {==}, {==}))
    case False{}:
      match nl:
        case True{}:
          Eq.bit.gone(&2, {T.lex.top.go(False{}, True{}, hash, br, qq, lit, bare, st,
            Chr{xx}) == T.st.push(st, Chr{xx}, T.LKey{}) : T.St},
            or2.no(xx, 10, 13, U32.is_eq(xx, 10), U32.is_eq(xx, 13), {==}, {==}, enl,
              ch => T.bare.at(ch), ee, {==}, {==}))
        case False{}:
          match hash:
            case True{}:
              Eq.bit.gone(&2, {T.lex.top.go(False{}, False{}, True{}, br, qq, lit, bare,
                st, Chr{xx}) == T.st.push(st, Chr{xx}, T.LKey{}) : T.St},
                Eq.refute_char(Chr{xx}, '#', ch => T.bare.at(ch), ehash, ee, {==}))
            case False{}:
              match br:
                case True{}:
                  Eq.bit.gone(&2, {T.lex.top.go(False{}, False{}, False{}, True{}, qq, lit,
                    bare, st, Chr{xx}) == T.st.push(st, Chr{xx}, T.LKey{}) : T.St},
                    Eq.refute_char(Chr{xx}, '[', ch => T.bare.at(ch), ebr, ee, {==}))
                case False{}:
                  match qq:
                    case True{}:
                      Eq.bit.gone(&2, {T.lex.top.go(False{}, False{}, False{}, False{},
                        True{}, lit, bare, st, Chr{xx}) == T.st.push(st, Chr{xx},
                        T.LKey{}) : T.St},
                        Eq.refute_char(Chr{xx}, '"', ch => T.bare.at(ch), eqq, ee, {==}))
                    case False{}:
                      match lit:
                        case True{}:
                          Eq.bit.gone(&2, {T.lex.top.go(False{}, False{}, False{}, False{},
                            False{}, True{}, bare, st, Chr{xx}) == T.st.push(st, Chr{xx},
                            T.LKey{}) : T.St},
                            Eq.refute_char(Chr{xx}, '\'', ch => T.bare.at(ch), elit, ee,
                              {==}))
                        case False{}:
                          match bare:
                            case True{}:
                              {==}
                            case False{}:
                              M16.clash(&2, {T.lex.top.go(False{}, False{}, False{}, False{},
                                False{}, False{}, False{}, st, Chr{xx})
                                == T.st.push(st, Chr{xx}, T.LKey{}) : T.St},
                                Equal.trans(Bool, False{}, T.bare.at(Chr{xx}), True{},
                                  Equal.sym(Bool, T.bare.at(Chr{xx}), False{}, ebare), ee))

# the head of a bare-key walk that answered True answered True
def ball.head(
  here: Bool,
  tt: List<&2, Char>,
  ee: {T.bare.all.step(here, _u => T.bare.all(tt)) == True{} : Bool}
) -> {here == True{} : Bool}:
  match here:
    case True{}:
      {==}
    case False{}:
      ee

# and so did the rest of it
def ball.tail(
  here: Bool,
  tt: List<&2, Char>,
  ee: {T.bare.all.step(here, _u => T.bare.all(tt)) == True{} : Bool}
) -> {T.bare.all(tt) == True{} : Bool}:
  match here:
    case True{}:
      ee
    case False{}:
      Eq.bit.absurd(&2, {T.bare.all(tt) == True{} : Bool}, ee)

# a buffer something was pushed onto is not empty
def rev.full(
  xs: String,
  hh: Char,
  acc: List<&2, Char>
) -> {List.is_empty(&2, Char, M8.rev.onto(xs, hh <> acc)) == False{} : Bool}:
  match xs:
    case SNil{}:
      {==}
    case SCon{h2, t2}:
      rev.full(t2, h2, hh <> acc)

# an `or` of two bits that each answered False
def or.ff(
  aa: Bool,
  bb: Bool,
  ea: {aa == False{} : Bool},
  eb: {bb == False{} : Bool}
) -> {Bool.or(aa, bb) == False{} : Bool}:
  match aa:
    case True{}:
      Eq.bit.absurd2(&2, {Bool.or(True{}, bb) == False{} : Bool}, ea)
    case False{}:
      eb

# span.str of no characters, whatever the count
def sp.nil(nn: U32, bz: Bool) -> {T.span.str(SNil{}, nn, bz) == M12.take(SNil{}, U32.to_nat(nn)) : String}:
  match bz:
    case True{}:
      {==}
    case False{}:
      {==}

# span.str of a character and the rest, once the zero test's answer is named
def sp.cons(
  +hd: Char,
  +tl: String,
  +nn: U32,
  bz: Bool,
  ez: {U32.is_zero(nn) == bz : Bool},
  ih: {T.span.str(tl, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1))) == M12.take(tl, U32.to_nat(U32.sub(nn, 1))) : String}
) -> {T.span.str(SCon{hd, tl}, nn, bz) == M12.take(SCon{hd, tl}, U32.to_nat(nn)) : String}:
  match bz:
    case True{}:
      e0 = Equal.cong(Char, U32, cc => Char.to_u32(cc), Chr{nn}, Chr{0}, Eq.u32_eq(nn, 0, ez))
      %Equal.sym(U32, nn, 0, e0) : {T.span.str(SCon{hd, tl}, nn, True{}) == M12.take(SCon{hd, tl},
        U32.to_nat(_)) : String}
      {==}
    case False{}:
      en = Equal.sym(Nat, U32.to_nat(nn), 1n+U32.to_nat(U32.sub(nn, 1)), Eq.u32_dec_nat(nn, ez))
      %en : {SCon{hd, T.span.str(tl, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)))}
        == M12.take(SCon{hd, tl}, _) : String}
      Equal.cong(String, String, xs => SCon{hd, xs},
        T.span.str(tl, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1))),
        M12.take(tl, U32.to_nat(U32.sub(nn, 1))), ih)

# a span's characters are the first n characters of its source
def sp.take(
  src: String,
  +nn: U32
) -> {T.span.str(src, nn, U32.is_zero(nn)) == M12.take(src, U32.to_nat(nn)) : String}:
  match src:
    case SNil{}:
      sp.nil(nn, U32.is_zero(nn))
    case SCon{+hd, +tl}:
      sp.cons(hd, tl, nn, U32.is_zero(nn), {==}, sp.take(tl, U32.sub(nn, 1)))

# a count one further on
def plus.succ(ss: String, nn: Nat) -> {M15.plus(ss, 1n+nn) == 1n+M15.plus(ss, nn) : Nat}:
  match ss:
    case SNil{}:
      {==}
    case SCon{_hh, tt}:
      plus.succ(tt, 1n+nn)

# taking a text's count of characters from the text and more takes the text
def take.app(
  ss: String,
  +xs: String,
  +kk: Nat
) -> {M12.take(String.append(ss, xs), M15.plus(ss, kk)) == String.append(ss, M12.take(xs, kk)) : String}:
  match ss:
    case SNil{}:
      {==}
    case SCon{+hh, +tt}:
      %Equal.sym(Nat, M15.plus(tt, 1n+kk), 1n+M15.plus(tt, kk), plus.succ(tt, kk)) :
        {M12.take(SCon{hh, String.append(tt, xs)}, _) == SCon{hh, String.append(tt, M12.take(xs, kk))}
          : String}
      Equal.cong(String, String, ys => SCon{hh, ys}, M12.take(String.append(tt, xs), M15.plus(tt, kk)),
        String.append(tt, M12.take(xs, kk)), take.app(tt, xs, kk))

# a bare segment's buffer reads back as its characters
def wh.bname(
  +xx: U32,
  +tt: String
) -> {T.buf.str(M8.rev.onto(tt, [Chr{xx}])) == SCon{Chr{xx}, tt} : String}:
  Equal.trans(String, T.buf.str.go(M8.rev.onto(tt, [Chr{xx}]), ""),
    T.buf.str.go([Chr{xx}], String.append(tt, "")), SCon{Chr{xx}, tt},
    ml.rev(tt, [Chr{xx}], ""),
    Equal.cong(String, String, zz => SCon{Chr{xx}, zz}, String.append(tt, ""), tt,
      Eq.append_nil(tt)))

# WP-S: a rendered string read back in any value position. render writes a
# string as key.basic of its characters (laws/StringRenderEscapes.bend); the lemmas below read
# that text back from the scanner just past the opening quote of a value, in
# a root pair, an array item or an inline table's pair alike: every field the
# string leaves alone is a parameter (bd the error, rw the rows, hs heads, he
# here, ps parts, sk the stack of open arrays and inline tables, ab arrtab).
# The string ends with its value placed by take.top, which is where the three
# positions part: the rest of the walk is a function of the value and of the
# fields the string may change (back, and uni and left after a \u escape), as
# in WP0's quoted-segment family. The value is a span of the text while no
# character needs an escape, and an owned string once one does; either way
# it holds the string's characters (sv.Is), and own reads it as them
# (sv.own.pair, sv.own.item). The rest of the walk ends in a motive PP over
# the document, so a caller proves what it needs of it (its owned form, for
# WP-D's exact lemma) whichever value the string became.

# the scanner just past the opening quote of a basic string in a value
# position
def sv.open(
  bd: String,
  rw: List<&2, T.Val>,
  hs: List<&2, String>,
  he: List<&2, String>,
  ps: List<&2, String>,
  bk: T.Lex,
  sk: List<&2, T.Ctx>,
  un: U32,
  lf: U32,
  ab: Bool
) -> T.Mode:
  T.MOpen{True{}, '"', T.QBasic{}, bd, rw, hs, he, ps, [], bk, sk, un, lf, ab}

# the scanner inside the span of such a string: cut is the text from its
# first character, nn the characters counted so far
def sv.eat(
  cut: String,
  nn: U32,
  bd: String,
  rw: List<&2, T.Val>,
  hs: List<&2, String>,
  he: List<&2, String>,
  ps: List<&2, String>,
  sk: List<&2, T.Ctx>,
  un: U32,
  lf: U32,
  ab: Bool
) -> T.Mode:
  T.MEat{True{}, '"', cut, nn, bd, rw, hs, he, ps, T.QBasic{}, sk, un, lf, ab}

# the scanner once the string's value vv is placed: take.top puts it into the
# root table, the open array or the open inline table, as sk says
def sv.took(
  sk: List<&2, T.Ctx>,
  vv: T.Val,
  bd: String,
  rw: List<&2, T.Val>,
  hs: List<&2, String>,
  +he: List<&2, String>,
  ps: List<&2, String>,
  bk: T.Lex,
  un: U32,
  lf: U32,
  ab: Bool
) -> T.St:
  T.take.top(sk, vv, bd, rw, hs, he, ps, bk, T.QBasic{}, un, lf, ab, False{})

# a string value holding the characters ss: an owned string of them, or a
# span of a text whose first n characters they are. No other value is one
def sv.Is(vv: T.Val, ss: String) -> Type:
  match vv:
    case T.VStr{tt}:
      {tt == ss : String}
    case T.VSpan{src, +nn}:
      {T.span.str(src, nn, U32.is_zero(nn)) == ss : String}
    case _:
      Empty

# the rest of the walk, for the string ss: reading rest from the scanner with
# any string value holding ss placed (sv.Is), and any back, uni and left, gives a
# document PP holds of. PP is what the caller proves of the document: its
# owned form, say, as WP-D's exact lemma needs, since the value itself is a
# span or an owned string depending on the escapes
def sv.Then(
  +ss: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  @vv: T.Val -> @bk: T.Lex -> @un: U32 -> @lf: U32 ->
    sv.Is(vv, ss) ->
    PP(T.doc.read(rest, T.MScan{sv.took(sk, vv, bd, rw, hs, he, ps, bk, un, lf, ab)}))

# what holds of a document holds of one equal to it
def pp.step(
  -PP: T.Doc -> Type,
  aa: T.Doc,
  bb: T.Doc,
  ee: {aa == bb : T.Doc},
  kk: PP(bb)
) -> PP(aa):
  %Equal.sym(T.Doc, aa, bb, ee) : PP(_)
  kk

# the rest of the walk for one string serves for another equal to it
def sv.then.cast(
  +s1: String,
  +s2: String,
  e12: {s1 == s2 : String},
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  ih: sv.Then(s1, bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> sv.Then(s2, bd, rw, hs, he, ps, sk, ab, rest, PP):
  %e12 : sv.Then(_, bd, rw, hs, he, ps, sk, ab, rest, PP)
  ih

# A placed value holds no character for the next step to read again, and it
# is no quote that opens a string: the full step's read.once2 and doc.wrap
# leave it as it is. The walk's result is a parameter, so this holds
# whatever the walk did.

# at the root
def tk.root(
  end: T.End,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +ld: Bool
) -> {T.doc.wrap(T.read.once2(T.take.root(end, he, bk, qk, un, lf, ab, ld)))
  == T.MScan{T.take.root(end, he, bk, qk, un, lf, ab, ld)} : T.Mode}:
  match end:
    case T.End{_vs, _bad, _heads}:
      {==}

# in an inline table
def tk.inl(
  end: T.End,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +rest: List<&2, T.Ctx>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +ld: Bool
) -> {T.doc.wrap(T.read.once2(T.take.inl(end, rw, hs, he, ps, rest, bk, qk, un, lf, ab, ld)))
  == T.MScan{T.take.inl(end, rw, hs, he, ps, rest, bk, qk, un, lf, ab, ld)} : T.Mode}:
  match end:
    case T.End{_vs, _bad, _heads}:
      {==}

# wherever the value goes
def tk.fix(
  sk: List<&2, T.Ctx>,
  +vv: T.Val,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +ld: Bool
) -> {T.doc.wrap(T.read.once2(T.take.top(sk, vv, bd, rw, hs, he, ps, bk, qk, un, lf, ab, ld)))
  == T.MScan{T.take.top(sk, vv, bd, rw, hs, he, ps, bk, qk, un, lf, ab, ld)} : T.Mode}:
  match sk:
    case []:
      tk.root(T.tree.walk(T.path.cat(he, ps), T.Tw{rw, T.JPut{vv}, [], bd, "", hs, False{}},
        T.path.len(he, 0)), he, bk, qk, un, lf, ab, ld)
    case T.CArr{_items, _saved, _at} <> _rest:
      {==}
    case T.CInl{inl, +saved, +at} <> +rest:
      tk.inl(T.tree.walk(List.reverse(&2, String, ps), T.Tw{inl, T.JPut{vv}, [], bd, "", [],
        True{}}, 0), rw, hs, at, saved, rest, bk, qk, un, lf, ab, ld)

# The span. A first character written as itself opens it, each later one
# adds one to its count, and the closing quote places it.

# the first character: no control, so the span starts
def so.ok(
  badc: Bool,
  +uu: U32,
  +tail: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  hc: {badc == False{} : Bool}
) -> {T.doc.open.ok(T.str.bad.go(badc, U32.is_eq(uu, 9), Bool.or(U32.is_eq(uu, 10),
  U32.is_eq(uu, 13)), False{}), True{}, '"', T.QBasic{}, bd, rw, hs, he, ps, [], bk, sk, un, lf,
  ab, Chr{uu}, tail) == sv.eat(SCon{Chr{uu}, tail}, 1, bd, rw, hs, he, ps, sk, un, lf, ab) : T.Mode}:
  match badc:
    case False{}:
      {==}
    case True{}:
      Eq.bit.absurd2(&2, {T.doc.open.ok(T.str.bad.go(True{}, U32.is_eq(uu, 9),
        Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)), False{}), True{}, '"', T.QBasic{}, bd, rw,
        hs, he, ps, [], bk, sk, un, lf, ab, Chr{uu}, tail)
        == sv.eat(SCon{Chr{uu}, tail}, 1, bd, rw, hs, he, ps, sk, un, lf, ab) : T.Mode}, hc)

# no backslash
def so.bs(
  bs: Bool,
  +uu: U32,
  +tail: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  hb: {bs == False{} : Bool},
  hc: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool}
) -> {T.doc.open.bs(bs, '"', T.QBasic{}, bd, rw, hs, he, ps, [], bk, sk, un, lf, ab, Chr{uu}, tail)
  == sv.eat(SCon{Chr{uu}, tail}, 1, bd, rw, hs, he, ps, sk, un, lf, ab) : T.Mode}:
  match bs:
    case False{}:
      so.ok(Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), uu, tail, bd, rw, hs, he, ps, bk, sk,
        un, lf, ab, hc)
    case True{}:
      Eq.bit.absurd2(&2, {T.doc.open.bs(True{}, '"', T.QBasic{}, bd, rw, hs, he, ps, [], bk, sk,
        un, lf, ab, Chr{uu}, tail) == sv.eat(SCon{Chr{uu}, tail}, 1, bd, rw, hs, he, ps, sk, un, lf,
        ab) : T.Mode}, hb)

# no quotation mark
def so.q(
  same: Bool,
  +uu: U32,
  +tail: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  hq: {same == False{} : Bool},
  hb: {U32.is_eq(uu, 92) == False{} : Bool},
  hc: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool}
) -> {T.doc.open.q(same, True{}, '"', T.QBasic{}, bd, rw, hs, he, ps, [], bk, sk, un, lf, ab,
  Chr{uu}, tail) == sv.eat(SCon{Chr{uu}, tail}, 1, bd, rw, hs, he, ps, sk, un, lf, ab) : T.Mode}:
  match same:
    case False{}:
      so.bs(U32.is_eq(uu, 92), uu, tail, bd, rw, hs, he, ps, bk, sk, un, lf, ab, hb, hc)
    case True{}:
      Eq.bit.absurd2(&2, {T.doc.open.q(True{}, True{}, '"', T.QBasic{}, bd, rw, hs, he, ps, [], bk,
        sk, un, lf, ab, Chr{uu}, tail) == sv.eat(SCon{Chr{uu}, tail}, 1, bd, rw, hs, he, ps, sk, un,
        lf, ab) : T.Mode}, hq)

# a first character that is no quotation mark, backslash or control opens the
# span
def so.one(
  +uu: U32,
  +tail: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  e34: {U32.is_eq(uu, 34) == False{} : Bool},
  e92: {U32.is_eq(uu, 92) == False{} : Bool},
  ec: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool}
) -> {T.doc.read(SCon{Chr{uu}, tail}, sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab))
  == T.doc.read(tail, sv.eat(SCon{Chr{uu}, tail}, 1, bd, rw, hs, he, ps, sk, un, lf, ab)) : T.Doc}:
  Equal.cong(T.Mode, T.Doc, md => T.doc.read(tail, md),
    T.doc.open(True{}, '"', T.QBasic{}, bd, rw, hs, he, ps, [], bk, sk, un, lf, ab, Chr{uu}, tail),
    sv.eat(SCon{Chr{uu}, tail}, 1, bd, rw, hs, he, ps, sk, un, lf, ab),
    so.q(U32.is_eq(uu, 34), uu, tail, bd, rw, hs, he, ps, bk, sk, un, lf, ab, e34, e92, ec))

# a later character: no control, so the span grows
def se.ctl(
  ctl: Bool,
  +uu: U32,
  +cut: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  hc: {ctl == False{} : Bool}
) -> {T.eat.ctrl(T.str.bad.go(ctl, U32.is_eq(uu, 9), Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)),
  False{}), True{}, '"', Chr{uu}, cut, nn, bd, rw, hs, he, ps, T.QBasic{}, sk, un, lf, ab)
  == sv.eat(cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un, lf, ab) : T.Mode}:
  match ctl:
    case False{}:
      {==}
    case True{}:
      Eq.bit.absurd2(&2, {T.eat.ctrl(T.str.bad.go(True{}, U32.is_eq(uu, 9),
        Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)), False{}), True{}, '"', Chr{uu}, cut, nn, bd,
        rw, hs, he, ps, T.QBasic{}, sk, un, lf, ab)
        == sv.eat(cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un, lf, ab) : T.Mode}, hc)

# no backslash
def se.bs(
  bs: Bool,
  +uu: U32,
  +cut: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  hb: {bs == False{} : Bool},
  hc: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool}
) -> {T.eat.bs(bs, True{}, '"', Chr{uu}, cut, nn, bd, rw, hs, he, ps, T.QBasic{}, sk, un, lf, ab)
  == sv.eat(cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un, lf, ab) : T.Mode}:
  match bs:
    case False{}:
      se.ctl(Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), uu, cut, nn, bd, rw, hs, he, ps, sk,
        un, lf, ab, hc)
    case True{}:
      Eq.bit.absurd2(&2, {T.eat.bs(True{}, True{}, '"', Chr{uu}, cut, nn, bd, rw, hs, he, ps,
        T.QBasic{}, sk, un, lf, ab) == sv.eat(cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un, lf,
        ab) : T.Mode}, hb)

# no quotation mark
def se.q(
  quote: Bool,
  +uu: U32,
  +cut: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  hq: {quote == False{} : Bool},
  hb: {U32.is_eq(uu, 92) == False{} : Bool},
  hc: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool}
) -> {T.eat.feed.q(quote, True{}, '"', Chr{uu}, cut, nn, bd, rw, hs, he, ps, T.QBasic{}, sk, un,
  lf, ab) == sv.eat(cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un, lf, ab) : T.Mode}:
  match quote:
    case False{}:
      se.bs(U32.is_eq(uu, 92), uu, cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab, hb, hc)
    case True{}:
      Eq.bit.absurd2(&2, {T.eat.feed.q(True{}, True{}, '"', Chr{uu}, cut, nn, bd, rw, hs, he, ps,
        T.QBasic{}, sk, un, lf, ab) == sv.eat(cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un, lf,
        ab) : T.Mode}, hq)

# a later character written as itself grows the span by one
def se.one(
  +uu: U32,
  +tail: String,
  +cut: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  e34: {U32.is_eq(uu, 34) == False{} : Bool},
  e92: {U32.is_eq(uu, 92) == False{} : Bool},
  ec: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool}
) -> {T.doc.read(SCon{Chr{uu}, tail}, sv.eat(cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab))
  == T.doc.read(tail, sv.eat(cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un, lf, ab)) : T.Doc}:
  Equal.cong(T.Mode, T.Doc, md => T.doc.read(tail, md),
    T.eat.feed(True{}, '"', cut, nn, bd, rw, hs, he, ps, T.QBasic{}, sk, un, lf, ab, Chr{uu}),
    sv.eat(cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un, lf, ab),
    se.q(U32.is_eq(uu, 34), uu, cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab, e34, e92, ec))

# the closing quote places the span, with back at LStr
def se.close(
  +rest: String,
  +cut: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool
) -> {T.doc.read(SCon{'"', rest}, sv.eat(cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab))
  == T.doc.read(rest, T.MScan{sv.took(sk, T.VSpan{cut, nn}, bd, rw, hs, he, ps, T.LStr{}, un, lf,
    ab)}) : T.Doc}:
  {==}

# The span's characters. Counting a text's characters in a Nat (plus, from
# render_parse_plain_pair's proof) runs through an append one part at a time.

# the count after two texts is the count after the second, from the count
# after the first
def plus.app(
  xs: String,
  +ys: String,
  nn: Nat
) -> {M15.plus(String.append(xs, ys), nn) == M15.plus(ys, M15.plus(xs, nn)) : Nat}:
  match xs:
    case SNil{}:
      {==}
    case SCon{_hh, tt}:
      plus.app(tt, ys, 1n+nn)

# no characters of any text
def take.zero(ss: String) -> {M12.take(ss, 0n) == SNil{} : String}:
  match ss:
    case SNil{}:
      {==}
    case SCon{_hh, _tt}:
      {==}

# a span of a text that starts with pre, counting pre's characters, is pre
def sp.pre(
  +pre: String,
  +cut: String,
  +more: String,
  +nn: U32,
  hc: {cut == String.append(pre, more) : String},
  hn: {U32.to_nat(nn) == M15.plus(pre, 0n) : Nat}
) -> {M12.take(cut, U32.to_nat(nn)) == pre : String}:
  Equal.trans(String, M12.take(cut, U32.to_nat(nn)), M12.take(String.append(pre, more), M15.plus(pre, 0n)), pre,
    Equal.trans(String, M12.take(cut, U32.to_nat(nn)), M12.take(String.append(pre, more), U32.to_nat(nn)),
      M12.take(String.append(pre, more), M15.plus(pre, 0n)),
      Equal.cong(String, String, xs => M12.take(xs, U32.to_nat(nn)), cut, String.append(pre, more), hc),
      Equal.cong(Nat, String, kk => M12.take(String.append(pre, more), kk), U32.to_nat(nn), M15.plus(pre, 0n),
        hn)),
    Equal.trans(String, M12.take(String.append(pre, more), M15.plus(pre, 0n)),
      String.append(pre, M12.take(more, 0n)), pre,
      take.app(pre, more, 0n),
      Equal.trans(String, String.append(pre, M12.take(more, 0n)), String.append(pre, SNil{}), pre,
        Equal.cong(String, String, xs => String.append(pre, xs), M12.take(more, 0n), SNil{},
          take.zero(more)),
        Eq.append_nil(pre))))

# the placed span holds the characters counted into it
def se.own(
  +pre: String,
  +cut: String,
  +more: String,
  +nn: U32,
  hc: {cut == String.append(pre, more) : String},
  hn: {U32.to_nat(nn) == M15.plus(pre, 0n) : Nat}
) -> sv.Is(T.VSpan{cut, nn}, pre):
  Equal.trans(String, T.span.str(cut, nn, U32.is_zero(nn)), M12.take(cut, U32.to_nat(nn)), pre,
    sp.take(cut, nn), sp.pre(pre, cut, more, nn, hc, hn))

# the rest of the walk from a string with buf in its buffer, whatever uni
# and left are
def ls.Then(
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  @u2: U32 -> @l2: U32 ->
    PP(T.doc.read(rest, T.MScan{M11.ls(bd, rw, hs, he, ps, sk, ab, u2, l2, buf)}))

# one character's escape read in a string, then the rest of the text: the
# rest is read with the character pushed, from whatever uni and left the
# escape left
def ls.Goal(
  +uu: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  (@u2: U32 -> @l2: U32 ->
    PP(T.doc.read(rest, T.MScan{M11.ls(bd, rw, hs, he, ps, sk, ab, u2, l2, Chr{uu} <> buf)}))) ->
    PP(T.doc.read(String.append(L12.esc(Chr{uu}), rest), T.MScan{M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf, buf)}))

# a character that is no control is pushed: str.bad passes it
def ls.push(
  ctl: Bool,
  +uu: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  hc: {ctl == False{} : Bool}
) -> {T.read.fast.push(T.str.bad.go(ctl, U32.is_eq(uu, 9), Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)),
  False{}), bd, rw, hs, he, ps, buf, T.LStr{}, T.LStr{}, T.QBasic{}, sk, un, lf, ab, Chr{uu})
  == M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf, Chr{uu} <> buf) : T.St}:
  match ctl:
    case False{}:
      {==}
    case True{}:
      Eq.bit.absurd2(&2, {T.read.fast.push(T.str.bad.go(True{}, U32.is_eq(uu, 9),
        Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)), False{}), bd, rw, hs, he, ps, buf, T.LStr{},
        T.LStr{}, T.QBasic{}, sk, un, lf, ab, Chr{uu}) == M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf,
        Chr{uu} <> buf) : T.St}, hc)

# a character that is no quote and no backslash is no closer and no escape
def ls.go(
  quote: Bool,
  bs: Bool,
  +uu: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  hq: {quote == False{} : Bool},
  hb: {bs == False{} : Bool},
  hc: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool}
) -> {T.read.fast.basic(quote, bs, bd, rw, hs, he, ps, buf, T.LStr{}, sk, un, lf, ab, Chr{uu})
  == M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf, Chr{uu} <> buf) : T.St}:
  match quote:
    case True{}:
      Eq.bit.absurd2(&2, {T.read.fast.basic(True{}, bs, bd, rw, hs, he, ps, buf, T.LStr{}, sk, un,
        lf, ab, Chr{uu}) == M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf, Chr{uu} <> buf) : T.St}, hq)
    case False{}:
      match bs:
        case True{}:
          Eq.bit.absurd2(&2, {T.read.fast.basic(False{}, True{}, bd, rw, hs, he, ps, buf, T.LStr{},
            sk, un, lf, ab, Chr{uu}) == M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf, Chr{uu} <> buf)
            : T.St}, hb)
        case False{}:
          ls.push(Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), uu, bd, rw, hs, he, ps, sk, ab, un,
            lf, buf, hc)

# the fast step pushes a character
def ls.Fast(
  +uu: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>
) -> Type:
  {T.read.fast(M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf, buf), Chr{uu})
    == M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf, Chr{uu} <> buf) : T.St}

# the doc.scan dispatch sends such a character to the fast step, and an
# apostrophe comes back from doc.wrap in the string's state
def ls.q(
  dq: Bool,
  sq: Bool,
  cr: Bool,
  +uu: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  hq: {dq == False{} : Bool},
  hr: {cr == False{} : Bool},
  fast: ls.Fast(uu, bd, rw, hs, he, ps, sk, ab, un, lf, buf)
) -> {T.doc.scan.q(dq, sq, cr, M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf, buf), Chr{uu})
  == T.MScan{M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf, Chr{uu} <> buf)} : T.Mode}:
  match dq:
    case True{}:
      Eq.bit.absurd2(&2, {T.doc.scan.q(True{}, sq, cr, M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf, buf),
        Chr{uu}) == T.MScan{M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf, Chr{uu} <> buf)} : T.Mode}, hq)
    case False{}:
      match sq:
        case True{}:
          Equal.cong(T.St, T.Mode, st => T.doc.wrap(st),
            T.read.fast(M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf, buf), Chr{uu}),
            M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf, Chr{uu} <> buf), fast)
        case False{}:
          match cr:
            case True{}:
              Eq.bit.absurd2(&2, {T.doc.scan.q(False{}, False{}, True{}, M11.ls(bd, rw, hs, he, ps, sk,
                ab, un, lf, buf), Chr{uu}) == T.MScan{M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf,
                Chr{uu} <> buf)} : T.Mode}, hr)
            case False{}:
              Equal.cong(T.St, T.Mode, st => T.MScan{st},
                T.read.fast(M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf, buf), Chr{uu}),
                M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf, Chr{uu} <> buf), fast)

# a character that is no control, quotation mark or backslash is written as
# itself
def esc.pl2(
  +uu: U32,
  e34: {U32.is_eq(uu, 34) == False{} : Bool},
  e92: {U32.is_eq(uu, 92) == False{} : Bool},
  +ec: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool}
) -> {L12.esc(Chr{uu}) == SCon{Chr{uu}, SNil{}} : String}:
  ek = M3.cls.plain(uu, M3.ctl.off(uu, 8, ec, {==}), M3.ctl.off(uu, 9, ec, {==}), M3.ctl.off(uu, 10, ec, {==}),
    M3.ctl.off(uu, 12, ec, {==}), M3.ctl.off(uu, 13, ec, {==}), e34, e92, ec)
  %Equal.sym(T.BK, T.basic.cls(uu), T.BKCh{}, ek) :
    {String.from_list(List.reverse(&2, Char, T.basic.disp(_, Chr{uu}, uu, []))) == SCon{Chr{uu}, SNil{}}
      : String}
  {==}

# a character written as itself is pushed, and uni and left stay as they
# were
def ls.plain(
  +uu: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  +e34: {U32.is_eq(uu, 34) == False{} : Bool},
  +e92: {U32.is_eq(uu, 92) == False{} : Bool},
  +ec: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool},
  ih: ls.Then(bd, rw, hs, he, ps, sk, ab, Chr{uu} <> buf, rest, PP)
) -> PP(T.doc.read(String.append(L12.esc(Chr{uu}), rest), T.MScan{M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf, buf)})):
  +e13 = {M3.ctl.off(uu, 13, ec, {==}) : {U32.is_eq(uu, 13) == False{} : Bool}}
  %Equal.sym(String, L12.esc(Chr{uu}), SCon{Chr{uu}, SNil{}}, esc.pl2(uu, e34, e92, ec)) :
    PP(T.doc.read(String.append(_, rest), T.MScan{M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf, buf)}))
  pp.step(PP,
    T.doc.read(rest, T.doc.scan(M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf, buf), Chr{uu})),
    T.doc.read(rest, T.MScan{M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf, Chr{uu} <> buf)}),
    Equal.cong(T.Mode, T.Doc, md => T.doc.read(rest, md),
      T.doc.scan(M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf, buf), Chr{uu}),
      T.MScan{M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf, Chr{uu} <> buf)},
      ls.q(U32.is_eq(uu, 34), U32.is_eq(uu, 39), U32.is_eq(uu, 13), uu, bd, rw, hs, he, ps, sk, ab, un,
        lf, buf, e34, e13,
        ls.go(U32.is_eq(uu, 34), U32.is_eq(uu, 92), uu, bd, rw, hs, he, ps, sk, ab, un, lf, buf, e34,
          e92, ec))),
    ih(un, lf))

# a quotation mark: its escape reads back by computation, and leaves uni and
# left as they were
def ls.q34(
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type
) -> ls.Goal(34, bd, rw, hs, he, ps, sk, ab, un, lf, buf, rest, PP):
  ih => ih(un, lf)

# and a backslash
def ls.q92(
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type
) -> ls.Goal(92, bd, rw, hs, he, ps, sk, ab, un, lf, buf, rest, PP):
  ih => ih(un, lf)

# CTL: ls.Goal with the escape's text as ss, for ctl.esc.all
def ls.GoalS(
  +uu: U32,
  ss: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  (@u2: U32 -> @l2: U32 ->
    PP(T.doc.read(rest, T.MScan{M11.ls(bd, rw, hs, he, ps, sk, ab, u2, l2, Chr{uu} <> buf)}))) ->
    PP(T.doc.read(String.append(ss, rest), T.MScan{M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf, buf)}))

# a control: each of the thirty-three escapes reads back by computation. The
# five with a letter (\b, \t, \n, \f, \r) leave uni and left as they were; a
# \u escape leaves both at 0
def ls.ctl(
  +uu: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  h_c: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == True{} : Bool}
) -> ls.Goal(uu, bd, rw, hs, he, ps, sk, ab, un, lf, buf, rest, PP):
  M3.ctl.esc.all(kk => ss => ls.GoalS(kk, ss, bd, rw, hs, he, ps, sk, ab, un, lf, buf, rest, PP), uu, h_c,
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(un, lf),
    ih => ih(un, lf),
    ih => ih(un, lf),
    ih => ih(0, 0),
    ih => ih(un, lf),
    ih => ih(un, lf),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0))

# one code point k that the test found: its answer answers for the character
def ls.is(
  +uu: U32,
  +kk: U32,
  ee: {U32.is_eq(uu, kk) == True{} : Bool},
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  at: ls.Goal(kk, bd, rw, hs, he, ps, sk, ab, un, lf, buf, rest, PP)
) -> ls.Goal(uu, bd, rw, hs, he, ps, sk, ab, un, lf, buf, rest, PP):
  eu = Equal.cong(Char, U32, cc => Char.to_u32(cc), Chr{uu}, Chr{kk}, Eq.u32_eq(uu, kk, ee))
  %Equal.sym(U32, uu, kk, eu) : ls.Goal(_, bd, rw, hs, he, ps, sk, ab, un, lf, buf, rest, PP)
  at

# every character: a quote, a backslash, a control, or one written as itself
def ls.split(
  +uu: U32,
  q34: Bool,
  b92: Bool,
  ctl: Bool,
  +e34: {U32.is_eq(uu, 34) == q34 : Bool},
  +e92: {U32.is_eq(uu, 92) == b92 : Bool},
  +ec: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == ctl : Bool},
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type
) -> ls.Goal(uu, bd, rw, hs, he, ps, sk, ab, un, lf, buf, rest, PP):
  match q34:
    case True{}:
      ls.is(uu, 34, e34, bd, rw, hs, he, ps, sk, ab, un, lf, buf, rest, PP,
        ls.q34(bd, rw, hs, he, ps, sk, ab, un, lf, buf, rest, PP))
    case False{}:
      match b92:
        case True{}:
          ls.is(uu, 92, e92, bd, rw, hs, he, ps, sk, ab, un, lf, buf, rest, PP,
            ls.q92(bd, rw, hs, he, ps, sk, ab, un, lf, buf, rest, PP))
        case False{}:
          match ctl:
            case True{}:
              ls.ctl(uu, bd, rw, hs, he, ps, sk, ab, un, lf, buf, rest, PP, ec)
            case False{}:
              ih => ls.plain(uu, bd, rw, hs, he, ps, sk, ab, un, lf, buf, rest, PP, e34, e92, ec, ih)

# one character of a string
def ls.one(
  +uu: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type
) -> ls.Goal(uu, bd, rw, hs, he, ps, sk, ab, un, lf, buf, rest, PP):
  ls.split(uu, U32.is_eq(uu, 34), U32.is_eq(uu, 92), Bool.or(U32.is_lt(uu, 32),
    U32.is_eq(uu, 127)), {==}, {==}, {==}, bd, rw, hs, he, ps, sk, ab, un, lf, buf, rest, PP)

# every character of a string, as escs writes it, read in LStr: the rest is
# read with the characters pushed, from whatever uni and left the last escape
# left
def ls.escs(
  ss: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  ih: ls.Then(bd, rw, hs, he, ps, sk, ab, M8.rev.onto(ss, buf), rest, PP)
) -> PP(T.doc.read(String.append(L12.escs(ss), rest), T.MScan{M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf, buf)})):
  match ss:
    case SNil{}:
      ih(un, lf)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+uu}:
          pp.step(PP,
            T.doc.read(String.append(String.append(L12.esc(Chr{uu}), L12.escs(tt)), rest),
              T.MScan{M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf, buf)}),
            T.doc.read(String.append(L12.esc(Chr{uu}), String.append(L12.escs(tt), rest)),
              T.MScan{M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf, buf)}),
            Equal.cong(String, T.Doc, xs => T.doc.read(xs, T.MScan{M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf,
              buf)}),
              String.append(String.append(L12.esc(Chr{uu}), L12.escs(tt)), rest),
              String.append(L12.esc(Chr{uu}), String.append(L12.escs(tt), rest)),
              Eq.append_assoc(L12.esc(Chr{uu}), L12.escs(tt), rest)),
            ls.one(uu, bd, rw, hs, he, ps, sk, ab, un, lf, buf, String.append(L12.escs(tt), rest), PP)(
              u2 => l2 => ls.escs(tt, bd, rw, hs, he, ps, sk, ab, u2, l2, Chr{uu} <> buf, rest, PP, ih)))

# the closing quote places the owned string, with back at LStr
def ls.close(
  +rest: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>
) -> {T.doc.read(SCon{'"', rest}, T.MScan{M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf, buf)})
  == T.doc.read(rest, T.MScan{sv.took(sk, T.VStr{T.buf.str(buf)}, bd, rw, hs, he, ps, T.LStr{}, un, lf,
    ab)}) : T.Doc}:
  Equal.cong(T.Mode, T.Doc, md => T.doc.read(rest, md),
    T.doc.wrap(T.read.once2(sv.took(sk, T.VStr{T.buf.str(buf)}, bd, rw, hs, he, ps, T.LStr{}, un, lf,
      ab))),
    T.MScan{sv.took(sk, T.VStr{T.buf.str(buf)}, bd, rw, hs, he, ps, T.LStr{}, un, lf, ab)},
    tk.fix(sk, T.VStr{T.buf.str(buf)}, bd, rw, hs, he, ps, T.LStr{}, T.QBasic{}, un, lf, ab, False{}))

# a buffer the text pre and then ss were pushed onto holds pre and ss
def ls.own(
  +pre: String,
  +ss: String
) -> sv.Is(T.VStr{T.buf.str(M8.rev.onto(ss, M8.rev.onto(pre, [])))}, String.append(pre, ss)):
  Equal.trans(String, T.buf.str.go(M8.rev.onto(ss, M8.rev.onto(pre, [])), ""),
    T.buf.str.go(M8.rev.onto(pre, []), String.append(ss, "")), String.append(pre, ss),
    ml.rev(ss, M8.rev.onto(pre, []), ""),
    Equal.trans(String, T.buf.str.go(M8.rev.onto(pre, []), String.append(ss, "")),
      String.append(pre, String.append(ss, "")), String.append(pre, ss),
      ml.rev(pre, [], String.append(ss, "")),
      Equal.cong(String, String, xs => String.append(pre, xs), String.append(ss, ""), ss,
        Eq.append_nil(ss))))

# the rest of a string, from a buffer holding pre: the escapes of ss and the
# closing quote read to the value pre and ss placed
def ls.fin(
  +ss: String,
  +pre: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +un: U32,
  +lf: U32,
  +rest: String,
  -PP: T.Doc -> Type,
  ih: sv.Then(String.append(pre, ss), bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(String.append(L12.escs(ss), SCon{'"', rest}),
  T.MScan{M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf, M8.rev.onto(pre, []))})):
  ls.escs(ss, bd, rw, hs, he, ps, sk, ab, un, lf, M8.rev.onto(pre, []), SCon{'"', rest}, PP,
    +u2 => +l2 => pp.step(PP,
      T.doc.read(SCon{'"', rest}, T.MScan{M11.ls(bd, rw, hs, he, ps, sk, ab, u2, l2,
        M8.rev.onto(ss, M8.rev.onto(pre, [])))}),
      T.doc.read(rest, T.MScan{sv.took(sk, T.VStr{T.buf.str(M8.rev.onto(ss, M8.rev.onto(pre, [])))}, bd, rw,
        hs, he, ps, T.LStr{}, u2, l2, ab)}),
      ls.close(rest, bd, rw, hs, he, ps, sk, ab, u2, l2, M8.rev.onto(ss, M8.rev.onto(pre, []))),
      ih(T.VStr{T.buf.str(M8.rev.onto(ss, M8.rev.onto(pre, [])))}, T.LStr{}, u2, l2, ls.own(pre, ss))))

# A character that needs an escape starts it with a backslash, whichever it
# is, so the span meets a backslash there and copies itself.

# a text with its first character dropped
def str.tl(ss: String) -> String:
  match ss:
    case SNil{}:
      SNil{}
    case SCon{_hh, tt}:
      tt

# render writes the character with a backslash first
def esc.Lead(+uu: U32) -> Type:
  {L12.esc(Chr{uu}) == SCon{'\\', str.tl(L12.esc(Chr{uu}))} : String}

# one code point k that the test found
def esc.lead.is(
  +uu: U32,
  +kk: U32,
  ee: {U32.is_eq(uu, kk) == True{} : Bool},
  at: esc.Lead(kk)
) -> esc.Lead(uu):
  eu = Equal.cong(Char, U32, cc => Char.to_u32(cc), Chr{uu}, Chr{kk}, Eq.u32_eq(uu, kk, ee))
  %Equal.sym(U32, uu, kk, eu) : esc.Lead(_)
  at

# every control: its escape is ctl.txt, a backslash first
def esc.lead.ctl(
  +uu: U32,
  h_c: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == True{} : Bool}
) -> esc.Lead(uu):
  %M3.ctl.esc.lit(uu, h_c) : {_ == SCon{'\\', str.tl(_)} : String}
  {==}

# span.rev copies the span's first n characters, reversed onto acc
def sp.Rv(+src: String, +nn: U32, +acc: List<&2, Char>) -> Type:
  {T.span.rev(src, nn, U32.is_zero(nn), acc) == M8.rev.onto(M12.take(src, U32.to_nat(nn)), acc) : List<&2, Char>}

# the span's first n characters, reversed onto acc, are what span.rev copies
def sp.rv.nil(
  nn: U32,
  bz: Bool,
  +acc: List<&2, Char>
) -> {T.span.rev(SNil{}, nn, bz, acc) == M8.rev.onto(M12.take(SNil{}, U32.to_nat(nn)), acc) : List<&2, Char>}:
  match bz:
    case True{}:
      {==}
    case False{}:
      {==}

# a character and the rest, once the zero test's answer is named
def sp.rv.cons(
  +hd: Char,
  +tl: String,
  +nn: U32,
  bz: Bool,
  ez: {U32.is_zero(nn) == bz : Bool},
  +acc: List<&2, Char>,
  ih: sp.Rv(tl, U32.sub(nn, 1), hd <> acc)
) -> {T.span.rev(SCon{hd, tl}, nn, bz, acc) == M8.rev.onto(M12.take(SCon{hd, tl}, U32.to_nat(nn)), acc)
  : List<&2, Char>}:
  match bz:
    case True{}:
      e0 = Equal.cong(Char, U32, cc => Char.to_u32(cc), Chr{nn}, Chr{0}, Eq.u32_eq(nn, 0, ez))
      %Equal.sym(U32, nn, 0, e0) : {T.span.rev(SCon{hd, tl}, nn, True{}, acc) == M8.rev.onto(M12.take(SCon{hd, tl},
        U32.to_nat(_)), acc) : List<&2, Char>}
      {==}
    case False{}:
      en = Equal.sym(Nat, U32.to_nat(nn), 1n+U32.to_nat(U32.sub(nn, 1)), Eq.u32_dec_nat(nn, ez))
      %en : {T.span.rev(tl, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)), hd <> acc)
        == M8.rev.onto(M12.take(SCon{hd, tl}, _), acc) : List<&2, Char>}
      ih

# span.rev copies the span's characters, reversed
def sp.rv(
  src: String,
  +nn: U32,
  +acc: List<&2, Char>
) -> {T.span.rev(src, nn, U32.is_zero(nn), acc) == M8.rev.onto(M12.take(src, U32.to_nat(nn)), acc)
  : List<&2, Char>}:
  match src:
    case SNil{}:
      sp.rv.nil(nn, U32.is_zero(nn), acc)
    case SCon{+hd, +tl}:
      sp.rv.cons(hd, tl, nn, U32.is_zero(nn), {==}, acc, sp.rv(tl, U32.sub(nn, 1), hd <> acc))

# the copied span of a text that starts with pre, counting pre's characters,
# is pre reversed
def se.rev(
  +pre: String,
  +cut: String,
  +more: String,
  +nn: U32,
  hc: {cut == String.append(pre, more) : String},
  hn: {U32.to_nat(nn) == M15.plus(pre, 0n) : Nat}
) -> {T.span.rev(cut, nn, U32.is_zero(nn), []) == M8.rev.onto(pre, []) : List<&2, Char>}:
  Equal.trans(List<&2, Char>, T.span.rev(cut, nn, U32.is_zero(nn), []), M8.rev.onto(M12.take(cut, U32.to_nat(nn)), []),
    M8.rev.onto(pre, []),
    sp.rv(cut, nn, []),
    Equal.cong(String, List<&2, Char>, xs => M8.rev.onto(xs, []), M12.take(cut, U32.to_nat(nn)), pre,
      sp.pre(pre, cut, more, nn, hc, hn)))

# a backslash in the span copies it and starts an escape, as a backslash in
# the copied string does
def se.copy(
  +xx: String,
  +cut: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool
) -> {T.doc.read(SCon{'\\', xx}, sv.eat(cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab))
  == T.doc.read(SCon{'\\', xx}, T.MScan{M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf,
    T.span.rev(cut, nn, U32.is_zero(nn), []))}) : T.Doc}:
  {==}

# so does a character that needs an escape, then the rest of the string
def se.copy.esc(
  +uu: U32,
  ee: esc.Lead(uu),
  +tt: String,
  +rest: String,
  +cut: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool
) -> {T.doc.read(String.append(String.append(L12.esc(Chr{uu}), L12.escs(tt)), SCon{'"', rest}),
  sv.eat(cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab))
  == T.doc.read(String.append(String.append(L12.esc(Chr{uu}), L12.escs(tt)), SCon{'"', rest}),
    T.MScan{M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf, T.span.rev(cut, nn, U32.is_zero(nn), []))}) : T.Doc}:
  %Equal.sym(String, L12.esc(Chr{uu}), SCon{'\\', str.tl(L12.esc(Chr{uu}))}, ee) :
    {T.doc.read(String.append(String.append(_, L12.escs(tt)), SCon{'"', rest}),
      sv.eat(cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab))
      == T.doc.read(String.append(String.append(_, L12.escs(tt)), SCon{'"', rest}),
        T.MScan{M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf, T.span.rev(cut, nn, U32.is_zero(nn), []))}) : T.Doc}
  se.copy(String.append(String.append(str.tl(L12.esc(Chr{uu})), L12.escs(tt)), SCon{'"', rest}), cut, nn,
    bd, rw, hs, he, ps, sk, un, lf, ab)

# a character that needs an escape ends the span: the copy holds pre, and the
# rest of the string is read in LStr
def se.esc(
  +uu: U32,
  ee: esc.Lead(uu),
  +tt: String,
  +pre: String,
  +cut: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  hc: {cut == String.append(pre, String.append(L12.escs(SCon{Chr{uu}, tt}), SCon{'"', rest})) : String},
  hn: {U32.to_nat(nn) == M15.plus(pre, 0n) : Nat},
  ih: sv.Then(String.append(pre, SCon{Chr{uu}, tt}), bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(String.append(L12.escs(SCon{Chr{uu}, tt}), SCon{'"', rest}),
  sv.eat(cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab))):
  pp.step(PP,
    T.doc.read(String.append(L12.escs(SCon{Chr{uu}, tt}), SCon{'"', rest}),
      sv.eat(cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab)),
    T.doc.read(String.append(L12.escs(SCon{Chr{uu}, tt}), SCon{'"', rest}),
      T.MScan{M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf, T.span.rev(cut, nn, U32.is_zero(nn), []))}),
    se.copy.esc(uu, ee, tt, rest, cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab),
    pp.step(PP,
      T.doc.read(String.append(L12.escs(SCon{Chr{uu}, tt}), SCon{'"', rest}),
        T.MScan{M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf, T.span.rev(cut, nn, U32.is_zero(nn), []))}),
      T.doc.read(String.append(L12.escs(SCon{Chr{uu}, tt}), SCon{'"', rest}),
        T.MScan{M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf, M8.rev.onto(pre, []))}),
      Equal.cong(List<&2, Char>, T.Doc, bb => T.doc.read(String.append(L12.escs(SCon{Chr{uu}, tt}),
        SCon{'"', rest}), T.MScan{M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf, bb)}),
        T.span.rev(cut, nn, U32.is_zero(nn), []), M8.rev.onto(pre, []),
        se.rev(pre, cut, String.append(L12.escs(SCon{Chr{uu}, tt}), SCon{'"', rest}), nn, hc, hn)),
      ls.fin(SCon{Chr{uu}, tt}, pre, bd, rw, hs, he, ps, sk, ab, un, lf, rest, PP, ih)))

# the text of the span after pre and a plain character: the character joins
# pre
def se.cut(
  +uu: U32,
  +tt: String,
  +pre: String,
  +cut: String,
  +rest: String,
  ep: {L12.esc(Chr{uu}) == SCon{Chr{uu}, SNil{}} : String},
  hc: {cut == String.append(pre, String.append(L12.escs(SCon{Chr{uu}, tt}), SCon{'"', rest})) : String}
) -> {cut == String.append(String.append(pre, SCon{Chr{uu}, SNil{}}),
  String.append(L12.escs(tt), SCon{'"', rest})) : String}:
  Equal.trans(String, cut,
    String.append(pre, SCon{Chr{uu}, String.append(L12.escs(tt), SCon{'"', rest})}),
    String.append(String.append(pre, SCon{Chr{uu}, SNil{}}), String.append(L12.escs(tt), SCon{'"', rest})),
    Equal.trans(String, cut,
      String.append(pre, String.append(String.append(L12.esc(Chr{uu}), L12.escs(tt)), SCon{'"', rest})),
      String.append(pre, SCon{Chr{uu}, String.append(L12.escs(tt), SCon{'"', rest})}),
      hc,
      Equal.cong(String, String, xs => String.append(pre, String.append(String.append(xs, L12.escs(tt)),
        SCon{'"', rest})), L12.esc(Chr{uu}), SCon{Chr{uu}, SNil{}}, ep)),
    Equal.sym(String,
      String.append(String.append(pre, SCon{Chr{uu}, SNil{}}), String.append(L12.escs(tt), SCon{'"', rest})),
      String.append(pre, SCon{Chr{uu}, String.append(L12.escs(tt), SCon{'"', rest})}),
      Eq.append_assoc(pre, SCon{Chr{uu}, SNil{}}, String.append(L12.escs(tt), SCon{'"', rest}))))

# the rest of the string after a plain character, read from the span grown
# by it: the induction hypothesis of se.go, given the text it was cut from
# and the rest of the walk
def se.Rec(
  +uu: U32,
  +tt: String,
  +pre: String,
  +cut: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  {cut == String.append(String.append(pre, SCon{Chr{uu}, SNil{}}),
    String.append(L12.escs(tt), SCon{'"', rest})) : String} ->
    sv.Then(String.append(String.append(pre, SCon{Chr{uu}, SNil{}}), tt), bd, rw, hs, he, ps, sk, ab, rest,
      PP) ->
    PP(T.doc.read(String.append(L12.escs(tt), SCon{'"', rest}),
      sv.eat(cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un, lf, ab)))

# a plain character grows the span, and the rest of the string is read from
# there
def se.plain(
  +uu: U32,
  +e34: {U32.is_eq(uu, 34) == False{} : Bool},
  +e92: {U32.is_eq(uu, 92) == False{} : Bool},
  +ec: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool},
  +tt: String,
  +pre: String,
  +cut: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  hc: {cut == String.append(pre, String.append(L12.escs(SCon{Chr{uu}, tt}), SCon{'"', rest})) : String},
  ih: sv.Then(String.append(pre, SCon{Chr{uu}, tt}), bd, rw, hs, he, ps, sk, ab, rest, PP),
  rec: se.Rec(uu, tt, pre, cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab, rest, PP)
) -> PP(T.doc.read(String.append(L12.escs(SCon{Chr{uu}, tt}), SCon{'"', rest}),
  sv.eat(cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab))):
  +ep = {esc.pl2(uu, e34, e92, ec) : {L12.esc(Chr{uu}) == SCon{Chr{uu}, SNil{}} : String}}
  %Equal.sym(String, L12.esc(Chr{uu}), SCon{Chr{uu}, SNil{}}, ep) :
    PP(T.doc.read(String.append(String.append(_, L12.escs(tt)), SCon{'"', rest}),
      sv.eat(cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab)))
  pp.step(PP,
    T.doc.read(SCon{Chr{uu}, String.append(L12.escs(tt), SCon{'"', rest})},
      sv.eat(cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab)),
    T.doc.read(String.append(L12.escs(tt), SCon{'"', rest}),
      sv.eat(cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un, lf, ab)),
    se.one(uu, String.append(L12.escs(tt), SCon{'"', rest}), cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab,
      e34, e92, ec),
    rec(se.cut(uu, tt, pre, cut, rest, ep, hc),
      sv.then.cast(String.append(pre, SCon{Chr{uu}, tt}), String.append(String.append(pre, SCon{Chr{uu},
        SNil{}}), tt), Equal.sym(String, String.append(String.append(pre, SCon{Chr{uu}, SNil{}}), tt),
        String.append(pre, SCon{Chr{uu}, tt}), Eq.append_assoc(pre, SCon{Chr{uu}, SNil{}}, tt)),
        bd, rw, hs, he, ps, sk, ab, rest, PP, ih)))

# one character of the string inside the span: a quote, a backslash or a
# control ends the span, and any other grows it
def se.step(
  +uu: U32,
  q34: Bool,
  b92: Bool,
  ctl: Bool,
  +e34: {U32.is_eq(uu, 34) == q34 : Bool},
  +e92: {U32.is_eq(uu, 92) == b92 : Bool},
  +ec: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == ctl : Bool},
  +tt: String,
  +pre: String,
  +cut: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  +hc: {cut == String.append(pre, String.append(L12.escs(SCon{Chr{uu}, tt}), SCon{'"', rest})) : String},
  +hn: {U32.to_nat(nn) == M15.plus(pre, 0n) : Nat},
  ih: sv.Then(String.append(pre, SCon{Chr{uu}, tt}), bd, rw, hs, he, ps, sk, ab, rest, PP),
  rec: se.Rec(uu, tt, pre, cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab, rest, PP)
) -> PP(T.doc.read(String.append(L12.escs(SCon{Chr{uu}, tt}), SCon{'"', rest}),
  sv.eat(cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab))):
  match q34:
    case True{}:
      se.esc(uu, esc.lead.is(uu, 34, e34, {==}), tt, pre, cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab, rest,
        PP, hc, hn, ih)
    case False{}:
      match b92:
        case True{}:
          se.esc(uu, esc.lead.is(uu, 92, e92, {==}), tt, pre, cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab,
            rest, PP, hc, hn, ih)
        case False{}:
          match ctl:
            case True{}:
              se.esc(uu, esc.lead.ctl(uu, ec), tt, pre, cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab, rest,
                PP, hc, hn, ih)
            case False{}:
              se.plain(uu, e34, e92, ec, tt, pre, cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab, rest, PP,
                hc, ih, rec)

# the rest ss of a string inside its span, pre read so far: cut is the text
# from the string's first character, and nn counts pre's characters without
# wrapping. The string reads to a value holding pre and ss (sv.Is): the span
# itself when ss needs no escape, and the copied string otherwise
def se.go(
  ss: String,
  +pre: String,
  +cut: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  +hc: {cut == String.append(pre, String.append(L12.escs(ss), SCon{'"', rest})) : String},
  +hn: {U32.to_nat(nn) == M15.plus(pre, 0n) : Nat},
  +hk: {D1.counts(ss, nn) == True{} : Bool},
  ih: sv.Then(String.append(pre, ss), bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(String.append(L12.escs(ss), SCon{'"', rest}),
  sv.eat(cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab))):
  match ss:
    case SNil{}:
      pp.step(PP,
        T.doc.read(SCon{'"', rest}, sv.eat(cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab)),
        T.doc.read(rest, T.MScan{sv.took(sk, T.VSpan{cut, nn}, bd, rw, hs, he, ps, T.LStr{}, un, lf, ab)}),
        se.close(rest, cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab),
        sv.then.cast(String.append(pre, SNil{}), pre, Eq.append_nil(pre), bd, rw, hs, he, ps, sk, ab, rest,
          PP, ih)(T.VSpan{cut, nn}, T.LStr{}, un, lf, se.own(pre, cut, SCon{'"', rest}, nn, hc, hn)))
    case SCon{hh, +tt}:
      match hh:
        case Chr{+uu}:
          se.step(uu, U32.is_eq(uu, 34), U32.is_eq(uu, 92), Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)),
            {==}, {==}, {==}, tt, pre, cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab, rest, PP, hc, hn, ih,
            hc2 => ih2 => se.go(tt, String.append(pre, SCon{Chr{uu}, SNil{}}), cut, U32.add(nn, 1), bd, rw,
              hs, he, ps, sk, un, lf, ab, rest, PP, hc2,
              Equal.trans(Nat, U32.to_nat(U32.add(nn, 1)), 1n+U32.to_nat(nn),
                M15.plus(String.append(pre, SCon{Chr{uu}, SNil{}}), 0n),
                Eq.inc.nat(nn, Eq.not.true(U32.is_zero(U32.add(nn, 1)),
                  Eq.and.left(Bool.not(U32.is_zero(U32.add(nn, 1))), D1.counts(tt, U32.add(nn, 1)), hk))),
                Equal.trans(Nat, 1n+U32.to_nat(nn), 1n+M15.plus(pre, 0n),
                  M15.plus(String.append(pre, SCon{Chr{uu}, SNil{}}), 0n),
                  Equal.cong(Nat, Nat, kk => 1n+kk, U32.to_nat(nn), M15.plus(pre, 0n), hn),
                  Equal.sym(Nat, M15.plus(String.append(pre, SCon{Chr{uu}, SNil{}}), 0n), 1n+M15.plus(pre, 0n),
                    plus.app(pre, SCon{Chr{uu}, SNil{}}, 0n)))),
              Eq.and.right(Bool.not(U32.is_zero(U32.add(nn, 1))), D1.counts(tt, U32.add(nn, 1)), hk),
              ih2))

# The first character decides the path: one written as itself opens the
# span, and one that needs an escape starts the copied string at once.

# a backslash right after the opening quote starts an escape, as it does in
# a string being copied with nothing in its buffer
def so.copy(
  +xx: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool
) -> {T.doc.read(SCon{'\\', xx}, sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab))
  == T.doc.read(SCon{'\\', xx}, T.MScan{M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf, [])}) : T.Doc}:
  {==}

# and so does a first character that needs an escape
def so.copy.esc(
  +uu: U32,
  ee: esc.Lead(uu),
  +tt: String,
  +rest: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool
) -> {T.doc.read(String.append(String.append(L12.esc(Chr{uu}), L12.escs(tt)), SCon{'"', rest}),
  sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab))
  == T.doc.read(String.append(String.append(L12.esc(Chr{uu}), L12.escs(tt)), SCon{'"', rest}),
    T.MScan{M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf, [])}) : T.Doc}:
  %Equal.sym(String, L12.esc(Chr{uu}), SCon{'\\', str.tl(L12.esc(Chr{uu}))}, ee) :
    {T.doc.read(String.append(String.append(_, L12.escs(tt)), SCon{'"', rest}),
      sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab))
      == T.doc.read(String.append(String.append(_, L12.escs(tt)), SCon{'"', rest}),
        T.MScan{M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf, [])}) : T.Doc}
  so.copy(String.append(String.append(str.tl(L12.esc(Chr{uu})), L12.escs(tt)), SCon{'"', rest}), bd, rw,
    hs, he, ps, bk, sk, un, lf, ab)

# a first character that needs an escape: the string is read in LStr from an
# empty buffer
def so.esc(
  +uu: U32,
  ee: esc.Lead(uu),
  +tt: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  ih: sv.Then(SCon{Chr{uu}, tt}, bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(String.append(L12.escs(SCon{Chr{uu}, tt}), SCon{'"', rest}),
  sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab))):
  pp.step(PP,
    T.doc.read(String.append(L12.escs(SCon{Chr{uu}, tt}), SCon{'"', rest}),
      sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab)),
    T.doc.read(String.append(L12.escs(SCon{Chr{uu}, tt}), SCon{'"', rest}),
      T.MScan{M11.ls(bd, rw, hs, he, ps, sk, ab, un, lf, [])}),
    so.copy.esc(uu, ee, tt, rest, bd, rw, hs, he, ps, bk, sk, un, lf, ab),
    ls.fin(SCon{Chr{uu}, tt}, SNil{}, bd, rw, hs, he, ps, sk, ab, un, lf, rest, PP, ih))

# a first character written as itself opens the span, and the rest of the
# string is read from there
def so.plain(
  +uu: U32,
  +e34: {U32.is_eq(uu, 34) == False{} : Bool},
  +e92: {U32.is_eq(uu, 92) == False{} : Bool},
  +ec: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool},
  +tt: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  +hk: {D1.counts(tt, 1) == True{} : Bool},
  ih: sv.Then(SCon{Chr{uu}, tt}, bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(String.append(L12.escs(SCon{Chr{uu}, tt}), SCon{'"', rest}),
  sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab))):
  %Equal.sym(String, L12.esc(Chr{uu}), SCon{Chr{uu}, SNil{}}, esc.pl2(uu, e34, e92, ec)) :
    PP(T.doc.read(String.append(String.append(_, L12.escs(tt)), SCon{'"', rest}),
      sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab)))
  pp.step(PP,
    T.doc.read(SCon{Chr{uu}, String.append(L12.escs(tt), SCon{'"', rest})},
      sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab)),
    T.doc.read(String.append(L12.escs(tt), SCon{'"', rest}),
      sv.eat(SCon{Chr{uu}, String.append(L12.escs(tt), SCon{'"', rest})}, 1, bd, rw, hs, he, ps, sk, un, lf,
        ab)),
    so.one(uu, String.append(L12.escs(tt), SCon{'"', rest}), bd, rw, hs, he, ps, bk, sk, un, lf, ab, e34,
      e92, ec),
    se.go(tt, SCon{Chr{uu}, SNil{}}, SCon{Chr{uu}, String.append(L12.escs(tt), SCon{'"', rest})}, 1, bd, rw,
      hs, he, ps, sk, un, lf, ab, rest, PP, {==}, {==}, hk, ih))

# the first character: a quote, a backslash or a control starts the copied
# string, and any other opens the span
def so.first(
  +uu: U32,
  q34: Bool,
  b92: Bool,
  ctl: Bool,
  +e34: {U32.is_eq(uu, 34) == q34 : Bool},
  +e92: {U32.is_eq(uu, 92) == b92 : Bool},
  +ec: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == ctl : Bool},
  +tt: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  +hk: {D1.counts(tt, 1) == True{} : Bool},
  ih: sv.Then(SCon{Chr{uu}, tt}, bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(String.append(L12.escs(SCon{Chr{uu}, tt}), SCon{'"', rest}),
  sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab))):
  match q34:
    case True{}:
      so.esc(uu, esc.lead.is(uu, 34, e34, {==}), tt, bd, rw, hs, he, ps, bk, sk, un, lf, ab, rest, PP, ih)
    case False{}:
      match b92:
        case True{}:
          so.esc(uu, esc.lead.is(uu, 92, e92, {==}), tt, bd, rw, hs, he, ps, bk, sk, un, lf, ab, rest, PP,
            ih)
        case False{}:
          match ctl:
            case True{}:
              so.esc(uu, esc.lead.ctl(uu, ec), tt, bd, rw, hs, he, ps, bk, sk, un, lf, ab, rest, PP, ih)
            case False{}:
              so.plain(uu, e34, e92, ec, tt, bd, rw, hs, he, ps, bk, sk, un, lf, ab, rest, PP, hk, ih)

# a nonempty string, as render writes it after the opening quote, then the
# closing quote and any rest: from every value position the rest is read with
# a value holding the string placed (sv.Is), back at LStr and uni and left as
# the last escape left them
def sv.more(
  +uu: U32,
  +tt: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  es: {D1.short(SCon{Chr{uu}, tt}) == True{} : Bool},
  ih: sv.Then(SCon{Chr{uu}, tt}, bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(String.append(L12.escs(SCon{Chr{uu}, tt}), SCon{'"', rest}),
  sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab))):
  so.first(uu, U32.is_eq(uu, 34), U32.is_eq(uu, 92), Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), {==},
    {==}, {==}, tt, bd, rw, hs, he, ps, bk, sk, un, lf, ab, rest, PP,
    Eq.and.right(Bool.not(U32.is_zero(U32.add(0, 1))), D1.counts(tt, U32.add(0, 1)), es), ih)

# and read.fin.close leaves it as it is too, at the end of the text
def tk.fin.root(
  end: T.End,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +ld: Bool
) -> {T.take.root(end, he, bk, qk, un, lf, ab, ld)
  == T.read.fin.close(T.read.once2(T.take.root(end, he, bk, qk, un, lf, ab, ld))) : T.St}:
  match end:
    case T.End{_vs, _bad, _heads}:
      {==}

# in an inline table
def tk.fin.inl(
  end: T.End,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +rest: List<&2, T.Ctx>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +ld: Bool
) -> {T.take.inl(end, rw, hs, he, ps, rest, bk, qk, un, lf, ab, ld)
  == T.read.fin.close(T.read.once2(T.take.inl(end, rw, hs, he, ps, rest, bk, qk, un, lf, ab, ld))) : T.St}:
  match end:
    case T.End{_vs, _bad, _heads}:
      {==}

# wherever the value goes
def tk.fin(
  sk: List<&2, T.Ctx>,
  +vv: T.Val,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +ld: Bool
) -> {T.take.top(sk, vv, bd, rw, hs, he, ps, bk, qk, un, lf, ab, ld)
  == T.read.fin.close(T.read.once2(T.take.top(sk, vv, bd, rw, hs, he, ps, bk, qk, un, lf, ab, ld))) : T.St}:
  match sk:
    case []:
      tk.fin.root(T.tree.walk(T.path.cat(he, ps), T.Tw{rw, T.JPut{vv}, [], bd, "", hs, False{}},
        T.path.len(he, 0)), he, bk, qk, un, lf, ab, ld)
    case T.CArr{_items, _saved, _at} <> _rest:
      {==}
    case T.CInl{inl, +saved, +at} <> +rest:
      tk.fin.inl(T.tree.walk(List.reverse(&2, String, ps), T.Tw{inl, T.JPut{vv}, [], bd, "", [],
        True{}}, 0), rw, hs, at, saved, rest, bk, qk, un, lf, ab, ld)

# the scanner after `""`, waiting for the next character
def sv.q2(
  bd: String,
  rw: List<&2, T.Val>,
  hs: List<&2, String>,
  he: List<&2, String>,
  ps: List<&2, String>,
  bk: T.Lex,
  sk: List<&2, T.Ctx>,
  un: U32,
  lf: U32,
  ab: Bool
) -> T.St:
  T.St{bd, rw, hs, he, ps, [], T.LQ2{}, bk, T.QBasic{}, sk, T.HNone{}, un, lf, ab, False{}}

# a character after `""` that is no quote places the empty string and is
# read as the fast step would read it with the string placed
def fs.q2(
  same: Bool,
  +cc: Char,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  hq: {same == False{} : Bool}
) -> {T.read.once2(T.lex.q2.go(same, sv.q2(bd, rw, hs, he, ps, bk, sk, un, lf, ab), cc, T.QBasic{}))
  == T.read.fast(sv.took(sk, T.VStr{""}, bd, rw, hs, he, ps, bk, un, lf, ab), cc) : T.St}:
  match same:
    case False{}:
      M9.fs.held(sk, T.VStr{""}, cc, bd, rw, hs, he, ps, bk, T.QBasic{}, un, lf, ab)
    case True{}:
      Eq.bit.absurd2(&2, {T.read.once2(T.lex.q2.go(True{}, sv.q2(bd, rw, hs, he, ps, bk, sk, un, lf, ab), cc,
        T.QBasic{})) == T.read.fast(sv.took(sk, T.VStr{""}, bd, rw, hs, he, ps, bk, un, lf, ab), cc) : T.St}, hq)

# two states whose fast steps agree on a character are read alike from it
def scan.fast(
  dq: Bool,
  sq: Bool,
  cr: Bool,
  +s1: T.St,
  +s2: T.St,
  +cc: Char,
  ee: {T.read.fast(s1, cc) == T.read.fast(s2, cc) : T.St}
) -> {T.doc.scan.q(dq, sq, cr, s1, cc) == T.doc.scan.q(dq, sq, cr, s2, cc) : T.Mode}:
  match dq:
    case True{}:
      Equal.cong(T.St, T.Mode, st => T.doc.wrap(st), T.read.fast(s1, cc), T.read.fast(s2, cc), ee)
    case False{}:
      match sq:
        case True{}:
          Equal.cong(T.St, T.Mode, st => T.doc.wrap(st), T.read.fast(s1, cc), T.read.fast(s2, cc), ee)
        case False{}:
          match cr:
            case True{}:
              Equal.cong(T.St, T.Mode, st => T.MCr{st}, T.read.fast(s1, cc), T.read.fast(s2, cc), ee)
            case False{}:
              Equal.cong(T.St, T.Mode, st => T.MScan{st}, T.read.fast(s1, cc), T.read.fast(s2, cc), ee)

# a text that does not start with a quote: what may follow `""`
def sv.free(rest: String) -> Bool:
  match rest:
    case SNil{}:
      True{}
    case SCon{hh, _tt}:
      Bool.not(Char.is_eq(hh, '"'))

# `""` then any rest that does not start with a quote: the rest is read with
# the empty string placed, back where the value position left it
def sv.empty(
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  rest: String,
  -PP: T.Doc -> Type,
  hr: {sv.free(rest) == True{} : Bool},
  ih: sv.Then(SNil{}, bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(SCon{'"', rest}, sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab))):
  match rest:
    case SNil{}:
      pp.step(PP, T.doc.read(SCon{'"', SNil{}}, sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab)),
        T.doc.read(SNil{}, T.MScan{sv.took(sk, T.VStr{""}, bd, rw, hs, he, ps, bk, un, lf, ab)}),
        Equal.cong(T.St, T.Doc, st => T.read.fin2(st), sv.took(sk, T.VStr{""}, bd, rw, hs, he, ps, bk, un, lf, ab),
          T.read.fin.close(T.read.once2(sv.took(sk, T.VStr{""}, bd, rw, hs, he, ps, bk, un, lf, ab))),
          tk.fin(sk, T.VStr{""}, bd, rw, hs, he, ps, bk, T.QBasic{}, un, lf, ab, False{})),
        ih(T.VStr{""}, bk, un, lf, {==}))
    case SCon{hh, +tt}:
      match hh:
        case Chr{+uu}:
          pp.step(PP, T.doc.read(SCon{'"', SCon{Chr{uu}, tt}}, sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab)),
            T.doc.read(SCon{Chr{uu}, tt}, T.MScan{sv.took(sk, T.VStr{""}, bd, rw, hs, he, ps, bk, un, lf, ab)}),
            Equal.cong(T.Mode, T.Doc, md => T.doc.read(tt, md),
              T.doc.scan(sv.q2(bd, rw, hs, he, ps, bk, sk, un, lf, ab), Chr{uu}),
              T.doc.scan(sv.took(sk, T.VStr{""}, bd, rw, hs, he, ps, bk, un, lf, ab), Chr{uu}),
              scan.fast(U32.is_eq(uu, 34), U32.is_eq(uu, 39), U32.is_eq(uu, 13),
                sv.q2(bd, rw, hs, he, ps, bk, sk, un, lf, ab),
                sv.took(sk, T.VStr{""}, bd, rw, hs, he, ps, bk, un, lf, ab), Chr{uu},
                fs.q2(U32.is_eq(uu, 34), Chr{uu}, bd, rw, hs, he, ps, bk, sk, un, lf, ab,
                  Eq.not.true(U32.is_eq(uu, 34), hr)))),
            ih(T.VStr{""}, bk, un, lf, {==}))

# The whole string, from each value position.

# every string as render writes it after the opening quote, then the closing
# quote and any rest that does not start with a quote: the rest is read with
# a string value holding it placed, and whatever back, uni and left
def sv.read(
  ss: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  es: {D1.short(ss) == True{} : Bool},
  hr: {sv.free(rest) == True{} : Bool},
  ih: sv.Then(ss, bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(String.append(L12.escs(ss), SCon{'"', rest}), sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab))):
  match ss:
    case SNil{}:
      sv.empty(bd, rw, hs, he, ps, bk, sk, un, lf, ab, rest, PP, hr, ih)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+uu}:
          sv.more(uu, tt, bd, rw, hs, he, ps, bk, sk, un, lf, ab, rest, PP, es, ih)

# key.basic(s) then rest, read from a scanner in state q: the premise form
# WP-C and WP-D call
def sv.Read(
  +ss: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +buf: List<&2, Char>,
  +lx: T.Lex,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  PP: T.Doc -> Type
) -> Type:
  PP(T.doc.read(String.append(T.key.basic(ss), rest), T.MScan{M9.fs.st(bd, rw, hs, he, ps, buf, lx, bk, qk, sk, un,
    lf, ab)}))

# the quotes around escs, and the text after them
def sv.text(
  +ss: String,
  +rest: String,
  -PP: T.Doc -> Type,
  +md: T.Mode,
  kk: PP(T.doc.read(String.append(L12.escs(ss), SCon{'"', rest}), md))
) -> PP(T.doc.read(String.append(L12.escs(ss), String.append("\"", rest)), md)):
  kk

# a value position: after `=` in a root pair or an inline table's pair, the
# scanner waits for the value in LVal; the opening quote opens the string
# with back where the pair left it
def sv.val(
  +ss: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +buf: List<&2, Char>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  es: {D1.short(ss) == True{} : Bool},
  hr: {sv.free(rest) == True{} : Bool},
  ih: sv.Then(ss, bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> sv.Read(ss, bd, rw, hs, he, ps, buf, T.LVal{}, bk, qk, sk, un, lf, ab, rest, PP):
  %Equal.sym(String, T.key.basic(ss), "\"" ++ L12.escs(ss) ++ "\"", L12.basic_escs(ss)) :
    PP(T.doc.read(String.append(_, rest), T.MScan{M9.fs.st(bd, rw, hs, he, ps, buf, T.LVal{}, bk, qk, sk, un, lf,
      ab)}))
  %Equal.sym(String, String.append(String.append(L12.escs(ss), "\""), rest),
    String.append(L12.escs(ss), String.append("\"", rest)), Eq.append_assoc(L12.escs(ss), "\"", rest)) :
    PP(T.doc.read(_, sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab)))
  sv.text(ss, rest, PP, sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab),
    sv.read(ss, bd, rw, hs, he, ps, bk, sk, un, lf, ab, rest, PP, es, hr, ih))

# A string value holding ss reads as the owned string ss, in a table's pair
# or as an item: what WP-D needs to take own off the parsed side.

# as a pair's value
def sv.own.pair(
  vv: T.Val,
  +ss: String,
  +kk: String,
  +tt: List<&2, T.Val>,
  hv: sv.Is(vv, ss)
) -> {D1.own.rows(T.VPair{kk, vv} <> tt) == T.VPair{kk, T.VStr{ss}} <> D1.own.rows(tt) : List<&2, T.Val>}:
  match vv:
    case T.VStr{st}:
      Equal.cong(String, List<&2, T.Val>, xs => T.VPair{kk, T.VStr{xs}} <> D1.own.rows(tt), st, ss, hv)
    case T.VSpan{src, +nn}:
      Equal.cong(String, List<&2, T.Val>, xs => T.VPair{kk, T.VStr{xs}} <> D1.own.rows(tt),
        T.span.str(src, nn, U32.is_zero(nn)), ss, hv)
    case T.VInt{_sign, _digits}:
      match hv:
    case T.VFlo{_sign, _text}:
      match hv:
    case T.VBool{_bit}:
      match hv:
    case T.VWhen{_when}:
      match hv:
    case T.VArr{_items}:
      match hv:
    case T.VInl{_rows}:
      match hv:
    case T.VHead{_path, _rows}:
      match hv:
    case T.VAot{_path, _rows}:
      match hv:
    case T.VAots{_path, _elems}:
      match hv:
    case T.VPair{_name, _val}:
      match hv:

# as an item
def sv.own.item(
  vv: T.Val,
  +ss: String,
  +tt: List<&2, T.Val>,
  hv: sv.Is(vv, ss)
) -> {D1.own.rows(vv <> tt) == T.VStr{ss} <> D1.own.rows(tt) : List<&2, T.Val>}:
  match vv:
    case T.VStr{st}:
      Equal.cong(String, List<&2, T.Val>, xs => T.VStr{xs} <> D1.own.rows(tt), st, ss, hv)
    case T.VSpan{src, +nn}:
      Equal.cong(String, List<&2, T.Val>, xs => T.VStr{xs} <> D1.own.rows(tt),
        T.span.str(src, nn, U32.is_zero(nn)), ss, hv)
    case T.VInt{_sign, _digits}:
      match hv:
    case T.VFlo{_sign, _text}:
      match hv:
    case T.VBool{_bit}:
      match hv:
    case T.VWhen{_when}:
      match hv:
    case T.VArr{_items}:
      match hv:
    case T.VInl{_rows}:
      match hv:
    case T.VHead{_path, _rows}:
      match hv:
    case T.VAot{_path, _rows}:
      match hv:
    case T.VAots{_path, _elems}:
      match hv:
    case T.VPair{_name, _val}:
      match hv:

def L18.word_reads_back(v, s, hc, hv, fx, rest):
  match s:
    case SNil{}:
      Eq.bit.absurd(&2, {D5.from_val(fx, String.append(SNil{}, SCon{'\n', rest})) == D5.after_val(fx, v, rest)
        : T.Doc}, hc)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          +h1 = {Eq.and.left(D1.word.first(Chr{xx}), L18.word.rest(tt), hc)
            : {D1.word.first(Chr{xx}) == True{} : Bool}}
          +hr = {Eq.and.right(D1.word.first(Chr{xx}), L18.word.rest(tt), hc) : {L18.word.rest(tt) == True{} : Bool}}
          +ho = {Equal.trans(T.Got, T.word.val(List.reverse(&2, Char, M8.rev.onto(tt, [Chr{xx}]))),
            T.word.val(String.to_list(SCon{Chr{xx}, tt})), T.GotVal{v},
            Equal.cong(List<&2, Char>, T.Got, cs => T.word.val(cs), List.reverse(&2, Char, M8.rev.onto(tt, [Chr{xx}])),
              String.to_list(SCon{Chr{xx}, tt}), M8.wd.order(Chr{xx}, tt)), hv)
            : {T.word.val(List.reverse(&2, Char, M8.rev.onto(tt, [Chr{xx}]))) == T.GotVal{v} : T.Got}}
          Equal.trans(T.Doc,
            T.doc.read(String.append(tt, SCon{'\n', rest}), T.doc.scan(D5.vst(fx, [], T.LVal{}), Chr{xx})),
            T.doc.read(String.append(tt, SCon{'\n', rest}), T.MScan{D5.vst(fx, [Chr{xx}], T.LBare{})}),
            D5.after_val(fx, v, rest),
            Equal.cong(T.Mode, T.Doc, md => T.doc.read(String.append(tt, SCon{'\n', rest}), md),
              T.doc.scan(D5.vst(fx, [], T.LVal{}), Chr{xx}), T.MScan{D5.vst(fx, [Chr{xx}], T.LBare{})},
              M1.wd.first(fx, xx, h1)),
            Equal.trans(T.Doc,
              T.doc.read(String.append(tt, SCon{'\n', rest}), T.MScan{D5.vst(fx, [Chr{xx}], T.LBare{})}),
              T.doc.read(SCon{'\n', rest}, T.MScan{D5.vst(fx, M8.rev.onto(tt, [Chr{xx}]), T.LBare{})}),
              D5.after_val(fx, v, rest),
              M1.wd.run(tt, SCon{'\n', rest}, fx, [Chr{xx}], hr),
              Equal.trans(T.Doc,
                T.doc.read(rest, T.doc.scan(D5.vst(fx, M8.rev.onto(tt, [Chr{xx}]), T.LBare{}), '\n')),
                T.doc.read(rest, T.MScan{T.read.once2(T.bare.got(T.word.val(List.reverse(&2, Char,
                  M8.rev.onto(tt, [Chr{xx}]))), D5.vst(fx, [], T.LBare{}), '\n', D5.vf.inl(fx)))}),
                D5.after_val(fx, v, rest),
                Equal.cong(T.Mode, T.Doc, md => T.doc.read(rest, md),
                  T.doc.scan(D5.vst(fx, M8.rev.onto(tt, [Chr{xx}]), T.LBare{}), '\n'),
                  T.MScan{T.read.once2(T.bare.got(T.word.val(List.reverse(&2, Char, M8.rev.onto(tt, [Chr{xx}]))),
                    D5.vst(fx, [], T.LBare{}), '\n', D5.vf.inl(fx)))},
                  M1.wd.end(fx, M8.rev.onto(tt, [Chr{xx}]))),
                Equal.cong(T.Got, T.Doc, gg => T.doc.read(rest, T.MScan{T.read.once2(T.bare.got(gg,
                  D5.vst(fx, [], T.LBare{}), '\n', D5.vf.inl(fx)))}),
                  T.word.val(List.reverse(&2, Char, M8.rev.onto(tt, [Chr{xx}]))), T.GotVal{v}, ho))))

def L1.bool_reads_back(b, fx, rest):
  match b:
    case True{}:
      L18.word_reads_back(T.VBool{True{}}, "true", {==}, {==}, fx, rest)
    case False{}:
      L18.word_reads_back(T.VBool{False{}}, "false", {==}, {==}, fx, rest)

def L7.int_reads_back(sg, ds, w, fx, rest):
  L18.word_reads_back(T.VInt{sg, ds}, T.render.atom(T.VInt{sg, ds}),
    M6.int.chars(sg, ds, Eq.and.left(T.wf.dec(ds), T.i64.fits(sg, ds), w)), L8.int_word(sg, ds, w), fx, rest)

# Floats. wf.flo reads a float's spelling with an automaton of states Fl; the
# numeral scan reads the same spelling with its own states. nm names the scan
# state that matches each Fl state, and one lemma per state and character (a
# bundle) says the two step together, with the facts about the character the
# classifier needs. inf and nan are fixed texts.

# the numeral scan state that matches a float automaton state; ds is the
# numeral the scan has built, which only integer and float digits keep
def nm(fl: T.Fl, +sg: T.Sign, ds: List<&2, U32>) -> T.Num:
  match fl:
    case T.FlStart{}:
      T.Num{T.NLead{}, sg, 10, [], False{}, False{}, ""}
    case T.FlZero{}:
      T.Num{T.NZero{}, sg, 10, [], False{}, True{}, ""}
    case T.FlInt{}:
      T.Num{T.NDig{}, sg, 10, ds, False{}, True{}, ""}
    case T.FlDot{}:
      T.Num{T.NFrac{}, sg, 10, [], False{}, False{}, ""}
    case T.FlFrac{}:
      T.Num{T.NFrac{}, sg, 10, ds, False{}, True{}, ""}
    case T.FlE{}:
      T.Num{T.NExp{}, sg, 10, [], False{}, False{}, ""}
    case T.FlESign{}:
      T.Num{T.NEDig{}, sg, 10, [], False{}, False{}, ""}
    case T.FlExp{}:
      T.Num{T.NEDig{}, sg, 10, ds, False{}, True{}, ""}
    case T.FlNo{}:
      T.Num{T.NBad{}, sg, 10, [], False{}, False{}, ""}

# the numeral a scan state keeps
def nm.ds(fl: T.Fl, ds: List<&2, U32>) -> List<&2, U32>:
  match fl:
    case T.FlInt{}:
      ds
    case T.FlFrac{}:
      ds
    case T.FlExp{}:
      ds
    case _:
      []

# the numeral after a spelling, as the scan builds it
def nds(cs: List<&2, Char>, +fl: T.Fl, ds: List<&2, U32>) -> List<&2, U32>:
  match cs:
    case []:
      ds
    case +cc <> tt:
      nds(tt, T.wf.flo.step(fl, cc), T.dec.go(nm.ds(fl, ds), 10, T.dig.val(cc)))

# a state the automaton can still accept from
def fl.live(fl: T.Fl) -> Bool:
  match fl:
    case T.FlNo{}:
      False{}
    case _:
      True{}

# a state before the exponent
def fl.pre(fl: T.Fl) -> Bool:
  match fl:
    case T.FlStart{}:
      True{}
    case T.FlZero{}:
      True{}
    case T.FlInt{}:
      True{}
    case T.FlDot{}:
      True{}
    case T.FlFrac{}:
      True{}
    case _:
      False{}

# the first state
def fl.start(fl: T.Fl) -> Bool:
  match fl:
    case T.FlStart{}:
      True{}
    case _:
      False{}

# two bits are one bit
def beq(aa: Bool, bb: Bool) -> Bool:
  match aa bb:
    case True{} True{}:
      True{}
    case False{} False{}:
      True{}
    case _ _:
      False{}

# two bits beq calls equal are one bit
def beq.eq(aa: Bool, bb: Bool, ee: {beq(aa, bb) == True{} : Bool}) -> {aa == bb : Bool}:
  match aa bb:
    case True{} True{}:
      {==}
    case False{} False{}:
      {==}
    case True{} False{}:
      Eq.bit.absurd(&2, {True{} == False{} : Bool}, ee)
    case False{} True{}:
      Eq.bit.absurd(&2, {False{} == True{} : Bool}, ee)

# a sign
def fq.pm(+cc: Char) -> Bool:
  Bool.or(Char.is_eq(cc, '+'), Char.is_eq(cc, '-'))

# a capital exponent mark or a sign
def fq.big(+cc: Char) -> Bool:
  Bool.or(Char.is_eq(cc, 'E'), fq.pm(cc))

# an exponent mark or a sign
def fq.e(+cc: Char) -> Bool:
  Bool.or(Char.is_eq(cc, 'e'), fq.big(cc))

# a dot, an exponent mark or a sign
def fq.dot(+cc: Char) -> Bool:
  Bool.or(Char.is_eq(cc, '.'), fq.e(cc))

# a character of the float alphabet: a digit, a dot, an exponent mark or a
# sign
def fch(+cc: Char) -> Bool:
  Bool.or(Char.is_digit(cc), Bool.or(Char.is_eq(cc, '.'), Bool.or(Char.is_eq(cc, 'e'), Bool.or(Char.is_eq(cc, 'E'),
    Bool.or(Char.is_eq(cc, '+'), Char.is_eq(cc, '-'))))))

# what a live step says of its character: a character a bare value keeps, no
# underscore and no colon, no minus before the exponent, a digit first, and
# the step leaves the exponent's part only at an exponent mark
def fa6(+fl: T.Fl, +cc: Char) -> Bool:
  beq(fl.pre(T.wf.flo.step(fl, cc)), Bool.and(fl.pre(fl), Bool.not(T.word.ee.hit(cc))))

def fa5(+fl: T.Fl, +cc: Char) -> Bool:
  Bool.and(Bool.or(Bool.not(fl.start(fl)), Char.is_digit(cc)), fa6(fl, cc))

def fa4(+fl: T.Fl, +cc: Char) -> Bool:
  Bool.and(Bool.not(Bool.and(fl.pre(fl), Char.is_eq(cc, '-'))), fa5(fl, cc))

def fa3(+fl: T.Fl, +cc: Char) -> Bool:
  Bool.and(Bool.not(Char.is_eq(cc, ':')), fa4(fl, cc))

def fa2(+fl: T.Fl, +cc: Char) -> Bool:
  Bool.and(Bool.not(Char.is_eq(cc, '_')), fa3(fl, cc))

def fl.facts(+fl: T.Fl, +cc: Char) -> Bool:
  Bool.and(D1.word.char(cc), fa2(fl, cc))

# a scan state and a bit
type Fs is Data:
  Fs{n: T.Num, b: Bool}

# the scan state
def fs.n(fs: Fs) -> T.Num:
  match fs:
    case Fs{nn, _b}:
      nn

# the bit
def fs.b(fs: Fs) -> Bool:
  match fs:
    case Fs{_n, bb}:
      bb

# the bundle: on a live step the scan steps as the automaton does, and the
# facts hold
def fb(+fl: T.Fl, +sg: T.Sign, +ds: List<&2, U32>, +cc: Char) -> Type:
  {Fs{T.num.step(nm(fl, sg, ds), cc), fl.facts(fl, cc)}
    == Fs{nm(T.wf.flo.step(fl, cc), sg, T.dec.go(nm.ds(fl, ds), 10, T.dig.val(cc))), True{}} : Fs}

# a sign of the float alphabet
def fe.pm(
  -P: Char -> Type,
  +cc: Char,
  pl: Bool,
  epl: {Char.is_eq(cc, '+') == pl : Bool},
  h: {Bool.or(pl, Char.is_eq(cc, '-')) == True{} : Bool},
  pp: P('+'),
  pm: P('-')
) -> P(cc):
  match pl:
    case True{}:
      %Equal.sym(Char, cc, '+', Eq.char_eq_true(cc, '+', epl)) : P(_)
      pp
    case False{}:
      %Equal.sym(Char, cc, '-', Eq.char_eq_true(cc, '-', h)) : P(_)
      pm

# a capital exponent mark or a sign
def fe.big(
  -P: Char -> Type,
  +cc: Char,
  be: Bool,
  ebe: {Char.is_eq(cc, 'E') == be : Bool},
  h: {Bool.or(be, Bool.or(Char.is_eq(cc, '+'), Char.is_eq(cc, '-'))) == True{} : Bool},
  pE: P('E'),
  pp: P('+'),
  pm: P('-')
) -> P(cc):
  match be:
    case True{}:
      %Equal.sym(Char, cc, 'E', Eq.char_eq_true(cc, 'E', ebe)) : P(_)
      pE
    case False{}:
      fe.pm(P, cc, Char.is_eq(cc, '+'), {==}, h, pp, pm)

# an exponent mark or a sign
def fe.e(
  -P: Char -> Type,
  +cc: Char,
  e1: Bool,
  ee1: {Char.is_eq(cc, 'e') == e1 : Bool},
  h: {Bool.or(e1, fq.big(cc)) == True{} : Bool},
  pe: P('e'),
  pE: P('E'),
  pp: P('+'),
  pm: P('-')
) -> P(cc):
  match e1:
    case True{}:
      %Equal.sym(Char, cc, 'e', Eq.char_eq_true(cc, 'e', ee1)) : P(_)
      pe
    case False{}:
      fe.big(P, cc, Char.is_eq(cc, 'E'), {==}, h, pE, pp, pm)

# the fifteen characters of the float alphabet, from the dot on
def fe.rest(
  -P: Char -> Type,
  +cc: Char,
  dt: Bool,
  edt: {Char.is_eq(cc, '.') == dt : Bool},
  h: {Bool.or(dt, fq.e(cc)) == True{} : Bool},
  pdt: P('.'),
  pe: P('e'),
  pE: P('E'),
  pp: P('+'),
  pm: P('-')
) -> P(cc):
  match dt:
    case True{}:
      %Equal.sym(Char, cc, '.', Eq.char_eq_true(cc, '.', edt)) : P(_)
      pdt
    case False{}:
      fe.e(P, cc, Char.is_eq(cc, 'e'), {==}, h, pe, pE, pp, pm)

# a digit, or one of the others
def fe.go(
  -P: Char -> Type,
  +cc: Char,
  dg: Bool,
  edg: {Char.is_digit(cc) == dg : Bool},
  h: {Bool.or(dg, fq.dot(cc)) == True{} : Bool},
  p0: P('0'),
  p1: P('1'),
  p2: P('2'),
  p3: P('3'),
  p4: P('4'),
  p5: P('5'),
  p6: P('6'),
  p7: P('7'),
  p8: P('8'),
  p9: P('9'),
  pdt: P('.'),
  pe: P('e'),
  pE: P('E'),
  pp: P('+'),
  pm: P('-')
) -> P(cc):
  match dg:
    case True{}:
      M8.dg.elim(P, cc, edg, p0, p1, p2, p3, p4, p5, p6, p7, p8, p9)
    case False{}:
      fe.rest(P, cc, Char.is_eq(cc, '.'), {==}, h, pdt, pe, pE, pp, pm)

# a claim made of each character of the float alphabet is made of every
# character of it
def fe.elim(
  -P: Char -> Type,
  +cc: Char,
  h: {fch(cc) == True{} : Bool},
  p0: P('0'),
  p1: P('1'),
  p2: P('2'),
  p3: P('3'),
  p4: P('4'),
  p5: P('5'),
  p6: P('6'),
  p7: P('7'),
  p8: P('8'),
  p9: P('9'),
  pdt: P('.'),
  pe: P('e'),
  pE: P('E'),
  pp: P('+'),
  pm: P('-')
) -> P(cc):
  fe.go(P, cc, Char.is_digit(cc), {==}, h, p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, pdt, pe, pE, pp, pm)

# a character that is no digit is no 0
def z0.go(
  cc: Char,
  zz: Bool,
  ez: {Char.is_eq(cc, '0') == zz : Bool},
  nd: {Char.is_digit(cc) == False{} : Bool}
) -> {zz == False{} : Bool}:
  match zz:
    case False{}:
      {==}
    case True{}:
      Eq.bit.absurd2(&2, {True{} == False{} : Bool}, Equal.trans(Bool, True{}, Char.is_digit(cc), False{},
        Equal.cong(Char, Bool, ch => Char.is_digit(ch), '0', cc,
          Equal.sym(Char, cc, '0', Eq.char_eq_true(cc, '0', ez))), nd))

# no exponent mark
def nie(
  +cc: Char,
  ne: {Char.is_eq(cc, 'e') == False{} : Bool},
  nE: {Char.is_eq(cc, 'E') == False{} : Bool}
) -> {T.wf.flo.is_e(cc) == False{} : Bool}:
  Equal.trans(Bool, T.wf.flo.is_e(cc), Bool.or(False{}, Char.is_eq(cc, 'E')), False{},
    Equal.cong(Bool, Bool, bb => Bool.or(bb, Char.is_eq(cc, 'E')), Char.is_eq(cc, 'e'), False{}, ne), nE)

# no dot and no exponent mark: nothing may follow the integer part
def tail.no(
  +cc: Char,
  ndt: {Char.is_eq(cc, '.') == False{} : Bool},
  ne: {T.wf.flo.is_e(cc) == False{} : Bool}
) -> {T.wf.flo.tail(cc) == T.FlNo{} : T.Fl}:
  Equal.trans(T.Fl, T.wf.flo.tail(cc), Bool.pick(T.Fl, T.wf.flo.is_e(cc), T.FlE{}, T.FlNo{}), T.FlNo{},
    Equal.cong(Bool, T.Fl, bb => Bool.pick(T.Fl, bb, T.FlDot{}, Bool.pick(T.Fl, T.wf.flo.is_e(cc), T.FlE{},
      T.FlNo{})), Char.is_eq(cc, '.'), False{}, ndt),
    Equal.cong(Bool, T.Fl, bb => Bool.pick(T.Fl, bb, T.FlE{}, T.FlNo{}), T.wf.flo.is_e(cc), False{}, ne))

# a character outside the float alphabet ends every state's walk
def step.no(
  fl: T.Fl,
  +cc: Char,
  n0: {Char.is_eq(cc, '0') == False{} : Bool},
  +nd: {Char.is_digit(cc) == False{} : Bool},
  +ndt: {Char.is_eq(cc, '.') == False{} : Bool},
  +ne: {T.wf.flo.is_e(cc) == False{} : Bool},
  ns: {Bool.or(Char.is_eq(cc, '+'), Char.is_eq(cc, '-')) == False{} : Bool}
) -> {T.wf.flo.step(fl, cc) == T.FlNo{} : T.Fl}:
  match fl:
    case T.FlStart{}:
      Equal.trans(T.Fl, T.wf.flo.step(T.FlStart{}, cc), Bool.pick(T.Fl, Char.is_digit(cc), T.FlInt{}, T.FlNo{}),
        T.FlNo{},
        Equal.cong(Bool, T.Fl, bb => Bool.pick(T.Fl, bb, T.FlZero{}, Bool.pick(T.Fl, Char.is_digit(cc), T.FlInt{},
          T.FlNo{})), Char.is_eq(cc, '0'), False{}, n0),
        Equal.cong(Bool, T.Fl, bb => Bool.pick(T.Fl, bb, T.FlInt{}, T.FlNo{}), Char.is_digit(cc), False{}, nd))
    case T.FlZero{}:
      tail.no(cc, ndt, ne)
    case T.FlInt{}:
      Equal.trans(T.Fl, T.wf.flo.step(T.FlInt{}, cc), T.wf.flo.tail(cc), T.FlNo{},
        Equal.cong(Bool, T.Fl, bb => Bool.pick(T.Fl, bb, T.FlInt{}, T.wf.flo.tail(cc)), Char.is_digit(cc), False{},
          nd), tail.no(cc, ndt, ne))
    case T.FlDot{}:
      Equal.cong(Bool, T.Fl, bb => Bool.pick(T.Fl, bb, T.FlFrac{}, T.FlNo{}), Char.is_digit(cc), False{}, nd)
    case T.FlFrac{}:
      Equal.trans(T.Fl, T.wf.flo.step(T.FlFrac{}, cc), Bool.pick(T.Fl, T.wf.flo.is_e(cc), T.FlE{}, T.FlNo{}),
        T.FlNo{},
        Equal.cong(Bool, T.Fl, bb => Bool.pick(T.Fl, bb, T.FlFrac{}, Bool.pick(T.Fl, T.wf.flo.is_e(cc), T.FlE{},
          T.FlNo{})), Char.is_digit(cc), False{}, nd),
        Equal.cong(Bool, T.Fl, bb => Bool.pick(T.Fl, bb, T.FlE{}, T.FlNo{}), T.wf.flo.is_e(cc), False{}, ne))
    case T.FlE{}:
      Equal.trans(T.Fl, T.wf.flo.step(T.FlE{}, cc), Bool.pick(T.Fl, Char.is_digit(cc), T.FlExp{}, T.FlNo{}),
        T.FlNo{},
        Equal.cong(Bool, T.Fl, bb => Bool.pick(T.Fl, bb, T.FlESign{}, Bool.pick(T.Fl, Char.is_digit(cc), T.FlExp{},
          T.FlNo{})), Bool.or(Char.is_eq(cc, '+'), Char.is_eq(cc, '-')), False{}, ns),
        Equal.cong(Bool, T.Fl, bb => Bool.pick(T.Fl, bb, T.FlExp{}, T.FlNo{}), Char.is_digit(cc), False{}, nd))
    case T.FlESign{}:
      Equal.cong(Bool, T.Fl, bb => Bool.pick(T.Fl, bb, T.FlExp{}, T.FlNo{}), Char.is_digit(cc), False{}, nd)
    case T.FlExp{}:
      Equal.cong(Bool, T.Fl, bb => Bool.pick(T.Fl, bb, T.FlExp{}, T.FlNo{}), Char.is_digit(cc), False{}, nd)
    case T.FlNo{}:
      {==}

# a live step reads a character of the float alphabet
def fch.go(
  fl: T.Fl,
  +cc: Char,
  bb: Bool,
  +eb: {fch(cc) == bb : Bool},
  hl: {fl.live(T.wf.flo.step(fl, cc)) == True{} : Bool}
) -> {fch(cc) == True{} : Bool}:
  match bb:
    case True{}:
      eb
    case False{}:
      +r1 = {Eq.or.right_false(Char.is_digit(cc), Bool.or(Char.is_eq(cc, '.'), Bool.or(Char.is_eq(cc, 'e'),
        Bool.or(Char.is_eq(cc, 'E'), Bool.or(Char.is_eq(cc, '+'), Char.is_eq(cc, '-'))))), eb)
        : {Bool.or(Char.is_eq(cc, '.'), Bool.or(Char.is_eq(cc, 'e'), Bool.or(Char.is_eq(cc, 'E'),
        Bool.or(Char.is_eq(cc, '+'), Char.is_eq(cc, '-'))))) == False{} : Bool}}
      +r2 = {Eq.or.right_false(Char.is_eq(cc, '.'), Bool.or(Char.is_eq(cc, 'e'), Bool.or(Char.is_eq(cc, 'E'),
        Bool.or(Char.is_eq(cc, '+'), Char.is_eq(cc, '-')))), r1)
        : {Bool.or(Char.is_eq(cc, 'e'), Bool.or(Char.is_eq(cc, 'E'), Bool.or(Char.is_eq(cc, '+'),
        Char.is_eq(cc, '-')))) == False{} : Bool}}
      +r3 = {Eq.or.right_false(Char.is_eq(cc, 'e'), Bool.or(Char.is_eq(cc, 'E'), Bool.or(Char.is_eq(cc, '+'),
        Char.is_eq(cc, '-'))), r2)
        : {Bool.or(Char.is_eq(cc, 'E'), Bool.or(Char.is_eq(cc, '+'), Char.is_eq(cc, '-'))) == False{} : Bool}}
      +nd = {Eq.or.left_false(Char.is_digit(cc), Bool.or(Char.is_eq(cc, '.'), Bool.or(Char.is_eq(cc, 'e'),
        Bool.or(Char.is_eq(cc, 'E'), Bool.or(Char.is_eq(cc, '+'), Char.is_eq(cc, '-'))))), eb)
        : {Char.is_digit(cc) == False{} : Bool}}
      +sn = {step.no(fl, cc, z0.go(cc, Char.is_eq(cc, '0'), {==}, nd), nd,
        Eq.or.left_false(Char.is_eq(cc, '.'), Bool.or(Char.is_eq(cc, 'e'), Bool.or(Char.is_eq(cc, 'E'),
          Bool.or(Char.is_eq(cc, '+'), Char.is_eq(cc, '-')))), r1),
        nie(cc, Eq.or.left_false(Char.is_eq(cc, 'e'), Bool.or(Char.is_eq(cc, 'E'), Bool.or(Char.is_eq(cc, '+'),
          Char.is_eq(cc, '-'))), r2), Eq.or.left_false(Char.is_eq(cc, 'E'), Bool.or(Char.is_eq(cc, '+'),
          Char.is_eq(cc, '-')), r3)),
        Eq.or.right_false(Char.is_eq(cc, 'E'), Bool.or(Char.is_eq(cc, '+'), Char.is_eq(cc, '-')), r3))
        : {T.wf.flo.step(fl, cc) == T.FlNo{} : T.Fl}}
      Eq.bit.absurd(&2, {fch(cc) == True{} : Bool}, Equal.trans(Bool, False{}, fl.live(T.wf.flo.step(fl, cc)),
        True{}, Equal.cong(T.Fl, Bool, ff => fl.live(ff), T.FlNo{}, T.wf.flo.step(fl, cc),
          Equal.sym(T.Fl, T.wf.flo.step(fl, cc), T.FlNo{}, sn)), hl))

# the bundle from FlStart, one character of the float alphabet at a time
def fb.start(
  +sg: T.Sign,
  +ds: List<&2, U32>,
  cc: Char,
  hf: {fch(cc) == True{} : Bool},
  hl: {fl.live(T.wf.flo.step(T.FlStart{}, cc)) == True{} : Bool}
) -> fb(T.FlStart{}, sg, ds, cc):
  fe.elim(zz => {fl.live(T.wf.flo.step(T.FlStart{}, zz)) == True{} : Bool} -> fb(T.FlStart{}, sg, ds, zz), cc, hf,
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    ll => Eq.bit.absurd(&1, fb(T.FlStart{}, sg, ds, '.'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlStart{}, sg, ds, 'e'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlStart{}, sg, ds, 'E'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlStart{}, sg, ds, '+'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlStart{}, sg, ds, '-'), ll))(hl)

# the bundle from FlZero, one character of the float alphabet at a time
def fb.zero(
  +sg: T.Sign,
  +ds: List<&2, U32>,
  cc: Char,
  hf: {fch(cc) == True{} : Bool},
  hl: {fl.live(T.wf.flo.step(T.FlZero{}, cc)) == True{} : Bool}
) -> fb(T.FlZero{}, sg, ds, cc):
  fe.elim(zz => {fl.live(T.wf.flo.step(T.FlZero{}, zz)) == True{} : Bool} -> fb(T.FlZero{}, sg, ds, zz), cc, hf,
    ll => Eq.bit.absurd(&1, fb(T.FlZero{}, sg, ds, '0'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlZero{}, sg, ds, '1'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlZero{}, sg, ds, '2'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlZero{}, sg, ds, '3'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlZero{}, sg, ds, '4'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlZero{}, sg, ds, '5'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlZero{}, sg, ds, '6'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlZero{}, sg, ds, '7'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlZero{}, sg, ds, '8'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlZero{}, sg, ds, '9'), ll),
    _l => {==},
    _l => {==},
    _l => {==},
    ll => Eq.bit.absurd(&1, fb(T.FlZero{}, sg, ds, '+'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlZero{}, sg, ds, '-'), ll))(hl)

# the bundle from FlInt, one character of the float alphabet at a time
def fb.int(
  +sg: T.Sign,
  +ds: List<&2, U32>,
  cc: Char,
  hf: {fch(cc) == True{} : Bool},
  hl: {fl.live(T.wf.flo.step(T.FlInt{}, cc)) == True{} : Bool}
) -> fb(T.FlInt{}, sg, ds, cc):
  fe.elim(zz => {fl.live(T.wf.flo.step(T.FlInt{}, zz)) == True{} : Bool} -> fb(T.FlInt{}, sg, ds, zz), cc, hf,
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    ll => Eq.bit.absurd(&1, fb(T.FlInt{}, sg, ds, '+'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlInt{}, sg, ds, '-'), ll))(hl)

# the bundle from FlDot, one character of the float alphabet at a time
def fb.dot(
  +sg: T.Sign,
  +ds: List<&2, U32>,
  cc: Char,
  hf: {fch(cc) == True{} : Bool},
  hl: {fl.live(T.wf.flo.step(T.FlDot{}, cc)) == True{} : Bool}
) -> fb(T.FlDot{}, sg, ds, cc):
  fe.elim(zz => {fl.live(T.wf.flo.step(T.FlDot{}, zz)) == True{} : Bool} -> fb(T.FlDot{}, sg, ds, zz), cc, hf,
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    ll => Eq.bit.absurd(&1, fb(T.FlDot{}, sg, ds, '.'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlDot{}, sg, ds, 'e'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlDot{}, sg, ds, 'E'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlDot{}, sg, ds, '+'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlDot{}, sg, ds, '-'), ll))(hl)

# the bundle from FlFrac, one character of the float alphabet at a time
def fb.frac(
  +sg: T.Sign,
  +ds: List<&2, U32>,
  cc: Char,
  hf: {fch(cc) == True{} : Bool},
  hl: {fl.live(T.wf.flo.step(T.FlFrac{}, cc)) == True{} : Bool}
) -> fb(T.FlFrac{}, sg, ds, cc):
  fe.elim(zz => {fl.live(T.wf.flo.step(T.FlFrac{}, zz)) == True{} : Bool} -> fb(T.FlFrac{}, sg, ds, zz), cc, hf,
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    ll => Eq.bit.absurd(&1, fb(T.FlFrac{}, sg, ds, '.'), ll),
    _l => {==},
    _l => {==},
    ll => Eq.bit.absurd(&1, fb(T.FlFrac{}, sg, ds, '+'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlFrac{}, sg, ds, '-'), ll))(hl)

# the bundle from FlE, one character of the float alphabet at a time
def fb.e(
  +sg: T.Sign,
  +ds: List<&2, U32>,
  cc: Char,
  hf: {fch(cc) == True{} : Bool},
  hl: {fl.live(T.wf.flo.step(T.FlE{}, cc)) == True{} : Bool}
) -> fb(T.FlE{}, sg, ds, cc):
  fe.elim(zz => {fl.live(T.wf.flo.step(T.FlE{}, zz)) == True{} : Bool} -> fb(T.FlE{}, sg, ds, zz), cc, hf,
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    ll => Eq.bit.absurd(&1, fb(T.FlE{}, sg, ds, '.'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlE{}, sg, ds, 'e'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlE{}, sg, ds, 'E'), ll),
    _l => {==},
    _l => {==})(hl)

# the bundle from FlESign, one character of the float alphabet at a time
def fb.esign(
  +sg: T.Sign,
  +ds: List<&2, U32>,
  cc: Char,
  hf: {fch(cc) == True{} : Bool},
  hl: {fl.live(T.wf.flo.step(T.FlESign{}, cc)) == True{} : Bool}
) -> fb(T.FlESign{}, sg, ds, cc):
  fe.elim(zz => {fl.live(T.wf.flo.step(T.FlESign{}, zz)) == True{} : Bool} -> fb(T.FlESign{}, sg, ds, zz), cc, hf,
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    ll => Eq.bit.absurd(&1, fb(T.FlESign{}, sg, ds, '.'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlESign{}, sg, ds, 'e'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlESign{}, sg, ds, 'E'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlESign{}, sg, ds, '+'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlESign{}, sg, ds, '-'), ll))(hl)

# the bundle from FlExp, one character of the float alphabet at a time
def fb.exp(
  +sg: T.Sign,
  +ds: List<&2, U32>,
  cc: Char,
  hf: {fch(cc) == True{} : Bool},
  hl: {fl.live(T.wf.flo.step(T.FlExp{}, cc)) == True{} : Bool}
) -> fb(T.FlExp{}, sg, ds, cc):
  fe.elim(zz => {fl.live(T.wf.flo.step(T.FlExp{}, zz)) == True{} : Bool} -> fb(T.FlExp{}, sg, ds, zz), cc, hf,
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    ll => Eq.bit.absurd(&1, fb(T.FlExp{}, sg, ds, '.'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlExp{}, sg, ds, 'e'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlExp{}, sg, ds, 'E'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlExp{}, sg, ds, '+'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlExp{}, sg, ds, '-'), ll))(hl)

# the bundle for every state and every character of a live step
def fb.at(
  fl: T.Fl,
  +sg: T.Sign,
  +ds: List<&2, U32>,
  +cc: Char,
  +hl: {fl.live(T.wf.flo.step(fl, cc)) == True{} : Bool}
) -> fb(fl, sg, ds, cc):
  match fl:
    case T.FlStart{}:
      fb.start(sg, ds, cc, fch.go(T.FlStart{}, cc, fch(cc), {==}, hl), hl)
    case T.FlZero{}:
      fb.zero(sg, ds, cc, fch.go(T.FlZero{}, cc, fch(cc), {==}, hl), hl)
    case T.FlInt{}:
      fb.int(sg, ds, cc, fch.go(T.FlInt{}, cc, fch(cc), {==}, hl), hl)
    case T.FlDot{}:
      fb.dot(sg, ds, cc, fch.go(T.FlDot{}, cc, fch(cc), {==}, hl), hl)
    case T.FlFrac{}:
      fb.frac(sg, ds, cc, fch.go(T.FlFrac{}, cc, fch(cc), {==}, hl), hl)
    case T.FlE{}:
      fb.e(sg, ds, cc, fch.go(T.FlE{}, cc, fch(cc), {==}, hl), hl)
    case T.FlESign{}:
      fb.esign(sg, ds, cc, fch.go(T.FlESign{}, cc, fch(cc), {==}, hl), hl)
    case T.FlExp{}:
      fb.exp(sg, ds, cc, fch.go(T.FlExp{}, cc, fch(cc), {==}, hl), hl)
    case T.FlNo{}:
      Eq.bit.absurd(&1, fb(T.FlNo{}, sg, ds, cc), hl)

# a walk from the dead state stays there
def go.no(cs: List<&2, Char>) -> {T.wf.flo.go(cs, T.FlNo{}) == T.FlNo{} : T.Fl}:
  match cs:
    case []:
      {==}
    case _c <> tt:
      go.no(tt)

# a walk that ends accepting starts from a live state
def live.of(
  fl: T.Fl,
  cs: List<&2, Char>,
  hh: {T.wf.flo.end(T.wf.flo.go(cs, fl)) == True{} : Bool}
) -> {fl.live(fl) == True{} : Bool}:
  match fl:
    case T.FlNo{}:
      Eq.bit.absurd(&2, {False{} == True{} : Bool}, Equal.trans(Bool, False{},
        T.wf.flo.end(T.wf.flo.go(cs, T.FlNo{})), True{},
        Equal.cong(T.Fl, Bool, ff => T.wf.flo.end(ff), T.FlNo{}, T.wf.flo.go(cs, T.FlNo{}),
          Equal.sym(T.Fl, T.wf.flo.go(cs, T.FlNo{}), T.FlNo{}, go.no(cs))), hh))
    case T.FlStart{}:
      {==}
    case T.FlZero{}:
      {==}
    case T.FlInt{}:
      {==}
    case T.FlDot{}:
      {==}
    case T.FlFrac{}:
      {==}
    case T.FlE{}:
      {==}
    case T.FlESign{}:
      {==}
    case T.FlExp{}:
      {==}

# the facts of a step on a walk that ends accepting
def ffacts(
  +fl: T.Fl,
  +cc: Char,
  tt: List<&2, Char>,
  hh: {T.wf.flo.end(T.wf.flo.go(tt, T.wf.flo.step(fl, cc))) == True{} : Bool}
) -> {fl.facts(fl, cc) == True{} : Bool}:
  Equal.cong(Fs, Bool, fs => fs.b(fs),
    Fs{T.num.step(nm(fl, T.Plus{}, []), cc), fl.facts(fl, cc)},
    Fs{nm(T.wf.flo.step(fl, cc), T.Plus{}, T.dec.go(nm.ds(fl, []), 10, T.dig.val(cc))), True{}},
    fb.at(fl, T.Plus{}, [], cc, live.of(T.wf.flo.step(fl, cc), tt, hh)))

# the numeral scan walks a float's spelling as the automaton does
def fw.num(
  cs: List<&2, Char>,
  +fl: T.Fl,
  +sg: T.Sign,
  +ds: List<&2, U32>,
  +hh: {T.wf.flo.end(T.wf.flo.go(cs, fl)) == True{} : Bool}
) -> {T.num.go(cs, nm(fl, sg, ds)) == nm(T.wf.flo.go(cs, fl), sg, nds(cs, fl, ds)) : T.Num}:
  match cs:
    case []:
      {==}
    case +cc <> +tt:
      Equal.trans(T.Num, T.num.go(tt, T.num.step(nm(fl, sg, ds), cc)),
        T.num.go(tt, nm(T.wf.flo.step(fl, cc), sg, T.dec.go(nm.ds(fl, ds), 10, T.dig.val(cc)))),
        nm(T.wf.flo.go(tt, T.wf.flo.step(fl, cc)), sg, nds(tt, T.wf.flo.step(fl, cc),
          T.dec.go(nm.ds(fl, ds), 10, T.dig.val(cc)))),
        Equal.cong(T.Num, T.Num, nn => T.num.go(tt, nn), T.num.step(nm(fl, sg, ds), cc),
          nm(T.wf.flo.step(fl, cc), sg, T.dec.go(nm.ds(fl, ds), 10, T.dig.val(cc))),
          Equal.cong(Fs, T.Num, fs => fs.n(fs), Fs{T.num.step(nm(fl, sg, ds), cc), fl.facts(fl, cc)},
            Fs{nm(T.wf.flo.step(fl, cc), sg, T.dec.go(nm.ds(fl, ds), 10, T.dig.val(cc))), True{}},
            fb.at(fl, sg, ds, cc, live.of(T.wf.flo.step(fl, cc), tt, hh)))),
        fw.num(tt, T.wf.flo.step(fl, cc), sg, T.dec.go(nm.ds(fl, ds), 10, T.dig.val(cc)), hh))

# a float's spelling is characters a bare value keeps
def fw.rest(
  tt: String,
  +fl: T.Fl,
  +hh: {T.wf.flo.end(T.wf.flo.go(String.to_list(tt), fl)) == True{} : Bool}
) -> {L18.word.rest(tt) == True{} : Bool}:
  match tt:
    case SNil{}:
      {==}
    case SCon{+cc, +ts}:
      M12.and.tt(D1.word.char(cc), L18.word.rest(ts), Eq.and.left(D1.word.char(cc), fa2(fl, cc),
        ffacts(fl, cc, String.to_list(ts), hh)), fw.rest(ts, T.wf.flo.step(fl, cc), hh))

# a float's spelling holds no underscore, so its body is itself
def fw.body(
  cs: List<&2, Char>,
  +fl: T.Fl,
  +out: List<&2, Char>,
  +hh: {T.wf.flo.end(T.wf.flo.go(cs, fl)) == True{} : Bool}
) -> {T.word.body.go(cs, False{}, out) == List.reverse.go(&2, Char, out, cs) : List<&2, Char>}:
  match cs:
    case []:
      {==}
    case +cc <> +tt:
      +f2 = {Eq.and.right(D1.word.char(cc), fa2(fl, cc), ffacts(fl, cc, tt, hh)) : {fa2(fl, cc) == True{} : Bool}}
      Equal.trans(List<&2, Char>, T.word.body.go(tt, False{}, T.word.body.put.us(Char.is_eq(cc, '_'), cc, out)),
        T.word.body.go(tt, False{}, cc <> out), List.reverse.go(&2, Char, cc <> out, tt),
        Equal.cong(Bool, List<&2, Char>, bb => T.word.body.go(tt, False{}, T.word.body.put.us(bb, cc, out)),
          Char.is_eq(cc, '_'), False{}, Eq.not.true(Char.is_eq(cc, '_'), Eq.and.left(Bool.not(Char.is_eq(cc, '_')),
          fa3(fl, cc), f2))),
        fw.body(tt, T.wf.flo.step(fl, cc), cc <> out, hh))

# a float's spelling holds no colon
def fw.colon(
  cs: List<&2, Char>,
  +fl: T.Fl,
  +hh: {T.wf.flo.end(T.wf.flo.go(cs, fl)) == True{} : Bool}
) -> {T.word.colon(cs) == False{} : Bool}:
  match cs:
    case []:
      {==}
    case +cc <> +tt:
      +f3 = {Eq.and.right(Bool.not(Char.is_eq(cc, '_')), fa3(fl, cc), Eq.and.right(D1.word.char(cc), fa2(fl, cc),
        ffacts(fl, cc, tt, hh))) : {fa3(fl, cc) == True{} : Bool}}
      Equal.trans(Bool, T.word.or(Char.is_eq(cc, ':'), T.word.colon(tt)), T.word.or(False{}, T.word.colon(tt)),
        False{},
        Equal.cong(Bool, Bool, bb => T.word.or(bb, T.word.colon(tt)), Char.is_eq(cc, ':'), False{},
          Eq.not.true(Char.is_eq(cc, ':'), Eq.and.left(Bool.not(Char.is_eq(cc, ':')), fa4(fl, cc), f3))),
        fw.colon(tt, T.wf.flo.step(fl, cc), hh))

# the left flag of a word.or that answered False
def wor.l(aa: Bool, bb: Bool, ee: {T.word.or(aa, bb) == False{} : Bool}) -> {aa == False{} : Bool}:
  match aa:
    case True{}:
      ee
    case False{}:
      {==}

# and the right one
def wor.r(aa: Bool, bb: Bool, ee: {T.word.or(aa, bb) == False{} : Bool}) -> {bb == False{} : Bool}:
  match aa:
    case True{}:
      Eq.bit.absurd2(&2, {bb == False{} : Bool}, ee)
    case False{}:
      ee

# a character that is no minus is no dash, first or not
def dhit(
  ff: Bool,
  cc: Char,
  hm: {Char.is_eq(cc, '-') == False{} : Bool}
) -> {T.word.dash.hit(ff, cc) == False{} : Bool}:
  match ff:
    case True{}:
      {==}
    case False{}:
      hm

# before the exponent, a spelling with no exponent mark holds no minus, and
# its walk stays before the exponent
def fw.dash(
  cs: List<&2, Char>,
  +fl: T.Fl,
  ff: Bool,
  +hh: {T.wf.flo.end(T.wf.flo.go(cs, fl)) == True{} : Bool},
  +hp: {fl.pre(fl) == True{} : Bool},
  +he: {T.word.ee(cs) == False{} : Bool}
) -> {T.word.dash(cs, ff) == False{} : Bool}:
  match cs:
    case []:
      {==}
    case +cc <> +tt:
      +f4 = {Eq.and.right(Bool.not(Char.is_eq(cc, ':')), fa4(fl, cc), Eq.and.right(Bool.not(Char.is_eq(cc, '_')),
        fa3(fl, cc), Eq.and.right(D1.word.char(cc), fa2(fl, cc), ffacts(fl, cc, tt, hh))))
        : {fa4(fl, cc) == True{} : Bool}}
      +f5 = {Eq.and.right(Bool.not(Bool.and(fl.pre(fl), Char.is_eq(cc, '-'))), fa5(fl, cc), f4)
        : {fa5(fl, cc) == True{} : Bool}}
      +hx = {wor.l(T.word.ee.hit(cc), T.word.ee(tt), he) : {T.word.ee.hit(cc) == False{} : Bool}}
      +hm = {Equal.trans(Bool, Char.is_eq(cc, '-'), Bool.and(fl.pre(fl), Char.is_eq(cc, '-')), False{},
        Equal.cong(Bool, Bool, bb => Bool.and(bb, Char.is_eq(cc, '-')), True{}, fl.pre(fl),
          Equal.sym(Bool, fl.pre(fl), True{}, hp)),
        Eq.not.true(Bool.and(fl.pre(fl), Char.is_eq(cc, '-')), Eq.and.left(Bool.not(Bool.and(fl.pre(fl),
          Char.is_eq(cc, '-'))), fa5(fl, cc), f4))) : {Char.is_eq(cc, '-') == False{} : Bool}}
      +hq = {Equal.trans(Bool, fl.pre(T.wf.flo.step(fl, cc)), Bool.and(fl.pre(fl), Bool.not(T.word.ee.hit(cc))),
        True{},
        beq.eq(fl.pre(T.wf.flo.step(fl, cc)), Bool.and(fl.pre(fl), Bool.not(T.word.ee.hit(cc))),
          Eq.and.right(Bool.or(Bool.not(fl.start(fl)), Char.is_digit(cc)), fa6(fl, cc), f5)),
        Equal.trans(Bool, Bool.and(fl.pre(fl), Bool.not(T.word.ee.hit(cc))),
          Bool.and(True{}, Bool.not(T.word.ee.hit(cc))), True{},
          Equal.cong(Bool, Bool, bb => Bool.and(bb, Bool.not(T.word.ee.hit(cc))), fl.pre(fl), True{}, hp),
          Equal.cong(Bool, Bool, bb => Bool.and(True{}, Bool.not(bb)), T.word.ee.hit(cc), False{}, hx)))
        : {fl.pre(T.wf.flo.step(fl, cc)) == True{} : Bool}}
      Equal.trans(Bool, T.word.or(T.word.dash.hit(ff, cc), T.word.dash(tt, False{})),
        T.word.or(False{}, T.word.dash(tt, False{})), False{},
        Equal.cong(Bool, Bool, bb => T.word.or(bb, T.word.dash(tt, False{})), T.word.dash.hit(ff, cc), False{},
          dhit(ff, cc, hm)),
        fw.dash(tt, T.wf.flo.step(fl, cc), False{}, hh, hq, wor.r(T.word.ee.hit(cc), T.word.ee(tt), he)))

# a finished walk that accepts is a float, spelled by the body of the word
def fin.end(
  fl: T.Fl,
  +sg: T.Sign,
  ds: List<&2, U32>,
  cs: List<&2, Char>,
  hh: {T.wf.flo.end(fl) == True{} : Bool}
) -> {T.num.fin(nm(fl, sg, ds), cs) == T.GotVal{T.VFlo{sg, T.word.body(cs)}} : T.Got}:
  match fl:
    case T.FlFrac{}:
      {==}
    case T.FlExp{}:
      {==}
    case T.FlStart{}:
      Eq.bit.absurd(&2, {T.num.fin(nm(T.FlStart{}, sg, ds), cs) == T.GotVal{T.VFlo{sg, T.word.body(cs)}} : T.Got}, hh)
    case T.FlZero{}:
      Eq.bit.absurd(&2, {T.num.fin(nm(T.FlZero{}, sg, ds), cs) == T.GotVal{T.VFlo{sg, T.word.body(cs)}} : T.Got}, hh)
    case T.FlInt{}:
      Eq.bit.absurd(&2, {T.num.fin(nm(T.FlInt{}, sg, ds), cs) == T.GotVal{T.VFlo{sg, T.word.body(cs)}} : T.Got}, hh)
    case T.FlDot{}:
      Eq.bit.absurd(&2, {T.num.fin(nm(T.FlDot{}, sg, ds), cs) == T.GotVal{T.VFlo{sg, T.word.body(cs)}} : T.Got}, hh)
    case T.FlE{}:
      Eq.bit.absurd(&2, {T.num.fin(nm(T.FlE{}, sg, ds), cs) == T.GotVal{T.VFlo{sg, T.word.body(cs)}} : T.Got}, hh)
    case T.FlESign{}:
      Eq.bit.absurd(&2, {T.num.fin(nm(T.FlESign{}, sg, ds), cs) == T.GotVal{T.VFlo{sg, T.word.body(cs)}} : T.Got},
        hh)
    case T.FlNo{}:
      Eq.bit.absurd(&2, {T.num.fin(nm(T.FlNo{}, sg, ds), cs) == T.GotVal{T.VFlo{sg, T.word.body(cs)}} : T.Got}, hh)

# a word the datetime route could take only by a dash in its exponent: an
# exponent mark keeps it a numeral, and with none it has no dash
def flo.route(
  +cs: List<&2, Char>,
  ex: Bool,
  eex: {T.word.ee(cs) == ex : Bool},
  hc: {T.word.colon(cs) == False{} : Bool},
  hd: {T.word.ee(cs) == False{} : Bool} -> {T.word.dash(cs, True{}) == False{} : Bool}
) -> {T.word.route(T.GotBad{""}, T.word.or(T.word.colon(cs), T.word.dash(cs, True{})), cs) == T.word.num(cs) : T.Got}:
  match ex:
    case True{}:
      %Equal.sym(Bool, T.word.ee(cs), True{}, eex) :
        {T.word.route.date(T.word.as_date(T.word.or(T.word.colon(cs), T.word.dash(cs, True{})), _), cs)
          == T.word.num(cs) : T.Got}
      {==}
    case False{}:
      M6.route.num(cs, hc, hd(eex))

# a digit is no sign
def dg.nosign(
  cc: Char,
  hc: {Char.is_digit(cc) == True{} : Bool}
) -> {Bool.or(Char.is_eq(cc, '+'), Char.is_eq(cc, '-')) == False{} : Bool}:
  M8.dg.elim(zz => {Bool.or(Char.is_eq(zz, '+'), Char.is_eq(zz, '-')) == False{} : Bool}, cc, hc,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# after a minus, a digit is read as the first character of an unsigned
# numeral with the minus kept
def sign.skip(
  cc: Char,
  hc: {Char.is_digit(cc) == True{} : Bool}
) -> {T.num.step(T.Num{T.NSign{}, T.Minus{}, 10, [], False{}, False{}, ""}, cc) == T.num.step(nm(T.FlStart{}, T.Minus{},
  []), cc) : T.Num}:
  M8.dg.elim(zz => {T.num.step(T.Num{T.NSign{}, T.Minus{}, 10, [], False{}, False{}, ""}, zz)
    == T.num.step(nm(T.FlStart{}, T.Minus{}, []), zz) : T.Num}, cc, hc,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# what flo_word claims
def flo.Goal(+sg: T.Sign, +text: String) -> Type:
  {T.word.val(String.to_list(T.render.atom(T.VFlo{sg, text}))) == T.GotVal{T.VFlo{sg, text}} : T.Got}

# a float's spelling starts with a digit
def fl.dig(
  +hh: Char,
  tt: String,
  hw: {T.wf.flo.end(T.wf.flo.go(hh <> String.to_list(tt), T.FlStart{})) == True{} : Bool}
) -> {Char.is_digit(hh) == True{} : Bool}:
  Eq.and.left(Char.is_digit(hh), fa6(T.FlStart{}, hh), Eq.and.right(Bool.not(Bool.and(True{},
    Char.is_eq(hh, '-'))), fa5(T.FlStart{}, hh), Eq.and.right(Bool.not(Char.is_eq(hh, ':')), fa4(T.FlStart{}, hh),
    Eq.and.right(Bool.not(Char.is_eq(hh, '_')), fa3(T.FlStart{}, hh), Eq.and.right(D1.word.char(hh),
    fa2(T.FlStart{}, hh), ffacts(T.FlStart{}, hh, String.to_list(tt), hw))))))

# a positive float spelled by the automaton
def flo.plus(
  +hh: Char,
  +tt: String,
  +hw: {T.wf.flo.end(T.wf.flo.go(hh <> String.to_list(tt), T.FlStart{})) == True{} : Bool}
) -> flo.Goal(T.Plus{}, SCon{hh, tt}):
  +hd = {fl.dig(hh, tt, hw) : {Char.is_digit(hh) == True{} : Bool}}
  +cs = {hh <> String.to_list(tt) : List<&2, Char>}
  Equal.trans(T.Got, T.word.val.pick(T.word.special(hh), cs), T.word.val.pick(False{}, cs),
    T.GotVal{T.VFlo{T.Plus{}, SCon{hh, tt}}},
    Equal.cong(Bool, T.Got, bb => T.word.val.pick(bb, cs), T.word.special(hh), False{}, M6.dg.nospec(hh, hd)),
    Equal.trans(T.Got, T.word.route(T.GotBad{""}, T.word.or(T.word.colon(cs), T.word.dash(cs, True{})), cs),
      T.word.num(cs), T.GotVal{T.VFlo{T.Plus{}, SCon{hh, tt}}},
      flo.route(cs, T.word.ee(cs), {==}, fw.colon(cs, T.FlStart{}, hw),
        ee => fw.dash(cs, T.FlStart{}, True{}, hw, {==}, ee)),
      Equal.trans(T.Got, T.num.fin(T.num.go(cs, nm(T.FlStart{}, T.Plus{}, [])), cs),
        T.num.fin(nm(T.wf.flo.go(cs, T.FlStart{}), T.Plus{}, nds(cs, T.FlStart{}, [])), cs),
        T.GotVal{T.VFlo{T.Plus{}, SCon{hh, tt}}},
        Equal.cong(T.Num, T.Got, nn => T.num.fin(nn, cs), T.num.go(cs, nm(T.FlStart{}, T.Plus{}, [])),
          nm(T.wf.flo.go(cs, T.FlStart{}), T.Plus{}, nds(cs, T.FlStart{}, [])),
          fw.num(cs, T.FlStart{}, T.Plus{}, [], hw)),
        Equal.trans(T.Got, T.num.fin(nm(T.wf.flo.go(cs, T.FlStart{}), T.Plus{}, nds(cs, T.FlStart{}, [])), cs),
          T.GotVal{T.VFlo{T.Plus{}, T.word.body(cs)}}, T.GotVal{T.VFlo{T.Plus{}, SCon{hh, tt}}},
          fin.end(T.wf.flo.go(cs, T.FlStart{}), T.Plus{}, nds(cs, T.FlStart{}, []), cs, hw),
          Equal.cong(String, T.Got, ss => T.GotVal{T.VFlo{T.Plus{}, ss}}, T.word.body(cs), SCon{hh, tt},
            Equal.trans(String, String.from_list(T.word.body.go(String.to_list(tt), False{},
              T.word.body.put.sign(Bool.or(Char.is_eq(hh, '+'), Char.is_eq(hh, '-')), hh, []))),
              String.from_list(T.word.body.go(String.to_list(tt), False{}, [hh])), SCon{hh, tt},
              Equal.cong(Bool, String, bb => String.from_list(T.word.body.go(String.to_list(tt), False{},
                T.word.body.put.sign(bb, hh, []))), Bool.or(Char.is_eq(hh, '+'), Char.is_eq(hh, '-')), False{},
                dg.nosign(hh, hd)),
              Equal.trans(String, String.from_list(T.word.body.go(String.to_list(tt), False{}, [hh])),
                String.from_list(hh <> String.to_list(tt)), SCon{hh, tt},
                Equal.cong(List<&2, Char>, String, ls => String.from_list(ls),
                  T.word.body.go(String.to_list(tt), False{}, [hh]), hh <> String.to_list(tt),
                  fw.body(String.to_list(tt), T.wf.flo.step(T.FlStart{}, hh), [hh], hw)),
                M8.ftl(SCon{hh, tt}))))))))

# a negative float spelled by the automaton: the minus makes the word a
# special candidate, which it is not, and the scan keeps the minus as the sign
def flo.minus(
  +hh: Char,
  +tt: String,
  +hw: {T.wf.flo.end(T.wf.flo.go(hh <> String.to_list(tt), T.FlStart{})) == True{} : Bool}
) -> flo.Goal(T.Minus{}, SCon{hh, tt}):
  +hd = {fl.dig(hh, tt, hw) : {Char.is_digit(hh) == True{} : Bool}}
  +cs = {hh <> String.to_list(tt) : List<&2, Char>}
  Equal.trans(T.Got, T.word.route(T.word.spec(String.from_list('-' <> cs)),
    T.word.or(T.word.colon('-' <> cs), T.word.dash('-' <> cs, True{})), '-' <> cs),
    T.word.route(T.GotBad{""}, T.word.or(T.word.colon('-' <> cs), T.word.dash('-' <> cs, True{})), '-' <> cs),
    T.GotVal{T.VFlo{T.Minus{}, SCon{hh, tt}}},
    Equal.cong(T.Got, T.Got, gg => T.word.route(gg, T.word.or(T.word.colon('-' <> cs),
      T.word.dash('-' <> cs, True{})), '-' <> cs), T.word.spec(String.from_list('-' <> cs)), T.GotBad{""},
      M6.spec.m(hh, String.to_list(tt), M6.dg.noi(hh, hd), M6.dg.non(hh, hd))),
    Equal.trans(T.Got, T.word.route(T.GotBad{""}, T.word.or(T.word.colon('-' <> cs), T.word.dash('-' <> cs,
      True{})), '-' <> cs), T.word.num('-' <> cs), T.GotVal{T.VFlo{T.Minus{}, SCon{hh, tt}}},
      flo.route('-' <> cs, T.word.ee(cs), {==}, fw.colon(cs, T.FlStart{}, hw),
        ee => fw.dash(cs, T.FlStart{}, False{}, hw, {==}, ee)),
      Equal.trans(T.Got, T.num.fin(T.num.go(String.to_list(tt), T.num.step(T.Num{T.NSign{}, T.Minus{}, 10, [],
        False{}, False{}, ""}, hh)), '-' <> cs),
        T.num.fin(nm(T.wf.flo.go(cs, T.FlStart{}), T.Minus{}, nds(cs, T.FlStart{}, [])), '-' <> cs),
        T.GotVal{T.VFlo{T.Minus{}, SCon{hh, tt}}},
        Equal.cong(T.Num, T.Got, nn => T.num.fin(nn, '-' <> cs),
          T.num.go(String.to_list(tt), T.num.step(T.Num{T.NSign{}, T.Minus{}, 10, [], False{}, False{}, ""}, hh)),
          nm(T.wf.flo.go(cs, T.FlStart{}), T.Minus{}, nds(cs, T.FlStart{}, [])),
          Equal.trans(T.Num,
            T.num.go(String.to_list(tt), T.num.step(T.Num{T.NSign{}, T.Minus{}, 10, [], False{}, False{}, ""}, hh)),
            T.num.go(cs, nm(T.FlStart{}, T.Minus{}, [])),
            nm(T.wf.flo.go(cs, T.FlStart{}), T.Minus{}, nds(cs, T.FlStart{}, [])),
            Equal.cong(T.Num, T.Num, nn => T.num.go(String.to_list(tt), nn),
              T.num.step(T.Num{T.NSign{}, T.Minus{}, 10, [], False{}, False{}, ""}, hh),
              T.num.step(nm(T.FlStart{}, T.Minus{}, []), hh), sign.skip(hh, hd)),
            fw.num(cs, T.FlStart{}, T.Minus{}, [], hw))),
        Equal.trans(T.Got, T.num.fin(nm(T.wf.flo.go(cs, T.FlStart{}), T.Minus{}, nds(cs, T.FlStart{}, [])),
          '-' <> cs),
          T.GotVal{T.VFlo{T.Minus{}, T.word.body('-' <> cs)}}, T.GotVal{T.VFlo{T.Minus{}, SCon{hh, tt}}},
          fin.end(T.wf.flo.go(cs, T.FlStart{}), T.Minus{}, nds(cs, T.FlStart{}, []), '-' <> cs, hw),
          Equal.cong(String, T.Got, ss => T.GotVal{T.VFlo{T.Minus{}, ss}}, T.word.body('-' <> cs), SCon{hh, tt},
            Equal.trans(String, String.from_list(T.word.body.go(cs, False{}, [])), String.from_list(cs),
              SCon{hh, tt},
              Equal.cong(List<&2, Char>, String, ls => String.from_list(ls), T.word.body.go(cs, False{}, []), cs,
                fw.body(cs, T.FlStart{}, [], hw)),
              M8.ftl(SCon{hh, tt})))))))

# a spelling the automaton accepts, with its first character, by the sign
def flo.auto.sg(
  +sg: T.Sign,
  +hh: Char,
  +tt: String,
  +hw: {T.wf.flo.end(T.wf.flo.go(hh <> String.to_list(tt), T.FlStart{})) == True{} : Bool}
) -> flo.Goal(sg, SCon{hh, tt}):
  match sg:
    case T.Plus{}:
      flo.plus(hh, tt, hw)
    case T.Minus{}:
      flo.minus(hh, tt, hw)

# a spelling the automaton accepts
def flo.auto(
  text: String,
  +sg: T.Sign,
  +hw: {T.wf.flo.end(T.wf.flo.go(String.to_list(text), T.FlStart{})) == True{} : Bool}
) -> flo.Goal(sg, text):
  match text:
    case SNil{}:
      Eq.bit.absurd(&1, flo.Goal(sg, SNil{}), hw)
    case SCon{+hh, +tt}:
      flo.auto.sg(sg, hh, tt, hw)

# inf or nan
def flo.name(aa: Bool) -> String:
  match aa:
    case True{}:
      "inf"
    case False{}:
      "nan"

# inf and nan, by the sign
def flo.fixed(+sg: T.Sign, aa: Bool) -> flo.Goal(sg, flo.name(aa)):
  match sg:
    case T.Plus{}:
      match aa:
        case True{}:
          {==}
        case False{}:
          {==}
    case T.Minus{}:
      match aa:
        case True{}:
          {==}
        case False{}:
          {==}

# a well-formed float: inf, nan, or a spelling the automaton accepts
def flo.spec(
  +sg: T.Sign,
  +text: String,
  aa: Bool,
  ea: {T.str.eq(text, "inf") == aa : Bool},
  bb: Bool,
  eb: {T.str.eq(text, "nan") == bb : Bool},
  +hw: {Bool.or(aa, Bool.or(bb, T.wf.flo.end(T.wf.flo.go(String.to_list(text), T.FlStart{})))) == True{} : Bool}
) -> flo.Goal(sg, text):
  match aa:
    case True{}:
      %Equal.sym(String, text, "inf", M7.str.eq.true(text, "inf", ea)) : flo.Goal(sg, _)
      flo.fixed(sg, True{})
    case False{}:
      match bb:
        case True{}:
          %Equal.sym(String, text, "nan", M7.str.eq.true(text, "nan", eb)) : flo.Goal(sg, _)
          flo.fixed(sg, False{})
        case False{}:
          flo.auto(text, sg, hw)

def L6.flo_word(sg, text, w):
  flo.spec(sg, text, T.str.eq(text, "inf"), {==}, T.str.eq(text, "nan"), {==}, w)

# what flo.chars claims
def flo.Chars(+sg: T.Sign, +text: String) -> Type:
  {L18.word.chars(T.render.atom(T.VFlo{sg, text})) == True{} : Bool}

# a spelling the automaton accepts is a bare value, by the sign
def flo.chars.sg(
  +sg: T.Sign,
  +hh: Char,
  +tt: String,
  +hw: {T.wf.flo.end(T.wf.flo.go(hh <> String.to_list(tt), T.FlStart{})) == True{} : Bool}
) -> flo.Chars(sg, SCon{hh, tt}):
  match sg:
    case T.Plus{}:
      M12.and.tt(D1.word.first(hh), L18.word.rest(tt), M6.dg.first(hh, fl.dig(hh, tt, hw)),
        fw.rest(tt, T.wf.flo.step(T.FlStart{}, hh), hw))
    case T.Minus{}:
      M12.and.tt(D1.word.first('-'), L18.word.rest(SCon{hh, tt}), {==}, fw.rest(SCon{hh, tt}, T.FlStart{}, hw))

# a spelling the automaton accepts is a bare value
def flo.chars.auto(
  text: String,
  +sg: T.Sign,
  +hw: {T.wf.flo.end(T.wf.flo.go(String.to_list(text), T.FlStart{})) == True{} : Bool}
) -> flo.Chars(sg, text):
  match text:
    case SNil{}:
      Eq.bit.absurd(&1, flo.Chars(sg, SNil{}), hw)
    case SCon{+hh, +tt}:
      flo.chars.sg(sg, hh, tt, hw)

# inf and nan are bare values, with either sign
def flo.chars.fixed(+sg: T.Sign, aa: Bool) -> flo.Chars(sg, flo.name(aa)):
  match sg:
    case T.Plus{}:
      match aa:
        case True{}:
          {==}
        case False{}:
          {==}
    case T.Minus{}:
      match aa:
        case True{}:
          {==}
        case False{}:
          {==}

# a well-formed float is a bare value
def flo.chars(
  +sg: T.Sign,
  +text: String,
  aa: Bool,
  ea: {T.str.eq(text, "inf") == aa : Bool},
  bb: Bool,
  eb: {T.str.eq(text, "nan") == bb : Bool},
  +hw: {Bool.or(aa, Bool.or(bb, T.wf.flo.end(T.wf.flo.go(String.to_list(text), T.FlStart{})))) == True{} : Bool}
) -> flo.Chars(sg, text):
  match aa:
    case True{}:
      %Equal.sym(String, text, "inf", M7.str.eq.true(text, "inf", ea)) : flo.Chars(sg, _)
      flo.chars.fixed(sg, True{})
    case False{}:
      match bb:
        case True{}:
          %Equal.sym(String, text, "nan", M7.str.eq.true(text, "nan", eb)) : flo.Chars(sg, _)
          flo.chars.fixed(sg, False{})
        case False{}:
          flo.chars.auto(text, sg, hw)

def L5.flo_reads_back(sg, text, w, fx, rest):
  L18.word_reads_back(T.VFlo{sg, text}, T.render.atom(T.VFlo{sg, text}),
    flo.chars(sg, text, T.str.eq(text, "inf"), {==}, T.str.eq(text, "nan"), {==}, w), L6.flo_word(sg, text, w),
    fx, rest)

def L17.when_reads_back(w, h, fx, rest):
  L18.word_reads_back(T.VWhen{w}, T.when.text(w), Equal.trans(Bool, L18.word.chars(T.when.text(w)),
    L18.word.chars(M5.tstr(M4.tks(w))), True{}, Equal.cong(String, Bool, ss => L18.word.chars(ss), T.when.text(w),
    M5.tstr(M4.tks(w)), M4.when.eq(Unit{}, w, h)), M4.wch.all(w, h)), L3.when_word(w, h), fx, rest)

# WP-C: arrays and inline tables read back. A value in a value position is
# read from the value state (LVal) up to the character after it, a newline,
# a comma or a closer, which ends it; the value is then put where the stack
# of open arrays and inline tables puts values (take.top). The lemmas below
# state that in premise form: the rest of the walk is a function of the value
# put and of the fields the value may change (back, qkind, uni and left), as
# in WP-S; the value is known through own (Laws.cv.own1 of it is Laws.cv.raw1
# of the value render wrote). A scalar ends at any of those characters (WP-N
# read it only up to a newline); a string is WP-S's; an array and an inline
# table go by induction on the value and its shape together, as ezjson's pv.

# the scanner waiting for a value, with no error and nothing in its buffer
def cv.vp(
  rw: List<&2, T.Val>,
  hs: List<&2, String>,
  he: List<&2, String>,
  ps: List<&2, String>,
  bk: T.Lex,
  qk: T.QKind,
  sk: List<&2, T.Ctx>,
  un: U32,
  lf: U32,
  ab: Bool
) -> T.St:
  T.St{"", rw, hs, he, ps, [], T.LVal{}, bk, qk, sk, T.HNone{}, un, lf, ab, False{}}

# the scanner once a value is put where the stack puts values
def cv.put(
  sk: List<&2, T.Ctx>,
  vv: T.Val,
  rw: List<&2, T.Val>,
  hs: List<&2, String>,
  +he: List<&2, String>,
  ps: List<&2, String>,
  bk: T.Lex,
  qk: T.QKind,
  un: U32,
  lf: U32,
  ab: Bool
) -> T.St:
  T.take.top(sk, vv, "", rw, hs, he, ps, bk, qk, un, lf, ab, False{})

# the rest of the walk, for the value v: reading rest from the scanner with a
# value vv put that own reads as the scanner's form of v, and any back, qkind,
# uni and left, gives a document PP holds of
def cv.Then(
  +v: T.Val,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  @vv: T.Val -> @bk: T.Lex -> @qk: T.QKind -> @un: U32 -> @lf: U32 ->
    {L15.cv.own1(vv) == L15.cv.raw1(v) : T.Val} ->
    PP(T.doc.read(rest, T.MScan{cv.put(sk, vv, rw, hs, he, ps, bk, qk, un, lf, ab)}))

# a character that may end a value is a newline, a comma or a closer: a claim
# made of each of the four is made of it
def cv.ech(
  -P: Char -> Type,
  +cc: Char,
  b1: Bool,
  b2: Bool,
  b3: Bool,
  b4: Bool,
  e1: {Char.is_eq(cc, '\n') == b1 : Bool},
  e2: {Char.is_eq(cc, ',') == b2 : Bool},
  e3: {Char.is_eq(cc, ']') == b3 : Bool},
  e4: {Char.is_eq(cc, '}') == b4 : Bool},
  hh: {Bool.or(b1, Bool.or(b2, Bool.or(b3, b4))) == True{} : Bool},
  p1: P('\n'),
  p2: P(','),
  p3: P(']'),
  p4: P('}')
) -> P(cc):
  match b1:
    case True{}:
      %Equal.sym(Char, cc, '\n', Eq.char_eq_true(cc, '\n', e1)) : P(_)
      p1
    case False{}:
      match b2:
        case True{}:
          %Equal.sym(Char, cc, ',', Eq.char_eq_true(cc, ',', e2)) : P(_)
          p2
        case False{}:
          match b3:
            case True{}:
              %Equal.sym(Char, cc, ']', Eq.char_eq_true(cc, ']', e3)) : P(_)
              p3
            case False{}:
              match b4:
                case True{}:
                  %Equal.sym(Char, cc, '}', Eq.char_eq_true(cc, '}', e4)) : P(_)
                  p4
                case False{}:
                  Eq.bit.absurd(&1, P(cc), hh)

# a text that starts with such a character is one for each of the four
def cv.eall(
  -P: String -> Type,
  rest: String,
  hn: {L15.cv.end(rest) == True{} : Bool},
  p1: @tt: String -> P(SCon{'\n', tt}),
  p2: @tt: String -> P(SCon{',', tt}),
  p3: @tt: String -> P(SCon{']', tt}),
  p4: @tt: String -> P(SCon{'}', tt})
) -> P(rest):
  match rest:
    case SNil{}:
      Eq.bit.absurd(&1, P(SNil{}), hn)
    case SCon{+cc, +tt}:
      cv.ech(ch => P(SCon{ch, tt}), cc, Char.is_eq(cc, '\n'), Char.is_eq(cc, ','), Char.is_eq(cc, ']'),
        Char.is_eq(cc, '}'), {==}, {==}, {==}, {==}, hn, p1(tt), p2(tt), p3(tt), p4(tt))

# The scalar ends. A comma or a closer ends a bare value as a newline does,
# but is held and read again once the value is put; reading it again is the
# fast step from the state with the value put (fs.held). A newline is read
# again only inside an inline table; elsewhere the value's step already
# consumed it, as the fast step would.

# a comma ends a bare value, and is held
def wd.endc(
  +fx: D5.Vf,
  +buf: List<&2, Char>
) -> {T.doc.scan(D5.vst(fx, buf, T.LBare{}), ',') == T.MScan{T.read.once2(T.bare.got(T.word.val(List.reverse(&2,
  Char, buf)), D5.vst(fx, [], T.LBare{}), ',', True{}))} : T.Mode}:
  match fx:
    case D5.Vf{_bad, _rows, _heads, _here, _parts, _back, _qkind, _stack, _uni, _left, _arrtab}:
      {==}

# and so does a bracket
def wd.endb(
  +fx: D5.Vf,
  +buf: List<&2, Char>
) -> {T.doc.scan(D5.vst(fx, buf, T.LBare{}), ']') == T.MScan{T.read.once2(T.bare.got(T.word.val(List.reverse(&2,
  Char, buf)), D5.vst(fx, [], T.LBare{}), ']', True{}))} : T.Mode}:
  match fx:
    case D5.Vf{_bad, _rows, _heads, _here, _parts, _back, _qkind, _stack, _uni, _left, _arrtab}:
      {==}

# and a brace
def wd.endr(
  +fx: D5.Vf,
  +buf: List<&2, Char>
) -> {T.doc.scan(D5.vst(fx, buf, T.LBare{}), '}') == T.MScan{T.read.once2(T.bare.got(T.word.val(List.reverse(&2,
  Char, buf)), D5.vst(fx, [], T.LBare{}), '}', True{}))} : T.Mode}:
  match fx:
    case D5.Vf{_bad, _rows, _heads, _here, _parts, _back, _qkind, _stack, _uni, _left, _arrtab}:
      {==}

# the scanner once a bare value's buffer is classified and put, and the
# character that ended it is read again or not, as hold says
def cw.got(+fx: D5.Vf, bb: List<&2, Char>, +cc: Char, +hold: Bool) -> T.Mode:
  T.MScan{T.read.once2(T.bare.got(T.word.val(List.reverse(&2, Char, bb)), D5.vst(fx, [], T.LBare{}), cc, hold))}

# the character cc ends a bare value, whatever it holds, and hold says
# whether it is read again
def cw.Ew(+fx: D5.Vf, +cc: Char, +hold: Bool) -> Type:
  @bb: List<&2, Char> ->
    {T.doc.scan(D5.vst(fx, bb, T.LBare{}), cc) == cw.got(fx, bb, cc, hold) : T.Mode}

# the character is read by the fast step from the state with the value put
def cw.Es(+fx: D5.Vf, +vv: T.Val, +cc: Char) -> Type:
  {T.doc.scan(T.val.take(D5.vst(fx, [], T.LBare{}), vv), cc)
    == T.MScan{T.read.fast(T.val.take(D5.vst(fx, [], T.LBare{}), vv), cc)} : T.Mode}

# a bare value, then a character that ends it: the rest is read with the
# value put, once the word, its end and the step after it are named
def cw.gen(
  +vv: T.Val,
  ss: String,
  +hc: {L18.word.chars(ss) == True{} : Bool},
  +hv: {T.word.val(String.to_list(ss)) == T.GotVal{vv} : T.Got},
  +fx: D5.Vf,
  +cc: Char,
  +hold: Bool,
  +rest: String,
  ew: cw.Ew(fx, cc, hold),
  eh: M9.cw.Eh(fx, vv, cc, hold),
  es: cw.Es(fx, vv, cc)
) -> {T.doc.read(String.append(ss, SCon{cc, rest}), T.MScan{D5.vst(fx, [], T.LVal{})})
  == T.doc.read(SCon{cc, rest}, T.MScan{T.val.take(D5.vst(fx, [], T.LBare{}), vv)}) : T.Doc}:
  match ss:
    case SNil{}:
      Eq.bit.absurd(&2, {T.doc.read(String.append(SNil{}, SCon{cc, rest}), T.MScan{D5.vst(fx, [], T.LVal{})})
        == T.doc.read(SCon{cc, rest}, T.MScan{T.val.take(D5.vst(fx, [], T.LBare{}), vv)}) : T.Doc}, hc)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          +h1 = {Eq.and.left(D1.word.first(Chr{xx}), L18.word.rest(tt), hc)
            : {D1.word.first(Chr{xx}) == True{} : Bool}}
          +hr = {Eq.and.right(D1.word.first(Chr{xx}), L18.word.rest(tt), hc) : {L18.word.rest(tt) == True{} : Bool}}
          +bb = {M8.rev.onto(tt, [Chr{xx}]) : List<&2, Char>}
          +ho = {Equal.trans(T.Got, T.word.val(List.reverse(&2, Char, bb)),
            T.word.val(String.to_list(SCon{Chr{xx}, tt})), T.GotVal{vv},
            Equal.cong(List<&2, Char>, T.Got, cs => T.word.val(cs), List.reverse(&2, Char, bb),
              String.to_list(SCon{Chr{xx}, tt}), M8.wd.order(Chr{xx}, tt)), hv)
            : {T.word.val(List.reverse(&2, Char, bb)) == T.GotVal{vv} : T.Got}}
          +st = {T.val.take(D5.vst(fx, [], T.LBare{}), vv) : T.St}
          Equal.trans(T.Doc,
            T.doc.read(String.append(tt, SCon{cc, rest}), T.doc.scan(D5.vst(fx, [], T.LVal{}), Chr{xx})),
            T.doc.read(String.append(tt, SCon{cc, rest}), T.MScan{D5.vst(fx, [Chr{xx}], T.LBare{})}),
            T.doc.read(SCon{cc, rest}, T.MScan{st}),
            Equal.cong(T.Mode, T.Doc, md => T.doc.read(String.append(tt, SCon{cc, rest}), md),
              T.doc.scan(D5.vst(fx, [], T.LVal{}), Chr{xx}), T.MScan{D5.vst(fx, [Chr{xx}], T.LBare{})},
              M1.wd.first(fx, xx, h1)),
            Equal.trans(T.Doc,
              T.doc.read(String.append(tt, SCon{cc, rest}), T.MScan{D5.vst(fx, [Chr{xx}], T.LBare{})}),
              T.doc.read(SCon{cc, rest}, T.MScan{D5.vst(fx, bb, T.LBare{})}),
              T.doc.read(SCon{cc, rest}, T.MScan{st}),
              M1.wd.run(tt, SCon{cc, rest}, fx, [Chr{xx}], hr),
              Equal.trans(T.Doc,
                T.doc.read(rest, T.doc.scan(D5.vst(fx, bb, T.LBare{}), cc)),
                T.doc.read(rest, T.MScan{T.read.once2(T.bare.got(T.GotVal{vv}, D5.vst(fx, [], T.LBare{}), cc,
                  hold))}),
                T.doc.read(rest, T.doc.scan(st, cc)),
                Equal.trans(T.Doc,
                  T.doc.read(rest, T.doc.scan(D5.vst(fx, bb, T.LBare{}), cc)),
                  T.doc.read(rest, T.MScan{T.read.once2(T.bare.got(T.word.val(List.reverse(&2, Char, bb)),
                    D5.vst(fx, [], T.LBare{}), cc, hold))}),
                  T.doc.read(rest, T.MScan{T.read.once2(T.bare.got(T.GotVal{vv}, D5.vst(fx, [], T.LBare{}), cc,
                    hold))}),
                  Equal.cong(T.Mode, T.Doc, md => T.doc.read(rest, md),
                    T.doc.scan(D5.vst(fx, bb, T.LBare{}), cc),
                    T.MScan{T.read.once2(T.bare.got(T.word.val(List.reverse(&2, Char, bb)),
                      D5.vst(fx, [], T.LBare{}), cc, hold))}, ew(bb)),
                  Equal.cong(T.Got, T.Doc, gg => T.doc.read(rest, T.MScan{T.read.once2(T.bare.got(gg,
                    D5.vst(fx, [], T.LBare{}), cc, hold))}), T.word.val(List.reverse(&2, Char, bb)),
                    T.GotVal{vv}, ho)),
                Equal.cong(T.Mode, T.Doc, md => T.doc.read(rest, md),
                  T.MScan{T.read.once2(T.bare.hold(st, cc, hold))}, T.doc.scan(st, cc),
                  Equal.trans(T.Mode, T.MScan{T.read.once2(T.bare.hold(st, cc, hold))},
                    T.MScan{T.read.fast(st, cc)}, T.doc.scan(st, cc),
                    Equal.cong(T.St, T.Mode, sx => T.MScan{sx}, T.read.once2(T.bare.hold(st, cc, hold)),
                      T.read.fast(st, cc), eh),
                    Equal.sym(T.Mode, T.doc.scan(st, cc), T.MScan{T.read.fast(st, cc)}, es))))))

# the word's text, as the claim cw.word makes
def cw.Word(+fx: D5.Vf, +vv: T.Val, +ss: String, +rest: String) -> Type:
  {T.doc.read(String.append(ss, rest), T.MScan{D5.vst(fx, [], T.LVal{})})
    == T.doc.read(rest, T.MScan{T.val.take(D5.vst(fx, [], T.LBare{}), vv)}) : T.Doc}

# a bare value then any character that may end a value: the rest, that
# character first, is read with the value put
def cw.word(
  +vv: T.Val,
  +ss: String,
  +hc: {L18.word.chars(ss) == True{} : Bool},
  +hv: {T.word.val(String.to_list(ss)) == T.GotVal{vv} : T.Got},
  +fx: D5.Vf,
  rest: String,
  hn: {L15.cv.end(rest) == True{} : Bool}
) -> cw.Word(fx, vv, ss, rest):
  cv.eall(rr => cw.Word(fx, vv, ss, rr), rest, hn,
    tt => cw.gen(vv, ss, hc, hv, fx, '\n', D5.vf.inl(fx), tt, bb => M1.wd.end(fx, bb), M9.cw.nl(fx, vv), {==}),
    tt => cw.gen(vv, ss, hc, hv, fx, ',', True{}, tt, bb => wd.endc(fx, bb), M9.cw.held(fx, vv, ','), {==}),
    tt => cw.gen(vv, ss, hc, hv, fx, ']', True{}, tt, bb => wd.endb(fx, bb), M9.cw.held(fx, vv, ']'), {==}),
    tt => cw.gen(vv, ss, hc, hv, fx, '}', True{}, tt, bb => wd.endr(fx, bb), M9.cw.held(fx, vv, '}'), {==}))

# a well-formed scalar render writes as a bare value is a word of the
# characters a bare value keeps
def cv.wch(
  vv: T.Val,
  +w: {L10.bare_val(vv) == True{} : Bool}
) -> {L18.word.chars(T.render.atom(vv)) == True{} : Bool}:
  match vv:
    case T.VInt{+sg, +ds}:
      M6.int.chars(sg, ds, Eq.and.left(T.wf.dec(ds), T.i64.fits(sg, ds), w))
    case T.VFlo{+sg, +text}:
      flo.chars(sg, text, T.str.eq(text, "inf"), {==}, T.str.eq(text, "nan"), {==}, w)
    case T.VBool{bb}:
      match bb:
        case True{}:
          {==}
        case False{}:
          {==}
    case T.VWhen{+ww}:
      Equal.trans(Bool, L18.word.chars(T.when.text(ww)), L18.word.chars(M5.tstr(M4.tks(ww))), True{},
        Equal.cong(String, Bool, ss => L18.word.chars(ss), T.when.text(ww), M5.tstr(M4.tks(ww)),
          M4.when.eq(Unit{}, ww, w)), M4.wch.all(ww, w))
    case T.VStr{tx}:
      Eq.bit.absurd(&2, {L18.word.chars(T.render.atom(T.VStr{tx})) == True{} : Bool}, w)
    case T.VSpan{src, nn}:
      Eq.bit.absurd(&2, {L18.word.chars(T.render.atom(T.VSpan{src, nn})) == True{} : Bool}, w)
    case T.VArr{it}:
      Eq.bit.absurd(&2, {L18.word.chars(T.render.atom(T.VArr{it})) == True{} : Bool}, w)
    case T.VInl{rs}:
      Eq.bit.absurd(&2, {L18.word.chars(T.render.atom(T.VInl{rs})) == True{} : Bool}, w)
    case T.VHead{pp, rs}:
      Eq.bit.absurd(&2, {L18.word.chars(T.render.atom(T.VHead{pp, rs})) == True{} : Bool}, w)
    case T.VAot{pp, rs}:
      Eq.bit.absurd(&2, {L18.word.chars(T.render.atom(T.VAot{pp, rs})) == True{} : Bool}, w)
    case T.VAots{pp, es}:
      Eq.bit.absurd(&2, {L18.word.chars(T.render.atom(T.VAots{pp, es})) == True{} : Bool}, w)
    case T.VPair{nm, pv}:
      Eq.bit.absurd(&2, {L18.word.chars(T.render.atom(T.VPair{nm, pv})) == True{} : Bool}, w)

# and word.val classifies it as the scalar
def cv.wvl(
  vv: T.Val,
  +w: {L10.bare_val(vv) == True{} : Bool}
) -> {T.word.val(String.to_list(T.render.atom(vv))) == T.GotVal{vv} : T.Got}:
  match vv:
    case T.VInt{+sg, +ds}:
      L8.int_word(sg, ds, w)
    case T.VFlo{+sg, +text}:
      L6.flo_word(sg, text, w)
    case T.VBool{bb}:
      L2.bool_word(bb)
    case T.VWhen{+ww}:
      L3.when_word(ww, w)
    case T.VStr{tx}:
      Eq.bit.absurd(&2, {T.word.val(String.to_list(T.render.atom(T.VStr{tx}))) == T.GotVal{T.VStr{tx}} : T.Got}, w)
    case T.VSpan{src, nn}:
      Eq.bit.absurd(&2, {T.word.val(String.to_list(T.render.atom(T.VSpan{src, nn}))) == T.GotVal{T.VSpan{src, nn}}
        : T.Got}, w)
    case T.VArr{it}:
      Eq.bit.absurd(&2, {T.word.val(String.to_list(T.render.atom(T.VArr{it}))) == T.GotVal{T.VArr{it}} : T.Got}, w)
    case T.VInl{rs}:
      Eq.bit.absurd(&2, {T.word.val(String.to_list(T.render.atom(T.VInl{rs}))) == T.GotVal{T.VInl{rs}} : T.Got}, w)
    case T.VHead{pp, rs}:
      Eq.bit.absurd(&2, {T.word.val(String.to_list(T.render.atom(T.VHead{pp, rs}))) == T.GotVal{T.VHead{pp, rs}}
        : T.Got}, w)
    case T.VAot{pp, rs}:
      Eq.bit.absurd(&2, {T.word.val(String.to_list(T.render.atom(T.VAot{pp, rs}))) == T.GotVal{T.VAot{pp, rs}}
        : T.Got}, w)
    case T.VAots{pp, es}:
      Eq.bit.absurd(&2, {T.word.val(String.to_list(T.render.atom(T.VAots{pp, es}))) == T.GotVal{T.VAots{pp, es}}
        : T.Got}, w)
    case T.VPair{nm, pv}:
      Eq.bit.absurd(&2, {T.word.val(String.to_list(T.render.atom(T.VPair{nm, pv}))) == T.GotVal{T.VPair{nm, pv}}
        : T.Got}, w)

# a scalar holds no span, so own reads it as itself
def cv.own.sc(
  vv: T.Val,
  w: {L10.bare_val(vv) == True{} : Bool}
) -> {L15.cv.own1(vv) == L15.cv.raw1(vv) : T.Val}:
  match vv:
    case T.VInt{_sg, _ds}:
      {==}
    case T.VFlo{_sg, _text}:
      {==}
    case T.VBool{_bb}:
      {==}
    case T.VWhen{_ww}:
      {==}
    case T.VStr{tx}:
      Eq.bit.absurd(&2, {L15.cv.own1(T.VStr{tx}) == L15.cv.raw1(T.VStr{tx}) : T.Val}, w)
    case T.VSpan{src, nn}:
      Eq.bit.absurd(&2, {L15.cv.own1(T.VSpan{src, nn}) == L15.cv.raw1(T.VSpan{src, nn}) : T.Val}, w)
    case T.VArr{it}:
      Eq.bit.absurd(&2, {L15.cv.own1(T.VArr{it}) == L15.cv.raw1(T.VArr{it}) : T.Val}, w)
    case T.VInl{rs}:
      Eq.bit.absurd(&2, {L15.cv.own1(T.VInl{rs}) == L15.cv.raw1(T.VInl{rs}) : T.Val}, w)
    case T.VHead{pp, rs}:
      Eq.bit.absurd(&2, {L15.cv.own1(T.VHead{pp, rs}) == L15.cv.raw1(T.VHead{pp, rs}) : T.Val}, w)
    case T.VAot{pp, rs}:
      Eq.bit.absurd(&2, {L15.cv.own1(T.VAot{pp, rs}) == L15.cv.raw1(T.VAot{pp, rs}) : T.Val}, w)
    case T.VAots{pp, es}:
      Eq.bit.absurd(&2, {L15.cv.own1(T.VAots{pp, es}) == L15.cv.raw1(T.VAots{pp, es}) : T.Val}, w)
    case T.VPair{nm, pv}:
      Eq.bit.absurd(&2, {L15.cv.own1(T.VPair{nm, pv}) == L15.cv.raw1(T.VPair{nm, pv}) : T.Val}, w)

# a well-formed scalar render writes as a bare value, then a character that
# ends it: the rest is read with the scalar put
def cv.scalar(
  +vv: T.Val,
  +w: {L10.bare_val(vv) == True{} : Bool},
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  hn: {L15.cv.end(rest) == True{} : Bool},
  ih: cv.Then(vv, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(String.append(T.render.atom(vv), rest), T.MScan{cv.vp(rw, hs, he, ps, bk, qk, sk, un, lf, ab)})):
  pp.step(PP, T.doc.read(String.append(T.render.atom(vv), rest), T.MScan{cv.vp(rw, hs, he, ps, bk, qk, sk, un, lf,
    ab)}), T.doc.read(rest, T.MScan{cv.put(sk, vv, rw, hs, he, ps, bk, qk, un, lf, ab)}),
    cw.word(vv, T.render.atom(vv), cv.wch(vv, w), cv.wvl(vv, w), D5.Vf{"", rw, hs, he, ps, bk, qk, sk, un, lf,
      ab}, rest, hn),
    ih(vv, bk, qk, un, lf, cv.own.sc(vv, w)))

# no text that starts with a character that ends a value starts with a quote
def cv.free(
  rest: String,
  hn: {L15.cv.end(rest) == True{} : Bool}
) -> {sv.free(rest) == True{} : Bool}:
  cv.eall(rr => {sv.free(rr) == True{} : Bool}, rest, hn, _tt => {==}, _tt => {==}, _tt => {==}, _tt => {==})

# a string value holding ss is one own reads as the owned string ss
def cv.isstr(
  vv: T.Val,
  +ss: String,
  hv: sv.Is(vv, ss)
) -> {L15.cv.own1(vv) == T.VStr{ss} : T.Val}:
  match vv:
    case T.VStr{st}:
      Equal.cong(String, T.Val, xs => T.VStr{xs}, st, ss, hv)
    case T.VSpan{src, +nn}:
      Equal.cong(String, T.Val, xs => T.VStr{xs}, T.span.str(src, nn, U32.is_zero(nn)), ss, hv)
    case T.VInt{_sign, _digits}:
      match hv:
    case T.VFlo{_sign, _text}:
      match hv:
    case T.VBool{_bit}:
      match hv:
    case T.VWhen{_when}:
      match hv:
    case T.VArr{_items}:
      match hv:
    case T.VInl{_rows}:
      match hv:
    case T.VHead{_path, _rows}:
      match hv:
    case T.VAot{_path, _rows}:
      match hv:
    case T.VAots{_path, _elems}:
      match hv:
    case T.VPair{_name, _val}:
      match hv:

# a string, as key.basic writes it, then a character that ends a value: the
# rest is read with a string value holding it put (WP-S)
def cv.str(
  +ss: String,
  es: {D1.short(ss) == True{} : Bool},
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  hn: {L15.cv.end(rest) == True{} : Bool},
  ih: cv.Then(T.VStr{ss}, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(String.append(T.key.basic(ss), rest), T.MScan{cv.vp(rw, hs, he, ps, bk, qk, sk, un, lf, ab)})):
  sv.val(ss, "", rw, hs, he, ps, [], bk, qk, sk, un, lf, ab, rest, PP, es, cv.free(rest, hn),
    +vv => b2 => u2 => l2 => hv => ih(vv, b2, T.QBasic{}, u2, l2, cv.isstr(vv, ss, hv)))

# a span is written as its characters are, so it reads back as they do
def cv.span(
  +src: String,
  +nn: U32,
  es: {D1.short(T.span.str(src, nn, U32.is_zero(nn))) == True{} : Bool},
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  hn: {L15.cv.end(rest) == True{} : Bool},
  ih: cv.Then(T.VSpan{src, nn}, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(String.append(T.render.atom(T.VSpan{src, nn}), rest), T.MScan{cv.vp(rw, hs, he, ps, bk, qk, sk,
  un, lf, ab)})):
  %Equal.sym(String, T.span.quote(src, nn), T.key.basic(T.string(T.VSpan{src, nn})), L12.span_quote_basic(src, nn)) :
    PP(T.doc.read(String.append(_, rest), T.MScan{cv.vp(rw, hs, he, ps, bk, qk, sk, un, lf, ab)}))
  cv.str(T.span.str(src, nn, U32.is_zero(nn)), es, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP, hn, ih)

# every well-formed scalar with short strings, then a character that ends a
# value: the rest is read with the scalar put
def cv.atom(
  vv: T.Val,
  hw: {T.wf.atom(vv) == True{} : Bool},
  hs2: {D1.cv.short1(vv) == True{} : Bool},
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  hn: {L15.cv.end(rest) == True{} : Bool},
  ih: cv.Then(vv, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(D1.cv.tx(vv, rest), T.MScan{cv.vp(rw, hs, he, ps, bk, qk, sk, un, lf, ab)})):
  match vv:
    case T.VStr{+ss}:
      cv.str(ss, hs2, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP, hn, ih)
    case T.VSpan{+src, +nn}:
      cv.span(src, nn, hs2, rw, hs, he, ps,
        bk, qk, sk, un, lf, ab, rest, PP, hn, ih)
    case T.VInt{+sg, +ds}:
      cv.scalar(T.VInt{sg, ds}, hw, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP, hn, ih)
    case T.VFlo{+sg, +text}:
      cv.scalar(T.VFlo{sg, text}, hw, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP, hn, ih)
    case T.VBool{+bb}:
      cv.scalar(T.VBool{bb}, hw, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP, hn, ih)
    case T.VWhen{+ww}:
      cv.scalar(T.VWhen{ww}, hw, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP, hn, ih)
    case T.VArr{it}:
      Eq.bit.absurd(&1, PP(T.doc.read(D1.cv.tx(T.VArr{it}, rest), T.MScan{cv.vp(rw, hs, he, ps, bk, qk, sk, un, lf,
        ab)})), hw)
    case T.VInl{rs}:
      Eq.bit.absurd(&1, PP(T.doc.read(D1.cv.tx(T.VInl{rs}, rest), T.MScan{cv.vp(rw, hs, he, ps, bk, qk, sk, un, lf,
        ab)})), hw)
    case T.VHead{pp, rs}:
      Eq.bit.absurd(&1, PP(T.doc.read(D1.cv.tx(T.VHead{pp, rs}, rest), T.MScan{cv.vp(rw, hs, he, ps, bk, qk, sk, un,
        lf, ab)})), hw)
    case T.VAot{pp, rs}:
      Eq.bit.absurd(&1, PP(T.doc.read(D1.cv.tx(T.VAot{pp, rs}, rest), T.MScan{cv.vp(rw, hs, he, ps, bk, qk, sk, un,
        lf, ab)})), hw)
    case T.VAots{pp, es}:
      Eq.bit.absurd(&1, PP(T.doc.read(D1.cv.tx(T.VAots{pp, es}, rest), T.MScan{cv.vp(rw, hs, he, ps, bk, qk, sk, un,
        lf, ab)})), hw)
    case T.VPair{nm, pv}:
      Eq.bit.absurd(&1, PP(T.doc.read(D1.cv.tx(T.VPair{nm, pv}, rest), T.MScan{cv.vp(rw, hs, he, ps, bk, qk, sk, un,
        lf, ab)})), hw)

# Arrays. `[` opens a frame and waits in LArr; an item's first character is
# held there and read again in LVal, with back at LVal; the item is put onto
# the frame's items, newest first, and the scanner waits in LArrC, where
# ", " goes back to LArr and `]` closes the array: its items, reversed, are
# put where the stack puts values. The items read so far are known through
# own: own.rows of them is the scanner's form of the items read, pushed onto
# what was there (cv.ThenA).

# the scanner in an open array, waiting for an item or `]`: the frame holds
# the items so far (acc, newest first) and the parts and path to put the
# array at
def cv.ar(
  acc: List<&2, T.Val>,
  ps0: List<&2, String>,
  he0: List<&2, String>,
  rw: List<&2, T.Val>,
  hs: List<&2, String>,
  he: List<&2, String>,
  ps: List<&2, String>,
  bk: T.Lex,
  qk: T.QKind,
  sk: List<&2, T.Ctx>,
  un: U32,
  lf: U32,
  ab: Bool
) -> T.St:
  T.St{"", rw, hs, he, ps, [], T.LArr{}, bk, qk, T.CArr{acc, ps0, he0} <> sk, T.HNone{}, un, lf, ab, False{}}

# the scanner in an open inline table after `, `, waiting for a key: the frame
# holds the pairs so far (newest first) and the parts and path to put the
# table at
def cv.ik(
  inl: List<&2, T.Val>,
  ps0: List<&2, String>,
  +he0: List<&2, String>,
  rw: List<&2, T.Val>,
  hs: List<&2, String>,
  bk: T.Lex,
  qk: T.QKind,
  sk: List<&2, T.Ctx>,
  un: U32,
  lf: U32,
  ab: Bool
) -> T.St:
  T.St{"", rw, hs, he0, [], [], T.LInlK{}, bk, qk, T.CInl{inl, ps0, he0} <> sk, T.HNone{}, un, lf, ab, False{}}

# what follows an item or a pair render wrote: the closer when it is the
# last, and ", " and the rest otherwise
def cv.tl(vs: List<&2, T.Val>, +close: Char, xx: String) -> String:
  match vs:
    case []:
      SCon{close, xx}
    case +hh <> +tt:
      SCon{',', SCon{' ', String.append(T.render.go(hh <> tt, ", ", False{}), SCon{close, xx})}}

# the separator and the rest render writes after an item or a pair
def cv.S(+vs: List<&2, T.Val>) -> String:
  String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, vs)), T.render.go(vs, ", ", False{}))

# the rest of the walk once an array is closed: its items, reversed, are put,
# and own reads what the scanner pushed as the items read pushed onto what
# the frame held
def cv.ThenA(
  +items: List<&2, T.Val>,
  +acc: List<&2, T.Val>,
  +ps0: List<&2, String>,
  +he0: List<&2, String>,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  @ac2: List<&2, T.Val> -> @bk: T.Lex -> @qk: T.QKind -> @un: U32 -> @lf: U32 ->
    {D1.own.rows(ac2) == List.reverse.go(&2, T.Val, L15.cv.raw(items), D1.own.rows(acc)) : List<&2, T.Val>} ->
    PP(T.doc.read(rest, T.MScan{cv.put(sk, T.VArr{List.reverse(&2, T.Val, ac2)}, rw, hs, he0, ps0, bk, qk, un, lf,
      ab)}))

# the rest of the walk once an inline table is closed: its pairs, sealed,
# are put, and own reads them as the pairs read pushed onto what the frame
# held; sealing leaves them as they are
def cv.ThenI(
  +rows: List<&2, T.Val>,
  +inl: List<&2, T.Val>,
  +ps0: List<&2, String>,
  +he0: List<&2, String>,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  @in2: List<&2, T.Val> -> @bk: T.Lex -> @qk: T.QKind -> @un: U32 -> @lf: U32 ->
    {D1.own.rows(in2) == List.reverse.go(&2, T.Val, L15.cv.raw(rows), D1.own.rows(inl)) : List<&2, T.Val>} ->
    {T.inl.seal(in2) == in2 : List<&2, T.Val>} ->
    PP(T.doc.read(rest, T.MScan{cv.put(sk, T.VInl{T.inl.seal(in2)}, rw, hs, he0, ps0, bk, qk, un, lf, ab)}))

# what the induction claims of a list: an array's items (rows false) read
# from LArr up to `]` and the rest, or an inline table's pairs (rows true),
# at least one, read from LInlK up to `}` and the rest
def cv.G(
  +vs: List<&2, T.Val>,
  rows: Bool,
  +acc: List<&2, T.Val>,
  +ps0: List<&2, String>,
  +he0: List<&2, String>,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  match rows:
    case False{}:
      {T.wf.go(vs, T.WfItems{}) == True{} : Bool} -> {D1.cv.shorts(vs) == True{} : Bool} ->
        {L15.cv.end(rest) == True{} : Bool} -> cv.ThenA(vs, acc, ps0, he0, rw, hs, sk, ab, rest, PP) ->
        PP(T.doc.read(String.append(T.render.go(vs, ", ", False{}), SCon{']', rest}), T.MScan{cv.ar(acc, ps0, he0,
          rw, hs, he, ps, bk, qk, sk, un, lf, ab)}))
    case True{}:
      {List.is_empty(&2, T.Val, vs) == False{} : Bool} -> {T.wf.go(vs, T.WfInl{}) == True{} : Bool} ->
        {D1.cv.shorts(vs) == True{} : Bool} -> {L15.cv.end(rest) == True{} : Bool} ->
        {M8.cv.fr(acc, vs) == True{} : Bool} -> {T.inl.seal(acc) == acc : List<&2, T.Val>} ->
        cv.ThenI(vs, acc, ps0, he0, rw, hs, sk, ab, rest, PP) ->
        PP(T.doc.read(String.append(T.render.go(vs, ", ", False{}), SCon{'}', rest}), T.MScan{cv.ik(acc, ps0, he0,
          rw, hs, bk, qk, sk, un, lf, ab)}))

# reading a value from a value position, once its well-formedness and its
# strings' lengths are known: the claim the induction proves of each value
def cv.Rd(
  +vv: T.Val,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  {L15.cv.end(rest) == True{} : Bool} -> cv.Then(vv, rw, hs, he, ps, sk, ab, rest, PP) ->
    PP(T.doc.read(D1.cv.tx(vv, rest), T.MScan{cv.vp(rw, hs, he, ps, bk, qk, sk, un, lf, ab)}))

# Lists. own and the scanner's form both read a list one value at a time.

# own reads a list's head by itself
def cv.own.cons(
  xx: T.Val,
  +tt: List<&2, T.Val>
) -> {D1.own.rows(xx <> tt) == L15.cv.own1(xx) <> D1.own.rows(tt) : List<&2, T.Val>}:
  match xx:
    case T.VPair{nn, yy}:
      match yy:
        case T.VStr{_a}:
          {==}
        case T.VSpan{_a, _b}:
          {==}
        case T.VInt{_a, _b}:
          {==}
        case T.VFlo{_a, _b}:
          {==}
        case T.VBool{_a}:
          {==}
        case T.VWhen{_a}:
          {==}
        case T.VArr{_a}:
          {==}
        case T.VInl{_a}:
          {==}
        case T.VHead{_a, _b}:
          {==}
        case T.VAot{_a, _b}:
          {==}
        case T.VAots{_a, _b}:
          {==}
        case T.VPair{_a, _b}:
          {==}
    case T.VStr{_a}:
      {==}
    case T.VSpan{_a, _b}:
      {==}
    case T.VInt{_a, _b}:
      {==}
    case T.VFlo{_a, _b}:
      {==}
    case T.VBool{_a}:
      {==}
    case T.VWhen{_a}:
      {==}
    case T.VArr{_a}:
      {==}
    case T.VInl{_a}:
      {==}
    case T.VHead{_a, _b}:
      {==}
    case T.VAot{_a, _b}:
      {==}
    case T.VAots{_a, _b}:
      {==}

# and so does the scanner's form
def cv.raw.cons(
  xx: T.Val,
  +tt: List<&2, T.Val>
) -> {L15.cv.raw(xx <> tt) == L15.cv.raw1(xx) <> L15.cv.raw(tt) : List<&2, T.Val>}:
  match xx:
    case T.VPair{nn, yy}:
      match yy:
        case T.VStr{_a}:
          {==}
        case T.VSpan{_a, _b}:
          {==}
        case T.VInt{_a, _b}:
          {==}
        case T.VFlo{_a, _b}:
          {==}
        case T.VBool{_a}:
          {==}
        case T.VWhen{_a}:
          {==}
        case T.VArr{_a}:
          {==}
        case T.VInl{_a}:
          {==}
        case T.VHead{_a, _b}:
          {==}
        case T.VAot{_a, _b}:
          {==}
        case T.VAots{_a, _b}:
          {==}
        case T.VPair{_a, _b}:
          {==}
    case T.VStr{_a}:
      {==}
    case T.VSpan{_a, _b}:
      {==}
    case T.VInt{_a, _b}:
      {==}
    case T.VFlo{_a, _b}:
      {==}
    case T.VBool{_a}:
      {==}
    case T.VWhen{_a}:
      {==}
    case T.VArr{_a}:
      {==}
    case T.VInl{_a}:
      {==}
    case T.VHead{_a, _b}:
      {==}
    case T.VAot{_a, _b}:
      {==}
    case T.VAots{_a, _b}:
      {==}

# own reads a reversal onto a list as the reversal of what it reads
def cv.own.rev(
  xs: List<&2, T.Val>,
  +aa: List<&2, T.Val>
) -> {D1.own.rows(List.reverse.go(&2, T.Val, xs, aa))
  == List.reverse.go(&2, T.Val, D1.own.rows(xs), D1.own.rows(aa)) : List<&2, T.Val>}:
  match xs:
    case []:
      {==}
    case +hh <> +tt:
      Equal.trans(List<&2, T.Val>,
        D1.own.rows(List.reverse.go(&2, T.Val, tt, hh <> aa)),
        List.reverse.go(&2, T.Val, D1.own.rows(tt), D1.own.rows(hh <> aa)),
        List.reverse.go(&2, T.Val, D1.own.rows(hh <> tt), D1.own.rows(aa)),
        cv.own.rev(tt, hh <> aa),
        Equal.trans(List<&2, T.Val>,
          List.reverse.go(&2, T.Val, D1.own.rows(tt), D1.own.rows(hh <> aa)),
          List.reverse.go(&2, T.Val, L15.cv.own1(hh) <> D1.own.rows(tt), D1.own.rows(aa)),
          List.reverse.go(&2, T.Val, D1.own.rows(hh <> tt), D1.own.rows(aa)),
          Equal.cong(List<&2, T.Val>, List<&2, T.Val>, ys => List.reverse.go(&2, T.Val, D1.own.rows(tt), ys),
            D1.own.rows(hh <> aa), L15.cv.own1(hh) <> D1.own.rows(aa), cv.own.cons(hh, aa)),
          Equal.cong(List<&2, T.Val>, List<&2, T.Val>, ys => List.reverse.go(&2, T.Val, ys, D1.own.rows(aa)),
            L15.cv.own1(hh) <> D1.own.rows(tt), D1.own.rows(hh <> tt),
            Equal.sym(List<&2, T.Val>, D1.own.rows(hh <> tt), L15.cv.own1(hh) <> D1.own.rows(tt),
              cv.own.cons(hh, tt)))))

# a list appended to nothing is itself
def cv.app.nil(xs: List<&2, T.Val>) -> {List.append(&2, T.Val, xs, []) == xs : List<&2, T.Val>}:
  match xs:
    case []:
      {==}
    case +hh <> tt:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, ys => hh <> ys, List.append(&2, T.Val, tt, []), tt,
        cv.app.nil(tt))

# reversing twice puts a list back, what it was reversed onto after it
def cv.rr(
  xs: List<&2, T.Val>,
  aa: List<&2, T.Val>,
  bb: List<&2, T.Val>
) -> {List.reverse.go(&2, T.Val, List.reverse.go(&2, T.Val, xs, aa), bb)
  == List.reverse.go(&2, T.Val, aa, List.append(&2, T.Val, xs, bb)) : List<&2, T.Val>}:
  match xs:
    case []:
      {==}
    case hh <> tt:
      cv.rr(tt, hh <> aa, bb)

# reversing twice is the list
def cv.rev2(+xs: List<&2, T.Val>) -> {List.reverse(&2, T.Val, List.reverse(&2, T.Val, xs)) == xs : List<&2, T.Val>}:
  Equal.trans(List<&2, T.Val>, List.reverse.go(&2, T.Val, List.reverse.go(&2, T.Val, xs, []), []),
    List.append(&2, T.Val, xs, []), xs, cv.rr(xs, [], []), cv.app.nil(xs))

# The text. render writes an item or a pair's value as cv.tx writes the value,
# then the separator and the rest (cv.tl).

# the separator and the rest, then the closer
def cv.suf(
  vs: List<&2, T.Val>,
  +close: Char,
  +xx: String
) -> {String.append(cv.S(vs), SCon{close, xx}) == cv.tl(vs, close, xx) : String}:
  match vs:
    case []:
      {==}
    case _hh <> _tt:
      {==}

# a scalar's text, then the separator, the rest and the closer
def cv.at(
  +aa: String,
  +vs: List<&2, T.Val>,
  +close: Char,
  +xx: String
) -> {String.append(String.append(aa, cv.S(vs)), SCon{close, xx}) == String.append(aa, cv.tl(vs, close, xx)) : String}:
  Equal.trans(String, String.append(String.append(aa, cv.S(vs)), SCon{close, xx}),
    String.append(aa, String.append(cv.S(vs), SCon{close, xx})), String.append(aa, cv.tl(vs, close, xx)),
    Eq.append_assoc(aa, cv.S(vs), SCon{close, xx}),
    Equal.cong(String, String, zz => String.append(aa, zz), String.append(cv.S(vs), SCon{close, xx}),
      cv.tl(vs, close, xx), cv.suf(vs, close, xx)))

# a container's items and its closer, then the separator, the rest and the
# outer closer
def cv.cl(
  +rr: String,
  +c2: Char,
  +vs: List<&2, T.Val>,
  +close: Char,
  +xx: String
) -> {String.append(String.append(rr, SCon{c2, cv.S(vs)}), SCon{close, xx})
  == String.append(rr, SCon{c2, cv.tl(vs, close, xx)}) : String}:
  Equal.trans(String, String.append(String.append(rr, SCon{c2, cv.S(vs)}), SCon{close, xx}),
    String.append(rr, String.append(SCon{c2, cv.S(vs)}, SCon{close, xx})),
    String.append(rr, SCon{c2, cv.tl(vs, close, xx)}),
    Eq.append_assoc(rr, SCon{c2, cv.S(vs)}, SCon{close, xx}),
    Equal.cong(String, String, zz => String.append(rr, SCon{c2, zz}), String.append(cv.S(vs), SCon{close, xx}),
      cv.tl(vs, close, xx), cv.suf(vs, close, xx)))

# an item and the rest of the items, then the closer: the item's text, then
# what follows it
def cv.itx(
  ii: T.Val,
  +tt: List<&2, T.Val>,
  +close: Char,
  +xx: String,
  hw: {D1.cv.wf(ii) == True{} : Bool}
) -> {String.append(T.render.go(ii <> tt, ", ", False{}), SCon{close, xx}) == D1.cv.tx(ii, cv.tl(tt, close, xx))
  : String}:
  match ii:
    case T.VArr{+items}:
      Equal.cong(String, String, zz => SCon{'[', zz},
        String.append(String.append(T.render.go(items, ", ", False{}), SCon{']', cv.S(tt)}), SCon{close, xx}),
        String.append(T.render.go(items, ", ", False{}), SCon{']', cv.tl(tt, close, xx)}),
        cv.cl(T.render.go(items, ", ", False{}), ']', tt, close, xx))
    case T.VInl{+rows}:
      Equal.cong(String, String, zz => SCon{'{', zz},
        String.append(String.append(T.render.go(rows, ", ", False{}), SCon{'}', cv.S(tt)}), SCon{close, xx}),
        String.append(T.render.go(rows, ", ", False{}), SCon{'}', cv.tl(tt, close, xx)}),
        cv.cl(T.render.go(rows, ", ", False{}), '}', tt, close, xx))
    case T.VStr{+aa}:
      cv.at(T.render.atom(T.VStr{aa}), tt, close, xx)
    case T.VSpan{+aa, +bb}:
      cv.at(T.render.atom(T.VSpan{aa, bb}), tt, close, xx)
    case T.VInt{+aa, +bb}:
      cv.at(T.render.atom(T.VInt{aa, bb}), tt, close, xx)
    case T.VFlo{+aa, +bb}:
      cv.at(T.render.atom(T.VFlo{aa, bb}), tt, close, xx)
    case T.VBool{+aa}:
      cv.at(T.render.atom(T.VBool{aa}), tt, close, xx)
    case T.VWhen{+aa}:
      cv.at(T.render.atom(T.VWhen{aa}), tt, close, xx)
    case T.VHead{aa, bb}:
      Eq.bit.absurd(&2, {String.append(T.render.go(T.VHead{aa, bb} <> tt, ", ", False{}), SCon{close, xx})
        == D1.cv.tx(T.VHead{aa, bb}, cv.tl(tt, close, xx)) : String}, hw)
    case T.VAot{aa, bb}:
      Eq.bit.absurd(&2, {String.append(T.render.go(T.VAot{aa, bb} <> tt, ", ", False{}), SCon{close, xx})
        == D1.cv.tx(T.VAot{aa, bb}, cv.tl(tt, close, xx)) : String}, hw)
    case T.VAots{aa, bb}:
      Eq.bit.absurd(&2, {String.append(T.render.go(T.VAots{aa, bb} <> tt, ", ", False{}), SCon{close, xx})
        == D1.cv.tx(T.VAots{aa, bb}, cv.tl(tt, close, xx)) : String}, hw)
    case T.VPair{aa, bb}:
      Eq.bit.absurd(&2, {String.append(T.render.go(T.VPair{aa, bb} <> tt, ", ", False{}), SCon{close, xx})
        == D1.cv.tx(T.VPair{aa, bb}, cv.tl(tt, close, xx)) : String}, hw)

# the text after an item ends a value
def cv.tl.end(
  vs: List<&2, T.Val>,
  +xx: String
) -> {L15.cv.end(cv.tl(vs, ']', xx)) == True{} : Bool}:
  match vs:
    case []:
      {==}
    case _hh <> _tt:
      {==}

# and so does the text after an inline table's pair
def cv.tl.endi(
  vs: List<&2, T.Val>,
  +xx: String
) -> {L15.cv.end(cv.tl(vs, '}', xx)) == True{} : Bool}:
  match vs:
    case []:
      {==}
    case _hh <> _tt:
      {==}

# An item's first character. LArr holds any character that is no blank, no
# newline, no `#` and no `]`, and reads it again in LVal with back at LVal:
# from there on the item is read as a value in a value position.

# a character LArr does not keep for itself
def cv.bad(+cc: Char) -> Bool:
  Bool.or(T.ch.sp(cc), Bool.or(T.ch.nl(cc), Bool.or(Char.is_eq(cc, '#'), Char.is_eq(cc, ']'))))

# the first character of a text is one LArr passes on
def cv.xbad(xs: String) -> Bool:
  match xs:
    case SNil{}:
      True{}
    case SCon{+cc, _tt}:
      cv.bad(cc)

# a character no delimiter is no character LArr keeps
def cv.bad.d(
  aa: Bool,
  bb: Bool,
  cc: Bool,
  dd: Bool,
  ee: Bool,
  ff: Bool,
  hh: {Bool.or(aa, Bool.or(bb, Bool.or(cc, Bool.or(dd, Bool.or(ee, ff))))) == False{} : Bool}
) -> {Bool.or(aa, Bool.or(bb, Bool.or(cc, ee))) == False{} : Bool}:
  match aa:
    case True{}:
      Eq.bit.absurd2(&2, {Bool.or(True{}, Bool.or(bb, Bool.or(cc, ee))) == False{} : Bool}, hh)
    case False{}:
      match bb:
        case True{}:
          Eq.bit.absurd2(&2, {Bool.or(False{}, Bool.or(True{}, Bool.or(cc, ee))) == False{} : Bool}, hh)
        case False{}:
          match cc:
            case True{}:
              Eq.bit.absurd2(&2, {Bool.or(False{}, Bool.or(False{}, Bool.or(True{}, ee))) == False{} : Bool}, hh)
            case False{}:
              match dd:
                case True{}:
                  Eq.bit.absurd2(&2, {Bool.or(False{}, Bool.or(False{}, Bool.or(False{}, ee))) == False{} : Bool},
                    hh)
                case False{}:
                  Eq.or.left_false(ee, ff, hh)

# a bare value's text starts with such a character
def cv.xb.w(
  ss: String,
  +zz: String,
  hc: {L18.word.chars(ss) == True{} : Bool}
) -> {cv.xbad(String.append(ss, zz)) == False{} : Bool}:
  match ss:
    case SNil{}:
      Eq.bit.absurd(&2, {cv.xbad(String.append(SNil{}, zz)) == False{} : Bool}, hc)
    case SCon{hh, tt}:
      match hh:
        case Chr{+xx}:
          +h1 = {Eq.and.left(D1.word.first(Chr{xx}), L18.word.rest(tt), hc)
            : {D1.word.first(Chr{xx}) == True{} : Bool}}
          +hw = {Eq.and.left(D1.word.char(Chr{xx}), Bool.not(Bool.or(Char.is_eq(Chr{xx}, '['),
            Char.is_eq(Chr{xx}, '{'))), h1) : {D1.word.char(Chr{xx}) == True{} : Bool}}
          cv.bad.d(T.ch.sp(Chr{xx}), T.ch.nl(Chr{xx}), Char.is_eq(Chr{xx}, '#'), Char.is_eq(Chr{xx}, ','),
            Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '}'), M1.wd.delim(Chr{xx}, hw))

# every value's text starts with such a character
def cv.xb(
  ii: T.Val,
  +zz: String,
  hw: {D1.cv.wf(ii) == True{} : Bool}
) -> {cv.xbad(D1.cv.tx(ii, zz)) == False{} : Bool}:
  match ii:
    case T.VArr{_items}:
      {==}
    case T.VInl{_rows}:
      {==}
    case T.VStr{_aa}:
      {==}
    case T.VSpan{+src, +nn}:
      %Equal.sym(String, T.span.quote(src, nn), T.key.basic(T.string(T.VSpan{src, nn})),
        L12.span_quote_basic(src, nn)) : {cv.xbad(String.append(_, zz)) == False{} : Bool}
      {==}
    case T.VInt{+aa, +bb}:
      cv.xb.w(T.render.atom(T.VInt{aa, bb}), zz, cv.wch(T.VInt{aa, bb}, hw))
    case T.VFlo{+aa, +bb}:
      cv.xb.w(T.render.atom(T.VFlo{aa, bb}), zz, cv.wch(T.VFlo{aa, bb}, hw))
    case T.VBool{+aa}:
      cv.xb.w(T.render.atom(T.VBool{aa}), zz, cv.wch(T.VBool{aa}, hw))
    case T.VWhen{+aa}:
      cv.xb.w(T.render.atom(T.VWhen{aa}), zz, cv.wch(T.VWhen{aa}, hw))
    case T.VHead{aa, bb}:
      Eq.bit.absurd(&2, {cv.xbad(D1.cv.tx(T.VHead{aa, bb}, zz)) == False{} : Bool}, hw)
    case T.VAot{aa, bb}:
      Eq.bit.absurd(&2, {cv.xbad(D1.cv.tx(T.VAot{aa, bb}, zz)) == False{} : Bool}, hw)
    case T.VAots{aa, bb}:
      Eq.bit.absurd(&2, {cv.xbad(D1.cv.tx(T.VAots{aa, bb}, zz)) == False{} : Bool}, hw)
    case T.VPair{aa, bb}:
      Eq.bit.absurd(&2, {cv.xbad(D1.cv.tx(T.VPair{aa, bb}, zz)) == False{} : Bool}, hw)

# the value state's step leaves nothing held on every character but a newline
def cv.a2v.vg(
  sp: Bool,
  nl: Bool,
  hash: Bool,
  qq: Bool,
  lit: Bool,
  br: Bool,
  inl: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +cc: Char,
  hnl: {nl == False{} : Bool}
) -> {T.lex.val.go(sp, nl, hash, qq, lit, br, inl, cv.vp(rw, hs, he, ps, T.LVal{}, qk, sk, un, lf, ab), cc)
  == T.read.once2(T.lex.val.go(sp, nl, hash, qq, lit, br, inl, cv.vp(rw, hs, he, ps, T.LVal{}, qk, sk, un, lf, ab),
  cc)) : T.St}:
  match sp:
    case True{}:
      {==}
    case False{}:
      match nl:
        case True{}:
          Eq.bit.absurd2(&2, {T.lex.val.go(False{}, True{}, hash, qq, lit, br, inl, cv.vp(rw, hs, he, ps, T.LVal{},
            qk, sk, un, lf, ab), cc) == T.read.once2(T.lex.val.go(False{}, True{}, hash, qq, lit, br, inl,
            cv.vp(rw, hs, he, ps, T.LVal{}, qk, sk, un, lf, ab), cc)) : T.St}, hnl)
        case False{}:
          match hash:
            case True{}:
              {==}
            case False{}:
              match qq:
                case True{}:
                  {==}
                case False{}:
                  match lit:
                    case True{}:
                      {==}
                    case False{}:
                      match br:
                        case True{}:
                          {==}
                        case False{}:
                          match inl:
                            case True{}:
                              {==}
                            case False{}:
                              {==}

# LArr holds a character it does not keep and reads it in LVal
def cv.a2v.ag(
  sp: Bool,
  nl: Bool,
  hash: Bool,
  rb: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +cc: Char,
  hsp: {sp == False{} : Bool},
  hnl: {nl == False{} : Bool},
  hhs: {hash == False{} : Bool},
  hrb: {rb == False{} : Bool}
) -> {T.read.once2(T.lex.arr.go(sp, nl, hash, rb, T.St{"", rw, hs, he, ps, [], T.LArr{}, bk, qk, sk, T.HNone{}, un,
  lf, ab, False{}}, cc)) == T.lex.val(cv.vp(rw, hs, he, ps, T.LVal{}, qk, sk, un, lf, ab), cc) : T.St}:
  match sp:
    case True{}:
      Eq.bit.absurd2(&2, {T.read.once2(T.lex.arr.go(True{}, nl, hash, rb, T.St{"", rw, hs, he, ps, [], T.LArr{}, bk,
        qk, sk, T.HNone{}, un, lf, ab, False{}}, cc)) == T.lex.val(cv.vp(rw, hs, he, ps, T.LVal{}, qk, sk, un, lf, ab),
        cc) : T.St}, hsp)
    case False{}:
      match nl:
        case True{}:
          Eq.bit.absurd2(&2, {T.read.once2(T.lex.arr.go(False{}, True{}, hash, rb, T.St{"", rw, hs, he, ps, [],
            T.LArr{}, bk, qk, sk, T.HNone{}, un, lf, ab, False{}}, cc)) == T.lex.val(cv.vp(rw, hs, he, ps, T.LVal{},
            qk, sk, un, lf, ab), cc) : T.St}, hnl)
        case False{}:
          match hash:
            case True{}:
              Eq.bit.absurd2(&2, {T.read.once2(T.lex.arr.go(False{}, False{}, True{}, rb, T.St{"", rw, hs, he, ps, [],
                T.LArr{}, bk, qk, sk, T.HNone{}, un, lf, ab, False{}}, cc)) == T.lex.val(cv.vp(rw, hs, he, ps,
                T.LVal{}, qk, sk, un, lf, ab), cc) : T.St}, hhs)
            case False{}:
              match rb:
                case True{}:
                  Eq.bit.absurd2(&2, {T.read.once2(T.lex.arr.go(False{}, False{}, False{}, True{}, T.St{"", rw, hs,
                    he, ps, [], T.LArr{}, bk, qk, sk, T.HNone{}, un, lf, ab, False{}}, cc)) == T.lex.val(cv.vp(rw, hs,
                    he, ps, T.LVal{}, qk, sk, un, lf, ab), cc) : T.St}, hrb)
                case False{}:
                  {==}

# the fast steps of LArr and of LVal with back at LVal agree on such a
# character
def cv.a2v.ws(
  sp: Bool,
  nl: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +cc: Char,
  hsp: {sp == False{} : Bool},
  hnl: {nl == False{} : Bool},
  +fsp: {T.ch.sp(cc) == False{} : Bool},
  +fnl: {T.ch.nl(cc) == False{} : Bool},
  fhs: {Char.is_eq(cc, '#') == False{} : Bool},
  frb: {Char.is_eq(cc, ']') == False{} : Bool}
) -> {T.read.fast.ws(sp, nl, True{}, "", rw, hs, he, ps, [], T.LArr{}, bk, qk, sk, un, lf, ab, cc)
  == T.read.fast.ws(sp, nl, False{}, "", rw, hs, he, ps, [], T.LVal{}, T.LVal{}, qk, sk, un, lf, ab, cc) : T.St}:
  match sp:
    case True{}:
      Eq.bit.absurd2(&2, {T.read.fast.ws(True{}, nl, True{}, "", rw, hs, he, ps, [], T.LArr{}, bk, qk, sk, un, lf, ab,
        cc) == T.read.fast.ws(True{}, nl, False{}, "", rw, hs, he, ps, [], T.LVal{}, T.LVal{}, qk, sk, un, lf, ab, cc)
        : T.St}, hsp)
    case False{}:
      match nl:
        case True{}:
          Eq.bit.absurd2(&2, {T.read.fast.ws(False{}, True{}, True{}, "", rw, hs, he, ps, [], T.LArr{}, bk, qk, sk,
            un, lf, ab, cc) == T.read.fast.ws(False{}, True{}, False{}, "", rw, hs, he, ps, [], T.LVal{}, T.LVal{},
            qk, sk, un, lf, ab, cc) : T.St}, hnl)
        case False{}:
          Equal.trans(T.St,
            T.read.once2(T.lex.arr.go(T.ch.sp(cc), T.ch.nl(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, ']'),
              T.St{"", rw, hs, he, ps, [], T.LArr{}, bk, qk, sk, T.HNone{}, un, lf, ab, False{}}, cc)),
            T.lex.val(cv.vp(rw, hs, he, ps, T.LVal{}, qk, sk, un, lf, ab), cc),
            T.read.once2(T.lex.val(cv.vp(rw, hs, he, ps, T.LVal{}, qk, sk, un, lf, ab), cc)),
            cv.a2v.ag(T.ch.sp(cc), T.ch.nl(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, ']'), rw, hs, he, ps, bk, qk,
              sk, un, lf, ab, cc, fsp, fnl, fhs, frb),
            cv.a2v.vg(T.ch.sp(cc), T.ch.nl(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, '"'), Char.is_eq(cc, '\''),
              Char.is_eq(cc, '['), Char.is_eq(cc, '{'), rw, hs, he, ps, qk, sk, un, lf, ab, cc, fnl))

# a text whose first character LArr passes on reads from LArr as from LVal
# with back at LVal
def cv.a2v(
  xs: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +hb: {cv.xbad(xs) == False{} : Bool}
) -> {T.doc.read(xs, T.MScan{T.St{"", rw, hs, he, ps, [], T.LArr{}, bk, qk, sk, T.HNone{}, un, lf, ab, False{}}})
  == T.doc.read(xs, T.MScan{cv.vp(rw, hs, he, ps, T.LVal{}, qk, sk, un, lf, ab)}) : T.Doc}:
  match xs:
    case SNil{}:
      Eq.bit.absurd2(&2, {T.doc.read(SNil{}, T.MScan{T.St{"", rw, hs, he, ps, [], T.LArr{}, bk, qk, sk, T.HNone{}, un,
        lf, ab, False{}}}) == T.doc.read(SNil{}, T.MScan{cv.vp(rw, hs, he, ps, T.LVal{}, qk, sk, un, lf, ab)}) : T.Doc},
        hb)
    case SCon{+cc, +tt}:
      +r1 = {Eq.or.right_false(T.ch.sp(cc), Bool.or(T.ch.nl(cc), Bool.or(Char.is_eq(cc, '#'), Char.is_eq(cc, ']'))),
        hb) : {Bool.or(T.ch.nl(cc), Bool.or(Char.is_eq(cc, '#'), Char.is_eq(cc, ']'))) == False{} : Bool}}
      +r2 = {Eq.or.right_false(T.ch.nl(cc), Bool.or(Char.is_eq(cc, '#'), Char.is_eq(cc, ']')), r1)
        : {Bool.or(Char.is_eq(cc, '#'), Char.is_eq(cc, ']')) == False{} : Bool}}
      Equal.cong(T.Mode, T.Doc, md => T.doc.read(tt, md),
        T.doc.scan(T.St{"", rw, hs, he, ps, [], T.LArr{}, bk, qk, sk, T.HNone{}, un, lf, ab, False{}}, cc),
        T.doc.scan(cv.vp(rw, hs, he, ps, T.LVal{}, qk, sk, un, lf, ab), cc),
        scan.fast(Char.is_eq(cc, '"'), Char.is_eq(cc, '\''), U32.is_eq(Char.to_u32(cc), 13),
          T.St{"", rw, hs, he, ps, [], T.LArr{}, bk, qk, sk, T.HNone{}, un, lf, ab, False{}},
          cv.vp(rw, hs, he, ps, T.LVal{}, qk, sk, un, lf, ab), cc,
          cv.a2v.ws(T.ch.sp(cc), T.ch.nl(cc), rw, hs, he, ps, bk, qk, sk, un, lf, ab, cc,
            Eq.or.left_false(T.ch.sp(cc), Bool.or(T.ch.nl(cc), Bool.or(Char.is_eq(cc, '#'), Char.is_eq(cc, ']'))),
              hb),
            Eq.or.left_false(T.ch.nl(cc), Bool.or(Char.is_eq(cc, '#'), Char.is_eq(cc, ']')), r1),
            Eq.or.left_false(T.ch.sp(cc), Bool.or(T.ch.nl(cc), Bool.or(Char.is_eq(cc, '#'), Char.is_eq(cc, ']'))),
              hb),
            Eq.or.left_false(T.ch.nl(cc), Bool.or(Char.is_eq(cc, '#'), Char.is_eq(cc, ']')), r1),
            Eq.or.left_false(Char.is_eq(cc, '#'), Char.is_eq(cc, ']'), r2),
            Eq.or.right_false(Char.is_eq(cc, '#'), Char.is_eq(cc, ']'), r2))))

# The frame's items. Putting a value that own reads as the scanner's form of
# the next item keeps what own reads of the frame the items read so far,
# pushed onto what it held.

# one more value put, read as one more item
def cv.grew(
  ii: T.Val,
  +tt: List<&2, T.Val>,
  +vv: T.Val,
  +acc: List<&2, T.Val>,
  ac2: List<&2, T.Val>,
  hh: {L15.cv.own1(vv) == L15.cv.raw1(ii) : T.Val},
  h2: {D1.own.rows(ac2) == List.reverse.go(&2, T.Val, L15.cv.raw(tt), D1.own.rows(vv <> acc)) : List<&2, T.Val>}
) -> {D1.own.rows(ac2) == List.reverse.go(&2, T.Val, L15.cv.raw(ii <> tt), D1.own.rows(acc)) : List<&2, T.Val>}:
  Equal.trans(List<&2, T.Val>, D1.own.rows(ac2),
    List.reverse.go(&2, T.Val, L15.cv.raw(tt), D1.own.rows(vv <> acc)),
    List.reverse.go(&2, T.Val, L15.cv.raw(ii <> tt), D1.own.rows(acc)), h2,
    Equal.trans(List<&2, T.Val>, List.reverse.go(&2, T.Val, L15.cv.raw(tt), D1.own.rows(vv <> acc)),
      List.reverse.go(&2, T.Val, L15.cv.raw(tt), L15.cv.own1(vv) <> D1.own.rows(acc)),
      List.reverse.go(&2, T.Val, L15.cv.raw(ii <> tt), D1.own.rows(acc)),
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, ys => List.reverse.go(&2, T.Val, L15.cv.raw(tt), ys),
        D1.own.rows(vv <> acc), L15.cv.own1(vv) <> D1.own.rows(acc), cv.own.cons(vv, acc)),
      Equal.trans(List<&2, T.Val>, List.reverse.go(&2, T.Val, L15.cv.raw(tt), L15.cv.own1(vv) <> D1.own.rows(acc)),
        List.reverse.go(&2, T.Val, L15.cv.raw1(ii) <> L15.cv.raw(tt), D1.own.rows(acc)),
        List.reverse.go(&2, T.Val, L15.cv.raw(ii <> tt), D1.own.rows(acc)),
        Equal.cong(T.Val, List<&2, T.Val>, yy => List.reverse.go(&2, T.Val, L15.cv.raw(tt), yy <> D1.own.rows(acc)),
          L15.cv.own1(vv), L15.cv.raw1(ii), hh),
        Equal.cong(List<&2, T.Val>, List<&2, T.Val>, ys => List.reverse.go(&2, T.Val, ys, D1.own.rows(acc)),
          L15.cv.raw1(ii) <> L15.cv.raw(tt), L15.cv.raw(ii <> tt),
          Equal.sym(List<&2, T.Val>, L15.cv.raw(ii <> tt), L15.cv.raw1(ii) <> L15.cv.raw(tt),
            cv.raw.cons(ii, tt))))))

# `]` in LArr closes the array: what the frame holds, reversed, is put
def cv.close0(
  +acc: List<&2, T.Val>,
  +ps0: List<&2, String>,
  +he0: List<&2, String>,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  then: cv.ThenA([], acc, ps0, he0, rw, hs, sk, ab, rest, PP)
) -> PP(T.doc.read(SCon{']', rest}, T.MScan{cv.ar(acc, ps0, he0, rw, hs, he, ps, bk, qk, sk, un, lf, ab)})):
  pp.step(PP, T.doc.read(SCon{']', rest}, T.MScan{cv.ar(acc, ps0, he0, rw, hs, he, ps, bk, qk, sk, un, lf, ab)}),
    T.doc.read(rest, T.MScan{cv.put(sk, T.VArr{List.reverse(&2, T.Val, acc)}, rw, hs, he0, ps0, bk, qk, un, lf, ab)}),
    Equal.cong(T.St, T.Doc, st => T.doc.read(rest, T.MScan{st}),
      T.read.once2(cv.put(sk, T.VArr{List.reverse(&2, T.Val, acc)}, rw, hs, he0, ps0, bk, qk, un, lf, ab)),
      cv.put(sk, T.VArr{List.reverse(&2, T.Val, acc)}, rw, hs, he0, ps0, bk, qk, un, lf, ab),
      Equal.sym(T.St, cv.put(sk, T.VArr{List.reverse(&2, T.Val, acc)}, rw, hs, he0, ps0, bk, qk, un, lf, ab),
        T.read.once2(cv.put(sk, T.VArr{List.reverse(&2, T.Val, acc)}, rw, hs, he0, ps0, bk, qk, un, lf, ab)),
        M9.tk.once(sk, T.VArr{List.reverse(&2, T.Val, acc)}, "", rw, hs, he0, ps0, bk, qk, un, lf, ab, False{}))),
    then(acc, bk, qk, un, lf, {==}))

# the claim for the items after one, from the frame with any value put onto
# it and any fields that value leaves
def cv.IhA(
  +tt: List<&2, T.Val>,
  +acc: List<&2, T.Val>,
  +ps0: List<&2, String>,
  +he0: List<&2, String>,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  @v2: T.Val -> @b2: T.Lex -> @q2: T.QKind -> @u2: U32 -> @l2: U32 ->
    cv.G(tt, False{}, v2 <> acc, ps0, he0, rw, hs, he0, ps0, b2, q2, sk, u2, l2, ab, rest, PP)

# after an item: `]` closes the array, and ", " waits for the next item
def cv.after(
  tt: List<&2, T.Val>,
  ii: T.Val,
  +vv: T.Val,
  +acc: List<&2, T.Val>,
  +ps0: List<&2, String>,
  +he0: List<&2, String>,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  hh: {L15.cv.own1(vv) == L15.cv.raw1(ii) : T.Val},
  ih_t: cv.IhA(tt, acc, ps0, he0, rw, hs, sk, ab, rest, PP),
  hwt: {T.wf.go(tt, T.WfItems{}) == True{} : Bool},
  hst: {D1.cv.shorts(tt) == True{} : Bool},
  hn: {L15.cv.end(rest) == True{} : Bool},
  then: cv.ThenA(ii <> tt, acc, ps0, he0, rw, hs, sk, ab, rest, PP)
) -> PP(T.doc.read(cv.tl(tt, ']', rest), T.MScan{cv.put(T.CArr{acc, ps0, he0} <> sk, vv, rw, hs, he, ps, bk, qk, un,
  lf, ab)})):
  match tt:
    case []:
      pp.step(PP, T.doc.read(SCon{']', rest}, T.MScan{cv.put(T.CArr{acc, ps0, he0} <> sk, vv, rw, hs, he, ps, bk, qk,
        un, lf, ab)}),
        T.doc.read(rest, T.MScan{cv.put(sk, T.VArr{List.reverse(&2, T.Val, vv <> acc)}, rw, hs, he0, ps0, bk, qk, un,
          lf, ab)}),
        Equal.cong(T.St, T.Doc, st => T.doc.read(rest, T.MScan{st}),
          T.read.once2(cv.put(sk, T.VArr{List.reverse(&2, T.Val, vv <> acc)}, rw, hs, he0, ps0, bk, qk, un, lf, ab)),
          cv.put(sk, T.VArr{List.reverse(&2, T.Val, vv <> acc)}, rw, hs, he0, ps0, bk, qk, un, lf, ab),
          Equal.sym(T.St, cv.put(sk, T.VArr{List.reverse(&2, T.Val, vv <> acc)}, rw, hs, he0, ps0, bk, qk, un, lf,
            ab), T.read.once2(cv.put(sk, T.VArr{List.reverse(&2, T.Val, vv <> acc)}, rw, hs, he0, ps0, bk, qk, un, lf,
            ab)), M9.tk.once(sk, T.VArr{List.reverse(&2, T.Val, vv <> acc)}, "", rw, hs, he0, ps0, bk, qk, un, lf, ab,
            False{}))),
        then(vv <> acc, bk, qk, un, lf, cv.grew(ii, [], vv, acc, vv <> acc, hh, {==})))
    case +h2 <> +t2:
      ih_t(vv, bk, qk, un, lf)(hwt, hst, hn,
        +ac2 => b3 => q3 => u3 => l3 => h3 => then(ac2, b3, q3, u3, l3, cv.grew(ii, h2 <> t2, vv, acc, ac2, hh, h3)))

# an item, then what follows it: the item is read as a value, from LVal with
# back at LVal, and put onto the frame
def cv.item(
  +ii: T.Val,
  +tt: List<&2, T.Val>,
  +acc: List<&2, T.Val>,
  +ps0: List<&2, String>,
  +he0: List<&2, String>,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  rd: cv.Rd(ii, rw, hs, he, ps, T.LVal{}, qk, T.CArr{acc, ps0, he0} <> sk, un, lf, ab, cv.tl(tt, ']', rest), PP),
  ih_t: cv.IhA(tt, acc, ps0, he0, rw, hs, sk, ab, rest, PP),
  +hw: {D1.cv.wf(ii) == True{} : Bool},
  hwt: {T.wf.go(tt, T.WfItems{}) == True{} : Bool},
  hst: {D1.cv.shorts(tt) == True{} : Bool},
  +hn: {L15.cv.end(rest) == True{} : Bool},
  then: cv.ThenA(ii <> tt, acc, ps0, he0, rw, hs, sk, ab, rest, PP)
) -> PP(T.doc.read(String.append(T.render.go(ii <> tt, ", ", False{}), SCon{']', rest}), T.MScan{cv.ar(acc, ps0, he0,
  rw, hs, he, ps, bk, qk, sk, un, lf, ab)})):
  +zz = {cv.tl(tt, ']', rest) : String}
  pp.step(PP, T.doc.read(String.append(T.render.go(ii <> tt, ", ", False{}), SCon{']', rest}), T.MScan{cv.ar(acc, ps0,
    he0, rw, hs, he, ps, bk, qk, sk, un, lf, ab)}),
    T.doc.read(D1.cv.tx(ii, zz), T.MScan{cv.vp(rw, hs, he, ps, T.LVal{}, qk, T.CArr{acc, ps0, he0} <> sk, un, lf,
      ab)}),
    Equal.trans(T.Doc,
      T.doc.read(String.append(T.render.go(ii <> tt, ", ", False{}), SCon{']', rest}), T.MScan{cv.ar(acc, ps0, he0,
        rw, hs, he, ps, bk, qk, sk, un, lf, ab)}),
      T.doc.read(D1.cv.tx(ii, zz), T.MScan{cv.ar(acc, ps0, he0, rw, hs, he, ps, bk, qk, sk, un, lf, ab)}),
      T.doc.read(D1.cv.tx(ii, zz), T.MScan{cv.vp(rw, hs, he, ps, T.LVal{}, qk, T.CArr{acc, ps0, he0} <> sk, un, lf,
        ab)}),
      Equal.cong(String, T.Doc, xs => T.doc.read(xs, T.MScan{cv.ar(acc, ps0, he0, rw, hs, he, ps, bk, qk, sk, un, lf,
        ab)}), String.append(T.render.go(ii <> tt, ", ", False{}), SCon{']', rest}), D1.cv.tx(ii, zz),
        cv.itx(ii, tt, ']', rest, hw)),
      cv.a2v(D1.cv.tx(ii, zz), rw, hs, he, ps, bk, qk, T.CArr{acc, ps0, he0} <> sk, un, lf, ab, cv.xb(ii, zz, hw))),
    rd(cv.tl.end(tt, rest), +vv => b2 => q2 => u2 => l2 => hh => cv.after(tt, ii, vv, acc, ps0, he0, rw, hs, he, ps,
      b2, q2, sk, u2, l2, ab, rest, PP, hh, ih_t, hwt, hst, hn, then)))

# Inline tables. An inline table's key is read from any uni and left: a
# string value before it, in the same inline table, may have left them
# anywhere a \u escape puts them. WP0's quoted-segment family fixes both at
# 0, so a quoted key is read here by the same family over a scanner that
# keeps them as parameters, as WP-S's ls does for a string (qu).

# a scanner inside a quoted key, its characters so far reversed in buf, back
# wherever the last escape left it, and uni and left as they are
def qu(
  rw: List<&2, T.Val>,
  hs: List<&2, String>,
  he: List<&2, String>,
  ps: List<&2, String>,
  sk: List<&2, T.Ctx>,
  ab: Bool,
  bk: T.Lex,
  un: U32,
  lf: U32,
  buf: List<&2, Char>
) -> T.St:
  T.St{"", rw, hs, he, ps, buf, T.LKeyQ{}, bk, T.QBasic{}, sk, T.HNone{}, un, lf, ab, False{}}

# the rest of the walk from a quoted key with buf in its buffer, whatever
# back, uni and left are
def qu.Then(
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  @b2: T.Lex -> @u2: U32 -> @l2: U32 ->
    PP(T.doc.read(rest, T.MScan{qu(rw, hs, he, ps, sk, ab, b2, u2, l2, buf)}))

# one character's escape read in a quoted key, then the rest of the text
def qu.Goal(
  +uu: U32,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  qu.Then(rw, hs, he, ps, sk, ab, Chr{uu} <> buf, rest, PP) ->
    PP(T.doc.read(String.append(L12.esc(Chr{uu}), rest), T.MScan{qu(rw, hs, he, ps, sk, ab, bk, un, lf, buf)}))

# the fast step of a character in a quoted key is the key's full step
def qu.fast(
  +uu: U32,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>
) -> {T.read.fast(qu(rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu}) == T.read.once2(T.lex.kq.go(U32.is_eq(uu, 34),
  U32.is_eq(uu, 92), True{}, Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)), qu(rw, hs, he, ps, sk, ab, bk, un, lf, buf),
  Chr{uu}, T.LAfter{}, T.LKeyQ{})) : T.St}:
  {==}

# a character that is no control is pushed: str.bad passes it
def qu.char(
  ctl: Bool,
  +uu: U32,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  hc: {ctl == False{} : Bool}
) -> {T.read.once2(T.lex.kq.char.go(T.str.bad.go(ctl, U32.is_eq(uu, 9), Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)),
  False{}), qu(rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu}, T.LKeyQ{}))
  == qu(rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf) : T.St}:
  match ctl:
    case False{}:
      {==}
    case True{}:
      Eq.bit.absurd2(&2, {T.read.once2(T.lex.kq.char.go(T.str.bad.go(True{}, U32.is_eq(uu, 9),
        Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)), False{}), qu(rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu},
        T.LKeyQ{})) == qu(rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf) : T.St}, hc)

# a character that is no quote, no backslash and no newline is no closer and
# no escape
def qu.go(
  quote: Bool,
  bs: Bool,
  nl: Bool,
  +uu: U32,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  hq: {quote == False{} : Bool},
  hb: {bs == False{} : Bool},
  hn: {nl == False{} : Bool},
  hc: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool}
) -> {T.read.once2(T.lex.kq.go(quote, bs, True{}, nl, qu(rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu}, T.LAfter{},
  T.LKeyQ{})) == qu(rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf) : T.St}:
  match quote:
    case True{}:
      Eq.bit.absurd2(&2, {T.read.once2(T.lex.kq.go(True{}, bs, True{}, nl, qu(rw, hs, he, ps, sk, ab, bk, un, lf, buf),
        Chr{uu}, T.LAfter{}, T.LKeyQ{})) == qu(rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf) : T.St}, hq)
    case False{}:
      match bs:
        case True{}:
          Eq.bit.absurd2(&2, {T.read.once2(T.lex.kq.go(False{}, True{}, True{}, nl, qu(rw, hs, he, ps, sk, ab, bk, un,
            lf, buf), Chr{uu}, T.LAfter{}, T.LKeyQ{})) == qu(rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf)
            : T.St}, hb)
        case False{}:
          match nl:
            case True{}:
              Eq.bit.absurd2(&2, {T.read.once2(T.lex.kq.go(False{}, False{}, True{}, True{}, qu(rw, hs, he, ps, sk,
                ab, bk, un, lf, buf), Chr{uu}, T.LAfter{}, T.LKeyQ{})) == qu(rw, hs, he, ps, sk, ab, bk, un, lf,
                Chr{uu} <> buf) : T.St}, hn)
            case False{}:
              qu.char(Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), uu, rw, hs, he, ps, sk, ab, bk, un, lf, buf, hc)

# the fast step pushes a character
def qu.Fast(
  +uu: U32,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>
) -> Type:
  {T.read.fast(qu(rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu})
    == qu(rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf) : T.St}

# the doc.scan dispatch sends such a character to the fast step, and an
# apostrophe comes back from doc.wrap in the key's state
def qu.q(
  dq: Bool,
  sq: Bool,
  cr: Bool,
  +uu: U32,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  hq: {dq == False{} : Bool},
  hr: {cr == False{} : Bool},
  fast: qu.Fast(uu, rw, hs, he, ps, sk, ab, bk, un, lf, buf)
) -> {T.doc.scan.q(dq, sq, cr, qu(rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu})
  == T.MScan{qu(rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf)} : T.Mode}:
  match dq:
    case True{}:
      Eq.bit.absurd2(&2, {T.doc.scan.q(True{}, sq, cr, qu(rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu})
        == T.MScan{qu(rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf)} : T.Mode}, hq)
    case False{}:
      match sq:
        case True{}:
          Equal.cong(T.St, T.Mode, st => T.doc.wrap(st),
            T.read.fast(qu(rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu}),
            qu(rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf), fast)
        case False{}:
          match cr:
            case True{}:
              Eq.bit.absurd2(&2, {T.doc.scan.q(False{}, False{}, True{}, qu(rw, hs, he, ps, sk, ab, bk, un, lf, buf),
                Chr{uu}) == T.MScan{qu(rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf)} : T.Mode}, hr)
            case False{}:
              Equal.cong(T.St, T.Mode, st => T.MScan{st},
                T.read.fast(qu(rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu}),
                qu(rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf), fast)

# a character written as itself is pushed, and back, uni and left stay
def qu.plain(
  +uu: U32,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  +e34: {U32.is_eq(uu, 34) == False{} : Bool},
  +e92: {U32.is_eq(uu, 92) == False{} : Bool},
  +ec: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool},
  ih: qu.Then(rw, hs, he, ps, sk, ab, Chr{uu} <> buf, rest, PP)
) -> PP(T.doc.read(String.append(L12.esc(Chr{uu}), rest), T.MScan{qu(rw, hs, he, ps, sk, ab, bk, un, lf, buf)})):
  +e10 = {M3.ctl.off(uu, 10, ec, {==}) : {U32.is_eq(uu, 10) == False{} : Bool}}
  +e13 = {M3.ctl.off(uu, 13, ec, {==}) : {U32.is_eq(uu, 13) == False{} : Bool}}
  %Equal.sym(String, L12.esc(Chr{uu}), SCon{Chr{uu}, SNil{}}, esc.pl2(uu, e34, e92, ec)) :
    PP(T.doc.read(String.append(_, rest), T.MScan{qu(rw, hs, he, ps, sk, ab, bk, un, lf, buf)}))
  pp.step(PP,
    T.doc.read(rest, T.doc.scan(qu(rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu})),
    T.doc.read(rest, T.MScan{qu(rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf)}),
    Equal.cong(T.Mode, T.Doc, md => T.doc.read(rest, md),
      T.doc.scan(qu(rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu}),
      T.MScan{qu(rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf)},
      qu.q(U32.is_eq(uu, 34), U32.is_eq(uu, 39), U32.is_eq(uu, 13), uu, rw, hs, he, ps, sk, ab, bk, un, lf, buf, e34,
        e13, Equal.trans(T.St, T.read.fast(qu(rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu}),
          T.read.once2(T.lex.kq.go(U32.is_eq(uu, 34), U32.is_eq(uu, 92), True{},
            Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)), qu(rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu},
            T.LAfter{}, T.LKeyQ{})),
          qu(rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf),
          qu.fast(uu, rw, hs, he, ps, sk, ab, bk, un, lf, buf),
          qu.go(U32.is_eq(uu, 34), U32.is_eq(uu, 92), Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)), uu, rw, hs, he,
            ps, sk, ab, bk, un, lf, buf, e34, e92, or.ff(U32.is_eq(uu, 10), U32.is_eq(uu, 13), e10, e13), ec)))),
    ih(bk, un, lf))

# a quotation mark: its escape reads back by computation, and leaves back at
# the key's state and uni and left as they were
def qu.q34(
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type
) -> qu.Goal(34, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP):
  ih => ih(T.LKeyQ{}, un, lf)

# and a backslash
def qu.q92(
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type
) -> qu.Goal(92, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP):
  ih => ih(T.LKeyQ{}, un, lf)

# CTL: qu.Goal with the escape's text as ss, for ctl.esc.all
def qu.GoalS(
  +uu: U32,
  ss: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  qu.Then(rw, hs, he, ps, sk, ab, Chr{uu} <> buf, rest, PP) ->
    PP(T.doc.read(String.append(ss, rest), T.MScan{qu(rw, hs, he, ps, sk, ab, bk, un, lf, buf)}))

# a control: each of the thirty-three escapes reads back by computation and
# leaves back at the key's state. The five with a letter (\b, \t, \n, \f,
# \r) leave uni and left as they were; a \u escape leaves both at 0
def qu.ctl(
  +uu: U32,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  h_c: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == True{} : Bool}
) -> qu.Goal(uu, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP):
  M3.ctl.esc.all(kk => ss => qu.GoalS(kk, ss, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP), uu, h_c,
    ih => ih(T.LKeyQ{}, 0, 0),
    ih => ih(T.LKeyQ{}, 0, 0),
    ih => ih(T.LKeyQ{}, 0, 0),
    ih => ih(T.LKeyQ{}, 0, 0),
    ih => ih(T.LKeyQ{}, 0, 0),
    ih => ih(T.LKeyQ{}, 0, 0),
    ih => ih(T.LKeyQ{}, 0, 0),
    ih => ih(T.LKeyQ{}, 0, 0),
    ih => ih(T.LKeyQ{}, un, lf),
    ih => ih(T.LKeyQ{}, un, lf),
    ih => ih(T.LKeyQ{}, un, lf),
    ih => ih(T.LKeyQ{}, 0, 0),
    ih => ih(T.LKeyQ{}, un, lf),
    ih => ih(T.LKeyQ{}, un, lf),
    ih => ih(T.LKeyQ{}, 0, 0),
    ih => ih(T.LKeyQ{}, 0, 0),
    ih => ih(T.LKeyQ{}, 0, 0),
    ih => ih(T.LKeyQ{}, 0, 0),
    ih => ih(T.LKeyQ{}, 0, 0),
    ih => ih(T.LKeyQ{}, 0, 0),
    ih => ih(T.LKeyQ{}, 0, 0),
    ih => ih(T.LKeyQ{}, 0, 0),
    ih => ih(T.LKeyQ{}, 0, 0),
    ih => ih(T.LKeyQ{}, 0, 0),
    ih => ih(T.LKeyQ{}, 0, 0),
    ih => ih(T.LKeyQ{}, 0, 0),
    ih => ih(T.LKeyQ{}, 0, 0),
    ih => ih(T.LKeyQ{}, 0, 0),
    ih => ih(T.LKeyQ{}, 0, 0),
    ih => ih(T.LKeyQ{}, 0, 0),
    ih => ih(T.LKeyQ{}, 0, 0),
    ih => ih(T.LKeyQ{}, 0, 0),
    ih => ih(T.LKeyQ{}, 0, 0))

# one code point k that the test found: its answer answers for the character
def qu.is(
  +uu: U32,
  +kk: U32,
  ee: {U32.is_eq(uu, kk) == True{} : Bool},
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  at: qu.Goal(kk, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP)
) -> qu.Goal(uu, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP):
  eu = Equal.cong(Char, U32, cc => Char.to_u32(cc), Chr{uu}, Chr{kk}, Eq.u32_eq(uu, kk, ee))
  %Equal.sym(U32, uu, kk, eu) : qu.Goal(_, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP)
  at

# every character: a quote, a backslash, a control, or one written as itself
def qu.split(
  +uu: U32,
  q34: Bool,
  b92: Bool,
  ctl: Bool,
  +e34: {U32.is_eq(uu, 34) == q34 : Bool},
  +e92: {U32.is_eq(uu, 92) == b92 : Bool},
  +ec: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == ctl : Bool},
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type
) -> qu.Goal(uu, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP):
  match q34:
    case True{}:
      qu.is(uu, 34, e34, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP,
        qu.q34(rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP))
    case False{}:
      match b92:
        case True{}:
          qu.is(uu, 92, e92, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP,
            qu.q92(rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP))
        case False{}:
          match ctl:
            case True{}:
              qu.ctl(uu, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP, ec)
            case False{}:
              ih => qu.plain(uu, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP, e34, e92, ec, ih)

# one character of a quoted key
def qu.one(
  +uu: U32,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type
) -> qu.Goal(uu, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP):
  qu.split(uu, U32.is_eq(uu, 34), U32.is_eq(uu, 92), Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), {==}, {==}, {==},
    rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP)

# every character of a name, as escs writes it, read in a quoted key: the
# rest is read with the characters pushed, from wherever the last escape
# left back, uni and left
def qu.escs(
  ss: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  ih: qu.Then(rw, hs, he, ps, sk, ab, M8.rev.onto(ss, buf), rest, PP)
) -> PP(T.doc.read(String.append(L12.escs(ss), rest), T.MScan{qu(rw, hs, he, ps, sk, ab, bk, un, lf, buf)})):
  match ss:
    case SNil{}:
      ih(bk, un, lf)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+uu}:
          pp.step(PP,
            T.doc.read(String.append(String.append(L12.esc(Chr{uu}), L12.escs(tt)), rest),
              T.MScan{qu(rw, hs, he, ps, sk, ab, bk, un, lf, buf)}),
            T.doc.read(String.append(L12.esc(Chr{uu}), String.append(L12.escs(tt), rest)),
              T.MScan{qu(rw, hs, he, ps, sk, ab, bk, un, lf, buf)}),
            Equal.cong(String, T.Doc, xs => T.doc.read(xs, T.MScan{qu(rw, hs, he, ps, sk, ab, bk, un, lf, buf)}),
              String.append(String.append(L12.esc(Chr{uu}), L12.escs(tt)), rest),
              String.append(L12.esc(Chr{uu}), String.append(L12.escs(tt), rest)),
              Eq.append_assoc(L12.esc(Chr{uu}), L12.escs(tt), rest)),
            qu.one(uu, rw, hs, he, ps, sk, ab, bk, un, lf, buf, String.append(L12.escs(tt), rest), PP)(
              b2 => u2 => l2 => qu.escs(tt, rw, hs, he, ps, sk, ab, b2, u2, l2, Chr{uu} <> buf, rest, PP, ih)))

# An inline table's key, from the state after `{` or ", " (LInlK), with the
# frame and every other field as parameters: a quoted key through qu, a bare
# key on the key's fast path, then " = " leaves the scanner waiting for the
# value with the key's name as the one part.

# the scanner waiting for an inline table's key
def cv.ks(
  rw: List<&2, T.Val>,
  hs: List<&2, String>,
  he: List<&2, String>,
  bk: T.Lex,
  qk: T.QKind,
  sk: List<&2, T.Ctx>,
  un: U32,
  lf: U32,
  ab: Bool
) -> T.St:
  T.St{"", rw, hs, he, [], [], T.LInlK{}, bk, qk, sk, T.HNone{}, un, lf, ab, False{}}

# the scanner inside a bare key, its characters so far reversed in buf
def cv.kbs(
  rw: List<&2, T.Val>,
  hs: List<&2, String>,
  he: List<&2, String>,
  bk: T.Lex,
  qk: T.QKind,
  sk: List<&2, T.Ctx>,
  un: U32,
  lf: U32,
  ab: Bool,
  buf: List<&2, Char>
) -> T.St:
  T.St{"", rw, hs, he, [], buf, T.LKey{}, bk, qk, sk, T.HNone{}, un, lf, ab, False{}}

# the rest of the walk once a key named kk and " = " are read: the scanner
# waits for the value, from whatever back, qkind, uni and left the key left
def cv.KThen(
  +kk: String,
  +yy: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  -PP: T.Doc -> Type
) -> Type:
  @b2: T.Lex -> @q2: T.QKind -> @u2: U32 -> @l2: U32 ->
    PP(T.doc.read(yy, T.MScan{cv.vp(rw, hs, he, [kk], b2, q2, sk, u2, l2, ab)}))

# a buffer a name was pushed onto reads as the name
def cv.bufk(+kk: String) -> {T.buf.str(M8.rev.onto(kk, [])) == kk : String}:
  Equal.trans(String, T.buf.str.go(M8.rev.onto(kk, []), ""), String.append(kk, ""), kk, ml.rev(kk, [], ""),
    Eq.append_nil(kk))

# the closing quote of a quoted key and " = ": the key's characters are its
# one part, and the scanner waits for the value
def cv.kq.close(
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +kk: String,
  +yy: String
) -> {T.doc.read(SCon{'"', SCon{' ', SCon{'=', SCon{' ', yy}}}}, T.MScan{qu(rw, hs, he, [], sk, ab, bk, un, lf,
  M8.rev.onto(kk, []))}) == T.doc.read(yy, T.MScan{cv.vp(rw, hs, he, [kk], bk, T.QBasic{}, sk, un, lf, ab)}) : T.Doc}:
  Equal.cong(String, T.Doc, nm => T.doc.read(yy, T.MScan{cv.vp(rw, hs, he, [nm], bk, T.QBasic{}, sk, un, lf, ab)}),
    T.buf.str(M8.rev.onto(kk, [])), kk, cv.bufk(kk))

# a quoted key, as key.basic writes it, then " = "
def cv.kq(
  +kk: String,
  +yy: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  -PP: T.Doc -> Type,
  ih: cv.KThen(kk, yy, rw, hs, he, sk, ab, PP)
) -> PP(T.doc.read(String.append(T.key.basic(kk), SCon{' ', SCon{'=', SCon{' ', yy}}}), T.MScan{cv.ks(rw, hs, he,
  bk, qk, sk, un, lf, ab)})):
  +zz = {SCon{' ', SCon{'=', SCon{' ', yy}}} : String}
  %Equal.sym(String, T.key.basic(kk), "\"" ++ L12.escs(kk) ++ "\"", L12.basic_escs(kk)) :
    PP(T.doc.read(String.append(_, zz), T.MScan{cv.ks(rw, hs, he, bk, qk, sk, un, lf, ab)}))
  %Equal.sym(String, String.append(String.append(L12.escs(kk), "\""), zz), String.append(L12.escs(kk), SCon{'"',
    zz}), Eq.append_assoc(L12.escs(kk), "\"", zz)) :
    PP(T.doc.read(SCon{'"', _}, T.MScan{cv.ks(rw, hs, he, bk, qk, sk, un, lf, ab)}))
  qu.escs(kk, rw, hs, he, [], sk, ab, bk, un, lf, [], SCon{'"', zz}, PP,
    +b2 => +u2 => +l2 => pp.step(PP, T.doc.read(SCon{'"', zz}, T.MScan{qu(rw, hs, he, [], sk, ab, b2, u2, l2,
      M8.rev.onto(kk, []))}), T.doc.read(yy, T.MScan{cv.vp(rw, hs, he, [kk], b2, T.QBasic{}, sk, u2, l2, ab)}),
      cv.kq.close(rw, hs, he, sk, ab, b2, u2, l2, kk, yy), ih(b2, T.QBasic{}, u2, l2)))

# a code point that is a blank or a newline is no bare-key character
def cv.nsp(
  bb: Bool,
  +xx: U32,
  +k1: U32,
  +k2: U32,
  ee: {Bool.or(U32.is_eq(xx, k1), U32.is_eq(xx, k2)) == bb : Bool},
  yes: {T.bare.at(Chr{xx}) == True{} : Bool},
  n1: {T.bare.at(Chr{k1}) == False{} : Bool},
  n2: {T.bare.at(Chr{k2}) == False{} : Bool}
) -> {bb == False{} : Bool}:
  match bb:
    case True{}:
      Eq.bit.gone(&2, {True{} == False{} : Bool}, or2.no(xx, k1, k2, U32.is_eq(xx, k1), U32.is_eq(xx, k2), {==}, {==},
        ee, ch => T.bare.at(ch), yes, n1, n2))
    case False{}:
      {==}

# a character another bare-key test refuses is not a bare-key character
def cv.nch(
  bb: Bool,
  +cc: Char,
  +kk: Char,
  ee: {Char.is_eq(cc, kk) == bb : Bool},
  yes: {T.bare.at(cc) == True{} : Bool},
  no: {T.bare.at(kk) == False{} : Bool}
) -> {bb == False{} : Bool}:
  match bb:
    case True{}:
      Eq.bit.gone(&2, {True{} == False{} : Bool}, Eq.refute_char(cc, kk, ch => T.bare.at(ch), ee, yes, no))
    case False{}:
      {==}

# the key dispatch pushes a bare-key character once it is no quote
def cv.kb.b(
  ok: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +cc: Char,
  fb: {ok == True{} : Bool}
) -> {T.read.once2(T.lex.key.bare(ok, cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, []), cc))
  == cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, [cc]) : T.St}:
  match ok:
    case True{}:
      {==}
    case False{}:
      Eq.bit.absurd(&2, {T.read.once2(T.lex.key.bare(False{}, cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, []), cc))
        == cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, [cc]) : T.St}, fb)

# and once it is no apostrophe
def cv.kb.l(
  lit: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +cc: Char,
  fl: {lit == False{} : Bool},
  fb: {T.bare.at(cc) == True{} : Bool}
) -> {T.read.once2(T.lex.key.lit(lit, cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, []), cc))
  == cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, [cc]) : T.St}:
  match lit:
    case True{}:
      Eq.bit.absurd2(&2, {T.read.once2(T.lex.key.lit(True{}, cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, []), cc))
        == cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, [cc]) : T.St}, fl)
    case False{}:
      cv.kb.b(T.bare.at(cc), rw, hs, he, bk, qk, sk, un, lf, ab, cc, fb)

# and once it is no quotation mark
def cv.kb.q(
  qq: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +cc: Char,
  fq: {qq == False{} : Bool},
  fl: {Char.is_eq(cc, '\'') == False{} : Bool},
  fb: {T.bare.at(cc) == True{} : Bool}
) -> {T.read.once2(T.lex.key.q(qq, cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, []), cc))
  == cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, [cc]) : T.St}:
  match qq:
    case True{}:
      Eq.bit.absurd2(&2, {T.read.once2(T.lex.key.q(True{}, cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, []), cc))
        == cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, [cc]) : T.St}, fq)
    case False{}:
      cv.kb.l(Char.is_eq(cc, '\''), rw, hs, he, bk, qk, sk, un, lf, ab, cc, fl, fb)

# LInlK passes a character that is no blank, `#` or newline to the key
def cv.kb.ik(
  sp: Bool,
  hash: Bool,
  nl: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +cc: Char,
  fsp: {sp == False{} : Bool},
  fhs: {hash == False{} : Bool},
  fnl: {nl == False{} : Bool},
  fq: {Char.is_eq(cc, '"') == False{} : Bool},
  fl: {Char.is_eq(cc, '\'') == False{} : Bool},
  fb: {T.bare.at(cc) == True{} : Bool}
) -> {T.read.once2(T.lex.inlk.go(sp, hash, nl, cv.ks(rw, hs, he, bk, qk, sk, un, lf, ab), cc))
  == cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, [cc]) : T.St}:
  match sp:
    case True{}:
      Eq.bit.absurd2(&2, {T.read.once2(T.lex.inlk.go(True{}, hash, nl, cv.ks(rw, hs, he, bk, qk, sk, un, lf, ab), cc))
        == cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, [cc]) : T.St}, fsp)
    case False{}:
      match hash:
        case True{}:
          Eq.bit.absurd2(&2, {T.read.once2(T.lex.inlk.go(False{}, True{}, nl, cv.ks(rw, hs, he, bk, qk, sk, un, lf,
            ab), cc)) == cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, [cc]) : T.St}, fhs)
        case False{}:
          match nl:
            case True{}:
              Eq.bit.absurd2(&2, {T.read.once2(T.lex.inlk.go(False{}, False{}, True{}, cv.ks(rw, hs, he, bk, qk, sk,
                un, lf, ab), cc)) == cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, [cc]) : T.St}, fnl)
            case False{}:
              cv.kb.q(Char.is_eq(cc, '"'), rw, hs, he, bk, qk, sk, un, lf, ab, cc, fq, fl, fb)

# the fast step of LInlK on such a character
def cv.kb.ws(
  sp: Bool,
  nl: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +cc: Char,
  hsp: {sp == False{} : Bool},
  hnl: {nl == False{} : Bool},
  fsp: {T.ch.sp(cc) == False{} : Bool},
  fhs: {Char.is_eq(cc, '#') == False{} : Bool},
  fnl: {T.ch.nl(cc) == False{} : Bool},
  fq: {Char.is_eq(cc, '"') == False{} : Bool},
  fl: {Char.is_eq(cc, '\'') == False{} : Bool},
  fb: {T.bare.at(cc) == True{} : Bool}
) -> {T.read.fast.ws(sp, nl, False{}, "", rw, hs, he, [], [], T.LInlK{}, bk, qk, sk, un, lf, ab, cc)
  == cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, [cc]) : T.St}:
  match sp:
    case True{}:
      Eq.bit.absurd2(&2, {T.read.fast.ws(True{}, nl, False{}, "", rw, hs, he, [], [], T.LInlK{}, bk, qk, sk, un, lf, ab,
        cc) == cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, [cc]) : T.St}, hsp)
    case False{}:
      match nl:
        case True{}:
          Eq.bit.absurd2(&2, {T.read.fast.ws(False{}, True{}, False{}, "", rw, hs, he, [], [], T.LInlK{}, bk, qk, sk,
            un, lf, ab, cc) == cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, [cc]) : T.St}, hnl)
        case False{}:
          cv.kb.ik(T.ch.sp(cc), Char.is_eq(cc, '#'), T.ch.nl(cc), rw, hs, he, bk, qk, sk, un, lf, ab, cc, fsp, fhs, fnl,
            fq, fl, fb)

# the first character of a bare key starts the key
def cv.kb.first(
  +xx: U32,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +fb: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.doc.scan(cv.ks(rw, hs, he, bk, qk, sk, un, lf, ab), Chr{xx}) == T.MScan{cv.kbs(rw, hs, he, bk, qk, sk, un, lf,
  ab, [Chr{xx}])} : T.Mode}:
  +fsp = {cv.nsp(T.ch.sp(Chr{xx}), xx, 32, 9, {==}, fb, {==}, {==}) : {T.ch.sp(Chr{xx}) == False{} : Bool}}
  +fnl = {cv.nsp(T.ch.nl(Chr{xx}), xx, 10, 13, {==}, fb, {==}, {==}) : {T.ch.nl(Chr{xx}) == False{} : Bool}}
  Equal.trans(T.Mode,
    T.doc.scan(cv.ks(rw, hs, he, bk, qk, sk, un, lf, ab), Chr{xx}),
    T.MScan{T.read.fast(cv.ks(rw, hs, he, bk, qk, sk, un, lf, ab), Chr{xx})},
    T.MScan{cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, [Chr{xx}])},
    M13.scan.other(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), U32.is_eq(xx, 13),
      cv.ks(rw, hs, he, bk, qk, sk, un, lf, ab), Chr{xx}, {==}, {==}, {==}, ch => T.bare.at(ch), fb, {==}, {==}, {==}),
    Equal.cong(T.St, T.Mode, st => T.MScan{st},
      T.read.fast(cv.ks(rw, hs, he, bk, qk, sk, un, lf, ab), Chr{xx}),
      cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, [Chr{xx}]),
      cv.kb.ws(T.ch.sp(Chr{xx}), T.ch.nl(Chr{xx}), rw, hs, he, bk, qk, sk, un, lf, ab, Chr{xx}, fsp, fnl, fsp,
        cv.nch(Char.is_eq(Chr{xx}, '#'), Chr{xx}, '#', {==}, fb, {==}), fnl,
        cv.nch(Char.is_eq(Chr{xx}, '"'), Chr{xx}, '"', {==}, fb, {==}),
        cv.nch(Char.is_eq(Chr{xx}, '\''), Chr{xx}, '\'', {==}, fb, {==}), fb)))

# a later bare-key character stays on the key's fast path
def cv.kb.fast(
  ok: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +buf: List<&2, Char>,
  +cc: Char,
  fb: {ok == True{} : Bool}
) -> {T.read.fast.key(ok, "", rw, hs, he, [], buf, bk, qk, sk, un, lf, ab, cc)
  == cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, cc <> buf) : T.St}:
  match ok:
    case True{}:
      {==}
    case False{}:
      Eq.bit.absurd(&2, {T.read.fast.key(False{}, "", rw, hs, he, [], buf, bk, qk, sk, un, lf, ab, cc)
        == cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, cc <> buf) : T.St}, fb)

# one later character of the key, from the scan mode
def cv.kb.step(
  +xx: U32,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +buf: List<&2, Char>,
  +fb: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.doc.scan(cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, buf), Chr{xx}) == T.MScan{cv.kbs(rw, hs, he, bk, qk, sk, un,
  lf, ab, Chr{xx} <> buf)} : T.Mode}:
  Equal.trans(T.Mode,
    T.doc.scan(cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, buf), Chr{xx}),
    T.MScan{T.read.fast(cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, buf), Chr{xx})},
    T.MScan{cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, Chr{xx} <> buf)},
    M13.scan.other(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), U32.is_eq(xx, 13),
      cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, buf), Chr{xx}, {==}, {==}, {==}, ch => T.bare.at(ch), fb, {==}, {==},
      {==}),
    Equal.cong(T.St, T.Mode, st => T.MScan{st},
      T.read.fast(cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, buf), Chr{xx}),
      cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, Chr{xx} <> buf),
      cv.kb.fast(T.bare.at(Chr{xx}), rw, hs, he, bk, qk, sk, un, lf, ab, buf, Chr{xx}, fb)))

# a text of bare-key characters is pushed onto the key's buffer
def cv.kb.body(
  ks: String,
  +rr: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +buf: List<&2, Char>,
  +ee: {T.bare.all(String.to_list(ks)) == True{} : Bool}
) -> {T.doc.read(String.append(ks, rr), T.MScan{cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, buf)})
  == T.doc.read(rr, T.MScan{cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, M8.rev.onto(ks, buf))}) : T.Doc}:
  match ks:
    case SNil{}:
      {==}
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          Equal.trans(T.Doc,
            T.doc.read(String.append(tt, rr), T.doc.scan(cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, buf), Chr{xx})),
            T.doc.read(String.append(tt, rr), T.MScan{cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, Chr{xx} <> buf)}),
            T.doc.read(rr, T.MScan{cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, M8.rev.onto(tt, Chr{xx} <> buf))}),
            Equal.cong(T.Mode, T.Doc, md => T.doc.read(String.append(tt, rr), md),
              T.doc.scan(cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, buf), Chr{xx}),
              T.MScan{cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, Chr{xx} <> buf)},
              cv.kb.step(xx, rw, hs, he, bk, qk, sk, un, lf, ab, buf, ball.head(T.bare.at(Chr{xx}),
                String.to_list(tt), ee))),
            cv.kb.body(tt, rr, rw, hs, he, bk, qk, sk, un, lf, ab, Chr{xx} <> buf,
              ball.tail(T.bare.at(Chr{xx}), String.to_list(tt), ee)))

# a space ends a nonempty bare key, and " = " leaves the scanner waiting for
# the value, the key its one part
def cv.kb.eq(
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +bb: List<&2, Char>,
  full: {List.is_empty(&2, Char, bb) == False{} : Bool},
  +yy: String
) -> {T.doc.read(SCon{' ', SCon{'=', SCon{' ', yy}}}, T.MScan{cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, bb)})
  == T.doc.read(yy, T.MScan{cv.vp(rw, hs, he, [T.buf.str(bb)], bk, qk, sk, un, lf, ab)}) : T.Doc}:
  Equal.trans(T.Doc,
    T.doc.read(SCon{'=', SCon{' ', yy}}, T.MScan{T.read.once2(T.lex.key.end.go(List.is_empty(&2, Char, bb),
      cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, bb), T.LAfter{}))}),
    T.doc.read(SCon{'=', SCon{' ', yy}}, T.MScan{T.read.once2(T.lex.key.end.go(False{},
      cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, bb), T.LAfter{}))}),
    T.doc.read(yy, T.MScan{cv.vp(rw, hs, he, [T.buf.str(bb)], bk, qk, sk, un, lf, ab)}),
    Equal.cong(Bool, T.Doc, bt => T.doc.read(SCon{'=', SCon{' ', yy}}, T.MScan{T.read.once2(T.lex.key.end.go(bt,
      cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, bb), T.LAfter{}))}), List.is_empty(&2, Char, bb), False{}, full),
    {==})

# a bare key then " = "
def cv.kb(
  +xx: U32,
  +tt: String,
  +yy: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  -PP: T.Doc -> Type,
  +ee: {T.bare.all.step(T.bare.at(Chr{xx}), _u => T.bare.all(String.to_list(tt))) == True{} : Bool},
  ih: cv.KThen(SCon{Chr{xx}, tt}, yy, rw, hs, he, sk, ab, PP)
) -> PP(T.doc.read(String.append(SCon{Chr{xx}, tt}, SCon{' ', SCon{'=', SCon{' ', yy}}}), T.MScan{cv.ks(rw, hs, he, bk,
  qk, sk, un, lf, ab)})):
  +zz = {SCon{' ', SCon{'=', SCon{' ', yy}}} : String}
  +b1 = {M8.rev.onto(tt, [Chr{xx}]) : List<&2, Char>}
  pp.step(PP, T.doc.read(String.append(tt, zz), T.doc.scan(cv.ks(rw, hs, he, bk, qk, sk, un, lf, ab), Chr{xx})),
    T.doc.read(yy, T.MScan{cv.vp(rw, hs, he, [SCon{Chr{xx}, tt}], bk, qk, sk, un, lf, ab)}),
    Equal.trans(T.Doc,
      T.doc.read(String.append(tt, zz), T.doc.scan(cv.ks(rw, hs, he, bk, qk, sk, un, lf, ab), Chr{xx})),
      T.doc.read(String.append(tt, zz), T.MScan{cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, [Chr{xx}])}),
      T.doc.read(yy, T.MScan{cv.vp(rw, hs, he, [SCon{Chr{xx}, tt}], bk, qk, sk, un, lf, ab)}),
      Equal.cong(T.Mode, T.Doc, md => T.doc.read(String.append(tt, zz), md),
        T.doc.scan(cv.ks(rw, hs, he, bk, qk, sk, un, lf, ab), Chr{xx}),
        T.MScan{cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, [Chr{xx}])},
        cv.kb.first(xx, rw, hs, he, bk, qk, sk, un, lf, ab, ball.head(T.bare.at(Chr{xx}), String.to_list(tt), ee))),
      Equal.trans(T.Doc,
        T.doc.read(String.append(tt, zz), T.MScan{cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, [Chr{xx}])}),
        T.doc.read(zz, T.MScan{cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, b1)}),
        T.doc.read(yy, T.MScan{cv.vp(rw, hs, he, [SCon{Chr{xx}, tt}], bk, qk, sk, un, lf, ab)}),
        cv.kb.body(tt, zz, rw, hs, he, bk, qk, sk, un, lf, ab, [Chr{xx}], ball.tail(T.bare.at(Chr{xx}),
          String.to_list(tt), ee)),
        Equal.trans(T.Doc,
          T.doc.read(zz, T.MScan{cv.kbs(rw, hs, he, bk, qk, sk, un, lf, ab, b1)}),
          T.doc.read(yy, T.MScan{cv.vp(rw, hs, he, [T.buf.str(b1)], bk, qk, sk, un, lf, ab)}),
          T.doc.read(yy, T.MScan{cv.vp(rw, hs, he, [SCon{Chr{xx}, tt}], bk, qk, sk, un, lf, ab)}),
          cv.kb.eq(rw, hs, he, bk, qk, sk, un, lf, ab, b1, rev.full(tt, Chr{xx}, []), yy),
          Equal.cong(String, T.Doc, nm => T.doc.read(yy, T.MScan{cv.vp(rw, hs, he, [nm], bk, qk, sk, un, lf, ab)}),
            T.buf.str(b1), SCon{Chr{xx}, tt},
            Equal.trans(String, T.buf.str.go(b1, ""), SCon{Chr{xx}, String.append(tt, "")}, SCon{Chr{xx}, tt},
              ml.rev(tt, [Chr{xx}], ""),
              Equal.cong(String, String, ss => SCon{Chr{xx}, ss}, String.append(tt, ""), tt, Eq.append_nil(tt))))))),
    ih(bk, qk, un, lf))

# a key as key writes it, bare or quoted, then " = "
def cv.key.go(
  bb: Bool,
  +kk: String,
  eb: {T.bare(kk) == bb : Bool},
  +yy: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  -PP: T.Doc -> Type,
  ih: cv.KThen(kk, yy, rw, hs, he, sk, ab, PP)
) -> PP(T.doc.read(String.append(T.key.go(bb, kk), SCon{' ', SCon{'=', SCon{' ', yy}}}), T.MScan{cv.ks(rw, hs, he, bk,
  qk, sk, un, lf, ab)})):
  match bb:
    case False{}:
      cv.kq(kk, yy, rw, hs, he, bk, qk, sk, un, lf, ab, PP, ih)
    case True{}:
      match kk:
        case SNil{}:
          Eq.bit.absurd(&1, PP(T.doc.read(String.append(SNil{}, SCon{' ', SCon{'=', SCon{' ', yy}}}),
            T.MScan{cv.ks(rw, hs, he, bk, qk, sk, un, lf, ab)})), eb)
        case SCon{hh, +tt}:
          match hh:
            case Chr{+xx}:
              cv.kb(xx, tt, yy, rw, hs, he, bk, qk, sk, un, lf, ab, PP, eb, ih)

# a key as key writes it, then " = "
def cv.key(
  +kk: String,
  +yy: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  -PP: T.Doc -> Type,
  ih: cv.KThen(kk, yy, rw, hs, he, sk, ab, PP)
) -> PP(T.doc.read(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', yy}}}), T.MScan{cv.ks(rw, hs, he, bk, qk,
  sk, un, lf, ab)})):
  cv.key.go(T.bare(kk), kk, {==}, yy, rw, hs, he, bk, qk, sk, un, lf, ab, PP, ih)

# LInl, right after `{`, reads the first key as LInlK does after ", ": both
# pass a character that is no blank, newline, `#` or `}` to the key.

# a character LInl keeps for itself or LInlK refuses
def cv.kbad(+cc: Char) -> Bool:
  Bool.or(T.ch.sp(cc), Bool.or(T.ch.nl(cc), Bool.or(Char.is_eq(cc, '#'), Char.is_eq(cc, '}'))))

# the first character of a text is no such character
def cv.xkbad(xs: String) -> Bool:
  match xs:
    case SNil{}:
      True{}
    case SCon{+cc, _tt}:
      cv.kbad(cc)

# the two dispatches agree on such a character
def cv.l2k.go(
  sp: Bool,
  hash: Bool,
  end: Bool,
  nl: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +cc: Char,
  fsp: {sp == False{} : Bool},
  fhs: {hash == False{} : Bool},
  fen: {end == False{} : Bool},
  fnl: {nl == False{} : Bool}
) -> {T.read.once2(T.lex.inl.go(sp, hash, end, nl, T.St{"", rw, hs, he, [], [], T.LInl{}, bk, qk, sk, T.HNone{}, un,
  lf, ab, False{}}, cc)) == T.read.once2(T.lex.inlk.go(sp, hash, nl, cv.ks(rw, hs, he, bk, qk, sk, un, lf, ab), cc))
  : T.St}:
  match sp:
    case True{}:
      Eq.bit.absurd2(&2, {T.read.once2(T.lex.inl.go(True{}, hash, end, nl, T.St{"", rw, hs, he, [], [], T.LInl{}, bk,
        qk, sk, T.HNone{}, un, lf, ab, False{}}, cc)) == T.read.once2(T.lex.inlk.go(True{}, hash, nl, cv.ks(rw, hs, he,
        bk, qk, sk, un, lf, ab), cc)) : T.St}, fsp)
    case False{}:
      match hash:
        case True{}:
          Eq.bit.absurd2(&2, {T.read.once2(T.lex.inl.go(False{}, True{}, end, nl, T.St{"", rw, hs, he, [], [],
            T.LInl{}, bk, qk, sk, T.HNone{}, un, lf, ab, False{}}, cc)) == T.read.once2(T.lex.inlk.go(False{}, True{},
            nl, cv.ks(rw, hs, he, bk, qk, sk, un, lf, ab), cc)) : T.St}, fhs)
        case False{}:
          match end:
            case True{}:
              Eq.bit.absurd2(&2, {T.read.once2(T.lex.inl.go(False{}, False{}, True{}, nl, T.St{"", rw, hs, he, [], [],
                T.LInl{}, bk, qk, sk, T.HNone{}, un, lf, ab, False{}}, cc)) == T.read.once2(T.lex.inlk.go(False{},
                False{}, nl, cv.ks(rw, hs, he, bk, qk, sk, un, lf, ab), cc)) : T.St}, fen)
            case False{}:
              match nl:
                case True{}:
                  Eq.bit.absurd2(&2, {T.read.once2(T.lex.inl.go(False{}, False{}, False{}, True{}, T.St{"", rw, hs,
                    he, [], [], T.LInl{}, bk, qk, sk, T.HNone{}, un, lf, ab, False{}}, cc)) == T.read.once2(
                    T.lex.inlk.go(False{}, False{}, True{}, cv.ks(rw, hs, he, bk, qk, sk, un, lf, ab), cc)) : T.St},
                    fnl)
                case False{}:
                  {==}

# and so do the two fast steps
def cv.l2k.ws(
  sp: Bool,
  nl: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +cc: Char,
  hsp: {sp == False{} : Bool},
  hnl: {nl == False{} : Bool},
  fsp: {T.ch.sp(cc) == False{} : Bool},
  fhs: {Char.is_eq(cc, '#') == False{} : Bool},
  fen: {Char.is_eq(cc, '}') == False{} : Bool},
  fnl: {T.ch.nl(cc) == False{} : Bool}
) -> {T.read.fast.ws(sp, nl, False{}, "", rw, hs, he, [], [], T.LInl{}, bk, qk, sk, un, lf, ab, cc)
  == T.read.fast.ws(sp, nl, False{}, "", rw, hs, he, [], [], T.LInlK{}, bk, qk, sk, un, lf, ab, cc) : T.St}:
  match sp:
    case True{}:
      Eq.bit.absurd2(&2, {T.read.fast.ws(True{}, nl, False{}, "", rw, hs, he, [], [], T.LInl{}, bk, qk, sk, un, lf, ab,
        cc) == T.read.fast.ws(True{}, nl, False{}, "", rw, hs, he, [], [], T.LInlK{}, bk, qk, sk, un, lf, ab, cc)
        : T.St}, hsp)
    case False{}:
      match nl:
        case True{}:
          Eq.bit.absurd2(&2, {T.read.fast.ws(False{}, True{}, False{}, "", rw, hs, he, [], [], T.LInl{}, bk, qk, sk,
            un, lf, ab, cc) == T.read.fast.ws(False{}, True{}, False{}, "", rw, hs, he, [], [], T.LInlK{}, bk, qk, sk,
            un, lf, ab, cc) : T.St}, hnl)
        case False{}:
          cv.l2k.go(T.ch.sp(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, '}'), T.ch.nl(cc), rw, hs, he, bk, qk, sk, un,
            lf, ab, cc, fsp, fhs, fen, fnl)

# a text whose first character both pass on reads from LInl as from LInlK
def cv.l2k(
  xs: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +hb: {cv.xkbad(xs) == False{} : Bool}
) -> {T.doc.read(xs, T.MScan{T.St{"", rw, hs, he, [], [], T.LInl{}, bk, qk, sk, T.HNone{}, un, lf, ab, False{}}})
  == T.doc.read(xs, T.MScan{cv.ks(rw, hs, he, bk, qk, sk, un, lf, ab)}) : T.Doc}:
  match xs:
    case SNil{}:
      Eq.bit.absurd2(&2, {T.doc.read(SNil{}, T.MScan{T.St{"", rw, hs, he, [], [], T.LInl{}, bk, qk, sk, T.HNone{}, un,
        lf, ab, False{}}}) == T.doc.read(SNil{}, T.MScan{cv.ks(rw, hs, he, bk, qk, sk, un, lf, ab)}) : T.Doc}, hb)
    case SCon{+cc, +tt}:
      +r1 = {Eq.or.right_false(T.ch.sp(cc), Bool.or(T.ch.nl(cc), Bool.or(Char.is_eq(cc, '#'), Char.is_eq(cc, '}'))),
        hb) : {Bool.or(T.ch.nl(cc), Bool.or(Char.is_eq(cc, '#'), Char.is_eq(cc, '}'))) == False{} : Bool}}
      +r2 = {Eq.or.right_false(T.ch.nl(cc), Bool.or(Char.is_eq(cc, '#'), Char.is_eq(cc, '}')), r1)
        : {Bool.or(Char.is_eq(cc, '#'), Char.is_eq(cc, '}')) == False{} : Bool}}
      +fsp = {Eq.or.left_false(T.ch.sp(cc), Bool.or(T.ch.nl(cc), Bool.or(Char.is_eq(cc, '#'), Char.is_eq(cc, '}'))),
        hb) : {T.ch.sp(cc) == False{} : Bool}}
      +fnl = {Eq.or.left_false(T.ch.nl(cc), Bool.or(Char.is_eq(cc, '#'), Char.is_eq(cc, '}')), r1)
        : {T.ch.nl(cc) == False{} : Bool}}
      Equal.cong(T.Mode, T.Doc, md => T.doc.read(tt, md),
        T.doc.scan(T.St{"", rw, hs, he, [], [], T.LInl{}, bk, qk, sk, T.HNone{}, un, lf, ab, False{}}, cc),
        T.doc.scan(cv.ks(rw, hs, he, bk, qk, sk, un, lf, ab), cc),
        scan.fast(Char.is_eq(cc, '"'), Char.is_eq(cc, '\''), U32.is_eq(Char.to_u32(cc), 13),
          T.St{"", rw, hs, he, [], [], T.LInl{}, bk, qk, sk, T.HNone{}, un, lf, ab, False{}},
          cv.ks(rw, hs, he, bk, qk, sk, un, lf, ab), cc,
          cv.l2k.ws(T.ch.sp(cc), T.ch.nl(cc), rw, hs, he, bk, qk, sk, un, lf, ab, cc, fsp, fnl, fsp,
            Eq.or.left_false(Char.is_eq(cc, '#'), Char.is_eq(cc, '}'), r2),
            Eq.or.right_false(Char.is_eq(cc, '#'), Char.is_eq(cc, '}'), r2), fnl)))

# a bare-key character is no such character
def cv.kbad.of(
  sp: Bool,
  nl: Bool,
  hash: Bool,
  end: Bool,
  hsp: {sp == False{} : Bool},
  hnl: {nl == False{} : Bool},
  hhs: {hash == False{} : Bool},
  hen: {end == False{} : Bool}
) -> {Bool.or(sp, Bool.or(nl, Bool.or(hash, end))) == False{} : Bool}:
  match sp:
    case True{}:
      hsp
    case False{}:
      match nl:
        case True{}:
          hnl
        case False{}:
          match hash:
            case True{}:
              hhs
            case False{}:
              hen

# a key as key writes it starts with such a character
def cv.kx.go(
  bb: Bool,
  kk: String,
  eb: {T.bare(kk) == bb : Bool},
  +zz: String
) -> {cv.xkbad(String.append(T.key.go(bb, kk), zz)) == False{} : Bool}:
  match bb:
    case False{}:
      {==}
    case True{}:
      match kk:
        case SNil{}:
          Eq.bit.absurd(&2, {cv.xkbad(String.append(SNil{}, zz)) == False{} : Bool}, eb)
        case SCon{hh, +tt}:
          match hh:
            case Chr{+xx}:
              +fb = {ball.head(T.bare.at(Chr{xx}), String.to_list(tt), eb) : {T.bare.at(Chr{xx}) == True{} : Bool}}
              cv.kbad.of(T.ch.sp(Chr{xx}), T.ch.nl(Chr{xx}), Char.is_eq(Chr{xx}, '#'), Char.is_eq(Chr{xx}, '}'),
                cv.nsp(T.ch.sp(Chr{xx}), xx, 32, 9, {==}, fb, {==}, {==}),
                cv.nsp(T.ch.nl(Chr{xx}), xx, 10, 13, {==}, fb, {==}, {==}),
                cv.nch(Char.is_eq(Chr{xx}, '#'), Chr{xx}, '#', {==}, fb, {==}),
                cv.nch(Char.is_eq(Chr{xx}, '}'), Chr{xx}, '}', {==}, fb, {==}))

# the text of a pair render writes starts with such a character
def cv.kx(+kk: String, +zz: String) -> {cv.xkbad(String.append(T.key(kk), zz)) == False{} : Bool}:
  cv.kx.go(T.bare(kk), kk, {==}, zz)

# The pairs of an inline table: the text render writes for one, what
# well-formedness says of it, and the names read so far.

# a pair of a scalar, then the separator, the rest and the closer
def cv.pat(
  +kk: String,
  +aa: String,
  +vs: List<&2, T.Val>,
  +close: Char,
  +xx: String
) -> {String.append(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', String.append(aa, cv.S(vs))}}}), SCon{close,
  xx}) == String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', String.append(aa, cv.tl(vs, close, xx))}}}) : String}:
  Equal.trans(String,
    String.append(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', String.append(aa, cv.S(vs))}}}), SCon{close,
      xx}),
    String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', String.append(String.append(aa, cv.S(vs)), SCon{close,
      xx})}}}),
    String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', String.append(aa, cv.tl(vs, close, xx))}}}),
    Eq.append_assoc(T.key(kk), SCon{' ', SCon{'=', SCon{' ', String.append(aa, cv.S(vs))}}}, SCon{close, xx}),
    Equal.cong(String, String, zz => String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', zz}}}),
      String.append(String.append(aa, cv.S(vs)), SCon{close, xx}), String.append(aa, cv.tl(vs, close, xx)),
      cv.at(aa, vs, close, xx)))

# a pair of an array or an inline table, then the separator, the rest and
# the closer
def cv.pcl(
  +kk: String,
  +c1: Char,
  +rr: String,
  +c2: Char,
  +vs: List<&2, T.Val>,
  +close: Char,
  +xx: String
) -> {String.append(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', SCon{c1, String.append(rr, SCon{c2,
  cv.S(vs)})}}}}), SCon{close, xx}) == String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', SCon{c1, String.append(rr,
  SCon{c2, cv.tl(vs, close, xx)})}}}}) : String}:
  Equal.trans(String,
    String.append(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', SCon{c1, String.append(rr, SCon{c2,
      cv.S(vs)})}}}}), SCon{close, xx}),
    String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', SCon{c1, String.append(String.append(rr, SCon{c2,
      cv.S(vs)}), SCon{close, xx})}}}}),
    String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', SCon{c1, String.append(rr, SCon{c2, cv.tl(vs, close,
      xx)})}}}}),
    Eq.append_assoc(T.key(kk), SCon{' ', SCon{'=', SCon{' ', SCon{c1, String.append(rr, SCon{c2, cv.S(vs)})}}}},
      SCon{close, xx}),
    Equal.cong(String, String, zz => String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', SCon{c1, zz}}}}),
      String.append(String.append(rr, SCon{c2, cv.S(vs)}), SCon{close, xx}),
      String.append(rr, SCon{c2, cv.tl(vs, close, xx)}), cv.cl(rr, c2, vs, close, xx)))

# a pair and the rest of the pairs, then the closer: the key, " = ", the
# value's text, then what follows it
def cv.ptx(
  +kk: String,
  vv: T.Val,
  +tt: List<&2, T.Val>,
  +close: Char,
  +xx: String,
  hw: {D1.cv.wf(vv) == True{} : Bool}
) -> {String.append(T.render.go(T.VPair{kk, vv} <> tt, ", ", False{}), SCon{close, xx}) == String.append(T.key(kk),
  SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(vv, cv.tl(tt, close, xx))}}}) : String}:
  match vv:
    case T.VArr{+items}:
      cv.pcl(kk, '[', T.render.go(items, ", ", False{}), ']', tt, close, xx)
    case T.VInl{+rows}:
      cv.pcl(kk, '{', T.render.go(rows, ", ", False{}), '}', tt, close, xx)
    case T.VStr{+aa}:
      cv.pat(kk, T.render.atom(T.VStr{aa}), tt, close, xx)
    case T.VSpan{+aa, +bb}:
      cv.pat(kk, T.render.atom(T.VSpan{aa, bb}), tt, close, xx)
    case T.VInt{+aa, +bb}:
      cv.pat(kk, T.render.atom(T.VInt{aa, bb}), tt, close, xx)
    case T.VFlo{+aa, +bb}:
      cv.pat(kk, T.render.atom(T.VFlo{aa, bb}), tt, close, xx)
    case T.VBool{+aa}:
      cv.pat(kk, T.render.atom(T.VBool{aa}), tt, close, xx)
    case T.VWhen{+aa}:
      cv.pat(kk, T.render.atom(T.VWhen{aa}), tt, close, xx)
    case T.VHead{aa, bb}:
      Eq.bit.absurd(&2, {String.append(T.render.go(T.VPair{kk, T.VHead{aa, bb}} <> tt, ", ", False{}), SCon{close, xx})
        == String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VHead{aa, bb}, cv.tl(tt, close,
        xx))}}}) : String}, hw)
    case T.VAot{aa, bb}:
      Eq.bit.absurd(&2, {String.append(T.render.go(T.VPair{kk, T.VAot{aa, bb}} <> tt, ", ", False{}), SCon{close, xx})
        == String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VAot{aa, bb}, cv.tl(tt, close,
        xx))}}}) : String}, hw)
    case T.VAots{aa, bb}:
      Eq.bit.absurd(&2, {String.append(T.render.go(T.VPair{kk, T.VAots{aa, bb}} <> tt, ", ", False{}), SCon{close,
        xx}) == String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VAots{aa, bb}, cv.tl(tt, close,
        xx))}}}) : String}, hw)
    case T.VPair{aa, bb}:
      Eq.bit.absurd(&2, {String.append(T.render.go(T.VPair{kk, T.VPair{aa, bb}} <> tt, ", ", False{}), SCon{close,
        xx}) == String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VPair{aa, bb}, cv.tl(tt, close,
        xx))}}}) : String}, hw)

# the part of a check that held
def cv.thl(
  ok: Bool,
  -more: Unit -> Bool,
  hh: {T.wf.then(ok, more) == True{} : Bool}
) -> {ok == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      hh

# and the rest of it
def cv.thr(
  ok: Bool,
  -more: Unit -> Bool,
  hh: {T.wf.then(ok, more) == True{} : Bool}
) -> {more(Unit{}) == True{} : Bool}:
  match ok:
    case True{}:
      hh
    case False{}:
      Eq.bit.absurd(&2, {more(Unit{}) == True{} : Bool}, hh)

# what wf.go says of an array's first item: it may sit in a value position
def cv.wfi.hd(
  ii: T.Val,
  +tt: List<&2, T.Val>,
  hw: {T.wf.go(ii <> tt, T.WfItems{}) == True{} : Bool}
) -> {D1.cv.wf(ii) == True{} : Bool}:
  match ii:
    case T.VArr{+items}:
      cv.thl(T.wf.go(items, T.WfItems{}), _v => T.wf.go(tt, T.WfItems{}), hw)
    case T.VInl{+rows}:
      cv.thl(T.wf.go(rows, T.WfInl{}), _v => T.wf.go(tt, T.WfItems{}), hw)
    case T.VStr{+aa}:
      cv.thl(T.wf.atom(T.VStr{aa}), _u => T.wf.go(tt, T.WfItems{}), hw)
    case T.VSpan{+aa, +bb}:
      cv.thl(T.wf.atom(T.VSpan{aa, bb}), _u => T.wf.go(tt, T.WfItems{}), hw)
    case T.VInt{+aa, +bb}:
      cv.thl(T.wf.atom(T.VInt{aa, bb}), _u => T.wf.go(tt, T.WfItems{}), hw)
    case T.VFlo{+aa, +bb}:
      cv.thl(T.wf.atom(T.VFlo{aa, bb}), _u => T.wf.go(tt, T.WfItems{}), hw)
    case T.VBool{+aa}:
      cv.thl(T.wf.atom(T.VBool{aa}), _u => T.wf.go(tt, T.WfItems{}), hw)
    case T.VWhen{+aa}:
      cv.thl(T.wf.atom(T.VWhen{aa}), _u => T.wf.go(tt, T.WfItems{}), hw)
    case T.VHead{+aa, +bb}:
      cv.thl(T.wf.atom(T.VHead{aa, bb}), _u => T.wf.go(tt, T.WfItems{}), hw)
    case T.VAot{aa, bb}:
      Eq.bit.absurd(&2, {D1.cv.wf(T.VAot{aa, bb}) == True{} : Bool}, hw)
    case T.VAots{+aa, +bb}:
      cv.thl(T.wf.atom(T.VAots{aa, bb}), _u => T.wf.go(tt, T.WfItems{}), hw)
    case T.VPair{aa, bb}:
      match bb:
        case T.VHead{_c, _d}:
          Eq.bit.absurd(&2, {D1.cv.wf(T.VPair{aa, T.VHead{_c, _d}}) == True{} : Bool}, hw)
        case T.VAots{_c, _d}:
          Eq.bit.absurd(&2, {D1.cv.wf(T.VPair{aa, T.VAots{_c, _d}}) == True{} : Bool}, hw)
        case T.VArr{_c}:
          Eq.bit.absurd(&2, {D1.cv.wf(T.VPair{aa, T.VArr{_c}}) == True{} : Bool}, hw)
        case T.VInl{_c}:
          Eq.bit.absurd(&2, {D1.cv.wf(T.VPair{aa, T.VInl{_c}}) == True{} : Bool}, hw)
        case T.VStr{_c}:
          Eq.bit.absurd(&2, {D1.cv.wf(T.VPair{aa, T.VStr{_c}}) == True{} : Bool}, hw)
        case T.VSpan{_c, _d}:
          Eq.bit.absurd(&2, {D1.cv.wf(T.VPair{aa, T.VSpan{_c, _d}}) == True{} : Bool}, hw)
        case T.VInt{_c, _d}:
          Eq.bit.absurd(&2, {D1.cv.wf(T.VPair{aa, T.VInt{_c, _d}}) == True{} : Bool}, hw)
        case T.VFlo{_c, _d}:
          Eq.bit.absurd(&2, {D1.cv.wf(T.VPair{aa, T.VFlo{_c, _d}}) == True{} : Bool}, hw)
        case T.VBool{_c}:
          Eq.bit.absurd(&2, {D1.cv.wf(T.VPair{aa, T.VBool{_c}}) == True{} : Bool}, hw)
        case T.VWhen{_c}:
          Eq.bit.absurd(&2, {D1.cv.wf(T.VPair{aa, T.VWhen{_c}}) == True{} : Bool}, hw)
        case T.VAot{_c, _d}:
          Eq.bit.absurd(&2, {D1.cv.wf(T.VPair{aa, T.VAot{_c, _d}}) == True{} : Bool}, hw)
        case T.VPair{_c, _d}:
          Eq.bit.absurd(&2, {D1.cv.wf(T.VPair{aa, T.VPair{_c, _d}}) == True{} : Bool}, hw)

# and of the items after it
def cv.wfi.tl(
  ii: T.Val,
  +tt: List<&2, T.Val>,
  hw: {T.wf.go(ii <> tt, T.WfItems{}) == True{} : Bool}
) -> {T.wf.go(tt, T.WfItems{}) == True{} : Bool}:
  match ii:
    case T.VArr{+items}:
      cv.thr(T.wf.go(items, T.WfItems{}), _v => T.wf.go(tt, T.WfItems{}), hw)
    case T.VInl{+rows}:
      cv.thr(T.wf.go(rows, T.WfInl{}), _v => T.wf.go(tt, T.WfItems{}), hw)
    case T.VStr{+aa}:
      cv.thr(T.wf.atom(T.VStr{aa}), _u => T.wf.go(tt, T.WfItems{}), hw)
    case T.VSpan{+aa, +bb}:
      cv.thr(T.wf.atom(T.VSpan{aa, bb}), _u => T.wf.go(tt, T.WfItems{}), hw)
    case T.VInt{+aa, +bb}:
      cv.thr(T.wf.atom(T.VInt{aa, bb}), _u => T.wf.go(tt, T.WfItems{}), hw)
    case T.VFlo{+aa, +bb}:
      cv.thr(T.wf.atom(T.VFlo{aa, bb}), _u => T.wf.go(tt, T.WfItems{}), hw)
    case T.VBool{+aa}:
      cv.thr(T.wf.atom(T.VBool{aa}), _u => T.wf.go(tt, T.WfItems{}), hw)
    case T.VWhen{+aa}:
      cv.thr(T.wf.atom(T.VWhen{aa}), _u => T.wf.go(tt, T.WfItems{}), hw)
    case T.VHead{+aa, +bb}:
      cv.thr(T.wf.atom(T.VHead{aa, bb}), _u => T.wf.go(tt, T.WfItems{}), hw)
    case T.VAot{_aa, _bb}:
      Eq.bit.absurd(&2, {T.wf.go(tt, T.WfItems{}) == True{} : Bool}, hw)
    case T.VAots{+aa, +bb}:
      cv.thr(T.wf.atom(T.VAots{aa, bb}), _u => T.wf.go(tt, T.WfItems{}), hw)
    case T.VPair{_aa, bb}:
      match bb:
        case T.VHead{_c, _d}:
          Eq.bit.absurd(&2, {T.wf.go(tt, T.WfItems{}) == True{} : Bool}, hw)
        case T.VAots{_c, _d}:
          Eq.bit.absurd(&2, {T.wf.go(tt, T.WfItems{}) == True{} : Bool}, hw)
        case T.VArr{_c}:
          Eq.bit.absurd(&2, {T.wf.go(tt, T.WfItems{}) == True{} : Bool}, hw)
        case T.VInl{_c}:
          Eq.bit.absurd(&2, {T.wf.go(tt, T.WfItems{}) == True{} : Bool}, hw)
        case T.VStr{_c}:
          Eq.bit.absurd(&2, {T.wf.go(tt, T.WfItems{}) == True{} : Bool}, hw)
        case T.VSpan{_c, _d}:
          Eq.bit.absurd(&2, {T.wf.go(tt, T.WfItems{}) == True{} : Bool}, hw)
        case T.VInt{_c, _d}:
          Eq.bit.absurd(&2, {T.wf.go(tt, T.WfItems{}) == True{} : Bool}, hw)
        case T.VFlo{_c, _d}:
          Eq.bit.absurd(&2, {T.wf.go(tt, T.WfItems{}) == True{} : Bool}, hw)
        case T.VBool{_c}:
          Eq.bit.absurd(&2, {T.wf.go(tt, T.WfItems{}) == True{} : Bool}, hw)
        case T.VWhen{_c}:
          Eq.bit.absurd(&2, {T.wf.go(tt, T.WfItems{}) == True{} : Bool}, hw)
        case T.VAot{_c, _d}:
          Eq.bit.absurd(&2, {T.wf.go(tt, T.WfItems{}) == True{} : Bool}, hw)
        case T.VPair{_c, _d}:
          Eq.bit.absurd(&2, {T.wf.go(tt, T.WfItems{}) == True{} : Bool}, hw)

# what wf.go says of an inline table's first pair: its value may sit in a
# value position
def cv.wfp.v(
  +kk: String,
  vv: T.Val,
  +tt: List<&2, T.Val>,
  hw: {T.wf.go(T.VPair{kk, vv} <> tt, T.WfInl{}) == True{} : Bool}
) -> {D1.cv.wf(vv) == True{} : Bool}:
  match vv:
    case T.VArr{+items}:
      cv.thl(T.wf.go(items, T.WfItems{}), _v => T.wf.go(tt, T.WfInl{}), cv.thr(T.wf.key(kk, tt),
        _u => T.wf.then(T.wf.go(items, T.WfItems{}), _v => T.wf.go(tt, T.WfInl{})), hw))
    case T.VInl{+rows}:
      cv.thl(T.wf.go(rows, T.WfInl{}), _v => T.wf.go(tt, T.WfInl{}), cv.thr(T.wf.key(kk, tt),
        _u => T.wf.then(T.wf.go(rows, T.WfInl{}), _v => T.wf.go(tt, T.WfInl{})), hw))
    case T.VStr{+aa}:
      Eq.and.left(T.wf.atom(T.VStr{aa}), T.wf.key(kk, tt), cv.thl(Bool.and(T.wf.atom(T.VStr{aa}), T.wf.key(kk, tt)),
        _u => T.wf.go(tt, T.WfInl{}), hw))
    case T.VSpan{+aa, +bb}:
      Eq.and.left(T.wf.atom(T.VSpan{aa, bb}), T.wf.key(kk, tt), cv.thl(Bool.and(T.wf.atom(T.VSpan{aa, bb}),
        T.wf.key(kk, tt)), _u => T.wf.go(tt, T.WfInl{}), hw))
    case T.VInt{+aa, +bb}:
      Eq.and.left(T.wf.atom(T.VInt{aa, bb}), T.wf.key(kk, tt), cv.thl(Bool.and(T.wf.atom(T.VInt{aa, bb}),
        T.wf.key(kk, tt)), _u => T.wf.go(tt, T.WfInl{}), hw))
    case T.VFlo{+aa, +bb}:
      Eq.and.left(T.wf.atom(T.VFlo{aa, bb}), T.wf.key(kk, tt), cv.thl(Bool.and(T.wf.atom(T.VFlo{aa, bb}),
        T.wf.key(kk, tt)), _u => T.wf.go(tt, T.WfInl{}), hw))
    case T.VBool{+aa}:
      Eq.and.left(T.wf.atom(T.VBool{aa}), T.wf.key(kk, tt), cv.thl(Bool.and(T.wf.atom(T.VBool{aa}), T.wf.key(kk, tt)),
        _u => T.wf.go(tt, T.WfInl{}), hw))
    case T.VWhen{+aa}:
      Eq.and.left(T.wf.atom(T.VWhen{aa}), T.wf.key(kk, tt), cv.thl(Bool.and(T.wf.atom(T.VWhen{aa}), T.wf.key(kk, tt)),
        _u => T.wf.go(tt, T.WfInl{}), hw))
    case T.VHead{aa, bb}:
      Eq.bit.absurd(&2, {D1.cv.wf(T.VHead{aa, bb}) == True{} : Bool}, hw)
    case T.VAot{+aa, +bb}:
      Eq.and.left(T.wf.atom(T.VAot{aa, bb}), T.wf.key(kk, tt), cv.thl(Bool.and(T.wf.atom(T.VAot{aa, bb}),
        T.wf.key(kk, tt)), _u => T.wf.go(tt, T.WfInl{}), hw))
    case T.VAots{aa, bb}:
      Eq.bit.absurd(&2, {D1.cv.wf(T.VAots{aa, bb}) == True{} : Bool}, hw)
    case T.VPair{+aa, +bb}:
      Eq.and.left(T.wf.atom(T.VPair{aa, bb}), T.wf.key(kk, tt), cv.thl(Bool.and(T.wf.atom(T.VPair{aa, bb}),
        T.wf.key(kk, tt)), _u => T.wf.go(tt, T.WfInl{}), hw))

# its name is none of the later pairs'
def cv.wfp.k(
  +kk: String,
  vv: T.Val,
  +tt: List<&2, T.Val>,
  hw: {T.wf.go(T.VPair{kk, vv} <> tt, T.WfInl{}) == True{} : Bool}
) -> {T.wf.key(kk, tt) == True{} : Bool}:
  match vv:
    case T.VArr{+items}:
      cv.thl(T.wf.key(kk, tt), _u => T.wf.then(T.wf.go(items, T.WfItems{}), _v => T.wf.go(tt, T.WfInl{})), hw)
    case T.VInl{+rows}:
      cv.thl(T.wf.key(kk, tt), _u => T.wf.then(T.wf.go(rows, T.WfInl{}), _v => T.wf.go(tt, T.WfInl{})), hw)
    case T.VStr{+aa}:
      Eq.and.right(T.wf.atom(T.VStr{aa}), T.wf.key(kk, tt), cv.thl(Bool.and(T.wf.atom(T.VStr{aa}), T.wf.key(kk, tt)),
        _u => T.wf.go(tt, T.WfInl{}), hw))
    case T.VSpan{+aa, +bb}:
      Eq.and.right(T.wf.atom(T.VSpan{aa, bb}), T.wf.key(kk, tt), cv.thl(Bool.and(T.wf.atom(T.VSpan{aa, bb}),
        T.wf.key(kk, tt)), _u => T.wf.go(tt, T.WfInl{}), hw))
    case T.VInt{+aa, +bb}:
      Eq.and.right(T.wf.atom(T.VInt{aa, bb}), T.wf.key(kk, tt), cv.thl(Bool.and(T.wf.atom(T.VInt{aa, bb}),
        T.wf.key(kk, tt)), _u => T.wf.go(tt, T.WfInl{}), hw))
    case T.VFlo{+aa, +bb}:
      Eq.and.right(T.wf.atom(T.VFlo{aa, bb}), T.wf.key(kk, tt), cv.thl(Bool.and(T.wf.atom(T.VFlo{aa, bb}),
        T.wf.key(kk, tt)), _u => T.wf.go(tt, T.WfInl{}), hw))
    case T.VBool{+aa}:
      Eq.and.right(T.wf.atom(T.VBool{aa}), T.wf.key(kk, tt), cv.thl(Bool.and(T.wf.atom(T.VBool{aa}),
        T.wf.key(kk, tt)), _u => T.wf.go(tt, T.WfInl{}), hw))
    case T.VWhen{+aa}:
      Eq.and.right(T.wf.atom(T.VWhen{aa}), T.wf.key(kk, tt), cv.thl(Bool.and(T.wf.atom(T.VWhen{aa}),
        T.wf.key(kk, tt)), _u => T.wf.go(tt, T.WfInl{}), hw))
    case T.VHead{_aa, _bb}:
      Eq.bit.absurd(&2, {T.wf.key(kk, tt) == True{} : Bool}, hw)
    case T.VAot{+aa, +bb}:
      Eq.and.right(T.wf.atom(T.VAot{aa, bb}), T.wf.key(kk, tt), cv.thl(Bool.and(T.wf.atom(T.VAot{aa, bb}),
        T.wf.key(kk, tt)), _u => T.wf.go(tt, T.WfInl{}), hw))
    case T.VAots{_aa, _bb}:
      Eq.bit.absurd(&2, {T.wf.key(kk, tt) == True{} : Bool}, hw)
    case T.VPair{+aa, +bb}:
      Eq.and.right(T.wf.atom(T.VPair{aa, bb}), T.wf.key(kk, tt), cv.thl(Bool.and(T.wf.atom(T.VPair{aa, bb}),
        T.wf.key(kk, tt)), _u => T.wf.go(tt, T.WfInl{}), hw))

# and the later pairs are well-formed
def cv.wfp.t(
  +kk: String,
  vv: T.Val,
  +tt: List<&2, T.Val>,
  hw: {T.wf.go(T.VPair{kk, vv} <> tt, T.WfInl{}) == True{} : Bool}
) -> {T.wf.go(tt, T.WfInl{}) == True{} : Bool}:
  match vv:
    case T.VArr{+items}:
      cv.thr(T.wf.go(items, T.WfItems{}), _v => T.wf.go(tt, T.WfInl{}), cv.thr(T.wf.key(kk, tt),
        _u => T.wf.then(T.wf.go(items, T.WfItems{}), _v => T.wf.go(tt, T.WfInl{})), hw))
    case T.VInl{+rows}:
      cv.thr(T.wf.go(rows, T.WfInl{}), _v => T.wf.go(tt, T.WfInl{}), cv.thr(T.wf.key(kk, tt),
        _u => T.wf.then(T.wf.go(rows, T.WfInl{}), _v => T.wf.go(tt, T.WfInl{})), hw))
    case T.VStr{+aa}:
      cv.thr(Bool.and(T.wf.atom(T.VStr{aa}), T.wf.key(kk, tt)), _u => T.wf.go(tt, T.WfInl{}), hw)
    case T.VSpan{+aa, +bb}:
      cv.thr(Bool.and(T.wf.atom(T.VSpan{aa, bb}), T.wf.key(kk, tt)), _u => T.wf.go(tt, T.WfInl{}), hw)
    case T.VInt{+aa, +bb}:
      cv.thr(Bool.and(T.wf.atom(T.VInt{aa, bb}), T.wf.key(kk, tt)), _u => T.wf.go(tt, T.WfInl{}), hw)
    case T.VFlo{+aa, +bb}:
      cv.thr(Bool.and(T.wf.atom(T.VFlo{aa, bb}), T.wf.key(kk, tt)), _u => T.wf.go(tt, T.WfInl{}), hw)
    case T.VBool{+aa}:
      cv.thr(Bool.and(T.wf.atom(T.VBool{aa}), T.wf.key(kk, tt)), _u => T.wf.go(tt, T.WfInl{}), hw)
    case T.VWhen{+aa}:
      cv.thr(Bool.and(T.wf.atom(T.VWhen{aa}), T.wf.key(kk, tt)), _u => T.wf.go(tt, T.WfInl{}), hw)
    case T.VHead{_aa, _bb}:
      Eq.bit.absurd(&2, {T.wf.go(tt, T.WfInl{}) == True{} : Bool}, hw)
    case T.VAot{+aa, +bb}:
      cv.thr(Bool.and(T.wf.atom(T.VAot{aa, bb}), T.wf.key(kk, tt)), _u => T.wf.go(tt, T.WfInl{}), hw)
    case T.VAots{_aa, _bb}:
      Eq.bit.absurd(&2, {T.wf.go(tt, T.WfInl{}) == True{} : Bool}, hw)
    case T.VPair{+aa, +bb}:
      cv.thr(Bool.and(T.wf.atom(T.VPair{aa, bb}), T.wf.key(kk, tt)), _u => T.wf.go(tt, T.WfInl{}), hw)

# the strings of an item and of the items after it
def cv.sh.item(
  ii: T.Val,
  +tt: List<&2, T.Val>,
  hw: {D1.cv.wf(ii) == True{} : Bool}
) -> {D1.cv.shorts(ii <> tt) == Bool.and(D1.cv.short1(ii), D1.cv.shorts(tt)) : Bool}:
  match ii:
    case T.VStr{_a}:
      {==}
    case T.VSpan{_a, _b}:
      {==}
    case T.VInt{_a, _b}:
      {==}
    case T.VFlo{_a, _b}:
      {==}
    case T.VBool{_a}:
      {==}
    case T.VWhen{_a}:
      {==}
    case T.VArr{_a}:
      {==}
    case T.VInl{_a}:
      {==}
    case T.VHead{_a, _b}:
      {==}
    case T.VAot{_a, _b}:
      {==}
    case T.VAots{_a, _b}:
      {==}
    case T.VPair{aa, bb}:
      Eq.bit.absurd(&2, {D1.cv.shorts(T.VPair{aa, bb} <> tt) == Bool.and(D1.cv.short1(T.VPair{aa, bb}),
        D1.cv.shorts(tt)) : Bool}, hw)

# the strings of a pair's value and of the pairs after it
def cv.sh.pair(
  +kk: String,
  vv: T.Val,
  +tt: List<&2, T.Val>
) -> {D1.cv.shorts(T.VPair{kk, vv} <> tt) == Bool.and(D1.cv.short1(vv), D1.cv.shorts(tt)) : Bool}:
  match vv:
    case T.VStr{_a}:
      {==}
    case T.VSpan{_a, _b}:
      {==}
    case T.VInt{_a, _b}:
      {==}
    case T.VFlo{_a, _b}:
      {==}
    case T.VBool{_a}:
      {==}
    case T.VWhen{_a}:
      {==}
    case T.VArr{_a}:
      {==}
    case T.VInl{_a}:
      {==}
    case T.VHead{_a, _b}:
      {==}
    case T.VAot{_a, _b}:
      {==}
    case T.VAots{_a, _b}:
      {==}
    case T.VPair{_a, _b}:
      {==}

# Names. The pairs read so far are the inline table's rows, newest first; a
# pair's name must be none of theirs for the walk to put it, and wf says it is
# none of the later pairs'. str.eq is symmetric, so that is the same thing.

# a lookup that missed is a miss
def cv.miss(
  hh: T.Hit,
  ee: {L4.is_miss(hh) == True{} : Bool}
) -> {hh == T.Miss{} : T.Hit}:
  match hh:
    case T.Miss{}:
      {==}
    case T.Found{vv}:
      Eq.bit.absurd(&2, {T.Found{vv} == T.Miss{} : T.Hit}, ee)

# a pair put in front keeps every later name missing, once its own name is
# none of theirs
def cv.fr.step(
  tt: List<&2, T.Val>,
  +kk: String,
  +v2: T.Val,
  +inl: List<&2, T.Val>,
  +h1: {M8.cv.fr(inl, tt) == True{} : Bool},
  +h2: {T.wf.fresh(T.get(tt, kk)) == True{} : Bool}
) -> {M8.cv.fr(T.VPair{kk, v2} <> inl, tt) == True{} : Bool}:
  match tt:
    case []:
      {==}
    case T.VPair{+k2, +xx} <> +t2:
      +e1 = {M8.cv.fs.l(T.str.eq(k2, kk), xx, _u => T.rows.find(t2, kk), h2) : {T.str.eq(k2, kk) == False{} : Bool}}
      +e3 = {Equal.trans(Bool, T.str.eq(kk, k2), T.str.eq(k2, kk), False{}, M8.cv.seqs(kk, k2, True{}), e1)
        : {T.str.eq(kk, k2) == False{} : Bool}}
      %Equal.sym(Bool, T.str.eq(kk, k2), False{}, e3) : {Bool.and(L4.is_miss(T.find.step(_, v2,
        _u => T.rows.find(inl, k2))), M8.cv.fr(T.VPair{kk, v2} <> inl, t2)) == True{} : Bool}
      M15.cv.and2(L4.is_miss(T.rows.find(inl, k2)), M8.cv.fr(T.VPair{kk, v2} <> inl, t2),
        Eq.and.left(L4.is_miss(T.get(inl, k2)), M8.cv.fr(inl, t2), h1),
        cv.fr.step(t2, kk, v2, inl, Eq.and.right(L4.is_miss(T.get(inl, k2)), M8.cv.fr(inl, t2), h1),
          M8.cv.fs.r(T.str.eq(k2, kk), xx, _u => T.rows.find(t2, kk), h2)))
    case T.VStr{_a} <> +t2:
      cv.fr.step(t2, kk, v2, inl, h1, h2)
    case T.VSpan{_a, _b} <> +t2:
      cv.fr.step(t2, kk, v2, inl, h1, h2)
    case T.VInt{_a, _b} <> +t2:
      cv.fr.step(t2, kk, v2, inl, h1, h2)
    case T.VFlo{_a, _b} <> +t2:
      cv.fr.step(t2, kk, v2, inl, h1, h2)
    case T.VBool{_a} <> +t2:
      cv.fr.step(t2, kk, v2, inl, h1, h2)
    case T.VWhen{_a} <> +t2:
      cv.fr.step(t2, kk, v2, inl, h1, h2)
    case T.VArr{_a} <> +t2:
      cv.fr.step(t2, kk, v2, inl, h1, h2)
    case T.VInl{_a} <> +t2:
      cv.fr.step(t2, kk, v2, inl, h1, h2)
    case T.VHead{_a, _b} <> +t2:
      cv.fr.step(t2, kk, v2, inl, h1, h2)
    case T.VAot{_a, _b} <> +t2:
      cv.fr.step(t2, kk, v2, inl, h1, h2)
    case T.VAots{_a, _b} <> +t2:
      cv.fr.step(t2, kk, v2, inl, h1, h2)

# Values put. A value own reads as the scanner's form of a well-formed value
# is no pair and no table, so a pair of it reads as the pair of that form,
# and sealing an inline table leaves it where it is.

# no pair and no table
def cv.plain(vv: T.Val) -> Bool:
  match vv:
    case T.VPair{_nn, _yy}:
      False{}
    case T.VHead{_pp, _rr}:
      False{}
    case _:
      True{}

# own keeps a value a pair or a table, or neither
def cv.plain.own(xx: T.Val) -> {cv.plain(L15.cv.own1(xx)) == cv.plain(xx) : Bool}:
  match xx:
    case T.VPair{_nn, yy}:
      match yy:
        case T.VStr{_a}:
          {==}
        case T.VSpan{_a, _b}:
          {==}
        case T.VInt{_a, _b}:
          {==}
        case T.VFlo{_a, _b}:
          {==}
        case T.VBool{_a}:
          {==}
        case T.VWhen{_a}:
          {==}
        case T.VArr{_a}:
          {==}
        case T.VInl{_a}:
          {==}
        case T.VHead{_a, _b}:
          {==}
        case T.VAot{_a, _b}:
          {==}
        case T.VAots{_a, _b}:
          {==}
        case T.VPair{_a, _b}:
          {==}
    case T.VStr{_a}:
      {==}
    case T.VSpan{_a, _b}:
      {==}
    case T.VInt{_a, _b}:
      {==}
    case T.VFlo{_a, _b}:
      {==}
    case T.VBool{_a}:
      {==}
    case T.VWhen{_a}:
      {==}
    case T.VArr{_a}:
      {==}
    case T.VInl{_a}:
      {==}
    case T.VHead{_a, _b}:
      {==}
    case T.VAot{_a, _b}:
      {==}
    case T.VAots{_a, _b}:
      {==}

# the scanner's form of a well-formed value is no pair and no table
def cv.plain.raw(
  vv: T.Val,
  hw: {D1.cv.wf(vv) == True{} : Bool}
) -> {cv.plain(L15.cv.raw1(vv)) == True{} : Bool}:
  match vv:
    case T.VStr{_a}:
      {==}
    case T.VSpan{_a, _b}:
      {==}
    case T.VInt{_a, _b}:
      {==}
    case T.VFlo{_a, _b}:
      {==}
    case T.VBool{_a}:
      {==}
    case T.VWhen{_a}:
      {==}
    case T.VArr{_a}:
      {==}
    case T.VInl{_a}:
      {==}
    case T.VHead{aa, bb}:
      Eq.bit.absurd(&2, {cv.plain(L15.cv.raw1(T.VHead{aa, bb})) == True{} : Bool}, hw)
    case T.VAot{_a, _b}:
      {==}
    case T.VAots{_a, _b}:
      {==}
    case T.VPair{aa, bb}:
      Eq.bit.absurd(&2, {cv.plain(L15.cv.raw1(T.VPair{aa, bb})) == True{} : Bool}, hw)

# so a value put for it is no pair and no table
def cv.plain.of(
  +vv: T.Val,
  +ww: T.Val,
  hh: {L15.cv.own1(vv) == L15.cv.raw1(ww) : T.Val},
  hw: {D1.cv.wf(ww) == True{} : Bool}
) -> {cv.plain(vv) == True{} : Bool}:
  Equal.trans(Bool, cv.plain(vv), cv.plain(L15.cv.own1(vv)), True{},
    Equal.sym(Bool, cv.plain(L15.cv.own1(vv)), cv.plain(vv), cv.plain.own(vv)),
    Equal.trans(Bool, cv.plain(L15.cv.own1(vv)), cv.plain(L15.cv.raw1(ww)), True{},
      Equal.cong(T.Val, Bool, xx => cv.plain(xx), L15.cv.own1(vv), L15.cv.raw1(ww), hh),
      cv.plain.raw(ww, hw)))

# own reads a pair of a value that is no pair as the pair of what it reads
def cv.own.pair(
  +kk: String,
  vv: T.Val,
  hp: {cv.plain(vv) == True{} : Bool}
) -> {L15.cv.own1(T.VPair{kk, vv}) == T.VPair{kk, L15.cv.own1(vv)} : T.Val}:
  match vv:
    case T.VStr{_a}:
      {==}
    case T.VSpan{_a, _b}:
      {==}
    case T.VInt{_a, _b}:
      {==}
    case T.VFlo{_a, _b}:
      {==}
    case T.VBool{_a}:
      {==}
    case T.VWhen{_a}:
      {==}
    case T.VArr{_a}:
      {==}
    case T.VInl{_a}:
      {==}
    case T.VHead{_a, _b}:
      {==}
    case T.VAot{_a, _b}:
      {==}
    case T.VAots{_a, _b}:
      {==}
    case T.VPair{aa, bb}:
      Eq.bit.absurd(&2, {L15.cv.own1(T.VPair{kk, T.VPair{aa, bb}}) == T.VPair{kk, L15.cv.own1(T.VPair{aa, bb})}
        : T.Val}, hp)

# and so does the scanner's form
def cv.raw.pair(
  +kk: String,
  vv: T.Val,
  hw: {D1.cv.wf(vv) == True{} : Bool}
) -> {L15.cv.raw1(T.VPair{kk, vv}) == T.VPair{kk, L15.cv.raw1(vv)} : T.Val}:
  match vv:
    case T.VStr{_a}:
      {==}
    case T.VSpan{_a, _b}:
      {==}
    case T.VInt{_a, _b}:
      {==}
    case T.VFlo{_a, _b}:
      {==}
    case T.VBool{_a}:
      {==}
    case T.VWhen{_a}:
      {==}
    case T.VArr{_a}:
      {==}
    case T.VInl{_a}:
      {==}
    case T.VHead{_a, _b}:
      {==}
    case T.VAot{_a, _b}:
      {==}
    case T.VAots{_a, _b}:
      {==}
    case T.VPair{aa, bb}:
      Eq.bit.absurd(&2, {L15.cv.raw1(T.VPair{kk, T.VPair{aa, bb}}) == T.VPair{kk, L15.cv.raw1(T.VPair{aa, bb})}
        : T.Val}, hw)

# a pair of a value put reads as the pair of the value render wrote
def cv.lift(
  +kk: String,
  +vv: T.Val,
  +ww: T.Val,
  +hh: {L15.cv.own1(vv) == L15.cv.raw1(ww) : T.Val},
  +hw: {D1.cv.wf(ww) == True{} : Bool}
) -> {L15.cv.own1(T.VPair{kk, vv}) == L15.cv.raw1(T.VPair{kk, ww}) : T.Val}:
  Equal.trans(T.Val, L15.cv.own1(T.VPair{kk, vv}), T.VPair{kk, L15.cv.own1(vv)}, L15.cv.raw1(T.VPair{kk, ww}),
    cv.own.pair(kk, vv, cv.plain.of(vv, ww, hh, hw)),
    Equal.trans(T.Val, T.VPair{kk, L15.cv.own1(vv)}, T.VPair{kk, L15.cv.raw1(ww)}, L15.cv.raw1(T.VPair{kk, ww}),
      Equal.cong(T.Val, T.Val, yy => T.VPair{kk, yy}, L15.cv.own1(vv), L15.cv.raw1(ww), hh),
      Equal.sym(T.Val, L15.cv.raw1(T.VPair{kk, ww}), T.VPair{kk, L15.cv.raw1(ww)}, cv.raw.pair(kk, ww, hw))))

# sealing passes over a pair of a value that is no table
def cv.seal.cons(
  +kk: String,
  vv: T.Val,
  +xs: List<&2, T.Val>,
  hp: {cv.plain(vv) == True{} : Bool}
) -> {T.inl.seal(T.VPair{kk, vv} <> xs) == T.VPair{kk, vv} <> T.inl.seal(xs) : List<&2, T.Val>}:
  match vv:
    case T.VStr{_a}:
      {==}
    case T.VSpan{_a, _b}:
      {==}
    case T.VInt{_a, _b}:
      {==}
    case T.VFlo{_a, _b}:
      {==}
    case T.VBool{_a}:
      {==}
    case T.VWhen{_a}:
      {==}
    case T.VArr{_a}:
      {==}
    case T.VInl{_a}:
      {==}
    case T.VHead{aa, bb}:
      Eq.bit.absurd(&2, {T.inl.seal(T.VPair{kk, T.VHead{aa, bb}} <> xs) == T.VPair{kk, T.VHead{aa, bb}} <>
        T.inl.seal(xs) : List<&2, T.Val>}, hp)
    case T.VAot{_a, _b}:
      {==}
    case T.VAots{_a, _b}:
      {==}
    case T.VPair{_a, _b}:
      {==}

# An inline table's pair. The key is read to the value position with the key
# as the one part; the value is read and put by a walk of that one part into
# the frame's rows (WP-W's put contract, with the rows so far as the table,
# no heads and the inline flag), so it goes in front; the scanner waits in
# LInlC, where ", " goes on to the next key and `}` closes the table.

# the scanner after a pair of an inline table, waiting for ", " or `}`
def cv.ic(
  inl: List<&2, T.Val>,
  ps0: List<&2, String>,
  +he0: List<&2, String>,
  rw: List<&2, T.Val>,
  hs: List<&2, String>,
  bk: T.Lex,
  qk: T.QKind,
  sk: List<&2, T.Ctx>,
  un: U32,
  lf: U32,
  ab: Bool
) -> T.St:
  T.St{"", rw, hs, he0, [], [], T.LInlC{}, bk, qk, T.CInl{inl, ps0, he0} <> sk, T.HNone{}, un, lf, ab, False{}}

# the claim for the pairs after one, from the frame with any pair of the
# name put in front and any fields that value leaves
def cv.IhI(
  +tt: List<&2, T.Val>,
  +kk: String,
  +inl: List<&2, T.Val>,
  +ps0: List<&2, String>,
  +he0: List<&2, String>,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  @v2: T.Val -> @b2: T.Lex -> @q2: T.QKind -> @u2: U32 -> @l2: U32 ->
    cv.G(tt, True{}, T.VPair{kk, v2} <> inl, ps0, he0, rw, hs, he0, [], b2, q2, sk, u2, l2, ab, rest, PP)

# the reader of a pair's value, from wherever the key left the fields
def cv.RdP(
  +vv: T.Val,
  +kk: String,
  +inl: List<&2, T.Val>,
  +ps0: List<&2, String>,
  +he0: List<&2, String>,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +zz: String,
  -PP: T.Doc -> Type
) -> Type:
  @b2: T.Lex -> @q2: T.QKind -> @u2: U32 -> @l2: U32 -> {D1.cv.wf(vv) == True{} : Bool} ->
    {D1.cv.short1(vv) == True{} : Bool} ->
    cv.Rd(vv, rw, hs, he0, [kk], b2, q2, T.CInl{inl, ps0, he0} <> sk, u2, l2, ab, zz, PP)

# the frame's rows once a pair is put in front: sealing still leaves them
def cv.seal.put(
  +kk: String,
  +v2: T.Val,
  +vv: T.Val,
  +inl: List<&2, T.Val>,
  hh: {L15.cv.own1(v2) == L15.cv.raw1(vv) : T.Val},
  hwv: {D1.cv.wf(vv) == True{} : Bool},
  hsl: {T.inl.seal(inl) == inl : List<&2, T.Val>}
) -> {T.inl.seal(T.VPair{kk, v2} <> inl) == T.VPair{kk, v2} <> inl : List<&2, T.Val>}:
  Equal.trans(List<&2, T.Val>, T.inl.seal(T.VPair{kk, v2} <> inl), T.VPair{kk, v2} <> T.inl.seal(inl),
    T.VPair{kk, v2} <> inl, cv.seal.cons(kk, v2, inl, cv.plain.of(v2, vv, hh, hwv)),
    Equal.cong(List<&2, T.Val>, List<&2, T.Val>, ys => T.VPair{kk, v2} <> ys, T.inl.seal(inl), inl, hsl))

# after the pair is put: `}` closes, ", " goes on
def cv.afteri.go(
  tt: List<&2, T.Val>,
  +kk: String,
  +vv: T.Val,
  +v2: T.Val,
  +inl: List<&2, T.Val>,
  +ps0: List<&2, String>,
  +he0: List<&2, String>,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  +hh: {L15.cv.own1(v2) == L15.cv.raw1(vv) : T.Val},
  ih_t: cv.IhI(tt, kk, inl, ps0, he0, rw, hs, sk, ab, rest, PP),
  hwt: {T.wf.go(tt, T.WfInl{}) == True{} : Bool},
  hst: {D1.cv.shorts(tt) == True{} : Bool},
  hn: {L15.cv.end(rest) == True{} : Bool},
  hfr: {T.wf.fresh(T.get(tt, kk)) == True{} : Bool},
  hft: {M8.cv.fr(inl, tt) == True{} : Bool},
  hsl: {T.inl.seal(inl) == inl : List<&2, T.Val>},
  +hwv: {D1.cv.wf(vv) == True{} : Bool},
  then: cv.ThenI(T.VPair{kk, vv} <> tt, inl, ps0, he0, rw, hs, sk, ab, rest, PP)
) -> PP(T.doc.read(cv.tl(tt, '}', rest), T.MScan{cv.ic(T.VPair{kk, v2} <> inl, ps0, he0, rw, hs, bk, qk, sk, un, lf,
  ab)})):
  match tt:
    case []:
      pp.step(PP, T.doc.read(SCon{'}', rest}, T.MScan{cv.ic(T.VPair{kk, v2} <> inl, ps0, he0, rw, hs, bk, qk, sk, un,
        lf, ab)}),
        T.doc.read(rest, T.MScan{cv.put(sk, T.VInl{T.inl.seal(T.VPair{kk, v2} <> inl)}, rw, hs, he0, ps0, bk, qk, un,
          lf, ab)}),
        Equal.cong(T.St, T.Doc, st => T.doc.read(rest, T.MScan{st}),
          T.read.once2(cv.put(sk, T.VInl{T.inl.seal(T.VPair{kk, v2} <> inl)}, rw, hs, he0, ps0, bk, qk, un, lf, ab)),
          cv.put(sk, T.VInl{T.inl.seal(T.VPair{kk, v2} <> inl)}, rw, hs, he0, ps0, bk, qk, un, lf, ab),
          Equal.sym(T.St, cv.put(sk, T.VInl{T.inl.seal(T.VPair{kk, v2} <> inl)}, rw, hs, he0, ps0, bk, qk, un, lf, ab),
            T.read.once2(cv.put(sk, T.VInl{T.inl.seal(T.VPair{kk, v2} <> inl)}, rw, hs, he0, ps0, bk, qk, un, lf,
            ab)), M9.tk.once(sk, T.VInl{T.inl.seal(T.VPair{kk, v2} <> inl)}, "", rw, hs, he0, ps0, bk, qk, un, lf, ab,
            False{}))),
        then(T.VPair{kk, v2} <> inl, bk, qk, un, lf, cv.grew(T.VPair{kk, vv}, [], T.VPair{kk, v2}, inl,
          T.VPair{kk, v2} <> inl, cv.lift(kk, v2, vv, hh, hwv), {==}), cv.seal.put(kk, v2, vv, inl, hh, hwv, hsl)))
    case +h2 <> +t2:
      ih_t(v2, bk, qk, un, lf)({==}, hwt, hst, hn, cv.fr.step(h2 <> t2, kk, v2, inl, hft, hfr),
        cv.seal.put(kk, v2, vv, inl, hh, hwv, hsl),
        +in2 => b4 => q4 => u4 => l4 => hg => hs4 => then(in2, b4, q4, u4, l4, cv.grew(T.VPair{kk, vv}, h2 <> t2,
          T.VPair{kk, v2}, inl, in2, cv.lift(kk, v2, vv, hh, hwv), hg), hs4))

# after a pair's value: the walk puts the pair in front, then `}` closes the
# table and ", " waits for the next key
def cv.afteri(
  +tt: List<&2, T.Val>,
  +kk: String,
  +vv: T.Val,
  +v2: T.Val,
  +inl: List<&2, T.Val>,
  +ps0: List<&2, String>,
  +he0: List<&2, String>,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  +hh: {L15.cv.own1(v2) == L15.cv.raw1(vv) : T.Val},
  ih_t: cv.IhI(tt, kk, inl, ps0, he0, rw, hs, sk, ab, rest, PP),
  hwt: {T.wf.go(tt, T.WfInl{}) == True{} : Bool},
  hst: {D1.cv.shorts(tt) == True{} : Bool},
  hn: {L15.cv.end(rest) == True{} : Bool},
  hfr: {T.wf.fresh(T.get(tt, kk)) == True{} : Bool},
  hft: {M8.cv.fr(inl, tt) == True{} : Bool},
  hsl: {T.inl.seal(inl) == inl : List<&2, T.Val>},
  +hwv: {D1.cv.wf(vv) == True{} : Bool},
  em: {T.get(inl, kk) == T.Miss{} : T.Hit},
  then: cv.ThenI(T.VPair{kk, vv} <> tt, inl, ps0, he0, rw, hs, sk, ab, rest, PP)
) -> PP(T.doc.read(cv.tl(tt, '}', rest), T.MScan{cv.put(T.CInl{inl, ps0, he0} <> sk, v2, rw, hs, he0, [kk], bk, qk,
  un, lf, ab)})):
  pp.step(PP, T.doc.read(cv.tl(tt, '}', rest), T.MScan{cv.put(T.CInl{inl, ps0, he0} <> sk, v2, rw, hs, he0, [kk], bk,
    qk, un, lf, ab)}),
    T.doc.read(cv.tl(tt, '}', rest), T.MScan{cv.ic(T.VPair{kk, v2} <> inl, ps0, he0, rw, hs, bk, qk, sk, un, lf, ab)}),
    Equal.cong(T.End, T.Doc, en => T.doc.read(cv.tl(tt, '}', rest), T.MScan{T.take.inl(en, rw, hs, he0, ps0, sk, bk,
      qk, un, lf, ab, False{})}),
      T.tree.walk(List.append(&2, String, [], [kk]), T.Tw{inl, T.JPut{v2}, [], "", "", [], True{}}, 0),
      T.End{D1.tb.set([], "", inl, T.VPair{kk, v2} <> D1.tb.rows([], inl)), "", []},
      L16.walk_put_at_head([], kk, v2, inl, [], 0, True{}, {==}, {==}, em)),
    cv.afteri.go(tt, kk, vv, v2, inl, ps0, he0, rw, hs, bk, qk, sk, un, lf, ab, rest, PP, hh, ih_t, hwt, hst, hn, hfr,
      hft, hsl, hwv, then))

# a pair, then what follows it: the key, " = ", the value, put in front of
# the frame's rows
def cv.pair(
  +kk: String,
  +vv: T.Val,
  +tt: List<&2, T.Val>,
  +inl: List<&2, T.Val>,
  +ps0: List<&2, String>,
  +he0: List<&2, String>,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  rd: cv.RdP(vv, kk, inl, ps0, he0, rw, hs, sk, ab, cv.tl(tt, '}', rest), PP),
  ih_t: cv.IhI(tt, kk, inl, ps0, he0, rw, hs, sk, ab, rest, PP),
  +hw: {T.wf.go(T.VPair{kk, vv} <> tt, T.WfInl{}) == True{} : Bool},
  +hs2: {D1.cv.shorts(T.VPair{kk, vv} <> tt) == True{} : Bool},
  hn: {L15.cv.end(rest) == True{} : Bool},
  +hfi: {M8.cv.fr(inl, T.VPair{kk, vv} <> tt) == True{} : Bool},
  hsl: {T.inl.seal(inl) == inl : List<&2, T.Val>},
  then: cv.ThenI(T.VPair{kk, vv} <> tt, inl, ps0, he0, rw, hs, sk, ab, rest, PP)
) -> PP(T.doc.read(String.append(T.render.go(T.VPair{kk, vv} <> tt, ", ", False{}), SCon{'}', rest}),
  T.MScan{cv.ik(inl, ps0, he0, rw, hs, bk, qk, sk, un, lf, ab)})):
  +hwv = {cv.wfp.v(kk, vv, tt, hw) : {D1.cv.wf(vv) == True{} : Bool}}
  +hsp = {Equal.trans(Bool, Bool.and(D1.cv.short1(vv), D1.cv.shorts(tt)), D1.cv.shorts(T.VPair{kk, vv} <> tt),
    True{}, Equal.sym(Bool, D1.cv.shorts(T.VPair{kk, vv} <> tt), Bool.and(D1.cv.short1(vv), D1.cv.shorts(tt)),
    cv.sh.pair(kk, vv, tt)), hs2) : {Bool.and(D1.cv.short1(vv), D1.cv.shorts(tt)) == True{} : Bool}}
  +zz = {cv.tl(tt, '}', rest) : String}
  pp.step(PP, T.doc.read(String.append(T.render.go(T.VPair{kk, vv} <> tt, ", ", False{}), SCon{'}', rest}),
    T.MScan{cv.ik(inl, ps0, he0, rw, hs, bk, qk, sk, un, lf, ab)}),
    T.doc.read(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(vv, zz)}}}),
      T.MScan{cv.ik(inl, ps0, he0, rw, hs, bk, qk, sk, un, lf, ab)}),
    Equal.cong(String, T.Doc, xs => T.doc.read(xs, T.MScan{cv.ik(inl, ps0, he0, rw, hs, bk, qk, sk, un, lf, ab)}),
      String.append(T.render.go(T.VPair{kk, vv} <> tt, ", ", False{}), SCon{'}', rest}),
      String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(vv, zz)}}}),
      cv.ptx(kk, vv, tt, '}', rest, hwv)),
    cv.key(kk, D1.cv.tx(vv, zz), rw, hs, he0, bk, qk, T.CInl{inl, ps0, he0} <> sk, un, lf, ab, PP,
      b2 => q2 => u2 => l2 => rd(b2, q2, u2, l2, hwv, Eq.and.left(D1.cv.short1(vv), D1.cv.shorts(tt), hsp))(
        cv.tl.endi(tt, rest), +v2 => b3 => q3 => u3 => l3 => hh => cv.afteri(tt, kk, vv, v2, inl, ps0, he0, rw, hs, b3,
        q3, sk, u3, l3, ab, rest, PP, hh, ih_t, cv.wfp.t(kk, vv, tt, hw), Eq.and.right(D1.cv.short1(vv),
        D1.cv.shorts(tt), hsp), hn, Eq.and.right(T.wf.text(kk), T.wf.fresh(T.get(tt, kk)), cv.wfp.k(kk, vv, tt, hw)),
        Eq.and.right(L4.is_miss(T.get(inl, kk)), M8.cv.fr(inl, tt), hfi), hsl, hwv,
        cv.miss(T.get(inl, kk), Eq.and.left(L4.is_miss(T.get(inl, kk)), M8.cv.fr(inl, tt), hfi)), then))))

# the array put: own reads its items, reversed from what the frame held, as
# the scanner's form of the items
def cv.arr.is(
  +items: List<&2, T.Val>,
  +ac2: List<&2, T.Val>,
  hh: {D1.own.rows(ac2) == List.reverse.go(&2, T.Val, L15.cv.raw(items), D1.own.rows([])) : List<&2, T.Val>}
) -> {L15.cv.own1(T.VArr{List.reverse(&2, T.Val, ac2)}) == L15.cv.raw1(T.VArr{items}) : T.Val}:
  Equal.cong(List<&2, T.Val>, T.Val, xs => T.VArr{xs}, D1.own.rows(List.reverse(&2, T.Val, ac2)), L15.cv.raw(items),
    Equal.trans(List<&2, T.Val>, D1.own.rows(List.reverse.go(&2, T.Val, ac2, [])),
      List.reverse.go(&2, T.Val, D1.own.rows(ac2), []), L15.cv.raw(items), cv.own.rev(ac2, []),
      Equal.trans(List<&2, T.Val>, List.reverse.go(&2, T.Val, D1.own.rows(ac2), []),
        List.reverse(&2, T.Val, List.reverse(&2, T.Val, L15.cv.raw(items))), L15.cv.raw(items),
        Equal.cong(List<&2, T.Val>, List<&2, T.Val>, ys => List.reverse.go(&2, T.Val, ys, []), D1.own.rows(ac2),
          List.reverse.go(&2, T.Val, L15.cv.raw(items), []), hh),
        cv.rev2(L15.cv.raw(items)))))

# the inline table put: own reads its pairs, sealed, as the scanner's form
def cv.inl.is(
  +rows: List<&2, T.Val>,
  +in2: List<&2, T.Val>,
  hh: {D1.own.rows(in2) == List.reverse.go(&2, T.Val, L15.cv.raw(rows), D1.own.rows([])) : List<&2, T.Val>},
  hsl: {T.inl.seal(in2) == in2 : List<&2, T.Val>}
) -> {L15.cv.own1(T.VInl{T.inl.seal(in2)}) == L15.cv.raw1(T.VInl{rows}) : T.Val}:
  Equal.cong(List<&2, T.Val>, T.Val, xs => T.VInl{xs}, D1.own.rows(T.inl.seal(in2)),
    List.reverse(&2, T.Val, L15.cv.raw(rows)),
    Equal.trans(List<&2, T.Val>, D1.own.rows(T.inl.seal(in2)), D1.own.rows(in2),
      List.reverse(&2, T.Val, L15.cv.raw(rows)),
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, ys => D1.own.rows(ys), T.inl.seal(in2), in2, hsl), hh))

# what the induction proves of a value's list: an array's items, an inline
# table's pairs, or nothing for a scalar
def cv.Sub(
  +vv: T.Val,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  match vv:
    case T.VArr{items}:
      cv.G(items, False{}, [], ps, he, rw, hs, he, [], bk, qk, sk, un, lf, ab, rest, PP)
    case T.VInl{rows}:
      cv.G(rows, True{}, [], ps, he, rw, hs, he, [], bk, qk, sk, un, lf, ab, rest, PP)
    case _:
      Unit

# The induction. A value's reader (cv.one) reads `[`, `{` or a scalar; an
# array's items and an inline table's pairs are read by the claim the
# induction proves of the list (cv.Sub), which cv.go proves of every list,
# value and shape together, as ezjson's pv: an item's or a pair's value by
# its reader, with the claim for its own list from the induction, and the
# items or pairs after it by the induction.

# the rows of an inline table read from LInl, as they are from LInlK
def cv.l2k.rows(
  +kk: String,
  +vv: T.Val,
  +tt: List<&2, T.Val>,
  +ps: List<&2, String>,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  +hwv: {D1.cv.wf(vv) == True{} : Bool}
) -> {T.doc.read(String.append(T.render.go(T.VPair{kk, vv} <> tt, ", ", False{}), SCon{'}', rest}), T.MScan{T.St{"",
  rw, hs, he, [], [], T.LInl{}, bk, qk, T.CInl{[], ps, he} <> sk, T.HNone{}, un, lf, ab, False{}}})
  == T.doc.read(String.append(T.render.go(T.VPair{kk, vv} <> tt, ", ", False{}), SCon{'}', rest}),
  T.MScan{cv.ik([], ps, he, rw, hs, bk, qk, sk, un, lf, ab)}) : T.Doc}:
  +xs = {String.append(T.render.go(T.VPair{kk, vv} <> tt, ", ", False{}), SCon{'}', rest}) : String}
  +ys = {String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(vv, cv.tl(tt, '}', rest))}}}) : String}
  +exy = {cv.ptx(kk, vv, tt, '}', rest, hwv) : {xs == ys : String}}
  %Equal.sym(String, xs, ys, exy) : {T.doc.read(_, T.MScan{T.St{"", rw, hs, he, [], [], T.LInl{}, bk, qk, T.CInl{[], ps,
    he} <> sk, T.HNone{}, un,
    lf, ab, False{}}}) == T.doc.read(_, T.MScan{cv.ik([], ps, he, rw, hs, bk, qk, sk, un, lf, ab)}) : T.Doc}
  cv.l2k(ys, rw, hs, he, bk, qk, T.CInl{[], ps, he} <> sk, un, lf, ab, cv.kx(kk, SCon{' ', SCon{'=', SCon{' ',
    D1.cv.tx(vv, cv.tl(tt, '}', rest))}}}))

# a value in a value position, once the claim for its list is in hand
def cv.one(
  vv: T.Val,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  sub: cv.Sub(vv, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP),
  +hw: {D1.cv.wf(vv) == True{} : Bool},
  hs1: {D1.cv.short1(vv) == True{} : Bool}
) -> cv.Rd(vv, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP):
  match vv:
    case T.VArr{+items}:
      hn => ih => pp.step(PP, T.doc.read(D1.cv.tx(T.VArr{items}, rest), T.MScan{cv.vp(rw, hs, he, ps, bk, qk, sk, un,
        lf, ab)}), T.doc.read(String.append(T.render.go(items, ", ", False{}), SCon{']', rest}), T.MScan{cv.ar([], ps,
        he, rw, hs, he, [], bk, qk, sk, un, lf, ab)}), {==},
        sub(hw, hs1, hn, +ac2 => b2 => q2 => u2 => l2 => hh => ih(T.VArr{List.reverse(&2, T.Val, ac2)}, b2, q2, u2, l2,
          cv.arr.is(items, ac2, hh))))
    case T.VInl{rows}:
      match rows:
        case []:
          _hn => ih => pp.step(PP, T.doc.read(D1.cv.tx(T.VInl{[]}, rest), T.MScan{cv.vp(rw, hs, he, ps, bk, qk, sk,
            un, lf, ab)}), T.doc.read(rest, T.MScan{cv.put(sk, T.VInl{T.inl.seal([])}, rw, hs, he, ps, bk, qk, un,
            lf, ab)}),
            Equal.cong(T.St, T.Doc, st => T.doc.read(rest, T.MScan{st}),
              T.read.once2(cv.put(sk, T.VInl{T.inl.seal([])}, rw, hs, he, ps, bk, qk, un, lf, ab)),
              cv.put(sk, T.VInl{T.inl.seal([])}, rw, hs, he, ps, bk, qk, un, lf, ab),
              Equal.sym(T.St, cv.put(sk, T.VInl{T.inl.seal([])}, rw, hs, he, ps, bk, qk, un, lf, ab),
                T.read.once2(cv.put(sk, T.VInl{T.inl.seal([])}, rw, hs, he, ps, bk, qk, un, lf, ab)),
                M9.tk.once(sk, T.VInl{T.inl.seal([])}, "", rw, hs, he, ps, bk, qk, un, lf, ab, False{}))),
            ih(T.VInl{T.inl.seal([])}, bk, qk, un, lf, {==}))
        case T.VStr{raa} <> rt:
          Eq.bit.absurd(&1, cv.Rd(T.VInl{T.VStr{raa} <> rt}, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP), hw)
        case T.VSpan{raa, rbb} <> rt:
          Eq.bit.absurd(&1, cv.Rd(T.VInl{T.VSpan{raa, rbb} <> rt}, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP),
            hw)
        case T.VInt{raa, rbb} <> rt:
          Eq.bit.absurd(&1, cv.Rd(T.VInl{T.VInt{raa, rbb} <> rt}, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP), hw)
        case T.VFlo{raa, rbb} <> rt:
          Eq.bit.absurd(&1, cv.Rd(T.VInl{T.VFlo{raa, rbb} <> rt}, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP), hw)
        case T.VBool{raa} <> rt:
          Eq.bit.absurd(&1, cv.Rd(T.VInl{T.VBool{raa} <> rt}, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP), hw)
        case T.VWhen{raa} <> rt:
          Eq.bit.absurd(&1, cv.Rd(T.VInl{T.VWhen{raa} <> rt}, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP), hw)
        case T.VArr{raa} <> rt:
          Eq.bit.absurd(&1, cv.Rd(T.VInl{T.VArr{raa} <> rt}, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP), hw)
        case T.VInl{raa} <> rt:
          Eq.bit.absurd(&1, cv.Rd(T.VInl{T.VInl{raa} <> rt}, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP), hw)
        case T.VHead{raa, rbb} <> rt:
          Eq.bit.absurd(&1, cv.Rd(T.VInl{T.VHead{raa, rbb} <> rt}, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP),
            hw)
        case T.VAot{raa, rbb} <> rt:
          Eq.bit.absurd(&1, cv.Rd(T.VInl{T.VAot{raa, rbb} <> rt}, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP), hw)
        case T.VAots{raa, rbb} <> rt:
          Eq.bit.absurd(&1, cv.Rd(T.VInl{T.VAots{raa, rbb} <> rt}, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP),
            hw)
        case T.VPair{+kk, +v1} <> +rt:
          +hwv = {cv.wfp.v(kk, v1, rt, hw) : {D1.cv.wf(v1) == True{} : Bool}}
          hn => ih => pp.step(PP, T.doc.read(D1.cv.tx(T.VInl{T.VPair{kk, v1} <> rt}, rest), T.MScan{cv.vp(rw, hs,
            he, ps, bk, qk, sk, un, lf, ab)}), T.doc.read(String.append(T.render.go(T.VPair{kk, v1} <> rt, ", ",
            False{}), SCon{'}', rest}), T.MScan{cv.ik([], ps, he, rw, hs, bk, qk, sk, un, lf, ab)}),
            cv.l2k.rows(kk, v1, rt, ps, rw, hs, he, bk, qk, sk, un, lf, ab, rest, hwv),
            sub({==}, hw, hs1, hn, M13.cv.fr.nil(T.VPair{kk, v1} <> rt), {==},
              +in2 => b2 => q2 => u2 => l2 => hh => hsl => ih(T.VInl{T.inl.seal(in2)}, b2, q2, u2, l2,
                cv.inl.is(T.VPair{kk, v1} <> rt, in2, hh, hsl))))
    case T.VStr{+aa}:
      hn => ih => cv.atom(T.VStr{aa}, hw, hs1, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP, hn, ih)
    case T.VSpan{+aa, +bb}:
      hn => ih => cv.atom(T.VSpan{aa, bb}, hw, hs1, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP, hn, ih)
    case T.VInt{+aa, +bb}:
      hn => ih => cv.atom(T.VInt{aa, bb}, hw, hs1, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP, hn, ih)
    case T.VFlo{+aa, +bb}:
      hn => ih => cv.atom(T.VFlo{aa, bb}, hw, hs1, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP, hn, ih)
    case T.VBool{+aa}:
      hn => ih => cv.atom(T.VBool{aa}, hw, hs1, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP, hn, ih)
    case T.VWhen{+aa}:
      hn => ih => cv.atom(T.VWhen{aa}, hw, hs1, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP, hn, ih)
    case T.VHead{aa, bb}:
      Eq.bit.absurd(&1, cv.Rd(T.VHead{aa, bb}, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP), hw)
    case T.VAot{aa, bb}:
      Eq.bit.absurd(&1, cv.Rd(T.VAot{aa, bb}, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP), hw)
    case T.VAots{aa, bb}:
      Eq.bit.absurd(&1, cv.Rd(T.VAots{aa, bb}, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP), hw)
    case T.VPair{aa, bb}:
      Eq.bit.absurd(&1, cv.Rd(T.VPair{aa, bb}, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP), hw)

# an array's item and what follows it, from what wf.go and the lengths say
# of the whole list
def cv.itm(
  +ii: T.Val,
  +tt: List<&2, T.Val>,
  +acc: List<&2, T.Val>,
  +ps0: List<&2, String>,
  +he0: List<&2, String>,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  sub: cv.Sub(ii, rw, hs, he, ps, T.LVal{}, qk, T.CArr{acc, ps0, he0} <> sk, un, lf, ab, cv.tl(tt, ']', rest), PP),
  ih_t: cv.IhA(tt, acc, ps0, he0, rw, hs, sk, ab, rest, PP),
  +hw: {T.wf.go(ii <> tt, T.WfItems{}) == True{} : Bool},
  +hs2: {D1.cv.shorts(ii <> tt) == True{} : Bool},
  hn: {L15.cv.end(rest) == True{} : Bool},
  then: cv.ThenA(ii <> tt, acc, ps0, he0, rw, hs, sk, ab, rest, PP)
) -> PP(T.doc.read(String.append(T.render.go(ii <> tt, ", ", False{}), SCon{']', rest}), T.MScan{cv.ar(acc, ps0, he0,
  rw, hs, he, ps, bk, qk, sk, un, lf, ab)})):
  +hwi = {cv.wfi.hd(ii, tt, hw) : {D1.cv.wf(ii) == True{} : Bool}}
  +hsp = {Equal.trans(Bool, Bool.and(D1.cv.short1(ii), D1.cv.shorts(tt)), D1.cv.shorts(ii <> tt), True{},
    Equal.sym(Bool, D1.cv.shorts(ii <> tt), Bool.and(D1.cv.short1(ii), D1.cv.shorts(tt)), cv.sh.item(ii, tt,
    hwi)), hs2) : {Bool.and(D1.cv.short1(ii), D1.cv.shorts(tt)) == True{} : Bool}}
  cv.item(ii, tt, acc, ps0, he0, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP,
    cv.one(ii, rw, hs, he, ps, T.LVal{}, qk, T.CArr{acc, ps0, he0} <> sk, un, lf, ab, cv.tl(tt, ']', rest), PP, sub,
      hwi,
      Eq.and.left(D1.cv.short1(ii), D1.cv.shorts(tt), hsp)),
    ih_t, hwi, cv.wfi.tl(ii, tt, hw), Eq.and.right(D1.cv.short1(ii), D1.cv.shorts(tt), hsp), hn, then)

# every list, as an array's items (rows false) or an inline table's pairs
# (rows true)
def cv.go(
  vs: List<&2, T.Val>,
  rows: Bool,
  +acc: List<&2, T.Val>,
  +ps0: List<&2, String>,
  +he0: List<&2, String>,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type
) -> cv.G(vs, rows, acc, ps0, he0, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP):
  match vs:
    case []:
      match rows:
        case False{}:
          _hw => _hs => _hn => then => cv.close0(acc, ps0, he0, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP, then)
        case True{}:
          hne => _hw => _hs => _hn => _hfi => _hsl => _then => Eq.bit.absurd2(&1, PP(T.doc.read(String.append(
            T.render.go([], ", ", False{}), SCon{'}', rest}), T.MScan{cv.ik(acc, ps0, he0, rw, hs, bk, qk, sk, un, lf,
            ab)})), hne)
    case T.VStr{+aa} <> +tt:
      match rows:
        case False{}:
          +hw => +hs2 => hn => then => cv.itm(T.VStr{aa}, tt, acc, ps0, he0, rw, hs, he, ps, bk, qk, sk, un, lf, ab,
            rest, PP, Unit{}, +v2 => b2 => q2 => u2 => l2 => cv.go(tt, False{}, v2 <> acc, ps0, he0, rw, hs, he0, ps0,
            b2, q2, sk, u2, l2, ab, rest, PP), hw, hs2, hn, then)
        case True{}:
          _hne => hw => _hs => _hn => _hfi => _hsl => _then => Eq.bit.absurd(&1,
            PP(T.doc.read(String.append(T.render.go(T.VStr{aa} <> tt, ", ", False{}), SCon{'}', rest}),
            T.MScan{cv.ik(acc, ps0, he0, rw, hs, bk, qk, sk, un, lf, ab)})), hw)
    case T.VSpan{+aa, +bb} <> +tt:
      match rows:
        case False{}:
          +hw => +hs2 => hn => then => cv.itm(T.VSpan{aa, bb}, tt, acc, ps0, he0, rw, hs, he, ps, bk, qk, sk, un, lf,
            ab, rest, PP, Unit{}, +v2 => b2 => q2 => u2 => l2 => cv.go(tt, False{}, v2 <> acc, ps0, he0, rw, hs, he0,
            ps0, b2, q2, sk, u2, l2, ab, rest, PP), hw, hs2, hn, then)
        case True{}:
          _hne => hw => _hs => _hn => _hfi => _hsl => _then => Eq.bit.absurd(&1,
            PP(T.doc.read(String.append(T.render.go(T.VSpan{aa, bb} <> tt, ", ", False{}), SCon{'}', rest}),
            T.MScan{cv.ik(acc, ps0, he0, rw, hs, bk, qk, sk, un, lf, ab)})), hw)
    case T.VInt{+aa, +bb} <> +tt:
      match rows:
        case False{}:
          +hw => +hs2 => hn => then => cv.itm(T.VInt{aa, bb}, tt, acc, ps0, he0, rw, hs, he, ps, bk, qk, sk, un, lf, ab,
            rest, PP, Unit{}, +v2 => b2 => q2 => u2 => l2 => cv.go(tt, False{}, v2 <> acc, ps0, he0, rw, hs, he0, ps0,
            b2, q2, sk, u2, l2, ab, rest, PP), hw, hs2, hn, then)
        case True{}:
          _hne => hw => _hs => _hn => _hfi => _hsl => _then => Eq.bit.absurd(&1,
            PP(T.doc.read(String.append(T.render.go(T.VInt{aa, bb} <> tt, ", ", False{}), SCon{'}', rest}),
            T.MScan{cv.ik(acc, ps0, he0, rw, hs, bk, qk, sk, un, lf, ab)})), hw)
    case T.VFlo{+aa, +bb} <> +tt:
      match rows:
        case False{}:
          +hw => +hs2 => hn => then => cv.itm(T.VFlo{aa, bb}, tt, acc, ps0, he0, rw, hs, he, ps, bk, qk, sk, un, lf, ab,
            rest, PP, Unit{}, +v2 => b2 => q2 => u2 => l2 => cv.go(tt, False{}, v2 <> acc, ps0, he0, rw, hs, he0, ps0,
            b2, q2, sk, u2, l2, ab, rest, PP), hw, hs2, hn, then)
        case True{}:
          _hne => hw => _hs => _hn => _hfi => _hsl => _then => Eq.bit.absurd(&1,
            PP(T.doc.read(String.append(T.render.go(T.VFlo{aa, bb} <> tt, ", ", False{}), SCon{'}', rest}),
            T.MScan{cv.ik(acc, ps0, he0, rw, hs, bk, qk, sk, un, lf, ab)})), hw)
    case T.VBool{+aa} <> +tt:
      match rows:
        case False{}:
          +hw => +hs2 => hn => then => cv.itm(T.VBool{aa}, tt, acc, ps0, he0, rw, hs, he, ps, bk, qk, sk, un, lf, ab,
            rest, PP, Unit{}, +v2 => b2 => q2 => u2 => l2 => cv.go(tt, False{}, v2 <> acc, ps0, he0, rw, hs, he0, ps0,
            b2, q2, sk, u2, l2, ab, rest, PP), hw, hs2, hn, then)
        case True{}:
          _hne => hw => _hs => _hn => _hfi => _hsl => _then => Eq.bit.absurd(&1,
            PP(T.doc.read(String.append(T.render.go(T.VBool{aa} <> tt, ", ", False{}), SCon{'}', rest}),
            T.MScan{cv.ik(acc, ps0, he0, rw, hs, bk, qk, sk, un, lf, ab)})), hw)
    case T.VWhen{+aa} <> +tt:
      match rows:
        case False{}:
          +hw => +hs2 => hn => then => cv.itm(T.VWhen{aa}, tt, acc, ps0, he0, rw, hs, he, ps, bk, qk, sk, un, lf, ab,
            rest, PP, Unit{}, +v2 => b2 => q2 => u2 => l2 => cv.go(tt, False{}, v2 <> acc, ps0, he0, rw, hs, he0, ps0,
            b2, q2, sk, u2, l2, ab, rest, PP), hw, hs2, hn, then)
        case True{}:
          _hne => hw => _hs => _hn => _hfi => _hsl => _then => Eq.bit.absurd(&1,
            PP(T.doc.read(String.append(T.render.go(T.VWhen{aa} <> tt, ", ", False{}), SCon{'}', rest}),
            T.MScan{cv.ik(acc, ps0, he0, rw, hs, bk, qk, sk, un, lf, ab)})), hw)
    case T.VArr{+aa} <> +tt:
      match rows:
        case False{}:
          +hw => +hs2 => hn => then => cv.itm(T.VArr{aa}, tt, acc, ps0, he0, rw, hs, he, ps, bk, qk, sk, un, lf, ab,
            rest, PP, cv.go(aa, False{}, [], ps, he, rw, hs, he, [], T.LVal{}, qk, T.CArr{acc, ps0, he0} <> sk, un, lf,
            ab, cv.tl(tt, ']', rest), PP), +v2 => b2 => q2 => u2 => l2 => cv.go(tt, False{}, v2 <> acc, ps0, he0, rw,
            hs, he0, ps0, b2, q2, sk, u2, l2, ab, rest, PP), hw, hs2, hn, then)
        case True{}:
          _hne => hw => _hs => _hn => _hfi => _hsl => _then => Eq.bit.absurd(&1,
            PP(T.doc.read(String.append(T.render.go(T.VArr{aa} <> tt, ", ", False{}), SCon{'}', rest}),
            T.MScan{cv.ik(acc, ps0, he0, rw, hs, bk, qk, sk, un, lf, ab)})), hw)
    case T.VInl{+aa} <> +tt:
      match rows:
        case False{}:
          +hw => +hs2 => hn => then => cv.itm(T.VInl{aa}, tt, acc, ps0, he0, rw, hs, he, ps, bk, qk, sk, un, lf, ab,
            rest, PP, cv.go(aa, True{}, [], ps, he, rw, hs, he, [], T.LVal{}, qk, T.CArr{acc, ps0, he0} <> sk, un, lf,
            ab, cv.tl(tt, ']', rest), PP), +v2 => b2 => q2 => u2 => l2 => cv.go(tt, False{}, v2 <> acc, ps0, he0, rw,
            hs, he0, ps0, b2, q2, sk, u2, l2, ab, rest, PP), hw, hs2, hn, then)
        case True{}:
          _hne => hw => _hs => _hn => _hfi => _hsl => _then => Eq.bit.absurd(&1,
            PP(T.doc.read(String.append(T.render.go(T.VInl{aa} <> tt, ", ", False{}), SCon{'}', rest}),
            T.MScan{cv.ik(acc, ps0, he0, rw, hs, bk, qk, sk, un, lf, ab)})), hw)
    case T.VHead{+aa, +bb} <> +tt:
      match rows:
        case False{}:
          +hw => +hs2 => hn => then => cv.itm(T.VHead{aa, bb}, tt, acc, ps0, he0, rw, hs, he, ps, bk, qk, sk, un, lf,
            ab, rest, PP, Unit{}, +v2 => b2 => q2 => u2 => l2 => cv.go(tt, False{}, v2 <> acc, ps0, he0, rw, hs, he0,
            ps0, b2, q2, sk, u2, l2, ab, rest, PP), hw, hs2, hn, then)
        case True{}:
          _hne => hw => _hs => _hn => _hfi => _hsl => _then => Eq.bit.absurd(&1,
            PP(T.doc.read(String.append(T.render.go(T.VHead{aa, bb} <> tt, ", ", False{}), SCon{'}', rest}),
            T.MScan{cv.ik(acc, ps0, he0, rw, hs, bk, qk, sk, un, lf, ab)})), hw)
    case T.VAot{+aa, +bb} <> +tt:
      match rows:
        case False{}:
          +hw => +hs2 => hn => then => cv.itm(T.VAot{aa, bb}, tt, acc, ps0, he0, rw, hs, he, ps, bk, qk, sk, un, lf, ab,
            rest, PP, Unit{}, +v2 => b2 => q2 => u2 => l2 => cv.go(tt, False{}, v2 <> acc, ps0, he0, rw, hs, he0, ps0,
            b2, q2, sk, u2, l2, ab, rest, PP), hw, hs2, hn, then)
        case True{}:
          _hne => hw => _hs => _hn => _hfi => _hsl => _then => Eq.bit.absurd(&1,
            PP(T.doc.read(String.append(T.render.go(T.VAot{aa, bb} <> tt, ", ", False{}), SCon{'}', rest}),
            T.MScan{cv.ik(acc, ps0, he0, rw, hs, bk, qk, sk, un, lf, ab)})), hw)
    case T.VAots{+aa, +bb} <> +tt:
      match rows:
        case False{}:
          +hw => +hs2 => hn => then => cv.itm(T.VAots{aa, bb}, tt, acc, ps0, he0, rw, hs, he, ps, bk, qk, sk, un, lf,
            ab, rest, PP, Unit{}, +v2 => b2 => q2 => u2 => l2 => cv.go(tt, False{}, v2 <> acc, ps0, he0, rw, hs, he0,
            ps0, b2, q2, sk, u2, l2, ab, rest, PP), hw, hs2, hn, then)
        case True{}:
          _hne => hw => _hs => _hn => _hfi => _hsl => _then => Eq.bit.absurd(&1,
            PP(T.doc.read(String.append(T.render.go(T.VAots{aa, bb} <> tt, ", ", False{}), SCon{'}', rest}),
            T.MScan{cv.ik(acc, ps0, he0, rw, hs, bk, qk, sk, un, lf, ab)})), hw)
    case T.VPair{+kk, T.VStr{+aa}} <> +tt:
      match rows:
        case False{}:
          +hw => +hs2 => hn => then => cv.itm(T.VPair{kk, T.VStr{aa}}, tt, acc, ps0, he0, rw, hs, he, ps, bk, qk, sk,
            un, lf, ab, rest, PP, Unit{}, +v2 => b2 => q2 => u2 => l2 => cv.go(tt, False{}, v2 <> acc, ps0, he0, rw, hs,
            he0, ps0, b2, q2, sk, u2, l2, ab, rest, PP), hw, hs2, hn, then)
        case True{}:
          _hne => +hw => +hs2 => hn => hfi => hsl => then => cv.pair(kk, T.VStr{aa}, tt, acc, ps0, he0, rw, hs, bk, qk,
            sk, un, lf, ab, rest, PP, +b2 => +q2 => +u2 => +l2 => hwv => hsv => cv.one(T.VStr{aa}, rw, hs, he0, [kk],
            b2, q2, T.CInl{acc, ps0, he0} <> sk, u2, l2, ab, cv.tl(tt, '}', rest), PP, Unit{}, hwv, hsv),
            +v2 => b2 => q2 => u2 => l2 => cv.go(tt, True{}, T.VPair{kk, v2} <> acc, ps0, he0, rw, hs, he0, [], b2, q2,
            sk, u2, l2, ab, rest, PP), hw, hs2, hn, hfi, hsl, then)
    case T.VPair{+kk, T.VSpan{+aa, +bb}} <> +tt:
      match rows:
        case False{}:
          +hw => +hs2 => hn => then => cv.itm(T.VPair{kk, T.VSpan{aa, bb}}, tt, acc, ps0, he0, rw, hs, he, ps, bk, qk,
            sk, un, lf, ab, rest, PP, Unit{}, +v2 => b2 => q2 => u2 => l2 => cv.go(tt, False{}, v2 <> acc, ps0, he0, rw,
            hs, he0, ps0, b2, q2, sk, u2, l2, ab, rest, PP), hw, hs2, hn, then)
        case True{}:
          _hne => +hw => +hs2 => hn => hfi => hsl => then => cv.pair(kk, T.VSpan{aa, bb}, tt, acc, ps0, he0, rw, hs, bk,
            qk, sk, un, lf, ab, rest, PP, +b2 => +q2 => +u2 => +l2 => hwv => hsv => cv.one(T.VSpan{aa, bb}, rw, hs, he0,
            [kk], b2, q2, T.CInl{acc, ps0, he0} <> sk, u2, l2, ab, cv.tl(tt, '}', rest), PP, Unit{}, hwv, hsv),
            +v2 => b2 => q2 => u2 => l2 => cv.go(tt, True{}, T.VPair{kk, v2} <> acc, ps0, he0, rw, hs, he0, [], b2, q2,
            sk, u2, l2, ab, rest, PP), hw, hs2, hn, hfi, hsl, then)
    case T.VPair{+kk, T.VInt{+aa, +bb}} <> +tt:
      match rows:
        case False{}:
          +hw => +hs2 => hn => then => cv.itm(T.VPair{kk, T.VInt{aa, bb}}, tt, acc, ps0, he0, rw, hs, he, ps, bk, qk,
            sk, un, lf, ab, rest, PP, Unit{}, +v2 => b2 => q2 => u2 => l2 => cv.go(tt, False{}, v2 <> acc, ps0, he0, rw,
            hs, he0, ps0, b2, q2, sk, u2, l2, ab, rest, PP), hw, hs2, hn, then)
        case True{}:
          _hne => +hw => +hs2 => hn => hfi => hsl => then => cv.pair(kk, T.VInt{aa, bb}, tt, acc, ps0, he0, rw, hs, bk,
            qk, sk, un, lf, ab, rest, PP, +b2 => +q2 => +u2 => +l2 => hwv => hsv => cv.one(T.VInt{aa, bb}, rw, hs, he0,
            [kk], b2, q2, T.CInl{acc, ps0, he0} <> sk, u2, l2, ab, cv.tl(tt, '}', rest), PP, Unit{}, hwv, hsv),
            +v2 => b2 => q2 => u2 => l2 => cv.go(tt, True{}, T.VPair{kk, v2} <> acc, ps0, he0, rw, hs, he0, [], b2, q2,
            sk, u2, l2, ab, rest, PP), hw, hs2, hn, hfi, hsl, then)
    case T.VPair{+kk, T.VFlo{+aa, +bb}} <> +tt:
      match rows:
        case False{}:
          +hw => +hs2 => hn => then => cv.itm(T.VPair{kk, T.VFlo{aa, bb}}, tt, acc, ps0, he0, rw, hs, he, ps, bk, qk,
            sk, un, lf, ab, rest, PP, Unit{}, +v2 => b2 => q2 => u2 => l2 => cv.go(tt, False{}, v2 <> acc, ps0, he0, rw,
            hs, he0, ps0, b2, q2, sk, u2, l2, ab, rest, PP), hw, hs2, hn, then)
        case True{}:
          _hne => +hw => +hs2 => hn => hfi => hsl => then => cv.pair(kk, T.VFlo{aa, bb}, tt, acc, ps0, he0, rw, hs, bk,
            qk, sk, un, lf, ab, rest, PP, +b2 => +q2 => +u2 => +l2 => hwv => hsv => cv.one(T.VFlo{aa, bb}, rw, hs, he0,
            [kk], b2, q2, T.CInl{acc, ps0, he0} <> sk, u2, l2, ab, cv.tl(tt, '}', rest), PP, Unit{}, hwv, hsv),
            +v2 => b2 => q2 => u2 => l2 => cv.go(tt, True{}, T.VPair{kk, v2} <> acc, ps0, he0, rw, hs, he0, [], b2, q2,
            sk, u2, l2, ab, rest, PP), hw, hs2, hn, hfi, hsl, then)
    case T.VPair{+kk, T.VBool{+aa}} <> +tt:
      match rows:
        case False{}:
          +hw => +hs2 => hn => then => cv.itm(T.VPair{kk, T.VBool{aa}}, tt, acc, ps0, he0, rw, hs, he, ps, bk, qk, sk,
            un, lf, ab, rest, PP, Unit{}, +v2 => b2 => q2 => u2 => l2 => cv.go(tt, False{}, v2 <> acc, ps0, he0, rw, hs,
            he0, ps0, b2, q2, sk, u2, l2, ab, rest, PP), hw, hs2, hn, then)
        case True{}:
          _hne => +hw => +hs2 => hn => hfi => hsl => then => cv.pair(kk, T.VBool{aa}, tt, acc, ps0, he0, rw, hs, bk, qk,
            sk, un, lf, ab, rest, PP, +b2 => +q2 => +u2 => +l2 => hwv => hsv => cv.one(T.VBool{aa}, rw, hs, he0, [kk],
            b2, q2, T.CInl{acc, ps0, he0} <> sk, u2, l2, ab, cv.tl(tt, '}', rest), PP, Unit{}, hwv, hsv),
            +v2 => b2 => q2 => u2 => l2 => cv.go(tt, True{}, T.VPair{kk, v2} <> acc, ps0, he0, rw, hs, he0, [], b2, q2,
            sk, u2, l2, ab, rest, PP), hw, hs2, hn, hfi, hsl, then)
    case T.VPair{+kk, T.VWhen{+aa}} <> +tt:
      match rows:
        case False{}:
          +hw => +hs2 => hn => then => cv.itm(T.VPair{kk, T.VWhen{aa}}, tt, acc, ps0, he0, rw, hs, he, ps, bk, qk, sk,
            un, lf, ab, rest, PP, Unit{}, +v2 => b2 => q2 => u2 => l2 => cv.go(tt, False{}, v2 <> acc, ps0, he0, rw, hs,
            he0, ps0, b2, q2, sk, u2, l2, ab, rest, PP), hw, hs2, hn, then)
        case True{}:
          _hne => +hw => +hs2 => hn => hfi => hsl => then => cv.pair(kk, T.VWhen{aa}, tt, acc, ps0, he0, rw, hs, bk, qk,
            sk, un, lf, ab, rest, PP, +b2 => +q2 => +u2 => +l2 => hwv => hsv => cv.one(T.VWhen{aa}, rw, hs, he0, [kk],
            b2, q2, T.CInl{acc, ps0, he0} <> sk, u2, l2, ab, cv.tl(tt, '}', rest), PP, Unit{}, hwv, hsv),
            +v2 => b2 => q2 => u2 => l2 => cv.go(tt, True{}, T.VPair{kk, v2} <> acc, ps0, he0, rw, hs, he0, [], b2, q2,
            sk, u2, l2, ab, rest, PP), hw, hs2, hn, hfi, hsl, then)
    case T.VPair{+kk, T.VArr{+aa}} <> +tt:
      match rows:
        case False{}:
          +hw => +hs2 => hn => then => cv.itm(T.VPair{kk, T.VArr{aa}}, tt, acc, ps0, he0, rw, hs, he, ps, bk, qk, sk,
            un, lf, ab, rest, PP, Unit{}, +v2 => b2 => q2 => u2 => l2 => cv.go(tt, False{}, v2 <> acc, ps0, he0, rw, hs,
            he0, ps0, b2, q2, sk, u2, l2, ab, rest, PP), hw, hs2, hn, then)
        case True{}:
          _hne => +hw => +hs2 => hn => hfi => hsl => then => cv.pair(kk, T.VArr{aa}, tt, acc, ps0, he0, rw, hs, bk, qk,
            sk, un, lf, ab, rest, PP, +b2 => +q2 => +u2 => +l2 => hwv => hsv => cv.one(T.VArr{aa}, rw, hs, he0, [kk],
            b2, q2, T.CInl{acc, ps0, he0} <> sk, u2, l2, ab, cv.tl(tt, '}', rest), PP, cv.go(aa, False{}, [], [kk], he0,
            rw, hs, he0, [], b2, q2, T.CInl{acc, ps0, he0} <> sk, u2, l2, ab, cv.tl(tt, '}', rest), PP), hwv, hsv),
            +v2 => b2 => q2 => u2 => l2 => cv.go(tt, True{}, T.VPair{kk, v2} <> acc, ps0, he0, rw, hs, he0, [], b2, q2,
            sk, u2, l2, ab, rest, PP), hw, hs2, hn, hfi, hsl, then)
    case T.VPair{+kk, T.VInl{+aa}} <> +tt:
      match rows:
        case False{}:
          +hw => +hs2 => hn => then => cv.itm(T.VPair{kk, T.VInl{aa}}, tt, acc, ps0, he0, rw, hs, he, ps, bk, qk, sk,
            un, lf, ab, rest, PP, Unit{}, +v2 => b2 => q2 => u2 => l2 => cv.go(tt, False{}, v2 <> acc, ps0, he0, rw, hs,
            he0, ps0, b2, q2, sk, u2, l2, ab, rest, PP), hw, hs2, hn, then)
        case True{}:
          _hne => +hw => +hs2 => hn => hfi => hsl => then => cv.pair(kk, T.VInl{aa}, tt, acc, ps0, he0, rw, hs, bk, qk,
            sk, un, lf, ab, rest, PP, +b2 => +q2 => +u2 => +l2 => hwv => hsv => cv.one(T.VInl{aa}, rw, hs, he0, [kk],
            b2, q2, T.CInl{acc, ps0, he0} <> sk, u2, l2, ab, cv.tl(tt, '}', rest), PP, cv.go(aa, True{}, [], [kk], he0,
            rw, hs, he0, [], b2, q2, T.CInl{acc, ps0, he0} <> sk, u2, l2, ab, cv.tl(tt, '}', rest), PP), hwv, hsv),
            +v2 => b2 => q2 => u2 => l2 => cv.go(tt, True{}, T.VPair{kk, v2} <> acc, ps0, he0, rw, hs, he0, [], b2, q2,
            sk, u2, l2, ab, rest, PP), hw, hs2, hn, hfi, hsl, then)
    case T.VPair{+kk, T.VHead{+aa, +bb}} <> +tt:
      match rows:
        case False{}:
          +hw => +hs2 => hn => then => cv.itm(T.VPair{kk, T.VHead{aa, bb}}, tt, acc, ps0, he0, rw, hs, he, ps, bk, qk,
            sk, un, lf, ab, rest, PP, Unit{}, +v2 => b2 => q2 => u2 => l2 => cv.go(tt, False{}, v2 <> acc, ps0, he0, rw,
            hs, he0, ps0, b2, q2, sk, u2, l2, ab, rest, PP), hw, hs2, hn, then)
        case True{}:
          _hne => +hw => +hs2 => hn => hfi => hsl => then => cv.pair(kk, T.VHead{aa, bb}, tt, acc, ps0, he0, rw, hs, bk,
            qk, sk, un, lf, ab, rest, PP, +b2 => +q2 => +u2 => +l2 => hwv => hsv => cv.one(T.VHead{aa, bb}, rw, hs, he0,
            [kk], b2, q2, T.CInl{acc, ps0, he0} <> sk, u2, l2, ab, cv.tl(tt, '}', rest), PP, Unit{}, hwv, hsv),
            +v2 => b2 => q2 => u2 => l2 => cv.go(tt, True{}, T.VPair{kk, v2} <> acc, ps0, he0, rw, hs, he0, [], b2, q2,
            sk, u2, l2, ab, rest, PP), hw, hs2, hn, hfi, hsl, then)
    case T.VPair{+kk, T.VAot{+aa, +bb}} <> +tt:
      match rows:
        case False{}:
          +hw => +hs2 => hn => then => cv.itm(T.VPair{kk, T.VAot{aa, bb}}, tt, acc, ps0, he0, rw, hs, he, ps, bk, qk,
            sk, un, lf, ab, rest, PP, Unit{}, +v2 => b2 => q2 => u2 => l2 => cv.go(tt, False{}, v2 <> acc, ps0, he0, rw,
            hs, he0, ps0, b2, q2, sk, u2, l2, ab, rest, PP), hw, hs2, hn, then)
        case True{}:
          _hne => +hw => +hs2 => hn => hfi => hsl => then => cv.pair(kk, T.VAot{aa, bb}, tt, acc, ps0, he0, rw, hs, bk,
            qk, sk, un, lf, ab, rest, PP, +b2 => +q2 => +u2 => +l2 => hwv => hsv => cv.one(T.VAot{aa, bb}, rw, hs, he0,
            [kk], b2, q2, T.CInl{acc, ps0, he0} <> sk, u2, l2, ab, cv.tl(tt, '}', rest), PP, Unit{}, hwv, hsv),
            +v2 => b2 => q2 => u2 => l2 => cv.go(tt, True{}, T.VPair{kk, v2} <> acc, ps0, he0, rw, hs, he0, [], b2, q2,
            sk, u2, l2, ab, rest, PP), hw, hs2, hn, hfi, hsl, then)
    case T.VPair{+kk, T.VAots{+aa, +bb}} <> +tt:
      match rows:
        case False{}:
          +hw => +hs2 => hn => then => cv.itm(T.VPair{kk, T.VAots{aa, bb}}, tt, acc, ps0, he0, rw, hs, he, ps, bk, qk,
            sk, un, lf, ab, rest, PP, Unit{}, +v2 => b2 => q2 => u2 => l2 => cv.go(tt, False{}, v2 <> acc, ps0, he0, rw,
            hs, he0, ps0, b2, q2, sk, u2, l2, ab, rest, PP), hw, hs2, hn, then)
        case True{}:
          _hne => +hw => +hs2 => hn => hfi => hsl => then => cv.pair(kk, T.VAots{aa, bb}, tt, acc, ps0, he0, rw, hs, bk,
            qk, sk, un, lf, ab, rest, PP, +b2 => +q2 => +u2 => +l2 => hwv => hsv => cv.one(T.VAots{aa, bb}, rw, hs, he0,
            [kk], b2, q2, T.CInl{acc, ps0, he0} <> sk, u2, l2, ab, cv.tl(tt, '}', rest), PP, Unit{}, hwv, hsv),
            +v2 => b2 => q2 => u2 => l2 => cv.go(tt, True{}, T.VPair{kk, v2} <> acc, ps0, he0, rw, hs, he0, [], b2, q2,
            sk, u2, l2, ab, rest, PP), hw, hs2, hn, hfi, hsl, then)
    case T.VPair{+kk, T.VPair{+aa, +bb}} <> +tt:
      match rows:
        case False{}:
          +hw => +hs2 => hn => then => cv.itm(T.VPair{kk, T.VPair{aa, bb}}, tt, acc, ps0, he0, rw, hs, he, ps, bk, qk,
            sk, un, lf, ab, rest, PP, Unit{}, +v2 => b2 => q2 => u2 => l2 => cv.go(tt, False{}, v2 <> acc, ps0, he0, rw,
            hs, he0, ps0, b2, q2, sk, u2, l2, ab, rest, PP), hw, hs2, hn, then)
        case True{}:
          _hne => +hw => +hs2 => hn => hfi => hsl => then => cv.pair(kk, T.VPair{aa, bb}, tt, acc, ps0, he0, rw, hs, bk,
            qk, sk, un, lf, ab, rest, PP, +b2 => +q2 => +u2 => +l2 => hwv => hsv => cv.one(T.VPair{aa, bb}, rw, hs, he0,
            [kk], b2, q2, T.CInl{acc, ps0, he0} <> sk, u2, l2, ab, cv.tl(tt, '}', rest), PP, Unit{}, hwv, hsv),
            +v2 => b2 => q2 => u2 => l2 => cv.go(tt, True{}, T.VPair{kk, v2} <> acc, ps0, he0, rw, hs, he0, [], b2, q2,
            sk, u2, l2, ab, rest, PP), hw, hs2, hn, hfi, hsl, then)

# a value in a value position: its reader, with the claim for its list
def cv.val(
  vv: T.Val,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  hw: {D1.cv.wf(vv) == True{} : Bool},
  hs1: {D1.cv.short1(vv) == True{} : Bool}
) -> cv.Rd(vv, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP):
  match vv:
    case T.VStr{+aa}:
      cv.one(T.VStr{aa}, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP, Unit{}, hw, hs1)
    case T.VSpan{+aa, +bb}:
      cv.one(T.VSpan{aa, bb}, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP, Unit{}, hw, hs1)
    case T.VInt{+aa, +bb}:
      cv.one(T.VInt{aa, bb}, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP, Unit{}, hw, hs1)
    case T.VFlo{+aa, +bb}:
      cv.one(T.VFlo{aa, bb}, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP, Unit{}, hw, hs1)
    case T.VBool{+aa}:
      cv.one(T.VBool{aa}, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP, Unit{}, hw, hs1)
    case T.VWhen{+aa}:
      cv.one(T.VWhen{aa}, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP, Unit{}, hw, hs1)
    case T.VArr{+aa}:
      cv.one(T.VArr{aa}, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP, cv.go(aa, False{}, [], ps, he, rw, hs, he,
        [], bk, qk, sk, un, lf, ab, rest, PP), hw, hs1)
    case T.VInl{+aa}:
      cv.one(T.VInl{aa}, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP, cv.go(aa, True{}, [], ps, he, rw, hs, he, [],
        bk, qk, sk, un, lf, ab, rest, PP), hw, hs1)
    case T.VHead{+aa, +bb}:
      cv.one(T.VHead{aa, bb}, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP, Unit{}, hw, hs1)
    case T.VAot{+aa, +bb}:
      cv.one(T.VAot{aa, bb}, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP, Unit{}, hw, hs1)
    case T.VAots{+aa, +bb}:
      cv.one(T.VAots{aa, bb}, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP, Unit{}, hw, hs1)
    case T.VPair{+aa, +bb}:
      cv.one(T.VPair{aa, bb}, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP, Unit{}, hw, hs1)

def L15.value_reads_back(v, hw, hl, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, hn, PP, ih):
  cv.val(v, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP, hw, hl)(hn, ih)

# The seal. rows.seal puts each table's rows back in the order they were
# written and leaves an array's items as they are. own reads a sealed list
# as the seal of what it reads (cv.osl); sealing the scanner's form of a
# well-formed value's list gives what own reads of the list (cv.sm); so a
# document of one pair of any value reads back as that pair, as own reads it.

# a list appended to another, read out
def cv.own.app(
  xs: List<&2, T.Val>,
  +ys: List<&2, T.Val>
) -> {D1.own.rows(List.append(&2, T.Val, xs, ys)) == List.append(&2, T.Val, D1.own.rows(xs), D1.own.rows(ys))
  : List<&2, T.Val>}:
  match xs:
    case []:
      {==}
    case +hh <> +tt:
      Equal.trans(List<&2, T.Val>, D1.own.rows(hh <> List.append(&2, T.Val, tt, ys)),
        L15.cv.own1(hh) <> D1.own.rows(List.append(&2, T.Val, tt, ys)),
        List.append(&2, T.Val, D1.own.rows(hh <> tt), D1.own.rows(ys)),
        cv.own.cons(hh, List.append(&2, T.Val, tt, ys)),
        Equal.trans(List<&2, T.Val>, L15.cv.own1(hh) <> D1.own.rows(List.append(&2, T.Val, tt, ys)),
          L15.cv.own1(hh) <> List.append(&2, T.Val, D1.own.rows(tt), D1.own.rows(ys)),
          List.append(&2, T.Val, D1.own.rows(hh <> tt), D1.own.rows(ys)),
          Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => L15.cv.own1(hh) <> zs,
            D1.own.rows(List.append(&2, T.Val, tt, ys)), List.append(&2, T.Val, D1.own.rows(tt), D1.own.rows(ys)),
            cv.own.app(tt, ys)),
          Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => List.append(&2, T.Val, zs, D1.own.rows(ys)),
            L15.cv.own1(hh) <> D1.own.rows(tt), D1.own.rows(hh <> tt),
            Equal.sym(List<&2, T.Val>, D1.own.rows(hh <> tt), L15.cv.own1(hh) <> D1.own.rows(tt),
              cv.own.cons(hh, tt)))))

# one value in front of a list: own reads the seal of the list as the seal of
# what it reads, once it does so for the list and for the value
def cv.osl.step(
  +xx: T.Val,
  +tt: List<&2, T.Val>,
  ex: {L15.cv.own1(D6.sealed(xx)) == D6.sealed(L15.cv.own1(xx)) : T.Val},
  ih: {D1.own.rows(T.rows.seal(tt)) == T.rows.seal(D1.own.rows(tt)) : List<&2, T.Val>}
) -> {D1.own.rows(T.rows.seal(xx <> tt)) == T.rows.seal(D1.own.rows(xx <> tt)) : List<&2, T.Val>}:
  Equal.trans(List<&2, T.Val>, D1.own.rows(T.rows.seal(xx <> tt)),
    D1.own.rows(List.append(&2, T.Val, T.rows.seal(tt), [D6.sealed(xx)])),
    T.rows.seal(D1.own.rows(xx <> tt)),
    Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => D1.own.rows(zs), T.rows.seal(xx <> tt),
      List.append(&2, T.Val, T.rows.seal(tt), [D6.sealed(xx)]), L11.seal_puts_newest_last(xx, tt)),
    Equal.trans(List<&2, T.Val>, D1.own.rows(List.append(&2, T.Val, T.rows.seal(tt), [D6.sealed(xx)])),
      List.append(&2, T.Val, D1.own.rows(T.rows.seal(tt)), D1.own.rows([D6.sealed(xx)])),
      T.rows.seal(D1.own.rows(xx <> tt)),
      cv.own.app(T.rows.seal(tt), [D6.sealed(xx)]),
      Equal.trans(List<&2, T.Val>,
        List.append(&2, T.Val, D1.own.rows(T.rows.seal(tt)), D1.own.rows([D6.sealed(xx)])),
        List.append(&2, T.Val, T.rows.seal(D1.own.rows(tt)), [D6.sealed(L15.cv.own1(xx))]),
        T.rows.seal(D1.own.rows(xx <> tt)),
        Equal.trans(List<&2, T.Val>,
          List.append(&2, T.Val, D1.own.rows(T.rows.seal(tt)), D1.own.rows([D6.sealed(xx)])),
          List.append(&2, T.Val, T.rows.seal(D1.own.rows(tt)), D1.own.rows([D6.sealed(xx)])),
          List.append(&2, T.Val, T.rows.seal(D1.own.rows(tt)), [D6.sealed(L15.cv.own1(xx))]),
          Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => List.append(&2, T.Val, zs, D1.own.rows([D6.sealed(
            xx)])), D1.own.rows(T.rows.seal(tt)), T.rows.seal(D1.own.rows(tt)), ih),
          Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => List.append(&2, T.Val, T.rows.seal(D1.own.rows(tt)), zs),
            D1.own.rows([D6.sealed(xx)]), [D6.sealed(L15.cv.own1(xx))],
            Equal.trans(List<&2, T.Val>, D1.own.rows([D6.sealed(xx)]), [L15.cv.own1(D6.sealed(xx))],
              [D6.sealed(L15.cv.own1(xx))], cv.own.cons(D6.sealed(xx), []),
              Equal.cong(T.Val, List<&2, T.Val>, yy => [yy], L15.cv.own1(D6.sealed(xx)),
                D6.sealed(L15.cv.own1(xx)), ex)))),
        Equal.trans(List<&2, T.Val>,
          List.append(&2, T.Val, T.rows.seal(D1.own.rows(tt)), [D6.sealed(L15.cv.own1(xx))]),
          T.rows.seal(L15.cv.own1(xx) <> D1.own.rows(tt)), T.rows.seal(D1.own.rows(xx <> tt)),
          Equal.sym(List<&2, T.Val>, T.rows.seal(L15.cv.own1(xx) <> D1.own.rows(tt)),
            List.append(&2, T.Val, T.rows.seal(D1.own.rows(tt)), [D6.sealed(L15.cv.own1(xx))]),
            L11.seal_puts_newest_last(L15.cv.own1(xx), D1.own.rows(tt))),
          Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => T.rows.seal(zs),
            L15.cv.own1(xx) <> D1.own.rows(tt), D1.own.rows(xx <> tt),
            Equal.sym(List<&2, T.Val>, D1.own.rows(xx <> tt), L15.cv.own1(xx) <> D1.own.rows(tt),
              cv.own.cons(xx, tt)))))))

# own reads a reversal of what it reads the seal of as the reversal of that
# seal
def cv.own.rs(
  +ss: List<&2, T.Val>,
  +s2: List<&2, T.Val>,
  hh: {D1.own.rows(ss) == s2 : List<&2, T.Val>}
) -> {D1.own.rows(List.reverse(&2, T.Val, ss)) == List.reverse(&2, T.Val, s2) : List<&2, T.Val>}:
  Equal.trans(List<&2, T.Val>, D1.own.rows(List.reverse.go(&2, T.Val, ss, [])),
    List.reverse.go(&2, T.Val, D1.own.rows(ss), []), List.reverse(&2, T.Val, s2), cv.own.rev(ss, []),
    Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => List.reverse.go(&2, T.Val, zs, []), D1.own.rows(ss), s2, hh))

# own reads the seal of every list as the seal of what it reads
def cv.osl(
  xs: List<&2, T.Val>
) -> {D1.own.rows(T.rows.seal(xs)) == T.rows.seal(D1.own.rows(xs)) : List<&2, T.Val>}:
  match xs:
    case []:
      {==}
    case T.VPair{+nn, T.VHead{+pp, +rr}} <> +tt:
      cv.osl.step(T.VPair{nn, T.VHead{pp, rr}}, tt, Equal.cong(List<&2, T.Val>, T.Val, zs => T.VPair{nn, T.VHead{pp,
        zs}}, D1.own.rows(T.rows.seal(rr)), T.rows.seal(D1.own.rows(rr)), cv.osl(rr)), cv.osl(tt))
    case T.VPair{+nn, T.VAots{+pp, +rr}} <> +tt:
      cv.osl.step(T.VPair{nn, T.VAots{pp, rr}}, tt, Equal.cong(List<&2, T.Val>, T.Val, zs => T.VPair{nn, T.VAots{pp,
        zs}}, D1.own.rows(T.rows.seal(rr)), T.rows.seal(D1.own.rows(rr)), cv.osl(rr)), cv.osl(tt))
    case T.VPair{+nn, T.VInl{+rr}} <> +tt:
      cv.osl.step(T.VPair{nn, T.VInl{rr}}, tt, Equal.cong(List<&2, T.Val>, T.Val, zs => T.VPair{nn, T.VInl{zs}},
        D1.own.rows(T.rows.seal(rr)), T.rows.seal(D1.own.rows(rr)), cv.osl(rr)), cv.osl(tt))
    case T.VPair{+nn, T.VArr{+rr}} <> +tt:
      cv.osl.step(T.VPair{nn, T.VArr{rr}}, tt, Equal.cong(List<&2, T.Val>, T.Val, zs => T.VPair{nn, T.VArr{zs}},
        D1.own.rows(List.reverse(&2, T.Val, T.rows.seal(rr))), List.reverse(&2, T.Val,
        T.rows.seal(D1.own.rows(rr))), cv.own.rs(T.rows.seal(rr), T.rows.seal(D1.own.rows(rr)), cv.osl(rr))),
        cv.osl(tt))
    case T.VPair{+nn, T.VStr{+a}} <> +tt:
      cv.osl.step(T.VPair{nn, T.VStr{a}}, tt, {==}, cv.osl(tt))
    case T.VPair{+nn, T.VSpan{+a, +b}} <> +tt:
      cv.osl.step(T.VPair{nn, T.VSpan{a, b}}, tt, {==}, cv.osl(tt))
    case T.VPair{+nn, T.VInt{+a, +b}} <> +tt:
      cv.osl.step(T.VPair{nn, T.VInt{a, b}}, tt, {==}, cv.osl(tt))
    case T.VPair{+nn, T.VFlo{+a, +b}} <> +tt:
      cv.osl.step(T.VPair{nn, T.VFlo{a, b}}, tt, {==}, cv.osl(tt))
    case T.VPair{+nn, T.VBool{+a}} <> +tt:
      cv.osl.step(T.VPair{nn, T.VBool{a}}, tt, {==}, cv.osl(tt))
    case T.VPair{+nn, T.VWhen{+a}} <> +tt:
      cv.osl.step(T.VPair{nn, T.VWhen{a}}, tt, {==}, cv.osl(tt))
    case T.VPair{+nn, T.VAot{+a, +b}} <> +tt:
      cv.osl.step(T.VPair{nn, T.VAot{a, b}}, tt, {==}, cv.osl(tt))
    case T.VPair{+nn, T.VPair{+a, +b}} <> +tt:
      cv.osl.step(T.VPair{nn, T.VPair{a, b}}, tt, {==}, cv.osl(tt))
    case T.VAot{+pp, +rr} <> +tt:
      cv.osl.step(T.VAot{pp, rr}, tt, Equal.cong(List<&2, T.Val>, T.Val, zs => T.VAot{pp, zs},
        D1.own.rows(T.rows.seal(rr)), T.rows.seal(D1.own.rows(rr)), cv.osl(rr)), cv.osl(tt))
    case T.VAots{+pp, +rr} <> +tt:
      cv.osl.step(T.VAots{pp, rr}, tt, Equal.cong(List<&2, T.Val>, T.Val, zs => T.VAots{pp, zs},
        D1.own.rows(T.rows.seal(rr)), T.rows.seal(D1.own.rows(rr)), cv.osl(rr)), cv.osl(tt))
    case T.VInl{+rr} <> +tt:
      cv.osl.step(T.VInl{rr}, tt, Equal.cong(List<&2, T.Val>, T.Val, zs => T.VInl{zs}, D1.own.rows(T.rows.seal(rr)),
        T.rows.seal(D1.own.rows(rr)), cv.osl(rr)), cv.osl(tt))
    case T.VArr{+rr} <> +tt:
      cv.osl.step(T.VArr{rr}, tt, Equal.cong(List<&2, T.Val>, T.Val, zs => T.VArr{zs}, D1.own.rows(List.reverse(&2,
        T.Val, T.rows.seal(rr))), List.reverse(&2, T.Val, T.rows.seal(D1.own.rows(rr))), cv.own.rs(T.rows.seal(rr),
        T.rows.seal(D1.own.rows(rr)), cv.osl(rr))), cv.osl(tt))
    case T.VStr{+a} <> +tt:
      cv.osl.step(T.VStr{a}, tt, {==}, cv.osl(tt))
    case T.VSpan{+a, +b} <> +tt:
      cv.osl.step(T.VSpan{a, b}, tt, {==}, cv.osl(tt))
    case T.VInt{+a, +b} <> +tt:
      cv.osl.step(T.VInt{a, b}, tt, {==}, cv.osl(tt))
    case T.VFlo{+a, +b} <> +tt:
      cv.osl.step(T.VFlo{a, b}, tt, {==}, cv.osl(tt))
    case T.VBool{+a} <> +tt:
      cv.osl.step(T.VBool{a}, tt, {==}, cv.osl(tt))
    case T.VWhen{+a} <> +tt:
      cv.osl.step(T.VWhen{a}, tt, {==}, cv.osl(tt))
    case T.VHead{+a, +b} <> +tt:
      cv.osl.step(T.VHead{a, b}, tt, {==}, cv.osl(tt))

# every value of a list sealed, in order
def cv.smap(xs: List<&2, T.Val>) -> List<&2, T.Val>:
  match xs:
    case []:
      []
    case hh <> tt:
      D6.sealed(hh) <> cv.smap(tt)

# a reversal onto a list is the reversal, then the list
def cv.rga(
  zs: List<&2, T.Val>,
  +bb: List<&2, T.Val>,
  +acc: List<&2, T.Val>
) -> {List.reverse.go(&2, T.Val, zs, List.append(&2, T.Val, bb, acc))
  == List.append(&2, T.Val, List.reverse.go(&2, T.Val, zs, bb), acc) : List<&2, T.Val>}:
  match zs:
    case []:
      {==}
    case +hh <> tt:
      cv.rga(tt, hh <> bb, acc)

# rows.seal seals every value and reverses the list
def cv.seal.rs(xs: List<&2, T.Val>) -> {T.rows.seal(xs) == List.reverse(&2, T.Val, cv.smap(xs)) : List<&2, T.Val>}:
  match xs:
    case []:
      {==}
    case +hh <> +tt:
      Equal.trans(List<&2, T.Val>, T.rows.seal(hh <> tt), List.append(&2, T.Val, T.rows.seal(tt), [D6.sealed(hh)]),
        List.reverse(&2, T.Val, cv.smap(hh <> tt)), L11.seal_puts_newest_last(hh, tt),
        Equal.trans(List<&2, T.Val>, List.append(&2, T.Val, T.rows.seal(tt), [D6.sealed(hh)]),
          List.append(&2, T.Val, List.reverse(&2, T.Val, cv.smap(tt)), [D6.sealed(hh)]),
          List.reverse(&2, T.Val, cv.smap(hh <> tt)),
          Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => List.append(&2, T.Val, zs, [D6.sealed(hh)]),
            T.rows.seal(tt), List.reverse(&2, T.Val, cv.smap(tt)), cv.seal.rs(tt)),
          Equal.sym(List<&2, T.Val>, List.reverse.go(&2, T.Val, cv.smap(tt), [D6.sealed(hh)]),
            List.append(&2, T.Val, List.reverse(&2, T.Val, cv.smap(tt)), [D6.sealed(hh)]),
            cv.rga(cv.smap(tt), [], [D6.sealed(hh)]))))

# sealing every value commutes with a reversal
def cv.smap.rev(
  xs: List<&2, T.Val>,
  +acc: List<&2, T.Val>
) -> {cv.smap(List.reverse.go(&2, T.Val, xs, acc)) == List.reverse.go(&2, T.Val, cv.smap(xs), cv.smap(acc))
  : List<&2, T.Val>}:
  match xs:
    case []:
      {==}
    case +hh <> tt:
      cv.smap.rev(tt, hh <> acc)

# the list a well-formed value holds, by where it sits
def cv.wat(rows: Bool) -> T.WfAt:
  match rows:
    case False{}:
      T.WfItems{}
    case True{}:
      T.WfInl{}

# one value of a list sealed in the scanner's form, then the rest: the head
# and the rest each read as own reads them
def cv.sm.step(
  +yy: T.Val,
  +tt: List<&2, T.Val>,
  ey: {D6.sealed(L15.cv.raw1(yy)) == L15.cv.own1(yy) : T.Val},
  ih: {cv.smap(L15.cv.raw(tt)) == D1.own.rows(tt) : List<&2, T.Val>}
) -> {cv.smap(L15.cv.raw(yy <> tt)) == D1.own.rows(yy <> tt) : List<&2, T.Val>}:
  Equal.trans(List<&2, T.Val>, cv.smap(L15.cv.raw(yy <> tt)), cv.smap(L15.cv.raw1(yy) <> L15.cv.raw(tt)),
    D1.own.rows(yy <> tt),
    Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => cv.smap(zs), L15.cv.raw(yy <> tt),
      L15.cv.raw1(yy) <> L15.cv.raw(tt), cv.raw.cons(yy, tt)),
    Equal.trans(List<&2, T.Val>, D6.sealed(L15.cv.raw1(yy)) <> cv.smap(L15.cv.raw(tt)),
      L15.cv.own1(yy) <> D1.own.rows(tt), D1.own.rows(yy <> tt),
      Equal.trans(List<&2, T.Val>, D6.sealed(L15.cv.raw1(yy)) <> cv.smap(L15.cv.raw(tt)),
        L15.cv.own1(yy) <> cv.smap(L15.cv.raw(tt)), L15.cv.own1(yy) <> D1.own.rows(tt),
        Equal.cong(T.Val, List<&2, T.Val>, zz => zz <> cv.smap(L15.cv.raw(tt)), D6.sealed(L15.cv.raw1(yy)),
          L15.cv.own1(yy), ey),
        Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => L15.cv.own1(yy) <> zs, cv.smap(L15.cv.raw(tt)),
          D1.own.rows(tt), ih)),
      Equal.sym(List<&2, T.Val>, D1.own.rows(yy <> tt), L15.cv.own1(yy) <> D1.own.rows(tt), cv.own.cons(yy, tt))))

# an array's items: reversing their seal gives what own reads of them, once
# sealing them one by one does
def cv.sra(
  +its: List<&2, T.Val>,
  hh: {cv.smap(L15.cv.raw(its)) == D1.own.rows(its) : List<&2, T.Val>}
) -> {List.reverse(&2, T.Val, T.rows.seal(L15.cv.raw(its))) == D1.own.rows(its) : List<&2, T.Val>}:
  Equal.trans(List<&2, T.Val>, List.reverse(&2, T.Val, T.rows.seal(L15.cv.raw(its))),
    List.reverse(&2, T.Val, List.reverse(&2, T.Val, cv.smap(L15.cv.raw(its)))), D1.own.rows(its),
    Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => List.reverse(&2, T.Val, zs), T.rows.seal(L15.cv.raw(its)),
      List.reverse(&2, T.Val, cv.smap(L15.cv.raw(its))), cv.seal.rs(L15.cv.raw(its))),
    Equal.trans(List<&2, T.Val>, List.reverse(&2, T.Val, List.reverse(&2, T.Val, cv.smap(L15.cv.raw(its)))),
      cv.smap(L15.cv.raw(its)), D1.own.rows(its), cv.rev2(cv.smap(L15.cv.raw(its))), hh))

# an inline table's pairs: the seal of their reversal gives what own reads of
# them, once sealing them one by one does
def cv.sri(
  +rs: List<&2, T.Val>,
  hh: {cv.smap(L15.cv.raw(rs)) == D1.own.rows(rs) : List<&2, T.Val>}
) -> {T.rows.seal(List.reverse(&2, T.Val, L15.cv.raw(rs))) == D1.own.rows(rs) : List<&2, T.Val>}:
  Equal.trans(List<&2, T.Val>, T.rows.seal(List.reverse(&2, T.Val, L15.cv.raw(rs))),
    List.reverse(&2, T.Val, cv.smap(List.reverse(&2, T.Val, L15.cv.raw(rs)))), D1.own.rows(rs),
    cv.seal.rs(List.reverse(&2, T.Val, L15.cv.raw(rs))),
    Equal.trans(List<&2, T.Val>, List.reverse(&2, T.Val, cv.smap(List.reverse(&2, T.Val, L15.cv.raw(rs)))),
      List.reverse(&2, T.Val, List.reverse(&2, T.Val, cv.smap(L15.cv.raw(rs)))), D1.own.rows(rs),
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => List.reverse(&2, T.Val, zs),
        cv.smap(List.reverse(&2, T.Val, L15.cv.raw(rs))), List.reverse(&2, T.Val, cv.smap(L15.cv.raw(rs))),
        cv.smap.rev(L15.cv.raw(rs), [])),
      Equal.trans(List<&2, T.Val>, List.reverse(&2, T.Val, List.reverse(&2, T.Val, cv.smap(L15.cv.raw(rs)))),
        cv.smap(L15.cv.raw(rs)), D1.own.rows(rs), cv.rev2(cv.smap(L15.cv.raw(rs))), hh)))

# sealing the scanner's form of a well-formed list, value by value, gives
# what own reads of it
def cv.sm(
  ys: List<&2, T.Val>,
  rows: Bool,
  +hw: {T.wf.go(ys, cv.wat(rows)) == True{} : Bool}
) -> {cv.smap(L15.cv.raw(ys)) == D1.own.rows(ys) : List<&2, T.Val>}:
  match ys:
    case []:
      {==}
    case T.VStr{+aa} <> +tt:
      match rows:
        case False{}:
          cv.sm.step(T.VStr{aa}, tt, {==}, cv.sm(tt, False{}, cv.wfi.tl(T.VStr{aa}, tt, hw)))
        case True{}:
          Eq.bit.absurd(&2, {cv.smap(L15.cv.raw(T.VStr{aa} <> tt)) == D1.own.rows(T.VStr{aa} <> tt) : List<&2,
            T.Val>}, hw)
    case T.VSpan{+aa, +bb} <> +tt:
      match rows:
        case False{}:
          cv.sm.step(T.VSpan{aa, bb}, tt, {==}, cv.sm(tt, False{}, cv.wfi.tl(T.VSpan{aa, bb}, tt, hw)))
        case True{}:
          Eq.bit.absurd(&2, {cv.smap(L15.cv.raw(T.VSpan{aa, bb} <> tt)) == D1.own.rows(T.VSpan{aa,
            bb} <> tt) : List<&2, T.Val>}, hw)
    case T.VInt{+aa, +bb} <> +tt:
      match rows:
        case False{}:
          cv.sm.step(T.VInt{aa, bb}, tt, {==}, cv.sm(tt, False{}, cv.wfi.tl(T.VInt{aa, bb}, tt, hw)))
        case True{}:
          Eq.bit.absurd(&2, {cv.smap(L15.cv.raw(T.VInt{aa, bb} <> tt)) == D1.own.rows(T.VInt{aa,
            bb} <> tt) : List<&2, T.Val>}, hw)
    case T.VFlo{+aa, +bb} <> +tt:
      match rows:
        case False{}:
          cv.sm.step(T.VFlo{aa, bb}, tt, {==}, cv.sm(tt, False{}, cv.wfi.tl(T.VFlo{aa, bb}, tt, hw)))
        case True{}:
          Eq.bit.absurd(&2, {cv.smap(L15.cv.raw(T.VFlo{aa, bb} <> tt)) == D1.own.rows(T.VFlo{aa,
            bb} <> tt) : List<&2, T.Val>}, hw)
    case T.VBool{+aa} <> +tt:
      match rows:
        case False{}:
          cv.sm.step(T.VBool{aa}, tt, {==}, cv.sm(tt, False{}, cv.wfi.tl(T.VBool{aa}, tt, hw)))
        case True{}:
          Eq.bit.absurd(&2, {cv.smap(L15.cv.raw(T.VBool{aa} <> tt)) == D1.own.rows(T.VBool{aa} <> tt) : List<&2,
            T.Val>}, hw)
    case T.VWhen{+aa} <> +tt:
      match rows:
        case False{}:
          cv.sm.step(T.VWhen{aa}, tt, {==}, cv.sm(tt, False{}, cv.wfi.tl(T.VWhen{aa}, tt, hw)))
        case True{}:
          Eq.bit.absurd(&2, {cv.smap(L15.cv.raw(T.VWhen{aa} <> tt)) == D1.own.rows(T.VWhen{aa} <> tt) : List<&2,
            T.Val>}, hw)
    case T.VArr{+its} <> +tt:
      match rows:
        case False{}:
          cv.sm.step(T.VArr{its}, tt, Equal.cong(List<&2, T.Val>, T.Val, zs => T.VArr{zs}, List.reverse(&2, T.Val,
            T.rows.seal(L15.cv.raw(its))), D1.own.rows(its), cv.sra(its, cv.sm(its, False{}, cv.wfi.hd(T.VArr{its},
            tt, hw)))), cv.sm(tt, False{}, cv.wfi.tl(T.VArr{its}, tt, hw)))
        case True{}:
          Eq.bit.absurd(&2, {cv.smap(L15.cv.raw(T.VArr{its} <> tt)) == D1.own.rows(T.VArr{its} <> tt) : List<&2,
            T.Val>}, hw)
    case T.VInl{+rs} <> +tt:
      match rows:
        case False{}:
          cv.sm.step(T.VInl{rs}, tt, Equal.cong(List<&2, T.Val>, T.Val, zs => T.VInl{zs}, T.rows.seal(List.reverse(&2,
            T.Val, L15.cv.raw(rs))), D1.own.rows(rs), cv.sri(rs, cv.sm(rs, True{}, cv.wfi.hd(T.VInl{rs}, tt, hw)))),
            cv.sm(tt, False{}, cv.wfi.tl(T.VInl{rs}, tt, hw)))
        case True{}:
          Eq.bit.absurd(&2, {cv.smap(L15.cv.raw(T.VInl{rs} <> tt)) == D1.own.rows(T.VInl{rs} <> tt) : List<&2,
            T.Val>}, hw)
    case T.VHead{+aa, +bb} <> +tt:
      match rows:
        case False{}:
          Eq.bit.absurd(&2, {cv.smap(L15.cv.raw(T.VHead{aa, bb} <> tt)) == D1.own.rows(T.VHead{aa,
            bb} <> tt) : List<&2, T.Val>}, cv.wfi.hd(T.VHead{aa, bb}, tt, hw))
        case True{}:
          Eq.bit.absurd(&2, {cv.smap(L15.cv.raw(T.VHead{aa, bb} <> tt)) == D1.own.rows(T.VHead{aa,
            bb} <> tt) : List<&2, T.Val>}, hw)
    case T.VAot{+aa, +bb} <> +tt:
      match rows:
        case False{}:
          Eq.bit.absurd(&2, {cv.smap(L15.cv.raw(T.VAot{aa, bb} <> tt)) == D1.own.rows(T.VAot{aa,
            bb} <> tt) : List<&2, T.Val>}, cv.wfi.hd(T.VAot{aa, bb}, tt, hw))
        case True{}:
          Eq.bit.absurd(&2, {cv.smap(L15.cv.raw(T.VAot{aa, bb} <> tt)) == D1.own.rows(T.VAot{aa,
            bb} <> tt) : List<&2, T.Val>}, hw)
    case T.VAots{+aa, +bb} <> +tt:
      match rows:
        case False{}:
          Eq.bit.absurd(&2, {cv.smap(L15.cv.raw(T.VAots{aa, bb} <> tt)) == D1.own.rows(T.VAots{aa,
            bb} <> tt) : List<&2, T.Val>}, cv.wfi.hd(T.VAots{aa, bb}, tt, hw))
        case True{}:
          Eq.bit.absurd(&2, {cv.smap(L15.cv.raw(T.VAots{aa, bb} <> tt)) == D1.own.rows(T.VAots{aa,
            bb} <> tt) : List<&2, T.Val>}, hw)
    case T.VPair{+kk, T.VStr{+aa}} <> +tt:
      match rows:
        case False{}:
          Eq.bit.absurd(&2, {cv.smap(L15.cv.raw(T.VPair{kk, T.VStr{aa}} <> tt)) == D1.own.rows(T.VPair{kk,
            T.VStr{aa}} <> tt) : List<&2, T.Val>}, cv.wfi.hd(T.VPair{kk, T.VStr{aa}}, tt, hw))
        case True{}:
          cv.sm.step(T.VPair{kk, T.VStr{aa}}, tt, {==}, cv.sm(tt, True{}, cv.wfp.t(kk, T.VStr{aa}, tt, hw)))
    case T.VPair{+kk, T.VSpan{+aa, +bb}} <> +tt:
      match rows:
        case False{}:
          Eq.bit.absurd(&2, {cv.smap(L15.cv.raw(T.VPair{kk, T.VSpan{aa, bb}} <> tt)) == D1.own.rows(T.VPair{kk,
            T.VSpan{aa, bb}} <> tt) : List<&2, T.Val>}, cv.wfi.hd(T.VPair{kk, T.VSpan{aa, bb}}, tt, hw))
        case True{}:
          cv.sm.step(T.VPair{kk, T.VSpan{aa, bb}}, tt, {==}, cv.sm(tt, True{}, cv.wfp.t(kk, T.VSpan{aa, bb}, tt, hw)))
    case T.VPair{+kk, T.VInt{+aa, +bb}} <> +tt:
      match rows:
        case False{}:
          Eq.bit.absurd(&2, {cv.smap(L15.cv.raw(T.VPair{kk, T.VInt{aa, bb}} <> tt)) == D1.own.rows(T.VPair{kk,
            T.VInt{aa, bb}} <> tt) : List<&2, T.Val>}, cv.wfi.hd(T.VPair{kk, T.VInt{aa, bb}}, tt, hw))
        case True{}:
          cv.sm.step(T.VPair{kk, T.VInt{aa, bb}}, tt, {==}, cv.sm(tt, True{}, cv.wfp.t(kk, T.VInt{aa, bb}, tt, hw)))
    case T.VPair{+kk, T.VFlo{+aa, +bb}} <> +tt:
      match rows:
        case False{}:
          Eq.bit.absurd(&2, {cv.smap(L15.cv.raw(T.VPair{kk, T.VFlo{aa, bb}} <> tt)) == D1.own.rows(T.VPair{kk,
            T.VFlo{aa, bb}} <> tt) : List<&2, T.Val>}, cv.wfi.hd(T.VPair{kk, T.VFlo{aa, bb}}, tt, hw))
        case True{}:
          cv.sm.step(T.VPair{kk, T.VFlo{aa, bb}}, tt, {==}, cv.sm(tt, True{}, cv.wfp.t(kk, T.VFlo{aa, bb}, tt, hw)))
    case T.VPair{+kk, T.VBool{+aa}} <> +tt:
      match rows:
        case False{}:
          Eq.bit.absurd(&2, {cv.smap(L15.cv.raw(T.VPair{kk, T.VBool{aa}} <> tt)) == D1.own.rows(T.VPair{kk,
            T.VBool{aa}} <> tt) : List<&2, T.Val>}, cv.wfi.hd(T.VPair{kk, T.VBool{aa}}, tt, hw))
        case True{}:
          cv.sm.step(T.VPair{kk, T.VBool{aa}}, tt, {==}, cv.sm(tt, True{}, cv.wfp.t(kk, T.VBool{aa}, tt, hw)))
    case T.VPair{+kk, T.VWhen{+aa}} <> +tt:
      match rows:
        case False{}:
          Eq.bit.absurd(&2, {cv.smap(L15.cv.raw(T.VPair{kk, T.VWhen{aa}} <> tt)) == D1.own.rows(T.VPair{kk,
            T.VWhen{aa}} <> tt) : List<&2, T.Val>}, cv.wfi.hd(T.VPair{kk, T.VWhen{aa}}, tt, hw))
        case True{}:
          cv.sm.step(T.VPair{kk, T.VWhen{aa}}, tt, {==}, cv.sm(tt, True{}, cv.wfp.t(kk, T.VWhen{aa}, tt, hw)))
    case T.VPair{+kk, T.VArr{+its}} <> +tt:
      match rows:
        case False{}:
          Eq.bit.absurd(&2, {cv.smap(L15.cv.raw(T.VPair{kk, T.VArr{its}} <> tt)) == D1.own.rows(T.VPair{kk,
            T.VArr{its}} <> tt) : List<&2, T.Val>}, cv.wfi.hd(T.VPair{kk, T.VArr{its}}, tt, hw))
        case True{}:
          cv.sm.step(T.VPair{kk, T.VArr{its}}, tt, Equal.cong(List<&2, T.Val>, T.Val, zs => T.VPair{kk, T.VArr{zs}},
            List.reverse(&2, T.Val, T.rows.seal(L15.cv.raw(its))), D1.own.rows(its), cv.sra(its, cv.sm(its, False{},
            cv.wfp.v(kk, T.VArr{its}, tt, hw)))), cv.sm(tt, True{}, cv.wfp.t(kk, T.VArr{its}, tt, hw)))
    case T.VPair{+kk, T.VInl{+rs}} <> +tt:
      match rows:
        case False{}:
          Eq.bit.absurd(&2, {cv.smap(L15.cv.raw(T.VPair{kk, T.VInl{rs}} <> tt)) == D1.own.rows(T.VPair{kk,
            T.VInl{rs}} <> tt) : List<&2, T.Val>}, cv.wfi.hd(T.VPair{kk, T.VInl{rs}}, tt, hw))
        case True{}:
          cv.sm.step(T.VPair{kk, T.VInl{rs}}, tt, Equal.cong(List<&2, T.Val>, T.Val, zs => T.VPair{kk, T.VInl{zs}},
            T.rows.seal(List.reverse(&2, T.Val, L15.cv.raw(rs))), D1.own.rows(rs), cv.sri(rs, cv.sm(rs, True{},
            cv.wfp.v(kk, T.VInl{rs}, tt, hw)))), cv.sm(tt, True{}, cv.wfp.t(kk, T.VInl{rs}, tt, hw)))
    case T.VPair{+kk, T.VHead{+aa, +bb}} <> +tt:
      match rows:
        case False{}:
          Eq.bit.absurd(&2, {cv.smap(L15.cv.raw(T.VPair{kk, T.VHead{aa, bb}} <> tt)) == D1.own.rows(T.VPair{kk,
            T.VHead{aa, bb}} <> tt) : List<&2, T.Val>}, cv.wfi.hd(T.VPair{kk, T.VHead{aa, bb}}, tt, hw))
        case True{}:
          Eq.bit.absurd(&2, {cv.smap(L15.cv.raw(T.VPair{kk, T.VHead{aa, bb}} <> tt)) == D1.own.rows(T.VPair{kk,
            T.VHead{aa, bb}} <> tt) : List<&2, T.Val>}, cv.wfp.v(kk, T.VHead{aa, bb}, tt, hw))
    case T.VPair{+kk, T.VAot{+aa, +bb}} <> +tt:
      match rows:
        case False{}:
          Eq.bit.absurd(&2, {cv.smap(L15.cv.raw(T.VPair{kk, T.VAot{aa, bb}} <> tt)) == D1.own.rows(T.VPair{kk,
            T.VAot{aa, bb}} <> tt) : List<&2, T.Val>}, cv.wfi.hd(T.VPair{kk, T.VAot{aa, bb}}, tt, hw))
        case True{}:
          Eq.bit.absurd(&2, {cv.smap(L15.cv.raw(T.VPair{kk, T.VAot{aa, bb}} <> tt)) == D1.own.rows(T.VPair{kk,
            T.VAot{aa, bb}} <> tt) : List<&2, T.Val>}, cv.wfp.v(kk, T.VAot{aa, bb}, tt, hw))
    case T.VPair{+kk, T.VAots{+aa, +bb}} <> +tt:
      match rows:
        case False{}:
          Eq.bit.absurd(&2, {cv.smap(L15.cv.raw(T.VPair{kk, T.VAots{aa, bb}} <> tt)) == D1.own.rows(T.VPair{kk,
            T.VAots{aa, bb}} <> tt) : List<&2, T.Val>}, cv.wfi.hd(T.VPair{kk, T.VAots{aa, bb}}, tt, hw))
        case True{}:
          Eq.bit.absurd(&2, {cv.smap(L15.cv.raw(T.VPair{kk, T.VAots{aa, bb}} <> tt)) == D1.own.rows(T.VPair{kk,
            T.VAots{aa, bb}} <> tt) : List<&2, T.Val>}, cv.wfp.v(kk, T.VAots{aa, bb}, tt, hw))
    case T.VPair{+kk, T.VPair{+aa, +bb}} <> +tt:
      match rows:
        case False{}:
          Eq.bit.absurd(&2, {cv.smap(L15.cv.raw(T.VPair{kk, T.VPair{aa, bb}} <> tt)) == D1.own.rows(T.VPair{kk,
            T.VPair{aa, bb}} <> tt) : List<&2, T.Val>}, cv.wfi.hd(T.VPair{kk, T.VPair{aa, bb}}, tt, hw))
        case True{}:
          Eq.bit.absurd(&2, {cv.smap(L15.cv.raw(T.VPair{kk, T.VPair{aa, bb}} <> tt)) == D1.own.rows(T.VPair{kk,
            T.VPair{aa, bb}} <> tt) : List<&2, T.Val>}, cv.wfp.v(kk, T.VPair{aa, bb}, tt, hw))

# the root's rows once the pair is put, sealed, read out as the pair render
# was given
def rv.own(
  +kk: String,
  +vv: T.Val,
  +ww: T.Val,
  +hh: {L15.cv.own1(vv) == L15.cv.raw1(ww) : T.Val},
  +hw: {D1.cv.wf(ww) == True{} : Bool},
  hi: {T.wf.go([T.VPair{kk, ww}], T.WfInl{}) == True{} : Bool}
) -> {D1.own.rows(T.rows.seal([T.VPair{kk, vv}])) == D1.own.rows([T.VPair{kk, ww}]) : List<&2, T.Val>}:
  +p1 = {T.VPair{kk, vv} : T.Val}
  +p2 = {T.VPair{kk, ww} : T.Val}
  Equal.trans(List<&2, T.Val>, D1.own.rows(T.rows.seal([p1])), T.rows.seal(D1.own.rows([p1])),
    D1.own.rows([p2]), cv.osl([p1]),
    Equal.trans(List<&2, T.Val>, T.rows.seal(D1.own.rows([p1])), T.rows.seal(L15.cv.raw([p2])), D1.own.rows([p2]),
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => T.rows.seal(zs), D1.own.rows([p1]), L15.cv.raw([p2]),
        Equal.trans(List<&2, T.Val>, D1.own.rows([p1]), [L15.cv.own1(p1)], L15.cv.raw([p2]),
          cv.own.cons(p1, []),
          Equal.trans(List<&2, T.Val>, [L15.cv.own1(p1)], [L15.cv.raw1(p2)], L15.cv.raw([p2]),
            Equal.cong(T.Val, List<&2, T.Val>, yy => [yy], L15.cv.own1(p1), L15.cv.raw1(p2),
              cv.lift(kk, vv, ww, hh, hw)),
            Equal.sym(List<&2, T.Val>, L15.cv.raw([p2]), [L15.cv.raw1(p2)], cv.raw.cons(p2, []))))),
      Equal.trans(List<&2, T.Val>, T.rows.seal(L15.cv.raw([p2])), List.reverse(&2, T.Val, cv.smap(L15.cv.raw([p2]))),
        D1.own.rows([p2]), cv.seal.rs(L15.cv.raw([p2])),
        Equal.trans(List<&2, T.Val>, List.reverse(&2, T.Val, cv.smap(L15.cv.raw([p2]))),
          List.reverse(&2, T.Val, D1.own.rows([p2])), D1.own.rows([p2]),
          Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => List.reverse(&2, T.Val, zs), cv.smap(L15.cv.raw([p2])),
            D1.own.rows([p2]), cv.sm([p2], True{}, hi)),
          Equal.trans(List<&2, T.Val>, List.reverse(&2, T.Val, D1.own.rows([p2])), [L15.cv.own1(p2)],
            D1.own.rows([p2]),
            Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => List.reverse(&2, T.Val, zs), D1.own.rows([p2]),
              [L15.cv.own1(p2)], cv.own.cons(p2, [])),
            Equal.sym(List<&2, T.Val>, D1.own.rows([p2]), [L15.cv.own1(p2)], cv.own.cons(p2, [])))))))

# at the start of a line, a character that is no blank and no newline takes
# the full step
def dl.ws(
  sp: Bool,
  nl: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +cc: Char,
  fsp: {sp == False{} : Bool},
  fnl: {nl == False{} : Bool}
) -> {T.read.fast.ws(sp, nl, True{}, "", rw, hs, he, [], [], T.LTop{}, bk, qk, [], un, lf, ab, cc)
  == T.read.fast.old("", rw, hs, he, [], [], T.LTop{}, bk, qk, [], un, lf, ab, cc) : T.St}:
  match sp:
    case True{}:
      Eq.bit.absurd2(&2, {T.read.fast.ws(True{}, nl, True{}, "", rw, hs, he, [], [], T.LTop{}, bk, qk, [], un, lf, ab,
        cc) == T.read.fast.old("", rw, hs, he, [], [], T.LTop{}, bk, qk, [], un, lf, ab, cc) : T.St}, fsp)
    case False{}:
      match nl:
        case True{}:
          Eq.bit.absurd2(&2, {T.read.fast.ws(False{}, True{}, True{}, "", rw, hs, he, [], [], T.LTop{}, bk, qk, [], un,
            lf, ab, cc) == T.read.fast.old("", rw, hs, he, [], [], T.LTop{}, bk, qk, [], un, lf, ab, cc) : T.St}, fnl)
        case False{}:
          {==}

# the first character of a bare key starts the key's buffer
def dl.b1(
  +xx: U32,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +fb: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.doc.scan(M5.dl(rw, hs, he, bk, qk, un, lf, ab), Chr{xx}) == T.MScan{cv.kbs(rw, hs, he, bk, qk, [], un, lf, ab,
  [Chr{xx}])} : T.Mode}:
  +st = {M5.dl(rw, hs, he, bk, qk, un, lf, ab) : T.St}
  +fsp = {cv.nsp(T.ch.sp(Chr{xx}), xx, 32, 9, {==}, fb, {==}, {==}) : {T.ch.sp(Chr{xx}) == False{} : Bool}}
  +fnl = {cv.nsp(T.ch.nl(Chr{xx}), xx, 10, 13, {==}, fb, {==}, {==}) : {T.ch.nl(Chr{xx}) == False{} : Bool}}
  Equal.trans(T.Mode,
    T.doc.scan(st, Chr{xx}),
    T.MScan{T.read.fast(st, Chr{xx})},
    T.MScan{cv.kbs(rw, hs, he, bk, qk, [], un, lf, ab, [Chr{xx}])},
    M13.scan.other(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), U32.is_eq(xx, 13), st, Chr{xx}, {==}, {==},
        {==},
      ch => T.bare.at(ch), fb, {==}, {==}, {==}),
    Equal.cong(T.St, T.Mode, s2 => T.MScan{s2},
      T.read.fast(st, Chr{xx}),
      cv.kbs(rw, hs, he, bk, qk, [], un, lf, ab, [Chr{xx}]),
      Equal.trans(T.St,
        T.read.fast(st, Chr{xx}),
        T.read.fast.old("", rw, hs, he, [], [], T.LTop{}, bk, qk, [], un, lf, ab, Chr{xx}),
        cv.kbs(rw, hs, he, bk, qk, [], un, lf, ab, [Chr{xx}]),
        dl.ws(T.ch.sp(Chr{xx}), T.ch.nl(Chr{xx}), rw, hs, he, bk, qk, un, lf, ab, Chr{xx}, fsp, fnl),
        Equal.cong(T.St, T.St, s2 => T.read.once2(s2),
          T.lex.top.go(T.ch.sp(Chr{xx}), T.ch.nl(Chr{xx}), Char.is_eq(Chr{xx}, '#'), Char.is_eq(Chr{xx}, '['),
            Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), T.bare.at(Chr{xx}), st, Chr{xx}),
          T.st.push(st, Chr{xx}, T.LKey{}),
          key.top(T.ch.sp(Chr{xx}), T.ch.nl(Chr{xx}), Char.is_eq(Chr{xx}, '#'), Char.is_eq(Chr{xx}, '['),
            Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), T.bare.at(Chr{xx}), st, xx, {==}, {==}, {==}, {==},
            {==}, {==}, {==}, fb)))))

# a bare key then " = ", from the start of a line
def dl.kb(
  +xx: U32,
  +tt: String,
  +yy: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  -PP: T.Doc -> Type,
  +ee: {T.bare.all.step(T.bare.at(Chr{xx}), _u => T.bare.all(String.to_list(tt))) == True{} : Bool},
  ih: cv.KThen(SCon{Chr{xx}, tt}, yy, rw, hs, he, [], ab, PP)
) -> PP(T.doc.read(String.append(SCon{Chr{xx}, tt}, SCon{' ', SCon{'=', SCon{' ', yy}}}), T.MScan{M5.dl(rw, hs, he, bk,
    qk,
  un, lf, ab)})):
  +zz = {SCon{' ', SCon{'=', SCon{' ', yy}}} : String}
  +b1 = {M8.rev.onto(tt, [Chr{xx}]) : List<&2, Char>}
  pp.step(PP, T.doc.read(String.append(tt, zz), T.doc.scan(M5.dl(rw, hs, he, bk, qk, un, lf, ab), Chr{xx})),
    T.doc.read(yy, T.MScan{cv.vp(rw, hs, he, [SCon{Chr{xx}, tt}], bk, qk, [], un, lf, ab)}),
    Equal.trans(T.Doc,
      T.doc.read(String.append(tt, zz), T.doc.scan(M5.dl(rw, hs, he, bk, qk, un, lf, ab), Chr{xx})),
      T.doc.read(String.append(tt, zz), T.MScan{cv.kbs(rw, hs, he, bk, qk, [], un, lf, ab, [Chr{xx}])}),
      T.doc.read(yy, T.MScan{cv.vp(rw, hs, he, [SCon{Chr{xx}, tt}], bk, qk, [], un, lf, ab)}),
      Equal.cong(T.Mode, T.Doc, md => T.doc.read(String.append(tt, zz), md),
        T.doc.scan(M5.dl(rw, hs, he, bk, qk, un, lf, ab), Chr{xx}),
        T.MScan{cv.kbs(rw, hs, he, bk, qk, [], un, lf, ab, [Chr{xx}])},
        dl.b1(xx, rw, hs, he, bk, qk, un, lf, ab, ball.head(T.bare.at(Chr{xx}), String.to_list(tt), ee))),
      Equal.trans(T.Doc,
        T.doc.read(String.append(tt, zz), T.MScan{cv.kbs(rw, hs, he, bk, qk, [], un, lf, ab, [Chr{xx}])}),
        T.doc.read(zz, T.MScan{cv.kbs(rw, hs, he, bk, qk, [], un, lf, ab, b1)}),
        T.doc.read(yy, T.MScan{cv.vp(rw, hs, he, [SCon{Chr{xx}, tt}], bk, qk, [], un, lf, ab)}),
        cv.kb.body(tt, zz, rw, hs, he, bk, qk, [], un, lf, ab, [Chr{xx}], ball.tail(T.bare.at(Chr{xx}),
          String.to_list(tt), ee)),
        Equal.trans(T.Doc,
          T.doc.read(zz, T.MScan{cv.kbs(rw, hs, he, bk, qk, [], un, lf, ab, b1)}),
          T.doc.read(yy, T.MScan{cv.vp(rw, hs, he, [T.buf.str(b1)], bk, qk, [], un, lf, ab)}),
          T.doc.read(yy, T.MScan{cv.vp(rw, hs, he, [SCon{Chr{xx}, tt}], bk, qk, [], un, lf, ab)}),
          cv.kb.eq(rw, hs, he, bk, qk, [], un, lf, ab, b1, rev.full(tt, Chr{xx}, []), yy),
          Equal.cong(String, T.Doc, nm => T.doc.read(yy, T.MScan{cv.vp(rw, hs, he, [nm], bk, qk, [], un, lf, ab)}),
            T.buf.str(b1), SCon{Chr{xx}, tt}, wh.bname(xx, tt))))),
    ih(bk, qk, un, lf))

# a quoted key, as key.basic writes it, then " = ", from the start of a line
def dl.kq(
  +kk: String,
  +yy: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  -PP: T.Doc -> Type,
  ih: cv.KThen(kk, yy, rw, hs, he, [], ab, PP)
) -> PP(T.doc.read(String.append(T.key.basic(kk), SCon{' ', SCon{'=', SCon{' ', yy}}}), T.MScan{M5.dl(rw, hs, he, bk,
    qk,
  un, lf, ab)})):
  +zz = {SCon{' ', SCon{'=', SCon{' ', yy}}} : String}
  %Equal.sym(String, T.key.basic(kk), "\"" ++ L12.escs(kk) ++ "\"", L12.basic_escs(kk)) :
    PP(T.doc.read(String.append(_, zz), T.MScan{M5.dl(rw, hs, he, bk, qk, un, lf, ab)}))
  %Equal.sym(String, String.append(String.append(L12.escs(kk), "\""), zz), String.append(L12.escs(kk), SCon{'"',
    zz}), Eq.append_assoc(L12.escs(kk), "\"", zz)) :
    PP(T.doc.read(SCon{'"', _}, T.MScan{M5.dl(rw, hs, he, bk, qk, un, lf, ab)}))
  qu.escs(kk, rw, hs, he, [], [], ab, bk, un, lf, [], SCon{'"', zz}, PP,
    +b2 => +u2 => +l2 => pp.step(PP, T.doc.read(SCon{'"', zz}, T.MScan{qu(rw, hs, he, [], [], ab, b2, u2, l2,
      M8.rev.onto(kk, []))}), T.doc.read(yy, T.MScan{cv.vp(rw, hs, he, [kk], b2, T.QBasic{}, [], u2, l2, ab)}),
      cv.kq.close(rw, hs, he, [], ab, b2, u2, l2, kk, yy), ih(b2, T.QBasic{}, u2, l2)))

# a key as key writes it, bare or quoted, then " = ", from the start of a line
def dl.key.go(
  bb: Bool,
  +kk: String,
  eb: {T.bare(kk) == bb : Bool},
  +yy: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  -PP: T.Doc -> Type,
  ih: cv.KThen(kk, yy, rw, hs, he, [], ab, PP)
) -> PP(T.doc.read(String.append(T.key.go(bb, kk), SCon{' ', SCon{'=', SCon{' ', yy}}}), T.MScan{M5.dl(rw, hs, he, bk,
    qk,
  un, lf, ab)})):
  match bb:
    case False{}:
      dl.kq(kk, yy, rw, hs, he, bk, qk, un, lf, ab, PP, ih)
    case True{}:
      match kk:
        case SNil{}:
          Eq.bit.absurd(&1, PP(T.doc.read(String.append(SNil{}, SCon{' ', SCon{'=', SCon{' ', yy}}}),
            T.MScan{M5.dl(rw, hs, he, bk, qk, un, lf, ab)})), eb)
        case SCon{hh, +tt}:
          match hh:
            case Chr{+xx}:
              dl.kb(xx, tt, yy, rw, hs, he, bk, qk, un, lf, ab, PP, eb, ih)

# a key as key writes it, then " = ", from the start of a line
def dl.key(
  +kk: String,
  +yy: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  -PP: T.Doc -> Type,
  ih: cv.KThen(kk, yy, rw, hs, he, [], ab, PP)
) -> PP(T.doc.read(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', yy}}}), T.MScan{M5.dl(rw, hs, he, bk, qk, un,
    lf,
  ab)})):
  dl.key.go(T.bare(kk), kk, {==}, yy, rw, hs, he, bk, qk, un, lf, ab, PP, ih)

# the rest of the text after a key line, from the start of the next line with
# the value put at the head of the current table's rows: a value own reads as
# the scanner's form of v, and whatever back, qkind, uni and left it leaves
def dl.Then(
  +kk: String,
  +v: T.Val,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  @vv: T.Val -> @b2: T.Lex -> @q2: T.QKind -> @u2: U32 -> @l2: U32 ->
    {L15.cv.own1(vv) == L15.cv.raw1(v) : T.Val} ->
    PP(T.doc.read(rest, T.MScan{M5.dl(D1.tb.set(he, "", rw, T.VPair{kk, vv} <> D1.tb.rows(he, rw)), hs, he, b2, q2,
      u2, l2, ab)}))

# the value's walk puts it at the head of the current table's rows, and the
# newline starts the next line
def dl.put(
  +kk: String,
  +vv: T.Val,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  +eo: {D1.tb.open(he, rw) == True{} : Bool},
  +ec: {D1.counts.down(he, T.path.len(he, 0)) == True{} : Bool},
  +em: {T.get(D1.tb.rows(he, rw), kk) == T.Miss{} : T.Hit}
) -> {T.doc.read(SCon{'\n', rest}, T.MScan{T.take.top([], vv, "", rw, hs, he, [kk], bk, qk, un, lf, ab, False{})})
  == T.doc.read(rest, T.MScan{M5.dl(D1.tb.set(he, "", rw, T.VPair{kk, vv} <> D1.tb.rows(he, rw)), hs, he, bk, qk, un,
    lf, ab)}) : T.Doc}:
  Equal.cong(T.End, T.Doc, en => T.doc.read(SCon{'\n', rest}, T.MScan{T.take.root(en, he, bk, qk, un, lf, ab,
    False{})}),
    T.tree.walk(List.append(&2, String, he, [kk]), T.Tw{rw, T.JPut{vv}, [], "", "", hs, False{}}, T.path.len(he, 0)),
    T.End{D1.tb.set(he, "", rw, T.VPair{kk, vv} <> D1.tb.rows(he, rw)), "", hs},
    L16.walk_put_at_head(he, kk, vv, rw, hs, T.path.len(he, 0), False{}, eo, ec, em))

# a key line as render writes it, from the start of a line in the table he:
# the key, " = ", the value's text and a newline
def dl.line(
  +kk: String,
  +v: T.Val,
  +hw: {D1.cv.wf(v) == True{} : Bool},
  +hl: {D1.cv.short1(v) == True{} : Bool},
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  +eo: {D1.tb.open(he, rw) == True{} : Bool},
  +ec: {D1.counts.down(he, T.path.len(he, 0)) == True{} : Bool},
  +em: {T.get(D1.tb.rows(he, rw), kk) == T.Miss{} : T.Hit},
  ih: dl.Then(kk, v, rw, hs, he, ab, rest, PP)
) -> PP(T.doc.read(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(v, SCon{'\n', rest})}}}),
  T.MScan{M5.dl(rw, hs, he, bk, qk, un, lf, ab)})):
  dl.key(kk, D1.cv.tx(v, SCon{'\n', rest}), rw, hs, he, bk, qk, un, lf, ab, PP,
    +b2 => +q2 => +u2 => +l2 => L15.value_reads_back(v, hw, hl, rw, hs, he, [kk], b2, q2, [], u2, l2, ab,
      SCon{'\n', rest}, {==}, PP,
      +vv => +b3 => +q3 => +u3 => +l3 => ho => pp.step(PP,
        T.doc.read(SCon{'\n', rest}, T.MScan{T.take.top([], vv, "", rw, hs, he, [kk], b3, q3, u3, l3, ab, False{})}),
        T.doc.read(rest, T.MScan{M5.dl(D1.tb.set(he, "", rw, T.VPair{kk, vv} <> D1.tb.rows(he, rw)), hs, he, b3, q3,
          u3, l3, ab)}),
        dl.put(kk, vv, rw, hs, he, b3, q3, u3, l3, ab, rest, eo, ec, em),
        ih(vv, b3, q3, u3, l3, ho))))

# appending nothing leaves a list of values
def va.nil(xs: List<&2, T.Val>) -> {List.append(&2, T.Val, xs, []) == xs : List<&2, T.Val>}:
  match xs:
    case []:
      {==}
    case +xx <> rest:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, tt => xx <> tt, List.append(&2, T.Val, rest, []), rest, va.nil(rest))

# whether a lookup found nothing
def lk.miss(lk: T.Look) -> Bool:
  match lk:
    case T.KMiss{}:
      True{}
    case _:
      False{}

# what a value refers to is never nothing
def wa.lo(vv: T.Val) -> {lk.miss(T.look.of(vv)) == False{} : Bool}:
  match vv:

    case T.VStr{_a1}:
      {==}
    case T.VSpan{_a1, _a2}:
      {==}
    case T.VInt{_a1, _a2}:
      {==}
    case T.VFlo{_a1, _a2}:
      {==}
    case T.VBool{_a1}:
      {==}
    case T.VWhen{_a1}:
      {==}
    case T.VArr{_a1}:
      {==}
    case T.VInl{_a1}:
      {==}
    case T.VHead{_a1, _a2}:
      {==}
    case T.VAot{_a1, _a2}:
      {==}
    case T.VAots{_a1, _a2}:
      {==}
    case T.VPair{_a1, _a2}:
      {==}

# a lookup of a pair's value misses as the lookup of the pair does
def wa.lm.p(
  bb: Bool,
  +old: T.Val,
  +t: List<&2, T.Val>,
  +nn: String,
  ih: {lk.miss(T.rows.look(t, nn)) == L4.is_miss(T.rows.find(t, nn)) : Bool}
) -> {lk.miss(T.look.step(bb, old, _u => T.rows.look(t, nn))) == L4.is_miss(T.find.step(bb, old,
  _u => T.rows.find(t, nn))) : Bool}:
  match bb:
    case True{}:
      wa.lo(old)
    case False{}:
      ih

# rows.look finds nothing exactly when get does
def wa.lm(
  rows: List<&2, T.Val>,
  +nn: String
) -> {lk.miss(T.rows.look(rows, nn)) == L4.is_miss(T.get(rows, nn)) : Bool}:
  match rows:
    case []:
      {==}
    case T.VPair{+n2, +old} <> +t:
      wa.lm.p(T.str.eq(n2, nn), old, t, nn, wa.lm(t, nn))

    case T.VStr{_a1} <> +t:
      wa.lm(t, nn)
    case T.VSpan{_a1, _a2} <> +t:
      wa.lm(t, nn)
    case T.VInt{_a1, _a2} <> +t:
      wa.lm(t, nn)
    case T.VFlo{_a1, _a2} <> +t:
      wa.lm(t, nn)
    case T.VBool{_a1} <> +t:
      wa.lm(t, nn)
    case T.VWhen{_a1} <> +t:
      wa.lm(t, nn)
    case T.VArr{_a1} <> +t:
      wa.lm(t, nn)
    case T.VInl{_a1} <> +t:
      wa.lm(t, nn)
    case T.VHead{_a1, _a2} <> +t:
      wa.lm(t, nn)
    case T.VAot{_a1, _a2} <> +t:
      wa.lm(t, nn)
    case T.VAots{_a1, _a2} <> +t:
      wa.lm(t, nn)

# what a name refers to once its pairs hold x: nothing if it had no pair,
# else what x is
def lk.r(lk: T.Look, xx: T.Val) -> T.Look:
  match lk:
    case T.KMiss{}:
      T.KMiss{}
    case _:
      T.look.of(xx)

# a pair the name had refers to x once replaced
def wa.lr.o(old: T.Val, +xx: T.Val) -> {lk.r(T.look.of(old), xx) == T.look.of(xx) : T.Look}:
  match old:

    case T.VStr{_a1}:
      {==}
    case T.VSpan{_a1, _a2}:
      {==}
    case T.VInt{_a1, _a2}:
      {==}
    case T.VFlo{_a1, _a2}:
      {==}
    case T.VBool{_a1}:
      {==}
    case T.VWhen{_a1}:
      {==}
    case T.VArr{_a1}:
      {==}
    case T.VInl{_a1}:
      {==}
    case T.VHead{_a1, _a2}:
      {==}
    case T.VAot{_a1, _a2}:
      {==}
    case T.VAots{_a1, _a2}:
      {==}
    case T.VPair{_a1, _a2}:
      {==}

# one pair of the rows
def wa.lr.p(
  bb: Bool,
  +n2: String,
  +old: T.Val,
  +t: List<&2, T.Val>,
  +nn: String,
  +xx: T.Val,
  ee: {T.str.eq(n2, nn) == bb : Bool},
  ih: {T.rows.look(T.rows.repl(t, nn, xx), nn) == lk.r(T.rows.look(t, nn), xx) : T.Look}
) -> {T.rows.look(T.rows.repl.step(bb, n2, old, xx, _u => T.rows.repl(t, nn, xx)), nn)
  == lk.r(T.look.step(bb, old, _u => T.rows.look(t, nn)), xx) : T.Look}:
  match bb:
    case True{}:
      Equal.trans(T.Look, T.look.step(T.str.eq(n2, nn), xx, _u => T.rows.look(T.rows.repl(t, nn, xx), nn)),
        T.look.of(xx), lk.r(T.look.of(old), xx),
        Equal.cong(Bool, T.Look, b2 => T.look.step(b2, xx, _u => T.rows.look(T.rows.repl(t, nn, xx), nn)),
          T.str.eq(n2, nn), True{}, ee),
        Equal.sym(T.Look, lk.r(T.look.of(old), xx), T.look.of(xx), wa.lr.o(old, xx)))
    case False{}:
      Equal.trans(T.Look, T.look.step(T.str.eq(n2, nn), old, _u => T.rows.look(T.rows.repl(t, nn, xx), nn)),
        T.rows.look(T.rows.repl(t, nn, xx), nn), lk.r(T.rows.look(t, nn), xx),
        Equal.cong(Bool, T.Look, b2 => T.look.step(b2, old, _u => T.rows.look(T.rows.repl(t, nn, xx), nn)),
          T.str.eq(n2, nn), False{}, ee),
        ih)

# a name whose pairs are replaced by x refers to x, if it referred to anything
def wa.lr(
  rows: List<&2, T.Val>,
  +nn: String,
  +xx: T.Val
) -> {T.rows.look(T.rows.repl(rows, nn, xx), nn)
  == lk.r(T.rows.look(rows, nn), xx) : T.Look}:
  match rows:
    case []:
      {==}
    case T.VPair{+n2, +old} <> +t:
      wa.lr.p(T.str.eq(n2, nn), n2, old, t, nn, xx, {==}, wa.lr(t, nn, xx))

    case T.VStr{_a1} <> +t:
      wa.lr(t, nn, xx)
    case T.VSpan{_a1, _a2} <> +t:
      wa.lr(t, nn, xx)
    case T.VInt{_a1, _a2} <> +t:
      wa.lr(t, nn, xx)
    case T.VFlo{_a1, _a2} <> +t:
      wa.lr(t, nn, xx)
    case T.VBool{_a1} <> +t:
      wa.lr(t, nn, xx)
    case T.VWhen{_a1} <> +t:
      wa.lr(t, nn, xx)
    case T.VArr{_a1} <> +t:
      wa.lr(t, nn, xx)
    case T.VInl{_a1} <> +t:
      wa.lr(t, nn, xx)
    case T.VHead{_a1, _a2} <> +t:
      wa.lr(t, nn, xx)
    case T.VAot{_a1, _a2} <> +t:
      wa.lr(t, nn, xx)
    case T.VAots{_a1, _a2} <> +t:
      wa.lr(t, nn, xx)

# one pair of the rows
def wa.rr.p(
  bb: Bool,
  +n2: String,
  +old: T.Val,
  +t: List<&2, T.Val>,
  +nn: String,
  +xx: T.Val,
  +yy: T.Val,
  ee: {T.str.eq(n2, nn) == bb : Bool},
  ih: {T.rows.repl(T.rows.repl(t, nn, xx), nn, yy) == T.rows.repl(t, nn, yy) : List<&2, T.Val>}
) -> {T.rows.repl(T.rows.repl.step(bb, n2, old, xx, _u => T.rows.repl(t, nn, xx)), nn, yy)
  == T.rows.repl.step(bb, n2, old, yy, _u => T.rows.repl(t, nn, yy)) : List<&2, T.Val>}:
  match bb:
    case True{}:
      Equal.trans(List<&2, T.Val>,
        T.rows.repl.step(T.str.eq(n2, nn), n2, xx, yy, _u => T.rows.repl(T.rows.repl(t, nn, xx), nn, yy)),
        T.VPair{n2, yy} <> T.rows.repl(T.rows.repl(t, nn, xx), nn, yy),
        T.VPair{n2, yy} <> T.rows.repl(t, nn, yy),
        Equal.cong(Bool, List<&2, T.Val>, b2 => T.rows.repl.step(b2, n2, xx, yy, _u => T.rows.repl(T.rows.repl(t, nn,
          xx),
          nn, yy)), T.str.eq(n2, nn), True{}, ee),
        Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => T.VPair{n2, yy} <> zs, T.rows.repl(T.rows.repl(t, nn, xx),
          nn, yy),
          T.rows.repl(t, nn, yy), ih))
    case False{}:
      Equal.trans(List<&2, T.Val>,
        T.rows.repl.step(T.str.eq(n2, nn), n2, old, yy, _u => T.rows.repl(T.rows.repl(t, nn, xx), nn, yy)),
        T.VPair{n2, old} <> T.rows.repl(T.rows.repl(t, nn, xx), nn, yy),
        T.VPair{n2, old} <> T.rows.repl(t, nn, yy),
        Equal.cong(Bool, List<&2, T.Val>, b2 => T.rows.repl.step(b2, n2, old, yy, _u => T.rows.repl(T.rows.repl(t, nn,
          xx),
          nn, yy)), T.str.eq(n2, nn), False{}, ee),
        Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => T.VPair{n2, old} <> zs, T.rows.repl(T.rows.repl(t, nn, xx),
          nn, yy),
          T.rows.repl(t, nn, yy), ih))

# replacing a name's pairs twice is replacing them once with the second value
def wa.rr(
  rows: List<&2, T.Val>,
  +nn: String,
  +xx: T.Val,
  +yy: T.Val
) -> {T.rows.repl(T.rows.repl(rows, nn, xx), nn, yy)
  == T.rows.repl(rows, nn, yy) : List<&2, T.Val>}:
  match rows:
    case []:
      {==}
    case T.VPair{+n2, +old} <> +t:
      wa.rr.p(T.str.eq(n2, nn), n2, old, t, nn, xx, yy, {==}, wa.rr(t, nn, xx, yy))

    case T.VStr{+a1} <> +t:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => T.VStr{a1} <> zs, T.rows.repl(T.rows.repl(t, nn, xx), nn, yy),
        T.rows.repl(t, nn, yy), wa.rr(t, nn, xx, yy))
    case T.VSpan{+a1, +a2} <> +t:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => T.VSpan{a1, a2} <> zs, T.rows.repl(T.rows.repl(t, nn, xx), nn,
        yy),
        T.rows.repl(t, nn, yy), wa.rr(t, nn, xx, yy))
    case T.VInt{+a1, +a2} <> +t:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => T.VInt{a1, a2} <> zs, T.rows.repl(T.rows.repl(t, nn, xx), nn,
        yy),
        T.rows.repl(t, nn, yy), wa.rr(t, nn, xx, yy))
    case T.VFlo{+a1, +a2} <> +t:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => T.VFlo{a1, a2} <> zs, T.rows.repl(T.rows.repl(t, nn, xx), nn,
        yy),
        T.rows.repl(t, nn, yy), wa.rr(t, nn, xx, yy))
    case T.VBool{+a1} <> +t:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => T.VBool{a1} <> zs, T.rows.repl(T.rows.repl(t, nn, xx), nn, yy),
        T.rows.repl(t, nn, yy), wa.rr(t, nn, xx, yy))
    case T.VWhen{+a1} <> +t:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => T.VWhen{a1} <> zs, T.rows.repl(T.rows.repl(t, nn, xx), nn, yy),
        T.rows.repl(t, nn, yy), wa.rr(t, nn, xx, yy))
    case T.VArr{+a1} <> +t:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => T.VArr{a1} <> zs, T.rows.repl(T.rows.repl(t, nn, xx), nn, yy),
        T.rows.repl(t, nn, yy), wa.rr(t, nn, xx, yy))
    case T.VInl{+a1} <> +t:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => T.VInl{a1} <> zs, T.rows.repl(T.rows.repl(t, nn, xx), nn, yy),
        T.rows.repl(t, nn, yy), wa.rr(t, nn, xx, yy))
    case T.VHead{+a1, +a2} <> +t:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => T.VHead{a1, a2} <> zs, T.rows.repl(T.rows.repl(t, nn, xx), nn,
        yy),
        T.rows.repl(t, nn, yy), wa.rr(t, nn, xx, yy))
    case T.VAot{+a1, +a2} <> +t:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => T.VAot{a1, a2} <> zs, T.rows.repl(T.rows.repl(t, nn, xx), nn,
        yy),
        T.rows.repl(t, nn, yy), wa.rr(t, nn, xx, yy))
    case T.VAots{+a1, +a2} <> +t:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => T.VAots{a1, a2} <> zs, T.rows.repl(T.rows.repl(t, nn, xx), nn,
        yy),
        T.rows.repl(t, nn, yy), wa.rr(t, nn, xx, yy))

# one pair of rows that do not hold the name
def wa.rm.p(
  bb: Bool,
  +n2: String,
  +old: T.Val,
  +t: List<&2, T.Val>,
  +nn: String,
  +xx: T.Val,
  em: {L4.is_miss(T.find.step(bb, old, _u => T.rows.find(t, nn))) == True{} : Bool},
  ih: {L4.is_miss(T.rows.find(t, nn)) == True{} : Bool} -> {T.rows.repl(t, nn, xx) == t : List<&2, T.Val>}
) -> {T.rows.repl.step(bb, n2, old, xx, _u => T.rows.repl(t, nn, xx)) == T.VPair{n2, old} <> t : List<&2, T.Val>}:
  match bb:
    case True{}:
      Eq.bit.absurd(&2, {T.rows.repl.step(True{}, n2, old, xx, _u => T.rows.repl(t, nn, xx)) == T.VPair{n2, old} <> t
        : List<&2, T.Val>}, em)
    case False{}:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => T.VPair{n2, old} <> zs, T.rows.repl(t, nn, xx), t, ih(em))

# replacing the pairs of a name the rows do not hold leaves them
def wa.rm(
  rows: List<&2, T.Val>,
  +nn: String,
  +xx: T.Val,
  em: {L4.is_miss(T.get(rows, nn)) == True{} : Bool}
) -> {T.rows.repl(rows, nn, xx) == rows : List<&2, T.Val>}:
  match rows:
    case []:
      {==}
    case T.VPair{+n2, +old} <> +t:
      wa.rm.p(T.str.eq(n2, nn), n2, old, t, nn, xx, em, e2 => wa.rm(t, nn, xx, e2))

    case T.VStr{+a1} <> +t:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => T.VStr{a1} <> zs, T.rows.repl(t, nn, xx), t, wa.rm(t, nn, xx,
        em))
    case T.VSpan{+a1, +a2} <> +t:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => T.VSpan{a1, a2} <> zs, T.rows.repl(t, nn, xx), t, wa.rm(t, nn,
        xx, em))
    case T.VInt{+a1, +a2} <> +t:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => T.VInt{a1, a2} <> zs, T.rows.repl(t, nn, xx), t, wa.rm(t, nn,
        xx, em))
    case T.VFlo{+a1, +a2} <> +t:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => T.VFlo{a1, a2} <> zs, T.rows.repl(t, nn, xx), t, wa.rm(t, nn,
        xx, em))
    case T.VBool{+a1} <> +t:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => T.VBool{a1} <> zs, T.rows.repl(t, nn, xx), t, wa.rm(t, nn, xx,
        em))
    case T.VWhen{+a1} <> +t:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => T.VWhen{a1} <> zs, T.rows.repl(t, nn, xx), t, wa.rm(t, nn, xx,
        em))
    case T.VArr{+a1} <> +t:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => T.VArr{a1} <> zs, T.rows.repl(t, nn, xx), t, wa.rm(t, nn, xx,
        em))
    case T.VInl{+a1} <> +t:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => T.VInl{a1} <> zs, T.rows.repl(t, nn, xx), t, wa.rm(t, nn, xx,
        em))
    case T.VHead{+a1, +a2} <> +t:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => T.VHead{a1, a2} <> zs, T.rows.repl(t, nn, xx), t, wa.rm(t, nn,
        xx, em))
    case T.VAot{+a1, +a2} <> +t:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => T.VAot{a1, a2} <> zs, T.rows.repl(t, nn, xx), t, wa.rm(t, nn,
        xx, em))
    case T.VAots{+a1, +a2} <> +t:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => T.VAots{a1, a2} <> zs, T.rows.repl(t, nn, xx), t, wa.rm(t, nn,
        xx, em))

# a pair at the head of the rows is what its name refers to
def wa.look.hd(
  +nn: String,
  +xx: T.Val,
  +cs: List<&2, T.Val>
) -> {T.rows.look(T.VPair{nn, xx} <> cs, nn) == T.look.of(xx) : T.Look}:
  Equal.cong(Bool, T.Look, b2 => T.look.step(b2, xx, _u => T.rows.look(cs, nn)), T.str.eq(nn, nn), True{},
    M16.str.eq.self(nn))

# and the pair replaced, when the rest does not hold the name
def wa.repl.hd(
  +nn: String,
  +xx: T.Val,
  +cs: List<&2, T.Val>,
  +yy: T.Val,
  em: {L4.is_miss(T.get(cs, nn)) == True{} : Bool}
) -> {T.rows.repl(T.VPair{nn, xx} <> cs, nn, yy) == T.VPair{nn, yy} <> cs : List<&2, T.Val>}:
  Equal.trans(List<&2, T.Val>, T.rows.repl.step(T.str.eq(nn, nn), nn, xx, yy, _u => T.rows.repl(cs, nn, yy)),
    T.VPair{nn, yy} <> T.rows.repl(cs, nn, yy), T.VPair{nn, yy} <> cs,
    Equal.cong(Bool, List<&2, T.Val>, b2 => T.rows.repl.step(b2, nn, xx, yy, _u => T.rows.repl(cs, nn, yy)),
      T.str.eq(nn, nn),
      True{}, M16.str.eq.self(nn)),
    Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => T.VPair{nn, yy} <> zs, T.rows.repl(cs, nn, yy), cs, wa.rm(cs, nn,
      yy, em)))

# the table a pair holds, with its rows replaced: a table's own rows, or the
# rows of the newest element of an array of tables, which takes the array's path
def slot(xx: T.Val, new: List<&2, T.Val>) -> T.Val:
  match xx:
    case T.VHead{pp, _r}:
      T.VHead{pp, new}
    case T.VAots{+pp, es}:
      match es:
        case T.VAot{_q, _r} <> older:
          T.VAots{pp, T.VAot{pp, new} <> older}
        case other:
          T.VAots{pp, other}
    case other:
      other

# whether a pair holds such a table
def slot.ok(xx: T.Val) -> Bool:
  match xx:
    case T.VHead{_p, _r}:
      True{}
    case T.VAots{_p, es}:
      match es:
        case T.VAot{_q, _r} <> _older:
          True{}
        case _:
          False{}
    case _:
      False{}

# a walk goes on through such a table
def slot.can(xx: T.Val, ok: {slot.ok(xx) == True{} : Bool}) -> {D1.tb.can(T.look.of(xx)) == True{} : Bool}:
  match xx:
    case T.VHead{_p, _r}:
      {==}
    case T.VAots{_p, es}:
      match es:
        case []:
          Eq.bit.absurd(&2, {D1.tb.can(T.look.of(T.VAots{_p, []})) == True{} : Bool}, ok)

        case T.VStr{_a1} <> _older:
          Eq.bit.absurd(&2, {D1.tb.can(T.look.of(T.VAots{_p, T.VStr{_a1} <> _older})) == True{} : Bool}, ok)
        case T.VSpan{_a1, _a2} <> _older:
          Eq.bit.absurd(&2, {D1.tb.can(T.look.of(T.VAots{_p, T.VSpan{_a1, _a2} <> _older})) == True{} : Bool}, ok)
        case T.VInt{_a1, _a2} <> _older:
          Eq.bit.absurd(&2, {D1.tb.can(T.look.of(T.VAots{_p, T.VInt{_a1, _a2} <> _older})) == True{} : Bool}, ok)
        case T.VFlo{_a1, _a2} <> _older:
          Eq.bit.absurd(&2, {D1.tb.can(T.look.of(T.VAots{_p, T.VFlo{_a1, _a2} <> _older})) == True{} : Bool}, ok)
        case T.VBool{_a1} <> _older:
          Eq.bit.absurd(&2, {D1.tb.can(T.look.of(T.VAots{_p, T.VBool{_a1} <> _older})) == True{} : Bool}, ok)
        case T.VWhen{_a1} <> _older:
          Eq.bit.absurd(&2, {D1.tb.can(T.look.of(T.VAots{_p, T.VWhen{_a1} <> _older})) == True{} : Bool}, ok)
        case T.VArr{_a1} <> _older:
          Eq.bit.absurd(&2, {D1.tb.can(T.look.of(T.VAots{_p, T.VArr{_a1} <> _older})) == True{} : Bool}, ok)
        case T.VInl{_a1} <> _older:
          Eq.bit.absurd(&2, {D1.tb.can(T.look.of(T.VAots{_p, T.VInl{_a1} <> _older})) == True{} : Bool}, ok)
        case T.VHead{_a1, _a2} <> _older:
          Eq.bit.absurd(&2, {D1.tb.can(T.look.of(T.VAots{_p, T.VHead{_a1, _a2} <> _older})) == True{} : Bool}, ok)
        case T.VAot{_a1, _a2} <> _older:
          {==}
        case T.VAots{_a1, _a2} <> _older:
          Eq.bit.absurd(&2, {D1.tb.can(T.look.of(T.VAots{_p, T.VAots{_a1, _a2} <> _older})) == True{} : Bool}, ok)
        case T.VPair{_a1, _a2} <> _older:
          Eq.bit.absurd(&2, {D1.tb.can(T.look.of(T.VAots{_p, T.VPair{_a1, _a2} <> _older})) == True{} : Bool}, ok)
    case T.VStr{_a1}:
      Eq.bit.absurd(&2, {D1.tb.can(T.look.of(T.VStr{_a1})) == True{} : Bool}, ok)
    case T.VSpan{_a1, _a2}:
      Eq.bit.absurd(&2, {D1.tb.can(T.look.of(T.VSpan{_a1, _a2})) == True{} : Bool}, ok)
    case T.VInt{_a1, _a2}:
      Eq.bit.absurd(&2, {D1.tb.can(T.look.of(T.VInt{_a1, _a2})) == True{} : Bool}, ok)
    case T.VFlo{_a1, _a2}:
      Eq.bit.absurd(&2, {D1.tb.can(T.look.of(T.VFlo{_a1, _a2})) == True{} : Bool}, ok)
    case T.VBool{_a1}:
      Eq.bit.absurd(&2, {D1.tb.can(T.look.of(T.VBool{_a1})) == True{} : Bool}, ok)
    case T.VWhen{_a1}:
      Eq.bit.absurd(&2, {D1.tb.can(T.look.of(T.VWhen{_a1})) == True{} : Bool}, ok)
    case T.VArr{_a1}:
      Eq.bit.absurd(&2, {D1.tb.can(T.look.of(T.VArr{_a1})) == True{} : Bool}, ok)
    case T.VInl{_a1}:
      Eq.bit.absurd(&2, {D1.tb.can(T.look.of(T.VInl{_a1})) == True{} : Bool}, ok)
    case T.VAot{_a1, _a2}:
      Eq.bit.absurd(&2, {D1.tb.can(T.look.of(T.VAot{_a1, _a2})) == True{} : Bool}, ok)
    case T.VPair{_a1, _a2}:
      Eq.bit.absurd(&2, {D1.tb.can(T.look.of(T.VPair{_a1, _a2})) == True{} : Bool}, ok)

# a table put into by a set along a one-segment path to a pair at the head of
# the rows: the pair's table holds the new rows, and nothing else changes
def wa.head.x(
  xx: T.Val,
  +nn: String,
  +cs: List<&2, T.Val>,
  +pre: String,
  +new: List<&2, T.Val>,
  em: {L4.is_miss(T.get(cs, nn)) == True{} : Bool},
  ok: {slot.ok(xx) == True{} : Bool}
) -> {D1.tb.put.in(T.look.of(xx), nn, T.VPair{nn, xx} <> cs, pre, new) == T.VPair{nn, slot(xx, new)} <> cs
  : List<&2, T.Val>}:
  match xx:
    case T.VHead{+pp, +rr}:
      wa.repl.hd(nn, T.VHead{pp, rr}, cs, T.VHead{pp, new}, em)
    case T.VAots{+pp, es}:
      match es:
        case []:
          Eq.bit.absurd(&2, {D1.tb.put.in(T.look.of(T.VAots{pp, []}), nn, T.VPair{nn, T.VAots{pp, []}} <> cs, pre,
            new) == T.VPair{nn, slot(T.VAots{pp, []}, new)} <> cs : List<&2, T.Val>}, ok)

        case T.VStr{+a1} <> +older:
          Eq.bit.absurd(&2, {D1.tb.put.in(T.look.of(T.VAots{pp, T.VStr{a1} <> older}), nn, T.VPair{nn,
            T.VAots{pp, T.VStr{a1} <> older}} <> cs, pre, new) == T.VPair{nn, slot(T.VAots{pp, T.VStr{a1} <> older},
              new)} <> cs
            : List<&2, T.Val>}, ok)
        case T.VSpan{+a1, +a2} <> +older:
          Eq.bit.absurd(&2, {D1.tb.put.in(T.look.of(T.VAots{pp, T.VSpan{a1, a2} <> older}), nn, T.VPair{nn,
            T.VAots{pp, T.VSpan{a1, a2} <> older}} <> cs, pre, new) == T.VPair{nn, slot(T.VAots{pp, T.VSpan{a1,
              a2} <> older}, new)} <> cs
            : List<&2, T.Val>}, ok)
        case T.VInt{+a1, +a2} <> +older:
          Eq.bit.absurd(&2, {D1.tb.put.in(T.look.of(T.VAots{pp, T.VInt{a1, a2} <> older}), nn, T.VPair{nn,
            T.VAots{pp, T.VInt{a1, a2} <> older}} <> cs, pre, new) == T.VPair{nn, slot(T.VAots{pp, T.VInt{a1,
              a2} <> older}, new)} <> cs
            : List<&2, T.Val>}, ok)
        case T.VFlo{+a1, +a2} <> +older:
          Eq.bit.absurd(&2, {D1.tb.put.in(T.look.of(T.VAots{pp, T.VFlo{a1, a2} <> older}), nn, T.VPair{nn,
            T.VAots{pp, T.VFlo{a1, a2} <> older}} <> cs, pre, new) == T.VPair{nn, slot(T.VAots{pp, T.VFlo{a1,
              a2} <> older}, new)} <> cs
            : List<&2, T.Val>}, ok)
        case T.VBool{+a1} <> +older:
          Eq.bit.absurd(&2, {D1.tb.put.in(T.look.of(T.VAots{pp, T.VBool{a1} <> older}), nn, T.VPair{nn,
            T.VAots{pp, T.VBool{a1} <> older}} <> cs, pre, new) == T.VPair{nn, slot(T.VAots{pp, T.VBool{a1} <> older},
              new)} <> cs
            : List<&2, T.Val>}, ok)
        case T.VWhen{+a1} <> +older:
          Eq.bit.absurd(&2, {D1.tb.put.in(T.look.of(T.VAots{pp, T.VWhen{a1} <> older}), nn, T.VPair{nn,
            T.VAots{pp, T.VWhen{a1} <> older}} <> cs, pre, new) == T.VPair{nn, slot(T.VAots{pp, T.VWhen{a1} <> older},
              new)} <> cs
            : List<&2, T.Val>}, ok)
        case T.VArr{+a1} <> +older:
          Eq.bit.absurd(&2, {D1.tb.put.in(T.look.of(T.VAots{pp, T.VArr{a1} <> older}), nn, T.VPair{nn,
            T.VAots{pp, T.VArr{a1} <> older}} <> cs, pre, new) == T.VPair{nn, slot(T.VAots{pp, T.VArr{a1} <> older},
              new)} <> cs
            : List<&2, T.Val>}, ok)
        case T.VInl{+a1} <> +older:
          Eq.bit.absurd(&2, {D1.tb.put.in(T.look.of(T.VAots{pp, T.VInl{a1} <> older}), nn, T.VPair{nn,
            T.VAots{pp, T.VInl{a1} <> older}} <> cs, pre, new) == T.VPair{nn, slot(T.VAots{pp, T.VInl{a1} <> older},
              new)} <> cs
            : List<&2, T.Val>}, ok)
        case T.VHead{+a1, +a2} <> +older:
          Eq.bit.absurd(&2, {D1.tb.put.in(T.look.of(T.VAots{pp, T.VHead{a1, a2} <> older}), nn, T.VPair{nn,
            T.VAots{pp, T.VHead{a1, a2} <> older}} <> cs, pre, new) == T.VPair{nn, slot(T.VAots{pp, T.VHead{a1,
              a2} <> older}, new)} <> cs
            : List<&2, T.Val>}, ok)
        case T.VAot{+q, +r} <> +older:
          wa.repl.hd(nn, T.VAots{pp, T.VAot{q, r} <> older}, cs, T.VAots{pp, T.VAot{pp, new} <> older}, em)
        case T.VAots{+a1, +a2} <> +older:
          Eq.bit.absurd(&2, {D1.tb.put.in(T.look.of(T.VAots{pp, T.VAots{a1, a2} <> older}), nn, T.VPair{nn,
            T.VAots{pp, T.VAots{a1, a2} <> older}} <> cs, pre, new) == T.VPair{nn, slot(T.VAots{pp, T.VAots{a1,
              a2} <> older}, new)} <> cs
            : List<&2, T.Val>}, ok)
        case T.VPair{+a1, +a2} <> +older:
          Eq.bit.absurd(&2, {D1.tb.put.in(T.look.of(T.VAots{pp, T.VPair{a1, a2} <> older}), nn, T.VPair{nn,
            T.VAots{pp, T.VPair{a1, a2} <> older}} <> cs, pre, new) == T.VPair{nn, slot(T.VAots{pp, T.VPair{a1,
              a2} <> older}, new)} <> cs
            : List<&2, T.Val>}, ok)
    case T.VStr{+a1}:
      Eq.bit.absurd(&2, {D1.tb.put.in(T.look.of(T.VStr{a1}), nn, T.VPair{nn, T.VStr{a1}} <> cs, pre, new)
        == T.VPair{nn, slot(T.VStr{a1}, new)} <> cs : List<&2, T.Val>}, ok)
    case T.VSpan{+a1, +a2}:
      Eq.bit.absurd(&2, {D1.tb.put.in(T.look.of(T.VSpan{a1, a2}), nn, T.VPair{nn, T.VSpan{a1, a2}} <> cs, pre, new)
        == T.VPair{nn, slot(T.VSpan{a1, a2}, new)} <> cs : List<&2, T.Val>}, ok)
    case T.VInt{+a1, +a2}:
      Eq.bit.absurd(&2, {D1.tb.put.in(T.look.of(T.VInt{a1, a2}), nn, T.VPair{nn, T.VInt{a1, a2}} <> cs, pre, new)
        == T.VPair{nn, slot(T.VInt{a1, a2}, new)} <> cs : List<&2, T.Val>}, ok)
    case T.VFlo{+a1, +a2}:
      Eq.bit.absurd(&2, {D1.tb.put.in(T.look.of(T.VFlo{a1, a2}), nn, T.VPair{nn, T.VFlo{a1, a2}} <> cs, pre, new)
        == T.VPair{nn, slot(T.VFlo{a1, a2}, new)} <> cs : List<&2, T.Val>}, ok)
    case T.VBool{+a1}:
      Eq.bit.absurd(&2, {D1.tb.put.in(T.look.of(T.VBool{a1}), nn, T.VPair{nn, T.VBool{a1}} <> cs, pre, new)
        == T.VPair{nn, slot(T.VBool{a1}, new)} <> cs : List<&2, T.Val>}, ok)
    case T.VWhen{+a1}:
      Eq.bit.absurd(&2, {D1.tb.put.in(T.look.of(T.VWhen{a1}), nn, T.VPair{nn, T.VWhen{a1}} <> cs, pre, new)
        == T.VPair{nn, slot(T.VWhen{a1}, new)} <> cs : List<&2, T.Val>}, ok)
    case T.VArr{+a1}:
      Eq.bit.absurd(&2, {D1.tb.put.in(T.look.of(T.VArr{a1}), nn, T.VPair{nn, T.VArr{a1}} <> cs, pre, new)
        == T.VPair{nn, slot(T.VArr{a1}, new)} <> cs : List<&2, T.Val>}, ok)
    case T.VInl{+a1}:
      Eq.bit.absurd(&2, {D1.tb.put.in(T.look.of(T.VInl{a1}), nn, T.VPair{nn, T.VInl{a1}} <> cs, pre, new)
        == T.VPair{nn, slot(T.VInl{a1}, new)} <> cs : List<&2, T.Val>}, ok)
    case T.VAot{+a1, +a2}:
      Eq.bit.absurd(&2, {D1.tb.put.in(T.look.of(T.VAot{a1, a2}), nn, T.VPair{nn, T.VAot{a1, a2}} <> cs, pre, new)
        == T.VPair{nn, slot(T.VAot{a1, a2}, new)} <> cs : List<&2, T.Val>}, ok)
    case T.VPair{+a1, +a2}:
      Eq.bit.absurd(&2, {D1.tb.put.in(T.look.of(T.VPair{a1, a2}), nn, T.VPair{nn, T.VPair{a1, a2}} <> cs, pre, new)
        == T.VPair{nn, slot(T.VPair{a1, a2}, new)} <> cs : List<&2, T.Val>}, ok)

# a set along a one-segment path to a pair at the head of the rows
def wa.head(
  +nn: String,
  +xx: T.Val,
  +cs: List<&2, T.Val>,
  +pre: String,
  +new: List<&2, T.Val>,
  em: {L4.is_miss(T.get(cs, nn)) == True{} : Bool},
  ok: {slot.ok(xx) == True{} : Bool}
) -> {D1.tb.set([nn], pre, T.VPair{nn, xx} <> cs, new) == T.VPair{nn, slot(xx, new)} <> cs : List<&2, T.Val>}:
  Equal.trans(List<&2, T.Val>, D1.tb.put.in(T.rows.look(T.VPair{nn, xx} <> cs, nn), nn, T.VPair{nn, xx} <> cs, pre,
    new),
    D1.tb.put.in(T.look.of(xx), nn, T.VPair{nn, xx} <> cs, pre, new), T.VPair{nn, slot(xx, new)} <> cs,
    Equal.cong(T.Look, List<&2, T.Val>, lk => D1.tb.put.in(lk, nn, T.VPair{nn, xx} <> cs, pre, new),
      T.rows.look(T.VPair{nn, xx} <> cs, nn), T.look.of(xx), wa.look.hd(nn, xx, cs)),
    wa.head.x(xx, nn, cs, pre, new, em, ok))

# the walk goes on through the pair at the head of the rows
def wa.head.open(
  +nn: String,
  +xx: T.Val,
  +cs: List<&2, T.Val>,
  ok: {slot.ok(xx) == True{} : Bool}
) -> {D1.tb.open([nn], T.VPair{nn, xx} <> cs) == True{} : Bool}:
  Equal.trans(Bool, Bool.and(D1.tb.can(T.rows.look(T.VPair{nn, xx} <> cs, nn)), True{}),
    Bool.and(D1.tb.can(T.look.of(xx)), True{}), True{},
    Equal.cong(T.Look, Bool, lk => Bool.and(D1.tb.can(lk), True{}), T.rows.look(T.VPair{nn, xx} <> cs, nn),
      T.look.of(xx), wa.look.hd(nn, xx, cs)),
    Equal.cong(Bool, Bool, bt => Bool.and(bt, True{}), D1.tb.can(T.look.of(xx)), True{}, slot.can(xx, ok)))

# the rows after one step of a set along seg then rest
def wa.R1(
  +lk: T.Look,
  +seg: String,
  +rest: List<&2, String>,
  +pre: String,
  +rows: List<&2, T.Val>,
  +aa: List<&2, T.Val>
) -> List<&2, T.Val>:
  D1.tb.put.in(lk, seg, rows, pre, D1.tb.set(rest, T.tree.pre(pre, seg), D1.tb.into(lk), aa))

# a second set after the first, one step at a time: what the step after the
# first set does, against what the second set alone does
def wa.G(
  +lk: T.Look,
  +seg: String,
  +rest: List<&2, String>,
  +pre: String,
  +rows: List<&2, T.Val>,
  +aa: List<&2, T.Val>,
  +bb: List<&2, T.Val>
) -> Type:
  {D1.tb.put.in(T.rows.look(wa.R1(lk, seg, rest, pre, rows, aa), seg), seg, wa.R1(lk, seg, rest, pre, rows, aa), pre,
    D1.tb.set(rest, T.tree.pre(pre, seg), D1.tb.into(T.rows.look(wa.R1(lk, seg, rest, pre, rows, aa), seg)), bb))
    == D1.tb.put.in(lk, seg, rows, pre, D1.tb.set(rest, T.tree.pre(pre, seg), D1.tb.into(lk),
      bb)) : List<&2, T.Val>}

# the step's claim for the rows under the name: for every open r2, setting
# them twice is setting them once
def wa.ssIH(
  +rest: List<&2, String>,
  +pre: String,
  +seg: String,
  +aa: List<&2, T.Val>,
  +bb: List<&2, T.Val>
) -> Type:
  @r2: List<&2, T.Val> -> {D1.tb.open(rest, r2) == True{} : Bool} ->
    {D1.tb.set(rest, T.tree.pre(pre, seg), D1.tb.set(rest, T.tree.pre(pre, seg), r2, aa), bb)
      == D1.tb.set(rest, T.tree.pre(pre, seg), r2, bb) : List<&2, T.Val>}

# the step's rows set twice are the rows set once, by what the name refers to
def wa.ss.l(
  lk: T.Look,
  +seg: String,
  +rest: List<&2, String>,
  +pre: String,
  +rows: List<&2, T.Val>,
  +aa: List<&2, T.Val>,
  +bb: List<&2, T.Val>,
  e: {T.rows.look(rows, seg) == lk : T.Look},
  eo: {Bool.and(D1.tb.can(lk), D1.tb.open(rest, D1.tb.into(lk))) == True{} : Bool},
  ih: wa.ssIH(rest, pre, seg, aa, bb)
) -> wa.G(lk, seg, rest, pre, rows, aa, bb):
  match lk:
    case T.KMiss{}:
      +p1 = {T.tree.pre(pre, seg) : String}
      +sa = {D1.tb.set(rest, p1, [], aa) : List<&2, T.Val>}
      +x1 = {D1.tb.set(rest, p1, sa, bb) : List<&2, T.Val>}
      +r1 = {T.VPair{seg, T.VHead{p1, sa}} <> rows : List<&2, T.Val>}
      +em = {Equal.trans(Bool, L4.is_miss(T.get(rows, seg)), lk.miss(T.rows.look(rows, seg)), True{},
        Equal.sym(Bool, lk.miss(T.rows.look(rows, seg)), L4.is_miss(T.get(rows, seg)), wa.lm(rows, seg)),
        Equal.cong(T.Look, Bool, l2 => lk.miss(l2), T.rows.look(rows, seg), T.KMiss{}, e))
        : {L4.is_miss(T.get(rows, seg)) == True{} : Bool}}
      Equal.trans(List<&2, T.Val>,
        D1.tb.put.in(T.rows.look(r1, seg), seg, r1, pre, D1.tb.set(rest, p1, D1.tb.into(T.rows.look(r1, seg)),
          bb)),
        D1.tb.put.in(T.KHead{p1, sa}, seg, r1, pre, x1),
        T.VPair{seg, T.VHead{p1, D1.tb.set(rest, p1, [], bb)}} <> rows,
        Equal.cong(T.Look, List<&2, T.Val>, l2 => D1.tb.put.in(l2, seg, r1, pre, D1.tb.set(rest, p1,
          D1.tb.into(l2), bb)),
          T.rows.look(r1, seg), T.KHead{p1, sa}, wa.look.hd(seg, T.VHead{p1, sa}, rows)),
        Equal.trans(List<&2, T.Val>, T.rows.repl(r1, seg, T.VHead{p1, x1}), T.VPair{seg, T.VHead{p1, x1}} <> rows,
          T.VPair{seg, T.VHead{p1, D1.tb.set(rest, p1, [], bb)}} <> rows,
          wa.repl.hd(seg, T.VHead{p1, sa}, rows, T.VHead{p1, x1}, em),
          Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zz => T.VPair{seg, T.VHead{p1, zz}} <> rows, x1,
            D1.tb.set(rest, p1, [], bb),
            ih([], eo))))
    case T.KHead{+p, +sub}:
      +p1 = {T.tree.pre(pre, seg) : String}
      +sa = {D1.tb.set(rest, p1, sub, aa) : List<&2, T.Val>}
      +x1 = {D1.tb.set(rest, p1, sa, bb) : List<&2, T.Val>}
      +r1 = {T.rows.repl(rows, seg, T.VHead{p, sa}) : List<&2, T.Val>}
      +el = {Equal.trans(T.Look, T.rows.look(r1, seg), lk.r(T.rows.look(rows, seg), T.VHead{p, sa}), T.KHead{p, sa},
        wa.lr(rows, seg, T.VHead{p, sa}),
        Equal.cong(T.Look, T.Look, l2 => lk.r(l2, T.VHead{p, sa}), T.rows.look(rows, seg), T.KHead{p, sub}, e))
        : {T.rows.look(r1, seg) == T.KHead{p, sa} : T.Look}}
      Equal.trans(List<&2, T.Val>,
        D1.tb.put.in(T.rows.look(r1, seg), seg, r1, pre, D1.tb.set(rest, p1, D1.tb.into(T.rows.look(r1, seg)),
          bb)),
        T.rows.repl(r1, seg, T.VHead{p, x1}),
        T.rows.repl(rows, seg, T.VHead{p, D1.tb.set(rest, p1, sub, bb)}),
        Equal.cong(T.Look, List<&2, T.Val>, l2 => D1.tb.put.in(l2, seg, r1, pre, D1.tb.set(rest, p1,
          D1.tb.into(l2), bb)),
          T.rows.look(r1, seg), T.KHead{p, sa}, el),
        Equal.trans(List<&2, T.Val>, T.rows.repl(r1, seg, T.VHead{p, x1}), T.rows.repl(rows, seg, T.VHead{p, x1}),
          T.rows.repl(rows, seg, T.VHead{p, D1.tb.set(rest, p1, sub, bb)}),
          wa.rr(rows, seg, T.VHead{p, sa}, T.VHead{p, x1}),
          Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zz => T.rows.repl(rows, seg, T.VHead{p, zz}), x1,
            D1.tb.set(rest, p1, sub, bb),
            ih(sub, eo))))
    case T.KAots{+p, es}:
      match es:
        case []:
          Eq.bit.absurd(&1, wa.G(T.KAots{p, []}, seg, rest, pre, rows, aa, bb), eo)

        case T.VStr{+a1} <> +older:
          Eq.bit.absurd(&1, wa.G(T.KAots{p, T.VStr{a1} <> older}, seg, rest, pre, rows, aa, bb), eo)
        case T.VSpan{+a1, +a2} <> +older:
          Eq.bit.absurd(&1, wa.G(T.KAots{p, T.VSpan{a1, a2} <> older}, seg, rest, pre, rows, aa, bb), eo)
        case T.VInt{+a1, +a2} <> +older:
          Eq.bit.absurd(&1, wa.G(T.KAots{p, T.VInt{a1, a2} <> older}, seg, rest, pre, rows, aa, bb), eo)
        case T.VFlo{+a1, +a2} <> +older:
          Eq.bit.absurd(&1, wa.G(T.KAots{p, T.VFlo{a1, a2} <> older}, seg, rest, pre, rows, aa, bb), eo)
        case T.VBool{+a1} <> +older:
          Eq.bit.absurd(&1, wa.G(T.KAots{p, T.VBool{a1} <> older}, seg, rest, pre, rows, aa, bb), eo)
        case T.VWhen{+a1} <> +older:
          Eq.bit.absurd(&1, wa.G(T.KAots{p, T.VWhen{a1} <> older}, seg, rest, pre, rows, aa, bb), eo)
        case T.VArr{+a1} <> +older:
          Eq.bit.absurd(&1, wa.G(T.KAots{p, T.VArr{a1} <> older}, seg, rest, pre, rows, aa, bb), eo)
        case T.VInl{+a1} <> +older:
          Eq.bit.absurd(&1, wa.G(T.KAots{p, T.VInl{a1} <> older}, seg, rest, pre, rows, aa, bb), eo)
        case T.VHead{+a1, +a2} <> +older:
          Eq.bit.absurd(&1, wa.G(T.KAots{p, T.VHead{a1, a2} <> older}, seg, rest, pre, rows, aa, bb), eo)
        case T.VAot{+q, +r} <> +older:
          +p1 = {T.tree.pre(pre, seg) : String}
          +sa = {D1.tb.set(rest, p1, r, aa) : List<&2, T.Val>}
          +x1 = {D1.tb.set(rest, p1, sa, bb) : List<&2, T.Val>}
          +r1 = {T.rows.repl(rows, seg, T.VAots{p, T.VAot{p, sa} <> older}) : List<&2, T.Val>}
          +el = {Equal.trans(T.Look, T.rows.look(r1, seg), lk.r(T.rows.look(rows, seg), T.VAots{p, T.VAot{p,
            sa} <> older}),
            T.KAots{p, T.VAot{p, sa} <> older},
            wa.lr(rows, seg, T.VAots{p, T.VAot{p, sa} <> older}),
            Equal.cong(T.Look, T.Look, l2 => lk.r(l2, T.VAots{p, T.VAot{p, sa} <> older}), T.rows.look(rows, seg),
              T.KAots{p, T.VAot{q, r} <> older}, e))
            : {T.rows.look(r1, seg) == T.KAots{p, T.VAot{p, sa} <> older} : T.Look}}
          Equal.trans(List<&2, T.Val>,
            D1.tb.put.in(T.rows.look(r1, seg), seg, r1, pre, D1.tb.set(rest, p1, D1.tb.into(T.rows.look(r1, seg)),
              bb)),
            T.rows.repl(r1, seg, T.VAots{p, T.VAot{p, x1} <> older}),
            T.rows.repl(rows, seg, T.VAots{p, T.VAot{p, D1.tb.set(rest, p1, r, bb)} <> older}),
            Equal.cong(T.Look, List<&2, T.Val>, l2 => D1.tb.put.in(l2, seg, r1, pre, D1.tb.set(rest, p1,
              D1.tb.into(l2), bb)),
              T.rows.look(r1, seg), T.KAots{p, T.VAot{p, sa} <> older}, el),
            Equal.trans(List<&2, T.Val>, T.rows.repl(r1, seg, T.VAots{p, T.VAot{p, x1} <> older}),
              T.rows.repl(rows, seg, T.VAots{p, T.VAot{p, x1} <> older}),
              T.rows.repl(rows, seg, T.VAots{p, T.VAot{p, D1.tb.set(rest, p1, r, bb)} <> older}),
              wa.rr(rows, seg, T.VAots{p, T.VAot{p, sa} <> older}, T.VAots{p, T.VAot{p, x1} <> older}),
              Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zz => T.rows.repl(rows, seg, T.VAots{p, T.VAot{p,
                zz} <> older}), x1,
                D1.tb.set(rest, p1, r, bb), ih(r, eo))))
        case T.VAots{+a1, +a2} <> +older:
          Eq.bit.absurd(&1, wa.G(T.KAots{p, T.VAots{a1, a2} <> older}, seg, rest, pre, rows, aa, bb), eo)
        case T.VPair{+a1, +a2} <> +older:
          Eq.bit.absurd(&1, wa.G(T.KAots{p, T.VPair{a1, a2} <> older}, seg, rest, pre, rows, aa, bb), eo)
    case T.KInl{}:
      Eq.bit.absurd(&1, wa.G(T.KInl{}, seg, rest, pre, rows, aa, bb), eo)
    case T.KNo{+why}:
      Eq.bit.absurd(&1, wa.G(T.KNo{why}, seg, rest, pre, rows, aa, bb), eo)

# a second set along a path the walk goes on through replaces the first
def wa.ss(
  path: List<&2, String>,
  +pre: String,
  +rows: List<&2, T.Val>,
  +aa: List<&2, T.Val>,
  +bb: List<&2, T.Val>,
  eo: {D1.tb.open(path, rows) == True{} : Bool}
) -> {D1.tb.set(path, pre, D1.tb.set(path, pre, rows, aa), bb) == D1.tb.set(path, pre, rows,
  bb) : List<&2, T.Val>}:
  match path:
    case []:
      {==}
    case +seg <> +rest:
      wa.ss.l(T.rows.look(rows, seg), seg, rest, pre, rows, aa, bb, {==}, eo,
        +r2 => e2 => wa.ss(rest, T.tree.pre(pre, seg), r2, aa, bb, e2))

# a set along a longer path is a set along the shorter one of a set in the
# table there
def wa.sa(
  aa: List<&2, String>,
  +bb: List<&2, String>,
  +pre: String,
  +rows: List<&2, T.Val>,
  +new: List<&2, T.Val>
) -> {D1.tb.set(List.append(&2, String, aa, bb), pre, rows, new) == D1.tb.set(aa, pre, rows, D1.tb.set(bb,
  D1.tb.join(aa, pre), D1.tb.rows(aa, rows), new)) : List<&2, T.Val>}:
  match aa:
    case []:
      {==}
    case +seg <> +rest:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zz => D1.tb.put.in(T.rows.look(rows, seg), seg, rows, pre, zz),
        D1.tb.set(List.append(&2, String, rest, bb), T.tree.pre(pre, seg), D1.tb.into(T.rows.look(rows, seg)), new),
        D1.tb.set(rest, T.tree.pre(pre, seg), D1.tb.into(T.rows.look(rows, seg)), D1.tb.set(bb,
          D1.tb.join(rest, T.tree.pre(pre, seg)), D1.tb.rows(rest, D1.tb.into(T.rows.look(rows, seg))), new)),
        wa.sa(rest, bb, T.tree.pre(pre, seg), D1.tb.into(T.rows.look(rows, seg)), new))

# a walk goes on through a longer path when it goes on through both parts
def wa.oa(
  aa: List<&2, String>,
  +bb: List<&2, String>,
  +rows: List<&2, T.Val>,
  +e1: {D1.tb.open(aa, rows) == True{} : Bool},
  e2: {D1.tb.open(bb, D1.tb.rows(aa, rows)) == True{} : Bool}
) -> {D1.tb.open(List.append(&2, String, aa, bb), rows) == True{} : Bool}:
  match aa:
    case []:
      e2
    case +seg <> +rest:
      M15.cv.and2(D1.tb.can(T.rows.look(rows, seg)), D1.tb.open(List.append(&2, String, rest, bb),
        D1.tb.into(T.rows.look(rows, seg))),
        Eq.and.left(D1.tb.can(T.rows.look(rows, seg)), D1.tb.open(rest, D1.tb.into(T.rows.look(rows, seg))), e1),
        wa.oa(rest, bb, D1.tb.into(T.rows.look(rows, seg)),
          Eq.and.right(D1.tb.can(T.rows.look(rows, seg)), D1.tb.open(rest, D1.tb.into(T.rows.look(rows, seg))),
            e1), e2))

# entering the table a pair at the head of the current table's rows holds:
# a set there is a set of the current table with that pair's table replaced
def wa.enter(
  +he: List<&2, String>,
  +r0: List<&2, T.Val>,
  +nn: String,
  +xx: T.Val,
  +cs: List<&2, T.Val>,
  +new: List<&2, T.Val>,
  +eo: {D1.tb.open(he, r0) == True{} : Bool},
  +em: {L4.is_miss(T.get(cs, nn)) == True{} : Bool},
  +ok: {slot.ok(xx) == True{} : Bool}
) -> {D1.tb.set(List.append(&2, String, he, [nn]), "", D1.tb.set(he, "", r0, T.VPair{nn, xx} <> cs), new)
  == D1.tb.set(he, "", r0, T.VPair{nn, slot(xx, new)} <> cs) : List<&2, T.Val>}:
  +r1 = {D1.tb.set(he, "", r0, T.VPair{nn, xx} <> cs) : List<&2, T.Val>}
  Equal.trans(List<&2, T.Val>, D1.tb.set(List.append(&2, String, he, [nn]), "", r1, new),
    D1.tb.set(he, "", r1, D1.tb.set([nn], D1.tb.join(he, ""), D1.tb.rows(he, r1), new)),
    D1.tb.set(he, "", r0, T.VPair{nn, slot(xx, new)} <> cs),
    wa.sa(he, [nn], "", r1, new),
    Equal.trans(List<&2, T.Val>, D1.tb.set(he, "", r1, D1.tb.set([nn], D1.tb.join(he, ""), D1.tb.rows(he, r1),
      new)),
      D1.tb.set(he, "", r1, T.VPair{nn, slot(xx, new)} <> cs),
      D1.tb.set(he, "", r0, T.VPair{nn, slot(xx, new)} <> cs),
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zz => D1.tb.set(he, "", r1, zz),
        D1.tb.set([nn], D1.tb.join(he, ""), D1.tb.rows(he, r1), new), T.VPair{nn, slot(xx, new)} <> cs,
        Equal.trans(List<&2, T.Val>, D1.tb.set([nn], D1.tb.join(he, ""), D1.tb.rows(he, r1), new),
          D1.tb.set([nn], D1.tb.join(he, ""), T.VPair{nn, xx} <> cs, new), T.VPair{nn, slot(xx, new)} <> cs,
          Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zz => D1.tb.set([nn], D1.tb.join(he, ""), zz, new),
            D1.tb.rows(he, r1),
            T.VPair{nn, xx} <> cs, L14.tb_rows_after_set(he, "", r0, T.VPair{nn, xx} <> cs, eo)),
          wa.head(nn, xx, cs, D1.tb.join(he, ""), new, em, ok))),
      wa.ss(he, "", r0, T.VPair{nn, xx} <> cs, T.VPair{nn, slot(xx, new)} <> cs, eo)))

# and the walk goes on through that table
def wa.eopen(
  +he: List<&2, String>,
  +r0: List<&2, T.Val>,
  +nn: String,
  +xx: T.Val,
  +cs: List<&2, T.Val>,
  +eo: {D1.tb.open(he, r0) == True{} : Bool},
  +ok: {slot.ok(xx) == True{} : Bool}
) -> {D1.tb.open(List.append(&2, String, he, [nn]), D1.tb.set(he, "", r0, T.VPair{nn, xx} <> cs)) == True{}
  : Bool}:
  +r1 = {D1.tb.set(he, "", r0, T.VPair{nn, xx} <> cs) : List<&2, T.Val>}
  wa.oa(he, [nn], r1, L13.tb_open_after_set(he, "", r0, T.VPair{nn, xx} <> cs, eo),
    Equal.trans(Bool, D1.tb.open([nn], D1.tb.rows(he, r1)), D1.tb.open([nn], T.VPair{nn, xx} <> cs), True{},
      Equal.cong(List<&2, T.Val>, Bool, zz => D1.tb.open([nn], zz), D1.tb.rows(he, r1), T.VPair{nn, xx} <> cs,
        L14.tb_rows_after_set(he, "", r0, T.VPair{nn, xx} <> cs, eo)),
      wa.head.open(nn, xx, cs, ok)))

# the text of a value in a value position, then more text
def cv.tx.app(
  vv: T.Val,
  +aa: String,
  +bb: String
) -> {String.append(D1.cv.tx(vv, aa), bb) == D1.cv.tx(vv, String.append(aa, bb)) : String}:
  match vv:
    case T.VArr{+its}:
      Equal.cong(String, String, zz => SCon{'[', zz}, String.append(String.append(T.render.go(its, ", ", False{}),
        SCon{']', aa}), bb), String.append(T.render.go(its, ", ", False{}), SCon{']', String.append(aa, bb)}),
        Eq.append_assoc(T.render.go(its, ", ", False{}), SCon{']', aa}, bb))
    case T.VInl{+rs}:
      Equal.cong(String, String, zz => SCon{'{', zz}, String.append(String.append(T.render.go(rs, ", ", False{}),
        SCon{'}', aa}), bb), String.append(T.render.go(rs, ", ", False{}), SCon{'}', String.append(aa, bb)}),
        Eq.append_assoc(T.render.go(rs, ", ", False{}), SCon{'}', aa}, bb))

    case T.VStr{+a1}:
      Eq.append_assoc(T.render.atom(T.VStr{a1}), aa, bb)
    case T.VSpan{+a1, +a2}:
      Eq.append_assoc(T.render.atom(T.VSpan{a1, a2}), aa, bb)
    case T.VInt{+a1, +a2}:
      Eq.append_assoc(T.render.atom(T.VInt{a1, a2}), aa, bb)
    case T.VFlo{+a1, +a2}:
      Eq.append_assoc(T.render.atom(T.VFlo{a1, a2}), aa, bb)
    case T.VBool{+a1}:
      Eq.append_assoc(T.render.atom(T.VBool{a1}), aa, bb)
    case T.VWhen{+a1}:
      Eq.append_assoc(T.render.atom(T.VWhen{a1}), aa, bb)
    case T.VHead{+a1, +a2}:
      Eq.append_assoc(T.render.atom(T.VHead{a1, a2}), aa, bb)
    case T.VAot{+a1, +a2}:
      Eq.append_assoc(T.render.atom(T.VAot{a1, a2}), aa, bb)
    case T.VAots{+a1, +a2}:
      Eq.append_assoc(T.render.atom(T.VAots{a1, a2}), aa, bb)
    case T.VPair{+a1, +a2}:
      Eq.append_assoc(T.render.atom(T.VPair{a1, a2}), aa, bb)

# a key line's text, then more text
def kp.txt(
  +kk: String,
  +vv: T.Val,
  +aa: String,
  +bb: String
) -> {String.append(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(vv, aa)}}}), bb)
  == String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(vv, String.append(aa, bb))}}}) : String}:
  Equal.trans(String, String.append(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(vv, aa)}}}), bb),
    String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', String.append(D1.cv.tx(vv, aa), bb)}}}),
    String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(vv, String.append(aa, bb))}}}),
    Eq.append_assoc(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(vv, aa)}}}, bb),
    Equal.cong(String, String, zz => String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', zz}}}),
      String.append(D1.cv.tx(vv, aa), bb), D1.cv.tx(vv, String.append(aa, bb)), cv.tx.app(vv, aa, bb)))

# one row put in front of rows that own reads, sealed, as mm: own reads the
# sealed rows as mm then what it reads the row alone as, sealed
def os.step(
  +xx: T.Val,
  +cs: List<&2, T.Val>,
  +mm: List<&2, T.Val>,
  +yy: T.Val,
  +ho: {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>},
  +h1: {D1.own.rows(T.rows.seal([xx])) == D1.own.rows([yy]) : List<&2, T.Val>}
) -> {D1.own.rows(T.rows.seal(xx <> cs)) == D1.own.rows(List.append(&2, T.Val, mm, [yy])) : List<&2, T.Val>}:
  +h2 = {Equal.trans(List<&2, T.Val>, D1.own.rows([D6.sealed(xx)]), D1.own.rows(T.rows.seal([xx])),
    D1.own.rows([yy]),
    Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => D1.own.rows(zs), [D6.sealed(xx)], T.rows.seal([xx]),
      Equal.sym(List<&2, T.Val>, T.rows.seal([xx]), [D6.sealed(xx)], L11.seal_puts_newest_last(xx, []))), h1)
    : {D1.own.rows([D6.sealed(xx)]) == D1.own.rows([yy]) : List<&2, T.Val>}}
  Equal.trans(List<&2, T.Val>, D1.own.rows(T.rows.seal(xx <> cs)),
    D1.own.rows(List.append(&2, T.Val, T.rows.seal(cs), [D6.sealed(xx)])),
    D1.own.rows(List.append(&2, T.Val, mm, [yy])),
    Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => D1.own.rows(zs), T.rows.seal(xx <> cs),
      List.append(&2, T.Val, T.rows.seal(cs), [D6.sealed(xx)]), L11.seal_puts_newest_last(xx, cs)),
    Equal.trans(List<&2, T.Val>, D1.own.rows(List.append(&2, T.Val, T.rows.seal(cs), [D6.sealed(xx)])),
      List.append(&2, T.Val, D1.own.rows(T.rows.seal(cs)), D1.own.rows([D6.sealed(xx)])),
      D1.own.rows(List.append(&2, T.Val, mm, [yy])),
      cv.own.app(T.rows.seal(cs), [D6.sealed(xx)]),
      Equal.trans(List<&2, T.Val>, List.append(&2, T.Val, D1.own.rows(T.rows.seal(cs)),
        D1.own.rows([D6.sealed(xx)])),
        List.append(&2, T.Val, D1.own.rows(mm), D1.own.rows([yy])),
        D1.own.rows(List.append(&2, T.Val, mm, [yy])),
        Equal.trans(List<&2, T.Val>, List.append(&2, T.Val, D1.own.rows(T.rows.seal(cs)),
          D1.own.rows([D6.sealed(xx)])),
          List.append(&2, T.Val, D1.own.rows(mm), D1.own.rows([D6.sealed(xx)])),
          List.append(&2, T.Val, D1.own.rows(mm), D1.own.rows([yy])),
          Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => List.append(&2, T.Val, zs,
            D1.own.rows([D6.sealed(xx)])),
            D1.own.rows(T.rows.seal(cs)), D1.own.rows(mm), ho),
          Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => List.append(&2, T.Val, D1.own.rows(mm), zs),
            D1.own.rows([D6.sealed(xx)]), D1.own.rows([yy]), h2)),
        Equal.sym(List<&2, T.Val>, D1.own.rows(List.append(&2, T.Val, mm, [yy])),
          List.append(&2, T.Val, D1.own.rows(mm), D1.own.rows([yy])), cv.own.app(mm, [yy])))))

# a scalar pair alone is well-formed in an inline table, from the scalar and
# its name
def hi.at(
  aa: Bool,
  bb: Bool,
  ea: {aa == True{} : Bool},
  eb: {bb == True{} : Bool}
) -> {T.wf.then(Bool.and(aa, Bool.and(bb, True{})), _u => True{}) == True{} : Bool}:
  match aa:
    case True{}:
      match bb:
        case True{}:
          {==}
        case False{}:
          eb
    case False{}:
      ea

# and a pair of an array or an inline table, from its name and its list
def hi.cn(
  bb: Bool,
  cc: Bool,
  eb: {bb == True{} : Bool},
  ec: {cc == True{} : Bool}
) -> {T.wf.then(Bool.and(bb, True{}), _u => T.wf.then(cc, _v => True{})) == True{} : Bool}:
  match bb:
    case True{}:
      match cc:
        case True{}:
          {==}
        case False{}:
          ec
    case False{}:
      eb

# the rest of the text after the key pass over pairs of which ks are no
# table: from the start of the next line in the same table, its rows holding
# those pairs in front, sealed and read out as mm then ks, and every later
# name tz none of theirs
def kp.Then(
  +r0: List<&2, T.Val>,
  +he: List<&2, String>,
  +hs: List<&2, String>,
  +ab: Bool,
  +mm: List<&2, T.Val>,
  +ks: List<&2, T.Val>,
  +tz: List<&2, T.Val>,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  @c2: List<&2, T.Val> -> @b2: T.Lex -> @q2: T.QKind -> @u2: U32 -> @l2: U32 ->
    {M8.cv.fr(c2, tz) == True{} : Bool} ->
    {D1.own.rows(T.rows.seal(c2)) == D1.own.rows(List.append(&2, T.Val, mm, ks)) : List<&2, T.Val>} ->
    PP(T.doc.read(rest, T.MScan{M5.dl(D1.tb.set(he, "", r0, c2), hs, he, b2, q2, u2, l2, ab)}))

# what the key pass over the pairs after the first gives: from any rows c2
# fresh for the names after them, it reads the rest as kp.Then says
def kp.Rec(
  +t: List<&2, T.Val>,
  +r0: List<&2, T.Val>,
  +he: List<&2, String>,
  +hs: List<&2, String>,
  +ab: Bool,
  +tz: List<&2, T.Val>,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  @c2: List<&2, T.Val> -> @m2: List<&2, T.Val> -> @b2: T.Lex -> @q2: T.QKind -> @u2: U32 -> @l2: U32 ->
    {M8.cv.fr(c2, List.append(&2, T.Val, D2.canon.keys(t), tz)) == True{} : Bool} ->
    {M8.nd(List.append(&2, T.Val, D2.canon.keys(t), tz)) == True{} : Bool} ->
    {D1.own.rows(T.rows.seal(c2)) == D1.own.rows(m2) : List<&2, T.Val>} ->
    kp.Then(r0, he, hs, ab, m2, D2.canon.keys(t), tz, rest, PP) ->
    PP(T.doc.read(String.append(T.render.pass(t, "\n", True{}, False{}), rest), T.MScan{M5.dl(D1.tb.set(he, "", r0, c2),
      hs,
      he, b2, q2, u2, l2, ab)}))

# one pair of the key pass: its line puts it, and the pass goes on
def kp.one(
  +kk: String,
  +v: T.Val,
  +t: List<&2, T.Val>,
  +r0: List<&2, T.Val>,
  +he: List<&2, String>,
  +hs: List<&2, String>,
  +ab: Bool,
  +cs: List<&2, T.Val>,
  +mm: List<&2, T.Val>,
  +tz: List<&2, T.Val>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +rest: String,
  -PP: T.Doc -> Type,
  +eo: {D1.tb.open(he, r0) == True{} : Bool},
  +ec: {D1.counts.down(he, T.path.len(he, 0)) == True{} : Bool},
  +hw1: {D1.cv.wf(v) == True{} : Bool},
  +hl1: {D1.cv.short1(v) == True{} : Bool},
  +hi: {T.wf.go([T.VPair{kk, v}], T.WfInl{}) == True{} : Bool},
  +hf: {M8.cv.fr(cs, T.VPair{kk, v} <> List.append(&2, T.Val, D2.canon.keys(t), tz)) == True{} : Bool},
  +hn: {M8.nd(T.VPair{kk, v} <> List.append(&2, T.Val, D2.canon.keys(t), tz)) == True{} : Bool},
  +ho: {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>},
  ih: kp.Then(r0, he, hs, ab, mm, T.VPair{kk, v} <> D2.canon.keys(t), tz, rest, PP),
  rec: kp.Rec(t, r0, he, hs, ab, tz, rest, PP)
) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{kk, v} <> t, "\n", True{}, False{}), rest),
  T.MScan{M5.dl(D1.tb.set(he, "", r0, cs), hs, he, bk, qk, un, lf, ab)})):
  +rw = {D1.tb.set(he, "", r0, cs) : List<&2, T.Val>}
  +zz = {List.append(&2, T.Val, D2.canon.keys(t), tz) : List<&2, T.Val>}
  +rt = {String.append(T.render.pass(t, "\n", True{}, False{}), rest) : String}
  +erw = {L14.tb_rows_after_set(he, "", r0, cs, eo) : {D1.tb.rows(he, rw) == cs : List<&2, T.Val>}}
  +em = {Equal.trans(T.Hit, T.get(D1.tb.rows(he, rw), kk), T.get(cs, kk), T.Miss{},
    Equal.cong(List<&2, T.Val>, T.Hit, zs => T.get(zs, kk), D1.tb.rows(he, rw), cs, erw),
    cv.miss(T.get(cs, kk), Eq.and.left(L4.is_miss(T.get(cs, kk)), M8.cv.fr(cs, zz), hf)))
    : {T.get(D1.tb.rows(he, rw), kk) == T.Miss{} : T.Hit}}
  pp.step(PP,
    T.doc.read(String.append(T.render.pass(T.VPair{kk, v} <> t, "\n", True{}, False{}), rest),
      T.MScan{M5.dl(rw, hs, he, bk, qk, un, lf, ab)}),
    T.doc.read(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(v, SCon{'\n', rt})}}}),
      T.MScan{M5.dl(rw, hs, he, bk, qk, un, lf, ab)}),
    Equal.cong(String, T.Doc, ss => T.doc.read(ss, T.MScan{M5.dl(rw, hs, he, bk, qk, un, lf, ab)}),
      String.append(T.render.pass(T.VPair{kk, v} <> t, "\n", True{}, False{}), rest),
      String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(v, SCon{'\n', rt})}}}),
      Equal.trans(String,
        String.append(T.render.pass(T.VPair{kk, v} <> t, "\n", True{}, False{}), rest),
        String.append(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(v, SCon{'\n',
          T.render.pass(t, "\n", True{}, False{})})}}}), rest),
        String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(v, SCon{'\n', rt})}}}),
        Equal.cong(String, String, ss => String.append(ss, rest),
          T.render.pass(T.VPair{kk, v} <> t, "\n", True{}, False{}),
          String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(v, SCon{'\n',
            T.render.pass(t, "\n", True{}, False{})})}}}),
          L9.pass_value(kk, v, hw1, t, "\n", True{})),
        kp.txt(kk, v, SCon{'\n', T.render.pass(t, "\n", True{}, False{})}, rest))),
    dl.line(kk, v, hw1, hl1, rw, hs, he, bk, qk, un, lf, ab, rt, PP,
      L13.tb_open_after_set(he, "", r0, cs, eo), ec, em,
      +vv => +b2 => +q2 => +u2 => +l2 => h1 => pp.step(PP,
        T.doc.read(rt, T.MScan{M5.dl(D1.tb.set(he, "", rw, T.VPair{kk, vv} <> D1.tb.rows(he, rw)), hs, he, b2, q2, u2,
          l2, ab)}),
        T.doc.read(rt, T.MScan{M5.dl(D1.tb.set(he, "", r0, T.VPair{kk, vv} <> cs), hs, he, b2, q2, u2, l2, ab)}),
        Equal.cong(List<&2, T.Val>, T.Doc, zs => T.doc.read(rt, T.MScan{M5.dl(zs, hs, he, b2, q2, u2, l2, ab)}),
          D1.tb.set(he, "", rw, T.VPair{kk, vv} <> D1.tb.rows(he, rw)),
          D1.tb.set(he, "", r0, T.VPair{kk, vv} <> cs),
          Equal.trans(List<&2, T.Val>, D1.tb.set(he, "", rw, T.VPair{kk, vv} <> D1.tb.rows(he, rw)),
            D1.tb.set(he, "", rw, T.VPair{kk, vv} <> cs), D1.tb.set(he, "", r0, T.VPair{kk, vv} <> cs),
            Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => D1.tb.set(he, "", rw, T.VPair{kk, vv} <> zs),
              D1.tb.rows(he, rw), cs, erw),
            wa.ss(he, "", r0, cs, T.VPair{kk, vv} <> cs, eo))),
        rec(T.VPair{kk, vv} <> cs, List.append(&2, T.Val, mm, [T.VPair{kk, v}]), b2, q2, u2, l2,
          cv.fr.step(zz, kk, vv, cs, Eq.and.right(L4.is_miss(T.get(cs, kk)), M8.cv.fr(cs, zz), hf),
            Eq.and.left(T.wf.fresh(T.get(zz, kk)), M8.nd(zz), hn)),
          Eq.and.right(T.wf.fresh(T.get(zz, kk)), M8.nd(zz), hn),
          os.step(T.VPair{kk, vv}, cs, mm, T.VPair{kk, v}, ho, rv.own(kk, vv, v, h1, hw1, hi)),
          +c3 => +b3 => +q3 => +u3 => +l3 => f3 => o3 => ih(c3, b3, q3, u3, l3, f3,
            Equal.trans(List<&2, T.Val>, D1.own.rows(T.rows.seal(c3)),
              D1.own.rows(List.append(&2, T.Val, List.append(&2, T.Val, mm, [T.VPair{kk, v}]), D2.canon.keys(t))),
              D1.own.rows(List.append(&2, T.Val, mm, T.VPair{kk, v} <> D2.canon.keys(t))), o3,
              Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => D1.own.rows(zs),
                List.append(&2, T.Val, List.append(&2, T.Val, mm, [T.VPair{kk, v}]), D2.canon.keys(t)),
                List.append(&2, T.Val, mm, T.VPair{kk, v} <> D2.canon.keys(t)),
                M8.va.assoc(mm, [T.VPair{kk, v}], D2.canon.keys(t)))))))))

# the key pass over a table's rows, from the start of a line in that table:
# every pair that is no table is read and put, the tables are left for the
# table pass
def kp(
  ys: List<&2, T.Val>,
  +hp: String,
  +r0: List<&2, T.Val>,
  +he: List<&2, String>,
  +hs: List<&2, String>,
  +ab: Bool,
  +cs: List<&2, T.Val>,
  +mm: List<&2, T.Val>,
  +tz: List<&2, T.Val>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +rest: String,
  -PP: T.Doc -> Type,
  +eo: {D1.tb.open(he, r0) == True{} : Bool},
  +ec: {D1.counts.down(he, T.path.len(he, 0)) == True{} : Bool},
  +hw: {T.wf.go(ys, T.WfRows{hp}) == True{} : Bool},
  +hl: {D4.short.rows(ys) == True{} : Bool},
  +hf: {M8.cv.fr(cs, List.append(&2, T.Val, D2.canon.keys(ys), tz)) == True{} : Bool},
  +hn: {M8.nd(List.append(&2, T.Val, D2.canon.keys(ys), tz)) == True{} : Bool},
  ho: {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>},
  ih: kp.Then(r0, he, hs, ab, mm, D2.canon.keys(ys), tz, rest, PP)
) -> PP(T.doc.read(String.append(T.render.pass(ys, "\n", True{}, False{}), rest), T.MScan{M5.dl(D1.tb.set(he, "", r0,
  cs),
  hs, he, bk, qk, un, lf, ab)})):
  match ys:
    case []:
      ih(cs, bk, qk, un, lf, hf, Equal.trans(List<&2, T.Val>, D1.own.rows(T.rows.seal(cs)), D1.own.rows(mm),
        D1.own.rows(List.append(&2, T.Val, mm, [])), ho, Equal.cong(List<&2, T.Val>, List<&2, T.Val>,
          zs => D1.own.rows(zs), mm,
        List.append(&2, T.Val, mm, []), Equal.sym(List<&2, T.Val>, List.append(&2, T.Val, mm, []), mm, va.nil(mm)))))
    case T.VPair{+kk, T.VHead{+p, +r}} <> +t:
      kp(t, hp, r0, he, hs, ab, cs, mm, tz, bk, qk, un, lf, rest, PP, eo, ec,
        M15.wt.more(T.wf.go(r, T.WfRows{p}), _v => T.wf.go(t, T.WfRows{hp}), M15.wt.more(Bool.and(T.wf.key(kk, t),
          T.str.eq(p, T.tree.pre(hp, kk))), _u => T.wf.then(T.wf.go(r, T.WfRows{p}), _v => T.wf.go(t, T.WfRows{hp})),
          hw)),
        Eq.and.right(D4.short.rows(r), D4.short.rows(t), Eq.and.right(D1.short(p), Bool.and(D4.short.rows(r),
          D4.short.rows(t)), hl)), hf, hn, ho, ih)
    case T.VPair{+kk, T.VAots{+p, +es}} <> +t:
      kp(t, hp, r0, he, hs, ab, cs, mm, tz, bk, qk, un, lf, rest, PP, eo, ec,
        M15.wt.more(T.wf.go(es, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}),
            M15.wt.more(Bool.and(Bool.not(List.is_empty(&2,
          T.Val, es)), Bool.and(T.wf.key(kk, t), T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(es,
          T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp})), hw)),
        Eq.and.right(D4.short.rows(es), D4.short.rows(t), Eq.and.right(D1.short(p), Bool.and(D4.short.rows(es),
          D4.short.rows(t)), hl)), hf, hn, ho, ih)
    case T.VPair{+kk, T.VStr{+a1}} <> +t:
      +ha = {M15.wt.ok(Bool.and(T.wf.atom(T.VStr{a1}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}), hw)
        : {Bool.and(T.wf.atom(T.VStr{a1}), T.wf.key(kk, t)) == True{} : Bool}}
      +hwt = {M15.wt.more(Bool.and(T.wf.atom(T.VStr{a1}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}), hw)
        : {T.wf.go(t, T.WfRows{hp}) == True{} : Bool}}
      +hw1 = {Eq.and.left(T.wf.atom(T.VStr{a1}), T.wf.key(kk, t), ha) : {T.wf.atom(T.VStr{a1}) == True{} : Bool}}
      +htx = {Eq.and.left(T.wf.text(kk), T.wf.fresh(T.get(t, kk)), Eq.and.right(T.wf.atom(T.VStr{a1}), T.wf.key(kk, t),
        ha)) : {T.wf.text(kk) == True{} : Bool}}
      kp.one(kk, T.VStr{a1}, t, r0, he, hs, ab, cs, mm, tz, bk, qk, un, lf, rest, PP, eo, ec, hw1,
        Eq.and.left(D1.cv.short1(T.VStr{a1}), D4.short.rows(t), hl), hi.at(T.wf.atom(T.VStr{a1}), T.wf.text(kk),
          hw1, htx), hf, hn,
        ho, ih,
        +c2 => +m2 => +b2 => +q2 => +u2 => +l2 => f2 => n2 => o2 => i2 => kp(t, hp, r0, he, hs, ab, c2, m2, tz, b2, q2,
          u2,
          l2, rest, PP, eo, ec, hwt, Eq.and.right(D1.cv.short1(T.VStr{a1}), D4.short.rows(t), hl), f2, n2, o2, i2))
    case T.VPair{+kk, T.VSpan{+a1, +a2}} <> +t:
      +ha = {M15.wt.ok(Bool.and(T.wf.atom(T.VSpan{a1, a2}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}), hw)
        : {Bool.and(T.wf.atom(T.VSpan{a1, a2}), T.wf.key(kk, t)) == True{} : Bool}}
      +hwt = {M15.wt.more(Bool.and(T.wf.atom(T.VSpan{a1, a2}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}), hw)
        : {T.wf.go(t, T.WfRows{hp}) == True{} : Bool}}
      +hw1 = {Eq.and.left(T.wf.atom(T.VSpan{a1, a2}), T.wf.key(kk, t), ha) : {T.wf.atom(T.VSpan{a1,
        a2}) == True{} : Bool}}
      +htx = {Eq.and.left(T.wf.text(kk), T.wf.fresh(T.get(t, kk)), Eq.and.right(T.wf.atom(T.VSpan{a1, a2}), T.wf.key(kk,
        t),
        ha)) : {T.wf.text(kk) == True{} : Bool}}
      kp.one(kk, T.VSpan{a1, a2}, t, r0, he, hs, ab, cs, mm, tz, bk, qk, un, lf, rest, PP, eo, ec, hw1,
        Eq.and.left(D1.cv.short1(T.VSpan{a1, a2}), D4.short.rows(t), hl), hi.at(T.wf.atom(T.VSpan{a1, a2}),
          T.wf.text(kk), hw1, htx), hf, hn,
        ho, ih,
        +c2 => +m2 => +b2 => +q2 => +u2 => +l2 => f2 => n2 => o2 => i2 => kp(t, hp, r0, he, hs, ab, c2, m2, tz, b2, q2,
          u2,
          l2, rest, PP, eo, ec, hwt, Eq.and.right(D1.cv.short1(T.VSpan{a1, a2}), D4.short.rows(t), hl), f2, n2, o2,
            i2))
    case T.VPair{+kk, T.VInt{+a1, +a2}} <> +t:
      +ha = {M15.wt.ok(Bool.and(T.wf.atom(T.VInt{a1, a2}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}), hw)
        : {Bool.and(T.wf.atom(T.VInt{a1, a2}), T.wf.key(kk, t)) == True{} : Bool}}
      +hwt = {M15.wt.more(Bool.and(T.wf.atom(T.VInt{a1, a2}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}), hw)
        : {T.wf.go(t, T.WfRows{hp}) == True{} : Bool}}
      +hw1 = {Eq.and.left(T.wf.atom(T.VInt{a1, a2}), T.wf.key(kk, t), ha) : {T.wf.atom(T.VInt{a1,
        a2}) == True{} : Bool}}
      +htx = {Eq.and.left(T.wf.text(kk), T.wf.fresh(T.get(t, kk)), Eq.and.right(T.wf.atom(T.VInt{a1, a2}), T.wf.key(kk,
        t),
        ha)) : {T.wf.text(kk) == True{} : Bool}}
      kp.one(kk, T.VInt{a1, a2}, t, r0, he, hs, ab, cs, mm, tz, bk, qk, un, lf, rest, PP, eo, ec, hw1,
        Eq.and.left(D1.cv.short1(T.VInt{a1, a2}), D4.short.rows(t), hl), hi.at(T.wf.atom(T.VInt{a1, a2}),
          T.wf.text(kk), hw1, htx), hf, hn,
        ho, ih,
        +c2 => +m2 => +b2 => +q2 => +u2 => +l2 => f2 => n2 => o2 => i2 => kp(t, hp, r0, he, hs, ab, c2, m2, tz, b2, q2,
          u2,
          l2, rest, PP, eo, ec, hwt, Eq.and.right(D1.cv.short1(T.VInt{a1, a2}), D4.short.rows(t), hl), f2, n2, o2,
            i2))
    case T.VPair{+kk, T.VFlo{+a1, +a2}} <> +t:
      +ha = {M15.wt.ok(Bool.and(T.wf.atom(T.VFlo{a1, a2}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}), hw)
        : {Bool.and(T.wf.atom(T.VFlo{a1, a2}), T.wf.key(kk, t)) == True{} : Bool}}
      +hwt = {M15.wt.more(Bool.and(T.wf.atom(T.VFlo{a1, a2}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}), hw)
        : {T.wf.go(t, T.WfRows{hp}) == True{} : Bool}}
      +hw1 = {Eq.and.left(T.wf.atom(T.VFlo{a1, a2}), T.wf.key(kk, t), ha) : {T.wf.atom(T.VFlo{a1,
        a2}) == True{} : Bool}}
      +htx = {Eq.and.left(T.wf.text(kk), T.wf.fresh(T.get(t, kk)), Eq.and.right(T.wf.atom(T.VFlo{a1, a2}), T.wf.key(kk,
        t),
        ha)) : {T.wf.text(kk) == True{} : Bool}}
      kp.one(kk, T.VFlo{a1, a2}, t, r0, he, hs, ab, cs, mm, tz, bk, qk, un, lf, rest, PP, eo, ec, hw1,
        Eq.and.left(D1.cv.short1(T.VFlo{a1, a2}), D4.short.rows(t), hl), hi.at(T.wf.atom(T.VFlo{a1, a2}),
          T.wf.text(kk), hw1, htx), hf, hn,
        ho, ih,
        +c2 => +m2 => +b2 => +q2 => +u2 => +l2 => f2 => n2 => o2 => i2 => kp(t, hp, r0, he, hs, ab, c2, m2, tz, b2, q2,
          u2,
          l2, rest, PP, eo, ec, hwt, Eq.and.right(D1.cv.short1(T.VFlo{a1, a2}), D4.short.rows(t), hl), f2, n2, o2,
            i2))
    case T.VPair{+kk, T.VBool{+a1}} <> +t:
      +ha = {M15.wt.ok(Bool.and(T.wf.atom(T.VBool{a1}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}), hw)
        : {Bool.and(T.wf.atom(T.VBool{a1}), T.wf.key(kk, t)) == True{} : Bool}}
      +hwt = {M15.wt.more(Bool.and(T.wf.atom(T.VBool{a1}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}), hw)
        : {T.wf.go(t, T.WfRows{hp}) == True{} : Bool}}
      +hw1 = {Eq.and.left(T.wf.atom(T.VBool{a1}), T.wf.key(kk, t), ha) : {T.wf.atom(T.VBool{a1}) == True{} : Bool}}
      +htx = {Eq.and.left(T.wf.text(kk), T.wf.fresh(T.get(t, kk)), Eq.and.right(T.wf.atom(T.VBool{a1}), T.wf.key(kk, t),
        ha)) : {T.wf.text(kk) == True{} : Bool}}
      kp.one(kk, T.VBool{a1}, t, r0, he, hs, ab, cs, mm, tz, bk, qk, un, lf, rest, PP, eo, ec, hw1,
        Eq.and.left(D1.cv.short1(T.VBool{a1}), D4.short.rows(t), hl), hi.at(T.wf.atom(T.VBool{a1}), T.wf.text(kk),
          hw1, htx), hf, hn,
        ho, ih,
        +c2 => +m2 => +b2 => +q2 => +u2 => +l2 => f2 => n2 => o2 => i2 => kp(t, hp, r0, he, hs, ab, c2, m2, tz, b2, q2,
          u2,
          l2, rest, PP, eo, ec, hwt, Eq.and.right(D1.cv.short1(T.VBool{a1}), D4.short.rows(t), hl), f2, n2, o2, i2))
    case T.VPair{+kk, T.VWhen{+a1}} <> +t:
      +ha = {M15.wt.ok(Bool.and(T.wf.atom(T.VWhen{a1}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}), hw)
        : {Bool.and(T.wf.atom(T.VWhen{a1}), T.wf.key(kk, t)) == True{} : Bool}}
      +hwt = {M15.wt.more(Bool.and(T.wf.atom(T.VWhen{a1}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}), hw)
        : {T.wf.go(t, T.WfRows{hp}) == True{} : Bool}}
      +hw1 = {Eq.and.left(T.wf.atom(T.VWhen{a1}), T.wf.key(kk, t), ha) : {T.wf.atom(T.VWhen{a1}) == True{} : Bool}}
      +htx = {Eq.and.left(T.wf.text(kk), T.wf.fresh(T.get(t, kk)), Eq.and.right(T.wf.atom(T.VWhen{a1}), T.wf.key(kk, t),
        ha)) : {T.wf.text(kk) == True{} : Bool}}
      kp.one(kk, T.VWhen{a1}, t, r0, he, hs, ab, cs, mm, tz, bk, qk, un, lf, rest, PP, eo, ec, hw1,
        Eq.and.left(D1.cv.short1(T.VWhen{a1}), D4.short.rows(t), hl), hi.at(T.wf.atom(T.VWhen{a1}), T.wf.text(kk),
          hw1, htx), hf, hn,
        ho, ih,
        +c2 => +m2 => +b2 => +q2 => +u2 => +l2 => f2 => n2 => o2 => i2 => kp(t, hp, r0, he, hs, ab, c2, m2, tz, b2, q2,
          u2,
          l2, rest, PP, eo, ec, hwt, Eq.and.right(D1.cv.short1(T.VWhen{a1}), D4.short.rows(t), hl), f2, n2, o2, i2))
    case T.VPair{+kk, T.VArr{+a1}} <> +t:
      +hin = {M15.wt.more(T.wf.key(kk, t), _u => T.wf.then(T.wf.go(a1, T.WfItems{}), _v => T.wf.go(t, T.WfRows{hp})),
          hw)
        : {T.wf.then(T.wf.go(a1, T.WfItems{}), _v => T.wf.go(t, T.WfRows{hp})) == True{} : Bool}}
      +hwt = {M15.wt.more(T.wf.go(a1, T.WfItems{}), _v => T.wf.go(t, T.WfRows{hp}), hin) : {T.wf.go(t,
        T.WfRows{hp}) == True{}
        : Bool}}
      +hw1 = {M15.wt.ok(T.wf.go(a1, T.WfItems{}), _v => T.wf.go(t, T.WfRows{hp}), hin) : {T.wf.go(a1,
        T.WfItems{}) == True{} : Bool}}
      +htx = {Eq.and.left(T.wf.text(kk), T.wf.fresh(T.get(t, kk)), M15.wt.ok(T.wf.key(kk, t),
          _u => T.wf.then(T.wf.go(a1,
        T.WfItems{}), _v => T.wf.go(t, T.WfRows{hp})), hw)) : {T.wf.text(kk) == True{} : Bool}}
      kp.one(kk, T.VArr{a1}, t, r0, he, hs, ab, cs, mm, tz, bk, qk, un, lf, rest, PP, eo, ec, hw1,
        Eq.and.left(D1.cv.short1(T.VArr{a1}), D4.short.rows(t), hl), hi.cn(T.wf.text(kk), T.wf.go(a1, T.WfItems{}),
          htx, hw1), hf,
        hn, ho, ih,
        +c2 => +m2 => +b2 => +q2 => +u2 => +l2 => f2 => n2 => o2 => i2 => kp(t, hp, r0, he, hs, ab, c2, m2, tz, b2, q2,
          u2,
          l2, rest, PP, eo, ec, hwt, Eq.and.right(D1.cv.short1(T.VArr{a1}), D4.short.rows(t), hl), f2, n2, o2, i2))
    case T.VPair{+kk, T.VInl{+a1}} <> +t:
      +hin = {M15.wt.more(T.wf.key(kk, t), _u => T.wf.then(T.wf.go(a1, T.WfInl{}), _v => T.wf.go(t, T.WfRows{hp})), hw)
        : {T.wf.then(T.wf.go(a1, T.WfInl{}), _v => T.wf.go(t, T.WfRows{hp})) == True{} : Bool}}
      +hwt = {M15.wt.more(T.wf.go(a1, T.WfInl{}), _v => T.wf.go(t, T.WfRows{hp}), hin) : {T.wf.go(t,
          T.WfRows{hp}) == True{}
        : Bool}}
      +hw1 = {M15.wt.ok(T.wf.go(a1, T.WfInl{}), _v => T.wf.go(t, T.WfRows{hp}), hin) : {T.wf.go(a1,
        T.WfInl{}) == True{} : Bool}}
      +htx = {Eq.and.left(T.wf.text(kk), T.wf.fresh(T.get(t, kk)), M15.wt.ok(T.wf.key(kk, t),
          _u => T.wf.then(T.wf.go(a1,
        T.WfInl{}), _v => T.wf.go(t, T.WfRows{hp})), hw)) : {T.wf.text(kk) == True{} : Bool}}
      kp.one(kk, T.VInl{a1}, t, r0, he, hs, ab, cs, mm, tz, bk, qk, un, lf, rest, PP, eo, ec, hw1,
        Eq.and.left(D1.cv.short1(T.VInl{a1}), D4.short.rows(t), hl), hi.cn(T.wf.text(kk), T.wf.go(a1, T.WfInl{}),
          htx, hw1), hf,
        hn, ho, ih,
        +c2 => +m2 => +b2 => +q2 => +u2 => +l2 => f2 => n2 => o2 => i2 => kp(t, hp, r0, he, hs, ab, c2, m2, tz, b2, q2,
          u2,
          l2, rest, PP, eo, ec, hwt, Eq.and.right(D1.cv.short1(T.VInl{a1}), D4.short.rows(t), hl), f2, n2, o2, i2))
    case T.VPair{+kk, T.VAot{+a1, +a2}} <> +t:
      Eq.bit.absurd(&1, PP(T.doc.read(String.append(T.render.pass(T.VPair{kk, T.VAot{a1, a2}} <> t, "\n", True{},
        False{}), rest), T.MScan{M5.dl(D1.tb.set(he, "",
          r0, cs), hs, he, bk, qk, un, lf, ab)})), hw)
    case T.VPair{+kk, T.VPair{+a1, +a2}} <> +t:
      Eq.bit.absurd(&1, PP(T.doc.read(String.append(T.render.pass(T.VPair{kk, T.VPair{a1, a2}} <> t, "\n", True{},
        False{}), rest), T.MScan{M5.dl(D1.tb.set(he, "",
          r0, cs), hs, he, bk, qk, un, lf, ab)})), hw)
    case T.VStr{+a1} <> +t:
      Eq.bit.absurd(&1, PP(T.doc.read(String.append(T.render.pass(T.VStr{a1} <> t, "\n", True{}, False{}), rest),
        T.MScan{M5.dl(D1.tb.set(he, "",
          r0, cs), hs, he, bk, qk, un, lf, ab)})), hw)
    case T.VSpan{+a1, +a2} <> +t:
      Eq.bit.absurd(&1, PP(T.doc.read(String.append(T.render.pass(T.VSpan{a1, a2} <> t, "\n", True{}, False{}), rest),
        T.MScan{M5.dl(D1.tb.set(he, "",
          r0, cs), hs, he, bk, qk, un, lf, ab)})), hw)
    case T.VInt{+a1, +a2} <> +t:
      Eq.bit.absurd(&1, PP(T.doc.read(String.append(T.render.pass(T.VInt{a1, a2} <> t, "\n", True{}, False{}), rest),
        T.MScan{M5.dl(D1.tb.set(he, "",
          r0, cs), hs, he, bk, qk, un, lf, ab)})), hw)
    case T.VFlo{+a1, +a2} <> +t:
      Eq.bit.absurd(&1, PP(T.doc.read(String.append(T.render.pass(T.VFlo{a1, a2} <> t, "\n", True{}, False{}), rest),
        T.MScan{M5.dl(D1.tb.set(he, "",
          r0, cs), hs, he, bk, qk, un, lf, ab)})), hw)
    case T.VBool{+a1} <> +t:
      Eq.bit.absurd(&1, PP(T.doc.read(String.append(T.render.pass(T.VBool{a1} <> t, "\n", True{}, False{}), rest),
        T.MScan{M5.dl(D1.tb.set(he, "",
          r0, cs), hs, he, bk, qk, un, lf, ab)})), hw)
    case T.VWhen{+a1} <> +t:
      Eq.bit.absurd(&1, PP(T.doc.read(String.append(T.render.pass(T.VWhen{a1} <> t, "\n", True{}, False{}), rest),
        T.MScan{M5.dl(D1.tb.set(he, "",
          r0, cs), hs, he, bk, qk, un, lf, ab)})), hw)
    case T.VArr{+a1} <> +t:
      Eq.bit.absurd(&1, PP(T.doc.read(String.append(T.render.pass(T.VArr{a1} <> t, "\n", True{}, False{}), rest),
        T.MScan{M5.dl(D1.tb.set(he, "",
          r0, cs), hs, he, bk, qk, un, lf, ab)})), hw)
    case T.VInl{+a1} <> +t:
      Eq.bit.absurd(&1, PP(T.doc.read(String.append(T.render.pass(T.VInl{a1} <> t, "\n", True{}, False{}), rest),
        T.MScan{M5.dl(D1.tb.set(he, "",
          r0, cs), hs, he, bk, qk, un, lf, ab)})), hw)
    case T.VHead{+a1, +a2} <> +t:
      Eq.bit.absurd(&1, PP(T.doc.read(String.append(T.render.pass(T.VHead{a1, a2} <> t, "\n", True{}, False{}), rest),
        T.MScan{M5.dl(D1.tb.set(he, "",
          r0, cs), hs, he, bk, qk, un, lf, ab)})), hw)
    case T.VAot{+a1, +a2} <> +t:
      Eq.bit.absurd(&1, PP(T.doc.read(String.append(T.render.pass(T.VAot{a1, a2} <> t, "\n", True{}, False{}), rest),
        T.MScan{M5.dl(D1.tb.set(he, "",
          r0, cs), hs, he, bk, qk, un, lf, ab)})), hw)
    case T.VAots{+a1, +a2} <> +t:
      Eq.bit.absurd(&1, PP(T.doc.read(String.append(T.render.pass(T.VAots{a1, a2} <> t, "\n", True{}, False{}), rest),
        T.MScan{M5.dl(D1.tb.set(he, "",
          r0, cs), hs, he, bk, qk, un, lf, ab)})), hw)

# a name missing from two lists together is missing from the first
def fr.l(
  aa: List<&2, T.Val>,
  +bb: List<&2, T.Val>,
  +kk: String,
  +ee: {T.wf.fresh(T.get(List.append(&2, T.Val, aa, bb), kk)) == True{} : Bool}
) -> {T.wf.fresh(T.get(aa, kk)) == True{} : Bool}:
  match aa:
    case []:
      {==}
    case T.VPair{+nn, +vv} <> +t:
      M8.fs.join(T.str.eq(nn, kk), vv, _u => T.rows.find(t, kk),
        M8.cv.fs.l(T.str.eq(nn, kk), vv, _u => T.rows.find(List.append(&2, T.Val, t, bb), kk), ee),
        fr.l(t, bb, kk, M8.cv.fs.r(T.str.eq(nn, kk), vv, _u => T.rows.find(List.append(&2, T.Val, t, bb), kk), ee)))

    case T.VStr{_a1} <> +t:
      fr.l(t, bb, kk, ee)
    case T.VSpan{_a1, _a2} <> +t:
      fr.l(t, bb, kk, ee)
    case T.VInt{_a1, _a2} <> +t:
      fr.l(t, bb, kk, ee)
    case T.VFlo{_a1, _a2} <> +t:
      fr.l(t, bb, kk, ee)
    case T.VBool{_a1} <> +t:
      fr.l(t, bb, kk, ee)
    case T.VWhen{_a1} <> +t:
      fr.l(t, bb, kk, ee)
    case T.VArr{_a1} <> +t:
      fr.l(t, bb, kk, ee)
    case T.VInl{_a1} <> +t:
      fr.l(t, bb, kk, ee)
    case T.VHead{_a1, _a2} <> +t:
      fr.l(t, bb, kk, ee)
    case T.VAot{_a1, _a2} <> +t:
      fr.l(t, bb, kk, ee)
    case T.VAots{_a1, _a2} <> +t:
      fr.l(t, bb, kk, ee)

# and from the second
def fr.r(
  aa: List<&2, T.Val>,
  +bb: List<&2, T.Val>,
  +kk: String,
  +ee: {T.wf.fresh(T.get(List.append(&2, T.Val, aa, bb), kk)) == True{} : Bool}
) -> {T.wf.fresh(T.get(bb, kk)) == True{} : Bool}:
  match aa:
    case []:
      ee
    case T.VPair{+nn, +vv} <> +t:
      fr.r(t, bb, kk, M8.cv.fs.r(T.str.eq(nn, kk), vv, _u => T.rows.find(List.append(&2, T.Val, t, bb), kk), ee))

    case T.VStr{_a1} <> +t:
      fr.r(t, bb, kk, ee)
    case T.VSpan{_a1, _a2} <> +t:
      fr.r(t, bb, kk, ee)
    case T.VInt{_a1, _a2} <> +t:
      fr.r(t, bb, kk, ee)
    case T.VFlo{_a1, _a2} <> +t:
      fr.r(t, bb, kk, ee)
    case T.VBool{_a1} <> +t:
      fr.r(t, bb, kk, ee)
    case T.VWhen{_a1} <> +t:
      fr.r(t, bb, kk, ee)
    case T.VArr{_a1} <> +t:
      fr.r(t, bb, kk, ee)
    case T.VInl{_a1} <> +t:
      fr.r(t, bb, kk, ee)
    case T.VHead{_a1, _a2} <> +t:
      fr.r(t, bb, kk, ee)
    case T.VAot{_a1, _a2} <> +t:
      fr.r(t, bb, kk, ee)
    case T.VAots{_a1, _a2} <> +t:
      fr.r(t, bb, kk, ee)

# and from its tables, reordered
def fr.tabs(
  xs: List<&2, T.Val>,
  +kk: String,
  +ee: {T.wf.fresh(T.get(xs, kk)) == True{} : Bool}
) -> {T.wf.fresh(T.get(D2.canon.tabs(xs), kk)) == True{} : Bool}:
  match xs:
    case []:
      {==}

    case T.VPair{+nn, T.VStr{+a1}} <> +t:
      fr.tabs(t, kk, M8.cv.fs.r(T.str.eq(nn, kk), T.VStr{a1}, _u => T.rows.find(t, kk), ee))
    case T.VPair{+nn, T.VSpan{+a1, +a2}} <> +t:
      fr.tabs(t, kk, M8.cv.fs.r(T.str.eq(nn, kk), T.VSpan{a1, a2}, _u => T.rows.find(t, kk), ee))
    case T.VPair{+nn, T.VInt{+a1, +a2}} <> +t:
      fr.tabs(t, kk, M8.cv.fs.r(T.str.eq(nn, kk), T.VInt{a1, a2}, _u => T.rows.find(t, kk), ee))
    case T.VPair{+nn, T.VFlo{+a1, +a2}} <> +t:
      fr.tabs(t, kk, M8.cv.fs.r(T.str.eq(nn, kk), T.VFlo{a1, a2}, _u => T.rows.find(t, kk), ee))
    case T.VPair{+nn, T.VBool{+a1}} <> +t:
      fr.tabs(t, kk, M8.cv.fs.r(T.str.eq(nn, kk), T.VBool{a1}, _u => T.rows.find(t, kk), ee))
    case T.VPair{+nn, T.VWhen{+a1}} <> +t:
      fr.tabs(t, kk, M8.cv.fs.r(T.str.eq(nn, kk), T.VWhen{a1}, _u => T.rows.find(t, kk), ee))
    case T.VPair{+nn, T.VArr{+a1}} <> +t:
      fr.tabs(t, kk, M8.cv.fs.r(T.str.eq(nn, kk), T.VArr{a1}, _u => T.rows.find(t, kk), ee))
    case T.VPair{+nn, T.VInl{+a1}} <> +t:
      fr.tabs(t, kk, M8.cv.fs.r(T.str.eq(nn, kk), T.VInl{a1}, _u => T.rows.find(t, kk), ee))
    case T.VPair{+nn, T.VHead{+a1, +a2}} <> +t:
      M8.fs.join(T.str.eq(nn, kk), T.VHead{a1, D2.canon.rows(a2)}, _u => T.rows.find(D2.canon.tabs(t), kk),
        M8.cv.fs.l(T.str.eq(nn, kk), T.VHead{a1, a2}, _u => T.rows.find(t, kk), ee),
        fr.tabs(t, kk, M8.cv.fs.r(T.str.eq(nn, kk), T.VHead{a1, a2}, _u => T.rows.find(t, kk), ee)))
    case T.VPair{+nn, T.VAot{+a1, +a2}} <> +t:
      fr.tabs(t, kk, M8.cv.fs.r(T.str.eq(nn, kk), T.VAot{a1, a2}, _u => T.rows.find(t, kk), ee))
    case T.VPair{+nn, T.VAots{+a1, +a2}} <> +t:
      M8.fs.join(T.str.eq(nn, kk), T.VAots{a1, D2.canon.go(a2, D2.CElems{a1})}, _u => T.rows.find(D2.canon.tabs(t),
        kk),
        M8.cv.fs.l(T.str.eq(nn, kk), T.VAots{a1, a2}, _u => T.rows.find(t, kk), ee),
        fr.tabs(t, kk, M8.cv.fs.r(T.str.eq(nn, kk), T.VAots{a1, a2}, _u => T.rows.find(t, kk), ee)))
    case T.VPair{+nn, T.VPair{+a1, +a2}} <> +t:
      fr.tabs(t, kk, M8.cv.fs.r(T.str.eq(nn, kk), T.VPair{a1, a2}, _u => T.rows.find(t, kk), ee))
    case T.VStr{_a1} <> +t:
      fr.tabs(t, kk, ee)
    case T.VSpan{_a1, _a2} <> +t:
      fr.tabs(t, kk, ee)
    case T.VInt{_a1, _a2} <> +t:
      fr.tabs(t, kk, ee)
    case T.VFlo{_a1, _a2} <> +t:
      fr.tabs(t, kk, ee)
    case T.VBool{_a1} <> +t:
      fr.tabs(t, kk, ee)
    case T.VWhen{_a1} <> +t:
      fr.tabs(t, kk, ee)
    case T.VArr{_a1} <> +t:
      fr.tabs(t, kk, ee)
    case T.VInl{_a1} <> +t:
      fr.tabs(t, kk, ee)
    case T.VHead{_a1, _a2} <> +t:
      fr.tabs(t, kk, ee)
    case T.VAot{_a1, _a2} <> +t:
      fr.tabs(t, kk, ee)
    case T.VAots{_a1, _a2} <> +t:
      fr.tabs(t, kk, ee)

# a pair put between two lists keeps nd, when its name is none of theirs
def nd.mid(
  aa: List<&2, T.Val>,
  +bb: List<&2, T.Val>,
  +nn: String,
  +vv: T.Val,
  +hh: {M8.nd(List.append(&2, T.Val, aa, bb)) == True{} : Bool},
  +ea: {T.wf.fresh(T.get(aa, nn)) == True{} : Bool},
  +eb: {T.wf.fresh(T.get(bb, nn)) == True{} : Bool}
) -> {M8.nd(List.append(&2, T.Val, aa, T.VPair{nn, vv} <> bb)) == True{} : Bool}:
  match aa:
    case []:
      M15.cv.and2(T.wf.fresh(T.get(bb, nn)), M8.nd(bb), eb, hh)
    case T.VPair{+mm, +ww} <> +t:
      +e1 = {M8.cv.fs.l(T.str.eq(mm, nn), ww, _u => T.rows.find(t, nn), ea) : {T.str.eq(mm, nn) == False{} : Bool}}
      +e2 = {Equal.trans(Bool, T.str.eq(nn, mm), T.str.eq(mm, nn), False{}, M8.cv.seqs(nn, mm, True{}), e1)
        : {T.str.eq(nn, mm) == False{} : Bool}}
      +hf = {Eq.and.left(T.wf.fresh(T.get(List.append(&2, T.Val, t, bb), mm)), M8.nd(List.append(&2, T.Val, t, bb)), hh)
        : {T.wf.fresh(T.get(List.append(&2, T.Val, t, bb), mm)) == True{} : Bool}}
      M15.cv.and2(T.wf.fresh(T.get(List.append(&2, T.Val, t, T.VPair{nn, vv} <> bb), mm)),
        M8.nd(List.append(&2, T.Val, t, T.VPair{nn, vv} <> bb)),
        M8.fr.app(t, T.VPair{nn, vv} <> bb, mm, fr.l(t, bb, mm, hf),
          M8.fs.join(T.str.eq(nn, mm), vv, _u => T.rows.find(bb, mm), e2, fr.r(t, bb, mm, hf))),
        nd.mid(t, bb, nn, vv, Eq.and.right(T.wf.fresh(T.get(List.append(&2, T.Val, t, bb), mm)),
          M8.nd(List.append(&2, T.Val, t, bb)), hh), M8.cv.fs.r(T.str.eq(mm, nn), ww, _u => T.rows.find(t, nn), ea),
              eb))

    case T.VStr{_a1} <> +t:
      nd.mid(t, bb, nn, vv, hh, ea, eb)
    case T.VSpan{_a1, _a2} <> +t:
      nd.mid(t, bb, nn, vv, hh, ea, eb)
    case T.VInt{_a1, _a2} <> +t:
      nd.mid(t, bb, nn, vv, hh, ea, eb)
    case T.VFlo{_a1, _a2} <> +t:
      nd.mid(t, bb, nn, vv, hh, ea, eb)
    case T.VBool{_a1} <> +t:
      nd.mid(t, bb, nn, vv, hh, ea, eb)
    case T.VWhen{_a1} <> +t:
      nd.mid(t, bb, nn, vv, hh, ea, eb)
    case T.VArr{_a1} <> +t:
      nd.mid(t, bb, nn, vv, hh, ea, eb)
    case T.VInl{_a1} <> +t:
      nd.mid(t, bb, nn, vv, hh, ea, eb)
    case T.VHead{_a1, _a2} <> +t:
      nd.mid(t, bb, nn, vv, hh, ea, eb)
    case T.VAot{_a1, _a2} <> +t:
      nd.mid(t, bb, nn, vv, hh, ea, eb)
    case T.VAots{_a1, _a2} <> +t:
      nd.mid(t, bb, nn, vv, hh, ea, eb)

# nd holds of the later part of a list it holds of
def nd.suf(
  aa: List<&2, T.Val>,
  +bb: List<&2, T.Val>,
  +hh: {M8.nd(List.append(&2, T.Val, aa, bb)) == True{} : Bool}
) -> {M8.nd(bb) == True{} : Bool}:
  match aa:
    case []:
      hh
    case T.VPair{+nn, _vv} <> +t:
      nd.suf(t, bb, Eq.and.right(T.wf.fresh(T.get(List.append(&2, T.Val, t, bb), nn)), M8.nd(List.append(&2, T.Val, t,
        bb)), hh))

    case T.VStr{_a1} <> +t:
      nd.suf(t, bb, hh)
    case T.VSpan{_a1, _a2} <> +t:
      nd.suf(t, bb, hh)
    case T.VInt{_a1, _a2} <> +t:
      nd.suf(t, bb, hh)
    case T.VFlo{_a1, _a2} <> +t:
      nd.suf(t, bb, hh)
    case T.VBool{_a1} <> +t:
      nd.suf(t, bb, hh)
    case T.VWhen{_a1} <> +t:
      nd.suf(t, bb, hh)
    case T.VArr{_a1} <> +t:
      nd.suf(t, bb, hh)
    case T.VInl{_a1} <> +t:
      nd.suf(t, bb, hh)
    case T.VHead{_a1, _a2} <> +t:
      nd.suf(t, bb, hh)
    case T.VAot{_a1, _a2} <> +t:
      nd.suf(t, bb, hh)
    case T.VAots{_a1, _a2} <> +t:
      nd.suf(t, bb, hh)

# a well-formed table's rows, read as render writes them, hold nd
def nd.wf(
  xs: List<&2, T.Val>,
  +hp: String,
  +hw: {T.wf.go(xs, T.WfRows{hp}) == True{} : Bool}
) -> {M8.nd(List.append(&2, T.Val, D2.canon.keys(xs), D2.canon.tabs(xs))) == True{} : Bool}:
  match xs:
    case []:
      {==}
    case T.VPair{+kk, T.VHead{+p, +r}} <> +t:
      +ha = {M15.wt.ok(Bool.and(T.wf.key(kk, t), T.str.eq(p, T.tree.pre(hp, kk))), _u => T.wf.then(T.wf.go(r,
          T.WfRows{p}),
        _v => T.wf.go(t, T.WfRows{hp})), hw) : {Bool.and(T.wf.key(kk, t), T.str.eq(p, T.tree.pre(hp, kk))) == True{}
        : Bool}}
      +fr = {Eq.and.right(T.wf.text(kk), T.wf.fresh(T.get(t, kk)), Eq.and.left(T.wf.key(kk, t), T.str.eq(p,
        T.tree.pre(hp, kk)),
        ha)) : {T.wf.fresh(T.get(t, kk)) == True{} : Bool}}
      +hwt = {M15.wt.more(T.wf.go(r, T.WfRows{p}), _v => T.wf.go(t, T.WfRows{hp}), M15.wt.more(Bool.and(T.wf.key(kk, t),
        T.str.eq(p, T.tree.pre(hp, kk))), _u => T.wf.then(T.wf.go(r, T.WfRows{p}), _v => T.wf.go(t, T.WfRows{hp})), hw))
        : {T.wf.go(t, T.WfRows{hp}) == True{} : Bool}}
      nd.mid(D2.canon.keys(t), D2.canon.tabs(t), kk, T.VHead{p, D2.canon.rows(r)}, nd.wf(t, hp, hwt),
        M8.fr.keys(t, kk, fr), fr.tabs(t, kk, fr))
    case T.VPair{+kk, T.VAots{+p, +es}} <> +t:
      +ha = {M15.wt.ok(Bool.and(Bool.not(List.is_empty(&2, T.Val, es)), Bool.and(T.wf.key(kk, t), T.str.eq(p,
          T.tree.pre(hp,
        kk)))), _u => T.wf.then(T.wf.go(es, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp})), hw)
        : {Bool.and(Bool.not(List.is_empty(&2, T.Val, es)), Bool.and(T.wf.key(kk, t), T.str.eq(p, T.tree.pre(hp, kk))))
        == True{} : Bool}}
      +fr = {Eq.and.right(T.wf.text(kk), T.wf.fresh(T.get(t, kk)), Eq.and.left(T.wf.key(kk, t), T.str.eq(p,
        T.tree.pre(hp, kk)),
        Eq.and.right(Bool.not(List.is_empty(&2, T.Val, es)), Bool.and(T.wf.key(kk, t), T.str.eq(p, T.tree.pre(hp, kk))),
        ha))) : {T.wf.fresh(T.get(t, kk)) == True{} : Bool}}
      +hwt = {M15.wt.more(T.wf.go(es, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}), M15.wt.more(Bool.and(Bool.not(
        List.is_empty(&2, T.Val, es)), Bool.and(T.wf.key(kk, t), T.str.eq(p, T.tree.pre(hp, kk)))),
        _u => T.wf.then(T.wf.go(es, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp})), hw))
        : {T.wf.go(t, T.WfRows{hp}) == True{} : Bool}}
      nd.mid(D2.canon.keys(t), D2.canon.tabs(t), kk, T.VAots{p, D2.canon.go(es, D2.CElems{p})}, nd.wf(t, hp,
        hwt), M8.fr.keys(t, kk, fr), fr.tabs(t, kk, fr))

    case T.VPair{+kk, T.VStr{+a1}} <> +t:
      +ha = {M15.wt.ok(Bool.and(T.wf.atom(T.VStr{a1}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}), hw)
        : {Bool.and(T.wf.atom(T.VStr{a1}), T.wf.key(kk, t)) == True{} : Bool}}
      +fr = {Eq.and.right(T.wf.text(kk), T.wf.fresh(T.get(t, kk)), Eq.and.right(T.wf.atom(T.VStr{a1}), T.wf.key(kk, t),
        ha))
        : {T.wf.fresh(T.get(t, kk)) == True{} : Bool}}
      M15.cv.and2(T.wf.fresh(T.get(List.append(&2, T.Val, D2.canon.keys(t), D2.canon.tabs(t)), kk)),
          M8.nd(List.append(&2,
        T.Val, D2.canon.keys(t), D2.canon.tabs(t))),
        M8.fr.app(D2.canon.keys(t), D2.canon.tabs(t), kk, M8.fr.keys(t, kk, fr), fr.tabs(t, kk, fr)),
        nd.wf(t, hp, M15.wt.more(Bool.and(T.wf.atom(T.VStr{a1}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}), hw)))
    case T.VPair{+kk, T.VSpan{+a1, +a2}} <> +t:
      +ha = {M15.wt.ok(Bool.and(T.wf.atom(T.VSpan{a1, a2}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}), hw)
        : {Bool.and(T.wf.atom(T.VSpan{a1, a2}), T.wf.key(kk, t)) == True{} : Bool}}
      +fr = {Eq.and.right(T.wf.text(kk), T.wf.fresh(T.get(t, kk)), Eq.and.right(T.wf.atom(T.VSpan{a1, a2}), T.wf.key(kk,
        t), ha))
        : {T.wf.fresh(T.get(t, kk)) == True{} : Bool}}
      M15.cv.and2(T.wf.fresh(T.get(List.append(&2, T.Val, D2.canon.keys(t), D2.canon.tabs(t)), kk)),
          M8.nd(List.append(&2,
        T.Val, D2.canon.keys(t), D2.canon.tabs(t))),
        M8.fr.app(D2.canon.keys(t), D2.canon.tabs(t), kk, M8.fr.keys(t, kk, fr), fr.tabs(t, kk, fr)),
        nd.wf(t, hp, M15.wt.more(Bool.and(T.wf.atom(T.VSpan{a1, a2}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}),
          hw)))
    case T.VPair{+kk, T.VInt{+a1, +a2}} <> +t:
      +ha = {M15.wt.ok(Bool.and(T.wf.atom(T.VInt{a1, a2}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}), hw)
        : {Bool.and(T.wf.atom(T.VInt{a1, a2}), T.wf.key(kk, t)) == True{} : Bool}}
      +fr = {Eq.and.right(T.wf.text(kk), T.wf.fresh(T.get(t, kk)), Eq.and.right(T.wf.atom(T.VInt{a1, a2}), T.wf.key(kk,
        t), ha))
        : {T.wf.fresh(T.get(t, kk)) == True{} : Bool}}
      M15.cv.and2(T.wf.fresh(T.get(List.append(&2, T.Val, D2.canon.keys(t), D2.canon.tabs(t)), kk)),
          M8.nd(List.append(&2,
        T.Val, D2.canon.keys(t), D2.canon.tabs(t))),
        M8.fr.app(D2.canon.keys(t), D2.canon.tabs(t), kk, M8.fr.keys(t, kk, fr), fr.tabs(t, kk, fr)),
        nd.wf(t, hp, M15.wt.more(Bool.and(T.wf.atom(T.VInt{a1, a2}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}),
            hw)))
    case T.VPair{+kk, T.VFlo{+a1, +a2}} <> +t:
      +ha = {M15.wt.ok(Bool.and(T.wf.atom(T.VFlo{a1, a2}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}), hw)
        : {Bool.and(T.wf.atom(T.VFlo{a1, a2}), T.wf.key(kk, t)) == True{} : Bool}}
      +fr = {Eq.and.right(T.wf.text(kk), T.wf.fresh(T.get(t, kk)), Eq.and.right(T.wf.atom(T.VFlo{a1, a2}), T.wf.key(kk,
        t), ha))
        : {T.wf.fresh(T.get(t, kk)) == True{} : Bool}}
      M15.cv.and2(T.wf.fresh(T.get(List.append(&2, T.Val, D2.canon.keys(t), D2.canon.tabs(t)), kk)),
          M8.nd(List.append(&2,
        T.Val, D2.canon.keys(t), D2.canon.tabs(t))),
        M8.fr.app(D2.canon.keys(t), D2.canon.tabs(t), kk, M8.fr.keys(t, kk, fr), fr.tabs(t, kk, fr)),
        nd.wf(t, hp, M15.wt.more(Bool.and(T.wf.atom(T.VFlo{a1, a2}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}),
            hw)))
    case T.VPair{+kk, T.VBool{+a1}} <> +t:
      +ha = {M15.wt.ok(Bool.and(T.wf.atom(T.VBool{a1}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}), hw)
        : {Bool.and(T.wf.atom(T.VBool{a1}), T.wf.key(kk, t)) == True{} : Bool}}
      +fr = {Eq.and.right(T.wf.text(kk), T.wf.fresh(T.get(t, kk)), Eq.and.right(T.wf.atom(T.VBool{a1}), T.wf.key(kk, t),
        ha))
        : {T.wf.fresh(T.get(t, kk)) == True{} : Bool}}
      M15.cv.and2(T.wf.fresh(T.get(List.append(&2, T.Val, D2.canon.keys(t), D2.canon.tabs(t)), kk)),
          M8.nd(List.append(&2,
        T.Val, D2.canon.keys(t), D2.canon.tabs(t))),
        M8.fr.app(D2.canon.keys(t), D2.canon.tabs(t), kk, M8.fr.keys(t, kk, fr), fr.tabs(t, kk, fr)),
        nd.wf(t, hp, M15.wt.more(Bool.and(T.wf.atom(T.VBool{a1}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}),
            hw)))
    case T.VPair{+kk, T.VWhen{+a1}} <> +t:
      +ha = {M15.wt.ok(Bool.and(T.wf.atom(T.VWhen{a1}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}), hw)
        : {Bool.and(T.wf.atom(T.VWhen{a1}), T.wf.key(kk, t)) == True{} : Bool}}
      +fr = {Eq.and.right(T.wf.text(kk), T.wf.fresh(T.get(t, kk)), Eq.and.right(T.wf.atom(T.VWhen{a1}), T.wf.key(kk, t),
        ha))
        : {T.wf.fresh(T.get(t, kk)) == True{} : Bool}}
      M15.cv.and2(T.wf.fresh(T.get(List.append(&2, T.Val, D2.canon.keys(t), D2.canon.tabs(t)), kk)),
          M8.nd(List.append(&2,
        T.Val, D2.canon.keys(t), D2.canon.tabs(t))),
        M8.fr.app(D2.canon.keys(t), D2.canon.tabs(t), kk, M8.fr.keys(t, kk, fr), fr.tabs(t, kk, fr)),
        nd.wf(t, hp, M15.wt.more(Bool.and(T.wf.atom(T.VWhen{a1}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}),
            hw)))
    case T.VPair{+kk, T.VArr{+a1}} <> +t:
      +hin = {M15.wt.more(T.wf.key(kk, t), _u => T.wf.then(T.wf.go(a1, T.WfItems{}), _v => T.wf.go(t, T.WfRows{hp})),
          hw)
        : {T.wf.then(T.wf.go(a1, T.WfItems{}), _v => T.wf.go(t, T.WfRows{hp})) == True{} : Bool}}
      +fr = {Eq.and.right(T.wf.text(kk), T.wf.fresh(T.get(t, kk)), M15.wt.ok(T.wf.key(kk, t),
          _u => T.wf.then(T.wf.go(a1,
        T.WfItems{}),
        _v => T.wf.go(t, T.WfRows{hp})), hw)) : {T.wf.fresh(T.get(t, kk)) == True{} : Bool}}
      M15.cv.and2(T.wf.fresh(T.get(List.append(&2, T.Val, D2.canon.keys(t), D2.canon.tabs(t)), kk)),
          M8.nd(List.append(&2,
        T.Val, D2.canon.keys(t), D2.canon.tabs(t))),
        M8.fr.app(D2.canon.keys(t), D2.canon.tabs(t), kk, M8.fr.keys(t, kk, fr), fr.tabs(t, kk, fr)),
        nd.wf(t, hp, M15.wt.more(T.wf.go(a1, T.WfItems{}), _v => T.wf.go(t, T.WfRows{hp}), hin)))
    case T.VPair{+kk, T.VInl{+a1}} <> +t:
      +hin = {M15.wt.more(T.wf.key(kk, t), _u => T.wf.then(T.wf.go(a1, T.WfInl{}), _v => T.wf.go(t, T.WfRows{hp})), hw)
        : {T.wf.then(T.wf.go(a1, T.WfInl{}), _v => T.wf.go(t, T.WfRows{hp})) == True{} : Bool}}
      +fr = {Eq.and.right(T.wf.text(kk), T.wf.fresh(T.get(t, kk)), M15.wt.ok(T.wf.key(kk, t),
          _u => T.wf.then(T.wf.go(a1,
        T.WfInl{}),
        _v => T.wf.go(t, T.WfRows{hp})), hw)) : {T.wf.fresh(T.get(t, kk)) == True{} : Bool}}
      M15.cv.and2(T.wf.fresh(T.get(List.append(&2, T.Val, D2.canon.keys(t), D2.canon.tabs(t)), kk)),
          M8.nd(List.append(&2,
        T.Val, D2.canon.keys(t), D2.canon.tabs(t))),
        M8.fr.app(D2.canon.keys(t), D2.canon.tabs(t), kk, M8.fr.keys(t, kk, fr), fr.tabs(t, kk, fr)),
        nd.wf(t, hp, M15.wt.more(T.wf.go(a1, T.WfInl{}), _v => T.wf.go(t, T.WfRows{hp}), hin)))
    case T.VPair{+kk, T.VAot{+a1, +a2}} <> +t:
      Eq.bit.absurd(&2, {M8.nd(List.append(&2, T.Val, D2.canon.keys(T.VPair{kk, T.VAot{a1, a2}} <> t),
        D2.canon.tabs(T.VPair{kk, T.VAot{a1, a2}} <> t))) == True{} : Bool}, hw)
    case T.VPair{+kk, T.VPair{+a1, +a2}} <> +t:
      Eq.bit.absurd(&2, {M8.nd(List.append(&2, T.Val, D2.canon.keys(T.VPair{kk, T.VPair{a1, a2}} <> t),
        D2.canon.tabs(T.VPair{kk, T.VPair{a1, a2}} <> t))) == True{} : Bool}, hw)
    case T.VStr{+a1} <> +t:
      Eq.bit.absurd(&2, {M8.nd(List.append(&2, T.Val, D2.canon.keys(T.VStr{a1} <> t),
        D2.canon.tabs(T.VStr{a1} <> t))) == True{} : Bool}, hw)
    case T.VSpan{+a1, +a2} <> +t:
      Eq.bit.absurd(&2, {M8.nd(List.append(&2, T.Val, D2.canon.keys(T.VSpan{a1, a2} <> t), D2.canon.tabs(T.VSpan{a1,
        a2} <> t))) == True{} : Bool}, hw)
    case T.VInt{+a1, +a2} <> +t:
      Eq.bit.absurd(&2, {M8.nd(List.append(&2, T.Val, D2.canon.keys(T.VInt{a1, a2} <> t), D2.canon.tabs(T.VInt{a1,
        a2} <> t))) == True{} : Bool}, hw)
    case T.VFlo{+a1, +a2} <> +t:
      Eq.bit.absurd(&2, {M8.nd(List.append(&2, T.Val, D2.canon.keys(T.VFlo{a1, a2} <> t), D2.canon.tabs(T.VFlo{a1,
        a2} <> t))) == True{} : Bool}, hw)
    case T.VBool{+a1} <> +t:
      Eq.bit.absurd(&2, {M8.nd(List.append(&2, T.Val, D2.canon.keys(T.VBool{a1} <> t),
        D2.canon.tabs(T.VBool{a1} <> t))) == True{} : Bool}, hw)
    case T.VWhen{+a1} <> +t:
      Eq.bit.absurd(&2, {M8.nd(List.append(&2, T.Val, D2.canon.keys(T.VWhen{a1} <> t),
        D2.canon.tabs(T.VWhen{a1} <> t))) == True{} : Bool}, hw)
    case T.VArr{+a1} <> +t:
      Eq.bit.absurd(&2, {M8.nd(List.append(&2, T.Val, D2.canon.keys(T.VArr{a1} <> t),
        D2.canon.tabs(T.VArr{a1} <> t))) == True{} : Bool}, hw)
    case T.VInl{+a1} <> +t:
      Eq.bit.absurd(&2, {M8.nd(List.append(&2, T.Val, D2.canon.keys(T.VInl{a1} <> t),
        D2.canon.tabs(T.VInl{a1} <> t))) == True{} : Bool}, hw)
    case T.VHead{+a1, +a2} <> +t:
      Eq.bit.absurd(&2, {M8.nd(List.append(&2, T.Val, D2.canon.keys(T.VHead{a1, a2} <> t), D2.canon.tabs(T.VHead{a1,
        a2} <> t))) == True{} : Bool}, hw)
    case T.VAot{+a1, +a2} <> +t:
      Eq.bit.absurd(&2, {M8.nd(List.append(&2, T.Val, D2.canon.keys(T.VAot{a1, a2} <> t), D2.canon.tabs(T.VAot{a1,
        a2} <> t))) == True{} : Bool}, hw)
    case T.VAots{+a1, +a2} <> +t:
      Eq.bit.absurd(&2, {M8.nd(List.append(&2, T.Val, D2.canon.keys(T.VAots{a1, a2} <> t), D2.canon.tabs(T.VAots{a1,
        a2} <> t))) == True{} : Bool}, hw)

# The table pass. render writes each table as its header then its rows the
# same way, and each array of tables as one such header per element. A
# header makes the table, or the element, and makes it the current table;
# the rows after it are read as a table's are, and what they leave in it is
# the pair's table once the next header leaves it.

# replacing a pair's table twice is replacing it once
def slot.ss(xx: T.Val, +aa: List<&2, T.Val>, +bb: List<&2, T.Val>) -> {slot(slot(xx, aa), bb) == slot(xx, bb) : T.Val}:
  match xx:
    case T.VAots{_p, es}:
      match es:
        case []:
          {==}

        case T.VStr{_a1} <> _older:
          {==}
        case T.VSpan{_a1, _a2} <> _older:
          {==}
        case T.VInt{_a1, _a2} <> _older:
          {==}
        case T.VFlo{_a1, _a2} <> _older:
          {==}
        case T.VBool{_a1} <> _older:
          {==}
        case T.VWhen{_a1} <> _older:
          {==}
        case T.VArr{_a1} <> _older:
          {==}
        case T.VInl{_a1} <> _older:
          {==}
        case T.VHead{_a1, _a2} <> _older:
          {==}
        case T.VAot{_a1, _a2} <> _older:
          {==}
        case T.VAots{_a1, _a2} <> _older:
          {==}
        case T.VPair{_a1, _a2} <> _older:
          {==}
    case T.VStr{_a1}:
      {==}
    case T.VSpan{_a1, _a2}:
      {==}
    case T.VInt{_a1, _a2}:
      {==}
    case T.VFlo{_a1, _a2}:
      {==}
    case T.VBool{_a1}:
      {==}
    case T.VWhen{_a1}:
      {==}
    case T.VArr{_a1}:
      {==}
    case T.VInl{_a1}:
      {==}
    case T.VHead{_a1, _a2}:
      {==}
    case T.VAot{_a1, _a2}:
      {==}
    case T.VPair{_a1, _a2}:
      {==}

# a pair holds a table after its table is replaced, as before
def slot.okk(xx: T.Val, +aa: List<&2, T.Val>) -> {slot.ok(slot(xx, aa)) == slot.ok(xx) : Bool}:
  match xx:
    case T.VAots{_p, es}:
      match es:
        case []:
          {==}

        case T.VStr{_a1} <> _older:
          {==}
        case T.VSpan{_a1, _a2} <> _older:
          {==}
        case T.VInt{_a1, _a2} <> _older:
          {==}
        case T.VFlo{_a1, _a2} <> _older:
          {==}
        case T.VBool{_a1} <> _older:
          {==}
        case T.VWhen{_a1} <> _older:
          {==}
        case T.VArr{_a1} <> _older:
          {==}
        case T.VInl{_a1} <> _older:
          {==}
        case T.VHead{_a1, _a2} <> _older:
          {==}
        case T.VAot{_a1, _a2} <> _older:
          {==}
        case T.VAots{_a1, _a2} <> _older:
          {==}
        case T.VPair{_a1, _a2} <> _older:
          {==}
    case T.VStr{_a1}:
      {==}
    case T.VSpan{_a1, _a2}:
      {==}
    case T.VInt{_a1, _a2}:
      {==}
    case T.VFlo{_a1, _a2}:
      {==}
    case T.VBool{_a1}:
      {==}
    case T.VWhen{_a1}:
      {==}
    case T.VArr{_a1}:
      {==}
    case T.VInl{_a1}:
      {==}
    case T.VHead{_a1, _a2}:
      {==}
    case T.VAot{_a1, _a2}:
      {==}
    case T.VPair{_a1, _a2}:
      {==}

# the rest of the text once the table pass has read a table's tables: from
# the start of a line, in any table, with the current table's rows (at he)
# holding what own reads, sealed, as mm
def tp.Then(
  +r0: List<&2, T.Val>,
  +he: List<&2, String>,
  +mm: List<&2, T.Val>,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  @c2: List<&2, T.Val> -> @hs2: List<&2, String> -> @he2: List<&2, String> -> @b2: T.Lex -> @q2: T.QKind -> @u2: U32 ->
    @l2: U32 -> @a2: Bool ->
    {D1.own.rows(T.rows.seal(c2)) == D1.own.rows(mm) : List<&2, T.Val>} ->
    PP(T.doc.read(rest, T.MScan{M5.dl(D1.tb.set(he, "", r0, c2), hs2, he2, b2, q2, u2, l2, a2)}))

# the counts down from a path's length
def cdn(+path: List<&2, String>) -> Bool:
  D1.counts.down(path, T.path.len(path, 0))

# what the table pass the caller gives does: from rows c2 fresh for the
# tables of r, it reads the tables of r and then the rest
def body.Rec(
  +kk: String,
  +xx: T.Val,
  +r: List<&2, T.Val>,
  +he: List<&2, String>,
  +r0: List<&2, T.Val>,
  +cs: List<&2, T.Val>,
  +hs: List<&2, String>,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  @c2: List<&2, T.Val> -> @b2: T.Lex -> @q2: T.QKind -> @u2: U32 -> @l2: U32 ->
    {M8.cv.fr(c2, D2.canon.tabs(r)) == True{} : Bool} -> {M8.nd(D2.canon.tabs(r)) == True{} : Bool} ->
    {D1.own.rows(T.rows.seal(c2)) == D1.own.rows(D2.canon.keys(r)) : List<&2, T.Val>} ->
    tp.Then(D1.tb.set(he, "", r0, T.VPair{kk, slot(xx, [])} <> cs), List.append(&2, String, he, [kk]), List.append(&2,
      T.Val, D2.canon.keys(r), D2.canon.tabs(r)), rest, PP) ->
    PP(T.doc.read(String.append(T.render.pass(r, "\n", True{}, True{}), rest), T.MScan{M5.dl(D1.tb.set(List.append(&2,
      String, he, [kk]), "", D1.tb.set(he, "", r0, T.VPair{kk, slot(xx, [])} <> cs), c2), hs, List.append(&2, String,
      he, [kk]), b2, q2, u2, l2, ab)}))

# the rest after the rows of the table the pair holds: from any line state,
# its rows c3 sealed owning the rows of r reordered
def body.Then(
  +kk: String,
  +xx: T.Val,
  +r: List<&2, T.Val>,
  +he: List<&2, String>,
  +r0: List<&2, T.Val>,
  +cs: List<&2, T.Val>,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  @c3: List<&2, T.Val> -> @hs3: List<&2, String> -> @he3: List<&2, String> -> @b3: T.Lex -> @q3: T.QKind -> @u3: U32 ->
    @l3: U32 -> @a3: Bool ->
    {D1.own.rows(T.rows.seal(c3)) == D1.own.rows(D2.canon.rows(r)) : List<&2, T.Val>} ->
    PP(T.doc.read(rest, T.MScan{M5.dl(D1.tb.set(he, "", r0, T.VPair{kk, slot(xx, c3)} <> cs), hs3, he3, b3, q3, u3, l3,
      a3)}))

# the rows of the table a pair holds, read after its header: the key pass,
# then the table pass the caller gives (rec), leave in it what own reads,
# sealed, as the rows reordered
def body(
  +kk: String,
  +xx: T.Val,
  +r: List<&2, T.Val>,
  +pq: String,
  +he: List<&2, String>,
  +r0: List<&2, T.Val>,
  +cs: List<&2, T.Val>,
  +hs: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  +eo: {D1.tb.open(he, r0) == True{} : Bool},
  +em: {L4.is_miss(T.get(cs, kk)) == True{} : Bool},
  +ok: {slot.ok(xx) == True{} : Bool},
  +ec: {cdn(List.append(&2, String, he, [kk])) == True{} : Bool},
  +hw: {T.wf.go(r, T.WfRows{pq}) == True{} : Bool},
  +hl: {D4.short.rows(r) == True{} : Bool},
  rec: body.Rec(kk, xx, r, he, r0, cs, hs, ab, rest, PP),
  ih: body.Then(kk, xx, r, he, r0, cs, rest, PP)
) -> PP(T.doc.read(String.append(T.render.pass(r, "\n", True{}, False{}), String.append(T.render.pass(r, "\n", True{},
  True{}), rest)), T.MScan{M5.dl(D1.tb.set(he, "", r0, T.VPair{kk, slot(xx, [])} <> cs), hs, List.append(&2, String, he,
  [kk]), bk, qk, un, lf, ab)})):
  +r1 = {D1.tb.set(he, "", r0, T.VPair{kk, slot(xx, [])} <> cs) : List<&2, T.Val>}
  +ok1 = {Equal.trans(Bool, slot.ok(slot(xx, [])), slot.ok(xx), True{}, slot.okk(xx, []), ok)
    : {slot.ok(slot(xx, [])) == True{} : Bool}}
  +tx = {String.append(T.render.pass(r, "\n", True{}, False{}), String.append(T.render.pass(r, "\n", True{}, True{}),
    rest)) : String}
  +nw = {nd.wf(r, pq, hw) : {M8.nd(List.append(&2, T.Val, D2.canon.keys(r), D2.canon.tabs(r))) == True{} : Bool}}
  pp.step(PP, T.doc.read(tx, T.MScan{M5.dl(r1, hs, List.append(&2, String, he, [kk]), bk, qk, un, lf, ab)}),
    T.doc.read(tx, T.MScan{M5.dl(D1.tb.set(List.append(&2, String, he, [kk]), "", r1, []), hs, List.append(&2, String,
      he, [kk]), bk, qk, un, lf, ab)}),
    Equal.cong(List<&2, T.Val>, T.Doc, zs => T.doc.read(tx, T.MScan{M5.dl(zs, hs, List.append(&2, String, he, [kk]), bk,
      qk, un, lf, ab)}), r1,
      D1.tb.set(List.append(&2, String, he, [kk]), "", r1, []),
      Equal.sym(List<&2, T.Val>, D1.tb.set(List.append(&2, String, he, [kk]), "", r1, []), r1,
        Equal.trans(List<&2, T.Val>, D1.tb.set(List.append(&2, String, he, [kk]), "", r1, []),
          D1.tb.set(he, "", r0, T.VPair{kk, slot(slot(xx, []), [])} <> cs), r1,
          wa.enter(he, r0, kk, slot(xx, []), cs, [], eo, em, ok1),
          Equal.cong(T.Val, List<&2, T.Val>, zz => D1.tb.set(he, "", r0, T.VPair{kk, zz} <> cs), slot(slot(xx, []),
            []),
            slot(xx, []), slot.ss(xx, [], []))))),
    kp(r, pq, r1, List.append(&2, String, he, [kk]), hs, ab, [], [], D2.canon.tabs(r), bk, qk, un, lf,
      String.append(T.render.pass(r, "\n", True{}, True{}), rest), PP,
      wa.eopen(he, r0, kk, slot(xx, []), cs, eo, ok1), ec, hw, hl,
      M13.cv.fr.nil(List.append(&2, T.Val, D2.canon.keys(r), D2.canon.tabs(r))), nw, {==},
      +c2 => +b2 => +q2 => +u2 => +l2 => f2 => o2 => rec(c2, b2, q2, u2, l2, f2,
        nd.suf(D2.canon.keys(r), D2.canon.tabs(r), nw), o2,
        +c3 => +hs3 => +he3 => +b3 => +q3 => +u3 => +l3 => +a3 => o3 => pp.step(PP,
          T.doc.read(rest, T.MScan{M5.dl(D1.tb.set(List.append(&2, String, he, [kk]), "", r1, c3), hs3, he3, b3, q3, u3,
            l3, a3)}),
          T.doc.read(rest, T.MScan{M5.dl(D1.tb.set(he, "", r0, T.VPair{kk, slot(xx, c3)} <> cs), hs3, he3, b3, q3, u3,
            l3, a3)}),
          Equal.cong(List<&2, T.Val>, T.Doc, zs => T.doc.read(rest, T.MScan{M5.dl(zs, hs3, he3, b3, q3, u3, l3, a3)}),
            D1.tb.set(List.append(&2, String, he, [kk]), "", r1, c3), D1.tb.set(he, "", r0, T.VPair{kk, slot(xx,
              c3)} <> cs),
            Equal.trans(List<&2, T.Val>, D1.tb.set(List.append(&2, String, he, [kk]), "", r1, c3),
              D1.tb.set(he, "", r0, T.VPair{kk, slot(slot(xx, []), c3)} <> cs),
              D1.tb.set(he, "", r0, T.VPair{kk, slot(xx, c3)} <> cs),
              wa.enter(he, r0, kk, slot(xx, []), cs, c3, eo, em, ok1),
              Equal.cong(T.Val, List<&2, T.Val>, zz => D1.tb.set(he, "", r0, T.VPair{kk, zz} <> cs), slot(slot(xx,
                []), c3),
                slot(xx, c3), slot.ss(xx, [], c3)))),
          ih(c3, hs3, he3, b3, q3, u3, l3, a3, o3)))))

# a hexadecimal digit's character is one dig.val reads as the digit's value
def k3.hx.dv(hx: D3.KHex) -> {D3.k3.hex.val(hx) == T.dig.val(D3.k3.hex.char(hx)) : U32}:
  match hx:
    case D3.Kx0{}:
      {==}
    case D3.Kx1{}:
      {==}
    case D3.Kx2{}:
      {==}
    case D3.Kx3{}:
      {==}
    case D3.Kx4{}:
      {==}
    case D3.Kx5{}:
      {==}
    case D3.Kx6{}:
      {==}
    case D3.Kx7{}:
      {==}
    case D3.Kx8{}:
      {==}
    case D3.Kx9{}:
      {==}
    case D3.KxA{True{}}:
      {==}
    case D3.KxA{False{}}:
      {==}
    case D3.KxB{True{}}:
      {==}
    case D3.KxB{False{}}:
      {==}
    case D3.KxC{True{}}:
      {==}
    case D3.KxC{False{}}:
      {==}
    case D3.KxD{True{}}:
      {==}
    case D3.KxD{False{}}:
      {==}
    case D3.KxE{True{}}:
      {==}
    case D3.KxE{False{}}:
      {==}
    case D3.KxF{True{}}:
      {==}
    case D3.KxF{False{}}:
      {==}

# and one dig.ok takes for a digit of base 16
def k3.hx.ok(hx: D3.KHex) -> {True{} == T.dig.ok(T.dig.val(D3.k3.hex.char(hx)), 16) : Bool}:
  match hx:
    case D3.Kx0{}:
      {==}
    case D3.Kx1{}:
      {==}
    case D3.Kx2{}:
      {==}
    case D3.Kx3{}:
      {==}
    case D3.Kx4{}:
      {==}
    case D3.Kx5{}:
      {==}
    case D3.Kx6{}:
      {==}
    case D3.Kx7{}:
      {==}
    case D3.Kx8{}:
      {==}
    case D3.Kx9{}:
      {==}
    case D3.KxA{True{}}:
      {==}
    case D3.KxA{False{}}:
      {==}
    case D3.KxB{True{}}:
      {==}
    case D3.KxB{False{}}:
      {==}
    case D3.KxC{True{}}:
      {==}
    case D3.KxC{False{}}:
      {==}
    case D3.KxD{True{}}:
      {==}
    case D3.KxD{False{}}:
      {==}
    case D3.KxE{True{}}:
      {==}
    case D3.KxE{False{}}:
      {==}
    case D3.KxF{True{}}:
      {==}
    case D3.KxF{False{}}:
      {==}

# the scan mode sends a hexadecimal digit to the fast step
def k3.hx.scan(
  hx: D3.KHex,
  st: T.St
) -> {T.MScan{T.read.fast(st, D3.k3.hex.char(hx))} == T.doc.scan(st, D3.k3.hex.char(hx)) : T.Mode}:
  match hx:
    case D3.Kx0{}:
      {==}
    case D3.Kx1{}:
      {==}
    case D3.Kx2{}:
      {==}
    case D3.Kx3{}:
      {==}
    case D3.Kx4{}:
      {==}
    case D3.Kx5{}:
      {==}
    case D3.Kx6{}:
      {==}
    case D3.Kx7{}:
      {==}
    case D3.Kx8{}:
      {==}
    case D3.Kx9{}:
      {==}
    case D3.KxA{True{}}:
      {==}
    case D3.KxA{False{}}:
      {==}
    case D3.KxB{True{}}:
      {==}
    case D3.KxB{False{}}:
      {==}
    case D3.KxC{True{}}:
      {==}
    case D3.KxC{False{}}:
      {==}
    case D3.KxD{True{}}:
      {==}
    case D3.KxD{False{}}:
      {==}
    case D3.KxE{True{}}:
      {==}
    case D3.KxE{False{}}:
      {==}
    case D3.KxF{True{}}:
      {==}
    case D3.KxF{False{}}:
      {==}

# the digits an escape reads: eight when lg, four otherwise
def k3.hx.n(lg: Bool) -> U32:
  match lg:
    case True{}:
      8
    case False{}:
      4

# the letter after its backslash
def k3.hx.u(lg: Bool) -> Char:
  match lg:
    case True{}:
      'U'
    case False{}:
      'u'

# a name's characters pushed onto an empty buffer read back as the name
def k3.nm(+ss: String) -> {ss == T.buf.str.go(M8.rev.onto(ss, []), "") : String}:
  Equal.sym(String, T.buf.str.go(M8.rev.onto(ss, []), ""), ss, Equal.trans(String, T.buf.str.go(M8.rev.onto(ss, []),
      ""),
    String.append(ss, ""), ss, ml.rev(ss, [], ""), Eq.append_nil(ss)))

# Newlines, whitespace after a line-ending backslash, and the closing
# delimiter.

# the code point is k
def s1.isk(+uu: U32, +kk: U32, ee: {U32.is_eq(uu, kk) == True{} : Bool}) -> {uu == kk : U32}:
  Equal.cong(Char, U32, cc => Char.to_u32(cc), Chr{uu}, Chr{kk}, Eq.u32_eq(uu, kk, ee))
