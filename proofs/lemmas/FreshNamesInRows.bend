# names missing from rows, lookups, picks and datetime tokens
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/DefinesEachTableOnce.bend as L1
import ../../laws/defs/DocumentSameness.bend as D1
import ./PickAndDigitSteps.bend as M1
import ./ShortTextBounds.bend as M2

# the characters of a text pushed one by one onto a buffer
def rev.onto(xs: String, acc: List<&2, Char>) -> List<&2, Char>:
  match xs:
    case SNil{}:
      acc
    case SCon{hh, tt}:
      rev.onto(tt, hh <> acc)

# WP-N: a scalar reads back as itself. A bare value is read from the value
# state one character at a time on the fast path, ended by a newline, and
# classified by word.val; the classification is proved kind by kind.

# The ten digits. A digit is a code point from 48 to 57, so its bits above
# the sixth are zero and its six low bits are one of ten patterns; a claim
# made of each of the ten digit characters is made of every digit.

# a code point's comparisons with 48 and 57, bit by bit, the bits above the
# sixth comparing as cc with zero
def dg.cp(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +cc: Cmp) -> Bool:
  Bool.and(Cmp.is_ge(Word.cmp.fin(b0, False{}, Word.cmp.fin(b1, False{}, Word.cmp.fin(b2, False{},
    Word.cmp.fin(b3, False{}, Word.cmp.fin(b4, True{}, Word.cmp.fin(b5, True{}, cc))))))),
    Cmp.is_le(Word.cmp.fin(b0, True{}, Word.cmp.fin(b1, False{}, Word.cmp.fin(b2, False{},
    Word.cmp.fin(b3, True{}, Word.cmp.fin(b4, True{}, Word.cmp.fin(b5, True{}, cc))))))))

# the char of six low bits and zeros above them
def dg.ch(b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool) -> Char:
  Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, Eq.zw(26n)}}}}}}}}

# the six low bits of a digit, highest first: ten patterns are the digits,
# and the others compare below 48 or above 57
def dg.bits(
  -P: Char -> Type,
  +b5: Bool,
  +b4: Bool,
  +b3: Bool,
  +b2: Bool,
  +b1: Bool,
  +b0: Bool,
  h: {dg.cp(b0, b1, b2, b3, b4, b5, EQ{}) == True{} : Bool},
  p0: P('0'),
  p1: P('1'),
  p2: P('2'),
  p3: P('3'),
  p4: P('4'),
  p5: P('5'),
  p6: P('6'),
  p7: P('7'),
  p8: P('8'),
  p9: P('9')
) -> P(dg.ch(b0, b1, b2, b3, b4, b5)):
  match b5:
    case False{}:
      Eq.bit.absurd(&1, P(dg.ch(b0, b1, b2, b3, b4, False{})), h)
    case True{}:
      match b4:
        case False{}:
          Eq.bit.absurd(&1, P(dg.ch(b0, b1, b2, b3, False{}, True{})), h)
        case True{}:
          match b3:
            case False{}:
              match b2 b1 b0:
                case False{} False{} False{}:
                  p0
                case False{} False{} True{}:
                  p1
                case False{} True{} False{}:
                  p2
                case False{} True{} True{}:
                  p3
                case True{} False{} False{}:
                  p4
                case True{} False{} True{}:
                  p5
                case True{} True{} False{}:
                  p6
                case True{} True{} True{}:
                  p7
            case True{}:
              match b2:
                case True{}:
                  Eq.bit.absurd(&1, P(dg.ch(b0, b1, True{}, True{}, True{}, True{})), h)
                case False{}:
                  match b1:
                    case True{}:
                      Eq.bit.absurd(&1, P(dg.ch(b0, True{}, False{}, True{}, True{}, True{})), h)
                    case False{}:
                      match b0:
                        case False{}:
                          p8
                        case True{}:
                          p9

# the bits above the sixth compare as cc with zero: they are zero, or the
# code point is above 57
def dg.at(
  -P: Char -> Type,
  cc: Cmp,
  +b5: Bool,
  +b4: Bool,
  +b3: Bool,
  +b2: Bool,
  +b1: Bool,
  +b0: Bool,
  +rest: Word(26n),
  ec: {Word.cmp(26n, rest, Eq.zw(26n)) == cc : Cmp},
  h: {dg.cp(b0, b1, b2, b3, b4, b5, cc) == True{} : Bool},
  p0: P('0'),
  p1: P('1'),
  p2: P('2'),
  p3: P('3'),
  p4: P('4'),
  p5: P('5'),
  p6: P('6'),
  p7: P('7'),
  p8: P('8'),
  p9: P('9')
) -> P(Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}}}):
  match cc:
    case LT{}:
      Eq.bit.gone(&1, P(Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}}}),
        Eq.bit.clash2(Equal.trans(Bool, True{}, Cmp.is_lt(Word.cmp(26n, rest, Eq.zw(26n))), False{},
          Equal.sym(Bool, Cmp.is_lt(Word.cmp(26n, rest, Eq.zw(26n))), True{},
            Equal.cong(Cmp, Bool, xx => Cmp.is_lt(xx), Word.cmp(26n, rest, Eq.zw(26n)), LT{}, ec)),
          Eq.zw_nlt(26n, rest))))
    case GT{}:
      Eq.bit.absurd(&1, P(Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}}}), h)
    case EQ{}:
      er = Equal.sym(Word(26n), rest, Eq.zw(26n), Eq.word_eq(26n, rest, Eq.zw(26n), ec))
      %er : P(Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, _}}}}}}}})
      dg.bits(P, b5, b4, b3, b2, b1, b0, h, p0, p1, p2, p3, p4, p5, p6, p7, p8, p9)

# a claim made of each of the ten digits is made of every digit
def dg.elim(
  -P: Char -> Type,
  cc: Char,
  h: {Char.is_digit(cc) == True{} : Bool},
  p0: P('0'),
  p1: P('1'),
  p2: P('2'),
  p3: P('3'),
  p4: P('4'),
  p5: P('5'),
  p6: P('6'),
  p7: P('7'),
  p8: P('8'),
  p9: P('9')
) -> P(cc):
  match cc:
    case Chr{U32{WCon{+b0, WCon{+b1, WCon{+b2, WCon{+b3, WCon{+b4, WCon{+b5, +rest}}}}}}}}:
      dg.at(P, Word.cmp(26n, rest, Eq.zw(26n)), b5, b4, b3, b2, b1, b0, rest, {==}, h,
        p0, p1, p2, p3, p4, p5, p6, p7, p8, p9)

# the characters of a text, onto a list
def tl.onto(ss: String, ys: List<&2, Char>) -> List<&2, Char>:
  match ss:
    case SNil{}:
      ys
    case SCon{hh, tt}:
      hh <> tl.onto(tt, ys)

# reversing what a text was pushed onto puts the text back in front
def wd.rev(
  ss: String,
  acc: List<&2, Char>,
  ys: List<&2, Char>
) -> {List.reverse.go(&2, Char, rev.onto(ss, acc), ys) == List.reverse.go(&2, Char, acc, tl.onto(ss, ys)) :
  List<&2, Char>}:
  match ss:
    case SNil{}:
      {==}
    case SCon{hh, tt}:
      wd.rev(tt, hh <> acc, ys)

# a text's characters onto nothing are its characters
def tl.nil(ss: String) -> {tl.onto(ss, []) == String.to_list(ss) : List<&2, Char>}:
  match ss:
    case SNil{}:
      {==}
    case SCon{+hh, tt}:
      Equal.cong(List<&2, Char>, List<&2, Char>, ys => hh <> ys, tl.onto(tt, []), String.to_list(tt), tl.nil(tt))

# a bare value's first character and the rest, pushed, read back in order
def wd.order(
  +cc: Char,
  +tt: String
) -> {List.reverse(&2, Char, rev.onto(tt, [cc])) == String.to_list(SCon{cc, tt}) : List<&2, Char>}:
  Equal.trans(List<&2, Char>, List.reverse.go(&2, Char, rev.onto(tt, [cc]), []),
    List.reverse.go(&2, Char, [cc], tl.onto(tt, [])), String.to_list(SCon{cc, tt}),
    wd.rev(tt, [cc], []),
    Equal.cong(List<&2, Char>, List<&2, Char>, ys => cc <> ys, tl.onto(tt, []), String.to_list(tt), tl.nil(tt)))

# the head of an all-digits walk that answered True is a digit
def then.l(
  ok: Bool,
  tt: String,
  ee: {T.wf.then(ok, _u => T.wf.digits(tt)) == True{} : Bool}
) -> {ok == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      ee

# and the rest of it is all digits
def then.r(
  ok: Bool,
  tt: String,
  ee: {T.wf.then(ok, _u => T.wf.digits(tt)) == True{} : Bool}
) -> {T.wf.digits(tt) == True{} : Bool}:
  match ok:
    case True{}:
      ee
    case False{}:
      Eq.bit.absurd(&2, {T.wf.digits(tt) == True{} : Bool}, ee)

# a text's characters make the text again
def ftl(ss: String) -> {String.from_list(String.to_list(ss)) == ss : String}:
  match ss:
    case SNil{}:
      {==}
    case SCon{+hh, tt}:
      Equal.cong(String, String, zs => SCon{hh, zs}, String.from_list(String.to_list(tt)), tt, ftl(tt))

# A datetime's text as tokens: a digit of a remainder by ten, or a character
# written as itself (a separator, a zone mark, or a digit of the fraction).
type Tk is Data:
  TD{x: U32}
  TC{c: Char}

# the two digits pad2 writes for a value below one hundred
def d2(+nn: U32) -> List<&2, Tk>:
  [TD{U32.div(nn, 10)}, TD{nn}]

# the four digits pad4 writes for a value below ten thousand
def d4(+yy: U32) -> List<&2, Tk>:
  [TD{U32.div(U32.div(U32.div(yy, 10), 10), 10)}, TD{U32.div(U32.div(yy, 10), 10)}, TD{U32.div(yy, 10)}, TD{yy}]

# a truth read through an equation of bits
def bt(aa: Bool, bb: Bool, cc: Bool, ee: {aa == bb : Bool}, hh: {aa == cc : Bool}) -> {bb == cc : Bool}:
  Equal.trans(Bool, bb, aa, cc, Equal.sym(Bool, aa, bb, ee), hh)

# every pair's name in rows is missing from inl
def cv.fr(+inl: List<&2, T.Val>, rows: List<&2, T.Val>) -> Bool:
  match rows:
    case []:
      True{}
    case T.VPair{+kk, _vv} <> tt:
      Bool.and(L1.is_miss(T.get(inl, kk)), cv.fr(inl, tt))
    case _hh <> tt:
      cv.fr(inl, tt)

# two chars compare alike either way round
def cv.ceq.go(
  b1: Bool,
  b2: Bool,
  +xx: Char,
  +yy: Char,
  +e1: {Char.is_eq(xx, yy) == b1 : Bool},
  +e2: {Char.is_eq(yy, xx) == b2 : Bool}
) -> {b1 == b2 : Bool}:
  match b1:
    case True{}:
      match b2:
        case True{}:
          {==}
        case False{}:
          Equal.trans(Bool, True{}, Char.is_eq(yy, xx), False{},
            Equal.trans(Bool, True{}, Char.is_eq(yy, yy), Char.is_eq(yy, xx),
              Equal.sym(Bool, Char.is_eq(yy, yy), True{}, Eq.char_eq_self(yy)),
              Equal.cong(Char, Bool, cc => Char.is_eq(yy, cc), yy, xx,
                Equal.sym(Char, xx, yy, Eq.char_eq_true(xx, yy, e1)))), e2)
    case False{}:
      match b2:
        case True{}:
          Equal.trans(Bool, False{}, Char.is_eq(xx, yy), True{}, Equal.sym(Bool, Char.is_eq(xx, yy), False{}, e1),
            Equal.trans(Bool, Char.is_eq(xx, yy), Char.is_eq(xx, xx), True{},
              Equal.cong(Char, Bool, cc => Char.is_eq(xx, cc), yy, xx, Eq.char_eq_true(yy, xx, e2)),
              Eq.char_eq_self(xx)))
        case False{}:
          {==}

# two chars compare alike either way round
def cv.ceq.sym(+xx: Char, +yy: Char) -> {Char.is_eq(xx, yy) == Char.is_eq(yy, xx) : Bool}:
  cv.ceq.go(Char.is_eq(xx, yy), Char.is_eq(yy, xx), xx, yy, {==}, {==})

# and so do two strings, from any start
def cv.seqs(
  aa: String,
  bb: String,
  ss: Bool
) -> {T.str.eq.step(aa, bb, ss) == T.str.eq.step(bb, aa, ss) : Bool}:
  match aa:
    case SNil{}:
      match bb:
        case SNil{}:
          match ss:
            case True{}:
              {==}
            case False{}:
              {==}
        case SCon{_y, _yt}:
          match ss:
            case True{}:
              {==}
            case False{}:
              {==}
    case SCon{+xx, +xt}:
      match bb:
        case SNil{}:
          match ss:
            case True{}:
              {==}
            case False{}:
              {==}
        case SCon{+yy, +yt}:
          match ss:
            case True{}:
              Equal.trans(Bool, T.str.eq.step(xt, yt, Char.is_eq(xx, yy)), T.str.eq.step(yt, xt, Char.is_eq(xx, yy)),
                T.str.eq.step(yt, xt, Char.is_eq(yy, xx)), cv.seqs(xt, yt, Char.is_eq(xx, yy)),
                Equal.cong(Bool, Bool, bt => T.str.eq.step(yt, xt, bt), Char.is_eq(xx, yy), Char.is_eq(yy, xx),
                  cv.ceq.sym(xx, yy)))
            case False{}:
              {==}

# a lookup that passes a pair tells its name was not the one looked for
def cv.fs.l(
  bb: Bool,
  +xx: T.Val,
  -more: Unit -> T.Hit,
  hh: {T.wf.fresh(T.find.step(bb, xx, more)) == True{} : Bool}
) -> {bb == False{} : Bool}:
  match bb:
    case True{}:
      Eq.bit.absurd(&2, {True{} == False{} : Bool}, hh)
    case False{}:
      {==}

# and goes on to the rest
def cv.fs.r(
  bb: Bool,
  +xx: T.Val,
  -more: Unit -> T.Hit,
  hh: {T.wf.fresh(T.find.step(bb, xx, more)) == True{} : Bool}
) -> {T.wf.fresh(more(Unit{})) == True{} : Bool}:
  match bb:
    case True{}:
      Eq.bit.absurd(&2, {T.wf.fresh(more(Unit{})) == True{} : Bool}, hh)
    case False{}:
      hh

# Lists and walks. The document induction keeps the root as tb.set of the
# current table's rows into a fixed root, so the walk's contracts compose: a
# second set along the same path replaces the first, a set along a longer path
# is a set along the shorter one of a set in the table there, and a set into a
# pair at the head of a table's rows changes that pair only.

# appending lists of values is associative
def va.assoc(
  xs: List<&2, T.Val>,
  +ys: List<&2, T.Val>,
  +zs: List<&2, T.Val>
) -> {List.append(&2, T.Val, List.append(&2, T.Val, xs, ys), zs)
  == List.append(&2, T.Val, xs, List.append(&2, T.Val, ys, zs)) : List<&2, T.Val>}:
  match xs:
    case []:
      {==}
    case +xx <> rest:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, tt => xx <> tt,
        List.append(&2, T.Val, List.append(&2, T.Val, rest, ys), zs),
        List.append(&2, T.Val, rest, List.append(&2, T.Val, ys, zs)), va.assoc(rest, ys, zs))

# The key pass. A table's pairs that are no table are read one line each,
# in order, and each is put at the head of the current table's rows. Its name
# must be none of the names read so far in this table (cv.fr); wf says each
# name is none of the later pairs', and nd carries that over the order the
# pairs are read in: the pairs that are no table, then the tables.

# every pair's name is none of the later pairs' names
def nd(xs: List<&2, T.Val>) -> Bool:
  match xs:
    case []:
      True{}
    case T.VPair{+nn, _vv} <> +tt:
      Bool.and(T.wf.fresh(T.get(tt, nn)), nd(tt))
    case _hh <> tt:
      nd(tt)

# Names. wf says each pair's name is none of the later pairs'. parse reads
# a table's pairs that are no table first, then its tables, so the pairs are
# put in that order; nd holds of it too, since a name missing from a list is
# missing from any part of it, and one missing from two lists is missing from
# both together.

# a lookup that passes a pair whose name is not the one looked for misses
# when the rest does
def fs.join(
  bb: Bool,
  +xx: T.Val,
  -more: Unit -> T.Hit,
  +eb: {bb == False{} : Bool},
  +hm: {T.wf.fresh(more(Unit{})) == True{} : Bool}
) -> {T.wf.fresh(T.find.step(bb, xx, more)) == True{} : Bool}:
  match bb:
    case True{}:
      Eq.bit.absurd2(&2, {T.wf.fresh(T.find.step(True{}, xx, more)) == True{} : Bool}, eb)
    case False{}:
      hm

# a name missing from two lists is missing from both together
def fr.app(
  aa: List<&2, T.Val>,
  +bb: List<&2, T.Val>,
  +kk: String,
  +ea: {T.wf.fresh(T.get(aa, kk)) == True{} : Bool},
  +eb: {T.wf.fresh(T.get(bb, kk)) == True{} : Bool}
) -> {T.wf.fresh(T.get(List.append(&2, T.Val, aa, bb), kk)) == True{} : Bool}:
  match aa:
    case []:
      eb
    case T.VPair{+nn, +vv} <> +t:
      fs.join(T.str.eq(nn, kk), vv, _u => T.rows.find(List.append(&2, T.Val, t, bb), kk),
        cv.fs.l(T.str.eq(nn, kk), vv, _u => T.rows.find(t, kk), ea),
        fr.app(t, bb, kk, cv.fs.r(T.str.eq(nn, kk), vv, _u => T.rows.find(t, kk), ea), eb))

    case T.VStr{_a1} <> +t:
      fr.app(t, bb, kk, ea, eb)
    case T.VSpan{_a1, _a2} <> +t:
      fr.app(t, bb, kk, ea, eb)
    case T.VInt{_a1, _a2} <> +t:
      fr.app(t, bb, kk, ea, eb)
    case T.VFlo{_a1, _a2} <> +t:
      fr.app(t, bb, kk, ea, eb)
    case T.VBool{_a1} <> +t:
      fr.app(t, bb, kk, ea, eb)
    case T.VWhen{_a1} <> +t:
      fr.app(t, bb, kk, ea, eb)
    case T.VArr{_a1} <> +t:
      fr.app(t, bb, kk, ea, eb)
    case T.VInl{_a1} <> +t:
      fr.app(t, bb, kk, ea, eb)
    case T.VHead{_a1, _a2} <> +t:
      fr.app(t, bb, kk, ea, eb)
    case T.VAot{_a1, _a2} <> +t:
      fr.app(t, bb, kk, ea, eb)
    case T.VAots{_a1, _a2} <> +t:
      fr.app(t, bb, kk, ea, eb)

# a name missing from a table's rows is missing from its pairs that are no
# table
def fr.keys(
  xs: List<&2, T.Val>,
  +kk: String,
  +ee: {T.wf.fresh(T.get(xs, kk)) == True{} : Bool}
) -> {T.wf.fresh(T.get(D1.canon.keys(xs), kk)) == True{} : Bool}:
  match xs:
    case []:
      {==}

    case T.VPair{+nn, T.VStr{+a1}} <> +t:
      fs.join(T.str.eq(nn, kk), T.VStr{a1}, _u => T.rows.find(D1.canon.keys(t), kk),
        cv.fs.l(T.str.eq(nn, kk), T.VStr{a1}, _u => T.rows.find(t, kk), ee),
        fr.keys(t, kk, cv.fs.r(T.str.eq(nn, kk), T.VStr{a1}, _u => T.rows.find(t, kk), ee)))
    case T.VPair{+nn, T.VSpan{+a1, +a2}} <> +t:
      fs.join(T.str.eq(nn, kk), T.VSpan{a1, a2}, _u => T.rows.find(D1.canon.keys(t), kk),
        cv.fs.l(T.str.eq(nn, kk), T.VSpan{a1, a2}, _u => T.rows.find(t, kk), ee),
        fr.keys(t, kk, cv.fs.r(T.str.eq(nn, kk), T.VSpan{a1, a2}, _u => T.rows.find(t, kk), ee)))
    case T.VPair{+nn, T.VInt{+a1, +a2}} <> +t:
      fs.join(T.str.eq(nn, kk), T.VInt{a1, a2}, _u => T.rows.find(D1.canon.keys(t), kk),
        cv.fs.l(T.str.eq(nn, kk), T.VInt{a1, a2}, _u => T.rows.find(t, kk), ee),
        fr.keys(t, kk, cv.fs.r(T.str.eq(nn, kk), T.VInt{a1, a2}, _u => T.rows.find(t, kk), ee)))
    case T.VPair{+nn, T.VFlo{+a1, +a2}} <> +t:
      fs.join(T.str.eq(nn, kk), T.VFlo{a1, a2}, _u => T.rows.find(D1.canon.keys(t), kk),
        cv.fs.l(T.str.eq(nn, kk), T.VFlo{a1, a2}, _u => T.rows.find(t, kk), ee),
        fr.keys(t, kk, cv.fs.r(T.str.eq(nn, kk), T.VFlo{a1, a2}, _u => T.rows.find(t, kk), ee)))
    case T.VPair{+nn, T.VBool{+a1}} <> +t:
      fs.join(T.str.eq(nn, kk), T.VBool{a1}, _u => T.rows.find(D1.canon.keys(t), kk),
        cv.fs.l(T.str.eq(nn, kk), T.VBool{a1}, _u => T.rows.find(t, kk), ee),
        fr.keys(t, kk, cv.fs.r(T.str.eq(nn, kk), T.VBool{a1}, _u => T.rows.find(t, kk), ee)))
    case T.VPair{+nn, T.VWhen{+a1}} <> +t:
      fs.join(T.str.eq(nn, kk), T.VWhen{a1}, _u => T.rows.find(D1.canon.keys(t), kk),
        cv.fs.l(T.str.eq(nn, kk), T.VWhen{a1}, _u => T.rows.find(t, kk), ee),
        fr.keys(t, kk, cv.fs.r(T.str.eq(nn, kk), T.VWhen{a1}, _u => T.rows.find(t, kk), ee)))
    case T.VPair{+nn, T.VArr{+a1}} <> +t:
      fs.join(T.str.eq(nn, kk), T.VArr{a1}, _u => T.rows.find(D1.canon.keys(t), kk),
        cv.fs.l(T.str.eq(nn, kk), T.VArr{a1}, _u => T.rows.find(t, kk), ee),
        fr.keys(t, kk, cv.fs.r(T.str.eq(nn, kk), T.VArr{a1}, _u => T.rows.find(t, kk), ee)))
    case T.VPair{+nn, T.VInl{+a1}} <> +t:
      fs.join(T.str.eq(nn, kk), T.VInl{a1}, _u => T.rows.find(D1.canon.keys(t), kk),
        cv.fs.l(T.str.eq(nn, kk), T.VInl{a1}, _u => T.rows.find(t, kk), ee),
        fr.keys(t, kk, cv.fs.r(T.str.eq(nn, kk), T.VInl{a1}, _u => T.rows.find(t, kk), ee)))
    case T.VPair{+nn, T.VHead{+a1, +a2}} <> +t:
      fr.keys(t, kk, cv.fs.r(T.str.eq(nn, kk), T.VHead{a1, a2}, _u => T.rows.find(t, kk), ee))
    case T.VPair{+nn, T.VAot{+a1, +a2}} <> +t:
      fs.join(T.str.eq(nn, kk), T.VAot{a1, a2}, _u => T.rows.find(D1.canon.keys(t), kk),
        cv.fs.l(T.str.eq(nn, kk), T.VAot{a1, a2}, _u => T.rows.find(t, kk), ee),
        fr.keys(t, kk, cv.fs.r(T.str.eq(nn, kk), T.VAot{a1, a2}, _u => T.rows.find(t, kk), ee)))
    case T.VPair{+nn, T.VAots{+a1, +a2}} <> +t:
      fr.keys(t, kk, cv.fs.r(T.str.eq(nn, kk), T.VAots{a1, a2}, _u => T.rows.find(t, kk), ee))
    case T.VPair{+nn, T.VPair{+a1, +a2}} <> +t:
      fs.join(T.str.eq(nn, kk), T.VPair{a1, a2}, _u => T.rows.find(D1.canon.keys(t), kk),
        cv.fs.l(T.str.eq(nn, kk), T.VPair{a1, a2}, _u => T.rows.find(t, kk), ee),
        fr.keys(t, kk, cv.fs.r(T.str.eq(nn, kk), T.VPair{a1, a2}, _u => T.rows.find(t, kk), ee)))
    case T.VStr{_a1} <> +t:
      fr.keys(t, kk, ee)
    case T.VSpan{_a1, _a2} <> +t:
      fr.keys(t, kk, ee)
    case T.VInt{_a1, _a2} <> +t:
      fr.keys(t, kk, ee)
    case T.VFlo{_a1, _a2} <> +t:
      fr.keys(t, kk, ee)
    case T.VBool{_a1} <> +t:
      fr.keys(t, kk, ee)
    case T.VWhen{_a1} <> +t:
      fr.keys(t, kk, ee)
    case T.VArr{_a1} <> +t:
      fr.keys(t, kk, ee)
    case T.VInl{_a1} <> +t:
      fr.keys(t, kk, ee)
    case T.VHead{_a1, _a2} <> +t:
      fr.keys(t, kk, ee)
    case T.VAot{_a1, _a2} <> +t:
      fr.keys(t, kk, ee)
    case T.VAots{_a1, _a2} <> +t:
      fr.keys(t, kk, ee)

# The same document. canon is the document with each table's pairs that are
# no table moved in front of its tables and every span read out. same
# compares a table as the pairs it holds, each against the other table's
# first pair of its name, so moving a pair past pairs of other names changes
# nothing, and own changes nothing either (own.l, own.r).

# a lookup that missed is one wf.fresh reads so
def miss.fresh(hh: T.Hit) -> {L1.is_miss(hh) == T.wf.fresh(hh) : Bool}:
  match hh:
    case T.Miss{}:
      {==}
    case T.Found{_v}:
      {==}

# the pick of nn from the rows f2, then nn's pair, then rr
def pk.afT(
  +f2: List<&2, T.Val>,
  +nn: String,
  +xx: T.Val,
  +rr: List<&2, T.Val>
) -> Type:
  {D1.pick(List.append(&2, T.Val, f2, T.VPair{nn, xx} <> rr), nn) == D1.Picked{xx, List.append(&2, T.Val, f2,
    rr)} : D1.Pick}

# one pair of the rows before the one picked
def pk.af.p(
  bb: Bool,
  +mm: String,
  +ww: T.Val,
  +nn: String,
  +xx: T.Val,
  +f2: List<&2, T.Val>,
  +rr: List<&2, T.Val>,
  eb: {bb == False{} : Bool},
  ih: pk.afT(f2, nn, xx, rr)
) -> {D1.pick.step(bb, mm, ww, List.append(&2, T.Val, f2, T.VPair{nn, xx} <> rr), _u => D1.pick(List.append(&2,
  T.Val, f2, T.VPair{nn, xx} <> rr), nn))
  == D1.Picked{xx, T.VPair{mm, ww} <> List.append(&2, T.Val, f2, rr)} : D1.Pick}:
  match bb:
    case True{}:
      Eq.bit.absurd2(&2, {D1.pick.step(True{}, mm, ww, List.append(&2, T.Val, f2, T.VPair{nn, xx} <> rr),
        _u => D1.pick(List.append(&2, T.Val, f2, T.VPair{nn, xx} <> rr), nn)) == D1.Picked{xx, T.VPair{mm,
        ww} <> List.append(&2, T.Val, f2, rr)} : D1.Pick}, eb)
    case False{}:
      Equal.cong(D1.Pick, D1.Pick, pk => D1.pick.cons(T.VPair{mm, ww}, pk), D1.pick(List.append(&2, T.Val, f2,
        T.VPair{nn, xx} <> rr), nn), D1.Picked{xx, List.append(&2, T.Val, f2, rr)}, ih)

# a pair behind rows that do not hold its name is what a pick of its name
# takes, with those rows kept in front of the rest
def pk.af(
  ff: List<&2, T.Val>,
  +nn: String,
  +xx: T.Val,
  +rr: List<&2, T.Val>,
  +em: {T.wf.fresh(T.get(ff, nn)) == True{} : Bool}
) -> {D1.pick(List.append(&2, T.Val, ff, T.VPair{nn, xx} <> rr), nn) == D1.Picked{xx, List.append(&2, T.Val, ff,
  rr)} : D1.Pick}:
  match ff:
    case []:
      M1.pick.self(nn, xx, rr)
    case T.VPair{+mm, +ww} <> +f2:
      pk.af.p(String.eq(mm, nn), mm, ww, nn, xx, f2, rr,
        Equal.trans(Bool, String.eq(mm, nn), T.str.eq(mm, nn), False{}, Equal.sym(Bool, T.str.eq(mm, nn), String.eq(mm,
          nn), M1.str.eq.agree(mm, nn)), cv.fs.l(T.str.eq(mm, nn), ww, _u => T.rows.find(f2, nn), em)),
        pk.af(f2, nn, xx, rr, cv.fs.r(T.str.eq(mm, nn), ww, _u => T.rows.find(f2, nn), em)))
    case T.VStr{+a1} <> +f2:
      Equal.cong(D1.Pick, D1.Pick, pk => D1.pick.cons(T.VStr{a1}, pk), D1.pick(List.append(&2, T.Val, f2,
        T.VPair{nn, xx} <> rr), nn),
        D1.Picked{xx, List.append(&2, T.Val, f2, rr)}, pk.af(f2, nn, xx, rr, em))
    case T.VSpan{+a1, +a2} <> +f2:
      Equal.cong(D1.Pick, D1.Pick, pk => D1.pick.cons(T.VSpan{a1, a2}, pk), D1.pick(List.append(&2, T.Val, f2,
        T.VPair{nn, xx} <> rr), nn),
        D1.Picked{xx, List.append(&2, T.Val, f2, rr)}, pk.af(f2, nn, xx, rr, em))
    case T.VInt{+a1, +a2} <> +f2:
      Equal.cong(D1.Pick, D1.Pick, pk => D1.pick.cons(T.VInt{a1, a2}, pk), D1.pick(List.append(&2, T.Val, f2,
        T.VPair{nn, xx} <> rr), nn),
        D1.Picked{xx, List.append(&2, T.Val, f2, rr)}, pk.af(f2, nn, xx, rr, em))
    case T.VFlo{+a1, +a2} <> +f2:
      Equal.cong(D1.Pick, D1.Pick, pk => D1.pick.cons(T.VFlo{a1, a2}, pk), D1.pick(List.append(&2, T.Val, f2,
        T.VPair{nn, xx} <> rr), nn),
        D1.Picked{xx, List.append(&2, T.Val, f2, rr)}, pk.af(f2, nn, xx, rr, em))
    case T.VBool{+a1} <> +f2:
      Equal.cong(D1.Pick, D1.Pick, pk => D1.pick.cons(T.VBool{a1}, pk), D1.pick(List.append(&2, T.Val, f2,
        T.VPair{nn, xx} <> rr), nn),
        D1.Picked{xx, List.append(&2, T.Val, f2, rr)}, pk.af(f2, nn, xx, rr, em))
    case T.VWhen{+a1} <> +f2:
      Equal.cong(D1.Pick, D1.Pick, pk => D1.pick.cons(T.VWhen{a1}, pk), D1.pick(List.append(&2, T.Val, f2,
        T.VPair{nn, xx} <> rr), nn),
        D1.Picked{xx, List.append(&2, T.Val, f2, rr)}, pk.af(f2, nn, xx, rr, em))
    case T.VArr{+a1} <> +f2:
      Equal.cong(D1.Pick, D1.Pick, pk => D1.pick.cons(T.VArr{a1}, pk), D1.pick(List.append(&2, T.Val, f2,
        T.VPair{nn, xx} <> rr), nn),
        D1.Picked{xx, List.append(&2, T.Val, f2, rr)}, pk.af(f2, nn, xx, rr, em))
    case T.VInl{+a1} <> +f2:
      Equal.cong(D1.Pick, D1.Pick, pk => D1.pick.cons(T.VInl{a1}, pk), D1.pick(List.append(&2, T.Val, f2,
        T.VPair{nn, xx} <> rr), nn),
        D1.Picked{xx, List.append(&2, T.Val, f2, rr)}, pk.af(f2, nn, xx, rr, em))
    case T.VHead{+a1, +a2} <> +f2:
      Equal.cong(D1.Pick, D1.Pick, pk => D1.pick.cons(T.VHead{a1, a2}, pk), D1.pick(List.append(&2, T.Val, f2,
        T.VPair{nn, xx} <> rr), nn),
        D1.Picked{xx, List.append(&2, T.Val, f2, rr)}, pk.af(f2, nn, xx, rr, em))
    case T.VAot{+a1, +a2} <> +f2:
      Equal.cong(D1.Pick, D1.Pick, pk => D1.pick.cons(T.VAot{a1, a2}, pk), D1.pick(List.append(&2, T.Val, f2,
        T.VPair{nn, xx} <> rr), nn),
        D1.Picked{xx, List.append(&2, T.Val, f2, rr)}, pk.af(f2, nn, xx, rr, em))
    case T.VAots{+a1, +a2} <> +f2:
      Equal.cong(D1.Pick, D1.Pick, pk => D1.pick.cons(T.VAots{a1, a2}, pk), D1.pick(List.append(&2, T.Val, f2,
        T.VPair{nn, xx} <> rr), nn),
        D1.Picked{xx, List.append(&2, T.Val, f2, rr)}, pk.af(f2, nn, xx, rr, em))

# a name every pair of a list is missing from stays missing from rows with a
# pair of a name none of the list's has behind them
def fr.snoc(
  ls: List<&2, T.Val>,
  +ff: List<&2, T.Val>,
  +nn: String,
  +xx: T.Val,
  +h1: {cv.fr(ff, ls) == True{} : Bool},
  +h2: {T.wf.fresh(T.get(ls, nn)) == True{} : Bool}
) -> {cv.fr(List.append(&2, T.Val, ff, [T.VPair{nn, xx}]), ls) == True{} : Bool}:
  match ls:
    case []:
      {==}
    case T.VPair{+kk, +vv} <> +t:
      +e1 = {cv.fs.l(T.str.eq(kk, nn), vv, _u => T.rows.find(t, nn), h2) : {T.str.eq(kk, nn) == False{} : Bool}}
      +e2 = {Equal.trans(Bool, T.str.eq(nn, kk), T.str.eq(kk, nn), False{}, cv.seqs(nn, kk, True{}), e1)
        : {T.str.eq(nn, kk) == False{} : Bool}}
      M2.cv.and2(L1.is_miss(T.get(List.append(&2, T.Val, ff, [T.VPair{nn, xx}]), kk)), cv.fr(List.append(&2, T.Val, ff,
        [T.VPair{nn, xx}]), t),
        Equal.trans(Bool, L1.is_miss(T.get(List.append(&2, T.Val, ff, [T.VPair{nn, xx}]), kk)),
          T.wf.fresh(T.get(List.append(&2, T.Val, ff, [T.VPair{nn, xx}]), kk)), True{},
          miss.fresh(T.get(List.append(&2, T.Val, ff, [T.VPair{nn, xx}]), kk)),
          fr.app(ff, [T.VPair{nn, xx}], kk, Equal.trans(Bool, T.wf.fresh(T.get(ff, kk)), L1.is_miss(T.get(ff, kk)),
            True{},
            Equal.sym(Bool, L1.is_miss(T.get(ff, kk)), T.wf.fresh(T.get(ff, kk)), miss.fresh(T.get(ff, kk))),
            Eq.and.left(L1.is_miss(T.get(ff, kk)), cv.fr(ff, t), h1)),
            fs.join(T.str.eq(nn, kk), xx, _u => T.rows.find([], kk), e2, {==}))),
        fr.snoc(t, ff, nn, xx, Eq.and.right(L1.is_miss(T.get(ff, kk)), cv.fr(ff, t), h1),
          cv.fs.r(T.str.eq(kk, nn), vv, _u => T.rows.find(t, nn), h2)))
    case T.VStr{_a1} <> +t:
      fr.snoc(t, ff, nn, xx, h1, h2)
    case T.VSpan{_a1, _a2} <> +t:
      fr.snoc(t, ff, nn, xx, h1, h2)
    case T.VInt{_a1, _a2} <> +t:
      fr.snoc(t, ff, nn, xx, h1, h2)
    case T.VFlo{_a1, _a2} <> +t:
      fr.snoc(t, ff, nn, xx, h1, h2)
    case T.VBool{_a1} <> +t:
      fr.snoc(t, ff, nn, xx, h1, h2)
    case T.VWhen{_a1} <> +t:
      fr.snoc(t, ff, nn, xx, h1, h2)
    case T.VArr{_a1} <> +t:
      fr.snoc(t, ff, nn, xx, h1, h2)
    case T.VInl{_a1} <> +t:
      fr.snoc(t, ff, nn, xx, h1, h2)
    case T.VHead{_a1, _a2} <> +t:
      fr.snoc(t, ff, nn, xx, h1, h2)
    case T.VAot{_a1, _a2} <> +t:
      fr.snoc(t, ff, nn, xx, h1, h2)
    case T.VAots{_a1, _a2} <> +t:
      fr.snoc(t, ff, nn, xx, h1, h2)

# a table's tables and arrays of tables, in order, as they are
def rtabs(xs: List<&2, T.Val>) -> List<&2, T.Val>:
  match xs:
    case []:
      []
    case T.VPair{nn, T.VHead{pp, rr}} <> tt:
      T.VPair{nn, T.VHead{pp, rr}} <> rtabs(tt)
    case T.VPair{nn, T.VAots{pp, es}} <> tt:
      T.VPair{nn, T.VAots{pp, es}} <> rtabs(tt)
    case _hh <> tt:
      rtabs(tt)

# comparing a table's pairs that are no table, then any rows, against the
# table's rows behind any rows ff none of their names are in: each such pair
# picks itself, and what is left is ff and the table's tables
def pk(
  o: List<&2, T.Val>,
  +hp: String,
  +zz: List<&2, T.Val>,
  +ff: List<&2, T.Val>,
  +hw: {T.wf.go(o, T.WfRows{hp}) == True{} : Bool},
  +hs: {M1.selfs(o) == True{} : Bool},
  +hf: {cv.fr(ff, D1.canon.keys(o)) == True{} : Bool}
) -> {D1.same.go(List.append(&2, T.Val, D1.canon.keys(o), zz), List.append(&2, T.Val, ff, o)) == D1.same.go(zz,
  List.append(&2, T.Val, ff, rtabs(o))) : Bool}:
  match o:
    case []:
      {==}
    case T.VPair{+kk, T.VHead{+p, +r}} <> +t:
      +fr = {Eq.and.right(T.wf.text(kk), T.wf.fresh(T.get(t, kk)), Eq.and.left(T.wf.key(kk, t), T.str.eq(p,
        T.tree.pre(hp, kk)), M2.wt.ok(Bool.and(T.wf.key(kk, t), T.str.eq(p, T.tree.pre(hp, kk))),
        _u => T.wf.then(T.wf.go(r, T.WfRows{p}), _v => T.wf.go(t, T.WfRows{hp})), hw))) : {T.wf.fresh(T.get(t,
        kk)) == True{} : Bool}}
      Equal.trans(Bool, D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz), List.append(&2, T.Val, ff,
        T.VPair{kk, T.VHead{p, r}} <> t)),
        D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz), List.append(&2, T.Val, List.append(&2, T.Val, ff,
          [T.VPair{kk, T.VHead{p, r}}]), t)),
        D1.same.go(zz, List.append(&2, T.Val, ff, T.VPair{kk, T.VHead{p, r}} <> rtabs(t))),
        Equal.cong(List<&2, T.Val>, Bool, ys => D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz), ys),
          List.append(&2, T.Val, ff, T.VPair{kk, T.VHead{p, r}} <> t),
          List.append(&2, T.Val, List.append(&2, T.Val, ff, [T.VPair{kk, T.VHead{p, r}}]), t),
            Equal.sym(List<&2, T.Val>, List.append(&2, T.Val, List.append(&2, T.Val, ff, [T.VPair{kk, T.VHead{p, r}}]),
            t), List.append(&2, T.Val, ff, T.VPair{kk, T.VHead{p, r}} <> t), va.assoc(ff,
          [T.VPair{kk, T.VHead{p, r}}], t))),
        Equal.trans(Bool, D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz), List.append(&2, T.Val,
          List.append(&2, T.Val, ff, [T.VPair{kk, T.VHead{p, r}}]), t)),
          D1.same.go(zz, List.append(&2, T.Val, List.append(&2, T.Val, ff, [T.VPair{kk, T.VHead{p, r}}]), rtabs(t))),
            D1.same.go(zz, List.append(&2, T.Val, ff, T.VPair{kk, T.VHead{p, r}} <> rtabs(t))),
          pk(t, hp, zz, List.append(&2, T.Val, ff, [T.VPair{kk, T.VHead{p, r}}]), M2.wt.more(T.wf.go(r, T.WfRows{p}),
            _v => T.wf.go(t, T.WfRows{hp}), M2.wt.more(Bool.and(T.wf.key(kk, t), T.str.eq(p, T.tree.pre(hp, kk))),
            _u => T.wf.then(T.wf.go(r, T.WfRows{p}), _v => T.wf.go(t, T.WfRows{hp})), hw)),
            Eq.and.right(D1.same.go(T.VPair{kk, T.VHead{p, r}} <> [], T.VPair{kk, T.VHead{p, r}} <> []),
            M1.selfs(t), hs), fr.snoc(D1.canon.keys(t), ff, kk, T.VHead{p, r}, hf, fr.keys(t, kk, fr))),
          Equal.cong(List<&2, T.Val>, Bool, ys => D1.same.go(zz, ys), List.append(&2, T.Val, List.append(&2, T.Val,
            ff, [T.VPair{kk, T.VHead{p, r}}]), rtabs(t)),
            List.append(&2, T.Val, ff, T.VPair{kk, T.VHead{p, r}} <> rtabs(t)), va.assoc(ff, [T.VPair{kk, T.VHead{p,
              r}}], rtabs(t)))))
    case T.VPair{+kk, T.VAots{+p, +r}} <> +t:
      +fr = {Eq.and.right(T.wf.text(kk), T.wf.fresh(T.get(t, kk)), Eq.and.left(T.wf.key(kk, t), T.str.eq(p,
        T.tree.pre(hp, kk)), Eq.and.right(Bool.not(List.is_empty(&2, T.Val, r)), Bool.and(T.wf.key(kk, t), T.str.eq(p,
        T.tree.pre(hp, kk))), M2.wt.ok(Bool.and(Bool.not(List.is_empty(&2, T.Val, r)), Bool.and(T.wf.key(kk, t),
        T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(r, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp})),
        hw)))) : {T.wf.fresh(T.get(t, kk)) == True{} : Bool}}
      Equal.trans(Bool, D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz), List.append(&2, T.Val, ff,
        T.VPair{kk, T.VAots{p, r}} <> t)),
        D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz), List.append(&2, T.Val, List.append(&2, T.Val, ff,
          [T.VPair{kk, T.VAots{p, r}}]), t)),
        D1.same.go(zz, List.append(&2, T.Val, ff, T.VPair{kk, T.VAots{p, r}} <> rtabs(t))),
        Equal.cong(List<&2, T.Val>, Bool, ys => D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz), ys),
          List.append(&2, T.Val, ff, T.VPair{kk, T.VAots{p, r}} <> t),
          List.append(&2, T.Val, List.append(&2, T.Val, ff, [T.VPair{kk, T.VAots{p, r}}]), t),
            Equal.sym(List<&2, T.Val>, List.append(&2, T.Val, List.append(&2, T.Val, ff, [T.VPair{kk, T.VAots{p, r}}]),
            t), List.append(&2, T.Val, ff, T.VPair{kk, T.VAots{p, r}} <> t), va.assoc(ff,
          [T.VPair{kk, T.VAots{p, r}}], t))),
        Equal.trans(Bool, D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz), List.append(&2, T.Val,
          List.append(&2, T.Val, ff, [T.VPair{kk, T.VAots{p, r}}]), t)),
          D1.same.go(zz, List.append(&2, T.Val, List.append(&2, T.Val, ff, [T.VPair{kk, T.VAots{p, r}}]), rtabs(t))),
            D1.same.go(zz, List.append(&2, T.Val, ff, T.VPair{kk, T.VAots{p, r}} <> rtabs(t))),
          pk(t, hp, zz, List.append(&2, T.Val, ff, [T.VPair{kk, T.VAots{p, r}}]), M2.wt.more(T.wf.go(r, T.WfElems{p}),
            _v => T.wf.go(t, T.WfRows{hp}), M2.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, r)),
            Bool.and(T.wf.key(kk, t), T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(r, T.WfElems{p}),
            _v => T.wf.go(t, T.WfRows{hp})), hw)), Eq.and.right(D1.same.go(T.VPair{kk, T.VAots{p, r}} <> [],
            T.VPair{kk, T.VAots{p, r}} <> []),
            M1.selfs(t), hs), fr.snoc(D1.canon.keys(t), ff, kk, T.VAots{p, r}, hf, fr.keys(t, kk, fr))),
          Equal.cong(List<&2, T.Val>, Bool, ys => D1.same.go(zz, ys), List.append(&2, T.Val, List.append(&2, T.Val,
            ff, [T.VPair{kk, T.VAots{p, r}}]), rtabs(t)),
            List.append(&2, T.Val, ff, T.VPair{kk, T.VAots{p, r}} <> rtabs(t)), va.assoc(ff, [T.VPair{kk, T.VAots{p,
              r}}], rtabs(t)))))
    case T.VPair{+kk, T.VStr{+a1}} <> +t:
      +hs1 = {Eq.and.left(D1.same.go(T.VPair{kk, T.VStr{a1}} <> [], T.VPair{kk, T.VStr{a1}} <> []), M1.selfs(t),
        hs) : {D1.same.go(T.VPair{kk, T.VStr{a1}} <> [], T.VPair{kk, T.VStr{a1}} <> [])
        == True{} : Bool}}
      Equal.trans(Bool, D1.same.go(T.VPair{kk, T.VStr{a1}} <> List.append(&2, T.Val, D1.canon.keys(t), zz),
        List.append(&2, T.Val, ff, T.VPair{kk, T.VStr{a1}} <> t)),
        D1.same.go(T.VPair{kk, T.VStr{a1}} <> List.append(&2, T.Val, D1.canon.keys(t), zz), T.VPair{kk,
          T.VStr{a1}} <> List.append(&2, T.Val, ff, t)),
        D1.same.go(zz, List.append(&2, T.Val, ff, rtabs(t))),
        M1.pick.same(kk, T.VStr{a1}, List.append(&2, T.Val, D1.canon.keys(t), zz), List.append(&2, T.Val, ff,
            T.VPair{kk,
          T.VStr{a1}} <> t), T.VPair{kk, T.VStr{a1}} <> List.append(&2, T.Val, ff, t),
          Equal.trans(D1.Pick, D1.pick(List.append(&2, T.Val, ff, T.VPair{kk, T.VStr{a1}} <> t), kk),
            D1.Picked{T.VStr{a1}, List.append(&2, T.Val, ff, t)},
            D1.pick(T.VPair{kk, T.VStr{a1}} <> List.append(&2, T.Val, ff, t), kk),
            pk.af(ff, kk, T.VStr{a1}, t, Equal.trans(Bool, T.wf.fresh(T.get(ff, kk)), L1.is_miss(T.get(ff, kk)),
              True{},
              Equal.sym(Bool, L1.is_miss(T.get(ff, kk)), T.wf.fresh(T.get(ff, kk)), miss.fresh(T.get(ff, kk))),
              Eq.and.left(L1.is_miss(T.get(ff, kk)), cv.fr(ff, D1.canon.keys(t)), hf))),
            Equal.sym(D1.Pick, D1.pick(T.VPair{kk, T.VStr{a1}} <> List.append(&2, T.Val, ff, t), kk),
              D1.Picked{T.VStr{a1}, List.append(&2, T.Val, ff, t)},
              M1.pick.self(kk, T.VStr{a1}, List.append(&2, T.Val, ff, t))))),
        Equal.trans(Bool, D1.same.go(T.VPair{kk, T.VStr{a1}} <> List.append(&2, T.Val, D1.canon.keys(t), zz),
          T.VPair{kk, T.VStr{a1}} <> List.append(&2, T.Val, ff, t)),
          Bool.and(D1.same.go(T.VPair{kk, T.VStr{a1}} <> [], T.VPair{kk, T.VStr{a1}} <> []),
            D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz), List.append(&2, T.Val, ff, t))),
          D1.same.go(zz, List.append(&2, T.Val, ff, rtabs(t))),
          M1.hc.p(kk, T.VStr{a1}, List.append(&2, T.Val, D1.canon.keys(t), zz), List.append(&2, T.Val, ff, t)),
          Equal.trans(Bool, Bool.and(D1.same.go(T.VPair{kk, T.VStr{a1}} <> [], T.VPair{kk, T.VStr{a1}} <> []),
            D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz),
            List.append(&2, T.Val, ff, t))), D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz),
              List.append(&2, T.Val, ff, t)),
            D1.same.go(zz, List.append(&2, T.Val, ff, rtabs(t))),
            Equal.cong(Bool, Bool, bt => Bool.and(bt, D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz),
              List.append(&2, T.Val, ff, t))),
              D1.same.go(T.VPair{kk, T.VStr{a1}} <> [], T.VPair{kk, T.VStr{a1}} <> []), True{}, hs1),
            pk(t, hp, zz, ff, M2.wt.more(Bool.and(T.wf.atom(T.VStr{a1}), T.wf.key(kk, t)), _u => T.wf.go(t,
                T.WfRows{hp}),
              hw), Eq.and.right(D1.same.go(T.VPair{kk, T.VStr{a1}} <> [], T.VPair{kk, T.VStr{a1}} <> []), M1.selfs(t),
              hs),
              Eq.and.right(L1.is_miss(T.get(ff, kk)), cv.fr(ff, D1.canon.keys(t)), hf)))))
    case T.VPair{+kk, T.VSpan{+a1, +a2}} <> +t:
      +hs1 = {Eq.and.left(D1.same.go(T.VPair{kk, T.VSpan{a1, a2}} <> [], T.VPair{kk, T.VSpan{a1, a2}} <> []),
        M1.selfs(t), hs) : {D1.same.go(T.VPair{kk, T.VSpan{a1, a2}} <> [], T.VPair{kk, T.VSpan{a1, a2}} <> [])
        == True{} : Bool}}
      Equal.trans(Bool, D1.same.go(T.VPair{kk, T.VSpan{a1, a2}} <> List.append(&2, T.Val, D1.canon.keys(t), zz),
        List.append(&2, T.Val, ff, T.VPair{kk, T.VSpan{a1, a2}} <> t)),
        D1.same.go(T.VPair{kk, T.VSpan{a1, a2}} <> List.append(&2, T.Val, D1.canon.keys(t), zz), T.VPair{kk,
          T.VSpan{a1, a2}} <> List.append(&2, T.Val, ff, t)),
        D1.same.go(zz, List.append(&2, T.Val, ff, rtabs(t))),
        M1.pick.same(kk, T.VSpan{a1, a2}, List.append(&2, T.Val, D1.canon.keys(t), zz), List.append(&2, T.Val, ff,
          T.VPair{kk, T.VSpan{a1, a2}} <> t), T.VPair{kk, T.VSpan{a1, a2}} <> List.append(&2, T.Val, ff, t),
          Equal.trans(D1.Pick, D1.pick(List.append(&2, T.Val, ff, T.VPair{kk, T.VSpan{a1, a2}} <> t), kk),
            D1.Picked{T.VSpan{a1, a2}, List.append(&2, T.Val, ff, t)},
            D1.pick(T.VPair{kk, T.VSpan{a1, a2}} <> List.append(&2, T.Val, ff, t), kk),
            pk.af(ff, kk, T.VSpan{a1, a2}, t, Equal.trans(Bool, T.wf.fresh(T.get(ff, kk)), L1.is_miss(T.get(ff, kk)),
              True{},
              Equal.sym(Bool, L1.is_miss(T.get(ff, kk)), T.wf.fresh(T.get(ff, kk)), miss.fresh(T.get(ff, kk))),
              Eq.and.left(L1.is_miss(T.get(ff, kk)), cv.fr(ff, D1.canon.keys(t)), hf))),
            Equal.sym(D1.Pick, D1.pick(T.VPair{kk, T.VSpan{a1, a2}} <> List.append(&2, T.Val, ff, t), kk),
              D1.Picked{T.VSpan{a1, a2}, List.append(&2, T.Val, ff, t)},
              M1.pick.self(kk, T.VSpan{a1, a2}, List.append(&2, T.Val, ff, t))))),
        Equal.trans(Bool, D1.same.go(T.VPair{kk, T.VSpan{a1, a2}} <> List.append(&2, T.Val, D1.canon.keys(t), zz),
          T.VPair{kk, T.VSpan{a1, a2}} <> List.append(&2, T.Val, ff, t)),
          Bool.and(D1.same.go(T.VPair{kk, T.VSpan{a1, a2}} <> [], T.VPair{kk, T.VSpan{a1, a2}} <> []),
            D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz), List.append(&2, T.Val, ff, t))),
          D1.same.go(zz, List.append(&2, T.Val, ff, rtabs(t))),
          M1.hc.p(kk, T.VSpan{a1, a2}, List.append(&2, T.Val, D1.canon.keys(t), zz), List.append(&2, T.Val, ff, t)),
          Equal.trans(Bool, Bool.and(D1.same.go(T.VPair{kk, T.VSpan{a1, a2}} <> [], T.VPair{kk, T.VSpan{a1,
            a2}} <> []), D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz),
            List.append(&2, T.Val, ff, t))), D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz),
              List.append(&2, T.Val, ff, t)),
            D1.same.go(zz, List.append(&2, T.Val, ff, rtabs(t))),
            Equal.cong(Bool, Bool, bt => Bool.and(bt, D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz),
              List.append(&2, T.Val, ff, t))),
              D1.same.go(T.VPair{kk, T.VSpan{a1, a2}} <> [], T.VPair{kk, T.VSpan{a1, a2}} <> []), True{}, hs1),
            pk(t, hp, zz, ff, M2.wt.more(Bool.and(T.wf.atom(T.VSpan{a1, a2}), T.wf.key(kk, t)), _u => T.wf.go(t,
              T.WfRows{hp}), hw), Eq.and.right(D1.same.go(T.VPair{kk, T.VSpan{a1, a2}} <> [], T.VPair{kk, T.VSpan{a1,
              a2}} <> []), M1.selfs(t), hs),
              Eq.and.right(L1.is_miss(T.get(ff, kk)), cv.fr(ff, D1.canon.keys(t)), hf)))))
    case T.VPair{+kk, T.VInt{+a1, +a2}} <> +t:
      +hs1 = {Eq.and.left(D1.same.go(T.VPair{kk, T.VInt{a1, a2}} <> [], T.VPair{kk, T.VInt{a1, a2}} <> []), M1.selfs(t),
        hs) : {D1.same.go(T.VPair{kk, T.VInt{a1, a2}} <> [], T.VPair{kk, T.VInt{a1, a2}} <> [])
        == True{} : Bool}}
      Equal.trans(Bool, D1.same.go(T.VPair{kk, T.VInt{a1, a2}} <> List.append(&2, T.Val, D1.canon.keys(t), zz),
        List.append(&2, T.Val, ff, T.VPair{kk, T.VInt{a1, a2}} <> t)),
        D1.same.go(T.VPair{kk, T.VInt{a1, a2}} <> List.append(&2, T.Val, D1.canon.keys(t), zz), T.VPair{kk,
          T.VInt{a1, a2}} <> List.append(&2, T.Val, ff, t)),
        D1.same.go(zz, List.append(&2, T.Val, ff, rtabs(t))),
        M1.pick.same(kk, T.VInt{a1, a2}, List.append(&2, T.Val, D1.canon.keys(t), zz), List.append(&2, T.Val, ff,
          T.VPair{kk, T.VInt{a1, a2}} <> t), T.VPair{kk, T.VInt{a1, a2}} <> List.append(&2, T.Val, ff, t),
          Equal.trans(D1.Pick, D1.pick(List.append(&2, T.Val, ff, T.VPair{kk, T.VInt{a1, a2}} <> t), kk),
            D1.Picked{T.VInt{a1, a2}, List.append(&2, T.Val, ff, t)},
            D1.pick(T.VPair{kk, T.VInt{a1, a2}} <> List.append(&2, T.Val, ff, t), kk),
            pk.af(ff, kk, T.VInt{a1, a2}, t, Equal.trans(Bool, T.wf.fresh(T.get(ff, kk)), L1.is_miss(T.get(ff, kk)),
              True{},
              Equal.sym(Bool, L1.is_miss(T.get(ff, kk)), T.wf.fresh(T.get(ff, kk)), miss.fresh(T.get(ff, kk))),
              Eq.and.left(L1.is_miss(T.get(ff, kk)), cv.fr(ff, D1.canon.keys(t)), hf))),
            Equal.sym(D1.Pick, D1.pick(T.VPair{kk, T.VInt{a1, a2}} <> List.append(&2, T.Val, ff, t), kk),
              D1.Picked{T.VInt{a1, a2}, List.append(&2, T.Val, ff, t)},
              M1.pick.self(kk, T.VInt{a1, a2}, List.append(&2, T.Val, ff, t))))),
        Equal.trans(Bool, D1.same.go(T.VPair{kk, T.VInt{a1, a2}} <> List.append(&2, T.Val, D1.canon.keys(t), zz),
          T.VPair{kk, T.VInt{a1, a2}} <> List.append(&2, T.Val, ff, t)),
          Bool.and(D1.same.go(T.VPair{kk, T.VInt{a1, a2}} <> [], T.VPair{kk, T.VInt{a1, a2}} <> []),
            D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz), List.append(&2, T.Val, ff, t))),
          D1.same.go(zz, List.append(&2, T.Val, ff, rtabs(t))),
          M1.hc.p(kk, T.VInt{a1, a2}, List.append(&2, T.Val, D1.canon.keys(t), zz), List.append(&2, T.Val, ff, t)),
          Equal.trans(Bool, Bool.and(D1.same.go(T.VPair{kk, T.VInt{a1, a2}} <> [], T.VPair{kk, T.VInt{a1, a2}} <> []),
            D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz),
            List.append(&2, T.Val, ff, t))), D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz),
              List.append(&2, T.Val, ff, t)),
            D1.same.go(zz, List.append(&2, T.Val, ff, rtabs(t))),
            Equal.cong(Bool, Bool, bt => Bool.and(bt, D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz),
              List.append(&2, T.Val, ff, t))),
              D1.same.go(T.VPair{kk, T.VInt{a1, a2}} <> [], T.VPair{kk, T.VInt{a1, a2}} <> []), True{}, hs1),
            pk(t, hp, zz, ff, M2.wt.more(Bool.and(T.wf.atom(T.VInt{a1, a2}), T.wf.key(kk, t)), _u => T.wf.go(t,
              T.WfRows{hp}), hw), Eq.and.right(D1.same.go(T.VPair{kk, T.VInt{a1, a2}} <> [], T.VPair{kk, T.VInt{a1,
              a2}} <> []), M1.selfs(t), hs),
              Eq.and.right(L1.is_miss(T.get(ff, kk)), cv.fr(ff, D1.canon.keys(t)), hf)))))
    case T.VPair{+kk, T.VFlo{+a1, +a2}} <> +t:
      +hs1 = {Eq.and.left(D1.same.go(T.VPair{kk, T.VFlo{a1, a2}} <> [], T.VPair{kk, T.VFlo{a1, a2}} <> []), M1.selfs(t),
        hs) : {D1.same.go(T.VPair{kk, T.VFlo{a1, a2}} <> [], T.VPair{kk, T.VFlo{a1, a2}} <> [])
        == True{} : Bool}}
      Equal.trans(Bool, D1.same.go(T.VPair{kk, T.VFlo{a1, a2}} <> List.append(&2, T.Val, D1.canon.keys(t), zz),
        List.append(&2, T.Val, ff, T.VPair{kk, T.VFlo{a1, a2}} <> t)),
        D1.same.go(T.VPair{kk, T.VFlo{a1, a2}} <> List.append(&2, T.Val, D1.canon.keys(t), zz), T.VPair{kk,
          T.VFlo{a1, a2}} <> List.append(&2, T.Val, ff, t)),
        D1.same.go(zz, List.append(&2, T.Val, ff, rtabs(t))),
        M1.pick.same(kk, T.VFlo{a1, a2}, List.append(&2, T.Val, D1.canon.keys(t), zz), List.append(&2, T.Val, ff,
          T.VPair{kk, T.VFlo{a1, a2}} <> t), T.VPair{kk, T.VFlo{a1, a2}} <> List.append(&2, T.Val, ff, t),
          Equal.trans(D1.Pick, D1.pick(List.append(&2, T.Val, ff, T.VPair{kk, T.VFlo{a1, a2}} <> t), kk),
            D1.Picked{T.VFlo{a1, a2}, List.append(&2, T.Val, ff, t)},
            D1.pick(T.VPair{kk, T.VFlo{a1, a2}} <> List.append(&2, T.Val, ff, t), kk),
            pk.af(ff, kk, T.VFlo{a1, a2}, t, Equal.trans(Bool, T.wf.fresh(T.get(ff, kk)), L1.is_miss(T.get(ff, kk)),
              True{},
              Equal.sym(Bool, L1.is_miss(T.get(ff, kk)), T.wf.fresh(T.get(ff, kk)), miss.fresh(T.get(ff, kk))),
              Eq.and.left(L1.is_miss(T.get(ff, kk)), cv.fr(ff, D1.canon.keys(t)), hf))),
            Equal.sym(D1.Pick, D1.pick(T.VPair{kk, T.VFlo{a1, a2}} <> List.append(&2, T.Val, ff, t), kk),
              D1.Picked{T.VFlo{a1, a2}, List.append(&2, T.Val, ff, t)},
              M1.pick.self(kk, T.VFlo{a1, a2}, List.append(&2, T.Val, ff, t))))),
        Equal.trans(Bool, D1.same.go(T.VPair{kk, T.VFlo{a1, a2}} <> List.append(&2, T.Val, D1.canon.keys(t), zz),
          T.VPair{kk, T.VFlo{a1, a2}} <> List.append(&2, T.Val, ff, t)),
          Bool.and(D1.same.go(T.VPair{kk, T.VFlo{a1, a2}} <> [], T.VPair{kk, T.VFlo{a1, a2}} <> []),
            D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz), List.append(&2, T.Val, ff, t))),
          D1.same.go(zz, List.append(&2, T.Val, ff, rtabs(t))),
          M1.hc.p(kk, T.VFlo{a1, a2}, List.append(&2, T.Val, D1.canon.keys(t), zz), List.append(&2, T.Val, ff, t)),
          Equal.trans(Bool, Bool.and(D1.same.go(T.VPair{kk, T.VFlo{a1, a2}} <> [], T.VPair{kk, T.VFlo{a1, a2}} <> []),
            D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz),
            List.append(&2, T.Val, ff, t))), D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz),
              List.append(&2, T.Val, ff, t)),
            D1.same.go(zz, List.append(&2, T.Val, ff, rtabs(t))),
            Equal.cong(Bool, Bool, bt => Bool.and(bt, D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz),
              List.append(&2, T.Val, ff, t))),
              D1.same.go(T.VPair{kk, T.VFlo{a1, a2}} <> [], T.VPair{kk, T.VFlo{a1, a2}} <> []), True{}, hs1),
            pk(t, hp, zz, ff, M2.wt.more(Bool.and(T.wf.atom(T.VFlo{a1, a2}), T.wf.key(kk, t)), _u => T.wf.go(t,
              T.WfRows{hp}), hw), Eq.and.right(D1.same.go(T.VPair{kk, T.VFlo{a1, a2}} <> [], T.VPair{kk, T.VFlo{a1,
              a2}} <> []), M1.selfs(t), hs),
              Eq.and.right(L1.is_miss(T.get(ff, kk)), cv.fr(ff, D1.canon.keys(t)), hf)))))
    case T.VPair{+kk, T.VBool{+a1}} <> +t:
      +hs1 = {Eq.and.left(D1.same.go(T.VPair{kk, T.VBool{a1}} <> [], T.VPair{kk, T.VBool{a1}} <> []), M1.selfs(t),
        hs) : {D1.same.go(T.VPair{kk, T.VBool{a1}} <> [], T.VPair{kk, T.VBool{a1}} <> [])
        == True{} : Bool}}
      Equal.trans(Bool, D1.same.go(T.VPair{kk, T.VBool{a1}} <> List.append(&2, T.Val, D1.canon.keys(t), zz),
        List.append(&2, T.Val, ff, T.VPair{kk, T.VBool{a1}} <> t)),
        D1.same.go(T.VPair{kk, T.VBool{a1}} <> List.append(&2, T.Val, D1.canon.keys(t), zz), T.VPair{kk,
          T.VBool{a1}} <> List.append(&2, T.Val, ff, t)),
        D1.same.go(zz, List.append(&2, T.Val, ff, rtabs(t))),
        M1.pick.same(kk, T.VBool{a1}, List.append(&2, T.Val, D1.canon.keys(t), zz), List.append(&2, T.Val, ff,
          T.VPair{kk, T.VBool{a1}} <> t), T.VPair{kk, T.VBool{a1}} <> List.append(&2, T.Val, ff, t),
          Equal.trans(D1.Pick, D1.pick(List.append(&2, T.Val, ff, T.VPair{kk, T.VBool{a1}} <> t), kk),
            D1.Picked{T.VBool{a1}, List.append(&2, T.Val, ff, t)},
            D1.pick(T.VPair{kk, T.VBool{a1}} <> List.append(&2, T.Val, ff, t), kk),
            pk.af(ff, kk, T.VBool{a1}, t, Equal.trans(Bool, T.wf.fresh(T.get(ff, kk)), L1.is_miss(T.get(ff, kk)),
              True{},
              Equal.sym(Bool, L1.is_miss(T.get(ff, kk)), T.wf.fresh(T.get(ff, kk)), miss.fresh(T.get(ff, kk))),
              Eq.and.left(L1.is_miss(T.get(ff, kk)), cv.fr(ff, D1.canon.keys(t)), hf))),
            Equal.sym(D1.Pick, D1.pick(T.VPair{kk, T.VBool{a1}} <> List.append(&2, T.Val, ff, t), kk),
              D1.Picked{T.VBool{a1}, List.append(&2, T.Val, ff, t)},
              M1.pick.self(kk, T.VBool{a1}, List.append(&2, T.Val, ff, t))))),
        Equal.trans(Bool, D1.same.go(T.VPair{kk, T.VBool{a1}} <> List.append(&2, T.Val, D1.canon.keys(t), zz),
          T.VPair{kk, T.VBool{a1}} <> List.append(&2, T.Val, ff, t)),
          Bool.and(D1.same.go(T.VPair{kk, T.VBool{a1}} <> [], T.VPair{kk, T.VBool{a1}} <> []),
            D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz), List.append(&2, T.Val, ff, t))),
          D1.same.go(zz, List.append(&2, T.Val, ff, rtabs(t))),
          M1.hc.p(kk, T.VBool{a1}, List.append(&2, T.Val, D1.canon.keys(t), zz), List.append(&2, T.Val, ff, t)),
          Equal.trans(Bool, Bool.and(D1.same.go(T.VPair{kk, T.VBool{a1}} <> [], T.VPair{kk, T.VBool{a1}} <> []),
            D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz),
            List.append(&2, T.Val, ff, t))), D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz),
              List.append(&2, T.Val, ff, t)),
            D1.same.go(zz, List.append(&2, T.Val, ff, rtabs(t))),
            Equal.cong(Bool, Bool, bt => Bool.and(bt, D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz),
              List.append(&2, T.Val, ff, t))),
              D1.same.go(T.VPair{kk, T.VBool{a1}} <> [], T.VPair{kk, T.VBool{a1}} <> []), True{}, hs1),
            pk(t, hp, zz, ff, M2.wt.more(Bool.and(T.wf.atom(T.VBool{a1}), T.wf.key(kk, t)), _u => T.wf.go(t,
                T.WfRows{hp}),
              hw), Eq.and.right(D1.same.go(T.VPair{kk, T.VBool{a1}} <> [], T.VPair{kk, T.VBool{a1}} <> []), M1.selfs(t),
              hs),
              Eq.and.right(L1.is_miss(T.get(ff, kk)), cv.fr(ff, D1.canon.keys(t)), hf)))))
    case T.VPair{+kk, T.VWhen{+a1}} <> +t:
      +hs1 = {Eq.and.left(D1.same.go(T.VPair{kk, T.VWhen{a1}} <> [], T.VPair{kk, T.VWhen{a1}} <> []), M1.selfs(t),
        hs) : {D1.same.go(T.VPair{kk, T.VWhen{a1}} <> [], T.VPair{kk, T.VWhen{a1}} <> [])
        == True{} : Bool}}
      Equal.trans(Bool, D1.same.go(T.VPair{kk, T.VWhen{a1}} <> List.append(&2, T.Val, D1.canon.keys(t), zz),
        List.append(&2, T.Val, ff, T.VPair{kk, T.VWhen{a1}} <> t)),
        D1.same.go(T.VPair{kk, T.VWhen{a1}} <> List.append(&2, T.Val, D1.canon.keys(t), zz), T.VPair{kk,
          T.VWhen{a1}} <> List.append(&2, T.Val, ff, t)),
        D1.same.go(zz, List.append(&2, T.Val, ff, rtabs(t))),
        M1.pick.same(kk, T.VWhen{a1}, List.append(&2, T.Val, D1.canon.keys(t), zz), List.append(&2, T.Val, ff,
          T.VPair{kk, T.VWhen{a1}} <> t), T.VPair{kk, T.VWhen{a1}} <> List.append(&2, T.Val, ff, t),
          Equal.trans(D1.Pick, D1.pick(List.append(&2, T.Val, ff, T.VPair{kk, T.VWhen{a1}} <> t), kk),
            D1.Picked{T.VWhen{a1}, List.append(&2, T.Val, ff, t)},
            D1.pick(T.VPair{kk, T.VWhen{a1}} <> List.append(&2, T.Val, ff, t), kk),
            pk.af(ff, kk, T.VWhen{a1}, t, Equal.trans(Bool, T.wf.fresh(T.get(ff, kk)), L1.is_miss(T.get(ff, kk)),
              True{},
              Equal.sym(Bool, L1.is_miss(T.get(ff, kk)), T.wf.fresh(T.get(ff, kk)), miss.fresh(T.get(ff, kk))),
              Eq.and.left(L1.is_miss(T.get(ff, kk)), cv.fr(ff, D1.canon.keys(t)), hf))),
            Equal.sym(D1.Pick, D1.pick(T.VPair{kk, T.VWhen{a1}} <> List.append(&2, T.Val, ff, t), kk),
              D1.Picked{T.VWhen{a1}, List.append(&2, T.Val, ff, t)},
              M1.pick.self(kk, T.VWhen{a1}, List.append(&2, T.Val, ff, t))))),
        Equal.trans(Bool, D1.same.go(T.VPair{kk, T.VWhen{a1}} <> List.append(&2, T.Val, D1.canon.keys(t), zz),
          T.VPair{kk, T.VWhen{a1}} <> List.append(&2, T.Val, ff, t)),
          Bool.and(D1.same.go(T.VPair{kk, T.VWhen{a1}} <> [], T.VPair{kk, T.VWhen{a1}} <> []),
            D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz), List.append(&2, T.Val, ff, t))),
          D1.same.go(zz, List.append(&2, T.Val, ff, rtabs(t))),
          M1.hc.p(kk, T.VWhen{a1}, List.append(&2, T.Val, D1.canon.keys(t), zz), List.append(&2, T.Val, ff, t)),
          Equal.trans(Bool, Bool.and(D1.same.go(T.VPair{kk, T.VWhen{a1}} <> [], T.VPair{kk, T.VWhen{a1}} <> []),
            D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz),
            List.append(&2, T.Val, ff, t))), D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz),
              List.append(&2, T.Val, ff, t)),
            D1.same.go(zz, List.append(&2, T.Val, ff, rtabs(t))),
            Equal.cong(Bool, Bool, bt => Bool.and(bt, D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz),
              List.append(&2, T.Val, ff, t))),
              D1.same.go(T.VPair{kk, T.VWhen{a1}} <> [], T.VPair{kk, T.VWhen{a1}} <> []), True{}, hs1),
            pk(t, hp, zz, ff, M2.wt.more(Bool.and(T.wf.atom(T.VWhen{a1}), T.wf.key(kk, t)), _u => T.wf.go(t,
                T.WfRows{hp}),
              hw), Eq.and.right(D1.same.go(T.VPair{kk, T.VWhen{a1}} <> [], T.VPair{kk, T.VWhen{a1}} <> []), M1.selfs(t),
              hs),
              Eq.and.right(L1.is_miss(T.get(ff, kk)), cv.fr(ff, D1.canon.keys(t)), hf)))))
    case T.VPair{+kk, T.VArr{+a1}} <> +t:
      +hs1 = {Eq.and.left(D1.same.go(T.VPair{kk, T.VArr{a1}} <> [], T.VPair{kk, T.VArr{a1}} <> []), M1.selfs(t),
        hs) : {D1.same.go(T.VPair{kk, T.VArr{a1}} <> [], T.VPair{kk, T.VArr{a1}} <> [])
        == True{} : Bool}}
      Equal.trans(Bool, D1.same.go(T.VPair{kk, T.VArr{a1}} <> List.append(&2, T.Val, D1.canon.keys(t), zz),
        List.append(&2, T.Val, ff, T.VPair{kk, T.VArr{a1}} <> t)),
        D1.same.go(T.VPair{kk, T.VArr{a1}} <> List.append(&2, T.Val, D1.canon.keys(t), zz), T.VPair{kk,
          T.VArr{a1}} <> List.append(&2, T.Val, ff, t)),
        D1.same.go(zz, List.append(&2, T.Val, ff, rtabs(t))),
        M1.pick.same(kk, T.VArr{a1}, List.append(&2, T.Val, D1.canon.keys(t), zz), List.append(&2, T.Val, ff,
            T.VPair{kk,
          T.VArr{a1}} <> t), T.VPair{kk, T.VArr{a1}} <> List.append(&2, T.Val, ff, t),
          Equal.trans(D1.Pick, D1.pick(List.append(&2, T.Val, ff, T.VPair{kk, T.VArr{a1}} <> t), kk),
            D1.Picked{T.VArr{a1}, List.append(&2, T.Val, ff, t)},
            D1.pick(T.VPair{kk, T.VArr{a1}} <> List.append(&2, T.Val, ff, t), kk),
            pk.af(ff, kk, T.VArr{a1}, t, Equal.trans(Bool, T.wf.fresh(T.get(ff, kk)), L1.is_miss(T.get(ff, kk)),
              True{},
              Equal.sym(Bool, L1.is_miss(T.get(ff, kk)), T.wf.fresh(T.get(ff, kk)), miss.fresh(T.get(ff, kk))),
              Eq.and.left(L1.is_miss(T.get(ff, kk)), cv.fr(ff, D1.canon.keys(t)), hf))),
            Equal.sym(D1.Pick, D1.pick(T.VPair{kk, T.VArr{a1}} <> List.append(&2, T.Val, ff, t), kk),
              D1.Picked{T.VArr{a1}, List.append(&2, T.Val, ff, t)},
              M1.pick.self(kk, T.VArr{a1}, List.append(&2, T.Val, ff, t))))),
        Equal.trans(Bool, D1.same.go(T.VPair{kk, T.VArr{a1}} <> List.append(&2, T.Val, D1.canon.keys(t), zz),
          T.VPair{kk, T.VArr{a1}} <> List.append(&2, T.Val, ff, t)),
          Bool.and(D1.same.go(T.VPair{kk, T.VArr{a1}} <> [], T.VPair{kk, T.VArr{a1}} <> []),
            D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz), List.append(&2, T.Val, ff, t))),
          D1.same.go(zz, List.append(&2, T.Val, ff, rtabs(t))),
          M1.hc.p(kk, T.VArr{a1}, List.append(&2, T.Val, D1.canon.keys(t), zz), List.append(&2, T.Val, ff, t)),
          Equal.trans(Bool, Bool.and(D1.same.go(T.VPair{kk, T.VArr{a1}} <> [], T.VPair{kk, T.VArr{a1}} <> []),
            D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz),
            List.append(&2, T.Val, ff, t))), D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz),
              List.append(&2, T.Val, ff, t)),
            D1.same.go(zz, List.append(&2, T.Val, ff, rtabs(t))),
            Equal.cong(Bool, Bool, bt => Bool.and(bt, D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz),
              List.append(&2, T.Val, ff, t))),
              D1.same.go(T.VPair{kk, T.VArr{a1}} <> [], T.VPair{kk, T.VArr{a1}} <> []), True{}, hs1),
            pk(t, hp, zz, ff, M2.wt.more(T.wf.go(a1, T.WfItems{}), _v => T.wf.go(t, T.WfRows{hp}),
                M2.wt.more(T.wf.key(kk, t),
              _u => T.wf.then(T.wf.go(a1, T.WfItems{}), _v => T.wf.go(t, T.WfRows{hp})), hw)),
              Eq.and.right(D1.same.go(T.VPair{kk, T.VArr{a1}} <> [], T.VPair{kk, T.VArr{a1}} <> []), M1.selfs(t), hs),
              Eq.and.right(L1.is_miss(T.get(ff, kk)), cv.fr(ff, D1.canon.keys(t)), hf)))))
    case T.VPair{+kk, T.VInl{+a1}} <> +t:
      +hs1 = {Eq.and.left(D1.same.go(T.VPair{kk, T.VInl{a1}} <> [], T.VPair{kk, T.VInl{a1}} <> []), M1.selfs(t),
        hs) : {D1.same.go(T.VPair{kk, T.VInl{a1}} <> [], T.VPair{kk, T.VInl{a1}} <> [])
        == True{} : Bool}}
      Equal.trans(Bool, D1.same.go(T.VPair{kk, T.VInl{a1}} <> List.append(&2, T.Val, D1.canon.keys(t), zz),
        List.append(&2, T.Val, ff, T.VPair{kk, T.VInl{a1}} <> t)),
        D1.same.go(T.VPair{kk, T.VInl{a1}} <> List.append(&2, T.Val, D1.canon.keys(t), zz), T.VPair{kk,
          T.VInl{a1}} <> List.append(&2, T.Val, ff, t)),
        D1.same.go(zz, List.append(&2, T.Val, ff, rtabs(t))),
        M1.pick.same(kk, T.VInl{a1}, List.append(&2, T.Val, D1.canon.keys(t), zz), List.append(&2, T.Val, ff,
            T.VPair{kk,
          T.VInl{a1}} <> t), T.VPair{kk, T.VInl{a1}} <> List.append(&2, T.Val, ff, t),
          Equal.trans(D1.Pick, D1.pick(List.append(&2, T.Val, ff, T.VPair{kk, T.VInl{a1}} <> t), kk),
            D1.Picked{T.VInl{a1}, List.append(&2, T.Val, ff, t)},
            D1.pick(T.VPair{kk, T.VInl{a1}} <> List.append(&2, T.Val, ff, t), kk),
            pk.af(ff, kk, T.VInl{a1}, t, Equal.trans(Bool, T.wf.fresh(T.get(ff, kk)), L1.is_miss(T.get(ff, kk)),
              True{},
              Equal.sym(Bool, L1.is_miss(T.get(ff, kk)), T.wf.fresh(T.get(ff, kk)), miss.fresh(T.get(ff, kk))),
              Eq.and.left(L1.is_miss(T.get(ff, kk)), cv.fr(ff, D1.canon.keys(t)), hf))),
            Equal.sym(D1.Pick, D1.pick(T.VPair{kk, T.VInl{a1}} <> List.append(&2, T.Val, ff, t), kk),
              D1.Picked{T.VInl{a1}, List.append(&2, T.Val, ff, t)},
              M1.pick.self(kk, T.VInl{a1}, List.append(&2, T.Val, ff, t))))),
        Equal.trans(Bool, D1.same.go(T.VPair{kk, T.VInl{a1}} <> List.append(&2, T.Val, D1.canon.keys(t), zz),
          T.VPair{kk, T.VInl{a1}} <> List.append(&2, T.Val, ff, t)),
          Bool.and(D1.same.go(T.VPair{kk, T.VInl{a1}} <> [], T.VPair{kk, T.VInl{a1}} <> []),
            D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz), List.append(&2, T.Val, ff, t))),
          D1.same.go(zz, List.append(&2, T.Val, ff, rtabs(t))),
          M1.hc.p(kk, T.VInl{a1}, List.append(&2, T.Val, D1.canon.keys(t), zz), List.append(&2, T.Val, ff, t)),
          Equal.trans(Bool, Bool.and(D1.same.go(T.VPair{kk, T.VInl{a1}} <> [], T.VPair{kk, T.VInl{a1}} <> []),
            D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz),
            List.append(&2, T.Val, ff, t))), D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz),
              List.append(&2, T.Val, ff, t)),
            D1.same.go(zz, List.append(&2, T.Val, ff, rtabs(t))),
            Equal.cong(Bool, Bool, bt => Bool.and(bt, D1.same.go(List.append(&2, T.Val, D1.canon.keys(t), zz),
              List.append(&2, T.Val, ff, t))),
              D1.same.go(T.VPair{kk, T.VInl{a1}} <> [], T.VPair{kk, T.VInl{a1}} <> []), True{}, hs1),
            pk(t, hp, zz, ff, M2.wt.more(T.wf.go(a1, T.WfInl{}), _v => T.wf.go(t, T.WfRows{hp}),
                M2.wt.more(T.wf.key(kk, t),
              _u => T.wf.then(T.wf.go(a1, T.WfInl{}), _v => T.wf.go(t, T.WfRows{hp})), hw)),
              Eq.and.right(D1.same.go(T.VPair{kk, T.VInl{a1}} <> [], T.VPair{kk, T.VInl{a1}} <> []), M1.selfs(t), hs),
              Eq.and.right(L1.is_miss(T.get(ff, kk)), cv.fr(ff, D1.canon.keys(t)), hf)))))
    case T.VPair{+kk, T.VAot{+a1, +a2}} <> +t:
      Eq.bit.absurd(&2, {D1.same.go(List.append(&2, T.Val, D1.canon.keys(T.VPair{kk, T.VAot{a1, a2}} <> t), zz),
        List.append(&2, T.Val, ff, T.VPair{kk, T.VAot{a1, a2}} <> t)) == D1.same.go(zz, List.append(&2, T.Val, ff,
        rtabs(T.VPair{kk, T.VAot{a1, a2}} <> t))) : Bool}, hw)
    case T.VPair{+kk, T.VPair{+a1, +a2}} <> +t:
      Eq.bit.absurd(&2, {D1.same.go(List.append(&2, T.Val, D1.canon.keys(T.VPair{kk, T.VPair{a1, a2}} <> t), zz),
        List.append(&2, T.Val, ff, T.VPair{kk, T.VPair{a1, a2}} <> t)) == D1.same.go(zz, List.append(&2, T.Val, ff,
        rtabs(T.VPair{kk, T.VPair{a1, a2}} <> t))) : Bool}, hw)
    case T.VStr{+a1} <> +t:
      Eq.bit.absurd(&2, {D1.same.go(List.append(&2, T.Val, D1.canon.keys(T.VStr{a1} <> t), zz), List.append(&2,
        T.Val, ff, T.VStr{a1} <> t)) == D1.same.go(zz, List.append(&2, T.Val, ff, rtabs(T.VStr{a1} <> t))) : Bool},
        hw)
    case T.VSpan{+a1, +a2} <> +t:
      Eq.bit.absurd(&2, {D1.same.go(List.append(&2, T.Val, D1.canon.keys(T.VSpan{a1, a2} <> t), zz), List.append(&2,
        T.Val, ff, T.VSpan{a1, a2} <> t)) == D1.same.go(zz, List.append(&2, T.Val, ff, rtabs(T.VSpan{a1,
        a2} <> t))) : Bool}, hw)
    case T.VInt{+a1, +a2} <> +t:
      Eq.bit.absurd(&2, {D1.same.go(List.append(&2, T.Val, D1.canon.keys(T.VInt{a1, a2} <> t), zz), List.append(&2,
        T.Val, ff, T.VInt{a1, a2} <> t)) == D1.same.go(zz, List.append(&2, T.Val, ff, rtabs(T.VInt{a1,
        a2} <> t))) : Bool}, hw)
    case T.VFlo{+a1, +a2} <> +t:
      Eq.bit.absurd(&2, {D1.same.go(List.append(&2, T.Val, D1.canon.keys(T.VFlo{a1, a2} <> t), zz), List.append(&2,
        T.Val, ff, T.VFlo{a1, a2} <> t)) == D1.same.go(zz, List.append(&2, T.Val, ff, rtabs(T.VFlo{a1,
        a2} <> t))) : Bool}, hw)
    case T.VBool{+a1} <> +t:
      Eq.bit.absurd(&2, {D1.same.go(List.append(&2, T.Val, D1.canon.keys(T.VBool{a1} <> t), zz), List.append(&2,
        T.Val, ff, T.VBool{a1} <> t)) == D1.same.go(zz, List.append(&2, T.Val, ff, rtabs(T.VBool{a1} <> t))) : Bool},
        hw)
    case T.VWhen{+a1} <> +t:
      Eq.bit.absurd(&2, {D1.same.go(List.append(&2, T.Val, D1.canon.keys(T.VWhen{a1} <> t), zz), List.append(&2,
        T.Val, ff, T.VWhen{a1} <> t)) == D1.same.go(zz, List.append(&2, T.Val, ff, rtabs(T.VWhen{a1} <> t))) : Bool},
        hw)
    case T.VArr{+a1} <> +t:
      Eq.bit.absurd(&2, {D1.same.go(List.append(&2, T.Val, D1.canon.keys(T.VArr{a1} <> t), zz), List.append(&2,
        T.Val, ff, T.VArr{a1} <> t)) == D1.same.go(zz, List.append(&2, T.Val, ff, rtabs(T.VArr{a1} <> t))) : Bool},
        hw)
    case T.VInl{+a1} <> +t:
      Eq.bit.absurd(&2, {D1.same.go(List.append(&2, T.Val, D1.canon.keys(T.VInl{a1} <> t), zz), List.append(&2,
        T.Val, ff, T.VInl{a1} <> t)) == D1.same.go(zz, List.append(&2, T.Val, ff, rtabs(T.VInl{a1} <> t))) : Bool},
        hw)
    case T.VHead{+a1, +a2} <> +t:
      Eq.bit.absurd(&2, {D1.same.go(List.append(&2, T.Val, D1.canon.keys(T.VHead{a1, a2} <> t), zz), List.append(&2,
        T.Val, ff, T.VHead{a1, a2} <> t)) == D1.same.go(zz, List.append(&2, T.Val, ff, rtabs(T.VHead{a1,
        a2} <> t))) : Bool}, hw)
    case T.VAot{+a1, +a2} <> +t:
      Eq.bit.absurd(&2, {D1.same.go(List.append(&2, T.Val, D1.canon.keys(T.VAot{a1, a2} <> t), zz), List.append(&2,
        T.Val, ff, T.VAot{a1, a2} <> t)) == D1.same.go(zz, List.append(&2, T.Val, ff, rtabs(T.VAot{a1,
        a2} <> t))) : Bool}, hw)
    case T.VAots{+a1, +a2} <> +t:
      Eq.bit.absurd(&2, {D1.same.go(List.append(&2, T.Val, D1.canon.keys(T.VAots{a1, a2} <> t), zz), List.append(&2,
        T.Val, ff, T.VAots{a1, a2} <> t)) == D1.same.go(zz, List.append(&2, T.Val, ff, rtabs(T.VAots{a1,
        a2} <> t))) : Bool}, hw)
