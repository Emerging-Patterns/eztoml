# a digit's value written as a digit reads back, with leading zeros dropped
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/defs/AbnfGrammar.bend as D1
import ../../laws/defs/DocumentSameness.bend as D2
import ./ControlEscapeText.bend as M1
import ./FreshNamesInRows.bend as M2
import ./PrefixAndTake.bend as M3

# Integers. render writes the sign (a minus only) and the digits. The scan
# reads a first digit that is not 0 into a one-digit numeral, and each later
# digit multiplies the numeral by ten and adds it, least-significant digit
# first; dec.text writes the numeral back as the digits. A lone 0 and -0
# are fixed texts.

# the digit values of characters, in the same order
def vals(cs: List<&2, Char>) -> List<&2, U32>:
  match cs:
    case []:
      []
    case cc <> tt:
      T.dig.val(cc) <> vals(tt)

# a numeral's digits, least-significant first: all digits, and the last one,
# the most significant, is not 0
def nzl(xs: List<&2, Char>) -> Bool:
  match xs:
    case []:
      False{}
    case +xx <> +tt:
      Bool.and(Char.is_digit(xx), Bool.or(nzl(tt), Bool.and(List.is_empty(&2, Char, tt),
        Bool.not(Char.is_eq(xx, '0')))))

# the scan inside the digits of an integer
def ndig(+sg: T.Sign, ds: List<&2, U32>) -> T.Num:
  T.Num{T.NDig{}, sg, 10, ds, False{}, True{}, ""}

# an `or` whose right half answered False answered its left half
def or.fl(aa: Bool, ee: {Bool.or(aa, False{}) == True{} : Bool}) -> {aa == True{} : Bool}:
  match aa:
    case True{}:
      {==}
    case False{}:
      ee

# ten times a digit plus a digit, over ten and modulo ten, is the two digits:
# one decimal step of the numeral, for each of the hundred pairs
def dgo.step(
  xx: Char,
  +cc: Char,
  +rest: List<&2, U32>,
  hx: {Char.is_digit(xx) == True{} : Bool},
  +hc: {Char.is_digit(cc) == True{} : Bool}
) -> {T.dec.go(T.dig.val(xx) <> rest, 10, T.dig.val(cc)) == T.dig.val(cc) <> T.dec.go(rest, 10, T.dig.val(xx)) :
  List<&2, U32>}:
  M2.dg.elim(zz => {T.dec.go(T.dig.val(zz) <> rest, 10, T.dig.val(cc))
    == T.dig.val(cc) <> T.dec.go(rest, 10, T.dig.val(zz)) : List<&2, U32>}, xx, hx,
    M2.dg.elim(yy => {T.dec.go(T.dig.val('0') <> rest, 10, T.dig.val(yy))
      == T.dig.val(yy) <> T.dec.go(rest, 10, T.dig.val('0')) : List<&2, U32>}, cc, hc,
      {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}),
    M2.dg.elim(yy => {T.dec.go(T.dig.val('1') <> rest, 10, T.dig.val(yy))
      == T.dig.val(yy) <> T.dec.go(rest, 10, T.dig.val('1')) : List<&2, U32>}, cc, hc,
      {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}),
    M2.dg.elim(yy => {T.dec.go(T.dig.val('2') <> rest, 10, T.dig.val(yy))
      == T.dig.val(yy) <> T.dec.go(rest, 10, T.dig.val('2')) : List<&2, U32>}, cc, hc,
      {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}),
    M2.dg.elim(yy => {T.dec.go(T.dig.val('3') <> rest, 10, T.dig.val(yy))
      == T.dig.val(yy) <> T.dec.go(rest, 10, T.dig.val('3')) : List<&2, U32>}, cc, hc,
      {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}),
    M2.dg.elim(yy => {T.dec.go(T.dig.val('4') <> rest, 10, T.dig.val(yy))
      == T.dig.val(yy) <> T.dec.go(rest, 10, T.dig.val('4')) : List<&2, U32>}, cc, hc,
      {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}),
    M2.dg.elim(yy => {T.dec.go(T.dig.val('5') <> rest, 10, T.dig.val(yy))
      == T.dig.val(yy) <> T.dec.go(rest, 10, T.dig.val('5')) : List<&2, U32>}, cc, hc,
      {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}),
    M2.dg.elim(yy => {T.dec.go(T.dig.val('6') <> rest, 10, T.dig.val(yy))
      == T.dig.val(yy) <> T.dec.go(rest, 10, T.dig.val('6')) : List<&2, U32>}, cc, hc,
      {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}),
    M2.dg.elim(yy => {T.dec.go(T.dig.val('7') <> rest, 10, T.dig.val(yy))
      == T.dig.val(yy) <> T.dec.go(rest, 10, T.dig.val('7')) : List<&2, U32>}, cc, hc,
      {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}),
    M2.dg.elim(yy => {T.dec.go(T.dig.val('8') <> rest, 10, T.dig.val(yy))
      == T.dig.val(yy) <> T.dec.go(rest, 10, T.dig.val('8')) : List<&2, U32>}, cc, hc,
      {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}),
    M2.dg.elim(yy => {T.dec.go(T.dig.val('9') <> rest, 10, T.dig.val(yy))
      == T.dig.val(yy) <> T.dec.go(rest, 10, T.dig.val('9')) : List<&2, U32>}, cc, hc,
      {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}))

# the carry left once the numeral runs out is its last digit, when that is
# not 0
def dgo.last(
  xx: Char,
  hx: {Char.is_digit(xx) == True{} : Bool},
  hz: {Char.is_eq(xx, '0') == False{} : Bool}
) -> {T.dec.go([], 10, T.dig.val(xx)) == [T.dig.val(xx)] : List<&2, U32>}:
  M2.dg.elim(zz => {Char.is_eq(zz, '0') == False{} : Bool} -> {T.dec.go([], 10, T.dig.val(zz)) == [T.dig.val(zz)]
    : List<&2, U32>}, xx, hx,
    ee => Eq.bit.absurd2(&2, {T.dec.go([], 10, T.dig.val('0')) == [T.dig.val('0')] : List<&2, U32>}, ee),
    _e => {==}, _e => {==}, _e => {==}, _e => {==}, _e => {==}, _e => {==}, _e => {==}, _e => {==},
    _e => {==})(hz)

# a numeral's digits whose last is not 0: the carry reaches the end as that
# digit, so one more digit only goes in front
def dgo.rest(
  +xx: Char,
  tt: List<&2, Char>,
  +hx: {Char.is_digit(xx) == True{} : Bool},
  +hn: {Bool.or(nzl(tt), Bool.and(List.is_empty(&2, Char, tt), Bool.not(Char.is_eq(xx, '0')))) == True{} : Bool},
  ih: {nzl(tt) == True{} : Bool} -> {T.dec.go(vals(tt), 10, T.dig.val(xx)) == vals(xx <> tt) : List<&2, U32>}
) -> {T.dec.go(vals(tt), 10, T.dig.val(xx)) == vals(xx <> tt) : List<&2, U32>}:
  match tt:
    case []:
      dgo.last(xx, hx, Eq.not.true(Char.is_eq(xx, '0'), hn))
    case yy <> ys:
      ih(or.fl(nzl(yy <> ys), hn))

# one more digit in front of a numeral's digits is the numeral times ten plus
# the digit
def dgo(
  acc: List<&2, Char>,
  +cc: Char,
  +hc: {Char.is_digit(cc) == True{} : Bool},
  +hn: {nzl(acc) == True{} : Bool}
) -> {T.dec.go(vals(acc), 10, T.dig.val(cc)) == vals(cc <> acc) : List<&2, U32>}:
  match acc:
    case []:
      Eq.bit.absurd(&2, {T.dec.go([], 10, T.dig.val(cc)) == [T.dig.val(cc)] : List<&2, U32>}, hn)
    case +xx <> +tt:
      +hx = {Eq.and.left(Char.is_digit(xx), Bool.or(nzl(tt), Bool.and(List.is_empty(&2, Char, tt),
        Bool.not(Char.is_eq(xx, '0')))), hn) : {Char.is_digit(xx) == True{} : Bool}}
      Equal.trans(List<&2, U32>, T.dec.go(T.dig.val(xx) <> vals(tt), 10, T.dig.val(cc)),
        T.dig.val(cc) <> T.dec.go(vals(tt), 10, T.dig.val(xx)), T.dig.val(cc) <> vals(xx <> tt),
        dgo.step(xx, cc, vals(tt), hx, hc),
        Equal.cong(List<&2, U32>, List<&2, U32>, ys => T.dig.val(cc) <> ys, T.dec.go(vals(tt), 10, T.dig.val(xx)),
          vals(xx <> tt), dgo.rest(xx, tt, hx, Eq.and.right(Char.is_digit(xx), Bool.or(nzl(tt),
          Bool.and(List.is_empty(&2, Char, tt), Bool.not(Char.is_eq(xx, '0')))), hn),
          ht => dgo(tt, xx, hx, ht))))

# a later digit in the digits of an integer joins the numeral
def nw.step(
  +sg: T.Sign,
  +ds: List<&2, U32>,
  cc: Char,
  hc: {Char.is_digit(cc) == True{} : Bool}
) -> {T.num.step(ndig(sg, ds), cc) == ndig(sg, T.dec.go(ds, 10, T.dig.val(cc))) : T.Num}:
  M2.dg.elim(zz => {T.num.step(ndig(sg, ds), zz) == ndig(sg, T.dec.go(ds, 10, T.dig.val(zz))) : T.Num}, cc, hc,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# the first digit, not 0, after no sign
def nw.lead(
  +sg: T.Sign,
  cc: Char,
  hc: {Char.is_digit(cc) == True{} : Bool},
  hz: {Char.is_eq(cc, '0') == False{} : Bool}
) -> {T.num.step(T.Num{T.NLead{}, sg, 10, [], False{}, False{}, ""}, cc) == ndig(sg, vals([cc])) : T.Num}:
  M2.dg.elim(zz => {Char.is_eq(zz, '0') == False{} : Bool} -> {T.num.step(T.Num{T.NLead{}, sg, 10, [], False{},
    False{}, ""}, zz) == ndig(sg, vals([zz])) : T.Num}, cc, hc,
    ee => Eq.bit.absurd2(&2, {T.num.step(T.Num{T.NLead{}, sg, 10, [], False{}, False{}, ""}, '0')
      == ndig(sg, vals(['0'])) : T.Num}, ee),
    _e => {==}, _e => {==}, _e => {==}, _e => {==}, _e => {==}, _e => {==}, _e => {==}, _e => {==},
    _e => {==})(hz)

# and after a sign
def nw.sign(
  +sg: T.Sign,
  cc: Char,
  hc: {Char.is_digit(cc) == True{} : Bool},
  hz: {Char.is_eq(cc, '0') == False{} : Bool}
) -> {T.num.step(T.Num{T.NSign{}, sg, 10, [], False{}, False{}, ""}, cc) == ndig(sg, vals([cc])) : T.Num}:
  M2.dg.elim(zz => {Char.is_eq(zz, '0') == False{} : Bool} -> {T.num.step(T.Num{T.NSign{}, sg, 10, [], False{},
    False{}, ""}, zz) == ndig(sg, vals([zz])) : T.Num}, cc, hc,
    ee => Eq.bit.absurd2(&2, {T.num.step(T.Num{T.NSign{}, sg, 10, [], False{}, False{}, ""}, '0')
      == ndig(sg, vals(['0'])) : T.Num}, ee),
    _e => {==}, _e => {==}, _e => {==}, _e => {==}, _e => {==}, _e => {==}, _e => {==}, _e => {==},
    _e => {==})(hz)

# reversing digit values is reversing the digits
def vals.rev(
  xs: List<&2, Char>,
  ys: List<&2, Char>
) -> {List.reverse.go(&2, U32, vals(xs), vals(ys)) == vals(List.reverse.go(&2, Char, xs, ys)) : List<&2, U32>}:
  match xs:
    case []:
      {==}
    case xx <> xt:
      vals.rev(xt, xx <> ys)

# a digit's value written as a digit is the digit
def dg.back(
  cc: Char,
  hc: {Char.is_digit(cc) == True{} : Bool}
) -> {T.dec.ch(T.dig.val(cc)) == cc : Char}:
  M2.dg.elim(zz => {T.dec.ch(T.dig.val(zz)) == zz : Char}, cc, hc,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# digits' values written as digits are the digits
def dg.backs(
  tt: String,
  +ht: {T.wf.digits(tt) == True{} : Bool}
) -> {T.dec.chars(vals(String.to_list(tt))) == String.to_list(tt) : List<&2, Char>}:
  match tt:
    case SNil{}:
      {==}
    case SCon{+cc, +ts}:
      Equal.trans(List<&2, Char>, T.dec.ch(T.dig.val(cc)) <> T.dec.chars(vals(String.to_list(ts))),
        cc <> T.dec.chars(vals(String.to_list(ts))), cc <> String.to_list(ts),
        Equal.cong(Char, List<&2, Char>, zz => zz <> T.dec.chars(vals(String.to_list(ts))),
          T.dec.ch(T.dig.val(cc)), cc, dg.back(cc, M2.then.l(Char.is_digit(cc), ts, ht))),
        Equal.cong(List<&2, Char>, List<&2, Char>, zs => cc <> zs, T.dec.chars(vals(String.to_list(ts))),
          String.to_list(ts), dg.backs(ts, M2.then.r(Char.is_digit(cc), ts, ht))))

# once no zero is being skipped, the digits are kept in order
def dd.kept(
  cs: List<&2, Char>,
  out: List<&2, Char>
) -> {T.dec.drop(cs, False{}, out) == String.from_list(List.reverse.go(&2, Char, out, cs)) : String}:
  match cs:
    case []:
      M1.fold.nil(out)
    case hh <> tt:
      dd.kept(tt, hh <> out)

# dec.text of the numeral read from digits whose first is not 0 is the digits
def dtext(
  +hh: Char,
  +tt: String,
  +hx: {Char.is_digit(hh) == True{} : Bool},
  +hz: {Char.is_eq(hh, '0') == False{} : Bool},
  +ht: {T.wf.digits(tt) == True{} : Bool}
) -> {T.dec.text(vals(M2.rev.onto(tt, [hh]))) == SCon{hh, tt} : String}:
  +ro = {M2.wd.order(hh, tt) : {List.reverse(&2, Char, M2.rev.onto(tt, [hh])) == hh <> String.to_list(tt)
    : List<&2, Char>}}
  +hd = {Equal.trans(Bool, T.wf.then(Char.is_digit(hh), _u => T.wf.digits(tt)),
    T.wf.then(True{}, _u => T.wf.digits(tt)), True{},
    Equal.cong(Bool, Bool, bb => T.wf.then(bb, _u => T.wf.digits(tt)), Char.is_digit(hh), True{}, hx), ht)
    : {T.wf.digits(SCon{hh, tt}) == True{} : Bool}}
  Equal.trans(String, T.dec.drop(T.dec.chars(List.reverse.go(&2, U32, vals(M2.rev.onto(tt, [hh])), [])), True{}, []),
    T.dec.drop(T.dec.chars(vals(hh <> String.to_list(tt))), True{}, []), SCon{hh, tt},
    Equal.cong(List<&2, U32>, String, ds => T.dec.drop(T.dec.chars(ds), True{}, []),
      List.reverse.go(&2, U32, vals(M2.rev.onto(tt, [hh])), []), vals(hh <> String.to_list(tt)),
      Equal.trans(List<&2, U32>, List.reverse.go(&2, U32, vals(M2.rev.onto(tt, [hh])), []),
        vals(List.reverse(&2, Char, M2.rev.onto(tt, [hh]))), vals(hh <> String.to_list(tt)),
        vals.rev(M2.rev.onto(tt, [hh]), []),
        Equal.cong(List<&2, Char>, List<&2, U32>, xs => vals(xs), List.reverse(&2, Char, M2.rev.onto(tt, [hh])),
          hh <> String.to_list(tt), ro))),
    Equal.trans(String, T.dec.drop(T.dec.chars(vals(hh <> String.to_list(tt))), True{}, []),
      T.dec.drop(hh <> String.to_list(tt), True{}, []), SCon{hh, tt},
      Equal.cong(List<&2, Char>, String, cs => T.dec.drop(cs, True{}, []),
        T.dec.chars(vals(hh <> String.to_list(tt))), hh <> String.to_list(tt), dg.backs(SCon{hh, tt}, hd)),
      Equal.trans(String, T.dec.drop(String.to_list(tt), Char.is_eq(hh, '0'),
        T.dec.drop.outz(Char.is_eq(hh, '0'), hh, [])),
        T.dec.drop(String.to_list(tt), False{}, [hh]), SCon{hh, tt},
        Equal.cong(Bool, String, bb => T.dec.drop(String.to_list(tt), bb, T.dec.drop.outz(bb, hh, [])),
          Char.is_eq(hh, '0'), False{}, hz),
        Equal.trans(String, T.dec.drop(String.to_list(tt), False{}, [hh]),
          String.from_list(hh <> String.to_list(tt)), SCon{hh, tt},
          dd.kept(String.to_list(tt), [hh]), M2.ftl(SCon{hh, tt})))))

# the finished numeral is the integer, in range
def int.fin(
  +sg: T.Sign,
  +hh: Char,
  +tt: String,
  +hx: {Char.is_digit(hh) == True{} : Bool},
  +hz: {Char.is_eq(hh, '0') == False{} : Bool},
  +ht: {T.wf.digits(tt) == True{} : Bool},
  hf: {T.i64.fits(sg, SCon{hh, tt}) == True{} : Bool},
  cs: List<&2, Char>
) -> {T.num.fin(ndig(sg, vals(M2.rev.onto(tt, [hh]))), cs) == T.GotVal{T.VInt{sg, SCon{hh, tt}}} : T.Got}:
  Equal.trans(T.Got,
    T.num.fin.range(T.i64.fits(sg, T.dec.text(vals(M2.rev.onto(tt, [hh])))), sg, T.dec.text(vals(M2.rev.onto(tt,
        [hh])))),
    T.num.fin.range(T.i64.fits(sg, SCon{hh, tt}), sg, SCon{hh, tt}),
    T.GotVal{T.VInt{sg, SCon{hh, tt}}},
    Equal.cong(String, T.Got, ss => T.num.fin.range(T.i64.fits(sg, ss), sg, ss),
      T.dec.text(vals(M2.rev.onto(tt, [hh]))), SCon{hh, tt}, dtext(hh, tt, hx, hz, ht)),
    Equal.cong(Bool, T.Got, bb => T.num.fin.range(bb, sg, SCon{hh, tt}), T.i64.fits(sg, SCon{hh, tt}), True{},
      hf))

# GRAMMAR SPIKE: the lemmas of dec_int_word (retired by REVIEW-G10 once
# laws/IntegerReadExactly.bend was proved). The transcribed rule is taken apart by the
# characters it tests, and each part is read by the numeral lemmas of WP-N
# (nw.lead, nw.sign, nw.step, dgo, int.fin): an underscore between digits
# leaves the numeral as it was, so the scan reads the digits with the
# underscores removed.

# a DIGIT is a digit: the two tests are one test once the code point is out
def gs.dig(cc: Char, h: {D1.abnf.DIGIT(cc) == True{} : Bool}) -> {Char.is_digit(cc) == True{} : Bool}:
  match cc:
    case Chr{+cp}:
      h

# a digit is no underscore
def gs.nous(cc: Char, hc: {Char.is_digit(cc) == True{} : Bool}) -> {D1.abnf.underscore(cc) == False{} : Bool}:
  M2.dg.elim(zz => {D1.abnf.underscore(zz) == False{} : Bool}, cc, hc,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# an underscore is the character _
def gs.us(cc: Char, h: {D1.abnf.underscore(cc) == True{} : Bool}) -> {cc == '_' : Char}:
  match cc:
    case Chr{+cp}:
      Eq.char_eq_true(Chr{cp}, '_', h)

# a minus is the character -
def gs.minus(cc: Char, h: {D1.abnf.minus(cc) == True{} : Bool}) -> {cc == '-' : Char}:
  match cc:
    case Chr{+cp}:
      Eq.char_eq_true(Chr{cp}, '-', h)

# a plus is the character +
def gs.plus(cc: Char, h: {D1.abnf.plus(cc) == True{} : Bool}) -> {cc == '+' : Char}:
  match cc:
    case Chr{+cp}:
      Eq.char_eq_true(Chr{cp}, '+', h)

# the 31 bits above a code point's lowest
def gs.up(uu: U32) -> Word(31n):
  match uu:
    case U32{WCon{_bb, rr}}:
      rr

# 48 and 49 differ in their lowest bit only: a code point at least 49 is at
# least 48
def gs.ge01(
  +b0: Bool,
  tt: Cmp,
  +h: {Cmp.is_ge(Word.cmp.fin(b0, True{}, tt)) == True{} : Bool}
) -> {Cmp.is_ge(Word.cmp.fin(b0, False{}, tt)) == True{} : Bool}:
  match b0 tt:
    case _b LT{}:
      h
    case True{} EQ{}:
      {==}
    case False{} EQ{}:
      {==}
    case _b GT{}:
      {==}

# a digit1-9 is a digit
def gs.d19(cc: Char, +h: {D1.abnf.digit1_9(cc) == True{} : Bool}) -> {Char.is_digit(cc) == True{} : Bool}:
  match cc:
    case Chr{U32{WCon{+b0, +rr}}}:
      M3.and.tt(Cmp.is_ge(Word.cmp.fin(b0, False{}, Word.cmp(31n, rr, gs.up(48)))),
        Cmp.is_le(Word.cmp.fin(b0, True{}, Word.cmp(31n, rr, gs.up(57)))),
        gs.ge01(b0, Word.cmp(31n, rr, gs.up(48)), Eq.and.left(Cmp.is_ge(Word.cmp.fin(b0, True{}, Word.cmp(31n, rr,
          gs.up(48)))), Cmp.is_le(Word.cmp.fin(b0, True{}, Word.cmp(31n, rr, gs.up(57)))), h)),
        Eq.and.right(Cmp.is_ge(Word.cmp.fin(b0, True{}, Word.cmp(31n, rr, gs.up(48)))),
          Cmp.is_le(Word.cmp.fin(b0, True{}, Word.cmp(31n, rr, gs.up(57)))), h))

# an and with False on its right is False
def gs.andf(aa: Bool) -> {Bool.and(aa, False{}) == False{} : Bool}:
  match aa:
    case True{}:
      {==}
    case False{}:
      {==}

# with a DIGIT first, the repetition is the repetition after it
def gs.rep.dl(
  +hh: Char,
  +h2: Char,
  +t2: List<&2, Char>,
  +ed: {D1.abnf.DIGIT(hh) == True{} : Bool},
  +hu: {D1.abnf.underscore(hh) == False{} : Bool}
) -> {Bool.or(D1.abnf.dec_rep(h2 <> t2), False{}) == D1.abnf.dec_rep(hh <> h2 <> t2) : Bool}:
  %Equal.sym(Bool, D1.abnf.DIGIT(hh), True{}, ed) : {Bool.or(D1.abnf.dec_rep(h2 <> t2), False{})
    == Bool.or(Bool.and(_, D1.abnf.dec_rep(h2 <> t2)), Bool.and(D1.abnf.underscore(hh),
    Bool.and(D1.abnf.DIGIT(h2), D1.abnf.dec_rep(t2)))) : Bool}
  %Equal.sym(Bool, D1.abnf.underscore(hh), False{}, hu) : {Bool.or(D1.abnf.dec_rep(h2 <> t2), False{})
    == Bool.or(Bool.and(True{}, D1.abnf.dec_rep(h2 <> t2)), Bool.and(_, Bool.and(D1.abnf.DIGIT(h2),
    D1.abnf.dec_rep(t2)))) : Bool}
  {==}

# with no DIGIT first, it is an underscore, a DIGIT and the rest
def gs.rep.ul(
  +hh: Char,
  +h2: Char,
  +t2: List<&2, Char>,
  +ed: {D1.abnf.DIGIT(hh) == False{} : Bool}
) -> {Bool.and(D1.abnf.underscore(hh), Bool.and(D1.abnf.DIGIT(h2), D1.abnf.dec_rep(t2)))
  == D1.abnf.dec_rep(hh <> h2 <> t2) : Bool}:
  %Equal.sym(Bool, D1.abnf.DIGIT(hh), False{}, ed) : {Bool.and(D1.abnf.underscore(hh),
    Bool.and(D1.abnf.DIGIT(h2), D1.abnf.dec_rep(t2))) == Bool.or(Bool.and(_, D1.abnf.dec_rep(h2 <> t2)),
    Bool.and(D1.abnf.underscore(hh), Bool.and(D1.abnf.DIGIT(h2), D1.abnf.dec_rep(t2)))) : Bool}
  {==}

# The repetition *( DIGIT / underscore DIGIT ), taken apart: a claim of each
# of its three shapes is a claim of every text it matches. A DIGIT leads, or
# an underscore and a DIGIT do.
def gs.rep.two(
  -P: List<&2, Char> -> Type,
  +hh: Char,
  +h2: Char,
  +t2: List<&2, Char>,
  dd: Bool,
  +ed: {D1.abnf.DIGIT(hh) == dd : Bool},
  +h: {D1.abnf.dec_rep(hh <> h2 <> t2) == True{} : Bool},
  kd: {Char.is_digit(hh) == True{} : Bool} -> {D1.abnf.dec_rep(h2 <> t2) == True{} : Bool} -> P(hh <> h2 <> t2),
  ku: {Char.is_digit(h2) == True{} : Bool} -> {D1.abnf.dec_rep(t2) == True{} : Bool} -> P('_' <> h2 <> t2)
) -> P(hh <> h2 <> t2):
  match dd:
    case True{}:
      +hx = {gs.dig(hh, ed) : {Char.is_digit(hh) == True{} : Bool}}
      kd(hx, or.fl(D1.abnf.dec_rep(h2 <> t2), Equal.trans(Bool, Bool.or(D1.abnf.dec_rep(h2 <> t2), False{}),
        D1.abnf.dec_rep(hh <> h2 <> t2), True{}, gs.rep.dl(hh, h2, t2, ed, gs.nous(hh, hx)), h)))
    case False{}:
      +hq = {Equal.trans(Bool, Bool.and(D1.abnf.underscore(hh), Bool.and(D1.abnf.DIGIT(h2),
        D1.abnf.dec_rep(t2))), D1.abnf.dec_rep(hh <> h2 <> t2), True{}, gs.rep.ul(hh, h2, t2, ed), h)
        : {Bool.and(D1.abnf.underscore(hh), Bool.and(D1.abnf.DIGIT(h2), D1.abnf.dec_rep(t2))) == True{} : Bool}}
      +hk = {Eq.and.right(D1.abnf.underscore(hh), Bool.and(D1.abnf.DIGIT(h2), D1.abnf.dec_rep(t2)), hq)
        : {Bool.and(D1.abnf.DIGIT(h2), D1.abnf.dec_rep(t2)) == True{} : Bool}}
      %Equal.sym(Char, hh, '_', gs.us(hh, Eq.and.left(D1.abnf.underscore(hh), Bool.and(D1.abnf.DIGIT(h2),
        D1.abnf.dec_rep(t2)), hq))) : P(_ <> h2 <> t2)
      ku(gs.dig(h2, Eq.and.left(D1.abnf.DIGIT(h2), D1.abnf.dec_rep(t2), hk)),
        Eq.and.right(D1.abnf.DIGIT(h2), D1.abnf.dec_rep(t2), hk))

# a character a code point test passed is that character
def gp.cp(cc: Char, +nn: U32, +h: {D1.abnf.cp(cc, nn) == True{} : Bool}) -> {cc == Chr{nn} : Char}:
  match cc:
    case Chr{+cp}:
      Eq.u32_eq(cp, nn, h)

# A fraction. The scan keeps its digits reversed and turns them back at the
# end; the grammar takes them from the front.

# a list reversed onto more, then reversed again, is the more reversed onto
# the list
def t1.revrev(
  ds: List<&2, Char>,
  +acc: List<&2, Char>
) -> {List.reverse.go(&2, Char, List.reverse.go(&2, Char, ds, acc), []) == List.reverse.go(&2, Char, acc, ds)
  : List<&2, Char>}:
  match ds:
    case []:
      {==}
    case +dd <> +dt:
      t1.revrev(dt, dd <> acc)

# two signs sign.eq takes for one are one
def n1.sign.eq(aa: T.Sign, bb: T.Sign, hh: {D2.sign.eq(aa, bb) == True{} : Bool}) -> {aa == bb : T.Sign}:
  match aa bb:
    case T.Plus{} T.Plus{}:
      {==}
    case T.Minus{} T.Minus{}:
      {==}
    case T.Plus{} T.Minus{}:
      Eq.bit.absurd(&2, {T.Plus{} == T.Minus{} : T.Sign}, hh)
    case T.Minus{} T.Plus{}:
      Eq.bit.absurd(&2, {T.Minus{} == T.Plus{} : T.Sign}, hh)
