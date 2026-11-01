# datetime words are accepted exactly when the grammar says, including
# calendar ranges
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../src/arith.bend as Ar
import ../../laws/DateTimeReadExactly.bend as L1
import ../../laws/defs/AbnfGrammar.bend as D1
import ../../laws/defs/DocumentSameness.bend as D2
import ./ControlEscapeText.bend as M1
import ./DigitsWrittenBack.bend as M2
import ./FreshNamesInRows.bend as M3

# February's days by the three divisibility tests, the code's way and the
# table's way, for every answer the tests can give
def feb.same(
  four: Bool,
  hundred: Bool,
  four_hundred: Bool
) -> {T.when.feb.go(four, hundred, four_hundred)
  == D1.feb_days(Bool.and(four, Bool.or(Bool.not(hundred), four_hundred))) : U32}:
  match four hundred four_hundred:
    case False{} _h _q:
      {==}
    case True{} False{} _q:
      {==}
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}

# the code's days of a month are the table's, month by month
def days.same(+yy: U32, mm: D1.Month) -> {T.when.days(yy, L1.month.num(mm)) == D1.days_in(yy, mm) : U32}:
  match mm:
    case D1.Jan{}:
      {==}
    case D1.Feb{}:
      feb.same(U32.is_eq(U32.mod(yy, 4), 0), U32.is_eq(U32.mod(yy, 100), 0),
        U32.is_eq(U32.mod(yy, 400), 0))
    case D1.Mar{}:
      {==}
    case D1.Apr{}:
      {==}
    case D1.May{}:
      {==}
    case D1.Jun{}:
      {==}
    case D1.Jul{}:
      {==}
    case D1.Aug{}:
      {==}
    case D1.Sep{}:
      {==}
    case D1.Oct{}:
      {==}
    case D1.Nov{}:
      {==}
    case D1.Dec{}:
      {==}

# WP-T1: datetime words, exact in both directions. The datetime scan
# (when.read) and toml.abnf's date-time rules are walked together, one
# character test at a time: each test the scan makes is the one the grammar
# makes at the same character (a DIGIT, a separator, T or t, Z or z), so the
# two agree on every word, the failing tests included. The grammar is read
# through its rules' ARest results, and the two digits of each field through
# one eliminator (t1.tk2), with the digits symbolic. A word that matches is
# routed to the datetime scan by word.val (t1.rs); every other word reads as
# no datetime (t1.rn).

# what a datetime scan gives, as a datetime or none
type T1o is Data:
  T1some{w: T.When}
  T1none{}

# a datetime scan's datetime, or none
def t1.wopt(ww: T.WhenOut) -> T1o:
  match ww:
    case T.WSome{w}:
      T1some{w}
    case _:
      T1none{}

# a datetime when the test holds, and none otherwise
def t1.pk(bb: Bool, ww: T.When) -> T1o:
  match bb:
    case True{}:
      T1some{ww}
    case False{}:
      T1none{}

# what the grammar says a word is: the datetime it denotes when it matches a
# date-time rule within the ranges, and none otherwise
def t1.spec(+cs: List<&2, Char>) -> T1o:
  t1.pk(Bool.and(D1.abnf.date_time(cs), D1.prose.date_time_in_range(cs)), D1.g.dt.when(cs))

# nothing is below zero, as a comparison
def t1.ge0n(nn: Nat) -> {Cmp.is_ge(Nat.cmp(nn, 0n)) == True{} : Bool}:
  match nn:
    case 0n:
      {==}
    case 1n+_p:
      {==}

# every U32 is at least 0
def t1.ge0(+xx: U32) -> {U32.is_ge(xx, 0) == True{} : Bool}:
  Equal.trans(Bool, U32.is_ge(xx, 0), Cmp.is_ge(Nat.cmp(U32.to_nat(xx), 0n)), True{},
    Equal.cong(Cmp, Bool, cc => Cmp.is_ge(cc), U32.cmp(xx, 0), Nat.cmp(U32.to_nat(xx), 0n), Ar.u_cmp(xx, 0)),
    t1.ge0n(U32.to_nat(xx)))

# zero plus a word is the word
def t1.wadd0(nn: Nat, ww: Word(nn)) -> {Word.adc(nn, Word.zero(nn), ww, False{}, False{}) == ww : Word(nn)}:
  match nn:
    case 0n:
      match ww:
        case WNil{}:
          {==}
    case 1n+p:
      match ww:
        case WCon{bb, ts}:
          match bb:
            case False{}:
              Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, Word.zero(p), ts, False{}, False{}),
                ts,
                t1.wadd0(p, ts))
            case True{}:
              Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, Word.zero(p), ts, False{}, False{}), ts,
                t1.wadd0(p, ts))

# zero plus a number is the number
def t1.add0(xx: U32) -> {U32.add(0, xx) == xx : U32}:
  match xx:
    case U32{ww}:
      Equal.cong(Word(32n), U32, w => U32{w}, Word.adc(32n, Word.zero(32n), ww, False{}, False{}), ww,
        t1.wadd0(32n, ww))

# the claim of the two-digit eliminator for a failed take and no match
def t1.Tb(-P: List<&2, Char> -> T.Dig -> D1.ARest -> Type) -> Type:
  @xs: List<&2, Char> -> P(xs, T.DigBad{}, D1.ANone{})

# and for two digits and the rest
def t1.Tk(-P: List<&2, Char> -> T.Dig -> D1.ARest -> Type) -> Type:
  @c1: Char -> @c2: Char -> @rr: List<&2, Char> -> {Char.is_digit(c1) == True{} : Bool} ->
    {Char.is_digit(c2) == True{} : Bool} -> P(c1 <> c2 <> rr, T.DigOk{D1.g.two(c1 <> c2 <> rr), rr}, D1.ALeft{rr})

# the second digit
def t1.tk2.b(
  -P: List<&2, Char> -> T.Dig -> D1.ARest -> Type,
  +x1: U32,
  +x2: U32,
  +ts: List<&2, Char>,
  d2: Bool,
  +e1: {Char.is_digit(Chr{x1}) == True{} : Bool},
  +e2: {Char.is_digit(Chr{x2}) == d2 : Bool},
  hb: t1.Tb(P),
  hk: t1.Tk(P)
) -> P(Chr{x1} <> Chr{x2} <> ts, T.take.fin(d2, T.take.acc.d(d2, U32.add(U32.mul(0, 10), U32.sub(x1, 48)), Chr{x2}),
  ts),
  D1.abnf.keep(d2, ts)):
  match d2:
    case False{}:
      hb(Chr{x1} <> Chr{x2} <> ts)
    case True{}:
      %Equal.sym(U32, U32.add(0, U32.sub(x1, 48)), U32.sub(x1, 48), t1.add0(U32.sub(x1, 48))) :
        P(Chr{x1} <> Chr{x2} <> ts, T.DigOk{U32.add(U32.mul(_, 10), U32.sub(x2, 48)), ts}, D1.ALeft{ts})
      hk(Chr{x1}, Chr{x2}, ts, e1, e2)

# the first digit
def t1.tk2.a(
  -P: List<&2, Char> -> T.Dig -> D1.ARest -> Type,
  +x1: U32,
  d1: Bool,
  ts: List<&2, Char>,
  e1: {Char.is_digit(Chr{x1}) == d1 : Bool},
  hb: t1.Tb(P),
  hk: t1.Tk(P)
) -> P(Chr{x1} <> ts, T.take.n(1n, ts, T.take.acc.d(d1, 0, Chr{x1}), d1),
  D1.abnf.digit_r(D1.abnf.keep(d1, ts))):
  match d1:
    case False{}:
      match ts:
        case []:
          hb([Chr{x1}])
        case +h2 <> +t2:
          hb(Chr{x1} <> h2 <> t2)
    case True{}:
      match ts:
        case []:
          hb([Chr{x1}])
        case +h2 <> +t2:
          match h2:
            case Chr{+x2}:
              t1.tk2.b(P, x1, x2, t2, Char.is_digit(Chr{x2}), e1, {==}, hb, hk)

# two digits from the front of a word, as the scan takes them and as two
# DIGITs of the grammar: a claim of the failed take and no match, and of two
# digits and the rest, is a claim of every word
def t1.tk2(
  -P: List<&2, Char> -> T.Dig -> D1.ARest -> Type,
  cs: List<&2, Char>,
  hb: t1.Tb(P),
  hk: t1.Tk(P)
) -> P(cs, T.take.n(2n, cs, 0, True{}), D1.abnf.digit_r(D1.abnf.digit_r(D1.ALeft{cs}))):
  match cs:
    case []:
      hb([])
    case hh <> +ts:
      match hh:
        case Chr{+x1}:
          t1.tk2.a(P, x1, Char.is_digit(Chr{x1}), ts, {==}, hb, hk)

# a range from 0 is the upper bound's test, since every number is at least 0
def t1.rng0(+xx: U32, +hi: U32) -> {T.bound.rng(xx, 0, hi) == U32.is_le(xx, hi) : Bool}:
  %Equal.sym(Bool, U32.is_ge(xx, 0), True{}, t1.ge0(xx)) : {Bool.and(_, U32.is_le(xx, hi)) == U32.is_le(xx, hi) : Bool}
  {==}

# A zone, or the end of a local datetime. The grammar's time-offset, or
# nothing, after a partial-time: a word that ends there is a local-date-time
# (or local-time), and one that goes on with a time-offset is an
# offset-date-time.

# a time-offset's range, or nothing to check when the word ends
def t1.zok(zz: List<&2, Char>) -> Bool:
  match zz:
    case []:
      True{}
    case _h <> _t:
      D1.prose.zone_ok(D1.g.dt.zone(zz))

# what the grammar says of the text z after a partial-time: the end, or a
# time-offset within its range, and the datetime of the date and clock with
# that zone
def t1.zn(+zz: List<&2, Char>, clock: T.Clock, date: T.Date) -> T1o:
  t1.pk(Bool.and(Bool.or(D1.abnf.all_r(D1.abnf.time_offset(D1.ALeft{zz})), D1.abnf.all_r(D1.ALeft{zz})),
    t1.zok(zz)), D1.g.dt.zoned(date, clock, zz))

# the offset's two ranges, once nothing follows it
def t1.z.ok(
  hk: Bool,
  mk: Bool,
  +sign: T.Sign,
  +hh: U32,
  +mi: U32,
  +clock: T.Clock,
  +date: T.Date
) -> {t1.wopt(T.when.zone.mm.ok(hk, mk, sign, hh, mi, clock, date))
  == t1.pk(Bool.and(True{}, Bool.and(hk, mk)), T.WOff{date, clock, T.Shift{sign, hh, mi}}) : T1o}:
  match hk:
    case False{}:
      {==}
    case True{}:
      match mk:
        case False{}:
          {==}
        case True{}:
          {==}

# nothing may follow the offset's minutes
def t1.z.end(
  rr: List<&2, Char>,
  +hk: Bool,
  +mk: Bool,
  +sign: T.Sign,
  +hh: U32,
  +mi: U32,
  +clock: T.Clock,
  +date: T.Date
) -> {t1.wopt(T.when.zone.mm.end(rr, hk, mk, sign, hh, mi, clock, date))
  == t1.pk(Bool.and(Bool.or(D1.abnf.all_r(D1.ALeft{rr}), False{}), Bool.and(hk, mk)),
    T.WOff{date, clock, T.Shift{sign, hh, mi}}) : T1o}:
  match rr:
    case []:
      t1.z.ok(hk, mk, sign, hh, mi, clock, date)
    case _h <> _t:
      {==}

# the offset's end, with its ranges as the scan tests them
def t1.z.fin(
  +rr: List<&2, Char>,
  +sign: T.Sign,
  +hh: U32,
  +mi: U32,
  +clock: T.Clock,
  +date: T.Date
) -> {t1.wopt(T.when.zone.mm.end(rr, T.bound.rng(hh, 0, 23), T.bound.rng(mi, 0, 59), sign, hh, mi, clock, date))
  == t1.pk(Bool.and(Bool.or(D1.abnf.all_r(D1.ALeft{rr}), False{}), D1.prose.zone_ok(T.Shift{sign, hh, mi})),
    T.WOff{date, clock, T.Shift{sign, hh, mi}}) : T1o}:
  %t1.rng0(hh, 23) : {t1.wopt(T.when.zone.mm.end(rr, T.bound.rng(hh, 0, 23), T.bound.rng(mi, 0, 59), sign, hh, mi,
    clock,
    date)) == t1.pk(Bool.and(Bool.or(D1.abnf.all_r(D1.ALeft{rr}), False{}), Bool.and(_, U32.is_le(mi, 59))),
    T.WOff{date, clock, T.Shift{sign, hh, mi}}) : T1o}
  %t1.rng0(mi, 59) : {t1.wopt(T.when.zone.mm.end(rr, T.bound.rng(hh, 0, 23), T.bound.rng(mi, 0, 59), sign, hh, mi,
    clock,
    date)) == t1.pk(Bool.and(Bool.or(D1.abnf.all_r(D1.ALeft{rr}), False{}), Bool.and(T.bound.rng(hh, 0, 23), _)),
    T.WOff{date, clock, T.Shift{sign, hh, mi}}) : T1o}
  t1.z.end(rr, T.bound.rng(hh, 0, 23), T.bound.rng(mi, 0, 59), sign, hh, mi, clock, date)

# the offset's minutes, after its colon
def t1.z.mm(
  hit: Bool,
  +uu: List<&2, Char>,
  +sign: T.Sign,
  +hh: U32,
  +clock: T.Clock,
  +date: T.Date
) -> {t1.wopt(T.when.zone.mm(hit, T.take.n(2n, uu, 0, True{}), sign, hh, clock, date))
  == t1.pk(Bool.and(Bool.or(D1.abnf.all_r(D1.abnf.digit_r(D1.abnf.digit_r(D1.abnf.keep(hit, uu)))), False{}),
    D1.prose.zone_ok(T.Shift{sign, hh, D1.g.two(List.drop(&2, Char, uu, 0n))})),
    T.WOff{date, clock, T.Shift{sign, hh, D1.g.two(List.drop(&2, Char, uu, 0n))}}) : T1o}:
  match hit:
    case False{}:
      {==}
    case True{}:
      t1.tk2(xs => dd => r => {t1.wopt(T.when.zone.mm.go(dd, sign, hh, clock, date))
        == t1.pk(Bool.and(Bool.or(D1.abnf.all_r(r), False{}),
        D1.prose.zone_ok(T.Shift{sign, hh, D1.g.two(List.drop(&2, Char, xs, 0n))})),
        T.WOff{date, clock, T.Shift{sign, hh, D1.g.two(List.drop(&2, Char, xs, 0n))}}) : T1o}, uu,
        _xs => {==},
        +c1 => +c2 => +rr => _e1 => _e2 => t1.z.fin(rr, sign, hh, D1.g.two(c1 <> c2 <> rr), clock, date))

# the colon after the offset's hour
def t1.z.col(
  rr: List<&2, Char>,
  +sign: T.Sign,
  +hh: U32,
  +clock: T.Clock,
  +date: T.Date
) -> {t1.wopt(T.when.zone.hh.colon(rr, sign, hh, clock, date))
  == t1.pk(Bool.and(Bool.or(D1.abnf.all_r(D1.abnf.digit_r(D1.abnf.digit_r(D1.abnf.char_r(D1.ALeft{rr},
    58)))), False{}), D1.prose.zone_ok(T.Shift{sign, hh, D1.g.two(List.drop(&2, Char, rr, 1n))})),
    T.WOff{date, clock, T.Shift{sign, hh, D1.g.two(List.drop(&2, Char, rr, 1n))}}) : T1o}:
  match rr:
    case []:
      {==}
    case hh2 <> +uu:
      match hh2:
        case Chr{+qq}:
          t1.z.mm(Char.is_eq(Chr{qq}, ':'), uu, sign, hh, clock, date)

# a numeric offset's hour, colon and minute, after its sign
def t1.z.off(
  +sign: T.Sign,
  +tt: List<&2, Char>,
  +clock: T.Clock,
  +date: T.Date
) -> {t1.wopt(T.when.zone.off(sign, tt, clock, date))
  == t1.pk(Bool.and(Bool.or(D1.abnf.all_r(D1.abnf.time_minute(D1.abnf.char_r(D1.abnf.time_hour(D1.ALeft{tt}),
    58))), False{}), D1.prose.zone_ok(T.Shift{sign, D1.g.two(tt), D1.g.two(List.drop(&2, Char, tt, 3n))})),
    T.WOff{date, clock, T.Shift{sign, D1.g.two(tt), D1.g.two(List.drop(&2, Char, tt, 3n))}}) : T1o}:
  t1.tk2(xs => dd => r => {t1.wopt(T.when.zone.hh(dd, sign, clock, date))
    == t1.pk(Bool.and(Bool.or(D1.abnf.all_r(D1.abnf.digit_r(D1.abnf.digit_r(D1.abnf.char_r(r, 58)))), False{}),
    D1.prose.zone_ok(T.Shift{sign, D1.g.two(xs), D1.g.two(List.drop(&2, Char, xs, 3n))})),
    T.WOff{date, clock, T.Shift{sign, D1.g.two(xs), D1.g.two(List.drop(&2, Char, xs, 3n))}}) : T1o}, tt,
    _xs => {==},
    +c1 => +c2 => +rr => _e1 => _e2 => t1.z.col(rr, sign, D1.g.two(c1 <> c2 <> rr), clock, date))

# what the grammar says after a time-offset's sign: the numeric offset
def t1.z.num(+pl: Bool, +mi: Bool, +tt: List<&2, Char>) -> D1.ARest:
  D1.abnf.time_minute(D1.abnf.char_r(D1.abnf.time_hour(D1.abnf.or_r(D1.abnf.keep(pl, tt),
    D1.abnf.keep(mi, tt))), 58))

# a plus: the offset is read with that sign, since a plus is no minus
def t1.z.plus(
  mi: Bool,
  +tt: List<&2, Char>,
  +clock: T.Clock,
  +date: T.Date,
  hm: {Char.is_eq('+', '-') == mi : Bool}
) -> {t1.wopt(T.when.zone.off(T.Plus{}, tt, clock, date))
  == t1.pk(Bool.and(Bool.or(D1.abnf.all_r(t1.z.num(True{}, mi, tt)), False{}),
    D1.prose.zone_ok(D1.g.dt.zone.pick(mi, False{}, tt))), T.WOff{date, clock, D1.g.dt.zone.pick(mi, False{},
      tt)})
    : T1o}:
  match mi:
    case True{}:
      Eq.bit.absurd(&2, {t1.wopt(T.when.zone.off(T.Plus{}, tt, clock, date))
        == t1.pk(Bool.and(Bool.or(D1.abnf.all_r(t1.z.num(True{}, True{}, tt)), False{}),
        D1.prose.zone_ok(D1.g.dt.zone.pick(True{}, False{}, tt))), T.WOff{date, clock,
        D1.g.dt.zone.pick(True{}, False{}, tt)}) : T1o}, hm)
    case False{}:
      t1.z.off(T.Plus{}, tt, clock, date)

# a plus or a minus starts a numeric offset
def t1.z.sign(
  pl: Bool,
  mi: Bool,
  +xx: U32,
  +tt: List<&2, Char>,
  +clock: T.Clock,
  +date: T.Date,
  hp: {Char.is_eq(Chr{xx}, '+') == pl : Bool},
  hm: {Char.is_eq(Chr{xx}, '-') == mi : Bool}
) -> {t1.wopt(T.when.zone.sign(pl, mi, tt, clock, date))
  == t1.pk(Bool.and(Bool.or(D1.abnf.all_r(t1.z.num(pl, mi, tt)), False{}),
    D1.prose.zone_ok(D1.g.dt.zone.pick(mi, False{}, tt))), T.WOff{date, clock, D1.g.dt.zone.pick(mi, False{},
      tt)})
    : T1o}:
  match pl:
    case True{}:
      t1.z.plus(mi, tt, clock, date, Equal.trans(Bool, Char.is_eq('+', '-'), Char.is_eq(Chr{xx}, '-'), mi,
        Equal.cong(Char, Bool, cc => Char.is_eq(cc, '-'), '+', Chr{xx},
          Equal.sym(Char, Chr{xx}, '+', Eq.char_eq_true(Chr{xx}, '+', hp))), hm))
    case False{}:
      match mi:
        case True{}:
          t1.z.off(T.Minus{}, tt, clock, date)
        case False{}:
          {==}

# Z (or z) ends the word, and otherwise a sign starts a numeric offset
def t1.z.go(
  zee: Bool,
  +pl: Bool,
  +mi: Bool,
  +xx: U32,
  tt: List<&2, Char>,
  +clock: T.Clock,
  +date: T.Date,
  hp: {Char.is_eq(Chr{xx}, '+') == pl : Bool},
  hm: {Char.is_eq(Chr{xx}, '-') == mi : Bool}
) -> {t1.wopt(T.when.zone.go(zee, pl, mi, tt, clock, date))
  == t1.pk(Bool.and(Bool.or(D1.abnf.all_r(D1.abnf.or_r(D1.abnf.keep(zee, tt), t1.z.num(pl, mi, tt))), False{}),
    D1.prose.zone_ok(D1.g.dt.zone.pick(mi, zee, tt))), T.WOff{date, clock, D1.g.dt.zone.pick(mi, zee,
      tt)}) : T1o}:
  match zee:
    case True{}:
      match tt:
        case []:
          {==}
        case _h <> _t:
          {==}
    case False{}:
      t1.z.sign(pl, mi, xx, tt, clock, date, hp, hm)

# a zone, or the end, after a partial-time: the scan reads exactly what the
# grammar says, Z or z included
def t1.z(
  zz: List<&2, Char>,
  +clock: T.Clock,
  +date: T.Date
) -> {t1.wopt(T.when.zone(zz, clock, date)) == t1.zn(zz, clock, date) : T1o}:
  match zz:
    case []:
      {==}
    case hh <> +tt:
      match hh:
        case Chr{+xx}:
          t1.z.go(Bool.or(Char.is_eq(Chr{xx}, 'Z'), Char.is_eq(Chr{xx}, 'z')), Char.is_eq(Chr{xx}, '+'),
            Char.is_eq(Chr{xx}, '-'), xx, tt, clock, date, {==}, {==})

# what is observed of a datetime scan's outcome: the datetime (md), or the
# local time the scan keeps of it when it read a time with no date
def t1.obs(md: Bool, ww: T.WhenOut) -> T1o:
  match md:
    case True{}:
      t1.wopt(ww)
    case False{}:
      t1.wopt(T.when.time.only(ww))

# a failed scan is observed as none
def t1.obs.fail(md: Bool, +why: String) -> {t1.obs(md, T.WFail{why}) == T1none{} : T1o}:
  match md:
    case True{}:
      {==}
    case False{}:
      {==}

# a list reversed onto a list with a character has a character
def t1.somerev(
  xs: List<&2, Char>,
  +hh: Char,
  +acc: List<&2, Char>
) -> {T.cs.some(List.reverse.go(&2, Char, xs, hh <> acc)) == True{} : Bool}:
  match xs:
    case []:
      {==}
    case +xh <> +xt:
      t1.somerev(xt, xh, hh <> acc)

# the scan's fraction digits are the word's leading digits, and what follows
# them is the word after its leading digits
def t1.Fl(+tt: List<&2, Char>, +rv: List<&2, Char>, +clock: T.Clock, +date: T.Date) -> Type:
  {T.when.frac.digits(tt, rv, clock, date) == T.when.frac.end(List.reverse.go(&2, Char, D1.g.take_digits(tt), rv),
    clock, date, D1.abnf.drop_digits(tt)) : T.WhenOut}

# one character of the fraction's digits: a digit is kept, and anything else
# ends them
def t1.fl.d(
  dg: Bool,
  +yy: U32,
  +uu: List<&2, Char>,
  +rv: List<&2, Char>,
  +clock: T.Clock,
  +date: T.Date,
  ih: t1.Fl(uu, Chr{yy} <> rv, clock, date)
) -> {T.when.frac.digit(dg, Chr{yy}, uu, rv, clock, date, _u => T.when.frac.digits(uu, Chr{yy} <> rv, clock, date))
  == T.when.frac.end(List.reverse.go(&2, Char, D1.g.take_digits.pick(dg, Chr{yy}, D1.g.take_digits(uu)), rv), clock,
    date, D1.abnf.drop_digits.pick(dg, Chr{yy}, uu, D1.abnf.drop_digits(uu))) : T.WhenOut}:
  match dg:
    case True{}:
      ih
    case False{}:
      {==}

# the fraction's digits are the word's leading digits, and what follows them
# is the word after its leading digits
def t1.fl(
  tt: List<&2, Char>,
  +rv: List<&2, Char>,
  +clock: T.Clock,
  +date: T.Date
) -> {T.when.frac.digits(tt, rv, clock, date) == T.when.frac.end(List.reverse.go(&2, Char, D1.g.take_digits(tt), rv),
  clock, date, D1.abnf.drop_digits(tt)) : T.WhenOut}:
  match tt:
    case []:
      {==}
    case hh <> +uu:
      match hh:
        case Chr{+yy}:
          t1.fl.d(Char.is_digit(Chr{yy}), yy, uu, rv, clock, date, t1.fl(uu, Chr{yy} <> rv, clock, date))

# a match of the grammar's rest handed to what follows it, or none
def t1.ofz(
  pp: D1.ARest,
  fin: List<&2, Char> -> T.Clock -> List<&2, Char> -> T1o,
  clk: T.Clock,
  aa: List<&2, Char>
) -> T1o:
  match pp:
    case D1.ALeft{zz}:
      fin(zz, clk, aa)
    case D1.ANone{}:
      T1none{}

# the fraction's digits end: there is one, and the zone follows
def t1.F.end(
  +md: Bool,
  -fin: List<&2, Char> -> T.Clock -> List<&2, Char> -> T1o,
  +yy: U32,
  +uu: List<&2, Char>,
  +hh: U32,
  +mi: U32,
  +ss: U32,
  +date: T.Date,
  hz: @zz: List<&2, Char> -> @ck: T.Clock -> {t1.obs(md, T.when.zone(zz, ck, date)) == fin(zz, ck, zz) : T1o}
) -> {t1.obs(md, T.when.frac.end(List.reverse.go(&2, Char, D1.g.take_digits(uu), [Chr{yy}]), T.Clock{hh, mi, ss,
  ""}, date,
  D1.abnf.drop_digits(uu))) == fin(D1.abnf.drop_digits(uu), T.Clock{hh, mi, ss, String.from_list(Chr{yy}
  <> D1.g.take_digits(uu))}, D1.abnf.drop_digits(uu)) : T1o}:
  %Equal.sym(Bool, T.cs.some(List.reverse.go(&2, Char, D1.g.take_digits(uu), [Chr{yy}])), True{},
    t1.somerev(D1.g.take_digits(uu), Chr{yy}, [])) : {t1.obs(md, T.when.frac.end.go(_, List.reverse.go(&2, Char,
    D1.g.take_digits(uu), [Chr{yy}]), T.Clock{hh, mi, ss, ""}, date, D1.abnf.drop_digits(uu)))
    == fin(D1.abnf.drop_digits(uu), T.Clock{hh, mi, ss, String.from_list(Chr{yy} <> D1.g.take_digits(uu))},
    D1.abnf.drop_digits(uu)) : T1o}
  Equal.trans(T1o,
    t1.obs(md, T.when.zone(D1.abnf.drop_digits(uu), T.Clock{hh, mi, ss, T.buf.str.go(List.reverse.go(&2, Char,
      D1.g.take_digits(uu), [Chr{yy}]), "")}, date)),
    t1.obs(md, T.when.zone(D1.abnf.drop_digits(uu), T.Clock{hh, mi, ss, String.from_list(Chr{yy}
      <> D1.g.take_digits(uu))}, date)),
    fin(D1.abnf.drop_digits(uu), T.Clock{hh, mi, ss, String.from_list(Chr{yy} <> D1.g.take_digits(uu))},
      D1.abnf.drop_digits(uu)),
    Equal.cong(String, T1o, fs => t1.obs(md, T.when.zone(D1.abnf.drop_digits(uu), T.Clock{hh, mi, ss, fs}, date)),
      T.buf.str.go(List.reverse.go(&2, Char, D1.g.take_digits(uu), [Chr{yy}]), ""),
      String.from_list(Chr{yy} <> D1.g.take_digits(uu)),
      Equal.trans(String,
        T.buf.str.go(List.reverse.go(&2, Char, D1.g.take_digits(uu), [Chr{yy}]), ""),
        String.from_list(List.reverse.go(&2, Char, List.reverse.go(&2, Char, D1.g.take_digits(uu), [Chr{yy}]), [])),
        String.from_list(Chr{yy} <> D1.g.take_digits(uu)),
        M1.fold.nil(List.reverse.go(&2, Char, D1.g.take_digits(uu), [Chr{yy}])),
        Equal.cong(List<&2, Char>, String, ls => String.from_list(ls),
          List.reverse.go(&2, Char, List.reverse.go(&2, Char, D1.g.take_digits(uu), [Chr{yy}]), []),
          Chr{yy} <> D1.g.take_digits(uu), M2.t1.revrev(D1.g.take_digits(uu), [Chr{yy}])))),
    hz(D1.abnf.drop_digits(uu), T.Clock{hh, mi, ss, String.from_list(Chr{yy} <> D1.g.take_digits(uu))}))

# the fraction's first digit, and the rest of its digits
def t1.F.d1(
  +md: Bool,
  -fin: List<&2, Char> -> T.Clock -> List<&2, Char> -> T1o,
  dg: Bool,
  +yy: U32,
  +uu: List<&2, Char>,
  +hh: U32,
  +mi: U32,
  +ss: U32,
  +date: T.Date,
  hz: @zz: List<&2, Char> -> @ck: T.Clock -> {t1.obs(md, T.when.zone(zz, ck, date)) == fin(zz, ck, zz) : T1o}
) -> {t1.obs(md, T.when.frac.digit(dg, Chr{yy}, uu, [], T.Clock{hh, mi, ss, ""}, date, _u => T.when.frac.digits(uu,
  [Chr{yy}],
  T.Clock{hh, mi, ss, ""}, date))) == t1.ofz(D1.abnf.keep(dg, D1.abnf.drop_digits(uu)), fin, T.Clock{hh, mi, ss,
  String.from_list(D1.g.take_digits.pick(dg, Chr{yy}, D1.g.take_digits(uu)))},
  D1.abnf.drop_digits.pick(dg, Chr{yy}, uu, D1.abnf.drop_digits(uu))) : T1o}:
  match dg:
    case False{}:
      t1.obs.fail(md, "invalid fraction")
    case True{}:
      Equal.trans(T1o, t1.obs(md, T.when.frac.digits(uu, [Chr{yy}], T.Clock{hh, mi, ss, ""}, date)),
        t1.obs(md, T.when.frac.end(List.reverse.go(&2, Char, D1.g.take_digits(uu), [Chr{yy}]), T.Clock{hh, mi, ss,
          ""}, date,
          D1.abnf.drop_digits(uu))),
        fin(D1.abnf.drop_digits(uu), T.Clock{hh, mi, ss, String.from_list(Chr{yy} <> D1.g.take_digits(uu))},
          D1.abnf.drop_digits(uu)),
        Equal.cong(T.WhenOut, T1o, ww => t1.obs(md, ww), T.when.frac.digits(uu, [Chr{yy}], T.Clock{hh, mi, ss, ""},
          date),
          T.when.frac.end(List.reverse.go(&2, Char, D1.g.take_digits(uu), [Chr{yy}]), T.Clock{hh, mi, ss, ""}, date,
          D1.abnf.drop_digits(uu)), t1.fl(uu, [Chr{yy}], T.Clock{hh, mi, ss, ""}, date)),
        t1.F.end(md, fin, yy, uu, hh, mi, ss, date, hz))

# the fraction's digits after its dot: at least one
def t1.F.dig(
  +md: Bool,
  -fin: List<&2, Char> -> T.Clock -> List<&2, Char> -> T1o,
  tt: List<&2, Char>,
  +hh: U32,
  +mi: U32,
  +ss: U32,
  +date: T.Date,
  hz: @zz: List<&2, Char> -> @ck: T.Clock -> {t1.obs(md, T.when.zone(zz, ck, date)) == fin(zz, ck, zz) : T1o}
) -> {t1.obs(md, T.when.frac.digits(tt, [], T.Clock{hh, mi, ss, ""},
  date)) == t1.ofz(D1.abnf.digits1_r(D1.ALeft{tt}), fin,
  T.Clock{hh, mi, ss, String.from_list(D1.g.take_digits(tt))}, D1.abnf.drop_digits(tt)) : T1o}:
  match tt:
    case []:
      t1.obs.fail(md, "invalid fraction")
    case yh <> +uu:
      match yh:
        case Chr{+yy}:
          t1.F.d1(md, fin, Char.is_digit(Chr{yy}), yy, uu, hh, mi, ss, date, hz)

# a dot starts a fraction, and anything else is the zone
def t1.F.go(
  +md: Bool,
  -fin: List<&2, Char> -> T.Clock -> List<&2, Char> -> T1o,
  dot: Bool,
  +xx: U32,
  +tt: List<&2, Char>,
  +hh: U32,
  +mi: U32,
  +ss: U32,
  +date: T.Date,
  hd: {Char.is_eq(Chr{xx}, '.') == dot : Bool},
  hz: @zz: List<&2, Char> -> @ck: T.Clock -> {t1.obs(md, T.when.zone(zz, ck, date)) == fin(zz, ck, zz) : T1o}
) -> {t1.obs(md, T.when.frac.go(dot, tt, T.Clock{hh, mi, ss, ""}, date,
  Chr{xx})) == t1.ofz(D1.abnf.opt_secfrac.pick(dot,
  Chr{xx} <> tt), fin, T.Clock{hh, mi, ss, D1.g.dt.frac.pick(dot, tt)}, D1.g.dt.after_frac.pick(dot, Chr{xx}, tt))
  : T1o}:
  match dot:
    case False{}:
      hz(Chr{xx} <> tt, T.Clock{hh, mi, ss, ""})
    case True{}:
      %Equal.sym(Char, Chr{xx}, '.', Eq.char_eq_true(Chr{xx}, '.', hd)) : {t1.obs(md, T.when.frac.digits(tt, [],
        T.Clock{hh, mi,
        ss, ""}, date)) == t1.ofz(D1.abnf.time_secfrac(D1.ALeft{_ <> tt}), fin, T.Clock{hh, mi, ss,
        String.from_list(D1.g.take_digits(tt))}, D1.abnf.drop_digits(tt)) : T1o}
      t1.F.dig(md, fin, tt, hh, mi, ss, date, hz)

# after a partial-time's seconds: an optional fraction, and then the zone or
# the end, read by the scan as the grammar's [ time-secfrac ] and then
# whatever follows it (fin), with the clock's fraction the digits after the
# dot. O is what is observed of the scan's outcome
def t1.F(
  +md: Bool,
  -fin: List<&2, Char> -> T.Clock -> List<&2, Char> -> T1o,
  rr: List<&2, Char>,
  +hh: U32,
  +mi: U32,
  +ss: U32,
  +date: T.Date,
  hz: @zz: List<&2, Char> -> @ck: T.Clock -> {t1.obs(md, T.when.zone(zz, ck, date)) == fin(zz, ck, zz) : T1o}
) -> {t1.obs(md, T.when.frac(rr, T.Clock{hh, mi, ss, ""}, date)) == t1.ofz(D1.abnf.opt_secfrac(D1.ALeft{rr}), fin,
  T.Clock{hh, mi, ss, D1.g.dt.frac(List.drop(&2, Char, rr, 0n))}, D1.g.dt.after_frac(List.drop(&2, Char, rr, 0n)))
  : T1o}:
  match rr:
    case []:
      hz([], T.Clock{hh, mi, ss, ""})
    case xh <> +tt:
      match xh:
        case Chr{+xx}:
          t1.F.go(md, fin, Char.is_eq(Chr{xx}, '.'), xx, tt, hh, mi, ss, date, {==}, hz)

# A partial-time's minutes and seconds, after its hour and colon, and then
# the fraction and zone. The scan checks the clock's ranges once it has the
# seconds; the grammar's are prose.clock_ok.

# a result when the test holds, and none otherwise
def t1.gate(bb: Bool, oo: T1o) -> T1o:
  match bb:
    case True{}:
      oo
    case False{}:
      T1none{}

# a match of the grammar's rest handed on when the clock is in range
def t1.ofg(
  pp: D1.ARest,
  ck: Bool,
  fin: List<&2, Char> -> T.Clock -> List<&2, Char> -> T1o,
  clk: T.Clock,
  aa: List<&2, Char>
) -> T1o:
  match pp:
    case D1.ALeft{zz}:
      t1.gate(ck, fin(zz, clk, aa))
    case D1.ANone{}:
      T1none{}

# a range check before the rest is the rest's match with the check
def t1.gofz(
  ck: Bool,
  pp: D1.ARest,
  -fin: List<&2, Char> -> T.Clock -> List<&2, Char> -> T1o,
  +clk: T.Clock,
  +aa: List<&2, Char>
) -> {t1.gate(ck, t1.ofz(pp, fin, clk, aa)) == t1.ofg(pp, ck, fin, clk, aa) : T1o}:
  match ck:
    case True{}:
      match pp:
        case D1.ALeft{_z}:
          {==}
        case D1.ANone{}:
          {==}
    case False{}:
      match pp:
        case D1.ALeft{_z}:
          {==}
        case D1.ANone{}:
          {==}

# what the grammar says of the text after a partial-time's hour and colon:
# minutes, colon and seconds (qq is the grammar's rest after them), the clock
# in range, and then the fraction and what follows it
def t1.ofc(
  qq: D1.ARest,
  fin: List<&2, Char> -> T.Clock -> List<&2, Char> -> T1o,
  +hh: U32,
  +mi: U32,
  +ss: U32,
  +r5: List<&2, Char>
) -> T1o:
  t1.ofg(D1.abnf.opt_secfrac(qq), D1.prose.clock_ok(T.Clock{hh, mi, ss, ""}), fin,
    T.Clock{hh, mi, ss, D1.g.dt.frac(r5)}, D1.g.dt.after_frac(r5))

# the scan's three range checks are the clock's ranges
def t1.C.ck(
  +hh: U32,
  +mi: U32,
  +ss: U32
) -> {Bool.and(T.bound.rng(hh, 0, 23), Bool.and(T.bound.rng(mi, 0, 59), T.bound.rng(ss, 0, 60))) ==
  D1.prose.clock_ok(T.Clock{hh, mi, ss, ""}) : Bool}:
  %t1.rng0(hh, 23) : {Bool.and(T.bound.rng(hh, 0, 23), Bool.and(T.bound.rng(mi, 0, 59), T.bound.rng(ss, 0, 60)))
    == Bool.and(_, Bool.and(U32.is_le(mi, 59), U32.is_le(ss, 60))) : Bool}
  %t1.rng0(mi, 59) : {Bool.and(T.bound.rng(hh, 0, 23), Bool.and(T.bound.rng(mi, 0, 59), T.bound.rng(ss, 0, 60)))
    == Bool.and(T.bound.rng(hh, 0, 23), Bool.and(_, U32.is_le(ss, 60))) : Bool}
  %t1.rng0(ss, 60) : {Bool.and(T.bound.rng(hh, 0, 23), Bool.and(T.bound.rng(mi, 0, 59), T.bound.rng(ss, 0, 60)))
    == Bool.and(T.bound.rng(hh, 0, 23), Bool.and(T.bound.rng(mi, 0, 59), _)) : Bool}
  {==}

# the scan's range checks gate the fraction
def t1.C.rng(
  +md: Bool,
  hk: Bool,
  mk: Bool,
  sk: Bool,
  +hh: U32,
  +mi: U32,
  +ss: U32,
  +rr: List<&2, Char>,
  +date: T.Date,
) -> {t1.obs(md, T.when.clock.range(hk, mk, sk, hh, mi, ss, rr, date)) == t1.gate(Bool.and(hk, Bool.and(mk, sk)),
  t1.obs(md, T.when.frac(rr, T.Clock{hh, mi, ss, ""}, date))) : T1o}:
  match hk:
    case False{}:
      t1.obs.fail(md, "hour is out of range")
    case True{}:
      match mk:
        case False{}:
          t1.obs.fail(md, "minute is out of range")
        case True{}:
          match sk:
            case False{}:
              t1.obs.fail(md, "second is out of range")
            case True{}:
              {==}

# the seconds taken: the ranges, then the fraction and the zone
def t1.C.fin(
  +md: Bool,
  -fin: List<&2, Char> -> T.Clock -> List<&2, Char> -> T1o,
  +rr: List<&2, Char>,
  +hh: U32,
  +mi: U32,
  +ss: U32,
  +date: T.Date,
  hz: @zz: List<&2, Char> -> @ck: T.Clock -> {t1.obs(md, T.when.zone(zz, ck, date)) == fin(zz, ck, zz) : T1o}
) -> {t1.obs(md, T.when.clock.range(T.bound.rng(hh, 0, 23), T.bound.rng(mi, 0, 59), T.bound.rng(ss, 0, 60), hh, mi,
  ss, rr,
  date)) == t1.ofc(D1.ALeft{rr}, fin, hh, mi, ss, List.drop(&2, Char, rr, 0n)) : T1o}:
  Equal.trans(T1o, t1.obs(md, T.when.clock.range(T.bound.rng(hh, 0, 23), T.bound.rng(mi, 0, 59), T.bound.rng(ss, 0,
    60), hh, mi,
    ss, rr, date)),
    t1.gate(Bool.and(T.bound.rng(hh, 0, 23), Bool.and(T.bound.rng(mi, 0, 59), T.bound.rng(ss, 0, 60))),
      t1.obs(md, T.when.frac(rr, T.Clock{hh, mi, ss, ""}, date))),
    t1.ofc(D1.ALeft{rr}, fin, hh, mi, ss, List.drop(&2, Char, rr, 0n)),
    t1.C.rng(md, T.bound.rng(hh, 0, 23), T.bound.rng(mi, 0, 59), T.bound.rng(ss, 0, 60), hh, mi, ss, rr, date),
    %Equal.sym(Bool, Bool.and(T.bound.rng(hh, 0, 23), Bool.and(T.bound.rng(mi, 0, 59), T.bound.rng(ss, 0, 60))),
      D1.prose.clock_ok(T.Clock{hh, mi, ss, ""}), t1.C.ck(hh, mi, ss)) : {t1.gate(_, t1.obs(md, T.when.frac(rr,
        T.Clock{hh,
      mi, ss, ""}, date))) == t1.ofc(D1.ALeft{rr}, fin, hh, mi, ss, List.drop(&2, Char, rr, 0n)) : T1o}
    %Equal.sym(T1o, t1.obs(md, T.when.frac(rr, T.Clock{hh, mi, ss, ""}, date)),
      t1.ofz(D1.abnf.opt_secfrac(D1.ALeft{rr}), fin,
      T.Clock{hh, mi, ss, D1.g.dt.frac(List.drop(&2, Char, rr, 0n))}, D1.g.dt.after_frac(List.drop(&2, Char, rr,
      0n))), t1.F(md, fin, rr, hh, mi, ss, date, hz)) : {t1.gate(D1.prose.clock_ok(T.Clock{hh, mi, ss, ""}), _)
      == t1.ofc(D1.ALeft{rr}, fin, hh, mi, ss, List.drop(&2, Char, rr, 0n)) : T1o}
    t1.gofz(D1.prose.clock_ok(T.Clock{hh, mi, ss, ""}), D1.abnf.opt_secfrac(D1.ALeft{rr}), fin,
      T.Clock{hh, mi, ss, D1.g.dt.frac(List.drop(&2, Char, rr, 0n))},
      D1.g.dt.after_frac(List.drop(&2, Char, rr, 0n))))

# the seconds, after the colon that follows the minutes
def t1.C.ss(
  +md: Bool,
  -fin: List<&2, Char> -> T.Clock -> List<&2, Char> -> T1o,
  hit: Bool,
  +uu: List<&2, Char>,
  +hh: U32,
  +mi: U32,
  +date: T.Date,
  hz: @zz: List<&2, Char> -> @ck: T.Clock -> {t1.obs(md, T.when.zone(zz, ck, date)) == fin(zz, ck, zz) : T1o}
) -> {t1.obs(md, T.when.clock.ss(hit, T.take.n(2n, uu, 0, True{}), hh, mi, date)) == t1.ofc(D1.abnf.time_second(
  D1.abnf.keep(hit, uu)), fin, hh, mi, D1.g.two(List.drop(&2, Char, uu, 0n)), List.drop(&2, Char, uu, 2n)) : T1o}:
  match hit:
    case False{}:
      t1.obs.fail(md, "invalid time")
    case True{}:
      t1.tk2(xs => dd => r => {t1.obs(md, T.when.clock.ss.go(dd, hh, mi, date)) == t1.ofc(r, fin, hh, mi,
        D1.g.two(List.drop(&2, Char, xs, 0n)), List.drop(&2, Char, xs, 2n)) : T1o}, uu,
        _xs => t1.obs.fail(md, "invalid time"),
        +s1 => +s2 => +rr => _e1 => _e2 => t1.C.fin(md, fin, rr, hh, mi, D1.g.two(s1 <> s2 <> rr), date, hz))

# the colon after the minutes
def t1.C.col(
  +md: Bool,
  -fin: List<&2, Char> -> T.Clock -> List<&2, Char> -> T1o,
  rr: List<&2, Char>,
  +hh: U32,
  +mi: U32,
  +date: T.Date,
  hz: @zz: List<&2, Char> -> @ck: T.Clock -> {t1.obs(md, T.when.zone(zz, ck, date)) == fin(zz, ck, zz) : T1o}
) -> {t1.obs(md, T.when.clock.mm.colon(rr, hh, mi, date)) == t1.ofc(D1.abnf.time_second(D1.abnf.char_r(
  D1.ALeft{rr}, 58)), fin, hh, mi, D1.g.two(List.drop(&2, Char, rr, 1n)), List.drop(&2, Char, rr, 3n)) : T1o}:
  match rr:
    case []:
      t1.obs.fail(md, "invalid time")
    case qh <> +uu:
      match qh:
        case Chr{+qq}:
          t1.C.ss(md, fin, Char.is_eq(Chr{qq}, ':'), uu, hh, mi, date, hz)

# a partial-time after its hour and colon, then the fraction and what
# follows: the scan reads the minutes and seconds as the grammar's two
# DIGITs each, checks the clock's ranges, and reads the rest (t1.F)
def t1.C(
  +md: Bool,
  -fin: List<&2, Char> -> T.Clock -> List<&2, Char> -> T1o,
  tt: List<&2, Char>,
  +hh: U32,
  +date: T.Date,
  hz: @zz: List<&2, Char> -> @ck: T.Clock -> {t1.obs(md, T.when.zone(zz, ck, date)) == fin(zz, ck, zz) : T1o}
) -> {t1.obs(md, T.when.clock.mm(T.take.n(2n, tt, 0, True{}), hh, date)) == t1.ofc(D1.abnf.time_second(
  D1.abnf.char_r(D1.abnf.time_minute(D1.ALeft{tt}), 58)), fin, hh, D1.g.two(List.drop(&2, Char, tt, 0n)),
  D1.g.two(List.drop(&2, Char, tt, 3n)), List.drop(&2, Char, tt, 5n)) : T1o}:
  t1.tk2(xs => dd => r => {t1.obs(md, T.when.clock.mm(dd, hh, date)) == t1.ofc(D1.abnf.time_second(
    D1.abnf.char_r(r, 58)), fin, hh, D1.g.two(List.drop(&2, Char, xs, 0n)), D1.g.two(List.drop(&2, Char, xs, 3n)),
    List.drop(&2, Char, xs, 5n)) : T1o}, tt,
    _xs => t1.obs.fail(md, "invalid time"),
    +m1 => +m2 => +rr => _e1 => _e2 => t1.C.col(md, fin, rr, hh, D1.g.two(m1 <> m2 <> rr), date, hz))

# The date's day check: the code's days of a month are the table's for every
# number, a month's or not. Each month's number is tested in turn; a number
# no month has is read by both as January's 31 days.

# the claim for a month's number
def t1.Dm(+yy: U32, +mo: U32) -> Type:
  {T.when.days(yy, mo) == D1.days_in(yy, D1.prose.month(mo)) : U32}

# a number that is a month's number k, or one tested and found not to be
def t1.dd(
  ee: Bool,
  +kk: U32,
  +mo: U32,
  +yy: U32,
  he: {U32.is_eq(mo, kk) == ee : Bool},
  yes: t1.Dm(yy, kk),
  no: {ee == False{} : Bool} -> t1.Dm(yy, mo)
) -> t1.Dm(yy, mo):
  match ee:
    case True{}:
      %Equal.sym(U32, mo, kk, Equal.cong(Char, U32, cc => Char.to_u32(cc), Chr{mo}, Chr{kk}, Eq.u32_eq(mo, kk, he))) :
        {T.when.days(yy, _) == D1.days_in(yy, D1.prose.month(_)) : U32}
      yes
    case False{}:
      no({==})

# a number no month has is January to the table
def t1.jan(
  e2: Bool,
  e3: Bool,
  e4: Bool,
  e5: Bool,
  e6: Bool,
  e7: Bool,
  e8: Bool,
  e9: Bool,
  e10: Bool,
  e11: Bool,
  e12: Bool,
  h2: {e2 == False{} : Bool},
  h3: {e3 == False{} : Bool},
  h4: {e4 == False{} : Bool},
  h5: {e5 == False{} : Bool},
  h6: {e6 == False{} : Bool},
  h7: {e7 == False{} : Bool},
  h8: {e8 == False{} : Bool},
  h9: {e9 == False{} : Bool},
  h10: {e10 == False{} : Bool},
  h11: {e11 == False{} : Bool},
  h12: {e12 == False{} : Bool}
) -> {D1.prose.month.pick(e2, D1.Feb{}, D1.prose.month.pick(e3, D1.Mar{}, D1.prose.month.pick(e4, D1.Apr{},
  D1.prose.month.pick(e5, D1.May{}, D1.prose.month.pick(e6, D1.Jun{}, D1.prose.month.pick(e7, D1.Jul{},
  D1.prose.month.pick(e8, D1.Aug{}, D1.prose.month.pick(e9, D1.Sep{}, D1.prose.month.pick(e10, D1.Oct{},
  D1.prose.month.pick(e11, D1.Nov{}, D1.prose.month.pick(e12, D1.Dec{}, D1.Jan{}))))))))))) == D1.Jan{}
  : D1.Month}:
  %Equal.sym(Bool, e2, False{}, h2) : {D1.prose.month.pick(_, D1.Feb{}, D1.prose.month.pick(e3, D1.Mar{},
    D1.prose.month.pick(e4, D1.Apr{},
    D1.prose.month.pick(e5, D1.May{}, D1.prose.month.pick(e6, D1.Jun{}, D1.prose.month.pick(e7, D1.Jul{},
    D1.prose.month.pick(e8, D1.Aug{}, D1.prose.month.pick(e9, D1.Sep{}, D1.prose.month.pick(e10, D1.Oct{},
    D1.prose.month.pick(e11, D1.Nov{}, D1.prose.month.pick(e12, D1.Dec{}, D1.Jan{}))))))))))) == D1.Jan{}
    : D1.Month}
  %Equal.sym(Bool, e3, False{}, h3) : {D1.prose.month.pick(_, D1.Mar{}, D1.prose.month.pick(e4, D1.Apr{},
    D1.prose.month.pick(e5, D1.May{}, D1.prose.month.pick(e6, D1.Jun{}, D1.prose.month.pick(e7, D1.Jul{},
    D1.prose.month.pick(e8, D1.Aug{}, D1.prose.month.pick(e9, D1.Sep{}, D1.prose.month.pick(e10, D1.Oct{},
    D1.prose.month.pick(e11, D1.Nov{}, D1.prose.month.pick(e12, D1.Dec{}, D1.Jan{})))))))))) == D1.Jan{}
    : D1.Month}
  %Equal.sym(Bool, e4, False{}, h4) : {D1.prose.month.pick(_, D1.Apr{},
    D1.prose.month.pick(e5, D1.May{}, D1.prose.month.pick(e6, D1.Jun{}, D1.prose.month.pick(e7, D1.Jul{},
    D1.prose.month.pick(e8, D1.Aug{}, D1.prose.month.pick(e9, D1.Sep{}, D1.prose.month.pick(e10, D1.Oct{},
    D1.prose.month.pick(e11, D1.Nov{}, D1.prose.month.pick(e12, D1.Dec{}, D1.Jan{}))))))))) == D1.Jan{}
    : D1.Month}
  %Equal.sym(Bool, e5, False{}, h5) : {D1.prose.month.pick(_, D1.May{}, D1.prose.month.pick(e6, D1.Jun{},
    D1.prose.month.pick(e7, D1.Jul{},
    D1.prose.month.pick(e8, D1.Aug{}, D1.prose.month.pick(e9, D1.Sep{}, D1.prose.month.pick(e10, D1.Oct{},
    D1.prose.month.pick(e11, D1.Nov{}, D1.prose.month.pick(e12, D1.Dec{}, D1.Jan{})))))))) == D1.Jan{}
    : D1.Month}
  %Equal.sym(Bool, e6, False{}, h6) : {D1.prose.month.pick(_, D1.Jun{}, D1.prose.month.pick(e7, D1.Jul{},
    D1.prose.month.pick(e8, D1.Aug{}, D1.prose.month.pick(e9, D1.Sep{}, D1.prose.month.pick(e10, D1.Oct{},
    D1.prose.month.pick(e11, D1.Nov{}, D1.prose.month.pick(e12, D1.Dec{}, D1.Jan{}))))))) == D1.Jan{}
    : D1.Month}
  %Equal.sym(Bool, e7, False{}, h7) : {D1.prose.month.pick(_, D1.Jul{},
    D1.prose.month.pick(e8, D1.Aug{}, D1.prose.month.pick(e9, D1.Sep{}, D1.prose.month.pick(e10, D1.Oct{},
    D1.prose.month.pick(e11, D1.Nov{}, D1.prose.month.pick(e12, D1.Dec{}, D1.Jan{})))))) == D1.Jan{}
    : D1.Month}
  %Equal.sym(Bool, e8, False{}, h8) : {D1.prose.month.pick(_, D1.Aug{}, D1.prose.month.pick(e9, D1.Sep{},
    D1.prose.month.pick(e10, D1.Oct{},
    D1.prose.month.pick(e11, D1.Nov{}, D1.prose.month.pick(e12, D1.Dec{}, D1.Jan{}))))) == D1.Jan{}
    : D1.Month}
  %Equal.sym(Bool, e9, False{}, h9) : {D1.prose.month.pick(_, D1.Sep{}, D1.prose.month.pick(e10, D1.Oct{},
    D1.prose.month.pick(e11, D1.Nov{}, D1.prose.month.pick(e12, D1.Dec{}, D1.Jan{})))) == D1.Jan{}
    : D1.Month}
  %Equal.sym(Bool, e10, False{}, h10) : {D1.prose.month.pick(_, D1.Oct{},
    D1.prose.month.pick(e11, D1.Nov{}, D1.prose.month.pick(e12, D1.Dec{}, D1.Jan{}))) == D1.Jan{}
    : D1.Month}
  %Equal.sym(Bool, e11, False{}, h11) : {D1.prose.month.pick(_, D1.Nov{}, D1.prose.month.pick(e12, D1.Dec{},
    D1.Jan{})) == D1.Jan{}
    : D1.Month}
  %Equal.sym(Bool, e12, False{}, h12) : {D1.prose.month.pick(_, D1.Dec{}, D1.Jan{}) == D1.Jan{} : D1.Month}
  {==}

# and 31 days to the code
def t1.d31(
  +yy: U32,
  e2: Bool,
  e4: Bool,
  e6: Bool,
  e9: Bool,
  e11: Bool,
  h2: {e2 == False{} : Bool},
  h4: {e4 == False{} : Bool},
  h6: {e6 == False{} : Bool},
  h9: {e9 == False{} : Bool},
  h11: {e11 == False{} : Bool}
) -> {T.when.days.go(e2, Bool.or(Bool.or(e4, e6), Bool.or(e9, e11)), yy) == 31 : U32}:
  %Equal.sym(Bool, e2, False{}, h2) : {T.when.days.go(_, Bool.or(Bool.or(e4, e6), Bool.or(e9, e11)), yy) == 31 : U32}
  %Equal.sym(Bool, e4, False{}, h4) : {T.when.days.go(False{}, Bool.or(Bool.or(_, e6), Bool.or(e9, e11)),
    yy) == 31 : U32}
  %Equal.sym(Bool, e6, False{}, h6) : {T.when.days.go(False{}, Bool.or(Bool.or(False{}, _), Bool.or(e9, e11)),
    yy) == 31 : U32}
  %Equal.sym(Bool, e9, False{}, h9) : {T.when.days.go(False{}, Bool.or(False{}, Bool.or(_, e11)), yy) == 31 : U32}
  %Equal.sym(Bool, e11, False{}, h11) : {T.when.days.go(False{}, Bool.or(False{}, Bool.or(False{}, _)), yy) == 31 : U32}
  {==}

# a number that is no month's
def t1.dlast(
  +mo: U32,
  +yy: U32,
  h2: {U32.is_eq(mo, 2) == False{} : Bool},
  h3: {U32.is_eq(mo, 3) == False{} : Bool},
  +h4: {U32.is_eq(mo, 4) == False{} : Bool},
  h5: {U32.is_eq(mo, 5) == False{} : Bool},
  +h6: {U32.is_eq(mo, 6) == False{} : Bool},
  h7: {U32.is_eq(mo, 7) == False{} : Bool},
  h8: {U32.is_eq(mo, 8) == False{} : Bool},
  +h9: {U32.is_eq(mo, 9) == False{} : Bool},
  h10: {U32.is_eq(mo, 10) == False{} : Bool},
  +h11: {U32.is_eq(mo, 11) == False{} : Bool},
  h12: {U32.is_eq(mo, 12) == False{} : Bool},
  +g2: {U32.is_eq(mo, 2) == False{} : Bool}
) -> t1.Dm(yy, mo):
  Equal.trans(U32, T.when.days(yy, mo), 31, D1.days_in(yy, D1.prose.month(mo)),
    t1.d31(yy, U32.is_eq(mo, 2), U32.is_eq(mo, 4), U32.is_eq(mo, 6), U32.is_eq(mo, 9), U32.is_eq(mo, 11), g2, h4, h6,
      h9, h11),
    Equal.cong(D1.Month, U32, mm => D1.days_in(yy, mm), D1.Jan{}, D1.prose.month(mo),
      Equal.sym(D1.Month, D1.prose.month(mo), D1.Jan{}, t1.jan(U32.is_eq(mo, 2), U32.is_eq(mo, 3),
        U32.is_eq(mo, 4), U32.is_eq(mo, 5), U32.is_eq(mo, 6), U32.is_eq(mo, 7), U32.is_eq(mo, 8), U32.is_eq(mo, 9),
        U32.is_eq(mo, 10), U32.is_eq(mo, 11), U32.is_eq(mo, 12), h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12))))

# the code's days of a month are the table's, for every number
def t1.days(+yy: U32, +mo: U32) -> t1.Dm(yy, mo):
  t1.dd(U32.is_eq(mo, 2), 2, mo, yy, {==}, days.same(yy, D1.Feb{}), +h2 =>
  t1.dd(U32.is_eq(mo, 3), 3, mo, yy, {==}, days.same(yy, D1.Mar{}), h3 =>
  t1.dd(U32.is_eq(mo, 4), 4, mo, yy, {==}, days.same(yy, D1.Apr{}), +h4 =>
  t1.dd(U32.is_eq(mo, 5), 5, mo, yy, {==}, days.same(yy, D1.May{}), h5 =>
  t1.dd(U32.is_eq(mo, 6), 6, mo, yy, {==}, days.same(yy, D1.Jun{}), +h6 =>
  t1.dd(U32.is_eq(mo, 7), 7, mo, yy, {==}, days.same(yy, D1.Jul{}), h7 =>
  t1.dd(U32.is_eq(mo, 8), 8, mo, yy, {==}, days.same(yy, D1.Aug{}), h8 =>
  t1.dd(U32.is_eq(mo, 9), 9, mo, yy, {==}, days.same(yy, D1.Sep{}), +h9 =>
  t1.dd(U32.is_eq(mo, 10), 10, mo, yy, {==}, days.same(yy, D1.Oct{}), h10 =>
  t1.dd(U32.is_eq(mo, 11), 11, mo, yy, {==}, days.same(yy, D1.Nov{}), +h11 =>
  t1.dd(U32.is_eq(mo, 12), 12, mo, yy, {==}, days.same(yy, D1.Dec{}), h12 =>
  t1.dlast(mo, yy, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h2))))))))))))

# an and with False on its right is False
def t1.andf(aa: Bool) -> {Bool.and(aa, False{}) == False{} : Bool}:
  match aa:
    case True{}:
      {==}
    case False{}:
      {==}

# the date's range check is the scan's two checks, with the code's days of
# the month
def t1.dok(
  +yy: U32,
  +mo: U32,
  +dd: U32
) -> {D1.prose.date_ok(T.Date{yy, mo, dd}) == Bool.and(T.bound.rng(mo, 1, 12), T.bound.rng(dd, 1, T.when.days(yy,
  mo))) : Bool}:
  %t1.days(yy, mo) : {Bool.and(D1.abnf.range(mo, 1, 12), Bool.and(U32.is_ge(dd, 1), U32.is_le(dd, _)))
    == Bool.and(T.bound.rng(mo, 1, 12), T.bound.rng(dd, 1, T.when.days(yy, mo))) : Bool}
  {==}

# a datetime with a date out of range is out of range, whatever its zone
def t1.wkz(
  +date: T.Date,
  +clk: T.Clock,
  zz: List<&2, Char>,
  +hd: {D1.prose.date_ok(date) == False{} : Bool}
) -> {D1.prose.when_ok(D1.g.dt.zoned(date, clk, zz)) == False{} : Bool}:
  match zz:
    case []:
      %Equal.sym(Bool, D1.prose.date_ok(date), False{}, hd) : {Bool.and(_,
        D1.prose.clock_ok(clk)) == False{} : Bool}
      {==}
    case +zh <> +zt:
      %Equal.sym(Bool, D1.prose.date_ok(date), False{}, hd) : {Bool.and(_, Bool.and(D1.prose.clock_ok(clk),
        D1.prose.zone_ok(D1.g.dt.zone(zh <> zt)))) == False{} : Bool}
      {==}

# and so is a date alone, or a date with a time after it
def t1.wk(
  +cs: List<&2, Char>,
  +tm: List<&2, Char>,
  ee: Bool,
  +hd: {D1.prose.date_ok(D1.g.dt.date(cs)) == False{} : Bool}
) -> {D1.prose.when_ok(D1.g.dt.when.pick(False{}, cs, tm, ee)) == False{} : Bool}:
  match ee:
    case True{}:
      hd
    case False{}:
      t1.wkz(D1.g.dt.date(cs), D1.g.dt.clock(tm), D1.g.dt.after_frac(List.drop(&2, Char, tm, 8n)), hd)

# so a word with a date out of range denotes nothing the grammar allows
def t1.dbad(
  +xx: Bool,
  +cs: List<&2, Char>,
  +tm: List<&2, Char>,
  +ee: Bool,
  +hd: {D1.prose.date_ok(D1.g.dt.date(cs)) == False{} : Bool}
) -> {t1.pk(Bool.and(xx, D1.prose.when_ok(D1.g.dt.when.pick(False{}, cs, tm, ee))),
  D1.g.dt.when.pick(False{}, cs, tm, ee)) == T1none{} : T1o}:
  %Equal.sym(Bool, D1.prose.when_ok(D1.g.dt.when.pick(False{}, cs, tm, ee)), False{}, t1.wk(cs, tm, ee, hd)) :
    {t1.pk(Bool.and(xx, _), D1.g.dt.when.pick(False{}, cs, tm, ee)) == T1none{} : T1o}
  %Equal.sym(Bool, Bool.and(xx, False{}), False{}, t1.andf(xx)) : {t1.pk(_, D1.g.dt.when.pick(False{}, cs, tm, ee))
    == T1none{} : T1o}
  {==}

# Finishing a partial-time: after a date and a delimiter, the scan's zone is
# the grammar's time-offset or the end (t1.fdt); after a time alone, the
# scan reads a zone too and then keeps only a local time, and the grammar's
# local-time is the partial-time and nothing after it (t1.ftm).

# after a date: the end, or a time-offset in its range
def t1.fdt(+date: T.Date, +zz: List<&2, Char>, clk: T.Clock, +aa: List<&2, Char>) -> T1o:
  t1.pk(Bool.and(Bool.or(D1.abnf.all_r(D1.abnf.time_offset(D1.ALeft{zz})), D1.abnf.all_r(D1.ALeft{zz})),
    t1.zok(aa)), D1.g.dt.zoned(date, clk, aa))

# after a time alone: the end
def t1.ftm(zz: List<&2, Char>, clk: T.Clock, _aa: List<&2, Char>) -> T1o:
  t1.pk(D1.abnf.all_r(D1.ALeft{zz}), T.WTime{clk})

# a local datetime kept as its time, and nothing else
def t1.only(oo: T1o) -> T1o:
  match oo:
    case T1some{ww}:
      match ww:
        case T.WLocal{_d, clk}:
          T1some{T.WTime{clk}}
        case _:
          T1none{}
    case T1none{}:
      T1none{}

# what the scan keeps of a time alone
def t1.onlyw(ww: T.WhenOut) -> {t1.wopt(T.when.time.only(ww)) == t1.only(t1.wopt(ww)) : T1o}:
  match ww:
    case T.WSome{w}:
      match w:
        case T.WOff{_d, _c, _z}:
          {==}
        case T.WLocal{_d, _c}:
          {==}
        case T.WDate{_d}:
          {==}
        case T.WTime{_c}:
          {==}
    case T.WFail{_y}:
      {==}
    case T.WSkip{}:
      {==}

# a datetime with a zone is no time alone
def t1.only.off(
  bb: Bool,
  +date: T.Date,
  +clk: T.Clock,
  +zn: T.Zone
) -> {t1.only(t1.pk(bb, T.WOff{date, clk, zn})) == T1none{} : T1o}:
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# a time alone: the end is kept, and a zone is refused
def t1.zt(
  zz: List<&2, Char>,
  +clk: T.Clock
) -> {t1.obs(False{}, T.when.zone(zz, clk, T.Date{0, 1, 1})) == t1.ftm(zz, clk, zz) : T1o}:
  match zz:
    case []:
      {==}
    case +zh <> +zt:
      Equal.trans(T1o, t1.wopt(T.when.time.only(T.when.zone(zh <> zt, clk, T.Date{0, 1, 1}))),
        t1.only(t1.wopt(T.when.zone(zh <> zt, clk, T.Date{0, 1, 1}))), T1none{},
        t1.onlyw(T.when.zone(zh <> zt, clk, T.Date{0, 1, 1})),
        Equal.trans(T1o, t1.only(t1.wopt(T.when.zone(zh <> zt, clk, T.Date{0, 1, 1}))),
          t1.only(t1.zn(zh <> zt, clk, T.Date{0, 1, 1})), T1none{},
          Equal.cong(T1o, T1o, oo => t1.only(oo), t1.wopt(T.when.zone(zh <> zt, clk, T.Date{0, 1, 1})),
            t1.zn(zh <> zt, clk, T.Date{0, 1, 1}), t1.z(zh <> zt, clk, T.Date{0, 1, 1})),
          t1.only.off(Bool.and(Bool.or(D1.abnf.all_r(D1.abnf.time_offset(D1.ALeft{zh <> zt})), False{}),
            t1.zok(zh <> zt)), T.Date{0, 1, 1}, clk, D1.g.dt.zone(zh <> zt))))

# a time alone, its clock gated by its range: the partial-time and nothing
# after it, with the clock in range
def t1.algt(
  pp: D1.ARest,
  ck: Bool,
  +clk: T.Clock,
  +aa: List<&2, Char>
) -> {t1.ofg(pp, ck, zz => cc => ab => t1.ftm(zz, cc, ab), clk, aa)
  == t1.pk(Bool.and(D1.abnf.all_r(pp), ck), T.WTime{clk}) : T1o}:
  match pp:
    case D1.ALeft{zz}:
      match zz:
        case []:
          match ck:
            case True{}:
              {==}
            case False{}:
              {==}
        case _h <> _t:
          match ck:
            case True{}:
              {==}
            case False{}:
              {==}
    case D1.ANone{}:
      {==}

# the scan's clock check gating the zone's, against the grammar's ranges,
# when the word ends after its partial-time
def t1.b4(
  ck: Bool,
  aa: Bool,
  bb: Bool,
  +ww: T.When
) -> {t1.gate(ck, t1.pk(Bool.and(Bool.or(aa, bb), True{}), ww)) == t1.pk(Bool.and(Bool.or(aa, Bool.or(bb, False{})),
  Bool.and(True{}, ck)), ww) : T1o}:
  match ck:
    case False{}:
      match aa:
        case True{}:
          {==}
        case False{}:
          match bb:
            case True{}:
              {==}
            case False{}:
              {==}
    case True{}:
      match aa:
        case True{}:
          {==}
        case False{}:
          match bb:
            case True{}:
              {==}
            case False{}:
              {==}

# and when a time-offset follows it
def t1.b5(
  ck: Bool,
  aa: Bool,
  bb: Bool,
  +zk: Bool,
  +ww: T.When
) -> {t1.gate(ck, t1.pk(Bool.and(Bool.or(aa, bb), zk), ww)) == t1.pk(Bool.and(Bool.or(aa, Bool.or(bb, False{})),
  Bool.and(True{}, Bool.and(ck, zk))), ww) : T1o}:
  match ck:
    case False{}:
      match aa:
        case True{}:
          match zk:
            case True{}:
              {==}
            case False{}:
              {==}
        case False{}:
          match bb:
            case True{}:
              match zk:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              {==}
    case True{}:
      match aa:
        case True{}:
          {==}
        case False{}:
          match bb:
            case True{}:
              {==}
            case False{}:
              {==}

# a date and a time, its clock gated by its range, and then the end or a
# time-offset: the grammar's local-date-time or offset-date-time, with every
# field in range, when the date is in range
def t1.algd(
  pp: D1.ARest,
  aa: List<&2, Char>,
  ck: Bool,
  +date: T.Date,
  +clk: T.Clock,
  hdo: {D1.prose.date_ok(date) == True{} : Bool},
  hck: {D1.prose.clock_ok(clk) == ck : Bool}
) -> {t1.ofg(pp, ck, zz => cc => ab => t1.fdt(date, zz, cc, ab), clk, aa)
  == t1.pk(Bool.and(Bool.or(D1.abnf.all_r(D1.abnf.time_offset(pp)), Bool.or(D1.abnf.all_r(pp), False{})),
    D1.prose.when_ok(D1.g.dt.zoned(date, clk, aa))), D1.g.dt.zoned(date, clk, aa)) : T1o}:
  match pp:
    case D1.ANone{}:
      {==}
    case D1.ALeft{+zz}:
      match aa:
        case []:
          %Equal.sym(Bool, D1.prose.date_ok(date), True{}, hdo) : {t1.gate(ck, t1.pk(Bool.and(Bool.or(D1.abnf.all_r(
            D1.abnf.time_offset(D1.ALeft{zz})), D1.abnf.all_r(D1.ALeft{zz})), True{}), T.WLocal{date, clk}))
            == t1.pk(Bool.and(Bool.or(D1.abnf.all_r(D1.abnf.time_offset(D1.ALeft{zz})),
            Bool.or(D1.abnf.all_r(D1.ALeft{zz}), False{})), Bool.and(_, D1.prose.clock_ok(clk))),
            T.WLocal{date, clk}) : T1o}
          %Equal.sym(Bool, D1.prose.clock_ok(clk), ck, hck) : {t1.gate(ck, t1.pk(Bool.and(Bool.or(D1.abnf.all_r(
            D1.abnf.time_offset(D1.ALeft{zz})), D1.abnf.all_r(D1.ALeft{zz})), True{}), T.WLocal{date, clk}))
            == t1.pk(Bool.and(Bool.or(D1.abnf.all_r(D1.abnf.time_offset(D1.ALeft{zz})),
            Bool.or(D1.abnf.all_r(D1.ALeft{zz}), False{})), Bool.and(True{}, _)),
            T.WLocal{date, clk}) : T1o}
          t1.b4(ck, D1.abnf.all_r(D1.abnf.time_offset(D1.ALeft{zz})), D1.abnf.all_r(D1.ALeft{zz}),
            T.WLocal{date, clk})
        case +ah <> +at:
          %Equal.sym(Bool, D1.prose.date_ok(date), True{}, hdo) : {t1.gate(ck, t1.pk(Bool.and(Bool.or(D1.abnf.all_r(
            D1.abnf.time_offset(D1.ALeft{zz})), D1.abnf.all_r(D1.ALeft{zz})), D1.prose.zone_ok(
            D1.g.dt.zone(ah <> at))), T.WOff{date, clk, D1.g.dt.zone(ah <> at)}))
            == t1.pk(Bool.and(Bool.or(D1.abnf.all_r(D1.abnf.time_offset(D1.ALeft{zz})),
            Bool.or(D1.abnf.all_r(D1.ALeft{zz}), False{})), Bool.and(_, Bool.and(D1.prose.clock_ok(clk),
            D1.prose.zone_ok(D1.g.dt.zone(ah <> at))))), T.WOff{date, clk, D1.g.dt.zone(ah <> at)}) : T1o}
          %Equal.sym(Bool, D1.prose.clock_ok(clk), ck, hck) : {t1.gate(ck, t1.pk(Bool.and(Bool.or(D1.abnf.all_r(
            D1.abnf.time_offset(D1.ALeft{zz})), D1.abnf.all_r(D1.ALeft{zz})), D1.prose.zone_ok(
            D1.g.dt.zone(ah <> at))), T.WOff{date, clk, D1.g.dt.zone(ah <> at)}))
            == t1.pk(Bool.and(Bool.or(D1.abnf.all_r(D1.abnf.time_offset(D1.ALeft{zz})),
            Bool.or(D1.abnf.all_r(D1.ALeft{zz}), False{})), Bool.and(True{}, Bool.and(_,
            D1.prose.zone_ok(D1.g.dt.zone(ah <> at))))), T.WOff{date, clk, D1.g.dt.zone(ah <> at)}) : T1o}
          t1.b5(ck, D1.abnf.all_r(D1.abnf.time_offset(D1.ALeft{zz})), D1.abnf.all_r(D1.ALeft{zz}),
            D1.prose.zone_ok(D1.g.dt.zone(ah <> at)), T.WOff{date, clk, D1.g.dt.zone(ah <> at)})

# The whole word. toml.abnf's date-time is four alternatives; offset-date-time,
# local-date-time and local-date start with a full-date and local-time with a
# partial-time, and each of those starts with two DIGITs. The scan takes the
# same two digits and then goes by the third character: a colon is a time
# alone, and a digit a date.

# the four alternatives, from what full-date (fd) and partial-time (pt) left
# of the word
def t1.G(+fd: D1.ARest, pt: D1.ARest) -> Bool:
  Bool.or(D1.abnf.all_r(D1.abnf.time_offset(D1.abnf.partial_time(D1.abnf.time_delim(fd)))),
    Bool.or(D1.abnf.all_r(D1.abnf.partial_time(D1.abnf.time_delim(fd))),
    Bool.or(D1.abnf.all_r(fd), D1.abnf.all_r(pt))))

# the datetime a word denotes, with its third character's colon test given
def t1.W3(colon: Bool, +cs: List<&2, Char>) -> T.When:
  D1.g.dt.when.pick(colon, cs, List.drop(&2, Char, cs, 11n), List.is_empty(&2, Char, List.drop(&2, Char, cs, 10n)))

# what the grammar says of a word, from what full-date and partial-time left
# of it and its third character's colon test
def t1.S3(fd: D1.ARest, pt: D1.ARest, +colon: Bool, +cs: List<&2, Char>) -> T1o:
  t1.pk(Bool.and(t1.G(fd, pt), D1.prose.when_ok(t1.W3(colon, cs))), t1.W3(colon, cs))

# full-date after its first two DIGITs
def t1.FDa(xx: D1.ARest) -> D1.ARest:
  D1.abnf.date_mday(D1.abnf.char_r(D1.abnf.date_month(D1.abnf.char_r(D1.abnf.digit_r(D1.abnf.digit_r(xx)),
    45)), 45))

# after three
def t1.FDb(xx: D1.ARest) -> D1.ARest:
  D1.abnf.date_mday(D1.abnf.char_r(D1.abnf.date_month(D1.abnf.char_r(D1.abnf.digit_r(xx), 45)), 45))

# after the year
def t1.FDc(xx: D1.ARest) -> D1.ARest:
  D1.abnf.date_mday(D1.abnf.char_r(D1.abnf.date_month(D1.abnf.char_r(xx, 45)), 45))

# partial-time after its hour
def t1.PTa(xx: D1.ARest) -> D1.ARest:
  D1.abnf.opt_secfrac(D1.abnf.time_second(D1.abnf.char_r(D1.abnf.time_minute(D1.abnf.char_r(xx, 58)), 58)))

# after its hour and colon
def t1.PTb(xx: D1.ARest) -> D1.ARest:
  D1.abnf.opt_secfrac(D1.abnf.time_second(D1.abnf.char_r(D1.abnf.time_minute(xx), 58)))

# what the grammar says after a full-date and a time-delim: the partial-time
# matched (pp) and what follows it, with the date and the time's text tm
def t1.SP(+pp: D1.ARest, +date: T.Date, +tm: List<&2, Char>) -> T1o:
  t1.pk(Bool.and(Bool.or(D1.abnf.all_r(D1.abnf.time_offset(pp)), Bool.or(D1.abnf.all_r(pp), False{})),
    D1.prose.when_ok(D1.g.dt.zoned(date, D1.g.dt.clock(tm), D1.g.dt.after_frac(List.drop(&2, Char, tm, 8n))))),
    D1.g.dt.zoned(date, D1.g.dt.clock(tm), D1.g.dt.after_frac(List.drop(&2, Char, tm, 8n))))

# the time's colon after its hour, and the rest of the time
def t1.r17(
  hit: Bool,
  +h1: Char,
  +h2: Char,
  +qq: U32,
  +t3: List<&2, Char>,
  +date: T.Date,
  hdo: {D1.prose.date_ok(date) == True{} : Bool}
) -> {t1.wopt(T.when.clock.colon.go(hit, D1.g.two(h1 <> h2 <> Chr{qq} <> t3), t3, date))
  == t1.SP(t1.PTb(D1.abnf.keep(hit, t3)), date, h1 <> h2 <> Chr{qq} <> t3) : T1o}:
  match hit:
    case False{}:
      {==}
    case True{}:
      Equal.trans(T1o, t1.wopt(T.when.clock.mm(T.take.n(2n, t3, 0, True{}), D1.g.two(h1 <> h2 <> Chr{qq} <> t3),
        date)),
        t1.ofc(D1.abnf.time_second(D1.abnf.char_r(D1.abnf.time_minute(D1.ALeft{t3}), 58)),
          zz => cc => ab => t1.fdt(date, zz, cc, ab), D1.g.two(h1 <> h2 <> Chr{qq} <> t3),
          D1.g.two(List.drop(&2, Char, t3, 0n)), D1.g.two(List.drop(&2, Char, t3, 3n)), List.drop(&2, Char, t3,
            5n)),
        t1.SP(t1.PTb(D1.ALeft{t3}), date, h1 <> h2 <> Chr{qq} <> t3),
        t1.C(True{}, zz => cc => ab => t1.fdt(date, zz, cc, ab), t3, D1.g.two(h1 <> h2 <> Chr{qq} <> t3), date,
          zz => ck => t1.z(zz, ck, date)),
        t1.algd(t1.PTb(D1.ALeft{t3}), D1.g.dt.after_frac(List.drop(&2, Char, t3, 5n)),
          D1.prose.clock_ok(T.Clock{D1.g.two(h1 <> h2 <> Chr{qq} <> t3), D1.g.two(List.drop(&2, Char, t3, 0n)),
          D1.g.two(List.drop(&2, Char, t3, 3n)), ""}), date, D1.g.dt.clock(h1 <> h2 <> Chr{qq} <> t3), hdo, {==}))

# the character after the time's hour
def t1.r16(
  +h1: Char,
  +h2: Char,
  rr: List<&2, Char>,
  +date: T.Date,
  hdo: {D1.prose.date_ok(date) == True{} : Bool}
) -> {t1.wopt(T.when.clock.colon(rr, D1.g.two(h1 <> h2 <> rr), date))
  == t1.SP(t1.PTa(D1.ALeft{rr}), date, h1 <> h2 <> rr) : T1o}:
  match rr:
    case []:
      {==}
    case qh <> +t3:
      match qh:
        case Chr{+qq}:
          t1.r17(Char.is_eq(Chr{qq}, ':'), h1, h2, qq, t3, date, hdo)

# the time's hour, after the delimiter
def t1.r15(
  +t2: List<&2, Char>,
  +date: T.Date,
  hdo: {D1.prose.date_ok(date) == True{} : Bool}
) -> {t1.wopt(T.when.clock.of(T.take.n(2n, t2, 0, True{}), date))
  == t1.SP(D1.abnf.partial_time(D1.ALeft{t2}), date, List.drop(&2, Char, t2, 0n)) : T1o}:
  t1.tk2(xs => dd => r => {t1.wopt(T.when.clock.of(dd, date)) == t1.SP(t1.PTa(r), date, List.drop(&2, Char, xs, 0n))
    : T1o}, t2, _xs => {==}, +h1 => +h2 => +rr => _e1 => _e2 => t1.r16(h1, h2, rr, date, hdo))

# the delimiter after a date: T or t, or a space
def t1.r14(
  tee: Bool,
  sp: Bool,
  +t2: List<&2, Char>,
  +date: T.Date,
  hdo: {D1.prose.date_ok(date) == True{} : Bool}
) -> {t1.wopt(T.when.after.sep(tee, sp, date, t2)) == t1.SP(D1.abnf.partial_time(D1.abnf.or_r(
  D1.abnf.keep(tee, t2), D1.abnf.keep(sp, t2))), date, List.drop(&2, Char, t2, 0n)) : T1o}:
  match tee:
    case True{}:
      t1.r15(t2, date, hdo)
    case False{}:
      match sp:
        case True{}:
          t1.r15(t2, date, hdo)
        case False{}:
          {==}

# the ten characters of a date, then the rest of a word
def t1.pre(
  +c1: Char,
  +c2: Char,
  +c3: Char,
  +c4: Char,
  +c5: Char,
  +c6: Char,
  +c7: Char,
  +c8: Char,
  +c9: Char,
  +c10: Char,
  +rest: List<&2, Char>
) -> List<&2, Char>:
  c1 <> c2 <> c3 <> c4 <> c5 <> c6 <> c7 <> c8 <> c9 <> c10 <> rest

# two tests that answered as two bits, joined
def t1.and2(
  +aa: Bool,
  +bb: Bool,
  +xx: Bool,
  +yy: Bool,
  ha: {aa == xx : Bool},
  hb: {bb == yy : Bool}
) -> {Bool.and(aa, bb) == Bool.and(xx, yy) : Bool}:
  Equal.trans(Bool, Bool.and(aa, bb), Bool.and(xx, bb), Bool.and(xx, yy),
    Equal.cong(Bool, Bool, zz => Bool.and(zz, bb), aa, xx, ha),
    Equal.cong(Bool, Bool, zz => Bool.and(xx, zz), bb, yy, hb))

# the number two digits write
def t1.two2(+c1: Char, +c2: Char) -> U32:
  D1.g.two(c1 <> c2 <> [])

# the number four digits write
def t1.four4(+c1: Char, +c2: Char, +c3: Char, +c4: Char) -> U32:
  D1.g.four(c1 <> c2 <> c3 <> c4 <> [])

# the scan's day check, of a year, a month and a day's digits
def t1.dayck(+yy: U32, +mo: U32, +c9: Char, +c10: Char) -> Bool:
  T.bound.rng(t1.two2(c9, c10), 1, T.when.days(yy, mo))

# the date's range, as the scan's two checks answered
def t1.dq(
  +yy: U32,
  +c6: Char,
  +c7: Char,
  +c9: Char,
  +c10: Char,
  +mo_ok: Bool,
  +d_ok: Bool,
  hmo: {T.bound.rng(t1.two2(c6, c7), 1, 12) == mo_ok : Bool},
  hdk: {t1.dayck(yy, t1.two2(c6, c7), c9, c10) == d_ok : Bool}
) -> {D1.prose.date_ok(T.Date{yy, t1.two2(c6, c7), t1.two2(c9, c10)}) == Bool.and(mo_ok, d_ok) : Bool}:
  Equal.trans(Bool, D1.prose.date_ok(T.Date{yy, t1.two2(c6, c7), t1.two2(c9, c10)}),
    Bool.and(T.bound.rng(t1.two2(c6, c7), 1, 12), t1.dayck(yy, t1.two2(c6, c7), c9, c10)), Bool.and(mo_ok, d_ok),
    t1.dok(yy, t1.two2(c6, c7), t1.two2(c9, c10)),
    t1.and2(T.bound.rng(t1.two2(c6, c7), 1, 12), t1.dayck(yy, t1.two2(c6, c7), c9, c10), mo_ok, d_ok, hmo, hdk))

# what follows a date: nothing, or a delimiter and a time
def t1.r13(
  rest: List<&2, Char>,
  +c1: Char,
  +c2: Char,
  +c3: Char,
  +c4: Char,
  +c5: Char,
  +c6: Char,
  +c7: Char,
  +c8: Char,
  +c9: Char,
  +c10: Char,
  hdo: {D1.prose.date_ok(T.Date{t1.four4(c1, c2, c3, c4), t1.two2(c6, c7), t1.two2(c9, c10)}) == True{} : Bool}
) -> {t1.wopt(T.when.after.date(T.Date{t1.four4(c1, c2, c3, c4), t1.two2(c6, c7), t1.two2(c9, c10)}, rest))
  == t1.S3(D1.ALeft{rest}, D1.ANone{}, False{}, t1.pre(c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, rest)) : T1o}:
  match rest:
    case []:
      %Equal.sym(Bool, D1.prose.date_ok(T.Date{t1.four4(c1, c2, c3, c4), t1.two2(c6, c7), t1.two2(c9, c10)}),
        True{}, hdo) : {T1some{T.WDate{T.Date{t1.four4(c1, c2, c3, c4), t1.two2(c6, c7), t1.two2(c9, c10)}}}
        == t1.pk(Bool.and(True{}, _), T.WDate{T.Date{t1.four4(c1, c2, c3, c4), t1.two2(c6, c7), t1.two2(c9, c10)}})
        : T1o}
      {==}
    case sh <> +t2:
      match sh:
        case Chr{+ss}:
          t1.r14(Bool.or(Char.is_eq(Chr{ss}, 'T'), Char.is_eq(Chr{ss}, 't')), Char.is_eq(Chr{ss}, ' '), t2,
            T.Date{t1.four4(c1, c2, c3, c4), t1.two2(c6, c7), t1.two2(c9, c10)}, hdo)

# the date's two range checks: a date out of range denotes nothing
def t1.r12(
  mo_ok: Bool,
  d_ok: Bool,
  +rest: List<&2, Char>,
  +c1: Char,
  +c2: Char,
  +c3: Char,
  +c4: Char,
  +c5: Char,
  +c6: Char,
  +c7: Char,
  +c8: Char,
  +c9: Char,
  +c10: Char,
  +hmo: {T.bound.rng(t1.two2(c6, c7), 1, 12) == mo_ok : Bool},
  +hdk: {t1.dayck(t1.four4(c1, c2, c3, c4), t1.two2(c6, c7), c9, c10) == d_ok : Bool}
) -> {t1.wopt(T.when.date.ok.go(mo_ok, d_ok, t1.four4(c1, c2, c3, c4), t1.two2(c6, c7), t1.two2(c9, c10), rest))
  == t1.S3(D1.ALeft{rest}, D1.ANone{}, False{}, t1.pre(c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, rest)) : T1o}:
  match mo_ok:
    case False{}:
      Equal.sym(T1o, t1.S3(D1.ALeft{rest}, D1.ANone{}, False{}, t1.pre(c1, c2, c3, c4, c5, c6, c7, c8, c9, c10,
        rest)), T1none{}, t1.dbad(t1.G(D1.ALeft{rest}, D1.ANone{}), t1.pre(c1, c2, c3, c4, c5, c6, c7, c8, c9, c10,
        rest), List.drop(&2, Char, rest, 1n), List.is_empty(&2, Char, List.drop(&2, Char, rest, 0n)),
        t1.dq(t1.four4(c1, c2, c3, c4), c6, c7, c9, c10, False{}, d_ok, hmo, hdk)))
    case True{}:
      match d_ok:
        case False{}:
          Equal.sym(T1o, t1.S3(D1.ALeft{rest}, D1.ANone{}, False{}, t1.pre(c1, c2, c3, c4, c5, c6, c7, c8, c9,
            c10, rest)), T1none{}, t1.dbad(t1.G(D1.ALeft{rest}, D1.ANone{}), t1.pre(c1, c2, c3, c4, c5, c6, c7,
            c8, c9, c10, rest), List.drop(&2, Char, rest, 1n), List.is_empty(&2, Char, List.drop(&2, Char, rest, 0n)),
            t1.dq(t1.four4(c1, c2, c3, c4), c6, c7, c9, c10, True{}, False{}, hmo, hdk)))
        case True{}:
          t1.r13(rest, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10,
            t1.dq(t1.four4(c1, c2, c3, c4), c6, c7, c9, c10, True{}, True{}, hmo, hdk))

# the day's two digits, after its dash
def t1.r10(
  hit: Bool,
  +v2: List<&2, Char>,
  +c1: Char,
  +c2: Char,
  +c3: Char,
  +c4: Char,
  +c5: Char,
  +c6: Char,
  +c7: Char,
  +c8: Char
) -> {t1.wopt(T.when.day.go(hit, T.take.n(2n, v2, 0, True{}), t1.four4(c1, c2, c3, c4), t1.two2(c6, c7)))
  == t1.S3(D1.abnf.date_mday(D1.abnf.keep(hit, v2)), D1.ANone{}, False{}, c1 <> c2 <> c3 <> c4 <> c5 <> c6
  <> c7 <> c8 <> v2) : T1o}:
  match hit:
    case False{}:
      {==}
    case True{}:
      t1.tk2(xs => dd => r => {t1.wopt(T.when.day.end(dd, t1.four4(c1, c2, c3, c4), t1.two2(c6, c7)))
        == t1.S3(r, D1.ANone{}, False{}, c1 <> c2 <> c3 <> c4 <> c5 <> c6 <> c7 <> c8 <> xs) : T1o}, v2, _xs => {==},
        +d1 => +d2 => +rest => _e1 => _e2 => t1.r12(T.bound.rng(t1.two2(c6, c7), 1, 12),
          t1.dayck(t1.four4(c1, c2, c3, c4), t1.two2(c6, c7), d1, d2), rest, c1, c2, c3, c4, c5, c6, c7, c8, d1, d2,
          {==}, {==}))

# the dash before the day
def t1.r9(
  ww: List<&2, Char>,
  +c1: Char,
  +c2: Char,
  +c3: Char,
  +c4: Char,
  +c5: Char,
  +c6: Char,
  +c7: Char
) -> {t1.wopt(T.when.day(ww, D1.g.four(c1 <> c2 <> c3 <> c4 <> []), D1.g.two(c6 <> c7 <> [])))
  == t1.S3(D1.abnf.date_mday(D1.abnf.char_r(D1.ALeft{ww}, 45)), D1.ANone{}, False{}, c1 <> c2 <> c3 <> c4
  <> c5 <> c6 <> c7 <> ww) : T1o}:
  match ww:
    case []:
      {==}
    case zh <> +v2:
      match zh:
        case Chr{+z2}:
          t1.r10(Char.is_eq(Chr{z2}, '-'), v2, c1, c2, c3, c4, c5, c6, c7, Chr{z2})

# the month's two digits, after its dash
def t1.r8(
  hit: Bool,
  +vv: List<&2, Char>,
  +c1: Char,
  +c2: Char,
  +c3: Char,
  +c4: Char,
  +c5: Char
) -> {t1.wopt(T.when.month(hit, T.take.n(2n, vv, 0, True{}), D1.g.four(c1 <> c2 <> c3 <> c4 <> [])))
  == t1.S3(D1.abnf.date_mday(D1.abnf.char_r(D1.abnf.date_month(D1.abnf.keep(hit, vv)), 45)), D1.ANone{},
  False{}, c1 <> c2 <> c3 <> c4 <> c5 <> vv) : T1o}:
  match hit:
    case False{}:
      {==}
    case True{}:
      t1.tk2(xs => dd => r => {t1.wopt(T.when.month.go(dd, D1.g.four(c1 <> c2 <> c3 <> c4 <> [])))
        == t1.S3(D1.abnf.date_mday(D1.abnf.char_r(r, 45)), D1.ANone{}, False{}, c1 <> c2 <> c3 <> c4 <> c5 <> xs)
        : T1o}, vv, _xs => {==},
        +m1 => +m2 => +ww => _e1 => _e2 => t1.r9(ww, c1, c2, c3, c4, c5, m1, m2))

# the dash after the year
def t1.r7(
  uu: List<&2, Char>,
  +c1: Char,
  +c2: Char,
  +c3: Char,
  +c4: Char
) -> {t1.wopt(T.when.year.dash(uu, D1.g.four(c1 <> c2 <> c3 <> c4 <> [])))
  == t1.S3(t1.FDc(D1.ALeft{uu}), D1.ANone{}, False{}, c1 <> c2 <> c3 <> c4 <> uu) : T1o}:
  match uu:
    case []:
      {==}
    case zh <> +vv:
      match zh:
        case Chr{+zz}:
          t1.r8(Char.is_eq(Chr{zz}, '-'), vv, c1, c2, c3, c4, Chr{zz})

# the year's fourth digit
def t1.r6(
  dg: Bool,
  +yy: U32,
  +uu: List<&2, Char>,
  +c1: Char,
  +c2: Char,
  +xx: U32
) -> {t1.wopt(T.when.year4(T.take.fin(dg, T.take.acc.d(dg, U32.add(U32.mul(D1.g.two(c1 <> c2 <> []), 10),
  U32.sub(xx, 48)), Chr{yy}), uu))) == t1.S3(t1.FDc(D1.abnf.keep(dg, uu)), D1.ANone{}, False{}, c1 <> c2 <> Chr{xx}
  <> Chr{yy} <> uu) : T1o}:
  match dg:
    case False{}:
      {==}
    case True{}:
      t1.r7(uu, c1, c2, Chr{xx}, Chr{yy})

# the character after the year's third digit
def t1.r5(
  tt: List<&2, Char>,
  +c1: Char,
  +c2: Char,
  +xx: U32
) -> {t1.wopt(T.when.year4(T.take.n(1n, tt, U32.add(U32.mul(D1.g.two(c1 <> c2 <> []), 10), U32.sub(xx, 48)), True{})))
  == t1.S3(t1.FDb(D1.ALeft{tt}), D1.ANone{}, False{}, c1 <> c2 <> Chr{xx} <> tt) : T1o}:
  match tt:
    case []:
      {==}
    case yh <> +uu:
      match yh:
        case Chr{+yy}:
          t1.r6(Char.is_digit(Chr{yy}), yy, uu, c1, c2, xx)

# a digit's value is its code point less 48
def t1.dv(+xx: U32, hd: {Char.is_digit(Chr{xx}) == True{} : Bool}) -> {T.dig.val(Chr{xx}) == U32.sub(xx, 48) : U32}:
  %Equal.sym(Bool, Char.is_digit(Chr{xx}), True{}, hd) : {T.dig.dec(_, xx) == U32.sub(xx, 48) : U32}
  {==}

# a year: its third character is a digit
def t1.r4(
  +tt: List<&2, Char>,
  +c1: Char,
  +c2: Char,
  +xx: U32,
  +hd: {Char.is_digit(Chr{xx}) == True{} : Bool}
) -> {t1.wopt(T.when.year.more(True{}, D1.g.two(c1 <> c2 <> Chr{xx} <> tt), Chr{xx}, tt))
  == t1.S3(t1.FDb(D1.ALeft{tt}), D1.ANone{}, False{}, c1 <> c2 <> Chr{xx} <> tt) : T1o}:
  %Equal.sym(U32, T.dig.val(Chr{xx}), U32.sub(xx, 48), t1.dv(xx, hd)) : {t1.wopt(T.when.year4(T.take.n(1n, tt,
    U32.add(U32.mul(D1.g.two(c1 <> c2 <> Chr{xx} <> tt), 10), _), True{}))) == t1.S3(t1.FDb(D1.ALeft{tt}),
    D1.ANone{}, False{}, c1 <> c2 <> Chr{xx} <> tt) : T1o}
  t1.r5(tt, c1, c2, xx)

# no colon third: a date, when the third character is a digit
def t1.rd(
  digit: Bool,
  +c1: Char,
  +c2: Char,
  +xx: U32,
  +tt: List<&2, Char>,
  +hd: {Char.is_digit(Chr{xx}) == digit : Bool}
) -> {t1.wopt(T.when.branch(False{}, digit, D1.g.two(c1 <> c2 <> Chr{xx} <> tt), Chr{xx}, tt))
  == t1.S3(t1.FDb(D1.abnf.keep(digit, tt)), D1.ANone{}, False{}, c1 <> c2 <> Chr{xx} <> tt) : T1o}:
  match digit:
    case False{}:
      {==}
    case True{}:
      t1.r4(tt, c1, c2, xx, hd)

# a colon third: a time alone, since a colon is no digit
def t1.rt(
  digit: Bool,
  +c1: Char,
  +c2: Char,
  +xx: U32,
  +tt: List<&2, Char>,
  hd: {Char.is_digit(':') == digit : Bool}
) -> {t1.wopt(T.when.branch(True{}, digit, D1.g.two(c1 <> c2 <> Chr{xx} <> tt), Chr{xx}, tt))
  == t1.S3(t1.FDb(D1.abnf.keep(digit, tt)), t1.PTb(D1.ALeft{tt}), True{}, c1 <> c2 <> Chr{xx} <> tt) : T1o}:
  match digit:
    case True{}:
      Eq.bit.absurd(&2, {t1.wopt(T.when.branch(True{}, True{}, D1.g.two(c1 <> c2 <> Chr{xx} <> tt), Chr{xx}, tt))
        == t1.S3(t1.FDb(D1.ALeft{tt}), t1.PTb(D1.ALeft{tt}), True{}, c1 <> c2 <> Chr{xx} <> tt) : T1o}, hd)
    case False{}:
      Equal.trans(T1o, t1.obs(False{}, T.when.clock.mm(T.take.n(2n, tt, 0, True{}),
        D1.g.two(c1 <> c2 <> Chr{xx} <> tt),
        T.Date{0, 1, 1})),
        t1.ofc(D1.abnf.time_second(D1.abnf.char_r(D1.abnf.time_minute(D1.ALeft{tt}), 58)),
          zz => cc => ab => t1.ftm(zz, cc, ab), D1.g.two(c1 <> c2 <> Chr{xx} <> tt),
          D1.g.two(List.drop(&2, Char, tt, 0n)), D1.g.two(List.drop(&2, Char, tt, 3n)), List.drop(&2, Char, tt,
            5n)),
        t1.S3(D1.ANone{}, t1.PTb(D1.ALeft{tt}), True{}, c1 <> c2 <> Chr{xx} <> tt),
        t1.C(False{}, zz => cc => ab => t1.ftm(zz, cc, ab), tt, D1.g.two(c1 <> c2 <> Chr{xx} <> tt), T.Date{0, 1, 1},
          zz => ck => t1.zt(zz, ck)),
        t1.algt(t1.PTb(D1.ALeft{tt}), D1.prose.clock_ok(T.Clock{D1.g.two(c1 <> c2 <> Chr{xx} <> tt),
          D1.g.two(List.drop(&2, Char, tt, 0n)), D1.g.two(List.drop(&2, Char, tt, 3n)), ""}),
          D1.g.dt.clock(c1 <> c2 <> Chr{xx} <> tt), D1.g.dt.after_frac(List.drop(&2, Char, tt, 5n))))

# the third character: a colon, a digit, or neither
def t1.r3(
  colon: Bool,
  +digit: Bool,
  +c1: Char,
  +c2: Char,
  +xx: U32,
  +tt: List<&2, Char>,
  hc: {Char.is_eq(Chr{xx}, ':') == colon : Bool},
  +hd: {Char.is_digit(Chr{xx}) == digit : Bool}
) -> {t1.wopt(T.when.branch(colon, digit, D1.g.two(c1 <> c2 <> Chr{xx} <> tt), Chr{xx}, tt))
  == t1.S3(t1.FDb(D1.abnf.keep(digit, tt)), t1.PTb(D1.abnf.keep(colon, tt)), colon, c1 <> c2 <> Chr{xx} <> tt)
  : T1o}:
  match colon:
    case True{}:
      t1.rt(digit, c1, c2, xx, tt, Equal.trans(Bool, Char.is_digit(':'), Char.is_digit(Chr{xx}), digit,
        Equal.cong(Char, Bool, cc => Char.is_digit(cc), ':', Chr{xx},
          Equal.sym(Char, Chr{xx}, ':', Eq.char_eq_true(Chr{xx}, ':', hc))), hd))
    case False{}:
      t1.rd(digit, c1, c2, xx, tt, hd)

# after the first two digits
def t1.r2(
  +c1: Char,
  +c2: Char,
  rr: List<&2, Char>
) -> {t1.wopt(T.when.after2(T.DigOk{D1.g.two(c1 <> c2 <> rr), rr})) == t1.S3(t1.FDa(D1.ALeft{rr}),
  t1.PTa(D1.ALeft{rr}), D1.abnf.cp(D1.g.dt.third(c1 <> c2 <> rr), 58), c1 <> c2 <> rr) : T1o}:
  match rr:
    case []:
      {==}
    case xh <> +tt:
      match xh:
        case Chr{+xx}:
          t1.r3(Char.is_eq(Chr{xx}, ':'), Char.is_digit(Chr{xx}), c1, c2, xx, tt, {==}, {==})

# the datetime scan reads a word exactly as the grammar says: the datetime a
# word denotes when it matches one of the four date-time rules with every
# field in range, and nothing otherwise
def t1.read(+cs: List<&2, Char>) -> {t1.wopt(T.when.read(cs)) == t1.spec(cs) : T1o}:
  t1.tk2(xs => dd => r => {t1.wopt(T.when.after2(dd)) == t1.S3(t1.FDa(r), t1.PTa(r),
    D1.abnf.cp(D1.g.dt.third(xs), 58), xs) : T1o}, cs, _xs => {==},
    +c1 => +c2 => +rr => _e1 => _e2 => t1.r2(c1, c2, rr))

# The route to the datetime scan. word.val sends a word to the datetime scan
# when it starts with no special's first character, holds a colon or a dash
# after its first character, and holds no e or E; a special word and a
# numeral are never datetimes.

# a bare word's value as a datetime, or none
def t1.gopt(gg: T.Got) -> T1o:
  match gg:
    case T.GotVal{vv}:
      match vv:
        case T.VWhen{ww}:
          T1some{ww}
        case _:
          T1none{}
    case T.GotBad{_w}:
      T1none{}

# the datetime scan's outcome as a bare word's value
def t1.gfw(ww: T.WhenOut) -> {t1.gopt(T.word.from.when(ww)) == t1.wopt(ww) : T1o}:
  match ww:
    case T.WSome{_w}:
      {==}
    case T.WFail{_y}:
      {==}
    case T.WSkip{}:
      {==}

# nan, signed or not, is no datetime
def t1.nw.nan(aa: Bool, bb: Bool, cc: Bool) -> {t1.gopt(T.word.spec.nan(aa, bb, cc)) == T1none{} : T1o}:
  match aa:
    case True{}:
      {==}
    case False{}:
      match bb:
        case True{}:
          {==}
        case False{}:
          match cc:
            case True{}:
              {==}
            case False{}:
              {==}

# nor is inf
def t1.nw.inf(
  aa: Bool,
  bb: Bool,
  cc: Bool,
  +ss: String
) -> {t1.gopt(T.word.spec.inf(aa, bb, cc, ss)) == T1none{} : T1o}:
  match aa:
    case True{}:
      {==}
    case False{}:
      match bb:
        case True{}:
          {==}
        case False{}:
          match cc:
            case True{}:
              {==}
            case False{}:
              t1.nw.nan(T.str.eq(ss, "nan"), T.str.eq(ss, "+nan"), T.str.eq(ss, "-nan"))

# nor true or false
def t1.nw.st(hit: Bool, other: Bool, +ss: String) -> {t1.gopt(T.word.spec.t(hit, other, ss)) == T1none{} : T1o}:
  match hit:
    case True{}:
      {==}
    case False{}:
      match other:
        case True{}:
          {==}
        case False{}:
          t1.nw.inf(T.str.eq(ss, "inf"), T.str.eq(ss, "+inf"), T.str.eq(ss, "-inf"), ss)

# a special word is no datetime
def t1.nw.spec(+ss: String) -> {t1.gopt(T.word.spec(ss)) == T1none{} : T1o}:
  t1.nw.st(T.str.eq(ss, "true"), T.str.eq(ss, "false"), ss)

# an integer checked for its range is no datetime
def t1.nw.rng(
  ok: Bool,
  +sign: T.Sign,
  +digits: String
) -> {t1.gopt(T.num.fin.range(ok, sign, digits)) == T1none{} : T1o}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

# nor a finished integer
def t1.nw.int(
  saw: Bool,
  +sign: T.Sign,
  +digits: String
) -> {t1.gopt(T.num.fin.int(saw, sign, digits)) == T1none{} : T1o}:
  match saw:
    case False{}:
      {==}
    case True{}:
      t1.nw.rng(T.i64.fits(sign, digits), sign, digits)

# nor a prefixed integer
def t1.nw.base(
  signed: Bool,
  +saw: Bool,
  +sign: T.Sign,
  +ds: List<&2, U32>
) -> {t1.gopt(T.num.fin.base(signed, saw, sign, ds)) == T1none{} : T1o}:
  match signed:
    case True{}:
      {==}
    case False{}:
      t1.nw.int(saw, sign, T.dec.text(ds))

# nor a float
def t1.nw.saw(
  saw: Bool,
  +vv: T.Val,
  +ev: {t1.gopt(T.GotVal{vv}) == T1none{} : T1o}
) -> {t1.gopt(T.num.fin.saw(saw, vv)) == T1none{} : T1o}:
  match saw:
    case False{}:
      {==}
    case True{}:
      ev

# nor any numeral, by the kind the scan finished in
def t1.nw.nk(
  nk: T.NK,
  +sign: T.Sign,
  +ds: List<&2, U32>,
  +saw: Bool,
  +why: String,
  +cs: List<&2, Char>
) -> {t1.gopt(T.num.fin.nk(nk, sign, ds, saw, why, cs)) == T1none{} : T1o}:
  match nk:
    case T.NBad{}:
      {==}
    case T.NLead{}:
      {==}
    case T.NSign{}:
      {==}
    case T.NZero{}:
      {==}
    case T.NDig{}:
      t1.nw.int(saw, sign, T.dec.text(ds))
    case T.NBase{}:
      t1.nw.base(T.num.signed(cs), saw, sign, ds)
    case T.NFrac{}:
      t1.nw.saw(saw, T.VFlo{sign, T.word.body(cs)}, {==})
    case T.NExp{}:
      {==}
    case T.NEDig{}:
      t1.nw.saw(saw, T.VFlo{sign, T.word.body(cs)}, {==})

# nor a numeral with a trailing underscore
def t1.nw.us(
  us: Bool,
  +nk: T.NK,
  +sign: T.Sign,
  +ds: List<&2, U32>,
  +saw: Bool,
  +why: String,
  +cs: List<&2, Char>
) -> {t1.gopt(T.num.fin.us(us, nk, sign, ds, saw, why, cs)) == T1none{} : T1o}:
  match us:
    case True{}:
      {==}
    case False{}:
      t1.nw.nk(nk, sign, ds, saw, why, cs)

# a numeral is no datetime
def t1.nw.fin(st: T.Num, +cs: List<&2, Char>) -> {t1.gopt(T.num.fin(st, cs)) == T1none{} : T1o}:
  match st:
    case T.Num{+nk, +sign, _base, +ds, +us, +saw, +why}:
      t1.nw.us(us, nk, sign, ds, saw, why, cs)

# so a numeral token is no datetime
def t1.nw.num(+cs: List<&2, Char>) -> {t1.gopt(T.word.num(cs)) == T1none{} : T1o}:
  t1.nw.fin(T.num.go(cs, T.num.start()), cs)

# the route to the datetime scan or the numeral scan
def t1.rn.date(
  bb: Bool,
  +cs: List<&2, Char>,
  hn: {t1.wopt(T.when.read(cs)) == T1none{} : T1o}
) -> {t1.gopt(T.word.route.date(bb, cs)) == T1none{} : T1o}:
  match bb:
    case True{}:
      Equal.trans(T1o, t1.gopt(T.word.from.when(T.when.read(cs))), t1.wopt(T.when.read(cs)), T1none{},
        t1.gfw(T.when.read(cs)), hn)
    case False{}:
      t1.nw.num(cs)

# a special word's value, or the route
def t1.rn.route(
  gg: T.Got,
  +dd: Bool,
  +cs: List<&2, Char>,
  hn: {t1.wopt(T.when.read(cs)) == T1none{} : T1o},
  hg: {t1.gopt(gg) == T1none{} : T1o}
) -> {t1.gopt(T.word.route(gg, dd, cs)) == T1none{} : T1o}:
  match gg:
    case T.GotVal{_v}:
      hg
    case T.GotBad{_w}:
      t1.rn.date(T.word.as_date(dd, T.word.ee(cs)), cs, hn)

# a word the datetime scan refuses is no datetime, whatever route it takes
def t1.rn(
  sp: Bool,
  +cs: List<&2, Char>,
  hn: {t1.wopt(T.when.read(cs)) == T1none{} : T1o}
) -> {t1.gopt(T.word.val.pick(sp, cs)) == T1none{} : T1o}:
  match sp:
    case True{}:
      t1.rn.route(T.word.spec(String.from_list(cs)), T.word.or(T.word.colon(cs), T.word.dash(cs, True{})), cs, hn,
        t1.nw.spec(String.from_list(cs)))
    case False{}:
      t1.rn.route(T.GotBad{""}, T.word.or(T.word.colon(cs), T.word.dash(cs, True{})), cs, hn, {==})

# a digit is no special word's first character
def t1.dsp(cc: Char, hd: {Char.is_digit(cc) == True{} : Bool}) -> {T.word.special(cc) == False{} : Bool}:
  M3.dg.elim(zz => {T.word.special(zz) == False{} : Bool}, cc, hd,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# a digit is no colon
def t1.dnc(cc: Char, hd: {Char.is_digit(cc) == True{} : Bool}) -> {Char.is_eq(cc, ':') == False{} : Bool}:
  M3.dg.elim(zz => {Char.is_eq(zz, ':') == False{} : Bool}, cc, hd,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# a digit is no dash
def t1.dnd(cc: Char, hd: {Char.is_digit(cc) == True{} : Bool}) -> {Char.is_eq(cc, '-') == False{} : Bool}:
  M3.dg.elim(zz => {Char.is_eq(zz, '-') == False{} : Bool}, cc, hd,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# a digit is no exponent mark
def t1.dee(cc: Char, hd: {Char.is_digit(cc) == True{} : Bool}) -> {T.word.ee.hit(cc) == False{} : Bool}:
  M3.dg.elim(zz => {T.word.ee.hit(zz) == False{} : Bool}, cc, hd,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# either flag, once the second is set
def t1.wort(aa: Bool) -> {T.word.or(aa, True{}) == True{} : Bool}:
  match aa:
    case True{}:
      {==}
    case False{}:
      {==}

# the route's flags: the word starts with no special's first character, and
# holds a colon, or a dash after its first character
def t1.flag(+cs: List<&2, Char>) -> Bool:
  Bool.and(Bool.not(T.word.lead(cs)), T.word.or(T.word.colon(cs), T.word.dash(cs, True{})))

# full-date after its first dash, with the dash's test given
def t1.FDd(hz: Bool, vv: List<&2, Char>) -> D1.ARest:
  D1.abnf.date_mday(D1.abnf.char_r(D1.abnf.date_month(D1.abnf.keep(hz, vv)), 45))

# the date's second dash
def t1.p8(
  hz: Bool,
  +vv: List<&2, Char>,
  hh: {t1.G(t1.FDd(hz, vv), D1.ANone{}) == True{} : Bool}
) -> {T.word.or(hz, T.word.dash(vv, False{})) == True{} : Bool}:
  match hz:
    case True{}:
      {==}
    case False{}:
      Eq.bit.absurd(&2, {T.word.or(False{}, T.word.dash(vv, False{})) == True{} : Bool}, hh)

# the character after the year
def t1.p7(
  uu: List<&2, Char>,
  hh: {t1.G(t1.FDc(D1.ALeft{uu}), D1.ANone{}) == True{} : Bool}
) -> {T.word.dash(uu, False{}) == True{} : Bool}:
  match uu:
    case []:
      Eq.bit.absurd(&2, {T.word.dash([], False{}) == True{} : Bool}, hh)
    case zh <> +vv:
      match zh:
        case Chr{+zz}:
          t1.p8(Char.is_eq(Chr{zz}, '-'), vv, hh)

# the year's fourth digit, which is no dash
def t1.p6(
  dy: Bool,
  +yy: U32,
  +uu: List<&2, Char>,
  hy: {Char.is_digit(Chr{yy}) == dy : Bool},
  hh: {t1.G(t1.FDc(D1.abnf.keep(dy, uu)), D1.ANone{}) == True{} : Bool}
) -> {T.word.or(Char.is_eq(Chr{yy}, '-'), T.word.dash(uu, False{})) == True{} : Bool}:
  match dy:
    case False{}:
      Eq.bit.absurd(&2, {T.word.or(Char.is_eq(Chr{yy}, '-'), T.word.dash(uu, False{})) == True{} : Bool}, hh)
    case True{}:
      %Equal.sym(Bool, Char.is_eq(Chr{yy}, '-'), False{}, t1.dnd(Chr{yy}, hy)) : {T.word.or(_, T.word.dash(uu, False{}))
        == True{} : Bool}
      t1.p7(uu, hh)

# the character after the year's third digit
def t1.p5(
  tt: List<&2, Char>,
  hh: {t1.G(t1.FDb(D1.ALeft{tt}), D1.ANone{}) == True{} : Bool}
) -> {T.word.dash(tt, False{}) == True{} : Bool}:
  match tt:
    case []:
      Eq.bit.absurd(&2, {T.word.dash([], False{}) == True{} : Bool}, hh)
    case yh <> +uu:
      match yh:
        case Chr{+yy}:
          t1.p6(Char.is_digit(Chr{yy}), yy, uu, {==}, hh)

# the third character: a colon, or a digit and then the year's dash
def t1.p4(
  col: Bool,
  dig: Bool,
  +xx: U32,
  +tt: List<&2, Char>,
  hd: {Char.is_digit(Chr{xx}) == dig : Bool},
  hh: {t1.G(t1.FDb(D1.abnf.keep(dig, tt)), t1.PTb(D1.abnf.keep(col, tt))) == True{} : Bool}
) -> {T.word.or(T.word.or(col, T.word.colon(tt)), T.word.or(Char.is_eq(Chr{xx}, '-'), T.word.dash(tt, False{})))
  == True{} : Bool}:
  match col:
    case True{}:
      {==}
    case False{}:
      match dig:
        case False{}:
          Eq.bit.absurd(&2, {T.word.or(T.word.or(False{}, T.word.colon(tt)), T.word.or(Char.is_eq(Chr{xx}, '-'),
            T.word.dash(tt, False{}))) == True{} : Bool}, hh)
        case True{}:
          %Equal.sym(Bool, Char.is_eq(Chr{xx}, '-'), False{}, t1.dnd(Chr{xx}, hd)) : {T.word.or(T.word.colon(tt),
            T.word.or(_, T.word.dash(tt, False{}))) == True{} : Bool}
          %Equal.sym(Bool, T.word.dash(tt, False{}), True{}, t1.p5(tt, hh)) : {T.word.or(T.word.colon(tt), _)
            == True{} : Bool}
          t1.wort(T.word.colon(tt))

# after the first two digits
def t1.p3(
  rr: List<&2, Char>,
  hh: {t1.G(t1.FDa(D1.ALeft{rr}), t1.PTa(D1.ALeft{rr})) == True{} : Bool}
) -> {T.word.or(T.word.colon(rr), T.word.dash(rr, False{})) == True{} : Bool}:
  match rr:
    case []:
      Eq.bit.absurd(&2, {T.word.or(T.word.colon([]), T.word.dash([], False{})) == True{} : Bool}, hh)
    case xh <> +tt:
      match xh:
        case Chr{+xx}:
          t1.p4(Char.is_eq(Chr{xx}, ':'), Char.is_digit(Chr{xx}), xx, tt, {==}, hh)

# the first two characters are digits: no special's, no colon and no dash
def t1.p2(
  +c1: Char,
  +c2: Char,
  +rr: List<&2, Char>,
  +e1: {Char.is_digit(c1) == True{} : Bool},
  +e2: {Char.is_digit(c2) == True{} : Bool},
  hh: {t1.G(t1.FDa(D1.ALeft{rr}), t1.PTa(D1.ALeft{rr})) == True{} : Bool}
) -> {t1.flag(c1 <> c2 <> rr) == True{} : Bool}:
  %Equal.sym(Bool, T.word.special(c1), False{}, t1.dsp(c1, e1)) : {Bool.and(Bool.not(_), T.word.or(T.word.or(
    Char.is_eq(c1, ':'), T.word.or(Char.is_eq(c2, ':'), T.word.colon(rr))), T.word.or(Char.is_eq(c2, '-'),
    T.word.dash(rr, False{})))) == True{} : Bool}
  %Equal.sym(Bool, Char.is_eq(c1, ':'), False{}, t1.dnc(c1, e1)) : {Bool.and(True{}, T.word.or(T.word.or(
    _, T.word.or(Char.is_eq(c2, ':'), T.word.colon(rr))), T.word.or(Char.is_eq(c2, '-'),
    T.word.dash(rr, False{})))) == True{} : Bool}
  %Equal.sym(Bool, Char.is_eq(c2, ':'), False{}, t1.dnc(c2, e2)) : {T.word.or(T.word.or(_, T.word.colon(rr)),
    T.word.or(Char.is_eq(c2, '-'), T.word.dash(rr, False{}))) == True{} : Bool}
  %Equal.sym(Bool, Char.is_eq(c2, '-'), False{}, t1.dnd(c2, e2)) : {T.word.or(T.word.colon(rr),
    T.word.or(_, T.word.dash(rr, False{}))) == True{} : Bool}
  t1.p3(rr, hh)

# a word that matches the grammar is routed to the datetime scan by its first
# characters
def t1.pfx(+cs: List<&2, Char>, hdt: {D1.abnf.date_time(cs) == True{} : Bool}) -> {t1.flag(cs) == True{} : Bool}:
  t1.tk2(xs => _dd => r => ({t1.G(t1.FDa(r), t1.PTa(r)) == True{} : Bool} -> {t1.flag(xs) == True{} : Bool}), cs,
    +xs => hh => Eq.bit.absurd(&2, {t1.flag(xs) == True{} : Bool}, hh),
    +c1 => +c2 => +rr => +e1 => +e2 => hh => t1.p2(c1, c2, rr, e1, e2, hh))(hdt)

# No e or E. Every character a date-time rule takes is a digit or one of
# - : . + T t Z z and the space, none of them an exponent mark, so a word
# with one is left with one by every rule, and no rule matches it whole.

# what a rule left of a word still holds an exponent mark, or it matched
# nothing
def t1.ek(rr: D1.ARest) -> Bool:
  match rr:
    case D1.ALeft{cs}:
      T.word.ee(cs)
    case D1.ANone{}:
      True{}

# a character that is no exponent mark leaves the mark in the rest
def t1.e.step(
  +cc: Char,
  +tt: List<&2, Char>,
  hc: {T.word.ee.hit(cc) == False{} : Bool},
  hh: {T.word.ee(cc <> tt) == True{} : Bool}
) -> {T.word.ee(tt) == True{} : Bool}:
  Equal.trans(Bool, T.word.ee(tt), T.word.or(T.word.ee.hit(cc), T.word.ee(tt)), True{},
    Equal.cong(Bool, Bool, bb => T.word.or(bb, T.word.ee(tt)), False{}, T.word.ee.hit(cc),
      Equal.sym(Bool, T.word.ee.hit(cc), False{}, hc)), hh)

# a DIGIT taken
def t1.e.dr0(
  dg: Bool,
  +xx: U32,
  +tt: List<&2, Char>,
  hd: {Char.is_digit(Chr{xx}) == dg : Bool},
  hh: {T.word.ee(Chr{xx} <> tt) == True{} : Bool}
) -> {t1.ek(D1.abnf.keep(dg, tt)) == True{} : Bool}:
  match dg:
    case False{}:
      {==}
    case True{}:
      t1.e.step(Chr{xx}, tt, t1.dee(Chr{xx}, hd), hh)

# DIGIT keeps the mark
def t1.e.dr(rr: D1.ARest, hh: {t1.ek(rr) == True{} : Bool}) -> {t1.ek(D1.abnf.digit_r(rr)) == True{} : Bool}:
  match rr:
    case D1.ANone{}:
      {==}
    case D1.ALeft{cs}:
      match cs:
        case []:
          {==}
        case xh <> +tt:
          match xh:
            case Chr{+xx}:
              t1.e.dr0(Char.is_digit(Chr{xx}), xx, tt, {==}, hh)

# two DIGITs keep it
def t1.e.d2(
  +rr: D1.ARest,
  hh: {t1.ek(rr) == True{} : Bool}
) -> {t1.ek(D1.abnf.digit_r(D1.abnf.digit_r(rr))) == True{} : Bool}:
  t1.e.dr(D1.abnf.digit_r(rr), t1.e.dr(rr, hh))

# a character with code point n taken, n no exponent mark
def t1.e.cr0(
  bb: Bool,
  +xx: U32,
  +nn: U32,
  +tt: List<&2, Char>,
  hb: {U32.is_eq(xx, nn) == bb : Bool},
  hn: {T.word.ee.hit(Chr{nn}) == False{} : Bool},
  hh: {T.word.ee(Chr{xx} <> tt) == True{} : Bool}
) -> {t1.ek(D1.abnf.keep(bb, tt)) == True{} : Bool}:
  match bb:
    case False{}:
      {==}
    case True{}:
      t1.e.step(Chr{xx}, tt, Equal.trans(Bool, T.word.ee.hit(Chr{xx}), T.word.ee.hit(Chr{nn}), False{},
        Equal.cong(Char, Bool, cc => T.word.ee.hit(cc), Chr{xx}, Chr{nn}, Eq.u32_eq(xx, nn, hb)), hn), hh)

# such a character keeps the mark
def t1.e.cr(
  rr: D1.ARest,
  +nn: U32,
  hn: {T.word.ee.hit(Chr{nn}) == False{} : Bool},
  hh: {t1.ek(rr) == True{} : Bool}
) -> {t1.ek(D1.abnf.char_r(rr, nn)) == True{} : Bool}:
  match rr:
    case D1.ANone{}:
      {==}
    case D1.ALeft{cs}:
      match cs:
        case []:
          {==}
        case xh <> +tt:
          match xh:
            case Chr{+xx}:
              t1.e.cr0(U32.is_eq(xx, nn), xx, nn, tt, {==}, hn, hh)

# a letter in either case taken
def t1.e.lr0(
  bu: Bool,
  bl: Bool,
  +xx: U32,
  +up: U32,
  +low: U32,
  +tt: List<&2, Char>,
  hbu: {U32.is_eq(xx, up) == bu : Bool},
  hbl: {U32.is_eq(xx, low) == bl : Bool},
  hu: {T.word.ee.hit(Chr{up}) == False{} : Bool},
  hl: {T.word.ee.hit(Chr{low}) == False{} : Bool},
  +hh: {T.word.ee(Chr{xx} <> tt) == True{} : Bool}
) -> {t1.ek(D1.abnf.keep(Bool.or(bu, bl), tt)) == True{} : Bool}:
  match bu:
    case True{}:
      t1.e.cr0(True{}, xx, up, tt, hbu, hu, hh)
    case False{}:
      t1.e.cr0(bl, xx, low, tt, hbl, hl, hh)

# such a letter keeps the mark
def t1.e.lr(
  rr: D1.ARest,
  +up: U32,
  +low: U32,
  hu: {T.word.ee.hit(Chr{up}) == False{} : Bool},
  hl: {T.word.ee.hit(Chr{low}) == False{} : Bool},
  hh: {t1.ek(rr) == True{} : Bool}
) -> {t1.ek(D1.abnf.letter_r(rr, up, low)) == True{} : Bool}:
  match rr:
    case D1.ANone{}:
      {==}
    case D1.ALeft{cs}:
      match cs:
        case []:
          {==}
        case xh <> +tt:
          match xh:
            case Chr{+xx}:
              t1.e.lr0(U32.is_eq(xx, up), U32.is_eq(xx, low), xx, up, low, tt, {==}, {==}, hu, hl, hh)

# either of two alternatives keeps it
def t1.e.or(
  aa: D1.ARest,
  +bb: D1.ARest,
  ha: {t1.ek(aa) == True{} : Bool},
  hb: {t1.ek(bb) == True{} : Bool}
) -> {t1.ek(D1.abnf.or_r(aa, bb)) == True{} : Bool}:
  match aa:
    case D1.ALeft{_c}:
      ha
    case D1.ANone{}:
      hb

# one of the leading digits dropped
def t1.e.dd0(
  dg: Bool,
  +yy: U32,
  +uu: List<&2, Char>,
  hd: {Char.is_digit(Chr{yy}) == dg : Bool},
  +hh: {T.word.ee(Chr{yy} <> uu) == True{} : Bool},
  ih: {T.word.ee(uu) == True{} : Bool} -> {T.word.ee(D1.abnf.drop_digits(uu)) == True{} : Bool}
) -> {T.word.ee(D1.abnf.drop_digits.pick(dg, Chr{yy}, uu, D1.abnf.drop_digits(uu))) == True{} : Bool}:
  match dg:
    case True{}:
      ih(t1.e.step(Chr{yy}, uu, t1.dee(Chr{yy}, hd), hh))
    case False{}:
      hh

# dropping the leading digits keeps it
def t1.e.dd(
  tt: List<&2, Char>,
  +hh: {T.word.ee(tt) == True{} : Bool}
) -> {T.word.ee(D1.abnf.drop_digits(tt)) == True{} : Bool}:
  match tt:
    case []:
      hh
    case yh <> +uu:
      match yh:
        case Chr{+yy}:
          t1.e.dd0(Char.is_digit(Chr{yy}), yy, uu, {==}, hh, hu => t1.e.dd(uu, hu))

# a fraction's first digit
def t1.e.d10(
  dg: Bool,
  +xx: U32,
  +tt: List<&2, Char>,
  hd: {Char.is_digit(Chr{xx}) == dg : Bool},
  hh: {T.word.ee(Chr{xx} <> tt) == True{} : Bool}
) -> {t1.ek(D1.abnf.keep(dg, D1.abnf.drop_digits(tt))) == True{} : Bool}:
  match dg:
    case False{}:
      {==}
    case True{}:
      t1.e.dd(tt, t1.e.step(Chr{xx}, tt, t1.dee(Chr{xx}, hd), hh))

# 1*DIGIT keeps it
def t1.e.d1(rr: D1.ARest, hh: {t1.ek(rr) == True{} : Bool}) -> {t1.ek(D1.abnf.digits1_r(rr)) == True{} : Bool}:
  match rr:
    case D1.ANone{}:
      {==}
    case D1.ALeft{cs}:
      match cs:
        case []:
          {==}
        case xh <> +tt:
          match xh:
            case Chr{+xx}:
              t1.e.d10(Char.is_digit(Chr{xx}), xx, tt, {==}, hh)

# a dot, or no fraction
def t1.e.os0(
  dot: Bool,
  +xx: U32,
  +tt: List<&2, Char>,
  +hh: {T.word.ee(Chr{xx} <> tt) == True{} : Bool}
) -> {t1.ek(D1.abnf.opt_secfrac.pick(dot, Chr{xx} <> tt)) == True{} : Bool}:
  match dot:
    case False{}:
      hh
    case True{}:
      t1.e.d1(D1.abnf.char_r(D1.ALeft{Chr{xx} <> tt}, 46), t1.e.cr(D1.ALeft{Chr{xx} <> tt}, 46, {==}, hh))

# [ time-secfrac ] keeps it
def t1.e.os(rr: D1.ARest, hh: {t1.ek(rr) == True{} : Bool}) -> {t1.ek(D1.abnf.opt_secfrac(rr)) == True{} : Bool}:
  match rr:
    case D1.ANone{}:
      {==}
    case D1.ALeft{cs}:
      match cs:
        case []:
          hh
        case xh <> +tt:
          match xh:
            case Chr{+xx}:
              t1.e.os0(D1.abnf.cp(Chr{xx}, 46), xx, tt, hh)

# full-date keeps it
def t1.e.fd(+rr: D1.ARest, hh: {t1.ek(rr) == True{} : Bool}) -> {t1.ek(D1.abnf.full_date(rr)) == True{} : Bool}:
  t1.e.d2(D1.abnf.char_r(D1.abnf.date_month(D1.abnf.char_r(D1.abnf.date_fullyear(rr), 45)), 45),
    t1.e.cr(D1.abnf.date_month(D1.abnf.char_r(D1.abnf.date_fullyear(rr), 45)), 45, {==},
    t1.e.d2(D1.abnf.char_r(D1.abnf.date_fullyear(rr), 45), t1.e.cr(D1.abnf.date_fullyear(rr), 45, {==},
    t1.e.d2(D1.abnf.digit_r(D1.abnf.digit_r(rr)), t1.e.d2(rr, hh))))))

# partial-time keeps it
def t1.e.pt(+rr: D1.ARest, hh: {t1.ek(rr) == True{} : Bool}) -> {t1.ek(D1.abnf.partial_time(rr)) == True{} : Bool}:
  t1.e.os(D1.abnf.time_second(D1.abnf.char_r(D1.abnf.time_minute(D1.abnf.char_r(D1.abnf.time_hour(rr), 58)),
    58)),
    t1.e.d2(D1.abnf.char_r(D1.abnf.time_minute(D1.abnf.char_r(D1.abnf.time_hour(rr), 58)), 58),
    t1.e.cr(D1.abnf.time_minute(D1.abnf.char_r(D1.abnf.time_hour(rr), 58)), 58, {==},
    t1.e.d2(D1.abnf.char_r(D1.abnf.time_hour(rr), 58), t1.e.cr(D1.abnf.time_hour(rr), 58, {==},
    t1.e.d2(rr, hh))))))

# time-delim keeps it
def t1.e.td(+rr: D1.ARest, +hh: {t1.ek(rr) == True{} : Bool}) -> {t1.ek(D1.abnf.time_delim(rr)) == True{} : Bool}:
  t1.e.or(D1.abnf.letter_r(rr, 84, 116), D1.abnf.char_r(rr, 32), t1.e.lr(rr, 84, 116, {==}, {==}, hh),
    t1.e.cr(rr, 32, {==}, hh))

# time-offset keeps it
def t1.e.to(+rr: D1.ARest, +hh: {t1.ek(rr) == True{} : Bool}) -> {t1.ek(D1.abnf.time_offset(rr)) == True{} : Bool}:
  t1.e.or(D1.abnf.letter_r(rr, 90, 122), D1.abnf.time_numoffset(rr), t1.e.lr(rr, 90, 122, {==}, {==}, hh),
    t1.e.d2(D1.abnf.char_r(D1.abnf.time_hour(D1.abnf.or_r(D1.abnf.char_r(rr, 43), D1.abnf.char_r(rr, 45))),
      58),
      t1.e.cr(D1.abnf.time_hour(D1.abnf.or_r(D1.abnf.char_r(rr, 43), D1.abnf.char_r(rr, 45))), 58, {==},
      t1.e.d2(D1.abnf.or_r(D1.abnf.char_r(rr, 43), D1.abnf.char_r(rr, 45)), t1.e.or(D1.abnf.char_r(rr, 43),
      D1.abnf.char_r(rr, 45), t1.e.cr(rr, 43, {==}, hh), t1.e.cr(rr, 45, {==}, hh))))))

# a rule's match that leaves an exponent mark is no whole-word match
def t1.e.all(rr: D1.ARest, hh: {t1.ek(rr) == True{} : Bool}) -> {D1.abnf.all_r(rr) == False{} : Bool}:
  match rr:
    case D1.ANone{}:
      {==}
    case D1.ALeft{cs}:
      match cs:
        case []:
          Eq.bit.absurd(&2, {D1.abnf.all_r(D1.ALeft{[]}) == False{} : Bool}, hh)
        case _h <> _t:
          {==}

# four alternatives that each answered False
def t1.or4f(
  +aa: Bool,
  +bb: Bool,
  +cc: Bool,
  +dd: Bool,
  ha: {aa == False{} : Bool},
  hb: {bb == False{} : Bool},
  hc: {cc == False{} : Bool},
  hd: {dd == False{} : Bool}
) -> {Bool.or(aa, Bool.or(bb, Bool.or(cc, dd))) == False{} : Bool}:
  %Equal.sym(Bool, aa, False{}, ha) : {Bool.or(_, Bool.or(bb, Bool.or(cc, dd))) == False{} : Bool}
  %Equal.sym(Bool, bb, False{}, hb) : {Bool.or(_, Bool.or(cc, dd)) == False{} : Bool}
  %Equal.sym(Bool, cc, False{}, hc) : {Bool.or(_, dd) == False{} : Bool}
  hd

# a word with an exponent mark matches no date-time rule
def t1.e.dt(+cs: List<&2, Char>, +hh: {T.word.ee(cs) == True{} : Bool}) -> {D1.abnf.date_time(cs) == False{} : Bool}:
  t1.or4f(D1.abnf.all_r(D1.abnf.offset_date_time(D1.ALeft{cs})),
    D1.abnf.all_r(D1.abnf.local_date_time(D1.ALeft{cs})), D1.abnf.all_r(D1.abnf.local_date(D1.ALeft{cs})),
    D1.abnf.all_r(D1.abnf.local_time(D1.ALeft{cs})),
    t1.e.all(D1.abnf.offset_date_time(D1.ALeft{cs}), t1.e.to(D1.abnf.partial_time(D1.abnf.time_delim(
      D1.abnf.full_date(D1.ALeft{cs}))), t1.e.pt(D1.abnf.time_delim(D1.abnf.full_date(D1.ALeft{cs})),
      t1.e.td(D1.abnf.full_date(D1.ALeft{cs}), t1.e.fd(D1.ALeft{cs}, hh))))),
    t1.e.all(D1.abnf.local_date_time(D1.ALeft{cs}), t1.e.pt(D1.abnf.time_delim(D1.abnf.full_date(
      D1.ALeft{cs})), t1.e.td(D1.abnf.full_date(D1.ALeft{cs}), t1.e.fd(D1.ALeft{cs}, hh)))),
    t1.e.all(D1.abnf.local_date(D1.ALeft{cs}), t1.e.fd(D1.ALeft{cs}, hh)),
    t1.e.all(D1.abnf.local_time(D1.ALeft{cs}), t1.e.pt(D1.ALeft{cs}, hh)))

# so a word that matches holds no exponent mark
def t1.noe.go(
  ee: Bool,
  +cs: List<&2, Char>,
  he: {T.word.ee(cs) == ee : Bool},
  hdt: {D1.abnf.date_time(cs) == True{} : Bool}
) -> {T.word.ee(cs) == False{} : Bool}:
  match ee:
    case False{}:
      he
    case True{}:
      Eq.bit.absurd(&2, {T.word.ee(cs) == False{} : Bool}, Equal.trans(Bool, False{}, D1.abnf.date_time(cs), True{},
        Equal.sym(Bool, D1.abnf.date_time(cs), False{}, t1.e.dt(cs, he)), hdt))

# a word that matches is routed to the datetime scan
def t1.rs(
  +cs: List<&2, Char>,
  +hdt: {D1.abnf.date_time(cs) == True{} : Bool}
) -> {T.word.val(cs) == T.word.from.when(T.when.read(cs)) : T.Got}:
  %Equal.sym(Bool, T.word.lead(cs), False{}, Eq.not.true(T.word.lead(cs), Eq.and.left(Bool.not(T.word.lead(cs)),
    T.word.or(T.word.colon(cs), T.word.dash(cs, True{})), t1.pfx(cs, hdt)))) : {T.word.val.pick(_, cs)
    == T.word.from.when(T.when.read(cs)) : T.Got}
  %Equal.sym(Bool, T.word.or(T.word.colon(cs), T.word.dash(cs, True{})), True{}, Eq.and.right(Bool.not(T.word.lead(cs)),
    T.word.or(T.word.colon(cs), T.word.dash(cs, True{})), t1.pfx(cs, hdt))) : {T.word.route.date(T.word.as_date(_,
    T.word.ee(cs)), cs) == T.word.from.when(T.when.read(cs)) : T.Got}
  %Equal.sym(Bool, T.word.ee(cs), False{}, t1.noe.go(T.word.ee(cs), cs, {==}, hdt)) : {T.word.route.date(
    T.word.as_date(True{}, _), cs) == T.word.from.when(T.when.read(cs)) : T.Got}
  {==}

# a bare word's value as a datetime is what the grammar says
def t1.fin(
  bb: Bool,
  +cs: List<&2, Char>,
  +hb: {Bool.and(D1.abnf.date_time(cs), D1.prose.date_time_in_range(cs)) == bb : Bool}
) -> {t1.gopt(T.word.val(cs)) == t1.spec(cs) : T1o}:
  match bb:
    case False{}:
      Equal.trans(T1o, t1.gopt(T.word.val(cs)), T1none{}, t1.spec(cs),
        t1.rn(T.word.lead(cs), cs, Equal.trans(T1o, t1.wopt(T.when.read(cs)), t1.spec(cs), T1none{}, t1.read(cs),
          Equal.cong(Bool, T1o, xx => t1.pk(xx, D1.g.dt.when(cs)), Bool.and(D1.abnf.date_time(cs),
          D1.prose.date_time_in_range(cs)), False{}, hb))),
        Equal.sym(T1o, t1.spec(cs), T1none{}, Equal.cong(Bool, T1o, xx => t1.pk(xx, D1.g.dt.when(cs)),
          Bool.and(D1.abnf.date_time(cs), D1.prose.date_time_in_range(cs)), False{}, hb)))
    case True{}:
      Equal.trans(T1o, t1.gopt(T.word.val(cs)), t1.gopt(T.word.from.when(T.when.read(cs))), t1.spec(cs),
        Equal.cong(T.Got, T1o, gg => t1.gopt(gg), T.word.val(cs), T.word.from.when(T.when.read(cs)),
          t1.rs(cs, Eq.and.left(D1.abnf.date_time(cs), D1.prose.date_time_in_range(cs), hb))),
        Equal.trans(T1o, t1.gopt(T.word.from.when(T.when.read(cs))), t1.wopt(T.when.read(cs)), t1.spec(cs),
          t1.gfw(T.when.read(cs)), t1.read(cs)))

# the classifier: a bare word reads as a datetime exactly as the grammar says
def t1.core(+cs: List<&2, Char>) -> {t1.gopt(T.word.val(cs)) == t1.spec(cs) : T1o}:
  t1.fin(Bool.and(D1.abnf.date_time(cs), D1.prose.date_time_in_range(cs)), cs, {==})

# The laws. The classifier compares the word's outcome with a datetime; both
# sides are options, the scan's (t1.gopt) and the grammar's (t1.spec).

# an option compared with a datetime
def t1.oeq(oo: T1o, ww: T.When) -> Bool:
  match oo:
    case T1some{vv}:
      D2.when.eq(ww, vv)
    case T1none{}:
      False{}

# the law's comparison is the option's
def t1.go(gg: T.Got, +ww: T.When) -> {L1.t1.got_when(gg, ww) == t1.oeq(t1.gopt(gg), ww) : Bool}:
  match gg:
    case T.GotVal{vv}:
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
    case T.GotBad{_w}:
      {==}

# the grammar's option compared with a datetime
def t1.op(
  bb: Bool,
  +vv: T.When,
  +ww: T.When
) -> {t1.oeq(t1.pk(bb, vv), ww) == Bool.and(bb, D2.when.eq(ww, vv)) : Bool}:
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# the scan and the grammar agree on every word (t1.core)
def L1.date_time_word(cs, w):
  Equal.trans(Bool, L1.t1.got_when(T.word.val(cs), w), t1.oeq(t1.gopt(T.word.val(cs)), w),
    Bool.and(Bool.and(D1.abnf.date_time(cs), D1.prose.date_time_in_range(cs)), D2.when.eq(w, D1.g.dt.when(cs))),
    t1.go(T.word.val(cs), w),
    Equal.trans(Bool, t1.oeq(t1.gopt(T.word.val(cs)), w), t1.oeq(t1.spec(cs), w),
      Bool.and(Bool.and(D1.abnf.date_time(cs), D1.prose.date_time_in_range(cs)), D2.when.eq(w,
      D1.g.dt.when(cs))),
      Equal.cong(T1o, Bool, oo => t1.oeq(oo, w), t1.gopt(T.word.val(cs)), t1.spec(cs), t1.core(cs)),
      t1.op(Bool.and(D1.abnf.date_time(cs), D1.prose.date_time_in_range(cs)), D1.g.dt.when(cs), w)))
