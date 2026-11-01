# a refused bare word says why, from the sign, base, digit and exponent it met
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/KeyNameIsItsCharacters.bend as L1

# KEY-3: a bare word the scanner refuses is refused with a reason
# (bare_word_refusal_says_why). A datetime's refusals are literal reasons or
# pass one on (kn.wne); a numeral's scan keeps a reason once it fails
# (kn.ok); and word.val routes to one of the two or gives a value.

# a datetime's result says why when it refuses
def kn.wne(ww: T.WhenOut) -> Bool:
  match ww:
    case T.WFail{why}:
      Bool.not(String.is_empty(why))
    case _w:
      True{}

# a failed numeral scan
def kn.nb(nk: T.NK) -> Bool:
  match nk:
    case T.NBad{}:
      True{}
    case _n:
      False{}

# a numeral's scan says why once it fails
def kn.ok2(nk: T.NK, +why: String) -> Bool:
  match nk:
    case T.NBad{}:
      Bool.not(String.is_empty(why))
    case _n:
      True{}

# a numeral's scan state says why once it fails
def kn.ok(st: T.Num) -> Bool:
  match st:
    case T.Num{nk, _s, _b, _d, _u, _w, why}:
      kn.ok2(nk, why)

# a digit joined to a scan that has not failed
def kn.dok(
  nk: T.NK,
  +sign: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +enk: {kn.nb(nk) == False{} : Bool}
) -> {kn.ok(T.Num{nk, sign, base, ds, False{}, True{}, ""}) == True{} : Bool}:
  match nk:
    case T.NBad{}:
      Eq.bit.absurd2(&2, {kn.ok(T.Num{T.NBad{}, sign, base, ds, False{}, True{}, ""}) == True{} : Bool}, enk)
    case T.NLead{}:
      {==}
    case T.NSign{}:
      {==}
    case T.NZero{}:
      {==}
    case T.NDig{}:
      {==}
    case T.NBase{}:
      {==}
    case T.NFrac{}:
      {==}
    case T.NExp{}:
      {==}
    case T.NEDig{}:
      {==}

# a base prefix read
def kn.base(+st: T.Num, +bb: U32) -> {kn.ok(T.num.base(st, bb)) == True{} : Bool}:
  match st:
    case T.Num{_k, _s, _b, _d, _u, _w, _y}:
      {==}

# an exponent's sign read
def kn.expsign(+st: T.Num) -> {kn.ok(T.num.exp.sign(st)) == True{} : Bool}:
  match st:
    case T.Num{_k, _s, _b, _d, _u, _w, _y}:
      {==}

# a finished local datetime, or one with a zone still to read
def kw2.done(
  +_date: T.Date,
  +_clock: T.Clock,
  +ww: T.When
) -> {kn.wne(T.when.done(_date, _clock, ww)) == True{} : Bool}:
  {==}

# Z ends the token
def kw2.zone.z(
  +tt: List<&2, Char>,
  +clock: T.Clock,
  +date: T.Date
) -> {kn.wne(T.when.zone.z(tt, clock, date)) == True{} : Bool}:
  match tt:
    case []:
      {==}
    case _ <> _:
      {==}

# the offset minute is in range
def kw2.zone.mm.ok2(
  +mi_ok: Bool,
  +sign: T.Sign,
  +hh: U32,
  +mi: U32,
  +clock: T.Clock,
  +date: T.Date
) -> {kn.wne(T.when.zone.mm.ok2(mi_ok, sign, hh, mi, clock, date)) == True{} : Bool}:
  match mi_ok:
    case False{}:
      {==}
    case True{}:
      {==}

# the offset fields are in range
def kw2.zone.mm.ok(
  +h_ok: Bool,
  +mi_ok: Bool,
  +sign: T.Sign,
  +hh: U32,
  +mi: U32,
  +clock: T.Clock,
  +date: T.Date
) -> {kn.wne(T.when.zone.mm.ok(h_ok, mi_ok, sign, hh, mi, clock, date)) == True{} : Bool}:
  match h_ok:
    case False{}:
      {==}
    case True{}:
      kw2.zone.mm.ok2(mi_ok, sign, hh, mi, clock, date)

# nothing follows an offset, and its fields are in range
def kw2.zone.mm.end(
  +cs: List<&2, Char>,
  +h_ok: Bool,
  +mi_ok: Bool,
  +sign: T.Sign,
  +hh: U32,
  +mi: U32,
  +clock: T.Clock,
  +date: T.Date
) -> {kn.wne(T.when.zone.mm.end(cs, h_ok, mi_ok, sign, hh, mi, clock, date)) == True{} : Bool}:
  match cs:
    case []:
      kw2.zone.mm.ok(h_ok, mi_ok, sign, hh, mi, clock, date)
    case _ <> _:
      {==}

# the offset minute is in range
def kw2.zone.mm.go(
  +dd: T.Dig,
  +sign: T.Sign,
  +hh: U32,
  +clock: T.Clock,
  +date: T.Date
) -> {kn.wne(T.when.zone.mm.go(dd, sign, hh, clock, date)) == True{} : Bool}:
  match dd:
    case T.DigBad{}:
      {==}
    case T.DigOk{+n, cs}:
      kw2.zone.mm.end(cs, T.bound.rng(hh, 0, 23), T.bound.rng(n, 0, 59), sign, hh, n, clock, date)

# the offset minute
def kw2.zone.mm(
  +hit: Bool,
  +dd: T.Dig,
  +sign: T.Sign,
  +hh: U32,
  +clock: T.Clock,
  +date: T.Date
) -> {kn.wne(T.when.zone.mm(hit, dd, sign, hh, clock, date)) == True{} : Bool}:
  match hit:
    case False{}:
      {==}
    case True{}:
      kw2.zone.mm.go(dd, sign, hh, clock, date)

# the colon in an offset
def kw2.zone.hh.colon(
  +cs: List<&2, Char>,
  +sign: T.Sign,
  +hh: U32,
  +clock: T.Clock,
  +date: T.Date
) -> {kn.wne(T.when.zone.hh.colon(cs, sign, hh, clock, date)) == True{} : Bool}:
  match cs:
    case []:
      {==}
    case +c <> t:
      kw2.zone.mm(Char.is_eq(c, ':'), T.take.n(2n, t, 0, True{}), sign, hh, clock, date)

# the offset hour
def kw2.zone.hh(
  +dd: T.Dig,
  +sign: T.Sign,
  +clock: T.Clock,
  +date: T.Date
) -> {kn.wne(T.when.zone.hh(dd, sign, clock, date)) == True{} : Bool}:
  match dd:
    case T.DigBad{}:
      {==}
    case T.DigOk{+n, +cs}:
      kw2.zone.hh.colon(cs, sign, n, clock, date)

# HH:MM of a numeric offset
def kw2.zone.off(
  +sign: T.Sign,
  +tt: List<&2, Char>,
  +clock: T.Clock,
  +date: T.Date
) -> {kn.wne(T.when.zone.off(sign, tt, clock, date)) == True{} : Bool}:
  kw2.zone.hh(T.take.n(2n, tt, 0, True{}), sign, clock, date)

# a minus starts a numeric offset
def kw2.zone.minus(
  +minus: Bool,
  +tt: List<&2, Char>,
  +clock: T.Clock,
  +date: T.Date
) -> {kn.wne(T.when.zone.minus(minus, tt, clock, date)) == True{} : Bool}:
  match minus:
    case True{}:
      kw2.zone.off(T.Minus{}, tt, clock, date)
    case False{}:
      {==}

# a plus or a minus starts a numeric offset
def kw2.zone.sign(
  +plus: Bool,
  +minus: Bool,
  +tt: List<&2, Char>,
  +clock: T.Clock,
  +date: T.Date
) -> {kn.wne(T.when.zone.sign(plus, minus, tt, clock, date)) == True{} : Bool}:
  match plus:
    case True{}:
      kw2.zone.off(T.Plus{}, tt, clock, date)
    case False{}:
      kw2.zone.minus(minus, tt, clock, date)

# Z, or a signed numeric offset
def kw2.zone.go(
  +zee: Bool,
  +plus: Bool,
  +minus: Bool,
  +tt: List<&2, Char>,
  +clock: T.Clock,
  +date: T.Date
) -> {kn.wne(T.when.zone.go(zee, plus, minus, tt, clock, date)) == True{} : Bool}:
  match zee:
    case True{}:
      kw2.zone.z(tt, clock, date)
    case False{}:
      kw2.zone.sign(plus, minus, tt, clock, date)

# a zone, or the end of a local datetime
def kw2.zone(
  +cs: List<&2, Char>,
  +clock: T.Clock,
  +date: T.Date
) -> {kn.wne(T.when.zone(cs, clock, date)) == True{} : Bool}:
  match cs:
    case []:
      {==}
    case +c <> t:
      kw2.zone.go(Bool.or(Char.is_eq(c, 'Z'), Char.is_eq(c, 'z')), Char.is_eq(c, '+'), Char.is_eq(c, '-'), t, clock,
        date)

# the fraction must hold a digit
def kw2.frac.end.go(
  +some: Bool,
  +rev: List<&2, Char>,
  +clock: T.Clock,
  +date: T.Date,
  +rest: List<&2, Char>
) -> {kn.wne(T.when.frac.end.go(some, rev, clock, date, rest)) == True{} : Bool}:
  match some:
    case False{}:
      {==}
    case True{}:
      kw2.zone(rest, T.clock.with(clock, T.buf.str.go(rev, "")), date)

# the fraction must hold a digit
def kw2.frac.end(
  +rev: List<&2, Char>,
  +clock: T.Clock,
  +date: T.Date,
  +rest: List<&2, Char>
) -> {kn.wne(T.when.frac.end(rev, clock, date, rest)) == True{} : Bool}:
  kw2.frac.end.go(T.cs.some(rev), rev, clock, date, rest)

# one fractional digit, or the end of the fraction
def kw2.frac.digit(
  +digit: Bool,
  +cc: Char,
  +tt: List<&2, Char>,
  +rev: List<&2, Char>,
  +clock: T.Clock,
  +date: T.Date,
  _more: Unit -> T.WhenOut,
  +em: {kn.wne(_more(Unit{})) == True{} : Bool}
) -> {kn.wne(T.when.frac.digit(digit, cc, tt, rev, clock, date, _more)) == True{} : Bool}:
  match digit:
    case True{}:
      em
    case False{}:
      kw2.frac.end(rev, clock, date, cc <> tt)

# fractional digits
def kw2.frac.digits(
  +cs: List<&2, Char>,
  +rev: List<&2, Char>,
  +clock: T.Clock,
  +date: T.Date
) -> {kn.wne(T.when.frac.digits(cs, rev, clock, date)) == True{} : Bool}:
  match cs:
    case []:
      kw2.frac.end(rev, clock, date, [])
    case +c <> +t:
      kw2.frac.digit(Char.is_digit(c), c, t, rev, clock, date, _u => T.when.frac.digits(t, c <> rev, clock, date),
        kw2.frac.digits(t, c <> rev, clock, date))

# a dot starts a fraction; anything else is a zone
def kw2.frac.go(
  +dot: Bool,
  +tt: List<&2, Char>,
  +clock: T.Clock,
  +date: T.Date,
  +cc: Char
) -> {kn.wne(T.when.frac.go(dot, tt, clock, date, cc)) == True{} : Bool}:
  match dot:
    case True{}:
      kw2.frac.digits(tt, [], clock, date)
    case False{}:
      kw2.zone(cc <> tt, clock, date)

# an optional fractional second
def kw2.frac(
  +cs: List<&2, Char>,
  +clock: T.Clock,
  +date: T.Date
) -> {kn.wne(T.when.frac(cs, clock, date)) == True{} : Bool}:
  match cs:
    case []:
      kw2.done(date, clock, T.WLocal{date, clock})
    case +c <> t:
      kw2.frac.go(Char.is_eq(c, '.'), t, clock, date, c)

# the second is in range, then the fraction and the zone
def kw2.clock.range.s(
  +s_ok: Bool,
  +hh: U32,
  +mi: U32,
  +ss: U32,
  +cs: List<&2, Char>,
  +date: T.Date
) -> {kn.wne(T.when.clock.range.s(s_ok, hh, mi, ss, cs, date)) == True{} : Bool}:
  match s_ok:
    case False{}:
      {==}
    case True{}:
      kw2.frac(cs, T.Clock{hh, mi, ss, ""}, date)

# minute and second are in range
def kw2.clock.range.m(
  +mi_ok: Bool,
  +s_ok: Bool,
  +hh: U32,
  +mi: U32,
  +ss: U32,
  +cs: List<&2, Char>,
  +date: T.Date
) -> {kn.wne(T.when.clock.range.m(mi_ok, s_ok, hh, mi, ss, cs, date)) == True{} : Bool}:
  match mi_ok:
    case False{}:
      {==}
    case True{}:
      kw2.clock.range.s(s_ok, hh, mi, ss, cs, date)

# hour, minute, and second are in range
def kw2.clock.range(
  +h_ok: Bool,
  +mi_ok: Bool,
  +s_ok: Bool,
  +hh: U32,
  +mi: U32,
  +ss: U32,
  +cs: List<&2, Char>,
  +date: T.Date
) -> {kn.wne(T.when.clock.range(h_ok, mi_ok, s_ok, hh, mi, ss, cs, date)) == True{} : Bool}:
  match h_ok:
    case False{}:
      {==}
    case True{}:
      kw2.clock.range.m(mi_ok, s_ok, hh, mi, ss, cs, date)

# seconds, then an optional fraction and zone
def kw2.clock.ss.go(
  +dd: T.Dig,
  +hh: U32,
  +mi: U32,
  +date: T.Date
) -> {kn.wne(T.when.clock.ss.go(dd, hh, mi, date)) == True{} : Bool}:
  match dd:
    case T.DigBad{}:
      {==}
    case T.DigOk{+n, cs}:
      kw2.clock.range(T.bound.rng(hh, 0, 23), T.bound.rng(mi, 0, 59), T.bound.rng(n, 0, 60), hh, mi, n, cs, date)

# seconds after the colon
def kw2.clock.ss(
  +hit: Bool,
  +dd: T.Dig,
  +hh: U32,
  +mi: U32,
  +date: T.Date
) -> {kn.wne(T.when.clock.ss(hit, dd, hh, mi, date)) == True{} : Bool}:
  match hit:
    case False{}:
      {==}
    case True{}:
      kw2.clock.ss.go(dd, hh, mi, date)

# the colon after the minutes
def kw2.clock.mm.colon(
  +cs: List<&2, Char>,
  +hh: U32,
  +mi: U32,
  +date: T.Date
) -> {kn.wne(T.when.clock.mm.colon(cs, hh, mi, date)) == True{} : Bool}:
  match cs:
    case []:
      {==}
    case +c <> t:
      kw2.clock.ss(Char.is_eq(c, ':'), T.take.n(2n, t, 0, True{}), hh, mi, date)

# minutes, then seconds
def kw2.clock.mm(
  +dd: T.Dig,
  +hh: U32,
  +date: T.Date
) -> {kn.wne(T.when.clock.mm(dd, hh, date)) == True{} : Bool}:
  match dd:
    case T.DigBad{}:
      {==}
    case T.DigOk{+n, +cs}:
      kw2.clock.mm.colon(cs, hh, n, date)

# the colon after the hour
def kw2.clock.colon.go(
  +hit: Bool,
  +hh: U32,
  +tt: List<&2, Char>,
  +date: T.Date
) -> {kn.wne(T.when.clock.colon.go(hit, hh, tt, date)) == True{} : Bool}:
  match hit:
    case False{}:
      {==}
    case True{}:
      kw2.clock.mm(T.take.n(2n, tt, 0, True{}), hh, date)

# the colon after the hour
def kw2.clock.colon(
  +cs: List<&2, Char>,
  +hh: U32,
  +date: T.Date
) -> {kn.wne(T.when.clock.colon(cs, hh, date)) == True{} : Bool}:
  match cs:
    case []:
      {==}
    case +c <> t:
      kw2.clock.colon.go(Char.is_eq(c, ':'), hh, t, date)

# a clock following a date
def kw2.clock.of(
  +dd: T.Dig,
  +date: T.Date
) -> {kn.wne(T.when.clock.of(dd, date)) == True{} : Bool}:
  match dd:
    case T.DigBad{}:
      {==}
    case T.DigOk{+n, +cs}:
      kw2.clock.colon(cs, n, date)

# a space separates a date from a time
def kw2.after.sp(
  +sp: Bool,
  +date: T.Date,
  +tt: List<&2, Char>
) -> {kn.wne(T.when.after.sp(sp, date, tt)) == True{} : Bool}:
  match sp:
    case True{}:
      kw2.clock.of(T.take.n(2n, tt, 0, True{}), date)
    case False{}:
      {==}

# T or a space separates a date from a time
def kw2.after.sep(
  +tee: Bool,
  +sp: Bool,
  +date: T.Date,
  +tt: List<&2, Char>
) -> {kn.wne(T.when.after.sep(tee, sp, date, tt)) == True{} : Bool}:
  match tee:
    case True{}:
      kw2.clock.of(T.take.n(2n, tt, 0, True{}), date)
    case False{}:
      kw2.after.sp(sp, date, tt)

# the character after a date: nothing, T, or a space, and then a time
def kw2.after.date(
  +date: T.Date,
  +cs: List<&2, Char>
) -> {kn.wne(T.when.after.date(date, cs)) == True{} : Bool}:
  match cs:
    case []:
      {==}
    case +c <> t:
      kw2.after.sep(Bool.or(Char.is_eq(c, 'T'), Char.is_eq(c, 't')), Char.is_eq(c, ' '), date, t)

# the day is in range, then the rest of the token is a time or nothing
def kw2.date.ok.d(
  +d_ok: Bool,
  +yy: U32,
  +mo: U32,
  +dd: U32,
  +cs: List<&2, Char>
) -> {kn.wne(T.when.date.ok.d(d_ok, yy, mo, dd, cs)) == True{} : Bool}:
  match d_ok:
    case False{}:
      {==}
    case True{}:
      kw2.after.date(T.Date{yy, mo, dd}, cs)

# a date whose fields are in range
def kw2.date.ok.go(
  +mo_ok: Bool,
  +d_ok: Bool,
  +yy: U32,
  +mo: U32,
  +dd: U32,
  +cs: List<&2, Char>
) -> {kn.wne(T.when.date.ok.go(mo_ok, d_ok, yy, mo, dd, cs)) == True{} : Bool}:
  match mo_ok:
    case False{}:
      {==}
    case True{}:
      kw2.date.ok.d(d_ok, yy, mo, dd, cs)

# a date whose fields are in range: the day within its month in that year
def kw2.date.ok(
  +yy: U32,
  +mo: U32,
  +dd: U32,
  +cs: List<&2, Char>
) -> {kn.wne(T.when.date.ok(yy, mo, dd, cs)) == True{} : Bool}:
  kw2.date.ok.go(T.bound.rng(mo, 1, 12), T.bound.rng(dd, 1, T.when.days(yy, mo)), yy, mo, dd, cs)

# a local time: HH:MM:SS, with the hour already taken
def kw2.time.rest(
  +tt: List<&2, Char>,
  +hh: U32
) -> {kn.wne(T.when.time.rest(tt, hh)) == True{} : Bool}:
  kw2.clock.mm(T.take.n(2n, tt, 0, True{}), hh, T.Date{0, 1, 1})

# a local time uses a dummy date and then keeps only the clock
def kw2.time.only(
  +ww: T.WhenOut,
  +ew: {kn.wne(ww) == True{} : Bool}
) -> {kn.wne(T.when.time.only(ww)) == True{} : Bool}:
  match ww:
    case T.WSome{T.WLocal{_d, _c}}:
      {==}
    case T.WSome{T.WOff{_d, _c, _z}}:
      {==}
    case T.WSome{T.WDate{_d}}:
      {==}
    case T.WSome{T.WTime{_c}}:
      {==}
    case T.WFail{_w}:
      ew
    case T.WSkip{}:
      {==}

# a complete date, then whatever follows it
def kw2.day.end(
  +dd: T.Dig,
  +yy: U32,
  +mo: U32
) -> {kn.wne(T.when.day.end(dd, yy, mo)) == True{} : Bool}:
  match dd:
    case T.DigBad{}:
      {==}
    case T.DigOk{+n, +cs}:
      kw2.date.ok(yy, mo, n, cs)

# the day is two digits
def kw2.day.go(
  +hit: Bool,
  +dd: T.Dig,
  +yy: U32,
  +mo: U32
) -> {kn.wne(T.when.day.go(hit, dd, yy, mo)) == True{} : Bool}:
  match hit:
    case False{}:
      {==}
    case True{}:
      kw2.day.end(dd, yy, mo)

# the day
def kw2.day(
  +cs: List<&2, Char>,
  +yy: U32,
  +mo: U32
) -> {kn.wne(T.when.day(cs, yy, mo)) == True{} : Bool}:
  match cs:
    case []:
      {==}
    case +c <> t:
      kw2.day.go(Char.is_eq(c, '-'), T.take.n(2n, t, 0, True{}), yy, mo)

# the dash after the month
def kw2.month.go(
  +dd: T.Dig,
  +yy: U32
) -> {kn.wne(T.when.month.go(dd, yy)) == True{} : Bool}:
  match dd:
    case T.DigBad{}:
      {==}
    case T.DigOk{+n, +cs}:
      kw2.day(cs, yy, n)

# the month
def kw2.month(
  +hit: Bool,
  +dd: T.Dig,
  +yy: U32
) -> {kn.wne(T.when.month(hit, dd, yy)) == True{} : Bool}:
  match hit:
    case False{}:
      {==}
    case True{}:
      kw2.month.go(dd, yy)

# the dash after the year
def kw2.year.dash(
  +cs: List<&2, Char>,
  +yy: U32
) -> {kn.wne(T.when.year.dash(cs, yy)) == True{} : Bool}:
  match cs:
    case []:
      {==}
    case +c <> t:
      kw2.month(Char.is_eq(c, '-'), T.take.n(2n, t, 0, True{}), yy)

# the fourth year digit, then the month
def kw2.year4(
  +dd: T.Dig
) -> {kn.wne(T.when.year4(dd)) == True{} : Bool}:
  match dd:
    case T.DigBad{}:
      {==}
    case T.DigOk{+n, +cs}:
      kw2.year.dash(cs, n)

# two more year digits, then a dash
def kw2.year.more(
  +digit: Bool,
  +nn: U32,
  +cc: Char,
  +tt: List<&2, Char>
) -> {kn.wne(T.when.year.more(digit, nn, cc, tt)) == True{} : Bool}:
  match digit:
    case False{}:
      {==}
    case True{}:
      kw2.year4(T.take.n(1n, tt, U32.add(U32.mul(nn, 10), T.dig.val(cc)), True{}))

# a colon means a local time; another digit continues a year
def kw2.branch(
  +colon: Bool,
  +digit: Bool,
  +nn: U32,
  +cc: Char,
  +tt: List<&2, Char>
) -> {kn.wne(T.when.branch(colon, digit, nn, cc, tt)) == True{} : Bool}:
  match colon:
    case True{}:
      kw2.time.only(T.when.time.rest(tt, nn), kw2.time.rest(tt, nn))
    case False{}:
      kw2.year.more(digit, nn, cc, tt)

# two digits decide a time or a date
def kw2.after2.go(
  +cs: List<&2, Char>,
  +nn: U32
) -> {kn.wne(T.when.after2.go(cs, nn)) == True{} : Bool}:
  match cs:
    case []:
      {==}
    case +c <> t:
      kw2.branch(Char.is_eq(c, ':'), Char.is_digit(c), nn, c, t)

# two digits decide a time (HH:) or a date (YYYY-)
def kw2.after2(
  +dd: T.Dig
) -> {kn.wne(T.when.after2(dd)) == True{} : Bool}:
  match dd:
    case T.DigBad{}:
      {==}
    case T.DigOk{+n, +cs}:
      kw2.after2.go(cs, n)

# a datetime token
def kw2.read(
  +cs: List<&2, Char>
) -> {kn.wne(T.when.read(cs)) == True{} : Bool}:
  kw2.after2(T.take.n(2n, cs, 0, True{}))

# a digit that fits the base
def kn.digit.ok(
  +ok: Bool,
  +cc: Char,
  +nk: T.NK,
  +sign: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +enk: {kn.nb(nk) == False{} : Bool}
) -> {kn.ok(T.num.digit.ok(ok, cc, nk, sign, base, ds)) == True{} : Bool}:
  match ok:
    case False{}:
      {==}
    case True{}:
      kn.dok(nk, sign, base, T.dec.go(ds, base, T.dig.val(cc)), enk)

# a decimal digit joined to the numeral
def kn.digit.go(
  +st: T.Num,
  +cc: Char,
  +nk: T.NK,
  +_en: {kn.ok(st) == True{} : Bool},
  +enk: {kn.nb(nk) == False{} : Bool}
) -> {kn.ok(T.num.digit.go(st, cc, nk)) == True{} : Bool}:
  match st:
    case T.Num{_nk, +sign, +base, +ds, _us, _saw, _why}:
      kn.digit.ok(T.dig.ok(T.dig.val(cc), base), cc, nk, sign, base, ds, enk)

# a decimal digit joined to the numeral
def kn.digit(
  +st: T.Num,
  +cc: Char,
  +nk: T.NK,
  +en: {kn.ok(st) == True{} : Bool},
  +enk: {kn.nb(nk) == False{} : Bool}
) -> {kn.ok(T.num.digit(st, cc, nk)) == True{} : Bool}:
  kn.digit.go(st, cc, nk, en, enk)

# an underscore between digits
def kn.us.go(
  +ok: Bool,
  +nk: T.NK,
  +sign: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +why: String,
  +en: {kn.ok2(nk, why) == True{} : Bool}
) -> {kn.ok(T.num.us.go(ok, nk, sign, base, ds, why)) == True{} : Bool}:
  match ok:
    case False{}:
      {==}
    case True{}:
      en

# an underscore between digits
def kn.us(
  +st: T.Num,
  +en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.us(st)) == True{} : Bool}:
  match st:
    case T.Num{+nk, +sign, +base, +ds, +us, +saw, +why}:
      kn.us.go(Bool.and(saw, Bool.not(us)), nk, sign, base, ds, why, en)

# a dot begins the fraction
def kn.dot.go(
  +ok: Bool,
  +sign: T.Sign
) -> {kn.ok(T.num.dot.go(ok, sign)) == True{} : Bool}:
  match ok:
    case False{}:
      {==}
    case True{}:
      {==}

# a dot begins the fraction
def kn.dot(
  +st: T.Num,
  +_en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.dot(st)) == True{} : Bool}:
  match st:
    case T.Num{_nk, +sign, _b, _ds, +us, +saw, _why}:
      kn.dot.go(Bool.and(saw, Bool.not(us)), sign)

# an exponent marker
def kn.exp.go(
  +ok: Bool,
  +sign: T.Sign
) -> {kn.ok(T.num.exp.go(ok, sign)) == True{} : Bool}:
  match ok:
    case False{}:
      {==}
    case True{}:
      {==}

# an exponent marker
def kn.exp(
  +st: T.Num,
  +_en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.exp(st)) == True{} : Bool}:
  match st:
    case T.Num{_nk, +sign, _b, _ds, +us, +saw, _why}:
      kn.exp.go(Bool.and(saw, Bool.not(us)), sign)

# a first digit
def kn.lead.digit(
  +digit: Bool,
  +st: T.Num,
  +cc: Char,
  +en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.lead.digit(digit, st, cc)) == True{} : Bool}:
  match digit:
    case True{}:
      kn.digit(st, cc, T.NDig{}, en, {==})
    case False{}:
      {==}

# a leading zero, or another digit
def kn.lead.zero(
  +zero: Bool,
  +digit: Bool,
  +st: T.Num,
  +cc: Char,
  +en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.lead.zero(zero, digit, st, cc)) == True{} : Bool}:
  match zero:
    case True{}:
      {==}
    case False{}:
      kn.lead.digit(digit, st, cc, en)

# a minus, a zero, or a digit
def kn.lead.minus(
  +minus: Bool,
  +zero: Bool,
  +digit: Bool,
  +st: T.Num,
  +cc: Char,
  +en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.lead.minus(minus, zero, digit, st, cc)) == True{} : Bool}:
  match minus:
    case True{}:
      {==}
    case False{}:
      kn.lead.zero(zero, digit, st, cc, en)

# a sign, a zero, or a digit
def kn.lead.go(
  +plus: Bool,
  +minus: Bool,
  +zero: Bool,
  +digit: Bool,
  +st: T.Num,
  +cc: Char,
  +en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.lead.go(plus, minus, zero, digit, st, cc)) == True{} : Bool}:
  match plus:
    case True{}:
      {==}
    case False{}:
      kn.lead.minus(minus, zero, digit, st, cc, en)

# the first character after an optional sign
def kn.lead(
  +st: T.Num,
  +cc: Char,
  +en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.lead(st, cc)) == True{} : Bool}:
  kn.lead.go(Char.is_eq(cc, '+'), Char.is_eq(cc, '-'), Char.is_eq(cc, '0'), Char.is_digit(cc), st, cc, en)

# a second sign is refused; any other character is read as the first one of
# an unsigned numeral, with the sign kept
def kn.after.sign.go(
  +twice: Bool,
  +sign: T.Sign,
  +cc: Char
) -> {kn.ok(T.num.after.sign.go(twice, sign, cc)) == True{} : Bool}:
  match twice:
    case True{}:
      {==}
    case False{}:
      kn.lead(T.Num{T.NLead{}, sign, 10, [], False{}, False{}, ""}, cc, {==})

# the character after a sign
def kn.after.sign(
  +st: T.Num,
  +cc: Char,
  +_en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.after.sign(st, cc)) == True{} : Bool}:
  kn.after.sign.go(Bool.or(Char.is_eq(cc, '+'), Char.is_eq(cc, '-')), T.num.sign.of(st), cc)

# a capital exponent; any other character is refused, since a digit or an
# underscore after a leading zero (`01`, `0_1`) would hide it
def kn.zero.exp2(
  +ee: Bool,
  +st: T.Num,
  +_c: Char,
  +en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.zero.exp2(ee, st, _c)) == True{} : Bool}:
  match ee:
    case True{}:
      kn.exp(st, en)
    case False{}:
      {==}

# an exponent after zero, or a rejected extra digit
def kn.zero.exp(
  +eee: Bool,
  +ee: Bool,
  +st: T.Num,
  +cc: Char,
  +en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.zero.exp(eee, ee, st, cc)) == True{} : Bool}:
  match eee:
    case True{}:
      kn.exp(st, en)
    case False{}:
      kn.zero.exp2(ee, st, cc, en)

# a fraction or an exponent after zero
def kn.zero.dot(
  +dot: Bool,
  +eee: Bool,
  +ee: Bool,
  +st: T.Num,
  +cc: Char,
  +en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.zero.dot(dot, eee, ee, st, cc)) == True{} : Bool}:
  match dot:
    case True{}:
      kn.dot(st, en)
    case False{}:
      kn.zero.exp(eee, ee, st, cc, en)

# a binary prefix, or a float
def kn.zero.b(
  +bb: Bool,
  +dot: Bool,
  +eee: Bool,
  +ee: Bool,
  +st: T.Num,
  +cc: Char,
  +en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.zero.b(bb, dot, eee, ee, st, cc)) == True{} : Bool}:
  match bb:
    case True{}:
      kn.base(st, 2)
    case False{}:
      kn.zero.dot(dot, eee, ee, st, cc, en)

# an octal prefix, or the rest
def kn.zero.o(
  +oo: Bool,
  +bb: Bool,
  +dot: Bool,
  +eee: Bool,
  +ee: Bool,
  +st: T.Num,
  +cc: Char,
  +en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.zero.o(oo, bb, dot, eee, ee, st, cc)) == True{} : Bool}:
  match oo:
    case True{}:
      kn.base(st, 8)
    case False{}:
      kn.zero.b(bb, dot, eee, ee, st, cc, en)

# a base prefix, a fraction, or an exponent
def kn.zero.go(
  +xx: Bool,
  +oo: Bool,
  +bb: Bool,
  +dot: Bool,
  +eee: Bool,
  +ee: Bool,
  +st: T.Num,
  +cc: Char,
  +en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.zero.go(xx, oo, bb, dot, eee, ee, st, cc)) == True{} : Bool}:
  match xx:
    case True{}:
      kn.base(st, 16)
    case False{}:
      kn.zero.o(oo, bb, dot, eee, ee, st, cc, en)

# the character after a lone zero
def kn.zero(
  +st: T.Num,
  +cc: Char,
  +en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.zero(st, cc)) == True{} : Bool}:
  kn.zero.go(Char.is_eq(cc, 'x'), Char.is_eq(cc, 'o'), Char.is_eq(cc, 'b'), Char.is_eq(cc, '.'), Char.is_eq(cc, 'e'),
    Char.is_eq(cc, 'E'), st, cc, en)

# a capital exponent, or a rejected character
def kn.digs.exp2(
  +ee: Bool,
  +st: T.Num,
  +_c: Char,
  +en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.digs.exp2(ee, st, _c)) == True{} : Bool}:
  match ee:
    case True{}:
      kn.exp(st, en)
    case False{}:
      {==}

# an exponent
def kn.digs.exp(
  +eee: Bool,
  +ee: Bool,
  +st: T.Num,
  +cc: Char,
  +en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.digs.exp(eee, ee, st, cc)) == True{} : Bool}:
  match eee:
    case True{}:
      kn.exp(st, en)
    case False{}:
      kn.digs.exp2(ee, st, cc, en)

# a dot or an exponent
def kn.digs.dot(
  +dot: Bool,
  +eee: Bool,
  +ee: Bool,
  +st: T.Num,
  +cc: Char,
  +en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.digs.dot(dot, eee, ee, st, cc)) == True{} : Bool}:
  match dot:
    case True{}:
      kn.dot(st, en)
    case False{}:
      kn.digs.exp(eee, ee, st, cc, en)

# an underscore, a dot, or an exponent
def kn.digs.us(
  +us: Bool,
  +dot: Bool,
  +eee: Bool,
  +ee: Bool,
  +st: T.Num,
  +cc: Char,
  +en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.digs.us(us, dot, eee, ee, st, cc)) == True{} : Bool}:
  match us:
    case True{}:
      kn.us(st, en)
    case False{}:
      kn.digs.dot(dot, eee, ee, st, cc, en)

# a decimal digit, an underscore, a dot, or an exponent
def kn.digs.go(
  +digit: Bool,
  +us: Bool,
  +dot: Bool,
  +eee: Bool,
  +ee: Bool,
  +st: T.Num,
  +cc: Char,
  +en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.digs.go(digit, us, dot, eee, ee, st, cc)) == True{} : Bool}:
  match digit:
    case True{}:
      kn.digit(st, cc, T.NDig{}, en, {==})
    case False{}:
      kn.digs.us(us, dot, eee, ee, st, cc, en)

# a decimal digit, an underscore, a dot, or an exponent
def kn.digs(
  +st: T.Num,
  +cc: Char,
  +en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.digs(st, cc)) == True{} : Bool}:
  kn.digs.go(Char.is_digit(cc), Char.is_eq(cc, '_'), Char.is_eq(cc, '.'), Char.is_eq(cc, 'e'), Char.is_eq(cc, 'E'),
    st, cc, en)

# an underscore, or a digit of the base
def kn.based.go(
  +us: Bool,
  +st: T.Num,
  +cc: Char,
  +en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.based.go(us, st, cc)) == True{} : Bool}:
  match us:
    case True{}:
      kn.us(st, en)
    case False{}:
      kn.digit(st, cc, T.NBase{}, en, {==})

# a digit of a prefixed integer, or an underscore
def kn.based(
  +st: T.Num,
  +cc: Char,
  +en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.based(st, cc)) == True{} : Bool}:
  kn.based.go(Char.is_eq(cc, '_'), st, cc, en)

# a capital exponent, or a rejected character
def kn.frac.exp2(
  +ee: Bool,
  +st: T.Num,
  +_c: Char,
  +en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.frac.exp2(ee, st, _c)) == True{} : Bool}:
  match ee:
    case True{}:
      kn.exp(st, en)
    case False{}:
      {==}

# an exponent in a fraction
def kn.frac.exp(
  +eee: Bool,
  +ee: Bool,
  +st: T.Num,
  +cc: Char,
  +en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.frac.exp(eee, ee, st, cc)) == True{} : Bool}:
  match eee:
    case True{}:
      kn.exp(st, en)
    case False{}:
      kn.frac.exp2(ee, st, cc, en)

# an underscore or an exponent in a fraction
def kn.frac.us(
  +us: Bool,
  +eee: Bool,
  +ee: Bool,
  +st: T.Num,
  +cc: Char,
  +en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.frac.us(us, eee, ee, st, cc)) == True{} : Bool}:
  match us:
    case True{}:
      kn.us(st, en)
    case False{}:
      kn.frac.exp(eee, ee, st, cc, en)

# a fraction digit, an underscore, or an exponent
def kn.frac.go(
  +digit: Bool,
  +us: Bool,
  +eee: Bool,
  +ee: Bool,
  +st: T.Num,
  +cc: Char,
  +en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.frac.go(digit, us, eee, ee, st, cc)) == True{} : Bool}:
  match digit:
    case True{}:
      kn.digit(st, cc, T.NFrac{}, en, {==})
    case False{}:
      kn.frac.us(us, eee, ee, st, cc, en)

# a fraction digit, an underscore, or an exponent
def kn.frac(
  +st: T.Num,
  +cc: Char,
  +en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.frac(st, cc)) == True{} : Bool}:
  kn.frac.go(Char.is_digit(cc), Char.is_eq(cc, '_'), Char.is_eq(cc, 'e'), Char.is_eq(cc, 'E'), st, cc, en)

# a digit of the exponent
def kn.expon.digit(
  +digit: Bool,
  +st: T.Num,
  +cc: Char,
  +en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.expon.digit(digit, st, cc)) == True{} : Bool}:
  match digit:
    case True{}:
      kn.digit(st, cc, T.NEDig{}, en, {==})
    case False{}:
      {==}

# a minus or a digit in an exponent
def kn.expon.minus(
  +minus: Bool,
  +digit: Bool,
  +st: T.Num,
  +cc: Char,
  +en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.expon.minus(minus, digit, st, cc)) == True{} : Bool}:
  match minus:
    case True{}:
      kn.expsign(st)
    case False{}:
      kn.expon.digit(digit, st, cc, en)

# the sign or the first digit of an exponent
def kn.expon.go(
  +plus: Bool,
  +minus: Bool,
  +digit: Bool,
  +st: T.Num,
  +cc: Char,
  +en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.expon.go(plus, minus, digit, st, cc)) == True{} : Bool}:
  match plus:
    case True{}:
      kn.expsign(st)
    case False{}:
      kn.expon.minus(minus, digit, st, cc, en)

# the sign or the first digit of an exponent
def kn.expon(
  +st: T.Num,
  +cc: Char,
  +en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.expon(st, cc)) == True{} : Bool}:
  kn.expon.go(Char.is_eq(cc, '+'), Char.is_eq(cc, '-'), Char.is_digit(cc), st, cc, en)

# an underscore in an exponent
def kn.edig.us(
  +us: Bool,
  +st: T.Num,
  +_c: Char,
  +en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.edig.us(us, st, _c)) == True{} : Bool}:
  match us:
    case True{}:
      kn.us(st, en)
    case False{}:
      {==}

# an exponent digit or an underscore
def kn.edig.go(
  +digit: Bool,
  +us: Bool,
  +st: T.Num,
  +cc: Char,
  +en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.edig.go(digit, us, st, cc)) == True{} : Bool}:
  match digit:
    case True{}:
      kn.digit(st, cc, T.NEDig{}, en, {==})
    case False{}:
      kn.edig.us(us, st, cc, en)

# an exponent digit or an underscore
def kn.edig(
  +st: T.Num,
  +cc: Char,
  +en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.edig(st, cc)) == True{} : Bool}:
  kn.edig.go(Char.is_digit(cc), Char.is_eq(cc, '_'), st, cc, en)

# one character of a numeral
def kn.on(
  +nk: T.NK,
  +st: T.Num,
  +cc: Char,
  +en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.on(nk, st, cc)) == True{} : Bool}:
  match nk:
    case T.NLead{}:
      kn.lead(st, cc, en)
    case T.NSign{}:
      kn.after.sign(st, cc, en)
    case T.NZero{}:
      kn.zero(st, cc, en)
    case T.NDig{}:
      kn.digs(st, cc, en)
    case T.NBase{}:
      kn.based(st, cc, en)
    case T.NFrac{}:
      kn.frac(st, cc, en)
    case T.NExp{}:
      kn.expon(st, cc, en)
    case T.NEDig{}:
      kn.edig(st, cc, en)
    case T.NBad{}:
      en

# one character of a numeral
def kn.step.go(
  +st: T.Num,
  +cc: Char,
  +en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.step.go(st, cc)) == True{} : Bool}:
  match st:
    case T.Num{+nk, +sign, +base, +ds, +us, +saw, +why}:
      kn.on(nk, T.Num{nk, sign, base, ds, us, saw, why}, cc, en)

# one character of a numeral
def kn.step(
  +st: T.Num,
  +cc: Char,
  +en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.step(st, cc)) == True{} : Bool}:
  kn.step.go(st, cc, en)

# the walk over a numeral
def kn.go(
  +cs: List<&2, Char>,
  +st: T.Num,
  +en: {kn.ok(st) == True{} : Bool}
) -> {kn.ok(T.num.go(cs, st)) == True{} : Bool}:
  match cs:
    case []:
      en
    case +h <> t:
      kn.go(t, T.num.step(st, h), kn.step(st, h, en))

# a datetime's result as a bare word's
def kn.fw(
  ww: T.WhenOut,
  +ee: {kn.wne(ww) == True{} : Bool}
) -> {L1.k3.why(T.word.from.when(ww)) == True{} : Bool}:
  match ww:
    case T.WSome{_w}:
      {==}
    case T.WFail{_y}:
      ee
    case T.WSkip{}:
      {==}

# an integer's range
def kn.frange(
  ok: Bool,
  +sign: T.Sign,
  +digits: String
) -> {L1.k3.why(T.num.fin.range(ok, sign, digits)) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

# a finished integer
def kn.fint(
  saw: Bool,
  +sign: T.Sign,
  +digits: String
) -> {L1.k3.why(T.num.fin.int(saw, sign, digits)) == True{} : Bool}:
  match saw:
    case False{}:
      {==}
    case True{}:
      kn.frange(T.i64.fits(sign, digits), sign, digits)

# a numeral's last run
def kn.fsaw(saw: Bool, +val: T.Val) -> {L1.k3.why(T.num.fin.saw(saw, val)) == True{} : Bool}:
  match saw:
    case False{}:
      {==}
    case True{}:
      {==}

# a prefixed integer
def kn.fbase(
  signed: Bool,
  +saw: Bool,
  +sign: T.Sign,
  +ds: List<&2, U32>
) -> {L1.k3.why(T.num.fin.base(signed, saw, sign, ds)) == True{} : Bool}:
  match signed:
    case True{}:
      {==}
    case False{}:
      kn.fint(saw, sign, T.dec.text(ds))

# the kind a numeral's scan finished in
def kn.fnk(
  nk: T.NK,
  +sign: T.Sign,
  +ds: List<&2, U32>,
  +saw: Bool,
  +why: String,
  +cs: List<&2, Char>,
  +en: {kn.ok2(nk, why) == True{} : Bool}
) -> {L1.k3.why(T.num.fin.nk(nk, sign, ds, saw, why, cs)) == True{} : Bool}:
  match nk:
    case T.NBad{}:
      en
    case T.NLead{}:
      {==}
    case T.NSign{}:
      {==}
    case T.NZero{}:
      {==}
    case T.NDig{}:
      kn.fint(saw, sign, T.dec.text(ds))
    case T.NBase{}:
      kn.fbase(T.num.signed(cs), saw, sign, ds)
    case T.NFrac{}:
      kn.fsaw(saw, T.VFlo{sign, T.word.body(cs)})
    case T.NExp{}:
      {==}
    case T.NEDig{}:
      kn.fsaw(saw, T.VFlo{sign, T.word.body(cs)})

# a trailing underscore
def kn.fus(
  us: Bool,
  +nk: T.NK,
  +sign: T.Sign,
  +ds: List<&2, U32>,
  +saw: Bool,
  +why: String,
  +cs: List<&2, Char>,
  +en: {kn.ok2(nk, why) == True{} : Bool}
) -> {L1.k3.why(T.num.fin.us(us, nk, sign, ds, saw, why, cs)) == True{} : Bool}:
  match us:
    case True{}:
      {==}
    case False{}:
      kn.fnk(nk, sign, ds, saw, why, cs, en)

# a finished numeral
def kn.fin(
  +st: T.Num,
  +cs: List<&2, Char>,
  +en: {kn.ok(st) == True{} : Bool}
) -> {L1.k3.why(T.num.fin(st, cs)) == True{} : Bool}:
  match st:
    case T.Num{+nk, +sign, _b, +ds, +us, +saw, +why}:
      kn.fus(us, nk, sign, ds, saw, why, cs, en)

# a datetime token, or a numeral
def kn.rdate(
  date: Bool,
  +cs: List<&2, Char>
) -> {L1.k3.why(T.word.route.date(date, cs)) == True{} : Bool}:
  match date:
    case True{}:
      kn.fw(T.when.read(cs), kw2.read(cs))
    case False{}:
      kn.fin(T.num.go(cs, T.num.start()), cs, kn.go(cs, T.num.start(), {==}))

# a special word, or a routed one
def kn.route(
  gg: T.Got,
  +date: Bool,
  +cs: List<&2, Char>
) -> {L1.k3.why(T.word.route(gg, date, cs)) == True{} : Bool}:
  match gg:
    case T.GotVal{_v}:
      {==}
    case T.GotBad{_w}:
      kn.rdate(T.word.as_date(date, T.word.ee(cs)), cs)

# a word that may be special, or not
def kn.pick(
  special: Bool,
  +cs: List<&2, Char>
) -> {L1.k3.why(T.word.val.pick(special, cs)) == True{} : Bool}:
  match special:
    case True{}:
      kn.route(T.word.spec(String.from_list(cs)), T.word.or(T.word.colon(cs), T.word.dash(cs, True{})), cs)
    case False{}:
      kn.route(T.GotBad{""}, T.word.or(T.word.colon(cs), T.word.dash(cs, True{})), cs)

def L1.bare_word_refusal_says_why(cs):
  kn.pick(T.word.lead(cs), cs)
