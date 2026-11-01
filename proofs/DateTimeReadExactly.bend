# proofs of laws/DateTimeReadExactly.bend
import Base
import ../main.bend as T
import ../src/eq.bend as Eq
import ../laws/DateTimeReadExactly.bend as Laws
import ../laws/defs/AbnfGrammar.bend as D1
import ../laws/defs/BareValueGrammar.bend as D2
import ../laws/defs/DocumentSameness.bend as D3
import ../laws/defs/GrammarDerivations.bend as D4
import ./lemmas/BareWordInArray.bend as M1
import ./lemmas/BareWordRefusal.bend as M2
import ./lemmas/BooleanIsBareWord.bend as M3
import ./lemmas/DateClockText.bend as M4
import ./lemmas/DateTimeBareWord.bend as M5
import ./lemmas/DateTimeWordGrammar.bend as M6
import ./lemmas/DecimalArithmetic.bend as M7
import ./lemmas/DigitsWrittenBack.bend as M8
import ./lemmas/FreshNamesInRows.bend as M9
import ./lemmas/PickAndDigitSteps.bend as M10
import ./lemmas/PrefixAndTake.bend as M11
import ./lemmas/ShortTextBounds.bend as M12
import ./lemmas/ValueSelfEquality.bend as M13
import ./lemmas/ValueTextReadback.bend as M14

# every month's number is from 1 to 12
def month.ok(mm: D1.Month) -> {True{} == T.bound.rng(Laws.month.num(mm), 1, 12) : Bool}:
  match mm:
    case D1.Jan{}:
      {==}
    case D1.Feb{}:
      {==}
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

# the day test, with the code's days of the month turned into the table's
def day.test(
  +yy: U32,
  +mm: D1.Month,
  +dd: U32
) -> {Bool.and(U32.is_ge(dd, 1), U32.is_le(dd, D1.days_in(yy, mm)))
  == T.bound.rng(dd, 1, T.when.days(yy, Laws.month.num(mm))) : Bool}:
  Equal.cong(U32, Bool, xx => Bool.and(U32.is_ge(dd, 1), U32.is_le(dd, xx)),
    D1.days_in(yy, mm), T.when.days(yy, Laws.month.num(mm)),
    Equal.sym(U32, T.when.days(yy, Laws.month.num(mm)), D1.days_in(yy, mm), M6.days.same(yy, mm)))

# the claim that a date is accepted and the rest read after it
def date.In(mo_ok: Bool, d_ok: Bool, +yy: U32, +mo: U32, +dd: U32, rest: List<&2, Char>) -> Type:
  {T.when.date.ok.go(mo_ok, d_ok, yy, mo, dd, rest) == T.when.after.date(T.Date{yy, mo, dd}, rest) : T.WhenOut}

# both tests passed, so the date is accepted
def date.in(
  mo_ok: Bool,
  d_ok: Bool,
  em: {True{} == mo_ok : Bool},
  ed: {True{} == d_ok : Bool},
  +yy: U32,
  +mo: U32,
  +dd: U32,
  rest: List<&2, Char>
) -> date.In(mo_ok, d_ok, yy, mo, dd, rest):
  match mo_ok d_ok:
    case True{} True{}:
      {==}
    case True{} False{}:
      Eq.bit.absurd2(&1, date.In(True{}, False{}, yy, mo, dd, rest), ed)
    case False{} dk:
      Eq.bit.absurd2(&1, date.In(False{}, dk, yy, mo, dd, rest), em)

# the claim that a date is refused
def date.Out(mo_ok: Bool, d_ok: Bool, +yy: U32, +mo: U32, +dd: U32, rest: List<&2, Char>) -> Type:
  {Laws.when_refused(T.when.date.ok.go(mo_ok, d_ok, yy, mo, dd, rest)) == True{} : Bool}

# the day test failed, so the date is refused whatever the month test said
def date.out(
  mo_ok: Bool,
  d_ok: Bool,
  ed: {False{} == d_ok : Bool},
  +yy: U32,
  +mo: U32,
  +dd: U32,
  rest: List<&2, Char>
) -> date.Out(mo_ok, d_ok, yy, mo, dd, rest):
  match mo_ok d_ok:
    case True{} False{}:
      {==}
    case True{} True{}:
      Eq.bit.absurd(&1, date.Out(True{}, True{}, yy, mo, dd, rest), ed)
    case False{} dk:
      {==}

# the month is in range, and the day test is the table's
def Laws.date_day_in_month(yy, mm, dd, rest, e):
  date.in(T.bound.rng(Laws.month.num(mm), 1, 12), T.bound.rng(dd, 1, T.when.days(yy, Laws.month.num(mm))),
    month.ok(mm),
    Equal.trans(Bool, True{}, Bool.and(U32.is_ge(dd, 1), U32.is_le(dd, D1.days_in(yy, mm))),
      T.bound.rng(dd, 1, T.when.days(yy, Laws.month.num(mm))), e, day.test(yy, mm, dd)),
    yy, Laws.month.num(mm), dd, rest)

# the day test is the table's, and it failed
def Laws.date_day_past_month(yy, mm, dd, rest, e):
  date.out(T.bound.rng(Laws.month.num(mm), 1, 12), T.bound.rng(dd, 1, T.when.days(yy, Laws.month.num(mm))),
    Equal.trans(Bool, False{}, Bool.and(U32.is_ge(dd, 1), U32.is_le(dd, D1.days_in(yy, mm))),
      T.bound.rng(dd, 1, T.when.days(yy, Laws.month.num(mm))), e, day.test(yy, mm, dd)),
    yy, Laws.month.num(mm), dd, rest)

# none is not some datetime, as a type
def t1.dis(oo: M6.T1o) -> Type:
  match oo:
    case M6.T1some{_w}:
      Empty
    case M6.T1none{}:
      Unit

# none is not some datetime
def t1.clash(-ww: T.When, hh: {M6.T1none{} == M6.T1some{ww} : M6.T1o}) -> Empty:
  %hh : t1.dis(_)
  Unit{}

# the datetime an option holds, or the one given
def t1.ow(oo: M6.T1o, dflt: T.When) -> T.When:
  match oo:
    case M6.T1some{ww}:
      ww
    case M6.T1none{}:
      dflt

# a scan observed as a datetime gave that datetime
def t1.wsome(
  ww: T.WhenOut,
  +vv: T.When,
  hh: {M6.t1.wopt(ww) == M6.T1some{vv} : M6.T1o}
) -> {T.word.from.when(ww) == T.GotVal{T.VWhen{vv}} : T.Got}:
  match ww:
    case T.WSome{w}:
      Equal.cong(M6.T1o, T.Got, oo => T.GotVal{T.VWhen{t1.ow(oo, vv)}}, M6.T1some{w}, M6.T1some{vv}, hh)
    case T.WFail{yy}:
      Eq.bit.gone(&2, {T.word.from.when(T.WFail{yy}) == T.GotVal{T.VWhen{vv}} : T.Got}, t1.clash(vv, hh))
    case T.WSkip{}:
      Eq.bit.gone(&2, {T.word.from.when(T.WSkip{}) == T.GotVal{T.VWhen{vv}} : T.Got}, t1.clash(vv, hh))

# a word that matches reads as what it denotes (t1.rs, t1.read)
def Laws.date_time_word_read(cs, h):
  Equal.trans(T.Got, T.word.val(cs), T.word.from.when(T.when.read(cs)), T.GotVal{T.VWhen{D1.g.dt.when(cs)}},
    M6.t1.rs(cs, Eq.and.left(D1.abnf.date_time(cs), D1.prose.date_time_in_range(cs), h)),
    t1.wsome(T.when.read(cs), D1.g.dt.when(cs), Equal.trans(M6.T1o, M6.t1.wopt(T.when.read(cs)), M6.t1.spec(cs),
      M6.T1some{D1.g.dt.when(cs)}, M6.t1.read(cs), Equal.cong(Bool, M6.T1o, xx => M6.t1.pk(xx, D1.g.dt.when(cs)),
      Bool.and(D1.abnf.date_time(cs), D1.prose.date_time_in_range(cs)), True{}, h))))

# render's text reads back as the datetime (when_word), so by the classifier
# it matches and denotes it
def Laws.date_time_render(w, h):
  Equal.trans(Bool, Bool.and(D1.g.ok.val(D4.GvDateTime{String.to_list(T.render.atom(T.VWhen{w}))}, D1.RVal{}),
    D1.g.val(D4.GvDateTime{String.to_list(T.render.atom(T.VWhen{w}))}, T.VWhen{w})),
    Laws.t1.got_when(T.word.val(String.to_list(T.render.atom(T.VWhen{w}))), w), True{},
    Equal.sym(Bool, Laws.t1.got_when(T.word.val(String.to_list(T.render.atom(T.VWhen{w}))), w),
      Bool.and(D1.g.ok.val(D4.GvDateTime{String.to_list(T.render.atom(T.VWhen{w}))}, D1.RVal{}),
      D1.g.val(D4.GvDateTime{String.to_list(T.render.atom(T.VWhen{w}))}, T.VWhen{w})),
      Laws.date_time_word(String.to_list(T.render.atom(T.VWhen{w})), w)),
    Equal.trans(Bool, Laws.t1.got_when(T.word.val(String.to_list(T.render.atom(T.VWhen{w}))), w),
      Laws.t1.got_when(T.GotVal{T.VWhen{w}}, w), True{},
      Equal.cong(T.Got, Bool, gg => Laws.t1.got_when(gg, w), T.word.val(String.to_list(T.render.atom(T.VWhen{w}))),
        T.GotVal{T.VWhen{w}}, Laws.when_word(w, h)),
      M13.when.self(w)))

# nor a datetime
def vl.norm.when(gg: T.Got, +ww: T.When) -> {Laws.t1.got_when(M2.vl.norm(gg), ww) == Laws.t1.got_when(gg, ww) : Bool}:
  match gg:
    case T.GotVal{_v}:
      {==}
    case T.GotBad{_why}:
      {==}

def Laws.date_time_parses_exactly(k, ek, w, hw, d):
  Equal.trans(Bool, Laws.t1.got_when(D2.bw.got(T.parse(D1.bw.kv(k, w)), k), d),
    Laws.t1.got_when(M2.vl.norm(T.word.val(String.to_list(w))), d),
    Bool.and(D1.g.ok.val(D4.GvDateTime{String.to_list(w)}, D1.RVal{}), D1.g.val(D4.GvDateTime{
      String.to_list(w)}, T.VWhen{d})),
    Equal.cong(T.Got, Bool, gg => Laws.t1.got_when(gg, d), D2.bw.got(T.parse(D1.bw.kv(k, w)), k),
      M2.vl.norm(T.word.val(String.to_list(w))), M2.vl.pv(k, ek, w, hw)),
    Equal.trans(Bool, Laws.t1.got_when(M2.vl.norm(T.word.val(String.to_list(w))), d),
      Laws.t1.got_when(T.word.val(String.to_list(w)), d),
      Bool.and(D1.g.ok.val(D4.GvDateTime{String.to_list(w)}, D1.RVal{}), D1.g.val(D4.GvDateTime{
        String.to_list(w)}, T.VWhen{d})),
      vl.norm.when(T.word.val(String.to_list(w)), d), Laws.date_time_word(String.to_list(w), d)))

# a character written as itself that is none of them, for every one written
# as itself; a digit is none
def vl.utok(ts: List<&2, M9.Tk>) -> Bool:
  match ts:
    case []:
      True{}
    case M9.TD{_x} <> tt:
      vl.utok(tt)
    case M9.TC{+cc} <> tt:
      Bool.and(Bool.not(Laws.bw.lower(cc)), vl.utok(tt))

# the digit of a remainder by ten is none of them
def vl.up.d(+xx: U32) -> {Laws.bw.lower(M10.dch(U32.mod(xx, 10))) == False{} : Bool}:
  M10.sm.elim(rr => {Laws.bw.lower(M10.dch(rr)) == False{} : Bool}, U32.mod(xx, 10), M12.md(xx), {==}, {==}, {==},
      {==}, {==}, {==},
    {==}, {==}, {==}, {==})

# a text of tokens with none of them holds none of them
def vl.up.tks(ts: List<&2, M9.Tk>, +hh: {vl.utok(ts) == True{} : Bool}) -> {Laws.bw.upper(M7.tl(ts)) == True{} : Bool}:
  match ts:
    case []:
      {==}
    case M9.TD{+xx} <> +tt:
      M11.and.tt(Bool.not(Laws.bw.lower(M10.dch(U32.mod(xx, 10)))), Laws.bw.upper(M7.tl(tt)),
        Equal.cong(Bool, Bool, bb => Bool.not(bb), Laws.bw.lower(M10.dch(U32.mod(xx, 10))), False{}, vl.up.d(xx)),
        vl.up.tks(tt, hh))
    case M9.TC{+cc} <> +tt:
      M11.and.tt(Bool.not(Laws.bw.lower(cc)), Laws.bw.upper(M7.tl(tt)), Eq.and.left(Bool.not(Laws.bw.lower(cc)),
          vl.utok(tt),
        hh), vl.up.tks(tt, Eq.and.right(Bool.not(Laws.bw.lower(cc)), vl.utok(tt), hh)))

# a digit is none of them
def vl.up.dg(cc: Char, hc: {Char.is_digit(cc) == True{} : Bool}) -> {Bool.not(Laws.bw.lower(cc)) == True{} : Bool}:
  M9.dg.elim(zz => {Bool.not(Laws.bw.lower(zz)) == True{} : Bool}, cc, hc, {==}, {==}, {==}, {==}, {==}, {==}, {==},
      {==},
    {==}, {==})

# a fraction's digits are none of them
def vl.up.tcs(
  fr: String,
  +zs: List<&2, M9.Tk>,
  +hd: {T.wf.digits(fr) == True{} : Bool},
  +hz: {vl.utok(zs) == True{} : Bool}
) -> {vl.utok(M4.tcs(fr, zs)) == True{} : Bool}:
  match fr:
    case SNil{}:
      hz
    case SCon{+cc, +tt}:
      M11.and.tt(Bool.not(Laws.bw.lower(cc)), vl.utok(M4.tcs(tt, zs)), vl.up.dg(cc, M9.then.l(Char.is_digit(cc), tt,
          hd)),
        vl.up.tcs(tt, zs, M9.then.r(Char.is_digit(cc), tt, hd), hz))

# and so is its dot
def vl.up.fr(
  fr: String,
  +zs: List<&2, M9.Tk>,
  +hd: {T.wf.digits(fr) == True{} : Bool},
  +hz: {vl.utok(zs) == True{} : Bool}
) -> {vl.utok(M4.tfr(fr, zs)) == True{} : Bool}:
  match fr:
    case SNil{}:
      hz
    case SCon{+cc, +tt}:
      vl.up.tcs(SCon{cc, tt}, zs, hd, hz)

# a zone: Z, or a sign and digits
def vl.up.z(zz: T.Zone) -> {vl.utok(M4.tzone(zz)) == True{} : Bool}:
  match zz:
    case T.Zulu{}:
      {==}
    case T.Shift{sg, _h, _m}:
      match sg:
        case T.Plus{}:
          {==}
        case T.Minus{}:
          {==}

# a well-formed datetime's tokens are none of them
def vl.up.all(ww: T.When, +hw: {T.wf.when(ww) == True{} : Bool}) -> {vl.utok(M4.tks(ww)) == True{} : Bool}:
  match ww:
    case T.WOff{T.Date{yy, mo, dd}, T.Clock{+hh, +mi, +ss, +fr}, +zz}:
      vl.up.fr(fr, M4.tzone(zz), M4.wc.fr(hh, mi, ss, fr, Eq.and.left(T.wf.clock(T.Clock{hh, mi, ss, fr}),
          T.wf.zone(zz),
        Eq.and.right(T.wf.date(T.Date{yy, mo, dd}), Bool.and(T.wf.clock(T.Clock{hh, mi, ss, fr}), T.wf.zone(zz)), hw))),
        vl.up.z(zz))
    case T.WLocal{T.Date{yy, mo, dd}, T.Clock{+hh, +mi, +ss, +fr}}:
      vl.up.fr(fr, [], M4.wc.fr(hh, mi, ss, fr, Eq.and.right(T.wf.date(T.Date{yy, mo, dd}),
        T.wf.clock(T.Clock{hh, mi, ss, fr}), hw)), {==})
    case T.WDate{T.Date{_y, _m, _d}}:
      {==}
    case T.WTime{T.Clock{+hh, +mi, +ss, +fr}}:
      vl.up.fr(fr, [], M4.wc.fr(hh, mi, ss, fr, hw), {==})

def Laws.date_time_render_upper(w, h):
  Equal.trans(Bool, Laws.bw.upper(String.to_list(T.when.text(w))), Laws.bw.upper(M7.tl(M4.tks(w))), True{},
    Equal.cong(String, Bool, ss => Laws.bw.upper(String.to_list(ss)), T.when.text(w), M7.tstr(M4.tks(w)),
      M4.when.eq(Unit{}, w, h)), vl.up.tks(M4.tks(w), vl.up.all(w, h)))

# two dates date.eq takes for one are one
def vl.eq.date(aa: T.Date, bb: T.Date, +hh: {D3.date.eq(aa, bb) == True{} : Bool}) -> {aa == bb : T.Date}:
  match aa bb:
    case T.Date{+y1, +m1, +d1} T.Date{+y2, +m2, +d2}:
      +h2 = {Eq.and.right(U32.is_eq(y1, y2), Bool.and(U32.is_eq(m1, m2), U32.is_eq(d1, d2)), hh)
        : {Bool.and(U32.is_eq(m1, m2), U32.is_eq(d1, d2)) == True{} : Bool}}
      Equal.trans(T.Date, T.Date{y1, m1, d1}, T.Date{y2, m1, d1}, T.Date{y2, m2, d2},
        Equal.cong(U32, T.Date, xx => T.Date{xx, m1, d1}, y1, y2, M14.s1.isk(y1, y2, Eq.and.left(U32.is_eq(y1, y2),
        Bool.and(U32.is_eq(m1, m2), U32.is_eq(d1, d2)), hh))),
        Equal.trans(T.Date, T.Date{y2, m1, d1}, T.Date{y2, m2, d1}, T.Date{y2, m2, d2},
          Equal.cong(U32, T.Date, xx => T.Date{y2, xx, d1}, m1, m2, M14.s1.isk(m1, m2, Eq.and.left(U32.is_eq(m1, m2),
          U32.is_eq(d1, d2), h2))),
          Equal.cong(U32, T.Date, xx => T.Date{y2, m2, xx}, d1, d2, M14.s1.isk(d1, d2, Eq.and.right(U32.is_eq(m1, m2),
          U32.is_eq(d1, d2), h2)))))

# two clocks clock.eq takes for one are one
def vl.eq.clock(aa: T.Clock, bb: T.Clock, +hh: {D3.clock.eq(aa, bb) == True{} : Bool}) -> {aa == bb : T.Clock}:
  match aa bb:
    case T.Clock{+h1, +m1, +s1, +f1} T.Clock{+h2, +m2, +s2, +f2}:
      +r1 = {Eq.and.right(U32.is_eq(h1, h2), Bool.and(U32.is_eq(m1, m2), Bool.and(U32.is_eq(s1, s2), String.eq(f1,
        f2))), hh) : {Bool.and(U32.is_eq(m1, m2), Bool.and(U32.is_eq(s1, s2), String.eq(f1, f2))) == True{} : Bool}}
      +r2 = {Eq.and.right(U32.is_eq(m1, m2), Bool.and(U32.is_eq(s1, s2), String.eq(f1, f2)), r1)
        : {Bool.and(U32.is_eq(s1, s2), String.eq(f1, f2)) == True{} : Bool}}
      Equal.trans(T.Clock, T.Clock{h1, m1, s1, f1}, T.Clock{h2, m1, s1, f1}, T.Clock{h2, m2, s2, f2},
        Equal.cong(U32, T.Clock, xx => T.Clock{xx, m1, s1, f1}, h1, h2, M14.s1.isk(h1, h2, Eq.and.left(U32.is_eq(h1,
            h2),
        Bool.and(U32.is_eq(m1, m2), Bool.and(U32.is_eq(s1, s2), String.eq(f1, f2))), hh))),
        Equal.trans(T.Clock, T.Clock{h2, m1, s1, f1}, T.Clock{h2, m2, s1, f1}, T.Clock{h2, m2, s2, f2},
          Equal.cong(U32, T.Clock, xx => T.Clock{h2, xx, s1, f1}, m1, m2, M14.s1.isk(m1, m2, Eq.and.left(U32.is_eq(m1,
              m2),
          Bool.and(U32.is_eq(s1, s2), String.eq(f1, f2)), r1))),
          Equal.trans(T.Clock, T.Clock{h2, m2, s1, f1}, T.Clock{h2, m2, s2, f1}, T.Clock{h2, m2, s2, f2},
            Equal.cong(U32, T.Clock, xx => T.Clock{h2, m2, xx, f1}, s1, s2, M14.s1.isk(s1, s2, Eq.and.left(U32.is_eq(s1,
            s2), String.eq(f1, f2), r2))),
            Equal.cong(String, T.Clock, xx => T.Clock{h2, m2, s2, xx}, f1, f2, M3.vl.str.eq(f1, f2, Eq.and.right(
            U32.is_eq(s1, s2), String.eq(f1, f2), r2))))))

# two zones zone.eq takes for one are one
def vl.eq.zone(aa: T.Zone, bb: T.Zone, +hh: {D3.zone.eq(aa, bb) == True{} : Bool}) -> {aa == bb : T.Zone}:
  match aa bb:
    case T.Zulu{} T.Zulu{}:
      {==}
    case T.Shift{+g1, +h1, +m1} T.Shift{+g2, +h2, +m2}:
      +r1 = {Eq.and.right(D3.sign.eq(g1, g2), Bool.and(U32.is_eq(h1, h2), U32.is_eq(m1, m2)), hh)
        : {Bool.and(U32.is_eq(h1, h2), U32.is_eq(m1, m2)) == True{} : Bool}}
      Equal.trans(T.Zone, T.Shift{g1, h1, m1}, T.Shift{g2, h1, m1}, T.Shift{g2, h2, m2},
        Equal.cong(T.Sign, T.Zone, xx => T.Shift{xx, h1, m1}, g1, g2, M8.n1.sign.eq(g1, g2, Eq.and.left(D3.sign.eq(g1,
        g2), Bool.and(U32.is_eq(h1, h2), U32.is_eq(m1, m2)), hh))),
        Equal.trans(T.Zone, T.Shift{g2, h1, m1}, T.Shift{g2, h2, m1}, T.Shift{g2, h2, m2},
          Equal.cong(U32, T.Zone, xx => T.Shift{g2, xx, m1}, h1, h2, M14.s1.isk(h1, h2, Eq.and.left(U32.is_eq(h1, h2),
          U32.is_eq(m1, m2), r1))),
          Equal.cong(U32, T.Zone, xx => T.Shift{g2, h2, xx}, m1, m2, M14.s1.isk(m1, m2, Eq.and.right(U32.is_eq(h1, h2),
          U32.is_eq(m1, m2), r1)))))
    case T.Zulu{} T.Shift{g2, h2, m2}:
      Eq.bit.absurd(&2, {T.Zulu{} == T.Shift{g2, h2, m2} : T.Zone}, hh)
    case T.Shift{g1, h1, m1} T.Zulu{}:
      Eq.bit.absurd(&2, {T.Shift{g1, h1, m1} == T.Zulu{} : T.Zone}, hh)

# two datetimes when.eq takes for one are one
def vl.eq.w(aa: T.When, bb: T.When, +hh: {D3.when.eq(aa, bb) == True{} : Bool}) -> {aa == bb : T.When}:
  match aa bb:
    case T.WOff{+d1, +c1, +z1} T.WOff{+d2, +c2, +z2}:
      +r1 = {Eq.and.right(D3.date.eq(d1, d2), Bool.and(D3.clock.eq(c1, c2), D3.zone.eq(z1, z2)), hh)
        : {Bool.and(D3.clock.eq(c1, c2), D3.zone.eq(z1, z2)) == True{} : Bool}}
      Equal.trans(T.When, T.WOff{d1, c1, z1}, T.WOff{d2, c1, z1}, T.WOff{d2, c2, z2},
        Equal.cong(T.Date, T.When, xx => T.WOff{xx, c1, z1}, d1, d2, vl.eq.date(d1, d2, Eq.and.left(D3.date.eq(d1,
        d2), Bool.and(D3.clock.eq(c1, c2), D3.zone.eq(z1, z2)), hh))),
        Equal.trans(T.When, T.WOff{d2, c1, z1}, T.WOff{d2, c2, z1}, T.WOff{d2, c2, z2},
          Equal.cong(T.Clock, T.When, xx => T.WOff{d2, xx, z1}, c1, c2, vl.eq.clock(c1, c2, Eq.and.left(
          D3.clock.eq(c1, c2), D3.zone.eq(z1, z2), r1))),
          Equal.cong(T.Zone, T.When, xx => T.WOff{d2, c2, xx}, z1, z2, vl.eq.zone(z1, z2, Eq.and.right(
          D3.clock.eq(c1, c2), D3.zone.eq(z1, z2), r1)))))
    case T.WLocal{+d1, +c1} T.WLocal{+d2, +c2}:
      Equal.trans(T.When, T.WLocal{d1, c1}, T.WLocal{d2, c1}, T.WLocal{d2, c2},
        Equal.cong(T.Date, T.When, xx => T.WLocal{xx, c1}, d1, d2, vl.eq.date(d1, d2, Eq.and.left(D3.date.eq(d1, d2),
        D3.clock.eq(c1, c2), hh))),
        Equal.cong(T.Clock, T.When, xx => T.WLocal{d2, xx}, c1, c2, vl.eq.clock(c1, c2, Eq.and.right(D3.date.eq(d1,
        d2), D3.clock.eq(c1, c2), hh))))
    case T.WDate{+d1} T.WDate{+d2}:
      Equal.cong(T.Date, T.When, xx => T.WDate{xx}, d1, d2, vl.eq.date(d1, d2, hh))
    case T.WTime{+c1} T.WTime{+c2}:
      Equal.cong(T.Clock, T.When, xx => T.WTime{xx}, c1, c2, vl.eq.clock(c1, c2, hh))
    case T.WOff{_a, _b, _c} T.WLocal{_x, _y}:
      Eq.bit.absurd(&2, {T.WOff{_a, _b, _c} == T.WLocal{_x, _y} : T.When}, hh)
    case T.WOff{_a, _b, _c} T.WDate{_x}:
      Eq.bit.absurd(&2, {T.WOff{_a, _b, _c} == T.WDate{_x} : T.When}, hh)
    case T.WOff{_a, _b, _c} T.WTime{_x}:
      Eq.bit.absurd(&2, {T.WOff{_a, _b, _c} == T.WTime{_x} : T.When}, hh)
    case T.WLocal{_a, _b} T.WOff{_x, _y, _z}:
      Eq.bit.absurd(&2, {T.WLocal{_a, _b} == T.WOff{_x, _y, _z} : T.When}, hh)
    case T.WLocal{_a, _b} T.WDate{_x}:
      Eq.bit.absurd(&2, {T.WLocal{_a, _b} == T.WDate{_x} : T.When}, hh)
    case T.WLocal{_a, _b} T.WTime{_x}:
      Eq.bit.absurd(&2, {T.WLocal{_a, _b} == T.WTime{_x} : T.When}, hh)
    case T.WDate{_a} T.WOff{_x, _y, _z}:
      Eq.bit.absurd(&2, {T.WDate{_a} == T.WOff{_x, _y, _z} : T.When}, hh)
    case T.WDate{_a} T.WLocal{_x, _y}:
      Eq.bit.absurd(&2, {T.WDate{_a} == T.WLocal{_x, _y} : T.When}, hh)
    case T.WDate{_a} T.WTime{_x}:
      Eq.bit.absurd(&2, {T.WDate{_a} == T.WTime{_x} : T.When}, hh)
    case T.WTime{_a} T.WOff{_x, _y, _z}:
      Eq.bit.absurd(&2, {T.WTime{_a} == T.WOff{_x, _y, _z} : T.When}, hh)
    case T.WTime{_a} T.WLocal{_x, _y}:
      Eq.bit.absurd(&2, {T.WTime{_a} == T.WLocal{_x, _y} : T.When}, hh)
    case T.WTime{_a} T.WDate{_x}:
      Eq.bit.absurd(&2, {T.WTime{_a} == T.WDate{_x} : T.When}, hh)

# a bare word's reading that t1.got_when takes for ww is ww
def vl.eq.when(
  gg: T.Got,
  ww: T.When,
  hh: {Laws.t1.got_when(gg, ww) == True{} : Bool}
) -> {gg == T.GotVal{T.VWhen{ww}} : T.Got}:
  match gg:
    case T.GotVal{g1}:
      match g1:
        case T.VWhen{+w1}:
          Equal.cong(T.When, T.Got, xx => T.GotVal{T.VWhen{xx}}, w1, ww, Equal.sym(T.When, ww, w1, vl.eq.w(ww, w1, hh)))
        case T.VStr{_a}:
          Eq.bit.absurd(&2, {T.GotVal{T.VStr{_a}} == T.GotVal{T.VWhen{ww}} : T.Got}, hh)
        case T.VSpan{_a, _b}:
          Eq.bit.absurd(&2, {T.GotVal{T.VSpan{_a, _b}} == T.GotVal{T.VWhen{ww}} : T.Got}, hh)
        case T.VInt{_a, _b}:
          Eq.bit.absurd(&2, {T.GotVal{T.VInt{_a, _b}} == T.GotVal{T.VWhen{ww}} : T.Got}, hh)
        case T.VFlo{_a, _b}:
          Eq.bit.absurd(&2, {T.GotVal{T.VFlo{_a, _b}} == T.GotVal{T.VWhen{ww}} : T.Got}, hh)
        case T.VBool{_a}:
          Eq.bit.absurd(&2, {T.GotVal{T.VBool{_a}} == T.GotVal{T.VWhen{ww}} : T.Got}, hh)
        case T.VArr{_a}:
          Eq.bit.absurd(&2, {T.GotVal{T.VArr{_a}} == T.GotVal{T.VWhen{ww}} : T.Got}, hh)
        case T.VInl{_a}:
          Eq.bit.absurd(&2, {T.GotVal{T.VInl{_a}} == T.GotVal{T.VWhen{ww}} : T.Got}, hh)
        case T.VHead{_a, _b}:
          Eq.bit.absurd(&2, {T.GotVal{T.VHead{_a, _b}} == T.GotVal{T.VWhen{ww}} : T.Got}, hh)
        case T.VAot{_a, _b}:
          Eq.bit.absurd(&2, {T.GotVal{T.VAot{_a, _b}} == T.GotVal{T.VWhen{ww}} : T.Got}, hh)
        case T.VAots{_a, _b}:
          Eq.bit.absurd(&2, {T.GotVal{T.VAots{_a, _b}} == T.GotVal{T.VWhen{ww}} : T.Got}, hh)
        case T.VPair{_a, _b}:
          Eq.bit.absurd(&2, {T.GotVal{T.VPair{_a, _b}} == T.GotVal{T.VWhen{ww}} : T.Got}, hh)
    case T.GotBad{why}:
      Eq.bit.absurd(&2, {T.GotBad{why} == T.GotVal{T.VWhen{ww}} : T.Got}, hh)

# a word a date-time rule matches within the ranges, denoting the datetime
# ww, reads as ww
def vl.hv.dt(
  +cs: List<&2, Char>,
  +hw: {D1.g.ok.val(D4.GvDateTime{cs}, D1.RVal{}) == True{} : Bool},
  +ww: T.When,
  +hv: {D1.g.val(D4.GvDateTime{cs}, T.VWhen{ww}) == True{} : Bool}
) -> {T.word.val(cs) == T.GotVal{T.VWhen{ww}} : T.Got}:
  vl.eq.when(T.word.val(cs), ww, Equal.trans(Bool, Laws.t1.got_when(T.word.val(cs), ww), Bool.and(D1.g.ok.val(
    D4.GvDateTime{cs}, D1.RVal{}), D1.g.val(D4.GvDateTime{cs}, T.VWhen{ww})), True{}, Laws.date_time_word(cs,
    ww), M11.and.tt(D1.g.ok.val(D4.GvDateTime{cs}, D1.RVal{}), D1.g.val(D4.GvDateTime{cs}, T.VWhen{ww}), hw,
    hv)))

def Laws.date_time_parses_as_denoted(k, ek, w, hw, v, hv):
  match v:
    case T.VStr{_a}:
      Eq.bit.absurd(&2, {T.parse(D1.bw.kv(k, w)) == T.Doc{"", [T.VPair{k, T.VStr{_a}}]} : T.Doc}, hv)
    case T.VSpan{_a, _b}:
      Eq.bit.absurd(&2, {T.parse(D1.bw.kv(k, w)) == T.Doc{"", [T.VPair{k, T.VSpan{_a, _b}}]} : T.Doc}, hv)
    case T.VInt{_a, _b}:
      Eq.bit.absurd(&2, {T.parse(D1.bw.kv(k, w)) == T.Doc{"", [T.VPair{k, T.VInt{_a, _b}}]} : T.Doc}, hv)
    case T.VFlo{_a, _b}:
      Eq.bit.absurd(&2, {T.parse(D1.bw.kv(k, w)) == T.Doc{"", [T.VPair{k, T.VFlo{_a, _b}}]} : T.Doc}, hv)
    case T.VBool{_a}:
      Eq.bit.absurd(&2, {T.parse(D1.bw.kv(k, w)) == T.Doc{"", [T.VPair{k, T.VBool{_a}}]} : T.Doc}, hv)
    case T.VWhen{+ww}:
      M3.vl.acc.v(k, ek, w, Laws.date_time_is_bare_word(w, Eq.and.left(D1.abnf.date_time(String.to_list(w)),
          D1.prose.date_time_in_range(String.to_list(w)), hw)), T.VWhen{ww}, vl.hv.dt(String.to_list(w), hw, ww, hv),
          M3.vl.sc.of(String.to_list(w), T.VWhen{ww}, vl.hv.dt(String.to_list(w), hw, ww, hv)))
    case T.VArr{_a}:
      Eq.bit.absurd(&2, {T.parse(D1.bw.kv(k, w)) == T.Doc{"", [T.VPair{k, T.VArr{_a}}]} : T.Doc}, hv)
    case T.VInl{_a}:
      Eq.bit.absurd(&2, {T.parse(D1.bw.kv(k, w)) == T.Doc{"", [T.VPair{k, T.VInl{_a}}]} : T.Doc}, hv)
    case T.VHead{_a, _b}:
      Eq.bit.absurd(&2, {T.parse(D1.bw.kv(k, w)) == T.Doc{"", [T.VPair{k, T.VHead{_a, _b}}]} : T.Doc}, hv)
    case T.VAot{_a, _b}:
      Eq.bit.absurd(&2, {T.parse(D1.bw.kv(k, w)) == T.Doc{"", [T.VPair{k, T.VAot{_a, _b}}]} : T.Doc}, hv)
    case T.VAots{_a, _b}:
      Eq.bit.absurd(&2, {T.parse(D1.bw.kv(k, w)) == T.Doc{"", [T.VPair{k, T.VAots{_a, _b}}]} : T.Doc}, hv)
    case T.VPair{_a, _b}:
      Eq.bit.absurd(&2, {T.parse(D1.bw.kv(k, w)) == T.Doc{"", [T.VPair{k, T.VPair{_a, _b}}]} : T.Doc}, hv)

def Laws.date_time_parses_as_denoted_in_array(k, ek, w, hw, v, hv):
  match v:
    case T.VStr{_a}:
      Eq.bit.absurd(&2, {T.parse(D1.bw.kva(k, w)) == T.Doc{"", [T.VPair{k, T.VArr{[T.VStr{_a}]}}]} : T.Doc}, hv)
    case T.VSpan{_a, _b}:
      Eq.bit.absurd(&2, {T.parse(D1.bw.kva(k, w)) == T.Doc{"", [T.VPair{k, T.VArr{[T.VSpan{_a, _b}]}}]} : T.Doc}, hv)
    case T.VInt{_a, _b}:
      Eq.bit.absurd(&2, {T.parse(D1.bw.kva(k, w)) == T.Doc{"", [T.VPair{k, T.VArr{[T.VInt{_a, _b}]}}]} : T.Doc}, hv)
    case T.VFlo{_a, _b}:
      Eq.bit.absurd(&2, {T.parse(D1.bw.kva(k, w)) == T.Doc{"", [T.VPair{k, T.VArr{[T.VFlo{_a, _b}]}}]} : T.Doc}, hv)
    case T.VBool{_a}:
      Eq.bit.absurd(&2, {T.parse(D1.bw.kva(k, w)) == T.Doc{"", [T.VPair{k, T.VArr{[T.VBool{_a}]}}]} : T.Doc}, hv)
    case T.VWhen{+ww}:
      M1.vl.acc.a(k, ek, w, Laws.date_time_is_bare_word(w, Eq.and.left(D1.abnf.date_time(String.to_list(w)),
          D1.prose.date_time_in_range(String.to_list(w)), hw)), T.VWhen{ww}, vl.hv.dt(String.to_list(w), hw, ww, hv),
          M3.vl.sc.of(String.to_list(w), T.VWhen{ww}, vl.hv.dt(String.to_list(w), hw, ww, hv)))
    case T.VArr{_a}:
      Eq.bit.absurd(&2, {T.parse(D1.bw.kva(k, w)) == T.Doc{"", [T.VPair{k, T.VArr{[T.VArr{_a}]}}]} : T.Doc}, hv)
    case T.VInl{_a}:
      Eq.bit.absurd(&2, {T.parse(D1.bw.kva(k, w)) == T.Doc{"", [T.VPair{k, T.VArr{[T.VInl{_a}]}}]} : T.Doc}, hv)
    case T.VHead{_a, _b}:
      Eq.bit.absurd(&2, {T.parse(D1.bw.kva(k, w)) == T.Doc{"", [T.VPair{k, T.VArr{[T.VHead{_a, _b}]}}]} : T.Doc}, hv)
    case T.VAot{_a, _b}:
      Eq.bit.absurd(&2, {T.parse(D1.bw.kva(k, w)) == T.Doc{"", [T.VPair{k, T.VArr{[T.VAot{_a, _b}]}}]} : T.Doc}, hv)
    case T.VAots{_a, _b}:
      Eq.bit.absurd(&2, {T.parse(D1.bw.kva(k, w)) == T.Doc{"", [T.VPair{k, T.VArr{[T.VAots{_a, _b}]}}]} : T.Doc}, hv)
    case T.VPair{_a, _b}:
      Eq.bit.absurd(&2, {T.parse(D1.bw.kva(k, w)) == T.Doc{"", [T.VPair{k, T.VArr{[T.VPair{_a, _b}]}}]} : T.Doc}, hv)

def Laws.date_time_parses_as_denoted_in_inline_table(k, ek, w, hw, v, hv):
  match v:
    case T.VStr{_a}:
      Eq.bit.absurd(&2, {T.parse(D1.bw.kvi(k, w)) == T.Doc{"", [T.VPair{k, T.VInl{[T.VPair{"v", T.VStr{_a}}]}}]} :
          T.Doc}, hv)
    case T.VSpan{_a, _b}:
      Eq.bit.absurd(&2, {T.parse(D1.bw.kvi(k, w)) == T.Doc{"", [T.VPair{k, T.VInl{[T.VPair{"v", T.VSpan{_a, _b}}]}}]}
          : T.Doc}, hv)
    case T.VInt{_a, _b}:
      Eq.bit.absurd(&2, {T.parse(D1.bw.kvi(k, w)) == T.Doc{"", [T.VPair{k, T.VInl{[T.VPair{"v", T.VInt{_a, _b}}]}}]} :
          T.Doc}, hv)
    case T.VFlo{_a, _b}:
      Eq.bit.absurd(&2, {T.parse(D1.bw.kvi(k, w)) == T.Doc{"", [T.VPair{k, T.VInl{[T.VPair{"v", T.VFlo{_a, _b}}]}}]} :
          T.Doc}, hv)
    case T.VBool{_a}:
      Eq.bit.absurd(&2, {T.parse(D1.bw.kvi(k, w)) == T.Doc{"", [T.VPair{k, T.VInl{[T.VPair{"v", T.VBool{_a}}]}}]} :
          T.Doc}, hv)
    case T.VWhen{+ww}:
      M3.vl.acc.i(k, ek, w, Laws.date_time_is_bare_word(w, Eq.and.left(D1.abnf.date_time(String.to_list(w)),
          D1.prose.date_time_in_range(String.to_list(w)), hw)), T.VWhen{ww}, vl.hv.dt(String.to_list(w), hw, ww, hv),
          M3.vl.sc.of(String.to_list(w), T.VWhen{ww}, vl.hv.dt(String.to_list(w), hw, ww, hv)))
    case T.VArr{_a}:
      Eq.bit.absurd(&2, {T.parse(D1.bw.kvi(k, w)) == T.Doc{"", [T.VPair{k, T.VInl{[T.VPair{"v", T.VArr{_a}}]}}]} :
          T.Doc}, hv)
    case T.VInl{_a}:
      Eq.bit.absurd(&2, {T.parse(D1.bw.kvi(k, w)) == T.Doc{"", [T.VPair{k, T.VInl{[T.VPair{"v", T.VInl{_a}}]}}]} :
          T.Doc}, hv)
    case T.VHead{_a, _b}:
      Eq.bit.absurd(&2, {T.parse(D1.bw.kvi(k, w)) == T.Doc{"", [T.VPair{k, T.VInl{[T.VPair{"v", T.VHead{_a, _b}}]}}]}
          : T.Doc}, hv)
    case T.VAot{_a, _b}:
      Eq.bit.absurd(&2, {T.parse(D1.bw.kvi(k, w)) == T.Doc{"", [T.VPair{k, T.VInl{[T.VPair{"v", T.VAot{_a, _b}}]}}]} :
          T.Doc}, hv)
    case T.VAots{_a, _b}:
      Eq.bit.absurd(&2, {T.parse(D1.bw.kvi(k, w)) == T.Doc{"", [T.VPair{k, T.VInl{[T.VPair{"v", T.VAots{_a, _b}}]}}]}
          : T.Doc}, hv)
    case T.VPair{_a, _b}:
      Eq.bit.absurd(&2, {T.parse(D1.bw.kvi(k, w)) == T.Doc{"", [T.VPair{k, T.VInl{[T.VPair{"v", T.VPair{_a, _b}}]}}]}
          : T.Doc}, hv)
