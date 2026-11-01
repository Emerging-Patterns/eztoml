# a date-time is a bare word, with the step patterns of its date and time
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/DateTimeReadExactly.bend as L1
import ../../laws/defs/AbnfGrammar.bend as D1
import ../../laws/defs/BareValueGrammar.bend as D2
import ./BareValueCharTests.bend as M1
import ./BareWordReadsOn.bend as M2
import ./BooleanIsBareWord.bend as M3
import ./DigitsWrittenBack.bend as M4
import ./GrammarWordMatching.bend as M5
import ./PrefixAndTake.bend as M6

# The date-time rules. Every character they take starts a bare value but the
# space of time-delim, so a word with a character that does not keeps one
# after every rule but that space (as t1.e does for an exponent mark), and
# no such rule matches it whole.

# what a rule left of a word still holds a character that starts no bare
# value, or it matched nothing
def vl.zb(rr: D1.ARest) -> Bool:
  match rr:
    case D1.ALeft{cs}:
      Bool.not(M3.vl.qs(cs))
    case D1.ANone{}:
      True{}

# a character that starts a bare value, taken, leaves the others
def vl.z.tail(
  +xx: Char,
  +tt: List<&2, Char>,
  hw: {D2.word.first(xx) == True{} : Bool},
  hz: {Bool.not(M3.vl.qs(xx <> tt)) == True{} : Bool}
) -> {Bool.not(M3.vl.qs(tt)) == True{} : Bool}:
  Equal.trans(Bool, Bool.not(M3.vl.qs(tt)), Bool.not(Bool.and(D2.word.first(xx), M3.vl.qs(tt))), True{},
    Equal.cong(Bool, Bool, bb => Bool.not(Bool.and(bb, M3.vl.qs(tt))), True{}, D2.word.first(xx), Equal.sym(Bool,
    D2.word.first(xx), True{}, hw)), hz)

# a character a test took starts a bare value, so what is left keeps one
def vl.z.keep(
  bb: Bool,
  +xx: Char,
  +tt: List<&2, Char>,
  hb: {bb == True{} : Bool} -> {D2.word.first(xx) == True{} : Bool},
  hz: {Bool.not(M3.vl.qs(xx <> tt)) == True{} : Bool}
) -> {vl.zb(D1.abnf.keep(bb, tt)) == True{} : Bool}:
  match bb:
    case True{}:
      vl.z.tail(xx, tt, hb({==}), hz)
    case False{}:
      {==}

# DIGIT from the front
def vl.z.dr(rr: D1.ARest, hz: {vl.zb(rr) == True{} : Bool}) -> {vl.zb(D1.abnf.digit_r(rr)) == True{} : Bool}:
  match rr:
    case D1.ALeft{cs}:
      match cs:
        case []:
          {==}
        case +xx <> +tt:
          vl.z.keep(D1.abnf.DIGIT(xx), xx, tt, hd => M1.vl.q.dig(xx, hd), hz)
    case D1.ANone{}:
      {==}

# a character by its code point, one that starts a bare value
def vl.z.cr(
  rr: D1.ARest,
  +nn: U32,
  +hn: {D2.word.first(Chr{nn}) == True{} : Bool},
  hz: {vl.zb(rr) == True{} : Bool}
) -> {vl.zb(D1.abnf.char_r(rr, nn)) == True{} : Bool}:
  match rr:
    case D1.ALeft{cs}:
      match cs:
        case []:
          {==}
        case +xx <> +tt:
          vl.z.keep(D1.abnf.cp(xx, nn), xx, tt, hc => M1.vl.q.cp(xx, nn, hc, hn), hz)
    case D1.ANone{}:
      {==}

# a quoted letter, both of whose cases start a bare value
def vl.z.lr(
  rr: D1.ARest,
  +up: U32,
  +low: U32,
  +hu: {D2.word.first(Chr{up}) == True{} : Bool},
  +hl: {D2.word.first(Chr{low}) == True{} : Bool},
  hz: {vl.zb(rr) == True{} : Bool}
) -> {vl.zb(D1.abnf.letter_r(rr, up, low)) == True{} : Bool}:
  match rr:
    case D1.ALeft{cs}:
      match cs:
        case []:
          {==}
        case +xx <> +tt:
          vl.z.keep(Bool.or(D1.abnf.cp(xx, up), D1.abnf.cp(xx, low)), xx, tt, hc => M5.gp.or({D2.word.first(xx)
            == True{} : Bool}, D1.abnf.cp(xx, up), D1.abnf.cp(xx, low), hc, h1 => M1.vl.q.cp(xx, up, h1, hu),
            h2 => M1.vl.q.cp(xx, low, h2, hl)), hz)
    case D1.ANone{}:
      {==}

# the first of two alternatives
def vl.z.or(
  aa: D1.ARest,
  bb: D1.ARest,
  ha: {vl.zb(aa) == True{} : Bool},
  hb: {vl.zb(bb) == True{} : Bool}
) -> {vl.zb(D1.abnf.or_r(aa, bb)) == True{} : Bool}:
  match aa:
    case D1.ALeft{_cs}:
      ha
    case D1.ANone{}:
      hb

# the step of vl.z.dd: a DIGIT dropped, or the word kept
def vl.z.dd.go(
  dg: Bool,
  +xx: Char,
  +tt: List<&2, Char>,
  ed: {D1.abnf.DIGIT(xx) == dg : Bool},
  hz: {Bool.not(M3.vl.qs(xx <> tt)) == True{} : Bool},
  ih: {Bool.not(M3.vl.qs(tt)) == True{} : Bool} -> {Bool.not(M3.vl.qs(D1.abnf.drop_digits(tt))) == True{} : Bool}
) -> {Bool.not(M3.vl.qs(D1.abnf.drop_digits.pick(dg, xx, tt, D1.abnf.drop_digits(tt)))) == True{} : Bool}:
  match dg:
    case True{}:
      ih(vl.z.tail(xx, tt, M1.vl.q.dig(xx, ed), hz))
    case False{}:
      hz

# leading DIGITs dropped leave such a character
def vl.z.dd(
  cs: List<&2, Char>,
  hz: {Bool.not(M3.vl.qs(cs)) == True{} : Bool}
) -> {Bool.not(M3.vl.qs(D1.abnf.drop_digits(cs))) == True{} : Bool}:
  match cs:
    case []:
      hz
    case +xx <> +tt:
      vl.z.dd.go(D1.abnf.DIGIT(xx), xx, tt, {==}, hz, h1 => vl.z.dd(tt, h1))

# the first DIGIT of 1*DIGIT, then the rest dropped
def vl.z.d1.go(
  dg: Bool,
  +xx: Char,
  +tt: List<&2, Char>,
  ed: {D1.abnf.DIGIT(xx) == dg : Bool},
  hz: {Bool.not(M3.vl.qs(xx <> tt)) == True{} : Bool}
) -> {vl.zb(D1.abnf.keep(dg, D1.abnf.drop_digits(tt))) == True{} : Bool}:
  match dg:
    case True{}:
      vl.z.dd(tt, vl.z.tail(xx, tt, M1.vl.q.dig(xx, ed), hz))
    case False{}:
      {==}

# 1*DIGIT
def vl.z.d1(rr: D1.ARest, hz: {vl.zb(rr) == True{} : Bool}) -> {vl.zb(D1.abnf.digits1_r(rr)) == True{} : Bool}:
  match rr:
    case D1.ALeft{cs}:
      match cs:
        case []:
          {==}
        case +xx <> +tt:
          vl.z.d1.go(D1.abnf.DIGIT(xx), xx, tt, {==}, hz)
    case D1.ANone{}:
      {==}

# a time-secfrac, or none
def vl.z.os.go(
  dt: Bool,
  +xx: Char,
  +tt: List<&2, Char>,
  hz: {Bool.not(M3.vl.qs(xx <> tt)) == True{} : Bool}
) -> {vl.zb(D1.abnf.opt_secfrac.pick(dt, xx <> tt)) == True{} : Bool}:
  match dt:
    case True{}:
      vl.z.d1(D1.abnf.char_r(D1.ALeft{xx <> tt}, 46), vl.z.cr(D1.ALeft{xx <> tt}, 46, {==}, hz))
    case False{}:
      hz

# [ time-secfrac ]
def vl.z.os(rr: D1.ARest, hz: {vl.zb(rr) == True{} : Bool}) -> {vl.zb(D1.abnf.opt_secfrac(rr)) == True{} : Bool}:
  match rr:
    case D1.ALeft{cs}:
      match cs:
        case []:
          hz
        case +xx <> +tt:
          vl.z.os.go(D1.abnf.cp(xx, 46), xx, tt, hz)
    case D1.ANone{}:
      {==}

# two DIGITs
def vl.z.d2(
  +rr: D1.ARest,
  +hz: {vl.zb(rr) == True{} : Bool}
) -> {vl.zb(D1.abnf.digit_r(D1.abnf.digit_r(rr))) == True{} : Bool}:
  vl.z.dr(D1.abnf.digit_r(rr), vl.z.dr(rr, hz))

# full-date
def vl.z.fd(+rr: D1.ARest, +hz: {vl.zb(rr) == True{} : Bool}) -> {vl.zb(D1.abnf.full_date(rr)) == True{} : Bool}:
  vl.z.d2(D1.abnf.char_r(D1.abnf.date_month(D1.abnf.char_r(D1.abnf.date_fullyear(rr), 45)), 45),
    vl.z.cr(D1.abnf.date_month(D1.abnf.char_r(D1.abnf.date_fullyear(rr), 45)), 45, {==},
    vl.z.d2(D1.abnf.char_r(D1.abnf.date_fullyear(rr), 45), vl.z.cr(D1.abnf.date_fullyear(rr), 45, {==},
    vl.z.d2(D1.abnf.digit_r(D1.abnf.digit_r(rr)), vl.z.d2(rr, hz))))))

# partial-time
def vl.z.pt(+rr: D1.ARest, +hz: {vl.zb(rr) == True{} : Bool}) -> {vl.zb(D1.abnf.partial_time(rr)) == True{} : Bool}:
  vl.z.os(D1.abnf.time_second(D1.abnf.char_r(D1.abnf.time_minute(D1.abnf.char_r(D1.abnf.time_hour(rr), 58)),
    58)), vl.z.d2(D1.abnf.char_r(D1.abnf.time_minute(D1.abnf.char_r(D1.abnf.time_hour(rr), 58)), 58),
    vl.z.cr(D1.abnf.time_minute(D1.abnf.char_r(D1.abnf.time_hour(rr), 58)), 58, {==},
    vl.z.d2(D1.abnf.char_r(D1.abnf.time_hour(rr), 58), vl.z.cr(D1.abnf.time_hour(rr), 58, {==},
    vl.z.d2(rr, hz))))))

# time-offset
def vl.z.to(+rr: D1.ARest, +hz: {vl.zb(rr) == True{} : Bool}) -> {vl.zb(D1.abnf.time_offset(rr)) == True{} : Bool}:
  vl.z.or(D1.abnf.letter_r(rr, 90, 122), D1.abnf.time_numoffset(rr), vl.z.lr(rr, 90, 122, {==}, {==}, hz),
    vl.z.d2(D1.abnf.char_r(D1.abnf.time_hour(D1.abnf.or_r(D1.abnf.char_r(rr, 43), D1.abnf.char_r(rr, 45))),
    58), vl.z.cr(D1.abnf.time_hour(D1.abnf.or_r(D1.abnf.char_r(rr, 43), D1.abnf.char_r(rr, 45))), 58, {==},
    vl.z.d2(D1.abnf.or_r(D1.abnf.char_r(rr, 43), D1.abnf.char_r(rr, 45)), vl.z.or(D1.abnf.char_r(rr, 43),
    D1.abnf.char_r(rr, 45), vl.z.cr(rr, 43, {==}, hz), vl.z.cr(rr, 45, {==}, hz))))))

# a rule that leaves such a character matched no whole word
def vl.z.all(rr: D1.ARest, hz: {vl.zb(rr) == True{} : Bool}) -> {D1.abnf.all_r(rr) == False{} : Bool}:
  match rr:
    case D1.ALeft{cs}:
      match cs:
        case []:
          Eq.bit.absurd(&2, {D1.abnf.all_r(D1.ALeft{[]}) == False{} : Bool}, hz)
        case _xx <> _tt:
          {==}
    case D1.ANone{}:
      {==}

# a word a rule matched whole, where a character that starts no bare value
# stays, is of characters that start one
def vl.qs.of.go(
  qq: Bool,
  +cs: List<&2, Char>,
  rr: D1.ARest,
  eq: {M3.vl.qs(cs) == qq : Bool},
  hh: {D1.abnf.all_r(rr) == True{} : Bool},
  hz: {Bool.not(M3.vl.qs(cs)) == True{} : Bool} -> {vl.zb(rr) == True{} : Bool}
) -> {qq == True{} : Bool}:
  match qq:
    case True{}:
      {==}
    case False{}:
      Eq.bit.absurd(&2, {False{} == True{} : Bool}, Equal.trans(Bool, False{}, D1.abnf.all_r(rr), True{},
        Equal.sym(Bool, D1.abnf.all_r(rr), False{}, vl.z.all(rr, hz(Equal.cong(Bool, Bool, bb => Bool.not(bb),
        M3.vl.qs(cs), False{}, eq)))), hh))

# the same, for the word's own test
def vl.qs.of(
  +cs: List<&2, Char>,
  rr: D1.ARest,
  hh: {D1.abnf.all_r(rr) == True{} : Bool},
  hz: {Bool.not(M3.vl.qs(cs)) == True{} : Bool} -> {vl.zb(rr) == True{} : Bool}
) -> {M3.vl.qs(cs) == True{} : Bool}:
  vl.qs.of.go(M3.vl.qs(cs), cs, rr, {==}, hh, hz)

# A full-date read from the front is ten steps, a DIGIT or the dash each. A
# word full-date leaves some rest of is ten characters the steps take, then
# that rest (vl.walk); the ten are the date the scan's buffer is shaped as
# (vl.deq, date.shaped).

# one step of a full-date
type VStep is Data:
  VD{}
  VDash{}

# a step from the front
def vl.stp1(st: VStep, rr: D1.ARest) -> D1.ARest:
  match st:
    case VD{}:
      D1.abnf.digit_r(rr)
    case VDash{}:
      D1.abnf.char_r(rr, 45)

# steps from the front, first to last
def vl.runr(ss: List<&2, VStep>, rr: D1.ARest) -> D1.ARest:
  match ss:
    case []:
      rr
    case +st <> tt:
      vl.runr(tt, vl.stp1(st, rr))

# full-date's steps: date-fullyear "-" date-month "-" date-mday
def vl.dsteps() -> List<&2, VStep>:
  [VD{}, VD{}, VD{}, VD{}, VDash{}, VD{}, VD{}, VDash{}, VD{}, VD{}]

# whether the characters are the ones the steps take, one each
def vl.match(ss: List<&2, VStep>, pre: List<&2, Char>) -> Bool:
  match ss pre:
    case Nil{} Nil{}:
      True{}
    case VD{} <> st +cc <> pt:
      Bool.and(D1.abnf.DIGIT(cc), vl.match(st, pt))
    case VDash{} <> st +cc <> pt:
      Bool.and(D1.abnf.cp(cc, 45), vl.match(st, pt))
    case _s _p:
      False{}

# the steps as date.shaped's pattern: D for a DIGIT
def vl.pat(ss: List<&2, VStep>) -> List<&2, Char>:
  match ss:
    case []:
      []
    case VD{} <> tt:
      'D' <> vl.pat(tt)
    case VDash{} <> tt:
      '-' <> vl.pat(tt)

# no match stays no match
def vl.runr.none(ss: List<&2, VStep>) -> {vl.runr(ss, D1.ANone{}) == D1.ANone{} : D1.ARest}:
  match ss:
    case []:
      {==}
    case st <> tt:
      match st:
        case VD{}:
          vl.runr.none(tt)
        case VDash{}:
          vl.runr.none(tt)

# whether a rule matched
def vl.isl(rr: D1.ARest) -> Bool:
  match rr:
    case D1.ALeft{_cs}:
      True{}
    case D1.ANone{}:
      False{}

# what a rule left, or dd
def vl.lft(rr: D1.ARest, dd: List<&2, Char>) -> List<&2, Char>:
  match rr:
    case D1.ALeft{cs}:
      cs
    case D1.ANone{}:
      dd

# a step's test failed: the steps after it match nothing
def vl.kp(
  bb: Bool,
  +rr: List<&2, Char>,
  +tt: List<&2, VStep>,
  +ss: List<&2, Char>,
  hh: {vl.runr(tt, D1.abnf.keep(bb, rr)) == D1.ALeft{ss} : D1.ARest}
) -> {bb == True{} : Bool}:
  match bb:
    case True{}:
      {==}
    case False{}:
      Eq.bit.absurd(&2, {False{} == True{} : Bool}, Equal.cong(D1.ARest, Bool, xx => vl.isl(xx), D1.ANone{},
        D1.ALeft{ss}, Equal.trans(D1.ARest, D1.ANone{}, vl.runr(tt, D1.ANone{}), D1.ALeft{ss},
        Equal.sym(D1.ARest, vl.runr(tt, D1.ANone{}), D1.ANone{}, vl.runr.none(tt)), hh)))

# the steps from nothing match nothing
def vl.kp0(
  +tt: List<&2, VStep>,
  +ss: List<&2, Char>,
  hh: {vl.runr(tt, D1.ANone{}) == D1.ALeft{ss} : D1.ARest}
) -> {False{} == True{} : Bool}:
  Equal.cong(D1.ARest, Bool, xx => vl.isl(xx), D1.ANone{}, D1.ALeft{ss}, Equal.trans(D1.ARest, D1.ANone{},
    vl.runr(tt, D1.ANone{}), D1.ALeft{ss}, Equal.sym(D1.ARest, vl.runr(tt, D1.ANone{}), D1.ANone{},
    vl.runr.none(tt)), hh))

# a word the steps leave ss of is the characters they take, then ss: a
# claim of every such word is a claim of it
def vl.walk(
  ss: List<&2, VStep>,
  -P: List<&2, Char> -> Type,
  +cs: List<&2, Char>,
  +rest: List<&2, Char>,
  +hh: {vl.runr(ss, D1.ALeft{cs}) == D1.ALeft{rest} : D1.ARest},
  kk: @pre: List<&2, Char> -> {vl.match(ss, pre) == True{} : Bool} -> P(List.append(&2, Char, pre, rest))
) -> P(cs):
  match ss:
    case []:
      M5.gp.subst(P, cs, rest, Equal.cong(D1.ARest, List<&2, Char>, xx => vl.lft(xx, cs), D1.ALeft{cs},
        D1.ALeft{rest}, hh), kk([], {==}))
    case VD{} <> +tt:
      match cs:
        case []:
          Eq.bit.absurd(&1, P([]), vl.kp0(tt, rest, hh))
        case +cc <> +rr:
          +ed = {vl.kp(D1.abnf.DIGIT(cc), rr, tt, rest, hh) : {D1.abnf.DIGIT(cc) == True{} : Bool}}
          vl.walk(tt, zs => P(cc <> zs), rr, rest, Equal.trans(D1.ARest, vl.runr(tt, D1.abnf.keep(True{}, rr)),
            vl.runr(tt, D1.abnf.keep(D1.abnf.DIGIT(cc), rr)), D1.ALeft{rest}, Equal.cong(Bool, D1.ARest,
            bb => vl.runr(tt, D1.abnf.keep(bb, rr)), True{}, D1.abnf.DIGIT(cc), Equal.sym(Bool,
            D1.abnf.DIGIT(cc), True{}, ed)), hh),
            +pre => hm => kk(cc <> pre, M6.and.tt(D1.abnf.DIGIT(cc), vl.match(tt, pre), ed, hm)))
    case VDash{} <> +tt:
      match cs:
        case []:
          Eq.bit.absurd(&1, P([]), vl.kp0(tt, rest, hh))
        case +cc <> +rr:
          +ed = {vl.kp(D1.abnf.cp(cc, 45), rr, tt, rest, hh) : {D1.abnf.cp(cc, 45) == True{} : Bool}}
          vl.walk(tt, zs => P(cc <> zs), rr, rest, Equal.trans(D1.ARest, vl.runr(tt, D1.abnf.keep(True{}, rr)),
            vl.runr(tt, D1.abnf.keep(D1.abnf.cp(cc, 45), rr)), D1.ALeft{rest}, Equal.cong(Bool, D1.ARest,
            bb => vl.runr(tt, D1.abnf.keep(bb, rr)), True{}, D1.abnf.cp(cc, 45), Equal.sym(Bool,
            D1.abnf.cp(cc, 45), True{}, ed)), hh),
            +pre => hm => kk(cc <> pre, M6.and.tt(D1.abnf.cp(cc, 45), vl.match(tt, pre), ed, hm)))

# a digit test, then the rest, as date.eq.go and as an and
def vl.deq.go(
  bb: Bool,
  xx: Bool,
  yy: Bool,
  ee: {xx == yy : Bool}
) -> {T.date.eq.go(bb, _u => xx) == Bool.and(bb, yy) : Bool}:
  match bb:
    case True{}:
      ee
    case False{}:
      {==}

# a word is shaped as the steps' pattern exactly when the steps take it
def vl.deq(ss: List<&2, VStep>, pre: List<&2, Char>) -> {T.date.eq(pre, vl.pat(ss)) == vl.match(ss, pre) : Bool}:
  match ss:
    case []:
      match pre:
        case []:
          {==}
        case _cc <> _pt:
          {==}
    case VD{} <> +tt:
      match pre:
        case []:
          {==}
        case cc <> +pt:
          match cc:
            case Chr{+xx}:
              vl.deq.go(Char.is_digit(Chr{xx}), T.date.eq(pt, vl.pat(tt)), vl.match(tt, pt), vl.deq(tt, pt))
    case VDash{} <> +tt:
      match pre:
        case []:
          {==}
        case cc <> +pt:
          match cc:
            case Chr{+xx}:
              vl.deq.go(Char.is_eq(Chr{xx}, '-'), T.date.eq(pt, vl.pat(tt)), vl.match(tt, pt), vl.deq(tt, pt))

# every character of a list is one a bare value keeps
def vl.wcs(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      True{}
    case +hh <> tt:
      Bool.and(D2.word.char(hh), vl.wcs(tt))

# a DIGIT is kept
def vl.wc.dig(+cc: Char, +hh: {D1.abnf.DIGIT(cc) == True{} : Bool}) -> {D2.word.char(cc) == True{} : Bool}:
  Eq.and.left(D2.word.char(cc), Bool.not(Bool.or(Char.is_eq(cc, '['), Char.is_eq(cc, '{'))), M1.vl.q.dig(cc, hh))

# the characters the steps take are kept
def vl.match.wc(
  ss: List<&2, VStep>,
  pre: List<&2, Char>,
  +hh: {vl.match(ss, pre) == True{} : Bool}
) -> {vl.wcs(pre) == True{} : Bool}:
  match ss:
    case []:
      match pre:
        case []:
          {==}
        case _cc <> _pt:
          Eq.bit.absurd(&2, {vl.wcs(_cc <> _pt) == True{} : Bool}, hh)
    case VD{} <> +tt:
      match pre:
        case []:
          {==}
        case +cc <> +pt:
          M6.and.tt(D2.word.char(cc), vl.wcs(pt), vl.wc.dig(cc, Eq.and.left(D1.abnf.DIGIT(cc), vl.match(tt, pt), hh)),
            vl.match.wc(tt, pt, Eq.and.right(D1.abnf.DIGIT(cc), vl.match(tt, pt), hh)))
    case VDash{} <> +tt:
      match pre:
        case []:
          {==}
        case +cc <> +pt:
          M6.and.tt(D2.word.char(cc), vl.wcs(pt), M2.vl.chs(ch => {D2.word.char(ch) == True{} : Bool}, cc, '-',
            M4.gp.cp(cc, 45, Eq.and.left(D1.abnf.cp(cc, 45), vl.match(tt, pt), hh)), {==}),
            vl.match.wc(tt, pt, Eq.and.right(D1.abnf.cp(cc, 45), vl.match(tt, pt), hh)))

# kept characters, then more: the more read on from the buffer they leave
def vl.more.app(
  pp: List<&2, Char>,
  +ss: List<&2, Char>,
  +buf: List<&2, Char>,
  +hw: {vl.wcs(pp) == True{} : Bool}
) -> {M3.vl.morel(List.append(&2, Char, pp, ss), buf) == M3.vl.morel(ss, List.reverse.go(&2, Char, pp, buf)) : Bool}:
  match pp:
    case []:
      {==}
    case +hh <> +pt:
      Equal.trans(Bool, M3.vl.morel(List.append(&2, Char, hh <> pt, ss), buf), M3.vl.morel(List.append(&2, Char, pt,
          ss),
        hh <> buf), M3.vl.morel(ss, List.reverse.go(&2, Char, pt, hh <> buf)),
        Equal.cong(Bool, Bool, bb => Bool.and(Bool.or(bb, Bool.and(Char.is_eq(hh, ' '), Bool.and(T.date.shaped(buf),
          M3.vl.d1(List.append(&2, Char, pt, ss))))), M3.vl.morel(List.append(&2, Char, pt, ss), hh <> buf)),
          D2.word.char(hh), True{}, Eq.and.left(D2.word.char(hh), vl.wcs(pt), hw)),
        vl.more.app(pt, ss, hh <> buf, Eq.and.right(D2.word.char(hh), vl.wcs(pt), hw)))

# a full-date, a space, then a partial-time's characters: a bare word
def vl.dt.pre(
  pre: List<&2, Char>,
  +tt: List<&2, Char>,
  +hm: {vl.match(vl.dsteps(), pre) == True{} : Bool},
  +hq: {M3.vl.qs(tt) == True{} : Bool},
  +hd: {M3.vl.d1(tt) == True{} : Bool}
) -> {M3.vl.wordl(List.append(&2, Char, pre, ' ' <> tt)) == True{} : Bool}:
  match pre:
    case []:
      Eq.bit.absurd(&2, {M3.vl.wordl(List.append(&2, Char, [], ' ' <> tt)) == True{} : Bool}, hm)
    case +c1 <> +pp:
      +bb = {List.reverse.go(&2, Char, pp, [c1]) : List<&2, Char>}
      +hs = {Equal.trans(Bool, T.date.shaped(bb), T.date.eq(c1 <> pp, vl.pat(vl.dsteps())), True{},
        Equal.cong(List<&2, Char>, Bool, xs => T.date.eq(xs, vl.pat(vl.dsteps())), List.reverse(&2, Char, bb), c1 <> pp,
        M4.t1.revrev(pp, [c1])), Equal.trans(Bool, T.date.eq(c1 <> pp, vl.pat(vl.dsteps())), vl.match(vl.dsteps(),
        c1 <> pp), True{}, vl.deq(vl.dsteps(), c1 <> pp), hm)) : {T.date.shaped(bb) == True{} : Bool}}
      M6.and.tt(D2.word.first(c1), M3.vl.morel(List.append(&2, Char, pp, ' ' <> tt), [c1]), M1.vl.q.dig(c1,
        Eq.and.left(D1.abnf.DIGIT(c1), vl.match([VD{}, VD{}, VD{}, VDash{}, VD{}, VD{}, VDash{}, VD{}, VD{}], pp),
        hm)),
        Equal.trans(Bool, M3.vl.morel(List.append(&2, Char, pp, ' ' <> tt), [c1]), M3.vl.morel(' ' <> tt, bb), True{},
          vl.more.app(pp, ' ' <> tt, [c1], vl.match.wc([VD{}, VD{}, VD{}, VDash{}, VD{}, VD{}, VDash{}, VD{}, VD{}], pp,
          Eq.and.right(D1.abnf.DIGIT(c1), vl.match([VD{}, VD{}, VD{}, VDash{}, VD{}, VD{}, VDash{}, VD{}, VD{}], pp),
          hm))),
          M6.and.tt(Bool.and(T.date.shaped(bb), M3.vl.d1(tt)), M3.vl.morel(tt, ' ' <> bb), M6.and.tt(T.date.shaped(bb),
              M3.vl.d1(tt),
            hs, hd), M3.vl.qs.more(tt, ' ' <> bb, hq))))

# a word whose full-date leaves a space then tt, a partial-time's
# characters, is a bare word
def vl.dt.core(
  +cs: List<&2, Char>,
  +tt: List<&2, Char>,
  hf: {D1.abnf.full_date(D1.ALeft{cs}) == D1.ALeft{' ' <> tt} : D1.ARest},
  +hq: {M3.vl.qs(tt) == True{} : Bool},
  +hd: {M3.vl.d1(tt) == True{} : Bool}
) -> {M3.vl.wordl(cs) == True{} : Bool}:
  vl.walk(vl.dsteps(), zs => {M3.vl.wordl(zs) == True{} : Bool}, cs, ' ' <> tt, hf, pre => hm => vl.dt.pre(pre, tt, hm,
    hq, hd))

# The four date-time rules. local-date and local-time take no space, and
# neither do the other two when time-delim is T or t; when it is the space,
# full-date left it and a partial-time after it (vl.dt.core).

# partial-time after its first DIGIT
def vl.pt1(xx: D1.ARest) -> D1.ARest:
  D1.abnf.opt_secfrac(D1.abnf.time_second(D1.abnf.char_r(D1.abnf.time_minute(D1.abnf.char_r(
    D1.abnf.digit_r(xx), 58)), 58)))

# a partial-time's first character is a digit
def vl.pt.d1.c(
  bb: Bool,
  +dd: Char,
  +rr: List<&2, Char>,
  eb: {D1.abnf.DIGIT(dd) == bb : Bool},
  hh: {D1.abnf.all_r(vl.pt1(D1.abnf.keep(bb, rr))) == True{} : Bool}
) -> {M3.vl.d1(dd <> rr) == True{} : Bool}:
  match bb:
    case True{}:
      M4.gs.dig(dd, eb)
    case False{}:
      Eq.bit.absurd(&2, {M3.vl.d1(dd <> rr) == True{} : Bool}, hh)

# so a word a partial-time matches starts with a digit
def vl.pt.d1(
  tt: List<&2, Char>,
  hh: {D1.abnf.all_r(D1.abnf.partial_time(D1.ALeft{tt})) == True{} : Bool}
) -> {M3.vl.d1(tt) == True{} : Bool}:
  match tt:
    case []:
      Eq.bit.absurd(&2, {M3.vl.d1([]) == True{} : Bool}, hh)
    case +dd <> +rr:
      vl.pt.d1.c(D1.abnf.DIGIT(dd), dd, rr, {==}, hh)

# and a full-time's first character
def vl.pt.d1o.c(
  bb: Bool,
  +dd: Char,
  +rr: List<&2, Char>,
  eb: {D1.abnf.DIGIT(dd) == bb : Bool},
  hh: {D1.abnf.all_r(D1.abnf.time_offset(vl.pt1(D1.abnf.keep(bb, rr)))) == True{} : Bool}
) -> {M3.vl.d1(dd <> rr) == True{} : Bool}:
  match bb:
    case True{}:
      M4.gs.dig(dd, eb)
    case False{}:
      Eq.bit.absurd(&2, {M3.vl.d1(dd <> rr) == True{} : Bool}, hh)

# so a word a full-time matches starts with a digit
def vl.pt.d1o(
  tt: List<&2, Char>,
  hh: {D1.abnf.all_r(D1.abnf.time_offset(D1.abnf.partial_time(D1.ALeft{tt}))) == True{} : Bool}
) -> {M3.vl.d1(tt) == True{} : Bool}:
  match tt:
    case []:
      Eq.bit.absurd(&2, {M3.vl.d1([]) == True{} : Bool}, hh)
    case +dd <> +rr:
      vl.pt.d1o.c(D1.abnf.DIGIT(dd), dd, rr, {==}, hh)

# local-date-time with a space: the space is time-delim's
def vl.dt.sp2.c(
  bb: Bool,
  +h1: Char,
  +tt: List<&2, Char>,
  +cs: List<&2, Char>,
  eb: {D1.abnf.cp(h1, 32) == bb : Bool},
  ef: {D1.abnf.full_date(D1.ALeft{cs}) == D1.ALeft{h1 <> tt} : D1.ARest},
  +hh: {D1.abnf.all_r(D1.abnf.partial_time(D1.abnf.keep(bb, tt))) == True{} : Bool}
) -> {M3.vl.wordl(cs) == True{} : Bool}:
  match bb:
    case True{}:
      vl.dt.core(cs, tt, Equal.trans(D1.ARest, D1.abnf.full_date(D1.ALeft{cs}), D1.ALeft{h1 <> tt},
        D1.ALeft{' ' <> tt}, ef, Equal.cong(Char, D1.ARest, ch => D1.ALeft{ch <> tt}, h1, ' ', M4.gp.cp(h1, 32,
          eb))),
        vl.qs.of(tt, D1.abnf.partial_time(D1.ALeft{tt}), hh, hn => vl.z.pt(D1.ALeft{tt}, hn)), vl.pt.d1(tt, hh))
    case False{}:
      Eq.bit.absurd(&2, {M3.vl.wordl(cs) == True{} : Bool}, hh)

# what full-date left, then the space
def vl.dt.sp2.go(
  fd: D1.ARest,
  +cs: List<&2, Char>,
  ef: {D1.abnf.full_date(D1.ALeft{cs}) == fd : D1.ARest},
  hh: {D1.abnf.all_r(D1.abnf.partial_time(D1.abnf.char_r(fd, 32))) == True{} : Bool}
) -> {M3.vl.wordl(cs) == True{} : Bool}:
  match fd:
    case D1.ALeft{ss}:
      match ss:
        case []:
          Eq.bit.absurd(&2, {M3.vl.wordl(cs) == True{} : Bool}, hh)
        case +h1 <> +tt:
          vl.dt.sp2.c(D1.abnf.cp(h1, 32), h1, tt, cs, {==}, ef, hh)
    case D1.ANone{}:
      Eq.bit.absurd(&2, {M3.vl.wordl(cs) == True{} : Bool}, hh)

# offset-date-time with a space
def vl.dt.sp1.c(
  bb: Bool,
  +h1: Char,
  +tt: List<&2, Char>,
  +cs: List<&2, Char>,
  eb: {D1.abnf.cp(h1, 32) == bb : Bool},
  ef: {D1.abnf.full_date(D1.ALeft{cs}) == D1.ALeft{h1 <> tt} : D1.ARest},
  +hh: {D1.abnf.all_r(D1.abnf.time_offset(D1.abnf.partial_time(D1.abnf.keep(bb, tt)))) == True{} : Bool}
) -> {M3.vl.wordl(cs) == True{} : Bool}:
  match bb:
    case True{}:
      vl.dt.core(cs, tt, Equal.trans(D1.ARest, D1.abnf.full_date(D1.ALeft{cs}), D1.ALeft{h1 <> tt},
        D1.ALeft{' ' <> tt}, ef, Equal.cong(Char, D1.ARest, ch => D1.ALeft{ch <> tt}, h1, ' ', M4.gp.cp(h1, 32,
          eb))),
        vl.qs.of(tt, D1.abnf.time_offset(D1.abnf.partial_time(D1.ALeft{tt})), hh, hn => vl.z.to(
        D1.abnf.partial_time(D1.ALeft{tt}), vl.z.pt(D1.ALeft{tt}, hn))), vl.pt.d1o(tt, hh))
    case False{}:
      Eq.bit.absurd(&2, {M3.vl.wordl(cs) == True{} : Bool}, hh)

# what full-date left, then the space
def vl.dt.sp1.go(
  fd: D1.ARest,
  +cs: List<&2, Char>,
  ef: {D1.abnf.full_date(D1.ALeft{cs}) == fd : D1.ARest},
  hh: {D1.abnf.all_r(D1.abnf.time_offset(D1.abnf.partial_time(D1.abnf.char_r(fd, 32)))) == True{} : Bool}
) -> {M3.vl.wordl(cs) == True{} : Bool}:
  match fd:
    case D1.ALeft{ss}:
      match ss:
        case []:
          Eq.bit.absurd(&2, {M3.vl.wordl(cs) == True{} : Bool}, hh)
        case +h1 <> +tt:
          vl.dt.sp1.c(D1.abnf.cp(h1, 32), h1, tt, cs, {==}, ef, hh)
    case D1.ANone{}:
      Eq.bit.absurd(&2, {M3.vl.wordl(cs) == True{} : Bool}, hh)

# local-date-time matched a whole word
def vl.A2(+xx: Char, +rr: List<&2, Char>) -> Data:
  {D1.abnf.all_r(D1.abnf.partial_time(D1.abnf.time_delim(D1.abnf.full_date(D1.ALeft{xx <> rr})))) == True{}
    : Bool}

# offset-date-time matched a whole word
def vl.A1(+xx: Char, +rr: List<&2, Char>) -> Data:
  {D1.abnf.all_r(D1.abnf.time_offset(D1.abnf.partial_time(D1.abnf.time_delim(D1.abnf.full_date(
    D1.ALeft{xx <> rr}))))) == True{} : Bool}

# local-date-time: T or t, or a space
def vl.dt.a2.go(
  lt: D1.ARest,
  +xx: Char,
  +rr: List<&2, Char>,
  +el: {D1.abnf.letter_r(D1.abnf.full_date(D1.ALeft{xx <> rr}), 84, 116) == lt : D1.ARest},
  +hh: vl.A2(xx, rr)
) -> {M3.vl.wordl(xx <> rr) == True{} : Bool}:
  match lt:
    case D1.ALeft{+ys}:
      M3.vl.qs.word(xx, rr, vl.qs.of(xx <> rr, D1.abnf.partial_time(D1.ALeft{ys}), Equal.trans(Bool,
        D1.abnf.all_r(D1.abnf.partial_time(D1.abnf.or_r(D1.ALeft{ys}, D1.abnf.char_r(D1.abnf.full_date(
        D1.ALeft{xx <> rr}), 32)))), D1.abnf.all_r(D1.abnf.partial_time(D1.abnf.time_delim(D1.abnf.full_date(
        D1.ALeft{xx <> rr})))), True{}, Equal.cong(D1.ARest, Bool, zz => D1.abnf.all_r(D1.abnf.partial_time(
        D1.abnf.or_r(zz, D1.abnf.char_r(D1.abnf.full_date(D1.ALeft{xx <> rr}), 32)))), D1.ALeft{ys},
        D1.abnf.letter_r(D1.abnf.full_date(D1.ALeft{xx <> rr}), 84, 116), Equal.sym(D1.ARest,
        D1.abnf.letter_r(D1.abnf.full_date(D1.ALeft{xx <> rr}), 84, 116), D1.ALeft{ys}, el)), hh),
        hn => vl.z.pt(D1.ALeft{ys}, Equal.trans(Bool, vl.zb(D1.ALeft{ys}), vl.zb(D1.abnf.letter_r(
        D1.abnf.full_date(D1.ALeft{xx <> rr}), 84, 116)), True{}, Equal.cong(D1.ARest, Bool, zz => vl.zb(zz),
        D1.ALeft{ys}, D1.abnf.letter_r(D1.abnf.full_date(D1.ALeft{xx <> rr}), 84, 116), Equal.sym(D1.ARest,
        D1.abnf.letter_r(D1.abnf.full_date(D1.ALeft{xx <> rr}), 84, 116), D1.ALeft{ys}, el)),
        vl.z.lr(D1.abnf.full_date(D1.ALeft{xx <> rr}), 84, 116, {==}, {==}, vl.z.fd(D1.ALeft{xx <> rr},
        hn))))))
    case D1.ANone{}:
      vl.dt.sp2.go(D1.abnf.full_date(D1.ALeft{xx <> rr}), xx <> rr, {==}, Equal.trans(Bool,
        D1.abnf.all_r(D1.abnf.partial_time(D1.abnf.or_r(D1.ANone{}, D1.abnf.char_r(D1.abnf.full_date(
        D1.ALeft{xx <> rr}), 32)))), D1.abnf.all_r(D1.abnf.partial_time(D1.abnf.time_delim(D1.abnf.full_date(
        D1.ALeft{xx <> rr})))), True{}, Equal.cong(D1.ARest, Bool, zz => D1.abnf.all_r(D1.abnf.partial_time(
        D1.abnf.or_r(zz, D1.abnf.char_r(D1.abnf.full_date(D1.ALeft{xx <> rr}), 32)))), D1.ANone{},
        D1.abnf.letter_r(D1.abnf.full_date(D1.ALeft{xx <> rr}), 84, 116), Equal.sym(D1.ARest,
        D1.abnf.letter_r(D1.abnf.full_date(D1.ALeft{xx <> rr}), 84, 116), D1.ANone{}, el)), hh))

# offset-date-time: T or t, or a space
def vl.dt.a1.go(
  lt: D1.ARest,
  +xx: Char,
  +rr: List<&2, Char>,
  +el: {D1.abnf.letter_r(D1.abnf.full_date(D1.ALeft{xx <> rr}), 84, 116) == lt : D1.ARest},
  +hh: vl.A1(xx, rr)
) -> {M3.vl.wordl(xx <> rr) == True{} : Bool}:
  match lt:
    case D1.ALeft{+ys}:
      M3.vl.qs.word(xx, rr, vl.qs.of(xx <> rr, D1.abnf.time_offset(D1.abnf.partial_time(D1.ALeft{ys})),
        Equal.trans(Bool, D1.abnf.all_r(D1.abnf.time_offset(D1.abnf.partial_time(D1.abnf.or_r(D1.ALeft{ys},
        D1.abnf.char_r(D1.abnf.full_date(D1.ALeft{xx <> rr}), 32))))), D1.abnf.all_r(D1.abnf.time_offset(
        D1.abnf.partial_time(D1.abnf.time_delim(D1.abnf.full_date(D1.ALeft{xx <> rr}))))), True{},
        Equal.cong(D1.ARest, Bool, zz => D1.abnf.all_r(D1.abnf.time_offset(D1.abnf.partial_time(
        D1.abnf.or_r(zz, D1.abnf.char_r(D1.abnf.full_date(D1.ALeft{xx <> rr}), 32))))), D1.ALeft{ys},
        D1.abnf.letter_r(D1.abnf.full_date(D1.ALeft{xx <> rr}), 84, 116), Equal.sym(D1.ARest,
        D1.abnf.letter_r(D1.abnf.full_date(D1.ALeft{xx <> rr}), 84, 116), D1.ALeft{ys}, el)), hh),
        hn => vl.z.to(D1.abnf.partial_time(D1.ALeft{ys}), vl.z.pt(D1.ALeft{ys}, Equal.trans(Bool,
        vl.zb(D1.ALeft{ys}), vl.zb(D1.abnf.letter_r(D1.abnf.full_date(D1.ALeft{xx <> rr}), 84, 116)), True{},
        Equal.cong(D1.ARest, Bool, zz => vl.zb(zz), D1.ALeft{ys}, D1.abnf.letter_r(D1.abnf.full_date(
        D1.ALeft{xx <> rr}), 84, 116), Equal.sym(D1.ARest, D1.abnf.letter_r(D1.abnf.full_date(D1.ALeft{xx <>
        rr}), 84, 116), D1.ALeft{ys}, el)), vl.z.lr(D1.abnf.full_date(D1.ALeft{xx <> rr}), 84, 116, {==}, {==},
        vl.z.fd(D1.ALeft{xx <> rr}, hn)))))))
    case D1.ANone{}:
      vl.dt.sp1.go(D1.abnf.full_date(D1.ALeft{xx <> rr}), xx <> rr, {==}, Equal.trans(Bool,
        D1.abnf.all_r(D1.abnf.time_offset(D1.abnf.partial_time(D1.abnf.or_r(D1.ANone{}, D1.abnf.char_r(
        D1.abnf.full_date(D1.ALeft{xx <> rr}), 32))))),
          D1.abnf.all_r(D1.abnf.time_offset(D1.abnf.partial_time(
        D1.abnf.time_delim(D1.abnf.full_date(D1.ALeft{xx <> rr}))))), True{}, Equal.cong(D1.ARest, Bool,
        zz => D1.abnf.all_r(D1.abnf.time_offset(D1.abnf.partial_time(D1.abnf.or_r(zz, D1.abnf.char_r(
        D1.abnf.full_date(D1.ALeft{xx <> rr}), 32))))), D1.ANone{}, D1.abnf.letter_r(D1.abnf.full_date(
        D1.ALeft{xx <> rr}), 84, 116), Equal.sym(D1.ARest, D1.abnf.letter_r(D1.abnf.full_date(D1.ALeft{xx <>
        rr}), 84, 116), D1.ANone{}, el)), hh))

# every word a date-time rule matches is a bare word
def vl.dt.shape(cs: List<&2, Char>, hh: {D1.abnf.date_time(cs) == True{} : Bool}) -> {M3.vl.wordl(cs) == True{} : Bool}:
  match cs:
    case []:
      Eq.bit.absurd(&2, {M3.vl.wordl([]) == True{} : Bool}, hh)
    case +xx <> +rr:
      M5.gp.or({M3.vl.wordl(xx <> rr) == True{} : Bool}, D1.abnf.all_r(D1.abnf.offset_date_time(D1.ALeft{xx <> rr})),
        Bool.or(D1.abnf.all_r(D1.abnf.local_date_time(D1.ALeft{xx <> rr})), Bool.or(D1.abnf.all_r(
        D1.abnf.local_date(D1.ALeft{xx <> rr})), D1.abnf.all_r(D1.abnf.local_time(D1.ALeft{xx <> rr})))), hh,
        h1 => vl.dt.a1.go(D1.abnf.letter_r(D1.abnf.full_date(D1.ALeft{xx <> rr}), 84, 116), xx, rr, {==}, h1),
        hr => M5.gp.or({M3.vl.wordl(xx <> rr) == True{} : Bool}, D1.abnf.all_r(D1.abnf.local_date_time(D1.ALeft{xx <>
          rr})), Bool.or(D1.abnf.all_r(D1.abnf.local_date(D1.ALeft{xx <> rr})), D1.abnf.all_r(
          D1.abnf.local_time(D1.ALeft{xx <> rr}))), hr,
          h2 => vl.dt.a2.go(D1.abnf.letter_r(D1.abnf.full_date(D1.ALeft{xx <> rr}), 84, 116), xx, rr, {==}, h2),
          hs => M5.gp.or({M3.vl.wordl(xx <> rr) == True{} : Bool}, D1.abnf.all_r(D1.abnf.local_date(D1.ALeft{xx <>
            rr})), D1.abnf.all_r(D1.abnf.local_time(D1.ALeft{xx <> rr})), hs,
            h3 => M3.vl.qs.word(xx, rr, vl.qs.of(xx <> rr, D1.abnf.full_date(D1.ALeft{xx <> rr}), h3,
              hn => vl.z.fd(D1.ALeft{xx <> rr}, hn))),
            h4 => M3.vl.qs.word(xx, rr, vl.qs.of(xx <> rr, D1.abnf.partial_time(D1.ALeft{xx <> rr}), h4,
              hn => vl.z.pt(D1.ALeft{xx <> rr}, hn))))))

def L1.date_time_is_bare_word(w, h):
  Equal.trans(Bool, D2.bw.word(w), M3.vl.wordl(String.to_list(w)), True{}, M3.vl.word.eq(w),
      vl.dt.shape(String.to_list(w),
    h))
