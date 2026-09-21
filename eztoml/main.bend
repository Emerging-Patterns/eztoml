# eztoml reads and writes TOML documents. Values are strings, integers, floats,
# booleans, datetimes, arrays, inline tables, tables, and arrays of tables.
# Comments and blank lines are passed over.
#
# parse, render, get, at, root, bad, string, digits, flag
# str, integer, float, boolean, array, inline, table, pair
# key
import Base

# the sign of an integer, a float, or a zone offset
type Sign is Data:
  Plus{}
  Minus{}

# a calendar date: year, month, day
type Date is Data:
  Date{y: U32, mo: U32, d: U32}

# a time of day. frac is the fractional second, empty when there is none
type Clock is Data:
  Clock{h: U32, mi: U32, s: U32, frac: String}

# a zone offset: Z, or a numeric offset
type Zone is Data:
  Zulu{}
  Shift{sign: Sign, h: U32, mi: U32}

# the four TOML datetime forms
type When is Data:
  WOff{date: Date, clock: Clock, zone: Zone}
  WLocal{date: Date, clock: Clock}
  WDate{date: Date}
  WTime{clock: Clock}

# one TOML value. Tables remember the dotted path they were opened under.
# An inline table is VInl. An array of tables is VAots, and each element is
# VAot. VPair is a key in a table.
type Val is Data:
  VStr{text: String}
  VInt{sign: Sign, digits: String}
  VFlo{sign: Sign, text: String}
  VBool{bit: Bool}
  VWhen{when: When}
  VArr{items: List<&2, Val>}
  VInl{rows: List<&2, Val>}
  VHead{path: String, rows: List<&2, Val>}
  VAot{path: String, rows: List<&2, Val>}
  VAots{path: String, elems: List<&2, Val>}
  VPair{name: String, val: Val}

# a key found in a table, or not
type Hit is Data:
  Found{val: Val}
  Miss{}

# a parsed document: the first error, and the root table in order
type Doc is Data:
  Doc{bad: String, rows: List<&2, Val>}

# a value read from a bare word, or the reason it is not one
type Got is Data:
  GotVal{val: Val}
  GotBad{why: String}

# digits taken from the front of a character list
type Dig is Data:
  DigOk{n: U32, cs: List<&2, Char>}
  DigBad{}

# what a datetime scan produced
type WhenOut is Data:
  WSome{when: When}
  WFail{why: String}
  WSkip{}

# a decimal numeral being built, least-significant digit first
type NK is Data:
  NLead{}
  NZero{}
  NDig{}
  NBase{}
  NFrac{}
  NExp{}
  NEDig{}
  NBad{}

# the numeral scan
type Num is Data:
  Num{nk: NK, sign: Sign, base: U32, ds: List<&2, U32>, us: Bool, saw: Bool,
    why: String}

# how a basic-string character is written
type BK is Data:
  BKCh{}
  BKHex{}
  BKEsc{mark: Char}

# where the scanner is in a document
type Lex is Data:
  LTop{}
  LKey{}
  LAfter{}
  LKeyQ{}
  LKeyE{}
  LKeyU{}
  LVal{}
  LQ{}
  LQ2{}
  LStr{}
  LEsc{}
  LUni{}
  LFold{}
  LMq{}
  LTrim{}
  LTrim2{}
  LBare{}
  LDate{}
  LCom{}
  LHead{}
  LHeadGap{}
  LHeadDot{}
  LHeadQ{}
  LHeadE{}
  LHeadU{}
  LHeadR{}
  LArr{}
  LArrC{}
  LInl{}
  LInlK{}
  LInlC{}
  LSink{}

# which quotes a string is using
type QKind is Data:
  QBasic{}
  QLit{}
  QMulti{}
  QMultiLit{}

# one character to read again
type Hold is Data:
  HNone{}
  HChar{c: Char}

# an open array or inline table
type Ctx is Data:
  CArr{items: List<&2, Val>, parts: List<&2, String>, here: List<&2, String>}
  CInl{rows: List<&2, Val>, parts: List<&2, String>, here: List<&2, String>}

# the scanner
type St is Data:
  St{bad: String, rows: List<&2, Val>, heads: List<&2, String>,
    here: List<&2, String>, parts: List<&2, String>, buf: List<&2, Char>,
    lex: Lex, back: Lex, qkind: QKind, stack: List<&2, Ctx>, hold: Hold,
    uni: U32, left: U32, arrtab: Bool, lead: Bool}

# an escape in a basic string
type Esc is Data:
  EChar{c: Char}
  EUni{n: U32}
  EFold{saw: Bool}
  EBad{}

# a character a bare key may hold
def bare.at(+c: Char) -> Bool:
  Bool.or(Char.is_alpha(c), Bool.or(Char.is_digit(c),
    Bool.or(Char.is_eq(c, '_'), Char.is_eq(c, '-'))))

# one step of the bare-key walk, with the head's answer in hand
def bare.all.step(here: Bool, rest: Unit -> Bool) -> Bool:
  match here:
    case True{}:
      rest(Unit{})
    case False{}:
      False{}

# whether every character of a key is one a bare key may hold
def bare.all(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      True{}
    case +h <> t:
      bare.all.step(bare.at(h), _u => bare.all(t))

# whether a key can be written without quotes
def bare(+s: String) -> Bool:
  Bool.and(Bool.not(String.is_empty(s)), bare.all(String.to_list(s)))

# one hex nibble as a character
def hex.char.go(dec: Bool, n: U32) -> Char:
  match dec:
    case True{}:
      Chr{U32.add(48, n)}
    case False{}:
      Chr{U32.add(87, n)}

# one hex nibble as a character
def hex.char(+n: U32) -> Char:
  hex.char.go(U32.is_lt(n, 10), n)

# four lowercase hex digits of a code point, then the \u introducer, reversed
def basic.hex(+u: U32, out: List<&2, Char>) -> List<&2, Char>:
  hex.char(U32.mod(u, 16)) <> (hex.char(U32.mod(U32.shrn(u, 4n), 16)) <>
    (hex.char(U32.mod(U32.shrn(u, 8n), 16)) <>
      (hex.char(U32.mod(U32.shrn(u, 12n), 16)) <> ('u' <> ('\\' <> out)))))

# an escape mark reversed onto the output: the mark, then the backslash
def basic.esc(mark: Char, out: List<&2, Char>) -> List<&2, Char>:
  mark <> ('\\' <> out)

# other controls are \u escapes; the rest are themselves
def basic.cls.hex(hit: Bool) -> BK:
  match hit:
    case True{}:
      BKHex{}
    case False{}:
      BKCh{}

# backslash
def basic.cls.92(hit: Bool, +u: U32) -> BK:
  match hit:
    case True{}:
      BKEsc{'\\'}
    case False{}:
      basic.cls.hex(Bool.or(U32.is_lt(u, 32), U32.is_eq(u, 127)))

# quotation mark
def basic.cls.34(hit: Bool, +u: U32) -> BK:
  match hit:
    case True{}:
      BKEsc{'"'}
    case False{}:
      basic.cls.92(U32.is_eq(u, 92), u)

# carriage return
def basic.cls.13(hit: Bool, +u: U32) -> BK:
  match hit:
    case True{}:
      BKEsc{'r'}
    case False{}:
      basic.cls.34(U32.is_eq(u, 34), u)

# form feed
def basic.cls.12(hit: Bool, +u: U32) -> BK:
  match hit:
    case True{}:
      BKEsc{'f'}
    case False{}:
      basic.cls.13(U32.is_eq(u, 13), u)

# line feed
def basic.cls.10(hit: Bool, +u: U32) -> BK:
  match hit:
    case True{}:
      BKEsc{'n'}
    case False{}:
      basic.cls.12(U32.is_eq(u, 12), u)

# tab
def basic.cls.9(hit: Bool, +u: U32) -> BK:
  match hit:
    case True{}:
      BKEsc{'t'}
    case False{}:
      basic.cls.10(U32.is_eq(u, 10), u)

# backspace, then the rest
def basic.cls.8(hit: Bool, +u: U32) -> BK:
  match hit:
    case True{}:
      BKEsc{'b'}
    case False{}:
      basic.cls.9(U32.is_eq(u, 9), u)

# the class of a code point in a basic string
def basic.cls(+u: U32) -> BK:
  basic.cls.8(U32.is_eq(u, 8), u)

# one character of a basic string, reversed onto the output
def basic.disp(k: BK, c: Char, u: U32, out: List<&2, Char>) -> List<&2, Char>:
  match k:
    case BKCh{}:
      c <> out
    case BKEsc{mark}:
      basic.esc(mark, out)
    case BKHex{}:
      basic.hex(u, out)

# one character of a basic string
def basic.one(+c: Char, out: List<&2, Char>) -> List<&2, Char>:
  +u = Char.to_u32(c)
  basic.disp(basic.cls(u), c, u, out)

# the escaped characters of a basic string, reversed
def basic.go(cs: List<&2, Char>, out: List<&2, Char>) -> List<&2, Char>:
  match cs:
    case []:
      out
    case +h <> t:
      basic.go(t, basic.one(h, out))

# a basic string: quotes, with controls and quotes escaped
def key.basic(+s: String) -> String:
  "\"" ++ String.from_list(List.reverse(&2, Char,
    basic.go(String.to_list(s), []))) ++ "\""

# bare when the name allows it, otherwise a basic string
def key.go(ok: Bool, +s: String) -> String:
  match ok:
    case True{}:
      s
    case False{}:
      key.basic(s)

# a key as TOML writes it
def key(+s: String) -> String:
  key.go(bare(s), s)

# the overflow of a decimal step, least-significant digit first
def dec.carry.c0(z: Bool, c: U32) -> List<&2, U32>:
  match z:
    case True{}:
      []
    case False{}:
      [U32.mod(c, 10)]

# the overflow of a decimal step
def dec.carry.c(+c: U32) -> List<&2, U32>:
  dec.carry.c0(U32.is_zero(c), c)

# the next digit of an overflow
def dec.carry.b0(z: Bool, +c: U32) -> List<&2, U32>:
  match z:
    case True{}:
      []
    case False{}:
      U32.mod(c, 10) <> dec.carry.c(U32.div(c, 10))

# the next digit of an overflow
def dec.carry.b(+c: U32) -> List<&2, U32>:
  dec.carry.b0(U32.is_zero(c), c)

# the first digit of an overflow
def dec.carry.a(z: Bool, +c: U32) -> List<&2, U32>:
  match z:
    case True{}:
      []
    case False{}:
      U32.mod(c, 10) <> dec.carry.b(U32.div(c, 10))

# the digits of a leftover carry
def dec.carry(+c: U32) -> List<&2, U32>:
  dec.carry.a(U32.is_zero(c), c)

# multiply a decimal numeral by a radix and add a digit
def dec.go(ds: List<&2, U32>, +radix: U32, +carry: U32) -> List<&2, U32>:
  match ds:
    case []:
      dec.carry(carry)
    case +d <> t:
      U32.mod(U32.add(U32.mul(d, radix), carry), 10) <> dec.go(t, radix,
        U32.div(U32.add(U32.mul(d, radix), carry), 10))

# a digit character
def dec.ch(d: U32) -> Char:
  Chr{U32.add(48, d)}

# digits as characters, in the order given
def dec.chars(ds: List<&2, U32>) -> List<&2, Char>:
  match ds:
    case []:
      []
    case d <> t:
      dec.ch(d) <> dec.chars(t)

# whether a leading zero is still being skipped
def dec.drop.lead(lead: Bool, +h: Char) -> Bool:
  match lead:
    case False{}:
      False{}
    case True{}:
      Char.is_eq(h, '0')

# a leading zero is skipped; any other character is kept
def dec.drop.outz(z: Bool, h: Char, out: List<&2, Char>) -> List<&2, Char>:
  match z:
    case True{}:
      out
    case False{}:
      h <> out

# the output after one character, reversed
def dec.drop.out(lead: Bool, +h: Char, out: List<&2, Char>) -> List<&2, Char>:
  match lead:
    case False{}:
      h <> out
    case True{}:
      dec.drop.outz(Char.is_eq(h, '0'), h, out)

# the numeral, or 0 when every digit was zero
def dec.drop.end(lead: Bool, out: List<&2, Char>) -> String:
  match lead:
    case True{}:
      "0"
    case False{}:
      String.from_list(List.reverse(&2, Char, out))

# drop leading zeros from a most-significant-first digit list
def dec.drop(cs: List<&2, Char>, +lead: Bool, out: List<&2, Char>) -> String:
  match cs:
    case []:
      dec.drop.end(lead, out)
    case +h <> t:
      dec.drop(t, dec.drop.lead(lead, h), dec.drop.out(lead, h, out))

# a decimal numeral. The digit list is least-significant first
def dec.text(ds: List<&2, U32>) -> String:
  dec.drop(dec.chars(List.reverse(&2, U32, ds)), True{}, [])

# a code point's digit value, or 99 when the character is not a digit
def dig.up(ok: Bool, u: U32) -> U32:
  match ok:
    case True{}:
      U32.sub(u, 55)
    case False{}:
      99

# a lowercase hex digit, otherwise an uppercase one
def dig.low(ok: Bool, +u: U32) -> U32:
  match ok:
    case True{}:
      U32.sub(u, 87)
    case False{}:
      dig.up(Bool.and(U32.is_ge(u, 65), U32.is_le(u, 70)), u)

# a decimal digit, otherwise a hex letter
def dig.dec(ok: Bool, +u: U32) -> U32:
  match ok:
    case True{}:
      U32.sub(u, 48)
    case False{}:
      dig.low(Bool.and(U32.is_ge(u, 97), U32.is_le(u, 102)), u)

# the value of a digit character, or 99
def dig.val(+c: Char) -> U32:
  +u = Char.to_u32(c)
  dig.dec(Bool.and(U32.is_ge(u, 48), U32.is_le(u, 57)), u)

# whether a digit value fits a base
def dig.ok(d: U32, base: U32) -> Bool:
  U32.is_lt(d, base)

# exactly k digits, or DigBad
def take.acc.d(digit: Bool, n: U32, +c: Char) -> U32:
  match digit:
    case False{}:
      n
    case True{}:
      U32.add(U32.mul(n, 10), U32.sub(Char.to_u32(c), 48))

# the accumulator after one character
def take.acc(ok: Bool, n: U32, +c: Char) -> U32:
  match ok:
    case False{}:
      n
    case True{}:
      take.acc.d(Char.is_digit(c), n, c)

# the scan stays well only while every character is a digit
def take.ok(ok: Bool, +c: Char) -> Bool:
  match ok:
    case False{}:
      False{}
    case True{}:
      Char.is_digit(c)

# the finished take
def take.fin(ok: Bool, n: U32, cs: List<&2, Char>) -> Dig:
  match ok:
    case True{}:
      DigOk{n, cs}
    case False{}:
      DigBad{}

# exactly k digits from the front of a list
def take.n(k: Nat, cs: List<&2, Char>, n: U32, +ok: Bool) -> Dig:
  match k:
    case 0n:
      take.fin(ok, n, cs)
    case 1n+p:
      match cs:
        case []:
          DigBad{}
        case +h <> t:
          take.n(p, t, take.acc(ok, n, h), take.ok(ok, h))

# a number is inside the inclusive bounds
def bound.rng(+n: U32, lo: U32, hi: U32) -> Bool:
  Bool.and(U32.is_ge(n, lo), U32.is_le(n, hi))

# two digits, zero padded
def pad2.go(small: Bool, n: U32) -> String:
  match small:
    case True{}:
      "0" ++ U32.show(n)
    case False{}:
      U32.show(n)

# two digits, zero padded
def text.pad2(+n: U32) -> String:
  pad2.go(U32.is_lt(n, 10), n)

# the one-zero pad, or the digits themselves
def pad4.big(n: U32, big: Bool) -> String:
  match big:
    case True{}:
      "0" ++ U32.show(n)
    case False{}:
      U32.show(n)

# the three-digit and two-digit pads
def pad4.mid(n: U32, mid: Bool, big: Bool) -> String:
  match mid:
    case True{}:
      "00" ++ U32.show(n)
    case False{}:
      pad4.big(n, big)

# four digits, zero padded
def pad4.go(n: U32, small: Bool, mid: Bool, big: Bool) -> String:
  match small:
    case True{}:
      "000" ++ U32.show(n)
    case False{}:
      pad4.mid(n, mid, big)

# four digits, zero padded
def text.pad4(+n: U32) -> String:
  pad4.go(n, U32.is_lt(n, 10), U32.is_lt(n, 100), U32.is_lt(n, 1000))

# the sign of a zone offset
def zone.mark(sign: Sign) -> String:
  match sign:
    case Plus{}:
      "+"
    case Minus{}:
      "-"

# a numeric zone offset
def zone.shift(sign: Sign, h: U32, mi: U32) -> String:
  zone.mark(sign) ++ text.pad2(h) ++ ":" ++ text.pad2(mi)

# a zone suffix
def zone.text(z: Zone) -> String:
  match z:
    case Zulu{}:
      "Z"
    case Shift{sign, h, mi}:
      zone.shift(sign, h, mi)

# the fractional second, or nothing
def clock.frac.go(empty: Bool, frac: String) -> String:
  match empty:
    case True{}:
      ""
    case False{}:
      "." ++ frac

# the fractional second, or nothing
def clock.frac(+frac: String) -> String:
  clock.frac.go(String.is_empty(frac), frac)

# a clock, with a fractional second when it has one
def clock.text(c: Clock) -> String:
  Clock{h, mi, s, frac} = c
  text.pad2(h) ++ ":" ++ text.pad2(mi) ++ ":" ++ text.pad2(s) ++ clock.frac(frac)

# a date
def date.text(d: Date) -> String:
  Date{y, mo, day} = d
  text.pad4(y) ++ "-" ++ text.pad2(mo) ++ "-" ++ text.pad2(day)

# a datetime in TOML spelling
def when.text(w: When) -> String:
  match w:
    case WOff{date, clock, zone}:
      date.text(date) ++ "T" ++ clock.text(clock) ++ zone.text(zone)
    case WLocal{date, clock}:
      date.text(date) ++ "T" ++ clock.text(clock)
    case WDate{date}:
      date.text(date)
    case WTime{clock}:
      clock.text(clock)

# the sign of an integer or a float, empty when it is positive
def sign.text(sign: Sign) -> String:
  match sign:
    case Plus{}:
      ""
    case Minus{}:
      "-"

# whether the list still has a character
def cs.some(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      False{}
    case _ <> _:
      True{}

# one character, when the list has one
def cs.head(cs: List<&2, Char>) -> Char:
  match cs:
    case []:
      ' '
    case h <> _:
      h

# the tail of a list
def cs.tail(cs: List<&2, Char>) -> List<&2, Char>:
  match cs:
    case []:
      []
    case _ <> t:
      t

# a clock with its fraction filled in
def clock.with(c: Clock, frac: String) -> Clock:
  Clock{h, mi, s, _f} = c
  Clock{h, mi, s, frac}

# a finished local datetime, or one with a zone still to read
def when.done(_date: Date, _clock: Clock, w: When) -> WhenOut:
  WSome{w}

# Z ends the token
def when.zone.z(t: List<&2, Char>, clock: Clock, date: Date) -> WhenOut:
  match t:
    case []:
      WSome{WOff{date, clock, Zulu{}}}
    case _ <> _:
      WFail{"invalid zone"}

# the offset minute is in range
def when.zone.mm.ok2(mi_ok: Bool, sign: Sign, h: U32, mi: U32, clock: Clock,
  date: Date) -> WhenOut:
  match mi_ok:
    case False{}:
      WFail{"zone minute is out of range"}
    case True{}:
      WSome{WOff{date, clock, Shift{sign, h, mi}}}

# the offset fields are in range
def when.zone.mm.ok(h_ok: Bool, mi_ok: Bool, sign: Sign, h: U32, mi: U32,
  clock: Clock, date: Date) -> WhenOut:
  match h_ok:
    case False{}:
      WFail{"zone hour is out of range"}
    case True{}:
      when.zone.mm.ok2(mi_ok, sign, h, mi, clock, date)

# nothing follows an offset, and its fields are in range
def when.zone.mm.end(cs: List<&2, Char>, h_ok: Bool, mi_ok: Bool, sign: Sign,
  h: U32, mi: U32, clock: Clock, date: Date) -> WhenOut:
  match cs:
    case []:
      when.zone.mm.ok(h_ok, mi_ok, sign, h, mi, clock, date)
    case _ <> _:
      WFail{"invalid zone"}

# the offset minute is in range
def when.zone.mm.go(d: Dig, sign: Sign, +h: U32, clock: Clock, date: Date) -> WhenOut:
  match d:
    case DigBad{}:
      WFail{"invalid zone"}
    case DigOk{+n, cs}:
      when.zone.mm.end(cs, bound.rng(h, 0, 23), bound.rng(n, 0, 59), sign, h, n, clock, date)

# the offset minute
def when.zone.mm(hit: Bool, d: Dig, sign: Sign, h: U32, clock: Clock, date: Date) -> WhenOut:
  match hit:
    case False{}:
      WFail{"invalid zone"}
    case True{}:
      when.zone.mm.go(d, sign, h, clock, date)

# the colon in an offset
def when.zone.hh.colon(cs: List<&2, Char>, sign: Sign, h: U32, clock: Clock,
  date: Date) -> WhenOut:
  match cs:
    case []:
      WFail{"invalid zone"}
    case +c <> t:
      when.zone.mm(Char.is_eq(c, ':'), take.n(2n, t, 0, True{}), sign, h, clock, date)

# the offset hour
def when.zone.hh(d: Dig, sign: Sign, clock: Clock, date: Date) -> WhenOut:
  match d:
    case DigBad{}:
      WFail{"invalid zone"}
    case DigOk{n, cs}:
      when.zone.hh.colon(cs, sign, n, clock, date)

# HH:MM of a numeric offset
def when.zone.off(sign: Sign, t: List<&2, Char>, clock: Clock, date: Date) -> WhenOut:
  when.zone.hh(take.n(2n, t, 0, True{}), sign, clock, date)

# a minus starts a numeric offset
def when.zone.minus(minus: Bool, t: List<&2, Char>, clock: Clock, date: Date) -> WhenOut:
  match minus:
    case True{}:
      when.zone.off(Minus{}, t, clock, date)
    case False{}:
      WFail{"invalid zone"}

# a plus or a minus starts a numeric offset
def when.zone.sign(plus: Bool, minus: Bool, t: List<&2, Char>, clock: Clock,
  date: Date) -> WhenOut:
  match plus:
    case True{}:
      when.zone.off(Plus{}, t, clock, date)
    case False{}:
      when.zone.minus(minus, t, clock, date)

# Z, or a signed numeric offset
def when.zone.go(zee: Bool, plus: Bool, minus: Bool, t: List<&2, Char>,
  clock: Clock, date: Date) -> WhenOut:
  match zee:
    case True{}:
      when.zone.z(t, clock, date)
    case False{}:
      when.zone.sign(plus, minus, t, clock, date)

# a zone, or the end of a local datetime
def when.zone(cs: List<&2, Char>, clock: Clock, date: Date) -> WhenOut:
  match cs:
    case []:
      WSome{WLocal{date, clock}}
    case +c <> t:
      when.zone.go(Char.is_eq(c, 'Z'), Char.is_eq(c, '+'), Char.is_eq(c, '-'), t,
        clock, date)

# the fraction must hold a digit
def when.frac.end.go(some: Bool, rev: List<&2, Char>, clock: Clock, date: Date,
  rest: List<&2, Char>) -> WhenOut:
  match some:
    case False{}:
      WFail{"invalid fraction"}
    case True{}:
      when.zone(rest, clock.with(clock, String.from_list(List.reverse(&2, Char, rev))),
        date)

# the fraction must hold a digit
def when.frac.end(+rev: List<&2, Char>, clock: Clock, date: Date,
  rest: List<&2, Char>) -> WhenOut:
  when.frac.end.go(cs.some(rev), rev, clock, date, rest)

# one fractional digit, or the end of the fraction
def when.frac.digit(digit: Bool, +c: Char, t: List<&2, Char>, rev: List<&2, Char>,
  clock: Clock, date: Date, more: Unit -> WhenOut) -> WhenOut:
  match digit:
    case True{}:
      more(Unit{})
    case False{}:
      when.frac.end(rev, clock, date, c <> t)

# fractional digits
def when.frac.digits(cs: List<&2, Char>, +rev: List<&2, Char>, +clock: Clock,
  +date: Date) -> WhenOut:
  match cs:
    case []:
      when.frac.end(rev, clock, date, [])
    case +c <> +t:
      when.frac.digit(Char.is_digit(c), c, t, rev, clock, date,
        _u => when.frac.digits(t, c <> rev, clock, date))

# a dot starts a fraction; anything else is a zone
def when.frac.go(dot: Bool, t: List<&2, Char>, clock: Clock, date: Date,
  +c: Char) -> WhenOut:
  match dot:
    case True{}:
      when.frac.digits(t, [], clock, date)
    case False{}:
      when.zone(c <> t, clock, date)

# an optional fractional second
def when.frac(cs: List<&2, Char>, +clock: Clock, +date: Date) -> WhenOut:
  match cs:
    case []:
      when.done(date, clock, WLocal{date, clock})
    case +c <> t:
      when.frac.go(Char.is_eq(c, '.'), t, clock, date, c)

# the second is in range, then the fraction and the zone
def when.clock.range.s(s_ok: Bool, h: U32, mi: U32, s: U32, cs: List<&2, Char>,
  date: Date) -> WhenOut:
  match s_ok:
    case False{}:
      WFail{"second is out of range"}
    case True{}:
      when.frac(cs, Clock{h, mi, s, ""}, date)

# minute and second are in range
def when.clock.range.m(mi_ok: Bool, s_ok: Bool, h: U32, mi: U32, s: U32,
  cs: List<&2, Char>, date: Date) -> WhenOut:
  match mi_ok:
    case False{}:
      WFail{"minute is out of range"}
    case True{}:
      when.clock.range.s(s_ok, h, mi, s, cs, date)

# hour, minute, and second are in range
def when.clock.range(h_ok: Bool, mi_ok: Bool, s_ok: Bool, h: U32, mi: U32,
  s: U32, cs: List<&2, Char>, date: Date) -> WhenOut:
  match h_ok:
    case False{}:
      WFail{"hour is out of range"}
    case True{}:
      when.clock.range.m(mi_ok, s_ok, h, mi, s, cs, date)

# seconds, then an optional fraction and zone
def when.clock.ss.go(d: Dig, +h: U32, +mi: U32, date: Date) -> WhenOut:
  match d:
    case DigBad{}:
      WFail{"invalid time"}
    case DigOk{+n, cs}:
      when.clock.range(bound.rng(h, 0, 23), bound.rng(mi, 0, 59), bound.rng(n, 0, 60), h, mi, n,
        cs, date)

# seconds after the colon
def when.clock.ss(hit: Bool, d: Dig, h: U32, mi: U32, date: Date) -> WhenOut:
  match hit:
    case False{}:
      WFail{"invalid time"}
    case True{}:
      when.clock.ss.go(d, h, mi, date)

# the colon after the minutes
def when.clock.mm.colon(cs: List<&2, Char>, h: U32, mi: U32, date: Date) -> WhenOut:
  match cs:
    case []:
      WFail{"invalid time"}
    case +c <> t:
      when.clock.ss(Char.is_eq(c, ':'), take.n(2n, t, 0, True{}), h, mi, date)

# minutes, then seconds
def when.clock.mm(d: Dig, h: U32, date: Date) -> WhenOut:
  match d:
    case DigBad{}:
      WFail{"invalid time"}
    case DigOk{n, cs}:
      when.clock.mm.colon(cs, h, n, date)

# the colon after the hour
def when.clock.colon.go(hit: Bool, h: U32, t: List<&2, Char>, date: Date) -> WhenOut:
  match hit:
    case False{}:
      WFail{"invalid time"}
    case True{}:
      when.clock.mm(take.n(2n, t, 0, True{}), h, date)

# the colon after the hour
def when.clock.colon(cs: List<&2, Char>, h: U32, date: Date) -> WhenOut:
  match cs:
    case []:
      WFail{"invalid time"}
    case +c <> t:
      when.clock.colon.go(Char.is_eq(c, ':'), h, t, date)

# a clock following a date
def when.clock.of(d: Dig, date: Date) -> WhenOut:
  match d:
    case DigBad{}:
      WFail{"invalid time"}
    case DigOk{n, cs}:
      when.clock.colon(cs, n, date)

# a space separates a date from a time
def when.after.sp(sp: Bool, date: Date, t: List<&2, Char>) -> WhenOut:
  match sp:
    case True{}:
      when.clock.of(take.n(2n, t, 0, True{}), date)
    case False{}:
      WFail{"invalid datetime"}

# T or a space separates a date from a time
def when.after.sep(tee: Bool, sp: Bool, date: Date, t: List<&2, Char>) -> WhenOut:
  match tee:
    case True{}:
      when.clock.of(take.n(2n, t, 0, True{}), date)
    case False{}:
      when.after.sp(sp, date, t)

# the character after a date: nothing, T, or a space, and then a time
def when.after.date(date: Date, cs: List<&2, Char>) -> WhenOut:
  match cs:
    case []:
      WSome{WDate{date}}
    case +c <> t:
      when.after.sep(Char.is_eq(c, 'T'), Char.is_eq(c, ' '), date, t)

# the day is in range, then the rest of the token is a time or nothing
def when.date.ok.d(d_ok: Bool, y: U32, mo: U32, d: U32,
  cs: List<&2, Char>) -> WhenOut:
  match d_ok:
    case False{}:
      WFail{"day is out of range"}
    case True{}:
      when.after.date(Date{y, mo, d}, cs)

# a date whose fields are in range
def when.date.ok.go(mo_ok: Bool, d_ok: Bool, y: U32, mo: U32, d: U32,
  cs: List<&2, Char>) -> WhenOut:
  match mo_ok:
    case False{}:
      WFail{"month is out of range"}
    case True{}:
      when.date.ok.d(d_ok, y, mo, d, cs)

# a date whose fields are in range
def when.date.ok(y: U32, +mo: U32, +d: U32, cs: List<&2, Char>) -> WhenOut:
  when.date.ok.go(bound.rng(mo, 1, 12), bound.rng(d, 1, 31), y, mo, d, cs)

# a local time: HH:MM:SS, with the hour already taken
def when.time.rest(t: List<&2, Char>, h: U32) -> WhenOut:
  when.clock.mm(take.n(2n, t, 0, True{}), h, Date{0, 1, 1})

# a local time uses a dummy date and then keeps only the clock
def when.time.only(w: WhenOut) -> WhenOut:
  match w:
    case WSome{WLocal{_date, clock}}:
      WSome{WTime{clock}}
    case WSome{WOff{_date, clock, zone}}:
      WFail{"invalid time"}
    case WSome{other}:
      WFail{"invalid time"}
    case WFail{why}:
      WFail{why}
    case WSkip{}:
      WFail{"invalid time"}

# a complete date, then whatever follows it
def when.day.end(d: Dig, y: U32, mo: U32) -> WhenOut:
  match d:
    case DigBad{}:
      WFail{"invalid date"}
    case DigOk{n, cs}:
      when.date.ok(y, mo, n, cs)

# the day is two digits
def when.day.go(hit: Bool, d: Dig, y: U32, mo: U32) -> WhenOut:
  match hit:
    case False{}:
      WFail{"invalid date"}
    case True{}:
      when.day.end(d, y, mo)

# the day
def when.day(cs: List<&2, Char>, y: U32, mo: U32) -> WhenOut:
  match cs:
    case []:
      WFail{"invalid date"}
    case +c <> t:
      when.day.go(Char.is_eq(c, '-'), take.n(2n, t, 0, True{}), y, mo)

# the dash after the month
def when.month.go(d: Dig, y: U32) -> WhenOut:
  match d:
    case DigBad{}:
      WFail{"invalid date"}
    case DigOk{n, cs}:
      when.day(cs, y, n)

# the month
def when.month(hit: Bool, d: Dig, y: U32) -> WhenOut:
  match hit:
    case False{}:
      WFail{"invalid date"}
    case True{}:
      when.month.go(d, y)

# the dash after the year
def when.year.dash(cs: List<&2, Char>, y: U32) -> WhenOut:
  match cs:
    case []:
      WFail{"invalid date"}
    case +c <> t:
      when.month(Char.is_eq(c, '-'), take.n(2n, t, 0, True{}), y)

# the fourth year digit, then the month
def when.year4(d: Dig) -> WhenOut:
  match d:
    case DigBad{}:
      WFail{"invalid date"}
    case DigOk{n, cs}:
      when.year.dash(cs, n)

# two more year digits, then a dash
def when.year.more(digit: Bool, n: U32, +c: Char, t: List<&2, Char>) -> WhenOut:
  match digit:
    case False{}:
      WFail{"invalid datetime"}
    case True{}:
      when.year4(take.n(1n, t, U32.add(U32.mul(n, 10), dig.val(c)), True{}))

# a colon means a local time; another digit continues a year
def when.branch(colon: Bool, digit: Bool, n: U32, +c: Char, t: List<&2, Char>) -> WhenOut:
  match colon:
    case True{}:
      when.time.only(when.time.rest(t, n))
    case False{}:
      when.year.more(digit, n, c, t)

# two digits decide a time or a date
def when.after2.go(cs: List<&2, Char>, n: U32) -> WhenOut:
  match cs:
    case []:
      WFail{"invalid datetime"}
    case +c <> t:
      when.branch(Char.is_eq(c, ':'), Char.is_digit(c), n, c, t)

# two digits decide a time (HH:) or a date (YYYY-)
def when.after2(d: Dig) -> WhenOut:
  match d:
    case DigBad{}:
      WFail{"invalid datetime"}
    case DigOk{n, cs}:
      when.after2.go(cs, n)

# a datetime token
def when.read(cs: List<&2, Char>) -> WhenOut:
  when.after2(take.n(2n, cs, 0, True{}))

# a dash after the first character
def word.dash.hit(first: Bool, +c: Char) -> Bool:
  match first:
    case True{}:
      False{}
    case False{}:
      Char.is_eq(c, '-')

# either flag
def word.or(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      True{}
    case False{}:
      b

# a colon anywhere in the token
def word.colon(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      False{}
    case +c <> t:
      word.or(Char.is_eq(c, ':'), word.colon(t))

# a dash after the first character
def word.dash(cs: List<&2, Char>, first: Bool) -> Bool:
  match cs:
    case []:
      False{}
    case +c <> t:
      word.or(word.dash.hit(first, c), word.dash(t, False{}))

# a negative nan, or not a special
def word.spec.nan3(c: Bool) -> Got:
  match c:
    case True{}:
      GotVal{VFlo{Minus{}, "nan"}}
    case False{}:
      GotBad{""}

# a signed nan
def word.spec.nan2(b: Bool, c: Bool) -> Got:
  match b:
    case True{}:
      GotVal{VFlo{Plus{}, "nan"}}
    case False{}:
      word.spec.nan3(c)

# nan
def word.spec.nan(a: Bool, b: Bool, c: Bool) -> Got:
  match a:
    case True{}:
      GotVal{VFlo{Plus{}, "nan"}}
    case False{}:
      word.spec.nan2(b, c)

# a negative inf, or nan
def word.spec.inf3(c: Bool, +s: String) -> Got:
  match c:
    case True{}:
      GotVal{VFlo{Minus{}, "inf"}}
    case False{}:
      word.spec.nan(String.eq(s, "nan"), String.eq(s, "+nan"), String.eq(s, "-nan"))

# a signed inf, or nan
def word.spec.inf2(b: Bool, c: Bool, +s: String) -> Got:
  match b:
    case True{}:
      GotVal{VFlo{Plus{}, "inf"}}
    case False{}:
      word.spec.inf3(c, s)

# inf, or nan
def word.spec.inf(a: Bool, b: Bool, c: Bool, +s: String) -> Got:
  match a:
    case True{}:
      GotVal{VFlo{Plus{}, "inf"}}
    case False{}:
      word.spec.inf2(b, c, s)

# false, or the rest of the specials
def word.spec.f(hit: Bool, +s: String) -> Got:
  match hit:
    case True{}:
      GotVal{VBool{False{}}}
    case False{}:
      word.spec.inf(String.eq(s, "inf"), String.eq(s, "+inf"), String.eq(s, "-inf"), s)

# true, or the rest of the specials
def word.spec.t(hit: Bool, other: Bool, +s: String) -> Got:
  match hit:
    case True{}:
      GotVal{VBool{True{}}}
    case False{}:
      word.spec.f(other, s)

# true, false, inf, and nan, including a sign on inf and nan
def word.spec(+s: String) -> Got:
  word.spec.t(String.eq(s, "true"), String.eq(s, "false"), s)

# a datetime result as a value
def word.from.when(w: WhenOut) -> Got:
  match w:
    case WSome{when}:
      GotVal{VWhen{when}}
    case WFail{why}:
      GotBad{why}
    case WSkip{}:
      GotBad{"invalid datetime"}

# the spelling of a numeral with the leading sign and underscores removed
def word.body.put.sign(is_sign: Bool, c: Char, out: List<&2, Char>) -> List<&2, Char>:
  match is_sign:
    case True{}:
      out
    case False{}:
      c <> out

# an underscore is dropped; every other character is kept
def word.body.put.us(is_us: Bool, c: Char, out: List<&2, Char>) -> List<&2, Char>:
  match is_us:
    case True{}:
      out
    case False{}:
      c <> out

# one character of a numeral spelling
def word.body.put(lead: Bool, +c: Char, out: List<&2, Char>) -> List<&2, Char>:
  match lead:
    case True{}:
      word.body.put.sign(Bool.or(Char.is_eq(c, '+'), Char.is_eq(c, '-')), c, out)
    case False{}:
      word.body.put.us(Char.is_eq(c, '_'), c, out)

# the spelling, reversed, then put back in order at the end
def word.body.go(cs: List<&2, Char>, lead: Bool, out: List<&2, Char>) -> List<&2, Char>:
  match cs:
    case []:
      List.reverse(&2, Char, out)
    case +c <> t:
      word.body.go(t, False{}, word.body.put(lead, c, out))

# the spelling of a numeral with the leading sign and underscores removed
def word.body(cs: List<&2, Char>) -> String:
  String.from_list(word.body.go(cs, True{}, []))

# a fresh numeral scan
def num.start() -> Num:
  Num{NLead{}, Plus{}, 10, [], False{}, False{}, ""}

# a scan that has failed
def num.bad(_st: Num, why: String) -> Num:
  Num{NBad{}, Plus{}, 10, [], False{}, False{}, why}

# set the sign and wait for a digit
def num.sign(_st: Num, sign: Sign) -> Num:
  Num{NLead{}, sign, 10, [], False{}, False{}, ""}

# a digit that fits the base
def num.digit.ok(ok: Bool, +c: Char, nk: NK, sign: Sign, +base: U32,
  ds: List<&2, U32>) -> Num:
  match ok:
    case False{}:
      num.bad(Num{NLead{}, Plus{}, 10, [], False{}, False{}, ""}, "invalid digit")
    case True{}:
      Num{nk, sign, base, dec.go(ds, base, dig.val(c)), False{}, True{}, ""}

# a decimal digit joined to the numeral
def num.digit.go(st: Num, +c: Char, nk: NK) -> Num:
  Num{_nk, sign, +base, ds, _us, _saw, _why} = st
  num.digit.ok(dig.ok(dig.val(c), base), c, nk, sign, base, ds)

# a decimal digit joined to the numeral
def num.digit(st: Num, +c: Char, nk: NK) -> Num:
  num.digit.go(st, c, nk)

# an underscore between digits
def num.us.go(ok: Bool, nk: NK, sign: Sign, base: U32, ds: List<&2, U32>,
  why: String) -> Num:
  match ok:
    case False{}:
      num.bad(Num{NLead{}, Plus{}, 10, [], False{}, False{}, ""}, "invalid underscore")
    case True{}:
      Num{nk, sign, base, ds, True{}, True{}, why}

# an underscore between digits
def num.us(st: Num) -> Num:
  Num{nk, sign, base, ds, us, saw, why} = st
  num.us.go(Bool.and(saw, Bool.not(us)), nk, sign, base, ds, why)

# the base prefix after a leading zero
def num.base(st: Num, base: U32) -> Num:
  Num{_nk, sign, _b, _ds, _us, _saw, _why} = st
  Num{NBase{}, sign, base, [], False{}, False{}, ""}

# a dot begins the fraction
def num.dot.go(ok: Bool, sign: Sign) -> Num:
  match ok:
    case False{}:
      num.bad(Num{NLead{}, Plus{}, 10, [], False{}, False{}, ""}, "invalid fraction")
    case True{}:
      Num{NFrac{}, sign, 10, [], False{}, False{}, ""}

# a dot begins the fraction
def num.dot(st: Num) -> Num:
  Num{_nk, sign, _b, _ds, us, saw, _why} = st
  num.dot.go(Bool.and(saw, Bool.not(us)), sign)

# an exponent marker
def num.exp.go(ok: Bool, sign: Sign) -> Num:
  match ok:
    case False{}:
      num.bad(Num{NLead{}, Plus{}, 10, [], False{}, False{}, ""}, "invalid exponent")
    case True{}:
      Num{NExp{}, sign, 10, [], False{}, False{}, ""}

# an exponent marker
def num.exp(st: Num) -> Num:
  Num{_nk, sign, _b, _ds, us, saw, _why} = st
  num.exp.go(Bool.and(saw, Bool.not(us)), sign)

# the sign already chosen
def num.sign.of(st: Num) -> Sign:
  Num{_nk, sign, _b, _ds, _us, _saw, _why} = st
  sign

# a first digit
def num.lead.digit(digit: Bool, st: Num, +c: Char) -> Num:
  match digit:
    case True{}:
      num.digit(st, c, NDig{})
    case False{}:
      num.bad(st, "invalid number")

# a leading zero, or another digit
def num.lead.zero(zero: Bool, digit: Bool, st: Num, +c: Char) -> Num:
  match zero:
    case True{}:
      Num{NZero{}, num.sign.of(st), 10, [], False{}, True{}, ""}
    case False{}:
      num.lead.digit(digit, st, c)

# a minus, a zero, or a digit
def num.lead.minus(minus: Bool, zero: Bool, digit: Bool, st: Num, +c: Char) -> Num:
  match minus:
    case True{}:
      num.sign(st, Minus{})
    case False{}:
      num.lead.zero(zero, digit, st, c)

# a sign, a zero, or a digit
def num.lead.go(plus: Bool, minus: Bool, zero: Bool, digit: Bool, st: Num,
  +c: Char) -> Num:
  match plus:
    case True{}:
      num.sign(st, Plus{})
    case False{}:
      num.lead.minus(minus, zero, digit, st, c)

# the first character after an optional sign
def num.lead(st: Num, +c: Char) -> Num:
  num.lead.go(Char.is_eq(c, '+'), Char.is_eq(c, '-'), Char.is_eq(c, '0'),
    Char.is_digit(c), st, c)

# the leading zero becomes a decimal digit, with an underscore open
def num.zero.dig(st: Num) -> Num:
  Num{_nk, sign, _b, _ds, _us, _saw, _why} = st
  Num{NDig{}, sign, 10, dec.go([], 10, 0), True{}, True{}, ""}

# 0_1 keeps the zero and requires another digit
def num.zero.us(us: Bool, st: Num) -> Num:
  match us:
    case True{}:
      num.zero.dig(st)
    case False{}:
      num.bad(st, "invalid number")

# a capital exponent, or an underscore after the leading zero
def num.zero.exp2(ee: Bool, st: Num, +c: Char) -> Num:
  match ee:
    case True{}:
      num.exp(st)
    case False{}:
      num.zero.us(Char.is_eq(c, '_'), st)

# an exponent after zero, or a rejected extra digit
def num.zero.exp(e: Bool, ee: Bool, st: Num, +c: Char) -> Num:
  match e:
    case True{}:
      num.exp(st)
    case False{}:
      num.zero.exp2(ee, st, c)

# a fraction or an exponent after zero
def num.zero.dot(dot: Bool, e: Bool, ee: Bool, st: Num, +c: Char) -> Num:
  match dot:
    case True{}:
      num.dot(st)
    case False{}:
      num.zero.exp(e, ee, st, c)

# a binary prefix, or a float
def num.zero.b(b: Bool, dot: Bool, e: Bool, ee: Bool, st: Num, +c: Char) -> Num:
  match b:
    case True{}:
      num.base(st, 2)
    case False{}:
      num.zero.dot(dot, e, ee, st, c)

# an octal prefix, or the rest
def num.zero.o(o: Bool, b: Bool, dot: Bool, e: Bool, ee: Bool, st: Num, +c: Char) -> Num:
  match o:
    case True{}:
      num.base(st, 8)
    case False{}:
      num.zero.b(b, dot, e, ee, st, c)

# a base prefix, a fraction, or an exponent
def num.zero.go(x: Bool, o: Bool, b: Bool, dot: Bool, e: Bool, ee: Bool, st: Num,
  +c: Char) -> Num:
  match x:
    case True{}:
      num.base(st, 16)
    case False{}:
      num.zero.o(o, b, dot, e, ee, st, c)

# the character after a lone zero
def num.zero(st: Num, +c: Char) -> Num:
  num.zero.go(Char.is_eq(c, 'x'), Char.is_eq(c, 'o'), Char.is_eq(c, 'b'),
    Char.is_eq(c, '.'), Char.is_eq(c, 'e'), Char.is_eq(c, 'E'), st, c)

# a capital exponent, or a rejected character
def num.digs.exp2(ee: Bool, st: Num, _c: Char) -> Num:
  match ee:
    case True{}:
      num.exp(st)
    case False{}:
      num.bad(st, "invalid number")

# an exponent
def num.digs.exp(e: Bool, ee: Bool, st: Num, +c: Char) -> Num:
  match e:
    case True{}:
      num.exp(st)
    case False{}:
      num.digs.exp2(ee, st, c)

# a dot or an exponent
def num.digs.dot(dot: Bool, e: Bool, ee: Bool, st: Num, +c: Char) -> Num:
  match dot:
    case True{}:
      num.dot(st)
    case False{}:
      num.digs.exp(e, ee, st, c)

# an underscore, a dot, or an exponent
def num.digs.us(us: Bool, dot: Bool, e: Bool, ee: Bool, st: Num, +c: Char) -> Num:
  match us:
    case True{}:
      num.us(st)
    case False{}:
      num.digs.dot(dot, e, ee, st, c)

# a decimal digit, an underscore, a dot, or an exponent
def num.digs.go(digit: Bool, us: Bool, dot: Bool, e: Bool, ee: Bool, st: Num,
  +c: Char) -> Num:
  match digit:
    case True{}:
      num.digit(st, c, NDig{})
    case False{}:
      num.digs.us(us, dot, e, ee, st, c)

# a decimal digit, an underscore, a dot, or an exponent
def num.digs(st: Num, +c: Char) -> Num:
  num.digs.go(Char.is_digit(c), Char.is_eq(c, '_'), Char.is_eq(c, '.'),
    Char.is_eq(c, 'e'), Char.is_eq(c, 'E'), st, c)

# an underscore, or a digit of the base
def num.based.go(us: Bool, st: Num, +c: Char) -> Num:
  match us:
    case True{}:
      num.us(st)
    case False{}:
      num.digit(st, c, NBase{})

# a digit of a prefixed integer, or an underscore
def num.based(st: Num, +c: Char) -> Num:
  num.based.go(Char.is_eq(c, '_'), st, c)

# a capital exponent, or a rejected character
def num.frac.exp2(ee: Bool, st: Num, _c: Char) -> Num:
  match ee:
    case True{}:
      num.exp(st)
    case False{}:
      num.bad(st, "invalid fraction")

# an exponent in a fraction
def num.frac.exp(e: Bool, ee: Bool, st: Num, +c: Char) -> Num:
  match e:
    case True{}:
      num.exp(st)
    case False{}:
      num.frac.exp2(ee, st, c)

# an underscore or an exponent in a fraction
def num.frac.us(us: Bool, e: Bool, ee: Bool, st: Num, +c: Char) -> Num:
  match us:
    case True{}:
      num.us(st)
    case False{}:
      num.frac.exp(e, ee, st, c)

# a fraction digit, an underscore, or an exponent
def num.frac.go(digit: Bool, us: Bool, e: Bool, ee: Bool, st: Num, +c: Char) -> Num:
  match digit:
    case True{}:
      num.digit(st, c, NFrac{})
    case False{}:
      num.frac.us(us, e, ee, st, c)

# a fraction digit, an underscore, or an exponent
def num.frac(st: Num, +c: Char) -> Num:
  num.frac.go(Char.is_digit(c), Char.is_eq(c, '_'), Char.is_eq(c, 'e'),
    Char.is_eq(c, 'E'), st, c)

# the exponent sign is part of the spelling; digits follow
def num.exp.sign(st: Num) -> Num:
  Num{_nk, sign, _b, _ds, _us, _saw, _why} = st
  Num{NEDig{}, sign, 10, [], False{}, False{}, ""}

# a digit of the exponent
def num.expon.digit(digit: Bool, st: Num, +c: Char) -> Num:
  match digit:
    case True{}:
      num.digit(st, c, NEDig{})
    case False{}:
      num.bad(st, "invalid exponent")

# a minus or a digit in an exponent
def num.expon.minus(minus: Bool, digit: Bool, st: Num, +c: Char) -> Num:
  match minus:
    case True{}:
      num.exp.sign(st)
    case False{}:
      num.expon.digit(digit, st, c)

# the sign or the first digit of an exponent
def num.expon.go(plus: Bool, minus: Bool, digit: Bool, st: Num, +c: Char) -> Num:
  match plus:
    case True{}:
      num.exp.sign(st)
    case False{}:
      num.expon.minus(minus, digit, st, c)

# the sign or the first digit of an exponent
def num.expon(st: Num, +c: Char) -> Num:
  num.expon.go(Char.is_eq(c, '+'), Char.is_eq(c, '-'), Char.is_digit(c), st, c)

# an underscore in an exponent
def num.edig.us(us: Bool, st: Num, _c: Char) -> Num:
  match us:
    case True{}:
      num.us(st)
    case False{}:
      num.bad(st, "invalid exponent")

# an exponent digit or an underscore
def num.edig.go(digit: Bool, us: Bool, st: Num, +c: Char) -> Num:
  match digit:
    case True{}:
      num.digit(st, c, NEDig{})
    case False{}:
      num.edig.us(us, st, c)

# an exponent digit or an underscore
def num.edig(st: Num, +c: Char) -> Num:
  num.edig.go(Char.is_digit(c), Char.is_eq(c, '_'), st, c)

# one character of a numeral
def num.on(nk: NK, st: Num, +c: Char) -> Num:
  match nk:
    case NLead{}:
      num.lead(st, c)
    case NZero{}:
      num.zero(st, c)
    case NDig{}:
      num.digs(st, c)
    case NBase{}:
      num.based(st, c)
    case NFrac{}:
      num.frac(st, c)
    case NExp{}:
      num.expon(st, c)
    case NEDig{}:
      num.edig(st, c)
    case NBad{}:
      st

# one character of a numeral
def num.step.go(st: Num, +c: Char) -> Num:
  Num{+nk, sign, base, ds, us, saw, why} = st
  num.on(nk, Num{nk, sign, base, ds, us, saw, why}, c)

# one character of a numeral
def num.step(st: Num, +c: Char) -> Num:
  num.step.go(st, c)

# the walk over a numeral
def num.go(cs: List<&2, Char>, st: Num) -> Num:
  match cs:
    case []:
      st
    case +h <> t:
      num.go(t, num.step(st, h))

# a numeral needs a digit in its last run
def num.fin.saw(saw: Bool, val: Val) -> Got:
  match saw:
    case False{}:
      GotBad{"invalid number"}
    case True{}:
      GotVal{val}

# the kind of numeral the scan finished in
def num.fin.nk(nk: NK, sign: Sign, ds: List<&2, U32>, saw: Bool, why: String,
  cs: List<&2, Char>) -> Got:
  match nk:
    case NBad{}:
      GotBad{why}
    case NLead{}:
      GotBad{"invalid number"}
    case NZero{}:
      GotVal{VInt{sign, "0"}}
    case NDig{}:
      num.fin.saw(saw, VInt{sign, dec.text(ds)})
    case NBase{}:
      num.fin.saw(saw, VInt{sign, dec.text(ds)})
    case NFrac{}:
      num.fin.saw(saw, VFlo{sign, word.body(cs)})
    case NExp{}:
      GotBad{"invalid exponent"}
    case NEDig{}:
      num.fin.saw(saw, VFlo{sign, word.body(cs)})

# a trailing underscore is rejected
def num.fin.us(us: Bool, nk: NK, sign: Sign, ds: List<&2, U32>, saw: Bool,
  why: String, cs: List<&2, Char>) -> Got:
  match us:
    case True{}:
      GotBad{"invalid underscore"}
    case False{}:
      num.fin.nk(nk, sign, ds, saw, why, cs)

# the value of a finished numeral
def num.fin(st: Num, cs: List<&2, Char>) -> Got:
  Num{nk, sign, _base, ds, us, saw, why} = st
  num.fin.us(us, nk, sign, ds, saw, why, cs)

# a numeral token
def word.num(+cs: List<&2, Char>) -> Got:
  num.fin(num.go(cs, num.start()), cs)

# a datetime when the token has a colon or a dash, otherwise a numeral
def word.route.date(date: Bool, cs: List<&2, Char>) -> Got:
  match date:
    case True{}:
      word.from.when(when.read(cs))
    case False{}:
      word.num(cs)

# a special word, or a numeral
def word.route(g: Got, date: Bool, cs: List<&2, Char>) -> Got:
  match g:
    case GotVal{val}:
      GotVal{val}
    case GotBad{_}:
      word.route.date(date, cs)

# a bare word: a special, a datetime, or a numeral
def word.val(+cs: List<&2, Char>) -> Got:
  word.route(word.spec(String.from_list(cs)),
    word.or(word.colon(cs), word.dash(cs, True{})), cs)
# a change applied at the end of a key path
type Job is Data:
  JPut{val: Val}
  JDef{}
  JAot{}

# one table the walk has entered
type Fr is Data:
  FrNew{name: String, parent: List<&2, Val>, path: String, inl: Bool}
  FrRep{name: String, parent: List<&2, Val>, path: String}
  FrAot{name: String, parent: List<&2, Val>, pre: List<&2, Val>, path: String}

# the walk: the table being edited, and the frames above it
type Tw is Data:
  Tw{vs: List<&2, Val>, job: Job, stack: List<&2, Fr>, bad: String, pre: String,
    heads: List<&2, String>, inl: Bool}

# the root table after a walk
type End is Data:
  End{vs: List<&2, Val>, bad: String, heads: List<&2, String>}

# what a key in a table refers to
type Look is Data:
  KMiss{}
  KHead{path: String, rows: List<&2, Val>}
  KInl{}
  KAots{path: String, elems: List<&2, Val>}
  KNo{why: String}

# the last element of an array of tables
type Last is Data:
  LastSome{path: String, pre: List<&2, Val>, rows: List<&2, Val>}
  LastNo{why: String}

# the first error is kept
def err.first.go(empty: Bool, bad: String, why: String) -> String:
  match empty:
    case True{}:
      why
    case False{}:
      bad

# the first error is kept
def err.first(+bad: String, why: String) -> String:
  err.first.go(String.is_empty(bad), bad, why)

# a key found earlier wins
def find.step(eq: Bool, v: Val, more: Unit -> Hit) -> Hit:
  match eq:
    case True{}:
      Found{v}
    case False{}:
      more(Unit{})

# the first pair of this name
def rows.find(rows: List<&2, Val>, +name: String) -> Hit:
  match rows:
    case []:
      Miss{}
    case VPair{n, v} <> t:
      find.step(String.eq(n, name), v, _u => rows.find(t, name))
    case _ <> t:
      rows.find(t, name)

# the value written for a key, or Miss
def get(rows: List<&2, Val>, +name: String) -> Hit:
  rows.find(rows, name)

# replace the value of one pair
def rows.repl.step(eq: Bool, n: String, old: Val, val: Val,
  more: Unit -> List<&2, Val>) -> List<&2, Val>:
  match eq:
    case True{}:
      VPair{n, val} <> more(Unit{})
    case False{}:
      VPair{n, old} <> more(Unit{})

# replace every pair of this name
def rows.repl(rows: List<&2, Val>, +name: String, +val: Val) -> List<&2, Val>:
  match rows:
    case []:
      []
    case VPair{+n, old} <> t:
      rows.repl.step(String.eq(n, name), n, old, val, _u => rows.repl(t, name, val))
    case h <> t:
      h <> rows.repl(t, name, val)

# either flag
def heads.or(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      True{}
    case False{}:
      b

# whether a header path was opened by a header
def heads.has(hs: List<&2, String>, +p: String) -> Bool:
  match hs:
    case []:
      False{}
    case h <> t:
      heads.or(String.eq(h, p), heads.has(t, p))

# a dotted path from a prefix and one segment
def tree.pre.go(empty: Bool, pre: String, name: String) -> String:
  match empty:
    case True{}:
      key(name)
    case False{}:
      pre ++ "." ++ key(name)

# a dotted path from a prefix and one segment
def tree.pre(+pre: String, name: String) -> String:
  tree.pre.go(String.is_empty(pre), pre, name)

# the value a key already holds
def look.of(v: Val) -> Look:
  match v:
    case VHead{path, rows}:
      KHead{path, rows}
    case VInl{_rows}:
      KInl{}
    case VAots{path, elems}:
      KAots{path, elems}
    case _:
      KNo{"not a table"}

# the matching pair, or the rest of the table
def look.step(eq: Bool, v: Val, more: Unit -> Look) -> Look:
  match eq:
    case True{}:
      look.of(v)
    case False{}:
      more(Unit{})

# what a key in this table refers to
def rows.look(rows: List<&2, Val>, +name: String) -> Look:
  match rows:
    case []:
      KMiss{}
    case VPair{n, v} <> t:
      look.step(String.eq(n, name), v, _u => rows.look(t, name))
    case _ <> t:
      rows.look(t, name)

# the last element, when the list has run out on a value
def look.last.one(v: Val, path: String, pre: List<&2, Val>) -> Last:
  match v:
    case VAot{_p, rows}:
      LastSome{path, List.reverse(&2, Val, pre), rows}
    case _:
      LastNo{"not a table"}

# the last element of an array of tables, and the elements before it
def look.last(elems: List<&2, Val>, path: String, pre: List<&2, Val>) -> Last:
  match elems:
    case []:
      LastNo{"empty array of tables"}
    case +h <> t:
      match t:
        case []:
          look.last.one(h, path, pre)
        case _ <> _:
          look.last(t, path, h <> pre)

# a new implicit table, inline or standard
def tree.wrap.new(inl: Bool, name: String, parent: List<&2, Val>, path: String,
  child: List<&2, Val>) -> List<&2, Val>:
  match inl:
    case True{}:
      List.append(&2, Val, parent, [VPair{name, VInl{child}}])
    case False{}:
      List.append(&2, Val, parent, [VPair{name, VHead{path, child}}])

# put the child rows back into the parent table
def tree.wrap(fr: Fr, child: List<&2, Val>) -> List<&2, Val>:
  match fr:
    case FrNew{name, parent, path, inl}:
      tree.wrap.new(inl, name, parent, path, child)
    case FrRep{name, parent, path}:
      rows.repl(parent, name, VHead{path, child})
    case FrAot{name, parent, pre, +path}:
      rows.repl(parent, name,
        VAots{path, List.append(&2, Val, pre, [VAot{path, child}])})

# walk the frames back to the root
def tree.rebuild(stack: List<&2, Fr>, vs: List<&2, Val>, bad: String,
  heads: List<&2, String>) -> End:
  match stack:
    case []:
      End{vs, bad, heads}
    case fr <> t:
      tree.rebuild(t, tree.wrap(fr, vs), bad, heads)

# a key that is already present is a duplicate
def tree.leaf.put(hit: Hit, name: String, vs: List<&2, Val>, val: Val,
  stack: List<&2, Fr>, bad: String, heads: List<&2, String>) -> End:
  match hit:
    case Found{_v}:
      tree.rebuild(stack, vs, err.first(bad, "duplicate key"), heads)
    case Miss{}:
      tree.rebuild(stack, List.append(&2, Val, vs, [VPair{name, val}]), bad, heads)

# an explicit header for a table that already exists
def tree.leaf.def.head(seen: Bool, name: String, vs: List<&2, Val>,
  rows: List<&2, Val>, stack: List<&2, Fr>, bad: String, +path: String,
  heads: List<&2, String>) -> End:
  match seen:
    case True{}:
      tree.rebuild(stack, vs, err.first(bad, "duplicate table"), heads)
    case False{}:
      tree.rebuild(stack, rows.repl(vs, name, VHead{path, rows}), bad, path <> heads)

# open a standard table
def tree.leaf.def.hit(hit: Look, name: String, vs: List<&2, Val>,
  stack: List<&2, Fr>, bad: String, +path: String, +heads: List<&2, String>) -> End:
  match hit:
    case KMiss{}:
      tree.rebuild(stack,
        List.append(&2, Val, vs, [VPair{name, VHead{path, []}}]), bad, path <> heads)
    case KHead{_p, rows}:
      tree.leaf.def.head(heads.has(heads, path), name, vs, rows, stack, bad, path,
        heads)
    case KInl{}:
      tree.rebuild(stack, vs, err.first(bad, "inline table is closed"), heads)
    case KAots{_p, _elems}:
      tree.rebuild(stack, vs, err.first(bad, "not a table"), heads)
    case KNo{why}:
      tree.rebuild(stack, vs, err.first(bad, why), heads)

# open a standard table
def tree.leaf.def(hit: Look, +name: String, vs: List<&2, Val>, stack: List<&2, Fr>,
  bad: String, pre: String, heads: List<&2, String>) -> End:
  tree.leaf.def.hit(hit, name, vs, stack, bad, tree.pre(pre, name), heads)

# append one element of an array of tables
def tree.leaf.aot.hit(hit: Look, name: String, vs: List<&2, Val>,
  stack: List<&2, Fr>, bad: String, +path: String, heads: List<&2, String>) -> End:
  match hit:
    case KMiss{}:
      tree.rebuild(stack, List.append(&2, Val, vs,
        [VPair{name, VAots{path, [VAot{path, []}]}}]), bad, heads)
    case KAots{_p, elems}:
      tree.rebuild(stack, rows.repl(vs, name,
        VAots{path, List.append(&2, Val, elems, [VAot{path, []}])}), bad, heads)
    case KHead{_p, _rows}:
      tree.rebuild(stack, vs, err.first(bad, "not a table"), heads)
    case KInl{}:
      tree.rebuild(stack, vs, err.first(bad, "inline table is closed"), heads)
    case KNo{why}:
      tree.rebuild(stack, vs, err.first(bad, why), heads)

# append one element of an array of tables
def tree.leaf.aot(hit: Look, +name: String, vs: List<&2, Val>, stack: List<&2, Fr>,
  bad: String, pre: String, heads: List<&2, String>) -> End:
  tree.leaf.aot.hit(hit, name, vs, stack, bad, tree.pre(pre, name), heads)

# the key at the end of the path
def tree.leaf.job(job: Job, +name: String, +vs: List<&2, Val>, stack: List<&2, Fr>,
  bad: String, pre: String, heads: List<&2, String>) -> End:
  match job:
    case JPut{val}:
      tree.leaf.put(get(vs, name), name, vs, val, stack, bad, heads)
    case JDef{}:
      tree.leaf.def(rows.look(vs, name), name, vs, stack, bad, pre, heads)
    case JAot{}:
      tree.leaf.aot(rows.look(vs, name), name, vs, stack, bad, pre, heads)

# a failed walk rebuilds what it has
def tree.leaf.bad(ok: Bool, name: String, vs: List<&2, Val>, job: Job,
  stack: List<&2, Fr>, bad: String, pre: String, heads: List<&2, String>) -> End:
  match ok:
    case False{}:
      tree.rebuild(stack, vs, bad, heads)
    case True{}:
      tree.leaf.job(job, name, vs, stack, bad, pre, heads)

# the key at the end of the path
def tree.leaf(name: String, tw: Tw) -> End:
  Tw{vs, job, stack, +bad, pre, heads, _inl} = tw
  tree.leaf.bad(String.is_empty(bad), name, vs, job, stack, bad, pre, heads)

# enter the last element of an array of tables
def tree.sub.aots(last: Last, +name: String, +vs: List<&2, Val>, job: Job,
  stack: List<&2, Fr>, +pre: String, heads: List<&2, String>, inl: Bool,
  path: String) -> Tw:
  match last:
    case LastSome{_p, prefix, rows}:
      Tw{rows, job, FrAot{name, vs, prefix, path} <> stack, "", tree.pre(pre, name),
        heads, inl}
    case LastNo{why}:
      Tw{vs, job, stack, why, pre, heads, inl}

# descend into one key, or record why it cannot be entered
def tree.sub.look(hit: Look, +name: String, +vs: List<&2, Val>, job: Job,
  stack: List<&2, Fr>, +pre: String, heads: List<&2, String>, +inl: Bool) -> Tw:
  match hit:
    case KMiss{}:
      Tw{[], job, FrNew{name, vs, tree.pre(pre, name), inl} <> stack, "",
        tree.pre(pre, name), heads, inl}
    case KHead{path, rows}:
      Tw{rows, job, FrRep{name, vs, path} <> stack, "", tree.pre(pre, name), heads,
        inl}
    case KInl{}:
      Tw{vs, job, stack, "inline table is closed", pre, heads, inl}
    case KAots{+path, elems}:
      tree.sub.aots(look.last(elems, path, []), name, vs, job, stack, pre, heads, inl,
        path)
    case KNo{why}:
      Tw{vs, job, stack, why, pre, heads, inl}

# descend into one key when the walk is still well
def tree.sub.bad(ok: Bool, +name: String, +vs: List<&2, Val>, job: Job,
  stack: List<&2, Fr>, bad: String, pre: String, heads: List<&2, String>,
  inl: Bool) -> Tw:
  match ok:
    case False{}:
      Tw{vs, job, stack, bad, pre, heads, inl}
    case True{}:
      tree.sub.look(rows.look(vs, name), name, vs, job, stack, pre, heads, inl)

# descend into one key
def tree.sub(name: String, tw: Tw) -> Tw:
  Tw{+vs, job, stack, +bad, pre, heads, inl} = tw
  tree.sub.bad(String.is_empty(bad), name, vs, job, stack, bad, pre, heads, inl)

# an empty path records an error
def tree.walk.none(tw: Tw) -> End:
  Tw{vs, _job, stack, bad, _pre, heads, _inl} = tw
  tree.rebuild(stack, vs, err.first(bad, "empty key"), heads)

# follow a key path and apply the job at its end
def tree.walk(path: List<&2, String>, tw: Tw) -> End:
  match path:
    case []:
      tree.walk.none(tw)
    case name <> rest:
      match rest:
        case []:
          tree.leaf(name, tw)
        case _ <> _:
          tree.walk(rest, tree.sub(name, tw))

# space or tab
def ch.sp(+c: Char) -> Bool:
  Bool.or(U32.is_eq(Char.to_u32(c), 32), U32.is_eq(Char.to_u32(c), 9))

# line feed or carriage return
def ch.nl(+c: Char) -> Bool:
  Bool.or(U32.is_eq(Char.to_u32(c), 10), U32.is_eq(Char.to_u32(c), 13))

# a character that ends a bare value
def ch.delim(+c: Char) -> Bool:
  Bool.or(ch.sp(c), Bool.or(ch.nl(c), Bool.or(Char.is_eq(c, '#'),
    Bool.or(Char.is_eq(c, ','), Bool.or(Char.is_eq(c, ']'), Char.is_eq(c, '}'))))))

# whitespace that a bare value swallows
def ch.skip(+c: Char) -> Bool:
  Bool.or(ch.sp(c), ch.nl(c))

# the quote character of a string kind
def q.char(k: QKind) -> Char:
  match k:
    case QLit{}:
      '\''
    case QMultiLit{}:
      '\''
    case _:
      '"'

# a multiline string
def q.multi(k: QKind) -> Bool:
  match k:
    case QMulti{}:
      True{}
    case QMultiLit{}:
      True{}
    case _:
      False{}

# a basic string, which has escapes
def q.basic(k: QKind) -> Bool:
  match k:
    case QBasic{}:
      True{}
    case QMulti{}:
      True{}
    case _:
      False{}

# the multiline kind of a one-line kind
def q.as.multi(k: QKind) -> QKind:
  match k:
    case QLit{}:
      QMultiLit{}
    case _:
      QMulti{}

# a pattern character that stands for a digit
def date.mode(p: Char) -> Bool:
  U32.is_eq(Char.to_u32(p), 68)

# whether the rest of the shape matches
def date.eq.go(ok: Bool, more: Unit -> Bool) -> Bool:
  match ok:
    case False{}:
      False{}
    case True{}:
      more(Unit{})

# one character of a date shape
def date.step(mode: Bool, digit: Bool, same: Bool, more: Unit -> Bool) -> Bool:
  match mode:
    case True{}:
      date.eq.go(digit, more)
    case False{}:
      date.eq.go(same, more)

# both lists ended together
def date.eq.nil(pat: List<&2, Char>) -> Bool:
  match pat:
    case []:
      True{}
    case _ <> _:
      False{}

# YYYY-MM-DD, with D standing for a digit
def date.eq(cs: List<&2, Char>, pat: List<&2, Char>) -> Bool:
  match cs:
    case []:
      date.eq.nil(pat)
    case +h <> t:
      match pat:
        case []:
          False{}
        case +p <> r:
          date.step(date.mode(p), Char.is_digit(h), Char.is_eq(h, p),
            _u => date.eq(t, r))

# the buffer is a calendar date
def date.shaped(buf: List<&2, Char>) -> Bool:
  date.eq(List.reverse(&2, Char, buf), String.to_list("DDDD-DD-DD"))

# the buffer, in order
def buf.str(buf: List<&2, Char>) -> String:
  String.from_list(List.reverse(&2, Char, buf))

# the key path, document table then this key
def path.cat(here: List<&2, String>, parts: List<&2, String>) -> List<&2, String>:
  List.append(&2, String, here, List.reverse(&2, String, parts))

# a multiline string keeps a newline
def str.bad.nl(nl: Bool, multi: Bool) -> Bool:
  match nl:
    case False{}:
      True{}
    case True{}:
      Bool.not(multi)

# tab is kept
def str.bad.tab(tab: Bool, nl: Bool, multi: Bool) -> Bool:
  match tab:
    case True{}:
      False{}
    case False{}:
      str.bad.nl(nl, multi)

# a raw control is rejected
def str.bad.go(ctrl: Bool, tab: Bool, nl: Bool, multi: Bool) -> Bool:
  match ctrl:
    case False{}:
      False{}
    case True{}:
      str.bad.tab(tab, nl, multi)

# a raw control is rejected. Tab is kept. A multiline string also keeps newlines
def str.bad(+u: U32, multi: Bool) -> Bool:
  str.bad.go(Bool.or(U32.is_lt(u, 32), U32.is_eq(u, 127)), U32.is_eq(u, 9),
    Bool.or(U32.is_eq(u, 10), U32.is_eq(u, 13)), multi)

# the scanner has failed
def st.err(st: St, why: String) -> St:
  St{+bad, rows, heads, here, parts, buf, _lex, back, qkind, stack, _hold, uni, left,
    arrtab, lead} = st
  St{err.first(bad, why), rows, heads, here, parts, buf, LSink{}, back, qkind, stack,
    HNone{}, uni, left, arrtab, lead}

# replace the lex state
def st.lex(st: St, lex: Lex) -> St:
  St{bad, rows, heads, here, parts, buf, _lex, back, qkind, stack, hold, uni, left,
    arrtab, lead} = st
  St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left,
    arrtab, lead}

# hold one character and set the lex state
def st.hold(st: St, +lex: Lex, c: Char) -> St:
  St{bad, rows, heads, here, parts, buf, _lex, _back, qkind, stack, _hold, uni, left,
    arrtab, lead} = st
  St{bad, rows, heads, here, parts, buf, lex, lex, qkind, stack, HChar{c}, uni, left,
    arrtab, lead}

# append one character
def st.push(st: St, c: Char, lex: Lex) -> St:
  St{bad, rows, heads, here, parts, buf, _lex, back, qkind, stack, hold, uni, left,
    arrtab, lead} = st
  St{bad, rows, heads, here, parts, c <> buf, lex, back, qkind, stack, hold, uni, left,
    arrtab, lead}

# the segment in the buffer joins the key, and the buffer is cleared
def seg.push(st: St, lex: Lex) -> St:
  St{bad, rows, heads, here, parts, buf, _lex, back, qkind, stack, hold, uni, left,
    arrtab, lead} = st
  St{bad, rows, heads, here, buf.str(buf) <> parts, [], lex, back, qkind, stack, hold,
    uni, left, arrtab, lead}

# a finished value at the document root
def take.root(end: End, here: List<&2, String>, back: Lex, qkind: QKind, uni: U32,
  left: U32, arrtab: Bool, lead: Bool) -> St:
  End{rows, bad, heads} = end
  St{bad, rows, heads, here, [], [], LTop{}, back, qkind, [], HNone{}, uni, left, arrtab,
    lead}

# a finished value inside an inline table
def take.inl(end: End, rows: List<&2, Val>, heads: List<&2, String>,
  +here: List<&2, String>, +parts: List<&2, String>, rest: List<&2, Ctx>, back: Lex,
  qkind: QKind, uni: U32, left: U32, arrtab: Bool, lead: Bool) -> St:
  End{inl, bad, _h} = end
  St{bad, rows, heads, here, [], [], LInlC{}, back, qkind,
    CInl{inl, parts, here} <> rest, HNone{}, uni, left, arrtab, lead}

# place a finished value into the current table, array, or inline table
def take.top(stack: List<&2, Ctx>, val: Val, bad: String, rows: List<&2, Val>,
  heads: List<&2, String>, +here: List<&2, String>, parts: List<&2, String>, back: Lex,
  qkind: QKind, uni: U32, left: U32, arrtab: Bool, lead: Bool) -> St:
  match stack:
    case []:
      take.root(tree.walk(path.cat(here, parts),
        Tw{rows, JPut{val}, [], bad, "", heads, False{}}), here, back, qkind, uni, left,
        arrtab, lead)
    case CArr{items, +saved, +at} <> rest:
      St{bad, rows, heads, at, saved, [], LArrC{}, back, qkind,
        CArr{val <> items, saved, at} <> rest, HNone{}, uni, left, arrtab, lead}
    case CInl{inl, +saved, +at} <> rest:
      take.inl(tree.walk(List.reverse(&2, String, parts),
        Tw{inl, JPut{val}, [], bad, "", [], True{}}), rows, heads, at, saved, rest, back,
        qkind, uni, left, arrtab, lead)

# place a finished value
def val.take(st: St, val: Val) -> St:
  St{bad, rows, heads, here, parts, _buf, _lex, back, qkind, stack, _hold, uni, left,
    arrtab, lead} = st
  take.top(stack, val, bad, rows, heads, here, parts, back, qkind, uni, left, arrtab,
    lead)

# hold the delimiter when the following state must see it
def bare.hold.on(st: St, c: Char) -> St:
  St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, _h, uni, left,
    arrtab, lead} = st
  St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, HChar{c}, uni, left,
    arrtab, lead}

# hold the delimiter when the following state must see it
def bare.hold(st: St, c: Char, hold: Bool) -> St:
  match hold:
    case False{}:
      st
    case True{}:
      bare.hold.on(st, c)

# a bare word has been classified
def bare.got(g: Got, st: St, c: Char, hold: Bool) -> St:
  match g:
    case GotBad{why}:
      st.err(st, why)
    case GotVal{val}:
      bare.hold(val.take(st, val), c, hold)

# finish a bare word. hold is true when the delimiter is not whitespace
def bare.finish(st: St, c: Char, hold: Bool) -> St:
  St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, h, uni, left, arrtab,
    lead} = st
  bare.got(word.val(List.reverse(&2, Char, buf)),
    St{bad, rows, heads, here, parts, [], lex, back, qkind, stack, h, uni, left, arrtab,
      lead}, c, hold)

# close the header that was just read
def head.apply(end: End, segs: List<&2, String>, back: Lex, qkind: QKind, uni: U32,
  left: U32, lead: Bool) -> St:
  End{rows, bad, heads} = end
  St{bad, rows, heads, segs, [], [], LTop{}, back, qkind, [], HNone{}, uni, left,
    False{}, lead}

# an array-of-tables header, or a table header
def head.job(arr: Bool, bad: String, rows: List<&2, Val>, heads: List<&2, String>,
  +segs: List<&2, String>, back: Lex, qkind: QKind, uni: U32, left: U32, lead: Bool)
  -> St:
  match arr:
    case True{}:
      head.apply(tree.walk(segs, Tw{rows, JAot{}, [], bad, "", heads, False{}}), segs,
        back, qkind, uni, left, lead)
    case False{}:
      head.apply(tree.walk(segs, Tw{rows, JDef{}, [], bad, "", heads, False{}}), segs,
        back, qkind, uni, left, lead)

# open the table or the array of tables named by the header
def head.on(st: St, segs: List<&2, String>) -> St:
  St{bad, rows, heads, _here, _parts, _buf, _lex, back, qkind, _stack, _hold, uni, left,
    arrtab, lead} = st
  head.job(arrtab, bad, rows, heads, segs, back, qkind, uni, left, lead)

# the header key is ready
def head.go(empty: Bool, st: St, segs: List<&2, String>) -> St:
  match empty:
    case True{}:
      st.err(st, "empty key")
    case False{}:
      head.on(st, segs)

# the segment was pushed
def head.use(st: St) -> St:
  St{bad, rows, heads, here, +parts, buf, lex, back, qkind, stack, hold, uni, left,
    arrtab, lead} = st
  head.go(List.is_empty(&2, String, parts),
    St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left,
      arrtab, lead}, List.reverse(&2, String, parts))

# the buffer is the last segment when it holds one
def head.fin.buf(empty: Bool, st: St) -> St:
  match empty:
    case True{}:
      head.use(st)
    case False{}:
      head.use(seg.push(st, LTop{}))

# push a trailing segment, then open the header
def head.fin(st: St) -> St:
  St{bad, rows, heads, here, parts, +buf, lex, back, qkind, stack, hold, uni, left,
    arrtab, lead} = st
  head.fin.buf(List.is_empty(&2, Char, buf),
    St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left,
      arrtab, lead})

# close an array and place it
def arr.top(stack: List<&2, Ctx>, bad: String, rows: List<&2, Val>,
  heads: List<&2, String>, back: Lex, qkind: QKind, uni: U32, left: U32, arrtab: Bool,
  lead: Bool) -> St:
  match stack:
    case CArr{items, parts, here} <> rest:
      val.take(St{bad, rows, heads, here, parts, [], LTop{}, back, qkind, rest, HNone{},
        uni, left, arrtab, lead}, VArr{List.reverse(&2, Val, items)})
    case _:
      St{err.first(bad, "unclosed"), rows, heads, [], [], [], LSink{}, back, qkind, [],
        HNone{}, uni, left, arrtab, lead}

# close an array and place it
def arr.close(st: St) -> St:
  St{bad, rows, heads, _here, _parts, _buf, _lex, back, qkind, stack, _hold, uni, left,
    arrtab, lead} = st
  arr.top(stack, bad, rows, heads, back, qkind, uni, left, arrtab, lead)

# close an inline table and place it
def inl.top(stack: List<&2, Ctx>, bad: String, rows: List<&2, Val>,
  heads: List<&2, String>, back: Lex, qkind: QKind, uni: U32, left: U32, arrtab: Bool,
  lead: Bool) -> St:
  match stack:
    case CInl{inl, parts, here} <> rest:
      val.take(St{bad, rows, heads, here, parts, [], LTop{}, back, qkind, rest, HNone{},
        uni, left, arrtab, lead}, VInl{inl})
    case _:
      St{err.first(bad, "unclosed"), rows, heads, [], [], [], LSink{}, back, qkind, [],
        HNone{}, uni, left, arrtab, lead}

# close an inline table and place it
def inl.close(st: St) -> St:
  St{bad, rows, heads, _here, _parts, _buf, _lex, back, qkind, stack, _hold, uni, left,
    arrtab, lead} = st
  inl.top(stack, bad, rows, heads, back, qkind, uni, left, arrtab, lead)

# the innermost frame is an inline table
def inl.open(stack: List<&2, Ctx>) -> Bool:
  match stack:
    case CInl{_rows, _parts, _here} <> _rest:
      True{}
    case _:
      False{}

# a string is finished
def str.fin(st: St) -> St:
  St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab,
    lead} = st
  val.take(St{bad, rows, heads, here, parts, [], lex, back, qkind, stack, hold, uni, left,
    arrtab, lead}, VStr{buf.str(buf)})

# one or two quotes that did not close a multiline string
def mq.put(one: Bool, +q: Char, buf: List<&2, Char>) -> List<&2, Char>:
  match one:
    case True{}:
      q <> buf
    case False{}:
      q <> (q <> buf)

# a code point may be written as a character
def uni.ok(+u: U32) -> Bool:
  Bool.and(U32.is_le(u, 1114111),
    Bool.not(Bool.and(U32.is_ge(u, 55296), U32.is_le(u, 57343))))

# a finished unicode escape written into the buffer
def uni.finish.on(st: St, u: U32, back: Lex) -> St:
  St{bad, rows, heads, here, parts, buf, _lex, b, qkind, stack, _hold, _uni, _left,
    arrtab, lead} = st
  St{bad, rows, heads, here, parts, Char.from_u32(u) <> buf, back, b, qkind, stack,
    HNone{}, 0, 0, arrtab, lead}

# a finished unicode escape
def uni.finish(ok: Bool, st: St, u: U32, back: Lex) -> St:
  match ok:
    case False{}:
      st.err(st, "invalid escape")
    case True{}:
      uni.finish.on(st, u, back)

# another hex digit is still required
def uni.next.more(st: St, u: U32, left: U32) -> St:
  St{bad, rows, heads, here, parts, buf, lex, b, qkind, stack, hold, _uni, _left,
    arrtab, lead} = st
  St{bad, rows, heads, here, parts, buf, lex, b, qkind, stack, hold, u,
    U32.sub(left, 1), arrtab, lead}

# the escape is finished, or another hex digit is required
def uni.next(last: Bool, st: St, +u: U32, back: Lex, left: U32) -> St:
  match last:
    case True{}:
      uni.finish(uni.ok(u), st, u, back)
    case False{}:
      uni.next.more(st, u, left)

# one hex digit of a unicode escape
def uni.go(ok: Bool, st: St, +c: Char, back: Lex, uni: U32, +left: U32) -> St:
  match ok:
    case False{}:
      st.err(st, "invalid escape")
    case True{}:
      uni.next(U32.is_eq(left, 1), st, U32.add(U32.mul(uni, 16), dig.val(c)), back, left)

# one hex digit of a unicode escape
def uni.step(st: St, +c: Char, back: Lex) -> St:
  St{bad, rows, heads, here, parts, buf, lex, b, qkind, stack, hold, +uni, +left, arrtab,
    lead} = st
  uni.go(dig.ok(dig.val(c), 16),
    St{bad, rows, heads, here, parts, buf, lex, b, qkind, stack, hold, uni, left, arrtab,
      lead}, c, back, uni, left)

# a long unicode escape, or an unknown escape
def esc.uu(uu: Bool) -> Esc:
  match uu:
    case True{}:
      EUni{8}
    case False{}:
      EBad{}

# a unicode escape
def esc.u(u: Bool, uu: Bool) -> Esc:
  match u:
    case True{}:
      EUni{4}
    case False{}:
      esc.uu(uu)

# carriage return or a unicode escape
def esc.r(r: Bool, u: Bool, uu: Bool) -> Esc:
  match r:
    case True{}:
      EChar{'\r'}
    case False{}:
      esc.u(u, uu)

# form feed or the rest
def esc.f(f: Bool, r: Bool, u: Bool, uu: Bool) -> Esc:
  match f:
    case True{}:
      EChar{Chr{12}}
    case False{}:
      esc.r(r, u, uu)

# newline or the rest
def esc.n(n: Bool, f: Bool, r: Bool, u: Bool, uu: Bool) -> Esc:
  match n:
    case True{}:
      EChar{'\n'}
    case False{}:
      esc.f(f, r, u, uu)

# tab, newline, form feed, carriage return, or a unicode escape
def esc.t(t: Bool, n: Bool, f: Bool, r: Bool, u: Bool, uu: Bool) -> Esc:
  match t:
    case True{}:
      EChar{'\t'}
    case False{}:
      esc.n(n, f, r, u, uu)

# backslash, quotation mark, or a letter escape
def esc.letter(b: Bool, t: Bool, n: Bool, f: Bool, r: Bool, u: Bool, uu: Bool) -> Esc:
  match b:
    case True{}:
      EChar{Chr{8}}
    case False{}:
      esc.t(t, n, f, r, u, uu)

# spaces before the newline of a line-ending backslash
def esc.sp(sp: Bool, b: Bool, t: Bool, n: Bool, f: Bool, r: Bool, u: Bool, uu: Bool)
  -> Esc:
  match sp:
    case True{}:
      EFold{False{}}
    case False{}:
      esc.letter(b, t, n, f, r, u, uu)

# a line-ending backslash, or a letter
def esc.fold(nl: Bool, sp: Bool, b: Bool, t: Bool, n: Bool, f: Bool, r: Bool, u: Bool,
  uu: Bool) -> Esc:
  match nl:
    case True{}:
      EFold{True{}}
    case False{}:
      esc.sp(sp, b, t, n, f, r, u, uu)

# a backslash or a letter
def esc.bs(bs: Bool, b: Bool, t: Bool, n: Bool, f: Bool, r: Bool, u: Bool, uu: Bool,
  nl: Bool, sp: Bool) -> Esc:
  match bs:
    case True{}:
      EChar{'\\'}
    case False{}:
      esc.fold(nl, sp, b, t, n, f, r, u, uu)

# a quote, a backslash, or a letter
def esc.of.go(q: Bool, bs: Bool, b: Bool, t: Bool, n: Bool, f: Bool, r: Bool, u: Bool,
  uu: Bool, nl: Bool, sp: Bool) -> Esc:
  match q:
    case True{}:
      EChar{'"'}
    case False{}:
      esc.bs(bs, b, t, n, f, r, u, uu, nl, sp)

# classify one escaped character
def esc.of(+c: Char) -> Esc:
  esc.of.go(Char.is_eq(c, '"'), Char.is_eq(c, '\\'), Char.is_eq(c, 'b'),
    Char.is_eq(c, 't'), Char.is_eq(c, 'n'), Char.is_eq(c, 'f'), Char.is_eq(c, 'r'),
    Char.is_eq(c, 'u'), Char.is_eq(c, 'U'), ch.nl(c), ch.sp(c))

# the lex state that reads the hex digits of an escape
def esc.uni.lex(back: Lex) -> Lex:
  match back:
    case LKeyQ{}:
      LKeyU{}
    case LHeadQ{}:
      LHeadU{}
    case _:
      LUni{}

# a unicode escape starts with no digits seen
def esc.uni(st: St, back: Lex, n: U32) -> St:
  St{bad, rows, heads, here, parts, buf, _lex, b, qkind, stack, hold, _uni, _left,
    arrtab, lead} = st
  St{bad, rows, heads, here, parts, buf, esc.uni.lex(back), b, qkind, stack, hold, 0, n,
    arrtab, lead}

# 1 once a newline has been seen
def esc.fold.bit(saw: Bool) -> U32:
  match saw:
    case True{}:
      1
    case False{}:
      0

# a line-ending backslash skips following whitespace
def esc.fold.on(st: St, saw: Bool) -> St:
  St{bad, rows, heads, here, parts, buf, _lex, b, qkind, stack, hold, _uni, _left,
    arrtab, lead} = st
  St{bad, rows, heads, here, parts, buf, LFold{}, b, qkind, stack, hold, 0,
    esc.fold.bit(saw), arrtab, lead}

# a line-ending backslash is only part of a string
def esc.fold.use(back: Lex, st: St, saw: Bool) -> St:
  match back:
    case LStr{}:
      esc.fold.on(st, saw)
    case _:
      st.err(st, "invalid escape")

# apply one escape and return to the string
def esc.use(e: Esc, st: St, back: Lex) -> St:
  match e:
    case EChar{c}:
      st.push(st, c, back)
    case EUni{n}:
      esc.uni(st, back, n)
    case EFold{saw}:
      esc.fold.use(back, st, saw)
    case EBad{}:
      st.err(st, "invalid escape")

# the lex state a comment returns to
def com.enter(st: St, back: Lex) -> St:
  St{bad, rows, heads, here, parts, buf, _lex, _back, qkind, stack, hold, uni, left,
    arrtab, lead} = st
  St{bad, rows, heads, here, parts, buf, LCom{}, back, qkind, stack, hold, uni, left,
    arrtab, lead}

# a bare key, or a rejected character
def lex.top.bare(bare: Bool, st: St, c: Char) -> St:
  match bare:
    case True{}:
      st.push(st, c, LKey{})
    case False{}:
      st.err(st, "invalid key")

# a header starts with a clear key
def lex.bracket(st: St) -> St:
  St{bad, rows, heads, here, _parts, _buf, _lex, back, qkind, stack, hold, uni, left,
    _arr, lead} = st
  St{bad, rows, heads, here, [], [], LHead{}, back, qkind, stack, hold, uni, left,
    False{}, lead}

# a quoted key starts with an empty buffer
def lex.qkey(st: St, kind: QKind, lex: Lex) -> St:
  St{bad, rows, heads, here, parts, _buf, _lex, back, _q, stack, hold, uni, left, arrtab,
    lead} = st
  St{bad, rows, heads, here, parts, [], lex, back, kind, stack, hold, uni, left, arrtab,
    lead}

# a literal key or a bare key
def lex.top.lit(lit: Bool, bare: Bool, st: St, c: Char) -> St:
  match lit:
    case True{}:
      lex.qkey(st, QLit{}, LKeyQ{})
    case False{}:
      lex.top.bare(bare, st, c)

# a quoted key or a bare key
def lex.top.q(q: Bool, lit: Bool, bare: Bool, st: St, c: Char) -> St:
  match q:
    case True{}:
      lex.qkey(st, QBasic{}, LKeyQ{})
    case False{}:
      lex.top.lit(lit, bare, st, c)

# a header or a key
def lex.top.br(br: Bool, q: Bool, lit: Bool, bare: Bool, st: St, c: Char) -> St:
  match br:
    case True{}:
      lex.bracket(st)
    case False{}:
      lex.top.q(q, lit, bare, st, c)

# a comment, a header, or a key
def lex.top.hash(hash: Bool, br: Bool, q: Bool, lit: Bool, bare: Bool, st: St, c: Char)
  -> St:
  match hash:
    case True{}:
      com.enter(st, LTop{})
    case False{}:
      lex.top.br(br, q, lit, bare, st, c)

# a newline, a comment, a header, or a key
def lex.top.nl(nl: Bool, hash: Bool, br: Bool, q: Bool, lit: Bool, bare: Bool, st: St,
  c: Char) -> St:
  match nl:
    case True{}:
      st
    case False{}:
      lex.top.hash(hash, br, q, lit, bare, st, c)

# whitespace, a comment, a header, or a key
def lex.top.go(sp: Bool, nl: Bool, hash: Bool, br: Bool, q: Bool, lit: Bool, bare: Bool,
  st: St, c: Char) -> St:
  match sp:
    case True{}:
      st
    case False{}:
      lex.top.nl(nl, hash, br, q, lit, bare, st, c)

# top level: a key, a header, a comment, or whitespace
def lex.top(st: St, +c: Char) -> St:
  lex.top.go(ch.sp(c), ch.nl(c), Char.is_eq(c, '#'), Char.is_eq(c, '['),
    Char.is_eq(c, '"'), Char.is_eq(c, '\''), bare.at(c), st, c)

# a newline before equals is rejected
def lex.key.nl(nl: Bool, st: St, _c: Char) -> St:
  match nl:
    case True{}:
      st.err(st, "newline in key")
    case False{}:
      st.err(st, "invalid key")

# an empty segment is rejected
def lex.key.end.go(empty: Bool, st: St, lex: Lex) -> St:
  match empty:
    case True{}:
      st.err(st, "empty key")
    case False{}:
      seg.push(st, lex)

# end a nonempty segment
def lex.key.end(st: St, next: Lex) -> St:
  St{bad, rows, heads, here, parts, +buf, lx, back, qkind, stack, hold, uni, left,
    arrtab, lead} = st
  lex.key.end.go(List.is_empty(&2, Char, buf),
    St{bad, rows, heads, here, parts, buf, lx, back, qkind, stack, hold, uni, left,
      arrtab, lead}, next)

# a comment ends the segment and waits for equals
def lex.key.hash(hash: Bool, nl: Bool, st: St, c: Char) -> St:
  match hash:
    case True{}:
      com.enter(lex.key.end(st, LAfter{}), LAfter{})
    case False{}:
      lex.key.nl(nl, st, c)

# an equals ends the key
def lex.key.eq(eq: Bool, hash: Bool, nl: Bool, st: St, +c: Char) -> St:
  match eq:
    case True{}:
      lex.key.end(st, LVal{})
    case False{}:
      lex.key.hash(hash, nl, st, c)

# a dot ends the segment
def lex.key.dot(dot: Bool, eq: Bool, hash: Bool, nl: Bool, st: St, c: Char) -> St:
  match dot:
    case True{}:
      lex.key.end(st, LKey{})
    case False{}:
      lex.key.eq(eq, hash, nl, st, c)

# whitespace ends the segment
def lex.key.sp(sp: Bool, dot: Bool, eq: Bool, hash: Bool, nl: Bool, st: St, c: Char)
  -> St:
  match sp:
    case True{}:
      lex.key.end(st, LAfter{})
    case False{}:
      lex.key.dot(dot, eq, hash, nl, st, c)

# a bare character, whitespace, a dot, or an equals
def lex.key.go(bare: Bool, sp: Bool, dot: Bool, eq: Bool, hash: Bool, nl: Bool, st: St,
  c: Char) -> St:
  match bare:
    case True{}:
      st.push(st, c, LKey{})
    case False{}:
      lex.key.sp(sp, dot, eq, hash, nl, st, c)

# inside a bare key segment
def lex.key(st: St, +c: Char) -> St:
  lex.key.go(bare.at(c), ch.sp(c), Char.is_eq(c, '.'), Char.is_eq(c, '='),
    Char.is_eq(c, '#'), ch.nl(c), st, c)

# a newline before equals is rejected
def lex.after.nl(nl: Bool, st: St, _c: Char) -> St:
  match nl:
    case True{}:
      st.err(st, "newline in key")
    case False{}:
      st.err(st, "invalid key")

# a comment waits for equals
def lex.after.hash(hash: Bool, nl: Bool, st: St, c: Char) -> St:
  match hash:
    case True{}:
      com.enter(st, LAfter{})
    case False{}:
      lex.after.nl(nl, st, c)

# equals starts the value
def lex.after.eq(eq: Bool, hash: Bool, nl: Bool, st: St, c: Char) -> St:
  match eq:
    case True{}:
      st.lex(st, LVal{})
    case False{}:
      lex.after.hash(hash, nl, st, c)

# a dot starts the next segment
def lex.after.dot(dot: Bool, eq: Bool, hash: Bool, nl: Bool, st: St, c: Char) -> St:
  match dot:
    case True{}:
      st.lex(st, LKey{})
    case False{}:
      lex.after.eq(eq, hash, nl, st, c)

# whitespace, a dot, or an equals
def lex.after.go(sp: Bool, dot: Bool, eq: Bool, hash: Bool, nl: Bool, st: St, c: Char)
  -> St:
  match sp:
    case True{}:
      st
    case False{}:
      lex.after.dot(dot, eq, hash, nl, st, c)

# after a key segment, before equals or a dot
def lex.after(st: St, +c: Char) -> St:
  lex.after.go(ch.sp(c), Char.is_eq(c, '.'), Char.is_eq(c, '='), Char.is_eq(c, '#'),
    ch.nl(c), st, c)

# a newline inside an inline table is rejected
def lex.val.nl3(inside: Bool, st: St) -> St:
  match inside:
    case True{}:
      st.err(st, "newline in inline table")
    case False{}:
      st

# a newline inside an inline table is rejected
def lex.val.nl2(st: St, _c: Char) -> St:
  St{bad, rows, heads, here, parts, buf, lx, back, qkind, +stack, hold, uni, left,
    arrtab, lead} = st
  lex.val.nl3(inl.open(stack),
    St{bad, rows, heads, here, parts, buf, lx, back, qkind, stack, hold, uni, left,
      arrtab, lead})

# an array starts a frame and waits for a value
def lex.array(st: St) -> St:
  St{bad, rows, heads, +here, +parts, _buf, _lex, back, qkind, stack, hold, uni, left,
    arrtab, lead} = st
  St{bad, rows, heads, here, [], [], LArr{}, back, qkind,
    CArr{[], parts, here} <> stack, hold, uni, left, arrtab, lead}

# an inline table starts a frame and waits for a key
def lex.inline(st: St) -> St:
  St{bad, rows, heads, +here, +parts, _buf, _lex, back, qkind, stack, hold, uni, left,
    arrtab, lead} = st
  St{bad, rows, heads, here, [], [], LInl{}, back, qkind,
    CInl{[], parts, here} <> stack, hold, uni, left, arrtab, lead}

# an inline table, or a bare value
def lex.val.inl(inl: Bool, st: St, c: Char) -> St:
  match inl:
    case True{}:
      lex.inline(st)
    case False{}:
      st.push(st, c, LBare{})

# an array, or another value
def lex.val.br(br: Bool, inl: Bool, st: St, c: Char) -> St:
  match br:
    case True{}:
      lex.array(st)
    case False{}:
      lex.val.inl(inl, st, c)

# a literal string, or another value
def lex.val.lit(lit: Bool, br: Bool, inl: Bool, st: St, c: Char) -> St:
  match lit:
    case True{}:
      lex.qkey(st, QLit{}, LQ{})
    case False{}:
      lex.val.br(br, inl, st, c)

# a basic string, or another value
def lex.val.q(q: Bool, lit: Bool, br: Bool, inl: Bool, st: St, c: Char) -> St:
  match q:
    case True{}:
      lex.qkey(st, QBasic{}, LQ{})
    case False{}:
      lex.val.lit(lit, br, inl, st, c)

# a comment, a string, an array, an inline table, or a bare value
def lex.val.hash(hash: Bool, q: Bool, lit: Bool, br: Bool, inl: Bool, st: St, c: Char)
  -> St:
  match hash:
    case True{}:
      com.enter(st, LVal{})
    case False{}:
      lex.val.q(q, lit, br, inl, st, c)

# a newline is whitespace outside an inline table
def lex.val.nl(nl: Bool, hash: Bool, q: Bool, lit: Bool, br: Bool, inl: Bool, st: St,
  c: Char) -> St:
  match nl:
    case True{}:
      lex.val.nl2(st, c)
    case False{}:
      lex.val.hash(hash, q, lit, br, inl, st, c)

# whitespace or the value itself
def lex.val.go(sp: Bool, nl: Bool, hash: Bool, q: Bool, lit: Bool, br: Bool, inl: Bool,
  st: St, c: Char) -> St:
  match sp:
    case True{}:
      st
    case False{}:
      lex.val.nl(nl, hash, q, lit, br, inl, st, c)

# the start of a value
def lex.val(st: St, +c: Char) -> St:
  lex.val.go(ch.sp(c), ch.nl(c), Char.is_eq(c, '#'), Char.is_eq(c, '"'),
    Char.is_eq(c, '\''), Char.is_eq(c, '['), Char.is_eq(c, '{'), st, c)

# a second quote may start a multiline string; otherwise the first character is held
def lex.q.go(same: Bool, st: St, c: Char) -> St:
  match same:
    case True{}:
      st.lex(st, LQ2{})
    case False{}:
      st.hold(st.lex(st, LStr{}), LStr{}, c)

# the first quote has been seen
def lex.q(st: St, +c: Char) -> St:
  St{bad, rows, heads, here, parts, buf, lx, back, +qkind, stack, hold, uni, left,
    arrtab, lead} = st
  lex.q.go(Char.is_eq(c, q.char(qkind)),
    St{bad, rows, heads, here, parts, buf, lx, back, qkind, stack, hold, uni, left,
      arrtab, lead}, c)

# a multiline string, about to trim one opening newline
def lex.multi(st: St, kind: QKind) -> St:
  St{bad, rows, heads, here, parts, buf, _lex, back, _q, stack, hold, uni, left, arrtab,
    lead} = st
  St{bad, rows, heads, here, parts, buf, LTrim{}, back, q.as.multi(kind), stack, hold,
    uni, left, arrtab, lead}

# a third quote starts a multiline string; two quotes are an empty string
def lex.q2.go(same: Bool, st: St, c: Char, kind: QKind) -> St:
  match same:
    case True{}:
      lex.multi(st, kind)
    case False{}:
      bare.hold(val.take(st, VStr{""}), c, True{})

# two quotes have been seen
def lex.q2(st: St, +c: Char) -> St:
  St{bad, rows, heads, here, parts, buf, lx, back, +qkind, stack, hold, uni, left,
    arrtab, lead} = st
  lex.q2.go(Char.is_eq(c, q.char(qkind)),
    St{bad, rows, heads, here, parts, buf, lx, back, qkind, stack, hold, uni, left,
      arrtab, lead}, c, qkind)

# a line feed is trimmed; any other character is the first of the string
def lex.trim.nl(nl: Bool, st: St, c: Char) -> St:
  match nl:
    case True{}:
      st.lex(st, LStr{})
    case False{}:
      st.hold(st.lex(st, LStr{}), LStr{}, c)

# a carriage return may still have a line feed after it
def lex.trim.go(cr: Bool, nl: Bool, st: St, c: Char) -> St:
  match cr:
    case True{}:
      st.lex(st, LTrim2{})
    case False{}:
      lex.trim.nl(nl, st, c)

# trim one opening newline of a multiline string
def lex.trim(st: St, +c: Char) -> St:
  lex.trim.go(U32.is_eq(Char.to_u32(c), 13), ch.nl(c), st, c)

# the line feed of a CRLF opening newline
def lex.trim2.go(lf: Bool, st: St, c: Char) -> St:
  match lf:
    case True{}:
      st.lex(st, LStr{})
    case False{}:
      st.hold(st.lex(st, LStr{}), LStr{}, c)

# the line feed of a CRLF opening newline
def lex.trim2(st: St, +c: Char) -> St:
  lex.trim2.go(U32.is_eq(Char.to_u32(c), 10), st, c)

# a forbidden control, or one character of the string
def lex.str.char.go(bad: Bool, st: St, c: Char) -> St:
  match bad:
    case True{}:
      st.err(st, "invalid control")
    case False{}:
      st.push(st, c, LStr{})

# a raw character, rejected when it is a forbidden control
def lex.str.char(multi: Bool, st: St, +c: Char) -> St:
  lex.str.char.go(str.bad(Char.to_u32(c), multi), st, c)

# an escape, or a plain character
def lex.str.bs(bs: Bool, multi: Bool, st: St, c: Char, _kind: QKind) -> St:
  match bs:
    case True{}:
      st.lex(st, LEsc{})
    case False{}:
      lex.str.char(multi, st, c)

# a backslash starts an escape in a basic string
def lex.str.esc(basic: Bool, multi: Bool, st: St, +c: Char, kind: QKind) -> St:
  match basic:
    case True{}:
      lex.str.bs(Char.is_eq(c, '\\'), multi, st, c, kind)
    case False{}:
      lex.str.char(multi, st, c)

# count closing quotes of a multiline string
def lex.mq(st: St, n: U32) -> St:
  St{bad, rows, heads, here, parts, buf, _lex, back, qkind, stack, hold, _uni, _left,
    arrtab, lead} = st
  St{bad, rows, heads, here, parts, buf, LMq{}, back, qkind, stack, hold, 0, n, arrtab,
    lead}

# one quote closes a one-line string and may close a multiline string
def lex.str.quote(multi: Bool, st: St) -> St:
  match multi:
    case False{}:
      str.fin(st)
    case True{}:
      lex.mq(st, 1)

# a quote, an escape, or a character
def lex.str.go(quote: Bool, multi: Bool, basic: Bool, st: St, +c: Char, kind: QKind)
  -> St:
  match quote:
    case True{}:
      lex.str.quote(multi, st)
    case False{}:
      lex.str.esc(basic, multi, st, c, kind)

# inside a string
def lex.str(st: St, +c: Char) -> St:
  St{bad, rows, heads, here, parts, buf, lx, back, +qkind, stack, hold, uni, left,
    arrtab, lead} = st
  lex.str.go(Char.is_eq(c, q.char(qkind)), q.multi(qkind), q.basic(qkind),
    St{bad, rows, heads, here, parts, buf, lx, back, qkind, stack, hold, uni, left,
      arrtab, lead}, c, qkind)

# the second quote waits; the third closes
def lex.mq.one(one: Bool, st: St) -> St:
  match one:
    case True{}:
      lex.mq(st, 2)
    case False{}:
      str.fin(st)

# quotes that were not a closer return to the string, and the character is held
def lex.mq.back(st: St, c: Char, buf: List<&2, Char>) -> St:
  St{bad, rows, heads, here, parts, _buf, _lex, back, qkind, stack, _hold, uni, _left,
    arrtab, lead} = st
  St{bad, rows, heads, here, parts, buf, LStr{}, back, qkind, stack, HChar{c}, uni, 0,
    arrtab, lead}

# a quote continues the closer; anything else is content
def lex.mq.go(quote: Bool, one: Bool, st: St, c: Char, buf: List<&2, Char>, kind: QKind,
  _left: U32) -> St:
  match quote:
    case True{}:
      lex.mq.one(one, st)
    case False{}:
      lex.mq.back(st, c, mq.put(one, q.char(kind), buf))

# one character while closing a multiline string
def lex.mq.step(st: St, +c: Char) -> St:
  St{bad, rows, heads, here, parts, +buf, lx, back, +qkind, stack, hold, uni, +left,
    arrtab, lead} = st
  lex.mq.go(Char.is_eq(c, q.char(qkind)), U32.is_eq(left, 1),
    St{bad, rows, heads, here, parts, buf, lx, back, qkind, stack, hold, uni, left,
      arrtab, lead}, c, buf, qkind, left)

# one escaped character
def lex.esc(st: St, +c: Char) -> St:
  esc.use(esc.of(c), st, LStr{})

# remember that a newline was seen
def lex.fold.saw(st: St) -> St:
  St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, _left,
    arrtab, lead} = st
  St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, 1, arrtab,
    lead}

# a character before the newline is rejected
def lex.fold.end.go(saw: Bool, st: St, c: Char) -> St:
  match saw:
    case True{}:
      st.hold(st.lex(st, LStr{}), LStr{}, c)
    case False{}:
      st.err(st, "invalid escape")

# the next character ends the fold only after a newline
def lex.fold.end(st: St, c: Char) -> St:
  St{bad, rows, heads, here, parts, buf, lx, back, qkind, stack, hold, uni, +left,
    arrtab, lead} = st
  lex.fold.end.go(U32.is_eq(left, 1),
    St{bad, rows, heads, here, parts, buf, lx, back, qkind, stack, hold, uni, left,
      arrtab, lead}, c)

# a newline has been seen, so later whitespace may still be skipped
def lex.fold.nl(nl: Bool, st: St, c: Char) -> St:
  match nl:
    case True{}:
      lex.fold.saw(st)
    case False{}:
      lex.fold.end(st, c)

# more whitespace, or the next character of the string
def lex.fold.go(sp: Bool, nl: Bool, st: St, c: Char) -> St:
  match sp:
    case True{}:
      st
    case False{}:
      lex.fold.nl(nl, st, c)

# whitespace after a line-ending backslash
def lex.fold(st: St, +c: Char) -> St:
  lex.fold.go(ch.sp(c), ch.nl(c), st, c)

# keep the space only when the buffer is a date; otherwise it ends the token
def lex.bare.date.go(date: Bool, st: St, c: Char) -> St:
  match date:
    case True{}:
      st.lex(st, LDate{})
    case False{}:
      bare.finish(st, c, False{})

# a date may continue after one space
def lex.bare.date(st: St, c: Char) -> St:
  St{bad, rows, heads, here, parts, +buf, lx, back, qkind, stack, hold, uni, left,
    arrtab, lead} = st
  lex.bare.date.go(date.shaped(buf),
    St{bad, rows, heads, here, parts, buf, lx, back, qkind, stack, hold, uni, left,
      arrtab, lead}, c)

# a newline inside an inline table is held, and so is any other delimiter
def lex.bare.hold(skip: Bool, nl: Bool, inside: Bool) -> Bool:
  Bool.or(Bool.not(skip), Bool.and(nl, inside))

# a delimiter other than a date-space is held unless it is whitespace
def lex.bare.end(st: St, +c: Char) -> St:
  St{bad, rows, heads, here, parts, buf, lx, back, qkind, +stack, hold, uni, left,
    arrtab, lead} = st
  bare.finish(St{bad, rows, heads, here, parts, buf, lx, back, qkind, stack, hold,
    uni, left, arrtab, lead}, c, lex.bare.hold(ch.skip(c), ch.nl(c), inl.open(stack)))

# a space may be the space inside a datetime
def lex.bare.sp(sp: Bool, st: St, c: Char) -> St:
  match sp:
    case True{}:
      lex.bare.date(st, c)
    case False{}:
      lex.bare.end(st, c)

# a delimiter ends the token
def lex.bare.go(delim: Bool, sp: Bool, st: St, c: Char) -> St:
  match delim:
    case False{}:
      st.push(st, c, LBare{})
    case True{}:
      lex.bare.sp(sp, st, c)

# a bare value
def lex.bare(st: St, +c: Char) -> St:
  lex.bare.go(ch.delim(c), ch.sp(c), st, c)

# the space and the digit belong to the datetime
def lex.date.digit(st: St, c: Char) -> St:
  St{bad, rows, heads, here, parts, buf, _lex, back, qkind, stack, hold, uni, left,
    arrtab, lead} = st
  St{bad, rows, heads, here, parts, c <> (' ' <> buf), LBare{}, back, qkind, stack, hold,
    uni, left, arrtab, lead}

# the character after the space of a possible datetime
def lex.date.go(digit: Bool, st: St, c: Char) -> St:
  match digit:
    case True{}:
      lex.date.digit(st, c)
    case False{}:
      bare.finish(st, c, True{})

# the character after the space of a possible datetime
def lex.date(st: St, +c: Char) -> St:
  lex.date.go(Char.is_digit(c), st, c)

# the newline is read again in the state that was waiting
def lex.com.nl(st: St, c: Char) -> St:
  St{bad, rows, heads, here, parts, buf, _lex, +back, qkind, stack, _hold, uni, left,
    arrtab, lead} = st
  St{bad, rows, heads, here, parts, buf, back, back, qkind, stack, HChar{c}, uni, left,
    arrtab, lead}

# a comment runs to the end of the line
def lex.com.go(nl: Bool, st: St, c: Char) -> St:
  match nl:
    case False{}:
      st
    case True{}:
      lex.com.nl(st, c)

# a comment runs to the end of the line
def lex.com(st: St, +c: Char) -> St:
  lex.com.go(ch.nl(c), st, c)

# the header is an array of tables
def lex.head.arr(st: St) -> St:
  St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, _arr,
    lead} = st
  St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left,
    True{}, lead}

# one extra bracket
def lex.head.br2(once: Bool, st: St) -> St:
  match once:
    case False{}:
      st.err(st, "invalid header")
    case True{}:
      lex.head.arr(st)

# the second bracket is only legal at the start
def lex.head.br.go(fresh: Bool, once: Bool, st: St) -> St:
  match fresh:
    case False{}:
      st.err(st, "invalid header")
    case True{}:
      lex.head.br2(once, st)

# [[ opens an array of tables when the key has not started
def lex.head.br(st: St) -> St:
  St{bad, rows, heads, here, +parts, +buf, lx, back, qkind, stack, hold, uni, left,
    +arrtab, lead} = st
  lex.head.br.go(Bool.and(List.is_empty(&2, String, parts),
    List.is_empty(&2, Char, buf)), Bool.not(arrtab),
    St{bad, rows, heads, here, parts, buf, lx, back, qkind, stack, hold, uni, left,
      arrtab, lead})

# between segments a dot is required
def lex.head.ch.go(gap: Bool, st: St, c: Char) -> St:
  match gap:
    case True{}:
      st.err(st, "invalid header")
    case False{}:
      st.push(st, c, LHead{})

# a bare character continues the segment, or starts one at the beginning
def lex.head.ch(st: St, c: Char) -> St:
  St{bad, rows, heads, here, +parts, +buf, lx, back, qkind, stack, hold, uni, left,
    arrtab, lead} = st
  lex.head.ch.go(Bool.and(Bool.not(List.is_empty(&2, String, parts)),
    List.is_empty(&2, Char, buf)),
    St{bad, rows, heads, here, parts, buf, lx, back, qkind, stack, hold, uni, left,
      arrtab, lead}, c)

# an empty buffer was already between segments
def lex.head.gap.go(empty: Bool, st: St) -> St:
  match empty:
    case True{}:
      st
    case False{}:
      seg.push(st, LHeadGap{})

# whitespace ends a segment when one is open
def lex.head.gap(st: St) -> St:
  St{bad, rows, heads, here, parts, +buf, lx, back, qkind, stack, hold, uni, left,
    arrtab, lead} = st
  lex.head.gap.go(List.is_empty(&2, Char, buf),
    St{bad, rows, heads, here, parts, buf, lx, back, qkind, stack, hold, uni, left,
      arrtab, lead})

# a dot with no segment is rejected
def lex.head.dot3(empty: Bool, st: St) -> St:
  match empty:
    case True{}:
      st.err(st, "empty key")
    case False{}:
      seg.push(st, LHeadDot{})

# a dot ends the open segment
def lex.head.dot2(st: St) -> St:
  St{bad, rows, heads, here, parts, +buf, lx, back, qkind, stack, hold, uni, left,
    arrtab, lead} = st
  lex.head.dot3(List.is_empty(&2, Char, buf),
    St{bad, rows, heads, here, parts, buf, lx, back, qkind, stack, hold, uni, left,
      arrtab, lead})

# an array of tables still needs one ]
def lex.head.close2(arr: Bool, st: St) -> St:
  match arr:
    case True{}:
      st.lex(st, LHeadR{})
    case False{}:
      head.fin(st)

# push the last segment when the buffer holds one
def lex.head.close.go(empty: Bool, arr: Bool, st: St) -> St:
  match empty:
    case True{}:
      lex.head.close2(arr, st)
    case False{}:
      lex.head.close2(arr, seg.push(st, LHead{}))

# ] closes, or waits for the second ] of an array of tables
def lex.head.close(st: St) -> St:
  St{bad, rows, heads, here, parts, +buf, lx, back, qkind, stack, hold, uni, left,
    +arrtab, lead} = st
  lex.head.close.go(List.is_empty(&2, Char, buf), arrtab,
    St{bad, rows, heads, here, parts, buf, lx, back, qkind, stack, hold, uni, left,
      arrtab, lead})

# a comment in a header
def lex.head.hash(hash: Bool, st: St) -> St:
  match hash:
    case True{}:
      com.enter(st, LHead{})
    case False{}:
      st.err(st, "invalid header")

# a literal header segment or a comment
def lex.head.lit(lit: Bool, hash: Bool, st: St) -> St:
  match lit:
    case True{}:
      lex.qkey(st, QLit{}, LHeadQ{})
    case False{}:
      lex.head.hash(hash, st)

# a quoted header segment or a comment
def lex.head.q(q: Bool, lit: Bool, hash: Bool, st: St, _c: Char) -> St:
  match q:
    case True{}:
      lex.qkey(st, QBasic{}, LHeadQ{})
    case False{}:
      lex.head.lit(lit, hash, st)

# the closing bracket, a quoted key, or a comment
def lex.head.end(end: Bool, q: Bool, lit: Bool, hash: Bool, st: St, c: Char) -> St:
  match end:
    case True{}:
      lex.head.close(st)
    case False{}:
      lex.head.q(q, lit, hash, st, c)

# a dot, the end, or a quoted segment
def lex.head.dot(dot: Bool, end: Bool, q: Bool, lit: Bool, hash: Bool, st: St, c: Char)
  -> St:
  match dot:
    case True{}:
      lex.head.dot2(st)
    case False{}:
      lex.head.end(end, q, lit, hash, st, c)

# whitespace, a dot, or the closing bracket
def lex.head.sp(sp: Bool, dot: Bool, end: Bool, q: Bool, lit: Bool, hash: Bool, st: St,
  c: Char) -> St:
  match sp:
    case True{}:
      lex.head.gap(st)
    case False{}:
      lex.head.dot(dot, end, q, lit, hash, st, c)

# a bare character, whitespace, a dot, or the end
def lex.head.bare(bare: Bool, sp: Bool, dot: Bool, end: Bool, q: Bool, lit: Bool,
  hash: Bool, st: St, c: Char) -> St:
  match bare:
    case True{}:
      lex.head.ch(st, c)
    case False{}:
      lex.head.sp(sp, dot, end, q, lit, hash, st, c)

# a second bracket, a key character, or whitespace
def lex.head.go(br: Bool, bare: Bool, sp: Bool, dot: Bool, end: Bool, q: Bool,
  lit: Bool, hash: Bool, st: St, c: Char) -> St:
  match br:
    case True{}:
      lex.head.br(st)
    case False{}:
      lex.head.bare(bare, sp, dot, end, q, lit, hash, st, c)

# inside a header
def lex.head(st: St, +c: Char) -> St:
  lex.head.go(Char.is_eq(c, '['), bare.at(c), ch.sp(c), Char.is_eq(c, '.'),
    Char.is_eq(c, ']'), Char.is_eq(c, '"'), Char.is_eq(c, '\''), Char.is_eq(c, '#'),
    st, c)

# the end, or a comment
def lex.hgap.end(end: Bool, hash: Bool, st: St) -> St:
  match end:
    case True{}:
      lex.head.close(st)
    case False{}:
      lex.head.hash(hash, st)

# a dot starts the next segment
def lex.hgap.dot(dot: Bool, end: Bool, hash: Bool, st: St) -> St:
  match dot:
    case True{}:
      st.lex(st, LHeadDot{})
    case False{}:
      lex.hgap.end(end, hash, st)

# whitespace, a dot, or the end
def lex.hgap(sp: Bool, dot: Bool, end: Bool, hash: Bool, st: St, _c: Char) -> St:
  match sp:
    case True{}:
      st
    case False{}:
      lex.hgap.dot(dot, end, hash, st)

# between header segments
def lex.head.gap.step(st: St, +c: Char) -> St:
  lex.hgap(ch.sp(c), Char.is_eq(c, '.'), Char.is_eq(c, ']'), Char.is_eq(c, '#'), st, c)

# a literal segment, or a rejected character
def lex.hdot.lit(lit: Bool, st: St, _c: Char) -> St:
  match lit:
    case True{}:
      lex.qkey(st, QLit{}, LHeadQ{})
    case False{}:
      st.err(st, "invalid header")

# a quoted segment
def lex.hdot.q(q: Bool, lit: Bool, st: St, c: Char) -> St:
  match q:
    case True{}:
      lex.qkey(st, QBasic{}, LHeadQ{})
    case False{}:
      lex.hdot.lit(lit, st, c)

# a bare segment or a quoted one
def lex.hdot.bare(bare: Bool, q: Bool, lit: Bool, st: St, c: Char) -> St:
  match bare:
    case True{}:
      st.push(st, c, LHead{})
    case False{}:
      lex.hdot.q(q, lit, st, c)

# whitespace or the next segment
def lex.hdot(sp: Bool, bare: Bool, q: Bool, lit: Bool, st: St, c: Char) -> St:
  match sp:
    case True{}:
      st
    case False{}:
      lex.hdot.bare(bare, q, lit, st, c)

# after a dot, a segment must start
def lex.head.dot.step(st: St, +c: Char) -> St:
  lex.hdot(ch.sp(c), bare.at(c), Char.is_eq(c, '"'), Char.is_eq(c, '\''), st, c)

# a forbidden control, or one character of the key
def lex.kq.char.go(bad: Bool, st: St, c: Char, stay: Lex) -> St:
  match bad:
    case True{}:
      st.err(st, "invalid control")
    case False{}:
      st.push(st, c, stay)

# one character of a quoted key
def lex.kq.char(st: St, +c: Char, stay: Lex) -> St:
  lex.kq.char.go(str.bad(Char.to_u32(c), False{}), st, c, stay)

# a newline in a key is rejected
def lex.kq.nl(nl: Bool, st: St, +c: Char, stay: Lex) -> St:
  match nl:
    case True{}:
      st.err(st, "newline in key")
    case False{}:
      lex.kq.char(st, c, stay)

# the escape state for a quoted key
def lex.esc.lex(stay: Lex) -> Lex:
  match stay:
    case LHeadQ{}:
      LHeadE{}
    case _:
      LKeyE{}

# the escape returns to the quoted key
def lex.kesc(st: St, +stay: Lex) -> St:
  St{bad, rows, heads, here, parts, buf, _lex, _b, qkind, stack, hold, uni, left, arrtab,
    lead} = st
  St{bad, rows, heads, here, parts, buf, lex.esc.lex(stay), stay, qkind, stack, hold,
    uni, left, arrtab, lead}

# only a basic key treats the backslash as an escape
def lex.kq.esc(basic: Bool, st: St, stay: Lex) -> St:
  match basic:
    case True{}:
      lex.kesc(st, stay)
    case False{}:
      st.push(st, '\\', stay)

# an escape in a basic key
def lex.kq.bs(bs: Bool, basic: Bool, nl: Bool, st: St, c: Char, stay: Lex) -> St:
  match bs:
    case True{}:
      lex.kq.esc(basic, st, stay)
    case False{}:
      lex.kq.nl(nl, st, c, stay)

# the closer, an escape, or a character
def lex.kq.go(quote: Bool, bs: Bool, basic: Bool, nl: Bool, st: St, c: Char, back: Lex,
  stay: Lex) -> St:
  match quote:
    case True{}:
      lex.key.end(st, back)
    case False{}:
      lex.kq.bs(bs, basic, nl, st, c, stay)

# a quoted key segment. back is the state after the closer; stay is this quote
def lex.kq(st: St, +c: Char, back: Lex, stay: Lex) -> St:
  St{bad, rows, heads, here, parts, buf, lex, b, +qkind, stack, hold, uni, left, arrtab,
    lead} = st
  lex.kq.go(Char.is_eq(c, q.char(qkind)), Char.is_eq(c, '\\'), q.basic(qkind), ch.nl(c),
    St{bad, rows, heads, here, parts, buf, lex, b, qkind, stack, hold, uni, left, arrtab,
      lead}, c, back, stay)

# the second ] of an array of tables
def lex.head.r.go(end: Bool, st: St) -> St:
  match end:
    case True{}:
      head.fin(st)
    case False{}:
      st.err(st, "invalid header")

# the second ] of an array of tables
def lex.head.r(st: St, +c: Char) -> St:
  lex.head.r.go(Char.is_eq(c, ']'), st)

# ] closes; anything else is a value
def lex.arr.end(end: Bool, st: St, c: Char) -> St:
  match end:
    case True{}:
      arr.close(st)
    case False{}:
      st.hold(st.lex(st, LVal{}), LVal{}, c)

# a comment, the end, or a value
def lex.arr.hash(hash: Bool, end: Bool, st: St, c: Char) -> St:
  match hash:
    case True{}:
      com.enter(st, LArr{})
    case False{}:
      lex.arr.end(end, st, c)

# a newline is whitespace in an array
def lex.arr.nl(nl: Bool, hash: Bool, end: Bool, st: St, c: Char) -> St:
  match nl:
    case True{}:
      st
    case False{}:
      lex.arr.hash(hash, end, st, c)

# whitespace, a comment, the end, or a value
def lex.arr.go(sp: Bool, nl: Bool, hash: Bool, end: Bool, st: St, c: Char) -> St:
  match sp:
    case True{}:
      st
    case False{}:
      lex.arr.nl(nl, hash, end, st, c)

# an array waits for a value or ]
def lex.arr(st: St, +c: Char) -> St:
  lex.arr.go(ch.sp(c), ch.nl(c), Char.is_eq(c, '#'), Char.is_eq(c, ']'), st, c)

# ] closes the array
def lex.arrc.end(end: Bool, st: St) -> St:
  match end:
    case True{}:
      arr.close(st)
    case False{}:
      st.err(st, "invalid array")

# a comma waits for another value
def lex.arrc.comma(comma: Bool, end: Bool, st: St) -> St:
  match comma:
    case True{}:
      st.lex(st, LArr{})
    case False{}:
      lex.arrc.end(end, st)

# a comment, a comma, or the end
def lex.arrc.hash(hash: Bool, comma: Bool, end: Bool, st: St, _c: Char) -> St:
  match hash:
    case True{}:
      com.enter(st, LArrC{})
    case False{}:
      lex.arrc.comma(comma, end, st)

# a newline is whitespace
def lex.arrc.nl(nl: Bool, hash: Bool, comma: Bool, end: Bool, st: St, c: Char) -> St:
  match nl:
    case True{}:
      st
    case False{}:
      lex.arrc.hash(hash, comma, end, st, c)

# whitespace, a comment, a comma, or the end
def lex.arrc.go(sp: Bool, nl: Bool, hash: Bool, comma: Bool, end: Bool, st: St, c: Char)
  -> St:
  match sp:
    case True{}:
      st
    case False{}:
      lex.arrc.nl(nl, hash, comma, end, st, c)

# after an array value: a comma, ], or whitespace
def lex.arrc(st: St, +c: Char) -> St:
  lex.arrc.go(ch.sp(c), ch.nl(c), Char.is_eq(c, '#'), Char.is_eq(c, ','),
    Char.is_eq(c, ']'), st, c)

# a new key starts with an empty segment list
def lex.key.clear(st: St) -> St:
  St{bad, rows, heads, here, _parts, _buf, _lex, back, qkind, stack, hold, uni, left,
    arrtab, lead} = st
  St{bad, rows, heads, here, [], [], LKey{}, back, qkind, stack, hold, uni, left,
    arrtab, lead}

# a bare character opens the key
def lex.key.bare(ok: Bool, st: St, c: Char) -> St:
  match ok:
    case True{}:
      st.push(st, c, LKey{})
    case False{}:
      st.err(st, "invalid key")

# a literal quote or a bare character opens the key
def lex.key.lit(lit: Bool, st: St, +c: Char) -> St:
  match lit:
    case True{}:
      lex.qkey(st, QLit{}, LKeyQ{})
    case False{}:
      lex.key.bare(bare.at(c), st, c)

# a quote or a bare character opens the key
def lex.key.q(q: Bool, st: St, +c: Char) -> St:
  match q:
    case True{}:
      lex.qkey(st, QBasic{}, LKeyQ{})
    case False{}:
      lex.key.lit(Char.is_eq(c, '\''), st, c)

# the first character of a key inside an inline table
def lex.key.start(st: St, +c: Char) -> St:
  lex.key.q(Char.is_eq(c, '"'), lex.key.clear(st), c)

# a newline is rejected; anything else is a key
def lex.inl.nl(nl: Bool, st: St, c: Char) -> St:
  match nl:
    case True{}:
      st.err(st, "newline in inline table")
    case False{}:
      lex.key.start(st, c)

# } closes an empty inline table
def lex.inl.end(end: Bool, nl: Bool, st: St, c: Char) -> St:
  match end:
    case True{}:
      inl.close(st)
    case False{}:
      lex.inl.nl(nl, st, c)

# a comment, the end, or a key
def lex.inl.hash(hash: Bool, end: Bool, nl: Bool, st: St, c: Char) -> St:
  match hash:
    case True{}:
      com.enter(st, LInl{})
    case False{}:
      lex.inl.end(end, nl, st, c)

# whitespace, a comment, the end, or a key
def lex.inl.go(sp: Bool, hash: Bool, end: Bool, nl: Bool, st: St, c: Char) -> St:
  match sp:
    case True{}:
      st
    case False{}:
      lex.inl.hash(hash, end, nl, st, c)

# an inline table waits for a key or }
def lex.inl(st: St, +c: Char) -> St:
  lex.inl.go(ch.sp(c), Char.is_eq(c, '#'), Char.is_eq(c, '}'), ch.nl(c), st, c)

# a comment or a key
def lex.inlk.hash(hash: Bool, nl: Bool, st: St, c: Char) -> St:
  match hash:
    case True{}:
      com.enter(st, LInlK{})
    case False{}:
      lex.inl.nl(nl, st, c)

# whitespace or a key
def lex.inlk.go(sp: Bool, hash: Bool, nl: Bool, st: St, c: Char) -> St:
  match sp:
    case True{}:
      st
    case False{}:
      lex.inlk.hash(hash, nl, st, c)

# after a comma, a key is required
def lex.inlk(st: St, +c: Char) -> St:
  lex.inlk.go(ch.sp(c), Char.is_eq(c, '#'), ch.nl(c), st, c)

# a newline is rejected
def lex.inlc.nl(nl: Bool, st: St) -> St:
  match nl:
    case True{}:
      st.err(st, "newline in inline table")
    case False{}:
      st.err(st, "invalid inline table")

# } closes the inline table
def lex.inlc.end(end: Bool, nl: Bool, st: St, _c: Char) -> St:
  match end:
    case True{}:
      inl.close(st)
    case False{}:
      lex.inlc.nl(nl, st)

# a comma requires another key
def lex.inlc.comma(comma: Bool, end: Bool, nl: Bool, st: St, c: Char) -> St:
  match comma:
    case True{}:
      st.lex(st, LInlK{})
    case False{}:
      lex.inlc.end(end, nl, st, c)

# a comment, a comma, or the end
def lex.inlc.hash(hash: Bool, comma: Bool, end: Bool, nl: Bool, st: St, c: Char) -> St:
  match hash:
    case True{}:
      com.enter(st, LInlC{})
    case False{}:
      lex.inlc.comma(comma, end, nl, st, c)

# whitespace, a comment, a comma, or the end
def lex.inlc.go(sp: Bool, hash: Bool, comma: Bool, end: Bool, nl: Bool, st: St, c: Char)
  -> St:
  match sp:
    case True{}:
      st
    case False{}:
      lex.inlc.hash(hash, comma, end, nl, st, c)

# after an inline value: a comma or }
def lex.inlc(st: St, +c: Char) -> St:
  lex.inlc.go(ch.sp(c), Char.is_eq(c, '#'), Char.is_eq(c, ','), Char.is_eq(c, '}'),
    ch.nl(c), st, c)

# the rest of a failed document is ignored
def lex.sink(st: St, _c: Char) -> St:
  st

# a quoted header segment
def lex.hq(st: St, +c: Char) -> St:
  lex.kq(st, c, LHeadGap{}, LHeadQ{})

# one character, dispatched on the lex state
def read.on(lex: Lex, st: St, c: Char) -> St:
  match lex:
    case LTop{}:
      lex.top(st, c)
    case LKey{}:
      lex.key(st, c)
    case LAfter{}:
      lex.after(st, c)
    case LKeyQ{}:
      lex.kq(st, c, LAfter{}, LKeyQ{})
    case LKeyE{}:
      esc.use(esc.of(c), st, LKeyQ{})
    case LKeyU{}:
      uni.step(st, c, LKeyQ{})
    case LVal{}:
      lex.val(st, c)
    case LQ{}:
      lex.q(st, c)
    case LQ2{}:
      lex.q2(st, c)
    case LStr{}:
      lex.str(st, c)
    case LEsc{}:
      lex.esc(st, c)
    case LUni{}:
      uni.step(st, c, LStr{})
    case LFold{}:
      lex.fold(st, c)
    case LMq{}:
      lex.mq.step(st, c)
    case LTrim{}:
      lex.trim(st, c)
    case LTrim2{}:
      lex.trim2(st, c)
    case LBare{}:
      lex.bare(st, c)
    case LDate{}:
      lex.date(st, c)
    case LCom{}:
      lex.com(st, c)
    case LHead{}:
      lex.head(st, c)
    case LHeadGap{}:
      lex.head.gap.step(st, c)
    case LHeadDot{}:
      lex.head.dot.step(st, c)
    case LHeadQ{}:
      lex.hq(st, c)
    case LHeadE{}:
      esc.use(esc.of(c), st, LHeadQ{})
    case LHeadU{}:
      uni.step(st, c, LHeadQ{})
    case LHeadR{}:
      lex.head.r(st, c)
    case LArr{}:
      lex.arr(st, c)
    case LArrC{}:
      lex.arrc(st, c)
    case LInl{}:
      lex.inl(st, c)
    case LInlK{}:
      lex.inlk(st, c)
    case LInlC{}:
      lex.inlc(st, c)
    case LSink{}:
      lex.sink(st, c)

# read the lex state and step
def read.on.st(st: St, c: Char) -> St:
  St{bad, rows, heads, here, parts, buf, +lex, back, qkind, stack, hold, uni, left,
    arrtab, lead} = st
  read.on(lex, St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni,
    left, arrtab, lead}, c)

# one character, after a leading mark has been decided
def read.step.bom(bom: Bool, st: St, c: Char) -> St:
  match bom:
    case True{}:
      st
    case False{}:
      read.on.st(st, c)

# the first character may be a byte-order mark
def read.step.lead(lead: Bool, st: St, +c: Char) -> St:
  match lead:
    case False{}:
      read.on.st(st, c)
    case True{}:
      read.step.bom(U32.is_eq(Char.to_u32(c), 65279), st, c)

# one character of the document
def read.step(st: St, +c: Char) -> St:
  St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left,
    arrtab, +lead} = st
  read.step.lead(lead, St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack,
    hold, uni, left, arrtab, False{}}, c)

# a held character is read once
def read.once.hold(hold: Hold, st: St) -> St:
  match hold:
    case HNone{}:
      st
    case HChar{c}:
      read.step(st, c)

# a held character is read once
def read.once2(st: St) -> St:
  St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left,
    arrtab, lead} = st
  read.once.hold(hold, St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack,
    HNone{}, uni, left, arrtab, lead})

# one new character, then a held character if the step asked for one
def read.once(st: St, c: Char) -> St:
  read.once2(read.step(st, c))

# a bare token still open at the end is closed
def read.fin.lex(lex: Lex, st: St) -> St:
  match lex:
    case LBare{}:
      bare.finish(st, ' ', False{})
    case LDate{}:
      bare.finish(st, ' ', False{})
    case _:
      st

# a bare token still open at the end is closed
def read.fin.close(st: St) -> St:
  St{bad, rows, heads, here, parts, buf, +lex, back, qkind, stack, hold, uni, left,
    arrtab, lead} = st
  read.fin.lex(lex, St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold,
    uni, left, arrtab, lead})

# an open frame at the end is an error
def read.fin.stack(stack: List<&2, Ctx>, bad: String, rows: List<&2, Val>) -> Doc:
  match stack:
    case []:
      Doc{bad, rows}
    case _ <> _:
      Doc{err.first(bad, "unclosed"), rows}

# the document from a finished state
def read.fin.doc(st: St) -> Doc:
  St{bad, rows, _heads, _here, _parts, _buf, _lex, _back, _q, stack, _hold, _uni, _left,
    _arr, _lead} = st
  read.fin.stack(stack, bad, rows)

# any other state is unfinished
def read.fin.bad(st: St) -> Doc:
  St{bad, rows, _heads, _here, _parts, _buf, _lex, _back, _q, _stack, _hold, _uni,
    _left, _arr, _lead} = st
  Doc{err.first(bad, "unclosed"), rows}

# the states that may end a document
def read.fin.ok(lex: Lex, st: St) -> Doc:
  match lex:
    case LTop{}:
      read.fin.doc(st)
    case LCom{}:
      read.fin.doc(st)
    case LSink{}:
      read.fin.doc(st)
    case _:
      read.fin.bad(st)

# the document once the last token has been closed
def read.fin2(st: St) -> Doc:
  St{bad, rows, heads, here, parts, buf, +lex, back, qkind, stack, hold, uni, left,
    arrtab, lead} = st
  read.fin.ok(lex, St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold,
    uni, left, arrtab, lead})

# the document at the end of the text
def read.fin(st: St) -> Doc:
  read.fin2(read.fin.close(st))

# one character at a time
def doc.read(cs: List<&2, Char>, st: St) -> Doc:
  match cs:
    case []:
      read.fin(read.once2(st))
    case +h <> t:
      doc.read(t, read.once(read.once2(st), h))

# a scanner at the start of a document
def st.start() -> St:
  St{"", [], [], [], [], [], LTop{}, LTop{}, QBasic{}, [], HNone{}, 0, 0, False{},
    True{}}

# true or false
def render.bool(bit: Bool) -> String:
  match bit:
    case True{}:
      "true"
    case False{}:
      "false"

# a scalar value
def render.atom(v: Val) -> String:
  match v:
    case VStr{text}:
      key.basic(text)
    case VInt{sign, digits}:
      sign.text(sign) ++ digits
    case VFlo{sign, text}:
      sign.text(sign) ++ text
    case VBool{bit}:
      render.bool(bit)
    case VWhen{w}:
      when.text(w)
    case _:
      ""

# a separator that is omitted after the last item
def render.suf.last(last: Bool, gap: String) -> String:
  match last:
    case True{}:
      ""
    case False{}:
      gap

# a separator. trail keeps the separator after the last item
def render.suf(+gap: String, trail: Bool, last: Bool) -> String:
  match trail:
    case True{}:
      gap
    case False{}:
      render.suf.last(last, gap)

# the values of a table, an array, or an inline table
def render.go(vs: List<&2, Val>, +gap: String, +trail: Bool) -> String:
  match vs:
    case []:
      ""
    case VPair{_name, VHead{path, rows}} <> +t:
      "[" ++ path ++ "]\n" ++ render.go(rows, "\n", True{}) ++
        render.suf(gap, trail, List.is_empty(&2, Val, t)) ++ render.go(t, gap, trail)
    case VPair{_name, VAots{_path, elems}} <> +t:
      render.go(elems, "\n", True{}) ++
        render.suf(gap, trail, List.is_empty(&2, Val, t)) ++ render.go(t, gap, trail)
    case VAot{path, rows} <> +t:
      "[[" ++ path ++ "]]\n" ++ render.go(rows, "\n", True{}) ++
        render.suf(gap, trail, List.is_empty(&2, Val, t)) ++ render.go(t, gap, trail)
    case VPair{name, VArr{items}} <> +t:
      key(name) ++ " = [" ++ render.go(items, ", ", False{}) ++ "]" ++
        render.suf(gap, trail, List.is_empty(&2, Val, t)) ++ render.go(t, gap, trail)
    case VPair{name, VInl{rows}} <> +t:
      key(name) ++ " = {" ++ render.go(rows, ", ", False{}) ++ "}" ++
        render.suf(gap, trail, List.is_empty(&2, Val, t)) ++ render.go(t, gap, trail)
    case VPair{name, val} <> +t:
      key(name) ++ " = " ++ render.atom(val) ++
        render.suf(gap, trail, List.is_empty(&2, Val, t)) ++ render.go(t, gap, trail)
    case VArr{items} <> +t:
      "[" ++ render.go(items, ", ", False{}) ++ "]" ++
        render.suf(gap, trail, List.is_empty(&2, Val, t)) ++ render.go(t, gap, trail)
    case VInl{rows} <> +t:
      "{" ++ render.go(rows, ", ", False{}) ++ "}" ++
        render.suf(gap, trail, List.is_empty(&2, Val, t)) ++ render.go(t, gap, trail)
    case v <> +t:
      render.atom(v) ++ render.suf(gap, trail, List.is_empty(&2, Val, t)) ++
        render.go(t, gap, trail)

# a nested table rendering that this pass does not print
def render.skip(_path: String, _rows: List<&2, Val>, _tail: List<&2, Val>, _gap: String,
  _trail: Bool, nest: Unit -> String, rest: Unit -> String) -> String:
  _n = nest
  rest(Unit{})

# the rows are already closed over by the nested rendering
def render.use(_rows: List<&2, Val>, text: String) -> String:
  text

# a header already ends in a newline
def render.rest(_tail: List<&2, Val>, _gap: String, _trail: Bool, rest: Unit -> String)
  -> String:
  rest(Unit{})

# a table header. Direct keys are printed by the other pass
def render.head(tabs: Bool, path: String, rows: List<&2, Val>, tail: List<&2, Val>,
  gap: String, trail: Bool, nest: Unit -> String, rest: Unit -> String) -> String:
  match tabs:
    case False{}:
      render.skip(path, rows, tail, gap, trail, nest, rest)
    case True{}:
      "[" ++ path ++ "]\n" ++ render.use(rows, nest(Unit{})) ++
        render.rest(tail, gap, trail, rest)

# an array of tables. Its elements are headers
def render.aots(tabs: Bool, elems: List<&2, Val>, tail: List<&2, Val>, gap: String,
  trail: Bool, nest: Unit -> String, rest: Unit -> String) -> String:
  match tabs:
    case False{}:
      render.skip("", elems, tail, gap, trail, nest, rest)
    case True{}:
      render.use(elems, nest(Unit{})) ++ render.rest(tail, gap, trail, rest)

# one element of an array of tables
def render.aot(tabs: Bool, path: String, rows: List<&2, Val>, tail: List<&2, Val>,
  gap: String, trail: Bool, nest: Unit -> String, rest: Unit -> String) -> String:
  match tabs:
    case False{}:
      render.skip(path, rows, tail, gap, trail, nest, rest)
    case True{}:
      "[[" ++ path ++ "]]\n" ++ render.use(rows, nest(Unit{})) ++
        render.rest(tail, gap, trail, rest)

# a value left out of the table pass
def render.val.skip(_text: String, _tail: List<&2, Val>, _gap: String, _trail: Bool,
  rest: Unit -> String) -> String:
  rest(Unit{})

# a key, an array, or an inline table. The table pass leaves it
def render.val(tabs: Bool, text: String, tail: List<&2, Val>, gap: String, trail: Bool,
  rest: Unit -> String) -> String:
  match tabs:
    case True{}:
      render.val.skip(text, tail, gap, trail, rest)
    case False{}:
      text ++ render.suf(gap, trail, List.is_empty(&2, Val, tail)) ++ rest(Unit{})

# one pass: keys, or the tables that follow them
def render.pass(vs: List<&2, Val>, +gap: String, +trail: Bool, +tabs: Bool) -> String:
  match vs:
    case []:
      ""
    case VPair{_name, VHead{path, +rows}} <> +t:
      render.head(tabs, path, rows, t, gap, trail,
        _u => render.pass(rows, "\n", True{}, False{}) ++
          render.pass(rows, "\n", True{}, True{}),
        _u => render.pass(t, gap, trail, tabs))
    case VPair{_name, VAots{_path, +elems}} <> +t:
      render.aots(tabs, elems, t, gap, trail,
        _u => render.pass(elems, "\n", True{}, False{}) ++
          render.pass(elems, "\n", True{}, True{}),
        _u => render.pass(t, gap, trail, tabs))
    case VAot{path, +rows} <> +t:
      render.aot(tabs, path, rows, t, gap, trail,
        _u => render.pass(rows, "\n", True{}, False{}) ++
          render.pass(rows, "\n", True{}, True{}),
        _u => render.pass(t, gap, trail, tabs))
    case VPair{name, VArr{items}} <> +t:
      render.val(tabs, key(name) ++ " = [" ++ render.go(items, ", ", False{}) ++ "]",
        t, gap, trail, _u => render.pass(t, gap, trail, tabs))
    case VPair{name, VInl{rows}} <> +t:
      render.val(tabs, key(name) ++ " = {" ++ render.go(rows, ", ", False{}) ++ "}",
        t, gap, trail, _u => render.pass(t, gap, trail, tabs))
    case VPair{name, val} <> +t:
      render.val(tabs, key(name) ++ " = " ++ render.atom(val), t, gap, trail,
        _u => render.pass(t, gap, trail, tabs))
    case VArr{items} <> +t:
      render.val(tabs, "[" ++ render.go(items, ", ", False{}) ++ "]", t, gap, trail,
        _u => render.pass(t, gap, trail, tabs))
    case VInl{rows} <> +t:
      render.val(tabs, "{" ++ render.go(rows, ", ", False{}) ++ "}", t, gap, trail,
        _u => render.pass(t, gap, trail, tabs))
    case v <> +t:
      render.val(tabs, render.atom(v), t, gap, trail,
        _u => render.pass(t, gap, trail, tabs))

# keys first, then tables and arrays of tables
def render.both(+vs: List<&2, Val>, +gap: String, +trail: Bool) -> String:
  render.pass(vs, gap, trail, False{}) ++ render.pass(vs, gap, trail, True{})

# the text of a string value
def string(v: Val) -> String:
  match v:
    case VStr{text}:
      text
    case _:
      ""

# the digits of an integer value
def digits(v: Val) -> String:
  match v:
    case VInt{_sign, text}:
      text
    case _:
      ""

# the bit of a boolean value
def flag(v: Val) -> Bool:
  match v:
    case VBool{bit}:
      bit
    case _:
      False{}

# the rows of a table value
def at.rows(v: Val) -> List<&2, Val>:
  match v:
    case VHead{_path, rows}:
      rows
    case VInl{rows}:
      rows
    case VAot{_path, rows}:
      rows
    case _:
      []

# the rows of a hit, when it is a table
def at.rows_of(h: Hit) -> List<&2, Val>:
  match h:
    case Found{val}:
      at.rows(val)
    case Miss{}:
      []

# the rest of a path after the first key
def at.step(rest: List<&2, String>, hit: Hit) -> Hit:
  match rest:
    case []:
      hit
    case name <> t:
      at.step(t, get(at.rows_of(hit), name))

# the value at a dotted path
def at(rows: List<&2, Val>, path: List<&2, String>) -> Hit:
  match path:
    case []:
      Miss{}
    case name <> rest:
      at.step(rest, get(rows, name))

# the root table
def root(doc: Doc) -> List<&2, Val>:
  Doc{_bad, rows} = doc
  rows

# the first error, or "" when the document is well formed
def bad(doc: Doc) -> String:
  Doc{text, _rows} = doc
  text

# a string value
def str(text: String) -> Val:
  VStr{text}

# an integer value
def integer(sign: Sign, text: String) -> Val:
  VInt{sign, text}

# a float value
def float(sign: Sign, text: String) -> Val:
  VFlo{sign, text}

# a boolean value
def boolean(bit: Bool) -> Val:
  VBool{bit}

# an array value
def array(items: List<&2, Val>) -> Val:
  VArr{items}

# an inline table
def inline(rows: List<&2, Val>) -> Val:
  VInl{rows}

# a table
def table(path: String, rows: List<&2, Val>) -> Val:
  VHead{path, rows}

# a key and a value
def pair(name: String, val: Val) -> Val:
  VPair{name, val}

# a document written back as TOML
def render(doc: Doc) -> String:
  Doc{_bad, rows} = doc
  render.both(rows, "\n", True{})

# a document read from TOML text
def parse(text: String) -> Doc:
  doc.read(String.to_list(text), st.start())
