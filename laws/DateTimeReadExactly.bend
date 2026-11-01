# A datetime is read exactly when it matches one of toml.abnf's four date-time
# rules with RFC 3339's ranges (month 1 to 12, the day within the month in
# that year, hour 0 to 23, minute 0 to 59, second 0 to 60, offset hours 0 to
# 23 and minutes 0 to 59), and `render` writes it with `T` and `Z` in upper
# case, keeping the fraction's digits
#
# also rests on: laws/BareWordReadsOn.bend, laws/BareWordReadsOnInArray.bend,
# laws/BareWordRefused.bend, laws/BareWordRefusedInArray.bend,
# laws/WordRefusedInDocument.bend
import Base
import ../main.bend as T
import ./defs/AbnfGrammar.bend as D1
import ./defs/BareValueGrammar.bend as D2
import ./defs/DocumentSameness.bend as D3
import ./defs/GrammarDerivations.bend as D4

# a month's number, as a date writes it
def month.num(mm: D1.Month) -> U32:
  match mm:
    case D1.Jan{}:
      1
    case D1.Feb{}:
      2
    case D1.Mar{}:
      3
    case D1.Apr{}:
      4
    case D1.May{}:
      5
    case D1.Jun{}:
      6
    case D1.Jul{}:
      7
    case D1.Aug{}:
      8
    case D1.Sep{}:
      9
    case D1.Oct{}:
      10
    case D1.Nov{}:
      11
    case D1.Dec{}:
      12

# a datetime scan that holds no value
def when_refused(ww: T.WhenOut) -> Bool:
  match ww:
    case T.WSome{_when}:
      False{}
    case T.WFail{_why}:
      True{}
    case T.WSkip{}:
      True{}

# LAW: a date whose day is from 1 to the days of its month in its year is
# accepted: the rest of the token is read after it
law date_day_in_month:
  for +yy: U32
  for +mm: D1.Month
  for +dd: U32
  for rest: List<&2, Char>
  for e: {True{} == Bool.and(U32.is_ge(dd, 1), U32.is_le(dd, D1.days_in(yy, mm))) : Bool}
  {T.when.date.ok(yy, month.num(mm), dd, rest)
    == T.when.after.date(T.Date{yy, month.num(mm), dd}, rest) : T.WhenOut}

# LAW: a date whose day is 0 or past the days of its month in its year is
# refused, whatever follows it
law date_day_past_month:
  for +yy: U32
  for +mm: D1.Month
  for +dd: U32
  for rest: List<&2, Char>
  for e: {False{} == Bool.and(U32.is_ge(dd, 1), U32.is_le(dd, D1.days_in(yy, mm))) : Bool}
  {when_refused(T.when.date.ok(yy, month.num(mm), dd, rest)) == True{} : Bool}

# LAW: a well-formed datetime's text is classified as the datetime: render
# writes the year with four digits and every other field with two, with T and
# Z in upper case and the fraction's digits kept, and the scan reads each field
# back, for all four forms
law when_word:
  for +w: T.When
  for +h: {T.wf.when(w) == True{} : Bool}
  {T.word.val(String.to_list(T.render.atom(T.VWhen{w}))) == T.GotVal{T.VWhen{w}} : T.Got}

#
# Datetime words, exact in both directions (docs/rfc/eztoml-grammar-proofs.md,
# WP-T1). word.val gives a datetime exactly when the word matches one of
# toml.abnf's four date-time rules (abnf.date_time) with every field within
# RFC 3339's ranges (prose.date_time_in_range), and the datetime is the one
# the word denotes (g.val). The laws are over any list of characters, so they
# cover a lowercase t or z, a space between the date and the time (the scan
# keeps it in the word after a date-shaped buffer, the LDate state), a
# fraction of any length, Z or a numeric offset, and every word no rule
# matches. The lift over parse is WP-V's.

# a value compared with a datetime: the datetime it holds, or none
def t1.val_when(vv: T.Val, ww: T.When) -> Bool:
  match vv:
    case T.VWhen{when}:
      D3.when.eq(ww, when)
    case _:
      False{}

# a bare word's outcome compared with a datetime: true when the word reads as
# that datetime, and false when it reads as another value, another datetime
# or no value
def t1.got_when(gg: T.Got, ww: T.When) -> Bool:
  match gg:
    case T.GotVal{vv}:
      t1.val_when(vv, ww)
    case T.GotBad{_why}:
      False{}

# LAW: a bare word reads as a datetime exactly when it matches one of
# toml.abnf's four date-time rules (offset-date-time, local-date-time,
# local-date, local-time: T, t or a space between date and time, Z, z or a
# numeric offset, a fraction of any length) with every field within RFC
# 3339's ranges, and the datetime it reads as is the one the word denotes
law date_time_word:
  for +cs: List<&2, Char>
  for +w: T.When
  {t1.got_when(T.word.val(cs), w) == Bool.and(D1.g.ok.val(D4.GvDateTime{cs}, D1.RVal{}), D1.g.val(D4.GvDateTime{cs},
      T.VWhen{w}))
    : Bool}

# LAW: a bare word that matches a date-time rule within the ranges reads as
# the datetime it denotes
law date_time_word_read:
  for +cs: List<&2, Char>
  for +h: {D1.g.ok.val(D4.GvDateTime{cs}, D1.RVal{}) == True{} : Bool}
  {T.word.val(cs) == T.GotVal{T.VWhen{D1.g.dt.when(cs)}} : T.Got}

# LAW: render writes every well-formed datetime as a word that matches a
# date-time rule within the ranges and denotes that datetime
law date_time_render:
  for +w: T.When
  for +h: {T.wf.when(w) == True{} : Bool}
  {Bool.and(D1.g.ok.val(D4.GvDateTime{String.to_list(T.render.atom(T.VWhen{w}))}, D1.RVal{}),
    D1.g.val(D4.GvDateTime{String.to_list(T.render.atom(T.VWhen{w}))}, T.VWhen{w})) == True{} : Bool}

# LAW: and as a datetime: k = w parses to the datetime d exactly when w
# matches one of toml.abnf's four date-time rules (T, t or a space between
# the date and the time) within RFC 3339's ranges and denotes d
law date_time_parses_exactly:
  for +k: String
  for ek: {T.bare(k) == True{} : Bool}
  for +w: String
  for hw: {D2.bw.word(w) == True{} : Bool}
  for +d: T.When
  {t1.got_when(D2.bw.got(T.parse(D1.bw.kv(k, w)), k), d) == Bool.and(D1.g.ok.val(D4.GvDateTime{String.to_list(w)},
      D1.RVal{}),
    D1.g.val(D4.GvDateTime{String.to_list(w)}, T.VWhen{d})) : Bool}

# whether a character is a lowercase t, a lowercase z or a space: the
# separators toml.abnf allows in a datetime besides T and Z
def bw.lower(+cc: Char) -> Bool:
  Bool.or(Char.is_eq(cc, 't'), Bool.or(Char.is_eq(cc, 'z'), Char.is_eq(cc, ' ')))

# whether a text holds none of them
def bw.upper(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      True{}
    case +hh <> tt:
      Bool.and(Bool.not(bw.lower(hh)), bw.upper(tt))

# LAW: render writes every well-formed datetime with T and Z in upper case:
# its text holds no t, no z and no space, so of the separators the date-time
# rules allow (date_time_render) it uses T between the date and the time and
# Z for UTC
law date_time_render_upper:
  for +w: T.When
  for +h: {T.wf.when(w) == True{} : Bool}
  {bw.upper(String.to_list(T.render.atom(T.VWhen{w}))) == True{} : Bool}

# LAW: and every word a date-time rule matches, a space between the date and
# the time included, which the scan keeps after a date before a digit
law date_time_is_bare_word:
  for +w: String
  for h: {D1.abnf.date_time(String.to_list(w)) == True{} : Bool}
  {D2.bw.word(w) == True{} : Bool}

# LAW: a datetime word in a document: for every bare key k and every word w
# that matches one of toml.abnf's four date-time rules (T, t or a space between
# the date and the time) within RFC 3339's ranges and denotes v, k = w and a
# newline parse with no error to one pair named k holding v
law date_time_parses_as_denoted:
  for +k: String
  for ek: {T.bare(k) == True{} : Bool}
  for +w: String
  for +hw: {D1.g.ok.val(D4.GvDateTime{String.to_list(w)}, D1.RVal{}) == True{} : Bool}
  for +v: T.Val
  for +hv: {D1.g.val(D4.GvDateTime{String.to_list(w)}, v) == True{} : Bool}
  {T.parse(D1.bw.kv(k, w)) == T.Doc{"", [T.VPair{k, v}]} : T.Doc}

# LAW: a datetime word as an array's item: for every bare key k and every word
# w that matches one of toml.abnf's four date-time rules (T, t or a space
# between the date and the time) within RFC 3339's ranges and denotes v, k =
# [w] and a newline parse with no error to one pair named k holding an array of
# v
law date_time_parses_as_denoted_in_array:
  for +k: String
  for ek: {T.bare(k) == True{} : Bool}
  for +w: String
  for +hw: {D1.g.ok.val(D4.GvDateTime{String.to_list(w)}, D1.RVal{}) == True{} : Bool}
  for +v: T.Val
  for +hv: {D1.g.val(D4.GvDateTime{String.to_list(w)}, v) == True{} : Bool}
  {T.parse(D1.bw.kva(k, w)) == T.Doc{"", [T.VPair{k, T.VArr{[v]}}]} : T.Doc}

# LAW: a datetime word as an inline table's value: for every bare key k and
# every word w that matches one of toml.abnf's four date-time rules (T, t or a
# space between the date and the time) within RFC 3339's ranges and denotes v,
# k = {v = w} and a newline parse with no error to one pair named k holding an
# inline table whose pair v holds v
law date_time_parses_as_denoted_in_inline_table:
  for +k: String
  for ek: {T.bare(k) == True{} : Bool}
  for +w: String
  for +hw: {D1.g.ok.val(D4.GvDateTime{String.to_list(w)}, D1.RVal{}) == True{} : Bool}
  for +v: T.Val
  for +hv: {D1.g.val(D4.GvDateTime{String.to_list(w)}, v) == True{} : Bool}
  {T.parse(D1.bw.kvi(k, w)) == T.Doc{"", [T.VPair{k, T.VInl{[T.VPair{"v", v}]}}]} : T.Doc}
