# eztoml: the laws. Each law carries the SPEC.md row it proves, or proves part
# of, on its own comment line. PROOF.bend fills them; `bend PROOF.bend` is
# the gate.
import Base
import ./main.bend as T

# LAW: a pair at the head of a table's rows is what get finds for its name
# TOML-GET-1
law get_first:
  for +name: String
  for +v: T.Val
  for rest: List<&2, T.Val>
  {T.get(T.VPair{name, v} <> rest, name) == T.Found{v} : T.Hit}

# LAW: an empty key is not bare
# TOML-KEY-1
law bare_needs_a_char:
  for +s: String
  for e: {True{} == String.is_empty(s) : Bool}
  {T.bare(s) == False{} : Bool}

# LAW: a bare key is written as itself
# TOML-KEY-2
law key_is_bare_when_it_can:
  for +s: String
  for e: {True{} == T.bare(s) : Bool}
  {T.key(s) == s : String}

# LAW: a key that is not bare is written as a basic string
# TOML-KEY-2
law key_is_quoted_when_it_must:
  for +s: String
  for e: {False{} == T.bare(s) : Bool}
  {T.key(s) == T.key.basic(s) : String}

# LAW: string reads the text of an owned string value
# TOML-READ-1
law string_of:
  for text: String
  {T.string(T.VStr{text}) == text : String}

# The law side of TOML-KEY-1: toml.abnf (TOML v1.0.0) transcribed over each
# character's code point. Bend has no hex literals, so each bound is written
# in decimal with its hex beside it.

# ALPHA = %x41-5A / %x61-7A ; A-Z / a-z
# (%x41 is 65, %x5A is 90, %x61 is 97, %x7A is 122)
def abnf.alpha(+cp: U32) -> Bool:
  Bool.or(Bool.and(U32.is_ge(cp, 65), U32.is_le(cp, 90)),
    Bool.and(U32.is_ge(cp, 97), U32.is_le(cp, 122)))

# DIGIT = %x30-39 ; 0-9
# (%x30 is 48, %x39 is 57)
def abnf.digit(+cp: U32) -> Bool:
  Bool.and(U32.is_ge(cp, 48), U32.is_le(cp, 57))

# unquoted-key = 1*( ALPHA / DIGIT / %x2D / %x5F ) ; A-Z / a-z / 0-9 / - / _
# One character of the repetition, by its code point. (%x2D is 45, %x5F is 95)
def abnf.unquoted_key_char(cc: Char) -> Bool:
  match cc:
    case Chr{+cp}:
      Bool.or(abnf.alpha(cp), Bool.or(abnf.digit(cp),
        Bool.or(U32.is_eq(cp, 45), U32.is_eq(cp, 95))))

# every character of a string is one of the repetition's
def abnf.all_unquoted_key_chars(ss: String) -> Bool:
  match ss:
    case SNil{}:
      True{}
    case SCon{hh, tt}:
      Bool.and(abnf.unquoted_key_char(hh), abnf.all_unquoted_key_chars(tt))

# unquoted-key = 1*( ALPHA / DIGIT / %x2D / %x5F ): one or more of them
def abnf.unquoted_key(ss: String) -> Bool:
  match ss:
    case SNil{}:
      False{}
    case SCon{hh, tt}:
      Bool.and(abnf.unquoted_key_char(hh), abnf.all_unquoted_key_chars(tt))

# LAW: a key is bare exactly when it matches toml.abnf's unquoted-key
# TOML-KEY-1
law bare_is_unquoted_key:
  for +s: String
  {T.bare(s) == abnf.unquoted_key(s) : Bool}

# whether some pair in the rows has the name k
def has_pair(rows: List<&2, T.Val>, +kk: String) -> Bool:
  match rows:
    case []:
      False{}
    case T.VPair{nn, _vv} <> tt:
      Bool.or(String.eq(nn, kk), has_pair(tt, kk))
    case _ <> tt:
      has_pair(tt, kk)

# whether a value is a pair
def is_pair(vv: T.Val) -> Bool:
  match vv:
    case T.VPair{_nn, _vv}:
      True{}
    case _:
      False{}

# LAW: get passes over a pair of another name
# TOML-GET-1
law get_skips_other_name:
  for +n: String
  for v: T.Val
  for rest: List<&2, T.Val>
  for +k: String
  for e: {String.eq(n, k) == False{} : Bool}
  {T.get(T.VPair{n, v} <> rest, k) == T.get(rest, k) : T.Hit}

# LAW: get passes over a value that is not a pair
# TOML-GET-1
law get_skips_non_pair:
  for x: T.Val
  for rest: List<&2, T.Val>
  for +k: String
  for e: {is_pair(x) == False{} : Bool}
  {T.get(x <> rest, k) == T.get(rest, k) : T.Hit}

# LAW: get finds the value of the first pair named k, wherever it sits
# TOML-GET-1
law get_finds_first:
  for pre: List<&2, T.Val>
  for +k: String
  for v: T.Val
  for post: List<&2, T.Val>
  for +e: {has_pair(pre, k) == False{} : Bool}
  {T.get(List.append(&2, T.Val, pre, T.VPair{k, v} <> post), k)
    == T.Found{v} : T.Hit}

# LAW: get misses when no pair in the rows is named k
# TOML-GET-1
law get_misses:
  for rows: List<&2, T.Val>
  for +k: String
  for +e: {has_pair(rows, k) == False{} : Bool}
  {T.get(rows, k) == T.Miss{} : T.Hit}

# whether a value holds no rows for at to go on in. A table (VHead), an
# element of an array of tables (VAot) and an inline table (VInl) hold rows.
def holds_no_rows(vv: T.Val) -> Bool:
  match vv:
    case T.VHead{_pp, _rr}:
      False{}
    case T.VInl{_rr}:
      False{}
    case T.VAot{_pp, _rr}:
      False{}
    case _:
      True{}

# LAW: an empty path finds nothing
# TOML-GET-2
law at_empty:
  for rows: List<&2, T.Val>
  {T.at(rows, []) == T.Miss{} : T.Hit}

# LAW: a path of one key finds what get finds for it
# TOML-GET-2
law at_one:
  for rows: List<&2, T.Val>
  for +k: String
  {T.at(rows, [k]) == T.get(rows, k) : T.Hit}

# LAW: a longer path goes on in the rows of the table get finds
# TOML-GET-2
law at_table:
  for rows: List<&2, T.Val>
  for +k: String
  for path: String
  for sub: List<&2, T.Val>
  for +next: String
  for ks: List<&2, String>
  for e: {T.get(rows, k) == T.Found{T.VHead{path, sub}} : T.Hit}
  {T.at(rows, k <> next <> ks) == T.at(sub, next <> ks) : T.Hit}

# LAW: a longer path goes on in the rows of the inline table get finds
# TOML-GET-2
law at_inline:
  for rows: List<&2, T.Val>
  for +k: String
  for sub: List<&2, T.Val>
  for +next: String
  for ks: List<&2, String>
  for e: {T.get(rows, k) == T.Found{T.VInl{sub}} : T.Hit}
  {T.at(rows, k <> next <> ks) == T.at(sub, next <> ks) : T.Hit}

# LAW: a longer path goes on in the rows of the array-of-tables element get
# finds, which a hand-built document can hold as a pair's value
# TOML-GET-2
law at_aot:
  for rows: List<&2, T.Val>
  for +k: String
  for path: String
  for sub: List<&2, T.Val>
  for +next: String
  for ks: List<&2, String>
  for e: {T.get(rows, k) == T.Found{T.VAot{path, sub}} : T.Hit}
  {T.at(rows, k <> next <> ks) == T.at(sub, next <> ks) : T.Hit}

# LAW: a longer path misses when get misses its first key
# TOML-GET-2
law at_miss:
  for rows: List<&2, T.Val>
  for +k: String
  for next: String
  for ks: List<&2, String>
  for e: {T.get(rows, k) == T.Miss{} : T.Hit}
  {T.at(rows, k <> next <> ks) == T.Miss{} : T.Hit}

# LAW: a longer path misses when get finds a value with no rows: a string,
# a number, a bit, a datetime, an array, an array of tables or a pair
# TOML-GET-2
law at_leaf:
  for rows: List<&2, T.Val>
  for +k: String
  for v: T.Val
  for next: String
  for ks: List<&2, String>
  for e: {T.get(rows, k) == T.Found{v} : T.Hit}
  for f: {holds_no_rows(v) == True{} : Bool}
  {T.at(rows, k <> next <> ks) == T.Miss{} : T.Hit}

# whether a value is a string, owned or a span
def is_string(vv: T.Val) -> Bool:
  match vv:
    case T.VStr{_tt}:
      True{}
    case T.VSpan{_ss, _nn}:
      True{}
    case _:
      False{}

# whether a value is an integer
def is_int(vv: T.Val) -> Bool:
  match vv:
    case T.VInt{_ss, _dd}:
      True{}
    case _:
      False{}

# whether a value is a boolean
def is_bool(vv: T.Val) -> Bool:
  match vv:
    case T.VBool{_bb}:
      True{}
    case _:
      False{}

# LAW: string reads a span as the first n characters of its source
# TOML-READ-1
law string_of_span:
  for src: String
  for +n: U32
  {T.string(T.VSpan{src, n}) == String.take(src, U32.to_nat(n)) : String}

# LAW: string reads "" from every value that is not a string
# TOML-READ-1
law string_of_other:
  for v: T.Val
  for e: {is_string(v) == False{} : Bool}
  {T.string(v) == "" : String}

# LAW: digits reads the digits of an integer
# TOML-READ-1
law digits_of:
  for sign: T.Sign
  for text: String
  {T.digits(T.VInt{sign, text}) == text : String}

# LAW: digits reads "" from every value that is not an integer
# TOML-READ-1
law digits_of_other:
  for v: T.Val
  for e: {is_int(v) == False{} : Bool}
  {T.digits(v) == "" : String}

# LAW: flag reads the bit of a boolean
# TOML-READ-1
law flag_of:
  for bit: Bool
  {T.flag(T.VBool{bit}) == bit : Bool}

# LAW: flag reads false from every value that is not a boolean
# TOML-READ-1
law flag_of_other:
  for v: T.Val
  for e: {is_bool(v) == False{} : Bool}
  {T.flag(v) == False{} : Bool}

# The numeral scan (I6, R-I6). toml.abnf: `dec-int = [ minus / plus ]
# unsigned-dec-int`, `unsigned-dec-int = DIGIT / digit1-9 1*( DIGIT /
# underscore DIGIT )`, and `float-int-part = dec-int`: one sign at most, and
# no leading zero but a lone 0, so no `_` after it.

# the character a sign is written with
def mark(sg: T.Sign) -> Char:
  match sg:
    case T.Plus{}:
      '+'
    case T.Minus{}:
      '-'

# a scan result that holds no value
def refused(gg: T.Got) -> Bool:
  match gg:
    case T.GotVal{_val}:
      False{}
    case T.GotBad{_why}:
      True{}

# a sign character
def is_sign(+cc: Char) -> Bool:
  Bool.or(Char.is_eq(cc, '+'), Char.is_eq(cc, '-'))

# LAW: a numeral that starts with two signs is refused, whatever follows
# TOML-NUM-1
# TOML-NUM-2
law num_two_signs:
  for s1: T.Sign
  for s2: T.Sign
  for +rest: List<&2, Char>
  {refused(T.word.num(mark(s1) <> mark(s2) <> rest)) == True{} : Bool}

# LAW: a numeral that starts with a zero and an underscore is refused,
# whatever follows: the underscore would hide a leading zero
# TOML-NUM-1
# TOML-NUM-2
law num_zero_underscore:
  for +rest: List<&2, Char>
  {refused(T.word.num('0' <> '_' <> rest)) == True{} : Bool}

# LAW: a signed numeral that starts with a zero and an underscore is refused,
# whatever follows
# TOML-NUM-1
# TOML-NUM-2
law num_signed_zero_underscore:
  for sg: T.Sign
  for +rest: List<&2, Char>
  {refused(T.word.num(mark(sg) <> '0' <> '_' <> rest)) == True{} : Bool}

# LAW: after one sign, a character that is not a sign is read as the first
# character of an unsigned numeral, and the sign is kept
# TOML-NUM-1
# TOML-NUM-2
law num_one_sign:
  for +sg: T.Sign
  for +cc: Char
  for e: {False{} == is_sign(cc) : Bool}
  {T.num.step(T.num.step(T.num.start(), mark(sg)), cc)
    == T.num.lead(T.Num{T.NLead{}, sg, 10, [], False{}, False{}, ""}, cc) : T.Num}

# LAW: a bare word that starts with two signs holds no value, whatever
# follows: it is neither a special, a datetime nor a numeral
# TOML-NUM-1
# TOML-NUM-2
law word_two_signs:
  for s1: T.Sign
  for s2: T.Sign
  for +rest: List<&2, Char>
  {refused(T.word.val(mark(s1) <> mark(s2) <> rest)) == True{} : Bool}

# LAW: a bare word that starts with a zero and an underscore, with or without
# a sign, holds no value, whatever follows
# TOML-NUM-1
# TOML-NUM-2
law word_zero_underscore:
  for +rest: List<&2, Char>
  {refused(T.word.val('0' <> '_' <> rest)) == True{} : Bool}

# LAW: the same after a sign
# TOML-NUM-1
# TOML-NUM-2
law word_signed_zero_underscore:
  for sg: T.Sign
  for +rest: List<&2, Char>
  {refused(T.word.val(mark(sg) <> '0' <> '_' <> rest)) == True{} : Bool}

# The date check (I4). The day of a date is within its month in its year.

# the twelve months, so a law can range over every one
type Month is Data:
  Jan{}
  Feb{}
  Mar{}
  Apr{}
  May{}
  Jun{}
  Jul{}
  Aug{}
  Sep{}
  Oct{}
  Nov{}
  Dec{}

# a month's number, as a date writes it
def month.num(mm: Month) -> U32:
  match mm:
    case Jan{}:
      1
    case Feb{}:
      2
    case Mar{}:
      3
    case Apr{}:
      4
    case May{}:
      5
    case Jun{}:
      6
    case Jul{}:
      7
    case Aug{}:
      8
    case Sep{}:
      9
    case Oct{}:
      10
    case Nov{}:
      11
    case Dec{}:
      12

# RFC 3339, Appendix C: a leap year is
#   (year % 4 == 0 && (year % 100 != 0 || year % 400 == 0))
def leap(+yy: U32) -> Bool:
  Bool.and(U32.is_eq(U32.mod(yy, 4), 0),
    Bool.or(Bool.not(U32.is_eq(U32.mod(yy, 100), 0)), U32.is_eq(U32.mod(yy, 400), 0)))

# February's row of the table below
def feb_days(is_leap: Bool) -> U32:
  match is_leap:
    case True{}:
      29
    case False{}:
      28

# RFC 3339, section 5.7:
#   Month Number  Month/Year           Maximum value of date-mday
#   ------------  ----------           --------------------------
#   01            January              31
#   02            February, normal     28
#   02            February, leap year  29
#   03            March                31
#   04            April                30
#   05            May                  31
#   06            June                 30
#   07            July                 31
#   08            August               31
#   09            September            30
#   10            October              31
#   11            November             30
#   12            December             31
def days_in(+yy: U32, mm: Month) -> U32:
  match mm:
    case Jan{}:
      31
    case Feb{}:
      feb_days(leap(yy))
    case Mar{}:
      31
    case Apr{}:
      30
    case May{}:
      31
    case Jun{}:
      30
    case Jul{}:
      31
    case Aug{}:
      31
    case Sep{}:
      30
    case Oct{}:
      31
    case Nov{}:
      30
    case Dec{}:
      31

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
# TOML-TIME-1
law date_day_in_month:
  for +yy: U32
  for +mm: Month
  for +dd: U32
  for rest: List<&2, Char>
  for e: {True{} == Bool.and(U32.is_ge(dd, 1), U32.is_le(dd, days_in(yy, mm))) : Bool}
  {T.when.date.ok(yy, month.num(mm), dd, rest)
    == T.when.after.date(T.Date{yy, month.num(mm), dd}, rest) : T.WhenOut}

# LAW: a date whose day is 0 or past the days of its month in its year is
# refused, whatever follows it
# TOML-TIME-1
law date_day_past_month:
  for +yy: U32
  for +mm: Month
  for +dd: U32
  for rest: List<&2, Char>
  for e: {False{} == Bool.and(U32.is_ge(dd, 1), U32.is_le(dd, days_in(yy, mm))) : Bool}
  {when_refused(T.when.date.ok(yy, month.num(mm), dd, rest)) == True{} : Bool}

# LAW: once the scanner has failed, the rest of the text leaves the first error
# as it is. Every refusal of the scanner lands here, so each law below only
# has to show that one step fails
# TOML-TEXT-1
law fail_stays:
  for +bad: String
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +here: List<&2, String>
  for +parts: List<&2, String>
  for +buf: List<&2, Char>
  for +back: T.Lex
  for +qkind: T.QKind
  for +stack: List<&2, T.Ctx>
  for +uni: U32
  for +left: U32
  for +arrtab: Bool
  for +lead: Bool
  for e: {String.is_empty(bad) == False{} : Bool}
  for +t: String
  {T.bad(T.doc.read(t, T.MScan{T.St{bad, rows, heads, here, parts, buf, T.LSink{}, back,
    qkind, stack, T.HNone{}, uni, left, arrtab, lead}})) == bad : String}

# a character toml.abnf's non-eol leaves out, besides the line feed and the
# carriage return a newline is made of: U+0000 to U+001F or U+007F, and not
# U+000A, U+000D or tab
def com.ctl(+cc: Char) -> Bool:
  Bool.and(Bool.or(U32.is_lt(Char.to_u32(cc), 32), U32.is_eq(Char.to_u32(cc), 127)),
    Bool.not(Bool.or(Bool.or(U32.is_eq(Char.to_u32(cc), 10),
      U32.is_eq(Char.to_u32(cc), 13)), U32.is_eq(Char.to_u32(cc), 9))))

# LAW: a comment holds no control but tab: from every scanner state inside a
# comment, such a character fails the document, whatever follows it
# TOML-TEXT-1
law comment_control_refused:
  for +bad: String
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +here: List<&2, String>
  for +parts: List<&2, String>
  for +buf: List<&2, Char>
  for +back: T.Lex
  for +qkind: T.QKind
  for +stack: List<&2, T.Ctx>
  for +uni: U32
  for +left: U32
  for +arrtab: Bool
  for +c: Char
  for e: {com.ctl(c) == True{} : Bool}
  for +t: String
  {String.is_empty(T.bad(T.doc.read(SCon{c, t}, T.MScan{T.St{bad, rows, heads, here,
    parts, buf, T.LCom{}, back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}}})))
    == False{} : Bool}

# LAW: a carriage return is a newline only with a line feed after it: from
# every scanner state, one followed by any other character fails the document
# TOML-TEXT-1
law lone_cr_refused:
  for +st: T.St
  for +c: Char
  for e: {Char.is_eq(c, '\n') == False{} : Bool}
  for +t: String
  {String.is_empty(T.bad(T.doc.read(SCon{'\r', SCon{c, t}}, T.MScan{st}))) == False{}
    : Bool}

# LAW: and one that ends the text fails it too
# TOML-TEXT-1
law last_cr_refused:
  for +st: T.St
  {String.is_empty(T.bad(T.doc.read("\r", T.MScan{st}))) == False{} : Bool}

# LAW: a value is on its key's line: from every scanner state waiting for the
# value after `=`, a line feed fails the document, whatever follows it
# TOML-TEXT-1
law value_on_key_line:
  for +bad: String
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +here: List<&2, String>
  for +parts: List<&2, String>
  for +buf: List<&2, Char>
  for +back: T.Lex
  for +qkind: T.QKind
  for +stack: List<&2, T.Ctx>
  for +uni: U32
  for +left: U32
  for +arrtab: Bool
  for +t: String
  {String.is_empty(T.bad(T.doc.read(SCon{'\n', t}, T.MScan{T.St{bad, rows, heads, here,
    parts, buf, T.LVal{}, back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}}})))
    == False{} : Bool}

# LAW: and so does a carriage return and line feed
# TOML-TEXT-1
law value_on_key_line_crlf:
  for +bad: String
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +here: List<&2, String>
  for +parts: List<&2, String>
  for +buf: List<&2, Char>
  for +back: T.Lex
  for +qkind: T.QKind
  for +stack: List<&2, T.Ctx>
  for +uni: U32
  for +left: U32
  for +arrtab: Bool
  for +t: String
  {String.is_empty(T.bad(T.doc.read(SCon{'\r', SCon{'\n', t}}, T.MScan{T.St{bad, rows,
    heads, here, parts, buf, T.LVal{}, back, qkind, stack, T.HNone{}, uni, left, arrtab,
    False{}}}))) == False{} : Bool}
