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

# a character a multi-line string of either kind holds as itself: not a
# control (U+0000 to U+001F, U+007F), and not a quote, an apostrophe or a
# backslash
def ml.plain(+cc: Char) -> Bool:
  Bool.and(Bool.not(Bool.or(U32.is_lt(Char.to_u32(cc), 32), U32.is_eq(Char.to_u32(cc), 127))),
    Bool.not(Bool.or(Char.is_eq(cc, '"'), Bool.or(Char.is_eq(cc, '\''),
      Char.is_eq(cc, '\\')))))

# a text of such characters
def ml.text(ss: String) -> Bool:
  match ss:
    case SNil{}:
      True{}
    case SCon{+hh, tt}:
      Bool.and(ml.plain(hh), ml.text(tt))

# LAW: one quote right before a multi-line basic string's closing delimiter
# is part of the string (toml.abnf's mlb-quotes): for every text x of plain
# characters, a = """x"""" and a newline reads x and a quote
# TOML-STR-1
law ml_basic_one_quote:
  for +x: String
  for e: {ml.text(x) == True{} : Bool}
  {T.parse(String.append("a = \"\"\"", String.append(x, "\"\"\"\"\n")))
    == T.Doc{"", [T.VPair{"a", T.VStr{String.append(x, "\"")}}]} : T.Doc}

# LAW: and so are two, with the text ending right after the delimiter:
# a = """x""""" reads x and two quotes
# TOML-STR-1
law ml_basic_two_quotes:
  for +x: String
  for e: {ml.text(x) == True{} : Bool}
  {T.parse(String.append("a = \"\"\"", String.append(x, "\"\"\"\"\"")))
    == T.Doc{"", [T.VPair{"a", T.VStr{String.append(x, "\"\"")}}]} : T.Doc}

# LAW: one apostrophe right before a multi-line literal string's closing
# delimiter is part of the string (mll-quotes): a = '''x'''' and a newline
# reads x and an apostrophe
# TOML-STR-1
law ml_literal_one_quote:
  for +x: String
  for e: {ml.text(x) == True{} : Bool}
  {T.parse(String.append("a = '''", String.append(x, "''''\n")))
    == T.Doc{"", [T.VPair{"a", T.VStr{String.append(x, "'")}}]} : T.Doc}

# LAW: and so are two, with the text ending right after the delimiter:
# a = '''x''''' reads x and two apostrophes
# TOML-STR-1
law ml_literal_two_quotes:
  for +x: String
  for e: {ml.text(x) == True{} : Bool}
  {T.parse(String.append("a = '''", String.append(x, "'''''")))
    == T.Doc{"", [T.VPair{"a", T.VStr{String.append(x, "''")}}]} : T.Doc}

# LAW: an empty basic string may end the text: for every bare key k, k=""
# with nothing after it reads k as the empty string
# TOML-STR-1
law empty_basic_at_end:
  for +k: String
  for e: {T.bare(k) == True{} : Bool}
  {T.parse(String.append(k, "=\"\"")) == T.Doc{"", [T.VPair{k, T.VStr{""}}]} : T.Doc}

# LAW: and so may an empty literal string: k='' reads k as the empty string
# TOML-STR-1
law empty_literal_at_end:
  for +k: String
  for e: {T.bare(k) == True{} : Bool}
  {T.parse(String.append(k, "=''")) == T.Doc{"", [T.VPair{k, T.VStr{""}}]} : T.Doc}

# `same` and `own`: the specification's equality of documents (REVIEW-4).
# A parsed plain string is a span and a built one is owned; a table's pairs
# are in no particular order. `same` compares documents as TOML values: a
# table as the pairs it holds, matched by name whatever their order, an
# array and an array of tables in order, and a scalar by its fields, a
# string by its characters whether owned or a span. A table and an inline
# table are different kinds; a table's stored path and the error field are
# not compared. `own` reads every span out into an owned string.

# the value of a table's first pair of a name, and the rows without that pair
type Pick is Data:
  Picked{val: T.Val, rest: List<&2, T.Val>}
  NoPick{}

# a row kept in front of what a pick left
def pick.cons(hh: T.Val, pp: Pick) -> Pick:
  match pp:
    case Picked{vv, rest}:
      Picked{vv, hh <> rest}
    case NoPick{}:
      NoPick{}

# a pair of the name is picked; any other pair is kept
def pick.step(eq: Bool, nn: String, vv: T.Val, tt: List<&2, T.Val>, more: Unit -> Pick) -> Pick:
  match eq:
    case True{}:
      Picked{vv, tt}
    case False{}:
      pick.cons(T.VPair{nn, vv}, more(Unit{}))

# the first pair named k, taken out of the rows
def pick(rows: List<&2, T.Val>, +kk: String) -> Pick:
  match rows:
    case []:
      NoPick{}
    case T.VPair{+nn, vv} <> +tt:
      pick.step(String.eq(nn, kk), nn, vv, tt, _u => pick(tt, kk))
    case hh <> tt:
      pick.cons(hh, pick(tt, kk))

# the rest when this part holds, and False otherwise
def and_then(ok: Bool, more: Unit -> Bool) -> Bool:
  match ok:
    case True{}:
      more(Unit{})
    case False{}:
      False{}

# the kinds of value that hold a list: an array, an inline table, a table, an
# element of an array of tables, and an array of tables
type Kin is Data:
  KArr{}
  KInl{}
  KHead{}
  KAot{}
  KAots{}

# whether two kinds are one
def kin.eq(aa: Kin, bb: Kin) -> Bool:
  match aa bb:
    case KArr{} KArr{}:
      True{}
    case KInl{} KInl{}:
      True{}
    case KHead{} KHead{}:
      True{}
    case KAot{} KAot{}:
      True{}
    case KAots{} KAots{}:
      True{}
    case _a _b:
      False{}

# a value's kind and list, when it holds one
type Box is Data:
  Boxed{kin: Kin, list: List<&2, T.Val>}
  Unboxed{}

# the kind and the list a value holds
def kids(vv: T.Val) -> Box:
  match vv:
    case T.VArr{items}:
      Boxed{KArr{}, items}
    case T.VInl{rows}:
      Boxed{KInl{}, rows}
    case T.VHead{_path, rows}:
      Boxed{KHead{}, rows}
    case T.VAot{_path, rows}:
      Boxed{KAot{}, rows}
    case T.VAots{_path, elems}:
      Boxed{KAots{}, elems}
    case _:
      Unboxed{}

# a box of the kind whose list the comparison accepts
def same.boxed(kk: Kin, bx: Box, cmp: List<&2, T.Val> -> Bool) -> Bool:
  match bx:
    case Boxed{k2, list}:
      and_then(kin.eq(kk, k2), _u => cmp(list))
    case Unboxed{}:
      False{}

# a value of the kind whose list the comparison accepts
def same.box(kk: Kin, ww: T.Val, cmp: List<&2, T.Val> -> Bool) -> Bool:
  same.boxed(kk, kids(ww), cmp)

# a scalar's fields as parse stores them; a string's characters, owned or a
# span
type Sc is Data:
  ScStr{text: String}
  ScInt{sign: T.Sign, digits: String}
  ScFlo{sign: T.Sign, text: String}
  ScBool{bit: Bool}
  ScWhen{when: T.When}
  ScNo{}

# the fields of a scalar value, and ScNo for any other value
def scal(vv: T.Val) -> Sc:
  match vv:
    case T.VStr{text}:
      ScStr{text}
    case T.VSpan{src, +nn}:
      ScStr{T.span.str(src, nn, U32.is_zero(nn))}
    case T.VInt{sign, digits}:
      ScInt{sign, digits}
    case T.VFlo{sign, text}:
      ScFlo{sign, text}
    case T.VBool{bit}:
      ScBool{bit}
    case T.VWhen{when}:
      ScWhen{when}
    case _:
      ScNo{}

# whether two signs are one
def sign.eq(aa: T.Sign, bb: T.Sign) -> Bool:
  match aa bb:
    case T.Plus{} T.Plus{}:
      True{}
    case T.Minus{} T.Minus{}:
      True{}
    case _a _b:
      False{}

# whether two bits are one
def bit.eq(aa: Bool, bb: Bool) -> Bool:
  match aa bb:
    case True{} True{}:
      True{}
    case False{} False{}:
      True{}
    case _a _b:
      False{}

# whether two dates are one, field by field
def date.eq(aa: T.Date, bb: T.Date) -> Bool:
  match aa bb:
    case T.Date{y1, m1, d1} T.Date{y2, m2, d2}:
      Bool.and(U32.is_eq(y1, y2), Bool.and(U32.is_eq(m1, m2), U32.is_eq(d1, d2)))

# whether two clocks are one, field by field
def clock.eq(aa: T.Clock, bb: T.Clock) -> Bool:
  match aa bb:
    case T.Clock{h1, m1, s1, f1} T.Clock{h2, m2, s2, f2}:
      Bool.and(U32.is_eq(h1, h2), Bool.and(U32.is_eq(m1, m2),
        Bool.and(U32.is_eq(s1, s2), String.eq(f1, f2))))

# whether two zones are one, field by field
def zone.eq(aa: T.Zone, bb: T.Zone) -> Bool:
  match aa bb:
    case T.Zulu{} T.Zulu{}:
      True{}
    case T.Shift{s1, h1, m1} T.Shift{s2, h2, m2}:
      Bool.and(sign.eq(s1, s2), Bool.and(U32.is_eq(h1, h2), U32.is_eq(m1, m2)))
    case _a _b:
      False{}

# whether two datetimes are one: the same form, field by field
def when.eq(aa: T.When, bb: T.When) -> Bool:
  match aa bb:
    case T.WOff{d1, c1, z1} T.WOff{d2, c2, z2}:
      Bool.and(date.eq(d1, d2), Bool.and(clock.eq(c1, c2), zone.eq(z1, z2)))
    case T.WLocal{d1, c1} T.WLocal{d2, c2}:
      Bool.and(date.eq(d1, d2), clock.eq(c1, c2))
    case T.WDate{d1} T.WDate{d2}:
      date.eq(d1, d2)
    case T.WTime{c1} T.WTime{c2}:
      clock.eq(c1, c2)
    case _a _b:
      False{}

# whether two scalars are one: the same kind, field by field
def sc.eq(aa: Sc, bb: Sc) -> Bool:
  match aa bb:
    case ScStr{x1} ScStr{x2}:
      String.eq(x1, x2)
    case ScInt{s1, d1} ScInt{s2, d2}:
      Bool.and(sign.eq(s1, s2), String.eq(d1, d2))
    case ScFlo{s1, x1} ScFlo{s2, x2}:
      Bool.and(sign.eq(s1, s2), String.eq(x1, x2))
    case ScBool{b1} ScBool{b2}:
      bit.eq(b1, b2)
    case ScWhen{w1} ScWhen{w2}:
      when.eq(w1, w2)
    case _a _b:
      False{}

# whether two values are the same scalar
def same.atom(vv: T.Val, ww: T.Val) -> Bool:
  sc.eq(scal(vv), scal(ww))

# a pair's value against the value of the other rows' first pair of its name,
# then the rest against the other rows without that pair
def same.pair(pp: Pick, cmp: T.Val -> Bool, rest: List<&2, T.Val> -> Bool) -> Bool:
  match pp:
    case Picked{ww, left}:
      and_then(cmp(ww), _u => rest(left))
    case NoPick{}:
      False{}

# a value that is not a pair against the other rows' first value, then the
# rest against the others after it
def same.item(other: List<&2, T.Val>, cmp: T.Val -> Bool, rest: List<&2, T.Val> -> Bool) -> Bool:
  match other:
    case []:
      False{}
    case ww <> left:
      and_then(cmp(ww), _u => rest(left))

# whether every value of xs has its match in the other rows, with nothing of
# them left over: a pair matches the first pair of its name, wherever it is,
# and any other value matches the first value left, in order. A table's rows
# are pairs and an array's items are not, so a table is compared as a map
# and an array in order. A pair whose value is a pair, which no well-formed
# document holds, matches nothing
def same.go(xs: List<&2, T.Val>, other: List<&2, T.Val>) -> Bool:
  match xs:
    case []:
      List.is_empty(&2, T.Val, other)
    case T.VPair{nn, T.VArr{items}} <> tt:
      same.pair(pick(other, nn), ww => same.box(KArr{}, ww, ws => same.go(items, ws)), rr => same.go(tt, rr))
    case T.VPair{nn, T.VInl{rows}} <> tt:
      same.pair(pick(other, nn), ww => same.box(KInl{}, ww, ws => same.go(rows, ws)), rr => same.go(tt, rr))
    case T.VPair{nn, T.VHead{_path, rows}} <> tt:
      same.pair(pick(other, nn), ww => same.box(KHead{}, ww, ws => same.go(rows, ws)), rr => same.go(tt, rr))
    case T.VPair{nn, T.VAot{_path, rows}} <> tt:
      same.pair(pick(other, nn), ww => same.box(KAot{}, ww, ws => same.go(rows, ws)), rr => same.go(tt, rr))
    case T.VPair{nn, T.VAots{_path, elems}} <> tt:
      same.pair(pick(other, nn), ww => same.box(KAots{}, ww, ws => same.go(elems, ws)), rr => same.go(tt, rr))
    case T.VPair{nn, vv} <> tt:
      same.pair(pick(other, nn), ww => same.atom(vv, ww), rr => same.go(tt, rr))
    case T.VArr{items} <> tt:
      same.item(other, ww => same.box(KArr{}, ww, ws => same.go(items, ws)), rr => same.go(tt, rr))
    case T.VInl{rows} <> tt:
      same.item(other, ww => same.box(KInl{}, ww, ws => same.go(rows, ws)), rr => same.go(tt, rr))
    case T.VHead{_path, rows} <> tt:
      same.item(other, ww => same.box(KHead{}, ww, ws => same.go(rows, ws)), rr => same.go(tt, rr))
    case T.VAot{_path, rows} <> tt:
      same.item(other, ww => same.box(KAot{}, ww, ws => same.go(rows, ws)), rr => same.go(tt, rr))
    case T.VAots{_path, elems} <> tt:
      same.item(other, ww => same.box(KAots{}, ww, ws => same.go(elems, ws)), rr => same.go(tt, rr))
    case vv <> tt:
      same.item(other, ww => same.atom(vv, ww), rr => same.go(tt, rr))

# whether two documents are the same TOML document: each root table matches
# the other
def same(aa: T.Doc, bb: T.Doc) -> Bool:
  match aa bb:
    case T.Doc{_e1, +r1} T.Doc{_e2, +r2}:
      Bool.and(same.go(r1, r2), same.go(r2, r1))

# rows with every span read out into an owned string. A pair whose value is a
# pair, which no well-formed document holds, is kept as it is
def own.rows(vs: List<&2, T.Val>) -> List<&2, T.Val>:
  match vs:
    case []:
      []
    case T.VPair{nn, T.VSpan{src, +kk}} <> tt:
      T.VPair{nn, T.VStr{T.span.str(src, kk, U32.is_zero(kk))}} <> own.rows(tt)
    case T.VPair{nn, T.VArr{items}} <> tt:
      T.VPair{nn, T.VArr{own.rows(items)}} <> own.rows(tt)
    case T.VPair{nn, T.VInl{rows}} <> tt:
      T.VPair{nn, T.VInl{own.rows(rows)}} <> own.rows(tt)
    case T.VPair{nn, T.VHead{path, rows}} <> tt:
      T.VPair{nn, T.VHead{path, own.rows(rows)}} <> own.rows(tt)
    case T.VPair{nn, T.VAot{path, rows}} <> tt:
      T.VPair{nn, T.VAot{path, own.rows(rows)}} <> own.rows(tt)
    case T.VPair{nn, T.VAots{path, elems}} <> tt:
      T.VPair{nn, T.VAots{path, own.rows(elems)}} <> own.rows(tt)
    case T.VSpan{src, +kk} <> tt:
      T.VStr{T.span.str(src, kk, U32.is_zero(kk))} <> own.rows(tt)
    case T.VArr{items} <> tt:
      T.VArr{own.rows(items)} <> own.rows(tt)
    case T.VInl{rows} <> tt:
      T.VInl{own.rows(rows)} <> own.rows(tt)
    case T.VHead{path, rows} <> tt:
      T.VHead{path, own.rows(rows)} <> own.rows(tt)
    case T.VAot{path, rows} <> tt:
      T.VAot{path, own.rows(rows)} <> own.rows(tt)
    case T.VAots{path, elems} <> tt:
      T.VAots{path, own.rows(elems)} <> own.rows(tt)
    case vv <> tt:
      vv <> own.rows(tt)

# a document with every span read out into an owned string
def own(dd: T.Doc) -> T.Doc:
  match dd:
    case T.Doc{bad, rows}:
      T.Doc{bad, own.rows(rows)}

# LAW: a well-formed document is the same as itself
law same_refl:
  for +d: T.Doc
  for e: {T.wf(d) == True{} : Bool}
  {same(d, d) == True{} : Bool}

# LAW: same does not depend on which document comes first
law same_sym:
  for a: T.Doc
  for b: T.Doc
  {same(a, b) == same(b, a) : Bool}

# LAW: a well-formed document is the same as itself with every span read out
law same_own:
  for +d: T.Doc
  for e: {T.wf(d) == True{} : Bool}
  {same(d, own(d)) == True{} : Bool}

# LAW: swapping two adjacent pairs of different names in a well-formed
# document's root table gives the same document
law same_swap:
  for +e: String
  for +pre: List<&2, T.Val>
  for +nx: String
  for +vx: T.Val
  for +ny: String
  for +vy: T.Val
  for +post: List<&2, T.Val>
  for w: {T.wf(T.Doc{e, List.append(&2, T.Val, pre, T.VPair{nx, vx} <> T.VPair{ny, vy} <> post)})
    == True{} : Bool}
  for ne: {String.eq(nx, ny) == False{} : Bool}
  {same(T.Doc{e, List.append(&2, T.Val, pre, T.VPair{nx, vx} <> T.VPair{ny, vy} <> post)},
    T.Doc{e, List.append(&2, T.Val, pre, T.VPair{ny, vy} <> T.VPair{nx, vx} <> post)}) == True{} : Bool}

# TOML-STR-2: how render writes a string. A string value, owned or a span, is
# written as key.basic of its characters: a quotation mark, each character's
# escape in order, and a quotation mark. basic.one writes one character,
# reversed onto the output; esc reads it back in order.

# the characters render writes for one character of a string, in order
def esc(+cc: Char) -> String:
  String.from_list(List.reverse(&2, Char, T.basic.one(cc, [])))

# every character of a string written so, in order
def escs(ss: String) -> String:
  match ss:
    case SNil{}:
      ""
    case SCon{+hh, tt}:
      String.append(esc(hh), escs(tt))

# a control character: U+0000 to U+001F, or U+007F
def is_ctl(+cc: Char) -> Bool:
  Bool.or(U32.is_lt(Char.to_u32(cc), 32), U32.is_eq(Char.to_u32(cc), 127))

# the hexadecimal digits, lowercase
def hex_lower() -> String:
  "0123456789abcdef"

# the character at a position of a text; U+0000 past its end
def char_at(+txt: String, left: Nat) -> Char:
  match txt left:
    case SNil{} _n:
      Char.from_u32(0)
    case SCon{hd, _t} 0n:
      hd
    case SCon{_h, tl} 1n+pp:
      char_at(tl, pp)

# LAW: a quotation mark is written as backslash, quotation mark
# TOML-STR-2
law esc_quote:
  for +c: Char
  for h: {c == '"' : Char}
  {esc(c) == "\\\"" : String}

# LAW: a backslash is written as two
# TOML-STR-2
law esc_backslash:
  for +c: Char
  for h: {c == '\\' : Char}
  {esc(c) == "\\\\" : String}

# LAW: a backspace is written as \b
# TOML-STR-2
law esc_b:
  for +c: Char
  for h: {c == '\u{8}' : Char}
  {esc(c) == "\\b" : String}

# LAW: a tab is written as \t
# TOML-STR-2
law esc_t:
  for +c: Char
  for h: {c == '\t' : Char}
  {esc(c) == "\\t" : String}

# LAW: a line feed is written as \n
# TOML-STR-2
law esc_n:
  for +c: Char
  for h: {c == '\n' : Char}
  {esc(c) == "\\n" : String}

# LAW: a form feed is written as \f
# TOML-STR-2
law esc_f:
  for +c: Char
  for h: {c == '\u{c}' : Char}
  {esc(c) == "\\f" : String}

# LAW: a carriage return is written as \r
# TOML-STR-2
law esc_r:
  for +c: Char
  for h: {c == '\r' : Char}
  {esc(c) == "\\r" : String}

# LAW: every other control, U+0000 to U+001F and U+007F, is written as \u00
# and its two hexadecimal digits, lowercase
# TOML-STR-2
law esc_ctl:
  for +c: Char
  for h_c: {is_ctl(c) == True{} : Bool}
  for h_b: {c != '\u{8}' : Char}
  for h_t: {c != '\t' : Char}
  for h_n: {c != '\n' : Char}
  for h_f: {c != '\u{c}' : Char}
  for h_r: {c != '\r' : Char}
  {esc(c) == "\\u00" ++ String.from_list([char_at(hex_lower(), U32.to_nat(U32.div(Char.to_u32(c), 16))),
    char_at(hex_lower(), U32.to_nat(U32.mod(Char.to_u32(c), 16)))]) : String}

# LAW: every character that is no control, no quotation mark and no
# backslash is written as itself
# TOML-STR-2
law esc_plain:
  for +c: Char
  for +h_c: {is_ctl(c) == False{} : Bool}
  for h_q: {c != '"' : Char}
  for h_b: {c != '\\' : Char}
  {esc(c) == String.from_list([c]) : String}

# LAW: a basic string is a quotation mark, each character written in order,
# and a quotation mark
# TOML-STR-2
law basic_escs:
  for +s: String
  {T.key.basic(s) == "\"" ++ escs(s) ++ "\"" : String}

# LAW: a span is quoted, on the fast path that copies it when no character
# needs an escape, exactly as key.basic quotes its characters
# TOML-STR-2
law span_quote_basic:
  for +src: String
  for +n: U32
  {T.span.quote(src, n) == T.key.basic(T.string(T.VSpan{src, n})) : String}

# LAW: a document whose root table starts with a string pair renders that
# pair as its key, " = ", key.basic of its characters and a newline, then the
# rest of the document as it would render alone
# TOML-STR-2
law render_string:
  for +e: String
  for name: String
  for +v: T.Val
  for +rest: List<&2, T.Val>
  for h: {is_string(v) == True{} : Bool}
  {T.render(T.Doc{e, T.VPair{name, v} <> rest})
    == T.key(name) ++ " = " ++ T.key.basic(T.string(v)) ++ "\n" ++ T.render(T.Doc{e, rest}) : String}

# LAW: in any table, the pass that writes keys writes a string pair as its
# key, " = " and key.basic of its characters, then the separator and the rest
# TOML-STR-2
law pass_string:
  for name: String
  for +v: T.Val
  for +rest: List<&2, T.Val>
  for +gap: String
  for +trail: Bool
  for h: {is_string(v) == True{} : Bool}
  {T.render.pass(T.VPair{name, v} <> rest, gap, trail, False{})
    == (T.key(name) ++ " = " ++ T.key.basic(T.string(v))) ++
      T.render.suf(gap, trail, List.is_empty(&2, T.Val, rest)) ++ T.render.pass(rest, gap, trail, False{})
    : String}

# LAW: the pass that writes tables writes nothing for a string pair
# TOML-STR-2
law pass_string_tables:
  for name: String
  for +v: T.Val
  for +rest: List<&2, T.Val>
  for +gap: String
  for +trail: Bool
  for h: {is_string(v) == True{} : Bool}
  {T.render.pass(T.VPair{name, v} <> rest, gap, trail, True{}) == T.render.pass(rest, gap, trail, True{}) : String}

# LAW: in an inline table, a string pair is written as its key, " = " and
# key.basic of its characters, then the separator and the rest
# TOML-STR-2
law inline_string:
  for name: String
  for +v: T.Val
  for +rest: List<&2, T.Val>
  for +gap: String
  for +trail: Bool
  for h: {is_string(v) == True{} : Bool}
  {T.render.go(T.VPair{name, v} <> rest, gap, trail)
    == T.key(name) ++ " = " ++ T.key.basic(T.string(v)) ++
      T.render.suf(gap, trail, List.is_empty(&2, T.Val, rest)) ++ T.render.go(rest, gap, trail) : String}

# LAW: in an array, a string item is written as key.basic of its characters,
# then the separator and the rest
# TOML-STR-2
law array_string:
  for +v: T.Val
  for +rest: List<&2, T.Val>
  for +gap: String
  for +trail: Bool
  for h: {is_string(v) == True{} : Bool}
  {T.render.go(v <> rest, gap, trail)
    == T.key.basic(T.string(v)) ++ T.render.suf(gap, trail, List.is_empty(&2, T.Val, rest)) ++
      T.render.go(rest, gap, trail) : String}

# The table-definition rules (TOML-TEXT-2), stated over the walk that follows
# a key path through the tables. A walk step either enters the table a key
# names or records why it cannot.

# the error a walk step holds, "" while it has none
def tw_bad(tw: T.Tw) -> String:
  match tw:
    case T.Tw{_vs, _job, _stack, bad, _pre, _heads, _inl}:
      bad

# the tables a finished walk has recorded as defined
def end_heads(end: T.End) -> List<&2, String>:
  match end:
    case T.End{_vs, _bad, heads}:
      heads

# the job of a table header: an array of tables, or a table
def header_job(arr: Bool) -> T.Job:
  match arr:
    case True{}:
      T.JAot{}
    case False{}:
      T.JDef{}

# LAW: a dotted key cannot add to a table a header defined: the segment of
# the key that reaches it is refused
# TOML-TEXT-2
law dotted_key_refused_in_header_table:
  for path: String
  for rows: List<&2, T.Val>
  for +name: String
  for vs: List<&2, T.Val>
  for val: T.Val
  for stack: List<&2, T.Fr>
  for +pre: String
  for heads: List<&2, String>
  for inl: Bool
  for e: {T.heads.head(heads, T.tree.pre(pre, name)) == True{} : Bool}
  {String.is_empty(tw_bad(T.tree.sub.look(T.KHead{path, rows}, name, vs,
    T.JPut{val}, stack, pre, heads, inl, True{}))) == False{} : Bool}

# LAW: a dotted key goes on into a table no header defined, such as one other
# dotted keys defined
# TOML-TEXT-2
law dotted_key_enters_other_table:
  for path: String
  for rows: List<&2, T.Val>
  for +name: String
  for vs: List<&2, T.Val>
  for val: T.Val
  for stack: List<&2, T.Fr>
  for +pre: String
  for heads: List<&2, String>
  for inl: Bool
  for e: {T.heads.head(heads, T.tree.pre(pre, name)) == False{} : Bool}
  {tw_bad(T.tree.sub.look(T.KHead{path, rows}, name, vs, T.JPut{val}, stack,
    pre, heads, inl, True{})) == "" : String}

# LAW: a dotted key cannot add to an array of tables
# TOML-TEXT-2
law dotted_key_refused_in_array_of_tables:
  for path: String
  for elems: List<&2, T.Val>
  for name: String
  for vs: List<&2, T.Val>
  for val: T.Val
  for stack: List<&2, T.Fr>
  for pre: String
  for heads: List<&2, String>
  for inl: Bool
  {String.is_empty(tw_bad(T.tree.sub.look(T.KAots{path, elems}, name, vs,
    T.JPut{val}, stack, pre, heads, inl, True{}))) == False{} : Bool}

# LAW: a header goes on through every table on its path, whoever defined it
# TOML-TEXT-2
law header_enters_any_table:
  for path: String
  for rows: List<&2, T.Val>
  for name: String
  for vs: List<&2, T.Val>
  for arr: Bool
  for stack: List<&2, T.Fr>
  for pre: String
  for heads: List<&2, String>
  for inl: Bool
  for mark: Bool
  {tw_bad(T.tree.sub.look(T.KHead{path, rows}, name, vs, header_job(arr),
    stack, pre, heads, inl, mark)) == "" : String}

# LAW: a [table] header that makes a new table records it as defined by a
# header
# TOML-TEXT-2
law header_records_new_table:
  for name: String
  for vs: List<&2, T.Val>
  for stack: List<&2, T.Fr>
  for bad: String
  for +path: String
  for heads: List<&2, String>
  {T.heads.head(end_heads(T.tree.leaf.def.hit(T.KMiss{}, name, vs, stack, bad,
    path, heads)), path) == True{} : Bool}

# LAW: a [table] header that defines a table only made on the way to another
# records it as defined by a header
# TOML-TEXT-2
law header_records_implicit_table:
  for p: String
  for rows: List<&2, T.Val>
  for name: String
  for vs: List<&2, T.Val>
  for stack: List<&2, T.Fr>
  for bad: String
  for +path: String
  for +heads: List<&2, String>
  for e: {T.heads.has(heads, path) == False{} : Bool}
  {T.heads.head(end_heads(T.tree.leaf.def.hit(T.KHead{p, rows}, name, vs,
    stack, bad, path, heads)), path) == True{} : Bool}

# LAW: a new element of an array of tables starts with no table under the
# array defined, so each element is its own scope for defining tables
# TOML-TEXT-2
law new_element_forgets_tables_under_it:
  for p: String
  for elems: List<&2, T.Val>
  for name: String
  for vs: List<&2, T.Val>
  for stack: List<&2, T.Fr>
  for bad: String
  for +path: String
  for +heads: List<&2, String>
  for rest: String
  {T.heads.has(end_heads(T.tree.leaf.aot.hit(T.KAots{p, elems}, name, vs, stack,
    bad, path, heads)), String.append(String.append(path, "."), rest))
    == False{} : Bool}

# LAW: a new element of an array of tables leaves every table not under the
# array defined as it was
# TOML-TEXT-2
law new_element_keeps_other_tables:
  for p: String
  for elems: List<&2, T.Val>
  for name: String
  for vs: List<&2, T.Val>
  for stack: List<&2, T.Fr>
  for bad: String
  for +path: String
  for +heads: List<&2, String>
  for +q: String
  for e: {String.starts_with(q, String.append(path, ".")) == False{} : Bool}
  {T.heads.has(end_heads(T.tree.leaf.aot.hit(T.KAots{p, elems}, name, vs, stack,
    bad, path, heads)), q) == T.heads.has(heads, q) : Bool}

# the rows of a finished walk
def end_rows(end: T.End) -> List<&2, T.Val>:
  match end:
    case T.End{vs, _bad, _heads}:
      vs

# the error of a finished walk, "" when it has none
def end_bad(end: T.End) -> String:
  match end:
    case T.End{_vs, bad, _heads}:
      bad

# whether no pair of the rows holds a table a later key could go on in
def holds_no_open_table(rows: List<&2, T.Val>) -> Bool:
  match rows:
    case []:
      True{}
    case T.VPair{_nn, T.VHead{_pp, _rr}} <> _tt:
      False{}
    case _ <> tt:
      holds_no_open_table(tt)

# LAW: in an inline table, two dotted keys that share their first segment
# are both read: once `b.c = v` is in the inline table, `b.d = w` is read
# with no error when c is not d. The walk is the one an inline table's key
# takes, starting from its rows with no error
# TOML-TEXT-1
law inline_dotted_keys_share_a_prefix:
  for +inl: List<&2, T.Val>
  for +b: String
  for +c: String
  for +d: String
  for +v: T.Val
  for w: T.Val
  for e: {has_pair(inl, b) == False{} : Bool}
  for f: {String.eq(c, d) == False{} : Bool}
  {end_bad(T.tree.walk([b, d], T.Tw{end_rows(T.tree.walk([b, c],
    T.Tw{inl, T.JPut{v}, [], "", "", [], True{}}, 0)), T.JPut{w}, [], "", "", [],
    True{}}, 0)) == "" : String}

# LAW: an inline table, once closed, holds no table a later key could go on
# in: the tables its dotted keys made close with it
# TOML-TEXT-2
law closed_inline_table_holds_no_open_table:
  for rows: List<&2, T.Val>
  {holds_no_open_table(T.inl.seal(rows)) == True{} : Bool}

# LAW: no key goes on in an inline table: a dotted key or a header that
# reaches one is refused
# TOML-TEXT-2
law inline_table_refuses_keys:
  for name: String
  for vs: List<&2, T.Val>
  for job: T.Job
  for stack: List<&2, T.Fr>
  for pre: String
  for heads: List<&2, String>
  for inl: Bool
  for mark: Bool
  {String.is_empty(tw_bad(T.tree.sub.look(T.KInl{}, name, vs, job, stack, pre,
    heads, inl, mark))) == False{} : Bool}


# The header scanner. Each law below holds from every scanner state inside a
# header with the buffer it names, whatever the other fields hold. A refusal
# fails the document whatever follows (fail_stays).

# a quote: a literal one or a basic one
def quote_char(lit: Bool) -> Char:
  match lit:
    case True{}:
      '\''
    case False{}:
      '"'

# the kind of key a quote starts
def quote_kind(lit: Bool) -> T.QKind:
  match lit:
    case True{}:
      T.QLit{}
    case False{}:
      T.QBasic{}

# a space or a tab
def blank_char(tab: Bool) -> Char:
  match tab:
    case True{}:
      '\t'
    case False{}:
      ' '

# LAW: in a header, a quote right after a bare character fails the document,
# whatever follows: a segment is one bare key or one quoted key, so no bare
# part of a header's name is dropped
# TOML-TEXT-1
# TOML-KEY-3
law header_quote_after_bare_refused:
  for bad: String
  for rows: List<&2, T.Val>
  for heads: List<&2, String>
  for here: List<&2, String>
  for parts: List<&2, String>
  for c: Char
  for cs: List<&2, Char>
  for back: T.Lex
  for qkind: T.QKind
  for stack: List<&2, T.Ctx>
  for uni: U32
  for left: U32
  for arrtab: Bool
  for lit: Bool
  for +t: String
  {String.is_empty(T.bad(T.doc.read(SCon{quote_char(lit), t}, T.MScan{T.St{bad, rows,
    heads, here, parts, c <> cs, T.LHead{}, back, qkind, stack, T.HNone{}, uni, left,
    arrtab, False{}}}))) == False{} : Bool}

# LAW: a quote right after a header's opening bracket starts a quoted segment
# TOML-TEXT-1
# TOML-KEY-3
law header_quote_at_start_opens_segment:
  for bad: String
  for rows: List<&2, T.Val>
  for heads: List<&2, String>
  for here: List<&2, String>
  for back: T.Lex
  for qkind: T.QKind
  for stack: List<&2, T.Ctx>
  for uni: U32
  for left: U32
  for arrtab: Bool
  for lit: Bool
  {T.doc.scan(T.St{bad, rows, heads, here, [], [], T.LHead{}, back, qkind, stack,
    T.HNone{}, uni, left, arrtab, False{}}, quote_char(lit))
    == T.MScan{T.St{bad, rows, heads, here, [], [], T.LHeadQ{}, back, quote_kind(lit),
    stack, T.HNone{}, uni, left, arrtab, False{}}} : T.Mode}

# LAW: in a header, blank space with no segment open and then a bracket fail
# the document, whatever follows: the two brackets of `[[` are adjacent, so
# `[ [` does not open an array of tables
# TOML-TEXT-1
law header_blank_then_bracket_refused:
  for bad: String
  for rows: List<&2, T.Val>
  for heads: List<&2, String>
  for here: List<&2, String>
  for parts: List<&2, String>
  for back: T.Lex
  for qkind: T.QKind
  for stack: List<&2, T.Ctx>
  for uni: U32
  for left: U32
  for arrtab: Bool
  for tab: Bool
  for +t: String
  {String.is_empty(T.bad(T.doc.read(SCon{blank_char(tab), SCon{'[', t}},
    T.MScan{T.St{bad, rows, heads, here, parts, [], T.LHead{}, back, qkind, stack,
    T.HNone{}, uni, left, arrtab, False{}}}))) == False{} : Bool}

# LAW: in a header, blank space with no segment open leaves the scanner
# waiting for a segment, as it does after a dot: a bare or quoted key may
# follow
# TOML-TEXT-1
law header_blank_waits_for_segment:
  for bad: String
  for rows: List<&2, T.Val>
  for heads: List<&2, String>
  for here: List<&2, String>
  for parts: List<&2, String>
  for back: T.Lex
  for qkind: T.QKind
  for stack: List<&2, T.Ctx>
  for uni: U32
  for left: U32
  for arrtab: Bool
  for tab: Bool
  {T.doc.scan(T.St{bad, rows, heads, here, parts, [], T.LHead{}, back, qkind, stack,
    T.HNone{}, uni, left, arrtab, False{}}, blank_char(tab))
    == T.MScan{T.St{bad, rows, heads, here, parts, [], T.LHeadDot{}, back, qkind,
    stack, T.HNone{}, uni, left, arrtab, False{}}} : T.Mode}
# TOML-KEY-2's read-back. key writes a name bare, or as a basic string; the
# scanner reads either back as the name's characters.

# LAW: a key reads back as its name: for every string s, key(s) followed by
# " = 1" parses with no error to one pair, named s, holding the integer 1
# TOML-KEY-2
law key_reads_back:
  for +s: String
  {T.parse(String.append(T.key(s), " = 1"))
    == T.Doc{"", [T.VPair{s, T.VInt{T.Plus{}, "1"}}]} : T.Doc}

# TOML-RT-1 for a document of one pair: a bare key and a string render writes
# with no escape. parse keeps such a string as a span of the text, whose
# length it counts in a U32, so the string must be short enough that the
# count does not wrap.

# a character render writes as itself in a basic string: no control, no
# quotation mark and no backslash (esc_plain)
def plain.char(+cc: Char) -> Bool:
  Bool.not(Bool.or(is_ctl(cc), Bool.or(Char.is_eq(cc, '"'), Char.is_eq(cc, '\\'))))

# a text of such characters
def plain.text(ss: String) -> Bool:
  match ss:
    case SNil{}:
      True{}
    case SCon{+hh, tt}:
      Bool.and(plain.char(hh), plain.text(tt))

# counting the characters of a text up from n in a U32 never comes back to 0
def counts(ss: String, +nn: U32) -> Bool:
  match ss:
    case SNil{}:
      True{}
    case SCon{_hh, tt}:
      Bool.and(Bool.not(U32.is_zero(U32.add(nn, 1))), counts(tt, U32.add(nn, 1)))

# fewer than 2^32 characters: a U32 counts them from 0 without wrapping
def short(ss: String) -> Bool:
  counts(ss, 0)

# LAW: a document of one pair, a bare key and a string that render writes
# with no escape and that is shorter than 2^32 characters, reads back with no
# error as the same document
# TOML-RT-1
law render_parse_plain_pair:
  for +e: String
  for +k: String
  for ek: {T.bare(k) == True{} : Bool}
  for +s: String
  for ep: {plain.text(s) == True{} : Bool}
  for es: {short(s) == True{} : Bool}
  {Bool.and(String.is_empty(T.bad(T.parse(T.render(T.Doc{e, [T.VPair{k, T.VStr{s}}]})))),
    same(T.parse(T.render(T.Doc{e, [T.VPair{k, T.VStr{s}}]})), T.Doc{e, [T.VPair{k, T.VStr{s}}]}))
    == True{} : Bool}

# WP-W: contracts of the walk. tree.walk follows a key path from the root and
# applies a job at its end: a value put into a table (JPut), a [table] header
# (JDef) or an [[array]] header (JAot). The laws below say what a walk returns
# (the root's rows, the error and the recorded definitions) for a path whose
# tables are premises read off the rows, so a proof about a document applies
# them without replaying its text. Rows are newest first until rows.seal.

# whether the newest element of an array of tables is one a walk can enter
def tb.last.can(last: T.Last) -> Bool:
  match last:
    case T.LastSome{_p, _older, _rows}:
      True{}
    case T.LastNo{_why}:
      False{}

# whether a walk goes on through what a name refers to: a table, an array of
# tables whose newest element is a table, or nothing yet, where the walk makes
# an implicit table
def tb.can(look: T.Look) -> Bool:
  match look:
    case T.KMiss{}:
      True{}
    case T.KHead{_p, _rows}:
      True{}
    case T.KAots{p, elems}:
      tb.last.can(T.look.last(elems, p))
    case _:
      False{}

# the rows of the newest element of an array of tables
def tb.last.rows(last: T.Last) -> List<&2, T.Val>:
  match last:
    case T.LastSome{_p, _older, rows}:
      rows
    case T.LastNo{_why}:
      []

# the rows a walk goes on in: a table's, the newest element's of an array of
# tables, or none for a table the walk makes
def tb.into(look: T.Look) -> List<&2, T.Val>:
  match look:
    case T.KHead{_p, rows}:
      rows
    case T.KAots{p, elems}:
      tb.last.rows(T.look.last(elems, p))
    case _:
      []

# the newest element of an array of tables with its rows replaced
def tb.last.put(
  last: T.Last,
  +name: String,
  rows: List<&2, T.Val>,
  +pp: String,
  child: List<&2, T.Val>
) -> List<&2, T.Val>:
  match last:
    case T.LastSome{_q, older, _r}:
      T.rows.repl(rows, name, T.VAots{pp, T.VAot{pp, child} <> older})
    case T.LastNo{_why}:
      rows

# the rows with the table a name refers to holding child: a table keeps its
# path, the newest element of an array of tables takes the array's path, and a
# name that is not there yet becomes an implicit table in front
def tb.put.in(
  look: T.Look,
  +name: String,
  rows: List<&2, T.Val>,
  +pre: String,
  child: List<&2, T.Val>
) -> List<&2, T.Val>:
  match look:
    case T.KMiss{}:
      T.VPair{name, T.VHead{T.tree.pre(pre, name), child}} <> rows
    case T.KHead{p, _r}:
      T.rows.repl(rows, name, T.VHead{p, child})
    case T.KAots{+p, elems}:
      tb.last.put(T.look.last(elems, p), name, rows, p, child)
    case _:
      rows

# whether a walk goes on through every segment of the path
def tb.open(path: List<&2, String>, +rows: List<&2, T.Val>) -> Bool:
  match path:
    case []:
      True{}
    case +seg <> rest:
      Bool.and(tb.can(T.rows.look(rows, seg)), tb.open(rest, tb.into(T.rows.look(rows, seg))))

# the rows of the table at the end of the path
def tb.rows(path: List<&2, String>, rows: List<&2, T.Val>) -> List<&2, T.Val>:
  match path:
    case []:
      rows
    case seg <> rest:
      tb.rows(rest, tb.into(T.rows.look(rows, seg)))

# the rows with the table at the end of the path holding new. pre is the path
# of the table the rows are, which names an implicit table made on the way
def tb.set(
  path: List<&2, String>,
  +pre: String,
  +rows: List<&2, T.Val>,
  new: List<&2, T.Val>
) -> List<&2, T.Val>:
  match path:
    case []:
      new
    case +seg <> rest:
      tb.put.in(T.rows.look(rows, seg), seg, rows, pre,
        tb.set(rest, T.tree.pre(pre, seg), tb.into(T.rows.look(rows, seg)), new))

# the path a walk names a table by: each segment as key writes it, joined by
# dots after pre
def tb.join(path: List<&2, String>, pre: String) -> String:
  match path:
    case []:
      pre
    case seg <> rest:
      tb.join(rest, T.tree.pre(pre, seg))

# whether the walk counts skip down past every segment of the path before it
# reaches zero: each segment is navigation into the current table
def counts.down(path: List<&2, String>, +skip: U32) -> Bool:
  match path:
    case []:
      True{}
    case _seg <> rest:
      Bool.and(Bool.not(U32.is_zero(skip)), counts.down(rest, T.path.dec(skip)))

# whether a lookup missed
def is_miss(hh: T.Hit) -> Bool:
  match hh:
    case T.Miss{}:
      True{}
    case T.Found{_v}:
      False{}

# whether a [table] header may define the table a name holds: a name not yet
# there, or a table no header or dotted key defined (one made on the way to
# another)
def hdr.ok(hh: T.Hit, heads: List<&2, String>, +path: String) -> Bool:
  match hh:
    case T.Miss{}:
      True{}
    case T.Found{T.VHead{_p, _rows}}:
      Bool.not(T.heads.has(heads, path))
    case _:
      False{}

# whether an [[array]] header may add an element for a name: a name not yet
# there, or an array of tables
def aot.ok(hh: T.Hit) -> Bool:
  match hh:
    case T.Miss{}:
      True{}
    case T.Found{T.VAots{_p, _elems}}:
      True{}
    case _:
      False{}

# LAW: a value put along a path the walk goes on through, to a name the table
# at its end does not hold, goes at the head of that table's rows (newest
# first); the walk changes nothing else: every other table, the recorded
# definitions and the error are as they were. skip counts the segments that
# are navigation into the current table
law walk_put_at_head:
  for +here: List<&2, String>
  for +k: String
  for +v: T.Val
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +skip: U32
  for +inl: Bool
  for +eo: {tb.open(here, rows) == True{} : Bool}
  for ec: {counts.down(here, skip) == True{} : Bool}
  for em: {T.get(tb.rows(here, rows), k) == T.Miss{} : T.Hit}
  {T.tree.walk(List.append(&2, String, here, [k]), T.Tw{rows, T.JPut{v}, [], "", "", heads, inl},
    skip) == T.End{tb.set(here, "", rows, T.VPair{k, v} <> tb.rows(here, rows)), "", heads} : T.End}

# LAW: a value put along a path the walk goes on through is refused exactly
# when the table at its end already holds the name: a key is defined once
# TOML-TEXT-2
law walk_put_refused_exactly:
  for +here: List<&2, String>
  for +k: String
  for +v: T.Val
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +skip: U32
  for +inl: Bool
  for eo: {tb.open(here, rows) == True{} : Bool}
  for ec: {counts.down(here, skip) == True{} : Bool}
  {String.is_empty(end_bad(T.tree.walk(List.append(&2, String, here, [k]),
    T.Tw{rows, T.JPut{v}, [], "", "", heads, inl}, skip)))
    == is_miss(T.get(tb.rows(here, rows), k)) : Bool}

# LAW: a [table] header whose last segment names nothing yet defines a new,
# empty table at the head of the rows it walks to, and records its path as
# defined by a header; nothing else changes
law header_defines_new_table:
  for +segs: List<&2, String>
  for +k: String
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +eo: {tb.open(segs, rows) == True{} : Bool}
  for em: {T.get(tb.rows(segs, rows), k) == T.Miss{} : T.Hit}
  {T.tree.walk(List.append(&2, String, segs, [k]), T.Tw{rows, T.JDef{}, [], "", "", heads, False{}}, 0)
    == T.End{tb.set(segs, "", rows, T.VPair{k, T.VHead{T.tree.pre(tb.join(segs, ""), k), []}}
      <> tb.rows(segs, rows)), "", T.heads.by.head(T.tree.pre(tb.join(segs, ""), k)) <> heads}
    : T.End}

# LAW: a [table] header whose last segment names a table only made on the way
# to another defines it where it is, under the header's path, and records the
# path as defined by a header; nothing else changes
law header_defines_implicit_table:
  for +segs: List<&2, String>
  for +k: String
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for p: String
  for +sub: List<&2, T.Val>
  for +eo: {tb.open(segs, rows) == True{} : Bool}
  for ef: {T.get(tb.rows(segs, rows), k) == T.Found{T.VHead{p, sub}} : T.Hit}
  for eh: {T.heads.has(heads, T.tree.pre(tb.join(segs, ""), k)) == False{} : Bool}
  {T.tree.walk(List.append(&2, String, segs, [k]), T.Tw{rows, T.JDef{}, [], "", "", heads, False{}}, 0)
    == T.End{tb.set(segs, "", rows, T.rows.repl(tb.rows(segs, rows), k,
      T.VHead{T.tree.pre(tb.join(segs, ""), k), sub})), "",
      T.heads.by.head(T.tree.pre(tb.join(segs, ""), k)) <> heads} : T.End}

# LAW: a [table] header is refused exactly when its last segment names
# something other than a table, or a table a header or dotted keys defined
# TOML-TEXT-2
law header_refused_exactly:
  for +segs: List<&2, String>
  for +k: String
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for eo: {tb.open(segs, rows) == True{} : Bool}
  {String.is_empty(end_bad(T.tree.walk(List.append(&2, String, segs, [k]),
    T.Tw{rows, T.JDef{}, [], "", "", heads, False{}}, 0)))
    == hdr.ok(T.get(tb.rows(segs, rows), k), heads, T.tree.pre(tb.join(segs, ""), k)) : Bool}

# LAW: an [[array]] header whose last segment names nothing yet starts an
# array of tables of one empty element at the head of the rows it walks to;
# nothing else changes, and no definition is recorded
law aot_header_starts_array:
  for +segs: List<&2, String>
  for +k: String
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +eo: {tb.open(segs, rows) == True{} : Bool}
  for em: {T.get(tb.rows(segs, rows), k) == T.Miss{} : T.Hit}
  {T.tree.walk(List.append(&2, String, segs, [k]), T.Tw{rows, T.JAot{}, [], "", "", heads, False{}}, 0)
    == T.End{tb.set(segs, "", rows, T.VPair{k, T.VAots{T.tree.pre(tb.join(segs, ""), k),
      [T.VAot{T.tree.pre(tb.join(segs, ""), k), []}]}} <> tb.rows(segs, rows)), "", heads} : T.End}

# LAW: an [[array]] header whose last segment names an array of tables adds
# a new empty element in front of its elements (newest first), and forgets
# every table under the array defined, so the element is its own scope;
# nothing else changes
law aot_header_extends_array:
  for +segs: List<&2, String>
  for +k: String
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for p: String
  for +elems: List<&2, T.Val>
  for +eo: {tb.open(segs, rows) == True{} : Bool}
  for ef: {T.get(tb.rows(segs, rows), k) == T.Found{T.VAots{p, elems}} : T.Hit}
  {T.tree.walk(List.append(&2, String, segs, [k]), T.Tw{rows, T.JAot{}, [], "", "", heads, False{}}, 0)
    == T.End{tb.set(segs, "", rows, T.rows.repl(tb.rows(segs, rows), k,
      T.VAots{T.tree.pre(tb.join(segs, ""), k), T.VAot{T.tree.pre(tb.join(segs, ""), k), []}
        <> elems})), "",
      T.heads.drop(heads, String.append(T.tree.pre(tb.join(segs, ""), k), "."))} : T.End}

# LAW: an [[array]] header is refused exactly when its last segment names
# something other than an array of tables: a table, an inline table, a
# static array or any other value
# TOML-TEXT-2
law aot_header_refused_exactly:
  for +segs: List<&2, String>
  for +k: String
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for eo: {tb.open(segs, rows) == True{} : Bool}
  {String.is_empty(end_bad(T.tree.walk(List.append(&2, String, segs, [k]),
    T.Tw{rows, T.JAot{}, [], "", "", heads, False{}}, 0)))
    == aot.ok(T.get(tb.rows(segs, rows), k)) : Bool}

# LAW: a walk that starts with an error keeps it and changes nothing: once a
# key or header is refused, no later one in the same text clears the error
# or touches the tables
# TOML-TEXT-2
law failed_walk_changes_nothing:
  for path: List<&2, String>
  for +rows: List<&2, T.Val>
  for +job: T.Job
  for +bad: String
  for +pre: String
  for +heads: List<&2, String>
  for +inl: Bool
  for +skip: U32
  for +eb: {String.is_empty(bad) == False{} : Bool}
  {T.tree.walk(path, T.Tw{rows, job, [], bad, pre, heads, inl}, skip) == T.End{rows, bad, heads}
    : T.End}

# a value as rows.seal leaves it: the rows of a table, of an element of an
# array of tables and of an inline table, and the elements of an array of
# tables, each sealed in turn; an array's items sealed and kept in order
def sealed(+vv: T.Val) -> T.Val:
  match vv:
    case T.VPair{nn, T.VHead{pp, rows}}:
      T.VPair{nn, T.VHead{pp, T.rows.seal(rows)}}
    case T.VPair{nn, T.VAots{pp, elems}}:
      T.VPair{nn, T.VAots{pp, T.rows.seal(elems)}}
    case T.VPair{nn, T.VInl{rows}}:
      T.VPair{nn, T.VInl{T.rows.seal(rows)}}
    case T.VPair{nn, T.VArr{items}}:
      T.VPair{nn, T.VArr{List.reverse(&2, T.Val, T.rows.seal(items))}}
    case T.VAot{pp, rows}:
      T.VAot{pp, T.rows.seal(rows)}
    case T.VAots{pp, elems}:
      T.VAots{pp, T.rows.seal(elems)}
    case T.VInl{rows}:
      T.VInl{T.rows.seal(rows)}
    case T.VArr{items}:
      T.VArr{List.reverse(&2, T.Val, T.rows.seal(items))}
    case _:
      vv

# LAW: rows.seal puts the newest row last: sealing rows with x at their head
# is sealing the rest, then x sealed. Rows built newest first come out in the
# order they were written, and every table inside is sealed the same way
law seal_puts_newest_last:
  for +x: T.Val
  for +rows: List<&2, T.Val>
  {T.rows.seal(x <> rows) == List.append(&2, T.Val, T.rows.seal(rows), [sealed(x)])
    : List<&2, T.Val>}

# LAW: the table a path leads to, once set, holds what it was set to, so the
# next walk along the same path puts into what the last one left
law tb_rows_after_set:
  for path: List<&2, String>
  for +pre: String
  for +rows: List<&2, T.Val>
  for +new: List<&2, T.Val>
  for +eo: {tb.open(path, rows) == True{} : Bool}
  {tb.rows(path, tb.set(path, pre, rows, new)) == new : List<&2, T.Val>}

# LAW: and a walk still goes on through every segment of the path
law tb_open_after_set:
  for path: List<&2, String>
  for +pre: String
  for +rows: List<&2, T.Val>
  for +new: List<&2, T.Val>
  for +eo: {tb.open(path, rows) == True{} : Bool}
  {tb.open(path, tb.set(path, pre, rows, new)) == True{} : Bool}

# WP-H: headers read back. A header as render writes it, `[`, its path, `]`
# and a newline, read from the start of a line, is the rest of the text read
# from the start of the next line, with the rows and definitions the header's
# walk returns (WP-W's contracts say what those are) and the header's
# segments as the current table. A quoted segment leaves back and qkind
# where its last escape and its quote put them, so each law takes the rest of
# the text as read from every back and qkind.

# the scanner at the start of a line in the table here: nothing buffered, no
# array or inline table open, and back, qkind and arrtab as the lines before
# left them
def hb.line(
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  back: T.Lex,
  qkind: T.QKind,
  arrtab: Bool
) -> T.St:
  T.St{"", rows, heads, here, [], [], T.LTop{}, back, qkind, [], T.HNone{}, 0, 0, arrtab,
    False{}}

# LAW: a header as render writes it, `[`, the stored path (the parent's path
# joined with the last segment k, each segment bare or basic-quoted as key
# writes it), `]` and a newline, read from the start of a line, is the rest
# read from the start of the next line in the table named by the segments'
# characters, with the rows and definitions the walk along those names
# returns. Every name reads back as itself, escapes decoded
# TOML-KEY-3
law header_reads_back:
  for +segs: List<&2, String>
  for +k: String
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +here: List<&2, String>
  for +back: T.Lex
  for +qkind: T.QKind
  for +arrtab: Bool
  for +rows2: List<&2, T.Val>
  for +heads2: List<&2, String>
  for ew: {T.tree.walk(List.append(&2, String, segs, [k]), T.Tw{rows, T.JDef{}, [], "", "", heads,
    False{}}, 0) == T.End{rows2, "", heads2} : T.End}
  for +rest: String
  for +goal: T.Doc
  for ih: @bk: T.Lex -> @qk: T.QKind -> {T.doc.read(rest, T.MScan{hb.line(rows2, heads2,
    List.append(&2, String, segs, [k]), bk, qk, False{})}) == goal : T.Doc}
  {T.doc.read("[" ++ T.tree.pre(tb.join(segs, ""), k) ++ "]\n" ++ rest, T.MScan{hb.line(rows, heads,
    here, back, qkind, arrtab)}) == goal : T.Doc}

# LAW: a header whose last segment names nothing yet in the table its parent
# path leads to reads back with a new, empty table under k's characters at
# the head of that table's rows, recorded as defined by a header, and the
# header's segments as the current table (header_defines_new_table)
# TOML-KEY-3
law header_new_table_reads_back:
  for +segs: List<&2, String>
  for +k: String
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +eo: {tb.open(segs, rows) == True{} : Bool}
  for em: {T.get(tb.rows(segs, rows), k) == T.Miss{} : T.Hit}
  for +here: List<&2, String>
  for +back: T.Lex
  for +qkind: T.QKind
  for +arrtab: Bool
  for +rest: String
  for +goal: T.Doc
  for ih: @bk: T.Lex -> @qk: T.QKind -> {T.doc.read(rest, T.MScan{hb.line(tb.set(segs, "", rows,
    T.VPair{k, T.VHead{T.tree.pre(tb.join(segs, ""), k), []}} <> tb.rows(segs, rows)),
    T.heads.by.head(T.tree.pre(tb.join(segs, ""), k)) <> heads, List.append(&2, String, segs, [k]),
    bk, qk, False{})}) == goal : T.Doc}
  {T.doc.read("[" ++ T.tree.pre(tb.join(segs, ""), k) ++ "]\n" ++ rest, T.MScan{hb.line(rows, heads,
    here, back, qkind, arrtab)}) == goal : T.Doc}

# LAW: a header whose last segment names a table only made on the way to
# another reads back with that table defined where it is, under the header's
# path, and recorded as defined by a header (header_defines_implicit_table)
# TOML-KEY-3
law header_implicit_table_reads_back:
  for +segs: List<&2, String>
  for +k: String
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for p: String
  for +sub: List<&2, T.Val>
  for +eo: {tb.open(segs, rows) == True{} : Bool}
  for ef: {T.get(tb.rows(segs, rows), k) == T.Found{T.VHead{p, sub}} : T.Hit}
  for eh: {T.heads.has(heads, T.tree.pre(tb.join(segs, ""), k)) == False{} : Bool}
  for +here: List<&2, String>
  for +back: T.Lex
  for +qkind: T.QKind
  for +arrtab: Bool
  for +rest: String
  for +goal: T.Doc
  for ih: @bk: T.Lex -> @qk: T.QKind -> {T.doc.read(rest, T.MScan{hb.line(tb.set(segs, "", rows,
    T.rows.repl(tb.rows(segs, rows), k, T.VHead{T.tree.pre(tb.join(segs, ""), k), sub})),
    T.heads.by.head(T.tree.pre(tb.join(segs, ""), k)) <> heads, List.append(&2, String, segs, [k]),
    bk, qk, False{})}) == goal : T.Doc}
  {T.doc.read("[" ++ T.tree.pre(tb.join(segs, ""), k) ++ "]\n" ++ rest, T.MScan{hb.line(rows, heads,
    here, back, qkind, arrtab)}) == goal : T.Doc}

# LAW: an array-of-tables header as render writes it, `[[`, the stored path,
# `]]` and a newline, read from the start of a line, is the rest read from the
# start of the next line in the table named by the segments' characters, with
# the rows and definitions the walk along those names returns
# TOML-KEY-3
law aot_header_reads_back:
  for +segs: List<&2, String>
  for +k: String
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +here: List<&2, String>
  for +back: T.Lex
  for +qkind: T.QKind
  for +arrtab: Bool
  for +rows2: List<&2, T.Val>
  for +heads2: List<&2, String>
  for ew: {T.tree.walk(List.append(&2, String, segs, [k]), T.Tw{rows, T.JAot{}, [], "", "", heads,
    False{}}, 0) == T.End{rows2, "", heads2} : T.End}
  for +rest: String
  for +goal: T.Doc
  for ih: @bk: T.Lex -> @qk: T.QKind -> {T.doc.read(rest, T.MScan{hb.line(rows2, heads2,
    List.append(&2, String, segs, [k]), bk, qk, False{})}) == goal : T.Doc}
  {T.doc.read("[[" ++ T.tree.pre(tb.join(segs, ""), k) ++ "]]\n" ++ rest, T.MScan{hb.line(rows,
    heads, here, back, qkind, arrtab)}) == goal : T.Doc}

# LAW: an array-of-tables header whose last segment names nothing yet reads
# back with an array of one empty element under k's characters at the head
# of the rows its parent path leads to (aot_header_starts_array)
# TOML-KEY-3
law aot_header_new_array_reads_back:
  for +segs: List<&2, String>
  for +k: String
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +eo: {tb.open(segs, rows) == True{} : Bool}
  for em: {T.get(tb.rows(segs, rows), k) == T.Miss{} : T.Hit}
  for +here: List<&2, String>
  for +back: T.Lex
  for +qkind: T.QKind
  for +arrtab: Bool
  for +rest: String
  for +goal: T.Doc
  for ih: @bk: T.Lex -> @qk: T.QKind -> {T.doc.read(rest, T.MScan{hb.line(tb.set(segs, "", rows,
    T.VPair{k, T.VAots{T.tree.pre(tb.join(segs, ""), k), [T.VAot{T.tree.pre(tb.join(segs, ""), k),
    []}]}} <> tb.rows(segs, rows)), heads, List.append(&2, String, segs, [k]), bk, qk, False{})})
    == goal : T.Doc}
  {T.doc.read("[[" ++ T.tree.pre(tb.join(segs, ""), k) ++ "]]\n" ++ rest, T.MScan{hb.line(rows,
    heads, here, back, qkind, arrtab)}) == goal : T.Doc}

# LAW: an array-of-tables header whose last segment names an array of tables
# reads back with a new empty element in front of its elements, and every
# table under the array forgotten (aot_header_extends_array)
# TOML-KEY-3
law aot_header_extends_array_reads_back:
  for +segs: List<&2, String>
  for +k: String
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for p: String
  for +elems: List<&2, T.Val>
  for +eo: {tb.open(segs, rows) == True{} : Bool}
  for ef: {T.get(tb.rows(segs, rows), k) == T.Found{T.VAots{p, elems}} : T.Hit}
  for +here: List<&2, String>
  for +back: T.Lex
  for +qkind: T.QKind
  for +arrtab: Bool
  for +rest: String
  for +goal: T.Doc
  for ih: @bk: T.Lex -> @qk: T.QKind -> {T.doc.read(rest, T.MScan{hb.line(tb.set(segs, "", rows,
    T.rows.repl(tb.rows(segs, rows), k, T.VAots{T.tree.pre(tb.join(segs, ""), k),
    T.VAot{T.tree.pre(tb.join(segs, ""), k), []} <> elems})),
    T.heads.drop(heads, String.append(T.tree.pre(tb.join(segs, ""), k), ".")),
    List.append(&2, String, segs, [k]), bk, qk, False{})}) == goal : T.Doc}
  {T.doc.read("[[" ++ T.tree.pre(tb.join(segs, ""), k) ++ "]]\n" ++ rest, T.MScan{hb.line(rows,
    heads, here, back, qkind, arrtab)}) == goal : T.Doc}

# WP-S: a rendered string read back in any value position. render writes a
# string as key.basic of its characters (TOML-STR-2); parse reads that text
# back as those characters, as a span of the text or, once a character needs
# an escape, as an owned string, which own reads alike. The laws below read
# one string in each position a value takes: a root pair's value, an array
# item and an inline table's pair. The string must be short: a span counts
# its characters in a U32.

# LAW: a basic string render writes reads back as its text in a root pair:
# for every bare key k and every string s shorter than 2^32 characters,
# k = key.basic(s) and a newline parse with no error to one pair named k
# holding s
# TOML-STR-1
law basic_string_reads_back:
  for +k: String
  for ek: {T.bare(k) == True{} : Bool}
  for +s: String
  for es: {short(s) == True{} : Bool}
  {own(T.parse(String.append(k, String.append(" = ", String.append(T.key.basic(s), "\n")))))
    == T.Doc{"", [T.VPair{k, T.VStr{s}}]} : T.Doc}

# LAW: and as an array item: k = [key.basic(s)] and a newline parse with no
# error to one pair named k holding an array of s
# TOML-STR-1
law basic_string_reads_back_in_array:
  for +k: String
  for ek: {T.bare(k) == True{} : Bool}
  for +s: String
  for es: {short(s) == True{} : Bool}
  {own(T.parse(String.append(k, String.append(" = [", String.append(T.key.basic(s), "]\n")))))
    == T.Doc{"", [T.VPair{k, T.VArr{[T.VStr{s}]}}]} : T.Doc}

# LAW: and as an inline table's value: k = {v = key.basic(s)} and a newline
# parse with no error to one pair named k holding an inline table whose pair
# v holds s
# TOML-STR-1
law basic_string_reads_back_in_inline_table:
  for +k: String
  for ek: {T.bare(k) == True{} : Bool}
  for +s: String
  for es: {short(s) == True{} : Bool}
  {own(T.parse(String.append(k, String.append(" = {v = ", String.append(T.key.basic(s), "}\n")))))
    == T.Doc{"", [T.VPair{k, T.VInl{[T.VPair{"v", T.VStr{s}}]}}]} : T.Doc}

# WP-N: a scalar reads back as itself. render writes an integer, a float, a
# boolean and a datetime as a bare word. The scanner reads a bare word from the
# state that waits for a value, up to the character that ends it, and word.val
# classifies it. The laws below state the classification of what render
# writes, kind by kind, and the scan in premise form: from every value state,
# whatever else it holds, as the round trip's document induction uses it.

# the fields of a scanner state that a bare value does not decide
type Vf is Data:
  Vf{bad: String, rows: List<&2, T.Val>, heads: List<&2, String>, here: List<&2, String>,
    parts: List<&2, String>, back: T.Lex, qkind: T.QKind, stack: List<&2, T.Ctx>,
    uni: U32, left: U32, arrtab: Bool}

# the scanner with those fields, a buffer and a lex state, holding no
# character and past the first character of the text
def vst(fx: Vf, buf: List<&2, Char>, lex: T.Lex) -> T.St:
  match fx:
    case Vf{bad, rows, heads, here, parts, back, qkind, stack, uni, left, arrtab}:
      T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, T.HNone{}, uni,
        left, arrtab, False{}}

# whether those fields are inside an inline table
def vf.inl(fx: Vf) -> Bool:
  match fx:
    case Vf{_bad, _rows, _heads, _here, _parts, _back, _qkind, stack, _uni, _left, _arrtab}:
      T.inl.open(stack)

# a text read from the state that waits for a value
def from_val(fx: Vf, text: String) -> T.Doc:
  T.doc.read(text, T.MScan{vst(fx, [], T.LVal{})})

# the text after a value's newline, read on from the state that put the value
# where the state puts values
def after_val(+fx: Vf, vv: T.Val, rest: String) -> T.Doc:
  T.doc.read(rest, T.MScan{T.read.once2(T.bare.hold(T.val.take(vst(fx, [], T.LBare{}), vv), '\n',
    vf.inl(fx)))})

# a character a bare value keeps: no delimiter and no quote
def word.char(+cc: Char) -> Bool:
  Bool.and(Bool.not(T.ch.delim(cc)), Bool.not(Bool.or(Char.is_eq(cc, '"'), Char.is_eq(cc, '\''))))

# a character that starts a bare value: one it keeps, and no bracket or brace
def word.first(+cc: Char) -> Bool:
  Bool.and(word.char(cc), Bool.not(Bool.or(Char.is_eq(cc, '['), Char.is_eq(cc, '{'))))

# characters a bare value keeps
def word.rest(ss: String) -> Bool:
  match ss:
    case SNil{}:
      True{}
    case SCon{+hh, tt}:
      Bool.and(word.char(hh), word.rest(tt))

# a bare value: a character that starts one, then characters it keeps
def word.chars(ss: String) -> Bool:
  match ss:
    case SNil{}:
      False{}
    case SCon{+hh, tt}:
      Bool.and(word.first(hh), word.rest(tt))

# LAW: a bare value then a newline is read from every value state as the value
# word.val classifies it as, put where the state puts values, and the text
# after the newline is read on from there
law word_reads_back:
  for +v: T.Val
  for +s: String
  for +hc: {word.chars(s) == True{} : Bool}
  for hv: {T.word.val(String.to_list(s)) == T.GotVal{v} : T.Got}
  for +fx: Vf
  for +rest: String
  {from_val(fx, String.append(s, SCon{'\n', rest})) == after_val(fx, v, rest) : T.Doc}

# LAW: a boolean's text is classified as the boolean
law bool_word:
  for b: Bool
  {T.word.val(String.to_list(T.render.atom(T.VBool{b}))) == T.GotVal{T.VBool{b}} : T.Got}

# LAW: a boolean's text then a newline is read from every value state as the
# boolean
law bool_reads_back:
  for +b: Bool
  for +fx: Vf
  for +rest: String
  {from_val(fx, String.append(T.render.atom(T.VBool{b}), SCon{'\n', rest}))
    == after_val(fx, T.VBool{b}, rest) : T.Doc}
