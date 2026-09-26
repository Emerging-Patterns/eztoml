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

# The bound on a text's length. parse keeps a string render writes with no
# escape as a span of the text, whose length it counts in a U32, so the
# string must be short enough that the count does not wrap; TOML-RT-1 bounds
# the whole rendered text so.

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

# LAW: a well-formed integer's text is classified as its sign and its digits:
# render writes the sign (a minus only) and the digits, and the scan reads
# them back, a lone 0 and -0 as well as digits with no leading zero, up to the
# signed 64-bit bounds
# TOML-NUM-1
law int_word:
  for +sg: T.Sign
  for +ds: String
  for +w: {T.wf.int(sg, ds) == True{} : Bool}
  {T.word.val(String.to_list(T.render.atom(T.VInt{sg, ds}))) == T.GotVal{T.VInt{sg, ds}} : T.Got}

# LAW: a well-formed integer's text then a newline is read from every value
# state as the integer
law int_reads_back:
  for +sg: T.Sign
  for +ds: String
  for +w: {T.wf.int(sg, ds) == True{} : Bool}
  for +fx: Vf
  for +rest: String
  {from_val(fx, String.append(T.render.atom(T.VInt{sg, ds}), SCon{'\n', rest}))
    == after_val(fx, T.VInt{sg, ds}, rest) : T.Doc}

# LAW: a well-formed float's text is classified as its sign and its spelling:
# render writes the sign (a minus only) and the spelling, inf, nan, or
# toml.abnf's float with no sign and no underscore, and the scan reads them
# back with the spelling kept
# TOML-NUM-2
law flo_word:
  for +sg: T.Sign
  for +text: String
  for +w: {T.wf.flo(text) == True{} : Bool}
  {T.word.val(String.to_list(T.render.atom(T.VFlo{sg, text}))) == T.GotVal{T.VFlo{sg, text}} : T.Got}

# LAW: a well-formed float's text then a newline is read from every value
# state as the float
law flo_reads_back:
  for +sg: T.Sign
  for +text: String
  for +w: {T.wf.flo(text) == True{} : Bool}
  for +fx: Vf
  for +rest: String
  {from_val(fx, String.append(T.render.atom(T.VFlo{sg, text}), SCon{'\n', rest}))
    == after_val(fx, T.VFlo{sg, text}, rest) : T.Doc}

# LAW: a well-formed datetime's text is classified as the datetime: render
# writes the year with four digits and every other field with two, with T and
# Z in upper case and the fraction's digits kept, and the scan reads each field
# back, for all four forms
# TOML-TIME-1
law when_word:
  for +w: T.When
  for +h: {T.wf.when(w) == True{} : Bool}
  {T.word.val(String.to_list(T.render.atom(T.VWhen{w}))) == T.GotVal{T.VWhen{w}} : T.Got}

# LAW: a well-formed datetime's text then a newline is read from every value
# state as the datetime
law when_reads_back:
  for +w: T.When
  for +h: {T.wf.when(w) == True{} : Bool}
  for +fx: Vf
  for +rest: String
  {from_val(fx, String.append(T.render.atom(T.VWhen{w}), SCon{'\n', rest}))
    == after_val(fx, T.VWhen{w}, rest) : T.Doc}

# a well-formed scalar render writes as a bare value: an integer, a float, a
# boolean or a datetime
def bare_val(vv: T.Val) -> Bool:
  match vv:
    case T.VInt{+sg, +ds}:
      T.wf.int(sg, ds)
    case T.VFlo{_sg, +text}:
      T.wf.flo(text)
    case T.VBool{_b}:
      True{}
    case T.VWhen{ww}:
      T.wf.when(ww)
    case _:
      False{}

# LAW: every well-formed scalar render writes as a bare value, then a newline,
# is read from every value state as itself, put where the state puts values,
# and the text after the newline is read on from there
law scalar_reads_back:
  for +v: T.Val
  for +w: {bare_val(v) == True{} : Bool}
  for +fx: Vf
  for +rest: String
  {from_val(fx, String.append(T.render.atom(v), SCon{'\n', rest})) == after_val(fx, v, rest) : T.Doc}

# WP-K3: a key's name is its characters however it is written. A key segment
# is bare, a basic string (written as key writes one, escapes decoded) or a
# literal string (its characters as they are, no escapes); a dotted key is
# segments joined by dots, with blank space allowed around each dot; the
# segments of a header are spelled the same way. The laws below read each
# spelling back as its characters, put a dotted key's value under the nested
# tables its segments name, and find it with at.

# a character a literal string may hold: any but the apostrophe and the
# controls other than tab (toml.abnf literal-char)
def lit.char(+cc: Char) -> Bool:
  Bool.not(Bool.or(Char.is_eq(cc, '\''), Bool.and(is_ctl(cc), Bool.not(Char.is_eq(cc, '\t')))))

# a text a literal string may hold
def lit.text(ss: String) -> Bool:
  match ss:
    case SNil{}:
      True{}
    case SCon{+hh, tt}:
      Bool.and(lit.char(hh), lit.text(tt))

# LAW: a literal key reads back as its characters: for every text s a
# literal string can hold, 's' followed by " = 1" parses with no error to
# one pair, named s, holding the integer 1
# TOML-KEY-3
law literal_key_reads_back:
  for +s: String
  for e: {lit.text(s) == True{} : Bool}
  {T.parse(SCon{'\'', String.append(s, "' = 1")})
    == T.Doc{"", [T.VPair{s, T.VInt{T.Plus{}, "1"}}]} : T.Doc}

# how a key segment is spelled: bare, as a basic string the way key writes
# one, or as a literal string
type Spell is Data:
  SpBare{}
  SpBasic{}
  SpLit{}

# a key segment: a name and how it is spelled
type Seg is Data:
  Seg{sp: Spell, name: String}

# a segment of a dotted key that a dot follows, with the blank space before
# the dot and after it (each blank a tab when true, a space when false)
type Dot is Data:
  Dot{seg: Seg, g1: List<&2, Bool>, g2: List<&2, Bool>}

# blank space: a tab for each true, a space for each false
def gap(gs: List<&2, Bool>) -> String:
  match gs:
    case []:
      ""
    case tab <> rest:
      SCon{blank_char(tab), gap(rest)}

# a segment's text
def seg.text(sg: Seg) -> String:
  match sg:
    case Seg{SpBare{}, name}:
      name
    case Seg{SpBasic{}, name}:
      T.key.basic(name)
    case Seg{SpLit{}, name}:
      SCon{'\'', String.append(name, "'")}

# a segment's name
def seg.name(sg: Seg) -> String:
  match sg:
    case Seg{_sp, name}:
      name

# whether a segment's name can be spelled so: a bare name is a bare key, a
# literal one holds no apostrophe and no control but tab, and every name can
# be written as a basic string
def seg.ok(sg: Seg) -> Bool:
  match sg:
    case Seg{SpBare{}, name}:
      T.bare(name)
    case Seg{SpBasic{}, _name}:
      True{}
    case Seg{SpLit{}, name}:
      lit.text(name)

# the text of a dotted key, its segments joined by dots with their blank
# space, then tail
def dk.text(ds: List<&2, Dot>, last: Seg, tail: String) -> String:
  match ds:
    case []:
      String.append(seg.text(last), tail)
    case Dot{sg, g1, g2} <> rest:
      String.append(seg.text(sg), String.append(gap(g1), SCon{'.', String.append(gap(g2),
        dk.text(rest, last, tail))}))

# the names of a dotted key's segments, in order
def dk.names(ds: List<&2, Dot>, last: Seg) -> List<&2, String>:
  match ds:
    case []:
      [seg.name(last)]
    case Dot{sg, _g1, _g2} <> rest:
      seg.name(sg) <> dk.names(rest, last)

# whether every segment of a dotted key can be spelled as it is
def dk.ok(ds: List<&2, Dot>, last: Seg) -> Bool:
  match ds:
    case []:
      seg.ok(last)
    case Dot{sg, _g1, _g2} <> rest:
      Bool.and(seg.ok(sg), dk.ok(rest, last))

# the scanner after a key's `=`, waiting for its value in the table here:
# the key's segments in parts, newest first
def kb.val(
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  parts: List<&2, String>,
  back: T.Lex,
  qkind: T.QKind,
  arrtab: Bool
) -> T.St:
  T.St{"", rows, heads, here, parts, [], T.LVal{}, back, qkind, [], T.HNone{}, 0, 0, arrtab,
    False{}}

# LAW: a dotted key reads back as its segments' names: from the start of a
# line in any table, a key of segments each bare, basic or literal, joined
# by dots with blank space around them, then blank space and `=`, is the rest
# read waiting for the value with every segment's characters, escapes
# decoded, as the key's parts
# TOML-KEY-3
law dotted_key_reads_back:
  for +ds: List<&2, Dot>
  for +last: Seg
  for ok: {dk.ok(ds, last) == True{} : Bool}
  for +g: List<&2, Bool>
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +here: List<&2, String>
  for +back: T.Lex
  for +qkind: T.QKind
  for +arrtab: Bool
  for +rest: String
  for +goal: T.Doc
  for ih: @bk: T.Lex -> @qk: T.QKind -> {T.doc.read(rest, T.MScan{kb.val(rows, heads, here,
    List.reverse(&2, String, dk.names(ds, last)), bk, qk, arrtab)}) == goal : T.Doc}
  {T.doc.read(dk.text(ds, last, String.append(gap(g), SCon{'=', rest})), T.MScan{hb.line(rows,
    heads, here, back, qkind, arrtab)}) == goal : T.Doc}

# A key's value is put by a walk along the current table's path then the
# key's segments. The walk counts skip down past the current table's
# segments, which are navigation; once skip reaches zero each segment is a
# dotted key's, which may enter a table no header defined, or make a new
# implicit one, and records the table's path behind `.` (heads.by.dot) the
# first time. WP-W's walk_put_at_head is the case where skip never reaches
# zero.

# whether a dotted key's segment goes on through what its name refers to:
# nothing yet, or a table no header defined
def dk.can.dot(look: T.Look, heads: List<&2, String>, +path: String) -> Bool:
  match look:
    case T.KMiss{}:
      True{}
    case T.KHead{_p, _rows}:
      Bool.not(T.heads.head(heads, path))
    case _:
      False{}

# whether a walk step goes on: navigation when zz is false, a dotted key's
# segment when it is true
def dk.can(zz: Bool, look: T.Look, heads: List<&2, String>, +path: String) -> Bool:
  match zz:
    case False{}:
      tb.can(look)
    case True{}:
      dk.can.dot(look, heads, path)

# a table's path recorded behind `.`, unless it is recorded already
def dk.mark.new(seen: Bool, path: String, heads: List<&2, String>) -> List<&2, String>:
  match seen:
    case True{}:
      heads
    case False{}:
      SCon{'.', path} <> heads

# the definitions after a walk step: navigation records none, a dotted key's
# segment records its table's path behind `.` unless it is recorded already
def dk.mark(zz: Bool, +path: String, +heads: List<&2, String>) -> List<&2, String>:
  match zz:
    case False{}:
      heads
    case True{}:
      dk.mark.new(T.heads.has(heads, path), path, heads)

# whether a put's walk goes on through every segment of the path, from the
# table pre names, with the definitions heads and the count skip
def dk.open(
  path: List<&2, String>,
  +pre: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +skip: U32
) -> Bool:
  match path:
    case []:
      True{}
    case +seg <> rest:
      Bool.and(dk.can(U32.is_zero(skip), T.rows.look(rows, seg), heads, T.tree.pre(pre, seg)),
        dk.open(rest, T.tree.pre(pre, seg), tb.into(T.rows.look(rows, seg)),
          dk.mark(U32.is_zero(skip), T.tree.pre(pre, seg), heads), T.path.dec(skip)))

# the definitions after a put's walk along the path
def dk.heads(
  path: List<&2, String>,
  +pre: String,
  +heads: List<&2, String>,
  +skip: U32
) -> List<&2, String>:
  match path:
    case []:
      heads
    case +seg <> rest:
      dk.heads(rest, T.tree.pre(pre, seg), dk.mark(U32.is_zero(skip), T.tree.pre(pre, seg), heads),
        T.path.dec(skip))

# the names of the segments a dot follows
def dk.init(ds: List<&2, Dot>) -> List<&2, String>:
  match ds:
    case []:
      []
    case Dot{sg, _g1, _g2} <> rest:
      seg.name(sg) <> dk.init(rest)

# the integer 1, the value the key/value laws below read
def one() -> T.Val:
  T.VInt{T.Plus{}, "1"}

# LAW: a value put along a path the walk goes on through, navigation then a
# dotted key's segments, to a name the table at its end does not hold, goes at
# the head of that table's rows; every table on the way is entered or made
# under its segment's name, and each table a dotted key's segment reached is
# recorded as defined by dotted keys. This is walk_put_at_head with skip
# allowed to reach zero
# TOML-KEY-3
law dotted_put_at_head:
  for +path: List<&2, String>
  for +k: String
  for +v: T.Val
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +skip: U32
  for +inl: Bool
  for +eo: {dk.open(path, "", rows, heads, skip) == True{} : Bool}
  for em: {T.get(tb.rows(path, rows), k) == T.Miss{} : T.Hit}
  {T.tree.walk(List.append(&2, String, path, [k]), T.Tw{rows, T.JPut{v}, [], "", "", heads, inl}, skip)
    == T.End{tb.set(path, "", rows, T.VPair{k, v} <> tb.rows(path, rows)), "",
      dk.heads(path, "", heads, skip)} : T.End}

# LAW: a key/value line of a dotted key, spelled any way, and the value 1,
# read from the start of a line in the table here, is the rest read from the
# start of the next line with the rows and definitions the put's walk along
# here and the segments' names returns
# TOML-KEY-3
law dotted_key_pair_reads_back:
  for +ds: List<&2, Dot>
  for +last: Seg
  for ok: {dk.ok(ds, last) == True{} : Bool}
  for +g: List<&2, Bool>
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +here: List<&2, String>
  for +back: T.Lex
  for +qkind: T.QKind
  for +arrtab: Bool
  for +rows2: List<&2, T.Val>
  for +heads2: List<&2, String>
  for ew: {T.tree.walk(List.append(&2, String, here, dk.names(ds, last)), T.Tw{rows, T.JPut{one()}, [],
    "", "", heads, False{}}, T.path.len(here, 0)) == T.End{rows2, "", heads2} : T.End}
  for +rest: String
  for +goal: T.Doc
  for ih: @bk: T.Lex -> @qk: T.QKind -> {T.doc.read(rest, T.MScan{hb.line(rows2, heads2, here, bk, qk,
    arrtab)}) == goal : T.Doc}
  {T.doc.read(dk.text(ds, last, String.append(gap(g), String.append("= 1\n", rest))),
    T.MScan{hb.line(rows, heads, here, back, qkind, arrtab)}) == goal : T.Doc}

# LAW: and when the walk goes on through the current table and every segment
# before the last, and the table there does not hold the last name, the line
# puts the value at the head of that table's rows, under the last name's
# characters, in nested tables named by the other segments' characters
# (dotted_put_at_head)
# TOML-KEY-3
law dotted_key_pair_puts_value:
  for +ds: List<&2, Dot>
  for +last: Seg
  for ok: {dk.ok(ds, last) == True{} : Bool}
  for +g: List<&2, Bool>
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +here: List<&2, String>
  for +eo: {dk.open(List.append(&2, String, here, dk.init(ds)), "", rows, heads, T.path.len(here, 0))
    == True{} : Bool}
  for em: {T.get(tb.rows(List.append(&2, String, here, dk.init(ds)), rows), seg.name(last)) == T.Miss{}
    : T.Hit}
  for +back: T.Lex
  for +qkind: T.QKind
  for +arrtab: Bool
  for +rest: String
  for +goal: T.Doc
  for ih: @bk: T.Lex -> @qk: T.QKind -> {T.doc.read(rest, T.MScan{hb.line(tb.set(List.append(&2, String,
    here, dk.init(ds)), "", rows, T.VPair{seg.name(last), one()} <> tb.rows(List.append(&2, String, here,
    dk.init(ds)), rows)), dk.heads(List.append(&2, String, here, dk.init(ds)), "", heads, T.path.len(here,
    0)), here, bk, qk, arrtab)}) == goal : T.Doc}
  {T.doc.read(dk.text(ds, last, String.append(gap(g), String.append("= 1\n", rest))),
    T.MScan{hb.line(rows, heads, here, back, qkind, arrtab)}) == goal : T.Doc}

# LAW: a document of one key/value line, a dotted key spelled any way and the
# value 1, parses with no error to the value under the last name's
# characters, in nested tables named by the other segments' characters
# TOML-KEY-3
law dotted_key_line_reads_back:
  for +ds: List<&2, Dot>
  for +last: Seg
  for +ok: {dk.ok(ds, last) == True{} : Bool}
  for +g: List<&2, Bool>
  {T.parse(dk.text(ds, last, String.append(gap(g), "= 1\n")))
    == T.Doc{"", T.rows.seal(tb.set(dk.init(ds), "", [], [T.VPair{seg.name(last), one()}]))} : T.Doc}

# LAW: and at finds the value by the segments' names: a key's name is its
# characters however it was written
# TOML-KEY-3
law dotted_key_line_found_by_at:
  for +ds: List<&2, Dot>
  for +last: Seg
  for ok: {dk.ok(ds, last) == True{} : Bool}
  for +g: List<&2, Bool>
  {T.at(T.root(T.parse(dk.text(ds, last, String.append(gap(g), "= 1\n")))), dk.names(ds, last))
    == T.Found{one()} : T.Hit}

# A header's segments are spelled the same way, bare, basic or literal, and
# joined the same way, by dots with blank space around them, with blank
# space allowed after the opening bracket and before the closing one. WP-H's
# header_reads_back reads the segments as key writes them; the laws below
# read every spelling.

# a header line: `[` (`[[` for an array of tables), blank space, a dotted
# key's text, blank space, `]` (`]]`), a newline, then rest
def hd.line(
  arr: Bool,
  g0: List<&2, Bool>,
  ds: List<&2, Dot>,
  last: Seg,
  g9: List<&2, Bool>,
  rest: String
) -> String:
  match arr:
    case False{}:
      SCon{'[', String.append(gap(g0), dk.text(ds, last, String.append(gap(g9), SCon{']', SCon{'\n', rest}})))}
    case True{}:
      SCon{'[', SCon{'[', String.append(gap(g0), dk.text(ds, last, String.append(gap(g9), SCon{']', SCon{']',
        SCon{'\n', rest}}})))}}

# the path a header names: its segments' names, the last one last
def hd.path(ds: List<&2, Dot>, last: Seg) -> List<&2, String>:
  List.append(&2, String, dk.init(ds), [seg.name(last)])

# LAW: a header line whose segments are each bare, basic or literal, with
# blank space around its dots and inside its brackets, read from the start of
# a line, is the rest read from the start of the next line in the table named
# by the segments' characters, escapes decoded, with the rows and definitions
# the header's walk along those names returns; for a `[table]` header and an
# `[[array]]` one alike
# TOML-KEY-3
law header_segments_read_back:
  for +arr: Bool
  for +g0: List<&2, Bool>
  for +ds: List<&2, Dot>
  for +last: Seg
  for ok: {dk.ok(ds, last) == True{} : Bool}
  for +g9: List<&2, Bool>
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +here: List<&2, String>
  for +back: T.Lex
  for +qkind: T.QKind
  for +arrtab: Bool
  for +rows2: List<&2, T.Val>
  for +heads2: List<&2, String>
  for ew: {T.tree.walk(hd.path(ds, last), T.Tw{rows, header_job(arr), [], "", "", heads, False{}}, 0)
    == T.End{rows2, "", heads2} : T.End}
  for +rest: String
  for +goal: T.Doc
  for ih: @bk: T.Lex -> @qk: T.QKind -> {T.doc.read(rest, T.MScan{hb.line(rows2, heads2, hd.path(ds, last), bk,
    qk, False{})}) == goal : T.Doc}
  {T.doc.read(hd.line(arr, g0, ds, last, g9, rest), T.MScan{hb.line(rows, heads, here, back, qkind, arrtab)})
    == goal : T.Doc}

# LAW: a document of one `[table]` header, its segments spelled any way,
# parses with no error to an empty table under the last name's characters,
# in nested tables named by the other segments' characters
# TOML-KEY-3
law header_line_reads_back:
  for +g0: List<&2, Bool>
  for +ds: List<&2, Dot>
  for +last: Seg
  for +ok: {dk.ok(ds, last) == True{} : Bool}
  for +g9: List<&2, Bool>
  {T.parse(hd.line(False{}, g0, ds, last, g9, "")) == T.Doc{"", T.rows.seal(tb.set(dk.init(ds), "", [],
    [T.VPair{seg.name(last), T.VHead{T.tree.pre(tb.join(dk.init(ds), ""), seg.name(last)), []}}]))} : T.Doc}

# LAW: and at finds that table by the segments' names
# TOML-KEY-3
law header_line_found_by_at:
  for +g0: List<&2, Bool>
  for +ds: List<&2, Dot>
  for +last: Seg
  for ok: {dk.ok(ds, last) == True{} : Bool}
  for +g9: List<&2, Bool>
  {T.at(T.root(T.parse(hd.line(False{}, g0, ds, last, g9, ""))), hd.path(ds, last))
    == T.Found{T.VHead{T.tree.pre(tb.join(dk.init(ds), ""), seg.name(last)), []}} : T.Hit}

# WP-C: arrays and inline tables read back. render writes an array as `[`,
# its items joined by ", " and `]`, and an inline table as `{`, its pairs
# `key = value` joined by ", " and `}`, nested to any depth. The scanner reads
# such a value from the state that waits for a value up to the character
# after it, which ends it: a newline at the top level, a comma or a closer
# inside a container. The value it puts is in the raw form below: a string a
# span or an owned string, an array's items in order, an inline table's pairs
# newest first until rows.seal; own reads it as cv.raw says.

# a text that starts with a character that may end a value: a newline, a
# comma, or a closer
def cv.end(rest: String) -> Bool:
  match rest:
    case SNil{}:
      False{}
    case SCon{+cc, _tt}:
      Bool.or(Char.is_eq(cc, '\n'), Bool.or(Char.is_eq(cc, ','), Bool.or(Char.is_eq(cc, ']'),
        Char.is_eq(cc, '}'))))

# one value with every span read out, as own.rows reads the head of a list
def cv.own1(vv: T.Val) -> T.Val:
  match vv:
    case T.VPair{nn, T.VSpan{src, +kk}}:
      T.VPair{nn, T.VStr{T.span.str(src, kk, U32.is_zero(kk))}}
    case T.VPair{nn, T.VArr{items}}:
      T.VPair{nn, T.VArr{own.rows(items)}}
    case T.VPair{nn, T.VInl{rows}}:
      T.VPair{nn, T.VInl{own.rows(rows)}}
    case T.VPair{nn, T.VHead{path, rows}}:
      T.VPair{nn, T.VHead{path, own.rows(rows)}}
    case T.VPair{nn, T.VAot{path, rows}}:
      T.VPair{nn, T.VAot{path, own.rows(rows)}}
    case T.VPair{nn, T.VAots{path, elems}}:
      T.VPair{nn, T.VAots{path, own.rows(elems)}}
    case T.VSpan{src, +kk}:
      T.VStr{T.span.str(src, kk, U32.is_zero(kk))}
    case T.VArr{items}:
      T.VArr{own.rows(items)}
    case T.VInl{rows}:
      T.VInl{own.rows(rows)}
    case T.VHead{path, rows}:
      T.VHead{path, own.rows(rows)}
    case T.VAot{path, rows}:
      T.VAot{path, own.rows(rows)}
    case T.VAots{path, elems}:
      T.VAots{path, own.rows(elems)}
    case other:
      other

# values as the scanner puts them, every span read out: strings owned, an
# array's items in order, an inline table's pairs newest first
def cv.raw(vs: List<&2, T.Val>) -> List<&2, T.Val>:
  match vs:
    case []:
      []
    case T.VPair{nn, T.VSpan{src, +kk}} <> tt:
      T.VPair{nn, T.VStr{T.span.str(src, kk, U32.is_zero(kk))}} <> cv.raw(tt)
    case T.VPair{nn, T.VArr{items}} <> tt:
      T.VPair{nn, T.VArr{cv.raw(items)}} <> cv.raw(tt)
    case T.VPair{nn, T.VInl{rows}} <> tt:
      T.VPair{nn, T.VInl{List.reverse(&2, T.Val, cv.raw(rows))}} <> cv.raw(tt)
    case T.VSpan{src, +kk} <> tt:
      T.VStr{T.span.str(src, kk, U32.is_zero(kk))} <> cv.raw(tt)
    case T.VArr{items} <> tt:
      T.VArr{cv.raw(items)} <> cv.raw(tt)
    case T.VInl{rows} <> tt:
      T.VInl{List.reverse(&2, T.Val, cv.raw(rows))} <> cv.raw(tt)
    case vv <> tt:
      vv <> cv.raw(tt)

# one value as the scanner puts it, as cv.raw reads the head of a list
def cv.raw1(vv: T.Val) -> T.Val:
  match vv:
    case T.VPair{nn, T.VSpan{src, +kk}}:
      T.VPair{nn, T.VStr{T.span.str(src, kk, U32.is_zero(kk))}}
    case T.VPair{nn, T.VArr{items}}:
      T.VPair{nn, T.VArr{cv.raw(items)}}
    case T.VPair{nn, T.VInl{rows}}:
      T.VPair{nn, T.VInl{List.reverse(&2, T.Val, cv.raw(rows))}}
    case T.VSpan{src, +kk}:
      T.VStr{T.span.str(src, kk, U32.is_zero(kk))}
    case T.VArr{items}:
      T.VArr{cv.raw(items)}
    case T.VInl{rows}:
      T.VInl{List.reverse(&2, T.Val, cv.raw(rows))}
    case other:
      other

# the text render writes for a value in a value position, then xx: an array's
# items joined by ", " in brackets, an inline table's pairs joined by ", " in
# braces, or a scalar's text
def cv.tx(vv: T.Val, xx: String) -> String:
  match vv:
    case T.VArr{items}:
      SCon{'[', String.append(T.render.go(items, ", ", False{}), SCon{']', xx})}
    case T.VInl{rows}:
      SCon{'{', String.append(T.render.go(rows, ", ", False{}), SCon{'}', xx})}
    case other:
      String.append(T.render.atom(other), xx)

# a value that may sit in a value position, well-formed as wf.go reads an
# array's item or a pair's value: an array of well-formed items, an inline
# table of well-formed pairs, or a well-formed scalar
def cv.wf(vv: T.Val) -> Bool:
  match vv:
    case T.VArr{items}:
      T.wf.go(items, T.WfItems{})
    case T.VInl{rows}:
      T.wf.go(rows, T.WfInl{})
    case other:
      T.wf.atom(other)

# every string in the values, at any depth, is short: a span counts its
# characters in a U32
def cv.shorts(vs: List<&2, T.Val>) -> Bool:
  match vs:
    case []:
      True{}
    case T.VPair{_nn, T.VStr{ss}} <> tt:
      Bool.and(short(ss), cv.shorts(tt))
    case T.VPair{_nn, T.VSpan{src, +kk}} <> tt:
      Bool.and(short(T.span.str(src, kk, U32.is_zero(kk))), cv.shorts(tt))
    case T.VPair{_nn, T.VArr{items}} <> tt:
      Bool.and(cv.shorts(items), cv.shorts(tt))
    case T.VPair{_nn, T.VInl{rows}} <> tt:
      Bool.and(cv.shorts(rows), cv.shorts(tt))
    case T.VStr{ss} <> tt:
      Bool.and(short(ss), cv.shorts(tt))
    case T.VSpan{src, +kk} <> tt:
      Bool.and(short(T.span.str(src, kk, U32.is_zero(kk))), cv.shorts(tt))
    case T.VArr{items} <> tt:
      Bool.and(cv.shorts(items), cv.shorts(tt))
    case T.VInl{rows} <> tt:
      Bool.and(cv.shorts(rows), cv.shorts(tt))
    case _vv <> tt:
      cv.shorts(tt)

# every string in one value, at any depth, is short
def cv.short1(vv: T.Val) -> Bool:
  match vv:
    case T.VStr{ss}:
      short(ss)
    case T.VSpan{src, +kk}:
      short(T.span.str(src, kk, U32.is_zero(kk)))
    case T.VArr{items}:
      cv.shorts(items)
    case T.VInl{rows}:
      cv.shorts(rows)
    case _vv:
      True{}

# the scanner waiting for a value, with no error and nothing buffered, the
# fields a value does not decide left as parameters
def vpos(
  rw: List<&2, T.Val>,
  hs: List<&2, String>,
  he: List<&2, String>,
  ps: List<&2, String>,
  bk: T.Lex,
  qk: T.QKind,
  sk: List<&2, T.Ctx>,
  un: U32,
  lf: U32,
  ab: Bool
) -> T.St:
  T.St{"", rw, hs, he, ps, [], T.LVal{}, bk, qk, sk, T.HNone{}, un, lf, ab, False{}}

# the rest of the walk once a value ww is read: from the state with a value
# put where the stack puts values, one that own reads as the scanner's form
# of ww, and whatever back, qkind, uni and left the value leaves, the rest of
# the text gives a document PP holds of
def vrest(
  +ww: T.Val,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  @vv: T.Val -> @bk: T.Lex -> @qk: T.QKind -> @un: U32 -> @lf: U32 ->
    {cv.own1(vv) == cv.raw1(ww) : T.Val} ->
    PP(T.doc.read(rest, T.MScan{T.take.top(sk, vv, "", rw, hs, he, ps, bk, qk, un, lf, ab, False{})}))

# LAW: a value render writes in a value position reads back: from every
# state that waits for a value, the text of a well-formed value whose strings
# are short (a scalar, a string, or an array or an inline table nested to any
# depth), then a character that ends a value and any rest, reads on as the
# rest from the state with the value put, in the scanner's form, whatever the
# value leaves in back, qkind, uni and left. PP is what the caller proves of
# the document
law value_reads_back:
  for +v: T.Val
  for hw: {cv.wf(v) == True{} : Bool}
  for hl: {cv.short1(v) == True{} : Bool}
  for +rw: List<&2, T.Val>
  for +hs: List<&2, String>
  for +he: List<&2, String>
  for +ps: List<&2, String>
  for +bk: T.Lex
  for +qk: T.QKind
  for +sk: List<&2, T.Ctx>
  for +un: U32
  for +lf: U32
  for +ab: Bool
  for +rest: String
  for hn: {cv.end(rest) == True{} : Bool}
  for -PP: T.Doc -> Type
  for ih: vrest(v, rw, hs, he, ps, sk, ab, rest, PP)
  PP(T.doc.read(cv.tx(v, rest), T.MScan{vpos(rw, hs, he, ps, bk, qk, sk, un, lf, ab)}))

# LAW: in any table, the pass that writes keys writes a pair of a value that
# may sit in a value position as its key, " = " and the value's text, then
# the separator and the rest
law pass_value:
  for +k: String
  for +v: T.Val
  for hw: {cv.wf(v) == True{} : Bool}
  for +rest: List<&2, T.Val>
  for +gap: String
  for +trail: Bool
  {T.render.pass(T.VPair{k, v} <> rest, gap, trail, False{}) == String.append(T.key(k), SCon{' ', SCon{'=',
    SCon{' ', cv.tx(v, String.append(T.render.suf(gap, trail, List.is_empty(&2, T.Val, rest)),
    T.render.pass(rest, gap, trail, False{})))}}}) : String}

# LAW: a document of one pair, a bare key and a value that is no table (a
# scalar, a string, or an array or an inline table nested to any depth),
# well-formed and with every string in it shorter than 2^32 characters, reads
# back with no error as the same document
# TOML-RT-1
law render_parse_value_pair:
  for +e: String
  for +k: String
  for +ek: {T.bare(k) == True{} : Bool}
  for +v: T.Val
  for w: {T.wf(T.Doc{e, [T.VPair{k, v}]}) == True{} : Bool}
  for +hv: {cv.wf(v) == True{} : Bool}
  for hl: {cv.short1(v) == True{} : Bool}
  {Bool.and(String.is_empty(T.bad(T.parse(T.render(T.Doc{e, [T.VPair{k, v}]})))),
    same(T.parse(T.render(T.Doc{e, [T.VPair{k, v}]})), T.Doc{e, [T.VPair{k, v}]})) == True{} : Bool}

# WP-R3: TOML-RT-3's invariant. parse keeps the root's rows newest first and
# seals them at the end; wf.go read on those rows as they are, newest first,
# is the invariant for the tables, because a pair the walk adds goes in front
# of the pairs it must not repeat. A state is good when what it has built can
# only seal into a well-formed document: its rows and open frames while it has
# not failed, and always the key segments, the buffer and a held character,
# which hold Unicode scalar values. A failed state is good whatever it holds:
# parse then returns an error, and TOML-RT-3 says nothing of it.

# the rest when the scanner has not failed, and True once it has
def gd.ifok(ok: Bool, rest: Bool) -> Bool:
  match ok:
    case True{}:
      rest
    case False{}:
      True{}

# every character is a Unicode scalar value
def gd.cs(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      True{}
    case +h <> t:
      Bool.and(T.wf.char(h), gd.cs(t))

# every segment's characters are Unicode scalar values
def gd.segs(xs: List<&2, String>) -> Bool:
  match xs:
    case []:
      True{}
    case h <> t:
      Bool.and(T.wf.text(h), gd.segs(t))

# a held character is a Unicode scalar value
def gd.hold(hh: T.Hold) -> Bool:
  match hh:
    case T.HNone{}:
      True{}
    case T.HChar{+c}:
      T.wf.char(c)

# no array of tables, in these rows or the tables under them
def gd.na(rows: List<&2, T.Val>) -> Bool:
  match rows:
    case []:
      True{}
    case T.VPair{_n, T.VHead{_p, sub}} <> t:
      Bool.and(gd.na(sub), gd.na(t))
    case T.VPair{_n, T.VAots{_p, _e}} <> _t:
      False{}
    case _ <> t:
      gd.na(t)

# the rows of an open inline table: its dotted keys walk from "" as a root's
# do, so they are well-formed as a root's rows with no array of tables; the
# tables they made become inline tables when it closes
def gd.inl(+rows: List<&2, T.Val>) -> Bool:
  Bool.and(T.wf.go(rows, T.WfRows{""}), gd.na(rows))

# what the open arrays and inline tables have built
def gd.vals(stack: List<&2, T.Ctx>) -> Bool:
  match stack:
    case []:
      True{}
    case T.CArr{items, _p, _h} <> t:
      Bool.and(T.wf.go(items, T.WfItems{}), gd.vals(t))
    case T.CInl{rows, _p, _h} <> t:
      Bool.and(gd.inl(rows), gd.vals(t))

# the keys the open arrays and inline tables saved
def gd.keys(stack: List<&2, T.Ctx>) -> Bool:
  match stack:
    case []:
      True{}
    case T.CArr{_i, parts, here} <> t:
      Bool.and(gd.segs(parts), Bool.and(gd.segs(here), gd.keys(t)))
    case T.CInl{_r, parts, here} <> t:
      Bool.and(gd.segs(parts), Bool.and(gd.segs(here), gd.keys(t)))

# the tables a state has built, while it has not failed
def gd.tr(+bad: String, rows: List<&2, T.Val>, stack: List<&2, T.Ctx>) -> Bool:
  gd.ifok(String.is_empty(bad), Bool.and(T.wf.go(rows, T.WfRows{""}), gd.vals(stack)))

# the characters a state holds: the current table's path, the key's segments,
# the buffer, the saved keys and a held character
def gd.lx(
  here: List<&2, String>,
  parts: List<&2, String>,
  buf: List<&2, Char>,
  stack: List<&2, T.Ctx>,
  hold: T.Hold
) -> Bool:
  Bool.and(gd.segs(here), Bool.and(gd.segs(parts), Bool.and(gd.cs(buf),
    Bool.and(gd.keys(stack), gd.hold(hold)))))

# TOML-RT-3's invariant over every scanner state
def good(st: T.St) -> Bool:
  match st:
    case T.St{+bad, rows, _heads, here, parts, buf, _lex, _back, _q, +stack, hold, _uni,
      _left, _arr, _lead}:
      Bool.and(gd.tr(bad, rows, stack), gd.lx(here, parts, buf, stack, hold))

# the root after a walk, while the walk has not failed
def gd.end(end: T.End) -> Bool:
  match end:
    case T.End{vs, +bad, _h}:
      gd.ifok(String.is_empty(bad), T.wf.go(vs, T.WfRows{""}))

# a value a key's walk may put: no table, well-formed where a pair holds it
def gd.vok(vv: T.Val) -> Bool:
  match vv:
    case T.VHead{_p, _r}:
      False{}
    case T.VAots{_p, _e}:
      False{}
    case T.VArr{items}:
      T.wf.go(items, T.WfItems{})
    case T.VInl{rows}:
      T.wf.go(rows, T.WfInl{})
    case other:
      T.wf.atom(other)

# what a walk is asked to do: put a value a key may hold, or open a table
def gd.job(job: T.Job) -> Bool:
  match job:
    case T.JPut{vv}:
      gd.vok(vv)
    case _:
      True{}

# the scanner's states inside a header
def gd.hd(lex: T.Lex) -> Bool:
  match lex:
    case T.LHead{}:
      True{}
    case T.LHeadGap{}:
      True{}
    case T.LHeadDot{}:
      True{}
    case T.LHeadQ{}:
      True{}
    case T.LHeadE{}:
      True{}
    case T.LHeadU{}:
      True{}
    case T.LHeadR{}:
      True{}
    case _:
      False{}

# LAW: a state that has read nothing of a key, a value or a header, with
# well-formed rows and a current table named by scalar values, is good,
# whatever its other fields; the scanner's start is one
# TOML-RT-3
law gd_start:
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +here: List<&2, String>
  for +lex: T.Lex
  for +back: T.Lex
  for +qkind: T.QKind
  for +uni: U32
  for +left: U32
  for +arrtab: Bool
  for +lead: Bool
  for ew: {T.wf.go(rows, T.WfRows{""}) == True{} : Bool}
  for eh: {gd.segs(here) == True{} : Bool}
  {good(T.St{"", rows, heads, here, [], [], lex, back, qkind, [], T.HNone{}, uni, left, arrtab,
    lead}) == True{} : Bool}

# LAW: a walk from the root keeps the rows well-formed: along any path of
# scalar-value segments, with any job that puts no table and a value
# well-formed where a pair holds it, from rows that are well-formed newest
# first, the root it returns is well-formed unless the walk failed
# TOML-RT-3
law gd_walk:
  for path: List<&2, String>
  for +rows: List<&2, T.Val>
  for +job: T.Job
  for +bad: String
  for +heads: List<&2, String>
  for +inl: Bool
  for +skip: U32
  for ew: {gd.ifok(String.is_empty(bad), T.wf.go(rows, T.WfRows{""})) == True{} : Bool}
  for ep: {gd.segs(path) == True{} : Bool}
  for ej: {gd.job(job) == True{} : Bool}
  {gd.end(T.tree.walk(path, T.Tw{rows, job, [], bad, "", heads, inl}, skip)) == True{} : Bool}

# LAW: every step inside a header keeps a state good: from every good state,
# whatever its fields, one character that is a Unicode scalar value read in
# any of the seven header states leaves a good state
# TOML-RT-3
law gd_header_steps:
  for +lex: T.Lex
  for hl: {gd.hd(lex) == True{} : Bool}
  for +st: T.St
  for eg: {good(st) == True{} : Bool}
  for +cc: Char
  for ec: {T.wf.char(cc) == True{} : Bool}
  {good(T.read.on(lex, st, cc)) == True{} : Bool}

# the scanner's states inside a key, before its `=`, and at the start and
# the end of a line
def gd.ky(lex: T.Lex) -> Bool:
  match lex:
    case T.LTop{}:
      True{}
    case T.LLine{}:
      True{}
    case T.LKey{}:
      True{}
    case T.LKeyDot{}:
      True{}
    case T.LAfter{}:
      True{}
    case T.LKeyQ{}:
      True{}
    case T.LKeyE{}:
      True{}
    case T.LKeyU{}:
      True{}
    case _:
      False{}

# LAW: every step at the start of a line, inside a key or after it keeps a
# state good: from every good state, whatever its fields, one character that
# is a Unicode scalar value read in any of the eight key states leaves a good
# state
# TOML-RT-3
law gd_key_steps:
  for +lex: T.Lex
  for hl: {gd.ky(lex) == True{} : Bool}
  for +st: T.St
  for eg: {good(st) == True{} : Bool}
  for +cc: Char
  for ec: {T.wf.char(cc) == True{} : Bool}
  {good(T.read.on(lex, st, cc)) == True{} : Bool}

# LAW: sealing keeps rows well-formed wherever they sit: rows well-formed
# newest first, as the scanner builds them, are well-formed once rows.seal
# has put every table back in the order it was written. A table's names are
# fresh against the pairs before them exactly when they are against the pairs
# after, so the reversal keeps them apart
# TOML-RT-3
law gd_seal:
  for +rows: List<&2, T.Val>
  for +at: T.WfAt
  for ew: {T.wf.go(rows, at) == True{} : Bool}
  {T.wf.go(T.rows.seal(rows), at) == True{} : Bool}

# LAW: a good state that ends the text gives a well-formed document whenever
# it gives no error: the document's rows are the state's, sealed
# TOML-RT-3
law gd_fin:
  for +st: T.St
  for eg: {good(st) == True{} : Bool}
  for eo: {String.is_empty(T.bad(T.read.fin.doc(st))) == True{} : Bool}
  {T.wf(T.read.fin.doc(st)) == True{} : Bool}

# a value a key may hold, unless the scanner has failed
def gd.okv(st: T.St, val: T.Val) -> Bool:
  match st:
    case T.St{+bad, _rows, _heads, _here, _parts, _buf, _lex, _back, _q, _stack, _hold, _uni, _left, _arr,
      _lead}:
      gd.ifok(String.is_empty(bad), gd.vok(val))

# LAW: placing a finished value keeps a state good: from every good state,
# whatever its fields, a value a key may hold (no table, well-formed where a
# pair holds it) put where the state is (the root through its key's walk, an
# array in front of its items, an inline table through its key's walk) leaves
# a good state; once the scanner has failed, any value does
# TOML-RT-3
law gd_take:
  for +st: T.St
  for eg: {good(st) == True{} : Bool}
  for +val: T.Val
  for ev: {gd.okv(st, val) == True{} : Bool}
  {good(T.val.take(st, val)) == True{} : Bool}

# the value states whose steps need no bare word read: a value's start,
# strings, comments, arrays, inline tables and the failed state
def gd.vl(lex: T.Lex) -> Bool:
  match lex:
    case T.LVal{}:
      True{}
    case T.LQ{}:
      True{}
    case T.LQ2{}:
      True{}
    case T.LStr{}:
      True{}
    case T.LEsc{}:
      True{}
    case T.LUni{}:
      True{}
    case T.LFold{}:
      True{}
    case T.LMq{}:
      True{}
    case T.LMqEnd{}:
      True{}
    case T.LTrim{}:
      True{}
    case T.LTrim2{}:
      True{}
    case T.LCom{}:
      True{}
    case T.LSink{}:
      True{}
    case T.LArr{}:
      True{}
    case T.LArrC{}:
      True{}
    case T.LInl{}:
      True{}
    case T.LInlK{}:
      True{}
    case T.LInlC{}:
      True{}
    case _:
      False{}

# LAW: every step in a value, other than one that ends a bare word, keeps a
# state good: from every good state, whatever its fields, one character that
# is a Unicode scalar value read in any of the eighteen states of a value's
# start, a string, a comment, an array, an inline table or the failed state
# leaves a good state
# TOML-RT-3
law gd_value_steps:
  for +lex: T.Lex
  for hl: {gd.vl(lex) == True{} : Bool}
  for +st: T.St
  for eg: {good(st) == True{} : Bool}
  for +cc: Char
  for ec: {T.wf.char(cc) == True{} : Bool}
  {good(T.read.on(lex, st, cc)) == True{} : Bool}


# WP-D: the document render writes, read back. render writes a table's pairs
# that are no table first, in order, then its tables and arrays of tables, in
# order, each one's rows the same way; parse puts every pair in the order it
# reads it and reads a span out only when own asks. canon is the document so
# reordered, with every span read out and no error: an element of an array of
# tables under the array's path, as the walk stores it.

# a table's pairs that are no table and no array of tables, in order
def canon.keys(xs: List<&2, T.Val>) -> List<&2, T.Val>:
  match xs:
    case []:
      []
    case T.VPair{_n, T.VHead{_p, _r}} <> tt:
      canon.keys(tt)
    case T.VPair{_n, T.VAots{_p, _es}} <> tt:
      canon.keys(tt)
    case hh <> tt:
      hh <> canon.keys(tt)

# which list canon.go reorders: a table's rows, or the elements of an array
# of tables stored under path
type CMode is Data:
  CTabs{}
  CElems{path: String}

# a table's tables and arrays of tables, in order, each one's rows reordered;
# or an array's elements, each under the array's path with its rows reordered
def canon.go(xs: List<&2, T.Val>, md: CMode) -> List<&2, T.Val>:
  match xs md:
    case [] _m:
      []
    case T.VPair{nn, T.VHead{pp, +rr}} <> tt CTabs{}:
      T.VPair{nn, T.VHead{pp, List.append(&2, T.Val, canon.keys(rr), canon.go(rr, CTabs{}))}} <>
        canon.go(tt, CTabs{})
    case T.VPair{nn, T.VAots{+pp, es}} <> tt CTabs{}:
      T.VPair{nn, T.VAots{pp, canon.go(es, CElems{pp})}} <> canon.go(tt, CTabs{})
    case T.VAot{_q, +rr} <> tt CElems{+pp}:
      T.VAot{pp, List.append(&2, T.Val, canon.keys(rr), canon.go(rr, CTabs{}))} <> canon.go(tt, CElems{pp})
    case _hh <> tt m2:
      canon.go(tt, m2)

# a table's tables and arrays of tables, reordered
def canon.tabs(xs: List<&2, T.Val>) -> List<&2, T.Val>:
  canon.go(xs, CTabs{})

# a table's rows as render writes them: the pairs that are no table, then
# the tables
def canon.rows(+xs: List<&2, T.Val>) -> List<&2, T.Val>:
  List.append(&2, T.Val, canon.keys(xs), canon.tabs(xs))

# the document as parse reads back what render wrote for it
def canon(dd: T.Doc) -> T.Doc:
  match dd:
    case T.Doc{_bad, rows}:
      T.Doc{"", own.rows(canon.rows(rows))}

# every string in the rows, at any depth and in every table, and every
# table's path, is short
def short.rows(xs: List<&2, T.Val>) -> Bool:
  match xs:
    case []:
      True{}
    case T.VPair{_n, T.VHead{pp, rr}} <> tt:
      Bool.and(short(pp), Bool.and(short.rows(rr), short.rows(tt)))
    case T.VPair{_n, T.VAots{pp, es}} <> tt:
      Bool.and(short(pp), Bool.and(short.rows(es), short.rows(tt)))
    case T.VAot{_p, rr} <> tt:
      Bool.and(short.rows(rr), short.rows(tt))
    case T.VPair{_n, vv} <> tt:
      Bool.and(cv.short1(vv), short.rows(tt))
    case vv <> tt:
      Bool.and(cv.short1(vv), short.rows(tt))

# LAW: for every well-formed document whose rendered text is shorter than
# 2^32 characters, the document parse reads back from that text, every span
# read out, is canon of it: no error, and every table's pairs that are no
# table in order, before its tables and arrays of tables in order
# TOML-RT-1
law render_parse_canon:
  for +d: T.Doc
  for +w: {T.wf(d) == True{} : Bool}
  for h_s: {short(T.render(d)) == True{} : Bool}
  {own(T.parse(T.render(d))) == canon(d) : T.Doc}

# LAW: a well-formed document is the same as canon of it: moving a table's
# pairs that are no table in front of its tables, and reading every span
# out, changes no value same compares
# TOML-RT-1
law canon_same:
  for +d: T.Doc
  for +w: {T.wf(d) == True{} : Bool}
  {same(canon(d), d) == True{} : Bool}

# LAW: render then parse is the same document: for every well-formed document
# whose rendered text is shorter than 2^32 characters, parse reads that text
# back with no error, as a document the same as the one render was given
# TOML-RT-1
law render_parse:
  for +d: T.Doc
  for +w: {T.wf(d) == True{} : Bool}
  for h_s: {short(T.render(d)) == True{} : Bool}
  {Bool.and(String.is_empty(T.bad(T.parse(T.render(d)))), same(T.parse(T.render(d)), d)) == True{} : Bool}

# a bare word's value, when it has one, is one a key may hold
def gd.gok(gg: T.Got) -> Bool:
  match gg:
    case T.GotVal{vv}:
      gd.vok(vv)
    case T.GotBad{_why}:
      True{}

# LAW: every value a bare word reads as is well-formed where a key or an array
# holds it: for every list of characters, word.val gives a boolean, a float
# spelled as wf.flo's grammar or inf or nan, an integer of decimal digits with
# no leading zero within signed 64 bits, or a datetime whose fields are in
# range, or no value at all
# TOML-RT-3
law gd_word:
  for +cs: List<&2, Char>
  {gd.gok(T.word.val(cs)) == True{} : Bool}

# a bare word's two states: its characters, and the space a datetime may hold
def gd.bw(lex: T.Lex) -> Bool:
  match lex:
    case T.LBare{}:
      True{}
    case T.LDate{}:
      True{}
    case _:
      False{}

# LAW: every step in a bare word keeps a state good: from every good state,
# whatever its fields, one character that is a Unicode scalar value read in a
# bare word's state or a datetime's space leaves a good state; a word that
# ends is read as a value (gd_word) and placed (gd_take)
# TOML-RT-3
law gd_bare_steps:
  for +lex: T.Lex
  for hl: {gd.bw(lex) == True{} : Bool}
  for +st: T.St
  for eg: {good(st) == True{} : Bool}
  for +cc: Char
  for ec: {T.wf.char(cc) == True{} : Bool}
  {good(T.read.on(lex, st, cc)) == True{} : Bool}

# LAW: the step parse takes for each character keeps a state good: from every
# good state, whatever its fields, one character that is a Unicode scalar
# value read by the fast step, with a held character and a byte-order mark,
# leaves a good state
# TOML-RT-3
law gd_fast_step:
  for +st: T.St
  for eg: {good(st) == True{} : Bool}
  for +cc: Char
  for ec: {T.wf.char(cc) == True{} : Bool}
  {good(T.read.fast(st, cc)) == True{} : Bool}

# LAW: reading a held character keeps a state good
# TOML-RT-3
law gd_held:
  for +st: T.St
  for eg: {good(st) == True{} : Bool}
  {good(T.read.once2(st)) == True{} : Bool}

# two texts of the same length
def gd.ln(aa: String, bb: String) -> Bool:
  match aa bb:
    case SNil{} SNil{}:
      True{}
    case SCon{_ah, at} SCon{_bh, bt}:
      gd.ln(at, bt)
    case _a _b:
      False{}

# a plain string's span as parse keeps it: n characters of the cut, each a
# Unicode scalar value, and then the rest of the cut, of scalar values and as
# long as the text still to read. zz says whether n has run down to 0
def gd.sp(cut: String, zz: Bool, +nn: U32, +text: String) -> Bool:
  match cut:
    case SNil{}:
      match zz:
        case True{}:
          Bool.and(T.wf.text(SNil{}), gd.ln(SNil{}, text))
        case False{}:
          False{}
    case SCon{+hh, +tt}:
      match zz:
        case True{}:
          Bool.and(T.wf.text(SCon{hh, tt}), gd.ln(SCon{hh, tt}, text))
        case False{}:
          Bool.and(T.wf.char(hh), gd.sp(tt, U32.is_zero(U32.sub(nn, 1)), U32.sub(nn, 1), text))

# TOML-RT-3's invariant over the modes doc.read reads the text in: a state
# that scans, or follows a carriage return, is good; an opening quote's state
# is good as the quote left it; a plain string's state is good with its
# buffer empty, its span holds scalar values up to the text still to read,
# and the span's count runs on through that text without wrapping
def gd.md(mode: T.Mode, +text: String) -> Bool:
  match mode:
    case T.MScan{st}:
      good(st)
    case T.MCr{st}:
      good(st)
    case T.MOpen{_basic, _q, qkind, bad, rows, heads, here, parts, buf, back, stack, uni, left, arrtab}:
      good(T.St{bad, rows, heads, here, parts, buf, T.LQ{}, back, qkind, stack, T.HNone{}, uni, left, arrtab,
        False{}})
    case T.MEat{_basic, _q, +cut, +nn, bad, rows, heads, here, parts, qkind, stack, uni, left, arrtab}:
      Bool.and(good(T.St{bad, rows, heads, here, parts, [], T.LStr{}, T.LStr{}, qkind, stack, T.HNone{}, uni,
        left, arrtab, False{}}), Bool.and(gd.sp(cut, U32.is_zero(nn), nn, text), counts(text, nn)))

# the mode doc.read moves to on one character, with the text after it
def gd.next(mode: T.Mode, +hh: Char, tt: String) -> T.Mode:
  match mode:
    case T.MOpen{basic, qq, qkind, bad, rows, heads, here, parts, buf, back, stack, uni, left, arrtab}:
      T.doc.open(basic, qq, qkind, bad, rows, heads, here, parts, buf, back, stack, uni, left, arrtab, hh, tt)
    case T.MEat{basic, qq, cut, nn, bad, rows, heads, here, parts, qkind, stack, uni, left, arrtab}:
      T.eat.feed(basic, qq, cut, nn, bad, rows, heads, here, parts, qkind, stack, uni, left, arrtab, hh)
    case T.MScan{st}:
      T.doc.scan(st, hh)
    case T.MCr{st}:
      T.doc.cr(Char.is_eq(hh, '\n'), st, hh)

# LAW: a plain string's span, kept as gd.md keeps it, is a well-formed span:
# its n characters are there and are Unicode scalar values
# TOML-RT-3
law gd_span_wf:
  for +cut: String
  for +nn: U32
  for +text: String
  for ep: {gd.sp(cut, U32.is_zero(nn), nn, text) == True{} : Bool}
  {T.wf.span(cut, nn, U32.is_zero(nn)) == True{} : Bool}

# LAW: every step doc.read takes keeps its mode good: from a mode good for a
# text of Unicode scalar values shorter than 2^32 characters, the mode after
# its first character is good for the rest. A scanning state takes the fast
# step, and a quote may open a string's span; a carriage return must meet a
# line feed; an opening quote's next character starts the span, or goes the
# old way; a span's character extends it, or closes it as a VSpan, or copies
# it to the buffer
# TOML-RT-3
law gd_mode_step:
  for +mode: T.Mode
  for +hh: Char
  for +tt: String
  for +em: {gd.md(mode, SCon{hh, tt}) == True{} : Bool}
  for eh: {T.wf.char(hh) == True{} : Bool}
  for et: {T.wf.text(tt) == True{} : Bool}
  for es: {short(SCon{hh, tt}) == True{} : Bool}
  {gd.md(gd.next(mode, hh, tt), tt) == True{} : Bool}

# LAW: doc.read takes a character to the mode gd.next names
# TOML-RT-3
law gd_next:
  for +mode: T.Mode
  for +hh: Char
  for +tt: String
  {T.doc.read(SCon{hh, tt}, mode) == T.doc.read(tt, gd.next(mode, hh, tt)) : T.Doc}

# LAW: doc.read, from a mode good for a text of Unicode scalar values shorter
# than 2^32 characters, gives a well-formed document whenever it gives no
# error: each character keeps the mode good (gd_mode_step), and at the end a
# token still open is closed, a held character read, and a good end state
# sealed (gd_fin); a string still open is an error
# TOML-RT-3
law gd_read:
  for +text: String
  for +mode: T.Mode
  for em: {gd.md(mode, text) == True{} : Bool}
  for +ew: {T.wf.text(text) == True{} : Bool}
  for +es: {short(text) == True{} : Bool}
  for eo: {String.is_empty(T.bad(T.doc.read(text, mode))) == True{} : Bool}
  {T.wf(T.doc.read(text, mode)) == True{} : Bool}

# LAW: parse only accepts what it can give back well-formed: for every text
# of Unicode scalar values shorter than 2^32 characters, a parse with no
# error is a well-formed document
# TOML-RT-3
law parse_wf:
  for +text: String
  for ew: {T.wf.text(text) == True{} : Bool}
  for es: {short(text) == True{} : Bool}
  for eo: {String.is_empty(T.bad(T.parse(text))) == True{} : Bool}
  {T.wf(T.parse(text)) == True{} : Bool}

# WP-R2: a parsed document renders, reparses and renders again unchanged.
# The first half is TOML-RT-1 at parse(t), which TOML-RT-3 makes well-formed;
# the second is render_parse_canon read through render: render writes a span
# as its characters, and already writes each table's pairs that are no table
# before its tables, so render(canon(d)) is render(d).

# LAW: for every text of Unicode scalar values shorter than 2^32 characters
# that parse reads with no error, and whose parse renders to a text shorter
# than 2^32 characters, parse reads that rendering back as the same document,
# which renders to the same text again
# TOML-RT-2
law parse_render_parse:
  for +t: String
  for h_u: {T.wf.text(t) == True{} : Bool}
  for h_s: {short(t) == True{} : Bool}
  for +h_r: {short(T.render(T.parse(t))) == True{} : Bool}
  for ok: {String.is_empty(T.bad(T.parse(t))) == True{} : Bool}
  {Bool.and(same(T.parse(T.render(T.parse(t))), T.parse(t)),
    String.eq(T.render(T.parse(T.render(T.parse(t)))), T.render(T.parse(t)))) == True{} : Bool}

# KEY-3: a key's name is its characters however it is written, read from
# every place a key may start. toml.abnf spells a basic string as quotation
# marks around basic-char pieces: basic-unescaped (any character but `"`,
# `\` and the controls other than tab) written as itself, or escaped: a
# backslash and one of `"`, `\`, b, f, n, r, t, or u and four HEXDIG, or U
# and eight. HEXDIG is a digit or a letter A to F, in either case, and the
# escape must name a Unicode scalar value. A basic key segment is a list of
# such pieces, named by the characters they stand for; a key segment is
# that, bare or literal, and a dotted key's segments are joined by dots with
# blank space around them, in a key and in a header alike.

# the letter of a two-character escape
type KMark is Data:
  KmQuote{}
  KmBack{}
  KmB{}
  KmF{}
  KmN{}
  KmR{}
  KmT{}

# the letter written after the backslash
def k3.mark.char(mm: KMark) -> Char:
  match mm:
    case KmQuote{}:
      '"'
    case KmBack{}:
      '\\'
    case KmB{}:
      'b'
    case KmF{}:
      'f'
    case KmN{}:
      'n'
    case KmR{}:
      'r'
    case KmT{}:
      't'

# the character it stands for: `"`, `\`, backspace, form feed, line feed,
# carriage return, tab
def k3.mark.dec(mm: KMark) -> Char:
  match mm:
    case KmQuote{}:
      '"'
    case KmBack{}:
      '\\'
    case KmB{}:
      Chr{8}
    case KmF{}:
      Chr{12}
    case KmN{}:
      '\n'
    case KmR{}:
      '\r'
    case KmT{}:
      '\t'

# a hexadecimal digit, a letter one in upper case when up
type KHex is Data:
  Kx0{}
  Kx1{}
  Kx2{}
  Kx3{}
  Kx4{}
  Kx5{}
  Kx6{}
  Kx7{}
  Kx8{}
  Kx9{}
  KxA{up: Bool}
  KxB{up: Bool}
  KxC{up: Bool}
  KxD{up: Bool}
  KxE{up: Bool}
  KxF{up: Bool}

# a letter digit's character: the upper case one, or the lower case one
def k3.hex.case(up: Bool, +upper: Char, +lower: Char) -> Char:
  match up:
    case True{}:
      upper
    case False{}:
      lower

# a hexadecimal digit's character
def k3.hex.char(hx: KHex) -> Char:
  match hx:
    case Kx0{}:
      '0'
    case Kx1{}:
      '1'
    case Kx2{}:
      '2'
    case Kx3{}:
      '3'
    case Kx4{}:
      '4'
    case Kx5{}:
      '5'
    case Kx6{}:
      '6'
    case Kx7{}:
      '7'
    case Kx8{}:
      '8'
    case Kx9{}:
      '9'
    case KxA{up}:
      k3.hex.case(up, 'A', 'a')
    case KxB{up}:
      k3.hex.case(up, 'B', 'b')
    case KxC{up}:
      k3.hex.case(up, 'C', 'c')
    case KxD{up}:
      k3.hex.case(up, 'D', 'd')
    case KxE{up}:
      k3.hex.case(up, 'E', 'e')
    case KxF{up}:
      k3.hex.case(up, 'F', 'f')

# a hexadecimal digit's value
def k3.hex.val(hx: KHex) -> U32:
  match hx:
    case Kx0{}:
      0
    case Kx1{}:
      1
    case Kx2{}:
      2
    case Kx3{}:
      3
    case Kx4{}:
      4
    case Kx5{}:
      5
    case Kx6{}:
      6
    case Kx7{}:
      7
    case Kx8{}:
      8
    case Kx9{}:
      9
    case KxA{_up}:
      10
    case KxB{_up}:
      11
    case KxC{_up}:
      12
    case KxD{_up}:
      13
    case KxE{_up}:
      14
    case KxF{_up}:
      15

# a number read so far, then one more digit
def k3.hex.acc(+acc: U32, hx: KHex) -> U32:
  U32.add(U32.mul(acc, 16), k3.hex.val(hx))

# the number four digits write, the most significant first
def k3.hex4(dd: KHex, cc: KHex, bb: KHex, aa: KHex) -> U32:
  k3.hex.acc(k3.hex.acc(k3.hex.acc(k3.hex.acc(0, dd), cc), bb), aa)

# a Unicode scalar value: at most U+10FFFF, and no surrogate (U+D800 to
# U+DFFF; 1114111 is %x10FFFF, 55296 %xD800 and 57343 %xDFFF)
def k3.scalar(+uu: U32) -> Bool:
  Bool.and(U32.is_le(uu, 1114111), Bool.not(Bool.and(U32.is_ge(uu, 55296), U32.is_le(uu, 57343))))

# basic-unescaped: any character but `"`, `\` and the controls other than tab
def k3.bchar(+cc: Char) -> Bool:
  Bool.not(Bool.or(Char.is_eq(cc, '"'), Bool.or(Char.is_eq(cc, '\\'), Bool.and(is_ctl(cc),
    Bool.not(Char.is_eq(cc, '\t'))))))

# one piece of a basic string: a character written as itself, a
# two-character escape, `\u` and four hexadecimal digits, or `\U` and eight
type KPiece is Data:
  KpChar{cc: Char}
  KpEsc{mm: KMark}
  KpU4{dd: KHex, cc: KHex, bb: KHex, aa: KHex}
  KpU8{hh: KHex, gg: KHex, ff: KHex, ee: KHex, dd: KHex, cc: KHex, bb: KHex, aa: KHex}

# four hexadecimal digits, then tail
def k3.hex4.text(dd: KHex, cc: KHex, bb: KHex, aa: KHex, tail: String) -> String:
  SCon{k3.hex.char(dd), SCon{k3.hex.char(cc), SCon{k3.hex.char(bb), SCon{k3.hex.char(aa), tail}}}}

# a piece's text, then tail
def k3.pc.text(pp: KPiece, tail: String) -> String:
  match pp:
    case KpChar{cc}:
      SCon{cc, tail}
    case KpEsc{mm}:
      SCon{'\\', SCon{k3.mark.char(mm), tail}}
    case KpU4{dd, cc, bb, aa}:
      SCon{'\\', SCon{'u', k3.hex4.text(dd, cc, bb, aa, tail)}}
    case KpU8{hh, gg, ff, ee, dd, cc, bb, aa}:
      SCon{'\\', SCon{'U', k3.hex4.text(hh, gg, ff, ee, k3.hex4.text(dd, cc, bb, aa, tail))}}

# the number eight digits write, the most significant first
def k3.hex8(
  hh: KHex,
  gg: KHex,
  ff: KHex,
  ee: KHex,
  dd: KHex,
  cc: KHex,
  bb: KHex,
  aa: KHex
) -> U32:
  k3.hex.acc(k3.hex.acc(k3.hex.acc(k3.hex.acc(k3.hex4(hh, gg, ff, ee), dd), cc), bb), aa)

# the character a piece stands for
def k3.pc.char(pp: KPiece) -> Char:
  match pp:
    case KpChar{cc}:
      cc
    case KpEsc{mm}:
      k3.mark.dec(mm)
    case KpU4{dd, cc, bb, aa}:
      Chr{k3.hex4(dd, cc, bb, aa)}
    case KpU8{hh, gg, ff, ee, dd, cc, bb, aa}:
      Chr{k3.hex8(hh, gg, ff, ee, dd, cc, bb, aa)}

# whether a basic string may hold the piece: a character written as itself
# must be basic-unescaped, and an escape's digits must name a Unicode scalar
# value
def k3.pc.ok(pp: KPiece) -> Bool:
  match pp:
    case KpChar{cc}:
      k3.bchar(cc)
    case KpEsc{_mm}:
      True{}
    case KpU4{dd, cc, bb, aa}:
      k3.scalar(k3.hex4(dd, cc, bb, aa))
    case KpU8{hh, gg, ff, ee, dd, cc, bb, aa}:
      k3.scalar(k3.hex8(hh, gg, ff, ee, dd, cc, bb, aa))

# the pieces' text, then tail
def k3.pcs.text(ps: List<&2, KPiece>, tail: String) -> String:
  match ps:
    case []:
      tail
    case pp <> rest:
      k3.pc.text(pp, k3.pcs.text(rest, tail))

# the characters the pieces stand for
def k3.pcs.name(ps: List<&2, KPiece>) -> String:
  match ps:
    case []:
      ""
    case pp <> rest:
      SCon{k3.pc.char(pp), k3.pcs.name(rest)}

# whether a basic string may hold every piece
def k3.pcs.ok(ps: List<&2, KPiece>) -> Bool:
  match ps:
    case []:
      True{}
    case pp <> rest:
      Bool.and(k3.pc.ok(pp), k3.pcs.ok(rest))

# LAW: a basic key reads back as its characters however it is spelled: for
# every list of pieces a basic string may hold, the key they spell in
# quotation marks, then " = 1", parses with no error to one pair named by the
# characters the pieces stand for, holding 1
# TOML-KEY-3
law basic_key_reads_back:
  for +ps: List<&2, KPiece>
  for ok: {k3.pcs.ok(ps) == True{} : Bool}
  {T.parse(SCon{'"', k3.pcs.text(ps, "\" = 1")}) == T.Doc{"", [T.VPair{k3.pcs.name(ps), one()}]} : T.Doc}

# a key segment: bare, a basic string of pieces, or a literal string
type KSeg is Data:
  KsBare{name: String}
  KsBasic{pl: List<&2, KPiece>}
  KsLit{name: String}

# a segment's text, then tail
def k3.seg.text(sg: KSeg, tail: String) -> String:
  match sg:
    case KsBare{name}:
      String.append(name, tail)
    case KsBasic{pl}:
      SCon{'"', k3.pcs.text(pl, SCon{'"', tail})}
    case KsLit{name}:
      SCon{'\'', String.append(name, SCon{'\'', tail})}

# a segment's name: its characters, a basic one's escapes decoded
def k3.seg.name(sg: KSeg) -> String:
  match sg:
    case KsBare{name}:
      name
    case KsBasic{pl}:
      k3.pcs.name(pl)
    case KsLit{name}:
      name

# whether a segment is spelled as toml.abnf allows: a bare one is a bare
# key, a basic one's pieces a basic string may hold, and a literal one's
# characters a literal string may hold
def k3.seg.ok(sg: KSeg) -> Bool:
  match sg:
    case KsBare{name}:
      T.bare(name)
    case KsBasic{pl}:
      k3.pcs.ok(pl)
    case KsLit{name}:
      lit.text(name)

# a segment of a dotted key that a dot follows, with the blank space before
# the dot and after it
type KDot is Data:
  KDot{seg: KSeg, g1: List<&2, Bool>, g2: List<&2, Bool>}

# the text of a dotted key, its segments joined by dots with their blank
# space, then tail
def k3.dk.text(ds: List<&2, KDot>, last: KSeg, tail: String) -> String:
  match ds:
    case []:
      k3.seg.text(last, tail)
    case KDot{sg, g1, g2} <> rest:
      k3.seg.text(sg, String.append(gap(g1), SCon{'.', String.append(gap(g2), k3.dk.text(rest, last, tail))}))

# the names of a dotted key's segments, in order
def k3.dk.names(ds: List<&2, KDot>, last: KSeg) -> List<&2, String>:
  match ds:
    case []:
      [k3.seg.name(last)]
    case KDot{sg, _g1, _g2} <> rest:
      k3.seg.name(sg) <> k3.dk.names(rest, last)

# whether every segment of a dotted key is spelled as toml.abnf allows
def k3.dk.ok(ds: List<&2, KDot>, last: KSeg) -> Bool:
  match ds:
    case []:
      k3.seg.ok(last)
    case KDot{sg, _g1, _g2} <> rest:
      Bool.and(k3.seg.ok(sg), k3.dk.ok(rest, last))

# where a key may start: at the start of a line, after an inline table's
# `{`, or after a comma in one
type KPos is Data:
  AtLine{}
  AtInl{}
  AtInlK{}

# the scanner's state there
def k3.pos.lex(at: KPos) -> T.Lex:
  match at:
    case AtLine{}:
      T.LTop{}
    case AtInl{}:
      T.LInl{}
    case AtInlK{}:
      T.LInlK{}

# a scanner where a key may start, having read nothing of it, with the
# tables, the stack of open arrays and inline tables and the other fields as
# the text before left them
def k3.at(
  at: KPos,
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  stack: List<&2, T.Ctx>,
  arrtab: Bool,
  back: T.Lex,
  qkind: T.QKind,
  uni: U32,
  left: U32
) -> T.St:
  T.St{"", rows, heads, here, [], [], k3.pos.lex(at), back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}}

# a scanner after a key's `=`, waiting for its value: the key's segments in
# parts, newest first
def k3.val(
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  parts: List<&2, String>,
  stack: List<&2, T.Ctx>,
  arrtab: Bool,
  back: T.Lex,
  qkind: T.QKind,
  uni: U32,
  left: U32
) -> T.St:
  T.St{"", rows, heads, here, parts, [], T.LVal{}, back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}}

# the rest of the text read once a key's `=` is read, wherever the key's
# segments left back, qkind, uni and left
def k3.KeyThen(
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  parts: List<&2, String>,
  stack: List<&2, T.Ctx>,
  arrtab: Bool,
  rest: String,
  goal: T.Doc
) -> Type:
  @bk: T.Lex -> @qk: T.QKind -> @un: U32 -> @lf: U32 ->
    {T.doc.read(rest, T.MScan{k3.val(rows, heads, here, parts, stack, arrtab, bk, qk, un, lf)}) == goal : T.Doc}

# LAW: a key reads back as its characters wherever a key may start: at the
# start of a line in any table, or in an inline table after its `{` or a
# comma, whatever the stack and the other fields hold, blank space, a key of
# segments each bare, basic or literal and spelled any way toml.abnf allows,
# joined by dots with blank space around them, then blank space and `=`,
# leave the scanner waiting for the value with every segment's characters,
# escapes decoded, as the key's parts
# TOML-KEY-3
law key_reads_back_anywhere:
  for +at: KPos
  for +g0: List<&2, Bool>
  for +ds: List<&2, KDot>
  for +last: KSeg
  for ok: {k3.dk.ok(ds, last) == True{} : Bool}
  for +g: List<&2, Bool>
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +here: List<&2, String>
  for +stack: List<&2, T.Ctx>
  for +arrtab: Bool
  for +back: T.Lex
  for +qkind: T.QKind
  for +uni: U32
  for +left: U32
  for +rest: String
  for +goal: T.Doc
  for ih: k3.KeyThen(rows, heads, here, List.reverse(&2, String, k3.dk.names(ds, last)), stack, arrtab, rest, goal)
  {T.doc.read(String.append(gap(g0), k3.dk.text(ds, last, String.append(gap(g), SCon{'=', rest}))),
    T.MScan{k3.at(at, rows, heads, here, stack, arrtab, back, qkind, uni, left)}) == goal : T.Doc}

# a header's text: `[` (`[[` for an array of tables), blank space, a dotted
# key's text, blank space, `]` (`]]`), then rest
def k3.hd.text(
  arr: Bool,
  g0: List<&2, Bool>,
  ds: List<&2, KDot>,
  last: KSeg,
  g9: List<&2, Bool>,
  rest: String
) -> String:
  match arr:
    case False{}:
      SCon{'[', String.append(gap(g0), k3.dk.text(ds, last, String.append(gap(g9), SCon{']', rest})))}
    case True{}:
      SCon{'[', SCon{'[', String.append(gap(g0), k3.dk.text(ds, last, String.append(gap(g9), SCon{']', SCon{']',
        rest}})))}}

# a scanner after a whole expression, in the table here, before the end of
# its line
def k3.line(
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  back: T.Lex,
  qkind: T.QKind,
  uni: U32,
  left: U32
) -> T.St:
  T.St{"", rows, heads, here, [], [], T.LLine{}, back, qkind, [], T.HNone{}, uni, left, False{}, False{}}

# LAW: a header reads back as the table named by its segments' characters,
# however they are written: from the start of a line in any table, with no
# array or inline table open and whatever the other fields hold, `[` (`[[`),
# blank space, segments each bare, basic or literal and spelled any way
# toml.abnf allows, joined by dots with blank space around them, blank space
# and `]` (`]]`) run the header's walk along the segments' characters, escapes
# decoded, and leave the scanner in that table with the rows and definitions
# the walk returns
# TOML-KEY-3
law header_reads_back_anywhere:
  for +arr: Bool
  for +g0: List<&2, Bool>
  for +ds: List<&2, KDot>
  for +last: KSeg
  for ok: {k3.dk.ok(ds, last) == True{} : Bool}
  for +g9: List<&2, Bool>
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +here: List<&2, String>
  for +arrtab: Bool
  for +back: T.Lex
  for +qkind: T.QKind
  for +uni: U32
  for +left: U32
  for +rows2: List<&2, T.Val>
  for +heads2: List<&2, String>
  for ew: {T.tree.walk(k3.dk.names(ds, last), T.Tw{rows, header_job(arr), [], "", "", heads, False{}}, 0)
    == T.End{rows2, "", heads2} : T.End}
  for +rest: String
  for +goal: T.Doc
  for ih: @bk: T.Lex -> @qk: T.QKind -> @un: U32 -> @lf: U32 -> {T.doc.read(rest, T.MScan{k3.line(rows2, heads2,
    k3.dk.names(ds, last), bk, qk, un, lf)}) == goal : T.Doc}
  {T.doc.read(k3.hd.text(arr, g0, ds, last, g9, rest), T.MScan{k3.at(AtLine{}, rows, heads, here, [], arrtab, back,
    qkind, uni, left)}) == goal : T.Doc}

# KEY-3: a key found in a parsed document. k3.has(rows, path, k) says the
# rows hold a pair named k in the table the path names: the path's first
# name is some pair's in the rows, every pair of that name holds the rest of
# the path, and the last table's rows are ones get finds k in. A table's
# rows, an inline table's and an element of an array of tables hold the path
# as rows do; an array of tables or an array holds it when some element or
# item does, so at, which enters no array, is not needed to say it. Names
# compare as get compares them (str.eq).

# how k3.h reads its list, and the rest of the path: the rows seen for one
# name, or the elements of an array of tables or the items of an array
type KHm is Data:
  KhAll{name: String, path: List<&2, String>}
  KhSome{path: List<&2, String>}

# whether a lookup found something
def k3.found(hh: T.Hit) -> Bool:
  match hh:
    case T.Found{_v}:
      True{}
    case T.Miss{}:
      False{}

# whether a list, read as md says, holds a pair named kk at the end of the
# path. A table's rows are read in place: kk found in them at the end of the
# path, or the next name found in them and every pair of it holding the rest
def k3.h(xs: List<&2, T.Val>, md: KHm, +kk: String) -> Bool:
  match xs md:
    case [] KhAll{_n, _p}:
      True{}
    case T.VPair{+mm, T.VHead{_q, rows}} <> tt KhAll{+nn, Nil{}}:
      Bool.and(Bool.or(Bool.not(T.str.eq(mm, nn)), k3.found(T.get(rows, kk))), k3.h(tt, KhAll{nn, []}, kk))
    case T.VPair{+mm, T.VHead{_q, +rows}} <> tt KhAll{+nn, +n2 <> +p2}:
      Bool.and(Bool.or(Bool.not(T.str.eq(mm, nn)), Bool.and(k3.found(T.get(rows, n2)), k3.h(rows, KhAll{n2, p2},
        kk))), k3.h(tt, KhAll{nn, n2 <> p2}, kk))
    case T.VPair{+mm, T.VInl{rows}} <> tt KhAll{+nn, Nil{}}:
      Bool.and(Bool.or(Bool.not(T.str.eq(mm, nn)), k3.found(T.get(rows, kk))), k3.h(tt, KhAll{nn, []}, kk))
    case T.VPair{+mm, T.VInl{+rows}} <> tt KhAll{+nn, +n2 <> +p2}:
      Bool.and(Bool.or(Bool.not(T.str.eq(mm, nn)), Bool.and(k3.found(T.get(rows, n2)), k3.h(rows, KhAll{n2, p2},
        kk))), k3.h(tt, KhAll{nn, n2 <> p2}, kk))
    case T.VPair{+mm, T.VAots{_q, es}} <> tt KhAll{+nn, +pp}:
      Bool.and(Bool.or(Bool.not(T.str.eq(mm, nn)), k3.h(es, KhSome{pp}, kk)), k3.h(tt, KhAll{nn, pp}, kk))
    case T.VPair{+mm, T.VArr{items}} <> tt KhAll{+nn, +pp}:
      Bool.and(Bool.or(Bool.not(T.str.eq(mm, nn)), k3.h(items, KhSome{pp}, kk)), k3.h(tt, KhAll{nn, pp}, kk))
    case T.VPair{+mm, _v} <> tt KhAll{+nn, +pp}:
      Bool.and(Bool.not(T.str.eq(mm, nn)), k3.h(tt, KhAll{nn, pp}, kk))
    case _h <> tt KhAll{+nn, +pp}:
      k3.h(tt, KhAll{nn, pp}, kk)
    case [] KhSome{_p}:
      False{}
    case T.VAot{_q, rows} <> tt KhSome{Nil{}}:
      Bool.or(k3.found(T.get(rows, kk)), k3.h(tt, KhSome{[]}, kk))
    case T.VAot{_q, +rows} <> tt KhSome{+n2 <> +p2}:
      Bool.or(Bool.and(k3.found(T.get(rows, n2)), k3.h(rows, KhAll{n2, p2}, kk)), k3.h(tt, KhSome{n2 <> p2}, kk))
    case T.VInl{rows} <> tt KhSome{Nil{}}:
      Bool.or(k3.found(T.get(rows, kk)), k3.h(tt, KhSome{[]}, kk))
    case T.VInl{+rows} <> tt KhSome{+n2 <> +p2}:
      Bool.or(Bool.and(k3.found(T.get(rows, n2)), k3.h(rows, KhAll{n2, p2}, kk)), k3.h(tt, KhSome{n2 <> p2}, kk))
    case T.VArr{items} <> tt KhSome{+pp}:
      Bool.or(k3.h(items, KhSome{pp}, kk), k3.h(tt, KhSome{pp}, kk))
    case _v <> tt KhSome{+pp}:
      k3.h(tt, KhSome{pp}, kk)

# the path under which a value taken now is found at the end: the current
# table and the key's parts at the root; an array's item is found where the
# array is; a pair in an inline table under the key's parts where the
# inline table is
def k3.pl(
  stack: List<&2, T.Ctx>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +pp: List<&2, String>
) -> List<&2, String>:
  match stack:
    case []:
      List.append(&2, String, List.append(&2, String, here, List.reverse(&2, String, parts)), pp)
    case T.CArr{_i, +sp, +sh} <> rest:
      k3.pl(rest, sh, sp, pp)
    case T.CInl{_r, +sp, +sh} <> rest:
      k3.pl(rest, sh, sp, List.append(&2, String, List.reverse(&2, String, parts), pp))

# whether the rows hold a pair named kk in the table the path names
def k3.has(+rows: List<&2, T.Val>, path: List<&2, String>, +kk: String) -> Bool:
  match path:
    case []:
      k3.found(T.get(rows, kk))
    case +nn <> pp:
      Bool.and(k3.found(T.get(rows, nn)), k3.h(rows, KhAll{nn, pp}, kk))

# whether a bare word's refusal says why: a value, or a reason that is not
# empty
def k3.why(gg: T.Got) -> Bool:
  match gg:
    case T.GotVal{_v}:
      True{}
    case T.GotBad{why}:
      Bool.not(String.is_empty(why))

# LAW: a bare word the scanner refuses is refused with a reason: for every
# list of characters, word.val gives a value, or a reason that is not empty,
# so a refused value always leaves the document with an error
# TOML-KEY-3
law bare_word_refusal_says_why:
  for +cs: List<&2, Char>
  {k3.why(T.word.val(cs)) == True{} : Bool}

# the names of a dotted key's segments but the last, in order
def k3.dk.init(ds: List<&2, KDot>) -> List<&2, String>:
  match ds:
    case []:
      []
    case KDot{sg, _g1, _g2} <> rest:
      k3.seg.name(sg) <> k3.dk.init(rest)

# no array is open around a key: the innermost open frame, if any, is an
# inline table
def k3.noarr1(stack: List<&2, T.Ctx>) -> Bool:
  match stack:
    case []:
      True{}
    case T.CArr{_i, _p, _h} <> _t:
      False{}
    case T.CInl{_r, _p, _h} <> _t:
      True{}

# the table a key read with the scanner in this state is put in: the
# current table and the key's other segments at the root, or those segments
# in an open inline table, where that table is put
def k3.key.table(stack: List<&2, T.Ctx>, +here: List<&2, String>, ds: List<&2, KDot>) -> List<&2, String>:
  k3.pl(stack, here, List.reverse(&2, String, k3.dk.init(ds)), [])

# a key's text and the rest of a document read from where a key may start
def k3.key.doc(
  at: KPos,
  g0: List<&2, Bool>,
  ds: List<&2, KDot>,
  last: KSeg,
  gs: List<&2, Bool>,
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  stack: List<&2, T.Ctx>,
  arrtab: Bool,
  back: T.Lex,
  qkind: T.QKind,
  uni: U32,
  left: U32,
  rest: String
) -> T.Doc:
  T.doc.read(String.append(gap(g0), k3.dk.text(ds, last, String.append(gap(gs), SCon{'=', rest}))),
    T.MScan{k3.at(at, rows, heads, here, stack, arrtab, back, qkind, uni, left)})

# LAW: a key's value, whatever it is, is put under the key's name in the
# key's table: after a key's `=`, with the key's segments newest first in
# parts and no array open around the key, the rest of any text read leaves a
# document that has an error or whose root holds a pair named by the key's
# last segment in the table k3.pl names (TOML-KEY-3's any value)
# TOML-KEY-3
law key_found_after_equals:
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +here: List<&2, String>
  for +k: String
  for +ps: List<&2, String>
  for +stack: List<&2, T.Ctx>
  for +arrtab: Bool
  for +back: T.Lex
  for +qkind: T.QKind
  for +uni: U32
  for +left: U32
  for +rest: String
  for es: {k3.noarr1(stack) == True{} : Bool}
  for eo: {String.is_empty(T.bad(T.doc.read(rest, T.MScan{k3.val(rows, heads, here, k <> ps, stack, arrtab, back,
    qkind, uni, left)}))) == True{} : Bool}
  {k3.has(T.root(T.doc.read(rest, T.MScan{k3.val(rows, heads, here, k <> ps, stack, arrtab, back, qkind, uni,
    left)})), k3.pl(stack, here, ps, []), k) == True{} : Bool}

# LAW: a key is put under its characters in the table its line or inline
# table names, however it is written: wherever a key may start (the start of
# a line in any table, or an inline table after its `{` or a comma), with no
# array open around it and whatever the other fields hold, blank space, a
# dotted key of segments each bare, basic or literal and spelled any way
# toml.abnf allows, blank space, `=` and then any text leave a document that
# has an error or whose root holds a pair named by the last segment's
# characters in the table the other segments name from the current table
# (k3.key.table), so get finds it by them in that table's rows
# TOML-KEY-3
law key_found_anywhere:
  for +at: KPos
  for +g0: List<&2, Bool>
  for +ds: List<&2, KDot>
  for +last: KSeg
  for ok: {k3.dk.ok(ds, last) == True{} : Bool}
  for +g: List<&2, Bool>
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +here: List<&2, String>
  for +stack: List<&2, T.Ctx>
  for +arrtab: Bool
  for +back: T.Lex
  for +qkind: T.QKind
  for +uni: U32
  for +left: U32
  for +rest: String
  for es: {k3.noarr1(stack) == True{} : Bool}
  for eo: {String.is_empty(T.bad(k3.key.doc(at, g0, ds, last, g, rows, heads, here, stack, arrtab, back, qkind, uni,
    left, rest))) == True{} : Bool}
  {k3.has(T.root(k3.key.doc(at, g0, ds, last, g, rows, heads, here, stack, arrtab, back, qkind, uni, left, rest)),
    k3.key.table(stack, here, ds), k3.seg.name(last)) == True{} : Bool}

# a header's text and the rest of a document read from the start of a line
def k3.hd.doc(
  arr: Bool,
  g0: List<&2, Bool>,
  ds: List<&2, KDot>,
  last: KSeg,
  g9: List<&2, Bool>,
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  arrtab: Bool,
  back: T.Lex,
  qkind: T.QKind,
  uni: U32,
  left: U32,
  rest: String
) -> T.Doc:
  T.doc.read(k3.hd.text(arr, g0, ds, last, g9, rest), T.MScan{k3.at(AtLine{}, rows, heads, here, [], arrtab, back,
    qkind, uni, left)})

# LAW: a header's table is put under its characters: from the start of a
# line in any table, with no array or inline table open, a `[table]` or
# `[[array]]` header of segments spelled any way toml.abnf allows, then any
# text, leave a document that has an error or whose root holds, in the table
# the other segments name, a pair named by the last segment's characters
# TOML-KEY-3
law header_found_anywhere:
  for +arr: Bool
  for +g0: List<&2, Bool>
  for +ds: List<&2, KDot>
  for +last: KSeg
  for ok: {k3.dk.ok(ds, last) == True{} : Bool}
  for +g9: List<&2, Bool>
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +here: List<&2, String>
  for +arrtab: Bool
  for +back: T.Lex
  for +qkind: T.QKind
  for +uni: U32
  for +left: U32
  for +rest: String
  for eo: {String.is_empty(T.bad(k3.hd.doc(arr, g0, ds, last, g9, rows, heads, here, arrtab, back, qkind, uni, left,
    rest))) == True{} : Bool}
  {k3.has(T.root(k3.hd.doc(arr, g0, ds, last, g9, rows, heads, here, arrtab, back, qkind, uni, left, rest)),
    k3.dk.init(ds), k3.seg.name(last)) == True{} : Bool}

# a hit is a table or an inline table
def k3.istab(hh: T.Hit) -> Bool:
  match hh:
    case T.Found{T.VHead{_q, _r}}:
      True{}
    case T.Found{T.VInl{_r}}:
      True{}
    case _h:
      False{}

# the hit and every name after it on a path are tables or inline tables
def k3.tabh(pp: List<&2, String>, +hh: T.Hit) -> Bool:
  match pp:
    case []:
      k3.istab(hh)
    case +nn <> rest:
      Bool.and(k3.istab(hh), k3.tabh(rest, T.get(T.at.rows_of(hh), nn)))

# every name on a path, from these rows, is a table or an inline table's:
# no array lies on the path, so at can follow it
def k3.tabs(+rows: List<&2, T.Val>, path: List<&2, String>) -> Bool:
  match path:
    case []:
      True{}
    case +nn <> pp:
      k3.tabh(pp, T.get(rows, nn))

# LAW: and at finds it from the root by the names on its path when no array
# lies on that path: in the document key_found_anywhere reads, with no
# error, when every name of the key's table path is a table or an inline
# table, at finds the key by the path's names and the key's
# TOML-KEY-3
law key_found_by_at:
  for +at: KPos
  for +g0: List<&2, Bool>
  for +ds: List<&2, KDot>
  for +last: KSeg
  for ok: {k3.dk.ok(ds, last) == True{} : Bool}
  for +g: List<&2, Bool>
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +here: List<&2, String>
  for +stack: List<&2, T.Ctx>
  for +arrtab: Bool
  for +back: T.Lex
  for +qkind: T.QKind
  for +uni: U32
  for +left: U32
  for +rest: String
  for es: {k3.noarr1(stack) == True{} : Bool}
  for eo: {String.is_empty(T.bad(k3.key.doc(at, g0, ds, last, g, rows, heads, here, stack, arrtab, back, qkind, uni,
    left, rest))) == True{} : Bool}
  for et: {k3.tabs(T.root(k3.key.doc(at, g0, ds, last, g, rows, heads, here, stack, arrtab, back, qkind, uni, left,
    rest)), k3.key.table(stack, here, ds)) == True{} : Bool}
  {k3.found(T.at(T.root(k3.key.doc(at, g0, ds, last, g, rows, heads, here, stack, arrtab, back, qkind, uni, left,
    rest)), List.append(&2, String, k3.key.table(stack, here, ds), [k3.seg.name(last)]))) == True{} : Bool}

# LAW: and a header's table the same way: in the document
# header_found_anywhere reads, with no error, when every name before the
# last is a table or an inline table, at finds the header's table by its
# names
# TOML-KEY-3
law header_found_by_at:
  for +arr: Bool
  for +g0: List<&2, Bool>
  for +ds: List<&2, KDot>
  for +last: KSeg
  for ok: {k3.dk.ok(ds, last) == True{} : Bool}
  for +g9: List<&2, Bool>
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +here: List<&2, String>
  for +arrtab: Bool
  for +back: T.Lex
  for +qkind: T.QKind
  for +uni: U32
  for +left: U32
  for +rest: String
  for eo: {String.is_empty(T.bad(k3.hd.doc(arr, g0, ds, last, g9, rows, heads, here, arrtab, back, qkind, uni, left,
    rest))) == True{} : Bool}
  for et: {k3.tabs(T.root(k3.hd.doc(arr, g0, ds, last, g9, rows, heads, here, arrtab, back, qkind, uni, left, rest)),
    k3.dk.init(ds)) == True{} : Bool}
  {k3.found(T.at(T.root(k3.hd.doc(arr, g0, ds, last, g9, rows, heads, here, arrtab, back, qkind, uni, left, rest)),
    List.append(&2, String, k3.dk.init(ds), [k3.seg.name(last)]))) == True{} : Bool}

# LAW: in a parsed document: when parse reads a text's first part, pre, to
# where a key may start, with no array open, and a key's text and the rest
# follow, the document parse returns, with no error, holds the pair under
# the key's characters in its table
# TOML-KEY-3
law key_found_in_document:
  for +pre: String
  for +at: KPos
  for +g0: List<&2, Bool>
  for +ds: List<&2, KDot>
  for +last: KSeg
  for ok: {k3.dk.ok(ds, last) == True{} : Bool}
  for +g: List<&2, Bool>
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +here: List<&2, String>
  for +stack: List<&2, T.Ctx>
  for +arrtab: Bool
  for +back: T.Lex
  for +qkind: T.QKind
  for +uni: U32
  for +left: U32
  for +rest: String
  for es: {k3.noarr1(stack) == True{} : Bool}
  for +ep: {T.parse(String.append(pre, String.append(gap(g0), k3.dk.text(ds, last, String.append(gap(g), SCon{'=',
    rest}))))) == k3.key.doc(at, g0, ds, last, g, rows, heads, here, stack, arrtab, back, qkind, uni, left, rest)
    : T.Doc}
  for eo: {String.is_empty(T.bad(T.parse(String.append(pre, String.append(gap(g0), k3.dk.text(ds, last,
    String.append(gap(g), SCon{'=', rest}))))))) == True{} : Bool}
  {k3.has(T.root(T.parse(String.append(pre, String.append(gap(g0), k3.dk.text(ds, last, String.append(gap(g),
    SCon{'=', rest})))))), k3.key.table(stack, here, ds), k3.seg.name(last)) == True{} : Bool}

# GRAMMAR SPIKE
#
# One rule of toml.abnf (TOML v1.0.0), dec-int, transcribed as a Bool
# recognizer over a bare word's characters, one def per rule with the rule
# quoted above it, as TOML-KEY-1's unquoted-key is. It tries the leaf form of
# the grammar relation (docs/rfc/eztoml-grammar-proofs.md) against the numeral
# scan. Bend has no hex literals, so each bound is in decimal with its hex
# beside it.

# minus = %x2D ; -
# (%x2D is 45)
def abnf.minus(cc: Char) -> Bool:
  match cc:
    case Chr{+cp}:
      U32.is_eq(cp, 45)

# plus = %x2B ; +
# (%x2B is 43)
def abnf.plus(cc: Char) -> Bool:
  match cc:
    case Chr{+cp}:
      U32.is_eq(cp, 43)

# underscore = %x5F ; _
# (%x5F is 95)
def abnf.underscore(cc: Char) -> Bool:
  match cc:
    case Chr{+cp}:
      U32.is_eq(cp, 95)

# digit1-9 = %x31-39 ; 1-9
# (%x31 is 49, %x39 is 57)
def abnf.digit1_9(cc: Char) -> Bool:
  match cc:
    case Chr{+cp}:
      Bool.and(U32.is_ge(cp, 49), U32.is_le(cp, 57))

# DIGIT = %x30-39 ; 0-9, over a character (abnf.digit is over a code point)
def abnf.DIGIT(cc: Char) -> Bool:
  match cc:
    case Chr{+cp}:
      abnf.digit(cp)

# *( DIGIT / underscore DIGIT ): nothing, or one of the two and the rest. A
# lone character left can only be a DIGIT, since underscore needs one after it
def abnf.dec_rep(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      True{}
    case +hh <> tt:
      match tt:
        case []:
          abnf.DIGIT(hh)
        case +h2 <> +t2:
          Bool.or(Bool.and(abnf.DIGIT(hh), abnf.dec_rep(h2 <> t2)),
            Bool.and(abnf.underscore(hh), Bool.and(abnf.DIGIT(h2), abnf.dec_rep(t2))))

# 1*( DIGIT / underscore DIGIT ): the repetition, at least once
def abnf.dec_rep1(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      False{}
    case +hh <> tt:
      abnf.dec_rep(hh <> tt)

# unsigned-dec-int = DIGIT / digit1-9 1*( DIGIT / underscore DIGIT )
def abnf.unsigned_dec_int(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      False{}
    case +hh <> +tt:
      Bool.or(Bool.and(abnf.DIGIT(hh), List.is_empty(&2, Char, tt)),
        Bool.and(abnf.digit1_9(hh), abnf.dec_rep1(tt)))

# dec-int = [ minus / plus ] unsigned-dec-int
def abnf.dec_int(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      False{}
    case +hh <> +tt:
      Bool.or(Bool.and(Bool.or(abnf.minus(hh), abnf.plus(hh)), abnf.unsigned_dec_int(tt)),
        abnf.unsigned_dec_int(hh <> tt))

# a character of a numeral kept unless it is an underscore
def abnf.no_us.pick(us: Bool, cc: Char, rest: String) -> String:
  match us:
    case True{}:
      rest
    case False{}:
      SCon{cc, rest}

# a numeral's characters with its underscores removed
def abnf.no_us(cs: List<&2, Char>) -> String:
  match cs:
    case []:
      ""
    case +hh <> tt:
      abnf.no_us.pick(abnf.underscore(hh), hh, abnf.no_us(tt))

# the sign a leading minus gives, and plus otherwise
def abnf.sign.pick(minus: Bool) -> T.Sign:
  match minus:
    case True{}:
      T.Minus{}
    case False{}:
      T.Plus{}

# the sign a dec-int is read with: minus when it starts with one, else plus
def abnf.dec_sign(cs: List<&2, Char>) -> T.Sign:
  match cs:
    case []:
      T.Plus{}
    case +hh <> _:
      abnf.sign.pick(abnf.minus(hh))

# the characters after a leading sign, or all of them
def abnf.digits.pick(signed: Bool, cc: Char, rest: List<&2, Char>) -> String:
  match signed:
    case True{}:
      abnf.no_us(rest)
    case False{}:
      abnf.no_us(cc <> rest)

# the digits a dec-int is read as: after its sign, with the underscores
# removed. unsigned-dec-int allows no leading zero except in 0 itself, so these
# are its value's decimal digits
def abnf.dec_digits(cs: List<&2, Char>) -> String:
  match cs:
    case []:
      ""
    case +hh <> tt:
      abnf.digits.pick(Bool.or(abnf.minus(hh), abnf.plus(hh)), hh, tt)

# LAW: a bare word that matches toml.abnf's dec-int and lies within signed 64
# bits is read as an integer: minus when it starts with a minus and plus
# otherwise, with the digits after the sign and the underscores removed
# TOML-NUM-1
law dec_int_word:
  for +cs: List<&2, Char>
  for +h: {abnf.dec_int(cs) == True{} : Bool}
  for +r: {T.i64.fits(abnf.dec_sign(cs), abnf.dec_digits(cs)) == True{} : Bool}
  {T.word.val(cs) == T.GotVal{T.VInt{abnf.dec_sign(cs), abnf.dec_digits(cs)}} : T.Got}

# GRAMMAR
#
# toml.abnf (TOML v1.0.0; github.com/toml-lang/toml at tag 1.0.0) transcribed
# as the grammar relation of TOML-TEXT-1 (docs/rfc/eztoml-grammar-proofs.md,
# WP-G). The context-free structure is data, a derivation (Gd) whose
# constructors are named after the rules they spell; the regular rules are
# Bool recognizers at its leaves, over a leaf's characters. A text matches
# the grammar when, with one leading U+FEFF taken off (bom.drop), it is
# g.text(d) for a derivation d with g.ok(d). g.ok asks each leaf to match its
# rule and to keep the four restrictions the specification's prose adds
# (prose.*). g.val says what a value derivation denotes, and defs is the
# prose's definition rules, which TOML-TEXT-2 states.
#
# Each rule is quoted verbatim above the def or constructor that transcribes
# it; a rule the GRAMMAR SPIKE or TOML-KEY-1 already transcribed is reused
# (DIGIT, minus, plus, underscore, digit1-9, dec-int, unsigned-dec-int,
# unquoted-key), and TOML-KEY-3's KPiece and KSeg are a basic string's
# pieces and a simple-key. Two traps: a quoted string in ABNF is
# case-insensitive (RFC 5234, section 2.3), so "T", "Z", "e" and HEXDIG's "A"
# to "F" match either case, while a %x string such as hex-prefix, true or inf
# matches only itself; and Bend has no mutual recursion, so the mutually
# recursive rules val, array-values, inline-table-keyvals and keyval are
# constructors of one type, GVal, and a def over it takes a mode (GRule)
# saying which rule a node spells. Bend has no hex literals, so each bound is
# in decimal with its hex beside it.

# whether a character is the one with code point nn
def abnf.cp(cc: Char, +nn: U32) -> Bool:
  match cc:
    case Chr{+cp}:
      U32.is_eq(cp, nn)

# whether a code point is from lo to hi, both included: RFC 5234's %xLO-HI
def abnf.range(+cp: U32, +lo: U32, +hi: U32) -> Bool:
  Bool.and(U32.is_ge(cp, lo), U32.is_le(cp, hi))

# whether a word is exactly the characters of ss, each matched as itself
# (a %x string: %x74.72.75.65 is the word true and nothing else)
def abnf.chars_are(cs: List<&2, Char>, ss: String) -> Bool:
  match cs ss:
    case [] SNil{}:
      True{}
    case +hh <> tt SCon{+h2, t2}:
      Bool.and(Char.is_eq(hh, h2), abnf.chars_are(tt, t2))
    case _c _s:
      False{}

# Whitespace, newline and comment.

# wschar =  %x20  ; Space
# wschar =/ %x09  ; Horizontal tab
# (%x20 is 32, %x09 is 9)
def abnf.wschar(cc: Char) -> Bool:
  match cc:
    case Chr{+cp}:
      Bool.or(U32.is_eq(cp, 32), U32.is_eq(cp, 9))

# ws = *wschar
def abnf.ws(ss: String) -> Bool:
  match ss:
    case SNil{}:
      True{}
    case SCon{hh, tt}:
      Bool.and(abnf.wschar(hh), abnf.ws(tt))

# newline =  %x0A     ; LF
# newline =/ %x0D.0A  ; CRLF
# (%x0A is 10, %x0D is 13)
def abnf.newline(ss: String) -> Bool:
  match ss:
    case SNil{}:
      False{}
    case SCon{hh, tt}:
      match tt:
        case SNil{}:
          abnf.cp(hh, 10)
        case SCon{h2, t2}:
          Bool.and(abnf.cp(hh, 13), Bool.and(abnf.cp(h2, 10), String.is_empty(t2)))

# [ newline ]: nothing, or a newline
def abnf.opt_newline(ss: String) -> Bool:
  match ss:
    case SNil{}:
      True{}
    case SCon{hh, tt}:
      abnf.newline(SCon{hh, tt})

# non-ascii = %x80-D7FF / %xE000-10FFFF
# (%x80 is 128, %xD7FF is 55295, %xE000 is 57344, %x10FFFF is 1114111)
def abnf.non_ascii(cc: Char) -> Bool:
  match cc:
    case Chr{+cp}:
      Bool.or(abnf.range(cp, 128, 55295), abnf.range(cp, 57344, 1114111))

# non-eol = %x09 / %x20-7F / non-ascii
# (%x09 is 9, %x20 is 32, %x7F is 127)
def abnf.non_eol(cc: Char) -> Bool:
  match cc:
    case Chr{+cp}:
      Bool.or(U32.is_eq(cp, 9), Bool.or(abnf.range(cp, 32, 127), abnf.non_ascii(Chr{cp})))

# comment-start-symbol = %x23 ; #
# comment = comment-start-symbol *non-eol
# over the characters after the # (g.com.text writes the #)
def abnf.comment(ss: String) -> Bool:
  match ss:
    case SNil{}:
      True{}
    case SCon{hh, tt}:
      Bool.and(abnf.non_eol(hh), abnf.comment(tt))

# *( wschar / newline ), the tail of mlb-escaped-nl. A newline is LF or CR
# LF, so a CR is taken with the LF after it
def abnf.ws_newlines(ss: String) -> Bool:
  match ss:
    case SNil{}:
      True{}
    case SCon{+hh, tt}:
      match tt:
        case SNil{}:
          Bool.or(abnf.wschar(hh), abnf.cp(hh, 10))
        case SCon{+h2, +t2}:
          Bool.or(Bool.and(Bool.or(abnf.wschar(hh), abnf.cp(hh, 10)), abnf.ws_newlines(SCon{h2, t2})),
            Bool.and(abnf.cp(hh, 13), Bool.and(abnf.cp(h2, 10), abnf.ws_newlines(t2))))

# Strings. A basic string's pieces are TOML-KEY-3's KPiece: KpChar is a
# basic-unescaped character, KpEsc the seven escape-seq-char letters (KMark),
# and KpU4 and KpU8 the %x75 4HEXDIG and %x55 8HEXDIG forms, each digit a
# KHex, a HEXDIG in either case.

# basic-unescaped = wschar / %x21 / %x23-5B / %x5D-7E / non-ascii
# (%x21 is 33, %x23 is 35, %x5B is 91, %x5D is 93, %x7E is 126)
def abnf.basic_unescaped(cc: Char) -> Bool:
  match cc:
    case Chr{+cp}:
      Bool.or(abnf.wschar(Chr{cp}), Bool.or(U32.is_eq(cp, 33), Bool.or(abnf.range(cp, 35, 91),
        Bool.or(abnf.range(cp, 93, 126), abnf.non_ascii(Chr{cp})))))

# basic-char = basic-unescaped / escaped
# escaped = escape escape-seq-char
# escape = %x5C                   ; \
# escape-seq-char =  %x22         ; "    quotation mark  U+0022
# escape-seq-char =/ %x5C         ; \    reverse solidus U+005C
# escape-seq-char =/ %x62         ; b    backspace       U+0008
# escape-seq-char =/ %x66         ; f    form feed       U+000C
# escape-seq-char =/ %x6E         ; n    line feed       U+000A
# escape-seq-char =/ %x72         ; r    carriage return U+000D
# escape-seq-char =/ %x74         ; t    tab             U+0009
# escape-seq-char =/ %x75 4HEXDIG ; uXXXX                U+XXXX
# escape-seq-char =/ %x55 8HEXDIG ; UXXXXXXXX            U+XXXXXXXX
# every escaped piece is one of these by its type; a character written as
# itself must be basic-unescaped
def abnf.basic_char(pp: KPiece) -> Bool:
  match pp:
    case KpChar{cc}:
      abnf.basic_unescaped(cc)
    case KpEsc{_mm}:
      True{}
    case KpU4{_d, _c, _b, _a}:
      True{}
    case KpU8{_h, _g, _f, _e, _d, _c, _b, _a}:
      True{}

# basic-string = quotation-mark *basic-char quotation-mark
# quotation-mark = %x22            ; "
# over the pieces between the quotation marks
def abnf.basic_string(ps: List<&2, KPiece>) -> Bool:
  match ps:
    case []:
      True{}
    case pp <> rest:
      Bool.and(abnf.basic_char(pp), abnf.basic_string(rest))

# mlb-unescaped = wschar / %x21 / %x23-5B / %x5D-7E / non-ascii
# (the set basic-unescaped is)
def abnf.mlb_unescaped(cc: Char) -> Bool:
  match cc:
    case Chr{+cp}:
      Bool.or(abnf.wschar(Chr{cp}), Bool.or(U32.is_eq(cp, 33), Bool.or(abnf.range(cp, 35, 91),
        Bool.or(abnf.range(cp, 93, 126), abnf.non_ascii(Chr{cp})))))

# mlb-char = mlb-unescaped / escaped
def abnf.mlb_char(pp: KPiece) -> Bool:
  match pp:
    case KpChar{cc}:
      abnf.mlb_unescaped(cc)
    case KpEsc{_mm}:
      True{}
    case KpU4{_d, _c, _b, _a}:
      True{}
    case KpU8{_h, _g, _f, _e, _d, _c, _b, _a}:
      True{}

# mlb-quotes = 1*2quotation-mark
# mlb-content = mlb-char / newline / mlb-escaped-nl
# a piece of a multi-line basic body: an mlb-content (a character or escape,
# a newline as written, or a line-ending backslash) or an mlb-quotes, of one
# quotation mark or of two when two
type GMlb is Data:
  GmChar{pp: KPiece}
  GmNewline{nl: String}
  GmEscapedNl{w1: String, nl: String, more: String}
  GmQuotes{two: Bool}

# mlb-escaped-nl = escape ws newline *( wschar / newline )
# over the ws, the newline and what follows them
def abnf.mlb_escaped_nl(w1: String, nl: String, more: String) -> Bool:
  Bool.and(abnf.ws(w1), Bool.and(abnf.newline(nl), abnf.ws_newlines(more)))

# mlb-content = mlb-char / newline / mlb-escaped-nl
def abnf.mlb_content(pp: GMlb) -> Bool:
  match pp:
    case GmChar{kp}:
      abnf.mlb_char(kp)
    case GmNewline{nl}:
      abnf.newline(nl)
    case GmEscapedNl{w1, nl, more}:
      abnf.mlb_escaped_nl(w1, nl, more)
    case GmQuotes{_two}:
      False{}

# ml-basic-body = *mlb-content *( mlb-quotes 1*mlb-content ) [ mlb-quotes ]
# A list of pieces matches exactly when each is an mlb-content or an
# mlb-quotes and no two mlb-quotes are next to each other; qq says the piece
# before was an mlb-quotes
def abnf.ml_basic_body(ps: List<&2, GMlb>, qq: Bool) -> Bool:
  match ps:
    case []:
      True{}
    case GmQuotes{_two} <> rest:
      Bool.and(Bool.not(qq), abnf.ml_basic_body(rest, True{}))
    case pp <> rest:
      Bool.and(abnf.mlb_content(pp), abnf.ml_basic_body(rest, False{}))

# literal-char = %x09 / %x20-26 / %x28-7E / non-ascii
# (%x09 is 9, %x20 is 32, %x26 is 38, %x28 is 40, %x7E is 126)
def abnf.literal_char(cc: Char) -> Bool:
  match cc:
    case Chr{+cp}:
      Bool.or(U32.is_eq(cp, 9), Bool.or(abnf.range(cp, 32, 38), Bool.or(abnf.range(cp, 40, 126),
        abnf.non_ascii(Chr{cp}))))

# literal-string = apostrophe *literal-char apostrophe
# apostrophe = %x27 ; ' apostrophe
# over the characters between the apostrophes
def abnf.literal_string(ss: String) -> Bool:
  match ss:
    case SNil{}:
      True{}
    case SCon{hh, tt}:
      Bool.and(abnf.literal_char(hh), abnf.literal_string(tt))

# mll-char = %x09 / %x20-26 / %x28-7E / non-ascii
def abnf.mll_char(cc: Char) -> Bool:
  match cc:
    case Chr{+cp}:
      Bool.or(U32.is_eq(cp, 9), Bool.or(abnf.range(cp, 32, 38), Bool.or(abnf.range(cp, 40, 126),
        abnf.non_ascii(Chr{cp}))))

# mll-content = mll-char / newline
# mll-quotes = 1*2apostrophe
# a piece of a multi-line literal body: an mll-content (a character, or a
# newline as written) or an mll-quotes, of one apostrophe or of two when two
type GMll is Data:
  GlChar{cc: Char}
  GlNewline{nl: String}
  GlQuotes{two: Bool}

# mll-content = mll-char / newline
def abnf.mll_content(pp: GMll) -> Bool:
  match pp:
    case GlChar{cc}:
      abnf.mll_char(cc)
    case GlNewline{nl}:
      abnf.newline(nl)
    case GlQuotes{_two}:
      False{}

# ml-literal-body = *mll-content *( mll-quotes 1*mll-content ) [ mll-quotes ]
# as ml-basic-body: no two mll-quotes next to each other
def abnf.ml_literal_body(ps: List<&2, GMll>, qq: Bool) -> Bool:
  match ps:
    case []:
      True{}
    case GlQuotes{_two} <> rest:
      Bool.and(Bool.not(qq), abnf.ml_literal_body(rest, True{}))
    case pp <> rest:
      Bool.and(abnf.mll_content(pp), abnf.ml_literal_body(rest, False{}))

# string = ml-basic-string / basic-string / ml-literal-string / literal-string
# ml-basic-string = ml-basic-string-delim [ newline ] ml-basic-body
#                   ml-basic-string-delim
# ml-basic-string-delim = 3quotation-mark
# ml-literal-string = ml-literal-string-delim [ newline ] ml-literal-body
#                     ml-literal-string-delim
# ml-literal-string-delim = 3apostrophe
# nl is the optional newline after the opening delimiter, "" when there is
# none
type GString is Data:
  GsMlBasic{nl: String, body: List<&2, GMlb>}
  GsBasic{pl: List<&2, KPiece>}
  GsMlLiteral{nl: String, body: List<&2, GMll>}
  GsLiteral{text: String}

# Integer. dec-int, unsigned-dec-int, minus, plus, underscore, digit1-9 and
# DIGIT are the GRAMMAR SPIKE's.

# HEXDIG = DIGIT / "A" / "B" / "C" / "D" / "E" / "F"
# The quoted letters are case-insensitive, so a to f match too
# (%x41 is 65, %x46 is 70, %x61 is 97, %x66 is 102)
def abnf.HEXDIG(cc: Char) -> Bool:
  match cc:
    case Chr{+cp}:
      Bool.or(abnf.digit(cp), Bool.or(abnf.range(cp, 65, 70), abnf.range(cp, 97, 102)))

# digit0-7 = %x30-37                 ; 0-7
# (%x30 is 48, %x37 is 55)
def abnf.digit0_7(cc: Char) -> Bool:
  match cc:
    case Chr{+cp}:
      abnf.range(cp, 48, 55)

# digit0-1 = %x30-31                 ; 0-1
# (%x30 is 48, %x31 is 49)
def abnf.digit0_1(cc: Char) -> Bool:
  match cc:
    case Chr{+cp}:
      abnf.range(cp, 48, 49)

# the digit rule of a prefixed integer: HEXDIG, digit0-7 or digit0-1
type ARadix is Data:
  AHex{}
  AOct{}
  ABin{}

# a character of the radix's digit rule
def abnf.radix_digit(rx: ARadix, cc: Char) -> Bool:
  match rx:
    case AHex{}:
      abnf.HEXDIG(cc)
    case AOct{}:
      abnf.digit0_7(cc)
    case ABin{}:
      abnf.digit0_1(cc)

# *( D / underscore D ), for D the radix's digit rule, as abnf.dec_rep is for
# DIGIT: a lone character left can only be a D
def abnf.radix_rep(cs: List<&2, Char>, +rx: ARadix) -> Bool:
  match cs:
    case []:
      True{}
    case +hh <> tt:
      match tt:
        case []:
          abnf.radix_digit(rx, hh)
        case +h2 <> +t2:
          Bool.or(Bool.and(abnf.radix_digit(rx, hh), abnf.radix_rep(h2 <> t2, rx)),
            Bool.and(abnf.underscore(hh), Bool.and(abnf.radix_digit(rx, h2), abnf.radix_rep(t2, rx))))

# a prefix of 0 and the letter with code point ll, then one D, then
# *( D / underscore D )
def abnf.prefixed(cs: List<&2, Char>, +ll: U32, +rx: ARadix) -> Bool:
  match cs:
    case +c0 <> +c1 <> +c2 <> rest:
      Bool.and(abnf.cp(c0, 48), Bool.and(abnf.cp(c1, ll), Bool.and(abnf.radix_digit(rx, c2),
        abnf.radix_rep(rest, rx))))
    case _:
      False{}

# hex-int = hex-prefix HEXDIG *( HEXDIG / underscore HEXDIG )
# hex-prefix = %x30.78               ; 0x
# (%x78 is 120; a %x string, so 0X is no prefix)
def abnf.hex_int(cs: List<&2, Char>) -> Bool:
  abnf.prefixed(cs, 120, AHex{})

# oct-int = oct-prefix digit0-7 *( digit0-7 / underscore digit0-7 )
# oct-prefix = %x30.6F               ; 0o
# (%x6F is 111)
def abnf.oct_int(cs: List<&2, Char>) -> Bool:
  abnf.prefixed(cs, 111, AOct{})

# bin-int = bin-prefix digit0-1 *( digit0-1 / underscore digit0-1 )
# bin-prefix = %x30.62               ; 0b
# (%x62 is 98)
def abnf.bin_int(cs: List<&2, Char>) -> Bool:
  abnf.prefixed(cs, 98, ABin{})

# integer = dec-int / hex-int / oct-int / bin-int
def abnf.integer(+cs: List<&2, Char>) -> Bool:
  Bool.or(abnf.dec_int(cs), Bool.or(abnf.hex_int(cs), Bool.or(abnf.oct_int(cs), abnf.bin_int(cs))))

# Float.

# decimal-point = %x2E               ; .
# (%x2E is 46)
def abnf.decimal_point(cc: Char) -> Bool:
  abnf.cp(cc, 46)

# the "e" of exp: a quoted string, so e or E
# (%x65 is 101, %x45 is 69)
def abnf.e(+cc: Char) -> Bool:
  Bool.or(abnf.cp(cc, 101), abnf.cp(cc, 69))

# where a float's parts are cut: at the first decimal-point or e (Dot), or at
# the first e (Exp)
type ACut is Data:
  ACutDot{}
  ACutExp{}

# whether a character is where the cut falls
def abnf.cut.at(ct: ACut, +cc: Char) -> Bool:
  match ct:
    case ACutDot{}:
      Bool.or(abnf.decimal_point(cc), abnf.e(cc))
    case ACutExp{}:
      abnf.e(cc)

# a character kept before the cut, or the cut reached
def abnf.cut.pre.pick(at: Bool, cc: Char, rest: List<&2, Char>) -> List<&2, Char>:
  match at:
    case True{}:
      []
    case False{}:
      cc <> rest

# the characters before the cut
def abnf.cut.pre(cs: List<&2, Char>, +ct: ACut) -> List<&2, Char>:
  match cs:
    case []:
      []
    case +hh <> tt:
      abnf.cut.pre.pick(abnf.cut.at(ct, hh), hh, abnf.cut.pre(tt, ct))

# the characters after a kept one, or all of them from the cut on
def abnf.cut.post.pick(at: Bool, cc: Char, tt: List<&2, Char>, rest: List<&2, Char>) -> List<&2, Char>:
  match at:
    case True{}:
      cc <> tt
    case False{}:
      rest

# the characters from the cut on, the cut's character first; none when there
# is no cut
def abnf.cut.post(cs: List<&2, Char>, +ct: ACut) -> List<&2, Char>:
  match cs:
    case []:
      []
    case +hh <> +tt:
      abnf.cut.post.pick(abnf.cut.at(ct, hh), hh, tt, abnf.cut.post(tt, ct))

# zero-prefixable-int = DIGIT *( DIGIT / underscore DIGIT )
def abnf.zero_prefixable_int(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      False{}
    case hh <> tt:
      Bool.and(abnf.DIGIT(hh), abnf.dec_rep(tt))

# frac = decimal-point zero-prefixable-int
def abnf.frac(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      False{}
    case hh <> tt:
      Bool.and(abnf.decimal_point(hh), abnf.zero_prefixable_int(tt))

# float-exp-part = [ minus / plus ] zero-prefixable-int
def abnf.float_exp_part(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      False{}
    case +hh <> +tt:
      Bool.or(Bool.and(Bool.or(abnf.minus(hh), abnf.plus(hh)), abnf.zero_prefixable_int(tt)),
        abnf.zero_prefixable_int(hh <> tt))

# exp = "e" float-exp-part
def abnf.exp(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      False{}
    case hh <> tt:
      Bool.and(abnf.e(hh), abnf.float_exp_part(tt))

# [ exp ]: nothing, or an exp
def abnf.opt_exp(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      True{}
    case hh <> tt:
      abnf.exp(hh <> tt)

# frac [ exp ], cut at the first e: a frac holds none, so no other cut can
# match
def abnf.frac_exp(+cs: List<&2, Char>) -> Bool:
  Bool.and(abnf.frac(abnf.cut.pre(cs, ACutExp{})), abnf.opt_exp(abnf.cut.post(cs, ACutExp{})))

# float-int-part = dec-int
def abnf.float_int_part(cs: List<&2, Char>) -> Bool:
  abnf.dec_int(cs)

# float = float-int-part ( exp / frac [ exp ] ), cut at the first
# decimal-point or e: a float-int-part (a dec-int) holds neither, and exp and
# frac each start with one, so no other cut can match
def abnf.float_std(+cs: List<&2, Char>) -> Bool:
  +post = abnf.cut.post(cs, ACutDot{})
  Bool.and(abnf.float_int_part(abnf.cut.pre(cs, ACutDot{})), Bool.or(abnf.exp(post), abnf.frac_exp(post)))

# inf = %x69.6e.66  ; inf
def abnf.inf(cs: List<&2, Char>) -> Bool:
  abnf.chars_are(cs, "inf")

# nan = %x6e.61.6e  ; nan
def abnf.nan(cs: List<&2, Char>) -> Bool:
  abnf.chars_are(cs, "nan")

# special-float = [ minus / plus ] ( inf / nan )
def abnf.special_float(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      False{}
    case +hh <> +tt:
      Bool.or(Bool.and(Bool.or(abnf.minus(hh), abnf.plus(hh)), Bool.or(abnf.inf(tt), abnf.nan(tt))),
        Bool.or(abnf.inf(hh <> tt), abnf.nan(hh <> tt)))

# float = float-int-part ( exp / frac [ exp ] )
# float =/ special-float
def abnf.float(+cs: List<&2, Char>) -> Bool:
  Bool.or(abnf.float_std(cs), abnf.special_float(cs))

# Boolean.

# true    = %x74.72.75.65     ; true
def abnf.true(cs: List<&2, Char>) -> Bool:
  abnf.chars_are(cs, "true")

# false   = %x66.61.6C.73.65  ; false
def abnf.false(cs: List<&2, Char>) -> Bool:
  abnf.chars_are(cs, "false")

# boolean = true / false
def abnf.boolean(+cs: List<&2, Char>) -> Bool:
  Bool.or(abnf.true(cs), abnf.false(cs))

# Date and Time. Each rule is read from the front of a word and gives what is
# left of it (ALeft), or no match (ANone). Every alternative and option here
# is told apart by its first character, so at most one way can match.

# what is left of a word after a rule matched a prefix of it, or no match
type ARest is Data:
  ALeft{cs: List<&2, Char>}
  ANone{}

# the rest after a character that passed a test
def abnf.keep(ok: Bool, tt: List<&2, Char>) -> ARest:
  match ok:
    case True{}:
      ALeft{tt}
    case False{}:
      ANone{}

# DIGIT, from the front
def abnf.digit_r(rr: ARest) -> ARest:
  match rr:
    case ALeft{cs}:
      match cs:
        case []:
          ANone{}
        case hh <> tt:
          abnf.keep(abnf.DIGIT(hh), tt)
    case ANone{}:
      ANone{}

# the character with code point nn, from the front: a %x character, or a
# quoted one that is no letter
def abnf.char_r(rr: ARest, +nn: U32) -> ARest:
  match rr:
    case ALeft{cs}:
      match cs:
        case []:
          ANone{}
        case hh <> tt:
          abnf.keep(abnf.cp(hh, nn), tt)
    case ANone{}:
      ANone{}

# a quoted letter, from the front: its upper case (code point up) or its
# lower case (low)
def abnf.letter_r(rr: ARest, +up: U32, +low: U32) -> ARest:
  match rr:
    case ALeft{cs}:
      match cs:
        case []:
          ANone{}
        case +hh <> tt:
          abnf.keep(Bool.or(abnf.cp(hh, up), abnf.cp(hh, low)), tt)
    case ANone{}:
      ANone{}

# the first of two alternatives that matched
def abnf.or_r(aa: ARest, bb: ARest) -> ARest:
  match aa:
    case ALeft{cs}:
      ALeft{cs}
    case ANone{}:
      bb

# whether a rule matched the whole word
def abnf.all_r(rr: ARest) -> Bool:
  match rr:
    case ALeft{cs}:
      List.is_empty(&2, Char, cs)
    case ANone{}:
      False{}

# a word with its leading DIGITs taken off, or kept when the first is none
def abnf.drop_digits.pick(dg: Bool, hh: Char, tt: List<&2, Char>, after: List<&2, Char>) -> List<&2, Char>:
  match dg:
    case True{}:
      after
    case False{}:
      hh <> tt

# the word after its leading DIGITs
def abnf.drop_digits(cs: List<&2, Char>) -> List<&2, Char>:
  match cs:
    case []:
      []
    case +hh <> +tt:
      abnf.drop_digits.pick(abnf.DIGIT(hh), hh, tt, abnf.drop_digits(tt))

# 1*DIGIT, taking every DIGIT there is: in a date-time what follows it is a
# time-offset or the end, which starts with no DIGIT
def abnf.digits1_r(rr: ARest) -> ARest:
  match rr:
    case ALeft{cs}:
      match cs:
        case []:
          ANone{}
        case +hh <> +tt:
          abnf.keep(abnf.DIGIT(hh), abnf.drop_digits(tt))
    case ANone{}:
      ANone{}

# date-fullyear  = 4DIGIT
def abnf.date_fullyear(rr: ARest) -> ARest:
  abnf.digit_r(abnf.digit_r(abnf.digit_r(abnf.digit_r(rr))))

# date-month     = 2DIGIT  ; 01-12
# (the range is prose.date_time_in_range's)
def abnf.date_month(rr: ARest) -> ARest:
  abnf.digit_r(abnf.digit_r(rr))

# date-mday      = 2DIGIT  ; 01-28, 01-29, 01-30, 01-31 based on month/year
def abnf.date_mday(rr: ARest) -> ARest:
  abnf.digit_r(abnf.digit_r(rr))

# time-delim     = "T" / %x20 ; T, t, or space
# (%x54 is 84, %x74 is 116, %x20 is 32)
def abnf.time_delim(+rr: ARest) -> ARest:
  abnf.or_r(abnf.letter_r(rr, 84, 116), abnf.char_r(rr, 32))

# time-hour      = 2DIGIT  ; 00-23
def abnf.time_hour(rr: ARest) -> ARest:
  abnf.digit_r(abnf.digit_r(rr))

# time-minute    = 2DIGIT  ; 00-59
def abnf.time_minute(rr: ARest) -> ARest:
  abnf.digit_r(abnf.digit_r(rr))

# time-second    = 2DIGIT  ; 00-58, 00-59, 00-60 based on leap second rules
def abnf.time_second(rr: ARest) -> ARest:
  abnf.digit_r(abnf.digit_r(rr))

# time-secfrac   = "." 1*DIGIT
# (%x2E is 46)
def abnf.time_secfrac(rr: ARest) -> ARest:
  abnf.digits1_r(abnf.char_r(rr, 46))

# time-numoffset = ( "+" / "-" ) time-hour ":" time-minute
# (%x2B is 43, %x2D is 45, %x3A is 58)
def abnf.time_numoffset(+rr: ARest) -> ARest:
  abnf.time_minute(abnf.char_r(abnf.time_hour(abnf.or_r(abnf.char_r(rr, 43), abnf.char_r(rr, 45))), 58))

# time-offset    = "Z" / time-numoffset
# (%x5A is 90, %x7A is 122)
def abnf.time_offset(+rr: ARest) -> ARest:
  abnf.or_r(abnf.letter_r(rr, 90, 122), abnf.time_numoffset(rr))

# a time-secfrac when the word goes on with ".", and nothing otherwise
def abnf.opt_secfrac.pick(dot: Bool, cs: List<&2, Char>) -> ARest:
  match dot:
    case True{}:
      abnf.time_secfrac(ALeft{cs})
    case False{}:
      ALeft{cs}

# [ time-secfrac ]: taken when the next character is ".", since what follows
# a partial-time (a time-offset or the end) never starts with one
def abnf.opt_secfrac(rr: ARest) -> ARest:
  match rr:
    case ALeft{cs}:
      match cs:
        case []:
          ALeft{[]}
        case +hh <> +tt:
          abnf.opt_secfrac.pick(abnf.cp(hh, 46), hh <> tt)
    case ANone{}:
      ANone{}

# partial-time   = time-hour ":" time-minute ":" time-second [ time-secfrac ]
def abnf.partial_time(rr: ARest) -> ARest:
  abnf.opt_secfrac(abnf.time_second(abnf.char_r(abnf.time_minute(abnf.char_r(abnf.time_hour(rr), 58)), 58)))

# full-date      = date-fullyear "-" date-month "-" date-mday
def abnf.full_date(rr: ARest) -> ARest:
  abnf.date_mday(abnf.char_r(abnf.date_month(abnf.char_r(abnf.date_fullyear(rr), 45)), 45))

# full-time      = partial-time time-offset
def abnf.full_time(rr: ARest) -> ARest:
  abnf.time_offset(abnf.partial_time(rr))

# offset-date-time = full-date time-delim full-time
def abnf.offset_date_time(rr: ARest) -> ARest:
  abnf.full_time(abnf.time_delim(abnf.full_date(rr)))

# local-date-time = full-date time-delim partial-time
def abnf.local_date_time(rr: ARest) -> ARest:
  abnf.partial_time(abnf.time_delim(abnf.full_date(rr)))

# local-date = full-date
def abnf.local_date(rr: ARest) -> ARest:
  abnf.full_date(rr)

# local-time = partial-time
def abnf.local_time(rr: ARest) -> ARest:
  abnf.partial_time(rr)

# date-time      = offset-date-time / local-date-time / local-date / local-time
# a whole word matches one of the four
def abnf.date_time(+cs: List<&2, Char>) -> Bool:
  Bool.or(abnf.all_r(abnf.offset_date_time(ALeft{cs})), Bool.or(abnf.all_r(abnf.local_date_time(ALeft{cs})),
    Bool.or(abnf.all_r(abnf.local_date(ALeft{cs})), abnf.all_r(abnf.local_time(ALeft{cs})))))

# The four restrictions the specification's prose adds to toml.abnf
# (REVIEW-G1), each with its sentence of TOML v1.0.0.

# the largest integer, 2^63 - 1, and the largest magnitude of a negative one,
# 2^63, in decimal
def prose.i64.limit(sign: T.Sign) -> String:
  match sign:
    case T.Plus{}:
      "9223372036854775807"
    case T.Minus{}:
      "9223372036854775808"

# the first differing digit decides; a tie keeps what came before
def prose.dec_le.ord(seen: Cmp, now: Cmp) -> Cmp:
  match seen:
    case EQ{}:
      now
    case LT{}:
      LT{}
    case GT{}:
      GT{}

# whether a string of decimal digits with no leading zero is at most the
# limit: shorter is less, longer is more, and the same length compares digit
# by digit from the most significant
def prose.dec_le(ds: String, lim: String, ord: Cmp) -> Bool:
  match ds lim:
    case SNil{} SNil{}:
      Cmp.is_le(ord)
    case SNil{} SCon{_h, _t}:
      True{}
    case SCon{_h, _t} SNil{}:
      False{}
    case SCon{xx, xt} SCon{yy, yt}:
      prose.dec_le(xt, yt, prose.dec_le.ord(ord, U32.cmp(Char.to_u32(xx), Char.to_u32(yy))))

# a leading underscore or zero dropped, or the rest kept as it is, its
# underscores removed
def prose.sig.pick(skip: Bool, hh: Char, tt: List<&2, Char>, after: List<&2, Char>) -> List<&2, Char>:
  match skip:
    case True{}:
      after
    case False{}:
      String.to_list(abnf.no_us(hh <> tt))

# a numeral's characters with its underscores and leading zeros removed: its
# significant digits
def prose.sig(cs: List<&2, Char>) -> List<&2, Char>:
  match cs:
    case []:
      []
    case +hh <> +tt:
      prose.sig.pick(Bool.or(abnf.underscore(hh), abnf.cp(hh, 48)), hh, tt, prose.sig(tt))

# whether a list starts with a digit from 0 to 7
def prose.first_le7(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      True{}
    case hh <> _tt:
      abnf.digit0_7(hh)

# whether significant digits in a radix are at most 2^63 - 1: in hexadecimal
# 7FFFFFFFFFFFFFFF, at most 15 digits or 16 whose first is at most 7; in
# octal 777777777777777777777, at most 21 digits; in binary, at most 63
def prose.radix_fits(rx: ARadix, +nn: Nat, sig: List<&2, Char>) -> Bool:
  match rx:
    case AHex{}:
      Bool.or(Nat.is_lt(nn, 16n), Bool.and(Nat.is_eq(nn, 16n), prose.first_le7(sig)))
    case AOct{}:
      Nat.is_le(nn, 21n)
    case ABin{}:
      Nat.is_le(nn, 63n)

# the significant digits after a two-character prefix, against the radix's
# bound
def prose.radix_in_range(rx: ARadix, +cs: List<&2, Char>) -> Bool:
  +sig = prose.sig(List.drop(&2, Char, cs, 2n))
  prose.radix_fits(rx, List.length(&2, Char, sig), sig)

# the range of a prefixed integer, by its radix, or of a dec-int: its digits
# against the limit of its sign
def prose.int_in_range.pick(hx: Bool, oc: Bool, bi: Bool, +cs: List<&2, Char>) -> Bool:
  match hx oc bi:
    case True{} _o _b:
      prose.radix_in_range(AHex{}, cs)
    case False{} True{} _b:
      prose.radix_in_range(AOct{}, cs)
    case False{} False{} True{}:
      prose.radix_in_range(ABin{}, cs)
    case False{} False{} False{}:
      prose.dec_le(abnf.dec_digits(cs), prose.i64.limit(abnf.dec_sign(cs)), EQ{})

# TOML v1.0.0, Integer: "Arbitrary 64-bit signed integers (from -2^63 to
# 2^63-1) should be accepted and handled losslessly. If an integer cannot be
# represented losslessly, an error must be thrown." Over an integer word: a
# dec-int's digits (its sign and underscores removed; unsigned-dec-int has no
# leading zero) against the limit of its sign, and a prefixed one's
# significant digits against 2^63 - 1 in its radix (TOML-NUM-1)
def prose.int_in_range(+cs: List<&2, Char>) -> Bool:
  prose.int_in_range.pick(abnf.hex_int(cs), abnf.oct_int(cs), abnf.bin_int(cs), cs)

# the value of a DIGIT, as a U32
def g.dig(cc: Char) -> U32:
  U32.sub(Char.to_u32(cc), 48)

# the number two DIGITs at the front of a word write
def g.two(cs: List<&2, Char>) -> U32:
  match cs:
    case aa <> bb <> _rest:
      U32.add(U32.mul(g.dig(aa), 10), g.dig(bb))
    case _:
      0

# the number four DIGITs at the front of a word write
def g.four(cs: List<&2, Char>) -> U32:
  match cs:
    case aa <> bb <> cc <> dd <> _rest:
      U32.add(U32.mul(U32.add(U32.mul(U32.add(U32.mul(g.dig(aa), 10), g.dig(bb)), 10), g.dig(cc)), 10),
        g.dig(dd))
    case _:
      0

# the word's leading DIGITs
def g.take_digits.pick(dg: Bool, hh: Char, after: List<&2, Char>) -> List<&2, Char>:
  match dg:
    case True{}:
      hh <> after
    case False{}:
      []

# the word's leading DIGITs
def g.take_digits(cs: List<&2, Char>) -> List<&2, Char>:
  match cs:
    case []:
      []
    case +hh <> tt:
      g.take_digits.pick(abnf.DIGIT(hh), hh, g.take_digits(tt))

# Z, or an offset of the sign minus when mm, else plus
def g.dt.zone.pick(mm: Bool, zz: Bool, +tt: List<&2, Char>) -> T.Zone:
  match zz:
    case True{}:
      T.Zulu{}
    case False{}:
      T.Shift{abnf.sign.pick(mm), g.two(tt), g.two(List.drop(&2, Char, tt, 3n))}

# the time-offset at the front of a word: Z or z, or a sign, two digits, a
# colon and two digits
def g.dt.zone(cs: List<&2, Char>) -> T.Zone:
  match cs:
    case +hh <> +tt:
      g.dt.zone.pick(abnf.cp(hh, 45), Bool.or(abnf.cp(hh, 90), abnf.cp(hh, 122)), tt)
    case []:
      T.Zulu{}

# the digits after a ".", or none
def g.dt.frac.pick(dot: Bool, tt: List<&2, Char>) -> String:
  match dot:
    case True{}:
      String.from_list(g.take_digits(tt))
    case False{}:
      ""

# the fraction's digits after a partial-time's seconds, "" when the word goes
# on with no ".", and the rest after them
def g.dt.frac(cs: List<&2, Char>) -> String:
  match cs:
    case +hh <> tt:
      g.dt.frac.pick(abnf.cp(hh, 46), tt)
    case []:
      ""

# the word after "." and its digits, or the word as it is
def g.dt.after_frac.pick(dot: Bool, hh: Char, tt: List<&2, Char>) -> List<&2, Char>:
  match dot:
    case True{}:
      abnf.drop_digits(tt)
    case False{}:
      hh <> tt

# what follows the fraction, if there is one
def g.dt.after_frac(cs: List<&2, Char>) -> List<&2, Char>:
  match cs:
    case +hh <> +tt:
      g.dt.after_frac.pick(abnf.cp(hh, 46), hh, tt)
    case []:
      []

# the partial-time at the front of a word: hour, minute, second, fraction
def g.dt.clock(+cs: List<&2, Char>) -> T.Clock:
  T.Clock{g.two(cs), g.two(List.drop(&2, Char, cs, 3n)), g.two(List.drop(&2, Char, cs, 6n)),
    g.dt.frac(List.drop(&2, Char, cs, 8n))}

# the full-date at the front of a word: year, month, day
def g.dt.date(+cs: List<&2, Char>) -> T.Date:
  T.Date{g.four(cs), g.two(List.drop(&2, Char, cs, 5n)), g.two(List.drop(&2, Char, cs, 8n))}

# a word's third character, or U+0000
def g.dt.third(cs: List<&2, Char>) -> Char:
  match cs:
    case _a <> _b <> cc <> _rest:
      cc
    case _:
      Chr{0}

# a local-date-time when nothing follows the partial-time, and an
# offset-date-time with the time-offset that does
def g.dt.zoned(date: T.Date, clock: T.Clock, +zz: List<&2, Char>) -> T.When:
  match zz:
    case []:
      T.WLocal{date, clock}
    case _h <> _t:
      T.WOff{date, clock, g.dt.zone(zz)}

# a local-time, a local-date, or a date with a time after it
def g.dt.when.pick(colon: Bool, +cs: List<&2, Char>, +tm: List<&2, Char>, dateonly: Bool) -> T.When:
  match colon dateonly:
    case True{} _d:
      T.WTime{g.dt.clock(cs)}
    case False{} True{}:
      T.WDate{g.dt.date(cs)}
    case False{} False{}:
      g.dt.zoned(g.dt.date(cs), g.dt.clock(tm), g.dt.after_frac(List.drop(&2, Char, tm, 8n)))

# the datetime a date-time word writes: a local-time when its third
# character is ":", and otherwise a full-date, then nothing (a local-date), or
# a time-delim, a partial-time and a time-offset or nothing
def g.dt.when(+cs: List<&2, Char>) -> T.When:
  g.dt.when.pick(abnf.cp(g.dt.third(cs), 58), cs, List.drop(&2, Char, cs, 11n),
    List.is_empty(&2, Char, List.drop(&2, Char, cs, 10n)))

# the month the test names when it holds, and the other otherwise
def prose.month.pick(hit: Bool, mm: Month, other: Month) -> Month:
  match hit:
    case True{}:
      mm
    case False{}:
      other

# the month a number from 1 to 12 names (January otherwise; the range check
# asks for 1 to 12 first)
def prose.month(+mo: U32) -> Month:
  prose.month.pick(U32.is_eq(mo, 2), Feb{}, prose.month.pick(U32.is_eq(mo, 3), Mar{},
    prose.month.pick(U32.is_eq(mo, 4), Apr{}, prose.month.pick(U32.is_eq(mo, 5), May{},
    prose.month.pick(U32.is_eq(mo, 6), Jun{}, prose.month.pick(U32.is_eq(mo, 7), Jul{},
    prose.month.pick(U32.is_eq(mo, 8), Aug{}, prose.month.pick(U32.is_eq(mo, 9), Sep{},
    prose.month.pick(U32.is_eq(mo, 10), Oct{}, prose.month.pick(U32.is_eq(mo, 11), Nov{},
    prose.month.pick(U32.is_eq(mo, 12), Dec{}, Jan{})))))))))))

# a full-date in range: month 1 to 12, day 1 to the days of its month in its
# year (RFC 3339, section 5.7, as days_in transcribes it)
def prose.date_ok(dd: T.Date) -> Bool:
  match dd:
    case T.Date{+yy, +mo, +dy}:
      Bool.and(abnf.range(mo, 1, 12), Bool.and(U32.is_ge(dy, 1), U32.is_le(dy, days_in(yy, prose.month(mo)))))

# a partial-time in range: hour 0 to 23, minute 0 to 59, second 0 to 60
def prose.clock_ok(cl: T.Clock) -> Bool:
  match cl:
    case T.Clock{hh, mi, ss, _frac}:
      Bool.and(U32.is_le(hh, 23), Bool.and(U32.is_le(mi, 59), U32.is_le(ss, 60)))

# a time-offset in range: hours 0 to 23 and minutes 0 to 59
def prose.zone_ok(zz: T.Zone) -> Bool:
  match zz:
    case T.Zulu{}:
      True{}
    case T.Shift{_sign, hh, mi}:
      Bool.and(U32.is_le(hh, 23), U32.is_le(mi, 59))

# every field of a datetime in range
def prose.when_ok(ww: T.When) -> Bool:
  match ww:
    case T.WOff{date, clock, zone}:
      Bool.and(prose.date_ok(date), Bool.and(prose.clock_ok(clock), prose.zone_ok(zone)))
    case T.WLocal{date, clock}:
      Bool.and(prose.date_ok(date), prose.clock_ok(clock))
    case T.WDate{date}:
      prose.date_ok(date)
    case T.WTime{clock}:
      prose.clock_ok(clock)

# toml.abnf gives RFC 3339's ranges only in comments (date-month ; 01-12,
# date-mday ; 01-28, 01-29, 01-30, 01-31 based on month/year, time-hour ;
# 00-23, time-minute ; 00-59, time-second ; 00-58, 00-59, 00-60 based on leap
# second rules), and TOML v1.0.0 asks for RFC 3339 datetimes. Over a
# date-time word: every field within its range (TOML-TIME-1)
def prose.date_time_in_range(+cs: List<&2, Char>) -> Bool:
  prose.when_ok(g.dt.when(cs))

# TOML v1.0.0, String: "Any Unicode character may be escaped with the \uXXXX
# or \UXXXXXXXX forms. The escape codes must be valid Unicode scalar values."
# A \u or \U escape's digits name a scalar value (k3.scalar)
def prose.escape_scalar(pp: KPiece) -> Bool:
  match pp:
    case KpChar{_cc}:
      True{}
    case KpEsc{_mm}:
      True{}
    case KpU4{dd, cc, bb, aa}:
      k3.scalar(k3.hex4(dd, cc, bb, aa))
    case KpU8{hh, gg, ff, ee, dd, cc, bb, aa}:
      k3.scalar(k3.hex8(hh, gg, ff, ee, dd, cc, bb, aa))

# every escape of a basic string's pieces names a scalar value
def prose.escapes_scalar(ps: List<&2, KPiece>) -> Bool:
  match ps:
    case []:
      True{}
    case pp <> rest:
      Bool.and(prose.escape_scalar(pp), prose.escapes_scalar(rest))

# every escape of a multi-line basic body names a scalar value
def prose.mlb_escapes_scalar(ps: List<&2, GMlb>) -> Bool:
  match ps:
    case []:
      True{}
    case GmChar{kp} <> rest:
      Bool.and(prose.escape_scalar(kp), prose.mlb_escapes_scalar(rest))
    case _pp <> rest:
      prose.mlb_escapes_scalar(rest)

# TOML v1.0.0, Comment: "Control characters other than tab (U+0000 to
# U+0008, U+000A to U+001F, U+007F) are not permitted in comments."
# non-eol already leaves out every control but U+007F (%x7F is 127)
def prose.comment_char(cc: Char) -> Bool:
  Bool.not(abnf.cp(cc, 127))

# no character of a comment is U+007F
def prose.comment_chars(ss: String) -> Bool:
  match ss:
    case SNil{}:
      True{}
    case SCon{hh, tt}:
      Bool.and(prose.comment_char(hh), prose.comment_chars(tt))

# Keys. simple-key is TOML-KEY-3's KSeg: KsBare an unquoted-key, KsBasic a
# basic-string of pieces and KsLit a literal-string of characters.

# dot-sep   = ws %x2E ws  ; . Period
# a dot-sep and the simple-key after it: the ws before the dot, the ws after
# it, and the key
type GDotSep is Data:
  GDotSep{w1: String, w2: String, sk: KSeg}

# key = simple-key / dotted-key
# dotted-key = simple-key 1*( dot-sep simple-key )
type GKey is Data:
  GSimpleKey{sk: KSeg}
  GDottedKey{sk: KSeg, more: List<&2, GDotSep>}

# simple-key = quoted-key / unquoted-key
# quoted-key = basic-string / literal-string
# unquoted-key = 1*( ALPHA / DIGIT / %x2D / %x5F ) ; A-Z / a-z / 0-9 / - / _
# (abnf.unquoted_key, TOML-KEY-1), with the escape restriction on a basic one
def g.ok.seg(sg: KSeg) -> Bool:
  match sg:
    case KsBare{name}:
      abnf.unquoted_key(name)
    case KsBasic{+pl}:
      Bool.and(abnf.basic_string(pl), prose.escapes_scalar(pl))
    case KsLit{name}:
      abnf.literal_string(name)

# 1*( dot-sep simple-key )'s every part; at least one is the key's own test
def g.ok.dots(ds: List<&2, GDotSep>) -> Bool:
  match ds:
    case []:
      True{}
    case GDotSep{w1, w2, sk} <> rest:
      Bool.and(abnf.ws(w1), Bool.and(abnf.ws(w2), Bool.and(g.ok.seg(sk), g.ok.dots(rest))))

# key = simple-key / dotted-key: a dotted key has at least one dot-sep
def g.ok.key(kk: GKey) -> Bool:
  match kk:
    case GSimpleKey{sk}:
      g.ok.seg(sk)
    case GDottedKey{sk, +more}:
      Bool.and(Bool.not(List.is_empty(&2, GDotSep, more)), Bool.and(g.ok.seg(sk), g.ok.dots(more)))

# the names of a key's segments, in order
def g.dots.names(ds: List<&2, GDotSep>) -> List<&2, String>:
  match ds:
    case []:
      []
    case GDotSep{_w1, _w2, sk} <> rest:
      k3.seg.name(sk) <> g.dots.names(rest)

# the names of a key's segments, in order: each its characters, a basic
# one's escapes decoded
def g.key.names(kk: GKey) -> List<&2, String>:
  match kk:
    case GSimpleKey{sk}:
      [k3.seg.name(sk)]
    case GDottedKey{sk, more}:
      k3.seg.name(sk) <> g.dots.names(more)

# Arrays, inline tables and comments.

# [ comment ]: none, or a comment of the characters after the #
type GCom is Data:
  GcNone{}
  GcSome{body: String}

# ws-comment-newline = *( wschar / [ comment ] newline ): one wschar, or a
# newline with the comment before it
type GWcn is Data:
  GwWschar{cc: Char}
  GwNewline{com: GCom, nl: String}

# val = string / boolean / array / inline-table / date-time / float / integer
# array = array-open [ array-values ] ws-comment-newline array-close
# array-values =  ws-comment-newline val ws-comment-newline array-sep array-values
# array-values =/ ws-comment-newline val ws-comment-newline [ array-sep ]
# inline-table = inline-table-open [ inline-table-keyvals ] inline-table-close
# inline-table-keyvals = keyval [ inline-table-sep inline-table-keyvals ]
# keyval = key keyval-sep val
# These rules are mutually recursive, so they are one type. The first eight
# constructors spell val's alternatives (an empty array or inline table is
# its own constructor, for the option left out); GArrayValues and
# GArrayValuesLast spell array-values; GInlineTableKeyvals and
# GInlineTableKeyvalsLast spell inline-table-keyvals; GKeyval spells keyval.
# A bare value is its characters; the whitespace around brackets, commas and
# the equals sign is ws, or ws-comment-newline inside an array.
type GVal is Data:
  GvString{st: GString}
  GvBoolean{cs: List<&2, Char>}
  GvArrayEmpty{wn: List<&2, GWcn>}
  GvArray{vals: GVal, wn: List<&2, GWcn>}
  GvInlineTableEmpty{w1: String, w2: String}
  GvInlineTable{w1: String, kvs: GVal, w2: String}
  GvDateTime{cs: List<&2, Char>}
  GvFloat{cs: List<&2, Char>}
  GvInteger{cs: List<&2, Char>}
  GArrayValues{wa: List<&2, GWcn>, val: GVal, wb: List<&2, GWcn>, rest: GVal}
  GArrayValuesLast{wa: List<&2, GWcn>, val: GVal, wb: List<&2, GWcn>, sep: Bool}
  GInlineTableKeyvals{kv: GVal, w1: String, w2: String, rest: GVal}
  GInlineTableKeyvalsLast{kv: GVal}
  GKeyval{key: GKey, w1: String, w2: String, val: GVal}

# which of the mutually recursive rules a GVal node spells
type GRule is Data:
  RVal{}
  RArrayValues{}
  RInlineTableKeyvals{}
  RKeyval{}

# Tables and the document.

# table = std-table / array-table
# std-table = std-table-open key std-table-close
# std-table-open  = %x5B ws     ; [ Left square bracket
# std-table-close = ws %x5D     ; ] Right square bracket
# array-table = array-table-open key array-table-close
# array-table-open  = %x5B.5B ws  ; [[ Double left square bracket
# array-table-close = ws %x5D.5D  ; ]] Double right square bracket
# the ws after the opening brackets, the key, and the ws before the closing
type GTable is Data:
  GStdTable{w1: String, key: GKey, w2: String}
  GArrayTable{w1: String, key: GKey, w2: String}

# expression =  ws [ comment ]
# expression =/ ws keyval ws [ comment ]
# expression =/ ws table ws [ comment ]
# (the keyval is a GKeyval)
type GExpr is Data:
  GxBlank{w1: String, com: GCom}
  GxKeyval{w1: String, kv: GVal, w2: String, com: GCom}
  GxTable{w1: String, tb: GTable, w2: String, com: GCom}

# newline expression: one of toml's *( newline expression )
type GLine is Data:
  GLine{nl: String, ex: GExpr}

# toml = expression *( newline expression )
type Gd is Data:
  GToml{first: GExpr, rest: List<&2, GLine>}

# A leading byte-order mark.

# the rest after a byte-order mark, or the text as it is
def bom.drop.pick(bom: Bool, hh: Char, tt: String) -> String:
  match bom:
    case True{}:
      tt
    case False{}:
      SCon{hh, tt}

# the text with one leading U+FEFF taken off: the encoding's signature, not
# text (REVIEW-G1); toml-test's valid utf8-bom cases start with one
# (65279 is %xFEFF)
def bom.drop(ss: String) -> String:
  match ss:
    case SNil{}:
      SNil{}
    case SCon{+hh, tt}:
      bom.drop.pick(abnf.cp(hh, 65279), hh, tt)

# g.text: the text a derivation spells. Each def writes its part, then tail.

# a comment, if there is one: the # and its characters
def g.com.text(cm: GCom, tail: String) -> String:
  match cm:
    case GcNone{}:
      tail
    case GcSome{body}:
      SCon{'#', String.append(body, tail)}

# ws-comment-newline's text
def g.wcn.text(ws: List<&2, GWcn>, tail: String) -> String:
  match ws:
    case []:
      tail
    case GwWschar{cc} <> rest:
      SCon{cc, g.wcn.text(rest, tail)}
    case GwNewline{com, nl} <> rest:
      g.com.text(com, String.append(nl, g.wcn.text(rest, tail)))

# a key's dot-seps and simple-keys after its first
def g.dots.text(ds: List<&2, GDotSep>, tail: String) -> String:
  match ds:
    case []:
      tail
    case GDotSep{w1, w2, sk} <> rest:
      String.append(w1, SCon{'.', String.append(w2, k3.seg.text(sk, g.dots.text(rest, tail)))})

# a key's text
def g.key.text(kk: GKey, tail: String) -> String:
  match kk:
    case GSimpleKey{sk}:
      k3.seg.text(sk, tail)
    case GDottedKey{sk, more}:
      k3.seg.text(sk, g.dots.text(more, tail))

# mlb-quotes: one quotation mark, or two
def g.quotes.text(two: Bool, +qc: Char, tail: String) -> String:
  match two:
    case True{}:
      SCon{qc, SCon{qc, tail}}
    case False{}:
      SCon{qc, tail}

# a multi-line basic body's text
def g.mlb.text(ps: List<&2, GMlb>, tail: String) -> String:
  match ps:
    case []:
      tail
    case GmChar{kp} <> rest:
      k3.pc.text(kp, g.mlb.text(rest, tail))
    case GmNewline{nl} <> rest:
      String.append(nl, g.mlb.text(rest, tail))
    case GmEscapedNl{w1, nl, more} <> rest:
      SCon{'\\', String.append(w1, String.append(nl, String.append(more, g.mlb.text(rest, tail))))}
    case GmQuotes{two} <> rest:
      g.quotes.text(two, '"', g.mlb.text(rest, tail))

# a multi-line literal body's text
def g.mll.text(ps: List<&2, GMll>, tail: String) -> String:
  match ps:
    case []:
      tail
    case GlChar{cc} <> rest:
      SCon{cc, g.mll.text(rest, tail)}
    case GlNewline{nl} <> rest:
      String.append(nl, g.mll.text(rest, tail))
    case GlQuotes{two} <> rest:
      g.quotes.text(two, '\'', g.mll.text(rest, tail))

# a string's text, with its delimiters
def g.str.text(st: GString, tail: String) -> String:
  match st:
    case GsMlBasic{nl, body}:
      SCon{'"', SCon{'"', SCon{'"', String.append(nl, g.mlb.text(body, SCon{'"', SCon{'"', SCon{'"', tail}}}))}}}
    case GsBasic{pl}:
      SCon{'"', k3.pcs.text(pl, SCon{'"', tail})}
    case GsMlLiteral{nl, body}:
      SCon{'\'', SCon{'\'', SCon{'\'', String.append(nl, g.mll.text(body, SCon{'\'', SCon{'\'', SCon{'\'', tail}}}))}}}
    case GsLiteral{text}:
      SCon{'\'', String.append(text, SCon{'\'', tail})}

# [ array-sep ]: a comma when there is one
def g.sep.text(sep: Bool, tail: String) -> String:
  match sep:
    case True{}:
      SCon{',', tail}
    case False{}:
      tail

# a value's text, or that of an array-values, inline-table-keyvals or keyval
# node: array-open is [ (%x5B), array-close ] (%x5D), array-sep , (%x2C),
# inline-table-open { and ws (%x7B), inline-table-close ws and } (%x7D),
# inline-table-sep ws , ws, keyval-sep ws = ws (%x3D)
def g.val.text(vv: GVal, tail: String) -> String:
  match vv:
    case GvString{st}:
      g.str.text(st, tail)
    case GvBoolean{cs}:
      String.append(String.from_list(cs), tail)
    case GvArrayEmpty{wn}:
      SCon{'[', g.wcn.text(wn, SCon{']', tail})}
    case GvArray{vals, wn}:
      SCon{'[', g.val.text(vals, g.wcn.text(wn, SCon{']', tail}))}
    case GvInlineTableEmpty{w1, w2}:
      SCon{'{', String.append(w1, String.append(w2, SCon{'}', tail}))}
    case GvInlineTable{w1, kvs, w2}:
      SCon{'{', String.append(w1, g.val.text(kvs, String.append(w2, SCon{'}', tail})))}
    case GvDateTime{cs}:
      String.append(String.from_list(cs), tail)
    case GvFloat{cs}:
      String.append(String.from_list(cs), tail)
    case GvInteger{cs}:
      String.append(String.from_list(cs), tail)
    case GArrayValues{wa, val, wb, rest}:
      g.wcn.text(wa, g.val.text(val, g.wcn.text(wb, SCon{',', g.val.text(rest, tail)})))
    case GArrayValuesLast{wa, val, wb, sep}:
      g.wcn.text(wa, g.val.text(val, g.wcn.text(wb, g.sep.text(sep, tail))))
    case GInlineTableKeyvals{kv, w1, w2, rest}:
      g.val.text(kv, String.append(w1, SCon{',', String.append(w2, g.val.text(rest, tail))}))
    case GInlineTableKeyvalsLast{kv}:
      g.val.text(kv, tail)
    case GKeyval{key, w1, w2, val}:
      g.key.text(key, String.append(w1, SCon{'=', String.append(w2, g.val.text(val, tail))}))

# a table header's text
def g.table.text(tb: GTable, tail: String) -> String:
  match tb:
    case GStdTable{w1, key, w2}:
      SCon{'[', String.append(w1, g.key.text(key, String.append(w2, SCon{']', tail})))}
    case GArrayTable{w1, key, w2}:
      SCon{'[', SCon{'[', String.append(w1, g.key.text(key, String.append(w2, SCon{']', SCon{']', tail}})))}}

# an expression's text
def g.expr.text(ex: GExpr, tail: String) -> String:
  match ex:
    case GxBlank{w1, com}:
      String.append(w1, g.com.text(com, tail))
    case GxKeyval{w1, kv, w2, com}:
      String.append(w1, g.val.text(kv, String.append(w2, g.com.text(com, tail))))
    case GxTable{w1, tb, w2, com}:
      String.append(w1, g.table.text(tb, String.append(w2, g.com.text(com, tail))))

# the text of each newline and expression after the first
def g.lines.text(ls: List<&2, GLine>, tail: String) -> String:
  match ls:
    case []:
      tail
    case GLine{nl, ex} <> rest:
      String.append(nl, g.expr.text(ex, g.lines.text(rest, tail)))

# the text a derivation spells
def g.text(dd: Gd) -> String:
  match dd:
    case GToml{first, rest}:
      g.expr.text(first, g.lines.text(rest, ""))

# g.ok: every leaf matches its rule and keeps the prose's restrictions.

# [ comment ]: a comment's characters are non-eol, and none is U+007F
def g.ok.com(cm: GCom) -> Bool:
  match cm:
    case GcNone{}:
      True{}
    case GcSome{+body}:
      Bool.and(abnf.comment(body), prose.comment_chars(body))

# ws-comment-newline = *( wschar / [ comment ] newline )
def g.ok.wcn(ws: List<&2, GWcn>) -> Bool:
  match ws:
    case []:
      True{}
    case GwWschar{cc} <> rest:
      Bool.and(abnf.wschar(cc), g.ok.wcn(rest))
    case GwNewline{com, nl} <> rest:
      Bool.and(g.ok.com(com), Bool.and(abnf.newline(nl), g.ok.wcn(rest)))

# a string of its form, with the escape restriction on a basic one's
def g.ok.str(st: GString) -> Bool:
  match st:
    case GsMlBasic{nl, +body}:
      Bool.and(abnf.opt_newline(nl), Bool.and(abnf.ml_basic_body(body, False{}), prose.mlb_escapes_scalar(body)))
    case GsBasic{+pl}:
      Bool.and(abnf.basic_string(pl), prose.escapes_scalar(pl))
    case GsMlLiteral{nl, body}:
      Bool.and(abnf.opt_newline(nl), abnf.ml_literal_body(body, False{}))
    case GsLiteral{text}:
      abnf.literal_string(text)

# whether a GVal node spells the rule the mode names, every leaf in it
# matching its rule: a bare value's word matches its rule (an integer within
# signed 64 bits, a date-time within RFC 3339's ranges), and every part is
# of the rule its place asks for
def g.ok.val(vv: GVal, md: GRule) -> Bool:
  match vv md:
    case GvString{st} RVal{}:
      g.ok.str(st)
    case GvBoolean{+cs} RVal{}:
      abnf.boolean(cs)
    case GvArrayEmpty{wn} RVal{}:
      g.ok.wcn(wn)
    case GvArray{vals, wn} RVal{}:
      Bool.and(g.ok.val(vals, RArrayValues{}), g.ok.wcn(wn))
    case GvInlineTableEmpty{w1, w2} RVal{}:
      Bool.and(abnf.ws(w1), abnf.ws(w2))
    case GvInlineTable{w1, kvs, w2} RVal{}:
      Bool.and(abnf.ws(w1), Bool.and(g.ok.val(kvs, RInlineTableKeyvals{}), abnf.ws(w2)))
    case GvDateTime{+cs} RVal{}:
      Bool.and(abnf.date_time(cs), prose.date_time_in_range(cs))
    case GvFloat{+cs} RVal{}:
      abnf.float(cs)
    case GvInteger{+cs} RVal{}:
      Bool.and(abnf.integer(cs), prose.int_in_range(cs))
    case GArrayValues{wa, val, wb, rest} RArrayValues{}:
      Bool.and(g.ok.wcn(wa), Bool.and(g.ok.val(val, RVal{}), Bool.and(g.ok.wcn(wb),
        g.ok.val(rest, RArrayValues{}))))
    case GArrayValuesLast{wa, val, wb, _sep} RArrayValues{}:
      Bool.and(g.ok.wcn(wa), Bool.and(g.ok.val(val, RVal{}), g.ok.wcn(wb)))
    case GInlineTableKeyvals{kv, w1, w2, rest} RInlineTableKeyvals{}:
      Bool.and(g.ok.val(kv, RKeyval{}), Bool.and(abnf.ws(w1), Bool.and(abnf.ws(w2),
        g.ok.val(rest, RInlineTableKeyvals{}))))
    case GInlineTableKeyvalsLast{kv} RInlineTableKeyvals{}:
      g.ok.val(kv, RKeyval{})
    case GKeyval{key, w1, w2, val} RKeyval{}:
      Bool.and(g.ok.key(key), Bool.and(abnf.ws(w1), Bool.and(abnf.ws(w2), g.ok.val(val, RVal{}))))
    case _v _m:
      False{}

# a table header's key and ws
def g.ok.table(tb: GTable) -> Bool:
  match tb:
    case GStdTable{w1, key, w2}:
      Bool.and(abnf.ws(w1), Bool.and(g.ok.key(key), abnf.ws(w2)))
    case GArrayTable{w1, key, w2}:
      Bool.and(abnf.ws(w1), Bool.and(g.ok.key(key), abnf.ws(w2)))

# an expression's parts
def g.ok.expr(ex: GExpr) -> Bool:
  match ex:
    case GxBlank{w1, com}:
      Bool.and(abnf.ws(w1), g.ok.com(com))
    case GxKeyval{w1, kv, w2, com}:
      Bool.and(abnf.ws(w1), Bool.and(g.ok.val(kv, RKeyval{}), Bool.and(abnf.ws(w2), g.ok.com(com))))
    case GxTable{w1, tb, w2, com}:
      Bool.and(abnf.ws(w1), Bool.and(g.ok.table(tb), Bool.and(abnf.ws(w2), g.ok.com(com))))

# each newline and expression after the first
def g.ok.lines(ls: List<&2, GLine>) -> Bool:
  match ls:
    case []:
      True{}
    case GLine{nl, ex} <> rest:
      Bool.and(abnf.newline(nl), Bool.and(g.ok.expr(ex), g.ok.lines(rest)))

# whether every part of a derivation spells its rule
def g.ok(dd: Gd) -> Bool:
  match dd:
    case GToml{first, rest}:
      Bool.and(g.ok.expr(first), g.ok.lines(rest))

# g.val: what a value derivation denotes, as parse stores it.

# the characters a multi-line body starts with are trimmed: the first newline
# (right after the opening delimiter, TFirst), or all whitespace and newlines
# (after a line-ending backslash, TAll), or none
type GTrim is Data:
  TNone{}
  TFirst{}
  TAll{}

# a whitespace character dropped, or any other kept
def g.mlb.char.pick(drop: Bool, cc: Char, rest: String) -> String:
  match drop:
    case True{}:
      rest
    case False{}:
      SCon{cc, rest}

# a character written as itself: dropped while whitespace is trimmed
def g.mlb.char(tm: GTrim, +cc: Char, rest: String) -> String:
  match tm:
    case TAll{}:
      g.mlb.char.pick(abnf.wschar(cc), cc, rest)
    case TFirst{}:
      SCon{cc, rest}
    case TNone{}:
      SCon{cc, rest}

# whitespace keeps the trim going, and anything else ends it
def g.mlb.char.trim.pick(ws: Bool) -> GTrim:
  match ws:
    case True{}:
      TAll{}
    case False{}:
      TNone{}

# the trim that goes on after a character written as itself: whitespace
# goes on being trimmed after a line-ending backslash, and nothing else does
def g.mlb.char.trim(tm: GTrim, +cc: Char) -> GTrim:
  match tm:
    case TAll{}:
      g.mlb.char.trim.pick(abnf.wschar(cc))
    case TFirst{}:
      TNone{}
    case TNone{}:
      TNone{}

# a newline written as itself: dropped when trimmed, kept as written
# otherwise, LF or CRLF (REVIEW-G9)
def g.nl.char(tm: GTrim, nl: String, rest: String) -> String:
  match tm:
    case TAll{}:
      rest
    case TFirst{}:
      rest
    case TNone{}:
      String.append(nl, rest)

# the trim after a newline: whitespace after a backslash goes on being
# trimmed; the first newline is trimmed only once
def g.nl.trim(tm: GTrim) -> GTrim:
  match tm:
    case TAll{}:
      TAll{}
    case TFirst{}:
      TNone{}
    case TNone{}:
      TNone{}

# the characters a multi-line basic body stands for, with the specification's
# prose: "A newline immediately following the opening delimiter will be
# trimmed", whichever part of the derivation holds it, and "When the last
# non-whitespace character on a line is an unescaped \, it will be trimmed
# along with all whitespace (including newlines) up to the next
# non-whitespace character or closing delimiter". An escape stands for its
# character, a newline for itself as written (REVIEW-G9), and quotes for
# themselves
def g.mlb.chars(ps: List<&2, GMlb>, +tm: GTrim) -> String:
  match ps:
    case []:
      ""
    case GmChar{KpChar{+cc}} <> rest:
      g.mlb.char(tm, cc, g.mlb.chars(rest, g.mlb.char.trim(tm, cc)))
    case GmChar{kp} <> rest:
      SCon{k3.pc.char(kp), g.mlb.chars(rest, TNone{})}
    case GmNewline{nl} <> rest:
      g.nl.char(tm, nl, g.mlb.chars(rest, g.nl.trim(tm)))
    case GmEscapedNl{_w1, _nl, _more} <> rest:
      g.mlb.chars(rest, TAll{})
    case GmQuotes{two} <> rest:
      g.quotes.text(two, '"', g.mlb.chars(rest, TNone{}))

# the characters a multi-line literal body stands for: itself, but a newline
# right after the opening delimiter
def g.mll.chars(ps: List<&2, GMll>, +tm: GTrim) -> String:
  match ps:
    case []:
      ""
    case GlChar{cc} <> rest:
      SCon{cc, g.mll.chars(rest, TNone{})}
    case GlNewline{nl} <> rest:
      g.nl.char(tm, nl, g.mll.chars(rest, g.nl.trim(tm)))
    case GlQuotes{two} <> rest:
      g.quotes.text(two, '\'', g.mll.chars(rest, TNone{}))

# the trim a multi-line body starts with: none after a newline right after
# the delimiter, which is dropped, and the first newline otherwise
def g.first.trim(nl: String) -> GTrim:
  match nl:
    case SNil{}:
      TFirst{}
    case SCon{_h, _t}:
      TNone{}

# the characters a string stands for
def g.str.chars(st: GString) -> String:
  match st:
    case GsMlBasic{nl, body}:
      g.mlb.chars(body, g.first.trim(nl))
    case GsBasic{pl}:
      k3.pcs.name(pl)
    case GsMlLiteral{nl, body}:
      g.mll.chars(body, g.first.trim(nl))
    case GsLiteral{text}:
      text

# whether a value is a string, owned or a span, of the characters
def g.str.is(vv: T.Val, text: String) -> Bool:
  match vv:
    case T.VStr{tx}:
      String.eq(tx, text)
    case T.VSpan{src, nn}:
      String.eq(T.string(T.VSpan{src, nn}), text)
    case _:
      False{}

# a digit's value, an upper case letter's, or a lower case one's
def g.hexdig.val.pick(dg: Bool, up: Bool, +cp: U32) -> Nat:
  match dg up:
    case True{} _u:
      U32.to_nat(U32.sub(cp, 48))
    case False{} True{}:
      U32.to_nat(U32.sub(cp, 55))
    case False{} False{}:
      U32.to_nat(U32.sub(cp, 87))

# the value of a HEXDIG, which a DIGIT is: its digit, or a letter's 10 to 15
# in either case
def g.hexdig.val(cc: Char) -> Nat:
  match cc:
    case Chr{+cp}:
      g.hexdig.val.pick(abnf.digit(cp), abnf.range(cp, 65, 70), cp)

# an underscore leaves the value as it is; a digit is one more place
def g.num.nat.step(us: Bool, hh: Char, +radix: Nat, acc: Nat) -> Nat:
  match us:
    case True{}:
      acc
    case False{}:
      Nat.add(Nat.mul(acc, radix), g.hexdig.val(hh))

# the value of a numeral's digits in a radix, the most significant first,
# its underscores skipped; acc is the value of the digits before
def g.num.nat(cs: List<&2, Char>, +radix: Nat, acc: Nat) -> Nat:
  match cs:
    case []:
      acc
    case +hh <> tt:
      g.num.nat(tt, radix, g.num.nat.step(abnf.underscore(hh), hh, radix, acc))

# whether every character of a string is a DIGIT
def g.dec.all(ss: String) -> Bool:
  match ss:
    case SNil{}:
      True{}
    case SCon{hh, tt}:
      Bool.and(abnf.DIGIT(hh), g.dec.all(tt))

# whether a string is decimal digits with no leading zero, or 0 alone
def g.dec.canon(ss: String) -> Bool:
  match ss:
    case SNil{}:
      False{}
    case SCon{+hh, +tt}:
      Bool.and(abnf.DIGIT(hh), Bool.or(Bool.and(abnf.cp(hh, 48), String.is_empty(tt)),
        Bool.and(abnf.digit1_9(hh), g.dec.all(tt))))

# the radix of the prefix that matched, or 10
def g.int.radix.pick(hx: Bool, oc: Bool, bi: Bool) -> Nat:
  match hx oc bi:
    case True{} _o _b:
      16n
    case False{} True{} _b:
      8n
    case False{} False{} True{}:
      2n
    case False{} False{} False{}:
      10n

# an integer word's radix: 16, 8 or 2 after its prefix, and 10 for a dec-int
def g.int.radix(+cs: List<&2, Char>) -> Nat:
  g.int.radix.pick(abnf.hex_int(cs), abnf.oct_int(cs), abnf.bin_int(cs))

# the digits after a two-character prefix, or after a dec-int's sign
def g.int.body.pick(pre: Bool, cs: List<&2, Char>) -> List<&2, Char>:
  match pre:
    case True{}:
      List.drop(&2, Char, cs, 2n)
    case False{}:
      String.to_list(abnf.dec_digits(cs))

# an integer word's digits: after the prefix, or after a dec-int's sign
def g.int.body(+cs: List<&2, Char>) -> List<&2, Char>:
  g.int.body.pick(Bool.or(abnf.hex_int(cs), Bool.or(abnf.oct_int(cs), abnf.bin_int(cs))), cs)

# an integer word denotes a sign, minus for a dec-int that starts with one
# and plus otherwise, and a value, written as decimal digits with no leading
# zero: those digits' value in base 10 is the numeral's in its radix, both
# as Nats. It is a relation, not computed, since a Nat is not evaluated
def g.int.is(vv: T.Val, +cs: List<&2, Char>) -> Bool:
  match vv:
    case T.VInt{sign, +digits}:
      Bool.and(sign.eq(sign, abnf.dec_sign(cs)), Bool.and(g.dec.canon(digits),
        Nat.is_eq(g.num.nat(String.to_list(digits), 10n, 0n), g.num.nat(g.int.body(cs), g.int.radix(cs), 0n))))
    case _:
      False{}

# a float word denotes its sign, minus when it starts with one and plus
# otherwise, and its spelling with the sign and every underscore removed
# (abnf.dec_sign and abnf.dec_digits read any word that way)
def g.flo.is(vv: T.Val, +cs: List<&2, Char>) -> Bool:
  match vv:
    case T.VFlo{sign, text}:
      Bool.and(sign.eq(sign, abnf.dec_sign(cs)), String.eq(text, abnf.dec_digits(cs)))
    case _:
      False{}

# a boolean word denotes its bit: true for true
def g.bool.is(vv: T.Val, cs: List<&2, Char>) -> Bool:
  match vv:
    case T.VBool{bit}:
      bit.eq(bit, abnf.true(cs))
    case _:
      False{}

# a date-time word denotes its form and fields
def g.when.is(vv: T.Val, cs: List<&2, Char>) -> Bool:
  match vv:
    case T.VWhen{when}:
      when.eq(when, g.dt.when(cs))
    case _:
      False{}

# what g.val.go compares a node against: a value (GMVal), none (GMMiss, a
# lookup that found nothing, which no value derivation denotes), an array's
# items for its array-values (GMItems), or an inline table's rows for its
# keyvals (GMRows)
type GMode is Data:
  GMVal{val: T.Val}
  GMMiss{}
  GMItems{items: List<&2, T.Val>}
  GMRows{rows: List<&2, T.Val>}

# the mode for what a lookup found
def g.hit.mode(hh: T.Hit) -> GMode:
  match hh:
    case T.Found{vv}:
      GMVal{vv}
    case T.Miss{}:
      GMMiss{}

# the key paths of an inline table's keyvals
def g.kv.paths(vv: GVal) -> List<&2, List<&2, String>>:
  match vv:
    case GInlineTableKeyvals{GKeyval{key, _w1, _w2, _v}, _a, _b, rest}:
      g.key.names(key) <> g.kv.paths(rest)
    case GInlineTableKeyvalsLast{GKeyval{key, _w1, _w2, _v}}:
      [g.key.names(key)]
    case _:
      []

# whether two key paths are one
def g.path.eq(aa: List<&2, String>, bb: List<&2, String>) -> Bool:
  match aa bb:
    case Nil{} Nil{}:
      True{}
    case +xx <> xt +yy <> yt:
      Bool.and(String.eq(xx, yy), g.path.eq(xt, yt))
    case _a _b:
      False{}

# whether a path is one of the paths
def g.path.in(+pp: List<&2, String>, ps: List<&2, List<&2, String>>) -> Bool:
  match ps:
    case []:
      False{}
    case qq <> rest:
      Bool.or(g.path.eq(pp, qq), g.path.in(pp, rest))

# whether a path lies strictly under another: it is longer and starts with it
def g.path.under(pp: List<&2, String>, at: List<&2, String>) -> Bool:
  match pp at:
    case Nil{} _a:
      False{}
    case _x <> _t Nil{}:
      True{}
    case xx <> xt yy <> yt:
      Bool.and(String.eq(xx, yy), g.path.under(xt, yt))

# whether some path lies strictly under the path
def g.path.above(+at: List<&2, String>, ps: List<&2, List<&2, String>>) -> Bool:
  match ps:
    case []:
      False{}
    case qq <> rest:
      Bool.or(g.path.under(qq, at), g.path.above(at, rest))

# a table's own paths when a keyval's path lies under it, and its path as one
# value otherwise
def g.leaf.pick(
  above: Bool,
  inner: List<&2, List<&2, String>>,
  at: List<&2, String>,
  rest: List<&2, List<&2, String>>
) -> List<&2, List<&2, String>>:
  match above:
    case True{}:
      List.append(&2, List<&2, String>, inner, rest)
    case False{}:
      at <> rest

# the paths from an inline table's rows to the values in it, entering a
# table (an inline table, as parse seals every table in one) exactly when the
# path of one of the keyvals ps lies under it: a table dotted keys made. A row
# that is no pair, which no inline table holds, counts as a value at the empty
# path, which no keyval has
def g.leaf.paths(
  rows: List<&2, T.Val>,
  +at: List<&2, String>,
  +ps: List<&2, List<&2, String>>
) -> List<&2, List<&2, String>>:
  match rows:
    case []:
      []
    case T.VPair{+nn, T.VInl{sub}} <> +tt:
      +pp = List.append(&2, String, at, [nn])
      g.leaf.pick(g.path.above(pp, ps), g.leaf.paths(sub, pp, ps), pp, g.leaf.paths(tt, at, ps))
    case T.VPair{+nn, _v} <> +tt:
      List.append(&2, String, at, [nn]) <> g.leaf.paths(tt, at, ps)
    case _v <> tt:
      Nil{} <> g.leaf.paths(tt, at, ps)

# whether every path of the first list is one of the second
def g.paths.within(ps: List<&2, List<&2, String>>, +qs: List<&2, List<&2, String>>) -> Bool:
  match ps:
    case []:
      True{}
    case pp <> rest:
      Bool.and(g.path.in(pp, qs), g.paths.within(rest, qs))

# whether an inline table's rows hold its keyvals' values and nothing else:
# as many values as keyvals, each at one of their paths, with only the tables
# dotted keys make on the way
def g.inl.only(+rows: List<&2, T.Val>, kvs: GVal) -> Bool:
  +ps = g.kv.paths(kvs)
  +ls = g.leaf.paths(rows, [], ps)
  Bool.and(Nat.is_eq(List.length(&2, List<&2, String>, ls), List.length(&2, List<&2, String>, ps)),
    g.paths.within(ls, ps))

# whether a GVal node denotes what the mode holds: a string its characters
# (owned or a span), an integer, float, boolean or date-time word its value,
# an array its items in order, and an inline table the table its keyvals
# make: each keyval's value where `at` finds its key, and nothing else
def g.val.go(vv: GVal, md: GMode) -> Bool:
  match vv md:
    case GvString{st} GMVal{val}:
      g.str.is(val, g.str.chars(st))
    case GvBoolean{cs} GMVal{val}:
      g.bool.is(val, cs)
    case GvArrayEmpty{_wn} GMVal{T.VArr{items}}:
      List.is_empty(&2, T.Val, items)
    case GvArray{vals, _wn} GMVal{T.VArr{items}}:
      g.val.go(vals, GMItems{items})
    case GvInlineTableEmpty{_w1, _w2} GMVal{T.VInl{rows}}:
      List.is_empty(&2, T.Val, rows)
    case GvInlineTable{_w1, +kvs, _w2} GMVal{T.VInl{+rows}}:
      Bool.and(g.val.go(kvs, GMRows{rows}), g.inl.only(rows, kvs))
    case GvDateTime{cs} GMVal{val}:
      g.when.is(val, cs)
    case GvFloat{cs} GMVal{val}:
      g.flo.is(val, cs)
    case GvInteger{cs} GMVal{val}:
      g.int.is(val, cs)
    case GArrayValues{_wa, val, _wb, rest} GMItems{it <> its}:
      Bool.and(g.val.go(val, GMVal{it}), g.val.go(rest, GMItems{its}))
    case GArrayValuesLast{_wa, val, _wb, _sep} GMItems{it <> its}:
      Bool.and(g.val.go(val, GMVal{it}), List.is_empty(&2, T.Val, its))
    case GInlineTableKeyvals{kv, _w1, _w2, rest} GMRows{+rows}:
      Bool.and(g.val.go(kv, GMRows{rows}), g.val.go(rest, GMRows{rows}))
    case GInlineTableKeyvalsLast{kv} GMRows{rows}:
      g.val.go(kv, GMRows{rows})
    case GKeyval{key, _w1, _w2, val} GMRows{rows}:
      g.val.go(val, g.hit.mode(T.at(rows, g.key.names(key))))
    case _v _m:
      False{}

# whether a value derivation denotes the value
def g.val(vv: GVal, val: T.Val) -> Bool:
  g.val.go(vv, GMVal{val})

# defs: the definition rules of TOML v1.0.0's prose, which TOML-TEXT-2
# states, over a derivation's expressions in order. A record says what each
# key path (the names of its segments, from the root) holds; each keyval and
# header reads it and adds to it, and the first rule broken fails the whole.

# what a key path holds, as the rules tell kinds apart: nothing yet; a key's
# value (a string, number, boolean, datetime, array or inline table); a table
# a [table] header named; a table a header only passed through on its way; a
# table dotted keys made, or entered after a header only passed through it;
# an array of tables
type DKind is Data:
  DAbsent{}
  DValue{}
  DHeader{}
  DPassed{}
  DDotted{}
  DArrayOfTables{}

# a path and what it holds
type DEnt is Data:
  DEnt{path: List<&2, String>, kind: DKind}

# the record so far, newest first, and the table the lines are in; or a rule
# broken
type DSt is Data:
  DOk{ents: List<&2, DEnt>, here: List<&2, String>}
  DFail{}

# what defines a path: a keyval's key, a [table] header, or an [[array]]
# header
type DJob is Data:
  DjKey{}
  DjStd{}
  DjAot{}

# what a key or header does with a table on its way to the path it defines:
# go on through it, record it as the kind and go on, or break a rule
type DStep is Data:
  DsGo{}
  DsMake{kind: DKind}
  DsBreak{}

# the newest entry's kind when it is for the path, and the older ones'
# otherwise
def defs.kind.pick(hit: Bool, kk: DKind, other: DKind) -> DKind:
  match hit:
    case True{}:
      kk
    case False{}:
      other

# what a path holds: its newest entry's kind, or DAbsent
def defs.kind(ents: List<&2, DEnt>, +pp: List<&2, String>) -> DKind:
  match ents:
    case []:
      DAbsent{}
    case DEnt{qq, kk} <> rest:
      defs.kind.pick(g.path.eq(qq, pp), kk, defs.kind(rest, pp))

# an entry kept when it is not under the path
def defs.drop.pick(under: Bool, en: DEnt, rest: List<&2, DEnt>) -> List<&2, DEnt>:
  match under:
    case True{}:
      rest
    case False{}:
      en <> rest

# the record with every path under at taken out
def defs.drop(ents: List<&2, DEnt>, +at: List<&2, String>) -> List<&2, DEnt>:
  match ents:
    case []:
      []
    case DEnt{+qq, kk} <> rest:
      defs.drop.pick(g.path.under(qq, at), DEnt{qq, kk}, defs.drop(rest, at))

# A table on the way to the path a key or header defines. TOML v1.0.0:
# "Dotted keys create and define a table for each key part before the last
# one, provided that such tables were not previously created." "If you
# don't [create a super-table], it will be created implicitly for you."
# "Since tables cannot be defined more than once, redefining such tables
# using a [table] header is not allowed. Likewise, using dotted keys to
# redefine tables already defined in [table] form is not allowed." "Inline
# tables are fully self-contained and define all keys and sub-tables within
# them. Keys and sub-tables cannot be added outside the braces." "Any
# reference to an array of tables points to the most recently defined table
# element of the array." A value is entered by nothing; a table a header
# named or an array of tables is entered by a header, never by a dotted key;
# a table a header passed through is entered by either, and dotted keys that
# enter it make it theirs (REVIEW-G2: open to dotted keys, and then no longer
# to a header naming it, as the code and tomllib do)
def defs.enter(look: DKind, job: DJob) -> DStep:
  match look job:
    case DAbsent{} DjKey{}:
      DsMake{DDotted{}}
    case DAbsent{} _j:
      DsMake{DPassed{}}
    case DValue{} _j:
      DsBreak{}
    case DHeader{} DjKey{}:
      DsBreak{}
    case DHeader{} _j:
      DsGo{}
    case DPassed{} DjKey{}:
      DsMake{DDotted{}}
    case DPassed{} _j:
      DsGo{}
    case DDotted{} _j:
      DsGo{}
    case DArrayOfTables{} DjKey{}:
      DsBreak{}
    case DArrayOfTables{} _j:
      DsGo{}

# The path a key or header defines. TOML v1.0.0: "Defining a key multiple
# times is invalid." "Just as keys, you cannot define a table more than
# once." "The [table] form can, however, be used to define sub-tables within
# tables defined via dotted keys", so a header may name a table it or another
# header only passed through. "Attempting to append to a statically defined
# array, even if that array is empty, must produce an error at parse time."
# "Attempting to define a normal table with the same name as an already
# established array must produce an error at parse time. Attempting to
# redefine a normal table as an array must likewise produce an error at
# parse time." A key's value needs the path free; a [table] header needs it
# free or only passed through, and its lines are in it after; an [[array]]
# header needs it free or an array of tables, and starts a new element,
# which is its own scope for these rules
def defs.last(look: DKind, job: DJob, ents: List<&2, DEnt>, +at: List<&2, String>, here: List<&2, String>) -> DSt:
  match look job:
    case DAbsent{} DjKey{}:
      DOk{DEnt{at, DValue{}} <> ents, here}
    case DAbsent{} DjStd{}:
      DOk{DEnt{at, DHeader{}} <> ents, at}
    case DPassed{} DjStd{}:
      DOk{DEnt{at, DHeader{}} <> ents, at}
    case DAbsent{} DjAot{}:
      DOk{DEnt{at, DArrayOfTables{}} <> ents, at}
    case DArrayOfTables{} DjAot{}:
      DOk{defs.drop(ents, at), at}
    case _l _j:
      DFail{}

# a key's or header's segments after the path at, whose kind is look and
# whose step on the way is st: each segment but the last enters a table,
# and the last is the path defined
def defs.walk(
  names: List<&2, String>,
  +ents: List<&2, DEnt>,
  +at: List<&2, String>,
  look: DKind,
  st: DStep,
  +job: DJob,
  here: List<&2, String>
) -> DSt:
  match names:
    case []:
      defs.last(look, job, ents, at, here)
    case nn <> rest:
      match st:
        case DsBreak{}:
          DFail{}
        case DsGo{}:
          +a2 = List.append(&2, String, at, [nn])
          +k2 = defs.kind(ents, a2)
          defs.walk(rest, ents, a2, k2, defs.enter(k2, job), job, here)
        case DsMake{kk}:
          +e2 = {DEnt{at, kk} <> ents : List<&2, DEnt>}
          +a2 = List.append(&2, String, at, [nn])
          +k2 = defs.kind(e2, a2)
          defs.walk(rest, e2, a2, k2, defs.enter(k2, job), job, here)

# the path a key starts from: the table the lines are in for a keyval's key,
# the root for a header's
def defs.base(job: DJob, here: List<&2, String>) -> List<&2, String>:
  match job:
    case DjKey{}:
      here
    case DjStd{}:
      []
    case DjAot{}:
      []

# a key or a header, of the names of its segments, defined from a record
def defs.key(st: DSt, names: List<&2, String>, +job: DJob) -> DSt:
  match st names:
    case DFail{} _n:
      DFail{}
    case DOk{_e, _h} Nil{}:
      DFail{}
    case DOk{+ents, +here} nn <> rest:
      +a0 = List.append(&2, String, defs.base(job, here), [nn])
      +k0 = defs.kind(ents, a0)
      defs.walk(rest, ents, a0, k0, defs.enter(k0, job), job, here)

# the record as it was when an inner record kept the rules, and a failure
# when it broke one
def defs.keep(inner: DSt, st: DSt) -> DSt:
  match inner:
    case DOk{_e, _h}:
      st
    case DFail{}:
      DFail{}

# a GVal node's definitions: a keyval defines its key in the record; the
# keyvals of an inline table are defined in a record of their own, from the
# empty one, since it is self-contained; and every value in an array or an
# inline table is checked the same way
def defs.go(vv: GVal, st: DSt) -> DSt:
  match vv:
    case GvArray{vals, _wn}:
      defs.go(vals, st)
    case GvInlineTable{_w1, kvs, _w2}:
      defs.keep(defs.go(kvs, DOk{[], []}), st)
    case GArrayValues{_wa, val, _wb, rest}:
      defs.go(rest, defs.go(val, st))
    case GArrayValuesLast{_wa, val, _wb, _sep}:
      defs.go(val, st)
    case GInlineTableKeyvals{kv, _w1, _w2, rest}:
      defs.go(rest, defs.go(kv, st))
    case GInlineTableKeyvalsLast{kv}:
      defs.go(kv, st)
    case GKeyval{key, _w1, _w2, val}:
      defs.keep(defs.go(val, DOk{[], []}), defs.key(st, g.key.names(key), DjKey{}))
    case _v:
      st

# an expression's definitions: a keyval's in the table the lines are in, a
# [table] header's, whose table the lines after it are in, and an [[array]]
# header's
def defs.expr(ex: GExpr, st: DSt) -> DSt:
  match ex:
    case GxBlank{_w1, _com}:
      st
    case GxKeyval{_w1, kv, _w2, _com}:
      defs.go(kv, st)
    case GxTable{_w1, GStdTable{_a, key, _b}, _w2, _com}:
      defs.key(st, g.key.names(key), DjStd{})
    case GxTable{_w1, GArrayTable{_a, key, _b}, _w2, _com}:
      defs.key(st, g.key.names(key), DjAot{})

# the definitions of each expression after the first, in order
def defs.lines(ls: List<&2, GLine>, st: DSt) -> DSt:
  match ls:
    case []:
      st
    case GLine{_nl, ex} <> rest:
      defs.lines(rest, defs.expr(ex, st))

# whether no rule was broken
def defs.ok(st: DSt) -> Bool:
  match st:
    case DOk{_e, _h}:
      True{}
    case DFail{}:
      False{}

# whether a derivation's expressions, in order, break none of the definition
# rules
def defs(dd: Gd) -> Bool:
  match dd:
    case GToml{first, rest}:
      defs.ok(defs.lines(rest, defs.expr(first, DOk{[], []})))

# Basic facts of the transcription (WP-G).

# LAW: TOML-KEY-3's blank space, spaces and tabs, is ws
law gap_is_ws:
  for +gs: List<&2, Bool>
  {abnf.ws(gap(gs)) == True{} : Bool}

# LAW: the lines after a document's first expression, split anywhere, spell
# the first part's text and then the second's
law g_lines_text_append:
  for +xs: List<&2, GLine>
  for +ys: List<&2, GLine>
  for +tail: String
  {g.lines.text(List.append(&2, GLine, xs, ys), tail) == g.lines.text(xs, g.lines.text(ys, tail)) : String}

# LAW: a value's text before a tail is its own text, then the tail
law g_val_text_tail:
  for +vv: GVal
  for +tail: String
  {g.val.text(vv, tail) == String.append(g.val.text(vv, ""), tail) : String}

# LAW: a derivation's text is its first expression's text, then its lines'
law g_text_parts:
  for +first: GExpr
  for +rest: List<&2, GLine>
  {g.text(GToml{first, rest}) == String.append(g.expr.text(first, ""), g.lines.text(rest, "")) : String}

# LAW: no word is both a boolean and an integer
law boolean_not_integer:
  for +cs: List<&2, Char>
  for +h: {abnf.boolean(cs) == True{} : Bool}
  {abnf.integer(cs) == False{} : Bool}

# LAW: no word is both a boolean and a float
law boolean_not_float:
  for +cs: List<&2, Char>
  for +h: {abnf.boolean(cs) == True{} : Bool}
  {abnf.float(cs) == False{} : Bool}

# LAW: no word is both a boolean and a date-time
law boolean_not_date_time:
  for +cs: List<&2, Char>
  for +h: {abnf.boolean(cs) == True{} : Bool}
  {abnf.date_time(cs) == False{} : Bool}

# LAW: no word is both an integer and a float
law integer_not_float:
  for +cs: List<&2, Char>
  for +h: {abnf.integer(cs) == True{} : Bool}
  {abnf.float(cs) == False{} : Bool}

# LAW: no word is both an integer and a date-time
law integer_not_date_time:
  for +cs: List<&2, Char>
  for +h: {abnf.integer(cs) == True{} : Bool}
  {abnf.date_time(cs) == False{} : Bool}

# LAW: no word is both a float and a date-time
law float_not_date_time:
  for +cs: List<&2, Char>
  for +h: {abnf.float(cs) == True{} : Bool}
  {abnf.date_time(cs) == False{} : Bool}
