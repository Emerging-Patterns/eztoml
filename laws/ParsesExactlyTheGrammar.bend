# For every text `t` of Unicode scalar values shorter than 2^32 characters:
# `bad(parse(t))` is `""` exactly when `t`, with one leading U+FEFF taken off,
# matches the grammar of toml.abnf's `toml` rule (TOML v1.0.0) together with
# the four restrictions its prose adds (every integer within signed 64 bits,
# as laws/IntegerReadExactly.bend states; every date and time within RFC 3339's ranges, as
# laws/DateTimeReadExactly.bend states; every `\u` and `\U` escape naming a Unicode scalar
# value; and no U+007F in a comment), and breaks none of the rules of
# laws/DefinesEachTableOnce.bend
#
# pending: the laws here prove part of this, not all of it.
#
# also rests on: laws/ErrorStays.bend, laws/HeaderQuoteAfterBareRefused.bend,
# laws/HeaderQuoteAtStartOpensSegment.bend, laws/HeadersParseAsReplay.bend,
# laws/TextReadsAsReplay.bend
import Base
import ../main.bend as T
import ./defs/BareValueGrammar.bend as D1
import ./defs/BlankAndControlChars.bend as D2
import ./defs/PairPresence.bend as D3

# LAW: once the scanner has failed, the rest of the text leaves the first error
# as it is. Every refusal of the scanner lands here, so each law below only
# has to show that one step fails
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
law lone_cr_refused:
  for +st: T.St
  for +c: Char
  for e: {Char.is_eq(c, '\n') == False{} : Bool}
  for +t: String
  {String.is_empty(T.bad(T.doc.read(SCon{'\r', SCon{c, t}}, T.MScan{st}))) == False{}
    : Bool}

# LAW: and one that ends the text fails it too
law last_cr_refused:
  for +st: T.St
  {String.is_empty(T.bad(T.doc.read("\r", T.MScan{st}))) == False{} : Bool}

# LAW: a value is on its key's line: from every scanner state waiting for the
# value after `=`, a line feed fails the document, whatever follows it
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

# the rows of a finished walk
def end_rows(end: T.End) -> List<&2, T.Val>:
  match end:
    case T.End{vs, _bad, _heads}:
      vs

# LAW: in an inline table, two dotted keys that share their first segment
# are both read: once `b.c = v` is in the inline table, `b.d = w` is read
# with no error when c is not d. The walk is the one an inline table's key
# takes, starting from its rows with no error
law inline_dotted_keys_share_a_prefix:
  for +inl: List<&2, T.Val>
  for +b: String
  for +c: String
  for +d: String
  for +v: T.Val
  for w: T.Val
  for e: {D3.has_pair(inl, b) == False{} : Bool}
  for f: {String.eq(c, d) == False{} : Bool}
  {D1.end_bad(T.tree.walk([b, d], T.Tw{end_rows(T.tree.walk([b, c],
    T.Tw{inl, T.JPut{v}, [], "", "", [], True{}}, 0)), T.JPut{w}, [], "", "", [],
    True{}}, 0)) == "" : String}

# LAW: in a header, blank space with no segment open and then a bracket fail
# the document, whatever follows: the two brackets of `[[` are adjacent, so
# `[ [` does not open an array of tables
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
  {String.is_empty(T.bad(T.doc.read(SCon{D2.blank_char(tab), SCon{'[', t}},
    T.MScan{T.St{bad, rows, heads, here, parts, [], T.LHead{}, back, qkind, stack,
    T.HNone{}, uni, left, arrtab, False{}}}))) == False{} : Bool}

# LAW: in a header, blank space with no segment open leaves the scanner
# waiting for a segment, as it does after a dot: a bare or quoted key may
# follow
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
    T.HNone{}, uni, left, arrtab, False{}}, D2.blank_char(tab))
    == T.MScan{T.St{bad, rows, heads, here, parts, [], T.LHeadDot{}, back, qkind,
    stack, T.HNone{}, uni, left, arrtab, False{}}} : T.Mode}
