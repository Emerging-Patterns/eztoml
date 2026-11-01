# `render` writes a string value as a basic string that escapes exactly `"`,
# `\` and the controls U+0000 to U+001F and U+007F (with `\b`, `\t`, `\n`,
# `\f`, `\r` where TOML has them, and otherwise `\u00` and two lowercase
# hexadecimal digits), and writes every other character as itself
import Base
import ../main.bend as T
import ./defs/BlankAndControlChars.bend as D1
import ./defs/StringValueTest.bend as D2

# laws/StringRenderEscapes.bend: how render writes a string. A string value, owned or a span, is
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
law esc_quote:
  for +c: Char
  for h: {c == '"' : Char}
  {esc(c) == "\\\"" : String}

# LAW: a backslash is written as two
law esc_backslash:
  for +c: Char
  for h: {c == '\\' : Char}
  {esc(c) == "\\\\" : String}

# LAW: a backspace is written as \b
law esc_b:
  for +c: Char
  for h: {c == '\u{8}' : Char}
  {esc(c) == "\\b" : String}

# LAW: a tab is written as \t
law esc_t:
  for +c: Char
  for h: {c == '\t' : Char}
  {esc(c) == "\\t" : String}

# LAW: a line feed is written as \n
law esc_n:
  for +c: Char
  for h: {c == '\n' : Char}
  {esc(c) == "\\n" : String}

# LAW: a form feed is written as \f
law esc_f:
  for +c: Char
  for h: {c == '\u{c}' : Char}
  {esc(c) == "\\f" : String}

# LAW: a carriage return is written as \r
law esc_r:
  for +c: Char
  for h: {c == '\r' : Char}
  {esc(c) == "\\r" : String}

# LAW: every other control, U+0000 to U+001F and U+007F, is written as \u00
# and its two hexadecimal digits, lowercase
law esc_ctl:
  for +c: Char
  for h_c: {D1.is_ctl(c) == True{} : Bool}
  for h_b: {c != '\u{8}' : Char}
  for h_t: {c != '\t' : Char}
  for h_n: {c != '\n' : Char}
  for h_f: {c != '\u{c}' : Char}
  for h_r: {c != '\r' : Char}
  {esc(c) == "\\u00" ++ String.from_list([char_at(hex_lower(), U32.to_nat(U32.div(Char.to_u32(c), 16))),
    char_at(hex_lower(), U32.to_nat(U32.mod(Char.to_u32(c), 16)))]) : String}

# LAW: every character that is no control, no quotation mark and no
# backslash is written as itself
law esc_plain:
  for +c: Char
  for +h_c: {D1.is_ctl(c) == False{} : Bool}
  for h_q: {c != '"' : Char}
  for h_b: {c != '\\' : Char}
  {esc(c) == String.from_list([c]) : String}

# LAW: a basic string is a quotation mark, each character written in order,
# and a quotation mark
law basic_escs:
  for +s: String
  {T.key.basic(s) == "\"" ++ escs(s) ++ "\"" : String}

# LAW: a span is quoted, on the fast path that copies it when no character
# needs an escape, exactly as key.basic quotes its characters
law span_quote_basic:
  for +src: String
  for +n: U32
  {T.span.quote(src, n) == T.key.basic(T.string(T.VSpan{src, n})) : String}

# LAW: a document whose root table starts with a string pair renders that
# pair as its key, " = ", key.basic of its characters and a newline, then the
# rest of the document as it would render alone
law render_string:
  for +e: String
  for name: String
  for +v: T.Val
  for +rest: List<&2, T.Val>
  for h: {D2.is_string(v) == True{} : Bool}
  {T.render(T.Doc{e, T.VPair{name, v} <> rest})
    == T.key(name) ++ " = " ++ T.key.basic(T.string(v)) ++ "\n" ++ T.render(T.Doc{e, rest}) : String}

# LAW: in any table, the pass that writes keys writes a string pair as its
# key, " = " and key.basic of its characters, then the separator and the rest
law pass_string:
  for name: String
  for +v: T.Val
  for +rest: List<&2, T.Val>
  for +gap: String
  for +trail: Bool
  for h: {D2.is_string(v) == True{} : Bool}
  {T.render.pass(T.VPair{name, v} <> rest, gap, trail, False{})
    == (T.key(name) ++ " = " ++ T.key.basic(T.string(v))) ++
      T.render.suf(gap, trail, List.is_empty(&2, T.Val, rest)) ++ T.render.pass(rest, gap, trail, False{})
    : String}

# LAW: the pass that writes tables writes nothing for a string pair
law pass_string_tables:
  for name: String
  for +v: T.Val
  for +rest: List<&2, T.Val>
  for +gap: String
  for +trail: Bool
  for h: {D2.is_string(v) == True{} : Bool}
  {T.render.pass(T.VPair{name, v} <> rest, gap, trail, True{}) == T.render.pass(rest, gap, trail, True{}) : String}

# LAW: in an inline table, a string pair is written as its key, " = " and
# key.basic of its characters, then the separator and the rest
law inline_string:
  for name: String
  for +v: T.Val
  for +rest: List<&2, T.Val>
  for +gap: String
  for +trail: Bool
  for h: {D2.is_string(v) == True{} : Bool}
  {T.render.go(T.VPair{name, v} <> rest, gap, trail)
    == T.key(name) ++ " = " ++ T.key.basic(T.string(v)) ++
      T.render.suf(gap, trail, List.is_empty(&2, T.Val, rest)) ++ T.render.go(rest, gap, trail) : String}

# LAW: in an array, a string item is written as key.basic of its characters,
# then the separator and the rest
law array_string:
  for +v: T.Val
  for +rest: List<&2, T.Val>
  for +gap: String
  for +trail: Bool
  for h: {D2.is_string(v) == True{} : Bool}
  {T.render.go(v <> rest, gap, trail)
    == T.key.basic(T.string(v)) ++ T.render.suf(gap, trail, List.is_empty(&2, T.Val, rest)) ++
      T.render.go(rest, gap, trail) : String}
