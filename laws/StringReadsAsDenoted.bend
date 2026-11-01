# For every string form of toml.abnf (basic, literal, multi-line basic,
# multi-line literal) and every text that form can hold, in a document shorter
# than 2^32 characters, `string` of the value `parse` reads is the text it
# denotes: escapes decoded, a line-ending backslash and the whitespace after
# it dropped in a multi-line basic string, and a newline right after the
# opening delimiter dropped
import Base
import ../main.bend as T
import ./defs/AbnfGrammar.bend as D1
import ./defs/BareValueGrammar.bend as D2
import ./defs/GrammarDerivations.bend as D3

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
law ml_basic_one_quote:
  for +x: String
  for e: {ml.text(x) == True{} : Bool}
  {T.parse(String.append("a = \"\"\"", String.append(x, "\"\"\"\"\n")))
    == T.Doc{"", [T.VPair{"a", T.VStr{String.append(x, "\"")}}]} : T.Doc}

# LAW: and so are two, with the text ending right after the delimiter:
# a = """x""""" reads x and two quotes
law ml_basic_two_quotes:
  for +x: String
  for e: {ml.text(x) == True{} : Bool}
  {T.parse(String.append("a = \"\"\"", String.append(x, "\"\"\"\"\"")))
    == T.Doc{"", [T.VPair{"a", T.VStr{String.append(x, "\"\"")}}]} : T.Doc}

# LAW: one apostrophe right before a multi-line literal string's closing
# delimiter is part of the string (mll-quotes): a = '''x'''' and a newline
# reads x and an apostrophe
law ml_literal_one_quote:
  for +x: String
  for e: {ml.text(x) == True{} : Bool}
  {T.parse(String.append("a = '''", String.append(x, "''''\n")))
    == T.Doc{"", [T.VPair{"a", T.VStr{String.append(x, "'")}}]} : T.Doc}

# LAW: and so are two, with the text ending right after the delimiter:
# a = '''x''''' reads x and two apostrophes
law ml_literal_two_quotes:
  for +x: String
  for e: {ml.text(x) == True{} : Bool}
  {T.parse(String.append("a = '''", String.append(x, "'''''")))
    == T.Doc{"", [T.VPair{"a", T.VStr{String.append(x, "''")}}]} : T.Doc}

# LAW: an empty basic string may end the text: for every bare key k, k=""
# with nothing after it reads k as the empty string
law empty_basic_at_end:
  for +k: String
  for e: {T.bare(k) == True{} : Bool}
  {T.parse(String.append(k, "=\"\"")) == T.Doc{"", [T.VPair{k, T.VStr{""}}]} : T.Doc}

# LAW: and so may an empty literal string: k='' reads k as the empty string
law empty_literal_at_end:
  for +k: String
  for e: {T.bare(k) == True{} : Bool}
  {T.parse(String.append(k, "=''")) == T.Doc{"", [T.VPair{k, T.VStr{""}}]} : T.Doc}

# WP-S: a rendered string read back in any value position. render writes a
# string as key.basic of its characters (laws/StringRenderEscapes.bend); parse reads that text
# back as those characters, as a span of the text or, once a character needs
# an escape, as an owned string, which own reads alike. The laws below read
# one string in each position a value takes: a root pair's value, an array
# item and an inline table's pair. The string must be short: a span counts
# its characters in a U32.

# LAW: a basic string render writes reads back as its text in a root pair:
# for every bare key k and every string s shorter than 2^32 characters,
# k = key.basic(s) and a newline parse with no error to one pair named k
# holding s
law basic_string_reads_back:
  for +k: String
  for ek: {T.bare(k) == True{} : Bool}
  for +s: String
  for es: {D2.short(s) == True{} : Bool}
  {D2.own(T.parse(String.append(k, String.append(" = ", String.append(T.key.basic(s), "\n")))))
    == T.Doc{"", [T.VPair{k, T.VStr{s}}]} : T.Doc}

# LAW: and as an array item: k = [key.basic(s)] and a newline parse with no
# error to one pair named k holding an array of s
law basic_string_reads_back_in_array:
  for +k: String
  for ek: {T.bare(k) == True{} : Bool}
  for +s: String
  for es: {D2.short(s) == True{} : Bool}
  {D2.own(T.parse(String.append(k, String.append(" = [", String.append(T.key.basic(s), "]\n")))))
    == T.Doc{"", [T.VPair{k, T.VArr{[T.VStr{s}]}}]} : T.Doc}

# LAW: and as an inline table's value: k = {v = key.basic(s)} and a newline
# parse with no error to one pair named k holding an inline table whose pair
# v holds s
law basic_string_reads_back_in_inline_table:
  for +k: String
  for ek: {T.bare(k) == True{} : Bool}
  for +s: String
  for es: {D2.short(s) == True{} : Bool}
  {D2.own(T.parse(String.append(k, String.append(" = {v = ", String.append(T.key.basic(s), "}\n")))))
    == T.Doc{"", [T.VPair{k, T.VInl{[T.VPair{"v", T.VStr{s}}]}}]} : T.Doc}

#
# Strings of every form read as the text they denote
# (docs/rfc/eztoml-grammar-proofs.md, WP-S1). For every derivation of a
# string (GString: basic, literal, multi-line basic or multi-line literal,
# with any pieces its form can hold) that matches its rule, the scanner
# reads its text from every state that waits for a value, and the value it
# places is a string, owned or a span, of the characters the derivation
# stands for (g.str.chars): every escape decoded, \u and \U of any scalar
# value in either case, a line-ending backslash dropped with the whitespace
# and newlines after it, the newline right after the opening delimiter
# dropped, one or two quotes inside a multi-line body kept, and every other
# newline kept as written (REVIEW-G9). A span counts its characters in a
# U32, so the characters are fewer than 2^32.

# a text that may follow a string: it is empty, or starts with neither a
# quotation mark nor an apostrophe, which would still belong to it (`""` and
# `''` open multi-line strings, and a multi-line string takes up to two more
# quotes after its closing delimiter)
def s1.free(rest: String) -> Bool:
  match rest:
    case SNil{}:
      True{}
    case SCon{+hh, _tt}:
      Bool.not(Bool.or(Char.is_eq(hh, '"'), Char.is_eq(hh, '\'')))

# a string value holding the characters ss: an owned string of them, or a
# span of a text whose first n characters they are. No other value is one
def s1.holds(vv: T.Val, ss: String) -> Type:
  match vv:
    case T.VStr{tt}:
      {tt == ss : String}
    case T.VSpan{src, +nn}:
      {T.span.str(src, nn, U32.is_zero(nn)) == ss : String}
    case _:
      Empty

# the rest of the walk once a string of the characters ss is read: from the
# state with a string value holding them put where the stack puts values, and
# whatever back, qkind, uni and left the string leaves, the rest of the text
# gives a document PP holds of
def s1.rest(
  +ss: String,
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
    s1.holds(vv, ss) ->
    PP(T.doc.read(rest, T.MScan{T.take.top(sk, vv, "", rw, hs, he, ps, bk, qk, un, lf, ab, False{})}))

# LAW: a string of every form reads as the text it denotes: from every state
# that waits for a value, the text of a string that matches its rule and
# holds fewer than 2^32 characters, then any rest a string may be followed
# by, reads on as the rest from the state with a string value of the
# characters the string stands for put where the state puts values: escapes
# decoded, a line-ending backslash dropped with the whitespace after it, the
# newline right after an opening delimiter dropped, and every other newline
# kept as written. PP is what the caller proves of the document
law string_reads_as_denoted:
  for +st: D3.GString
  for ok: {D1.g.ok.str(st) == True{} : Bool}
  for es: {D2.short(D1.g.str.chars(st)) == True{} : Bool}
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
  for hr: {s1.free(rest) == True{} : Bool}
  for -PP: T.Doc -> Type
  for ih: s1.rest(D1.g.str.chars(st), rw, hs, he, ps, sk, ab, rest, PP)
  PP(T.doc.read(D3.g.str.text(st, rest), T.MScan{D2.vpos(rw, hs, he, ps, bk, qk, sk, un, lf, ab)}))

# LAW: and so as an array's item: from every state that waits for an
# array's item, the string's text and the rest read on as the rest with a
# string value of the characters the string stands for put in the array
law string_reads_as_denoted_in_array:
  for +st: D3.GString
  for ok: {D1.g.ok.str(st) == True{} : Bool}
  for es: {D2.short(D1.g.str.chars(st)) == True{} : Bool}
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
  for hr: {s1.free(rest) == True{} : Bool}
  for -PP: T.Doc -> Type
  for ih: s1.rest(D1.g.str.chars(st), rw, hs, he, ps, sk, ab, rest, PP)
  PP(T.doc.read(D3.g.str.text(st, rest), T.MScan{D2.s1.apos(rw, hs, he, ps, bk, qk, sk, un, lf, ab)}))

# LAW: a string denotes no more characters than its text holds, so in a
# document shorter than 2^32 characters it stands for fewer than 2^32: for
# every string and every text before and after it, when the three together
# are shorter than 2^32 characters, so are the characters the string stands
# for
law string_short_in_document:
  for +pre: String
  for +st: D3.GString
  for +rest: String
  for h: {D2.short(String.append(pre, D3.g.str.text(st, rest))) == True{} : Bool}
  {D2.short(D1.g.str.chars(st)) == True{} : Bool}

# LAW: and so as a document: for every bare key k and every string that
# matches its rule, k = the string and a newline, a document shorter than
# 2^32 characters, parse with no error to one pair named k holding the
# characters the string stands for
law string_parses_as_denoted:
  for +k: String
  for ek: {T.bare(k) == True{} : Bool}
  for +st: D3.GString
  for ok: {D1.g.ok.str(st) == True{} : Bool}
  for es: {D2.short(String.append(k, String.append(" = ", D3.g.str.text(st, "\n")))) == True{} : Bool}
  {D2.own(T.parse(String.append(k, String.append(" = ", D3.g.str.text(st, "\n")))))
    == T.Doc{"", [T.VPair{k, T.VStr{D1.g.str.chars(st)}}]} : T.Doc}

# LAW: and as an array's item: for every bare key k and every string that
# matches its rule, k = [the string] and a newline, a document shorter than
# 2^32 characters, parse with no error to one pair named k holding an array
# of the characters the string stands for
law string_parses_as_denoted_in_array:
  for +k: String
  for ek: {T.bare(k) == True{} : Bool}
  for +st: D3.GString
  for ok: {D1.g.ok.str(st) == True{} : Bool}
  for es: {D2.short(String.append(k, String.append(" = [", D3.g.str.text(st, "]\n")))) == True{} : Bool}
  {D2.own(T.parse(String.append(k, String.append(" = [", D3.g.str.text(st, "]\n")))))
    == T.Doc{"", [T.VPair{k, T.VArr{[T.VStr{D1.g.str.chars(st)}]}}]} : T.Doc}

# LAW: and as an inline table's value: k = {v = the string} and a newline, a
# document shorter than 2^32 characters, parse with no error to one pair
# named k holding an inline table whose pair v holds the characters the
# string stands for
law string_parses_as_denoted_in_inline_table:
  for +k: String
  for ek: {T.bare(k) == True{} : Bool}
  for +st: D3.GString
  for ok: {D1.g.ok.str(st) == True{} : Bool}
  for es: {D2.short(String.append(k, String.append(" = {v = ", D3.g.str.text(st, "}\n")))) == True{} : Bool}
  {D2.own(T.parse(String.append(k, String.append(" = {v = ", D3.g.str.text(st, "}\n")))))
    == T.Doc{"", [T.VPair{k, T.VInl{[T.VPair{"v", T.VStr{D1.g.str.chars(st)}}]}}]} : T.Doc}
