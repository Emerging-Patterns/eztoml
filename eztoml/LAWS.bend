# Laws for eztoml. PROOF.bend proves them.
import Base
import ./main.bend as T

# a lookup answers with the value written for that key
law get_first:
  for +name: String
  for +v: T.Val
  for rest: List<&2, T.Val>
  {T.get(T.VPair{name, v} <> rest, name) == T.Found{v} : T.Hit}

# an empty key is not bare
law bare_needs_a_char:
  for +s: String
  for e: {True{} == String.is_empty(s) : Bool}
  {T.bare(s) == False{} : Bool}

# a bare key is written as itself
law key_is_bare_when_it_can:
  for +s: String
  for e: {True{} == T.bare(s) : Bool}
  {T.key(s) == s : String}

# a key that is not bare is written as a basic string
law key_is_quoted_when_it_must:
  for +s: String
  for e: {False{} == T.bare(s) : Bool}
  {T.key(s) == T.key.basic(s) : String}

# an empty text is an empty document
law parse_empty:
  for +s: String
  for e: {True{} == String.is_empty(s) : Bool}
  {T.parse(s) == T.Doc{"", []} : T.Doc}

# an empty table is written as nothing
law render_empty:
  for bad: String
  {T.render(T.Doc{bad, []}) == "" : String}

# string reads the text of a string value
law string_of:
  for text: String
  {T.string(T.VStr{text}) == text : String}

# digits reads the digits of an integer value
law digits_of:
  for sign: T.Sign
  for text: String
  {T.digits(T.VInt{sign, text}) == text : String}

# flag reads the bit of a boolean value
law flag_of:
  for bit: Bool
  {T.flag(T.VBool{bit}) == bit : Bool}

# one key is the same lookup as get
law at_one:
  for +rows: List<&2, T.Val>
  for +name: String
  {T.at(rows, name <> []) == T.get(rows, name) : T.Hit}

# an empty path misses
law at_empty:
  for rows: List<&2, T.Val>
  {T.at(rows, []) == T.Miss{} : T.Hit}

# root is the document's table
law root_rows:
  for bad: String
  for rows: List<&2, T.Val>
  {T.root(T.Doc{bad, rows}) == rows : List<&2, T.Val>}

# bad is the document's error
law bad_text:
  for text: String
  for rows: List<&2, T.Val>
  {T.bad(T.Doc{text, rows}) == text : String}

# str builds a string value
law str_builds:
  for text: String
  {T.str(text) == T.VStr{text} : T.Val}

# integer builds an integer value
law integer_builds:
  for sign: T.Sign
  for text: String
  {T.integer(sign, text) == T.VInt{sign, text} : T.Val}

# float builds a float value
law float_builds:
  for sign: T.Sign
  for text: String
  {T.float(sign, text) == T.VFlo{sign, text} : T.Val}

# boolean builds a boolean value
law boolean_builds:
  for bit: Bool
  {T.boolean(bit) == T.VBool{bit} : T.Val}

# array builds an array value
law array_builds:
  for items: List<&2, T.Val>
  {T.array(items) == T.VArr{items} : T.Val}

# inline builds an inline table
law inline_builds:
  for rows: List<&2, T.Val>
  {T.inline(rows) == T.VInl{rows} : T.Val}

# table builds a table
law table_builds:
  for path: String
  for rows: List<&2, T.Val>
  {T.table(path, rows) == T.VHead{path, rows} : T.Val}

# pair builds a key and a value
law pair_builds:
  for name: String
  for val: T.Val
  {T.pair(name, val) == T.VPair{name, val} : T.Val}

# the document written back
def again(text: String) -> String:
  T.render(T.parse(text))

# the first error, empty when the document is well formed
def why(text: String) -> String:
  T.bad(T.parse(text))

# the value at a hit, or an empty string when it missed
def read(h: T.Hit) -> T.Val:
  match h:
    case T.Found{v}:
      v
    case T.Miss{}:
      T.VStr{""}

# the string at a root key
def str_at(+text: String, +name: String) -> String:
  T.string(read(T.get(T.root(T.parse(text)), name)))

# the digits at a root key
def dig_at(+text: String, +name: String) -> String:
  T.digits(read(T.get(T.root(T.parse(text)), name)))

# T when the boolean is true
def bit_at.go(bit: Bool) -> String:
  match bit:
    case True{}:
      "T"
    case False{}:
      "F"

# T or F for the boolean at a root key
def bit_at(+text: String, +name: String) -> String:
  bit_at.go(T.flag(read(T.get(T.root(T.parse(text)), name))))

# the string at a two-key path
def path_at(+text: String, +a: String, +b: String) -> String:
  T.string(read(T.at(T.root(T.parse(text)), a <> (b <> []))))

# TOML v1.0.0 / toml.abnf comment: a comment line is ignored and the key is kept
law toml_comment:
  {again("# comment\nkey = \"v\"") ++ again("key = \"v\" # tail")
    ++ again("hash = \"# not\"") ++ str_at("# comment\nkey = \"v\"", "key")
    == "key = \"v\"\n" ++ "key = \"v\"\n" ++ "hash = \"# not\"\n" ++ "v" : String}

# TOML v1.0.0 / toml.abnf boolean: true and false, and True is not a boolean
law toml_bool:
  {again("a = true\nb = false") ++ bit_at("a = true", "a") ++ bit_at("a = false", "a")
    ++ why("a = True")
    == "a = true\nb = false\n" ++ "T" ++ "F" ++ "invalid number" : String}

# TOML v1.0.0 / toml.abnf basic-string, literal-string, ml-basic-string, ml-literal-string
law toml_string:
  {str_at("s = \"A\\nB\\tC\\\"D\\\\E\\u0041\"", "s") ++ str_at("s = 'A\\nB\\\\C'", "s")
    ++ again("s = \"\\b\\f\\r\"") ++ again("s = \"\\u00E9\"") ++ again("s = \"\\U00000041\"")
    ++ again("s = '''I [dw]on't need \\d{2} apples'''")
    ++ again("s = \"\"\"\nRoses are red\nViolets are blue\"\"\"")
    ++ again("s = \"\"\"\\\n  ab\\\n  c\"\"\"")
    ++ why("s = \"\\q\"")
    == "A\nB\tC\"D\\EA" ++ "A\\nB\\\\C"
    ++ "s = \"\\b\\f\\r\"\n" ++ "s = \"é\"\n" ++ "s = \"A\"\n"
    ++ "s = \"I [dw]on't need \\\\d{2} apples\"\n"
    ++ "s = \"Roses are red\\nViolets are blue\"\n" ++ "s = \"abc\"\n"
    ++ "invalid escape" : String}

# TOML v1.0.0 / toml.abnf dec-int, hex-int, oct-int, and bin-int
law toml_integer:
  {again("a = +99\nb = 42\nc = 0\nd = -17\ne = -0\nf = +0")
    ++ again("a = 1_000\nb = 1_2_3") ++ dig_at("a = 1_000", "a")
    ++ again("a = 0x10\nb = 0o10\nc = 0b10\nd = 0xDEAD\ne = 0b1101_0110")
    ++ why("a = 01") ++ why("a = -01") ++ why("a = 1_") ++ why("a = 1__2")
    ++ why("a = _1") ++ why("a = +0x10") ++ why("a = -0x10") ++ why("a = +0o7")
    ++ why("a = +0b1")
    == "a = 99\nb = 42\nc = 0\nd = -17\ne = -0\nf = 0\n"
    ++ "a = 1000\nb = 123\n" ++ "1000"
    ++ "a = 16\nb = 8\nc = 2\nd = 57005\ne = 214\n"
    ++ "invalid number" ++ "invalid number" ++ "invalid underscore"
    ++ "invalid underscore" ++ "invalid number" ++ "invalid number"
    ++ "invalid number" ++ "invalid number" ++ "invalid number" : String}

# TOML v1.0.0 / toml.abnf float and special-float
law toml_float:
  {again("a = +1.0\nb = -0.01\nc = 5e+22\nd = 6.626e-34\ne = -2E-2\nf = 1e06\ng = 1_0.5_0")
    ++ again("a = inf\nb = +inf\nc = -inf\nd = nan\ne = +nan\nf = -nan")
    ++ why("a = .7") ++ why("a = 7.") ++ why("a = 3.e+20") ++ why("a = Inf")
    == "a = 1.0\nb = -0.01\nc = 5e+22\nd = 6.626e-34\ne = -2E-2\nf = 1e06\ng = 10.50\n"
    ++ "a = inf\nb = inf\nc = -inf\nd = nan\ne = nan\nf = -nan\n"
    ++ "invalid number" ++ "invalid number" ++ "invalid exponent"
    ++ "invalid number" : String}

# TOML v1.0.0 / toml.abnf std-table, dotted-key, and quoted-key
law toml_table:
  {again("[pkg]\nname = \"eztoml\"") ++ path_at("[pkg]\nname = \"eztoml\"", "pkg", "name")
    ++ again("a.b = 1") ++ again("fruit .name = \"banana\"") ++ again("[a.b]\nc = 1")
    ++ again("3.14159 = \"pi\"") ++ again("\"127.0.0.1\" = \"value\"")
    ++ again("'key2' = \"value\"") ++ again("1234 = \"v\"")
    ++ again("[fruit.apple]\ncolor = \"red\"\n\n[fruit]\norange = 2")
    ++ again("[fruit.apple]\ncolor = \"red\"\n\n[fruit.apple.texture]\nsmooth = true")
    == "[pkg]\nname = \"eztoml\"\n" ++ "eztoml" ++ "[a]\nb = 1\n"
    ++ "[fruit]\nname = \"banana\"\n" ++ "[a]\n[a.b]\nc = 1\n"
    ++ "[3]\n14159 = \"pi\"\n" ++ "\"127.0.0.1\" = \"value\"\n" ++ "key2 = \"value\"\n"
    ++ "1234 = \"v\"\n" ++ "[fruit]\norange = 2\n[fruit.apple]\ncolor = \"red\"\n"
    ++ "[fruit]\n[fruit.apple]\ncolor = \"red\"\n[fruit.apple.texture]\nsmooth = true\n"
    : String}

# TOML v1.0.0 / toml.abnf inline-table
law toml_inline:
  {again("p = { x = 1, y = 2 }") ++ again("animal = { type.name = \"pug\" }")
    ++ again("p = {}") ++ why("p = { x = 1, }") ++ why("p = { x = 1\n}")
    ++ why("p = { x = 1, x = 2 }")
    == "p = {x = 1, y = 2}\n" ++ "animal = {type = {name = \"pug\"}}\n" ++ "p = {}\n"
    ++ "invalid key" ++ "newline in inline table" ++ "duplicate key" : String}

# TOML v1.0.0 / toml.abnf array
law toml_array:
  {again("a = [1, 2]") ++ again("a = [1, 2,]\nb = []\nc = [[1], [2, 3]]")
    ++ again("a = [\n  1, # c\n  2,\n]")
    == "a = [1, 2]\n" ++ "a = [1, 2]\nb = []\nc = [[1], [2, 3]]\n" ++ "a = [1, 2]\n"
    : String}

# TOML v1.0.0 / toml.abnf array-table
law toml_aot:
  {again("[[fruit]]\nname = \"apple\"\n\n[[fruit]]\nname = \"banana\"")
    ++ again("[[fruit]]\nname = \"apple\"\n\n[[fruit]]")
    ++ why("[[fruit]]\nn = 1\n\n[fruit]\nx = 2")
    ++ why("[fruit]\nn = 1\n\n[[fruit]]\nx = 2")
    == "[[fruit]]\nname = \"apple\"\n[[fruit]]\nname = \"banana\"\n"
    ++ "[[fruit]]\nname = \"apple\"\n[[fruit]]\n" ++ "not a table" ++ "not a table"
    : String}

# TOML v1.0.0 / toml.abnf date-time; RFC 3339 offset-date-time, local-date-time, full-date, partial-time
law toml_datetime:
  {again("a = 1979-05-27T07:32:00Z\nb = 1979-05-27T00:32:00-07:00\nc = 1979-05-27T00:32:00.999999-07:00")
    ++ again("a = 1979-05-27T07:32:00\nb = 1979-05-27\nc = 07:32:00\nd = 00:32:00.999999")
    ++ again("a = 1979-05-27T07:32:00+00:00\nb = 1979-05-27T07:32:60Z")
    ++ again("a = 1979-05-27 07:32:00Z") ++ again("a = 1979-05-27T07:32:00z")
    ++ again("a = 1979-05-27t07:32:00Z") ++ why("a = 07:32:00Z")
    == "a = 1979-05-27T07:32:00Z\nb = 1979-05-27T00:32:00-07:00\nc = 1979-05-27T00:32:00.999999-07:00\n"
    ++ "a = 1979-05-27T07:32:00\nb = 1979-05-27\nc = 07:32:00\nd = 00:32:00.999999\n"
    ++ "a = 1979-05-27T07:32:00+00:00\nb = 1979-05-27T07:32:60Z\n"
    ++ "a = 1979-05-27T07:32:00Z\n" ++ "a = 1979-05-27T07:32:00Z\n"
    ++ "a = 1979-05-27T07:32:00Z\n" ++ "invalid time" : String}

# TOML v1.0.0 / toml.abnf keyval, string, and std-table: rejected documents
law toml_invalid:
  {why("= \"x\"") ++ why("key =") ++ why("k = \"abc") ++ why("name = \"a\"\nname = \"b\"")
    ++ why("spelling = \"a\"\n\"spelling\" = \"b\"")
    ++ why("[fruit]\na = 1\n\n[fruit]\nb = 2")
    ++ why("[fruit]\na = 1\n\n[fruit.a]\nb = 2") ++ why("key = # no\n")
    == "invalid key" ++ "unclosed" ++ "unclosed" ++ "duplicate key" ++ "duplicate key"
    ++ "duplicate table" ++ "not a table" ++ "unclosed" : String}

# a missing key is Miss
law toml_miss:
  {T.get(T.root(T.parse("a = 1")), "nope") == T.Miss{} : T.Hit}

# TOML v1.0.0 / toml.abnf keyval: one pair to a line, and a pair needs a value
law toml_keyval:
  {why("first = \"Tom\" last = \"Preston-Werner\"") ++ why("key = # no")
    ++ why("key # c") ++ again("first = \"Tom\"\nlast = \"Preston-Werner\"")
    == "newline required" ++ "unclosed" ++ "unclosed"
    ++ "first = \"Tom\"\nlast = \"Preston-Werner\"\n" : String}

# TOML v1.0.0 / toml.abnf dot-sep and quoted-key
law toml_dot:
  {again("fruit. name = \"banana\"") ++ again("fruit . name = \"banana\"")
    ++ again("site.\"google.com\" = true") ++ again("site.'google.com' = true")
    ++ again("\"\" = \"blank\"") ++ again("'' = \"blank\"")
    == "[fruit]\nname = \"banana\"\n" ++ "[fruit]\nname = \"banana\"\n"
    ++ "[site]\n\"google.com\" = true\n" ++ "[site]\n\"google.com\" = true\n"
    ++ "\"\" = \"blank\"\n" ++ "\"\" = \"blank\"\n" : String}

# TOML v1.0.0: a table defined by dotted keys is not opened again; a sub-table may be
law toml_reopen:
  {why("[fruit]\napple.color = \"red\"\n\n[fruit.apple]\ntexture = \"smooth\"")
    ++ again("[fruit]\napple.color = \"red\"\n\n[fruit.apple.texture]\nsmooth = true")
    == "duplicate table"
    ++ "[fruit]\n[fruit.apple]\ncolor = \"red\"\n[fruit.apple.texture]\nsmooth = true\n"
    : String}

# TOML v1.0.0: an integer outside signed 64-bit range is an error
law toml_range:
  {again("a = 9223372036854775807") ++ again("a = -9223372036854775808")
    ++ why("a = 9223372036854775808") ++ why("a = -9223372036854775809")
    ++ why("a = 0x8000000000000000") ++ again("a = 0x7fffffffffffffff")
    == "a = 9223372036854775807\n" ++ "a = -9223372036854775808\n"
    ++ "out of range" ++ "out of range" ++ "out of range"
    ++ "a = 9223372036854775807\n" : String}
