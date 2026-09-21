# Laws for eztoml. PROOF.bend proves them.
import Base
import ./toml.bend as T
import ./main.bend as Toml

# a lookup answers with the value written for that key
law get_first:
  for +name: String
  for +v: T.Val
  for rest: List<&2, T.Val>
  {T.get(T.VPair{name, v} <> rest, name) == T.Found{v} : T.Hit}

# the string at a key is the string written for it
law value_string:
  for +name: String
  for +text: String
  for rest: List<&2, T.Val>
  {T.value(T.VPair{name, T.VStr{text}} <> rest, name) == text : String}

# strip of a quoted string is the string
law quote_strip:
  for +s: String
  {T.strip(T.quote(s), '"', '"') == s : String}

# a header always cuts into at least one segment
law segments_never_empty:
  for s: String
  {List.is_empty(&2, String, T.segments(s)) == False{} : Bool}

# a pair of quotes toggles quoting and cuts nothing
law segments_quotes_toggle:
  for s: String
  {T.segments(SCon{'"', SCon{'"', s}}) == T.segments(s) : List<&2, String>}

# a quoted dot stays inside the segment
law segments_quoted_dot:
  for s: String
  {T.segments(SCon{'"', SCon{'.', SCon{'"', s}}})
    == T.seg.fin(T.seg.walk(String.to_list(s), T.Split{False{}, ['.'], []}))
    : List<&2, String>}

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

# the package entry's parse is the implementation's
law parse_is:
  for text: String
  {Toml.parse(text) == T.parse(text) : T.Doc}

# the package entry's render is the implementation's
law render_is:
  for doc: T.Doc
  {Toml.render(doc) == T.render(doc) : String}

# the package entry's get is the implementation's
law get_is:
  for rows: List<&2, T.Val>
  for +name: String
  {Toml.get(rows, name) == T.get(rows, name) : T.Hit}

# the package entry's at is the implementation's
law at_is:
  for rows: List<&2, T.Val>
  for path: List<&2, String>
  {Toml.at(rows, path) == T.at(rows, path) : T.Hit}

# the package entry's value is the implementation's
law value_is:
  for rows: List<&2, T.Val>
  for +name: String
  {Toml.value(rows, name) == T.value(rows, name) : String}

# the package entry's root is the implementation's
law root_is:
  for doc: T.Doc
  {Toml.root(doc) == T.root(doc) : List<&2, T.Val>}

# the package entry's bad is the implementation's
law bad_is:
  for doc: T.Doc
  {Toml.bad(doc) == T.bad(doc) : String}

# the package entry's string is the implementation's
law string_is:
  for v: T.Val
  {Toml.string(v) == T.string(v) : String}

# the package entry's digits is the implementation's
law digits_is:
  for v: T.Val
  {Toml.digits(v) == T.digits(v) : String}

# the package entry's flag is the implementation's
law flag_is:
  for v: T.Val
  {Toml.flag(v) == T.flag(v) : Bool}

# the package entry's str is the implementation's
law str_is:
  for text: String
  {Toml.str(text) == T.str(text) : T.Val}

# the package entry's integer is the implementation's
law integer_is:
  for sign: T.Sign
  for text: String
  {Toml.integer(sign, text) == T.integer(sign, text) : T.Val}

# the package entry's float is the implementation's
law float_is:
  for sign: T.Sign
  for text: String
  {Toml.float(sign, text) == T.float(sign, text) : T.Val}

# the package entry's boolean is the implementation's
law boolean_is:
  for bit: Bool
  {Toml.boolean(bit) == T.boolean(bit) : T.Val}

# the package entry's array is the implementation's
law array_is:
  for items: List<&2, T.Val>
  {Toml.array(items) == T.array(items) : T.Val}

# the package entry's inline is the implementation's
law inline_is:
  for rows: List<&2, T.Val>
  {Toml.inline(rows) == T.inline(rows) : T.Val}

# the package entry's table is the implementation's
law table_is:
  for path: String
  for rows: List<&2, T.Val>
  {Toml.table(path, rows) == T.table(path, rows) : T.Val}

# the package entry's pair is the implementation's
law pair_is:
  for name: String
  for val: T.Val
  {Toml.pair(name, val) == T.pair(name, val) : T.Val}

# the package entry's segments is the implementation's
law segments_is:
  for s: String
  {Toml.segments(s) == T.segments(s) : List<&2, String>}

# the package entry's quote is the implementation's
law quote_is:
  for +s: String
  {Toml.quote(s) == T.quote(s) : String}

# the package entry's key is the implementation's
law key_is:
  for +s: String
  {Toml.key(s) == T.key(s) : String}
