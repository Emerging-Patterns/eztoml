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
