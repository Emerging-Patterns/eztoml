# eztoml reads and writes TOML documents. Values are strings, integers, floats,
# booleans, datetimes, arrays, inline tables, tables, and arrays of tables.
#
# parse, render, get, at, value, root, bad, string, digits, flag
# str, integer, float, boolean, array, inline, table, pair
# segments, quote, key
import Base
import ./toml.bend as T

# a document read from TOML text
def parse(text: String) -> T.Doc:
  T.parse(text)

# a document written back as TOML
def render(doc: T.Doc) -> String:
  T.render(doc)

# the value written for a key, or Miss
def get(rows: List<&2, T.Val>, +name: String) -> T.Hit:
  T.get(rows, name)

# the value at a dotted path
def at(rows: List<&2, T.Val>, path: List<&2, String>) -> T.Hit:
  T.at(rows, path)

# the string written for a key, or "" when the key is absent or not a string
def value(rows: List<&2, T.Val>, +name: String) -> String:
  T.value(rows, name)

# the root table
def root(doc: T.Doc) -> List<&2, T.Val>:
  T.root(doc)

# the first error, or "" when the document is well formed
def bad(doc: T.Doc) -> String:
  T.bad(doc)

# the text of a string value
def string(v: T.Val) -> String:
  T.string(v)

# the digits of an integer value
def digits(v: T.Val) -> String:
  T.digits(v)

# the bit of a boolean value
def flag(v: T.Val) -> Bool:
  T.flag(v)

# a string value
def str(text: String) -> T.Val:
  T.str(text)

# an integer value
def integer(sign: T.Sign, text: String) -> T.Val:
  T.integer(sign, text)

# a float value
def float(sign: T.Sign, text: String) -> T.Val:
  T.float(sign, text)

# a boolean value
def boolean(bit: Bool) -> T.Val:
  T.boolean(bit)

# an array value
def array(items: List<&2, T.Val>) -> T.Val:
  T.array(items)

# an inline table
def inline(rows: List<&2, T.Val>) -> T.Val:
  T.inline(rows)

# a table
def table(path: String, rows: List<&2, T.Val>) -> T.Val:
  T.table(path, rows)

# a key and a value
def pair(name: String, val: T.Val) -> T.Val:
  T.pair(name, val)

# a dotted key's segments, quotes removed
def segments(s: String) -> List<&2, String>:
  T.segments(s)

# a string wrapped in double quotes
def quote(+s: String) -> String:
  T.quote(s)

# a key as TOML writes it
def key(+s: String) -> String:
  T.key(s)
