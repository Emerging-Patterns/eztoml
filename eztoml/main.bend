# eztoml: the TOML slice for string-valued sectioned docs. A line is blank, a
# comment, a `[section]` header, or a `key = "value"` pair. A header is a
# dotted path whose segments may be quoted, and a key may be quoted, so a file
# path can be one. No arrays, no inline tables, no numbers.
#
# parse, render, value, sects, segments, quote, key
# types: Kv, Sect, Toml
import Base
import ./toml.bend as T

# a key and the string written for it
def Kv(+key: String, +val: String) -> T.Kv:
  T.Kv{key, val}

# a section header and the pairs under it, in the order they were written
def Sect(+name: String, pairs: List<&2, T.Kv>) -> T.Sect:
  T.Sect{name, pairs}

# the sections read so far, and the first error if there was one
def toml(bad: String, name: String, pairs: List<&2, T.Kv>,
  done: List<&2, T.Sect>) -> T.Toml:
  T.Toml{bad, name, pairs, done}

# the sections of a document, and the first error if there was one
def parse(text: String) -> T.Toml:
  T.parse(text)

# a document of tables, one blank line between them
def render(ss: List<&2, T.Sect>) -> String:
  T.render(ss)

# the value written for a key in a table, or "" when it is absent
def value(pairs: List<&2, T.Kv>, +key: String) -> String:
  T.value(pairs, key)

# the sections a parse found, in the order they were written
def sects(t: T.Toml) -> List<&2, T.Sect>:
  T.sects(t)

# a header's segments, unquoted. `packages."0x0a".files` is three of them
def segments(s: String) -> List<&2, String>:
  T.segments(s)

# a string in quotes, which is how a segment or a key that is not bare is
# written, and how every value is
def quote(+s: String) -> String:
  T.quote(s)

# a key as it is written: bare when it can be, quoted when it must be
def key(+s: String) -> String:
  T.key(s)
