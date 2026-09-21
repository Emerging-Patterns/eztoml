# eztoml: TOML documents. `parse` reads text. `render` writes a value.
# `get` and `at` read a value back out.
import Base
import ./parse.bend as P
import ./print.bend as R
import ./value.bend as V
import ./text.bend as Txt

# the table in `text`, and the first error if there was one
def parse(text: String) -> P.Doc:
  P.parse(text)

# a value as TOML text
def render(v: V.Val) -> String:
  R.render(v)

# the table a parse built
def root(d: P.Doc) -> V.Val:
  match d:
    case P.Doc{_err, rt}:
      rt

# the first error a parse kept, or empty
def err(d: P.Doc) -> String:
  match d:
    case P.Doc{e, _rt}:
      e

# the value written for a key, or a missing key
def get(v: V.Val, key: String) -> V.Val:
  V.get(v, key)

# the cell at an index, or a missing key
def at(v: V.Val, n: Nat) -> V.Val:
  V.at(v, n)

# the text of a string value
def str(v: V.Val) -> Maybe<&2, String>:
  V.str(v)

# the written digits of an integer value
def integer(v: V.Val) -> Maybe<&2, String>:
  V.integer(v)

# the written digits of a float value
def float(v: V.Val) -> Maybe<&2, String>:
  V.float(v)

# the bit of a boolean value
def boolean(v: V.Val) -> Maybe<&2, Bool>:
  V.boolean(v)

# the written text of a datetime value
def datetime(v: V.Val) -> Maybe<&2, String>:
  V.datetime(v)

# the root table, with no pairs
def empty() -> V.Val:
  V.empty()

# a missing key
def miss() -> V.Val:
  V.miss()

# the end of a chain of cells
def nil() -> V.Val:
  V.nil()

# one array cell in front of the rest
def cons(head: V.Val, tail: V.Val) -> V.Val:
  V.cons(head, tail)

# one table pair in front of the rest
def pair(+key: String, val: V.Val, rest: V.Val) -> V.Val:
  V.pair(key, val, rest)

# a table from its pairs
def table(pairs: V.Val) -> V.Val:
  V.table(pairs)

# an array from its cells
def array(items: V.Val) -> V.Val:
  V.array(items)

# a string value
def string(+s: String) -> V.Val:
  V.string(s)

# an integer value, as its written digits
def int(+raw: String) -> V.Val:
  V.int(raw)

# a float value, as its written digits
def num(+raw: String) -> V.Val:
  V.num(raw)

# a boolean value
def flag(b: Bool) -> V.Val:
  V.flag(b)

# an offset datetime, as its written text
def offset(+raw: String) -> V.Val:
  V.offset(raw)

# a local datetime, as its written text
def local(+raw: String) -> V.Val:
  V.local(raw)

# a local date, as its written text
def day(+raw: String) -> V.Val:
  V.day(raw)

# a local time, as its written text
def time(+raw: String) -> V.Val:
  V.time(raw)

# a header's segments, unquoted
def segments(s: String) -> List<&2, String>:
  Txt.segments(s)

# a basic string in quotes
def quote(+s: String) -> String:
  Txt.quote(s)

# a key as it is written: bare when it can be, quoted when it must be
def key(+s: String) -> String:
  Txt.key(s)
