# `at(rows, [])` is `Miss`; `at(rows, [k])` is `get(rows, k)`; and `at(rows, k
# <> ks)` with `ks` nonempty is `at` of the rows of the value `get(rows, k)`
# finds, when that value is a table, an inline table, or one element of an
# array of tables (a `VAot`, which only a hand-built document holds as a
# pair's value), and `Miss` otherwise, a whole array of tables included
import Base
import ../main.bend as T

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
law at_empty:
  for rows: List<&2, T.Val>
  {T.at(rows, []) == T.Miss{} : T.Hit}

# LAW: a path of one key finds what get finds for it
law at_one:
  for rows: List<&2, T.Val>
  for +k: String
  {T.at(rows, [k]) == T.get(rows, k) : T.Hit}

# LAW: a longer path goes on in the rows of the table get finds
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
law at_miss:
  for rows: List<&2, T.Val>
  for +k: String
  for next: String
  for ks: List<&2, String>
  for e: {T.get(rows, k) == T.Miss{} : T.Hit}
  {T.at(rows, k <> next <> ks) == T.Miss{} : T.Hit}

# LAW: a longer path misses when get finds a value with no rows: a string,
# a number, a bit, a datetime, an array, an array of tables or a pair
law at_leaf:
  for rows: List<&2, T.Val>
  for +k: String
  for v: T.Val
  for next: String
  for ks: List<&2, String>
  for e: {T.get(rows, k) == T.Found{v} : T.Hit}
  for f: {holds_no_rows(v) == True{} : Bool}
  {T.at(rows, k <> next <> ks) == T.Miss{} : T.Hit}
