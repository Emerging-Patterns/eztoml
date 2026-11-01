# `get(rows, k)` is `Found{v}` for the value `v` of the first `VPair{k, v}` in
# `rows`, and `Miss` when no pair in `rows` is named `k`
import Base
import ../main.bend as T
import ./defs/PairPresence.bend as D1

# LAW: a pair at the head of a table's rows is what get finds for its name
law get_first:
  for +name: String
  for +v: T.Val
  for rest: List<&2, T.Val>
  {T.get(T.VPair{name, v} <> rest, name) == T.Found{v} : T.Hit}

# whether a value is a pair
def is_pair(vv: T.Val) -> Bool:
  match vv:
    case T.VPair{_nn, _vv}:
      True{}
    case _:
      False{}

# LAW: get passes over a pair of another name
law get_skips_other_name:
  for +n: String
  for v: T.Val
  for rest: List<&2, T.Val>
  for +k: String
  for e: {String.eq(n, k) == False{} : Bool}
  {T.get(T.VPair{n, v} <> rest, k) == T.get(rest, k) : T.Hit}

# LAW: get passes over a value that is not a pair
law get_skips_non_pair:
  for x: T.Val
  for rest: List<&2, T.Val>
  for +k: String
  for e: {is_pair(x) == False{} : Bool}
  {T.get(x <> rest, k) == T.get(rest, k) : T.Hit}

# LAW: get finds the value of the first pair named k, wherever it sits
law get_finds_first:
  for pre: List<&2, T.Val>
  for +k: String
  for v: T.Val
  for post: List<&2, T.Val>
  for +e: {D1.has_pair(pre, k) == False{} : Bool}
  {T.get(List.append(&2, T.Val, pre, T.VPair{k, v} <> post), k)
    == T.Found{v} : T.Hit}

# LAW: get misses when no pair in the rows is named k
law get_misses:
  for rows: List<&2, T.Val>
  for +k: String
  for +e: {D1.has_pair(rows, k) == False{} : Bool}
  {T.get(rows, k) == T.Miss{} : T.Hit}
