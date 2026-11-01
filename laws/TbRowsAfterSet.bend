import Base
import ../main.bend as T
import ./defs/BareValueGrammar.bend as D1

# LAW: the table a path leads to, once set, holds what it was set to, so the
# next walk along the same path puts into what the last one left
law tb_rows_after_set:
  for path: List<&2, String>
  for +pre: String
  for +rows: List<&2, T.Val>
  for +new: List<&2, T.Val>
  for +eo: {D1.tb.open(path, rows) == True{} : Bool}
  {D1.tb.rows(path, D1.tb.set(path, pre, rows, new)) == new : List<&2, T.Val>}
