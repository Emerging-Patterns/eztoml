import Base
import ../main.bend as T
import ./defs/BareValueGrammar.bend as D1

# LAW: and a walk still goes on through every segment of the path
law tb_open_after_set:
  for path: List<&2, String>
  for +pre: String
  for +rows: List<&2, T.Val>
  for +new: List<&2, T.Val>
  for +eo: {D1.tb.open(path, rows) == True{} : Bool}
  {D1.tb.open(path, D1.tb.set(path, pre, rows, new)) == True{} : Bool}
