# whether some pair in a table's rows has a given name
import Base
import ../../main.bend as T

# whether some pair in the rows has the name k
def has_pair(rows: List<&2, T.Val>, +kk: String) -> Bool:
  match rows:
    case []:
      False{}
    case T.VPair{nn, _vv} <> tt:
      Bool.or(String.eq(nn, kk), has_pair(tt, kk))
    case _ <> tt:
      has_pair(tt, kk)
