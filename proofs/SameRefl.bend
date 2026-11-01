# proofs of laws/SameRefl.bend
import Base
import ../main.bend as T
import ../laws/SameRefl.bend as Laws
import ../laws/defs/DocumentSameness.bend as D1
import ./lemmas/PrefixAndTake.bend as M1
import ./lemmas/ValueSelfEquality.bend as M2

# a well-formed document's rows match themselves: each value does
def Laws.same_refl(d, e):
  match d:
    case T.Doc{_e0, +rows}:
      +rr = {M2.refl.rows(rows, M2.wf.selfs(rows, T.WfRows{""}, e)) : {D1.same.go(rows, rows) == True{} : Bool}}
      M1.and.tt(D1.same.go(rows, rows), D1.same.go(rows, rows), rr, rr)
