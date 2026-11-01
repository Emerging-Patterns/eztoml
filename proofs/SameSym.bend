# proofs of laws/SameSym.bend
import Base
import ../main.bend as T
import ../laws/SameSym.bend as Laws
import ../laws/defs/DocumentSameness.bend as D1
import ./lemmas/AndCommutes.bend as M1

# same is an `and` of the two directions
def Laws.same_sym(a, b):
  match a b:
    case T.Doc{_e1, +r1} T.Doc{_e2, +r2}:
      M1.and.comm(D1.same.go(r1, r2), D1.same.go(r2, r1))
