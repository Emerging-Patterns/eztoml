# proofs of laws/SameOwn.bend
import Base
import ../main.bend as T
import ../laws/SameOwn.bend as Laws
import ../laws/defs/BareValueGrammar.bend as D1
import ../laws/defs/DocumentSameness.bend as D2
import ./lemmas/PrefixAndTake.bend as M1
import ./lemmas/ReadOutEquality.bend as M2
import ./lemmas/ValueSelfEquality.bend as M3

# reading out changes neither direction, and the rows match themselves
def Laws.same_own(d, e):
  match d:
    case T.Doc{_e0, +rows}:
      +rr = {M3.refl.rows(rows, M3.wf.selfs(rows, T.WfRows{""}, e)) : {D2.same.go(rows, rows) == True{} : Bool}}
      Equal.trans(Bool,
        Bool.and(D2.same.go(rows, D1.own.rows(rows)), D2.same.go(D1.own.rows(rows), rows)),
        Bool.and(D2.same.go(rows, rows), D2.same.go(rows, rows)), True{},
        Equal.trans(Bool,
          Bool.and(D2.same.go(rows, D1.own.rows(rows)), D2.same.go(D1.own.rows(rows), rows)),
          Bool.and(D2.same.go(rows, rows), D2.same.go(D1.own.rows(rows), rows)),
          Bool.and(D2.same.go(rows, rows), D2.same.go(rows, rows)),
          Equal.cong(Bool, Bool, xx => Bool.and(xx, D2.same.go(D1.own.rows(rows), rows)),
            D2.same.go(rows, D1.own.rows(rows)), D2.same.go(rows, rows), M2.own.r(rows, rows)),
          Equal.cong(Bool, Bool, yy => Bool.and(D2.same.go(rows, rows), yy),
            D2.same.go(D1.own.rows(rows), rows), D2.same.go(rows, rows), M2.own.l(rows, rows))),
        M1.and.tt(D2.same.go(rows, rows), D2.same.go(rows, rows), rr, rr))
