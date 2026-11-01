# proofs of laws/BareWordRefusedInArray.bend
import Base
import ../main.bend as T
import ../laws/BareWordRefused.bend as L1
import ../laws/BareWordRefusedInArray.bend as Laws
import ../laws/defs/BareValueGrammar.bend as D1
import ./lemmas/BareWordInArray.bend as M1
import ./lemmas/BareWordRefusal.bend as M2

def Laws.bare_word_refused_in_array(w, hw, why, hv, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, ee):
  Equal.trans(Bool, String.is_empty(T.bad(T.doc.read(String.append(w, rest), T.MScan{D1.s1.apos(rw, hs, he, ps, bk,
    qk, sk, un, lf, ab)}))), String.is_empty(T.bad(T.doc.read(String.append(w, rest), T.MScan{D1.vpos(rw, hs, he, ps,
    T.LVal{}, qk, sk, un, lf, ab)}))), False{},
    Equal.cong(T.Doc, Bool, dd => String.is_empty(T.bad(dd)), T.doc.read(String.append(w, rest),
      T.MScan{D1.s1.apos(rw, hs, he, ps, bk, qk, sk, un, lf, ab)}), T.doc.read(String.append(w, rest),
      T.MScan{D1.vpos(rw, hs, he, ps, T.LVal{}, qk, sk, un, lf, ab)}),
      M1.vl.arr.eq(w, hw, rest, rw, hs, he, ps, bk, qk, sk, un, lf, ab)),
    L1.bare_word_refused(w, hw, why, hv, rw, hs, he, ps, T.LVal{}, qk, sk, un, lf, ab, rest, ee))
