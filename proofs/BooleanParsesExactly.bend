# proofs of laws/BooleanParsesExactly.bend
import Base
import ../main.bend as T
import ../laws/BooleanParsesExactly.bend as Laws
import ../laws/BooleanWordExact.bend as L1
import ../laws/defs/AbnfGrammar.bend as D1
import ../laws/defs/BareValueGrammar.bend as D2
import ../laws/defs/GrammarDerivations.bend as D3
import ./lemmas/BareWordRefusal.bend as M1
import ./lemmas/BooleanWordExact.bend as M2

# nor a boolean
def vl.norm.bool(gg: T.Got, +vv: T.Val) -> {D1.n1.got.bool(M1.vl.norm(gg), vv) == D1.n1.got.bool(gg, vv) : Bool}:
  match gg:
    case T.GotVal{_v}:
      {==}
    case T.GotBad{_why}:
      {==}

def Laws.boolean_parses_exactly(k, ek, w, hw, v):
  Equal.trans(Bool, D1.n1.got.bool(D2.bw.got(T.parse(D1.bw.kv(k, w)), k), v),
    D1.n1.got.bool(M1.vl.norm(T.word.val(String.to_list(w))), v),
    Bool.and(D2.abnf.boolean(String.to_list(w)), D1.g.val(D3.GvBoolean{String.to_list(w)}, v)),
    Equal.cong(T.Got, Bool, gg => D1.n1.got.bool(gg, v), D2.bw.got(T.parse(D1.bw.kv(k, w)), k),
      M1.vl.norm(T.word.val(String.to_list(w))), M1.vl.pv(k, ek, w, hw)),
    Equal.trans(Bool, D1.n1.got.bool(M1.vl.norm(T.word.val(String.to_list(w))), v),
      D1.n1.got.bool(T.word.val(String.to_list(w)), v),
      Bool.and(D2.abnf.boolean(String.to_list(w)), D1.g.val(D3.GvBoolean{String.to_list(w)}, v)),
      vl.norm.bool(T.word.val(String.to_list(w)), v), L1.boolean_word_exact(String.to_list(w), v)))
