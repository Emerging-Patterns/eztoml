import Base
import ../main.bend as T
import ./defs/AbnfGrammar.bend as D1
import ./defs/BareValueGrammar.bend as D2
import ./defs/GrammarDerivations.bend as D3

# LAW: and as a boolean: k = w parses to the boolean v exactly when w is
# true or false and denotes v
law boolean_parses_exactly:
  for +k: String
  for ek: {T.bare(k) == True{} : Bool}
  for +w: String
  for hw: {D2.bw.word(w) == True{} : Bool}
  for +v: T.Val
  {D1.n1.got.bool(D2.bw.got(T.parse(D1.bw.kv(k, w)), k), v) == Bool.and(D2.abnf.boolean(String.to_list(w)),
    D1.g.val(D3.GvBoolean{String.to_list(w)}, v)) : Bool}
