import Base
import ../main.bend as T
import ./defs/AbnfGrammar.bend as D1
import ./defs/BareValueGrammar.bend as D2
import ./defs/GrammarDerivations.bend as D3

# LAW: a boolean word as an array's item: for every bare key k and every word w
# that matches toml.abnf's boolean rule and denotes v, k = [w] and a newline
# parse with no error to one pair named k holding an array of v
law boolean_parses_as_denoted_in_array:
  for +k: String
  for ek: {T.bare(k) == True{} : Bool}
  for +w: String
  for +hw: {D2.abnf.boolean(String.to_list(w)) == True{} : Bool}
  for +v: T.Val
  for +hv: {D1.g.val(D3.GvBoolean{String.to_list(w)}, v) == True{} : Bool}
  {T.parse(D1.bw.kva(k, w)) == T.Doc{"", [T.VPair{k, T.VArr{[v]}}]} : T.Doc}
