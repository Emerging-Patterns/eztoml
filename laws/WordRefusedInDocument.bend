import Base
import ../main.bend as T
import ./defs/AbnfGrammar.bend as D1
import ./defs/BareValueGrammar.bend as D2
import ./defs/GrammarDerivations.bend as D3

# whether a word matches none of toml.abnf's rules for a bare value: a
# boolean, an integer within signed 64 bits, a float, or a date-time within
# RFC 3339's ranges
def bw.none(+cs: List<&2, Char>) -> Bool:
  Bool.not(Bool.or(D1.g.ok.val(D3.GvBoolean{cs}, D1.RVal{}), Bool.or(D1.g.ok.val(D3.GvInteger{cs}, D1.RVal{}),
    Bool.or(D1.g.ok.val(D3.GvFloat{cs}, D1.RVal{}), D1.g.ok.val(D3.GvDateTime{cs}, D1.RVal{})))))

# LAW: a bare word that matches no rule for a bare value leaves the document
# with an error: for every bare key k and such a word w, k = w and a newline
# parse with an error
law word_refused_in_document:
  for +k: String
  for ek: {T.bare(k) == True{} : Bool}
  for +w: String
  for hw: {D2.bw.word(w) == True{} : Bool}
  for hn: {bw.none(String.to_list(w)) == True{} : Bool}
  {String.is_empty(T.bad(T.parse(D1.bw.kv(k, w)))) == False{} : Bool}
