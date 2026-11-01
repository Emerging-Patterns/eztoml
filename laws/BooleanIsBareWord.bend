import Base
import ./defs/BareValueGrammar.bend as D1

# LAW: and every word the boolean rule matches
law boolean_is_bare_word:
  for +w: String
  for h: {D1.abnf.boolean(String.to_list(w)) == True{} : Bool}
  {D1.bw.word(w) == True{} : Bool}
