import Base
import ./defs/AbnfGrammar.bend as D1
import ./defs/BareValueGrammar.bend as D2

# LAW: no word is both a boolean and an integer
law boolean_not_integer:
  for +cs: List<&2, Char>
  for +h: {D2.abnf.boolean(cs) == True{} : Bool}
  {D1.abnf.integer(cs) == False{} : Bool}
