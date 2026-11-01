import Base
import ./defs/AbnfGrammar.bend as D1

# LAW: no word is both an integer and a float
law integer_not_float:
  for +cs: List<&2, Char>
  for +h: {D1.abnf.integer(cs) == True{} : Bool}
  {D1.abnf.float(cs) == False{} : Bool}
