import Base
import ./defs/AbnfGrammar.bend as D1

# LAW: no word is both a float and a date-time
law float_not_date_time:
  for +cs: List<&2, Char>
  for +h: {D1.abnf.float(cs) == True{} : Bool}
  {D1.abnf.date_time(cs) == False{} : Bool}
