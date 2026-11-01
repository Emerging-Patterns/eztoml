import Base
import ./defs/AbnfGrammar.bend as D1

# LAW: no word is both an integer and a date-time
law integer_not_date_time:
  for +cs: List<&2, Char>
  for +h: {D1.abnf.integer(cs) == True{} : Bool}
  {D1.abnf.date_time(cs) == False{} : Bool}
