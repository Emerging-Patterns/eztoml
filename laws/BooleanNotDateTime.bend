import Base
import ./defs/AbnfGrammar.bend as D1
import ./defs/BareValueGrammar.bend as D2

# LAW: no word is both a boolean and a date-time
law boolean_not_date_time:
  for +cs: List<&2, Char>
  for +h: {D2.abnf.boolean(cs) == True{} : Bool}
  {D1.abnf.date_time(cs) == False{} : Bool}
