import Base
import ../main.bend as T
import ./defs/RefusedScan.bend as D1

# LAW: a bare word that starts with a zero and an underscore, with or without
# a sign, holds no value, whatever follows
law word_zero_underscore:
  for +rest: List<&2, Char>
  {D1.refused(T.word.val('0' <> '_' <> rest)) == True{} : Bool}
