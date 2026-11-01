import Base
import ../main.bend as T
import ./defs/BareValueGrammar.bend as D1
import ./defs/RefusedScan.bend as D2

# LAW: the same after a sign
law word_signed_zero_underscore:
  for sg: T.Sign
  for +rest: List<&2, Char>
  {D2.refused(T.word.val(D1.mark(sg) <> '0' <> '_' <> rest)) == True{} : Bool}
