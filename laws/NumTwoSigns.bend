# part of: laws/IntegerReadExactly.bend, laws/FloatReadExactly.bend
import Base
import ../main.bend as T
import ./defs/BareValueGrammar.bend as D1
import ./defs/RefusedScan.bend as D2

# LAW: a numeral that starts with two signs is refused, whatever follows
law num_two_signs:
  for s1: T.Sign
  for s2: T.Sign
  for +rest: List<&2, Char>
  {D2.refused(T.word.num(D1.mark(s1) <> D1.mark(s2) <> rest)) == True{} : Bool}
