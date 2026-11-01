import Base
import ../main.bend as T
import ./defs/RefusedScan.bend as D1

# LAW: a numeral that starts with a zero and an underscore is refused,
# whatever follows: the underscore would hide a leading zero
law num_zero_underscore:
  for +rest: List<&2, Char>
  {D1.refused(T.word.num('0' <> '_' <> rest)) == True{} : Bool}
