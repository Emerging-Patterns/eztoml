# part of: laws/IntegerReadExactly.bend, laws/FloatReadExactly.bend
import Base
import ../main.bend as T
import ./defs/BareValueGrammar.bend as D1

# a sign character
def is_sign(+cc: Char) -> Bool:
  Bool.or(Char.is_eq(cc, '+'), Char.is_eq(cc, '-'))

# LAW: after one sign, a character that is not a sign is read as the first
# character of an unsigned numeral, and the sign is kept
law num_one_sign:
  for +sg: T.Sign
  for +cc: Char
  for e: {False{} == is_sign(cc) : Bool}
  {T.num.step(T.num.step(T.num.start(), D1.mark(sg)), cc)
    == T.num.lead(T.Num{T.NLead{}, sg, 10, [], False{}, False{}, ""}, cc) : T.Num}
