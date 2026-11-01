# proofs of laws/WordTwoSigns.bend
import Base
import ../main.bend as T
import ../laws/NumTwoSigns.bend as L1
import ../laws/WordTwoSigns.bend as Laws
import ./lemmas/SignedNumberRefusal.bend as M1

# each pair of signs: no special, and both routes refuse it
def Laws.word_two_signs(s1, s2, rest):
  match s1 s2:
    case T.Plus{} T.Plus{}:
      M1.plus.no('+', rest, {==}, {==}, L1.num_two_signs(T.Plus{}, T.Plus{}, rest))
    case T.Plus{} T.Minus{}:
      M1.plus.no('-', rest, {==}, {==}, L1.num_two_signs(T.Plus{}, T.Minus{}, rest))
    case T.Minus{} T.Plus{}:
      M1.minus.no('+', rest, {==}, {==}, L1.num_two_signs(T.Minus{}, T.Plus{}, rest))
    case T.Minus{} T.Minus{}:
      M1.minus.no('-', rest, {==}, {==}, L1.num_two_signs(T.Minus{}, T.Minus{}, rest))
