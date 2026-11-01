# proofs of laws/WordSignedZeroUnderscore.bend
import Base
import ../main.bend as T
import ../laws/NumSignedZeroUnderscore.bend as L1
import ../laws/WordSignedZeroUnderscore.bend as Laws
import ./lemmas/SignedNumberRefusal.bend as M1

# after either sign, as for two signs
def Laws.word_signed_zero_underscore(sg, rest):
  match sg:
    case T.Plus{}:
      M1.plus.no('0', '_' <> rest, {==}, {==}, L1.num_signed_zero_underscore(T.Plus{}, rest))
    case T.Minus{}:
      M1.minus.no('0', '_' <> rest, {==}, {==}, L1.num_signed_zero_underscore(T.Minus{}, rest))
