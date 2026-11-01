# proofs of laws/WordZeroUnderscore.bend
import Base
import ../main.bend as T
import ../laws/NumZeroUnderscore.bend as L1
import ../laws/WordZeroUnderscore.bend as Laws
import ./lemmas/SignedNumberRefusal.bend as M1

# a word that starts with a digit is no special, and both routes refuse it
def Laws.word_zero_underscore(rest):
  M1.route.no(T.word.as_date(M1.word.date('0' <> '_' <> rest), T.word.ee('0' <> '_' <> rest)),
    '0' <> '_' <> rest, {==}, L1.num_zero_underscore(rest))
