# the two fixed texts of the boolean words
import Base
import ../../laws/BoolWord.bend as L1

# Booleans. Both texts are fixed, so both facts compute.

def L1.bool_word(b):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}
