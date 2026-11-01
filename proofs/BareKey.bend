# proofs of laws/BareKey.bend
import Base
import ../main.bend as T
import ../laws/BareKey.bend as Laws
import ./lemmas/BareKeyChars.bend as M1

def Laws.bare_needs_a_char(s, e):
  %e : {Bool.and(Bool.not(_), T.bare.all(String.to_list(s))) == False{}
    : Bool}
  {==}
