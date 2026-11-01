# proofs of laws/BooleanNotInteger.bend
import Base
import ../laws/BooleanNotInteger.bend as Laws
import ../laws/defs/AbnfGrammar.bend as D1
import ./lemmas/GrammarWordMatching.bend as M1

def Laws.boolean_not_integer(cs, h):
  M1.gp.bool(zs => {D1.abnf.integer(zs) == False{} : Bool}, cs, h, {==}, {==})
