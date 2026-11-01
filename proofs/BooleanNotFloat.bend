# proofs of laws/BooleanNotFloat.bend
import Base
import ../laws/BooleanNotFloat.bend as Laws
import ../laws/defs/AbnfGrammar.bend as D1
import ./lemmas/GrammarWordMatching.bend as M1

def Laws.boolean_not_float(cs, h):
  M1.gp.bool(zs => {D1.abnf.float(zs) == False{} : Bool}, cs, h, {==}, {==})
