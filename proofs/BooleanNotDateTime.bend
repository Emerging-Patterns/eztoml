# proofs of laws/BooleanNotDateTime.bend
import Base
import ../laws/BooleanNotDateTime.bend as Laws
import ../laws/defs/AbnfGrammar.bend as D1
import ./lemmas/GrammarWordMatching.bend as M1

def Laws.boolean_not_date_time(cs, h):
  M1.gp.bool(zs => {D1.abnf.date_time(zs) == False{} : Bool}, cs, h, {==}, {==})
