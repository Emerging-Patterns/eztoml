# proofs of laws/GTextParts.bend
import Base
import ../laws/GTextParts.bend as Laws
import ../laws/defs/GrammarDerivations.bend as D1
import ./lemmas/GrammarTextParts.bend as M1

def Laws.g_text_parts(first, rest):
  M1.gt.expr(first, D1.g.lines.text(rest, ""))
