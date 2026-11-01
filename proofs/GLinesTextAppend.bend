# proofs of laws/GLinesTextAppend.bend
import Base
import ../laws/GLinesTextAppend.bend as Laws
import ../laws/defs/GrammarDerivations.bend as D1

def Laws.g_lines_text_append(xs, ys, tail):
  match xs:
    case []:
      {==}
    case D1.GLine{+nl, +ex} <> rest:
      Equal.cong(String, String, zz => String.append(nl, D1.g.expr.text(ex, zz)),
        D1.g.lines.text(List.append(&2, D1.GLine, rest, ys), tail),
        D1.g.lines.text(rest, D1.g.lines.text(ys, tail)), Laws.g_lines_text_append(rest, ys, tail))
