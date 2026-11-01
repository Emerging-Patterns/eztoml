import Base
import ./defs/GrammarDerivations.bend as D1

# LAW: the lines after a document's first expression, split anywhere, spell
# the first part's text and then the second's
law g_lines_text_append:
  for +xs: List<&2, D1.GLine>
  for +ys: List<&2, D1.GLine>
  for +tail: String
  {D1.g.lines.text(List.append(&2, D1.GLine, xs, ys), tail) == D1.g.lines.text(xs, D1.g.lines.text(ys, tail)) : String}
