import Base
import ./defs/GrammarDerivations.bend as D1

# LAW: a derivation's text is its first expression's text, then its lines'
law g_text_parts:
  for +first: D1.GExpr
  for +rest: List<&2, D1.GLine>
  {D1.g.text(D1.GToml{first, rest}) == String.append(D1.g.expr.text(first, ""), D1.g.lines.text(rest, "")) : String}
