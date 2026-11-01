import Base
import ./defs/GrammarDerivations.bend as D1

# LAW: a value's text before a tail is its own text, then the tail
law g_val_text_tail:
  for +vv: D1.GVal
  for +tail: String
  {D1.g.val.text(vv, tail) == String.append(D1.g.val.text(vv, ""), tail) : String}
