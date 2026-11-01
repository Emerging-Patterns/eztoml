import Base
import ../main.bend as T
import ./defs/AbnfGrammar.bend as D1
import ./defs/BareValueGrammar.bend as D2
import ./defs/GrammarDerivations.bend as D3

# LAW: a bare word reads as the boolean v exactly when it matches toml.abnf's
# boolean rule and denotes v: true for true, false for false
law boolean_word_exact:
  for +cs: List<&2, Char>
  for +v: T.Val
  {D1.n1.got.bool(T.word.val(cs), v) == Bool.and(D2.abnf.boolean(cs), D1.g.val(D3.GvBoolean{cs}, v)) : Bool}
