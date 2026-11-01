import Base
import ../main.bend as T
import ./defs/BareValueGrammar.bend as D1
import ./defs/DocumentSameness.bend as D2

# LAW: a well-formed document is the same as itself with every span read out
law same_own:
  for +d: T.Doc
  for e: {T.wf(d) == True{} : Bool}
  {D2.same(d, D1.own(d)) == True{} : Bool}
