import Base
import ../main.bend as T
import ./defs/DocumentSameness.bend as D1

# LAW: a well-formed document is the same as itself
law same_refl:
  for +d: T.Doc
  for e: {T.wf(d) == True{} : Bool}
  {D1.same(d, d) == True{} : Bool}
