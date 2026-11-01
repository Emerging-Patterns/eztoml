import Base
import ../main.bend as T
import ./defs/DocumentSameness.bend as D1

# LAW: same does not depend on which document comes first
law same_sym:
  for a: T.Doc
  for b: T.Doc
  {D1.same(a, b) == D1.same(b, a) : Bool}
