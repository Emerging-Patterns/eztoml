# proofs of laws/RenderThenParse.bend
import Base
import ../main.bend as T
import ../laws/RenderThenParse.bend as Laws
import ./lemmas/RenderParseRoundTrip.bend as M1

def Laws.canon_same(d, w):
  match d:
    case T.Doc{+ee, +xs}:
      M1.cs.same(ee, xs, w)
