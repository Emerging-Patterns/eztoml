# the test of whether a value is a string, owned or a span
import Base
import ../../main.bend as T

# whether a value is a string, owned or a span
def is_string(vv: T.Val) -> Bool:
  match vv:
    case T.VStr{_tt}:
      True{}
    case T.VSpan{_ss, _nn}:
      True{}
    case _:
      False{}
