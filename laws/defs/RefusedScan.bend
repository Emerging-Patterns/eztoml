# a scan result that holds no value
import Base
import ../../main.bend as T

# a scan result that holds no value
def refused(gg: T.Got) -> Bool:
  match gg:
    case T.GotVal{_val}:
      False{}
    case T.GotBad{_why}:
      True{}
