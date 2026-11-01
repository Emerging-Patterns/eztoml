# an and of holding parts and the first n characters of a text
import Base

# an `and` of two parts that hold
def and.tt(
  aa: Bool,
  bb: Bool,
  ea: {aa == True{} : Bool},
  eb: {bb == True{} : Bool}
) -> {Bool.and(aa, bb) == True{} : Bool}:
  Equal.trans(Bool, Bool.and(aa, bb), Bool.and(True{}, bb), True{},
    Equal.cong(Bool, Bool, xx => Bool.and(xx, bb), aa, True{}, ea), eb)

# the first n characters of a text
def take(ss: String, nn: Nat) -> String:
  match ss nn:
    case SNil{} _nn:
      SNil{}
    case SCon{_hh, _tt} 0n:
      SNil{}
    case SCon{hh, tt} 1n+pp:
      SCon{hh, take(tt, pp)}
