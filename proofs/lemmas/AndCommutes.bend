# the and of two bits reads the same either way round
import Base

# which of two bits an `and` reads first does not change its answer
def and.comm(xx: Bool, yy: Bool) -> {Bool.and(xx, yy) == Bool.and(yy, xx) : Bool}:
  match xx yy:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}
