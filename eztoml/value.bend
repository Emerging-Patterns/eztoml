# eztoml/value: a TOML value. Arrays and tables keep their cells in the value
# (VCons, VPair, VNil). VMiss is what a missing key reads as.
import Base

# a TOML value
type Val is Data:
  VStr{s: String}
  VInt{raw: String}
  VFloat{raw: String}
  VBool{b: Bool}
  VOff{raw: String}
  VLocal{raw: String}
  VDay{raw: String}
  VTime{raw: String}
  VArr{items: Val, aot: Bool}
  VTab{pairs: Val, explicit: Bool, inline: Bool}
  VNil{}
  VCons{head: Val, tail: Val}
  VPair{key: String, val: Val, rest: Val}
  VMiss{}

# the root table, with no pairs
def empty() -> Val:
  VTab{VNil{}, False{}, False{}}

# a missing key
def miss() -> Val:
  VMiss{}

# the end of a chain of cells
def nil() -> Val:
  VNil{}

# one array cell in front of the rest
def cons(head: Val, tail: Val) -> Val:
  VCons{head, tail}

# one table pair in front of the rest
def pair(+key: String, val: Val, rest: Val) -> Val:
  VPair{key, val, rest}

# a table from its pairs
def table(pairs: Val) -> Val:
  VTab{pairs, True{}, False{}}

# an array from its cells
def array(items: Val) -> Val:
  VArr{items, False{}}

# a string value
def string(+s: String) -> Val:
  VStr{s}

# an integer value, as its written digits
def int(+raw: String) -> Val:
  VInt{raw}

# a float value, as its written digits
def num(+raw: String) -> Val:
  VFloat{raw}

# a boolean value
def flag(b: Bool) -> Val:
  VBool{b}

# an offset datetime, as its written text
def offset(+raw: String) -> Val:
  VOff{raw}

# a local datetime, as its written text
def local(+raw: String) -> Val:
  VLocal{raw}

# a local date, as its written text
def day(+raw: String) -> Val:
  VDay{raw}

# a local time, as its written text
def time(+raw: String) -> Val:
  VTime{raw}

# the value at a key, else the rest of the table
def get.at(here: Val, rest: Val, hit: Bool) -> Val:
  Bool.pick(Val, hit, here, rest)

# the value written for a key in a pair chain
def get.go(pairs: Val, +k: String) -> Val:
  match pairs:
    case VNil{}:
      VMiss{}
    case VPair{+n, v, r}:
      get.at(v, get.go(r, k), String.eq(n, k))
    case _:
      VMiss{}

# the value written for a key in a table, or VMiss
def get(v: Val, key: String) -> Val:
  match v:
    case VTab{pairs, _explicit, _inline}:
      get.go(pairs, key)
    case _:
      VMiss{}

# the cell at an index, else VMiss
def at.go(items: Val, n: Nat) -> Val:
  match items:
    case VCons{h, t}:
      match n:
        case 0n:
          h
        case 1n+p:
          at.go(t, p)
    case _:
      VMiss{}

# the cell at an index of an array, or VMiss
def at(v: Val, n: Nat) -> Val:
  match v:
    case VArr{items, _aot}:
      at.go(items, n)
    case _:
      VMiss{}

# the text of a string value
def str(v: Val) -> Maybe<&2, String>:
  match v:
    case VStr{s}:
      Some{s}
    case _:
      None{}

# the written digits of an integer value
def integer(v: Val) -> Maybe<&2, String>:
  match v:
    case VInt{raw}:
      Some{raw}
    case _:
      None{}

# the written digits of a float value
def float(v: Val) -> Maybe<&2, String>:
  match v:
    case VFloat{raw}:
      Some{raw}
    case _:
      None{}

# the bit of a boolean value
def boolean(v: Val) -> Maybe<&2, Bool>:
  match v:
    case VBool{b}:
      Some{b}
    case _:
      None{}

# the written text of a datetime value
def datetime(v: Val) -> Maybe<&2, String>:
  match v:
    case VOff{raw}:
      Some{raw}
    case VLocal{raw}:
      Some{raw}
    case VDay{raw}:
      Some{raw}
    case VTime{raw}:
      Some{raw}
    case _:
      None{}
