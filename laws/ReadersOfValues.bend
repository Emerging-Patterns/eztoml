# For every value `v`, `string(v)` is its characters when `v` is a string,
# owned or a span, and `""` otherwise; `digits(v)` is its digits when `v` is
# an integer, and `""` otherwise; `flag(v)` is its bit when `v` is a boolean,
# and `false` otherwise
import Base
import ../main.bend as T
import ./defs/StringValueTest.bend as D1

# LAW: string reads the text of an owned string value
law string_of:
  for text: String
  {T.string(T.VStr{text}) == text : String}

# whether a value is an integer
def is_int(vv: T.Val) -> Bool:
  match vv:
    case T.VInt{_ss, _dd}:
      True{}
    case _:
      False{}

# whether a value is a boolean
def is_bool(vv: T.Val) -> Bool:
  match vv:
    case T.VBool{_bb}:
      True{}
    case _:
      False{}

# LAW: string reads a span as the first n characters of its source
law string_of_span:
  for src: String
  for +n: U32
  {T.string(T.VSpan{src, n}) == String.take(src, U32.to_nat(n)) : String}

# LAW: string reads "" from every value that is not a string
law string_of_other:
  for v: T.Val
  for e: {D1.is_string(v) == False{} : Bool}
  {T.string(v) == "" : String}

# LAW: digits reads the digits of an integer
law digits_of:
  for sign: T.Sign
  for text: String
  {T.digits(T.VInt{sign, text}) == text : String}

# LAW: digits reads "" from every value that is not an integer
law digits_of_other:
  for v: T.Val
  for e: {is_int(v) == False{} : Bool}
  {T.digits(v) == "" : String}

# LAW: flag reads the bit of a boolean
law flag_of:
  for bit: Bool
  {T.flag(T.VBool{bit}) == bit : Bool}

# LAW: flag reads false from every value that is not a boolean
law flag_of_other:
  for v: T.Val
  for e: {is_bool(v) == False{} : Bool}
  {T.flag(v) == False{} : Bool}
