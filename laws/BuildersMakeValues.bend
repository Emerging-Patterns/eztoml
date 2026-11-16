import Base
import ../main.bend as T

# The builders make values: each builder makes the value of its kind that
# holds exactly what it is given, so a document built with them is the one
# the caller wrote down.

# LAW: str makes the string value of its text
law str_makes_string:
  for text: String
  {T.str(text) == T.VStr{text} : T.Val}

# LAW: integer makes the integer value of its sign and digits
law integer_makes_integer:
  for sign: T.Sign
  for text: String
  {T.integer(sign, text) == T.VInt{sign, text} : T.Val}

# LAW: float makes the float value of its sign and text
law float_makes_float:
  for sign: T.Sign
  for text: String
  {T.float(sign, text) == T.VFlo{sign, text} : T.Val}

# LAW: boolean makes the boolean value of its bit
law boolean_makes_boolean:
  for bit: Bool
  {T.boolean(bit) == T.VBool{bit} : T.Val}

# LAW: array makes the array of its items, in order
law array_makes_array:
  for items: List<&2, T.Val>
  {T.array(items) == T.VArr{items} : T.Val}

# LAW: inline makes the inline table of its rows, in order
law inline_makes_inline:
  for rows: List<&2, T.Val>
  {T.inline(rows) == T.VInl{rows} : T.Val}

# LAW: table makes the table of its path and rows
law table_makes_table:
  for path: String
  for rows: List<&2, T.Val>
  {T.table(path, rows) == T.VHead{path, rows} : T.Val}

# LAW: pair makes the pair of its name and value
law pair_makes_pair:
  for name: String
  for val: T.Val
  {T.pair(name, val) == T.VPair{name, val} : T.Val}
