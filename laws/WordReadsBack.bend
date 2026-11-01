import Base
import ../main.bend as T
import ./defs/BareValueGrammar.bend as D1
import ./defs/ScalarReadbackScan.bend as D2

# characters a bare value keeps
def word.rest(ss: String) -> Bool:
  match ss:
    case SNil{}:
      True{}
    case SCon{+hh, tt}:
      Bool.and(D1.word.char(hh), word.rest(tt))

# a bare value: a character that starts one, then characters it keeps
def word.chars(ss: String) -> Bool:
  match ss:
    case SNil{}:
      False{}
    case SCon{+hh, tt}:
      Bool.and(D1.word.first(hh), word.rest(tt))

# LAW: a bare value then a newline is read from every value state as the value
# word.val classifies it as, put where the state puts values, and the text
# after the newline is read on from there
law word_reads_back:
  for +v: T.Val
  for +s: String
  for +hc: {word.chars(s) == True{} : Bool}
  for hv: {T.word.val(String.to_list(s)) == T.GotVal{v} : T.Got}
  for +fx: D2.Vf
  for +rest: String
  {D2.from_val(fx, String.append(s, SCon{'\n', rest})) == D2.after_val(fx, v, rest) : T.Doc}
