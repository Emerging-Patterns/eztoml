import Base
import ../main.bend as T
import ./defs/BareValueGrammar.bend as D1

# LAW: in any table, the pass that writes keys writes a pair of a value that
# may sit in a value position as its key, " = " and the value's text, then
# the separator and the rest
law pass_value:
  for +k: String
  for +v: T.Val
  for hw: {D1.cv.wf(v) == True{} : Bool}
  for +rest: List<&2, T.Val>
  for +gap: String
  for +trail: Bool
  {T.render.pass(T.VPair{k, v} <> rest, gap, trail, False{}) == String.append(T.key(k), SCon{' ', SCon{'=',
    SCon{' ', D1.cv.tx(v, String.append(T.render.suf(gap, trail, List.is_empty(&2, T.Val, rest)),
    T.render.pass(rest, gap, trail, False{})))}}}) : String}
