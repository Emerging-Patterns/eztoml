import Base
import ../main.bend as T
import ./defs/ScalarReadbackScan.bend as D1

# a well-formed scalar render writes as a bare value: an integer, a float, a
# boolean or a datetime
def bare_val(vv: T.Val) -> Bool:
  match vv:
    case T.VInt{+sg, +ds}:
      T.wf.int(sg, ds)
    case T.VFlo{_sg, +text}:
      T.wf.flo(text)
    case T.VBool{_b}:
      True{}
    case T.VWhen{ww}:
      T.wf.when(ww)
    case _:
      False{}

# LAW: every well-formed scalar render writes as a bare value, then a newline,
# is read from every value state as itself, put where the state puts values,
# and the text after the newline is read on from there
law scalar_reads_back:
  for +v: T.Val
  for +w: {bare_val(v) == True{} : Bool}
  for +fx: D1.Vf
  for +rest: String
  {D1.from_val(fx, String.append(T.render.atom(v), SCon{'\n', rest})) == D1.after_val(fx, v, rest) : T.Doc}
