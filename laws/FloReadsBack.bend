import Base
import ../main.bend as T
import ./defs/ScalarReadbackScan.bend as D1

# LAW: a well-formed float's text then a newline is read from every value
# state as the float
law flo_reads_back:
  for +sg: T.Sign
  for +text: String
  for +w: {T.wf.flo(text) == True{} : Bool}
  for +fx: D1.Vf
  for +rest: String
  {D1.from_val(fx, String.append(T.render.atom(T.VFlo{sg, text}), SCon{'\n', rest}))
    == D1.after_val(fx, T.VFlo{sg, text}, rest) : T.Doc}
