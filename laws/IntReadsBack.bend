import Base
import ../main.bend as T
import ./defs/ScalarReadbackScan.bend as D1

# LAW: a well-formed integer's text then a newline is read from every value
# state as the integer
law int_reads_back:
  for +sg: T.Sign
  for +ds: String
  for +w: {T.wf.int(sg, ds) == True{} : Bool}
  for +fx: D1.Vf
  for +rest: String
  {D1.from_val(fx, String.append(T.render.atom(T.VInt{sg, ds}), SCon{'\n', rest}))
    == D1.after_val(fx, T.VInt{sg, ds}, rest) : T.Doc}
