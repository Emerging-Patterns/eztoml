import Base
import ../main.bend as T
import ./defs/ScalarReadbackScan.bend as D1

# LAW: a well-formed datetime's text then a newline is read from every value
# state as the datetime
law when_reads_back:
  for +w: T.When
  for +h: {T.wf.when(w) == True{} : Bool}
  for +fx: D1.Vf
  for +rest: String
  {D1.from_val(fx, String.append(T.render.atom(T.VWhen{w}), SCon{'\n', rest}))
    == D1.after_val(fx, T.VWhen{w}, rest) : T.Doc}
