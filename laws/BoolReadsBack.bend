import Base
import ../main.bend as T
import ./defs/ScalarReadbackScan.bend as D1

# LAW: a boolean's text then a newline is read from every value state as the
# boolean
law bool_reads_back:
  for +b: Bool
  for +fx: D1.Vf
  for +rest: String
  {D1.from_val(fx, String.append(T.render.atom(T.VBool{b}), SCon{'\n', rest}))
    == D1.after_val(fx, T.VBool{b}, rest) : T.Doc}
