# proofs of laws/ScalarReadsBack.bend
import Base
import ../main.bend as T
import ../src/eq.bend as Eq
import ../laws/BoolReadsBack.bend as L1
import ../laws/FloReadsBack.bend as L2
import ../laws/IntReadsBack.bend as L3
import ../laws/ScalarReadsBack.bend as Laws
import ../laws/WhenReadsBack.bend as L4
import ../laws/defs/ScalarReadbackScan.bend as D1
import ./lemmas/ValueTextReadback.bend as M1

def Laws.scalar_reads_back(v, w, fx, rest):
  match v:
    case T.VInt{+sg, +ds}:
      L3.int_reads_back(sg, ds, w, fx, rest)
    case T.VFlo{+sg, +text}:
      L2.flo_reads_back(sg, text, w, fx, rest)
    case T.VBool{+bb}:
      L1.bool_reads_back(bb, fx, rest)
    case T.VWhen{+ww}:
      L4.when_reads_back(ww, w, fx, rest)
    case T.VStr{tx}:
      Eq.bit.absurd(&2, {D1.from_val(fx, String.append(T.render.atom(T.VStr{tx}), SCon{'\n', rest}))
        == D1.after_val(fx, T.VStr{tx}, rest) : T.Doc}, w)
    case T.VSpan{src, nn}:
      Eq.bit.absurd(&2, {D1.from_val(fx, String.append(T.render.atom(T.VSpan{src, nn}), SCon{'\n', rest}))
        == D1.after_val(fx, T.VSpan{src, nn}, rest) : T.Doc}, w)
    case T.VArr{it}:
      Eq.bit.absurd(&2, {D1.from_val(fx, String.append(T.render.atom(T.VArr{it}), SCon{'\n', rest}))
        == D1.after_val(fx, T.VArr{it}, rest) : T.Doc}, w)
    case T.VInl{rs}:
      Eq.bit.absurd(&2, {D1.from_val(fx, String.append(T.render.atom(T.VInl{rs}), SCon{'\n', rest}))
        == D1.after_val(fx, T.VInl{rs}, rest) : T.Doc}, w)
    case T.VHead{pp, rs}:
      Eq.bit.absurd(&2, {D1.from_val(fx, String.append(T.render.atom(T.VHead{pp, rs}), SCon{'\n', rest}))
        == D1.after_val(fx, T.VHead{pp, rs}, rest) : T.Doc}, w)
    case T.VAot{pp, rs}:
      Eq.bit.absurd(&2, {D1.from_val(fx, String.append(T.render.atom(T.VAot{pp, rs}), SCon{'\n', rest}))
        == D1.after_val(fx, T.VAot{pp, rs}, rest) : T.Doc}, w)
    case T.VAots{pp, es}:
      Eq.bit.absurd(&2, {D1.from_val(fx, String.append(T.render.atom(T.VAots{pp, es}), SCon{'\n', rest}))
        == D1.after_val(fx, T.VAots{pp, es}, rest) : T.Doc}, w)
    case T.VPair{nm, vv}:
      Eq.bit.absurd(&2, {D1.from_val(fx, String.append(T.render.atom(T.VPair{nm, vv}), SCon{'\n', rest}))
        == D1.after_val(fx, T.VPair{nm, vv}, rest) : T.Doc}, w)
