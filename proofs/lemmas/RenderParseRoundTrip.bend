# rendering a document and parsing it gives back the same document
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/PassValue.bend as L1
import ../../laws/RenderThenParse.bend as L2
import ../../laws/defs/BareValueGrammar.bend as D1
import ../../laws/defs/DocumentSameness.bend as D2
import ../../laws/defs/KeySegmentSpelling.bend as D3
import ../../laws/defs/PartialDerivationRules.bend as D4
import ./DecimalArithmetic.bend as M1
import ./FreshNamesInRows.bend as M2
import ./PrefixAndTake.bend as M3
import ./ReadOutEquality.bend as M4
import ./RenderedHeaderLines.bend as M5
import ./ReorderedTableNames.bend as M6
import ./ShortTextBounds.bend as M7
import ./SignedNumberRefusal.bend as M8
import ./StringAndPathLimits.bend as M9
import ./ValuePassText.bend as M10
import ./ValueSelfEquality.bend as M11
import ./ValueTextReadback.bend as M12

# one text for another equal to it
def se.cast(aa: String, bb: String, ee: {aa == bb : String}, hh: M9.se(aa)) -> M9.se(bb):
  %ee : M9.se(_)
  hh

# a header's bracket
def se.br(+xx: String) -> M9.se(SCon{'[', xx}):
  {==}

# a key as key writes it, bare or quoted
def se.kg(
  bb: Bool,
  +kk: String,
  eb: {T.bare(kk) == bb : Bool},
  +ww: String
) -> M9.se(String.append(T.key.go(bb, kk), ww)):
  match bb:
    case True{}:
      M5.kl.start1(D3.Seg{D3.SpBare{}, kk}, ww, eb)
    case False{}:
      M5.kl.start1(D3.Seg{D3.SpBasic{}, kk}, ww, {==})

# a key as key writes it
def se.key(+kk: String, +ww: String) -> M9.se(String.append(T.key(kk), ww)):
  se.kg(T.bare(kk), kk, {==}, ww)

# the key pass's text, then any text read so
def se.P(
  xs: List<&2, T.Val>,
  +hp: String,
  +zz: String,
  +hw: {T.wf.go(xs, T.WfRows{hp}) == True{} : Bool},
  hz: M9.se(zz)
) -> M9.se(String.append(T.render.pass(xs, "\n", True{}, False{}), zz)):
  match xs:
    case []:
      hz
    case T.VPair{+kk, T.VHead{+p, +r}} <> +t:
      se.P(t, hp, zz, M7.wt.more(T.wf.go(r, T.WfRows{p}), _v => T.wf.go(t, T.WfRows{hp}),
          M7.wt.more(Bool.and(T.wf.key(kk, t),
        T.str.eq(p, T.tree.pre(hp, kk))), _u => T.wf.then(T.wf.go(r, T.WfRows{p}), _v => T.wf.go(t, T.WfRows{hp})),
          hw)), hz)
    case T.VPair{+kk, T.VAots{+p, +es}} <> +t:
      se.P(t, hp, zz, M7.wt.more(T.wf.go(es, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}),
          M7.wt.more(Bool.and(Bool.not(
        List.is_empty(&2, T.Val, es)), Bool.and(T.wf.key(kk, t), T.str.eq(p, T.tree.pre(hp, kk)))),
          _u => T.wf.then(T.wf.go(es,
        T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp})), hw)), hz)
    case T.VPair{+kk, T.VStr{+a1}} <> +t:
      se.cast(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VStr{a1}, String.append(SCon{'\n',
        T.render.pass(t, "\n", True{}, False{})}, zz))}}}),
        String.append(T.render.pass(T.VPair{kk, T.VStr{a1}} <> t, "\n", True{}, False{}), zz),
        Equal.sym(String, String.append(T.render.pass(T.VPair{kk, T.VStr{a1}} <> t, "\n", True{}, False{}), zz),
          String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ',
          D1.cv.tx(T.VStr{a1}, String.append(SCon{'\n', T.render.pass(t, "\n", True{}, False{})}, zz))}}}),
          Equal.trans(String, String.append(T.render.pass(T.VPair{kk, T.VStr{a1}} <> t, "\n", True{}, False{}), zz),
            String.append(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VStr{a1}, SCon{'\n',
              T.render.pass(t, "\n", True{}, False{})})}}}), zz),
            String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VStr{a1}, String.append(SCon{'\n',
              T.render.pass(t, "\n", True{}, False{})}, zz))}}}),
            Equal.cong(String, String, ss => String.append(ss, zz), T.render.pass(T.VPair{kk, T.VStr{a1}} <> t, "\n",
              True{}, False{}),
              String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VStr{a1}, SCon{'\n', T.render.pass(t,
                "\n", True{}, False{})})}}}),
              L1.pass_value(kk, T.VStr{a1}, Eq.and.left(T.wf.atom(T.VStr{a1}), T.wf.key(kk, t),
                M7.wt.ok(Bool.and(T.wf.atom(T.VStr{a1}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}), hw)), t,
                    "\n",
                True{})),
            M12.kp.txt(kk, T.VStr{a1}, SCon{'\n', T.render.pass(t, "\n", True{}, False{})}, zz))),
        se.key(kk, SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VStr{a1}, String.append(SCon{'\n', T.render.pass(t, "\n",
          True{}, False{})}, zz))}}}))
    case T.VPair{+kk, T.VSpan{+a1, +a2}} <> +t:
      se.cast(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VSpan{a1, a2},
        String.append(SCon{'\n', T.render.pass(t, "\n", True{}, False{})}, zz))}}}),
        String.append(T.render.pass(T.VPair{kk, T.VSpan{a1, a2}} <> t, "\n", True{}, False{}), zz),
        Equal.sym(String, String.append(T.render.pass(T.VPair{kk, T.VSpan{a1, a2}} <> t, "\n", True{}, False{}), zz),
          String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ',
          D1.cv.tx(T.VSpan{a1, a2}, String.append(SCon{'\n', T.render.pass(t, "\n", True{}, False{})}, zz))}}}),
          Equal.trans(String, String.append(T.render.pass(T.VPair{kk, T.VSpan{a1, a2}} <> t, "\n", True{}, False{}),
            zz),
            String.append(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VSpan{a1, a2}, SCon{'\n',
              T.render.pass(t, "\n", True{}, False{})})}}}), zz),
            String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VSpan{a1, a2}, String.append(SCon{'\n',
              T.render.pass(t, "\n", True{}, False{})}, zz))}}}),
            Equal.cong(String, String, ss => String.append(ss, zz), T.render.pass(T.VPair{kk, T.VSpan{a1, a2}} <> t,
              "\n", True{}, False{}),
              String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VSpan{a1, a2}, SCon{'\n',
                T.render.pass(t, "\n", True{}, False{})})}}}),
              L1.pass_value(kk, T.VSpan{a1, a2}, Eq.and.left(T.wf.atom(T.VSpan{a1, a2}), T.wf.key(kk, t),
                M7.wt.ok(Bool.and(T.wf.atom(T.VSpan{a1, a2}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}), hw)), t,
                "\n", True{})),
            M12.kp.txt(kk, T.VSpan{a1, a2}, SCon{'\n', T.render.pass(t, "\n", True{}, False{})}, zz))),
        se.key(kk, SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VSpan{a1, a2}, String.append(SCon{'\n', T.render.pass(t,
          "\n", True{}, False{})}, zz))}}}))
    case T.VPair{+kk, T.VInt{+a1, +a2}} <> +t:
      se.cast(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VInt{a1, a2}, String.append(SCon{'\n',
        T.render.pass(t, "\n", True{}, False{})}, zz))}}}),
        String.append(T.render.pass(T.VPair{kk, T.VInt{a1, a2}} <> t, "\n", True{}, False{}), zz),
        Equal.sym(String, String.append(T.render.pass(T.VPair{kk, T.VInt{a1, a2}} <> t, "\n", True{}, False{}), zz),
          String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ',
          D1.cv.tx(T.VInt{a1, a2}, String.append(SCon{'\n', T.render.pass(t, "\n", True{}, False{})}, zz))}}}),
          Equal.trans(String, String.append(T.render.pass(T.VPair{kk, T.VInt{a1, a2}} <> t, "\n", True{}, False{}), zz),
            String.append(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VInt{a1, a2}, SCon{'\n',
              T.render.pass(t, "\n", True{}, False{})})}}}), zz),
            String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VInt{a1, a2}, String.append(SCon{'\n',
              T.render.pass(t, "\n", True{}, False{})}, zz))}}}),
            Equal.cong(String, String, ss => String.append(ss, zz), T.render.pass(T.VPair{kk, T.VInt{a1, a2}} <> t,
              "\n", True{}, False{}),
              String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VInt{a1, a2}, SCon{'\n',
                T.render.pass(t, "\n", True{}, False{})})}}}),
              L1.pass_value(kk, T.VInt{a1, a2}, Eq.and.left(T.wf.atom(T.VInt{a1, a2}), T.wf.key(kk, t),
                M7.wt.ok(Bool.and(T.wf.atom(T.VInt{a1, a2}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}), hw)), t,
                "\n", True{})),
            M12.kp.txt(kk, T.VInt{a1, a2}, SCon{'\n', T.render.pass(t, "\n", True{}, False{})}, zz))),
        se.key(kk, SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VInt{a1, a2}, String.append(SCon{'\n', T.render.pass(t,
          "\n", True{}, False{})}, zz))}}}))
    case T.VPair{+kk, T.VFlo{+a1, +a2}} <> +t:
      se.cast(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VFlo{a1, a2}, String.append(SCon{'\n',
        T.render.pass(t, "\n", True{}, False{})}, zz))}}}),
        String.append(T.render.pass(T.VPair{kk, T.VFlo{a1, a2}} <> t, "\n", True{}, False{}), zz),
        Equal.sym(String, String.append(T.render.pass(T.VPair{kk, T.VFlo{a1, a2}} <> t, "\n", True{}, False{}), zz),
          String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ',
          D1.cv.tx(T.VFlo{a1, a2}, String.append(SCon{'\n', T.render.pass(t, "\n", True{}, False{})}, zz))}}}),
          Equal.trans(String, String.append(T.render.pass(T.VPair{kk, T.VFlo{a1, a2}} <> t, "\n", True{}, False{}), zz),
            String.append(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VFlo{a1, a2}, SCon{'\n',
              T.render.pass(t, "\n", True{}, False{})})}}}), zz),
            String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VFlo{a1, a2}, String.append(SCon{'\n',
              T.render.pass(t, "\n", True{}, False{})}, zz))}}}),
            Equal.cong(String, String, ss => String.append(ss, zz), T.render.pass(T.VPair{kk, T.VFlo{a1, a2}} <> t,
              "\n", True{}, False{}),
              String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VFlo{a1, a2}, SCon{'\n',
                T.render.pass(t, "\n", True{}, False{})})}}}),
              L1.pass_value(kk, T.VFlo{a1, a2}, Eq.and.left(T.wf.atom(T.VFlo{a1, a2}), T.wf.key(kk, t),
                M7.wt.ok(Bool.and(T.wf.atom(T.VFlo{a1, a2}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}), hw)), t,
                "\n", True{})),
            M12.kp.txt(kk, T.VFlo{a1, a2}, SCon{'\n', T.render.pass(t, "\n", True{}, False{})}, zz))),
        se.key(kk, SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VFlo{a1, a2}, String.append(SCon{'\n', T.render.pass(t,
          "\n", True{}, False{})}, zz))}}}))
    case T.VPair{+kk, T.VBool{+a1}} <> +t:
      se.cast(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VBool{a1}, String.append(SCon{'\n',
        T.render.pass(t, "\n", True{}, False{})}, zz))}}}),
        String.append(T.render.pass(T.VPair{kk, T.VBool{a1}} <> t, "\n", True{}, False{}), zz),
        Equal.sym(String, String.append(T.render.pass(T.VPair{kk, T.VBool{a1}} <> t, "\n", True{}, False{}), zz),
          String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ',
          D1.cv.tx(T.VBool{a1}, String.append(SCon{'\n', T.render.pass(t, "\n", True{}, False{})}, zz))}}}),
          Equal.trans(String, String.append(T.render.pass(T.VPair{kk, T.VBool{a1}} <> t, "\n", True{}, False{}), zz),
            String.append(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VBool{a1}, SCon{'\n',
              T.render.pass(t, "\n", True{}, False{})})}}}), zz),
            String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VBool{a1}, String.append(SCon{'\n',
              T.render.pass(t, "\n", True{}, False{})}, zz))}}}),
            Equal.cong(String, String, ss => String.append(ss, zz), T.render.pass(T.VPair{kk, T.VBool{a1}} <> t, "\n",
              True{}, False{}),
              String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VBool{a1}, SCon{'\n', T.render.pass(t,
                "\n", True{}, False{})})}}}),
              L1.pass_value(kk, T.VBool{a1}, Eq.and.left(T.wf.atom(T.VBool{a1}), T.wf.key(kk, t),
                M7.wt.ok(Bool.and(T.wf.atom(T.VBool{a1}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}), hw)), t,
                    "\n",
                True{})),
            M12.kp.txt(kk, T.VBool{a1}, SCon{'\n', T.render.pass(t, "\n", True{}, False{})}, zz))),
        se.key(kk, SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VBool{a1}, String.append(SCon{'\n', T.render.pass(t, "\n",
          True{}, False{})}, zz))}}}))
    case T.VPair{+kk, T.VWhen{+a1}} <> +t:
      se.cast(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VWhen{a1}, String.append(SCon{'\n',
        T.render.pass(t, "\n", True{}, False{})}, zz))}}}),
        String.append(T.render.pass(T.VPair{kk, T.VWhen{a1}} <> t, "\n", True{}, False{}), zz),
        Equal.sym(String, String.append(T.render.pass(T.VPair{kk, T.VWhen{a1}} <> t, "\n", True{}, False{}), zz),
          String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ',
          D1.cv.tx(T.VWhen{a1}, String.append(SCon{'\n', T.render.pass(t, "\n", True{}, False{})}, zz))}}}),
          Equal.trans(String, String.append(T.render.pass(T.VPair{kk, T.VWhen{a1}} <> t, "\n", True{}, False{}), zz),
            String.append(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VWhen{a1}, SCon{'\n',
              T.render.pass(t, "\n", True{}, False{})})}}}), zz),
            String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VWhen{a1}, String.append(SCon{'\n',
              T.render.pass(t, "\n", True{}, False{})}, zz))}}}),
            Equal.cong(String, String, ss => String.append(ss, zz), T.render.pass(T.VPair{kk, T.VWhen{a1}} <> t, "\n",
              True{}, False{}),
              String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VWhen{a1}, SCon{'\n', T.render.pass(t,
                "\n", True{}, False{})})}}}),
              L1.pass_value(kk, T.VWhen{a1}, Eq.and.left(T.wf.atom(T.VWhen{a1}), T.wf.key(kk, t),
                M7.wt.ok(Bool.and(T.wf.atom(T.VWhen{a1}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}), hw)), t,
                    "\n",
                True{})),
            M12.kp.txt(kk, T.VWhen{a1}, SCon{'\n', T.render.pass(t, "\n", True{}, False{})}, zz))),
        se.key(kk, SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VWhen{a1}, String.append(SCon{'\n', T.render.pass(t, "\n",
          True{}, False{})}, zz))}}}))
    case T.VPair{+kk, T.VArr{+a1}} <> +t:
      se.cast(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VArr{a1}, String.append(SCon{'\n',
        T.render.pass(t, "\n", True{}, False{})}, zz))}}}),
        String.append(T.render.pass(T.VPair{kk, T.VArr{a1}} <> t, "\n", True{}, False{}), zz),
        Equal.sym(String, String.append(T.render.pass(T.VPair{kk, T.VArr{a1}} <> t, "\n", True{}, False{}), zz),
          String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ',
          D1.cv.tx(T.VArr{a1}, String.append(SCon{'\n', T.render.pass(t, "\n", True{}, False{})}, zz))}}}),
          Equal.trans(String, String.append(T.render.pass(T.VPair{kk, T.VArr{a1}} <> t, "\n", True{}, False{}), zz),
            String.append(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VArr{a1}, SCon{'\n',
              T.render.pass(t, "\n", True{}, False{})})}}}), zz),
            String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VArr{a1}, String.append(SCon{'\n',
              T.render.pass(t, "\n", True{}, False{})}, zz))}}}),
            Equal.cong(String, String, ss => String.append(ss, zz), T.render.pass(T.VPair{kk, T.VArr{a1}} <> t, "\n",
              True{}, False{}),
              String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VArr{a1}, SCon{'\n', T.render.pass(t,
                "\n", True{}, False{})})}}}),
              L1.pass_value(kk, T.VArr{a1}, M7.wt.ok(T.wf.go(a1, T.WfItems{}), _v => T.wf.go(t, T.WfRows{hp}),
                M7.wt.more(T.wf.key(kk, t), _u => T.wf.then(T.wf.go(a1, T.WfItems{}),
          _v => T.wf.go(t, T.WfRows{hp})), hw)), t, "\n", True{})),
            M12.kp.txt(kk, T.VArr{a1}, SCon{'\n', T.render.pass(t, "\n", True{}, False{})}, zz))),
        se.key(kk, SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VArr{a1}, String.append(SCon{'\n', T.render.pass(t, "\n",
          True{}, False{})}, zz))}}}))
    case T.VPair{+kk, T.VInl{+a1}} <> +t:
      se.cast(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VInl{a1}, String.append(SCon{'\n',
        T.render.pass(t, "\n", True{}, False{})}, zz))}}}),
        String.append(T.render.pass(T.VPair{kk, T.VInl{a1}} <> t, "\n", True{}, False{}), zz),
        Equal.sym(String, String.append(T.render.pass(T.VPair{kk, T.VInl{a1}} <> t, "\n", True{}, False{}), zz),
          String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ',
          D1.cv.tx(T.VInl{a1}, String.append(SCon{'\n', T.render.pass(t, "\n", True{}, False{})}, zz))}}}),
          Equal.trans(String, String.append(T.render.pass(T.VPair{kk, T.VInl{a1}} <> t, "\n", True{}, False{}), zz),
            String.append(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VInl{a1}, SCon{'\n',
              T.render.pass(t, "\n", True{}, False{})})}}}), zz),
            String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VInl{a1}, String.append(SCon{'\n',
              T.render.pass(t, "\n", True{}, False{})}, zz))}}}),
            Equal.cong(String, String, ss => String.append(ss, zz), T.render.pass(T.VPair{kk, T.VInl{a1}} <> t, "\n",
              True{}, False{}),
              String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VInl{a1}, SCon{'\n', T.render.pass(t,
                "\n", True{}, False{})})}}}),
              L1.pass_value(kk, T.VInl{a1}, M7.wt.ok(T.wf.go(a1, T.WfInl{}), _v => T.wf.go(t, T.WfRows{hp}),
                M7.wt.more(T.wf.key(kk, t), _u => T.wf.then(T.wf.go(a1, T.WfInl{}),
          _v => T.wf.go(t, T.WfRows{hp})), hw)), t, "\n", True{})),
            M12.kp.txt(kk, T.VInl{a1}, SCon{'\n', T.render.pass(t, "\n", True{}, False{})}, zz))),
        se.key(kk, SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VInl{a1}, String.append(SCon{'\n', T.render.pass(t, "\n",
          True{}, False{})}, zz))}}}))
    case T.VPair{+kk, T.VAot{+a1, +a2}} <> +t:
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VPair{kk, T.VAot{a1, a2}} <> t, "\n", True{}, False{}),
          zz)),
        hw)
    case T.VPair{+kk, T.VPair{+a1, +a2}} <> +t:
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VPair{kk, T.VPair{a1, a2}} <> t, "\n", True{}, False{}),
          zz)),
        hw)
    case T.VStr{+a1} <> +t:
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VStr{a1} <> t, "\n", True{}, False{}), zz)), hw)
    case T.VSpan{+a1, +a2} <> +t:
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VSpan{a1, a2} <> t, "\n", True{}, False{}), zz)), hw)
    case T.VInt{+a1, +a2} <> +t:
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VInt{a1, a2} <> t, "\n", True{}, False{}), zz)), hw)
    case T.VFlo{+a1, +a2} <> +t:
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VFlo{a1, a2} <> t, "\n", True{}, False{}), zz)), hw)
    case T.VBool{+a1} <> +t:
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VBool{a1} <> t, "\n", True{}, False{}), zz)), hw)
    case T.VWhen{+a1} <> +t:
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VWhen{a1} <> t, "\n", True{}, False{}), zz)), hw)
    case T.VArr{+a1} <> +t:
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VArr{a1} <> t, "\n", True{}, False{}), zz)), hw)
    case T.VInl{+a1} <> +t:
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VInl{a1} <> t, "\n", True{}, False{}), zz)), hw)
    case T.VHead{+a1, +a2} <> +t:
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VHead{a1, a2} <> t, "\n", True{}, False{}), zz)), hw)
    case T.VAot{+a1, +a2} <> +t:
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VAot{a1, a2} <> t, "\n", True{}, False{}), zz)), hw)
    case T.VAots{+a1, +a2} <> +t:
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VAots{a1, a2} <> t, "\n", True{}, False{}), zz)), hw)

# the table pass's text, then any text read so
def se.T(
  xs: List<&2, T.Val>,
  +hp: String,
  +zz: String,
  +hw: {T.wf.go(xs, T.WfRows{hp}) == True{} : Bool},
  hz: M9.se(zz)
) -> M9.se(String.append(T.render.pass(xs, "\n", True{}, True{}), zz)):
  match xs:
    case []:
      hz
    case T.VPair{+kk, T.VHead{+p, +r}} <> +t:
      se.cast(SCon{'[', String.append(p, SCon{']', SCon{'\n', String.append(T.render.pass(r, "\n", True{}, False{}),
        String.append(T.render.pass(r, "\n", True{}, True{}), String.append(T.render.pass(t, "\n", True{}, True{}),
        zz)))}})},
        String.append(T.render.pass(T.VPair{kk, T.VHead{p, r}} <> t, "\n", True{}, True{}), zz),
        Equal.sym(String, String.append(T.render.pass(T.VPair{kk, T.VHead{p, r}} <> t, "\n", True{}, True{}), zz),
          SCon{'[', String.append(p, SCon{']', SCon{'\n',
          String.append(T.render.pass(r, "\n", True{}, False{}), String.append(T.render.pass(r, "\n", True{}, True{}),
            String.append(T.render.pass(t, "\n", True{}, True{}), zz)))}})}, M5.tt.head(kk, p, r, t, zz)),
        se.br(String.append(p, SCon{']', SCon{'\n', String.append(T.render.pass(r, "\n", True{}, False{}),
          String.append(T.render.pass(r, "\n", True{}, True{}), String.append(T.render.pass(t, "\n", True{}, True{}),
          zz)))}})))
    case T.VPair{+kk, T.VAots{+p, []}} <> +t:
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VPair{kk, T.VAots{p, []}} <> t, "\n", True{}, True{}), zz)),
        hw)
    case T.VPair{+kk, T.VAots{+p, T.VAot{+q, +r} <> +et}} <> +t:
      +hin = {M7.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VAot{q, r} <> et)), Bool.and(T.wf.key(kk, t),
        T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VAot{q, r} <> et, T.WfElems{p}), _v => T.wf.go(t,
        T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VAot{q, r} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}))
        == True{} : Bool}}
      +bd = {String.append(T.render.pass(r, "\n", True{}, False{}), String.append(T.render.pass(r, "\n", True{},
        True{}), String.append(T.render.pass(et, "\n", True{}, True{}), String.append(T.render.pass(t, "\n", True{},
        True{}), zz)))) : String}
      se.cast(SCon{'[', SCon{'[', String.append(q, SCon{']', SCon{']', SCon{'\n', bd}}})}},
        String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VAot{q, r} <> et}} <> t, "\n", True{}, True{}), zz),
        Equal.sym(String, String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VAot{q, r} <> et}} <> t, "\n", True{},
          True{}), zz), SCon{'[', SCon{'[',
          String.append(q, SCon{']', SCon{']', SCon{'\n', bd}}})}},
          Equal.trans(String, String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VAot{q, r} <> et}} <> t, "\n",
            True{}, True{}), zz),
            String.append(T.render.pass(T.VAot{q, r} <> et, "\n", True{}, True{}), String.append(T.render.pass(t, "\n",
              True{}, True{}), zz)),
            SCon{'[', SCon{'[', String.append(q, SCon{']', SCon{']', SCon{'\n', bd}}})}},
            M10.tt.aots(kk, p, T.VAot{q, r} <> et, t, zz, M10.tt.pe(T.VAot{q, r} <> et, p, M7.wt.ok(T.wf.go(T.VAot{q,
                r} <> et,
              T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}), hin))),
            M5.tt.aot(q, r, et, String.append(T.render.pass(t, "\n", True{}, True{}), zz)))),
        se.br(SCon{'[', String.append(q, SCon{']', SCon{']', SCon{'\n', bd}}})}))
    case T.VPair{+kk, T.VAots{+p, T.VStr{+a1} <> +et}} <> +t:
      +hin = {M7.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VStr{a1} <> et)), Bool.and(T.wf.key(kk, t),
        T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VStr{a1} <> et, T.WfElems{p}), _v => T.wf.go(t,
        T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VStr{a1} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}))
        == True{} : Bool}}
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VStr{a1} <> et}} <> t, "\n", True{},
        True{}), zz)), M7.wt.ok(T.wf.go(T.VStr{a1} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VSpan{+a1, +a2} <> +et}} <> +t:
      +hin = {M7.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VSpan{a1, a2} <> et)), Bool.and(T.wf.key(kk, t),
        T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VSpan{a1, a2} <> et, T.WfElems{p}),
          _v => T.wf.go(t,
        T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VSpan{a1, a2} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}))
        == True{} : Bool}}
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VSpan{a1, a2} <> et}} <> t, "\n",
        True{}, True{}), zz)), M7.wt.ok(T.wf.go(T.VSpan{a1, a2} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}),
            hin))
    case T.VPair{+kk, T.VAots{+p, T.VInt{+a1, +a2} <> +et}} <> +t:
      +hin = {M7.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VInt{a1, a2} <> et)), Bool.and(T.wf.key(kk, t),
        T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VInt{a1, a2} <> et, T.WfElems{p}), _v => T.wf.go(t,
        T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VInt{a1, a2} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}))
        == True{} : Bool}}
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VInt{a1, a2} <> et}} <> t, "\n",
          True{},
        True{}), zz)), M7.wt.ok(T.wf.go(T.VInt{a1, a2} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VFlo{+a1, +a2} <> +et}} <> +t:
      +hin = {M7.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VFlo{a1, a2} <> et)), Bool.and(T.wf.key(kk, t),
        T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VFlo{a1, a2} <> et, T.WfElems{p}), _v => T.wf.go(t,
        T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VFlo{a1, a2} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}))
        == True{} : Bool}}
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VFlo{a1, a2} <> et}} <> t, "\n",
          True{},
        True{}), zz)), M7.wt.ok(T.wf.go(T.VFlo{a1, a2} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VBool{+a1} <> +et}} <> +t:
      +hin = {M7.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VBool{a1} <> et)), Bool.and(T.wf.key(kk, t),
        T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VBool{a1} <> et, T.WfElems{p}), _v => T.wf.go(t,
        T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VBool{a1} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}))
        == True{} : Bool}}
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VBool{a1} <> et}} <> t, "\n", True{},
        True{}), zz)), M7.wt.ok(T.wf.go(T.VBool{a1} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VWhen{+a1} <> +et}} <> +t:
      +hin = {M7.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VWhen{a1} <> et)), Bool.and(T.wf.key(kk, t),
        T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VWhen{a1} <> et, T.WfElems{p}), _v => T.wf.go(t,
        T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VWhen{a1} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}))
        == True{} : Bool}}
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VWhen{a1} <> et}} <> t, "\n", True{},
        True{}), zz)), M7.wt.ok(T.wf.go(T.VWhen{a1} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VArr{+a1} <> +et}} <> +t:
      +hin = {M7.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VArr{a1} <> et)), Bool.and(T.wf.key(kk, t),
        T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VArr{a1} <> et, T.WfElems{p}), _v => T.wf.go(t,
        T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VArr{a1} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}))
        == True{} : Bool}}
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VArr{a1} <> et}} <> t, "\n", True{},
        True{}), zz)), M7.wt.ok(T.wf.go(T.VArr{a1} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VInl{+a1} <> +et}} <> +t:
      +hin = {M7.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VInl{a1} <> et)), Bool.and(T.wf.key(kk, t),
        T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VInl{a1} <> et, T.WfElems{p}), _v => T.wf.go(t,
        T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VInl{a1} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}))
        == True{} : Bool}}
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VInl{a1} <> et}} <> t, "\n", True{},
        True{}), zz)), M7.wt.ok(T.wf.go(T.VInl{a1} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VHead{+a1, +a2} <> +et}} <> +t:
      +hin = {M7.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VHead{a1, a2} <> et)), Bool.and(T.wf.key(kk, t),
        T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VHead{a1, a2} <> et, T.WfElems{p}),
          _v => T.wf.go(t,
        T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VHead{a1, a2} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}))
        == True{} : Bool}}
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VHead{a1, a2} <> et}} <> t, "\n",
        True{}, True{}), zz)), M7.wt.ok(T.wf.go(T.VHead{a1, a2} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}),
            hin))
    case T.VPair{+kk, T.VAots{+p, T.VAots{+a1, +a2} <> +et}} <> +t:
      +hin = {M7.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VAots{a1, a2} <> et)), Bool.and(T.wf.key(kk, t),
        T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VAots{a1, a2} <> et, T.WfElems{p}),
          _v => T.wf.go(t,
        T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VAots{a1, a2} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}))
        == True{} : Bool}}
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VAots{a1, a2} <> et}} <> t, "\n",
        True{}, True{}), zz)), M7.wt.ok(T.wf.go(T.VAots{a1, a2} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}),
            hin))
    case T.VPair{+kk, T.VAots{+p, T.VPair{+a1, T.VStr{+b1}} <> +et}} <> +t:
      +hin = {M7.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VPair{a1, T.VStr{b1}} <> et)),
          Bool.and(T.wf.key(kk,
        t),
        T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VPair{a1, T.VStr{b1}} <> et, T.WfElems{p}),
          _v => T.wf.go(t,
        T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VPair{a1, T.VStr{b1}} <> et, T.WfElems{p}), _v => T.wf.go(t,
          T.WfRows{hp}))
        == True{} : Bool}}
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VStr{b1}} <> et}} <> t,
        "\n", True{}, True{}), zz)), M7.wt.ok(T.wf.go(T.VPair{a1, T.VStr{b1}} <> et, T.WfElems{p}), _v => T.wf.go(t,
        T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VPair{+a1, T.VSpan{+b1, +b2}} <> +et}} <> +t:
      +hin = {M7.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VPair{a1, T.VSpan{b1, b2}} <> et)),
        Bool.and(T.wf.key(kk, t),
        T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VPair{a1, T.VSpan{b1, b2}} <> et, T.WfElems{p}),
          _v => T.wf.go(t,
        T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VPair{a1, T.VSpan{b1, b2}} <> et, T.WfElems{p}), _v => T.wf.go(t,
          T.WfRows{hp}))
        == True{} : Bool}}
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VSpan{b1,
          b2}} <> et}} <> t,
        "\n", True{}, True{}), zz)), M7.wt.ok(T.wf.go(T.VPair{a1, T.VSpan{b1, b2}} <> et, T.WfElems{p}),
            _v => T.wf.go(t,
        T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VPair{+a1, T.VInt{+b1, +b2}} <> +et}} <> +t:
      +hin = {M7.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VPair{a1, T.VInt{b1, b2}} <> et)),
        Bool.and(T.wf.key(kk, t),
        T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VPair{a1, T.VInt{b1, b2}} <> et, T.WfElems{p}),
          _v => T.wf.go(t,
        T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VPair{a1, T.VInt{b1, b2}} <> et, T.WfElems{p}), _v => T.wf.go(t,
          T.WfRows{hp}))
        == True{} : Bool}}
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VInt{b1,
          b2}} <> et}} <> t,
        "\n", True{}, True{}), zz)), M7.wt.ok(T.wf.go(T.VPair{a1, T.VInt{b1, b2}} <> et, T.WfElems{p}), _v => T.wf.go(t,
        T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VPair{+a1, T.VFlo{+b1, +b2}} <> +et}} <> +t:
      +hin = {M7.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VPair{a1, T.VFlo{b1, b2}} <> et)),
        Bool.and(T.wf.key(kk, t),
        T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VPair{a1, T.VFlo{b1, b2}} <> et, T.WfElems{p}),
          _v => T.wf.go(t,
        T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VPair{a1, T.VFlo{b1, b2}} <> et, T.WfElems{p}), _v => T.wf.go(t,
          T.WfRows{hp}))
        == True{} : Bool}}
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VFlo{b1,
          b2}} <> et}} <> t,
        "\n", True{}, True{}), zz)), M7.wt.ok(T.wf.go(T.VPair{a1, T.VFlo{b1, b2}} <> et, T.WfElems{p}), _v => T.wf.go(t,
        T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VPair{+a1, T.VBool{+b1}} <> +et}} <> +t:
      +hin = {M7.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VPair{a1, T.VBool{b1}} <> et)),
          Bool.and(T.wf.key(kk,
        t),
        T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VPair{a1, T.VBool{b1}} <> et, T.WfElems{p}),
          _v => T.wf.go(t,
        T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VPair{a1, T.VBool{b1}} <> et, T.WfElems{p}), _v => T.wf.go(t,
          T.WfRows{hp}))
        == True{} : Bool}}
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VBool{b1}} <> et}} <> t,
        "\n", True{}, True{}), zz)), M7.wt.ok(T.wf.go(T.VPair{a1, T.VBool{b1}} <> et, T.WfElems{p}), _v => T.wf.go(t,
        T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VPair{+a1, T.VWhen{+b1}} <> +et}} <> +t:
      +hin = {M7.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VPair{a1, T.VWhen{b1}} <> et)),
          Bool.and(T.wf.key(kk,
        t),
        T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VPair{a1, T.VWhen{b1}} <> et, T.WfElems{p}),
          _v => T.wf.go(t,
        T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VPair{a1, T.VWhen{b1}} <> et, T.WfElems{p}), _v => T.wf.go(t,
          T.WfRows{hp}))
        == True{} : Bool}}
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VWhen{b1}} <> et}} <> t,
        "\n", True{}, True{}), zz)), M7.wt.ok(T.wf.go(T.VPair{a1, T.VWhen{b1}} <> et, T.WfElems{p}), _v => T.wf.go(t,
        T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VPair{+a1, T.VArr{+b1}} <> +et}} <> +t:
      +hin = {M7.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VPair{a1, T.VArr{b1}} <> et)),
          Bool.and(T.wf.key(kk,
        t),
        T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VPair{a1, T.VArr{b1}} <> et, T.WfElems{p}),
          _v => T.wf.go(t,
        T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VPair{a1, T.VArr{b1}} <> et, T.WfElems{p}), _v => T.wf.go(t,
          T.WfRows{hp}))
        == True{} : Bool}}
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VArr{b1}} <> et}} <> t,
        "\n", True{}, True{}), zz)), M7.wt.ok(T.wf.go(T.VPair{a1, T.VArr{b1}} <> et, T.WfElems{p}), _v => T.wf.go(t,
        T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VPair{+a1, T.VInl{+b1}} <> +et}} <> +t:
      +hin = {M7.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VPair{a1, T.VInl{b1}} <> et)),
          Bool.and(T.wf.key(kk,
        t),
        T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VPair{a1, T.VInl{b1}} <> et, T.WfElems{p}),
          _v => T.wf.go(t,
        T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VPair{a1, T.VInl{b1}} <> et, T.WfElems{p}), _v => T.wf.go(t,
          T.WfRows{hp}))
        == True{} : Bool}}
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VInl{b1}} <> et}} <> t,
        "\n", True{}, True{}), zz)), M7.wt.ok(T.wf.go(T.VPair{a1, T.VInl{b1}} <> et, T.WfElems{p}), _v => T.wf.go(t,
        T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VPair{+a1, T.VHead{+b1, +b2}} <> +et}} <> +t:
      +hin = {M7.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VPair{a1, T.VHead{b1, b2}} <> et)),
        Bool.and(T.wf.key(kk, t),
        T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VPair{a1, T.VHead{b1, b2}} <> et, T.WfElems{p}),
          _v => T.wf.go(t,
        T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VPair{a1, T.VHead{b1, b2}} <> et, T.WfElems{p}), _v => T.wf.go(t,
          T.WfRows{hp}))
        == True{} : Bool}}
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VHead{b1,
          b2}} <> et}} <> t,
        "\n", True{}, True{}), zz)), M7.wt.ok(T.wf.go(T.VPair{a1, T.VHead{b1, b2}} <> et, T.WfElems{p}),
            _v => T.wf.go(t,
        T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VPair{+a1, T.VAot{+b1, +b2}} <> +et}} <> +t:
      +hin = {M7.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VPair{a1, T.VAot{b1, b2}} <> et)),
        Bool.and(T.wf.key(kk, t),
        T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VPair{a1, T.VAot{b1, b2}} <> et, T.WfElems{p}),
          _v => T.wf.go(t,
        T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VPair{a1, T.VAot{b1, b2}} <> et, T.WfElems{p}), _v => T.wf.go(t,
          T.WfRows{hp}))
        == True{} : Bool}}
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VAot{b1,
          b2}} <> et}} <> t,
        "\n", True{}, True{}), zz)), M7.wt.ok(T.wf.go(T.VPair{a1, T.VAot{b1, b2}} <> et, T.WfElems{p}), _v => T.wf.go(t,
        T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VPair{+a1, T.VAots{+b1, +b2}} <> +et}} <> +t:
      +hin = {M7.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VPair{a1, T.VAots{b1, b2}} <> et)),
        Bool.and(T.wf.key(kk, t),
        T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VPair{a1, T.VAots{b1, b2}} <> et, T.WfElems{p}),
          _v => T.wf.go(t,
        T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VPair{a1, T.VAots{b1, b2}} <> et, T.WfElems{p}), _v => T.wf.go(t,
          T.WfRows{hp}))
        == True{} : Bool}}
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VAots{b1,
          b2}} <> et}} <> t,
        "\n", True{}, True{}), zz)), M7.wt.ok(T.wf.go(T.VPair{a1, T.VAots{b1, b2}} <> et, T.WfElems{p}),
            _v => T.wf.go(t,
        T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VPair{+a1, T.VPair{+b1, +b2}} <> +et}} <> +t:
      +hin = {M7.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VPair{a1, T.VPair{b1, b2}} <> et)),
        Bool.and(T.wf.key(kk, t),
        T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VPair{a1, T.VPair{b1, b2}} <> et, T.WfElems{p}),
          _v => T.wf.go(t,
        T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VPair{a1, T.VPair{b1, b2}} <> et, T.WfElems{p}), _v => T.wf.go(t,
          T.WfRows{hp}))
        == True{} : Bool}}
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VPair{b1,
          b2}} <> et}} <> t,
        "\n", True{}, True{}), zz)), M7.wt.ok(T.wf.go(T.VPair{a1, T.VPair{b1, b2}} <> et, T.WfElems{p}),
            _v => T.wf.go(t,
        T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VStr{+a1}} <> +t:
      se.T(t, hp, zz, M7.wt.more(Bool.and(T.wf.atom(T.VStr{a1}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}), hw),
          hz)
    case T.VPair{+kk, T.VSpan{+a1, +a2}} <> +t:
      se.T(t, hp, zz, M7.wt.more(Bool.and(T.wf.atom(T.VSpan{a1, a2}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}),
        hw), hz)
    case T.VPair{+kk, T.VInt{+a1, +a2}} <> +t:
      se.T(t, hp, zz, M7.wt.more(Bool.and(T.wf.atom(T.VInt{a1, a2}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}),
          hw),
        hz)
    case T.VPair{+kk, T.VFlo{+a1, +a2}} <> +t:
      se.T(t, hp, zz, M7.wt.more(Bool.and(T.wf.atom(T.VFlo{a1, a2}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}),
          hw),
        hz)
    case T.VPair{+kk, T.VBool{+a1}} <> +t:
      se.T(t, hp, zz, M7.wt.more(Bool.and(T.wf.atom(T.VBool{a1}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}), hw),
        hz)
    case T.VPair{+kk, T.VWhen{+a1}} <> +t:
      se.T(t, hp, zz, M7.wt.more(Bool.and(T.wf.atom(T.VWhen{a1}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}), hw),
        hz)
    case T.VPair{+kk, T.VArr{+a1}} <> +t:
      se.T(t, hp, zz, M7.wt.more(T.wf.go(a1, T.WfItems{}), _v => T.wf.go(t, T.WfRows{hp}), M7.wt.more(T.wf.key(kk, t),
        _u => T.wf.then(T.wf.go(a1, T.WfItems{}), _v => T.wf.go(t, T.WfRows{hp})), hw)), hz)
    case T.VPair{+kk, T.VInl{+a1}} <> +t:
      se.T(t, hp, zz, M7.wt.more(T.wf.go(a1, T.WfInl{}), _v => T.wf.go(t, T.WfRows{hp}), M7.wt.more(T.wf.key(kk, t),
        _u => T.wf.then(T.wf.go(a1, T.WfInl{}), _v => T.wf.go(t, T.WfRows{hp})), hw)), hz)
    case T.VPair{+kk, T.VAot{+a1, +a2}} <> +t:
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VPair{kk, T.VAot{a1, a2}} <> t, "\n", True{}, True{}), zz)),
        hw)
    case T.VPair{+kk, T.VPair{+a1, +a2}} <> +t:
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VPair{kk, T.VPair{a1, a2}} <> t, "\n", True{}, True{}),
          zz)),
        hw)
    case T.VStr{+a1} <> +t:
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VStr{a1} <> t, "\n", True{}, True{}), zz)), hw)
    case T.VSpan{+a1, +a2} <> +t:
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VSpan{a1, a2} <> t, "\n", True{}, True{}), zz)), hw)
    case T.VInt{+a1, +a2} <> +t:
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VInt{a1, a2} <> t, "\n", True{}, True{}), zz)), hw)
    case T.VFlo{+a1, +a2} <> +t:
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VFlo{a1, a2} <> t, "\n", True{}, True{}), zz)), hw)
    case T.VBool{+a1} <> +t:
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VBool{a1} <> t, "\n", True{}, True{}), zz)), hw)
    case T.VWhen{+a1} <> +t:
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VWhen{a1} <> t, "\n", True{}, True{}), zz)), hw)
    case T.VArr{+a1} <> +t:
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VArr{a1} <> t, "\n", True{}, True{}), zz)), hw)
    case T.VInl{+a1} <> +t:
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VInl{a1} <> t, "\n", True{}, True{}), zz)), hw)
    case T.VHead{+a1, +a2} <> +t:
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VHead{a1, a2} <> t, "\n", True{}, True{}), zz)), hw)
    case T.VAot{+a1, +a2} <> +t:
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VAot{a1, a2} <> t, "\n", True{}, True{}), zz)), hw)
    case T.VAots{+a1, +a2} <> +t:
      Eq.bit.absurd(&1, M9.se(String.append(T.render.pass(T.VAots{a1, a2} <> t, "\n", True{}, True{}), zz)), hw)

# the document parse reads back from what render wrote, read out, is canon:
# the key pass and the table pass over the root, from the start of the text
def ex.canon(
  +ee: String,
  +xs: List<&2, T.Val>,
  +hw: {T.wf.go(xs, T.WfRows{""}) == True{} : Bool},
  +hl: {D4.short.rows(xs) == True{} : Bool}
) -> {D1.own(T.parse(T.render(T.Doc{ee, xs}))) == D2.canon(T.Doc{ee, xs}) : T.Doc}:
  +tx = {String.append(T.render.pass(xs, "\n", True{}, False{}), T.render.pass(xs, "\n", True{}, True{})) : String}
  +tz = {String.append(T.render.pass(xs, "\n", True{}, False{}), String.append(T.render.pass(xs, "\n", True{}, True{}),
    "")) : String}
  +nw = {M12.nd.wf(xs, "", hw) : {M2.nd(List.append(&2, T.Val, D2.canon.keys(xs), D2.canon.tabs(xs))) == True{} : Bool}}
  +etx = {Equal.cong(String, String, s2 => String.append(T.render.pass(xs, "\n", True{}, False{}), s2),
    T.render.pass(xs, "\n", True{}, True{}), String.append(T.render.pass(xs, "\n", True{}, True{}), ""),
    Equal.sym(String, String.append(T.render.pass(xs, "\n", True{}, True{}), ""), T.render.pass(xs, "\n", True{},
      True{}), Eq.append_nil(T.render.pass(xs, "\n", True{}, True{})))) : {tx == tz : String}}
  Equal.trans(T.Doc, D1.own(T.doc.read(tx, T.MScan{T.st.start()})), D1.own(T.doc.read(tx, T.MScan{M1.dl([], [], [],
    T.LTop{}, T.QBasic{}, 0, 0, False{})})),
    D2.canon(T.Doc{ee, xs}),
    Equal.cong(T.Doc, T.Doc, dd => D1.own(dd), T.doc.read(tx, T.MScan{T.st.start()}), T.doc.read(tx, T.MScan{M1.dl([],
      [], [], T.LTop{}, T.QBasic{}, 0, 0, False{})}),
      se.cast(tz, tx, Equal.sym(String, tx, tz, etx), se.P(xs, "", String.append(T.render.pass(xs, "\n", True{},
        True{}), ""), hw, se.T(xs, "", "", hw, {==})))),
    M12.pp.step(dd => {D1.own(dd) == D2.canon(T.Doc{ee, xs}) : T.Doc}, T.doc.read(tx, T.MScan{M1.dl([], [], [],
        T.LTop{},
      T.QBasic{}, 0, 0, False{})}),
      T.doc.read(tz, T.MScan{M1.dl([], [], [], T.LTop{}, T.QBasic{}, 0, 0, False{})}),
      Equal.cong(String, T.Doc, s2 => T.doc.read(s2, T.MScan{M1.dl([], [], [], T.LTop{}, T.QBasic{}, 0, 0, False{})}),
          tx,
        tz, etx),
      M12.kp(xs, "", [], [], [], False{}, [], [], D2.canon.tabs(xs), T.LTop{}, T.QBasic{}, 0, 0,
        String.append(T.render.pass(xs, "\n", True{}, True{}), ""),
        dd => {D1.own(dd) == D2.canon(T.Doc{ee, xs}) : T.Doc}, {==}, {==}, hw, hl,
        M6.cv.fr.nil(List.append(&2, T.Val, D2.canon.keys(xs), D2.canon.tabs(xs))), nw, {==},
        +c2 => +b2 => +q2 => +u2 => +l2 => f2 => o2 => M5.tp(xs, False{}, "", [], [], c2, D2.canon.keys(xs), "", [], [],
          [], b2,
          q2, u2, l2, False{}, "", dd => {D1.own(dd) == D2.canon(T.Doc{ee, xs}) : T.Doc}, {==})({==}, hw, hl, f2,
          M12.nd.suf(D2.canon.keys(xs), D2.canon.tabs(xs), nw), o2,
          +c3 => _hs3 => _he3 => _b3 => _q3 => _u3 => _l3 => _a3 => o3 => Equal.cong(List<&2, T.Val>, T.Doc,
            zs => T.Doc{"", zs}, D1.own.rows(T.rows.seal(c3)), D1.own.rows(D2.canon.rows(xs)), o3)))))

# every string and table path in a well-formed document whose rendered text
# is short is short
def sd.doc(
  +ee: String,
  +xs: List<&2, T.Val>,
  +hw: {T.wf.go(xs, T.WfRows{""}) == True{} : Bool},
  +hh: {D1.short(T.render(T.Doc{ee, xs})) == True{} : Bool}
) -> {D4.short.rows(xs) == True{} : Bool}:
  M9.sd(xs, False{}, "")(hw, M7.cn.pf(T.render.pass(xs, "\n", True{}, False{}), T.render.pass(xs, "\n", True{},
      True{}), 0,
    hh), M7.cd.dp(T.render.pass(xs, "\n", True{}, False{}), T.render.pass(xs, "\n", True{}, True{}), 0, hh))

# a well-formed document is the same as canon of it
def cs.same(
  +ee: String,
  +xs: List<&2, T.Val>,
  +hw: {T.wf.go(xs, T.WfRows{""}) == True{} : Bool}
) -> {D2.same(D2.canon(T.Doc{ee, xs}), T.Doc{ee, xs}) == True{} : Bool}:
  +cr = {D2.canon.rows(xs) : List<&2, T.Val>}
  M3.and.tt(D2.same.go(D1.own.rows(cr), xs), D2.same.go(xs, D1.own.rows(cr)),
    Equal.trans(Bool, D2.same.go(D1.own.rows(cr), xs), D2.same.go(cr, xs), True{}, M4.own.l(cr, xs),
      Equal.trans(Bool, D2.same.go(cr, xs), D2.same.go(D2.canon.tabs(xs), M2.rtabs(xs)), True{},
        M2.pk(xs, "", D2.canon.tabs(xs), [], hw, M11.wf.selfs(xs, T.WfRows{""}, hw), M6.cv.fr.nil(D2.canon.keys(xs))),
        M6.st(xs, False{}, "", hw))),
    Equal.trans(Bool, D2.same.go(xs, D1.own.rows(cr)), D2.same.go(xs, cr), True{}, M4.own.r(xs, cr),
      M8.s2(xs, False{}, "", hw, M11.wf.selfs(xs, T.WfRows{""}, hw))))

# laws/RenderThenParse.bend. The document induction reads render's text back as canon of the
# document, once each string's and table path's bound is read off the bound
# on the whole text; canon is the same as the document; and own changes
# neither the error nor what same compares.

def L2.render_parse_canon(d, w, h_s):
  match d:
    case T.Doc{+ee, +xs}:
      ex.canon(ee, xs, w, sd.doc(ee, xs, w, h_s))

# own keeps the error
def own.bad(dd: T.Doc) -> {T.bad(D1.own(dd)) == T.bad(dd) : String}:
  match dd:
    case T.Doc{_b, _r}:
      {==}

# same compares a document as own reads it
def own.same(dd: T.Doc, +d0: T.Doc) -> {D2.same(dd, d0) == D2.same(D1.own(dd), d0) : Bool}:
  match dd d0:
    case T.Doc{_b1, +r1} T.Doc{_b2, +r2}:
      Equal.sym(Bool, Bool.and(D2.same.go(D1.own.rows(r1), r2), D2.same.go(r2, D1.own.rows(r1))),
        Bool.and(D2.same.go(r1, r2), D2.same.go(r2, r1)),
        Equal.trans(Bool, Bool.and(D2.same.go(D1.own.rows(r1), r2), D2.same.go(r2, D1.own.rows(r1))),
          Bool.and(D2.same.go(r1, r2), D2.same.go(r2, D1.own.rows(r1))),
          Bool.and(D2.same.go(r1, r2), D2.same.go(r2, r1)),
          Equal.cong(Bool, Bool, xx => Bool.and(xx, D2.same.go(r2, D1.own.rows(r1))),
            D2.same.go(D1.own.rows(r1),
            r2), D2.same.go(r1, r2), M4.own.l(r1, r2)),
          Equal.cong(Bool, Bool, yy => Bool.and(D2.same.go(r1, r2), yy), D2.same.go(r2, D1.own.rows(r1)),
            D2.same.go(r2, r1), M4.own.r(r2, r1))))

def L2.render_parse(d, w, h_s):
  match d:
    case T.Doc{+ee, +xs}:
      +d0 = {T.Doc{ee, xs} : T.Doc}
      +pd = {T.parse(T.render(d0)) : T.Doc}
      +ex = {ex.canon(ee, xs, w, sd.doc(ee, xs, w, h_s)) : {D1.own(pd) == D2.canon(d0) : T.Doc}}
      M3.and.tt(String.is_empty(T.bad(pd)), D2.same(pd, d0),
        Equal.trans(Bool, String.is_empty(T.bad(pd)), String.is_empty(T.bad(D1.own(pd))), True{},
          Equal.cong(String, Bool, ss => String.is_empty(ss), T.bad(pd), T.bad(D1.own(pd)),
            Equal.sym(String, T.bad(D1.own(pd)), T.bad(pd), own.bad(pd))),
          Equal.cong(T.Doc, Bool, dd => String.is_empty(T.bad(dd)), D1.own(pd), D2.canon(d0), ex)),
        Equal.trans(Bool, D2.same(pd, d0), D2.same(D1.own(pd), d0), True{}, own.same(pd, d0),
          Equal.trans(Bool, D2.same(D1.own(pd), d0), D2.same(D2.canon(d0), d0), True{},
            Equal.cong(T.Doc, Bool, dd => D2.same(dd, d0), D1.own(pd), D2.canon(d0), ex), cs.same(ee, xs, w))))
