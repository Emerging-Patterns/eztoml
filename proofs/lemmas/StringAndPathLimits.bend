# every string and table path in a well-formed document is short, from the
# document start
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/PassValue.bend as L1
import ../../laws/defs/BareValueGrammar.bend as D1
import ../../laws/defs/PartialDerivationRules.bend as D2
import ./DecimalArithmetic.bend as M1
import ./FailedWalkNameCompare.bend as M2
import ./ShortTextBounds.bend as M3
import ./ValuePassText.bend as M4

# The start of the document. The scanner starts with the byte-order-mark
# check pending (st.start); for a first character that is no byte-order mark
# that is the start of a line in the root. render's text starts with a key,
# a bracket, or nothing.

# a text read from the start of the document as from the start of a line
def se(tx: String) -> Type:
  {T.doc.read(tx, T.MScan{T.st.start()}) == T.doc.read(tx, T.MScan{M1.dl([], [], [], T.LTop{}, T.QBasic{}, 0, 0,
    False{})}) : T.Doc}

# the text after a value's text
def tx.w(
  vv: T.Val,
  +ww: String,
  +hh: {D1.counts(D1.cv.tx(vv, ww), 0) == True{} : Bool}
) -> {D1.counts(ww, 0) == True{} : Bool}:
  match vv:
    case T.VArr{+its}:
      M3.cd.dp("]", ww, 0, M3.cd.dp(T.render.go(its, ", ", False{}), SCon{']', ww}, 0, M3.cd.dp("[",
        String.append(T.render.go(its, ", ", False{}), SCon{']', ww}), 0, hh)))
    case T.VInl{+rs}:
      M3.cd.dp("}", ww, 0, M3.cd.dp(T.render.go(rs, ", ", False{}), SCon{'}', ww}, 0, M3.cd.dp("{",
          String.append(T.render.go(rs,
        ", ", False{}), SCon{'}', ww}), 0, hh)))
    case T.VStr{+a1}:
      M3.cd.dp(T.render.atom(T.VStr{a1}), ww, 0, hh)
    case T.VSpan{+a1, +a2}:
      M3.cd.dp(T.render.atom(T.VSpan{a1, a2}), ww, 0, hh)
    case T.VInt{+a1, +a2}:
      M3.cd.dp(T.render.atom(T.VInt{a1, a2}), ww, 0, hh)
    case T.VFlo{+a1, +a2}:
      M3.cd.dp(T.render.atom(T.VFlo{a1, a2}), ww, 0, hh)
    case T.VBool{+a1}:
      M3.cd.dp(T.render.atom(T.VBool{a1}), ww, 0, hh)
    case T.VWhen{+a1}:
      M3.cd.dp(T.render.atom(T.VWhen{a1}), ww, 0, hh)
    case T.VHead{+a1, +a2}:
      M3.cd.dp(T.render.atom(T.VHead{a1, a2}), ww, 0, hh)
    case T.VAot{+a1, +a2}:
      M3.cd.dp(T.render.atom(T.VAot{a1, a2}), ww, 0, hh)
    case T.VAots{+a1, +a2}:
      M3.cd.dp(T.render.atom(T.VAots{a1, a2}), ww, 0, hh)
    case T.VPair{+a1, +a2}:
      M3.cd.dp(T.render.atom(T.VPair{a1, a2}), ww, 0, hh)

# every string in a well-formed value whose text starts a short text is short
def sv1(
  vv: T.Val,
  +ww: String,
  +hw: {D1.cv.wf(vv) == True{} : Bool},
  +hh: {D1.counts(D1.cv.tx(vv, ww), 0) == True{} : Bool}
) -> {D1.cv.short1(vv) == True{} : Bool}:
  match vv:
    case T.VArr{+its}:
      M3.sg(its, False{}, hw, M3.cn.pf(T.render.go(its, ", ", False{}), SCon{']', ww}, 0, M3.cd.dp("[",
        String.append(T.render.go(its, ", ", False{}), SCon{']', ww}), 0, hh)))
    case T.VInl{+rs}:
      M3.sg(rs, True{}, hw, M3.cn.pf(T.render.go(rs, ", ", False{}), SCon{'}', ww}, 0, M3.cd.dp("{",
        String.append(T.render.go(rs, ", ", False{}), SCon{'}', ww}), 0, hh)))
    case T.VStr{+a1}:
      M3.sb(a1, ww, hh)
    case T.VSpan{+a1, +a2}:
      M3.ssp(a1, a2, ww, hh)
    case T.VInt{_a1, _a2}:
      {==}
    case T.VFlo{_a1, _a2}:
      {==}
    case T.VBool{_a1}:
      {==}
    case T.VWhen{_a1}:
      {==}
    case T.VHead{_a1, _a2}:
      {==}
    case T.VAot{_a1, _a2}:
      {==}
    case T.VAots{_a1, _a2}:
      {==}
    case T.VPair{_a1, _a2}:
      {==}

# what sd claims of a list: a table's rows (md false) whose key pass and
# table pass texts are short, or an array's elements (md true) whose text is
def sd.G(md: Bool, +xs: List<&2, T.Val>, +hp: String) -> Type:
  match md:
    case False{}:
      {T.wf.go(xs, T.WfRows{hp}) == True{} : Bool} -> {D1.counts(T.render.pass(xs, "\n", True{}, False{}),
        0) == True{} : Bool} -> {D1.counts(T.render.pass(xs, "\n", True{}, True{}), 0) == True{} : Bool} ->
        {D2.short.rows(xs) == True{} : Bool}
    case True{}:
      {T.wf.go(xs, T.WfElems{hp}) == True{} : Bool} -> {D1.counts(T.render.pass(xs, "\n", True{}, True{}),
        0) == True{} : Bool} -> {D2.short.rows(xs) == True{} : Bool}

# every string and every table path in a well-formed document whose text is
# short is short
def sd(xs: List<&2, T.Val>, md: Bool, +hp: String) -> sd.G(md, xs, hp):
  match xs md:
    case [] False{}:
      _hw => _h1 => _h2 => {==}
    case [] True{}:
      _hw => _h2 => {==}
    case T.VPair{+kk, T.VStr{+a1}} <> +t False{}:
      +hw => +h1 => +h2 =>
        +hw1 = {Eq.and.left(T.wf.atom(T.VStr{a1}), T.wf.key(kk, t), M3.wt.ok(Bool.and(T.wf.atom(T.VStr{a1}),
            T.wf.key(kk,
          t)), _u => T.wf.go(t, T.WfRows{hp}), hw)) : {D1.cv.wf(T.VStr{a1}) == True{} : Bool}}
        +k1 = {Equal.trans(Bool, D1.counts(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ',
          D1.cv.tx(T.VStr{a1}, SCon{'\n', T.render.pass(t, "\n", True{}, False{})})}}}), 0),
          D1.counts(T.render.pass(T.VPair{kk, T.VStr{a1}} <> t, "\n", True{}, False{}), 0), True{}, Equal.cong(String,
          Bool, x2 => D1.counts(x2, 0),
          String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VStr{a1}, SCon{'\n', T.render.pass(t,
            "\n", True{}, False{})})}}}), T.render.pass(T.VPair{kk, T.VStr{a1}} <> t, "\n", True{}, False{}),
            Equal.sym(String, T.render.pass(T.VPair{kk, T.VStr{a1}} <> t, "\n", True{}, False{}),
            String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VStr{a1}, SCon{'\n', T.render.pass(t,
            "\n", True{}, False{})})}}}),
          L1.pass_value(kk, T.VStr{a1}, hw1, t, "\n", True{}))), h1) : {D1.counts(String.append(T.key(kk), SCon{' ',
            SCon{'=', SCon{' ', D1.cv.tx(T.VStr{a1}, SCon{'\n', T.render.pass(t, "\n", True{}, False{})})}}}),
            0) == True{} : Bool}}
        +k2 = {M3.cd.dp(" = ", D1.cv.tx(T.VStr{a1}, SCon{'\n', T.render.pass(t, "\n", True{}, False{})}), 0,
          M3.cd.dp(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VStr{a1}, SCon{'\n', T.render.pass(t, "\n",
          True{}, False{})})}}}, 0, k1)) : {D1.counts(D1.cv.tx(T.VStr{a1}, SCon{'\n', T.render.pass(t, "\n", True{},
          False{})}), 0) == True{} : Bool}}
        M3.cv.and2(D1.cv.short1(T.VStr{a1}), D2.short.rows(t), sv1(T.VStr{a1}, SCon{'\n', T.render.pass(t, "\n",
          True{}, False{})}, hw1, k2),
          sd(t, False{}, hp)(M3.wt.more(Bool.and(T.wf.atom(T.VStr{a1}), T.wf.key(kk, t)), _u => T.wf.go(t,
              T.WfRows{hp}),
            hw), M3.cd.dp("\n", T.render.pass(t, "\n", True{}, False{}), 0, tx.w(T.VStr{a1}, SCon{'\n', T.render.pass(t,
            "\n", True{}, False{})}, k2)), h2))
    case T.VPair{+kk, T.VSpan{+a1, +a2}} <> +t False{}:
      +hw => +h1 => +h2 =>
        +hw1 = {Eq.and.left(T.wf.atom(T.VSpan{a1, a2}), T.wf.key(kk, t), M3.wt.ok(Bool.and(T.wf.atom(T.VSpan{a1, a2}),
          T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}), hw)) : {D1.cv.wf(T.VSpan{a1, a2}) == True{} : Bool}}
        +k1 = {Equal.trans(Bool, D1.counts(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ',
          D1.cv.tx(T.VSpan{a1, a2}, SCon{'\n', T.render.pass(t, "\n", True{}, False{})})}}}), 0),
          D1.counts(T.render.pass(T.VPair{kk, T.VSpan{a1, a2}} <> t, "\n", True{}, False{}), 0), True{},
          Equal.cong(String, Bool, x2 => D1.counts(x2, 0),
          String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VSpan{a1, a2}, SCon{'\n', T.render.pass(t,
            "\n", True{}, False{})})}}}), T.render.pass(T.VPair{kk, T.VSpan{a1, a2}} <> t, "\n", True{}, False{}),
            Equal.sym(String, T.render.pass(T.VPair{kk, T.VSpan{a1, a2}} <> t, "\n", True{}, False{}),
            String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VSpan{a1, a2}, SCon{'\n',
            T.render.pass(t, "\n", True{}, False{})})}}}),
          L1.pass_value(kk, T.VSpan{a1, a2}, hw1, t, "\n", True{}))), h1) : {D1.counts(String.append(T.key(kk),
            SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VSpan{a1, a2}, SCon{'\n', T.render.pass(t, "\n", True{},
            False{})})}}}), 0) == True{} : Bool}}
        +k2 = {M3.cd.dp(" = ", D1.cv.tx(T.VSpan{a1, a2}, SCon{'\n', T.render.pass(t, "\n", True{}, False{})}), 0,
          M3.cd.dp(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VSpan{a1, a2}, SCon{'\n', T.render.pass(t, "\n",
          True{}, False{})})}}}, 0, k1)) : {D1.counts(D1.cv.tx(T.VSpan{a1, a2}, SCon{'\n', T.render.pass(t, "\n",
          True{}, False{})}), 0) == True{} : Bool}}
        M3.cv.and2(D1.cv.short1(T.VSpan{a1, a2}), D2.short.rows(t), sv1(T.VSpan{a1, a2}, SCon{'\n', T.render.pass(t,
          "\n", True{}, False{})}, hw1, k2),
          sd(t, False{}, hp)(M3.wt.more(Bool.and(T.wf.atom(T.VSpan{a1, a2}), T.wf.key(kk, t)), _u => T.wf.go(t,
            T.WfRows{hp}), hw), M3.cd.dp("\n", T.render.pass(t, "\n", True{}, False{}), 0, tx.w(T.VSpan{a1, a2},
                SCon{'\n',
            T.render.pass(t, "\n", True{}, False{})}, k2)), h2))
    case T.VPair{+kk, T.VInt{+a1, +a2}} <> +t False{}:
      +hw => +h1 => +h2 =>
        +hw1 = {Eq.and.left(T.wf.atom(T.VInt{a1, a2}), T.wf.key(kk, t), M3.wt.ok(Bool.and(T.wf.atom(T.VInt{a1, a2}),
          T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}), hw)) : {D1.cv.wf(T.VInt{a1, a2}) == True{} : Bool}}
        +k1 = {Equal.trans(Bool, D1.counts(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ',
          D1.cv.tx(T.VInt{a1, a2}, SCon{'\n', T.render.pass(t, "\n", True{}, False{})})}}}), 0),
          D1.counts(T.render.pass(T.VPair{kk, T.VInt{a1, a2}} <> t, "\n", True{}, False{}), 0), True{},
          Equal.cong(String, Bool, x2 => D1.counts(x2, 0),
          String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VInt{a1, a2}, SCon{'\n', T.render.pass(t,
            "\n", True{}, False{})})}}}), T.render.pass(T.VPair{kk, T.VInt{a1, a2}} <> t, "\n", True{}, False{}),
            Equal.sym(String, T.render.pass(T.VPair{kk, T.VInt{a1, a2}} <> t, "\n", True{}, False{}),
            String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VInt{a1, a2}, SCon{'\n',
            T.render.pass(t, "\n", True{}, False{})})}}}),
          L1.pass_value(kk, T.VInt{a1, a2}, hw1, t, "\n", True{}))), h1) : {D1.counts(String.append(T.key(kk),
            SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VInt{a1, a2}, SCon{'\n', T.render.pass(t, "\n", True{},
            False{})})}}}), 0) == True{} : Bool}}
        +k2 = {M3.cd.dp(" = ", D1.cv.tx(T.VInt{a1, a2}, SCon{'\n', T.render.pass(t, "\n", True{}, False{})}), 0,
          M3.cd.dp(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VInt{a1, a2}, SCon{'\n', T.render.pass(t, "\n",
          True{}, False{})})}}}, 0, k1)) : {D1.counts(D1.cv.tx(T.VInt{a1, a2}, SCon{'\n', T.render.pass(t, "\n",
          True{}, False{})}), 0) == True{} : Bool}}
        M3.cv.and2(D1.cv.short1(T.VInt{a1, a2}), D2.short.rows(t), sv1(T.VInt{a1, a2}, SCon{'\n', T.render.pass(t,
          "\n", True{}, False{})}, hw1, k2),
          sd(t, False{}, hp)(M3.wt.more(Bool.and(T.wf.atom(T.VInt{a1, a2}), T.wf.key(kk, t)), _u => T.wf.go(t,
            T.WfRows{hp}), hw), M3.cd.dp("\n", T.render.pass(t, "\n", True{}, False{}), 0, tx.w(T.VInt{a1, a2},
                SCon{'\n',
            T.render.pass(t, "\n", True{}, False{})}, k2)), h2))
    case T.VPair{+kk, T.VFlo{+a1, +a2}} <> +t False{}:
      +hw => +h1 => +h2 =>
        +hw1 = {Eq.and.left(T.wf.atom(T.VFlo{a1, a2}), T.wf.key(kk, t), M3.wt.ok(Bool.and(T.wf.atom(T.VFlo{a1, a2}),
          T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}), hw)) : {D1.cv.wf(T.VFlo{a1, a2}) == True{} : Bool}}
        +k1 = {Equal.trans(Bool, D1.counts(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ',
          D1.cv.tx(T.VFlo{a1, a2}, SCon{'\n', T.render.pass(t, "\n", True{}, False{})})}}}), 0),
          D1.counts(T.render.pass(T.VPair{kk, T.VFlo{a1, a2}} <> t, "\n", True{}, False{}), 0), True{},
          Equal.cong(String, Bool, x2 => D1.counts(x2, 0),
          String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VFlo{a1, a2}, SCon{'\n', T.render.pass(t,
            "\n", True{}, False{})})}}}), T.render.pass(T.VPair{kk, T.VFlo{a1, a2}} <> t, "\n", True{}, False{}),
            Equal.sym(String, T.render.pass(T.VPair{kk, T.VFlo{a1, a2}} <> t, "\n", True{}, False{}),
            String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VFlo{a1, a2}, SCon{'\n',
            T.render.pass(t, "\n", True{}, False{})})}}}),
          L1.pass_value(kk, T.VFlo{a1, a2}, hw1, t, "\n", True{}))), h1) : {D1.counts(String.append(T.key(kk),
            SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VFlo{a1, a2}, SCon{'\n', T.render.pass(t, "\n", True{},
            False{})})}}}), 0) == True{} : Bool}}
        +k2 = {M3.cd.dp(" = ", D1.cv.tx(T.VFlo{a1, a2}, SCon{'\n', T.render.pass(t, "\n", True{}, False{})}), 0,
          M3.cd.dp(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VFlo{a1, a2}, SCon{'\n', T.render.pass(t, "\n",
          True{}, False{})})}}}, 0, k1)) : {D1.counts(D1.cv.tx(T.VFlo{a1, a2}, SCon{'\n', T.render.pass(t, "\n",
          True{}, False{})}), 0) == True{} : Bool}}
        M3.cv.and2(D1.cv.short1(T.VFlo{a1, a2}), D2.short.rows(t), sv1(T.VFlo{a1, a2}, SCon{'\n', T.render.pass(t,
          "\n", True{}, False{})}, hw1, k2),
          sd(t, False{}, hp)(M3.wt.more(Bool.and(T.wf.atom(T.VFlo{a1, a2}), T.wf.key(kk, t)), _u => T.wf.go(t,
            T.WfRows{hp}), hw), M3.cd.dp("\n", T.render.pass(t, "\n", True{}, False{}), 0, tx.w(T.VFlo{a1, a2},
                SCon{'\n',
            T.render.pass(t, "\n", True{}, False{})}, k2)), h2))
    case T.VPair{+kk, T.VBool{+a1}} <> +t False{}:
      +hw => +h1 => +h2 =>
        +hw1 = {Eq.and.left(T.wf.atom(T.VBool{a1}), T.wf.key(kk, t), M3.wt.ok(Bool.and(T.wf.atom(T.VBool{a1}),
            T.wf.key(kk,
          t)), _u => T.wf.go(t, T.WfRows{hp}), hw)) : {D1.cv.wf(T.VBool{a1}) == True{} : Bool}}
        +k1 = {Equal.trans(Bool, D1.counts(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ',
          D1.cv.tx(T.VBool{a1}, SCon{'\n', T.render.pass(t, "\n", True{}, False{})})}}}), 0),
          D1.counts(T.render.pass(T.VPair{kk, T.VBool{a1}} <> t, "\n", True{}, False{}), 0), True{},
          Equal.cong(String, Bool, x2 => D1.counts(x2, 0),
          String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VBool{a1}, SCon{'\n', T.render.pass(t,
            "\n", True{}, False{})})}}}), T.render.pass(T.VPair{kk, T.VBool{a1}} <> t, "\n", True{}, False{}),
            Equal.sym(String, T.render.pass(T.VPair{kk, T.VBool{a1}} <> t, "\n", True{}, False{}),
            String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VBool{a1}, SCon{'\n', T.render.pass(t,
            "\n", True{}, False{})})}}}),
          L1.pass_value(kk, T.VBool{a1}, hw1, t, "\n", True{}))), h1) : {D1.counts(String.append(T.key(kk),
            SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VBool{a1}, SCon{'\n', T.render.pass(t, "\n", True{},
            False{})})}}}), 0) == True{} : Bool}}
        +k2 = {M3.cd.dp(" = ", D1.cv.tx(T.VBool{a1}, SCon{'\n', T.render.pass(t, "\n", True{}, False{})}), 0,
          M3.cd.dp(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VBool{a1}, SCon{'\n', T.render.pass(t, "\n",
          True{}, False{})})}}}, 0, k1)) : {D1.counts(D1.cv.tx(T.VBool{a1}, SCon{'\n', T.render.pass(t, "\n",
          True{}, False{})}), 0) == True{} : Bool}}
        M3.cv.and2(D1.cv.short1(T.VBool{a1}), D2.short.rows(t), sv1(T.VBool{a1}, SCon{'\n', T.render.pass(t, "\n",
          True{}, False{})}, hw1, k2),
          sd(t, False{}, hp)(M3.wt.more(Bool.and(T.wf.atom(T.VBool{a1}), T.wf.key(kk, t)), _u => T.wf.go(t,
              T.WfRows{hp}),
            hw), M3.cd.dp("\n", T.render.pass(t, "\n", True{}, False{}), 0, tx.w(T.VBool{a1}, SCon{'\n',
                T.render.pass(t,
            "\n", True{}, False{})}, k2)), h2))
    case T.VPair{+kk, T.VWhen{+a1}} <> +t False{}:
      +hw => +h1 => +h2 =>
        +hw1 = {Eq.and.left(T.wf.atom(T.VWhen{a1}), T.wf.key(kk, t), M3.wt.ok(Bool.and(T.wf.atom(T.VWhen{a1}),
            T.wf.key(kk,
          t)), _u => T.wf.go(t, T.WfRows{hp}), hw)) : {D1.cv.wf(T.VWhen{a1}) == True{} : Bool}}
        +k1 = {Equal.trans(Bool, D1.counts(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ',
          D1.cv.tx(T.VWhen{a1}, SCon{'\n', T.render.pass(t, "\n", True{}, False{})})}}}), 0),
          D1.counts(T.render.pass(T.VPair{kk, T.VWhen{a1}} <> t, "\n", True{}, False{}), 0), True{},
          Equal.cong(String, Bool, x2 => D1.counts(x2, 0),
          String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VWhen{a1}, SCon{'\n', T.render.pass(t,
            "\n", True{}, False{})})}}}), T.render.pass(T.VPair{kk, T.VWhen{a1}} <> t, "\n", True{}, False{}),
            Equal.sym(String, T.render.pass(T.VPair{kk, T.VWhen{a1}} <> t, "\n", True{}, False{}),
            String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VWhen{a1}, SCon{'\n', T.render.pass(t,
            "\n", True{}, False{})})}}}),
          L1.pass_value(kk, T.VWhen{a1}, hw1, t, "\n", True{}))), h1) : {D1.counts(String.append(T.key(kk),
            SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VWhen{a1}, SCon{'\n', T.render.pass(t, "\n", True{},
            False{})})}}}), 0) == True{} : Bool}}
        +k2 = {M3.cd.dp(" = ", D1.cv.tx(T.VWhen{a1}, SCon{'\n', T.render.pass(t, "\n", True{}, False{})}), 0,
          M3.cd.dp(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VWhen{a1}, SCon{'\n', T.render.pass(t, "\n",
          True{}, False{})})}}}, 0, k1)) : {D1.counts(D1.cv.tx(T.VWhen{a1}, SCon{'\n', T.render.pass(t, "\n",
          True{}, False{})}), 0) == True{} : Bool}}
        M3.cv.and2(D1.cv.short1(T.VWhen{a1}), D2.short.rows(t), sv1(T.VWhen{a1}, SCon{'\n', T.render.pass(t, "\n",
          True{}, False{})}, hw1, k2),
          sd(t, False{}, hp)(M3.wt.more(Bool.and(T.wf.atom(T.VWhen{a1}), T.wf.key(kk, t)), _u => T.wf.go(t,
              T.WfRows{hp}),
            hw), M3.cd.dp("\n", T.render.pass(t, "\n", True{}, False{}), 0, tx.w(T.VWhen{a1}, SCon{'\n',
                T.render.pass(t,
            "\n", True{}, False{})}, k2)), h2))
    case T.VPair{+kk, T.VArr{+a1}} <> +t False{}:
      +hw => +h1 => +h2 =>
        +hw1 = {M3.wt.ok(T.wf.go(a1, T.WfItems{}), _v => T.wf.go(t, T.WfRows{hp}), M3.wt.more(T.wf.key(kk, t),
          _u => T.wf.then(T.wf.go(a1, T.WfItems{}), _v => T.wf.go(t, T.WfRows{hp})),
          hw)) : {D1.cv.wf(T.VArr{a1}) == True{} : Bool}}
        +k1 = {Equal.trans(Bool, D1.counts(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ',
          D1.cv.tx(T.VArr{a1}, SCon{'\n', T.render.pass(t, "\n", True{}, False{})})}}}), 0),
          D1.counts(T.render.pass(T.VPair{kk, T.VArr{a1}} <> t, "\n", True{}, False{}), 0), True{}, Equal.cong(String,
          Bool, x2 => D1.counts(x2, 0),
          String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VArr{a1}, SCon{'\n', T.render.pass(t,
            "\n", True{}, False{})})}}}), T.render.pass(T.VPair{kk, T.VArr{a1}} <> t, "\n", True{}, False{}),
            Equal.sym(String, T.render.pass(T.VPair{kk, T.VArr{a1}} <> t, "\n", True{}, False{}),
            String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VArr{a1}, SCon{'\n', T.render.pass(t,
            "\n", True{}, False{})})}}}),
          L1.pass_value(kk, T.VArr{a1}, hw1, t, "\n", True{}))), h1) : {D1.counts(String.append(T.key(kk), SCon{' ',
            SCon{'=', SCon{' ', D1.cv.tx(T.VArr{a1}, SCon{'\n', T.render.pass(t, "\n", True{}, False{})})}}}),
            0) == True{} : Bool}}
        +k2 = {M3.cd.dp(" = ", D1.cv.tx(T.VArr{a1}, SCon{'\n', T.render.pass(t, "\n", True{}, False{})}), 0,
          M3.cd.dp(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VArr{a1}, SCon{'\n', T.render.pass(t, "\n",
          True{}, False{})})}}}, 0, k1)) : {D1.counts(D1.cv.tx(T.VArr{a1}, SCon{'\n', T.render.pass(t, "\n", True{},
          False{})}), 0) == True{} : Bool}}
        M3.cv.and2(D1.cv.short1(T.VArr{a1}), D2.short.rows(t), sv1(T.VArr{a1}, SCon{'\n', T.render.pass(t, "\n",
          True{}, False{})}, hw1, k2),
          sd(t, False{}, hp)(M3.wt.more(T.wf.go(a1, T.WfItems{}), _v => T.wf.go(t, T.WfRows{hp}),
              M3.wt.more(T.wf.key(kk, t),
            _u => T.wf.then(T.wf.go(a1, T.WfItems{}), _v => T.wf.go(t, T.WfRows{hp})), hw)), M3.cd.dp("\n",
            T.render.pass(t, "\n", True{}, False{}), 0, tx.w(T.VArr{a1}, SCon{'\n', T.render.pass(t, "\n", True{},
            False{})}, k2)), h2))
    case T.VPair{+kk, T.VInl{+a1}} <> +t False{}:
      +hw => +h1 => +h2 =>
        +hw1 = {M3.wt.ok(T.wf.go(a1, T.WfInl{}), _v => T.wf.go(t, T.WfRows{hp}), M3.wt.more(T.wf.key(kk, t),
          _u => T.wf.then(T.wf.go(a1, T.WfInl{}), _v => T.wf.go(t, T.WfRows{hp})),
          hw)) : {D1.cv.wf(T.VInl{a1}) == True{} : Bool}}
        +k1 = {Equal.trans(Bool, D1.counts(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ',
          D1.cv.tx(T.VInl{a1}, SCon{'\n', T.render.pass(t, "\n", True{}, False{})})}}}), 0),
          D1.counts(T.render.pass(T.VPair{kk, T.VInl{a1}} <> t, "\n", True{}, False{}), 0), True{}, Equal.cong(String,
          Bool, x2 => D1.counts(x2, 0),
          String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VInl{a1}, SCon{'\n', T.render.pass(t,
            "\n", True{}, False{})})}}}), T.render.pass(T.VPair{kk, T.VInl{a1}} <> t, "\n", True{}, False{}),
            Equal.sym(String, T.render.pass(T.VPair{kk, T.VInl{a1}} <> t, "\n", True{}, False{}),
            String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VInl{a1}, SCon{'\n', T.render.pass(t,
            "\n", True{}, False{})})}}}),
          L1.pass_value(kk, T.VInl{a1}, hw1, t, "\n", True{}))), h1) : {D1.counts(String.append(T.key(kk), SCon{' ',
            SCon{'=', SCon{' ', D1.cv.tx(T.VInl{a1}, SCon{'\n', T.render.pass(t, "\n", True{}, False{})})}}}),
            0) == True{} : Bool}}
        +k2 = {M3.cd.dp(" = ", D1.cv.tx(T.VInl{a1}, SCon{'\n', T.render.pass(t, "\n", True{}, False{})}), 0,
          M3.cd.dp(T.key(kk), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VInl{a1}, SCon{'\n', T.render.pass(t, "\n",
          True{}, False{})})}}}, 0, k1)) : {D1.counts(D1.cv.tx(T.VInl{a1}, SCon{'\n', T.render.pass(t, "\n", True{},
          False{})}), 0) == True{} : Bool}}
        M3.cv.and2(D1.cv.short1(T.VInl{a1}), D2.short.rows(t), sv1(T.VInl{a1}, SCon{'\n', T.render.pass(t, "\n",
          True{}, False{})}, hw1, k2),
          sd(t, False{}, hp)(M3.wt.more(T.wf.go(a1, T.WfInl{}), _v => T.wf.go(t, T.WfRows{hp}), M3.wt.more(T.wf.key(kk,
              t),
            _u => T.wf.then(T.wf.go(a1, T.WfInl{}), _v => T.wf.go(t, T.WfRows{hp})), hw)), M3.cd.dp("\n",
                T.render.pass(t,
            "\n", True{}, False{}), 0, tx.w(T.VInl{a1}, SCon{'\n', T.render.pass(t, "\n", True{}, False{})}, k2)), h2))
    case T.VPair{+kk, T.VHead{+p, +r}} <> +t False{}:
      +hw => +h1 => +h2 =>
        +hin = {M3.wt.more(Bool.and(T.wf.key(kk, t), T.str.eq(p, T.tree.pre(hp, kk))), _u => T.wf.then(T.wf.go(r,
          T.WfRows{p}), _v => T.wf.go(t, T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(r, T.WfRows{p}), _v => T.wf.go(t,
          T.WfRows{hp})) == True{} : Bool}}
        +zz = {String.append(String.append(T.render.pass(r, "\n", True{}, False{}), T.render.pass(r, "\n", True{},
          True{})), T.render.pass(t, "\n", True{}, True{})) : String}
        +j1 = {M3.cd.dp("[", String.append(p, SCon{']', SCon{'\n', zz}}), 0, h2) : {D1.counts(String.append(p, SCon{']',
          SCon{'\n', zz}}), 0) == True{} : Bool}}
        +j2 = {M3.cd.dp("]\n", zz, 0, M3.cd.dp(p, SCon{']', SCon{'\n', zz}}, 0, j1)) : {D1.counts(zz,
            0) == True{} : Bool}}
        +j3 = {M3.cn.pf(String.append(T.render.pass(r, "\n", True{}, False{}), T.render.pass(r, "\n", True{}, True{})),
          T.render.pass(t, "\n", True{}, True{}), 0, j2) : {D1.counts(String.append(T.render.pass(r, "\n", True{},
          False{}), T.render.pass(r, "\n", True{}, True{})), 0) == True{} : Bool}}
        M3.cv.and2(D1.short(p), Bool.and(D2.short.rows(r), D2.short.rows(t)), M3.cn.pf(p, SCon{']', SCon{'\n', zz}}, 0,
          j1),
          M3.cv.and2(D2.short.rows(r), D2.short.rows(t),
            sd(r, False{}, p)(M3.wt.ok(T.wf.go(r, T.WfRows{p}), _v => T.wf.go(t, T.WfRows{hp}), hin),
              M3.cn.pf(T.render.pass(r, "\n", True{}, False{}), T.render.pass(r, "\n", True{}, True{}), 0, j3),
              M3.cd.dp(T.render.pass(r, "\n", True{}, False{}), T.render.pass(r, "\n", True{}, True{}), 0, j3)),
            sd(t, False{}, hp)(M3.wt.more(T.wf.go(r, T.WfRows{p}), _v => T.wf.go(t, T.WfRows{hp}), hin), h1,
              M3.cd.dp(String.append(T.render.pass(r, "\n", True{}, False{}), T.render.pass(r, "\n", True{}, True{})),
                T.render.pass(t, "\n", True{}, True{}), 0, j2))))
    case T.VPair{+kk, T.VAots{+p, T.VAot{+q, +r} <> +et}} <> +t False{}:
      +hw => +h1 => +h2 =>
        +hin ={M3.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VAot{q, r} <> et)), Bool.and(T.wf.key(kk, t),
          T.str.eq(p,
          T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VAot{q, r} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp})), hw)
          : {T.wf.then(T.wf.go(T.VAot{q, r} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp})) == True{} : Bool}}
        +hwe = {M3.wt.ok(T.wf.go(T.VAot{q, r} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}),
          hin) : {T.wf.go(T.VAot{q, r} <> et, T.WfElems{p})
          == True{} : Bool}}
        +eq = {M2.str.eq.true(q, p, M3.wt.ok(T.str.eq(q, p), _u => T.wf.then(T.wf.go(r, T.WfRows{q}), _v => T.wf.go(et,
          T.WfElems{p})), hwe)) : {q == p : String}}
        +j0 = {Equal.trans(Bool, D1.counts(String.append(T.render.pass(T.VAot{q, r} <> et, "\n", True{}, True{}),
          T.render.pass(t, "\n", True{}, True{})), 0), D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VAot{q,
          r} <> et}} <> t, "\n", True{}, True{}), 0), True{},
          Equal.cong(String, Bool, x2 => D1.counts(x2, 0), String.append(T.render.pass(T.VAot{q, r} <> et, "\n",
            True{}, True{}), T.render.pass(t, "\n", True{}, True{})), T.render.pass(T.VPair{kk, T.VAots{p, T.VAot{q,
            r} <> et}} <> t, "\n", True{}, True{}),
          Equal.sym(String, T.render.pass(T.VPair{kk, T.VAots{p, T.VAot{q, r} <> et}} <> t, "\n", True{}, True{}),
            String.append(T.render.pass(T.VAot{q, r} <> et, "\n", True{}, True{}), T.render.pass(t, "\n", True{},
            True{})),
          Equal.trans(String, T.render.pass(T.VPair{kk, T.VAots{p, T.VAot{q, r} <> et}} <> t, "\n", True{}, True{}),
            String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VAot{q, r} <> et}} <> t, "\n", True{}, True{}), ""),
            String.append(T.render.pass(T.VAot{q, r} <> et, "\n", True{}, True{}), T.render.pass(t, "\n", True{},
              True{})), Equal.sym(String, String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VAot{q, r} <> et}} <> t,
              "\n", True{}, True{}), ""),
            T.render.pass(T.VPair{kk, T.VAots{p, T.VAot{q, r} <> et}} <> t, "\n", True{}, True{}),
              Eq.append_nil(T.render.pass(T.VPair{kk, T.VAots{p, T.VAot{q, r} <> et}} <> t, "\n", True{}, True{}))),
            Equal.trans(String, String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VAot{q, r} <> et}} <> t, "\n",
              True{}, True{}), ""), String.append(T.render.pass(T.VAot{q, r} <> et, "\n", True{}, True{}),
              String.append(T.render.pass(t, "\n", True{}, True{}), "")),
              String.append(T.render.pass(T.VAot{q, r} <> et, "\n", True{}, True{}), T.render.pass(t, "\n", True{},
                True{})), M4.tt.aots(kk, p, T.VAot{q, r} <> et, t, "", M4.tt.pe(T.VAot{q, r} <> et, p, hwe)),
              Equal.cong(String, String, x3 => String.append(T.render.pass(T.VAot{q, r} <> et, "\n", True{}, True{}),
                x3), String.append(T.render.pass(t, "\n", True{}, True{}), ""), T.render.pass(t, "\n", True{}, True{}),
                Eq.append_nil(T.render.pass(t, "\n", True{}, True{}))))))),
                  h2) : {D1.counts(String.append(T.render.pass(T.VAot{q, r} <> et, "\n", True{}, True{}),
                  T.render.pass(t, "\n", True{}, True{})), 0) == True{} : Bool}}
        +j1 = {M3.cn.pf(T.render.pass(T.VAot{q, r} <> et, "\n", True{}, True{}), T.render.pass(t, "\n", True{},
            True{}), 0,
          j0) : {D1.counts(T.render.pass(T.VAot{q, r} <> et, "\n", True{}, True{}), 0) == True{} : Bool}}
        +sq = {M3.cn.pf(q, SCon{']', SCon{']', SCon{'\n', String.append(String.append(T.render.pass(r, "\n", True{},
          False{}), T.render.pass(r, "\n", True{}, True{})), T.render.pass(et, "\n", True{}, True{}))}}}, 0,
              M3.cd.dp("[[",
          String.append(q, SCon{']', SCon{']', SCon{'\n', String.append(String.append(T.render.pass(r, "\n", True{},
          False{}), T.render.pass(r, "\n", True{}, True{})), T.render.pass(et, "\n", True{}, True{}))}}}), 0,
          j1)) : {D1.short(q) == True{} : Bool}}
        M3.cv.and2(D1.short(p), Bool.and(D2.short.rows(T.VAot{q, r} <> et), D2.short.rows(t)),
          Equal.trans(Bool, D1.short(p), D1.short(q), True{}, Equal.cong(String, Bool, s2 => D1.short(s2), p, q,
            Equal.sym(String, q, p, eq)), sq),
          M3.cv.and2(D2.short.rows(T.VAot{q, r} <> et), D2.short.rows(t), sd(T.VAot{q, r} <> et, True{}, p)(hwe, j1),
            sd(t, False{}, hp)(M3.wt.more(T.wf.go(T.VAot{q, r} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}),
                hin),
              h1,
              M3.cd.dp(T.render.pass(T.VAot{q, r} <> et, "\n", True{}, True{}), T.render.pass(t, "\n", True{}, True{}),
                  0,
                j0))))
    case T.VPair{+kk, T.VAots{+p, []}} <> +t False{}:
      hw => Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, []}} <> t, "\n", True{}, False{}),
        0) == True{} : Bool} -> {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, []}} <> t, "\n", True{}, True{}),
        0) == True{} : Bool} ->
        {D2.short.rows(T.VPair{kk, T.VAots{p, []}} <> t) == True{} : Bool}, hw)
    case T.VPair{+kk, T.VAots{+p, T.VStr{+a1} <> +et}} <> +t False{}:
      hw =>
        +hin = {M3.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VStr{a1} <> et)), Bool.and(T.wf.key(kk, t),
          T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VStr{a1} <> et, T.WfElems{p}), _v => T.wf.go(t,
          T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VStr{a1} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}))
          == True{} : Bool}}
        Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VStr{a1} <> et}} <> t, "\n", True{},
          False{}), 0) == True{} : Bool} -> {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VStr{a1} <> et}} <> t,
          "\n", True{}, True{}), 0) == True{} : Bool} -> {D2.short.rows(T.VPair{kk, T.VAots{p,
          T.VStr{a1} <> et}} <> t) == True{} : Bool}, M3.wt.ok(T.wf.go(T.VStr{a1} <> et, T.WfElems{p}), _v => T.wf.go(t,
          T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VSpan{+a1, +a2} <> +et}} <> +t False{}:
      hw =>
        +hin = {M3.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VSpan{a1, a2} <> et)), Bool.and(T.wf.key(kk, t),
          T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VSpan{a1, a2} <> et, T.WfElems{p}),
            _v => T.wf.go(t,
          T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VSpan{a1, a2} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}))
          == True{} : Bool}}
        Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VSpan{a1, a2} <> et}} <> t, "\n", True{},
          False{}), 0) == True{} : Bool} -> {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VSpan{a1,
          a2} <> et}} <> t, "\n", True{}, True{}), 0) == True{} : Bool} -> {D2.short.rows(T.VPair{kk, T.VAots{p,
          T.VSpan{a1, a2} <> et}} <> t) == True{} : Bool}, M3.wt.ok(T.wf.go(T.VSpan{a1, a2} <> et, T.WfElems{p}),
          _v => T.wf.go(t,
          T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VInt{+a1, +a2} <> +et}} <> +t False{}:
      hw =>
        +hin = {M3.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VInt{a1, a2} <> et)), Bool.and(T.wf.key(kk, t),
          T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VInt{a1, a2} <> et, T.WfElems{p}),
            _v => T.wf.go(t,
          T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VInt{a1, a2} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}))
          == True{} : Bool}}
        Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VInt{a1, a2} <> et}} <> t, "\n", True{},
          False{}), 0) == True{} : Bool} -> {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VInt{a1,
          a2} <> et}} <> t, "\n", True{}, True{}), 0) == True{} : Bool} -> {D2.short.rows(T.VPair{kk, T.VAots{p,
          T.VInt{a1, a2} <> et}} <> t) == True{} : Bool}, M3.wt.ok(T.wf.go(T.VInt{a1, a2} <> et, T.WfElems{p}),
          _v => T.wf.go(t,
          T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VFlo{+a1, +a2} <> +et}} <> +t False{}:
      hw =>
        +hin = {M3.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VFlo{a1, a2} <> et)), Bool.and(T.wf.key(kk, t),
          T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VFlo{a1, a2} <> et, T.WfElems{p}),
            _v => T.wf.go(t,
          T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VFlo{a1, a2} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}))
          == True{} : Bool}}
        Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VFlo{a1, a2} <> et}} <> t, "\n", True{},
          False{}), 0) == True{} : Bool} -> {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VFlo{a1,
          a2} <> et}} <> t, "\n", True{}, True{}), 0) == True{} : Bool} -> {D2.short.rows(T.VPair{kk, T.VAots{p,
          T.VFlo{a1, a2} <> et}} <> t) == True{} : Bool}, M3.wt.ok(T.wf.go(T.VFlo{a1, a2} <> et, T.WfElems{p}),
          _v => T.wf.go(t,
          T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VBool{+a1} <> +et}} <> +t False{}:
      hw =>
        +hin = {M3.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VBool{a1} <> et)), Bool.and(T.wf.key(kk, t),
          T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VBool{a1} <> et, T.WfElems{p}), _v => T.wf.go(t,
          T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VBool{a1} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}))
          == True{} : Bool}}
        Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VBool{a1} <> et}} <> t, "\n", True{},
          False{}), 0) == True{} : Bool} -> {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VBool{a1} <> et}} <> t,
          "\n", True{}, True{}), 0) == True{} : Bool} -> {D2.short.rows(T.VPair{kk, T.VAots{p,
          T.VBool{a1} <> et}} <> t) == True{} : Bool}, M3.wt.ok(T.wf.go(T.VBool{a1} <> et, T.WfElems{p}),
              _v => T.wf.go(t,
          T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VWhen{+a1} <> +et}} <> +t False{}:
      hw =>
        +hin = {M3.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VWhen{a1} <> et)), Bool.and(T.wf.key(kk, t),
          T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VWhen{a1} <> et, T.WfElems{p}), _v => T.wf.go(t,
          T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VWhen{a1} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}))
          == True{} : Bool}}
        Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VWhen{a1} <> et}} <> t, "\n", True{},
          False{}), 0) == True{} : Bool} -> {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VWhen{a1} <> et}} <> t,
          "\n", True{}, True{}), 0) == True{} : Bool} -> {D2.short.rows(T.VPair{kk, T.VAots{p,
          T.VWhen{a1} <> et}} <> t) == True{} : Bool}, M3.wt.ok(T.wf.go(T.VWhen{a1} <> et, T.WfElems{p}),
              _v => T.wf.go(t,
          T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VArr{+a1} <> +et}} <> +t False{}:
      hw =>
        +hin = {M3.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VArr{a1} <> et)), Bool.and(T.wf.key(kk, t),
          T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VArr{a1} <> et, T.WfElems{p}), _v => T.wf.go(t,
          T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VArr{a1} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}))
          == True{} : Bool}}
        Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VArr{a1} <> et}} <> t, "\n", True{},
          False{}), 0) == True{} : Bool} -> {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VArr{a1} <> et}} <> t,
          "\n", True{}, True{}), 0) == True{} : Bool} -> {D2.short.rows(T.VPair{kk, T.VAots{p,
          T.VArr{a1} <> et}} <> t) == True{} : Bool}, M3.wt.ok(T.wf.go(T.VArr{a1} <> et, T.WfElems{p}), _v => T.wf.go(t,
          T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VInl{+a1} <> +et}} <> +t False{}:
      hw =>
        +hin = {M3.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VInl{a1} <> et)), Bool.and(T.wf.key(kk, t),
          T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VInl{a1} <> et, T.WfElems{p}), _v => T.wf.go(t,
          T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VInl{a1} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}))
          == True{} : Bool}}
        Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VInl{a1} <> et}} <> t, "\n", True{},
          False{}), 0) == True{} : Bool} -> {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VInl{a1} <> et}} <> t,
          "\n", True{}, True{}), 0) == True{} : Bool} -> {D2.short.rows(T.VPair{kk, T.VAots{p,
          T.VInl{a1} <> et}} <> t) == True{} : Bool}, M3.wt.ok(T.wf.go(T.VInl{a1} <> et, T.WfElems{p}), _v => T.wf.go(t,
          T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VHead{+a1, +a2} <> +et}} <> +t False{}:
      hw =>
        +hin = {M3.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VHead{a1, a2} <> et)), Bool.and(T.wf.key(kk, t),
          T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VHead{a1, a2} <> et, T.WfElems{p}),
            _v => T.wf.go(t,
          T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VHead{a1, a2} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}))
          == True{} : Bool}}
        Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VHead{a1, a2} <> et}} <> t, "\n", True{},
          False{}), 0) == True{} : Bool} -> {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VHead{a1,
          a2} <> et}} <> t, "\n", True{}, True{}), 0) == True{} : Bool} -> {D2.short.rows(T.VPair{kk, T.VAots{p,
          T.VHead{a1, a2} <> et}} <> t) == True{} : Bool}, M3.wt.ok(T.wf.go(T.VHead{a1, a2} <> et, T.WfElems{p}),
          _v => T.wf.go(t,
          T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VAots{+a1, +a2} <> +et}} <> +t False{}:
      hw =>
        +hin = {M3.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VAots{a1, a2} <> et)), Bool.and(T.wf.key(kk, t),
          T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VAots{a1, a2} <> et, T.WfElems{p}),
            _v => T.wf.go(t,
          T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VAots{a1, a2} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}))
          == True{} : Bool}}
        Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VAots{a1, a2} <> et}} <> t, "\n", True{},
          False{}), 0) == True{} : Bool} -> {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VAots{a1,
          a2} <> et}} <> t, "\n", True{}, True{}), 0) == True{} : Bool} -> {D2.short.rows(T.VPair{kk, T.VAots{p,
          T.VAots{a1, a2} <> et}} <> t) == True{} : Bool}, M3.wt.ok(T.wf.go(T.VAots{a1, a2} <> et, T.WfElems{p}),
          _v => T.wf.go(t,
          T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VPair{+a1, T.VStr{+b1}} <> +et}} <> +t False{}:
      hw =>
        +hin = {M3.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VPair{a1, T.VStr{b1}} <> et)),
          Bool.and(T.wf.key(kk, t),
          T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VPair{a1, T.VStr{b1}} <> et, T.WfElems{p}),
            _v => T.wf.go(t,
          T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VPair{a1, T.VStr{b1}} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp}))
          == True{} : Bool}}
        Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VStr{b1}} <> et}} <> t, "\n",
          True{}, False{}), 0) == True{} : Bool} -> {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VStr{b1}} <> et}} <> t, "\n", True{}, True{}), 0) == True{} : Bool} -> {D2.short.rows(T.VPair{kk,
          T.VAots{p, T.VPair{a1, T.VStr{b1}} <> et}} <> t) == True{} : Bool}, M3.wt.ok(T.wf.go(T.VPair{a1,
          T.VStr{b1}} <> et, T.WfElems{p}), _v => T.wf.go(t,
          T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VPair{+a1, T.VSpan{+b1, +b2}} <> +et}} <> +t False{}:
      hw =>
        +hin = {M3.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VPair{a1, T.VSpan{b1, b2}} <> et)),
          Bool.and(T.wf.key(kk, t),
          T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VPair{a1, T.VSpan{b1, b2}} <> et, T.WfElems{p}),
            _v => T.wf.go(t,
          T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VPair{a1, T.VSpan{b1, b2}} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp}))
          == True{} : Bool}}
        Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VSpan{b1, b2}} <> et}} <> t,
          "\n", True{}, False{}), 0) == True{} : Bool} -> {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VSpan{b1, b2}} <> et}} <> t, "\n", True{}, True{}), 0) == True{} : Bool} -> {D2.short.rows(T.VPair{kk,
          T.VAots{p, T.VPair{a1, T.VSpan{b1, b2}} <> et}} <> t) == True{} : Bool}, M3.wt.ok(T.wf.go(T.VPair{a1,
              T.VSpan{b1,
          b2}} <> et, T.WfElems{p}), _v => T.wf.go(t,
          T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VPair{+a1, T.VInt{+b1, +b2}} <> +et}} <> +t False{}:
      hw =>
        +hin = {M3.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VPair{a1, T.VInt{b1, b2}} <> et)),
          Bool.and(T.wf.key(kk, t),
          T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VPair{a1, T.VInt{b1, b2}} <> et, T.WfElems{p}),
            _v => T.wf.go(t,
          T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VPair{a1, T.VInt{b1, b2}} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp}))
          == True{} : Bool}}
        Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VInt{b1, b2}} <> et}} <> t,
          "\n", True{}, False{}), 0) == True{} : Bool} -> {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VInt{b1, b2}} <> et}} <> t, "\n", True{}, True{}), 0) == True{} : Bool} -> {D2.short.rows(T.VPair{kk,
          T.VAots{p, T.VPair{a1, T.VInt{b1, b2}} <> et}} <> t) == True{} : Bool}, M3.wt.ok(T.wf.go(T.VPair{a1,
              T.VInt{b1,
          b2}} <> et, T.WfElems{p}), _v => T.wf.go(t,
          T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VPair{+a1, T.VFlo{+b1, +b2}} <> +et}} <> +t False{}:
      hw =>
        +hin = {M3.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VPair{a1, T.VFlo{b1, b2}} <> et)),
          Bool.and(T.wf.key(kk, t),
          T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VPair{a1, T.VFlo{b1, b2}} <> et, T.WfElems{p}),
            _v => T.wf.go(t,
          T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VPair{a1, T.VFlo{b1, b2}} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp}))
          == True{} : Bool}}
        Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VFlo{b1, b2}} <> et}} <> t,
          "\n", True{}, False{}), 0) == True{} : Bool} -> {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VFlo{b1, b2}} <> et}} <> t, "\n", True{}, True{}), 0) == True{} : Bool} -> {D2.short.rows(T.VPair{kk,
          T.VAots{p, T.VPair{a1, T.VFlo{b1, b2}} <> et}} <> t) == True{} : Bool}, M3.wt.ok(T.wf.go(T.VPair{a1,
              T.VFlo{b1,
          b2}} <> et, T.WfElems{p}), _v => T.wf.go(t,
          T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VPair{+a1, T.VBool{+b1}} <> +et}} <> +t False{}:
      hw =>
        +hin = {M3.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VPair{a1, T.VBool{b1}} <> et)),
          Bool.and(T.wf.key(kk, t),
          T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VPair{a1, T.VBool{b1}} <> et, T.WfElems{p}),
            _v => T.wf.go(t,
          T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VPair{a1, T.VBool{b1}} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp}))
          == True{} : Bool}}
        Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VBool{b1}} <> et}} <> t, "\n",
          True{}, False{}), 0) == True{} : Bool} -> {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VBool{b1}} <> et}} <> t, "\n", True{}, True{}), 0) == True{} : Bool} -> {D2.short.rows(T.VPair{kk,
          T.VAots{p, T.VPair{a1, T.VBool{b1}} <> et}} <> t) == True{} : Bool}, M3.wt.ok(T.wf.go(T.VPair{a1,
          T.VBool{b1}} <> et, T.WfElems{p}), _v => T.wf.go(t,
          T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VPair{+a1, T.VWhen{+b1}} <> +et}} <> +t False{}:
      hw =>
        +hin = {M3.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VPair{a1, T.VWhen{b1}} <> et)),
          Bool.and(T.wf.key(kk, t),
          T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VPair{a1, T.VWhen{b1}} <> et, T.WfElems{p}),
            _v => T.wf.go(t,
          T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VPair{a1, T.VWhen{b1}} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp}))
          == True{} : Bool}}
        Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VWhen{b1}} <> et}} <> t, "\n",
          True{}, False{}), 0) == True{} : Bool} -> {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VWhen{b1}} <> et}} <> t, "\n", True{}, True{}), 0) == True{} : Bool} -> {D2.short.rows(T.VPair{kk,
          T.VAots{p, T.VPair{a1, T.VWhen{b1}} <> et}} <> t) == True{} : Bool}, M3.wt.ok(T.wf.go(T.VPair{a1,
          T.VWhen{b1}} <> et, T.WfElems{p}), _v => T.wf.go(t,
          T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VPair{+a1, T.VArr{+b1}} <> +et}} <> +t False{}:
      hw =>
        +hin = {M3.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VPair{a1, T.VArr{b1}} <> et)),
          Bool.and(T.wf.key(kk, t),
          T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VPair{a1, T.VArr{b1}} <> et, T.WfElems{p}),
            _v => T.wf.go(t,
          T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VPair{a1, T.VArr{b1}} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp}))
          == True{} : Bool}}
        Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VArr{b1}} <> et}} <> t, "\n",
          True{}, False{}), 0) == True{} : Bool} -> {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VArr{b1}} <> et}} <> t, "\n", True{}, True{}), 0) == True{} : Bool} -> {D2.short.rows(T.VPair{kk,
          T.VAots{p, T.VPair{a1, T.VArr{b1}} <> et}} <> t) == True{} : Bool}, M3.wt.ok(T.wf.go(T.VPair{a1,
          T.VArr{b1}} <> et, T.WfElems{p}), _v => T.wf.go(t,
          T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VPair{+a1, T.VInl{+b1}} <> +et}} <> +t False{}:
      hw =>
        +hin = {M3.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VPair{a1, T.VInl{b1}} <> et)),
          Bool.and(T.wf.key(kk, t),
          T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VPair{a1, T.VInl{b1}} <> et, T.WfElems{p}),
            _v => T.wf.go(t,
          T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VPair{a1, T.VInl{b1}} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp}))
          == True{} : Bool}}
        Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VInl{b1}} <> et}} <> t, "\n",
          True{}, False{}), 0) == True{} : Bool} -> {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VInl{b1}} <> et}} <> t, "\n", True{}, True{}), 0) == True{} : Bool} -> {D2.short.rows(T.VPair{kk,
          T.VAots{p, T.VPair{a1, T.VInl{b1}} <> et}} <> t) == True{} : Bool}, M3.wt.ok(T.wf.go(T.VPair{a1,
          T.VInl{b1}} <> et, T.WfElems{p}), _v => T.wf.go(t,
          T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VPair{+a1, T.VHead{+b1, +b2}} <> +et}} <> +t False{}:
      hw =>
        +hin = {M3.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VPair{a1, T.VHead{b1, b2}} <> et)),
          Bool.and(T.wf.key(kk, t),
          T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VPair{a1, T.VHead{b1, b2}} <> et, T.WfElems{p}),
            _v => T.wf.go(t,
          T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VPair{a1, T.VHead{b1, b2}} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp}))
          == True{} : Bool}}
        Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VHead{b1, b2}} <> et}} <> t,
          "\n", True{}, False{}), 0) == True{} : Bool} -> {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VHead{b1, b2}} <> et}} <> t, "\n", True{}, True{}), 0) == True{} : Bool} -> {D2.short.rows(T.VPair{kk,
          T.VAots{p, T.VPair{a1, T.VHead{b1, b2}} <> et}} <> t) == True{} : Bool}, M3.wt.ok(T.wf.go(T.VPair{a1,
              T.VHead{b1,
          b2}} <> et, T.WfElems{p}), _v => T.wf.go(t,
          T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VPair{+a1, T.VAot{+b1, +b2}} <> +et}} <> +t False{}:
      hw =>
        +hin = {M3.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VPair{a1, T.VAot{b1, b2}} <> et)),
          Bool.and(T.wf.key(kk, t),
          T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VPair{a1, T.VAot{b1, b2}} <> et, T.WfElems{p}),
            _v => T.wf.go(t,
          T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VPair{a1, T.VAot{b1, b2}} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp}))
          == True{} : Bool}}
        Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VAot{b1, b2}} <> et}} <> t,
          "\n", True{}, False{}), 0) == True{} : Bool} -> {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VAot{b1, b2}} <> et}} <> t, "\n", True{}, True{}), 0) == True{} : Bool} -> {D2.short.rows(T.VPair{kk,
          T.VAots{p, T.VPair{a1, T.VAot{b1, b2}} <> et}} <> t) == True{} : Bool}, M3.wt.ok(T.wf.go(T.VPair{a1,
              T.VAot{b1,
          b2}} <> et, T.WfElems{p}), _v => T.wf.go(t,
          T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VPair{+a1, T.VAots{+b1, +b2}} <> +et}} <> +t False{}:
      hw =>
        +hin = {M3.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VPair{a1, T.VAots{b1, b2}} <> et)),
          Bool.and(T.wf.key(kk, t),
          T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VPair{a1, T.VAots{b1, b2}} <> et, T.WfElems{p}),
            _v => T.wf.go(t,
          T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VPair{a1, T.VAots{b1, b2}} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp}))
          == True{} : Bool}}
        Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VAots{b1, b2}} <> et}} <> t,
          "\n", True{}, False{}), 0) == True{} : Bool} -> {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VAots{b1, b2}} <> et}} <> t, "\n", True{}, True{}), 0) == True{} : Bool} -> {D2.short.rows(T.VPair{kk,
          T.VAots{p, T.VPair{a1, T.VAots{b1, b2}} <> et}} <> t) == True{} : Bool}, M3.wt.ok(T.wf.go(T.VPair{a1,
              T.VAots{b1,
          b2}} <> et, T.WfElems{p}), _v => T.wf.go(t,
          T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VPair{+a1, T.VPair{+b1, +b2}} <> +et}} <> +t False{}:
      hw =>
        +hin = {M3.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VPair{a1, T.VPair{b1, b2}} <> et)),
          Bool.and(T.wf.key(kk, t),
          T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VPair{a1, T.VPair{b1, b2}} <> et, T.WfElems{p}),
            _v => T.wf.go(t,
          T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(T.VPair{a1, T.VPair{b1, b2}} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp}))
          == True{} : Bool}}
        Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VPair{b1, b2}} <> et}} <> t,
          "\n", True{}, False{}), 0) == True{} : Bool} -> {D1.counts(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VPair{b1, b2}} <> et}} <> t, "\n", True{}, True{}), 0) == True{} : Bool} -> {D2.short.rows(T.VPair{kk,
          T.VAots{p, T.VPair{a1, T.VPair{b1, b2}} <> et}} <> t) == True{} : Bool}, M3.wt.ok(T.wf.go(T.VPair{a1,
              T.VPair{b1,
          b2}} <> et, T.WfElems{p}), _v => T.wf.go(t,
          T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAot{+a1, +a2}} <> +t False{}:
      hw => Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VPair{kk, T.VAot{a1, a2}} <> t, "\n", True{}, False{}),
        0) == True{} : Bool} -> {D1.counts(T.render.pass(T.VPair{kk, T.VAot{a1, a2}} <> t, "\n", True{}, True{}),
        0) == True{} : Bool} -> {D2.short.rows(T.VPair{kk, T.VAot{a1, a2}} <> t) == True{} : Bool}, hw)
    case T.VPair{+kk, T.VPair{+a1, +a2}} <> +t False{}:
      hw => Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VPair{kk, T.VPair{a1, a2}} <> t, "\n", True{}, False{}),
        0) == True{} : Bool} -> {D1.counts(T.render.pass(T.VPair{kk, T.VPair{a1, a2}} <> t, "\n", True{}, True{}),
        0) == True{} : Bool} -> {D2.short.rows(T.VPair{kk, T.VPair{a1, a2}} <> t) == True{} : Bool}, hw)
    case T.VStr{+a1} <> +t False{}:
      hw => Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VStr{a1} <> t, "\n", True{}, False{}),
        0) == True{} : Bool} -> {D1.counts(T.render.pass(T.VStr{a1} <> t, "\n", True{}, True{}),
        0) == True{} : Bool} -> {D2.short.rows(T.VStr{a1} <> t) == True{} : Bool}, hw)
    case T.VSpan{+a1, +a2} <> +t False{}:
      hw => Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VSpan{a1, a2} <> t, "\n", True{}, False{}),
        0) == True{} : Bool} -> {D1.counts(T.render.pass(T.VSpan{a1, a2} <> t, "\n", True{}, True{}),
        0) == True{} : Bool} -> {D2.short.rows(T.VSpan{a1, a2} <> t) == True{} : Bool}, hw)
    case T.VInt{+a1, +a2} <> +t False{}:
      hw => Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VInt{a1, a2} <> t, "\n", True{}, False{}),
        0) == True{} : Bool} -> {D1.counts(T.render.pass(T.VInt{a1, a2} <> t, "\n", True{}, True{}),
        0) == True{} : Bool} -> {D2.short.rows(T.VInt{a1, a2} <> t) == True{} : Bool}, hw)
    case T.VFlo{+a1, +a2} <> +t False{}:
      hw => Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VFlo{a1, a2} <> t, "\n", True{}, False{}),
        0) == True{} : Bool} -> {D1.counts(T.render.pass(T.VFlo{a1, a2} <> t, "\n", True{}, True{}),
        0) == True{} : Bool} -> {D2.short.rows(T.VFlo{a1, a2} <> t) == True{} : Bool}, hw)
    case T.VBool{+a1} <> +t False{}:
      hw => Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VBool{a1} <> t, "\n", True{}, False{}),
        0) == True{} : Bool} -> {D1.counts(T.render.pass(T.VBool{a1} <> t, "\n", True{}, True{}),
        0) == True{} : Bool} -> {D2.short.rows(T.VBool{a1} <> t) == True{} : Bool}, hw)
    case T.VWhen{+a1} <> +t False{}:
      hw => Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VWhen{a1} <> t, "\n", True{}, False{}),
        0) == True{} : Bool} -> {D1.counts(T.render.pass(T.VWhen{a1} <> t, "\n", True{}, True{}),
        0) == True{} : Bool} -> {D2.short.rows(T.VWhen{a1} <> t) == True{} : Bool}, hw)
    case T.VArr{+a1} <> +t False{}:
      hw => Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VArr{a1} <> t, "\n", True{}, False{}),
        0) == True{} : Bool} -> {D1.counts(T.render.pass(T.VArr{a1} <> t, "\n", True{}, True{}),
        0) == True{} : Bool} -> {D2.short.rows(T.VArr{a1} <> t) == True{} : Bool}, hw)
    case T.VInl{+a1} <> +t False{}:
      hw => Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VInl{a1} <> t, "\n", True{}, False{}),
        0) == True{} : Bool} -> {D1.counts(T.render.pass(T.VInl{a1} <> t, "\n", True{}, True{}),
        0) == True{} : Bool} -> {D2.short.rows(T.VInl{a1} <> t) == True{} : Bool}, hw)
    case T.VHead{+a1, +a2} <> +t False{}:
      hw => Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VHead{a1, a2} <> t, "\n", True{}, False{}),
        0) == True{} : Bool} -> {D1.counts(T.render.pass(T.VHead{a1, a2} <> t, "\n", True{}, True{}),
        0) == True{} : Bool} -> {D2.short.rows(T.VHead{a1, a2} <> t) == True{} : Bool}, hw)
    case T.VAot{+a1, +a2} <> +t False{}:
      hw => Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VAot{a1, a2} <> t, "\n", True{}, False{}),
        0) == True{} : Bool} -> {D1.counts(T.render.pass(T.VAot{a1, a2} <> t, "\n", True{}, True{}),
        0) == True{} : Bool} -> {D2.short.rows(T.VAot{a1, a2} <> t) == True{} : Bool}, hw)
    case T.VAots{+a1, +a2} <> +t False{}:
      hw => Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VAots{a1, a2} <> t, "\n", True{}, False{}),
        0) == True{} : Bool} -> {D1.counts(T.render.pass(T.VAots{a1, a2} <> t, "\n", True{}, True{}),
        0) == True{} : Bool} -> {D2.short.rows(T.VAots{a1, a2} <> t) == True{} : Bool}, hw)
    case T.VAot{+q, +r} <> +t True{}:
      +hw => +h2 =>
        +h1 = {M3.wt.more(T.str.eq(q, hp), _u => T.wf.then(T.wf.go(r, T.WfRows{q}), _v => T.wf.go(t, T.WfElems{hp})),
            hw)
          : {T.wf.then(T.wf.go(r, T.WfRows{q}), _v => T.wf.go(t, T.WfElems{hp})) == True{} : Bool}}
        +zz = {String.append(String.append(T.render.pass(r, "\n", True{}, False{}), T.render.pass(r, "\n", True{},
          True{})), T.render.pass(t, "\n", True{}, True{})) : String}
        +j1 = {M3.cd.dp(q, SCon{']', SCon{']', SCon{'\n', zz}}}, 0, M3.cd.dp("[[", String.append(q, SCon{']', SCon{']',
          SCon{'\n', zz}}}), 0, h2)) : {D1.counts(SCon{']', SCon{']', SCon{'\n', zz}}}, 0) == True{} : Bool}}
        +j2 = {M3.cd.dp("]]\n", zz, 0, j1) : {D1.counts(zz, 0) == True{} : Bool}}
        +j3 = {M3.cn.pf(String.append(T.render.pass(r, "\n", True{}, False{}), T.render.pass(r, "\n", True{}, True{})),
          T.render.pass(t, "\n", True{}, True{}), 0, j2) : {D1.counts(String.append(T.render.pass(r, "\n", True{},
          False{}), T.render.pass(r, "\n", True{}, True{})), 0) == True{} : Bool}}
        M3.cv.and2(D2.short.rows(r), D2.short.rows(t),
          sd(r, False{}, q)(M3.wt.ok(T.wf.go(r, T.WfRows{q}), _v => T.wf.go(t, T.WfElems{hp}), h1),
              M3.cn.pf(T.render.pass(r,
            "\n", True{}, False{}), T.render.pass(r, "\n", True{}, True{}), 0, j3),
            M3.cd.dp(T.render.pass(r, "\n", True{}, False{}), T.render.pass(r, "\n", True{}, True{}), 0, j3)),
          sd(t, True{}, hp)(M3.wt.more(T.wf.go(r, T.WfRows{q}), _v => T.wf.go(t, T.WfElems{hp}), h1),
            M3.cd.dp(String.append(T.render.pass(r, "\n", True{}, False{}), T.render.pass(r, "\n", True{}, True{})),
              T.render.pass(t, "\n", True{}, True{}), 0, j2)))
    case T.VStr{+a1} <> +t True{}:
      hw => Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VStr{a1} <> t, "\n", True{}, True{}),
        0) == True{} : Bool} -> {D2.short.rows(T.VStr{a1} <> t) == True{} : Bool}, hw)
    case T.VSpan{+a1, +a2} <> +t True{}:
      hw => Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VSpan{a1, a2} <> t, "\n", True{}, True{}),
        0) == True{} : Bool} -> {D2.short.rows(T.VSpan{a1, a2} <> t) == True{} : Bool}, hw)
    case T.VInt{+a1, +a2} <> +t True{}:
      hw => Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VInt{a1, a2} <> t, "\n", True{}, True{}),
        0) == True{} : Bool} -> {D2.short.rows(T.VInt{a1, a2} <> t) == True{} : Bool}, hw)
    case T.VFlo{+a1, +a2} <> +t True{}:
      hw => Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VFlo{a1, a2} <> t, "\n", True{}, True{}),
        0) == True{} : Bool} -> {D2.short.rows(T.VFlo{a1, a2} <> t) == True{} : Bool}, hw)
    case T.VBool{+a1} <> +t True{}:
      hw => Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VBool{a1} <> t, "\n", True{}, True{}),
        0) == True{} : Bool} -> {D2.short.rows(T.VBool{a1} <> t) == True{} : Bool}, hw)
    case T.VWhen{+a1} <> +t True{}:
      hw => Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VWhen{a1} <> t, "\n", True{}, True{}),
        0) == True{} : Bool} -> {D2.short.rows(T.VWhen{a1} <> t) == True{} : Bool}, hw)
    case T.VArr{+a1} <> +t True{}:
      hw => Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VArr{a1} <> t, "\n", True{}, True{}),
        0) == True{} : Bool} -> {D2.short.rows(T.VArr{a1} <> t) == True{} : Bool}, hw)
    case T.VInl{+a1} <> +t True{}:
      hw => Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VInl{a1} <> t, "\n", True{}, True{}),
        0) == True{} : Bool} -> {D2.short.rows(T.VInl{a1} <> t) == True{} : Bool}, hw)
    case T.VHead{+a1, +a2} <> +t True{}:
      hw => Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VHead{a1, a2} <> t, "\n", True{}, True{}),
        0) == True{} : Bool} -> {D2.short.rows(T.VHead{a1, a2} <> t) == True{} : Bool}, hw)
    case T.VAots{+a1, +a2} <> +t True{}:
      hw => Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VAots{a1, a2} <> t, "\n", True{}, True{}),
        0) == True{} : Bool} -> {D2.short.rows(T.VAots{a1, a2} <> t) == True{} : Bool}, hw)
    case T.VPair{+a1, T.VStr{+b1}} <> +t True{}:
      hw => Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VPair{a1, T.VStr{b1}} <> t, "\n", True{}, True{}),
        0) == True{} : Bool} -> {D2.short.rows(T.VPair{a1, T.VStr{b1}} <> t) == True{} : Bool}, hw)
    case T.VPair{+a1, T.VSpan{+b1, +b2}} <> +t True{}:
      hw => Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VPair{a1, T.VSpan{b1, b2}} <> t, "\n", True{}, True{}),
        0) == True{} : Bool} -> {D2.short.rows(T.VPair{a1, T.VSpan{b1, b2}} <> t) == True{} : Bool}, hw)
    case T.VPair{+a1, T.VInt{+b1, +b2}} <> +t True{}:
      hw => Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VPair{a1, T.VInt{b1, b2}} <> t, "\n", True{}, True{}),
        0) == True{} : Bool} -> {D2.short.rows(T.VPair{a1, T.VInt{b1, b2}} <> t) == True{} : Bool}, hw)
    case T.VPair{+a1, T.VFlo{+b1, +b2}} <> +t True{}:
      hw => Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VPair{a1, T.VFlo{b1, b2}} <> t, "\n", True{}, True{}),
        0) == True{} : Bool} -> {D2.short.rows(T.VPair{a1, T.VFlo{b1, b2}} <> t) == True{} : Bool}, hw)
    case T.VPair{+a1, T.VBool{+b1}} <> +t True{}:
      hw => Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VPair{a1, T.VBool{b1}} <> t, "\n", True{}, True{}),
        0) == True{} : Bool} -> {D2.short.rows(T.VPair{a1, T.VBool{b1}} <> t) == True{} : Bool}, hw)
    case T.VPair{+a1, T.VWhen{+b1}} <> +t True{}:
      hw => Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VPair{a1, T.VWhen{b1}} <> t, "\n", True{}, True{}),
        0) == True{} : Bool} -> {D2.short.rows(T.VPair{a1, T.VWhen{b1}} <> t) == True{} : Bool}, hw)
    case T.VPair{+a1, T.VArr{+b1}} <> +t True{}:
      hw => Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VPair{a1, T.VArr{b1}} <> t, "\n", True{}, True{}),
        0) == True{} : Bool} -> {D2.short.rows(T.VPair{a1, T.VArr{b1}} <> t) == True{} : Bool}, hw)
    case T.VPair{+a1, T.VInl{+b1}} <> +t True{}:
      hw => Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VPair{a1, T.VInl{b1}} <> t, "\n", True{}, True{}),
        0) == True{} : Bool} -> {D2.short.rows(T.VPair{a1, T.VInl{b1}} <> t) == True{} : Bool}, hw)
    case T.VPair{+a1, T.VHead{+b1, +b2}} <> +t True{}:
      hw => Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VPair{a1, T.VHead{b1, b2}} <> t, "\n", True{}, True{}),
        0) == True{} : Bool} -> {D2.short.rows(T.VPair{a1, T.VHead{b1, b2}} <> t) == True{} : Bool}, hw)
    case T.VPair{+a1, T.VAot{+b1, +b2}} <> +t True{}:
      hw => Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VPair{a1, T.VAot{b1, b2}} <> t, "\n", True{}, True{}),
        0) == True{} : Bool} -> {D2.short.rows(T.VPair{a1, T.VAot{b1, b2}} <> t) == True{} : Bool}, hw)
    case T.VPair{+a1, T.VAots{+b1, +b2}} <> +t True{}:
      hw => Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VPair{a1, T.VAots{b1, b2}} <> t, "\n", True{}, True{}),
        0) == True{} : Bool} -> {D2.short.rows(T.VPair{a1, T.VAots{b1, b2}} <> t) == True{} : Bool}, hw)
    case T.VPair{+a1, T.VPair{+b1, +b2}} <> +t True{}:
      hw => Eq.bit.absurd(&1, {D1.counts(T.render.pass(T.VPair{a1, T.VPair{b1, b2}} <> t, "\n", True{}, True{}),
        0) == True{} : Bool} -> {D2.short.rows(T.VPair{a1, T.VPair{b1, b2}} <> t) == True{} : Bool}, hw)
