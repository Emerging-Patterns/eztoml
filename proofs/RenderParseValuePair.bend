# proofs of laws/RenderParseValuePair.bend
import Base
import ../main.bend as T
import ../src/eq.bend as Eq
import ../laws/PassValue.bend as L1
import ../laws/RenderParseValuePair.bend as Laws
import ../laws/ValueReadsBack.bend as L2
import ../laws/defs/BareValueGrammar.bend as D1
import ../laws/defs/DocumentSameness.bend as D2
import ./lemmas/BareKeyValueScan.bend as M1
import ./lemmas/PrefixAndTake.bend as M2
import ./lemmas/ReadOutEquality.bend as M3
import ./lemmas/ValuePassText.bend as M4
import ./lemmas/ValueSelfEquality.bend as M5
import ./lemmas/ValueTextReadback.bend as M6

# The document of one pair. render writes the key, " = ", the value's text
# and a newline, and nothing in the pass that writes tables; parse reads the
# key and then the value (value_reads_back's reader), and the document it
# ends with, sealed and read out, is the document render was given, read out.

# the pass that writes tables writes nothing for a pair of a value that is
# no table
def rv.tabs(
  +kk: String,
  vv: T.Val,
  hv: {D1.cv.wf(vv) == True{} : Bool}
) -> {T.render.pass([T.VPair{kk, vv}], "\n", True{}, True{}) == "" : String}:
  match vv:
    case T.VStr{_a}:
      {==}
    case T.VSpan{_a, _b}:
      {==}
    case T.VInt{_a, _b}:
      {==}
    case T.VFlo{_a, _b}:
      {==}
    case T.VBool{_a}:
      {==}
    case T.VWhen{_a}:
      {==}
    case T.VArr{_a}:
      {==}
    case T.VInl{_a}:
      {==}
    case T.VHead{aa, bb}:
      Eq.bit.absurd(&2, {T.render.pass([T.VPair{kk, T.VHead{aa, bb}}], "\n", True{}, True{}) == "" : String}, hv)
    case T.VAot{_a, _b}:
      {==}
    case T.VAots{aa, bb}:
      Eq.bit.absurd(&2, {T.render.pass([T.VPair{kk, T.VAots{aa, bb}}], "\n", True{}, True{}) == "" : String}, hv)
    case T.VPair{_a, _b}:
      {==}

# the text of a document of one pair of such a value: the key, " = ", the
# value's text and a newline
def rv.text(
  +ee: String,
  +kk: String,
  +vv: T.Val,
  +hv: {D1.cv.wf(vv) == True{} : Bool},
  ek: {T.bare(kk) == True{} : Bool}
) -> {T.render(T.Doc{ee, [T.VPair{kk, vv}]}) == String.append(kk, SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(vv,
  "\n")}}}) : String}:
  +yy = {SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(vv, "\n")}}} : String}
  Equal.trans(String, T.render(T.Doc{ee, [T.VPair{kk, vv}]}),
    String.append(String.append(T.key(kk), yy), T.render.pass([T.VPair{kk, vv}], "\n", True{}, True{})),
    String.append(kk, yy),
    Equal.cong(String, String, xs => String.append(xs, T.render.pass([T.VPair{kk, vv}], "\n", True{}, True{})),
      T.render.pass([T.VPair{kk, vv}], "\n", True{}, False{}), String.append(T.key(kk), yy),
      L1.pass_value(kk, vv, hv, [], "\n", True{})),
    Equal.trans(String, String.append(String.append(T.key(kk), yy), T.render.pass([T.VPair{kk, vv}], "\n", True{},
      True{})), String.append(String.append(T.key(kk), yy), ""), String.append(kk, yy),
      Equal.cong(String, String, xs => String.append(String.append(T.key(kk), yy), xs),
        T.render.pass([T.VPair{kk, vv}], "\n", True{}, True{}), "", rv.tabs(kk, vv, hv)),
      Equal.trans(String, String.append(String.append(T.key(kk), yy), ""), String.append(T.key(kk), yy),
        String.append(kk, yy), Eq.append_nil(String.append(T.key(kk), yy)),
        Equal.cong(Bool, String, bb => String.append(T.key.go(bb, kk), yy), T.bare(kk), True{}, ek))))

# for a pair of a value that is no table, the root's verdict is an inline
# table's
def rv.r2i(
  +kk: String,
  vv: T.Val,
  hv: {D1.cv.wf(vv) == True{} : Bool},
  ww: {T.wf.go([T.VPair{kk, vv}], T.WfRows{""}) == True{} : Bool}
) -> {T.wf.go([T.VPair{kk, vv}], T.WfInl{}) == True{} : Bool}:
  match vv:
    case T.VStr{_a}:
      ww
    case T.VSpan{_a, _b}:
      ww
    case T.VInt{_a, _b}:
      ww
    case T.VFlo{_a, _b}:
      ww
    case T.VBool{_a}:
      ww
    case T.VWhen{_a}:
      ww
    case T.VArr{_a}:
      ww
    case T.VInl{_a}:
      ww
    case T.VHead{aa, bb}:
      Eq.bit.absurd(&2, {T.wf.go([T.VPair{kk, T.VHead{aa, bb}}], T.WfInl{}) == True{} : Bool}, hv)
    case T.VAot{aa, bb}:
      Eq.bit.absurd(&2, {T.wf.go([T.VPair{kk, T.VAot{aa, bb}}], T.WfInl{}) == True{} : Bool}, hv)
    case T.VAots{aa, bb}:
      Eq.bit.absurd(&2, {T.wf.go([T.VPair{kk, T.VAots{aa, bb}}], T.WfInl{}) == True{} : Bool}, hv)
    case T.VPair{aa, bb}:
      Eq.bit.absurd(&2, {T.wf.go([T.VPair{kk, T.VPair{aa, bb}}], T.WfInl{}) == True{} : Bool}, hv)

# the root's rows once the pair is put, sealed, are the same as the pair
# render was given, both ways
def rv.same(
  +ee: String,
  +kk: String,
  +vv: T.Val,
  +ww: T.Val,
  +ho: {D1.own.rows(T.rows.seal([T.VPair{kk, vv}])) == D1.own.rows([T.VPair{kk, ww}]) : List<&2, T.Val>},
  +w: {T.wf.go([T.VPair{kk, ww}], T.WfRows{""}) == True{} : Bool}
) -> {D2.same(T.Doc{"", T.rows.seal([T.VPair{kk, vv}])}, T.Doc{ee, [T.VPair{kk, ww}]}) == True{} : Bool}:
  +rr = {T.rows.seal([T.VPair{kk, vv}]) : List<&2, T.Val>}
  +pp = {[T.VPair{kk, ww}] : List<&2, T.Val>}
  +self = {M5.refl.rows(pp, M5.wf.selfs(pp, T.WfRows{""}, w)) : {D2.same.go(pp, pp) == True{} : Bool}}
  M2.and.tt(D2.same.go(rr, pp), D2.same.go(pp, rr),
    Equal.trans(Bool, D2.same.go(rr, pp), D2.same.go(D1.own.rows(rr), pp), True{},
      Equal.sym(Bool, D2.same.go(D1.own.rows(rr), pp), D2.same.go(rr, pp), M3.own.l(rr, pp)),
      Equal.trans(Bool, D2.same.go(D1.own.rows(rr), pp), D2.same.go(D1.own.rows(pp), pp), True{},
        Equal.cong(List<&2, T.Val>, Bool, xs => D2.same.go(xs, pp), D1.own.rows(rr), D1.own.rows(pp), ho),
        Equal.trans(Bool, D2.same.go(D1.own.rows(pp), pp), D2.same.go(pp, pp), True{}, M3.own.l(pp, pp), self))),
    Equal.trans(Bool, D2.same.go(pp, rr), D2.same.go(pp, D1.own.rows(rr)), True{},
      Equal.sym(Bool, D2.same.go(pp, D1.own.rows(rr)), D2.same.go(pp, rr), M3.own.r(pp, rr)),
      Equal.trans(Bool, D2.same.go(pp, D1.own.rows(rr)), D2.same.go(pp, D1.own.rows(pp)), True{},
        Equal.cong(List<&2, T.Val>, Bool, xs => D2.same.go(pp, xs), D1.own.rows(rr), D1.own.rows(pp), ho),
        Equal.trans(Bool, D2.same.go(pp, D1.own.rows(pp)), D2.same.go(pp, pp), True{}, M3.own.r(pp, pp), self))))

# the claim the law makes of a document
def rv.Ok(+dd: T.Doc, +d0: T.Doc) -> Type:
  {Bool.and(String.is_empty(T.bad(dd)), D2.same(dd, d0)) == True{} : Bool}

# after the value, the newline ends the document, and the claim holds of it
def rv.fin(
  +ee: String,
  +kk: String,
  +vv: T.Val,
  +ww: T.Val,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +hh: {L2.cv.own1(vv) == L2.cv.raw1(ww) : T.Val},
  +hw: {D1.cv.wf(ww) == True{} : Bool},
  +w: {T.wf.go([T.VPair{kk, ww}], T.WfRows{""}) == True{} : Bool}
) -> rv.Ok(T.doc.read("\n", T.MScan{T.take.top([], vv, "", [], [], [], [kk], bk, qk, un, lf, False{}, False{})}),
  T.Doc{ee, [T.VPair{kk, ww}]}):
  rv.same(ee, kk, vv, ww, M6.rv.own(kk, vv, ww, hh, hw, rv.r2i(kk, ww, hw, w)), w)

def Laws.render_parse_value_pair(e, k, ek, v, w, hv, hl):
  match k:
    case SNil{}:
      Eq.bit.absurd(&1, rv.Ok(T.parse(T.render(T.Doc{e, [T.VPair{SNil{}, v}]})), T.Doc{e, [T.VPair{SNil{}, v}]}), ek)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          +kk = {SCon{Chr{xx}, tt} : String}
          +d0 = {T.Doc{e, [T.VPair{kk, v}]} : T.Doc}
          M6.pp.step(dd => rv.Ok(dd, d0), T.parse(T.render(d0)),
            T.doc.read(D1.cv.tx(v, "\n"), T.MScan{M6.cv.vp([], [], [], [kk], T.LTop{}, T.QBasic{}, [], 0, 0, False{})}),
            Equal.trans(T.Doc, T.parse(T.render(d0)),
              T.parse(String.append(kk, SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(v, "\n")}}})),
              T.doc.read(D1.cv.tx(v, "\n"), T.MScan{M6.cv.vp([], [], [], [kk], T.LTop{}, T.QBasic{}, [], 0, 0,
                False{})}),
              Equal.cong(String, T.Doc, ss => T.parse(ss), T.render(d0),
                String.append(kk, SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(v, "\n")}}}), rv.text(e, kk, v, hv, ek)),
              M1.kv.key2(xx, tt, D1.cv.tx(v, "\n"), ek)),
            M6.cv.val(v, [], [], [], [kk], T.LTop{}, T.QBasic{}, [], 0, 0, False{}, "\n", dd => rv.Ok(dd, d0), hv,
              hl)({==},
              +vv => bk => qk => un => lf => ho => rv.fin(e, kk, vv, v, bk, qk, un, lf, ho, hv, w)))
