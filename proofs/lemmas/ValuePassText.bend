# the key pass's text for a scalar, array or inline table pair
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/PassValue.bend as L1
import ../../laws/defs/BareValueGrammar.bend as D1
import ./ShortTextBounds.bend as M1

# the key pass: a pair of an array or an inline table
def pv.cl(
  +kk: String,
  +c1: Char,
  +rr: String,
  +c2: Char,
  +yy: String
) -> {String.append(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', SCon{c1, String.append(rr, SCon{c2,
  SNil{}})}}}}), yy) == String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', SCon{c1, String.append(rr, SCon{c2,
  yy})}}}}) : String}:
  Equal.trans(String,
    String.append(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', SCon{c1, String.append(rr, SCon{c2,
      SNil{}})}}}}), yy),
    String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', SCon{c1, String.append(String.append(rr, SCon{c2, SNil{}}),
      yy)}}}}),
    String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', SCon{c1, String.append(rr, SCon{c2, yy})}}}}),
    Eq.append_assoc(T.key(kk), SCon{' ', SCon{'=', SCon{' ', SCon{c1, String.append(rr, SCon{c2, SNil{}})}}}}, yy),
    Equal.cong(String, String, zz => String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', SCon{c1, zz}}}}),
      String.append(String.append(rr, SCon{c2, SNil{}}), yy), String.append(rr, SCon{c2, yy}),
      Eq.append_assoc(rr, SCon{c2, SNil{}}, yy)))

# the key pass: a pair of a scalar
def pv.at(
  +kk: String,
  +aa: String,
  +yy: String
) -> {String.append(String.append(T.key(kk), SCon{' ', SCon{'=', SCon{' ', aa}}}), yy) == String.append(T.key(kk),
  SCon{' ', SCon{'=', SCon{' ', String.append(aa, yy)}}}) : String}:
  Eq.append_assoc(T.key(kk), SCon{' ', SCon{'=', SCon{' ', aa}}}, yy)

def L1.pass_value(k, v, hw, rest, gap, trail):
  match v:
    case T.VArr{+items}:
      pv.cl(k, '[', T.render.go(items, ", ", False{}), ']', String.append(T.render.suf(gap, trail, List.is_empty(&2,
        T.Val, rest)), T.render.pass(rest, gap, trail, False{})))
    case T.VInl{+rows}:
      pv.cl(k, '{', T.render.go(rows, ", ", False{}), '}', String.append(T.render.suf(gap, trail, List.is_empty(&2,
        T.Val, rest)), T.render.pass(rest, gap, trail, False{})))
    case T.VStr{+aa}:
      pv.at(k, T.render.atom(T.VStr{aa}), String.append(T.render.suf(gap, trail, List.is_empty(&2, T.Val, rest)),
        T.render.pass(rest, gap, trail, False{})))
    case T.VSpan{+aa, +bb}:
      pv.at(k, T.render.atom(T.VSpan{aa, bb}), String.append(T.render.suf(gap, trail, List.is_empty(&2, T.Val, rest)),
        T.render.pass(rest, gap, trail, False{})))
    case T.VInt{+aa, +bb}:
      pv.at(k, T.render.atom(T.VInt{aa, bb}), String.append(T.render.suf(gap, trail, List.is_empty(&2, T.Val, rest)),
        T.render.pass(rest, gap, trail, False{})))
    case T.VFlo{+aa, +bb}:
      pv.at(k, T.render.atom(T.VFlo{aa, bb}), String.append(T.render.suf(gap, trail, List.is_empty(&2, T.Val, rest)),
        T.render.pass(rest, gap, trail, False{})))
    case T.VBool{+aa}:
      pv.at(k, T.render.atom(T.VBool{aa}), String.append(T.render.suf(gap, trail, List.is_empty(&2, T.Val, rest)),
        T.render.pass(rest, gap, trail, False{})))
    case T.VWhen{+aa}:
      pv.at(k, T.render.atom(T.VWhen{aa}), String.append(T.render.suf(gap, trail, List.is_empty(&2, T.Val, rest)),
        T.render.pass(rest, gap, trail, False{})))
    case T.VHead{aa, bb}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{k, T.VHead{aa, bb}} <> rest, gap, trail, False{})
        == String.append(T.key(k), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VHead{aa, bb}, String.append(
        T.render.suf(gap, trail, List.is_empty(&2, T.Val, rest)), T.render.pass(rest, gap, trail, False{})))}}})
        : String}, hw)
    case T.VAot{aa, bb}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{k, T.VAot{aa, bb}} <> rest, gap, trail, False{})
        == String.append(T.key(k), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VAot{aa, bb}, String.append(
        T.render.suf(gap, trail, List.is_empty(&2, T.Val, rest)), T.render.pass(rest, gap, trail, False{})))}}})
        : String}, hw)
    case T.VAots{aa, bb}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{k, T.VAots{aa, bb}} <> rest, gap, trail, False{})
        == String.append(T.key(k), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VAots{aa, bb}, String.append(
        T.render.suf(gap, trail, List.is_empty(&2, T.Val, rest)), T.render.pass(rest, gap, trail, False{})))}}})
        : String}, hw)
    case T.VPair{aa, bb}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{k, T.VPair{aa, bb}} <> rest, gap, trail, False{})
        == String.append(T.key(k), SCon{' ', SCon{'=', SCon{' ', D1.cv.tx(T.VPair{aa, bb}, String.append(
        T.render.suf(gap, trail, List.is_empty(&2, T.Val, rest)), T.render.pass(rest, gap, trail, False{})))}}})
        : String}, hw)

# the key pass writes nothing for the elements of an array of tables
def tt.pe(
  es: List<&2, T.Val>,
  +pp: String,
  +hw: {T.wf.go(es, T.WfElems{pp}) == True{} : Bool}
) -> {T.render.pass(es, "\n", True{}, False{}) == "" : String}:
  match es:
    case []:
      {==}
    case T.VAot{+qq, +r} <> +t:
      tt.pe(t, pp, M1.wt.more(T.wf.go(r, T.WfRows{qq}), _v => T.wf.go(t, T.WfElems{pp}), M1.wt.more(T.str.eq(qq, pp),
        _u => T.wf.then(T.wf.go(r, T.WfRows{qq}), _v => T.wf.go(t, T.WfElems{pp})), hw)))

    case T.VStr{+a1} <> +t:
      Eq.bit.absurd(&2, {T.render.pass(T.VStr{a1} <> t, "\n", True{}, False{}) == "" : String},
        hw)
    case T.VSpan{+a1, +a2} <> +t:
      Eq.bit.absurd(&2, {T.render.pass(T.VSpan{a1, a2} <> t, "\n", True{}, False{}) == "" : String},
        hw)
    case T.VInt{+a1, +a2} <> +t:
      Eq.bit.absurd(&2, {T.render.pass(T.VInt{a1, a2} <> t, "\n", True{}, False{}) == "" : String},
        hw)
    case T.VFlo{+a1, +a2} <> +t:
      Eq.bit.absurd(&2, {T.render.pass(T.VFlo{a1, a2} <> t, "\n", True{}, False{}) == "" : String},
        hw)
    case T.VBool{+a1} <> +t:
      Eq.bit.absurd(&2, {T.render.pass(T.VBool{a1} <> t, "\n", True{}, False{}) == "" : String},
        hw)
    case T.VWhen{+a1} <> +t:
      Eq.bit.absurd(&2, {T.render.pass(T.VWhen{a1} <> t, "\n", True{}, False{}) == "" : String},
        hw)
    case T.VArr{+a1} <> +t:
      Eq.bit.absurd(&2, {T.render.pass(T.VArr{a1} <> t, "\n", True{}, False{}) == "" : String},
        hw)
    case T.VInl{+a1} <> +t:
      Eq.bit.absurd(&2, {T.render.pass(T.VInl{a1} <> t, "\n", True{}, False{}) == "" : String},
        hw)
    case T.VHead{+a1, +a2} <> +t:
      Eq.bit.absurd(&2, {T.render.pass(T.VHead{a1, a2} <> t, "\n", True{}, False{}) == "" : String},
        hw)
    case T.VAots{+a1, +a2} <> +t:
      Eq.bit.absurd(&2, {T.render.pass(T.VAots{a1, a2} <> t, "\n", True{}, False{}) == "" : String},
        hw)
    case T.VPair{+a1, a2} <> +t:
      match a2:
        case T.VStr{+b1}:
          Eq.bit.absurd(&2, {T.render.pass(T.VPair{a1, T.VStr{b1}} <> t, "\n", True{},
            False{}) == "" : String}, hw)
        case T.VSpan{+b1, +b2}:
          Eq.bit.absurd(&2, {T.render.pass(T.VPair{a1, T.VSpan{b1, b2}} <> t, "\n", True{},
            False{}) == "" : String}, hw)
        case T.VInt{+b1, +b2}:
          Eq.bit.absurd(&2, {T.render.pass(T.VPair{a1, T.VInt{b1, b2}} <> t, "\n", True{},
            False{}) == "" : String}, hw)
        case T.VFlo{+b1, +b2}:
          Eq.bit.absurd(&2, {T.render.pass(T.VPair{a1, T.VFlo{b1, b2}} <> t, "\n", True{},
            False{}) == "" : String}, hw)
        case T.VBool{+b1}:
          Eq.bit.absurd(&2, {T.render.pass(T.VPair{a1, T.VBool{b1}} <> t, "\n", True{},
            False{}) == "" : String}, hw)
        case T.VWhen{+b1}:
          Eq.bit.absurd(&2, {T.render.pass(T.VPair{a1, T.VWhen{b1}} <> t, "\n", True{},
            False{}) == "" : String}, hw)
        case T.VArr{+b1}:
          Eq.bit.absurd(&2, {T.render.pass(T.VPair{a1, T.VArr{b1}} <> t, "\n", True{},
            False{}) == "" : String}, hw)
        case T.VInl{+b1}:
          Eq.bit.absurd(&2, {T.render.pass(T.VPair{a1, T.VInl{b1}} <> t, "\n", True{},
            False{}) == "" : String}, hw)
        case T.VHead{+b1, +b2}:
          Eq.bit.absurd(&2, {T.render.pass(T.VPair{a1, T.VHead{b1, b2}} <> t, "\n", True{},
            False{}) == "" : String}, hw)
        case T.VAot{+b1, +b2}:
          Eq.bit.absurd(&2, {T.render.pass(T.VPair{a1, T.VAot{b1, b2}} <> t, "\n", True{},
            False{}) == "" : String}, hw)
        case T.VAots{+b1, +b2}:
          Eq.bit.absurd(&2, {T.render.pass(T.VPair{a1, T.VAots{b1, b2}} <> t, "\n", True{},
            False{}) == "" : String}, hw)
        case T.VPair{+b1, +b2}:
          Eq.bit.absurd(&2, {T.render.pass(T.VPair{a1, T.VPair{b1, b2}} <> t, "\n", True{},
            False{}) == "" : String}, hw)

# the table pass's text for an array of tables: its elements, then the
# later tables
def tt.aots(
  +kk: String,
  +pp: String,
  +es: List<&2, T.Val>,
  +t: List<&2, T.Val>,
  +rest: String,
  +pe: {T.render.pass(es, "\n", True{}, False{}) == "" : String}
) -> {String.append(T.render.pass(T.VPair{kk, T.VAots{pp, es}} <> t, "\n", True{}, True{}), rest)
  == String.append(T.render.pass(es, "\n", True{}, True{}), String.append(T.render.pass(t, "\n", True{}, True{}),
  rest)) : String}:
  +x2 = {T.render.pass(es, "\n", True{}, True{}) : String}
  +x3 = {T.render.pass(t, "\n", True{}, True{}) : String}
  Equal.trans(String,
    String.append(String.append(String.append(T.render.pass(es, "\n", True{}, False{}), x2), x3), rest),
    String.append(String.append(String.append("", x2), x3), rest),
    String.append(x2, String.append(x3, rest)),
    Equal.cong(String, String, zz => String.append(String.append(String.append(zz, x2), x3), rest),
      T.render.pass(es, "\n", True{}, False{}), "", pe),
    Eq.append_assoc(x2, x3, rest))
