# proofs of laws/FloatReadExactly.bend
import Base
import ../main.bend as T
import ../src/eq.bend as Eq
import ../laws/FloatReadExactly.bend as Laws
import ../laws/defs/AbnfGrammar.bend as D1
import ../laws/defs/BareValueGrammar.bend as D2
import ../laws/defs/DocumentSameness.bend as D3
import ../laws/defs/GrammarDerivations.bend as D4
import ./lemmas/BareWordInArray.bend as M1
import ./lemmas/BareWordRefusal.bend as M2
import ./lemmas/BooleanIsBareWord.bend as M3
import ./lemmas/DigitsWrittenBack.bend as M4
import ./lemmas/FloatIsBareWord.bend as M5
import ./lemmas/FloatWordExact.bend as M6
import ./lemmas/PrefixAndTake.bend as M7
import ./lemmas/ValueTextReadback.bend as M8

# nor a float
def vl.norm.flo(gg: T.Got, +vv: T.Val) -> {Laws.n1.got.flo(M2.vl.norm(gg), vv) == Laws.n1.got.flo(gg, vv) : Bool}:
  match gg:
    case T.GotVal{_v}:
      {==}
    case T.GotBad{_why}:
      {==}

def Laws.float_parses_exactly(k, ek, w, hw, v):
  Equal.trans(Bool, Laws.n1.got.flo(D2.bw.got(T.parse(D1.bw.kv(k, w)), k), v),
    Laws.n1.got.flo(M2.vl.norm(T.word.val(String.to_list(w))), v),
    Bool.and(D1.abnf.float(String.to_list(w)), D1.g.val(D4.GvFloat{String.to_list(w)}, v)),
    Equal.cong(T.Got, Bool, gg => Laws.n1.got.flo(gg, v), D2.bw.got(T.parse(D1.bw.kv(k, w)), k),
      M2.vl.norm(T.word.val(String.to_list(w))), M2.vl.pv(k, ek, w, hw)),
    Equal.trans(Bool, Laws.n1.got.flo(M2.vl.norm(T.word.val(String.to_list(w))), v),
      Laws.n1.got.flo(T.word.val(String.to_list(w)), v),
      Bool.and(D1.abnf.float(String.to_list(w)), D1.g.val(D4.GvFloat{String.to_list(w)}, v)),
      vl.norm.flo(T.word.val(String.to_list(w)), v), Laws.float_word_exact(String.to_list(w), v)))

# render's halves. A float's sign is sign.text; a datetime's text is its
# tokens (when.eq), none of which is a t, a z or a space.

def Laws.float_render(sg, _t):
  match sg:
    case T.Plus{}:
      {==}
    case T.Minus{}:
      {==}

# a bare word's reading that n1.got.flo takes for vv is vv
def vl.eq.flo(gg: T.Got, vv: T.Val, +hh: {Laws.n1.got.flo(gg, vv) == True{} : Bool}) -> {gg == T.GotVal{vv} : T.Got}:
  match gg:
    case T.GotVal{g1}:
      match g1:
        case T.VFlo{+s1, +d1}:
          match vv:
            case T.VFlo{+s2, +d2}:
              Equal.trans(T.Got, T.GotVal{T.VFlo{s1, d1}}, T.GotVal{T.VFlo{s2, d1}}, T.GotVal{T.VFlo{s2, d2}},
                Equal.cong(T.Sign, T.Got, xx => T.GotVal{T.VFlo{xx, d1}}, s1, s2, Equal.sym(T.Sign, s2, s1,
                M4.n1.sign.eq(s2, s1, Eq.and.left(D3.sign.eq(s2, s1), String.eq(d2, d1), hh)))),
                Equal.cong(String, T.Got, yy => T.GotVal{T.VFlo{s2, yy}}, d1, d2, Equal.sym(String, d2, d1,
                M3.vl.str.eq(d2, d1, Eq.and.right(D3.sign.eq(s2, s1), String.eq(d2, d1), hh)))))
            case T.VStr{_a}:
              Eq.bit.absurd(&2, {T.GotVal{T.VFlo{s1, d1}} == T.GotVal{T.VStr{_a}} : T.Got}, hh)
            case T.VSpan{_a, _b}:
              Eq.bit.absurd(&2, {T.GotVal{T.VFlo{s1, d1}} == T.GotVal{T.VSpan{_a, _b}} : T.Got}, hh)
            case T.VInt{_a, _b}:
              Eq.bit.absurd(&2, {T.GotVal{T.VFlo{s1, d1}} == T.GotVal{T.VInt{_a, _b}} : T.Got}, hh)
            case T.VBool{_a}:
              Eq.bit.absurd(&2, {T.GotVal{T.VFlo{s1, d1}} == T.GotVal{T.VBool{_a}} : T.Got}, hh)
            case T.VWhen{_a}:
              Eq.bit.absurd(&2, {T.GotVal{T.VFlo{s1, d1}} == T.GotVal{T.VWhen{_a}} : T.Got}, hh)
            case T.VArr{_a}:
              Eq.bit.absurd(&2, {T.GotVal{T.VFlo{s1, d1}} == T.GotVal{T.VArr{_a}} : T.Got}, hh)
            case T.VInl{_a}:
              Eq.bit.absurd(&2, {T.GotVal{T.VFlo{s1, d1}} == T.GotVal{T.VInl{_a}} : T.Got}, hh)
            case T.VHead{_a, _b}:
              Eq.bit.absurd(&2, {T.GotVal{T.VFlo{s1, d1}} == T.GotVal{T.VHead{_a, _b}} : T.Got}, hh)
            case T.VAot{_a, _b}:
              Eq.bit.absurd(&2, {T.GotVal{T.VFlo{s1, d1}} == T.GotVal{T.VAot{_a, _b}} : T.Got}, hh)
            case T.VAots{_a, _b}:
              Eq.bit.absurd(&2, {T.GotVal{T.VFlo{s1, d1}} == T.GotVal{T.VAots{_a, _b}} : T.Got}, hh)
            case T.VPair{_a, _b}:
              Eq.bit.absurd(&2, {T.GotVal{T.VFlo{s1, d1}} == T.GotVal{T.VPair{_a, _b}} : T.Got}, hh)
        case T.VStr{_a}:
          Eq.bit.absurd(&2, {T.GotVal{T.VStr{_a}} == T.GotVal{vv} : T.Got}, hh)
        case T.VSpan{_a, _b}:
          Eq.bit.absurd(&2, {T.GotVal{T.VSpan{_a, _b}} == T.GotVal{vv} : T.Got}, hh)
        case T.VInt{_a, _b}:
          Eq.bit.absurd(&2, {T.GotVal{T.VInt{_a, _b}} == T.GotVal{vv} : T.Got}, hh)
        case T.VBool{_a}:
          Eq.bit.absurd(&2, {T.GotVal{T.VBool{_a}} == T.GotVal{vv} : T.Got}, hh)
        case T.VWhen{_a}:
          Eq.bit.absurd(&2, {T.GotVal{T.VWhen{_a}} == T.GotVal{vv} : T.Got}, hh)
        case T.VArr{_a}:
          Eq.bit.absurd(&2, {T.GotVal{T.VArr{_a}} == T.GotVal{vv} : T.Got}, hh)
        case T.VInl{_a}:
          Eq.bit.absurd(&2, {T.GotVal{T.VInl{_a}} == T.GotVal{vv} : T.Got}, hh)
        case T.VHead{_a, _b}:
          Eq.bit.absurd(&2, {T.GotVal{T.VHead{_a, _b}} == T.GotVal{vv} : T.Got}, hh)
        case T.VAot{_a, _b}:
          Eq.bit.absurd(&2, {T.GotVal{T.VAot{_a, _b}} == T.GotVal{vv} : T.Got}, hh)
        case T.VAots{_a, _b}:
          Eq.bit.absurd(&2, {T.GotVal{T.VAots{_a, _b}} == T.GotVal{vv} : T.Got}, hh)
        case T.VPair{_a, _b}:
          Eq.bit.absurd(&2, {T.GotVal{T.VPair{_a, _b}} == T.GotVal{vv} : T.Got}, hh)
    case T.GotBad{why}:
      Eq.bit.absurd(&2, {T.GotBad{why} == T.GotVal{vv} : T.Got}, hh)

# a word the float rule matches, denoting v, reads as v
def vl.hv.flo(
  +cs: List<&2, Char>,
  +hw: {D1.abnf.float(cs) == True{} : Bool},
  +vv: T.Val,
  +hv: {D1.g.val(D4.GvFloat{cs}, vv) == True{} : Bool}
) -> {T.word.val(cs) == T.GotVal{vv} : T.Got}:
  vl.eq.flo(T.word.val(cs), vv, Equal.trans(Bool, Laws.n1.got.flo(T.word.val(cs), vv), Bool.and(D1.abnf.float(cs),
    D1.g.val(D4.GvFloat{cs}, vv)), True{}, Laws.float_word_exact(cs, vv), M7.and.tt(D1.abnf.float(cs),
    D1.g.val(D4.GvFloat{cs}, vv), hw, hv)))

def Laws.float_parses_as_denoted(k, ek, w, hw, v, hv):
  M3.vl.acc.v(k, ek, w, Laws.float_is_bare_word(w, hw), v, vl.hv.flo(String.to_list(w), hw, v, hv),
    M3.vl.sc.of(String.to_list(w), v, vl.hv.flo(String.to_list(w), hw, v, hv)))

def Laws.float_parses_as_denoted_in_array(k, ek, w, hw, v, hv):
  M1.vl.acc.a(k, ek, w, Laws.float_is_bare_word(w, hw), v, vl.hv.flo(String.to_list(w), hw, v, hv),
    M3.vl.sc.of(String.to_list(w), v, vl.hv.flo(String.to_list(w), hw, v, hv)))

def Laws.float_parses_as_denoted_in_inline_table(k, ek, w, hw, v, hv):
  M3.vl.acc.i(k, ek, w, Laws.float_is_bare_word(w, hw), v, vl.hv.flo(String.to_list(w), hw, v, hv),
    M3.vl.sc.of(String.to_list(w), v, vl.hv.flo(String.to_list(w), hw, v, hv)))
