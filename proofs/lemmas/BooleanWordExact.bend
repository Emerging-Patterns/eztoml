# the boolean scan accepts exactly true and false
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/BooleanWordExact.bend as L1
import ../../laws/defs/AbnfGrammar.bend as D1
import ../../laws/defs/BareValueGrammar.bend as D2
import ../../laws/defs/DocumentSameness.bend as D3
import ../../laws/defs/GrammarDerivations.bend as D4
import ./PrefixAndTake.bend as M1
import ./SpecialWordCompare.bend as M2

# The boolean law. A boolean is one of two special words, so only word.spec
# reads one: the datetime reader and the numeral scan never do.

# no datetime is a boolean
def n1.when.nbool(ww: T.WhenOut, +vv: T.Val) -> {D1.n1.got.bool(T.word.from.when(ww), vv) == False{} : Bool}:
  match ww:
    case T.WSome{_w}:
      {==}
    case T.WFail{_y}:
      {==}
    case T.WSkip{}:
      {==}

# an integer read or refused is no boolean
def n1.range.nbool(
  ok: Bool,
  +sg: T.Sign,
  +digits: String,
  +vv: T.Val
) -> {D1.n1.got.bool(T.num.fin.range(ok, sg, digits), vv) == False{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

# an integer, finished or refused, is no boolean
def n1.int.nbool(
  saw: Bool,
  +sg: T.Sign,
  +digits: String,
  +vv: T.Val
) -> {D1.n1.got.bool(T.num.fin.int(saw, sg, digits), vv) == False{} : Bool}:
  match saw:
    case True{}:
      n1.range.nbool(T.i64.fits(sg, digits), sg, digits, vv)
    case False{}:
      {==}

# a prefixed integer, finished or refused, is no boolean
def n1.base.nbool(
  sd: Bool,
  saw: Bool,
  +sg: T.Sign,
  +ds: List<&2, U32>,
  +vv: T.Val
) -> {D1.n1.got.bool(T.num.fin.base(sd, saw, sg, ds), vv) == False{} : Bool}:
  match sd:
    case True{}:
      {==}
    case False{}:
      n1.int.nbool(saw, sg, T.dec.text(ds), vv)

# a float, finished or refused, is no boolean
def n1.saw.nbool(
  saw: Bool,
  +sg: T.Sign,
  +text: String,
  +vv: T.Val
) -> {D1.n1.got.bool(T.num.fin.saw(saw, T.VFlo{sg, text}), vv) == False{} : Bool}:
  match saw:
    case True{}:
      {==}
    case False{}:
      {==}

# a finished scan is read as no boolean, by its fields
def n1.fin.nbool.go(
  uz: Bool,
  nk: T.NK,
  +saw: Bool,
  +sn: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +why: String,
  +cs: List<&2, Char>,
  +vv: T.Val
) -> {D1.n1.got.bool(T.num.fin(T.Num{nk, sn, base, ds, uz, saw, why}, cs), vv) == False{} : Bool}:
  match uz:
    case True{}:
      {==}
    case False{}:
      match nk:
        case T.NFrac{}:
          n1.saw.nbool(saw, sn, T.word.body(cs), vv)
        case T.NEDig{}:
          n1.saw.nbool(saw, sn, T.word.body(cs), vv)
        case T.NLead{}:
          {==}
        case T.NSign{}:
          {==}
        case T.NZero{}:
          {==}
        case T.NDig{}:
          n1.int.nbool(saw, sn, T.dec.text(ds), vv)
        case T.NBase{}:
          n1.base.nbool(T.num.signed(cs), saw, sn, ds, vv)
        case T.NExp{}:
          {==}
        case T.NBad{}:
          {==}

# a finished scan is read as no boolean
def n1.fin.nbool(
  +st: T.Num,
  +cs: List<&2, Char>,
  +vv: T.Val
) -> {D1.n1.got.bool(T.num.fin(st, cs), vv) == False{} : Bool}:
  match st:
    case T.Num{nk, +sg, +base, +ds, us, +saw, +why}:
      n1.fin.nbool.go(us, nk, saw, sg, base, ds, why, cs, vv)

# what the boolean law claims of a word
def n1.bool.G(+cs: List<&2, Char>, +vv: T.Val) -> Type:
  {D1.n1.got.bool(T.word.val(cs), vv) == Bool.and(D2.abnf.boolean(cs), D1.g.val(D4.GvBoolean{cs}, vv))
    : Bool}

# true's reading holds the value exactly when the value is true
def n1.bool.t(vv: T.Val) -> n1.bool.G(String.to_list("true"), vv):
  match vv:
    case T.VBool{b2}:
      match b2:
        case True{}:
          {==}
        case False{}:
          {==}
    case T.VFlo{_s, _t}:
      {==}
    case T.VStr{_t}:
      {==}
    case T.VSpan{_s, _n}:
      {==}
    case T.VInt{_s, _d}:
      {==}
    case T.VWhen{_w}:
      {==}
    case T.VArr{_i}:
      {==}
    case T.VInl{_r}:
      {==}
    case T.VHead{_p, _r}:
      {==}
    case T.VAot{_p, _r}:
      {==}
    case T.VAots{_p, _e}:
      {==}
    case T.VPair{_n, _v}:
      {==}

# false's reading holds the value exactly when the value is false
def n1.bool.f(vv: T.Val) -> n1.bool.G(String.to_list("false"), vv):
  match vv:
    case T.VBool{b2}:
      match b2:
        case True{}:
          {==}
        case False{}:
          {==}
    case T.VFlo{_s, _t}:
      {==}
    case T.VStr{_t}:
      {==}
    case T.VSpan{_s, _n}:
      {==}
    case T.VInt{_s, _d}:
      {==}
    case T.VWhen{_w}:
      {==}
    case T.VArr{_i}:
      {==}
    case T.VInl{_r}:
      {==}
    case T.VHead{_p, _r}:
      {==}
    case T.VAot{_p, _r}:
      {==}
    case T.VAots{_p, _e}:
      {==}
    case T.VPair{_n, _v}:
      {==}

# a special word's reading, for each special word
def n1.bool.spec(+vv: T.Val, +cs: List<&2, Char>, hs: {M2.n1.isspec(cs) == True{} : Bool}) -> n1.bool.G(cs, vv):
  M2.n1.spec.split(xs => n1.bool.G(xs, vv), cs, hs, n1.bool.t(vv), n1.bool.f(vv), {==}, {==}, {==}, {==}, {==}, {==})

# a word that is no special word is no boolean
def n1.bool.no(
  +cs: List<&2, Char>,
  +hs: {M2.n1.isspec(cs) == False{} : Bool}
) -> {D2.abnf.boolean(cs) == False{} : Bool}:
  +h1 = {Eq.or.left_false(D2.abnf.chars_are(cs, "true"), Bool.or(D2.abnf.chars_are(cs, "false"),
    Bool.or(D2.abnf.chars_are(cs, "inf"), Bool.or(D2.abnf.chars_are(cs, "+inf"), Bool.or(D2.abnf.chars_are(cs,
    "-inf"), Bool.or(D2.abnf.chars_are(cs, "nan"), Bool.or(D2.abnf.chars_are(cs, "+nan"), D2.abnf.chars_are(cs,
    "-nan"))))))), hs) : {D2.abnf.chars_are(cs, "true") == False{} : Bool}}
  +h2 = {Eq.or.left_false(D2.abnf.chars_are(cs, "false"), Bool.or(D2.abnf.chars_are(cs, "inf"),
    Bool.or(D2.abnf.chars_are(cs, "+inf"), Bool.or(D2.abnf.chars_are(cs, "-inf"), Bool.or(D2.abnf.chars_are(cs,
    "nan"), Bool.or(D2.abnf.chars_are(cs, "+nan"), D2.abnf.chars_are(cs, "-nan")))))),
    Eq.or.right_false(D2.abnf.chars_are(cs, "true"), Bool.or(D2.abnf.chars_are(cs, "false"),
    Bool.or(D2.abnf.chars_are(cs, "inf"), Bool.or(D2.abnf.chars_are(cs, "+inf"), Bool.or(D2.abnf.chars_are(cs,
    "-inf"), Bool.or(D2.abnf.chars_are(cs, "nan"), Bool.or(D2.abnf.chars_are(cs, "+nan"), D2.abnf.chars_are(cs,
    "-nan"))))))), hs)) : {D2.abnf.chars_are(cs, "false") == False{} : Bool}}
  %Equal.sym(Bool, D2.abnf.chars_are(cs, "true"), False{}, h1) : {Bool.or(_, D2.abnf.chars_are(cs, "false"))
    == False{} : Bool}
  h2

# a word sent to the datetime reader or the numeral scan is read as no
# boolean
def n1.bool.ns.go(
  ad: Bool,
  +cs: List<&2, Char>,
  +vv: T.Val
) -> {D1.n1.got.bool(T.word.route.date(ad, cs), vv) == False{} : Bool}:
  match ad:
    case True{}:
      n1.when.nbool(T.when.read(cs), vv)
    case False{}:
      n1.fin.nbool(T.num.go(cs, T.num.start()), cs, vv)

# a word that is no special word is read as no boolean, and matches none
def n1.bool.ns(+cs: List<&2, Char>, +vv: T.Val, +hs: {M2.n1.isspec(cs) == False{} : Bool}) -> n1.bool.G(cs, vv):
  %Equal.sym(T.Got, T.word.val(cs), T.word.route.date(T.word.as_date(T.word.or(T.word.colon(cs), T.word.dash(cs,
    True{})), T.word.ee(cs)), cs), M2.n1.wv.ns(cs, hs)) : {D1.n1.got.bool(_, vv) == Bool.and(D2.abnf.boolean(cs),
    D1.g.val(D4.GvBoolean{cs}, vv)) : Bool}
  %Equal.sym(Bool, D2.abnf.boolean(cs), False{}, n1.bool.no(cs, hs)) : {D1.n1.got.bool(T.word.route.date(
    T.word.as_date(T.word.or(T.word.colon(cs), T.word.dash(cs, True{})), T.word.ee(cs)), cs), vv) == Bool.and(_,
    D1.g.val(D4.GvBoolean{cs}, vv)) : Bool}
  n1.bool.ns.go(T.word.as_date(T.word.or(T.word.colon(cs), T.word.dash(cs, True{})), T.word.ee(cs)), cs, vv)

# the boolean law, by whether the word is a special word
def n1.bool.law(sp: Bool, +cs: List<&2, Char>, +vv: T.Val, es: {M2.n1.isspec(cs) == sp : Bool}) -> n1.bool.G(cs, vv):
  match sp:
    case True{}:
      n1.bool.spec(vv, cs, es)
    case False{}:
      n1.bool.ns(cs, vv, es)

def L1.boolean_word_exact(cs, v):
  n1.bool.law(M2.n1.isspec(cs), cs, v, {==})

# two bits bit.eq takes for one are one
def vl.eq.bit(
  b1: Bool,
  b2: Bool,
  hh: {D3.bit.eq(b2, b1) == True{} : Bool}
) -> {T.GotVal{T.VBool{b1}} == T.GotVal{T.VBool{b2}} : T.Got}:
  match b1 b2:
    case True{} True{}:
      {==}
    case False{} False{}:
      {==}
    case True{} False{}:
      Eq.bit.absurd(&2, {T.GotVal{T.VBool{True{}}} == T.GotVal{T.VBool{False{}}} : T.Got}, hh)
    case False{} True{}:
      Eq.bit.absurd(&2, {T.GotVal{T.VBool{False{}}} == T.GotVal{T.VBool{True{}}} : T.Got}, hh)

# and a boolean's
def vl.eq.bool(gg: T.Got, vv: T.Val, hh: {D1.n1.got.bool(gg, vv) == True{} : Bool}) -> {gg == T.GotVal{vv} : T.Got}:
  match gg:
    case T.GotVal{g1}:
      match g1:
        case T.VBool{+b1}:
          match vv:
            case T.VBool{+b2}:
              vl.eq.bit(b1, b2, hh)
            case T.VStr{_a}:
              Eq.bit.absurd(&2, {T.GotVal{T.VBool{b1}} == T.GotVal{T.VStr{_a}} : T.Got}, hh)
            case T.VSpan{_a, _b}:
              Eq.bit.absurd(&2, {T.GotVal{T.VBool{b1}} == T.GotVal{T.VSpan{_a, _b}} : T.Got}, hh)
            case T.VInt{_a, _b}:
              Eq.bit.absurd(&2, {T.GotVal{T.VBool{b1}} == T.GotVal{T.VInt{_a, _b}} : T.Got}, hh)
            case T.VFlo{_a, _b}:
              Eq.bit.absurd(&2, {T.GotVal{T.VBool{b1}} == T.GotVal{T.VFlo{_a, _b}} : T.Got}, hh)
            case T.VWhen{_a}:
              Eq.bit.absurd(&2, {T.GotVal{T.VBool{b1}} == T.GotVal{T.VWhen{_a}} : T.Got}, hh)
            case T.VArr{_a}:
              Eq.bit.absurd(&2, {T.GotVal{T.VBool{b1}} == T.GotVal{T.VArr{_a}} : T.Got}, hh)
            case T.VInl{_a}:
              Eq.bit.absurd(&2, {T.GotVal{T.VBool{b1}} == T.GotVal{T.VInl{_a}} : T.Got}, hh)
            case T.VHead{_a, _b}:
              Eq.bit.absurd(&2, {T.GotVal{T.VBool{b1}} == T.GotVal{T.VHead{_a, _b}} : T.Got}, hh)
            case T.VAot{_a, _b}:
              Eq.bit.absurd(&2, {T.GotVal{T.VBool{b1}} == T.GotVal{T.VAot{_a, _b}} : T.Got}, hh)
            case T.VAots{_a, _b}:
              Eq.bit.absurd(&2, {T.GotVal{T.VBool{b1}} == T.GotVal{T.VAots{_a, _b}} : T.Got}, hh)
            case T.VPair{_a, _b}:
              Eq.bit.absurd(&2, {T.GotVal{T.VBool{b1}} == T.GotVal{T.VPair{_a, _b}} : T.Got}, hh)
        case T.VStr{_a}:
          Eq.bit.absurd(&2, {T.GotVal{T.VStr{_a}} == T.GotVal{vv} : T.Got}, hh)
        case T.VSpan{_a, _b}:
          Eq.bit.absurd(&2, {T.GotVal{T.VSpan{_a, _b}} == T.GotVal{vv} : T.Got}, hh)
        case T.VInt{_a, _b}:
          Eq.bit.absurd(&2, {T.GotVal{T.VInt{_a, _b}} == T.GotVal{vv} : T.Got}, hh)
        case T.VFlo{_a, _b}:
          Eq.bit.absurd(&2, {T.GotVal{T.VFlo{_a, _b}} == T.GotVal{vv} : T.Got}, hh)
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

# a word the boolean rule matches, denoting v, reads as v
def vl.hv.bool(
  +cs: List<&2, Char>,
  +hw: {D2.abnf.boolean(cs) == True{} : Bool},
  +vv: T.Val,
  +hv: {D1.g.val(D4.GvBoolean{cs}, vv) == True{} : Bool}
) -> {T.word.val(cs) == T.GotVal{vv} : T.Got}:
  vl.eq.bool(T.word.val(cs), vv, Equal.trans(Bool, D1.n1.got.bool(T.word.val(cs), vv), Bool.and(
    D2.abnf.boolean(cs), D1.g.val(D4.GvBoolean{cs}, vv)), True{}, L1.boolean_word_exact(cs, vv),
    M1.and.tt(D2.abnf.boolean(cs), D1.g.val(D4.GvBoolean{cs}, vv), hw, hv)))
