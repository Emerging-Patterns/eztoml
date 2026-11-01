# proofs of laws/WordRefusedInDocument.bend
import Base
import ../main.bend as T
import ../src/eq.bend as Eq
import ../laws/BooleanWordExact.bend as L1
import ../laws/DateTimeReadExactly.bend as L2
import ../laws/FloatReadExactly.bend as L3
import ../laws/IntegerReadExactly.bend as L4
import ../laws/WordRefusedInDocument.bend as Laws
import ../laws/defs/AbnfGrammar.bend as D1
import ../laws/defs/BareValueGrammar.bend as D2
import ../laws/defs/DocumentSameness.bend as D3
import ../laws/defs/GrammarDerivations.bend as D4
import ../laws/defs/ScalarReadbackScan.bend as D5
import ./lemmas/BareKeyValueScan.bend as M1
import ./lemmas/BareWordReadsOn.bend as M2
import ./lemmas/BareWordRefusal.bend as M3
import ./lemmas/BooleanWordExact.bend as M4
import ./lemmas/DateTimeWordGrammar.bend as M5
import ./lemmas/FloatWordExact.bend as M6
import ./lemmas/IntegerWordExact.bend as M7
import ./lemmas/PrefixAndTake.bend as M8
import ./lemmas/ValueSelfEquality.bend as M9

# the four rules a bare value may match, each as g.ok.val reads it
def vl.rules(+cs: List<&2, Char>) -> Bool:
  Bool.or(D1.g.ok.val(D4.GvBoolean{cs}, D1.RVal{}), Bool.or(D1.g.ok.val(D4.GvInteger{cs}, D1.RVal{}),
    Bool.or(D1.g.ok.val(D4.GvFloat{cs}, D1.RVal{}), D1.g.ok.val(D4.GvDateTime{cs}, D1.RVal{}))))

# a word that matches none of them matches each of them not
def vl.rules.no(+cs: List<&2, Char>, hn: {Laws.bw.none(cs) == True{} : Bool}) -> {vl.rules(cs) == False{} : Bool}:
  Eq.not.true(vl.rules(cs), hn)

# the integer rule
def vl.no.int(
  +cs: List<&2, Char>,
  +hn: {Laws.bw.none(cs) == True{} : Bool}
) -> {D1.g.ok.val(D4.GvInteger{cs}, D1.RVal{}) == False{} : Bool}:
  Eq.or.left_false(D1.g.ok.val(D4.GvInteger{cs}, D1.RVal{}), Bool.or(D1.g.ok.val(D4.GvFloat{cs},
    D1.RVal{}), D1.g.ok.val(D4.GvDateTime{cs}, D1.RVal{})), Eq.or.right_false(D1.g.ok.val(
    D4.GvBoolean{cs}, D1.RVal{}), Bool.or(D1.g.ok.val(D4.GvInteger{cs}, D1.RVal{}),
    Bool.or(D1.g.ok.val(D4.GvFloat{cs}, D1.RVal{}), D1.g.ok.val(D4.GvDateTime{cs}, D1.RVal{}))),
    vl.rules.no(cs, hn)))

# the float rule
def vl.no.flo(
  +cs: List<&2, Char>,
  +hn: {Laws.bw.none(cs) == True{} : Bool}
) -> {D1.g.ok.val(D4.GvFloat{cs}, D1.RVal{}) == False{} : Bool}:
  Eq.or.left_false(D1.g.ok.val(D4.GvFloat{cs}, D1.RVal{}), D1.g.ok.val(D4.GvDateTime{cs}, D1.RVal{}),
    Eq.or.right_false(D1.g.ok.val(D4.GvInteger{cs}, D1.RVal{}), Bool.or(D1.g.ok.val(D4.GvFloat{cs},
    D1.RVal{}), D1.g.ok.val(D4.GvDateTime{cs}, D1.RVal{})), Eq.or.right_false(D1.g.ok.val(
    D4.GvBoolean{cs}, D1.RVal{}), Bool.or(D1.g.ok.val(D4.GvInteger{cs}, D1.RVal{}),
    Bool.or(D1.g.ok.val(D4.GvFloat{cs}, D1.RVal{}), D1.g.ok.val(D4.GvDateTime{cs}, D1.RVal{}))),
    vl.rules.no(cs, hn))))

# the date-time rule
def vl.no.dt(
  +cs: List<&2, Char>,
  +hn: {Laws.bw.none(cs) == True{} : Bool}
) -> {D1.g.ok.val(D4.GvDateTime{cs}, D1.RVal{}) == False{} : Bool}:
  Eq.or.right_false(D1.g.ok.val(D4.GvFloat{cs}, D1.RVal{}), D1.g.ok.val(D4.GvDateTime{cs}, D1.RVal{}),
    Eq.or.right_false(D1.g.ok.val(D4.GvInteger{cs}, D1.RVal{}), Bool.or(D1.g.ok.val(D4.GvFloat{cs},
    D1.RVal{}), D1.g.ok.val(D4.GvDateTime{cs}, D1.RVal{})), Eq.or.right_false(D1.g.ok.val(
    D4.GvBoolean{cs}, D1.RVal{}), Bool.or(D1.g.ok.val(D4.GvInteger{cs}, D1.RVal{}),
    Bool.or(D1.g.ok.val(D4.GvFloat{cs}, D1.RVal{}), D1.g.ok.val(D4.GvDateTime{cs}, D1.RVal{}))),
    vl.rules.no(cs, hn))))

# the boolean rule
def vl.no.bool(
  +cs: List<&2, Char>,
  +hn: {Laws.bw.none(cs) == True{} : Bool}
) -> {D1.g.ok.val(D4.GvBoolean{cs}, D1.RVal{}) == False{} : Bool}:
  Eq.or.left_false(D1.g.ok.val(D4.GvBoolean{cs}, D1.RVal{}), Bool.or(D1.g.ok.val(D4.GvInteger{cs},
    D1.RVal{}), Bool.or(D1.g.ok.val(D4.GvFloat{cs}, D1.RVal{}), D1.g.ok.val(D4.GvDateTime{cs},
    D1.RVal{}))), vl.rules.no(cs, hn))

# a rule that is false and true is no rule
def vl.clash(aa: Bool, e1: {aa == False{} : Bool}, e2: {aa == True{} : Bool}) -> {False{} == True{} : Bool}:
  Equal.trans(Bool, False{}, aa, True{}, Equal.sym(Bool, aa, False{}, e1), e2)

# a word that matches none of the rules is read as no value: by the
# classifiers, the value word.val gives would match its kind's rule
def vl.rn.val(
  vv: T.Val,
  +cs: List<&2, Char>,
  +eg: {T.word.val(cs) == T.GotVal{vv} : T.Got},
  sc: {M2.vl.sc(T.GotVal{vv}) == True{} : Bool},
  +hn: {Laws.bw.none(cs) == True{} : Bool}
) -> {False{} == True{} : Bool}:
  match vv:
    case T.VInt{+sg, +ds}:
      vl.clash(D1.g.ok.val(D4.GvInteger{cs}, D1.RVal{}), vl.no.int(cs, hn), Eq.and.left(D1.g.ok.val(
        D4.GvInteger{cs}, D1.RVal{}), D1.g.val(D4.GvInteger{cs}, T.VInt{sg, ds}), Equal.trans(Bool,
        Bool.and(D1.g.ok.val(D4.GvInteger{cs}, D1.RVal{}), D1.g.val(D4.GvInteger{cs}, T.VInt{sg, ds})),
        L4.n1.got.int(T.word.val(cs), T.VInt{sg, ds}), True{}, Equal.sym(Bool, L4.n1.got.int(T.word.val(cs),
        T.VInt{sg, ds}), Bool.and(D1.g.ok.val(D4.GvInteger{cs}, D1.RVal{}), D1.g.val(D4.GvInteger{cs},
        T.VInt{sg, ds})), L4.integer_word_exact(cs, T.VInt{sg, ds})), Equal.trans(Bool,
        L4.n1.got.int(T.word.val(cs), T.VInt{sg, ds}), L4.n1.got.int(T.GotVal{T.VInt{sg, ds}}, T.VInt{sg, ds}),
        True{}, Equal.cong(T.Got, Bool, gg => L4.n1.got.int(gg, T.VInt{sg, ds}), T.word.val(cs),
        T.GotVal{T.VInt{sg, ds}}, eg), M8.and.tt(D3.sign.eq(sg, sg), String.eq(ds, ds), M9.sign.self(sg),
        Eq.string_eq_self(ds))))))
    case T.VFlo{+sg, +tx}:
      vl.clash(D1.g.ok.val(D4.GvFloat{cs}, D1.RVal{}), vl.no.flo(cs, hn), Eq.and.left(D1.g.ok.val(
        D4.GvFloat{cs}, D1.RVal{}), D1.g.val(D4.GvFloat{cs}, T.VFlo{sg, tx}), Equal.trans(Bool,
        Bool.and(D1.g.ok.val(D4.GvFloat{cs}, D1.RVal{}), D1.g.val(D4.GvFloat{cs}, T.VFlo{sg, tx})),
        L3.n1.got.flo(T.word.val(cs), T.VFlo{sg, tx}), True{}, Equal.sym(Bool, L3.n1.got.flo(T.word.val(cs),
        T.VFlo{sg, tx}), Bool.and(D1.g.ok.val(D4.GvFloat{cs}, D1.RVal{}), D1.g.val(D4.GvFloat{cs},
        T.VFlo{sg, tx})), L3.float_word_exact(cs, T.VFlo{sg, tx})), Equal.trans(Bool,
        L3.n1.got.flo(T.word.val(cs), T.VFlo{sg, tx}), L3.n1.got.flo(T.GotVal{T.VFlo{sg, tx}}, T.VFlo{sg, tx}),
        True{}, Equal.cong(T.Got, Bool, gg => L3.n1.got.flo(gg, T.VFlo{sg, tx}), T.word.val(cs),
        T.GotVal{T.VFlo{sg, tx}}, eg), M8.and.tt(D3.sign.eq(sg, sg), String.eq(tx, tx), M9.sign.self(sg),
        Eq.string_eq_self(tx))))))
    case T.VBool{+bt}:
      vl.clash(D1.g.ok.val(D4.GvBoolean{cs}, D1.RVal{}), vl.no.bool(cs, hn), Eq.and.left(D1.g.ok.val(
        D4.GvBoolean{cs}, D1.RVal{}), D1.g.val(D4.GvBoolean{cs}, T.VBool{bt}), Equal.trans(Bool,
        Bool.and(D1.g.ok.val(D4.GvBoolean{cs}, D1.RVal{}), D1.g.val(D4.GvBoolean{cs}, T.VBool{bt})),
        D1.n1.got.bool(T.word.val(cs), T.VBool{bt}), True{}, Equal.sym(Bool, D1.n1.got.bool(T.word.val(cs),
        T.VBool{bt}), Bool.and(D1.g.ok.val(D4.GvBoolean{cs}, D1.RVal{}), D1.g.val(D4.GvBoolean{cs},
        T.VBool{bt})), L1.boolean_word_exact(cs, T.VBool{bt})), Equal.trans(Bool,
        D1.n1.got.bool(T.word.val(cs), T.VBool{bt}), D1.n1.got.bool(T.GotVal{T.VBool{bt}}, T.VBool{bt}),
        True{}, Equal.cong(T.Got, Bool, gg => D1.n1.got.bool(gg, T.VBool{bt}), T.word.val(cs),
        T.GotVal{T.VBool{bt}}, eg), M9.bit.self(bt)))))
    case T.VWhen{+ww}:
      vl.clash(D1.g.ok.val(D4.GvDateTime{cs}, D1.RVal{}), vl.no.dt(cs, hn), Eq.and.left(D1.g.ok.val(
        D4.GvDateTime{cs}, D1.RVal{}), D1.g.val(D4.GvDateTime{cs}, T.VWhen{ww}), Equal.trans(Bool,
        Bool.and(D1.g.ok.val(D4.GvDateTime{cs}, D1.RVal{}), D1.g.val(D4.GvDateTime{cs}, T.VWhen{ww})),
        L2.t1.got_when(T.word.val(cs), ww), True{}, Equal.sym(Bool, L2.t1.got_when(T.word.val(cs), ww),
        Bool.and(D1.g.ok.val(D4.GvDateTime{cs}, D1.RVal{}), D1.g.val(D4.GvDateTime{cs}, T.VWhen{ww})),
        L2.date_time_word(cs, ww)), Equal.trans(Bool, L2.t1.got_when(T.word.val(cs), ww),
        L2.t1.got_when(T.GotVal{T.VWhen{ww}}, ww), True{}, Equal.cong(T.Got, Bool, gg => L2.t1.got_when(gg, ww),
        T.word.val(cs), T.GotVal{T.VWhen{ww}}, eg), M9.when.self(ww)))))
    case T.VStr{_tx}:
      sc
    case T.VSpan{_src, _nn}:
      sc
    case T.VArr{_it}:
      sc
    case T.VInl{_rs}:
      sc
    case T.VHead{_pp, _rs}:
      sc
    case T.VAot{_pp, _rs}:
      sc
    case T.VAots{_pp, _es}:
      sc
    case T.VPair{_nm, _pv}:
      sc

# the document from the value state has an error, by the word's outcome
def vl.rn.at(
  gg: T.Got,
  +ww: String,
  +kk: String,
  +hw: {D2.bw.word(ww) == True{} : Bool},
  +eg: {T.word.val(String.to_list(ww)) == gg : T.Got},
  sc: {M2.vl.sc(gg) == True{} : Bool},
  +hn: {Laws.bw.none(String.to_list(ww)) == True{} : Bool}
) -> M3.vl.Bad(String.append(ww, "\n"), T.MScan{D5.vst(M2.vl.kf(kk), [], T.LVal{})}):
  match gg:
    case T.GotVal{vv}:
      Eq.bit.absurd(&1, M3.vl.Bad(String.append(ww, "\n"), T.MScan{D5.vst(M2.vl.kf(kk), [], T.LVal{})}),
        vl.rn.val(vv, String.to_list(ww), eg, sc, hn))
    case T.GotBad{+why}:
      M3.vl.blift(ww, hw, why, eg, M2.vl.kf(kk), "\n", {==})

def Laws.word_refused_in_document(k, ek, w, hw, hn):
  match k:
    case SNil{}:
      Eq.bit.absurd(&2, {String.is_empty(T.bad(T.parse(D1.bw.kv(SNil{}, w)))) == False{} : Bool}, ek)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          Equal.trans(Bool, String.is_empty(T.bad(T.parse(D1.bw.kv(SCon{Chr{xx}, tt}, w)))),
            String.is_empty(T.bad(T.doc.read(String.append(w, "\n"), T.MScan{D5.vst(M2.vl.kf(SCon{Chr{xx}, tt}), [],
            T.LVal{})}))), False{},
            Equal.cong(T.Doc, Bool, dd => String.is_empty(T.bad(dd)), T.parse(D1.bw.kv(SCon{Chr{xx}, tt}, w)),
              T.doc.read(String.append(w, "\n"), T.MScan{D5.vst(M2.vl.kf(SCon{Chr{xx}, tt}), [], T.LVal{})}),
              M1.kv.key2(xx, tt, String.append(w, "\n"), ek)),
            vl.rn.at(T.word.val(String.to_list(w)), w, SCon{Chr{xx}, tt}, hw, {==}, M2.vl.sc.word(String.to_list(w)),
              hn))
