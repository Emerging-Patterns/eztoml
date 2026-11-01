# a boolean is a bare word, with its character facts and placement as a scalar
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/BooleanIsBareWord.bend as L1
import ../../laws/defs/AbnfGrammar.bend as D1
import ../../laws/defs/BareValueGrammar.bend as D2
import ../../laws/defs/ScalarReadbackScan.bend as D3
import ./BareKeyValueScan.bend as M1
import ./BareWordReadsOn.bend as M2
import ./FailedWalkNameCompare.bend as M3
import ./GrammarWordMatching.bend as M4
import ./PickAndDigitSteps.bend as M5
import ./PrefixAndTake.bend as M6

# A word a bare value rule matches is a bare word. Every character the
# integer, float and boolean rules take starts a bare value, and so does
# every one the date-time rules take but the space of time-delim, which comes
# right after a full-date (DDDD-DD-DD) and before a partial-time's first
# DIGIT, where the scan keeps it.

# every character of a list starts a bare value
def vl.qs(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      True{}
    case +hh <> tt:
      Bool.and(D2.word.first(hh), vl.qs(tt))

# whether a list starts with a digit
def vl.d1(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      False{}
    case +hh <> _tt:
      Char.is_digit(hh)

# bw.more, over a list
def vl.morel(cs: List<&2, Char>, +buf: List<&2, Char>) -> Bool:
  match cs:
    case []:
      True{}
    case +hh <> +tt:
      Bool.and(Bool.or(D2.word.char(hh), Bool.and(Char.is_eq(hh, ' '), Bool.and(T.date.shaped(buf), vl.d1(tt)))),
        vl.morel(tt, hh <> buf))

# bw.word, over a list
def vl.wordl(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      False{}
    case +hh <> tt:
      Bool.and(D2.word.first(hh), vl.morel(tt, [hh]))

# a text starts with a digit as its characters do
def vl.d1.eq(ss: String) -> {D2.bw.digit1(ss) == vl.d1(String.to_list(ss)) : Bool}:
  match ss:
    case SNil{}:
      {==}
    case SCon{_hh, _tt}:
      {==}

# bw.more is vl.morel of the text's characters
def vl.more.eq(ss: String, +buf: List<&2, Char>) -> {D2.bw.more(ss, buf) == vl.morel(String.to_list(ss), buf) : Bool}:
  match ss:
    case SNil{}:
      {==}
    case SCon{+hh, +tt}:
      Equal.trans(Bool, D2.bw.more(SCon{hh, tt}, buf), Bool.and(Bool.or(D2.word.char(hh), Bool.and(Char.is_eq(hh,
        ' '), Bool.and(T.date.shaped(buf), vl.d1(String.to_list(tt))))), D2.bw.more(tt, hh <> buf)),
        vl.morel(String.to_list(SCon{hh, tt}), buf),
        Equal.cong(Bool, Bool, bb => Bool.and(Bool.or(D2.word.char(hh), Bool.and(Char.is_eq(hh, ' '),
          Bool.and(T.date.shaped(buf), bb))), D2.bw.more(tt, hh <> buf)), D2.bw.digit1(tt),
          vl.d1(String.to_list(tt)), vl.d1.eq(tt)),
        Equal.cong(Bool, Bool, bb => Bool.and(Bool.or(D2.word.char(hh), Bool.and(Char.is_eq(hh, ' '),
          Bool.and(T.date.shaped(buf), vl.d1(String.to_list(tt))))), bb), D2.bw.more(tt, hh <> buf),
          vl.morel(String.to_list(tt), hh <> buf), vl.more.eq(tt, hh <> buf)))

# bw.word is vl.wordl of the text's characters
def vl.word.eq(ss: String) -> {D2.bw.word(ss) == vl.wordl(String.to_list(ss)) : Bool}:
  match ss:
    case SNil{}:
      {==}
    case SCon{+hh, +tt}:
      Equal.cong(Bool, Bool, bb => Bool.and(D2.word.first(hh), bb), D2.bw.more(tt, [hh]),
        vl.morel(String.to_list(tt), [hh]), vl.more.eq(tt, [hh]))

# characters that start a bare value are kept whatever the buffer
def vl.qs.more(
  cs: List<&2, Char>,
  +buf: List<&2, Char>,
  +hq: {vl.qs(cs) == True{} : Bool}
) -> {vl.morel(cs, buf) == True{} : Bool}:
  match cs:
    case []:
      {==}
    case +hh <> +tt:
      +hw = {Eq.and.left(D2.word.first(hh), vl.qs(tt), hq) : {D2.word.first(hh) == True{} : Bool}}
      M6.and.tt(Bool.or(D2.word.char(hh), Bool.and(Char.is_eq(hh, ' '), Bool.and(T.date.shaped(buf), vl.d1(tt)))),
        vl.morel(tt, hh <> buf),
        Equal.cong(Bool, Bool, bb => Bool.or(bb, Bool.and(Char.is_eq(hh, ' '), Bool.and(T.date.shaped(buf),
          vl.d1(tt)))), D2.word.char(hh), True{}, Eq.and.left(D2.word.char(hh), Bool.not(Bool.or(Char.is_eq(hh,
          '['), Char.is_eq(hh, '{'))), hw)),
        vl.qs.more(tt, hh <> buf, Eq.and.right(D2.word.first(hh), vl.qs(tt), hq)))

# and such a word, not empty, is a bare word
def vl.qs.word(
  +hh: Char,
  +tt: List<&2, Char>,
  +hq: {vl.qs(hh <> tt) == True{} : Bool}
) -> {vl.wordl(hh <> tt) == True{} : Bool}:
  M6.and.tt(D2.word.first(hh), vl.morel(tt, [hh]), Eq.and.left(D2.word.first(hh), vl.qs(tt), hq),
    vl.qs.more(tt, [hh], Eq.and.right(D2.word.first(hh), vl.qs(tt), hq)))

# every character of a boolean does
def vl.qs.bool(+cs: List<&2, Char>, +hh: {D2.abnf.boolean(cs) == True{} : Bool}) -> {vl.qs(cs) == True{} : Bool}:
  M4.gp.bool(zs => {vl.qs(zs) == True{} : Bool}, cs, hh, {==}, {==})

# The classifiers say a word denotes the value it reads as, as the value's
# own equality says it (sign.eq, String.eq, bit.eq, when.eq); each of those
# is the value's equality.

# two strings String.eq takes for one are one
def vl.str.eq(+aa: String, +bb: String, hh: {String.eq(aa, bb) == True{} : Bool}) -> {aa == bb : String}:
  M3.str.eq.true(aa, bb, Equal.trans(Bool, T.str.eq(aa, bb), String.eq(aa, bb), True{}, M5.str.eq.agree(aa, bb), hh))

# The documents of one pair a word matching a rule parses to: the key brings
# the scanner to the value state (kv.key2), the lift reads the word, and the
# rest closes the document.

# the value state inside an inline table after `{v = `
def vl.kfi(+kk: String) -> D3.Vf:
  D3.Vf{"", [], [], [], ["v"], T.LTop{}, T.QBasic{}, [T.CInl{[], [kk], []}], 0, 0, False{}}

# a scalar placed as a root pair's value, then a newline, is the document of the pair
def vl.doc.v(
  vv: T.Val,
  +kk: String,
  sc: {M2.vl.sc(T.GotVal{vv}) == True{} : Bool}
) -> {T.doc.read("\n", T.MScan{M2.vl.vt(M2.vl.kf(kk), vv)}) == T.Doc{"", [T.VPair{kk, vv}]} : T.Doc}:
  match vv:
    case T.VStr{tx}:
      Eq.bit.absurd(&2, {T.doc.read("\n", T.MScan{M2.vl.vt(M2.vl.kf(kk), T.VStr{tx})}) == T.Doc{"", [T.VPair{kk,
          T.VStr{tx}}]}
          : T.Doc}, sc)
    case T.VSpan{src, nn}:
      Eq.bit.absurd(&2, {T.doc.read("\n", T.MScan{M2.vl.vt(M2.vl.kf(kk), T.VSpan{src, nn})}) == T.Doc{"", [T.VPair{kk,
          T.VSpan{src, nn}}]} : T.Doc}, sc)
    case T.VInt{sg, ds}:
      {==}
    case T.VFlo{sg, tx}:
      {==}
    case T.VBool{bt}:
      {==}
    case T.VWhen{ww}:
      {==}
    case T.VArr{it}:
      Eq.bit.absurd(&2, {T.doc.read("\n", T.MScan{M2.vl.vt(M2.vl.kf(kk), T.VArr{it})}) == T.Doc{"", [T.VPair{kk,
          T.VArr{it}}]}
          : T.Doc}, sc)
    case T.VInl{rs}:
      Eq.bit.absurd(&2, {T.doc.read("\n", T.MScan{M2.vl.vt(M2.vl.kf(kk), T.VInl{rs})}) == T.Doc{"", [T.VPair{kk,
          T.VInl{rs}}]}
          : T.Doc}, sc)
    case T.VHead{pp, rs}:
      Eq.bit.absurd(&2, {T.doc.read("\n", T.MScan{M2.vl.vt(M2.vl.kf(kk), T.VHead{pp, rs})}) == T.Doc{"", [T.VPair{kk,
          T.VHead{pp, rs}}]} : T.Doc}, sc)
    case T.VAot{pp, rs}:
      Eq.bit.absurd(&2, {T.doc.read("\n", T.MScan{M2.vl.vt(M2.vl.kf(kk), T.VAot{pp, rs})}) == T.Doc{"", [T.VPair{kk,
          T.VAot{pp, rs}}]} : T.Doc}, sc)
    case T.VAots{pp, es}:
      Eq.bit.absurd(&2, {T.doc.read("\n", T.MScan{M2.vl.vt(M2.vl.kf(kk), T.VAots{pp, es})}) == T.Doc{"", [T.VPair{kk,
          T.VAots{pp, es}}]} : T.Doc}, sc)
    case T.VPair{nm, pv}:
      Eq.bit.absurd(&2, {T.doc.read("\n", T.MScan{M2.vl.vt(M2.vl.kf(kk), T.VPair{nm, pv})}) == T.Doc{"", [T.VPair{kk,
          T.VPair{nm, pv}}]} : T.Doc}, sc)

# a scalar placed as an inline table's only value, then `}` and a newline, is the document of the pair
def vl.doc.i(
  vv: T.Val,
  +kk: String,
  sc: {M2.vl.sc(T.GotVal{vv}) == True{} : Bool}
) -> {T.doc.read("}\n", T.MScan{M2.vl.vt(vl.kfi(kk), vv)}) == T.Doc{"", [T.VPair{kk, T.VInl{[T.VPair{"v", vv}]}}]} :
    T.Doc}:
  match vv:
    case T.VStr{tx}:
      Eq.bit.absurd(&2, {T.doc.read("}\n", T.MScan{M2.vl.vt(vl.kfi(kk), T.VStr{tx})}) == T.Doc{"", [T.VPair{kk,
          T.VInl{[T.VPair{"v", T.VStr{tx}}]}}]} : T.Doc}, sc)
    case T.VSpan{src, nn}:
      Eq.bit.absurd(&2, {T.doc.read("}\n", T.MScan{M2.vl.vt(vl.kfi(kk), T.VSpan{src, nn})}) == T.Doc{"", [T.VPair{kk,
          T.VInl{[T.VPair{"v", T.VSpan{src, nn}}]}}]} : T.Doc}, sc)
    case T.VInt{sg, ds}:
      {==}
    case T.VFlo{sg, tx}:
      {==}
    case T.VBool{bt}:
      {==}
    case T.VWhen{ww}:
      {==}
    case T.VArr{it}:
      Eq.bit.absurd(&2, {T.doc.read("}\n", T.MScan{M2.vl.vt(vl.kfi(kk), T.VArr{it})}) == T.Doc{"", [T.VPair{kk,
          T.VInl{[T.VPair{"v", T.VArr{it}}]}}]} : T.Doc}, sc)
    case T.VInl{rs}:
      Eq.bit.absurd(&2, {T.doc.read("}\n", T.MScan{M2.vl.vt(vl.kfi(kk), T.VInl{rs})}) == T.Doc{"", [T.VPair{kk,
          T.VInl{[T.VPair{"v", T.VInl{rs}}]}}]} : T.Doc}, sc)
    case T.VHead{pp, rs}:
      Eq.bit.absurd(&2, {T.doc.read("}\n", T.MScan{M2.vl.vt(vl.kfi(kk), T.VHead{pp, rs})}) == T.Doc{"", [T.VPair{kk,
          T.VInl{[T.VPair{"v", T.VHead{pp, rs}}]}}]} : T.Doc}, sc)
    case T.VAot{pp, rs}:
      Eq.bit.absurd(&2, {T.doc.read("}\n", T.MScan{M2.vl.vt(vl.kfi(kk), T.VAot{pp, rs})}) == T.Doc{"", [T.VPair{kk,
          T.VInl{[T.VPair{"v", T.VAot{pp, rs}}]}}]} : T.Doc}, sc)
    case T.VAots{pp, es}:
      Eq.bit.absurd(&2, {T.doc.read("}\n", T.MScan{M2.vl.vt(vl.kfi(kk), T.VAots{pp, es})}) == T.Doc{"", [T.VPair{kk,
          T.VInl{[T.VPair{"v", T.VAots{pp, es}}]}}]} : T.Doc}, sc)
    case T.VPair{nm, pv}:
      Eq.bit.absurd(&2, {T.doc.read("}\n", T.MScan{M2.vl.vt(vl.kfi(kk), T.VPair{nm, pv})}) == T.Doc{"", [T.VPair{kk,
          T.VInl{[T.VPair{"v", T.VPair{nm, pv}}]}}]} : T.Doc}, sc)

# a word word.val reads as a scalar, after a bare key in each of the three
# positions, parses to the document of the pair
def vl.acc.v(
  kk: String,
  ek: {T.bare(kk) == True{} : Bool},
  +ww: String,
  +hw: {D2.bw.word(ww) == True{} : Bool},
  +vv: T.Val,
  +hv: {T.word.val(String.to_list(ww)) == T.GotVal{vv} : T.Got},
  +sc: {M2.vl.sc(T.GotVal{vv}) == True{} : Bool}
) -> {T.parse(D1.bw.kv(kk, ww)) == T.Doc{"", [T.VPair{kk, vv}]} : T.Doc}:
  match kk:
    case SNil{}:
      Eq.bit.absurd(&2, {T.parse(D1.bw.kv(SNil{}, ww)) == T.Doc{"", [T.VPair{SNil{}, vv}]} : T.Doc}, ek)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          Equal.trans(T.Doc, T.parse(D1.bw.kv(SCon{Chr{xx}, tt}, ww)), T.doc.read(String.append(ww, "\n"),
            T.MScan{D3.vst(M2.vl.kf(SCon{Chr{xx}, tt}), [], T.LVal{})}), T.Doc{"", [T.VPair{SCon{Chr{xx}, tt}, vv}]},
            M1.kv.key2(xx, tt, String.append(ww, "\n"), ek),
            Equal.trans(T.Doc, T.doc.read(String.append(ww, "\n"), T.MScan{D3.vst(M2.vl.kf(SCon{Chr{xx}, tt}), [],
              T.LVal{})}), T.doc.read("\n", T.MScan{M2.vl.vt(M2.vl.kf(SCon{Chr{xx}, tt}), vv)}),
              T.Doc{"", [T.VPair{SCon{Chr{xx}, tt}, vv}]}, M2.vl.lift(ww, hw, vv, hv, M2.vl.kf(SCon{Chr{xx}, tt}), "\n",
                {==}),
              vl.doc.v(vv, SCon{Chr{xx}, tt}, sc)))

# and as an inline table's only value
def vl.acc.i(
  kk: String,
  ek: {T.bare(kk) == True{} : Bool},
  +ww: String,
  +hw: {D2.bw.word(ww) == True{} : Bool},
  +vv: T.Val,
  +hv: {T.word.val(String.to_list(ww)) == T.GotVal{vv} : T.Got},
  +sc: {M2.vl.sc(T.GotVal{vv}) == True{} : Bool}
) -> {T.parse(D1.bw.kvi(kk, ww)) == T.Doc{"", [T.VPair{kk, T.VInl{[T.VPair{"v", vv}]}}]} : T.Doc}:
  match kk:
    case SNil{}:
      Eq.bit.absurd(&2, {T.parse(D1.bw.kvi(SNil{}, ww)) == T.Doc{"", [T.VPair{SNil{}, T.VInl{[T.VPair{"v", vv}]}}]}
        : T.Doc}, ek)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          Equal.trans(T.Doc, T.parse(D1.bw.kvi(SCon{Chr{xx}, tt}, ww)), T.doc.read(String.append(ww, "}\n"),
            T.MScan{D3.vst(vl.kfi(SCon{Chr{xx}, tt}), [], T.LVal{})}), T.Doc{"", [T.VPair{SCon{Chr{xx}, tt},
            T.VInl{[T.VPair{"v", vv}]}}]},
            M1.kv.key2(xx, tt, SCon{'{', SCon{'v', SCon{' ', SCon{'=', SCon{' ', String.append(ww, "}\n")}}}}}, ek),
            Equal.trans(T.Doc, T.doc.read(String.append(ww, "}\n"), T.MScan{D3.vst(vl.kfi(SCon{Chr{xx}, tt}), [],
              T.LVal{})}), T.doc.read("}\n", T.MScan{M2.vl.vt(vl.kfi(SCon{Chr{xx}, tt}), vv)}),
              T.Doc{"", [T.VPair{SCon{Chr{xx}, tt}, T.VInl{[T.VPair{"v", vv}]}}]},
              M2.vl.lift(ww, hw, vv, hv, vl.kfi(SCon{Chr{xx}, tt}), "}\n", {==}),
              vl.doc.i(vv, SCon{Chr{xx}, tt}, sc)))

# the outcome a word reads as is a scalar
def vl.sc.of(
  +cs: List<&2, Char>,
  +vv: T.Val,
  hv: {T.word.val(cs) == T.GotVal{vv} : T.Got}
) -> {M2.vl.sc(T.GotVal{vv}) == True{} : Bool}:
  Equal.trans(Bool, M2.vl.sc(T.GotVal{vv}), M2.vl.sc(T.word.val(cs)), True{}, Equal.cong(T.Got, Bool,
      gg => M2.vl.sc(gg),
    T.GotVal{vv}, T.word.val(cs), Equal.sym(T.Got, T.word.val(cs), T.GotVal{vv}, hv)), M2.vl.sc.word(cs))

# a word every character of which starts a bare value is a bare word
def vl.bw.qs(
  ww: String,
  hq: {vl.qs(String.to_list(ww)) == True{} : Bool},
  hn: {Bool.not(String.is_empty(ww)) == True{} : Bool}
) -> {D2.bw.word(ww) == True{} : Bool}:
  match ww:
    case SNil{}:
      Eq.bit.absurd(&2, {D2.bw.word(SNil{}) == True{} : Bool}, hn)
    case SCon{+hh, +tt}:
      Equal.trans(Bool, D2.bw.word(SCon{hh, tt}), vl.wordl(hh <> String.to_list(tt)), True{},
        vl.word.eq(SCon{hh, tt}), vl.qs.word(hh, String.to_list(tt), hq))

def L1.boolean_is_bare_word(w, h):
  match w:
    case SNil{}:
      Eq.bit.absurd(&2, {D2.bw.word(SNil{}) == True{} : Bool}, h)
    case SCon{+hh, +tt}:
      vl.bw.qs(SCon{hh, tt}, vl.qs.bool(hh <> String.to_list(tt), h), {==})
