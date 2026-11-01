# a refused bare word leaves the first error and the document that follows
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/BareWordRefused.bend as L1
import ../../laws/KeyNameIsItsCharacters.bend as L2
import ../../laws/ParsesExactlyTheGrammar.bend as L3
import ../../laws/defs/AbnfGrammar.bend as D1
import ../../laws/defs/BareValueGrammar.bend as D2
import ../../laws/defs/ScalarReadbackScan.bend as D3
import ./BareKeyValueScan.bend as M1
import ./BareValueScan.bend as M2
import ./BareWordReadsOn.bend as M3
import ./FailedScanStays.bend as M4
import ./FreshNamesInRows.bend as M5
import ./RefusalReasons.bend as M6

# A word word.val refuses: the step that ends it fails the scanner (st.err),
# and a failed scanner keeps its error to the end of the text (fail_stays),
# in the scan mode or after a carriage return.

# the document read from a mode has an error
def vl.Bad(+tt: String, md: T.Mode) -> Type:
  {String.is_empty(T.bad(T.doc.read(tt, md))) == False{} : Bool}

# and so does one read from a mode equal to it
def vl.btr(
  +tt: String,
  m1: T.Mode,
  m2: T.Mode,
  ee: {m1 == m2 : T.Mode},
  hh: vl.Bad(tt, m2)
) -> vl.Bad(tt, m1):
  Equal.trans(Bool, String.is_empty(T.bad(T.doc.read(tt, m1))), String.is_empty(T.bad(T.doc.read(tt, m2))), False{},
    Equal.cong(T.Mode, Bool, md => String.is_empty(T.bad(T.doc.read(tt, md))), m1, m2, ee), hh)

# the first error is kept, and a reason that is not empty leaves one
def vl.ef.go(
  em: Bool,
  +bad: String,
  +why: String,
  ee: {String.is_empty(bad) == em : Bool},
  hw: {String.is_empty(why) == False{} : Bool}
) -> {String.is_empty(T.err.first.go(em, bad, why)) == False{} : Bool}:
  match em:
    case True{}:
      hw
    case False{}:
      ee

# whatever error there was
def vl.ef(
  +bad: String,
  +why: String,
  hw: {String.is_empty(why) == False{} : Bool}
) -> {String.is_empty(T.err.first(bad, why)) == False{} : Bool}:
  vl.ef.go(String.is_empty(bad), bad, why, {==}, hw)

# a failed scanner leaves an error, whatever follows
def vl.sink(
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +hb: {String.is_empty(bd) == False{} : Bool},
  +tt: String
) -> vl.Bad(tt, T.MScan{T.St{bd, rw, hs, he, ps, [], T.LSink{}, bk, qk, sk, T.HNone{}, un, lf, ab, False{}}}):
  Equal.trans(Bool, String.is_empty(T.bad(T.doc.read(tt, T.MScan{T.St{bd, rw, hs, he, ps, [], T.LSink{}, bk, qk, sk,
    T.HNone{}, un, lf, ab, False{}}}))), String.is_empty(bd), False{},
    Equal.cong(String, Bool, ss => String.is_empty(ss), T.bad(T.doc.read(tt, T.MScan{T.St{bd, rw, hs, he, ps, [],
      T.LSink{}, bk, qk, sk, T.HNone{}, un, lf, ab, False{}}})), bd,
      L3.fail_stays(bd, rw, hs, he, ps, [], bk, qk, sk, un, lf, ab, False{}, hb, tt)), hb)

# the scanner once a word is refused for the reason why
def vl.err(+fx: D3.Vf, why: String) -> T.St:
  T.read.once2(T.st.err(D3.vst(fx, [], T.LBare{}), why))

# it leaves an error in the scan mode
def vl.bs(
  +fx: D3.Vf,
  +why: String,
  hw: {String.is_empty(why) == False{} : Bool},
  +tt: String
) -> vl.Bad(tt, T.MScan{vl.err(fx, why)}):
  match fx:
    case D3.Vf{+bad, +rows, +heads, +here, +parts, +back, +qkind, +stack, +uni, +left, +arrtab}:
      vl.sink(T.err.first(bad, why), rows, heads, here, parts, back, qkind, stack, uni, left, arrtab, vl.ef(bad, why,
        hw), tt)

# a character after a carriage return, from a failed scanner
def vl.bcr.at(
  lf: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf2: U32,
  +ab: Bool,
  +hb: {String.is_empty(bd) == False{} : Bool},
  +cc: Char,
  +tt: String
) -> vl.Bad(tt, T.doc.cr(lf, T.St{bd, rw, hs, he, ps, [], T.LSink{}, bk, qk, sk, T.HNone{}, un, lf2, ab, False{}}, cc)):
  match lf:
    case True{}:
      vl.sink(bd, rw, hs, he, ps, bk, qk, sk, un, lf2, ab, hb, tt)
    case False{}:
      vl.sink(T.err.first(bd, "carriage return without line feed"), rw, hs, he, ps, bk, qk, sk, un, lf2, ab,
        vl.ef(bd, "carriage return without line feed", {==}), tt)

# it leaves an error after a carriage return too
def vl.bcr(
  +fx: D3.Vf,
  +why: String,
  hw: {String.is_empty(why) == False{} : Bool},
  tt: String
) -> vl.Bad(tt, T.MCr{vl.err(fx, why)}):
  match fx:
    case D3.Vf{+bad, +rows, +heads, +here, +parts, +back, +qkind, +stack, +uni, +left, +arrtab}:
      match tt:
        case SNil{}:
          vl.sink(T.err.first(T.err.first(bad, why), "carriage return without line feed"), rows, heads, here, parts,
            back, qkind, stack, uni, left, arrtab, vl.ef(T.err.first(bad, why), "carriage return without line feed",
            {==}), SNil{})
        case SCon{+hh, +t2}:
          vl.bcr.at(Char.is_eq(hh, '\n'), T.err.first(bad, why), rows, heads, here, parts, back, qkind, stack, uni,
            left, arrtab, vl.ef(bad, why, hw), hh, t2)

# and in a mode a quote may open
def vl.bwrap(
  +fx: D3.Vf,
  +why: String,
  hw: {String.is_empty(why) == False{} : Bool},
  +tt: String
) -> vl.Bad(tt, T.doc.wrap(vl.err(fx, why))):
  match fx:
    case D3.Vf{+bad, +rows, +heads, +here, +parts, +back, +qkind, +stack, +uni, +left, +arrtab}:
      vl.sink(T.err.first(bad, why), rows, heads, here, parts, back, qkind, stack, uni, left, arrtab, vl.ef(bad, why,
        hw), tt)

# the step on any character, from a state the fast step fails, leaves an
# error in whatever mode it opens
def vl.bq(
  dq: Bool,
  sq: Bool,
  cr: Bool,
  st: T.St,
  +cc: Char,
  +fx: D3.Vf,
  +why: String,
  +hw: {String.is_empty(why) == False{} : Bool},
  +tt: String,
  +ee: {T.read.fast(st, cc) == vl.err(fx, why) : T.St}
) -> vl.Bad(tt, T.doc.scan.q(dq, sq, cr, st, cc)):
  match dq:
    case True{}:
      vl.btr(tt, T.doc.wrap(T.read.fast(st, cc)), T.doc.wrap(vl.err(fx, why)), Equal.cong(T.St, T.Mode,
        ss => T.doc.wrap(ss), T.read.fast(st, cc), vl.err(fx, why), ee), vl.bwrap(fx, why, hw, tt))
    case False{}:
      match sq:
        case True{}:
          vl.btr(tt, T.doc.wrap(T.read.fast(st, cc)), T.doc.wrap(vl.err(fx, why)), Equal.cong(T.St, T.Mode,
            ss => T.doc.wrap(ss), T.read.fast(st, cc), vl.err(fx, why), ee), vl.bwrap(fx, why, hw, tt))
        case False{}:
          match cr:
            case True{}:
              vl.btr(tt, T.MCr{T.read.fast(st, cc)}, T.MCr{vl.err(fx, why)}, Equal.cong(T.St, T.Mode,
                ss => T.MCr{ss}, T.read.fast(st, cc), vl.err(fx, why), ee), vl.bcr(fx, why, hw, tt))
            case False{}:
              vl.btr(tt, T.MScan{T.read.fast(st, cc)}, T.MScan{vl.err(fx, why)}, Equal.cong(T.St, T.Mode,
                ss => T.MScan{ss}, T.read.fast(st, cc), vl.err(fx, why), ee), vl.bs(fx, why, hw, tt))

# a character that ends a refused word fails the step
def vl.bacc(
  +fx: D3.Vf,
  +bb: List<&2, Char>,
  +why: String,
  +cc: Char,
  +hold: Bool,
  hv: {T.word.val(List.reverse(&2, Char, bb)) == T.GotBad{why} : T.Got},
  rf: M3.vl.Rf(fx, bb, cc, hold)
) -> {T.read.fast(D3.vst(fx, bb, T.LBare{}), cc) == vl.err(fx, why) : T.St}:
  Equal.trans(T.St, T.read.fast(D3.vst(fx, bb, T.LBare{}), cc), T.read.once2(T.bare.got(T.word.val(List.reverse(&2,
    Char, bb)), D3.vst(fx, [], T.LBare{}), cc, hold)), vl.err(fx, why), rf,
    Equal.cong(T.Got, T.St, gg => T.read.once2(T.bare.got(gg, D3.vst(fx, [], T.LBare{}), cc, hold)),
      T.word.val(List.reverse(&2, Char, bb)), T.GotBad{why}, hv))

# a character after a date's space that is no digit fails the step
def vl.bdacc(
  +fx: D3.Vf,
  +bb: List<&2, Char>,
  +why: String,
  +cc: Char,
  hv: {T.word.val(List.reverse(&2, Char, bb)) == T.GotBad{why} : T.Got},
  hd: {Char.is_digit(cc) == False{} : Bool}
) -> {T.read.fast(D3.vst(fx, bb, T.LDate{}), cc) == vl.err(fx, why) : T.St}:
  match fx:
    case D3.Vf{+bad, +rows, +heads, +here, +parts, +back, +qkind, +stack, +uni, +left, +arrtab}:
      Equal.trans(T.St, T.read.once2(T.lex.date.go(Char.is_digit(cc), T.St{bad, rows, heads, here, parts, bb,
        T.LDate{}, back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}}, cc)),
        T.read.once2(T.bare.got(T.word.val(List.reverse(&2, Char, bb)), T.St{bad, rows, heads, here, parts, [],
          T.LDate{}, back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}}, cc, True{})),
        vl.err(D3.Vf{bad, rows, heads, here, parts, back, qkind, stack, uni, left, arrtab}, why),
        Equal.cong(Bool, T.St, xx => T.read.once2(T.lex.date.go(xx, T.St{bad, rows, heads, here, parts, bb, T.LDate{},
          back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}}, cc)), Char.is_digit(cc), False{}, hd),
        Equal.cong(T.Got, T.St, gg => T.read.once2(T.bare.got(gg, T.St{bad, rows, heads, here, parts, [], T.LDate{},
          back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}}, cc, True{})),
          T.word.val(List.reverse(&2, Char, bb)), T.GotBad{why}, hv))

# the document from a refused word's buffer has an error
def vl.Bf(+fx: D3.Vf, +bb: List<&2, Char>, rest: String) -> Type:
  vl.Bad(rest, T.MScan{D3.vst(fx, bb, T.LBare{})})

# the end of the text after a refused word
def vl.bnil.b(
  +fx: D3.Vf,
  +bb: List<&2, Char>,
  +why: String,
  hw: {String.is_empty(why) == False{} : Bool},
  hv: {T.word.val(List.reverse(&2, Char, bb)) == T.GotBad{why} : T.Got}
) -> vl.Bad(SNil{}, T.MScan{D3.vst(fx, bb, T.LBare{})}):
  match fx:
    case D3.Vf{+bad, +rows, +heads, +here, +parts, +back, +qkind, +stack, +uni, +left, +arrtab}:
      Equal.trans(Bool, String.is_empty(T.bad(T.read.fin2(T.bare.got(T.word.val(List.reverse(&2, Char, bb)),
        T.St{bad, rows, heads, here, parts, [], T.LBare{}, back, qkind, stack, T.HNone{}, uni, left, arrtab,
        False{}}, ' ', False{})))), String.is_empty(T.bad(T.read.fin2(T.bare.got(T.GotBad{why}, T.St{bad, rows,
        heads, here, parts, [], T.LBare{}, back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}}, ' ',
        False{})))), False{},
        Equal.cong(T.Got, Bool, gg => String.is_empty(T.bad(T.read.fin2(T.bare.got(gg, T.St{bad, rows, heads, here,
          parts, [], T.LBare{}, back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}}, ' ', False{})))),
          T.word.val(List.reverse(&2, Char, bb)), T.GotBad{why}, hv),
        vl.bs(D3.Vf{bad, rows, heads, here, parts, back, qkind, stack, uni, left, arrtab}, why, hw, SNil{}))

# the end of the text after a refused word's date space
def vl.bnil.d(
  +fx: D3.Vf,
  +bb: List<&2, Char>,
  +why: String,
  hw: {String.is_empty(why) == False{} : Bool},
  hv: {T.word.val(List.reverse(&2, Char, bb)) == T.GotBad{why} : T.Got}
) -> vl.Bad(SNil{}, T.MScan{D3.vst(fx, bb, T.LDate{})}):
  match fx:
    case D3.Vf{+bad, +rows, +heads, +here, +parts, +back, +qkind, +stack, +uni, +left, +arrtab}:
      Equal.trans(Bool, String.is_empty(T.bad(T.read.fin2(T.bare.got(T.word.val(List.reverse(&2, Char, bb)),
        T.St{bad, rows, heads, here, parts, [], T.LDate{}, back, qkind, stack, T.HNone{}, uni, left, arrtab,
        False{}}, ' ', False{})))), String.is_empty(T.bad(T.read.fin2(T.bare.got(T.GotBad{why}, T.St{bad, rows,
        heads, here, parts, [], T.LDate{}, back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}}, ' ',
        False{})))), False{},
        Equal.cong(T.Got, Bool, gg => String.is_empty(T.bad(T.read.fin2(T.bare.got(gg, T.St{bad, rows, heads, here,
          parts, [], T.LDate{}, back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}}, ' ', False{})))),
          T.word.val(List.reverse(&2, Char, bb)), T.GotBad{why}, hv),
        vl.bs(D3.Vf{bad, rows, heads, here, parts, back, qkind, stack, uni, left, arrtab}, why, hw, SNil{}))

# the rest after a refused word's date space has an error
def vl.bdate.rest(
  +fx: D3.Vf,
  +bb: List<&2, Char>,
  +why: String,
  tt: String,
  +hw: {String.is_empty(why) == False{} : Bool},
  +hv: {T.word.val(List.reverse(&2, Char, bb)) == T.GotBad{why} : T.Got},
  hd: {D2.bw.digit1(tt) == False{} : Bool}
) -> vl.Bad(tt, T.MScan{D3.vst(fx, bb, T.LDate{})}):
  match tt:
    case SNil{}:
      vl.bnil.d(fx, bb, why, hw, hv)
    case SCon{+c2, +t2}:
      vl.bq(Char.is_eq(c2, '"'), Char.is_eq(c2, '\''), U32.is_eq(Char.to_u32(c2), 13), D3.vst(fx, bb, T.LDate{}), c2,
        fx, why, hw, t2, vl.bdacc(fx, bb, why, c2, hv, hd))

# a space after a refused word: the date's, or one that ends it at once
def vl.bfin.sp(
  ds: Bool,
  +fx: D3.Vf,
  +bb: List<&2, Char>,
  +why: String,
  +tt: String,
  +hw: {String.is_empty(why) == False{} : Bool},
  +hv: {T.word.val(List.reverse(&2, Char, bb)) == T.GotBad{why} : T.Got},
  +es: {T.date.shaped(bb) == ds : Bool},
  hn: {Bool.not(Bool.and(T.date.shaped(bb), D2.bw.digit1(tt))) == True{} : Bool}
) -> vl.Bf(fx, bb, SCon{' ', tt}):
  match ds:
    case True{}:
      vl.btr(tt, T.doc.scan(D3.vst(fx, bb, T.LBare{}), ' '), T.MScan{D3.vst(fx, bb, T.LDate{})}, M3.vl.sp(fx, bb, es),
        vl.bdate.rest(fx, bb, why, tt, hw, hv, M3.vl.nd(T.date.shaped(bb), D2.bw.digit1(tt), es, hn)))
    case False{}:
      vl.btr(tt, T.MScan{T.read.fast(D3.vst(fx, bb, T.LBare{}), ' ')}, T.MScan{vl.err(fx, why)},
        Equal.cong(T.St, T.Mode, ss => T.MScan{ss}, T.read.fast(D3.vst(fx, bb, T.LBare{}), ' '), vl.err(fx, why),
        vl.bacc(fx, bb, why, ' ', False{}, hv, M3.vl.rf.sp(fx, bb, es))), vl.bs(fx, why, hw, tt))

# a character other than a space that ends a refused word
def vl.bstp(
  +fx: D3.Vf,
  +bb: List<&2, Char>,
  +why: String,
  +cc: Char,
  +tt: String,
  hw: {String.is_empty(why) == False{} : Bool},
  ee: {T.read.fast(D3.vst(fx, bb, T.LBare{}), cc) == vl.err(fx, why) : T.St}
) -> vl.Bad(tt, T.MScan{T.read.fast(D3.vst(fx, bb, T.LBare{}), cc)}):
  vl.btr(tt, T.MScan{T.read.fast(D3.vst(fx, bb, T.LBare{}), cc)}, T.MScan{vl.err(fx, why)}, Equal.cong(T.St, T.Mode,
    ss => T.MScan{ss}, T.read.fast(D3.vst(fx, bb, T.LBare{}), cc), vl.err(fx, why), ee), vl.bs(fx, why, hw, tt))

# the claim for a refused word's buffer and one ending character
def vl.Bp(+fx: D3.Vf, +bb: List<&2, Char>, +tt: String, +cc: Char) -> Type:
  {Bool.not(D2.bw.dsp(cc, bb, tt)) == True{} : Bool} -> vl.Bf(fx, bb, SCon{cc, tt})

# a text that ends a refused word leaves an error
def vl.bfin(
  +fx: D3.Vf,
  +bb: List<&2, Char>,
  +why: String,
  rest: String,
  +hw: {String.is_empty(why) == False{} : Bool},
  +hv: {T.word.val(List.reverse(&2, Char, bb)) == T.GotBad{why} : T.Got},
  +ee: {D2.bw.end(bb, rest) == True{} : Bool}
) -> vl.Bf(fx, bb, rest):
  match rest:
    case SNil{}:
      vl.bnil.b(fx, bb, why, hw, hv)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          M3.vl.delim(ch => vl.Bp(fx, bb, tt, ch), xx, Eq.and.left(T.ch.delim(Chr{xx}),
            Bool.not(D2.bw.dsp(Chr{xx}, bb, tt)), ee),
            hn => vl.bfin.sp(T.date.shaped(bb), fx, bb, why, tt, hw, hv, {==}, hn),
            _hn => vl.bstp(fx, bb, why, Chr{9}, tt, hw, vl.bacc(fx, bb, why, Chr{9}, False{}, hv, M3.vl.rf.tab(fx,
                bb))),
            _hn => vl.bstp(fx, bb, why, '\n', tt, hw, vl.bacc(fx, bb, why, '\n', D3.vf.inl(fx), hv, M3.vl.rf.lf(fx,
              bb))),
            _hn => vl.btr(tt, T.MCr{T.read.fast(D3.vst(fx, bb, T.LBare{}), Chr{13})}, T.MCr{vl.err(fx, why)},
              Equal.cong(T.St, T.Mode, ss => T.MCr{ss}, T.read.fast(D3.vst(fx, bb, T.LBare{}), Chr{13}),
              vl.err(fx, why), vl.bacc(fx, bb, why, Chr{13}, D3.vf.inl(fx), hv, M3.vl.rf.cr(fx, bb))),
              vl.bcr(fx, why, hw, tt)),
            _hn => vl.bstp(fx, bb, why, '#', tt, hw, vl.bacc(fx, bb, why, '#', True{}, hv, M3.vl.rf.hash(fx, bb))),
            _hn => vl.bstp(fx, bb, why, ',', tt, hw, vl.bacc(fx, bb, why, ',', True{}, hv, M3.vl.rf.comma(fx, bb))),
            _hn => vl.bstp(fx, bb, why, ']', tt, hw, vl.bacc(fx, bb, why, ']', True{}, hv, M3.vl.rf.rb(fx, bb))),
            _hn => vl.bstp(fx, bb, why, '}', tt, hw, vl.bacc(fx, bb, why, '}', True{}, hv, M3.vl.rf.rc(fx, bb))))(
              Eq.and.right(T.ch.delim(Chr{xx}), Bool.not(D2.bw.dsp(Chr{xx}, bb, tt)), ee))

# a refused word's reason is not empty
def vl.why(
  +cs: List<&2, Char>,
  +why: String,
  hv: {T.word.val(cs) == T.GotBad{why} : T.Got}
) -> {String.is_empty(why) == False{} : Bool}:
  Eq.not.true(String.is_empty(why), Equal.trans(Bool, L2.k3.why(T.GotBad{why}), L2.k3.why(T.word.val(cs)), True{},
    Equal.cong(T.Got, Bool, gg => L2.k3.why(gg), T.GotBad{why}, T.word.val(cs), Equal.sym(T.Got, T.word.val(cs),
    T.GotBad{why}, hv)), L2.bare_word_refusal_says_why(cs)))

# a bare word word.val refuses, read from a value state, then a text that
# ends it: the document has an error
def vl.blift(
  ww: String,
  +hw: {D2.bw.word(ww) == True{} : Bool},
  +why: String,
  +hv: {T.word.val(String.to_list(ww)) == T.GotBad{why} : T.Got},
  +fx: D3.Vf,
  +rest: String,
  ee: {D2.bw.end(D2.bw.rev(ww, []), rest) == True{} : Bool}
) -> vl.Bad(String.append(ww, rest), T.MScan{D3.vst(fx, [], T.LVal{})}):
  match ww:
    case SNil{}:
      Eq.bit.absurd(&1, vl.Bad(String.append(SNil{}, rest), T.MScan{D3.vst(fx, [], T.LVal{})}), hw)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          +bb = {M5.rev.onto(tt, [Chr{xx}]) : List<&2, Char>}
          +ho = {Equal.trans(T.Got, T.word.val(List.reverse(&2, Char, bb)), T.word.val(String.to_list(SCon{Chr{xx},
            tt})), T.GotBad{why}, Equal.cong(List<&2, Char>, T.Got, cs => T.word.val(cs), List.reverse(&2, Char, bb),
            String.to_list(SCon{Chr{xx}, tt}), M5.wd.order(Chr{xx}, tt)), hv)
            : {T.word.val(List.reverse(&2, Char, bb)) == T.GotBad{why} : T.Got}}
          +he = {Equal.trans(Bool, D2.bw.end(bb, rest), D2.bw.end(D2.bw.rev(tt, [Chr{xx}]), rest), True{},
            Equal.cong(List<&2, Char>, Bool, ys => D2.bw.end(ys, rest), bb, D2.bw.rev(tt, [Chr{xx}]),
            Equal.sym(List<&2, Char>, D2.bw.rev(tt, [Chr{xx}]), bb, M3.vl.rev(tt, [Chr{xx}]))), ee)
            : {D2.bw.end(bb, rest) == True{} : Bool}}
          vl.btr(String.append(tt, rest), T.doc.scan(D3.vst(fx, [], T.LVal{}), Chr{xx}), T.MScan{D3.vst(fx,
            [Chr{xx}], T.LBare{})}, M2.wd.first(fx, xx, Eq.and.left(D2.word.first(Chr{xx}), D2.bw.more(tt, [Chr{xx}]),
            hw)),
            Equal.trans(Bool, String.is_empty(T.bad(T.doc.read(String.append(tt, rest), T.MScan{D3.vst(fx, [Chr{xx}],
              T.LBare{})}))), String.is_empty(T.bad(T.doc.read(rest, T.MScan{D3.vst(fx, bb, T.LBare{})}))), False{},
              Equal.cong(T.Doc, Bool, dd => String.is_empty(T.bad(dd)), T.doc.read(String.append(tt, rest),
                T.MScan{D3.vst(fx, [Chr{xx}], T.LBare{})}), T.doc.read(rest, T.MScan{D3.vst(fx, bb, T.LBare{})}),
                M3.vl.run(tt, rest, fx, [Chr{xx}], Eq.and.right(D2.word.first(Chr{xx}), D2.bw.more(tt, [Chr{xx}]),
                hw))),
              vl.bfin(fx, bb, why, rest, vl.why(String.to_list(SCon{Chr{xx}, tt}), why, hv), ho, he)))

def L1.bare_word_refused(w, hw, why, hv, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, ee):
  vl.blift(w, hw, why, hv, D3.Vf{"", rw, hs, he, ps, bk, qk, sk, un, lf, ab}, rest, ee)

# The document of one pair, k = w and a newline: a bare key brings the
# scanner to the value state (kv.key2), the lift reads the word, and the
# newline ends the document of the pair, or the document has an error.

# a bare word's outcome with the reason of a refusal dropped, as bw.got reads
# a document with an error
def vl.norm(gg: T.Got) -> T.Got:
  match gg:
    case T.GotVal{vv}:
      T.GotVal{vv}
    case T.GotBad{_why}:
      T.GotBad{""}

# a scalar placed at the root, then a newline, is the document of the pair
def vl.pv.v(
  vv: T.Val,
  +kk: String,
  sc: {M3.vl.sc(T.GotVal{vv}) == True{} : Bool}
) -> {D2.bw.got(T.doc.read("\n", T.MScan{M3.vl.vt(M3.vl.kf(kk), vv)}), kk) == T.GotVal{vv} : T.Got}:
  match vv:
    case T.VInt{+sg, +ds}:
      Equal.cong(Bool, T.Got, bb => D2.bw.got.one(True{}, bb, T.VInt{sg, ds}), String.eq(kk, kk), True{},
        Eq.string_eq_self(kk))
    case T.VFlo{+sg, +tx}:
      Equal.cong(Bool, T.Got, bb => D2.bw.got.one(True{}, bb, T.VFlo{sg, tx}), String.eq(kk, kk), True{},
        Eq.string_eq_self(kk))
    case T.VBool{+bt}:
      Equal.cong(Bool, T.Got, bb => D2.bw.got.one(True{}, bb, T.VBool{bt}), String.eq(kk, kk), True{},
        Eq.string_eq_self(kk))
    case T.VWhen{+ww}:
      Equal.cong(Bool, T.Got, bb => D2.bw.got.one(True{}, bb, T.VWhen{ww}), String.eq(kk, kk), True{},
        Eq.string_eq_self(kk))
    case T.VStr{tx}:
      Eq.bit.absurd(&2, {D2.bw.got(T.doc.read("\n", T.MScan{M3.vl.vt(M3.vl.kf(kk), T.VStr{tx})}), kk)
        == T.GotVal{T.VStr{tx}} : T.Got}, sc)
    case T.VSpan{src, nn}:
      Eq.bit.absurd(&2, {D2.bw.got(T.doc.read("\n", T.MScan{M3.vl.vt(M3.vl.kf(kk), T.VSpan{src, nn})}), kk)
        == T.GotVal{T.VSpan{src, nn}} : T.Got}, sc)
    case T.VArr{it}:
      Eq.bit.absurd(&2, {D2.bw.got(T.doc.read("\n", T.MScan{M3.vl.vt(M3.vl.kf(kk), T.VArr{it})}), kk)
        == T.GotVal{T.VArr{it}} : T.Got}, sc)
    case T.VInl{rs}:
      Eq.bit.absurd(&2, {D2.bw.got(T.doc.read("\n", T.MScan{M3.vl.vt(M3.vl.kf(kk), T.VInl{rs})}), kk)
        == T.GotVal{T.VInl{rs}} : T.Got}, sc)
    case T.VHead{pp, rs}:
      Eq.bit.absurd(&2, {D2.bw.got(T.doc.read("\n", T.MScan{M3.vl.vt(M3.vl.kf(kk), T.VHead{pp, rs})}), kk)
        == T.GotVal{T.VHead{pp, rs}} : T.Got}, sc)
    case T.VAot{pp, rs}:
      Eq.bit.absurd(&2, {D2.bw.got(T.doc.read("\n", T.MScan{M3.vl.vt(M3.vl.kf(kk), T.VAot{pp, rs})}), kk)
        == T.GotVal{T.VAot{pp, rs}} : T.Got}, sc)
    case T.VAots{pp, es}:
      Eq.bit.absurd(&2, {D2.bw.got(T.doc.read("\n", T.MScan{M3.vl.vt(M3.vl.kf(kk), T.VAots{pp, es})}), kk)
        == T.GotVal{T.VAots{pp, es}} : T.Got}, sc)
    case T.VPair{nm, pv}:
      Eq.bit.absurd(&2, {D2.bw.got(T.doc.read("\n", T.MScan{M3.vl.vt(M3.vl.kf(kk), T.VPair{nm, pv})}), kk)
        == T.GotVal{T.VPair{nm, pv}} : T.Got}, sc)

# a document with an error is read as no value
def vl.got.bad(
  dd: T.Doc,
  +kk: String,
  hb: {String.is_empty(T.bad(dd)) == False{} : Bool}
) -> {D2.bw.got(dd, kk) == T.GotBad{""} : T.Got}:
  match dd:
    case T.Doc{+bad, rows}:
      Equal.cong(Bool, T.Got, bb => D2.bw.got.go(bb, rows, kk), String.is_empty(bad), False{}, hb)

# the pair's document, from the value state, by the word's outcome
def vl.pv.at(
  gg: T.Got,
  +ww: String,
  +kk: String,
  +hw: {D2.bw.word(ww) == True{} : Bool},
  eg: {T.word.val(String.to_list(ww)) == gg : T.Got},
  sc: {M3.vl.sc(gg) == True{} : Bool}
) -> {D2.bw.got(T.doc.read(String.append(ww, "\n"), T.MScan{D3.vst(M3.vl.kf(kk), [], T.LVal{})}), kk) == vl.norm(gg)
  : T.Got}:
  match gg:
    case T.GotVal{+vv}:
      Equal.trans(T.Got, D2.bw.got(T.doc.read(String.append(ww, "\n"), T.MScan{D3.vst(M3.vl.kf(kk), [], T.LVal{})}),
        kk), D2.bw.got(T.doc.read("\n", T.MScan{M3.vl.vt(M3.vl.kf(kk), vv)}), kk), T.GotVal{vv},
        Equal.cong(T.Doc, T.Got, dd => D2.bw.got(dd, kk), T.doc.read(String.append(ww, "\n"),
          T.MScan{D3.vst(M3.vl.kf(kk), [], T.LVal{})}), T.doc.read("\n", T.MScan{M3.vl.vt(M3.vl.kf(kk), vv)}),
          M3.vl.lift(ww, hw, vv, eg, M3.vl.kf(kk), "\n", {==})),
        vl.pv.v(vv, kk, sc))
    case T.GotBad{+why}:
      vl.got.bad(T.doc.read(String.append(ww, "\n"), T.MScan{D3.vst(M3.vl.kf(kk), [], T.LVal{})}), kk,
        vl.blift(ww, hw, why, eg, M3.vl.kf(kk), "\n", {==}))

# a key, " = ", a bare word and a newline: the document reads as word.val
# reads the word, with a refusal's reason dropped
def vl.pv(
  kk: String,
  ek: {T.bare(kk) == True{} : Bool},
  +ww: String,
  +hw: {D2.bw.word(ww) == True{} : Bool}
) -> {D2.bw.got(T.parse(D1.bw.kv(kk, ww)), kk) == vl.norm(T.word.val(String.to_list(ww))) : T.Got}:
  match kk:
    case SNil{}:
      Eq.bit.absurd(&2, {D2.bw.got(T.parse(D1.bw.kv(SNil{}, ww)), SNil{}) == vl.norm(T.word.val(String.to_list(ww)))
        : T.Got}, ek)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          Equal.trans(T.Got, D2.bw.got(T.parse(D1.bw.kv(SCon{Chr{xx}, tt}, ww)), SCon{Chr{xx}, tt}),
            D2.bw.got(T.doc.read(String.append(ww, "\n"), T.MScan{D3.vst(M3.vl.kf(SCon{Chr{xx}, tt}), [],
              T.LVal{})}), SCon{Chr{xx}, tt}), vl.norm(T.word.val(String.to_list(ww))),
            Equal.cong(T.Doc, T.Got, dd => D2.bw.got(dd, SCon{Chr{xx}, tt}), T.parse(D1.bw.kv(SCon{Chr{xx}, tt},
              ww)), T.doc.read(String.append(ww, "\n"), T.MScan{D3.vst(M3.vl.kf(SCon{Chr{xx}, tt}), [], T.LVal{})}),
              M1.kv.key2(xx, tt, String.append(ww, "\n"), ek)),
            vl.pv.at(T.word.val(String.to_list(ww)), ww, SCon{Chr{xx}, tt}, hw, {==},
              M3.vl.sc.word(String.to_list(ww))))
