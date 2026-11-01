# a bare word read as an array item reads on and ends at the right delimiter
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/BareWordReadsOn.bend as L1
import ../../laws/BareWordReadsOnInArray.bend as L2
import ../../laws/defs/AbnfGrammar.bend as D1
import ../../laws/defs/BareValueGrammar.bend as D2
import ../../laws/defs/ScalarReadbackScan.bend as D3
import ./BareKeyValueScan.bend as M1
import ./BareValueScan.bend as M2
import ./BareWordReadsOn.bend as M3
import ./ReorderedTableNames.bend as M4

# An array's item. In LArr the word's first character is held and read again
# in LVal, with back at LVal: the word is read from that value position.

# a character that is no space and no newline takes the array state's full
# step
def vl.arr.ws(
  sp: Bool,
  nl: Bool,
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
  +cc: Char,
  hsp: {sp == False{} : Bool},
  hnl: {nl == False{} : Bool}
) -> {T.read.fast.ws(sp, nl, True{}, "", rw, hs, he, ps, [], T.LArr{}, bk, qk, sk, un, lf, ab, cc)
  == T.read.fast.old("", rw, hs, he, ps, [], T.LArr{}, bk, qk, sk, un, lf, ab, cc) : T.St}:
  match sp:
    case True{}:
      Eq.bit.absurd2(&2, {T.read.fast.ws(True{}, nl, True{}, "", rw, hs, he, ps, [], T.LArr{}, bk, qk, sk, un, lf, ab,
        cc) == T.read.fast.old("", rw, hs, he, ps, [], T.LArr{}, bk, qk, sk, un, lf, ab, cc) : T.St}, hsp)
    case False{}:
      match nl:
        case True{}:
          Eq.bit.absurd2(&2, {T.read.fast.ws(False{}, True{}, True{}, "", rw, hs, he, ps, [], T.LArr{}, bk, qk, sk, un,
            lf, ab, cc) == T.read.fast.old("", rw, hs, he, ps, [], T.LArr{}, bk, qk, sk, un, lf, ab, cc) : T.St}, hnl)
        case False{}:
          {==}

# no space, newline, # or ]: the array state holds the character for the
# value state
def vl.arr.go(
  sp: Bool,
  nl: Bool,
  hash: Bool,
  end: Bool,
  +st: T.St,
  +cc: Char,
  hsp: {sp == False{} : Bool},
  hnl: {nl == False{} : Bool},
  hhs: {hash == False{} : Bool},
  hen: {end == False{} : Bool}
) -> {T.lex.arr.go(sp, nl, hash, end, st, cc) == T.lex.arr.end(False{}, st, cc) : T.St}:
  match sp:
    case True{}:
      Eq.bit.absurd2(&2, {T.lex.arr.go(True{}, nl, hash, end, st, cc) == T.lex.arr.end(False{}, st, cc) : T.St}, hsp)
    case False{}:
      match nl:
        case True{}:
          Eq.bit.absurd2(&2, {T.lex.arr.go(False{}, True{}, hash, end, st, cc) == T.lex.arr.end(False{}, st, cc)
            : T.St}, hnl)
        case False{}:
          match hash:
            case True{}:
              Eq.bit.absurd2(&2, {T.lex.arr.go(False{}, False{}, True{}, end, st, cc) == T.lex.arr.end(False{}, st,
                cc) : T.St}, hhs)
            case False{}:
              match end:
                case True{}:
                  Eq.bit.absurd2(&2, {T.lex.arr.go(False{}, False{}, False{}, True{}, st, cc) == T.lex.arr.end(False{},
                    st, cc) : T.St}, hen)
                case False{}:
                  {==}

# the first character of a bare word, read in an array, is pushed as in the
# value state with back at LVal
def vl.arr.first(
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
  +xx: U32,
  +h1: {D2.word.first(Chr{xx}) == True{} : Bool}
) -> {T.doc.scan(D2.s1.apos(rw, hs, he, ps, bk, qk, sk, un, lf, ab), Chr{xx})
  == T.doc.scan(D2.vpos(rw, hs, he, ps, T.LVal{}, qk, sk, un, lf, ab), Chr{xx}) : T.Mode}:
  +hw = {Eq.and.left(D2.word.char(Chr{xx}), Bool.not(Bool.or(Char.is_eq(Chr{xx}, '['),
    Char.is_eq(Chr{xx}, '{'))), h1) : {D2.word.char(Chr{xx}) == True{} : Bool}}
  +hd = {M2.wd.delim(Chr{xx}, hw) : {T.ch.delim(Chr{xx}) == False{} : Bool}}
  +hq = {Eq.not.true(Bool.or(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\'')),
    Eq.and.right(Bool.not(T.ch.delim(Chr{xx})), Bool.not(Bool.or(Char.is_eq(Chr{xx}, '"'),
    Char.is_eq(Chr{xx}, '\''))), hw))
    : {Bool.or(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\'')) == False{} : Bool}}
  +hb = {Eq.not.true(Bool.or(Char.is_eq(Chr{xx}, '['), Char.is_eq(Chr{xx}, '{')),
    Eq.and.right(D2.word.char(Chr{xx}), Bool.not(Bool.or(Char.is_eq(Chr{xx}, '['),
    Char.is_eq(Chr{xx}, '{'))), h1)) : {Bool.or(Char.is_eq(Chr{xx}, '['), Char.is_eq(Chr{xx}, '{')) == False{} : Bool}}
  +d1 = {Eq.or.right_false(T.ch.sp(Chr{xx}), Bool.or(T.ch.nl(Chr{xx}), Bool.or(Char.is_eq(Chr{xx}, '#'),
    Bool.or(Char.is_eq(Chr{xx}, ','), Bool.or(Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '}'))))), hd)
    : {Bool.or(T.ch.nl(Chr{xx}), Bool.or(Char.is_eq(Chr{xx}, '#'), Bool.or(Char.is_eq(Chr{xx}, ','),
    Bool.or(Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '}'))))) == False{} : Bool}}
  +d2 = {Eq.or.right_false(T.ch.nl(Chr{xx}), Bool.or(Char.is_eq(Chr{xx}, '#'), Bool.or(Char.is_eq(Chr{xx}, ','),
    Bool.or(Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '}')))), d1)
    : {Bool.or(Char.is_eq(Chr{xx}, '#'), Bool.or(Char.is_eq(Chr{xx}, ','), Bool.or(Char.is_eq(Chr{xx}, ']'),
    Char.is_eq(Chr{xx}, '}')))) == False{} : Bool}}
  +d3 = {Eq.or.right_false(Char.is_eq(Chr{xx}, '#'), Bool.or(Char.is_eq(Chr{xx}, ','), Bool.or(Char.is_eq(Chr{xx},
    ']'), Char.is_eq(Chr{xx}, '}'))), d2) : {Bool.or(Char.is_eq(Chr{xx}, ','), Bool.or(Char.is_eq(Chr{xx}, ']'),
    Char.is_eq(Chr{xx}, '}'))) == False{} : Bool}}
  +d4 = {Eq.or.right_false(Char.is_eq(Chr{xx}, ','), Bool.or(Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '}')), d3)
    : {Bool.or(Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '}')) == False{} : Bool}}
  +fsp = {Eq.or.left_false(T.ch.sp(Chr{xx}), Bool.or(T.ch.nl(Chr{xx}), Bool.or(Char.is_eq(Chr{xx}, '#'),
    Bool.or(Char.is_eq(Chr{xx}, ','), Bool.or(Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '}'))))), hd)
    : {T.ch.sp(Chr{xx}) == False{} : Bool}}
  +fnl = {Eq.or.left_false(T.ch.nl(Chr{xx}), Bool.or(Char.is_eq(Chr{xx}, '#'), Bool.or(Char.is_eq(Chr{xx}, ','),
    Bool.or(Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '}')))), d1) : {T.ch.nl(Chr{xx}) == False{} : Bool}}
  +fhs = {Eq.or.left_false(Char.is_eq(Chr{xx}, '#'), Bool.or(Char.is_eq(Chr{xx}, ','), Bool.or(Char.is_eq(Chr{xx},
    ']'), Char.is_eq(Chr{xx}, '}'))), d2) : {Char.is_eq(Chr{xx}, '#') == False{} : Bool}}
  +frb = {Eq.or.left_false(Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '}'), d4)
    : {Char.is_eq(Chr{xx}, ']') == False{} : Bool}}
  +st = {T.St{"", rw, hs, he, ps, [], T.LArr{}, bk, qk, sk, T.HNone{}, un, lf, ab, False{}} : T.St}
  +sv = {T.St{"", rw, hs, he, ps, [], T.LVal{}, T.LVal{}, qk, sk, T.HNone{}, un, lf, ab, False{}} : T.St}
  Equal.trans(T.Mode, T.doc.scan(D2.s1.apos(rw, hs, he, ps, bk, qk, sk, un, lf, ab), Chr{xx}),
    T.MScan{T.read.fast(st, Chr{xx})},
    T.doc.scan(D2.vpos(rw, hs, he, ps, T.LVal{}, qk, sk, un, lf, ab), Chr{xx}),
    M4.scan.other(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), U32.is_eq(xx, 13), st, Chr{xx}, {==}, {==}, {==},
      ch => D2.word.first(ch), h1, {==}, {==}, {==}),
    Equal.trans(T.Mode, T.MScan{T.read.fast(st, Chr{xx})}, T.MScan{T.st.push(sv, Chr{xx}, T.LBare{})},
      T.doc.scan(D2.vpos(rw, hs, he, ps, T.LVal{}, qk, sk, un, lf, ab), Chr{xx}),
      Equal.cong(T.St, T.Mode, ss => T.MScan{ss}, T.read.fast(st, Chr{xx}), T.st.push(sv, Chr{xx}, T.LBare{}),
        Equal.trans(T.St, T.read.fast.ws(T.ch.sp(Chr{xx}), T.ch.nl(Chr{xx}), True{}, "", rw, hs, he, ps, [], T.LArr{},
          bk, qk, sk, un, lf, ab, Chr{xx}), T.read.fast.old("", rw, hs, he, ps, [], T.LArr{}, bk, qk, sk, un, lf, ab,
          Chr{xx}), T.st.push(sv, Chr{xx}, T.LBare{}),
          vl.arr.ws(T.ch.sp(Chr{xx}), T.ch.nl(Chr{xx}), rw, hs, he, ps, bk, qk, sk, un, lf, ab, Chr{xx}, fsp, fnl),
          Equal.trans(T.St, T.read.once2(T.lex.arr.go(T.ch.sp(Chr{xx}), T.ch.nl(Chr{xx}), Char.is_eq(Chr{xx}, '#'),
            Char.is_eq(Chr{xx}, ']'), st, Chr{xx})), T.read.once2(T.lex.arr.end(False{}, st, Chr{xx})),
            T.st.push(sv, Chr{xx}, T.LBare{}),
            Equal.cong(T.St, T.St, ss => T.read.once2(ss), T.lex.arr.go(T.ch.sp(Chr{xx}), T.ch.nl(Chr{xx}),
              Char.is_eq(Chr{xx}, '#'), Char.is_eq(Chr{xx}, ']'), st, Chr{xx}), T.lex.arr.end(False{}, st, Chr{xx}),
              vl.arr.go(T.ch.sp(Chr{xx}), T.ch.nl(Chr{xx}), Char.is_eq(Chr{xx}, '#'), Char.is_eq(Chr{xx}, ']'), st,
              Chr{xx}, fsp, fnl, fhs, frb)),
            M2.wd.go(T.ch.sp(Chr{xx}), T.ch.nl(Chr{xx}), Char.is_eq(Chr{xx}, '#'), Char.is_eq(Chr{xx}, '"'),
              Char.is_eq(Chr{xx}, '\''), Char.is_eq(Chr{xx}, '['), Char.is_eq(Chr{xx}, '{'), sv, Chr{xx}, fsp, fnl,
              fhs, Eq.or.left_false(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), hq),
              Eq.or.right_false(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), hq),
              Eq.or.left_false(Char.is_eq(Chr{xx}, '['), Char.is_eq(Chr{xx}, '{'), hb),
              Eq.or.right_false(Char.is_eq(Chr{xx}, '['), Char.is_eq(Chr{xx}, '{'), hb))))),
      Equal.sym(T.Mode, T.doc.scan(D2.vpos(rw, hs, he, ps, T.LVal{}, qk, sk, un, lf, ab), Chr{xx}),
        T.MScan{T.st.push(sv, Chr{xx}, T.LBare{})},
        M2.wd.first(D3.Vf{"", rw, hs, he, ps, T.LVal{}, qk, sk, un, lf, ab}, xx, h1))))

# a bare word from an array's item reads as from the value position the
# held character opens
def vl.arr.eq(
  ww: String,
  +hw: {D2.bw.word(ww) == True{} : Bool},
  +rest: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool
) -> {T.doc.read(String.append(ww, rest), T.MScan{D2.s1.apos(rw, hs, he, ps, bk, qk, sk, un, lf, ab)})
  == T.doc.read(String.append(ww, rest), T.MScan{D2.vpos(rw, hs, he, ps, T.LVal{}, qk, sk, un, lf, ab)}) : T.Doc}:
  match ww:
    case SNil{}:
      Eq.bit.absurd(&2, {T.doc.read(String.append(SNil{}, rest), T.MScan{D2.s1.apos(rw, hs, he, ps, bk, qk, sk, un,
        lf, ab)}) == T.doc.read(String.append(SNil{}, rest), T.MScan{D2.vpos(rw, hs, he, ps, T.LVal{}, qk, sk, un, lf,
        ab)}) : T.Doc}, hw)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          Equal.cong(T.Mode, T.Doc, md => T.doc.read(String.append(tt, rest), md),
            T.doc.scan(D2.s1.apos(rw, hs, he, ps, bk, qk, sk, un, lf, ab), Chr{xx}),
            T.doc.scan(D2.vpos(rw, hs, he, ps, T.LVal{}, qk, sk, un, lf, ab), Chr{xx}),
            vl.arr.first(rw, hs, he, ps, bk, qk, sk, un, lf, ab, xx, Eq.and.left(D2.word.first(Chr{xx}),
              D2.bw.more(tt, [Chr{xx}]), hw)))

def L2.bare_word_reads_on_in_array(w, hw, v, hv, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, ee):
  Equal.trans(T.Doc, T.doc.read(String.append(w, rest), T.MScan{D2.s1.apos(rw, hs, he, ps, bk, qk, sk, un, lf,
    ab)}), T.doc.read(String.append(w, rest), T.MScan{D2.vpos(rw, hs, he, ps, T.LVal{}, qk, sk, un, lf, ab)}),
    T.doc.read(rest, T.MScan{D2.bw.put(sk, v, rw, hs, he, ps, T.LVal{}, qk, un, lf, ab)}),
    vl.arr.eq(w, hw, rest, rw, hs, he, ps, bk, qk, sk, un, lf, ab),
    L1.bare_word_reads_on(w, hw, v, hv, rw, hs, he, ps, T.LVal{}, qk, sk, un, lf, ab, rest, ee))

# a scalar placed as an array's only item, then `]` and a newline, is the document of the pair
def vl.doc.a(
  vv: T.Val,
  +kk: String,
  sc: {M3.vl.sc(T.GotVal{vv}) == True{} : Bool}
) -> {T.doc.read("]\n", T.MScan{D2.bw.put([T.CArr{[], [kk], []}], vv, [], [], [], [], T.LVal{}, T.QBasic{}, 0, 0,
    False{})}) == T.Doc{"", [T.VPair{kk, T.VArr{[vv]}}]} : T.Doc}:
  match vv:
    case T.VStr{tx}:
      Eq.bit.absurd(&2, {T.doc.read("]\n", T.MScan{D2.bw.put([T.CArr{[], [kk], []}], T.VStr{tx}, [], [], [], [],
          T.LVal{}, T.QBasic{}, 0, 0, False{})}) == T.Doc{"", [T.VPair{kk, T.VArr{[T.VStr{tx}]}}]} : T.Doc}, sc)
    case T.VSpan{src, nn}:
      Eq.bit.absurd(&2, {T.doc.read("]\n", T.MScan{D2.bw.put([T.CArr{[], [kk], []}], T.VSpan{src, nn}, [], [], [], [],
          T.LVal{}, T.QBasic{}, 0, 0, False{})}) == T.Doc{"", [T.VPair{kk, T.VArr{[T.VSpan{src, nn}]}}]} : T.Doc}, sc)
    case T.VInt{sg, ds}:
      {==}
    case T.VFlo{sg, tx}:
      {==}
    case T.VBool{bt}:
      {==}
    case T.VWhen{ww}:
      {==}
    case T.VArr{it}:
      Eq.bit.absurd(&2, {T.doc.read("]\n", T.MScan{D2.bw.put([T.CArr{[], [kk], []}], T.VArr{it}, [], [], [], [],
          T.LVal{}, T.QBasic{}, 0, 0, False{})}) == T.Doc{"", [T.VPair{kk, T.VArr{[T.VArr{it}]}}]} : T.Doc}, sc)
    case T.VInl{rs}:
      Eq.bit.absurd(&2, {T.doc.read("]\n", T.MScan{D2.bw.put([T.CArr{[], [kk], []}], T.VInl{rs}, [], [], [], [],
          T.LVal{}, T.QBasic{}, 0, 0, False{})}) == T.Doc{"", [T.VPair{kk, T.VArr{[T.VInl{rs}]}}]} : T.Doc}, sc)
    case T.VHead{pp, rs}:
      Eq.bit.absurd(&2, {T.doc.read("]\n", T.MScan{D2.bw.put([T.CArr{[], [kk], []}], T.VHead{pp, rs}, [], [], [], [],
          T.LVal{}, T.QBasic{}, 0, 0, False{})}) == T.Doc{"", [T.VPair{kk, T.VArr{[T.VHead{pp, rs}]}}]} : T.Doc}, sc)
    case T.VAot{pp, rs}:
      Eq.bit.absurd(&2, {T.doc.read("]\n", T.MScan{D2.bw.put([T.CArr{[], [kk], []}], T.VAot{pp, rs}, [], [], [], [],
          T.LVal{}, T.QBasic{}, 0, 0, False{})}) == T.Doc{"", [T.VPair{kk, T.VArr{[T.VAot{pp, rs}]}}]} : T.Doc}, sc)
    case T.VAots{pp, es}:
      Eq.bit.absurd(&2, {T.doc.read("]\n", T.MScan{D2.bw.put([T.CArr{[], [kk], []}], T.VAots{pp, es}, [], [], [], [],
          T.LVal{}, T.QBasic{}, 0, 0, False{})}) == T.Doc{"", [T.VPair{kk, T.VArr{[T.VAots{pp, es}]}}]} : T.Doc}, sc)
    case T.VPair{nm, pv}:
      Eq.bit.absurd(&2, {T.doc.read("]\n", T.MScan{D2.bw.put([T.CArr{[], [kk], []}], T.VPair{nm, pv}, [], [], [], [],
          T.LVal{}, T.QBasic{}, 0, 0, False{})}) == T.Doc{"", [T.VPair{kk, T.VArr{[T.VPair{nm, pv}]}}]} : T.Doc}, sc)

# and as an array's only item
def vl.acc.a(
  kk: String,
  ek: {T.bare(kk) == True{} : Bool},
  +ww: String,
  +hw: {D2.bw.word(ww) == True{} : Bool},
  +vv: T.Val,
  +hv: {T.word.val(String.to_list(ww)) == T.GotVal{vv} : T.Got},
  +sc: {M3.vl.sc(T.GotVal{vv}) == True{} : Bool}
) -> {T.parse(D1.bw.kva(kk, ww)) == T.Doc{"", [T.VPair{kk, T.VArr{[vv]}}]} : T.Doc}:
  match kk:
    case SNil{}:
      Eq.bit.absurd(&2, {T.parse(D1.bw.kva(SNil{}, ww)) == T.Doc{"", [T.VPair{SNil{}, T.VArr{[vv]}}]} : T.Doc}, ek)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          Equal.trans(T.Doc, T.parse(D1.bw.kva(SCon{Chr{xx}, tt}, ww)), T.doc.read(String.append(ww, "]\n"),
            T.MScan{D2.s1.apos([], [], [], [], T.LTop{}, T.QBasic{}, [T.CArr{[], [SCon{Chr{xx}, tt}], []}], 0, 0,
            False{})}), T.Doc{"", [T.VPair{SCon{Chr{xx}, tt}, T.VArr{[vv]}}]},
            M1.kv.key2(xx, tt, SCon{'[', String.append(ww, "]\n")}, ek),
            Equal.trans(T.Doc, T.doc.read(String.append(ww, "]\n"), T.MScan{D2.s1.apos([], [], [], [], T.LTop{},
              T.QBasic{}, [T.CArr{[], [SCon{Chr{xx}, tt}], []}], 0, 0, False{})}), T.doc.read("]\n",
              T.MScan{D2.bw.put([T.CArr{[], [SCon{Chr{xx}, tt}], []}], vv, [], [], [], [], T.LVal{}, T.QBasic{}, 0, 0,
              False{})}), T.Doc{"", [T.VPair{SCon{Chr{xx}, tt}, T.VArr{[vv]}}]},
              L2.bare_word_reads_on_in_array(ww, hw, vv, hv, [], [], [], [], T.LTop{}, T.QBasic{}, [T.CArr{[],
              [SCon{Chr{xx}, tt}], []}], 0, 0, False{}, "]\n", {==}),
              vl.doc.a(vv, SCon{Chr{xx}, tt}, sc)))
