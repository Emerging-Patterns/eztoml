# table rows reordered by canon compared with the rows as they are
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/defs/DocumentSameness.bend as D1
import ./FreshNamesInRows.bend as M1
import ./PickAndDigitSteps.bend as M2
import ./ShortTextBounds.bend as M3
import ./ValueSelfEquality.bend as M4

# a character that is neither quote nor a carriage return is read in the scan
# mode. A law names such a character by a predicate that the three fail
def scan.other(
  dq: Bool,
  sq: Bool,
  cr: Bool,
  st: T.St,
  +cc: Char,
  edq: {Char.is_eq(cc, '"') == dq : Bool},
  esq: {Char.is_eq(cc, '\'') == sq : Bool},
  ecr: {Char.is_eq(cc, Chr{13}) == cr : Bool},
  pp: Char -> Bool,
  yes: {pp(cc) == True{} : Bool},
  n1: {pp('"') == False{} : Bool},
  n2: {pp('\'') == False{} : Bool},
  n3: {pp(Chr{13}) == False{} : Bool}
) -> {T.doc.scan.q(dq, sq, cr, st, cc) == T.MScan{T.read.fast(st, cc)} : T.Mode}:
  match dq:
    case True{}:
      Eq.bit.gone(&2, {T.doc.scan.q(True{}, sq, cr, st, cc) == T.MScan{T.read.fast(st, cc)}
        : T.Mode}, Eq.refute_char(cc, '"', pp, edq, yes, n1))
    case False{}:
      match sq:
        case True{}:
          Eq.bit.gone(&2, {T.doc.scan.q(False{}, True{}, cr, st, cc)
            == T.MScan{T.read.fast(st, cc)} : T.Mode},
            Eq.refute_char(cc, '\'', pp, esq, yes, n2))
        case False{}:
          match cr:
            case True{}:
              Eq.bit.gone(&2, {T.doc.scan.q(False{}, False{}, True{}, st, cc)
                == T.MScan{T.read.fast(st, cc)} : T.Mode},
                Eq.refute_char(cc, Chr{13}, pp, ecr, yes, n3))
            case False{}:
              {==}

# the quotient by ten
def dq(+xx: U32) -> U32:
  U32.div(xx, 10)

# no name is in an empty table
def cv.fr.nil(rows: List<&2, T.Val>) -> {M1.cv.fr([], rows) == True{} : Bool}:
  match rows:
    case []:
      {==}
    case T.VPair{_kk, _vv} <> tt:
      cv.fr.nil(tt)
    case T.VStr{_a} <> tt:
      cv.fr.nil(tt)
    case T.VSpan{_a, _b} <> tt:
      cv.fr.nil(tt)
    case T.VInt{_a, _b} <> tt:
      cv.fr.nil(tt)
    case T.VFlo{_a, _b} <> tt:
      cv.fr.nil(tt)
    case T.VBool{_a} <> tt:
      cv.fr.nil(tt)
    case T.VWhen{_a} <> tt:
      cv.fr.nil(tt)
    case T.VArr{_a} <> tt:
      cv.fr.nil(tt)
    case T.VInl{_a} <> tt:
      cv.fr.nil(tt)
    case T.VHead{_a, _b} <> tt:
      cv.fr.nil(tt)
    case T.VAot{_a, _b} <> tt:
      cv.fr.nil(tt)
    case T.VAots{_a, _b} <> tt:
      cv.fr.nil(tt)

# what st compares
def st.l(md: Bool, +xs: List<&2, T.Val>, +hp: String) -> List<&2, T.Val>:
  match md:
    case False{}:
      D1.canon.tabs(xs)
    case True{}:
      D1.canon.go(xs, D1.CElems{hp})

# and against what
def st.r(md: Bool, +xs: List<&2, T.Val>) -> List<&2, T.Val>:
  match md:
    case False{}:
      M1.rtabs(xs)
    case True{}:
      xs

# a table's rows, reordered, against them as they are
def st(
  xs: List<&2, T.Val>,
  md: Bool,
  +hp: String,
  +hw: {T.wf.go(xs, M4.st.at(md, hp)) == True{} : Bool}
) -> {D1.same.go(st.l(md, xs, hp), st.r(md, xs)) == True{} : Bool}:
  match xs md:
    case [] False{}:
      {==}
    case [] True{}:
      {==}
    case T.VPair{+kk, T.VHead{+p, +r}} <> +t False{}:
      +hin = {M3.wt.more(Bool.and(T.wf.key(kk, t), T.str.eq(p, T.tree.pre(hp, kk))), _u => T.wf.then(T.wf.go(r,
        T.WfRows{p}), _v => T.wf.go(t, T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(r, T.WfRows{p}), _v => T.wf.go(t,
        T.WfRows{hp})) == True{} : Bool}}
      +hwr = {M3.wt.ok(T.wf.go(r, T.WfRows{p}), _v => T.wf.go(t, T.WfRows{hp}), hin) : {T.wf.go(r,
          T.WfRows{p}) == True{}
        : Bool}}
      Equal.trans(Bool, D1.same.go(T.VPair{kk, T.VHead{p, D1.canon.rows(r)}} <> D1.canon.tabs(t),
        T.VPair{kk, T.VHead{p, r}} <> M1.rtabs(t)), D1.same.pair(D1.Picked{T.VHead{p, r}, M1.rtabs(t)},
        ww => D1.same.box(D1.KHead{}, ww, ws => D1.same.go(D1.canon.rows(r), ws)),
        rr => D1.same.go(D1.canon.tabs(t), rr)), True{},
        Equal.cong(D1.Pick, Bool, pk2 => D1.same.pair(pk2, ww => D1.same.box(D1.KHead{}, ww,
          ws => D1.same.go(D1.canon.rows(r), ws)), rr => D1.same.go(D1.canon.tabs(t), rr)),
          D1.pick(T.VPair{kk, T.VHead{p, r}} <> M1.rtabs(t), kk), D1.Picked{T.VHead{p, r}, M1.rtabs(t)},
          M2.pick.self(kk, T.VHead{p, r}, M1.rtabs(t))),
        M4.at.tt(D1.same.go(D1.canon.rows(r), r), _u => D1.same.go(D1.canon.tabs(t), M1.rtabs(t)),
          Equal.trans(Bool, D1.same.go(D1.canon.rows(r), r), D1.same.go(D1.canon.tabs(r), M1.rtabs(r)), True{},
            M1.pk(r, p, D1.canon.tabs(r), [], hwr, M4.wf.selfs(r, T.WfRows{p}, hwr), cv.fr.nil(D1.canon.keys(r))),
            st(r, False{}, p, hwr)),
          st(t, False{}, hp, M3.wt.more(T.wf.go(r, T.WfRows{p}), _v => T.wf.go(t, T.WfRows{hp}), hin))))
    case T.VPair{+kk, T.VAots{+p, +es}} <> +t False{}:
      +hin = {M3.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, es)), Bool.and(T.wf.key(kk, t), T.str.eq(p,
        T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(es, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp})), hw)
        : {T.wf.then(T.wf.go(es, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp})) == True{} : Bool}}
      Equal.trans(Bool, D1.same.go(T.VPair{kk, T.VAots{p, D1.canon.go(es, D1.CElems{p})}} <> D1.canon.tabs(t),
        T.VPair{kk, T.VAots{p, es}} <> M1.rtabs(t)), D1.same.pair(D1.Picked{T.VAots{p, es}, M1.rtabs(t)},
        ww => D1.same.box(D1.KAots{}, ww, ws => D1.same.go(D1.canon.go(es, D1.CElems{p}), ws)),
        rr => D1.same.go(D1.canon.tabs(t), rr)), True{},
        Equal.cong(D1.Pick, Bool, pk2 => D1.same.pair(pk2, ww => D1.same.box(D1.KAots{}, ww,
          ws => D1.same.go(D1.canon.go(es, D1.CElems{p}), ws)), rr => D1.same.go(D1.canon.tabs(t), rr)),
          D1.pick(T.VPair{kk, T.VAots{p, es}} <> M1.rtabs(t), kk), D1.Picked{T.VAots{p, es}, M1.rtabs(t)},
          M2.pick.self(kk, T.VAots{p, es}, M1.rtabs(t))),
        M4.at.tt(D1.same.go(D1.canon.go(es, D1.CElems{p}), es), _u => D1.same.go(D1.canon.tabs(t), M1.rtabs(t)),
          st(es, True{}, p, M3.wt.ok(T.wf.go(es, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}), hin)),
          st(t, False{}, hp, M3.wt.more(T.wf.go(es, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}), hin))))
    case T.VPair{+kk, T.VStr{+a1}} <> +t False{}:
      st(t, False{}, hp, M3.wt.more(Bool.and(T.wf.atom(T.VStr{a1}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}),
          hw))
    case T.VPair{+kk, T.VSpan{+a1, +a2}} <> +t False{}:
      st(t, False{}, hp, M3.wt.more(Bool.and(T.wf.atom(T.VSpan{a1, a2}), T.wf.key(kk, t)), _u => T.wf.go(t,
          T.WfRows{hp}),
        hw))
    case T.VPair{+kk, T.VInt{+a1, +a2}} <> +t False{}:
      st(t, False{}, hp, M3.wt.more(Bool.and(T.wf.atom(T.VInt{a1, a2}), T.wf.key(kk, t)), _u => T.wf.go(t,
          T.WfRows{hp}),
        hw))
    case T.VPair{+kk, T.VFlo{+a1, +a2}} <> +t False{}:
      st(t, False{}, hp, M3.wt.more(Bool.and(T.wf.atom(T.VFlo{a1, a2}), T.wf.key(kk, t)), _u => T.wf.go(t,
          T.WfRows{hp}),
        hw))
    case T.VPair{+kk, T.VBool{+a1}} <> +t False{}:
      st(t, False{}, hp, M3.wt.more(Bool.and(T.wf.atom(T.VBool{a1}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}),
          hw))
    case T.VPair{+kk, T.VWhen{+a1}} <> +t False{}:
      st(t, False{}, hp, M3.wt.more(Bool.and(T.wf.atom(T.VWhen{a1}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}),
          hw))
    case T.VPair{+kk, T.VArr{+a1}} <> +t False{}:
      st(t, False{}, hp, M3.wt.more(T.wf.go(a1, T.WfItems{}), _v => T.wf.go(t, T.WfRows{hp}), M3.wt.more(T.wf.key(kk,
          t),
        _u => T.wf.then(T.wf.go(a1, T.WfItems{}), _v => T.wf.go(t, T.WfRows{hp})), hw)))
    case T.VPair{+kk, T.VInl{+a1}} <> +t False{}:
      st(t, False{}, hp, M3.wt.more(T.wf.go(a1, T.WfInl{}), _v => T.wf.go(t, T.WfRows{hp}), M3.wt.more(T.wf.key(kk, t),
        _u => T.wf.then(T.wf.go(a1, T.WfInl{}), _v => T.wf.go(t, T.WfRows{hp})), hw)))
    case T.VPair{+kk, T.VAot{+a1, +a2}} <> +t False{}:
      Eq.bit.absurd(&2, {D1.same.go(st.l(False{}, T.VPair{kk, T.VAot{a1, a2}} <> t, hp), st.r(False{}, T.VPair{kk,
        T.VAot{a1, a2}} <> t)) == True{} : Bool}, hw)
    case T.VPair{+kk, T.VPair{+a1, +a2}} <> +t False{}:
      Eq.bit.absurd(&2, {D1.same.go(st.l(False{}, T.VPair{kk, T.VPair{a1, a2}} <> t, hp), st.r(False{}, T.VPair{kk,
        T.VPair{a1, a2}} <> t)) == True{} : Bool}, hw)
    case T.VStr{+a1} <> +t False{}:
      Eq.bit.absurd(&2, {D1.same.go(st.l(False{}, T.VStr{a1} <> t, hp), st.r(False{},
        T.VStr{a1} <> t)) == True{} : Bool}, hw)
    case T.VSpan{+a1, +a2} <> +t False{}:
      Eq.bit.absurd(&2, {D1.same.go(st.l(False{}, T.VSpan{a1, a2} <> t, hp), st.r(False{}, T.VSpan{a1,
        a2} <> t)) == True{} : Bool}, hw)
    case T.VInt{+a1, +a2} <> +t False{}:
      Eq.bit.absurd(&2, {D1.same.go(st.l(False{}, T.VInt{a1, a2} <> t, hp), st.r(False{}, T.VInt{a1,
        a2} <> t)) == True{} : Bool}, hw)
    case T.VFlo{+a1, +a2} <> +t False{}:
      Eq.bit.absurd(&2, {D1.same.go(st.l(False{}, T.VFlo{a1, a2} <> t, hp), st.r(False{}, T.VFlo{a1,
        a2} <> t)) == True{} : Bool}, hw)
    case T.VBool{+a1} <> +t False{}:
      Eq.bit.absurd(&2, {D1.same.go(st.l(False{}, T.VBool{a1} <> t, hp), st.r(False{},
        T.VBool{a1} <> t)) == True{} : Bool}, hw)
    case T.VWhen{+a1} <> +t False{}:
      Eq.bit.absurd(&2, {D1.same.go(st.l(False{}, T.VWhen{a1} <> t, hp), st.r(False{},
        T.VWhen{a1} <> t)) == True{} : Bool}, hw)
    case T.VArr{+a1} <> +t False{}:
      Eq.bit.absurd(&2, {D1.same.go(st.l(False{}, T.VArr{a1} <> t, hp), st.r(False{},
        T.VArr{a1} <> t)) == True{} : Bool}, hw)
    case T.VInl{+a1} <> +t False{}:
      Eq.bit.absurd(&2, {D1.same.go(st.l(False{}, T.VInl{a1} <> t, hp), st.r(False{},
        T.VInl{a1} <> t)) == True{} : Bool}, hw)
    case T.VHead{+a1, +a2} <> +t False{}:
      Eq.bit.absurd(&2, {D1.same.go(st.l(False{}, T.VHead{a1, a2} <> t, hp), st.r(False{}, T.VHead{a1,
        a2} <> t)) == True{} : Bool}, hw)
    case T.VAot{+a1, +a2} <> +t False{}:
      Eq.bit.absurd(&2, {D1.same.go(st.l(False{}, T.VAot{a1, a2} <> t, hp), st.r(False{}, T.VAot{a1,
        a2} <> t)) == True{} : Bool}, hw)
    case T.VAots{+a1, +a2} <> +t False{}:
      Eq.bit.absurd(&2, {D1.same.go(st.l(False{}, T.VAots{a1, a2} <> t, hp), st.r(False{}, T.VAots{a1,
        a2} <> t)) == True{} : Bool}, hw)
    case T.VAot{+q, +r} <> +t True{}:
      +hin = {M3.wt.more(T.str.eq(q, hp), _u => T.wf.then(T.wf.go(r, T.WfRows{q}), _v => T.wf.go(t, T.WfElems{hp})), hw)
        : {T.wf.then(T.wf.go(r, T.WfRows{q}), _v => T.wf.go(t, T.WfElems{hp})) == True{} : Bool}}
      +hwr = {M3.wt.ok(T.wf.go(r, T.WfRows{q}), _v => T.wf.go(t, T.WfElems{hp}), hin) : {T.wf.go(r,
          T.WfRows{q}) == True{}
        : Bool}}
      M4.at.tt(D1.same.go(D1.canon.rows(r), r), _u => D1.same.go(D1.canon.go(t, D1.CElems{hp}), t),
        Equal.trans(Bool, D1.same.go(D1.canon.rows(r), r), D1.same.go(D1.canon.tabs(r), M1.rtabs(r)), True{},
            M1.pk(r, q, D1.canon.tabs(r), [], hwr, M4.wf.selfs(r, T.WfRows{q}, hwr), cv.fr.nil(D1.canon.keys(r))),
            st(r, False{}, q, hwr)),
        st(t, True{}, hp, M3.wt.more(T.wf.go(r, T.WfRows{q}), _v => T.wf.go(t, T.WfElems{hp}), hin)))
    case T.VStr{+a1} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(st.l(True{}, T.VStr{a1} <> t, hp), st.r(True{},
        T.VStr{a1} <> t)) == True{} : Bool}, hw)
    case T.VSpan{+a1, +a2} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(st.l(True{}, T.VSpan{a1, a2} <> t, hp), st.r(True{}, T.VSpan{a1,
        a2} <> t)) == True{} : Bool}, hw)
    case T.VInt{+a1, +a2} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(st.l(True{}, T.VInt{a1, a2} <> t, hp), st.r(True{}, T.VInt{a1,
        a2} <> t)) == True{} : Bool}, hw)
    case T.VFlo{+a1, +a2} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(st.l(True{}, T.VFlo{a1, a2} <> t, hp), st.r(True{}, T.VFlo{a1,
        a2} <> t)) == True{} : Bool}, hw)
    case T.VBool{+a1} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(st.l(True{}, T.VBool{a1} <> t, hp), st.r(True{},
        T.VBool{a1} <> t)) == True{} : Bool}, hw)
    case T.VWhen{+a1} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(st.l(True{}, T.VWhen{a1} <> t, hp), st.r(True{},
        T.VWhen{a1} <> t)) == True{} : Bool}, hw)
    case T.VArr{+a1} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(st.l(True{}, T.VArr{a1} <> t, hp), st.r(True{},
        T.VArr{a1} <> t)) == True{} : Bool}, hw)
    case T.VInl{+a1} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(st.l(True{}, T.VInl{a1} <> t, hp), st.r(True{},
        T.VInl{a1} <> t)) == True{} : Bool}, hw)
    case T.VHead{+a1, +a2} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(st.l(True{}, T.VHead{a1, a2} <> t, hp), st.r(True{}, T.VHead{a1,
        a2} <> t)) == True{} : Bool}, hw)
    case T.VAots{+a1, +a2} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(st.l(True{}, T.VAots{a1, a2} <> t, hp), st.r(True{}, T.VAots{a1,
        a2} <> t)) == True{} : Bool}, hw)
    case T.VPair{+a1, T.VStr{+b1}} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(st.l(True{}, T.VPair{a1, T.VStr{b1}} <> t, hp), st.r(True{}, T.VPair{a1,
        T.VStr{b1}} <> t)) == True{} : Bool}, hw)
    case T.VPair{+a1, T.VSpan{+b1, +b2}} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(st.l(True{}, T.VPair{a1, T.VSpan{b1, b2}} <> t, hp), st.r(True{}, T.VPair{a1,
        T.VSpan{b1, b2}} <> t)) == True{} : Bool}, hw)
    case T.VPair{+a1, T.VInt{+b1, +b2}} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(st.l(True{}, T.VPair{a1, T.VInt{b1, b2}} <> t, hp), st.r(True{}, T.VPair{a1,
        T.VInt{b1, b2}} <> t)) == True{} : Bool}, hw)
    case T.VPair{+a1, T.VFlo{+b1, +b2}} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(st.l(True{}, T.VPair{a1, T.VFlo{b1, b2}} <> t, hp), st.r(True{}, T.VPair{a1,
        T.VFlo{b1, b2}} <> t)) == True{} : Bool}, hw)
    case T.VPair{+a1, T.VBool{+b1}} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(st.l(True{}, T.VPair{a1, T.VBool{b1}} <> t, hp), st.r(True{}, T.VPair{a1,
        T.VBool{b1}} <> t)) == True{} : Bool}, hw)
    case T.VPair{+a1, T.VWhen{+b1}} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(st.l(True{}, T.VPair{a1, T.VWhen{b1}} <> t, hp), st.r(True{}, T.VPair{a1,
        T.VWhen{b1}} <> t)) == True{} : Bool}, hw)
    case T.VPair{+a1, T.VArr{+b1}} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(st.l(True{}, T.VPair{a1, T.VArr{b1}} <> t, hp), st.r(True{}, T.VPair{a1,
        T.VArr{b1}} <> t)) == True{} : Bool}, hw)
    case T.VPair{+a1, T.VInl{+b1}} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(st.l(True{}, T.VPair{a1, T.VInl{b1}} <> t, hp), st.r(True{}, T.VPair{a1,
        T.VInl{b1}} <> t)) == True{} : Bool}, hw)
    case T.VPair{+a1, T.VHead{+b1, +b2}} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(st.l(True{}, T.VPair{a1, T.VHead{b1, b2}} <> t, hp), st.r(True{}, T.VPair{a1,
        T.VHead{b1, b2}} <> t)) == True{} : Bool}, hw)
    case T.VPair{+a1, T.VAot{+b1, +b2}} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(st.l(True{}, T.VPair{a1, T.VAot{b1, b2}} <> t, hp), st.r(True{}, T.VPair{a1,
        T.VAot{b1, b2}} <> t)) == True{} : Bool}, hw)
    case T.VPair{+a1, T.VAots{+b1, +b2}} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(st.l(True{}, T.VPair{a1, T.VAots{b1, b2}} <> t, hp), st.r(True{}, T.VPair{a1,
        T.VAots{b1, b2}} <> t)) == True{} : Bool}, hw)
    case T.VPair{+a1, T.VPair{+b1, +b2}} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(st.l(True{}, T.VPair{a1, T.VPair{b1, b2}} <> t, hp), st.r(True{}, T.VPair{a1,
        T.VPair{b1, b2}} <> t)) == True{} : Bool}, hw)
