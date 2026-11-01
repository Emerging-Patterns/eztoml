# lemmas that parse output is well formed, with fresh names, digits and
# escapes
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/ParsedIsWellFormed.bend as L1
import ../../laws/SealPutsNewestLast.bend as L2
import ../../laws/defs/BareValueGrammar.bend as D1
import ../../laws/defs/SealedValues.bend as D2
import ./AndCommutes.bend as M1
import ./SealNewestLast.bend as M2
import ./ValueSelfEquality.bend as M3
import ./WellFormedTextWalk.bend as M4

# a name fresh in rows
def gd.fg(rr: List<&2, T.Val>, kk: String) -> Bool:
  T.wf.fresh(T.get(rr, kk))

def L1.gd_start(rows, _heads, here, _lex, _back, _qkind, _uni, _left, _arrtab, _lead, ew, eh):
  M4.gd.tt(Bool.and(T.wf.go(rows, T.WfRows{""}), True{}), Bool.and(L1.gd.segs(here), True{}),
    M4.gd.tt(T.wf.go(rows, T.WfRows{""}), True{}, ew, {==}),
    M4.gd.tt(L1.gd.segs(here), True{}, eh, {==}))

# a name is fresh in two lists joined exactly when it is fresh in each
def gd.fr.app.step(
  bb: Bool,
  vv: T.Val,
  aa: List<&2, T.Val>,
  bs: List<&2, T.Val>,
  +kk: String,
  +ih: {gd.fg(List.append(&2, T.Val, aa, bs), kk) == Bool.and(gd.fg(aa, kk), gd.fg(bs, kk)) : Bool}
) -> {T.wf.fresh(T.find.step(bb, vv, _u => T.rows.find(List.append(&2, T.Val, aa, bs), kk)))
    == Bool.and(T.wf.fresh(T.find.step(bb, vv, _u => T.rows.find(aa, kk))), T.wf.fresh(T.get(bs, kk))) : Bool}:
  match bb:
    case True{}:
      {==}
    case False{}:
      ih

def gd.fr.app(
  aa: List<&2, T.Val>,
  +bs: List<&2, T.Val>,
  +kk: String
) -> {T.wf.fresh(T.get(List.append(&2, T.Val, aa, bs), kk))
    == Bool.and(T.wf.fresh(T.get(aa, kk)), T.wf.fresh(T.get(bs, kk))) : Bool}:
  match aa:
    case []:
      {==}
    case T.VPair{+n, +v} <> +t:
      gd.fr.app.step(T.str.eq(n, kk), v, t, bs, kk, gd.fr.app(t, bs, kk))
    case T.VStr{_a0} <> +t:
      gd.fr.app(t, bs, kk)
    case T.VSpan{_a0, _a1} <> +t:
      gd.fr.app(t, bs, kk)
    case T.VInt{_a0, _a1} <> +t:
      gd.fr.app(t, bs, kk)
    case T.VFlo{_a0, _a1} <> +t:
      gd.fr.app(t, bs, kk)
    case T.VBool{_a0} <> +t:
      gd.fr.app(t, bs, kk)
    case T.VWhen{_a0} <> +t:
      gd.fr.app(t, bs, kk)
    case T.VArr{_a0} <> +t:
      gd.fr.app(t, bs, kk)
    case T.VInl{_a0} <> +t:
      gd.fr.app(t, bs, kk)
    case T.VHead{_a0, _a1} <> +t:
      gd.fr.app(t, bs, kk)
    case T.VAot{_a0, _a1} <> +t:
      gd.fr.app(t, bs, kk)
    case T.VAots{_a0, _a1} <> +t:
      gd.fr.app(t, bs, kk)

# a pair's name the head of a list does not hold, so the name is fresh past it
def gd.fr.skip(
  bb: Bool,
  vv: T.Val,
  rest: Unit -> T.Hit,
  ee: {T.wf.fresh(T.find.step(bb, vv, rest)) == True{} : Bool}
) -> {T.wf.fresh(rest(Unit{})) == True{} : Bool}:
  match bb:
    case True{}:
      Eq.bit.absurd(&2, {T.wf.fresh(rest(Unit{})) == True{} : Bool}, ee)
    case False{}:
      ee

# and the test that let it past answered False
def gd.fr.no(
  bb: Bool,
  vv: T.Val,
  rest: Unit -> T.Hit,
  ee: {T.wf.fresh(T.find.step(bb, vv, rest)) == True{} : Bool}
) -> {bb == False{} : Bool}:
  match bb:
    case True{}:
      Eq.bit.absurd(&2, {True{} == False{} : Bool}, ee)
    case False{}:
      {==}

# the name of what comes after a list, fresh in it
def gd.fy(aa: List<&2, T.Val>, yy: T.Val) -> Bool:
  match yy:
    case T.VPair{+yn, _yv}:
      T.wf.fresh(T.get(aa, yn))
    case _:
      True{}

# a key is fresh in a list of one pair of a name fresh before it
def gd.y.fresh(
  yy: T.Val,
  +n: String,
  +v: T.Val,
  +aa: List<&2, T.Val>,
  +ef: {gd.fy(T.VPair{n, v} <> aa, yy) == True{} : Bool}
) -> {T.wf.fresh(T.get([yy], n)) == True{} : Bool}:
  match yy:
    case T.VPair{+yn, +yv}:
      Equal.trans(Bool, T.wf.fresh(T.find.step(T.str.eq(yn, n), yv, _u => T.rows.find([], n))),
        T.wf.fresh(T.find.step(False{}, yv, _u => T.rows.find([], n))), True{},
        Equal.cong(Bool, Bool, bb => T.wf.fresh(T.find.step(bb, yv, _u => T.rows.find([], n))),
          T.str.eq(yn, n), False{},
          Equal.trans(Bool, T.str.eq(yn, n), T.str.eq(n, yn), False{}, M3.str.eq.sym(yn, n, True{}),
            gd.fr.no(T.str.eq(n, yn), v, _u => T.rows.find(aa, yn), ef))),
        {==})
    case T.VStr{_a0}:
      {==}
    case T.VSpan{_a0, _a1}:
      {==}
    case T.VInt{_a0, _a1}:
      {==}
    case T.VFlo{_a0, _a1}:
      {==}
    case T.VBool{_a0}:
      {==}
    case T.VWhen{_a0}:
      {==}
    case T.VArr{_a0}:
      {==}
    case T.VInl{_a0}:
      {==}
    case T.VHead{_a0, _a1}:
      {==}
    case T.VAot{_a0, _a1}:
      {==}
    case T.VAots{_a0, _a1}:
      {==}

# a key fresh in a list is fresh in it with a pair of another name after it
def gd.key.app(
  +n: String,
  +v: T.Val,
  +aa: List<&2, T.Val>,
  +yy: T.Val,
  +ek: {T.wf.key(n, aa) == True{} : Bool},
  +ef: {gd.fy(T.VPair{n, v} <> aa, yy) == True{} : Bool}
) -> {T.wf.key(n, List.append(&2, T.Val, aa, [yy])) == True{} : Bool}:
  M4.gd.tt(T.wf.text(n), T.wf.fresh(T.get(List.append(&2, T.Val, aa, [yy]), n)),
    M4.gd.l(T.wf.text(n), T.wf.fresh(T.get(aa, n)), ek),
    Equal.trans(Bool, T.wf.fresh(T.get(List.append(&2, T.Val, aa, [yy]), n)),
      Bool.and(T.wf.fresh(T.get(aa, n)), T.wf.fresh(T.get([yy], n))), True{},
      gd.fr.app(aa, [yy], n),
      M4.gd.tt(T.wf.fresh(T.get(aa, n)), T.wf.fresh(T.get([yy], n)),
        M4.gd.r(T.wf.text(n), T.wf.fresh(T.get(aa, n)), ek), gd.y.fresh(yy, n, v, aa, ef))))

# the head's needs hold with one more value after the rest
def gd.h1.app(
  aa: T.Val,
  +rest: List<&2, T.Val>,
  +yy: T.Val,
  +at: T.WfAt,
  +e1: {M4.gd.h1(aa, rest, at) == True{} : Bool},
  +ef: {gd.fy(aa <> rest, yy) == True{} : Bool}
) -> {M4.gd.h1(aa, List.append(&2, T.Val, rest, [yy]), at) == True{} : Bool}:
  match aa:
    case T.VPair{+n, +v}:
      M4.gd.tt(T.wf.key(n, List.append(&2, T.Val, rest, [yy])), M4.gd.pa(at, n, v),
        gd.key.app(n, v, rest, yy, M4.gd.l(T.wf.key(n, rest), M4.gd.pa(at, n, v), e1), ef),
        M4.gd.r(T.wf.key(n, rest), M4.gd.pa(at, n, v), e1))
    case T.VStr{_a0}:
      e1
    case T.VSpan{_a0, _a1}:
      e1
    case T.VInt{_a0, _a1}:
      e1
    case T.VFlo{_a0, _a1}:
      e1
    case T.VBool{_a0}:
      e1
    case T.VWhen{_a0}:
      e1
    case T.VArr{_a0}:
      e1
    case T.VInl{_a0}:
      e1
    case T.VHead{_a0, _a1}:
      e1
    case T.VAot{_a0, _a1}:
      e1
    case T.VAots{_a0, _a1}:
      e1

# a name fresh in a list is fresh in its rest
def gd.fy.tail(
  yy: T.Val,
  aa: T.Val,
  +rest: List<&2, T.Val>,
  +ef: {gd.fy(aa <> rest, yy) == True{} : Bool}
) -> {gd.fy(rest, yy) == True{} : Bool}:
  match yy:
    case T.VPair{+yn, _yv}:
      match aa:
        case T.VPair{+n, +v}:
          gd.fr.skip(T.str.eq(n, yn), v, _u => T.rows.find(rest, yn), ef)
        case T.VStr{_a0}:
          ef
        case T.VSpan{_a0, _a1}:
          ef
        case T.VInt{_a0, _a1}:
          ef
        case T.VFlo{_a0, _a1}:
          ef
        case T.VBool{_a0}:
          ef
        case T.VWhen{_a0}:
          ef
        case T.VArr{_a0}:
          ef
        case T.VInl{_a0}:
          ef
        case T.VHead{_a0, _a1}:
          ef
        case T.VAot{_a0, _a1}:
          ef
        case T.VAots{_a0, _a1}:
          ef
    case T.VStr{_a0}:
      {==}
    case T.VSpan{_a0, _a1}:
      {==}
    case T.VInt{_a0, _a1}:
      {==}
    case T.VFlo{_a0, _a1}:
      {==}
    case T.VBool{_a0}:
      {==}
    case T.VWhen{_a0}:
      {==}
    case T.VArr{_a0}:
      {==}
    case T.VInl{_a0}:
      {==}
    case T.VHead{_a0, _a1}:
      {==}
    case T.VAot{_a0, _a1}:
      {==}
    case T.VAots{_a0, _a1}:
      {==}

# a list well-formed where it sits stays so with a value after it that is
# well-formed there alone and whose name, if any, the list does not hold
def gd.w1(
  aa: List<&2, T.Val>,
  +yy: T.Val,
  +at: T.WfAt,
  +ea: {T.wf.go(aa, at) == True{} : Bool},
  +ey: {T.wf.go([yy], at) == True{} : Bool},
  +ef: {gd.fy(aa, yy) == True{} : Bool}
) -> {T.wf.go(List.append(&2, T.Val, aa, [yy]), at) == True{} : Bool}:
  match aa:
    case []:
      ey
    case +a <> +rest:
      M4.gd.gen.mk(a, List.append(&2, T.Val, rest, [yy]), at,
        gd.h1.app(a, rest, yy, at, M4.gd.l(M4.gd.h1(a, rest, at), T.wf.go(rest, at), M4.gd.gen.un(a, rest, at, ea)),
            ef),
        gd.w1(rest, yy, at, M4.gd.r(M4.gd.h1(a, rest, at), T.wf.go(rest, at), M4.gd.gen.un(a, rest, at, ea)), ey,
          gd.fy.tail(yy, a, rest, ef)))

# two ands of equal halves are equal
def gd.and.cong(
  a1: Bool,
  a2: Bool,
  b1: Bool,
  b2: Bool,
  ea: {a1 == a2 : Bool},
  eb: {b1 == b2 : Bool}
) -> {Bool.and(a1, b1) == Bool.and(a2, b2) : Bool}:
  Equal.trans(Bool, Bool.and(a1, b1), Bool.and(a2, b1), Bool.and(a2, b2),
    Equal.cong(Bool, Bool, xx => Bool.and(xx, b1), a1, a2, ea),
    Equal.cong(Bool, Bool, xx => Bool.and(a2, xx), b1, b2, eb))

# a lookup that stops at a pair or not, whatever the pair holds
def gd.fr.w(
  bb: Bool,
  v1: T.Val,
  v2: T.Val,
  +kk: String
) -> {T.wf.fresh(T.find.step(bb, v1, _u => T.rows.find([], kk)))
    == T.wf.fresh(T.find.step(bb, v2, _u => T.rows.find([], kk))) : Bool}:
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# a pair's value
def gd.pval(vv: T.Val) -> T.Val:
  match vv:
    case T.VPair{_n, v}:
      v
    case _:
      T.VBool{True{}}

# sealing a value keeps its name
def gd.sealed.name(
  xx: T.Val,
  +kk: String
) -> {T.wf.fresh(T.get([D2.sealed(xx)], kk)) == T.wf.fresh(T.get([xx], kk)) : Bool}:
  match xx:
    case T.VPair{+n, v}:
      match v:
        case T.VStr{+a0}:
          gd.fr.w(T.str.eq(n, kk), gd.pval(D2.sealed(T.VPair{n, T.VStr{a0}})), T.VStr{a0}, kk)
        case T.VSpan{+a0, +a1}:
          gd.fr.w(T.str.eq(n, kk), gd.pval(D2.sealed(T.VPair{n, T.VSpan{a0, a1}})), T.VSpan{a0, a1}, kk)
        case T.VInt{+a0, +a1}:
          gd.fr.w(T.str.eq(n, kk), gd.pval(D2.sealed(T.VPair{n, T.VInt{a0, a1}})), T.VInt{a0, a1}, kk)
        case T.VFlo{+a0, +a1}:
          gd.fr.w(T.str.eq(n, kk), gd.pval(D2.sealed(T.VPair{n, T.VFlo{a0, a1}})), T.VFlo{a0, a1}, kk)
        case T.VBool{+a0}:
          gd.fr.w(T.str.eq(n, kk), gd.pval(D2.sealed(T.VPair{n, T.VBool{a0}})), T.VBool{a0}, kk)
        case T.VWhen{+a0}:
          gd.fr.w(T.str.eq(n, kk), gd.pval(D2.sealed(T.VPair{n, T.VWhen{a0}})), T.VWhen{a0}, kk)
        case T.VArr{+a0}:
          gd.fr.w(T.str.eq(n, kk), gd.pval(D2.sealed(T.VPair{n, T.VArr{a0}})), T.VArr{a0}, kk)
        case T.VInl{+a0}:
          gd.fr.w(T.str.eq(n, kk), gd.pval(D2.sealed(T.VPair{n, T.VInl{a0}})), T.VInl{a0}, kk)
        case T.VHead{+a0, +a1}:
          gd.fr.w(T.str.eq(n, kk), gd.pval(D2.sealed(T.VPair{n, T.VHead{a0, a1}})), T.VHead{a0, a1}, kk)
        case T.VAot{+a0, +a1}:
          gd.fr.w(T.str.eq(n, kk), gd.pval(D2.sealed(T.VPair{n, T.VAot{a0, a1}})), T.VAot{a0, a1}, kk)
        case T.VAots{+a0, +a1}:
          gd.fr.w(T.str.eq(n, kk), gd.pval(D2.sealed(T.VPair{n, T.VAots{a0, a1}})), T.VAots{a0, a1}, kk)
        case T.VPair{+a0, +a1}:
          gd.fr.w(T.str.eq(n, kk), gd.pval(D2.sealed(T.VPair{n, T.VPair{a0, a1}})), T.VPair{a0, a1}, kk)
    case T.VStr{_a0}:
      {==}
    case T.VSpan{_a0, _a1}:
      {==}
    case T.VInt{_a0, _a1}:
      {==}
    case T.VFlo{_a0, _a1}:
      {==}
    case T.VBool{_a0}:
      {==}
    case T.VWhen{_a0}:
      {==}
    case T.VArr{_a0}:
      {==}
    case T.VInl{_a0}:
      {==}
    case T.VHead{_a0, _a1}:
      {==}
    case T.VAot{_a0, _a1}:
      {==}
    case T.VAots{_a0, _a1}:
      {==}

# sealing a list keeps its names
def gd.seal.names(
  tt: List<&2, T.Val>,
  +kk: String
) -> {T.wf.fresh(T.get(T.rows.seal(tt), kk)) == T.wf.fresh(T.get(tt, kk)) : Bool}:
  match tt:
    case []:
      {==}
    case +x <> +t:
      Equal.trans(Bool, T.wf.fresh(T.get(T.rows.seal(x <> t), kk)),
        T.wf.fresh(T.get(List.append(&2, T.Val, T.rows.seal(t), [D2.sealed(x)]), kk)),
        T.wf.fresh(T.get(x <> t, kk)),
        Equal.cong(List<&2, T.Val>, Bool, ll => T.wf.fresh(T.get(ll, kk)), T.rows.seal(x <> t),
          List.append(&2, T.Val, T.rows.seal(t), [D2.sealed(x)]), L2.seal_puts_newest_last(x, t)),
        Equal.trans(Bool, T.wf.fresh(T.get(List.append(&2, T.Val, T.rows.seal(t), [D2.sealed(x)]), kk)),
          Bool.and(T.wf.fresh(T.get(T.rows.seal(t), kk)), T.wf.fresh(T.get([D2.sealed(x)], kk))),
          T.wf.fresh(T.get(x <> t, kk)),
          gd.fr.app(T.rows.seal(t), [D2.sealed(x)], kk),
          Equal.trans(Bool, Bool.and(T.wf.fresh(T.get(T.rows.seal(t), kk)), T.wf.fresh(T.get([D2.sealed(x)], kk))),
            Bool.and(T.wf.fresh(T.get(t, kk)), T.wf.fresh(T.get([x], kk))),
            T.wf.fresh(T.get(x <> t, kk)),
            gd.and.cong(T.wf.fresh(T.get(T.rows.seal(t), kk)), T.wf.fresh(T.get(t, kk)),
              T.wf.fresh(T.get([D2.sealed(x)], kk)), T.wf.fresh(T.get([x], kk)),
              gd.seal.names(t, kk), gd.sealed.name(x, kk)),
            Equal.trans(Bool, Bool.and(T.wf.fresh(T.get(t, kk)), T.wf.fresh(T.get([x], kk))),
              Bool.and(T.wf.fresh(T.get([x], kk)), T.wf.fresh(T.get(t, kk))),
              T.wf.fresh(T.get(x <> t, kk)),
              M1.and.comm(T.wf.fresh(T.get(t, kk)), T.wf.fresh(T.get([x], kk))),
              Equal.sym(Bool, T.wf.fresh(T.get(x <> t, kk)),
                Bool.and(T.wf.fresh(T.get([x], kk)), T.wf.fresh(T.get(t, kk))), gd.fr.app([x], t, kk))))))

# a list with one more value after it holds something
def gd.app.some(
  aa: List<&2, T.Val>,
  yy: T.Val
) -> {Bool.not(List.is_empty(&2, T.Val, List.append(&2, T.Val, aa, [yy]))) == True{} : Bool}:
  match aa:
    case []:
      {==}
    case _h <> _t:
      {==}

# sealing an array of tables that holds an element leaves one
def gd.seal.some(
  el: List<&2, T.Val>,
  +ee: {Bool.not(List.is_empty(&2, T.Val, el)) == True{} : Bool}
) -> {Bool.not(List.is_empty(&2, T.Val, T.rows.seal(el))) == True{} : Bool}:
  match el:
    case []:
      Eq.bit.absurd(&2, {Bool.not(List.is_empty(&2, T.Val, T.rows.seal([]))) == True{} : Bool}, ee)
    case +x <> +t:
      Equal.trans(Bool, Bool.not(List.is_empty(&2, T.Val, T.rows.seal(x <> t))),
        Bool.not(List.is_empty(&2, T.Val, List.append(&2, T.Val, T.rows.seal(t), [D2.sealed(x)]))), True{},
        Equal.cong(List<&2, T.Val>, Bool, ll => Bool.not(List.is_empty(&2, T.Val, ll)), T.rows.seal(x <> t),
          List.append(&2, T.Val, T.rows.seal(t), [D2.sealed(x)]), L2.seal_puts_newest_last(x, t)),
        gd.app.some(T.rows.seal(t), D2.sealed(x)))

# one value sealed onto the sealed rest
def gd.s.step(
  +xx: T.Val,
  +t: List<&2, T.Val>,
  +at: T.WfAt,
  +et: {T.wf.go(T.rows.seal(t), at) == True{} : Bool},
  +e1: {T.wf.go([D2.sealed(xx)], at) == True{} : Bool},
  +ef: {gd.fy(T.rows.seal(t), D2.sealed(xx)) == True{} : Bool}
) -> {T.wf.go(T.rows.seal(xx <> t), at) == True{} : Bool}:
  Equal.trans(Bool, T.wf.go(T.rows.seal(xx <> t), at),
    T.wf.go(List.append(&2, T.Val, T.rows.seal(t), [D2.sealed(xx)]), at), True{},
    Equal.cong(List<&2, T.Val>, Bool, ll => T.wf.go(ll, at), T.rows.seal(xx <> t),
      List.append(&2, T.Val, T.rows.seal(t), [D2.sealed(xx)]), L2.seal_puts_newest_last(xx, t)),
    gd.w1(T.rows.seal(t), D2.sealed(xx), at, et, e1, ef))

# sealing keeps a list well-formed wherever it sits: tables, arrays of
# tables and inline tables come out reversed, arrays in order, every table
# inside sealed the same way
def gd.S(
  ll: List<&2, T.Val>,
  +at: T.WfAt,
  +ee: {T.wf.go(ll, at) == True{} : Bool}
) -> {T.wf.go(T.rows.seal(ll), at) == True{} : Bool}:
  match ll:
    case []:
      {==}
    case T.VStr{+r} <> +t:
      match at:
        case T.WfRows{+h}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VStr{r} <> t), T.WfRows{h}) == True{} : Bool},
              M4.gd.l(M4.gd.h1(T.VStr{r},
            t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}), M4.gd.gen.un(T.VStr{r}, t, T.WfRows{h}, ee)))
        case T.WfInl{}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VStr{r} <> t), T.WfInl{}) == True{} : Bool},
              M4.gd.l(M4.gd.h1(T.VStr{r},
            t, T.WfInl{}), T.wf.go(t, T.WfInl{}), M4.gd.gen.un(T.VStr{r}, t, T.WfInl{}, ee)))
        case T.WfItems{}:
          gd.s.step(T.VStr{r}, t, T.WfItems{},
            gd.S(t, T.WfItems{}, M4.gd.r(M4.gd.h1(T.VStr{r}, t, T.WfItems{}), T.wf.go(t, T.WfItems{}),
                M4.gd.gen.un(T.VStr{r},
              t, T.WfItems{}, ee))),
            M4.gd.gen.mk(T.VStr{r}, [], T.WfItems{}, M4.gd.l(M4.gd.h1(T.VStr{r}, t, T.WfItems{}), T.wf.go(t,
                T.WfItems{}),
              M4.gd.gen.un(T.VStr{r}, t, T.WfItems{}, ee)), {==}),
            {==})
        case T.WfElems{+h}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VStr{r} <> t), T.WfElems{h}) == True{} : Bool},
            M4.gd.l(M4.gd.h1(T.VStr{r}, t, T.WfElems{h}), T.wf.go(t, T.WfElems{h}), M4.gd.gen.un(T.VStr{r}, t,
                T.WfElems{h},
            ee)))
    case T.VSpan{+p, +r} <> +t:
      match at:
        case T.WfRows{+h}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VSpan{p, r} <> t), T.WfRows{h}) == True{} : Bool},
            M4.gd.l(M4.gd.h1(T.VSpan{p, r}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}), M4.gd.gen.un(T.VSpan{p, r}, t,
            T.WfRows{h}, ee)))
        case T.WfInl{}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VSpan{p, r} <> t), T.WfInl{}) == True{} : Bool},
            M4.gd.l(M4.gd.h1(T.VSpan{p, r}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}), M4.gd.gen.un(T.VSpan{p, r}, t,
                T.WfInl{}, ee)))
        case T.WfItems{}:
          gd.s.step(T.VSpan{p, r}, t, T.WfItems{},
            gd.S(t, T.WfItems{}, M4.gd.r(M4.gd.h1(T.VSpan{p, r}, t, T.WfItems{}), T.wf.go(t, T.WfItems{}),
              M4.gd.gen.un(T.VSpan{p, r}, t, T.WfItems{}, ee))),
            M4.gd.gen.mk(T.VSpan{p, r}, [], T.WfItems{}, M4.gd.l(M4.gd.h1(T.VSpan{p, r}, t, T.WfItems{}), T.wf.go(t,
              T.WfItems{}), M4.gd.gen.un(T.VSpan{p, r}, t, T.WfItems{}, ee)), {==}),
            {==})
        case T.WfElems{+h}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VSpan{p, r} <> t), T.WfElems{h}) == True{} : Bool},
            M4.gd.l(M4.gd.h1(T.VSpan{p, r}, t, T.WfElems{h}), T.wf.go(t, T.WfElems{h}), M4.gd.gen.un(T.VSpan{p, r}, t,
            T.WfElems{h}, ee)))
    case T.VInt{+p, +r} <> +t:
      match at:
        case T.WfRows{+h}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VInt{p, r} <> t), T.WfRows{h}) == True{} : Bool},
            M4.gd.l(M4.gd.h1(T.VInt{p, r}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}), M4.gd.gen.un(T.VInt{p, r}, t,
                T.WfRows{h},
            ee)))
        case T.WfInl{}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VInt{p, r} <> t), T.WfInl{}) == True{} : Bool},
              M4.gd.l(M4.gd.h1(T.VInt{p,
            r}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}), M4.gd.gen.un(T.VInt{p, r}, t, T.WfInl{}, ee)))
        case T.WfItems{}:
          gd.s.step(T.VInt{p, r}, t, T.WfItems{},
            gd.S(t, T.WfItems{}, M4.gd.r(M4.gd.h1(T.VInt{p, r}, t, T.WfItems{}), T.wf.go(t, T.WfItems{}),
                M4.gd.gen.un(T.VInt{p,
              r}, t, T.WfItems{}, ee))),
            M4.gd.gen.mk(T.VInt{p, r}, [], T.WfItems{}, M4.gd.l(M4.gd.h1(T.VInt{p, r}, t, T.WfItems{}), T.wf.go(t,
                T.WfItems{}),
              M4.gd.gen.un(T.VInt{p, r}, t, T.WfItems{}, ee)), {==}),
            {==})
        case T.WfElems{+h}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VInt{p, r} <> t), T.WfElems{h}) == True{} : Bool},
            M4.gd.l(M4.gd.h1(T.VInt{p, r}, t, T.WfElems{h}), T.wf.go(t, T.WfElems{h}), M4.gd.gen.un(T.VInt{p, r}, t,
            T.WfElems{h}, ee)))
    case T.VFlo{+p, +r} <> +t:
      match at:
        case T.WfRows{+h}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VFlo{p, r} <> t), T.WfRows{h}) == True{} : Bool},
            M4.gd.l(M4.gd.h1(T.VFlo{p, r}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}), M4.gd.gen.un(T.VFlo{p, r}, t,
                T.WfRows{h},
            ee)))
        case T.WfInl{}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VFlo{p, r} <> t), T.WfInl{}) == True{} : Bool},
              M4.gd.l(M4.gd.h1(T.VFlo{p,
            r}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}), M4.gd.gen.un(T.VFlo{p, r}, t, T.WfInl{}, ee)))
        case T.WfItems{}:
          gd.s.step(T.VFlo{p, r}, t, T.WfItems{},
            gd.S(t, T.WfItems{}, M4.gd.r(M4.gd.h1(T.VFlo{p, r}, t, T.WfItems{}), T.wf.go(t, T.WfItems{}),
                M4.gd.gen.un(T.VFlo{p,
              r}, t, T.WfItems{}, ee))),
            M4.gd.gen.mk(T.VFlo{p, r}, [], T.WfItems{}, M4.gd.l(M4.gd.h1(T.VFlo{p, r}, t, T.WfItems{}), T.wf.go(t,
                T.WfItems{}),
              M4.gd.gen.un(T.VFlo{p, r}, t, T.WfItems{}, ee)), {==}),
            {==})
        case T.WfElems{+h}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VFlo{p, r} <> t), T.WfElems{h}) == True{} : Bool},
            M4.gd.l(M4.gd.h1(T.VFlo{p, r}, t, T.WfElems{h}), T.wf.go(t, T.WfElems{h}), M4.gd.gen.un(T.VFlo{p, r}, t,
            T.WfElems{h}, ee)))
    case T.VBool{+r} <> +t:
      match at:
        case T.WfRows{+h}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VBool{r} <> t), T.WfRows{h}) == True{} : Bool},
            M4.gd.l(M4.gd.h1(T.VBool{r}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}), M4.gd.gen.un(T.VBool{r}, t,
                T.WfRows{h}, ee)))
        case T.WfInl{}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VBool{r} <> t), T.WfInl{}) == True{} : Bool},
              M4.gd.l(M4.gd.h1(T.VBool{r},
            t, T.WfInl{}), T.wf.go(t, T.WfInl{}), M4.gd.gen.un(T.VBool{r}, t, T.WfInl{}, ee)))
        case T.WfItems{}:
          gd.s.step(T.VBool{r}, t, T.WfItems{},
            gd.S(t, T.WfItems{}, M4.gd.r(M4.gd.h1(T.VBool{r}, t, T.WfItems{}), T.wf.go(t, T.WfItems{}),
                M4.gd.gen.un(T.VBool{r},
              t, T.WfItems{}, ee))),
            M4.gd.gen.mk(T.VBool{r}, [], T.WfItems{}, M4.gd.l(M4.gd.h1(T.VBool{r}, t, T.WfItems{}), T.wf.go(t,
                T.WfItems{}),
              M4.gd.gen.un(T.VBool{r}, t, T.WfItems{}, ee)), {==}),
            {==})
        case T.WfElems{+h}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VBool{r} <> t), T.WfElems{h}) == True{} : Bool},
            M4.gd.l(M4.gd.h1(T.VBool{r}, t, T.WfElems{h}), T.wf.go(t, T.WfElems{h}), M4.gd.gen.un(T.VBool{r}, t,
                T.WfElems{h},
            ee)))
    case T.VWhen{+r} <> +t:
      match at:
        case T.WfRows{+h}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VWhen{r} <> t), T.WfRows{h}) == True{} : Bool},
            M4.gd.l(M4.gd.h1(T.VWhen{r}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}), M4.gd.gen.un(T.VWhen{r}, t,
                T.WfRows{h}, ee)))
        case T.WfInl{}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VWhen{r} <> t), T.WfInl{}) == True{} : Bool},
              M4.gd.l(M4.gd.h1(T.VWhen{r},
            t, T.WfInl{}), T.wf.go(t, T.WfInl{}), M4.gd.gen.un(T.VWhen{r}, t, T.WfInl{}, ee)))
        case T.WfItems{}:
          gd.s.step(T.VWhen{r}, t, T.WfItems{},
            gd.S(t, T.WfItems{}, M4.gd.r(M4.gd.h1(T.VWhen{r}, t, T.WfItems{}), T.wf.go(t, T.WfItems{}),
                M4.gd.gen.un(T.VWhen{r},
              t, T.WfItems{}, ee))),
            M4.gd.gen.mk(T.VWhen{r}, [], T.WfItems{}, M4.gd.l(M4.gd.h1(T.VWhen{r}, t, T.WfItems{}), T.wf.go(t,
                T.WfItems{}),
              M4.gd.gen.un(T.VWhen{r}, t, T.WfItems{}, ee)), {==}),
            {==})
        case T.WfElems{+h}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VWhen{r} <> t), T.WfElems{h}) == True{} : Bool},
            M4.gd.l(M4.gd.h1(T.VWhen{r}, t, T.WfElems{h}), T.wf.go(t, T.WfElems{h}), M4.gd.gen.un(T.VWhen{r}, t,
                T.WfElems{h},
            ee)))
    case T.VArr{+r} <> +t:
      match at:
        case T.WfRows{+h}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VArr{r} <> t), T.WfRows{h}) == True{} : Bool},
              M4.gd.l(M4.gd.h1(T.VArr{r},
            t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}), M4.gd.gen.un(T.VArr{r}, t, T.WfRows{h}, ee)))
        case T.WfInl{}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VArr{r} <> t), T.WfInl{}) == True{} : Bool},
              M4.gd.l(M4.gd.h1(T.VArr{r},
            t, T.WfInl{}), T.wf.go(t, T.WfInl{}), M4.gd.gen.un(T.VArr{r}, t, T.WfInl{}, ee)))
        case T.WfItems{}:
          gd.s.step(T.VArr{r}, t, T.WfItems{},
            gd.S(t, T.WfItems{}, M4.gd.r(M4.gd.h1(T.VArr{r}, t, T.WfItems{}), T.wf.go(t, T.WfItems{}),
                M4.gd.gen.un(T.VArr{r},
              t, T.WfItems{}, ee))),
            M4.gd.gen.mk(T.VArr{List.reverse(&2, T.Val, T.rows.seal(r))}, [], T.WfItems{}, M4.gd.rev.it(T.rows.seal(r),
                [],
              gd.S(r, T.WfItems{}, M4.gd.l(M4.gd.h1(T.VArr{r}, t, T.WfItems{}), T.wf.go(t, T.WfItems{}),
                  M4.gd.gen.un(T.VArr{r},
              t, T.WfItems{}, ee))), {==}), {==}),
            {==})
        case T.WfElems{+h}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VArr{r} <> t), T.WfElems{h}) == True{} : Bool},
            M4.gd.l(M4.gd.h1(T.VArr{r}, t, T.WfElems{h}), T.wf.go(t, T.WfElems{h}), M4.gd.gen.un(T.VArr{r}, t,
                T.WfElems{h},
            ee)))
    case T.VInl{+r} <> +t:
      match at:
        case T.WfRows{+h}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VInl{r} <> t), T.WfRows{h}) == True{} : Bool},
              M4.gd.l(M4.gd.h1(T.VInl{r},
            t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}), M4.gd.gen.un(T.VInl{r}, t, T.WfRows{h}, ee)))
        case T.WfInl{}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VInl{r} <> t), T.WfInl{}) == True{} : Bool},
              M4.gd.l(M4.gd.h1(T.VInl{r},
            t, T.WfInl{}), T.wf.go(t, T.WfInl{}), M4.gd.gen.un(T.VInl{r}, t, T.WfInl{}, ee)))
        case T.WfItems{}:
          gd.s.step(T.VInl{r}, t, T.WfItems{},
            gd.S(t, T.WfItems{}, M4.gd.r(M4.gd.h1(T.VInl{r}, t, T.WfItems{}), T.wf.go(t, T.WfItems{}),
                M4.gd.gen.un(T.VInl{r},
              t, T.WfItems{}, ee))),
            M4.gd.gen.mk(T.VInl{T.rows.seal(r)}, [], T.WfItems{}, gd.S(r, T.WfInl{}, M4.gd.l(M4.gd.h1(T.VInl{r}, t,
              T.WfItems{}), T.wf.go(t, T.WfItems{}), M4.gd.gen.un(T.VInl{r}, t, T.WfItems{}, ee))), {==}),
            {==})
        case T.WfElems{+h}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VInl{r} <> t), T.WfElems{h}) == True{} : Bool},
            M4.gd.l(M4.gd.h1(T.VInl{r}, t, T.WfElems{h}), T.wf.go(t, T.WfElems{h}), M4.gd.gen.un(T.VInl{r}, t,
                T.WfElems{h},
            ee)))
    case T.VHead{+p, +r} <> +t:
      match at:
        case T.WfRows{+h}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VHead{p, r} <> t), T.WfRows{h}) == True{} : Bool},
            M4.gd.l(M4.gd.h1(T.VHead{p, r}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}), M4.gd.gen.un(T.VHead{p, r}, t,
            T.WfRows{h}, ee)))
        case T.WfInl{}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VHead{p, r} <> t), T.WfInl{}) == True{} : Bool},
            M4.gd.l(M4.gd.h1(T.VHead{p, r}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}), M4.gd.gen.un(T.VHead{p, r}, t,
                T.WfInl{}, ee)))
        case T.WfItems{}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VHead{p, r} <> t), T.WfItems{}) == True{} : Bool},
            M4.gd.l(M4.gd.h1(T.VHead{p, r}, t, T.WfItems{}), T.wf.go(t, T.WfItems{}), M4.gd.gen.un(T.VHead{p, r}, t,
            T.WfItems{}, ee)))
        case T.WfElems{+h}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VHead{p, r} <> t), T.WfElems{h}) == True{} : Bool},
            M4.gd.l(M4.gd.h1(T.VHead{p, r}, t, T.WfElems{h}), T.wf.go(t, T.WfElems{h}), M4.gd.gen.un(T.VHead{p, r}, t,
            T.WfElems{h}, ee)))
    case T.VAot{+p, +r} <> +t:
      match at:
        case T.WfRows{+h}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VAot{p, r} <> t), T.WfRows{h}) == True{} : Bool},
            M4.gd.l(M4.gd.h1(T.VAot{p, r}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}), M4.gd.gen.un(T.VAot{p, r}, t,
                T.WfRows{h},
            ee)))
        case T.WfInl{}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VAot{p, r} <> t), T.WfInl{}) == True{} : Bool},
              M4.gd.l(M4.gd.h1(T.VAot{p,
            r}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}), M4.gd.gen.un(T.VAot{p, r}, t, T.WfInl{}, ee)))
        case T.WfItems{}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VAot{p, r} <> t), T.WfItems{}) == True{} : Bool},
            M4.gd.l(M4.gd.h1(T.VAot{p, r}, t, T.WfItems{}), T.wf.go(t, T.WfItems{}), M4.gd.gen.un(T.VAot{p, r}, t,
                T.WfItems{},
            ee)))
        case T.WfElems{+h}:
          gd.s.step(T.VAot{p, r}, t, T.WfElems{h},
            gd.S(t, T.WfElems{h}, M4.gd.r(M4.gd.h1(T.VAot{p, r}, t, T.WfElems{h}), T.wf.go(t, T.WfElems{h}),
              M4.gd.gen.un(T.VAot{p, r}, t, T.WfElems{h}, ee))),
            M4.gd.gen.mk(T.VAot{p, T.rows.seal(r)}, [], T.WfElems{h}, M4.gd.tt(T.str.eq(p, h), T.wf.go(T.rows.seal(r),
              T.WfRows{p}), M4.gd.l(T.str.eq(p, h), T.wf.go(r, T.WfRows{p}), M4.gd.l(M4.gd.h1(T.VAot{p, r}, t,
                  T.WfElems{h}),
              T.wf.go(t, T.WfElems{h}), M4.gd.gen.un(T.VAot{p, r}, t, T.WfElems{h}, ee))),
              gd.S(r, T.WfRows{p}, M4.gd.r(T.str.eq(p, h), T.wf.go(r, T.WfRows{p}), M4.gd.l(M4.gd.h1(T.VAot{p, r}, t,
                T.WfElems{h}), T.wf.go(t, T.WfElems{h}), M4.gd.gen.un(T.VAot{p, r}, t, T.WfElems{h}, ee))))), {==}),
            {==})
    case T.VAots{+p, +r} <> +t:
      match at:
        case T.WfRows{+h}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VAots{p, r} <> t), T.WfRows{h}) == True{} : Bool},
            M4.gd.l(M4.gd.h1(T.VAots{p, r}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}), M4.gd.gen.un(T.VAots{p, r}, t,
            T.WfRows{h}, ee)))
        case T.WfInl{}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VAots{p, r} <> t), T.WfInl{}) == True{} : Bool},
            M4.gd.l(M4.gd.h1(T.VAots{p, r}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}), M4.gd.gen.un(T.VAots{p, r}, t,
                T.WfInl{}, ee)))
        case T.WfItems{}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VAots{p, r} <> t), T.WfItems{}) == True{} : Bool},
            M4.gd.l(M4.gd.h1(T.VAots{p, r}, t, T.WfItems{}), T.wf.go(t, T.WfItems{}), M4.gd.gen.un(T.VAots{p, r}, t,
            T.WfItems{}, ee)))
        case T.WfElems{+h}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VAots{p, r} <> t), T.WfElems{h}) == True{} : Bool},
            M4.gd.l(M4.gd.h1(T.VAots{p, r}, t, T.WfElems{h}), T.wf.go(t, T.WfElems{h}), M4.gd.gen.un(T.VAots{p, r}, t,
            T.WfElems{h}, ee)))
    case T.VPair{+n, T.VStr{+r}} <> +t:
      match at:
        case T.WfRows{+h}:
          gd.s.step(T.VPair{n, T.VStr{r}}, t, T.WfRows{h},
            gd.S(t, T.WfRows{h}, M4.gd.r(M4.gd.h1(T.VPair{n, T.VStr{r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}),
              M4.gd.gen.un(T.VPair{n, T.VStr{r}}, t, T.WfRows{h}, ee))),
            M4.gd.gen.mk(T.VPair{n, T.VStr{r}}, [], T.WfRows{h},
              M4.gd.tt(T.wf.key(n, []), M4.gd.pa(T.WfRows{h}, n, T.VStr{r}), M4.gd.tt(T.wf.text(n), True{},
                  M4.gd.l(T.wf.text(n),
                T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t), M4.gd.pa(T.WfRows{h}, n, T.VStr{r}),
                    M4.gd.l(M4.gd.h1(T.VPair{n,
                T.VStr{r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}), M4.gd.gen.un(T.VPair{n, T.VStr{r}}, t,
                T.WfRows{h}, ee)))), {==}),
                M4.gd.r(T.wf.key(n, t), M4.gd.pa(T.WfRows{h}, n, T.VStr{r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VStr{r}}, t,
                  T.WfRows{h}), T.wf.go(t, T.WfRows{h}), M4.gd.gen.un(T.VPair{n, T.VStr{r}}, t, T.WfRows{h}, ee)))),
              {==}),
            Equal.trans(Bool, T.wf.fresh(T.get(T.rows.seal(t), n)), T.wf.fresh(T.get(t, n)), True{},
              gd.seal.names(t, n), M4.gd.r(T.wf.text(n), T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t),
                  M4.gd.pa(T.WfRows{h},
                n, T.VStr{r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VStr{r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}),
                M4.gd.gen.un(T.VPair{n, T.VStr{r}}, t, T.WfRows{h}, ee))))))
        case T.WfInl{}:
          gd.s.step(T.VPair{n, T.VStr{r}}, t, T.WfInl{},
            gd.S(t, T.WfInl{}, M4.gd.r(M4.gd.h1(T.VPair{n, T.VStr{r}}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}),
              M4.gd.gen.un(T.VPair{n, T.VStr{r}}, t, T.WfInl{}, ee))),
            M4.gd.gen.mk(T.VPair{n, T.VStr{r}}, [], T.WfInl{},
              M4.gd.tt(T.wf.key(n, []), M4.gd.pa(T.WfInl{}, n, T.VStr{r}), M4.gd.tt(T.wf.text(n), True{},
                  M4.gd.l(T.wf.text(n),
                T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t), M4.gd.pa(T.WfInl{}, n, T.VStr{r}),
                    M4.gd.l(M4.gd.h1(T.VPair{n,
                T.VStr{r}}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}), M4.gd.gen.un(T.VPair{n, T.VStr{r}}, t, T.WfInl{},
                ee)))), {==}),
                M4.gd.r(T.wf.key(n, t), M4.gd.pa(T.WfInl{}, n, T.VStr{r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VStr{r}}, t,
                    T.WfInl{}),
                  T.wf.go(t, T.WfInl{}), M4.gd.gen.un(T.VPair{n, T.VStr{r}}, t, T.WfInl{}, ee)))),
              {==}),
            Equal.trans(Bool, T.wf.fresh(T.get(T.rows.seal(t), n)), T.wf.fresh(T.get(t, n)), True{},
              gd.seal.names(t, n), M4.gd.r(T.wf.text(n), T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t),
                  M4.gd.pa(T.WfInl{}, n,
                T.VStr{r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VStr{r}}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}),
                M4.gd.gen.un(T.VPair{n, T.VStr{r}}, t, T.WfInl{}, ee))))))
        case T.WfItems{}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VPair{n, T.VStr{r}} <> t), T.WfItems{}) == True{} : Bool},
            M4.gd.r(T.wf.key(n, t), False{}, M4.gd.l(M4.gd.h1(T.VPair{n, T.VStr{r}}, t, T.WfItems{}), T.wf.go(t,
                T.WfItems{}),
              M4.gd.gen.un(T.VPair{n, T.VStr{r}}, t, T.WfItems{}, ee))))
        case T.WfElems{+h}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VPair{n, T.VStr{r}} <> t), T.WfElems{h}) == True{} : Bool},
            M4.gd.r(T.wf.key(n, t), False{}, M4.gd.l(M4.gd.h1(T.VPair{n, T.VStr{r}}, t, T.WfElems{h}), T.wf.go(t,
                T.WfElems{h}),
              M4.gd.gen.un(T.VPair{n, T.VStr{r}}, t, T.WfElems{h}, ee))))
    case T.VPair{+n, T.VSpan{+p, +r}} <> +t:
      match at:
        case T.WfRows{+h}:
          gd.s.step(T.VPair{n, T.VSpan{p, r}}, t, T.WfRows{h},
            gd.S(t, T.WfRows{h}, M4.gd.r(M4.gd.h1(T.VPair{n, T.VSpan{p, r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}),
              M4.gd.gen.un(T.VPair{n, T.VSpan{p, r}}, t, T.WfRows{h}, ee))),
            M4.gd.gen.mk(T.VPair{n, T.VSpan{p, r}}, [], T.WfRows{h},
              M4.gd.tt(T.wf.key(n, []), M4.gd.pa(T.WfRows{h}, n, T.VSpan{p, r}), M4.gd.tt(T.wf.text(n), True{},
                M4.gd.l(T.wf.text(n), T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t), M4.gd.pa(T.WfRows{h}, n,
                    T.VSpan{p, r}),
                M4.gd.l(M4.gd.h1(T.VPair{n, T.VSpan{p, r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}),
                    M4.gd.gen.un(T.VPair{n,
                T.VSpan{p, r}}, t, T.WfRows{h}, ee)))), {==}),
                M4.gd.r(T.wf.key(n, t), M4.gd.pa(T.WfRows{h}, n, T.VSpan{p, r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VSpan{p,
                    r}}, t,
                  T.WfRows{h}), T.wf.go(t, T.WfRows{h}), M4.gd.gen.un(T.VPair{n, T.VSpan{p, r}}, t, T.WfRows{h}, ee)))),
              {==}),
            Equal.trans(Bool, T.wf.fresh(T.get(T.rows.seal(t), n)), T.wf.fresh(T.get(t, n)), True{},
              gd.seal.names(t, n), M4.gd.r(T.wf.text(n), T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t),
                  M4.gd.pa(T.WfRows{h},
                n, T.VSpan{p, r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VSpan{p, r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}),
                M4.gd.gen.un(T.VPair{n, T.VSpan{p, r}}, t, T.WfRows{h}, ee))))))
        case T.WfInl{}:
          gd.s.step(T.VPair{n, T.VSpan{p, r}}, t, T.WfInl{},
            gd.S(t, T.WfInl{}, M4.gd.r(M4.gd.h1(T.VPair{n, T.VSpan{p, r}}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}),
              M4.gd.gen.un(T.VPair{n, T.VSpan{p, r}}, t, T.WfInl{}, ee))),
            M4.gd.gen.mk(T.VPair{n, T.VSpan{p, r}}, [], T.WfInl{},
              M4.gd.tt(T.wf.key(n, []), M4.gd.pa(T.WfInl{}, n, T.VSpan{p, r}), M4.gd.tt(T.wf.text(n), True{},
                  M4.gd.l(T.wf.text(n),
                T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t), M4.gd.pa(T.WfInl{}, n, T.VSpan{p, r}),
                    M4.gd.l(M4.gd.h1(T.VPair{n,
                T.VSpan{p, r}}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}), M4.gd.gen.un(T.VPair{n, T.VSpan{p, r}}, t,
                T.WfInl{}, ee)))), {==}),
                M4.gd.r(T.wf.key(n, t), M4.gd.pa(T.WfInl{}, n, T.VSpan{p, r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VSpan{p,
                    r}}, t,
                  T.WfInl{}), T.wf.go(t, T.WfInl{}), M4.gd.gen.un(T.VPair{n, T.VSpan{p, r}}, t, T.WfInl{}, ee)))),
              {==}),
            Equal.trans(Bool, T.wf.fresh(T.get(T.rows.seal(t), n)), T.wf.fresh(T.get(t, n)), True{},
              gd.seal.names(t, n), M4.gd.r(T.wf.text(n), T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t),
                  M4.gd.pa(T.WfInl{}, n,
                T.VSpan{p, r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VSpan{p, r}}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}),
                M4.gd.gen.un(T.VPair{n, T.VSpan{p, r}}, t, T.WfInl{}, ee))))))
        case T.WfItems{}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VPair{n, T.VSpan{p, r}} <> t), T.WfItems{}) == True{} : Bool},
            M4.gd.r(T.wf.key(n, t), False{}, M4.gd.l(M4.gd.h1(T.VPair{n, T.VSpan{p, r}}, t, T.WfItems{}), T.wf.go(t,
              T.WfItems{}), M4.gd.gen.un(T.VPair{n, T.VSpan{p, r}}, t, T.WfItems{}, ee))))
        case T.WfElems{+h}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VPair{n, T.VSpan{p, r}} <> t), T.WfElems{h}) == True{} : Bool},
            M4.gd.r(T.wf.key(n, t), False{}, M4.gd.l(M4.gd.h1(T.VPair{n, T.VSpan{p, r}}, t, T.WfElems{h}), T.wf.go(t,
              T.WfElems{h}), M4.gd.gen.un(T.VPair{n, T.VSpan{p, r}}, t, T.WfElems{h}, ee))))
    case T.VPair{+n, T.VInt{+p, +r}} <> +t:
      match at:
        case T.WfRows{+h}:
          gd.s.step(T.VPair{n, T.VInt{p, r}}, t, T.WfRows{h},
            gd.S(t, T.WfRows{h}, M4.gd.r(M4.gd.h1(T.VPair{n, T.VInt{p, r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}),
              M4.gd.gen.un(T.VPair{n, T.VInt{p, r}}, t, T.WfRows{h}, ee))),
            M4.gd.gen.mk(T.VPair{n, T.VInt{p, r}}, [], T.WfRows{h},
              M4.gd.tt(T.wf.key(n, []), M4.gd.pa(T.WfRows{h}, n, T.VInt{p, r}), M4.gd.tt(T.wf.text(n), True{},
                M4.gd.l(T.wf.text(n), T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t), M4.gd.pa(T.WfRows{h}, n,
                    T.VInt{p, r}),
                M4.gd.l(M4.gd.h1(T.VPair{n, T.VInt{p, r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}),
                    M4.gd.gen.un(T.VPair{n,
                T.VInt{p, r}}, t, T.WfRows{h}, ee)))), {==}),
                M4.gd.r(T.wf.key(n, t), M4.gd.pa(T.WfRows{h}, n, T.VInt{p, r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VInt{p,
                    r}}, t,
                  T.WfRows{h}), T.wf.go(t, T.WfRows{h}), M4.gd.gen.un(T.VPair{n, T.VInt{p, r}}, t, T.WfRows{h}, ee)))),
              {==}),
            Equal.trans(Bool, T.wf.fresh(T.get(T.rows.seal(t), n)), T.wf.fresh(T.get(t, n)), True{},
              gd.seal.names(t, n), M4.gd.r(T.wf.text(n), T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t),
                  M4.gd.pa(T.WfRows{h},
                n, T.VInt{p, r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VInt{p, r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}),
                M4.gd.gen.un(T.VPair{n, T.VInt{p, r}}, t, T.WfRows{h}, ee))))))
        case T.WfInl{}:
          gd.s.step(T.VPair{n, T.VInt{p, r}}, t, T.WfInl{},
            gd.S(t, T.WfInl{}, M4.gd.r(M4.gd.h1(T.VPair{n, T.VInt{p, r}}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}),
              M4.gd.gen.un(T.VPair{n, T.VInt{p, r}}, t, T.WfInl{}, ee))),
            M4.gd.gen.mk(T.VPair{n, T.VInt{p, r}}, [], T.WfInl{},
              M4.gd.tt(T.wf.key(n, []), M4.gd.pa(T.WfInl{}, n, T.VInt{p, r}), M4.gd.tt(T.wf.text(n), True{},
                  M4.gd.l(T.wf.text(n),
                T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t), M4.gd.pa(T.WfInl{}, n, T.VInt{p, r}),
                    M4.gd.l(M4.gd.h1(T.VPair{n,
                T.VInt{p, r}}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}), M4.gd.gen.un(T.VPair{n, T.VInt{p, r}}, t,
                T.WfInl{}, ee)))), {==}),
                M4.gd.r(T.wf.key(n, t), M4.gd.pa(T.WfInl{}, n, T.VInt{p, r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VInt{p,
                    r}}, t,
                  T.WfInl{}), T.wf.go(t, T.WfInl{}), M4.gd.gen.un(T.VPair{n, T.VInt{p, r}}, t, T.WfInl{}, ee)))),
              {==}),
            Equal.trans(Bool, T.wf.fresh(T.get(T.rows.seal(t), n)), T.wf.fresh(T.get(t, n)), True{},
              gd.seal.names(t, n), M4.gd.r(T.wf.text(n), T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t),
                  M4.gd.pa(T.WfInl{}, n,
                T.VInt{p, r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VInt{p, r}}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}),
                M4.gd.gen.un(T.VPair{n, T.VInt{p, r}}, t, T.WfInl{}, ee))))))
        case T.WfItems{}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VPair{n, T.VInt{p, r}} <> t), T.WfItems{}) == True{} : Bool},
            M4.gd.r(T.wf.key(n, t), False{}, M4.gd.l(M4.gd.h1(T.VPair{n, T.VInt{p, r}}, t, T.WfItems{}), T.wf.go(t,
              T.WfItems{}), M4.gd.gen.un(T.VPair{n, T.VInt{p, r}}, t, T.WfItems{}, ee))))
        case T.WfElems{+h}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VPair{n, T.VInt{p, r}} <> t), T.WfElems{h}) == True{} : Bool},
            M4.gd.r(T.wf.key(n, t), False{}, M4.gd.l(M4.gd.h1(T.VPair{n, T.VInt{p, r}}, t, T.WfElems{h}), T.wf.go(t,
              T.WfElems{h}), M4.gd.gen.un(T.VPair{n, T.VInt{p, r}}, t, T.WfElems{h}, ee))))
    case T.VPair{+n, T.VFlo{+p, +r}} <> +t:
      match at:
        case T.WfRows{+h}:
          gd.s.step(T.VPair{n, T.VFlo{p, r}}, t, T.WfRows{h},
            gd.S(t, T.WfRows{h}, M4.gd.r(M4.gd.h1(T.VPair{n, T.VFlo{p, r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}),
              M4.gd.gen.un(T.VPair{n, T.VFlo{p, r}}, t, T.WfRows{h}, ee))),
            M4.gd.gen.mk(T.VPair{n, T.VFlo{p, r}}, [], T.WfRows{h},
              M4.gd.tt(T.wf.key(n, []), M4.gd.pa(T.WfRows{h}, n, T.VFlo{p, r}), M4.gd.tt(T.wf.text(n), True{},
                M4.gd.l(T.wf.text(n), T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t), M4.gd.pa(T.WfRows{h}, n,
                    T.VFlo{p, r}),
                M4.gd.l(M4.gd.h1(T.VPair{n, T.VFlo{p, r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}),
                    M4.gd.gen.un(T.VPair{n,
                T.VFlo{p, r}}, t, T.WfRows{h}, ee)))), {==}),
                M4.gd.r(T.wf.key(n, t), M4.gd.pa(T.WfRows{h}, n, T.VFlo{p, r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VFlo{p,
                    r}}, t,
                  T.WfRows{h}), T.wf.go(t, T.WfRows{h}), M4.gd.gen.un(T.VPair{n, T.VFlo{p, r}}, t, T.WfRows{h}, ee)))),
              {==}),
            Equal.trans(Bool, T.wf.fresh(T.get(T.rows.seal(t), n)), T.wf.fresh(T.get(t, n)), True{},
              gd.seal.names(t, n), M4.gd.r(T.wf.text(n), T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t),
                  M4.gd.pa(T.WfRows{h},
                n, T.VFlo{p, r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VFlo{p, r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}),
                M4.gd.gen.un(T.VPair{n, T.VFlo{p, r}}, t, T.WfRows{h}, ee))))))
        case T.WfInl{}:
          gd.s.step(T.VPair{n, T.VFlo{p, r}}, t, T.WfInl{},
            gd.S(t, T.WfInl{}, M4.gd.r(M4.gd.h1(T.VPair{n, T.VFlo{p, r}}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}),
              M4.gd.gen.un(T.VPair{n, T.VFlo{p, r}}, t, T.WfInl{}, ee))),
            M4.gd.gen.mk(T.VPair{n, T.VFlo{p, r}}, [], T.WfInl{},
              M4.gd.tt(T.wf.key(n, []), M4.gd.pa(T.WfInl{}, n, T.VFlo{p, r}), M4.gd.tt(T.wf.text(n), True{},
                  M4.gd.l(T.wf.text(n),
                T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t), M4.gd.pa(T.WfInl{}, n, T.VFlo{p, r}),
                    M4.gd.l(M4.gd.h1(T.VPair{n,
                T.VFlo{p, r}}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}), M4.gd.gen.un(T.VPair{n, T.VFlo{p, r}}, t,
                T.WfInl{}, ee)))), {==}),
                M4.gd.r(T.wf.key(n, t), M4.gd.pa(T.WfInl{}, n, T.VFlo{p, r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VFlo{p,
                    r}}, t,
                  T.WfInl{}), T.wf.go(t, T.WfInl{}), M4.gd.gen.un(T.VPair{n, T.VFlo{p, r}}, t, T.WfInl{}, ee)))),
              {==}),
            Equal.trans(Bool, T.wf.fresh(T.get(T.rows.seal(t), n)), T.wf.fresh(T.get(t, n)), True{},
              gd.seal.names(t, n), M4.gd.r(T.wf.text(n), T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t),
                  M4.gd.pa(T.WfInl{}, n,
                T.VFlo{p, r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VFlo{p, r}}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}),
                M4.gd.gen.un(T.VPair{n, T.VFlo{p, r}}, t, T.WfInl{}, ee))))))
        case T.WfItems{}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VPair{n, T.VFlo{p, r}} <> t), T.WfItems{}) == True{} : Bool},
            M4.gd.r(T.wf.key(n, t), False{}, M4.gd.l(M4.gd.h1(T.VPair{n, T.VFlo{p, r}}, t, T.WfItems{}), T.wf.go(t,
              T.WfItems{}), M4.gd.gen.un(T.VPair{n, T.VFlo{p, r}}, t, T.WfItems{}, ee))))
        case T.WfElems{+h}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VPair{n, T.VFlo{p, r}} <> t), T.WfElems{h}) == True{} : Bool},
            M4.gd.r(T.wf.key(n, t), False{}, M4.gd.l(M4.gd.h1(T.VPair{n, T.VFlo{p, r}}, t, T.WfElems{h}), T.wf.go(t,
              T.WfElems{h}), M4.gd.gen.un(T.VPair{n, T.VFlo{p, r}}, t, T.WfElems{h}, ee))))
    case T.VPair{+n, T.VBool{+r}} <> +t:
      match at:
        case T.WfRows{+h}:
          gd.s.step(T.VPair{n, T.VBool{r}}, t, T.WfRows{h},
            gd.S(t, T.WfRows{h}, M4.gd.r(M4.gd.h1(T.VPair{n, T.VBool{r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}),
              M4.gd.gen.un(T.VPair{n, T.VBool{r}}, t, T.WfRows{h}, ee))),
            M4.gd.gen.mk(T.VPair{n, T.VBool{r}}, [], T.WfRows{h},
              M4.gd.tt(T.wf.key(n, []), M4.gd.pa(T.WfRows{h}, n, T.VBool{r}), M4.gd.tt(T.wf.text(n), True{},
                  M4.gd.l(T.wf.text(n),
                T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t), M4.gd.pa(T.WfRows{h}, n, T.VBool{r}),
                    M4.gd.l(M4.gd.h1(T.VPair{n,
                T.VBool{r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}), M4.gd.gen.un(T.VPair{n, T.VBool{r}}, t,
                T.WfRows{h}, ee)))), {==}),
                M4.gd.r(T.wf.key(n, t), M4.gd.pa(T.WfRows{h}, n, T.VBool{r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VBool{r}},
                    t,
                  T.WfRows{h}), T.wf.go(t, T.WfRows{h}), M4.gd.gen.un(T.VPair{n, T.VBool{r}}, t, T.WfRows{h}, ee)))),
              {==}),
            Equal.trans(Bool, T.wf.fresh(T.get(T.rows.seal(t), n)), T.wf.fresh(T.get(t, n)), True{},
              gd.seal.names(t, n), M4.gd.r(T.wf.text(n), T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t),
                  M4.gd.pa(T.WfRows{h},
                n, T.VBool{r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VBool{r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}),
                M4.gd.gen.un(T.VPair{n, T.VBool{r}}, t, T.WfRows{h}, ee))))))
        case T.WfInl{}:
          gd.s.step(T.VPair{n, T.VBool{r}}, t, T.WfInl{},
            gd.S(t, T.WfInl{}, M4.gd.r(M4.gd.h1(T.VPair{n, T.VBool{r}}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}),
              M4.gd.gen.un(T.VPair{n, T.VBool{r}}, t, T.WfInl{}, ee))),
            M4.gd.gen.mk(T.VPair{n, T.VBool{r}}, [], T.WfInl{},
              M4.gd.tt(T.wf.key(n, []), M4.gd.pa(T.WfInl{}, n, T.VBool{r}), M4.gd.tt(T.wf.text(n), True{},
                  M4.gd.l(T.wf.text(n),
                T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t), M4.gd.pa(T.WfInl{}, n, T.VBool{r}),
                    M4.gd.l(M4.gd.h1(T.VPair{n,
                T.VBool{r}}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}), M4.gd.gen.un(T.VPair{n, T.VBool{r}}, t, T.WfInl{},
                ee)))), {==}),
                M4.gd.r(T.wf.key(n, t), M4.gd.pa(T.WfInl{}, n, T.VBool{r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VBool{r}}, t,
                    T.WfInl{}),
                  T.wf.go(t, T.WfInl{}), M4.gd.gen.un(T.VPair{n, T.VBool{r}}, t, T.WfInl{}, ee)))),
              {==}),
            Equal.trans(Bool, T.wf.fresh(T.get(T.rows.seal(t), n)), T.wf.fresh(T.get(t, n)), True{},
              gd.seal.names(t, n), M4.gd.r(T.wf.text(n), T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t),
                  M4.gd.pa(T.WfInl{}, n,
                T.VBool{r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VBool{r}}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}),
                M4.gd.gen.un(T.VPair{n, T.VBool{r}}, t, T.WfInl{}, ee))))))
        case T.WfItems{}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VPair{n, T.VBool{r}} <> t), T.WfItems{}) == True{} : Bool},
            M4.gd.r(T.wf.key(n, t), False{}, M4.gd.l(M4.gd.h1(T.VPair{n, T.VBool{r}}, t, T.WfItems{}), T.wf.go(t,
                T.WfItems{}),
              M4.gd.gen.un(T.VPair{n, T.VBool{r}}, t, T.WfItems{}, ee))))
        case T.WfElems{+h}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VPair{n, T.VBool{r}} <> t), T.WfElems{h}) == True{} : Bool},
            M4.gd.r(T.wf.key(n, t), False{}, M4.gd.l(M4.gd.h1(T.VPair{n, T.VBool{r}}, t, T.WfElems{h}), T.wf.go(t,
              T.WfElems{h}), M4.gd.gen.un(T.VPair{n, T.VBool{r}}, t, T.WfElems{h}, ee))))
    case T.VPair{+n, T.VWhen{+r}} <> +t:
      match at:
        case T.WfRows{+h}:
          gd.s.step(T.VPair{n, T.VWhen{r}}, t, T.WfRows{h},
            gd.S(t, T.WfRows{h}, M4.gd.r(M4.gd.h1(T.VPair{n, T.VWhen{r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}),
              M4.gd.gen.un(T.VPair{n, T.VWhen{r}}, t, T.WfRows{h}, ee))),
            M4.gd.gen.mk(T.VPair{n, T.VWhen{r}}, [], T.WfRows{h},
              M4.gd.tt(T.wf.key(n, []), M4.gd.pa(T.WfRows{h}, n, T.VWhen{r}), M4.gd.tt(T.wf.text(n), True{},
                  M4.gd.l(T.wf.text(n),
                T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t), M4.gd.pa(T.WfRows{h}, n, T.VWhen{r}),
                    M4.gd.l(M4.gd.h1(T.VPair{n,
                T.VWhen{r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}), M4.gd.gen.un(T.VPair{n, T.VWhen{r}}, t,
                T.WfRows{h}, ee)))), {==}),
                M4.gd.r(T.wf.key(n, t), M4.gd.pa(T.WfRows{h}, n, T.VWhen{r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VWhen{r}},
                    t,
                  T.WfRows{h}), T.wf.go(t, T.WfRows{h}), M4.gd.gen.un(T.VPair{n, T.VWhen{r}}, t, T.WfRows{h}, ee)))),
              {==}),
            Equal.trans(Bool, T.wf.fresh(T.get(T.rows.seal(t), n)), T.wf.fresh(T.get(t, n)), True{},
              gd.seal.names(t, n), M4.gd.r(T.wf.text(n), T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t),
                  M4.gd.pa(T.WfRows{h},
                n, T.VWhen{r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VWhen{r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}),
                M4.gd.gen.un(T.VPair{n, T.VWhen{r}}, t, T.WfRows{h}, ee))))))
        case T.WfInl{}:
          gd.s.step(T.VPair{n, T.VWhen{r}}, t, T.WfInl{},
            gd.S(t, T.WfInl{}, M4.gd.r(M4.gd.h1(T.VPair{n, T.VWhen{r}}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}),
              M4.gd.gen.un(T.VPair{n, T.VWhen{r}}, t, T.WfInl{}, ee))),
            M4.gd.gen.mk(T.VPair{n, T.VWhen{r}}, [], T.WfInl{},
              M4.gd.tt(T.wf.key(n, []), M4.gd.pa(T.WfInl{}, n, T.VWhen{r}), M4.gd.tt(T.wf.text(n), True{},
                  M4.gd.l(T.wf.text(n),
                T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t), M4.gd.pa(T.WfInl{}, n, T.VWhen{r}),
                    M4.gd.l(M4.gd.h1(T.VPair{n,
                T.VWhen{r}}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}), M4.gd.gen.un(T.VPair{n, T.VWhen{r}}, t, T.WfInl{},
                ee)))), {==}),
                M4.gd.r(T.wf.key(n, t), M4.gd.pa(T.WfInl{}, n, T.VWhen{r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VWhen{r}}, t,
                    T.WfInl{}),
                  T.wf.go(t, T.WfInl{}), M4.gd.gen.un(T.VPair{n, T.VWhen{r}}, t, T.WfInl{}, ee)))),
              {==}),
            Equal.trans(Bool, T.wf.fresh(T.get(T.rows.seal(t), n)), T.wf.fresh(T.get(t, n)), True{},
              gd.seal.names(t, n), M4.gd.r(T.wf.text(n), T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t),
                  M4.gd.pa(T.WfInl{}, n,
                T.VWhen{r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VWhen{r}}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}),
                M4.gd.gen.un(T.VPair{n, T.VWhen{r}}, t, T.WfInl{}, ee))))))
        case T.WfItems{}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VPair{n, T.VWhen{r}} <> t), T.WfItems{}) == True{} : Bool},
            M4.gd.r(T.wf.key(n, t), False{}, M4.gd.l(M4.gd.h1(T.VPair{n, T.VWhen{r}}, t, T.WfItems{}), T.wf.go(t,
                T.WfItems{}),
              M4.gd.gen.un(T.VPair{n, T.VWhen{r}}, t, T.WfItems{}, ee))))
        case T.WfElems{+h}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VPair{n, T.VWhen{r}} <> t), T.WfElems{h}) == True{} : Bool},
            M4.gd.r(T.wf.key(n, t), False{}, M4.gd.l(M4.gd.h1(T.VPair{n, T.VWhen{r}}, t, T.WfElems{h}), T.wf.go(t,
              T.WfElems{h}), M4.gd.gen.un(T.VPair{n, T.VWhen{r}}, t, T.WfElems{h}, ee))))
    case T.VPair{+n, T.VArr{+r}} <> +t:
      match at:
        case T.WfRows{+h}:
          gd.s.step(T.VPair{n, T.VArr{r}}, t, T.WfRows{h},
            gd.S(t, T.WfRows{h}, M4.gd.r(M4.gd.h1(T.VPair{n, T.VArr{r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}),
              M4.gd.gen.un(T.VPair{n, T.VArr{r}}, t, T.WfRows{h}, ee))),
            M4.gd.gen.mk(T.VPair{n, T.VArr{List.reverse(&2, T.Val, T.rows.seal(r))}}, [], T.WfRows{h},
              M4.gd.tt(T.wf.key(n, []), T.wf.go(List.reverse(&2, T.Val, T.rows.seal(r)), T.WfItems{}),
                  M4.gd.tt(T.wf.text(n),
                True{}, M4.gd.l(T.wf.text(n), T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t), M4.gd.pa(T.WfRows{h}, n,
                T.VArr{r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VArr{r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}),
                M4.gd.gen.un(T.VPair{n, T.VArr{r}}, t, T.WfRows{h}, ee)))), {==}),
                M4.gd.rev.it(T.rows.seal(r), [], gd.S(r, T.WfItems{}, M4.gd.r(T.wf.key(n, t), M4.gd.pa(T.WfRows{h}, n,
                  T.VArr{r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VArr{r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}),
                  M4.gd.gen.un(T.VPair{n, T.VArr{r}}, t, T.WfRows{h}, ee)))), {==})),
              {==}),
            Equal.trans(Bool, T.wf.fresh(T.get(T.rows.seal(t), n)), T.wf.fresh(T.get(t, n)), True{},
              gd.seal.names(t, n), M4.gd.r(T.wf.text(n), T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t),
                  M4.gd.pa(T.WfRows{h},
                n, T.VArr{r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VArr{r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}),
                M4.gd.gen.un(T.VPair{n, T.VArr{r}}, t, T.WfRows{h}, ee))))))
        case T.WfInl{}:
          gd.s.step(T.VPair{n, T.VArr{r}}, t, T.WfInl{},
            gd.S(t, T.WfInl{}, M4.gd.r(M4.gd.h1(T.VPair{n, T.VArr{r}}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}),
              M4.gd.gen.un(T.VPair{n, T.VArr{r}}, t, T.WfInl{}, ee))),
            M4.gd.gen.mk(T.VPair{n, T.VArr{List.reverse(&2, T.Val, T.rows.seal(r))}}, [], T.WfInl{},
              M4.gd.tt(T.wf.key(n, []), T.wf.go(List.reverse(&2, T.Val, T.rows.seal(r)), T.WfItems{}),
                  M4.gd.tt(T.wf.text(n),
                True{}, M4.gd.l(T.wf.text(n), T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t), M4.gd.pa(T.WfInl{}, n,
                T.VArr{r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VArr{r}}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}),
                M4.gd.gen.un(T.VPair{n, T.VArr{r}}, t, T.WfInl{}, ee)))), {==}),
                M4.gd.rev.it(T.rows.seal(r), [], gd.S(r, T.WfItems{}, M4.gd.r(T.wf.key(n, t), M4.gd.pa(T.WfInl{}, n,
                    T.VArr{r}),
                  M4.gd.l(M4.gd.h1(T.VPair{n, T.VArr{r}}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}), M4.gd.gen.un(T.VPair{n,
                  T.VArr{r}}, t, T.WfInl{}, ee)))), {==})),
              {==}),
            Equal.trans(Bool, T.wf.fresh(T.get(T.rows.seal(t), n)), T.wf.fresh(T.get(t, n)), True{},
              gd.seal.names(t, n), M4.gd.r(T.wf.text(n), T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t),
                  M4.gd.pa(T.WfInl{}, n,
                T.VArr{r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VArr{r}}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}),
                M4.gd.gen.un(T.VPair{n, T.VArr{r}}, t, T.WfInl{}, ee))))))
        case T.WfItems{}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VPair{n, T.VArr{r}} <> t), T.WfItems{}) == True{} : Bool},
            M4.gd.r(T.wf.key(n, t), False{}, M4.gd.l(M4.gd.h1(T.VPair{n, T.VArr{r}}, t, T.WfItems{}), T.wf.go(t,
                T.WfItems{}),
              M4.gd.gen.un(T.VPair{n, T.VArr{r}}, t, T.WfItems{}, ee))))
        case T.WfElems{+h}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VPair{n, T.VArr{r}} <> t), T.WfElems{h}) == True{} : Bool},
            M4.gd.r(T.wf.key(n, t), False{}, M4.gd.l(M4.gd.h1(T.VPair{n, T.VArr{r}}, t, T.WfElems{h}), T.wf.go(t,
                T.WfElems{h}),
              M4.gd.gen.un(T.VPair{n, T.VArr{r}}, t, T.WfElems{h}, ee))))
    case T.VPair{+n, T.VInl{+r}} <> +t:
      match at:
        case T.WfRows{+h}:
          gd.s.step(T.VPair{n, T.VInl{r}}, t, T.WfRows{h},
            gd.S(t, T.WfRows{h}, M4.gd.r(M4.gd.h1(T.VPair{n, T.VInl{r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}),
              M4.gd.gen.un(T.VPair{n, T.VInl{r}}, t, T.WfRows{h}, ee))),
            M4.gd.gen.mk(T.VPair{n, T.VInl{T.rows.seal(r)}}, [], T.WfRows{h},
              M4.gd.tt(T.wf.key(n, []), T.wf.go(T.rows.seal(r), T.WfInl{}), M4.gd.tt(T.wf.text(n), True{},
                  M4.gd.l(T.wf.text(n),
                T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t), M4.gd.pa(T.WfRows{h}, n, T.VInl{r}),
                    M4.gd.l(M4.gd.h1(T.VPair{n,
                T.VInl{r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}), M4.gd.gen.un(T.VPair{n, T.VInl{r}}, t,
                T.WfRows{h}, ee)))), {==}),
                gd.S(r, T.WfInl{}, M4.gd.r(T.wf.key(n, t), M4.gd.pa(T.WfRows{h}, n, T.VInl{r}),
                    M4.gd.l(M4.gd.h1(T.VPair{n,
                  T.VInl{r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}), M4.gd.gen.un(T.VPair{n, T.VInl{r}}, t,
                  T.WfRows{h}, ee))))),
              {==}),
            Equal.trans(Bool, T.wf.fresh(T.get(T.rows.seal(t), n)), T.wf.fresh(T.get(t, n)), True{},
              gd.seal.names(t, n), M4.gd.r(T.wf.text(n), T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t),
                  M4.gd.pa(T.WfRows{h},
                n, T.VInl{r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VInl{r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}),
                M4.gd.gen.un(T.VPair{n, T.VInl{r}}, t, T.WfRows{h}, ee))))))
        case T.WfInl{}:
          gd.s.step(T.VPair{n, T.VInl{r}}, t, T.WfInl{},
            gd.S(t, T.WfInl{}, M4.gd.r(M4.gd.h1(T.VPair{n, T.VInl{r}}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}),
              M4.gd.gen.un(T.VPair{n, T.VInl{r}}, t, T.WfInl{}, ee))),
            M4.gd.gen.mk(T.VPair{n, T.VInl{T.rows.seal(r)}}, [], T.WfInl{},
              M4.gd.tt(T.wf.key(n, []), T.wf.go(T.rows.seal(r), T.WfInl{}), M4.gd.tt(T.wf.text(n), True{},
                  M4.gd.l(T.wf.text(n),
                T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t), M4.gd.pa(T.WfInl{}, n, T.VInl{r}),
                    M4.gd.l(M4.gd.h1(T.VPair{n,
                T.VInl{r}}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}), M4.gd.gen.un(T.VPair{n, T.VInl{r}}, t, T.WfInl{},
                ee)))), {==}),
                gd.S(r, T.WfInl{}, M4.gd.r(T.wf.key(n, t), M4.gd.pa(T.WfInl{}, n, T.VInl{r}),
                    M4.gd.l(M4.gd.h1(T.VPair{n,
                  T.VInl{r}}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}), M4.gd.gen.un(T.VPair{n, T.VInl{r}}, t, T.WfInl{},
                  ee))))),
              {==}),
            Equal.trans(Bool, T.wf.fresh(T.get(T.rows.seal(t), n)), T.wf.fresh(T.get(t, n)), True{},
              gd.seal.names(t, n), M4.gd.r(T.wf.text(n), T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t),
                  M4.gd.pa(T.WfInl{}, n,
                T.VInl{r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VInl{r}}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}),
                M4.gd.gen.un(T.VPair{n, T.VInl{r}}, t, T.WfInl{}, ee))))))
        case T.WfItems{}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VPair{n, T.VInl{r}} <> t), T.WfItems{}) == True{} : Bool},
            M4.gd.r(T.wf.key(n, t), False{}, M4.gd.l(M4.gd.h1(T.VPair{n, T.VInl{r}}, t, T.WfItems{}), T.wf.go(t,
                T.WfItems{}),
              M4.gd.gen.un(T.VPair{n, T.VInl{r}}, t, T.WfItems{}, ee))))
        case T.WfElems{+h}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VPair{n, T.VInl{r}} <> t), T.WfElems{h}) == True{} : Bool},
            M4.gd.r(T.wf.key(n, t), False{}, M4.gd.l(M4.gd.h1(T.VPair{n, T.VInl{r}}, t, T.WfElems{h}), T.wf.go(t,
                T.WfElems{h}),
              M4.gd.gen.un(T.VPair{n, T.VInl{r}}, t, T.WfElems{h}, ee))))
    case T.VPair{+n, T.VHead{+p, +r}} <> +t:
      match at:
        case T.WfRows{+h}:
          gd.s.step(T.VPair{n, T.VHead{p, r}}, t, T.WfRows{h},
            gd.S(t, T.WfRows{h}, M4.gd.r(M4.gd.h1(T.VPair{n, T.VHead{p, r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}),
              M4.gd.gen.un(T.VPair{n, T.VHead{p, r}}, t, T.WfRows{h}, ee))),
            M4.gd.gen.mk(T.VPair{n, T.VHead{p, T.rows.seal(r)}}, [], T.WfRows{h},
              M4.gd.tt(T.wf.key(n, []), Bool.and(T.str.eq(p, T.tree.pre(h, n)), T.wf.go(T.rows.seal(r), T.WfRows{p})),
                M4.gd.tt(T.wf.text(n), True{}, M4.gd.l(T.wf.text(n), T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t),
                M4.gd.pa(T.WfRows{h}, n, T.VHead{p, r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VHead{p, r}}, t, T.WfRows{h}),
                T.wf.go(t, T.WfRows{h}), M4.gd.gen.un(T.VPair{n, T.VHead{p, r}}, t, T.WfRows{h}, ee)))), {==}),
                M4.gd.tt(T.str.eq(p, T.tree.pre(h, n)), T.wf.go(T.rows.seal(r), T.WfRows{p}), M4.gd.l(T.str.eq(p,
                  T.tree.pre(h, n)), T.wf.go(r, T.WfRows{p}), M4.gd.r(T.wf.key(n, t), M4.gd.pa(T.WfRows{h}, n,
                      T.VHead{p,
                  r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VHead{p, r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}),
                  M4.gd.gen.un(T.VPair{n, T.VHead{p, r}}, t, T.WfRows{h}, ee)))),
              gd.S(r, T.WfRows{p}, M4.gd.r(T.str.eq(p, T.tree.pre(h, n)), T.wf.go(r, T.WfRows{p}), M4.gd.r(T.wf.key(n,
                  t),
                M4.gd.pa(T.WfRows{h}, n, T.VHead{p, r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VHead{p, r}}, t, T.WfRows{h}),
                    T.wf.go(t,
                T.WfRows{h}), M4.gd.gen.un(T.VPair{n, T.VHead{p, r}}, t, T.WfRows{h}, ee))))))),
              {==}),
            Equal.trans(Bool, T.wf.fresh(T.get(T.rows.seal(t), n)), T.wf.fresh(T.get(t, n)), True{},
              gd.seal.names(t, n), M4.gd.r(T.wf.text(n), T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t),
                  M4.gd.pa(T.WfRows{h},
                n, T.VHead{p, r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VHead{p, r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}),
                M4.gd.gen.un(T.VPair{n, T.VHead{p, r}}, t, T.WfRows{h}, ee))))))
        case T.WfInl{}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VPair{n, T.VHead{p, r}} <> t), T.WfInl{}) == True{} : Bool},
            M4.gd.r(T.wf.key(n, t), False{}, M4.gd.l(M4.gd.h1(T.VPair{n, T.VHead{p, r}}, t, T.WfInl{}), T.wf.go(t,
                T.WfInl{}),
              M4.gd.gen.un(T.VPair{n, T.VHead{p, r}}, t, T.WfInl{}, ee))))
        case T.WfItems{}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VPair{n, T.VHead{p, r}} <> t), T.WfItems{}) == True{} : Bool},
            M4.gd.r(T.wf.key(n, t), False{}, M4.gd.l(M4.gd.h1(T.VPair{n, T.VHead{p, r}}, t, T.WfItems{}), T.wf.go(t,
              T.WfItems{}), M4.gd.gen.un(T.VPair{n, T.VHead{p, r}}, t, T.WfItems{}, ee))))
        case T.WfElems{+h}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VPair{n, T.VHead{p, r}} <> t), T.WfElems{h}) == True{} : Bool},
            M4.gd.r(T.wf.key(n, t), False{}, M4.gd.l(M4.gd.h1(T.VPair{n, T.VHead{p, r}}, t, T.WfElems{h}), T.wf.go(t,
              T.WfElems{h}), M4.gd.gen.un(T.VPair{n, T.VHead{p, r}}, t, T.WfElems{h}, ee))))
    case T.VPair{+n, T.VAot{+p, +r}} <> +t:
      match at:
        case T.WfRows{+h}:
          gd.s.step(T.VPair{n, T.VAot{p, r}}, t, T.WfRows{h},
            gd.S(t, T.WfRows{h}, M4.gd.r(M4.gd.h1(T.VPair{n, T.VAot{p, r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}),
              M4.gd.gen.un(T.VPair{n, T.VAot{p, r}}, t, T.WfRows{h}, ee))),
            M4.gd.gen.mk(T.VPair{n, T.VAot{p, r}}, [], T.WfRows{h},
              M4.gd.tt(T.wf.key(n, []), M4.gd.pa(T.WfRows{h}, n, T.VAot{p, r}), M4.gd.tt(T.wf.text(n), True{},
                M4.gd.l(T.wf.text(n), T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t), M4.gd.pa(T.WfRows{h}, n,
                    T.VAot{p, r}),
                M4.gd.l(M4.gd.h1(T.VPair{n, T.VAot{p, r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}),
                    M4.gd.gen.un(T.VPair{n,
                T.VAot{p, r}}, t, T.WfRows{h}, ee)))), {==}),
                M4.gd.r(T.wf.key(n, t), M4.gd.pa(T.WfRows{h}, n, T.VAot{p, r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VAot{p,
                    r}}, t,
                  T.WfRows{h}), T.wf.go(t, T.WfRows{h}), M4.gd.gen.un(T.VPair{n, T.VAot{p, r}}, t, T.WfRows{h}, ee)))),
              {==}),
            Equal.trans(Bool, T.wf.fresh(T.get(T.rows.seal(t), n)), T.wf.fresh(T.get(t, n)), True{},
              gd.seal.names(t, n), M4.gd.r(T.wf.text(n), T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t),
                  M4.gd.pa(T.WfRows{h},
                n, T.VAot{p, r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VAot{p, r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}),
                M4.gd.gen.un(T.VPair{n, T.VAot{p, r}}, t, T.WfRows{h}, ee))))))
        case T.WfInl{}:
          gd.s.step(T.VPair{n, T.VAot{p, r}}, t, T.WfInl{},
            gd.S(t, T.WfInl{}, M4.gd.r(M4.gd.h1(T.VPair{n, T.VAot{p, r}}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}),
              M4.gd.gen.un(T.VPair{n, T.VAot{p, r}}, t, T.WfInl{}, ee))),
            M4.gd.gen.mk(T.VPair{n, T.VAot{p, r}}, [], T.WfInl{},
              M4.gd.tt(T.wf.key(n, []), M4.gd.pa(T.WfInl{}, n, T.VAot{p, r}), M4.gd.tt(T.wf.text(n), True{},
                  M4.gd.l(T.wf.text(n),
                T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t), M4.gd.pa(T.WfInl{}, n, T.VAot{p, r}),
                    M4.gd.l(M4.gd.h1(T.VPair{n,
                T.VAot{p, r}}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}), M4.gd.gen.un(T.VPair{n, T.VAot{p, r}}, t,
                T.WfInl{}, ee)))), {==}),
                M4.gd.r(T.wf.key(n, t), M4.gd.pa(T.WfInl{}, n, T.VAot{p, r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VAot{p,
                    r}}, t,
                  T.WfInl{}), T.wf.go(t, T.WfInl{}), M4.gd.gen.un(T.VPair{n, T.VAot{p, r}}, t, T.WfInl{}, ee)))),
              {==}),
            Equal.trans(Bool, T.wf.fresh(T.get(T.rows.seal(t), n)), T.wf.fresh(T.get(t, n)), True{},
              gd.seal.names(t, n), M4.gd.r(T.wf.text(n), T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t),
                  M4.gd.pa(T.WfInl{}, n,
                T.VAot{p, r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VAot{p, r}}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}),
                M4.gd.gen.un(T.VPair{n, T.VAot{p, r}}, t, T.WfInl{}, ee))))))
        case T.WfItems{}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VPair{n, T.VAot{p, r}} <> t), T.WfItems{}) == True{} : Bool},
            M4.gd.r(T.wf.key(n, t), False{}, M4.gd.l(M4.gd.h1(T.VPair{n, T.VAot{p, r}}, t, T.WfItems{}), T.wf.go(t,
              T.WfItems{}), M4.gd.gen.un(T.VPair{n, T.VAot{p, r}}, t, T.WfItems{}, ee))))
        case T.WfElems{+h}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VPair{n, T.VAot{p, r}} <> t), T.WfElems{h}) == True{} : Bool},
            M4.gd.r(T.wf.key(n, t), False{}, M4.gd.l(M4.gd.h1(T.VPair{n, T.VAot{p, r}}, t, T.WfElems{h}), T.wf.go(t,
              T.WfElems{h}), M4.gd.gen.un(T.VPair{n, T.VAot{p, r}}, t, T.WfElems{h}, ee))))
    case T.VPair{+n, T.VAots{+p, +r}} <> +t:
      match at:
        case T.WfRows{+h}:
          gd.s.step(T.VPair{n, T.VAots{p, r}}, t, T.WfRows{h},
            gd.S(t, T.WfRows{h}, M4.gd.r(M4.gd.h1(T.VPair{n, T.VAots{p, r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}),
              M4.gd.gen.un(T.VPair{n, T.VAots{p, r}}, t, T.WfRows{h}, ee))),
            M4.gd.gen.mk(T.VPair{n, T.VAots{p, T.rows.seal(r)}}, [], T.WfRows{h},
              M4.gd.tt(T.wf.key(n, []), Bool.and(Bool.not(List.is_empty(&2, T.Val, T.rows.seal(r))),
                  Bool.and(T.str.eq(p,
                T.tree.pre(h, n)), T.wf.go(T.rows.seal(r), T.WfElems{p}))), M4.gd.tt(T.wf.text(n), True{},
                M4.gd.l(T.wf.text(n), T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t), M4.gd.pa(T.WfRows{h}, n,
                    T.VAots{p,
                r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VAots{p, r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}),
                M4.gd.gen.un(T.VPair{n, T.VAots{p, r}}, t, T.WfRows{h}, ee)))), {==}),
                M4.gd.tt(Bool.not(List.is_empty(&2, T.Val, T.rows.seal(r))), Bool.and(T.str.eq(p, T.tree.pre(h, n)),
                  T.wf.go(T.rows.seal(r), T.WfElems{p})),
              gd.seal.some(r, M4.gd.l(Bool.not(List.is_empty(&2, T.Val, r)), Bool.and(T.str.eq(p, T.tree.pre(h, n)),
                T.wf.go(r, T.WfElems{p})), M4.gd.r(T.wf.key(n, t), M4.gd.pa(T.WfRows{h}, n, T.VAots{p, r}),
                M4.gd.l(M4.gd.h1(T.VPair{n, T.VAots{p, r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}),
                    M4.gd.gen.un(T.VPair{n,
                T.VAots{p, r}}, t, T.WfRows{h}, ee))))),
              M4.gd.tt(T.str.eq(p, T.tree.pre(h, n)), T.wf.go(T.rows.seal(r), T.WfElems{p}), M4.gd.l(T.str.eq(p,
                T.tree.pre(h, n)), T.wf.go(r, T.WfElems{p}), M4.gd.r(Bool.not(List.is_empty(&2, T.Val, r)),
                Bool.and(T.str.eq(p, T.tree.pre(h, n)), T.wf.go(r, T.WfElems{p})), M4.gd.r(T.wf.key(n, t),
                M4.gd.pa(T.WfRows{h}, n, T.VAots{p, r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VAots{p, r}}, t, T.WfRows{h}),
                T.wf.go(t, T.WfRows{h}), M4.gd.gen.un(T.VPair{n, T.VAots{p, r}}, t, T.WfRows{h}, ee))))),
                gd.S(r, T.WfElems{p}, M4.gd.r(T.str.eq(p, T.tree.pre(h, n)), T.wf.go(r, T.WfElems{p}),
                  M4.gd.r(Bool.not(List.is_empty(&2, T.Val, r)), Bool.and(T.str.eq(p, T.tree.pre(h, n)), T.wf.go(r,
                  T.WfElems{p})), M4.gd.r(T.wf.key(n, t), M4.gd.pa(T.WfRows{h}, n, T.VAots{p, r}),
                      M4.gd.l(M4.gd.h1(T.VPair{n,
                  T.VAots{p, r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}), M4.gd.gen.un(T.VPair{n, T.VAots{p, r}}, t,
                  T.WfRows{h}, ee))))))))),
              {==}),
            Equal.trans(Bool, T.wf.fresh(T.get(T.rows.seal(t), n)), T.wf.fresh(T.get(t, n)), True{},
              gd.seal.names(t, n), M4.gd.r(T.wf.text(n), T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t),
                  M4.gd.pa(T.WfRows{h},
                n, T.VAots{p, r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VAots{p, r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}),
                M4.gd.gen.un(T.VPair{n, T.VAots{p, r}}, t, T.WfRows{h}, ee))))))
        case T.WfInl{}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VPair{n, T.VAots{p, r}} <> t), T.WfInl{}) == True{} : Bool},
            M4.gd.r(T.wf.key(n, t), False{}, M4.gd.l(M4.gd.h1(T.VPair{n, T.VAots{p, r}}, t, T.WfInl{}), T.wf.go(t,
                T.WfInl{}),
              M4.gd.gen.un(T.VPair{n, T.VAots{p, r}}, t, T.WfInl{}, ee))))
        case T.WfItems{}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VPair{n, T.VAots{p, r}} <> t), T.WfItems{}) == True{} : Bool},
            M4.gd.r(T.wf.key(n, t), False{}, M4.gd.l(M4.gd.h1(T.VPair{n, T.VAots{p, r}}, t, T.WfItems{}), T.wf.go(t,
              T.WfItems{}), M4.gd.gen.un(T.VPair{n, T.VAots{p, r}}, t, T.WfItems{}, ee))))
        case T.WfElems{+h}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VPair{n, T.VAots{p, r}} <> t), T.WfElems{h}) == True{} : Bool},
            M4.gd.r(T.wf.key(n, t), False{}, M4.gd.l(M4.gd.h1(T.VPair{n, T.VAots{p, r}}, t, T.WfElems{h}), T.wf.go(t,
              T.WfElems{h}), M4.gd.gen.un(T.VPair{n, T.VAots{p, r}}, t, T.WfElems{h}, ee))))
    case T.VPair{+n, T.VPair{+p, +r}} <> +t:
      match at:
        case T.WfRows{+h}:
          gd.s.step(T.VPair{n, T.VPair{p, r}}, t, T.WfRows{h},
            gd.S(t, T.WfRows{h}, M4.gd.r(M4.gd.h1(T.VPair{n, T.VPair{p, r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}),
              M4.gd.gen.un(T.VPair{n, T.VPair{p, r}}, t, T.WfRows{h}, ee))),
            M4.gd.gen.mk(T.VPair{n, T.VPair{p, r}}, [], T.WfRows{h},
              M4.gd.tt(T.wf.key(n, []), M4.gd.pa(T.WfRows{h}, n, T.VPair{p, r}), M4.gd.tt(T.wf.text(n), True{},
                M4.gd.l(T.wf.text(n), T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t), M4.gd.pa(T.WfRows{h}, n,
                    T.VPair{p, r}),
                M4.gd.l(M4.gd.h1(T.VPair{n, T.VPair{p, r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}),
                    M4.gd.gen.un(T.VPair{n,
                T.VPair{p, r}}, t, T.WfRows{h}, ee)))), {==}),
                M4.gd.r(T.wf.key(n, t), M4.gd.pa(T.WfRows{h}, n, T.VPair{p, r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VPair{p,
                    r}}, t,
                  T.WfRows{h}), T.wf.go(t, T.WfRows{h}), M4.gd.gen.un(T.VPair{n, T.VPair{p, r}}, t, T.WfRows{h}, ee)))),
              {==}),
            Equal.trans(Bool, T.wf.fresh(T.get(T.rows.seal(t), n)), T.wf.fresh(T.get(t, n)), True{},
              gd.seal.names(t, n), M4.gd.r(T.wf.text(n), T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t),
                  M4.gd.pa(T.WfRows{h},
                n, T.VPair{p, r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VPair{p, r}}, t, T.WfRows{h}), T.wf.go(t, T.WfRows{h}),
                M4.gd.gen.un(T.VPair{n, T.VPair{p, r}}, t, T.WfRows{h}, ee))))))
        case T.WfInl{}:
          gd.s.step(T.VPair{n, T.VPair{p, r}}, t, T.WfInl{},
            gd.S(t, T.WfInl{}, M4.gd.r(M4.gd.h1(T.VPair{n, T.VPair{p, r}}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}),
              M4.gd.gen.un(T.VPair{n, T.VPair{p, r}}, t, T.WfInl{}, ee))),
            M4.gd.gen.mk(T.VPair{n, T.VPair{p, r}}, [], T.WfInl{},
              M4.gd.tt(T.wf.key(n, []), M4.gd.pa(T.WfInl{}, n, T.VPair{p, r}), M4.gd.tt(T.wf.text(n), True{},
                  M4.gd.l(T.wf.text(n),
                T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t), M4.gd.pa(T.WfInl{}, n, T.VPair{p, r}),
                    M4.gd.l(M4.gd.h1(T.VPair{n,
                T.VPair{p, r}}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}), M4.gd.gen.un(T.VPair{n, T.VPair{p, r}}, t,
                T.WfInl{}, ee)))), {==}),
                M4.gd.r(T.wf.key(n, t), M4.gd.pa(T.WfInl{}, n, T.VPair{p, r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VPair{p,
                    r}}, t,
                  T.WfInl{}), T.wf.go(t, T.WfInl{}), M4.gd.gen.un(T.VPair{n, T.VPair{p, r}}, t, T.WfInl{}, ee)))),
              {==}),
            Equal.trans(Bool, T.wf.fresh(T.get(T.rows.seal(t), n)), T.wf.fresh(T.get(t, n)), True{},
              gd.seal.names(t, n), M4.gd.r(T.wf.text(n), T.wf.fresh(T.get(t, n)), M4.gd.l(T.wf.key(n, t),
                  M4.gd.pa(T.WfInl{}, n,
                T.VPair{p, r}), M4.gd.l(M4.gd.h1(T.VPair{n, T.VPair{p, r}}, t, T.WfInl{}), T.wf.go(t, T.WfInl{}),
                M4.gd.gen.un(T.VPair{n, T.VPair{p, r}}, t, T.WfInl{}, ee))))))
        case T.WfItems{}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VPair{n, T.VPair{p, r}} <> t), T.WfItems{}) == True{} : Bool},
            M4.gd.r(T.wf.key(n, t), False{}, M4.gd.l(M4.gd.h1(T.VPair{n, T.VPair{p, r}}, t, T.WfItems{}), T.wf.go(t,
              T.WfItems{}), M4.gd.gen.un(T.VPair{n, T.VPair{p, r}}, t, T.WfItems{}, ee))))
        case T.WfElems{+h}:
          Eq.bit.absurd(&2, {T.wf.go(T.rows.seal(T.VPair{n, T.VPair{p, r}} <> t), T.WfElems{h}) == True{} : Bool},
            M4.gd.r(T.wf.key(n, t), False{}, M4.gd.l(M4.gd.h1(T.VPair{n, T.VPair{p, r}}, t, T.WfElems{h}), T.wf.go(t,
              T.WfElems{h}), M4.gd.gen.un(T.VPair{n, T.VPair{p, r}}, t, T.WfElems{h}, ee))))

# the frames at the end: none, or the document is unclosed
def gd.fin.stk(
  stack: List<&2, T.Ctx>,
  +bad: String,
  +rows: List<&2, T.Val>,
  +et: {L1.gd.tr(bad, rows, stack) == True{} : Bool},
  +eo: {String.is_empty(T.bad(T.read.fin.stack(stack, bad, rows))) == True{} : Bool}
) -> {T.wf(T.read.fin.stack(stack, bad, rows)) == True{} : Bool}:
  match stack:
    case []:
      match bad:
        case SNil{}:
          gd.S(rows, T.WfRows{""}, M4.gd.l(T.wf.go(rows, T.WfRows{""}), True{}, et))
        case SCon{+hh, +tt}:
          Eq.bit.absurd(&2, {T.wf(T.read.fin.stack([], SCon{hh, tt}, rows)) == True{} : Bool}, eo)
    case +c <> +r:
      Eq.bit.absurd(&2, {T.wf(T.read.fin.stack(c <> r, bad, rows)) == True{} : Bool},
        Equal.trans(Bool, False{}, String.is_empty(T.err.first(bad, "unclosed")), True{},
          Equal.sym(Bool, String.is_empty(T.err.first(bad, "unclosed")), False{},
            M4.gd.err.ne2(bad, "unclosed", {==})),
          eo))

def L1.gd_fin(st, eg, eo):
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.fin.stk(stack, bad, rows,
        M4.gd.l(L1.gd.tr(bad, rows, stack), L1.gd.lx(here, parts, buf, stack, hold), eg), eo)

# WP-R3: the span modes. doc.read reads the text in four modes. A scanning
# state and one after a carriage return are good states; an opening quote's
# mode is good as the quote left its state; a plain string's span keeps its
# first character and its length, and gd.sp ties the span to the text still
# to read, so each character the span takes is one the text had, a Unicode
# scalar value. A span that closes is a VSpan whose n characters are scalar
# values; one copied to the buffer puts scalar values there

# a then that holds holds its first part
def gd.th.l(aa: Bool, mm: Unit -> Bool, +ee: {T.wf.then(aa, mm) == True{} : Bool}) -> {aa == True{} : Bool}:
  match aa:
    case True{}:
      {==}
    case False{}:
      Eq.bit.absurd(&2, {False{} == True{} : Bool}, ee)

# a then that holds holds its rest
def gd.th.r(aa: Bool, mm: Unit -> Bool, +ee: {T.wf.then(aa, mm) == True{} : Bool}) -> {mm(Unit{}) == True{} : Bool}:
  match aa:
    case True{}:
      ee
    case False{}:
      Eq.bit.absurd(&2, {mm(Unit{}) == True{} : Bool}, ee)

# a text is as long as itself
def gd.ln.self(+ss: String) -> {L1.gd.ln(ss, ss) == True{} : Bool}:
  match ss:
    case SNil{}:
      {==}
    case SCon{_h, tt}:
      gd.ln.self(tt)

# taking a borrow from a word and then adding the carry back leaves the word
def gd.decinc.w(
  nn: Nat,
  ww: Word(nn),
  cc: Bool
) -> {Word.adc(nn, Word.adc(nn, ww, Word.zero(nn), True{}, cc), Word.zero(nn), False{}, Bool.not(cc)) == ww : Word(nn)}:
  match nn:
    case 0n:
      match ww:
        case WNil{}:
          {==}
    case 1n+pp:
      match ww:
        case WCon{bb, +tt}:
          match bb cc:
            case False{} False{}:
              Equal.cong(Word(pp), Word(1n+pp), yy => WCon{False{}, yy},
                Word.adc(pp, Word.adc(pp, tt, Word.zero(pp), True{}, False{}), Word.zero(pp), False{}, True{}), tt,
                gd.decinc.w(pp, tt, False{}))
            case False{} True{}:
              Equal.cong(Word(pp), Word(1n+pp), yy => WCon{False{}, yy},
                Word.adc(pp, Word.adc(pp, tt, Word.zero(pp), True{}, True{}), Word.zero(pp), False{}, False{}), tt,
                gd.decinc.w(pp, tt, True{}))
            case True{} False{}:
              Equal.cong(Word(pp), Word(1n+pp), yy => WCon{True{}, yy},
                Word.adc(pp, Word.adc(pp, tt, Word.zero(pp), True{}, True{}), Word.zero(pp), False{}, False{}), tt,
                gd.decinc.w(pp, tt, True{}))
            case True{} True{}:
              Equal.cong(Word(pp), Word(1n+pp), yy => WCon{True{}, yy},
                Word.adc(pp, Word.adc(pp, tt, Word.zero(pp), True{}, True{}), Word.zero(pp), False{}, False{}), tt,
                gd.decinc.w(pp, tt, True{}))

# one more than one less than a U32 is the U32
def gd.decinc(xx: U32) -> {U32.add(U32.sub(xx, 1), 1) == xx : U32}:
  match xx:
    case U32{ww}:
      match ww:
        case WCon{bb, +tt}:
          match bb:
            case False{}:
              Equal.cong(Word(31n), U32, yy => U32{WCon{False{}, yy}},
                Word.adc(31n, Word.adc(31n, tt, Word.zero(31n), True{}, False{}), Word.zero(31n), False{}, True{}),
                tt, gd.decinc.w(31n, tt, False{}))
            case True{}:
              Equal.cong(Word(31n), U32, yy => U32{WCon{True{}, yy}},
                Word.adc(31n, Word.adc(31n, tt, Word.zero(31n), True{}, True{}), Word.zero(31n), False{}, False{}),
                tt, gd.decinc.w(31n, tt, True{}))

# a span as gd.sp keeps it, at the count it has run down to
def gd.spm(+cut: String, +nn: U32, text: String) -> Bool:
  L1.gd.sp(cut, U32.is_zero(nn), nn, text)

# the span one character on, read back at the count it came from
def gd.spm.back(
  +cut: String,
  +nn: U32,
  +text: String
) -> {gd.spm(cut, U32.sub(U32.add(nn, 1), 1), text) == gd.spm(cut, nn, text) : Bool}:
  Equal.cong(U32, Bool, xx => gd.spm(cut, xx, text), U32.sub(U32.add(nn, 1), 1), nn, Eq.sub.inc(nn))

# the span one character back and on again is at its count
def gd.spm.fwd(
  +cut: String,
  +nn: U32,
  +text: String
) -> {gd.spm(cut, U32.add(U32.sub(nn, 1), 1), text) == gd.spm(cut, nn, text) : Bool}:
  Equal.cong(U32, Bool, xx => gd.spm(cut, xx, text), U32.add(U32.sub(nn, 1), 1), nn, gd.decinc(nn))

# a span's rest, where its count has run down
def gd.sp.end(
  +ct: String,
  +nn: U32,
  +tt: String,
  +hz: {U32.is_zero(nn) == True{} : Bool},
  +ee: {L1.gd.sp(ct, True{}, nn, tt) == True{} : Bool}
) -> {gd.spm(ct, U32.sub(U32.add(nn, 1), 1), tt) == True{} : Bool}:
  Equal.trans(Bool, gd.spm(ct, U32.sub(U32.add(nn, 1), 1), tt), gd.spm(ct, nn, tt), True{},
    gd.spm.back(ct, nn, tt),
    Equal.trans(Bool, gd.spm(ct, nn, tt), L1.gd.sp(ct, True{}, nn, tt), True{},
      Equal.cong(Bool, Bool, zz => L1.gd.sp(ct, zz, nn, tt), U32.is_zero(nn), True{}, hz), ee))

# a span's rest of scalar values, as long as the text, where its count has run down
def gd.sp.full(
  +ct: String,
  +nn: U32,
  +tt: String,
  +ew: {T.wf.text(ct) == True{} : Bool},
  +el: {L1.gd.ln(ct, tt) == True{} : Bool}
) -> {L1.gd.sp(ct, True{}, nn, tt) == True{} : Bool}:
  match ct:
    case SNil{}:
      M4.gd.tt(T.wf.text(SNil{}), L1.gd.ln(SNil{}, tt), {==}, el)
    case SCon{+dh, +dt}:
      M4.gd.tt(T.wf.text(SCon{dh, dt}), L1.gd.ln(SCon{dh, dt}, tt), ew, el)

# the rest of a span whose count has run down: scalar values, as long as the text
def gd.sp.rest(
  +ct: String,
  +nn: U32,
  +tt: String,
  +ch: Char,
  +ee: {Bool.and(T.wf.then(T.wf.char(ch), _u => T.wf.text(ct)), L1.gd.ln(ct, tt)) == True{} : Bool}
) -> {L1.gd.sp(ct, True{}, nn, tt) == True{} : Bool}:
  match ct:
    case SNil{}:
      M4.gd.tt(T.wf.text(SNil{}), L1.gd.ln(SNil{}, tt), {==},
        M4.gd.r(T.wf.then(T.wf.char(ch), _u => T.wf.text(SNil{})), L1.gd.ln(SNil{}, tt), ee))
    case SCon{+dh, +dt}:
      M4.gd.tt(T.wf.text(SCon{dh, dt}), L1.gd.ln(SCon{dh, dt}, tt),
        gd.th.r(T.wf.char(ch), _u => T.wf.text(SCon{dh, dt}),
          M4.gd.l(T.wf.then(T.wf.char(ch), _u => T.wf.text(SCon{dh, dt})), L1.gd.ln(SCon{dh, dt}, tt), ee)),
        M4.gd.r(T.wf.then(T.wf.char(ch), _u => T.wf.text(SCon{dh, dt})), L1.gd.ln(SCon{dh, dt}, tt), ee))

# a span takes the text's next character: its count goes up by one, and the
# span still reaches the text after that character
def gd.sp.inc(
  cut: String,
  zz: Bool,
  +nn: U32,
  +hh: Char,
  +tt: String,
  +hz: {U32.is_zero(nn) == zz : Bool},
  +en: {U32.is_zero(U32.add(nn, 1)) == False{} : Bool},
  +ep: {L1.gd.sp(cut, zz, nn, SCon{hh, tt}) == True{} : Bool}
) -> {gd.spm(cut, U32.add(nn, 1), tt) == True{} : Bool}:
  match cut:
    case SNil{}:
      match zz:
        case True{}:
          Eq.bit.absurd(&2, {gd.spm(SNil{}, U32.add(nn, 1), tt) == True{} : Bool}, ep)
        case False{}:
          Eq.bit.absurd(&2, {gd.spm(SNil{}, U32.add(nn, 1), tt) == True{} : Bool}, ep)
    case SCon{+ch, +ct}:
      match zz:
        case True{}:
          Equal.trans(Bool, gd.spm(SCon{ch, ct}, U32.add(nn, 1), tt),
            L1.gd.sp(SCon{ch, ct}, False{}, U32.add(nn, 1), tt), True{},
            Equal.cong(Bool, Bool, yy => L1.gd.sp(SCon{ch, ct}, yy, U32.add(nn, 1), tt),
              U32.is_zero(U32.add(nn, 1)), False{}, en),
            M4.gd.tt(T.wf.char(ch), gd.spm(ct, U32.sub(U32.add(nn, 1), 1), tt),
              gd.th.l(T.wf.char(ch), _u => T.wf.text(ct),
                M4.gd.l(T.wf.then(T.wf.char(ch), _u => T.wf.text(ct)), L1.gd.ln(ct, tt), ep)),
              gd.sp.end(ct, nn, tt, hz, gd.sp.rest(ct, nn, tt, ch, ep))))
        case False{}:
          Equal.trans(Bool, gd.spm(SCon{ch, ct}, U32.add(nn, 1), tt),
            L1.gd.sp(SCon{ch, ct}, False{}, U32.add(nn, 1), tt), True{},
            Equal.cong(Bool, Bool, yy => L1.gd.sp(SCon{ch, ct}, yy, U32.add(nn, 1), tt),
              U32.is_zero(U32.add(nn, 1)), False{}, en),
            M4.gd.tt(T.wf.char(ch), gd.spm(ct, U32.sub(U32.add(nn, 1), 1), tt),
              M4.gd.l(T.wf.char(ch), gd.spm(ct, U32.sub(nn, 1), SCon{hh, tt}), ep),
              Equal.trans(Bool, gd.spm(ct, U32.sub(U32.add(nn, 1), 1), tt), gd.spm(ct, nn, tt), True{},
                gd.spm.back(ct, nn, tt),
                Equal.trans(Bool, gd.spm(ct, nn, tt), gd.spm(ct, U32.add(U32.sub(nn, 1), 1), tt), True{},
                  Equal.sym(Bool, gd.spm(ct, U32.add(U32.sub(nn, 1), 1), tt), gd.spm(ct, nn, tt),
                    gd.spm.fwd(ct, nn, tt)),
                  gd.sp.inc(ct, U32.is_zero(U32.sub(nn, 1)), U32.sub(nn, 1), hh, tt, {==},
                    Equal.trans(Bool, U32.is_zero(U32.add(U32.sub(nn, 1), 1)), U32.is_zero(nn), False{},
                      Equal.cong(U32, Bool, xx => U32.is_zero(xx), U32.add(U32.sub(nn, 1), 1), nn, gd.decinc(nn)),
                      hz),
                    M4.gd.r(T.wf.char(ch), gd.spm(ct, U32.sub(nn, 1), SCon{hh, tt}), ep))))))

# a span kept as gd.sp keeps it is a well-formed span
def gd.sp.wf(
  cut: String,
  zz: Bool,
  +nn: U32,
  +text: String,
  +ep: {L1.gd.sp(cut, zz, nn, text) == True{} : Bool}
) -> {T.wf.span(cut, nn, zz) == True{} : Bool}:
  match cut:
    case SNil{}:
      match zz:
        case True{}:
          {==}
        case False{}:
          Eq.bit.absurd(&2, {T.wf.span(SNil{}, nn, False{}) == True{} : Bool}, ep)
    case SCon{+ch, +ct}:
      match zz:
        case True{}:
          {==}
        case False{}:
          M4.gd.then(T.wf.char(ch), _u => T.wf.span(ct, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1))),
            M4.gd.l(T.wf.char(ch), gd.spm(ct, U32.sub(nn, 1), text), ep),
            gd.sp.wf(ct, U32.is_zero(U32.sub(nn, 1)), U32.sub(nn, 1), text,
              M4.gd.r(T.wf.char(ch), gd.spm(ct, U32.sub(nn, 1), text), ep)))

# a span copied to the buffer, reversed onto scalar values, is scalar values
def gd.sp.rev(
  cut: String,
  zz: Bool,
  +nn: U32,
  +text: String,
  +acc: List<&2, Char>,
  +ep: {L1.gd.sp(cut, zz, nn, text) == True{} : Bool},
  +ea: {L1.gd.cs(acc) == True{} : Bool}
) -> {L1.gd.cs(T.span.rev(cut, nn, zz, acc)) == True{} : Bool}:
  match cut:
    case SNil{}:
      match zz:
        case True{}:
          ea
        case False{}:
          ea
    case SCon{+ch, +ct}:
      match zz:
        case True{}:
          ea
        case False{}:
          gd.sp.rev(ct, U32.is_zero(U32.sub(nn, 1)), U32.sub(nn, 1), text, ch <> acc,
            M4.gd.r(T.wf.char(ch), gd.spm(ct, U32.sub(nn, 1), text), ep),
            M4.gd.tt(T.wf.char(ch), L1.gd.cs(acc), M4.gd.l(T.wf.char(ch), gd.spm(ct, U32.sub(nn, 1), text), ep), ea))

def L1.gd_span_wf(cut, nn, text, ep) :
  gd.sp.wf(cut, U32.is_zero(nn), nn, text, ep)

def L1.gd_next(mode, _hh, _tt):
  match mode:
    case T.MOpen{_b, _q, _k, _bd, _rw, _hs, _he, _pt, _bf, _bk, _sk, _un, _lf, _at}:
      {==}
    case T.MEat{_b, _q, _c, _n, _bd, _rw, _hs, _he, _pt, _k, _sk, _un, _lf, _at}:
      {==}
    case T.MScan{_st}:
      {==}
    case T.MCr{_st}:
      {==}

# a quote's state: a one-line string opens a span unless a character is held
# or it is the first character; every other state scans on
def gd.wlex(
  lx: T.Lex,
  hd: T.Hold,
  ld: Bool,
  qk: T.QKind,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +bf: List<&2, Char>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +tl: String,
  +eg: {L1.good(T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, hd, un, lf, at, ld}) == True{} : Bool}
) -> {L1.gd.md(T.doc.wrap.lex(lx, bd, rw, hs, he, pt, bf, bk, qk, sk, hd, un, lf, at, ld), tl) == True{} : Bool}:
  match lx:
    case T.LTop{}:
      eg
    case T.LLine{}:
      eg
    case T.LKey{}:
      eg
    case T.LKeyDot{}:
      eg
    case T.LAfter{}:
      eg
    case T.LKeyQ{}:
      eg
    case T.LKeyE{}:
      eg
    case T.LKeyU{}:
      eg
    case T.LVal{}:
      eg
    case T.LQ{}:
      match hd:
        case T.HChar{_held}:
          eg
        case T.HNone{}:
          match ld:
            case True{}:
              eg
            case False{}:
              match qk:
                case T.QBasic{}:
                  eg
                case T.QLit{}:
                  eg
                case T.QMulti{}:
                  eg
                case T.QMultiLit{}:
                  eg
    case T.LQ2{}:
      eg
    case T.LStr{}:
      eg
    case T.LEsc{}:
      eg
    case T.LUni{}:
      eg
    case T.LFold{}:
      eg
    case T.LMq{}:
      eg
    case T.LMqEnd{}:
      eg
    case T.LTrim{}:
      eg
    case T.LTrim2{}:
      eg
    case T.LBare{}:
      eg
    case T.LDate{}:
      eg
    case T.LCom{}:
      eg
    case T.LHead{}:
      eg
    case T.LHeadGap{}:
      eg
    case T.LHeadDot{}:
      eg
    case T.LHeadQ{}:
      eg
    case T.LHeadE{}:
      eg
    case T.LHeadU{}:
      eg
    case T.LHeadR{}:
      eg
    case T.LArr{}:
      eg
    case T.LArrC{}:
      eg
    case T.LInl{}:
      eg
    case T.LInlK{}:
      eg
    case T.LInlC{}:
      eg
    case T.LSink{}:
      eg

# a state a quote may have opened a string in
def gd.wrap(
  +st: T.St,
  +tl: String,
  +eg: {L1.good(st) == True{} : Bool}
) -> {L1.gd.md(T.doc.wrap(st), tl) == True{} : Bool}:
  match st:
    case T.St{+bd, +rw, +hs, +he, +pt, +bf, +lx, +bk, +qk, +sk, +hd, +un, +lf, +at, +ld}:
      gd.wlex(lx, hd, ld, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, tl, eg)

# a carriage return, or another character
def gd.scr(
  cr: Bool,
  +st: T.St,
  +cc: Char,
  +tl: String,
  +eg: {L1.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L1.gd.md(T.doc.scan.cr(cr, st, cc), tl) == True{} : Bool}:
  match cr:
    case True{}:
      M4.gd.fast(st, cc, eg, ec)
    case False{}:
      M4.gd.fast(st, cc, eg, ec)

# an apostrophe, or another character
def gd.ssq(
  sq: Bool,
  +cr: Bool,
  +st: T.St,
  +cc: Char,
  +tl: String,
  +eg: {L1.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L1.gd.md(T.doc.scan.sq(sq, cr, st, cc), tl) == True{} : Bool}:
  match sq:
    case True{}:
      gd.wrap(T.read.fast(st, cc), tl, M4.gd.fast(st, cc, eg, ec))
    case False{}:
      gd.scr(cr, st, cc, tl, eg, ec)

# a quote, or another character
def gd.sdq(
  dq: Bool,
  +sq: Bool,
  +cr: Bool,
  +st: T.St,
  +cc: Char,
  +tl: String,
  +eg: {L1.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L1.gd.md(T.doc.scan.q(dq, sq, cr, st, cc), tl) == True{} : Bool}:
  match dq:
    case True{}:
      gd.wrap(T.read.fast(st, cc), tl, M4.gd.fast(st, cc, eg, ec))
    case False{}:
      gd.ssq(sq, cr, st, cc, tl, eg, ec)

# a line feed after a carriage return, or the error
def gd.dcr(
  lf: Bool,
  +st: T.St,
  +cc: Char,
  +tl: String,
  +eg: {L1.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L1.gd.md(T.doc.cr(lf, st, cc), tl) == True{} : Bool}:
  match lf:
    case True{}:
      M4.gd.fast(st, cc, eg, ec)
    case False{}:
      M4.gd.g.err2(st, "carriage return without line feed", eg)

# an empty buffer starts a span at this character; a buffer in use goes the
# old way
def gd.obuf(
  bf: List<&2, Char>,
  +ba: Bool,
  +qq: Char,
  +qk: T.QKind,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +cc: Char,
  +tl: String,
  +eg: {M4.gd.gf(bd, rw, he, pt, bf, sk) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool},
  +et: {T.wf.text(tl) == True{} : Bool},
  +es: {D1.short(SCon{cc, tl}) == True{} : Bool}
) -> {L1.gd.md(T.doc.open.buf(ba, qq, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc, tl), tl) == True{} : Bool}:
  match bf:
    case []:
      M4.gd.tt(M4.gd.gf(bd, rw, he, pt, [], sk), Bool.and(gd.spm(SCon{cc, tl}, 1, tl), D1.counts(tl, 1)), eg,
        M4.gd.tt(gd.spm(SCon{cc, tl}, 1, tl), D1.counts(tl, 1),
          M4.gd.tt(T.wf.char(cc), L1.gd.sp(tl, True{}, 0, tl), ec, gd.sp.full(tl, 0, tl, et, gd.ln.self(tl))),
          M4.gd.r(Bool.not(U32.is_zero(1)), D1.counts(tl, 1), es)))
    case +bh <> +bt:
      M4.gd.flex(T.LQ{}, qk, bd, rw, hs, he, pt, bh <> bt, bk, sk, un, lf, at, eg, cc, ec)

# a forbidden control goes the old way; any other starts a span
def gd.ook(
  badc: Bool,
  +ba: Bool,
  +qq: Char,
  +qk: T.QKind,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +bf: List<&2, Char>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +cc: Char,
  +tl: String,
  +eg: {M4.gd.gf(bd, rw, he, pt, bf, sk) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool},
  +et: {T.wf.text(tl) == True{} : Bool},
  +es: {D1.short(SCon{cc, tl}) == True{} : Bool}
) -> {L1.gd.md(T.doc.open.ok(badc, ba, qq, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc, tl),
  tl) == True{} : Bool}:
  match badc:
    case True{}:
      M4.gd.flex(T.LQ{}, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, eg, cc, ec)
    case False{}:
      gd.obuf(bf, ba, qq, qk, bd, rw, hs, he, pt, bk, sk, un, lf, at, cc, tl, eg, ec, et, es)

# a backslash in a basic string goes the old way
def gd.obs(
  bs: Bool,
  +qq: Char,
  +qk: T.QKind,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +bf: List<&2, Char>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +cc: Char,
  +tl: String,
  +eg: {M4.gd.gf(bd, rw, he, pt, bf, sk) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool},
  +et: {T.wf.text(tl) == True{} : Bool},
  +es: {D1.short(SCon{cc, tl}) == True{} : Bool}
) -> {L1.gd.md(T.doc.open.bs(bs, qq, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc, tl), tl) == True{} : Bool}:
  match bs:
    case True{}:
      M4.gd.flex(T.LQ{}, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, eg, cc, ec)
    case False{}:
      gd.ook(T.str.bad(Char.to_u32(cc), False{}), True{}, qq, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc, tl,
        eg, ec, et, es)

# a literal string keeps a backslash; a basic string does not
def gd.ob(
  ba: Bool,
  +qq: Char,
  +qk: T.QKind,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +bf: List<&2, Char>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +cc: Char,
  +tl: String,
  +eg: {M4.gd.gf(bd, rw, he, pt, bf, sk) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool},
  +et: {T.wf.text(tl) == True{} : Bool},
  +es: {D1.short(SCon{cc, tl}) == True{} : Bool}
) -> {L1.gd.md(T.doc.open.b(ba, qq, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc, tl), tl) == True{} : Bool}:
  match ba:
    case False{}:
      gd.ook(T.str.bad(Char.to_u32(cc), False{}), False{}, qq, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc, tl,
        eg, ec, et, es)
    case True{}:
      gd.obs(Char.is_eq(cc, '\\'), qq, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc, tl, eg, ec, et, es)

# a second quote goes the old way
def gd.oq(
  same: Bool,
  +ba: Bool,
  +qq: Char,
  +qk: T.QKind,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +bf: List<&2, Char>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +cc: Char,
  +tl: String,
  +eg: {M4.gd.gf(bd, rw, he, pt, bf, sk) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool},
  +et: {T.wf.text(tl) == True{} : Bool},
  +es: {D1.short(SCon{cc, tl}) == True{} : Bool}
) -> {L1.gd.md(T.doc.open.q(same, ba, qq, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc, tl),
  tl) == True{} : Bool}:
  match same:
    case True{}:
      M4.gd.flex(T.LQ{}, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, eg, cc, ec)
    case False{}:
      gd.ob(ba, qq, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc, tl, eg, ec, et, es)

# the span copied to the buffer, and the character read the old way
def gd.ecopy(
  +ct: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +hh: Char,
  +tt: String,
  +eg: {M4.gd.gf(bd, rw, he, pt, [], sk) == True{} : Bool},
  +ep: {gd.spm(ct, nn, SCon{hh, tt}) == True{} : Bool},
  +eh: {T.wf.char(hh) == True{} : Bool},
  _en: {D1.counts(SCon{hh, tt}, nn) == True{} : Bool}
) -> {L1.gd.md(T.eat.copy(hh, ct, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at), tt) == True{} : Bool}:
  M4.gd.g.str(T.St{bd, rw, hs, he, pt, T.span.rev(ct, nn, U32.is_zero(nn), []), T.LStr{}, T.LStr{}, qk, sk, T.HNone{},
    un, lf, at, False{}}, hh,
    M4.gd.tt(L1.gd.tr(bd, rw, sk), L1.gd.lx(he, pt, T.span.rev(ct, nn, U32.is_zero(nn), []), sk, T.HNone{}),
      M4.gd.l(L1.gd.tr(bd, rw, sk), L1.gd.lx(he, pt, [], sk, T.HNone{}), eg),
      M4.gd.lx.mk(he, pt, T.span.rev(ct, nn, U32.is_zero(nn), []), sk, T.HNone{}, M4.gd.lx.h(he, pt, [], sk, T.HNone{},
        M4.gd.r(L1.gd.tr(bd, rw, sk), L1.gd.lx(he, pt, [], sk, T.HNone{}), eg)), M4.gd.lx.p(he, pt, [], sk, T.HNone{},
          M4.gd.r(L1.gd.tr(bd, rw, sk), L1.gd.lx(he, pt, [], sk, T.HNone{}), eg)),
        gd.sp.rev(ct, U32.is_zero(nn), nn, SCon{hh, tt}, [], ep, {==}), M4.gd.lx.s(he, pt, [], sk, T.HNone{},
          M4.gd.r(L1.gd.tr(bd, rw, sk), L1.gd.lx(he, pt, [], sk, T.HNone{}), eg)), {==})),
    eh)

# the span one character longer
def gd.emore(
  +ba: Bool,
  +qq: Char,
  +ct: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +hh: Char,
  +tt: String,
  +eg: {M4.gd.gf(bd, rw, he, pt, [], sk) == True{} : Bool},
  +ep: {gd.spm(ct, nn, SCon{hh, tt}) == True{} : Bool},
  +en: {D1.counts(SCon{hh, tt}, nn) == True{} : Bool}
) -> {L1.gd.md(T.MEat{ba, qq, ct, U32.add(nn, 1), bd, rw, hs, he, pt, qk, sk, un, lf, at}, tt) == True{} : Bool}:
  M4.gd.tt(M4.gd.gf(bd, rw, he, pt, [], sk), Bool.and(gd.spm(ct, U32.add(nn, 1), tt), D1.counts(tt, U32.add(nn, 1))),
      eg,
    M4.gd.tt(gd.spm(ct, U32.add(nn, 1), tt), D1.counts(tt, U32.add(nn, 1)),
      gd.sp.inc(ct, U32.is_zero(nn), nn, hh, tt, {==},
        M4.gd.not.f(U32.is_zero(U32.add(nn, 1)),
          M4.gd.l(Bool.not(U32.is_zero(U32.add(nn, 1))), D1.counts(tt, U32.add(nn, 1)), en)),
        ep),
      M4.gd.r(Bool.not(U32.is_zero(U32.add(nn, 1))), D1.counts(tt, U32.add(nn, 1)), en)))

# a forbidden control copies the span; a plain character extends it
def gd.ectrl(
  badc: Bool,
  +ba: Bool,
  +qq: Char,
  +ct: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +hh: Char,
  +tt: String,
  +eg: {M4.gd.gf(bd, rw, he, pt, [], sk) == True{} : Bool},
  +ep: {gd.spm(ct, nn, SCon{hh, tt}) == True{} : Bool},
  +en: {D1.counts(SCon{hh, tt}, nn) == True{} : Bool},
  +eh: {T.wf.char(hh) == True{} : Bool}
) -> {L1.gd.md(T.eat.ctrl(badc, ba, qq, hh, ct, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at), tt) == True{} : Bool}:
  match badc:
    case True{}:
      gd.ecopy(ct, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at, hh, tt, eg, ep, eh, en)
    case False{}:
      gd.emore(ba, qq, ct, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at, hh, tt, eg, ep, en)

# a backslash in a basic string copies the span
def gd.ebs(
  bs: Bool,
  +ba: Bool,
  +qq: Char,
  +ct: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +hh: Char,
  +tt: String,
  +eg: {M4.gd.gf(bd, rw, he, pt, [], sk) == True{} : Bool},
  +ep: {gd.spm(ct, nn, SCon{hh, tt}) == True{} : Bool},
  +en: {D1.counts(SCon{hh, tt}, nn) == True{} : Bool},
  +eh: {T.wf.char(hh) == True{} : Bool}
) -> {L1.gd.md(T.eat.bs(bs, ba, qq, hh, ct, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at), tt) == True{} : Bool}:
  match bs:
    case True{}:
      gd.ecopy(ct, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at, hh, tt, eg, ep, eh, en)
    case False{}:
      gd.ectrl(T.str.bad(Char.to_u32(hh), False{}), ba, qq, ct, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at, hh, tt,
        eg, ep, en, eh)

# a literal string's character, or a basic string's
def gd.ebasic(
  ba: Bool,
  +qq: Char,
  +ct: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +hh: Char,
  +tt: String,
  +eg: {M4.gd.gf(bd, rw, he, pt, [], sk) == True{} : Bool},
  +ep: {gd.spm(ct, nn, SCon{hh, tt}) == True{} : Bool},
  +en: {D1.counts(SCon{hh, tt}, nn) == True{} : Bool},
  +eh: {T.wf.char(hh) == True{} : Bool}
) -> {L1.gd.md(T.eat.basic(ba, qq, hh, ct, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at), tt) == True{} : Bool}:
  match ba:
    case False{}:
      gd.ectrl(T.str.bad(Char.to_u32(hh), False{}), False{}, qq, ct, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at, hh,
        tt, eg, ep, en, eh)
    case True{}:
      gd.ebs(Char.is_eq(hh, '\\'), True{}, qq, ct, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at, hh, tt, eg, ep, en, eh)

# the quote closes the span as a VSpan; any other character goes on
def gd.eq(
  quote: Bool,
  +ba: Bool,
  +qq: Char,
  +ct: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +hh: Char,
  +tt: String,
  +eg: {M4.gd.gf(bd, rw, he, pt, [], sk) == True{} : Bool},
  +ep: {gd.spm(ct, nn, SCon{hh, tt}) == True{} : Bool},
  +en: {D1.counts(SCon{hh, tt}, nn) == True{} : Bool},
  +eh: {T.wf.char(hh) == True{} : Bool}
) -> {L1.gd.md(T.eat.feed.q(quote, ba, qq, hh, ct, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at), tt) == True{} : Bool}:
  match quote:
    case True{}:
      M4.gd.g.take(T.St{bd, rw, hs, he, pt, [], T.LStr{}, T.LStr{}, qk, sk, T.HNone{}, un, lf, at, False{}},
        T.VSpan{ct, nn}, eg,
        M4.gd.okv.of(T.St{bd, rw, hs, he, pt, [], T.LStr{}, T.LStr{}, qk, sk, T.HNone{}, un, lf, at, False{}},
          T.VSpan{ct, nn}, L1.gd_span_wf(ct, nn, SCon{hh, tt}, ep)))
    case False{}:
      gd.ebasic(ba, qq, ct, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at, hh, tt, eg, ep, en, eh)

def L1.gd_mode_step(mode, hh, tt, em, eh, et, es) :
  match mode:
    case T.MOpen{+ba, +qq, +qk, +bd, +rw, +hs, +he, +pt, +bf, +bk, +sk, +un, +lf, +at}:
      gd.oq(Char.is_eq(hh, qq), ba, qq, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, hh, tt, em, eh, et, es)
    case T.MEat{+ba, +qq, +ct, +nn, +bd, +rw, +hs, +he, +pt, +qk, +sk, +un, +lf, +at}:
      gd.eq(Char.is_eq(hh, qq), ba, qq, ct, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at, hh, tt,
        M4.gd.l(M4.gd.gf(bd, rw, he, pt, [], sk), Bool.and(gd.spm(ct, nn, SCon{hh, tt}), D1.counts(SCon{hh, tt}, nn)),
            em),
        M4.gd.l(gd.spm(ct, nn, SCon{hh, tt}), D1.counts(SCon{hh, tt}, nn),
          M4.gd.r(M4.gd.gf(bd, rw, he, pt, [], sk), Bool.and(gd.spm(ct, nn, SCon{hh, tt}), D1.counts(SCon{hh, tt}, nn)),
            em)),
        M4.gd.r(gd.spm(ct, nn, SCon{hh, tt}), D1.counts(SCon{hh, tt}, nn),
          M4.gd.r(M4.gd.gf(bd, rw, he, pt, [], sk), Bool.and(gd.spm(ct, nn, SCon{hh, tt}), D1.counts(SCon{hh, tt}, nn)),
            em)),
        eh)
    case T.MScan{+st}:
      gd.sdq(Char.is_eq(hh, '"'), Char.is_eq(hh, '\''), U32.is_eq(Char.to_u32(hh), 13), st, hh, tt, em, eh)
    case T.MCr{+st}:
      gd.dcr(Char.is_eq(hh, '\n'), st, hh, tt, em, eh)

# an unfinished document is an error, so a document with no error is not one
def gd.unc(
  +st: T.St,
  +eo: {String.is_empty(T.bad(T.read.fin.unclosed(st))) == True{} : Bool}
) -> {T.wf(T.read.fin.unclosed(st)) == True{} : Bool}:
  match st:
    case T.St{+bd, +rw, +hs, +he, +pt, +bf, +lx, +bk, +qk, +sk, +hd, +un, +lf, +at, +ld}:
      match bd:
        case SNil{}:
          Eq.bit.absurd(&2, {T.wf(T.read.fin.unclosed(T.St{"", rw, hs, he, pt, bf, lx, bk, qk, sk, hd, un, lf, at,
            ld})) == True{} : Bool}, eo)
        case SCon{+bh, +bt}:
          Eq.bit.absurd(&2, {T.wf(T.read.fin.unclosed(T.St{SCon{bh, bt}, rw, hs, he, pt, bf, lx, bk, qk, sk, hd, un,
            lf, at, ld})) == True{} : Bool}, eo)

# a token still open at the end is closed: a bare word read as a value, an
# empty string or a multiline string placed
def gd.rlex(
  lx: T.Lex,
  +st: T.St,
  +eg: {L1.good(st) == True{} : Bool}
) -> {L1.good(T.read.fin.lex(lx, st)) == True{} : Bool}:
  match lx:
    case T.LTop{}:
      eg
    case T.LLine{}:
      eg
    case T.LKey{}:
      eg
    case T.LKeyDot{}:
      eg
    case T.LAfter{}:
      eg
    case T.LKeyQ{}:
      eg
    case T.LKeyE{}:
      eg
    case T.LKeyU{}:
      eg
    case T.LVal{}:
      eg
    case T.LQ{}:
      eg
    case T.LQ2{}:
      M4.gd.g.take(st, T.VStr{""}, eg, M4.gd.okv.of(st, T.VStr{""}, {==}))
    case T.LStr{}:
      eg
    case T.LEsc{}:
      eg
    case T.LUni{}:
      eg
    case T.LFold{}:
      eg
    case T.LMq{}:
      eg
    case T.LMqEnd{}:
      M4.gd.g.strfin(st, eg)
    case T.LTrim{}:
      eg
    case T.LTrim2{}:
      eg
    case T.LBare{}:
      M4.gd.g.bfin(st, ' ', False{}, eg, {==})
    case T.LDate{}:
      M4.gd.g.bfin(st, ' ', False{}, eg, {==})
    case T.LCom{}:
      eg
    case T.LHead{}:
      eg
    case T.LHeadGap{}:
      eg
    case T.LHeadDot{}:
      eg
    case T.LHeadQ{}:
      eg
    case T.LHeadE{}:
      eg
    case T.LHeadU{}:
      eg
    case T.LHeadR{}:
      eg
    case T.LArr{}:
      eg
    case T.LArrC{}:
      eg
    case T.LInl{}:
      eg
    case T.LInlK{}:
      eg
    case T.LInlC{}:
      eg
    case T.LSink{}:
      eg

# the end's token closed, read off the state
def gd.rclose(+st: T.St, +eg: {L1.good(st) == True{} : Bool}) -> {L1.good(T.read.fin.close(st)) == True{} : Bool}:
  match st:
    case T.St{+bd, +rw, +hs, +he, +pt, +bf, +lx, +bk, +qk, +sk, +hd, +un, +lf, +at, +ld}:
      gd.rlex(lx, T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, hd, un, lf, at, ld}, eg)

# a comment at the end ends the document where the line could, and is an
# error anywhere else
def gd.rcom(
  ok: Bool,
  +st: T.St,
  +eg: {L1.good(st) == True{} : Bool},
  +eo: {String.is_empty(T.bad(T.read.fin.com(ok, st))) == True{} : Bool}
) -> {T.wf(T.read.fin.com(ok, st)) == True{} : Bool}:
  match ok:
    case True{}:
      L1.gd_fin(st, eg, eo)
    case False{}:
      gd.unc(st, eo)

# a comment at the end, read off the state
def gd.rcomst(
  +st: T.St,
  +eg: {L1.good(st) == True{} : Bool},
  +eo: {String.is_empty(T.bad(T.read.fin.com.st(st))) == True{} : Bool}
) -> {T.wf(T.read.fin.com.st(st)) == True{} : Bool}:
  match st:
    case T.St{+bd, +rw, +hs, +he, +pt, +bf, +lx, +bk, +qk, +sk, +hd, +un, +lf, +at, +ld}:
      gd.rcom(T.read.fin.end(bk), T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, hd, un, lf, at, ld}, eg, eo)

# the states that may end a document end it; any other is an error
def gd.rok(
  lx: T.Lex,
  +st: T.St,
  +eg: {L1.good(st) == True{} : Bool},
  +eo: {String.is_empty(T.bad(T.read.fin.ok(lx, st))) == True{} : Bool}
) -> {T.wf(T.read.fin.ok(lx, st)) == True{} : Bool}:
  match lx:
    case T.LTop{}:
      L1.gd_fin(st, eg, eo)
    case T.LLine{}:
      L1.gd_fin(st, eg, eo)
    case T.LKey{}:
      gd.unc(st, eo)
    case T.LKeyDot{}:
      gd.unc(st, eo)
    case T.LAfter{}:
      gd.unc(st, eo)
    case T.LKeyQ{}:
      gd.unc(st, eo)
    case T.LKeyE{}:
      gd.unc(st, eo)
    case T.LKeyU{}:
      gd.unc(st, eo)
    case T.LVal{}:
      gd.unc(st, eo)
    case T.LQ{}:
      gd.unc(st, eo)
    case T.LQ2{}:
      gd.unc(st, eo)
    case T.LStr{}:
      gd.unc(st, eo)
    case T.LEsc{}:
      gd.unc(st, eo)
    case T.LUni{}:
      gd.unc(st, eo)
    case T.LFold{}:
      gd.unc(st, eo)
    case T.LMq{}:
      gd.unc(st, eo)
    case T.LMqEnd{}:
      gd.unc(st, eo)
    case T.LTrim{}:
      gd.unc(st, eo)
    case T.LTrim2{}:
      gd.unc(st, eo)
    case T.LBare{}:
      gd.unc(st, eo)
    case T.LDate{}:
      gd.unc(st, eo)
    case T.LCom{}:
      gd.rcomst(st, eg, eo)
    case T.LHead{}:
      gd.unc(st, eo)
    case T.LHeadGap{}:
      gd.unc(st, eo)
    case T.LHeadDot{}:
      gd.unc(st, eo)
    case T.LHeadQ{}:
      gd.unc(st, eo)
    case T.LHeadE{}:
      gd.unc(st, eo)
    case T.LHeadU{}:
      gd.unc(st, eo)
    case T.LHeadR{}:
      gd.unc(st, eo)
    case T.LArr{}:
      gd.unc(st, eo)
    case T.LArrC{}:
      gd.unc(st, eo)
    case T.LInl{}:
      gd.unc(st, eo)
    case T.LInlK{}:
      gd.unc(st, eo)
    case T.LInlC{}:
      gd.unc(st, eo)
    case T.LSink{}:
      L1.gd_fin(st, eg, eo)

# the end, read off the closed state
def gd.rfin2(
  +st: T.St,
  +eg: {L1.good(st) == True{} : Bool},
  +eo: {String.is_empty(T.bad(T.read.fin2(st))) == True{} : Bool}
) -> {T.wf(T.read.fin2(st)) == True{} : Bool}:
  match st:
    case T.St{+bd, +rw, +hs, +he, +pt, +bf, +lx, +bk, +qk, +sk, +hd, +un, +lf, +at, +ld}:
      gd.rok(lx, T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, hd, un, lf, at, ld}, eg, eo)

# a good state at the end of the text gives a well-formed document, unless
# it gives an error
def gd.rfin(
  +st: T.St,
  +eg: {L1.good(st) == True{} : Bool},
  +eo: {String.is_empty(T.bad(T.read.fin(st))) == True{} : Bool}
) -> {T.wf(T.read.fin(st)) == True{} : Bool}:
  gd.rfin2(T.read.fin.close(st), gd.rclose(st, eg), eo)

# the text runs out: in a scanning state, after a carriage return, after an
# opening quote, or in a span, which is an error
def gd.dend(
  mode: T.Mode,
  +em: {L1.gd.md(mode, SNil{}) == True{} : Bool},
  +eo: {String.is_empty(T.bad(T.doc.read(SNil{}, mode))) == True{} : Bool}
) -> {T.wf(T.doc.read(SNil{}, mode)) == True{} : Bool}:
  match mode:
    case T.MScan{+st}:
      gd.rfin(T.read.once2(st), M4.gd.once2(st, em), eo)
    case T.MCr{+st}:
      gd.rfin(T.read.once2(T.st.err(st, "carriage return without line feed")),
        M4.gd.once2(T.st.err(st, "carriage return without line feed"),
          M4.gd.g.err2(st, "carriage return without line feed", em)), eo)
    case T.MOpen{_ba, _qq, +qk, +bd, +rw, +hs, +he, +pt, +bf, +bk, +sk, +un, +lf, +at}:
      gd.rfin(T.read.once2(T.St{bd, rw, hs, he, pt, bf, T.LQ{}, bk, qk, sk, T.HNone{}, un, lf, at, False{}}),
        M4.gd.once2(T.St{bd, rw, hs, he, pt, bf, T.LQ{}, bk, qk, sk, T.HNone{}, un, lf, at, False{}}, em), eo)
    case T.MEat{_ba, _qq, _ct, _nn, +bd, +rw, +hs, +he, +pt, +qk, +sk, +un, +lf, +at}:
      gd.unc(T.St{bd, rw, hs, he, pt, [], T.LStr{}, T.LStr{}, qk, sk, T.HNone{}, un, lf, at, False{}}, eo)

# doc.read's error, one character on
def gd.nexto(
  +mode: T.Mode,
  +hh: Char,
  +tt: String,
  +eo: {String.is_empty(T.bad(T.doc.read(SCon{hh, tt}, mode))) == True{} : Bool}
) -> {String.is_empty(T.bad(T.doc.read(tt, L1.gd.next(mode, hh, tt)))) == True{} : Bool}:
  Equal.trans(Bool, String.is_empty(T.bad(T.doc.read(tt, L1.gd.next(mode, hh, tt)))),
    String.is_empty(T.bad(T.doc.read(SCon{hh, tt}, mode))), True{},
    Equal.sym(Bool, String.is_empty(T.bad(T.doc.read(SCon{hh, tt}, mode))),
      String.is_empty(T.bad(T.doc.read(tt, L1.gd.next(mode, hh, tt)))),
      Equal.cong(T.Doc, Bool, dd => String.is_empty(T.bad(dd)), T.doc.read(SCon{hh, tt}, mode),
        T.doc.read(tt, L1.gd.next(mode, hh, tt)), L1.gd_next(mode, hh, tt))),
    eo)

# doc.read's document, one character on
def gd.nextw(
  +mode: T.Mode,
  +hh: Char,
  +tt: String,
  +ew: {T.wf(T.doc.read(tt, L1.gd.next(mode, hh, tt))) == True{} : Bool}
) -> {T.wf(T.doc.read(SCon{hh, tt}, mode)) == True{} : Bool}:
  Equal.trans(Bool, T.wf(T.doc.read(SCon{hh, tt}, mode)), T.wf(T.doc.read(tt, L1.gd.next(mode, hh, tt))), True{},
    Equal.cong(T.Doc, Bool, dd => T.wf(dd), T.doc.read(SCon{hh, tt}, mode),
      T.doc.read(tt, L1.gd.next(mode, hh, tt)), L1.gd_next(mode, hh, tt)),
    ew)

def L1.gd_read(text, mode, em, ew, es, eo) :
  match text:
    case SNil{}:
      gd.dend(mode, em, eo)
    case SCon{+hh, +tt}:
      gd.nextw(mode, hh, tt,
        L1.gd_read(tt, L1.gd.next(mode, hh, tt),
          L1.gd_mode_step(mode, hh, tt, em, gd.th.l(T.wf.char(hh), _u => T.wf.text(tt), ew),
            gd.th.r(T.wf.char(hh), _u => T.wf.text(tt), ew), es),
          gd.th.r(T.wf.char(hh), _u => T.wf.text(tt), ew),
          M4.gd.short.tail(hh, tt, es),
          gd.nexto(mode, hh, tt, eo)))

def L1.parse_wf(text, ew, es, eo) :
  L1.gd_read(text, T.MScan{T.st.start()},
    L1.gd_start([], [], [], T.LTop{}, T.LTop{}, T.QBasic{}, 0, 0, False{}, True{}, {==}, {==}), ew, es, eo)
