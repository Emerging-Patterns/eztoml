# reading spans out of a value keeps comparisons and scalar fields
import Base
import ../../main.bend as T
import ../../laws/defs/BareValueGrammar.bend as D1
import ../../laws/defs/DocumentSameness.bend as D2

# `own` changes no answer of `same`. own.rows reads a span out as an owned
# string of the same characters, and same compares strings by characters.

# one value with its spans read out, as own.rows writes a value it holds
def own.val(vv: T.Val) -> T.Val:
  match vv:
    case T.VSpan{src, +kk}:
      T.VStr{T.span.str(src, kk, U32.is_zero(kk))}
    case T.VArr{ls}:
      T.VArr{D1.own.rows(ls)}
    case T.VInl{ls}:
      T.VInl{D1.own.rows(ls)}
    case T.VHead{pa, ls}:
      T.VHead{pa, D1.own.rows(ls)}
    case T.VAot{pa, ls}:
      T.VAot{pa, D1.own.rows(ls)}
    case T.VAots{pa, ls}:
      T.VAots{pa, D1.own.rows(ls)}
    case other:
      other

# one row with its spans read out: a pair's value, or the value itself
def own.elem(hh: T.Val) -> T.Val:
  match hh:
    case T.VPair{nn, vv}:
      T.VPair{nn, own.val(vv)}
    case other:
      own.val(other)

# a pick with its spans read out
def pick.own(pp: D2.Pick) -> D2.Pick:
  match pp:
    case D2.Picked{vv, rest}:
      D2.Picked{own.val(vv), D1.own.rows(rest)}
    case D2.NoPick{}:
      D2.NoPick{}

# a box with its spans read out
def box.own(bx: D2.Box) -> D2.Box:
  match bx:
    case D2.Boxed{kk, ls}:
      D2.Boxed{kk, D1.own.rows(ls)}
    case D2.Unboxed{}:
      D2.Unboxed{}

# own.rows reads out one row at a time
def own.cons(
  hh: T.Val,
  tt: List<&2, T.Val>
) -> {D1.own.rows(hh <> tt) == own.elem(hh) <> D1.own.rows(tt) : List<&2, T.Val>}:
  match hh:
    case T.VPair{nn, vv}:
      match vv:
        case T.VStr{a1}:
          {==}
        case T.VSpan{a1, a2}:
          {==}
        case T.VInt{a1, a2}:
          {==}
        case T.VFlo{a1, a2}:
          {==}
        case T.VBool{a1}:
          {==}
        case T.VWhen{a1}:
          {==}
        case T.VArr{ls}:
          {==}
        case T.VInl{ls}:
          {==}
        case T.VHead{pa, ls}:
          {==}
        case T.VAot{pa, ls}:
          {==}
        case T.VAots{pa, ls}:
          {==}
        case T.VPair{a1, a2}:
          {==}
    case T.VStr{a1}:
      {==}
    case T.VSpan{a1, a2}:
      {==}
    case T.VInt{a1, a2}:
      {==}
    case T.VFlo{a1, a2}:
      {==}
    case T.VBool{a1}:
      {==}
    case T.VWhen{a1}:
      {==}
    case T.VArr{ls}:
      {==}
    case T.VInl{ls}:
      {==}
    case T.VHead{pa, ls}:
      {==}
    case T.VAot{pa, ls}:
      {==}
    case T.VAots{pa, ls}:
      {==}

# the list a value holds, read out
def kids.own(ww: T.Val) -> {D2.kids(own.val(ww)) == box.own(D2.kids(ww)) : D2.Box}:
  match ww:
    case T.VStr{a1}:
      {==}
    case T.VSpan{a1, a2}:
      {==}
    case T.VInt{a1, a2}:
      {==}
    case T.VFlo{a1, a2}:
      {==}
    case T.VBool{a1}:
      {==}
    case T.VWhen{a1}:
      {==}
    case T.VArr{ls}:
      {==}
    case T.VInl{ls}:
      {==}
    case T.VHead{pa, ls}:
      {==}
    case T.VAot{pa, ls}:
      {==}
    case T.VAots{pa, ls}:
      {==}
    case T.VPair{a1, a2}:
      {==}

# the list a row holds, read out
def kids.own.e(ww: T.Val) -> {D2.kids(own.elem(ww)) == box.own(D2.kids(ww)) : D2.Box}:
  match ww:
    case T.VStr{a1}:
      {==}
    case T.VSpan{a1, a2}:
      {==}
    case T.VInt{a1, a2}:
      {==}
    case T.VFlo{a1, a2}:
      {==}
    case T.VBool{a1}:
      {==}
    case T.VWhen{a1}:
      {==}
    case T.VArr{ls}:
      {==}
    case T.VInl{ls}:
      {==}
    case T.VHead{pa, ls}:
      {==}
    case T.VAot{pa, ls}:
      {==}
    case T.VAots{pa, ls}:
      {==}
    case T.VPair{a1, a2}:
      {==}

# reading out keeps a scalar's fields
def scal.own(ww: T.Val) -> {D2.scal(own.val(ww)) == D2.scal(ww) : D2.Sc}:
  match ww:
    case T.VStr{a1}:
      {==}
    case T.VSpan{a1, a2}:
      {==}
    case T.VInt{a1, a2}:
      {==}
    case T.VFlo{a1, a2}:
      {==}
    case T.VBool{a1}:
      {==}
    case T.VWhen{a1}:
      {==}
    case T.VArr{ls}:
      {==}
    case T.VInl{ls}:
      {==}
    case T.VHead{pa, ls}:
      {==}
    case T.VAot{pa, ls}:
      {==}
    case T.VAots{pa, ls}:
      {==}
    case T.VPair{a1, a2}:
      {==}

# and a row's
def scal.own.e(ww: T.Val) -> {D2.scal(own.elem(ww)) == D2.scal(ww) : D2.Sc}:
  match ww:
    case T.VStr{a1}:
      {==}
    case T.VSpan{a1, a2}:
      {==}
    case T.VInt{a1, a2}:
      {==}
    case T.VFlo{a1, a2}:
      {==}
    case T.VBool{a1}:
      {==}
    case T.VWhen{a1}:
      {==}
    case T.VArr{ls}:
      {==}
    case T.VInl{ls}:
      {==}
    case T.VHead{pa, ls}:
      {==}
    case T.VAot{pa, ls}:
      {==}
    case T.VAots{pa, ls}:
      {==}
    case T.VPair{a1, a2}:
      {==}

# a then whose rests agree
def at.cong2(
  bb: Bool,
  -m1: Unit -> Bool,
  -m2: Unit -> Bool,
  em: {m1(Unit{}) == m2(Unit{}) : Bool}
) -> {D2.and_then(bb, m1) == D2.and_then(bb, m2) : Bool}:
  match bb:
    case True{}:
      em
    case False{}:
      {==}

# a then whose parts and rests agree
def at.cong(
  -b1: Bool,
  b2: Bool,
  eb: {b1 == b2 : Bool},
  -m1: Unit -> Bool,
  -m2: Unit -> Bool,
  em: {m1(Unit{}) == m2(Unit{}) : Bool}
) -> {D2.and_then(b1, m1) == D2.and_then(b2, m2) : Bool}:
  Equal.trans(Bool, D2.and_then(b1, m1), D2.and_then(b2, m1), D2.and_then(b2, m2),
    Equal.cong(Bool, Bool, xx => D2.and_then(xx, m1), b1, b2, eb), at.cong2(b2, m1, m2, em))

# a box compared by comparisons that agree on every list
def boxed.cong(
  kk: D2.Kin,
  bx: D2.Box,
  -f1: List<&2, T.Val> -> Bool,
  -f2: List<&2, T.Val> -> Bool,
  hf: @ls: List<&2, T.Val> -> {f1(ls) == f2(ls) : Bool}
) -> {D2.same.boxed(kk, bx, f1) == D2.same.boxed(kk, bx, f2) : Bool}:
  match bx:
    case D2.Boxed{+k2, +ls}:
      at.cong2(D2.kin.eq(kk, k2), _u => f1(ls), _u => f2(ls), hf(ls))
    case D2.Unboxed{}:
      {==}

# a value compared by comparisons that agree on every list
def box.cong(
  kk: D2.Kin,
  ww: T.Val,
  -f1: List<&2, T.Val> -> Bool,
  -f2: List<&2, T.Val> -> Bool,
  hf: @ls: List<&2, T.Val> -> {f1(ls) == f2(ls) : Bool}
) -> {D2.same.box(kk, ww, f1) == D2.same.box(kk, ww, f2) : Bool}:
  boxed.cong(kk, D2.kids(ww), f1, f2, hf)

# a pick compared by comparisons and rests that agree
def pair.cong(
  pp: D2.Pick,
  -c1: T.Val -> Bool,
  c2: T.Val -> Bool,
  -r1: List<&2, T.Val> -> Bool,
  -r2: List<&2, T.Val> -> Bool,
  hc: @vv: T.Val -> {c1(vv) == c2(vv) : Bool},
  hr: @ls: List<&2, T.Val> -> {r1(ls) == r2(ls) : Bool}
) -> {D2.same.pair(pp, c1, r1) == D2.same.pair(pp, c2, r2) : Bool}:
  match pp:
    case D2.Picked{+ww, +left}:
      at.cong(c1(ww), c2(ww), hc(ww), _u => r1(left), _u => r2(left), hr(left))
    case D2.NoPick{}:
      {==}

# the other rows' first value compared by comparisons and rests that agree
def item.cong(
  oo: List<&2, T.Val>,
  -c1: T.Val -> Bool,
  c2: T.Val -> Bool,
  -r1: List<&2, T.Val> -> Bool,
  -r2: List<&2, T.Val> -> Bool,
  hc: @vv: T.Val -> {c1(vv) == c2(vv) : Bool},
  hr: @ls: List<&2, T.Val> -> {r1(ls) == r2(ls) : Bool}
) -> {D2.same.item(oo, c1, r1) == D2.same.item(oo, c2, r2) : Bool}:
  match oo:
    case []:
      {==}
    case +ww <> +left:
      at.cong(c1(ww), c2(ww), hc(ww), _u => r1(left), _u => r2(left), hr(left))

# rows read out compare as the rows do, against any other rows
def own.l(
  xs: List<&2, T.Val>,
  +oo: List<&2, T.Val>
) -> {D2.same.go(D1.own.rows(xs), oo) == D2.same.go(xs, oo) : Bool}:
  match xs:
    case []:
      {==}
    case T.VPair{+nn, T.VStr{+a1}} <> +tt:
      pair.cong(D2.pick(oo, nn), ww => D2.same.atom(T.VStr{a1}, ww),
        ww => D2.same.atom(T.VStr{a1}, ww),
        rr => D2.same.go(D1.own.rows(tt), rr), rr => D2.same.go(tt, rr),
        _ww => {==},
        rr => own.l(tt, rr))
    case T.VPair{+nn, T.VSpan{+a1, +a2}} <> +tt:
      pair.cong(D2.pick(oo, nn), ww => D2.same.atom(T.VStr{T.span.str(a1, a2, U32.is_zero(a2))}, ww),
        ww => D2.same.atom(T.VSpan{a1, a2}, ww),
        rr => D2.same.go(D1.own.rows(tt), rr), rr => D2.same.go(tt, rr),
        _ww => {==},
        rr => own.l(tt, rr))
    case T.VPair{+nn, T.VInt{+a1, +a2}} <> +tt:
      pair.cong(D2.pick(oo, nn), ww => D2.same.atom(T.VInt{a1, a2}, ww),
        ww => D2.same.atom(T.VInt{a1, a2}, ww),
        rr => D2.same.go(D1.own.rows(tt), rr), rr => D2.same.go(tt, rr),
        _ww => {==},
        rr => own.l(tt, rr))
    case T.VPair{+nn, T.VFlo{+a1, +a2}} <> +tt:
      pair.cong(D2.pick(oo, nn), ww => D2.same.atom(T.VFlo{a1, a2}, ww),
        ww => D2.same.atom(T.VFlo{a1, a2}, ww),
        rr => D2.same.go(D1.own.rows(tt), rr), rr => D2.same.go(tt, rr),
        _ww => {==},
        rr => own.l(tt, rr))
    case T.VPair{+nn, T.VBool{+a1}} <> +tt:
      pair.cong(D2.pick(oo, nn), ww => D2.same.atom(T.VBool{a1}, ww),
        ww => D2.same.atom(T.VBool{a1}, ww),
        rr => D2.same.go(D1.own.rows(tt), rr), rr => D2.same.go(tt, rr),
        _ww => {==},
        rr => own.l(tt, rr))
    case T.VPair{+nn, T.VWhen{+a1}} <> +tt:
      pair.cong(D2.pick(oo, nn), ww => D2.same.atom(T.VWhen{a1}, ww),
        ww => D2.same.atom(T.VWhen{a1}, ww),
        rr => D2.same.go(D1.own.rows(tt), rr), rr => D2.same.go(tt, rr),
        _ww => {==},
        rr => own.l(tt, rr))
    case T.VPair{+nn, T.VArr{+ls}} <> +tt:
      pair.cong(D2.pick(oo, nn), ww => D2.same.box(D2.KArr{}, ww, ws => D2.same.go(D1.own.rows(ls), ws)),
        ww => D2.same.box(D2.KArr{}, ww, ws => D2.same.go(ls, ws)),
        rr => D2.same.go(D1.own.rows(tt), rr), rr => D2.same.go(tt, rr),
        ww => box.cong(D2.KArr{}, ww, ws => D2.same.go(D1.own.rows(ls), ws), ws => D2.same.go(ls, ws),
          ws => own.l(ls, ws)),
        rr => own.l(tt, rr))
    case T.VPair{+nn, T.VInl{+ls}} <> +tt:
      pair.cong(D2.pick(oo, nn), ww => D2.same.box(D2.KInl{}, ww, ws => D2.same.go(D1.own.rows(ls), ws)),
        ww => D2.same.box(D2.KInl{}, ww, ws => D2.same.go(ls, ws)),
        rr => D2.same.go(D1.own.rows(tt), rr), rr => D2.same.go(tt, rr),
        ww => box.cong(D2.KInl{}, ww, ws => D2.same.go(D1.own.rows(ls), ws), ws => D2.same.go(ls, ws),
          ws => own.l(ls, ws)),
        rr => own.l(tt, rr))
    case T.VPair{+nn, T.VHead{+pa, +ls}} <> +tt:
      pair.cong(D2.pick(oo, nn), ww => D2.same.box(D2.KHead{}, ww, ws => D2.same.go(D1.own.rows(ls), ws)),
        ww => D2.same.box(D2.KHead{}, ww, ws => D2.same.go(ls, ws)),
        rr => D2.same.go(D1.own.rows(tt), rr), rr => D2.same.go(tt, rr),
        ww => box.cong(D2.KHead{}, ww, ws => D2.same.go(D1.own.rows(ls), ws), ws => D2.same.go(ls, ws),
          ws => own.l(ls, ws)),
        rr => own.l(tt, rr))
    case T.VPair{+nn, T.VAot{+pa, +ls}} <> +tt:
      pair.cong(D2.pick(oo, nn), ww => D2.same.box(D2.KAot{}, ww, ws => D2.same.go(D1.own.rows(ls), ws)),
        ww => D2.same.box(D2.KAot{}, ww, ws => D2.same.go(ls, ws)),
        rr => D2.same.go(D1.own.rows(tt), rr), rr => D2.same.go(tt, rr),
        ww => box.cong(D2.KAot{}, ww, ws => D2.same.go(D1.own.rows(ls), ws), ws => D2.same.go(ls, ws),
          ws => own.l(ls, ws)),
        rr => own.l(tt, rr))
    case T.VPair{+nn, T.VAots{+pa, +ls}} <> +tt:
      pair.cong(D2.pick(oo, nn), ww => D2.same.box(D2.KAots{}, ww, ws => D2.same.go(D1.own.rows(ls), ws)),
        ww => D2.same.box(D2.KAots{}, ww, ws => D2.same.go(ls, ws)),
        rr => D2.same.go(D1.own.rows(tt), rr), rr => D2.same.go(tt, rr),
        ww => box.cong(D2.KAots{}, ww, ws => D2.same.go(D1.own.rows(ls), ws), ws => D2.same.go(ls, ws),
          ws => own.l(ls, ws)),
        rr => own.l(tt, rr))
    case T.VPair{+nn, T.VPair{+a1, +a2}} <> +tt:
      pair.cong(D2.pick(oo, nn), ww => D2.same.atom(T.VPair{a1, a2}, ww),
        ww => D2.same.atom(T.VPair{a1, a2}, ww),
        rr => D2.same.go(D1.own.rows(tt), rr), rr => D2.same.go(tt, rr),
        _ww => {==},
        rr => own.l(tt, rr))
    case T.VStr{+a1} <> +tt:
      item.cong(oo, ww => D2.same.atom(T.VStr{a1}, ww),
        ww => D2.same.atom(T.VStr{a1}, ww),
        rr => D2.same.go(D1.own.rows(tt), rr), rr => D2.same.go(tt, rr),
        _ww => {==},
        rr => own.l(tt, rr))
    case T.VSpan{+a1, +a2} <> +tt:
      item.cong(oo, ww => D2.same.atom(T.VStr{T.span.str(a1, a2, U32.is_zero(a2))}, ww),
        ww => D2.same.atom(T.VSpan{a1, a2}, ww),
        rr => D2.same.go(D1.own.rows(tt), rr), rr => D2.same.go(tt, rr),
        _ww => {==},
        rr => own.l(tt, rr))
    case T.VInt{+a1, +a2} <> +tt:
      item.cong(oo, ww => D2.same.atom(T.VInt{a1, a2}, ww),
        ww => D2.same.atom(T.VInt{a1, a2}, ww),
        rr => D2.same.go(D1.own.rows(tt), rr), rr => D2.same.go(tt, rr),
        _ww => {==},
        rr => own.l(tt, rr))
    case T.VFlo{+a1, +a2} <> +tt:
      item.cong(oo, ww => D2.same.atom(T.VFlo{a1, a2}, ww),
        ww => D2.same.atom(T.VFlo{a1, a2}, ww),
        rr => D2.same.go(D1.own.rows(tt), rr), rr => D2.same.go(tt, rr),
        _ww => {==},
        rr => own.l(tt, rr))
    case T.VBool{+a1} <> +tt:
      item.cong(oo, ww => D2.same.atom(T.VBool{a1}, ww),
        ww => D2.same.atom(T.VBool{a1}, ww),
        rr => D2.same.go(D1.own.rows(tt), rr), rr => D2.same.go(tt, rr),
        _ww => {==},
        rr => own.l(tt, rr))
    case T.VWhen{+a1} <> +tt:
      item.cong(oo, ww => D2.same.atom(T.VWhen{a1}, ww),
        ww => D2.same.atom(T.VWhen{a1}, ww),
        rr => D2.same.go(D1.own.rows(tt), rr), rr => D2.same.go(tt, rr),
        _ww => {==},
        rr => own.l(tt, rr))
    case T.VArr{+ls} <> +tt:
      item.cong(oo, ww => D2.same.box(D2.KArr{}, ww, ws => D2.same.go(D1.own.rows(ls), ws)),
        ww => D2.same.box(D2.KArr{}, ww, ws => D2.same.go(ls, ws)),
        rr => D2.same.go(D1.own.rows(tt), rr), rr => D2.same.go(tt, rr),
        ww => box.cong(D2.KArr{}, ww, ws => D2.same.go(D1.own.rows(ls), ws), ws => D2.same.go(ls, ws),
          ws => own.l(ls, ws)),
        rr => own.l(tt, rr))
    case T.VInl{+ls} <> +tt:
      item.cong(oo, ww => D2.same.box(D2.KInl{}, ww, ws => D2.same.go(D1.own.rows(ls), ws)),
        ww => D2.same.box(D2.KInl{}, ww, ws => D2.same.go(ls, ws)),
        rr => D2.same.go(D1.own.rows(tt), rr), rr => D2.same.go(tt, rr),
        ww => box.cong(D2.KInl{}, ww, ws => D2.same.go(D1.own.rows(ls), ws), ws => D2.same.go(ls, ws),
          ws => own.l(ls, ws)),
        rr => own.l(tt, rr))
    case T.VHead{+pa, +ls} <> +tt:
      item.cong(oo, ww => D2.same.box(D2.KHead{}, ww, ws => D2.same.go(D1.own.rows(ls), ws)),
        ww => D2.same.box(D2.KHead{}, ww, ws => D2.same.go(ls, ws)),
        rr => D2.same.go(D1.own.rows(tt), rr), rr => D2.same.go(tt, rr),
        ww => box.cong(D2.KHead{}, ww, ws => D2.same.go(D1.own.rows(ls), ws), ws => D2.same.go(ls, ws),
          ws => own.l(ls, ws)),
        rr => own.l(tt, rr))
    case T.VAot{+pa, +ls} <> +tt:
      item.cong(oo, ww => D2.same.box(D2.KAot{}, ww, ws => D2.same.go(D1.own.rows(ls), ws)),
        ww => D2.same.box(D2.KAot{}, ww, ws => D2.same.go(ls, ws)),
        rr => D2.same.go(D1.own.rows(tt), rr), rr => D2.same.go(tt, rr),
        ww => box.cong(D2.KAot{}, ww, ws => D2.same.go(D1.own.rows(ls), ws), ws => D2.same.go(ls, ws),
          ws => own.l(ls, ws)),
        rr => own.l(tt, rr))
    case T.VAots{+pa, +ls} <> +tt:
      item.cong(oo, ww => D2.same.box(D2.KAots{}, ww, ws => D2.same.go(D1.own.rows(ls), ws)),
        ww => D2.same.box(D2.KAots{}, ww, ws => D2.same.go(ls, ws)),
        rr => D2.same.go(D1.own.rows(tt), rr), rr => D2.same.go(tt, rr),
        ww => box.cong(D2.KAots{}, ww, ws => D2.same.go(D1.own.rows(ls), ws), ws => D2.same.go(ls, ws),
          ws => own.l(ls, ws)),
        rr => own.l(tt, rr))

# a pick read out, cons'd onto a row read out
def cons.own(
  +hh: T.Val,
  pp: D2.Pick
) -> {D2.pick.cons(own.elem(hh), pick.own(pp)) == pick.own(D2.pick.cons(hh, pp)) : D2.Pick}:
  match pp:
    case D2.Picked{+vv, +rest}:
      Equal.cong(List<&2, T.Val>, D2.Pick, ls => D2.Picked{own.val(vv), ls},
        own.elem(hh) <> D1.own.rows(rest), D1.own.rows(hh <> rest),
        Equal.sym(List<&2, T.Val>, D1.own.rows(hh <> rest), own.elem(hh) <> D1.own.rows(rest),
          own.cons(hh, rest)))
    case D2.NoPick{}:
      {==}

# a pair of the name is picked the same way from rows read out
def po.step(
  bb: Bool,
  +mm: String,
  +vv: T.Val,
  +uu: List<&2, T.Val>,
  +nn: String,
  ih: {D2.pick(D1.own.rows(uu), nn) == pick.own(D2.pick(uu, nn)) : D2.Pick}
) -> {D2.pick.step(bb, mm, own.val(vv), D1.own.rows(uu), _u => D2.pick(D1.own.rows(uu), nn))
  == pick.own(D2.pick.step(bb, mm, vv, uu, _u => D2.pick(uu, nn))) : D2.Pick}:
  match bb:
    case True{}:
      {==}
    case False{}:
      Equal.trans(D2.Pick,
        D2.pick.cons(T.VPair{mm, own.val(vv)}, D2.pick(D1.own.rows(uu), nn)),
        D2.pick.cons(T.VPair{mm, own.val(vv)}, pick.own(D2.pick(uu, nn))),
        pick.own(D2.pick.cons(T.VPair{mm, vv}, D2.pick(uu, nn))),
        Equal.cong(D2.Pick, D2.Pick, pp => D2.pick.cons(T.VPair{mm, own.val(vv)}, pp),
          D2.pick(D1.own.rows(uu), nn), pick.own(D2.pick(uu, nn)), ih),
        cons.own(T.VPair{mm, vv}, D2.pick(uu, nn)))

# one row of a pick from rows read out
def po.cell(
  kk: T.Val,
  +uu: List<&2, T.Val>,
  +nn: String,
  +ih: {D2.pick(D1.own.rows(uu), nn) == pick.own(D2.pick(uu, nn)) : D2.Pick}
) -> {D2.pick(own.elem(kk) <> D1.own.rows(uu), nn) == pick.own(D2.pick(kk <> uu, nn)) : D2.Pick}:
  match kk:
    case T.VPair{+mm, +vv}:
      po.step(String.eq(mm, nn), mm, vv, uu, nn, ih)
    case T.VStr{+a1}:
      Equal.trans(D2.Pick,
        D2.pick.cons(own.elem(T.VStr{a1}), D2.pick(D1.own.rows(uu), nn)),
        D2.pick.cons(own.elem(T.VStr{a1}), pick.own(D2.pick(uu, nn))),
        pick.own(D2.pick.cons(T.VStr{a1}, D2.pick(uu, nn))),
        Equal.cong(D2.Pick, D2.Pick, pp => D2.pick.cons(own.elem(T.VStr{a1}), pp),
          D2.pick(D1.own.rows(uu), nn), pick.own(D2.pick(uu, nn)), ih),
        cons.own(T.VStr{a1}, D2.pick(uu, nn)))
    case T.VSpan{+a1, +a2}:
      Equal.trans(D2.Pick,
        D2.pick.cons(own.elem(T.VSpan{a1, a2}), D2.pick(D1.own.rows(uu), nn)),
        D2.pick.cons(own.elem(T.VSpan{a1, a2}), pick.own(D2.pick(uu, nn))),
        pick.own(D2.pick.cons(T.VSpan{a1, a2}, D2.pick(uu, nn))),
        Equal.cong(D2.Pick, D2.Pick, pp => D2.pick.cons(own.elem(T.VSpan{a1, a2}), pp),
          D2.pick(D1.own.rows(uu), nn), pick.own(D2.pick(uu, nn)), ih),
        cons.own(T.VSpan{a1, a2}, D2.pick(uu, nn)))
    case T.VInt{+a1, +a2}:
      Equal.trans(D2.Pick,
        D2.pick.cons(own.elem(T.VInt{a1, a2}), D2.pick(D1.own.rows(uu), nn)),
        D2.pick.cons(own.elem(T.VInt{a1, a2}), pick.own(D2.pick(uu, nn))),
        pick.own(D2.pick.cons(T.VInt{a1, a2}, D2.pick(uu, nn))),
        Equal.cong(D2.Pick, D2.Pick, pp => D2.pick.cons(own.elem(T.VInt{a1, a2}), pp),
          D2.pick(D1.own.rows(uu), nn), pick.own(D2.pick(uu, nn)), ih),
        cons.own(T.VInt{a1, a2}, D2.pick(uu, nn)))
    case T.VFlo{+a1, +a2}:
      Equal.trans(D2.Pick,
        D2.pick.cons(own.elem(T.VFlo{a1, a2}), D2.pick(D1.own.rows(uu), nn)),
        D2.pick.cons(own.elem(T.VFlo{a1, a2}), pick.own(D2.pick(uu, nn))),
        pick.own(D2.pick.cons(T.VFlo{a1, a2}, D2.pick(uu, nn))),
        Equal.cong(D2.Pick, D2.Pick, pp => D2.pick.cons(own.elem(T.VFlo{a1, a2}), pp),
          D2.pick(D1.own.rows(uu), nn), pick.own(D2.pick(uu, nn)), ih),
        cons.own(T.VFlo{a1, a2}, D2.pick(uu, nn)))
    case T.VBool{+a1}:
      Equal.trans(D2.Pick,
        D2.pick.cons(own.elem(T.VBool{a1}), D2.pick(D1.own.rows(uu), nn)),
        D2.pick.cons(own.elem(T.VBool{a1}), pick.own(D2.pick(uu, nn))),
        pick.own(D2.pick.cons(T.VBool{a1}, D2.pick(uu, nn))),
        Equal.cong(D2.Pick, D2.Pick, pp => D2.pick.cons(own.elem(T.VBool{a1}), pp),
          D2.pick(D1.own.rows(uu), nn), pick.own(D2.pick(uu, nn)), ih),
        cons.own(T.VBool{a1}, D2.pick(uu, nn)))
    case T.VWhen{+a1}:
      Equal.trans(D2.Pick,
        D2.pick.cons(own.elem(T.VWhen{a1}), D2.pick(D1.own.rows(uu), nn)),
        D2.pick.cons(own.elem(T.VWhen{a1}), pick.own(D2.pick(uu, nn))),
        pick.own(D2.pick.cons(T.VWhen{a1}, D2.pick(uu, nn))),
        Equal.cong(D2.Pick, D2.Pick, pp => D2.pick.cons(own.elem(T.VWhen{a1}), pp),
          D2.pick(D1.own.rows(uu), nn), pick.own(D2.pick(uu, nn)), ih),
        cons.own(T.VWhen{a1}, D2.pick(uu, nn)))
    case T.VArr{+ls}:
      Equal.trans(D2.Pick,
        D2.pick.cons(own.elem(T.VArr{ls}), D2.pick(D1.own.rows(uu), nn)),
        D2.pick.cons(own.elem(T.VArr{ls}), pick.own(D2.pick(uu, nn))),
        pick.own(D2.pick.cons(T.VArr{ls}, D2.pick(uu, nn))),
        Equal.cong(D2.Pick, D2.Pick, pp => D2.pick.cons(own.elem(T.VArr{ls}), pp),
          D2.pick(D1.own.rows(uu), nn), pick.own(D2.pick(uu, nn)), ih),
        cons.own(T.VArr{ls}, D2.pick(uu, nn)))
    case T.VInl{+ls}:
      Equal.trans(D2.Pick,
        D2.pick.cons(own.elem(T.VInl{ls}), D2.pick(D1.own.rows(uu), nn)),
        D2.pick.cons(own.elem(T.VInl{ls}), pick.own(D2.pick(uu, nn))),
        pick.own(D2.pick.cons(T.VInl{ls}, D2.pick(uu, nn))),
        Equal.cong(D2.Pick, D2.Pick, pp => D2.pick.cons(own.elem(T.VInl{ls}), pp),
          D2.pick(D1.own.rows(uu), nn), pick.own(D2.pick(uu, nn)), ih),
        cons.own(T.VInl{ls}, D2.pick(uu, nn)))
    case T.VHead{+pa, +ls}:
      Equal.trans(D2.Pick,
        D2.pick.cons(own.elem(T.VHead{pa, ls}), D2.pick(D1.own.rows(uu), nn)),
        D2.pick.cons(own.elem(T.VHead{pa, ls}), pick.own(D2.pick(uu, nn))),
        pick.own(D2.pick.cons(T.VHead{pa, ls}, D2.pick(uu, nn))),
        Equal.cong(D2.Pick, D2.Pick, pp => D2.pick.cons(own.elem(T.VHead{pa, ls}), pp),
          D2.pick(D1.own.rows(uu), nn), pick.own(D2.pick(uu, nn)), ih),
        cons.own(T.VHead{pa, ls}, D2.pick(uu, nn)))
    case T.VAot{+pa, +ls}:
      Equal.trans(D2.Pick,
        D2.pick.cons(own.elem(T.VAot{pa, ls}), D2.pick(D1.own.rows(uu), nn)),
        D2.pick.cons(own.elem(T.VAot{pa, ls}), pick.own(D2.pick(uu, nn))),
        pick.own(D2.pick.cons(T.VAot{pa, ls}, D2.pick(uu, nn))),
        Equal.cong(D2.Pick, D2.Pick, pp => D2.pick.cons(own.elem(T.VAot{pa, ls}), pp),
          D2.pick(D1.own.rows(uu), nn), pick.own(D2.pick(uu, nn)), ih),
        cons.own(T.VAot{pa, ls}, D2.pick(uu, nn)))
    case T.VAots{+pa, +ls}:
      Equal.trans(D2.Pick,
        D2.pick.cons(own.elem(T.VAots{pa, ls}), D2.pick(D1.own.rows(uu), nn)),
        D2.pick.cons(own.elem(T.VAots{pa, ls}), pick.own(D2.pick(uu, nn))),
        pick.own(D2.pick.cons(T.VAots{pa, ls}, D2.pick(uu, nn))),
        Equal.cong(D2.Pick, D2.Pick, pp => D2.pick.cons(own.elem(T.VAots{pa, ls}), pp),
          D2.pick(D1.own.rows(uu), nn), pick.own(D2.pick(uu, nn)), ih),
        cons.own(T.VAots{pa, ls}, D2.pick(uu, nn)))

# a pick from rows read out is the pick read out
def pick.own.rows(
  oo: List<&2, T.Val>,
  +nn: String
) -> {D2.pick(D1.own.rows(oo), nn) == pick.own(D2.pick(oo, nn)) : D2.Pick}:
  match oo:
    case []:
      {==}
    case +kk <> +uu:
      Equal.trans(D2.Pick, D2.pick(D1.own.rows(kk <> uu), nn),
        D2.pick(own.elem(kk) <> D1.own.rows(uu), nn), pick.own(D2.pick(kk <> uu, nn)),
        Equal.cong(List<&2, T.Val>, D2.Pick, ls => D2.pick(ls, nn), D1.own.rows(kk <> uu),
          own.elem(kk) <> D1.own.rows(uu), own.cons(kk, uu)),
        po.cell(kk, uu, nn, pick.own.rows(uu, nn)))

# rows read out are empty exactly when the rows are
def empty.own(
  oo: List<&2, T.Val>
) -> {List.is_empty(&2, T.Val, D1.own.rows(oo)) == List.is_empty(&2, T.Val, oo) : Bool}:
  match oo:
    case []:
      {==}
    case +kk <> +uu:
      Equal.cong(List<&2, T.Val>, Bool, ls => List.is_empty(&2, T.Val, ls), D1.own.rows(kk <> uu),
        own.elem(kk) <> D1.own.rows(uu), own.cons(kk, uu))

# a box read out, compared by a comparison that does not see reading out
def boxed.own(
  kk: D2.Kin,
  bx: D2.Box,
  -ff: List<&2, T.Val> -> Bool,
  hf: @ls: List<&2, T.Val> -> {ff(D1.own.rows(ls)) == ff(ls) : Bool}
) -> {D2.same.boxed(kk, box.own(bx), ff) == D2.same.boxed(kk, bx, ff) : Bool}:
  match bx:
    case D2.Boxed{+k2, +ls}:
      at.cong2(D2.kin.eq(kk, k2), _u => ff(D1.own.rows(ls)), _u => ff(ls), hf(ls))
    case D2.Unboxed{}:
      {==}

# a value read out, compared as a box
def box.own.v(
  kk: D2.Kin,
  +ww: T.Val,
  -ff: List<&2, T.Val> -> Bool,
  hf: @ls: List<&2, T.Val> -> {ff(D1.own.rows(ls)) == ff(ls) : Bool}
) -> {D2.same.box(kk, own.val(ww), ff) == D2.same.box(kk, ww, ff) : Bool}:
  Equal.trans(Bool, D2.same.boxed(kk, D2.kids(own.val(ww)), ff), D2.same.boxed(kk, box.own(D2.kids(ww)), ff),
    D2.same.boxed(kk, D2.kids(ww), ff),
    Equal.cong(D2.Box, Bool, bx => D2.same.boxed(kk, bx, ff), D2.kids(own.val(ww)), box.own(D2.kids(ww)),
      kids.own(ww)),
    boxed.own(kk, D2.kids(ww), ff, hf))

# a row read out, compared as a box
def box.own.e(
  kk: D2.Kin,
  +ww: T.Val,
  -ff: List<&2, T.Val> -> Bool,
  hf: @ls: List<&2, T.Val> -> {ff(D1.own.rows(ls)) == ff(ls) : Bool}
) -> {D2.same.box(kk, own.elem(ww), ff) == D2.same.box(kk, ww, ff) : Bool}:
  Equal.trans(Bool, D2.same.boxed(kk, D2.kids(own.elem(ww)), ff), D2.same.boxed(kk, box.own(D2.kids(ww)), ff),
    D2.same.boxed(kk, D2.kids(ww), ff),
    Equal.cong(D2.Box, Bool, bx => D2.same.boxed(kk, bx, ff), D2.kids(own.elem(ww)), box.own(D2.kids(ww)),
      kids.own.e(ww)),
    boxed.own(kk, D2.kids(ww), ff, hf))

# a value read out is the same scalar
def atom.own.v(
  +vv: T.Val,
  +ww: T.Val
) -> {D2.same.atom(vv, own.val(ww)) == D2.same.atom(vv, ww) : Bool}:
  Equal.cong(D2.Sc, Bool, sc => D2.sc.eq(D2.scal(vv), sc), D2.scal(own.val(ww)), D2.scal(ww), scal.own(ww))

# a row read out is the same scalar
def atom.own.e(
  +vv: T.Val,
  +ww: T.Val
) -> {D2.same.atom(vv, own.elem(ww)) == D2.same.atom(vv, ww) : Bool}:
  Equal.cong(D2.Sc, Bool, sc => D2.sc.eq(D2.scal(vv), sc), D2.scal(own.elem(ww)), D2.scal(ww), scal.own.e(ww))

# a pick read out compares as the pick
def pair.own(
  pp: D2.Pick,
  cmp: T.Val -> Bool,
  -rest: List<&2, T.Val> -> Bool,
  hc: @vv: T.Val -> {cmp(own.val(vv)) == cmp(vv) : Bool},
  hr: @ls: List<&2, T.Val> -> {rest(D1.own.rows(ls)) == rest(ls) : Bool}
) -> {D2.same.pair(pick.own(pp), cmp, rest) == D2.same.pair(pp, cmp, rest) : Bool}:
  match pp:
    case D2.Picked{+ww, +left}:
      at.cong(cmp(own.val(ww)), cmp(ww), hc(ww), _u => rest(D1.own.rows(left)), _u => rest(left), hr(left))
    case D2.NoPick{}:
      {==}

# other rows read out give their first value read out
def item.own(
  oo: List<&2, T.Val>,
  cmp: T.Val -> Bool,
  -rest: List<&2, T.Val> -> Bool,
  hc: @vv: T.Val -> {cmp(own.elem(vv)) == cmp(vv) : Bool},
  hr: @ls: List<&2, T.Val> -> {rest(D1.own.rows(ls)) == rest(ls) : Bool}
) -> {D2.same.item(D1.own.rows(oo), cmp, rest) == D2.same.item(oo, cmp, rest) : Bool}:
  match oo:
    case []:
      {==}
    case +kk <> +uu:
      Equal.trans(Bool, D2.same.item(D1.own.rows(kk <> uu), cmp, rest),
        D2.same.item(own.elem(kk) <> D1.own.rows(uu), cmp, rest), D2.same.item(kk <> uu, cmp, rest),
        Equal.cong(List<&2, T.Val>, Bool, ls => D2.same.item(ls, cmp, rest), D1.own.rows(kk <> uu),
          own.elem(kk) <> D1.own.rows(uu), own.cons(kk, uu)),
        at.cong(cmp(own.elem(kk)), cmp(kk), hc(kk), _u => rest(D1.own.rows(uu)), _u => rest(uu), hr(uu)))

# rows compare against other rows read out as against the rows
def own.r(
  xs: List<&2, T.Val>,
  +oo: List<&2, T.Val>
) -> {D2.same.go(xs, D1.own.rows(oo)) == D2.same.go(xs, oo) : Bool}:
  match xs:
    case []:
      empty.own(oo)
    case T.VPair{+nn, T.VStr{+a1}} <> +tt:
      Equal.trans(Bool, D2.same.pair(D2.pick(D1.own.rows(oo), nn), ww => D2.same.atom(T.VStr{a1}, ww),
        rr => D2.same.go(tt, rr)),
        D2.same.pair(pick.own(D2.pick(oo, nn)), ww => D2.same.atom(T.VStr{a1}, ww), rr => D2.same.go(tt, rr)),
        D2.same.pair(D2.pick(oo, nn), ww => D2.same.atom(T.VStr{a1}, ww), rr => D2.same.go(tt, rr)),
        Equal.cong(D2.Pick, Bool, pp => D2.same.pair(pp, ww => D2.same.atom(T.VStr{a1}, ww),
          rr => D2.same.go(tt, rr)),
          D2.pick(D1.own.rows(oo), nn), pick.own(D2.pick(oo, nn)), pick.own.rows(oo, nn)),
        pair.own(D2.pick(oo, nn), ww => D2.same.atom(T.VStr{a1}, ww), rr => D2.same.go(tt, rr),
          ww => atom.own.v(T.VStr{a1}, ww), rr => own.r(tt, rr)))
    case T.VPair{+nn, T.VSpan{+a1, +a2}} <> +tt:
      Equal.trans(Bool, D2.same.pair(D2.pick(D1.own.rows(oo), nn), ww => D2.same.atom(T.VSpan{a1, a2}, ww),
        rr => D2.same.go(tt, rr)),
        D2.same.pair(pick.own(D2.pick(oo, nn)), ww => D2.same.atom(T.VSpan{a1, a2}, ww), rr => D2.same.go(tt,
          rr)),
        D2.same.pair(D2.pick(oo, nn), ww => D2.same.atom(T.VSpan{a1, a2}, ww), rr => D2.same.go(tt, rr)),
        Equal.cong(D2.Pick, Bool, pp => D2.same.pair(pp, ww => D2.same.atom(T.VSpan{a1, a2}, ww),
          rr => D2.same.go(tt, rr)),
          D2.pick(D1.own.rows(oo), nn), pick.own(D2.pick(oo, nn)), pick.own.rows(oo, nn)),
        pair.own(D2.pick(oo, nn), ww => D2.same.atom(T.VSpan{a1, a2}, ww), rr => D2.same.go(tt, rr),
          ww => atom.own.v(T.VSpan{a1, a2}, ww), rr => own.r(tt, rr)))
    case T.VPair{+nn, T.VInt{+a1, +a2}} <> +tt:
      Equal.trans(Bool, D2.same.pair(D2.pick(D1.own.rows(oo), nn), ww => D2.same.atom(T.VInt{a1, a2}, ww),
        rr => D2.same.go(tt, rr)),
        D2.same.pair(pick.own(D2.pick(oo, nn)), ww => D2.same.atom(T.VInt{a1, a2}, ww), rr => D2.same.go(tt,
          rr)),
        D2.same.pair(D2.pick(oo, nn), ww => D2.same.atom(T.VInt{a1, a2}, ww), rr => D2.same.go(tt, rr)),
        Equal.cong(D2.Pick, Bool, pp => D2.same.pair(pp, ww => D2.same.atom(T.VInt{a1, a2}, ww),
          rr => D2.same.go(tt, rr)),
          D2.pick(D1.own.rows(oo), nn), pick.own(D2.pick(oo, nn)), pick.own.rows(oo, nn)),
        pair.own(D2.pick(oo, nn), ww => D2.same.atom(T.VInt{a1, a2}, ww), rr => D2.same.go(tt, rr),
          ww => atom.own.v(T.VInt{a1, a2}, ww), rr => own.r(tt, rr)))
    case T.VPair{+nn, T.VFlo{+a1, +a2}} <> +tt:
      Equal.trans(Bool, D2.same.pair(D2.pick(D1.own.rows(oo), nn), ww => D2.same.atom(T.VFlo{a1, a2}, ww),
        rr => D2.same.go(tt, rr)),
        D2.same.pair(pick.own(D2.pick(oo, nn)), ww => D2.same.atom(T.VFlo{a1, a2}, ww), rr => D2.same.go(tt,
          rr)),
        D2.same.pair(D2.pick(oo, nn), ww => D2.same.atom(T.VFlo{a1, a2}, ww), rr => D2.same.go(tt, rr)),
        Equal.cong(D2.Pick, Bool, pp => D2.same.pair(pp, ww => D2.same.atom(T.VFlo{a1, a2}, ww),
          rr => D2.same.go(tt, rr)),
          D2.pick(D1.own.rows(oo), nn), pick.own(D2.pick(oo, nn)), pick.own.rows(oo, nn)),
        pair.own(D2.pick(oo, nn), ww => D2.same.atom(T.VFlo{a1, a2}, ww), rr => D2.same.go(tt, rr),
          ww => atom.own.v(T.VFlo{a1, a2}, ww), rr => own.r(tt, rr)))
    case T.VPair{+nn, T.VBool{+a1}} <> +tt:
      Equal.trans(Bool, D2.same.pair(D2.pick(D1.own.rows(oo), nn), ww => D2.same.atom(T.VBool{a1}, ww),
        rr => D2.same.go(tt, rr)),
        D2.same.pair(pick.own(D2.pick(oo, nn)), ww => D2.same.atom(T.VBool{a1}, ww), rr => D2.same.go(tt, rr)),
        D2.same.pair(D2.pick(oo, nn), ww => D2.same.atom(T.VBool{a1}, ww), rr => D2.same.go(tt, rr)),
        Equal.cong(D2.Pick, Bool, pp => D2.same.pair(pp, ww => D2.same.atom(T.VBool{a1}, ww),
          rr => D2.same.go(tt, rr)),
          D2.pick(D1.own.rows(oo), nn), pick.own(D2.pick(oo, nn)), pick.own.rows(oo, nn)),
        pair.own(D2.pick(oo, nn), ww => D2.same.atom(T.VBool{a1}, ww), rr => D2.same.go(tt, rr),
          ww => atom.own.v(T.VBool{a1}, ww), rr => own.r(tt, rr)))
    case T.VPair{+nn, T.VWhen{+a1}} <> +tt:
      Equal.trans(Bool, D2.same.pair(D2.pick(D1.own.rows(oo), nn), ww => D2.same.atom(T.VWhen{a1}, ww),
        rr => D2.same.go(tt, rr)),
        D2.same.pair(pick.own(D2.pick(oo, nn)), ww => D2.same.atom(T.VWhen{a1}, ww), rr => D2.same.go(tt, rr)),
        D2.same.pair(D2.pick(oo, nn), ww => D2.same.atom(T.VWhen{a1}, ww), rr => D2.same.go(tt, rr)),
        Equal.cong(D2.Pick, Bool, pp => D2.same.pair(pp, ww => D2.same.atom(T.VWhen{a1}, ww),
          rr => D2.same.go(tt, rr)),
          D2.pick(D1.own.rows(oo), nn), pick.own(D2.pick(oo, nn)), pick.own.rows(oo, nn)),
        pair.own(D2.pick(oo, nn), ww => D2.same.atom(T.VWhen{a1}, ww), rr => D2.same.go(tt, rr),
          ww => atom.own.v(T.VWhen{a1}, ww), rr => own.r(tt, rr)))
    case T.VPair{+nn, T.VArr{+ls}} <> +tt:
      Equal.trans(Bool, D2.same.pair(D2.pick(D1.own.rows(oo), nn), ww => D2.same.box(D2.KArr{}, ww,
        ws => D2.same.go(ls, ws)), rr => D2.same.go(tt, rr)),
        D2.same.pair(pick.own(D2.pick(oo, nn)), ww => D2.same.box(D2.KArr{}, ww, ws => D2.same.go(ls, ws)),
          rr => D2.same.go(tt, rr)),
        D2.same.pair(D2.pick(oo, nn), ww => D2.same.box(D2.KArr{}, ww, ws => D2.same.go(ls, ws)),
          rr => D2.same.go(tt, rr)),
        Equal.cong(D2.Pick, Bool, pp => D2.same.pair(pp, ww => D2.same.box(D2.KArr{}, ww,
          ws => D2.same.go(ls, ws)), rr => D2.same.go(tt, rr)),
          D2.pick(D1.own.rows(oo), nn), pick.own(D2.pick(oo, nn)), pick.own.rows(oo, nn)),
        pair.own(D2.pick(oo, nn), ww => D2.same.box(D2.KArr{}, ww, ws => D2.same.go(ls, ws)),
          rr => D2.same.go(tt, rr), ww => box.own.v(D2.KArr{}, ww, ws => D2.same.go(ls, ws), ws => own.r(ls,
          ws)), rr => own.r(tt, rr)))
    case T.VPair{+nn, T.VInl{+ls}} <> +tt:
      Equal.trans(Bool, D2.same.pair(D2.pick(D1.own.rows(oo), nn), ww => D2.same.box(D2.KInl{}, ww,
        ws => D2.same.go(ls, ws)), rr => D2.same.go(tt, rr)),
        D2.same.pair(pick.own(D2.pick(oo, nn)), ww => D2.same.box(D2.KInl{}, ww, ws => D2.same.go(ls, ws)),
          rr => D2.same.go(tt, rr)),
        D2.same.pair(D2.pick(oo, nn), ww => D2.same.box(D2.KInl{}, ww, ws => D2.same.go(ls, ws)),
          rr => D2.same.go(tt, rr)),
        Equal.cong(D2.Pick, Bool, pp => D2.same.pair(pp, ww => D2.same.box(D2.KInl{}, ww,
          ws => D2.same.go(ls, ws)), rr => D2.same.go(tt, rr)),
          D2.pick(D1.own.rows(oo), nn), pick.own(D2.pick(oo, nn)), pick.own.rows(oo, nn)),
        pair.own(D2.pick(oo, nn), ww => D2.same.box(D2.KInl{}, ww, ws => D2.same.go(ls, ws)),
          rr => D2.same.go(tt, rr), ww => box.own.v(D2.KInl{}, ww, ws => D2.same.go(ls, ws), ws => own.r(ls,
          ws)), rr => own.r(tt, rr)))
    case T.VPair{+nn, T.VHead{+pa, +ls}} <> +tt:
      Equal.trans(Bool, D2.same.pair(D2.pick(D1.own.rows(oo), nn), ww => D2.same.box(D2.KHead{}, ww,
        ws => D2.same.go(ls, ws)), rr => D2.same.go(tt, rr)),
        D2.same.pair(pick.own(D2.pick(oo, nn)), ww => D2.same.box(D2.KHead{}, ww, ws => D2.same.go(ls, ws)),
          rr => D2.same.go(tt, rr)),
        D2.same.pair(D2.pick(oo, nn), ww => D2.same.box(D2.KHead{}, ww, ws => D2.same.go(ls, ws)),
          rr => D2.same.go(tt, rr)),
        Equal.cong(D2.Pick, Bool, pp => D2.same.pair(pp, ww => D2.same.box(D2.KHead{}, ww,
          ws => D2.same.go(ls, ws)), rr => D2.same.go(tt, rr)),
          D2.pick(D1.own.rows(oo), nn), pick.own(D2.pick(oo, nn)), pick.own.rows(oo, nn)),
        pair.own(D2.pick(oo, nn), ww => D2.same.box(D2.KHead{}, ww, ws => D2.same.go(ls, ws)),
          rr => D2.same.go(tt, rr), ww => box.own.v(D2.KHead{}, ww, ws => D2.same.go(ls, ws), ws => own.r(ls,
          ws)), rr => own.r(tt, rr)))
    case T.VPair{+nn, T.VAot{+pa, +ls}} <> +tt:
      Equal.trans(Bool, D2.same.pair(D2.pick(D1.own.rows(oo), nn), ww => D2.same.box(D2.KAot{}, ww,
        ws => D2.same.go(ls, ws)), rr => D2.same.go(tt, rr)),
        D2.same.pair(pick.own(D2.pick(oo, nn)), ww => D2.same.box(D2.KAot{}, ww, ws => D2.same.go(ls, ws)),
          rr => D2.same.go(tt, rr)),
        D2.same.pair(D2.pick(oo, nn), ww => D2.same.box(D2.KAot{}, ww, ws => D2.same.go(ls, ws)),
          rr => D2.same.go(tt, rr)),
        Equal.cong(D2.Pick, Bool, pp => D2.same.pair(pp, ww => D2.same.box(D2.KAot{}, ww,
          ws => D2.same.go(ls, ws)), rr => D2.same.go(tt, rr)),
          D2.pick(D1.own.rows(oo), nn), pick.own(D2.pick(oo, nn)), pick.own.rows(oo, nn)),
        pair.own(D2.pick(oo, nn), ww => D2.same.box(D2.KAot{}, ww, ws => D2.same.go(ls, ws)),
          rr => D2.same.go(tt, rr), ww => box.own.v(D2.KAot{}, ww, ws => D2.same.go(ls, ws), ws => own.r(ls,
          ws)), rr => own.r(tt, rr)))
    case T.VPair{+nn, T.VAots{+pa, +ls}} <> +tt:
      Equal.trans(Bool, D2.same.pair(D2.pick(D1.own.rows(oo), nn), ww => D2.same.box(D2.KAots{}, ww,
        ws => D2.same.go(ls, ws)), rr => D2.same.go(tt, rr)),
        D2.same.pair(pick.own(D2.pick(oo, nn)), ww => D2.same.box(D2.KAots{}, ww, ws => D2.same.go(ls, ws)),
          rr => D2.same.go(tt, rr)),
        D2.same.pair(D2.pick(oo, nn), ww => D2.same.box(D2.KAots{}, ww, ws => D2.same.go(ls, ws)),
          rr => D2.same.go(tt, rr)),
        Equal.cong(D2.Pick, Bool, pp => D2.same.pair(pp, ww => D2.same.box(D2.KAots{}, ww,
          ws => D2.same.go(ls, ws)), rr => D2.same.go(tt, rr)),
          D2.pick(D1.own.rows(oo), nn), pick.own(D2.pick(oo, nn)), pick.own.rows(oo, nn)),
        pair.own(D2.pick(oo, nn), ww => D2.same.box(D2.KAots{}, ww, ws => D2.same.go(ls, ws)),
          rr => D2.same.go(tt, rr), ww => box.own.v(D2.KAots{}, ww, ws => D2.same.go(ls, ws), ws => own.r(ls,
          ws)), rr => own.r(tt, rr)))
    case T.VPair{+nn, T.VPair{+a1, +a2}} <> +tt:
      Equal.trans(Bool, D2.same.pair(D2.pick(D1.own.rows(oo), nn), ww => D2.same.atom(T.VPair{a1, a2}, ww),
        rr => D2.same.go(tt, rr)),
        D2.same.pair(pick.own(D2.pick(oo, nn)), ww => D2.same.atom(T.VPair{a1, a2}, ww), rr => D2.same.go(tt,
          rr)),
        D2.same.pair(D2.pick(oo, nn), ww => D2.same.atom(T.VPair{a1, a2}, ww), rr => D2.same.go(tt, rr)),
        Equal.cong(D2.Pick, Bool, pp => D2.same.pair(pp, ww => D2.same.atom(T.VPair{a1, a2}, ww),
          rr => D2.same.go(tt, rr)),
          D2.pick(D1.own.rows(oo), nn), pick.own(D2.pick(oo, nn)), pick.own.rows(oo, nn)),
        pair.own(D2.pick(oo, nn), ww => D2.same.atom(T.VPair{a1, a2}, ww), rr => D2.same.go(tt, rr),
          ww => atom.own.v(T.VPair{a1, a2}, ww), rr => own.r(tt, rr)))
    case T.VStr{+a1} <> +tt:
      item.own(oo, ww => D2.same.atom(T.VStr{a1}, ww), rr => D2.same.go(tt, rr), ww => atom.own.e(T.VStr{a1}, ww),
        rr => own.r(tt, rr))
    case T.VSpan{+a1, +a2} <> +tt:
      item.own(oo, ww => D2.same.atom(T.VSpan{a1, a2}, ww), rr => D2.same.go(tt, rr), ww => atom.own.e(T.VSpan{a1,
        a2}, ww), rr => own.r(tt, rr))
    case T.VInt{+a1, +a2} <> +tt:
      item.own(oo, ww => D2.same.atom(T.VInt{a1, a2}, ww), rr => D2.same.go(tt, rr), ww => atom.own.e(T.VInt{a1,
        a2}, ww), rr => own.r(tt, rr))
    case T.VFlo{+a1, +a2} <> +tt:
      item.own(oo, ww => D2.same.atom(T.VFlo{a1, a2}, ww), rr => D2.same.go(tt, rr), ww => atom.own.e(T.VFlo{a1,
        a2}, ww), rr => own.r(tt, rr))
    case T.VBool{+a1} <> +tt:
      item.own(oo, ww => D2.same.atom(T.VBool{a1}, ww), rr => D2.same.go(tt, rr), ww => atom.own.e(T.VBool{a1},
        ww), rr => own.r(tt, rr))
    case T.VWhen{+a1} <> +tt:
      item.own(oo, ww => D2.same.atom(T.VWhen{a1}, ww), rr => D2.same.go(tt, rr), ww => atom.own.e(T.VWhen{a1},
        ww), rr => own.r(tt, rr))
    case T.VArr{+ls} <> +tt:
      item.own(oo, ww => D2.same.box(D2.KArr{}, ww, ws => D2.same.go(ls, ws)), rr => D2.same.go(tt, rr),
        ww => box.own.e(D2.KArr{}, ww, ws => D2.same.go(ls, ws), ws => own.r(ls, ws)), rr => own.r(tt, rr))
    case T.VInl{+ls} <> +tt:
      item.own(oo, ww => D2.same.box(D2.KInl{}, ww, ws => D2.same.go(ls, ws)), rr => D2.same.go(tt, rr),
        ww => box.own.e(D2.KInl{}, ww, ws => D2.same.go(ls, ws), ws => own.r(ls, ws)), rr => own.r(tt, rr))
    case T.VHead{+pa, +ls} <> +tt:
      item.own(oo, ww => D2.same.box(D2.KHead{}, ww, ws => D2.same.go(ls, ws)), rr => D2.same.go(tt, rr),
        ww => box.own.e(D2.KHead{}, ww, ws => D2.same.go(ls, ws), ws => own.r(ls, ws)), rr => own.r(tt, rr))
    case T.VAot{+pa, +ls} <> +tt:
      item.own(oo, ww => D2.same.box(D2.KAot{}, ww, ws => D2.same.go(ls, ws)), rr => D2.same.go(tt, rr),
        ww => box.own.e(D2.KAot{}, ww, ws => D2.same.go(ls, ws), ws => own.r(ls, ws)), rr => own.r(tt, rr))
    case T.VAots{+pa, +ls} <> +tt:
      item.own(oo, ww => D2.same.box(D2.KAots{}, ww, ws => D2.same.go(ls, ws)), rr => D2.same.go(tt, rr),
        ww => box.own.e(D2.KAots{}, ww, ws => D2.same.go(ls, ws), ws => own.r(ls, ws)), rr => own.r(tt, rr))
