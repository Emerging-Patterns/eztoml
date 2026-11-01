# a well-formed value, scalar, date, clock or zone equals itself
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/defs/DocumentSameness.bend as D1
import ./PickAndDigitSteps.bend as M1
import ./PrefixAndTake.bend as M2
import ./ShortTextBounds.bend as M3

# rows whose every value matches itself match themselves
def refl.rows(
  xs: List<&2, T.Val>,
  +ee: {M1.selfs(xs) == True{} : Bool}
) -> {D1.same.go(xs, xs) == True{} : Bool}:
  match xs:
    case []:
      {==}
    case +hh <> +tt:
      Equal.trans(Bool, D1.same.go(hh <> tt, hh <> tt),
        Bool.and(D1.same.go(hh <> [], hh <> []), D1.same.go(tt, tt)), True{},
        M1.hc(hh, tt, tt),
        M2.and.tt(D1.same.go(hh <> [], hh <> []), D1.same.go(tt, tt),
          Eq.and.left(D1.same.go(hh <> [], hh <> []), M1.selfs(tt), ee),
          refl.rows(tt, Eq.and.right(D1.same.go(hh <> [], hh <> []), M1.selfs(tt), ee))))

# a part that holds, then a rest that holds
def at.tt(
  -bb: Bool,
  -more: Unit -> Bool,
  eb: {bb == True{} : Bool},
  em: {more(Unit{}) == True{} : Bool}
) -> {D1.and_then(bb, more) == True{} : Bool}:
  Equal.trans(Bool, D1.and_then(bb, more), D1.and_then(True{}, more), True{},
    Equal.cong(Bool, Bool, xx => D1.and_then(xx, more), bb, True{}, eb), em)

# a pair alone matches itself when its value does
def pair.self.tt(
  +nn: String,
  +vv: T.Val,
  -cmp: T.Val -> Bool,
  ec: {cmp(vv) == True{} : Bool}
) -> {D1.same.pair(D1.pick(T.VPair{nn, vv} <> [], nn), cmp, rr => D1.same.go([], rr)) == True{} : Bool}:
  Equal.trans(Bool, D1.same.pair(D1.pick(T.VPair{nn, vv} <> [], nn), cmp, rr => D1.same.go([], rr)),
    D1.same.pair(D1.Picked{vv, []}, cmp, rr => D1.same.go([], rr)), True{},
    Equal.cong(D1.Pick, Bool, pp => D1.same.pair(pp, cmp, rr => D1.same.go([], rr)),
      D1.pick(T.VPair{nn, vv} <> [], nn), D1.Picked{vv, []}, M1.pick.self(nn, vv, [])),
    at.tt(cmp(vv), _u => True{}, ec, {==}))

# a value alone matches itself when it does
def item.self.tt(
  +hh: T.Val,
  -cmp: T.Val -> Bool,
  ec: {cmp(hh) == True{} : Bool}
) -> {D1.same.item(hh <> [], cmp, rr => D1.same.go([], rr)) == True{} : Bool}:
  at.tt(cmp(hh), _u => True{}, ec, {==})

# a well-formed table as a pair's value: the rest holds
def wf.head.more(
  at: T.WfAt,
  +name: String,
  +path: String,
  +rest: List<&2, T.Val>,
  -more: Unit -> Bool,
  ee: {T.wf.head(at, name, path, rest, more) == True{} : Bool}
) -> {more(Unit{}) == True{} : Bool}:
  match at:
    case T.WfRows{+here}:
      M3.wt.more(Bool.and(T.wf.key(name, rest), T.str.eq(path, T.tree.pre(here, name))), more, ee)
    case T.WfInl{}:
      Eq.bit.absurd(&2, {more(Unit{}) == True{} : Bool}, ee)
    case T.WfItems{}:
      Eq.bit.absurd(&2, {more(Unit{}) == True{} : Bool}, ee)
    case T.WfElems{_h}:
      Eq.bit.absurd(&2, {more(Unit{}) == True{} : Bool}, ee)

# a well-formed array of tables as a pair's value: the rest holds
def wf.aots.more(
  at: T.WfAt,
  +name: String,
  +path: String,
  some: Bool,
  +rest: List<&2, T.Val>,
  -more: Unit -> Bool,
  ee: {T.wf.aots(at, name, path, some, rest, more) == True{} : Bool}
) -> {more(Unit{}) == True{} : Bool}:
  match at:
    case T.WfRows{+here}:
      M3.wt.more(Bool.and(some, Bool.and(T.wf.key(name, rest), T.str.eq(path, T.tree.pre(here, name)))), more, ee)
    case T.WfInl{}:
      Eq.bit.absurd(&2, {more(Unit{}) == True{} : Bool}, ee)
    case T.WfItems{}:
      Eq.bit.absurd(&2, {more(Unit{}) == True{} : Bool}, ee)
    case T.WfElems{_h}:
      Eq.bit.absurd(&2, {more(Unit{}) == True{} : Bool}, ee)

# a well-formed element of an array of tables: the rest holds
def wf.aot.more(
  at: T.WfAt,
  +path: String,
  -more: Unit -> Bool,
  ee: {T.wf.aot(at, path, more) == True{} : Bool}
) -> {more(Unit{}) == True{} : Bool}:
  match at:
    case T.WfElems{+here}:
      M3.wt.more(T.str.eq(path, here), more, ee)
    case T.WfRows{_h}:
      Eq.bit.absurd(&2, {more(Unit{}) == True{} : Bool}, ee)
    case T.WfInl{}:
      Eq.bit.absurd(&2, {more(Unit{}) == True{} : Bool}, ee)
    case T.WfItems{}:
      Eq.bit.absurd(&2, {more(Unit{}) == True{} : Bool}, ee)

# a well-formed pair of any other value: the rest holds
def wf.pair.more(
  at: T.WfAt,
  +name: String,
  +rest: List<&2, T.Val>,
  ok: Bool,
  -more: Unit -> Bool,
  ee: {T.wf.pair(at, name, rest, ok, more) == True{} : Bool}
) -> {more(Unit{}) == True{} : Bool}:
  match at:
    case T.WfRows{_h}:
      M3.wt.more(Bool.and(ok, T.wf.key(name, rest)), more, ee)
    case T.WfInl{}:
      M3.wt.more(Bool.and(ok, T.wf.key(name, rest)), more, ee)
    case T.WfItems{}:
      Eq.bit.absurd(&2, {more(Unit{}) == True{} : Bool}, ee)
    case T.WfElems{_h}:
      Eq.bit.absurd(&2, {more(Unit{}) == True{} : Bool}, ee)

# a well-formed pair of any other value: its value is well-formed
def wf.pair.ok(
  at: T.WfAt,
  +name: String,
  +rest: List<&2, T.Val>,
  +ok: Bool,
  -more: Unit -> Bool,
  ee: {T.wf.pair(at, name, rest, ok, more) == True{} : Bool}
) -> {ok == True{} : Bool}:
  match at:
    case T.WfRows{_h}:
      Eq.and.left(ok, T.wf.key(name, rest), M3.wt.ok(Bool.and(ok, T.wf.key(name, rest)), more, ee))
    case T.WfInl{}:
      Eq.and.left(ok, T.wf.key(name, rest), M3.wt.ok(Bool.and(ok, T.wf.key(name, rest)), more, ee))
    case T.WfItems{}:
      Eq.bit.absurd(&2, {ok == True{} : Bool}, ee)
    case T.WfElems{_h}:
      Eq.bit.absurd(&2, {ok == True{} : Bool}, ee)

# a well-formed item: the rest holds
def wf.item.more(
  at: T.WfAt,
  ok: Bool,
  -more: Unit -> Bool,
  ee: {T.wf.item(at, ok, more) == True{} : Bool}
) -> {more(Unit{}) == True{} : Bool}:
  match at:
    case T.WfItems{}:
      M3.wt.more(ok, more, ee)
    case T.WfRows{_h}:
      Eq.bit.absurd(&2, {more(Unit{}) == True{} : Bool}, ee)
    case T.WfInl{}:
      Eq.bit.absurd(&2, {more(Unit{}) == True{} : Bool}, ee)
    case T.WfElems{_h}:
      Eq.bit.absurd(&2, {more(Unit{}) == True{} : Bool}, ee)

# a well-formed item: it is well-formed itself
def wf.item.ok(
  at: T.WfAt,
  ok: Bool,
  -more: Unit -> Bool,
  ee: {T.wf.item(at, ok, more) == True{} : Bool}
) -> {ok == True{} : Bool}:
  match at:
    case T.WfItems{}:
      M3.wt.ok(ok, more, ee)
    case T.WfRows{_h}:
      Eq.bit.absurd(&2, {ok == True{} : Bool}, ee)
    case T.WfInl{}:
      Eq.bit.absurd(&2, {ok == True{} : Bool}, ee)
    case T.WfElems{_h}:
      Eq.bit.absurd(&2, {ok == True{} : Bool}, ee)

# a number equals itself
def u32.self(+xx: U32) -> {U32.is_eq(xx, xx) == True{} : Bool}:
  Equal.cong(Cmp, Bool, cc => Cmp.is_eq(cc), U32.cmp(xx, xx), EQ{}, Eq.u32_cmp_self(xx))

# a sign equals itself
def sign.self(sg: T.Sign) -> {D1.sign.eq(sg, sg) == True{} : Bool}:
  match sg:
    case T.Plus{}:
      {==}
    case T.Minus{}:
      {==}

# a bit equals itself
def bit.self(bb: Bool) -> {D1.bit.eq(bb, bb) == True{} : Bool}:
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# a date equals itself
def date.self(dd: T.Date) -> {D1.date.eq(dd, dd) == True{} : Bool}:
  match dd:
    case T.Date{+yy, +mo, +dy}:
      M2.and.tt(U32.is_eq(yy, yy), Bool.and(U32.is_eq(mo, mo), U32.is_eq(dy, dy)), u32.self(yy),
        M2.and.tt(U32.is_eq(mo, mo), U32.is_eq(dy, dy), u32.self(mo), u32.self(dy)))

# a clock equals itself
def clock.self(cc: T.Clock) -> {D1.clock.eq(cc, cc) == True{} : Bool}:
  match cc:
    case T.Clock{+hh, +mi, +ss, +fr}:
      M2.and.tt(U32.is_eq(hh, hh), Bool.and(U32.is_eq(mi, mi), Bool.and(U32.is_eq(ss, ss), String.eq(fr, fr))),
        u32.self(hh),
        M2.and.tt(U32.is_eq(mi, mi), Bool.and(U32.is_eq(ss, ss), String.eq(fr, fr)), u32.self(mi),
          M2.and.tt(U32.is_eq(ss, ss), String.eq(fr, fr), u32.self(ss), Eq.string_eq_self(fr))))

# a zone equals itself
def zone.self(zz: T.Zone) -> {D1.zone.eq(zz, zz) == True{} : Bool}:
  match zz:
    case T.Zulu{}:
      {==}
    case T.Shift{+sg, +hh, +mi}:
      M2.and.tt(D1.sign.eq(sg, sg), Bool.and(U32.is_eq(hh, hh), U32.is_eq(mi, mi)), sign.self(sg),
        M2.and.tt(U32.is_eq(hh, hh), U32.is_eq(mi, mi), u32.self(hh), u32.self(mi)))

# a datetime equals itself
def when.self(ww: T.When) -> {D1.when.eq(ww, ww) == True{} : Bool}:
  match ww:
    case T.WOff{+dd, +cc, +zz}:
      M2.and.tt(D1.date.eq(dd, dd), Bool.and(D1.clock.eq(cc, cc), D1.zone.eq(zz, zz)), date.self(dd),
        M2.and.tt(D1.clock.eq(cc, cc), D1.zone.eq(zz, zz), clock.self(cc), zone.self(zz)))
    case T.WLocal{+dd, +cc}:
      M2.and.tt(D1.date.eq(dd, dd), D1.clock.eq(cc, cc), date.self(dd), clock.self(cc))
    case T.WDate{+dd}:
      date.self(dd)
    case T.WTime{+cc}:
      clock.self(cc)

# a well-formed scalar is the same scalar as itself
def atom.self(
  vv: T.Val,
  ee: {T.wf.atom(vv) == True{} : Bool}
) -> {D1.same.atom(vv, vv) == True{} : Bool}:
  match vv:
    case T.VStr{+a1}:
      Eq.string_eq_self(a1)
    case T.VSpan{+a1, +a2}:
      Eq.string_eq_self(T.span.str(a1, a2, U32.is_zero(a2)))
    case T.VInt{+a1, +a2}:
      M2.and.tt(D1.sign.eq(a1, a1), String.eq(a2, a2), sign.self(a1), Eq.string_eq_self(a2))
    case T.VFlo{+a1, +a2}:
      M2.and.tt(D1.sign.eq(a1, a1), String.eq(a2, a2), sign.self(a1), Eq.string_eq_self(a2))
    case T.VBool{+a1}:
      bit.self(a1)
    case T.VWhen{+a1}:
      when.self(a1)
    case T.VArr{+ls}:
      Eq.bit.absurd(&2, {D1.same.atom(T.VArr{ls}, T.VArr{ls}) == True{} : Bool}, ee)
    case T.VInl{+ls}:
      Eq.bit.absurd(&2, {D1.same.atom(T.VInl{ls}, T.VInl{ls}) == True{} : Bool}, ee)
    case T.VHead{+pa, +ls}:
      Eq.bit.absurd(&2, {D1.same.atom(T.VHead{pa, ls}, T.VHead{pa, ls}) == True{} : Bool}, ee)
    case T.VAot{+pa, +ls}:
      Eq.bit.absurd(&2, {D1.same.atom(T.VAot{pa, ls}, T.VAot{pa, ls}) == True{} : Bool}, ee)
    case T.VAots{+pa, +ls}:
      Eq.bit.absurd(&2, {D1.same.atom(T.VAots{pa, ls}, T.VAots{pa, ls}) == True{} : Bool}, ee)
    case T.VPair{+a1, +a2}:
      Eq.bit.absurd(&2, {D1.same.atom(T.VPair{a1, a2}, T.VPair{a1, a2}) == True{} : Bool}, ee)

# the values of well-formed rows each match themselves alone, by induction
# on the rows: a table, an inline table, an array or an array of tables
# matches itself by its list, a scalar by its fields, and wf rules out the
# rest
def wf.selfs(
  xs: List<&2, T.Val>,
  +at: T.WfAt,
  +ee: {T.wf.go(xs, at) == True{} : Bool}
) -> {M1.selfs(xs) == True{} : Bool}:
  match xs:
    case []:
      {==}
    case T.VPair{+nn, T.VStr{+a1}} <> +tt:
      M2.and.tt(D1.same.go(T.VPair{nn, T.VStr{a1}} <> [], T.VPair{nn, T.VStr{a1}} <> []), M1.selfs(tt),
        pair.self.tt(nn, T.VStr{a1}, ww => D1.same.atom(T.VStr{a1}, ww), atom.self(T.VStr{a1}, wf.pair.ok(at, nn, tt,
          T.wf.atom(T.VStr{a1}), _u => T.wf.go(tt, at), ee))),
        wf.selfs(tt, at, wf.pair.more(at, nn, tt, T.wf.atom(T.VStr{a1}), _u => T.wf.go(tt, at), ee)))
    case T.VPair{+nn, T.VSpan{+a1, +a2}} <> +tt:
      M2.and.tt(D1.same.go(T.VPair{nn, T.VSpan{a1, a2}} <> [], T.VPair{nn, T.VSpan{a1, a2}} <> []), M1.selfs(tt),
        pair.self.tt(nn, T.VSpan{a1, a2}, ww => D1.same.atom(T.VSpan{a1, a2}, ww), atom.self(T.VSpan{a1, a2},
          wf.pair.ok(at, nn, tt, T.wf.atom(T.VSpan{a1, a2}), _u => T.wf.go(tt, at), ee))),
        wf.selfs(tt, at, wf.pair.more(at, nn, tt, T.wf.atom(T.VSpan{a1, a2}), _u => T.wf.go(tt, at), ee)))
    case T.VPair{+nn, T.VInt{+a1, +a2}} <> +tt:
      M2.and.tt(D1.same.go(T.VPair{nn, T.VInt{a1, a2}} <> [], T.VPair{nn, T.VInt{a1, a2}} <> []), M1.selfs(tt),
        pair.self.tt(nn, T.VInt{a1, a2}, ww => D1.same.atom(T.VInt{a1, a2}, ww), atom.self(T.VInt{a1, a2},
          wf.pair.ok(at, nn, tt, T.wf.atom(T.VInt{a1, a2}), _u => T.wf.go(tt, at), ee))),
        wf.selfs(tt, at, wf.pair.more(at, nn, tt, T.wf.atom(T.VInt{a1, a2}), _u => T.wf.go(tt, at), ee)))
    case T.VPair{+nn, T.VFlo{+a1, +a2}} <> +tt:
      M2.and.tt(D1.same.go(T.VPair{nn, T.VFlo{a1, a2}} <> [], T.VPair{nn, T.VFlo{a1, a2}} <> []), M1.selfs(tt),
        pair.self.tt(nn, T.VFlo{a1, a2}, ww => D1.same.atom(T.VFlo{a1, a2}, ww), atom.self(T.VFlo{a1, a2},
          wf.pair.ok(at, nn, tt, T.wf.atom(T.VFlo{a1, a2}), _u => T.wf.go(tt, at), ee))),
        wf.selfs(tt, at, wf.pair.more(at, nn, tt, T.wf.atom(T.VFlo{a1, a2}), _u => T.wf.go(tt, at), ee)))
    case T.VPair{+nn, T.VBool{+a1}} <> +tt:
      M2.and.tt(D1.same.go(T.VPair{nn, T.VBool{a1}} <> [], T.VPair{nn, T.VBool{a1}} <> []), M1.selfs(tt),
        pair.self.tt(nn, T.VBool{a1}, ww => D1.same.atom(T.VBool{a1}, ww), atom.self(T.VBool{a1}, wf.pair.ok(at, nn,
          tt, T.wf.atom(T.VBool{a1}), _u => T.wf.go(tt, at), ee))),
        wf.selfs(tt, at, wf.pair.more(at, nn, tt, T.wf.atom(T.VBool{a1}), _u => T.wf.go(tt, at), ee)))
    case T.VPair{+nn, T.VWhen{+a1}} <> +tt:
      M2.and.tt(D1.same.go(T.VPair{nn, T.VWhen{a1}} <> [], T.VPair{nn, T.VWhen{a1}} <> []), M1.selfs(tt),
        pair.self.tt(nn, T.VWhen{a1}, ww => D1.same.atom(T.VWhen{a1}, ww), atom.self(T.VWhen{a1}, wf.pair.ok(at, nn,
          tt, T.wf.atom(T.VWhen{a1}), _u => T.wf.go(tt, at), ee))),
        wf.selfs(tt, at, wf.pair.more(at, nn, tt, T.wf.atom(T.VWhen{a1}), _u => T.wf.go(tt, at), ee)))
    case T.VPair{+nn, T.VArr{+ls}} <> +tt:
      M2.and.tt(D1.same.go(T.VPair{nn, T.VArr{ls}} <> [], T.VPair{nn, T.VArr{ls}} <> []), M1.selfs(tt),
        pair.self.tt(nn, T.VArr{ls}, ww => D1.same.box(D1.KArr{}, ww, ws => D1.same.go(ls, ws)), refl.rows(ls,
          wf.selfs(ls, T.WfItems{}, M3.wt.ok(T.wf.go(ls, T.WfItems{}), _v => T.wf.go(tt, at), wf.pair.more(at, nn, tt,
          True{}, _u => T.wf.then(T.wf.go(ls, T.WfItems{}), _v => T.wf.go(tt, at)), ee))))),
        wf.selfs(tt, at, M3.wt.more(T.wf.go(ls, T.WfItems{}), _v => T.wf.go(tt, at), wf.pair.more(at, nn, tt, True{},
          _u => T.wf.then(T.wf.go(ls, T.WfItems{}), _v => T.wf.go(tt, at)), ee))))
    case T.VPair{+nn, T.VInl{+ls}} <> +tt:
      M2.and.tt(D1.same.go(T.VPair{nn, T.VInl{ls}} <> [], T.VPair{nn, T.VInl{ls}} <> []), M1.selfs(tt),
        pair.self.tt(nn, T.VInl{ls}, ww => D1.same.box(D1.KInl{}, ww, ws => D1.same.go(ls, ws)), refl.rows(ls,
          wf.selfs(ls, T.WfInl{}, M3.wt.ok(T.wf.go(ls, T.WfInl{}), _v => T.wf.go(tt, at), wf.pair.more(at, nn, tt,
              True{},
          _u => T.wf.then(T.wf.go(ls, T.WfInl{}), _v => T.wf.go(tt, at)), ee))))),
        wf.selfs(tt, at, M3.wt.more(T.wf.go(ls, T.WfInl{}), _v => T.wf.go(tt, at), wf.pair.more(at, nn, tt, True{},
          _u => T.wf.then(T.wf.go(ls, T.WfInl{}), _v => T.wf.go(tt, at)), ee))))
    case T.VPair{+nn, T.VHead{+pa, +ls}} <> +tt:
      M2.and.tt(D1.same.go(T.VPair{nn, T.VHead{pa, ls}} <> [], T.VPair{nn, T.VHead{pa, ls}} <> []), M1.selfs(tt),
        pair.self.tt(nn, T.VHead{pa, ls}, ww => D1.same.box(D1.KHead{}, ww, ws => D1.same.go(ls, ws)),
          refl.rows(ls, wf.selfs(ls, T.WfRows{pa}, M3.wt.ok(T.wf.go(ls, T.WfRows{pa}), _v => T.wf.go(tt, at),
          wf.head.more(at, nn, pa, tt, _u => T.wf.then(T.wf.go(ls, T.WfRows{pa}), _v => T.wf.go(tt, at)), ee))))),
        wf.selfs(tt, at, M3.wt.more(T.wf.go(ls, T.WfRows{pa}), _v => T.wf.go(tt, at), wf.head.more(at, nn, pa, tt,
          _u => T.wf.then(T.wf.go(ls, T.WfRows{pa}), _v => T.wf.go(tt, at)), ee))))
    case T.VPair{+nn, T.VAot{+pa, +ls}} <> +tt:
      Eq.bit.absurd(&2, {M1.selfs(T.VPair{nn, T.VAot{pa, ls}} <> tt) == True{} : Bool}, wf.pair.ok(at, nn, tt,
        T.wf.atom(T.VAot{pa, ls}), _u => T.wf.go(tt, at), ee))
    case T.VPair{+nn, T.VAots{+pa, +ls}} <> +tt:
      M2.and.tt(D1.same.go(T.VPair{nn, T.VAots{pa, ls}} <> [], T.VPair{nn, T.VAots{pa, ls}} <> []), M1.selfs(tt),
        pair.self.tt(nn, T.VAots{pa, ls}, ww => D1.same.box(D1.KAots{}, ww, ws => D1.same.go(ls, ws)),
          refl.rows(ls, wf.selfs(ls, T.WfElems{pa}, M3.wt.ok(T.wf.go(ls, T.WfElems{pa}), _v => T.wf.go(tt, at),
          wf.aots.more(at, nn, pa, Bool.not(List.is_empty(&2, T.Val, ls)), tt, _u => T.wf.then(T.wf.go(ls,
          T.WfElems{pa}), _v => T.wf.go(tt, at)), ee))))),
        wf.selfs(tt, at, M3.wt.more(T.wf.go(ls, T.WfElems{pa}), _v => T.wf.go(tt, at), wf.aots.more(at, nn, pa,
          Bool.not(List.is_empty(&2, T.Val, ls)), tt, _u => T.wf.then(T.wf.go(ls, T.WfElems{pa}), _v => T.wf.go(tt,
          at)), ee))))
    case T.VPair{+nn, T.VPair{+a1, +a2}} <> +tt:
      Eq.bit.absurd(&2, {M1.selfs(T.VPair{nn, T.VPair{a1, a2}} <> tt) == True{} : Bool}, wf.pair.ok(at, nn, tt,
        T.wf.atom(T.VPair{a1, a2}), _u => T.wf.go(tt, at), ee))
    case T.VStr{+a1} <> +tt:
      M2.and.tt(D1.same.go(T.VStr{a1} <> [], T.VStr{a1} <> []), M1.selfs(tt),
        item.self.tt(T.VStr{a1}, ww => D1.same.atom(T.VStr{a1}, ww), atom.self(T.VStr{a1}, wf.item.ok(at,
          T.wf.atom(T.VStr{a1}), _u => T.wf.go(tt, at), ee))),
        wf.selfs(tt, at, wf.item.more(at, T.wf.atom(T.VStr{a1}), _u => T.wf.go(tt, at), ee)))
    case T.VSpan{+a1, +a2} <> +tt:
      M2.and.tt(D1.same.go(T.VSpan{a1, a2} <> [], T.VSpan{a1, a2} <> []), M1.selfs(tt),
        item.self.tt(T.VSpan{a1, a2}, ww => D1.same.atom(T.VSpan{a1, a2}, ww), atom.self(T.VSpan{a1, a2},
          wf.item.ok(at, T.wf.atom(T.VSpan{a1, a2}), _u => T.wf.go(tt, at), ee))),
        wf.selfs(tt, at, wf.item.more(at, T.wf.atom(T.VSpan{a1, a2}), _u => T.wf.go(tt, at), ee)))
    case T.VInt{+a1, +a2} <> +tt:
      M2.and.tt(D1.same.go(T.VInt{a1, a2} <> [], T.VInt{a1, a2} <> []), M1.selfs(tt),
        item.self.tt(T.VInt{a1, a2}, ww => D1.same.atom(T.VInt{a1, a2}, ww), atom.self(T.VInt{a1, a2}, wf.item.ok(at,
          T.wf.atom(T.VInt{a1, a2}), _u => T.wf.go(tt, at), ee))),
        wf.selfs(tt, at, wf.item.more(at, T.wf.atom(T.VInt{a1, a2}), _u => T.wf.go(tt, at), ee)))
    case T.VFlo{+a1, +a2} <> +tt:
      M2.and.tt(D1.same.go(T.VFlo{a1, a2} <> [], T.VFlo{a1, a2} <> []), M1.selfs(tt),
        item.self.tt(T.VFlo{a1, a2}, ww => D1.same.atom(T.VFlo{a1, a2}, ww), atom.self(T.VFlo{a1, a2}, wf.item.ok(at,
          T.wf.atom(T.VFlo{a1, a2}), _u => T.wf.go(tt, at), ee))),
        wf.selfs(tt, at, wf.item.more(at, T.wf.atom(T.VFlo{a1, a2}), _u => T.wf.go(tt, at), ee)))
    case T.VBool{+a1} <> +tt:
      M2.and.tt(D1.same.go(T.VBool{a1} <> [], T.VBool{a1} <> []), M1.selfs(tt),
        item.self.tt(T.VBool{a1}, ww => D1.same.atom(T.VBool{a1}, ww), atom.self(T.VBool{a1}, wf.item.ok(at,
          T.wf.atom(T.VBool{a1}), _u => T.wf.go(tt, at), ee))),
        wf.selfs(tt, at, wf.item.more(at, T.wf.atom(T.VBool{a1}), _u => T.wf.go(tt, at), ee)))
    case T.VWhen{+a1} <> +tt:
      M2.and.tt(D1.same.go(T.VWhen{a1} <> [], T.VWhen{a1} <> []), M1.selfs(tt),
        item.self.tt(T.VWhen{a1}, ww => D1.same.atom(T.VWhen{a1}, ww), atom.self(T.VWhen{a1}, wf.item.ok(at,
          T.wf.atom(T.VWhen{a1}), _u => T.wf.go(tt, at), ee))),
        wf.selfs(tt, at, wf.item.more(at, T.wf.atom(T.VWhen{a1}), _u => T.wf.go(tt, at), ee)))
    case T.VArr{+ls} <> +tt:
      M2.and.tt(D1.same.go(T.VArr{ls} <> [], T.VArr{ls} <> []), M1.selfs(tt),
        item.self.tt(T.VArr{ls}, ww => D1.same.box(D1.KArr{}, ww, ws => D1.same.go(ls, ws)), refl.rows(ls,
          wf.selfs(ls, T.WfItems{}, M3.wt.ok(T.wf.go(ls, T.WfItems{}), _v => T.wf.go(tt, at), wf.item.more(at, True{},
          _u => T.wf.then(T.wf.go(ls, T.WfItems{}), _v => T.wf.go(tt, at)), ee))))),
        wf.selfs(tt, at, M3.wt.more(T.wf.go(ls, T.WfItems{}), _v => T.wf.go(tt, at), wf.item.more(at, True{},
          _u => T.wf.then(T.wf.go(ls, T.WfItems{}), _v => T.wf.go(tt, at)), ee))))
    case T.VInl{+ls} <> +tt:
      M2.and.tt(D1.same.go(T.VInl{ls} <> [], T.VInl{ls} <> []), M1.selfs(tt),
        item.self.tt(T.VInl{ls}, ww => D1.same.box(D1.KInl{}, ww, ws => D1.same.go(ls, ws)), refl.rows(ls,
          wf.selfs(ls, T.WfInl{}, M3.wt.ok(T.wf.go(ls, T.WfInl{}), _v => T.wf.go(tt, at), wf.item.more(at, True{},
          _u => T.wf.then(T.wf.go(ls, T.WfInl{}), _v => T.wf.go(tt, at)), ee))))),
        wf.selfs(tt, at, M3.wt.more(T.wf.go(ls, T.WfInl{}), _v => T.wf.go(tt, at), wf.item.more(at, True{},
          _u => T.wf.then(T.wf.go(ls, T.WfInl{}), _v => T.wf.go(tt, at)), ee))))
    case T.VHead{+pa, +ls} <> +tt:
      Eq.bit.absurd(&2, {M1.selfs(T.VHead{pa, ls} <> tt) == True{} : Bool}, wf.item.ok(at, T.wf.atom(T.VHead{pa, ls}),
        _u => T.wf.go(tt, at), ee))
    case T.VAot{+pa, +ls} <> +tt:
      M2.and.tt(D1.same.go(T.VAot{pa, ls} <> [], T.VAot{pa, ls} <> []), M1.selfs(tt),
        item.self.tt(T.VAot{pa, ls}, ww => D1.same.box(D1.KAot{}, ww, ws => D1.same.go(ls, ws)), refl.rows(ls,
          wf.selfs(ls, T.WfRows{pa}, M3.wt.ok(T.wf.go(ls, T.WfRows{pa}), _v => T.wf.go(tt, at), wf.aot.more(at, pa,
          _u => T.wf.then(T.wf.go(ls, T.WfRows{pa}), _v => T.wf.go(tt, at)), ee))))),
        wf.selfs(tt, at, M3.wt.more(T.wf.go(ls, T.WfRows{pa}), _v => T.wf.go(tt, at), wf.aot.more(at, pa,
          _u => T.wf.then(T.wf.go(ls, T.WfRows{pa}), _v => T.wf.go(tt, at)), ee))))
    case T.VAots{+pa, +ls} <> +tt:
      Eq.bit.absurd(&2, {M1.selfs(T.VAots{pa, ls} <> tt) == True{} : Bool}, wf.item.ok(at, T.wf.atom(T.VAots{pa, ls}),
        _u => T.wf.go(tt, at), ee))

# two chars compare the same either way round
def char.sym.go(
  +xx: Char,
  +yy: Char,
  b1: Bool,
  b2: Bool,
  e1: {Char.is_eq(xx, yy) == b1 : Bool},
  e2: {Char.is_eq(yy, xx) == b2 : Bool}
) -> {b1 == b2 : Bool}:
  match b1 b2:
    case True{} True{}:
      {==}
    case False{} False{}:
      {==}
    case True{} False{}:
      Equal.trans(Bool, True{}, Char.is_eq(yy, yy), False{},
        Equal.sym(Bool, Char.is_eq(yy, yy), True{}, Eq.char_eq_self(yy)),
        Equal.trans(Bool, Char.is_eq(yy, yy), Char.is_eq(yy, xx), False{},
          Equal.cong(Char, Bool, zz => Char.is_eq(yy, zz), yy, xx,
            Equal.sym(Char, xx, yy, Eq.char_eq_true(xx, yy, e1))),
          e2))
    case False{} True{}:
      Equal.trans(Bool, False{}, Char.is_eq(xx, yy), True{},
        Equal.sym(Bool, Char.is_eq(xx, yy), False{}, e1),
        Equal.trans(Bool, Char.is_eq(xx, yy), Char.is_eq(xx, xx), True{},
          Equal.cong(Char, Bool, zz => Char.is_eq(xx, zz), yy, xx, Eq.char_eq_true(yy, xx, e2)),
          Eq.char_eq_self(xx)))

# two chars compare the same either way round
def char.sym(+xx: Char, +yy: Char) -> {Char.is_eq(xx, yy) == Char.is_eq(yy, xx) : Bool}:
  char.sym.go(xx, yy, Char.is_eq(xx, yy), Char.is_eq(yy, xx), {==}, {==})

# the code's string walk answers the same either way round
def str.eq.sym(
  aa: String,
  bb: String,
  ss: Bool
) -> {T.str.eq.step(aa, bb, ss) == T.str.eq.step(bb, aa, ss) : Bool}:
  match aa bb ss:
    case SNil{} SNil{} True{}:
      {==}
    case SNil{} SNil{} False{}:
      {==}
    case SNil{} SCon{_h, _t} _s:
      {==}
    case SCon{_h, _t} SNil{} _s:
      {==}
    case SCon{+xx, +xt} SCon{+yy, +yt} True{}:
      Equal.trans(Bool, T.str.eq.step(xt, yt, Char.is_eq(xx, yy)), T.str.eq.step(xt, yt, Char.is_eq(yy, xx)),
        T.str.eq.step(yt, xt, Char.is_eq(yy, xx)),
        Equal.cong(Bool, Bool, bb2 => T.str.eq.step(xt, yt, bb2), Char.is_eq(xx, yy), Char.is_eq(yy, xx),
          char.sym(xx, yy)),
        str.eq.sym(xt, yt, Char.is_eq(yy, xx)))
    case SCon{_x, _xt} SCon{_y, _yt} False{}:
      {==}

# a table's tables, reordered, against them as they are (md false), or an
# array's elements, reordered, against them as they are (md true): each
# compares its rows, reordered, against them as they are
def st.at(md: Bool, +hp: String) -> T.WfAt:
  match md:
    case False{}:
      T.WfRows{hp}
    case True{}:
      T.WfElems{hp}
