# what a lookup finds for a name once a table has been set and entered
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/TbOpenAfterSet.bend as L1
import ../../laws/TbRowsAfterSet.bend as L2
import ../../laws/defs/BareValueGrammar.bend as D1
import ./StringEqualsItself.bend as M1

# Reading a table back once it is set. rows.repl puts a value in every pair of
# the name, so rows.look, which stops at the first, finds the new value.

# whether rows.look found a pair
def look.some(look: T.Look) -> Bool:
  match look:
    case T.KMiss{}:
      False{}
    case _:
      True{}

# the rest of the rows, as the induction hypothesis
def repl.Ih(+tt: List<&2, T.Val>, +seg: String, +xx: T.Val) -> Type:
  {look.some(T.rows.look(tt, seg)) == True{} : Bool} ->
    {T.rows.look(T.rows.repl(tt, seg, xx), seg) == T.look.of(xx) : T.Look}

# one pair: the name's first pair now holds the new value, and another name's
# pair is passed over on both walks
def repl.look.pair(
  bb: Bool,
  +nn: String,
  vv: T.Val,
  +tt: List<&2, T.Val>,
  +seg: String,
  +xx: T.Val,
  +eb: {T.str.eq(nn, seg) == bb : Bool},
  ee: {look.some(T.look.step(T.str.eq(nn, seg), vv, _u => T.rows.look(tt, seg))) == True{} : Bool},
  ih: repl.Ih(tt, seg, xx)
) -> {T.rows.look(T.rows.repl.step(bb, nn, vv, xx, _u => T.rows.repl(tt, seg, xx)), seg)
  == T.look.of(xx) : T.Look}:
  match bb:
    case True{}:
      Equal.cong(Bool, T.Look,
        cc => T.look.step(cc, xx, _u => T.rows.look(T.rows.repl(tt, seg, xx), seg)),
        T.str.eq(nn, seg), True{}, eb)
    case False{}:
      Equal.trans(T.Look,
        T.look.step(T.str.eq(nn, seg), vv, _u => T.rows.look(T.rows.repl(tt, seg, xx), seg)),
        T.rows.look(T.rows.repl(tt, seg, xx), seg),
        T.look.of(xx),
        Equal.cong(Bool, T.Look,
          cc => T.look.step(cc, vv, _u => T.rows.look(T.rows.repl(tt, seg, xx), seg)),
          T.str.eq(nn, seg), False{}, eb),
        ih(Equal.trans(Bool,
          look.some(T.rows.look(tt, seg)),
          look.some(T.look.step(T.str.eq(nn, seg), vv, _u => T.rows.look(tt, seg))),
          True{},
          Equal.sym(Bool, look.some(T.look.step(T.str.eq(nn, seg), vv, _u => T.rows.look(tt, seg))),
            look.some(T.rows.look(tt, seg)),
            Equal.cong(Bool, Bool, cc => look.some(T.look.step(cc, vv, _u => T.rows.look(tt, seg))),
              T.str.eq(nn, seg), False{}, eb)),
          ee)))

# once a name's pairs are replaced, rows.look finds the new value, by
# induction on the rows
def repl.look(
  rows: List<&2, T.Val>,
  +seg: String,
  +xx: T.Val,
  ee: {look.some(T.rows.look(rows, seg)) == True{} : Bool}
) -> {T.rows.look(T.rows.repl(rows, seg, xx), seg) == T.look.of(xx) : T.Look}:
  match rows:
    case []:
      Eq.bit.absurd(&2, {T.rows.look(T.rows.repl([], seg, xx), seg) == T.look.of(xx) : T.Look}, ee)
    case T.VPair{+nn, vv} <> +tt:
      repl.look.pair(T.str.eq(nn, seg), nn, vv, tt, seg, xx, {==}, ee,
        pp => repl.look(tt, seg, xx, pp))
    case T.VStr{_a} <> tt:
      repl.look(tt, seg, xx, ee)
    case T.VSpan{_a, _b} <> tt:
      repl.look(tt, seg, xx, ee)
    case T.VInt{_a, _b} <> tt:
      repl.look(tt, seg, xx, ee)
    case T.VFlo{_a, _b} <> tt:
      repl.look(tt, seg, xx, ee)
    case T.VBool{_a} <> tt:
      repl.look(tt, seg, xx, ee)
    case T.VWhen{_a} <> tt:
      repl.look(tt, seg, xx, ee)
    case T.VArr{_a} <> tt:
      repl.look(tt, seg, xx, ee)
    case T.VInl{_a} <> tt:
      repl.look(tt, seg, xx, ee)
    case T.VHead{_a, _b} <> tt:
      repl.look(tt, seg, xx, ee)
    case T.VAot{_a, _b} <> tt:
      repl.look(tt, seg, xx, ee)
    case T.VAots{_a, _b} <> tt:
      repl.look(tt, seg, xx, ee)

# what rows.look finds for a name once tb.put.in has set its table
def put.after.last(last: T.Last, +pp: String, child: List<&2, T.Val>) -> T.Look:
  match last:
    case T.LastSome{_q, older, _r}:
      T.KAots{pp, T.VAot{pp, child} <> older}
    case T.LastNo{_why}:
      T.KMiss{}

# what rows.look finds for a name once tb.put.in has set its table
def put.after(look: T.Look, +pre: String, +seg: String, child: List<&2, T.Val>) -> T.Look:
  match look:
    case T.KMiss{}:
      T.KHead{T.tree.pre(pre, seg), child}
    case T.KHead{p, _r}:
      T.KHead{p, child}
    case T.KAots{+p, es}:
      put.after.last(T.look.last(es, p), p, child)
    case _:
      T.KMiss{}

# the newest element of an array of tables, set
def put.look.last(
  last: T.Last,
  +pp: String,
  +rows: List<&2, T.Val>,
  +seg: String,
  +child: List<&2, T.Val>,
  el: {look.some(T.rows.look(rows, seg)) == True{} : Bool},
  ec: {D1.tb.last.can(last) == True{} : Bool}
) -> {T.rows.look(D1.tb.last.put(last, seg, rows, pp, child), seg)
  == put.after.last(last, pp, child) : T.Look}:
  match last:
    case T.LastSome{_q, older, _r}:
      repl.look(rows, seg, T.VAots{pp, T.VAot{pp, child} <> older}, el)
    case T.LastNo{why}:
      Eq.bit.absurd(&2, {T.rows.look(D1.tb.last.put(T.LastNo{why}, seg, rows, pp, child), seg)
        == put.after.last(T.LastNo{why}, pp, child) : T.Look}, ec)

# a table set by tb.put.in is what rows.look then finds for its name
def put.look(
  +look: T.Look,
  +rows: List<&2, T.Val>,
  +seg: String,
  +pre: String,
  +child: List<&2, T.Val>,
  el: {T.rows.look(rows, seg) == look : T.Look},
  ec: {D1.tb.can(look) == True{} : Bool}
) -> {T.rows.look(D1.tb.put.in(look, seg, rows, pre, child), seg)
  == put.after(look, pre, seg, child) : T.Look}:
  match look:
    case T.KMiss{}:
      Equal.cong(Bool, T.Look,
        cc => T.look.step(cc, T.VHead{T.tree.pre(pre, seg), child}, _u => T.rows.look(rows, seg)),
        T.str.eq(seg, seg), True{}, M1.str.eq.self(seg))
    case T.KHead{+p, rr}:
      repl.look(rows, seg, T.VHead{p, child},
        Equal.cong(T.Look, Bool, ll => look.some(ll), T.rows.look(rows, seg), T.KHead{p, rr}, el))
    case T.KAots{+p, +es}:
      put.look.last(T.look.last(es, p), p, rows, seg, child,
        Equal.cong(T.Look, Bool, ll => look.some(ll), T.rows.look(rows, seg), T.KAots{p, es}, el), ec)
    case T.KInl{}:
      Eq.bit.absurd(&2, {T.rows.look(D1.tb.put.in(T.KInl{}, seg, rows, pre, child), seg)
        == put.after(T.KInl{}, pre, seg, child) : T.Look}, ec)
    case T.KNo{why}:
      Eq.bit.absurd(&2, {T.rows.look(D1.tb.put.in(T.KNo{why}, seg, rows, pre, child), seg)
        == put.after(T.KNo{why}, pre, seg, child) : T.Look}, ec)

# the newest element, set, holds the child
def after.last.into(
  last: T.Last,
  +pp: String,
  +child: List<&2, T.Val>,
  ec: {D1.tb.last.can(last) == True{} : Bool}
) -> {D1.tb.into(put.after.last(last, pp, child)) == child : List<&2, T.Val>}:
  match last:
    case T.LastSome{_q, _older, _r}:
      {==}
    case T.LastNo{why}:
      Eq.bit.absurd(&2, {D1.tb.into(put.after.last(T.LastNo{why}, pp, child)) == child
        : List<&2, T.Val>}, ec)

# a table set holds the child
def after.into(
  +look: T.Look,
  +pre: String,
  +seg: String,
  +child: List<&2, T.Val>,
  ec: {D1.tb.can(look) == True{} : Bool}
) -> {D1.tb.into(put.after(look, pre, seg, child)) == child : List<&2, T.Val>}:
  match look:
    case T.KMiss{}:
      {==}
    case T.KHead{_p, _r}:
      {==}
    case T.KAots{+p, es}:
      after.last.into(T.look.last(es, p), p, child, ec)
    case T.KInl{}:
      Eq.bit.absurd(&2, {D1.tb.into(put.after(T.KInl{}, pre, seg, child)) == child
        : List<&2, T.Val>}, ec)
    case T.KNo{why}:
      Eq.bit.absurd(&2, {D1.tb.into(put.after(T.KNo{why}, pre, seg, child)) == child
        : List<&2, T.Val>}, ec)

# the newest element, set, can be entered
def after.last.can(
  last: T.Last,
  +pp: String,
  +child: List<&2, T.Val>,
  ec: {D1.tb.last.can(last) == True{} : Bool}
) -> {D1.tb.can(put.after.last(last, pp, child)) == True{} : Bool}:
  match last:
    case T.LastSome{_q, _older, _r}:
      {==}
    case T.LastNo{why}:
      Eq.bit.absurd(&2, {D1.tb.can(put.after.last(T.LastNo{why}, pp, child)) == True{} : Bool}, ec)

# a table set can be entered
def after.can(
  +look: T.Look,
  +pre: String,
  +seg: String,
  +child: List<&2, T.Val>,
  ec: {D1.tb.can(look) == True{} : Bool}
) -> {D1.tb.can(put.after(look, pre, seg, child)) == True{} : Bool}:
  match look:
    case T.KMiss{}:
      {==}
    case T.KHead{_p, _r}:
      {==}
    case T.KAots{+p, es}:
      after.last.can(T.look.last(es, p), p, child, ec)
    case T.KInl{}:
      Eq.bit.absurd(&2, {D1.tb.can(put.after(T.KInl{}, pre, seg, child)) == True{} : Bool}, ec)
    case T.KNo{why}:
      Eq.bit.absurd(&2, {D1.tb.can(put.after(T.KNo{why}, pre, seg, child)) == True{} : Bool}, ec)

# by induction on the path: each segment finds the table it set
def L2.tb_rows_after_set(path, pre, rows, new, eo):
  match path:
    case []:
      {==}
    case +seg <> +rest:
      Equal.trans(List<&2, T.Val>,
        D1.tb.rows(rest, D1.tb.into(T.rows.look(D1.tb.put.in(T.rows.look(rows, seg), seg, rows,
          pre, D1.tb.set(rest, T.tree.pre(pre, seg), D1.tb.into(T.rows.look(rows, seg)), new)),
          seg))),
        D1.tb.rows(rest, D1.tb.set(rest, T.tree.pre(pre, seg), D1.tb.into(T.rows.look(rows,
          seg)), new)),
        new,
        Equal.cong(List<&2, T.Val>, List<&2, T.Val>, xx => D1.tb.rows(rest, xx),
          D1.tb.into(T.rows.look(D1.tb.put.in(T.rows.look(rows, seg), seg, rows, pre,
            D1.tb.set(rest, T.tree.pre(pre, seg), D1.tb.into(T.rows.look(rows, seg)), new)),
            seg)),
          D1.tb.set(rest, T.tree.pre(pre, seg), D1.tb.into(T.rows.look(rows, seg)), new),
          Equal.trans(List<&2, T.Val>,
            D1.tb.into(T.rows.look(D1.tb.put.in(T.rows.look(rows, seg), seg, rows, pre,
              D1.tb.set(rest, T.tree.pre(pre, seg), D1.tb.into(T.rows.look(rows, seg)), new)),
              seg)),
            D1.tb.into(put.after(T.rows.look(rows, seg), pre, seg, D1.tb.set(rest,
              T.tree.pre(pre, seg), D1.tb.into(T.rows.look(rows, seg)), new))),
            D1.tb.set(rest, T.tree.pre(pre, seg), D1.tb.into(T.rows.look(rows, seg)), new),
            Equal.cong(T.Look, List<&2, T.Val>, ll => D1.tb.into(ll),
              T.rows.look(D1.tb.put.in(T.rows.look(rows, seg), seg, rows, pre,
                D1.tb.set(rest, T.tree.pre(pre, seg), D1.tb.into(T.rows.look(rows, seg)), new)),
                seg),
              put.after(T.rows.look(rows, seg), pre, seg, D1.tb.set(rest, T.tree.pre(pre, seg),
                D1.tb.into(T.rows.look(rows, seg)), new)),
              put.look(T.rows.look(rows, seg), rows, seg, pre, D1.tb.set(rest, T.tree.pre(pre, seg),
                D1.tb.into(T.rows.look(rows, seg)), new), {==},
                Eq.and.left(D1.tb.can(T.rows.look(rows, seg)),
                  D1.tb.open(rest, D1.tb.into(T.rows.look(rows, seg))), eo))),
            after.into(T.rows.look(rows, seg), pre, seg, D1.tb.set(rest, T.tree.pre(pre, seg),
              D1.tb.into(T.rows.look(rows, seg)), new),
              Eq.and.left(D1.tb.can(T.rows.look(rows, seg)),
                D1.tb.open(rest, D1.tb.into(T.rows.look(rows, seg))), eo)))),
        L2.tb_rows_after_set(rest, T.tree.pre(pre, seg), D1.tb.into(T.rows.look(rows, seg)), new,
          Eq.and.right(D1.tb.can(T.rows.look(rows, seg)),
            D1.tb.open(rest, D1.tb.into(T.rows.look(rows, seg))), eo)))

# by induction on the path: each segment can still be entered, and leads to
# the table it set
def L1.tb_open_after_set(path, pre, rows, new, eo):
  match path:
    case []:
      {==}
    case +seg <> +rest:
      Equal.trans(Bool,
        Bool.and(D1.tb.can(T.rows.look(D1.tb.put.in(T.rows.look(rows, seg), seg, rows, pre,
          D1.tb.set(rest, T.tree.pre(pre, seg), D1.tb.into(T.rows.look(rows, seg)), new)), seg)),
          D1.tb.open(rest, D1.tb.into(T.rows.look(D1.tb.put.in(T.rows.look(rows, seg), seg,
            rows, pre, D1.tb.set(rest, T.tree.pre(pre, seg), D1.tb.into(T.rows.look(rows, seg)),
              new)), seg)))),
        Bool.and(D1.tb.can(put.after(T.rows.look(rows, seg), pre, seg, D1.tb.set(rest,
          T.tree.pre(pre, seg), D1.tb.into(T.rows.look(rows, seg)), new))),
          D1.tb.open(rest, D1.tb.into(put.after(T.rows.look(rows, seg), pre, seg,
            D1.tb.set(rest, T.tree.pre(pre, seg), D1.tb.into(T.rows.look(rows, seg)), new))))),
        True{},
        Equal.cong(T.Look, Bool, ll => Bool.and(D1.tb.can(ll), D1.tb.open(rest, D1.tb.into(ll))),
          T.rows.look(D1.tb.put.in(T.rows.look(rows, seg), seg, rows, pre,
            D1.tb.set(rest, T.tree.pre(pre, seg), D1.tb.into(T.rows.look(rows, seg)), new)), seg),
          put.after(T.rows.look(rows, seg), pre, seg, D1.tb.set(rest, T.tree.pre(pre, seg),
            D1.tb.into(T.rows.look(rows, seg)), new)),
          put.look(T.rows.look(rows, seg), rows, seg, pre, D1.tb.set(rest, T.tree.pre(pre, seg),
            D1.tb.into(T.rows.look(rows, seg)), new), {==},
            Eq.and.left(D1.tb.can(T.rows.look(rows, seg)),
              D1.tb.open(rest, D1.tb.into(T.rows.look(rows, seg))), eo))),
        Equal.trans(Bool,
          Bool.and(D1.tb.can(put.after(T.rows.look(rows, seg), pre, seg, D1.tb.set(rest,
            T.tree.pre(pre, seg), D1.tb.into(T.rows.look(rows, seg)), new))),
            D1.tb.open(rest, D1.tb.into(put.after(T.rows.look(rows, seg), pre, seg,
              D1.tb.set(rest, T.tree.pre(pre, seg), D1.tb.into(T.rows.look(rows, seg)), new))))),
          D1.tb.open(rest, D1.tb.into(put.after(T.rows.look(rows, seg), pre, seg,
            D1.tb.set(rest, T.tree.pre(pre, seg), D1.tb.into(T.rows.look(rows, seg)), new)))),
          True{},
          Equal.cong(Bool, Bool,
            bb => Bool.and(bb, D1.tb.open(rest, D1.tb.into(put.after(T.rows.look(rows, seg), pre,
              seg, D1.tb.set(rest, T.tree.pre(pre, seg), D1.tb.into(T.rows.look(rows, seg)),
                new))))),
            D1.tb.can(put.after(T.rows.look(rows, seg), pre, seg, D1.tb.set(rest,
              T.tree.pre(pre, seg), D1.tb.into(T.rows.look(rows, seg)), new))),
            True{},
            after.can(T.rows.look(rows, seg), pre, seg, D1.tb.set(rest, T.tree.pre(pre, seg),
              D1.tb.into(T.rows.look(rows, seg)), new),
              Eq.and.left(D1.tb.can(T.rows.look(rows, seg)),
                D1.tb.open(rest, D1.tb.into(T.rows.look(rows, seg))), eo))),
          Equal.trans(Bool,
            D1.tb.open(rest, D1.tb.into(put.after(T.rows.look(rows, seg), pre, seg,
              D1.tb.set(rest, T.tree.pre(pre, seg), D1.tb.into(T.rows.look(rows, seg)), new)))),
            D1.tb.open(rest, D1.tb.set(rest, T.tree.pre(pre, seg),
              D1.tb.into(T.rows.look(rows, seg)), new)),
            True{},
            Equal.cong(List<&2, T.Val>, Bool, xx => D1.tb.open(rest, xx),
              D1.tb.into(put.after(T.rows.look(rows, seg), pre, seg, D1.tb.set(rest,
                T.tree.pre(pre, seg), D1.tb.into(T.rows.look(rows, seg)), new))),
              D1.tb.set(rest, T.tree.pre(pre, seg), D1.tb.into(T.rows.look(rows, seg)), new),
              after.into(T.rows.look(rows, seg), pre, seg, D1.tb.set(rest, T.tree.pre(pre, seg),
                D1.tb.into(T.rows.look(rows, seg)), new),
                Eq.and.left(D1.tb.can(T.rows.look(rows, seg)),
                  D1.tb.open(rest, D1.tb.into(T.rows.look(rows, seg))), eo))),
            L1.tb_open_after_set(rest, T.tree.pre(pre, seg), D1.tb.into(T.rows.look(rows, seg)),
              new, Eq.and.right(D1.tb.can(T.rows.look(rows, seg)),
                D1.tb.open(rest, D1.tb.into(T.rows.look(rows, seg))), eo)))))
