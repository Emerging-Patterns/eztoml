# navigation steps, the frames a walk pushes and rebuilding them
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/WalkPutAtHead.bend as L1
import ../../laws/defs/BareValueGrammar.bend as D1

# a navigation step's job records no definition
def define.quiet(
  sj: T.Job,
  pp: String,
  hs: List<&2, String>,
  ee: {T.tree.sub.dot(sj) == False{} : Bool}
) -> {T.heads.define(sj, pp, hs) == hs : List<&2, String>}:
  match sj:
    case T.JPut{vv}:
      Eq.bit.absurd2(&2, {T.heads.define(T.JPut{vv}, pp, hs) == hs : List<&2, String>}, ee)
    case T.JDef{}:
      {==}
    case T.JAot{}:
      {==}

# the frame a navigation step pushes for what the name refers to
def tb.last.fr(last: T.Last, name: String, vs: List<&2, T.Val>, pp: String) -> T.Fr:
  match last:
    case T.LastSome{_q, older, _r}:
      T.FrAot{name, vs, older, pp}
    case T.LastNo{_why}:
      T.FrRep{name, vs, pp}

# the frame a navigation step pushes for what the name refers to
def tb.fr(look: T.Look, +name: String, vs: List<&2, T.Val>, +pre: String) -> T.Fr:
  match look:
    case T.KMiss{}:
      T.FrNew{name, vs, T.tree.pre(pre, name)}
    case T.KHead{p, _r}:
      T.FrRep{name, vs, p}
    case T.KAots{+p, elems}:
      tb.last.fr(T.look.last(elems, p), name, vs, p)
    case _:
      T.FrRep{name, vs, pre}

# the frames a walk along the path pushes, the innermost first
def nav.frs(
  path: List<&2, String>,
  +pre: String,
  +rows: List<&2, T.Val>,
  stack: List<&2, T.Fr>
) -> List<&2, T.Fr>:
  match path:
    case []:
      stack
    case +seg <> rest:
      nav.frs(rest, T.tree.pre(pre, seg), D1.tb.into(T.rows.look(rows, seg)),
        tb.fr(T.rows.look(rows, seg), seg, rows, pre) <> stack)

# whether every segment of the path is navigation for the job: no step asks
# who defined a table or records one
def nav.quiet(path: List<&2, String>, +job: T.Job, +skip: U32) -> Bool:
  match path:
    case []:
      True{}
    case _seg <> rest:
      Bool.and(Bool.not(T.tree.sub.dot(T.tree.sub.job(U32.is_zero(skip), job))),
        nav.quiet(rest, job, T.path.dec(skip)))

# where one navigation step leaves the walk
def sub.Goal(
  +look: T.Look,
  +seg: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +mark: Bool
) -> Type:
  {T.tree.sub.look(look, seg, vs, job, stack, pre, heads, inl, mark)
    == T.Tw{D1.tb.into(look), job, tb.fr(look, seg, vs, pre) <> stack, "", T.tree.pre(pre, seg),
      heads, inl} : T.Tw}

# a step into an array of tables enters its newest element
def sub.step.last(
  last: T.Last,
  +pp: String,
  +seg: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  ec: {D1.tb.last.can(last) == True{} : Bool}
) -> {T.tree.sub.aots(last, seg, vs, job, stack, pre, heads, inl, pp)
  == T.Tw{D1.tb.last.rows(last), job, tb.last.fr(last, seg, vs, pp) <> stack, "",
    T.tree.pre(pre, seg), heads, inl} : T.Tw}:
  match last:
    case T.LastSome{_q, _older, _r}:
      {==}
    case T.LastNo{why}:
      Eq.bit.absurd(&2, {T.tree.sub.aots(T.LastNo{why}, seg, vs, job, stack, pre, heads, inl, pp)
        == T.Tw{D1.tb.last.rows(T.LastNo{why}), job, tb.last.fr(T.LastNo{why}, seg, vs, pp)
          <> stack, "", T.tree.pre(pre, seg), heads, inl} : T.Tw}, ec)

# a navigation step enters the table the name refers to, pushes its frame, and
# leaves the error and the recorded definitions alone
def sub.step(
  +look: T.Look,
  +seg: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +mark: Bool,
  ec: {D1.tb.can(look) == True{} : Bool},
  +eq: {T.tree.sub.dot(T.tree.sub.job(mark, job)) == False{} : Bool}
) -> sub.Goal(look, seg, vs, job, stack, pre, heads, inl, mark):
  match look:
    case T.KMiss{}:
      Equal.cong(List<&2, String>, T.Tw,
        hh => T.Tw{[], job, T.FrNew{seg, vs, T.tree.pre(pre, seg)} <> stack, "", T.tree.pre(pre, seg),
          hh, inl},
        T.heads.define(T.tree.sub.job(mark, job), T.tree.pre(pre, seg), heads), heads,
        define.quiet(T.tree.sub.job(mark, job), T.tree.pre(pre, seg), heads, eq))
    case T.KHead{+p, +rr}:
      Equal.trans(T.Tw,
        T.tree.sub.head(T.tree.sub.dot(T.tree.sub.job(mark, job)), p, rr, seg, vs, job, stack, pre,
          heads, inl, mark),
        T.tree.sub.head(False{}, p, rr, seg, vs, job, stack, pre, heads, inl, mark),
        T.Tw{rr, job, T.FrRep{seg, vs, p} <> stack, "", T.tree.pre(pre, seg), heads, inl},
        Equal.cong(Bool, T.Tw,
          bb => T.tree.sub.head(bb, p, rr, seg, vs, job, stack, pre, heads, inl, mark),
          T.tree.sub.dot(T.tree.sub.job(mark, job)), False{}, eq),
        Equal.cong(List<&2, String>, T.Tw,
          hh => T.Tw{rr, job, T.FrRep{seg, vs, p} <> stack, "", T.tree.pre(pre, seg), hh, inl},
          T.heads.define(T.tree.sub.job(mark, job), T.tree.pre(pre, seg), heads), heads,
          define.quiet(T.tree.sub.job(mark, job), T.tree.pre(pre, seg), heads, eq)))
    case T.KAots{+p, +es}:
      Equal.trans(T.Tw,
        T.tree.sub.arr(T.tree.sub.dot(T.tree.sub.job(mark, job)), p, es, seg, vs, job, stack, pre,
          heads, inl),
        T.tree.sub.aots(T.look.last(es, p), seg, vs, job, stack, pre, heads, inl, p),
        T.Tw{D1.tb.last.rows(T.look.last(es, p)), job, tb.last.fr(T.look.last(es, p), seg, vs, p)
          <> stack, "", T.tree.pre(pre, seg), heads, inl},
        Equal.cong(Bool, T.Tw,
          bb => T.tree.sub.arr(bb, p, es, seg, vs, job, stack, pre, heads, inl),
          T.tree.sub.dot(T.tree.sub.job(mark, job)), False{}, eq),
        sub.step.last(T.look.last(es, p), p, seg, vs, job, stack, pre, heads, inl, ec))
    case T.KInl{}:
      Eq.bit.absurd(&2, {T.tree.sub.look(T.KInl{}, seg, vs, job, stack, pre, heads, inl, mark)
        == T.Tw{D1.tb.into(T.KInl{}), job, tb.fr(T.KInl{}, seg, vs, pre) <> stack, "",
          T.tree.pre(pre, seg), heads, inl} : T.Tw}, ec)
    case T.KNo{why}:
      Eq.bit.absurd(&2, {T.tree.sub.look(T.KNo{why}, seg, vs, job, stack, pre, heads, inl, mark)
        == T.Tw{D1.tb.into(T.KNo{why}), job, tb.fr(T.KNo{why}, seg, vs, pre) <> stack, "",
          T.tree.pre(pre, seg), heads, inl} : T.Tw}, ec)

# the walk goes on past a segment with the rest of the path
def walk.cons(
  +seg: String,
  rest: List<&2, String>,
  +kk: String,
  +tw: T.Tw,
  +skip: U32
) -> {T.tree.walk(seg <> List.append(&2, String, rest, [kk]), tw, skip)
  == T.tree.walk(List.append(&2, String, rest, [kk]), T.tree.sub(seg, tw, U32.is_zero(skip)),
    T.path.dec(skip)) : T.End}:
  match rest:
    case []:
      {==}
    case _r <> _rr:
      {==}

# where a walk along the path to one more name comes to that name
def nav.Goal(
  path: List<&2, String>,
  +kk: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +skip: U32
) -> Type:
  {T.tree.walk(List.append(&2, String, path, [kk]), T.Tw{vs, job, stack, "", pre, heads, inl}, skip)
    == T.tree.leaf(kk, T.Tw{D1.tb.rows(path, vs), job, nav.frs(path, pre, vs, stack), "",
      D1.tb.join(path, pre), heads, inl}) : T.End}

# by induction on the path: each segment is one navigation step
def nav.walk(
  path: List<&2, String>,
  +kk: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +skip: U32,
  +eo: {D1.tb.open(path, vs) == True{} : Bool},
  +eq: {nav.quiet(path, job, skip) == True{} : Bool}
) -> nav.Goal(path, kk, vs, job, stack, pre, heads, inl, skip):
  match path:
    case []:
      {==}
    case +seg <> +rest:
      Equal.trans(T.End,
        T.tree.walk(seg <> List.append(&2, String, rest, [kk]), T.Tw{vs, job, stack, "", pre, heads,
          inl}, skip),
        T.tree.walk(List.append(&2, String, rest, [kk]), T.Tw{D1.tb.into(T.rows.look(vs, seg)), job,
          tb.fr(T.rows.look(vs, seg), seg, vs, pre) <> stack, "", T.tree.pre(pre, seg), heads, inl},
          T.path.dec(skip)),
        T.tree.leaf(kk, T.Tw{D1.tb.rows(rest, D1.tb.into(T.rows.look(vs, seg))), job,
          nav.frs(rest, T.tree.pre(pre, seg), D1.tb.into(T.rows.look(vs, seg)),
            tb.fr(T.rows.look(vs, seg), seg, vs, pre) <> stack), "",
          D1.tb.join(rest, T.tree.pre(pre, seg)), heads, inl}),
        Equal.trans(T.End,
          T.tree.walk(seg <> List.append(&2, String, rest, [kk]), T.Tw{vs, job, stack, "", pre, heads,
            inl}, skip),
          T.tree.walk(List.append(&2, String, rest, [kk]), T.tree.sub(seg, T.Tw{vs, job, stack, "",
            pre, heads, inl}, U32.is_zero(skip)), T.path.dec(skip)),
          T.tree.walk(List.append(&2, String, rest, [kk]), T.Tw{D1.tb.into(T.rows.look(vs, seg)),
            job, tb.fr(T.rows.look(vs, seg), seg, vs, pre) <> stack, "", T.tree.pre(pre, seg), heads,
            inl}, T.path.dec(skip)),
          walk.cons(seg, rest, kk, T.Tw{vs, job, stack, "", pre, heads, inl}, skip),
          Equal.cong(T.Tw, T.End,
            tw => T.tree.walk(List.append(&2, String, rest, [kk]), tw, T.path.dec(skip)),
            T.tree.sub(seg, T.Tw{vs, job, stack, "", pre, heads, inl}, U32.is_zero(skip)),
            T.Tw{D1.tb.into(T.rows.look(vs, seg)), job, tb.fr(T.rows.look(vs, seg), seg, vs, pre)
              <> stack, "", T.tree.pre(pre, seg), heads, inl},
            sub.step(T.rows.look(vs, seg), seg, vs, job, stack, pre, heads, inl, U32.is_zero(skip),
              Eq.and.left(D1.tb.can(T.rows.look(vs, seg)),
                D1.tb.open(rest, D1.tb.into(T.rows.look(vs, seg))), eo),
              Eq.not.true(T.tree.sub.dot(T.tree.sub.job(U32.is_zero(skip), job)),
                Eq.and.left(Bool.not(T.tree.sub.dot(T.tree.sub.job(U32.is_zero(skip), job))),
                  nav.quiet(rest, job, T.path.dec(skip)), eq))))),
        nav.walk(rest, kk, D1.tb.into(T.rows.look(vs, seg)), job,
          tb.fr(T.rows.look(vs, seg), seg, vs, pre) <> stack, T.tree.pre(pre, seg), heads, inl,
          T.path.dec(skip),
          Eq.and.right(D1.tb.can(T.rows.look(vs, seg)),
            D1.tb.open(rest, D1.tb.into(T.rows.look(vs, seg))), eo),
          Eq.and.right(Bool.not(T.tree.sub.dot(T.tree.sub.job(U32.is_zero(skip), job))),
            nav.quiet(rest, job, T.path.dec(skip)), eq)))

# rebuilding the frame of an array of tables' element puts the element back
def wrap.last(
  last: T.Last,
  +pp: String,
  +seg: String,
  +vs: List<&2, T.Val>,
  +child: List<&2, T.Val>,
  ec: {D1.tb.last.can(last) == True{} : Bool}
) -> {T.tree.wrap(tb.last.fr(last, seg, vs, pp), child)
  == D1.tb.last.put(last, seg, vs, pp, child) : List<&2, T.Val>}:
  match last:
    case T.LastSome{_q, _older, _r}:
      {==}
    case T.LastNo{why}:
      Eq.bit.absurd(&2, {T.tree.wrap(tb.last.fr(T.LastNo{why}, seg, vs, pp), child)
        == D1.tb.last.put(T.LastNo{why}, seg, vs, pp, child) : List<&2, T.Val>}, ec)

# rebuilding a navigation step's frame puts the table back where it was
def wrap.step(
  +look: T.Look,
  +seg: String,
  +vs: List<&2, T.Val>,
  +pre: String,
  +child: List<&2, T.Val>,
  ec: {D1.tb.can(look) == True{} : Bool}
) -> {T.tree.wrap(tb.fr(look, seg, vs, pre), child)
  == D1.tb.put.in(look, seg, vs, pre, child) : List<&2, T.Val>}:
  match look:
    case T.KMiss{}:
      {==}
    case T.KHead{_p, _r}:
      {==}
    case T.KAots{+p, +es}:
      wrap.last(T.look.last(es, p), p, seg, vs, child, ec)
    case T.KInl{}:
      Eq.bit.absurd(&2, {T.tree.wrap(tb.fr(T.KInl{}, seg, vs, pre), child)
        == D1.tb.put.in(T.KInl{}, seg, vs, pre, child) : List<&2, T.Val>}, ec)
    case T.KNo{why}:
      Eq.bit.absurd(&2, {T.tree.wrap(tb.fr(T.KNo{why}, seg, vs, pre), child)
        == D1.tb.put.in(T.KNo{why}, seg, vs, pre, child) : List<&2, T.Val>}, ec)

# by induction on the path: rebuilding the frames a walk pushed sets the table
# at the path's end to what the leaf left, and puts every table above it back
def nav.rebuild(
  path: List<&2, String>,
  +pre: String,
  +vs: List<&2, T.Val>,
  +stack: List<&2, T.Fr>,
  +child: List<&2, T.Val>,
  +bad: String,
  +heads: List<&2, String>,
  +eo: {D1.tb.open(path, vs) == True{} : Bool}
) -> {T.tree.rebuild(nav.frs(path, pre, vs, stack), child, bad, heads)
  == T.tree.rebuild(stack, D1.tb.set(path, pre, vs, child), bad, heads) : T.End}:
  match path:
    case []:
      {==}
    case +seg <> +rest:
      Equal.trans(T.End,
        T.tree.rebuild(nav.frs(rest, T.tree.pre(pre, seg), D1.tb.into(T.rows.look(vs, seg)),
          tb.fr(T.rows.look(vs, seg), seg, vs, pre) <> stack), child, bad, heads),
        T.tree.rebuild(tb.fr(T.rows.look(vs, seg), seg, vs, pre) <> stack,
          D1.tb.set(rest, T.tree.pre(pre, seg), D1.tb.into(T.rows.look(vs, seg)), child), bad,
          heads),
        T.tree.rebuild(stack, D1.tb.put.in(T.rows.look(vs, seg), seg, vs, pre,
          D1.tb.set(rest, T.tree.pre(pre, seg), D1.tb.into(T.rows.look(vs, seg)), child)), bad,
          heads),
        nav.rebuild(rest, T.tree.pre(pre, seg), D1.tb.into(T.rows.look(vs, seg)),
          tb.fr(T.rows.look(vs, seg), seg, vs, pre) <> stack, child, bad, heads,
          Eq.and.right(D1.tb.can(T.rows.look(vs, seg)),
            D1.tb.open(rest, D1.tb.into(T.rows.look(vs, seg))), eo)),
        Equal.cong(List<&2, T.Val>, T.End, xx => T.tree.rebuild(stack, xx, bad, heads),
          T.tree.wrap(tb.fr(T.rows.look(vs, seg), seg, vs, pre),
            D1.tb.set(rest, T.tree.pre(pre, seg), D1.tb.into(T.rows.look(vs, seg)), child)),
          D1.tb.put.in(T.rows.look(vs, seg), seg, vs, pre,
            D1.tb.set(rest, T.tree.pre(pre, seg), D1.tb.into(T.rows.look(vs, seg)), child)),
          wrap.step(T.rows.look(vs, seg), seg, vs, pre,
            D1.tb.set(rest, T.tree.pre(pre, seg), D1.tb.into(T.rows.look(vs, seg)), child),
            Eq.and.left(D1.tb.can(T.rows.look(vs, seg)),
              D1.tb.open(rest, D1.tb.into(T.rows.look(vs, seg))), eo))))

# a segment the walk counts down past is navigation for a put
def quiet.put.step(
  zz: Bool,
  vv: T.Val,
  qq: Bool,
  ez: {Bool.not(zz) == True{} : Bool},
  eq: {qq == True{} : Bool}
) -> {Bool.and(Bool.not(T.tree.sub.dot(T.tree.sub.job(zz, T.JPut{vv}))), qq) == True{} : Bool}:
  match zz:
    case True{}:
      Eq.bit.absurd(&2, {Bool.and(Bool.not(T.tree.sub.dot(T.tree.sub.job(True{}, T.JPut{vv}))), qq)
        == True{} : Bool}, ez)
    case False{}:
      eq

# every segment the walk counts down past is navigation for a put
def quiet.put(
  path: List<&2, String>,
  +vv: T.Val,
  +skip: U32,
  +ec: {D1.counts.down(path, skip) == True{} : Bool}
) -> {nav.quiet(path, T.JPut{vv}, skip) == True{} : Bool}:
  match path:
    case []:
      {==}
    case _seg <> +rest:
      quiet.put.step(U32.is_zero(skip), vv, nav.quiet(rest, T.JPut{vv}, T.path.dec(skip)),
        Eq.and.left(Bool.not(U32.is_zero(skip)), D1.counts.down(rest, T.path.dec(skip)), ec),
        quiet.put(rest, vv, T.path.dec(skip),
          Eq.and.right(Bool.not(U32.is_zero(skip)), D1.counts.down(rest, T.path.dec(skip)), ec)))

def L1.walk_put_at_head(here, k, v, rows, heads, skip, inl, eo, ec, em):
  Equal.trans(T.End,
    T.tree.walk(List.append(&2, String, here, [k]), T.Tw{rows, T.JPut{v}, [], "", "", heads, inl},
      skip),
    T.tree.leaf(k, T.Tw{D1.tb.rows(here, rows), T.JPut{v}, nav.frs(here, "", rows, []), "",
      D1.tb.join(here, ""), heads, inl}),
    T.End{D1.tb.set(here, "", rows, T.VPair{k, v} <> D1.tb.rows(here, rows)), "", heads},
    nav.walk(here, k, rows, T.JPut{v}, [], "", heads, inl, skip, eo, quiet.put(here, v, skip, ec)),
    Equal.trans(T.End,
      T.tree.leaf(k, T.Tw{D1.tb.rows(here, rows), T.JPut{v}, nav.frs(here, "", rows, []), "",
        D1.tb.join(here, ""), heads, inl}),
      T.tree.rebuild(nav.frs(here, "", rows, []), T.VPair{k, v} <> D1.tb.rows(here, rows), "",
        heads),
      T.End{D1.tb.set(here, "", rows, T.VPair{k, v} <> D1.tb.rows(here, rows)), "", heads},
      Equal.cong(T.Hit, T.End,
        hh => T.tree.leaf.put(hh, k, D1.tb.rows(here, rows), v, nav.frs(here, "", rows, []), "",
          heads),
        T.get(D1.tb.rows(here, rows), k), T.Miss{}, em),
      nav.rebuild(here, "", rows, [], T.VPair{k, v} <> D1.tb.rows(here, rows), "", heads, eo)))
