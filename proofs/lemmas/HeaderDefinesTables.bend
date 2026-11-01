# what [table] and [[array]] headers define, extend or start in the rows
import Base
import ../../main.bend as T
import ../../laws/AotHeaderExtendsArray.bend as L1
import ../../laws/AotHeaderStartsArray.bend as L2
import ../../laws/HeaderDefinesImplicitTable.bend as L3
import ../../laws/HeaderDefinesNewTable.bend as L4
import ../../laws/defs/BareValueGrammar.bend as D1
import ./NavigationWalkFrames.bend as M1

# WP-W: contracts of the walk. A walk along a path is one navigation step per
# segment before the last (nav.walk), then the job at the last (tree.leaf),
# then the frames rebuilt back to the root (nav.rebuild). A step goes through
# what rows.look finds, and the laws' premises are what get finds, so the two
# lookups are shown to agree first.

# what the walk asks a table for a name, read off what get finds
def tb.look(hh: T.Hit) -> T.Look:
  match hh:
    case T.Found{vv}:
      T.look.of(vv)
    case T.Miss{}:
      T.KMiss{}

# one pair of the rows: both lookups stop at it or both pass it
def look.get.step(
  bb: Bool,
  vv: T.Val,
  tt: List<&2, T.Val>,
  +kk: String,
  ih: {T.rows.look(tt, kk) == tb.look(T.rows.find(tt, kk)) : T.Look}
) -> {T.look.step(bb, vv, _u => T.rows.look(tt, kk))
  == tb.look(T.find.step(bb, vv, _u => T.rows.find(tt, kk))) : T.Look}:
  match bb:
    case True{}:
      {==}
    case False{}:
      ih

# rows.look finds what get finds, by induction on the rows
def look.get(
  rows: List<&2, T.Val>,
  +kk: String
) -> {T.rows.look(rows, kk) == tb.look(T.get(rows, kk)) : T.Look}:
  match rows:
    case []:
      {==}
    case T.VPair{nn, vv} <> +tt:
      look.get.step(T.str.eq(nn, kk), vv, tt, kk, look.get(tt, kk))
    case T.VStr{_a} <> tt:
      look.get(tt, kk)
    case T.VSpan{_a, _b} <> tt:
      look.get(tt, kk)
    case T.VInt{_a, _b} <> tt:
      look.get(tt, kk)
    case T.VFlo{_a, _b} <> tt:
      look.get(tt, kk)
    case T.VBool{_a} <> tt:
      look.get(tt, kk)
    case T.VWhen{_a} <> tt:
      look.get(tt, kk)
    case T.VArr{_a} <> tt:
      look.get(tt, kk)
    case T.VInl{_a} <> tt:
      look.get(tt, kk)
    case T.VHead{_a, _b} <> tt:
      look.get(tt, kk)
    case T.VAot{_a, _b} <> tt:
      look.get(tt, kk)
    case T.VAots{_a, _b} <> tt:
      look.get(tt, kk)

# so a premise about get is one about rows.look
def look.via(
  +rows: List<&2, T.Val>,
  +kk: String,
  hh: T.Hit,
  ee: {T.get(rows, kk) == hh : T.Hit}
) -> {T.rows.look(rows, kk) == tb.look(hh) : T.Look}:
  Equal.trans(T.Look, T.rows.look(rows, kk), tb.look(T.get(rows, kk)), tb.look(hh),
    look.get(rows, kk), Equal.cong(T.Hit, T.Look, xx => tb.look(xx), T.get(rows, kk), hh, ee))

# every segment of a header is navigation
def quiet.def(path: List<&2, String>) -> {M1.nav.quiet(path, T.JDef{}, 0) == True{} : Bool}:
  match path:
    case []:
      {==}
    case _seg <> rest:
      quiet.def(rest)

def L4.header_defines_new_table(segs, k, rows, heads, eo, em):
  Equal.trans(T.End,
    T.tree.walk(List.append(&2, String, segs, [k]), T.Tw{rows, T.JDef{}, [], "", "", heads, False{}},
      0),
    T.tree.leaf(k, T.Tw{D1.tb.rows(segs, rows), T.JDef{}, M1.nav.frs(segs, "", rows, []), "",
      D1.tb.join(segs, ""), heads, False{}}),
    T.End{D1.tb.set(segs, "", rows, T.VPair{k, T.VHead{T.tree.pre(D1.tb.join(segs, ""), k), []}}
      <> D1.tb.rows(segs, rows)), "", T.heads.by.head(T.tree.pre(D1.tb.join(segs, ""), k))
      <> heads},
    M1.nav.walk(segs, k, rows, T.JDef{}, [], "", heads, False{}, 0, eo, quiet.def(segs)),
    Equal.trans(T.End,
      T.tree.leaf(k, T.Tw{D1.tb.rows(segs, rows), T.JDef{}, M1.nav.frs(segs, "", rows, []), "",
        D1.tb.join(segs, ""), heads, False{}}),
      T.tree.rebuild(M1.nav.frs(segs, "", rows, []), T.VPair{k, T.VHead{T.tree.pre(D1.tb.join(segs,
        ""), k), []}} <> D1.tb.rows(segs, rows), "",
        T.heads.by.head(T.tree.pre(D1.tb.join(segs, ""), k)) <> heads),
      T.End{D1.tb.set(segs, "", rows, T.VPair{k, T.VHead{T.tree.pre(D1.tb.join(segs, ""), k),
        []}} <> D1.tb.rows(segs, rows)), "",
        T.heads.by.head(T.tree.pre(D1.tb.join(segs, ""), k)) <> heads},
      Equal.cong(T.Look, T.End,
        ll => T.tree.leaf.def.hit(ll, k, D1.tb.rows(segs, rows), M1.nav.frs(segs, "", rows, []), "",
          T.tree.pre(D1.tb.join(segs, ""), k), heads),
        T.rows.look(D1.tb.rows(segs, rows), k), T.KMiss{},
        look.via(D1.tb.rows(segs, rows), k, T.Miss{}, em)),
      M1.nav.rebuild(segs, "", rows, [], T.VPair{k, T.VHead{T.tree.pre(D1.tb.join(segs, ""), k), []}}
        <> D1.tb.rows(segs, rows), "", T.heads.by.head(T.tree.pre(D1.tb.join(segs, ""), k))
        <> heads, eo)))

def L3.header_defines_implicit_table(segs, k, rows, heads, p, sub, eo, ef, eh):
  Equal.trans(T.End,
    T.tree.walk(List.append(&2, String, segs, [k]), T.Tw{rows, T.JDef{}, [], "", "", heads, False{}},
      0),
    T.tree.leaf(k, T.Tw{D1.tb.rows(segs, rows), T.JDef{}, M1.nav.frs(segs, "", rows, []), "",
      D1.tb.join(segs, ""), heads, False{}}),
    T.End{D1.tb.set(segs, "", rows, T.rows.repl(D1.tb.rows(segs, rows), k,
      T.VHead{T.tree.pre(D1.tb.join(segs, ""), k), sub})), "",
      T.heads.by.head(T.tree.pre(D1.tb.join(segs, ""), k)) <> heads},
    M1.nav.walk(segs, k, rows, T.JDef{}, [], "", heads, False{}, 0, eo, quiet.def(segs)),
    Equal.trans(T.End,
      T.tree.leaf(k, T.Tw{D1.tb.rows(segs, rows), T.JDef{}, M1.nav.frs(segs, "", rows, []), "",
        D1.tb.join(segs, ""), heads, False{}}),
      T.tree.leaf.def.head(T.heads.has(heads, T.tree.pre(D1.tb.join(segs, ""), k)), k,
        D1.tb.rows(segs, rows), sub, M1.nav.frs(segs, "", rows, []), "",
        T.tree.pre(D1.tb.join(segs, ""), k), heads),
      T.End{D1.tb.set(segs, "", rows, T.rows.repl(D1.tb.rows(segs, rows), k,
        T.VHead{T.tree.pre(D1.tb.join(segs, ""), k), sub})), "",
        T.heads.by.head(T.tree.pre(D1.tb.join(segs, ""), k)) <> heads},
      Equal.cong(T.Look, T.End,
        ll => T.tree.leaf.def.hit(ll, k, D1.tb.rows(segs, rows), M1.nav.frs(segs, "", rows, []), "",
          T.tree.pre(D1.tb.join(segs, ""), k), heads),
        T.rows.look(D1.tb.rows(segs, rows), k), T.KHead{p, sub},
        look.via(D1.tb.rows(segs, rows), k, T.Found{T.VHead{p, sub}}, ef)),
      Equal.trans(T.End,
        T.tree.leaf.def.head(T.heads.has(heads, T.tree.pre(D1.tb.join(segs, ""), k)), k,
          D1.tb.rows(segs, rows), sub, M1.nav.frs(segs, "", rows, []), "",
          T.tree.pre(D1.tb.join(segs, ""), k), heads),
        T.tree.rebuild(M1.nav.frs(segs, "", rows, []), T.rows.repl(D1.tb.rows(segs, rows), k,
          T.VHead{T.tree.pre(D1.tb.join(segs, ""), k), sub}), "",
          T.heads.by.head(T.tree.pre(D1.tb.join(segs, ""), k)) <> heads),
        T.End{D1.tb.set(segs, "", rows, T.rows.repl(D1.tb.rows(segs, rows), k,
          T.VHead{T.tree.pre(D1.tb.join(segs, ""), k), sub})), "",
          T.heads.by.head(T.tree.pre(D1.tb.join(segs, ""), k)) <> heads},
        Equal.cong(Bool, T.End,
          bb => T.tree.leaf.def.head(bb, k, D1.tb.rows(segs, rows), sub,
            M1.nav.frs(segs, "", rows, []), "", T.tree.pre(D1.tb.join(segs, ""), k), heads),
          T.heads.has(heads, T.tree.pre(D1.tb.join(segs, ""), k)), False{}, eh),
        M1.nav.rebuild(segs, "", rows, [], T.rows.repl(D1.tb.rows(segs, rows), k,
          T.VHead{T.tree.pre(D1.tb.join(segs, ""), k), sub}), "",
          T.heads.by.head(T.tree.pre(D1.tb.join(segs, ""), k)) <> heads, eo))))

# every segment of an array-of-tables header is navigation
def quiet.aot(path: List<&2, String>) -> {M1.nav.quiet(path, T.JAot{}, 0) == True{} : Bool}:
  match path:
    case []:
      {==}
    case _seg <> rest:
      quiet.aot(rest)

def L2.aot_header_starts_array(segs, k, rows, heads, eo, em):
  Equal.trans(T.End,
    T.tree.walk(List.append(&2, String, segs, [k]), T.Tw{rows, T.JAot{}, [], "", "", heads, False{}},
      0),
    T.tree.leaf(k, T.Tw{D1.tb.rows(segs, rows), T.JAot{}, M1.nav.frs(segs, "", rows, []), "",
      D1.tb.join(segs, ""), heads, False{}}),
    T.End{D1.tb.set(segs, "", rows, T.VPair{k, T.VAots{T.tree.pre(D1.tb.join(segs, ""), k),
      [T.VAot{T.tree.pre(D1.tb.join(segs, ""), k), []}]}} <> D1.tb.rows(segs, rows)), "", heads},
    M1.nav.walk(segs, k, rows, T.JAot{}, [], "", heads, False{}, 0, eo, quiet.aot(segs)),
    Equal.trans(T.End,
      T.tree.leaf(k, T.Tw{D1.tb.rows(segs, rows), T.JAot{}, M1.nav.frs(segs, "", rows, []), "",
        D1.tb.join(segs, ""), heads, False{}}),
      T.tree.rebuild(M1.nav.frs(segs, "", rows, []), T.VPair{k, T.VAots{T.tree.pre(D1.tb.join(segs,
        ""), k), [T.VAot{T.tree.pre(D1.tb.join(segs, ""), k), []}]}} <> D1.tb.rows(segs, rows),
        "", heads),
      T.End{D1.tb.set(segs, "", rows, T.VPair{k, T.VAots{T.tree.pre(D1.tb.join(segs, ""), k),
        [T.VAot{T.tree.pre(D1.tb.join(segs, ""), k), []}]}} <> D1.tb.rows(segs, rows)), "",
        heads},
      Equal.cong(T.Look, T.End,
        ll => T.tree.leaf.aot.hit(ll, k, D1.tb.rows(segs, rows), M1.nav.frs(segs, "", rows, []), "",
          T.tree.pre(D1.tb.join(segs, ""), k), heads),
        T.rows.look(D1.tb.rows(segs, rows), k), T.KMiss{},
        look.via(D1.tb.rows(segs, rows), k, T.Miss{}, em)),
      M1.nav.rebuild(segs, "", rows, [], T.VPair{k, T.VAots{T.tree.pre(D1.tb.join(segs, ""), k),
        [T.VAot{T.tree.pre(D1.tb.join(segs, ""), k), []}]}} <> D1.tb.rows(segs, rows), "", heads,
        eo)))

def L1.aot_header_extends_array(segs, k, rows, heads, p, elems, eo, ef):
  Equal.trans(T.End,
    T.tree.walk(List.append(&2, String, segs, [k]), T.Tw{rows, T.JAot{}, [], "", "", heads, False{}},
      0),
    T.tree.leaf(k, T.Tw{D1.tb.rows(segs, rows), T.JAot{}, M1.nav.frs(segs, "", rows, []), "",
      D1.tb.join(segs, ""), heads, False{}}),
    T.End{D1.tb.set(segs, "", rows, T.rows.repl(D1.tb.rows(segs, rows), k,
      T.VAots{T.tree.pre(D1.tb.join(segs, ""), k), T.VAot{T.tree.pre(D1.tb.join(segs, ""), k), []}
        <> elems})), "",
      T.heads.drop(heads, String.append(T.tree.pre(D1.tb.join(segs, ""), k), "."))},
    M1.nav.walk(segs, k, rows, T.JAot{}, [], "", heads, False{}, 0, eo, quiet.aot(segs)),
    Equal.trans(T.End,
      T.tree.leaf(k, T.Tw{D1.tb.rows(segs, rows), T.JAot{}, M1.nav.frs(segs, "", rows, []), "",
        D1.tb.join(segs, ""), heads, False{}}),
      T.tree.rebuild(M1.nav.frs(segs, "", rows, []), T.rows.repl(D1.tb.rows(segs, rows), k,
        T.VAots{T.tree.pre(D1.tb.join(segs, ""), k), T.VAot{T.tree.pre(D1.tb.join(segs, ""), k),
          []} <> elems}), "",
        T.heads.drop(heads, String.append(T.tree.pre(D1.tb.join(segs, ""), k), "."))),
      T.End{D1.tb.set(segs, "", rows, T.rows.repl(D1.tb.rows(segs, rows), k,
        T.VAots{T.tree.pre(D1.tb.join(segs, ""), k), T.VAot{T.tree.pre(D1.tb.join(segs, ""), k),
          []} <> elems})), "",
        T.heads.drop(heads, String.append(T.tree.pre(D1.tb.join(segs, ""), k), "."))},
      Equal.cong(T.Look, T.End,
        ll => T.tree.leaf.aot.hit(ll, k, D1.tb.rows(segs, rows), M1.nav.frs(segs, "", rows, []), "",
          T.tree.pre(D1.tb.join(segs, ""), k), heads),
        T.rows.look(D1.tb.rows(segs, rows), k), T.KAots{p, elems},
        look.via(D1.tb.rows(segs, rows), k, T.Found{T.VAots{p, elems}}, ef)),
      M1.nav.rebuild(segs, "", rows, [], T.rows.repl(D1.tb.rows(segs, rows), k,
        T.VAots{T.tree.pre(D1.tb.join(segs, ""), k), T.VAot{T.tree.pre(D1.tb.join(segs, ""), k),
          []} <> elems}), "",
        T.heads.drop(heads, String.append(T.tree.pre(D1.tb.join(segs, ""), k), ".")), eo)))
