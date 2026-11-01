# proofs of laws/DefinesEachTableOnce.bend
import Base
import ../main.bend as T
import ../src/eq.bend as Eq
import ../laws/DefinesEachTableOnce.bend as Laws
import ../laws/defs/BareValueGrammar.bend as D1
import ./lemmas/FailedWalkNameCompare.bend as M1
import ./lemmas/HeaderDefinesTables.bend as M2
import ./lemmas/NavigationWalkFrames.bend as M3
import ./lemmas/StringEqualsItself.bend as M4

# laws/DefinesEachTableOnce.bend. The walk steps that decide whether a key may add to a table.

# rebuilding the tables above a walk leaves the recorded definitions alone
def rebuild.heads(
  stack: List<&2, T.Fr>,
  vs: List<&2, T.Val>,
  bad: String,
  heads: List<&2, String>
) -> {Laws.end_heads(T.tree.rebuild(stack, vs, bad, heads)) == heads
  : List<&2, String>}:
  match stack:
    case []:
      {==}
    case fr <> tt:
      rebuild.heads(tt, T.tree.wrap(fr, vs), bad, heads)

# a table a header just recorded is one a header defined
def heads.head.first(
  +pp: String,
  hs: List<&2, String>
) -> {T.heads.head(T.heads.by.head(pp) <> hs, pp) == True{} : Bool}:
  Equal.cong(Bool, Bool, bb => T.heads.or(bb, T.heads.head(hs, pp)),
    T.str.eq(pp, pp), True{}, M4.str.eq.self(pp))

# and it is still there once the walk is rebuilt
def rebuild.head(
  stack: List<&2, T.Fr>,
  vs: List<&2, T.Val>,
  bad: String,
  +pp: String,
  +hs: List<&2, String>
) -> {T.heads.head(Laws.end_heads(T.tree.rebuild(stack, vs, bad, T.heads.by.head(pp) <> hs)),
  pp) == True{} : Bool}:
  Equal.trans(Bool,
    T.heads.head(Laws.end_heads(T.tree.rebuild(stack, vs, bad, T.heads.by.head(pp) <> hs)), pp),
    T.heads.head(T.heads.by.head(pp) <> hs, pp),
    True{},
    Equal.cong(List<&2, String>, Bool, ll => T.heads.head(ll, pp),
      Laws.end_heads(T.tree.rebuild(stack, vs, bad, T.heads.by.head(pp) <> hs)),
      T.heads.by.head(pp) <> hs, rebuild.heads(stack, vs, bad, T.heads.by.head(pp) <> hs)),
    heads.head.first(pp, hs))

def Laws.dotted_key_refused_in_header_table(path, rows, name, vs, val, stack, pre, heads, inl, e):
  %Equal.sym(Bool, T.heads.head(heads, T.tree.pre(pre, name)), True{}, e)
    : {String.is_empty(Laws.tw_bad(T.tree.sub.head.go(_, path, rows, name, vs,
      T.JPut{val}, stack, pre, heads, inl, True{}))) == False{} : Bool}
  {==}

def Laws.dotted_key_enters_other_table(path, rows, name, vs, val, stack, pre, heads, inl, e):
  %Equal.sym(Bool, T.heads.head(heads, T.tree.pre(pre, name)), False{}, e)
    : {Laws.tw_bad(T.tree.sub.head.go(_, path, rows, name, vs, T.JPut{val}, stack,
      pre, heads, inl, True{})) == "" : String}
  {==}

def Laws.dotted_key_refused_in_array_of_tables(_path, _elems, _name, _vs, _val, _stack, _pre, _heads, _inl):
  {==}

# a header's job never asks who defined the table, wherever the walk is
def Laws.header_enters_any_table(_path, _rows, _name, _vs, arr, _stack, _pre, _heads, _inl, mark):
  match arr mark:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def Laws.header_records_new_table(name, vs, stack, bad, path, heads):
  rebuild.head(stack, T.VPair{name, T.VHead{path, []}} <> vs, bad, path, heads)

def Laws.header_records_implicit_table(p, rows, name, vs, stack, bad, path, heads, e):
  Equal.trans(Bool,
    T.heads.head(Laws.end_heads(T.tree.leaf.def.hit(T.KHead{p, rows}, name, vs, stack,
      bad, path, heads)), path),
    T.heads.head(Laws.end_heads(T.tree.leaf.def.head(False{}, name, vs, rows, stack,
      bad, path, heads)), path),
    True{},
    Equal.cong(Bool, Bool,
      ss => T.heads.head(Laws.end_heads(T.tree.leaf.def.head(ss, name, vs, rows, stack,
        bad, path, heads)), path),
      T.heads.has(heads, path), False{}, e),
    rebuild.head(stack, T.rows.repl(vs, name, T.VHead{path, rows}), bad, path, heads))

# a table the drop kept does not name a path under the prefix
def drop.kept.gone(
  bb: Bool,
  +hh: String,
  +pre: String,
  +ss: String,
  rest: List<&2, String>,
  eb: {T.str.eq(hh, String.append(pre, ss)) == bb : Bool},
  eu: {String.starts_with(hh, pre) == False{} : Bool},
  ih: {T.heads.has(rest, String.append(pre, ss)) == False{} : Bool}
) -> {T.heads.or(bb, T.heads.has(rest, String.append(pre, ss))) == False{} : Bool}:
  match bb:
    case False{}:
      ih
    case True{}:
      Eq.bit.absurd(&2,
        {T.heads.or(True{}, T.heads.has(rest, String.append(pre, ss))) == False{}
          : Bool},
        Equal.trans(Bool, False{}, String.starts_with(hh, pre), True{},
          Equal.sym(Bool, String.starts_with(hh, pre), False{}, eu),
          Equal.trans(Bool, String.starts_with(hh, pre),
            String.starts_with(String.append(pre, ss), pre), True{},
            Equal.cong(String, Bool, xx => String.starts_with(xx, pre), hh,
              String.append(pre, ss), M1.str.eq.true(hh, String.append(pre, ss), eb)),
            Eq.starts_append(pre, ss))))

# one step of the drop keeps no table under the prefix
def drop.step.gone(
  under: Bool,
  mm: Char,
  +hh: String,
  +pre: String,
  +ss: String,
  rest: List<&2, String>,
  eu: {String.starts_with(hh, pre) == under : Bool},
  ih: {T.heads.has(rest, String.append(pre, ss)) == False{} : Bool}
) -> {T.heads.has(T.heads.drop.step(under, mm, hh, rest), String.append(pre, ss))
  == False{} : Bool}:
  match under:
    case True{}:
      ih
    case False{}:
      drop.kept.gone(T.str.eq(hh, String.append(pre, ss)), hh, pre, ss, rest, {==}, eu,
        ih)

# the drop keeps no table under the prefix
def drop.gone(
  hs: List<&2, String>,
  +pre: String,
  +ss: String
) -> {T.heads.has(T.heads.drop(hs, pre), String.append(pre, ss)) == False{} : Bool}:
  match hs:
    case []:
      {==}
    case SCon{mm, +hh} <> +tt:
      drop.step.gone(String.starts_with(hh, pre), mm, hh, pre, ss, T.heads.drop(tt, pre),
        {==}, drop.gone(tt, pre, ss))
    case SNil{} <> tt:
      drop.gone(tt, pre, ss)

# a table the drop removed does not name a path outside the prefix
def drop.under.keeps(
  bb: Bool,
  +hh: String,
  +pre: String,
  +qq: String,
  rest: List<&2, String>,
  tt: List<&2, String>,
  eb: {T.str.eq(hh, qq) == bb : Bool},
  eu: {String.starts_with(hh, pre) == True{} : Bool},
  ee: {String.starts_with(qq, pre) == False{} : Bool},
  ih: {T.heads.has(rest, qq) == T.heads.has(tt, qq) : Bool}
) -> {T.heads.has(rest, qq) == T.heads.or(bb, T.heads.has(tt, qq)) : Bool}:
  match bb:
    case False{}:
      ih
    case True{}:
      Eq.bit.absurd(&2,
        {T.heads.has(rest, qq) == T.heads.or(True{}, T.heads.has(tt, qq)) : Bool},
        Equal.trans(Bool, False{}, String.starts_with(qq, pre), True{},
          Equal.sym(Bool, String.starts_with(qq, pre), False{}, ee),
          Equal.trans(Bool, String.starts_with(qq, pre), String.starts_with(hh, pre),
            True{},
            Equal.cong(String, Bool, xx => String.starts_with(xx, pre), qq, hh,
              Equal.sym(String, hh, qq, M1.str.eq.true(hh, qq, eb))),
            eu)))

# one step of the drop leaves a path outside the prefix as defined as it was
def drop.step.keeps(
  under: Bool,
  mm: Char,
  +hh: String,
  +pre: String,
  +qq: String,
  rest: List<&2, String>,
  tt: List<&2, String>,
  eu: {String.starts_with(hh, pre) == under : Bool},
  ee: {String.starts_with(qq, pre) == False{} : Bool},
  ih: {T.heads.has(rest, qq) == T.heads.has(tt, qq) : Bool}
) -> {T.heads.has(T.heads.drop.step(under, mm, hh, rest), qq)
  == T.heads.has(SCon{mm, hh} <> tt, qq) : Bool}:
  match under:
    case True{}:
      drop.under.keeps(T.str.eq(hh, qq), hh, pre, qq, rest, tt, {==}, eu, ee, ih)
    case False{}:
      Equal.cong(Bool, Bool, xx => T.heads.or(T.str.eq(hh, qq), xx),
        T.heads.has(rest, qq), T.heads.has(tt, qq), ih)

# the drop leaves a path outside the prefix as defined as it was
def drop.keeps(
  hs: List<&2, String>,
  +pre: String,
  +qq: String,
  +ee: {String.starts_with(qq, pre) == False{} : Bool}
) -> {T.heads.has(T.heads.drop(hs, pre), qq) == T.heads.has(hs, qq) : Bool}:
  match hs:
    case []:
      {==}
    case SCon{mm, +hh} <> +tt:
      drop.step.keeps(String.starts_with(hh, pre), mm, hh, pre, qq,
        T.heads.drop(tt, pre), tt, {==}, ee, drop.keeps(tt, pre, qq, ee))
    case SNil{} <> tt:
      drop.keeps(tt, pre, qq, ee)

# a new element's tables are the old ones with those under the array dropped
def aot.heads(
  pp: String,
  elems: List<&2, T.Val>,
  name: String,
  vs: List<&2, T.Val>,
  stack: List<&2, T.Fr>,
  bad: String,
  +path: String,
  heads: List<&2, String>
) -> {Laws.end_heads(T.tree.leaf.aot.hit(T.KAots{pp, elems}, name, vs, stack, bad, path,
  heads)) == T.heads.drop(heads, String.append(path, ".")) : List<&2, String>}:
  rebuild.heads(stack, T.rows.repl(vs, name, T.VAots{path, T.VAot{path, []} <> elems}),
    bad, T.heads.drop(heads, String.append(path, ".")))

def Laws.new_element_forgets_tables_under_it(p, elems, name, vs, stack, bad, path, heads, rest):
  Equal.trans(Bool,
    T.heads.has(Laws.end_heads(T.tree.leaf.aot.hit(T.KAots{p, elems}, name, vs, stack,
      bad, path, heads)), String.append(String.append(path, "."), rest)),
    T.heads.has(T.heads.drop(heads, String.append(path, ".")),
      String.append(String.append(path, "."), rest)),
    False{},
    Equal.cong(List<&2, String>, Bool,
      ll => T.heads.has(ll, String.append(String.append(path, "."), rest)),
      Laws.end_heads(T.tree.leaf.aot.hit(T.KAots{p, elems}, name, vs, stack, bad, path,
        heads)),
      T.heads.drop(heads, String.append(path, ".")),
      aot.heads(p, elems, name, vs, stack, bad, path, heads)),
    drop.gone(heads, String.append(path, "."), rest))

def Laws.new_element_keeps_other_tables(p, elems, name, vs, stack, bad, path, heads, q, e):
  Equal.trans(Bool,
    T.heads.has(Laws.end_heads(T.tree.leaf.aot.hit(T.KAots{p, elems}, name, vs, stack,
      bad, path, heads)), q),
    T.heads.has(T.heads.drop(heads, String.append(path, ".")), q),
    T.heads.has(heads, q),
    Equal.cong(List<&2, String>, Bool, ll => T.heads.has(ll, q),
      Laws.end_heads(T.tree.leaf.aot.hit(T.KAots{p, elems}, name, vs, stack, bad, path,
        heads)),
      T.heads.drop(heads, String.append(path, ".")),
      aot.heads(p, elems, name, vs, stack, bad, path, heads)),
    drop.keeps(heads, String.append(path, "."), q, e))

# by induction on the rows, each case as inl.seal takes it
def Laws.closed_inline_table_holds_no_open_table(rows):
  match rows:
    case []:
      {==}
    case T.VPair{_n, T.VHead{_p, _r}} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VPair{_n, T.VStr{_a}} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VPair{_n, T.VSpan{_a, _b}} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VPair{_n, T.VInt{_a, _b}} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VPair{_n, T.VFlo{_a, _b}} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VPair{_n, T.VBool{_a}} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VPair{_n, T.VWhen{_a}} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VPair{_n, T.VArr{_a}} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VPair{_n, T.VInl{_a}} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VPair{_n, T.VAot{_a, _b}} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VPair{_n, T.VAots{_a, _b}} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VPair{_n, T.VPair{_a, _b}} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VStr{_a} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VSpan{_a, _b} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VInt{_a, _b} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VFlo{_a, _b} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VBool{_a} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VWhen{_a} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VArr{_a} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VInl{_a} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VHead{_a, _b} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VAot{_a, _b} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VAots{_a, _b} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)

def Laws.inline_table_refuses_keys(_name, _vs, _job, _stack, _pre, _heads, _inl, _mark):
  {==}

# rebuilding the tables above a walk leaves its error alone
def rebuild.bad(
  stack: List<&2, T.Fr>,
  vs: List<&2, T.Val>,
  bad: String,
  heads: List<&2, String>
) -> {D1.end_bad(T.tree.rebuild(stack, vs, bad, heads)) == bad : String}:
  match stack:
    case []:
      {==}
    case fr <> tt:
      rebuild.bad(tt, T.tree.wrap(fr, vs), bad, heads)

# and whether it has one
def rebuild.empty(
  stack: List<&2, T.Fr>,
  vs: List<&2, T.Val>,
  bad: String,
  heads: List<&2, String>
) -> {String.is_empty(D1.end_bad(T.tree.rebuild(stack, vs, bad, heads)))
  == String.is_empty(bad) : Bool}:
  Equal.cong(String, Bool, ss => String.is_empty(ss),
    D1.end_bad(T.tree.rebuild(stack, vs, bad, heads)), bad, rebuild.bad(stack, vs, bad, heads))

# a put's job at the last name: a new pair, or an error for a name held
def put.exact(
  hh: T.Hit,
  kk: String,
  vs: List<&2, T.Val>,
  vv: T.Val,
  stack: List<&2, T.Fr>,
  heads: List<&2, String>
) -> {String.is_empty(D1.end_bad(T.tree.leaf.put(hh, kk, vs, vv, stack, "", heads)))
  == Laws.is_miss(hh) : Bool}:
  match hh:
    case T.Found{_x}:
      rebuild.empty(stack, vs, T.err.first("", "duplicate key"), heads)
    case T.Miss{}:
      rebuild.empty(stack, T.VPair{kk, vv} <> vs, "", heads)

def Laws.walk_put_refused_exactly(here, k, v, rows, heads, skip, inl, eo, ec):
  Equal.trans(Bool,
    String.is_empty(D1.end_bad(T.tree.walk(List.append(&2, String, here, [k]),
      T.Tw{rows, T.JPut{v}, [], "", "", heads, inl}, skip))),
    String.is_empty(D1.end_bad(T.tree.leaf(k, T.Tw{D1.tb.rows(here, rows), T.JPut{v},
      M3.nav.frs(here, "", rows, []), "", D1.tb.join(here, ""), heads, inl}))),
    Laws.is_miss(T.get(D1.tb.rows(here, rows), k)),
    Equal.cong(T.End, Bool, ee => String.is_empty(D1.end_bad(ee)),
      T.tree.walk(List.append(&2, String, here, [k]), T.Tw{rows, T.JPut{v}, [], "", "", heads, inl},
        skip),
      T.tree.leaf(k, T.Tw{D1.tb.rows(here, rows), T.JPut{v}, M3.nav.frs(here, "", rows, []), "",
        D1.tb.join(here, ""), heads, inl}),
      M3.nav.walk(here, k, rows, T.JPut{v}, [], "", heads, inl, skip, eo, M3.quiet.put(here, v, skip, ec))),
    put.exact(T.get(D1.tb.rows(here, rows), k), k, D1.tb.rows(here, rows), v,
      M3.nav.frs(here, "", rows, []), heads))

# a header of a table that exists: refused when a header or dotted keys
# defined it
def hdr.seen(
  seen: Bool,
  kk: String,
  vs: List<&2, T.Val>,
  rr: List<&2, T.Val>,
  stack: List<&2, T.Fr>,
  +pp: String,
  heads: List<&2, String>
) -> {String.is_empty(D1.end_bad(T.tree.leaf.def.head(seen, kk, vs, rr, stack, "", pp, heads)))
  == Bool.not(seen) : Bool}:
  match seen:
    case True{}:
      rebuild.empty(stack, vs, T.err.first("", "duplicate table"), heads)
    case False{}:
      rebuild.empty(stack, T.rows.repl(vs, kk, T.VHead{pp, rr}), "", T.heads.by.head(pp) <> heads)

# a [table] header's job at the last name, for each thing get can find there
def hdr.exact(
  hh: T.Hit,
  +kk: String,
  +vs: List<&2, T.Val>,
  +stack: List<&2, T.Fr>,
  +pp: String,
  +heads: List<&2, String>
) -> {String.is_empty(D1.end_bad(T.tree.leaf.def.hit(M2.tb.look(hh), kk, vs, stack, "", pp, heads)))
  == Laws.hdr.ok(hh, heads, pp) : Bool}:
  match hh:
    case T.Miss{}:
      rebuild.empty(stack, T.VPair{kk, T.VHead{pp, []}} <> vs, "", T.heads.by.head(pp) <> heads)
    case T.Found{T.VHead{_p, rr}}:
      hdr.seen(T.heads.has(heads, pp), kk, vs, rr, stack, pp, heads)
    case T.Found{T.VInl{_a}}:
      rebuild.empty(stack, vs, T.err.first("", "inline table is closed"), heads)
    case T.Found{T.VAots{_a, _b}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)
    case T.Found{T.VStr{_a}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)
    case T.Found{T.VSpan{_a, _b}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)
    case T.Found{T.VInt{_a, _b}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)
    case T.Found{T.VFlo{_a, _b}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)
    case T.Found{T.VBool{_a}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)
    case T.Found{T.VWhen{_a}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)
    case T.Found{T.VArr{_a}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)
    case T.Found{T.VAot{_a, _b}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)
    case T.Found{T.VPair{_a, _b}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)

def Laws.header_refused_exactly(segs, k, rows, heads, eo):
  Equal.trans(Bool,
    String.is_empty(D1.end_bad(T.tree.walk(List.append(&2, String, segs, [k]),
      T.Tw{rows, T.JDef{}, [], "", "", heads, False{}}, 0))),
    String.is_empty(D1.end_bad(T.tree.leaf(k, T.Tw{D1.tb.rows(segs, rows), T.JDef{},
      M3.nav.frs(segs, "", rows, []), "", D1.tb.join(segs, ""), heads, False{}}))),
    Laws.hdr.ok(T.get(D1.tb.rows(segs, rows), k), heads, T.tree.pre(D1.tb.join(segs, ""), k)),
    Equal.cong(T.End, Bool, ee => String.is_empty(D1.end_bad(ee)),
      T.tree.walk(List.append(&2, String, segs, [k]), T.Tw{rows, T.JDef{}, [], "", "", heads,
        False{}}, 0),
      T.tree.leaf(k, T.Tw{D1.tb.rows(segs, rows), T.JDef{}, M3.nav.frs(segs, "", rows, []), "",
        D1.tb.join(segs, ""), heads, False{}}),
      M3.nav.walk(segs, k, rows, T.JDef{}, [], "", heads, False{}, 0, eo, M2.quiet.def(segs))),
    Equal.trans(Bool,
      String.is_empty(D1.end_bad(T.tree.leaf.def.hit(T.rows.look(D1.tb.rows(segs, rows), k), k,
        D1.tb.rows(segs, rows), M3.nav.frs(segs, "", rows, []), "",
        T.tree.pre(D1.tb.join(segs, ""), k), heads))),
      String.is_empty(D1.end_bad(T.tree.leaf.def.hit(M2.tb.look(T.get(D1.tb.rows(segs, rows), k)),
        k, D1.tb.rows(segs, rows), M3.nav.frs(segs, "", rows, []), "",
        T.tree.pre(D1.tb.join(segs, ""), k), heads))),
      Laws.hdr.ok(T.get(D1.tb.rows(segs, rows), k), heads, T.tree.pre(D1.tb.join(segs, ""), k)),
      Equal.cong(T.Look, Bool,
        ll => String.is_empty(D1.end_bad(T.tree.leaf.def.hit(ll, k, D1.tb.rows(segs, rows),
          M3.nav.frs(segs, "", rows, []), "", T.tree.pre(D1.tb.join(segs, ""), k), heads))),
        T.rows.look(D1.tb.rows(segs, rows), k), M2.tb.look(T.get(D1.tb.rows(segs, rows), k)),
        M2.look.get(D1.tb.rows(segs, rows), k)),
      hdr.exact(T.get(D1.tb.rows(segs, rows), k), k, D1.tb.rows(segs, rows),
        M3.nav.frs(segs, "", rows, []), T.tree.pre(D1.tb.join(segs, ""), k), heads)))

# an [[array]] header's job at the last name, for each thing get can find there
def aot.exact(
  hh: T.Hit,
  +kk: String,
  +vs: List<&2, T.Val>,
  +stack: List<&2, T.Fr>,
  +pp: String,
  +heads: List<&2, String>
) -> {String.is_empty(D1.end_bad(T.tree.leaf.aot.hit(M2.tb.look(hh), kk, vs, stack, "", pp, heads)))
  == Laws.aot.ok(hh) : Bool}:
  match hh:
    case T.Miss{}:
      rebuild.empty(stack, T.VPair{kk, T.VAots{pp, [T.VAot{pp, []}]}} <> vs, "", heads)
    case T.Found{T.VAots{_p, es}}:
      rebuild.empty(stack, T.rows.repl(vs, kk, T.VAots{pp, T.VAot{pp, []} <> es}), "",
        T.heads.drop(heads, String.append(pp, ".")))
    case T.Found{T.VHead{_a, _b}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)
    case T.Found{T.VInl{_a}}:
      rebuild.empty(stack, vs, T.err.first("", "inline table is closed"), heads)
    case T.Found{T.VStr{_a}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)
    case T.Found{T.VSpan{_a, _b}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)
    case T.Found{T.VInt{_a, _b}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)
    case T.Found{T.VFlo{_a, _b}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)
    case T.Found{T.VBool{_a}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)
    case T.Found{T.VWhen{_a}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)
    case T.Found{T.VArr{_a}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)
    case T.Found{T.VAot{_a, _b}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)
    case T.Found{T.VPair{_a, _b}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)

def Laws.aot_header_refused_exactly(segs, k, rows, heads, eo):
  Equal.trans(Bool,
    String.is_empty(D1.end_bad(T.tree.walk(List.append(&2, String, segs, [k]),
      T.Tw{rows, T.JAot{}, [], "", "", heads, False{}}, 0))),
    String.is_empty(D1.end_bad(T.tree.leaf(k, T.Tw{D1.tb.rows(segs, rows), T.JAot{},
      M3.nav.frs(segs, "", rows, []), "", D1.tb.join(segs, ""), heads, False{}}))),
    Laws.aot.ok(T.get(D1.tb.rows(segs, rows), k)),
    Equal.cong(T.End, Bool, ee => String.is_empty(D1.end_bad(ee)),
      T.tree.walk(List.append(&2, String, segs, [k]), T.Tw{rows, T.JAot{}, [], "", "", heads,
        False{}}, 0),
      T.tree.leaf(k, T.Tw{D1.tb.rows(segs, rows), T.JAot{}, M3.nav.frs(segs, "", rows, []), "",
        D1.tb.join(segs, ""), heads, False{}}),
      M3.nav.walk(segs, k, rows, T.JAot{}, [], "", heads, False{}, 0, eo, M2.quiet.aot(segs))),
    Equal.trans(Bool,
      String.is_empty(D1.end_bad(T.tree.leaf.aot.hit(T.rows.look(D1.tb.rows(segs, rows), k), k,
        D1.tb.rows(segs, rows), M3.nav.frs(segs, "", rows, []), "",
        T.tree.pre(D1.tb.join(segs, ""), k), heads))),
      String.is_empty(D1.end_bad(T.tree.leaf.aot.hit(M2.tb.look(T.get(D1.tb.rows(segs, rows), k)),
        k, D1.tb.rows(segs, rows), M3.nav.frs(segs, "", rows, []), "",
        T.tree.pre(D1.tb.join(segs, ""), k), heads))),
      Laws.aot.ok(T.get(D1.tb.rows(segs, rows), k)),
      Equal.cong(T.Look, Bool,
        ll => String.is_empty(D1.end_bad(T.tree.leaf.aot.hit(ll, k, D1.tb.rows(segs, rows),
          M3.nav.frs(segs, "", rows, []), "", T.tree.pre(D1.tb.join(segs, ""), k), heads))),
        T.rows.look(D1.tb.rows(segs, rows), k), M2.tb.look(T.get(D1.tb.rows(segs, rows), k)),
        M2.look.get(D1.tb.rows(segs, rows), k)),
      aot.exact(T.get(D1.tb.rows(segs, rows), k), k, D1.tb.rows(segs, rows),
        M3.nav.frs(segs, "", rows, []), T.tree.pre(D1.tb.join(segs, ""), k), heads)))
