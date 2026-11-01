# For every text `t` shorter than 2^32 characters that matches the grammar of
# laws/ParsesExactlyTheGrammar.bend, `bad(parse(t))` is `""` exactly when each key, table and array
# of tables is defined once; no `[table]` header names a table that dotted
# keys defined or an earlier header named, or an array of tables; no dotted
# key adds to a table a header named (a table a header only passes through on
# its way stays open to dotted keys), or to an array of tables; no `[[array]]`
# header names a table or a static array; and inline tables and arrays are not
# extended after they are written. Each element of an array of tables is its
# own scope for these rules
#
# pending: the laws here prove part of this, not all of it.
#
# also rests on: laws/ErrorStays.bend, laws/HeadersParseAsReplay.bend,
# laws/TextReadsAsReplay.bend
import Base
import ../main.bend as T
import ./defs/BareValueGrammar.bend as D1

# The table-definition rules (laws/DefinesEachTableOnce.bend), stated over the walk that follows
# a key path through the tables. A walk step either enters the table a key
# names or records why it cannot.

# the error a walk step holds, "" while it has none
def tw_bad(tw: T.Tw) -> String:
  match tw:
    case T.Tw{_vs, _job, _stack, bad, _pre, _heads, _inl}:
      bad

# the tables a finished walk has recorded as defined
def end_heads(end: T.End) -> List<&2, String>:
  match end:
    case T.End{_vs, _bad, heads}:
      heads

# LAW: a dotted key cannot add to a table a header defined: the segment of
# the key that reaches it is refused
law dotted_key_refused_in_header_table:
  for path: String
  for rows: List<&2, T.Val>
  for +name: String
  for vs: List<&2, T.Val>
  for val: T.Val
  for stack: List<&2, T.Fr>
  for +pre: String
  for heads: List<&2, String>
  for inl: Bool
  for e: {T.heads.head(heads, T.tree.pre(pre, name)) == True{} : Bool}
  {String.is_empty(tw_bad(T.tree.sub.look(T.KHead{path, rows}, name, vs,
    T.JPut{val}, stack, pre, heads, inl, True{}))) == False{} : Bool}

# LAW: a dotted key goes on into a table no header defined, such as one other
# dotted keys defined
law dotted_key_enters_other_table:
  for path: String
  for rows: List<&2, T.Val>
  for +name: String
  for vs: List<&2, T.Val>
  for val: T.Val
  for stack: List<&2, T.Fr>
  for +pre: String
  for heads: List<&2, String>
  for inl: Bool
  for e: {T.heads.head(heads, T.tree.pre(pre, name)) == False{} : Bool}
  {tw_bad(T.tree.sub.look(T.KHead{path, rows}, name, vs, T.JPut{val}, stack,
    pre, heads, inl, True{})) == "" : String}

# LAW: a dotted key cannot add to an array of tables
law dotted_key_refused_in_array_of_tables:
  for path: String
  for elems: List<&2, T.Val>
  for name: String
  for vs: List<&2, T.Val>
  for val: T.Val
  for stack: List<&2, T.Fr>
  for pre: String
  for heads: List<&2, String>
  for inl: Bool
  {String.is_empty(tw_bad(T.tree.sub.look(T.KAots{path, elems}, name, vs,
    T.JPut{val}, stack, pre, heads, inl, True{}))) == False{} : Bool}

# LAW: a header goes on through every table on its path, whoever defined it
law header_enters_any_table:
  for path: String
  for rows: List<&2, T.Val>
  for name: String
  for vs: List<&2, T.Val>
  for arr: Bool
  for stack: List<&2, T.Fr>
  for pre: String
  for heads: List<&2, String>
  for inl: Bool
  for mark: Bool
  {tw_bad(T.tree.sub.look(T.KHead{path, rows}, name, vs, D1.header_job(arr),
    stack, pre, heads, inl, mark)) == "" : String}

# LAW: a [table] header that makes a new table records it as defined by a
# header
law header_records_new_table:
  for name: String
  for vs: List<&2, T.Val>
  for stack: List<&2, T.Fr>
  for bad: String
  for +path: String
  for heads: List<&2, String>
  {T.heads.head(end_heads(T.tree.leaf.def.hit(T.KMiss{}, name, vs, stack, bad,
    path, heads)), path) == True{} : Bool}

# LAW: a [table] header that defines a table only made on the way to another
# records it as defined by a header
law header_records_implicit_table:
  for p: String
  for rows: List<&2, T.Val>
  for name: String
  for vs: List<&2, T.Val>
  for stack: List<&2, T.Fr>
  for bad: String
  for +path: String
  for +heads: List<&2, String>
  for e: {T.heads.has(heads, path) == False{} : Bool}
  {T.heads.head(end_heads(T.tree.leaf.def.hit(T.KHead{p, rows}, name, vs,
    stack, bad, path, heads)), path) == True{} : Bool}

# LAW: a new element of an array of tables starts with no table under the
# array defined, so each element is its own scope for defining tables
law new_element_forgets_tables_under_it:
  for p: String
  for elems: List<&2, T.Val>
  for name: String
  for vs: List<&2, T.Val>
  for stack: List<&2, T.Fr>
  for bad: String
  for +path: String
  for +heads: List<&2, String>
  for rest: String
  {T.heads.has(end_heads(T.tree.leaf.aot.hit(T.KAots{p, elems}, name, vs, stack,
    bad, path, heads)), String.append(String.append(path, "."), rest))
    == False{} : Bool}

# LAW: a new element of an array of tables leaves every table not under the
# array defined as it was
law new_element_keeps_other_tables:
  for p: String
  for elems: List<&2, T.Val>
  for name: String
  for vs: List<&2, T.Val>
  for stack: List<&2, T.Fr>
  for bad: String
  for +path: String
  for +heads: List<&2, String>
  for +q: String
  for e: {String.starts_with(q, String.append(path, ".")) == False{} : Bool}
  {T.heads.has(end_heads(T.tree.leaf.aot.hit(T.KAots{p, elems}, name, vs, stack,
    bad, path, heads)), q) == T.heads.has(heads, q) : Bool}

# whether no pair of the rows holds a table a later key could go on in
def holds_no_open_table(rows: List<&2, T.Val>) -> Bool:
  match rows:
    case []:
      True{}
    case T.VPair{_nn, T.VHead{_pp, _rr}} <> _tt:
      False{}
    case _ <> tt:
      holds_no_open_table(tt)

# LAW: an inline table, once closed, holds no table a later key could go on
# in: the tables its dotted keys made close with it
law closed_inline_table_holds_no_open_table:
  for rows: List<&2, T.Val>
  {holds_no_open_table(T.inl.seal(rows)) == True{} : Bool}

# LAW: no key goes on in an inline table: a dotted key or a header that
# reaches one is refused
law inline_table_refuses_keys:
  for name: String
  for vs: List<&2, T.Val>
  for job: T.Job
  for stack: List<&2, T.Fr>
  for pre: String
  for heads: List<&2, String>
  for inl: Bool
  for mark: Bool
  {String.is_empty(tw_bad(T.tree.sub.look(T.KInl{}, name, vs, job, stack, pre,
    heads, inl, mark))) == False{} : Bool}

# whether a lookup missed
def is_miss(hh: T.Hit) -> Bool:
  match hh:
    case T.Miss{}:
      True{}
    case T.Found{_v}:
      False{}

# whether a [table] header may define the table a name holds: a name not yet
# there, or a table no header or dotted key defined (one made on the way to
# another)
def hdr.ok(hh: T.Hit, heads: List<&2, String>, +path: String) -> Bool:
  match hh:
    case T.Miss{}:
      True{}
    case T.Found{T.VHead{_p, _rows}}:
      Bool.not(T.heads.has(heads, path))
    case _:
      False{}

# whether an [[array]] header may add an element for a name: a name not yet
# there, or an array of tables
def aot.ok(hh: T.Hit) -> Bool:
  match hh:
    case T.Miss{}:
      True{}
    case T.Found{T.VAots{_p, _elems}}:
      True{}
    case _:
      False{}

# LAW: a value put along a path the walk goes on through is refused exactly
# when the table at its end already holds the name: a key is defined once
law walk_put_refused_exactly:
  for +here: List<&2, String>
  for +k: String
  for +v: T.Val
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +skip: U32
  for +inl: Bool
  for eo: {D1.tb.open(here, rows) == True{} : Bool}
  for ec: {D1.counts.down(here, skip) == True{} : Bool}
  {String.is_empty(D1.end_bad(T.tree.walk(List.append(&2, String, here, [k]),
    T.Tw{rows, T.JPut{v}, [], "", "", heads, inl}, skip)))
    == is_miss(T.get(D1.tb.rows(here, rows), k)) : Bool}

# LAW: a [table] header is refused exactly when its last segment names
# something other than a table, or a table a header or dotted keys defined
law header_refused_exactly:
  for +segs: List<&2, String>
  for +k: String
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for eo: {D1.tb.open(segs, rows) == True{} : Bool}
  {String.is_empty(D1.end_bad(T.tree.walk(List.append(&2, String, segs, [k]),
    T.Tw{rows, T.JDef{}, [], "", "", heads, False{}}, 0)))
    == hdr.ok(T.get(D1.tb.rows(segs, rows), k), heads, T.tree.pre(D1.tb.join(segs, ""), k)) : Bool}

# LAW: an [[array]] header is refused exactly when its last segment names
# something other than an array of tables: a table, an inline table, a
# static array or any other value
law aot_header_refused_exactly:
  for +segs: List<&2, String>
  for +k: String
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for eo: {D1.tb.open(segs, rows) == True{} : Bool}
  {String.is_empty(D1.end_bad(T.tree.walk(List.append(&2, String, segs, [k]),
    T.Tw{rows, T.JAot{}, [], "", "", heads, False{}}, 0)))
    == aot.ok(T.get(D1.tb.rows(segs, rows), k)) : Bool}

# LAW: a walk that starts with an error keeps it and changes nothing: once a
# key or header is refused, no later one in the same text clears the error
# or touches the tables
law failed_walk_changes_nothing:
  for path: List<&2, String>
  for +rows: List<&2, T.Val>
  for +job: T.Job
  for +bad: String
  for +pre: String
  for +heads: List<&2, String>
  for +inl: Bool
  for +skip: U32
  for +eb: {String.is_empty(bad) == False{} : Bool}
  {T.tree.walk(path, T.Tw{rows, job, [], bad, pre, heads, inl}, skip) == T.End{rows, bad, heads}
    : T.End}
