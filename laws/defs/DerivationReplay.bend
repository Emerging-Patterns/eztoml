# the document a derivation's text parses to, built by replaying its
# expressions
import Base
import ../../main.bend as T
import ./AbnfGrammar.bend as D1
import ./GrammarDerivations.bend as D2

#
# The accept direction of the grammar (docs/rfc/eztoml-grammar-proofs.md,
# WP-A): for every derivation d with g.ok(d), parse of its text is replay(d),
# each expression's walk in the order the text has them, from the root, with
# each value as its reader gives it. The laws below are the pieces proved so
# far; the whole statement is in the design doc's update note until it is.

# replay: the walks a derivation's expressions run, in the order the text
# has them, as the scanner runs them. A keyval's value is read first (a
# string as the characters it stands for, a bare word as word.val reads it,
# an array's items in order, an inline table's keyvals each walked into its
# rows, which are sealed when it closes), then walked into the table the
# lines are in; a header walks from the root, and its table is the one the
# lines after it are in. Each walk starts from the error so far, so the first
# error a walk or a word sets is kept and no later walk changes anything
# (failed_walk_changes_nothing, error_stays). The rows are kept newest
# first, as the scanner keeps them, and sealed at the end, as parse seals
# them. A string is held owned, which is what own reads a span as.

# the walks' state between expressions: the error so far, the root's rows,
# the tables headers and dotted keys defined (heads), and the table the
# lines are in (here)
type RpSt is Data:
  RpSt{bad: String, rows: List<&2, T.Val>, heads: List<&2, String>, here: List<&2, String>}

# what reading a value node gives, with the error so far: a value, an
# array's items so far (newest first), or an inline table's rows so far
type RpAcc is Data:
  RaVal{val: T.Val, bad: String}
  RaItems{items: List<&2, T.Val>, bad: String}
  RaRows{rows: List<&2, T.Val>, bad: String}

# the error so far
def replay.bad(acc: RpAcc) -> String:
  match acc:
    case RaVal{_v, bd}:
      bd
    case RaItems{_i, bd}:
      bd
    case RaRows{_r, bd}:
      bd

# a bare word's value: what word.val reads it as, or, when it refuses the
# word (no word g.ok allows is refused), its reason as the error
def replay.got(gg: T.Got, +bad: String) -> RpAcc:
  match gg:
    case T.GotVal{vv}:
      RaVal{vv, bad}
    case T.GotBad{why}:
      RaVal{T.VArr{[]}, T.err.first(bad, why)}

# an item read goes on the array's items
def replay.item(got: RpAcc, acc: RpAcc) -> RpAcc:
  match got acc:
    case RaVal{vv, bd} RaItems{items, _b}:
      RaItems{vv <> items, bd}
    case _g other:
      other

# an array closed: its items in order
def replay.arr(acc: RpAcc) -> RpAcc:
  match acc:
    case RaItems{items, bd}:
      RaVal{T.VArr{List.reverse(&2, T.Val, items)}, bd}
    case other:
      other

# an inline table closed: its rows sealed, the tables its dotted keys made
# closed with it
def replay.inl(acc: RpAcc) -> RpAcc:
  match acc:
    case RaRows{rows, bd}:
      RaVal{T.VInl{T.inl.seal(rows)}, bd}
    case other:
      other

# the rows a walk ends with, and its error
def replay.end.rows(en: T.End) -> RpAcc:
  match en:
    case T.End{rows, bd, _hs}:
      RaRows{rows, bd}

# a keyval of an inline table: its value walked into the table's rows along
# the key's names, from the inline table's root
def replay.kv(+names: List<&2, String>, got: RpAcc, acc: RpAcc) -> RpAcc:
  match got acc:
    case RaVal{vv, bd} RaRows{rows, _b}:
      replay.end.rows(T.tree.walk(names, T.Tw{rows, T.JPut{vv}, [], bd, "", [], True{}}, 0))
    case _g other:
      other

# what a value node reads as, from the error so far in acc: a value for val,
# the items so far for array-values, the rows so far for
# inline-table-keyvals and keyval
def replay.go(vv: D2.GVal, +acc: RpAcc) -> RpAcc:
  match vv:
    case D2.GvString{st}:
      RaVal{T.VStr{D1.g.str.chars(st)}, replay.bad(acc)}
    case D2.GvBoolean{+cs}:
      replay.got(T.word.val(cs), replay.bad(acc))
    case D2.GvArrayEmpty{_wn}:
      RaVal{T.VArr{[]}, replay.bad(acc)}
    case D2.GvArray{vals, _wn}:
      replay.arr(replay.go(vals, RaItems{[], replay.bad(acc)}))
    case D2.GvInlineTableEmpty{_w1, _w2}:
      RaVal{T.VInl{[]}, replay.bad(acc)}
    case D2.GvInlineTable{_w1, kvs, _w2}:
      replay.inl(replay.go(kvs, RaRows{[], replay.bad(acc)}))
    case D2.GvDateTime{+cs}:
      replay.got(T.word.val(cs), replay.bad(acc))
    case D2.GvFloat{+cs}:
      replay.got(T.word.val(cs), replay.bad(acc))
    case D2.GvInteger{+cs}:
      replay.got(T.word.val(cs), replay.bad(acc))
    case D2.GArrayValues{_wa, val, _wb, rest}:
      replay.go(rest, replay.item(replay.go(val, acc), acc))
    case D2.GArrayValuesLast{_wa, val, _wb, _sep}:
      replay.item(replay.go(val, acc), acc)
    case D2.GInlineTableKeyvals{kv, _w1, _w2, rest}:
      replay.go(rest, replay.go(kv, acc))
    case D2.GInlineTableKeyvalsLast{kv}:
      replay.go(kv, acc)
    case D2.GKeyval{key, _w1, _w2, val}:
      replay.kv(D1.g.key.names(key), replay.go(val, acc), acc)

# the state after a walk from the table here
def replay.end(en: T.End, here: List<&2, String>) -> RpSt:
  match en:
    case T.End{rows, bd, heads}:
      RpSt{bd, rows, heads, here}

# a keyval's value walked into the table the lines are in, along the key's
# names after that table's
def replay.root(names: List<&2, String>, got: RpAcc, st: RpSt) -> RpSt:
  match got st:
    case RaVal{vv, bd} RpSt{_b, rows, heads, +here}:
      replay.end(T.tree.walk(List.append(&2, String, here, names), T.Tw{rows, T.JPut{vv}, [], bd, "", heads, False{}},
        T.path.len(here, 0)), here)
    case _g other:
      other

# a header's walk from the root, [table] (JDef) or [[array]] (JAot); the
# lines after it are in its table
def replay.head(job: T.Job, +names: List<&2, String>, st: RpSt) -> RpSt:
  match st:
    case RpSt{bd, rows, heads, _here}:
      replay.end(T.tree.walk(names, T.Tw{rows, job, [], bd, "", heads, False{}}, 0), names)

# the error so far
def replay.st.bad(st: RpSt) -> String:
  match st:
    case RpSt{bd, _r, _h, _e}:
      bd

# an expression's walks
def replay.expr(ex: D2.GExpr, +st: RpSt) -> RpSt:
  match ex:
    case D2.GxBlank{_w1, _com}:
      st
    case D2.GxKeyval{_w1, D2.GKeyval{key, _a, _b, val}, _w2, _com}:
      replay.root(D1.g.key.names(key), replay.go(val, RaVal{T.VArr{[]}, replay.st.bad(st)}), st)
    case D2.GxKeyval{_w1, _kv, _w2, _com}:
      st
    case D2.GxTable{_w1, D2.GStdTable{_a, key, _b}, _w2, _com}:
      replay.head(T.JDef{}, D1.g.key.names(key), st)
    case D2.GxTable{_w1, D2.GArrayTable{_a, key, _b}, _w2, _com}:
      replay.head(T.JAot{}, D1.g.key.names(key), st)

# each line's expression, in order
def replay.lines(ls: List<&2, D2.GLine>, st: RpSt) -> RpSt:
  match ls:
    case []:
      st
    case D2.GLine{_nl, ex} <> rest:
      replay.lines(rest, replay.expr(ex, st))

# the document: the first error, and the rows sealed
def replay.doc(st: RpSt) -> T.Doc:
  match st:
    case RpSt{bd, rows, _h, _e}:
      T.Doc{bd, T.rows.seal(rows)}

# the document a derivation's text parses to: its expressions' walks, in
# order, from no error, no rows, no definitions and the root
def replay(dd: D2.Gd) -> T.Doc:
  match dd:
    case D2.GToml{first, rest}:
      replay.doc(replay.lines(rest, replay.expr(first, RpSt{"", [], [], []})))
