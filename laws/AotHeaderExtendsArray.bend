import Base
import ../main.bend as T
import ./defs/BareValueGrammar.bend as D1

# LAW: an [[array]] header whose last segment names an array of tables adds
# a new empty element in front of its elements (newest first), and forgets
# every table under the array defined, so the element is its own scope;
# nothing else changes
law aot_header_extends_array:
  for +segs: List<&2, String>
  for +k: String
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for p: String
  for +elems: List<&2, T.Val>
  for +eo: {D1.tb.open(segs, rows) == True{} : Bool}
  for ef: {T.get(D1.tb.rows(segs, rows), k) == T.Found{T.VAots{p, elems}} : T.Hit}
  {T.tree.walk(List.append(&2, String, segs, [k]), T.Tw{rows, T.JAot{}, [], "", "", heads, False{}}, 0)
    == T.End{D1.tb.set(segs, "", rows, T.rows.repl(D1.tb.rows(segs, rows), k,
      T.VAots{T.tree.pre(D1.tb.join(segs, ""), k), T.VAot{T.tree.pre(D1.tb.join(segs, ""), k), []}
        <> elems})), "",
      T.heads.drop(heads, String.append(T.tree.pre(D1.tb.join(segs, ""), k), "."))} : T.End}
