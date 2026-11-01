import Base
import ../main.bend as T
import ./defs/BareValueGrammar.bend as D1

# LAW: an [[array]] header whose last segment names nothing yet starts an
# array of tables of one empty element at the head of the rows it walks to;
# nothing else changes, and no definition is recorded
law aot_header_starts_array:
  for +segs: List<&2, String>
  for +k: String
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +eo: {D1.tb.open(segs, rows) == True{} : Bool}
  for em: {T.get(D1.tb.rows(segs, rows), k) == T.Miss{} : T.Hit}
  {T.tree.walk(List.append(&2, String, segs, [k]), T.Tw{rows, T.JAot{}, [], "", "", heads, False{}}, 0)
    == T.End{D1.tb.set(segs, "", rows, T.VPair{k, T.VAots{T.tree.pre(D1.tb.join(segs, ""), k),
      [T.VAot{T.tree.pre(D1.tb.join(segs, ""), k), []}]}} <> D1.tb.rows(segs, rows)), "", heads} : T.End}
