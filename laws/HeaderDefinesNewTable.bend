import Base
import ../main.bend as T
import ./defs/BareValueGrammar.bend as D1

# LAW: a [table] header whose last segment names nothing yet defines a new,
# empty table at the head of the rows it walks to, and records its path as
# defined by a header; nothing else changes
law header_defines_new_table:
  for +segs: List<&2, String>
  for +k: String
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +eo: {D1.tb.open(segs, rows) == True{} : Bool}
  for em: {T.get(D1.tb.rows(segs, rows), k) == T.Miss{} : T.Hit}
  {T.tree.walk(List.append(&2, String, segs, [k]), T.Tw{rows, T.JDef{}, [], "", "", heads, False{}}, 0)
    == T.End{D1.tb.set(segs, "", rows, T.VPair{k, T.VHead{T.tree.pre(D1.tb.join(segs, ""), k), []}}
      <> D1.tb.rows(segs, rows)), "", T.heads.by.head(T.tree.pre(D1.tb.join(segs, ""), k)) <> heads}
    : T.End}
