import Base
import ../main.bend as T
import ./defs/BareValueGrammar.bend as D1

# LAW: a [table] header whose last segment names a table only made on the way
# to another defines it where it is, under the header's path, and records the
# path as defined by a header; nothing else changes
law header_defines_implicit_table:
  for +segs: List<&2, String>
  for +k: String
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for p: String
  for +sub: List<&2, T.Val>
  for +eo: {D1.tb.open(segs, rows) == True{} : Bool}
  for ef: {T.get(D1.tb.rows(segs, rows), k) == T.Found{T.VHead{p, sub}} : T.Hit}
  for eh: {T.heads.has(heads, T.tree.pre(D1.tb.join(segs, ""), k)) == False{} : Bool}
  {T.tree.walk(List.append(&2, String, segs, [k]), T.Tw{rows, T.JDef{}, [], "", "", heads, False{}}, 0)
    == T.End{D1.tb.set(segs, "", rows, T.rows.repl(D1.tb.rows(segs, rows), k,
      T.VHead{T.tree.pre(D1.tb.join(segs, ""), k), sub})), "",
      T.heads.by.head(T.tree.pre(D1.tb.join(segs, ""), k)) <> heads} : T.End}
