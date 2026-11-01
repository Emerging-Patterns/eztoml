import Base
import ../main.bend as T

# LAW: once the scanner has an error, the rest of the text keeps it and the
# rows: from every scanner state with an error, whatever its other fields,
# every text reads to a document with that error and the state's rows,
# sealed. A walk the definition rules refuse (a key or a table defined twice)
# sets the error and the scanner reads on, so the error it sets is the
# document's, and the rows are the ones the walk found
law error_stays:
  for +bad: String
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +here: List<&2, String>
  for +parts: List<&2, String>
  for +buf: List<&2, Char>
  for +lex: T.Lex
  for +back: T.Lex
  for +qkind: T.QKind
  for +stack: List<&2, T.Ctx>
  for +hold: T.Hold
  for +uni: U32
  for +left: U32
  for +arrtab: Bool
  for +lead: Bool
  for e: {String.is_empty(bad) == False{} : Bool}
  for +t: String
  {T.doc.read(t, T.MScan{T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab,
    lead}}) == T.Doc{bad, T.rows.seal(rows)} : T.Doc}
