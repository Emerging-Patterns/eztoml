import Base
import ../main.bend as T
import ./defs/BareValueGrammar.bend as D1

# LAW: in a header, a quote right after a bare character fails the document,
# whatever follows: a segment is one bare key or one quoted key, so no bare
# part of a header's name is dropped
law header_quote_after_bare_refused:
  for bad: String
  for rows: List<&2, T.Val>
  for heads: List<&2, String>
  for here: List<&2, String>
  for parts: List<&2, String>
  for c: Char
  for cs: List<&2, Char>
  for back: T.Lex
  for qkind: T.QKind
  for stack: List<&2, T.Ctx>
  for uni: U32
  for left: U32
  for arrtab: Bool
  for lit: Bool
  for +t: String
  {String.is_empty(T.bad(T.doc.read(SCon{D1.quote_char(lit), t}, T.MScan{T.St{bad, rows,
    heads, here, parts, c <> cs, T.LHead{}, back, qkind, stack, T.HNone{}, uni, left,
    arrtab, False{}}}))) == False{} : Bool}
