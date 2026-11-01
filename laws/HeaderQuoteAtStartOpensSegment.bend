# part of: laws/KeyNameIsItsCharacters.bend, laws/ParsesExactlyTheGrammar.bend
import Base
import ../main.bend as T
import ./defs/BareValueGrammar.bend as D1

# the kind of key a quote starts
def quote_kind(lit: Bool) -> T.QKind:
  match lit:
    case True{}:
      T.QLit{}
    case False{}:
      T.QBasic{}

# LAW: a quote right after a header's opening bracket starts a quoted segment
law header_quote_at_start_opens_segment:
  for bad: String
  for rows: List<&2, T.Val>
  for heads: List<&2, String>
  for here: List<&2, String>
  for back: T.Lex
  for qkind: T.QKind
  for stack: List<&2, T.Ctx>
  for uni: U32
  for left: U32
  for arrtab: Bool
  for lit: Bool
  {T.doc.scan(T.St{bad, rows, heads, here, [], [], T.LHead{}, back, qkind, stack,
    T.HNone{}, uni, left, arrtab, False{}}, D1.quote_char(lit))
    == T.MScan{T.St{bad, rows, heads, here, [], [], T.LHeadQ{}, back, quote_kind(lit),
    stack, T.HNone{}, uni, left, arrtab, False{}}} : T.Mode}
