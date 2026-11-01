# part of: laws/ParsesExactlyTheGrammar.bend, laws/DefinesEachTableOnce.bend
import Base
import ../main.bend as T
import ./defs/AbnfGrammar.bend as D1
import ./defs/DerivationReplay.bend as D2
import ./defs/GrammarDerivations.bend as D3

# whether an expression is a blank line or a table header: no keyval
def ra.nokv.expr(ex: D3.GExpr) -> Bool:
  match ex:
    case D3.GxKeyval{_w1, _kv, _w2, _com}:
      False{}
    case _:
      True{}

# whether every line's expression is a blank line or a table header
def ra.nokv.lines(ls: List<&2, D3.GLine>) -> Bool:
  match ls:
    case []:
      True{}
    case D3.GLine{_nl, ex} <> rest:
      Bool.and(ra.nokv.expr(ex), ra.nokv.lines(rest))

# whether a derivation's expressions are blank lines and table headers only
def ra.nokv(dd: D3.Gd) -> Bool:
  match dd:
    case D3.GToml{first, rest}:
      Bool.and(ra.nokv.expr(first), ra.nokv.lines(rest))

# LAW: a document of table headers, comments and blank lines parses to its
# replay: for every derivation of the grammar whose expressions are headers
# ([table] or [[array]], each key segment bare, basic or literal, with blank
# space anywhere the grammar allows it) and blank lines with or without a
# comment, joined by LF or CRLF in any order, parse gives what the headers'
# walks give in text order from the root: the first error a walk sets, and
# the rows, sealed
law headers_parse_as_replay:
  for +d: D3.Gd
  for +ok: {D1.g.ok(d) == True{} : Bool}
  for +nk: {ra.nokv(d) == True{} : Bool}
  {T.parse(D3.g.text(d)) == D2.replay(d) : T.Doc}
