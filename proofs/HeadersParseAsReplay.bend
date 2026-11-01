# proofs of laws/HeadersParseAsReplay.bend
import Base
import ../main.bend as T
import ../src/eq.bend as Eq
import ../laws/HeadersParseAsReplay.bend as Laws
import ../laws/defs/AbnfGrammar.bend as D1
import ../laws/defs/AbnfWhitespace.bend as D2
import ../laws/defs/DerivationReplay.bend as D3
import ../laws/defs/GrammarDerivations.bend as D4
import ./lemmas/ExpressionLineReplay.bend as M1

# a blank line or a header starts with no byte-order mark, before a text
# that starts with none
def ap.nb.expr(
  +ex: D4.GExpr,
  +xx: String,
  +hx: {D1.g.ok.expr(ex) == True{} : Bool},
  +nx: {Laws.ra.nokv.expr(ex) == True{} : Bool},
  +ht: {M1.ap.nobom(xx) == True{} : Bool}
) -> {M1.ap.nobom(D4.g.expr.text(ex, xx)) == True{} : Bool}:
  match ex:
    case D4.GxBlank{+w1, +com}:
      M1.ap.nb.ws(w1, D4.g.com.text(com, xx), Eq.and.left(D2.abnf.ws(w1), D1.g.ok.com(com), hx), M1.ap.nb.com(com, xx,
        ht))
    case D4.GxKeyval{_w1, _kv, _w2, _com}:
      Eq.bit.absurd(&2, {M1.ap.nobom(D4.g.expr.text(D4.GxKeyval{_w1, _kv, _w2, _com}, xx)) == True{} : Bool}, nx)
    case D4.GxTable{+w1, +tb, +w2, +com}:
      M1.ap.nb.ws(w1, D4.g.table.text(tb, String.append(w2, D4.g.com.text(com, xx))), Eq.and.left(D2.abnf.ws(w1),
        Bool.and(D1.g.ok.table(tb), Bool.and(D2.abnf.ws(w2), D1.g.ok.com(com))), hx), M1.ap.nb.tb(tb,
        String.append(w2, D4.g.com.text(com, xx))))

def Laws.headers_parse_as_replay(d, ok, nk):
  match d:
    case D4.GToml{+first, +rest}:
      Equal.trans(T.Doc, T.doc.read(D4.g.expr.text(first, D4.g.lines.text(rest, "")), T.MScan{T.st.start()}),
        T.doc.read(D4.g.expr.text(first, D4.g.lines.text(rest, "")), T.MScan{M1.ap.s0()}),
        D3.replay(D4.GToml{first, rest}), M1.ap.lead(D4.g.expr.text(first, D4.g.lines.text(rest, "")),
        ap.nb.expr(first, D4.g.lines.text(rest, ""), Eq.and.left(D1.g.ok.expr(first), D1.g.ok.lines(rest), ok),
        Eq.and.left(Laws.ra.nokv.expr(first), Laws.ra.nokv.lines(rest), nk), M1.ap.nb.lines(rest,
        Eq.and.right(D1.g.ok.expr(first), D1.g.ok.lines(rest), ok)))), M1.ap.go(rest, first, [], [], [], T.LTop{},
        T.QBasic{}, 0, 0, Eq.and.left(D1.g.ok.expr(first), D1.g.ok.lines(rest), ok),
        Eq.and.right(D1.g.ok.expr(first), D1.g.ok.lines(rest), ok), Eq.and.left(Laws.ra.nokv.expr(first),
        Laws.ra.nokv.lines(rest), nk), Eq.and.right(Laws.ra.nokv.expr(first), Laws.ra.nokv.lines(rest), nk)))
