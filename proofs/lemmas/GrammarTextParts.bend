# the text a grammar derivation spells, part by part
import Base
import ../../src/eq.bend as Eq
import ../../laws/GValTextTail.bend as L1
import ../../laws/defs/GrammarDerivations.bend as D1
import ../../laws/defs/KeySegmentSpelling.bend as D2

# what the text lemmas claim: a part written before the tail is the part
# written before nothing, then the tail
def gt.T(fa: String, fb: String, tail: String) -> Type:
  {fa == String.append(fb, tail) : String}

# f(x, g(y, t)) is f(x, g(y, "")) then t, when f and g each write their text
# before the tail they are given: pre is f's text alone, and gt and g0 are
# g's before t and before nothing
def gt.step(
  +fa: String,
  +fb: String,
  +pre: String,
  +gt: String,
  +g0: String,
  +tail: String,
  e1: {fa == String.append(pre, gt) : String},
  e2: {gt == String.append(g0, tail) : String},
  e3: {fb == String.append(pre, g0) : String}
) -> gt.T(fa, fb, tail):
  Equal.trans(String, fa, String.append(pre, gt), String.append(fb, tail), e1,
    Equal.trans(String, String.append(pre, gt), String.append(pre, String.append(g0, tail)),
      String.append(fb, tail),
      Equal.cong(String, String, zz => String.append(pre, zz), gt, String.append(g0, tail), e2),
      Equal.trans(String, String.append(pre, String.append(g0, tail)), String.append(String.append(pre, g0), tail),
        String.append(fb, tail),
        Equal.sym(String, String.append(String.append(pre, g0), tail), String.append(pre, String.append(g0, tail)),
          Eq.append_assoc(pre, g0, tail)),
        Equal.cong(String, String, zz => String.append(zz, tail), String.append(pre, g0), fb,
          Equal.sym(String, fb, String.append(pre, g0), e3)))))

# a text in front of a part
def gt.app(
  +ss: String,
  +xa: String,
  +xb: String,
  +tail: String,
  ee: gt.T(xa, xb, tail)
) -> gt.T(String.append(ss, xa), String.append(ss, xb), tail):
  gt.step(String.append(ss, xa), String.append(ss, xb), ss, xa, xb, tail, {==}, ee, {==})

# a character in front of a part
def gt.cons(
  +cc: Char,
  +xa: String,
  +xb: String,
  +tail: String,
  ee: gt.T(xa, xb, tail)
) -> gt.T(SCon{cc, xa}, SCon{cc, xb}, tail):
  Equal.cong(String, String, zz => SCon{cc, zz}, xa, String.append(xb, tail), ee)

# a text written with nothing after it
def gt.nil(+ss: String, +tail: String) -> gt.T(String.append(ss, tail), String.append(ss, ""), tail):
  Equal.cong(String, String, zz => String.append(zz, tail), ss, String.append(ss, ""),
    Equal.sym(String, String.append(ss, ""), ss, Eq.append_nil(ss)))

# a basic string's piece
def gt.pc(pp: D2.KPiece, +tail: String) -> gt.T(D2.k3.pc.text(pp, tail), D2.k3.pc.text(pp, ""), tail):
  match pp:
    case D2.KpChar{_c}:
      {==}
    case D2.KpEsc{_m}:
      {==}
    case D2.KpU4{_d, _c, _b, _a}:
      {==}
    case D2.KpU8{_h, _g, _f, _e, _d, _c, _b, _a}:
      {==}

# a basic string's pieces
def gt.pcs(
  ps: List<&2, D2.KPiece>,
  +tail: String
) -> gt.T(D2.k3.pcs.text(ps, tail), D2.k3.pcs.text(ps, ""), tail):
  match ps:
    case []:
      {==}
    case +pp <> +rest:
      gt.step(D2.k3.pc.text(pp, D2.k3.pcs.text(rest, tail)), D2.k3.pc.text(pp, D2.k3.pcs.text(rest, "")),
        D2.k3.pc.text(pp, ""), D2.k3.pcs.text(rest, tail), D2.k3.pcs.text(rest, ""), tail,
        gt.pc(pp, D2.k3.pcs.text(rest, tail)), gt.pcs(rest, tail), gt.pc(pp, D2.k3.pcs.text(rest, "")))

# pieces before a closing character
def gt.pcs.close(
  +ps: List<&2, D2.KPiece>,
  +cc: Char,
  +tail: String
) -> gt.T(D2.k3.pcs.text(ps, SCon{cc, tail}), D2.k3.pcs.text(ps, SCon{cc, ""}), tail):
  gt.step(D2.k3.pcs.text(ps, SCon{cc, tail}), D2.k3.pcs.text(ps, SCon{cc, ""}), D2.k3.pcs.text(ps, ""),
    SCon{cc, tail}, SCon{cc, ""}, tail, gt.pcs(ps, SCon{cc, tail}), {==}, gt.pcs(ps, SCon{cc, ""}))

# a simple-key
def gt.seg(sg: D2.KSeg, +tail: String) -> gt.T(D2.k3.seg.text(sg, tail), D2.k3.seg.text(sg, ""), tail):
  match sg:
    case D2.KsBare{+name}:
      gt.nil(name, tail)
    case D2.KsBasic{+pl}:
      gt.cons('"', D2.k3.pcs.text(pl, SCon{'"', tail}), D2.k3.pcs.text(pl, SCon{'"', ""}), tail,
        gt.pcs.close(pl, '"', tail))
    case D2.KsLit{+name}:
      gt.cons('\'', String.append(name, SCon{'\'', tail}), String.append(name, SCon{'\'', ""}), tail,
        gt.app(name, SCon{'\'', tail}, SCon{'\'', ""}, tail, {==}))

# a key's dot-seps and simple-keys after its first
def gt.dots(
  ds: List<&2, D1.GDotSep>,
  +tail: String
) -> gt.T(D1.g.dots.text(ds, tail), D1.g.dots.text(ds, ""), tail):
  match ds:
    case []:
      {==}
    case D1.GDotSep{+w1, +w2, +sk} <> +rest:
      +xa = D2.k3.seg.text(sk, D1.g.dots.text(rest, tail))
      +xb = D2.k3.seg.text(sk, D1.g.dots.text(rest, ""))
      gt.app(w1, SCon{'.', String.append(w2, xa)}, SCon{'.', String.append(w2, xb)}, tail,
        gt.cons('.', String.append(w2, xa), String.append(w2, xb), tail,
          gt.app(w2, xa, xb, tail,
            gt.step(xa, xb, D2.k3.seg.text(sk, ""), D1.g.dots.text(rest, tail), D1.g.dots.text(rest, ""), tail,
              gt.seg(sk, D1.g.dots.text(rest, tail)), gt.dots(rest, tail), gt.seg(sk, D1.g.dots.text(rest, ""))))))

# a key
def gt.key(kk: D1.GKey, +tail: String) -> gt.T(D1.g.key.text(kk, tail), D1.g.key.text(kk, ""), tail):
  match kk:
    case D1.GSimpleKey{sk}:
      gt.seg(sk, tail)
    case D1.GDottedKey{+sk, +more}:
      gt.step(D2.k3.seg.text(sk, D1.g.dots.text(more, tail)), D2.k3.seg.text(sk, D1.g.dots.text(more, "")),
        D2.k3.seg.text(sk, ""), D1.g.dots.text(more, tail), D1.g.dots.text(more, ""), tail,
        gt.seg(sk, D1.g.dots.text(more, tail)), gt.dots(more, tail), gt.seg(sk, D1.g.dots.text(more, "")))

# a comment, if there is one
def gt.com(cm: D1.GCom, +tail: String) -> gt.T(D1.g.com.text(cm, tail), D1.g.com.text(cm, ""), tail):
  match cm:
    case D1.GcNone{}:
      {==}
    case D1.GcSome{+body}:
      gt.cons('#', String.append(body, tail), String.append(body, ""), tail, gt.nil(body, tail))

# ws-comment-newline
def gt.wcn(
  ws: List<&2, D1.GWcn>,
  +tail: String
) -> gt.T(D1.g.wcn.text(ws, tail), D1.g.wcn.text(ws, ""), tail):
  match ws:
    case []:
      {==}
    case D1.GwWschar{+cc} <> +rest:
      gt.cons(cc, D1.g.wcn.text(rest, tail), D1.g.wcn.text(rest, ""), tail, gt.wcn(rest, tail))
    case D1.GwNewline{+com, +nl} <> +rest:
      +xa = String.append(nl, D1.g.wcn.text(rest, tail))
      +xb = String.append(nl, D1.g.wcn.text(rest, ""))
      gt.step(D1.g.com.text(com, xa), D1.g.com.text(com, xb), D1.g.com.text(com, ""), xa, xb, tail,
        gt.com(com, xa), gt.app(nl, D1.g.wcn.text(rest, tail), D1.g.wcn.text(rest, ""), tail, gt.wcn(rest, tail)),
        gt.com(com, xb))

# ws-comment-newline before a text
def gt.wcn.before(
  +ws: List<&2, D1.GWcn>,
  +xa: String,
  +xb: String,
  +tail: String,
  ee: gt.T(xa, xb, tail)
) -> gt.T(D1.g.wcn.text(ws, xa), D1.g.wcn.text(ws, xb), tail):
  gt.step(D1.g.wcn.text(ws, xa), D1.g.wcn.text(ws, xb), D1.g.wcn.text(ws, ""), xa, xb, tail,
    gt.wcn(ws, xa), ee, gt.wcn(ws, xb))

# one or two quotes
def gt.quotes(
  two: Bool,
  +qc: Char,
  +tail: String
) -> gt.T(D1.g.quotes.text(two, qc, tail), D1.g.quotes.text(two, qc, ""), tail):
  match two:
    case True{}:
      {==}
    case False{}:
      {==}

# a multi-line basic body
def gt.mlb(
  ps: List<&2, D1.GMlb>,
  +tail: String
) -> gt.T(D1.g.mlb.text(ps, tail), D1.g.mlb.text(ps, ""), tail):
  match ps:
    case []:
      {==}
    case D1.GmChar{+kp} <> +rest:
      gt.step(D2.k3.pc.text(kp, D1.g.mlb.text(rest, tail)), D2.k3.pc.text(kp, D1.g.mlb.text(rest, "")),
        D2.k3.pc.text(kp, ""), D1.g.mlb.text(rest, tail), D1.g.mlb.text(rest, ""), tail,
        gt.pc(kp, D1.g.mlb.text(rest, tail)), gt.mlb(rest, tail), gt.pc(kp, D1.g.mlb.text(rest, "")))
    case D1.GmNewline{+nl} <> +rest:
      gt.app(nl, D1.g.mlb.text(rest, tail), D1.g.mlb.text(rest, ""), tail, gt.mlb(rest, tail))
    case D1.GmEscapedNl{+w1, +nl, +more} <> +rest:
      +ma = String.append(more, D1.g.mlb.text(rest, tail))
      +mb = String.append(more, D1.g.mlb.text(rest, ""))
      gt.cons('\\', String.append(w1, String.append(nl, ma)), String.append(w1, String.append(nl, mb)), tail,
        gt.app(w1, String.append(nl, ma), String.append(nl, mb), tail,
          gt.app(nl, ma, mb, tail,
            gt.app(more, D1.g.mlb.text(rest, tail), D1.g.mlb.text(rest, ""), tail, gt.mlb(rest, tail)))))
    case D1.GmQuotes{+two} <> +rest:
      gt.step(D1.g.quotes.text(two, '"', D1.g.mlb.text(rest, tail)),
        D1.g.quotes.text(two, '"', D1.g.mlb.text(rest, "")), D1.g.quotes.text(two, '"', ""),
        D1.g.mlb.text(rest, tail), D1.g.mlb.text(rest, ""), tail,
        gt.quotes(two, '"', D1.g.mlb.text(rest, tail)), gt.mlb(rest, tail),
        gt.quotes(two, '"', D1.g.mlb.text(rest, "")))

# a multi-line literal body
def gt.mll(
  ps: List<&2, D1.GMll>,
  +tail: String
) -> gt.T(D1.g.mll.text(ps, tail), D1.g.mll.text(ps, ""), tail):
  match ps:
    case []:
      {==}
    case D1.GlChar{+cc} <> +rest:
      gt.cons(cc, D1.g.mll.text(rest, tail), D1.g.mll.text(rest, ""), tail, gt.mll(rest, tail))
    case D1.GlNewline{+nl} <> +rest:
      gt.app(nl, D1.g.mll.text(rest, tail), D1.g.mll.text(rest, ""), tail, gt.mll(rest, tail))
    case D1.GlQuotes{+two} <> +rest:
      gt.step(D1.g.quotes.text(two, '\'', D1.g.mll.text(rest, tail)),
        D1.g.quotes.text(two, '\'', D1.g.mll.text(rest, "")), D1.g.quotes.text(two, '\'', ""),
        D1.g.mll.text(rest, tail), D1.g.mll.text(rest, ""), tail,
        gt.quotes(two, '\'', D1.g.mll.text(rest, tail)), gt.mll(rest, tail),
        gt.quotes(two, '\'', D1.g.mll.text(rest, "")))

# three delimiter characters and a tail
def gt.delim(+qc: Char, +tail: String) -> String:
  SCon{qc, SCon{qc, SCon{qc, tail}}}

# a string, with its delimiters
def gt.str(st: D1.GString, +tail: String) -> gt.T(D1.g.str.text(st, tail), D1.g.str.text(st, ""), tail):
  match st:
    case D1.GsMlBasic{+nl, +body}:
      +ba = D1.g.mlb.text(body, gt.delim('"', tail))
      +bb = D1.g.mlb.text(body, gt.delim('"', ""))
      gt.cons('"', SCon{'"', SCon{'"', String.append(nl, ba)}}, SCon{'"', SCon{'"', String.append(nl, bb)}}, tail,
        gt.cons('"', SCon{'"', String.append(nl, ba)}, SCon{'"', String.append(nl, bb)}, tail,
          gt.cons('"', String.append(nl, ba), String.append(nl, bb), tail,
            gt.app(nl, ba, bb, tail,
              gt.step(ba, bb, D1.g.mlb.text(body, ""), gt.delim('"', tail), gt.delim('"', ""), tail,
                gt.mlb(body, gt.delim('"', tail)), {==}, gt.mlb(body, gt.delim('"', "")))))))
    case D1.GsBasic{+pl}:
      gt.cons('"', D2.k3.pcs.text(pl, SCon{'"', tail}), D2.k3.pcs.text(pl, SCon{'"', ""}), tail,
        gt.pcs.close(pl, '"', tail))
    case D1.GsMlLiteral{+nl, +body}:
      +ba = D1.g.mll.text(body, gt.delim('\'', tail))
      +bb = D1.g.mll.text(body, gt.delim('\'', ""))
      gt.cons('\'', SCon{'\'', SCon{'\'', String.append(nl, ba)}}, SCon{'\'', SCon{'\'', String.append(nl, bb)}},
        tail,
        gt.cons('\'', SCon{'\'', String.append(nl, ba)}, SCon{'\'', String.append(nl, bb)}, tail,
          gt.cons('\'', String.append(nl, ba), String.append(nl, bb), tail,
            gt.app(nl, ba, bb, tail,
              gt.step(ba, bb, D1.g.mll.text(body, ""), gt.delim('\'', tail), gt.delim('\'', ""), tail,
                gt.mll(body, gt.delim('\'', tail)), {==}, gt.mll(body, gt.delim('\'', "")))))))
    case D1.GsLiteral{+text}:
      gt.cons('\'', String.append(text, SCon{'\'', tail}), String.append(text, SCon{'\'', ""}), tail,
        gt.app(text, SCon{'\'', tail}, SCon{'\'', ""}, tail, {==}))

# [ array-sep ]
def gt.sep(sep: Bool, +tail: String) -> gt.T(D1.g.sep.text(sep, tail), D1.g.sep.text(sep, ""), tail):
  match sep:
    case True{}:
      {==}
    case False{}:
      {==}

# a value before a text
def gt.val.before(
  +vv: D1.GVal,
  +xa: String,
  +xb: String,
  +tail: String,
  ee: gt.T(xa, xb, tail),
  ea: gt.T(D1.g.val.text(vv, xa), D1.g.val.text(vv, ""), xa),
  eb: gt.T(D1.g.val.text(vv, xb), D1.g.val.text(vv, ""), xb)
) -> gt.T(D1.g.val.text(vv, xa), D1.g.val.text(vv, xb), tail):
  gt.step(D1.g.val.text(vv, xa), D1.g.val.text(vv, xb), D1.g.val.text(vv, ""), xa, xb, tail, ea, ee, eb)

def L1.g_val_text_tail(vv, tail):
  match vv:
    case D1.GvString{st}:
      gt.str(st, tail)
    case D1.GvBoolean{+cs}:
      gt.nil(String.from_list(cs), tail)
    case D1.GvArrayEmpty{+wn}:
      gt.cons('[', D1.g.wcn.text(wn, SCon{']', tail}), D1.g.wcn.text(wn, SCon{']', ""}), tail,
        gt.wcn.before(wn, SCon{']', tail}, SCon{']', ""}, tail, {==}))
    case D1.GvArray{+vals, +wn}:
      +wa = D1.g.wcn.text(wn, SCon{']', tail})
      +wb = D1.g.wcn.text(wn, SCon{']', ""})
      gt.cons('[', D1.g.val.text(vals, wa), D1.g.val.text(vals, wb), tail,
        gt.val.before(vals, wa, wb, tail, gt.wcn.before(wn, SCon{']', tail}, SCon{']', ""}, tail, {==}),
          L1.g_val_text_tail(vals, wa), L1.g_val_text_tail(vals, wb)))
    case D1.GvInlineTableEmpty{+w1, +w2}:
      gt.cons('{', String.append(w1, String.append(w2, SCon{'}', tail})),
        String.append(w1, String.append(w2, SCon{'}', ""})), tail,
        gt.app(w1, String.append(w2, SCon{'}', tail}), String.append(w2, SCon{'}', ""}), tail,
          gt.app(w2, SCon{'}', tail}, SCon{'}', ""}, tail, {==})))
    case D1.GvInlineTable{+w1, +kvs, +w2}:
      +xa = String.append(w2, SCon{'}', tail})
      +xb = String.append(w2, SCon{'}', ""})
      gt.cons('{', String.append(w1, D1.g.val.text(kvs, xa)), String.append(w1, D1.g.val.text(kvs, xb)), tail,
        gt.app(w1, D1.g.val.text(kvs, xa), D1.g.val.text(kvs, xb), tail,
          gt.val.before(kvs, xa, xb, tail, gt.app(w2, SCon{'}', tail}, SCon{'}', ""}, tail, {==}),
            L1.g_val_text_tail(kvs, xa), L1.g_val_text_tail(kvs, xb))))
    case D1.GvDateTime{+cs}:
      gt.nil(String.from_list(cs), tail)
    case D1.GvFloat{+cs}:
      gt.nil(String.from_list(cs), tail)
    case D1.GvInteger{+cs}:
      gt.nil(String.from_list(cs), tail)
    case D1.GArrayValues{+wa, +val, +wb, +rest}:
      +ra = {SCon{',', D1.g.val.text(rest, tail)} : String}
      +rb = {SCon{',', D1.g.val.text(rest, "")} : String}
      ea = gt.cons(',', D1.g.val.text(rest, tail), D1.g.val.text(rest, ""), tail,
        L1.g_val_text_tail(rest, tail))
      +ba = D1.g.wcn.text(wb, ra)
      +bb = D1.g.wcn.text(wb, rb)
      gt.wcn.before(wa, D1.g.val.text(val, ba), D1.g.val.text(val, bb), tail,
        gt.val.before(val, ba, bb, tail, gt.wcn.before(wb, ra, rb, tail, ea),
          L1.g_val_text_tail(val, ba), L1.g_val_text_tail(val, bb)))
    case D1.GArrayValuesLast{+wa, +val, +wb, +sep}:
      +ba = D1.g.wcn.text(wb, D1.g.sep.text(sep, tail))
      +bb = D1.g.wcn.text(wb, D1.g.sep.text(sep, ""))
      gt.wcn.before(wa, D1.g.val.text(val, ba), D1.g.val.text(val, bb), tail,
        gt.val.before(val, ba, bb, tail,
          gt.wcn.before(wb, D1.g.sep.text(sep, tail), D1.g.sep.text(sep, ""), tail, gt.sep(sep, tail)),
          L1.g_val_text_tail(val, ba), L1.g_val_text_tail(val, bb)))
    case D1.GInlineTableKeyvals{+kv, +w1, +w2, +rest}:
      +ra = String.append(w2, D1.g.val.text(rest, tail))
      +rb = String.append(w2, D1.g.val.text(rest, ""))
      +xa = String.append(w1, SCon{',', ra})
      +xb = String.append(w1, SCon{',', rb})
      gt.val.before(kv, xa, xb, tail,
        gt.app(w1, SCon{',', ra}, SCon{',', rb}, tail,
          gt.cons(',', ra, rb, tail,
            gt.app(w2, D1.g.val.text(rest, tail), D1.g.val.text(rest, ""), tail,
              L1.g_val_text_tail(rest, tail)))),
        L1.g_val_text_tail(kv, xa), L1.g_val_text_tail(kv, xb))
    case D1.GInlineTableKeyvalsLast{kv}:
      L1.g_val_text_tail(kv, tail)
    case D1.GKeyval{+key, +w1, +w2, +val}:
      +ra = String.append(w2, D1.g.val.text(val, tail))
      +rb = String.append(w2, D1.g.val.text(val, ""))
      +xa = String.append(w1, SCon{'=', ra})
      +xb = String.append(w1, SCon{'=', rb})
      gt.step(D1.g.key.text(key, xa), D1.g.key.text(key, xb), D1.g.key.text(key, ""), xa, xb, tail,
        gt.key(key, xa),
        gt.app(w1, SCon{'=', ra}, SCon{'=', rb}, tail,
          gt.cons('=', ra, rb, tail,
            gt.app(w2, D1.g.val.text(val, tail), D1.g.val.text(val, ""), tail,
              L1.g_val_text_tail(val, tail)))),
        gt.key(key, xb))

# a table header
def gt.table(tb: D1.GTable, +tail: String) -> gt.T(D1.g.table.text(tb, tail), D1.g.table.text(tb, ""), tail):
  match tb:
    case D1.GStdTable{+w1, +key, +w2}:
      +xa = String.append(w2, SCon{']', tail})
      +xb = String.append(w2, SCon{']', ""})
      gt.cons('[', String.append(w1, D1.g.key.text(key, xa)), String.append(w1, D1.g.key.text(key, xb)), tail,
        gt.app(w1, D1.g.key.text(key, xa), D1.g.key.text(key, xb), tail,
          gt.step(D1.g.key.text(key, xa), D1.g.key.text(key, xb), D1.g.key.text(key, ""), xa, xb, tail,
            gt.key(key, xa), gt.app(w2, SCon{']', tail}, SCon{']', ""}, tail, {==}), gt.key(key, xb))))
    case D1.GArrayTable{+w1, +key, +w2}:
      +xa = String.append(w2, SCon{']', SCon{']', tail}})
      +xb = String.append(w2, SCon{']', SCon{']', ""}})
      gt.cons('[', SCon{'[', String.append(w1, D1.g.key.text(key, xa))},
        SCon{'[', String.append(w1, D1.g.key.text(key, xb))}, tail,
        gt.cons('[', String.append(w1, D1.g.key.text(key, xa)), String.append(w1, D1.g.key.text(key, xb)), tail,
          gt.app(w1, D1.g.key.text(key, xa), D1.g.key.text(key, xb), tail,
            gt.step(D1.g.key.text(key, xa), D1.g.key.text(key, xb), D1.g.key.text(key, ""), xa, xb, tail,
              gt.key(key, xa), gt.app(w2, SCon{']', SCon{']', tail}}, SCon{']', SCon{']', ""}}, tail, {==}),
              gt.key(key, xb)))))

# an expression
def gt.expr(ex: D1.GExpr, +tail: String) -> gt.T(D1.g.expr.text(ex, tail), D1.g.expr.text(ex, ""), tail):
  match ex:
    case D1.GxBlank{+w1, +com}:
      gt.app(w1, D1.g.com.text(com, tail), D1.g.com.text(com, ""), tail, gt.com(com, tail))
    case D1.GxKeyval{+w1, +kv, +w2, +com}:
      +xa = String.append(w2, D1.g.com.text(com, tail))
      +xb = String.append(w2, D1.g.com.text(com, ""))
      gt.app(w1, D1.g.val.text(kv, xa), D1.g.val.text(kv, xb), tail,
        gt.val.before(kv, xa, xb, tail, gt.app(w2, D1.g.com.text(com, tail), D1.g.com.text(com, ""), tail,
          gt.com(com, tail)), L1.g_val_text_tail(kv, xa), L1.g_val_text_tail(kv, xb)))
    case D1.GxTable{+w1, +tb, +w2, +com}:
      +xa = String.append(w2, D1.g.com.text(com, tail))
      +xb = String.append(w2, D1.g.com.text(com, ""))
      gt.app(w1, D1.g.table.text(tb, xa), D1.g.table.text(tb, xb), tail,
        gt.step(D1.g.table.text(tb, xa), D1.g.table.text(tb, xb), D1.g.table.text(tb, ""), xa, xb, tail,
          gt.table(tb, xa), gt.app(w2, D1.g.com.text(com, tail), D1.g.com.text(com, ""), tail, gt.com(com, tail)),
          gt.table(tb, xb)))
