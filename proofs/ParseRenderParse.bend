# proofs of laws/ParseRenderParse.bend
import Base
import ../main.bend as T
import ../src/eq.bend as Eq
import ../laws/ParseRenderParse.bend as Laws
import ../laws/ParsedIsWellFormed.bend as L1
import ../laws/RenderThenParse.bend as L2
import ../laws/StringRenderEscapes.bend as L3
import ../laws/defs/BareValueGrammar.bend as D1
import ../laws/defs/DocumentSameness.bend as D2
import ./lemmas/ControlEscapeText.bend as M1
import ./lemmas/FailedWalkNameCompare.bend as M2
import ./lemmas/ParsedWellFormedness.bend as M3
import ./lemmas/PrefixAndTake.bend as M4
import ./lemmas/ReadOutEquality.bend as M5
import ./lemmas/RenderParseRoundTrip.bend as M6
import ./lemmas/ReorderedTableNames.bend as M7
import ./lemmas/ShortTextBounds.bend as M8
import ./lemmas/ValueSelfEquality.bend as M9

# WP-R2: laws/ParseRenderParse.bend. The first half is laws/RenderThenParse.bend at parse(t), which
# laws/ParsedIsWellFormed.bend
# makes well-formed. The second reads render_parse_canon through render:
# render writes a span as the owned string of its characters
# (span_quote_basic), so render(own(x)) is render(x); and render already writes
# each table's pairs that are no table before its tables, so render(canon(d))
# is render(d). An element of an array of tables is written under its own
# path and canon stores it under the array's, which wf.aot makes one string.

# the pass as render calls it for a table's rows, keeping the separator
def r2.P(xs: List<&2, T.Val>, +gg: String, +tb: Bool) -> String:
  T.render.pass(xs, gg, True{}, tb)

# what render.go writes after an item: the separator, then the rest
def r2.R(+tt: List<&2, T.Val>, +gg: String, +tr: Bool) -> String:
  String.append(T.render.suf(gg, tr, List.is_empty(&2, T.Val, tt)), T.render.go(tt, gg, tr))

# a table's text in the pass that writes tables, and nothing in the other
def r2.tab(tb: Bool, ss: String) -> String:
  match tb:
    case True{}:
      ss
    case False{}:
      ""

# a key's text and the separator in the pass that writes keys, and nothing in
# the other
def r2.key(tb: Bool, ss: String, gg: String) -> String:
  match tb:
    case True{}:
      ""
    case False{}:
      ss ++ gg

# what one pass writes for one row, before the rest
def r2.hd(hh: T.Val, +gg: String, +tb: Bool) -> String:
  match hh:
    case T.VPair{_n, T.VHead{pp, rr}}:
      r2.tab(tb, "[" ++ pp ++ "]\n" ++ T.render.both(rr, "\n", True{}))
    case T.VPair{_n, T.VAots{_p, es}}:
      r2.tab(tb, T.render.both(es, "\n", True{}))
    case T.VAot{pp, rr}:
      r2.tab(tb, "[[" ++ pp ++ "]]\n" ++ T.render.both(rr, "\n", True{}))
    case T.VPair{nn, T.VArr{ii}}:
      r2.key(tb, T.key(nn) ++ " = [" ++ T.render.go(ii, ", ", False{}) ++ "]", gg)
    case T.VPair{nn, T.VInl{ii}}:
      r2.key(tb, T.key(nn) ++ " = {" ++ T.render.go(ii, ", ", False{}) ++ "}", gg)
    case T.VPair{nn, vv}:
      r2.key(tb, T.key(nn) ++ " = " ++ T.render.atom(vv), gg)
    case T.VArr{ii}:
      r2.key(tb, "[" ++ T.render.go(ii, ", ", False{}) ++ "]", gg)
    case T.VInl{ii}:
      r2.key(tb, "{" ++ T.render.go(ii, ", ", False{}) ++ "}", gg)
    case vv:
      r2.key(tb, T.render.atom(vv), gg)

# what render.go writes for one item, followed by the given rest
def r2.gk(hh: T.Val, rr: String) -> String:
  match hh:
    case T.VPair{_n, T.VHead{pp, ls}}:
      "[" ++ pp ++ "]\n" ++ T.render.go(ls, "\n", True{}) ++ rr
    case T.VPair{_n, T.VAots{_p, es}}:
      T.render.go(es, "\n", True{}) ++ rr
    case T.VAot{pp, ls}:
      "[[" ++ pp ++ "]]\n" ++ T.render.go(ls, "\n", True{}) ++ rr
    case T.VPair{nn, T.VArr{ii}}:
      T.key(nn) ++ " = [" ++ T.render.go(ii, ", ", False{}) ++ "]" ++ rr
    case T.VPair{nn, T.VInl{ii}}:
      T.key(nn) ++ " = {" ++ T.render.go(ii, ", ", False{}) ++ "}" ++ rr
    case T.VPair{nn, vv}:
      T.key(nn) ++ " = " ++ T.render.atom(vv) ++ rr
    case T.VArr{ii}:
      "[" ++ T.render.go(ii, ", ", False{}) ++ "]" ++ rr
    case T.VInl{ii}:
      "{" ++ T.render.go(ii, ", ", False{}) ++ "}" ++ rr
    case vv:
      T.render.atom(vv) ++ rr

# two appends of equal parts are equal
def r2.app2(
  +aa: String,
  +bb: String,
  +cc: String,
  +dd: String,
  e1: {aa == bb : String},
  e2: {cc == dd : String}
) -> {String.append(aa, cc) == String.append(bb, dd) : String}:
  Equal.trans(String, String.append(aa, cc), String.append(bb, cc), String.append(bb, dd),
    Equal.cong(String, String, zz => String.append(zz, cc), aa, bb, e1),
    Equal.cong(String, String, zz => String.append(bb, zz), cc, dd, e2))

# four parts and a rest, regrouped
def r2.as4(
  +aa: String,
  +bb: String,
  +cc: String,
  +dd: String,
  +rr: String
) -> {String.append(aa, String.append(bb, String.append(cc, String.append(dd, rr))))
  == String.append(String.append(aa, String.append(bb, String.append(cc, dd))), rr) : String}:
  +xx = {String.append(bb, String.append(cc, dd)) : String}
  Equal.sym(String, String.append(String.append(aa, xx), rr),
    String.append(aa, String.append(bb, String.append(cc, String.append(dd, rr)))),
    Equal.trans(String, String.append(String.append(aa, xx), rr), String.append(aa, String.append(xx, rr)),
      String.append(aa, String.append(bb, String.append(cc, String.append(dd, rr)))),
      Eq.append_assoc(aa, xx, rr),
      Equal.cong(String, String, zz => String.append(aa, zz), String.append(xx, rr),
        String.append(bb, String.append(cc, String.append(dd, rr))),
        Equal.trans(String, String.append(xx, rr), String.append(bb, String.append(String.append(cc, dd), rr)),
          String.append(bb, String.append(cc, String.append(dd, rr))),
          Eq.append_assoc(bb, String.append(cc, dd), rr),
          Equal.cong(String, String, zz => String.append(bb, zz), String.append(String.append(cc, dd), rr),
            String.append(cc, String.append(dd, rr)), Eq.append_assoc(cc, dd, rr))))))

# a table's header and rows, then the rest
def r2.sp.h(
  tb: Bool,
  +pp: String,
  rows: List<&2, T.Val>,
  tt: List<&2, T.Val>,
  +gg: String,
  +nn: String,
  +rr: String
) -> {T.render.head(tb, pp, rows, tt, gg, True{}, _u => nn, _v => rr)
  == String.append(r2.tab(tb, "[" ++ pp ++ "]\n" ++ nn), rr) : String}:
  match tb:
    case False{}:
      {==}
    case True{}:
      r2.as4("[", pp, "]\n", nn, rr)

# an array of tables' elements, then the rest
def r2.sp.a(
  tb: Bool,
  es: List<&2, T.Val>,
  tt: List<&2, T.Val>,
  +gg: String,
  +nn: String,
  +rr: String
) -> {T.render.aots(tb, es, tt, gg, True{}, _u => nn, _v => rr) == String.append(r2.tab(tb, nn), rr) : String}:
  match tb:
    case False{}:
      {==}
    case True{}:
      {==}

# an element's header and rows, then the rest
def r2.sp.o(
  tb: Bool,
  +pp: String,
  rows: List<&2, T.Val>,
  tt: List<&2, T.Val>,
  +gg: String,
  +nn: String,
  +rr: String
) -> {T.render.aot(tb, pp, rows, tt, gg, True{}, _u => nn, _v => rr)
  == String.append(r2.tab(tb, "[[" ++ pp ++ "]]\n" ++ nn), rr) : String}:
  match tb:
    case False{}:
      {==}
    case True{}:
      r2.as4("[[", pp, "]]\n", nn, rr)

# a key's text and the separator, then the rest. The text is a thunk, so the
# pass that writes tables does not build it.
def r2.sp.v(
  tb: Bool,
  +text: String,
  +tt: List<&2, T.Val>,
  +gg: String,
  +rr: String
) -> {T.render.late(tb, _u => text, tt, gg, True{}, _v => rr)
  == String.append(r2.key(tb, text, gg), rr) : String}:
  match tb:
    case True{}:
      {==}
    case False{}:
      Equal.sym(String, String.append(String.append(text, gg), rr), String.append(text, String.append(gg, rr)),
        Eq.append_assoc(text, gg, rr))

# the pass writes a row's text, then the rest
def r2.split(
  hh: T.Val,
  +tt: List<&2, T.Val>,
  +gg: String,
  +tb: Bool
) -> {r2.P(hh <> tt, gg, tb) == String.append(r2.hd(hh, gg, tb), r2.P(tt, gg, tb)) : String}:
  match hh:
    case T.VPair{+kk, T.VStr{+a1}}:
      r2.sp.v(tb, T.key(kk) ++ " = " ++ T.render.atom(T.VStr{a1}), tt, gg, r2.P(tt, gg, tb))
    case T.VPair{+kk, T.VSpan{+a1, +a2}}:
      r2.sp.v(tb, T.key(kk) ++ " = " ++ T.render.atom(T.VSpan{a1, a2}), tt, gg, r2.P(tt, gg, tb))
    case T.VPair{+kk, T.VInt{+a1, +a2}}:
      r2.sp.v(tb, T.key(kk) ++ " = " ++ T.render.atom(T.VInt{a1, a2}), tt, gg, r2.P(tt, gg, tb))
    case T.VPair{+kk, T.VFlo{+a1, +a2}}:
      r2.sp.v(tb, T.key(kk) ++ " = " ++ T.render.atom(T.VFlo{a1, a2}), tt, gg, r2.P(tt, gg, tb))
    case T.VPair{+kk, T.VBool{+a1}}:
      r2.sp.v(tb, T.key(kk) ++ " = " ++ T.render.atom(T.VBool{a1}), tt, gg, r2.P(tt, gg, tb))
    case T.VPair{+kk, T.VWhen{+a1}}:
      r2.sp.v(tb, T.key(kk) ++ " = " ++ T.render.atom(T.VWhen{a1}), tt, gg, r2.P(tt, gg, tb))
    case T.VPair{+kk, T.VArr{+a1}}:
      r2.sp.v(tb, T.key(kk) ++ " = [" ++ T.render.go(a1, ", ", False{}) ++ "]", tt, gg,
        r2.P(tt, gg, tb))
    case T.VPair{+kk, T.VInl{+a1}}:
      r2.sp.v(tb, T.key(kk) ++ " = {" ++ T.render.go(a1, ", ", False{}) ++ "}", tt, gg,
        r2.P(tt, gg, tb))
    case T.VPair{+kk, T.VHead{+a1, +a2}}:
      r2.sp.h(tb, a1, a2, tt, gg, T.render.both(a2, "\n", True{}),
        r2.P(tt, gg, tb))
    case T.VPair{+kk, T.VAot{+a1, +a2}}:
      r2.sp.v(tb, T.key(kk) ++ " = " ++ T.render.atom(T.VAot{a1, a2}), tt, gg, r2.P(tt, gg, tb))
    case T.VPair{+kk, T.VAots{+a1, +a2}}:
      r2.sp.a(tb, a2, tt, gg, T.render.both(a2, "\n", True{}),
        r2.P(tt, gg, tb))
    case T.VPair{+kk, T.VPair{+a1, +a2}}:
      r2.sp.v(tb, T.key(kk) ++ " = " ++ T.render.atom(T.VPair{a1, a2}), tt, gg, r2.P(tt, gg, tb))
    case T.VStr{+a1}:
      r2.sp.v(tb, T.render.atom(T.VStr{a1}), tt, gg, r2.P(tt, gg, tb))
    case T.VSpan{+a1, +a2}:
      r2.sp.v(tb, T.render.atom(T.VSpan{a1, a2}), tt, gg, r2.P(tt, gg, tb))
    case T.VInt{+a1, +a2}:
      r2.sp.v(tb, T.render.atom(T.VInt{a1, a2}), tt, gg, r2.P(tt, gg, tb))
    case T.VFlo{+a1, +a2}:
      r2.sp.v(tb, T.render.atom(T.VFlo{a1, a2}), tt, gg, r2.P(tt, gg, tb))
    case T.VBool{+a1}:
      r2.sp.v(tb, T.render.atom(T.VBool{a1}), tt, gg, r2.P(tt, gg, tb))
    case T.VWhen{+a1}:
      r2.sp.v(tb, T.render.atom(T.VWhen{a1}), tt, gg, r2.P(tt, gg, tb))
    case T.VArr{+a1}:
      r2.sp.v(tb, "[" ++ T.render.go(a1, ", ", False{}) ++ "]", tt, gg, r2.P(tt, gg, tb))
    case T.VInl{+a1}:
      r2.sp.v(tb, "{" ++ T.render.go(a1, ", ", False{}) ++ "}", tt, gg, r2.P(tt, gg, tb))
    case T.VHead{+a1, +a2}:
      r2.sp.v(tb, T.render.atom(T.VHead{a1, a2}), tt, gg, r2.P(tt, gg, tb))
    case T.VAot{+a1, +a2}:
      r2.sp.o(tb, a1, a2, tt, gg, T.render.both(a2, "\n", True{}),
        r2.P(tt, gg, tb))
    case T.VAots{+a1, +a2}:
      r2.sp.v(tb, T.render.atom(T.VAots{a1, a2}), tt, gg, r2.P(tt, gg, tb))

# two rows one pass writes alike, before rests it writes alike
def r2.cc(
  +h1: T.Val,
  +h2: T.Val,
  +xx: List<&2, T.Val>,
  +yy: List<&2, T.Val>,
  +gg: String,
  +tb: Bool,
  eh: {r2.hd(h1, gg, tb) == r2.hd(h2, gg, tb) : String},
  et: {r2.P(xx, gg, tb) == r2.P(yy, gg, tb) : String}
) -> {r2.P(h1 <> xx, gg, tb) == r2.P(h2 <> yy, gg, tb) : String}:
  Equal.trans(String, r2.P(h1 <> xx, gg, tb), String.append(r2.hd(h1, gg, tb), r2.P(xx, gg, tb)),
    r2.P(h2 <> yy, gg, tb), r2.split(h1, xx, gg, tb),
    Equal.trans(String, String.append(r2.hd(h1, gg, tb), r2.P(xx, gg, tb)),
      String.append(r2.hd(h2, gg, tb), r2.P(yy, gg, tb)), r2.P(h2 <> yy, gg, tb),
      r2.app2(r2.hd(h1, gg, tb), r2.hd(h2, gg, tb), r2.P(xx, gg, tb), r2.P(yy, gg, tb), eh, et),
      Equal.sym(String, r2.P(h2 <> yy, gg, tb), String.append(r2.hd(h2, gg, tb), r2.P(yy, gg, tb)),
        r2.split(h2, yy, gg, tb))))

# a pass over two lists written one after the other
def r2.app(
  xs: List<&2, T.Val>,
  +ys: List<&2, T.Val>,
  +gg: String,
  +tb: Bool
) -> {r2.P(List.append(&2, T.Val, xs, ys), gg, tb) == String.append(r2.P(xs, gg, tb), r2.P(ys, gg, tb)) : String}:
  match xs:
    case []:
      {==}
    case +hh <> +tt:
      Equal.trans(String, r2.P(hh <> List.append(&2, T.Val, tt, ys), gg, tb),
        String.append(r2.hd(hh, gg, tb), r2.P(List.append(&2, T.Val, tt, ys), gg, tb)),
        String.append(r2.P(hh <> tt, gg, tb), r2.P(ys, gg, tb)),
        r2.split(hh, List.append(&2, T.Val, tt, ys), gg, tb),
        Equal.trans(String, String.append(r2.hd(hh, gg, tb), r2.P(List.append(&2, T.Val, tt, ys), gg, tb)),
          String.append(r2.hd(hh, gg, tb), String.append(r2.P(tt, gg, tb), r2.P(ys, gg, tb))),
          String.append(r2.P(hh <> tt, gg, tb), r2.P(ys, gg, tb)),
          Equal.cong(String, String, zz => String.append(r2.hd(hh, gg, tb), zz),
            r2.P(List.append(&2, T.Val, tt, ys), gg, tb), String.append(r2.P(tt, gg, tb), r2.P(ys, gg, tb)),
            r2.app(tt, ys, gg, tb)),
          Equal.trans(String, String.append(r2.hd(hh, gg, tb), String.append(r2.P(tt, gg, tb), r2.P(ys, gg, tb))),
            String.append(String.append(r2.hd(hh, gg, tb), r2.P(tt, gg, tb)), r2.P(ys, gg, tb)),
            String.append(r2.P(hh <> tt, gg, tb), r2.P(ys, gg, tb)),
            Equal.sym(String, String.append(String.append(r2.hd(hh, gg, tb), r2.P(tt, gg, tb)), r2.P(ys, gg, tb)),
              String.append(r2.hd(hh, gg, tb), String.append(r2.P(tt, gg, tb), r2.P(ys, gg, tb))),
              Eq.append_assoc(r2.hd(hh, gg, tb), r2.P(tt, gg, tb), r2.P(ys, gg, tb))),
            Equal.cong(String, String, zz => String.append(zz, r2.P(ys, gg, tb)),
              String.append(r2.hd(hh, gg, tb), r2.P(tt, gg, tb)), r2.P(hh <> tt, gg, tb),
              Equal.sym(String, r2.P(hh <> tt, gg, tb), String.append(r2.hd(hh, gg, tb), r2.P(tt, gg, tb)),
                r2.split(hh, tt, gg, tb))))))

# the separator and the rest render.go writes after an item, for the rest
# read out and as it is
def r2.rt(
  +tt: List<&2, T.Val>,
  +gg: String,
  +tr: Bool,
  ih: {T.render.go(D1.own.rows(tt), gg, tr) == T.render.go(tt, gg, tr) : String}
) -> {r2.R(D1.own.rows(tt), gg, tr) == r2.R(tt, gg, tr) : String}:
  r2.app2(T.render.suf(gg, tr, List.is_empty(&2, T.Val, D1.own.rows(tt))),
    T.render.suf(gg, tr, List.is_empty(&2, T.Val, tt)), T.render.go(D1.own.rows(tt), gg, tr),
    T.render.go(tt, gg, tr),
    Equal.cong(Bool, String, bb => T.render.suf(gg, tr, bb), List.is_empty(&2, T.Val, D1.own.rows(tt)),
      List.is_empty(&2, T.Val, tt), M5.empty.own(tt)),
    ih)

# two items render.go writes alike, before the rest read out and as it is
def r2.gc(
  +h1: T.Val,
  +h2: T.Val,
  +tt: List<&2, T.Val>,
  +gg: String,
  +tr: Bool,
  ih: {T.render.go(D1.own.rows(tt), gg, tr) == T.render.go(tt, gg, tr) : String},
  eh: {r2.gk(h1, r2.R(tt, gg, tr)) == r2.gk(h2, r2.R(tt, gg, tr)) : String}
) -> {r2.gk(h1, r2.R(D1.own.rows(tt), gg, tr)) == r2.gk(h2, r2.R(tt, gg, tr)) : String}:
  Equal.trans(String, r2.gk(h1, r2.R(D1.own.rows(tt), gg, tr)), r2.gk(h1, r2.R(tt, gg, tr)),
    r2.gk(h2, r2.R(tt, gg, tr)),
    Equal.cong(String, String, zz => r2.gk(h1, zz), r2.R(D1.own.rows(tt), gg, tr), r2.R(tt, gg, tr),
      r2.rt(tt, gg, tr, ih)),
    eh)

# render.go writes a list read out as it writes the list
def r2.own.go(
  xs: List<&2, T.Val>,
  +gg: String,
  +tr: Bool
) -> {T.render.go(D1.own.rows(xs), gg, tr) == T.render.go(xs, gg, tr) : String}:
  match xs:
    case []:
      {==}
    case T.VPair{+kk, T.VStr{+a1}} <> +tt:
      r2.gc(T.VPair{kk, T.VStr{a1}}, T.VPair{kk, T.VStr{a1}}, tt, gg, tr,
        r2.own.go(tt, gg, tr),
        {==})
    case T.VPair{+kk, T.VSpan{+a1, +a2}} <> +tt:
      r2.gc(T.VPair{kk, T.VStr{T.span.str(a1, a2, U32.is_zero(a2))}}, T.VPair{kk, T.VSpan{a1, a2}}, tt, gg, tr,
        r2.own.go(tt, gg, tr),
        Equal.cong(String, String, zz => T.key(kk) ++ " = " ++ zz ++ r2.R(tt, gg, tr),
          T.key.basic(T.span.str(a1, a2, U32.is_zero(a2))), T.span.quote(a1, a2),
          Equal.sym(String, T.span.quote(a1, a2), T.key.basic(T.span.str(a1, a2, U32.is_zero(a2))),
            L3.span_quote_basic(a1, a2))))
    case T.VPair{+kk, T.VInt{+a1, +a2}} <> +tt:
      r2.gc(T.VPair{kk, T.VInt{a1, a2}}, T.VPair{kk, T.VInt{a1, a2}}, tt, gg, tr,
        r2.own.go(tt, gg, tr),
        {==})
    case T.VPair{+kk, T.VFlo{+a1, +a2}} <> +tt:
      r2.gc(T.VPair{kk, T.VFlo{a1, a2}}, T.VPair{kk, T.VFlo{a1, a2}}, tt, gg, tr,
        r2.own.go(tt, gg, tr),
        {==})
    case T.VPair{+kk, T.VBool{+a1}} <> +tt:
      r2.gc(T.VPair{kk, T.VBool{a1}}, T.VPair{kk, T.VBool{a1}}, tt, gg, tr,
        r2.own.go(tt, gg, tr),
        {==})
    case T.VPair{+kk, T.VWhen{+a1}} <> +tt:
      r2.gc(T.VPair{kk, T.VWhen{a1}}, T.VPair{kk, T.VWhen{a1}}, tt, gg, tr,
        r2.own.go(tt, gg, tr),
        {==})
    case T.VPair{+kk, T.VArr{+a1}} <> +tt:
      r2.gc(T.VPair{kk, T.VArr{D1.own.rows(a1)}}, T.VPair{kk, T.VArr{a1}}, tt, gg, tr,
        r2.own.go(tt, gg, tr),
        Equal.cong(String, String, zz => T.key(kk) ++ " = [" ++ zz ++ "]" ++ r2.R(tt, gg, tr),
          T.render.go(D1.own.rows(a1), ", ", False{}), T.render.go(a1, ", ", False{}),
          r2.own.go(a1, ", ", False{})))
    case T.VPair{+kk, T.VInl{+a1}} <> +tt:
      r2.gc(T.VPair{kk, T.VInl{D1.own.rows(a1)}}, T.VPair{kk, T.VInl{a1}}, tt, gg, tr,
        r2.own.go(tt, gg, tr),
        Equal.cong(String, String, zz => T.key(kk) ++ " = {" ++ zz ++ "}" ++ r2.R(tt, gg, tr),
          T.render.go(D1.own.rows(a1), ", ", False{}), T.render.go(a1, ", ", False{}),
          r2.own.go(a1, ", ", False{})))
    case T.VPair{+kk, T.VHead{+a1, +a2}} <> +tt:
      r2.gc(T.VPair{kk, T.VHead{a1, D1.own.rows(a2)}}, T.VPair{kk, T.VHead{a1, a2}}, tt, gg, tr,
        r2.own.go(tt, gg, tr),
        Equal.cong(String, String, zz => "[" ++ a1 ++ "]\n" ++ zz ++ r2.R(tt, gg, tr),
          T.render.go(D1.own.rows(a2), "\n", True{}), T.render.go(a2, "\n", True{}),
          r2.own.go(a2, "\n", True{})))
    case T.VPair{+kk, T.VAot{+a1, +a2}} <> +tt:
      r2.gc(T.VPair{kk, T.VAot{a1, D1.own.rows(a2)}}, T.VPair{kk, T.VAot{a1, a2}}, tt, gg, tr,
        r2.own.go(tt, gg, tr),
        {==})
    case T.VPair{+kk, T.VAots{+a1, +a2}} <> +tt:
      r2.gc(T.VPair{kk, T.VAots{a1, D1.own.rows(a2)}}, T.VPair{kk, T.VAots{a1, a2}}, tt, gg, tr,
        r2.own.go(tt, gg, tr),
        Equal.cong(String, String, zz => zz ++ r2.R(tt, gg, tr),
          T.render.go(D1.own.rows(a2), "\n", True{}), T.render.go(a2, "\n", True{}),
          r2.own.go(a2, "\n", True{})))
    case T.VPair{+kk, T.VPair{+a1, +a2}} <> +tt:
      r2.gc(T.VPair{kk, T.VPair{a1, a2}}, T.VPair{kk, T.VPair{a1, a2}}, tt, gg, tr,
        r2.own.go(tt, gg, tr),
        {==})
    case T.VStr{+a1} <> +tt:
      r2.gc(T.VStr{a1}, T.VStr{a1}, tt, gg, tr,
        r2.own.go(tt, gg, tr),
        {==})
    case T.VSpan{+a1, +a2} <> +tt:
      r2.gc(T.VStr{T.span.str(a1, a2, U32.is_zero(a2))}, T.VSpan{a1, a2}, tt, gg, tr,
        r2.own.go(tt, gg, tr),
        Equal.cong(String, String, zz => zz ++ r2.R(tt, gg, tr),
          T.key.basic(T.span.str(a1, a2, U32.is_zero(a2))), T.span.quote(a1, a2),
          Equal.sym(String, T.span.quote(a1, a2), T.key.basic(T.span.str(a1, a2, U32.is_zero(a2))),
            L3.span_quote_basic(a1, a2))))
    case T.VInt{+a1, +a2} <> +tt:
      r2.gc(T.VInt{a1, a2}, T.VInt{a1, a2}, tt, gg, tr,
        r2.own.go(tt, gg, tr),
        {==})
    case T.VFlo{+a1, +a2} <> +tt:
      r2.gc(T.VFlo{a1, a2}, T.VFlo{a1, a2}, tt, gg, tr,
        r2.own.go(tt, gg, tr),
        {==})
    case T.VBool{+a1} <> +tt:
      r2.gc(T.VBool{a1}, T.VBool{a1}, tt, gg, tr,
        r2.own.go(tt, gg, tr),
        {==})
    case T.VWhen{+a1} <> +tt:
      r2.gc(T.VWhen{a1}, T.VWhen{a1}, tt, gg, tr,
        r2.own.go(tt, gg, tr),
        {==})
    case T.VArr{+a1} <> +tt:
      r2.gc(T.VArr{D1.own.rows(a1)}, T.VArr{a1}, tt, gg, tr,
        r2.own.go(tt, gg, tr),
        Equal.cong(String, String, zz => "[" ++ zz ++ "]" ++ r2.R(tt, gg, tr),
          T.render.go(D1.own.rows(a1), ", ", False{}), T.render.go(a1, ", ", False{}),
          r2.own.go(a1, ", ", False{})))
    case T.VInl{+a1} <> +tt:
      r2.gc(T.VInl{D1.own.rows(a1)}, T.VInl{a1}, tt, gg, tr,
        r2.own.go(tt, gg, tr),
        Equal.cong(String, String, zz => "{" ++ zz ++ "}" ++ r2.R(tt, gg, tr),
          T.render.go(D1.own.rows(a1), ", ", False{}), T.render.go(a1, ", ", False{}),
          r2.own.go(a1, ", ", False{})))
    case T.VHead{+a1, +a2} <> +tt:
      r2.gc(T.VHead{a1, D1.own.rows(a2)}, T.VHead{a1, a2}, tt, gg, tr,
        r2.own.go(tt, gg, tr),
        {==})
    case T.VAot{+a1, +a2} <> +tt:
      r2.gc(T.VAot{a1, D1.own.rows(a2)}, T.VAot{a1, a2}, tt, gg, tr,
        r2.own.go(tt, gg, tr),
        Equal.cong(String, String, zz => "[[" ++ a1 ++ "]]\n" ++ zz ++ r2.R(tt, gg, tr),
          T.render.go(D1.own.rows(a2), "\n", True{}), T.render.go(a2, "\n", True{}),
          r2.own.go(a2, "\n", True{})))
    case T.VAots{+a1, +a2} <> +tt:
      r2.gc(T.VAots{a1, D1.own.rows(a2)}, T.VAots{a1, a2}, tt, gg, tr,
        r2.own.go(tt, gg, tr),
        {==})

# the pass writes a list read out as it writes the list
def r2.own.pass(
  xs: List<&2, T.Val>,
  +gg: String,
  +tb: Bool
) -> {r2.P(D1.own.rows(xs), gg, tb) == r2.P(xs, gg, tb) : String}:
  match xs:
    case []:
      {==}
    case T.VPair{+kk, T.VStr{+a1}} <> +tt:
      r2.cc(T.VPair{kk, T.VStr{a1}}, T.VPair{kk, T.VStr{a1}},
        D1.own.rows(tt), tt, gg, tb,
        {==},
        r2.own.pass(tt, gg, tb))
    case T.VPair{+kk, T.VSpan{+a1, +a2}} <> +tt:
      r2.cc(T.VPair{kk, T.VStr{T.span.str(a1, a2, U32.is_zero(a2))}}, T.VPair{kk, T.VSpan{a1, a2}},
        D1.own.rows(tt), tt, gg, tb,
        Equal.cong(String, String, zz => r2.key(tb, T.key(kk) ++ " = " ++ zz, gg),
          T.key.basic(T.span.str(a1, a2, U32.is_zero(a2))), T.span.quote(a1, a2),
          Equal.sym(String, T.span.quote(a1, a2), T.key.basic(T.span.str(a1, a2, U32.is_zero(a2))),
            L3.span_quote_basic(a1, a2))),
        r2.own.pass(tt, gg, tb))
    case T.VPair{+kk, T.VInt{+a1, +a2}} <> +tt:
      r2.cc(T.VPair{kk, T.VInt{a1, a2}}, T.VPair{kk, T.VInt{a1, a2}},
        D1.own.rows(tt), tt, gg, tb,
        {==},
        r2.own.pass(tt, gg, tb))
    case T.VPair{+kk, T.VFlo{+a1, +a2}} <> +tt:
      r2.cc(T.VPair{kk, T.VFlo{a1, a2}}, T.VPair{kk, T.VFlo{a1, a2}},
        D1.own.rows(tt), tt, gg, tb,
        {==},
        r2.own.pass(tt, gg, tb))
    case T.VPair{+kk, T.VBool{+a1}} <> +tt:
      r2.cc(T.VPair{kk, T.VBool{a1}}, T.VPair{kk, T.VBool{a1}},
        D1.own.rows(tt), tt, gg, tb,
        {==},
        r2.own.pass(tt, gg, tb))
    case T.VPair{+kk, T.VWhen{+a1}} <> +tt:
      r2.cc(T.VPair{kk, T.VWhen{a1}}, T.VPair{kk, T.VWhen{a1}},
        D1.own.rows(tt), tt, gg, tb,
        {==},
        r2.own.pass(tt, gg, tb))
    case T.VPair{+kk, T.VArr{+a1}} <> +tt:
      r2.cc(T.VPair{kk, T.VArr{D1.own.rows(a1)}}, T.VPair{kk, T.VArr{a1}},
        D1.own.rows(tt), tt, gg, tb,
        Equal.cong(String, String, zz => r2.key(tb, T.key(kk) ++ " = [" ++ zz ++ "]", gg),
          T.render.go(D1.own.rows(a1), ", ", False{}), T.render.go(a1, ", ", False{}),
          r2.own.go(a1, ", ", False{})),
        r2.own.pass(tt, gg, tb))
    case T.VPair{+kk, T.VInl{+a1}} <> +tt:
      r2.cc(T.VPair{kk, T.VInl{D1.own.rows(a1)}}, T.VPair{kk, T.VInl{a1}},
        D1.own.rows(tt), tt, gg, tb,
        Equal.cong(String, String, zz => r2.key(tb, T.key(kk) ++ " = {" ++ zz ++ "}", gg),
          T.render.go(D1.own.rows(a1), ", ", False{}), T.render.go(a1, ", ", False{}),
          r2.own.go(a1, ", ", False{})),
        r2.own.pass(tt, gg, tb))
    case T.VPair{+kk, T.VHead{+a1, +a2}} <> +tt:
      r2.cc(T.VPair{kk, T.VHead{a1, D1.own.rows(a2)}}, T.VPair{kk, T.VHead{a1, a2}},
        D1.own.rows(tt), tt, gg, tb,
        Equal.cong(String, String, zz => r2.tab(tb, "[" ++ a1 ++ "]\n" ++ zz),
          T.render.both(D1.own.rows(a2), "\n", True{}), T.render.both(a2, "\n", True{}),
          r2.app2(r2.P(D1.own.rows(a2), "\n", False{}), r2.P(a2, "\n", False{}),
            r2.P(D1.own.rows(a2), "\n", True{}), r2.P(a2, "\n", True{}),
            r2.own.pass(a2, "\n", False{}), r2.own.pass(a2, "\n", True{}))),
        r2.own.pass(tt, gg, tb))
    case T.VPair{+kk, T.VAot{+a1, +a2}} <> +tt:
      r2.cc(T.VPair{kk, T.VAot{a1, D1.own.rows(a2)}}, T.VPair{kk, T.VAot{a1, a2}},
        D1.own.rows(tt), tt, gg, tb,
        {==},
        r2.own.pass(tt, gg, tb))
    case T.VPair{+kk, T.VAots{+a1, +a2}} <> +tt:
      r2.cc(T.VPair{kk, T.VAots{a1, D1.own.rows(a2)}}, T.VPair{kk, T.VAots{a1, a2}},
        D1.own.rows(tt), tt, gg, tb,
        Equal.cong(String, String, zz => r2.tab(tb, zz),
          T.render.both(D1.own.rows(a2), "\n", True{}), T.render.both(a2, "\n", True{}),
          r2.app2(r2.P(D1.own.rows(a2), "\n", False{}), r2.P(a2, "\n", False{}),
            r2.P(D1.own.rows(a2), "\n", True{}), r2.P(a2, "\n", True{}),
            r2.own.pass(a2, "\n", False{}), r2.own.pass(a2, "\n", True{}))),
        r2.own.pass(tt, gg, tb))
    case T.VPair{+kk, T.VPair{+a1, +a2}} <> +tt:
      r2.cc(T.VPair{kk, T.VPair{a1, a2}}, T.VPair{kk, T.VPair{a1, a2}},
        D1.own.rows(tt), tt, gg, tb,
        {==},
        r2.own.pass(tt, gg, tb))
    case T.VStr{+a1} <> +tt:
      r2.cc(T.VStr{a1}, T.VStr{a1},
        D1.own.rows(tt), tt, gg, tb,
        {==},
        r2.own.pass(tt, gg, tb))
    case T.VSpan{+a1, +a2} <> +tt:
      r2.cc(T.VStr{T.span.str(a1, a2, U32.is_zero(a2))}, T.VSpan{a1, a2},
        D1.own.rows(tt), tt, gg, tb,
        Equal.cong(String, String, zz => r2.key(tb, zz, gg),
          T.key.basic(T.span.str(a1, a2, U32.is_zero(a2))), T.span.quote(a1, a2),
          Equal.sym(String, T.span.quote(a1, a2), T.key.basic(T.span.str(a1, a2, U32.is_zero(a2))),
            L3.span_quote_basic(a1, a2))),
        r2.own.pass(tt, gg, tb))
    case T.VInt{+a1, +a2} <> +tt:
      r2.cc(T.VInt{a1, a2}, T.VInt{a1, a2},
        D1.own.rows(tt), tt, gg, tb,
        {==},
        r2.own.pass(tt, gg, tb))
    case T.VFlo{+a1, +a2} <> +tt:
      r2.cc(T.VFlo{a1, a2}, T.VFlo{a1, a2},
        D1.own.rows(tt), tt, gg, tb,
        {==},
        r2.own.pass(tt, gg, tb))
    case T.VBool{+a1} <> +tt:
      r2.cc(T.VBool{a1}, T.VBool{a1},
        D1.own.rows(tt), tt, gg, tb,
        {==},
        r2.own.pass(tt, gg, tb))
    case T.VWhen{+a1} <> +tt:
      r2.cc(T.VWhen{a1}, T.VWhen{a1},
        D1.own.rows(tt), tt, gg, tb,
        {==},
        r2.own.pass(tt, gg, tb))
    case T.VArr{+a1} <> +tt:
      r2.cc(T.VArr{D1.own.rows(a1)}, T.VArr{a1},
        D1.own.rows(tt), tt, gg, tb,
        Equal.cong(String, String, zz => r2.key(tb, "[" ++ zz ++ "]", gg),
          T.render.go(D1.own.rows(a1), ", ", False{}), T.render.go(a1, ", ", False{}),
          r2.own.go(a1, ", ", False{})),
        r2.own.pass(tt, gg, tb))
    case T.VInl{+a1} <> +tt:
      r2.cc(T.VInl{D1.own.rows(a1)}, T.VInl{a1},
        D1.own.rows(tt), tt, gg, tb,
        Equal.cong(String, String, zz => r2.key(tb, "{" ++ zz ++ "}", gg),
          T.render.go(D1.own.rows(a1), ", ", False{}), T.render.go(a1, ", ", False{}),
          r2.own.go(a1, ", ", False{})),
        r2.own.pass(tt, gg, tb))
    case T.VHead{+a1, +a2} <> +tt:
      r2.cc(T.VHead{a1, D1.own.rows(a2)}, T.VHead{a1, a2},
        D1.own.rows(tt), tt, gg, tb,
        {==},
        r2.own.pass(tt, gg, tb))
    case T.VAot{+a1, +a2} <> +tt:
      r2.cc(T.VAot{a1, D1.own.rows(a2)}, T.VAot{a1, a2},
        D1.own.rows(tt), tt, gg, tb,
        Equal.cong(String, String, zz => r2.tab(tb, "[[" ++ a1 ++ "]]\n" ++ zz),
          T.render.both(D1.own.rows(a2), "\n", True{}), T.render.both(a2, "\n", True{}),
          r2.app2(r2.P(D1.own.rows(a2), "\n", False{}), r2.P(a2, "\n", False{}),
            r2.P(D1.own.rows(a2), "\n", True{}), r2.P(a2, "\n", True{}),
            r2.own.pass(a2, "\n", False{}), r2.own.pass(a2, "\n", True{}))),
        r2.own.pass(tt, gg, tb))
    case T.VAots{+a1, +a2} <> +tt:
      r2.cc(T.VAots{a1, D1.own.rows(a2)}, T.VAots{a1, a2},
        D1.own.rows(tt), tt, gg, tb,
        {==},
        r2.own.pass(tt, gg, tb))

# render.both writes rows read out as it writes the rows
def r2.own.both(
  +ys: List<&2, T.Val>
) -> {T.render.both(D1.own.rows(ys), "\n", True{}) == T.render.both(ys, "\n", True{}) : String}:
  r2.app2(r2.P(D1.own.rows(ys), "\n", False{}), r2.P(ys, "\n", False{}), r2.P(D1.own.rows(ys), "\n", True{}),
    r2.P(ys, "\n", True{}), r2.own.pass(ys, "\n", False{}), r2.own.pass(ys, "\n", True{}))

# render writes a document read out as it writes the document
def r2.rown(dd: T.Doc) -> {T.render(D1.own(dd)) == T.render(dd) : String}:
  match dd:
    case T.Doc{_b, +rs}:
      r2.own.both(rs)

# the pass that writes keys writes the pairs canon keeps as it writes the
# table: it writes nothing for a table or an array of tables
def r2.keysF(
  xs: List<&2, T.Val>,
  +gg: String
) -> {r2.P(D2.canon.keys(xs), gg, False{}) == r2.P(xs, gg, False{}) : String}:
  match xs:
    case []:
      {==}
    case T.VPair{+kk, T.VStr{+a1}} <> +tt:
      r2.cc(T.VPair{kk, T.VStr{a1}}, T.VPair{kk, T.VStr{a1}}, D2.canon.keys(tt), tt, gg, False{}, {==},
        r2.keysF(tt, gg))
    case T.VPair{+kk, T.VSpan{+a1, +a2}} <> +tt:
      r2.cc(T.VPair{kk, T.VSpan{a1, a2}}, T.VPair{kk, T.VSpan{a1, a2}}, D2.canon.keys(tt), tt, gg, False{}, {==},
        r2.keysF(tt, gg))
    case T.VPair{+kk, T.VInt{+a1, +a2}} <> +tt:
      r2.cc(T.VPair{kk, T.VInt{a1, a2}}, T.VPair{kk, T.VInt{a1, a2}}, D2.canon.keys(tt), tt, gg, False{}, {==},
        r2.keysF(tt, gg))
    case T.VPair{+kk, T.VFlo{+a1, +a2}} <> +tt:
      r2.cc(T.VPair{kk, T.VFlo{a1, a2}}, T.VPair{kk, T.VFlo{a1, a2}}, D2.canon.keys(tt), tt, gg, False{}, {==},
        r2.keysF(tt, gg))
    case T.VPair{+kk, T.VBool{+a1}} <> +tt:
      r2.cc(T.VPair{kk, T.VBool{a1}}, T.VPair{kk, T.VBool{a1}}, D2.canon.keys(tt), tt, gg, False{}, {==},
        r2.keysF(tt, gg))
    case T.VPair{+kk, T.VWhen{+a1}} <> +tt:
      r2.cc(T.VPair{kk, T.VWhen{a1}}, T.VPair{kk, T.VWhen{a1}}, D2.canon.keys(tt), tt, gg, False{}, {==},
        r2.keysF(tt, gg))
    case T.VPair{+kk, T.VArr{+a1}} <> +tt:
      r2.cc(T.VPair{kk, T.VArr{a1}}, T.VPair{kk, T.VArr{a1}}, D2.canon.keys(tt), tt, gg, False{}, {==},
        r2.keysF(tt, gg))
    case T.VPair{+kk, T.VInl{+a1}} <> +tt:
      r2.cc(T.VPair{kk, T.VInl{a1}}, T.VPair{kk, T.VInl{a1}}, D2.canon.keys(tt), tt, gg, False{}, {==},
        r2.keysF(tt, gg))
    case T.VPair{+kk, T.VHead{+a1, +a2}} <> +tt:
      r2.keysF(tt, gg)
    case T.VPair{+kk, T.VAot{+a1, +a2}} <> +tt:
      r2.cc(T.VPair{kk, T.VAot{a1, a2}}, T.VPair{kk, T.VAot{a1, a2}}, D2.canon.keys(tt), tt, gg, False{}, {==},
        r2.keysF(tt, gg))
    case T.VPair{+kk, T.VAots{+a1, +a2}} <> +tt:
      r2.keysF(tt, gg)
    case T.VPair{+kk, T.VPair{+a1, +a2}} <> +tt:
      r2.cc(T.VPair{kk, T.VPair{a1, a2}}, T.VPair{kk, T.VPair{a1, a2}}, D2.canon.keys(tt), tt, gg, False{}, {==},
        r2.keysF(tt, gg))
    case T.VStr{+a1} <> +tt:
      r2.cc(T.VStr{a1}, T.VStr{a1}, D2.canon.keys(tt), tt, gg, False{}, {==},
        r2.keysF(tt, gg))
    case T.VSpan{+a1, +a2} <> +tt:
      r2.cc(T.VSpan{a1, a2}, T.VSpan{a1, a2}, D2.canon.keys(tt), tt, gg, False{}, {==},
        r2.keysF(tt, gg))
    case T.VInt{+a1, +a2} <> +tt:
      r2.cc(T.VInt{a1, a2}, T.VInt{a1, a2}, D2.canon.keys(tt), tt, gg, False{}, {==},
        r2.keysF(tt, gg))
    case T.VFlo{+a1, +a2} <> +tt:
      r2.cc(T.VFlo{a1, a2}, T.VFlo{a1, a2}, D2.canon.keys(tt), tt, gg, False{}, {==},
        r2.keysF(tt, gg))
    case T.VBool{+a1} <> +tt:
      r2.cc(T.VBool{a1}, T.VBool{a1}, D2.canon.keys(tt), tt, gg, False{}, {==},
        r2.keysF(tt, gg))
    case T.VWhen{+a1} <> +tt:
      r2.cc(T.VWhen{a1}, T.VWhen{a1}, D2.canon.keys(tt), tt, gg, False{}, {==},
        r2.keysF(tt, gg))
    case T.VArr{+a1} <> +tt:
      r2.cc(T.VArr{a1}, T.VArr{a1}, D2.canon.keys(tt), tt, gg, False{}, {==},
        r2.keysF(tt, gg))
    case T.VInl{+a1} <> +tt:
      r2.cc(T.VInl{a1}, T.VInl{a1}, D2.canon.keys(tt), tt, gg, False{}, {==},
        r2.keysF(tt, gg))
    case T.VHead{+a1, +a2} <> +tt:
      r2.cc(T.VHead{a1, a2}, T.VHead{a1, a2}, D2.canon.keys(tt), tt, gg, False{}, {==},
        r2.keysF(tt, gg))
    case T.VAot{+a1, +a2} <> +tt:
      r2.cc(T.VAot{a1, a2}, T.VAot{a1, a2}, D2.canon.keys(tt), tt, gg, False{}, {==},
        r2.keysF(tt, gg))
    case T.VAots{+a1, +a2} <> +tt:
      r2.cc(T.VAots{a1, a2}, T.VAots{a1, a2}, D2.canon.keys(tt), tt, gg, False{}, {==},
        r2.keysF(tt, gg))

# the rest of a well-formed table's rows is well-formed
def r2.tl(
  hh: T.Val,
  +tt: List<&2, T.Val>,
  +hp: String,
  hw: {T.wf.go(hh <> tt, T.WfRows{hp}) == True{} : Bool}
) -> {T.wf.go(tt, T.WfRows{hp}) == True{} : Bool}:
  match hh:
    case T.VPair{+kk, T.VStr{+a1}}:
      M8.wt.more(Bool.and(T.wf.atom(T.VStr{a1}), T.wf.key(kk, tt)), _u => T.wf.go(tt, T.WfRows{hp}), hw)
    case T.VPair{+kk, T.VSpan{+a1, +a2}}:
      M8.wt.more(Bool.and(T.wf.atom(T.VSpan{a1, a2}), T.wf.key(kk, tt)), _u => T.wf.go(tt, T.WfRows{hp}), hw)
    case T.VPair{+kk, T.VInt{+a1, +a2}}:
      M8.wt.more(Bool.and(T.wf.atom(T.VInt{a1, a2}), T.wf.key(kk, tt)), _u => T.wf.go(tt, T.WfRows{hp}), hw)
    case T.VPair{+kk, T.VFlo{+a1, +a2}}:
      M8.wt.more(Bool.and(T.wf.atom(T.VFlo{a1, a2}), T.wf.key(kk, tt)), _u => T.wf.go(tt, T.WfRows{hp}), hw)
    case T.VPair{+kk, T.VBool{+a1}}:
      M8.wt.more(Bool.and(T.wf.atom(T.VBool{a1}), T.wf.key(kk, tt)), _u => T.wf.go(tt, T.WfRows{hp}), hw)
    case T.VPair{+kk, T.VWhen{+a1}}:
      M8.wt.more(Bool.and(T.wf.atom(T.VWhen{a1}), T.wf.key(kk, tt)), _u => T.wf.go(tt, T.WfRows{hp}), hw)
    case T.VPair{+kk, T.VArr{+a1}}:
      M8.wt.more(T.wf.go(a1, T.WfItems{}), _v => T.wf.go(tt, T.WfRows{hp}), M8.wt.more(T.wf.key(kk, tt),
        _u => T.wf.then(T.wf.go(a1, T.WfItems{}), _v => T.wf.go(tt, T.WfRows{hp})), hw))
    case T.VPair{+kk, T.VInl{+a1}}:
      M8.wt.more(T.wf.go(a1, T.WfInl{}), _v => T.wf.go(tt, T.WfRows{hp}), M8.wt.more(T.wf.key(kk, tt),
        _u => T.wf.then(T.wf.go(a1, T.WfInl{}), _v => T.wf.go(tt, T.WfRows{hp})), hw))
    case T.VPair{+kk, T.VHead{+a1, +a2}}:
      M8.wt.more(T.wf.go(a2, T.WfRows{a1}), _v => T.wf.go(tt, T.WfRows{hp}),
        M8.wt.more(Bool.and(T.wf.key(kk, tt), T.str.eq(a1, T.tree.pre(hp, kk))),
          _u => T.wf.then(T.wf.go(a2, T.WfRows{a1}), _v => T.wf.go(tt, T.WfRows{hp})), hw))
    case T.VPair{+kk, T.VAot{+a1, +a2}}:
      Eq.bit.absurd(&2, {T.wf.go(tt, T.WfRows{hp}) == True{} : Bool}, hw)
    case T.VPair{+kk, T.VAots{+a1, +a2}}:
      M8.wt.more(T.wf.go(a2, T.WfElems{a1}), _v => T.wf.go(tt, T.WfRows{hp}),
        M8.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, a2)),
          Bool.and(T.wf.key(kk, tt), T.str.eq(a1, T.tree.pre(hp, kk)))),
          _u => T.wf.then(T.wf.go(a2, T.WfElems{a1}), _v => T.wf.go(tt, T.WfRows{hp})), hw))
    case T.VPair{+kk, T.VPair{+a1, +a2}}:
      Eq.bit.absurd(&2, {T.wf.go(tt, T.WfRows{hp}) == True{} : Bool}, hw)
    case T.VStr{+a1}:
      Eq.bit.absurd(&2, {T.wf.go(tt, T.WfRows{hp}) == True{} : Bool}, hw)
    case T.VSpan{+a1, +a2}:
      Eq.bit.absurd(&2, {T.wf.go(tt, T.WfRows{hp}) == True{} : Bool}, hw)
    case T.VInt{+a1, +a2}:
      Eq.bit.absurd(&2, {T.wf.go(tt, T.WfRows{hp}) == True{} : Bool}, hw)
    case T.VFlo{+a1, +a2}:
      Eq.bit.absurd(&2, {T.wf.go(tt, T.WfRows{hp}) == True{} : Bool}, hw)
    case T.VBool{+a1}:
      Eq.bit.absurd(&2, {T.wf.go(tt, T.WfRows{hp}) == True{} : Bool}, hw)
    case T.VWhen{+a1}:
      Eq.bit.absurd(&2, {T.wf.go(tt, T.WfRows{hp}) == True{} : Bool}, hw)
    case T.VArr{+a1}:
      Eq.bit.absurd(&2, {T.wf.go(tt, T.WfRows{hp}) == True{} : Bool}, hw)
    case T.VInl{+a1}:
      Eq.bit.absurd(&2, {T.wf.go(tt, T.WfRows{hp}) == True{} : Bool}, hw)
    case T.VHead{+a1, +a2}:
      Eq.bit.absurd(&2, {T.wf.go(tt, T.WfRows{hp}) == True{} : Bool}, hw)
    case T.VAot{+a1, +a2}:
      Eq.bit.absurd(&2, {T.wf.go(tt, T.WfRows{hp}) == True{} : Bool}, hw)
    case T.VAots{+a1, +a2}:
      Eq.bit.absurd(&2, {T.wf.go(tt, T.WfRows{hp}) == True{} : Bool}, hw)

# the pass that writes tables writes nothing for the pairs canon keeps
def r2.keysT(
  xs: List<&2, T.Val>,
  +hp: String,
  +gg: String,
  +hw: {T.wf.go(xs, T.WfRows{hp}) == True{} : Bool}
) -> {r2.P(D2.canon.keys(xs), gg, True{}) == "" : String}:
  match xs:
    case []:
      {==}
    case T.VPair{+kk, T.VStr{+a1}} <> +tt:
      r2.keysT(tt, hp, gg, r2.tl(T.VPair{kk, T.VStr{a1}}, tt, hp, hw))
    case T.VPair{+kk, T.VSpan{+a1, +a2}} <> +tt:
      r2.keysT(tt, hp, gg, r2.tl(T.VPair{kk, T.VSpan{a1, a2}}, tt, hp, hw))
    case T.VPair{+kk, T.VInt{+a1, +a2}} <> +tt:
      r2.keysT(tt, hp, gg, r2.tl(T.VPair{kk, T.VInt{a1, a2}}, tt, hp, hw))
    case T.VPair{+kk, T.VFlo{+a1, +a2}} <> +tt:
      r2.keysT(tt, hp, gg, r2.tl(T.VPair{kk, T.VFlo{a1, a2}}, tt, hp, hw))
    case T.VPair{+kk, T.VBool{+a1}} <> +tt:
      r2.keysT(tt, hp, gg, r2.tl(T.VPair{kk, T.VBool{a1}}, tt, hp, hw))
    case T.VPair{+kk, T.VWhen{+a1}} <> +tt:
      r2.keysT(tt, hp, gg, r2.tl(T.VPair{kk, T.VWhen{a1}}, tt, hp, hw))
    case T.VPair{+kk, T.VArr{+a1}} <> +tt:
      r2.keysT(tt, hp, gg, r2.tl(T.VPair{kk, T.VArr{a1}}, tt, hp, hw))
    case T.VPair{+kk, T.VInl{+a1}} <> +tt:
      r2.keysT(tt, hp, gg, r2.tl(T.VPair{kk, T.VInl{a1}}, tt, hp, hw))
    case T.VPair{+kk, T.VHead{+a1, +a2}} <> +tt:
      r2.keysT(tt, hp, gg, r2.tl(T.VPair{kk, T.VHead{a1, a2}}, tt, hp, hw))
    case T.VPair{+kk, T.VAot{+a1, +a2}} <> +tt:
      Eq.bit.absurd(&2, {r2.P(D2.canon.keys(T.VPair{kk, T.VAot{a1, a2}} <> tt), gg, True{}) == "" : String}, hw)
    case T.VPair{+kk, T.VAots{+a1, +a2}} <> +tt:
      r2.keysT(tt, hp, gg, r2.tl(T.VPair{kk, T.VAots{a1, a2}}, tt, hp, hw))
    case T.VPair{+kk, T.VPair{+a1, +a2}} <> +tt:
      Eq.bit.absurd(&2, {r2.P(D2.canon.keys(T.VPair{kk, T.VPair{a1, a2}} <> tt), gg, True{}) == "" : String}, hw)
    case T.VStr{+a1} <> +tt:
      Eq.bit.absurd(&2, {r2.P(D2.canon.keys(T.VStr{a1} <> tt), gg, True{}) == "" : String}, hw)
    case T.VSpan{+a1, +a2} <> +tt:
      Eq.bit.absurd(&2, {r2.P(D2.canon.keys(T.VSpan{a1, a2} <> tt), gg, True{}) == "" : String}, hw)
    case T.VInt{+a1, +a2} <> +tt:
      Eq.bit.absurd(&2, {r2.P(D2.canon.keys(T.VInt{a1, a2} <> tt), gg, True{}) == "" : String}, hw)
    case T.VFlo{+a1, +a2} <> +tt:
      Eq.bit.absurd(&2, {r2.P(D2.canon.keys(T.VFlo{a1, a2} <> tt), gg, True{}) == "" : String}, hw)
    case T.VBool{+a1} <> +tt:
      Eq.bit.absurd(&2, {r2.P(D2.canon.keys(T.VBool{a1} <> tt), gg, True{}) == "" : String}, hw)
    case T.VWhen{+a1} <> +tt:
      Eq.bit.absurd(&2, {r2.P(D2.canon.keys(T.VWhen{a1} <> tt), gg, True{}) == "" : String}, hw)
    case T.VArr{+a1} <> +tt:
      Eq.bit.absurd(&2, {r2.P(D2.canon.keys(T.VArr{a1} <> tt), gg, True{}) == "" : String}, hw)
    case T.VInl{+a1} <> +tt:
      Eq.bit.absurd(&2, {r2.P(D2.canon.keys(T.VInl{a1} <> tt), gg, True{}) == "" : String}, hw)
    case T.VHead{+a1, +a2} <> +tt:
      Eq.bit.absurd(&2, {r2.P(D2.canon.keys(T.VHead{a1, a2} <> tt), gg, True{}) == "" : String}, hw)
    case T.VAot{+a1, +a2} <> +tt:
      Eq.bit.absurd(&2, {r2.P(D2.canon.keys(T.VAot{a1, a2} <> tt), gg, True{}) == "" : String}, hw)
    case T.VAots{+a1, +a2} <> +tt:
      Eq.bit.absurd(&2, {r2.P(D2.canon.keys(T.VAots{a1, a2} <> tt), gg, True{}) == "" : String}, hw)

# the pass that writes keys writes nothing for the tables canon keeps
def r2.tabsF(
  xs: List<&2, T.Val>,
  md: Bool,
  +hp: String,
  +gg: String
) -> {r2.P(M7.st.l(md, xs, hp), gg, False{}) == "" : String}:
  match xs md:
    case [] False{}:
      {==}
    case [] True{}:
      {==}
    case T.VPair{+kk, T.VStr{+a1}} <> +tt False{}:
      r2.tabsF(tt, False{}, hp, gg)
    case T.VPair{+kk, T.VStr{+a1}} <> +tt True{}:
      r2.tabsF(tt, True{}, hp, gg)
    case T.VPair{+kk, T.VSpan{+a1, +a2}} <> +tt False{}:
      r2.tabsF(tt, False{}, hp, gg)
    case T.VPair{+kk, T.VSpan{+a1, +a2}} <> +tt True{}:
      r2.tabsF(tt, True{}, hp, gg)
    case T.VPair{+kk, T.VInt{+a1, +a2}} <> +tt False{}:
      r2.tabsF(tt, False{}, hp, gg)
    case T.VPair{+kk, T.VInt{+a1, +a2}} <> +tt True{}:
      r2.tabsF(tt, True{}, hp, gg)
    case T.VPair{+kk, T.VFlo{+a1, +a2}} <> +tt False{}:
      r2.tabsF(tt, False{}, hp, gg)
    case T.VPair{+kk, T.VFlo{+a1, +a2}} <> +tt True{}:
      r2.tabsF(tt, True{}, hp, gg)
    case T.VPair{+kk, T.VBool{+a1}} <> +tt False{}:
      r2.tabsF(tt, False{}, hp, gg)
    case T.VPair{+kk, T.VBool{+a1}} <> +tt True{}:
      r2.tabsF(tt, True{}, hp, gg)
    case T.VPair{+kk, T.VWhen{+a1}} <> +tt False{}:
      r2.tabsF(tt, False{}, hp, gg)
    case T.VPair{+kk, T.VWhen{+a1}} <> +tt True{}:
      r2.tabsF(tt, True{}, hp, gg)
    case T.VPair{+kk, T.VArr{+a1}} <> +tt False{}:
      r2.tabsF(tt, False{}, hp, gg)
    case T.VPair{+kk, T.VArr{+a1}} <> +tt True{}:
      r2.tabsF(tt, True{}, hp, gg)
    case T.VPair{+kk, T.VInl{+a1}} <> +tt False{}:
      r2.tabsF(tt, False{}, hp, gg)
    case T.VPair{+kk, T.VInl{+a1}} <> +tt True{}:
      r2.tabsF(tt, True{}, hp, gg)
    case T.VPair{+kk, T.VHead{+a1, +a2}} <> +tt False{}:
      r2.tabsF(tt, False{}, hp, gg)
    case T.VPair{+kk, T.VHead{+a1, +a2}} <> +tt True{}:
      r2.tabsF(tt, True{}, hp, gg)
    case T.VPair{+kk, T.VAot{+a1, +a2}} <> +tt False{}:
      r2.tabsF(tt, False{}, hp, gg)
    case T.VPair{+kk, T.VAot{+a1, +a2}} <> +tt True{}:
      r2.tabsF(tt, True{}, hp, gg)
    case T.VPair{+kk, T.VAots{+a1, +a2}} <> +tt False{}:
      r2.tabsF(tt, False{}, hp, gg)
    case T.VPair{+kk, T.VAots{+a1, +a2}} <> +tt True{}:
      r2.tabsF(tt, True{}, hp, gg)
    case T.VPair{+kk, T.VPair{+a1, +a2}} <> +tt False{}:
      r2.tabsF(tt, False{}, hp, gg)
    case T.VPair{+kk, T.VPair{+a1, +a2}} <> +tt True{}:
      r2.tabsF(tt, True{}, hp, gg)
    case T.VStr{+a1} <> +tt False{}:
      r2.tabsF(tt, False{}, hp, gg)
    case T.VStr{+a1} <> +tt True{}:
      r2.tabsF(tt, True{}, hp, gg)
    case T.VSpan{+a1, +a2} <> +tt False{}:
      r2.tabsF(tt, False{}, hp, gg)
    case T.VSpan{+a1, +a2} <> +tt True{}:
      r2.tabsF(tt, True{}, hp, gg)
    case T.VInt{+a1, +a2} <> +tt False{}:
      r2.tabsF(tt, False{}, hp, gg)
    case T.VInt{+a1, +a2} <> +tt True{}:
      r2.tabsF(tt, True{}, hp, gg)
    case T.VFlo{+a1, +a2} <> +tt False{}:
      r2.tabsF(tt, False{}, hp, gg)
    case T.VFlo{+a1, +a2} <> +tt True{}:
      r2.tabsF(tt, True{}, hp, gg)
    case T.VBool{+a1} <> +tt False{}:
      r2.tabsF(tt, False{}, hp, gg)
    case T.VBool{+a1} <> +tt True{}:
      r2.tabsF(tt, True{}, hp, gg)
    case T.VWhen{+a1} <> +tt False{}:
      r2.tabsF(tt, False{}, hp, gg)
    case T.VWhen{+a1} <> +tt True{}:
      r2.tabsF(tt, True{}, hp, gg)
    case T.VArr{+a1} <> +tt False{}:
      r2.tabsF(tt, False{}, hp, gg)
    case T.VArr{+a1} <> +tt True{}:
      r2.tabsF(tt, True{}, hp, gg)
    case T.VInl{+a1} <> +tt False{}:
      r2.tabsF(tt, False{}, hp, gg)
    case T.VInl{+a1} <> +tt True{}:
      r2.tabsF(tt, True{}, hp, gg)
    case T.VHead{+a1, +a2} <> +tt False{}:
      r2.tabsF(tt, False{}, hp, gg)
    case T.VHead{+a1, +a2} <> +tt True{}:
      r2.tabsF(tt, True{}, hp, gg)
    case T.VAot{+a1, +a2} <> +tt False{}:
      r2.tabsF(tt, False{}, hp, gg)
    case T.VAot{+a1, +a2} <> +tt True{}:
      r2.tabsF(tt, True{}, hp, gg)
    case T.VAots{+a1, +a2} <> +tt False{}:
      r2.tabsF(tt, False{}, hp, gg)
    case T.VAots{+a1, +a2} <> +tt True{}:
      r2.tabsF(tt, True{}, hp, gg)

# the pass that writes keys writes nothing for an array's elements
def r2.elemsF(
  xs: List<&2, T.Val>,
  +hp: String,
  +gg: String,
  +hw: {T.wf.go(xs, T.WfElems{hp}) == True{} : Bool}
) -> {r2.P(xs, gg, False{}) == "" : String}:
  match xs:
    case []:
      {==}
    case T.VPair{+kk, T.VStr{+a1}} <> +tt:
      Eq.bit.absurd(&2, {r2.P(T.VPair{kk, T.VStr{a1}} <> tt, gg, False{}) == "" : String}, hw)
    case T.VPair{+kk, T.VSpan{+a1, +a2}} <> +tt:
      Eq.bit.absurd(&2, {r2.P(T.VPair{kk, T.VSpan{a1, a2}} <> tt, gg, False{}) == "" : String}, hw)
    case T.VPair{+kk, T.VInt{+a1, +a2}} <> +tt:
      Eq.bit.absurd(&2, {r2.P(T.VPair{kk, T.VInt{a1, a2}} <> tt, gg, False{}) == "" : String}, hw)
    case T.VPair{+kk, T.VFlo{+a1, +a2}} <> +tt:
      Eq.bit.absurd(&2, {r2.P(T.VPair{kk, T.VFlo{a1, a2}} <> tt, gg, False{}) == "" : String}, hw)
    case T.VPair{+kk, T.VBool{+a1}} <> +tt:
      Eq.bit.absurd(&2, {r2.P(T.VPair{kk, T.VBool{a1}} <> tt, gg, False{}) == "" : String}, hw)
    case T.VPair{+kk, T.VWhen{+a1}} <> +tt:
      Eq.bit.absurd(&2, {r2.P(T.VPair{kk, T.VWhen{a1}} <> tt, gg, False{}) == "" : String}, hw)
    case T.VPair{+kk, T.VArr{+a1}} <> +tt:
      Eq.bit.absurd(&2, {r2.P(T.VPair{kk, T.VArr{a1}} <> tt, gg, False{}) == "" : String}, hw)
    case T.VPair{+kk, T.VInl{+a1}} <> +tt:
      Eq.bit.absurd(&2, {r2.P(T.VPair{kk, T.VInl{a1}} <> tt, gg, False{}) == "" : String}, hw)
    case T.VPair{+kk, T.VHead{+a1, +a2}} <> +tt:
      Eq.bit.absurd(&2, {r2.P(T.VPair{kk, T.VHead{a1, a2}} <> tt, gg, False{}) == "" : String}, hw)
    case T.VPair{+kk, T.VAot{+a1, +a2}} <> +tt:
      Eq.bit.absurd(&2, {r2.P(T.VPair{kk, T.VAot{a1, a2}} <> tt, gg, False{}) == "" : String}, hw)
    case T.VPair{+kk, T.VAots{+a1, +a2}} <> +tt:
      Eq.bit.absurd(&2, {r2.P(T.VPair{kk, T.VAots{a1, a2}} <> tt, gg, False{}) == "" : String}, hw)
    case T.VPair{+kk, T.VPair{+a1, +a2}} <> +tt:
      Eq.bit.absurd(&2, {r2.P(T.VPair{kk, T.VPair{a1, a2}} <> tt, gg, False{}) == "" : String}, hw)
    case T.VStr{+a1} <> +tt:
      Eq.bit.absurd(&2, {r2.P(T.VStr{a1} <> tt, gg, False{}) == "" : String}, hw)
    case T.VSpan{+a1, +a2} <> +tt:
      Eq.bit.absurd(&2, {r2.P(T.VSpan{a1, a2} <> tt, gg, False{}) == "" : String}, hw)
    case T.VInt{+a1, +a2} <> +tt:
      Eq.bit.absurd(&2, {r2.P(T.VInt{a1, a2} <> tt, gg, False{}) == "" : String}, hw)
    case T.VFlo{+a1, +a2} <> +tt:
      Eq.bit.absurd(&2, {r2.P(T.VFlo{a1, a2} <> tt, gg, False{}) == "" : String}, hw)
    case T.VBool{+a1} <> +tt:
      Eq.bit.absurd(&2, {r2.P(T.VBool{a1} <> tt, gg, False{}) == "" : String}, hw)
    case T.VWhen{+a1} <> +tt:
      Eq.bit.absurd(&2, {r2.P(T.VWhen{a1} <> tt, gg, False{}) == "" : String}, hw)
    case T.VArr{+a1} <> +tt:
      Eq.bit.absurd(&2, {r2.P(T.VArr{a1} <> tt, gg, False{}) == "" : String}, hw)
    case T.VInl{+a1} <> +tt:
      Eq.bit.absurd(&2, {r2.P(T.VInl{a1} <> tt, gg, False{}) == "" : String}, hw)
    case T.VHead{+a1, +a2} <> +tt:
      Eq.bit.absurd(&2, {r2.P(T.VHead{a1, a2} <> tt, gg, False{}) == "" : String}, hw)
    case T.VAot{+a1, +a2} <> +tt:
      r2.elemsF(tt, hp, gg, M8.wt.more(T.wf.go(a2, T.WfRows{a1}), _v => T.wf.go(tt, T.WfElems{hp}),
        M8.wt.more(T.str.eq(a1, hp), _u => T.wf.then(T.wf.go(a2, T.WfRows{a1}), _v => T.wf.go(tt, T.WfElems{hp})), hw)))
    case T.VAots{+a1, +a2} <> +tt:
      Eq.bit.absurd(&2, {r2.P(T.VAots{a1, a2} <> tt, gg, False{}) == "" : String}, hw)

# render.both writes a well-formed table's rows reordered as canon does as it
# writes the rows, given that the pass that writes tables does
def r2.both(
  +rr: List<&2, T.Val>,
  +hp: String,
  +hw: {T.wf.go(rr, T.WfRows{hp}) == True{} : Bool},
  et: {r2.P(D2.canon.tabs(rr), "\n", True{}) == r2.P(rr, "\n", True{}) : String}
) -> {T.render.both(D2.canon.rows(rr), "\n", True{}) == T.render.both(rr, "\n", True{}) : String}:
  +kk = {D2.canon.keys(rr) : List<&2, T.Val>}
  +cc = {D2.canon.tabs(rr) : List<&2, T.Val>}
  r2.app2(r2.P(List.append(&2, T.Val, kk, cc), "\n", False{}), r2.P(rr, "\n", False{}),
    r2.P(List.append(&2, T.Val, kk, cc), "\n", True{}), r2.P(rr, "\n", True{}),
    Equal.trans(String, r2.P(List.append(&2, T.Val, kk, cc), "\n", False{}),
      String.append(r2.P(kk, "\n", False{}), r2.P(cc, "\n", False{})), r2.P(rr, "\n", False{}),
      r2.app(kk, cc, "\n", False{}),
      Equal.trans(String, String.append(r2.P(kk, "\n", False{}), r2.P(cc, "\n", False{})),
        String.append(r2.P(rr, "\n", False{}), ""), r2.P(rr, "\n", False{}),
        r2.app2(r2.P(kk, "\n", False{}), r2.P(rr, "\n", False{}), r2.P(cc, "\n", False{}), "",
          r2.keysF(rr, "\n"), r2.tabsF(rr, False{}, hp, "\n")),
        Eq.append_nil(r2.P(rr, "\n", False{})))),
    Equal.trans(String, r2.P(List.append(&2, T.Val, kk, cc), "\n", True{}),
      String.append(r2.P(kk, "\n", True{}), r2.P(cc, "\n", True{})), r2.P(rr, "\n", True{}),
      r2.app(kk, cc, "\n", True{}),
      r2.app2(r2.P(kk, "\n", True{}), "", r2.P(cc, "\n", True{}), r2.P(rr, "\n", True{}),
        r2.keysT(rr, hp, "\n", hw), et)))

# the pass that writes tables writes canon's tables as it writes the
# table's (md false), and canon's elements of an array as it writes the
# elements (md true): each one's header, then its rows reordered, which
# render.both writes as it writes them
def r2.tabs(
  xs: List<&2, T.Val>,
  md: Bool,
  +hp: String,
  +gg: String,
  +hw: {T.wf.go(xs, M9.st.at(md, hp)) == True{} : Bool}
) -> {r2.P(M7.st.l(md, xs, hp), gg, True{}) == r2.P(xs, gg, True{}) : String}:
  match xs md:
    case [] False{}:
      {==}
    case [] True{}:
      {==}
    case T.VPair{+kk, T.VStr{+a1}} <> +tt False{}:
      r2.tabs(tt, False{}, hp, gg, r2.tl(T.VPair{kk, T.VStr{a1}}, tt, hp, hw))
    case T.VPair{+kk, T.VStr{+a1}} <> +tt True{}:
      Eq.bit.absurd(&2, {r2.P(M7.st.l(True{}, T.VPair{kk, T.VStr{a1}} <> tt, hp), gg, True{})
        == r2.P(T.VPair{kk, T.VStr{a1}} <> tt, gg, True{}) : String}, hw)
    case T.VPair{+kk, T.VSpan{+a1, +a2}} <> +tt False{}:
      r2.tabs(tt, False{}, hp, gg, r2.tl(T.VPair{kk, T.VSpan{a1, a2}}, tt, hp, hw))
    case T.VPair{+kk, T.VSpan{+a1, +a2}} <> +tt True{}:
      Eq.bit.absurd(&2, {r2.P(M7.st.l(True{}, T.VPair{kk, T.VSpan{a1, a2}} <> tt, hp), gg, True{})
        == r2.P(T.VPair{kk, T.VSpan{a1, a2}} <> tt, gg, True{}) : String}, hw)
    case T.VPair{+kk, T.VInt{+a1, +a2}} <> +tt False{}:
      r2.tabs(tt, False{}, hp, gg, r2.tl(T.VPair{kk, T.VInt{a1, a2}}, tt, hp, hw))
    case T.VPair{+kk, T.VInt{+a1, +a2}} <> +tt True{}:
      Eq.bit.absurd(&2, {r2.P(M7.st.l(True{}, T.VPair{kk, T.VInt{a1, a2}} <> tt, hp), gg, True{})
        == r2.P(T.VPair{kk, T.VInt{a1, a2}} <> tt, gg, True{}) : String}, hw)
    case T.VPair{+kk, T.VFlo{+a1, +a2}} <> +tt False{}:
      r2.tabs(tt, False{}, hp, gg, r2.tl(T.VPair{kk, T.VFlo{a1, a2}}, tt, hp, hw))
    case T.VPair{+kk, T.VFlo{+a1, +a2}} <> +tt True{}:
      Eq.bit.absurd(&2, {r2.P(M7.st.l(True{}, T.VPair{kk, T.VFlo{a1, a2}} <> tt, hp), gg, True{})
        == r2.P(T.VPair{kk, T.VFlo{a1, a2}} <> tt, gg, True{}) : String}, hw)
    case T.VPair{+kk, T.VBool{+a1}} <> +tt False{}:
      r2.tabs(tt, False{}, hp, gg, r2.tl(T.VPair{kk, T.VBool{a1}}, tt, hp, hw))
    case T.VPair{+kk, T.VBool{+a1}} <> +tt True{}:
      Eq.bit.absurd(&2, {r2.P(M7.st.l(True{}, T.VPair{kk, T.VBool{a1}} <> tt, hp), gg, True{})
        == r2.P(T.VPair{kk, T.VBool{a1}} <> tt, gg, True{}) : String}, hw)
    case T.VPair{+kk, T.VWhen{+a1}} <> +tt False{}:
      r2.tabs(tt, False{}, hp, gg, r2.tl(T.VPair{kk, T.VWhen{a1}}, tt, hp, hw))
    case T.VPair{+kk, T.VWhen{+a1}} <> +tt True{}:
      Eq.bit.absurd(&2, {r2.P(M7.st.l(True{}, T.VPair{kk, T.VWhen{a1}} <> tt, hp), gg, True{})
        == r2.P(T.VPair{kk, T.VWhen{a1}} <> tt, gg, True{}) : String}, hw)
    case T.VPair{+kk, T.VArr{+a1}} <> +tt False{}:
      r2.tabs(tt, False{}, hp, gg, r2.tl(T.VPair{kk, T.VArr{a1}}, tt, hp, hw))
    case T.VPair{+kk, T.VArr{+a1}} <> +tt True{}:
      Eq.bit.absurd(&2, {r2.P(M7.st.l(True{}, T.VPair{kk, T.VArr{a1}} <> tt, hp), gg, True{})
        == r2.P(T.VPair{kk, T.VArr{a1}} <> tt, gg, True{}) : String}, hw)
    case T.VPair{+kk, T.VInl{+a1}} <> +tt False{}:
      r2.tabs(tt, False{}, hp, gg, r2.tl(T.VPair{kk, T.VInl{a1}}, tt, hp, hw))
    case T.VPair{+kk, T.VInl{+a1}} <> +tt True{}:
      Eq.bit.absurd(&2, {r2.P(M7.st.l(True{}, T.VPair{kk, T.VInl{a1}} <> tt, hp), gg, True{})
        == r2.P(T.VPair{kk, T.VInl{a1}} <> tt, gg, True{}) : String}, hw)
    case T.VPair{+kk, T.VHead{+a1, +a2}} <> +tt False{}:
      +hin = {M8.wt.more(Bool.and(T.wf.key(kk, tt), T.str.eq(a1, T.tree.pre(hp, kk))),
        _u => T.wf.then(T.wf.go(a2, T.WfRows{a1}), _v => T.wf.go(tt, T.WfRows{hp})), hw)
        : {T.wf.then(T.wf.go(a2, T.WfRows{a1}), _v => T.wf.go(tt, T.WfRows{hp})) == True{} : Bool}}
      +hwr = {M8.wt.ok(T.wf.go(a2, T.WfRows{a1}), _v => T.wf.go(tt, T.WfRows{hp}), hin)
        : {T.wf.go(a2, T.WfRows{a1}) == True{} : Bool}}
      r2.cc(T.VPair{kk, T.VHead{a1, D2.canon.rows(a2)}}, T.VPair{kk, T.VHead{a1, a2}},
        D2.canon.tabs(tt), tt, gg, True{},
        Equal.cong(String, String, zz => "[" ++ a1 ++ "]\n" ++ zz,
          T.render.both(D2.canon.rows(a2), "\n", True{}), T.render.both(a2, "\n", True{}),
          r2.both(a2, a1, hwr, r2.tabs(a2, False{}, a1, "\n", hwr))),
        r2.tabs(tt, False{}, hp, gg, M8.wt.more(T.wf.go(a2, T.WfRows{a1}), _v => T.wf.go(tt, T.WfRows{hp}), hin)))
    case T.VPair{+kk, T.VHead{+a1, +a2}} <> +tt True{}:
      Eq.bit.absurd(&2, {r2.P(M7.st.l(True{}, T.VPair{kk, T.VHead{a1, a2}} <> tt, hp), gg, True{})
        == r2.P(T.VPair{kk, T.VHead{a1, a2}} <> tt, gg, True{}) : String}, hw)
    case T.VPair{+kk, T.VAot{+a1, +a2}} <> +tt False{}:
      Eq.bit.absurd(&2, {r2.P(M7.st.l(False{}, T.VPair{kk, T.VAot{a1, a2}} <> tt, hp), gg, True{})
        == r2.P(T.VPair{kk, T.VAot{a1, a2}} <> tt, gg, True{}) : String}, hw)
    case T.VPair{+kk, T.VAot{+a1, +a2}} <> +tt True{}:
      Eq.bit.absurd(&2, {r2.P(M7.st.l(True{}, T.VPair{kk, T.VAot{a1, a2}} <> tt, hp), gg, True{})
        == r2.P(T.VPair{kk, T.VAot{a1, a2}} <> tt, gg, True{}) : String}, hw)
    case T.VPair{+kk, T.VAots{+a1, +a2}} <> +tt False{}:
      +hin = {M8.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, a2)),
        Bool.and(T.wf.key(kk, tt), T.str.eq(a1, T.tree.pre(hp, kk)))),
        _u => T.wf.then(T.wf.go(a2, T.WfElems{a1}), _v => T.wf.go(tt, T.WfRows{hp})), hw)
        : {T.wf.then(T.wf.go(a2, T.WfElems{a1}), _v => T.wf.go(tt, T.WfRows{hp})) == True{} : Bool}}
      +hwe = {M8.wt.ok(T.wf.go(a2, T.WfElems{a1}), _v => T.wf.go(tt, T.WfRows{hp}), hin)
        : {T.wf.go(a2, T.WfElems{a1}) == True{} : Bool}}
      r2.cc(T.VPair{kk, T.VAots{a1, D2.canon.go(a2, D2.CElems{a1})}}, T.VPair{kk, T.VAots{a1, a2}},
        D2.canon.tabs(tt), tt, gg, True{},
        r2.app2(r2.P(M7.st.l(True{}, a2, a1), "\n", False{}), r2.P(a2, "\n", False{}),
          r2.P(M7.st.l(True{}, a2, a1), "\n", True{}), r2.P(a2, "\n", True{}),
          Equal.trans(String, r2.P(M7.st.l(True{}, a2, a1), "\n", False{}), "", r2.P(a2, "\n", False{}),
            r2.tabsF(a2, True{}, a1, "\n"),
            Equal.sym(String, r2.P(a2, "\n", False{}), "", r2.elemsF(a2, a1, "\n", hwe))),
          r2.tabs(a2, True{}, a1, "\n", hwe)),
        r2.tabs(tt, False{}, hp, gg, M8.wt.more(T.wf.go(a2, T.WfElems{a1}), _v => T.wf.go(tt, T.WfRows{hp}), hin)))
    case T.VPair{+kk, T.VAots{+a1, +a2}} <> +tt True{}:
      Eq.bit.absurd(&2, {r2.P(M7.st.l(True{}, T.VPair{kk, T.VAots{a1, a2}} <> tt, hp), gg, True{})
        == r2.P(T.VPair{kk, T.VAots{a1, a2}} <> tt, gg, True{}) : String}, hw)
    case T.VPair{+kk, T.VPair{+a1, +a2}} <> +tt False{}:
      Eq.bit.absurd(&2, {r2.P(M7.st.l(False{}, T.VPair{kk, T.VPair{a1, a2}} <> tt, hp), gg, True{})
        == r2.P(T.VPair{kk, T.VPair{a1, a2}} <> tt, gg, True{}) : String}, hw)
    case T.VPair{+kk, T.VPair{+a1, +a2}} <> +tt True{}:
      Eq.bit.absurd(&2, {r2.P(M7.st.l(True{}, T.VPair{kk, T.VPair{a1, a2}} <> tt, hp), gg, True{})
        == r2.P(T.VPair{kk, T.VPair{a1, a2}} <> tt, gg, True{}) : String}, hw)
    case T.VStr{+a1} <> +tt False{}:
      Eq.bit.absurd(&2, {r2.P(M7.st.l(False{}, T.VStr{a1} <> tt, hp), gg, True{})
        == r2.P(T.VStr{a1} <> tt, gg, True{}) : String}, hw)
    case T.VStr{+a1} <> +tt True{}:
      Eq.bit.absurd(&2, {r2.P(M7.st.l(True{}, T.VStr{a1} <> tt, hp), gg, True{})
        == r2.P(T.VStr{a1} <> tt, gg, True{}) : String}, hw)
    case T.VSpan{+a1, +a2} <> +tt False{}:
      Eq.bit.absurd(&2, {r2.P(M7.st.l(False{}, T.VSpan{a1, a2} <> tt, hp), gg, True{})
        == r2.P(T.VSpan{a1, a2} <> tt, gg, True{}) : String}, hw)
    case T.VSpan{+a1, +a2} <> +tt True{}:
      Eq.bit.absurd(&2, {r2.P(M7.st.l(True{}, T.VSpan{a1, a2} <> tt, hp), gg, True{})
        == r2.P(T.VSpan{a1, a2} <> tt, gg, True{}) : String}, hw)
    case T.VInt{+a1, +a2} <> +tt False{}:
      Eq.bit.absurd(&2, {r2.P(M7.st.l(False{}, T.VInt{a1, a2} <> tt, hp), gg, True{})
        == r2.P(T.VInt{a1, a2} <> tt, gg, True{}) : String}, hw)
    case T.VInt{+a1, +a2} <> +tt True{}:
      Eq.bit.absurd(&2, {r2.P(M7.st.l(True{}, T.VInt{a1, a2} <> tt, hp), gg, True{})
        == r2.P(T.VInt{a1, a2} <> tt, gg, True{}) : String}, hw)
    case T.VFlo{+a1, +a2} <> +tt False{}:
      Eq.bit.absurd(&2, {r2.P(M7.st.l(False{}, T.VFlo{a1, a2} <> tt, hp), gg, True{})
        == r2.P(T.VFlo{a1, a2} <> tt, gg, True{}) : String}, hw)
    case T.VFlo{+a1, +a2} <> +tt True{}:
      Eq.bit.absurd(&2, {r2.P(M7.st.l(True{}, T.VFlo{a1, a2} <> tt, hp), gg, True{})
        == r2.P(T.VFlo{a1, a2} <> tt, gg, True{}) : String}, hw)
    case T.VBool{+a1} <> +tt False{}:
      Eq.bit.absurd(&2, {r2.P(M7.st.l(False{}, T.VBool{a1} <> tt, hp), gg, True{})
        == r2.P(T.VBool{a1} <> tt, gg, True{}) : String}, hw)
    case T.VBool{+a1} <> +tt True{}:
      Eq.bit.absurd(&2, {r2.P(M7.st.l(True{}, T.VBool{a1} <> tt, hp), gg, True{})
        == r2.P(T.VBool{a1} <> tt, gg, True{}) : String}, hw)
    case T.VWhen{+a1} <> +tt False{}:
      Eq.bit.absurd(&2, {r2.P(M7.st.l(False{}, T.VWhen{a1} <> tt, hp), gg, True{})
        == r2.P(T.VWhen{a1} <> tt, gg, True{}) : String}, hw)
    case T.VWhen{+a1} <> +tt True{}:
      Eq.bit.absurd(&2, {r2.P(M7.st.l(True{}, T.VWhen{a1} <> tt, hp), gg, True{})
        == r2.P(T.VWhen{a1} <> tt, gg, True{}) : String}, hw)
    case T.VArr{+a1} <> +tt False{}:
      Eq.bit.absurd(&2, {r2.P(M7.st.l(False{}, T.VArr{a1} <> tt, hp), gg, True{})
        == r2.P(T.VArr{a1} <> tt, gg, True{}) : String}, hw)
    case T.VArr{+a1} <> +tt True{}:
      Eq.bit.absurd(&2, {r2.P(M7.st.l(True{}, T.VArr{a1} <> tt, hp), gg, True{})
        == r2.P(T.VArr{a1} <> tt, gg, True{}) : String}, hw)
    case T.VInl{+a1} <> +tt False{}:
      Eq.bit.absurd(&2, {r2.P(M7.st.l(False{}, T.VInl{a1} <> tt, hp), gg, True{})
        == r2.P(T.VInl{a1} <> tt, gg, True{}) : String}, hw)
    case T.VInl{+a1} <> +tt True{}:
      Eq.bit.absurd(&2, {r2.P(M7.st.l(True{}, T.VInl{a1} <> tt, hp), gg, True{})
        == r2.P(T.VInl{a1} <> tt, gg, True{}) : String}, hw)
    case T.VHead{+a1, +a2} <> +tt False{}:
      Eq.bit.absurd(&2, {r2.P(M7.st.l(False{}, T.VHead{a1, a2} <> tt, hp), gg, True{})
        == r2.P(T.VHead{a1, a2} <> tt, gg, True{}) : String}, hw)
    case T.VHead{+a1, +a2} <> +tt True{}:
      Eq.bit.absurd(&2, {r2.P(M7.st.l(True{}, T.VHead{a1, a2} <> tt, hp), gg, True{})
        == r2.P(T.VHead{a1, a2} <> tt, gg, True{}) : String}, hw)
    case T.VAot{+a1, +a2} <> +tt False{}:
      Eq.bit.absurd(&2, {r2.P(M7.st.l(False{}, T.VAot{a1, a2} <> tt, hp), gg, True{})
        == r2.P(T.VAot{a1, a2} <> tt, gg, True{}) : String}, hw)
    case T.VAot{+a1, +a2} <> +tt True{}:
      +hin = {M8.wt.more(T.str.eq(a1, hp),
        _u => T.wf.then(T.wf.go(a2, T.WfRows{a1}), _v => T.wf.go(tt, T.WfElems{hp})), hw)
        : {T.wf.then(T.wf.go(a2, T.WfRows{a1}), _v => T.wf.go(tt, T.WfElems{hp})) == True{} : Bool}}
      +hwr = {M8.wt.ok(T.wf.go(a2, T.WfRows{a1}), _v => T.wf.go(tt, T.WfElems{hp}), hin)
        : {T.wf.go(a2, T.WfRows{a1}) == True{} : Bool}}
      +heq = {M2.str.eq.true(a1, hp, M8.wt.ok(T.str.eq(a1, hp),
        _u => T.wf.then(T.wf.go(a2, T.WfRows{a1}), _v => T.wf.go(tt, T.WfElems{hp})), hw)) : {a1 == hp : String}}
      r2.cc(T.VAot{hp, D2.canon.rows(a2)}, T.VAot{a1, a2}, D2.canon.go(tt, D2.CElems{hp}), tt, gg,
        True{},
        Equal.trans(String, "[[" ++ hp ++ "]]\n" ++ T.render.both(D2.canon.rows(a2), "\n", True{}),
          "[[" ++ a1 ++ "]]\n" ++ T.render.both(D2.canon.rows(a2), "\n", True{}),
          "[[" ++ a1 ++ "]]\n" ++ T.render.both(a2, "\n", True{}),
          Equal.cong(String, String, zz => "[[" ++ zz ++ "]]\n" ++ T.render.both(D2.canon.rows(a2), "\n", True{}),
            hp, a1, Equal.sym(String, a1, hp, heq)),
          Equal.cong(String, String, zz => "[[" ++ a1 ++ "]]\n" ++ zz,
            T.render.both(D2.canon.rows(a2), "\n", True{}), T.render.both(a2, "\n", True{}),
            r2.both(a2, a1, hwr, r2.tabs(a2, False{}, a1, "\n", hwr)))),
        r2.tabs(tt, True{}, hp, gg, M8.wt.more(T.wf.go(a2, T.WfRows{a1}), _v => T.wf.go(tt, T.WfElems{hp}), hin)))
    case T.VAots{+a1, +a2} <> +tt False{}:
      Eq.bit.absurd(&2, {r2.P(M7.st.l(False{}, T.VAots{a1, a2} <> tt, hp), gg, True{})
        == r2.P(T.VAots{a1, a2} <> tt, gg, True{}) : String}, hw)
    case T.VAots{+a1, +a2} <> +tt True{}:
      Eq.bit.absurd(&2, {r2.P(M7.st.l(True{}, T.VAots{a1, a2} <> tt, hp), gg, True{})
        == r2.P(T.VAots{a1, a2} <> tt, gg, True{}) : String}, hw)

# render writes canon of a well-formed document as it writes the document
def r2.rcanon(
  +ee: String,
  +xs: List<&2, T.Val>,
  +ww: {T.wf(T.Doc{ee, xs}) == True{} : Bool}
) -> {T.render(D2.canon(T.Doc{ee, xs})) == T.render(T.Doc{ee, xs}) : String}:
  Equal.trans(String, T.render.both(D1.own.rows(D2.canon.rows(xs)), "\n", True{}),
    T.render.both(D2.canon.rows(xs), "\n", True{}), T.render.both(xs, "\n", True{}),
    r2.own.both(D2.canon.rows(xs)), r2.both(xs, "", ww, r2.tabs(xs, False{}, "", "\n", ww)))

# a well-formed document whose text is short renders, reparses and renders to
# the same text
def r2.half2(
  dd: T.Doc,
  +ww: {T.wf(dd) == True{} : Bool},
  +hs: {D1.short(T.render(dd)) == True{} : Bool}
) -> {String.eq(T.render(T.parse(T.render(dd))), T.render(dd)) == True{} : Bool}:
  match dd:
    case T.Doc{+ee, +xs}:
      +pd = {T.parse(T.render(T.Doc{ee, xs})) : T.Doc}
      +er = {Equal.trans(String, T.render(pd), T.render(D1.own(pd)), T.render(T.Doc{ee, xs}),
        Equal.sym(String, T.render(D1.own(pd)), T.render(pd), r2.rown(pd)),
        Equal.trans(String, T.render(D1.own(pd)), T.render(D2.canon(T.Doc{ee, xs})), T.render(T.Doc{ee, xs}),
          Equal.cong(T.Doc, String, zz => T.render(zz), D1.own(pd), D2.canon(T.Doc{ee, xs}),
            L2.render_parse_canon(T.Doc{ee, xs}, ww, hs)),
          r2.rcanon(ee, xs, ww))) : {T.render(pd) == T.render(T.Doc{ee, xs}) : String}}
      Equal.trans(Bool, String.eq(T.render(pd), T.render(T.Doc{ee, xs})),
        String.eq(T.render(T.Doc{ee, xs}), T.render(T.Doc{ee, xs})), True{},
        Equal.cong(String, Bool, zz => String.eq(zz, T.render(T.Doc{ee, xs})), T.render(pd), T.render(T.Doc{ee, xs}),
          er),
        Eq.string_eq_self(T.render(T.Doc{ee, xs})))

# laws/ParseRenderParse.bend: parse_wf makes parse(t) well-formed, so render_parse gives the
# first half and r2.half2 the second
def Laws.parse_render_parse(t, h_u, h_s, h_r, ok):
  +ww = {L1.parse_wf(t, h_u, h_s, ok) : {T.wf(T.parse(t)) == True{} : Bool}}
  M4.and.tt(D2.same(T.parse(T.render(T.parse(t))), T.parse(t)),
    String.eq(T.render(T.parse(T.render(T.parse(t)))), T.render(T.parse(t))),
    Eq.and.right(String.is_empty(T.bad(T.parse(T.render(T.parse(t))))),
      D2.same(T.parse(T.render(T.parse(t))), T.parse(t)), L2.render_parse(T.parse(t), ww, h_r)),
    r2.half2(T.parse(t), ww, h_r))
