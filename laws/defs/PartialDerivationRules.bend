# the rules still open at each scanner position of a partial derivation of the
# grammar
import Base
import ../../main.bend as T
import ./AbnfGrammar.bend as D1
import ./AbnfWhitespace.bend as D2
import ./BareValueGrammar.bend as D3
import ./BlankAndControlChars.bend as D4
import ./GrammarDerivations.bend as D5
import ./KeySegmentSpelling.bend as D6

# The bound on a text's length. parse keeps a string render writes with no
# escape as a span of the text, whose length it counts in a U32, so the
# string must be short enough that the count does not wrap; laws/RenderThenParse.bend bounds
# the whole rendered text so.

# a character render writes as itself in a basic string: no control, no
# quotation mark and no backslash (esc_plain)
def plain.char(+cc: Char) -> Bool:
  Bool.not(Bool.or(D4.is_ctl(cc), Bool.or(Char.is_eq(cc, '"'), Char.is_eq(cc, '\\'))))

# a text of such characters
def plain.text(ss: String) -> Bool:
  match ss:
    case SNil{}:
      True{}
    case SCon{+hh, tt}:
      Bool.and(plain.char(hh), plain.text(tt))

# every string in the rows, at any depth and in every table, and every
# table's path, is short
def short.rows(xs: List<&2, T.Val>) -> Bool:
  match xs:
    case []:
      True{}
    case T.VPair{_n, T.VHead{pp, rr}} <> tt:
      Bool.and(D3.short(pp), Bool.and(short.rows(rr), short.rows(tt)))
    case T.VPair{_n, T.VAots{pp, es}} <> tt:
      Bool.and(D3.short(pp), Bool.and(short.rows(es), short.rows(tt)))
    case T.VAot{_p, rr} <> tt:
      Bool.and(short.rows(rr), short.rows(tt))
    case T.VPair{_n, vv} <> tt:
      Bool.and(D3.cv.short1(vv), short.rows(tt))
    case vv <> tt:
      Bool.and(D3.cv.short1(vv), short.rows(tt))

#
# The refusal direction of laws/ParsesExactlyTheGrammar.bend (docs/rfc/eztoml-grammar-proofs.md,
# REVIEW-G5 (a)): a text parse accepts has a derivation. It runs backward
# over the scan induction (sipr in PROOF.bend). r1.gp maps each scanner
# state to a grammar position: the rules it has open, innermost first, as a
# list of frames. r1.fill says which texts complete a position: for each
# frame, the parts of a derivation (Gd) that close its rule, then the rest
# of the text completing the frames under it, as Sigma types, so that a
# completion carries its parts. A step's obligation is local: a character
# the scanner takes from s to s' turns a completion of gp(s') into one of
# gp(s), and the frames a step does not touch are passed through untouched.
# The spike defines the positions of the header and key states, and of the
# top, line and comment states they start and end in; the value states are
# RfLater, which WP-R proper defines. A state no step reaches (one holding a
# character, one before the byte-order mark but not the start, a top-level
# state with a frame open) is RfAny and claims nothing; a state whose every
# text fails (a comment inside a header or a key) is RfNone.

# one open rule of a partial derivation
type R1Fr is Data:
  RfAny{}
  RfNone{}
  RfLater{}
  RfBom{}
  RfTop{}
  RfLines{}
  RfLineEnd{}
  RfComment{}
  RfHOpen{arr: Bool}
  RfHClose{arr: Bool}
  RfRBr{}
  RfWs{}
  RfKSeg{}
  RfKBare{}
  RfKAfter{}
  RfEq{}
  RfKBasic{}
  RfKLit{}
  RfKEsc{}
  RfKUni{uni: U32, left: U32}
  RfVal{}
  RfArrAfter{}
  RfInlAfter{}

# what follows an array item's trailing ws-comment-newline: its [ array-sep ]
# and nothing more (RaEnd), or array-sep and more array-values (RaMore)
type R1ATail is Data:
  RaEnd{sep: Bool}
  RaMore{vals: D5.GVal}

# what follows a keyval in an inline table: nothing more (RiEnd), or
# inline-table-sep and more inline-table-keyvals (RiMore)
type R1ITail is Data:
  RiEnd{}
  RiMore{w1: String, w2: String, kvs: D5.GVal}

# a header's opening brackets, read already: [ (arr False) or [[ (arr True)
def r1.open(arr: Bool, tail: String) -> String:
  match arr:
    case False{}:
      SCon{'[', tail}
    case True{}:
      SCon{'[', SCon{'[', tail}}

# a header's closing brackets: std-table-close's ] or array-table-close's ]]
def r1.close(arr: Bool, tail: String) -> String:
  match arr:
    case False{}:
      SCon{']', tail}
    case True{}:
      SCon{']', SCon{']', tail}}

# the characters of hexadecimal digits, then tail
def r1.hexs.text(hs: List<&2, D6.KHex>, tail: String) -> String:
  match hs:
    case []:
      tail
    case hx <> rest:
      SCon{D6.k3.hex.char(hx), r1.hexs.text(rest, tail)}

# the number read so far, then the digits, the most significant first
def r1.hexs.acc(hs: List<&2, D6.KHex>, +acc: U32) -> U32:
  match hs:
    case []:
      acc
    case hx <> rest:
      r1.hexs.acc(rest, D6.k3.hex.acc(acc, hx))

# whether there are exactly left digits
def r1.hexs.count(hs: List<&2, D6.KHex>, +left: U32) -> Bool:
  match hs:
    case []:
      U32.is_zero(left)
    case _hx <> rest:
      Bool.and(Bool.not(U32.is_zero(left)), r1.hexs.count(rest, U32.sub(left, 1)))

# an array item's tail's text
def r1.atail.text(at: R1ATail, tail: String) -> String:
  match at:
    case RaEnd{sep}:
      D5.g.sep.text(sep, tail)
    case RaMore{vals}:
      SCon{',', D5.g.val.text(vals, tail)}

# and its parts' rules
def r1.atail.ok(at: R1ATail) -> Bool:
  match at:
    case RaEnd{_s}:
      True{}
    case RaMore{vals}:
      D1.g.ok.val(vals, D1.RArrayValues{})

# an inline table keyval's tail's text
def r1.itail.text(it: R1ITail, tail: String) -> String:
  match it:
    case RiEnd{}:
      tail
    case RiMore{w1, w2, kvs}:
      String.append(w1, SCon{',', String.append(w2, D5.g.val.text(kvs, tail))})

# and its parts' rules
def r1.itail.ok(it: R1ITail) -> Bool:
  match it:
    case RiEnd{}:
      True{}
    case RiMore{w1, w2, kvs}:
      Bool.and(D2.abnf.ws(w1), Bool.and(D2.abnf.ws(w2), D1.g.ok.val(kvs, D1.RInlineTableKeyvals{})))

# the texts that complete a position: none left when every rule is closed;
# else the innermost rule's parts, then the rest completing the frames under
# it. RfTop: expression *( newline expression ); RfLines: *( newline
# expression ); RfLineEnd: an expression's ws [ comment ]; RfComment: the
# rest of a comment's characters; RfHOpen: a table header whose [ or [[ is
# read; RfHClose: ws and the header's ] or ]]; RfRBr: the second ] of ]];
# RfWs: ws; RfKSeg: a simple-key; RfKBare: the rest of an unquoted-key;
# RfKAfter: *( dot-sep simple-key ); RfEq: keyval-sep up to its =; RfKBasic,
# RfKLit: the rest of a quoted key and its closing quote; RfKEsc: an escape
# after its backslash, then RfKBasic's; RfKUni: the rest of a \u or \U
# escape's digits, then RfKBasic's; RfVal: ws val; RfArrAfter,
# RfInlAfter: the rest of the array or inline table a value is in
def r1.fill(fs: List<&2, R1Fr>, +text: String) -> Type:
  match fs:
    case []:
      {text == "" : String}
    case fr <> rest:
      match fr:
        case RfAny{}:
          Unit
        case RfNone{}:
          Empty
        case RfLater{}:
          Unit
        case RfBom{}:
          r1.fill(rest, D1.bom.drop(text))
        case RfTop{}:
          &ex: D5.GExpr -> &ls: List<&2, D5.GLine> -> &rr: String -> ({text == D5.g.expr.text(ex, D5.g.lines.text(ls,
              rr)) :
            String} & ({Bool.and(D1.g.ok.expr(ex), D1.g.ok.lines(ls)) == True{} : Bool} & r1.fill(rest, rr)))
        case RfLines{}:
          &ls: List<&2, D5.GLine> -> &rr: String -> ({text == D5.g.lines.text(ls, rr) : String} &
            ({D1.g.ok.lines(ls) == True{} : Bool} & r1.fill(rest, rr)))
        case RfLineEnd{}:
          &ww: String -> &cm: D5.GCom -> &rr: String -> ({text == String.append(ww, D5.g.com.text(cm, rr)) : String} &
            ({Bool.and(D2.abnf.ws(ww), D1.g.ok.com(cm)) == True{} : Bool} & r1.fill(rest, rr)))
        case RfComment{}:
          &bd: String -> &rr: String -> ({text == String.append(bd, rr) : String} &
            ({D1.g.ok.com(D5.GcSome{bd}) == True{} : Bool} & r1.fill(rest, rr)))
        case RfHOpen{arr}:
          &tb: D5.GTable -> &rr: String -> ({r1.open(arr, text) == D5.g.table.text(tb, rr) : String} &
            ({D1.g.ok.table(tb) == True{} : Bool} & r1.fill(rest, rr)))
        case RfHClose{arr}:
          &ww: String -> &rr: String -> ({text == String.append(ww, r1.close(arr, rr)) : String} &
            ({D2.abnf.ws(ww) == True{} : Bool} & r1.fill(rest, rr)))
        case RfRBr{}:
          &rr: String -> ({text == SCon{']', rr} : String} & r1.fill(rest, rr))
        case RfWs{}:
          &ww: String -> &rr: String -> ({text == String.append(ww, rr) : String} &
            ({D2.abnf.ws(ww) == True{} : Bool} & r1.fill(rest, rr)))
        case RfKSeg{}:
          &sg: D6.KSeg -> &rr: String -> ({text == D6.k3.seg.text(sg, rr) : String} &
            ({D1.g.ok.seg(sg) == True{} : Bool} & r1.fill(rest, rr)))
        case RfKBare{}:
          &ss: String -> &rr: String -> ({text == String.append(ss, rr) : String} &
            ({D3.abnf.all_unquoted_key_chars(ss) == True{} : Bool} & r1.fill(rest, rr)))
        case RfKAfter{}:
          &ds: List<&2, D5.GDotSep> -> &rr: String -> ({text == D5.g.dots.text(ds, rr) : String} &
            ({D1.g.ok.dots(ds) == True{} : Bool} & r1.fill(rest, rr)))
        case RfEq{}:
          &ww: String -> &rr: String -> ({text == String.append(ww, SCon{'=', rr}) : String} &
            ({D2.abnf.ws(ww) == True{} : Bool} & r1.fill(rest, rr)))
        case RfKBasic{}:
          &pl: List<&2, D6.KPiece> -> &rr: String -> ({text == D6.k3.pcs.text(pl, SCon{'"', rr}) : String} &
            ({Bool.and(D1.abnf.basic_string(pl), D1.prose.escapes_scalar(pl)) == True{} : Bool} & r1.fill(rest, rr)))
        case RfKLit{}:
          &ss: String -> &rr: String -> ({text == String.append(ss, SCon{'\'', rr}) : String} &
            ({D1.abnf.literal_string(ss) == True{} : Bool} & r1.fill(rest, rr)))
        case RfKEsc{}:
          &pp: D6.KPiece -> &pl: List<&2, D6.KPiece> -> &rr: String -> ({SCon{'\\', text} == D6.k3.pc.text(pp,
            D6.k3.pcs.text(pl, SCon{'"', rr})) : String} & ({Bool.and(D1.abnf.basic_string(pp <> pl),
            D1.prose.escapes_scalar(pp <> pl)) == True{} : Bool} & r1.fill(rest, rr)))
        case RfKUni{uni, left}:
          &hs: List<&2, D6.KHex> -> &pl: List<&2, D6.KPiece> -> &rr: String -> ({text == r1.hexs.text(hs,
            D6.k3.pcs.text(pl, SCon{'"', rr})) : String} & ({Bool.and(r1.hexs.count(hs, left),
            Bool.and(D6.k3.scalar(r1.hexs.acc(hs, uni)), Bool.and(D1.abnf.basic_string(pl),
                D1.prose.escapes_scalar(pl))))
            == True{} : Bool} & r1.fill(rest, rr)))
        case RfVal{}:
          &ww: String -> &vv: D5.GVal -> &rr: String -> ({text == String.append(ww, D5.g.val.text(vv, rr)) : String} &
            ({Bool.and(D2.abnf.ws(ww), D1.g.ok.val(vv, D1.RVal{})) == True{} : Bool} & r1.fill(rest, rr)))
        case RfArrAfter{}:
          &wb: List<&2, D5.GWcn> -> &at: R1ATail -> &wn: List<&2, D5.GWcn> -> &rr: String -> ({text ==
            D5.g.wcn.text(wb, r1.atail.text(at, D5.g.wcn.text(wn, SCon{']', rr}))) : String} &
            ({Bool.and(D1.g.ok.wcn(wb), Bool.and(r1.atail.ok(at), D1.g.ok.wcn(wn))) == True{} : Bool} &
            r1.fill(rest, rr)))
        case RfInlAfter{}:
          &it: R1ITail -> &ww: String -> &rr: String -> ({text == r1.itail.text(it, String.append(ww,
            SCon{Chr{125}, rr})) : String} & ({Bool.and(r1.itail.ok(it), D2.abnf.ws(ww)) == True{} : Bool} &
            r1.fill(rest, rr)))

# the rules still open after an expression: ws [ comment ], then the lines
def r1.eol() -> List<&2, R1Fr>:
  [RfLineEnd{}, RfLines{}]

# the rules still open after a value, in the frames of the arrays and
# inline tables it is in, innermost first
def r1.after(stack: List<&2, T.Ctx>) -> List<&2, R1Fr>:
  match stack:
    case []:
      r1.eol()
    case T.CArr{_i, _p, _h} <> rest:
      RfArrAfter{} <> r1.after(rest)
    case T.CInl{_r, _p, _h} <> rest:
      RfInlAfter{} <> r1.after(rest)

# the rules after a header's key: ws and its closing brackets, then the line
def r1.hend(arr: Bool) -> List<&2, R1Fr>:
  RfHClose{arr} <> r1.eol()

# the rules after a keyval's key: keyval-sep and the value, in its frames
def r1.vend(stack: List<&2, T.Ctx>) -> List<&2, R1Fr>:
  RfEq{} <> (RfVal{} <> r1.after(stack))

# a top-level position, when no frame is open
def r1.gp.top(fs: List<&2, R1Fr>, stack: List<&2, T.Ctx>) -> List<&2, R1Fr>:
  match stack:
    case []:
      fs
    case _f <> _fs:
      [RfAny{}]

# a comment's: the rest of it and the lines after it at the top level or
# after an expression, doomed in a header or a key
def r1.gp.com(back: T.Lex, stack: List<&2, T.Ctx>) -> List<&2, R1Fr>:
  match back:
    case T.LTop{}:
      r1.gp.top([RfComment{}, RfLines{}], stack)
    case T.LLine{}:
      r1.gp.top([RfComment{}, RfLines{}], stack)
    case T.LHead{}:
      [RfNone{}]
    case T.LAfter{}:
      [RfNone{}]
    case _b:
      [RfLater{}]

# LHead's with no segment begun: the header right after [ (a second [ still
# possible) or [[
def r1.gp.head0(parts: List<&2, String>, arr: Bool) -> List<&2, R1Fr>:
  match parts:
    case []:
      RfHOpen{arr} <> r1.eol()
    case _p <> _ps:
      [RfAny{}]

# LHead's: the header right after its brackets, or a bare segment begun
def r1.gp.head(buf: List<&2, Char>, parts: List<&2, String>, arr: Bool) -> List<&2, R1Fr>:
  match buf:
    case []:
      r1.gp.head0(parts, arr)
    case _b <> _bs:
      RfKBare{} <> (RfKAfter{} <> r1.hend(arr))

# LHeadGap's: the rest of the key after a segment
def r1.gp.gap(buf: List<&2, Char>, arr: Bool) -> List<&2, R1Fr>:
  match buf:
    case []:
      RfKAfter{} <> r1.hend(arr)
    case _b <> _bs:
      [RfAny{}]

# LHeadR's with no segment read: doomed when none is in the buffer either
def r1.gp.hr0(buf: List<&2, Char>) -> List<&2, R1Fr>:
  match buf:
    case []:
      [RfNone{}]
    case _b <> _bs:
      RfRBr{} <> r1.eol()

# LHeadR's: the second ] of [[ ]]
def r1.gp.hr(parts: List<&2, String>, buf: List<&2, Char>) -> List<&2, R1Fr>:
  match parts:
    case []:
      r1.gp.hr0(buf)
    case _p <> _ps:
      RfRBr{} <> r1.eol()

# a segment in quotes: a basic or a literal one, then the key's rest
def r1.gp.q(qkind: T.QKind, ke: List<&2, R1Fr>) -> List<&2, R1Fr>:
  match qkind:
    case T.QBasic{}:
      RfKBasic{} <> (RfKAfter{} <> ke)
    case T.QLit{}:
      RfKLit{} <> (RfKAfter{} <> ke)
    case _q:
      [RfAny{}]

# an escape in a basic segment
def r1.gp.e(qkind: T.QKind, ke: List<&2, R1Fr>) -> List<&2, R1Fr>:
  match qkind:
    case T.QBasic{}:
      RfKEsc{} <> (RfKAfter{} <> ke)
    case _q:
      [RfAny{}]

# the hexadecimal digits still to read of a \u or \U escape; none left is
# a state no step reaches
def r1.gp.u0(zero: Bool, ke: List<&2, R1Fr>, uni: U32, left: U32) -> List<&2, R1Fr>:
  match zero:
    case True{}:
      [RfAny{}]
    case False{}:
      RfKUni{uni, left} <> (RfKAfter{} <> ke)

# the hexadecimal digits of a \u or \U escape in a basic segment
def r1.gp.u(qkind: T.QKind, ke: List<&2, R1Fr>, uni: U32, +left: U32) -> List<&2, R1Fr>:
  match qkind:
    case T.QBasic{}:
      r1.gp.u0(U32.is_zero(left), ke, uni, left)
    case _q:
      [RfAny{}]

# LKey's: a bare segment begun
def r1.gp.key(buf: List<&2, Char>, stack: List<&2, T.Ctx>) -> List<&2, R1Fr>:
  match buf:
    case []:
      [RfAny{}]
    case _b <> _bs:
      RfKBare{} <> (RfKAfter{} <> r1.vend(stack))

# LAfter's: the rest of a keyval's key, with nothing buffered; a state with
# a character buffered is one no step reaches
def r1.gp.aft(buf: List<&2, Char>, stack: List<&2, T.Ctx>) -> List<&2, R1Fr>:
  match buf:
    case []:
      RfKAfter{} <> r1.vend(stack)
    case _b <> _bs:
      [RfAny{}]

# LVal's: ws and a value, with nothing buffered; a state with a character
# buffered is one no step reaches
def r1.gp.val(buf: List<&2, Char>, stack: List<&2, T.Ctx>) -> List<&2, R1Fr>:
  match buf:
    case []:
      RfVal{} <> r1.after(stack)
    case _b <> _bs:
      [RfAny{}]

# the position of a scanner state's lex state and the fields it reads: at
# the top level or after an expression, with no frame open; in a comment; in
# a header's key (ending in r1.hend) or a keyval's key (ending in r1.vend):
# a segment begun, ws and a segment after a dot, the rest after a segment, a
# segment in quotes, an escape in a basic one and its hexadecimal digits;
# the second ] of [[ ]]; and a keyval's value
def r1.gp0(
  lex: T.Lex,
  back: T.Lex,
  qkind: T.QKind,
  stack: List<&2, T.Ctx>,
  parts: List<&2, String>,
  buf: List<&2, Char>,
  uni: U32,
  left: U32,
  arr: Bool
) -> List<&2, R1Fr>:
  match lex:
    case T.LTop{}:
      r1.gp.top([RfTop{}], stack)
    case T.LLine{}:
      r1.gp.top(r1.eol(), stack)
    case T.LCom{}:
      r1.gp.com(back, stack)
    case T.LHead{}:
      r1.gp.head(buf, parts, arr)
    case T.LHeadGap{}:
      r1.gp.gap(buf, arr)
    case T.LHeadDot{}:
      RfWs{} <> (RfKSeg{} <> (RfKAfter{} <> r1.hend(arr)))
    case T.LHeadR{}:
      r1.gp.hr(parts, buf)
    case T.LHeadQ{}:
      r1.gp.q(qkind, r1.hend(arr))
    case T.LHeadE{}:
      r1.gp.e(qkind, r1.hend(arr))
    case T.LHeadU{}:
      r1.gp.u(qkind, r1.hend(arr), uni, left)
    case T.LKey{}:
      r1.gp.key(buf, stack)
    case T.LKeyDot{}:
      RfWs{} <> (RfKSeg{} <> (RfKAfter{} <> r1.vend(stack)))
    case T.LAfter{}:
      r1.gp.aft(buf, stack)
    case T.LKeyQ{}:
      r1.gp.q(qkind, r1.vend(stack))
    case T.LKeyE{}:
      r1.gp.e(qkind, r1.vend(stack))
    case T.LKeyU{}:
      r1.gp.u(qkind, r1.vend(stack), uni, left)
    case T.LVal{}:
      r1.gp.val(buf, stack)
    case T.LSink{}:
      [RfAny{}]
    case _l:
      [RfLater{}]

# the start: the whole document, after one byte-order mark if there is one
def r1.gp.lead(lex: T.Lex, stack: List<&2, T.Ctx>, hold: T.Hold) -> List<&2, R1Fr>:
  match lex stack hold:
    case T.LTop{} Nil{} T.HNone{}:
      [RfBom{}, RfTop{}]
    case _l _s _h:
      [RfAny{}]

# a state past the start: none while a character is held, else its lex
# state's
def r1.gp.hold(
  hold: T.Hold,
  lex: T.Lex,
  back: T.Lex,
  qkind: T.QKind,
  stack: List<&2, T.Ctx>,
  parts: List<&2, String>,
  buf: List<&2, Char>,
  uni: U32,
  left: U32,
  arr: Bool
) -> List<&2, R1Fr>:
  match hold:
    case T.HChar{_c}:
      [RfAny{}]
    case T.HNone{}:
      r1.gp0(lex, back, qkind, stack, parts, buf, uni, left, arr)

# the position of a scanner state
def r1.gp(st: T.St) -> List<&2, R1Fr>:
  match st:
    case T.St{_b, _r, _h, _e, parts, buf, lex, back, qkind, stack, hold, uni, left, arr, lead}:
      match lead:
        case True{}:
          r1.gp.lead(lex, stack, hold)
        case False{}:
          r1.gp.hold(hold, lex, back, qkind, stack, parts, buf, uni, left, arr)

# the texts that complete a mode: a scanning state's position; after a
# carriage return, the line feed and then the state it reads to; a string's
# opening quote or span (the value states, RfLater's)
def r1.C(mode: T.Mode, +text: String) -> Type:
  match mode:
    case T.MScan{st}:
      r1.fill(r1.gp(st), text)
    case T.MCr{st}:
      &uu: String -> ({text == SCon{'\n', uu} : String} & r1.fill(r1.gp(T.read.fast(st, '\n')), uu))
    case T.MOpen{_ba, _q, _k, _bd, _rw, _hs, _he, _pt, _bf, _bk, _sk, _un, _lf, _at}:
      Unit
    case T.MEat{_ba, _q, _c, _n, _bd, _rw, _hs, _he, _pt, _k, _sk, _un, _lf, _at}:
      Unit

# WP-R (continued)
#
# The grammar positions of every scanner state (docs/rfc/eztoml-grammar-
# proofs.md, WP-R). r2.gp supersedes the spike's r1.gp: a frame is one of
# the spike's (R2Old) or one of the value states': an array or an inline
# table after its opening bracket (R2Arr, R2Inl) or after a comma (R2InlK),
# a newline after a comment in an array (R2Nl), a bare word begun (R2Word)
# or waiting after a date's space (R2Date), a string after one, two or three
# of its quotes (R2Str), and a multi-line string's body, escapes, folds and
# quotes (R2Mb*, R2Ml*, R2MEnd). The spike's thirteen states keep their
# positions (r2.lift of r1.gp's), so their obligations carry over; RfLater
# is gone from every state a step reaches.

# how far into a string's opening delimiter the scanner is: one quote, two,
# or the three of a multi-line string
type R2K is Data:
  SK1{}
  SK2{}
  SK3{}

# one open rule of a partial derivation: the spike's, or a value state's
type R2Fr is Data:
  R2Old{fr: R1Fr}
  R2Arr{}
  R2Inl{}
  R2InlK{}
  R2Nl{}
  R2Word{buf: List<&2, Char>}
  R2Date{buf: List<&2, Char>}
  R2Str{stage: R2K, basic: Bool}
  R2Mb{}
  R2MbEsc{}
  R2MbUni{uni: U32, left: U32}
  R2MbFold{}
  R2MbFold1{}
  R2MbQ{two: Bool}
  R2Ml{}
  R2MlQ{two: Bool}
  R2MEnd{qc: Char, nn: D3.R2N}

# the spike's frames, as frames of r2
def r2.lift(fs: List<&2, R1Fr>) -> List<&2, R2Fr>:
  match fs:
    case []:
      []
    case fr <> rest:
      R2Old{fr} <> r2.lift(rest)

# a position that claims nothing: a state no step reaches
def r2.any() -> List<&2, R2Fr>:
  [R2Old{RfAny{}}]

# a bare value: toml.abnf's boolean, date-time (within RFC 3339's ranges),
# float or integer (within signed 64 bits) rule, as g.ok.val says
def r2.word.ok(+cs: List<&2, Char>) -> Bool:
  Bool.or(D1.g.ok.val(D5.GvBoolean{cs}, D1.RVal{}), Bool.or(D1.g.ok.val(D5.GvDateTime{cs}, D1.RVal{}),
      Bool.or(D1.g.ok.val(D5.GvFloat{cs},
    D1.RVal{}), D1.g.ok.val(D5.GvInteger{cs}, D1.RVal{}))))

# the value node of a bare word, by the first rule it matches
def r2.wgv.pick(bo: Bool, dt: Bool, fl: Bool, +cs: List<&2, Char>) -> D5.GVal:
  match bo:
    case True{}:
      D5.GvBoolean{cs}
    case False{}:
      match dt:
        case True{}:
          D5.GvDateTime{cs}
        case False{}:
          match fl:
            case True{}:
              D5.GvFloat{cs}
            case False{}:
              D5.GvInteger{cs}

# the value node of a bare word
def r2.wgv(+cs: List<&2, Char>) -> D5.GVal:
  r2.wgv.pick(D1.g.ok.val(D5.GvBoolean{cs}, D1.RVal{}), D1.g.ok.val(D5.GvDateTime{cs}, D1.RVal{}),
      D1.g.ok.val(D5.GvFloat{cs}, D1.RVal{}), cs)

# after a date and its space: the word goes on with the space (ch), or it
# ended before the space and the rest follows the space
def r2.dok(ch: Bool, buf: List<&2, Char>, ww: List<&2, Char>) -> Bool:
  match ch:
    case True{}:
      r2.word.ok(List.reverse.go(&2, Char, ' ' <> buf, ww))
    case False{}:
      Bool.and(List.is_empty(&2, Char, ww), r2.word.ok(List.reverse.go(&2, Char, buf, [])))

# the text the frames under a date's word read: the space is theirs when
# the word ended before it
def r2.drr(ch: Bool, rr: String) -> String:
  match ch:
    case True{}:
      rr
    case False{}:
      SCon{' ', rr}

# whether a value node is an array
def r2.is.arr(gv: D5.GVal) -> Bool:
  match gv:
    case D5.GvArrayEmpty{_wn}:
      True{}
    case D5.GvArray{_vs, _wn}:
      True{}
    case _v:
      False{}

# an array's text after its [
def r2.arr.rest(gv: D5.GVal, rr: String) -> String:
  match gv:
    case D5.GvArrayEmpty{wn}:
      D5.g.wcn.text(wn, SCon{']', rr})
    case D5.GvArray{vals, wn}:
      D5.g.val.text(vals, D5.g.wcn.text(wn, SCon{']', rr}))
    case _v:
      rr

# whether a value node is an inline table
def r2.is.inl(gv: D5.GVal) -> Bool:
  match gv:
    case D5.GvInlineTableEmpty{_w1, _w2}:
      True{}
    case D5.GvInlineTable{_w1, _kv, _w2}:
      True{}
    case _v:
      False{}

# an inline table's text after its {
def r2.inl.rest(gv: D5.GVal, rr: String) -> String:
  match gv:
    case D5.GvInlineTableEmpty{w1, w2}:
      String.append(w1, String.append(w2, SCon{Chr{125}, rr}))
    case D5.GvInlineTable{w1, kvs, w2}:
      String.append(w1, D5.g.val.text(kvs, String.append(w2, SCon{Chr{125}, rr})))
    case _v:
      rr

# whether a string is of the basic forms (basic) or the literal ones, and
# fits the stage: after two quotes a one-line string is empty, after three
# it is multi-line
def r2.s.fit(stage: R2K, basic: Bool, st: D5.GString) -> Bool:
  match stage st:
    case SK1{} D5.GsMlBasic{_nl, _b}:
      basic
    case SK1{} D5.GsBasic{_p}:
      basic
    case SK1{} D5.GsMlLiteral{_nl, _b}:
      Bool.not(basic)
    case SK1{} D5.GsLiteral{_t}:
      Bool.not(basic)
    case SK2{} D5.GsMlBasic{_nl, _b}:
      basic
    case SK2{} D5.GsBasic{pl}:
      Bool.and(basic, List.is_empty(&2, D6.KPiece, pl))
    case SK2{} D5.GsMlLiteral{_nl, _b}:
      Bool.not(basic)
    case SK2{} D5.GsLiteral{tx}:
      Bool.and(Bool.not(basic), String.is_empty(tx))
    case SK3{} D5.GsMlBasic{_nl, _b}:
      basic
    case SK3{} D5.GsMlLiteral{_nl, _b}:
      Bool.not(basic)
    case SK3{} _s:
      False{}

# a string's text after the quotes of its stage
def r2.s.rest(stage: R2K, st: D5.GString, rr: String) -> String:
  match stage st:
    case SK1{} D5.GsMlBasic{nl, body}:
      SCon{'"', SCon{'"', String.append(nl, D5.g.mlb.text(body, SCon{'"', SCon{'"', SCon{'"', rr}}}))}}
    case SK1{} D5.GsBasic{pl}:
      D6.k3.pcs.text(pl, SCon{'"', rr})
    case SK1{} D5.GsMlLiteral{nl, body}:
      SCon{'\'', SCon{'\'', String.append(nl, D5.g.mll.text(body, SCon{'\'', SCon{'\'', SCon{'\'', rr}}}))}}
    case SK1{} D5.GsLiteral{tx}:
      String.append(tx, SCon{'\'', rr})
    case SK2{} D5.GsMlBasic{nl, body}:
      SCon{'"', String.append(nl, D5.g.mlb.text(body, SCon{'"', SCon{'"', SCon{'"', rr}}}))}
    case SK2{} D5.GsMlLiteral{nl, body}:
      SCon{'\'', String.append(nl, D5.g.mll.text(body, SCon{'\'', SCon{'\'', SCon{'\'', rr}}}))}
    case SK3{} D5.GsMlBasic{nl, body}:
      String.append(nl, D5.g.mlb.text(body, SCon{'"', SCon{'"', SCon{'"', rr}}}))
    case SK3{} D5.GsMlLiteral{nl, body}:
      String.append(nl, D5.g.mll.text(body, SCon{'\'', SCon{'\'', SCon{'\'', rr}}}))
    case _k _s:
      rr

# a multi-line basic body's rules
def r2.mb.ok(+body: List<&2, D5.GMlb>) -> Bool:
  Bool.and(D1.abnf.ml_basic_body(body, False{}), D1.prose.mlb_escapes_scalar(body))

# a multi-line basic body, then its closing delimiter and tail
def r2.mb.text(body: List<&2, D5.GMlb>, tail: String) -> String:
  D5.g.mlb.text(body, SCon{'"', SCon{'"', SCon{'"', tail}}})

# a multi-line literal body, then its closing delimiter and tail
def r2.ml.text(body: List<&2, D5.GMll>, tail: String) -> String:
  D5.g.mll.text(body, SCon{'\'', SCon{'\'', SCon{'\'', tail}}})

# nn quotes qc, then tail
def r2.qs(+qc: Char, nn: D3.R2N, tail: String) -> String:
  match nn:
    case D3.N0{}:
      tail
    case D3.N1{}:
      SCon{qc, tail}
    case D3.N2{}:
      SCon{qc, SCon{qc, tail}}

# at most two quotes in all after a closing delimiter: nn read, mm to come
def r2.n.le(nn: D3.R2N, mm: D3.R2N) -> Bool:
  match nn mm:
    case D3.N0{} _m:
      True{}
    case D3.N1{} D3.N2{}:
      False{}
    case D3.N1{} _m:
      True{}
    case D3.N2{} D3.N0{}:
      True{}
    case D3.N2{} _m:
      False{}

# the texts that complete a position: none left when every rule is closed;
# else the innermost rule's parts, then the rest completing the frames under
# it. R2Old: the spike's frame, as r1.fill reads it; R2Arr, R2Inl: an array
# or an inline table after its bracket; R2InlK: inline-table-keyvals after a
# comma, then ws and }; R2Nl: a newline; R2Word: the rest of a bare word
# begun with the buffer's characters; R2Date: after a date and a space;
# R2Str: a string after the quotes of its stage; R2Mb, R2Ml: a multi-line
# body and its delimiter; R2MbEsc: after an escape's backslash; R2MbUni: the
# rest of a \u or \U escape's digits; R2MbFold, R2MbFold1: a line-ending
# backslash's ws, newline and blank space, before and after the newline;
# R2MbQ, R2MlQ: after one or two quotes in a body; R2MEnd: after the
# closing delimiter, up to two more quotes
def r2.fill(fs: List<&2, R2Fr>, +text: String) -> Type:
  match fs:
    case []:
      {text == "" : String}
    case fr <> rest:
      match fr:
        case R2Old{f1}:
          match f1:
            case RfAny{}:
              Unit
            case RfNone{}:
              Empty
            case RfLater{}:
              Unit
            case RfBom{}:
              r2.fill(rest, D1.bom.drop(text))
            case RfTop{}:
              &ex: D5.GExpr -> &ls: List<&2, D5.GLine> -> &rr: String -> ({text == D5.g.expr.text(ex,
                  D5.g.lines.text(ls, rr)) :
                String} & ({Bool.and(D1.g.ok.expr(ex), D1.g.ok.lines(ls)) == True{} : Bool} & r2.fill(rest, rr)))
            case RfLines{}:
              &ls: List<&2, D5.GLine> -> &rr: String -> ({text == D5.g.lines.text(ls, rr) : String} &
                ({D1.g.ok.lines(ls) == True{} : Bool} & r2.fill(rest, rr)))
            case RfLineEnd{}:
              &ww: String -> &cm: D5.GCom -> &rr: String -> ({text == String.append(ww, D5.g.com.text(cm,
                  rr)) : String} &
                ({Bool.and(D2.abnf.ws(ww), D1.g.ok.com(cm)) == True{} : Bool} & r2.fill(rest, rr)))
            case RfComment{}:
              &bd: String -> &rr: String -> ({text == String.append(bd, rr) : String} &
                ({D1.g.ok.com(D5.GcSome{bd}) == True{} : Bool} & r2.fill(rest, rr)))
            case RfHOpen{arr}:
              &tb: D5.GTable -> &rr: String -> ({r1.open(arr, text) == D5.g.table.text(tb, rr) : String} &
                ({D1.g.ok.table(tb) == True{} : Bool} & r2.fill(rest, rr)))
            case RfHClose{arr}:
              &ww: String -> &rr: String -> ({text == String.append(ww, r1.close(arr, rr)) : String} &
                ({D2.abnf.ws(ww) == True{} : Bool} & r2.fill(rest, rr)))
            case RfRBr{}:
              &rr: String -> ({text == SCon{']', rr} : String} & r2.fill(rest, rr))
            case RfWs{}:
              &ww: String -> &rr: String -> ({text == String.append(ww, rr) : String} &
                ({D2.abnf.ws(ww) == True{} : Bool} & r2.fill(rest, rr)))
            case RfKSeg{}:
              &sg: D6.KSeg -> &rr: String -> ({text == D6.k3.seg.text(sg, rr) : String} &
                ({D1.g.ok.seg(sg) == True{} : Bool} & r2.fill(rest, rr)))
            case RfKBare{}:
              &ss: String -> &rr: String -> ({text == String.append(ss, rr) : String} &
                ({D3.abnf.all_unquoted_key_chars(ss) == True{} : Bool} & r2.fill(rest, rr)))
            case RfKAfter{}:
              &ds: List<&2, D5.GDotSep> -> &rr: String -> ({text == D5.g.dots.text(ds, rr) : String} &
                ({D1.g.ok.dots(ds) == True{} : Bool} & r2.fill(rest, rr)))
            case RfEq{}:
              &ww: String -> &rr: String -> ({text == String.append(ww, SCon{'=', rr}) : String} &
                ({D2.abnf.ws(ww) == True{} : Bool} & r2.fill(rest, rr)))
            case RfKBasic{}:
              &pl: List<&2, D6.KPiece> -> &rr: String -> ({text == D6.k3.pcs.text(pl, SCon{'"', rr}) : String} &
                ({Bool.and(D1.abnf.basic_string(pl), D1.prose.escapes_scalar(pl)) == True{} : Bool} & r2.fill(rest,
                    rr)))
            case RfKLit{}:
              &ss: String -> &rr: String -> ({text == String.append(ss, SCon{'\'', rr}) : String} &
                ({D1.abnf.literal_string(ss) == True{} : Bool} & r2.fill(rest, rr)))
            case RfKEsc{}:
              &pp: D6.KPiece -> &pl: List<&2, D6.KPiece> -> &rr: String -> ({SCon{'\\', text} == D6.k3.pc.text(pp,
                D6.k3.pcs.text(pl, SCon{'"', rr})) : String} & ({Bool.and(D1.abnf.basic_string(pp <> pl),
                D1.prose.escapes_scalar(pp <> pl)) == True{} : Bool} & r2.fill(rest, rr)))
            case RfKUni{uni, left}:
              &hs: List<&2, D6.KHex> -> &pl: List<&2, D6.KPiece> -> &rr: String -> ({text == r1.hexs.text(hs,
                D6.k3.pcs.text(pl, SCon{'"', rr})) : String} & ({Bool.and(r1.hexs.count(hs, left),
                Bool.and(D6.k3.scalar(r1.hexs.acc(hs, uni)), Bool.and(D1.abnf.basic_string(pl),
                D1.prose.escapes_scalar(pl)))) == True{} : Bool} & r2.fill(rest, rr)))
            case RfVal{}:
              &ww: String -> &vv: D5.GVal -> &rr: String -> ({text == String.append(ww, D5.g.val.text(vv,
                  rr)) : String} &
                ({Bool.and(D2.abnf.ws(ww), D1.g.ok.val(vv, D1.RVal{})) == True{} : Bool} & r2.fill(rest, rr)))
            case RfArrAfter{}:
              &wb: List<&2, D5.GWcn> -> &at: R1ATail -> &wn: List<&2, D5.GWcn> -> &rr: String -> ({text ==
                D5.g.wcn.text(wb, r1.atail.text(at, D5.g.wcn.text(wn, SCon{']', rr}))) : String} &
                ({Bool.and(D1.g.ok.wcn(wb), Bool.and(r1.atail.ok(at), D1.g.ok.wcn(wn))) == True{} : Bool} &
                r2.fill(rest, rr)))
            case RfInlAfter{}:
              &it: R1ITail -> &ww: String -> &rr: String -> ({text == r1.itail.text(it, String.append(ww,
                SCon{Chr{125}, rr})) : String} & ({Bool.and(r1.itail.ok(it), D2.abnf.ws(ww)) == True{} : Bool} &
                r2.fill(rest, rr)))
        case R2Arr{}:
          &gv: D5.GVal -> &rr: String -> ({text == r2.arr.rest(gv, rr) : String} &
            ({Bool.and(r2.is.arr(gv), D1.g.ok.val(gv, D1.RVal{})) == True{} : Bool} & r2.fill(rest, rr)))
        case R2Inl{}:
          &gv: D5.GVal -> &rr: String -> ({text == r2.inl.rest(gv, rr) : String} &
            ({Bool.and(r2.is.inl(gv), D1.g.ok.val(gv, D1.RVal{})) == True{} : Bool} & r2.fill(rest, rr)))
        case R2InlK{}:
          &w2: String -> &kvs: D5.GVal -> &ww: String -> &rr: String -> ({text == String.append(w2, D5.g.val.text(kvs,
            String.append(ww, SCon{Chr{125}, rr}))) : String} & ({Bool.and(D2.abnf.ws(w2), Bool.and(D1.g.ok.val(kvs,
            D1.RInlineTableKeyvals{}), D2.abnf.ws(ww))) == True{} : Bool} & r2.fill(rest, rr)))
        case R2Nl{}:
          &nl: String -> &rr: String -> ({text == String.append(nl, rr) : String} &
            ({D1.abnf.newline(nl) == True{} : Bool} & r2.fill(rest, rr)))
        case R2Word{buf}:
          &ww: List<&2, Char> -> &rr: String -> ({text == String.append(String.from_list(ww), rr) : String} &
            ({r2.word.ok(List.reverse.go(&2, Char, buf, ww)) == True{} : Bool} & r2.fill(rest, rr)))
        case R2Date{buf}:
          &ch: Bool -> &ww: List<&2, Char> -> &rr: String -> ({text == String.append(String.from_list(ww), rr) :
            String} & ({r2.dok(ch, buf, ww) == True{} : Bool} & r2.fill(rest, r2.drr(ch, rr))))
        case R2Str{stage, basic}:
          &st: D5.GString -> &rr: String -> ({text == r2.s.rest(stage, st, rr) : String} &
            ({Bool.and(r2.s.fit(stage, basic, st), D1.g.ok.str(st)) == True{} : Bool} & r2.fill(rest, rr)))
        case R2Mb{}:
          &body: List<&2, D5.GMlb> -> &rr: String -> ({text == r2.mb.text(body, rr) : String} &
            ({r2.mb.ok(body) == True{} : Bool} & r2.fill(rest, rr)))
        case R2MbEsc{}:
          &body: List<&2, D5.GMlb> -> &rr: String -> ({SCon{'\\', text} == r2.mb.text(body, rr) : String} &
            ({r2.mb.ok(body) == True{} : Bool} & r2.fill(rest, rr)))
        case R2MbUni{uni, left}:
          &hs: List<&2, D6.KHex> -> &body: List<&2, D5.GMlb> -> &rr: String -> ({text == r1.hexs.text(hs,
            r2.mb.text(body, rr)) : String} & ({Bool.and(r1.hexs.count(hs, left), Bool.and(D6.k3.scalar(r1.hexs.acc(hs,
            uni)), r2.mb.ok(body))) == True{} : Bool} & r2.fill(rest, rr)))
        case R2MbFold{}:
          &w1: String -> &nl: String -> &more: String -> &body: List<&2, D5.GMlb> -> &rr: String -> ({text ==
            String.append(w1, String.append(nl, String.append(more, r2.mb.text(body, rr)))) : String} &
            ({Bool.and(D1.abnf.mlb_escaped_nl(w1, nl, more), r2.mb.ok(body)) == True{} : Bool} & r2.fill(rest, rr)))
        case R2MbFold1{}:
          &more: String -> &body: List<&2, D5.GMlb> -> &rr: String -> ({text == String.append(more, r2.mb.text(body,
            rr)) : String} & ({Bool.and(D1.abnf.ws_newlines(more), r2.mb.ok(body)) == True{} : Bool} &
            r2.fill(rest, rr)))
        case R2MbQ{two}:
          &body: List<&2, D5.GMlb> -> &rr: String -> ({D5.g.quotes.text(two, '"', text) == r2.mb.text(body,
              rr) : String} &
            ({r2.mb.ok(body) == True{} : Bool} & r2.fill(rest, rr)))
        case R2Ml{}:
          &body: List<&2, D5.GMll> -> &rr: String -> ({text == r2.ml.text(body, rr) : String} &
            ({D1.abnf.ml_literal_body(body, False{}) == True{} : Bool} & r2.fill(rest, rr)))
        case R2MlQ{two}:
          &body: List<&2, D5.GMll> -> &rr: String -> ({D5.g.quotes.text(two, '\'', text) == r2.ml.text(body, rr) :
            String} & ({D1.abnf.ml_literal_body(body, False{}) == True{} : Bool} & r2.fill(rest, rr)))
        case R2MEnd{qc, nn}:
          &mm: D3.R2N -> &rr: String -> ({text == r2.qs(qc, mm, rr) : String} &
            ({r2.n.le(nn, mm) == True{} : Bool} & r2.fill(rest, rr)))

# the rules still open after a value, in the frames of the arrays and
# inline tables it is in, innermost first
def r2.aft(stack: List<&2, T.Ctx>) -> List<&2, R2Fr>:
  r2.lift(r1.after(stack))

# LArr's: an array after its [ or a comma, when an array is open
def r2.gp.arr0(stack: List<&2, T.Ctx>) -> List<&2, R2Fr>:
  match stack:
    case T.CArr{_i, _p, _h} <> rest:
      R2Arr{} <> r2.aft(rest)
    case _s:
      r2.any()

# LArr's, with nothing buffered; a state with a character buffered is one no
# step reaches
def r2.gp.arr(buf: List<&2, Char>, stack: List<&2, T.Ctx>) -> List<&2, R2Fr>:
  match buf:
    case []:
      r2.gp.arr0(stack)
    case _b <> _bs:
      r2.any()

# LArrC's: after an item, when an array is open
def r2.gp.arrc0(stack: List<&2, T.Ctx>) -> List<&2, R2Fr>:
  match stack:
    case T.CArr{_i, _p, _h} <> _r:
      r2.aft(stack)
    case _s:
      r2.any()

# LArrC's, with nothing buffered
def r2.gp.arrc(buf: List<&2, Char>, stack: List<&2, T.Ctx>) -> List<&2, R2Fr>:
  match buf:
    case []:
      r2.gp.arrc0(stack)
    case _b <> _bs:
      r2.any()

# LInl's: an inline table after its {, when one is open
def r2.gp.inl(stack: List<&2, T.Ctx>) -> List<&2, R2Fr>:
  match stack:
    case T.CInl{_i, _p, _h} <> rest:
      R2Inl{} <> r2.aft(rest)
    case _s:
      r2.any()

# LInlK's: an inline table's keyvals after a comma
def r2.gp.inlk(stack: List<&2, T.Ctx>) -> List<&2, R2Fr>:
  match stack:
    case T.CInl{_i, _p, _h} <> rest:
      R2InlK{} <> r2.aft(rest)
    case _s:
      r2.any()

# LInlC's: after a keyval's value, when an inline table is open
def r2.gp.inlc(stack: List<&2, T.Ctx>) -> List<&2, R2Fr>:
  match stack:
    case T.CInl{_i, _p, _h} <> _r:
      r2.aft(stack)
    case _s:
      r2.any()

# a comment's in an array: the rest of it, a newline and the array's rest
def r2.gp.com.arr(back: T.Lex, stack: List<&2, T.Ctx>) -> List<&2, R2Fr>:
  match back stack:
    case T.LArr{} T.CArr{_i, _p, _h} <> rest:
      R2Old{RfComment{}} <> (R2Nl{} <> (R2Arr{} <> r2.aft(rest)))
    case T.LArrC{} T.CArr{its, pts, hre} <> rest:
      R2Old{RfComment{}} <> (R2Nl{} <> r2.aft(T.CArr{its, pts, hre} <> rest))
    case _k _s:
      r2.any()

# and with nothing buffered
def r2.gp.com.ab(buf: List<&2, Char>, back: T.Lex, stack: List<&2, T.Ctx>) -> List<&2, R2Fr>:
  match buf:
    case []:
      r2.gp.com.arr(back, stack)
    case _b <> _bs:
      r2.any()

# a comment's: in an array, the rest of it, a newline and the array's rest;
# after a value's = or in an inline table, doomed; else the spike's
def r2.gp.com(buf: List<&2, Char>, back: T.Lex, stack: List<&2, T.Ctx>) -> List<&2, R2Fr>:
  match back:
    case T.LArr{}:
      r2.gp.com.ab(buf, T.LArr{}, stack)
    case T.LArrC{}:
      r2.gp.com.ab(buf, T.LArrC{}, stack)
    case T.LVal{}:
      [R2Old{RfNone{}}]
    case T.LInl{}:
      [R2Old{RfNone{}}]
    case T.LInlK{}:
      [R2Old{RfNone{}}]
    case T.LInlC{}:
      [R2Old{RfNone{}}]
    case bk:
      r2.lift(r1.gp.com(bk, stack))

# a string's stage, by its kind: basic or literal
def r2.gp.s(stage: R2K, qkind: T.QKind, stack: List<&2, T.Ctx>) -> List<&2, R2Fr>:
  match stage qkind:
    case SK3{} T.QMulti{}:
      R2Str{SK3{}, True{}} <> r2.aft(stack)
    case SK3{} T.QMultiLit{}:
      R2Str{SK3{}, False{}} <> r2.aft(stack)
    case SK3{} _q:
      r2.any()
    case _k T.QBasic{}:
      R2Str{stage, True{}} <> r2.aft(stack)
    case _k T.QLit{}:
      R2Str{stage, False{}} <> r2.aft(stack)
    case _k _q:
      r2.any()

# LStr's: a one-line string's pieces or characters and its quote, or a
# multi-line body and its delimiter
def r2.gp.str(qkind: T.QKind, stack: List<&2, T.Ctx>) -> List<&2, R2Fr>:
  match qkind:
    case T.QBasic{}:
      R2Old{RfKBasic{}} <> r2.aft(stack)
    case T.QLit{}:
      R2Old{RfKLit{}} <> r2.aft(stack)
    case T.QMulti{}:
      R2Mb{} <> r2.aft(stack)
    case T.QMultiLit{}:
      R2Ml{} <> r2.aft(stack)

# LEsc's: an escape in a basic string
def r2.gp.esc(qkind: T.QKind, stack: List<&2, T.Ctx>) -> List<&2, R2Fr>:
  match qkind:
    case T.QBasic{}:
      R2Old{RfKEsc{}} <> r2.aft(stack)
    case T.QMulti{}:
      R2MbEsc{} <> r2.aft(stack)
    case _q:
      r2.any()

# LUni's with digits still to read
def r2.gp.uni0(qkind: T.QKind, stack: List<&2, T.Ctx>, uni: U32, left: U32) -> List<&2, R2Fr>:
  match qkind:
    case T.QBasic{}:
      R2Old{RfKUni{uni, left}} <> r2.aft(stack)
    case T.QMulti{}:
      R2MbUni{uni, left} <> r2.aft(stack)
    case _q:
      r2.any()

# LUni's: the hexadecimal digits of a \u or \U escape; none left is a state
# no step reaches
def r2.gp.uni(zero: Bool, qkind: T.QKind, stack: List<&2, T.Ctx>, uni: U32, left: U32) -> List<&2, R2Fr>:
  match zero:
    case True{}:
      r2.any()
    case False{}:
      r2.gp.uni0(qkind, stack, uni, left)

# LFold's: a line-ending backslash in a multi-line basic string, before or
# after its newline
def r2.gp.fold(qkind: T.QKind, stack: List<&2, T.Ctx>, saw: Bool) -> List<&2, R2Fr>:
  match qkind saw:
    case T.QMulti{} True{}:
      R2MbFold1{} <> r2.aft(stack)
    case T.QMulti{} False{}:
      R2MbFold{} <> r2.aft(stack)
    case _q _s:
      r2.any()

# LMq's: one quote read in a multi-line body, or two
def r2.gp.mq(qkind: T.QKind, stack: List<&2, T.Ctx>, one: Bool) -> List<&2, R2Fr>:
  match qkind:
    case T.QMulti{}:
      R2MbQ{Bool.not(one)} <> r2.aft(stack)
    case T.QMultiLit{}:
      R2MlQ{Bool.not(one)} <> r2.aft(stack)
    case _q:
      r2.any()

# the quotes read after a closing delimiter, by the count the state keeps
def r2.n.of(z0: Bool, z1: Bool) -> D3.R2N:
  match z0:
    case True{}:
      D3.N0{}
    case False{}:
      match z1:
        case True{}:
          D3.N1{}
        case False{}:
          D3.N2{}

# LMqEnd's: after a multi-line string's closing delimiter
def r2.gp.mqend(qkind: T.QKind, stack: List<&2, T.Ctx>, +left: U32) -> List<&2, R2Fr>:
  match qkind:
    case T.QMulti{}:
      R2MEnd{'"', r2.n.of(U32.is_eq(left, 0), U32.is_eq(left, 1))} <> r2.aft(stack)
    case T.QMultiLit{}:
      R2MEnd{'\'', r2.n.of(U32.is_eq(left, 0), U32.is_eq(left, 1))} <> r2.aft(stack)
    case _q:
      r2.any()

# the position of a scanner state's lex state and the fields it reads: a
# comment's; an array's or an inline table's; a bare word's; a string's
# stages, body, escapes, folds and quotes; else the spike's
def r2.gp0(
  lex: T.Lex,
  back: T.Lex,
  qkind: T.QKind,
  stack: List<&2, T.Ctx>,
  parts: List<&2, String>,
  buf: List<&2, Char>,
  uni: U32,
  +left: U32,
  arr: Bool
) -> List<&2, R2Fr>:
  match lex:
    case T.LCom{}:
      r2.gp.com(buf, back, stack)
    case T.LArr{}:
      r2.gp.arr(buf, stack)
    case T.LArrC{}:
      r2.gp.arrc(buf, stack)
    case T.LInl{}:
      r2.gp.inl(stack)
    case T.LInlK{}:
      r2.gp.inlk(stack)
    case T.LInlC{}:
      r2.gp.inlc(stack)
    case T.LBare{}:
      R2Word{buf} <> r2.aft(stack)
    case T.LDate{}:
      R2Date{buf} <> r2.aft(stack)
    case T.LQ{}:
      r2.gp.s(SK1{}, qkind, stack)
    case T.LQ2{}:
      r2.gp.s(SK2{}, qkind, stack)
    case T.LTrim{}:
      r2.gp.s(SK3{}, qkind, stack)
    case T.LTrim2{}:
      r2.any()
    case T.LStr{}:
      r2.gp.str(qkind, stack)
    case T.LEsc{}:
      r2.gp.esc(qkind, stack)
    case T.LUni{}:
      r2.gp.uni(U32.is_zero(left), qkind, stack, uni, left)
    case T.LFold{}:
      r2.gp.fold(qkind, stack, U32.is_eq(left, 1))
    case T.LMq{}:
      r2.gp.mq(qkind, stack, U32.is_eq(left, 1))
    case T.LMqEnd{}:
      r2.gp.mqend(qkind, stack, left)
    case lx:
      r2.lift(r1.gp0(lx, back, qkind, stack, parts, buf, uni, left, arr))

# a state past the start: none while a character is held, else its lex
# state's
def r2.gp.hold(
  hold: T.Hold,
  lex: T.Lex,
  back: T.Lex,
  qkind: T.QKind,
  stack: List<&2, T.Ctx>,
  parts: List<&2, String>,
  buf: List<&2, Char>,
  uni: U32,
  left: U32,
  arr: Bool
) -> List<&2, R2Fr>:
  match hold:
    case T.HChar{_c}:
      r2.any()
    case T.HNone{}:
      r2.gp0(lex, back, qkind, stack, parts, buf, uni, left, arr)

# the position of a scanner state
def r2.gp(st: T.St) -> List<&2, R2Fr>:
  match st:
    case T.St{_b, _r, _h, _e, parts, buf, lex, back, qkind, stack, hold, uni, left, arr, lead}:
      match lead:
        case True{}:
          r2.lift(r1.gp.lead(lex, stack, hold))
        case False{}:
          r2.gp.hold(hold, lex, back, qkind, stack, parts, buf, uni, left, arr)

# a string's opening quote, as its fields say: a basic one's ", a literal
# one's '
def r2.q.ok(basic: Bool, +qc: Char, qkind: T.QKind) -> Bool:
  match basic qkind:
    case True{} T.QBasic{}:
      Char.is_eq(qc, '"')
    case False{} T.QLit{}:
      Char.is_eq(qc, '\'')
    case _b _k:
      False{}

# a position, when its fields agree; nothing otherwise
def r2.when(ok: Bool, fs: List<&2, R2Fr>, +text: String) -> Type:
  match ok:
    case True{}:
      r2.fill(fs, text)
    case False{}:
      Unit

# a span's position: a one-line basic string's pieces, or a literal one's
# characters
def r2.span(basic: Bool) -> R2Fr:
  match basic:
    case True{}:
      R2Old{RfKBasic{}}
    case False{}:
      R2Old{RfKLit{}}

# the texts that complete a mode: a scanning state's position; after a
# carriage return, the line feed and then the state it reads to; after an
# opening quote, the string after one quote; in a span, the rest of a
# one-line string
def r2.C(mode: T.Mode, +text: String) -> Type:
  match mode:
    case T.MScan{st}:
      r2.fill(r2.gp(st), text)
    case T.MCr{st}:
      &uu: String -> ({text == SCon{'\n', uu} : String} & r2.fill(r2.gp(T.read.fast(st, '\n')), uu))
    case T.MOpen{+ba, qq, qk, _bd, _rw, _hs, _he, _pt, _bf, _bk, sk, _un, _lf, _at}:
      r2.when(r2.q.ok(ba, qq, qk), R2Str{SK1{}, ba} <> r2.aft(sk), text)
    case T.MEat{+ba, qq, _c, _n, _bd, _rw, _hs, _he, _pt, qk, sk, _un, _lf, _at}:
      r2.when(r2.q.ok(ba, qq, qk), r2.span(ba) <> r2.aft(sk), text)
