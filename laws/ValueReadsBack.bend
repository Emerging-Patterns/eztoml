import Base
import ../main.bend as T
import ./defs/BareValueGrammar.bend as D1

# WP-C: arrays and inline tables read back. render writes an array as `[`,
# its items joined by ", " and `]`, and an inline table as `{`, its pairs
# `key = value` joined by ", " and `}`, nested to any depth. The scanner reads
# such a value from the state that waits for a value up to the character
# after it, which ends it: a newline at the top level, a comma or a closer
# inside a container. The value it puts is in the raw form below: a string a
# span or an owned string, an array's items in order, an inline table's pairs
# newest first until rows.seal; own reads it as cv.raw says.

# a text that starts with a character that may end a value: a newline, a
# comma, or a closer
def cv.end(rest: String) -> Bool:
  match rest:
    case SNil{}:
      False{}
    case SCon{+cc, _tt}:
      Bool.or(Char.is_eq(cc, '\n'), Bool.or(Char.is_eq(cc, ','), Bool.or(Char.is_eq(cc, ']'),
        Char.is_eq(cc, '}'))))

# one value with every span read out, as own.rows reads the head of a list
def cv.own1(vv: T.Val) -> T.Val:
  match vv:
    case T.VPair{nn, T.VSpan{src, +kk}}:
      T.VPair{nn, T.VStr{T.span.str(src, kk, U32.is_zero(kk))}}
    case T.VPair{nn, T.VArr{items}}:
      T.VPair{nn, T.VArr{D1.own.rows(items)}}
    case T.VPair{nn, T.VInl{rows}}:
      T.VPair{nn, T.VInl{D1.own.rows(rows)}}
    case T.VPair{nn, T.VHead{path, rows}}:
      T.VPair{nn, T.VHead{path, D1.own.rows(rows)}}
    case T.VPair{nn, T.VAot{path, rows}}:
      T.VPair{nn, T.VAot{path, D1.own.rows(rows)}}
    case T.VPair{nn, T.VAots{path, elems}}:
      T.VPair{nn, T.VAots{path, D1.own.rows(elems)}}
    case T.VSpan{src, +kk}:
      T.VStr{T.span.str(src, kk, U32.is_zero(kk))}
    case T.VArr{items}:
      T.VArr{D1.own.rows(items)}
    case T.VInl{rows}:
      T.VInl{D1.own.rows(rows)}
    case T.VHead{path, rows}:
      T.VHead{path, D1.own.rows(rows)}
    case T.VAot{path, rows}:
      T.VAot{path, D1.own.rows(rows)}
    case T.VAots{path, elems}:
      T.VAots{path, D1.own.rows(elems)}
    case other:
      other

# values as the scanner puts them, every span read out: strings owned, an
# array's items in order, an inline table's pairs newest first
def cv.raw(vs: List<&2, T.Val>) -> List<&2, T.Val>:
  match vs:
    case []:
      []
    case T.VPair{nn, T.VSpan{src, +kk}} <> tt:
      T.VPair{nn, T.VStr{T.span.str(src, kk, U32.is_zero(kk))}} <> cv.raw(tt)
    case T.VPair{nn, T.VArr{items}} <> tt:
      T.VPair{nn, T.VArr{cv.raw(items)}} <> cv.raw(tt)
    case T.VPair{nn, T.VInl{rows}} <> tt:
      T.VPair{nn, T.VInl{List.reverse(&2, T.Val, cv.raw(rows))}} <> cv.raw(tt)
    case T.VSpan{src, +kk} <> tt:
      T.VStr{T.span.str(src, kk, U32.is_zero(kk))} <> cv.raw(tt)
    case T.VArr{items} <> tt:
      T.VArr{cv.raw(items)} <> cv.raw(tt)
    case T.VInl{rows} <> tt:
      T.VInl{List.reverse(&2, T.Val, cv.raw(rows))} <> cv.raw(tt)
    case vv <> tt:
      vv <> cv.raw(tt)

# one value as the scanner puts it, as cv.raw reads the head of a list
def cv.raw1(vv: T.Val) -> T.Val:
  match vv:
    case T.VPair{nn, T.VSpan{src, +kk}}:
      T.VPair{nn, T.VStr{T.span.str(src, kk, U32.is_zero(kk))}}
    case T.VPair{nn, T.VArr{items}}:
      T.VPair{nn, T.VArr{cv.raw(items)}}
    case T.VPair{nn, T.VInl{rows}}:
      T.VPair{nn, T.VInl{List.reverse(&2, T.Val, cv.raw(rows))}}
    case T.VSpan{src, +kk}:
      T.VStr{T.span.str(src, kk, U32.is_zero(kk))}
    case T.VArr{items}:
      T.VArr{cv.raw(items)}
    case T.VInl{rows}:
      T.VInl{List.reverse(&2, T.Val, cv.raw(rows))}
    case other:
      other

# the rest of the walk once a value ww is read: from the state with a value
# put where the stack puts values, one that own reads as the scanner's form
# of ww, and whatever back, qkind, uni and left the value leaves, the rest of
# the text gives a document PP holds of
def vrest(
  +ww: T.Val,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  @vv: T.Val -> @bk: T.Lex -> @qk: T.QKind -> @un: U32 -> @lf: U32 ->
    {cv.own1(vv) == cv.raw1(ww) : T.Val} ->
    PP(T.doc.read(rest, T.MScan{T.take.top(sk, vv, "", rw, hs, he, ps, bk, qk, un, lf, ab, False{})}))

# LAW: a value render writes in a value position reads back: from every
# state that waits for a value, the text of a well-formed value whose strings
# are short (a scalar, a string, or an array or an inline table nested to any
# depth), then a character that ends a value and any rest, reads on as the
# rest from the state with the value put, in the scanner's form, whatever the
# value leaves in back, qkind, uni and left. PP is what the caller proves of
# the document
law value_reads_back:
  for +v: T.Val
  for hw: {D1.cv.wf(v) == True{} : Bool}
  for hl: {D1.cv.short1(v) == True{} : Bool}
  for +rw: List<&2, T.Val>
  for +hs: List<&2, String>
  for +he: List<&2, String>
  for +ps: List<&2, String>
  for +bk: T.Lex
  for +qk: T.QKind
  for +sk: List<&2, T.Ctx>
  for +un: U32
  for +lf: U32
  for +ab: Bool
  for +rest: String
  for hn: {cv.end(rest) == True{} : Bool}
  for -PP: T.Doc -> Type
  for ih: vrest(v, rw, hs, he, ps, sk, ab, rest, PP)
  PP(T.doc.read(D1.cv.tx(v, rest), T.MScan{D1.vpos(rw, hs, he, ps, bk, qk, sk, un, lf, ab)}))
