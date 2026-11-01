# the grammar's rule derivations and the text each one spells
import Base
import ./KeySegmentSpelling.bend as D1

# mlb-quotes = 1*2quotation-mark
# mlb-content = mlb-char / newline / mlb-escaped-nl
# a piece of a multi-line basic body: an mlb-content (a character or escape,
# a newline as written, or a line-ending backslash) or an mlb-quotes, of one
# quotation mark or of two when two
type GMlb is Data:
  GmChar{pp: D1.KPiece}
  GmNewline{nl: String}
  GmEscapedNl{w1: String, nl: String, more: String}
  GmQuotes{two: Bool}

# mll-content = mll-char / newline
# mll-quotes = 1*2apostrophe
# a piece of a multi-line literal body: an mll-content (a character, or a
# newline as written) or an mll-quotes, of one apostrophe or of two when two
type GMll is Data:
  GlChar{cc: Char}
  GlNewline{nl: String}
  GlQuotes{two: Bool}

# string = ml-basic-string / basic-string / ml-literal-string / literal-string
# ml-basic-string = ml-basic-string-delim [ newline ] ml-basic-body
#                   ml-basic-string-delim
# ml-basic-string-delim = 3quotation-mark
# ml-literal-string = ml-literal-string-delim [ newline ] ml-literal-body
#                     ml-literal-string-delim
# ml-literal-string-delim = 3apostrophe
# nl is the optional newline after the opening delimiter, "" when there is
# none
type GString is Data:
  GsMlBasic{nl: String, body: List<&2, GMlb>}
  GsBasic{pl: List<&2, D1.KPiece>}
  GsMlLiteral{nl: String, body: List<&2, GMll>}
  GsLiteral{text: String}

# Keys. simple-key is laws/KeyNameIsItsCharacters.bend's KSeg: KsBare an unquoted-key, KsBasic a
# basic-string of pieces and KsLit a literal-string of characters.

# dot-sep   = ws %x2E ws  ; . Period
# a dot-sep and the simple-key after it: the ws before the dot, the ws after
# it, and the key
type GDotSep is Data:
  GDotSep{w1: String, w2: String, sk: D1.KSeg}

# key = simple-key / dotted-key
# dotted-key = simple-key 1*( dot-sep simple-key )
type GKey is Data:
  GSimpleKey{sk: D1.KSeg}
  GDottedKey{sk: D1.KSeg, more: List<&2, GDotSep>}

# Arrays, inline tables and comments.

# [ comment ]: none, or a comment of the characters after the #
type GCom is Data:
  GcNone{}
  GcSome{body: String}

# ws-comment-newline = *( wschar / [ comment ] newline ): one wschar, or a
# newline with the comment before it
type GWcn is Data:
  GwWschar{cc: Char}
  GwNewline{com: GCom, nl: String}

# val = string / boolean / array / inline-table / date-time / float / integer
# array = array-open [ array-values ] ws-comment-newline array-close
# array-values =  ws-comment-newline val ws-comment-newline array-sep array-values
# array-values =/ ws-comment-newline val ws-comment-newline [ array-sep ]
# inline-table = inline-table-open [ inline-table-keyvals ] inline-table-close
# inline-table-keyvals = keyval [ inline-table-sep inline-table-keyvals ]
# keyval = key keyval-sep val
# These rules are mutually recursive, so they are one type. The first eight
# constructors spell val's alternatives (an empty array or inline table is
# its own constructor, for the option left out); GArrayValues and
# GArrayValuesLast spell array-values; GInlineTableKeyvals and
# GInlineTableKeyvalsLast spell inline-table-keyvals; GKeyval spells keyval.
# A bare value is its characters; the whitespace around brackets, commas and
# the equals sign is ws, or ws-comment-newline inside an array.
type GVal is Data:
  GvString{st: GString}
  GvBoolean{cs: List<&2, Char>}
  GvArrayEmpty{wn: List<&2, GWcn>}
  GvArray{vals: GVal, wn: List<&2, GWcn>}
  GvInlineTableEmpty{w1: String, w2: String}
  GvInlineTable{w1: String, kvs: GVal, w2: String}
  GvDateTime{cs: List<&2, Char>}
  GvFloat{cs: List<&2, Char>}
  GvInteger{cs: List<&2, Char>}
  GArrayValues{wa: List<&2, GWcn>, val: GVal, wb: List<&2, GWcn>, rest: GVal}
  GArrayValuesLast{wa: List<&2, GWcn>, val: GVal, wb: List<&2, GWcn>, sep: Bool}
  GInlineTableKeyvals{kv: GVal, w1: String, w2: String, rest: GVal}
  GInlineTableKeyvalsLast{kv: GVal}
  GKeyval{key: GKey, w1: String, w2: String, val: GVal}

# Tables and the document.

# table = std-table / array-table
# std-table = std-table-open key std-table-close
# std-table-open  = %x5B ws     ; [ Left square bracket
# std-table-close = ws %x5D     ; ] Right square bracket
# array-table = array-table-open key array-table-close
# array-table-open  = %x5B.5B ws  ; [[ Double left square bracket
# array-table-close = ws %x5D.5D  ; ]] Double right square bracket
# the ws after the opening brackets, the key, and the ws before the closing
type GTable is Data:
  GStdTable{w1: String, key: GKey, w2: String}
  GArrayTable{w1: String, key: GKey, w2: String}

# expression =  ws [ comment ]
# expression =/ ws keyval ws [ comment ]
# expression =/ ws table ws [ comment ]
# (the keyval is a GKeyval)
type GExpr is Data:
  GxBlank{w1: String, com: GCom}
  GxKeyval{w1: String, kv: GVal, w2: String, com: GCom}
  GxTable{w1: String, tb: GTable, w2: String, com: GCom}

# newline expression: one of toml's *( newline expression )
type GLine is Data:
  GLine{nl: String, ex: GExpr}

# toml = expression *( newline expression )
type Gd is Data:
  GToml{first: GExpr, rest: List<&2, GLine>}

# g.text: the text a derivation spells. Each def writes its part, then tail.

# a comment, if there is one: the # and its characters
def g.com.text(cm: GCom, tail: String) -> String:
  match cm:
    case GcNone{}:
      tail
    case GcSome{body}:
      SCon{'#', String.append(body, tail)}

# ws-comment-newline's text
def g.wcn.text(ws: List<&2, GWcn>, tail: String) -> String:
  match ws:
    case []:
      tail
    case GwWschar{cc} <> rest:
      SCon{cc, g.wcn.text(rest, tail)}
    case GwNewline{com, nl} <> rest:
      g.com.text(com, String.append(nl, g.wcn.text(rest, tail)))

# a key's dot-seps and simple-keys after its first
def g.dots.text(ds: List<&2, GDotSep>, tail: String) -> String:
  match ds:
    case []:
      tail
    case GDotSep{w1, w2, sk} <> rest:
      String.append(w1, SCon{'.', String.append(w2, D1.k3.seg.text(sk, g.dots.text(rest, tail)))})

# a key's text
def g.key.text(kk: GKey, tail: String) -> String:
  match kk:
    case GSimpleKey{sk}:
      D1.k3.seg.text(sk, tail)
    case GDottedKey{sk, more}:
      D1.k3.seg.text(sk, g.dots.text(more, tail))

# mlb-quotes: one quotation mark, or two
def g.quotes.text(two: Bool, +qc: Char, tail: String) -> String:
  match two:
    case True{}:
      SCon{qc, SCon{qc, tail}}
    case False{}:
      SCon{qc, tail}

# a multi-line basic body's text
def g.mlb.text(ps: List<&2, GMlb>, tail: String) -> String:
  match ps:
    case []:
      tail
    case GmChar{kp} <> rest:
      D1.k3.pc.text(kp, g.mlb.text(rest, tail))
    case GmNewline{nl} <> rest:
      String.append(nl, g.mlb.text(rest, tail))
    case GmEscapedNl{w1, nl, more} <> rest:
      SCon{'\\', String.append(w1, String.append(nl, String.append(more, g.mlb.text(rest, tail))))}
    case GmQuotes{two} <> rest:
      g.quotes.text(two, '"', g.mlb.text(rest, tail))

# a multi-line literal body's text
def g.mll.text(ps: List<&2, GMll>, tail: String) -> String:
  match ps:
    case []:
      tail
    case GlChar{cc} <> rest:
      SCon{cc, g.mll.text(rest, tail)}
    case GlNewline{nl} <> rest:
      String.append(nl, g.mll.text(rest, tail))
    case GlQuotes{two} <> rest:
      g.quotes.text(two, '\'', g.mll.text(rest, tail))

# a string's text, with its delimiters
def g.str.text(st: GString, tail: String) -> String:
  match st:
    case GsMlBasic{nl, body}:
      SCon{'"', SCon{'"', SCon{'"', String.append(nl, g.mlb.text(body, SCon{'"', SCon{'"', SCon{'"', tail}}}))}}}
    case GsBasic{pl}:
      SCon{'"', D1.k3.pcs.text(pl, SCon{'"', tail})}
    case GsMlLiteral{nl, body}:
      SCon{'\'', SCon{'\'', SCon{'\'', String.append(nl, g.mll.text(body, SCon{'\'', SCon{'\'', SCon{'\'', tail}}}))}}}
    case GsLiteral{text}:
      SCon{'\'', String.append(text, SCon{'\'', tail})}

# [ array-sep ]: a comma when there is one
def g.sep.text(sep: Bool, tail: String) -> String:
  match sep:
    case True{}:
      SCon{',', tail}
    case False{}:
      tail

# a value's text, or that of an array-values, inline-table-keyvals or keyval
# node: array-open is [ (%x5B), array-close ] (%x5D), array-sep , (%x2C),
# inline-table-open { and ws (%x7B), inline-table-close ws and } (%x7D),
# inline-table-sep ws , ws, keyval-sep ws = ws (%x3D)
def g.val.text(vv: GVal, tail: String) -> String:
  match vv:
    case GvString{st}:
      g.str.text(st, tail)
    case GvBoolean{cs}:
      String.append(String.from_list(cs), tail)
    case GvArrayEmpty{wn}:
      SCon{'[', g.wcn.text(wn, SCon{']', tail})}
    case GvArray{vals, wn}:
      SCon{'[', g.val.text(vals, g.wcn.text(wn, SCon{']', tail}))}
    case GvInlineTableEmpty{w1, w2}:
      SCon{'{', String.append(w1, String.append(w2, SCon{'}', tail}))}
    case GvInlineTable{w1, kvs, w2}:
      SCon{'{', String.append(w1, g.val.text(kvs, String.append(w2, SCon{'}', tail})))}
    case GvDateTime{cs}:
      String.append(String.from_list(cs), tail)
    case GvFloat{cs}:
      String.append(String.from_list(cs), tail)
    case GvInteger{cs}:
      String.append(String.from_list(cs), tail)
    case GArrayValues{wa, val, wb, rest}:
      g.wcn.text(wa, g.val.text(val, g.wcn.text(wb, SCon{',', g.val.text(rest, tail)})))
    case GArrayValuesLast{wa, val, wb, sep}:
      g.wcn.text(wa, g.val.text(val, g.wcn.text(wb, g.sep.text(sep, tail))))
    case GInlineTableKeyvals{kv, w1, w2, rest}:
      g.val.text(kv, String.append(w1, SCon{',', String.append(w2, g.val.text(rest, tail))}))
    case GInlineTableKeyvalsLast{kv}:
      g.val.text(kv, tail)
    case GKeyval{key, w1, w2, val}:
      g.key.text(key, String.append(w1, SCon{'=', String.append(w2, g.val.text(val, tail))}))

# a table header's text
def g.table.text(tb: GTable, tail: String) -> String:
  match tb:
    case GStdTable{w1, key, w2}:
      SCon{'[', String.append(w1, g.key.text(key, String.append(w2, SCon{']', tail})))}
    case GArrayTable{w1, key, w2}:
      SCon{'[', SCon{'[', String.append(w1, g.key.text(key, String.append(w2, SCon{']', SCon{']', tail}})))}}

# an expression's text
def g.expr.text(ex: GExpr, tail: String) -> String:
  match ex:
    case GxBlank{w1, com}:
      String.append(w1, g.com.text(com, tail))
    case GxKeyval{w1, kv, w2, com}:
      String.append(w1, g.val.text(kv, String.append(w2, g.com.text(com, tail))))
    case GxTable{w1, tb, w2, com}:
      String.append(w1, g.table.text(tb, String.append(w2, g.com.text(com, tail))))

# the text of each newline and expression after the first
def g.lines.text(ls: List<&2, GLine>, tail: String) -> String:
  match ls:
    case []:
      tail
    case GLine{nl, ex} <> rest:
      String.append(nl, g.expr.text(ex, g.lines.text(rest, tail)))

# the text a derivation spells
def g.text(dd: Gd) -> String:
  match dd:
    case GToml{first, rest}:
      g.expr.text(first, g.lines.text(rest, ""))
