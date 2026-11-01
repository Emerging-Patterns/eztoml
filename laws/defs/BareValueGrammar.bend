# unquoted-key and bare-word grammar facts with the numeral and counting
# helpers
import Base
import ../../main.bend as T

# The law side of laws/BareKey.bend: toml.abnf (TOML v1.0.0) transcribed over each
# character's code point. Bend has no hex literals, so each bound is written
# in decimal with its hex beside it.

# ALPHA = %x41-5A / %x61-7A ; A-Z / a-z
# (%x41 is 65, %x5A is 90, %x61 is 97, %x7A is 122)
def abnf.alpha(+cp: U32) -> Bool:
  Bool.or(Bool.and(U32.is_ge(cp, 65), U32.is_le(cp, 90)),
    Bool.and(U32.is_ge(cp, 97), U32.is_le(cp, 122)))

# DIGIT = %x30-39 ; 0-9
# (%x30 is 48, %x39 is 57)
def abnf.digit(+cp: U32) -> Bool:
  Bool.and(U32.is_ge(cp, 48), U32.is_le(cp, 57))

# unquoted-key = 1*( ALPHA / DIGIT / %x2D / %x5F ) ; A-Z / a-z / 0-9 / - / _
# One character of the repetition, by its code point. (%x2D is 45, %x5F is 95)
def abnf.unquoted_key_char(cc: Char) -> Bool:
  match cc:
    case Chr{+cp}:
      Bool.or(abnf.alpha(cp), Bool.or(abnf.digit(cp),
        Bool.or(U32.is_eq(cp, 45), U32.is_eq(cp, 95))))

# every character of a string is one of the repetition's
def abnf.all_unquoted_key_chars(ss: String) -> Bool:
  match ss:
    case SNil{}:
      True{}
    case SCon{hh, tt}:
      Bool.and(abnf.unquoted_key_char(hh), abnf.all_unquoted_key_chars(tt))

# unquoted-key = 1*( ALPHA / DIGIT / %x2D / %x5F ): one or more of them
def abnf.unquoted_key(ss: String) -> Bool:
  match ss:
    case SNil{}:
      False{}
    case SCon{hh, tt}:
      Bool.and(abnf.unquoted_key_char(hh), abnf.all_unquoted_key_chars(tt))

# The numeral scan (I6, R-I6). toml.abnf: `dec-int = [ minus / plus ]
# unsigned-dec-int`, `unsigned-dec-int = DIGIT / digit1-9 1*( DIGIT /
# underscore DIGIT )`, and `float-int-part = dec-int`: one sign at most, and
# no leading zero but a lone 0, so no `_` after it.

# the character a sign is written with
def mark(sg: T.Sign) -> Char:
  match sg:
    case T.Plus{}:
      '+'
    case T.Minus{}:
      '-'

# rows with every span read out into an owned string. A pair whose value is a
# pair, which no well-formed document holds, is kept as it is
def own.rows(vs: List<&2, T.Val>) -> List<&2, T.Val>:
  match vs:
    case []:
      []
    case T.VPair{nn, T.VSpan{src, +kk}} <> tt:
      T.VPair{nn, T.VStr{T.span.str(src, kk, U32.is_zero(kk))}} <> own.rows(tt)
    case T.VPair{nn, T.VArr{items}} <> tt:
      T.VPair{nn, T.VArr{own.rows(items)}} <> own.rows(tt)
    case T.VPair{nn, T.VInl{rows}} <> tt:
      T.VPair{nn, T.VInl{own.rows(rows)}} <> own.rows(tt)
    case T.VPair{nn, T.VHead{path, rows}} <> tt:
      T.VPair{nn, T.VHead{path, own.rows(rows)}} <> own.rows(tt)
    case T.VPair{nn, T.VAot{path, rows}} <> tt:
      T.VPair{nn, T.VAot{path, own.rows(rows)}} <> own.rows(tt)
    case T.VPair{nn, T.VAots{path, elems}} <> tt:
      T.VPair{nn, T.VAots{path, own.rows(elems)}} <> own.rows(tt)
    case T.VSpan{src, +kk} <> tt:
      T.VStr{T.span.str(src, kk, U32.is_zero(kk))} <> own.rows(tt)
    case T.VArr{items} <> tt:
      T.VArr{own.rows(items)} <> own.rows(tt)
    case T.VInl{rows} <> tt:
      T.VInl{own.rows(rows)} <> own.rows(tt)
    case T.VHead{path, rows} <> tt:
      T.VHead{path, own.rows(rows)} <> own.rows(tt)
    case T.VAot{path, rows} <> tt:
      T.VAot{path, own.rows(rows)} <> own.rows(tt)
    case T.VAots{path, elems} <> tt:
      T.VAots{path, own.rows(elems)} <> own.rows(tt)
    case vv <> tt:
      vv <> own.rows(tt)

# a document with every span read out into an owned string
def own(dd: T.Doc) -> T.Doc:
  match dd:
    case T.Doc{bad, rows}:
      T.Doc{bad, own.rows(rows)}

# the job of a table header: an array of tables, or a table
def header_job(arr: Bool) -> T.Job:
  match arr:
    case True{}:
      T.JAot{}
    case False{}:
      T.JDef{}

# the error of a finished walk, "" when it has none
def end_bad(end: T.End) -> String:
  match end:
    case T.End{_vs, bad, _heads}:
      bad

# The header scanner. Each law below holds from every scanner state inside a
# header with the buffer it names, whatever the other fields hold. A refusal
# fails the document whatever follows (fail_stays).

# a quote: a literal one or a basic one
def quote_char(lit: Bool) -> Char:
  match lit:
    case True{}:
      '\''
    case False{}:
      '"'

# counting the characters of a text up from n in a U32 never comes back to 0
def counts(ss: String, +nn: U32) -> Bool:
  match ss:
    case SNil{}:
      True{}
    case SCon{_hh, tt}:
      Bool.and(Bool.not(U32.is_zero(U32.add(nn, 1))), counts(tt, U32.add(nn, 1)))

# fewer than 2^32 characters: a U32 counts them from 0 without wrapping
def short(ss: String) -> Bool:
  counts(ss, 0)

# WP-W: contracts of the walk. tree.walk follows a key path from the root and
# applies a job at its end: a value put into a table (JPut), a [table] header
# (JDef) or an [[array]] header (JAot). The laws below say what a walk returns
# (the root's rows, the error and the recorded definitions) for a path whose
# tables are premises read off the rows, so a proof about a document applies
# them without replaying its text. Rows are newest first until rows.seal.

# whether the newest element of an array of tables is one a walk can enter
def tb.last.can(last: T.Last) -> Bool:
  match last:
    case T.LastSome{_p, _older, _rows}:
      True{}
    case T.LastNo{_why}:
      False{}

# whether a walk goes on through what a name refers to: a table, an array of
# tables whose newest element is a table, or nothing yet, where the walk makes
# an implicit table
def tb.can(look: T.Look) -> Bool:
  match look:
    case T.KMiss{}:
      True{}
    case T.KHead{_p, _rows}:
      True{}
    case T.KAots{p, elems}:
      tb.last.can(T.look.last(elems, p))
    case _:
      False{}

# the rows of the newest element of an array of tables
def tb.last.rows(last: T.Last) -> List<&2, T.Val>:
  match last:
    case T.LastSome{_p, _older, rows}:
      rows
    case T.LastNo{_why}:
      []

# the rows a walk goes on in: a table's, the newest element's of an array of
# tables, or none for a table the walk makes
def tb.into(look: T.Look) -> List<&2, T.Val>:
  match look:
    case T.KHead{_p, rows}:
      rows
    case T.KAots{p, elems}:
      tb.last.rows(T.look.last(elems, p))
    case _:
      []

# the newest element of an array of tables with its rows replaced
def tb.last.put(
  last: T.Last,
  +name: String,
  rows: List<&2, T.Val>,
  +pp: String,
  child: List<&2, T.Val>
) -> List<&2, T.Val>:
  match last:
    case T.LastSome{_q, older, _r}:
      T.rows.repl(rows, name, T.VAots{pp, T.VAot{pp, child} <> older})
    case T.LastNo{_why}:
      rows

# the rows with the table a name refers to holding child: a table keeps its
# path, the newest element of an array of tables takes the array's path, and a
# name that is not there yet becomes an implicit table in front
def tb.put.in(
  look: T.Look,
  +name: String,
  rows: List<&2, T.Val>,
  +pre: String,
  child: List<&2, T.Val>
) -> List<&2, T.Val>:
  match look:
    case T.KMiss{}:
      T.VPair{name, T.VHead{T.tree.pre(pre, name), child}} <> rows
    case T.KHead{p, _r}:
      T.rows.repl(rows, name, T.VHead{p, child})
    case T.KAots{+p, elems}:
      tb.last.put(T.look.last(elems, p), name, rows, p, child)
    case _:
      rows

# whether a walk goes on through every segment of the path
def tb.open(path: List<&2, String>, +rows: List<&2, T.Val>) -> Bool:
  match path:
    case []:
      True{}
    case +seg <> rest:
      Bool.and(tb.can(T.rows.look(rows, seg)), tb.open(rest, tb.into(T.rows.look(rows, seg))))

# the rows of the table at the end of the path
def tb.rows(path: List<&2, String>, rows: List<&2, T.Val>) -> List<&2, T.Val>:
  match path:
    case []:
      rows
    case seg <> rest:
      tb.rows(rest, tb.into(T.rows.look(rows, seg)))

# the rows with the table at the end of the path holding new. pre is the path
# of the table the rows are, which names an implicit table made on the way
def tb.set(
  path: List<&2, String>,
  +pre: String,
  +rows: List<&2, T.Val>,
  new: List<&2, T.Val>
) -> List<&2, T.Val>:
  match path:
    case []:
      new
    case +seg <> rest:
      tb.put.in(T.rows.look(rows, seg), seg, rows, pre,
        tb.set(rest, T.tree.pre(pre, seg), tb.into(T.rows.look(rows, seg)), new))

# the path a walk names a table by: each segment as key writes it, joined by
# dots after pre
def tb.join(path: List<&2, String>, pre: String) -> String:
  match path:
    case []:
      pre
    case seg <> rest:
      tb.join(rest, T.tree.pre(pre, seg))

# whether the walk counts skip down past every segment of the path before it
# reaches zero: each segment is navigation into the current table
def counts.down(path: List<&2, String>, +skip: U32) -> Bool:
  match path:
    case []:
      True{}
    case _seg <> rest:
      Bool.and(Bool.not(U32.is_zero(skip)), counts.down(rest, T.path.dec(skip)))

# a character a bare value keeps: no delimiter and no quote
def word.char(+cc: Char) -> Bool:
  Bool.and(Bool.not(T.ch.delim(cc)), Bool.not(Bool.or(Char.is_eq(cc, '"'), Char.is_eq(cc, '\''))))

# a character that starts a bare value: one it keeps, and no bracket or brace
def word.first(+cc: Char) -> Bool:
  Bool.and(word.char(cc), Bool.not(Bool.or(Char.is_eq(cc, '['), Char.is_eq(cc, '{'))))

# the integer 1, the value the key/value laws below read
def one() -> T.Val:
  T.VInt{T.Plus{}, "1"}

# the text render writes for a value in a value position, then xx: an array's
# items joined by ", " in brackets, an inline table's pairs joined by ", " in
# braces, or a scalar's text
def cv.tx(vv: T.Val, xx: String) -> String:
  match vv:
    case T.VArr{items}:
      SCon{'[', String.append(T.render.go(items, ", ", False{}), SCon{']', xx})}
    case T.VInl{rows}:
      SCon{'{', String.append(T.render.go(rows, ", ", False{}), SCon{'}', xx})}
    case other:
      String.append(T.render.atom(other), xx)

# a value that may sit in a value position, well-formed as wf.go reads an
# array's item or a pair's value: an array of well-formed items, an inline
# table of well-formed pairs, or a well-formed scalar
def cv.wf(vv: T.Val) -> Bool:
  match vv:
    case T.VArr{items}:
      T.wf.go(items, T.WfItems{})
    case T.VInl{rows}:
      T.wf.go(rows, T.WfInl{})
    case other:
      T.wf.atom(other)

# every string in the values, at any depth, is short: a span counts its
# characters in a U32
def cv.shorts(vs: List<&2, T.Val>) -> Bool:
  match vs:
    case []:
      True{}
    case T.VPair{_nn, T.VStr{ss}} <> tt:
      Bool.and(short(ss), cv.shorts(tt))
    case T.VPair{_nn, T.VSpan{src, +kk}} <> tt:
      Bool.and(short(T.span.str(src, kk, U32.is_zero(kk))), cv.shorts(tt))
    case T.VPair{_nn, T.VArr{items}} <> tt:
      Bool.and(cv.shorts(items), cv.shorts(tt))
    case T.VPair{_nn, T.VInl{rows}} <> tt:
      Bool.and(cv.shorts(rows), cv.shorts(tt))
    case T.VStr{ss} <> tt:
      Bool.and(short(ss), cv.shorts(tt))
    case T.VSpan{src, +kk} <> tt:
      Bool.and(short(T.span.str(src, kk, U32.is_zero(kk))), cv.shorts(tt))
    case T.VArr{items} <> tt:
      Bool.and(cv.shorts(items), cv.shorts(tt))
    case T.VInl{rows} <> tt:
      Bool.and(cv.shorts(rows), cv.shorts(tt))
    case _vv <> tt:
      cv.shorts(tt)

# every string in one value, at any depth, is short
def cv.short1(vv: T.Val) -> Bool:
  match vv:
    case T.VStr{ss}:
      short(ss)
    case T.VSpan{src, +kk}:
      short(T.span.str(src, kk, U32.is_zero(kk)))
    case T.VArr{items}:
      cv.shorts(items)
    case T.VInl{rows}:
      cv.shorts(rows)
    case _vv:
      True{}

# the scanner waiting for a value, with no error and nothing buffered, the
# fields a value does not decide left as parameters
def vpos(
  rw: List<&2, T.Val>,
  hs: List<&2, String>,
  he: List<&2, String>,
  ps: List<&2, String>,
  bk: T.Lex,
  qk: T.QKind,
  sk: List<&2, T.Ctx>,
  un: U32,
  lf: U32,
  ab: Bool
) -> T.St:
  T.St{"", rw, hs, he, ps, [], T.LVal{}, bk, qk, sk, T.HNone{}, un, lf, ab, False{}}

# whether a word is exactly the characters of ss, each matched as itself
# (a %x string: %x74.72.75.65 is the word true and nothing else)
def abnf.chars_are(cs: List<&2, Char>, ss: String) -> Bool:
  match cs ss:
    case [] SNil{}:
      True{}
    case +hh <> tt SCon{+h2, t2}:
      Bool.and(Char.is_eq(hh, h2), abnf.chars_are(tt, t2))
    case _c _s:
      False{}

# Boolean.

# true    = %x74.72.75.65     ; true
def abnf.true(cs: List<&2, Char>) -> Bool:
  abnf.chars_are(cs, "true")

# false   = %x66.61.6C.73.65  ; false
def abnf.false(cs: List<&2, Char>) -> Bool:
  abnf.chars_are(cs, "false")

# boolean = true / false
def abnf.boolean(+cs: List<&2, Char>) -> Bool:
  Bool.or(abnf.true(cs), abnf.false(cs))

# the scanner waiting for an array's next item, with no error and nothing
# buffered, the fields a value does not decide left as parameters
def s1.apos(
  rw: List<&2, T.Val>,
  hs: List<&2, String>,
  he: List<&2, String>,
  ps: List<&2, String>,
  bk: T.Lex,
  qk: T.QKind,
  sk: List<&2, T.Ctx>,
  un: U32,
  lf: U32,
  ab: Bool
) -> T.St:
  T.St{"", rw, hs, he, ps, [], T.LArr{}, bk, qk, sk, T.HNone{}, un, lf, ab, False{}}

#
# Bare values stated over parse (docs/rfc/eztoml-grammar-proofs.md, WP-V).
# From every state that waits for a value, the scan keeps a bare word: a
# character that starts one, then characters a bare value keeps, where a
# space is kept only right after a date (the buffer DDDD-DD-DD, the LDate
# state) with a digit after it, as a datetime's time-delim. The word ends at
# a character that ends a bare value (a space, a tab, a line feed, a carriage
# return, #, a comma, ] or }) or at the end of the text, and word.val
# classifies it: the value is placed where the state puts values and the
# rest is read on, or the document has an error. The document laws take the
# classifiers of WP-N1 and WP-T1 (integer_word_exact, float_word_exact,
# boolean_word_exact, date_time_word) to parse.

# a text's characters, last first, onto a list: the buffer the scan pushes
# them onto
def bw.rev(ss: String, acc: List<&2, Char>) -> List<&2, Char>:
  match ss:
    case SNil{}:
      acc
    case SCon{hh, tt}:
      bw.rev(tt, hh <> acc)

# whether a text starts with a digit
def bw.digit1(ss: String) -> Bool:
  match ss:
    case SNil{}:
      False{}
    case SCon{+hh, _tt}:
      Char.is_digit(hh)

# whether a space is where a datetime keeps it: the word so far (buf, last
# character first) is a date, and a digit follows
def bw.dsp(+cc: Char, buf: List<&2, Char>, rest: String) -> Bool:
  Bool.and(Char.is_eq(cc, ' '), Bool.and(T.date.shaped(buf), bw.digit1(rest)))

# the characters after a bare word's first, as the scan keeps them: each one
# a bare value keeps, or a space where a datetime keeps it. buf is the word so
# far, last character first
def bw.more(ss: String, +buf: List<&2, Char>) -> Bool:
  match ss:
    case SNil{}:
      True{}
    case SCon{+hh, +tt}:
      Bool.and(Bool.or(word.char(hh), bw.dsp(hh, buf, tt)), bw.more(tt, hh <> buf))

# a bare word as the scan reads it from a value state: a character that
# starts a bare value, then the characters it keeps
def bw.word(ss: String) -> Bool:
  match ss:
    case SNil{}:
      False{}
    case SCon{+hh, tt}:
      Bool.and(word.first(hh), bw.more(tt, [hh]))

# a text that ends a bare word (buf, last character first): the end of the
# text, or a character that ends a bare value, but not a space the word keeps
# as a datetime's
def bw.end(buf: List<&2, Char>, rest: String) -> Bool:
  match rest:
    case SNil{}:
      True{}
    case SCon{+hh, +tt}:
      Bool.and(T.ch.delim(hh), Bool.not(bw.dsp(hh, buf, tt)))

# the scanner with a bare value placed where the stack puts values, as it is
# after the value's word: a word keeps back, qkind, uni and left
def bw.put(
  sk: List<&2, T.Ctx>,
  vv: T.Val,
  rw: List<&2, T.Val>,
  hs: List<&2, String>,
  +he: List<&2, String>,
  ps: List<&2, String>,
  bk: T.Lex,
  qk: T.QKind,
  un: U32,
  lf: U32,
  ab: Bool
) -> T.St:
  T.take.top(sk, vv, "", rw, hs, he, ps, bk, qk, un, lf, ab, False{})

# the value of the one pair of rows when it is named kk, or none
def bw.got.one(last: Bool, hit: Bool, vv: T.Val) -> T.Got:
  match last hit:
    case True{} True{}:
      T.GotVal{vv}
    case _l _h:
      T.GotBad{""}

# the value of rows that are one pair named kk, or none
def bw.got.rows(rows: List<&2, T.Val>, +kk: String) -> T.Got:
  match rows:
    case T.VPair{nn, vv} <> tt:
      bw.got.one(List.is_empty(&2, T.Val, tt), String.eq(nn, kk), vv)
    case _r:
      T.GotBad{""}

# a document with no error holds what its rows hold
def bw.got.go(ok: Bool, rows: List<&2, T.Val>, +kk: String) -> T.Got:
  match ok:
    case True{}:
      bw.got.rows(rows, kk)
    case False{}:
      T.GotBad{""}

# a document read as a bare word is: the value of its one pair, named kk,
# when it has no error, and no value when it has an error or other rows
def bw.got(dd: T.Doc, +kk: String) -> T.Got:
  match dd:
    case T.Doc{+bad, rows}:
      bw.got.go(String.is_empty(bad), rows, kk)

# how many quotes follow a multi-line string's closing delimiter: 0, 1 or 2
type R2N is Data:
  N0{}
  N1{}
  N2{}
