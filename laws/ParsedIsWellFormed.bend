# For every text `t` of Unicode scalar values shorter than 2^32 characters
# with `bad(parse(t)) == ""`, `wf(parse(t))` holds
import Base
import ../main.bend as T
import ./defs/BareValueGrammar.bend as D1

# WP-R3: laws/ParsedIsWellFormed.bend's invariant. parse keeps the root's rows newest first and
# seals them at the end; wf.go read on those rows as they are, newest first,
# is the invariant for the tables, because a pair the walk adds goes in front
# of the pairs it must not repeat. A state is good when what it has built can
# only seal into a well-formed document: its rows and open frames while it has
# not failed, and always the key segments, the buffer and a held character,
# which hold Unicode scalar values. A failed state is good whatever it holds:
# parse then returns an error, and laws/ParsedIsWellFormed.bend says nothing of it.

# the rest when the scanner has not failed, and True once it has
def gd.ifok(ok: Bool, rest: Bool) -> Bool:
  match ok:
    case True{}:
      rest
    case False{}:
      True{}

# every character is a Unicode scalar value
def gd.cs(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      True{}
    case +h <> t:
      Bool.and(T.wf.char(h), gd.cs(t))

# every segment's characters are Unicode scalar values
def gd.segs(xs: List<&2, String>) -> Bool:
  match xs:
    case []:
      True{}
    case h <> t:
      Bool.and(T.wf.text(h), gd.segs(t))

# a held character is a Unicode scalar value
def gd.hold(hh: T.Hold) -> Bool:
  match hh:
    case T.HNone{}:
      True{}
    case T.HChar{+c}:
      T.wf.char(c)

# no array of tables, in these rows or the tables under them
def gd.na(rows: List<&2, T.Val>) -> Bool:
  match rows:
    case []:
      True{}
    case T.VPair{_n, T.VHead{_p, sub}} <> t:
      Bool.and(gd.na(sub), gd.na(t))
    case T.VPair{_n, T.VAots{_p, _e}} <> _t:
      False{}
    case _ <> t:
      gd.na(t)

# the rows of an open inline table: its dotted keys walk from "" as a root's
# do, so they are well-formed as a root's rows with no array of tables; the
# tables they made become inline tables when it closes
def gd.inl(+rows: List<&2, T.Val>) -> Bool:
  Bool.and(T.wf.go(rows, T.WfRows{""}), gd.na(rows))

# what the open arrays and inline tables have built
def gd.vals(stack: List<&2, T.Ctx>) -> Bool:
  match stack:
    case []:
      True{}
    case T.CArr{items, _p, _h} <> t:
      Bool.and(T.wf.go(items, T.WfItems{}), gd.vals(t))
    case T.CInl{rows, _p, _h} <> t:
      Bool.and(gd.inl(rows), gd.vals(t))

# the keys the open arrays and inline tables saved
def gd.keys(stack: List<&2, T.Ctx>) -> Bool:
  match stack:
    case []:
      True{}
    case T.CArr{_i, parts, here} <> t:
      Bool.and(gd.segs(parts), Bool.and(gd.segs(here), gd.keys(t)))
    case T.CInl{_r, parts, here} <> t:
      Bool.and(gd.segs(parts), Bool.and(gd.segs(here), gd.keys(t)))

# the tables a state has built, while it has not failed
def gd.tr(+bad: String, rows: List<&2, T.Val>, stack: List<&2, T.Ctx>) -> Bool:
  gd.ifok(String.is_empty(bad), Bool.and(T.wf.go(rows, T.WfRows{""}), gd.vals(stack)))

# the characters a state holds: the current table's path, the key's segments,
# the buffer, the saved keys and a held character
def gd.lx(
  here: List<&2, String>,
  parts: List<&2, String>,
  buf: List<&2, Char>,
  stack: List<&2, T.Ctx>,
  hold: T.Hold
) -> Bool:
  Bool.and(gd.segs(here), Bool.and(gd.segs(parts), Bool.and(gd.cs(buf),
    Bool.and(gd.keys(stack), gd.hold(hold)))))

# laws/ParsedIsWellFormed.bend's invariant over every scanner state
def good(st: T.St) -> Bool:
  match st:
    case T.St{+bad, rows, _heads, here, parts, buf, _lex, _back, _q, +stack, hold, _uni,
      _left, _arr, _lead}:
      Bool.and(gd.tr(bad, rows, stack), gd.lx(here, parts, buf, stack, hold))

# the root after a walk, while the walk has not failed
def gd.end(end: T.End) -> Bool:
  match end:
    case T.End{vs, +bad, _h}:
      gd.ifok(String.is_empty(bad), T.wf.go(vs, T.WfRows{""}))

# a value a key's walk may put: no table, well-formed where a pair holds it
def gd.vok(vv: T.Val) -> Bool:
  match vv:
    case T.VHead{_p, _r}:
      False{}
    case T.VAots{_p, _e}:
      False{}
    case T.VArr{items}:
      T.wf.go(items, T.WfItems{})
    case T.VInl{rows}:
      T.wf.go(rows, T.WfInl{})
    case other:
      T.wf.atom(other)

# what a walk is asked to do: put a value a key may hold, or open a table
def gd.job(job: T.Job) -> Bool:
  match job:
    case T.JPut{vv}:
      gd.vok(vv)
    case _:
      True{}

# the scanner's states inside a header
def gd.hd(lex: T.Lex) -> Bool:
  match lex:
    case T.LHead{}:
      True{}
    case T.LHeadGap{}:
      True{}
    case T.LHeadDot{}:
      True{}
    case T.LHeadQ{}:
      True{}
    case T.LHeadE{}:
      True{}
    case T.LHeadU{}:
      True{}
    case T.LHeadR{}:
      True{}
    case _:
      False{}

# LAW: a state that has read nothing of a key, a value or a header, with
# well-formed rows and a current table named by scalar values, is good,
# whatever its other fields; the scanner's start is one
law gd_start:
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +here: List<&2, String>
  for +lex: T.Lex
  for +back: T.Lex
  for +qkind: T.QKind
  for +uni: U32
  for +left: U32
  for +arrtab: Bool
  for +lead: Bool
  for ew: {T.wf.go(rows, T.WfRows{""}) == True{} : Bool}
  for eh: {gd.segs(here) == True{} : Bool}
  {good(T.St{"", rows, heads, here, [], [], lex, back, qkind, [], T.HNone{}, uni, left, arrtab,
    lead}) == True{} : Bool}

# LAW: a walk from the root keeps the rows well-formed: along any path of
# scalar-value segments, with any job that puts no table and a value
# well-formed where a pair holds it, from rows that are well-formed newest
# first, the root it returns is well-formed unless the walk failed
law gd_walk:
  for path: List<&2, String>
  for +rows: List<&2, T.Val>
  for +job: T.Job
  for +bad: String
  for +heads: List<&2, String>
  for +inl: Bool
  for +skip: U32
  for ew: {gd.ifok(String.is_empty(bad), T.wf.go(rows, T.WfRows{""})) == True{} : Bool}
  for ep: {gd.segs(path) == True{} : Bool}
  for ej: {gd.job(job) == True{} : Bool}
  {gd.end(T.tree.walk(path, T.Tw{rows, job, [], bad, "", heads, inl}, skip)) == True{} : Bool}

# LAW: every step inside a header keeps a state good: from every good state,
# whatever its fields, one character that is a Unicode scalar value read in
# any of the seven header states leaves a good state
law gd_header_steps:
  for +lex: T.Lex
  for hl: {gd.hd(lex) == True{} : Bool}
  for +st: T.St
  for eg: {good(st) == True{} : Bool}
  for +cc: Char
  for ec: {T.wf.char(cc) == True{} : Bool}
  {good(T.read.on(lex, st, cc)) == True{} : Bool}

# the scanner's states inside a key, before its `=`, and at the start and
# the end of a line
def gd.ky(lex: T.Lex) -> Bool:
  match lex:
    case T.LTop{}:
      True{}
    case T.LLine{}:
      True{}
    case T.LKey{}:
      True{}
    case T.LKeyDot{}:
      True{}
    case T.LAfter{}:
      True{}
    case T.LKeyQ{}:
      True{}
    case T.LKeyE{}:
      True{}
    case T.LKeyU{}:
      True{}
    case _:
      False{}

# LAW: every step at the start of a line, inside a key or after it keeps a
# state good: from every good state, whatever its fields, one character that
# is a Unicode scalar value read in any of the eight key states leaves a good
# state
law gd_key_steps:
  for +lex: T.Lex
  for hl: {gd.ky(lex) == True{} : Bool}
  for +st: T.St
  for eg: {good(st) == True{} : Bool}
  for +cc: Char
  for ec: {T.wf.char(cc) == True{} : Bool}
  {good(T.read.on(lex, st, cc)) == True{} : Bool}

# LAW: sealing keeps rows well-formed wherever they sit: rows well-formed
# newest first, as the scanner builds them, are well-formed once rows.seal
# has put every table back in the order it was written. A table's names are
# fresh against the pairs before them exactly when they are against the pairs
# after, so the reversal keeps them apart
law gd_seal:
  for +rows: List<&2, T.Val>
  for +at: T.WfAt
  for ew: {T.wf.go(rows, at) == True{} : Bool}
  {T.wf.go(T.rows.seal(rows), at) == True{} : Bool}

# LAW: a good state that ends the text gives a well-formed document whenever
# it gives no error: the document's rows are the state's, sealed
law gd_fin:
  for +st: T.St
  for eg: {good(st) == True{} : Bool}
  for eo: {String.is_empty(T.bad(T.read.fin.doc(st))) == True{} : Bool}
  {T.wf(T.read.fin.doc(st)) == True{} : Bool}

# a value a key may hold, unless the scanner has failed
def gd.okv(st: T.St, val: T.Val) -> Bool:
  match st:
    case T.St{+bad, _rows, _heads, _here, _parts, _buf, _lex, _back, _q, _stack, _hold, _uni, _left, _arr,
      _lead}:
      gd.ifok(String.is_empty(bad), gd.vok(val))

# LAW: placing a finished value keeps a state good: from every good state,
# whatever its fields, a value a key may hold (no table, well-formed where a
# pair holds it) put where the state is (the root through its key's walk, an
# array in front of its items, an inline table through its key's walk) leaves
# a good state; once the scanner has failed, any value does
law gd_take:
  for +st: T.St
  for eg: {good(st) == True{} : Bool}
  for +val: T.Val
  for ev: {gd.okv(st, val) == True{} : Bool}
  {good(T.val.take(st, val)) == True{} : Bool}

# the value states whose steps need no bare word read: a value's start,
# strings, comments, arrays, inline tables and the failed state
def gd.vl(lex: T.Lex) -> Bool:
  match lex:
    case T.LVal{}:
      True{}
    case T.LQ{}:
      True{}
    case T.LQ2{}:
      True{}
    case T.LStr{}:
      True{}
    case T.LEsc{}:
      True{}
    case T.LUni{}:
      True{}
    case T.LFold{}:
      True{}
    case T.LMq{}:
      True{}
    case T.LMqEnd{}:
      True{}
    case T.LTrim{}:
      True{}
    case T.LTrim2{}:
      True{}
    case T.LCom{}:
      True{}
    case T.LSink{}:
      True{}
    case T.LArr{}:
      True{}
    case T.LArrC{}:
      True{}
    case T.LInl{}:
      True{}
    case T.LInlK{}:
      True{}
    case T.LInlC{}:
      True{}
    case _:
      False{}

# LAW: every step in a value, other than one that ends a bare word, keeps a
# state good: from every good state, whatever its fields, one character that
# is a Unicode scalar value read in any of the eighteen states of a value's
# start, a string, a comment, an array, an inline table or the failed state
# leaves a good state
law gd_value_steps:
  for +lex: T.Lex
  for hl: {gd.vl(lex) == True{} : Bool}
  for +st: T.St
  for eg: {good(st) == True{} : Bool}
  for +cc: Char
  for ec: {T.wf.char(cc) == True{} : Bool}
  {good(T.read.on(lex, st, cc)) == True{} : Bool}

# a bare word's value, when it has one, is one a key may hold
def gd.gok(gg: T.Got) -> Bool:
  match gg:
    case T.GotVal{vv}:
      gd.vok(vv)
    case T.GotBad{_why}:
      True{}

# LAW: every value a bare word reads as is well-formed where a key or an array
# holds it: for every list of characters, word.val gives a boolean, a float
# spelled as wf.flo's grammar or inf or nan, an integer of decimal digits with
# no leading zero within signed 64 bits, or a datetime whose fields are in
# range, or no value at all
law gd_word:
  for +cs: List<&2, Char>
  {gd.gok(T.word.val(cs)) == True{} : Bool}

# a bare word's two states: its characters, and the space a datetime may hold
def gd.bw(lex: T.Lex) -> Bool:
  match lex:
    case T.LBare{}:
      True{}
    case T.LDate{}:
      True{}
    case _:
      False{}

# LAW: every step in a bare word keeps a state good: from every good state,
# whatever its fields, one character that is a Unicode scalar value read in a
# bare word's state or a datetime's space leaves a good state; a word that
# ends is read as a value (gd_word) and placed (gd_take)
law gd_bare_steps:
  for +lex: T.Lex
  for hl: {gd.bw(lex) == True{} : Bool}
  for +st: T.St
  for eg: {good(st) == True{} : Bool}
  for +cc: Char
  for ec: {T.wf.char(cc) == True{} : Bool}
  {good(T.read.on(lex, st, cc)) == True{} : Bool}

# LAW: the step parse takes for each character keeps a state good: from every
# good state, whatever its fields, one character that is a Unicode scalar
# value read by the fast step, with a held character and a byte-order mark,
# leaves a good state
law gd_fast_step:
  for +st: T.St
  for eg: {good(st) == True{} : Bool}
  for +cc: Char
  for ec: {T.wf.char(cc) == True{} : Bool}
  {good(T.read.fast(st, cc)) == True{} : Bool}

# LAW: reading a held character keeps a state good
law gd_held:
  for +st: T.St
  for eg: {good(st) == True{} : Bool}
  {good(T.read.once2(st)) == True{} : Bool}

# two texts of the same length
def gd.ln(aa: String, bb: String) -> Bool:
  match aa bb:
    case SNil{} SNil{}:
      True{}
    case SCon{_ah, at} SCon{_bh, bt}:
      gd.ln(at, bt)
    case _a _b:
      False{}

# a plain string's span as parse keeps it: n characters of the cut, each a
# Unicode scalar value, and then the rest of the cut, of scalar values and as
# long as the text still to read. zz says whether n has run down to 0
def gd.sp(cut: String, zz: Bool, +nn: U32, +text: String) -> Bool:
  match cut:
    case SNil{}:
      match zz:
        case True{}:
          Bool.and(T.wf.text(SNil{}), gd.ln(SNil{}, text))
        case False{}:
          False{}
    case SCon{+hh, +tt}:
      match zz:
        case True{}:
          Bool.and(T.wf.text(SCon{hh, tt}), gd.ln(SCon{hh, tt}, text))
        case False{}:
          Bool.and(T.wf.char(hh), gd.sp(tt, U32.is_zero(U32.sub(nn, 1)), U32.sub(nn, 1), text))

# laws/ParsedIsWellFormed.bend's invariant over the modes doc.read reads the text in: a state
# that scans, or follows a carriage return, is good; an opening quote's state
# is good as the quote left it; a plain string's state is good with its
# buffer empty, its span holds scalar values up to the text still to read,
# and the span's count runs on through that text without wrapping
def gd.md(mode: T.Mode, +text: String) -> Bool:
  match mode:
    case T.MScan{st}:
      good(st)
    case T.MCr{st}:
      good(st)
    case T.MOpen{_basic, _q, qkind, bad, rows, heads, here, parts, buf, back, stack, uni, left, arrtab}:
      good(T.St{bad, rows, heads, here, parts, buf, T.LQ{}, back, qkind, stack, T.HNone{}, uni, left, arrtab,
        False{}})
    case T.MEat{_basic, _q, +cut, +nn, bad, rows, heads, here, parts, qkind, stack, uni, left, arrtab}:
      Bool.and(good(T.St{bad, rows, heads, here, parts, [], T.LStr{}, T.LStr{}, qkind, stack, T.HNone{}, uni,
        left, arrtab, False{}}), Bool.and(gd.sp(cut, U32.is_zero(nn), nn, text), D1.counts(text, nn)))

# the mode doc.read moves to on one character, with the text after it
def gd.next(mode: T.Mode, +hh: Char, tt: String) -> T.Mode:
  match mode:
    case T.MOpen{basic, qq, qkind, bad, rows, heads, here, parts, buf, back, stack, uni, left, arrtab}:
      T.doc.open(basic, qq, qkind, bad, rows, heads, here, parts, buf, back, stack, uni, left, arrtab, hh, tt)
    case T.MEat{basic, qq, cut, nn, bad, rows, heads, here, parts, qkind, stack, uni, left, arrtab}:
      T.eat.feed(basic, qq, cut, nn, bad, rows, heads, here, parts, qkind, stack, uni, left, arrtab, hh)
    case T.MScan{st}:
      T.doc.scan(st, hh)
    case T.MCr{st}:
      T.doc.cr(Char.is_eq(hh, '\n'), st, hh)

# LAW: a plain string's span, kept as gd.md keeps it, is a well-formed span:
# its n characters are there and are Unicode scalar values
law gd_span_wf:
  for +cut: String
  for +nn: U32
  for +text: String
  for ep: {gd.sp(cut, U32.is_zero(nn), nn, text) == True{} : Bool}
  {T.wf.span(cut, nn, U32.is_zero(nn)) == True{} : Bool}

# LAW: every step doc.read takes keeps its mode good: from a mode good for a
# text of Unicode scalar values shorter than 2^32 characters, the mode after
# its first character is good for the rest. A scanning state takes the fast
# step, and a quote may open a string's span; a carriage return must meet a
# line feed; an opening quote's next character starts the span, or goes the
# old way; a span's character extends it, or closes it as a VSpan, or copies
# it to the buffer
law gd_mode_step:
  for +mode: T.Mode
  for +hh: Char
  for +tt: String
  for +em: {gd.md(mode, SCon{hh, tt}) == True{} : Bool}
  for eh: {T.wf.char(hh) == True{} : Bool}
  for et: {T.wf.text(tt) == True{} : Bool}
  for es: {D1.short(SCon{hh, tt}) == True{} : Bool}
  {gd.md(gd.next(mode, hh, tt), tt) == True{} : Bool}

# LAW: doc.read takes a character to the mode gd.next names
law gd_next:
  for +mode: T.Mode
  for +hh: Char
  for +tt: String
  {T.doc.read(SCon{hh, tt}, mode) == T.doc.read(tt, gd.next(mode, hh, tt)) : T.Doc}

# LAW: doc.read, from a mode good for a text of Unicode scalar values shorter
# than 2^32 characters, gives a well-formed document whenever it gives no
# error: each character keeps the mode good (gd_mode_step), and at the end a
# token still open is closed, a held character read, and a good end state
# sealed (gd_fin); a string still open is an error
law gd_read:
  for +text: String
  for +mode: T.Mode
  for em: {gd.md(mode, text) == True{} : Bool}
  for +ew: {T.wf.text(text) == True{} : Bool}
  for +es: {D1.short(text) == True{} : Bool}
  for eo: {String.is_empty(T.bad(T.doc.read(text, mode))) == True{} : Bool}
  {T.wf(T.doc.read(text, mode)) == True{} : Bool}

# LAW: parse only accepts what it can give back well-formed: for every text
# of Unicode scalar values shorter than 2^32 characters, a parse with no
# error is a well-formed document
law parse_wf:
  for +text: String
  for ew: {T.wf.text(text) == True{} : Bool}
  for es: {D1.short(text) == True{} : Bool}
  for eo: {String.is_empty(T.bad(T.parse(text))) == True{} : Bool}
  {T.wf(T.parse(text)) == True{} : Bool}
