# In a parsed document shorter than 2^32 characters, a key's name is its
# characters however it was written: a bare key, a basic or literal string
# with its escapes decoded, or a segment of a dotted key or a header. The pair
# is put under those characters in the table its line, header or inline table
# names, so `get` finds it by them in that table's rows, and `at` finds it
# from the root by the names on its path when no array (an array of tables, or
# an array holding an inline table) lies on that path, since `at` enters no
# array (laws/AtWalksKeys.bend)
#
# also rests on: laws/HeaderQuoteAfterBareRefused.bend,
# laws/HeaderQuoteAtStartOpensSegment.bend
import Base
import ../main.bend as T
import ./defs/BareValueGrammar.bend as D1
import ./defs/BlankAndControlChars.bend as D2
import ./defs/KeySegmentSpelling.bend as D3

# WP-H: headers read back. A header as render writes it, `[`, its path, `]`
# and a newline, read from the start of a line, is the rest of the text read
# from the start of the next line, with the rows and definitions the header's
# walk returns (WP-W's contracts say what those are) and the header's
# segments as the current table. A quoted segment leaves back and qkind
# where its last escape and its quote put them, so each law takes the rest of
# the text as read from every back and qkind.

# the scanner at the start of a line in the table here: nothing buffered, no
# array or inline table open, and back, qkind and arrtab as the lines before
# left them
def hb.line(
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  back: T.Lex,
  qkind: T.QKind,
  arrtab: Bool
) -> T.St:
  T.St{"", rows, heads, here, [], [], T.LTop{}, back, qkind, [], T.HNone{}, 0, 0, arrtab,
    False{}}

# LAW: a header as render writes it, `[`, the stored path (the parent's path
# joined with the last segment k, each segment bare or basic-quoted as key
# writes it), `]` and a newline, read from the start of a line, is the rest
# read from the start of the next line in the table named by the segments'
# characters, with the rows and definitions the walk along those names
# returns. Every name reads back as itself, escapes decoded
law header_reads_back:
  for +segs: List<&2, String>
  for +k: String
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +here: List<&2, String>
  for +back: T.Lex
  for +qkind: T.QKind
  for +arrtab: Bool
  for +rows2: List<&2, T.Val>
  for +heads2: List<&2, String>
  for ew: {T.tree.walk(List.append(&2, String, segs, [k]), T.Tw{rows, T.JDef{}, [], "", "", heads,
    False{}}, 0) == T.End{rows2, "", heads2} : T.End}
  for +rest: String
  for +goal: T.Doc
  for ih: @bk: T.Lex -> @qk: T.QKind -> {T.doc.read(rest, T.MScan{hb.line(rows2, heads2,
    List.append(&2, String, segs, [k]), bk, qk, False{})}) == goal : T.Doc}
  {T.doc.read("[" ++ T.tree.pre(D1.tb.join(segs, ""), k) ++ "]\n" ++ rest, T.MScan{hb.line(rows, heads,
    here, back, qkind, arrtab)}) == goal : T.Doc}

# LAW: a header whose last segment names nothing yet in the table its parent
# path leads to reads back with a new, empty table under k's characters at
# the head of that table's rows, recorded as defined by a header, and the
# header's segments as the current table (header_defines_new_table)
law header_new_table_reads_back:
  for +segs: List<&2, String>
  for +k: String
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +eo: {D1.tb.open(segs, rows) == True{} : Bool}
  for em: {T.get(D1.tb.rows(segs, rows), k) == T.Miss{} : T.Hit}
  for +here: List<&2, String>
  for +back: T.Lex
  for +qkind: T.QKind
  for +arrtab: Bool
  for +rest: String
  for +goal: T.Doc
  for ih: @bk: T.Lex -> @qk: T.QKind -> {T.doc.read(rest, T.MScan{hb.line(D1.tb.set(segs, "", rows,
    T.VPair{k, T.VHead{T.tree.pre(D1.tb.join(segs, ""), k), []}} <> D1.tb.rows(segs, rows)),
    T.heads.by.head(T.tree.pre(D1.tb.join(segs, ""), k)) <> heads, List.append(&2, String, segs, [k]),
    bk, qk, False{})}) == goal : T.Doc}
  {T.doc.read("[" ++ T.tree.pre(D1.tb.join(segs, ""), k) ++ "]\n" ++ rest, T.MScan{hb.line(rows, heads,
    here, back, qkind, arrtab)}) == goal : T.Doc}

# LAW: a header whose last segment names a table only made on the way to
# another reads back with that table defined where it is, under the header's
# path, and recorded as defined by a header (header_defines_implicit_table)
law header_implicit_table_reads_back:
  for +segs: List<&2, String>
  for +k: String
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for p: String
  for +sub: List<&2, T.Val>
  for +eo: {D1.tb.open(segs, rows) == True{} : Bool}
  for ef: {T.get(D1.tb.rows(segs, rows), k) == T.Found{T.VHead{p, sub}} : T.Hit}
  for eh: {T.heads.has(heads, T.tree.pre(D1.tb.join(segs, ""), k)) == False{} : Bool}
  for +here: List<&2, String>
  for +back: T.Lex
  for +qkind: T.QKind
  for +arrtab: Bool
  for +rest: String
  for +goal: T.Doc
  for ih: @bk: T.Lex -> @qk: T.QKind -> {T.doc.read(rest, T.MScan{hb.line(D1.tb.set(segs, "", rows,
    T.rows.repl(D1.tb.rows(segs, rows), k, T.VHead{T.tree.pre(D1.tb.join(segs, ""), k), sub})),
    T.heads.by.head(T.tree.pre(D1.tb.join(segs, ""), k)) <> heads, List.append(&2, String, segs, [k]),
    bk, qk, False{})}) == goal : T.Doc}
  {T.doc.read("[" ++ T.tree.pre(D1.tb.join(segs, ""), k) ++ "]\n" ++ rest, T.MScan{hb.line(rows, heads,
    here, back, qkind, arrtab)}) == goal : T.Doc}

# LAW: an array-of-tables header as render writes it, `[[`, the stored path,
# `]]` and a newline, read from the start of a line, is the rest read from the
# start of the next line in the table named by the segments' characters, with
# the rows and definitions the walk along those names returns
law aot_header_reads_back:
  for +segs: List<&2, String>
  for +k: String
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +here: List<&2, String>
  for +back: T.Lex
  for +qkind: T.QKind
  for +arrtab: Bool
  for +rows2: List<&2, T.Val>
  for +heads2: List<&2, String>
  for ew: {T.tree.walk(List.append(&2, String, segs, [k]), T.Tw{rows, T.JAot{}, [], "", "", heads,
    False{}}, 0) == T.End{rows2, "", heads2} : T.End}
  for +rest: String
  for +goal: T.Doc
  for ih: @bk: T.Lex -> @qk: T.QKind -> {T.doc.read(rest, T.MScan{hb.line(rows2, heads2,
    List.append(&2, String, segs, [k]), bk, qk, False{})}) == goal : T.Doc}
  {T.doc.read("[[" ++ T.tree.pre(D1.tb.join(segs, ""), k) ++ "]]\n" ++ rest, T.MScan{hb.line(rows,
    heads, here, back, qkind, arrtab)}) == goal : T.Doc}

# LAW: an array-of-tables header whose last segment names nothing yet reads
# back with an array of one empty element under k's characters at the head
# of the rows its parent path leads to (aot_header_starts_array)
law aot_header_new_array_reads_back:
  for +segs: List<&2, String>
  for +k: String
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +eo: {D1.tb.open(segs, rows) == True{} : Bool}
  for em: {T.get(D1.tb.rows(segs, rows), k) == T.Miss{} : T.Hit}
  for +here: List<&2, String>
  for +back: T.Lex
  for +qkind: T.QKind
  for +arrtab: Bool
  for +rest: String
  for +goal: T.Doc
  for ih: @bk: T.Lex -> @qk: T.QKind -> {T.doc.read(rest, T.MScan{hb.line(D1.tb.set(segs, "", rows,
    T.VPair{k, T.VAots{T.tree.pre(D1.tb.join(segs, ""), k), [T.VAot{T.tree.pre(D1.tb.join(segs, ""), k),
    []}]}} <> D1.tb.rows(segs, rows)), heads, List.append(&2, String, segs, [k]), bk, qk, False{})})
    == goal : T.Doc}
  {T.doc.read("[[" ++ T.tree.pre(D1.tb.join(segs, ""), k) ++ "]]\n" ++ rest, T.MScan{hb.line(rows,
    heads, here, back, qkind, arrtab)}) == goal : T.Doc}

# LAW: an array-of-tables header whose last segment names an array of tables
# reads back with a new empty element in front of its elements, and every
# table under the array forgotten (aot_header_extends_array)
law aot_header_extends_array_reads_back:
  for +segs: List<&2, String>
  for +k: String
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for p: String
  for +elems: List<&2, T.Val>
  for +eo: {D1.tb.open(segs, rows) == True{} : Bool}
  for ef: {T.get(D1.tb.rows(segs, rows), k) == T.Found{T.VAots{p, elems}} : T.Hit}
  for +here: List<&2, String>
  for +back: T.Lex
  for +qkind: T.QKind
  for +arrtab: Bool
  for +rest: String
  for +goal: T.Doc
  for ih: @bk: T.Lex -> @qk: T.QKind -> {T.doc.read(rest, T.MScan{hb.line(D1.tb.set(segs, "", rows,
    T.rows.repl(D1.tb.rows(segs, rows), k, T.VAots{T.tree.pre(D1.tb.join(segs, ""), k),
    T.VAot{T.tree.pre(D1.tb.join(segs, ""), k), []} <> elems})),
    T.heads.drop(heads, String.append(T.tree.pre(D1.tb.join(segs, ""), k), ".")),
    List.append(&2, String, segs, [k]), bk, qk, False{})}) == goal : T.Doc}
  {T.doc.read("[[" ++ T.tree.pre(D1.tb.join(segs, ""), k) ++ "]]\n" ++ rest, T.MScan{hb.line(rows,
    heads, here, back, qkind, arrtab)}) == goal : T.Doc}

# WP-K3: a key's name is its characters however it is written. A key segment
# is bare, a basic string (written as key writes one, escapes decoded) or a
# literal string (its characters as they are, no escapes); a dotted key is
# segments joined by dots, with blank space allowed around each dot; the
# segments of a header are spelled the same way. The laws below read each
# spelling back as its characters, put a dotted key's value under the nested
# tables its segments name, and find it with at.

# a character a literal string may hold: any but the apostrophe and the
# controls other than tab (toml.abnf literal-char)
def lit.char(+cc: Char) -> Bool:
  Bool.not(Bool.or(Char.is_eq(cc, '\''), Bool.and(D2.is_ctl(cc), Bool.not(Char.is_eq(cc, '\t')))))

# a text a literal string may hold
def lit.text(ss: String) -> Bool:
  match ss:
    case SNil{}:
      True{}
    case SCon{+hh, tt}:
      Bool.and(lit.char(hh), lit.text(tt))

# LAW: a literal key reads back as its characters: for every text s a
# literal string can hold, 's' followed by " = 1" parses with no error to
# one pair, named s, holding the integer 1
law literal_key_reads_back:
  for +s: String
  for e: {lit.text(s) == True{} : Bool}
  {T.parse(SCon{'\'', String.append(s, "' = 1")})
    == T.Doc{"", [T.VPair{s, T.VInt{T.Plus{}, "1"}}]} : T.Doc}

# a segment's text
def seg.text(sg: D3.Seg) -> String:
  match sg:
    case D3.Seg{D3.SpBare{}, name}:
      name
    case D3.Seg{D3.SpBasic{}, name}:
      T.key.basic(name)
    case D3.Seg{D3.SpLit{}, name}:
      SCon{'\'', String.append(name, "'")}

# a segment's name
def seg.name(sg: D3.Seg) -> String:
  match sg:
    case D3.Seg{_sp, name}:
      name

# whether a segment's name can be spelled so: a bare name is a bare key, a
# literal one holds no apostrophe and no control but tab, and every name can
# be written as a basic string
def seg.ok(sg: D3.Seg) -> Bool:
  match sg:
    case D3.Seg{D3.SpBare{}, name}:
      T.bare(name)
    case D3.Seg{D3.SpBasic{}, _name}:
      True{}
    case D3.Seg{D3.SpLit{}, name}:
      lit.text(name)

# the text of a dotted key, its segments joined by dots with their blank
# space, then tail
def dk.text(ds: List<&2, D3.Dot>, last: D3.Seg, tail: String) -> String:
  match ds:
    case []:
      String.append(seg.text(last), tail)
    case D3.Dot{sg, g1, g2} <> rest:
      String.append(seg.text(sg), String.append(D2.gap(g1), SCon{'.', String.append(D2.gap(g2),
        dk.text(rest, last, tail))}))

# the names of a dotted key's segments, in order
def dk.names(ds: List<&2, D3.Dot>, last: D3.Seg) -> List<&2, String>:
  match ds:
    case []:
      [seg.name(last)]
    case D3.Dot{sg, _g1, _g2} <> rest:
      seg.name(sg) <> dk.names(rest, last)

# whether every segment of a dotted key can be spelled as it is
def dk.ok(ds: List<&2, D3.Dot>, last: D3.Seg) -> Bool:
  match ds:
    case []:
      seg.ok(last)
    case D3.Dot{sg, _g1, _g2} <> rest:
      Bool.and(seg.ok(sg), dk.ok(rest, last))

# the scanner after a key's `=`, waiting for its value in the table here:
# the key's segments in parts, newest first
def kb.val(
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  parts: List<&2, String>,
  back: T.Lex,
  qkind: T.QKind,
  arrtab: Bool
) -> T.St:
  T.St{"", rows, heads, here, parts, [], T.LVal{}, back, qkind, [], T.HNone{}, 0, 0, arrtab,
    False{}}

# LAW: a dotted key reads back as its segments' names: from the start of a
# line in any table, a key of segments each bare, basic or literal, joined
# by dots with blank space around them, then blank space and `=`, is the rest
# read waiting for the value with every segment's characters, escapes
# decoded, as the key's parts
law dotted_key_reads_back:
  for +ds: List<&2, D3.Dot>
  for +last: D3.Seg
  for ok: {dk.ok(ds, last) == True{} : Bool}
  for +g: List<&2, Bool>
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +here: List<&2, String>
  for +back: T.Lex
  for +qkind: T.QKind
  for +arrtab: Bool
  for +rest: String
  for +goal: T.Doc
  for ih: @bk: T.Lex -> @qk: T.QKind -> {T.doc.read(rest, T.MScan{kb.val(rows, heads, here,
    List.reverse(&2, String, dk.names(ds, last)), bk, qk, arrtab)}) == goal : T.Doc}
  {T.doc.read(dk.text(ds, last, String.append(D2.gap(g), SCon{'=', rest})), T.MScan{hb.line(rows,
    heads, here, back, qkind, arrtab)}) == goal : T.Doc}

# A key's value is put by a walk along the current table's path then the
# key's segments. The walk counts skip down past the current table's
# segments, which are navigation; once skip reaches zero each segment is a
# dotted key's, which may enter a table no header defined, or make a new
# implicit one, and records the table's path behind `.` (heads.by.dot) the
# first time. WP-W's walk_put_at_head is the case where skip never reaches
# zero.

# whether a dotted key's segment goes on through what its name refers to:
# nothing yet, or a table no header defined
def dk.can.dot(look: T.Look, heads: List<&2, String>, +path: String) -> Bool:
  match look:
    case T.KMiss{}:
      True{}
    case T.KHead{_p, _rows}:
      Bool.not(T.heads.head(heads, path))
    case _:
      False{}

# whether a walk step goes on: navigation when zz is false, a dotted key's
# segment when it is true
def dk.can(zz: Bool, look: T.Look, heads: List<&2, String>, +path: String) -> Bool:
  match zz:
    case False{}:
      D1.tb.can(look)
    case True{}:
      dk.can.dot(look, heads, path)

# a table's path recorded behind `.`, unless it is recorded already
def dk.mark.new(seen: Bool, path: String, heads: List<&2, String>) -> List<&2, String>:
  match seen:
    case True{}:
      heads
    case False{}:
      SCon{'.', path} <> heads

# the definitions after a walk step: navigation records none, a dotted key's
# segment records its table's path behind `.` unless it is recorded already
def dk.mark(zz: Bool, +path: String, +heads: List<&2, String>) -> List<&2, String>:
  match zz:
    case False{}:
      heads
    case True{}:
      dk.mark.new(T.heads.has(heads, path), path, heads)

# whether a put's walk goes on through every segment of the path, from the
# table pre names, with the definitions heads and the count skip
def dk.open(
  path: List<&2, String>,
  +pre: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +skip: U32
) -> Bool:
  match path:
    case []:
      True{}
    case +seg <> rest:
      Bool.and(dk.can(U32.is_zero(skip), T.rows.look(rows, seg), heads, T.tree.pre(pre, seg)),
        dk.open(rest, T.tree.pre(pre, seg), D1.tb.into(T.rows.look(rows, seg)),
          dk.mark(U32.is_zero(skip), T.tree.pre(pre, seg), heads), T.path.dec(skip)))

# the definitions after a put's walk along the path
def dk.heads(
  path: List<&2, String>,
  +pre: String,
  +heads: List<&2, String>,
  +skip: U32
) -> List<&2, String>:
  match path:
    case []:
      heads
    case +seg <> rest:
      dk.heads(rest, T.tree.pre(pre, seg), dk.mark(U32.is_zero(skip), T.tree.pre(pre, seg), heads),
        T.path.dec(skip))

# the names of the segments a dot follows
def dk.init(ds: List<&2, D3.Dot>) -> List<&2, String>:
  match ds:
    case []:
      []
    case D3.Dot{sg, _g1, _g2} <> rest:
      seg.name(sg) <> dk.init(rest)

# LAW: a value put along a path the walk goes on through, navigation then a
# dotted key's segments, to a name the table at its end does not hold, goes at
# the head of that table's rows; every table on the way is entered or made
# under its segment's name, and each table a dotted key's segment reached is
# recorded as defined by dotted keys. This is walk_put_at_head with skip
# allowed to reach zero
law dotted_put_at_head:
  for +path: List<&2, String>
  for +k: String
  for +v: T.Val
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +skip: U32
  for +inl: Bool
  for +eo: {dk.open(path, "", rows, heads, skip) == True{} : Bool}
  for em: {T.get(D1.tb.rows(path, rows), k) == T.Miss{} : T.Hit}
  {T.tree.walk(List.append(&2, String, path, [k]), T.Tw{rows, T.JPut{v}, [], "", "", heads, inl}, skip)
    == T.End{D1.tb.set(path, "", rows, T.VPair{k, v} <> D1.tb.rows(path, rows)), "",
      dk.heads(path, "", heads, skip)} : T.End}

# LAW: a key/value line of a dotted key, spelled any way, and the value 1,
# read from the start of a line in the table here, is the rest read from the
# start of the next line with the rows and definitions the put's walk along
# here and the segments' names returns
law dotted_key_pair_reads_back:
  for +ds: List<&2, D3.Dot>
  for +last: D3.Seg
  for ok: {dk.ok(ds, last) == True{} : Bool}
  for +g: List<&2, Bool>
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +here: List<&2, String>
  for +back: T.Lex
  for +qkind: T.QKind
  for +arrtab: Bool
  for +rows2: List<&2, T.Val>
  for +heads2: List<&2, String>
  for ew: {T.tree.walk(List.append(&2, String, here, dk.names(ds, last)), T.Tw{rows, T.JPut{D1.one()}, [],
    "", "", heads, False{}}, T.path.len(here, 0)) == T.End{rows2, "", heads2} : T.End}
  for +rest: String
  for +goal: T.Doc
  for ih: @bk: T.Lex -> @qk: T.QKind -> {T.doc.read(rest, T.MScan{hb.line(rows2, heads2, here, bk, qk,
    arrtab)}) == goal : T.Doc}
  {T.doc.read(dk.text(ds, last, String.append(D2.gap(g), String.append("= 1\n", rest))),
    T.MScan{hb.line(rows, heads, here, back, qkind, arrtab)}) == goal : T.Doc}

# LAW: and when the walk goes on through the current table and every segment
# before the last, and the table there does not hold the last name, the line
# puts the value at the head of that table's rows, under the last name's
# characters, in nested tables named by the other segments' characters
# (dotted_put_at_head)
law dotted_key_pair_puts_value:
  for +ds: List<&2, D3.Dot>
  for +last: D3.Seg
  for ok: {dk.ok(ds, last) == True{} : Bool}
  for +g: List<&2, Bool>
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +here: List<&2, String>
  for +eo: {dk.open(List.append(&2, String, here, dk.init(ds)), "", rows, heads, T.path.len(here, 0))
    == True{} : Bool}
  for em: {T.get(D1.tb.rows(List.append(&2, String, here, dk.init(ds)), rows), seg.name(last)) == T.Miss{}
    : T.Hit}
  for +back: T.Lex
  for +qkind: T.QKind
  for +arrtab: Bool
  for +rest: String
  for +goal: T.Doc
  for ih: @bk: T.Lex -> @qk: T.QKind -> {T.doc.read(rest, T.MScan{hb.line(D1.tb.set(List.append(&2, String,
    here, dk.init(ds)), "", rows, T.VPair{seg.name(last), D1.one()} <> D1.tb.rows(List.append(&2, String, here,
    dk.init(ds)), rows)), dk.heads(List.append(&2, String, here, dk.init(ds)), "", heads, T.path.len(here,
    0)), here, bk, qk, arrtab)}) == goal : T.Doc}
  {T.doc.read(dk.text(ds, last, String.append(D2.gap(g), String.append("= 1\n", rest))),
    T.MScan{hb.line(rows, heads, here, back, qkind, arrtab)}) == goal : T.Doc}

# LAW: a document of one key/value line, a dotted key spelled any way and the
# value 1, parses with no error to the value under the last name's
# characters, in nested tables named by the other segments' characters
law dotted_key_line_reads_back:
  for +ds: List<&2, D3.Dot>
  for +last: D3.Seg
  for +ok: {dk.ok(ds, last) == True{} : Bool}
  for +g: List<&2, Bool>
  {T.parse(dk.text(ds, last, String.append(D2.gap(g), "= 1\n")))
    == T.Doc{"", T.rows.seal(D1.tb.set(dk.init(ds), "", [], [T.VPair{seg.name(last), D1.one()}]))} : T.Doc}

# LAW: and at finds the value by the segments' names: a key's name is its
# characters however it was written
law dotted_key_line_found_by_at:
  for +ds: List<&2, D3.Dot>
  for +last: D3.Seg
  for ok: {dk.ok(ds, last) == True{} : Bool}
  for +g: List<&2, Bool>
  {T.at(T.root(T.parse(dk.text(ds, last, String.append(D2.gap(g), "= 1\n")))), dk.names(ds, last))
    == T.Found{D1.one()} : T.Hit}

# A header's segments are spelled the same way, bare, basic or literal, and
# joined the same way, by dots with blank space around them, with blank
# space allowed after the opening bracket and before the closing one. WP-H's
# header_reads_back reads the segments as key writes them; the laws below
# read every spelling.

# a header line: `[` (`[[` for an array of tables), blank space, a dotted
# key's text, blank space, `]` (`]]`), a newline, then rest
def hd.line(
  arr: Bool,
  g0: List<&2, Bool>,
  ds: List<&2, D3.Dot>,
  last: D3.Seg,
  g9: List<&2, Bool>,
  rest: String
) -> String:
  match arr:
    case False{}:
      SCon{'[', String.append(D2.gap(g0), dk.text(ds, last, String.append(D2.gap(g9), SCon{']', SCon{'\n', rest}})))}
    case True{}:
      SCon{'[', SCon{'[', String.append(D2.gap(g0), dk.text(ds, last, String.append(D2.gap(g9), SCon{']', SCon{']',
        SCon{'\n', rest}}})))}}

# the path a header names: its segments' names, the last one last
def hd.path(ds: List<&2, D3.Dot>, last: D3.Seg) -> List<&2, String>:
  List.append(&2, String, dk.init(ds), [seg.name(last)])

# LAW: a header line whose segments are each bare, basic or literal, with
# blank space around its dots and inside its brackets, read from the start of
# a line, is the rest read from the start of the next line in the table named
# by the segments' characters, escapes decoded, with the rows and definitions
# the header's walk along those names returns; for a `[table]` header and an
# `[[array]]` one alike
law header_segments_read_back:
  for +arr: Bool
  for +g0: List<&2, Bool>
  for +ds: List<&2, D3.Dot>
  for +last: D3.Seg
  for ok: {dk.ok(ds, last) == True{} : Bool}
  for +g9: List<&2, Bool>
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +here: List<&2, String>
  for +back: T.Lex
  for +qkind: T.QKind
  for +arrtab: Bool
  for +rows2: List<&2, T.Val>
  for +heads2: List<&2, String>
  for ew: {T.tree.walk(hd.path(ds, last), T.Tw{rows, D1.header_job(arr), [], "", "", heads, False{}}, 0)
    == T.End{rows2, "", heads2} : T.End}
  for +rest: String
  for +goal: T.Doc
  for ih: @bk: T.Lex -> @qk: T.QKind -> {T.doc.read(rest, T.MScan{hb.line(rows2, heads2, hd.path(ds, last), bk,
    qk, False{})}) == goal : T.Doc}
  {T.doc.read(hd.line(arr, g0, ds, last, g9, rest), T.MScan{hb.line(rows, heads, here, back, qkind, arrtab)})
    == goal : T.Doc}

# LAW: a document of one `[table]` header, its segments spelled any way,
# parses with no error to an empty table under the last name's characters,
# in nested tables named by the other segments' characters
law header_line_reads_back:
  for +g0: List<&2, Bool>
  for +ds: List<&2, D3.Dot>
  for +last: D3.Seg
  for +ok: {dk.ok(ds, last) == True{} : Bool}
  for +g9: List<&2, Bool>
  {T.parse(hd.line(False{}, g0, ds, last, g9, "")) == T.Doc{"", T.rows.seal(D1.tb.set(dk.init(ds), "", [],
    [T.VPair{seg.name(last), T.VHead{T.tree.pre(D1.tb.join(dk.init(ds), ""), seg.name(last)), []}}]))} : T.Doc}

# LAW: and at finds that table by the segments' names
law header_line_found_by_at:
  for +g0: List<&2, Bool>
  for +ds: List<&2, D3.Dot>
  for +last: D3.Seg
  for ok: {dk.ok(ds, last) == True{} : Bool}
  for +g9: List<&2, Bool>
  {T.at(T.root(T.parse(hd.line(False{}, g0, ds, last, g9, ""))), hd.path(ds, last))
    == T.Found{T.VHead{T.tree.pre(D1.tb.join(dk.init(ds), ""), seg.name(last)), []}} : T.Hit}

# basic-unescaped: any character but `"`, `\` and the controls other than tab
def k3.bchar(+cc: Char) -> Bool:
  Bool.not(Bool.or(Char.is_eq(cc, '"'), Bool.or(Char.is_eq(cc, '\\'), Bool.and(D2.is_ctl(cc),
    Bool.not(Char.is_eq(cc, '\t'))))))

# whether a basic string may hold the piece: a character written as itself
# must be basic-unescaped, and an escape's digits must name a Unicode scalar
# value
def k3.pc.ok(pp: D3.KPiece) -> Bool:
  match pp:
    case D3.KpChar{cc}:
      k3.bchar(cc)
    case D3.KpEsc{_mm}:
      True{}
    case D3.KpU4{dd, cc, bb, aa}:
      D3.k3.scalar(D3.k3.hex4(dd, cc, bb, aa))
    case D3.KpU8{hh, gg, ff, ee, dd, cc, bb, aa}:
      D3.k3.scalar(D3.k3.hex8(hh, gg, ff, ee, dd, cc, bb, aa))

# whether a basic string may hold every piece
def k3.pcs.ok(ps: List<&2, D3.KPiece>) -> Bool:
  match ps:
    case []:
      True{}
    case pp <> rest:
      Bool.and(k3.pc.ok(pp), k3.pcs.ok(rest))

# LAW: a basic key reads back as its characters however it is spelled: for
# every list of pieces a basic string may hold, the key they spell in
# quotation marks, then " = 1", parses with no error to one pair named by the
# characters the pieces stand for, holding 1
law basic_key_reads_back:
  for +ps: List<&2, D3.KPiece>
  for ok: {k3.pcs.ok(ps) == True{} : Bool}
  {T.parse(SCon{'"', D3.k3.pcs.text(ps, "\" = 1")}) == T.Doc{"", [T.VPair{D3.k3.pcs.name(ps), D1.one()}]} : T.Doc}

# whether a segment is spelled as toml.abnf allows: a bare one is a bare
# key, a basic one's pieces a basic string may hold, and a literal one's
# characters a literal string may hold
def k3.seg.ok(sg: D3.KSeg) -> Bool:
  match sg:
    case D3.KsBare{name}:
      T.bare(name)
    case D3.KsBasic{pl}:
      k3.pcs.ok(pl)
    case D3.KsLit{name}:
      lit.text(name)

# a segment of a dotted key that a dot follows, with the blank space before
# the dot and after it
type KDot is Data:
  KDot{seg: D3.KSeg, g1: List<&2, Bool>, g2: List<&2, Bool>}

# the text of a dotted key, its segments joined by dots with their blank
# space, then tail
def k3.dk.text(ds: List<&2, KDot>, last: D3.KSeg, tail: String) -> String:
  match ds:
    case []:
      D3.k3.seg.text(last, tail)
    case KDot{sg, g1, g2} <> rest:
      D3.k3.seg.text(sg, String.append(D2.gap(g1), SCon{'.', String.append(D2.gap(g2), k3.dk.text(rest, last, tail))}))

# the names of a dotted key's segments, in order
def k3.dk.names(ds: List<&2, KDot>, last: D3.KSeg) -> List<&2, String>:
  match ds:
    case []:
      [D3.k3.seg.name(last)]
    case KDot{sg, _g1, _g2} <> rest:
      D3.k3.seg.name(sg) <> k3.dk.names(rest, last)

# whether every segment of a dotted key is spelled as toml.abnf allows
def k3.dk.ok(ds: List<&2, KDot>, last: D3.KSeg) -> Bool:
  match ds:
    case []:
      k3.seg.ok(last)
    case KDot{sg, _g1, _g2} <> rest:
      Bool.and(k3.seg.ok(sg), k3.dk.ok(rest, last))

# where a key may start: at the start of a line, after an inline table's
# `{`, or after a comma in one
type KPos is Data:
  AtLine{}
  AtInl{}
  AtInlK{}

# the scanner's state there
def k3.pos.lex(at: KPos) -> T.Lex:
  match at:
    case AtLine{}:
      T.LTop{}
    case AtInl{}:
      T.LInl{}
    case AtInlK{}:
      T.LInlK{}

# a scanner where a key may start, having read nothing of it, with the
# tables, the stack of open arrays and inline tables and the other fields as
# the text before left them
def k3.at(
  at: KPos,
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  stack: List<&2, T.Ctx>,
  arrtab: Bool,
  back: T.Lex,
  qkind: T.QKind,
  uni: U32,
  left: U32
) -> T.St:
  T.St{"", rows, heads, here, [], [], k3.pos.lex(at), back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}}

# a scanner after a key's `=`, waiting for its value: the key's segments in
# parts, newest first
def k3.val(
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  parts: List<&2, String>,
  stack: List<&2, T.Ctx>,
  arrtab: Bool,
  back: T.Lex,
  qkind: T.QKind,
  uni: U32,
  left: U32
) -> T.St:
  T.St{"", rows, heads, here, parts, [], T.LVal{}, back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}}

# the rest of the text read once a key's `=` is read, wherever the key's
# segments left back, qkind, uni and left
def k3.KeyThen(
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  parts: List<&2, String>,
  stack: List<&2, T.Ctx>,
  arrtab: Bool,
  rest: String,
  goal: T.Doc
) -> Type:
  @bk: T.Lex -> @qk: T.QKind -> @un: U32 -> @lf: U32 ->
    {T.doc.read(rest, T.MScan{k3.val(rows, heads, here, parts, stack, arrtab, bk, qk, un, lf)}) == goal : T.Doc}

# LAW: a key reads back as its characters wherever a key may start: at the
# start of a line in any table, or in an inline table after its `{` or a
# comma, whatever the stack and the other fields hold, blank space, a key of
# segments each bare, basic or literal and spelled any way toml.abnf allows,
# joined by dots with blank space around them, then blank space and `=`,
# leave the scanner waiting for the value with every segment's characters,
# escapes decoded, as the key's parts
law key_reads_back_anywhere:
  for +at: KPos
  for +g0: List<&2, Bool>
  for +ds: List<&2, KDot>
  for +last: D3.KSeg
  for ok: {k3.dk.ok(ds, last) == True{} : Bool}
  for +g: List<&2, Bool>
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +here: List<&2, String>
  for +stack: List<&2, T.Ctx>
  for +arrtab: Bool
  for +back: T.Lex
  for +qkind: T.QKind
  for +uni: U32
  for +left: U32
  for +rest: String
  for +goal: T.Doc
  for ih: k3.KeyThen(rows, heads, here, List.reverse(&2, String, k3.dk.names(ds, last)), stack, arrtab, rest, goal)
  {T.doc.read(String.append(D2.gap(g0), k3.dk.text(ds, last, String.append(D2.gap(g), SCon{'=', rest}))),
    T.MScan{k3.at(at, rows, heads, here, stack, arrtab, back, qkind, uni, left)}) == goal : T.Doc}

# a header's text: `[` (`[[` for an array of tables), blank space, a dotted
# key's text, blank space, `]` (`]]`), then rest
def k3.hd.text(
  arr: Bool,
  g0: List<&2, Bool>,
  ds: List<&2, KDot>,
  last: D3.KSeg,
  g9: List<&2, Bool>,
  rest: String
) -> String:
  match arr:
    case False{}:
      SCon{'[', String.append(D2.gap(g0), k3.dk.text(ds, last, String.append(D2.gap(g9), SCon{']', rest})))}
    case True{}:
      SCon{'[', SCon{'[', String.append(D2.gap(g0), k3.dk.text(ds, last, String.append(D2.gap(g9), SCon{']', SCon{']',
        rest}})))}}

# a scanner after a whole expression, in the table here, before the end of
# its line
def k3.line(
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  back: T.Lex,
  qkind: T.QKind,
  uni: U32,
  left: U32
) -> T.St:
  T.St{"", rows, heads, here, [], [], T.LLine{}, back, qkind, [], T.HNone{}, uni, left, False{}, False{}}

# LAW: a header reads back as the table named by its segments' characters,
# however they are written: from the start of a line in any table, with no
# array or inline table open and whatever the other fields hold, `[` (`[[`),
# blank space, segments each bare, basic or literal and spelled any way
# toml.abnf allows, joined by dots with blank space around them, blank space
# and `]` (`]]`) run the header's walk along the segments' characters, escapes
# decoded, and leave the scanner in that table with the rows and definitions
# the walk returns
law header_reads_back_anywhere:
  for +arr: Bool
  for +g0: List<&2, Bool>
  for +ds: List<&2, KDot>
  for +last: D3.KSeg
  for ok: {k3.dk.ok(ds, last) == True{} : Bool}
  for +g9: List<&2, Bool>
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +here: List<&2, String>
  for +arrtab: Bool
  for +back: T.Lex
  for +qkind: T.QKind
  for +uni: U32
  for +left: U32
  for +rows2: List<&2, T.Val>
  for +heads2: List<&2, String>
  for ew: {T.tree.walk(k3.dk.names(ds, last), T.Tw{rows, D1.header_job(arr), [], "", "", heads, False{}}, 0)
    == T.End{rows2, "", heads2} : T.End}
  for +rest: String
  for +goal: T.Doc
  for ih: @bk: T.Lex -> @qk: T.QKind -> @un: U32 -> @lf: U32 -> {T.doc.read(rest, T.MScan{k3.line(rows2, heads2,
    k3.dk.names(ds, last), bk, qk, un, lf)}) == goal : T.Doc}
  {T.doc.read(k3.hd.text(arr, g0, ds, last, g9, rest), T.MScan{k3.at(AtLine{}, rows, heads, here, [], arrtab, back,
    qkind, uni, left)}) == goal : T.Doc}

# a key found in a parsed document. k3.has(rows, path, k) says the
# rows hold a pair named k in the table the path names: the path's first
# name is some pair's in the rows, every pair of that name holds the rest of
# the path, and the last table's rows are ones get finds k in. A table's
# rows, an inline table's and an element of an array of tables hold the path
# as rows do; an array of tables or an array holds it when some element or
# item does, so at, which enters no array, is not needed to say it. Names
# compare as get compares them (str.eq).

# how k3.h reads its list, and the rest of the path: the rows seen for one
# name, or the elements of an array of tables or the items of an array
type KHm is Data:
  KhAll{name: String, path: List<&2, String>}
  KhSome{path: List<&2, String>}

# whether a lookup found something
def k3.found(hh: T.Hit) -> Bool:
  match hh:
    case T.Found{_v}:
      True{}
    case T.Miss{}:
      False{}

# whether a list, read as md says, holds a pair named kk at the end of the
# path. A table's rows are read in place: kk found in them at the end of the
# path, or the next name found in them and every pair of it holding the rest
def k3.h(xs: List<&2, T.Val>, md: KHm, +kk: String) -> Bool:
  match xs md:
    case [] KhAll{_n, _p}:
      True{}
    case T.VPair{+mm, T.VHead{_q, rows}} <> tt KhAll{+nn, Nil{}}:
      Bool.and(Bool.or(Bool.not(T.str.eq(mm, nn)), k3.found(T.get(rows, kk))), k3.h(tt, KhAll{nn, []}, kk))
    case T.VPair{+mm, T.VHead{_q, +rows}} <> tt KhAll{+nn, +n2 <> +p2}:
      Bool.and(Bool.or(Bool.not(T.str.eq(mm, nn)), Bool.and(k3.found(T.get(rows, n2)), k3.h(rows, KhAll{n2, p2},
        kk))), k3.h(tt, KhAll{nn, n2 <> p2}, kk))
    case T.VPair{+mm, T.VInl{rows}} <> tt KhAll{+nn, Nil{}}:
      Bool.and(Bool.or(Bool.not(T.str.eq(mm, nn)), k3.found(T.get(rows, kk))), k3.h(tt, KhAll{nn, []}, kk))
    case T.VPair{+mm, T.VInl{+rows}} <> tt KhAll{+nn, +n2 <> +p2}:
      Bool.and(Bool.or(Bool.not(T.str.eq(mm, nn)), Bool.and(k3.found(T.get(rows, n2)), k3.h(rows, KhAll{n2, p2},
        kk))), k3.h(tt, KhAll{nn, n2 <> p2}, kk))
    case T.VPair{+mm, T.VAots{_q, es}} <> tt KhAll{+nn, +pp}:
      Bool.and(Bool.or(Bool.not(T.str.eq(mm, nn)), k3.h(es, KhSome{pp}, kk)), k3.h(tt, KhAll{nn, pp}, kk))
    case T.VPair{+mm, T.VArr{items}} <> tt KhAll{+nn, +pp}:
      Bool.and(Bool.or(Bool.not(T.str.eq(mm, nn)), k3.h(items, KhSome{pp}, kk)), k3.h(tt, KhAll{nn, pp}, kk))
    case T.VPair{+mm, _v} <> tt KhAll{+nn, +pp}:
      Bool.and(Bool.not(T.str.eq(mm, nn)), k3.h(tt, KhAll{nn, pp}, kk))
    case _h <> tt KhAll{+nn, +pp}:
      k3.h(tt, KhAll{nn, pp}, kk)
    case [] KhSome{_p}:
      False{}
    case T.VAot{_q, rows} <> tt KhSome{Nil{}}:
      Bool.or(k3.found(T.get(rows, kk)), k3.h(tt, KhSome{[]}, kk))
    case T.VAot{_q, +rows} <> tt KhSome{+n2 <> +p2}:
      Bool.or(Bool.and(k3.found(T.get(rows, n2)), k3.h(rows, KhAll{n2, p2}, kk)), k3.h(tt, KhSome{n2 <> p2}, kk))
    case T.VInl{rows} <> tt KhSome{Nil{}}:
      Bool.or(k3.found(T.get(rows, kk)), k3.h(tt, KhSome{[]}, kk))
    case T.VInl{+rows} <> tt KhSome{+n2 <> +p2}:
      Bool.or(Bool.and(k3.found(T.get(rows, n2)), k3.h(rows, KhAll{n2, p2}, kk)), k3.h(tt, KhSome{n2 <> p2}, kk))
    case T.VArr{items} <> tt KhSome{+pp}:
      Bool.or(k3.h(items, KhSome{pp}, kk), k3.h(tt, KhSome{pp}, kk))
    case _v <> tt KhSome{+pp}:
      k3.h(tt, KhSome{pp}, kk)

# the path under which a value taken now is found at the end: the current
# table and the key's parts at the root; an array's item is found where the
# array is; a pair in an inline table under the key's parts where the
# inline table is
def k3.pl(
  stack: List<&2, T.Ctx>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +pp: List<&2, String>
) -> List<&2, String>:
  match stack:
    case []:
      List.append(&2, String, List.append(&2, String, here, List.reverse(&2, String, parts)), pp)
    case T.CArr{_i, +sp, +sh} <> rest:
      k3.pl(rest, sh, sp, pp)
    case T.CInl{_r, +sp, +sh} <> rest:
      k3.pl(rest, sh, sp, List.append(&2, String, List.reverse(&2, String, parts), pp))

# whether the rows hold a pair named kk in the table the path names
def k3.has(+rows: List<&2, T.Val>, path: List<&2, String>, +kk: String) -> Bool:
  match path:
    case []:
      k3.found(T.get(rows, kk))
    case +nn <> pp:
      Bool.and(k3.found(T.get(rows, nn)), k3.h(rows, KhAll{nn, pp}, kk))

# whether a bare word's refusal says why: a value, or a reason that is not
# empty
def k3.why(gg: T.Got) -> Bool:
  match gg:
    case T.GotVal{_v}:
      True{}
    case T.GotBad{why}:
      Bool.not(String.is_empty(why))

# LAW: a bare word the scanner refuses is refused with a reason: for every
# list of characters, word.val gives a value, or a reason that is not empty,
# so a refused value always leaves the document with an error
law bare_word_refusal_says_why:
  for +cs: List<&2, Char>
  {k3.why(T.word.val(cs)) == True{} : Bool}

# the names of a dotted key's segments but the last, in order
def k3.dk.init(ds: List<&2, KDot>) -> List<&2, String>:
  match ds:
    case []:
      []
    case KDot{sg, _g1, _g2} <> rest:
      D3.k3.seg.name(sg) <> k3.dk.init(rest)

# no array is open around a key: the innermost open frame, if any, is an
# inline table
def k3.noarr1(stack: List<&2, T.Ctx>) -> Bool:
  match stack:
    case []:
      True{}
    case T.CArr{_i, _p, _h} <> _t:
      False{}
    case T.CInl{_r, _p, _h} <> _t:
      True{}

# the table a key read with the scanner in this state is put in: the
# current table and the key's other segments at the root, or those segments
# in an open inline table, where that table is put
def k3.key.table(stack: List<&2, T.Ctx>, +here: List<&2, String>, ds: List<&2, KDot>) -> List<&2, String>:
  k3.pl(stack, here, List.reverse(&2, String, k3.dk.init(ds)), [])

# a key's text and the rest of a document read from where a key may start
def k3.key.doc(
  at: KPos,
  g0: List<&2, Bool>,
  ds: List<&2, KDot>,
  last: D3.KSeg,
  gs: List<&2, Bool>,
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  stack: List<&2, T.Ctx>,
  arrtab: Bool,
  back: T.Lex,
  qkind: T.QKind,
  uni: U32,
  left: U32,
  rest: String
) -> T.Doc:
  T.doc.read(String.append(D2.gap(g0), k3.dk.text(ds, last, String.append(D2.gap(gs), SCon{'=', rest}))),
    T.MScan{k3.at(at, rows, heads, here, stack, arrtab, back, qkind, uni, left)})

# LAW: a key's value, whatever it is, is put under the key's name in the
# key's table: after a key's `=`, with the key's segments newest first in
# parts and no array open around the key, the rest of any text read leaves a
# document that has an error or whose root holds a pair named by the key's
# last segment in the table k3.pl names (laws/KeyNameIsItsCharacters.bend's any value)
law key_found_after_equals:
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +here: List<&2, String>
  for +k: String
  for +ps: List<&2, String>
  for +stack: List<&2, T.Ctx>
  for +arrtab: Bool
  for +back: T.Lex
  for +qkind: T.QKind
  for +uni: U32
  for +left: U32
  for +rest: String
  for es: {k3.noarr1(stack) == True{} : Bool}
  for eo: {String.is_empty(T.bad(T.doc.read(rest, T.MScan{k3.val(rows, heads, here, k <> ps, stack, arrtab, back,
    qkind, uni, left)}))) == True{} : Bool}
  {k3.has(T.root(T.doc.read(rest, T.MScan{k3.val(rows, heads, here, k <> ps, stack, arrtab, back, qkind, uni,
    left)})), k3.pl(stack, here, ps, []), k) == True{} : Bool}

# LAW: a key is put under its characters in the table its line or inline
# table names, however it is written: wherever a key may start (the start of
# a line in any table, or an inline table after its `{` or a comma), with no
# array open around it and whatever the other fields hold, blank space, a
# dotted key of segments each bare, basic or literal and spelled any way
# toml.abnf allows, blank space, `=` and then any text leave a document that
# has an error or whose root holds a pair named by the last segment's
# characters in the table the other segments name from the current table
# (k3.key.table), so get finds it by them in that table's rows
law key_found_anywhere:
  for +at: KPos
  for +g0: List<&2, Bool>
  for +ds: List<&2, KDot>
  for +last: D3.KSeg
  for ok: {k3.dk.ok(ds, last) == True{} : Bool}
  for +g: List<&2, Bool>
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +here: List<&2, String>
  for +stack: List<&2, T.Ctx>
  for +arrtab: Bool
  for +back: T.Lex
  for +qkind: T.QKind
  for +uni: U32
  for +left: U32
  for +rest: String
  for es: {k3.noarr1(stack) == True{} : Bool}
  for eo: {String.is_empty(T.bad(k3.key.doc(at, g0, ds, last, g, rows, heads, here, stack, arrtab, back, qkind, uni,
    left, rest))) == True{} : Bool}
  {k3.has(T.root(k3.key.doc(at, g0, ds, last, g, rows, heads, here, stack, arrtab, back, qkind, uni, left, rest)),
    k3.key.table(stack, here, ds), D3.k3.seg.name(last)) == True{} : Bool}

# a header's text and the rest of a document read from the start of a line
def k3.hd.doc(
  arr: Bool,
  g0: List<&2, Bool>,
  ds: List<&2, KDot>,
  last: D3.KSeg,
  g9: List<&2, Bool>,
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  arrtab: Bool,
  back: T.Lex,
  qkind: T.QKind,
  uni: U32,
  left: U32,
  rest: String
) -> T.Doc:
  T.doc.read(k3.hd.text(arr, g0, ds, last, g9, rest), T.MScan{k3.at(AtLine{}, rows, heads, here, [], arrtab, back,
    qkind, uni, left)})

# LAW: a header's table is put under its characters: from the start of a
# line in any table, with no array or inline table open, a `[table]` or
# `[[array]]` header of segments spelled any way toml.abnf allows, then any
# text, leave a document that has an error or whose root holds, in the table
# the other segments name, a pair named by the last segment's characters
law header_found_anywhere:
  for +arr: Bool
  for +g0: List<&2, Bool>
  for +ds: List<&2, KDot>
  for +last: D3.KSeg
  for ok: {k3.dk.ok(ds, last) == True{} : Bool}
  for +g9: List<&2, Bool>
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +here: List<&2, String>
  for +arrtab: Bool
  for +back: T.Lex
  for +qkind: T.QKind
  for +uni: U32
  for +left: U32
  for +rest: String
  for eo: {String.is_empty(T.bad(k3.hd.doc(arr, g0, ds, last, g9, rows, heads, here, arrtab, back, qkind, uni, left,
    rest))) == True{} : Bool}
  {k3.has(T.root(k3.hd.doc(arr, g0, ds, last, g9, rows, heads, here, arrtab, back, qkind, uni, left, rest)),
    k3.dk.init(ds), D3.k3.seg.name(last)) == True{} : Bool}

# a hit is a table or an inline table
def k3.istab(hh: T.Hit) -> Bool:
  match hh:
    case T.Found{T.VHead{_q, _r}}:
      True{}
    case T.Found{T.VInl{_r}}:
      True{}
    case _h:
      False{}

# the hit and every name after it on a path are tables or inline tables
def k3.tabh(pp: List<&2, String>, +hh: T.Hit) -> Bool:
  match pp:
    case []:
      k3.istab(hh)
    case +nn <> rest:
      Bool.and(k3.istab(hh), k3.tabh(rest, T.get(T.at.rows_of(hh), nn)))

# every name on a path, from these rows, is a table or an inline table's:
# no array lies on the path, so at can follow it
def k3.tabs(+rows: List<&2, T.Val>, path: List<&2, String>) -> Bool:
  match path:
    case []:
      True{}
    case +nn <> pp:
      k3.tabh(pp, T.get(rows, nn))

# LAW: and at finds it from the root by the names on its path when no array
# lies on that path: in the document key_found_anywhere reads, with no
# error, when every name of the key's table path is a table or an inline
# table, at finds the key by the path's names and the key's
law key_found_by_at:
  for +at: KPos
  for +g0: List<&2, Bool>
  for +ds: List<&2, KDot>
  for +last: D3.KSeg
  for ok: {k3.dk.ok(ds, last) == True{} : Bool}
  for +g: List<&2, Bool>
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +here: List<&2, String>
  for +stack: List<&2, T.Ctx>
  for +arrtab: Bool
  for +back: T.Lex
  for +qkind: T.QKind
  for +uni: U32
  for +left: U32
  for +rest: String
  for es: {k3.noarr1(stack) == True{} : Bool}
  for eo: {String.is_empty(T.bad(k3.key.doc(at, g0, ds, last, g, rows, heads, here, stack, arrtab, back, qkind, uni,
    left, rest))) == True{} : Bool}
  for et: {k3.tabs(T.root(k3.key.doc(at, g0, ds, last, g, rows, heads, here, stack, arrtab, back, qkind, uni, left,
    rest)), k3.key.table(stack, here, ds)) == True{} : Bool}
  {k3.found(T.at(T.root(k3.key.doc(at, g0, ds, last, g, rows, heads, here, stack, arrtab, back, qkind, uni, left,
    rest)), List.append(&2, String, k3.key.table(stack, here, ds), [D3.k3.seg.name(last)]))) == True{} : Bool}

# LAW: and a header's table the same way: in the document
# header_found_anywhere reads, with no error, when every name before the
# last is a table or an inline table, at finds the header's table by its
# names
law header_found_by_at:
  for +arr: Bool
  for +g0: List<&2, Bool>
  for +ds: List<&2, KDot>
  for +last: D3.KSeg
  for ok: {k3.dk.ok(ds, last) == True{} : Bool}
  for +g9: List<&2, Bool>
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +here: List<&2, String>
  for +arrtab: Bool
  for +back: T.Lex
  for +qkind: T.QKind
  for +uni: U32
  for +left: U32
  for +rest: String
  for eo: {String.is_empty(T.bad(k3.hd.doc(arr, g0, ds, last, g9, rows, heads, here, arrtab, back, qkind, uni, left,
    rest))) == True{} : Bool}
  for et: {k3.tabs(T.root(k3.hd.doc(arr, g0, ds, last, g9, rows, heads, here, arrtab, back, qkind, uni, left, rest)),
    k3.dk.init(ds)) == True{} : Bool}
  {k3.found(T.at(T.root(k3.hd.doc(arr, g0, ds, last, g9, rows, heads, here, arrtab, back, qkind, uni, left, rest)),
    List.append(&2, String, k3.dk.init(ds), [D3.k3.seg.name(last)]))) == True{} : Bool}

# LAW: in a parsed document: when parse reads a text's first part, pre, to
# where a key may start, with no array open, and a key's text and the rest
# follow, the document parse returns, with no error, holds the pair under
# the key's characters in its table
law key_found_in_document:
  for +pre: String
  for +at: KPos
  for +g0: List<&2, Bool>
  for +ds: List<&2, KDot>
  for +last: D3.KSeg
  for ok: {k3.dk.ok(ds, last) == True{} : Bool}
  for +g: List<&2, Bool>
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +here: List<&2, String>
  for +stack: List<&2, T.Ctx>
  for +arrtab: Bool
  for +back: T.Lex
  for +qkind: T.QKind
  for +uni: U32
  for +left: U32
  for +rest: String
  for es: {k3.noarr1(stack) == True{} : Bool}
  for +ep: {T.parse(String.append(pre, String.append(D2.gap(g0), k3.dk.text(ds, last, String.append(D2.gap(g), SCon{'=',
    rest}))))) == k3.key.doc(at, g0, ds, last, g, rows, heads, here, stack, arrtab, back, qkind, uni, left, rest)
    : T.Doc}
  for eo: {String.is_empty(T.bad(T.parse(String.append(pre, String.append(D2.gap(g0), k3.dk.text(ds, last,
    String.append(D2.gap(g), SCon{'=', rest}))))))) == True{} : Bool}
  {k3.has(T.root(T.parse(String.append(pre, String.append(D2.gap(g0), k3.dk.text(ds, last, String.append(D2.gap(g),
    SCon{'=', rest})))))), k3.key.table(stack, here, ds), D3.k3.seg.name(last)) == True{} : Bool}
