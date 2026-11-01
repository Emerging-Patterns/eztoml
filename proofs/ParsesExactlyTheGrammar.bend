# proofs of laws/ParsesExactlyTheGrammar.bend
import Base
import ../main.bend as T
import ../src/eq.bend as Eq
import ../laws/ParsesExactlyTheGrammar.bend as Laws
import ../laws/defs/BareValueGrammar.bend as D1
import ../laws/defs/PairPresence.bend as D2
import ./lemmas/FailedScanStays.bend as M1
import ./lemmas/PickAndDigitSteps.bend as M2
import ./lemmas/ReorderedTableNames.bend as M3
import ./lemmas/StringEqualsItself.bend as M4

# a comment character that is a control, no newline and no tab fails the step
def com.go(
  nl: Bool,
  ctl: Bool,
  tab: Bool,
  st: T.St,
  cc: Char,
  enl: {T.ch.nl(cc) == nl : Bool},
  ectl: {T.ch.ctl(cc) == ctl : Bool},
  etab: {U32.is_eq(Char.to_u32(cc), 9) == tab : Bool},
  no_nl: {T.ch.nl(cc) == False{} : Bool},
  is_ctl: {T.ch.ctl(cc) == True{} : Bool},
  no_tab: {U32.is_eq(Char.to_u32(cc), 9) == False{} : Bool}
) -> {T.lex.com.go(nl, ctl, tab, st, cc) == T.st.err(st, "invalid control in comment")
  : T.St}:
  match nl:
    case True{}:
      M4.clash(&2, {T.lex.com.go(True{}, ctl, tab, st, cc)
        == T.st.err(st, "invalid control in comment") : T.St},
        Equal.trans(Bool, False{}, T.ch.nl(cc), True{},
          Equal.sym(Bool, T.ch.nl(cc), False{}, no_nl), enl))
    case False{}:
      match ctl:
        case False{}:
          M4.clash(&2, {T.lex.com.go(False{}, False{}, tab, st, cc)
            == T.st.err(st, "invalid control in comment") : T.St},
            Equal.trans(Bool, False{}, T.ch.ctl(cc), True{},
              Equal.sym(Bool, T.ch.ctl(cc), False{}, ectl), is_ctl))
        case True{}:
          match tab:
            case True{}:
              M4.clash(&2, {T.lex.com.go(False{}, True{}, True{}, st, cc)
                == T.st.err(st, "invalid control in comment") : T.St},
                Equal.trans(Bool, False{}, U32.is_eq(Char.to_u32(cc), 9), True{},
                  Equal.sym(Bool, U32.is_eq(Char.to_u32(cc), 9), False{}, no_tab), etab))
            case False{}:
              {==}

# the fast path sends a control in a comment to the full step, which fails it
def com.fast(
  ctl: Bool,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +buf: List<&2, Char>,
  +back: T.Lex,
  +qkind: T.QKind,
  +stack: List<&2, T.Ctx>,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +xx: U32,
  ectl: {T.ch.ctl(Chr{xx}) == ctl : Bool},
  no_nl: {T.ch.nl(Chr{xx}) == False{} : Bool},
  is_ctl: {T.ch.ctl(Chr{xx}) == True{} : Bool},
  no_tab: {U32.is_eq(xx, 9) == False{} : Bool}
) -> {T.read.fast.com(ctl, bad, rows, heads, here, parts, buf, back, qkind, stack, uni,
  left, arrtab, Chr{xx}) == T.st.err(T.St{bad, rows, heads, here, parts, buf, T.LCom{},
  back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}}, "invalid control in comment")
  : T.St}:
  match ctl:
    case False{}:
      M4.clash(&2, {T.read.fast.com(False{}, bad, rows, heads, here, parts, buf, back, qkind,
        stack, uni, left, arrtab, Chr{xx}) == T.st.err(T.St{bad, rows, heads, here, parts,
        buf, T.LCom{}, back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}},
        "invalid control in comment") : T.St},
        Equal.trans(Bool, False{}, T.ch.ctl(Chr{xx}), True{},
          Equal.sym(Bool, T.ch.ctl(Chr{xx}), False{}, ectl), is_ctl))
    case True{}:
      Equal.cong(T.St, T.St, s => T.read.once2(s),
        T.lex.com.go(T.ch.nl(Chr{xx}), T.ch.ctl(Chr{xx}), U32.is_eq(xx, 9),
          T.St{bad, rows, heads, here, parts, buf, T.LCom{}, back, qkind, stack, T.HNone{},
            uni, left, arrtab, False{}}, Chr{xx}),
        T.st.err(T.St{bad, rows, heads, here, parts, buf, T.LCom{}, back, qkind, stack,
          T.HNone{}, uni, left, arrtab, False{}}, "invalid control in comment"),
        com.go(T.ch.nl(Chr{xx}), T.ch.ctl(Chr{xx}), U32.is_eq(xx, 9),
          T.St{bad, rows, heads, here, parts, buf, T.LCom{}, back, qkind, stack, T.HNone{},
            uni, left, arrtab, False{}}, Chr{xx}, {==}, {==}, {==}, no_nl, is_ctl, no_tab))

# one comment character: the scan step and then the fast step, each past the
# branches the character cannot take
def com.step(
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +buf: List<&2, Char>,
  +back: T.Lex,
  +qkind: T.QKind,
  +stack: List<&2, T.Ctx>,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +xx: U32,
  +ee: {Laws.com.ctl(Chr{xx}) == True{} : Bool}
) -> {T.doc.scan(T.St{bad, rows, heads, here, parts, buf, T.LCom{}, back, qkind, stack,
  T.HNone{}, uni, left, arrtab, False{}}, Chr{xx}) == T.MScan{T.st.err(T.St{bad, rows,
  heads, here, parts, buf, T.LCom{}, back, qkind, stack, T.HNone{}, uni, left, arrtab,
  False{}}, "invalid control in comment")} : T.Mode}:
  +nots = {Eq.and.right(T.ch.ctl(Chr{xx}), Bool.not(Bool.or(T.ch.nl(Chr{xx}),
    U32.is_eq(xx, 9))), ee) : {Bool.not(Bool.or(T.ch.nl(Chr{xx}), U32.is_eq(xx, 9)))
    == True{} : Bool}}
  +ors = {Eq.not.true(Bool.or(T.ch.nl(Chr{xx}), U32.is_eq(xx, 9)), nots)
    : {Bool.or(T.ch.nl(Chr{xx}), U32.is_eq(xx, 9)) == False{} : Bool}}
  Equal.trans(T.Mode,
    T.doc.scan(T.St{bad, rows, heads, here, parts, buf, T.LCom{}, back, qkind, stack,
      T.HNone{}, uni, left, arrtab, False{}}, Chr{xx}),
    T.MScan{T.read.fast(T.St{bad, rows, heads, here, parts, buf, T.LCom{}, back, qkind,
      stack, T.HNone{}, uni, left, arrtab, False{}}, Chr{xx})},
    T.MScan{T.st.err(T.St{bad, rows, heads, here, parts, buf, T.LCom{}, back, qkind, stack,
      T.HNone{}, uni, left, arrtab, False{}}, "invalid control in comment")},
    M3.scan.other(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), U32.is_eq(xx, 13),
      T.St{bad, rows, heads, here, parts, buf, T.LCom{}, back, qkind, stack, T.HNone{},
        uni, left, arrtab, False{}}, Chr{xx}, {==}, {==}, {==}, ch => Laws.com.ctl(ch), ee, {==},
      {==}, {==}),
    Equal.cong(T.St, T.Mode, s => T.MScan{s},
      T.read.fast(T.St{bad, rows, heads, here, parts, buf, T.LCom{}, back, qkind, stack,
        T.HNone{}, uni, left, arrtab, False{}}, Chr{xx}),
      T.st.err(T.St{bad, rows, heads, here, parts, buf, T.LCom{}, back, qkind, stack,
        T.HNone{}, uni, left, arrtab, False{}}, "invalid control in comment"),
      com.fast(T.ch.ctl(Chr{xx}), bad, rows, heads, here, parts, buf, back, qkind, stack,
        uni, left, arrtab, xx, {==}, Eq.or.left_false(T.ch.nl(Chr{xx}), U32.is_eq(xx, 9),
        ors), Eq.and.left(T.ch.ctl(Chr{xx}), Bool.not(Bool.or(T.ch.nl(Chr{xx}),
        U32.is_eq(xx, 9))), ee), Eq.or.right_false(T.ch.nl(Chr{xx}), U32.is_eq(xx, 9),
        ors))))

def Laws.comment_control_refused(
  bad,
  rows,
  heads,
  here,
  parts,
  buf,
  back,
  qkind,
  stack,
  uni,
  left,
  arrtab,
  c,
  e,
  t
):
  match c:
    case Chr{+xx}:
      Equal.trans(Bool,
        String.is_empty(T.bad(T.doc.read(t, T.doc.scan(T.St{bad, rows, heads, here, parts,
          buf, T.LCom{}, back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}},
          Chr{xx})))),
        String.is_empty(T.bad(T.doc.read(t, T.MScan{T.st.err(T.St{bad, rows, heads, here,
          parts, buf, T.LCom{}, back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}},
          "invalid control in comment")}))),
        False{},
        Equal.cong(T.Mode, Bool, m => String.is_empty(T.bad(T.doc.read(t, m))),
          T.doc.scan(T.St{bad, rows, heads, here, parts, buf, T.LCom{}, back, qkind, stack,
            T.HNone{}, uni, left, arrtab, False{}}, Chr{xx}),
          T.MScan{T.st.err(T.St{bad, rows, heads, here, parts, buf, T.LCom{}, back, qkind,
            stack, T.HNone{}, uni, left, arrtab, False{}}, "invalid control in comment")},
          com.step(bad, rows, heads, here, parts, buf, back, qkind, stack, uni, left, arrtab,
            xx, e)),
        M1.err.sinks(T.St{bad, rows, heads, here, parts, buf, T.LCom{}, back, qkind, stack,
          T.HNone{}, uni, left, arrtab, False{}}, 'i', "nvalid control in comment", t))

def Laws.lone_cr_refused(st, c, e, t):
  Equal.trans(Bool,
    String.is_empty(T.bad(T.doc.read(t, T.doc.cr(Char.is_eq(c, '\n'),
      T.read.fast(st, '\r'), c)))),
    String.is_empty(T.bad(T.doc.read(t, T.doc.cr(False{}, T.read.fast(st, '\r'), c)))),
    False{},
    Equal.cong(Bool, Bool,
      bb => String.is_empty(T.bad(T.doc.read(t, T.doc.cr(bb, T.read.fast(st, '\r'), c)))),
      Char.is_eq(c, '\n'), False{}, e),
    M1.err.sinks(T.read.fast(st, '\r'), 'c', "arriage return without line feed", t))

def Laws.last_cr_refused(st):
  M1.err.sinks(T.read.fast(st, '\r'), 'c', "arriage return without line feed", "")

# a line feed where the value should start fails the step, inside an inline
# table or not
def val.nl(
  stack: List<&2, T.Ctx>,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +buf: List<&2, Char>,
  +back: T.Lex,
  +qkind: T.QKind,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +tt: String
) -> {String.is_empty(T.bad(T.doc.read(tt, T.MScan{T.read.fast(T.St{bad, rows, heads,
  here, parts, buf, T.LVal{}, back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}},
  '\n')}))) == False{} : Bool}:
  match stack:
    case []:
      M1.err.sinks(T.St{bad, rows, heads, here, parts, buf, T.LVal{}, back, qkind, [],
        T.HNone{}, uni, left, arrtab, False{}}, 'n', "ewline before value", tt)
    case T.CArr{items, ps, hs} <> rest:
      M1.err.sinks(T.St{bad, rows, heads, here, parts, buf, T.LVal{}, back, qkind,
        T.CArr{items, ps, hs} <> rest, T.HNone{}, uni, left, arrtab, False{}}, 'n',
        "ewline before value", tt)
    case T.CInl{items, ps, hs} <> rest:
      M1.err.sinks(T.St{bad, rows, heads, here, parts, buf, T.LVal{}, back, qkind,
        T.CInl{items, ps, hs} <> rest, T.HNone{}, uni, left, arrtab, False{}}, 'n',
        "ewline in inline table", tt)

def Laws.value_on_key_line(
  bad,
  rows,
  heads,
  here,
  parts,
  buf,
  back,
  qkind,
  stack,
  uni,
  left,
  arrtab,
  t
):
  val.nl(stack, bad, rows, heads, here, parts, buf, back, qkind, uni, left, arrtab, t)

# the carriage return fails the step, and the line feed after it changes nothing
def val.crlf(
  stack: List<&2, T.Ctx>,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +buf: List<&2, Char>,
  +back: T.Lex,
  +qkind: T.QKind,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +tt: String
) -> {String.is_empty(T.bad(T.doc.read(tt, T.MScan{T.read.fast(T.read.fast(T.St{bad, rows,
  heads, here, parts, buf, T.LVal{}, back, qkind, stack, T.HNone{}, uni, left, arrtab,
  False{}}, '\r'), '\n')}))) == False{} : Bool}:
  match stack:
    case []:
      M1.err.sinks(T.St{bad, rows, heads, here, parts, buf, T.LVal{}, back, qkind, [],
        T.HNone{}, uni, left, arrtab, False{}}, 'n', "ewline before value", tt)
    case T.CArr{items, ps, hs} <> rest:
      M1.err.sinks(T.St{bad, rows, heads, here, parts, buf, T.LVal{}, back, qkind,
        T.CArr{items, ps, hs} <> rest, T.HNone{}, uni, left, arrtab, False{}}, 'n',
        "ewline before value", tt)
    case T.CInl{items, ps, hs} <> rest:
      M1.err.sinks(T.St{bad, rows, heads, here, parts, buf, T.LVal{}, back, qkind,
        T.CInl{items, ps, hs} <> rest, T.HNone{}, uni, left, arrtab, False{}}, 'n',
        "ewline in inline table", tt)

def Laws.value_on_key_line_crlf(
  bad,
  rows,
  heads,
  here,
  parts,
  buf,
  back,
  qkind,
  stack,
  uni,
  left,
  arrtab,
  t
):
  val.crlf(stack, bad, rows, heads, here, parts, buf, back, qkind, uni, left, arrtab, t)

# laws/ParsesExactlyTheGrammar.bend and laws/DefinesEachTableOnce.bend for inline tables.

# a pair whose name is not k is passed over by rows.look
def look.skip(
  +nn: String,
  -vv: T.Val,
  -rest: List<&2, T.Val>,
  +kk: String,
  ee: {String.eq(nn, kk) == False{} : Bool}
) -> {T.rows.look(T.VPair{nn, vv} <> rest, kk) == T.rows.look(rest, kk) : T.Look}:
  Equal.cong(Bool, T.Look, bb => T.look.step(bb, vv, _u => T.rows.look(rest, kk)),
    T.str.eq(nn, kk), False{},
    Equal.trans(Bool, T.str.eq(nn, kk), String.eq(nn, kk), False{},
      M2.str.eq.agree(nn, kk), ee))

# rows.look misses when no pair in the rows is named k
def look.misses(
  rows: List<&2, T.Val>,
  +kk: String,
  +ee: {D2.has_pair(rows, kk) == False{} : Bool}
) -> {T.rows.look(rows, kk) == T.KMiss{} : T.Look}:
  match rows:
    case []:
      {==}
    case T.VPair{+nn, +vv} <> +tt:
      Equal.trans(T.Look, T.rows.look(T.VPair{nn, vv} <> tt, kk), T.rows.look(tt, kk),
        T.KMiss{},
        look.skip(nn, vv, tt, kk,
          Eq.or.false_left(String.eq(nn, kk), D2.has_pair(tt, kk), ee)),
        look.misses(tt, kk,
          Eq.or.false_right(String.eq(nn, kk), D2.has_pair(tt, kk), ee)))
    case T.VStr{_a} <> tt:
      look.misses(tt, kk, ee)
    case T.VSpan{_a, _b} <> tt:
      look.misses(tt, kk, ee)
    case T.VInt{_a, _b} <> tt:
      look.misses(tt, kk, ee)
    case T.VFlo{_a, _b} <> tt:
      look.misses(tt, kk, ee)
    case T.VBool{_a} <> tt:
      look.misses(tt, kk, ee)
    case T.VWhen{_a} <> tt:
      look.misses(tt, kk, ee)
    case T.VArr{_a} <> tt:
      look.misses(tt, kk, ee)
    case T.VInl{_a} <> tt:
      look.misses(tt, kk, ee)
    case T.VHead{_a, _b} <> tt:
      look.misses(tt, kk, ee)
    case T.VAot{_a, _b} <> tt:
      look.misses(tt, kk, ee)
    case T.VAots{_a, _b} <> tt:
      look.misses(tt, kk, ee)

# the first key of an inline table makes a table there, and the key is in it
def inl.first(
  inl: List<&2, T.Val>,
  +bb: String,
  cc: String,
  vv: T.Val,
  ee: {D2.has_pair(inl, bb) == False{} : Bool}
) -> {Laws.end_rows(T.tree.walk([bb, cc], T.Tw{inl, T.JPut{vv}, [], "", "", [], True{}},
  0)) == T.VPair{bb, T.VHead{T.tree.pre("", bb), [T.VPair{cc, vv}]}} <> inl
  : List<&2, T.Val>}:
  Equal.cong(T.Look, List<&2, T.Val>,
    hh => Laws.end_rows(T.tree.leaf(cc, T.tree.sub.look(hh, bb, inl, T.JPut{vv}, [], "",
      [], True{}, True{}))),
    T.rows.look(inl, bb), T.KMiss{}, look.misses(inl, bb, ee))

# the second key goes on in that table: bb finds it, and dd is not cc
def inl.second(
  inl: List<&2, T.Val>,
  +bb: String,
  +cc: String,
  +dd: String,
  vv: T.Val,
  ww: T.Val,
  ff: {String.eq(cc, dd) == False{} : Bool}
) -> {D1.end_bad(T.tree.walk([bb, dd], T.Tw{T.VPair{bb, T.VHead{T.tree.pre("", bb),
  [T.VPair{cc, vv}]}} <> inl, T.JPut{ww}, [], "", "", [], True{}}, 0)) == "" : String}:
  Equal.trans(String,
    D1.end_bad(T.tree.leaf(dd, T.tree.sub.look(T.look.step(T.str.eq(bb, bb),
      T.VHead{T.tree.pre("", bb), [T.VPair{cc, vv}]}, _u => T.rows.look(inl, bb)), bb,
      T.VPair{bb, T.VHead{T.tree.pre("", bb), [T.VPair{cc, vv}]}} <> inl, T.JPut{ww},
      [], "", [], True{}, True{}))),
    D1.end_bad(T.tree.leaf(dd, T.tree.sub.look(T.KHead{T.tree.pre("", bb),
      [T.VPair{cc, vv}]}, bb,
      T.VPair{bb, T.VHead{T.tree.pre("", bb), [T.VPair{cc, vv}]}} <> inl, T.JPut{ww},
      [], "", [], True{}, True{}))),
    "",
    Equal.cong(Bool, String,
      xx => D1.end_bad(T.tree.leaf(dd, T.tree.sub.look(T.look.step(xx,
        T.VHead{T.tree.pre("", bb), [T.VPair{cc, vv}]}, _u => T.rows.look(inl, bb)), bb,
        T.VPair{bb, T.VHead{T.tree.pre("", bb), [T.VPair{cc, vv}]}} <> inl, T.JPut{ww},
        [], "", [], True{}, True{}))),
      T.str.eq(bb, bb), True{}, M4.str.eq.self(bb)),
    Equal.cong(Bool, String,
      xx => D1.end_bad(T.tree.leaf.put(T.find.step(xx, vv, _u => T.rows.find([], dd)),
        dd, [T.VPair{cc, vv}], ww,
        [T.FrRep{bb, T.VPair{bb, T.VHead{T.tree.pre("", bb), [T.VPair{cc, vv}]}} <> inl,
          T.tree.pre("", bb)}],
        "", T.heads.define(T.JPut{ww}, T.tree.pre("", bb), []))),
      T.str.eq(cc, dd), False{},
      Equal.trans(Bool, T.str.eq(cc, dd), String.eq(cc, dd), False{},
        M2.str.eq.agree(cc, dd), ff)))

def Laws.inline_dotted_keys_share_a_prefix(inl, b, c, d, v, w, e, f):
  Equal.trans(String,
    D1.end_bad(T.tree.walk([b, d], T.Tw{Laws.end_rows(T.tree.walk([b, c],
      T.Tw{inl, T.JPut{v}, [], "", "", [], True{}}, 0)), T.JPut{w}, [], "", "", [],
      True{}}, 0)),
    D1.end_bad(T.tree.walk([b, d], T.Tw{T.VPair{b, T.VHead{T.tree.pre("", b),
      [T.VPair{c, v}]}} <> inl, T.JPut{w}, [], "", "", [], True{}}, 0)),
    "",
    Equal.cong(List<&2, T.Val>, String,
      rr => D1.end_bad(T.tree.walk([b, d], T.Tw{rr, T.JPut{w}, [], "", "", [], True{}},
        0)),
      Laws.end_rows(T.tree.walk([b, c], T.Tw{inl, T.JPut{v}, [], "", "", [], True{}}, 0)),
      T.VPair{b, T.VHead{T.tree.pre("", b), [T.VPair{c, v}]}} <> inl,
      inl.first(inl, b, c, v, e)),
    inl.second(inl, b, c, d, v, w, f))

def Laws.header_blank_then_bracket_refused(
  bad,
  rows,
  heads,
  here,
  parts,
  back,
  qkind,
  stack,
  uni,
  left,
  arrtab,
  tab,
  t
):
  match tab:
    case True{}:
      M1.err.sinks(T.St{bad, rows, heads, here, parts, [], T.LHeadDot{}, back, qkind, stack,
        T.HNone{}, uni, left, arrtab, False{}}, 'i', "nvalid header", t)
    case False{}:
      M1.err.sinks(T.St{bad, rows, heads, here, parts, [], T.LHeadDot{}, back, qkind, stack,
        T.HNone{}, uni, left, arrtab, False{}}, 'i', "nvalid header", t)

def Laws.header_blank_waits_for_segment(
  _bad,
  _rows,
  _heads,
  _here,
  _parts,
  _back,
  _qkind,
  _stack,
  _uni,
  _left,
  _arrtab,
  tab
):
  match tab:
    case True{}:
      {==}
    case False{}:
      {==}
