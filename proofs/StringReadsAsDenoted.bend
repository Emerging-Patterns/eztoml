# proofs of laws/StringReadsAsDenoted.bend
import Base
import ../main.bend as T
import ../src/eq.bend as Eq
import ../laws/StringReadsAsDenoted.bend as Laws
import ../laws/defs/AbnfGrammar.bend as D1
import ../laws/defs/BareValueGrammar.bend as D2
import ../laws/defs/GrammarDerivations.bend as D3
import ./lemmas/BareKeyValueScan.bend as M1
import ./lemmas/FreshNamesInRows.bend as M2
import ./lemmas/HeldCharacterSteps.bend as M3
import ./lemmas/ReorderedTableNames.bend as M4
import ./lemmas/StringBodyWalk.bend as M5
import ./lemmas/StringEqualsItself.bend as M6
import ./lemmas/ValueTextReadback.bend as M7

# a scanner inside a multi-line string, its body so far reversed in buf
def ms(
  lit: Bool,
  buf: List<&2, Char>,
  back: T.Lex,
  bad: String,
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  parts: List<&2, String>,
  stack: List<&2, T.Ctx>,
  uni: U32,
  left: U32,
  arrtab: Bool
) -> T.St:
  T.St{bad, rows, heads, here, parts, buf, T.LStr{}, back, M1.mk(lit), stack, T.HNone{}, uni,
    left, arrtab, False{}}

# a raw character that is no control is pushed
def ml.ctl(
  ctrl: Bool,
  st: T.St,
  +xx: U32,
  ectl: {Bool.or(U32.is_lt(xx, 32), U32.is_eq(xx, 127)) == ctrl : Bool},
  noctl: {Bool.or(U32.is_lt(xx, 32), U32.is_eq(xx, 127)) == False{} : Bool}
) -> {T.lex.str.char.go(T.str.bad.go(ctrl, U32.is_eq(xx, 9), Bool.or(U32.is_eq(xx, 10),
  U32.is_eq(xx, 13)), True{}), st, Chr{xx}) == T.st.push(st, Chr{xx}, T.LStr{}) : T.St}:
  match ctrl:
    case True{}:
      M6.clash(&2, {T.lex.str.char.go(T.str.bad.go(True{}, U32.is_eq(xx, 9),
        Bool.or(U32.is_eq(xx, 10), U32.is_eq(xx, 13)), True{}), st, Chr{xx})
        == T.st.push(st, Chr{xx}, T.LStr{}) : T.St},
        Equal.trans(Bool, False{}, Bool.or(U32.is_lt(xx, 32), U32.is_eq(xx, 127)), True{},
          Equal.sym(Bool, Bool.or(U32.is_lt(xx, 32), U32.is_eq(xx, 127)), False{}, noctl),
          ectl))
    case False{}:
      {==}

# no backslash in a basic string: the character is raw
def ml.bbs(
  bs: Bool,
  st: T.St,
  +xx: U32,
  ebs: {Char.is_eq(Chr{xx}, '\\') == bs : Bool},
  pp: Char -> Bool,
  yes: {pp(Chr{xx}) == True{} : Bool},
  nb: {pp('\\') == False{} : Bool},
  noctl: {Bool.or(U32.is_lt(xx, 32), U32.is_eq(xx, 127)) == False{} : Bool}
) -> {T.lex.str.bs(bs, True{}, st, Chr{xx}, T.QMulti{}) == T.st.push(st, Chr{xx}, T.LStr{})
  : T.St}:
  match bs:
    case True{}:
      Eq.bit.gone(&2, {T.lex.str.bs(True{}, True{}, st, Chr{xx}, T.QMulti{})
        == T.st.push(st, Chr{xx}, T.LStr{}) : T.St},
        Eq.refute_char(Chr{xx}, '\\', pp, ebs, yes, nb))
    case False{}:
      ml.ctl(Bool.or(U32.is_lt(xx, 32), U32.is_eq(xx, 127)), st, xx, {==}, noctl)

# no quote in a multi-line basic string: the character is not the closer
def ml.bq(
  quote: Bool,
  st: T.St,
  +xx: U32,
  eq: {Char.is_eq(Chr{xx}, '"') == quote : Bool},
  pp: Char -> Bool,
  +yes: {pp(Chr{xx}) == True{} : Bool},
  nq: {pp('"') == False{} : Bool},
  nb: {pp('\\') == False{} : Bool},
  noctl: {Bool.or(U32.is_lt(xx, 32), U32.is_eq(xx, 127)) == False{} : Bool}
) -> {T.lex.str.go(quote, True{}, True{}, st, Chr{xx}, T.QMulti{})
  == T.st.push(st, Chr{xx}, T.LStr{}) : T.St}:
  match quote:
    case True{}:
      Eq.bit.gone(&2, {T.lex.str.go(True{}, True{}, True{}, st, Chr{xx}, T.QMulti{})
        == T.st.push(st, Chr{xx}, T.LStr{}) : T.St},
        Eq.refute_char(Chr{xx}, '"', pp, eq, yes, nq))
    case False{}:
      ml.bbs(Char.is_eq(Chr{xx}, '\\'), st, xx, {==}, pp, yes, nb, noctl)

# no apostrophe in a multi-line literal string: the character is not the closer
def ml.lq(
  quote: Bool,
  st: T.St,
  +xx: U32,
  eq: {Char.is_eq(Chr{xx}, '\'') == quote : Bool},
  pp: Char -> Bool,
  yes: {pp(Chr{xx}) == True{} : Bool},
  nq: {pp('\'') == False{} : Bool},
  noctl: {Bool.or(U32.is_lt(xx, 32), U32.is_eq(xx, 127)) == False{} : Bool}
) -> {T.lex.str.go(quote, True{}, False{}, st, Chr{xx}, T.QMultiLit{})
  == T.st.push(st, Chr{xx}, T.LStr{}) : T.St}:
  match quote:
    case True{}:
      Eq.bit.gone(&2, {T.lex.str.go(True{}, True{}, False{}, st, Chr{xx}, T.QMultiLit{})
        == T.st.push(st, Chr{xx}, T.LStr{}) : T.St},
        Eq.refute_char(Chr{xx}, '\'', pp, eq, yes, nq))
    case False{}:
      ml.ctl(Bool.or(U32.is_lt(xx, 32), U32.is_eq(xx, 127)), st, xx, {==}, noctl)

# the controls a plain character is not
def ml.noctl(
  +xx: U32,
  ee: {Laws.ml.plain(Chr{xx}) == True{} : Bool}
) -> {Bool.or(U32.is_lt(xx, 32), U32.is_eq(xx, 127)) == False{} : Bool}:
  Eq.not.true(Bool.or(U32.is_lt(xx, 32), U32.is_eq(xx, 127)),
    Eq.and.left(Bool.not(Bool.or(U32.is_lt(xx, 32), U32.is_eq(xx, 127))),
      Bool.not(Bool.or(Char.is_eq(Chr{xx}, '"'), Bool.or(Char.is_eq(Chr{xx}, '\''),
        Char.is_eq(Chr{xx}, '\\')))), ee))

# a plain character inside a multi-line string of either kind is pushed
def ml.char(
  lit: Bool,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +buf: List<&2, Char>,
  +lx: T.Lex,
  +back: T.Lex,
  +stack: List<&2, T.Ctx>,
  +hold: T.Hold,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +lead: Bool,
  +xx: U32,
  +ee: {Laws.ml.plain(Chr{xx}) == True{} : Bool}
) -> {T.lex.str(T.St{bad, rows, heads, here, parts, buf, lx, back, M1.mk(lit), stack, hold,
  uni, left, arrtab, lead}, Chr{xx}) == T.st.push(T.St{bad, rows, heads, here, parts, buf,
  lx, back, M1.mk(lit), stack, hold, uni, left, arrtab, lead}, Chr{xx}, T.LStr{}) : T.St}:
  match lit:
    case False{}:
      ml.bq(Char.is_eq(Chr{xx}, '"'), T.St{bad, rows, heads, here, parts, buf, lx, back,
        T.QMulti{}, stack, hold, uni, left, arrtab, lead}, xx, {==},
        ch => Laws.ml.plain(ch), ee, {==}, {==}, ml.noctl(xx, ee))
    case True{}:
      ml.lq(Char.is_eq(Chr{xx}, '\''), T.St{bad, rows, heads, here, parts, buf, lx, back,
        T.QMultiLit{}, stack, hold, uni, left, arrtab, lead}, xx, {==},
        ch => Laws.ml.plain(ch), ee, {==}, ml.noctl(xx, ee))

# the fast path sends a multi-line string's character to the full step
def ml.fast(
  lit: Bool,
  +buf: List<&2, Char>,
  +back: T.Lex,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +stack: List<&2, T.Ctx>,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +xx: U32,
  +ee: {Laws.ml.plain(Chr{xx}) == True{} : Bool}
) -> {T.read.fast(ms(lit, buf, back, bad, rows, heads, here, parts, stack, uni, left,
  arrtab), Chr{xx}) == ms(lit, Chr{xx} <> buf, back, bad, rows, heads, here, parts, stack,
  uni, left, arrtab) : T.St}:
  match lit:
    case False{}:
      Equal.cong(T.St, T.St, s => T.read.once2(s),
        T.lex.str(T.St{bad, rows, heads, here, parts, buf, T.LStr{}, back, M1.mk(False{}),
          stack, T.HNone{}, uni, left, arrtab, False{}}, Chr{xx}),
        T.st.push(T.St{bad, rows, heads, here, parts, buf, T.LStr{}, back, M1.mk(False{}),
          stack, T.HNone{}, uni, left, arrtab, False{}}, Chr{xx}, T.LStr{}),
        ml.char(False{}, bad, rows, heads, here, parts, buf, T.LStr{}, back, stack,
          T.HNone{}, uni, left, arrtab, False{}, xx, ee))
    case True{}:
      Equal.cong(T.St, T.St, s => T.read.once2(s),
        T.lex.str(T.St{bad, rows, heads, here, parts, buf, T.LStr{}, back, M1.mk(True{}),
          stack, T.HNone{}, uni, left, arrtab, False{}}, Chr{xx}),
        T.st.push(T.St{bad, rows, heads, here, parts, buf, T.LStr{}, back, M1.mk(True{}),
          stack, T.HNone{}, uni, left, arrtab, False{}}, Chr{xx}, T.LStr{}),
        ml.char(True{}, bad, rows, heads, here, parts, buf, T.LStr{}, back, stack,
          T.HNone{}, uni, left, arrtab, False{}, xx, ee))

# one plain character of a multi-line string, from the scan mode
def ml.step(
  +lit: Bool,
  +buf: List<&2, Char>,
  +back: T.Lex,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +stack: List<&2, T.Ctx>,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +xx: U32,
  +ee: {Laws.ml.plain(Chr{xx}) == True{} : Bool}
) -> {T.doc.scan(ms(lit, buf, back, bad, rows, heads, here, parts, stack, uni, left,
  arrtab), Chr{xx}) == T.MScan{ms(lit, Chr{xx} <> buf, back, bad, rows, heads, here,
  parts, stack, uni, left, arrtab)} : T.Mode}:
  Equal.trans(T.Mode,
    T.doc.scan(ms(lit, buf, back, bad, rows, heads, here, parts, stack, uni, left, arrtab),
      Chr{xx}),
    T.MScan{T.read.fast(ms(lit, buf, back, bad, rows, heads, here, parts, stack, uni, left,
      arrtab), Chr{xx})},
    T.MScan{ms(lit, Chr{xx} <> buf, back, bad, rows, heads, here, parts, stack, uni, left,
      arrtab)},
    M4.scan.other(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), U32.is_eq(xx, 13),
      ms(lit, buf, back, bad, rows, heads, here, parts, stack, uni, left, arrtab), Chr{xx},
      {==}, {==}, {==}, ch => Laws.ml.plain(ch), ee, {==}, {==}, {==}),
    Equal.cong(T.St, T.Mode, s => T.MScan{s},
      T.read.fast(ms(lit, buf, back, bad, rows, heads, here, parts, stack, uni, left,
        arrtab), Chr{xx}),
      ms(lit, Chr{xx} <> buf, back, bad, rows, heads, here, parts, stack, uni, left, arrtab),
      ml.fast(lit, buf, back, bad, rows, heads, here, parts, stack, uni, left, arrtab, xx,
        ee)))

# a body of plain characters is pushed onto the buffer, whatever follows it
def ml.body(
  xs: String,
  +rr: String,
  +lit: Bool,
  +buf: List<&2, Char>,
  +back: T.Lex,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +stack: List<&2, T.Ctx>,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +ee: {Laws.ml.text(xs) == True{} : Bool}
) -> {T.doc.read(String.append(xs, rr), T.MScan{ms(lit, buf, back, bad, rows, heads, here,
  parts, stack, uni, left, arrtab)}) == T.doc.read(rr, T.MScan{ms(lit, M2.rev.onto(xs, buf),
  back, bad, rows, heads, here, parts, stack, uni, left, arrtab)}) : T.Doc}:
  match xs:
    case SNil{}:
      {==}
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          Equal.trans(T.Doc,
            T.doc.read(String.append(tt, rr), T.doc.scan(ms(lit, buf, back, bad, rows, heads,
              here, parts, stack, uni, left, arrtab), Chr{xx})),
            T.doc.read(String.append(tt, rr), T.MScan{ms(lit, Chr{xx} <> buf, back, bad,
              rows, heads, here, parts, stack, uni, left, arrtab)}),
            T.doc.read(rr, T.MScan{ms(lit, M2.rev.onto(tt, Chr{xx} <> buf), back, bad, rows,
              heads, here, parts, stack, uni, left, arrtab)}),
            Equal.cong(T.Mode, T.Doc, m => T.doc.read(String.append(tt, rr), m),
              T.doc.scan(ms(lit, buf, back, bad, rows, heads, here, parts, stack, uni, left,
                arrtab), Chr{xx}),
              T.MScan{ms(lit, Chr{xx} <> buf, back, bad, rows, heads, here, parts, stack, uni,
                left, arrtab)},
              ml.step(lit, buf, back, bad, rows, heads, here, parts, stack, uni, left, arrtab,
                xx, Eq.and.left(Laws.ml.plain(Chr{xx}), Laws.ml.text(tt), ee))),
            ml.body(tt, rr, lit, Chr{xx} <> buf, back, bad, rows, heads, here, parts, stack,
              uni, left, arrtab, Eq.and.right(Laws.ml.plain(Chr{xx}), Laws.ml.text(tt), ee)))

# a multi-line string about to trim one opening newline
def mt(
  lit: Bool,
  buf: List<&2, Char>,
  back: T.Lex,
  bad: String,
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  parts: List<&2, String>,
  stack: List<&2, T.Ctx>,
  uni: U32,
  left: U32,
  arrtab: Bool
) -> T.St:
  T.St{bad, rows, heads, here, parts, buf, T.LTrim{}, back, M1.mk(lit), stack, T.HNone{}, uni,
    left, arrtab, False{}}

# a plain first character is no newline to trim: it is held, then pushed
def ml.tgo(
  cr: Bool,
  nl: Bool,
  +lit: Bool,
  +buf: List<&2, Char>,
  +back: T.Lex,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +stack: List<&2, T.Ctx>,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +xx: U32,
  ecr: {U32.is_eq(xx, 13) == cr : Bool},
  enl: {T.ch.nl(Chr{xx}) == nl : Bool},
  +ee: {Laws.ml.plain(Chr{xx}) == True{} : Bool}
) -> {T.read.once2(T.lex.trim.go(cr, nl, mt(lit, buf, back, bad, rows, heads, here, parts,
  stack, uni, left, arrtab), Chr{xx})) == ms(lit, Chr{xx} <> buf, T.LStr{}, bad, rows,
  heads, here, parts, stack, uni, left, arrtab) : T.St}:
  match cr:
    case True{}:
      Eq.bit.gone(&2, {T.read.once2(T.lex.trim.go(True{}, nl, mt(lit, buf, back, bad, rows,
        heads, here, parts, stack, uni, left, arrtab), Chr{xx})) == ms(lit, Chr{xx} <> buf,
        T.LStr{}, bad, rows, heads, here, parts, stack, uni, left, arrtab) : T.St},
        Eq.refute_char(Chr{xx}, Chr{13}, ch => Laws.ml.plain(ch), ecr, ee, {==}))
    case False{}:
      match nl:
        case True{}:
          Eq.bit.gone(&2, {T.read.once2(T.lex.trim.go(False{}, True{}, mt(lit, buf, back,
            bad, rows, heads, here, parts, stack, uni, left, arrtab), Chr{xx}))
            == ms(lit, Chr{xx} <> buf, T.LStr{}, bad, rows, heads, here, parts, stack, uni,
            left, arrtab) : T.St},
            M7.or2.no(xx, 10, 13, U32.is_eq(xx, 10), U32.is_eq(xx, 13), {==}, {==}, enl,
              ch => Laws.ml.plain(ch), ee, {==}, {==}))
        case False{}:
          ml.char(lit, bad, rows, heads, here, parts, buf, T.LStr{}, T.LStr{}, stack,
            T.HNone{}, uni, left, arrtab, False{}, xx, ee)

# the first plain character of a multi-line string, from the scan mode
def ml.first(
  +lit: Bool,
  +buf: List<&2, Char>,
  +back: T.Lex,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +stack: List<&2, T.Ctx>,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +xx: U32,
  +ee: {Laws.ml.plain(Chr{xx}) == True{} : Bool}
) -> {T.doc.scan(mt(lit, buf, back, bad, rows, heads, here, parts, stack, uni, left,
  arrtab), Chr{xx}) == T.MScan{ms(lit, Chr{xx} <> buf, T.LStr{}, bad, rows, heads, here,
  parts, stack, uni, left, arrtab)} : T.Mode}:
  Equal.trans(T.Mode,
    T.doc.scan(mt(lit, buf, back, bad, rows, heads, here, parts, stack, uni, left, arrtab),
      Chr{xx}),
    T.MScan{T.read.fast(mt(lit, buf, back, bad, rows, heads, here, parts, stack, uni, left,
      arrtab), Chr{xx})},
    T.MScan{ms(lit, Chr{xx} <> buf, T.LStr{}, bad, rows, heads, here, parts, stack, uni,
      left, arrtab)},
    M4.scan.other(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), U32.is_eq(xx, 13),
      mt(lit, buf, back, bad, rows, heads, here, parts, stack, uni, left, arrtab), Chr{xx},
      {==}, {==}, {==}, ch => Laws.ml.plain(ch), ee, {==}, {==}, {==}),
    Equal.cong(T.St, T.Mode, s => T.MScan{s},
      T.read.fast(mt(lit, buf, back, bad, rows, heads, here, parts, stack, uni, left,
        arrtab), Chr{xx}),
      ms(lit, Chr{xx} <> buf, T.LStr{}, bad, rows, heads, here, parts, stack, uni, left,
        arrtab),
      ml.tgo(U32.is_eq(xx, 13), T.ch.nl(Chr{xx}), lit, buf, back, bad, rows, heads, here,
        parts, stack, uni, left, arrtab, xx, {==}, {==}, ee)))

# the document of one key `a` holding a string
def doc.a(ss: String) -> T.Doc:
  T.Doc{"", [T.VPair{"a", T.VStr{ss}}]}

# the closing quotes after a body pushed onto the buffer: the string closes
# with the quotes before the delimiter as its last characters
def ml.ends(
  lit: Bool,
  tail: String,
  extra: String,
  bb: List<&2, Char>
) -> Type:
  {T.doc.read(tail, T.MScan{ms(lit, bb, T.LStr{}, "", [], [], [], ["a"], [], 0, 0,
    False{})}) == doc.a(T.buf.str.go(bb, extra)) : T.Doc}

# a key `a` and a multi-line string of plain characters, from the character
# after the opening delimiter: the first character, the body, and then the
# closing quotes the law names, which `ends` reads
def ml.law(
  +lit: Bool,
  +tail: String,
  +extra: String,
  +xx: U32,
  +tt: String,
  +ee: {Bool.and(Laws.ml.plain(Chr{xx}), Laws.ml.text(tt)) == True{} : Bool},
  ends: ml.ends(lit, tail, extra, M2.rev.onto(tt, [Chr{xx}]))
) -> {T.doc.read(String.append(tt, tail), T.doc.scan(mt(lit, [], T.LTop{}, "", [], [], [],
  ["a"], [], 0, 0, False{}), Chr{xx})) == T.Doc{"", [T.VPair{"a", T.VStr{SCon{Chr{xx},
  String.append(tt, extra)}}}]} : T.Doc}:
  Equal.trans(T.Doc,
    T.doc.read(String.append(tt, tail), T.doc.scan(mt(lit, [], T.LTop{}, "", [], [], [],
      ["a"], [], 0, 0, False{}), Chr{xx})),
    T.doc.read(String.append(tt, tail), T.MScan{ms(lit, [Chr{xx}], T.LStr{}, "", [], [], [],
      ["a"], [], 0, 0, False{})}),
    T.Doc{"", [T.VPair{"a", T.VStr{SCon{Chr{xx}, String.append(tt, extra)}}}]},
    Equal.cong(T.Mode, T.Doc, m => T.doc.read(String.append(tt, tail), m),
      T.doc.scan(mt(lit, [], T.LTop{}, "", [], [], [], ["a"], [], 0, 0, False{}), Chr{xx}),
      T.MScan{ms(lit, [Chr{xx}], T.LStr{}, "", [], [], [], ["a"], [], 0, 0, False{})},
      ml.first(lit, [], T.LTop{}, "", [], [], [], ["a"], [], 0, 0, False{}, xx,
        Eq.and.left(Laws.ml.plain(Chr{xx}), Laws.ml.text(tt), ee))),
    Equal.trans(T.Doc,
      T.doc.read(String.append(tt, tail), T.MScan{ms(lit, [Chr{xx}], T.LStr{}, "", [], [],
        [], ["a"], [], 0, 0, False{})}),
      T.doc.read(tail, T.MScan{ms(lit, M2.rev.onto(tt, [Chr{xx}]), T.LStr{}, "", [], [], [],
        ["a"], [], 0, 0, False{})}),
      T.Doc{"", [T.VPair{"a", T.VStr{SCon{Chr{xx}, String.append(tt, extra)}}}]},
      ml.body(tt, tail, lit, [Chr{xx}], T.LStr{}, "", [], [], [], ["a"], [], 0, 0, False{},
        Eq.and.right(Laws.ml.plain(Chr{xx}), Laws.ml.text(tt), ee)),
      Equal.trans(T.Doc,
        T.doc.read(tail, T.MScan{ms(lit, M2.rev.onto(tt, [Chr{xx}]), T.LStr{}, "", [], [], [],
          ["a"], [], 0, 0, False{})}),
        T.Doc{"", [T.VPair{"a", T.VStr{T.buf.str.go(M2.rev.onto(tt, [Chr{xx}]), extra)}}]},
        T.Doc{"", [T.VPair{"a", T.VStr{SCon{Chr{xx}, String.append(tt, extra)}}}]},
        ends,
        Equal.cong(String, T.Doc, s => doc.a(s),
          T.buf.str.go(M2.rev.onto(tt, [Chr{xx}]), extra),
          SCon{Chr{xx}, String.append(tt, extra)},
          M7.ml.rev(tt, [Chr{xx}], extra)))))

def Laws.ml_basic_one_quote(x, e):
  match x:
    case SNil{}:
      {==}
    case SCon{hh, tt}:
      match hh:
        case Chr{xx}:
          ml.law(False{}, "\"\"\"\"\n", "\"", xx, tt, e, {==})

def Laws.ml_basic_two_quotes(x, e):
  match x:
    case SNil{}:
      {==}
    case SCon{hh, tt}:
      match hh:
        case Chr{xx}:
          ml.law(False{}, "\"\"\"\"\"", "\"\"", xx, tt, e, {==})

def Laws.ml_literal_one_quote(x, e):
  match x:
    case SNil{}:
      {==}
    case SCon{hh, tt}:
      match hh:
        case Chr{xx}:
          ml.law(True{}, "''''\n", "'", xx, tt, e, {==})

def Laws.ml_literal_two_quotes(x, e):
  match x:
    case SNil{}:
      {==}
    case SCon{hh, tt}:
      match hh:
        case Chr{xx}:
          ml.law(True{}, "'''''", "''", xx, tt, e, {==})

# the document of one key holding the empty string
def doc.empty(ss: String) -> T.Doc:
  T.Doc{"", [T.VPair{ss, T.VStr{""}}]}

# the rest of the text after `=` ends the key: the document is the key and an
# empty string
def key.done(rest: String, bb: List<&2, Char>) -> Type:
  {T.doc.read(rest, T.MScan{T.read.once2(T.lex.key.end.go(False{}, M1.ky(bb), T.LVal{}))})
    == doc.empty(T.buf.str.go(bb, "")) : T.Doc}

# `=` ends a nonempty key, and the rest of the text (an empty string of
# either kind) is read to the end: the document is the key and the value
def key.end(
  +rest: String,
  +bb: List<&2, Char>,
  full: {List.is_empty(&2, Char, bb) == False{} : Bool},
  done: key.done(rest, bb)
) -> {T.doc.read(SCon{'=', rest}, T.MScan{M1.ky(bb)}) == T.Doc{"", [T.VPair{T.buf.str.go(bb,
  ""), T.VStr{""}}]} : T.Doc}:
  Equal.trans(T.Doc,
    T.doc.read(rest, T.MScan{T.read.once2(T.lex.key.end.go(List.is_empty(&2, Char, bb),
      M1.ky(bb), T.LVal{}))}),
    T.doc.read(rest, T.MScan{T.read.once2(T.lex.key.end.go(False{}, M1.ky(bb), T.LVal{}))}),
    T.Doc{"", [T.VPair{T.buf.str.go(bb, ""), T.VStr{""}}]},
    Equal.cong(Bool, T.Doc,
      b => T.doc.read(rest, T.MScan{T.read.once2(T.lex.key.end.go(b, M1.ky(bb), T.LVal{}))}),
      List.is_empty(&2, Char, bb), False{}, full),
    done)

# a bare key, then `=` and an empty string that ends the text
def key.law(
  +rest: String,
  +xx: U32,
  +tt: String,
  +ee: {T.bare.all.step(T.bare.at(Chr{xx}), _u => T.bare.all(String.to_list(tt))) == True{} : Bool},
  done: key.done(rest, M2.rev.onto(tt, [Chr{xx}]))
) -> {T.doc.read(String.append(tt, SCon{'=', rest}), T.doc.scan(T.st.start(), Chr{xx}))
  == doc.empty(SCon{Chr{xx}, tt}) : T.Doc}:
  Equal.trans(T.Doc,
    T.doc.read(String.append(tt, SCon{'=', rest}), T.doc.scan(T.st.start(), Chr{xx})),
    T.doc.read(String.append(tt, SCon{'=', rest}), T.MScan{M1.ky([Chr{xx}])}),
    doc.empty(SCon{Chr{xx}, tt}),
    Equal.cong(T.Mode, T.Doc, m => T.doc.read(String.append(tt, SCon{'=', rest}), m),
      T.doc.scan(T.st.start(), Chr{xx}), T.MScan{M1.ky([Chr{xx}])},
      M1.key.first(xx, M7.ball.head(T.bare.at(Chr{xx}), String.to_list(tt), ee))),
    Equal.trans(T.Doc,
      T.doc.read(String.append(tt, SCon{'=', rest}), T.MScan{M1.ky([Chr{xx}])}),
      T.doc.read(SCon{'=', rest}, T.MScan{M1.ky(M2.rev.onto(tt, [Chr{xx}]))}),
      doc.empty(SCon{Chr{xx}, tt}),
      M1.key.body(tt, SCon{'=', rest}, [Chr{xx}],
        M7.ball.tail(T.bare.at(Chr{xx}), String.to_list(tt), ee)),
      Equal.trans(T.Doc,
        T.doc.read(SCon{'=', rest}, T.MScan{M1.ky(M2.rev.onto(tt, [Chr{xx}]))}),
        doc.empty(T.buf.str.go(M2.rev.onto(tt, [Chr{xx}]), "")),
        doc.empty(SCon{Chr{xx}, tt}),
        key.end(rest, M2.rev.onto(tt, [Chr{xx}]), M7.rev.full(tt, Chr{xx}, []), done),
        Equal.cong(String, T.Doc, s => doc.empty(s),
          T.buf.str.go(M2.rev.onto(tt, [Chr{xx}]), ""), SCon{Chr{xx}, tt},
          Equal.trans(String, T.buf.str.go(M2.rev.onto(tt, [Chr{xx}]), ""),
            SCon{Chr{xx}, String.append(tt, "")}, SCon{Chr{xx}, tt},
            M7.ml.rev(tt, [Chr{xx}], ""),
            Equal.cong(String, String, s => SCon{Chr{xx}, s}, String.append(tt, ""), tt,
              Eq.append_nil(tt)))))))

def Laws.empty_basic_at_end(k, e):
  match k:
    case SNil{}:
      Eq.bit.absurd(&2, {T.parse(String.append(SNil{}, "=\"\""))
        == T.Doc{"", [T.VPair{SNil{}, T.VStr{""}}]} : T.Doc}, e)
    case SCon{hh, tt}:
      match hh:
        case Chr{xx}:
          key.law("\"\"", xx, tt, e, {==})

def Laws.empty_literal_at_end(k, e):
  match k:
    case SNil{}:
      Eq.bit.absurd(&2, {T.parse(String.append(SNil{}, "=''"))
        == T.Doc{"", [T.VPair{SNil{}, T.VStr{""}}]} : T.Doc}, e)
    case SCon{hh, tt}:
      match hh:
        case Chr{xx}:
          key.law("''", xx, tt, e, {==})

# the owned document is the one named
def sw.Own(+want: T.Doc, dd: T.Doc) -> Type:
  {D2.own(dd) == want : T.Doc}

# a root pair's string value, then a newline, end the document
def sw.root(
  vv: T.Val,
  +kk: String,
  +ss: String,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  hv: M7.sv.Is(vv, ss)
) -> sw.Own(T.Doc{"", [T.VPair{kk, T.VStr{ss}}]}, T.doc.read("\n", T.MScan{M7.sv.took([], vv, "", [], [], [], [kk],
  bk, un, lf, False{})})):
  match vv:
    case T.VStr{st}:
      Equal.cong(String, T.Doc, xs => T.Doc{"", [T.VPair{kk, T.VStr{xs}}]}, st, ss, hv)
    case T.VSpan{src, +nn}:
      Equal.cong(String, T.Doc, xs => T.Doc{"", [T.VPair{kk, T.VStr{xs}}]}, T.span.str(src, nn, U32.is_zero(nn)),
        ss, hv)
    case T.VInt{_sign, _digits}:
      match hv:
    case T.VFlo{_sign, _text}:
      match hv:
    case T.VBool{_bit}:
      match hv:
    case T.VWhen{_when}:
      match hv:
    case T.VArr{_items}:
      match hv:
    case T.VInl{_rows}:
      match hv:
    case T.VHead{_path, _rows}:
      match hv:
    case T.VAot{_path, _rows}:
      match hv:
    case T.VAots{_path, _elems}:
      match hv:
    case T.VPair{_name, _val}:
      match hv:

# the root pair
def sw.pair(
  kk: String,
  ek: {T.bare(kk) == True{} : Bool},
  +ss: String,
  es: {D2.short(ss) == True{} : Bool}
) -> sw.Own(T.Doc{"", [T.VPair{kk, T.VStr{ss}}]}, T.parse(String.append(kk, String.append(" = ",
  String.append(T.key.basic(ss), "\n"))))):
  match kk:
    case SNil{}:
      Eq.bit.absurd(&1, sw.Own(T.Doc{"", [T.VPair{SNil{}, T.VStr{ss}}]}, T.parse(String.append(SNil{},
        String.append(" = ", String.append(T.key.basic(ss), "\n"))))), ek)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          M7.pp.step(dd => sw.Own(T.Doc{"", [T.VPair{SCon{Chr{xx}, tt}, T.VStr{ss}}]}, dd),
            T.parse(String.append(SCon{Chr{xx}, tt}, String.append(" = ", String.append(T.key.basic(ss), "\n")))),
            T.doc.read(String.append(T.key.basic(ss), "\n"), T.MScan{M3.fs.st("", [], [], [], [SCon{Chr{xx}, tt}], [],
              T.LVal{}, T.LTop{}, T.QBasic{}, [], 0, 0, False{})}),
            M1.kv.key2(xx, tt, String.append(T.key.basic(ss), "\n"), ek),
            M7.sv.val(ss, "", [], [], [], [SCon{Chr{xx}, tt}], [], T.LTop{}, T.QBasic{}, [], 0, 0, False{}, "\n",
              dd => sw.Own(T.Doc{"", [T.VPair{SCon{Chr{xx}, tt}, T.VStr{ss}}]}, dd), es, {==},
              vv => bk => un => lf => hv => sw.root(vv, SCon{Chr{xx}, tt}, ss, bk, un, lf, hv)))

def Laws.basic_string_reads_back(k, ek, s, es):
  sw.pair(k, ek, s, es)

# an array item's string value, then `]` and a newline, end the document
def sw.item(
  vv: T.Val,
  +kk: String,
  +ss: String,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  hv: M7.sv.Is(vv, ss)
) -> sw.Own(T.Doc{"", [T.VPair{kk, T.VArr{[T.VStr{ss}]}}]}, T.doc.read("]\n",
  T.MScan{M7.sv.took([T.CArr{[], [kk], []}], vv, "", [], [], [], [], bk, un, lf, False{})})):
  match vv:
    case T.VStr{st}:
      Equal.cong(String, T.Doc, xs => T.Doc{"", [T.VPair{kk, T.VArr{[T.VStr{xs}]}}]}, st, ss, hv)
    case T.VSpan{src, +nn}:
      Equal.cong(String, T.Doc, xs => T.Doc{"", [T.VPair{kk, T.VArr{[T.VStr{xs}]}}]},
        T.span.str(src, nn, U32.is_zero(nn)), ss, hv)
    case T.VInt{_sign, _digits}:
      match hv:
    case T.VFlo{_sign, _text}:
      match hv:
    case T.VBool{_bit}:
      match hv:
    case T.VWhen{_when}:
      match hv:
    case T.VArr{_items}:
      match hv:
    case T.VInl{_rows}:
      match hv:
    case T.VHead{_path, _rows}:
      match hv:
    case T.VAot{_path, _rows}:
      match hv:
    case T.VAots{_path, _elems}:
      match hv:
    case T.VPair{_name, _val}:
      match hv:

# the array
def sw.arr(
  kk: String,
  ek: {T.bare(kk) == True{} : Bool},
  +ss: String,
  es: {D2.short(ss) == True{} : Bool}
) -> sw.Own(T.Doc{"", [T.VPair{kk, T.VArr{[T.VStr{ss}]}}]}, T.parse(String.append(kk, String.append(" = [",
  String.append(T.key.basic(ss), "]\n"))))):
  match kk:
    case SNil{}:
      Eq.bit.absurd(&1, sw.Own(T.Doc{"", [T.VPair{SNil{}, T.VArr{[T.VStr{ss}]}}]}, T.parse(String.append(SNil{},
        String.append(" = [", String.append(T.key.basic(ss), "]\n"))))), ek)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          M7.pp.step(dd => sw.Own(T.Doc{"", [T.VPair{SCon{Chr{xx}, tt}, T.VArr{[T.VStr{ss}]}}]}, dd),
            T.parse(String.append(SCon{Chr{xx}, tt}, String.append(" = [", String.append(T.key.basic(ss),
              "]\n")))),
            T.doc.read(String.append(T.key.basic(ss), "]\n"), T.MScan{M3.fs.st("", [], [], [], [], [], T.LArr{},
              T.LTop{}, T.QBasic{}, [T.CArr{[], [SCon{Chr{xx}, tt}], []}], 0, 0, False{})}),
            M1.kv.key2(xx, tt, SCon{'[', String.append(T.key.basic(ss), "]\n")}, ek),
            M1.sv.arr(ss, "", [], [], [], [], [], T.LTop{}, T.QBasic{}, [T.CArr{[], [SCon{Chr{xx}, tt}], []}], 0, 0,
              False{}, "]\n", dd => sw.Own(T.Doc{"", [T.VPair{SCon{Chr{xx}, tt}, T.VArr{[T.VStr{ss}]}}]}, dd), es,
              {==}, vv => bk => un => lf => hv => sw.item(vv, SCon{Chr{xx}, tt}, ss, bk, un, lf, hv)))

def Laws.basic_string_reads_back_in_array(k, ek, s, es):
  sw.arr(k, ek, s, es)

# an inline table's string value, then `}` and a newline, end the document
def sw.inl.val(
  vv: T.Val,
  +kk: String,
  +ss: String,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  hv: M7.sv.Is(vv, ss)
) -> sw.Own(T.Doc{"", [T.VPair{kk, T.VInl{[T.VPair{"v", T.VStr{ss}}]}}]}, T.doc.read("}\n",
  T.MScan{M7.sv.took([T.CInl{[], [kk], []}], vv, "", [], [], [], ["v"], bk, un, lf, False{})})):
  match vv:
    case T.VStr{st}:
      Equal.cong(String, T.Doc, xs => T.Doc{"", [T.VPair{kk, T.VInl{[T.VPair{"v", T.VStr{xs}}]}}]}, st, ss, hv)
    case T.VSpan{src, +nn}:
      Equal.cong(String, T.Doc, xs => T.Doc{"", [T.VPair{kk, T.VInl{[T.VPair{"v", T.VStr{xs}}]}}]},
        T.span.str(src, nn, U32.is_zero(nn)), ss, hv)
    case T.VInt{_sign, _digits}:
      match hv:
    case T.VFlo{_sign, _text}:
      match hv:
    case T.VBool{_bit}:
      match hv:
    case T.VWhen{_when}:
      match hv:
    case T.VArr{_items}:
      match hv:
    case T.VInl{_rows}:
      match hv:
    case T.VHead{_path, _rows}:
      match hv:
    case T.VAot{_path, _rows}:
      match hv:
    case T.VAots{_path, _elems}:
      match hv:
    case T.VPair{_name, _val}:
      match hv:

# the inline table
def sw.inl(
  kk: String,
  ek: {T.bare(kk) == True{} : Bool},
  +ss: String,
  es: {D2.short(ss) == True{} : Bool}
) -> sw.Own(T.Doc{"", [T.VPair{kk, T.VInl{[T.VPair{"v", T.VStr{ss}}]}}]}, T.parse(String.append(kk,
  String.append(" = {v = ", String.append(T.key.basic(ss), "}\n"))))):
  match kk:
    case SNil{}:
      Eq.bit.absurd(&1, sw.Own(T.Doc{"", [T.VPair{SNil{}, T.VInl{[T.VPair{"v", T.VStr{ss}}]}}]},
        T.parse(String.append(SNil{}, String.append(" = {v = ", String.append(T.key.basic(ss), "}\n"))))), ek)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          M7.pp.step(dd => sw.Own(T.Doc{"", [T.VPair{SCon{Chr{xx}, tt}, T.VInl{[T.VPair{"v", T.VStr{ss}}]}}]}, dd),
            T.parse(String.append(SCon{Chr{xx}, tt}, String.append(" = {v = ", String.append(T.key.basic(ss),
              "}\n")))),
            T.doc.read(String.append(T.key.basic(ss), "}\n"), T.MScan{M3.fs.st("", [], [], [], ["v"], [], T.LVal{},
              T.LTop{}, T.QBasic{}, [T.CInl{[], [SCon{Chr{xx}, tt}], []}], 0, 0, False{})}),
            M1.kv.key2(xx, tt, SCon{'{', SCon{'v', SCon{' ', SCon{'=', SCon{' ', String.append(T.key.basic(ss),
              "}\n")}}}}}, ek),
            M7.sv.val(ss, "", [], [], [], ["v"], [], T.LTop{}, T.QBasic{}, [T.CInl{[], [SCon{Chr{xx}, tt}], []}], 0, 0,
              False{}, "}\n", dd => sw.Own(T.Doc{"", [T.VPair{SCon{Chr{xx}, tt}, T.VInl{[T.VPair{"v",
              T.VStr{ss}}]}}]}, dd), es, {==},
              vv => bk => un => lf => hv => sw.inl.val(vv, SCon{Chr{xx}, tt}, ss, bk, un, lf, hv)))

def Laws.basic_string_reads_back_in_inline_table(k, ek, s, es):
  sw.inl(k, ek, s, es)

# a root pair's string value, placed with any back, kind, uni and left, then
# a newline, ends the document of the pair
def s1.root(
  vv: T.Val,
  +kk: String,
  +ss: String,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  hv: Laws.s1.holds(vv, ss)
) -> sw.Own(T.Doc{"", [T.VPair{kk, T.VStr{ss}}]}, T.doc.read("\n", T.MScan{T.take.top([], vv, "", [], [], [], [kk], bk,
  qk, un, lf, False{}, False{})})):
  match vv:
    case T.VStr{tx}:
      Equal.cong(String, T.Doc, xs => T.Doc{"", [T.VPair{kk, T.VStr{xs}}]}, tx, ss, hv)
    case T.VSpan{src, +nn}:
      Equal.cong(String, T.Doc, xs => T.Doc{"", [T.VPair{kk, T.VStr{xs}}]}, T.span.str(src, nn, U32.is_zero(nn)), ss,
        hv)
    case T.VInt{_sign, _digits}:
      match hv:
    case T.VFlo{_sign, _text}:
      match hv:
    case T.VBool{_bit}:
      match hv:
    case T.VWhen{_when}:
      match hv:
    case T.VArr{_items}:
      match hv:
    case T.VInl{_rows}:
      match hv:
    case T.VHead{_path, _rows}:
      match hv:
    case T.VAot{_path, _rows}:
      match hv:
    case T.VAots{_path, _elems}:
      match hv:
    case T.VPair{_name, _val}:
      match hv:

# laws/StringReadsAsDenoted.bend as a document: a bare key, " = " and the string bring the
# scanner to a value position (kv.key2), where the law reads the string, and
# the newline closes the document of the pair
def Laws.string_parses_as_denoted(k, ek, st, ok, es):
  match k:
    case SNil{}:
      Eq.bit.absurd(&1, sw.Own(T.Doc{"", [T.VPair{SNil{}, T.VStr{D1.g.str.chars(st)}}]}, T.parse(String.append(SNil{},
        String.append(" = ", D3.g.str.text(st, "\n"))))), ek)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          M7.pp.step(dd => sw.Own(T.Doc{"", [T.VPair{SCon{Chr{xx}, tt}, T.VStr{D1.g.str.chars(st)}}]}, dd),
            T.parse(String.append(SCon{Chr{xx}, tt}, String.append(" = ", D3.g.str.text(st, "\n")))),
            T.doc.read(D3.g.str.text(st, "\n"), T.MScan{M3.fs.st("", [], [], [], [SCon{Chr{xx}, tt}], [], T.LVal{},
              T.LTop{}, T.QBasic{}, [], 0, 0, False{})}),
            M1.kv.key2(xx, tt, D3.g.str.text(st, "\n"), ek),
            M5.s1.str(st, [], [], [], [SCon{Chr{xx}, tt}], T.LTop{}, T.QBasic{}, [], 0, 0, False{}, "\n",
              dd => sw.Own(T.Doc{"", [T.VPair{SCon{Chr{xx}, tt}, T.VStr{D1.g.str.chars(st)}}]}, dd), ok,
              M5.s1.counts.le(D1.g.str.chars(st), String.append(SCon{Chr{xx}, tt}, String.append(" = ",
                D3.g.str.text(st, "\n"))), 0, M5.s1.ln.app(SCon{Chr{xx}, tt}, D1.g.str.chars(st), String.append(" = ",
                D3.g.str.text(st, "\n")), M5.s1.ln.app(" = ", D1.g.str.chars(st), D3.g.str.text(st, "\n"),
                M5.s1.ln.str(st, "\n"))), es), {==},
              +vv => bk => qk => un => lf => hv => s1.root(vv, SCon{Chr{xx}, tt}, D1.g.str.chars(st), bk, qk, un, lf,
                M5.s1.is.holds(vv, D1.g.str.chars(st), hv))))

# an array item's string value, placed with any back, kind, uni and left,
# then `]` and a newline, ends the document of the pair
def s1.item(
  vv: T.Val,
  +kk: String,
  +ss: String,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  hv: Laws.s1.holds(vv, ss)
) -> sw.Own(T.Doc{"", [T.VPair{kk, T.VArr{[T.VStr{ss}]}}]}, T.doc.read("]\n", T.MScan{T.take.top([T.CArr{[], [kk], []}],
  vv, "", [], [], [], [], bk, qk, un, lf, False{}, False{})})):
  match vv:
    case T.VStr{tx}:
      Equal.cong(String, T.Doc, xs => T.Doc{"", [T.VPair{kk, T.VArr{[T.VStr{xs}]}}]}, tx, ss, hv)
    case T.VSpan{src, +nn}:
      Equal.cong(String, T.Doc, xs => T.Doc{"", [T.VPair{kk, T.VArr{[T.VStr{xs}]}}]},
        T.span.str(src, nn, U32.is_zero(nn)), ss, hv)
    case T.VInt{_sign, _digits}:
      match hv:
    case T.VFlo{_sign, _text}:
      match hv:
    case T.VBool{_bit}:
      match hv:
    case T.VWhen{_when}:
      match hv:
    case T.VArr{_items}:
      match hv:
    case T.VInl{_rows}:
      match hv:
    case T.VHead{_path, _rows}:
      match hv:
    case T.VAot{_path, _rows}:
      match hv:
    case T.VAots{_path, _elems}:
      match hv:
    case T.VPair{_name, _val}:
      match hv:

# laws/StringReadsAsDenoted.bend as an array's item: a bare key and " = [" bring the scanner to
# an array's item (kv.key2), where the law reads the string, and `]` and the
# newline close the document
def Laws.string_parses_as_denoted_in_array(k, ek, st, ok, es):
  match k:
    case SNil{}:
      Eq.bit.absurd(&1, sw.Own(T.Doc{"", [T.VPair{SNil{}, T.VArr{[T.VStr{D1.g.str.chars(st)}]}}]},
        T.parse(String.append(SNil{}, String.append(" = [", D3.g.str.text(st, "]\n"))))), ek)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          M7.pp.step(dd => sw.Own(T.Doc{"", [T.VPair{SCon{Chr{xx}, tt}, T.VArr{[T.VStr{D1.g.str.chars(st)}]}}]}, dd),
            T.parse(String.append(SCon{Chr{xx}, tt}, String.append(" = [", D3.g.str.text(st, "]\n")))),
            T.doc.read(D3.g.str.text(st, "]\n"), T.MScan{D2.s1.apos([], [], [], [], T.LTop{}, T.QBasic{},
              [T.CArr{[], [SCon{Chr{xx}, tt}], []}], 0, 0, False{})}),
            M1.kv.key2(xx, tt, SCon{'[', D3.g.str.text(st, "]\n")}, ek),
            Laws.string_reads_as_denoted_in_array(st, ok, M5.s1.counts.le(D1.g.str.chars(st),
                String.append(SCon{Chr{xx},
              tt}, String.append(" = [", D3.g.str.text(st, "]\n"))), 0, M5.s1.ln.app(SCon{Chr{xx}, tt},
              D1.g.str.chars(st), String.append(" = [", D3.g.str.text(st, "]\n")), M5.s1.ln.app(" = [",
              D1.g.str.chars(st), D3.g.str.text(st, "]\n"), M5.s1.ln.str(st, "]\n"))), es), [], [], [], [], T.LTop{},
              T.QBasic{}, [T.CArr{[], [SCon{Chr{xx}, tt}], []}], 0, 0, False{}, "]\n",
              {==}, dd => sw.Own(T.Doc{"", [T.VPair{SCon{Chr{xx}, tt}, T.VArr{[T.VStr{D1.g.str.chars(st)}]}}]}, dd),
              +vv => bk => qk => un => lf => hv => s1.item(vv, SCon{Chr{xx}, tt}, D1.g.str.chars(st), bk, qk, un, lf,
                hv)))

# an inline table's string value, placed with any back, kind, uni and left,
# then `}` and a newline, ends the document of the pair
def s1.inl.val(
  vv: T.Val,
  +kk: String,
  +ss: String,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  hv: Laws.s1.holds(vv, ss)
) -> sw.Own(T.Doc{"", [T.VPair{kk, T.VInl{[T.VPair{"v", T.VStr{ss}}]}}]}, T.doc.read("}\n",
  T.MScan{T.take.top([T.CInl{[], [kk], []}], vv, "", [], [], [], ["v"], bk, qk, un, lf, False{}, False{})})):
  match vv:
    case T.VStr{tx}:
      Equal.cong(String, T.Doc, xs => T.Doc{"", [T.VPair{kk, T.VInl{[T.VPair{"v", T.VStr{xs}}]}}]}, tx, ss, hv)
    case T.VSpan{src, +nn}:
      Equal.cong(String, T.Doc, xs => T.Doc{"", [T.VPair{kk, T.VInl{[T.VPair{"v", T.VStr{xs}}]}}]},
        T.span.str(src, nn, U32.is_zero(nn)), ss, hv)
    case T.VInt{_sign, _digits}:
      match hv:
    case T.VFlo{_sign, _text}:
      match hv:
    case T.VBool{_bit}:
      match hv:
    case T.VWhen{_when}:
      match hv:
    case T.VArr{_items}:
      match hv:
    case T.VInl{_rows}:
      match hv:
    case T.VHead{_path, _rows}:
      match hv:
    case T.VAot{_path, _rows}:
      match hv:
    case T.VAots{_path, _elems}:
      match hv:
    case T.VPair{_name, _val}:
      match hv:

# laws/StringReadsAsDenoted.bend as an inline table's value: a bare key and " = {v = " bring the
# scanner to the inline table's value position (kv.key2), where the law
# reads the string, and `}` and the newline close the document
def Laws.string_parses_as_denoted_in_inline_table(k, ek, st, ok, es):
  match k:
    case SNil{}:
      Eq.bit.absurd(&1, sw.Own(T.Doc{"", [T.VPair{SNil{}, T.VInl{[T.VPair{"v", T.VStr{D1.g.str.chars(st)}}]}}]},
        T.parse(String.append(SNil{}, String.append(" = {v = ", D3.g.str.text(st, "}\n"))))), ek)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          M7.pp.step(dd => sw.Own(T.Doc{"", [T.VPair{SCon{Chr{xx}, tt}, T.VInl{[T.VPair{"v",
            T.VStr{D1.g.str.chars(st)}}]}}]}, dd),
            T.parse(String.append(SCon{Chr{xx}, tt}, String.append(" = {v = ", D3.g.str.text(st, "}\n")))),
            T.doc.read(D3.g.str.text(st, "}\n"), T.MScan{M3.fs.st("", [], [], [], ["v"], [], T.LVal{}, T.LTop{},
              T.QBasic{}, [T.CInl{[], [SCon{Chr{xx}, tt}], []}], 0, 0, False{})}),
            M1.kv.key2(xx, tt, SCon{'{', SCon{'v', SCon{' ', SCon{'=', SCon{' ', D3.g.str.text(st, "}\n")}}}}}, ek),
            M5.s1.str(st, [], [], [], ["v"], T.LTop{}, T.QBasic{}, [T.CInl{[], [SCon{Chr{xx}, tt}], []}], 0, 0, False{},
              "}\n", dd => sw.Own(T.Doc{"", [T.VPair{SCon{Chr{xx}, tt}, T.VInl{[T.VPair{"v",
              T.VStr{D1.g.str.chars(st)}}]}}]}, dd), ok,
              M5.s1.counts.le(D1.g.str.chars(st), String.append(SCon{Chr{xx}, tt}, String.append(" = {v = ",
                D3.g.str.text(st, "}\n"))), 0, M5.s1.ln.app(SCon{Chr{xx}, tt}, D1.g.str.chars(st),
                String.append(" = {v = ", D3.g.str.text(st, "}\n")), M5.s1.ln.app(" = {v = ", D1.g.str.chars(st),
                D3.g.str.text(st, "}\n"), M5.s1.ln.str(st, "}\n"))), es), {==},
              +vv => bk => qk => un => lf => hv => s1.inl.val(vv, SCon{Chr{xx}, tt}, D1.g.str.chars(st), bk, qk, un,
                lf, M5.s1.is.holds(vv, D1.g.str.chars(st), hv))))
