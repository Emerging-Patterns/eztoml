# the walk over the body of a string and the rest of the text after it
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/StringReadsAsDenoted.bend as L1
import ../../laws/defs/AbnfGrammar.bend as D1
import ../../laws/defs/AbnfWhitespace.bend as D2
import ../../laws/defs/BareValueGrammar.bend as D3
import ../../laws/defs/GrammarDerivations.bend as D4
import ../../laws/defs/KeySegmentSpelling.bend as D5
import ./BasicStringControls.bend as M1
import ./ControlEscapeText.bend as M2
import ./FreshNamesInRows.bend as M3
import ./HeldCharacterSteps.bend as M4
import ./PickAndDigitSteps.bend as M5
import ./PrefixAndTake.bend as M6
import ./ShortTextBounds.bend as M7
import ./ValueTextReadback.bend as M8

# such a character is one str.bad passes, in a one-line string or a
# multi-line one
def s1.sb.go(
  t9: Bool,
  +uu: U32,
  +ml: Bool,
  e9: {U32.is_eq(uu, 9) == t9 : Bool},
  c9: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == U32.is_eq(uu, 9) : Bool}
) -> {T.str.bad(uu, ml) == False{} : Bool}:
  match t9:
    case True{}:
      %Equal.sym(U32, uu, 9, M1.s1.is9(uu, e9)) : {T.str.bad(_, ml) == False{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), False{}, Equal.trans(Bool,
        Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), U32.is_eq(uu, 9), False{}, c9, e9)) :
        {T.str.bad.go(_, U32.is_eq(uu, 9), Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)), ml) == False{} : Bool}
      {==}

# str.bad passes it
def s1.sb(
  +uu: U32,
  +ml: Bool,
  c9: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == U32.is_eq(uu, 9) : Bool}
) -> {T.str.bad(uu, ml) == False{} : Bool}:
  s1.sb.go(U32.is_eq(uu, 9), uu, ml, {==}, c9)

# it is no control k other than tab
def s1.nk.go(
  t9: Bool,
  +uu: U32,
  +kk: U32,
  e9: {U32.is_eq(uu, 9) == t9 : Bool},
  c9: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == U32.is_eq(uu, 9) : Bool},
  ek: {Bool.or(U32.is_lt(kk, 32), U32.is_eq(kk, 127)) == True{} : Bool},
  k9: {U32.is_eq(9, kk) == False{} : Bool}
) -> {U32.is_eq(uu, kk) == False{} : Bool}:
  match t9:
    case True{}:
      %Equal.sym(U32, uu, 9, M1.s1.is9(uu, e9)) : {U32.is_eq(_, kk) == False{} : Bool}
      k9
    case False{}:
      M2.ctl.off(uu, kk, Equal.trans(Bool, Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), U32.is_eq(uu, 9), False{},
        c9, e9), ek)

# no carriage return
def s1.ncr(
  +uu: U32,
  c9: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == U32.is_eq(uu, 9) : Bool}
) -> {U32.is_eq(uu, 13) == False{} : Bool}:
  s1.nk.go(U32.is_eq(uu, 9), uu, 13, {==}, c9, {==}, {==})

# no line feed
def s1.nlf(
  +uu: U32,
  c9: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == U32.is_eq(uu, 9) : Bool}
) -> {U32.is_eq(uu, 10) == False{} : Bool}:
  s1.nk.go(U32.is_eq(uu, 9), uu, 10, {==}, c9, {==}, {==})

# no newline, as ch.nl tests one
def s1.nnl(
  +uu: U32,
  +c9: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == U32.is_eq(uu, 9) : Bool}
) -> {T.ch.nl(Chr{uu}) == False{} : Bool}:
  M8.or.ff(U32.is_eq(uu, 10), U32.is_eq(uu, 13), s1.nlf(uu, c9), s1.ncr(uu, c9))

# A basic string in LStr, one piece at a time. A one-line string's plain
# characters take the fast step (read.fast.basic), and a multi-line string's
# take the full step (lex.str); an escape goes through LEsc and a \u or \U
# escape through LUni in both. The string's state is fs.st with lex LStr,
# its characters so far reversed in buf; each piece pushes the character it
# stands for and keeps back, and the rest is read from whatever uni and left
# the piece leaves.

# the kind of a basic string: a multi-line one's when ml, a one-line one's
# otherwise
def s1.bk(ml: Bool) -> T.QKind:
  match ml:
    case True{}:
      T.QMulti{}
    case False{}:
      T.QBasic{}

# the rest of the text read from a string of kind qk in LStr with buf in its
# buffer, whatever back, uni and left are
def s1.Then(
  +qk: T.QKind,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  @b2: T.Lex -> @u2: U32 -> @l2: U32 ->
    PP(T.doc.read(rest, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, b2, qk, sk, u2, l2, ab)}))

# the scan mode reads a character that is no carriage return by the fast
# step, and doc.wrap leaves that step's state as it is when it opens no string
def s1.scq(
  dq: Bool,
  sq: Bool,
  cr: Bool,
  +st: T.St,
  +cc: Char,
  +s2: T.St,
  hr: {cr == False{} : Bool},
  fast: {T.read.fast(st, cc) == s2 : T.St},
  hw: {T.doc.wrap(s2) == T.MScan{s2} : T.Mode}
) -> {T.doc.scan.q(dq, sq, cr, st, cc) == T.MScan{s2} : T.Mode}:
  match dq sq cr:
    case True{} _s _c:
      Equal.trans(T.Mode, T.doc.wrap(T.read.fast(st, cc)), T.doc.wrap(s2), T.MScan{s2},
        Equal.cong(T.St, T.Mode, xs => T.doc.wrap(xs), T.read.fast(st, cc), s2, fast), hw)
    case False{} True{} _c:
      Equal.trans(T.Mode, T.doc.wrap(T.read.fast(st, cc)), T.doc.wrap(s2), T.MScan{s2},
        Equal.cong(T.St, T.Mode, xs => T.doc.wrap(xs), T.read.fast(st, cc), s2, fast), hw)
    case False{} False{} True{}:
      Eq.bit.absurd2(&2, {T.doc.scan.q(False{}, False{}, True{}, st, cc) == T.MScan{s2} : T.Mode}, hr)
    case False{} False{} False{}:
      Equal.cong(T.St, T.Mode, xs => T.MScan{xs}, T.read.fast(st, cc), s2, fast)

# a one-line string's fast step pushes a character that is no quotation
# mark and no backslash, and that str.bad passes
def s1.fb(
  quote: Bool,
  bs: Bool,
  +uu: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  hq: {quote == False{} : Bool},
  hb: {bs == False{} : Bool},
  sb: {T.str.bad(uu, False{}) == False{} : Bool}
) -> {T.read.fast.basic(quote, bs, bd, rw, hs, he, ps, buf, bk, sk, un, lf, ab, Chr{uu})
  == M4.fs.st(bd, rw, hs, he, ps, Chr{uu} <> buf, T.LStr{}, bk, T.QBasic{}, sk, un, lf, ab) : T.St}:
  match quote bs:
    case True{} b2:
      Eq.bit.absurd2(&2, {T.read.fast.basic(True{}, b2, bd, rw, hs, he, ps, buf, bk, sk, un, lf, ab, Chr{uu})
        == M4.fs.st(bd, rw, hs, he, ps, Chr{uu} <> buf, T.LStr{}, bk, T.QBasic{}, sk, un, lf, ab) : T.St}, hq)
    case False{} True{}:
      Eq.bit.absurd2(&2, {T.read.fast.basic(False{}, True{}, bd, rw, hs, he, ps, buf, bk, sk, un, lf, ab, Chr{uu})
        == M4.fs.st(bd, rw, hs, he, ps, Chr{uu} <> buf, T.LStr{}, bk, T.QBasic{}, sk, un, lf, ab) : T.St}, hb)
    case False{} False{}:
      %Equal.sym(Bool, T.str.bad(uu, False{}), False{}, sb) : {T.read.fast.push(_, bd, rw, hs, he, ps, buf,
        T.LStr{}, bk, T.QBasic{}, sk, un, lf, ab, Chr{uu})
        == M4.fs.st(bd, rw, hs, he, ps, Chr{uu} <> buf, T.LStr{}, bk, T.QBasic{}, sk, un, lf, ab) : T.St}
      {==}

# a multi-line string's full step pushes a character that is no backslash
# and that str.bad passes
def s1.fm2(
  bs: Bool,
  +uu: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  hb: {bs == False{} : Bool},
  sb: {T.str.bad(uu, True{}) == False{} : Bool}
) -> {T.read.once2(T.lex.str.bs(bs, True{}, M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, bk, T.QMulti{}, sk, un, lf, ab),
  Chr{uu}, T.QMulti{})) == M4.fs.st(bd, rw, hs, he, ps, Chr{uu} <> buf, T.LStr{}, bk, T.QMulti{}, sk, un, lf, ab) : T.St}:  # noqa: S002
  match bs:
    case True{}:
      Eq.bit.absurd2(&2, {T.read.once2(T.lex.str.bs(True{}, True{}, M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, bk,
        T.QMulti{}, sk, un, lf, ab), Chr{uu}, T.QMulti{}))
        == M4.fs.st(bd, rw, hs, he, ps, Chr{uu} <> buf, T.LStr{}, bk, T.QMulti{}, sk, un, lf, ab) : T.St}, hb)
    case False{}:
      %Equal.sym(Bool, T.str.bad(uu, True{}), False{}, sb) : {T.read.once2(T.lex.str.char.go(_, M4.fs.st(bd, rw, hs, he,
        ps, buf, T.LStr{}, bk, T.QMulti{}, sk, un, lf, ab), Chr{uu}))
        == M4.fs.st(bd, rw, hs, he, ps, Chr{uu} <> buf, T.LStr{}, bk, T.QMulti{}, sk, un, lf, ab) : T.St}
      {==}

# and that is no quotation mark
def s1.fm(
  quote: Bool,
  +uu: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  hq: {quote == False{} : Bool},
  hb: {U32.is_eq(uu, 92) == False{} : Bool},
  sb: {T.str.bad(uu, True{}) == False{} : Bool}
) -> {T.read.once2(T.lex.str.go(quote, True{}, True{}, M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, bk, T.QMulti{}, sk,
  un, lf, ab), Chr{uu}, T.QMulti{}))
  == M4.fs.st(bd, rw, hs, he, ps, Chr{uu} <> buf, T.LStr{}, bk, T.QMulti{}, sk, un, lf, ab) : T.St}:
  match quote:
    case True{}:
      Eq.bit.absurd2(&2, {T.read.once2(T.lex.str.go(True{}, True{}, True{}, M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{},
        bk, T.QMulti{}, sk, un, lf, ab), Chr{uu}, T.QMulti{}))
        == M4.fs.st(bd, rw, hs, he, ps, Chr{uu} <> buf, T.LStr{}, bk, T.QMulti{}, sk, un, lf, ab) : T.St}, hq)
    case False{}:
      s1.fm2(U32.is_eq(uu, 92), uu, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, hb, sb)

# the step of a basic string's character that is no quotation mark and no
# backslash, and that str.bad passes, pushes it, one-line or multi-line
def s1.fast.ch(
  ml: Bool,
  +uu: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  e34: {U32.is_eq(uu, 34) == False{} : Bool},
  e92: {U32.is_eq(uu, 92) == False{} : Bool},
  sb0: {T.str.bad(uu, False{}) == False{} : Bool},
  sb1: {T.str.bad(uu, True{}) == False{} : Bool}
) -> {T.read.fast(M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, bk, s1.bk(ml), sk, un, lf, ab), Chr{uu})
  == M4.fs.st(bd, rw, hs, he, ps, Chr{uu} <> buf, T.LStr{}, bk, s1.bk(ml), sk, un, lf, ab) : T.St}:
  match ml:
    case False{}:
      s1.fb(U32.is_eq(uu, 34), U32.is_eq(uu, 92), uu, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, e34, e92, sb0)
    case True{}:
      s1.fm(U32.is_eq(uu, 34), uu, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, e34, e92, sb1)

# a character basic-unescaped takes is pushed, and back, uni and left stay
def s1.chr(
  +ml: Bool,
  +uu: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  +hb: {D1.abnf.basic_unescaped(Chr{uu}) == True{} : Bool},
  ih: s1.Then(s1.bk(ml), bd, rw, hs, he, ps, sk, ab, Chr{uu} <> buf, rest, PP)
) -> PP(T.doc.read(SCon{Chr{uu}, rest}, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, bk, s1.bk(ml), sk, un, lf,
  ab)})):
  +c9 = {M1.s1.bu.c9(uu, hb) : {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == U32.is_eq(uu, 9) : Bool}}
  M8.pp.step(PP,
    T.doc.read(SCon{Chr{uu}, rest}, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, bk, s1.bk(ml), sk, un, lf,
        ab)}),
    T.doc.read(rest, T.MScan{M4.fs.st(bd, rw, hs, he, ps, Chr{uu} <> buf, T.LStr{}, bk, s1.bk(ml), sk, un, lf, ab)}),
    Equal.cong(T.Mode, T.Doc, md => T.doc.read(rest, md),
      T.doc.scan(M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, bk, s1.bk(ml), sk, un, lf, ab), Chr{uu}),
      T.MScan{M4.fs.st(bd, rw, hs, he, ps, Chr{uu} <> buf, T.LStr{}, bk, s1.bk(ml), sk, un, lf, ab)},
      s1.scq(U32.is_eq(uu, 34), U32.is_eq(uu, 39), U32.is_eq(uu, 13),
        M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, bk, s1.bk(ml), sk, un, lf, ab), Chr{uu},
        M4.fs.st(bd, rw, hs, he, ps, Chr{uu} <> buf, T.LStr{}, bk, s1.bk(ml), sk, un, lf, ab), s1.ncr(uu, c9),
        s1.fast.ch(ml, uu, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, M1.s1.bu.q(uu, hb), M1.s1.bu.b(uu, hb),
          s1.sb(uu, False{}, c9), s1.sb(uu, True{}, c9)), {==})),
    ih(bk, un, lf))

# a two-character escape pushes the character it stands for, and back, uni
# and left stay
def s1.esc(
  mm: D5.KMark,
  ml: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  ih: s1.Then(s1.bk(ml), bd, rw, hs, he, ps, sk, ab, D5.k3.mark.dec(mm) <> buf, rest, PP)
) -> PP(T.doc.read(SCon{'\\', SCon{D5.k3.mark.char(mm), rest}}, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{},
  bk, s1.bk(ml), sk, un, lf, ab)})):
  match mm ml:
    case D5.KmQuote{} False{}:
      ih(bk, un, lf)
    case D5.KmQuote{} True{}:
      ih(bk, un, lf)
    case D5.KmBack{} False{}:
      ih(bk, un, lf)
    case D5.KmBack{} True{}:
      ih(bk, un, lf)
    case D5.KmB{} False{}:
      ih(bk, un, lf)
    case D5.KmB{} True{}:
      ih(bk, un, lf)
    case D5.KmF{} False{}:
      ih(bk, un, lf)
    case D5.KmF{} True{}:
      ih(bk, un, lf)
    case D5.KmN{} False{}:
      ih(bk, un, lf)
    case D5.KmN{} True{}:
      ih(bk, un, lf)
    case D5.KmR{} False{}:
      ih(bk, un, lf)
    case D5.KmR{} True{}:
      ih(bk, un, lf)
    case D5.KmT{} False{}:
      ih(bk, un, lf)
    case D5.KmT{} True{}:
      ih(bk, un, lf)

# a digit of a \u or \U escape that is not the last one joins the number
# read so far, and one digit fewer is left, whatever kind the string is
def s1.hx.mid(
  +hx: D5.KHex,
  +qk: T.QKind,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  el: {U32.is_eq(lf, 1) == False{} : Bool}
) -> {M4.fs.st(bd, rw, hs, he, ps, buf, T.LUni{}, bk, qk, sk, D5.k3.hex.acc(un, hx), U32.sub(lf, 1), ab)
  == T.read.fast(M4.fs.st(bd, rw, hs, he, ps, buf, T.LUni{}, bk, qk, sk, un, lf, ab), D5.k3.hex.char(hx)) : T.St}:
  %M8.k3.hx.ok(hx) : {M4.fs.st(bd, rw, hs, he, ps, buf, T.LUni{}, bk, qk, sk, D5.k3.hex.acc(un, hx), U32.sub(lf, 1), ab)
    == T.read.once2(T.uni.go(_, M4.fs.st(bd, rw, hs, he, ps, buf, T.LUni{}, bk, qk, sk, un, lf, ab),
    D5.k3.hex.char(hx), T.LStr{}, un, lf)) : T.St}
  %M8.k3.hx.dv(hx) : {M4.fs.st(bd, rw, hs, he, ps, buf, T.LUni{}, bk, qk, sk, D5.k3.hex.acc(un, hx), U32.sub(lf, 1), ab)
    == T.read.once2(T.uni.next(U32.is_eq(lf, 1), M4.fs.st(bd, rw, hs, he, ps, buf, T.LUni{}, bk, qk, sk, un, lf, ab),
    U32.add(U32.mul(un, 16), _), T.LStr{}, lf)) : T.St}
  %Equal.sym(Bool, U32.is_eq(lf, 1), False{}, el) : {M4.fs.st(bd, rw, hs, he, ps, buf, T.LUni{}, bk, qk, sk,
    D5.k3.hex.acc(un, hx), U32.sub(lf, 1), ab) == T.read.once2(T.uni.next(_, M4.fs.st(bd, rw, hs, he, ps, buf,
    T.LUni{}, bk, qk, sk, un, lf, ab), D5.k3.hex.acc(un, hx), T.LStr{}, lf)) : T.St}
  {==}

# the last digit: the number is a Unicode scalar value, pushed as the
# character, and the string's state is back with uni and left at 0
def s1.hx.last(
  +hx: D5.KHex,
  +qk: T.QKind,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  el: {U32.is_eq(lf, 1) == True{} : Bool},
  eo: {D5.k3.scalar(D5.k3.hex.acc(un, hx)) == True{} : Bool}
) -> {M4.fs.st(bd, rw, hs, he, ps, Chr{D5.k3.hex.acc(un, hx)} <> buf, T.LStr{}, bk, qk, sk, 0, 0, ab)
  == T.read.fast(M4.fs.st(bd, rw, hs, he, ps, buf, T.LUni{}, bk, qk, sk, un, lf, ab), D5.k3.hex.char(hx)) : T.St}:
  %M8.k3.hx.ok(hx) : {M4.fs.st(bd, rw, hs, he, ps, Chr{D5.k3.hex.acc(un, hx)} <> buf, T.LStr{}, bk, qk, sk, 0, 0, ab)
    == T.read.once2(T.uni.go(_, M4.fs.st(bd, rw, hs, he, ps, buf, T.LUni{}, bk, qk, sk, un, lf, ab),
    D5.k3.hex.char(hx), T.LStr{}, un, lf)) : T.St}
  %M8.k3.hx.dv(hx) : {M4.fs.st(bd, rw, hs, he, ps, Chr{D5.k3.hex.acc(un, hx)} <> buf, T.LStr{}, bk, qk, sk, 0, 0, ab)
    == T.read.once2(T.uni.next(U32.is_eq(lf, 1), M4.fs.st(bd, rw, hs, he, ps, buf, T.LUni{}, bk, qk, sk, un, lf, ab),
    U32.add(U32.mul(un, 16), _), T.LStr{}, lf)) : T.St}
  %Equal.sym(Bool, U32.is_eq(lf, 1), True{}, el) : {M4.fs.st(bd, rw, hs, he, ps, Chr{D5.k3.hex.acc(un, hx)} <> buf,
    T.LStr{}, bk, qk, sk, 0, 0, ab) == T.read.once2(T.uni.next(_, M4.fs.st(bd, rw, hs, he, ps, buf, T.LUni{}, bk, qk,
        sk,
    un, lf, ab), D5.k3.hex.acc(un, hx), T.LStr{}, lf)) : T.St}
  %Equal.sym(Bool, T.uni.ok(D5.k3.hex.acc(un, hx)), True{}, eo) : {M4.fs.st(bd, rw, hs, he, ps,
    Chr{D5.k3.hex.acc(un, hx)} <> buf, T.LStr{}, bk, qk, sk, 0, 0, ab) == T.read.once2(T.uni.finish(_, M4.fs.st(bd,
    rw, hs, he, ps, buf, T.LUni{}, bk, qk, sk, un, lf, ab), D5.k3.hex.acc(un, hx), T.LStr{})) : T.St}
  {==}

# a digit that is not the last one, read from the text
def s1.hx.rmid(
  +hx: D5.KHex,
  +qk: T.QKind,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  el: {U32.is_eq(lf, 1) == False{} : Bool}
) -> {T.doc.read(rest, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LUni{}, bk, qk, sk, D5.k3.hex.acc(un, hx),
  U32.sub(lf, 1), ab)}) == T.doc.read(SCon{D5.k3.hex.char(hx), rest}, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf,
  T.LUni{}, bk, qk, sk, un, lf, ab)}) : T.Doc}:
  %M8.k3.hx.scan(hx, M4.fs.st(bd, rw, hs, he, ps, buf, T.LUni{}, bk, qk, sk, un, lf, ab)) : {T.doc.read(rest,
    T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LUni{}, bk, qk, sk, D5.k3.hex.acc(un, hx), U32.sub(lf, 1), ab)})
    == T.doc.read(rest, _) : T.Doc}
  %s1.hx.mid(hx, qk, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, el) : {T.doc.read(rest, T.MScan{M4.fs.st(bd, rw, hs,
    he, ps, buf, T.LUni{}, bk, qk, sk, D5.k3.hex.acc(un, hx), U32.sub(lf, 1), ab)}) == T.doc.read(rest, T.MScan{_})
    : T.Doc}
  {==}

# the last digit, read from the text
def s1.hx.rlast(
  +hx: D5.KHex,
  +qk: T.QKind,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  el: {U32.is_eq(lf, 1) == True{} : Bool},
  eo: {D5.k3.scalar(D5.k3.hex.acc(un, hx)) == True{} : Bool}
) -> {T.doc.read(rest, T.MScan{M4.fs.st(bd, rw, hs, he, ps, Chr{D5.k3.hex.acc(un, hx)} <> buf, T.LStr{}, bk, qk, sk,
  0, 0, ab)}) == T.doc.read(SCon{D5.k3.hex.char(hx), rest}, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LUni{}, bk,
  qk, sk, un, lf, ab)}) : T.Doc}:
  %M8.k3.hx.scan(hx, M4.fs.st(bd, rw, hs, he, ps, buf, T.LUni{}, bk, qk, sk, un, lf, ab)) : {T.doc.read(rest,
    T.MScan{M4.fs.st(bd, rw, hs, he, ps, Chr{D5.k3.hex.acc(un, hx)} <> buf, T.LStr{}, bk, qk, sk, 0, 0, ab)})
    == T.doc.read(rest, _) : T.Doc}
  %s1.hx.last(hx, qk, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, el, eo) : {T.doc.read(rest, T.MScan{M4.fs.st(bd, rw,
    hs, he, ps, Chr{D5.k3.hex.acc(un, hx)} <> buf, T.LStr{}, bk, qk, sk, 0, 0, ab)}) == T.doc.read(rest,
    T.MScan{_}) : T.Doc}
  {==}

# a backslash and u (U when lg) start an escape of four digits (eight),
# with back where it was
def s1.hx.open(
  +lg: Bool,
  +ml: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String
) -> {T.doc.read(rest, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LUni{}, bk, s1.bk(ml), sk, 0, M8.k3.hx.n(lg), ab)})
  == T.doc.read(SCon{'\\', SCon{M8.k3.hx.u(lg), rest}}, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, bk, s1.bk(ml),  # noqa: S002
  sk, un, lf, ab)}) : T.Doc}:
  match lg ml:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

# `\u` and four digits push the character they name, and leave back where it
# was and uni and left at 0
def s1.u4(
  +dd: D5.KHex,
  +cc: D5.KHex,
  +bb: D5.KHex,
  +aa: D5.KHex,
  +ml: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  eo: {D5.k3.scalar(D5.k3.hex4(dd, cc, bb, aa)) == True{} : Bool},
  ih: s1.Then(s1.bk(ml), bd, rw, hs, he, ps, sk, ab, Chr{D5.k3.hex4(dd, cc, bb, aa)} <> buf, rest, PP)
) -> PP(T.doc.read(D5.k3.pc.text(D5.KpU4{dd, cc, bb, aa}, rest), T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{},
  bk, s1.bk(ml), sk, un, lf, ab)})):
  +qk = {s1.bk(ml) : T.QKind}
  %s1.hx.open(False{}, ml, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, D5.k3.hex4.text(dd, cc, bb, aa, rest))
    : PP(_)
  %s1.hx.rmid(dd, qk, bd, rw, hs, he, ps, sk, ab, bk, 0, 4, buf, SCon{D5.k3.hex.char(cc),
    SCon{D5.k3.hex.char(bb), SCon{D5.k3.hex.char(aa), rest}}}, {==}) : PP(_)
  %s1.hx.rmid(cc, qk, bd, rw, hs, he, ps, sk, ab, bk, D5.k3.hex.acc(0, dd), 3, buf,
    SCon{D5.k3.hex.char(bb), SCon{D5.k3.hex.char(aa), rest}}, {==}) : PP(_)
  %s1.hx.rmid(bb, qk, bd, rw, hs, he, ps, sk, ab, bk, D5.k3.hex.acc(D5.k3.hex.acc(0, dd), cc), 2, buf,
    SCon{D5.k3.hex.char(aa), rest}, {==}) : PP(_)
  %s1.hx.rlast(aa, qk, bd, rw, hs, he, ps, sk, ab, bk, D5.k3.hex.acc(D5.k3.hex.acc(D5.k3.hex.acc(0, dd), cc),
    bb), 1, buf, rest, {==}, eo) : PP(_)
  ih(bk, 0, 0)

# the number eight digits write
def s1.h8(
  hh: D5.KHex,
  gg: D5.KHex,
  ff: D5.KHex,
  ee: D5.KHex,
  dd: D5.KHex,
  cc: D5.KHex,
  bb: D5.KHex,
  aa: D5.KHex
) -> U32:
  D5.k3.hex8(hh, gg, ff, ee, dd, cc, bb, aa)

# `\U` and eight digits push the character they name, and leave back where
# it was and uni and left at 0
def s1.u8(
  +hh: D5.KHex,
  +gg: D5.KHex,
  +ff: D5.KHex,
  +ee: D5.KHex,
  +dd: D5.KHex,
  +cc: D5.KHex,
  +bb: D5.KHex,
  +aa: D5.KHex,
  +ml: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  eo: {D5.k3.scalar(D5.k3.hex8(hh, gg, ff, ee, dd, cc, bb, aa)) == True{} : Bool},
  ih: s1.Then(s1.bk(ml), bd, rw, hs, he, ps, sk, ab, Chr{s1.h8(hh, gg, ff, ee, dd, cc, bb, aa)} <> buf, rest, PP)
) -> PP(T.doc.read(D5.k3.pc.text(D5.KpU8{hh, gg, ff, ee, dd, cc, bb, aa}, rest), T.MScan{M4.fs.st(bd, rw, hs, he, ps,
  buf, T.LStr{}, bk, s1.bk(ml), sk, un, lf, ab)})):
  +qk = {s1.bk(ml) : T.QKind}
  +t4 = D5.k3.hex4.text(dd, cc, bb, aa, rest)
  +a1 = D5.k3.hex.acc(0, hh)
  +a2 = D5.k3.hex.acc(a1, gg)
  +a3 = D5.k3.hex.acc(a2, ff)
  +a4 = D5.k3.hex.acc(a3, ee)
  +a5 = D5.k3.hex.acc(a4, dd)
  +a6 = D5.k3.hex.acc(a5, cc)
  +a7 = D5.k3.hex.acc(a6, bb)
  %s1.hx.open(True{}, ml, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, D5.k3.hex4.text(hh, gg, ff, ee, t4)) : PP(_)
  %s1.hx.rmid(hh, qk, bd, rw, hs, he, ps, sk, ab, bk, 0, 8, buf, SCon{D5.k3.hex.char(gg), SCon{D5.k3.hex.char(ff),
    SCon{D5.k3.hex.char(ee), t4}}}, {==}) : PP(_)
  %s1.hx.rmid(gg, qk, bd, rw, hs, he, ps, sk, ab, bk, a1, 7, buf, SCon{D5.k3.hex.char(ff), SCon{D5.k3.hex.char(ee),
    t4}}, {==}) : PP(_)
  %s1.hx.rmid(ff, qk, bd, rw, hs, he, ps, sk, ab, bk, a2, 6, buf, SCon{D5.k3.hex.char(ee), t4}, {==}) : PP(_)
  %s1.hx.rmid(ee, qk, bd, rw, hs, he, ps, sk, ab, bk, a3, 5, buf, t4, {==}) : PP(_)
  %s1.hx.rmid(dd, qk, bd, rw, hs, he, ps, sk, ab, bk, a4, 4, buf, SCon{D5.k3.hex.char(cc),
    SCon{D5.k3.hex.char(bb), SCon{D5.k3.hex.char(aa), rest}}}, {==}) : PP(_)
  %s1.hx.rmid(cc, qk, bd, rw, hs, he, ps, sk, ab, bk, a5, 3, buf, SCon{D5.k3.hex.char(bb), SCon{D5.k3.hex.char(aa),
    rest}}, {==}) : PP(_)
  %s1.hx.rmid(bb, qk, bd, rw, hs, he, ps, sk, ab, bk, a6, 2, buf, SCon{D5.k3.hex.char(aa), rest}, {==}) : PP(_)
  %s1.hx.rlast(aa, qk, bd, rw, hs, he, ps, sk, ab, bk, a7, 1, buf, rest, {==}, eo) : PP(_)
  ih(bk, 0, 0)

# one piece a basic string may hold pushes the character it stands for
def s1.pc(
  pp: D5.KPiece,
  +ml: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  hc: {D1.abnf.basic_char(pp) == True{} : Bool},
  eo: {D1.prose.escape_scalar(pp) == True{} : Bool},
  ih: s1.Then(s1.bk(ml), bd, rw, hs, he, ps, sk, ab, D5.k3.pc.char(pp) <> buf, rest, PP)
) -> PP(T.doc.read(D5.k3.pc.text(pp, rest), T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, bk, s1.bk(ml), sk, un,
  lf, ab)})):
  match pp:
    case D5.KpChar{cc}:
      match cc:
        case Chr{+uu}:
          s1.chr(ml, uu, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP, hc, ih)
    case D5.KpEsc{mm}:
      s1.esc(mm, ml, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP, ih)
    case D5.KpU4{+dd, +cc, +bb, +aa}:
      s1.u4(dd, cc, bb, aa, ml, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP, eo, ih)
    case D5.KpU8{+hh, +gg, +ff, +ee, +dd, +cc, +bb, +aa}:
      s1.u8(hh, gg, ff, ee, dd, cc, bb, aa, ml, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP, eo, ih)

# every piece of a list a basic string may hold, in order: the rest is read
# with their characters pushed, from wherever the last piece left back, uni
# and left
def s1.pcs(
  pl: List<&2, D5.KPiece>,
  +ml: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  +hc: {D1.abnf.basic_string(pl) == True{} : Bool},
  +eo: {D1.prose.escapes_scalar(pl) == True{} : Bool},
  ih: s1.Then(s1.bk(ml), bd, rw, hs, he, ps, sk, ab, M3.rev.onto(D5.k3.pcs.name(pl), buf), rest, PP)
) -> PP(T.doc.read(D5.k3.pcs.text(pl, rest), T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, bk, s1.bk(ml), sk,
  un, lf, ab)})):
  match pl:
    case []:
      ih(bk, un, lf)
    case +pp <> +pr:
      s1.pc(pp, ml, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, D5.k3.pcs.text(pr, rest), PP,
        Eq.and.left(D1.abnf.basic_char(pp), D1.abnf.basic_string(pr), hc),
        Eq.and.left(D1.prose.escape_scalar(pp), D1.prose.escapes_scalar(pr), eo),
        +b2 => +u2 => +l2 => s1.pcs(pr, ml, bd, rw, hs, he, ps, sk, ab, b2, u2, l2, D5.k3.pc.char(pp) <> buf, rest,
          PP, Eq.and.right(D1.abnf.basic_char(pp), D1.abnf.basic_string(pr), hc),
          Eq.and.right(D1.prose.escape_scalar(pp), D1.prose.escapes_scalar(pr), eo), ih))

# The rest of the walk once a string is read. A string of every form places
# a value holding its characters (sv.Is) by take.top; the kind it leaves in
# qkind is its own, so s1.Done takes it as a parameter too, as WP-C's vrest
# does, and WP-S's sv.Then is s1.Done at a basic string's kind.

# the rest of the walk for the string ss: reading rest from the scanner with
# any string value holding ss placed, and any back, kind, uni and left, gives
# a document PP holds of
def s1.Done(
  +ss: String,
  +bd: String,
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
    M8.sv.Is(vv, ss) ->
    PP(T.doc.read(rest, T.MScan{T.take.top(sk, vv, bd, rw, hs, he, ps, bk, qk, un, lf, ab, False{})}))

# WP-S's rest of the walk is s1.Done at a basic string's kind
def s1.done.sv(
  +ss: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  dn: s1.Done(ss, bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> M8.sv.Then(ss, bd, rw, hs, he, ps, sk, ab, rest, PP):
  vv => bk => un => lf => hv => dn(vv, bk, T.QBasic{}, un, lf, hv)

# the rest of the walk for one string serves for another equal to it
def s1.done.cast(
  +s1: String,
  +s2: String,
  e12: {s1 == s2 : String},
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  ih: s1.Done(s1, bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> s1.Done(s2, bd, rw, hs, he, ps, sk, ab, rest, PP):
  %e12 : s1.Done(_, bd, rw, hs, he, ps, sk, ab, rest, PP)
  ih

# Texts that may follow a string. Laws.s1.free leaves out a quotation mark
# and an apostrophe first.

# a pair of bits whose or is false: the first is false
def s1.nor.l(
  aa: Bool,
  bb: Bool,
  hh: {Bool.not(Bool.or(aa, bb)) == True{} : Bool}
) -> {aa == False{} : Bool}:
  match aa:
    case True{}:
      Eq.bit.absurd(&2, {True{} == False{} : Bool}, hh)
    case False{}:
      {==}

# and so is the second
def s1.nor.r(
  aa: Bool,
  bb: Bool,
  hh: {Bool.not(Bool.or(aa, bb)) == True{} : Bool}
) -> {bb == False{} : Bool}:
  match aa:
    case True{}:
      Eq.bit.absurd(&2, {bb == False{} : Bool}, hh)
    case False{}:
      Eq.not.true(bb, hh)

# a text that may follow a string does not start with a quotation mark
def s1.free.sv(
  rest: String,
  hr: {L1.s1.free(rest) == True{} : Bool}
) -> {M8.sv.free(rest) == True{} : Bool}:
  match rest:
    case SNil{}:
      {==}
    case SCon{hh, _tt}:
      match hh:
        case Chr{+uu}:
          Equal.cong(Bool, Bool, xx => Bool.not(xx), U32.is_eq(uu, 34), False{},
            s1.nor.l(U32.is_eq(uu, 34), U32.is_eq(uu, 39), hr))

# One-line basic strings. A character written as itself opens WP-S's span
# or grows it; a tab among them, since str.bad passes it. An escape meets a
# backslash, which copies the span into the buffer, and the pieces from it
# on are read in LStr by s1.pcs.

# the first character: str.bad passes it, so the span starts
def s1.so.ok(
  badc: Bool,
  +uu: U32,
  +tail: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  hc: {badc == False{} : Bool}
) -> {T.doc.open.ok(badc, True{}, '"', T.QBasic{}, bd, rw, hs, he, ps, [], bk, sk, un, lf, ab, Chr{uu}, tail)
  == M8.sv.eat(SCon{Chr{uu}, tail}, 1, bd, rw, hs, he, ps, sk, un, lf, ab) : T.Mode}:
  match badc:
    case False{}:
      {==}
    case True{}:
      Eq.bit.absurd2(&2, {T.doc.open.ok(True{}, True{}, '"', T.QBasic{}, bd, rw, hs, he, ps, [], bk, sk, un, lf, ab,
        Chr{uu}, tail) == M8.sv.eat(SCon{Chr{uu}, tail}, 1, bd, rw, hs, he, ps, sk, un, lf, ab) : T.Mode}, hc)

# no backslash
def s1.so.bs(
  bs: Bool,
  +uu: U32,
  +tail: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  hb: {bs == False{} : Bool},
  sb: {T.str.bad(uu, False{}) == False{} : Bool}
) -> {T.doc.open.bs(bs, '"', T.QBasic{}, bd, rw, hs, he, ps, [], bk, sk, un, lf, ab, Chr{uu}, tail)
  == M8.sv.eat(SCon{Chr{uu}, tail}, 1, bd, rw, hs, he, ps, sk, un, lf, ab) : T.Mode}:
  match bs:
    case False{}:
      s1.so.ok(T.str.bad(uu, False{}), uu, tail, bd, rw, hs, he, ps, bk, sk, un, lf, ab, sb)
    case True{}:
      Eq.bit.absurd2(&2, {T.doc.open.bs(True{}, '"', T.QBasic{}, bd, rw, hs, he, ps, [], bk, sk, un, lf, ab, Chr{uu},
        tail) == M8.sv.eat(SCon{Chr{uu}, tail}, 1, bd, rw, hs, he, ps, sk, un, lf, ab) : T.Mode}, hb)

# no quotation mark
def s1.so.q(
  same: Bool,
  +uu: U32,
  +tail: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  hq: {same == False{} : Bool},
  hb: {U32.is_eq(uu, 92) == False{} : Bool},
  sb: {T.str.bad(uu, False{}) == False{} : Bool}
) -> {T.doc.open.q(same, True{}, '"', T.QBasic{}, bd, rw, hs, he, ps, [], bk, sk, un, lf, ab, Chr{uu}, tail)
  == M8.sv.eat(SCon{Chr{uu}, tail}, 1, bd, rw, hs, he, ps, sk, un, lf, ab) : T.Mode}:
  match same:
    case False{}:
      s1.so.bs(U32.is_eq(uu, 92), uu, tail, bd, rw, hs, he, ps, bk, sk, un, lf, ab, hb, sb)
    case True{}:
      Eq.bit.absurd2(&2, {T.doc.open.q(True{}, True{}, '"', T.QBasic{}, bd, rw, hs, he, ps, [], bk, sk, un, lf, ab,
        Chr{uu}, tail) == M8.sv.eat(SCon{Chr{uu}, tail}, 1, bd, rw, hs, he, ps, sk, un, lf, ab) : T.Mode}, hq)

# a first character that is no quotation mark and no backslash, and that
# str.bad passes, opens the span
def s1.so.one(
  +uu: U32,
  +tail: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  e34: {U32.is_eq(uu, 34) == False{} : Bool},
  e92: {U32.is_eq(uu, 92) == False{} : Bool},
  sb: {T.str.bad(uu, False{}) == False{} : Bool}
) -> {T.doc.read(SCon{Chr{uu}, tail}, M8.sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab))
  == T.doc.read(tail, M8.sv.eat(SCon{Chr{uu}, tail}, 1, bd, rw, hs, he, ps, sk, un, lf, ab)) : T.Doc}:
  Equal.cong(T.Mode, T.Doc, md => T.doc.read(tail, md),
    T.doc.open(True{}, '"', T.QBasic{}, bd, rw, hs, he, ps, [], bk, sk, un, lf, ab, Chr{uu}, tail),
    M8.sv.eat(SCon{Chr{uu}, tail}, 1, bd, rw, hs, he, ps, sk, un, lf, ab),
    s1.so.q(U32.is_eq(uu, 34), uu, tail, bd, rw, hs, he, ps, bk, sk, un, lf, ab, e34, e92, sb))

# a later character: str.bad passes it, so the span grows
def s1.se.ctl(
  badc: Bool,
  +uu: U32,
  +cut: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  hc: {badc == False{} : Bool}
) -> {T.eat.ctrl(badc, True{}, '"', Chr{uu}, cut, nn, bd, rw, hs, he, ps, T.QBasic{}, sk, un, lf, ab)
  == M8.sv.eat(cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un, lf, ab) : T.Mode}:
  match badc:
    case False{}:
      {==}
    case True{}:
      Eq.bit.absurd2(&2, {T.eat.ctrl(True{}, True{}, '"', Chr{uu}, cut, nn, bd, rw, hs, he, ps, T.QBasic{}, sk, un, lf,
        ab) == M8.sv.eat(cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un, lf, ab) : T.Mode}, hc)

# no backslash
def s1.se.bs(
  bs: Bool,
  +uu: U32,
  +cut: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  hb: {bs == False{} : Bool},
  sb: {T.str.bad(uu, False{}) == False{} : Bool}
) -> {T.eat.bs(bs, True{}, '"', Chr{uu}, cut, nn, bd, rw, hs, he, ps, T.QBasic{}, sk, un, lf, ab)
  == M8.sv.eat(cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un, lf, ab) : T.Mode}:
  match bs:
    case False{}:
      s1.se.ctl(T.str.bad(uu, False{}), uu, cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab, sb)
    case True{}:
      Eq.bit.absurd2(&2, {T.eat.bs(True{}, True{}, '"', Chr{uu}, cut, nn, bd, rw, hs, he, ps, T.QBasic{}, sk, un, lf,
        ab) == M8.sv.eat(cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un, lf, ab) : T.Mode}, hb)

# no quotation mark
def s1.se.q(
  quote: Bool,
  +uu: U32,
  +cut: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  hq: {quote == False{} : Bool},
  hb: {U32.is_eq(uu, 92) == False{} : Bool},
  sb: {T.str.bad(uu, False{}) == False{} : Bool}
) -> {T.eat.feed.q(quote, True{}, '"', Chr{uu}, cut, nn, bd, rw, hs, he, ps, T.QBasic{}, sk, un, lf, ab)
  == M8.sv.eat(cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un, lf, ab) : T.Mode}:
  match quote:
    case False{}:
      s1.se.bs(U32.is_eq(uu, 92), uu, cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab, hb, sb)
    case True{}:
      Eq.bit.absurd2(&2, {T.eat.feed.q(True{}, True{}, '"', Chr{uu}, cut, nn, bd, rw, hs, he, ps, T.QBasic{}, sk, un,
        lf, ab) == M8.sv.eat(cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un, lf, ab) : T.Mode}, hq)

# a later character that is no quotation mark and no backslash, and that
# str.bad passes, grows the span by one
def s1.se.one(
  +uu: U32,
  +tail: String,
  +cut: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  e34: {U32.is_eq(uu, 34) == False{} : Bool},
  e92: {U32.is_eq(uu, 92) == False{} : Bool},
  sb: {T.str.bad(uu, False{}) == False{} : Bool}
) -> {T.doc.read(SCon{Chr{uu}, tail}, M8.sv.eat(cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab))
  == T.doc.read(tail, M8.sv.eat(cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un, lf, ab)) : T.Doc}:
  Equal.cong(T.Mode, T.Doc, md => T.doc.read(tail, md),
    T.eat.feed(True{}, '"', cut, nn, bd, rw, hs, he, ps, T.QBasic{}, sk, un, lf, ab, Chr{uu}),
    M8.sv.eat(cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un, lf, ab),
    s1.se.q(U32.is_eq(uu, 34), uu, cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab, e34, e92, sb))

# the span's count after one more character is the characters of pre and it,
# when the count does not wrap
def s1.hn(
  +nn: U32,
  +pre: String,
  +cc: Char,
  +tl: String,
  hn: {U32.to_nat(nn) == M7.plus(pre, 0n) : Nat},
  hk: {D3.counts(SCon{cc, tl}, nn) == True{} : Bool}
) -> {U32.to_nat(U32.add(nn, 1)) == M7.plus(String.append(pre, SCon{cc, SNil{}}), 0n) : Nat}:
  Equal.trans(Nat, U32.to_nat(U32.add(nn, 1)), 1n+U32.to_nat(nn), M7.plus(String.append(pre, SCon{cc, SNil{}}), 0n),
    Eq.inc.nat(nn, Eq.not.true(U32.is_zero(U32.add(nn, 1)), Eq.and.left(Bool.not(U32.is_zero(U32.add(nn, 1))),
      D3.counts(tl, U32.add(nn, 1)), hk))),
    Equal.trans(Nat, 1n+U32.to_nat(nn), 1n+M7.plus(pre, 0n), M7.plus(String.append(pre, SCon{cc, SNil{}}), 0n),
      Equal.cong(Nat, Nat, kk => 1n+kk, U32.to_nat(nn), M7.plus(pre, 0n), hn),
      Equal.sym(Nat, M7.plus(String.append(pre, SCon{cc, SNil{}}), 0n), 1n+M7.plus(pre, 0n),
        M8.plus.app(pre, SCon{cc, SNil{}}, 0n))))

# the text from pre, then a character and the rest: pre grows by it
def s1.cut(
  +cut: String,
  +pre: String,
  +cc: Char,
  +xx: String,
  hc: {cut == String.append(pre, SCon{cc, xx}) : String}
) -> {cut == String.append(String.append(pre, SCon{cc, SNil{}}), xx) : String}:
  Equal.trans(String, cut, String.append(pre, SCon{cc, xx}), String.append(String.append(pre, SCon{cc, SNil{}}), xx),
    hc, Equal.sym(String, String.append(String.append(pre, SCon{cc, SNil{}}), xx), String.append(pre, SCon{cc, xx}),
    Eq.append_assoc(pre, SCon{cc, SNil{}}, xx)))

# the placement after the copied pieces: the closing quote places the owned
# string, with back where the pieces left it
def s1.close.b(
  +rest: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>
) -> {T.doc.read(SCon{'"', rest}, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, bk, T.QBasic{}, sk, un, lf, ab)})
  == T.doc.read(rest, T.MScan{M8.sv.took(sk, T.VStr{T.buf.str(buf)}, bd, rw, hs, he, ps, bk, un, lf, ab)}) : T.Doc}:
  Equal.cong(T.Mode, T.Doc, md => T.doc.read(rest, md),
    T.doc.wrap(T.read.once2(M8.sv.took(sk, T.VStr{T.buf.str(buf)}, bd, rw, hs, he, ps, bk, un, lf, ab))),
    T.MScan{M8.sv.took(sk, T.VStr{T.buf.str(buf)}, bd, rw, hs, he, ps, bk, un, lf, ab)},
    M8.tk.fix(sk, T.VStr{T.buf.str(buf)}, bd, rw, hs, he, ps, bk, T.QBasic{}, un, lf, ab, False{}))

# the pieces from a copied span on, then the closing quote: read from a
# buffer holding pre, they place an owned string of pre and their characters
def s1.cp(
  +pl: List<&2, D5.KPiece>,
  +pre: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +un: U32,
  +lf: U32,
  +rest: String,
  -PP: T.Doc -> Type,
  hc: {D1.abnf.basic_string(pl) == True{} : Bool},
  eo: {D1.prose.escapes_scalar(pl) == True{} : Bool},
  ih: M8.sv.Then(String.append(pre, D5.k3.pcs.name(pl)), bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(D5.k3.pcs.text(pl, SCon{'"', rest}), T.MScan{M4.fs.st(bd, rw, hs, he, ps, M3.rev.onto(pre, []),
  T.LStr{}, T.LStr{}, T.QBasic{}, sk, un, lf, ab)})):
  s1.pcs(pl, False{}, bd, rw, hs, he, ps, sk, ab, T.LStr{}, un, lf, M3.rev.onto(pre, []), SCon{'"', rest}, PP, hc, eo,
    +b2 => +u2 => +l2 => M8.pp.step(PP,
      T.doc.read(SCon{'"', rest}, T.MScan{M4.fs.st(bd, rw, hs, he, ps, M3.rev.onto(D5.k3.pcs.name(pl), M3.rev.onto(pre,
          [])),
        T.LStr{}, b2, T.QBasic{}, sk, u2, l2, ab)}),
      T.doc.read(rest, T.MScan{M8.sv.took(sk, T.VStr{T.buf.str(M3.rev.onto(D5.k3.pcs.name(pl), M3.rev.onto(pre, [])))},
          bd,
        rw, hs, he, ps, b2, u2, l2, ab)}),
      s1.close.b(rest, bd, rw, hs, he, ps, sk, ab, b2, u2, l2, M3.rev.onto(D5.k3.pcs.name(pl), M3.rev.onto(pre, []))),
      ih(T.VStr{T.buf.str(M3.rev.onto(D5.k3.pcs.name(pl), M3.rev.onto(pre, [])))}, b2, u2, l2,
        M8.ls.own(pre, D5.k3.pcs.name(pl)))))

# the span meets a backslash where the pieces start: it copies itself
def s1.SgEq(
  +pl: List<&2, D5.KPiece>,
  +cut: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String
) -> Type:
  {T.doc.read(D5.k3.pcs.text(pl, SCon{'"', rest}), M8.sv.eat(cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab))
    == T.doc.read(D5.k3.pcs.text(pl, SCon{'"', rest}), T.MScan{M5.ls(bd, rw, hs, he, ps, sk, ab, un, lf,
    T.span.rev(cut, nn, U32.is_zero(nn), []))}) : T.Doc}

# an escape inside the span: the backslash copies the span, which holds pre,
# and the pieces from the escape on are read in LStr
def s1.sg.cp(
  +pl: List<&2, D5.KPiece>,
  +pre: String,
  +cut: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  eq: s1.SgEq(pl, cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab, rest),
  hc: {cut == String.append(pre, D5.k3.pcs.text(pl, SCon{'"', rest})) : String},
  hn: {U32.to_nat(nn) == M7.plus(pre, 0n) : Nat},
  hb: {D1.abnf.basic_string(pl) == True{} : Bool},
  eo: {D1.prose.escapes_scalar(pl) == True{} : Bool},
  ih: M8.sv.Then(String.append(pre, D5.k3.pcs.name(pl)), bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(D5.k3.pcs.text(pl, SCon{'"', rest}), M8.sv.eat(cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab))):
  M8.pp.step(PP,
    T.doc.read(D5.k3.pcs.text(pl, SCon{'"', rest}), M8.sv.eat(cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab)),
    T.doc.read(D5.k3.pcs.text(pl, SCon{'"', rest}), T.MScan{M5.ls(bd, rw, hs, he, ps, sk, ab, un, lf,
      T.span.rev(cut, nn, U32.is_zero(nn), []))}),
    eq,
    M8.pp.step(PP,
      T.doc.read(D5.k3.pcs.text(pl, SCon{'"', rest}), T.MScan{M5.ls(bd, rw, hs, he, ps, sk, ab, un, lf,
        T.span.rev(cut, nn, U32.is_zero(nn), []))}),
      T.doc.read(D5.k3.pcs.text(pl, SCon{'"', rest}), T.MScan{M5.ls(bd, rw, hs, he, ps, sk, ab, un, lf,
        M3.rev.onto(pre, []))}),
      Equal.cong(List<&2, Char>, T.Doc, bb => T.doc.read(D5.k3.pcs.text(pl, SCon{'"', rest}), T.MScan{M5.ls(bd, rw, hs,
        he, ps, sk, ab, un, lf, bb)}), T.span.rev(cut, nn, U32.is_zero(nn), []), M3.rev.onto(pre, []),
        M8.se.rev(pre, cut, D5.k3.pcs.text(pl, SCon{'"', rest}), nn, hc, hn)),
      s1.cp(pl, pre, bd, rw, hs, he, ps, sk, ab, un, lf, rest, PP, hb, eo, ih)))

# the rest pl of a string inside its span, pre read so far: cut is the text
# from the string's first character, and nn counts pre's characters without
# wrapping. The string reads to a value holding pre and the characters pl
# stands for: the span itself when pl holds no escape, and the copied string
# otherwise
def s1.sg(
  pl: List<&2, D5.KPiece>,
  +pre: String,
  +cut: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  +hc: {cut == String.append(pre, D5.k3.pcs.text(pl, SCon{'"', rest})) : String},
  +hn: {U32.to_nat(nn) == M7.plus(pre, 0n) : Nat},
  +hk: {D3.counts(D5.k3.pcs.name(pl), nn) == True{} : Bool},
  +hb: {D1.abnf.basic_string(pl) == True{} : Bool},
  +eo: {D1.prose.escapes_scalar(pl) == True{} : Bool},
  ih: M8.sv.Then(String.append(pre, D5.k3.pcs.name(pl)), bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(D5.k3.pcs.text(pl, SCon{'"', rest}), M8.sv.eat(cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab))):
  match pl:
    case []:
      M8.pp.step(PP,
        T.doc.read(SCon{'"', rest}, M8.sv.eat(cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab)),
        T.doc.read(rest, T.MScan{M8.sv.took(sk, T.VSpan{cut, nn}, bd, rw, hs, he, ps, T.LStr{}, un, lf, ab)}),
        M8.se.close(rest, cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab),
        M8.sv.then.cast(String.append(pre, SNil{}), pre, Eq.append_nil(pre), bd, rw, hs, he, ps, sk, ab, rest, PP, ih)(
          T.VSpan{cut, nn}, T.LStr{}, un, lf, M8.se.own(pre, cut, SCon{'"', rest}, nn, hc, hn)))
    case +kp <> +pr:
      match kp:
        case D5.KpChar{cc}:
          match cc:
            case Chr{+uu}:
              +tx = {D5.k3.pcs.text(pr, SCon{'"', rest}) : String}
              +hb0 = {Eq.and.left(D1.abnf.basic_unescaped(Chr{uu}), D1.abnf.basic_string(pr), hb)
                : {D1.abnf.basic_unescaped(Chr{uu}) == True{} : Bool}}
              +c9 = {M1.s1.bu.c9(uu, hb0) : {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == U32.is_eq(uu, 9) : Bool}}
              M8.pp.step(PP,
                T.doc.read(SCon{Chr{uu}, tx}, M8.sv.eat(cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab)),
                T.doc.read(tx, M8.sv.eat(cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un, lf, ab)),
                s1.se.one(uu, tx, cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab, M1.s1.bu.q(uu, hb0), M1.s1.bu.b(uu, hb0),
                  s1.sb(uu, False{}, c9)),
                s1.sg(pr, String.append(pre, SCon{Chr{uu}, SNil{}}), cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un,
                  lf, ab, rest, PP, s1.cut(cut, pre, Chr{uu}, tx, hc),
                  s1.hn(nn, pre, Chr{uu}, D5.k3.pcs.name(pr), hn, hk),
                  Eq.and.right(Bool.not(U32.is_zero(U32.add(nn, 1))), D3.counts(D5.k3.pcs.name(pr), U32.add(nn, 1)),
                    hk),
                  Eq.and.right(D1.abnf.basic_unescaped(Chr{uu}), D1.abnf.basic_string(pr), hb),
                  Eq.and.right(True{}, D1.prose.escapes_scalar(pr), eo),
                  M8.sv.then.cast(String.append(pre, SCon{Chr{uu}, D5.k3.pcs.name(pr)}),
                    String.append(String.append(pre, SCon{Chr{uu}, SNil{}}), D5.k3.pcs.name(pr)),
                    Equal.sym(String, String.append(String.append(pre, SCon{Chr{uu}, SNil{}}), D5.k3.pcs.name(pr)),
                      String.append(pre, SCon{Chr{uu}, D5.k3.pcs.name(pr)}),
                      Eq.append_assoc(pre, SCon{Chr{uu}, SNil{}}, D5.k3.pcs.name(pr))),
                    bd, rw, hs, he, ps, sk, ab, rest, PP, ih)))
        case D5.KpEsc{mm}:
          s1.sg.cp(D5.KpEsc{mm} <> pr, pre, cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab, rest, PP,
            M8.se.copy(SCon{D5.k3.mark.char(mm), D5.k3.pcs.text(pr, SCon{'"', rest})}, cut, nn, bd, rw, hs, he, ps,
              sk, un, lf, ab), hc, hn, hb, eo, ih)
        case D5.KpU4{+dd, +cc, +bb, +aa}:
          s1.sg.cp(D5.KpU4{dd, cc, bb, aa} <> pr, pre, cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab, rest, PP,
            M8.se.copy(SCon{'u', D5.k3.hex4.text(dd, cc, bb, aa, D5.k3.pcs.text(pr, SCon{'"', rest}))}, cut, nn, bd,
              rw, hs, he, ps, sk, un, lf, ab), hc, hn, hb, eo, ih)
        case D5.KpU8{+hh, +gg, +ff, +ee, +dd, +cc, +bb, +aa}:
          s1.sg.cp(D5.KpU8{hh, gg, ff, ee, dd, cc, bb, aa} <> pr, pre, cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab,
            rest, PP, M8.se.copy(SCon{'U', D5.k3.hex4.text(hh, gg, ff, ee, D5.k3.hex4.text(dd, cc, bb, aa,
              D5.k3.pcs.text(pr, SCon{'"', rest})))}, cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab), hc, hn, hb, eo,
            ih)

# a one-line basic string of pieces, after its opening quote, then the
# closing quote and a rest that does not start with a quote: from every
# value position the rest is read with a value holding the pieces'
# characters placed
def s1.bo(
  pl: List<&2, D5.KPiece>,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  +hk: {D3.short(D5.k3.pcs.name(pl)) == True{} : Bool},
  +hb: {D1.abnf.basic_string(pl) == True{} : Bool},
  +eo: {D1.prose.escapes_scalar(pl) == True{} : Bool},
  hr: {M8.sv.free(rest) == True{} : Bool},
  ih: M8.sv.Then(D5.k3.pcs.name(pl), bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(D5.k3.pcs.text(pl, SCon{'"', rest}), M8.sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab))):
  match pl:
    case []:
      M8.sv.empty(bd, rw, hs, he, ps, bk, sk, un, lf, ab, rest, PP, hr, ih)
    case +kp <> +pr:
      match kp:
        case D5.KpChar{cc}:
          match cc:
            case Chr{+uu}:
              +tx = {D5.k3.pcs.text(pr, SCon{'"', rest}) : String}
              +hb0 = {Eq.and.left(D1.abnf.basic_unescaped(Chr{uu}), D1.abnf.basic_string(pr), hb)
                : {D1.abnf.basic_unescaped(Chr{uu}) == True{} : Bool}}
              +c9 = {M1.s1.bu.c9(uu, hb0) : {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == U32.is_eq(uu, 9) : Bool}}
              M8.pp.step(PP,
                T.doc.read(SCon{Chr{uu}, tx}, M8.sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab)),
                T.doc.read(tx, M8.sv.eat(SCon{Chr{uu}, tx}, 1, bd, rw, hs, he, ps, sk, un, lf, ab)),
                s1.so.one(uu, tx, bd, rw, hs, he, ps, bk, sk, un, lf, ab, M1.s1.bu.q(uu, hb0), M1.s1.bu.b(uu, hb0),
                  s1.sb(uu, False{}, c9)),
                s1.sg(pr, SCon{Chr{uu}, SNil{}}, SCon{Chr{uu}, tx}, 1, bd, rw, hs, he, ps, sk, un, lf, ab, rest, PP,
                  {==}, {==},
                  Eq.and.right(Bool.not(U32.is_zero(U32.add(0, 1))), D3.counts(D5.k3.pcs.name(pr), U32.add(0, 1)),
                    hk),
                  Eq.and.right(D1.abnf.basic_unescaped(Chr{uu}), D1.abnf.basic_string(pr), hb),
                  Eq.and.right(True{}, D1.prose.escapes_scalar(pr), eo), ih))
        case D5.KpEsc{mm}:
          M8.pp.step(PP,
            T.doc.read(SCon{'\\', SCon{D5.k3.mark.char(mm), D5.k3.pcs.text(pr, SCon{'"', rest})}},
              M8.sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab)),
            T.doc.read(SCon{'\\', SCon{D5.k3.mark.char(mm), D5.k3.pcs.text(pr, SCon{'"', rest})}},
              T.MScan{M5.ls(bd, rw, hs, he, ps, sk, ab, un, lf, [])}),
            M8.so.copy(SCon{D5.k3.mark.char(mm), D5.k3.pcs.text(pr, SCon{'"', rest})}, bd, rw, hs, he, ps, bk, sk, un,
              lf, ab),
            s1.cp(D5.KpEsc{mm} <> pr, SNil{}, bd, rw, hs, he, ps, sk, ab, un, lf, rest, PP, hb, eo, ih))
        case D5.KpU4{+dd, +cc, +bb, +aa}:
          +xx = {SCon{'u', D5.k3.hex4.text(dd, cc, bb, aa, D5.k3.pcs.text(pr, SCon{'"', rest}))} : String}
          M8.pp.step(PP,
            T.doc.read(SCon{'\\', xx}, M8.sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab)),
            T.doc.read(SCon{'\\', xx}, T.MScan{M5.ls(bd, rw, hs, he, ps, sk, ab, un, lf, [])}),
            M8.so.copy(xx, bd, rw, hs, he, ps, bk, sk, un, lf, ab),
            s1.cp(D5.KpU4{dd, cc, bb, aa} <> pr, SNil{}, bd, rw, hs, he, ps, sk, ab, un, lf, rest, PP, hb, eo, ih))
        case D5.KpU8{+hh, +gg, +ff, +ee, +dd, +cc, +bb, +aa}:
          +xx = {SCon{'U', D5.k3.hex4.text(hh, gg, ff, ee, D5.k3.hex4.text(dd, cc, bb, aa,
            D5.k3.pcs.text(pr, SCon{'"', rest})))} : String}
          M8.pp.step(PP,
            T.doc.read(SCon{'\\', xx}, M8.sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab)),
            T.doc.read(SCon{'\\', xx}, T.MScan{M5.ls(bd, rw, hs, he, ps, sk, ab, un, lf, [])}),
            M8.so.copy(xx, bd, rw, hs, he, ps, bk, sk, un, lf, ab),
            s1.cp(D5.KpU8{hh, gg, ff, ee, dd, cc, bb, aa} <> pr, SNil{}, bd, rw, hs, he, ps, sk, ab, un, lf, rest, PP,
              hb, eo, ih))

# One-line literal strings. literal-char leaves out every control but tab
# and the apostrophe, so every character of a literal string opens or grows
# its span (MEat with basic false and the apostrophe as the quote), and the
# closing apostrophe places the span: a literal string is always a span.
# `''` goes through LQ2 as `""` does.

# the scanner just past the opening apostrophe of a literal string in a
# value position
def s1.lo(
  bd: String,
  rw: List<&2, T.Val>,
  hs: List<&2, String>,
  he: List<&2, String>,
  ps: List<&2, String>,
  bk: T.Lex,
  sk: List<&2, T.Ctx>,
  un: U32,
  lf: U32,
  ab: Bool
) -> T.Mode:
  T.MOpen{False{}, '\'', T.QLit{}, bd, rw, hs, he, ps, [], bk, sk, un, lf, ab}

# the scanner inside the span of such a string: cut is the text from its
# first character, nn the characters counted so far
def s1.le(
  cut: String,
  nn: U32,
  bd: String,
  rw: List<&2, T.Val>,
  hs: List<&2, String>,
  he: List<&2, String>,
  ps: List<&2, String>,
  sk: List<&2, T.Ctx>,
  un: U32,
  lf: U32,
  ab: Bool
) -> T.Mode:
  T.MEat{False{}, '\'', cut, nn, bd, rw, hs, he, ps, T.QLit{}, sk, un, lf, ab}

# the first character: str.bad passes it, so the span starts
def s1.lo.ok(
  badc: Bool,
  +uu: U32,
  +tail: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  hc: {badc == False{} : Bool}
) -> {T.doc.open.ok(badc, False{}, '\'', T.QLit{}, bd, rw, hs, he, ps, [], bk, sk, un, lf, ab, Chr{uu}, tail)
  == s1.le(SCon{Chr{uu}, tail}, 1, bd, rw, hs, he, ps, sk, un, lf, ab) : T.Mode}:
  match badc:
    case False{}:
      {==}
    case True{}:
      Eq.bit.absurd2(&2, {T.doc.open.ok(True{}, False{}, '\'', T.QLit{}, bd, rw, hs, he, ps, [], bk, sk, un, lf, ab,
        Chr{uu}, tail) == s1.le(SCon{Chr{uu}, tail}, 1, bd, rw, hs, he, ps, sk, un, lf, ab) : T.Mode}, hc)

# no apostrophe
def s1.lo.q(
  same: Bool,
  +uu: U32,
  +tail: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  hq: {same == False{} : Bool},
  sb: {T.str.bad(uu, False{}) == False{} : Bool}
) -> {T.doc.open.q(same, False{}, '\'', T.QLit{}, bd, rw, hs, he, ps, [], bk, sk, un, lf, ab, Chr{uu}, tail)
  == s1.le(SCon{Chr{uu}, tail}, 1, bd, rw, hs, he, ps, sk, un, lf, ab) : T.Mode}:
  match same:
    case False{}:
      s1.lo.ok(T.str.bad(uu, False{}), uu, tail, bd, rw, hs, he, ps, bk, sk, un, lf, ab, sb)
    case True{}:
      Eq.bit.absurd2(&2, {T.doc.open.q(True{}, False{}, '\'', T.QLit{}, bd, rw, hs, he, ps, [], bk, sk, un, lf, ab,
        Chr{uu}, tail) == s1.le(SCon{Chr{uu}, tail}, 1, bd, rw, hs, he, ps, sk, un, lf, ab) : T.Mode}, hq)

# a first character that is no apostrophe, and that str.bad passes, opens
# the span
def s1.lo.one(
  +uu: U32,
  +tail: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  e39: {U32.is_eq(uu, 39) == False{} : Bool},
  sb: {T.str.bad(uu, False{}) == False{} : Bool}
) -> {T.doc.read(SCon{Chr{uu}, tail}, s1.lo(bd, rw, hs, he, ps, bk, sk, un, lf, ab))
  == T.doc.read(tail, s1.le(SCon{Chr{uu}, tail}, 1, bd, rw, hs, he, ps, sk, un, lf, ab)) : T.Doc}:
  Equal.cong(T.Mode, T.Doc, md => T.doc.read(tail, md),
    T.doc.open(False{}, '\'', T.QLit{}, bd, rw, hs, he, ps, [], bk, sk, un, lf, ab, Chr{uu}, tail),
    s1.le(SCon{Chr{uu}, tail}, 1, bd, rw, hs, he, ps, sk, un, lf, ab),
    s1.lo.q(U32.is_eq(uu, 39), uu, tail, bd, rw, hs, he, ps, bk, sk, un, lf, ab, e39, sb))

# a later character: str.bad passes it, so the span grows
def s1.le.ctl(
  badc: Bool,
  +uu: U32,
  +cut: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  hc: {badc == False{} : Bool}
) -> {T.eat.ctrl(badc, False{}, '\'', Chr{uu}, cut, nn, bd, rw, hs, he, ps, T.QLit{}, sk, un, lf, ab)
  == s1.le(cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un, lf, ab) : T.Mode}:
  match badc:
    case False{}:
      {==}
    case True{}:
      Eq.bit.absurd2(&2, {T.eat.ctrl(True{}, False{}, '\'', Chr{uu}, cut, nn, bd, rw, hs, he, ps, T.QLit{}, sk, un, lf,
        ab) == s1.le(cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un, lf, ab) : T.Mode}, hc)

# no apostrophe
def s1.le.q(
  quote: Bool,
  +uu: U32,
  +cut: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  hq: {quote == False{} : Bool},
  sb: {T.str.bad(uu, False{}) == False{} : Bool}
) -> {T.eat.feed.q(quote, False{}, '\'', Chr{uu}, cut, nn, bd, rw, hs, he, ps, T.QLit{}, sk, un, lf, ab)
  == s1.le(cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un, lf, ab) : T.Mode}:
  match quote:
    case False{}:
      s1.le.ctl(T.str.bad(uu, False{}), uu, cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab, sb)
    case True{}:
      Eq.bit.absurd2(&2, {T.eat.feed.q(True{}, False{}, '\'', Chr{uu}, cut, nn, bd, rw, hs, he, ps, T.QLit{}, sk, un,
        lf, ab) == s1.le(cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un, lf, ab) : T.Mode}, hq)

# a later character that is no apostrophe, and that str.bad passes, grows
# the span by one
def s1.le.one(
  +uu: U32,
  +tail: String,
  +cut: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  e39: {U32.is_eq(uu, 39) == False{} : Bool},
  sb: {T.str.bad(uu, False{}) == False{} : Bool}
) -> {T.doc.read(SCon{Chr{uu}, tail}, s1.le(cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab))
  == T.doc.read(tail, s1.le(cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un, lf, ab)) : T.Doc}:
  Equal.cong(T.Mode, T.Doc, md => T.doc.read(tail, md),
    T.eat.feed(False{}, '\'', cut, nn, bd, rw, hs, he, ps, T.QLit{}, sk, un, lf, ab, Chr{uu}),
    s1.le(cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un, lf, ab),
    s1.le.q(U32.is_eq(uu, 39), uu, cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab, e39, sb))

# the rest tx of a literal string inside its span, pre read so far: cut is
# the text from the string's first character, and nn counts pre's
# characters without wrapping. The closing apostrophe places the span, which
# holds pre and tx
def s1.lg(
  tx: String,
  +pre: String,
  +cut: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  +hc: {cut == String.append(pre, String.append(tx, SCon{'\'', rest})) : String},
  +hn: {U32.to_nat(nn) == M7.plus(pre, 0n) : Nat},
  +hk: {D3.counts(tx, nn) == True{} : Bool},
  +hl: {D1.abnf.literal_string(tx) == True{} : Bool},
  ih: s1.Done(String.append(pre, tx), bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(String.append(tx, SCon{'\'', rest}), s1.le(cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab))):
  match tx:
    case SNil{}:
      s1.done.cast(String.append(pre, SNil{}), pre, Eq.append_nil(pre), bd, rw, hs, he, ps, sk, ab, rest, PP, ih)(
        T.VSpan{cut, nn}, T.LStr{}, T.QLit{}, un, lf, M8.se.own(pre, cut, SCon{'\'', rest}, nn, hc, hn))
    case SCon{hh, +tt}:
      match hh:
        case Chr{+uu}:
          +hl0 = {Eq.and.left(D1.abnf.literal_char(Chr{uu}), D1.abnf.literal_string(tt), hl)
            : {D1.abnf.literal_char(Chr{uu}) == True{} : Bool}}
          M8.pp.step(PP,
            T.doc.read(SCon{Chr{uu}, String.append(tt, SCon{'\'', rest})}, s1.le(cut, nn, bd, rw, hs, he, ps, sk, un,
              lf, ab)),
            T.doc.read(String.append(tt, SCon{'\'', rest}), s1.le(cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un, lf,
              ab)),
            s1.le.one(uu, String.append(tt, SCon{'\'', rest}), cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab,
              M1.s1.lc.a(uu, hl0), s1.sb(uu, False{}, M1.s1.lc.c9(uu, hl0))),
            s1.lg(tt, String.append(pre, SCon{Chr{uu}, SNil{}}), cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un, lf,
              ab, rest, PP, s1.cut(cut, pre, Chr{uu}, String.append(tt, SCon{'\'', rest}), hc),
              s1.hn(nn, pre, Chr{uu}, tt, hn, hk),
              Eq.and.right(Bool.not(U32.is_zero(U32.add(nn, 1))), D3.counts(tt, U32.add(nn, 1)), hk),
              Eq.and.right(D1.abnf.literal_char(Chr{uu}), D1.abnf.literal_string(tt), hl),
              s1.done.cast(String.append(pre, SCon{Chr{uu}, tt}),
                String.append(String.append(pre, SCon{Chr{uu}, SNil{}}), tt),
                Equal.sym(String, String.append(String.append(pre, SCon{Chr{uu}, SNil{}}), tt),
                  String.append(pre, SCon{Chr{uu}, tt}), Eq.append_assoc(pre, SCon{Chr{uu}, SNil{}}, tt)),
                bd, rw, hs, he, ps, sk, ab, rest, PP, ih)))

# a character after `''` that is no apostrophe places the empty string and
# is read as the fast step would read it with the string placed
def s1.lq2(
  same: Bool,
  +cc: Char,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  hq: {same == False{} : Bool}
) -> {T.read.once2(T.lex.q2.go(same, M4.fs.st(bd, rw, hs, he, ps, [], T.LQ2{}, bk, T.QLit{}, sk, un, lf, ab), cc,
  T.QLit{})) == T.read.fast(T.take.top(sk, T.VStr{""}, bd, rw, hs, he, ps, bk, T.QLit{}, un, lf, ab, False{}), cc)
  : T.St}:
  match same:
    case False{}:
      M4.fs.held(sk, T.VStr{""}, cc, bd, rw, hs, he, ps, bk, T.QLit{}, un, lf, ab)
    case True{}:
      Eq.bit.absurd2(&2, {T.read.once2(T.lex.q2.go(True{}, M4.fs.st(bd, rw, hs, he, ps, [], T.LQ2{}, bk, T.QLit{}, sk,
        un, lf, ab), cc, T.QLit{})) == T.read.fast(T.take.top(sk, T.VStr{""}, bd, rw, hs, he, ps, bk, T.QLit{}, un, lf,
        ab, False{}), cc) : T.St}, hq)

# `''` then a rest that may follow a string: the rest is read with the empty
# string placed, back where the value position left it
def s1.lempty(
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  rest: String,
  -PP: T.Doc -> Type,
  hr: {L1.s1.free(rest) == True{} : Bool},
  ih: s1.Done(SNil{}, bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(SCon{'\'', rest}, s1.lo(bd, rw, hs, he, ps, bk, sk, un, lf, ab))):
  match rest:
    case SNil{}:
      M8.pp.step(PP, T.doc.read(SCon{'\'', SNil{}}, s1.lo(bd, rw, hs, he, ps, bk, sk, un, lf, ab)),
        T.doc.read(SNil{}, T.MScan{T.take.top(sk, T.VStr{""}, bd, rw, hs, he, ps, bk, T.QLit{}, un, lf, ab, False{})}),
        Equal.cong(T.St, T.Doc, st => T.read.fin2(st),
          T.take.top(sk, T.VStr{""}, bd, rw, hs, he, ps, bk, T.QLit{}, un, lf, ab, False{}),
          T.read.fin.close(T.read.once2(T.take.top(sk, T.VStr{""}, bd, rw, hs, he, ps, bk, T.QLit{}, un, lf, ab,
            False{}))),
          M8.tk.fin(sk, T.VStr{""}, bd, rw, hs, he, ps, bk, T.QLit{}, un, lf, ab, False{})),
        ih(T.VStr{""}, bk, T.QLit{}, un, lf, {==}))
    case SCon{hh, +tt}:
      match hh:
        case Chr{+uu}:
          M8.pp.step(PP,
            T.doc.read(SCon{'\'', SCon{Chr{uu}, tt}}, s1.lo(bd, rw, hs, he, ps, bk, sk, un, lf, ab)),
            T.doc.read(SCon{Chr{uu}, tt}, T.MScan{T.take.top(sk, T.VStr{""}, bd, rw, hs, he, ps, bk, T.QLit{}, un, lf,
              ab, False{})}),
            Equal.cong(T.Mode, T.Doc, md => T.doc.read(tt, md),
              T.doc.scan(M4.fs.st(bd, rw, hs, he, ps, [], T.LQ2{}, bk, T.QLit{}, sk, un, lf, ab), Chr{uu}),
              T.doc.scan(T.take.top(sk, T.VStr{""}, bd, rw, hs, he, ps, bk, T.QLit{}, un, lf, ab, False{}), Chr{uu}),
              M8.scan.fast(U32.is_eq(uu, 34), U32.is_eq(uu, 39), U32.is_eq(uu, 13),
                M4.fs.st(bd, rw, hs, he, ps, [], T.LQ2{}, bk, T.QLit{}, sk, un, lf, ab),
                T.take.top(sk, T.VStr{""}, bd, rw, hs, he, ps, bk, T.QLit{}, un, lf, ab, False{}), Chr{uu},
                s1.lq2(U32.is_eq(uu, 39), Chr{uu}, bd, rw, hs, he, ps, bk, sk, un, lf, ab,
                  s1.nor.r(U32.is_eq(uu, 34), U32.is_eq(uu, 39), hr)))),
            ih(T.VStr{""}, bk, T.QLit{}, un, lf, {==}))

# a one-line literal string, after its opening apostrophe, then the closing
# apostrophe and a rest that may follow a string: from every value position
# the rest is read with a span of its characters placed
def s1.lopen(
  tx: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  hk: {D3.short(tx) == True{} : Bool},
  +hl: {D1.abnf.literal_string(tx) == True{} : Bool},
  hr: {L1.s1.free(rest) == True{} : Bool},
  ih: s1.Done(tx, bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(String.append(tx, SCon{'\'', rest}), s1.lo(bd, rw, hs, he, ps, bk, sk, un, lf, ab))):
  match tx:
    case SNil{}:
      s1.lempty(bd, rw, hs, he, ps, bk, sk, un, lf, ab, rest, PP, hr, ih)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+uu}:
          +hl0 = {Eq.and.left(D1.abnf.literal_char(Chr{uu}), D1.abnf.literal_string(tt), hl)
            : {D1.abnf.literal_char(Chr{uu}) == True{} : Bool}}
          M8.pp.step(PP,
            T.doc.read(SCon{Chr{uu}, String.append(tt, SCon{'\'', rest})}, s1.lo(bd, rw, hs, he, ps, bk, sk, un, lf,
              ab)),
            T.doc.read(String.append(tt, SCon{'\'', rest}), s1.le(SCon{Chr{uu}, String.append(tt, SCon{'\'', rest})}, 1,
              bd, rw, hs, he, ps, sk, un, lf, ab)),
            s1.lo.one(uu, String.append(tt, SCon{'\'', rest}), bd, rw, hs, he, ps, bk, sk, un, lf, ab,
              M1.s1.lc.a(uu, hl0), s1.sb(uu, False{}, M1.s1.lc.c9(uu, hl0))),
            s1.lg(tt, SCon{Chr{uu}, SNil{}}, SCon{Chr{uu}, String.append(tt, SCon{'\'', rest})}, 1, bd, rw, hs, he, ps,
              sk, un, lf, ab, rest, PP, {==}, {==},
              Eq.and.right(Bool.not(U32.is_zero(U32.add(0, 1))), D3.counts(tt, U32.add(0, 1)), hk),
              Eq.and.right(D1.abnf.literal_char(Chr{uu}), D1.abnf.literal_string(tt), hl), ih))

# Multi-line strings. Every step of a multi-line string is the full step
# (read.fast leaves only a one-line string's plain characters to the fast
# path). After the opening delimiter the scanner is in LTrim, which drops a
# newline; after a line-ending backslash it is in LFold, which drops
# whitespace and newlines; a quote waits in LMq for the two that would close
# the string, and after the closing delimiter LMqEnd takes up to two more.
# A character that ends a trim, or one after quotes that did not close, is
# held and read again in LStr, and since no LStr step holds a character,
# that is the fast step from LStr: the lemmas below turn each of those states
# into LStr for such a character. The same lemmas serve a multi-line basic
# string (QMulti, quotation marks) and a multi-line literal one (QMultiLit,
# apostrophes), by the bit lit.

# the kind of a multi-line string: a literal one's when lit
def s1.mk(lit: Bool) -> T.QKind:
  match lit:
    case True{}:
      T.QMultiLit{}
    case False{}:
      T.QMulti{}

# its quote: an apostrophe when lit, a quotation mark otherwise
def s1.qc(lit: Bool) -> Char:
  match lit:
    case True{}:
      '\''
    case False{}:
      '"'

# the rest of the walk once a multi-line string is closed with its
# characters reversed in fb: reading rest from the scanner with an owned
# string of them placed, and any back, kind, uni and left, gives a document
# PP holds of
def s1.Fin(
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +fb: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  @b2: T.Lex -> @q2: T.QKind -> @u2: U32 -> @l2: U32 ->
    PP(T.doc.read(rest, T.MScan{T.take.top(sk, T.VStr{T.buf.str(fb)}, bd, rw, hs, he, ps, b2, q2, u2, l2, ab,
      False{})}))

# A multi-line string's LStr step holds no character.

# a character is pushed, or refused
def s1.once.ch(
  bad: Bool,
  +uu: U32,
  +qk: T.QKind,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>
) -> {T.read.once2(T.lex.str.char.go(bad, M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, bk, qk, sk, un, lf, ab), Chr{uu}))
  == T.lex.str.char.go(bad, M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, bk, qk, sk, un, lf, ab), Chr{uu}) : T.St}:
  match bad:
    case True{}:
      {==}
    case False{}:
      {==}

# a backslash starts an escape, and anything else is a character
def s1.once.bs(
  bs: Bool,
  +uu: U32,
  +qk: T.QKind,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>
) -> {T.read.once2(T.lex.str.bs(bs, True{}, M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, bk, qk, sk, un, lf, ab),
    Chr{uu},
  qk)) == T.lex.str.bs(bs, True{}, M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, bk, qk, sk, un, lf, ab), Chr{uu}, qk)
  : T.St}:
  match bs:
    case True{}:
      {==}
    case False{}:
      s1.once.ch(T.str.bad(uu, True{}), uu, qk, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)

# a quote starts the closing quotes, a backslash an escape in a basic
# string, and anything else is a character
def s1.once.go(
  quote: Bool,
  basic: Bool,
  +uu: U32,
  +qk: T.QKind,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>
) -> {T.read.once2(T.lex.str.go(quote, True{}, basic, M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, bk, qk, sk, un, lf,
    ab),
  Chr{uu}, qk)) == T.lex.str.go(quote, True{}, basic, M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, bk, qk, sk, un, lf,
  ab), Chr{uu}, qk) : T.St}:
  match quote basic:
    case True{} _b:
      {==}
    case False{} True{}:
      s1.once.bs(U32.is_eq(uu, 92), uu, qk, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)
    case False{} False{}:
      s1.once.ch(T.str.bad(uu, True{}), uu, qk, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)

# so a multi-line string's fast step from LStr is its LStr step, which a
# held character is read by
def s1.once(
  lit: Bool,
  +uu: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>
) -> {T.read.fast(M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, bk, s1.mk(lit), sk, un, lf, ab), Chr{uu})
  == T.lex.str(M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, bk, s1.mk(lit), sk, un, lf, ab), Chr{uu}) : T.St}:
  match lit:
    case True{}:
      s1.once.go(U32.is_eq(uu, 39), False{}, uu, T.QMultiLit{}, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)
    case False{}:
      s1.once.go(U32.is_eq(uu, 34), True{}, uu, T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)

# The trims. A multi-line body is read from LStr (nothing trimmed), from
# LTrim (the first newline, right after the opening delimiter) or from LFold
# (whitespace and newlines after a line-ending backslash, with the newline
# seen); a character that ends the trim is read from LStr, with back at
# LStr.

# the scanner reading a multi-line body under the trim tm
def s1.ms(
  tm: D1.GTrim,
  qk: T.QKind,
  bd: String,
  rw: List<&2, T.Val>,
  hs: List<&2, String>,
  he: List<&2, String>,
  ps: List<&2, String>,
  sk: List<&2, T.Ctx>,
  ab: Bool,
  bk: T.Lex,
  un: U32,
  lf: U32,
  buf: List<&2, Char>
) -> T.St:
  match tm:
    case D1.TNone{}:
      M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, bk, qk, sk, un, lf, ab)
    case D1.TFirst{}:
      M4.fs.st(bd, rw, hs, he, ps, buf, T.LTrim{}, bk, qk, sk, un, lf, ab)
    case D1.TAll{}:
      M4.fs.st(bd, rw, hs, he, ps, buf, T.LFold{}, bk, qk, sk, un, 1, ab)

# the back a character that ends the trim leaves
def s1.eb(tm: D1.GTrim, bk: T.Lex) -> T.Lex:
  match tm:
    case D1.TNone{}:
      bk
    case D1.TFirst{}:
      T.LStr{}
    case D1.TAll{}:
      T.LStr{}

# the left it leaves
def s1.el(tm: D1.GTrim, lf: U32) -> U32:
  match tm:
    case D1.TNone{}:
      lf
    case D1.TFirst{}:
      lf
    case D1.TAll{}:
      1

# LTrim holds a character that is no newline, which LStr reads
def s1.tr.go(
  cr: Bool,
  nl: Bool,
  +lit: Bool,
  +uu: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  hc: {cr == False{} : Bool},
  hn: {nl == False{} : Bool}
) -> {T.read.once2(T.lex.trim.go(cr, nl, M4.fs.st(bd, rw, hs, he, ps, buf, T.LTrim{}, bk, s1.mk(lit), sk, un, lf, ab),
  Chr{uu})) == T.read.fast(M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, T.LStr{}, s1.mk(lit), sk, un, lf, ab), Chr{uu})
  : T.St}:
  match cr nl:
    case True{} n2:
      Eq.bit.absurd2(&2, {T.read.once2(T.lex.trim.go(True{}, n2, M4.fs.st(bd, rw, hs, he, ps, buf, T.LTrim{}, bk,
        s1.mk(lit), sk, un, lf, ab), Chr{uu})) == T.read.fast(M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, T.LStr{},
        s1.mk(lit), sk, un, lf, ab), Chr{uu}) : T.St}, hc)
    case False{} True{}:
      Eq.bit.absurd2(&2, {T.read.once2(T.lex.trim.go(False{}, True{}, M4.fs.st(bd, rw, hs, he, ps, buf, T.LTrim{}, bk,
        s1.mk(lit), sk, un, lf, ab), Chr{uu})) == T.read.fast(M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, T.LStr{},
        s1.mk(lit), sk, un, lf, ab), Chr{uu}) : T.St}, hn)
    case False{} False{}:
      Equal.sym(T.St, T.read.fast(M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, T.LStr{}, s1.mk(lit), sk, un, lf, ab),
        Chr{uu}), T.lex.str(M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, T.LStr{}, s1.mk(lit), sk, un, lf, ab), Chr{uu}),
        s1.once(lit, uu, bd, rw, hs, he, ps, sk, ab, T.LStr{}, un, lf, buf))

# LFold, after the newline, holds a character that is no whitespace and no
# newline, which LStr reads
def s1.fd.go(
  sp: Bool,
  nl: Bool,
  +lit: Bool,
  +uu: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +buf: List<&2, Char>,
  hs0: {sp == False{} : Bool},
  hn: {nl == False{} : Bool}
) -> {T.read.once2(T.lex.fold.go(sp, nl, M4.fs.st(bd, rw, hs, he, ps, buf, T.LFold{}, bk, s1.mk(lit), sk, un, 1, ab),
  Chr{uu})) == T.read.fast(M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, T.LStr{}, s1.mk(lit), sk, un, 1, ab), Chr{uu})
  : T.St}:
  match sp nl:
    case True{} n2:
      Eq.bit.absurd2(&2, {T.read.once2(T.lex.fold.go(True{}, n2, M4.fs.st(bd, rw, hs, he, ps, buf, T.LFold{}, bk,
        s1.mk(lit), sk, un, 1, ab), Chr{uu})) == T.read.fast(M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, T.LStr{},
        s1.mk(lit), sk, un, 1, ab), Chr{uu}) : T.St}, hs0)
    case False{} True{}:
      Eq.bit.absurd2(&2, {T.read.once2(T.lex.fold.go(False{}, True{}, M4.fs.st(bd, rw, hs, he, ps, buf, T.LFold{}, bk,
        s1.mk(lit), sk, un, 1, ab), Chr{uu})) == T.read.fast(M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, T.LStr{},
        s1.mk(lit), sk, un, 1, ab), Chr{uu}) : T.St}, hn)
    case False{} False{}:
      Equal.sym(T.St, T.read.fast(M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, T.LStr{}, s1.mk(lit), sk, un, 1, ab),
        Chr{uu}), T.lex.str(M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, T.LStr{}, s1.mk(lit), sk, un, 1, ab), Chr{uu}),
        s1.once(lit, uu, bd, rw, hs, he, ps, sk, ab, T.LStr{}, un, 1, buf))

# a character that is no whitespace (under TAll) and no newline ends the
# trim: the text from it is read from LStr
def s1.enter(
  tm: D1.GTrim,
  +lit: Bool,
  +uu: U32,
  +tt: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  hs0: {T.ch.sp(Chr{uu}) == False{} : Bool},
  +hn: {T.ch.nl(Chr{uu}) == False{} : Bool}
) -> {T.doc.read(SCon{Chr{uu}, tt}, T.MScan{s1.ms(tm, s1.mk(lit), bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)})
  == T.doc.read(SCon{Chr{uu}, tt}, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, s1.eb(tm, bk), s1.mk(lit), sk, un,  # noqa: S002
  s1.el(tm, lf), ab)}) : T.Doc}:
  match tm:
    case D1.TNone{}:
      {==}
    case D1.TFirst{}:
      Equal.cong(T.Mode, T.Doc, md => T.doc.read(tt, md),
        T.doc.scan(M4.fs.st(bd, rw, hs, he, ps, buf, T.LTrim{}, bk, s1.mk(lit), sk, un, lf, ab), Chr{uu}),
        T.doc.scan(M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, T.LStr{}, s1.mk(lit), sk, un, lf, ab), Chr{uu}),
        M8.scan.fast(U32.is_eq(uu, 34), U32.is_eq(uu, 39), U32.is_eq(uu, 13),
          M4.fs.st(bd, rw, hs, he, ps, buf, T.LTrim{}, bk, s1.mk(lit), sk, un, lf, ab),
          M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, T.LStr{}, s1.mk(lit), sk, un, lf, ab), Chr{uu},
          s1.tr.go(U32.is_eq(uu, 13), T.ch.nl(Chr{uu}), lit, uu, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf,
            Eq.or.right_false(U32.is_eq(uu, 10), U32.is_eq(uu, 13), hn), hn)))
    case D1.TAll{}:
      Equal.cong(T.Mode, T.Doc, md => T.doc.read(tt, md),
        T.doc.scan(M4.fs.st(bd, rw, hs, he, ps, buf, T.LFold{}, bk, s1.mk(lit), sk, un, 1, ab), Chr{uu}),
        T.doc.scan(M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, T.LStr{}, s1.mk(lit), sk, un, 1, ab), Chr{uu}),
        M8.scan.fast(U32.is_eq(uu, 34), U32.is_eq(uu, 39), U32.is_eq(uu, 13),
          M4.fs.st(bd, rw, hs, he, ps, buf, T.LFold{}, bk, s1.mk(lit), sk, un, 1, ab),
          M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, T.LStr{}, s1.mk(lit), sk, un, 1, ab), Chr{uu},
          s1.fd.go(T.ch.sp(Chr{uu}), T.ch.nl(Chr{uu}), lit, uu, bd, rw, hs, he, ps, sk, ab, bk, un, buf, hs0, hn)))

# The quotes. One or two quotes wait in LMq; a character that is no quote
# returns them to the string, pushed, and is held and read again in LStr.

# the left LMq counts: two quotes, or one
def s1.ql(two: Bool) -> U32:
  match two:
    case True{}:
      2
    case False{}:
      1

# the buffer with the quotes pushed
def s1.qp(two: Bool, +qc: Char, buf: List<&2, Char>) -> List<&2, Char>:
  match two:
    case True{}:
      qc <> (qc <> buf)
    case False{}:
      qc <> buf

# one or two quotes in LStr wait in LMq
def s1.mq.in(
  +lit: Bool,
  +two: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +xx: String
) -> {T.doc.read(D4.g.quotes.text(two, s1.qc(lit), xx), T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, bk,
  s1.mk(lit), sk, un, lf, ab)}) == T.doc.read(xx, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LMq{}, bk, s1.mk(lit), sk,
  0, s1.ql(two), ab)}) : T.Doc}:
  match lit two:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# a character that is no quote returns the waiting quotes to the string and
# is read again in LStr
def s1.mq.go(
  quote: Bool,
  +lit: Bool,
  +two: Bool,
  +uu: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +buf: List<&2, Char>,
  hq: {quote == False{} : Bool}
) -> {T.read.once2(T.lex.mq.go(quote, U32.is_eq(s1.ql(two), 1), M4.fs.st(bd, rw, hs, he, ps, buf, T.LMq{}, bk,
  s1.mk(lit), sk, 0, s1.ql(two), ab), Chr{uu}, buf, s1.mk(lit), s1.ql(two)))
  == T.lex.str(M4.fs.st(bd, rw, hs, he, ps, s1.qp(two, s1.qc(lit), buf), T.LStr{}, bk, s1.mk(lit), sk, 0, 0, ab), Chr{uu})  # noqa: S002
  : T.St}:
  match quote lit two:
    case True{} l2 t2:
      Eq.bit.absurd2(&2, {T.read.once2(T.lex.mq.go(True{}, U32.is_eq(s1.ql(t2), 1), M4.fs.st(bd, rw, hs, he, ps, buf,
        T.LMq{}, bk, s1.mk(l2), sk, 0, s1.ql(t2), ab), Chr{uu}, buf, s1.mk(l2), s1.ql(t2)))
        == T.lex.str(M4.fs.st(bd, rw, hs, he, ps, s1.qp(t2, s1.qc(l2), buf), T.LStr{}, bk, s1.mk(l2), sk, 0, 0, ab),
        Chr{uu}) : T.St}, hq)
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

# the fast step from the waiting quotes is the fast step from LStr with them
# pushed, for a character that is no quote of the string
def s1.mq.exit.eq(
  lit: Bool,
  +two: Bool,
  +uu: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +buf: List<&2, Char>,
  hq: {Char.is_eq(Chr{uu}, s1.qc(lit)) == False{} : Bool}
) -> {T.read.fast(M4.fs.st(bd, rw, hs, he, ps, buf, T.LMq{}, bk, s1.mk(lit), sk, 0, s1.ql(two), ab), Chr{uu})
  == T.read.fast(M4.fs.st(bd, rw, hs, he, ps, s1.qp(two, s1.qc(lit), buf), T.LStr{}, bk, s1.mk(lit), sk, 0, 0, ab),
    Chr{uu})
  : T.St}:
  match lit:
    case True{}:
      Equal.trans(T.St,
        T.read.fast(M4.fs.st(bd, rw, hs, he, ps, buf, T.LMq{}, bk, T.QMultiLit{}, sk, 0, s1.ql(two), ab), Chr{uu}),
        T.lex.str(M4.fs.st(bd, rw, hs, he, ps, s1.qp(two, '\'', buf), T.LStr{}, bk, T.QMultiLit{}, sk, 0, 0, ab),
            Chr{uu}),
        T.read.fast(M4.fs.st(bd, rw, hs, he, ps, s1.qp(two, '\'', buf), T.LStr{}, bk, T.QMultiLit{}, sk, 0, 0, ab),
          Chr{uu}),
        s1.mq.go(U32.is_eq(uu, 39), True{}, two, uu, bd, rw, hs, he, ps, sk, ab, bk, buf, hq),
        Equal.sym(T.St, T.read.fast(M4.fs.st(bd, rw, hs, he, ps, s1.qp(two, '\'', buf), T.LStr{}, bk, T.QMultiLit{}, sk,
          0, 0, ab), Chr{uu}), T.lex.str(M4.fs.st(bd, rw, hs, he, ps, s1.qp(two, '\'', buf), T.LStr{}, bk,
              T.QMultiLit{},
          sk, 0, 0, ab), Chr{uu}), s1.once(True{}, uu, bd, rw, hs, he, ps, sk, ab, bk, 0, 0, s1.qp(two, '\'', buf))))
    case False{}:
      Equal.trans(T.St,
        T.read.fast(M4.fs.st(bd, rw, hs, he, ps, buf, T.LMq{}, bk, T.QMulti{}, sk, 0, s1.ql(two), ab), Chr{uu}),
        T.lex.str(M4.fs.st(bd, rw, hs, he, ps, s1.qp(two, '"', buf), T.LStr{}, bk, T.QMulti{}, sk, 0, 0, ab), Chr{uu}),
        T.read.fast(M4.fs.st(bd, rw, hs, he, ps, s1.qp(two, '"', buf), T.LStr{}, bk, T.QMulti{}, sk, 0, 0, ab),
            Chr{uu}),
        s1.mq.go(U32.is_eq(uu, 34), False{}, two, uu, bd, rw, hs, he, ps, sk, ab, bk, buf, hq),
        Equal.sym(T.St, T.read.fast(M4.fs.st(bd, rw, hs, he, ps, s1.qp(two, '"', buf), T.LStr{}, bk, T.QMulti{}, sk, 0,
            0,
          ab), Chr{uu}), T.lex.str(M4.fs.st(bd, rw, hs, he, ps, s1.qp(two, '"', buf), T.LStr{}, bk, T.QMulti{}, sk, 0,
              0,
          ab), Chr{uu}), s1.once(False{}, uu, bd, rw, hs, he, ps, sk, ab, bk, 0, 0, s1.qp(two, '"', buf))))

# a text that starts with no quote of the string, after one or two quotes,
# is read from LStr with the quotes pushed
def s1.mq.exit(
  +lit: Bool,
  +two: Bool,
  +uu: U32,
  +tt: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +buf: List<&2, Char>,
  hq: {Char.is_eq(Chr{uu}, s1.qc(lit)) == False{} : Bool}
) -> {T.doc.read(SCon{Chr{uu}, tt}, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LMq{}, bk, s1.mk(lit), sk, 0,
  s1.ql(two), ab)}) == T.doc.read(SCon{Chr{uu}, tt}, T.MScan{M4.fs.st(bd, rw, hs, he, ps, s1.qp(two, s1.qc(lit), buf),
  T.LStr{}, bk, s1.mk(lit), sk, 0, 0, ab)}) : T.Doc}:
  Equal.cong(T.Mode, T.Doc, md => T.doc.read(tt, md),
    T.doc.scan(M4.fs.st(bd, rw, hs, he, ps, buf, T.LMq{}, bk, s1.mk(lit), sk, 0, s1.ql(two), ab), Chr{uu}),
    T.doc.scan(M4.fs.st(bd, rw, hs, he, ps, s1.qp(two, s1.qc(lit), buf), T.LStr{}, bk, s1.mk(lit), sk, 0, 0, ab),
        Chr{uu}),
    M8.scan.fast(U32.is_eq(uu, 34), U32.is_eq(uu, 39), U32.is_eq(uu, 13),
      M4.fs.st(bd, rw, hs, he, ps, buf, T.LMq{}, bk, s1.mk(lit), sk, 0, s1.ql(two), ab),
      M4.fs.st(bd, rw, hs, he, ps, s1.qp(two, s1.qc(lit), buf), T.LStr{}, bk, s1.mk(lit), sk, 0, 0, ab), Chr{uu},
      s1.mq.exit.eq(lit, two, uu, bd, rw, hs, he, ps, sk, ab, bk, buf, hq)))

# an or whose second half is false: its first half holds
def s1.or.l(
  aa: Bool,
  hh: {Bool.or(aa, False{}) == True{} : Bool}
) -> {aa == True{} : Bool}:
  match aa:
    case True{}:
      {==}
    case False{}:
      Eq.bit.absurd(&2, {False{} == True{} : Bool}, hh)

# the fold's state: LFold with uni and left as given
def s1.fd(
  qk: T.QKind,
  bd: String,
  rw: List<&2, T.Val>,
  hs: List<&2, String>,
  he: List<&2, String>,
  ps: List<&2, String>,
  sk: List<&2, T.Ctx>,
  ab: Bool,
  bk: T.Lex,
  un: U32,
  lf: U32,
  buf: List<&2, Char>
) -> T.Mode:
  T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LFold{}, bk, qk, sk, un, lf, ab)}

# The fold. After a line-ending backslash the scanner is in LFold: a space
# or a tab keeps it there, a newline (a line feed, or a carriage return and
# a line feed) keeps it there with the newline seen (left 1).

# a space or a tab stays in the fold
def s1.fws1.go(
  aa: Bool,
  bb: Bool,
  +uu: U32,
  +tt: String,
  +qk: T.QKind,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  ea: {U32.is_eq(uu, 32) == aa : Bool},
  eb: {U32.is_eq(uu, 9) == bb : Bool},
  hw: {Bool.or(aa, bb) == True{} : Bool}
) -> {T.doc.read(SCon{Chr{uu}, tt}, s1.fd(qk, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf))
  == T.doc.read(tt, s1.fd(qk, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)) : T.Doc}:
  match aa bb:
    case True{} _b:
      %Equal.sym(U32, uu, 32, M8.s1.isk(uu, 32, ea)) : {T.doc.read(SCon{Chr{_}, tt}, s1.fd(qk, bd, rw, hs, he, ps, sk,
          ab,
        bk, un, lf, buf)) == T.doc.read(tt, s1.fd(qk, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)) : T.Doc}
      {==}
    case False{} True{}:
      %Equal.sym(U32, uu, 9, M8.s1.isk(uu, 9, eb)) : {T.doc.read(SCon{Chr{_}, tt}, s1.fd(qk, bd, rw, hs, he, ps, sk, ab,
        bk, un, lf, buf)) == T.doc.read(tt, s1.fd(qk, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)) : T.Doc}
      {==}
    case False{} False{}:
      Eq.bit.absurd(&2, {T.doc.read(SCon{Chr{uu}, tt}, s1.fd(qk, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf))
        == T.doc.read(tt, s1.fd(qk, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)) : T.Doc}, hw)

# whitespace (ws) stays in the fold
def s1.fws(
  w1: String,
  +tt: String,
  +qk: T.QKind,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +hw: {D2.abnf.ws(w1) == True{} : Bool}
) -> {T.doc.read(String.append(w1, tt), s1.fd(qk, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf))
  == T.doc.read(tt, s1.fd(qk, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)) : T.Doc}:
  match w1:
    case SNil{}:
      {==}
    case SCon{hh, +wt}:
      match hh:
        case Chr{+uu}:
          Equal.trans(T.Doc,
            T.doc.read(SCon{Chr{uu}, String.append(wt, tt)}, s1.fd(qk, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)),
            T.doc.read(String.append(wt, tt), s1.fd(qk, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)),
            T.doc.read(tt, s1.fd(qk, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)),
            s1.fws1.go(U32.is_eq(uu, 32), U32.is_eq(uu, 9), uu, String.append(wt, tt), qk, bd, rw, hs, he, ps, sk, ab,
              bk, un, lf, buf, {==}, {==}, Eq.and.left(D2.abnf.wschar(Chr{uu}), D2.abnf.ws(wt), hw)),
            s1.fws(wt, tt, qk, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf,
              Eq.and.right(D2.abnf.wschar(Chr{uu}), D2.abnf.ws(wt), hw)))

# a newline in the fold is seen: left becomes 1
def s1.fnl(
  nl: String,
  +tt: String,
  +qk: T.QKind,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  hn: {D1.abnf.newline(nl) == True{} : Bool}
) -> {T.doc.read(String.append(nl, tt), s1.fd(qk, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf))
  == T.doc.read(tt, s1.fd(qk, bd, rw, hs, he, ps, sk, ab, bk, un, 1, buf)) : T.Doc}:
  M1.s1.nl.elim(xs => {T.doc.read(String.append(xs, tt), s1.fd(qk, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf))
    == T.doc.read(tt, s1.fd(qk, bd, rw, hs, he, ps, sk, ab, bk, un, 1, buf)) : T.Doc}, nl, hn, {==}, {==})

# one character of *( wschar / newline ) on its own: a space, a tab or a
# line feed stays in the fold after its newline
def s1.fwn1.go(
  aa: Bool,
  bb: Bool,
  cc: Bool,
  +uu: U32,
  +tt: String,
  +qk: T.QKind,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +buf: List<&2, Char>,
  ea: {U32.is_eq(uu, 32) == aa : Bool},
  eb: {U32.is_eq(uu, 9) == bb : Bool},
  ec: {U32.is_eq(uu, 10) == cc : Bool},
  hw: {Bool.or(Bool.or(aa, bb), cc) == True{} : Bool}
) -> {T.doc.read(SCon{Chr{uu}, tt}, s1.fd(qk, bd, rw, hs, he, ps, sk, ab, bk, un, 1, buf))
  == T.doc.read(tt, s1.fd(qk, bd, rw, hs, he, ps, sk, ab, bk, un, 1, buf)) : T.Doc}:
  match aa bb cc:
    case True{} _b _c:
      %Equal.sym(U32, uu, 32, M8.s1.isk(uu, 32, ea)) : {T.doc.read(SCon{Chr{_}, tt}, s1.fd(qk, bd, rw, hs, he, ps, sk,
          ab,
        bk, un, 1, buf)) == T.doc.read(tt, s1.fd(qk, bd, rw, hs, he, ps, sk, ab, bk, un, 1, buf)) : T.Doc}
      {==}
    case False{} True{} _c:
      %Equal.sym(U32, uu, 9, M8.s1.isk(uu, 9, eb)) : {T.doc.read(SCon{Chr{_}, tt}, s1.fd(qk, bd, rw, hs, he, ps, sk, ab,
        bk, un, 1, buf)) == T.doc.read(tt, s1.fd(qk, bd, rw, hs, he, ps, sk, ab, bk, un, 1, buf)) : T.Doc}
      {==}
    case False{} False{} True{}:
      %Equal.sym(U32, uu, 10, M8.s1.isk(uu, 10, ec)) : {T.doc.read(SCon{Chr{_}, tt}, s1.fd(qk, bd, rw, hs, he, ps, sk,
          ab,
        bk, un, 1, buf)) == T.doc.read(tt, s1.fd(qk, bd, rw, hs, he, ps, sk, ab, bk, un, 1, buf)) : T.Doc}
      {==}
    case False{} False{} False{}:
      Eq.bit.absurd(&2, {T.doc.read(SCon{Chr{uu}, tt}, s1.fd(qk, bd, rw, hs, he, ps, sk, ab, bk, un, 1, buf))
        == T.doc.read(tt, s1.fd(qk, bd, rw, hs, he, ps, sk, ab, bk, un, 1, buf)) : T.Doc}, hw)

# the text read after the rest of *( wschar / newline ), from the fold after
# its newline
def s1.Fwn(
  +more: String,
  +tt: String,
  +qk: T.QKind,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +buf: List<&2, Char>
) -> Type:
  {T.doc.read(String.append(more, tt), s1.fd(qk, bd, rw, hs, he, ps, sk, ab, bk, un, 1, buf))
    == T.doc.read(tt, s1.fd(qk, bd, rw, hs, he, ps, sk, ab, bk, un, 1, buf)) : T.Doc}

# the induction hypothesis for the rest after one character
def s1.FwnIh(
  +h2: Char,
  +t2: String,
  +tt: String,
  +qk: T.QKind,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +buf: List<&2, Char>
) -> Type:
  {D1.abnf.ws_newlines(SCon{h2, t2}) == True{} : Bool} -> s1.Fwn(SCon{h2, t2}, tt, qk, bd, rw, hs, he, ps, sk, ab, bk,
    un, buf)

# a carriage return in *( wschar / newline ) goes with the line feed after
# it, and the rest is read on from the fold
def s1.fwn.cr(
  +uu: U32,
  h2: Char,
  +t2: String,
  +tt: String,
  +qk: T.QKind,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +buf: List<&2, Char>,
  +eu: {uu == 13 : U32},
  hw: {D1.abnf.ws_newlines(SCon{Chr{uu}, SCon{h2, t2}}) == True{} : Bool},
  ih2: {D1.abnf.ws_newlines(t2) == True{} : Bool} -> s1.Fwn(t2, tt, qk, bd, rw, hs, he, ps, sk, ab, bk, un, buf)
) -> s1.Fwn(SCon{Chr{uu}, SCon{h2, t2}}, tt, qk, bd, rw, hs, he, ps, sk, ab, bk, un, buf):
  match h2:
    case Chr{+u2}:
      +hw13 = {Equal.trans(Bool, D1.abnf.ws_newlines(SCon{Chr{13}, SCon{Chr{u2}, t2}}),
        D1.abnf.ws_newlines(SCon{Chr{uu}, SCon{Chr{u2}, t2}}), True{},
        Equal.cong(U32, Bool, xx => D1.abnf.ws_newlines(SCon{Chr{xx}, SCon{Chr{u2}, t2}}), 13, uu,
          Equal.sym(U32, uu, 13, eu)), hw) : {Bool.and(U32.is_eq(u2, 10), D1.abnf.ws_newlines(t2)) == True{} : Bool}}
      %Equal.sym(U32, uu, 13, eu) : s1.Fwn(SCon{Chr{_}, SCon{Chr{u2}, t2}}, tt, qk, bd, rw, hs, he, ps, sk, ab, bk, un,
        buf)
      %Equal.sym(U32, u2, 10, M8.s1.isk(u2, 10, Eq.and.left(U32.is_eq(u2, 10), D1.abnf.ws_newlines(t2), hw13))) :
        s1.Fwn(SCon{Chr{13}, SCon{Chr{_}, t2}}, tt, qk, bd, rw, hs, he, ps, sk, ab, bk, un, buf)
      ih2(Eq.and.right(U32.is_eq(u2, 10), D1.abnf.ws_newlines(t2), hw13))

# a character of *( wschar / newline ) that is no carriage return is one on
# its own, and the rest is read on from the fold
def s1.fwn.one(
  +uu: U32,
  +h2: Char,
  +t2: String,
  +tt: String,
  +qk: T.QKind,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +buf: List<&2, Char>,
  e13: {U32.is_eq(uu, 13) == False{} : Bool},
  hw: {D1.abnf.ws_newlines(SCon{Chr{uu}, SCon{h2, t2}}) == True{} : Bool},
  ih1: s1.FwnIh(h2, t2, tt, qk, bd, rw, hs, he, ps, sk, ab, bk, un, buf)
) -> s1.Fwn(SCon{Chr{uu}, SCon{h2, t2}}, tt, qk, bd, rw, hs, he, ps, sk, ab, bk, un, buf):
  +xa = {Bool.or(Bool.or(U32.is_eq(uu, 32), U32.is_eq(uu, 9)), U32.is_eq(uu, 10)) : Bool}
  +hx = {s1.or.l(Bool.and(xa, D1.abnf.ws_newlines(SCon{h2, t2})), Equal.trans(Bool,
    Bool.or(Bool.and(xa, D1.abnf.ws_newlines(SCon{h2, t2})), False{}),
    Bool.or(Bool.and(xa, D1.abnf.ws_newlines(SCon{h2, t2})), Bool.and(U32.is_eq(uu, 13),
      Bool.and(D1.abnf.cp(h2, 10), D1.abnf.ws_newlines(t2)))), True{},
    Equal.cong(Bool, Bool, bb => Bool.or(Bool.and(xa, D1.abnf.ws_newlines(SCon{h2, t2})), Bool.and(bb,
      Bool.and(D1.abnf.cp(h2, 10), D1.abnf.ws_newlines(t2)))), False{}, U32.is_eq(uu, 13),
      Equal.sym(Bool, U32.is_eq(uu, 13), False{}, e13)), hw))
    : {Bool.and(xa, D1.abnf.ws_newlines(SCon{h2, t2})) == True{} : Bool}}
  Equal.trans(T.Doc,
    T.doc.read(SCon{Chr{uu}, String.append(SCon{h2, t2}, tt)}, s1.fd(qk, bd, rw, hs, he, ps, sk, ab, bk, un, 1, buf)),
    T.doc.read(String.append(SCon{h2, t2}, tt), s1.fd(qk, bd, rw, hs, he, ps, sk, ab, bk, un, 1, buf)),
    T.doc.read(tt, s1.fd(qk, bd, rw, hs, he, ps, sk, ab, bk, un, 1, buf)),
    s1.fwn1.go(U32.is_eq(uu, 32), U32.is_eq(uu, 9), U32.is_eq(uu, 10), uu, String.append(SCon{h2, t2}, tt), qk, bd, rw,
      hs, he, ps, sk, ab, bk, un, buf, {==}, {==}, {==}, Eq.and.left(xa, D1.abnf.ws_newlines(SCon{h2, t2}), hx)),
    ih1(Eq.and.right(xa, D1.abnf.ws_newlines(SCon{h2, t2}), hx)))

# two or more characters of *( wschar / newline ): a carriage return goes
# with the line feed after it, and anything else is one character on its own
def s1.fwn.two(
  c13: Bool,
  +uu: U32,
  +h2: Char,
  +t2: String,
  +tt: String,
  +qk: T.QKind,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +buf: List<&2, Char>,
  e13: {U32.is_eq(uu, 13) == c13 : Bool},
  +hw: {D1.abnf.ws_newlines(SCon{Chr{uu}, SCon{h2, t2}}) == True{} : Bool},
  ih1: s1.FwnIh(h2, t2, tt, qk, bd, rw, hs, he, ps, sk, ab, bk, un, buf),
  ih2: {D1.abnf.ws_newlines(t2) == True{} : Bool} -> s1.Fwn(t2, tt, qk, bd, rw, hs, he, ps, sk, ab, bk, un, buf)
) -> s1.Fwn(SCon{Chr{uu}, SCon{h2, t2}}, tt, qk, bd, rw, hs, he, ps, sk, ab, bk, un, buf):
  match c13:
    case True{}:
      s1.fwn.cr(uu, h2, t2, tt, qk, bd, rw, hs, he, ps, sk, ab, bk, un, buf, M8.s1.isk(uu, 13, e13), hw, ih2)
    case False{}:
      s1.fwn.one(uu, h2, t2, tt, qk, bd, rw, hs, he, ps, sk, ab, bk, un, buf, e13, hw, ih1)

# *( wschar / newline ), read from the fold after its newline, stays there
def s1.fwn(
  more: String,
  +tt: String,
  +qk: T.QKind,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +buf: List<&2, Char>,
  +hw: {D1.abnf.ws_newlines(more) == True{} : Bool}
) -> s1.Fwn(more, tt, qk, bd, rw, hs, he, ps, sk, ab, bk, un, buf):
  match more:
    case SNil{}:
      {==}
    case SCon{hh, t1}:
      match hh:
        case Chr{+uu}:
          match t1:
            case SNil{}:
              s1.fwn1.go(U32.is_eq(uu, 32), U32.is_eq(uu, 9), U32.is_eq(uu, 10), uu, tt, qk, bd, rw, hs, he, ps, sk, ab,
                bk, un, buf, {==}, {==}, {==}, hw)
            case SCon{+h2, +t2}:
              s1.fwn.two(U32.is_eq(uu, 13), uu, h2, t2, tt, qk, bd, rw, hs, he, ps, sk, ab, bk, un, buf, {==}, hw,
                h1 => s1.fwn(SCon{h2, t2}, tt, qk, bd, rw, hs, he, ps, sk, ab, bk, un, buf, h1),
                h3 => s1.fwn(t2, tt, qk, bd, rw, hs, he, ps, sk, ab, bk, un, buf, h3))

# A line-ending backslash (mlb-escaped-nl): `\`, whitespace, a newline and
# any whitespace and newlines after it, read from LStr, leave the scanner in
# the fold after its newline (left 1), with uni at 0.

# the escape state of a multi-line basic string
def s1.ls.esc(
  bd: String,
  rw: List<&2, T.Val>,
  hs: List<&2, String>,
  he: List<&2, String>,
  ps: List<&2, String>,
  sk: List<&2, T.Ctx>,
  ab: Bool,
  bk: T.Lex,
  un: U32,
  lf: U32,
  buf: List<&2, Char>
) -> T.Mode:
  T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LEsc{}, bk, T.QMulti{}, sk, un, lf, ab)}

# a space or a tab right after the backslash starts the fold, no newline
# seen yet
def s1.esc.ws.go(
  aa: Bool,
  bb: Bool,
  +uu: U32,
  +tt: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  ea: {U32.is_eq(uu, 32) == aa : Bool},
  eb: {U32.is_eq(uu, 9) == bb : Bool},
  hw: {Bool.or(aa, bb) == True{} : Bool}
) -> {T.doc.read(SCon{Chr{uu}, tt}, s1.ls.esc(bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf))
  == T.doc.read(tt, s1.fd(T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk, 0, 0, buf)) : T.Doc}:
  match aa bb:
    case True{} _b:
      %Equal.sym(U32, uu, 32, M8.s1.isk(uu, 32, ea)) : {T.doc.read(SCon{Chr{_}, tt}, s1.ls.esc(bd, rw, hs, he, ps, sk,
          ab,
        bk, un, lf, buf)) == T.doc.read(tt, s1.fd(T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk, 0, 0, buf)) : T.Doc}
      {==}
    case False{} True{}:
      %Equal.sym(U32, uu, 9, M8.s1.isk(uu, 9, eb)) : {T.doc.read(SCon{Chr{_}, tt}, s1.ls.esc(bd, rw, hs, he, ps, sk, ab,
        bk, un, lf, buf)) == T.doc.read(tt, s1.fd(T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk, 0, 0, buf)) : T.Doc}
      {==}
    case False{} False{}:
      Eq.bit.absurd(&2, {T.doc.read(SCon{Chr{uu}, tt}, s1.ls.esc(bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf))
        == T.doc.read(tt, s1.fd(T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk, 0, 0, buf)) : T.Doc}, hw)

# after the backslash: the whitespace and the newline start the fold and see
# the newline
def s1.enl.first(
  w1: String,
  +nl: String,
  +xx: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +hw: {D2.abnf.ws(w1) == True{} : Bool},
  +hn: {D1.abnf.newline(nl) == True{} : Bool}
) -> {T.doc.read(String.append(w1, String.append(nl, xx)), s1.ls.esc(bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf))
  == T.doc.read(xx, s1.fd(T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk, 0, 1, buf)) : T.Doc}:
  match w1:
    case SNil{}:
      M1.s1.nl.elim(ys => {T.doc.read(String.append(ys, xx), s1.ls.esc(bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf))
        == T.doc.read(xx, s1.fd(T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk, 0, 1, buf)) : T.Doc}, nl, hn, {==}, {==})
    case SCon{hh, +wt}:
      match hh:
        case Chr{+uu}:
          Equal.trans(T.Doc,
            T.doc.read(SCon{Chr{uu}, String.append(wt, String.append(nl, xx))}, s1.ls.esc(bd, rw, hs, he, ps, sk, ab,
              bk,
              un, lf, buf)),
            T.doc.read(String.append(wt, String.append(nl, xx)), s1.fd(T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk, 0, 0,
              buf)),
            T.doc.read(xx, s1.fd(T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk, 0, 1, buf)),
            s1.esc.ws.go(U32.is_eq(uu, 32), U32.is_eq(uu, 9), uu, String.append(wt, String.append(nl, xx)), bd, rw, hs,
              he, ps, sk, ab, bk, un, lf, buf, {==}, {==}, Eq.and.left(D2.abnf.wschar(Chr{uu}), D2.abnf.ws(wt),
                hw)),
            Equal.trans(T.Doc,
              T.doc.read(String.append(wt, String.append(nl, xx)), s1.fd(T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk, 0,
                0, buf)),
              T.doc.read(String.append(nl, xx), s1.fd(T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk, 0, 0, buf)),
              T.doc.read(xx, s1.fd(T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk, 0, 1, buf)),
              s1.fws(wt, String.append(nl, xx), T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk, 0, 0, buf,
                Eq.and.right(D2.abnf.wschar(Chr{uu}), D2.abnf.ws(wt), hw)),
              s1.fnl(nl, xx, T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk, 0, 0, buf, hn)))

# a line-ending backslash read from LStr: the backslash, its whitespace, its
# newline and every whitespace and newline after them leave the fold after
# its newline
def s1.enl(
  +w1: String,
  +nl: String,
  +more: String,
  +tt: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +hw: {D1.abnf.mlb_escaped_nl(w1, nl, more) == True{} : Bool}
) -> {T.doc.read(SCon{'\\', String.append(w1, String.append(nl, String.append(more, tt)))}, T.MScan{M4.fs.st(bd, rw, hs,
  he, ps, buf, T.LStr{}, bk, T.QMulti{}, sk, un, lf, ab)})
  == T.doc.read(tt, s1.fd(T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk, 0, 1, buf)) : T.Doc}:
  +h2 = {Eq.and.right(D2.abnf.ws(w1), Bool.and(D1.abnf.newline(nl), D1.abnf.ws_newlines(more)), hw)
    : {Bool.and(D1.abnf.newline(nl), D1.abnf.ws_newlines(more)) == True{} : Bool}}
  Equal.trans(T.Doc,
    T.doc.read(String.append(w1, String.append(nl, String.append(more, tt))), s1.ls.esc(bd, rw, hs, he, ps, sk, ab, bk,
      un, lf, buf)),
    T.doc.read(String.append(more, tt), s1.fd(T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk, 0, 1, buf)),
    T.doc.read(tt, s1.fd(T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk, 0, 1, buf)),
    s1.enl.first(w1, nl, String.append(more, tt), bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf,
      Eq.and.left(D2.abnf.ws(w1), Bool.and(D1.abnf.newline(nl), D1.abnf.ws_newlines(more)), hw),
      Eq.and.left(D1.abnf.newline(nl), D1.abnf.ws_newlines(more), h2)),
    s1.fwn(more, tt, T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk, 0, buf,
      Eq.and.right(D1.abnf.newline(nl), D1.abnf.ws_newlines(more), h2)))

# The closing delimiter: three quotes in LStr close the string, and up to two
# more after them are its own.

# three quotes in LStr are the closing delimiter
def s1.m3(
  +lit: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +xx: String
) -> {T.doc.read(SCon{s1.qc(lit), SCon{s1.qc(lit), SCon{s1.qc(lit), xx}}}, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf,
  T.LStr{}, bk, s1.mk(lit), sk, un, lf, ab)}) == T.doc.read(xx, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LMqEnd{}, bk,  # noqa: S002
  s1.mk(lit), sk, 0, 0, ab)}) : T.Doc}:
  match lit:
    case True{}:
      {==}
    case False{}:
      {==}

# and one or two quotes before them are the string's
def s1.m3x(
  +lit: Bool,
  +two: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +xx: String
) -> {T.doc.read(D4.g.quotes.text(two, s1.qc(lit), SCon{s1.qc(lit), SCon{s1.qc(lit), SCon{s1.qc(lit), xx}}}),
  T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, bk, s1.mk(lit), sk, un, lf, ab)}) == T.doc.read(xx,
  T.MScan{M4.fs.st(bd, rw, hs, he, ps, s1.qp(two, s1.qc(lit), buf), T.LMqEnd{}, bk, s1.mk(lit), sk, 0, s1.ql(two), ab)})
  : T.Doc}:
  match lit two:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# a text that does not start with the string's quote
def s1.nq(lit: Bool, rest: String) -> Bool:
  match rest:
    case SNil{}:
      True{}
    case SCon{+hh, _tt}:
      Bool.not(Char.is_eq(hh, s1.qc(lit)))

# a text that may follow a string starts with no apostrophe
def s1.free.na(
  rest: String,
  hr: {L1.s1.free(rest) == True{} : Bool}
) -> {s1.nq(True{}, rest) == True{} : Bool}:
  match rest:
    case SNil{}:
      {==}
    case SCon{hh, _tt}:
      match hh:
        case Chr{+uu}:
          Equal.cong(Bool, Bool, xx => Bool.not(xx), U32.is_eq(uu, 39), False{},
            s1.nor.r(U32.is_eq(uu, 34), U32.is_eq(uu, 39), hr))

# and no quotation mark
def s1.free.nd(
  rest: String,
  hr: {L1.s1.free(rest) == True{} : Bool}
) -> {s1.nq(False{}, rest) == True{} : Bool}:
  match rest:
    case SNil{}:
      {==}
    case SCon{hh, _tt}:
      match hh:
        case Chr{+uu}:
          Equal.cong(Bool, Bool, xx => Bool.not(xx), U32.is_eq(uu, 34), False{},
            s1.nor.l(U32.is_eq(uu, 34), U32.is_eq(uu, 39), hr))

# a text that may follow a string starts with neither quote
def s1.free.nq(
  lit: Bool,
  rest: String,
  hr: {L1.s1.free(rest) == True{} : Bool}
) -> {s1.nq(lit, rest) == True{} : Bool}:
  match lit:
    case True{}:
      s1.free.na(rest, hr)
    case False{}:
      s1.free.nd(rest, hr)

# a character after the closing quotes that is no quote places the string
# and is read as the fast step reads it from the state with it placed
def s1.me.go(
  quote: Bool,
  room: Bool,
  +cc: Char,
  +qk: T.QKind,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lx: U32,
  +fb: List<&2, Char>,
  hq: {quote == False{} : Bool}
) -> {T.read.once2(T.lex.mq.end.go(quote, room, M4.fs.st(bd, rw, hs, he, ps, fb, T.LMqEnd{}, bk, qk, sk, un, lx, ab),
    cc))
  == T.read.fast(T.take.top(sk, T.VStr{T.buf.str(fb)}, bd, rw, hs, he, ps, bk, qk, un, lx, ab, False{}), cc) : T.St}:
  match quote:
    case False{}:
      M4.fs.held(sk, T.VStr{T.buf.str(fb)}, cc, bd, rw, hs, he, ps, bk, qk, un, lx, ab)
    case True{}:
      Eq.bit.absurd2(&2, {T.read.once2(T.lex.mq.end.go(True{}, room, M4.fs.st(bd, rw, hs, he, ps, fb, T.LMqEnd{}, bk,
          qk,
        sk, un, lx, ab), cc)) == T.read.fast(T.take.top(sk, T.VStr{T.buf.str(fb)}, bd, rw, hs, he, ps, bk, qk, un, lx,
        ab, False{}), cc) : T.St}, hq)

# and so for the string's own kind and quote
def s1.me.q(
  lit: Bool,
  +uu: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lx: U32,
  +fb: List<&2, Char>,
  hr: {Bool.not(Char.is_eq(Chr{uu}, s1.qc(lit))) == True{} : Bool}
) -> {T.read.fast(M4.fs.st(bd, rw, hs, he, ps, fb, T.LMqEnd{}, bk, s1.mk(lit), sk, un, lx, ab), Chr{uu})
  == T.read.fast(T.take.top(sk, T.VStr{T.buf.str(fb)}, bd, rw, hs, he, ps, bk, s1.mk(lit), un, lx, ab, False{}),
    Chr{uu})
  : T.St}:
  match lit:
    case True{}:
      s1.me.go(U32.is_eq(uu, 39), U32.is_lt(lx, 2), Chr{uu}, T.QMultiLit{}, bd, rw, hs, he, ps, sk, ab, bk, un, lx, fb,
        Eq.not.true(U32.is_eq(uu, 39), hr))
    case False{}:
      s1.me.go(U32.is_eq(uu, 34), U32.is_lt(lx, 2), Chr{uu}, T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk, un, lx, fb,
        Eq.not.true(U32.is_eq(uu, 34), hr))

# after the closing quotes, a rest that does not start with the string's
# quote is read with the string placed: an owned string of the characters
# in the buffer, reversed
def s1.mend(
  +lit: Bool,
  rest: String,
  +fb: List<&2, Char>,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lx: U32,
  -PP: T.Doc -> Type,
  hr: {s1.nq(lit, rest) == True{} : Bool},
  ih: s1.Fin(bd, rw, hs, he, ps, sk, ab, fb, rest, PP)
) -> PP(T.doc.read(rest, T.MScan{M4.fs.st(bd, rw, hs, he, ps, fb, T.LMqEnd{}, bk, s1.mk(lit), sk, un, lx, ab)})):
  match rest:
    case SNil{}:
      M8.pp.step(PP, T.doc.read(SNil{}, T.MScan{M4.fs.st(bd, rw, hs, he, ps, fb, T.LMqEnd{}, bk, s1.mk(lit), sk, un, lx,
        ab)}),
        T.doc.read(SNil{}, T.MScan{T.take.top(sk, T.VStr{T.buf.str(fb)}, bd, rw, hs, he, ps, bk, s1.mk(lit), un, lx, ab,
          False{})}),
        Equal.cong(T.St, T.Doc, st => T.read.fin2(st),
          T.take.top(sk, T.VStr{T.buf.str(fb)}, bd, rw, hs, he, ps, bk, s1.mk(lit), un, lx, ab, False{}),
          T.read.fin.close(T.read.once2(T.take.top(sk, T.VStr{T.buf.str(fb)}, bd, rw, hs, he, ps, bk, s1.mk(lit), un,
            lx, ab, False{}))),
          M8.tk.fin(sk, T.VStr{T.buf.str(fb)}, bd, rw, hs, he, ps, bk, s1.mk(lit), un, lx, ab, False{})),
        ih(bk, s1.mk(lit), un, lx))
    case SCon{hh, +tt}:
      match hh:
        case Chr{+uu}:
          M8.pp.step(PP,
            T.doc.read(SCon{Chr{uu}, tt}, T.MScan{M4.fs.st(bd, rw, hs, he, ps, fb, T.LMqEnd{}, bk, s1.mk(lit), sk, un,
                lx,
              ab)}),
            T.doc.read(SCon{Chr{uu}, tt}, T.MScan{T.take.top(sk, T.VStr{T.buf.str(fb)}, bd, rw, hs, he, ps, bk,
              s1.mk(lit), un, lx, ab, False{})}),
            Equal.cong(T.Mode, T.Doc, md => T.doc.read(tt, md),
              T.doc.scan(M4.fs.st(bd, rw, hs, he, ps, fb, T.LMqEnd{}, bk, s1.mk(lit), sk, un, lx, ab), Chr{uu}),
              T.doc.scan(T.take.top(sk, T.VStr{T.buf.str(fb)}, bd, rw, hs, he, ps, bk, s1.mk(lit), un, lx, ab, False{}),
                Chr{uu}),
              M8.scan.fast(U32.is_eq(uu, 34), U32.is_eq(uu, 39), U32.is_eq(uu, 13),
                M4.fs.st(bd, rw, hs, he, ps, fb, T.LMqEnd{}, bk, s1.mk(lit), sk, un, lx, ab),
                T.take.top(sk, T.VStr{T.buf.str(fb)}, bd, rw, hs, he, ps, bk, s1.mk(lit), un, lx, ab, False{}), Chr{uu},
                s1.me.q(lit, uu, bd, rw, hs, he, ps, sk, ab, bk, un, lx, fb, hr))),
            ih(bk, s1.mk(lit), un, lx))

# A multi-line basic body, one piece at a time (GMlb), under the trim g.mlb.chars
# gives it: each piece is read from the state its trim says (s1.ms), and the
# characters it stands for are pushed. The rest of the body is the induction
# hypothesis, a function over the rest's flag, trim, back, uni, left and
# buffer (s1.MbRec), so each piece's lemma is its own def.

# a character that is no newline ends the first trim: the text from it is
# read from LStr
def s1.enter.tf(
  +lit: Bool,
  +uu: U32,
  +tt: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +hn: {T.ch.nl(Chr{uu}) == False{} : Bool}
) -> {T.doc.read(SCon{Chr{uu}, tt}, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LTrim{}, bk, s1.mk(lit), sk, un, lf,
    ab)})
  == T.doc.read(SCon{Chr{uu}, tt}, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, T.LStr{}, s1.mk(lit), sk, un, lf,
  ab)}) : T.Doc}:
  Equal.cong(T.Mode, T.Doc, md => T.doc.read(tt, md),
    T.doc.scan(M4.fs.st(bd, rw, hs, he, ps, buf, T.LTrim{}, bk, s1.mk(lit), sk, un, lf, ab), Chr{uu}),
    T.doc.scan(M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, T.LStr{}, s1.mk(lit), sk, un, lf, ab), Chr{uu}),
    M8.scan.fast(U32.is_eq(uu, 34), U32.is_eq(uu, 39), U32.is_eq(uu, 13),
      M4.fs.st(bd, rw, hs, he, ps, buf, T.LTrim{}, bk, s1.mk(lit), sk, un, lf, ab),
      M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, T.LStr{}, s1.mk(lit), sk, un, lf, ab), Chr{uu},
      s1.tr.go(U32.is_eq(uu, 13), T.ch.nl(Chr{uu}), lit, uu, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf,
        Eq.or.right_false(U32.is_eq(uu, 10), U32.is_eq(uu, 13), hn), hn)))

# a space or a tab stays in the fold
def s1.fd.stay(
  sp: Bool,
  nl: Bool,
  +uu: U32,
  +qk: T.QKind,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +buf: List<&2, Char>,
  hs0: {sp == True{} : Bool}
) -> {T.read.once2(T.lex.fold.go(sp, nl, M4.fs.st(bd, rw, hs, he, ps, buf, T.LFold{}, bk, qk, sk, un, 1, ab), Chr{uu}))
  == M4.fs.st(bd, rw, hs, he, ps, buf, T.LFold{}, bk, qk, sk, un, 1, ab) : T.St}:
  match sp:
    case True{}:
      {==}
    case False{}:
      Eq.bit.absurd(&2, {T.read.once2(T.lex.fold.go(False{}, nl, M4.fs.st(bd, rw, hs, he, ps, buf, T.LFold{}, bk, qk,
          sk,
        un, 1, ab), Chr{uu})) == M4.fs.st(bd, rw, hs, he, ps, buf, T.LFold{}, bk, qk, sk, un, 1, ab) : T.St}, hs0)

# a piece mlb-char takes is one basic-char takes
def s1.mlb.bc(
  kp: D5.KPiece,
  hm: {D1.abnf.mlb_char(kp) == True{} : Bool}
) -> {D1.abnf.basic_char(kp) == True{} : Bool}:
  match kp:
    case D5.KpChar{cc}:
      match cc:
        case Chr{_uu}:
          hm
    case D5.KpEsc{_mm}:
      {==}
    case D5.KpU4{_d, _c, _b, _a}:
      {==}
    case D5.KpU8{_h, _g, _f, _e, _d, _c, _b, _a}:
      {==}

# the rest of a multi-line basic body, then the closing delimiter and rest,
# read from the state the rest's trim says: the induction hypothesis, for
# every flag, trim, back, uni, left and buffer
def s1.MbRec(
  +rr: List<&2, D4.GMlb>,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  @q2: Bool -> {D1.abnf.ml_basic_body(rr, q2) == True{} : Bool} ->
    {D1.prose.mlb_escapes_scalar(rr) == True{} : Bool} ->
    @t2: D1.GTrim -> @b2: T.Lex -> @u2: U32 -> @l2: U32 -> @f2: List<&2, Char> ->
    s1.Fin(bd, rw, hs, he, ps, sk, ab, M3.rev.onto(D1.g.mlb.chars(rr, t2), f2), rest, PP) ->
    PP(T.doc.read(D4.g.mlb.text(rr, SCon{'"', SCon{'"', SCon{'"', rest}}}), T.MScan{s1.ms(t2, T.QMulti{}, bd, rw, hs,
      he, ps, sk, ab, b2, u2, l2, f2)}))

# the end of the body: the closing delimiter, from whatever state the trim
# left, places the characters pushed so far
def s1.mb.nil(
  +tm: D1.GTrim,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  hr: {s1.nq(False{}, rest) == True{} : Bool},
  ih: s1.Fin(bd, rw, hs, he, ps, sk, ab, buf, rest, PP)
) -> PP(T.doc.read(SCon{'"', SCon{'"', SCon{'"', rest}}}, T.MScan{s1.ms(tm, T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk,
  un, lf, buf)})):
  M8.pp.step(PP,
    T.doc.read(SCon{'"', SCon{'"', SCon{'"', rest}}}, T.MScan{s1.ms(tm, T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk, un,
      lf, buf)}),
    T.doc.read(SCon{'"', SCon{'"', SCon{'"', rest}}}, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, s1.eb(tm, bk),
      T.QMulti{}, sk, un, s1.el(tm, lf), ab)}),
    s1.enter(tm, False{}, 34, SCon{'"', SCon{'"', rest}}, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, {==}, {==}),
    M8.pp.step(PP,
      T.doc.read(SCon{'"', SCon{'"', SCon{'"', rest}}}, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, s1.eb(tm,
          bk),
        T.QMulti{}, sk, un, s1.el(tm, lf), ab)}),
      T.doc.read(rest, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LMqEnd{}, s1.eb(tm, bk), T.QMulti{}, sk, 0, 0, ab)}),
      s1.m3(False{}, bd, rw, hs, he, ps, sk, ab, s1.eb(tm, bk), un, s1.el(tm, lf), buf, rest),
      s1.mend(False{}, rest, buf, bd, rw, hs, he, ps, sk, ab, s1.eb(tm, bk), 0, 0, PP, hr, ih)))

# the buffers the body lemmas' rest of the walk is stated over: after a
# character under the trim after a line-ending backslash
def s1.wsb(+ww: Bool, +cc: Char, rr: List<&2, D4.GMlb>, buf: List<&2, Char>) -> List<&2, Char>:
  M3.rev.onto(D1.g.mlb.char.pick(ww, cc, D1.g.mlb.chars(rr, D1.g.mlb.char.trim.pick(ww))), buf)

# after a character under any trim
def s1.chb(+uu: U32, rr: List<&2, D4.GMlb>, tm: D1.GTrim, buf: List<&2, Char>) -> List<&2, Char>:
  M3.rev.onto(D1.g.mlb.chars(D4.GmChar{D5.KpChar{Chr{uu}}} <> rr, tm), buf)

# after an escape
def s1.escb(kp: D5.KPiece, rr: List<&2, D4.GMlb>, buf: List<&2, Char>) -> List<&2, Char>:
  M3.rev.onto(SCon{D5.k3.pc.char(kp), D1.g.mlb.chars(rr, D1.TNone{})}, buf)

# after a newline
def s1.nlb(+tm: D1.GTrim, nl: String, rr: List<&2, D4.GMlb>, buf: List<&2, Char>) -> List<&2, Char>:
  M3.rev.onto(D1.g.nl.char(tm, nl, D1.g.mlb.chars(rr, D1.g.nl.trim(tm))), buf)

# after one or two quotation marks
def s1.qb(two: Bool, rr: List<&2, D4.GMlb>, buf: List<&2, Char>) -> List<&2, Char>:
  M3.rev.onto(D4.g.quotes.text(two, '"', D1.g.mlb.chars(rr, D1.TNone{})), buf)

# after one or two apostrophes
def s1.lqb(two: Bool, rr: List<&2, D4.GMll>, buf: List<&2, Char>) -> List<&2, Char>:
  M3.rev.onto(D4.g.quotes.text(two, '\'', D1.g.mll.chars(rr, D1.TNone{})), buf)

# a character written as itself under the trim after a line-ending
# backslash: whitespace is dropped and keeps the trim, and anything else ends
# it and is pushed
def s1.mb.ws(
  ww: Bool,
  +uu: U32,
  +rr: List<&2, D4.GMlb>,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  ew: {T.ch.sp(Chr{uu}) == ww : Bool},
  +hbu: {D1.abnf.basic_unescaped(Chr{uu}) == True{} : Bool},
  +c9: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == U32.is_eq(uu, 9) : Bool},
  hbr: {D1.abnf.ml_basic_body(rr, False{}) == True{} : Bool},
  hx: {D1.prose.mlb_escapes_scalar(rr) == True{} : Bool},
  ih: s1.Fin(bd, rw, hs, he, ps, sk, ab, s1.wsb(ww, Chr{uu}, rr, buf), rest, PP),
  rec: s1.MbRec(rr, bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(SCon{Chr{uu}, D4.g.mlb.text(rr, SCon{'"', SCon{'"', SCon{'"', rest}}})}, T.MScan{M4.fs.st(bd, rw, hs,
  he, ps, buf, T.LFold{}, bk, T.QMulti{}, sk, un, 1, ab)})):
  match ww:
    case True{}:
      +tx = {D4.g.mlb.text(rr, SCon{'"', SCon{'"', SCon{'"', rest}}}) : String}
      M8.pp.step(PP,
        T.doc.read(SCon{Chr{uu}, tx}, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LFold{}, bk, T.QMulti{}, sk, un, 1,
          ab)}),
        T.doc.read(tx, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LFold{}, bk, T.QMulti{}, sk, un, 1, ab)}),
        Equal.cong(T.Mode, T.Doc, md => T.doc.read(tx, md),
          T.doc.scan(M4.fs.st(bd, rw, hs, he, ps, buf, T.LFold{}, bk, T.QMulti{}, sk, un, 1, ab), Chr{uu}),
          T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LFold{}, bk, T.QMulti{}, sk, un, 1, ab)},
          s1.scq(U32.is_eq(uu, 34), U32.is_eq(uu, 39), U32.is_eq(uu, 13),
            M4.fs.st(bd, rw, hs, he, ps, buf, T.LFold{}, bk, T.QMulti{}, sk, un, 1, ab), Chr{uu},
            M4.fs.st(bd, rw, hs, he, ps, buf, T.LFold{}, bk, T.QMulti{}, sk, un, 1, ab), s1.ncr(uu, c9),
            s1.fd.stay(T.ch.sp(Chr{uu}), T.ch.nl(Chr{uu}), uu, T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk, un, buf, ew),
            {==})),
        rec(False{}, hbr, hx, D1.TAll{}, bk, un, lf, buf, ih))
    case False{}:
      +tx = {D4.g.mlb.text(rr, SCon{'"', SCon{'"', SCon{'"', rest}}}) : String}
      M8.pp.step(PP,
        T.doc.read(SCon{Chr{uu}, tx}, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LFold{}, bk, T.QMulti{}, sk, un, 1,
          ab)}),
        T.doc.read(SCon{Chr{uu}, tx}, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, T.LStr{}, T.QMulti{}, sk, un,
            1,
          ab)}),
        s1.enter(D1.TAll{}, False{}, uu, tx, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, ew, s1.nnl(uu, c9)),
        s1.chr(True{}, uu, bd, rw, hs, he, ps, sk, ab, T.LStr{}, un, 1, buf, tx, PP, hbu,
          +b2 => +u2 => +l2 => rec(False{}, hbr, hx, D1.TNone{}, b2, u2, l2, Chr{uu} <> buf, ih)))

# a character written as itself: pushed under no trim or the first trim
# (which it ends), and under the trim after a line-ending backslash dropped
# when it is whitespace
def s1.mb.ch(
  tm: D1.GTrim,
  +uu: U32,
  +rr: List<&2, D4.GMlb>,
  +qq: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  +hb: {D1.abnf.ml_basic_body(D4.GmChar{D5.KpChar{Chr{uu}}} <> rr, qq) == True{} : Bool},
  hx: {D1.prose.mlb_escapes_scalar(rr) == True{} : Bool},
  ih: s1.Fin(bd, rw, hs, he, ps, sk, ab, s1.chb(uu, rr, tm, buf), rest, PP),
  rec: s1.MbRec(rr, bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(D4.g.mlb.text(D4.GmChar{D5.KpChar{Chr{uu}}} <> rr, SCon{'"', SCon{'"', SCon{'"', rest}}}),
  T.MScan{s1.ms(tm, T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)})):
  match tm:
    case D1.TNone{}:
      +hbu = {Eq.and.left(D1.abnf.mlb_unescaped(Chr{uu}), D1.abnf.ml_basic_body(rr, False{}), hb)
        : {D1.abnf.basic_unescaped(Chr{uu}) == True{} : Bool}}
      s1.chr(True{}, uu, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, D4.g.mlb.text(rr, SCon{'"', SCon{'"', SCon{'"',
        rest}}}), PP, hbu, +b2 => +u2 => +l2 => rec(False{}, Eq.and.right(D1.abnf.mlb_unescaped(Chr{uu}),
        D1.abnf.ml_basic_body(rr, False{}), hb), hx, D1.TNone{}, b2, u2, l2, Chr{uu} <> buf, ih))
    case D1.TFirst{}:
      +hbu = {Eq.and.left(D1.abnf.mlb_unescaped(Chr{uu}), D1.abnf.ml_basic_body(rr, False{}), hb)
        : {D1.abnf.basic_unescaped(Chr{uu}) == True{} : Bool}}
      +tx = {D4.g.mlb.text(rr, SCon{'"', SCon{'"', SCon{'"', rest}}}) : String}
      M8.pp.step(PP,
        T.doc.read(SCon{Chr{uu}, tx}, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LTrim{}, bk, T.QMulti{}, sk, un, lf,
          ab)}),
        T.doc.read(SCon{Chr{uu}, tx}, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, T.LStr{}, T.QMulti{}, sk, un,
            lf,
          ab)}),
        s1.enter.tf(False{}, uu, tx, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, s1.nnl(uu, M1.s1.bu.c9(uu, hbu))),
        s1.chr(True{}, uu, bd, rw, hs, he, ps, sk, ab, T.LStr{}, un, lf, buf, tx, PP, hbu,
          +b2 => +u2 => +l2 => rec(False{}, Eq.and.right(D1.abnf.mlb_unescaped(Chr{uu}), D1.abnf.ml_basic_body(rr,
          False{}), hb), hx, D1.TNone{}, b2, u2, l2, Chr{uu} <> buf, ih)))
    case D1.TAll{}:
      +hbu = {Eq.and.left(D1.abnf.mlb_unescaped(Chr{uu}), D1.abnf.ml_basic_body(rr, False{}), hb)
        : {D1.abnf.basic_unescaped(Chr{uu}) == True{} : Bool}}
      s1.mb.ws(T.ch.sp(Chr{uu}), uu, rr, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP, {==}, hbu,
        M1.s1.bu.c9(uu, hbu), Eq.and.right(D1.abnf.mlb_unescaped(Chr{uu}), D1.abnf.ml_basic_body(rr, False{}), hb), hx,
        ih, rec)

# a text that starts with a character ending the trim is read from LStr
def s1.enter.eq(
  tm: D1.GTrim,
  +uu: U32,
  +xx: String,
  +tx: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +hk: {tx == SCon{Chr{uu}, xx} : String},
  hs0: {T.ch.sp(Chr{uu}) == False{} : Bool},
  hn: {T.ch.nl(Chr{uu}) == False{} : Bool}
) -> {T.doc.read(tx, T.MScan{s1.ms(tm, T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)})
  == T.doc.read(tx, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, s1.eb(tm, bk), T.QMulti{}, sk, un, s1.el(tm, lf),  # noqa: S002
  ab)}) : T.Doc}:
  Equal.trans(T.Doc, T.doc.read(tx, T.MScan{s1.ms(tm, T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)}),
    T.doc.read(SCon{Chr{uu}, xx}, T.MScan{s1.ms(tm, T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)}),
    T.doc.read(tx, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, s1.eb(tm, bk), T.QMulti{}, sk, un, s1.el(tm, lf),
      ab)}),
    Equal.cong(String, T.Doc, zz => T.doc.read(zz, T.MScan{s1.ms(tm, T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk, un, lf,
      buf)}), tx, SCon{Chr{uu}, xx}, hk),
    Equal.trans(T.Doc,
      T.doc.read(SCon{Chr{uu}, xx}, T.MScan{s1.ms(tm, T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)}),
      T.doc.read(SCon{Chr{uu}, xx}, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, s1.eb(tm, bk), T.QMulti{}, sk,
          un,
        s1.el(tm, lf), ab)}),
      T.doc.read(tx, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, s1.eb(tm, bk), T.QMulti{}, sk, un, s1.el(tm,
          lf),
        ab)}),
      s1.enter(tm, False{}, uu, xx, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, hs0, hn),
      Equal.cong(String, T.Doc, zz => T.doc.read(zz, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, s1.eb(tm, bk),
        T.QMulti{}, sk, un, s1.el(tm, lf), ab)}), SCon{Chr{uu}, xx}, tx, Equal.sym(String, tx, SCon{Chr{uu}, xx}, hk))))

# an escape: it ends any trim and pushes the character it stands for
def s1.mb.esc(
  +kp: D5.KPiece,
  +xx: String,
  +rr: List<&2, D4.GMlb>,
  +tm: D1.GTrim,
  +qq: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  hk: {D5.k3.pc.text(kp, D4.g.mlb.text(rr, SCon{'"', SCon{'"', SCon{'"', rest}}})) == SCon{'\\', xx} : String},
  +hb: {D1.abnf.ml_basic_body(D4.GmChar{kp} <> rr, qq) == True{} : Bool},
  +hx: {D1.prose.mlb_escapes_scalar(D4.GmChar{kp} <> rr) == True{} : Bool},
  ih: s1.Fin(bd, rw, hs, he, ps, sk, ab, s1.escb(kp, rr, buf), rest, PP),
  rec: s1.MbRec(rr, bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(D5.k3.pc.text(kp, D4.g.mlb.text(rr, SCon{'"', SCon{'"', SCon{'"', rest}}})), T.MScan{s1.ms(tm,
  T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)})):
  M8.pp.step(PP,
    T.doc.read(D5.k3.pc.text(kp, D4.g.mlb.text(rr, SCon{'"', SCon{'"', SCon{'"', rest}}})), T.MScan{s1.ms(tm,
      T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)}),
    T.doc.read(D5.k3.pc.text(kp, D4.g.mlb.text(rr, SCon{'"', SCon{'"', SCon{'"', rest}}})), T.MScan{M4.fs.st(bd, rw,
      hs, he, ps, buf, T.LStr{}, s1.eb(tm, bk), T.QMulti{}, sk, un, s1.el(tm, lf), ab)}),
    s1.enter.eq(tm, 92, xx, D5.k3.pc.text(kp, D4.g.mlb.text(rr, SCon{'"', SCon{'"', SCon{'"', rest}}})), bd, rw, hs,
      he, ps, sk, ab, bk, un, lf, buf, hk, {==}, {==}),
    s1.pc(kp, True{}, bd, rw, hs, he, ps, sk, ab, s1.eb(tm, bk), un, s1.el(tm, lf), buf, D4.g.mlb.text(rr, SCon{'"',
      SCon{'"', SCon{'"', rest}}}), PP,
      s1.mlb.bc(kp, Eq.and.left(D1.abnf.mlb_char(kp), D1.abnf.ml_basic_body(rr, False{}), hb)),
      Eq.and.left(D1.prose.escape_scalar(kp), D1.prose.mlb_escapes_scalar(rr), hx),
      +b2 => +u2 => +l2 => rec(False{}, Eq.and.right(D1.abnf.mlb_char(kp), D1.abnf.ml_basic_body(rr, False{}), hb),
        Eq.and.right(D1.prose.escape_scalar(kp), D1.prose.mlb_escapes_scalar(rr), hx), D1.TNone{}, b2, u2, l2,
        D5.k3.pc.char(kp) <> buf, ih)))

# a line feed: pushed with no trim, dropped by either trim
def s1.mb.lf(
  tm: D1.GTrim,
  +rr: List<&2, D4.GMlb>,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  +hbr: {D1.abnf.ml_basic_body(rr, False{}) == True{} : Bool},
  +hx: {D1.prose.mlb_escapes_scalar(rr) == True{} : Bool}
) -> s1.MbRec(rr, bd, rw, hs, he, ps, sk, ab, rest, PP) -> s1.Fin(bd, rw, hs, he, ps, sk, ab,
  M3.rev.onto(D1.g.nl.char(tm, "\n", D1.g.mlb.chars(rr, D1.g.nl.trim(tm))), buf), rest, PP) ->
  PP(T.doc.read(String.append("\n", D4.g.mlb.text(rr, SCon{'"', SCon{'"', SCon{'"', rest}}})), T.MScan{s1.ms(tm,
  T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)})):
  match tm:
    case D1.TNone{}:
      rc => ih => rc(False{}, hbr, hx, D1.TNone{}, bk, un, lf, '\n' <> buf, ih)
    case D1.TFirst{}:
      rc => ih => rc(False{}, hbr, hx, D1.TNone{}, bk, un, lf, buf, ih)
    case D1.TAll{}:
      rc => ih => rc(False{}, hbr, hx, D1.TAll{}, bk, un, lf, buf, ih)

# a carriage return and a line feed: pushed with no trim, dropped by either
# trim
def s1.mb.crlf(
  tm: D1.GTrim,
  +rr: List<&2, D4.GMlb>,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  +hbr: {D1.abnf.ml_basic_body(rr, False{}) == True{} : Bool},
  +hx: {D1.prose.mlb_escapes_scalar(rr) == True{} : Bool}
) -> s1.MbRec(rr, bd, rw, hs, he, ps, sk, ab, rest, PP) -> s1.Fin(bd, rw, hs, he, ps, sk, ab,
  M3.rev.onto(D1.g.nl.char(tm, "\r\n", D1.g.mlb.chars(rr, D1.g.nl.trim(tm))), buf), rest, PP) ->
  PP(T.doc.read(String.append("\r\n", D4.g.mlb.text(rr, SCon{'"', SCon{'"', SCon{'"', rest}}})), T.MScan{s1.ms(tm,
  T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)})):
  match tm:
    case D1.TNone{}:
      rc => ih => rc(False{}, hbr, hx, D1.TNone{}, bk, un, lf, '\n' <> ('\r' <> buf), ih)
    case D1.TFirst{}:
      rc => ih => rc(False{}, hbr, hx, D1.TNone{}, bk, un, lf, buf, ih)
    case D1.TAll{}:
      rc => ih => rc(False{}, hbr, hx, D1.TAll{}, bk, un, lf, buf, ih)

# a newline, a line feed or a carriage return and a line feed
def s1.mb.nl(
  +nl: String,
  +rr: List<&2, D4.GMlb>,
  +tm: D1.GTrim,
  +qq: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  +hb: {D1.abnf.ml_basic_body(D4.GmNewline{nl} <> rr, qq) == True{} : Bool},
  +hx: {D1.prose.mlb_escapes_scalar(rr) == True{} : Bool},
  ih: s1.Fin(bd, rw, hs, he, ps, sk, ab, s1.nlb(tm, nl, rr, buf), rest, PP),
  rec: s1.MbRec(rr, bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(String.append(nl, D4.g.mlb.text(rr, SCon{'"', SCon{'"', SCon{'"', rest}}})), T.MScan{s1.ms(tm,
  T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)})):
  +hbr = {Eq.and.right(D1.abnf.newline(nl), D1.abnf.ml_basic_body(rr, False{}), hb)
    : {D1.abnf.ml_basic_body(rr, False{}) == True{} : Bool}}
  M1.s1.nl.elim(nn => s1.MbRec(rr, bd, rw, hs, he, ps, sk, ab, rest, PP) -> s1.Fin(bd, rw, hs, he, ps, sk, ab,
    M3.rev.onto(D1.g.nl.char(tm, nn, D1.g.mlb.chars(rr, D1.g.nl.trim(tm))), buf), rest, PP) ->
    PP(T.doc.read(String.append(nn, D4.g.mlb.text(rr, SCon{'"', SCon{'"', SCon{'"', rest}}})), T.MScan{s1.ms(tm,
    T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)})), nl,
    Eq.and.left(D1.abnf.newline(nl), D1.abnf.ml_basic_body(rr, False{}), hb),
    s1.mb.lf(tm, rr, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP, hbr, hx),
    s1.mb.crlf(tm, rr, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP, hbr, hx))(rec, ih)

# a line-ending backslash: it ends any trim, and the trim after it drops the
# whitespace and newlines that follow
def s1.mb.enl(
  +w1: String,
  +nl: String,
  +more: String,
  +rr: List<&2, D4.GMlb>,
  +tm: D1.GTrim,
  +qq: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  +hb: {D1.abnf.ml_basic_body(D4.GmEscapedNl{w1, nl, more} <> rr, qq) == True{} : Bool},
  hx: {D1.prose.mlb_escapes_scalar(rr) == True{} : Bool},
  ih: s1.Fin(bd, rw, hs, he, ps, sk, ab, M3.rev.onto(D1.g.mlb.chars(rr, D1.TAll{}), buf), rest, PP),
  rec: s1.MbRec(rr, bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(SCon{'\\', String.append(w1, String.append(nl, String.append(more, D4.g.mlb.text(rr, SCon{'"',
  SCon{'"', SCon{'"', rest}}}))))}, T.MScan{s1.ms(tm, T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)})):
  +tx = {D4.g.mlb.text(rr, SCon{'"', SCon{'"', SCon{'"', rest}}}) : String}
  M8.pp.step(PP,
    T.doc.read(SCon{'\\', String.append(w1, String.append(nl, String.append(more, tx)))}, T.MScan{s1.ms(tm, T.QMulti{},
      bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)}),
    T.doc.read(SCon{'\\', String.append(w1, String.append(nl, String.append(more, tx)))}, T.MScan{M4.fs.st(bd, rw, hs,
        he,
      ps, buf, T.LStr{}, s1.eb(tm, bk), T.QMulti{}, sk, un, s1.el(tm, lf), ab)}),
    s1.enter(tm, False{}, 92, String.append(w1, String.append(nl, String.append(more, tx))), bd, rw, hs, he, ps, sk, ab,
      bk, un, lf, buf, {==}, {==}),
    M8.pp.step(PP,
      T.doc.read(SCon{'\\', String.append(w1, String.append(nl, String.append(more, tx)))}, T.MScan{M4.fs.st(bd, rw, hs,
        he,
        ps, buf, T.LStr{}, s1.eb(tm, bk), T.QMulti{}, sk, un, s1.el(tm, lf), ab)}),
      T.doc.read(tx, s1.fd(T.QMulti{}, bd, rw, hs, he, ps, sk, ab, s1.eb(tm, bk), 0, 1, buf)),
      s1.enl(w1, nl, more, tx, bd, rw, hs, he, ps, sk, ab, s1.eb(tm, bk), un, s1.el(tm, lf), buf,
        Eq.and.left(D1.abnf.mlb_escaped_nl(w1, nl, more), D1.abnf.ml_basic_body(rr, False{}), hb)),
      rec(False{}, Eq.and.right(D1.abnf.mlb_escaped_nl(w1, nl, more), D1.abnf.ml_basic_body(rr, False{}), hb), hx,
        D1.TAll{}, s1.eb(tm, bk), 0, lf, buf, ih)))

# after one or two quotes, the next piece (never quotes: ml-basic-body puts
# content between two mlb-quotes) starts with no quotation mark, so the
# quotes return to the string
def s1.mb.qx(
  gm: D4.GMlb,
  +r2: List<&2, D4.GMlb>,
  +two: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +buf: List<&2, Char>,
  +rest: String,
  hbr: {D1.abnf.ml_basic_body(gm <> r2, True{}) == True{} : Bool}
) -> {T.doc.read(D4.g.mlb.text(gm <> r2, SCon{'"', SCon{'"', SCon{'"', rest}}}), T.MScan{M4.fs.st(bd, rw, hs, he, ps,
  buf, T.LMq{}, bk, T.QMulti{}, sk, 0, s1.ql(two), ab)}) == T.doc.read(D4.g.mlb.text(gm <> r2, SCon{'"', SCon{'"',
  SCon{'"', rest}}}), T.MScan{M4.fs.st(bd, rw, hs, he, ps, s1.qp(two, '"', buf), T.LStr{}, bk, T.QMulti{}, sk, 0, 0, ab)})  # noqa: S002
  : T.Doc}:
  match gm:
    case D4.GmChar{kp}:
      match kp:
        case D5.KpChar{cc}:
          match cc:
            case Chr{+uu}:
              s1.mq.exit(False{}, two, uu, D4.g.mlb.text(r2, SCon{'"', SCon{'"', SCon{'"', rest}}}), bd, rw, hs, he,
                ps, sk, ab, bk, buf, M1.s1.bu.q(uu, Eq.and.left(D1.abnf.mlb_unescaped(Chr{uu}),
                D1.abnf.ml_basic_body(r2, False{}), hbr)))
        case D5.KpEsc{+mm}:
          s1.mq.exit(False{}, two, 92, SCon{D5.k3.mark.char(mm), D4.g.mlb.text(r2, SCon{'"', SCon{'"', SCon{'"',
            rest}}})}, bd, rw, hs, he, ps, sk, ab, bk, buf, {==})
        case D5.KpU4{+dd, +cc, +bb, +aa}:
          s1.mq.exit(False{}, two, 92, SCon{'u', D5.k3.hex4.text(dd, cc, bb, aa, D4.g.mlb.text(r2, SCon{'"',
            SCon{'"', SCon{'"', rest}}}))}, bd, rw, hs, he, ps, sk, ab, bk, buf, {==})
        case D5.KpU8{+hh, +gg, +ff, +ee, +dd, +cc, +bb, +aa}:
          s1.mq.exit(False{}, two, 92, SCon{'U', D5.k3.hex4.text(hh, gg, ff, ee, D5.k3.hex4.text(dd, cc, bb, aa,
            D4.g.mlb.text(r2, SCon{'"', SCon{'"', SCon{'"', rest}}})))}, bd, rw, hs, he, ps, sk, ab, bk, buf, {==})
    case D4.GmNewline{+nl}:
      M1.s1.nl.elim(nn => {T.doc.read(String.append(nn, D4.g.mlb.text(r2, SCon{'"', SCon{'"', SCon{'"', rest}}})),
        T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LMq{}, bk, T.QMulti{}, sk, 0, s1.ql(two), ab)})
        == T.doc.read(String.append(nn, D4.g.mlb.text(r2, SCon{'"', SCon{'"', SCon{'"', rest}}})), T.MScan{M4.fs.st(bd,
        rw, hs, he, ps, s1.qp(two, '"', buf), T.LStr{}, bk, T.QMulti{}, sk, 0, 0, ab)}) : T.Doc}, nl,
        Eq.and.left(D1.abnf.newline(nl), D1.abnf.ml_basic_body(r2, False{}), hbr),
        s1.mq.exit(False{}, two, 10, D4.g.mlb.text(r2, SCon{'"', SCon{'"', SCon{'"', rest}}}), bd, rw, hs, he, ps, sk,
          ab, bk, buf, {==}),
        s1.mq.exit(False{}, two, 13, SCon{'\n', D4.g.mlb.text(r2, SCon{'"', SCon{'"', SCon{'"', rest}}})}, bd, rw, hs,
          he, ps, sk, ab, bk, buf, {==}))
    case D4.GmEscapedNl{+w1, +nl, +more}:
      s1.mq.exit(False{}, two, 92, String.append(w1, String.append(nl, String.append(more, D4.g.mlb.text(r2, SCon{'"',
        SCon{'"', SCon{'"', rest}}})))), bd, rw, hs, he, ps, sk, ab, bk, buf, {==})
    case D4.GmQuotes{t2}:
      Eq.bit.absurd(&2, {T.doc.read(D4.g.mlb.text(D4.GmQuotes{t2} <> r2, SCon{'"', SCon{'"', SCon{'"', rest}}}),
        T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LMq{}, bk, T.QMulti{}, sk, 0, s1.ql(two), ab)})
        == T.doc.read(D4.g.mlb.text(D4.GmQuotes{t2} <> r2, SCon{'"', SCon{'"', SCon{'"', rest}}}), T.MScan{M4.fs.st(bd,
        rw, hs, he, ps, s1.qp(two, '"', buf), T.LStr{}, bk, T.QMulti{}, sk, 0, 0, ab)}) : T.Doc}, hbr)

# one or two quotes read from LStr: the closing delimiter's when the body
# ends there, or the string's, pushed, when content follows
def s1.mb.qr(
  +two: Bool,
  rr: List<&2, D4.GMlb>,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  +hbr: {D1.abnf.ml_basic_body(rr, True{}) == True{} : Bool},
  hx: {D1.prose.mlb_escapes_scalar(rr) == True{} : Bool},
  hr: {s1.nq(False{}, rest) == True{} : Bool},
  ih: s1.Fin(bd, rw, hs, he, ps, sk, ab, M3.rev.onto(D1.g.mlb.chars(rr, D1.TNone{}), s1.qp(two, '"', buf)), rest, PP),
  rec: s1.MbRec(rr, bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(D4.g.quotes.text(two, '"', D4.g.mlb.text(rr, SCon{'"', SCon{'"', SCon{'"', rest}}})),
  T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, bk, T.QMulti{}, sk, un, lf, ab)})):
  match rr:
    case []:
      M8.pp.step(PP,
        T.doc.read(D4.g.quotes.text(two, '"', SCon{'"', SCon{'"', SCon{'"', rest}}}), T.MScan{M4.fs.st(bd, rw, hs, he,
          ps,
          buf, T.LStr{}, bk, T.QMulti{}, sk, un, lf, ab)}),
        T.doc.read(rest, T.MScan{M4.fs.st(bd, rw, hs, he, ps, s1.qp(two, '"', buf), T.LMqEnd{}, bk, T.QMulti{}, sk, 0,
          s1.ql(two), ab)}),
        s1.m3x(False{}, two, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest),
        s1.mend(False{}, rest, s1.qp(two, '"', buf), bd, rw, hs, he, ps, sk, ab, bk, 0, s1.ql(two), PP, hr, ih))
    case +gm <> +r2:
      M8.pp.step(PP,
        T.doc.read(D4.g.quotes.text(two, '"', D4.g.mlb.text(gm <> r2, SCon{'"', SCon{'"', SCon{'"', rest}}})),
          T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, bk, T.QMulti{}, sk, un, lf, ab)}),
        T.doc.read(D4.g.mlb.text(gm <> r2, SCon{'"', SCon{'"', SCon{'"', rest}}}), T.MScan{M4.fs.st(bd, rw, hs, he, ps,
          buf, T.LMq{}, bk, T.QMulti{}, sk, 0, s1.ql(two), ab)}),
        s1.mq.in(False{}, two, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, D4.g.mlb.text(gm <> r2, SCon{'"',
          SCon{'"', SCon{'"', rest}}})),
        M8.pp.step(PP,
          T.doc.read(D4.g.mlb.text(gm <> r2, SCon{'"', SCon{'"', SCon{'"', rest}}}), T.MScan{M4.fs.st(bd, rw, hs, he,
              ps,
            buf, T.LMq{}, bk, T.QMulti{}, sk, 0, s1.ql(two), ab)}),
          T.doc.read(D4.g.mlb.text(gm <> r2, SCon{'"', SCon{'"', SCon{'"', rest}}}), T.MScan{M4.fs.st(bd, rw, hs, he,
              ps,
            s1.qp(two, '"', buf), T.LStr{}, bk, T.QMulti{}, sk, 0, 0, ab)}),
          s1.mb.qx(gm, r2, two, bd, rw, hs, he, ps, sk, ab, bk, buf, rest, hbr),
          rec(True{}, hbr, hx, D1.TNone{}, bk, 0, 0, s1.qp(two, '"', buf), ih)))

# one or two quotes in the body: they end any trim
def s1.mb.q(
  two: Bool,
  +rr: List<&2, D4.GMlb>,
  +tm: D1.GTrim,
  +qq: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  hb: {D1.abnf.ml_basic_body(D4.GmQuotes{two} <> rr, qq) == True{} : Bool},
  hx: {D1.prose.mlb_escapes_scalar(rr) == True{} : Bool},
  hr: {s1.nq(False{}, rest) == True{} : Bool},
  ih: s1.Fin(bd, rw, hs, he, ps, sk, ab, s1.qb(two, rr, buf), rest, PP),
  rec: s1.MbRec(rr, bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(D4.g.quotes.text(two, '"', D4.g.mlb.text(rr, SCon{'"', SCon{'"', SCon{'"', rest}}})),
  T.MScan{s1.ms(tm, T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)})):
  match two:
    case True{}:
      +tx = {D4.g.mlb.text(rr, SCon{'"', SCon{'"', SCon{'"', rest}}}) : String}
      M8.pp.step(PP,
        T.doc.read(SCon{'"', SCon{'"', tx}}, T.MScan{s1.ms(tm, T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk, un, lf,
          buf)}),
        T.doc.read(SCon{'"', SCon{'"', tx}}, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, s1.eb(tm, bk),
            T.QMulti{},
          sk, un, s1.el(tm, lf), ab)}),
        s1.enter(tm, False{}, 34, SCon{'"', tx}, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, {==}, {==}),
        s1.mb.qr(True{}, rr, bd, rw, hs, he, ps, sk, ab, s1.eb(tm, bk), un, s1.el(tm, lf), buf, rest, PP,
          Eq.and.right(Bool.not(qq), D1.abnf.ml_basic_body(rr, True{}), hb), hx, hr, ih, rec))
    case False{}:
      +tx = {D4.g.mlb.text(rr, SCon{'"', SCon{'"', SCon{'"', rest}}}) : String}
      M8.pp.step(PP,
        T.doc.read(SCon{'"', tx}, T.MScan{s1.ms(tm, T.QMulti{}, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)}),
        T.doc.read(SCon{'"', tx}, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, s1.eb(tm, bk), T.QMulti{}, sk, un,
          s1.el(tm, lf), ab)}),
        s1.enter(tm, False{}, 34, tx, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, {==}, {==}),
        s1.mb.qr(False{}, rr, bd, rw, hs, he, ps, sk, ab, s1.eb(tm, bk), un, s1.el(tm, lf), buf, rest, PP,
          Eq.and.right(Bool.not(qq), D1.abnf.ml_basic_body(rr, True{}), hb), hx, hr, ih, rec))

# one piece of a multi-line basic body, then the rest by the induction
# hypothesis
def s1.mb.cons(
  gm: D4.GMlb,
  +rr: List<&2, D4.GMlb>,
  +tm: D1.GTrim,
  +qq: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  hb: {D1.abnf.ml_basic_body(gm <> rr, qq) == True{} : Bool},
  hx: {D1.prose.mlb_escapes_scalar(gm <> rr) == True{} : Bool},
  hr: {s1.nq(False{}, rest) == True{} : Bool},
  ih: s1.Fin(bd, rw, hs, he, ps, sk, ab, M3.rev.onto(D1.g.mlb.chars(gm <> rr, tm), buf), rest, PP),
  rec: s1.MbRec(rr, bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(D4.g.mlb.text(gm <> rr, SCon{'"', SCon{'"', SCon{'"', rest}}}), T.MScan{s1.ms(tm, T.QMulti{}, bd,
  rw, hs, he, ps, sk, ab, bk, un, lf, buf)})):
  match gm:
    case D4.GmChar{kp}:
      match kp:
        case D5.KpChar{cc}:
          match cc:
            case Chr{+uu}:
              s1.mb.ch(tm, uu, rr, qq, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP, hb, hx, ih, rec)
        case D5.KpEsc{+mm}:
          s1.mb.esc(D5.KpEsc{mm}, SCon{D5.k3.mark.char(mm), D4.g.mlb.text(rr, SCon{'"', SCon{'"', SCon{'"',
            rest}}})}, rr, tm, qq, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP, {==}, hb, hx, ih, rec)
        case D5.KpU4{+dd, +cc, +bb, +aa}:
          s1.mb.esc(D5.KpU4{dd, cc, bb, aa}, SCon{'u', D5.k3.hex4.text(dd, cc, bb, aa, D4.g.mlb.text(rr, SCon{'"',
            SCon{'"', SCon{'"', rest}}}))}, rr, tm, qq, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP, {==}, hb,
            hx, ih, rec)
        case D5.KpU8{+hh, +gg, +ff, +ee, +dd, +cc, +bb, +aa}:
          s1.mb.esc(D5.KpU8{hh, gg, ff, ee, dd, cc, bb, aa}, SCon{'U', D5.k3.hex4.text(hh, gg, ff, ee,
            D5.k3.hex4.text(dd, cc, bb, aa, D4.g.mlb.text(rr, SCon{'"', SCon{'"', SCon{'"', rest}}})))}, rr, tm, qq,
            bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP, {==}, hb, hx, ih, rec)
    case D4.GmNewline{+nl}:
      s1.mb.nl(nl, rr, tm, qq, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP, hb, hx, ih, rec)
    case D4.GmEscapedNl{+w1, +nl, +more}:
      s1.mb.enl(w1, nl, more, rr, tm, qq, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP, hb, hx, ih, rec)
    case D4.GmQuotes{two}:
      s1.mb.q(two, rr, tm, qq, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP, hb, hx, hr, ih, rec)

# a multi-line basic body under the trim tm, then the closing delimiter and
# a rest that does not start with a quotation mark, read from the state the
# trim says: the rest is read with an owned string of the characters pushed
# so far and the body's placed
def s1.mb(
  bl: List<&2, D4.GMlb>,
  +tm: D1.GTrim,
  +qq: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  hb: {D1.abnf.ml_basic_body(bl, qq) == True{} : Bool},
  hx: {D1.prose.mlb_escapes_scalar(bl) == True{} : Bool},
  +hr: {s1.nq(False{}, rest) == True{} : Bool},
  ih: s1.Fin(bd, rw, hs, he, ps, sk, ab, M3.rev.onto(D1.g.mlb.chars(bl, tm), buf), rest, PP)
) -> PP(T.doc.read(D4.g.mlb.text(bl, SCon{'"', SCon{'"', SCon{'"', rest}}}), T.MScan{s1.ms(tm, T.QMulti{}, bd, rw, hs,
  he, ps, sk, ab, bk, un, lf, buf)})):
  match bl:
    case []:
      s1.mb.nil(tm, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP, hr, ih)
    case +gm <> +rr:
      s1.mb.cons(gm, rr, tm, qq, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP, hb, hx, hr, ih,
        +q2 => +h2 => +x2 => +t2 => +b2 => +u2 => +l2 => +f2 => i2 => s1.mb(rr, t2, q2, bd, rw, hs, he, ps, sk, ab, b2,
          u2, l2, f2, rest, PP, h2, x2, hr, i2))

# A multi-line literal body (GMll), one piece at a time. It has no escapes,
# so its only trim is the first newline's (TFirst, by the bit first); every
# other character, a quotation mark and a backslash among them, is pushed as
# itself.

# the trim a multi-line literal body is read under
def s1.ft(first: Bool) -> D1.GTrim:
  match first:
    case True{}:
      D1.TFirst{}
    case False{}:
      D1.TNone{}

# a multi-line literal string's step pushes a character that is no
# apostrophe and that str.bad passes
def s1.fml(
  quote: Bool,
  +uu: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  hq: {quote == False{} : Bool},
  sb: {T.str.bad(uu, True{}) == False{} : Bool}
) -> {T.read.once2(T.lex.str.go(quote, True{}, False{}, M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, bk, T.QMultiLit{},
    sk,
  un, lf, ab), Chr{uu}, T.QMultiLit{}))
  == M4.fs.st(bd, rw, hs, he, ps, Chr{uu} <> buf, T.LStr{}, bk, T.QMultiLit{}, sk, un, lf, ab) : T.St}:
  match quote:
    case True{}:
      Eq.bit.absurd2(&2, {T.read.once2(T.lex.str.go(True{}, True{}, False{}, M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{},
        bk, T.QMultiLit{}, sk, un, lf, ab), Chr{uu}, T.QMultiLit{}))
        == M4.fs.st(bd, rw, hs, he, ps, Chr{uu} <> buf, T.LStr{}, bk, T.QMultiLit{}, sk, un, lf, ab) : T.St}, hq)
    case False{}:
      %Equal.sym(Bool, T.str.bad(uu, True{}), False{}, sb) : {T.read.once2(T.lex.str.char.go(_, M4.fs.st(bd, rw, hs, he,
        ps, buf, T.LStr{}, bk, T.QMultiLit{}, sk, un, lf, ab), Chr{uu}))
        == M4.fs.st(bd, rw, hs, he, ps, Chr{uu} <> buf, T.LStr{}, bk, T.QMultiLit{}, sk, un, lf, ab) : T.St}
      {==}

# a character literal-char takes is pushed, and back, uni and left stay
def s1.lchr(
  +uu: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  +hl: {D1.abnf.literal_char(Chr{uu}) == True{} : Bool},
  ih: s1.Then(T.QMultiLit{}, bd, rw, hs, he, ps, sk, ab, Chr{uu} <> buf, rest, PP)
) -> PP(T.doc.read(SCon{Chr{uu}, rest}, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, bk, T.QMultiLit{}, sk, un,
    lf,
  ab)})):
  +c9 = {M1.s1.lc.c9(uu, hl) : {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == U32.is_eq(uu, 9) : Bool}}
  M8.pp.step(PP,
    T.doc.read(SCon{Chr{uu}, rest}, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, bk, T.QMultiLit{}, sk, un, lf,
      ab)}),
    T.doc.read(rest, T.MScan{M4.fs.st(bd, rw, hs, he, ps, Chr{uu} <> buf, T.LStr{}, bk, T.QMultiLit{}, sk, un, lf,
        ab)}),
    Equal.cong(T.Mode, T.Doc, md => T.doc.read(rest, md),
      T.doc.scan(M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, bk, T.QMultiLit{}, sk, un, lf, ab), Chr{uu}),
      T.MScan{M4.fs.st(bd, rw, hs, he, ps, Chr{uu} <> buf, T.LStr{}, bk, T.QMultiLit{}, sk, un, lf, ab)},
      s1.scq(U32.is_eq(uu, 34), U32.is_eq(uu, 39), U32.is_eq(uu, 13),
        M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, bk, T.QMultiLit{}, sk, un, lf, ab), Chr{uu},
        M4.fs.st(bd, rw, hs, he, ps, Chr{uu} <> buf, T.LStr{}, bk, T.QMultiLit{}, sk, un, lf, ab), s1.ncr(uu, c9),
        s1.fml(U32.is_eq(uu, 39), uu, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, M1.s1.lc.a(uu, hl),
          s1.sb(uu, True{}, c9)), {==})),
    ih(bk, un, lf))

# the rest of a multi-line literal body, then the closing delimiter and
# rest: the induction hypothesis, for every flag, trim bit, back, uni, left
# and buffer
def s1.LbRec(
  +rr: List<&2, D4.GMll>,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  @q2: Bool -> {D1.abnf.ml_literal_body(rr, q2) == True{} : Bool} ->
    @t2: Bool -> @b2: T.Lex -> @u2: U32 -> @l2: U32 -> @f2: List<&2, Char> ->
    s1.Fin(bd, rw, hs, he, ps, sk, ab, M3.rev.onto(D1.g.mll.chars(rr, s1.ft(t2)), f2), rest, PP) ->
    PP(T.doc.read(D4.g.mll.text(rr, SCon{'\'', SCon{'\'', SCon{'\'', rest}}}), T.MScan{s1.ms(s1.ft(t2), T.QMultiLit{},
      bd, rw, hs, he, ps, sk, ab, b2, u2, l2, f2)}))

# the end of a multi-line literal body
def s1.lb.nil(
  first: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  hr: {s1.nq(True{}, rest) == True{} : Bool},
  ih: s1.Fin(bd, rw, hs, he, ps, sk, ab, buf, rest, PP)
) -> PP(T.doc.read(SCon{'\'', SCon{'\'', SCon{'\'', rest}}}, T.MScan{s1.ms(s1.ft(first), T.QMultiLit{}, bd, rw, hs, he,
  ps, sk, ab, bk, un, lf, buf)})):
  match first:
    case True{}:
      M8.pp.step(PP,
        T.doc.read(SCon{'\'', SCon{'\'', SCon{'\'', rest}}}, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LTrim{}, bk,
          T.QMultiLit{}, sk, un, lf, ab)}),
        T.doc.read(SCon{'\'', SCon{'\'', SCon{'\'', rest}}}, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{},
            T.LStr{},
          T.QMultiLit{}, sk, un, lf, ab)}),
        s1.enter.tf(True{}, 39, SCon{'\'', SCon{'\'', rest}}, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, {==}),
        M8.pp.step(PP,
          T.doc.read(SCon{'\'', SCon{'\'', SCon{'\'', rest}}}, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{},
            T.LStr{},
            T.QMultiLit{}, sk, un, lf, ab)}),
          T.doc.read(rest, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LMqEnd{}, T.LStr{}, T.QMultiLit{}, sk, 0, 0,
              ab)}),
          s1.m3(True{}, bd, rw, hs, he, ps, sk, ab, T.LStr{}, un, lf, buf, rest),
          s1.mend(True{}, rest, buf, bd, rw, hs, he, ps, sk, ab, T.LStr{}, 0, 0, PP, hr, ih)))
    case False{}:
      M8.pp.step(PP,
        T.doc.read(SCon{'\'', SCon{'\'', SCon{'\'', rest}}}, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, bk,
          T.QMultiLit{}, sk, un, lf, ab)}),
        T.doc.read(rest, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LMqEnd{}, bk, T.QMultiLit{}, sk, 0, 0, ab)}),
        s1.m3(True{}, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest),
        s1.mend(True{}, rest, buf, bd, rw, hs, he, ps, sk, ab, bk, 0, 0, PP, hr, ih))

# a character: it ends the first trim, and is pushed
def s1.lb.ch(
  first: Bool,
  +uu: U32,
  +rr: List<&2, D4.GMll>,
  +qq: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  +hb: {D1.abnf.ml_literal_body(D4.GlChar{Chr{uu}} <> rr, qq) == True{} : Bool},
  ih: s1.Fin(bd, rw, hs, he, ps, sk, ab, M3.rev.onto(SCon{Chr{uu}, D1.g.mll.chars(rr, D1.TNone{})}, buf), rest, PP),
  rec: s1.LbRec(rr, bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(SCon{Chr{uu}, D4.g.mll.text(rr, SCon{'\'', SCon{'\'', SCon{'\'', rest}}})}, T.MScan{s1.ms(
  s1.ft(first), T.QMultiLit{}, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)})):
  match first:
    case True{}:
      +hl = {Eq.and.left(D1.abnf.mll_char(Chr{uu}), D1.abnf.ml_literal_body(rr, False{}), hb)
        : {D1.abnf.literal_char(Chr{uu}) == True{} : Bool}}
      +tx = {D4.g.mll.text(rr, SCon{'\'', SCon{'\'', SCon{'\'', rest}}}) : String}
      M8.pp.step(PP,
        T.doc.read(SCon{Chr{uu}, tx}, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LTrim{}, bk, T.QMultiLit{}, sk, un,
            lf,
          ab)}),
        T.doc.read(SCon{Chr{uu}, tx}, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, T.LStr{}, T.QMultiLit{}, sk,
            un,
          lf, ab)}),
        s1.enter.tf(True{}, uu, tx, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, s1.nnl(uu, M1.s1.lc.c9(uu, hl))),
        s1.lchr(uu, bd, rw, hs, he, ps, sk, ab, T.LStr{}, un, lf, buf, tx, PP, hl,
          +b2 => +u2 => +l2 => rec(False{}, Eq.and.right(D1.abnf.mll_char(Chr{uu}), D1.abnf.ml_literal_body(rr,
          False{}), hb), False{}, b2, u2, l2, Chr{uu} <> buf, ih)))
    case False{}:
      +hl = {Eq.and.left(D1.abnf.mll_char(Chr{uu}), D1.abnf.ml_literal_body(rr, False{}), hb)
        : {D1.abnf.literal_char(Chr{uu}) == True{} : Bool}}
      s1.lchr(uu, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, D4.g.mll.text(rr, SCon{'\'', SCon{'\'', SCon{'\'',
        rest}}}), PP, hl, +b2 => +u2 => +l2 => rec(False{}, Eq.and.right(D1.abnf.mll_char(Chr{uu}),
        D1.abnf.ml_literal_body(rr, False{}), hb), False{}, b2, u2, l2, Chr{uu} <> buf, ih))

# a line feed: pushed, or dropped by the first trim
def s1.lb.lf(
  first: Bool,
  +rr: List<&2, D4.GMll>,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  +hbr: {D1.abnf.ml_literal_body(rr, False{}) == True{} : Bool}
) -> s1.LbRec(rr, bd, rw, hs, he, ps, sk, ab, rest, PP) -> s1.Fin(bd, rw, hs, he, ps, sk, ab,
  M3.rev.onto(D1.g.nl.char(s1.ft(first), "\n", D1.g.mll.chars(rr, D1.g.nl.trim(s1.ft(first)))), buf), rest, PP) ->
  PP(T.doc.read(String.append("\n", D4.g.mll.text(rr, SCon{'\'', SCon{'\'', SCon{'\'', rest}}})), T.MScan{s1.ms(
  s1.ft(first), T.QMultiLit{}, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)})):
  match first:
    case True{}:
      rc => ih => rc(False{}, hbr, False{}, bk, un, lf, buf, ih)
    case False{}:
      rc => ih => rc(False{}, hbr, False{}, bk, un, lf, '\n' <> buf, ih)

# a carriage return and a line feed: pushed, or dropped by the first trim
def s1.lb.crlf(
  first: Bool,
  +rr: List<&2, D4.GMll>,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  +hbr: {D1.abnf.ml_literal_body(rr, False{}) == True{} : Bool}
) -> s1.LbRec(rr, bd, rw, hs, he, ps, sk, ab, rest, PP) -> s1.Fin(bd, rw, hs, he, ps, sk, ab,
  M3.rev.onto(D1.g.nl.char(s1.ft(first), "\r\n", D1.g.mll.chars(rr, D1.g.nl.trim(s1.ft(first)))), buf), rest, PP) ->
  PP(T.doc.read(String.append("\r\n", D4.g.mll.text(rr, SCon{'\'', SCon{'\'', SCon{'\'', rest}}})), T.MScan{s1.ms(
  s1.ft(first), T.QMultiLit{}, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)})):
  match first:
    case True{}:
      rc => ih => rc(False{}, hbr, False{}, bk, un, lf, buf, ih)
    case False{}:
      rc => ih => rc(False{}, hbr, False{}, bk, un, lf, '\n' <> ('\r' <> buf), ih)

# after one or two apostrophes, the next piece (never apostrophes) starts
# with no apostrophe, so they return to the string
def s1.lb.qx(
  gl: D4.GMll,
  +r2: List<&2, D4.GMll>,
  +two: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +buf: List<&2, Char>,
  +rest: String,
  hbr: {D1.abnf.ml_literal_body(gl <> r2, True{}) == True{} : Bool}
) -> {T.doc.read(D4.g.mll.text(gl <> r2, SCon{'\'', SCon{'\'', SCon{'\'', rest}}}), T.MScan{M4.fs.st(bd, rw, hs, he, ps,
  buf, T.LMq{}, bk, T.QMultiLit{}, sk, 0, s1.ql(two), ab)}) == T.doc.read(D4.g.mll.text(gl <> r2, SCon{'\'',
  SCon{'\'', SCon{'\'', rest}}}), T.MScan{M4.fs.st(bd, rw, hs, he, ps, s1.qp(two, '\'', buf), T.LStr{}, bk, T.QMultiLit{},  # noqa: S002
  sk, 0, 0, ab)}) : T.Doc}:
  match gl:
    case D4.GlChar{cc}:
      match cc:
        case Chr{+uu}:
          s1.mq.exit(True{}, two, uu, D4.g.mll.text(r2, SCon{'\'', SCon{'\'', SCon{'\'', rest}}}), bd, rw, hs, he, ps,
            sk, ab, bk, buf, M1.s1.lc.a(uu, Eq.and.left(D1.abnf.mll_char(Chr{uu}), D1.abnf.ml_literal_body(r2,
            False{}), hbr)))
    case D4.GlNewline{+nl}:
      M1.s1.nl.elim(nn => {T.doc.read(String.append(nn, D4.g.mll.text(r2, SCon{'\'', SCon{'\'', SCon{'\'', rest}}})),
        T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LMq{}, bk, T.QMultiLit{}, sk, 0, s1.ql(two), ab)})
        == T.doc.read(String.append(nn, D4.g.mll.text(r2, SCon{'\'', SCon{'\'', SCon{'\'', rest}}})),
          T.MScan{M4.fs.st(bd,
        rw, hs, he, ps, s1.qp(two, '\'', buf), T.LStr{}, bk, T.QMultiLit{}, sk, 0, 0, ab)}) : T.Doc}, nl,
        Eq.and.left(D1.abnf.newline(nl), D1.abnf.ml_literal_body(r2, False{}), hbr),
        s1.mq.exit(True{}, two, 10, D4.g.mll.text(r2, SCon{'\'', SCon{'\'', SCon{'\'', rest}}}), bd, rw, hs, he, ps,
          sk, ab, bk, buf, {==}),
        s1.mq.exit(True{}, two, 13, SCon{'\n', D4.g.mll.text(r2, SCon{'\'', SCon{'\'', SCon{'\'', rest}}})}, bd, rw,
          hs, he, ps, sk, ab, bk, buf, {==}))
    case D4.GlQuotes{t2}:
      Eq.bit.absurd(&2, {T.doc.read(D4.g.mll.text(D4.GlQuotes{t2} <> r2, SCon{'\'', SCon{'\'', SCon{'\'', rest}}}),
        T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LMq{}, bk, T.QMultiLit{}, sk, 0, s1.ql(two), ab)})
        == T.doc.read(D4.g.mll.text(D4.GlQuotes{t2} <> r2, SCon{'\'', SCon{'\'', SCon{'\'', rest}}}),
        T.MScan{M4.fs.st(bd, rw, hs, he, ps, s1.qp(two, '\'', buf), T.LStr{}, bk, T.QMultiLit{}, sk, 0, 0,
            ab)}) : T.Doc},
        hbr)

# one or two apostrophes read from LStr: the closing delimiter's when the
# body ends there, or the string's, pushed, when content follows
def s1.lb.qr(
  +two: Bool,
  rr: List<&2, D4.GMll>,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  +hbr: {D1.abnf.ml_literal_body(rr, True{}) == True{} : Bool},
  hr: {s1.nq(True{}, rest) == True{} : Bool},
  ih: s1.Fin(bd, rw, hs, he, ps, sk, ab, M3.rev.onto(D1.g.mll.chars(rr, D1.TNone{}), s1.qp(two, '\'', buf)), rest, PP),
  rec: s1.LbRec(rr, bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(D4.g.quotes.text(two, '\'', D4.g.mll.text(rr, SCon{'\'', SCon{'\'', SCon{'\'', rest}}})),
  T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, bk, T.QMultiLit{}, sk, un, lf, ab)})):
  match rr:
    case []:
      M8.pp.step(PP,
        T.doc.read(D4.g.quotes.text(two, '\'', SCon{'\'', SCon{'\'', SCon{'\'', rest}}}), T.MScan{M4.fs.st(bd, rw, hs,
          he,
          ps, buf, T.LStr{}, bk, T.QMultiLit{}, sk, un, lf, ab)}),
        T.doc.read(rest, T.MScan{M4.fs.st(bd, rw, hs, he, ps, s1.qp(two, '\'', buf), T.LMqEnd{}, bk, T.QMultiLit{}, sk,
            0,
          s1.ql(two), ab)}),
        s1.m3x(True{}, two, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest),
        s1.mend(True{}, rest, s1.qp(two, '\'', buf), bd, rw, hs, he, ps, sk, ab, bk, 0, s1.ql(two), PP, hr, ih))
    case +gl <> +r2:
      M8.pp.step(PP,
        T.doc.read(D4.g.quotes.text(two, '\'', D4.g.mll.text(gl <> r2, SCon{'\'', SCon{'\'', SCon{'\'', rest}}})),
          T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, bk, T.QMultiLit{}, sk, un, lf, ab)}),
        T.doc.read(D4.g.mll.text(gl <> r2, SCon{'\'', SCon{'\'', SCon{'\'', rest}}}), T.MScan{M4.fs.st(bd, rw, hs, he,
          ps,
          buf, T.LMq{}, bk, T.QMultiLit{}, sk, 0, s1.ql(two), ab)}),
        s1.mq.in(True{}, two, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, D4.g.mll.text(gl <> r2, SCon{'\'',
          SCon{'\'', SCon{'\'', rest}}})),
        M8.pp.step(PP,
          T.doc.read(D4.g.mll.text(gl <> r2, SCon{'\'', SCon{'\'', SCon{'\'', rest}}}), T.MScan{M4.fs.st(bd, rw, hs, he,
            ps, buf, T.LMq{}, bk, T.QMultiLit{}, sk, 0, s1.ql(two), ab)}),
          T.doc.read(D4.g.mll.text(gl <> r2, SCon{'\'', SCon{'\'', SCon{'\'', rest}}}), T.MScan{M4.fs.st(bd, rw, hs, he,
            ps, s1.qp(two, '\'', buf), T.LStr{}, bk, T.QMultiLit{}, sk, 0, 0, ab)}),
          s1.lb.qx(gl, r2, two, bd, rw, hs, he, ps, sk, ab, bk, buf, rest, hbr),
          rec(True{}, hbr, False{}, bk, 0, 0, s1.qp(two, '\'', buf), ih)))

# one or two apostrophes in the body: they end the first trim
def s1.lb.q(
  two: Bool,
  +first: Bool,
  +rr: List<&2, D4.GMll>,
  +qq: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  hb: {D1.abnf.ml_literal_body(D4.GlQuotes{two} <> rr, qq) == True{} : Bool},
  hr: {s1.nq(True{}, rest) == True{} : Bool},
  ih: s1.Fin(bd, rw, hs, he, ps, sk, ab, s1.lqb(two, rr, buf), rest, PP),
  rec: s1.LbRec(rr, bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(D4.g.quotes.text(two, '\'', D4.g.mll.text(rr, SCon{'\'', SCon{'\'', SCon{'\'', rest}}})),
  T.MScan{s1.ms(s1.ft(first), T.QMultiLit{}, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)})):
  match two:
    case True{}:
      +tx = {D4.g.mll.text(rr, SCon{'\'', SCon{'\'', SCon{'\'', rest}}}) : String}
      M8.pp.step(PP,
        T.doc.read(SCon{'\'', SCon{'\'', tx}}, T.MScan{s1.ms(s1.ft(first), T.QMultiLit{}, bd, rw, hs, he, ps, sk, ab,
          bk,
          un, lf, buf)}),
        T.doc.read(SCon{'\'', SCon{'\'', tx}}, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, s1.eb(s1.ft(first),
            bk),
          T.QMultiLit{}, sk, un, s1.el(s1.ft(first), lf), ab)}),
        s1.enter(s1.ft(first), True{}, 39, SCon{'\'', tx}, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, {==}, {==}),
        s1.lb.qr(True{}, rr, bd, rw, hs, he, ps, sk, ab, s1.eb(s1.ft(first), bk), un, s1.el(s1.ft(first), lf), buf,
          rest,
          PP, Eq.and.right(Bool.not(qq), D1.abnf.ml_literal_body(rr, True{}), hb), hr, ih, rec))
    case False{}:
      +tx = {D4.g.mll.text(rr, SCon{'\'', SCon{'\'', SCon{'\'', rest}}}) : String}
      M8.pp.step(PP,
        T.doc.read(SCon{'\'', tx}, T.MScan{s1.ms(s1.ft(first), T.QMultiLit{}, bd, rw, hs, he, ps, sk, ab, bk, un, lf,
          buf)}),
        T.doc.read(SCon{'\'', tx}, T.MScan{M4.fs.st(bd, rw, hs, he, ps, buf, T.LStr{}, s1.eb(s1.ft(first), bk),
          T.QMultiLit{}, sk, un, s1.el(s1.ft(first), lf), ab)}),
        s1.enter(s1.ft(first), True{}, 39, tx, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, {==}, {==}),
        s1.lb.qr(False{}, rr, bd, rw, hs, he, ps, sk, ab, s1.eb(s1.ft(first), bk), un, s1.el(s1.ft(first), lf), buf,
          rest, PP, Eq.and.right(Bool.not(qq), D1.abnf.ml_literal_body(rr, True{}), hb), hr, ih, rec))

# one piece of a multi-line literal body, then the rest by the induction
# hypothesis
def s1.lb.cons(
  gl: D4.GMll,
  +rr: List<&2, D4.GMll>,
  +first: Bool,
  +qq: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  +hb: {D1.abnf.ml_literal_body(gl <> rr, qq) == True{} : Bool},
  hr: {s1.nq(True{}, rest) == True{} : Bool},
  ih: s1.Fin(bd, rw, hs, he, ps, sk, ab, M3.rev.onto(D1.g.mll.chars(gl <> rr, s1.ft(first)), buf), rest, PP),
  rec: s1.LbRec(rr, bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(D4.g.mll.text(gl <> rr, SCon{'\'', SCon{'\'', SCon{'\'', rest}}}), T.MScan{s1.ms(s1.ft(first),
  T.QMultiLit{}, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)})):
  match gl:
    case D4.GlChar{cc}:
      match cc:
        case Chr{+uu}:
          s1.lb.ch(first, uu, rr, qq, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP, hb, ih, rec)
    case D4.GlNewline{+nl}:
      +hbr = {Eq.and.right(D1.abnf.newline(nl), D1.abnf.ml_literal_body(rr, False{}), hb)
        : {D1.abnf.ml_literal_body(rr, False{}) == True{} : Bool}}
      M1.s1.nl.elim(nn => s1.LbRec(rr, bd, rw, hs, he, ps, sk, ab, rest, PP) -> s1.Fin(bd, rw, hs, he, ps, sk, ab,
        M3.rev.onto(D1.g.nl.char(s1.ft(first), nn, D1.g.mll.chars(rr, D1.g.nl.trim(s1.ft(first)))), buf), rest,
          PP) ->
        PP(T.doc.read(String.append(nn, D4.g.mll.text(rr, SCon{'\'', SCon{'\'', SCon{'\'', rest}}})), T.MScan{s1.ms(
        s1.ft(first), T.QMultiLit{}, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)})), nl,
        Eq.and.left(D1.abnf.newline(nl), D1.abnf.ml_literal_body(rr, False{}), hb),
        s1.lb.lf(first, rr, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP, hbr),
        s1.lb.crlf(first, rr, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP, hbr))(rec, ih)
    case D4.GlQuotes{two}:
      s1.lb.q(two, first, rr, qq, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP, hb, hr, ih, rec)

# a multi-line literal body, first-trimmed when first, then the closing
# delimiter and a rest that does not start with an apostrophe: the rest is
# read with an owned string of the characters pushed so far and the body's
# placed
def s1.lb(
  bl: List<&2, D4.GMll>,
  +first: Bool,
  +qq: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  hb: {D1.abnf.ml_literal_body(bl, qq) == True{} : Bool},
  +hr: {s1.nq(True{}, rest) == True{} : Bool},
  ih: s1.Fin(bd, rw, hs, he, ps, sk, ab, M3.rev.onto(D1.g.mll.chars(bl, s1.ft(first)), buf), rest, PP)
) -> PP(T.doc.read(D4.g.mll.text(bl, SCon{'\'', SCon{'\'', SCon{'\'', rest}}}), T.MScan{s1.ms(s1.ft(first),
  T.QMultiLit{}, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)})):
  match bl:
    case []:
      s1.lb.nil(first, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP, hr, ih)
    case +gl <> +rr:
      s1.lb.cons(gl, rr, first, qq, bd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP, hb, hr, ih,
        +q2 => +h2 => +t2 => +b2 => +u2 => +l2 => +f2 => i2 => s1.lb(rr, t2, q2, bd, rw, hs, he, ps, sk, ab, b2, u2, l2,
          f2, rest, PP, h2, hr, i2))

# A string denotes no more characters than its text holds: each piece
# stands for at most one character and is written with at least one, and
# the delimiters stand for none. So in a document shorter than 2^32
# characters the string's characters are fewer than 2^32 too, and its span
# counts them without wrapping.

# a text no longer than another
def s1.ln(xs: String, ys: String) -> Bool:
  match xs:
    case SNil{}:
      True{}
    case SCon{_hh, +xt}:
      match ys:
        case SNil{}:
          False{}
        case SCon{_gg, +yt}:
          s1.ln(xt, yt)

# a text no longer than another is no longer than it with one more
# character in front
def s1.ln.r(
  xs: String,
  ys: String,
  +cc: Char,
  hl: {s1.ln(xs, ys) == True{} : Bool}
) -> {s1.ln(xs, SCon{cc, ys}) == True{} : Bool}:
  match xs:
    case SNil{}:
      {==}
    case SCon{+xh, +xt}:
      match ys:
        case SNil{}:
          Eq.bit.absurd(&2, {s1.ln(SCon{xh, xt}, SCon{cc, SNil{}}) == True{} : Bool}, hl)
        case SCon{+yh, +yt}:
          s1.ln.r(xt, yt, yh, hl)

# nor than it with any text in front
def s1.ln.app(
  zs: String,
  +xs: String,
  +ys: String,
  hl: {s1.ln(xs, ys) == True{} : Bool}
) -> {s1.ln(xs, String.append(zs, ys)) == True{} : Bool}:
  match zs:
    case SNil{}:
      hl
    case SCon{+zh, +zt}:
      s1.ln.r(xs, String.append(zt, ys), zh, s1.ln.app(zt, xs, ys, hl))

# a text is no longer than it with any text after it
def s1.ln.pre(
  xs: String,
  +zs: String
) -> {s1.ln(xs, String.append(xs, zs)) == True{} : Bool}:
  match xs:
    case SNil{}:
      {==}
    case SCon{_xh, +xt}:
      s1.ln.pre(xt, zs)

# the same text in front of both keeps the order
def s1.ln.same(
  zs: String,
  +xs: String,
  +ys: String,
  hl: {s1.ln(xs, ys) == True{} : Bool}
) -> {s1.ln(String.append(zs, xs), String.append(zs, ys)) == True{} : Bool}:
  match zs:
    case SNil{}:
      hl
    case SCon{_zh, +zt}:
      s1.ln.same(zt, xs, ys, hl)

# a count that does not wrap over a text does not wrap over a shorter one
def s1.counts.le(
  xs: String,
  ys: String,
  +nn: U32,
  hl: {s1.ln(xs, ys) == True{} : Bool},
  hc: {D3.counts(ys, nn) == True{} : Bool}
) -> {D3.counts(xs, nn) == True{} : Bool}:
  match xs:
    case SNil{}:
      {==}
    case SCon{+xh, +xt}:
      match ys:
        case SNil{}:
          Eq.bit.absurd(&2, {D3.counts(SCon{xh, xt}, nn) == True{} : Bool}, hl)
        case SCon{_yh, +yt}:
          +hc2 = {hc : {Bool.and(Bool.not(U32.is_zero(U32.add(nn, 1))), D3.counts(yt, U32.add(nn, 1))) == True{}
            : Bool}}
          M6.and.tt(Bool.not(U32.is_zero(U32.add(nn, 1))), D3.counts(xt, U32.add(nn, 1)),
            Eq.and.left(Bool.not(U32.is_zero(U32.add(nn, 1))), D3.counts(yt, U32.add(nn, 1)), hc2),
            s1.counts.le(xt, yt, U32.add(nn, 1), hl, Eq.and.right(Bool.not(U32.is_zero(U32.add(nn, 1))),
              D3.counts(yt, U32.add(nn, 1)), hc2)))

# a piece of a basic string stands for one character and is written with at
# least one
def s1.ln.pc(
  pp: D5.KPiece,
  +xs: String,
  +ys: String,
  hl: {s1.ln(xs, ys) == True{} : Bool}
) -> {s1.ln(SCon{D5.k3.pc.char(pp), xs}, D5.k3.pc.text(pp, ys)) == True{} : Bool}:
  match pp:
    case D5.KpChar{_cc}:
      hl
    case D5.KpEsc{+mm}:
      s1.ln.r(xs, ys, D5.k3.mark.char(mm), hl)
    case D5.KpU4{+dd, +cc, +bb, +aa}:
      s1.ln.app(SCon{'u', D5.k3.hex4.text(dd, cc, bb, aa, "")}, xs, ys, hl)
    case D5.KpU8{+hh, +gg, +ff, +ee, +dd, +cc, +bb, +aa}:
      s1.ln.app(SCon{'U', D5.k3.hex4.text(hh, gg, ff, ee, D5.k3.hex4.text(dd, cc, bb, aa, ""))}, xs, ys, hl)

# a basic string's pieces
def s1.ln.pcs(
  pl: List<&2, D5.KPiece>,
  +ys: String
) -> {s1.ln(D5.k3.pcs.name(pl), D5.k3.pcs.text(pl, ys)) == True{} : Bool}:
  match pl:
    case []:
      {==}
    case +pp <> +pr:
      s1.ln.pc(pp, D5.k3.pcs.name(pr), D5.k3.pcs.text(pr, ys), s1.ln.pcs(pr, ys))

# a character is kept or dropped after a line-ending backslash
def s1.ln.pick(
  ww: Bool,
  +cc: Char,
  +xs: String,
  +ys: String,
  hl: {s1.ln(xs, ys) == True{} : Bool}
) -> {s1.ln(D1.g.mlb.char.pick(ww, cc, xs), SCon{cc, ys}) == True{} : Bool}:
  match ww:
    case True{}:
      s1.ln.r(xs, ys, cc, hl)
    case False{}:
      hl

# a multi-line basic body's character, under any trim
def s1.ln.mch(
  tm: D1.GTrim,
  +cc: Char,
  +xs: String,
  +ys: String,
  hl: {s1.ln(xs, ys) == True{} : Bool}
) -> {s1.ln(D1.g.mlb.char(tm, cc, xs), SCon{cc, ys}) == True{} : Bool}:
  match tm:
    case D1.TAll{}:
      s1.ln.pick(D2.abnf.wschar(cc), cc, xs, ys, hl)
    case D1.TFirst{}:
      hl
    case D1.TNone{}:
      hl

# a newline, kept or trimmed
def s1.ln.nlc(
  tm: D1.GTrim,
  +nl: String,
  +xs: String,
  +ys: String,
  hl: {s1.ln(xs, ys) == True{} : Bool}
) -> {s1.ln(D1.g.nl.char(tm, nl, xs), String.append(nl, ys)) == True{} : Bool}:
  match tm:
    case D1.TAll{}:
      s1.ln.app(nl, xs, ys, hl)
    case D1.TFirst{}:
      s1.ln.app(nl, xs, ys, hl)
    case D1.TNone{}:
      s1.ln.same(nl, xs, ys, hl)

# one or two quotes stand for themselves
def s1.ln.q(
  two: Bool,
  +qc: Char,
  +xs: String,
  +ys: String,
  hl: {s1.ln(xs, ys) == True{} : Bool}
) -> {s1.ln(D4.g.quotes.text(two, qc, xs), D4.g.quotes.text(two, qc, ys)) == True{} : Bool}:
  match two:
    case True{}:
      hl
    case False{}:
      hl

# a multi-line basic body, under any trim
def s1.ln.mlb(
  bl: List<&2, D4.GMlb>,
  +tm: D1.GTrim,
  +ys: String
) -> {s1.ln(D1.g.mlb.chars(bl, tm), D4.g.mlb.text(bl, ys)) == True{} : Bool}:
  match bl:
    case []:
      {==}
    case D4.GmChar{kp} <> +rr:
      match kp:
        case D5.KpChar{+cc}:
          s1.ln.mch(tm, cc, D1.g.mlb.chars(rr, D1.g.mlb.char.trim(tm, cc)), D4.g.mlb.text(rr, ys),
            s1.ln.mlb(rr, D1.g.mlb.char.trim(tm, cc), ys))
        case D5.KpEsc{+mm}:
          s1.ln.pc(D5.KpEsc{mm}, D1.g.mlb.chars(rr, D1.TNone{}), D4.g.mlb.text(rr, ys),
            s1.ln.mlb(rr, D1.TNone{}, ys))
        case D5.KpU4{+dd, +cc, +bb, +aa}:
          s1.ln.pc(D5.KpU4{dd, cc, bb, aa}, D1.g.mlb.chars(rr, D1.TNone{}), D4.g.mlb.text(rr, ys),
            s1.ln.mlb(rr, D1.TNone{}, ys))
        case D5.KpU8{+hh, +gg, +ff, +ee, +dd, +cc, +bb, +aa}:
          s1.ln.pc(D5.KpU8{hh, gg, ff, ee, dd, cc, bb, aa}, D1.g.mlb.chars(rr, D1.TNone{}), D4.g.mlb.text(rr,
            ys),
            s1.ln.mlb(rr, D1.TNone{}, ys))
    case D4.GmNewline{+nl} <> +rr:
      s1.ln.nlc(tm, nl, D1.g.mlb.chars(rr, D1.g.nl.trim(tm)), D4.g.mlb.text(rr, ys),
        s1.ln.mlb(rr, D1.g.nl.trim(tm), ys))
    case D4.GmEscapedNl{+w1, +nl, +more} <> +rr:
      s1.ln.r(D1.g.mlb.chars(rr, D1.TAll{}), String.append(w1, String.append(nl, String.append(more,
        D4.g.mlb.text(rr, ys)))), '\\', s1.ln.app(w1, D1.g.mlb.chars(rr, D1.TAll{}), String.append(nl,
        String.append(more, D4.g.mlb.text(rr, ys))), s1.ln.app(nl, D1.g.mlb.chars(rr, D1.TAll{}),
        String.append(more, D4.g.mlb.text(rr, ys)), s1.ln.app(more, D1.g.mlb.chars(rr, D1.TAll{}),
        D4.g.mlb.text(rr, ys), s1.ln.mlb(rr, D1.TAll{}, ys)))))
    case D4.GmQuotes{two} <> +rr:
      s1.ln.q(two, '"', D1.g.mlb.chars(rr, D1.TNone{}), D4.g.mlb.text(rr, ys), s1.ln.mlb(rr, D1.TNone{}, ys))

# a multi-line literal body, under any trim
def s1.ln.mll(
  bl: List<&2, D4.GMll>,
  +tm: D1.GTrim,
  +ys: String
) -> {s1.ln(D1.g.mll.chars(bl, tm), D4.g.mll.text(bl, ys)) == True{} : Bool}:
  match bl:
    case []:
      {==}
    case D4.GlChar{_cc} <> +rr:
      s1.ln.mll(rr, D1.TNone{}, ys)
    case D4.GlNewline{+nl} <> +rr:
      s1.ln.nlc(tm, nl, D1.g.mll.chars(rr, D1.g.nl.trim(tm)), D4.g.mll.text(rr, ys),
        s1.ln.mll(rr, D1.g.nl.trim(tm), ys))
    case D4.GlQuotes{two} <> +rr:
      s1.ln.q(two, '\'', D1.g.mll.chars(rr, D1.TNone{}), D4.g.mll.text(rr, ys), s1.ln.mll(rr, D1.TNone{}, ys))

# a string of every form
def s1.ln.str(
  st: D4.GString,
  +tail: String
) -> {s1.ln(D1.g.str.chars(st), D4.g.str.text(st, tail)) == True{} : Bool}:
  match st:
    case D4.GsBasic{+pl}:
      s1.ln.r(D5.k3.pcs.name(pl), D5.k3.pcs.text(pl, SCon{'"', tail}), '"', s1.ln.pcs(pl, SCon{'"', tail}))
    case D4.GsLiteral{+tx}:
      s1.ln.r(tx, String.append(tx, SCon{'\'', tail}), '\'', s1.ln.pre(tx, SCon{'\'', tail}))
    case D4.GsMlBasic{+nl, +bl}:
      s1.ln.app(SCon{'"', SCon{'"', SCon{'"', nl}}}, D1.g.mlb.chars(bl, D1.g.first.trim(nl)), D4.g.mlb.text(bl,
        SCon{'"', SCon{'"', SCon{'"', tail}}}), s1.ln.mlb(bl, D1.g.first.trim(nl), SCon{'"', SCon{'"', SCon{'"',
        tail}}}))
    case D4.GsMlLiteral{+nl, +bl}:
      s1.ln.app(SCon{'\'', SCon{'\'', SCon{'\'', nl}}}, D1.g.mll.chars(bl, D1.g.first.trim(nl)), D4.g.mll.text(bl,
        SCon{'\'', SCon{'\'', SCon{'\'', tail}}}), s1.ln.mll(bl, D1.g.first.trim(nl), SCon{'\'', SCon{'\'',
        SCon{'\'', tail}}}))

# The whole string, from every value position. The opening delimiter from
# LVal reaches WP-S's span (a basic string), the literal span (a literal
# string) or LTrim (a multi-line string), and the reader of the form takes
# it from there. The value it places holds the characters the derivation
# stands for (g.str.chars).

# a value holding the characters, as the scanner's lemmas say it, is one as
# the law says it
def s1.is.holds(
  vv: T.Val,
  +ss: String,
  hv: M8.sv.Is(vv, ss)
) -> L1.s1.holds(vv, ss):
  match vv:
    case T.VStr{_tx}:
      hv
    case T.VSpan{_src, _nn}:
      hv
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

# the law's rest of the walk is the scanner lemmas'
def s1.rest.done(
  +ss: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  ih: L1.s1.rest(ss, rw, hs, he, ps, sk, ab, rest, PP)
) -> s1.Done(ss, "", rw, hs, he, ps, sk, ab, rest, PP):
  +vv => bk => qk => un => lf => hv => ih(vv, bk, qk, un, lf, s1.is.holds(vv, ss, hv))

# an owned string of the characters pushed onto an empty buffer holds them
def s1.done.fin(
  +ss: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  dn: s1.Done(ss, bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> s1.Fin(bd, rw, hs, he, ps, sk, ab, M3.rev.onto(ss, []), rest, PP):
  b2 => q2 => u2 => l2 => dn(T.VStr{T.buf.str(M3.rev.onto(ss, []))}, b2, q2, u2, l2,
    Equal.sym(String, ss, T.buf.str.go(M3.rev.onto(ss, []), ""), M8.k3.nm(ss)))

# the optional newline right after a multi-line string's opening delimiter
# is dropped: with none the body is read under the first trim, and with one
# under none
def s1.mnl(
  +lit: Bool,
  nl: String,
  +xx: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  hn: {D1.abnf.opt_newline(nl) == True{} : Bool}
) -> {T.doc.read(String.append(nl, xx), T.MScan{M4.fs.st("", rw, hs, he, ps, [], T.LTrim{}, bk, s1.mk(lit), sk, un, lf,
  ab)}) == T.doc.read(xx, T.MScan{s1.ms(D1.g.first.trim(nl), s1.mk(lit), "", rw, hs, he, ps, sk, ab, bk, un, lf, [])})
  : T.Doc}:
  match nl:
    case SNil{}:
      {==}
    case SCon{hh, tt}:
      M1.s1.nl.elim(ys => {T.doc.read(String.append(ys, xx), T.MScan{M4.fs.st("", rw, hs, he, ps, [], T.LTrim{}, bk,
        s1.mk(lit), sk, un, lf, ab)}) == T.doc.read(xx, T.MScan{s1.ms(D1.g.first.trim(ys), s1.mk(lit), "", rw, hs, he,
        ps, sk, ab, bk, un, lf, [])}) : T.Doc}, SCon{hh, tt}, hn, {==}, {==})

# a multi-line literal string's body, after the optional newline
def s1.mll(
  nl: String,
  +bl: List<&2, D4.GMll>,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +rest: String,
  -PP: T.Doc -> Type,
  hn: {D1.abnf.opt_newline(nl) == True{} : Bool},
  hb: {D1.abnf.ml_literal_body(bl, False{}) == True{} : Bool},
  hr: {s1.nq(True{}, rest) == True{} : Bool},
  ih: s1.Fin("", rw, hs, he, ps, sk, ab, M3.rev.onto(D1.g.mll.chars(bl, D1.g.first.trim(nl)), []), rest, PP)
) -> PP(T.doc.read(String.append(nl, D4.g.mll.text(bl, SCon{'\'', SCon{'\'', SCon{'\'', rest}}})), T.MScan{M4.fs.st("",
  rw,
  hs, he, ps, [], T.LTrim{}, bk, T.QMultiLit{}, sk, un, lf, ab)})):
  match nl:
    case SNil{}:
      s1.lb(bl, True{}, False{}, "", rw, hs, he, ps, sk, ab, bk, un, lf, [], rest, PP, hb, hr, ih)
    case SCon{+hh, +tt}:
      M8.pp.step(PP,
        T.doc.read(String.append(SCon{hh, tt}, D4.g.mll.text(bl, SCon{'\'', SCon{'\'', SCon{'\'', rest}}})),
          T.MScan{M4.fs.st("", rw, hs, he, ps, [], T.LTrim{}, bk, T.QMultiLit{}, sk, un, lf, ab)}),
        T.doc.read(D4.g.mll.text(bl, SCon{'\'', SCon{'\'', SCon{'\'', rest}}}), T.MScan{M4.fs.st("", rw, hs, he, ps, [],
          T.LStr{}, bk, T.QMultiLit{}, sk, un, lf, ab)}),
        s1.mnl(True{}, SCon{hh, tt}, D4.g.mll.text(bl, SCon{'\'', SCon{'\'', SCon{'\'', rest}}}), rw, hs, he, ps, sk,
          ab, bk, un, lf, hn),
        s1.lb(bl, False{}, False{}, "", rw, hs, he, ps, sk, ab, bk, un, lf, [], rest, PP, hb, hr, ih))

# a string of every form, from every value position: the rest is read with
# a value holding the characters it stands for placed
def s1.str(
  st: D4.GString,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  +ok: {D1.g.ok.str(st) == True{} : Bool},
  es: {D3.short(D1.g.str.chars(st)) == True{} : Bool},
  +hr: {L1.s1.free(rest) == True{} : Bool},
  dn: s1.Done(D1.g.str.chars(st), "", rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(D4.g.str.text(st, rest), T.MScan{D3.vpos(rw, hs, he, ps, bk, qk, sk, un, lf, ab)})):
  match st:
    case D4.GsBasic{+pl}:
      s1.bo(pl, "", rw, hs, he, ps, bk, sk, un, lf, ab, rest, PP, es,
        Eq.and.left(D1.abnf.basic_string(pl), D1.prose.escapes_scalar(pl), ok),
        Eq.and.right(D1.abnf.basic_string(pl), D1.prose.escapes_scalar(pl), ok), s1.free.sv(rest, hr),
        s1.done.sv(D5.k3.pcs.name(pl), "", rw, hs, he, ps, sk, ab, rest, PP, dn))
    case D4.GsLiteral{+tx}:
      s1.lopen(tx, "", rw, hs, he, ps, bk, sk, un, lf, ab, rest, PP, es, ok, hr, dn)
    case D4.GsMlBasic{+nl, +bl}:
      +h2 = {Eq.and.right(D1.abnf.opt_newline(nl), Bool.and(D1.abnf.ml_basic_body(bl, False{}),
        D1.prose.mlb_escapes_scalar(bl)), ok) : {Bool.and(D1.abnf.ml_basic_body(bl, False{}),
        D1.prose.mlb_escapes_scalar(bl)) == True{} : Bool}}
      M8.pp.step(PP,
        T.doc.read(String.append(nl, D4.g.mlb.text(bl, SCon{'"', SCon{'"', SCon{'"', rest}}})), T.MScan{M4.fs.st("", rw,
          hs, he, ps, [], T.LTrim{}, bk, T.QMulti{}, sk, un, lf, ab)}),
        T.doc.read(D4.g.mlb.text(bl, SCon{'"', SCon{'"', SCon{'"', rest}}}), T.MScan{s1.ms(D1.g.first.trim(nl),
          T.QMulti{}, "", rw, hs, he, ps, sk, ab, bk, un, lf, [])}),
        s1.mnl(False{}, nl, D4.g.mlb.text(bl, SCon{'"', SCon{'"', SCon{'"', rest}}}), rw, hs, he, ps, sk, ab, bk, un,
          lf, Eq.and.left(D1.abnf.opt_newline(nl), Bool.and(D1.abnf.ml_basic_body(bl, False{}),
          D1.prose.mlb_escapes_scalar(bl)), ok)),
        s1.mb(bl, D1.g.first.trim(nl), False{}, "", rw, hs, he, ps, sk, ab, bk, un, lf, [], rest, PP,
          Eq.and.left(D1.abnf.ml_basic_body(bl, False{}), D1.prose.mlb_escapes_scalar(bl), h2),
          Eq.and.right(D1.abnf.ml_basic_body(bl, False{}), D1.prose.mlb_escapes_scalar(bl), h2),
          s1.free.nq(False{}, rest, hr),
          s1.done.fin(D1.g.mlb.chars(bl, D1.g.first.trim(nl)), "", rw, hs, he, ps, sk, ab, rest, PP, dn)))
    case D4.GsMlLiteral{+nl, +bl}:
      s1.mll(nl, bl, rw, hs, he, ps, sk, ab, bk, un, lf, rest, PP,
        Eq.and.left(D1.abnf.opt_newline(nl), D1.abnf.ml_literal_body(bl, False{}), ok),
        Eq.and.right(D1.abnf.opt_newline(nl), D1.abnf.ml_literal_body(bl, False{}), ok),
        s1.free.nq(True{}, rest, hr),
        s1.done.fin(D1.g.mll.chars(bl, D1.g.first.trim(nl)), "", rw, hs, he, ps, sk, ab, rest, PP, dn))

# laws/StringReadsAsDenoted.bend: s1.str, with the law's rest of the walk
def L1.string_reads_as_denoted(st, ok, es, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, hr, PP, ih):
  s1.str(st, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP, ok, es, hr,
    s1.rest.done(D1.g.str.chars(st), rw, hs, he, ps, sk, ab, rest, PP, ih))

# laws/StringReadsAsDenoted.bend: the characters are no more than the text holds (s1.ln.str),
# and a count that does not wrap over the document does not over them
def L1.string_short_in_document(pre, st, rest, h):
  s1.counts.le(D1.g.str.chars(st), String.append(pre, D4.g.str.text(st, rest)), 0,
    s1.ln.app(pre, D1.g.str.chars(st), D4.g.str.text(st, rest), s1.ln.str(st, rest)), h)

# An array's item. In LArr the opening quote is held and read again in LVal,
# with back at LVal: the string is read from that value position.

# the text of a string of every form, read from the state that waits for an
# array's item, is read from the value position the held quote opens
def s1.arr.eq(
  st: D4.GString,
  +rest: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool
) -> {T.doc.read(D4.g.str.text(st, rest), T.MScan{D3.s1.apos(rw, hs, he, ps, bk, qk, sk, un, lf, ab)})
  == T.doc.read(D4.g.str.text(st, rest), T.MScan{D3.vpos(rw, hs, he, ps, T.LVal{}, qk, sk, un, lf, ab)}) : T.Doc}:
  match st:
    case D4.GsMlBasic{_nl, _bl}:
      {==}
    case D4.GsBasic{_pl}:
      {==}
    case D4.GsMlLiteral{_nl, _bl}:
      {==}
    case D4.GsLiteral{_tx}:
      {==}

# laws/StringReadsAsDenoted.bend in an array: s1.arr.eq, then the string from the value position
def L1.string_reads_as_denoted_in_array(st, ok, es, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, hr, PP, ih):
  M8.pp.step(PP,
    T.doc.read(D4.g.str.text(st, rest), T.MScan{D3.s1.apos(rw, hs, he, ps, bk, qk, sk, un, lf, ab)}),
    T.doc.read(D4.g.str.text(st, rest), T.MScan{D3.vpos(rw, hs, he, ps, T.LVal{}, qk, sk, un, lf, ab)}),
    s1.arr.eq(st, rest, rw, hs, he, ps, bk, qk, sk, un, lf, ab),
    s1.str(st, rw, hs, he, ps, T.LVal{}, qk, sk, un, lf, ab, rest, PP, ok, es, hr,
      s1.rest.done(D1.g.str.chars(st), rw, hs, he, ps, sk, ab, rest, PP, ih)))
