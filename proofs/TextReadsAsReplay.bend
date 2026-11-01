# proofs of laws/TextReadsAsReplay.bend
import Base
import ../main.bend as T
import ../src/eq.bend as Eq
import ../laws/BareWordReadsOn.bend as L1
import ../laws/BooleanIsBareWord.bend as L2
import ../laws/DateTimeReadExactly.bend as L3
import ../laws/DefinesEachTableOnce.bend as L4
import ../laws/ErrorStays.bend as L5
import ../laws/FloatReadExactly.bend as L6
import ../laws/GValTextTail.bend as L7
import ../laws/IntegerReadExactly.bend as L8
import ../laws/KeyNameIsItsCharacters.bend as L9
import ../laws/StringReadsAsDenoted.bend as L10
import ../laws/TextReadsAsReplay.bend as Laws
import ../laws/ValueReadsBack.bend as L11
import ../laws/defs/AbnfGrammar.bend as D1
import ../laws/defs/AbnfWhitespace.bend as D2
import ../laws/defs/BareValueGrammar.bend as D3
import ../laws/defs/BlankAndControlChars.bend as D4
import ../laws/defs/DerivationReplay.bend as D5
import ../laws/defs/GrammarDerivations.bend as D6
import ../laws/defs/KeySegmentSpelling.bend as D7
import ../laws/defs/ScalarReadbackScan.bend as D8
import ./lemmas/BareValueScan.bend as M1
import ./lemmas/BareWordInArray.bend as M2
import ./lemmas/BareWordReadsOn.bend as M3
import ./lemmas/BareWordRefusal.bend as M4
import ./lemmas/BasicStringControls.bend as M5
import ./lemmas/BooleanIsBareWord.bend as M6
import ./lemmas/ControlEscapeText.bend as M7
import ./lemmas/DateTimeBareWord.bend as M8
import ./lemmas/DecimalArithmetic.bend as M9
import ./lemmas/ErrorPersistence.bend as M10
import ./lemmas/ExpressionLineReplay.bend as M11
import ./lemmas/FailedWalkNameCompare.bend as M12
import ./lemmas/FloatIsBareWord.bend as M13
import ./lemmas/FreshNamesInRows.bend as M14
import ./lemmas/GrammarTextParts.bend as M15
import ./lemmas/HeaderKeyScan.bend as M16
import ./lemmas/IntegerIsBareWord.bend as M17
import ./lemmas/KeyvalKeyScan.bend as M18
import ./lemmas/PickAndDigitSteps.bend as M19
import ./lemmas/QuotedKeySegments.bend as M20
import ./lemmas/StringBodyWalk.bend as M21
import ./lemmas/ValueTextReadback.bend as M22
import ./lemmas/WellFormedTextWalk.bend as M23

# the quotient of a U32 by ten
def q10(+nn: U32) -> U32:
  U32.div(nn, 10)

# WP-A: KEY-3's key and header readers over a motive. KEY-3 states them with
# the rest of the text equal to one document for every back, uni and left the
# key leaves; a document with values in it is known only as own reads it, so
# the readers are taken over a motive PP of the document instead, the same
# proofs with each equation to the goal read as PP of its side (kx.*).

# what holds of a document holds of one equal to it
def kx.tr(
  a: T.Doc,
  b: T.Doc,
  -PP: T.Doc -> Type,
  e: {a == b : T.Doc},
  k: PP(b)
) -> PP(a):
  %Equal.sym(T.Doc, a, b, e) : PP(_)
  k

# the rest of the text read from the segment with buf in its buffer, whatever
# back, uni and left are
def kx.Then(
  +hd: Bool,
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
    PP(T.doc.read(rest, T.MScan{M16.k3.q(hd, rw, hs, he, ps, sk, ab, b2, u2, l2, buf)}))

# a two-character escape pushes the character it stands for and leaves back
# at the segment's state
def kx.esc(
  mm: D7.KMark,
  +hd: Bool,
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
  ih: kx.Then(hd, rw, hs, he, ps, sk, ab, D7.k3.mark.dec(mm) <> buf, rest, PP)
) -> PP(T.doc.read(SCon{'\\', SCon{D7.k3.mark.char(mm), rest}}, T.MScan{M16.k3.q(hd, rw, hs, he, ps, sk, ab, bk, un,
  lf, buf)})):
  match mm hd:
    case D7.KmQuote{} False{}:
      ih(T.LKeyQ{}, un, lf)
    case D7.KmQuote{} True{}:
      ih(T.LHeadQ{}, un, lf)
    case D7.KmBack{} False{}:
      ih(T.LKeyQ{}, un, lf)
    case D7.KmBack{} True{}:
      ih(T.LHeadQ{}, un, lf)
    case D7.KmB{} False{}:
      ih(T.LKeyQ{}, un, lf)
    case D7.KmB{} True{}:
      ih(T.LHeadQ{}, un, lf)
    case D7.KmF{} False{}:
      ih(T.LKeyQ{}, un, lf)
    case D7.KmF{} True{}:
      ih(T.LHeadQ{}, un, lf)
    case D7.KmN{} False{}:
      ih(T.LKeyQ{}, un, lf)
    case D7.KmN{} True{}:
      ih(T.LHeadQ{}, un, lf)
    case D7.KmR{} False{}:
      ih(T.LKeyQ{}, un, lf)
    case D7.KmR{} True{}:
      ih(T.LHeadQ{}, un, lf)
    case D7.KmT{} False{}:
      ih(T.LKeyQ{}, un, lf)
    case D7.KmT{} True{}:
      ih(T.LHeadQ{}, un, lf)

# a raw tab is pushed as itself
def kx.tab(
  +hd: Bool,
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
  ih: kx.Then(hd, rw, hs, he, ps, sk, ab, Chr{9} <> buf, rest, PP)
) -> PP(T.doc.read(SCon{Chr{9}, rest}, T.MScan{M16.k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)})):
  match hd:
    case False{}:
      ih(bk, un, lf)
    case True{}:
      ih(bk, un, lf)

# a character written as itself that is no quote, no backslash and no
# control is pushed, and back, uni and left stay
def kx.plain(
  +uu: U32,
  +hd: Bool,
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
  +e34: {U32.is_eq(uu, 34) == False{} : Bool},
  +e92: {U32.is_eq(uu, 92) == False{} : Bool},
  +ec: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool},
  ih: kx.Then(hd, rw, hs, he, ps, sk, ab, Chr{uu} <> buf, rest, PP)
) -> PP(T.doc.read(SCon{Chr{uu}, rest}, T.MScan{M16.k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)})):
  +e10 = {M7.ctl.off(uu, 10, ec, {==}) : {U32.is_eq(uu, 10) == False{} : Bool}}
  +e13 = {M7.ctl.off(uu, 13, ec, {==}) : {U32.is_eq(uu, 13) == False{} : Bool}}
  fast = {Equal.sym(T.St, T.read.fast(M16.k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu}),
    M16.k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf),
    Equal.trans(T.St, T.read.fast(M16.k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu}),
    T.read.once2(T.lex.kq.go(U32.is_eq(uu, 34), U32.is_eq(uu, 92), True{}, Bool.or(U32.is_eq(uu, 10),
    U32.is_eq(uu, 13)), M16.k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu}, M20.qs.close(hd),
        M19.qs.lex(hd))),
    M16.k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf),
    M16.k3.fast(uu, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf),
    M16.k3.go(U32.is_eq(uu, 34), U32.is_eq(uu, 92), Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)), uu, hd, rw, hs, he,
      ps, sk, ab, bk, un, lf, buf, e34, e92, M22.or.ff(U32.is_eq(uu, 10), U32.is_eq(uu, 13), e10, e13), ec)))
    : M16.k3.Fast(uu, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)}
  %M16.k3.scq(U32.is_eq(uu, 34), U32.is_eq(uu, 39), U32.is_eq(uu, 13), uu, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf,
    e34, e13, fast) : PP(T.doc.read(rest, _))
  ih(bk, un, lf)

# `\u` and four digits push the character they name, and leave back at the
# segment's state and uni and left at 0
def kx.u4(
  +dd: D7.KHex,
  +cc: D7.KHex,
  +bb: D7.KHex,
  +aa: D7.KHex,
  +hd: Bool,
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
  eo: {D7.k3.scalar(D7.k3.hex4(dd, cc, bb, aa)) == True{} : Bool},
  ih: kx.Then(hd, rw, hs, he, ps, sk, ab, Chr{D7.k3.hex4(dd, cc, bb, aa)} <> buf, rest, PP)
) -> PP(T.doc.read(D7.k3.pc.text(D7.KpU4{dd, cc, bb, aa}, rest), T.MScan{M16.k3.q(hd, rw, hs, he, ps, sk, ab, bk, un,
  lf, buf)})):
  %M16.k3.hx.open(False{}, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, D7.k3.hex4.text(dd, cc, bb, aa, rest))
    : PP(_)
  %M16.k3.hx.rmid(dd, hd, rw, hs, he, ps, sk, ab, M19.qs.lex(hd), 0, 4, buf, SCon{D7.k3.hex.char(cc),
    SCon{D7.k3.hex.char(bb), SCon{D7.k3.hex.char(aa), rest}}}, {==}) : PP(_)
  %M16.k3.hx.rmid(cc, hd, rw, hs, he, ps, sk, ab, M19.qs.lex(hd), D7.k3.hex.acc(0, dd), 3, buf,
    SCon{D7.k3.hex.char(bb), SCon{D7.k3.hex.char(aa), rest}}, {==}) : PP(_)
  %M16.k3.hx.rmid(bb, hd, rw, hs, he, ps, sk, ab, M19.qs.lex(hd), D7.k3.hex.acc(D7.k3.hex.acc(0, dd), cc), 2, buf,
    SCon{D7.k3.hex.char(aa), rest}, {==}) : PP(_)
  %M16.k3.hx.rlast(aa, hd, rw, hs, he, ps, sk, ab, M19.qs.lex(hd), D7.k3.hex.acc(D7.k3.hex.acc(D7.k3.hex.acc(0, dd),
    cc), bb), 1, buf, rest, {==}, eo) : PP(_)
  ih(M19.qs.lex(hd), 0, 0)

# `\U` and eight digits push the character they name, and leave back at the
# segment's state and uni and left at 0
def kx.u8(
  +hh: D7.KHex,
  +gg: D7.KHex,
  +ff: D7.KHex,
  +ee: D7.KHex,
  +dd: D7.KHex,
  +cc: D7.KHex,
  +bb: D7.KHex,
  +aa: D7.KHex,
  +hd: Bool,
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
  eo: {D7.k3.scalar(D7.k3.hex8(hh, gg, ff, ee, dd, cc, bb, aa)) == True{} : Bool},
  ih: kx.Then(hd, rw, hs, he, ps, sk, ab, Chr{D7.k3.hex8(hh, gg, ff, ee, dd, cc, bb, aa)} <> buf, rest, PP)
) -> PP(T.doc.read(D7.k3.pc.text(D7.KpU8{hh, gg, ff, ee, dd, cc, bb, aa}, rest), T.MScan{M16.k3.q(hd, rw, hs, he, ps,
  sk, ab, bk, un, lf, buf)})):
  +t4 = D7.k3.hex4.text(dd, cc, bb, aa, rest)
  +a1 = D7.k3.hex.acc(0, hh)
  +a2 = D7.k3.hex.acc(a1, gg)
  +a3 = D7.k3.hex.acc(a2, ff)
  +a4 = D7.k3.hex.acc(a3, ee)
  +a5 = D7.k3.hex.acc(a4, dd)
  +a6 = D7.k3.hex.acc(a5, cc)
  +a7 = D7.k3.hex.acc(a6, bb)
  +sl = M19.qs.lex(hd)
  %M16.k3.hx.open(True{}, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, D7.k3.hex4.text(hh, gg, ff, ee, t4))
    : PP(_)
  %M16.k3.hx.rmid(hh, hd, rw, hs, he, ps, sk, ab, sl, 0, 8, buf, SCon{D7.k3.hex.char(gg), SCon{D7.k3.hex.char(ff),
    SCon{D7.k3.hex.char(ee), t4}}}, {==}) : PP(_)
  %M16.k3.hx.rmid(gg, hd, rw, hs, he, ps, sk, ab, sl, a1, 7, buf, SCon{D7.k3.hex.char(ff), SCon{D7.k3.hex.char(ee),
    t4}}, {==}) : PP(_)
  %M16.k3.hx.rmid(ff, hd, rw, hs, he, ps, sk, ab, sl, a2, 6, buf, SCon{D7.k3.hex.char(ee), t4}, {==})
    : PP(_)
  %M16.k3.hx.rmid(ee, hd, rw, hs, he, ps, sk, ab, sl, a3, 5, buf, t4, {==}) : PP(_)
  %M16.k3.hx.rmid(dd, hd, rw, hs, he, ps, sk, ab, sl, a4, 4, buf, SCon{D7.k3.hex.char(cc),
    SCon{D7.k3.hex.char(bb), SCon{D7.k3.hex.char(aa), rest}}}, {==}) : PP(_)
  %M16.k3.hx.rmid(cc, hd, rw, hs, he, ps, sk, ab, sl, a5, 3, buf, SCon{D7.k3.hex.char(bb), SCon{D7.k3.hex.char(aa),
    rest}}, {==}) : PP(_)
  %M16.k3.hx.rmid(bb, hd, rw, hs, he, ps, sk, ab, sl, a6, 2, buf, SCon{D7.k3.hex.char(aa), rest}, {==})
    : PP(_)
  %M16.k3.hx.rlast(aa, hd, rw, hs, he, ps, sk, ab, sl, a7, 1, buf, rest, {==}, eo) : PP(_)
  ih(sl, 0, 0)

# a character written as itself read from the segment, then the rest
def kx.PcG(
  +cc: Char,
  +hd: Bool,
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
  -PP: T.Doc -> Type
) -> Type:
  kx.Then(hd, rw, hs, he, ps, sk, ab, cc <> buf, rest, PP) ->
    PP(T.doc.read(SCon{cc, rest}, T.MScan{M16.k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)}))

# a character written as itself: a tab, or one that is no quote, no
# backslash and no control
def kx.chr(
  t9: Bool,
  +uu: U32,
  +e9: {U32.is_eq(uu, 9) == t9 : Bool},
  +hd: Bool,
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
  +eb: {L9.k3.bchar(Chr{uu}) == True{} : Bool}
) -> kx.PcG(Chr{uu}, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP):
  match t9:
    case True{}:
      %Equal.sym(Char, Chr{uu}, Chr{9}, Eq.u32_eq(uu, 9, e9)) : kx.PcG(_, hd, rw, hs, he, ps, sk, ab, bk, un, lf,
        buf, rest, PP)
      ih => kx.tab(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP, ih)
    case False{}:
      +tq = U32.is_eq(uu, 34)
      +tb = U32.is_eq(uu, 92)
      +tc = Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127))
      +tt = U32.is_eq(uu, 9)
      ih => kx.plain(uu, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP, M16.k3.bc.q(tq, tb, tc, tt, eb),
        M16.k3.bc.b(tq, tb, tc, tt, eb), M16.k3.bc.c(tq, tb, tc, tt, e9, eb), ih)

# one piece a basic string may hold pushes the character it stands for
def kx.pc(
  pp: D7.KPiece,
  +hd: Bool,
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
  eo: {L9.k3.pc.ok(pp) == True{} : Bool},
  ih: kx.Then(hd, rw, hs, he, ps, sk, ab, D7.k3.pc.char(pp) <> buf, rest, PP)
) -> PP(T.doc.read(D7.k3.pc.text(pp, rest), T.MScan{M16.k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)})):
  match pp:
    case D7.KpChar{cc}:
      match cc:
        case Chr{+uu}:
          kx.chr(U32.is_eq(uu, 9), uu, {==}, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP, eo)(ih)
    case D7.KpEsc{mm}:
      kx.esc(mm, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP, ih)
    case D7.KpU4{+dd, +cc, +bb, +aa}:
      kx.u4(dd, cc, bb, aa, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP, eo, ih)
    case D7.KpU8{+hh, +gg, +ff, +ee, +dd, +cc, +bb, +aa}:
      kx.u8(hh, gg, ff, ee, dd, cc, bb, aa, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP, eo, ih)

# every piece of a list a basic string may hold, in order: the rest is read
# with their characters pushed, from wherever the last piece left back, uni
# and left
def kx.pcs(
  pl: List<&2, D7.KPiece>,
  +hd: Bool,
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
  +eo: {L9.k3.pcs.ok(pl) == True{} : Bool},
  ih: kx.Then(hd, rw, hs, he, ps, sk, ab, M14.rev.onto(D7.k3.pcs.name(pl), buf), rest, PP)
) -> PP(T.doc.read(D7.k3.pcs.text(pl, rest), T.MScan{M16.k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)})):
  match pl:
    case []:
      ih(bk, un, lf)
    case +pp <> +pr:
      kx.pc(pp, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, D7.k3.pcs.text(pr, rest), PP,
        Eq.and.left(L9.k3.pc.ok(pp), L9.k3.pcs.ok(pr), eo),
        +b2 => +u2 => +l2 => kx.pcs(pr, hd, rw, hs, he, ps, sk, ab, b2, u2, l2, D7.k3.pc.char(pp) <> buf, rest,
          PP, Eq.and.right(L9.k3.pc.ok(pp), L9.k3.pcs.ok(pr), eo), ih))

# the rest of the text read after a segment and what ends it, from every
# back, qkind, uni and left
def kx.KT(
  +cl: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  @b2: T.Lex -> @q2: T.QKind -> @u2: U32 -> @l2: U32 ->
    PP(T.doc.read(rest, T.MScan{M16.k3.w(rw, hs, he, ps, [], M18.k3.aft(cl), b2, q2, sk, u2, l2, ab)}))

# a segment's name pushed onto parts, then blank space and a dot or `=`: the
# rest is read from there
def kx.fin(
  +nm: String,
  +bf: List<&2, Char>,
  en: {nm == T.buf.str(bf) : String},
  +gs: List<&2, Bool>,
  +cl: Bool,
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
  ih: kx.KT(cl, rw, hs, he, nm <> ps, sk, ab, rest, PP)
) -> PP(T.doc.read(String.append(D4.gap(gs), SCon{M18.k3.dl(cl), rest}), T.MScan{M16.k3.w(rw, hs, he,
    T.buf.str(bf) <> ps,
  [], T.LAfter{}, bk, qk, sk, un, lf, ab)})):
  %M18.k3.agap(gs, SCon{M18.k3.dl(cl), rest}, rw, hs, he, T.buf.str(bf) <> ps, bk, qk, sk, un, lf, ab) : PP(_)
  %M18.k3.adl(cl, rw, hs, he, T.buf.str(bf) <> ps, bk, qk, sk, un, lf, ab, rest) : PP(_)
  %en : PP(T.doc.read(rest, T.MScan{M16.k3.w(rw, hs, he, _ <> ps, [], M18.k3.aft(cl), bk, qk, sk, un, lf, ab)}))
  ih(bk, qk, un, lf)

# a bare segment, its blank space and a dot or `=`: the rest is read with the
# segment pushed, and back, qkind, uni and left as they were
def kx.bseg(
  +xx: U32,
  +tt: String,
  +gs: List<&2, Bool>,
  +cl: Bool,
  +dt: Bool,
  +at: L9.KPos,
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
  +ee: {T.bare.all.step(T.bare.at(Chr{xx}), _u => T.bare.all(String.to_list(tt))) == True{} : Bool},
  ih: kx.KT(cl, rw, hs, he, SCon{Chr{xx}, tt} <> M16.k3.ps0(dt, ps), sk, ab, rest, PP)
) -> PP(T.doc.read(String.append(SCon{Chr{xx}, tt}, String.append(D4.gap(gs), SCon{M18.k3.dl(cl), rest})),
  T.MScan{M16.k3.w(rw, hs, he, M16.k3.ps0(dt, ps), [], M18.k3.lex0(dt, at), bk, qk, sk, un, lf, ab)})):
  %M18.k3.b1(dt, at, rw, hs, he, ps, bk, qk, sk, un, lf, ab, xx, M22.ball.head(T.bare.at(Chr{xx}), String.to_list(tt),
      ee))
    : PP(T.doc.read(String.append(tt, String.append(D4.gap(gs), SCon{M18.k3.dl(cl), rest})), _))
  %M18.k3.bbody(tt, String.append(D4.gap(gs), SCon{M18.k3.dl(cl), rest}), rw, hs, he, M16.k3.ps0(dt, ps), [Chr{xx}],
      bk, qk, sk,
    un, lf, ab, M22.ball.tail(T.bare.at(Chr{xx}),
    String.to_list(tt), ee)) : PP(_)
  %M18.k3.bend(gs, cl, rw, hs, he, M16.k3.ps0(dt, ps), M14.rev.onto(tt, [Chr{xx}]), bk, qk, sk, un, lf, ab, rest,
      M22.rev.full(tt,
    Chr{xx},
    [])) : PP(_)
  %Equal.sym(String, T.buf.str(M14.rev.onto(tt, [Chr{xx}])), SCon{Chr{xx}, tt}, M22.wh.bname(xx,
      tt)) : PP(T.doc.read(rest,
    T.MScan{M16.k3.w(rw, hs, he, _ <> M16.k3.ps0(dt, ps), [], M18.k3.aft(cl), bk, qk, sk, un, lf, ab)}))
  ih(bk, qk, un, lf)

# a basic segment of pieces, its blank space and a dot or `=`: the rest is
# read with the segment pushed under the characters the pieces stand for,
# from wherever the last piece left back, uni and left
def kx.qseg(
  +pl: List<&2, D7.KPiece>,
  +gs: List<&2, Bool>,
  +cl: Bool,
  +dt: Bool,
  +at: L9.KPos,
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
  eo: {L9.k3.pcs.ok(pl) == True{} : Bool},
  ih: kx.KT(cl, rw, hs, he, D7.k3.pcs.name(pl) <> M16.k3.ps0(dt, ps), sk, ab, rest, PP)
) -> PP(T.doc.read(SCon{'"', D7.k3.pcs.text(pl, SCon{'"', String.append(D4.gap(gs), SCon{M18.k3.dl(cl), rest})})},
  T.MScan{M16.k3.w(rw, hs, he, M16.k3.ps0(dt, ps), [], M18.k3.lex0(dt, at), bk, qk, sk, un, lf, ab)})):
  %M18.k3.qopen(dt, at, rw, hs, he, ps, bk, qk, sk, un, lf, ab) : PP(T.doc.read(D7.k3.pcs.text(pl, SCon{'"',
    String.append(D4.gap(gs), SCon{M18.k3.dl(cl), rest})}),
    _))
  kx.pcs(pl, False{}, rw, hs, he, M16.k3.ps0(dt, ps), sk, ab, bk, un, lf, [], SCon{'"', String.append(D4.gap(gs),
    SCon{M18.k3.dl(cl), rest})}, PP, eo, +b2 => +u2 => +l2 =>
    kx.fin(D7.k3.pcs.name(pl), M14.rev.onto(D7.k3.pcs.name(pl), []), M22.k3.nm(D7.k3.pcs.name(pl)), gs, cl, rw, hs, he,
      M16.k3.ps0(dt, ps), b2, T.QBasic{}, sk, u2, l2, ab, rest, PP, ih))

# a literal segment, its blank space and a dot or `=`: the rest is read with
# the segment pushed under its characters, and back, uni and left as they
# were
def kx.lseg(
  +name: String,
  +gs: List<&2, Bool>,
  +cl: Bool,
  +dt: Bool,
  +at: L9.KPos,
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
  el: {L9.lit.text(name) == True{} : Bool},
  ih: kx.KT(cl, rw, hs, he, name <> M16.k3.ps0(dt, ps), sk, ab, rest, PP)
) -> PP(T.doc.read(SCon{'\'', String.append(name, SCon{'\'', String.append(D4.gap(gs), SCon{M18.k3.dl(cl), rest})})},
  T.MScan{M16.k3.w(rw, hs, he, M16.k3.ps0(dt, ps), [], M18.k3.lex0(dt, at), bk, qk, sk, un, lf, ab)})):
  %M18.k3.lopen(dt, at, rw, hs, he, ps, bk, qk, sk, un, lf, ab) : PP(T.doc.read(String.append(name, SCon{'\'',
    String.append(D4.gap(gs), SCon{M18.k3.dl(cl), rest})}), _))
  kx.tr( T.doc.read(String.append(name, SCon{'\'', String.append(D4.gap(gs), SCon{M18.k3.dl(cl), rest})}),
    T.MScan{M16.k3.l(False{}, rw, hs, he, M16.k3.ps0(dt, ps),
    sk, ab, bk, un, lf, [])}), T.doc.read(SCon{'\'', String.append(D4.gap(gs), SCon{M18.k3.dl(cl), rest})},
      T.MScan{M16.k3.l(False{}, rw, hs, he, M16.k3.ps0(dt, ps), sk, ab, bk,
    un, lf, M14.rev.onto(name, []))}), PP,
    M16.k3.l.body(name, SCon{'\'', String.append(D4.gap(gs), SCon{M18.k3.dl(cl), rest})}, False{}, rw, hs, he,
        M16.k3.ps0(dt,
      ps), sk, ab, bk, un, lf, [], el),
    kx.fin(name, M14.rev.onto(name, []), M22.k3.nm(name), gs, cl, rw, hs, he, M16.k3.ps0(dt, ps), bk, T.QLit{}, sk, un,
        lf, ab,
      rest, PP,
      ih))

# a segment spelled any way toml.abnf allows, its blank space and a dot or
# `=`
def kx.seg(
  sg: D7.KSeg,
  +gs: List<&2, Bool>,
  +cl: Bool,
  +dt: Bool,
  +at: L9.KPos,
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
  eo: {L9.k3.seg.ok(sg) == True{} : Bool},
  ih: kx.KT(cl, rw, hs, he, D7.k3.seg.name(sg) <> M16.k3.ps0(dt, ps), sk, ab, rest, PP)
) -> PP(T.doc.read(D7.k3.seg.text(sg, String.append(D4.gap(gs), SCon{M18.k3.dl(cl), rest})), T.MScan{M16.k3.w(rw, hs,
    he,
  M16.k3.ps0(dt, ps), [], M18.k3.lex0(dt, at), bk, qk, sk, un, lf, ab)})):
  match sg:
    case D7.KsBare{name}:
      match name:
        case SNil{}:
          Eq.bit.absurd(&1, PP(T.doc.read(String.append(SNil{}, String.append(D4.gap(gs), SCon{M18.k3.dl(cl), rest})),
            T.MScan{M16.k3.w(rw, hs, he, M16.k3.ps0(dt, ps), [], M18.k3.lex0(dt, at), bk, qk, sk, un, lf, ab)})),
              eo)
        case SCon{hh, +tt}:
          match hh:
            case Chr{+xx}:
              kx.bseg(xx, tt, gs, cl, dt, at, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP, eo, ih)
    case D7.KsBasic{+pl}:
      kx.qseg(pl, gs, cl, dt, at, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP, eo, ih)
    case D7.KsLit{+name}:
      kx.lseg(name, gs, cl, dt, at, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP, eo, ih)

# a dotted key's segments, then blank space and `=`: the rest is read with
# every segment pushed onto parts, newest first
def kx.keys(
  ds: List<&2, L9.KDot>,
  +last: D7.KSeg,
  +g: List<&2, Bool>,
  +dt: Bool,
  +at: L9.KPos,
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
  +eo: {L9.k3.dk.ok(ds, last) == True{} : Bool},
  ih: kx.KT(True{}, rw, hs, he, M16.k3.acc(ds, last, dt, ps), sk, ab, rest, PP)
) -> PP(T.doc.read(L9.k3.dk.text(ds, last, String.append(D4.gap(g), SCon{'=', rest})), T.MScan{M16.k3.w(rw, hs, he,
  M16.k3.ps0(dt, ps), [], M18.k3.lex0(dt, at), bk, qk, sk, un, lf, ab)})):
  match ds:
    case []:
      kx.seg(last, g, True{}, dt, at, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, PP, eo, ih)
    case L9.KDot{+sg, g1, +g2} <> +dr:
      kx.seg(sg, g1, False{}, dt, at, rw, hs, he, ps, bk, qk, sk, un, lf, ab, String.append(D4.gap(g2),
        L9.k3.dk.text(dr, last, String.append(D4.gap(g), SCon{'=', rest}))), PP, Eq.and.left(L9.k3.seg.ok(sg),
        L9.k3.dk.ok(dr, last), eo), +b2 => +q2 => +u2 => +l2 =>
        %M18.k3.dgap(g2, L9.k3.dk.text(dr, last, String.append(D4.gap(g), SCon{'=', rest})), rw, hs, he,
          D7.k3.seg.name(sg) <> M16.k3.ps0(dt, ps), b2, q2, sk, u2, l2, ab) : PP(_)
        kx.keys(dr, last, g, True{}, at, rw, hs, he, D7.k3.seg.name(sg) <> M16.k3.ps0(dt, ps), b2, q2, sk, u2, l2, ab,
          rest, PP,
          Eq.and.right(L9.k3.seg.ok(sg), L9.k3.dk.ok(dr, last), eo), ih))

# the rest of the text after a header segment, read from every back, qkind,
# uni and left
def kx.HT(
  +cl: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  @b2: T.Lex -> @q2: T.QKind -> @u2: U32 -> @l2: U32 ->
    PP(T.doc.read(rest, T.MScan{M16.k3.haft(cl, rw, hs, he, ps, b2, q2, u2, l2, ab)}))

# a header segment's name pushed onto parts, then blank space and a dot or
# the bracket: the rest is read from there
def kx.hfin(
  +nm: String,
  +bf: List<&2, Char>,
  en: {nm == T.buf.str(bf) : String},
  +gs: List<&2, Bool>,
  +cl: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  ih: kx.HT(cl, rw, hs, he, nm <> ps, ab, rest, PP)
) -> PP(T.doc.read(String.append(D4.gap(gs), SCon{M16.k3.hdl(cl), rest}), T.MScan{M16.k3.w(rw, hs, he,
    T.buf.str(bf) <> ps,
  [], T.LHeadGap{}, bk, qk, [], un, lf, ab)})):
  %M16.k3.hgap(gs, SCon{M16.k3.hdl(cl), rest}, rw, hs, he, T.buf.str(bf) <> ps, bk, qk, un, lf, ab) : PP(_)
  %M16.k3.hgdl(cl, rw, hs, he, T.buf.str(bf) <> ps, bk, qk, un, lf, ab, rest) : PP(_)
  %en : PP(T.doc.read(rest, T.MScan{M16.k3.haft(cl, rw, hs, he, _ <> ps, bk, qk, un, lf, ab)}))
  ih(bk, qk, un, lf)

# a bare header segment, its blank space and a dot or the bracket
def kx.hbseg(
  +xx: U32,
  +tt: String,
  +gs: List<&2, Bool>,
  +cl: Bool,
  +dt: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  +ee: {T.bare.all.step(T.bare.at(Chr{xx}), _u => T.bare.all(String.to_list(tt))) == True{} : Bool},
  ih: kx.HT(cl, rw, hs, he, SCon{Chr{xx}, tt} <> M16.k3.ps0(dt, ps), ab, rest, PP)
) -> PP(T.doc.read(String.append(SCon{Chr{xx}, tt}, String.append(D4.gap(gs), SCon{M16.k3.hdl(cl), rest})),
  T.MScan{M16.k3.w(rw, hs, he, M16.k3.ps0(dt, ps), [], M16.k3.hlex0(dt), bk, qk, [], un, lf, ab)})):
  %M16.k3.hb1(dt, rw, hs, he, ps, bk, qk, un, lf, ab, xx, M22.ball.head(T.bare.at(Chr{xx}), String.to_list(tt), ee))
    : PP(T.doc.read(String.append(tt, String.append(D4.gap(gs), SCon{M16.k3.hdl(cl), rest})), _))
  %M16.k3.hbbody(tt, String.append(D4.gap(gs), SCon{M16.k3.hdl(cl), rest}), rw, hs, he, M16.k3.ps0(dt, ps), Chr{xx},
      [], bk, qk,
    un, lf, ab, M22.ball.tail(T.bare.at(Chr{xx}),
    String.to_list(tt), ee)) : PP(_)
  %M16.k3.hbend(gs, cl, rw, hs, he, M16.k3.ps0(dt, ps), M14.rev.onto(tt, [Chr{xx}]), bk, qk, un, lf, ab, rest,
      M22.rev.full(tt,
    Chr{xx}, []))
    : PP(_)
  %Equal.sym(String, T.buf.str(M14.rev.onto(tt, [Chr{xx}])), SCon{Chr{xx}, tt}, M22.wh.bname(xx,
      tt)) : PP(T.doc.read(rest,
    T.MScan{M16.k3.haft(cl, rw, hs, he, _ <> M16.k3.ps0(dt, ps), bk, qk, un, lf, ab)}))
  ih(bk, qk, un, lf)

# a basic header segment of pieces, its blank space and a dot or the
# bracket
def kx.hqseg(
  +pl: List<&2, D7.KPiece>,
  +gs: List<&2, Bool>,
  +cl: Bool,
  +dt: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  eo: {L9.k3.pcs.ok(pl) == True{} : Bool},
  ih: kx.HT(cl, rw, hs, he, D7.k3.pcs.name(pl) <> M16.k3.ps0(dt, ps), ab, rest, PP)
) -> PP(T.doc.read(SCon{'"', D7.k3.pcs.text(pl, SCon{'"', String.append(D4.gap(gs), SCon{M16.k3.hdl(cl), rest})})},
  T.MScan{M16.k3.w(rw, hs, he, M16.k3.ps0(dt, ps), [], M16.k3.hlex0(dt), bk, qk, [], un, lf, ab)})):
  %M16.k3.hqopen(dt, rw, hs, he, ps, bk, qk, un, lf, ab) : PP(T.doc.read(D7.k3.pcs.text(pl, SCon{'"',
    String.append(D4.gap(gs), SCon{M16.k3.hdl(cl), rest})}), _))
  kx.pcs(pl, True{}, rw, hs, he, M16.k3.ps0(dt, ps), [], ab, bk, un, lf, [], SCon{'"', String.append(D4.gap(gs),
    SCon{M16.k3.hdl(cl), rest})}, PP, eo, +b2 => +u2 => +l2 =>
    kx.hfin(D7.k3.pcs.name(pl), M14.rev.onto(D7.k3.pcs.name(pl), []), M22.k3.nm(D7.k3.pcs.name(pl)), gs, cl, rw, hs,
      he, M16.k3.ps0(dt, ps), b2, T.QBasic{}, u2, l2, ab, rest, PP, ih))

# a literal header segment, its blank space and a dot or the bracket
def kx.hlseg(
  +name: String,
  +gs: List<&2, Bool>,
  +cl: Bool,
  +dt: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  el: {L9.lit.text(name) == True{} : Bool},
  ih: kx.HT(cl, rw, hs, he, name <> M16.k3.ps0(dt, ps), ab, rest, PP)
) -> PP(T.doc.read(SCon{'\'', String.append(name, SCon{'\'', String.append(D4.gap(gs), SCon{M16.k3.hdl(cl), rest})})},
  T.MScan{M16.k3.w(rw, hs, he, M16.k3.ps0(dt, ps), [], M16.k3.hlex0(dt), bk, qk, [], un, lf, ab)})):
  %M16.k3.hlopen(dt, rw, hs, he, ps, bk, qk, un, lf, ab) : PP(T.doc.read(String.append(name, SCon{'\'',
    String.append(D4.gap(gs), SCon{M16.k3.hdl(cl), rest})}), _))
  kx.tr( T.doc.read(String.append(name, SCon{'\'', String.append(D4.gap(gs), SCon{M16.k3.hdl(cl), rest})}),
    T.MScan{M16.k3.l(True{}, rw, hs, he, M16.k3.ps0(dt, ps),
    [], ab, bk, un, lf, [])}), T.doc.read(SCon{'\'', String.append(D4.gap(gs), SCon{M16.k3.hdl(cl), rest})},
      T.MScan{M16.k3.l(True{}, rw, hs, he, M16.k3.ps0(dt, ps), [], ab, bk,
    un, lf, M14.rev.onto(name, []))}), PP,
    M16.k3.l.body(name, SCon{'\'', String.append(D4.gap(gs), SCon{M16.k3.hdl(cl), rest})}, True{}, rw, hs, he,
        M16.k3.ps0(dt,
      ps), [], ab, bk, un, lf, [], el),
    kx.hfin(name, M14.rev.onto(name, []), M22.k3.nm(name), gs, cl, rw, hs, he, M16.k3.ps0(dt, ps), bk, T.QLit{}, un,
        lf, ab, rest,
      PP,
      ih))

# a header segment spelled any way toml.abnf allows, its blank space and a
# dot or the bracket
def kx.hseg(
  sg: D7.KSeg,
  +gs: List<&2, Bool>,
  +cl: Bool,
  +dt: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  eo: {L9.k3.seg.ok(sg) == True{} : Bool},
  ih: kx.HT(cl, rw, hs, he, D7.k3.seg.name(sg) <> M16.k3.ps0(dt, ps), ab, rest, PP)
) -> PP(T.doc.read(D7.k3.seg.text(sg, String.append(D4.gap(gs), SCon{M16.k3.hdl(cl), rest})), T.MScan{M16.k3.w(rw, hs,
    he,
  M16.k3.ps0(dt, ps), [], M16.k3.hlex0(dt), bk, qk, [], un, lf, ab)})):
  match sg:
    case D7.KsBare{name}:
      match name:
        case SNil{}:
          Eq.bit.absurd(&1, PP(T.doc.read(String.append(SNil{}, String.append(D4.gap(gs), SCon{M16.k3.hdl(cl), rest})),
            T.MScan{M16.k3.w(rw, hs, he, M16.k3.ps0(dt, ps), [], M16.k3.hlex0(dt), bk, qk, [], un, lf, ab)})), eo)
        case SCon{hh, +tt}:
          match hh:
            case Chr{+xx}:
              kx.hbseg(xx, tt, gs, cl, dt, rw, hs, he, ps, bk, qk, un, lf, ab, rest, PP, eo, ih)
    case D7.KsBasic{+pl}:
      kx.hqseg(pl, gs, cl, dt, rw, hs, he, ps, bk, qk, un, lf, ab, rest, PP, eo, ih)
    case D7.KsLit{+name}:
      kx.hlseg(name, gs, cl, dt, rw, hs, he, ps, bk, qk, un, lf, ab, rest, PP, eo, ih)

# a header's segments, then blank space and the bracket: the rest is read
# with every segment pushed onto parts, newest first
def kx.hkeys(
  ds: List<&2, L9.KDot>,
  +last: D7.KSeg,
  +g9: List<&2, Bool>,
  +dt: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  +eo: {L9.k3.dk.ok(ds, last) == True{} : Bool},
  ih: kx.HT(True{}, rw, hs, he, M16.k3.acc(ds, last, dt, ps), ab, rest, PP)
) -> PP(T.doc.read(L9.k3.dk.text(ds, last, String.append(D4.gap(g9), SCon{']', rest})), T.MScan{M16.k3.w(rw, hs, he,
  M16.k3.ps0(dt, ps), [], M16.k3.hlex0(dt), bk, qk, [], un, lf, ab)})):
  match ds:
    case []:
      kx.hseg(last, g9, True{}, dt, rw, hs, he, ps, bk, qk, un, lf, ab, rest, PP, eo, ih)
    case L9.KDot{+sg, g1, +g2} <> +dr:
      kx.hseg(sg, g1, False{}, dt, rw, hs, he, ps, bk, qk, un, lf, ab, String.append(D4.gap(g2),
        L9.k3.dk.text(dr, last, String.append(D4.gap(g9), SCon{']', rest}))), PP, Eq.and.left(L9.k3.seg.ok(sg),
        L9.k3.dk.ok(dr, last), eo), +b2 => +q2 => +u2 => +l2 =>
        %M16.k3.hdgap(g2, L9.k3.dk.text(dr, last, String.append(D4.gap(g9), SCon{']', rest})), rw, hs, he,
          D7.k3.seg.name(sg) <> M16.k3.ps0(dt, ps), b2, q2, u2, l2, ab) : PP(_)
        kx.hkeys(dr, last, g9, True{}, rw, hs, he, D7.k3.seg.name(sg) <> M16.k3.ps0(dt, ps), b2, q2, u2, l2, ab, rest,
          PP,
          Eq.and.right(L9.k3.seg.ok(sg), L9.k3.dk.ok(dr, last), eo), ih))

# WP-A: own and the walk. The walk never reads a string's characters, only
# names and kinds, so reading every span out before a walk or after it gives
# the same rows: own.rows of what a walk returns is what the walk returns on
# own.rows of what it was given, a value to put read out as own.rows reads it
# in a pair (ow.v). The lookups (rows.find, rows.look, look.last) and
# rows.repl each commute with own, and so do the frames a walk keeps.

# a value as own.rows reads it where it is a pair's: every span read out
def ow.v(vv: T.Val) -> T.Val:
  match vv:
    case T.VSpan{src, +kk}:
      T.VStr{T.span.str(src, kk, U32.is_zero(kk))}
    case T.VArr{items}:
      T.VArr{D3.own.rows(items)}
    case T.VInl{rows}:
      T.VInl{D3.own.rows(rows)}
    case T.VHead{path, rows}:
      T.VHead{path, D3.own.rows(rows)}
    case T.VAot{path, rows}:
      T.VAot{path, D3.own.rows(rows)}
    case T.VAots{path, elems}:
      T.VAots{path, D3.own.rows(elems)}
    case other:
      other

# a pair at the head of rows is read with its value read out
def ow.pair(
  +nn: String,
  vv: T.Val,
  +tt: List<&2, T.Val>
) -> {D3.own.rows(T.VPair{nn, vv} <> tt) == T.VPair{nn, ow.v(vv)} <> D3.own.rows(tt) : List<&2, T.Val>}:
  match vv:
    case T.VStr{_a0}:
      {==}
    case T.VSpan{_a0, _a1}:
      {==}
    case T.VInt{_a0, _a1}:
      {==}
    case T.VFlo{_a0, _a1}:
      {==}
    case T.VBool{_a0}:
      {==}
    case T.VWhen{_a0}:
      {==}
    case T.VArr{_a0}:
      {==}
    case T.VInl{_a0}:
      {==}
    case T.VHead{_a0, _a1}:
      {==}
    case T.VAot{_a0, _a1}:
      {==}
    case T.VAots{_a0, _a1}:
      {==}
    case T.VPair{_a0, _a1}:
      {==}

# a lookup's hit, read out
def ow.hit(hh: T.Hit) -> T.Hit:
  match hh:
    case T.Found{vv}:
      T.Found{ow.v(vv)}
    case T.Miss{}:
      T.Miss{}

# one pair of a lookup
def ow.fstep(
  eq: Bool,
  +vv: T.Val,
  +tt: List<&2, T.Val>,
  +name: String,
  ih: {T.rows.find(D3.own.rows(tt), name) == ow.hit(T.rows.find(tt, name)) : T.Hit}
) -> {T.find.step(eq, ow.v(vv), _u => T.rows.find(D3.own.rows(tt), name)) == ow.hit(T.find.step(eq, vv,
  _u => T.rows.find(tt, name))) : T.Hit}:
  match eq:
    case True{}:
      {==}
    case False{}:
      ih

# get reads out as own reads the rows
def ow.find(
  vs: List<&2, T.Val>,
  +name: String
) -> {T.rows.find(D3.own.rows(vs), name) == ow.hit(T.rows.find(vs, name)) : T.Hit}:
  match vs:
    case []:
      {==}
    case +xx <> +tt:
      match xx:
        case T.VStr{_a0}:
          ow.find(tt, name)
        case T.VSpan{_a0, _a1}:
          ow.find(tt, name)
        case T.VInt{_a0, _a1}:
          ow.find(tt, name)
        case T.VFlo{_a0, _a1}:
          ow.find(tt, name)
        case T.VBool{_a0}:
          ow.find(tt, name)
        case T.VWhen{_a0}:
          ow.find(tt, name)
        case T.VArr{_a0}:
          ow.find(tt, name)
        case T.VInl{_a0}:
          ow.find(tt, name)
        case T.VHead{_a0, _a1}:
          ow.find(tt, name)
        case T.VAot{_a0, _a1}:
          ow.find(tt, name)
        case T.VAots{_a0, _a1}:
          ow.find(tt, name)
        case T.VPair{+nn, +vv}:
          %Equal.sym(List<&2, T.Val>, D3.own.rows(T.VPair{nn, vv} <> tt), T.VPair{nn, ow.v(vv)} <> D3.own.rows(tt),
            ow.pair(nn, vv, tt)) : {T.rows.find(_, name) == ow.hit(T.rows.find(T.VPair{nn, vv} <> tt, name)) : T.Hit}
          ow.fstep(T.str.eq(nn, name), vv, tt, name, ow.find(tt, name))

# a lookup's answer, read out
def ow.look(lk: T.Look) -> T.Look:
  match lk:
    case T.KHead{path, rows}:
      T.KHead{path, D3.own.rows(rows)}
    case T.KAots{path, elems}:
      T.KAots{path, D3.own.rows(elems)}
    case other:
      other

# what a value refers to, read out
def ow.lookof(vv: T.Val) -> {T.look.of(ow.v(vv)) == ow.look(T.look.of(vv)) : T.Look}:
  match vv:
    case T.VStr{_a0}:
      {==}
    case T.VSpan{_a0, _a1}:
      {==}
    case T.VInt{_a0, _a1}:
      {==}
    case T.VFlo{_a0, _a1}:
      {==}
    case T.VBool{_a0}:
      {==}
    case T.VWhen{_a0}:
      {==}
    case T.VArr{_a0}:
      {==}
    case T.VInl{_a0}:
      {==}
    case T.VHead{_a0, _a1}:
      {==}
    case T.VAot{_a0, _a1}:
      {==}
    case T.VAots{_a0, _a1}:
      {==}
    case T.VPair{_a0, _a1}:
      {==}

# one pair of rows.look
def ow.lstep(
  eq: Bool,
  +vv: T.Val,
  +tt: List<&2, T.Val>,
  +name: String,
  ih: {T.rows.look(D3.own.rows(tt), name) == ow.look(T.rows.look(tt, name)) : T.Look}
) -> {T.look.step(eq, ow.v(vv), _u => T.rows.look(D3.own.rows(tt), name)) == ow.look(T.look.step(eq, vv,
  _u => T.rows.look(tt, name))) : T.Look}:
  match eq:
    case True{}:
      ow.lookof(vv)
    case False{}:
      ih

# rows.look reads out as own reads the rows
def ow.rlook(
  vs: List<&2, T.Val>,
  +name: String
) -> {T.rows.look(D3.own.rows(vs), name) == ow.look(T.rows.look(vs, name)) : T.Look}:
  match vs:
    case []:
      {==}
    case +xx <> +tt:
      match xx:
        case T.VStr{_a0}:
          ow.rlook(tt, name)
        case T.VSpan{_a0, _a1}:
          ow.rlook(tt, name)
        case T.VInt{_a0, _a1}:
          ow.rlook(tt, name)
        case T.VFlo{_a0, _a1}:
          ow.rlook(tt, name)
        case T.VBool{_a0}:
          ow.rlook(tt, name)
        case T.VWhen{_a0}:
          ow.rlook(tt, name)
        case T.VArr{_a0}:
          ow.rlook(tt, name)
        case T.VInl{_a0}:
          ow.rlook(tt, name)
        case T.VHead{_a0, _a1}:
          ow.rlook(tt, name)
        case T.VAot{_a0, _a1}:
          ow.rlook(tt, name)
        case T.VAots{_a0, _a1}:
          ow.rlook(tt, name)
        case T.VPair{+nn, +vv}:
          %Equal.sym(List<&2, T.Val>, D3.own.rows(T.VPair{nn, vv} <> tt), T.VPair{nn, ow.v(vv)} <> D3.own.rows(tt),
            ow.pair(nn, vv, tt)) : {T.rows.look(_, name) == ow.look(T.rows.look(T.VPair{nn, vv} <> tt, name)) : T.Look}
          ow.lstep(T.str.eq(nn, name), vv, tt, name, ow.rlook(tt, name))

# one pair of rows.repl
def ow.rstep(
  eq: Bool,
  +nn: String,
  +old: T.Val,
  +vv: T.Val,
  +tt: List<&2, T.Val>,
  +name: String,
  ih: {D3.own.rows(T.rows.repl(tt, name, vv)) == T.rows.repl(D3.own.rows(tt), name, ow.v(vv)) : List<&2, T.Val>}
) -> {D3.own.rows(T.rows.repl.step(eq, nn, old, vv, _u => T.rows.repl(tt, name, vv))) == T.rows.repl.step(eq, nn,
  ow.v(old), ow.v(vv), _u => T.rows.repl(D3.own.rows(tt), name, ow.v(vv))) : List<&2, T.Val>}:
  match eq:
    case True{}:
      %Equal.sym(List<&2, T.Val>, D3.own.rows(T.VPair{nn, vv} <> T.rows.repl(tt, name, vv)), T.VPair{nn, ow.v(vv)} <>
        D3.own.rows(T.rows.repl(tt, name, vv)), ow.pair(nn, vv, T.rows.repl(tt, name, vv))) : {_ == T.VPair{nn,
        ow.v(vv)} <> T.rows.repl(D3.own.rows(tt), name, ow.v(vv)) : List<&2, T.Val>}
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => T.VPair{nn, ow.v(vv)} <> zs, D3.own.rows(T.rows.repl(tt,
        name,
        vv)), T.rows.repl(D3.own.rows(tt), name, ow.v(vv)), ih)
    case False{}:
      %Equal.sym(List<&2, T.Val>, D3.own.rows(T.VPair{nn, old} <> T.rows.repl(tt, name, vv)), T.VPair{nn,
        ow.v(old)} <>
        D3.own.rows(T.rows.repl(tt, name, vv)), ow.pair(nn, old, T.rows.repl(tt, name, vv))) : {_ == T.VPair{nn,
        ow.v(old)} <> T.rows.repl(D3.own.rows(tt), name, ow.v(vv)) : List<&2, T.Val>}
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => T.VPair{nn, ow.v(old)} <> zs, D3.own.rows(T.rows.repl(tt,
        name,
        vv)), T.rows.repl(D3.own.rows(tt), name, ow.v(vv)), ih)

# rows.repl reads out as own reads the rows and the value
def ow.repl(
  vs: List<&2, T.Val>,
  +name: String,
  +vv: T.Val
) -> {D3.own.rows(T.rows.repl(vs, name, vv)) == T.rows.repl(D3.own.rows(vs), name, ow.v(vv)) : List<&2, T.Val>}:
  match vs:
    case []:
      {==}
    case +xx <> +tt:
      match xx:
        case T.VStr{+a0}:
          Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => L11.cv.own1(T.VStr{a0}) <> zs,
            D3.own.rows(T.rows.repl(tt, name,
            vv)), T.rows.repl(D3.own.rows(tt), name, ow.v(vv)), ow.repl(tt, name, vv))
        case T.VSpan{+a0, +a1}:
          Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => L11.cv.own1(T.VSpan{a0, a1}) <> zs,
            D3.own.rows(T.rows.repl(tt, name,
            vv)), T.rows.repl(D3.own.rows(tt), name, ow.v(vv)), ow.repl(tt, name, vv))
        case T.VInt{+a0, +a1}:
          Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => L11.cv.own1(T.VInt{a0, a1}) <> zs,
            D3.own.rows(T.rows.repl(tt, name,
            vv)), T.rows.repl(D3.own.rows(tt), name, ow.v(vv)), ow.repl(tt, name, vv))
        case T.VFlo{+a0, +a1}:
          Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => L11.cv.own1(T.VFlo{a0, a1}) <> zs,
            D3.own.rows(T.rows.repl(tt, name,
            vv)), T.rows.repl(D3.own.rows(tt), name, ow.v(vv)), ow.repl(tt, name, vv))
        case T.VBool{+a0}:
          Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => L11.cv.own1(T.VBool{a0}) <> zs,
            D3.own.rows(T.rows.repl(tt, name,
            vv)), T.rows.repl(D3.own.rows(tt), name, ow.v(vv)), ow.repl(tt, name, vv))
        case T.VWhen{+a0}:
          Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => L11.cv.own1(T.VWhen{a0}) <> zs,
            D3.own.rows(T.rows.repl(tt, name,
            vv)), T.rows.repl(D3.own.rows(tt), name, ow.v(vv)), ow.repl(tt, name, vv))
        case T.VArr{+a0}:
          Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => L11.cv.own1(T.VArr{a0}) <> zs,
            D3.own.rows(T.rows.repl(tt, name,
            vv)), T.rows.repl(D3.own.rows(tt), name, ow.v(vv)), ow.repl(tt, name, vv))
        case T.VInl{+a0}:
          Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => L11.cv.own1(T.VInl{a0}) <> zs,
            D3.own.rows(T.rows.repl(tt, name,
            vv)), T.rows.repl(D3.own.rows(tt), name, ow.v(vv)), ow.repl(tt, name, vv))
        case T.VHead{+a0, +a1}:
          Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => L11.cv.own1(T.VHead{a0, a1}) <> zs,
            D3.own.rows(T.rows.repl(tt, name,
            vv)), T.rows.repl(D3.own.rows(tt), name, ow.v(vv)), ow.repl(tt, name, vv))
        case T.VAot{+a0, +a1}:
          Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => L11.cv.own1(T.VAot{a0, a1}) <> zs,
            D3.own.rows(T.rows.repl(tt, name,
            vv)), T.rows.repl(D3.own.rows(tt), name, ow.v(vv)), ow.repl(tt, name, vv))
        case T.VAots{+a0, +a1}:
          Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => L11.cv.own1(T.VAots{a0, a1}) <> zs,
            D3.own.rows(T.rows.repl(tt, name,
            vv)), T.rows.repl(D3.own.rows(tt), name, ow.v(vv)), ow.repl(tt, name, vv))
        case T.VPair{+nn, +old}:
          %Equal.sym(List<&2, T.Val>, D3.own.rows(T.VPair{nn, old} <> tt), T.VPair{nn,
            ow.v(old)} <> D3.own.rows(tt),
            ow.pair(nn, old, tt)) : {D3.own.rows(T.rows.repl(T.VPair{nn, old} <> tt, name, vv)) == T.rows.repl(_,
              name,
            ow.v(vv)) : List<&2, T.Val>}
          ow.rstep(T.str.eq(nn, name), nn, old, vv, tt, name, ow.repl(tt, name, vv))

# the newest element found, read out
def ow.last(ll: T.Last) -> T.Last:
  match ll:
    case T.LastSome{path, pre, rows}:
      T.LastSome{path, D3.own.rows(pre), D3.own.rows(rows)}
    case T.LastNo{why}:
      T.LastNo{why}

# look.last reads out as own reads the elements
def ow.llast(
  elems: List<&2, T.Val>,
  +path: String
) -> {T.look.last(D3.own.rows(elems), path) == ow.last(T.look.last(elems, path)) : T.Last}:
  match elems:
    case []:
      {==}
    case xx <> +tt:
      match xx:
        case T.VStr{_a0}:
          {==}
        case T.VSpan{_a0, _a1}:
          {==}
        case T.VInt{_a0, _a1}:
          {==}
        case T.VFlo{_a0, _a1}:
          {==}
        case T.VBool{_a0}:
          {==}
        case T.VWhen{_a0}:
          {==}
        case T.VArr{_a0}:
          {==}
        case T.VInl{_a0}:
          {==}
        case T.VHead{_a0, _a1}:
          {==}
        case T.VAot{_a0, _a1}:
          {==}
        case T.VAots{_a0, _a1}:
          {==}
        case T.VPair{+nn, +vv}:
          %Equal.sym(List<&2, T.Val>, D3.own.rows(T.VPair{nn, vv} <> tt), T.VPair{nn, ow.v(vv)} <> D3.own.rows(tt),
            ow.pair(nn, vv, tt)) : {T.look.last(_, path) == ow.last(T.look.last(T.VPair{nn, vv} <> tt, path)) : T.Last}
          {==}

# a frame, its parent rows read out
def ow.fr(fr: T.Fr) -> T.Fr:
  match fr:
    case T.FrNew{name, parent, path}:
      T.FrNew{name, D3.own.rows(parent), path}
    case T.FrRep{name, parent, path}:
      T.FrRep{name, D3.own.rows(parent), path}
    case T.FrAot{name, parent, pre, path}:
      T.FrAot{name, D3.own.rows(parent), D3.own.rows(pre), path}

# every frame read out
def ow.frs(frs: List<&2, T.Fr>) -> List<&2, T.Fr>:
  match frs:
    case []:
      []
    case fr <> rest:
      ow.fr(fr) <> ow.frs(rest)

# a walk's job, its value read out
def ow.job(job: T.Job) -> T.Job:
  match job:
    case T.JPut{vv}:
      T.JPut{ow.v(vv)}
    case T.JDef{}:
      T.JDef{}
    case T.JAot{}:
      T.JAot{}

# a walk's state read out
def ow.tw(tw: T.Tw) -> T.Tw:
  match tw:
    case T.Tw{vs, job, stack, bad, pre, heads, inl}:
      T.Tw{D3.own.rows(vs), ow.job(job), ow.frs(stack), bad, pre, heads, inl}

# a walk's end read out
def ow.end(en: T.End) -> T.End:
  match en:
    case T.End{vs, bad, heads}:
      T.End{D3.own.rows(vs), bad, heads}

# a frame put back reads out as own reads it and the child
def ow.wrap(
  fr: T.Fr,
  +child: List<&2, T.Val>
) -> {D3.own.rows(T.tree.wrap(fr, child)) == T.tree.wrap(ow.fr(fr), D3.own.rows(child)) : List<&2, T.Val>}:
  match fr:
    case T.FrNew{_nm, _pa, _pt}:
      {==}
    case T.FrRep{+nm, +pa, +pt}:
      ow.repl(pa, nm, T.VHead{pt, child})
    case T.FrAot{+nm, +pa, +pre, +pt}:
      ow.repl(pa, nm, T.VAots{pt, T.VAot{pt, child} <> pre})

# walking the frames back reads out as own reads them
def ow.rebuild(
  stack: List<&2, T.Fr>,
  +vs: List<&2, T.Val>,
  +bad: String,
  +heads: List<&2, String>
) -> {ow.end(T.tree.rebuild(stack, vs, bad, heads)) == T.tree.rebuild(ow.frs(stack), D3.own.rows(vs), bad, heads)
  : T.End}:
  match stack:
    case []:
      {==}
    case +fr <> +rest:
      %ow.wrap(fr, vs) : {ow.end(T.tree.rebuild(rest, T.tree.wrap(fr, vs), bad,
        heads)) == T.tree.rebuild(ow.frs(rest), _,
        bad, heads) : T.End}
      ow.rebuild(rest, T.tree.wrap(fr, vs), bad, heads)

# a key that is found or not, at the end of a value's walk
def ow.put(
  hit: T.Hit,
  +name: String,
  +vs: List<&2, T.Val>,
  +vv: T.Val,
  +stack: List<&2, T.Fr>,
  +bad: String,
  +heads: List<&2, String>
) -> {ow.end(T.tree.leaf.put(hit, name, vs, vv, stack, bad, heads)) == T.tree.leaf.put(ow.hit(hit), name,
  D3.own.rows(vs), ow.v(vv), ow.frs(stack), bad, heads) : T.End}:
  match hit:
    case T.Found{_v}:
      ow.rebuild(stack, vs, T.err.first(bad, "duplicate key"), heads)
    case T.Miss{}:
      %ow.pair(name, vv, vs) : {ow.end(T.tree.rebuild(stack, T.VPair{name, vv} <> vs, bad, heads))
        == T.tree.rebuild(ow.frs(stack), _, bad, heads) : T.End}
      ow.rebuild(stack, T.VPair{name, vv} <> vs, bad, heads)

# a header on a table that exists
def ow.dhead(
  seen: Bool,
  +name: String,
  +vs: List<&2, T.Val>,
  +rows: List<&2, T.Val>,
  +stack: List<&2, T.Fr>,
  +bad: String,
  +path: String,
  +heads: List<&2, String>
) -> {ow.end(T.tree.leaf.def.head(seen, name, vs, rows, stack, bad, path, heads)) == T.tree.leaf.def.head(seen, name,
  D3.own.rows(vs), D3.own.rows(rows), ow.frs(stack), bad, path, heads) : T.End}:
  match seen:
    case True{}:
      ow.rebuild(stack, vs, T.err.first(bad, "duplicate table"), heads)
    case False{}:
      %ow.repl(vs, name, T.VHead{path, rows}) : {ow.end(T.tree.rebuild(stack, T.rows.repl(vs, name, T.VHead{path,
        rows}),
        bad, T.heads.by.head(path) <> heads)) == T.tree.rebuild(ow.frs(stack), _, bad, T.heads.by.head(path) <> heads)
        : T.End}
      ow.rebuild(stack, T.rows.repl(vs, name, T.VHead{path, rows}), bad, T.heads.by.head(path) <> heads)

# a [table] header's last name
def ow.dhit(
  lk: T.Look,
  +name: String,
  +vs: List<&2, T.Val>,
  +stack: List<&2, T.Fr>,
  +bad: String,
  +path: String,
  +heads: List<&2, String>
) -> {ow.end(T.tree.leaf.def.hit(lk, name, vs, stack, bad, path, heads)) == T.tree.leaf.def.hit(ow.look(lk), name,
  D3.own.rows(vs), ow.frs(stack), bad, path, heads) : T.End}:
  match lk:
    case T.KMiss{}:
      ow.rebuild(stack, T.VPair{name, T.VHead{path, []}} <> vs, bad, T.heads.by.head(path) <> heads)
    case T.KHead{_p, +rows}:
      ow.dhead(T.heads.has(heads, path), name, vs, rows, stack, bad, path, heads)
    case T.KInl{}:
      ow.rebuild(stack, vs, T.err.first(bad, "inline table is closed"), heads)
    case T.KAots{_p, _e}:
      ow.rebuild(stack, vs, T.err.first(bad, "not a table"), heads)
    case T.KNo{+why}:
      ow.rebuild(stack, vs, T.err.first(bad, why), heads)

# an [[array]] header's last name
def ow.ahit(
  lk: T.Look,
  +name: String,
  +vs: List<&2, T.Val>,
  +stack: List<&2, T.Fr>,
  +bad: String,
  +path: String,
  +heads: List<&2, String>
) -> {ow.end(T.tree.leaf.aot.hit(lk, name, vs, stack, bad, path, heads)) == T.tree.leaf.aot.hit(ow.look(lk), name,
  D3.own.rows(vs), ow.frs(stack), bad, path, heads) : T.End}:
  match lk:
    case T.KMiss{}:
      ow.rebuild(stack, T.VPair{name, T.VAots{path, [T.VAot{path, []}]}} <> vs, bad, heads)
    case T.KAots{_p, +elems}:
      %ow.repl(vs, name, T.VAots{path, T.VAot{path, []} <> elems}) : {ow.end(T.tree.rebuild(stack, T.rows.repl(vs, name,
        T.VAots{path, T.VAot{path, []} <> elems}), bad, T.heads.drop(heads, String.append(path,
          ".")))) == T.tree.rebuild(
        ow.frs(stack), _, bad, T.heads.drop(heads, String.append(path, "."))) : T.End}
      ow.rebuild(stack, T.rows.repl(vs, name, T.VAots{path, T.VAot{path, []} <> elems}), bad, T.heads.drop(heads,
        String.append(path, ".")))
    case T.KHead{_p, _r}:
      ow.rebuild(stack, vs, T.err.first(bad, "not a table"), heads)
    case T.KInl{}:
      ow.rebuild(stack, vs, T.err.first(bad, "inline table is closed"), heads)
    case T.KNo{+why}:
      ow.rebuild(stack, vs, T.err.first(bad, why), heads)

# the key at the end of a walk, with the walk still well
def ow.ljob(
  job: T.Job,
  +name: String,
  +vs: List<&2, T.Val>,
  +stack: List<&2, T.Fr>,
  +bad: String,
  +pre: String,
  +heads: List<&2, String>
) -> {ow.end(T.tree.leaf.job(job, name, vs, stack, bad, pre, heads)) == T.tree.leaf.job(ow.job(job), name,
  D3.own.rows(vs), ow.frs(stack), bad, pre, heads) : T.End}:
  match job:
    case T.JPut{+vv}:
      %Equal.sym(T.Hit, T.rows.find(D3.own.rows(vs), name), ow.hit(T.rows.find(vs, name)), ow.find(vs,
        name)) : {ow.end(T.tree.leaf.put(T.get(vs, name), name, vs, vv, stack, bad, heads))
        == T.tree.leaf.put(_, name, D3.own.rows(vs), ow.v(vv), ow.frs(stack), bad, heads) : T.End}
      ow.put(T.get(vs, name), name, vs, vv, stack, bad, heads)
    case T.JDef{}:
      %Equal.sym(T.Look, T.rows.look(D3.own.rows(vs), name), ow.look(T.rows.look(vs, name)), ow.rlook(vs, name))
        : {ow.end(T.tree.leaf.def.hit(T.rows.look(vs, name), name, vs, stack, bad, T.tree.pre(pre,
        name), heads)) == T.tree.leaf.def.hit(_, name, D3.own.rows(vs), ow.frs(stack), bad, T.tree.pre(pre, name),
        heads) : T.End}
      ow.dhit(T.rows.look(vs, name), name, vs, stack, bad, T.tree.pre(pre, name), heads)
    case T.JAot{}:
      %Equal.sym(T.Look, T.rows.look(D3.own.rows(vs), name), ow.look(T.rows.look(vs, name)), ow.rlook(vs, name))
        : {ow.end(T.tree.leaf.aot.hit(T.rows.look(vs, name), name, vs, stack, bad, T.tree.pre(pre,
        name), heads)) == T.tree.leaf.aot.hit(_, name, D3.own.rows(vs), ow.frs(stack), bad, T.tree.pre(pre, name),
        heads) : T.End}
      ow.ahit(T.rows.look(vs, name), name, vs, stack, bad, T.tree.pre(pre, name), heads)

# the key at the end of a walk
def ow.lbad(
  ok: Bool,
  +name: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +bad: String,
  +pre: String,
  +heads: List<&2, String>
) -> {ow.end(T.tree.leaf.bad(ok, name, vs, job, stack, bad, pre, heads)) == T.tree.leaf.bad(ok, name,
  D3.own.rows(vs), ow.job(job), ow.frs(stack), bad, pre, heads) : T.End}:
  match ok:
    case False{}:
      ow.rebuild(stack, vs, bad, heads)
    case True{}:
      ow.ljob(job, name, vs, stack, bad, pre, heads)

# the key at the end of a walk
def ow.leaf(+name: String, tw: T.Tw) -> {ow.end(T.tree.leaf(name, tw)) == T.tree.leaf(name, ow.tw(tw)) : T.End}:
  match tw:
    case T.Tw{+vs, +job, +stack, +bad, +pre, +heads, _inl}:
      ow.lbad(String.is_empty(bad), name, vs, job, stack, bad, pre, heads)

# the step into the newest element of an array of tables
def ow.saots(
  last: T.Last,
  +name: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +path: String
) -> {ow.tw(T.tree.sub.aots(last, name, vs, job, stack, pre, heads, inl, path)) == T.tree.sub.aots(ow.last(last), name,
  D3.own.rows(vs), ow.job(job), ow.frs(stack), pre, heads, inl, path) : T.Tw}:
  match last:
    case T.LastSome{_p, _prefix, _rows}:
      {==}
    case T.LastNo{_why}:
      {==}

# the step into an array of tables
def ow.sarr(
  dot: Bool,
  +path: String,
  +elems: List<&2, T.Val>,
  +name: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool
) -> {ow.tw(T.tree.sub.arr(dot, path, elems, name, vs, job, stack, pre, heads, inl)) == T.tree.sub.arr(dot, path,
  D3.own.rows(elems), name, D3.own.rows(vs), ow.job(job), ow.frs(stack), pre, heads, inl) : T.Tw}:
  match dot:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(T.Last, T.look.last(D3.own.rows(elems), path), ow.last(T.look.last(elems, path)), ow.llast(elems,
        path)) : {ow.tw(T.tree.sub.aots(T.look.last(elems, path), name, vs, job, stack, pre, heads, inl,
        path)) == T.tree.sub.aots(_, name, D3.own.rows(vs), ow.job(job), ow.frs(stack), pre, heads, inl, path) : T.Tw}
      ow.saots(T.look.last(elems, path), name, vs, job, stack, pre, heads, inl, path)

# the step into a table, by the walk's job and whether it is a prefix
def ow.shgo(
  job: T.Job,
  mark: Bool,
  shut: Bool,
  +path: String,
  +rows: List<&2, T.Val>,
  +name: String,
  +vs: List<&2, T.Val>,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool
) -> {ow.tw(T.tree.sub.head.go(shut, path, rows, name, vs, job, stack, pre, heads, inl, mark)) == T.tree.sub.head.go(
  shut, path, D3.own.rows(rows), name, D3.own.rows(vs), ow.job(job), ow.frs(stack), pre, heads, inl, mark) : T.Tw}:
  match job mark shut:
    case T.JPut{+vv} True{} True{}:
      {==}
    case T.JPut{+vv} True{} False{}:
      {==}
    case T.JPut{+vv} False{} True{}:
      {==}
    case T.JPut{+vv} False{} False{}:
      {==}
    case T.JDef{} True{} True{}:
      {==}
    case T.JDef{} True{} False{}:
      {==}
    case T.JDef{} False{} True{}:
      {==}
    case T.JDef{} False{} False{}:
      {==}
    case T.JAot{} True{} True{}:
      {==}
    case T.JAot{} True{} False{}:
      {==}
    case T.JAot{} False{} True{}:
      {==}
    case T.JAot{} False{} False{}:
      {==}

# the step into a table
def ow.shead(
  job: T.Job,
  mark: Bool,
  +path: String,
  +rows: List<&2, T.Val>,
  +name: String,
  +vs: List<&2, T.Val>,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool
) -> {ow.tw(T.tree.sub.head(T.tree.sub.dot(T.tree.sub.job(mark, job)), path, rows, name, vs, job, stack, pre, heads,
  inl, mark)) == T.tree.sub.head(T.tree.sub.dot(T.tree.sub.job(mark, ow.job(job))), path, D3.own.rows(rows), name,
  D3.own.rows(vs), ow.job(job), ow.frs(stack), pre, heads, inl, mark) : T.Tw}:
  match job mark:
    case T.JPut{+vv} True{}:
      ow.shgo(T.JPut{vv}, True{}, T.heads.head(heads, T.tree.pre(pre, name)), path, rows, name, vs, stack, pre, heads,
        inl)
    case T.JPut{+vv} False{}:
      ow.shgo(T.JPut{vv}, False{}, False{}, path, rows, name, vs, stack, pre, heads, inl)
    case T.JDef{} True{}:
      ow.shgo(T.JDef{}, True{}, False{}, path, rows, name, vs, stack, pre, heads, inl)
    case T.JDef{} False{}:
      ow.shgo(T.JDef{}, False{}, False{}, path, rows, name, vs, stack, pre, heads, inl)
    case T.JAot{} True{}:
      ow.shgo(T.JAot{}, True{}, False{}, path, rows, name, vs, stack, pre, heads, inl)
    case T.JAot{} False{}:
      ow.shgo(T.JAot{}, False{}, False{}, path, rows, name, vs, stack, pre, heads, inl)

# the step into an array of tables, by the walk's job and whether it is a
# prefix
def ow.sdot(
  job: T.Job,
  mark: Bool,
  +path: String,
  +elems: List<&2, T.Val>,
  +name: String,
  +vs: List<&2, T.Val>,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool
) -> {ow.tw(T.tree.sub.arr(T.tree.sub.dot(T.tree.sub.job(mark, job)), path, elems, name, vs, job, stack, pre, heads,
  inl)) == T.tree.sub.arr(T.tree.sub.dot(T.tree.sub.job(mark, ow.job(job))), path, D3.own.rows(elems), name,
  D3.own.rows(vs), ow.job(job), ow.frs(stack), pre, heads, inl) : T.Tw}:
  match job mark:
    case T.JPut{+vv} True{}:
      ow.sarr(True{}, path, elems, name, vs, T.JPut{vv}, stack, pre, heads, inl)
    case T.JPut{+vv} False{}:
      ow.sarr(False{}, path, elems, name, vs, T.JPut{vv}, stack, pre, heads, inl)
    case T.JDef{} True{}:
      ow.sarr(False{}, path, elems, name, vs, T.JDef{}, stack, pre, heads, inl)
    case T.JDef{} False{}:
      ow.sarr(False{}, path, elems, name, vs, T.JDef{}, stack, pre, heads, inl)
    case T.JAot{} True{}:
      ow.sarr(False{}, path, elems, name, vs, T.JAot{}, stack, pre, heads, inl)
    case T.JAot{} False{}:
      ow.sarr(False{}, path, elems, name, vs, T.JAot{}, stack, pre, heads, inl)

# one step of a walk, by what the name refers to
def ow.slook(
  lk: T.Look,
  job: T.Job,
  mark: Bool,
  +name: String,
  +vs: List<&2, T.Val>,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool
) -> {ow.tw(T.tree.sub.look(lk, name, vs, job, stack, pre, heads, inl, mark)) == T.tree.sub.look(ow.look(lk), name,
  D3.own.rows(vs), ow.job(job), ow.frs(stack), pre, heads, inl, mark) : T.Tw}:
  match lk:
    case T.KMiss{}:
      match job mark:
        case T.JPut{+vv} True{}:
          {==}
        case T.JPut{+vv} False{}:
          {==}
        case T.JDef{} True{}:
          {==}
        case T.JDef{} False{}:
          {==}
        case T.JAot{} True{}:
          {==}
        case T.JAot{} False{}:
          {==}
    case T.KHead{+path, +rows}:
      ow.shead(job, mark, path, rows, name, vs, stack, pre, heads, inl)
    case T.KInl{}:
      {==}
    case T.KAots{+path, +elems}:
      ow.sdot(job, mark, path, elems, name, vs, stack, pre, heads, inl)
    case T.KNo{_why}:
      {==}

# one step of a walk, when the walk is still well
def ow.sbad(
  ok: Bool,
  +name: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +bad: String,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +mark: Bool
) -> {ow.tw(T.tree.sub.bad(ok, name, vs, job, stack, bad, pre, heads, inl, mark)) == T.tree.sub.bad(ok, name,
  D3.own.rows(vs), ow.job(job), ow.frs(stack), bad, pre, heads, inl, mark) : T.Tw}:
  match ok:
    case False{}:
      {==}
    case True{}:
      %Equal.sym(T.Look, T.rows.look(D3.own.rows(vs), name), ow.look(T.rows.look(vs, name)), ow.rlook(vs, name))
        : {ow.tw(T.tree.sub.look(T.rows.look(vs, name), name, vs, job, stack, pre, heads, inl, mark))
        == T.tree.sub.look(_, name, D3.own.rows(vs), ow.job(job), ow.frs(stack), pre, heads, inl, mark) : T.Tw}
      ow.slook(T.rows.look(vs, name), job, mark, name, vs, stack, pre, heads, inl)

# one step of a walk
def ow.sub(
  +name: String,
  tw: T.Tw,
  +mark: Bool
) -> {ow.tw(T.tree.sub(name, tw, mark)) == T.tree.sub(name, ow.tw(tw), mark) : T.Tw}:
  match tw:
    case T.Tw{+vs, +job, +stack, +bad, +pre, +heads, +inl}:
      ow.sbad(String.is_empty(bad), name, vs, job, stack, bad, pre, heads, inl, mark)

# LAW-like: own of a walk's end is the walk on own of its state
def ow.walk(
  path: List<&2, String>,
  +tw: T.Tw,
  +skip: U32
) -> {ow.end(T.tree.walk(path, tw, skip)) == T.tree.walk(path, ow.tw(tw), skip) : T.End}:
  match path:
    case []:
      match tw:
        case T.Tw{+vs, _job, +stack, +bad, _pre, +heads, _inl}:
          ow.rebuild(stack, vs, T.err.first(bad, "empty key"), heads)
    case +name <> +rest:
      match rest:
        case []:
          ow.leaf(name, tw)
        case +r1 <> +r2:
          %ow.sub(name, tw, U32.is_zero(skip)) : {ow.end(T.tree.walk(r1 <> r2, T.tree.sub(name, tw, U32.is_zero(skip)),
            T.path.dec(skip))) == T.tree.walk(r1 <> r2, _, T.path.dec(skip)) : T.End}
          ow.walk(r1 <> r2, T.tree.sub(name, tw, U32.is_zero(skip)), T.path.dec(skip))

# WP-A: a refused word read to its document. WP-V shows that a bare word
# word.val refuses leaves an error (vl.blift); with error_stays in place of
# fail_stays the same steps give the document itself: the first error, the
# word's reason when there was none, and the rows as they were (wr.*).

# the document a refused word leaves: the first error, and the rows sealed
def wr.D(+fx: D8.Vf, +why: String) -> T.Doc:
  match fx:
    case D8.Vf{bad, rows, _heads, _here, _parts, _back, _qkind, _stack, _uni, _left, _arrtab}:
      T.Doc{T.err.first(bad, why), T.rows.seal(rows)}

# the document read from a mode is dd
def wr.Q(+tt: String, +md: T.Mode, +dd: T.Doc) -> Type:
  {T.doc.read(tt, md) == dd : T.Doc}

# and so is one read from a mode equal to it
def wr.tr(
  +tt: String,
  +m1: T.Mode,
  +m2: T.Mode,
  +dd: T.Doc,
  +ee: {m1 == m2 : T.Mode},
  hh: wr.Q(tt, m2, dd)
) -> wr.Q(tt, m1, dd):
  Equal.trans(T.Doc, T.doc.read(tt, m1), T.doc.read(tt, m2), dd, Equal.cong(T.Mode, T.Doc, md => T.doc.read(tt, md), m1,
    m2, ee), hh)

# a failed scanner reads to its error and rows
def wr.sink(
  +bd: String,
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
  +hb: {String.is_empty(bd) == False{} : Bool},
  +tt: String
) -> wr.Q(tt, T.MScan{T.St{bd, rw, hs, he, ps, [], T.LSink{}, bk, qk, sk, T.HNone{}, un, lf, ab, False{}}}, T.Doc{bd,
  T.rows.seal(rw)}):
  L5.error_stays(bd, rw, hs, he, ps, [], T.LSink{}, bk, qk, sk, T.HNone{}, un, lf, ab, False{}, hb, tt)

# a refused word's scanner, in the scan mode
def wr.bs(
  +fx: D8.Vf,
  +why: String,
  +hw: {String.is_empty(why) == False{} : Bool},
  +tt: String
) -> wr.Q(tt, T.MScan{M4.vl.err(fx, why)}, wr.D(fx, why)):
  match fx:
    case D8.Vf{+bad, +rows, +heads, +here, +parts, +back, +qkind, +stack, +uni, +left, +arrtab}:
      wr.sink(T.err.first(bad, why), rows, heads, here, parts, back, qkind, stack, uni, left, arrtab, M4.vl.ef(bad, why,
        hw),
        tt)

# a character after a carriage return, from a failed scanner
def wr.bcr.at(
  +lf: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf2: U32,
  +ab: Bool,
  +hb: {String.is_empty(bd) == False{} : Bool},
  +cc: Char,
  +tt: String
) -> wr.Q(tt, T.doc.cr(lf, T.St{bd, rw, hs, he, ps, [], T.LSink{}, bk, qk, sk, T.HNone{}, un, lf2, ab, False{}}, cc),
  T.Doc{bd, T.rows.seal(rw)}):
  match lf:
    case True{}:
      wr.sink(bd, rw, hs, he, ps, bk, qk, sk, un, lf2, ab, hb, tt)
    case False{}:
      %Equal.sym(Bool, String.is_empty(bd), False{}, hb) : wr.Q(tt, T.MScan{T.St{T.err.first.go(_, bd,
        "carriage return without line feed"), rw, hs, he, ps, [], T.LSink{}, bk, qk, sk, T.HNone{}, un, lf2, ab,
        False{}}}, T.Doc{bd, T.rows.seal(rw)})
      wr.sink(bd, rw, hs, he, ps, bk, qk, sk, un, lf2, ab, hb, tt)

# and after a carriage return
def wr.bcr(
  +fx: D8.Vf,
  +why: String,
  +hw: {String.is_empty(why) == False{} : Bool},
  +tt: String
) -> wr.Q(tt, T.MCr{M4.vl.err(fx, why)}, wr.D(fx, why)):
  match fx:
    case D8.Vf{+bad, +rows, +heads, +here, +parts, +back, +qkind, +stack, +uni, +left, +arrtab}:
      match tt:
        case SNil{}:
          %Equal.sym(Bool, String.is_empty(T.err.first(bad, why)), False{}, M4.vl.ef(bad, why, hw)) : wr.Q(SNil{},
            T.MScan{T.St{T.err.first.go(_, T.err.first(bad, why), "carriage return without line feed"), rows, heads,
            here, parts, [], T.LSink{}, back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}}},
              T.Doc{T.err.first(bad,
            why), T.rows.seal(rows)})
          wr.sink(T.err.first(bad, why), rows, heads, here, parts, back, qkind, stack, uni, left, arrtab, M4.vl.ef(bad,
            why,
            hw), SNil{})
        case SCon{+hh, +t2}:
          wr.bcr.at(Char.is_eq(hh, '\n'), T.err.first(bad, why), rows, heads, here, parts, back, qkind, stack, uni,
            left,
            arrtab, M4.vl.ef(bad, why, hw), hh, t2)

# and in a mode a quote may open
def wr.bwrap(
  +fx: D8.Vf,
  +why: String,
  +hw: {String.is_empty(why) == False{} : Bool},
  +tt: String
) -> wr.Q(tt, T.doc.wrap(M4.vl.err(fx, why)), wr.D(fx, why)):
  match fx:
    case D8.Vf{+bad, +rows, +heads, +here, +parts, +back, +qkind, +stack, +uni, +left, +arrtab}:
      wr.sink(T.err.first(bad, why), rows, heads, here, parts, back, qkind, stack, uni, left, arrtab, M4.vl.ef(bad, why,
        hw),
        tt)

# the step on any character, from a state the fast step fails
def wr.bq(
  +dq: Bool,
  +sq: Bool,
  +cr: Bool,
  +st: T.St,
  +cc: Char,
  +fx: D8.Vf,
  +why: String,
  +hw: {String.is_empty(why) == False{} : Bool},
  +tt: String,
  +ee: {T.read.fast(st, cc) == M4.vl.err(fx, why) : T.St}
) -> wr.Q(tt, T.doc.scan.q(dq, sq, cr, st, cc), wr.D(fx, why)):
  match dq:
    case True{}:
      wr.tr(tt, T.doc.wrap(T.read.fast(st, cc)), T.doc.wrap(M4.vl.err(fx, why)), wr.D(fx, why), Equal.cong(T.St, T.Mode,
        ss => T.doc.wrap(ss), T.read.fast(st, cc), M4.vl.err(fx, why), ee), wr.bwrap(fx, why, hw, tt))
    case False{}:
      match sq:
        case True{}:
          wr.tr(tt, T.doc.wrap(T.read.fast(st, cc)), T.doc.wrap(M4.vl.err(fx, why)), wr.D(fx, why), Equal.cong(T.St,
            T.Mode, ss => T.doc.wrap(ss), T.read.fast(st, cc), M4.vl.err(fx, why), ee), wr.bwrap(fx, why, hw, tt))
        case False{}:
          match cr:
            case True{}:
              wr.tr(tt, T.MCr{T.read.fast(st, cc)}, T.MCr{M4.vl.err(fx, why)}, wr.D(fx, why), Equal.cong(T.St, T.Mode,
                ss => T.MCr{ss}, T.read.fast(st, cc), M4.vl.err(fx, why), ee), wr.bcr(fx, why, hw, tt))
            case False{}:
              wr.tr(tt, T.MScan{T.read.fast(st, cc)}, T.MScan{M4.vl.err(fx, why)}, wr.D(fx, why), Equal.cong(T.St,
                  T.Mode,
                ss => T.MScan{ss}, T.read.fast(st, cc), M4.vl.err(fx, why), ee), wr.bs(fx, why, hw, tt))

# the end of the text after a refused word in LBare
def wr.bnil.b(
  +fx: D8.Vf,
  +bb: List<&2, Char>,
  +why: String,
  +hw: {String.is_empty(why) == False{} : Bool},
  +hv: {T.word.val(List.reverse(&2, Char, bb)) == T.GotBad{why} : T.Got}
) -> wr.Q(SNil{}, T.MScan{D8.vst(fx, bb, T.LBare{})}, wr.D(fx, why)):
  match fx:
    case D8.Vf{+bad, +rows, +heads, +here, +parts, +back, +qkind, +stack, +uni, +left, +arrtab}:
      Equal.trans(T.Doc, T.read.fin2(T.bare.got(T.word.val(List.reverse(&2, Char, bb)), T.St{bad, rows, heads, here,
        parts, [], T.LBare{}, back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}}, ' ', False{})),
        T.read.fin2(T.bare.got(T.GotBad{why}, T.St{bad, rows, heads, here, parts, [], T.LBare{}, back, qkind, stack,
        T.HNone{}, uni, left, arrtab, False{}}, ' ', False{})), T.Doc{T.err.first(bad, why), T.rows.seal(rows)},
        Equal.cong(T.Got, T.Doc, gg => T.read.fin2(T.bare.got(gg, T.St{bad, rows, heads, here, parts, [], T.LBare{},
          back,
          qkind, stack, T.HNone{}, uni, left, arrtab, False{}}, ' ', False{})), T.word.val(List.reverse(&2, Char, bb)),
          T.GotBad{why}, hv),
        wr.bs(D8.Vf{bad, rows, heads, here, parts, back, qkind, stack, uni, left, arrtab}, why, hw, SNil{}))

# the end of the text after a refused word in LDate
def wr.bnil.d(
  +fx: D8.Vf,
  +bb: List<&2, Char>,
  +why: String,
  +hw: {String.is_empty(why) == False{} : Bool},
  +hv: {T.word.val(List.reverse(&2, Char, bb)) == T.GotBad{why} : T.Got}
) -> wr.Q(SNil{}, T.MScan{D8.vst(fx, bb, T.LDate{})}, wr.D(fx, why)):
  match fx:
    case D8.Vf{+bad, +rows, +heads, +here, +parts, +back, +qkind, +stack, +uni, +left, +arrtab}:
      Equal.trans(T.Doc, T.read.fin2(T.bare.got(T.word.val(List.reverse(&2, Char, bb)), T.St{bad, rows, heads, here,
        parts, [], T.LDate{}, back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}}, ' ', False{})),
        T.read.fin2(T.bare.got(T.GotBad{why}, T.St{bad, rows, heads, here, parts, [], T.LDate{}, back, qkind, stack,
        T.HNone{}, uni, left, arrtab, False{}}, ' ', False{})), T.Doc{T.err.first(bad, why), T.rows.seal(rows)},
        Equal.cong(T.Got, T.Doc, gg => T.read.fin2(T.bare.got(gg, T.St{bad, rows, heads, here, parts, [], T.LDate{},
          back,
          qkind, stack, T.HNone{}, uni, left, arrtab, False{}}, ' ', False{})), T.word.val(List.reverse(&2, Char, bb)),
          T.GotBad{why}, hv),
        wr.bs(D8.Vf{bad, rows, heads, here, parts, back, qkind, stack, uni, left, arrtab}, why, hw, SNil{}))

# the rest after a refused word's date space
def wr.bdate.rest(
  +fx: D8.Vf,
  +bb: List<&2, Char>,
  +why: String,
  +tt: String,
  +hw: {String.is_empty(why) == False{} : Bool},
  +hv: {T.word.val(List.reverse(&2, Char, bb)) == T.GotBad{why} : T.Got},
  +hd: {D3.bw.digit1(tt) == False{} : Bool}
) -> wr.Q(tt, T.MScan{D8.vst(fx, bb, T.LDate{})}, wr.D(fx, why)):
  match tt:
    case SNil{}:
      wr.bnil.d(fx, bb, why, hw, hv)
    case SCon{+c2, +t2}:
      wr.bq(Char.is_eq(c2, '"'), Char.is_eq(c2, '\''), U32.is_eq(Char.to_u32(c2), 13), D8.vst(fx, bb, T.LDate{}), c2,
        fx, why, hw, t2, M4.vl.bdacc(fx, bb, why, c2, hv, hd))

# a space after a refused word: the date's, or one that ends it at once
def wr.bfin.sp(
  +ds: Bool,
  +fx: D8.Vf,
  +bb: List<&2, Char>,
  +why: String,
  +tt: String,
  +hw: {String.is_empty(why) == False{} : Bool},
  +hv: {T.word.val(List.reverse(&2, Char, bb)) == T.GotBad{why} : T.Got},
  +es: {T.date.shaped(bb) == ds : Bool},
  +hn: {Bool.not(Bool.and(T.date.shaped(bb), D3.bw.digit1(tt))) == True{} : Bool}
) -> wr.Q(SCon{' ', tt}, T.MScan{D8.vst(fx, bb, T.LBare{})}, wr.D(fx, why)):
  match ds:
    case True{}:
      wr.tr(tt, T.doc.scan(D8.vst(fx, bb, T.LBare{}), ' '), T.MScan{D8.vst(fx, bb, T.LDate{})}, wr.D(fx, why),
        M3.vl.sp(fx, bb, es), wr.bdate.rest(fx, bb, why, tt, hw, hv, M3.vl.nd(T.date.shaped(bb), D3.bw.digit1(tt), es,
            hn)))
    case False{}:
      wr.tr(tt, T.MScan{T.read.fast(D8.vst(fx, bb, T.LBare{}), ' ')}, T.MScan{M4.vl.err(fx, why)}, wr.D(fx, why),
        Equal.cong(T.St, T.Mode, ss => T.MScan{ss}, T.read.fast(D8.vst(fx, bb, T.LBare{}), ' '), M4.vl.err(fx, why),
        M4.vl.bacc(fx, bb, why, ' ', False{}, hv, M3.vl.rf.sp(fx, bb, es))), wr.bs(fx, why, hw, tt))

# a character other than a space that ends a refused word
def wr.bstp(
  +fx: D8.Vf,
  +bb: List<&2, Char>,
  +why: String,
  +cc: Char,
  +tt: String,
  +hw: {String.is_empty(why) == False{} : Bool},
  +ee: {T.read.fast(D8.vst(fx, bb, T.LBare{}), cc) == M4.vl.err(fx, why) : T.St}
) -> wr.Q(tt, T.MScan{T.read.fast(D8.vst(fx, bb, T.LBare{}), cc)}, wr.D(fx, why)):
  wr.tr(tt, T.MScan{T.read.fast(D8.vst(fx, bb, T.LBare{}), cc)}, T.MScan{M4.vl.err(fx, why)}, wr.D(fx, why),
    Equal.cong(T.St, T.Mode, ss => T.MScan{ss}, T.read.fast(D8.vst(fx, bb, T.LBare{}), cc), M4.vl.err(fx, why), ee),
    wr.bs(fx, why, hw, tt))

# the claim for a refused word's buffer and one ending character
def wr.Bp(+fx: D8.Vf, +bb: List<&2, Char>, +why: String, +tt: String, +cc: Char) -> Type:
  {Bool.not(D3.bw.dsp(cc, bb, tt)) == True{} : Bool} -> wr.Q(SCon{cc, tt}, T.MScan{D8.vst(fx, bb, T.LBare{})},
    wr.D(fx, why))

# a text that ends a refused word reads to the document of the refusal
def wr.bfin(
  +fx: D8.Vf,
  +bb: List<&2, Char>,
  +why: String,
  +rest: String,
  +hw: {String.is_empty(why) == False{} : Bool},
  +hv: {T.word.val(List.reverse(&2, Char, bb)) == T.GotBad{why} : T.Got},
  +ee: {D3.bw.end(bb, rest) == True{} : Bool}
) -> wr.Q(rest, T.MScan{D8.vst(fx, bb, T.LBare{})}, wr.D(fx, why)):
  match rest:
    case SNil{}:
      wr.bnil.b(fx, bb, why, hw, hv)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          M3.vl.delim(ch => wr.Bp(fx, bb, why, tt, ch), xx, Eq.and.left(T.ch.delim(Chr{xx}),
            Bool.not(D3.bw.dsp(Chr{xx}, bb, tt)), ee),
            hn => wr.bfin.sp(T.date.shaped(bb), fx, bb, why, tt, hw, hv, {==}, hn),
            _hn => wr.bstp(fx, bb, why, Chr{9}, tt, hw, M4.vl.bacc(fx, bb, why, Chr{9}, False{}, hv, M3.vl.rf.tab(fx,
                bb))),
            _hn => wr.bstp(fx, bb, why, '\n', tt, hw, M4.vl.bacc(fx, bb, why, '\n', D8.vf.inl(fx), hv, M3.vl.rf.lf(fx,
              bb))),
            _hn => wr.tr(tt, T.MCr{T.read.fast(D8.vst(fx, bb, T.LBare{}), Chr{13})}, T.MCr{M4.vl.err(fx, why)},
              wr.D(fx, why), Equal.cong(T.St, T.Mode, ss => T.MCr{ss}, T.read.fast(D8.vst(fx, bb, T.LBare{}),
              Chr{13}), M4.vl.err(fx, why), M4.vl.bacc(fx, bb, why, Chr{13}, D8.vf.inl(fx), hv, M3.vl.rf.cr(fx, bb))),
              wr.bcr(fx, why, hw, tt)),
            _hn => wr.bstp(fx, bb, why, '#', tt, hw, M4.vl.bacc(fx, bb, why, '#', True{}, hv, M3.vl.rf.hash(fx, bb))),
            _hn => wr.bstp(fx, bb, why, ',', tt, hw, M4.vl.bacc(fx, bb, why, ',', True{}, hv, M3.vl.rf.comma(fx, bb))),
            _hn => wr.bstp(fx, bb, why, ']', tt, hw, M4.vl.bacc(fx, bb, why, ']', True{}, hv, M3.vl.rf.rb(fx, bb))),
            _hn => wr.bstp(fx, bb, why, '}', tt, hw, M4.vl.bacc(fx, bb, why, '}', True{}, hv, M3.vl.rf.rc(fx, bb))))(
              Eq.and.right(T.ch.delim(Chr{xx}), Bool.not(D3.bw.dsp(Chr{xx}, bb, tt)), ee))

# a bare word word.val refuses, read from a value state, then a text that
# ends it: the document is the refusal's
def wr.lift(
  +ww: String,
  +hw: {D3.bw.word(ww) == True{} : Bool},
  +why: String,
  +hv: {T.word.val(String.to_list(ww)) == T.GotBad{why} : T.Got},
  +fx: D8.Vf,
  +rest: String,
  +ee: {D3.bw.end(D3.bw.rev(ww, []), rest) == True{} : Bool}
) -> wr.Q(String.append(ww, rest), T.MScan{D8.vst(fx, [], T.LVal{})}, wr.D(fx, why)):
  match ww:
    case SNil{}:
      Eq.bit.absurd(&1, wr.Q(String.append(SNil{}, rest), T.MScan{D8.vst(fx, [], T.LVal{})}, wr.D(fx, why)), hw)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          +bb = {M14.rev.onto(tt, [Chr{xx}]) : List<&2, Char>}
          +ho = {Equal.trans(T.Got, T.word.val(List.reverse(&2, Char, bb)), T.word.val(String.to_list(SCon{Chr{xx},
            tt})), T.GotBad{why}, Equal.cong(List<&2, Char>, T.Got, cs => T.word.val(cs), List.reverse(&2, Char, bb),
            String.to_list(SCon{Chr{xx}, tt}), M14.wd.order(Chr{xx}, tt)), hv)
            : {T.word.val(List.reverse(&2, Char, bb)) == T.GotBad{why} : T.Got}}
          +he = {Equal.trans(Bool, D3.bw.end(bb, rest), D3.bw.end(D3.bw.rev(tt, [Chr{xx}]), rest), True{},
            Equal.cong(List<&2, Char>, Bool, ys => D3.bw.end(ys, rest), bb, D3.bw.rev(tt, [Chr{xx}]),
            Equal.sym(List<&2, Char>, D3.bw.rev(tt, [Chr{xx}]), bb, M3.vl.rev(tt, [Chr{xx}]))), ee)
            : {D3.bw.end(bb, rest) == True{} : Bool}}
          wr.tr(String.append(tt, rest), T.doc.scan(D8.vst(fx, [], T.LVal{}), Chr{xx}), T.MScan{D8.vst(fx,
            [Chr{xx}], T.LBare{})}, wr.D(fx, why), M1.wd.first(fx, xx, Eq.and.left(D3.word.first(Chr{xx}),
            D3.bw.more(tt, [Chr{xx}]), hw)),
            Equal.trans(T.Doc, T.doc.read(String.append(tt, rest), T.MScan{D8.vst(fx, [Chr{xx}], T.LBare{})}),
              T.doc.read(rest, T.MScan{D8.vst(fx, bb, T.LBare{})}), wr.D(fx, why),
              M3.vl.run(tt, rest, fx, [Chr{xx}], Eq.and.right(D3.word.first(Chr{xx}), D3.bw.more(tt, [Chr{xx}]), hw)),
              wr.bfin(fx, bb, why, rest, M4.vl.why(String.to_list(SCon{Chr{xx}, tt}), why, hv), ho, he)))

# WP-A: keyval lines. A keyval's key is read by KEY-3's reader over a motive
# (kx.keys), its value by WP-S1's and WP-V's readers, and the value's walk
# is the replay's once own reads the rows (ow.walk). What follows a value is
# a follower (aq.fol): blank space, then the end, a comment, a newline, a
# comma or a closing bracket, which ends a bare word and starts no string.

# the rest of a short text is short
def aq.sh(
  pre: String,
  +ss: String,
  +hh: {D3.short(String.append(pre, ss)) == True{} : Bool}
) -> {D3.short(ss) == True{} : Bool}:
  match pre:
    case SNil{}:
      hh
    case SCon{+c0, +pt}:
      aq.sh(pt, ss, M23.gd.short.tail(c0, String.append(pt, ss), hh))

# a text is short when a text equal to it is
def aq.shq(
  +aa: String,
  +bb: String,
  ee: {aa == bb : String},
  hh: {D3.short(aa) == True{} : Bool}
) -> {D3.short(bb) == True{} : Bool}:
  %ee : {D3.short(_) == True{} : Bool}
  hh

# a string value holding ss reads out as the owned string ss
def aq.holds(
  vv: T.Val,
  +ss: String,
  hh: L10.s1.holds(vv, ss)
) -> {ow.v(vv) == T.VStr{ss} : T.Val}:
  match vv:
    case T.VStr{+tt}:
      Equal.cong(String, T.Val, xx => T.VStr{xx}, tt, ss, hh)
    case T.VSpan{+src, +nn}:
      Equal.cong(String, T.Val, xx => T.VStr{xx}, T.span.str(src, nn, U32.is_zero(nn)), ss, hh)
    case T.VInt{_a, _b}:
      match hh:
    case T.VFlo{_a, _b}:
      match hh:
    case T.VBool{_a}:
      match hh:
    case T.VWhen{_a}:
      match hh:
    case T.VArr{_a}:
      match hh:
    case T.VInl{_a}:
      match hh:
    case T.VHead{_a, _b}:
      match hh:
    case T.VAot{_a, _b}:
      match hh:
    case T.VAots{_a, _b}:
      match hh:
    case T.VPair{_a, _b}:
      match hh:

# whether a value is an owned string
def aq.iss(vv: T.Val) -> Bool:
  match vv:
    case T.VStr{_a0}:
      True{}
    case _:
      False{}

# a value own reads as an owned string reads so as an item of a list as well
def aq.holdsc(
  vv: T.Val,
  +ss: String,
  +hv: {ow.v(vv) == T.VStr{ss} : T.Val}
) -> {L11.cv.own1(vv) == T.VStr{ss} : T.Val}:
  match vv:
    case T.VStr{_a0}:
      hv
    case T.VSpan{_a0, _a1}:
      hv
    case T.VInt{_a0, _a1}:
      Eq.bit.absurd(&2, {L11.cv.own1(T.VInt{_a0, _a1}) == T.VStr{ss} : T.Val}, Equal.cong(T.Val, Bool, xx =>
        aq.iss(xx), ow.v(T.VInt{_a0, _a1}),
        T.VStr{ss}, hv))
    case T.VFlo{_a0, _a1}:
      Eq.bit.absurd(&2, {L11.cv.own1(T.VFlo{_a0, _a1}) == T.VStr{ss} : T.Val}, Equal.cong(T.Val, Bool, xx =>
        aq.iss(xx), ow.v(T.VFlo{_a0, _a1}),
        T.VStr{ss}, hv))
    case T.VBool{_a0}:
      Eq.bit.absurd(&2, {L11.cv.own1(T.VBool{_a0}) == T.VStr{ss} : T.Val}, Equal.cong(T.Val, Bool, xx => aq.iss(xx),
        ow.v(T.VBool{_a0}),
        T.VStr{ss}, hv))
    case T.VWhen{_a0}:
      Eq.bit.absurd(&2, {L11.cv.own1(T.VWhen{_a0}) == T.VStr{ss} : T.Val}, Equal.cong(T.Val, Bool, xx => aq.iss(xx),
        ow.v(T.VWhen{_a0}),
        T.VStr{ss}, hv))
    case T.VArr{_a0}:
      Eq.bit.absurd(&2, {L11.cv.own1(T.VArr{_a0}) == T.VStr{ss} : T.Val}, Equal.cong(T.Val, Bool, xx => aq.iss(xx),
        ow.v(T.VArr{_a0}),
        T.VStr{ss}, hv))
    case T.VInl{_a0}:
      Eq.bit.absurd(&2, {L11.cv.own1(T.VInl{_a0}) == T.VStr{ss} : T.Val}, Equal.cong(T.Val, Bool, xx => aq.iss(xx),
        ow.v(T.VInl{_a0}),
        T.VStr{ss}, hv))
    case T.VHead{_a0, _a1}:
      Eq.bit.absurd(&2, {L11.cv.own1(T.VHead{_a0, _a1}) == T.VStr{ss} : T.Val}, Equal.cong(T.Val, Bool, xx =>
        aq.iss(xx), ow.v(T.VHead{_a0, _a1}),
        T.VStr{ss}, hv))
    case T.VAot{_a0, _a1}:
      Eq.bit.absurd(&2, {L11.cv.own1(T.VAot{_a0, _a1}) == T.VStr{ss} : T.Val}, Equal.cong(T.Val, Bool, xx =>
        aq.iss(xx), ow.v(T.VAot{_a0, _a1}),
        T.VStr{ss}, hv))
    case T.VAots{_a0, _a1}:
      Eq.bit.absurd(&2, {L11.cv.own1(T.VAots{_a0, _a1}) == T.VStr{ss} : T.Val}, Equal.cong(T.Val, Bool, xx =>
        aq.iss(xx), ow.v(T.VAots{_a0, _a1}),
        T.VStr{ss}, hv))
    case T.VPair{_a0, _a1}:
      Eq.bit.absurd(&2, {L11.cv.own1(T.VPair{_a0, _a1}) == T.VStr{ss} : T.Val}, Equal.cong(T.Val, Bool, xx =>
        aq.iss(xx), ow.v(T.VPair{_a0, _a1}),
        T.VStr{ss}, hv))

# a scalar word.val reads reads out as itself
def aq.scv(vv: T.Val, hh: {M3.vl.sc(T.GotVal{vv}) == True{} : Bool}) -> {ow.v(vv) == vv : T.Val}:
  match vv:
    case T.VInt{_a, _b}:
      {==}
    case T.VFlo{_a, _b}:
      {==}
    case T.VBool{_a}:
      {==}
    case T.VWhen{_a}:
      {==}
    case T.VStr{_a}:
      Eq.bit.absurd(&2, {ow.v(T.VStr{_a}) == T.VStr{_a} : T.Val}, hh)
    case T.VSpan{_a, _b}:
      Eq.bit.absurd(&2, {ow.v(T.VSpan{_a, _b}) == T.VSpan{_a, _b} : T.Val}, hh)
    case T.VArr{_a}:
      Eq.bit.absurd(&2, {ow.v(T.VArr{_a}) == T.VArr{_a} : T.Val}, hh)
    case T.VInl{_a}:
      Eq.bit.absurd(&2, {ow.v(T.VInl{_a}) == T.VInl{_a} : T.Val}, hh)
    case T.VHead{_a, _b}:
      Eq.bit.absurd(&2, {ow.v(T.VHead{_a, _b}) == T.VHead{_a, _b} : T.Val}, hh)
    case T.VAot{_a, _b}:
      Eq.bit.absurd(&2, {ow.v(T.VAot{_a, _b}) == T.VAot{_a, _b} : T.Val}, hh)
    case T.VAots{_a, _b}:
      Eq.bit.absurd(&2, {ow.v(T.VAots{_a, _b}) == T.VAots{_a, _b} : T.Val}, hh)
    case T.VPair{_a, _b}:
      Eq.bit.absurd(&2, {ow.v(T.VPair{_a, _b}) == T.VPair{_a, _b} : T.Val}, hh)

# and so does it as an item of a list
def aq.scvc(vv: T.Val, hh: {M3.vl.sc(T.GotVal{vv}) == True{} : Bool}) -> {L11.cv.own1(vv) == vv : T.Val}:
  match vv:
    case T.VInt{_a, _b}:
      {==}
    case T.VFlo{_a, _b}:
      {==}
    case T.VBool{_a}:
      {==}
    case T.VWhen{_a}:
      {==}
    case T.VStr{_a}:
      Eq.bit.absurd(&2, {L11.cv.own1(T.VStr{_a}) == T.VStr{_a} : T.Val}, hh)
    case T.VSpan{_a, _b}:
      Eq.bit.absurd(&2, {L11.cv.own1(T.VSpan{_a, _b}) == T.VSpan{_a, _b} : T.Val}, hh)
    case T.VArr{_a}:
      Eq.bit.absurd(&2, {L11.cv.own1(T.VArr{_a}) == T.VArr{_a} : T.Val}, hh)
    case T.VInl{_a}:
      Eq.bit.absurd(&2, {L11.cv.own1(T.VInl{_a}) == T.VInl{_a} : T.Val}, hh)
    case T.VHead{_a, _b}:
      Eq.bit.absurd(&2, {L11.cv.own1(T.VHead{_a, _b}) == T.VHead{_a, _b} : T.Val}, hh)
    case T.VAot{_a, _b}:
      Eq.bit.absurd(&2, {L11.cv.own1(T.VAot{_a, _b}) == T.VAot{_a, _b} : T.Val}, hh)
    case T.VAots{_a, _b}:
      Eq.bit.absurd(&2, {L11.cv.own1(T.VAots{_a, _b}) == T.VAots{_a, _b} : T.Val}, hh)
    case T.VPair{_a, _b}:
      Eq.bit.absurd(&2, {L11.cv.own1(T.VPair{_a, _b}) == T.VPair{_a, _b} : T.Val}, hh)

# a character that ends a value at once: #, a newline's first character, a
# comma, or a closing bracket (%x23, %x0A, %x0D, %x2C, %x5D, %x7D)
def aq.stop(+cc: Char) -> Bool:
  Bool.or(D1.abnf.cp(cc, 35), Bool.or(D1.abnf.cp(cc, 10), Bool.or(D1.abnf.cp(cc, 13), Bool.or(D1.abnf.cp(cc,
    44), Bool.or(D1.abnf.cp(cc, 93), D1.abnf.cp(cc, 125))))))

# a text that may follow a value: blank space, then the end of the text or a
# character that ends a value at once
def aq.fol(ss: String) -> Bool:
  match ss:
    case SNil{}:
      True{}
    case SCon{+hh, tt}:
      Bool.or(Bool.and(D2.abnf.wschar(hh), aq.fol(tt)), aq.stop(hh))

# the right half of an or that holds, when the left half does not
def aq.orr(
  uu: Bool,
  +vv: Bool,
  hu: {uu == False{} : Bool},
  hh: {Bool.or(uu, vv) == True{} : Bool}
) -> {vv == True{} : Bool}:
  match uu:
    case False{}:
      hh
    case True{}:
      Eq.bit.absurd2(&2, {vv == True{} : Bool}, hu)

# whether a character is one of aq.stop's from 125 on
def aq.st125(+cc: Char) -> Bool:
  D1.abnf.cp(cc, 125)

# whether a character is one of aq.stop's from 93 on
def aq.st93(+cc: Char) -> Bool:
  Bool.or(D1.abnf.cp(cc, 93), aq.st125(cc))

# whether a character is one of aq.stop's from 44 on
def aq.st44(+cc: Char) -> Bool:
  Bool.or(D1.abnf.cp(cc, 44), aq.st93(cc))

# whether a character is one of aq.stop's from 13 on
def aq.st13(+cc: Char) -> Bool:
  Bool.or(D1.abnf.cp(cc, 13), aq.st44(cc))

# whether a character is one of aq.stop's from 10 on
def aq.st10(+cc: Char) -> Bool:
  Bool.or(D1.abnf.cp(cc, 10), aq.st13(cc))

# the last of aq.stop's characters
def aq.stop.e6(
  -QQ: Char -> Type,
  +uu: U32,
  hs: {D1.abnf.cp(Chr{uu}, 125) == True{} : Bool},
  _q35: QQ('#'),
  _q10: QQ('\n'),
  _q13: QQ(Chr{13}),
  _q44: QQ(','),
  _q93: QQ(']'),
  q125: QQ('}')
) -> QQ(Chr{uu}):
  %Equal.sym(U32, uu, 125, M22.s1.isk(uu, 125, hs)) : QQ(Chr{_})
  q125

# aq.stop's characters from 93 on
def aq.stop.e5(
  ek: Bool,
  -QQ: Char -> Type,
  +uu: U32,
  +hk: {U32.is_eq(uu, 93) == ek : Bool},
  +hs: {aq.st93(Chr{uu}) == True{} : Bool},
  q35: QQ('#'),
  q10: QQ('\n'),
  q13: QQ(Chr{13}),
  q44: QQ(','),
  q93: QQ(']'),
  q125: QQ('}')
) -> QQ(Chr{uu}):
  match ek:
    case True{}:
      %Equal.sym(U32, uu, 93, M22.s1.isk(uu, 93, hk)) : QQ(Chr{_})
      q93
    case False{}:
      aq.stop.e6(QQ, uu, aq.orr(U32.is_eq(uu, 93), D1.abnf.cp(Chr{uu}, 125), hk, hs), q35, q10, q13, q44, q93, q125)

# aq.stop's characters from 44 on
def aq.stop.e4(
  ek: Bool,
  -QQ: Char -> Type,
  +uu: U32,
  +hk: {U32.is_eq(uu, 44) == ek : Bool},
  +hs: {aq.st44(Chr{uu}) == True{} : Bool},
  q35: QQ('#'),
  q10: QQ('\n'),
  q13: QQ(Chr{13}),
  q44: QQ(','),
  q93: QQ(']'),
  q125: QQ('}')
) -> QQ(Chr{uu}):
  match ek:
    case True{}:
      %Equal.sym(U32, uu, 44, M22.s1.isk(uu, 44, hk)) : QQ(Chr{_})
      q44
    case False{}:
      aq.stop.e5(U32.is_eq(uu, 93), QQ, uu, {==}, aq.orr(U32.is_eq(uu, 44), aq.st93(Chr{uu}), hk, hs), q35, q10, q13,
        q44, q93, q125)

# aq.stop's characters from 13 on
def aq.stop.e3(
  ek: Bool,
  -QQ: Char -> Type,
  +uu: U32,
  +hk: {U32.is_eq(uu, 13) == ek : Bool},
  +hs: {aq.st13(Chr{uu}) == True{} : Bool},
  q35: QQ('#'),
  q10: QQ('\n'),
  q13: QQ(Chr{13}),
  q44: QQ(','),
  q93: QQ(']'),
  q125: QQ('}')
) -> QQ(Chr{uu}):
  match ek:
    case True{}:
      %Equal.sym(U32, uu, 13, M22.s1.isk(uu, 13, hk)) : QQ(Chr{_})
      q13
    case False{}:
      aq.stop.e4(U32.is_eq(uu, 44), QQ, uu, {==}, aq.orr(U32.is_eq(uu, 13), aq.st44(Chr{uu}), hk, hs), q35, q10, q13,
        q44, q93, q125)

# aq.stop's characters from 10 on
def aq.stop.e2(
  ek: Bool,
  -QQ: Char -> Type,
  +uu: U32,
  +hk: {U32.is_eq(uu, 10) == ek : Bool},
  +hs: {aq.st10(Chr{uu}) == True{} : Bool},
  q35: QQ('#'),
  q10: QQ('\n'),
  q13: QQ(Chr{13}),
  q44: QQ(','),
  q93: QQ(']'),
  q125: QQ('}')
) -> QQ(Chr{uu}):
  match ek:
    case True{}:
      %Equal.sym(U32, uu, 10, M22.s1.isk(uu, 10, hk)) : QQ(Chr{_})
      q10
    case False{}:
      aq.stop.e3(U32.is_eq(uu, 13), QQ, uu, {==}, aq.orr(U32.is_eq(uu, 10), aq.st13(Chr{uu}), hk, hs), q35, q10, q13,
        q44, q93, q125)

# aq.stop's characters from 35 on
def aq.stop.e1(
  ek: Bool,
  -QQ: Char -> Type,
  +uu: U32,
  +hk: {U32.is_eq(uu, 35) == ek : Bool},
  +hs: {aq.stop(Chr{uu}) == True{} : Bool},
  q35: QQ('#'),
  q10: QQ('\n'),
  q13: QQ(Chr{13}),
  q44: QQ(','),
  q93: QQ(']'),
  q125: QQ('}')
) -> QQ(Chr{uu}):
  match ek:
    case True{}:
      %Equal.sym(U32, uu, 35, M22.s1.isk(uu, 35, hk)) : QQ(Chr{_})
      q35
    case False{}:
      aq.stop.e2(U32.is_eq(uu, 10), QQ, uu, {==}, aq.orr(U32.is_eq(uu, 35), aq.st10(Chr{uu}), hk, hs), q35, q10, q13,
        q44, q93, q125)

# a follower's first character: blank space before a follower, or one that
# ends a value at once
def aq.fol.e1(
  ws: Bool,
  -QQ: String -> Type,
  +hh: Char,
  +tt: String,
  +hw: {Bool.and(D2.abnf.wschar(hh), aq.fol(tt)) == ws : Bool},
  hf: {Bool.or(ws, aq.stop(hh)) == True{} : Bool},
  sp: @t2: String -> {aq.fol(t2) == True{} : Bool} -> QQ(SCon{' ', t2}),
  tab: @t2: String -> {aq.fol(t2) == True{} : Bool} -> QQ(SCon{'\t', t2}),
  stop: @cc: Char -> @t2: String -> {aq.stop(cc) == True{} : Bool} -> QQ(SCon{cc, t2})
) -> QQ(SCon{hh, tt}):
  match ws:
    case True{}:
      M11.ap.wc(cc => QQ(SCon{cc, tt}), hh, Eq.and.left(D2.abnf.wschar(hh), aq.fol(tt), hw), sp(tt,
        Eq.and.right(D2.abnf.wschar(hh), aq.fol(tt), hw)), tab(tt, Eq.and.right(D2.abnf.wschar(hh), aq.fol(tt),
          hw)))
    case False{}:
      stop(hh, tt, hf)

# what holds of the six characters holds of every one aq.stop takes
def aq.stop.elim(
  -QQ: Char -> Type,
  +uu: U32,
  hs: {aq.stop(Chr{uu}) == True{} : Bool},
  q35: QQ('#'),
  q10: QQ('\n'),
  q13: QQ(Chr{13}),
  q44: QQ(','),
  q93: QQ(']'),
  q125: QQ('}')
) -> QQ(Chr{uu}):
  aq.stop.e1(U32.is_eq(uu, 35), QQ, uu, {==}, hs, q35, q10, q13, q44, q93, q125)

# a follower's shapes: a claim about each holds of every follower
def aq.fol.elim(
  -QQ: String -> Type,
  ss: String,
  hf: {aq.fol(ss) == True{} : Bool},
  nil: QQ(""),
  sp: @tt: String -> {aq.fol(tt) == True{} : Bool} -> QQ(SCon{' ', tt}),
  tab: @tt: String -> {aq.fol(tt) == True{} : Bool} -> QQ(SCon{'\t', tt}),
  stop: @cc: Char -> @tt: String -> {aq.stop(cc) == True{} : Bool} -> QQ(SCon{cc, tt})
) -> QQ(ss):
  match ss:
    case SNil{}:
      nil
    case SCon{+hh, +tt}:
      aq.fol.e1(Bool.and(D2.abnf.wschar(hh), aq.fol(tt)), QQ, hh, tt, {==}, hf, sp, tab, stop)

# a character that ends a value at once starts no string
def aq.free.stop(
  cc: Char,
  +t2: String,
  hs: {aq.stop(cc) == True{} : Bool}
) -> {L10.s1.free(SCon{cc, t2}) == True{} : Bool}:
  match cc:
    case Chr{+uu}:
      aq.stop.elim(c => {L10.s1.free(SCon{c, t2}) == True{} : Bool}, uu, hs, {==}, {==}, {==}, {==}, {==}, {==})

# a follower starts no string
def aq.free(+ss: String, +hf: {aq.fol(ss) == True{} : Bool}) -> {L10.s1.free(ss) == True{} : Bool}:
  aq.fol.elim(s => {L10.s1.free(s) == True{} : Bool}, ss, hf, {==}, _t => _h => {==}, _t => _h => {==},
    cc => t2 => hs => aq.free.stop(cc, t2, hs))

# a character that ends a value at once is no digit
def aq.nod.stop(
  cc: Char,
  +t2: String,
  hs: {aq.stop(cc) == True{} : Bool}
) -> {D3.bw.digit1(SCon{cc, t2}) == False{} : Bool}:
  match cc:
    case Chr{+uu}:
      aq.stop.elim(c => {D3.bw.digit1(SCon{c, t2}) == False{} : Bool}, uu, hs, {==}, {==}, {==}, {==}, {==}, {==})

# a follower starts with no digit
def aq.nod(+ss: String, +hf: {aq.fol(ss) == True{} : Bool}) -> {D3.bw.digit1(ss) == False{} : Bool}:
  aq.fol.elim(s => {D3.bw.digit1(s) == False{} : Bool}, ss, hf, {==}, _t => _h => {==}, _t => _h => {==},
    cc => t2 => hs => aq.nod.stop(cc, t2, hs))

# an and with a false right half is false
def aq.andf(+aa: Bool) -> {Bool.and(aa, False{}) == False{} : Bool}:
  match aa:
    case True{}:
      {==}
    case False{}:
      {==}

# a space before a follower ends a bare word, the date's space included
def aq.bwe.sp(
  +buf: List<&2, Char>,
  +tt: String,
  +ht: {aq.fol(tt) == True{} : Bool}
) -> {D3.bw.end(buf, SCon{' ', tt}) == True{} : Bool}:
  %Equal.sym(Bool, D3.bw.digit1(tt), False{}, aq.nod(tt, ht)) : {Bool.not(Bool.and(True{},
    Bool.and(T.date.shaped(buf),
    _))) == True{} : Bool}
  %Equal.sym(Bool, Bool.and(T.date.shaped(buf), False{}), False{}, aq.andf(T.date.shaped(buf)))
    : {Bool.not(Bool.and(True{}, _)) == True{} : Bool}
  {==}

# a character that ends a value at once ends a bare word
def aq.bwe.stop(
  +buf: List<&2, Char>,
  cc: Char,
  +t2: String,
  hs: {aq.stop(cc) == True{} : Bool}
) -> {D3.bw.end(buf, SCon{cc, t2}) == True{} : Bool}:
  match cc:
    case Chr{+uu}:
      aq.stop.elim(c => {D3.bw.end(buf, SCon{c, t2}) == True{} : Bool}, uu, hs, {==}, {==}, {==}, {==}, {==}, {==})

# a follower ends a bare word
def aq.bwe(
  +buf: List<&2, Char>,
  +ss: String,
  +hf: {aq.fol(ss) == True{} : Bool}
) -> {D3.bw.end(buf, ss) == True{} : Bool}:
  aq.fol.elim(s => {D3.bw.end(buf, s) == True{} : Bool}, ss, hf, {==}, t2 => h2 => aq.bwe.sp(buf, t2, h2),
    _t => _h => {==}, cc => t2 => hs => aq.bwe.stop(buf, cc, t2, hs))

# one blank before a follower
def aq.fol.ws1(
  +hh: Char,
  +tt: String,
  hw: {D2.abnf.wschar(hh) == True{} : Bool},
  +ht: {aq.fol(tt) == True{} : Bool}
) -> {aq.fol(SCon{hh, tt}) == True{} : Bool}:
  %Equal.sym(Bool, aq.fol(tt), True{}, ht) : {Bool.or(Bool.and(D2.abnf.wschar(hh), _), aq.stop(hh)) == True{} : Bool}
  %Equal.sym(Bool, D2.abnf.wschar(hh), True{}, hw) : {Bool.or(Bool.and(_, True{}), aq.stop(hh)) == True{} : Bool}
  {==}

# blank space before a follower is one
def aq.fol.ws(
  ww: String,
  +xx: String,
  +hw: {D2.abnf.ws(ww) == True{} : Bool},
  +hx: {aq.fol(xx) == True{} : Bool}
) -> {aq.fol(String.append(ww, xx)) == True{} : Bool}:
  match ww:
    case SNil{}:
      hx
    case SCon{+hh, +tt}:
      aq.fol.ws1(hh, String.append(tt, xx), Eq.and.left(D2.abnf.wschar(hh), D2.abnf.ws(tt), hw), aq.fol.ws(tt, xx,
        Eq.and.right(D2.abnf.wschar(hh), D2.abnf.ws(tt), hw), hx))

# a comment, or the text after it
def aq.fol.com(
  +com: D6.GCom,
  +xx: String,
  +hx: {aq.fol(xx) == True{} : Bool}
) -> {aq.fol(D6.g.com.text(com, xx)) == True{} : Bool}:
  match com:
    case D6.GcNone{}:
      hx
    case D6.GcSome{_body}:
      {==}

# a newline
def aq.fol.nl(
  nl: String,
  +xx: String,
  +hn: {D1.abnf.newline(nl) == True{} : Bool}
) -> {aq.fol(String.append(nl, xx)) == True{} : Bool}:
  M5.s1.nl.elim(n2 => {aq.fol(String.append(n2, xx)) == True{} : Bool}, nl, hn, {==}, {==})

# What a value reads as: the continuation a value reader is given. With the
# replay's value v and no error, the rest is read from the state with a
# value that own reads as v put where the stack puts values, whatever back,
# qkind, uni and left the value leaves; with an error bd, the document is bd
# and the rows as they were.

# the continuation, by the replay's error
def aq.vk2(
  +bd: String,
  +_vv: T.Val,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  PP: T.Doc -> Type
) -> Type:
  match bd:
    case SNil{}:
      @xv: T.Val -> @bk: T.Lex -> @qk: T.QKind -> @un: U32 -> @lf: U32 -> @hv: {ow.v(xv) == _vv : T.Val} ->
        @hc: {L11.cv.own1(xv) == _vv : T.Val} ->
        PP(T.doc.read(rest, T.MScan{T.take.top(sk, xv, "", rw, hs, he, ps, bk, qk, un, lf, ab, False{})}))
    case SCon{+c0, +cs}:
      PP(T.Doc{SCon{c0, cs}, T.rows.seal(rw)})

# the continuation, by the replay's reading
def aq.vk(
  +rr: D5.RpAcc,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  PP: T.Doc -> Type
) -> Type:
  match rr:
    case D5.RaVal{vv, bd}:
      aq.vk2(bd, vv, rw, hs, he, ps, sk, ab, rest, PP)
    case D5.RaItems{_i, _b}:
      Unit
    case D5.RaRows{_r, _b}:
      Unit

# the continuation of a value node, from no error
def aq.VK(
  +val: D6.GVal,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  PP: T.Doc -> Type
) -> Type:
  aq.vk(D5.replay.go(val, D5.RaVal{T.VArr{[]}, ""}), rw, hs, he, ps, sk, ab, rest, PP)

# a string value's continuation applied, with both readings of the value
def aq.kstr(
  +xv: T.Val,
  +ss: String,
  +b2: T.Lex,
  +q2: T.QKind,
  +u2: U32,
  +l2: U32,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  +hv: {ow.v(xv) == T.VStr{ss} : T.Val},
  kk: aq.vk2("", T.VStr{ss}, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(rest, T.MScan{T.take.top(sk, xv, "", rw, hs, he, ps, b2, q2, u2, l2, ab, False{})})):
  kk(xv, b2, q2, u2, l2, hv, aq.holdsc(xv, ss, hv))

# a string of any form, from a value state
def aq.str(
  +st: D6.GString,
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
  +ab: Bool,
  -PP: T.Doc -> Type,
  +ok: {D1.g.ok.str(st) == True{} : Bool},
  +es: {D3.short(D6.g.str.text(st, rest)) == True{} : Bool},
  +hf: {aq.fol(rest) == True{} : Bool},
  kk: aq.VK(D6.GvString{st}, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(D6.g.str.text(st, rest), T.MScan{D3.vpos(rw, hs, he, ps, bk, qk, sk, un, lf, ab)})):
  L10.string_reads_as_denoted(st, ok, L10.string_short_in_document("", st, rest, es), rw, hs, he, ps, bk, qk, sk, un,
    lf, ab, rest, aq.free(rest, hf), PP, +xv => b2 => q2 => u2 => l2 => hh => aq.kstr(xv, D1.g.str.chars(st), b2,
      q2, u2, l2, rw, hs, he, ps, sk,
    ab, rest, PP, aq.holds(xv, D1.g.str.chars(st), hh), kk))

# a refused bare word: the document is its reason and the rows
def aq.wbad(
  why: String,
  +ww: String,
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
  +ab: Bool,
  -PP: T.Doc -> Type,
  +hw: {D3.bw.word(ww) == True{} : Bool},
  +eg: {T.word.val(String.to_list(ww)) == T.GotBad{why} : T.Got},
  +hf: {aq.fol(rest) == True{} : Bool},
  +hy: {String.is_empty(why) == False{} : Bool},
  kk: aq.vk(D5.replay.got(T.GotBad{why}, ""), rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(String.append(ww, rest), T.MScan{D3.vpos(rw, hs, he, ps, bk, qk, sk, un, lf, ab)})):
  match why:
    case SNil{}:
      Eq.bit.absurd2(&1, PP(T.doc.read(String.append(ww, rest), T.MScan{D3.vpos(rw, hs, he, ps, bk, qk, sk, un, lf,
        ab)})), hy)
    case SCon{+c0, +cs}:
      %Equal.sym(T.Doc, T.doc.read(String.append(ww, rest), T.MScan{D3.vpos(rw, hs, he, ps, bk, qk, sk, un, lf, ab)}),
        T.Doc{SCon{c0, cs}, T.rows.seal(rw)}, wr.lift(ww, hw, SCon{c0, cs}, eg, D8.Vf{"", rw, hs, he, ps, bk, qk, sk,
        un, lf, ab}, rest, aq.bwe(D3.bw.rev(ww, []), rest, hf))) : PP(_)
      kk

# a bare word by what word.val reads it as
def aq.wgot(
  gg: T.Got,
  +ww: String,
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
  +ab: Bool,
  -PP: T.Doc -> Type,
  +hw: {D3.bw.word(ww) == True{} : Bool},
  +eg: {T.word.val(String.to_list(ww)) == gg : T.Got},
  +hf: {aq.fol(rest) == True{} : Bool},
  kk: aq.vk(D5.replay.got(gg, ""), rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(String.append(ww, rest), T.MScan{D3.vpos(rw, hs, he, ps, bk, qk, sk, un, lf, ab)})):
  match gg:
    case T.GotVal{+vv}:
      %Equal.sym(T.Doc, T.doc.read(String.append(ww, rest), T.MScan{D3.vpos(rw, hs, he, ps, bk, qk, sk, un, lf, ab)}),
        T.doc.read(rest, T.MScan{D3.bw.put(sk, vv, rw, hs, he, ps, bk, qk, un, lf, ab)}), L1.bare_word_reads_on(ww,
        hw, vv, eg, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, aq.bwe(D3.bw.rev(ww, []), rest, hf))) : PP(_)
      +hsc = {Equal.trans(Bool, M3.vl.sc(T.GotVal{vv}), M3.vl.sc(T.word.val(String.to_list(ww))), True{},
          Equal.cong(T.Got,
        Bool,
        g2 => M3.vl.sc(g2), T.GotVal{vv}, T.word.val(String.to_list(ww)), Equal.sym(T.Got,
            T.word.val(String.to_list(ww)),
        T.GotVal{vv}, eg)), M3.vl.sc.word(String.to_list(ww))) : {M3.vl.sc(T.GotVal{vv}) == True{} : Bool}}
      kk(vv, bk, qk, un, lf, aq.scv(vv, hsc), aq.scvc(vv, hsc))
    case T.GotBad{+why}:
      aq.wbad(why, ww, rest, rw, hs, he, ps, bk, qk, sk, un, lf, ab, PP, hw, eg, hf, M4.vl.why(String.to_list(ww), why,
        eg), kk)

# WP-A: values and keyvals read from an error. Replay keeps an error it has:
# a value node read from an error keeps it (aq.gobad), however deep its
# arrays and inline tables go, since every walk a keyval of an inline table
# runs starts from it and fails (failed_walk_changes_nothing), and a word
# word.val refuses keeps the first error. A keyval's walk from the root fails
# as well (aq.rootst), so every expression replayed from an error keeps it,
# the rows and the definitions (aq.stays).

# the first error is the one there was
def aq.efirst(
  bd: String,
  +why: String,
  +eb: {String.is_empty(bd) == False{} : Bool}
) -> {T.err.first(bd, why) == bd : String}:
  match bd:
    case SNil{}:
      Eq.bit.absurd2(&2, {T.err.first("", why) == "" : String}, eb)
    case SCon{_c0, _cs}:
      {==}

# a bare word read from an error keeps it
def aq.gotbad(
  gg: T.Got,
  +b0: String,
  +bd: String,
  +eb: {String.is_empty(bd) == False{} : Bool},
  +hb: {b0 == bd : String}
) -> {D5.replay.bad(D5.replay.got(gg, b0)) == bd : String}:
  match gg:
    case T.GotVal{_vv}:
      hb
    case T.GotBad{+why}:
      %Equal.sym(String, b0, bd, hb) : {T.err.first(_, why) == bd : String}
      aq.efirst(bd, why, eb)

# an array closed keeps the error of its items
def aq.arrbad(
  xx: D5.RpAcc,
  +bd: String,
  +hx: {D5.replay.bad(xx) == bd : String}
) -> {D5.replay.bad(D5.replay.arr(xx)) == bd : String}:
  match xx:
    case D5.RaVal{_v, _b}:
      hx
    case D5.RaItems{_i, _b}:
      hx
    case D5.RaRows{_r, _b}:
      hx

# and so does an inline table closed
def aq.inlbad(
  xx: D5.RpAcc,
  +bd: String,
  +hx: {D5.replay.bad(xx) == bd : String}
) -> {D5.replay.bad(D5.replay.inl(xx)) == bd : String}:
  match xx:
    case D5.RaVal{_v, _b}:
      hx
    case D5.RaItems{_i, _b}:
      hx
    case D5.RaRows{_r, _b}:
      hx

# an item put on the items keeps the error both have
def aq.itembad(
  got: D5.RpAcc,
  acc: D5.RpAcc,
  +bd: String,
  +hg: {D5.replay.bad(got) == bd : String},
  +ha: {D5.replay.bad(acc) == bd : String}
) -> {D5.replay.bad(D5.replay.item(got, acc)) == bd : String}:
  match got:
    case D5.RaVal{_v, _b}:
      match acc:
        case D5.RaVal{_v2, _b2}:
          ha
        case D5.RaItems{_i, _b2}:
          hg
        case D5.RaRows{_r, _b2}:
          ha
    case D5.RaItems{_i, _b}:
      ha
    case D5.RaRows{_r, _b}:
      ha

# a keyval of an inline table walked from an error keeps it
def aq.kvbad(
  +names: List<&2, String>,
  got: D5.RpAcc,
  acc: D5.RpAcc,
  +bd: String,
  +eb: {String.is_empty(bd) == False{} : Bool},
  +hg: {D5.replay.bad(got) == bd : String},
  +ha: {D5.replay.bad(acc) == bd : String}
) -> {D5.replay.bad(D5.replay.kv(names, got, acc)) == bd : String}:
  match got:
    case D5.RaVal{+vv, +b}:
      match acc:
        case D5.RaVal{_v2, _b2}:
          ha
        case D5.RaItems{_i, _b2}:
          ha
        case D5.RaRows{+rows, _b2}:
          %Equal.sym(String, b, bd, hg) : {D5.replay.bad(D5.replay.end.rows(T.tree.walk(names, T.Tw{rows,
            T.JPut{vv}, [], _, "", [], True{}}, 0))) == bd : String}
          %Equal.sym(T.End, T.tree.walk(names, T.Tw{rows, T.JPut{vv}, [], bd, "", [], True{}}, 0), T.End{rows, bd,
            []}, L4.failed_walk_changes_nothing(names, rows, T.JPut{vv}, bd, "", [], True{}, 0,
              eb)) : {D5.replay.bad(D5.replay.end.rows(_)) == bd : String}
          {==}
    case D5.RaItems{_i, _b}:
      ha
    case D5.RaRows{_r, _b}:
      ha

# a value node read from an error keeps it
def aq.gobad(
  vv: D6.GVal,
  +acc: D5.RpAcc,
  +bd: String,
  +eb: {String.is_empty(bd) == False{} : Bool},
  +ha: {D5.replay.bad(acc) == bd : String}
) -> {D5.replay.bad(D5.replay.go(vv, acc)) == bd : String}:
  match vv:
    case D6.GvString{_st}:
      ha
    case D6.GvBoolean{+cs}:
      aq.gotbad(T.word.val(cs), D5.replay.bad(acc), bd, eb, ha)
    case D6.GvArrayEmpty{_wn}:
      ha
    case D6.GvArray{+vals, _wn}:
      aq.arrbad(D5.replay.go(vals, D5.RaItems{[], D5.replay.bad(acc)}), bd, aq.gobad(vals, D5.RaItems{[],
        D5.replay.bad(acc)}, bd, eb, ha))
    case D6.GvInlineTableEmpty{_w1, _w2}:
      ha
    case D6.GvInlineTable{_w1, +kvs, _w2}:
      aq.inlbad(D5.replay.go(kvs, D5.RaRows{[], D5.replay.bad(acc)}), bd, aq.gobad(kvs, D5.RaRows{[],
        D5.replay.bad(acc)}, bd, eb, ha))
    case D6.GvDateTime{+cs}:
      aq.gotbad(T.word.val(cs), D5.replay.bad(acc), bd, eb, ha)
    case D6.GvFloat{+cs}:
      aq.gotbad(T.word.val(cs), D5.replay.bad(acc), bd, eb, ha)
    case D6.GvInteger{+cs}:
      aq.gotbad(T.word.val(cs), D5.replay.bad(acc), bd, eb, ha)
    case D6.GArrayValues{_wa, +val, _wb, +rest}:
      aq.gobad(rest, D5.replay.item(D5.replay.go(val, acc), acc), bd, eb, aq.itembad(D5.replay.go(val, acc),
        acc, bd, aq.gobad(val, acc, bd, eb, ha), ha))
    case D6.GArrayValuesLast{_wa, +val, _wb, _sep}:
      aq.itembad(D5.replay.go(val, acc), acc, bd, aq.gobad(val, acc, bd, eb, ha), ha)
    case D6.GInlineTableKeyvals{+kv, _w1, _w2, +rest}:
      aq.gobad(rest, D5.replay.go(kv, acc), bd, eb, aq.gobad(kv, acc, bd, eb, ha))
    case D6.GInlineTableKeyvalsLast{+kv}:
      aq.gobad(kv, acc, bd, eb, ha)
    case D6.GKeyval{+key, _w1, _w2, +val}:
      aq.kvbad(D1.g.key.names(key), D5.replay.go(val, acc), acc, bd, eb, aq.gobad(val, acc, bd, eb, ha), ha)

# a keyval's walk from the root, from an error, keeps it, the rows and the
# definitions
def aq.rootst(
  rr: D5.RpAcc,
  +names: List<&2, String>,
  +bd: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +eb: {String.is_empty(bd) == False{} : Bool},
  +hr: {D5.replay.bad(rr) == bd : String}
) -> {D5.replay.root(names, rr, D5.RpSt{bd, rows, heads, here}) == D5.RpSt{bd, rows, heads, here} : D5.RpSt}:
  match rr:
    case D5.RaVal{+vv, +b}:
      %Equal.sym(String, b, bd, hr) : {D5.replay.end(T.tree.walk(List.append(&2, String, here, names), T.Tw{rows,
        T.JPut{vv}, [], _, "", heads, False{}}, T.path.len(here, 0)), here) == D5.RpSt{bd, rows, heads,
          here} : D5.RpSt}
      %Equal.sym(T.End, T.tree.walk(List.append(&2, String, here, names), T.Tw{rows, T.JPut{vv}, [], bd, "", heads,
        False{}}, T.path.len(here, 0)), T.End{rows, bd, heads}, L4.failed_walk_changes_nothing(List.append(&2,
          String, here, names), rows, T.JPut{vv}, bd, "", heads, False{}, T.path.len(here, 0),
            eb)) : {D5.replay.end(_, here) == D5.RpSt{bd, rows, heads, here} : D5.RpSt}
      {==}
    case D5.RaItems{_i, _b}:
      {==}
    case D5.RaRows{_r, _b}:
      {==}

# an expression replayed from an error keeps it, the rows and the
# definitions
def aq.stays.x(
  +ex: D6.GExpr,
  +bd: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +eb: {String.is_empty(bd) == False{} : Bool}
) -> {D5.replay.expr(ex, D5.RpSt{bd, rows, heads, here}) == D5.RpSt{bd, rows, heads, M11.ap.xhere(ex,
  here)} : D5.RpSt}:
  match ex:
    case D6.GxBlank{_w1, _com}:
      {==}
    case D6.GxKeyval{_w1, +kv, _w2, _com}:
      match kv:
        case D6.GKeyval{+key, _a, _b, +val}:
          aq.rootst(D5.replay.go(val, D5.RaVal{T.VArr{[]}, bd}), D1.g.key.names(key), bd, rows, heads, here, eb,
            aq.gobad(val, D5.RaVal{T.VArr{[]}, bd}, bd, eb, {==}))
        case D6.GvString{_a0}:
          {==}
        case D6.GvBoolean{_a0}:
          {==}
        case D6.GvArrayEmpty{_a0}:
          {==}
        case D6.GvArray{_a0, _a1}:
          {==}
        case D6.GvInlineTableEmpty{_a0, _a1}:
          {==}
        case D6.GvInlineTable{_a0, _a1, _a2}:
          {==}
        case D6.GvDateTime{_a0}:
          {==}
        case D6.GvFloat{_a0}:
          {==}
        case D6.GvInteger{_a0}:
          {==}
        case D6.GArrayValues{_a0, _a1, _a2, _a3}:
          {==}
        case D6.GArrayValuesLast{_a0, _a1, _a2, _a3}:
          {==}
        case D6.GInlineTableKeyvals{_a0, _a1, _a2, _a3}:
          {==}
        case D6.GInlineTableKeyvalsLast{_a0}:
          {==}
    case D6.GxTable{_w1, D6.GStdTable{_a, +key, _b}, _w2, _com}:
      %Equal.sym(T.End, T.tree.walk(D1.g.key.names(key), T.Tw{rows, T.JDef{}, [], bd, "", heads, False{}}, 0),
        T.End{rows, bd, heads}, L4.failed_walk_changes_nothing(D1.g.key.names(key), rows, T.JDef{}, bd, "", heads,
          False{}, 0, eb)) : {D5.replay.end(_, D1.g.key.names(key)) == D5.RpSt{bd, rows, heads,
            D1.g.key.names(key)} : D5.RpSt}
      {==}
    case D6.GxTable{_w1, D6.GArrayTable{_a, +key, _b}, _w2, _com}:
      %Equal.sym(T.End, T.tree.walk(D1.g.key.names(key), T.Tw{rows, T.JAot{}, [], bd, "", heads, False{}}, 0),
        T.End{rows, bd, heads}, L4.failed_walk_changes_nothing(D1.g.key.names(key), rows, T.JAot{}, bd, "", heads,
          False{}, 0, eb)) : {D5.replay.end(_, D1.g.key.names(key)) == D5.RpSt{bd, rows, heads,
            D1.g.key.names(key)} : D5.RpSt}
      {==}

# the lines replayed from an error keep it and the rows to the end
def aq.stays(
  +ls: List<&2, D6.GLine>,
  +bd: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +eb: {String.is_empty(bd) == False{} : Bool}
) -> {D5.replay.doc(D5.replay.lines(ls, D5.RpSt{bd, rows, heads, here})) == T.Doc{bd, T.rows.seal(rows)} : T.Doc}:
  match ls:
    case []:
      {==}
    case D6.GLine{_nl, +ex} <> +rest:
      %Equal.sym(D5.RpSt, D5.replay.expr(ex, D5.RpSt{bd, rows, heads, here}), D5.RpSt{bd, rows, heads,
        M11.ap.xhere(ex, here)}, aq.stays.x(ex, bd, rows, heads, here, eb)) : {D5.replay.doc(D5.replay.lines(rest,
          _)) == T.Doc{bd, T.rows.seal(rows)} : T.Doc}
      aq.stays(rest, bd, rows, heads, M11.ap.xhere(ex, here), eb)

# and so the lines' replay from an error gives the document of the error and
# the rows
def aq.E(+ls: List<&2, D6.GLine>) -> M11.ap.E(ls):
  +bd => +eb => +rows => +heads => +here => aq.stays(ls, bd, rows, heads, here, eb)

# WP-A: the line invariant, own-level. The rows the scanner keeps hold spans
# where the replay holds owned strings, so a state with rows rw stands for
# the replay's own.rows(rw): the rest of the text after an expression reads
# to a document that own reads as the replay's (aq.K). A walk commutes with
# own (ow.walk), so a header's walk on rw ends where the replay's on
# own.rows(rw) does, read out; and an error the scanner keeps is the
# replay's, with the rows read out after they are sealed as before (cv.osl).
# KEY-3's header reader runs as before, with its continuation any claim
# about the document (aq.hcore, from kx.hkeys).

# the rest of the text read after a walk from a line, in the table path,
# with the walk's error, rows and definitions, from every back, qkind, uni
# and left
def aq.HLP(
  +bd2: String,
  +rows2: List<&2, T.Val>,
  +heads2: List<&2, String>,
  +path: List<&2, String>,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  @b2: T.Lex -> @q2: T.QKind -> @u2: U32 -> @l2: U32 ->
    PP(T.doc.read(rest, T.MScan{M11.ap.ln(bd2, rows2, heads2, path, b2, q2, u2, l2)}))

# the rest of the text after an expression, as the reader of the lines ls
# after it gives it: from the state a [ comment ] leaves at the start of a
# line or after a header or a keyval, with no error, the rest reads to a
# document own reads as the lines' replay from the rows read out
def aq.K(+ls: List<&2, D6.GLine>, +tail: String) -> Type:
  @com: D6.GCom -> @lx: T.Lex -> {M11.ap.tll(lx) == True{} : Bool} -> @bk: T.Lex -> @rw: List<&2, T.Val> ->
    @hs: List<&2, String> -> @he: List<&2, String> -> @qk: T.QKind -> @un: U32 -> @lf: U32 ->
    {D3.own(T.doc.read(tail, T.MScan{M11.ap.aft(com, lx, bk, rw, hs, he, [], qk, [], un, lf, False{})}))
    == M11.ap.F(ls, D5.RpSt{"", D3.own.rows(rw), hs, he}) : T.Doc}

# an error the scanner keeps with its rows is the replay's, read out
def aq.err(
  +bd: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +ls: List<&2, D6.GLine>,
  +eb: {String.is_empty(bd) == False{} : Bool},
  ee: M11.ap.E(ls)
) -> {D3.own(T.Doc{bd, T.rows.seal(rows)}) == M11.ap.F(ls, D5.RpSt{bd, D3.own.rows(rows), heads, here}) : T.Doc}:
  Equal.trans(T.Doc, D3.own(T.Doc{bd, T.rows.seal(rows)}), T.Doc{bd, T.rows.seal(D3.own.rows(rows))}, M11.ap.F(ls,
    D5.RpSt{bd, D3.own.rows(rows), heads, here}), Equal.cong(List<&2, T.Val>, T.Doc, zs => T.Doc{bd, zs},
      D3.own.rows(T.rows.seal(rows)), T.rows.seal(D3.own.rows(rows)), M22.cv.osl(rows)), Equal.sym(T.Doc, M11.ap.F(ls,
        D5.RpSt{bd, D3.own.rows(rows), heads, here}), T.Doc{bd, T.rows.seal(D3.own.rows(rows))}, ee(bd, eb,
          D3.own.rows(rows), heads, here)))

# after a walk from a line, however it ended: the blank space, the comment
# and the rest read to a document own reads as the replay's
def aq.hl(
  +bd2: String,
  +rows2: List<&2, T.Val>,
  +heads2: List<&2, String>,
  +names: List<&2, String>,
  +w2: String,
  +com: D6.GCom,
  +tail: String,
  +ls: List<&2, D6.GLine>,
  +hw: {D2.abnf.ws(w2) == True{} : Bool},
  +hc: {D1.g.ok.com(com) == True{} : Bool},
  kk: aq.K(ls, tail),
  ee: M11.ap.E(ls)
) -> aq.HLP(bd2, rows2, heads2, names, String.append(w2, D6.g.com.text(com, tail)), dd => {D3.own(dd) == M11.ap.F(ls,
  D5.RpSt{bd2, D3.own.rows(rows2), heads2, names}) : T.Doc}):
  match bd2:
    case SNil{}:
      +b2 => +q2 => +u2 => +l2 => Equal.trans(T.Doc, D3.own(T.doc.read(String.append(w2, D6.g.com.text(com,
        tail)), T.MScan{M11.ap.ln("", rows2, heads2, names, b2, q2, u2, l2)})), D3.own(T.doc.read(tail,
          T.MScan{M11.ap.aft(com, T.LLine{}, b2, rows2, heads2, names, [], q2, [], u2, l2, False{})})), M11.ap.F(ls,
            D5.RpSt{"", D3.own.rows(rows2), heads2, names}), Equal.cong(T.Doc, T.Doc, dd => D3.own(dd),
              T.doc.read(String.append(w2, D6.g.com.text(com, tail)), T.MScan{M11.ap.ln("", rows2, heads2, names, b2,
                q2, u2, l2)}), T.doc.read(tail, T.MScan{M11.ap.aft(com, T.LLine{}, b2, rows2, heads2, names, [], q2, [],
                  u2, l2, False{})}), M11.ap.tail(w2, com, tail, T.LLine{}, b2, rows2, heads2, names, [], q2, [], u2,
                      l2,
                    False{}, {==}, {==}, hw, hc)), kk(com, T.LLine{}, {==}, b2, rows2, heads2, names, q2, u2, l2))
    case SCon{+c0, +cs}:
      +b2 => +q2 => +u2 => +l2 => Equal.trans(T.Doc, D3.own(T.doc.read(String.append(w2, D6.g.com.text(com,
        tail)), T.MScan{M11.ap.ln(SCon{c0, cs}, rows2, heads2, names, b2, q2, u2, l2)})), D3.own(T.Doc{SCon{c0, cs},
          T.rows.seal(rows2)}), M11.ap.F(ls, D5.RpSt{SCon{c0, cs}, D3.own.rows(rows2), heads2, names}),
            Equal.cong(T.Doc, T.Doc, dd => D3.own(dd), T.doc.read(String.append(w2, D6.g.com.text(com, tail)),
              T.MScan{M11.ap.ln(SCon{c0, cs}, rows2, heads2, names, b2, q2, u2, l2)}), T.Doc{SCon{c0, cs},
                T.rows.seal(rows2)}, L5.error_stays(SCon{c0, cs}, rows2, heads2, names, [], [], T.LLine{}, b2, q2,
                  [], T.HNone{}, u2, l2, False{}, False{}, {==}, String.append(w2, D6.g.com.text(com, tail)))),
                    aq.err(SCon{c0, cs}, rows2, heads2, names, ls, {==}, ee))

# a whole header, from the start of a line in any table, whatever its walk
# returns, with any claim about the document the rest reads to
def aq.hcore(
  +arr: Bool,
  +g0: List<&2, Bool>,
  +ds: List<&2, L9.KDot>,
  +last: D7.KSeg,
  +g9: List<&2, Bool>,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +a0: Bool,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +rows2: List<&2, T.Val>,
  +bd2: String,
  +heads2: List<&2, String>,
  +rest: String,
  -PP: T.Doc -> Type,
  +eo: {L9.k3.dk.ok(ds, last) == True{} : Bool},
  +ew: M11.ap.Wk(L9.k3.dk.names(ds, last), rw, D3.header_job(arr), hs, T.End{rows2, bd2, heads2}),
  ih: aq.HLP(bd2, rows2, heads2, L9.k3.dk.names(ds, last), rest, PP)
) -> PP(T.doc.read(L9.k3.hd.text(arr, g0, ds, last, g9, rest), T.MScan{L9.k3.at(L9.AtLine{}, rw, hs, he, [], a0,
  bk, qk, un, lf)})):
  match arr:
    case False{}:
      %M16.k3.hlead(g0, L9.k3.dk.text(ds, last, String.append(D4.gap(g9), SCon{']', rest})), rw, hs, he, bk, qk, un,
        lf, False{}) : PP(_)
      kx.hkeys(ds, last, g9, M16.k3.nz(g0), rw, hs, he, [], bk, qk, un, lf, False{}, rest, PP, eo, +b2 => +q2 => +u2 =>
        +l2 =>
        %M11.ap.hend(False{}, rw, hs, he, M16.k3.acc(ds, last, M16.k3.nz(g0), []), b2, q2, u2, l2, L9.k3.dk.names(ds,
            last),
          rows2, bd2, heads2, rest, M16.k3.ne(ds, last, M16.k3.ps0(M16.k3.nz(g0), [])), M16.k3.path(M16.k3.nz(g0), ds,
              last), ew) : PP(_)
        ih(b2, q2, u2, l2))
    case True{}:
      %M16.k3.hlead(g0, L9.k3.dk.text(ds, last, String.append(D4.gap(g9), SCon{']', SCon{']', rest}})), rw, hs, he,
        bk, qk, un, lf, True{}) : PP(_)
      kx.hkeys(ds, last, g9, M16.k3.nz(g0), rw, hs, he, [], bk, qk, un, lf, True{}, SCon{']', rest}, PP, eo,
          +b2 => +q2 =>
        +u2 => +l2 =>
        %M11.ap.hend(True{}, rw, hs, he, M16.k3.acc(ds, last, M16.k3.nz(g0), []), b2, q2, u2, l2, L9.k3.dk.names(ds,
            last),
          rows2, bd2, heads2, rest, M16.k3.ne(ds, last, M16.k3.ps0(M16.k3.nz(g0), [])), M16.k3.path(M16.k3.nz(g0), ds,
              last), ew) : PP(_)
        ih(b2, q2, u2, l2))

# a table header of the grammar, from the start of a line in any table,
# whatever its walk returns, with any claim about the document the rest
# reads to in its table
def aq.table(
  +tb: D6.GTable,
  +tail: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ab: Bool,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +rows2: List<&2, T.Val>,
  +bd2: String,
  +heads2: List<&2, String>,
  -PP: T.Doc -> Type,
  +hok: {D1.g.ok.table(tb) == True{} : Bool},
  ew: M11.ap.Wk(D1.g.key.names(M11.ap.tkey(tb)), rw, D3.header_job(M11.ap.tarr(tb)), hs, T.End{rows2, bd2, heads2}),
  ih: aq.HLP(bd2, rows2, heads2, D1.g.key.names(M11.ap.tkey(tb)), tail, PP)
) -> PP(T.doc.read(D6.g.table.text(tb, tail), T.MScan{M11.ap.s(T.LTop{}, bk, rw, hs, he, [], qk, [], un, lf, ab)})):
  %Equal.sym(String, D6.g.table.text(tb, tail), L9.k3.hd.text(M11.ap.tarr(tb), M11.ap.gs(M11.ap.tw1(tb)),
      M11.ap.kds(M11.ap.tkey(tb)),
    M11.ap.klast(M11.ap.tkey(tb)), M11.ap.gs(M11.ap.tw2(tb)), tail), M11.ap.tbl.text(tb, tail, hok)) : PP(T.doc.read(_,
      T.MScan{M11.ap.s(T.LTop{}, bk, rw, hs, he, [], qk, [], un, lf, ab)}))
  aq.hcore(M11.ap.tarr(tb), M11.ap.gs(M11.ap.tw1(tb)), M11.ap.kds(M11.ap.tkey(tb)), M11.ap.klast(M11.ap.tkey(tb)),
      M11.ap.gs(M11.ap.tw2(tb)), rw, hs, he,
    ab, bk, qk, un, lf, rows2, bd2, heads2, tail, PP, M11.ap.key.ok(M11.ap.tkey(tb), M11.ap.tbl.hk(tb, hok)),
        M11.ap.tp(ns =>
      M11.ap.Wk(ns, rw, D3.header_job(M11.ap.tarr(tb)), hs, T.End{rows2, bd2, heads2}), D1.g.key.names(M11.ap.tkey(tb)),
        L9.k3.dk.names(M11.ap.kds(M11.ap.tkey(tb)), M11.ap.klast(M11.ap.tkey(tb))), M11.ap.key.names(M11.ap.tkey(tb)),
            ew), M11.ap.tp(ns =>
          aq.HLP(bd2, rows2, heads2, ns, tail, PP), D1.g.key.names(M11.ap.tkey(tb)),
            L9.k3.dk.names(M11.ap.kds(M11.ap.tkey(tb)), M11.ap.klast(M11.ap.tkey(tb))),
                M11.ap.key.names(M11.ap.tkey(tb)), ih))

# a header and what follows it, with its walk's result named: own reads the
# document as the replay from the walk's end read out
def aq.xtab(
  +tb: D6.GTable,
  +w2: String,
  +com: D6.GCom,
  +tail: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ls: List<&2, D6.GLine>,
  +en: T.End,
  +hen: M11.ap.Wk(D1.g.key.names(M11.ap.tkey(tb)), rw, D3.header_job(M11.ap.tarr(tb)), hs, en),
  +hok: {D1.g.ok.table(tb) == True{} : Bool},
  +hw: {D2.abnf.ws(w2) == True{} : Bool},
  +hc: {D1.g.ok.com(com) == True{} : Bool},
  kk: aq.K(ls, tail),
  ee: M11.ap.E(ls)
) -> {D3.own(T.doc.read(D6.g.table.text(tb, String.append(w2, D6.g.com.text(com, tail))), T.MScan{M11.ap.s(T.LTop{},
  bk, rw, hs, he, [], qk, [], un, lf, False{})})) == M11.ap.F(ls, D5.replay.end(ow.end(en),
    D1.g.key.names(M11.ap.tkey(tb)))) : T.Doc}:
  match en:
    case T.End{+rows2, +bd2, +heads2}:
      aq.table(tb, String.append(w2, D6.g.com.text(com, tail)), rw, hs, he, False{}, bk, qk, un, lf, rows2, bd2,
        heads2, dd => {D3.own(dd) == M11.ap.F(ls, D5.RpSt{bd2, D3.own.rows(rows2), heads2,
          D1.g.key.names(M11.ap.tkey(tb))}) : T.Doc}, hok, hen, aq.hl(bd2, rows2, heads2,
              D1.g.key.names(M11.ap.tkey(tb)),
            w2, com, tail, ls, hw, hc, kk, ee))

# a header and what follows it, as its walk replays on the rows read out
def aq.xtb2(
  +tb: D6.GTable,
  +w1: String,
  +w2: String,
  +com: D6.GCom,
  +tail: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ls: List<&2, D6.GLine>,
  +hok: {D1.g.ok.table(tb) == True{} : Bool},
  +hw: {D2.abnf.ws(w2) == True{} : Bool},
  +hc: {D1.g.ok.com(com) == True{} : Bool},
  kk: aq.K(ls, tail),
  ee: M11.ap.E(ls)
) -> {D3.own(T.doc.read(D6.g.table.text(tb, String.append(w2, D6.g.com.text(com, tail))), T.MScan{M11.ap.s(T.LTop{},
  bk, rw, hs, he, [], qk, [], un, lf, False{})})) == M11.ap.F(ls, D5.replay.expr(D6.GxTable{w1, tb, w2, com},
    D5.RpSt{"", D3.own.rows(rw), hs, he})) : T.Doc}:
  match tb:
    case D6.GStdTable{+v1, +key, +v2}:
      %ow.walk(D1.g.key.names(key), T.Tw{rw, T.JDef{}, [], "", "", hs, False{}},
        0) : {D3.own(T.doc.read(D6.g.table.text(D6.GStdTable{v1, key, v2}, String.append(w2,
          D6.g.com.text(com, tail))), T.MScan{M11.ap.s(T.LTop{}, bk, rw, hs, he, [], qk, [], un, lf,
            False{})})) == M11.ap.F(ls, D5.replay.end(_, D1.g.key.names(key))) : T.Doc}
      aq.xtab(D6.GStdTable{v1, key, v2}, w2, com, tail, rw, hs, he, bk, qk, un, lf, ls,
        T.tree.walk(D1.g.key.names(key), T.Tw{rw, T.JDef{}, [], "", "", hs, False{}}, 0), {==}, hok, hw, hc, kk, ee)
    case D6.GArrayTable{+v1, +key, +v2}:
      %ow.walk(D1.g.key.names(key), T.Tw{rw, T.JAot{}, [], "", "", hs, False{}},
        0) : {D3.own(T.doc.read(D6.g.table.text(D6.GArrayTable{v1, key, v2}, String.append(w2,
          D6.g.com.text(com, tail))), T.MScan{M11.ap.s(T.LTop{}, bk, rw, hs, he, [], qk, [], un, lf,
            False{})})) == M11.ap.F(ls, D5.replay.end(_, D1.g.key.names(key))) : T.Doc}
      aq.xtab(D6.GArrayTable{v1, key, v2}, w2, com, tail, rw, hs, he, bk, qk, un, lf, ls,
        T.tree.walk(D1.g.key.names(key), T.Tw{rw, T.JAot{}, [], "", "", hs, False{}}, 0), {==}, hok, hw, hc, kk, ee)

# a header line: its blank space, the header and what follows it
def aq.xtb(
  +tb: D6.GTable,
  +w1: String,
  +w2: String,
  +com: D6.GCom,
  +tail: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ls: List<&2, D6.GLine>,
  +hx: {D1.g.ok.expr(D6.GxTable{w1, tb, w2, com}) == True{} : Bool},
  kk: aq.K(ls, tail),
  ee: M11.ap.E(ls)
) -> {D3.own(T.doc.read(D6.g.expr.text(D6.GxTable{w1, tb, w2, com}, tail), T.MScan{M11.ap.s(T.LTop{}, bk, rw, hs,
  he, [], qk, [], un, lf, False{})})) == M11.ap.F(ls, D5.replay.expr(D6.GxTable{w1, tb, w2, com}, D5.RpSt{"",
    D3.own.rows(rw), hs, he})) : T.Doc}:
  +hr = {Eq.and.right(D2.abnf.ws(w1), Bool.and(D1.g.ok.table(tb), Bool.and(D2.abnf.ws(w2), D1.g.ok.com(com))),
    hx) : {Bool.and(D1.g.ok.table(tb), Bool.and(D2.abnf.ws(w2), D1.g.ok.com(com))) == True{} : Bool}}
  +hr2 = {Eq.and.right(D1.g.ok.table(tb), Bool.and(D2.abnf.ws(w2), D1.g.ok.com(com)),
    hr) : {Bool.and(D2.abnf.ws(w2), D1.g.ok.com(com)) == True{} : Bool}}
  Equal.trans(T.Doc, D3.own(T.doc.read(D6.g.expr.text(D6.GxTable{w1, tb, w2, com}, tail), T.MScan{M11.ap.s(T.LTop{},
    bk, rw, hs, he, [], qk, [], un, lf, False{})})), D3.own(T.doc.read(D6.g.table.text(tb, String.append(w2,
      D6.g.com.text(com, tail))), T.MScan{M11.ap.s(T.LTop{}, bk, rw, hs, he, [], qk, [], un, lf, False{})})),
          M11.ap.F(ls,
        D5.replay.expr(D6.GxTable{w1, tb, w2, com}, D5.RpSt{"", D3.own.rows(rw), hs, he})), Equal.cong(T.Doc,
          T.Doc, dd => D3.own(dd), T.doc.read(D6.g.expr.text(D6.GxTable{w1, tb, w2, com}, tail),
            T.MScan{M11.ap.s(T.LTop{}, bk, rw, hs, he, [], qk, [], un, lf, False{})}), T.doc.read(D6.g.table.text(tb,
              String.append(w2, D6.g.com.text(com, tail))), T.MScan{M11.ap.s(T.LTop{}, bk, rw, hs, he, [], qk, [], un,
                lf, False{})}), M11.ap.ws(w1, D6.g.table.text(tb, String.append(w2, D6.g.com.text(com, tail))),
                  T.LTop{}, bk, rw, hs, he, [], qk, [], un, lf, False{}, {==}, Eq.and.left(D2.abnf.ws(w1),
                    Bool.and(D1.g.ok.table(tb), Bool.and(D2.abnf.ws(w2), D1.g.ok.com(com))), hx))), aq.xtb2(tb,
                      w1, w2, com, tail, rw, hs, he, bk, qk, un, lf, ls, Eq.and.left(D1.g.ok.table(tb),
                        Bool.and(D2.abnf.ws(w2), D1.g.ok.com(com)), hr), Eq.and.left(D2.abnf.ws(w2),
                          D1.g.ok.com(com), hr2), Eq.and.right(D2.abnf.ws(w2), D1.g.ok.com(com), hr2), kk, ee))

# a list a claim holds of, spelled out and back
def aq.tlp(
  -QQ: List<&2, Char> -> Type,
  +cs: List<&2, Char>,
  hh: QQ(cs)
) -> QQ(String.to_list(String.from_list(cs))):
  %Equal.sym(List<&2, Char>, String.to_list(String.from_list(cs)), cs, M9.gd.tlfl(cs)) : QQ(_)
  hh

# a bare word of the grammar, the characters a value node holds
def aq.word(
  +cs: List<&2, Char>,
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
  +ab: Bool,
  -PP: T.Doc -> Type,
  +hw: {D3.bw.word(String.from_list(cs)) == True{} : Bool},
  +hf: {aq.fol(rest) == True{} : Bool},
  kk: aq.vk(D5.replay.got(T.word.val(cs), ""), rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(String.append(String.from_list(cs), rest), T.MScan{D3.vpos(rw, hs, he, ps, bk, qk, sk, un, lf,
  ab)})):
  aq.wgot(T.word.val(cs), String.from_list(cs), rest, rw, hs, he, ps, bk, qk, sk, un, lf, ab, PP, hw,
    Equal.cong(List<&2, Char>, T.Got, xs => T.word.val(xs), String.to_list(String.from_list(cs)), cs, M9.gd.tlfl(cs)),
      hf, kk)

# the names pushed while reading a key, reversed, are the key's
def aq.kpath(
  +key: D6.GKey
) -> {List.reverse(&2, String, M16.k3.acc(M11.ap.kds(key), M11.ap.klast(key), False{},
    [])) == D1.g.key.names(key) : List<&2,
  String>}:
  Equal.trans(List<&2, String>, List.reverse(&2, String, M16.k3.acc(M11.ap.kds(key), M11.ap.klast(key), False{}, [])),
    L9.k3.dk.names(M11.ap.kds(key), M11.ap.klast(key)), D1.g.key.names(key), M16.k3.path(False{}, M11.ap.kds(key),
        M11.ap.klast(key)),
      Equal.sym(List<&2, String>, D1.g.key.names(key), L9.k3.dk.names(M11.ap.kds(key), M11.ap.klast(key)),
        M11.ap.key.names(key)))

# WP-A: arrays and inline tables, the steps. An array opens with a frame
# for its items (aq.aopen), passes blank space, comments and newlines over
# in LArr and LArrC (aq.wcn), takes each item into the frame (take.top),
# waits for another after a comma, and closes into the value of its items in
# order (aq.aclose). An inline table opens with a frame for its rows
# (aq.iopen), walks each keyval into them (take.inl), and closes into the
# value of its rows sealed (aq.iclose). An item's value is read as in a
# keyval once its first character is held (aq.vst, vl.arr.eq). own reads
# items in a list (cv.own1), and commutes with inl.seal (aq.oinl).

# the scanner waiting for a value: as an array's item (m) or after `=`
def aq.vst(
  +m: Bool,
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
) -> T.St:
  match m:
    case True{}:
      D3.s1.apos(rw, hs, he, ps, bk, qk, sk, un, lf, ab)
    case False{}:
      D3.vpos(rw, hs, he, ps, bk, qk, sk, un, lf, ab)

# the back state an item's first character leaves: LVal, as it is held
def aq.bk0(+m: Bool, +bk: T.Lex) -> T.Lex:
  match m:
    case True{}:
      T.LVal{}
    case False{}:
      bk

# where an array waits after its items: for another (LArr, after a comma)
# or for a comma or the end (LArrC)
def aq.alx(+sp: Bool) -> T.Lex:
  match sp:
    case True{}:
      T.LArr{}
    case False{}:
      T.LArrC{}

# where an inline table's keyval starts: after the brace, or after a comma
def aq.kpos(+pos: Bool) -> L9.KPos:
  match pos:
    case True{}:
      L9.AtInlK{}
    case False{}:
      L9.AtInl{}

# where an inline table closes: empty (LInl), or after a keyval (LInlC)
def aq.ilx(+cl: Bool) -> T.Lex:
  match cl:
    case True{}:
      T.LInlC{}
    case False{}:
      T.LInl{}

# an array's lex states pass blank space over
def aq.alx.wsl(+sp: Bool) -> {M11.ap.wsl(aq.alx(sp)) == True{} : Bool}:
  match sp:
    case True{}:
      {==}
    case False{}:
      {==}

# and take a comment
def aq.alx.coml(+sp: Bool) -> {M11.ap.coml(aq.alx(sp)) == True{} : Bool}:
  match sp:
    case True{}:
      {==}
    case False{}:
      {==}

# and stay after a newline
def aq.alx.nlx(+sp: Bool) -> {M11.ap.nlx(aq.alx(sp)) == aq.alx(sp) : T.Lex}:
  match sp:
    case True{}:
      {==}
    case False{}:
      {==}

# a value placed in a table leaves nothing held
def aq.once.r(
  en: T.End,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool
) -> {T.read.once2(T.take.root(en, he, bk, qk, un, lf, ab, False{})) == T.take.root(en, he, bk, qk, un, lf, ab,
  False{}) : T.St}:
  match en:
    case T.End{_rows, _bad, _heads}:
      {==}

# nor does one placed in an inline table
def aq.once.i(
  en: T.End,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +at: List<&2, String>,
  +sv: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool
) -> {T.read.once2(T.take.inl(en, rw, hs, at, sv, sk, bk, qk, un, lf, ab, False{})) == T.take.inl(en, rw, hs, at, sv,
  sk, bk, qk, un, lf, ab, False{}) : T.St}:
  match en:
    case T.End{_rows, _bad, _heads}:
      {==}

# a value placed anywhere leaves nothing held
def aq.once(
  sk: List<&2, T.Ctx>,
  +xv: T.Val,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool
) -> {T.read.once2(T.take.top(sk, xv, "", rw, hs, he, ps, bk, qk, un, lf, ab, False{})) == T.take.top(sk, xv, "", rw,
  hs, he, ps, bk, qk, un, lf, ab, False{}) : T.St}:
  match sk:
    case []:
      aq.once.r(T.tree.walk(T.path.cat(he, ps), T.Tw{rw, T.JPut{xv}, [], "", "", hs, False{}}, T.path.len(he, 0)), he,
        bk, qk, un, lf, ab)
    case T.CArr{_its, _sv, _at} <> _rest:
      {==}
    case T.CInl{+inl, +sv, +at} <> +rest:
      aq.once.i(T.tree.walk(List.reverse(&2, String, ps), T.Tw{inl, T.JPut{xv}, [], "", "", [], True{}}, 0), rw, hs,
        at, sv, rest, bk, qk, un, lf, ab)

# `[` opens an array: a frame for its items, the key's parts kept in it
def aq.aopen(
  +m: Bool,
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
) -> {T.doc.scan(aq.vst(m, rw, hs, he, ps, bk, qk, sk, un, lf, ab), '[') == T.MScan{M11.ap.s(T.LArr{}, aq.bk0(m, bk),
    rw,
  hs, he, [], qk, T.CArr{[], ps, he} <> sk, un, lf, ab)} : T.Mode}:
  match m:
    case True{}:
      {==}
    case False{}:
      {==}

# `{` opens an inline table: a frame for its rows
def aq.iopen(
  +m: Bool,
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
) -> {T.doc.scan(aq.vst(m, rw, hs, he, ps, bk, qk, sk, un, lf, ab), '{') == T.MScan{M11.ap.s(T.LInl{}, aq.bk0(m, bk),
    rw,
  hs, he, [], qk, T.CInl{[], ps, he} <> sk, un, lf, ab)} : T.Mode}:
  match m:
    case True{}:
      {==}
    case False{}:
      {==}

# `]` closes an array: its items in order are placed as the frame's value
def aq.aclose(
  +sp: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +its: List<&2, T.Val>,
  +sv: List<&2, String>,
  +at: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool
) -> {T.doc.scan(M11.ap.s(aq.alx(sp), bk, rw, hs, he, ps, qk, T.CArr{its, sv, at} <> sk, un, lf, ab),
  ']') == T.MScan{T.take.top(sk, T.VArr{List.reverse(&2, T.Val, its)}, "", rw, hs, at, sv, bk, qk, un, lf, ab,
    False{})} : T.Mode}:
  match sp:
    case True{}:
      Equal.cong(T.St, T.Mode, st => T.MScan{st}, T.read.once2(T.take.top(sk, T.VArr{List.reverse(&2, T.Val, its)},
        "", rw, hs, at, sv, bk, qk, un, lf, ab, False{})), T.take.top(sk, T.VArr{List.reverse(&2, T.Val, its)}, "",
          rw, hs, at, sv, bk, qk, un, lf, ab, False{}), aq.once(sk, T.VArr{List.reverse(&2, T.Val, its)}, rw, hs, at,
            sv, bk, qk, un, lf, ab))
    case False{}:
      Equal.cong(T.St, T.Mode, st => T.MScan{st}, T.read.once2(T.take.top(sk, T.VArr{List.reverse(&2, T.Val, its)},
        "", rw, hs, at, sv, bk, qk, un, lf, ab, False{})), T.take.top(sk, T.VArr{List.reverse(&2, T.Val, its)}, "",
          rw, hs, at, sv, bk, qk, un, lf, ab, False{}), aq.once(sk, T.VArr{List.reverse(&2, T.Val, its)}, rw, hs, at,
            sv, bk, qk, un, lf, ab))

# `}` closes an inline table: its rows sealed are placed as the frame's value
def aq.iclose(
  +cl: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +inl: List<&2, T.Val>,
  +sv: List<&2, String>,
  +at: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool
) -> {T.doc.scan(M11.ap.s(aq.ilx(cl), bk, rw, hs, he, ps, qk, T.CInl{inl, sv, at} <> sk, un, lf, ab),
  '}') == T.MScan{T.take.top(sk, T.VInl{T.inl.seal(inl)}, "", rw, hs, at, sv, bk, qk, un, lf, ab, False{})} : T.Mode}:
  match cl:
    case True{}:
      Equal.cong(T.St, T.Mode, st => T.MScan{st}, T.read.once2(T.take.top(sk, T.VInl{T.inl.seal(inl)}, "", rw, hs, at,
        sv, bk, qk, un, lf, ab, False{})), T.take.top(sk, T.VInl{T.inl.seal(inl)}, "", rw, hs, at, sv, bk, qk, un, lf,
          ab, False{}), aq.once(sk, T.VInl{T.inl.seal(inl)}, rw, hs, at, sv, bk, qk, un, lf, ab))
    case False{}:
      Equal.cong(T.St, T.Mode, st => T.MScan{st}, T.read.once2(T.take.top(sk, T.VInl{T.inl.seal(inl)}, "", rw, hs, at,
        sv, bk, qk, un, lf, ab, False{})), T.take.top(sk, T.VInl{T.inl.seal(inl)}, "", rw, hs, at, sv, bk, qk, un, lf,
          ab, False{}), aq.once(sk, T.VInl{T.inl.seal(inl)}, rw, hs, at, sv, bk, qk, un, lf, ab))

# ws-comment-newline in a state that passes blank space over and takes a
# comment, and stays after a newline: the rest is read from the same state,
# with the back state a comment leaves
def aq.wcn(
  ws: List<&2, D6.GWcn>,
  +rest: String,
  +lx: T.Lex,
  +bk: T.Lex,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +hl: {M11.ap.wsl(lx) == True{} : Bool},
  +hm: {M11.ap.coml(lx) == True{} : Bool},
  +hn: {M11.ap.nlx(lx) == lx : T.Lex},
  +hw: {D1.g.ok.wcn(ws) == True{} : Bool},
  -PP: T.Doc -> Type,
  ih: @b2: T.Lex -> PP(T.doc.read(rest, T.MScan{M11.ap.s(lx, b2, rw, hs, he, pt, qk, sk, un, lf, ab)}))
) -> PP(T.doc.read(D6.g.wcn.text(ws, rest), T.MScan{M11.ap.s(lx, bk, rw, hs, he, pt, qk, sk, un, lf, ab)})):
  match ws:
    case []:
      ih(bk)
    case D6.GwWschar{+cc} <> +wr:
      %Equal.sym(T.Mode, T.doc.scan(M11.ap.s(lx, bk, rw, hs, he, pt, qk, sk, un, lf, ab), cc), T.MScan{M11.ap.s(lx, bk,
          rw,
        hs, he, pt, qk, sk, un, lf, ab)}, M11.ap.wsc(lx, cc, bk, rw, hs, he, pt, qk, sk, un, lf, ab, hl,
          Eq.and.left(D2.abnf.wschar(cc), D1.g.ok.wcn(wr), hw))) : PP(T.doc.read(D6.g.wcn.text(wr, rest), _))
      aq.wcn(wr, rest, lx, bk, rw, hs, he, pt, qk, sk, un, lf, ab, hl, hm, hn, Eq.and.right(D2.abnf.wschar(cc),
        D1.g.ok.wcn(wr), hw), PP, ih)
    case D6.GwNewline{+com, +nl} <> +wr:
      +hr = {Eq.and.right(D1.g.ok.com(com), Bool.and(D1.abnf.newline(nl), D1.g.ok.wcn(wr)),
        hw) : {Bool.and(D1.abnf.newline(nl), D1.g.ok.wcn(wr)) == True{} : Bool}}
      %Equal.sym(T.Doc, T.doc.read(D6.g.com.text(com, String.append(nl, D6.g.wcn.text(wr, rest))),
        T.MScan{M11.ap.s(lx, bk, rw, hs, he, pt, qk, sk, un, lf, ab)}), T.doc.read(String.append(nl, D6.g.wcn.text(wr,
          rest)), T.MScan{M11.ap.aft(com, lx, bk, rw, hs, he, pt, qk, sk, un, lf, ab)}), M11.ap.tail("", com,
            String.append(nl, D6.g.wcn.text(wr, rest)), lx, bk, rw, hs, he, pt, qk, sk, un, lf, ab, hl, hm, {==},
              Eq.and.left(D1.g.ok.com(com), Bool.and(D1.abnf.newline(nl), D1.g.ok.wcn(wr)), hw))) : PP(_)
      %Equal.sym(T.Doc, T.doc.read(String.append(nl, D6.g.wcn.text(wr, rest)), T.MScan{M11.ap.aft(com, lx, bk, rw, hs,
        he, pt, qk, sk, un, lf, ab)}), T.doc.read(D6.g.wcn.text(wr, rest), T.MScan{M11.ap.s(M11.ap.nlx(lx),
            M11.ap.abk(com, lx,
          bk), rw, hs, he, pt, qk, sk, un, lf, ab)}), M11.ap.eol(com, lx, nl, D6.g.wcn.text(wr, rest), bk, rw, hs, he,
            pt, qk, sk, un, lf, ab, hm, Eq.and.left(D1.abnf.newline(nl), D1.g.ok.wcn(wr), hr))) : PP(_)
      %Equal.sym(T.Lex, M11.ap.nlx(lx), lx, hn) : PP(T.doc.read(D6.g.wcn.text(wr, rest), T.MScan{M11.ap.s(_,
          M11.ap.abk(com, lx,
        bk), rw, hs, he, pt, qk, sk, un, lf, ab)}))
      aq.wcn(wr, rest, lx, M11.ap.abk(com, lx, bk), rw, hs, he, pt, qk, sk, un, lf, ab, hl, hm, hn,
        Eq.and.right(D1.abnf.newline(nl), D1.g.ok.wcn(wr), hr), PP, ih)

# a follower after ws-comment-newline is one
def aq.fol.wcn(
  ws: List<&2, D6.GWcn>,
  +xx: String,
  +hw: {D1.g.ok.wcn(ws) == True{} : Bool},
  +hx: {aq.fol(xx) == True{} : Bool}
) -> {aq.fol(D6.g.wcn.text(ws, xx)) == True{} : Bool}:
  match ws:
    case []:
      hx
    case D6.GwWschar{+cc} <> +wr:
      aq.fol.ws1(cc, D6.g.wcn.text(wr, xx), Eq.and.left(D2.abnf.wschar(cc), D1.g.ok.wcn(wr), hw), aq.fol.wcn(wr,
        xx, Eq.and.right(D2.abnf.wschar(cc), D1.g.ok.wcn(wr), hw), hx))
    case D6.GwNewline{+com, +nl} <> +wr:
      aq.fol.com(com, String.append(nl, D6.g.wcn.text(wr, xx)), aq.fol.nl(nl, D6.g.wcn.text(wr, xx),
        Eq.and.left(D1.abnf.newline(nl), D1.g.ok.wcn(wr), Eq.and.right(D1.g.ok.com(com),
          Bool.and(D1.abnf.newline(nl), D1.g.ok.wcn(wr)), hw))))

# a follower, or a comma before any text
def aq.fol.sep(
  +sep: Bool,
  +xx: String,
  +hx: {aq.fol(xx) == True{} : Bool}
) -> {aq.fol(D6.g.sep.text(sep, xx)) == True{} : Bool}:
  match sep:
    case True{}:
      {==}
    case False{}:
      hx

# the text after ws-comment-newline in a short text is short
def aq.sh.wcn(
  +ws: List<&2, D6.GWcn>,
  +xx: String,
  +hh: {D3.short(D6.g.wcn.text(ws, xx)) == True{} : Bool}
) -> {D3.short(xx) == True{} : Bool}:
  aq.sh(D6.g.wcn.text(ws, ""), xx, aq.shq(D6.g.wcn.text(ws, xx), String.append(D6.g.wcn.text(ws, ""), xx),
    M15.gt.wcn(ws, xx), hh))

# and so is the text after a value
def aq.sh.val(
  +vv: D6.GVal,
  +xx: String,
  +hh: {D3.short(D6.g.val.text(vv, xx)) == True{} : Bool}
) -> {D3.short(xx) == True{} : Bool}:
  aq.sh(D6.g.val.text(vv, ""), xx, aq.shq(D6.g.val.text(vv, xx), String.append(D6.g.val.text(vv, ""), xx),
    L7.g_val_text_tail(vv, xx), hh))

# own reads an inline table's rows sealed as the seal of what it reads
def aq.oinl(
  xs: List<&2, T.Val>
) -> {D3.own.rows(T.inl.seal(xs)) == T.inl.seal(D3.own.rows(xs)) : List<&2, T.Val>}:
  match xs:
    case []:
      {==}
    case T.VPair{+nn, T.VHead{+pp, +rr}} <> +tt:
      Equal.trans(List<&2, T.Val>, T.VPair{nn,
        T.VInl{D3.own.rows(T.inl.seal(rr))}} <> D3.own.rows(T.inl.seal(tt)), T.VPair{nn,
          T.VInl{T.inl.seal(D3.own.rows(rr))}} <> D3.own.rows(T.inl.seal(tt)), T.VPair{nn,
            T.VInl{T.inl.seal(D3.own.rows(rr))}} <> T.inl.seal(D3.own.rows(tt)), Equal.cong(List<&2, T.Val>,
              List<&2, T.Val>, zs => T.VPair{nn, T.VInl{zs}} <> D3.own.rows(T.inl.seal(tt)),
                D3.own.rows(T.inl.seal(rr)), T.inl.seal(D3.own.rows(rr)), aq.oinl(rr)), Equal.cong(List<&2,
                  T.Val>, List<&2, T.Val>, zs => T.VPair{nn, T.VInl{T.inl.seal(D3.own.rows(rr))}} <> zs,
                    D3.own.rows(T.inl.seal(tt)), T.inl.seal(D3.own.rows(tt)), aq.oinl(tt)))
    case T.VStr{+a0} <> +tt:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => L11.cv.own1(T.VStr{a0}) <> zs, D3.own.rows(T.inl.seal(tt)),
        T.inl.seal(D3.own.rows(tt)), aq.oinl(tt))
    case T.VSpan{+a0, +a1} <> +tt:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => L11.cv.own1(T.VSpan{a0, a1}) <> zs,
        D3.own.rows(T.inl.seal(tt)),
        T.inl.seal(D3.own.rows(tt)), aq.oinl(tt))
    case T.VInt{+a0, +a1} <> +tt:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => L11.cv.own1(T.VInt{a0, a1}) <> zs,
        D3.own.rows(T.inl.seal(tt)),
        T.inl.seal(D3.own.rows(tt)), aq.oinl(tt))
    case T.VFlo{+a0, +a1} <> +tt:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => L11.cv.own1(T.VFlo{a0, a1}) <> zs,
        D3.own.rows(T.inl.seal(tt)),
        T.inl.seal(D3.own.rows(tt)), aq.oinl(tt))
    case T.VBool{+a0} <> +tt:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => L11.cv.own1(T.VBool{a0}) <> zs, D3.own.rows(T.inl.seal(tt)),
        T.inl.seal(D3.own.rows(tt)), aq.oinl(tt))
    case T.VWhen{+a0} <> +tt:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => L11.cv.own1(T.VWhen{a0}) <> zs, D3.own.rows(T.inl.seal(tt)),
        T.inl.seal(D3.own.rows(tt)), aq.oinl(tt))
    case T.VArr{+a0} <> +tt:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => L11.cv.own1(T.VArr{a0}) <> zs, D3.own.rows(T.inl.seal(tt)),
        T.inl.seal(D3.own.rows(tt)), aq.oinl(tt))
    case T.VInl{+a0} <> +tt:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => L11.cv.own1(T.VInl{a0}) <> zs, D3.own.rows(T.inl.seal(tt)),
        T.inl.seal(D3.own.rows(tt)), aq.oinl(tt))
    case T.VHead{+a0, +a1} <> +tt:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => L11.cv.own1(T.VHead{a0, a1}) <> zs,
        D3.own.rows(T.inl.seal(tt)),
        T.inl.seal(D3.own.rows(tt)), aq.oinl(tt))
    case T.VAot{+a0, +a1} <> +tt:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => L11.cv.own1(T.VAot{a0, a1}) <> zs,
        D3.own.rows(T.inl.seal(tt)),
        T.inl.seal(D3.own.rows(tt)), aq.oinl(tt))
    case T.VAots{+a0, +a1} <> +tt:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => L11.cv.own1(T.VAots{a0, a1}) <> zs,
        D3.own.rows(T.inl.seal(tt)),
        T.inl.seal(D3.own.rows(tt)), aq.oinl(tt))
    case T.VPair{+nn, T.VStr{+b0}} <> +tt:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => L11.cv.own1(T.VPair{nn, T.VStr{b0}}) <> zs,
        D3.own.rows(T.inl.seal(tt)),
        T.inl.seal(D3.own.rows(tt)), aq.oinl(tt))
    case T.VPair{+nn, T.VSpan{+b0, +b1}} <> +tt:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => L11.cv.own1(T.VPair{nn, T.VSpan{b0, b1}}) <> zs,
        D3.own.rows(T.inl.seal(tt)),
        T.inl.seal(D3.own.rows(tt)), aq.oinl(tt))
    case T.VPair{+nn, T.VInt{+b0, +b1}} <> +tt:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => L11.cv.own1(T.VPair{nn, T.VInt{b0, b1}}) <> zs,
        D3.own.rows(T.inl.seal(tt)),
        T.inl.seal(D3.own.rows(tt)), aq.oinl(tt))
    case T.VPair{+nn, T.VFlo{+b0, +b1}} <> +tt:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => L11.cv.own1(T.VPair{nn, T.VFlo{b0, b1}}) <> zs,
        D3.own.rows(T.inl.seal(tt)),
        T.inl.seal(D3.own.rows(tt)), aq.oinl(tt))
    case T.VPair{+nn, T.VBool{+b0}} <> +tt:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => L11.cv.own1(T.VPair{nn, T.VBool{b0}}) <> zs,
        D3.own.rows(T.inl.seal(tt)),
        T.inl.seal(D3.own.rows(tt)), aq.oinl(tt))
    case T.VPair{+nn, T.VWhen{+b0}} <> +tt:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => L11.cv.own1(T.VPair{nn, T.VWhen{b0}}) <> zs,
        D3.own.rows(T.inl.seal(tt)),
        T.inl.seal(D3.own.rows(tt)), aq.oinl(tt))
    case T.VPair{+nn, T.VArr{+b0}} <> +tt:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => L11.cv.own1(T.VPair{nn, T.VArr{b0}}) <> zs,
        D3.own.rows(T.inl.seal(tt)),
        T.inl.seal(D3.own.rows(tt)), aq.oinl(tt))
    case T.VPair{+nn, T.VInl{+b0}} <> +tt:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => L11.cv.own1(T.VPair{nn, T.VInl{b0}}) <> zs,
        D3.own.rows(T.inl.seal(tt)),
        T.inl.seal(D3.own.rows(tt)), aq.oinl(tt))
    case T.VPair{+nn, T.VAot{+b0, +b1}} <> +tt:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => L11.cv.own1(T.VPair{nn, T.VAot{b0, b1}}) <> zs,
        D3.own.rows(T.inl.seal(tt)),
        T.inl.seal(D3.own.rows(tt)), aq.oinl(tt))
    case T.VPair{+nn, T.VAots{+b0, +b1}} <> +tt:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => L11.cv.own1(T.VPair{nn, T.VAots{b0, b1}}) <> zs,
        D3.own.rows(T.inl.seal(tt)),
        T.inl.seal(D3.own.rows(tt)), aq.oinl(tt))
    case T.VPair{+nn, T.VPair{+b0, +b1}} <> +tt:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => L11.cv.own1(T.VPair{nn, T.VPair{b0, b1}}) <> zs,
        D3.own.rows(T.inl.seal(tt)),
        T.inl.seal(D3.own.rows(tt)), aq.oinl(tt))

# a value own reads as vv in a list, and the rest as ri: the list with it in
# front as vv in front of ri
def aq.cons2(
  +xv: T.Val,
  +its: List<&2, T.Val>,
  +vv: T.Val,
  +ri: List<&2, T.Val>,
  +hc: {L11.cv.own1(xv) == vv : T.Val},
  +hi: {D3.own.rows(its) == ri : List<&2, T.Val>}
) -> {D3.own.rows(xv <> its) == vv <> ri : List<&2, T.Val>}:
  %Equal.sym(List<&2, T.Val>, D3.own.rows(xv <> its), L11.cv.own1(xv) <> D3.own.rows(its), M22.cv.own.cons(xv, its))
    : {_ == vv <> ri : List<&2, T.Val>}
  %Equal.sym(T.Val, L11.cv.own1(xv), vv, hc) : {_ <> D3.own.rows(its) == vv <> ri : List<&2, T.Val>}
  %Equal.sym(List<&2, T.Val>, D3.own.rows(its), ri, hi) : {vv <> _ == vv <> ri : List<&2, T.Val>}
  {==}

# WP-A: values of every kind, nested to any depth. One induction over the
# value nodes (aq.rd) proves three claims of each: as a value from a value
# state or an array's item (aq.VT), as an array's items from where the
# array waits for one (aq.IT), and as an inline table's keyvals from where
# it waits for a key (aq.KT); the claims a node's rule rules out hold as g.ok
# refuses it (aq.nov, aq.noi, aq.nok). Each is taken over its continuation:
# the rest of the text read, own-level, to a document G, from the state the
# node leaves: a value placed (aq.vk), the frame's items (aq.ik), or the
# frame's rows (aq.rk); or, from an error the node sets, the document of the
# error and the rows as they were, which the replay keeps from then on.

# the rest after an array's items, by the replay's error: with none, from
# where the array waits after its items, with items own reads as the
# replay's; with one, the document of the error and the rows
def aq.ik2(
  +bd: String,
  +_ri: List<&2, T.Val>,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +at: List<&2, String>,
  +sv: List<&2, String>,
  +sk0: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  PP: T.Doc -> Type
) -> Type:
  match bd:
    case SNil{}:
      @its: List<&2, T.Val> -> @sp: Bool -> @b2: T.Lex -> @q2: T.QKind -> @u2: U32 -> @l2: U32 ->
        @hi: {D3.own.rows(its) == _ri : List<&2, T.Val>} ->
        PP(T.doc.read(rest, T.MScan{M11.ap.s(aq.alx(sp), b2, rw, hs, at, sv, q2, T.CArr{its, sv, at} <> sk0, u2, l2,
            ab)}))
    case SCon{+c0, +cs}:
      PP(T.Doc{SCon{c0, cs}, T.rows.seal(rw)})

# the rest after an array's items, by the replay's reading of them
def aq.ik(
  +rr: D5.RpAcc,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +at: List<&2, String>,
  +sv: List<&2, String>,
  +sk0: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  PP: T.Doc -> Type
) -> Type:
  match rr:
    case D5.RaItems{ri, bd}:
      aq.ik2(bd, ri, rw, hs, at, sv, sk0, ab, rest, PP)
    case D5.RaVal{_v, _b}:
      Unit
    case D5.RaRows{_r, _b}:
      Unit

# the rest after an inline table's keyvals, by the replay's error: with
# none, from where the table waits after a keyval, with rows own reads as
# the replay's; with one, the document of the error and the rows
def aq.rk2(
  +bd: String,
  +_ri: List<&2, T.Val>,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +at: List<&2, String>,
  +sv: List<&2, String>,
  +sk0: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  PP: T.Doc -> Type
) -> Type:
  match bd:
    case SNil{}:
      @inl: List<&2, T.Val> -> @b2: T.Lex -> @q2: T.QKind -> @u2: U32 -> @l2: U32 ->
        @hi: {D3.own.rows(inl) == _ri : List<&2, T.Val>} ->
        PP(T.doc.read(rest, T.MScan{M11.ap.s(T.LInlC{}, b2, rw, hs, at, [], q2, T.CInl{inl, sv, at} <> sk0, u2, l2,
            ab)}))
    case SCon{+c0, +cs}:
      PP(T.Doc{SCon{c0, cs}, T.rows.seal(rw)})

# the rest after an inline table's keyvals, by the replay's reading of them
def aq.rk(
  +rr: D5.RpAcc,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +at: List<&2, String>,
  +sv: List<&2, String>,
  +sk0: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  PP: T.Doc -> Type
) -> Type:
  match rr:
    case D5.RaRows{ri, bd}:
      aq.rk2(bd, ri, rw, hs, at, sv, sk0, ab, rest, PP)
    case D5.RaVal{_v, _b}:
      Unit
    case D5.RaItems{_i, _b}:
      Unit

# the continuations over the claim that own reads the document as G
def aq.VKG(
  +rr: D5.RpAcc,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  +G: T.Doc
) -> Type:
  aq.vk(rr, rw, hs, he, ps, sk, ab, rest, dd => {D3.own(dd) == G : T.Doc})

# of the items
def aq.IKG(
  +rr: D5.RpAcc,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +at: List<&2, String>,
  +sv: List<&2, String>,
  +sk0: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  +G: T.Doc
) -> Type:
  aq.ik(rr, rw, hs, at, sv, sk0, ab, rest, dd => {D3.own(dd) == G : T.Doc})

# and of the rows
def aq.RKG(
  +rr: D5.RpAcc,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +at: List<&2, String>,
  +sv: List<&2, String>,
  +sk0: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  +G: T.Doc
) -> Type:
  aq.rk(rr, rw, hs, at, sv, sk0, ab, rest, dd => {D3.own(dd) == G : T.Doc})

# the continuation of a value node read from no error
def aq.VKV(
  +val: D6.GVal,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  +G: T.Doc
) -> Type:
  aq.VKG(D5.replay.go(val, D5.RaVal{T.VArr{[]}, ""}), rw, hs, he, ps, sk, ab, rest, G)

# the items continuation of a node read from the items ri
def aq.IKN(
  +nd: D6.GVal,
  +ri: List<&2, T.Val>,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +at: List<&2, String>,
  +sv: List<&2, String>,
  +sk0: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  +G: T.Doc
) -> Type:
  aq.IKG(D5.replay.go(nd, D5.RaItems{ri, ""}), rw, hs, at, sv, sk0, ab, rest, G)

# and the rows continuation of one read from the rows ri
def aq.RKN(
  +nd: D6.GVal,
  +ri: List<&2, T.Val>,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +at: List<&2, String>,
  +sv: List<&2, String>,
  +sk0: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  +G: T.Doc
) -> Type:
  aq.RKG(D5.replay.go(nd, D5.RaRows{ri, ""}), rw, hs, at, sv, sk0, ab, rest, G)

# the items after an error, from any items read so far, to the document of
# the error and the rows
def aq.IKE(
  +_rv: D6.GVal,
  +c0: Char,
  +cs: String,
  +rw: List<&2, T.Val>,
  +_hs: List<&2, String>,
  +_at: List<&2, String>,
  +_sv: List<&2, String>,
  +_sk0: List<&2, T.Ctx>,
  +_ab: Bool,
  +_rest: String,
  -PP: T.Doc -> Type
) -> Type:
  @x2: List<&2, T.Val> -> aq.ik(D5.replay.go(_rv, D5.RaItems{x2, SCon{c0, cs}}), rw, _hs, _at, _sv, _sk0, _ab,
    _rest, PP) ->
    PP(T.Doc{SCon{c0, cs}, T.rows.seal(rw)})

# and so does one over the items
def aq.ikt(
  +r1: D5.RpAcc,
  +r2: D5.RpAcc,
  +ee: {r1 == r2 : D5.RpAcc},
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +at: List<&2, String>,
  +sv: List<&2, String>,
  +sk0: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  kk: aq.ik(r1, rw, hs, at, sv, sk0, ab, rest, PP)
) -> aq.ik(r2, rw, hs, at, sv, sk0, ab, rest, PP):
  %ee : aq.ik(_, rw, hs, at, sv, sk0, ab, rest, PP)
  kk

# and one over the rows
def aq.rkt(
  +r1: D5.RpAcc,
  +r2: D5.RpAcc,
  +ee: {r1 == r2 : D5.RpAcc},
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +at: List<&2, String>,
  +sv: List<&2, String>,
  +sk0: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  kk: aq.rk(r1, rw, hs, at, sv, sk0, ab, rest, PP)
) -> aq.rk(r2, rw, hs, at, sv, sk0, ab, rest, PP):
  %ee : aq.rk(_, rw, hs, at, sv, sk0, ab, rest, PP)
  kk

# whether a node is an inline table's keyvals or one keyval, as its rule
# allows
def aq.kvok(nd: D6.GVal) -> Bool:
  match nd:
    case D6.GKeyval{k, a, b, v}:
      D1.g.ok.val(D6.GKeyval{k, a, b, v}, D1.RKeyval{})
    case D6.GInlineTableKeyvals{kv, a, b, r}:
      D1.g.ok.val(D6.GInlineTableKeyvals{kv, a, b, r}, D1.RInlineTableKeyvals{})
    case D6.GInlineTableKeyvalsLast{kv}:
      D1.g.ok.val(D6.GInlineTableKeyvalsLast{kv}, D1.RInlineTableKeyvals{})
    case _:
      False{}

# a keyval of the grammar is one aq.kvok takes
def aq.kvok.k(
  nd: D6.GVal,
  +hh: {D1.g.ok.val(nd, D1.RKeyval{}) == True{} : Bool}
) -> {aq.kvok(nd) == True{} : Bool}:
  match nd:
    case D6.GvString{_a0}:
      Eq.bit.absurd(&2, {aq.kvok(D6.GvString{_a0}) == True{} : Bool}, hh)
    case D6.GvBoolean{_a0}:
      Eq.bit.absurd(&2, {aq.kvok(D6.GvBoolean{_a0}) == True{} : Bool}, hh)
    case D6.GvArrayEmpty{_a0}:
      Eq.bit.absurd(&2, {aq.kvok(D6.GvArrayEmpty{_a0}) == True{} : Bool}, hh)
    case D6.GvArray{_a0, _a1}:
      Eq.bit.absurd(&2, {aq.kvok(D6.GvArray{_a0, _a1}) == True{} : Bool}, hh)
    case D6.GvInlineTableEmpty{_a0, _a1}:
      Eq.bit.absurd(&2, {aq.kvok(D6.GvInlineTableEmpty{_a0, _a1}) == True{} : Bool}, hh)
    case D6.GvInlineTable{_a0, _a1, _a2}:
      Eq.bit.absurd(&2, {aq.kvok(D6.GvInlineTable{_a0, _a1, _a2}) == True{} : Bool}, hh)
    case D6.GvDateTime{_a0}:
      Eq.bit.absurd(&2, {aq.kvok(D6.GvDateTime{_a0}) == True{} : Bool}, hh)
    case D6.GvFloat{_a0}:
      Eq.bit.absurd(&2, {aq.kvok(D6.GvFloat{_a0}) == True{} : Bool}, hh)
    case D6.GvInteger{_a0}:
      Eq.bit.absurd(&2, {aq.kvok(D6.GvInteger{_a0}) == True{} : Bool}, hh)
    case D6.GArrayValues{_a0, _a1, _a2, _a3}:
      Eq.bit.absurd(&2, {aq.kvok(D6.GArrayValues{_a0, _a1, _a2, _a3}) == True{} : Bool}, hh)
    case D6.GArrayValuesLast{_a0, _a1, _a2, _a3}:
      Eq.bit.absurd(&2, {aq.kvok(D6.GArrayValuesLast{_a0, _a1, _a2, _a3}) == True{} : Bool}, hh)
    case D6.GInlineTableKeyvals{_a0, _a1, _a2, _a3}:
      Eq.bit.absurd(&2, {aq.kvok(D6.GInlineTableKeyvals{_a0, _a1, _a2, _a3}) == True{} : Bool}, hh)
    case D6.GInlineTableKeyvalsLast{_a0}:
      Eq.bit.absurd(&2, {aq.kvok(D6.GInlineTableKeyvalsLast{_a0}) == True{} : Bool}, hh)
    case D6.GKeyval{_a0, _a1, _a2, _a3}:
      hh

# and so are an inline table's keyvals
def aq.kvok.i(
  nd: D6.GVal,
  +hh: {D1.g.ok.val(nd, D1.RInlineTableKeyvals{}) == True{} : Bool}
) -> {aq.kvok(nd) == True{} : Bool}:
  match nd:
    case D6.GvString{_a0}:
      Eq.bit.absurd(&2, {aq.kvok(D6.GvString{_a0}) == True{} : Bool}, hh)
    case D6.GvBoolean{_a0}:
      Eq.bit.absurd(&2, {aq.kvok(D6.GvBoolean{_a0}) == True{} : Bool}, hh)
    case D6.GvArrayEmpty{_a0}:
      Eq.bit.absurd(&2, {aq.kvok(D6.GvArrayEmpty{_a0}) == True{} : Bool}, hh)
    case D6.GvArray{_a0, _a1}:
      Eq.bit.absurd(&2, {aq.kvok(D6.GvArray{_a0, _a1}) == True{} : Bool}, hh)
    case D6.GvInlineTableEmpty{_a0, _a1}:
      Eq.bit.absurd(&2, {aq.kvok(D6.GvInlineTableEmpty{_a0, _a1}) == True{} : Bool}, hh)
    case D6.GvInlineTable{_a0, _a1, _a2}:
      Eq.bit.absurd(&2, {aq.kvok(D6.GvInlineTable{_a0, _a1, _a2}) == True{} : Bool}, hh)
    case D6.GvDateTime{_a0}:
      Eq.bit.absurd(&2, {aq.kvok(D6.GvDateTime{_a0}) == True{} : Bool}, hh)
    case D6.GvFloat{_a0}:
      Eq.bit.absurd(&2, {aq.kvok(D6.GvFloat{_a0}) == True{} : Bool}, hh)
    case D6.GvInteger{_a0}:
      Eq.bit.absurd(&2, {aq.kvok(D6.GvInteger{_a0}) == True{} : Bool}, hh)
    case D6.GArrayValues{_a0, _a1, _a2, _a3}:
      Eq.bit.absurd(&2, {aq.kvok(D6.GArrayValues{_a0, _a1, _a2, _a3}) == True{} : Bool}, hh)
    case D6.GArrayValuesLast{_a0, _a1, _a2, _a3}:
      Eq.bit.absurd(&2, {aq.kvok(D6.GArrayValuesLast{_a0, _a1, _a2, _a3}) == True{} : Bool}, hh)
    case D6.GInlineTableKeyvals{_a0, _a1, _a2, _a3}:
      hh
    case D6.GInlineTableKeyvalsLast{_a0}:
      hh
    case D6.GKeyval{_a0, _a1, _a2, _a3}:
      Eq.bit.absurd(&2, {aq.kvok(D6.GKeyval{_a0, _a1, _a2, _a3}) == True{} : Bool}, hh)

# a value node reads the same from every reading with the same error
def aq.goval(
  vv: D6.GVal,
  +acc: D5.RpAcc,
  +ok: {D1.g.ok.val(vv, D1.RVal{}) == True{} : Bool}
) -> {D5.replay.go(vv, acc) == D5.replay.go(vv, D5.RaVal{T.VArr{[]}, D5.replay.bad(acc)}) : D5.RpAcc}:
  match vv:
    case D6.GvString{_a0}:
      {==}
    case D6.GvBoolean{_a0}:
      {==}
    case D6.GvArrayEmpty{_a0}:
      {==}
    case D6.GvArray{_a0, _a1}:
      {==}
    case D6.GvInlineTableEmpty{_a0, _a1}:
      {==}
    case D6.GvInlineTable{_a0, _a1, _a2}:
      {==}
    case D6.GvDateTime{_a0}:
      {==}
    case D6.GvFloat{_a0}:
      {==}
    case D6.GvInteger{_a0}:
      {==}
    case D6.GArrayValues{_a0, _a1, _a2, _a3}:
      Eq.bit.absurd(&2, {D5.replay.go(D6.GArrayValues{_a0, _a1, _a2, _a3},
        acc) == D5.replay.go(D6.GArrayValues{_a0, _a1, _a2, _a3}, D5.RaVal{T.VArr{[]},
          D5.replay.bad(acc)}) : D5.RpAcc}, ok)
    case D6.GArrayValuesLast{_a0, _a1, _a2, _a3}:
      Eq.bit.absurd(&2, {D5.replay.go(D6.GArrayValuesLast{_a0, _a1, _a2, _a3},
        acc) == D5.replay.go(D6.GArrayValuesLast{_a0, _a1, _a2, _a3}, D5.RaVal{T.VArr{[]},
          D5.replay.bad(acc)}) : D5.RpAcc}, ok)
    case D6.GInlineTableKeyvals{_a0, _a1, _a2, _a3}:
      Eq.bit.absurd(&2, {D5.replay.go(D6.GInlineTableKeyvals{_a0, _a1, _a2, _a3},
        acc) == D5.replay.go(D6.GInlineTableKeyvals{_a0, _a1, _a2, _a3}, D5.RaVal{T.VArr{[]},
          D5.replay.bad(acc)}) : D5.RpAcc}, ok)
    case D6.GInlineTableKeyvalsLast{_a0}:
      Eq.bit.absurd(&2, {D5.replay.go(D6.GInlineTableKeyvalsLast{_a0},
        acc) == D5.replay.go(D6.GInlineTableKeyvalsLast{_a0}, D5.RaVal{T.VArr{[]},
          D5.replay.bad(acc)}) : D5.RpAcc}, ok)
    case D6.GKeyval{_a0, _a1, _a2, _a3}:
      Eq.bit.absurd(&2, {D5.replay.go(D6.GKeyval{_a0, _a1, _a2, _a3}, acc) == D5.replay.go(D6.GKeyval{_a0,
        _a1, _a2, _a3}, D5.RaVal{T.VArr{[]}, D5.replay.bad(acc)}) : D5.RpAcc}, ok)

# a value read from an array's item or after `=`, then the rest: own reads
# the document as G, given the continuation
def aq.VT(+val: D6.GVal) -> Type:
  @m: Bool -> @rw: List<&2, T.Val> -> @hs: List<&2, String> -> @he: List<&2, String> -> @ps: List<&2, String> ->
    @bk: T.Lex -> @qk: T.QKind -> @sk: List<&2, T.Ctx> -> @un: U32 -> @lf: U32 -> @ab: Bool -> @rest: String ->
    @G: T.Doc -> @ok: {D1.g.ok.val(val, D1.RVal{}) == True{} : Bool} ->
    @es: {D3.short(D6.g.val.text(val, rest)) == True{} : Bool} -> @hf: {aq.fol(rest) == True{} : Bool} ->
    @kk: aq.vk(D5.replay.go(val, D5.RaVal{T.VArr{[]}, ""}), rw, hs, he, ps, sk, ab, rest, dd =>
      {D3.own(dd) == G : T.Doc}) ->
    {D3.own(T.doc.read(D6.g.val.text(val, rest), T.MScan{aq.vst(m, rw, hs, he, ps, bk, qk, sk, un, lf,
      ab)})) == G : T.Doc}

# an array's items read from where it waits for one, then the rest
def aq.IT(+nd: D6.GVal) -> Type:
  @rw: List<&2, T.Val> -> @hs: List<&2, String> -> @at: List<&2, String> -> @p: List<&2, String> ->
    @sv: List<&2, String> -> @sk0: List<&2, T.Ctx> -> @its: List<&2, T.Val> -> @ri: List<&2, T.Val> -> @bk: T.Lex ->
    @qk: T.QKind -> @un: U32 -> @lf: U32 -> @ab: Bool -> @rest: String -> @G: T.Doc ->
    @ok: {D1.g.ok.val(nd, D1.RArrayValues{}) == True{} : Bool} ->
    @es: {D3.short(D6.g.val.text(nd, rest)) == True{} : Bool} -> @hf: {aq.fol(rest) == True{} : Bool} ->
    @hi: {D3.own.rows(its) == ri : List<&2, T.Val>} ->
    @kk: aq.ik(D5.replay.go(nd, D5.RaItems{ri, ""}), rw, hs, at, sv, sk0, ab, rest, dd =>
      {D3.own(dd) == G : T.Doc}) ->
    {D3.own(T.doc.read(D6.g.val.text(nd, rest), T.MScan{M11.ap.s(T.LArr{}, bk, rw, hs, at, p, qk, T.CArr{its, sv,
      at} <> sk0, un, lf, ab)})) == G : T.Doc}

# an inline table's keyvals read from where it waits for a key, then the
# rest
def aq.KT(+nd: D6.GVal) -> Type:
  @pos: Bool -> @rw: List<&2, T.Val> -> @hs: List<&2, String> -> @at: List<&2, String> -> @sv: List<&2, String> ->
    @sk0: List<&2, T.Ctx> -> @inl: List<&2, T.Val> -> @ri: List<&2, T.Val> -> @bk: T.Lex -> @qk: T.QKind -> @un: U32 ->
    @lf: U32 -> @ab: Bool -> @rest: String -> @G: T.Doc -> @ok: {aq.kvok(nd) == True{} : Bool} ->
    @es: {D3.short(D6.g.val.text(nd, rest)) == True{} : Bool} -> @hf: {aq.fol(rest) == True{} : Bool} ->
    @hi: {D3.own.rows(inl) == ri : List<&2, T.Val>} ->
    @kk: aq.rk(D5.replay.go(nd, D5.RaRows{ri, ""}), rw, hs, at, sv, sk0, ab, rest, dd =>
      {D3.own(dd) == G : T.Doc}) ->
    {D3.own(T.doc.read(D6.g.val.text(nd, rest), T.MScan{M11.ap.s(L9.k3.pos.lex(aq.kpos(pos)), bk, rw, hs, at, [],
      qk, T.CInl{inl, sv, at} <> sk0, un, lf, ab)})) == G : T.Doc}

# one of the three claims: a value (a), the items (b), or the keyvals
def aq.RDW(+a: Bool, +b: Bool, +nd: D6.GVal) -> Type:
  match a:
    case True{}:
      aq.VT(nd)
    case False{}:
      match b:
        case True{}:
          aq.IT(nd)
        case False{}:
          aq.KT(nd)

# the three claims of a node
def aq.RD(+_nd: D6.GVal) -> Type:
  @a: Bool -> @b: Bool -> aq.RDW(a, b, _nd)

# the claim asked for, from the three
def aq.pick(
  +a: Bool,
  +b: Bool,
  +_nd: D6.GVal,
  pv: aq.VT(_nd),
  pi: aq.IT(_nd),
  pk: aq.KT(_nd)
) -> aq.RDW(a, b, _nd):
  match a:
    case True{}:
      pv
    case False{}:
      match b:
        case True{}:
          pi
        case False{}:
          pk

# a node the value rule refuses: the value claim holds as g.ok refuses it
def aq.nov(
  +nd: D6.GVal,
  +hh: {D1.g.ok.val(nd, D1.RVal{}) == False{} : Bool}
) -> aq.VT(nd):
  +m => +rw => +hs => +he => +ps => +bk => +qk => +sk => +un => +lf => +ab => +rest => +G => ok => _es => _hf => _kk =>
    Eq.bit.absurd(&2, {D3.own(T.doc.read(D6.g.val.text(nd, rest), T.MScan{aq.vst(m, rw, hs, he, ps, bk, qk, sk,
      un, lf, ab)})) == G : T.Doc}, Equal.trans(Bool, False{}, D1.g.ok.val(nd, D1.RVal{}), True{}, Equal.sym(Bool,
        D1.g.ok.val(nd, D1.RVal{}), False{}, hh), ok))

# a node the array-values rule refuses: the items claim holds so
def aq.noi(
  +nd: D6.GVal,
  +hh: {D1.g.ok.val(nd, D1.RArrayValues{}) == False{} : Bool}
) -> aq.IT(nd):
  +rw => +hs => +at => +p => +sv => +sk0 => +its => +_ri => +bk => +qk => +un => +lf => +ab => +rest => +G => ok =>
    _es => _hf => _hi => _kk =>
    Eq.bit.absurd(&2, {D3.own(T.doc.read(D6.g.val.text(nd, rest), T.MScan{M11.ap.s(T.LArr{}, bk, rw, hs, at, p, qk,
      T.CArr{its, sv, at} <> sk0, un, lf, ab)})) == G : T.Doc}, Equal.trans(Bool, False{}, D1.g.ok.val(nd,
        D1.RArrayValues{}), True{}, Equal.sym(Bool, D1.g.ok.val(nd, D1.RArrayValues{}), False{}, hh), ok))

# a node that is no inline table's keyvals: the keyvals claim holds so
def aq.nok(
  +nd: D6.GVal,
  +hh: {aq.kvok(nd) == False{} : Bool}
) -> aq.KT(nd):
  +pos => +rw => +hs => +at => +sv => +sk0 => +inl => +_ri => +bk => +qk => +un => +lf => +ab => +rest => +G => ok =>
    _es => _hf => _hi => _kk =>
    Eq.bit.absurd(&2, {D3.own(T.doc.read(D6.g.val.text(nd, rest), T.MScan{M11.ap.s(L9.k3.pos.lex(aq.kpos(pos)), bk,
      rw, hs, at, [], qk, T.CInl{inl, sv, at} <> sk0, un, lf, ab)})) == G : T.Doc}, Equal.trans(Bool, False{},
        aq.kvok(nd), True{}, Equal.sym(Bool, aq.kvok(nd), False{}, hh), ok))

# an error an array's items reach keeps the document at the error and the
# rows: the items after one are read from it (aq.gobad)
def aq.ike.av(
  g0: D5.RpAcc,
  +rv: D6.GVal,
  +x: List<&2, T.Val>,
  +c0: Char,
  +cs: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +at: List<&2, String>,
  +sv: List<&2, String>,
  +sk0: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  +hg: {D5.replay.bad(g0) == SCon{c0, cs} : String},
  ih: aq.IKE(rv, c0, cs, rw, hs, at, sv, sk0, ab, rest, PP),
  kk: aq.ik(D5.replay.go(rv, D5.replay.item(g0, D5.RaItems{x, SCon{c0, cs}})), rw, hs, at, sv, sk0, ab, rest, PP)
) -> PP(T.Doc{SCon{c0, cs}, T.rows.seal(rw)}):
  match g0:
    case D5.RaVal{+v, +b}:
      ih(v <> x, aq.ikt(D5.replay.go(rv, D5.RaItems{v <> x, b}), D5.replay.go(rv, D5.RaItems{v <> x, SCon{c0,
        cs}}), Equal.cong(String, D5.RpAcc, bb => D5.replay.go(rv, D5.RaItems{v <> x, bb}), b, SCon{c0, cs},
          hg), rw, hs, at, sv, sk0, ab, rest, PP, kk))
    case D5.RaItems{_i, _b}:
      ih(x, kk)
    case D5.RaRows{_r, _b}:
      ih(x, kk)

# the last item read from an error
def aq.ike.avl(
  g0: D5.RpAcc,
  +x: List<&2, T.Val>,
  +c0: Char,
  +cs: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +at: List<&2, String>,
  +sv: List<&2, String>,
  +sk0: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  +hg: {D5.replay.bad(g0) == SCon{c0, cs} : String},
  kk: aq.ik(D5.replay.item(g0, D5.RaItems{x, SCon{c0, cs}}), rw, hs, at, sv, sk0, ab, rest, PP)
) -> PP(T.Doc{SCon{c0, cs}, T.rows.seal(rw)}):
  match g0:
    case D5.RaVal{+v, +b}:
      aq.ikt(D5.RaItems{v <> x, b}, D5.RaItems{v <> x, SCon{c0, cs}}, Equal.cong(String, D5.RpAcc, bb =>
        D5.RaItems{v <> x, bb}, b, SCon{c0, cs}, hg), rw, hs, at, sv, sk0, ab, rest, PP, kk)
    case D5.RaItems{_i, _b}:
      kk
    case D5.RaRows{_r, _b}:
      kk

# an array's items read from an error: the document of the error and the
# rows
def aq.ike(
  nd: D6.GVal,
  +x: List<&2, T.Val>,
  +c0: Char,
  +cs: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +at: List<&2, String>,
  +sv: List<&2, String>,
  +sk0: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  +ok: {D1.g.ok.val(nd, D1.RArrayValues{}) == True{} : Bool},
  kk: aq.ik(D5.replay.go(nd, D5.RaItems{x, SCon{c0, cs}}), rw, hs, at, sv, sk0, ab, rest, PP)
) -> PP(T.Doc{SCon{c0, cs}, T.rows.seal(rw)}):
  match nd:
    case D6.GArrayValues{+wa, +val, +wb, +rv}:
      aq.ike.av(D5.replay.go(val, D5.RaItems{x, SCon{c0, cs}}), rv, x, c0, cs, rw, hs, at, sv, sk0, ab, rest, PP,
        aq.gobad(val, D5.RaItems{x, SCon{c0, cs}}, SCon{c0, cs}, {==}, {==}), +x2 => k2 => aq.ike(rv, x2, c0, cs,
          rw, hs, at, sv, sk0, ab, rest, PP, Eq.and.right(D1.g.ok.wcn(wb), D1.g.ok.val(rv, D1.RArrayValues{}),
            Eq.and.right(D1.g.ok.val(val, D1.RVal{}), Bool.and(D1.g.ok.wcn(wb), D1.g.ok.val(rv,
              D1.RArrayValues{})), Eq.and.right(D1.g.ok.wcn(wa), Bool.and(D1.g.ok.val(val, D1.RVal{}),
                Bool.and(D1.g.ok.wcn(wb), D1.g.ok.val(rv, D1.RArrayValues{}))), ok))), k2), kk)
    case D6.GArrayValuesLast{_wa, +val, _wb, _sep}:
      aq.ike.avl(D5.replay.go(val, D5.RaItems{x, SCon{c0, cs}}), x, c0, cs, rw, hs, at, sv, sk0, ab, rest, PP,
        aq.gobad(val, D5.RaItems{x, SCon{c0, cs}}, SCon{c0, cs}, {==}, {==}), kk)
    case D6.GvString{_a0}:
      Eq.bit.absurd(&1, PP(T.Doc{SCon{c0, cs}, T.rows.seal(rw)}), ok)
    case D6.GvBoolean{_a0}:
      Eq.bit.absurd(&1, PP(T.Doc{SCon{c0, cs}, T.rows.seal(rw)}), ok)
    case D6.GvArrayEmpty{_a0}:
      Eq.bit.absurd(&1, PP(T.Doc{SCon{c0, cs}, T.rows.seal(rw)}), ok)
    case D6.GvArray{_a0, _a1}:
      Eq.bit.absurd(&1, PP(T.Doc{SCon{c0, cs}, T.rows.seal(rw)}), ok)
    case D6.GvInlineTableEmpty{_a0, _a1}:
      Eq.bit.absurd(&1, PP(T.Doc{SCon{c0, cs}, T.rows.seal(rw)}), ok)
    case D6.GvInlineTable{_a0, _a1, _a2}:
      Eq.bit.absurd(&1, PP(T.Doc{SCon{c0, cs}, T.rows.seal(rw)}), ok)
    case D6.GvDateTime{_a0}:
      Eq.bit.absurd(&1, PP(T.Doc{SCon{c0, cs}, T.rows.seal(rw)}), ok)
    case D6.GvFloat{_a0}:
      Eq.bit.absurd(&1, PP(T.Doc{SCon{c0, cs}, T.rows.seal(rw)}), ok)
    case D6.GvInteger{_a0}:
      Eq.bit.absurd(&1, PP(T.Doc{SCon{c0, cs}, T.rows.seal(rw)}), ok)
    case D6.GInlineTableKeyvals{_a0, _a1, _a2, _a3}:
      Eq.bit.absurd(&1, PP(T.Doc{SCon{c0, cs}, T.rows.seal(rw)}), ok)
    case D6.GInlineTableKeyvalsLast{_a0}:
      Eq.bit.absurd(&1, PP(T.Doc{SCon{c0, cs}, T.rows.seal(rw)}), ok)
    case D6.GKeyval{_a0, _a1, _a2, _a3}:
      Eq.bit.absurd(&1, PP(T.Doc{SCon{c0, cs}, T.rows.seal(rw)}), ok)

# a keyval of an inline table walked from an error leaves its rows
def aq.kvst.kv(
  +names: List<&2, String>,
  g0: D5.RpAcc,
  +x: List<&2, T.Val>,
  +c0: Char,
  +cs: String,
  +hg: {D5.replay.bad(g0) == SCon{c0, cs} : String}
) -> {D5.replay.kv(names, g0, D5.RaRows{x, SCon{c0, cs}}) == D5.RaRows{x, SCon{c0, cs}} : D5.RpAcc}:
  match g0:
    case D5.RaVal{+v, +b}:
      %Equal.sym(String, b, SCon{c0, cs}, hg) : {D5.replay.end.rows(T.tree.walk(names, T.Tw{x, T.JPut{v}, [], _, "",
        [], True{}}, 0)) == D5.RaRows{x, SCon{c0, cs}} : D5.RpAcc}
      %Equal.sym(T.End, T.tree.walk(names, T.Tw{x, T.JPut{v}, [], SCon{c0, cs}, "", [], True{}}, 0), T.End{x, SCon{c0,
        cs}, []}, L4.failed_walk_changes_nothing(names, x, T.JPut{v}, SCon{c0, cs}, "", [], True{}, 0,
          {==})) : {D5.replay.end.rows(_) == D5.RaRows{x, SCon{c0, cs}} : D5.RpAcc}
      {==}
    case D5.RaItems{_i, _b}:
      {==}
    case D5.RaRows{_r, _b}:
      {==}

# an inline table's keyvals read from an error leave its rows
def aq.kvst(
  nd: D6.GVal,
  +x: List<&2, T.Val>,
  +c0: Char,
  +cs: String,
  +ok: {aq.kvok(nd) == True{} : Bool}
) -> {D5.replay.go(nd, D5.RaRows{x, SCon{c0, cs}}) == D5.RaRows{x, SCon{c0, cs}} : D5.RpAcc}:
  match nd:
    case D6.GKeyval{+key, _wa, _wb, +val}:
      aq.kvst.kv(D1.g.key.names(key), D5.replay.go(val, D5.RaRows{x, SCon{c0, cs}}), x, c0, cs, aq.gobad(val,
        D5.RaRows{x, SCon{c0, cs}}, SCon{c0, cs}, {==}, {==}))
    case D6.GInlineTableKeyvals{+kv, +w1, +w2, +rv}:
      Equal.trans(D5.RpAcc, D5.replay.go(rv, D5.replay.go(kv, D5.RaRows{x, SCon{c0, cs}})), D5.replay.go(rv,
        D5.RaRows{x, SCon{c0, cs}}), D5.RaRows{x, SCon{c0, cs}}, Equal.cong(D5.RpAcc, D5.RpAcc, aa =>
          D5.replay.go(rv, aa), D5.replay.go(kv, D5.RaRows{x, SCon{c0, cs}}), D5.RaRows{x, SCon{c0, cs}},
            aq.kvst(kv, x, c0, cs, aq.kvok.k(kv, Eq.and.left(D1.g.ok.val(kv, D1.RKeyval{}),
              Bool.and(D2.abnf.ws(w1), Bool.and(D2.abnf.ws(w2), D1.g.ok.val(rv, D1.RInlineTableKeyvals{}))),
                ok)))), aq.kvst(rv, x, c0, cs, aq.kvok.i(rv, Eq.and.right(D2.abnf.ws(w2), D1.g.ok.val(rv,
                  D1.RInlineTableKeyvals{}), Eq.and.right(D2.abnf.ws(w1), Bool.and(D2.abnf.ws(w2),
                    D1.g.ok.val(rv, D1.RInlineTableKeyvals{})), Eq.and.right(D1.g.ok.val(kv, D1.RKeyval{}),
                      Bool.and(D2.abnf.ws(w1), Bool.and(D2.abnf.ws(w2), D1.g.ok.val(rv,
                        D1.RInlineTableKeyvals{}))), ok))))))
    case D6.GInlineTableKeyvalsLast{+kv}:
      aq.kvst(kv, x, c0, cs, aq.kvok.k(kv, ok))
    case D6.GvString{_a0}:
      Eq.bit.absurd(&2, {D5.replay.go(D6.GvString{_a0}, D5.RaRows{x, SCon{c0, cs}}) == D5.RaRows{x, SCon{c0,
        cs}} : D5.RpAcc}, ok)
    case D6.GvBoolean{_a0}:
      Eq.bit.absurd(&2, {D5.replay.go(D6.GvBoolean{_a0}, D5.RaRows{x, SCon{c0, cs}}) == D5.RaRows{x, SCon{c0,
        cs}} : D5.RpAcc}, ok)
    case D6.GvArrayEmpty{_a0}:
      Eq.bit.absurd(&2, {D5.replay.go(D6.GvArrayEmpty{_a0}, D5.RaRows{x, SCon{c0, cs}}) == D5.RaRows{x,
        SCon{c0, cs}} : D5.RpAcc}, ok)
    case D6.GvArray{_a0, _a1}:
      Eq.bit.absurd(&2, {D5.replay.go(D6.GvArray{_a0, _a1}, D5.RaRows{x, SCon{c0, cs}}) == D5.RaRows{x,
        SCon{c0, cs}} : D5.RpAcc}, ok)
    case D6.GvInlineTableEmpty{_a0, _a1}:
      Eq.bit.absurd(&2, {D5.replay.go(D6.GvInlineTableEmpty{_a0, _a1}, D5.RaRows{x, SCon{c0,
        cs}}) == D5.RaRows{x, SCon{c0, cs}} : D5.RpAcc}, ok)
    case D6.GvInlineTable{_a0, _a1, _a2}:
      Eq.bit.absurd(&2, {D5.replay.go(D6.GvInlineTable{_a0, _a1, _a2}, D5.RaRows{x, SCon{c0,
        cs}}) == D5.RaRows{x, SCon{c0, cs}} : D5.RpAcc}, ok)
    case D6.GvDateTime{_a0}:
      Eq.bit.absurd(&2, {D5.replay.go(D6.GvDateTime{_a0}, D5.RaRows{x, SCon{c0, cs}}) == D5.RaRows{x, SCon{c0,
        cs}} : D5.RpAcc}, ok)
    case D6.GvFloat{_a0}:
      Eq.bit.absurd(&2, {D5.replay.go(D6.GvFloat{_a0}, D5.RaRows{x, SCon{c0, cs}}) == D5.RaRows{x, SCon{c0,
        cs}} : D5.RpAcc}, ok)
    case D6.GvInteger{_a0}:
      Eq.bit.absurd(&2, {D5.replay.go(D6.GvInteger{_a0}, D5.RaRows{x, SCon{c0, cs}}) == D5.RaRows{x, SCon{c0,
        cs}} : D5.RpAcc}, ok)
    case D6.GArrayValues{_a0, _a1, _a2, _a3}:
      Eq.bit.absurd(&2, {D5.replay.go(D6.GArrayValues{_a0, _a1, _a2, _a3}, D5.RaRows{x, SCon{c0,
        cs}}) == D5.RaRows{x, SCon{c0, cs}} : D5.RpAcc}, ok)
    case D6.GArrayValuesLast{_a0, _a1, _a2, _a3}:
      Eq.bit.absurd(&2, {D5.replay.go(D6.GArrayValuesLast{_a0, _a1, _a2, _a3}, D5.RaRows{x, SCon{c0,
        cs}}) == D5.RaRows{x, SCon{c0, cs}} : D5.RpAcc}, ok)

# an inline table's keyvals read from an error: the document of the error
# and the rows
def aq.rke(
  +nd: D6.GVal,
  +x: List<&2, T.Val>,
  +c0: Char,
  +cs: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +at: List<&2, String>,
  +sv: List<&2, String>,
  +sk0: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  +ok: {aq.kvok(nd) == True{} : Bool},
  kk: aq.rk(D5.replay.go(nd, D5.RaRows{x, SCon{c0, cs}}), rw, hs, at, sv, sk0, ab, rest, PP)
) -> PP(T.Doc{SCon{c0, cs}, T.rows.seal(rw)}):
  aq.rkt(D5.replay.go(nd, D5.RaRows{x, SCon{c0, cs}}), D5.RaRows{x, SCon{c0, cs}}, aq.kvst(nd, x, c0, cs, ok),
    rw, hs, at, sv, sk0, ab, rest, PP, kk)

# a string of any form as an array's item
def aq.stra(
  +st: D6.GString,
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
  +ab: Bool,
  -PP: T.Doc -> Type,
  +ok: {D1.g.ok.str(st) == True{} : Bool},
  +es: {D3.short(D6.g.str.text(st, rest)) == True{} : Bool},
  +hf: {aq.fol(rest) == True{} : Bool},
  kk: aq.VK(D6.GvString{st}, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(D6.g.str.text(st, rest), T.MScan{D3.s1.apos(rw, hs, he, ps, bk, qk, sk, un, lf, ab)})):
  L10.string_reads_as_denoted_in_array(st, ok, L10.string_short_in_document("", st, rest, es), rw, hs, he, ps, bk,
    qk, sk, un, lf, ab, rest, aq.free(rest, hf), PP, +xv => b2 => q2 => u2 => l2 => hh => aq.kstr(xv,
      D1.g.str.chars(st), b2, q2, u2, l2, rw, hs, he, ps, sk, ab, rest, PP, aq.holds(xv, D1.g.str.chars(st), hh),
        kk))

# a string, from either value state
def aq.v.str(
  +st: D6.GString,
  +m: Bool,
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
  +G: T.Doc,
  +ok: {D1.g.ok.str(st) == True{} : Bool},
  +es: {D3.short(D6.g.str.text(st, rest)) == True{} : Bool},
  +hf: {aq.fol(rest) == True{} : Bool},
  kk: aq.VKG(D5.replay.go(D6.GvString{st}, D5.RaVal{T.VArr{[]}, ""}), rw, hs, he, ps, sk, ab, rest, G)
) -> {D3.own(T.doc.read(D6.g.str.text(st, rest), T.MScan{aq.vst(m, rw, hs, he, ps, bk, qk, sk, un, lf,
  ab)})) == G : T.Doc}:
  match m:
    case True{}:
      aq.stra(st, rest, rw, hs, he, ps, bk, qk, sk, un, lf, ab, dd => {D3.own(dd) == G : T.Doc}, ok, es, hf, kk)
    case False{}:
      aq.str(st, rest, rw, hs, he, ps, bk, qk, sk, un, lf, ab, dd => {D3.own(dd) == G : T.Doc}, ok, es, hf, kk)

# a bare word, from either value state: an item's is read as after `=` once
# its first character is held (vl.arr.eq)
def aq.v.word(
  +cs: List<&2, Char>,
  +m: Bool,
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
  +G: T.Doc,
  +hw: {D3.bw.word(String.from_list(cs)) == True{} : Bool},
  +hf: {aq.fol(rest) == True{} : Bool},
  kk: aq.VKG(D5.replay.got(T.word.val(cs), ""), rw, hs, he, ps, sk, ab, rest, G)
) -> {D3.own(T.doc.read(String.append(String.from_list(cs), rest), T.MScan{aq.vst(m, rw, hs, he, ps, bk, qk, sk, un,
  lf, ab)})) == G : T.Doc}:
  match m:
    case True{}:
      %Equal.sym(T.Doc, T.doc.read(String.append(String.from_list(cs), rest), T.MScan{D3.s1.apos(rw, hs, he, ps, bk,
        qk, sk, un, lf, ab)}), T.doc.read(String.append(String.from_list(cs), rest), T.MScan{D3.vpos(rw, hs, he, ps,
          T.LVal{}, qk, sk, un, lf, ab)}), M2.vl.arr.eq(String.from_list(cs), hw, rest, rw, hs, he, ps, bk, qk, sk, un,
            lf, ab)) : {D3.own(_) == G : T.Doc}
      aq.word(cs, rest, rw, hs, he, ps, T.LVal{}, qk, sk, un, lf, ab, dd => {D3.own(dd) == G : T.Doc}, hw, hf, kk)
    case False{}:
      aq.word(cs, rest, rw, hs, he, ps, bk, qk, sk, un, lf, ab, dd => {D3.own(dd) == G : T.Doc}, hw, hf, kk)

# `]` after an array's items: the array of the items in order is placed
def aq.arrk2(
  +sp: Bool,
  +its: List<&2, T.Val>,
  +ri: List<&2, T.Val>,
  +b3: T.Lex,
  +q2: T.QKind,
  +u2: U32,
  +l2: U32,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  +G: T.Doc,
  +hi: {D3.own.rows(its) == ri : List<&2, T.Val>},
  kk: aq.VKG(D5.RaVal{T.VArr{List.reverse(&2, T.Val, ri)}, ""}, rw, hs, he, ps, sk, ab, rest, G)
) -> {D3.own(T.doc.read(SCon{']', rest}, T.MScan{M11.ap.s(aq.alx(sp), b3, rw, hs, he, ps, q2, T.CArr{its, ps, he} <> sk,
  u2, l2, ab)})) == G : T.Doc}:
  %Equal.sym(T.Mode, T.doc.scan(M11.ap.s(aq.alx(sp), b3, rw, hs, he, ps, q2, T.CArr{its, ps, he} <> sk, u2, l2, ab),
      ']'),
    T.MScan{T.take.top(sk, T.VArr{List.reverse(&2, T.Val, its)}, "", rw, hs, he, ps, b3, q2, u2, l2, ab, False{})},
      aq.aclose(sp, rw, hs, he, ps, its, ps, he, b3, q2, sk, u2, l2, ab)) : {D3.own(T.doc.read(rest, _)) == G : T.Doc}
  +hv = {Equal.cong(List<&2, T.Val>, T.Val, zs => T.VArr{zs}, D3.own.rows(List.reverse(&2, T.Val, its)),
    List.reverse(&2, T.Val, ri), M22.cv.own.rs(its, ri, hi)) : {T.VArr{D3.own.rows(List.reverse(&2, T.Val,
      its))} == T.VArr{List.reverse(&2, T.Val, ri)} : T.Val}}
  kk(T.VArr{List.reverse(&2, T.Val, its)}, b3, q2, u2, l2, hv, hv)

# an array's items read: ws-comment-newline and `]` close it, by the
# replay's reading of the items
def aq.arrk(
  +rr: D5.RpAcc,
  +wn: List<&2, D6.GWcn>,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  +G: T.Doc,
  +okw: {D1.g.ok.wcn(wn) == True{} : Bool},
  kk: aq.VKG(D5.replay.arr(rr), rw, hs, he, ps, sk, ab, rest, G)
) -> aq.ik(rr, rw, hs, he, ps, sk, ab, D6.g.wcn.text(wn, SCon{']', rest}), dd => {D3.own(dd) == G : T.Doc}):
  match rr:
    case D5.RaItems{+ri, +bd}:
      match bd:
        case SNil{}:
          +its => +sp => +b2 => +q2 => +u2 => +l2 => +hi =>
            aq.wcn(wn, SCon{']', rest}, aq.alx(sp), b2, rw, hs, he, ps, q2, T.CArr{its, ps, he} <> sk, u2, l2, ab,
              aq.alx.wsl(sp), aq.alx.coml(sp), aq.alx.nlx(sp), okw, dd => {D3.own(dd) == G : T.Doc}, +b3 =>
                aq.arrk2(sp, its, ri, b3, q2, u2, l2, rw, hs, he, ps, sk, ab, rest, G, hi, kk))
        case SCon{_c0, _cs}:
          kk
    case D5.RaVal{_v, _b}:
      Unit{}
    case D5.RaRows{_r, _b}:
      Unit{}

# an empty array
def aq.v.arr0(
  +wn: List<&2, D6.GWcn>,
  +m: Bool,
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
  +G: T.Doc,
  +okw: {D1.g.ok.wcn(wn) == True{} : Bool},
  kk: aq.VKG(D5.RaVal{T.VArr{[]}, ""}, rw, hs, he, ps, sk, ab, rest, G)
) -> {D3.own(T.doc.read(SCon{'[', D6.g.wcn.text(wn, SCon{']', rest})}, T.MScan{aq.vst(m, rw, hs, he, ps, bk, qk,
  sk, un, lf, ab)})) == G : T.Doc}:
  %Equal.sym(T.Mode, T.doc.scan(aq.vst(m, rw, hs, he, ps, bk, qk, sk, un, lf, ab), '['), T.MScan{M11.ap.s(T.LArr{},
    aq.bk0(m, bk), rw, hs, he, [], qk, T.CArr{[], ps, he} <> sk, un, lf, ab)}, aq.aopen(m, rw, hs, he, ps, bk, qk, sk,
      un, lf, ab)) : {D3.own(T.doc.read(D6.g.wcn.text(wn, SCon{']', rest}), _)) == G : T.Doc}
  aq.wcn(wn, SCon{']', rest}, T.LArr{}, aq.bk0(m, bk), rw, hs, he, [], qk, T.CArr{[], ps, he} <> sk, un, lf, ab, {==},
    {==}, {==}, okw, dd => {D3.own(dd) == G : T.Doc}, +b2 => aq.arrk2(True{}, [], [], b2, qk, un, lf, rw, hs, he,
      ps, sk, ab, rest, G, {==}, kk))

# an array with items
def aq.v.arr(
  +vals: D6.GVal,
  +wn: List<&2, D6.GWcn>,
  +m: Bool,
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
  +G: T.Doc,
  +okv: {D1.g.ok.val(vals, D1.RArrayValues{}) == True{} : Bool},
  +okw: {D1.g.ok.wcn(wn) == True{} : Bool},
  +es: {D3.short(D6.g.val.text(D6.GvArray{vals, wn}, rest)) == True{} : Bool},
  kk: aq.VKG(D5.replay.arr(D5.replay.go(vals, D5.RaItems{[], ""})), rw, hs, he, ps, sk, ab, rest, G),
  ih: aq.IT(vals)
) -> {D3.own(T.doc.read(SCon{'[', D6.g.val.text(vals, D6.g.wcn.text(wn, SCon{']', rest}))}, T.MScan{aq.vst(m,
  rw, hs, he, ps, bk, qk, sk, un, lf, ab)})) == G : T.Doc}:
  %Equal.sym(T.Mode, T.doc.scan(aq.vst(m, rw, hs, he, ps, bk, qk, sk, un, lf, ab), '['), T.MScan{M11.ap.s(T.LArr{},
    aq.bk0(m, bk), rw, hs, he, [], qk, T.CArr{[], ps, he} <> sk, un, lf, ab)}, aq.aopen(m, rw, hs, he, ps, bk, qk, sk,
      un, lf, ab)) : {D3.own(T.doc.read(D6.g.val.text(vals, D6.g.wcn.text(wn, SCon{']', rest})), _)) == G : T.Doc}
  ih(rw, hs, he, [], ps, sk, [], [], aq.bk0(m, bk), qk, un, lf, ab, D6.g.wcn.text(wn, SCon{']', rest}), G, okv,
    M23.gd.short.tail('[', D6.g.val.text(vals, D6.g.wcn.text(wn, SCon{']', rest})), es), aq.fol.wcn(wn, SCon{']',
      rest}, okw, {==}), {==}, aq.arrk(D5.replay.go(vals, D5.RaItems{[], ""}), wn, rw, hs, he, ps, sk, ab, rest,
        G, okw, kk))

# an empty inline table
def aq.v.inl0(
  +w1: String,
  +w2: String,
  +m: Bool,
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
  +G: T.Doc,
  +h1: {D2.abnf.ws(w1) == True{} : Bool},
  +h2: {D2.abnf.ws(w2) == True{} : Bool},
  kk: aq.VKG(D5.RaVal{T.VInl{[]}, ""}, rw, hs, he, ps, sk, ab, rest, G)
) -> {D3.own(T.doc.read(SCon{'{', String.append(w1, String.append(w2, SCon{'}', rest}))}, T.MScan{aq.vst(m, rw, hs,
  he, ps, bk, qk, sk, un, lf, ab)})) == G : T.Doc}:
  %Equal.sym(T.Mode, T.doc.scan(aq.vst(m, rw, hs, he, ps, bk, qk, sk, un, lf, ab), '{'), T.MScan{M11.ap.s(T.LInl{},
    aq.bk0(m, bk), rw, hs, he, [], qk, T.CInl{[], ps, he} <> sk, un, lf, ab)}, aq.iopen(m, rw, hs, he, ps, bk, qk, sk,
      un, lf, ab)) : {D3.own(T.doc.read(String.append(w1, String.append(w2, SCon{'}', rest})), _)) == G : T.Doc}
  %Equal.sym(T.Doc, T.doc.read(String.append(w1, String.append(w2, SCon{'}', rest})), T.MScan{M11.ap.s(T.LInl{},
      aq.bk0(m,
    bk), rw, hs, he, [], qk, T.CInl{[], ps, he} <> sk, un, lf, ab)}), T.doc.read(String.append(w2, SCon{'}', rest}),
      T.MScan{M11.ap.s(T.LInl{}, aq.bk0(m, bk), rw, hs, he, [], qk, T.CInl{[], ps, he} <> sk, un, lf, ab)}),
          M11.ap.ws(w1,
        String.append(w2, SCon{'}', rest}), T.LInl{}, aq.bk0(m, bk), rw, hs, he, [], qk, T.CInl{[], ps, he} <> sk, un,
          lf, ab, {==}, h1)) : {D3.own(_) == G : T.Doc}
  %Equal.sym(T.Doc, T.doc.read(String.append(w2, SCon{'}', rest}), T.MScan{M11.ap.s(T.LInl{}, aq.bk0(m, bk), rw, hs, he,
    [], qk, T.CInl{[], ps, he} <> sk, un, lf, ab)}), T.doc.read(SCon{'}', rest}, T.MScan{M11.ap.s(T.LInl{}, aq.bk0(m,
        bk),
      rw, hs, he, [], qk, T.CInl{[], ps, he} <> sk, un, lf, ab)}), M11.ap.ws(w2, SCon{'}', rest}, T.LInl{}, aq.bk0(m,
          bk),
        rw, hs, he, [], qk, T.CInl{[], ps, he} <> sk, un, lf, ab, {==}, h2)) : {D3.own(_) == G : T.Doc}
  %Equal.sym(T.Mode, T.doc.scan(M11.ap.s(aq.ilx(False{}), aq.bk0(m, bk), rw, hs, he, [], qk, T.CInl{[], ps, he} <> sk,
      un,
    lf, ab), '}'), T.MScan{T.take.top(sk, T.VInl{T.inl.seal([])}, "", rw, hs, he, ps, aq.bk0(m, bk), qk, un, lf, ab,
      False{})}, aq.iclose(False{}, rw, hs, he, [], [], ps, he, aq.bk0(m, bk), qk, sk, un, lf,
        ab)) : {D3.own(T.doc.read(rest, _)) == G : T.Doc}
  kk(T.VInl{T.inl.seal([])}, aq.bk0(m, bk), qk, un, lf, {==}, {==})

# `}` after an inline table's keyvals: the table of its rows sealed is
# placed
def aq.inlk2(
  +inl: List<&2, T.Val>,
  +ri: List<&2, T.Val>,
  +b2: T.Lex,
  +q2: T.QKind,
  +u2: U32,
  +l2: U32,
  +w2: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  +G: T.Doc,
  +h2: {D2.abnf.ws(w2) == True{} : Bool},
  +hi: {D3.own.rows(inl) == ri : List<&2, T.Val>},
  kk: aq.VKG(D5.RaVal{T.VInl{T.inl.seal(ri)}, ""}, rw, hs, he, ps, sk, ab, rest, G)
) -> {D3.own(T.doc.read(String.append(w2, SCon{'}', rest}), T.MScan{M11.ap.s(T.LInlC{}, b2, rw, hs, he, [], q2,
  T.CInl{inl, ps, he} <> sk, u2, l2, ab)})) == G : T.Doc}:
  %Equal.sym(T.Doc, T.doc.read(String.append(w2, SCon{'}', rest}), T.MScan{M11.ap.s(T.LInlC{}, b2, rw, hs, he, [], q2,
    T.CInl{inl, ps, he} <> sk, u2, l2, ab)}), T.doc.read(SCon{'}', rest}, T.MScan{M11.ap.s(T.LInlC{}, b2, rw, hs, he,
        [],
      q2, T.CInl{inl, ps, he} <> sk, u2, l2, ab)}), M11.ap.ws(w2, SCon{'}', rest}, T.LInlC{}, b2, rw, hs, he, [], q2,
        T.CInl{inl, ps, he} <> sk, u2, l2, ab, {==}, h2)) : {D3.own(_) == G : T.Doc}
  %Equal.sym(T.Mode, T.doc.scan(M11.ap.s(aq.ilx(True{}), b2, rw, hs, he, [], q2, T.CInl{inl, ps, he} <> sk, u2, l2, ab),
    '}'), T.MScan{T.take.top(sk, T.VInl{T.inl.seal(inl)}, "", rw, hs, he, ps, b2, q2, u2, l2, ab, False{})},
      aq.iclose(True{}, rw, hs, he, [], inl, ps, he, b2, q2, sk, u2, l2, ab)) : {D3.own(T.doc.read(rest,
        _)) == G : T.Doc}
  +hv = {Equal.cong(List<&2, T.Val>, T.Val, zs => T.VInl{zs}, D3.own.rows(T.inl.seal(inl)), T.inl.seal(ri),
    Equal.trans(List<&2, T.Val>, D3.own.rows(T.inl.seal(inl)), T.inl.seal(D3.own.rows(inl)), T.inl.seal(ri),
      aq.oinl(inl), Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => T.inl.seal(zs), D3.own.rows(inl), ri,
        hi))) : {T.VInl{D3.own.rows(T.inl.seal(inl))} == T.VInl{T.inl.seal(ri)} : T.Val}}
  kk(T.VInl{T.inl.seal(inl)}, b2, q2, u2, l2, hv, hv)

# an inline table's keyvals read: blank space and `}` close it, by the
# replay's reading of the keyvals
def aq.inlk(
  +rr: D5.RpAcc,
  +w2: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  +G: T.Doc,
  +h2: {D2.abnf.ws(w2) == True{} : Bool},
  kk: aq.VKG(D5.replay.inl(rr), rw, hs, he, ps, sk, ab, rest, G)
) -> aq.rk(rr, rw, hs, he, ps, sk, ab, String.append(w2, SCon{'}', rest}), dd => {D3.own(dd) == G : T.Doc}):
  match rr:
    case D5.RaRows{+ri, +bd}:
      match bd:
        case SNil{}:
          +inl => +b2 => +q2 => +u2 => +l2 => +hi => aq.inlk2(inl, ri, b2, q2, u2, l2, w2, rw, hs, he, ps, sk, ab,
            rest, G, h2, hi, kk)
        case SCon{_c0, _cs}:
          kk
    case D5.RaVal{_v, _b}:
      Unit{}
    case D5.RaItems{_i, _b}:
      Unit{}

# an inline table with keyvals
def aq.v.inl(
  +w1: String,
  +kvs: D6.GVal,
  +w2: String,
  +m: Bool,
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
  +G: T.Doc,
  +h1: {D2.abnf.ws(w1) == True{} : Bool},
  +okk: {D1.g.ok.val(kvs, D1.RInlineTableKeyvals{}) == True{} : Bool},
  +h2: {D2.abnf.ws(w2) == True{} : Bool},
  +es: {D3.short(D6.g.val.text(D6.GvInlineTable{w1, kvs, w2}, rest)) == True{} : Bool},
  kk: aq.VKG(D5.replay.inl(D5.replay.go(kvs, D5.RaRows{[], ""})), rw, hs, he, ps, sk, ab, rest, G),
  ih: aq.KT(kvs)
) -> {D3.own(T.doc.read(SCon{'{', String.append(w1, D6.g.val.text(kvs, String.append(w2, SCon{'}', rest})))},
  T.MScan{aq.vst(m, rw, hs, he, ps, bk, qk, sk, un, lf, ab)})) == G : T.Doc}:
  %Equal.sym(T.Mode, T.doc.scan(aq.vst(m, rw, hs, he, ps, bk, qk, sk, un, lf, ab), '{'), T.MScan{M11.ap.s(T.LInl{},
    aq.bk0(m, bk), rw, hs, he, [], qk, T.CInl{[], ps, he} <> sk, un, lf, ab)}, aq.iopen(m, rw, hs, he, ps, bk, qk, sk,
      un, lf, ab)) : {D3.own(T.doc.read(String.append(w1, D6.g.val.text(kvs, String.append(w2, SCon{'}', rest}))),
        _)) == G : T.Doc}
  %Equal.sym(T.Doc, T.doc.read(String.append(w1, D6.g.val.text(kvs, String.append(w2, SCon{'}', rest}))),
    T.MScan{M11.ap.s(T.LInl{}, aq.bk0(m, bk), rw, hs, he, [], qk, T.CInl{[], ps, he} <> sk, un, lf, ab)}),
      T.doc.read(D6.g.val.text(kvs, String.append(w2, SCon{'}', rest})), T.MScan{M11.ap.s(T.LInl{}, aq.bk0(m, bk), rw,
        hs, he, [], qk, T.CInl{[], ps, he} <> sk, un, lf, ab)}), M11.ap.ws(w1, D6.g.val.text(kvs, String.append(w2,
          SCon{'}', rest})), T.LInl{}, aq.bk0(m, bk), rw, hs, he, [], qk, T.CInl{[], ps, he} <> sk, un, lf, ab, {==},
            h1)) : {D3.own(_) == G : T.Doc}
  ih(False{}, rw, hs, he, ps, sk, [], [], aq.bk0(m, bk), qk, un, lf, ab, String.append(w2, SCon{'}', rest}), G,
    aq.kvok.i(kvs, okk), aq.sh(w1, D6.g.val.text(kvs, String.append(w2, SCon{'}', rest})), M23.gd.short.tail('{',
      String.append(w1, D6.g.val.text(kvs, String.append(w2, SCon{'}', rest}))), es)), aq.fol.ws(w2, SCon{'}',
        rest}, h2, {==}), {==}, aq.inlk(D5.replay.go(kvs, D5.RaRows{[], ""}), w2, rw, hs, he, ps, sk, ab, rest, G,
          h2, kk))

# an array's item read: ws-comment-newline, a comma and the next items, by
# the replay's reading of the item
def aq.itemk(
  +rr: D5.RpAcc,
  +wb: List<&2, D6.GWcn>,
  +rv: D6.GVal,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +at: List<&2, String>,
  +p: List<&2, String>,
  +sv: List<&2, String>,
  +sk0: List<&2, T.Ctx>,
  +its: List<&2, T.Val>,
  +ri: List<&2, T.Val>,
  +ab: Bool,
  +rest: String,
  +G: T.Doc,
  +hwb: {D1.g.ok.wcn(wb) == True{} : Bool},
  +hrv: {D1.g.ok.val(rv, D1.RArrayValues{}) == True{} : Bool},
  +er: {D3.short(D6.g.val.text(rv, rest)) == True{} : Bool},
  +hf: {aq.fol(rest) == True{} : Bool},
  +hi: {D3.own.rows(its) == ri : List<&2, T.Val>},
  kk: aq.IKG(D5.replay.go(rv, D5.replay.item(rr, D5.RaItems{ri, ""})), rw, hs, at, sv, sk0, ab, rest, G),
  ihr: aq.IT(rv)
) -> aq.vk(rr, rw, hs, at, p, T.CArr{its, sv, at} <> sk0, ab, D6.g.wcn.text(wb, SCon{',', D6.g.val.text(rv,
  rest)}), dd => {D3.own(dd) == G : T.Doc}):
  match rr:
    case D5.RaVal{+vv, +bd}:
      match bd:
        case SNil{}:
          +xv => +b2 => +q2 => +u2 => +l2 => _hv => +hc =>
            aq.wcn(wb, SCon{',', D6.g.val.text(rv, rest)}, T.LArrC{}, b2, rw, hs, at, sv, q2, T.CArr{xv <> its, sv,
              at} <> sk0, u2, l2, ab, {==}, {==}, {==}, hwb, dd => {D3.own(dd) == G : T.Doc}, +b3 => ihr(rw, hs, at,
                sv, sv, sk0, xv <> its, vv <> ri, b3, q2, u2, l2, ab, rest, G, hrv, er, hf, aq.cons2(xv, its, vv, ri,
                  hc, hi), kk))
        case SCon{+c0, +cs}:
          aq.ike(rv, vv <> ri, c0, cs, rw, hs, at, sv, sk0, ab, rest, dd => {D3.own(dd) == G : T.Doc}, hrv, kk)
    case D5.RaItems{_i, _b}:
      Unit{}
    case D5.RaRows{_r, _b}:
      Unit{}

# an array's items: blank space, comments and newlines, a value, more, a
# comma and the items after it
def aq.i.av(
  +wa: List<&2, D6.GWcn>,
  +val: D6.GVal,
  +wb: List<&2, D6.GWcn>,
  +rv: D6.GVal,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +at: List<&2, String>,
  +p: List<&2, String>,
  +sv: List<&2, String>,
  +sk0: List<&2, T.Ctx>,
  +its: List<&2, T.Val>,
  +ri: List<&2, T.Val>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  +G: T.Doc,
  +ok: {D1.g.ok.val(D6.GArrayValues{wa, val, wb, rv}, D1.RArrayValues{}) == True{} : Bool},
  +es: {D3.short(D6.g.val.text(D6.GArrayValues{wa, val, wb, rv}, rest)) == True{} : Bool},
  +hf: {aq.fol(rest) == True{} : Bool},
  +hi: {D3.own.rows(its) == ri : List<&2, T.Val>},
  kk: aq.IKN(D6.GArrayValues{wa, val, wb, rv}, ri, rw, hs, at, sv, sk0, ab, rest, G),
  ihv: aq.VT(val),
  ihr: aq.IT(rv)
) -> {D3.own(T.doc.read(D6.g.val.text(D6.GArrayValues{wa, val, wb, rv}, rest), T.MScan{M11.ap.s(T.LArr{}, bk, rw,
  hs, at, p, qk, T.CArr{its, sv, at} <> sk0, un, lf, ab)})) == G : T.Doc}:
  +h2 = {Eq.and.right(D1.g.ok.wcn(wa), Bool.and(D1.g.ok.val(val, D1.RVal{}), Bool.and(D1.g.ok.wcn(wb),
    D1.g.ok.val(rv, D1.RArrayValues{}))), ok) : {Bool.and(D1.g.ok.val(val, D1.RVal{}),
      Bool.and(D1.g.ok.wcn(wb), D1.g.ok.val(rv, D1.RArrayValues{}))) == True{} : Bool}}
  +h3 = {Eq.and.right(D1.g.ok.val(val, D1.RVal{}), Bool.and(D1.g.ok.wcn(wb), D1.g.ok.val(rv,
    D1.RArrayValues{})), h2) : {Bool.and(D1.g.ok.wcn(wb), D1.g.ok.val(rv, D1.RArrayValues{})) == True{} : Bool}}
  +hv0 = {Eq.and.left(D1.g.ok.val(val, D1.RVal{}), Bool.and(D1.g.ok.wcn(wb), D1.g.ok.val(rv,
    D1.RArrayValues{})), h2) : {D1.g.ok.val(val, D1.RVal{}) == True{} : Bool}}
  +hwb = {Eq.and.left(D1.g.ok.wcn(wb), D1.g.ok.val(rv, D1.RArrayValues{}),
    h3) : {D1.g.ok.wcn(wb) == True{} : Bool}}
  +e1 = {aq.sh.wcn(wa, D6.g.val.text(val, D6.g.wcn.text(wb, SCon{',', D6.g.val.text(rv, rest)})),
    es) : {D3.short(D6.g.val.text(val, D6.g.wcn.text(wb, SCon{',', D6.g.val.text(rv,
      rest)}))) == True{} : Bool}}
  +e4 = {M23.gd.short.tail(',', D6.g.val.text(rv, rest), aq.sh.wcn(wb, SCon{',', D6.g.val.text(rv, rest)},
    aq.sh.val(val, D6.g.wcn.text(wb, SCon{',', D6.g.val.text(rv, rest)}), e1))) : {D3.short(D6.g.val.text(rv,
      rest)) == True{} : Bool}}
  aq.wcn(wa, D6.g.val.text(val, D6.g.wcn.text(wb, SCon{',', D6.g.val.text(rv, rest)})), T.LArr{}, bk, rw, hs,
    at, p, qk, T.CArr{its, sv, at} <> sk0, un, lf, ab, {==}, {==}, {==}, Eq.and.left(D1.g.ok.wcn(wa),
      Bool.and(D1.g.ok.val(val, D1.RVal{}), Bool.and(D1.g.ok.wcn(wb), D1.g.ok.val(rv, D1.RArrayValues{}))),
        ok), dd => {D3.own(dd) == G : T.Doc}, +b2 => ihv(True{}, rw, hs, at, p, b2, qk, T.CArr{its, sv, at} <> sk0,
          un, lf, ab, D6.g.wcn.text(wb, SCon{',', D6.g.val.text(rv, rest)}), G, hv0, e1, aq.fol.wcn(wb, SCon{',',
            D6.g.val.text(rv, rest)}, hwb, {==}), aq.itemk(D5.replay.go(val, D5.RaVal{T.VArr{[]}, ""}), wb, rv,
              rw, hs, at, p, sv, sk0, its, ri, ab, rest, G, hwb, Eq.and.right(D1.g.ok.wcn(wb), D1.g.ok.val(rv,
                D1.RArrayValues{}), h3), e4, hf, hi, aq.ikt(D5.replay.go(rv, D5.replay.item(D5.replay.go(val,
                  D5.RaItems{ri, ""}), D5.RaItems{ri, ""})), D5.replay.go(rv,
                    D5.replay.item(D5.replay.go(val, D5.RaVal{T.VArr{[]}, ""}), D5.RaItems{ri, ""})),
                      Equal.cong(D5.RpAcc, D5.RpAcc, aa => D5.replay.go(rv, D5.replay.item(aa,
                        D5.RaItems{ri, ""})), D5.replay.go(val, D5.RaItems{ri, ""}), D5.replay.go(val,
                          D5.RaVal{T.VArr{[]}, ""}), aq.goval(val, D5.RaItems{ri, ""}, hv0)), rw, hs, at, sv, sk0,
                            ab, rest, dd => {D3.own(dd) == G : T.Doc}, kk), ihr)))

# after the last item: a comma or none, with what the continuation takes
def aq.sepk(
  +sep: Bool,
  +its: List<&2, T.Val>,
  +ri: List<&2, T.Val>,
  +b3: T.Lex,
  +q2: T.QKind,
  +u2: U32,
  +l2: U32,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +at: List<&2, String>,
  +sv: List<&2, String>,
  +sk0: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  +G: T.Doc,
  +hi: {D3.own.rows(its) == ri : List<&2, T.Val>},
  kk: aq.ik2("", ri, rw, hs, at, sv, sk0, ab, rest, dd => {D3.own(dd) == G : T.Doc})
) -> {D3.own(T.doc.read(D6.g.sep.text(sep, rest), T.MScan{M11.ap.s(T.LArrC{}, b3, rw, hs, at, sv, q2, T.CArr{its, sv,
  at} <> sk0, u2, l2, ab)})) == G : T.Doc}:
  match sep:
    case True{}:
      kk(its, True{}, b3, q2, u2, l2, hi)
    case False{}:
      kk(its, False{}, b3, q2, u2, l2, hi)

# the last item read: ws-comment-newline and the separator, by the replay's
# reading of the item
def aq.itemkl(
  +rr: D5.RpAcc,
  +wb: List<&2, D6.GWcn>,
  +sep: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +at: List<&2, String>,
  +p: List<&2, String>,
  +sv: List<&2, String>,
  +sk0: List<&2, T.Ctx>,
  +its: List<&2, T.Val>,
  +ri: List<&2, T.Val>,
  +ab: Bool,
  +rest: String,
  +G: T.Doc,
  +hwb: {D1.g.ok.wcn(wb) == True{} : Bool},
  +hi: {D3.own.rows(its) == ri : List<&2, T.Val>},
  kk: aq.IKG(D5.replay.item(rr, D5.RaItems{ri, ""}), rw, hs, at, sv, sk0, ab, rest, G)
) -> aq.vk(rr, rw, hs, at, p, T.CArr{its, sv, at} <> sk0, ab, D6.g.wcn.text(wb, D6.g.sep.text(sep, rest)), dd =>
  {D3.own(dd) == G : T.Doc}):
  match rr:
    case D5.RaVal{+vv, +bd}:
      match bd:
        case SNil{}:
          +xv => +b2 => +q2 => +u2 => +l2 => _hv => +hc =>
            aq.wcn(wb, D6.g.sep.text(sep, rest), T.LArrC{}, b2, rw, hs, at, sv, q2, T.CArr{xv <> its, sv,
              at} <> sk0, u2, l2, ab, {==}, {==}, {==}, hwb, dd => {D3.own(dd) == G : T.Doc}, +b3 => aq.sepk(sep,
                xv <> its, vv <> ri, b3, q2, u2, l2, rw, hs, at, sv, sk0, ab, rest, G, aq.cons2(xv, its, vv, ri, hc,
                  hi), kk))
        case SCon{_c0, _cs}:
          kk
    case D5.RaItems{_i, _b}:
      Unit{}
    case D5.RaRows{_r, _b}:
      Unit{}

# an array's last item: blank space, comments and newlines, a value, more,
# and a comma or none
def aq.i.avl(
  +wa: List<&2, D6.GWcn>,
  +val: D6.GVal,
  +wb: List<&2, D6.GWcn>,
  +sep: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +at: List<&2, String>,
  +p: List<&2, String>,
  +sv: List<&2, String>,
  +sk0: List<&2, T.Ctx>,
  +its: List<&2, T.Val>,
  +ri: List<&2, T.Val>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  +G: T.Doc,
  +ok: {D1.g.ok.val(D6.GArrayValuesLast{wa, val, wb, sep}, D1.RArrayValues{}) == True{} : Bool},
  +es: {D3.short(D6.g.val.text(D6.GArrayValuesLast{wa, val, wb, sep}, rest)) == True{} : Bool},
  +hf: {aq.fol(rest) == True{} : Bool},
  +hi: {D3.own.rows(its) == ri : List<&2, T.Val>},
  kk: aq.IKN(D6.GArrayValuesLast{wa, val, wb, sep}, ri, rw, hs, at, sv, sk0, ab, rest, G),
  ihv: aq.VT(val)
) -> {D3.own(T.doc.read(D6.g.val.text(D6.GArrayValuesLast{wa, val, wb, sep}, rest), T.MScan{M11.ap.s(T.LArr{}, bk,
  rw, hs, at, p, qk, T.CArr{its, sv, at} <> sk0, un, lf, ab)})) == G : T.Doc}:
  +h2 = {Eq.and.right(D1.g.ok.wcn(wa), Bool.and(D1.g.ok.val(val, D1.RVal{}), D1.g.ok.wcn(wb)),
    ok) : {Bool.and(D1.g.ok.val(val, D1.RVal{}), D1.g.ok.wcn(wb)) == True{} : Bool}}
  +hv0 = {Eq.and.left(D1.g.ok.val(val, D1.RVal{}), D1.g.ok.wcn(wb), h2) : {D1.g.ok.val(val,
    D1.RVal{}) == True{} : Bool}}
  +hwb = {Eq.and.right(D1.g.ok.val(val, D1.RVal{}), D1.g.ok.wcn(wb), h2) : {D1.g.ok.wcn(wb) == True{} : Bool}}
  aq.wcn(wa, D6.g.val.text(val, D6.g.wcn.text(wb, D6.g.sep.text(sep, rest))), T.LArr{}, bk, rw, hs, at, p, qk,
    T.CArr{its, sv, at} <> sk0, un, lf, ab, {==}, {==}, {==}, Eq.and.left(D1.g.ok.wcn(wa),
      Bool.and(D1.g.ok.val(val, D1.RVal{}), D1.g.ok.wcn(wb)), ok), dd => {D3.own(dd) == G : T.Doc}, +b2 =>
        ihv(True{}, rw, hs, at, p, b2, qk, T.CArr{its, sv, at} <> sk0, un, lf, ab, D6.g.wcn.text(wb,
          D6.g.sep.text(sep, rest)), G, hv0, aq.sh.wcn(wa, D6.g.val.text(val, D6.g.wcn.text(wb,
            D6.g.sep.text(sep, rest))), es), aq.fol.wcn(wb, D6.g.sep.text(sep, rest), hwb, aq.fol.sep(sep, rest,
              hf)), aq.itemkl(D5.replay.go(val, D5.RaVal{T.VArr{[]}, ""}), wb, sep, rw, hs, at, p, sv, sk0, its,
                ri, ab, rest, G, hwb, hi, aq.ikt(D5.replay.item(D5.replay.go(val, D5.RaItems{ri, ""}),
                  D5.RaItems{ri, ""}), D5.replay.item(D5.replay.go(val, D5.RaVal{T.VArr{[]}, ""}),
                    D5.RaItems{ri, ""}), Equal.cong(D5.RpAcc, D5.RpAcc, aa => D5.replay.item(aa,
                      D5.RaItems{ri, ""}), D5.replay.go(val, D5.RaItems{ri, ""}), D5.replay.go(val,
                        D5.RaVal{T.VArr{[]}, ""}), aq.goval(val, D5.RaItems{ri, ""}, hv0)), rw, hs, at, sv, sk0,
                          ab, rest, dd => {D3.own(dd) == G : T.Doc}, kk))))

# the walk of an inline table's keyval, however it ends: the rest read from
# where the table waits after a keyval, or the error it sets stays
def aq.ikw(
  en: T.End,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +at: List<&2, String>,
  +sv: List<&2, String>,
  +sk0: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  +G: T.Doc,
  +b2: T.Lex,
  +q2: T.QKind,
  +u2: U32,
  +l2: U32,
  kk: aq.RKG(D5.replay.end.rows(ow.end(en)), rw, hs, at, sv, sk0, ab, rest, G)
) -> {D3.own(T.doc.read(rest, T.MScan{T.take.inl(en, rw, hs, at, sv, sk0, b2, q2, u2, l2, ab,
  False{})})) == G : T.Doc}:
  match en:
    case T.End{+inl2, +bad2, _h2}:
      match bad2:
        case SNil{}:
          kk(inl2, b2, q2, u2, l2, {==})
        case SCon{+c0, +cs}:
          %Equal.sym(T.Doc, T.doc.read(rest, T.MScan{T.St{SCon{c0, cs}, rw, hs, at, [], [], T.LInlC{}, b2, q2,
            T.CInl{inl2, sv, at} <> sk0, T.HNone{}, u2, l2, ab, False{}}}), T.Doc{SCon{c0, cs}, T.rows.seal(rw)},
              L5.error_stays(SCon{c0, cs}, rw, hs, at, [], [], T.LInlC{}, b2, q2, T.CInl{inl2, sv, at} <> sk0,
                T.HNone{}, u2, l2, ab, False{}, {==}, rest)) : {D3.own(_) == G : T.Doc}
          kk

# a keyval's walk into an inline table's rows is the replay's, read out
def aq.e1(
  +names: List<&2, String>,
  +racc: List<&2, String>,
  +ri: List<&2, T.Val>,
  +oinl: List<&2, T.Val>,
  +vv: T.Val,
  +ovx: T.Val,
  +hp: {racc == names : List<&2, String>},
  +hi: {oinl == ri : List<&2, T.Val>},
  +hv: {ovx == vv : T.Val}
) -> {T.tree.walk(names, T.Tw{ri, T.JPut{vv}, [], "", "", [], True{}}, 0) == T.tree.walk(racc, T.Tw{oinl, T.JPut{ovx},
  [], "", "", [], True{}}, 0) : T.End}:
  %hp : {T.tree.walk(_, T.Tw{ri, T.JPut{vv}, [], "", "", [], True{}}, 0) == T.tree.walk(racc, T.Tw{oinl, T.JPut{ovx},
    [], "", "", [], True{}}, 0) : T.End}
  %hi : {T.tree.walk(racc, T.Tw{_, T.JPut{vv}, [], "", "", [], True{}}, 0) == T.tree.walk(racc, T.Tw{oinl,
    T.JPut{ovx}, [], "", "", [], True{}}, 0) : T.End}
  %hv : {T.tree.walk(racc, T.Tw{oinl, T.JPut{_}, [], "", "", [], True{}}, 0) == T.tree.walk(racc, T.Tw{oinl,
    T.JPut{ovx}, [], "", "", [], True{}}, 0) : T.End}
  {==}

# an inline table's keyval's value read: it is walked into the table's rows
# along the key's names, by the replay's reading of the value
def aq.ikv(
  +rr: D5.RpAcc,
  +names: List<&2, String>,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +at: List<&2, String>,
  +sv: List<&2, String>,
  +sk0: List<&2, T.Ctx>,
  +inl: List<&2, T.Val>,
  +ri: List<&2, T.Val>,
  +acc: List<&2, String>,
  +ab: Bool,
  +rest: String,
  +G: T.Doc,
  +hp: {List.reverse(&2, String, acc) == names : List<&2, String>},
  +hi: {D3.own.rows(inl) == ri : List<&2, T.Val>},
  kk: aq.RKG(D5.replay.kv(names, rr, D5.RaRows{ri, ""}), rw, hs, at, sv, sk0, ab, rest, G)
) -> aq.vk(rr, rw, hs, at, acc, T.CInl{inl, sv, at} <> sk0, ab, rest, dd => {D3.own(dd) == G : T.Doc}):
  match rr:
    case D5.RaVal{+vv, +bd}:
      match bd:
        case SNil{}:
          +xv => +b2 => +q2 => +u2 => +l2 => +hv => _hc =>
            aq.ikw(T.tree.walk(List.reverse(&2, String, acc), T.Tw{inl, T.JPut{xv}, [], "", "", [], True{}}, 0), rw,
              hs, at, sv, sk0, ab, rest, G, b2, q2, u2, l2, aq.rkt(D5.replay.end.rows(T.tree.walk(names, T.Tw{ri,
                T.JPut{vv}, [], "", "", [], True{}}, 0)), D5.replay.end.rows(ow.end(T.tree.walk(List.reverse(&2,
                  String, acc), T.Tw{inl, T.JPut{xv}, [], "", "", [], True{}}, 0))), Equal.cong(T.End, D5.RpAcc,
                    en => D5.replay.end.rows(en), T.tree.walk(names, T.Tw{ri, T.JPut{vv}, [], "", "", [], True{}},
                      0), ow.end(T.tree.walk(List.reverse(&2, String, acc), T.Tw{inl, T.JPut{xv}, [], "", "", [],
                        True{}}, 0)), Equal.trans(T.End, T.tree.walk(names, T.Tw{ri, T.JPut{vv}, [], "", "", [],
                          True{}}, 0), T.tree.walk(List.reverse(&2, String, acc), T.Tw{D3.own.rows(inl),
                            T.JPut{ow.v(xv)}, [], "", "", [], True{}}, 0), ow.end(T.tree.walk(List.reverse(&2, String,
                              acc), T.Tw{inl, T.JPut{xv}, [], "", "", [], True{}}, 0)), aq.e1(names, List.reverse(&2,
                                String, acc), ri, D3.own.rows(inl), vv, ow.v(xv), hp, hi, hv), Equal.sym(T.End,
                                  ow.end(T.tree.walk(List.reverse(&2, String, acc), T.Tw{inl, T.JPut{xv}, [], "", "",
                                    [], True{}}, 0)), T.tree.walk(List.reverse(&2, String, acc),
                                      T.Tw{D3.own.rows(inl), T.JPut{ow.v(xv)}, [], "", "", [], True{}}, 0),
                                        ow.walk(List.reverse(&2, String, acc), T.Tw{inl, T.JPut{xv}, [], "", "", [],
                                          True{}}, 0)))), rw, hs, at, sv, sk0, ab, rest, dd =>
                                            {D3.own(dd) == G : T.Doc}, kk))
        case SCon{+c0, +cs}:
          aq.rkt(D5.replay.end.rows(T.tree.walk(names, T.Tw{ri, T.JPut{vv}, [], SCon{c0, cs}, "", [], True{}}, 0)),
            D5.RaRows{ri, SCon{c0, cs}}, Equal.cong(T.End, D5.RpAcc, en => D5.replay.end.rows(en),
              T.tree.walk(names, T.Tw{ri, T.JPut{vv}, [], SCon{c0, cs}, "", [], True{}}, 0), T.End{ri, SCon{c0, cs},
                []}, L4.failed_walk_changes_nothing(names, ri, T.JPut{vv}, SCon{c0, cs}, "", [], True{}, 0, {==})),
                  rw, hs, at, sv, sk0, ab, rest, dd => {D3.own(dd) == G : T.Doc}, kk)
    case D5.RaItems{_i, _b}:
      Unit{}
    case D5.RaRows{_r, _b}:
      Unit{}

# a keyval of an inline table: its key from where the table waits for one,
# `=`, its value, and its walk into the table's rows
def aq.k.kv(
  +key: D6.GKey,
  +wa: String,
  +wb: String,
  +val: D6.GVal,
  +pos: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +at: List<&2, String>,
  +sv: List<&2, String>,
  +sk0: List<&2, T.Ctx>,
  +inl: List<&2, T.Val>,
  +ri: List<&2, T.Val>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  +G: T.Doc,
  +ok: {aq.kvok(D6.GKeyval{key, wa, wb, val}) == True{} : Bool},
  +es: {D3.short(D6.g.val.text(D6.GKeyval{key, wa, wb, val}, rest)) == True{} : Bool},
  +hf: {aq.fol(rest) == True{} : Bool},
  +hi: {D3.own.rows(inl) == ri : List<&2, T.Val>},
  kk: aq.RKG(D5.replay.go(D6.GKeyval{key, wa, wb, val}, D5.RaRows{ri, ""}), rw, hs, at, sv, sk0, ab, rest, G),
  ihv: aq.VT(val)
) -> {D3.own(T.doc.read(D6.g.val.text(D6.GKeyval{key, wa, wb, val}, rest),
  T.MScan{M11.ap.s(L9.k3.pos.lex(aq.kpos(pos)), bk, rw, hs, at, [], qk, T.CInl{inl, sv, at} <> sk0, un, lf,
    ab)})) == G : T.Doc}:
  +ha2 = {Eq.and.right(D1.g.ok.key(key), Bool.and(D2.abnf.ws(wa), Bool.and(D2.abnf.ws(wb), D1.g.ok.val(val,
    D1.RVal{}))), ok) : {Bool.and(D2.abnf.ws(wa), Bool.and(D2.abnf.ws(wb), D1.g.ok.val(val,
      D1.RVal{}))) == True{} : Bool}}
  +ha3 = {Eq.and.right(D2.abnf.ws(wa), Bool.and(D2.abnf.ws(wb), D1.g.ok.val(val, D1.RVal{})),
    ha2) : {Bool.and(D2.abnf.ws(wb), D1.g.ok.val(val, D1.RVal{})) == True{} : Bool}}
  +hk = {Eq.and.left(D1.g.ok.key(key), Bool.and(D2.abnf.ws(wa), Bool.and(D2.abnf.ws(wb), D1.g.ok.val(val,
    D1.RVal{}))), ok) : {D1.g.ok.key(key) == True{} : Bool}}
  +hv0 = {Eq.and.right(D2.abnf.ws(wb), D1.g.ok.val(val, D1.RVal{}), ha3) : {D1.g.ok.val(val,
    D1.RVal{}) == True{} : Bool}}
  +s2 = {aq.sh(D6.g.key.text(key, ""), String.append(wa, SCon{'=', String.append(wb, D6.g.val.text(val, rest))}),
    aq.shq(D6.g.key.text(key, String.append(wa, SCon{'=', String.append(wb, D6.g.val.text(val, rest))})),
      String.append(D6.g.key.text(key, ""), String.append(wa, SCon{'=', String.append(wb, D6.g.val.text(val,
        rest))})), M15.gt.key(key, String.append(wa, SCon{'=', String.append(wb, D6.g.val.text(val, rest))})),
          es)) : {D3.short(String.append(wa, SCon{'=', String.append(wb, D6.g.val.text(val,
            rest))})) == True{} : Bool}}
  +s5 = {aq.sh(wb, D6.g.val.text(val, rest), M23.gd.short.tail('=', String.append(wb, D6.g.val.text(val, rest)),
    aq.sh(wa, SCon{'=', String.append(wb, D6.g.val.text(val, rest))}, s2))) : {D3.short(D6.g.val.text(val,
      rest)) == True{} : Bool}}
  %Equal.sym(String, D6.g.key.text(key, String.append(wa, SCon{'=', String.append(wb, D6.g.val.text(val,
    rest))})), L9.k3.dk.text(M11.ap.kds(key), M11.ap.klast(key), String.append(wa, SCon{'=', String.append(wb,
      D6.g.val.text(val, rest))})), M11.ap.key.text(key, String.append(wa, SCon{'=', String.append(wb,
        D6.g.val.text(val, rest))}), hk)) : {D3.own(T.doc.read(_, T.MScan{M11.ap.s(L9.k3.pos.lex(aq.kpos(pos)), bk,
          rw, hs, at, [], qk, T.CInl{inl, sv, at} <> sk0, un, lf, ab)})) == G : T.Doc}
  %M11.ap.gap(wa, Eq.and.left(D2.abnf.ws(wa), Bool.and(D2.abnf.ws(wb), D1.g.ok.val(val, D1.RVal{})),
    ha2)) : {D3.own(T.doc.read(L9.k3.dk.text(M11.ap.kds(key), M11.ap.klast(key), String.append(_, SCon{'=',
      String.append(wb, D6.g.val.text(val, rest))})), T.MScan{M11.ap.s(L9.k3.pos.lex(aq.kpos(pos)), bk, rw, hs, at,
        [], qk, T.CInl{inl, sv, at} <> sk0, un, lf, ab)})) == G : T.Doc}
  kx.keys(M11.ap.kds(key), M11.ap.klast(key), M11.ap.gs(wa), False{}, aq.kpos(pos), rw, hs, at, [], bk, qk, T.CInl{inl,
      sv,
    at} <> sk0, un, lf, ab, String.append(wb, D6.g.val.text(val, rest)), dd => {D3.own(dd) == G : T.Doc},
      M11.ap.key.ok(key, hk), +b2 => +q2 => +u2 => +l2 =>
    %Equal.sym(T.Doc, T.doc.read(String.append(wb, D6.g.val.text(val, rest)), T.MScan{M11.ap.s(T.LVal{}, b2, rw, hs, at,
      M16.k3.acc(M11.ap.kds(key), M11.ap.klast(key), False{}, []), q2, T.CInl{inl, sv, at} <> sk0, u2, l2, ab)}),
        T.doc.read(D6.g.val.text(val, rest), T.MScan{M11.ap.s(T.LVal{}, b2, rw, hs, at, M16.k3.acc(M11.ap.kds(key),
          M11.ap.klast(key), False{}, []), q2, T.CInl{inl, sv, at} <> sk0, u2, l2, ab)}), M11.ap.ws(wb,
              D6.g.val.text(val,
            rest), T.LVal{}, b2, rw, hs, at, M16.k3.acc(M11.ap.kds(key), M11.ap.klast(key), False{}, []), q2,
                T.CInl{inl, sv,
              at} <> sk0, u2, l2, ab, {==}, Eq.and.left(D2.abnf.ws(wb), D1.g.ok.val(val, D1.RVal{}),
                ha3))) : {D3.own(_) == G : T.Doc}
    ihv(False{}, rw, hs, at, M16.k3.acc(M11.ap.kds(key), M11.ap.klast(key), False{}, []), b2, q2, T.CInl{inl, sv,
        at} <> sk0, u2,
      l2, ab, rest, G, hv0, s5, hf, aq.ikv(D5.replay.go(val, D5.RaVal{T.VArr{[]}, ""}), D1.g.key.names(key), rw,
        hs, at, sv, sk0, inl, ri, M16.k3.acc(M11.ap.kds(key), M11.ap.klast(key), False{}, []), ab, rest, G,
            aq.kpath(key), hi,
          aq.rkt(D5.replay.kv(D1.g.key.names(key), D5.replay.go(val, D5.RaRows{ri, ""}), D5.RaRows{ri, ""}),
            D5.replay.kv(D1.g.key.names(key), D5.replay.go(val, D5.RaVal{T.VArr{[]}, ""}), D5.RaRows{ri,
              ""}), Equal.cong(D5.RpAcc, D5.RpAcc, aa => D5.replay.kv(D1.g.key.names(key), aa, D5.RaRows{ri,
                ""}), D5.replay.go(val, D5.RaRows{ri, ""}), D5.replay.go(val, D5.RaVal{T.VArr{[]}, ""}),
                  aq.goval(val, D5.RaRows{ri, ""}, hv0)), rw, hs, at, sv, sk0, ab, rest, dd =>
                    {D3.own(dd) == G : T.Doc}, kk))))

# a keyval read: blank space, a comma, blank space and the keyvals after it,
# by the replay's reading of the keyval
def aq.kvsk(
  +rr: D5.RpAcc,
  +w1: String,
  +w2: String,
  +rv: D6.GVal,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +at: List<&2, String>,
  +sv: List<&2, String>,
  +sk0: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  +G: T.Doc,
  +h1: {D2.abnf.ws(w1) == True{} : Bool},
  +h2: {D2.abnf.ws(w2) == True{} : Bool},
  +hrv: {D1.g.ok.val(rv, D1.RInlineTableKeyvals{}) == True{} : Bool},
  +er: {D3.short(D6.g.val.text(rv, rest)) == True{} : Bool},
  +hf: {aq.fol(rest) == True{} : Bool},
  kk: aq.RKG(D5.replay.go(rv, rr), rw, hs, at, sv, sk0, ab, rest, G),
  ihr: aq.KT(rv)
) -> aq.rk(rr, rw, hs, at, sv, sk0, ab, String.append(w1, SCon{',', String.append(w2, D6.g.val.text(rv, rest))}),
  dd => {D3.own(dd) == G : T.Doc}):
  match rr:
    case D5.RaRows{+ri2, +bd}:
      match bd:
        case SNil{}:
          +inl2 => +b2 => +q2 => +u2 => +l2 => +hi2 =>
            %Equal.sym(T.Doc, T.doc.read(String.append(w1, SCon{',', String.append(w2, D6.g.val.text(rv, rest))}),
              T.MScan{M11.ap.s(T.LInlC{}, b2, rw, hs, at, [], q2, T.CInl{inl2, sv, at} <> sk0, u2, l2, ab)}),
                T.doc.read(SCon{',', String.append(w2, D6.g.val.text(rv, rest))}, T.MScan{M11.ap.s(T.LInlC{}, b2, rw,
                  hs, at, [], q2, T.CInl{inl2, sv, at} <> sk0, u2, l2, ab)}), M11.ap.ws(w1, SCon{',', String.append(w2,
                    D6.g.val.text(rv, rest))}, T.LInlC{}, b2, rw, hs, at, [], q2, T.CInl{inl2, sv, at} <> sk0, u2,
                      l2, ab, {==}, h1)) : {D3.own(_) == G : T.Doc}
            %Equal.sym(T.Doc, T.doc.read(String.append(w2, D6.g.val.text(rv, rest)), T.MScan{M11.ap.s(T.LInlK{}, b2, rw,
              hs, at, [], q2, T.CInl{inl2, sv, at} <> sk0, u2, l2, ab)}), T.doc.read(D6.g.val.text(rv, rest),
                T.MScan{M11.ap.s(T.LInlK{}, b2, rw, hs, at, [], q2, T.CInl{inl2, sv, at} <> sk0, u2, l2, ab)}),
                    M11.ap.ws(w2,
                  D6.g.val.text(rv, rest), T.LInlK{}, b2, rw, hs, at, [], q2, T.CInl{inl2, sv, at} <> sk0, u2, l2,
                    ab, {==}, h2)) : {D3.own(_) == G : T.Doc}
            ihr(True{}, rw, hs, at, sv, sk0, inl2, ri2, b2, q2, u2, l2, ab, rest, G, aq.kvok.i(rv, hrv), er, hf, hi2,
              kk)
        case SCon{+c0, +cs}:
          aq.rke(rv, ri2, c0, cs, rw, hs, at, sv, sk0, ab, rest, dd => {D3.own(dd) == G : T.Doc}, aq.kvok.i(rv,
            hrv), kk)
    case D5.RaVal{_v, _b}:
      Unit{}
    case D5.RaItems{_i, _b}:
      Unit{}

# an inline table's keyvals: a keyval, a comma and the keyvals after it
def aq.k.kvs(
  +kv: D6.GVal,
  +w1: String,
  +w2: String,
  +rv: D6.GVal,
  +pos: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +at: List<&2, String>,
  +sv: List<&2, String>,
  +sk0: List<&2, T.Ctx>,
  +inl: List<&2, T.Val>,
  +ri: List<&2, T.Val>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  +G: T.Doc,
  +ok: {aq.kvok(D6.GInlineTableKeyvals{kv, w1, w2, rv}) == True{} : Bool},
  +es: {D3.short(D6.g.val.text(D6.GInlineTableKeyvals{kv, w1, w2, rv}, rest)) == True{} : Bool},
  +hf: {aq.fol(rest) == True{} : Bool},
  +hi: {D3.own.rows(inl) == ri : List<&2, T.Val>},
  kk: aq.RKN(D6.GInlineTableKeyvals{kv, w1, w2, rv}, ri, rw, hs, at, sv, sk0, ab, rest, G),
  ihk: aq.KT(kv),
  ihr: aq.KT(rv)
) -> {D3.own(T.doc.read(D6.g.val.text(D6.GInlineTableKeyvals{kv, w1, w2, rv}, rest),
  T.MScan{M11.ap.s(L9.k3.pos.lex(aq.kpos(pos)), bk, rw, hs, at, [], qk, T.CInl{inl, sv, at} <> sk0, un, lf,
    ab)})) == G : T.Doc}:
  +h1r = {Eq.and.right(D1.g.ok.val(kv, D1.RKeyval{}), Bool.and(D2.abnf.ws(w1), Bool.and(D2.abnf.ws(w2),
    D1.g.ok.val(rv, D1.RInlineTableKeyvals{}))), ok) : {Bool.and(D2.abnf.ws(w1), Bool.and(D2.abnf.ws(w2),
      D1.g.ok.val(rv, D1.RInlineTableKeyvals{}))) == True{} : Bool}}
  +h2r = {Eq.and.right(D2.abnf.ws(w1), Bool.and(D2.abnf.ws(w2), D1.g.ok.val(rv, D1.RInlineTableKeyvals{})),
    h1r) : {Bool.and(D2.abnf.ws(w2), D1.g.ok.val(rv, D1.RInlineTableKeyvals{})) == True{} : Bool}}
  +h1 = {Eq.and.left(D2.abnf.ws(w1), Bool.and(D2.abnf.ws(w2), D1.g.ok.val(rv, D1.RInlineTableKeyvals{})),
    h1r) : {D2.abnf.ws(w1) == True{} : Bool}}
  +er = {aq.sh(w2, D6.g.val.text(rv, rest), M23.gd.short.tail(',', String.append(w2, D6.g.val.text(rv, rest)),
    aq.sh(w1, SCon{',', String.append(w2, D6.g.val.text(rv, rest))}, aq.sh.val(kv, String.append(w1, SCon{',',
      String.append(w2, D6.g.val.text(rv, rest))}), es)))) : {D3.short(D6.g.val.text(rv, rest)) == True{} : Bool}}
  ihk(pos, rw, hs, at, sv, sk0, inl, ri, bk, qk, un, lf, ab, String.append(w1, SCon{',', String.append(w2,
    D6.g.val.text(rv, rest))}), G, aq.kvok.k(kv, Eq.and.left(D1.g.ok.val(kv, D1.RKeyval{}),
      Bool.and(D2.abnf.ws(w1), Bool.and(D2.abnf.ws(w2), D1.g.ok.val(rv, D1.RInlineTableKeyvals{}))), ok)), es,
        aq.fol.ws(w1, SCon{',', String.append(w2, D6.g.val.text(rv, rest))}, h1, {==}), hi,
          aq.kvsk(D5.replay.go(kv, D5.RaRows{ri, ""}), w1, w2, rv, rw, hs, at, sv, sk0, ab, rest, G, h1,
            Eq.and.left(D2.abnf.ws(w2), D1.g.ok.val(rv, D1.RInlineTableKeyvals{}), h2r),
              Eq.and.right(D2.abnf.ws(w2), D1.g.ok.val(rv, D1.RInlineTableKeyvals{}), h2r), er, hf, kk, ihr))

# every value node, as a value, as an array's items and as an inline table's
# keyvals, each claim by the rule its node spells
def aq.rd(
  nd: D6.GVal
) -> aq.RD(nd):
  match nd:
    case D6.GvString{+st}:
      +a => +b => aq.pick(a, b, D6.GvString{st},
        (+m => +rw => +hs => +he => +ps => +bk => +qk => +sk => +un => +lf => +ab => +rest => +G => +ok => +es =>
          +hf => kk =>
          aq.v.str(st, m, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, G, ok, es, hf, kk)),
        aq.noi(D6.GvString{st}, {==}),
        aq.nok(D6.GvString{st}, {==}))
    case D6.GvBoolean{+cs}:
      +a => +b => aq.pick(a, b, D6.GvBoolean{cs},
        (+m => +rw => +hs => +he => +ps => +bk => +qk => +sk => +un => +lf => +ab => +rest => +G => +ok => +_es =>
          +hf => kk =>
          aq.v.word(cs, m, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, G,
            L2.boolean_is_bare_word(String.from_list(cs), aq.tlp(xs => {D3.abnf.boolean(xs) == True{} : Bool}, cs,
              ok)), hf, kk)),
        aq.noi(D6.GvBoolean{cs}, {==}),
        aq.nok(D6.GvBoolean{cs}, {==}))
    case D6.GvArrayEmpty{+wn}:
      +a => +b => aq.pick(a, b, D6.GvArrayEmpty{wn},
        (+m => +rw => +hs => +he => +ps => +bk => +qk => +sk => +un => +lf => +ab => +rest => +G => +ok => +_es =>
          +_hf => kk =>
          aq.v.arr0(wn, m, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, G, ok, kk)),
        aq.noi(D6.GvArrayEmpty{wn}, {==}),
        aq.nok(D6.GvArrayEmpty{wn}, {==}))
    case D6.GvArray{+vals, +wn}:
      +a => +b => aq.pick(a, b, D6.GvArray{vals, wn},
        (+m => +rw => +hs => +he => +ps => +bk => +qk => +sk => +un => +lf => +ab => +rest => +G => +ok => +es =>
          +_hf => kk =>
          aq.v.arr(vals, wn, m, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, G, Eq.and.left(D1.g.ok.val(vals,
            D1.RArrayValues{}), D1.g.ok.wcn(wn), ok), Eq.and.right(D1.g.ok.val(vals, D1.RArrayValues{}),
              D1.g.ok.wcn(wn), ok), es, kk, aq.rd(vals)(False{}, True{}))),
        aq.noi(D6.GvArray{vals, wn}, {==}),
        aq.nok(D6.GvArray{vals, wn}, {==}))
    case D6.GvInlineTableEmpty{+w1, +w2}:
      +a => +b => aq.pick(a, b, D6.GvInlineTableEmpty{w1, w2},
        (+m => +rw => +hs => +he => +ps => +bk => +qk => +sk => +un => +lf => +ab => +rest => +G => +ok => +_es =>
          +_hf => kk =>
          aq.v.inl0(w1, w2, m, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, G, Eq.and.left(D2.abnf.ws(w1),
            D2.abnf.ws(w2), ok), Eq.and.right(D2.abnf.ws(w1), D2.abnf.ws(w2), ok), kk)),
        aq.noi(D6.GvInlineTableEmpty{w1, w2}, {==}),
        aq.nok(D6.GvInlineTableEmpty{w1, w2}, {==}))
    case D6.GvInlineTable{+w1, +kvs, +w2}:
      +a => +b => aq.pick(a, b, D6.GvInlineTable{w1, kvs, w2},
        (+m => +rw => +hs => +he => +ps => +bk => +qk => +sk => +un => +lf => +ab => +rest => +G => +ok => +es =>
          +_hf => kk =>
          aq.v.inl(w1, kvs, w2, m, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, G, Eq.and.left(D2.abnf.ws(w1),
            Bool.and(D1.g.ok.val(kvs, D1.RInlineTableKeyvals{}), D2.abnf.ws(w2)), ok),
              Eq.and.left(D1.g.ok.val(kvs, D1.RInlineTableKeyvals{}), D2.abnf.ws(w2),
                Eq.and.right(D2.abnf.ws(w1), Bool.and(D1.g.ok.val(kvs, D1.RInlineTableKeyvals{}),
                  D2.abnf.ws(w2)), ok)), Eq.and.right(D1.g.ok.val(kvs, D1.RInlineTableKeyvals{}),
                    D2.abnf.ws(w2), Eq.and.right(D2.abnf.ws(w1), Bool.and(D1.g.ok.val(kvs,
                      D1.RInlineTableKeyvals{}), D2.abnf.ws(w2)), ok)), es, kk, aq.rd(kvs)(False{}, False{}))),
        aq.noi(D6.GvInlineTable{w1, kvs, w2}, {==}),
        aq.nok(D6.GvInlineTable{w1, kvs, w2}, {==}))
    case D6.GvDateTime{+cs}:
      +a => +b => aq.pick(a, b, D6.GvDateTime{cs},
        (+m => +rw => +hs => +he => +ps => +bk => +qk => +sk => +un => +lf => +ab => +rest => +G => +ok => +_es =>
          +hf => kk =>
          aq.v.word(cs, m, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, G,
            L3.date_time_is_bare_word(String.from_list(cs), aq.tlp(xs => {D1.abnf.date_time(xs) == True{} : Bool},
              cs, Eq.and.left(D1.abnf.date_time(cs), D1.prose.date_time_in_range(cs), ok))), hf, kk)),
        aq.noi(D6.GvDateTime{cs}, {==}),
        aq.nok(D6.GvDateTime{cs}, {==}))
    case D6.GvFloat{+cs}:
      +a => +b => aq.pick(a, b, D6.GvFloat{cs},
        (+m => +rw => +hs => +he => +ps => +bk => +qk => +sk => +un => +lf => +ab => +rest => +G => +ok => +_es =>
          +hf => kk =>
          aq.v.word(cs, m, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, G,
            L6.float_is_bare_word(String.from_list(cs), aq.tlp(xs => {D1.abnf.float(xs) == True{} : Bool}, cs,
              ok)), hf, kk)),
        aq.noi(D6.GvFloat{cs}, {==}),
        aq.nok(D6.GvFloat{cs}, {==}))
    case D6.GvInteger{+cs}:
      +a => +b => aq.pick(a, b, D6.GvInteger{cs},
        (+m => +rw => +hs => +he => +ps => +bk => +qk => +sk => +un => +lf => +ab => +rest => +G => +ok => +_es =>
          +hf => kk =>
          aq.v.word(cs, m, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, G,
            L8.integer_is_bare_word(String.from_list(cs), aq.tlp(xs => {D1.abnf.integer(xs) == True{} : Bool}, cs,
              Eq.and.left(D1.abnf.integer(cs), D1.prose.int_in_range(cs), ok))), hf, kk)),
        aq.noi(D6.GvInteger{cs}, {==}),
        aq.nok(D6.GvInteger{cs}, {==}))
    case D6.GArrayValues{+wa, +val, +wb, +rv}:
      +a => +b => aq.pick(a, b, D6.GArrayValues{wa, val, wb, rv},
        aq.nov(D6.GArrayValues{wa, val, wb, rv}, {==}),
        (+rw => +hs => +at => +p => +sv => +sk0 => +its => +ri => +bk => +qk => +un => +lf => +ab => +rest => +G =>
          +ok => +es => +hf => +hi => kk =>
          aq.i.av(wa, val, wb, rv, rw, hs, at, p, sv, sk0, its, ri, bk, qk, un, lf, ab, rest, G, ok, es, hf, hi, kk,
            aq.rd(val)(True{}, True{}), aq.rd(rv)(False{}, True{}))),
        aq.nok(D6.GArrayValues{wa, val, wb, rv}, {==}))
    case D6.GArrayValuesLast{+wa, +val, +wb, +sep}:
      +a => +b => aq.pick(a, b, D6.GArrayValuesLast{wa, val, wb, sep},
        aq.nov(D6.GArrayValuesLast{wa, val, wb, sep}, {==}),
        (+rw => +hs => +at => +p => +sv => +sk0 => +its => +ri => +bk => +qk => +un => +lf => +ab => +rest => +G =>
          +ok => +es => +hf => +hi => kk =>
          aq.i.avl(wa, val, wb, sep, rw, hs, at, p, sv, sk0, its, ri, bk, qk, un, lf, ab, rest, G, ok, es, hf, hi, kk,
            aq.rd(val)(True{}, True{}))),
        aq.nok(D6.GArrayValuesLast{wa, val, wb, sep}, {==}))
    case D6.GInlineTableKeyvals{+kv, +w1, +w2, +rv}:
      +a => +b => aq.pick(a, b, D6.GInlineTableKeyvals{kv, w1, w2, rv},
        aq.nov(D6.GInlineTableKeyvals{kv, w1, w2, rv}, {==}),
        aq.noi(D6.GInlineTableKeyvals{kv, w1, w2, rv}, {==}),
        (+pos => +rw => +hs => +at => +sv => +sk0 => +inl => +ri => +bk => +qk => +un => +lf => +ab => +rest => +G =>
          +ok => +es => +hf => +hi => kk =>
          aq.k.kvs(kv, w1, w2, rv, pos, rw, hs, at, sv, sk0, inl, ri, bk, qk, un, lf, ab, rest, G, ok, es, hf, hi, kk,
            aq.rd(kv)(False{}, False{}), aq.rd(rv)(False{}, False{}))))
    case D6.GInlineTableKeyvalsLast{+kv}:
      +a => +b => aq.pick(a, b, D6.GInlineTableKeyvalsLast{kv},
        aq.nov(D6.GInlineTableKeyvalsLast{kv}, {==}),
        aq.noi(D6.GInlineTableKeyvalsLast{kv}, {==}),
        (+pos => +rw => +hs => +at => +sv => +sk0 => +inl => +ri => +bk => +qk => +un => +lf => +ab => +rest => +G =>
          +ok => +es => +hf => +hi => kk =>
          aq.rd(kv)(False{}, False{})(pos, rw, hs, at, sv, sk0, inl, ri, bk, qk, un, lf, ab, rest, G, aq.kvok.k(kv,
            ok), es, hf, hi, kk)))
    case D6.GKeyval{+key, +wa, +wb, +val}:
      +a => +b => aq.pick(a, b, D6.GKeyval{key, wa, wb, val},
        aq.nov(D6.GKeyval{key, wa, wb, val}, {==}),
        aq.noi(D6.GKeyval{key, wa, wb, val}, {==}),
        (+pos => +rw => +hs => +at => +sv => +sk0 => +inl => +ri => +bk => +qk => +un => +lf => +ab => +rest => +G =>
          +ok => +es => +hf => +hi => kk =>
          aq.k.kv(key, wa, wb, val, pos, rw, hs, at, sv, sk0, inl, ri, bk, qk, un, lf, ab, rest, G, ok, es, hf, hi,
            kk, aq.rd(val)(True{}, True{}))))

# WP-A: a keyval line. Its blank space is passed over (ap.ws); KEY-3's key
# reader (kx.keys) reads the key and `=` from the start of a line with the
# segments pushed onto parts, from every back, qkind, uni and left; the
# blank space after `=` is passed over in LVal; the value, of any kind, is
# read by aq.rd, and put at the key's path in the lines' table (take.top). That walk commutes with own
# (ow.walk), so it ends where the replay's walk on the rows read out does,
# read out, and the rest of the line reads on as after a header (aq.hl). A
# word word.val refuses sets the error, which stays (wr.lift, error_stays).

# the keyval's walk has ended: the rest of the line and the text after it
# read, owned, to the replay from the walk's end read out
def aq.kvw(
  +en: T.End,
  +he: List<&2, String>,
  +w2: String,
  +com: D6.GCom,
  +tail: String,
  +ls: List<&2, D6.GLine>,
  +hw: {D2.abnf.ws(w2) == True{} : Bool},
  +hc: {D1.g.ok.com(com) == True{} : Bool},
  kk: aq.K(ls, tail),
  ee: M11.ap.E(ls),
  +b2: T.Lex,
  +q2: T.QKind,
  +u2: U32,
  +l2: U32
) -> {D3.own(T.doc.read(String.append(w2, D6.g.com.text(com, tail)), T.MScan{T.take.root(en, he, b2, q2, u2, l2,
  False{}, False{})})) == M11.ap.F(ls, D5.replay.end(ow.end(en), he)) : T.Doc}:
  match en:
    case T.End{+rows2, +bd2, +heads2}:
      aq.hl(bd2, rows2, heads2, he, w2, com, tail, ls, hw, hc, kk, ee)(b2, q2, u2, l2)

# a refused word's error: the document is the replay's, whose walk fails
def aq.kverr(
  +c0: Char,
  +cs: String,
  +vv: T.Val,
  +names: List<&2, String>,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ls: List<&2, D6.GLine>,
  ee: M11.ap.E(ls)
) -> {D3.own(T.Doc{SCon{c0, cs}, T.rows.seal(rw)}) == M11.ap.F(ls, D5.replay.root(names, D5.RaVal{vv, SCon{c0, cs}},
  D5.RpSt{"", D3.own.rows(rw), hs, he})) : T.Doc}:
  %Equal.sym(T.End, T.tree.walk(List.append(&2, String, he, names), T.Tw{D3.own.rows(rw), T.JPut{vv}, [], SCon{c0,
    cs}, "", hs, False{}}, T.path.len(he, 0)), T.End{D3.own.rows(rw), SCon{c0, cs}, hs},
      L4.failed_walk_changes_nothing(List.append(&2, String, he, names), D3.own.rows(rw), T.JPut{vv}, SCon{c0,
        cs}, "", hs, False{}, T.path.len(he, 0), {==})) : {D3.own(T.Doc{SCon{c0, cs}, T.rows.seal(rw)}) == M11.ap.F(ls,
          D5.replay.end(_, he)) : T.Doc}
  aq.err(SCon{c0, cs}, rw, hs, he, ls, {==}, ee)

# a root keyval's value, however the replay reads it: the value put at the
# key's path, and the rest read, owned, to the replay's walk and the lines
# after it
def aq.kvk(
  +rr: D5.RpAcc,
  +names: List<&2, String>,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +acc: List<&2, String>,
  +w2: String,
  +com: D6.GCom,
  +tail: String,
  +ls: List<&2, D6.GLine>,
  +hp: {List.reverse(&2, String, acc) == names : List<&2, String>},
  +hw: {D2.abnf.ws(w2) == True{} : Bool},
  +hc: {D1.g.ok.com(com) == True{} : Bool},
  kk: aq.K(ls, tail),
  ee: M11.ap.E(ls)
) -> aq.vk(rr, rw, hs, he, acc, [], False{}, String.append(w2, D6.g.com.text(com, tail)), dd =>
  {D3.own(dd) == M11.ap.F(ls, D5.replay.root(names, rr, D5.RpSt{"", D3.own.rows(rw), hs, he})) : T.Doc}):
  match rr:
    case D5.RaVal{+vv, +bd}:
      match bd:
        case SNil{}:
          +xv => +b2 => +q2 => +u2 => +l2 => hv => _hc =>
            %hv : {D3.own(T.doc.read(String.append(w2, D6.g.com.text(com, tail)), T.MScan{T.take.top([], xv, "",
              rw, hs, he, acc, b2, q2, u2, l2, False{}, False{})})) == M11.ap.F(ls,
                D5.replay.end(T.tree.walk(List.append(&2, String, he, names), T.Tw{D3.own.rows(rw), T.JPut{_}, [],
                  "", "", hs, False{}}, T.path.len(he, 0)), he)) : T.Doc}
            %hp : {D3.own(T.doc.read(String.append(w2, D6.g.com.text(com, tail)), T.MScan{T.take.top([], xv, "",
              rw, hs, he, acc, b2, q2, u2, l2, False{}, False{})})) == M11.ap.F(ls,
                D5.replay.end(T.tree.walk(List.append(&2, String, he, _), T.Tw{D3.own.rows(rw), T.JPut{ow.v(xv)},
                  [], "", "", hs, False{}}, T.path.len(he, 0)), he)) : T.Doc}
            %ow.walk(List.append(&2, String, he, List.reverse(&2, String, acc)), T.Tw{rw, T.JPut{xv}, [], "", "", hs,
              False{}}, T.path.len(he, 0)) : {D3.own(T.doc.read(String.append(w2, D6.g.com.text(com, tail)),
                T.MScan{T.take.top([], xv, "", rw, hs, he, acc, b2, q2, u2, l2, False{}, False{})})) == M11.ap.F(ls,
                  D5.replay.end(_, he)) : T.Doc}
            aq.kvw(T.tree.walk(T.path.cat(he, acc), T.Tw{rw, T.JPut{xv}, [], "", "", hs, False{}}, T.path.len(he, 0)),
              he, w2, com, tail, ls, hw, hc, kk, ee, b2, q2, u2, l2)
        case SCon{+c0, +cs}:
          aq.kverr(c0, cs, vv, names, rw, hs, he, ls, ee)
    case D5.RaItems{_i, _b}:
      Unit{}
    case D5.RaRows{_r, _b}:
      Unit{}

# a keyval's key, `=` and value, from the start of a line in any table: the
# rest is read as the value's continuation gives it
def aq.kvl(
  +key: D6.GKey,
  +wa: String,
  +wb: String,
  +val: D6.GVal,
  +rest: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +G: T.Doc,
  +hk: {D1.g.ok.key(key) == True{} : Bool},
  +hwa: {D2.abnf.ws(wa) == True{} : Bool},
  +hwb: {D2.abnf.ws(wb) == True{} : Bool},
  +ok: {D1.g.ok.val(val, D1.RVal{}) == True{} : Bool},
  +es: {D3.short(D6.g.val.text(val, rest)) == True{} : Bool},
  +hf: {aq.fol(rest) == True{} : Bool},
  kv: aq.VKV(val, rw, hs, he, M16.k3.acc(M11.ap.kds(key), M11.ap.klast(key), False{}, []), [], False{}, rest, G)
) -> {D3.own(T.doc.read(D6.g.key.text(key, String.append(wa, SCon{'=', String.append(wb, D6.g.val.text(val,
  rest))})), T.MScan{M11.ap.s(T.LTop{}, bk, rw, hs, he, [], qk, [], un, lf, False{})})) == G : T.Doc}:
  %Equal.sym(String, D6.g.key.text(key, String.append(wa, SCon{'=', String.append(wb, D6.g.val.text(val,
    rest))})), L9.k3.dk.text(M11.ap.kds(key), M11.ap.klast(key), String.append(wa, SCon{'=', String.append(wb,
      D6.g.val.text(val, rest))})), M11.ap.key.text(key, String.append(wa, SCon{'=', String.append(wb,
        D6.g.val.text(val, rest))}), hk)) : {D3.own(T.doc.read(_, T.MScan{M11.ap.s(T.LTop{}, bk, rw, hs, he, [], qk,
          [], un, lf, False{})})) == G : T.Doc}
  %M11.ap.gap(wa, hwa) : {D3.own(T.doc.read(L9.k3.dk.text(M11.ap.kds(key), M11.ap.klast(key), String.append(_, SCon{'=',
    String.append(wb, D6.g.val.text(val, rest))})), T.MScan{M11.ap.s(T.LTop{}, bk, rw, hs, he, [], qk, [], un, lf,
      False{})})) == G : T.Doc}
  kx.keys(M11.ap.kds(key), M11.ap.klast(key), M11.ap.gs(wa), False{}, L9.AtLine{}, rw, hs, he, [], bk, qk, [], un, lf,
      False{},
    String.append(wb, D6.g.val.text(val, rest)), dd => {D3.own(dd) == G : T.Doc}, M11.ap.key.ok(key, hk), +b2 =>
      +q2 => +u2 => +l2 =>
    %Equal.sym(T.Doc, T.doc.read(String.append(wb, D6.g.val.text(val, rest)), T.MScan{M11.ap.s(T.LVal{}, b2, rw, hs, he,
      M16.k3.acc(M11.ap.kds(key), M11.ap.klast(key), False{}, []), q2, [], u2, l2, False{})}),
          T.doc.read(D6.g.val.text(val,
        rest), T.MScan{M11.ap.s(T.LVal{}, b2, rw, hs, he, M16.k3.acc(M11.ap.kds(key), M11.ap.klast(key), False{}, []),
            q2, [], u2, l2,
          False{})}), M11.ap.ws(wb, D6.g.val.text(val, rest), T.LVal{}, b2, rw, hs, he, M16.k3.acc(M11.ap.kds(key),
            M11.ap.klast(key), False{}, []), q2, [], u2, l2, False{}, {==}, hwb)) : {D3.own(_) == G : T.Doc}
    aq.rd(val)(True{}, True{})(False{}, rw, hs, he, M16.k3.acc(M11.ap.kds(key), M11.ap.klast(key), False{}, []), b2,
        q2, [], u2, l2,
      False{}, rest, G, ok, es, hf, kv))

# a keyval line's expression
def aq.kx(
  +w1: String,
  +key: D6.GKey,
  +wa: String,
  +wb: String,
  +val: D6.GVal,
  +w2: String,
  +com: D6.GCom
) -> D6.GExpr:
  D6.GxKeyval{w1, D6.GKeyval{key, wa, wb, val}, w2, com}

# a keyval line, its value of any kind, from the start of a line in any
# table, then the rest as aq.K reads it
def aq.xkv(
  +w1: String,
  +key: D6.GKey,
  +wa: String,
  +wb: String,
  +val: D6.GVal,
  +w2: String,
  +com: D6.GCom,
  +tail: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ls: List<&2, D6.GLine>,
  +hx: {D1.g.ok.expr(D6.GxKeyval{w1, D6.GKeyval{key, wa, wb, val}, w2, com}) == True{} : Bool},
  +es: {D3.short(D6.g.expr.text(aq.kx(w1, key, wa, wb, val, w2, com), tail)) == True{} : Bool},
  +hft: {aq.fol(tail) == True{} : Bool},
  kk: aq.K(ls, tail),
  ee: M11.ap.E(ls)
) -> {D3.own(T.doc.read(D6.g.expr.text(D6.GxKeyval{w1, D6.GKeyval{key, wa, wb, val}, w2, com}, tail),
  T.MScan{M11.ap.s(T.LTop{}, bk, rw, hs, he, [], qk, [], un, lf, False{})})) == M11.ap.F(ls,
    D5.replay.expr(D6.GxKeyval{w1, D6.GKeyval{key, wa, wb, val}, w2, com}, D5.RpSt{"", D3.own.rows(rw), hs,
      he})) : T.Doc}:
  +hr1 = {Eq.and.right(D2.abnf.ws(w1), Bool.and(D1.g.ok.val(D6.GKeyval{key, wa, wb, val}, D1.RKeyval{}),
    Bool.and(D2.abnf.ws(w2), D1.g.ok.com(com))), hx) : {Bool.and(D1.g.ok.val(D6.GKeyval{key, wa, wb, val},
      D1.RKeyval{}), Bool.and(D2.abnf.ws(w2), D1.g.ok.com(com))) == True{} : Bool}}
  +hkv = {Eq.and.left(D1.g.ok.val(D6.GKeyval{key, wa, wb, val}, D1.RKeyval{}), Bool.and(D2.abnf.ws(w2),
    D1.g.ok.com(com)), hr1) : {Bool.and(D1.g.ok.key(key), Bool.and(D2.abnf.ws(wa), Bool.and(D2.abnf.ws(wb),
      D1.g.ok.val(val, D1.RVal{})))) == True{} : Bool}}
  +hr2 = {Eq.and.right(D1.g.ok.val(D6.GKeyval{key, wa, wb, val}, D1.RKeyval{}), Bool.and(D2.abnf.ws(w2),
    D1.g.ok.com(com)), hr1) : {Bool.and(D2.abnf.ws(w2), D1.g.ok.com(com)) == True{} : Bool}}
  +ha2 = {Eq.and.right(D1.g.ok.key(key), Bool.and(D2.abnf.ws(wa), Bool.and(D2.abnf.ws(wb), D1.g.ok.val(val,
    D1.RVal{}))), hkv) : {Bool.and(D2.abnf.ws(wa), Bool.and(D2.abnf.ws(wb), D1.g.ok.val(val,
      D1.RVal{}))) == True{} : Bool}}
  +ha3 = {Eq.and.right(D2.abnf.ws(wa), Bool.and(D2.abnf.ws(wb), D1.g.ok.val(val, D1.RVal{})),
    ha2) : {Bool.and(D2.abnf.ws(wb), D1.g.ok.val(val, D1.RVal{})) == True{} : Bool}}
  +s1 = {aq.sh(w1, D6.g.key.text(key, String.append(wa, SCon{'=', String.append(wb, D6.g.val.text(val,
    String.append(w2, D6.g.com.text(com, tail))))})), es) : {D3.short(D6.g.key.text(key, String.append(wa,
      SCon{'=', String.append(wb, D6.g.val.text(val, String.append(w2, D6.g.com.text(com,
        tail))))}))) == True{} : Bool}}
  +s2 = {aq.sh(D6.g.key.text(key, ""), String.append(wa, SCon{'=', String.append(wb, D6.g.val.text(val,
    String.append(w2, D6.g.com.text(com, tail))))}), aq.shq(D6.g.key.text(key, String.append(wa, SCon{'=',
      String.append(wb, D6.g.val.text(val, String.append(w2, D6.g.com.text(com, tail))))})),
        String.append(D6.g.key.text(key, ""), String.append(wa, SCon{'=', String.append(wb, D6.g.val.text(val,
          String.append(w2, D6.g.com.text(com, tail))))})), M15.gt.key(key, String.append(wa, SCon{'=',
            String.append(wb, D6.g.val.text(val, String.append(w2, D6.g.com.text(com, tail))))})),
              s1)) : {D3.short(String.append(wa, SCon{'=', String.append(wb, D6.g.val.text(val, String.append(w2,
                D6.g.com.text(com, tail))))})) == True{} : Bool}}
  +s5 = {aq.sh(wb, D6.g.val.text(val, String.append(w2, D6.g.com.text(com, tail))), M23.gd.short.tail('=',
    String.append(wb, D6.g.val.text(val, String.append(w2, D6.g.com.text(com, tail)))), aq.sh(wa, SCon{'=',
      String.append(wb, D6.g.val.text(val, String.append(w2, D6.g.com.text(com, tail))))},
        s2))) : {D3.short(D6.g.val.text(val, String.append(w2, D6.g.com.text(com, tail)))) == True{} : Bool}}
  Equal.trans(T.Doc, D3.own(T.doc.read(String.append(w1, D6.g.key.text(key, String.append(wa, SCon{'=',
    String.append(wb, D6.g.val.text(val, String.append(w2, D6.g.com.text(com, tail))))}))), T.MScan{M11.ap.s(T.LTop{},
      bk, rw, hs, he, [], qk, [], un, lf, False{})})), D3.own(T.doc.read(D6.g.key.text(key, String.append(wa,
        SCon{'=', String.append(wb, D6.g.val.text(val, String.append(w2, D6.g.com.text(com, tail))))})),
          T.MScan{M11.ap.s(T.LTop{}, bk, rw, hs, he, [], qk, [], un, lf, False{})})), M11.ap.F(ls,
            D5.replay.expr(D6.GxKeyval{w1, D6.GKeyval{key, wa, wb, val}, w2, com}, D5.RpSt{"",
              D3.own.rows(rw), hs, he})), Equal.cong(T.Doc, T.Doc, dd => D3.own(dd), T.doc.read(String.append(w1,
                D6.g.key.text(key, String.append(wa, SCon{'=', String.append(wb, D6.g.val.text(val,
                  String.append(w2, D6.g.com.text(com, tail))))}))), T.MScan{M11.ap.s(T.LTop{}, bk, rw, hs, he, [], qk,
                    [], un, lf, False{})}), T.doc.read(D6.g.key.text(key, String.append(wa, SCon{'=',
                      String.append(wb, D6.g.val.text(val, String.append(w2, D6.g.com.text(com, tail))))})),
                        T.MScan{M11.ap.s(T.LTop{}, bk, rw, hs, he, [], qk, [], un, lf, False{})}), M11.ap.ws(w1,
                          D6.g.key.text(key, String.append(wa, SCon{'=', String.append(wb, D6.g.val.text(val,
                            String.append(w2, D6.g.com.text(com, tail))))})), T.LTop{}, bk, rw, hs, he, [], qk, [],
                              un, lf, False{}, {==}, Eq.and.left(D2.abnf.ws(w1),
                                Bool.and(D1.g.ok.val(D6.GKeyval{key, wa, wb, val}, D1.RKeyval{}),
                                  Bool.and(D2.abnf.ws(w2), D1.g.ok.com(com))), hx))), aq.kvl(key, wa, wb, val,
                                    String.append(w2, D6.g.com.text(com, tail)), rw, hs, he, bk, qk, un, lf,
                                      M11.ap.F(ls, D5.replay.expr(D6.GxKeyval{w1, D6.GKeyval{key, wa, wb, val}, w2,
                                        com}, D5.RpSt{"", D3.own.rows(rw), hs, he})),
                                          Eq.and.left(D1.g.ok.key(key), Bool.and(D2.abnf.ws(wa),
                                            Bool.and(D2.abnf.ws(wb), D1.g.ok.val(val, D1.RVal{}))), hkv),
                                              Eq.and.left(D2.abnf.ws(wa), Bool.and(D2.abnf.ws(wb),
                                                D1.g.ok.val(val, D1.RVal{})), ha2), Eq.and.left(D2.abnf.ws(wb),
                                                  D1.g.ok.val(val, D1.RVal{}), ha3),
                                                    Eq.and.right(D2.abnf.ws(wb), D1.g.ok.val(val, D1.RVal{}),
                                                      ha3), s5, aq.fol.ws(w2, D6.g.com.text(com, tail),
                                                        Eq.and.left(D2.abnf.ws(w2), D1.g.ok.com(com), hr2),
                                                          aq.fol.com(com, tail, hft)), aq.kvk(D5.replay.go(val,
                                                            D5.RaVal{T.VArr{[]}, ""}), D1.g.key.names(key), rw,
                                                              hs, he, M16.k3.acc(M11.ap.kds(key), M11.ap.klast(key),
                                                                  False{}, []),
                                                                w2, com, tail, ls, aq.kpath(key),
                                                                  Eq.and.left(D2.abnf.ws(w2), D1.g.ok.com(com),
                                                                    hr2), Eq.and.right(D2.abnf.ws(w2),
                                                                      D1.g.ok.com(com), hr2), kk, ee)))

# a keyval line, by its value node: only a keyval is one g.ok allows
def aq.xkv0(
  +w1: String,
  +kv: D6.GVal,
  +w2: String,
  +com: D6.GCom,
  +tail: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ls: List<&2, D6.GLine>,
  +hx: {D1.g.ok.expr(D6.GxKeyval{w1, kv, w2, com}) == True{} : Bool},
  +es: {D3.short(D6.g.expr.text(D6.GxKeyval{w1, kv, w2, com}, tail)) == True{} : Bool},
  +hft: {aq.fol(tail) == True{} : Bool},
  kk: aq.K(ls, tail),
  ee: M11.ap.E(ls)
) -> {D3.own(T.doc.read(D6.g.expr.text(D6.GxKeyval{w1, kv, w2, com}, tail), T.MScan{M11.ap.s(T.LTop{}, bk, rw, hs,
  he, [], qk, [], un, lf, False{})})) == M11.ap.F(ls, D5.replay.expr(D6.GxKeyval{w1, kv, w2, com}, D5.RpSt{"",
    D3.own.rows(rw), hs, he})) : T.Doc}:
  match kv:
    case D6.GKeyval{+key, +wa, +wb, +val}:
      aq.xkv(w1, key, wa, wb, val, w2, com, tail, rw, hs, he, bk, qk, un, lf, ls, hx, es, hft, kk, ee)
    case D6.GvString{_a0}:
      Eq.bit.absurd(&2, {D3.own(T.doc.read(D6.g.expr.text(D6.GxKeyval{w1, D6.GvString{_a0}, w2, com}, tail),
        T.MScan{M11.ap.s(T.LTop{}, bk, rw, hs, he, [], qk, [], un, lf, False{})})) == M11.ap.F(ls,
          D5.replay.expr(D6.GxKeyval{w1, D6.GvString{_a0}, w2, com}, D5.RpSt{"", D3.own.rows(rw), hs,
            he})) : T.Doc}, Eq.and.left(D1.g.ok.val(D6.GvString{_a0}, D1.RKeyval{}), Bool.and(D2.abnf.ws(w2),
              D1.g.ok.com(com)), Eq.and.right(D2.abnf.ws(w1), Bool.and(D1.g.ok.val(D6.GvString{_a0},
                D1.RKeyval{}), Bool.and(D2.abnf.ws(w2), D1.g.ok.com(com))), hx)))
    case D6.GvBoolean{_a0}:
      Eq.bit.absurd(&2, {D3.own(T.doc.read(D6.g.expr.text(D6.GxKeyval{w1, D6.GvBoolean{_a0}, w2, com}, tail),
        T.MScan{M11.ap.s(T.LTop{}, bk, rw, hs, he, [], qk, [], un, lf, False{})})) == M11.ap.F(ls,
          D5.replay.expr(D6.GxKeyval{w1, D6.GvBoolean{_a0}, w2, com}, D5.RpSt{"", D3.own.rows(rw), hs,
            he})) : T.Doc}, Eq.and.left(D1.g.ok.val(D6.GvBoolean{_a0}, D1.RKeyval{}), Bool.and(D2.abnf.ws(w2),
              D1.g.ok.com(com)), Eq.and.right(D2.abnf.ws(w1), Bool.and(D1.g.ok.val(D6.GvBoolean{_a0},
                D1.RKeyval{}), Bool.and(D2.abnf.ws(w2), D1.g.ok.com(com))), hx)))
    case D6.GvArrayEmpty{_a0}:
      Eq.bit.absurd(&2, {D3.own(T.doc.read(D6.g.expr.text(D6.GxKeyval{w1, D6.GvArrayEmpty{_a0}, w2, com},
        tail), T.MScan{M11.ap.s(T.LTop{}, bk, rw, hs, he, [], qk, [], un, lf, False{})})) == M11.ap.F(ls,
          D5.replay.expr(D6.GxKeyval{w1, D6.GvArrayEmpty{_a0}, w2, com}, D5.RpSt{"", D3.own.rows(rw), hs,
            he})) : T.Doc}, Eq.and.left(D1.g.ok.val(D6.GvArrayEmpty{_a0}, D1.RKeyval{}),
              Bool.and(D2.abnf.ws(w2), D1.g.ok.com(com)), Eq.and.right(D2.abnf.ws(w1),
                Bool.and(D1.g.ok.val(D6.GvArrayEmpty{_a0}, D1.RKeyval{}), Bool.and(D2.abnf.ws(w2),
                  D1.g.ok.com(com))), hx)))
    case D6.GvArray{_a0, _a1}:
      Eq.bit.absurd(&2, {D3.own(T.doc.read(D6.g.expr.text(D6.GxKeyval{w1, D6.GvArray{_a0, _a1}, w2, com},
        tail), T.MScan{M11.ap.s(T.LTop{}, bk, rw, hs, he, [], qk, [], un, lf, False{})})) == M11.ap.F(ls,
          D5.replay.expr(D6.GxKeyval{w1, D6.GvArray{_a0, _a1}, w2, com}, D5.RpSt{"", D3.own.rows(rw), hs,
            he})) : T.Doc}, Eq.and.left(D1.g.ok.val(D6.GvArray{_a0, _a1}, D1.RKeyval{}),
              Bool.and(D2.abnf.ws(w2), D1.g.ok.com(com)), Eq.and.right(D2.abnf.ws(w1),
                Bool.and(D1.g.ok.val(D6.GvArray{_a0, _a1}, D1.RKeyval{}), Bool.and(D2.abnf.ws(w2),
                  D1.g.ok.com(com))), hx)))
    case D6.GvInlineTableEmpty{_a0, _a1}:
      Eq.bit.absurd(&2, {D3.own(T.doc.read(D6.g.expr.text(D6.GxKeyval{w1, D6.GvInlineTableEmpty{_a0, _a1}, w2,
        com}, tail), T.MScan{M11.ap.s(T.LTop{}, bk, rw, hs, he, [], qk, [], un, lf, False{})})) == M11.ap.F(ls,
          D5.replay.expr(D6.GxKeyval{w1, D6.GvInlineTableEmpty{_a0, _a1}, w2, com}, D5.RpSt{"",
            D3.own.rows(rw), hs, he})) : T.Doc}, Eq.and.left(D1.g.ok.val(D6.GvInlineTableEmpty{_a0, _a1},
              D1.RKeyval{}), Bool.and(D2.abnf.ws(w2), D1.g.ok.com(com)), Eq.and.right(D2.abnf.ws(w1),
                Bool.and(D1.g.ok.val(D6.GvInlineTableEmpty{_a0, _a1}, D1.RKeyval{}), Bool.and(D2.abnf.ws(w2),
                  D1.g.ok.com(com))), hx)))
    case D6.GvInlineTable{_a0, _a1, _a2}:
      Eq.bit.absurd(&2, {D3.own(T.doc.read(D6.g.expr.text(D6.GxKeyval{w1, D6.GvInlineTable{_a0, _a1, _a2}, w2,
        com}, tail), T.MScan{M11.ap.s(T.LTop{}, bk, rw, hs, he, [], qk, [], un, lf, False{})})) == M11.ap.F(ls,
          D5.replay.expr(D6.GxKeyval{w1, D6.GvInlineTable{_a0, _a1, _a2}, w2, com}, D5.RpSt{"",
            D3.own.rows(rw), hs, he})) : T.Doc}, Eq.and.left(D1.g.ok.val(D6.GvInlineTable{_a0, _a1, _a2},
              D1.RKeyval{}), Bool.and(D2.abnf.ws(w2), D1.g.ok.com(com)), Eq.and.right(D2.abnf.ws(w1),
                Bool.and(D1.g.ok.val(D6.GvInlineTable{_a0, _a1, _a2}, D1.RKeyval{}), Bool.and(D2.abnf.ws(w2),
                  D1.g.ok.com(com))), hx)))
    case D6.GvDateTime{_a0}:
      Eq.bit.absurd(&2, {D3.own(T.doc.read(D6.g.expr.text(D6.GxKeyval{w1, D6.GvDateTime{_a0}, w2, com}, tail),
        T.MScan{M11.ap.s(T.LTop{}, bk, rw, hs, he, [], qk, [], un, lf, False{})})) == M11.ap.F(ls,
          D5.replay.expr(D6.GxKeyval{w1, D6.GvDateTime{_a0}, w2, com}, D5.RpSt{"", D3.own.rows(rw), hs,
            he})) : T.Doc}, Eq.and.left(D1.g.ok.val(D6.GvDateTime{_a0}, D1.RKeyval{}),
              Bool.and(D2.abnf.ws(w2), D1.g.ok.com(com)), Eq.and.right(D2.abnf.ws(w1),
                Bool.and(D1.g.ok.val(D6.GvDateTime{_a0}, D1.RKeyval{}), Bool.and(D2.abnf.ws(w2),
                  D1.g.ok.com(com))), hx)))
    case D6.GvFloat{_a0}:
      Eq.bit.absurd(&2, {D3.own(T.doc.read(D6.g.expr.text(D6.GxKeyval{w1, D6.GvFloat{_a0}, w2, com}, tail),
        T.MScan{M11.ap.s(T.LTop{}, bk, rw, hs, he, [], qk, [], un, lf, False{})})) == M11.ap.F(ls,
          D5.replay.expr(D6.GxKeyval{w1, D6.GvFloat{_a0}, w2, com}, D5.RpSt{"", D3.own.rows(rw), hs,
            he})) : T.Doc}, Eq.and.left(D1.g.ok.val(D6.GvFloat{_a0}, D1.RKeyval{}), Bool.and(D2.abnf.ws(w2),
              D1.g.ok.com(com)), Eq.and.right(D2.abnf.ws(w1), Bool.and(D1.g.ok.val(D6.GvFloat{_a0},
                D1.RKeyval{}), Bool.and(D2.abnf.ws(w2), D1.g.ok.com(com))), hx)))
    case D6.GvInteger{_a0}:
      Eq.bit.absurd(&2, {D3.own(T.doc.read(D6.g.expr.text(D6.GxKeyval{w1, D6.GvInteger{_a0}, w2, com}, tail),
        T.MScan{M11.ap.s(T.LTop{}, bk, rw, hs, he, [], qk, [], un, lf, False{})})) == M11.ap.F(ls,
          D5.replay.expr(D6.GxKeyval{w1, D6.GvInteger{_a0}, w2, com}, D5.RpSt{"", D3.own.rows(rw), hs,
            he})) : T.Doc}, Eq.and.left(D1.g.ok.val(D6.GvInteger{_a0}, D1.RKeyval{}), Bool.and(D2.abnf.ws(w2),
              D1.g.ok.com(com)), Eq.and.right(D2.abnf.ws(w1), Bool.and(D1.g.ok.val(D6.GvInteger{_a0},
                D1.RKeyval{}), Bool.and(D2.abnf.ws(w2), D1.g.ok.com(com))), hx)))
    case D6.GArrayValues{_a0, _a1, _a2, _a3}:
      Eq.bit.absurd(&2, {D3.own(T.doc.read(D6.g.expr.text(D6.GxKeyval{w1, D6.GArrayValues{_a0, _a1, _a2, _a3},
        w2, com}, tail), T.MScan{M11.ap.s(T.LTop{}, bk, rw, hs, he, [], qk, [], un, lf, False{})})) == M11.ap.F(ls,
          D5.replay.expr(D6.GxKeyval{w1, D6.GArrayValues{_a0, _a1, _a2, _a3}, w2, com}, D5.RpSt{"",
            D3.own.rows(rw), hs, he})) : T.Doc}, Eq.and.left(D1.g.ok.val(D6.GArrayValues{_a0, _a1, _a2, _a3},
              D1.RKeyval{}), Bool.and(D2.abnf.ws(w2), D1.g.ok.com(com)), Eq.and.right(D2.abnf.ws(w1),
                Bool.and(D1.g.ok.val(D6.GArrayValues{_a0, _a1, _a2, _a3}, D1.RKeyval{}),
                  Bool.and(D2.abnf.ws(w2), D1.g.ok.com(com))), hx)))
    case D6.GArrayValuesLast{_a0, _a1, _a2, _a3}:
      Eq.bit.absurd(&2, {D3.own(T.doc.read(D6.g.expr.text(D6.GxKeyval{w1, D6.GArrayValuesLast{_a0, _a1, _a2,
        _a3}, w2, com}, tail), T.MScan{M11.ap.s(T.LTop{}, bk, rw, hs, he, [], qk, [], un, lf,
            False{})})) == M11.ap.F(ls,
          D5.replay.expr(D6.GxKeyval{w1, D6.GArrayValuesLast{_a0, _a1, _a2, _a3}, w2, com}, D5.RpSt{"",
            D3.own.rows(rw), hs, he})) : T.Doc}, Eq.and.left(D1.g.ok.val(D6.GArrayValuesLast{_a0, _a1, _a2,
              _a3}, D1.RKeyval{}), Bool.and(D2.abnf.ws(w2), D1.g.ok.com(com)), Eq.and.right(D2.abnf.ws(w1),
                Bool.and(D1.g.ok.val(D6.GArrayValuesLast{_a0, _a1, _a2, _a3}, D1.RKeyval{}),
                  Bool.and(D2.abnf.ws(w2), D1.g.ok.com(com))), hx)))
    case D6.GInlineTableKeyvals{_a0, _a1, _a2, _a3}:
      Eq.bit.absurd(&2, {D3.own(T.doc.read(D6.g.expr.text(D6.GxKeyval{w1, D6.GInlineTableKeyvals{_a0, _a1,
        _a2, _a3}, w2, com}, tail), T.MScan{M11.ap.s(T.LTop{}, bk, rw, hs, he, [], qk, [], un, lf,
            False{})})) == M11.ap.F(ls,
          D5.replay.expr(D6.GxKeyval{w1, D6.GInlineTableKeyvals{_a0, _a1, _a2, _a3}, w2, com}, D5.RpSt{"",
            D3.own.rows(rw), hs, he})) : T.Doc}, Eq.and.left(D1.g.ok.val(D6.GInlineTableKeyvals{_a0, _a1, _a2,
              _a3}, D1.RKeyval{}), Bool.and(D2.abnf.ws(w2), D1.g.ok.com(com)), Eq.and.right(D2.abnf.ws(w1),
                Bool.and(D1.g.ok.val(D6.GInlineTableKeyvals{_a0, _a1, _a2, _a3}, D1.RKeyval{}),
                  Bool.and(D2.abnf.ws(w2), D1.g.ok.com(com))), hx)))
    case D6.GInlineTableKeyvalsLast{_a0}:
      Eq.bit.absurd(&2, {D3.own(T.doc.read(D6.g.expr.text(D6.GxKeyval{w1, D6.GInlineTableKeyvalsLast{_a0}, w2,
        com}, tail), T.MScan{M11.ap.s(T.LTop{}, bk, rw, hs, he, [], qk, [], un, lf, False{})})) == M11.ap.F(ls,
          D5.replay.expr(D6.GxKeyval{w1, D6.GInlineTableKeyvalsLast{_a0}, w2, com}, D5.RpSt{"",
            D3.own.rows(rw), hs, he})) : T.Doc}, Eq.and.left(D1.g.ok.val(D6.GInlineTableKeyvalsLast{_a0},
              D1.RKeyval{}), Bool.and(D2.abnf.ws(w2), D1.g.ok.com(com)), Eq.and.right(D2.abnf.ws(w1),
                Bool.and(D1.g.ok.val(D6.GInlineTableKeyvalsLast{_a0}, D1.RKeyval{}), Bool.and(D2.abnf.ws(w2),
                  D1.g.ok.com(com))), hx)))

# one expression from the start of a line in any table, then the rest as
# aq.K reads it
def aq.xstep(
  +ex: D6.GExpr,
  +tail: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ls: List<&2, D6.GLine>,
  +hx: {D1.g.ok.expr(ex) == True{} : Bool},
  +es: {D3.short(D6.g.expr.text(ex, tail)) == True{} : Bool},
  +hft: {aq.fol(tail) == True{} : Bool},
  kk: aq.K(ls, tail),
  ee: M11.ap.E(ls)
) -> {D3.own(T.doc.read(D6.g.expr.text(ex, tail), T.MScan{M11.ap.s(T.LTop{}, bk, rw, hs, he, [], qk, [], un, lf,
  False{})})) == M11.ap.F(ls, D5.replay.expr(ex, D5.RpSt{"", D3.own.rows(rw), hs, he})) : T.Doc}:
  match ex:
    case D6.GxBlank{+w1, +com}:
      Equal.trans(T.Doc, D3.own(T.doc.read(String.append(w1, D6.g.com.text(com, tail)), T.MScan{M11.ap.s(T.LTop{}, bk,
        rw, hs, he, [], qk, [], un, lf, False{})})), D3.own(T.doc.read(tail, T.MScan{M11.ap.aft(com, T.LTop{}, bk, rw,
          hs, he, [], qk, [], un, lf, False{})})), M11.ap.F(ls, D5.RpSt{"", D3.own.rows(rw), hs, he}),
            Equal.cong(T.Doc, T.Doc, dd => D3.own(dd), T.doc.read(String.append(w1, D6.g.com.text(com, tail)),
              T.MScan{M11.ap.s(T.LTop{}, bk, rw, hs, he, [], qk, [], un, lf, False{})}), T.doc.read(tail,
                T.MScan{M11.ap.aft(com, T.LTop{}, bk, rw, hs, he, [], qk, [], un, lf, False{})}), M11.ap.tail(w1, com,
                    tail,
                  T.LTop{}, bk, rw, hs, he, [], qk, [], un, lf, False{}, {==}, {==}, Eq.and.left(D2.abnf.ws(w1),
                    D1.g.ok.com(com), hx), Eq.and.right(D2.abnf.ws(w1), D1.g.ok.com(com), hx))), kk(com,
                      T.LTop{}, {==}, bk, rw, hs, he, qk, un, lf))
    case D6.GxKeyval{+w1, +kv, +w2, +com}:
      aq.xkv0(w1, kv, w2, com, tail, rw, hs, he, bk, qk, un, lf, ls, hx, es, hft, kk, ee)
    case D6.GxTable{+w1, +tb, +w2, +com}:
      aq.xtb(tb, w1, w2, com, tail, rw, hs, he, bk, qk, un, lf, ls, hx, kk, ee)

# the end of the text after the last expression: the rows, sealed and read
# out
def aq.fin(
  +com: D6.GCom,
  +lx: T.Lex,
  +hl: {M11.ap.tll(lx) == True{} : Bool},
  +bk: T.Lex,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +qk: T.QKind,
  +un: U32,
  +lf: U32
) -> {D3.own(T.doc.read("", T.MScan{M11.ap.aft(com, lx, bk, rw, hs, he, [], qk, [], un, lf, False{})})) == M11.ap.F([],
  D5.RpSt{"", D3.own.rows(rw), hs, he}) : T.Doc}:
  Equal.trans(T.Doc, D3.own(T.doc.read("", T.MScan{M11.ap.aft(com, lx, bk, rw, hs, he, [], qk, [], un, lf, False{})})),
    D3.own(T.Doc{"", T.rows.seal(rw)}), T.Doc{"", T.rows.seal(D3.own.rows(rw))}, Equal.cong(T.Doc, T.Doc, dd =>
      D3.own(dd), T.doc.read("", T.MScan{M11.ap.aft(com, lx, bk, rw, hs, he, [], qk, [], un, lf, False{})}), T.Doc{"",
        T.rows.seal(rw)}, M11.ap.fin(com, lx, bk, rw, hs, he, [], qk, un, lf, False{}, hl)), Equal.cong(List<&2, T.Val>,
          T.Doc, zs => T.Doc{"", zs}, D3.own.rows(T.rows.seal(rw)), T.rows.seal(D3.own.rows(rw)), M22.cv.osl(rw)))

# the lines after a newline read from the start of the next line, own-level,
# to the replay
def aq.NL(
  +ex2: D6.GExpr,
  +ls2: List<&2, D6.GLine>,
  +lx: T.Lex,
  +bk: T.Lex,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +qk: T.QKind,
  +un: U32,
  +lf: U32
) -> Type:
  {D3.own(T.doc.read(D6.g.expr.text(ex2, D6.g.lines.text(ls2, "")), T.MScan{M11.ap.s(lx, bk, rw, hs, he, [], qk, [],
    un,
    lf, False{})})) == D5.replay.doc(D5.replay.lines(ls2, D5.replay.expr(ex2, D5.RpSt{"", D3.own.rows(rw), hs,
    he}))) : T.Doc}

# a newline, then the next line's expression and the lines after it, from
# the state a [ comment ] leaves, read own-level to the replay
def aq.nl(
  +com: D6.GCom,
  +lx: T.Lex,
  +nn: String,
  +ex2: D6.GExpr,
  +ls2: List<&2, D6.GLine>,
  +bk: T.Lex,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +hm: {M11.ap.coml(lx) == True{} : Bool},
  +hn: {D1.abnf.newline(nn) == True{} : Bool},
  ih: aq.NL(ex2, ls2, M11.ap.nlx(lx), M11.ap.abk(com, lx, bk), rw, hs, he, qk, un, lf)
) -> {D3.own(T.doc.read(String.append(nn, D6.g.expr.text(ex2, D6.g.lines.text(ls2, ""))), T.MScan{M11.ap.aft(com,
  lx, bk, rw, hs, he, [], qk, [], un, lf, False{})})) == M11.ap.F(D6.GLine{nn, ex2} <> ls2, D5.RpSt{"",
    D3.own.rows(rw), hs, he}) : T.Doc}:
  Equal.trans(T.Doc, D3.own(T.doc.read(String.append(nn, D6.g.expr.text(ex2, D6.g.lines.text(ls2, ""))),
    T.MScan{M11.ap.aft(com, lx, bk, rw, hs, he, [], qk, [], un, lf, False{})})), D3.own(T.doc.read(D6.g.expr.text(ex2,
      D6.g.lines.text(ls2, "")), T.MScan{M11.ap.s(M11.ap.nlx(lx), M11.ap.abk(com, lx, bk), rw, hs, he, [], qk, [], un,
          lf,
        False{})})), D5.replay.doc(D5.replay.lines(ls2, D5.replay.expr(ex2, D5.RpSt{"", D3.own.rows(rw), hs,
          he}))), Equal.cong(T.Doc, T.Doc, dd => D3.own(dd), T.doc.read(String.append(nn, D6.g.expr.text(ex2,
            D6.g.lines.text(ls2, ""))), T.MScan{M11.ap.aft(com, lx, bk, rw, hs, he, [], qk, [], un, lf, False{})}),
              T.doc.read(D6.g.expr.text(ex2, D6.g.lines.text(ls2, "")), T.MScan{M11.ap.s(M11.ap.nlx(lx),
                  M11.ap.abk(com, lx,
                bk), rw, hs, he, [], qk, [], un, lf, False{})}), M11.ap.eol(com, lx, nn, D6.g.expr.text(ex2,
                  D6.g.lines.text(ls2, "")), bk, rw, hs, he, [], qk, [], un, lf, False{}, hm, hn)), ih)

# the lines after an expression: the expression, a newline and the next
# line's, and so on to the end, read from the start of a line to a document
# own reads as the replay's
def aq.go(
  +ls: List<&2, D6.GLine>,
  +ex: D6.GExpr,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +hx: {D1.g.ok.expr(ex) == True{} : Bool},
  +hl: {D1.g.ok.lines(ls) == True{} : Bool},
  +es: {D3.short(D6.g.expr.text(ex, D6.g.lines.text(ls, ""))) == True{} : Bool}
) -> {D3.own(T.doc.read(D6.g.expr.text(ex, D6.g.lines.text(ls, "")), T.MScan{M11.ap.s(T.LTop{}, bk, rw, hs, he, [],
  qk, [], un, lf, False{})})) == D5.replay.doc(D5.replay.lines(ls, D5.replay.expr(ex, D5.RpSt{"",
    D3.own.rows(rw), hs, he}))) : T.Doc}:
  match ls:
    case []:
      aq.xstep(ex, "", rw, hs, he, bk, qk, un, lf, [], hx, es, {==}, +com => +lx => +h2 => +b2 => +r2 => +s2 => +e2 =>
        +q2 => +u2 => +l2 => aq.fin(com, lx, h2, b2, r2, s2, e2, q2, u2, l2), aq.E([]))
    case D6.GLine{+nn, +ex2} <> +ls2:
      +h1 = {Eq.and.right(D1.abnf.newline(nn), Bool.and(D1.g.ok.expr(ex2), D1.g.ok.lines(ls2)),
        hl) : {Bool.and(D1.g.ok.expr(ex2), D1.g.ok.lines(ls2)) == True{} : Bool}}
      +hn = {Eq.and.left(D1.abnf.newline(nn), Bool.and(D1.g.ok.expr(ex2), D1.g.ok.lines(ls2)),
        hl) : {D1.abnf.newline(nn) == True{} : Bool}}
      +es2 = {aq.sh(nn, D6.g.expr.text(ex2, D6.g.lines.text(ls2, "")), aq.sh(D6.g.expr.text(ex, ""),
        String.append(nn, D6.g.expr.text(ex2, D6.g.lines.text(ls2, ""))), aq.shq(D6.g.expr.text(ex,
          String.append(nn, D6.g.expr.text(ex2, D6.g.lines.text(ls2, "")))), String.append(D6.g.expr.text(ex,
            ""), String.append(nn, D6.g.expr.text(ex2, D6.g.lines.text(ls2, "")))), M15.gt.expr(ex, String.append(nn,
              D6.g.expr.text(ex2, D6.g.lines.text(ls2, "")))), es))) : {D3.short(D6.g.expr.text(ex2,
                D6.g.lines.text(ls2, ""))) == True{} : Bool}}
      aq.xstep(ex, String.append(nn, D6.g.expr.text(ex2, D6.g.lines.text(ls2, ""))), rw, hs, he, bk, qk, un, lf,
        D6.GLine{nn, ex2} <> ls2, hx, es, aq.fol.nl(nn, D6.g.expr.text(ex2, D6.g.lines.text(ls2, "")), hn),
        +com => +lx => +h2 => +b2 => +r2 => +s2 => +e2 => +q2 => +u2 => +l2 => M11.ap.tll.elim(l3 =>
          {D3.own(T.doc.read(String.append(nn, D6.g.expr.text(ex2, D6.g.lines.text(ls2, ""))),
            T.MScan{M11.ap.aft(com, l3, b2, r2, s2, e2, [], q2, [], u2, l2, False{})})) == M11.ap.F(D6.GLine{nn,
              ex2} <> ls2, D5.RpSt{"", D3.own.rows(r2), s2, e2}) : T.Doc}, lx, h2,
          aq.nl(com, T.LTop{}, nn, ex2, ls2, b2, r2, s2, e2, q2, u2, l2, {==}, hn, aq.go(ls2, ex2, r2, s2, e2,
            M11.ap.abk(com, T.LTop{}, b2), q2, u2, l2, Eq.and.left(D1.g.ok.expr(ex2), D1.g.ok.lines(ls2), h1),
              Eq.and.right(D1.g.ok.expr(ex2), D1.g.ok.lines(ls2), h1), es2)),
          aq.nl(com, T.LLine{}, nn, ex2, ls2, b2, r2, s2, e2, q2, u2, l2, {==}, hn, aq.go(ls2, ex2, r2, s2, e2,
            M11.ap.abk(com, T.LLine{}, b2), q2, u2, l2, Eq.and.left(D1.g.ok.expr(ex2), D1.g.ok.lines(ls2), h1),
              Eq.and.right(D1.g.ok.expr(ex2), D1.g.ok.lines(ls2), h1), es2))),
        aq.E(D6.GLine{nn, ex2} <> ls2))

# WP-A: the whole document. Its text starts with no byte-order mark (aq.nb.expr:
# a keyval starts with blank space and a key, whose first character is a
# bare-key character, a quotation mark or an apostrophe), so parse reads it
# from the start of a line (ap.lead), and the lines read own-level to the
# replay (aq.go).

# a bare-key character is no byte-order mark
def aq.nbc2(
  bom: Bool,
  +xx: U32,
  eb: {U32.is_eq(xx, 65279) == bom : Bool},
  hk: {D3.abnf.unquoted_key_char(Chr{xx}) == True{} : Bool}
) -> {Bool.not(bom) == True{} : Bool}:
  match bom:
    case False{}:
      {==}
    case True{}:
      Equal.trans(Bool, False{}, D3.abnf.unquoted_key_char(Chr{xx}), True{}, Equal.sym(Bool,
        D3.abnf.unquoted_key_char(Chr{xx}), False{}, Equal.cong(U32, Bool, uu =>
          D3.abnf.unquoted_key_char(Chr{uu}), xx, 65279, M22.s1.isk(xx, 65279, eb))), hk)

# and so a text that starts with one does not start with a byte-order mark
def aq.nbc(
  hh: Char,
  +hk: {D3.abnf.unquoted_key_char(hh) == True{} : Bool}
) -> {Bool.not(U32.is_eq(Char.to_u32(hh), 65279)) == True{} : Bool}:
  match hh:
    case Chr{+xx}:
      aq.nbc2(U32.is_eq(xx, 65279), xx, {==}, hk)

# a key segment starts with no byte-order mark
def aq.nb.seg(
  +sg: D7.KSeg,
  +xx: String,
  +hs: {D1.g.ok.seg(sg) == True{} : Bool}
) -> {M11.ap.nobom(D7.k3.seg.text(sg, xx)) == True{} : Bool}:
  match sg:
    case D7.KsBare{+name}:
      match name:
        case SNil{}:
          Eq.bit.absurd(&2, {M11.ap.nobom(D7.k3.seg.text(D7.KsBare{""}, xx)) == True{} : Bool}, hs)
        case SCon{+hh, +tt}:
          aq.nbc(hh, Eq.and.left(D3.abnf.unquoted_key_char(hh), D3.abnf.all_unquoted_key_chars(tt), hs))
    case D7.KsBasic{_pl}:
      {==}
    case D7.KsLit{_name}:
      {==}

# and so does a key
def aq.nb.key(
  +key: D6.GKey,
  +xx: String,
  +hk: {D1.g.ok.key(key) == True{} : Bool}
) -> {M11.ap.nobom(D6.g.key.text(key, xx)) == True{} : Bool}:
  match key:
    case D6.GSimpleKey{+sk}:
      aq.nb.seg(sk, xx, hk)
    case D6.GDottedKey{+sk, +more}:
      aq.nb.seg(sk, D6.g.dots.text(more, xx), Eq.and.left(D1.g.ok.seg(sk), D1.g.ok.dots(more),
        Eq.and.right(Bool.not(List.is_empty(&2, D6.GDotSep, more)), Bool.and(D1.g.ok.seg(sk),
          D1.g.ok.dots(more)), hk)))

# and so does a keyval
def aq.nb.kv(
  +kv: D6.GVal,
  +xx: String,
  +hk: {D1.g.ok.val(kv, D1.RKeyval{}) == True{} : Bool}
) -> {M11.ap.nobom(D6.g.val.text(kv, xx)) == True{} : Bool}:
  match kv:
    case D6.GKeyval{+key, +wa, +wb, +val}:
      aq.nb.key(key, String.append(wa, SCon{'=', String.append(wb, D6.g.val.text(val, xx))}),
        Eq.and.left(D1.g.ok.key(key), Bool.and(D2.abnf.ws(wa), Bool.and(D2.abnf.ws(wb), D1.g.ok.val(val,
          D1.RVal{}))), hk))
    case D6.GvString{_a0}:
      Eq.bit.absurd(&2, {M11.ap.nobom(D6.g.val.text(D6.GvString{_a0}, xx)) == True{} : Bool}, hk)
    case D6.GvBoolean{_a0}:
      Eq.bit.absurd(&2, {M11.ap.nobom(D6.g.val.text(D6.GvBoolean{_a0}, xx)) == True{} : Bool}, hk)
    case D6.GvArrayEmpty{_a0}:
      Eq.bit.absurd(&2, {M11.ap.nobom(D6.g.val.text(D6.GvArrayEmpty{_a0}, xx)) == True{} : Bool}, hk)
    case D6.GvArray{_a0, _a1}:
      Eq.bit.absurd(&2, {M11.ap.nobom(D6.g.val.text(D6.GvArray{_a0, _a1}, xx)) == True{} : Bool}, hk)
    case D6.GvInlineTableEmpty{_a0, _a1}:
      Eq.bit.absurd(&2, {M11.ap.nobom(D6.g.val.text(D6.GvInlineTableEmpty{_a0, _a1}, xx)) == True{} : Bool}, hk)
    case D6.GvInlineTable{_a0, _a1, _a2}:
      Eq.bit.absurd(&2, {M11.ap.nobom(D6.g.val.text(D6.GvInlineTable{_a0, _a1, _a2}, xx)) == True{} : Bool}, hk)
    case D6.GvDateTime{_a0}:
      Eq.bit.absurd(&2, {M11.ap.nobom(D6.g.val.text(D6.GvDateTime{_a0}, xx)) == True{} : Bool}, hk)
    case D6.GvFloat{_a0}:
      Eq.bit.absurd(&2, {M11.ap.nobom(D6.g.val.text(D6.GvFloat{_a0}, xx)) == True{} : Bool}, hk)
    case D6.GvInteger{_a0}:
      Eq.bit.absurd(&2, {M11.ap.nobom(D6.g.val.text(D6.GvInteger{_a0}, xx)) == True{} : Bool}, hk)
    case D6.GArrayValues{_a0, _a1, _a2, _a3}:
      Eq.bit.absurd(&2, {M11.ap.nobom(D6.g.val.text(D6.GArrayValues{_a0, _a1, _a2, _a3}, xx)) == True{} : Bool}, hk)
    case D6.GArrayValuesLast{_a0, _a1, _a2, _a3}:
      Eq.bit.absurd(&2, {M11.ap.nobom(D6.g.val.text(D6.GArrayValuesLast{_a0, _a1, _a2, _a3}, xx)) == True{} : Bool}, hk)
    case D6.GInlineTableKeyvals{_a0, _a1, _a2, _a3}:
      Eq.bit.absurd(&2, {M11.ap.nobom(D6.g.val.text(D6.GInlineTableKeyvals{_a0, _a1, _a2, _a3},
        xx)) == True{} : Bool}, hk)
    case D6.GInlineTableKeyvalsLast{_a0}:
      Eq.bit.absurd(&2, {M11.ap.nobom(D6.g.val.text(D6.GInlineTableKeyvalsLast{_a0}, xx)) == True{} : Bool}, hk)

# an expression starts with no byte-order mark, before a text that starts
# with none
def aq.nb.expr(
  +ex: D6.GExpr,
  +xx: String,
  +hx: {D1.g.ok.expr(ex) == True{} : Bool},
  +ht: {M11.ap.nobom(xx) == True{} : Bool}
) -> {M11.ap.nobom(D6.g.expr.text(ex, xx)) == True{} : Bool}:
  match ex:
    case D6.GxBlank{+w1, +com}:
      M11.ap.nb.ws(w1, D6.g.com.text(com, xx), Eq.and.left(D2.abnf.ws(w1), D1.g.ok.com(com), hx), M11.ap.nb.com(com, xx,
        ht))
    case D6.GxKeyval{+w1, +kv, +w2, +com}:
      M11.ap.nb.ws(w1, D6.g.val.text(kv, String.append(w2, D6.g.com.text(com, xx))), Eq.and.left(D2.abnf.ws(w1),
        Bool.and(D1.g.ok.val(kv, D1.RKeyval{}), Bool.and(D2.abnf.ws(w2), D1.g.ok.com(com))), hx), aq.nb.kv(kv,
          String.append(w2, D6.g.com.text(com, xx)), Eq.and.left(D1.g.ok.val(kv, D1.RKeyval{}),
            Bool.and(D2.abnf.ws(w2), D1.g.ok.com(com)), Eq.and.right(D2.abnf.ws(w1), Bool.and(D1.g.ok.val(kv,
              D1.RKeyval{}), Bool.and(D2.abnf.ws(w2), D1.g.ok.com(com))), hx))))
    case D6.GxTable{+w1, +tb, +w2, +com}:
      M11.ap.nb.ws(w1, D6.g.table.text(tb, String.append(w2, D6.g.com.text(com, xx))), Eq.and.left(D2.abnf.ws(w1),
        Bool.and(D1.g.ok.table(tb), Bool.and(D2.abnf.ws(w2), D1.g.ok.com(com))), hx), M11.ap.nb.tb(tb,
          String.append(w2, D6.g.com.text(com, xx))))

def Laws.text_reads_as_replay(d, ok, es):
  match d:
    case D6.GToml{+first, +rest}:
      Equal.trans(T.Doc, D3.own(T.doc.read(D6.g.expr.text(first, D6.g.lines.text(rest, "")),
        T.MScan{T.st.start()})), D3.own(T.doc.read(D6.g.expr.text(first, D6.g.lines.text(rest, "")),
          T.MScan{M11.ap.s0()})), D5.replay(D6.GToml{first, rest}), Equal.cong(T.Doc, T.Doc, dd => D3.own(dd),
            T.doc.read(D6.g.expr.text(first, D6.g.lines.text(rest, "")), T.MScan{T.st.start()}),
              T.doc.read(D6.g.expr.text(first, D6.g.lines.text(rest, "")), T.MScan{M11.ap.s0()}),
                M11.ap.lead(D6.g.expr.text(first, D6.g.lines.text(rest, "")), aq.nb.expr(first,
                  D6.g.lines.text(rest, ""), Eq.and.left(D1.g.ok.expr(first), D1.g.ok.lines(rest), ok),
                    M11.ap.nb.lines(rest, Eq.and.right(D1.g.ok.expr(first), D1.g.ok.lines(rest), ok))))), aq.go(rest,
                      first, [], [], [], T.LTop{}, T.QBasic{}, 0, 0, Eq.and.left(D1.g.ok.expr(first),
                        D1.g.ok.lines(rest), ok), Eq.and.right(D1.g.ok.expr(first), D1.g.ok.lines(rest), ok), es))
