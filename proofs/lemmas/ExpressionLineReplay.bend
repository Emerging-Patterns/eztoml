# replay of expression lines, headers and comments from a given state
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/BareKey.bend as L1
import ../../laws/DefinesEachTableOnce.bend as L2
import ../../laws/ErrorStays.bend as L3
import ../../laws/HeadersParseAsReplay.bend as L4
import ../../laws/KeyNameIsItsCharacters.bend as L5
import ../../laws/defs/AbnfGrammar.bend as D1
import ../../laws/defs/AbnfWhitespace.bend as D2
import ../../laws/defs/BareValueGrammar.bend as D3
import ../../laws/defs/BlankAndControlChars.bend as D4
import ../../laws/defs/DerivationReplay.bend as D5
import ../../laws/defs/GrammarDerivations.bend as D6
import ../../laws/defs/KeySegmentSpelling.bend as D7
import ./BareKeyChars.bend as M1
import ./BasicStringControls.bend as M2
import ./ErrorPersistence.bend as M3
import ./FailedWalkNameCompare.bend as M4
import ./HeaderKeyScan.bend as M5
import ./ValueTextReadback.bend as M6

# WP-A: blank space, comments and newlines between expressions. A state at
# rest (ap.s: no error, nothing buffered or held) in a state that passes blank
# space over stays as it is for each space or tab (ap.ws); a # there enters a
# comment, whose characters each leave it as it is (ap.cm), since a comment
# character is a control only when it is a tab (ap.cm.c9, one enumeration of
# the controls); a newline, LF or CRLF, ends the comment and the line and
# leaves the scanner at the start of the next line (ap.eol); and the end of
# the text gives the document of the rows (ap.fin).

# a scanner at rest in the lex state lx: no error, nothing buffered or held,
# past the first character
def ap.s(
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
  +ab: Bool
) -> T.St:
  T.St{"", rw, hs, he, pt, [], lx, bk, qk, sk, T.HNone{}, un, lf, ab, False{}}

# the lex states that pass a space or a tab over
def ap.wsl(+lx: T.Lex) -> Bool:
  match lx:
    case T.LTop{}:
      True{}
    case T.LLine{}:
      True{}
    case T.LKey{}:
      False{}
    case T.LKeyDot{}:
      False{}
    case T.LAfter{}:
      True{}
    case T.LKeyQ{}:
      False{}
    case T.LKeyE{}:
      False{}
    case T.LKeyU{}:
      False{}
    case T.LVal{}:
      True{}
    case T.LQ{}:
      False{}
    case T.LQ2{}:
      False{}
    case T.LStr{}:
      False{}
    case T.LEsc{}:
      False{}
    case T.LUni{}:
      False{}
    case T.LFold{}:
      False{}
    case T.LMq{}:
      False{}
    case T.LMqEnd{}:
      False{}
    case T.LTrim{}:
      False{}
    case T.LTrim2{}:
      False{}
    case T.LBare{}:
      False{}
    case T.LDate{}:
      False{}
    case T.LCom{}:
      False{}
    case T.LHead{}:
      False{}
    case T.LHeadGap{}:
      False{}
    case T.LHeadDot{}:
      False{}
    case T.LHeadQ{}:
      False{}
    case T.LHeadE{}:
      False{}
    case T.LHeadU{}:
      False{}
    case T.LHeadR{}:
      False{}
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
    case T.LSink{}:
      False{}

# the lex states a comment may follow blank space in: the start of a line,
# the rest of a line after an expression, and an array's blank space
def ap.coml(+lx: T.Lex) -> Bool:
  match lx:
    case T.LTop{}:
      True{}
    case T.LLine{}:
      True{}
    case T.LKey{}:
      False{}
    case T.LKeyDot{}:
      False{}
    case T.LAfter{}:
      False{}
    case T.LKeyQ{}:
      False{}
    case T.LKeyE{}:
      False{}
    case T.LKeyU{}:
      False{}
    case T.LVal{}:
      False{}
    case T.LQ{}:
      False{}
    case T.LQ2{}:
      False{}
    case T.LStr{}:
      False{}
    case T.LEsc{}:
      False{}
    case T.LUni{}:
      False{}
    case T.LFold{}:
      False{}
    case T.LMq{}:
      False{}
    case T.LMqEnd{}:
      False{}
    case T.LTrim{}:
      False{}
    case T.LTrim2{}:
      False{}
    case T.LBare{}:
      False{}
    case T.LDate{}:
      False{}
    case T.LCom{}:
      False{}
    case T.LHead{}:
      False{}
    case T.LHeadGap{}:
      False{}
    case T.LHeadDot{}:
      False{}
    case T.LHeadQ{}:
      False{}
    case T.LHeadE{}:
      False{}
    case T.LHeadU{}:
      False{}
    case T.LHeadR{}:
      False{}
    case T.LArr{}:
      True{}
    case T.LArrC{}:
      True{}
    case T.LInl{}:
      False{}
    case T.LInlK{}:
      False{}
    case T.LInlC{}:
      False{}
    case T.LSink{}:
      False{}

# the lex state a newline leaves: the start of the next line after a line,
# and an array's own state inside one
def ap.nlx(+lx: T.Lex) -> T.Lex:
  match lx:
    case T.LLine{}:
      T.LTop{}
    case other:
      other

# a character wschar takes is a space or a tab, by its code point
def ap.wc.go(
  +e32: Bool,
  -QQ: Char -> Type,
  +uu: U32,
  +h32: {U32.is_eq(uu, 32) == e32 : Bool},
  +hw: {Bool.or(e32, U32.is_eq(uu, 9)) == True{} : Bool},
  sp: QQ(' '),
  tab: QQ('\t')
) -> QQ(Chr{uu}):
  match e32:
    case True{}:
      %Equal.sym(U32, uu, 32, M6.s1.isk(uu, 32, h32)) : QQ(Chr{_})
      sp
    case False{}:
      %Equal.sym(U32, uu, 9, M6.s1.isk(uu, 9, hw)) : QQ(Chr{_})
      tab

# a character wschar takes is a space or a tab: a claim about both holds of it
def ap.wc(
  -QQ: Char -> Type,
  +cc: Char,
  +hw: {D2.abnf.wschar(cc) == True{} : Bool},
  sp: QQ(' '),
  tab: QQ('\t')
) -> QQ(cc):
  match cc:
    case Chr{+uu}:
      ap.wc.go(U32.is_eq(uu, 32), QQ, uu, {==}, hw, sp, tab)

# a space leaves a state that passes it over as it is
def ap.wsp(
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
  +hl: {ap.wsl(lx) == True{} : Bool}
) -> {T.doc.scan(ap.s(lx, bk, rw, hs, he, pt, qk, sk, un, lf, ab), ' ') == T.MScan{ap.s(lx, bk, rw, hs, he, pt, qk,
  sk, un, lf, ab)} : T.Mode}:
  match lx:
    case T.LTop{}:
      {==}
    case T.LLine{}:
      {==}
    case T.LKey{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LKey{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        ' ') == T.MScan{ap.s(T.LKey{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LKeyDot{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LKeyDot{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        ' ') == T.MScan{ap.s(T.LKeyDot{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LAfter{}:
      {==}
    case T.LKeyQ{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LKeyQ{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        ' ') == T.MScan{ap.s(T.LKeyQ{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LKeyE{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LKeyE{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        ' ') == T.MScan{ap.s(T.LKeyE{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LKeyU{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LKeyU{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        ' ') == T.MScan{ap.s(T.LKeyU{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LVal{}:
      {==}
    case T.LQ{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LQ{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab), ' ') == T.MScan{ap.s(T.LQ{},
        bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LQ2{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LQ2{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        ' ') == T.MScan{ap.s(T.LQ2{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LStr{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LStr{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        ' ') == T.MScan{ap.s(T.LStr{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LEsc{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LEsc{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        ' ') == T.MScan{ap.s(T.LEsc{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LUni{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LUni{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        ' ') == T.MScan{ap.s(T.LUni{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LFold{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LFold{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        ' ') == T.MScan{ap.s(T.LFold{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LMq{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LMq{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        ' ') == T.MScan{ap.s(T.LMq{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LMqEnd{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LMqEnd{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        ' ') == T.MScan{ap.s(T.LMqEnd{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LTrim{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LTrim{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        ' ') == T.MScan{ap.s(T.LTrim{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LTrim2{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LTrim2{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        ' ') == T.MScan{ap.s(T.LTrim2{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LBare{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LBare{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        ' ') == T.MScan{ap.s(T.LBare{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LDate{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LDate{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        ' ') == T.MScan{ap.s(T.LDate{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LCom{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LCom{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        ' ') == T.MScan{ap.s(T.LCom{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LHead{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LHead{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        ' ') == T.MScan{ap.s(T.LHead{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LHeadGap{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LHeadGap{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        ' ') == T.MScan{ap.s(T.LHeadGap{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LHeadDot{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LHeadDot{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        ' ') == T.MScan{ap.s(T.LHeadDot{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LHeadQ{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LHeadQ{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        ' ') == T.MScan{ap.s(T.LHeadQ{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LHeadE{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LHeadE{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        ' ') == T.MScan{ap.s(T.LHeadE{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LHeadU{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LHeadU{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        ' ') == T.MScan{ap.s(T.LHeadU{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LHeadR{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LHeadR{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        ' ') == T.MScan{ap.s(T.LHeadR{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LArr{}:
      {==}
    case T.LArrC{}:
      {==}
    case T.LInl{}:
      {==}
    case T.LInlK{}:
      {==}
    case T.LInlC{}:
      {==}
    case T.LSink{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LSink{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        ' ') == T.MScan{ap.s(T.LSink{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)

# a tab leaves a state that passes it over as it is
def ap.wtab(
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
  +hl: {ap.wsl(lx) == True{} : Bool}
) -> {T.doc.scan(ap.s(lx, bk, rw, hs, he, pt, qk, sk, un, lf, ab), '\t') == T.MScan{ap.s(lx, bk, rw, hs, he, pt, qk,
  sk, un, lf, ab)} : T.Mode}:
  match lx:
    case T.LTop{}:
      {==}
    case T.LLine{}:
      {==}
    case T.LKey{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LKey{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '\t') == T.MScan{ap.s(T.LKey{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LKeyDot{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LKeyDot{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '\t') == T.MScan{ap.s(T.LKeyDot{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LAfter{}:
      {==}
    case T.LKeyQ{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LKeyQ{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '\t') == T.MScan{ap.s(T.LKeyQ{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LKeyE{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LKeyE{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '\t') == T.MScan{ap.s(T.LKeyE{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LKeyU{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LKeyU{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '\t') == T.MScan{ap.s(T.LKeyU{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LVal{}:
      {==}
    case T.LQ{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LQ{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '\t') == T.MScan{ap.s(T.LQ{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LQ2{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LQ2{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '\t') == T.MScan{ap.s(T.LQ2{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LStr{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LStr{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '\t') == T.MScan{ap.s(T.LStr{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LEsc{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LEsc{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '\t') == T.MScan{ap.s(T.LEsc{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LUni{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LUni{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '\t') == T.MScan{ap.s(T.LUni{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LFold{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LFold{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '\t') == T.MScan{ap.s(T.LFold{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LMq{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LMq{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '\t') == T.MScan{ap.s(T.LMq{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LMqEnd{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LMqEnd{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '\t') == T.MScan{ap.s(T.LMqEnd{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LTrim{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LTrim{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '\t') == T.MScan{ap.s(T.LTrim{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LTrim2{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LTrim2{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '\t') == T.MScan{ap.s(T.LTrim2{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LBare{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LBare{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '\t') == T.MScan{ap.s(T.LBare{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LDate{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LDate{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '\t') == T.MScan{ap.s(T.LDate{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LCom{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LCom{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '\t') == T.MScan{ap.s(T.LCom{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LHead{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LHead{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '\t') == T.MScan{ap.s(T.LHead{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LHeadGap{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LHeadGap{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '\t') == T.MScan{ap.s(T.LHeadGap{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LHeadDot{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LHeadDot{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '\t') == T.MScan{ap.s(T.LHeadDot{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LHeadQ{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LHeadQ{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '\t') == T.MScan{ap.s(T.LHeadQ{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LHeadE{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LHeadE{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '\t') == T.MScan{ap.s(T.LHeadE{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LHeadU{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LHeadU{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '\t') == T.MScan{ap.s(T.LHeadU{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LHeadR{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LHeadR{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '\t') == T.MScan{ap.s(T.LHeadR{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)
    case T.LArr{}:
      {==}
    case T.LArrC{}:
      {==}
    case T.LInl{}:
      {==}
    case T.LInlK{}:
      {==}
    case T.LInlC{}:
      {==}
    case T.LSink{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LSink{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '\t') == T.MScan{ap.s(T.LSink{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode},
        hl)

# a space or a tab leaves a state that passes it over as it is
def ap.wsc(
  +lx: T.Lex,
  +cc: Char,
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
  +hl: {ap.wsl(lx) == True{} : Bool},
  +hw: {D2.abnf.wschar(cc) == True{} : Bool}
) -> {T.doc.scan(ap.s(lx, bk, rw, hs, he, pt, qk, sk, un, lf, ab), cc) == T.MScan{ap.s(lx, bk, rw, hs, he, pt, qk, sk,
  un, lf, ab)} : T.Mode}:
  ap.wc(c2 => {T.doc.scan(ap.s(lx, bk, rw, hs, he, pt, qk, sk, un, lf, ab), c2) == T.MScan{ap.s(lx, bk, rw, hs, he,
    pt, qk, sk, un, lf, ab)} : T.Mode}, cc, hw,
    ap.wsp(lx, bk, rw, hs, he, pt, qk, sk, un, lf, ab, hl), ap.wtab(lx, bk, rw, hs, he, pt, qk, sk, un, lf, ab, hl))

# blank space leaves a state that passes it over as it is
def ap.ws(
  +ww: String,
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
  +hl: {ap.wsl(lx) == True{} : Bool},
  +hw: {D2.abnf.ws(ww) == True{} : Bool}
) -> {T.doc.read(String.append(ww, rest), T.MScan{ap.s(lx, bk, rw, hs, he, pt, qk, sk, un, lf, ab)}) == T.doc.read(rest,
  T.MScan{ap.s(lx, bk, rw, hs, he, pt, qk, sk, un, lf, ab)}) : T.Doc}:
  match ww:
    case SNil{}:
      {==}
    case SCon{+hh, tt}:
      Equal.trans(T.Doc, T.doc.read(String.append(tt, rest), T.doc.scan(ap.s(lx, bk, rw, hs, he, pt, qk, sk, un, lf,
        ab), hh)),
        T.doc.read(String.append(tt, rest), T.MScan{ap.s(lx, bk, rw, hs, he, pt, qk, sk, un, lf, ab)}),
          T.doc.read(rest, T.MScan{ap.s(lx,
        bk, rw, hs, he, pt, qk, sk, un, lf, ab)}), Equal.cong(T.Mode, T.Doc, md => T.doc.read(String.append(tt, rest),
          md), T.doc.scan(ap.s(lx,
        bk, rw, hs, he, pt, qk, sk, un, lf, ab), hh), T.MScan{ap.s(lx, bk, rw, hs, he, pt, qk, sk, un, lf, ab)},
          ap.wsc(lx, hh, bk, rw, hs, he, pt, qk, sk, un, lf, ab, hl,
        Eq.and.left(D2.abnf.wschar(hh), D2.abnf.ws(tt), hw))), ap.ws(tt, rest, lx, bk, rw, hs, he, pt, qk, sk, un,
          lf, ab, hl,
        Eq.and.right(D2.abnf.wschar(hh), D2.abnf.ws(tt), hw)))

# a comment character is a control only when it is a tab: non-eol leaves out
# every control but tab and U+007F, and the prose leaves out U+007F
def ap.cm.tab(
  +uu: U32,
  +h_c: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == True{} : Bool},
  +hn: {Bool.and(D1.abnf.non_eol(Chr{uu}), D1.prose.comment_char(Chr{uu})) == True{} : Bool}
) -> {U32.is_eq(uu, 9) == True{} : Bool}:
  Eq.ctl.all(kk => {Bool.and(D1.abnf.non_eol(Chr{kk}), D1.prose.comment_char(Chr{kk})) == True{} : Bool}
    -> {U32.is_eq(kk, 9) == True{} : Bool}, uu, h_c,
    h0 => Eq.bit.absurd(&2, {U32.is_eq(0, 9) == True{} : Bool}, h0),
    h1 => Eq.bit.absurd(&2, {U32.is_eq(1, 9) == True{} : Bool}, h1),
    h2 => Eq.bit.absurd(&2, {U32.is_eq(2, 9) == True{} : Bool}, h2),
    h3 => Eq.bit.absurd(&2, {U32.is_eq(3, 9) == True{} : Bool}, h3),
    h4 => Eq.bit.absurd(&2, {U32.is_eq(4, 9) == True{} : Bool}, h4),
    h5 => Eq.bit.absurd(&2, {U32.is_eq(5, 9) == True{} : Bool}, h5),
    h6 => Eq.bit.absurd(&2, {U32.is_eq(6, 9) == True{} : Bool}, h6),
    h7 => Eq.bit.absurd(&2, {U32.is_eq(7, 9) == True{} : Bool}, h7),
    h8 => Eq.bit.absurd(&2, {U32.is_eq(8, 9) == True{} : Bool}, h8),
    _h9 => {==},
    h10 => Eq.bit.absurd(&2, {U32.is_eq(10, 9) == True{} : Bool}, h10),
    h11 => Eq.bit.absurd(&2, {U32.is_eq(11, 9) == True{} : Bool}, h11),
    h12 => Eq.bit.absurd(&2, {U32.is_eq(12, 9) == True{} : Bool}, h12),
    h13 => Eq.bit.absurd(&2, {U32.is_eq(13, 9) == True{} : Bool}, h13),
    h14 => Eq.bit.absurd(&2, {U32.is_eq(14, 9) == True{} : Bool}, h14),
    h15 => Eq.bit.absurd(&2, {U32.is_eq(15, 9) == True{} : Bool}, h15),
    h16 => Eq.bit.absurd(&2, {U32.is_eq(16, 9) == True{} : Bool}, h16),
    h17 => Eq.bit.absurd(&2, {U32.is_eq(17, 9) == True{} : Bool}, h17),
    h18 => Eq.bit.absurd(&2, {U32.is_eq(18, 9) == True{} : Bool}, h18),
    h19 => Eq.bit.absurd(&2, {U32.is_eq(19, 9) == True{} : Bool}, h19),
    h20 => Eq.bit.absurd(&2, {U32.is_eq(20, 9) == True{} : Bool}, h20),
    h21 => Eq.bit.absurd(&2, {U32.is_eq(21, 9) == True{} : Bool}, h21),
    h22 => Eq.bit.absurd(&2, {U32.is_eq(22, 9) == True{} : Bool}, h22),
    h23 => Eq.bit.absurd(&2, {U32.is_eq(23, 9) == True{} : Bool}, h23),
    h24 => Eq.bit.absurd(&2, {U32.is_eq(24, 9) == True{} : Bool}, h24),
    h25 => Eq.bit.absurd(&2, {U32.is_eq(25, 9) == True{} : Bool}, h25),
    h26 => Eq.bit.absurd(&2, {U32.is_eq(26, 9) == True{} : Bool}, h26),
    h27 => Eq.bit.absurd(&2, {U32.is_eq(27, 9) == True{} : Bool}, h27),
    h28 => Eq.bit.absurd(&2, {U32.is_eq(28, 9) == True{} : Bool}, h28),
    h29 => Eq.bit.absurd(&2, {U32.is_eq(29, 9) == True{} : Bool}, h29),
    h30 => Eq.bit.absurd(&2, {U32.is_eq(30, 9) == True{} : Bool}, h30),
    h31 => Eq.bit.absurd(&2, {U32.is_eq(31, 9) == True{} : Bool}, h31),
    h127 => Eq.bit.absurd(&2, {U32.is_eq(127, 9) == True{} : Bool}, h127))(hn)

# so a comment character is a control exactly when it is a tab
def ap.cm.c9(
  +uu: U32,
  +hn: {Bool.and(D1.abnf.non_eol(Chr{uu}), D1.prose.comment_char(Chr{uu})) == True{} : Bool}
) -> M2.s1.C9(uu):
  M2.s1.c9.go(Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), U32.is_eq(uu, 9), uu, {==}, {==},
    ec => ap.cm.tab(uu, ec, hn))

# the first halves of two ands
def ap.and2(
  +aa: Bool,
  +bb: Bool,
  +cc: Bool,
  +dd: Bool,
  +ha: {Bool.and(aa, bb) == True{} : Bool},
  +hc: {Bool.and(cc, dd) == True{} : Bool}
) -> {Bool.and(aa, cc) == True{} : Bool}:
  match aa cc:
    case True{} True{}:
      {==}
    case False{} _c:
      Eq.bit.absurd(&2, {Bool.and(False{}, _c) == True{} : Bool}, ha)
    case True{} False{}:
      Eq.bit.absurd(&2, {Bool.and(True{}, False{}) == True{} : Bool}, hc)

# a comment character's fast step leaves the comment as it is: a tab goes to
# the full step, which passes it over, and anything else stays in LCom
def ap.cm.f9(
  +t9: Bool,
  +uu: U32,
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
  +e9: {U32.is_eq(uu, 9) == t9 : Bool}
) -> {T.read.fast.com(t9, "", rw, hs, he, pt, [], bk, qk, sk, un, lf, ab, Chr{uu}) == ap.s(T.LCom{}, bk, rw, hs, he,
  pt, qk, sk, un, lf, ab)
  : T.St}:
  match t9:
    case True{}:
      %Equal.sym(U32, uu, 9, M2.s1.is9(uu, e9)) : {T.read.fast.com(True{}, "", rw, hs, he, pt, [], bk, qk, sk, un, lf,
          ab,
        Chr{_}) == ap.s(T.LCom{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab) : T.St}
      {==}
    case False{}:
      {==}

# a comment character's fast step leaves the comment as it is
def ap.cm.fast(
  +uu: U32,
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
  +hn: {Bool.and(D1.abnf.non_eol(Chr{uu}), D1.prose.comment_char(Chr{uu})) == True{} : Bool}
) -> {T.read.fast(ap.s(T.LCom{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab), Chr{uu}) == ap.s(T.LCom{}, bk, rw, hs, he,
  pt, qk, sk, un, lf, ab) : T.St}:
  %Equal.sym(Bool, Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), U32.is_eq(uu, 9), ap.cm.c9(uu, hn))
    : {T.read.fast.com(_, "", rw, hs, he, pt, [], bk, qk, sk, un, lf, ab, Chr{uu}) == ap.s(T.LCom{}, bk, rw, hs, he,
      pt, qk, sk, un, lf, ab)
    : T.St}
  ap.cm.f9(U32.is_eq(uu, 9), uu, bk, rw, hs, he, pt, qk, sk, un, lf, ab, {==})

# a comment character's fast step leaves the comment as it is
def ap.cmf(
  +uu: U32,
  +bk: T.Lex,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool
) -> Data:
  {T.read.fast(ap.s(T.LCom{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab), Chr{uu}) == ap.s(T.LCom{}, bk, rw, hs, he, pt,
    qk, sk, un, lf, ab) : T.St}

# a character that is a control exactly when a tab is no carriage return
def ap.nocr(
  +uu: U32,
  h9: M2.s1.C9(uu),
  +e13: {U32.is_eq(uu, 13) == True{} : Bool}
) -> Empty:
  Eq.bit.clash2(Equal.trans(Bool, True{}, U32.is_eq(uu, 9), False{}, Equal.trans(Bool, True{}, Bool.or(U32.is_lt(uu,
    32), U32.is_eq(uu, 127)), U32.is_eq(uu, 9), Equal.cong(U32, Bool, nn => Bool.or(U32.is_lt(nn, 32), U32.is_eq(nn,
    127)), 13, uu, Equal.sym(U32, uu, 13, M6.s1.isk(uu, 13, e13))), h9), Equal.cong(U32, Bool, nn => U32.is_eq(nn, 9),
    uu, 13, M6.s1.isk(uu, 13, e13))))

# a comment character leaves the comment as it is, whichever way doc.scan
# takes it
def ap.cm.scan(
  +dq: Bool,
  +sq: Bool,
  +cr: Bool,
  +uu: U32,
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
  +ecr: {U32.is_eq(uu, 13) == cr : Bool},
  h9: M2.s1.C9(uu),
  +ef: ap.cmf(uu, bk, rw, hs, he, pt, qk, sk, un, lf, ab)
) -> {T.doc.scan.q(dq, sq, cr, ap.s(T.LCom{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
  Chr{uu}) == T.MScan{ap.s(T.LCom{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)}
  : T.Mode}:
  match dq:
    case True{}:
      %Equal.sym(T.St, T.read.fast(ap.s(T.LCom{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab), Chr{uu}), ap.s(T.LCom{},
        bk, rw, hs, he, pt, qk, sk, un, lf, ab), ef)
        : {T.doc.wrap(_) == T.MScan{ap.s(T.LCom{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode}
      {==}
    case False{}:
      match sq:
        case True{}:
          %Equal.sym(T.St, T.read.fast(ap.s(T.LCom{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab), Chr{uu}),
            ap.s(T.LCom{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab), ef)
            : {T.doc.wrap(_) == T.MScan{ap.s(T.LCom{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode}
          {==}
        case False{}:
          match cr:
            case True{}:
              Eq.bit.gone(&2, {T.doc.scan.cr(True{}, ap.s(T.LCom{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
                Chr{uu}) == T.MScan{ap.s(T.LCom{},
                bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode}, ap.nocr(uu, h9, ecr))
            case False{}:
              %Equal.sym(T.St, T.read.fast(ap.s(T.LCom{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab), Chr{uu}),
                ap.s(T.LCom{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
                ef) : {T.MScan{_} == T.MScan{ap.s(T.LCom{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)} : T.Mode}
              {==}

# a comment character leaves the comment as it is
def ap.cmc(
  +cc: Char,
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
  +hn: {Bool.and(D1.abnf.non_eol(cc), D1.prose.comment_char(cc)) == True{} : Bool}
) -> {T.doc.scan(ap.s(T.LCom{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab), cc) == T.MScan{ap.s(T.LCom{}, bk, rw, hs, he,
  pt, qk, sk, un, lf, ab)} : T.Mode}:
  match cc:
    case Chr{+uu}:
      ap.cm.scan(Char.is_eq(Chr{uu}, '"'), Char.is_eq(Chr{uu}, '\''), U32.is_eq(uu, 13), uu, bk, rw, hs, he, pt, qk,
        sk, un, lf, ab, {==},
        ap.cm.c9(uu, hn), ap.cm.fast(uu, bk, rw, hs, he, pt, qk, sk, un, lf, ab, hn))

# a comment's characters leave the comment as it is
def ap.cm(
  +body: String,
  +rest: String,
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
  +hc: {D1.abnf.comment(body) == True{} : Bool},
  +hp: {D1.prose.comment_chars(body) == True{} : Bool}
) -> {T.doc.read(String.append(body, rest), T.MScan{ap.s(T.LCom{}, bk, rw, hs, he, pt, qk, sk, un, lf,
  ab)}) == T.doc.read(rest,
  T.MScan{ap.s(T.LCom{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)}) : T.Doc}:
  match body:
    case SNil{}:
      {==}
    case SCon{+hh, tt}:
      Equal.trans(T.Doc, T.doc.read(String.append(tt, rest), T.doc.scan(ap.s(T.LCom{}, bk, rw, hs, he, pt, qk, sk, un,
        lf, ab), hh)),
        T.doc.read(String.append(tt, rest), T.MScan{ap.s(T.LCom{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)}),
          T.doc.read(rest,
        T.MScan{ap.s(T.LCom{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab)}), Equal.cong(T.Mode, T.Doc,
          md => T.doc.read(String.append(tt, rest), md),
        T.doc.scan(ap.s(T.LCom{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab), hh), T.MScan{ap.s(T.LCom{}, bk, rw, hs, he,
          pt, qk, sk, un, lf, ab)}, ap.cmc(hh, bk, rw, hs, he, pt, qk, sk, un, lf, ab,
        ap.and2(D1.abnf.non_eol(hh), D1.abnf.comment(tt), D1.prose.comment_char(hh), D1.prose.comment_chars(tt),
        hc, hp))), ap.cm(tt, rest, bk, rw, hs, he, pt, qk, sk, un, lf, ab, Eq.and.right(D1.abnf.non_eol(hh),
          D1.abnf.comment(tt), hc),
        Eq.and.right(D1.prose.comment_char(hh), D1.prose.comment_chars(tt), hp)))

# a # enters a comment that returns to the state it interrupted
def ap.hash(
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
  +hl: {ap.coml(lx) == True{} : Bool}
) -> {T.doc.scan(ap.s(lx, bk, rw, hs, he, pt, qk, sk, un, lf, ab), '#') == T.MScan{ap.s(T.LCom{}, lx, rw, hs, he, pt,
  qk, sk, un, lf, ab)} : T.Mode}:
  match lx:
    case T.LTop{}:
      {==}
    case T.LLine{}:
      {==}
    case T.LKey{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LKey{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '#') == T.MScan{ap.s(T.LCom{}, T.LKey{}, rw, hs, he, pt, qk, sk, un, lf, ab)}
        : T.Mode}, hl)
    case T.LKeyDot{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LKeyDot{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '#') == T.MScan{ap.s(T.LCom{}, T.LKeyDot{}, rw, hs, he, pt, qk, sk, un, lf, ab)}
        : T.Mode}, hl)
    case T.LAfter{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LAfter{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '#') == T.MScan{ap.s(T.LCom{}, T.LAfter{}, rw, hs, he, pt, qk, sk, un, lf, ab)}
        : T.Mode}, hl)
    case T.LKeyQ{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LKeyQ{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '#') == T.MScan{ap.s(T.LCom{}, T.LKeyQ{}, rw, hs, he, pt, qk, sk, un, lf, ab)}
        : T.Mode}, hl)
    case T.LKeyE{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LKeyE{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '#') == T.MScan{ap.s(T.LCom{}, T.LKeyE{}, rw, hs, he, pt, qk, sk, un, lf, ab)}
        : T.Mode}, hl)
    case T.LKeyU{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LKeyU{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '#') == T.MScan{ap.s(T.LCom{}, T.LKeyU{}, rw, hs, he, pt, qk, sk, un, lf, ab)}
        : T.Mode}, hl)
    case T.LVal{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LVal{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '#') == T.MScan{ap.s(T.LCom{}, T.LVal{}, rw, hs, he, pt, qk, sk, un, lf, ab)}
        : T.Mode}, hl)
    case T.LQ{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LQ{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '#') == T.MScan{ap.s(T.LCom{}, T.LQ{}, rw, hs, he, pt, qk, sk, un, lf, ab)}
        : T.Mode}, hl)
    case T.LQ2{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LQ2{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '#') == T.MScan{ap.s(T.LCom{}, T.LQ2{}, rw, hs, he, pt, qk, sk, un, lf, ab)}
        : T.Mode}, hl)
    case T.LStr{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LStr{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '#') == T.MScan{ap.s(T.LCom{}, T.LStr{}, rw, hs, he, pt, qk, sk, un, lf, ab)}
        : T.Mode}, hl)
    case T.LEsc{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LEsc{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '#') == T.MScan{ap.s(T.LCom{}, T.LEsc{}, rw, hs, he, pt, qk, sk, un, lf, ab)}
        : T.Mode}, hl)
    case T.LUni{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LUni{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '#') == T.MScan{ap.s(T.LCom{}, T.LUni{}, rw, hs, he, pt, qk, sk, un, lf, ab)}
        : T.Mode}, hl)
    case T.LFold{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LFold{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '#') == T.MScan{ap.s(T.LCom{}, T.LFold{}, rw, hs, he, pt, qk, sk, un, lf, ab)}
        : T.Mode}, hl)
    case T.LMq{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LMq{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '#') == T.MScan{ap.s(T.LCom{}, T.LMq{}, rw, hs, he, pt, qk, sk, un, lf, ab)}
        : T.Mode}, hl)
    case T.LMqEnd{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LMqEnd{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '#') == T.MScan{ap.s(T.LCom{}, T.LMqEnd{}, rw, hs, he, pt, qk, sk, un, lf, ab)}
        : T.Mode}, hl)
    case T.LTrim{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LTrim{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '#') == T.MScan{ap.s(T.LCom{}, T.LTrim{}, rw, hs, he, pt, qk, sk, un, lf, ab)}
        : T.Mode}, hl)
    case T.LTrim2{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LTrim2{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '#') == T.MScan{ap.s(T.LCom{}, T.LTrim2{}, rw, hs, he, pt, qk, sk, un, lf, ab)}
        : T.Mode}, hl)
    case T.LBare{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LBare{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '#') == T.MScan{ap.s(T.LCom{}, T.LBare{}, rw, hs, he, pt, qk, sk, un, lf, ab)}
        : T.Mode}, hl)
    case T.LDate{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LDate{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '#') == T.MScan{ap.s(T.LCom{}, T.LDate{}, rw, hs, he, pt, qk, sk, un, lf, ab)}
        : T.Mode}, hl)
    case T.LCom{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LCom{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '#') == T.MScan{ap.s(T.LCom{}, T.LCom{}, rw, hs, he, pt, qk, sk, un, lf, ab)}
        : T.Mode}, hl)
    case T.LHead{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LHead{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '#') == T.MScan{ap.s(T.LCom{}, T.LHead{}, rw, hs, he, pt, qk, sk, un, lf, ab)}
        : T.Mode}, hl)
    case T.LHeadGap{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LHeadGap{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '#') == T.MScan{ap.s(T.LCom{}, T.LHeadGap{}, rw, hs, he, pt, qk, sk, un, lf, ab)}
        : T.Mode}, hl)
    case T.LHeadDot{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LHeadDot{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '#') == T.MScan{ap.s(T.LCom{}, T.LHeadDot{}, rw, hs, he, pt, qk, sk, un, lf, ab)}
        : T.Mode}, hl)
    case T.LHeadQ{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LHeadQ{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '#') == T.MScan{ap.s(T.LCom{}, T.LHeadQ{}, rw, hs, he, pt, qk, sk, un, lf, ab)}
        : T.Mode}, hl)
    case T.LHeadE{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LHeadE{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '#') == T.MScan{ap.s(T.LCom{}, T.LHeadE{}, rw, hs, he, pt, qk, sk, un, lf, ab)}
        : T.Mode}, hl)
    case T.LHeadU{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LHeadU{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '#') == T.MScan{ap.s(T.LCom{}, T.LHeadU{}, rw, hs, he, pt, qk, sk, un, lf, ab)}
        : T.Mode}, hl)
    case T.LHeadR{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LHeadR{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '#') == T.MScan{ap.s(T.LCom{}, T.LHeadR{}, rw, hs, he, pt, qk, sk, un, lf, ab)}
        : T.Mode}, hl)
    case T.LArr{}:
      {==}
    case T.LArrC{}:
      {==}
    case T.LInl{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LInl{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '#') == T.MScan{ap.s(T.LCom{}, T.LInl{}, rw, hs, he, pt, qk, sk, un, lf, ab)}
        : T.Mode}, hl)
    case T.LInlK{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LInlK{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '#') == T.MScan{ap.s(T.LCom{}, T.LInlK{}, rw, hs, he, pt, qk, sk, un, lf, ab)}
        : T.Mode}, hl)
    case T.LInlC{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LInlC{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '#') == T.MScan{ap.s(T.LCom{}, T.LInlC{}, rw, hs, he, pt, qk, sk, un, lf, ab)}
        : T.Mode}, hl)
    case T.LSink{}:
      Eq.bit.absurd(&2, {T.doc.scan(ap.s(T.LSink{}, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '#') == T.MScan{ap.s(T.LCom{}, T.LSink{}, rw, hs, he, pt, qk, sk, un, lf, ab)}
        : T.Mode}, hl)

# what a [ comment ] leaves the scanner in: the state it follows, or the
# comment, which returns to that state
def ap.aft(
  +com: D6.GCom,
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
  +ab: Bool
) -> T.St:
  match com:
    case D6.GcNone{}:
      ap.s(lx, bk, rw, hs, he, pt, qk, sk, un, lf, ab)
    case D6.GcSome{_body}:
      ap.s(T.LCom{}, lx, rw, hs, he, pt, qk, sk, un, lf, ab)

# the back state after a [ comment ] and its newline
def ap.abk(+com: D6.GCom, +lx: T.Lex, +bk: T.Lex) -> T.Lex:
  match com:
    case D6.GcNone{}:
      bk
    case D6.GcSome{_body}:
      lx

# a comment, from a state it may follow, leaves the scanner in ap.aft
def ap.tail2(
  +com: D6.GCom,
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
  +hm: {ap.coml(lx) == True{} : Bool},
  +hc: {D1.g.ok.com(com) == True{} : Bool}
) -> {T.doc.read(D6.g.com.text(com, rest), T.MScan{ap.s(lx, bk, rw, hs, he, pt, qk, sk, un, lf, ab)})
  == T.doc.read(rest, T.MScan{ap.aft(com, lx, bk, rw, hs, he, pt, qk, sk, un, lf, ab)}) : T.Doc}:
  match com:
    case D6.GcNone{}:
      {==}
    case D6.GcSome{+body}:
      Equal.trans(T.Doc, T.doc.read(String.append(body, rest), T.doc.scan(ap.s(lx, bk, rw, hs, he, pt, qk, sk, un, lf,
        ab),
        '#')), T.doc.read(String.append(body, rest), T.MScan{ap.s(T.LCom{}, lx, rw, hs, he, pt, qk, sk, un, lf, ab)}),
        T.doc.read(rest, T.MScan{ap.s(T.LCom{}, lx, rw, hs, he, pt, qk, sk, un, lf, ab)}), Equal.cong(T.Mode, T.Doc,
        md => T.doc.read(String.append(body, rest), md), T.doc.scan(ap.s(lx, bk, rw, hs, he, pt, qk, sk, un, lf, ab),
        '#'), T.MScan{ap.s(T.LCom{}, lx, rw, hs, he, pt, qk, sk, un, lf, ab)}, ap.hash(lx, bk, rw, hs, he, pt, qk, sk,
          un,
        lf, ab, hm)), ap.cm(body, rest, lx, rw, hs, he, pt, qk, sk, un, lf, ab, Eq.and.left(D1.abnf.comment(body),
        D1.prose.comment_chars(body), hc), Eq.and.right(D1.abnf.comment(body), D1.prose.comment_chars(body), hc)))

# blank space and a comment, from a state they may follow, leave the scanner
# in ap.aft
def ap.tail(
  +ww: String,
  +com: D6.GCom,
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
  +hl: {ap.wsl(lx) == True{} : Bool},
  +hm: {ap.coml(lx) == True{} : Bool},
  +hw: {D2.abnf.ws(ww) == True{} : Bool},
  +hc: {D1.g.ok.com(com) == True{} : Bool}
) -> {T.doc.read(String.append(ww, D6.g.com.text(com, rest)), T.MScan{ap.s(lx, bk, rw, hs, he, pt, qk, sk, un, lf,
  ab)}) == T.doc.read(rest, T.MScan{ap.aft(com, lx, bk, rw, hs, he, pt, qk, sk, un, lf, ab)}) : T.Doc}:
  Equal.trans(T.Doc, T.doc.read(String.append(ww, D6.g.com.text(com, rest)), T.MScan{ap.s(lx, bk, rw, hs, he, pt, qk,
    sk, un, lf, ab)}), T.doc.read(D6.g.com.text(com, rest), T.MScan{ap.s(lx, bk, rw, hs, he, pt, qk, sk, un, lf,
    ab)}), T.doc.read(rest, T.MScan{ap.aft(com, lx, bk, rw, hs, he, pt, qk, sk, un, lf, ab)}), ap.ws(ww,
    D6.g.com.text(com, rest), lx, bk, rw, hs, he, pt, qk, sk, un, lf, ab, hl, hw), ap.tail2(com, rest, lx, bk, rw,
    hs, he, pt, qk, sk, un, lf, ab, hm, hc))

# the lex states a comment may follow, each: a claim about the four holds of
# every such state
def ap.coml.elim(
  -QQ: T.Lex -> Type,
  +lx: T.Lex,
  +hl: {ap.coml(lx) == True{} : Bool},
  top: QQ(T.LTop{}),
  line: QQ(T.LLine{}),
  arr: QQ(T.LArr{}),
  arrc: QQ(T.LArrC{})
) -> QQ(lx):
  match lx:
    case T.LTop{}:
      top
    case T.LLine{}:
      line
    case T.LKey{}:
      Eq.bit.absurd(&1, QQ(T.LKey{}), hl)
    case T.LKeyDot{}:
      Eq.bit.absurd(&1, QQ(T.LKeyDot{}), hl)
    case T.LAfter{}:
      Eq.bit.absurd(&1, QQ(T.LAfter{}), hl)
    case T.LKeyQ{}:
      Eq.bit.absurd(&1, QQ(T.LKeyQ{}), hl)
    case T.LKeyE{}:
      Eq.bit.absurd(&1, QQ(T.LKeyE{}), hl)
    case T.LKeyU{}:
      Eq.bit.absurd(&1, QQ(T.LKeyU{}), hl)
    case T.LVal{}:
      Eq.bit.absurd(&1, QQ(T.LVal{}), hl)
    case T.LQ{}:
      Eq.bit.absurd(&1, QQ(T.LQ{}), hl)
    case T.LQ2{}:
      Eq.bit.absurd(&1, QQ(T.LQ2{}), hl)
    case T.LStr{}:
      Eq.bit.absurd(&1, QQ(T.LStr{}), hl)
    case T.LEsc{}:
      Eq.bit.absurd(&1, QQ(T.LEsc{}), hl)
    case T.LUni{}:
      Eq.bit.absurd(&1, QQ(T.LUni{}), hl)
    case T.LFold{}:
      Eq.bit.absurd(&1, QQ(T.LFold{}), hl)
    case T.LMq{}:
      Eq.bit.absurd(&1, QQ(T.LMq{}), hl)
    case T.LMqEnd{}:
      Eq.bit.absurd(&1, QQ(T.LMqEnd{}), hl)
    case T.LTrim{}:
      Eq.bit.absurd(&1, QQ(T.LTrim{}), hl)
    case T.LTrim2{}:
      Eq.bit.absurd(&1, QQ(T.LTrim2{}), hl)
    case T.LBare{}:
      Eq.bit.absurd(&1, QQ(T.LBare{}), hl)
    case T.LDate{}:
      Eq.bit.absurd(&1, QQ(T.LDate{}), hl)
    case T.LCom{}:
      Eq.bit.absurd(&1, QQ(T.LCom{}), hl)
    case T.LHead{}:
      Eq.bit.absurd(&1, QQ(T.LHead{}), hl)
    case T.LHeadGap{}:
      Eq.bit.absurd(&1, QQ(T.LHeadGap{}), hl)
    case T.LHeadDot{}:
      Eq.bit.absurd(&1, QQ(T.LHeadDot{}), hl)
    case T.LHeadQ{}:
      Eq.bit.absurd(&1, QQ(T.LHeadQ{}), hl)
    case T.LHeadE{}:
      Eq.bit.absurd(&1, QQ(T.LHeadE{}), hl)
    case T.LHeadU{}:
      Eq.bit.absurd(&1, QQ(T.LHeadU{}), hl)
    case T.LHeadR{}:
      Eq.bit.absurd(&1, QQ(T.LHeadR{}), hl)
    case T.LArr{}:
      arr
    case T.LArrC{}:
      arrc
    case T.LInl{}:
      Eq.bit.absurd(&1, QQ(T.LInl{}), hl)
    case T.LInlK{}:
      Eq.bit.absurd(&1, QQ(T.LInlK{}), hl)
    case T.LInlC{}:
      Eq.bit.absurd(&1, QQ(T.LInlC{}), hl)
    case T.LSink{}:
      Eq.bit.absurd(&1, QQ(T.LSink{}), hl)

# a newline read after a [ comment ]: the text reads on as the rest from the
# state the newline leaves, back where the comment returned
def ap.Eol(
  +com: D6.GCom,
  +lx: T.Lex,
  +nl: String,
  +rest: String,
  +bk: T.Lex,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool
) -> Type:
  {T.doc.read(String.append(nl, rest), T.MScan{ap.aft(com, lx, bk, rw, hs, he, pt, qk, sk, un, lf, ab)})
    == T.doc.read(rest, T.MScan{ap.s(ap.nlx(lx), ap.abk(com, lx, bk), rw, hs, he, pt, qk, sk, un, lf, ab)}) : T.Doc}

# a line feed after a [ comment ] leaves the scanner where the next line, or
# the array's next part, starts
def ap.eol.lf(
  +com: D6.GCom,
  +lx: T.Lex,
  +rest: String,
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
  +hl: {ap.coml(lx) == True{} : Bool}
) -> ap.Eol(com, lx, "\n", rest, bk, rw, hs, he, pt, qk, sk, un, lf, ab):
  match com:
    case D6.GcNone{}:
      ap.coml.elim(l2 => ap.Eol(D6.GcNone{}, l2, "\n", rest, bk, rw, hs, he, pt, qk, sk, un, lf, ab), lx, hl, {==},
        {==}, {==}, {==})
    case D6.GcSome{bd}:
      ap.coml.elim(l2 => ap.Eol(D6.GcSome{bd}, l2, "\n", rest, bk, rw, hs, he, pt, qk, sk, un, lf, ab), lx, hl, {==},
        {==}, {==}, {==})

# and so does a carriage return and a line feed
def ap.eol.crlf(
  +com: D6.GCom,
  +lx: T.Lex,
  +rest: String,
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
  +hl: {ap.coml(lx) == True{} : Bool}
) -> ap.Eol(com, lx, "\r\n", rest, bk, rw, hs, he, pt, qk, sk, un, lf, ab):
  match com:
    case D6.GcNone{}:
      ap.coml.elim(l2 => ap.Eol(D6.GcNone{}, l2, "\r\n", rest, bk, rw, hs, he, pt, qk, sk, un, lf, ab), lx, hl, {==},
        {==}, {==}, {==})
    case D6.GcSome{bd}:
      ap.coml.elim(l2 => ap.Eol(D6.GcSome{bd}, l2, "\r\n", rest, bk, rw, hs, he, pt, qk, sk, un, lf, ab), lx, hl,
        {==}, {==}, {==}, {==})

# a newline after a [ comment ] leaves the scanner where the next line, or
# the array's next part, starts: in the state a newline leaves, back where
# the comment returned
def ap.eol(
  +com: D6.GCom,
  +lx: T.Lex,
  +nl: String,
  +rest: String,
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
  +hl: {ap.coml(lx) == True{} : Bool},
  +hn: {D1.abnf.newline(nl) == True{} : Bool}
) -> ap.Eol(com, lx, nl, rest, bk, rw, hs, he, pt, qk, sk, un, lf, ab):
  M2.s1.nl.elim(n2 => ap.Eol(com, lx, n2, rest, bk, rw, hs, he, pt, qk, sk, un, lf, ab), nl, hn, ap.eol.lf(com, lx,
      rest,
    bk, rw, hs, he, pt, qk, sk, un, lf, ab, hl), ap.eol.crlf(com, lx, rest, bk, rw, hs, he, pt, qk, sk, un, lf, ab, hl))

# the states a document may end in after an expression: the start of a line
# and the rest of one
def ap.tll(+lx: T.Lex) -> Bool:
  match lx:
    case T.LTop{}:
      True{}
    case T.LLine{}:
      True{}
    case T.LKey{}:
      False{}
    case T.LKeyDot{}:
      False{}
    case T.LAfter{}:
      False{}
    case T.LKeyQ{}:
      False{}
    case T.LKeyE{}:
      False{}
    case T.LKeyU{}:
      False{}
    case T.LVal{}:
      False{}
    case T.LQ{}:
      False{}
    case T.LQ2{}:
      False{}
    case T.LStr{}:
      False{}
    case T.LEsc{}:
      False{}
    case T.LUni{}:
      False{}
    case T.LFold{}:
      False{}
    case T.LMq{}:
      False{}
    case T.LMqEnd{}:
      False{}
    case T.LTrim{}:
      False{}
    case T.LTrim2{}:
      False{}
    case T.LBare{}:
      False{}
    case T.LDate{}:
      False{}
    case T.LCom{}:
      False{}
    case T.LHead{}:
      False{}
    case T.LHeadGap{}:
      False{}
    case T.LHeadDot{}:
      False{}
    case T.LHeadQ{}:
      False{}
    case T.LHeadE{}:
      False{}
    case T.LHeadU{}:
      False{}
    case T.LHeadR{}:
      False{}
    case T.LArr{}:
      False{}
    case T.LArrC{}:
      False{}
    case T.LInl{}:
      False{}
    case T.LInlK{}:
      False{}
    case T.LInlC{}:
      False{}
    case T.LSink{}:
      False{}

# the two states: a claim about both holds of every such state
def ap.tll.elim(
  -QQ: T.Lex -> Type,
  +lx: T.Lex,
  +hl: {ap.tll(lx) == True{} : Bool},
  top: QQ(T.LTop{}),
  line: QQ(T.LLine{})
) -> QQ(lx):
  match lx:
    case T.LTop{}:
      top
    case T.LLine{}:
      line
    case T.LKey{}:
      Eq.bit.absurd(&1, QQ(T.LKey{}), hl)
    case T.LKeyDot{}:
      Eq.bit.absurd(&1, QQ(T.LKeyDot{}), hl)
    case T.LAfter{}:
      Eq.bit.absurd(&1, QQ(T.LAfter{}), hl)
    case T.LKeyQ{}:
      Eq.bit.absurd(&1, QQ(T.LKeyQ{}), hl)
    case T.LKeyE{}:
      Eq.bit.absurd(&1, QQ(T.LKeyE{}), hl)
    case T.LKeyU{}:
      Eq.bit.absurd(&1, QQ(T.LKeyU{}), hl)
    case T.LVal{}:
      Eq.bit.absurd(&1, QQ(T.LVal{}), hl)
    case T.LQ{}:
      Eq.bit.absurd(&1, QQ(T.LQ{}), hl)
    case T.LQ2{}:
      Eq.bit.absurd(&1, QQ(T.LQ2{}), hl)
    case T.LStr{}:
      Eq.bit.absurd(&1, QQ(T.LStr{}), hl)
    case T.LEsc{}:
      Eq.bit.absurd(&1, QQ(T.LEsc{}), hl)
    case T.LUni{}:
      Eq.bit.absurd(&1, QQ(T.LUni{}), hl)
    case T.LFold{}:
      Eq.bit.absurd(&1, QQ(T.LFold{}), hl)
    case T.LMq{}:
      Eq.bit.absurd(&1, QQ(T.LMq{}), hl)
    case T.LMqEnd{}:
      Eq.bit.absurd(&1, QQ(T.LMqEnd{}), hl)
    case T.LTrim{}:
      Eq.bit.absurd(&1, QQ(T.LTrim{}), hl)
    case T.LTrim2{}:
      Eq.bit.absurd(&1, QQ(T.LTrim2{}), hl)
    case T.LBare{}:
      Eq.bit.absurd(&1, QQ(T.LBare{}), hl)
    case T.LDate{}:
      Eq.bit.absurd(&1, QQ(T.LDate{}), hl)
    case T.LCom{}:
      Eq.bit.absurd(&1, QQ(T.LCom{}), hl)
    case T.LHead{}:
      Eq.bit.absurd(&1, QQ(T.LHead{}), hl)
    case T.LHeadGap{}:
      Eq.bit.absurd(&1, QQ(T.LHeadGap{}), hl)
    case T.LHeadDot{}:
      Eq.bit.absurd(&1, QQ(T.LHeadDot{}), hl)
    case T.LHeadQ{}:
      Eq.bit.absurd(&1, QQ(T.LHeadQ{}), hl)
    case T.LHeadE{}:
      Eq.bit.absurd(&1, QQ(T.LHeadE{}), hl)
    case T.LHeadU{}:
      Eq.bit.absurd(&1, QQ(T.LHeadU{}), hl)
    case T.LHeadR{}:
      Eq.bit.absurd(&1, QQ(T.LHeadR{}), hl)
    case T.LArr{}:
      Eq.bit.absurd(&1, QQ(T.LArr{}), hl)
    case T.LArrC{}:
      Eq.bit.absurd(&1, QQ(T.LArrC{}), hl)
    case T.LInl{}:
      Eq.bit.absurd(&1, QQ(T.LInl{}), hl)
    case T.LInlK{}:
      Eq.bit.absurd(&1, QQ(T.LInlK{}), hl)
    case T.LInlC{}:
      Eq.bit.absurd(&1, QQ(T.LInlC{}), hl)
    case T.LSink{}:
      Eq.bit.absurd(&1, QQ(T.LSink{}), hl)

# the end of the text after a [ comment ] at the top level gives the
# document of the rows, with no error
def ap.fin(
  +com: D6.GCom,
  +lx: T.Lex,
  +bk: T.Lex,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +hl: {ap.tll(lx) == True{} : Bool}
) -> {T.doc.read("", T.MScan{ap.aft(com, lx, bk, rw, hs, he, pt, qk, [], un, lf, ab)}) == T.Doc{"", T.rows.seal(rw)}
  : T.Doc}:
  match com:
    case D6.GcNone{}:
      ap.tll.elim(l2 => {T.doc.read("", T.MScan{ap.aft(D6.GcNone{}, l2, bk, rw, hs, he, pt, qk, [], un, lf, ab)})
        == T.Doc{"", T.rows.seal(rw)} : T.Doc}, lx, hl, {==}, {==})
    case D6.GcSome{bd}:
      ap.tll.elim(l2 => {T.doc.read("", T.MScan{ap.aft(D6.GcSome{bd}, l2, bk, rw, hs, he, pt, qk, [], un, lf, ab)})
        == T.Doc{"", T.rows.seal(rw)} : T.Doc}, lx, hl, {==}, {==})

# WP-A: a header however its walk ends. KEY-3's header reader (k3.hcore)
# reads a header whose walk succeeds; the same reading (k3.hlead, k3.hkeys)
# ends at the bracket in a walk that may fail as well (ap.hend), and the
# scanner reads on with the walk's error, rows and definitions. A header of
# the grammar (GTable) is one of KEY-3's (ap.dots and ap.last spell its key
# as KEY-3's KDot list and last segment, ap.gs its blank space as gap).

# the scanner after a header in its table, with the error, rows and
# definitions its walk returned
def ap.ln(
  +bd: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32
) -> T.St:
  T.St{bd, rows, heads, here, [], [], T.LLine{}, bk, qk, [], T.HNone{}, un, lf, False{}, False{}}

# a header's walk from the root, with what it returns
def ap.Wk(
  +path: List<&2, String>,
  +rw: List<&2, T.Val>,
  +job: T.Job,
  +hs: List<&2, String>,
  +en: T.End
) -> Data:
  {T.tree.walk(path, T.Tw{rw, job, [], "", "", hs, False{}}, 0) == en : T.End}

# the bracket runs the header's walk along the segments read, whatever it
# returns, and leaves the scanner in the header's table
def ap.hend(
  +ab: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +parts: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +path: List<&2, String>,
  +rows2: List<&2, T.Val>,
  +bd2: String,
  +heads2: List<&2, String>,
  +rest: String,
  +ne: {List.is_empty(&2, String, parts) == False{} : Bool},
  +er: {List.reverse(&2, String, parts) == path : List<&2, String>},
  +ew: ap.Wk(path, rw, D3.header_job(ab), hs, T.End{rows2, bd2, heads2})
) -> {T.doc.read(rest, T.MScan{ap.ln(bd2, rows2, heads2, path, bk, qk, un, lf)}) == T.doc.read(M5.k3.htail(ab, rest),
  T.MScan{M5.k3.haft(True{}, rw, hs, he, parts, bk, qk, un, lf, ab)}) : T.Doc}:
  match ab:
    case False{}:
      %Equal.sym(Bool, List.is_empty(&2, String, parts), False{}, ne) : {T.doc.read(rest,
        T.MScan{ap.ln(bd2, rows2, heads2, path, bk, qk, un, lf)}) == T.doc.read(rest, T.MScan{T.read.once2(T.head.go(_,
        M5.k3.w(rw, hs, he, parts, [], T.LHeadGap{}, bk, qk, [], un, lf, False{}), List.reverse(&2, String, parts)))})
        : T.Doc}
      %Equal.sym(List<&2, String>, List.reverse(&2, String, parts), path, er) : {T.doc.read(rest,
        T.MScan{ap.ln(bd2, rows2, heads2, path, bk, qk, un, lf)}) == T.doc.read(rest,
        T.MScan{T.read.once2(T.head.apply(T.tree.walk(_, T.Tw{rw, T.JDef{}, [], "", "", hs, False{}}, 0), _, bk, qk,
        un, lf, False{}))}) : T.Doc}
      %Equal.sym(T.End, T.tree.walk(path, T.Tw{rw, T.JDef{}, [], "", "", hs, False{}}, 0), T.End{rows2, bd2, heads2},
        ew) : {T.doc.read(rest, T.MScan{ap.ln(bd2, rows2, heads2, path, bk, qk, un, lf)}) == T.doc.read(rest,
        T.MScan{T.read.once2(T.head.apply(_, path, bk, qk, un, lf, False{}))}) : T.Doc}
      {==}
    case True{}:
      %Equal.sym(Bool, List.is_empty(&2, String, parts), False{}, ne) : {T.doc.read(rest,
        T.MScan{ap.ln(bd2, rows2, heads2, path, bk, qk, un, lf)}) == T.doc.read(rest, T.MScan{T.read.once2(T.head.go(_,
        M5.k3.w(rw, hs, he, parts, [], T.LHeadR{}, bk, qk, [], un, lf, True{}), List.reverse(&2, String, parts)))})
        : T.Doc}
      %Equal.sym(List<&2, String>, List.reverse(&2, String, parts), path, er) : {T.doc.read(rest,
        T.MScan{ap.ln(bd2, rows2, heads2, path, bk, qk, un, lf)}) == T.doc.read(rest,
        T.MScan{T.read.once2(T.head.apply(T.tree.walk(_, T.Tw{rw, T.JAot{}, [], "", "", hs, False{}}, 0), _, bk, qk,
        un, lf, False{}))}) : T.Doc}
      %Equal.sym(T.End, T.tree.walk(path, T.Tw{rw, T.JAot{}, [], "", "", hs, False{}}, 0), T.End{rows2, bd2, heads2},
        ew) : {T.doc.read(rest, T.MScan{ap.ln(bd2, rows2, heads2, path, bk, qk, un, lf)}) == T.doc.read(rest,
        T.MScan{T.read.once2(T.head.apply(_, path, bk, qk, un, lf, False{}))}) : T.Doc}
      {==}

# the rest of the text read after a header in its table, with the walk's
# error, rows and definitions, from every back, qkind, uni and left
def ap.HLine(
  +bd2: String,
  +rows2: List<&2, T.Val>,
  +heads2: List<&2, String>,
  +path: List<&2, String>,
  +rest: String,
  +goal: T.Doc
) -> Type:
  @b2: T.Lex -> @q2: T.QKind -> @u2: U32 -> @l2: U32 ->
    {T.doc.read(rest, T.MScan{ap.ln(bd2, rows2, heads2, path, b2, q2, u2, l2)}) == goal : T.Doc}

# a whole header, from the start of a line in any table, whatever its walk
# returns
def ap.hcore(
  +arr: Bool,
  +g0: List<&2, Bool>,
  +ds: List<&2, L5.KDot>,
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
  +goal: T.Doc,
  +eo: {L5.k3.dk.ok(ds, last) == True{} : Bool},
  +ew: ap.Wk(L5.k3.dk.names(ds, last), rw, D3.header_job(arr), hs, T.End{rows2, bd2, heads2}),
  ih: ap.HLine(bd2, rows2, heads2, L5.k3.dk.names(ds, last), rest, goal)
) -> {T.doc.read(L5.k3.hd.text(arr, g0, ds, last, g9, rest), T.MScan{L5.k3.at(L5.AtLine{}, rw, hs, he, [], a0,
  bk, qk, un, lf)}) == goal : T.Doc}:
  match arr:
    case False{}:
      %M5.k3.hlead(g0, L5.k3.dk.text(ds, last, String.append(D4.gap(g9), SCon{']', rest})), rw, hs, he, bk, qk, un, lf,
        False{}) : {_ == goal : T.Doc}
      M5.k3.hkeys(ds, last, g9, M5.k3.nz(g0), rw, hs, he, [], bk, qk, un, lf, False{}, rest, goal, eo,
          +b2 => +q2 => +u2 =>
        +l2 =>
        %ap.hend(False{}, rw, hs, he, M5.k3.acc(ds, last, M5.k3.nz(g0), []), b2, q2, u2, l2, L5.k3.dk.names(ds, last),
          rows2, bd2, heads2, rest, M5.k3.ne(ds, last, M5.k3.ps0(M5.k3.nz(g0), [])), M5.k3.path(M5.k3.nz(g0), ds,
              last), ew)
          : {_ == goal : T.Doc}
        ih(b2, q2, u2, l2))
    case True{}:
      %M5.k3.hlead(g0, L5.k3.dk.text(ds, last, String.append(D4.gap(g9), SCon{']', SCon{']', rest}})), rw, hs, he,
        bk, qk, un, lf, True{}) : {_ == goal : T.Doc}
      M5.k3.hkeys(ds, last, g9, M5.k3.nz(g0), rw, hs, he, [], bk, qk, un, lf, True{}, SCon{']', rest}, goal, eo,
        +b2 => +q2 => +u2 => +l2 =>
        %ap.hend(True{}, rw, hs, he, M5.k3.acc(ds, last, M5.k3.nz(g0), []), b2, q2, u2, l2, L5.k3.dk.names(ds, last),
          rows2, bd2, heads2, rest, M5.k3.ne(ds, last, M5.k3.ps0(M5.k3.nz(g0), [])), M5.k3.path(M5.k3.nz(g0), ds,
              last), ew)
          : {_ == goal : T.Doc}
        ih(b2, q2, u2, l2))

# The grammar's keys and blank space as KEY-3 spells them.

# blank space as KEY-3's list of tabs and spaces
def ap.gs(+ww: String) -> List<&2, Bool>:
  match ww:
    case SNil{}:
      []
    case SCon{+hh, tt}:
      Char.is_eq(hh, '\t') <> ap.gs(tt)

# a space or a tab is the blank character of whether it is a tab
def ap.bc(
  +cc: Char,
  +hw: {D2.abnf.wschar(cc) == True{} : Bool}
) -> {D4.blank_char(Char.is_eq(cc, '\t')) == cc : Char}:
  ap.wc(c2 => {D4.blank_char(Char.is_eq(c2, '\t')) == c2 : Char}, cc, hw, {==}, {==})

# blank space is the gap of its tabs and spaces
def ap.gap(+ww: String, +hw: {D2.abnf.ws(ww) == True{} : Bool}) -> {D4.gap(ap.gs(ww)) == ww : String}:
  match ww:
    case SNil{}:
      {==}
    case SCon{+hh, +tt}:
      %Equal.sym(Char, D4.blank_char(Char.is_eq(hh, '\t')), hh, ap.bc(hh, Eq.and.left(D2.abnf.wschar(hh),
        D2.abnf.ws(tt), hw))) : {SCon{_, D4.gap(ap.gs(tt))} == SCon{hh, tt} : String}
      %Equal.sym(String, D4.gap(ap.gs(tt)), tt, ap.gap(tt, Eq.and.right(D2.abnf.wschar(hh), D2.abnf.ws(tt), hw)))
        : {SCon{hh, _} == SCon{hh, tt} : String}
      {==}

# a dotted key's segments after its first, from the first, as KEY-3's KDot
# list: each segment with the blank space around the dot after it
def ap.dots(+more: List<&2, D6.GDotSep>, +first: D7.KSeg) -> List<&2, L5.KDot>:
  match more:
    case []:
      []
    case D6.GDotSep{w1, w2, sk} <> rest:
      L5.KDot{first, ap.gs(w1), ap.gs(w2)} <> ap.dots(rest, sk)

# the last segment of a dotted key
def ap.last(+more: List<&2, D6.GDotSep>, +first: D7.KSeg) -> D7.KSeg:
  match more:
    case []:
      first
    case D6.GDotSep{_w1, _w2, sk} <> rest:
      ap.last(rest, sk)

# a key's segments but its last, as KEY-3's KDot list
def ap.kds(+kk: D6.GKey) -> List<&2, L5.KDot>:
  match kk:
    case D6.GSimpleKey{_sk}:
      []
    case D6.GDottedKey{sk, more}:
      ap.dots(more, sk)

# a key's last segment
def ap.klast(+kk: D6.GKey) -> D7.KSeg:
  match kk:
    case D6.GSimpleKey{sk}:
      sk
    case D6.GDottedKey{sk, more}:
      ap.last(more, sk)

# a dotted key's text, from a first segment, is KEY-3's
def ap.DT(
  +more: List<&2, D6.GDotSep>,
  +first: D7.KSeg,
  +tail: String
) -> Data:
  {D7.k3.seg.text(first, D6.g.dots.text(more, tail)) == L5.k3.dk.text(ap.dots(more, first), ap.last(more, first),
    tail) : String}

# one dot-sep's text is KEY-3's, given the rest's
def ap.dots.text2(
  +first: D7.KSeg,
  +w1: String,
  +w2: String,
  +sk: D7.KSeg,
  +rest: List<&2, D6.GDotSep>,
  +tail: String,
  +h1: {D2.abnf.ws(w1) == True{} : Bool},
  +h2: {D2.abnf.ws(w2) == True{} : Bool},
  +ih: ap.DT(rest, sk, tail)
) -> {D7.k3.seg.text(first, D6.g.dots.text(D6.GDotSep{w1, w2, sk} <> rest, tail))
  == L5.k3.dk.text(ap.dots(D6.GDotSep{w1, w2, sk} <> rest, first), ap.last(D6.GDotSep{w1, w2, sk} <> rest, first),
  tail) : String}:
  %ap.gap(w1, h1) : {D7.k3.seg.text(first, String.append(_, SCon{'.', String.append(w2, D7.k3.seg.text(sk,
    D6.g.dots.text(rest, tail)))})) == L5.k3.dk.text(ap.dots(D6.GDotSep{w1, w2, sk} <> rest, first),
    ap.last(D6.GDotSep{w1, w2, sk} <> rest, first), tail) : String}
  %ap.gap(w2, h2) : {D7.k3.seg.text(first, String.append(D4.gap(ap.gs(w1)), SCon{'.', String.append(_,
    D7.k3.seg.text(sk, D6.g.dots.text(rest, tail)))})) == L5.k3.dk.text(ap.dots(D6.GDotSep{w1, w2,
    sk} <> rest, first), ap.last(D6.GDotSep{w1, w2, sk} <> rest, first), tail) : String}
  %Equal.sym(String, D7.k3.seg.text(sk, D6.g.dots.text(rest, tail)), L5.k3.dk.text(ap.dots(rest, sk),
    ap.last(rest, sk), tail), ih) : {D7.k3.seg.text(first, String.append(D4.gap(ap.gs(w1)), SCon{'.',
      String.append(D4.gap(ap.gs(w2)),
    _)})) == L5.k3.dk.text(ap.dots(D6.GDotSep{w1, w2, sk} <> rest, first), ap.last(D6.GDotSep{w1, w2,
    sk} <> rest, first), tail) : String}
  {==}

# a dotted key's text is KEY-3's
def ap.dots.text(
  +more: List<&2, D6.GDotSep>,
  +first: D7.KSeg,
  +tail: String,
  +hd: {D1.g.ok.dots(more) == True{} : Bool}
) -> {D7.k3.seg.text(first, D6.g.dots.text(more, tail)) == L5.k3.dk.text(ap.dots(more, first), ap.last(more,
  first), tail) : String}:
  match more:
    case []:
      {==}
    case D6.GDotSep{+w1, +w2, +sk} <> +rest:
      +h1 = {Eq.and.left(D2.abnf.ws(w1), Bool.and(D2.abnf.ws(w2), Bool.and(D1.g.ok.seg(sk),
        D1.g.ok.dots(rest))),
        hd) : {D2.abnf.ws(w1) == True{} : Bool}}
      +h2r = {Eq.and.right(D2.abnf.ws(w1), Bool.and(D2.abnf.ws(w2), Bool.and(D1.g.ok.seg(sk),
        D1.g.ok.dots(rest))), hd) : {Bool.and(D2.abnf.ws(w2), Bool.and(D1.g.ok.seg(sk), D1.g.ok.dots(rest)))
        == True{} : Bool}}
      +h2 = {Eq.and.left(D2.abnf.ws(w2), Bool.and(D1.g.ok.seg(sk), D1.g.ok.dots(rest)), h2r)
        : {D2.abnf.ws(w2) == True{} : Bool}}
      +h3 = {Eq.and.right(D1.g.ok.seg(sk), D1.g.ok.dots(rest), Eq.and.right(D2.abnf.ws(w2),
        Bool.and(D1.g.ok.seg(sk), D1.g.ok.dots(rest)), h2r)) : {D1.g.ok.dots(rest) == True{} : Bool}}
      ap.dots.text2(first, w1, w2, sk, rest, tail, h1, h2, ap.dots.text(rest, sk, tail, h3))

# a list of names equal to another: what holds of one holds of the other
def ap.tp(
  -PP: List<&2, String> -> Type,
  +aa: List<&2, String>,
  +bb: List<&2, String>,
  ee: {aa == bb : List<&2, String>},
  xx: PP(aa)
) -> PP(bb):
  %ee : PP(_)
  xx

# a dotted key's names are KEY-3's
def ap.dots.names(
  +more: List<&2, D6.GDotSep>,
  +first: D7.KSeg
) -> {D7.k3.seg.name(first) <> D1.g.dots.names(more) == L5.k3.dk.names(ap.dots(more, first), ap.last(more,
  first)) : List<&2, String>}:
  match more:
    case []:
      {==}
    case D6.GDotSep{_w1, _w2, +sk} <> +rest:
      Equal.cong(List<&2, String>, List<&2, String>, ns => D7.k3.seg.name(first) <> ns, D7.k3.seg.name(sk) <>
        D1.g.dots.names(rest), L5.k3.dk.names(ap.dots(rest, sk), ap.last(rest, sk)), ap.dots.names(rest, sk))

# a key's names are KEY-3's
def ap.key.names(
  +kk: D6.GKey
) -> {D1.g.key.names(kk) == L5.k3.dk.names(ap.kds(kk), ap.klast(kk)) : List<&2, String>}:
  match kk:
    case D6.GSimpleKey{_sk}:
      {==}
    case D6.GDottedKey{+sk, +more}:
      ap.dots.names(more, sk)

# a key's text is KEY-3's
def ap.key.text(
  +kk: D6.GKey,
  +tail: String,
  +hk: {D1.g.ok.key(kk) == True{} : Bool}
) -> {D6.g.key.text(kk, tail) == L5.k3.dk.text(ap.kds(kk), ap.klast(kk), tail) : String}:
  match kk:
    case D6.GSimpleKey{_sk}:
      {==}
    case D6.GDottedKey{+sk, +more}:
      ap.dots.text(more, sk, tail, Eq.and.right(D1.g.ok.seg(sk), D1.g.ok.dots(more),
        Eq.and.right(Bool.not(List.is_empty(&2, D6.GDotSep, more)), Bool.and(D1.g.ok.seg(sk),
        D1.g.ok.dots(more)), hk)))

# two halves that hold make an and that holds
def ap.and.t(
  +aa: Bool,
  +bb: Bool,
  +ha: {aa == True{} : Bool},
  +hb: {bb == True{} : Bool}
) -> {Bool.and(aa, bb) == True{} : Bool}:
  match aa:
    case True{}:
      hb
    case False{}:
      Eq.bit.absurd(&2, {Bool.and(False{}, bb) == True{} : Bool}, ha)

# nothing is both and not
def ap.nand(+bb: Bool) -> {Bool.not(Bool.or(False{}, Bool.or(False{}, Bool.and(bb, Bool.not(bb))))) == True{} : Bool}:
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# and so for one fewer test
def ap.nand1(+bb: Bool) -> {Bool.not(Bool.or(False{}, Bool.and(bb, Bool.not(bb)))) == True{} : Bool}:
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# a character basic-unescaped takes is one KEY-3's basic key may hold
def ap.bchar(
  +uu: U32,
  +hb: {D1.abnf.basic_unescaped(Chr{uu}) == True{} : Bool}
) -> {L5.k3.bchar(Chr{uu}) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_eq(uu, 34), False{}, M2.s1.bu.q(uu, hb)) : {Bool.not(Bool.or(_, Bool.or(U32.is_eq(uu, 92),
    Bool.and(Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), Bool.not(U32.is_eq(uu, 9)))))) == True{} : Bool}
  %Equal.sym(Bool, U32.is_eq(uu, 92), False{}, M2.s1.bu.b(uu, hb)) : {Bool.not(Bool.or(False{}, Bool.or(_,
    Bool.and(Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), Bool.not(U32.is_eq(uu, 9)))))) == True{} : Bool}
  %Equal.sym(Bool, Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), U32.is_eq(uu, 9), M2.s1.bu.c9(uu, hb))
    : {Bool.not(Bool.or(False{}, Bool.or(False{}, Bool.and(_, Bool.not(U32.is_eq(uu, 9)))))) == True{} : Bool}
  ap.nand(U32.is_eq(uu, 9))

# a character literal-char takes is one KEY-3's literal key may hold
def ap.lchar(
  +uu: U32,
  +hl: {D1.abnf.literal_char(Chr{uu}) == True{} : Bool}
) -> {L5.lit.char(Chr{uu}) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_eq(uu, 39), False{}, M2.s1.lc.a(uu, hl)) : {Bool.not(Bool.or(_,
    Bool.and(Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), Bool.not(U32.is_eq(uu, 9))))) == True{} : Bool}
  %Equal.sym(Bool, Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), U32.is_eq(uu, 9), M2.s1.lc.c9(uu, hl))
    : {Bool.not(Bool.or(False{}, Bool.and(_, Bool.not(U32.is_eq(uu, 9))))) == True{} : Bool}
  ap.nand1(U32.is_eq(uu, 9))

# a piece of a basic string of the grammar is one KEY-3's basic key may hold
def ap.pc.ok(
  +pp: D7.KPiece,
  +hb: {D1.abnf.basic_char(pp) == True{} : Bool},
  +he: {D1.prose.escape_scalar(pp) == True{} : Bool}
) -> {L5.k3.pc.ok(pp) == True{} : Bool}:
  match pp:
    case D7.KpChar{cc}:
      match cc:
        case Chr{+uu}:
          ap.bchar(uu, hb)
    case D7.KpEsc{_mm}:
      {==}
    case D7.KpU4{_d, _c, _b, _a}:
      he
    case D7.KpU8{_h, _g, _f, _e, _d, _c, _b, _a}:
      he

# and so are all its pieces
def ap.pcs.ok(
  +pl: List<&2, D7.KPiece>,
  +hb: {D1.abnf.basic_string(pl) == True{} : Bool},
  +he: {D1.prose.escapes_scalar(pl) == True{} : Bool}
) -> {L5.k3.pcs.ok(pl) == True{} : Bool}:
  match pl:
    case []:
      {==}
    case +pp <> +rest:
      ap.and.t(L5.k3.pc.ok(pp), L5.k3.pcs.ok(rest), ap.pc.ok(pp, Eq.and.left(D1.abnf.basic_char(pp),
        D1.abnf.basic_string(rest), hb), Eq.and.left(D1.prose.escape_scalar(pp), D1.prose.escapes_scalar(rest),
        he)), ap.pcs.ok(rest, Eq.and.right(D1.abnf.basic_char(pp), D1.abnf.basic_string(rest), hb),
        Eq.and.right(D1.prose.escape_scalar(pp), D1.prose.escapes_scalar(rest), he)))

# a literal string's first character and the rest KEY-3 reads
def ap.lit.ok2(
  +hh: Char,
  +tt: String,
  +h1: {D1.abnf.literal_char(hh) == True{} : Bool},
  +ih: {L5.lit.text(tt) == True{} : Bool}
) -> {Bool.and(L5.lit.char(hh), L5.lit.text(tt)) == True{} : Bool}:
  match hh:
    case Chr{+uu}:
      ap.and.t(L5.lit.char(Chr{uu}), L5.lit.text(tt), ap.lchar(uu, h1), ih)

# a literal string of the grammar is one KEY-3's literal key may hold
def ap.lit.ok(
  +name: String,
  +hl: {D1.abnf.literal_string(name) == True{} : Bool}
) -> {L5.lit.text(name) == True{} : Bool}:
  match name:
    case SNil{}:
      {==}
    case SCon{+hh, +tt}:
      ap.lit.ok2(hh, tt, Eq.and.left(D1.abnf.literal_char(hh), D1.abnf.literal_string(tt), hl), ap.lit.ok(tt,
        Eq.and.right(D1.abnf.literal_char(hh), D1.abnf.literal_string(tt), hl)))

# a segment of the grammar is one KEY-3 reads
def ap.seg.ok(
  +sg: D7.KSeg,
  +hs: {D1.g.ok.seg(sg) == True{} : Bool}
) -> {L5.k3.seg.ok(sg) == True{} : Bool}:
  match sg:
    case D7.KsBare{+name}:
      Equal.trans(Bool, T.bare(name), D3.abnf.unquoted_key(name), True{}, L1.bare_is_unquoted_key(name), hs)
    case D7.KsBasic{+pl}:
      ap.pcs.ok(pl, Eq.and.left(D1.abnf.basic_string(pl), D1.prose.escapes_scalar(pl), hs),
        Eq.and.right(D1.abnf.basic_string(pl), D1.prose.escapes_scalar(pl), hs))
    case D7.KsLit{+name}:
      ap.lit.ok(name, hs)

# a dotted key's segments are ones KEY-3 reads
def ap.dots.ok(
  +more: List<&2, D6.GDotSep>,
  +first: D7.KSeg,
  +hf: {D1.g.ok.seg(first) == True{} : Bool},
  +hd: {D1.g.ok.dots(more) == True{} : Bool}
) -> {L5.k3.dk.ok(ap.dots(more, first), ap.last(more, first)) == True{} : Bool}:
  match more:
    case []:
      ap.seg.ok(first, hf)
    case D6.GDotSep{+w1, +w2, +sk} <> +rest:
      +h2r = {Eq.and.right(D2.abnf.ws(w1), Bool.and(D2.abnf.ws(w2), Bool.and(D1.g.ok.seg(sk),
        D1.g.ok.dots(rest))), hd) : {Bool.and(D2.abnf.ws(w2), Bool.and(D1.g.ok.seg(sk), D1.g.ok.dots(rest)))
        == True{} : Bool}}
      +h3r = {Eq.and.right(D2.abnf.ws(w2), Bool.and(D1.g.ok.seg(sk), D1.g.ok.dots(rest)), h2r)
        : {Bool.and(D1.g.ok.seg(sk), D1.g.ok.dots(rest)) == True{} : Bool}}
      ap.and.t(L5.k3.seg.ok(first), L5.k3.dk.ok(ap.dots(rest, sk), ap.last(rest, sk)), ap.seg.ok(first, hf),
        ap.dots.ok(rest, sk, Eq.and.left(D1.g.ok.seg(sk), D1.g.ok.dots(rest), h3r), Eq.and.right(D1.g.ok.seg(sk),
        D1.g.ok.dots(rest), h3r)))

# a key of the grammar is one KEY-3 reads
def ap.key.ok(
  +kk: D6.GKey,
  +hk: {D1.g.ok.key(kk) == True{} : Bool}
) -> {L5.k3.dk.ok(ap.kds(kk), ap.klast(kk)) == True{} : Bool}:
  match kk:
    case D6.GSimpleKey{+sk}:
      ap.seg.ok(sk, hk)
    case D6.GDottedKey{+sk, +more}:
      +hr = {Eq.and.right(Bool.not(List.is_empty(&2, D6.GDotSep, more)), Bool.and(D1.g.ok.seg(sk),
        D1.g.ok.dots(more)), hk) : {Bool.and(D1.g.ok.seg(sk), D1.g.ok.dots(more)) == True{} : Bool}}
      ap.dots.ok(more, sk, Eq.and.left(D1.g.ok.seg(sk), D1.g.ok.dots(more), hr), Eq.and.right(D1.g.ok.seg(sk),
        D1.g.ok.dots(more), hr))

# a table header's key
def ap.tkey(tb: D6.GTable) -> D6.GKey:
  match tb:
    case D6.GStdTable{_w1, key, _w2}:
      key
    case D6.GArrayTable{_w1, key, _w2}:
      key

# whether a table header is an [[array]] one
def ap.tarr(tb: D6.GTable) -> Bool:
  match tb:
    case D6.GStdTable{_w1, _key, _w2}:
      False{}
    case D6.GArrayTable{_w1, _key, _w2}:
      True{}

# the blank space after a header's opening brackets
def ap.tw1(tb: D6.GTable) -> String:
  match tb:
    case D6.GStdTable{w1, _key, _w2}:
      w1
    case D6.GArrayTable{w1, _key, _w2}:
      w1

# the blank space before a header's closing brackets
def ap.tw2(tb: D6.GTable) -> String:
  match tb:
    case D6.GStdTable{_w1, _key, w2}:
      w2
    case D6.GArrayTable{_w1, _key, w2}:
      w2

# a header's key is one of the grammar
def ap.tbl.hk(
  +tb: D6.GTable,
  +hok: {D1.g.ok.table(tb) == True{} : Bool}
) -> {D1.g.ok.key(ap.tkey(tb)) == True{} : Bool}:
  match tb:
    case D6.GStdTable{+w1, +key, +w2}:
      Eq.and.left(D1.g.ok.key(key), D2.abnf.ws(w2), Eq.and.right(D2.abnf.ws(w1), Bool.and(D1.g.ok.key(key),
        D2.abnf.ws(w2)), hok))
    case D6.GArrayTable{+w1, +key, +w2}:
      Eq.and.left(D1.g.ok.key(key), D2.abnf.ws(w2), Eq.and.right(D2.abnf.ws(w1), Bool.and(D1.g.ok.key(key),
        D2.abnf.ws(w2)), hok))

# a [table] header's text is KEY-3's
def ap.std.text(
  +v1: String,
  +key: D6.GKey,
  +v2: String,
  +xx: String,
  +h1: {D2.abnf.ws(v1) == True{} : Bool},
  +hk: {D1.g.ok.key(key) == True{} : Bool},
  +h2: {D2.abnf.ws(v2) == True{} : Bool}
) -> {D6.g.table.text(D6.GStdTable{v1, key, v2}, xx) == L5.k3.hd.text(False{}, ap.gs(v1), ap.kds(key),
  ap.klast(key), ap.gs(v2), xx) : String}:
  %ap.gap(v1, h1) : {SCon{'[', String.append(_, D6.g.key.text(key, String.append(v2, SCon{']', xx})))}
    == L5.k3.hd.text(False{}, ap.gs(v1), ap.kds(key), ap.klast(key), ap.gs(v2), xx) : String}
  %ap.gap(v2, h2) : {SCon{'[', String.append(D4.gap(ap.gs(v1)), D6.g.key.text(key, String.append(_, SCon{']',
    xx})))} == L5.k3.hd.text(False{}, ap.gs(v1), ap.kds(key), ap.klast(key), ap.gs(v2), xx) : String}
  %Equal.sym(String, D6.g.key.text(key, String.append(D4.gap(ap.gs(v2)), SCon{']', xx})),
    L5.k3.dk.text(ap.kds(key),
    ap.klast(key), String.append(D4.gap(ap.gs(v2)), SCon{']', xx})), ap.key.text(key,
      String.append(D4.gap(ap.gs(v2)),
    SCon{']', xx}), hk)) : {SCon{'[', String.append(D4.gap(ap.gs(v1)), _)} == L5.k3.hd.text(False{}, ap.gs(v1),
    ap.kds(key), ap.klast(key), ap.gs(v2), xx) : String}
  {==}

# an [[array]] header's text is KEY-3's
def ap.aot.text(
  +v1: String,
  +key: D6.GKey,
  +v2: String,
  +xx: String,
  +h1: {D2.abnf.ws(v1) == True{} : Bool},
  +hk: {D1.g.ok.key(key) == True{} : Bool},
  +h2: {D2.abnf.ws(v2) == True{} : Bool}
) -> {D6.g.table.text(D6.GArrayTable{v1, key, v2}, xx) == L5.k3.hd.text(True{}, ap.gs(v1), ap.kds(key),
  ap.klast(key), ap.gs(v2), xx) : String}:
  %ap.gap(v1, h1) : {SCon{'[', SCon{'[', String.append(_, D6.g.key.text(key, String.append(v2, SCon{']', SCon{']',
    xx}})))}} == L5.k3.hd.text(True{}, ap.gs(v1), ap.kds(key), ap.klast(key), ap.gs(v2), xx) : String}
  %ap.gap(v2, h2) : {SCon{'[', SCon{'[', String.append(D4.gap(ap.gs(v1)), D6.g.key.text(key, String.append(_,
    SCon{']', SCon{']', xx}})))}} == L5.k3.hd.text(True{}, ap.gs(v1), ap.kds(key), ap.klast(key), ap.gs(v2), xx)
    : String}
  %Equal.sym(String, D6.g.key.text(key, String.append(D4.gap(ap.gs(v2)), SCon{']', SCon{']', xx}})),
    L5.k3.dk.text(ap.kds(key), ap.klast(key), String.append(D4.gap(ap.gs(v2)), SCon{']', SCon{']', xx}})),
    ap.key.text(key, String.append(D4.gap(ap.gs(v2)), SCon{']', SCon{']', xx}}), hk)) : {SCon{'[', SCon{'[',
    String.append(D4.gap(ap.gs(v1)), _)}} == L5.k3.hd.text(True{}, ap.gs(v1), ap.kds(key), ap.klast(key),
    ap.gs(v2), xx) : String}
  {==}

# a table header's text is KEY-3's
def ap.tbl.text(
  +tb: D6.GTable,
  +xx: String,
  +hok: {D1.g.ok.table(tb) == True{} : Bool}
) -> {D6.g.table.text(tb, xx) == L5.k3.hd.text(ap.tarr(tb), ap.gs(ap.tw1(tb)), ap.kds(ap.tkey(tb)),
  ap.klast(ap.tkey(tb)), ap.gs(ap.tw2(tb)), xx) : String}:
  match tb:
    case D6.GStdTable{+w1, +key, +w2}:
      +hr = {Eq.and.right(D2.abnf.ws(w1), Bool.and(D1.g.ok.key(key), D2.abnf.ws(w2)), hok)
        : {Bool.and(D1.g.ok.key(key), D2.abnf.ws(w2)) == True{} : Bool}}
      ap.std.text(w1, key, w2, xx, Eq.and.left(D2.abnf.ws(w1), Bool.and(D1.g.ok.key(key), D2.abnf.ws(w2)), hok),
        Eq.and.left(D1.g.ok.key(key), D2.abnf.ws(w2), hr), Eq.and.right(D1.g.ok.key(key), D2.abnf.ws(w2), hr))
    case D6.GArrayTable{+w1, +key, +w2}:
      +hr = {Eq.and.right(D2.abnf.ws(w1), Bool.and(D1.g.ok.key(key), D2.abnf.ws(w2)), hok)
        : {Bool.and(D1.g.ok.key(key), D2.abnf.ws(w2)) == True{} : Bool}}
      ap.aot.text(w1, key, w2, xx, Eq.and.left(D2.abnf.ws(w1), Bool.and(D1.g.ok.key(key), D2.abnf.ws(w2)), hok),
        Eq.and.left(D1.g.ok.key(key), D2.abnf.ws(w2), hr), Eq.and.right(D1.g.ok.key(key), D2.abnf.ws(w2), hr))

# a table header of the grammar, from the start of a line in any table,
# whatever its walk returns: the rest is read in its table with the walk's
# error, rows and definitions
def ap.table(
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
  +goal: T.Doc,
  +hok: {D1.g.ok.table(tb) == True{} : Bool},
  ew: ap.Wk(D1.g.key.names(ap.tkey(tb)), rw, D3.header_job(ap.tarr(tb)), hs, T.End{rows2, bd2, heads2}),
  ih: ap.HLine(bd2, rows2, heads2, D1.g.key.names(ap.tkey(tb)), tail, goal)
) -> {T.doc.read(D6.g.table.text(tb, tail), T.MScan{ap.s(T.LTop{}, bk, rw, hs, he, [], qk, [], un, lf, ab)}) == goal
  : T.Doc}:
  %Equal.sym(String, D6.g.table.text(tb, tail), L5.k3.hd.text(ap.tarr(tb), ap.gs(ap.tw1(tb)), ap.kds(ap.tkey(tb)),
    ap.klast(ap.tkey(tb)), ap.gs(ap.tw2(tb)), tail), ap.tbl.text(tb, tail, hok)) : {T.doc.read(_, T.MScan{ap.s(T.LTop{},
    bk, rw, hs, he, [], qk, [], un, lf, ab)}) == goal : T.Doc}
  ap.hcore(ap.tarr(tb), ap.gs(ap.tw1(tb)), ap.kds(ap.tkey(tb)), ap.klast(ap.tkey(tb)), ap.gs(ap.tw2(tb)), rw, hs, he,
    ab,
    bk, qk, un, lf, rows2, bd2, heads2, tail, goal, ap.key.ok(ap.tkey(tb), ap.tbl.hk(tb, hok)), ap.tp(ns =>
    ap.Wk(ns, rw, D3.header_job(ap.tarr(tb)), hs, T.End{rows2, bd2, heads2}), D1.g.key.names(ap.tkey(tb)),
      L5.k3.dk.names(ap.kds(ap.tkey(tb)), ap.klast(ap.tkey(tb))),
    ap.key.names(ap.tkey(tb)), ew), ap.tp(ns => ap.HLine(bd2, rows2, heads2, ns, tail, goal),
    D1.g.key.names(ap.tkey(tb)), L5.k3.dk.names(ap.kds(ap.tkey(tb)), ap.klast(ap.tkey(tb))),
    ap.key.names(ap.tkey(tb)), ih))

# WP-A: a document of headers, comments and blank lines. parse starts with
# a byte-order mark allowed (lead); a text that starts with none reads as it
# does from the start of a line (ap.lead). Each expression is read from the
# start of a line (ap.xstep): a blank line's blank space and comment, or a
# header, its walk, and the blank space and comment after it. The rest of the
# text is then read from the state they leave (ap.K): the end of the text
# gives the rows, and a newline starts the next line (ap.go). A header whose
# walk fails leaves the scanner with its error, which stays with its rows to
# the end (error_stays), and replay keeps them as well (ap.stays).

# a text that does not start with a byte-order mark
def ap.nobom(+ss: String) -> Bool:
  match ss:
    case SNil{}:
      True{}
    case SCon{+hh, _tt}:
      Bool.not(U32.is_eq(Char.to_u32(hh), 65279))

# the scanner at the start of a document, past its first character
def ap.s0() -> T.St:
  ap.s(T.LTop{}, T.LTop{}, [], [], [], [], T.QBasic{}, [], 0, 0, False{})

# the first character, when it is no byte-order mark, is read as a later one
def ap.lead.fast(
  +cc: Char,
  +hb: {U32.is_eq(Char.to_u32(cc), 65279) == False{} : Bool}
) -> {T.read.fast(T.st.start(), cc) == T.read.fast(ap.s0(), cc) : T.St}:
  %Equal.sym(T.St, T.read.fast.lex(T.LTop{}, T.QBasic{}, "", [], [], [], [], [], T.LTop{}, [], 0, 0, False{}, cc),
    T.read.fast.old("", [], [], [], [], [], T.LTop{}, T.LTop{}, T.QBasic{}, [], 0, 0, False{}, cc), M3.sr.ff(T.LTop{},
    T.QBasic{}, "", [], [], [], [], [], T.LTop{}, [], 0, 0, False{}, cc)) : {T.read.fast(T.st.start(), cc) == _ : T.St}
  %Equal.sym(Bool, U32.is_eq(Char.to_u32(cc), 65279), False{}, hb) : {T.read.once2(T.read.step.bom(_, ap.s0(), cc))
    == T.read.fast.old("", [], [], [], [], [], T.LTop{}, T.LTop{}, T.QBasic{}, [], 0, 0, False{}, cc) : T.St}
  {==}

# and so doc.scan takes it the same way
def ap.lead.scan(
  +dq: Bool,
  +sq: Bool,
  +cr: Bool,
  +cc: Char,
  +ef: {T.read.fast(T.st.start(), cc) == T.read.fast(ap.s0(), cc) : T.St}
) -> {T.doc.scan.q(dq, sq, cr, T.st.start(), cc) == T.doc.scan.q(dq, sq, cr, ap.s0(), cc) : T.Mode}:
  match dq:
    case True{}:
      Equal.cong(T.St, T.Mode, st => T.doc.wrap(st), T.read.fast(T.st.start(), cc), T.read.fast(ap.s0(), cc), ef)
    case False{}:
      match sq:
        case True{}:
          Equal.cong(T.St, T.Mode, st => T.doc.wrap(st), T.read.fast(T.st.start(), cc), T.read.fast(ap.s0(), cc), ef)
        case False{}:
          match cr:
            case True{}:
              Equal.cong(T.St, T.Mode, st => T.MCr{st}, T.read.fast(T.st.start(), cc), T.read.fast(ap.s0(), cc), ef)
            case False{}:
              Equal.cong(T.St, T.Mode, st => T.MScan{st}, T.read.fast(T.st.start(), cc), T.read.fast(ap.s0(), cc), ef)

# a text that starts with no byte-order mark reads from the start of a
# document as from the start of a line
def ap.lead(
  +tt: String,
  +ht: {ap.nobom(tt) == True{} : Bool}
) -> {T.doc.read(tt, T.MScan{T.st.start()}) == T.doc.read(tt, T.MScan{ap.s0()}) : T.Doc}:
  match tt:
    case SNil{}:
      {==}
    case SCon{+hh, +t2}:
      Equal.cong(T.Mode, T.Doc, md => T.doc.read(t2, md), T.doc.scan(T.st.start(), hh), T.doc.scan(ap.s0(), hh),
        ap.lead.scan(Char.is_eq(hh, '"'), Char.is_eq(hh, '\''), U32.is_eq(Char.to_u32(hh), 13), hh,
        ap.lead.fast(hh, Eq.not.true(U32.is_eq(Char.to_u32(hh), 65279), ht))))

# blank space starts with no byte-order mark, and so does what follows it
def ap.nb.ws(
  +ww: String,
  +xx: String,
  +hw: {D2.abnf.ws(ww) == True{} : Bool},
  +hx: {ap.nobom(xx) == True{} : Bool}
) -> {ap.nobom(String.append(ww, xx)) == True{} : Bool}:
  match ww:
    case SNil{}:
      hx
    case SCon{+hh, _tt}:
      ap.wc(cc => {Bool.not(U32.is_eq(Char.to_u32(cc), 65279)) == True{} : Bool}, hh, Eq.and.left(D2.abnf.wschar(hh),
        D2.abnf.ws(_tt), hw), {==}, {==})

# a newline starts with none
def ap.nb.nl(
  +nl: String,
  +xx: String,
  +hn: {D1.abnf.newline(nl) == True{} : Bool}
) -> {ap.nobom(String.append(nl, xx)) == True{} : Bool}:
  M2.s1.nl.elim(n2 => {ap.nobom(String.append(n2, xx)) == True{} : Bool}, nl, hn, {==}, {==})

# nor do the lines after the first expression
def ap.nb.lines(
  +ls: List<&2, D6.GLine>,
  +hl: {D1.g.ok.lines(ls) == True{} : Bool}
) -> {ap.nobom(D6.g.lines.text(ls, "")) == True{} : Bool}:
  match ls:
    case []:
      {==}
    case D6.GLine{+nl, +ex} <> +rest:
      ap.nb.nl(nl, D6.g.expr.text(ex, D6.g.lines.text(rest, "")), Eq.and.left(D1.abnf.newline(nl),
        Bool.and(D1.g.ok.expr(ex), D1.g.ok.lines(rest)), hl))

# a [ comment ] starts with a #, or is nothing before what follows
def ap.nb.com(
  +com: D6.GCom,
  +xx: String,
  +hx: {ap.nobom(xx) == True{} : Bool}
) -> {ap.nobom(D6.g.com.text(com, xx)) == True{} : Bool}:
  match com:
    case D6.GcNone{}:
      hx
    case D6.GcSome{_body}:
      {==}

# a header starts with a bracket
def ap.nb.tb(+tb: D6.GTable, +xx: String) -> {ap.nobom(D6.g.table.text(tb, xx)) == True{} : Bool}:
  match tb:
    case D6.GStdTable{_w1, _key, _w2}:
      {==}
    case D6.GArrayTable{_w1, _key, _w2}:
      {==}

# the table a header's lines are in, and here otherwise
def ap.xhere(+ex: D6.GExpr, +here: List<&2, String>) -> List<&2, String>:
  match ex:
    case D6.GxTable{_w1, D6.GStdTable{_a, key, _b}, _w2, _com}:
      D1.g.key.names(key)
    case D6.GxTable{_w1, D6.GArrayTable{_a, key, _b}, _w2, _com}:
      D1.g.key.names(key)
    case _:
      here

# a blank line or a header, replayed from an error, keeps it and the rows
def ap.stays.x(
  +ex: D6.GExpr,
  +bd: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +eb: {String.is_empty(bd) == False{} : Bool},
  +nx: {L4.ra.nokv.expr(ex) == True{} : Bool}
) -> {D5.replay.expr(ex, D5.RpSt{bd, rows, heads, here}) == D5.RpSt{bd, rows, heads, ap.xhere(ex, here)}
  : D5.RpSt}:
  match ex:
    case D6.GxBlank{_w1, _com}:
      {==}
    case D6.GxKeyval{_w1, _kv, _w2, _com}:
      Eq.bit.absurd(&2, {D5.replay.expr(D6.GxKeyval{_w1, _kv, _w2, _com}, D5.RpSt{bd, rows, heads, here})
        == D5.RpSt{bd, rows, heads, ap.xhere(D6.GxKeyval{_w1, _kv, _w2, _com}, here)} : D5.RpSt}, nx)
    case D6.GxTable{_w1, D6.GStdTable{_a, +key, _b}, _w2, _com}:
      %Equal.sym(T.End, T.tree.walk(D1.g.key.names(key), T.Tw{rows, T.JDef{}, [], bd, "", heads, False{}}, 0),
        T.End{rows, bd, heads}, L2.failed_walk_changes_nothing(D1.g.key.names(key), rows, T.JDef{}, bd, "", heads,
        False{}, 0, eb)) : {D5.replay.end(_, D1.g.key.names(key)) == D5.RpSt{bd, rows, heads,
          D1.g.key.names(key)}
        : D5.RpSt}
      {==}
    case D6.GxTable{_w1, D6.GArrayTable{_a, +key, _b}, _w2, _com}:
      %Equal.sym(T.End, T.tree.walk(D1.g.key.names(key), T.Tw{rows, T.JAot{}, [], bd, "", heads, False{}}, 0),
        T.End{rows, bd, heads}, L2.failed_walk_changes_nothing(D1.g.key.names(key), rows, T.JAot{}, bd, "", heads,
        False{}, 0, eb)) : {D5.replay.end(_, D1.g.key.names(key)) == D5.RpSt{bd, rows, heads,
          D1.g.key.names(key)}
        : D5.RpSt}
      {==}

# blank lines and headers, replayed from an error, keep it and the rows to
# the end
def ap.stays(
  +ls: List<&2, D6.GLine>,
  +bd: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +eb: {String.is_empty(bd) == False{} : Bool},
  +nl: {L4.ra.nokv.lines(ls) == True{} : Bool}
) -> {D5.replay.doc(D5.replay.lines(ls, D5.RpSt{bd, rows, heads, here})) == T.Doc{bd, T.rows.seal(rows)}
  : T.Doc}:
  match ls:
    case []:
      {==}
    case D6.GLine{_nl, +ex} <> +rest:
      %Equal.sym(D5.RpSt, D5.replay.expr(ex, D5.RpSt{bd, rows, heads, here}), D5.RpSt{bd, rows, heads,
        ap.xhere(ex, here)}, ap.stays.x(ex, bd, rows, heads, here, eb, Eq.and.left(L4.ra.nokv.expr(ex),
        L4.ra.nokv.lines(rest), nl))) : {D5.replay.doc(D5.replay.lines(rest, _)) == T.Doc{bd, T.rows.seal(rows)}
        : T.Doc}
      ap.stays(rest, bd, rows, heads, ap.xhere(ex, here), eb, Eq.and.right(L4.ra.nokv.expr(ex),
        L4.ra.nokv.lines(rest), nl))

# the document the replay of the lines ls gives from a replay state
def ap.F(+ls: List<&2, D6.GLine>, +rp: D5.RpSt) -> T.Doc:
  D5.replay.doc(D5.replay.lines(ls, rp))

# the rest of the text after an expression, as the reader of the lines ls
# after it gives it: from the state a [ comment ] leaves at the start of a
# line or after a header, with no error, the rest reads to the document the
# lines' replay gives from the same rows, definitions and table
def ap.K(+ls: List<&2, D6.GLine>, +tail: String) -> Type:
  @com: D6.GCom -> @lx: T.Lex -> {ap.tll(lx) == True{} : Bool} -> @bk: T.Lex -> @rw: List<&2, T.Val> ->
    @hs: List<&2, String> -> @he: List<&2, String> -> @qk: T.QKind -> @un: U32 -> @lf: U32 ->
    {T.doc.read(tail, T.MScan{ap.aft(com, lx, bk, rw, hs, he, [], qk, [], un, lf, False{})})
    == ap.F(ls, D5.RpSt{"", rw, hs, he}) : T.Doc}

# and the lines' replay from a state with an error gives the document of the
# error and the rows
def ap.E(+ls: List<&2, D6.GLine>) -> Type:
  @bd: String -> {String.is_empty(bd) == False{} : Bool} -> @rows: List<&2, T.Val> -> @heads: List<&2, String> ->
    @here: List<&2, String> ->
    {ap.F(ls, D5.RpSt{bd, rows, heads, here}) == T.Doc{bd, T.rows.seal(rows)} : T.Doc}

# after a header, however its walk ended, the blank space, the comment and
# the rest read to what the replay gives
def ap.hl(
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
  kk: ap.K(ls, tail),
  ee: ap.E(ls)
) -> ap.HLine(bd2, rows2, heads2, names, String.append(w2, D6.g.com.text(com, tail)), ap.F(ls, D5.RpSt{bd2, rows2,
  heads2, names})):
  match bd2:
    case SNil{}:
      +b2 => +q2 => +u2 => +l2 => Equal.trans(T.Doc, T.doc.read(String.append(w2, D6.g.com.text(com, tail)),
        T.MScan{ap.ln("", rows2, heads2, names, b2, q2, u2, l2)}), T.doc.read(tail, T.MScan{ap.aft(com, T.LLine{}, b2,
        rows2, heads2, names, [], q2, [], u2, l2, False{})}), ap.F(ls, D5.RpSt{"", rows2, heads2, names}),
          ap.tail(w2, com,
        tail, T.LLine{}, b2, rows2, heads2, names, [], q2, [], u2, l2, False{}, {==}, {==}, hw, hc), kk(com, T.LLine{},
        {==}, b2, rows2, heads2, names, q2, u2, l2))
    case SCon{+c0, +cs}:
      +b2 => +q2 => +u2 => +l2 => Equal.trans(T.Doc, T.doc.read(String.append(w2, D6.g.com.text(com, tail)),
        T.MScan{ap.ln(SCon{c0, cs}, rows2, heads2, names, b2, q2, u2, l2)}), T.Doc{SCon{c0, cs}, T.rows.seal(rows2)},
        ap.F(ls, D5.RpSt{SCon{c0, cs}, rows2, heads2, names}), L3.error_stays(SCon{c0, cs}, rows2, heads2, names,
          [], [],
        T.LLine{}, b2, q2, [], T.HNone{}, u2, l2, False{}, False{}, {==}, String.append(w2, D6.g.com.text(com,
          tail))),
        Equal.sym(T.Doc, ap.F(ls, D5.RpSt{SCon{c0, cs}, rows2, heads2, names}), T.Doc{SCon{c0, cs},
          T.rows.seal(rows2)},
        ee(SCon{c0, cs}, {==}, rows2, heads2, names)))

# a header and what follows it, with its walk's result named
def ap.xtab(
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
  +hen: ap.Wk(D1.g.key.names(ap.tkey(tb)), rw, D3.header_job(ap.tarr(tb)), hs, en),
  +hok: {D1.g.ok.table(tb) == True{} : Bool},
  +hw: {D2.abnf.ws(w2) == True{} : Bool},
  +hc: {D1.g.ok.com(com) == True{} : Bool},
  kk: ap.K(ls, tail),
  ee: ap.E(ls)
) -> {T.doc.read(D6.g.table.text(tb, String.append(w2, D6.g.com.text(com, tail))), T.MScan{ap.s(T.LTop{}, bk, rw,
  hs, he, [], qk, [], un, lf, False{})}) == ap.F(ls, D5.replay.end(en, D1.g.key.names(ap.tkey(tb)))) : T.Doc}:
  match en:
    case T.End{+rows2, +bd2, +heads2}:
      ap.table(tb, String.append(w2, D6.g.com.text(com, tail)), rw, hs, he, False{}, bk, qk, un, lf, rows2, bd2,
        heads2, ap.F(ls, D5.RpSt{bd2, rows2, heads2, D1.g.key.names(ap.tkey(tb))}), hok, hen, ap.hl(bd2, rows2,
          heads2,
        D1.g.key.names(ap.tkey(tb)), w2, com, tail, ls, hw, hc, kk, ee))

# a header and what follows it, as its walk replays
def ap.xtb2(
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
  kk: ap.K(ls, tail),
  ee: ap.E(ls)
) -> {T.doc.read(D6.g.table.text(tb, String.append(w2, D6.g.com.text(com, tail))), T.MScan{ap.s(T.LTop{}, bk, rw,
  hs, he, [], qk, [], un, lf, False{})}) == ap.F(ls, D5.replay.expr(D6.GxTable{w1, tb, w2, com}, D5.RpSt{"", rw,
    hs,
  he})) : T.Doc}:
  match tb:
    case D6.GStdTable{+v1, +key, +v2}:
      ap.xtab(D6.GStdTable{v1, key, v2}, w2, com, tail, rw, hs, he, bk, qk, un, lf, ls,
        T.tree.walk(D1.g.key.names(key), T.Tw{rw, T.JDef{}, [], "", "", hs, False{}}, 0), {==}, hok, hw, hc, kk, ee)
    case D6.GArrayTable{+v1, +key, +v2}:
      ap.xtab(D6.GArrayTable{v1, key, v2}, w2, com, tail, rw, hs, he, bk, qk, un, lf, ls,
        T.tree.walk(D1.g.key.names(key), T.Tw{rw, T.JAot{}, [], "", "", hs, False{}}, 0), {==}, hok, hw, hc, kk, ee)

# a header line: its blank space, the header and what follows it
def ap.xtb(
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
  kk: ap.K(ls, tail),
  ee: ap.E(ls)
) -> {T.doc.read(D6.g.expr.text(D6.GxTable{w1, tb, w2, com}, tail), T.MScan{ap.s(T.LTop{}, bk, rw, hs, he, [], qk,
  [], un, lf, False{})}) == ap.F(ls, D5.replay.expr(D6.GxTable{w1, tb, w2, com}, D5.RpSt{"", rw, hs,
    he})) : T.Doc}:
  +hr = {Eq.and.right(D2.abnf.ws(w1), Bool.and(D1.g.ok.table(tb), Bool.and(D2.abnf.ws(w2), D1.g.ok.com(com))),
    hx) : {Bool.and(D1.g.ok.table(tb), Bool.and(D2.abnf.ws(w2), D1.g.ok.com(com))) == True{} : Bool}}
  +hr2 = {Eq.and.right(D1.g.ok.table(tb), Bool.and(D2.abnf.ws(w2), D1.g.ok.com(com)), hr)
    : {Bool.and(D2.abnf.ws(w2), D1.g.ok.com(com)) == True{} : Bool}}
  Equal.trans(T.Doc, T.doc.read(D6.g.expr.text(D6.GxTable{w1, tb, w2, com}, tail), T.MScan{ap.s(T.LTop{}, bk, rw,
    hs, he, [], qk, [], un, lf, False{})}), T.doc.read(D6.g.table.text(tb, String.append(w2, D6.g.com.text(com,
    tail))), T.MScan{ap.s(T.LTop{}, bk, rw, hs, he, [], qk, [], un, lf, False{})}), ap.F(ls,
      D5.replay.expr(D6.GxTable{w1,
    tb, w2, com}, D5.RpSt{"", rw, hs, he})), ap.ws(w1, D6.g.table.text(tb, String.append(w2, D6.g.com.text(com,
    tail))), T.LTop{}, bk, rw, hs, he, [], qk, [], un, lf, False{}, {==}, Eq.and.left(D2.abnf.ws(w1),
    Bool.and(D1.g.ok.table(tb), Bool.and(D2.abnf.ws(w2), D1.g.ok.com(com))), hx)), ap.xtb2(tb, w1, w2, com, tail,
    rw, hs, he, bk, qk, un, lf, ls, Eq.and.left(D1.g.ok.table(tb), Bool.and(D2.abnf.ws(w2), D1.g.ok.com(com)),
    hr), Eq.and.left(D2.abnf.ws(w2), D1.g.ok.com(com), hr2), Eq.and.right(D2.abnf.ws(w2), D1.g.ok.com(com),
    hr2), kk, ee))

# one blank line or header from the start of a line in any table, then the
# rest as ap.K reads it
def ap.xstep(
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
  +nx: {L4.ra.nokv.expr(ex) == True{} : Bool},
  kk: ap.K(ls, tail),
  ee: ap.E(ls)
) -> {T.doc.read(D6.g.expr.text(ex, tail), T.MScan{ap.s(T.LTop{}, bk, rw, hs, he, [], qk, [], un, lf, False{})})
  == ap.F(ls, D5.replay.expr(ex, D5.RpSt{"", rw, hs, he})) : T.Doc}:
  match ex:
    case D6.GxBlank{+w1, +com}:
      Equal.trans(T.Doc, T.doc.read(String.append(w1, D6.g.com.text(com, tail)), T.MScan{ap.s(T.LTop{}, bk, rw, hs,
        he, [], qk, [], un, lf, False{})}), T.doc.read(tail, T.MScan{ap.aft(com, T.LTop{}, bk, rw, hs, he, [], qk, [],
        un, lf, False{})}), ap.F(ls, D5.RpSt{"", rw, hs, he}), ap.tail(w1, com, tail, T.LTop{}, bk, rw, hs, he, [],
          qk, [],
        un, lf, False{}, {==}, {==}, Eq.and.left(D2.abnf.ws(w1), D1.g.ok.com(com), hx),
        Eq.and.right(D2.abnf.ws(w1), D1.g.ok.com(com), hx)), kk(com, T.LTop{}, {==}, bk, rw, hs, he, qk, un, lf))
    case D6.GxKeyval{_w1, _kv, _w2, _com}:
      Eq.bit.absurd(&2, {T.doc.read(D6.g.expr.text(D6.GxKeyval{_w1, _kv, _w2, _com}, tail), T.MScan{ap.s(T.LTop{},
        bk, rw, hs, he, [], qk, [], un, lf, False{})}) == ap.F(ls, D5.replay.expr(D6.GxKeyval{_w1, _kv, _w2, _com},
        D5.RpSt{"", rw, hs, he})) : T.Doc}, nx)
    case D6.GxTable{+w1, +tb, +w2, +com}:
      ap.xtb(tb, w1, w2, com, tail, rw, hs, he, bk, qk, un, lf, ls, hx, kk, ee)

# the lines after an expression: the expression, a newline and the next
# line's, and so on to the end, read from the start of a line to the
# document the replay gives
def ap.go(
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
  +nx: {L4.ra.nokv.expr(ex) == True{} : Bool},
  +nl: {L4.ra.nokv.lines(ls) == True{} : Bool}
) -> {T.doc.read(D6.g.expr.text(ex, D6.g.lines.text(ls, "")), T.MScan{ap.s(T.LTop{}, bk, rw, hs, he, [], qk, [], un,
  lf, False{})}) == D5.replay.doc(D5.replay.lines(ls, D5.replay.expr(ex, D5.RpSt{"", rw, hs, he}))) : T.Doc}:
  match ls:
    case []:
      ap.xstep(ex, "", rw, hs, he, bk, qk, un, lf, [], hx, nx,
        +com => +lx => +h2 => +b2 => +r2 => +s2 => +e2 => +q2 => +u2 => +l2 => ap.fin(com, lx, b2, r2, s2, e2, [], q2,
          u2,
        l2, False{}, h2), _bd => _eb => _rows => _heads => _here => {==})
    case D6.GLine{+nn, +ex2} <> +ls2:
      +h1 = {Eq.and.right(D1.abnf.newline(nn), Bool.and(D1.g.ok.expr(ex2), D1.g.ok.lines(ls2)), hl)
        : {Bool.and(D1.g.ok.expr(ex2), D1.g.ok.lines(ls2)) == True{} : Bool}}
      ap.xstep(ex, String.append(nn, D6.g.expr.text(ex2, D6.g.lines.text(ls2, ""))), rw, hs, he, bk, qk, un, lf,
        D6.GLine{nn, ex2} <> ls2, hx, nx,
        +com => +lx => +h2 => +b2 => +r2 => +s2 => +e2 => +q2 => +u2 => +l2 => ap.tll.elim(l3 =>
        {T.doc.read(String.append(nn, D6.g.expr.text(ex2, D6.g.lines.text(ls2, ""))), T.MScan{ap.aft(com, l3, b2,
          r2,
        s2, e2, [], q2, [], u2, l2, False{})}) == D5.replay.doc(D5.replay.lines(D6.GLine{nn, ex2} <> ls2,
        D5.RpSt{"", r2, s2, e2})) : T.Doc}, lx, h2, Equal.trans(T.Doc, T.doc.read(String.append(nn,
        D6.g.expr.text(ex2, D6.g.lines.text(ls2, ""))), T.MScan{ap.aft(com, T.LTop{}, b2, r2, s2, e2, [], q2, [],
          u2,
        l2, False{})}), T.doc.read(D6.g.expr.text(ex2, D6.g.lines.text(ls2, "")), T.MScan{ap.s(T.LTop{},
        ap.abk(com, T.LTop{}, b2), r2, s2, e2, [], q2, [], u2, l2, False{})}), D5.replay.doc(D5.replay.lines(ls2,
        D5.replay.expr(ex2, D5.RpSt{"", r2, s2, e2}))), ap.eol(com, T.LTop{}, nn, D6.g.expr.text(ex2,
        D6.g.lines.text(ls2, "")), b2, r2, s2, e2, [], q2, [], u2, l2, False{}, {==},
          Eq.and.left(D1.abnf.newline(nn),
        Bool.and(D1.g.ok.expr(ex2), D1.g.ok.lines(ls2)), hl)), ap.go(ls2, ex2, r2, s2, e2, ap.abk(com, T.LTop{},
          b2),
        q2, u2, l2, Eq.and.left(D1.g.ok.expr(ex2), D1.g.ok.lines(ls2), h1), Eq.and.right(D1.g.ok.expr(ex2),
        D1.g.ok.lines(ls2), h1), Eq.and.left(L4.ra.nokv.expr(ex2), L4.ra.nokv.lines(ls2), nl),
        Eq.and.right(L4.ra.nokv.expr(ex2), L4.ra.nokv.lines(ls2), nl))), Equal.trans(T.Doc,
          T.doc.read(String.append(nn,
        D6.g.expr.text(ex2, D6.g.lines.text(ls2, ""))), T.MScan{ap.aft(com, T.LLine{}, b2, r2, s2, e2, [], q2, [],
          u2,
        l2, False{})}), T.doc.read(D6.g.expr.text(ex2, D6.g.lines.text(ls2, "")), T.MScan{ap.s(T.LTop{},
        ap.abk(com, T.LLine{}, b2), r2, s2, e2, [], q2, [], u2, l2, False{})}), D5.replay.doc(D5.replay.lines(ls2,
        D5.replay.expr(ex2, D5.RpSt{"", r2, s2, e2}))), ap.eol(com, T.LLine{}, nn, D6.g.expr.text(ex2,
        D6.g.lines.text(ls2, "")), b2, r2, s2, e2, [], q2, [], u2, l2, False{}, {==},
          Eq.and.left(D1.abnf.newline(nn),
        Bool.and(D1.g.ok.expr(ex2), D1.g.ok.lines(ls2)), hl)), ap.go(ls2, ex2, r2, s2, e2, ap.abk(com, T.LLine{},
        b2), q2, u2, l2, Eq.and.left(D1.g.ok.expr(ex2), D1.g.ok.lines(ls2), h1), Eq.and.right(D1.g.ok.expr(ex2),
        D1.g.ok.lines(ls2), h1), Eq.and.left(L4.ra.nokv.expr(ex2), L4.ra.nokv.lines(ls2), nl),
        Eq.and.right(L4.ra.nokv.expr(ex2), L4.ra.nokv.lines(ls2), nl)))),
        +bd => +eb => +rows => +heads => +here => ap.stays(D6.GLine{nn, ex2} <> ls2, bd, rows, heads, here, eb, nl))
