# the scan invariant and each full step that keeps it
import Base
import ../../main.bend as T
import ../../laws/ParsedIsWellFormed.bend as L1
import ./WellFormedTextWalk.bend as M1

# SCAN: an induction over parse's reading of a text, for any invariant of
# the scanner's state. doc.read reads a text in four modes (laws/ParsedIsWellFormed.bend's
# gd.md): a scanning state and one after a carriage return hold a state; an
# opening quote's mode holds the fields of the state the quote left; a plain
# string's mode holds a span of the source, the first n characters of cut.
# An invariant ii of states, with a predicate sp of a span against the text
# still to read, is kept by every character when each obligation below
# holds, and then holds of what parse returns in the form pd asks. The
# characters are those cp allows, in a text tx allows; laws/ParsedIsWellFormed.bend's good is
# the instance ii = good, sp = its span check, cp = wf.char. The invariant,
# the span predicate, the document's property and the obligations take a
# context gg of any type GG (laws/ParsedIsWellFormed.bend's is Unit; a key's is the key), since
# a template argument must be closed and cannot capture it. The invariant,
# the predicates and the obligations are template parameters (~), since an
# obligation is used once for every character and Bend copies a function
# only as a template argument; their names start with `_` because bolt's
# unused-parameter check does not see a template parameter's uses.

# a mode's invariant, over the text still to read
def si.md(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_sp: _GG -> String -> U32 -> String -> Bool,
  -gg: _GG,
  mode: T.Mode,
  -text: String
) -> Data:
  match mode:
    case T.MScan{st}:
      {_ii(gg, st) == True{} : Bool}
    case T.MCr{st}:
      {_ii(gg, st) == True{} : Bool}
    case T.MOpen{_basic, _q, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at}:
      {_ii(gg, T.St{bd, rw, hs, he, pt, bf, T.LQ{}, bk, qk, sk, T.HNone{}, un, lf, at,
        False{}}) == True{} : Bool}
    case T.MEat{_basic, _q, cut, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at}:
      {Bool.and(_ii(gg, T.St{bd, rw, hs, he, pt, [], T.LStr{}, T.LStr{}, qk, sk, T.HNone{}, un, lf,
        at, False{}}), _sp(gg, cut, nn, text)) == True{} : Bool}

# a plain string's state, as its span keeps it
def si.str(
  bd: String,
  rw: List<&2, T.Val>,
  hs: List<&2, String>,
  he: List<&2, String>,
  pt: List<&2, String>,
  bf: List<&2, Char>,
  qk: T.QKind,
  sk: List<&2, T.Ctx>,
  un: U32,
  lf: U32,
  at: Bool
) -> T.St:
  T.St{bd, rw, hs, he, pt, bf, T.LStr{}, T.LStr{}, qk, sk, T.HNone{}, un, lf, at, False{}}

# every full step keeps the invariant: one character read in any state
def si.OStep(~_GG: Data, ~_ii: _GG -> T.St -> Bool, ~_cp: Char -> Bool) -> Type:
  @gg: _GG -> @st: T.St -> {_ii(gg, st) == True{} : Bool} -> @cc: Char -> {_cp(cc) == True{} : Bool} ->
    {_ii(gg, T.read.step(st, cc)) == True{} : Bool}

# and so does reading a held character
def si.OOnce(~_GG: Data, ~_ii: _GG -> T.St -> Bool) -> Type:
  @gg: _GG -> @st: T.St -> {_ii(gg, st) == True{} : Bool} -> {_ii(gg, T.read.once2(st)) == True{} : Bool}

# the fast step's character pushed onto the buffer keeps it, in a state
# with no held character that is past the first
def si.OCons(~_GG: Data, ~_ii: _GG -> T.St -> Bool, ~_cp: Char -> Bool) -> Type:
  @gg: _GG -> @bd: String -> @rw: List<&2, T.Val> -> @hs: List<&2, String> -> @he: List<&2, String> ->
    @pt: List<&2, String> -> @bf: List<&2, Char> -> @lx: T.Lex -> @bk: T.Lex -> @qk: T.QKind ->
    @sk: List<&2, T.Ctx> -> @un: U32 -> @lf: U32 -> @at: Bool -> @cc: Char ->
    {_ii(gg, T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, T.HNone{}, un, lf, at, False{}})
      == True{} : Bool} -> {_cp(cc) == True{} : Bool} ->
    {_ii(gg, T.St{bd, rw, hs, he, pt, cc <> bf, lx, bk, qk, sk, T.HNone{}, un, lf, at,
      False{}}) == True{} : Bool}

# a failed step keeps it
def si.OErr(~_GG: Data, ~_ii: _GG -> T.St -> Bool) -> Type:
  @gg: _GG -> @st: T.St -> @why: String -> {String.is_empty(why) == False{} : Bool} -> {_ii(gg, st) == True{} : Bool} ->
    {_ii(gg, T.st.err(st, why)) == True{} : Bool}

# an opening quote's state that starts a span keeps it as the span's state
def si.OOpen(~_GG: Data, ~_ii: _GG -> T.St -> Bool) -> Type:
  @gg: _GG -> @bd: String -> @rw: List<&2, T.Val> -> @hs: List<&2, String> -> @he: List<&2, String> ->
    @pt: List<&2, String> -> @bk: T.Lex -> @qk: T.QKind -> @sk: List<&2, T.Ctx> -> @un: U32 ->
    @lf: U32 -> @at: Bool ->
    {_ii(gg, T.St{bd, rw, hs, he, pt, [], T.LQ{}, bk, qk, sk, T.HNone{}, un, lf, at, False{}})
      == True{} : Bool} ->
    {_ii(gg, si.str(bd, rw, hs, he, pt, [], qk, sk, un, lf, at)) == True{} : Bool}

# a span of one character, the text's first, holds sp against the rest
def si.OSp1(~_GG: Data, ~_sp: _GG -> String -> U32 -> String -> Bool, ~_cp: Char -> Bool, ~_tx: String -> Bool) -> Type:
  @gg: _GG -> @hh: Char -> @tt: String -> {_cp(hh) == True{} : Bool} -> {_tx(SCon{hh, tt}) == True{} : Bool} ->
    {_sp(gg, SCon{hh, tt}, 1, tt) == True{} : Bool}

# a span that takes the text's next character still holds sp
def si.OSpInc(
  ~_GG: Data,
  ~_sp: _GG -> String -> U32 -> String -> Bool,
  ~_cp: Char -> Bool,
  ~_tx: String -> Bool
) -> Type:
  @gg: _GG -> @cut: String -> @nn: U32 -> @hh: Char -> @tt: String -> {_sp(gg, cut, nn, SCon{hh,
    tt}) == True{} : Bool} ->
    {_cp(hh) == True{} : Bool} -> {_tx(SCon{hh, tt}) == True{} : Bool} -> {_sp(gg, cut, U32.add(nn, 1),
      tt) == True{} : Bool}

# a span that closes is placed as a VSpan and keeps it
def si.OClose(~_GG: Data, ~_ii: _GG -> T.St -> Bool, ~_sp: _GG -> String -> U32 -> String -> Bool) -> Type:
  @gg: _GG -> @bd: String -> @rw: List<&2, T.Val> -> @hs: List<&2, String> -> @he: List<&2, String> ->
    @pt: List<&2, String> -> @qk: T.QKind -> @sk: List<&2, T.Ctx> -> @un: U32 -> @lf: U32 ->
    @at: Bool -> @cut: String -> @nn: U32 -> @text: String ->
    {_ii(gg, si.str(bd, rw, hs, he, pt, [], qk, sk, un, lf, at)) == True{} : Bool} ->
    {_sp(gg, cut, nn, text) == True{} : Bool} ->
    {_ii(gg, T.val.take(si.str(bd, rw, hs, he, pt, [], qk, sk, un, lf, at), T.VSpan{cut, nn}))
      == True{} : Bool}

# a span copied to the buffer keeps it
def si.OCopy(~_GG: Data, ~_ii: _GG -> T.St -> Bool, ~_sp: _GG -> String -> U32 -> String -> Bool) -> Type:
  @gg: _GG -> @bd: String -> @rw: List<&2, T.Val> -> @hs: List<&2, String> -> @he: List<&2, String> ->
    @pt: List<&2, String> -> @qk: T.QKind -> @sk: List<&2, T.Ctx> -> @un: U32 -> @lf: U32 ->
    @at: Bool -> @cut: String -> @nn: U32 -> @text: String ->
    {_ii(gg, si.str(bd, rw, hs, he, pt, [], qk, sk, un, lf, at)) == True{} : Bool} ->
    {_sp(gg, cut, nn, text) == True{} : Bool} ->
    {_ii(gg, si.str(bd, rw, hs, he, pt, T.span.rev(cut, nn, U32.is_zero(nn), []), qk, sk, un, lf,
      at)) == True{} : Bool}

# a state at the end of the text gives what pd asks of the document
def si.OFin(~_GG: Data, ~_ii: _GG -> T.St -> Bool, ~_pd: _GG -> T.Doc -> Type) -> Type:
  @gg: _GG -> @st: T.St -> {_ii(gg, st) == True{} : Bool} -> _pd(gg, T.read.fin(st))

# and a span still open at the end
def si.OUnc(~_GG: Data, ~_ii: _GG -> T.St -> Bool, ~_pd: _GG -> T.Doc -> Type) -> Type:
  @gg: _GG -> @bd: String -> @rw: List<&2, T.Val> -> @hs: List<&2, String> -> @he: List<&2, String> ->
    @pt: List<&2, String> -> @qk: T.QKind -> @sk: List<&2, T.Ctx> -> @un: U32 -> @lf: U32 ->
    @at: Bool ->
    {_ii(gg, si.str(bd, rw, hs, he, pt, [], qk, sk, un, lf, at)) == True{} : Bool} ->
    _pd(gg, T.read.fin.unclosed(si.str(bd, rw, hs, he, pt, [], qk, sk, un, lf, at)))

# a text tx allows starts with a character cp allows
def si.OTxH(~_cp: Char -> Bool, ~_tx: String -> Bool) -> Type:
  @hh: Char -> @tt: String -> {_tx(SCon{hh, tt}) == True{} : Bool} -> {_cp(hh) == True{} : Bool}

# and goes on with a text tx allows
def si.OTxT(~_tx: String -> Bool) -> Type:
  @hh: Char -> @tt: String -> {_tx(SCon{hh, tt}) == True{} : Bool} -> {_tx(tt) == True{} : Bool}

# SCAN: the induction over the text, for any invariant (sip.read below).
# This is laws/ParsedIsWellFormed.bend's dispatch, span modes and induction (gd.fast, gd.mode
# step, gd_read) with good replaced by the invariant ii and its lemmas by the
# obligations: the fast step keeps a plain character in the buffer (si.OCons)
# or ignores it, and gives every other character, and a held one, to the
# full step (si.OStep, si.OOnce); a quote may open a span, which grows, closes
# or is copied to the buffer (si.OOpen, si.OSp1, si.OSpInc, si.OClose,
# si.OCopy); a carriage return must meet a line feed (si.OErr); and the text
# ends in a state (si.OFin) or in a span (si.OUnc).

# a state as the fast step builds it: no held character, past the first
def sip.S(
  bd: String,
  rw: List<&2, T.Val>,
  hs: List<&2, String>,
  he: List<&2, String>,
  pt: List<&2, String>,
  bf: List<&2, Char>,
  lx: T.Lex,
  bk: T.Lex,
  qk: T.QKind,
  sk: List<&2, T.Ctx>,
  un: U32,
  lf: U32,
  at: Bool
) -> T.St:
  T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, T.HNone{}, un, lf, at, False{}}

# the full step, from the fast step's state
def sip.fold(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_cp: Char -> Bool,
  ~_os: si.OStep(~_GG, ~_ii, ~_cp),
  ~_oo: si.OOnce(~_GG, ~_ii),
  ~_oc: si.OCons(~_GG, ~_ii, ~_cp),
  +gg: _GG,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +bf: List<&2, Char>,
  +lx: T.Lex,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +eg: {_ii(gg, sip.S(bd, rw, hs, he, pt, bf, lx, bk, qk, sk, un, lf, at)) == True{} : Bool},
  +cc: Char,
  +ec: {_cp(cc) == True{} : Bool}
) -> {_ii(gg, T.read.fast.old(bd, rw, hs, he, pt, bf, lx, bk, qk, sk, un, lf, at, cc)) == True{} : Bool}:
  _oo(gg, T.read.on.st(sip.S(bd, rw, hs, he, pt, bf, lx, bk, qk, sk, un, lf, at), cc), _os(gg, sip.S(bd, rw, hs, he,
    pt, bf,
    lx, bk, qk, sk, un, lf, at), eg, cc, ec))

# the character joins the buffer
def sip.fcons(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_cp: Char -> Bool,
  ~_os: si.OStep(~_GG, ~_ii, ~_cp),
  ~_oo: si.OOnce(~_GG, ~_ii),
  ~_oc: si.OCons(~_GG, ~_ii, ~_cp),
  +gg: _GG,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +bf: List<&2, Char>,
  +lx: T.Lex,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +eg: {_ii(gg, sip.S(bd, rw, hs, he, pt, bf, lx, bk, qk, sk, un, lf, at)) == True{} : Bool},
  +cc: Char,
  +ec: {_cp(cc) == True{} : Bool}
) -> {_ii(gg, T.read.fast.cons(bd, rw, hs, he, pt, bf, lx, bk, qk, sk, un, lf, at, cc)) == True{} : Bool}:
  _oc(gg, bd, rw, hs, he, pt, bf, lx, bk, qk, sk, un, lf, at, cc, eg, ec)

# a control takes the full step; a plain character is kept
def sip.fpush(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_cp: Char -> Bool,
  ~_os: si.OStep(~_GG, ~_ii, ~_cp),
  ~_oo: si.OOnce(~_GG, ~_ii),
  ~_oc: si.OCons(~_GG, ~_ii, ~_cp),
  +gg: _GG,
  ctrl: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +bf: List<&2, Char>,
  +lx: T.Lex,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +eg: {_ii(gg, sip.S(bd, rw, hs, he, pt, bf, lx, bk, qk, sk, un, lf, at)) == True{} : Bool},
  +cc: Char,
  +ec: {_cp(cc) == True{} : Bool}
) -> {_ii(gg, T.read.fast.push(ctrl, bd, rw, hs, he, pt, bf, lx, bk, qk, sk, un, lf, at, cc)) == True{} : Bool}:
  match ctrl:
    case False{}:
      sip.fcons(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, bd, rw, hs, he, pt, bf, lx, bk, qk, sk, un, lf, at, eg, cc, ec)
    case True{}:
      sip.fold(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, bd, rw, hs, he, pt, bf, lx, bk, qk, sk, un, lf, at, eg, cc, ec)

# a backslash in a basic string takes the full step
def sip.fbbs(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_cp: Char -> Bool,
  ~_os: si.OStep(~_GG, ~_ii, ~_cp),
  ~_oo: si.OOnce(~_GG, ~_ii),
  ~_oc: si.OCons(~_GG, ~_ii, ~_cp),
  +gg: _GG,
  bs: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +bf: List<&2, Char>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +eg: {_ii(gg, sip.S(bd, rw, hs, he, pt, bf, T.LStr{}, bk, T.QBasic{}, sk, un, lf, at)) == True{} : Bool},
  +cc: Char,
  +ec: {_cp(cc) == True{} : Bool}
) -> {_ii(gg, T.read.fast.basic.bs(bs, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc)) == True{} : Bool}:
  match bs:
    case True{}:
      sip.fold(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, bd, rw, hs, he, pt, bf, T.LStr{}, bk, T.QBasic{}, sk, un, lf,
        at, eg, cc,
        ec)
    case False{}:
      sip.fpush(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, T.str.bad(Char.to_u32(cc), False{}), bd, rw, hs, he, pt, bf,
        T.LStr{},
        bk, T.QBasic{}, sk, un, lf, at, eg, cc, ec)

# a quote in a basic string takes the full step
def sip.fbasic(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_cp: Char -> Bool,
  ~_os: si.OStep(~_GG, ~_ii, ~_cp),
  ~_oo: si.OOnce(~_GG, ~_ii),
  ~_oc: si.OCons(~_GG, ~_ii, ~_cp),
  +gg: _GG,
  quote: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +bf: List<&2, Char>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +eg: {_ii(gg, sip.S(bd, rw, hs, he, pt, bf, T.LStr{}, bk, T.QBasic{}, sk, un, lf, at)) == True{} : Bool},
  +cc: Char,
  +ec: {_cp(cc) == True{} : Bool}
) -> {_ii(gg, T.read.fast.basic(quote, Char.is_eq(cc, '\\'), bd, rw, hs, he, pt, bf, bk, sk, un, lf, at,
  cc)) == True{} : Bool}:
  match quote:
    case True{}:
      sip.fold(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, bd, rw, hs, he, pt, bf, T.LStr{}, bk, T.QBasic{}, sk, un, lf,
        at, eg, cc,
        ec)
    case False{}:
      sip.fbbs(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, Char.is_eq(cc, '\\'), bd, rw, hs, he, pt, bf, bk, sk, un, lf,
        at, eg, cc,
        ec)

# a quote in a literal string takes the full step
def sip.flit(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_cp: Char -> Bool,
  ~_os: si.OStep(~_GG, ~_ii, ~_cp),
  ~_oo: si.OOnce(~_GG, ~_ii),
  ~_oc: si.OCons(~_GG, ~_ii, ~_cp),
  +gg: _GG,
  quote: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +bf: List<&2, Char>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +eg: {_ii(gg, sip.S(bd, rw, hs, he, pt, bf, T.LStr{}, bk, T.QLit{}, sk, un, lf, at)) == True{} : Bool},
  +cc: Char,
  +ec: {_cp(cc) == True{} : Bool}
) -> {_ii(gg, T.read.fast.lit(quote, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc)) == True{} : Bool}:
  match quote:
    case True{}:
      sip.fold(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, bd, rw, hs, he, pt, bf, T.LStr{}, bk, T.QLit{}, sk, un, lf, at,
        eg, cc, ec)
    case False{}:
      sip.fpush(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, T.str.bad(Char.to_u32(cc), False{}), bd, rw, hs, he, pt, bf,
        T.LStr{},
        bk, T.QLit{}, sk, un, lf, at, eg, cc, ec)

# one character of a string on the fast step
def sip.fstr(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_cp: Char -> Bool,
  ~_os: si.OStep(~_GG, ~_ii, ~_cp),
  ~_oo: si.OOnce(~_GG, ~_ii),
  ~_oc: si.OCons(~_GG, ~_ii, ~_cp),
  +gg: _GG,
  qk: T.QKind,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +bf: List<&2, Char>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +eg: {_ii(gg, sip.S(bd, rw, hs, he, pt, bf, T.LStr{}, bk, qk, sk, un, lf, at)) == True{} : Bool},
  +cc: Char,
  +ec: {_cp(cc) == True{} : Bool}
) -> {_ii(gg, T.read.fast.str(qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc)) == True{} : Bool}:
  match qk:
    case T.QBasic{}:
      sip.fbasic(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, Char.is_eq(cc, '"'), bd, rw, hs, he, pt, bf, bk, sk, un, lf,
        at, eg,
        cc, ec)
    case T.QLit{}:
      sip.flit(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, Char.is_eq(cc, '\''), bd, rw, hs, he, pt, bf, bk, sk, un, lf,
        at, eg, cc,
        ec)
    case T.QMulti{}:
      sip.fold(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, bd, rw, hs, he, pt, bf, T.LStr{}, bk, T.QMulti{}, sk, un, lf,
        at, eg, cc,
        ec)
    case T.QMultiLit{}:
      sip.fold(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, bd, rw, hs, he, pt, bf, T.LStr{}, bk, T.QMultiLit{}, sk, un,
        lf, at, eg,
        cc, ec)

# one character of a bare key on the fast step
def sip.fkey(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_cp: Char -> Bool,
  ~_os: si.OStep(~_GG, ~_ii, ~_cp),
  ~_oo: si.OOnce(~_GG, ~_ii),
  ~_oc: si.OCons(~_GG, ~_ii, ~_cp),
  +gg: _GG,
  ok: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +bf: List<&2, Char>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +eg: {_ii(gg, sip.S(bd, rw, hs, he, pt, bf, T.LKey{}, bk, qk, sk, un, lf, at)) == True{} : Bool},
  +cc: Char,
  +ec: {_cp(cc) == True{} : Bool}
) -> {_ii(gg, T.read.fast.key(ok, bd, rw, hs, he, pt, bf, bk, qk, sk, un, lf, at, cc)) == True{} : Bool}:
  match ok:
    case True{}:
      sip.fcons(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, bd, rw, hs, he, pt, bf, T.LKey{}, bk, qk, sk, un, lf, at, eg,
        cc, ec)
    case False{}:
      sip.fold(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, bd, rw, hs, he, pt, bf, T.LKey{}, bk, qk, sk, un, lf, at, eg,
        cc, ec)

# one character of a bare value on the fast step
def sip.fbare(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_cp: Char -> Bool,
  ~_os: si.OStep(~_GG, ~_ii, ~_cp),
  ~_oo: si.OOnce(~_GG, ~_ii),
  ~_oc: si.OCons(~_GG, ~_ii, ~_cp),
  +gg: _GG,
  delim: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +bf: List<&2, Char>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +eg: {_ii(gg, sip.S(bd, rw, hs, he, pt, bf, T.LBare{}, bk, qk, sk, un, lf, at)) == True{} : Bool},
  +cc: Char,
  +ec: {_cp(cc) == True{} : Bool}
) -> {_ii(gg, T.read.fast.bare(delim, bd, rw, hs, he, pt, bf, bk, qk, sk, un, lf, at, cc)) == True{} : Bool}:
  match delim:
    case True{}:
      sip.fold(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, bd, rw, hs, he, pt, bf, T.LBare{}, bk, qk, sk, un, lf, at, eg,
        cc, ec)
    case False{}:
      sip.fcons(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, bd, rw, hs, he, pt, bf, T.LBare{}, bk, qk, sk, un, lf, at, eg,
        cc, ec)

# one character of a comment on the fast step
def sip.fcom(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_cp: Char -> Bool,
  ~_os: si.OStep(~_GG, ~_ii, ~_cp),
  ~_oo: si.OOnce(~_GG, ~_ii),
  ~_oc: si.OCons(~_GG, ~_ii, ~_cp),
  +gg: _GG,
  ctl: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +bf: List<&2, Char>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +eg: {_ii(gg, sip.S(bd, rw, hs, he, pt, bf, T.LCom{}, bk, qk, sk, un, lf, at)) == True{} : Bool},
  +cc: Char,
  +ec: {_cp(cc) == True{} : Bool}
) -> {_ii(gg, T.read.fast.com(ctl, bd, rw, hs, he, pt, bf, bk, qk, sk, un, lf, at, cc)) == True{} : Bool}:
  match ctl:
    case True{}:
      sip.fold(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, bd, rw, hs, he, pt, bf, T.LCom{}, bk, qk, sk, un, lf, at, eg,
        cc, ec)
    case False{}:
      eg

# a newline this state ignores
def sip.fkeep(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_cp: Char -> Bool,
  ~_os: si.OStep(~_GG, ~_ii, ~_cp),
  ~_oo: si.OOnce(~_GG, ~_ii),
  ~_oc: si.OCons(~_GG, ~_ii, ~_cp),
  +gg: _GG,
  keep: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +bf: List<&2, Char>,
  +lx: T.Lex,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +eg: {_ii(gg, sip.S(bd, rw, hs, he, pt, bf, lx, bk, qk, sk, un, lf, at)) == True{} : Bool},
  +cc: Char,
  +ec: {_cp(cc) == True{} : Bool}
) -> {_ii(gg, T.read.fast.ws.keep(keep, bd, rw, hs, he, pt, bf, lx, bk, qk, sk, un, lf, at, cc)) == True{} : Bool}:
  match keep:
    case True{}:
      eg
    case False{}:
      sip.fold(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, bd, rw, hs, he, pt, bf, lx, bk, qk, sk, un, lf, at, eg, cc, ec)

# a newline, or the full step
def sip.fwsnl(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_cp: Char -> Bool,
  ~_os: si.OStep(~_GG, ~_ii, ~_cp),
  ~_oo: si.OOnce(~_GG, ~_ii),
  ~_oc: si.OCons(~_GG, ~_ii, ~_cp),
  +gg: _GG,
  nl: Bool,
  +keep: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +bf: List<&2, Char>,
  +lx: T.Lex,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +eg: {_ii(gg, sip.S(bd, rw, hs, he, pt, bf, lx, bk, qk, sk, un, lf, at)) == True{} : Bool},
  +cc: Char,
  +ec: {_cp(cc) == True{} : Bool}
) -> {_ii(gg, T.read.fast.ws.nl(nl, keep, bd, rw, hs, he, pt, bf, lx, bk, qk, sk, un, lf, at, cc)) == True{} : Bool}:
  match nl:
    case True{}:
      sip.fkeep(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, keep, bd, rw, hs, he, pt, bf, lx, bk, qk, sk, un, lf, at, eg,
        cc, ec)
    case False{}:
      sip.fold(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, bd, rw, hs, he, pt, bf, lx, bk, qk, sk, un, lf, at, eg, cc, ec)

# blank space this state ignores
def sip.fws(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_cp: Char -> Bool,
  ~_os: si.OStep(~_GG, ~_ii, ~_cp),
  ~_oo: si.OOnce(~_GG, ~_ii),
  ~_oc: si.OCons(~_GG, ~_ii, ~_cp),
  +gg: _GG,
  _sp: Bool,
  +nl: Bool,
  +keep: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +bf: List<&2, Char>,
  +lx: T.Lex,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +eg: {_ii(gg, sip.S(bd, rw, hs, he, pt, bf, lx, bk, qk, sk, un, lf, at)) == True{} : Bool},
  +cc: Char,
  +ec: {_cp(cc) == True{} : Bool}
) -> {_ii(gg, T.read.fast.ws(_sp, nl, keep, bd, rw, hs, he, pt, bf, lx, bk, qk, sk, un, lf, at, cc)) == True{} : Bool}:
  match _sp:
    case True{}:
      eg
    case False{}:
      sip.fwsnl(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, nl, keep, bd, rw, hs, he, pt, bf, lx, bk, qk, sk, un, lf, at,
        eg, cc, ec)

# the fast step, by the state
def sip.flex(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_cp: Char -> Bool,
  ~_os: si.OStep(~_GG, ~_ii, ~_cp),
  ~_oo: si.OOnce(~_GG, ~_ii),
  ~_oc: si.OCons(~_GG, ~_ii, ~_cp),
  +gg: _GG,
  lx: T.Lex,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +bf: List<&2, Char>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +eg: {_ii(gg, sip.S(bd, rw, hs, he, pt, bf, lx, bk, qk, sk, un, lf, at)) == True{} : Bool},
  +cc: Char,
  +ec: {_cp(cc) == True{} : Bool}
) -> {_ii(gg, T.read.fast.lex(lx, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc)) == True{} : Bool}:
  match lx:
    case T.LTop{}:
      sip.fws(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, T.ch.sp(cc), T.ch.nl(cc), True{}, bd, rw, hs, he, pt, bf,
        T.LTop{}, bk,
        qk, sk, un, lf, at, eg, cc, ec)
    case T.LLine{}:
      sip.fws(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, T.ch.sp(cc), T.ch.nl(cc), False{}, bd, rw, hs, he, pt, bf,
        T.LLine{}, bk,
        qk, sk, un, lf, at, eg, cc, ec)
    case T.LKey{}:
      sip.fkey(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, T.bare.at(cc), bd, rw, hs, he, pt, bf, bk, qk, sk, un, lf, at,
        eg, cc, ec)
    case T.LKeyDot{}:
      sip.fold(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, bd, rw, hs, he, pt, bf, T.LKeyDot{}, bk, qk, sk, un, lf, at,
        eg, cc, ec)
    case T.LAfter{}:
      sip.fws(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, T.ch.sp(cc), T.ch.nl(cc), False{}, bd, rw, hs, he, pt, bf,
        T.LAfter{}, bk,
        qk, sk, un, lf, at, eg, cc, ec)
    case T.LKeyQ{}:
      sip.fold(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, bd, rw, hs, he, pt, bf, T.LKeyQ{}, bk, qk, sk, un, lf, at, eg,
        cc, ec)
    case T.LKeyE{}:
      sip.fold(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, bd, rw, hs, he, pt, bf, T.LKeyE{}, bk, qk, sk, un, lf, at, eg,
        cc, ec)
    case T.LKeyU{}:
      sip.fold(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, bd, rw, hs, he, pt, bf, T.LKeyU{}, bk, qk, sk, un, lf, at, eg,
        cc, ec)
    case T.LVal{}:
      sip.fws(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, T.ch.sp(cc), T.ch.nl(cc), False{}, bd, rw, hs, he, pt, bf,
        T.LVal{}, bk,
        qk, sk, un, lf, at, eg, cc, ec)
    case T.LQ{}:
      sip.fold(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, bd, rw, hs, he, pt, bf, T.LQ{}, bk, qk, sk, un, lf, at, eg, cc,
        ec)
    case T.LQ2{}:
      sip.fold(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, bd, rw, hs, he, pt, bf, T.LQ2{}, bk, qk, sk, un, lf, at, eg,
        cc, ec)
    case T.LStr{}:
      sip.fstr(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, eg, cc, ec)
    case T.LEsc{}:
      sip.fold(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, bd, rw, hs, he, pt, bf, T.LEsc{}, bk, qk, sk, un, lf, at, eg,
        cc, ec)
    case T.LUni{}:
      sip.fold(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, bd, rw, hs, he, pt, bf, T.LUni{}, bk, qk, sk, un, lf, at, eg,
        cc, ec)
    case T.LFold{}:
      sip.fold(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, bd, rw, hs, he, pt, bf, T.LFold{}, bk, qk, sk, un, lf, at, eg,
        cc, ec)
    case T.LMq{}:
      sip.fold(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, bd, rw, hs, he, pt, bf, T.LMq{}, bk, qk, sk, un, lf, at, eg,
        cc, ec)
    case T.LMqEnd{}:
      sip.fold(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, bd, rw, hs, he, pt, bf, T.LMqEnd{}, bk, qk, sk, un, lf, at, eg,
        cc, ec)
    case T.LTrim{}:
      sip.fold(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, bd, rw, hs, he, pt, bf, T.LTrim{}, bk, qk, sk, un, lf, at, eg,
        cc, ec)
    case T.LTrim2{}:
      sip.fold(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, bd, rw, hs, he, pt, bf, T.LTrim2{}, bk, qk, sk, un, lf, at, eg,
        cc, ec)
    case T.LBare{}:
      sip.fbare(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, T.ch.delim(cc), bd, rw, hs, he, pt, bf, bk, qk, sk, un, lf,
        at, eg, cc,
        ec)
    case T.LDate{}:
      sip.fold(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, bd, rw, hs, he, pt, bf, T.LDate{}, bk, qk, sk, un, lf, at, eg,
        cc, ec)
    case T.LCom{}:
      sip.fcom(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, T.ch.ctl(cc), bd, rw, hs, he, pt, bf, bk, qk, sk, un, lf, at,
        eg, cc, ec)
    case T.LHead{}:
      sip.fold(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, bd, rw, hs, he, pt, bf, T.LHead{}, bk, qk, sk, un, lf, at, eg,
        cc, ec)
    case T.LHeadGap{}:
      sip.fold(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, bd, rw, hs, he, pt, bf, T.LHeadGap{}, bk, qk, sk, un, lf, at,
        eg, cc, ec)
    case T.LHeadDot{}:
      sip.fold(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, bd, rw, hs, he, pt, bf, T.LHeadDot{}, bk, qk, sk, un, lf, at,
        eg, cc, ec)
    case T.LHeadQ{}:
      sip.fold(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, bd, rw, hs, he, pt, bf, T.LHeadQ{}, bk, qk, sk, un, lf, at, eg,
        cc, ec)
    case T.LHeadE{}:
      sip.fold(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, bd, rw, hs, he, pt, bf, T.LHeadE{}, bk, qk, sk, un, lf, at, eg,
        cc, ec)
    case T.LHeadU{}:
      sip.fold(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, bd, rw, hs, he, pt, bf, T.LHeadU{}, bk, qk, sk, un, lf, at, eg,
        cc, ec)
    case T.LHeadR{}:
      sip.fold(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, bd, rw, hs, he, pt, bf, T.LHeadR{}, bk, qk, sk, un, lf, at, eg,
        cc, ec)
    case T.LArr{}:
      sip.fws(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, T.ch.sp(cc), T.ch.nl(cc), True{}, bd, rw, hs, he, pt, bf,
        T.LArr{}, bk,
        qk, sk, un, lf, at, eg, cc, ec)
    case T.LArrC{}:
      sip.fws(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, T.ch.sp(cc), T.ch.nl(cc), True{}, bd, rw, hs, he, pt, bf,
        T.LArrC{}, bk,
        qk, sk, un, lf, at, eg, cc, ec)
    case T.LInl{}:
      sip.fws(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, T.ch.sp(cc), T.ch.nl(cc), False{}, bd, rw, hs, he, pt, bf,
        T.LInl{}, bk,
        qk, sk, un, lf, at, eg, cc, ec)
    case T.LInlK{}:
      sip.fws(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, T.ch.sp(cc), T.ch.nl(cc), False{}, bd, rw, hs, he, pt, bf,
        T.LInlK{}, bk,
        qk, sk, un, lf, at, eg, cc, ec)
    case T.LInlC{}:
      sip.fws(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, T.ch.sp(cc), T.ch.nl(cc), False{}, bd, rw, hs, he, pt, bf,
        T.LInlC{}, bk,
        qk, sk, un, lf, at, eg, cc, ec)
    case T.LSink{}:
      sip.fold(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, bd, rw, hs, he, pt, bf, T.LSink{}, bk, qk, sk, un, lf, at, eg,
        cc, ec)

# the first character takes the full step
def sip.flead(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_cp: Char -> Bool,
  ~_os: si.OStep(~_GG, ~_ii, ~_cp),
  ~_oo: si.OOnce(~_GG, ~_ii),
  ~_oc: si.OCons(~_GG, ~_ii, ~_cp),
  +gg: _GG,
  lead: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +bf: List<&2, Char>,
  +lx: T.Lex,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +eg: {_ii(gg, T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, T.HNone{}, un, lf, at, lead}) == True{} : Bool},
  +cc: Char,
  +ec: {_cp(cc) == True{} : Bool}
) -> {_ii(gg, T.read.fast.lead(lead, lx, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc)) == True{} : Bool}:
  match lead:
    case True{}:
      _oo(gg, T.read.step(T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, T.HNone{}, un, lf, at, True{}}, cc), _os(gg,
        T.St{bd,
        rw, hs, he, pt, bf, lx, bk, qk, sk, T.HNone{}, un, lf, at, True{}}, eg, cc, ec))
    case False{}:
      sip.flex(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, lx, bd, rw, hs, he, pt, bf, bk, qk, sk, un, lf, at, eg, cc, ec)

# a held character takes the full step first
def sip.fhold(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_cp: Char -> Bool,
  ~_os: si.OStep(~_GG, ~_ii, ~_cp),
  ~_oo: si.OOnce(~_GG, ~_ii),
  ~_oc: si.OCons(~_GG, ~_ii, ~_cp),
  +gg: _GG,
  hold: T.Hold,
  +lead: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +bf: List<&2, Char>,
  +lx: T.Lex,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +eg: {_ii(gg, T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, hold, un, lf, at, lead}) == True{} : Bool},
  +cc: Char,
  +ec: {_cp(cc) == True{} : Bool}
) -> {_ii(gg, T.read.fast.hold(hold, lead, lx, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc)) == True{} : Bool}:
  match hold:
    case T.HChar{+held}:
      _oo(gg, T.read.step(T.read.once2(T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, T.HChar{held}, un, lf, at, lead}),
        cc), _os(gg, T.read.once2(T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, T.HChar{held}, un, lf, at, lead}),
          _oo(gg, T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, T.HChar{held}, un, lf, at, lead}, eg), cc, ec))
    case T.HNone{}:
      sip.flead(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, lead, bd, rw, hs, he, pt, bf, lx, bk, qk, sk, un, lf, at, eg,
        cc, ec)

# one character by the fast step
def sip.fast(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_cp: Char -> Bool,
  ~_os: si.OStep(~_GG, ~_ii, ~_cp),
  ~_oo: si.OOnce(~_GG, ~_ii),
  ~_oc: si.OCons(~_GG, ~_ii, ~_cp),
  +gg: _GG,
  +st: T.St,
  +eg: {_ii(gg, st) == True{} : Bool},
  +cc: Char,
  +ec: {_cp(cc) == True{} : Bool}
) -> {_ii(gg, T.read.fast(st, cc)) == True{} : Bool}:
  match st:
    case T.St{+bd, +rw, +hs, +he, +pt, +bf, +lx, +bk, +qk, +sk, +hold, +un, +lf, +at,
      +lead}:
      sip.fhold(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, hold, lead, bd, rw, hs, he, pt, bf, lx, bk, qk, sk, un, lf,
        at, eg, cc,
        ec)

# a quote's state: a one-line string opens a span unless a character is held
# or it is the first character; every other state scans on
def sip.wlex(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_sp: _GG -> String -> U32 -> String -> Bool,
  ~_cp: Char -> Bool,
  ~_tx: String -> Bool,
  ~_pd: _GG -> T.Doc -> Type,
  ~_os: si.OStep(~_GG, ~_ii, ~_cp),
  ~_oo: si.OOnce(~_GG, ~_ii),
  ~_oc: si.OCons(~_GG, ~_ii, ~_cp),
  ~_oe: si.OErr(~_GG, ~_ii),
  ~_oq: si.OOpen(~_GG, ~_ii),
  ~_o1: si.OSp1(~_GG, ~_sp, ~_cp, ~_tx),
  ~_oi: si.OSpInc(~_GG, ~_sp, ~_cp, ~_tx),
  ~_ol: si.OClose(~_GG, ~_ii, ~_sp),
  ~_oy: si.OCopy(~_GG, ~_ii, ~_sp),
  ~_of: si.OFin(~_GG, ~_ii, ~_pd),
  ~_ou: si.OUnc(~_GG, ~_ii, ~_pd),
  ~_oh: si.OTxH(~_cp, ~_tx),
  ~_ot: si.OTxT(~_tx),
  +gg: _GG,
  lx: T.Lex,
  hd: T.Hold,
  ld: Bool,
  qk: T.QKind,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +bf: List<&2, Char>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +tl: String,
  +eg: {_ii(gg, T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, hd, un, lf, at, ld}) == True{} : Bool}
) -> si.md(~_GG, ~_ii, ~_sp, gg, T.doc.wrap.lex(lx, bd, rw, hs, he, pt, bf, bk, qk, sk, hd, un, lf, at, ld), tl):
  match lx:
    case T.LTop{}:
      eg
    case T.LLine{}:
      eg
    case T.LKey{}:
      eg
    case T.LKeyDot{}:
      eg
    case T.LAfter{}:
      eg
    case T.LKeyQ{}:
      eg
    case T.LKeyE{}:
      eg
    case T.LKeyU{}:
      eg
    case T.LVal{}:
      eg
    case T.LQ{}:
      match hd:
        case T.HChar{_held}:
          eg
        case T.HNone{}:
          match ld:
            case True{}:
              eg
            case False{}:
              match qk:
                case T.QBasic{}:
                  eg
                case T.QLit{}:
                  eg
                case T.QMulti{}:
                  eg
                case T.QMultiLit{}:
                  eg
    case T.LQ2{}:
      eg
    case T.LStr{}:
      eg
    case T.LEsc{}:
      eg
    case T.LUni{}:
      eg
    case T.LFold{}:
      eg
    case T.LMq{}:
      eg
    case T.LMqEnd{}:
      eg
    case T.LTrim{}:
      eg
    case T.LTrim2{}:
      eg
    case T.LBare{}:
      eg
    case T.LDate{}:
      eg
    case T.LCom{}:
      eg
    case T.LHead{}:
      eg
    case T.LHeadGap{}:
      eg
    case T.LHeadDot{}:
      eg
    case T.LHeadQ{}:
      eg
    case T.LHeadE{}:
      eg
    case T.LHeadU{}:
      eg
    case T.LHeadR{}:
      eg
    case T.LArr{}:
      eg
    case T.LArrC{}:
      eg
    case T.LInl{}:
      eg
    case T.LInlK{}:
      eg
    case T.LInlC{}:
      eg
    case T.LSink{}:
      eg

# a state a quote may have opened a string in
def sip.wrap(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_sp: _GG -> String -> U32 -> String -> Bool,
  ~_cp: Char -> Bool,
  ~_tx: String -> Bool,
  ~_pd: _GG -> T.Doc -> Type,
  ~_os: si.OStep(~_GG, ~_ii, ~_cp),
  ~_oo: si.OOnce(~_GG, ~_ii),
  ~_oc: si.OCons(~_GG, ~_ii, ~_cp),
  ~_oe: si.OErr(~_GG, ~_ii),
  ~_oq: si.OOpen(~_GG, ~_ii),
  ~_o1: si.OSp1(~_GG, ~_sp, ~_cp, ~_tx),
  ~_oi: si.OSpInc(~_GG, ~_sp, ~_cp, ~_tx),
  ~_ol: si.OClose(~_GG, ~_ii, ~_sp),
  ~_oy: si.OCopy(~_GG, ~_ii, ~_sp),
  ~_of: si.OFin(~_GG, ~_ii, ~_pd),
  ~_ou: si.OUnc(~_GG, ~_ii, ~_pd),
  ~_oh: si.OTxH(~_cp, ~_tx),
  ~_ot: si.OTxT(~_tx),
  +gg: _GG,
  +st: T.St,
  +tl: String,
  +eg: {_ii(gg, st) == True{} : Bool}
) -> si.md(~_GG, ~_ii, ~_sp, gg, T.doc.wrap(st), tl):
  match st:
    case T.St{+bd, +rw, +hs, +he, +pt, +bf, +lx, +bk, +qk, +sk, +hd, +un, +lf, +at, +ld}:
      sip.wlex(~_GG, ~_ii, ~_sp, ~_cp, ~_tx, ~_pd, ~_os, ~_oo, ~_oc, ~_oe, ~_oq, ~_o1, ~_oi, ~_ol, ~_oy, ~_of, ~_ou,
        ~_oh,
        ~_ot, gg, lx, hd, ld, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, tl, eg)

# a carriage return, or another character
def sip.scr(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_sp: _GG -> String -> U32 -> String -> Bool,
  ~_cp: Char -> Bool,
  ~_tx: String -> Bool,
  ~_pd: _GG -> T.Doc -> Type,
  ~_os: si.OStep(~_GG, ~_ii, ~_cp),
  ~_oo: si.OOnce(~_GG, ~_ii),
  ~_oc: si.OCons(~_GG, ~_ii, ~_cp),
  ~_oe: si.OErr(~_GG, ~_ii),
  ~_oq: si.OOpen(~_GG, ~_ii),
  ~_o1: si.OSp1(~_GG, ~_sp, ~_cp, ~_tx),
  ~_oi: si.OSpInc(~_GG, ~_sp, ~_cp, ~_tx),
  ~_ol: si.OClose(~_GG, ~_ii, ~_sp),
  ~_oy: si.OCopy(~_GG, ~_ii, ~_sp),
  ~_of: si.OFin(~_GG, ~_ii, ~_pd),
  ~_ou: si.OUnc(~_GG, ~_ii, ~_pd),
  ~_oh: si.OTxH(~_cp, ~_tx),
  ~_ot: si.OTxT(~_tx),
  +gg: _GG,
  cr: Bool,
  +st: T.St,
  +cc: Char,
  +tl: String,
  +eg: {_ii(gg, st) == True{} : Bool},
  +ec: {_cp(cc) == True{} : Bool}
) -> si.md(~_GG, ~_ii, ~_sp, gg, T.doc.scan.cr(cr, st, cc), tl):
  match cr:
    case True{}:
      sip.fast(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, st, eg, cc, ec)
    case False{}:
      sip.fast(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, st, eg, cc, ec)

# an apostrophe, or another character
def sip.ssq(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_sp: _GG -> String -> U32 -> String -> Bool,
  ~_cp: Char -> Bool,
  ~_tx: String -> Bool,
  ~_pd: _GG -> T.Doc -> Type,
  ~_os: si.OStep(~_GG, ~_ii, ~_cp),
  ~_oo: si.OOnce(~_GG, ~_ii),
  ~_oc: si.OCons(~_GG, ~_ii, ~_cp),
  ~_oe: si.OErr(~_GG, ~_ii),
  ~_oq: si.OOpen(~_GG, ~_ii),
  ~_o1: si.OSp1(~_GG, ~_sp, ~_cp, ~_tx),
  ~_oi: si.OSpInc(~_GG, ~_sp, ~_cp, ~_tx),
  ~_ol: si.OClose(~_GG, ~_ii, ~_sp),
  ~_oy: si.OCopy(~_GG, ~_ii, ~_sp),
  ~_of: si.OFin(~_GG, ~_ii, ~_pd),
  ~_ou: si.OUnc(~_GG, ~_ii, ~_pd),
  ~_oh: si.OTxH(~_cp, ~_tx),
  ~_ot: si.OTxT(~_tx),
  +gg: _GG,
  sq: Bool,
  +cr: Bool,
  +st: T.St,
  +cc: Char,
  +tl: String,
  +eg: {_ii(gg, st) == True{} : Bool},
  +ec: {_cp(cc) == True{} : Bool}
) -> si.md(~_GG, ~_ii, ~_sp, gg, T.doc.scan.sq(sq, cr, st, cc), tl):
  match sq:
    case True{}:
      sip.wrap(~_GG, ~_ii, ~_sp, ~_cp, ~_tx, ~_pd, ~_os, ~_oo, ~_oc, ~_oe, ~_oq, ~_o1, ~_oi, ~_ol, ~_oy, ~_of, ~_ou,
        ~_oh,
        ~_ot, gg, T.read.fast(st, cc), tl, sip.fast(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, st, eg, cc, ec))
    case False{}:
      sip.scr(~_GG, ~_ii, ~_sp, ~_cp, ~_tx, ~_pd, ~_os, ~_oo, ~_oc, ~_oe, ~_oq, ~_o1, ~_oi, ~_ol, ~_oy, ~_of, ~_ou,
        ~_oh,
        ~_ot, gg, cr, st, cc, tl, eg, ec)

# a quote, or another character
def sip.sdq(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_sp: _GG -> String -> U32 -> String -> Bool,
  ~_cp: Char -> Bool,
  ~_tx: String -> Bool,
  ~_pd: _GG -> T.Doc -> Type,
  ~_os: si.OStep(~_GG, ~_ii, ~_cp),
  ~_oo: si.OOnce(~_GG, ~_ii),
  ~_oc: si.OCons(~_GG, ~_ii, ~_cp),
  ~_oe: si.OErr(~_GG, ~_ii),
  ~_oq: si.OOpen(~_GG, ~_ii),
  ~_o1: si.OSp1(~_GG, ~_sp, ~_cp, ~_tx),
  ~_oi: si.OSpInc(~_GG, ~_sp, ~_cp, ~_tx),
  ~_ol: si.OClose(~_GG, ~_ii, ~_sp),
  ~_oy: si.OCopy(~_GG, ~_ii, ~_sp),
  ~_of: si.OFin(~_GG, ~_ii, ~_pd),
  ~_ou: si.OUnc(~_GG, ~_ii, ~_pd),
  ~_oh: si.OTxH(~_cp, ~_tx),
  ~_ot: si.OTxT(~_tx),
  +gg: _GG,
  dq: Bool,
  +sq: Bool,
  +cr: Bool,
  +st: T.St,
  +cc: Char,
  +tl: String,
  +eg: {_ii(gg, st) == True{} : Bool},
  +ec: {_cp(cc) == True{} : Bool}
) -> si.md(~_GG, ~_ii, ~_sp, gg, T.doc.scan.q(dq, sq, cr, st, cc), tl):
  match dq:
    case True{}:
      sip.wrap(~_GG, ~_ii, ~_sp, ~_cp, ~_tx, ~_pd, ~_os, ~_oo, ~_oc, ~_oe, ~_oq, ~_o1, ~_oi, ~_ol, ~_oy, ~_of, ~_ou,
        ~_oh,
        ~_ot, gg, T.read.fast(st, cc), tl, sip.fast(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, st, eg, cc, ec))
    case False{}:
      sip.ssq(~_GG, ~_ii, ~_sp, ~_cp, ~_tx, ~_pd, ~_os, ~_oo, ~_oc, ~_oe, ~_oq, ~_o1, ~_oi, ~_ol, ~_oy, ~_of, ~_ou,
        ~_oh,
        ~_ot, gg, sq, cr, st, cc, tl, eg, ec)

# a line feed after a carriage return, or the error
def sip.dcr(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_sp: _GG -> String -> U32 -> String -> Bool,
  ~_cp: Char -> Bool,
  ~_tx: String -> Bool,
  ~_pd: _GG -> T.Doc -> Type,
  ~_os: si.OStep(~_GG, ~_ii, ~_cp),
  ~_oo: si.OOnce(~_GG, ~_ii),
  ~_oc: si.OCons(~_GG, ~_ii, ~_cp),
  ~_oe: si.OErr(~_GG, ~_ii),
  ~_oq: si.OOpen(~_GG, ~_ii),
  ~_o1: si.OSp1(~_GG, ~_sp, ~_cp, ~_tx),
  ~_oi: si.OSpInc(~_GG, ~_sp, ~_cp, ~_tx),
  ~_ol: si.OClose(~_GG, ~_ii, ~_sp),
  ~_oy: si.OCopy(~_GG, ~_ii, ~_sp),
  ~_of: si.OFin(~_GG, ~_ii, ~_pd),
  ~_ou: si.OUnc(~_GG, ~_ii, ~_pd),
  ~_oh: si.OTxH(~_cp, ~_tx),
  ~_ot: si.OTxT(~_tx),
  +gg: _GG,
  lf: Bool,
  +st: T.St,
  +cc: Char,
  +tl: String,
  +eg: {_ii(gg, st) == True{} : Bool},
  +ec: {_cp(cc) == True{} : Bool}
) -> si.md(~_GG, ~_ii, ~_sp, gg, T.doc.cr(lf, st, cc), tl):
  match lf:
    case True{}:
      sip.fast(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, st, eg, cc, ec)
    case False{}:
      _oe(gg, st, "carriage return without line feed", {==}, eg)

# an empty buffer starts a span at this character; a buffer in use goes the
# old way
def sip.obuf(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_sp: _GG -> String -> U32 -> String -> Bool,
  ~_cp: Char -> Bool,
  ~_tx: String -> Bool,
  ~_pd: _GG -> T.Doc -> Type,
  ~_os: si.OStep(~_GG, ~_ii, ~_cp),
  ~_oo: si.OOnce(~_GG, ~_ii),
  ~_oc: si.OCons(~_GG, ~_ii, ~_cp),
  ~_oe: si.OErr(~_GG, ~_ii),
  ~_oq: si.OOpen(~_GG, ~_ii),
  ~_o1: si.OSp1(~_GG, ~_sp, ~_cp, ~_tx),
  ~_oi: si.OSpInc(~_GG, ~_sp, ~_cp, ~_tx),
  ~_ol: si.OClose(~_GG, ~_ii, ~_sp),
  ~_oy: si.OCopy(~_GG, ~_ii, ~_sp),
  ~_of: si.OFin(~_GG, ~_ii, ~_pd),
  ~_ou: si.OUnc(~_GG, ~_ii, ~_pd),
  ~_oh: si.OTxH(~_cp, ~_tx),
  ~_ot: si.OTxT(~_tx),
  +gg: _GG,
  bf: List<&2, Char>,
  +ba: Bool,
  +qq: Char,
  +qk: T.QKind,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +eg: {_ii(gg, T.St{bd, rw, hs, he, pt, bf, T.LQ{}, bk, qk, sk, T.HNone{}, un, lf, at, False{}}) == True{} : Bool},
  +cc: Char,
  +tl: String,
  +ec: {_cp(cc) == True{} : Bool},
  +et: {_tx(SCon{cc, tl}) == True{} : Bool}
) -> si.md(~_GG, ~_ii, ~_sp, gg, T.doc.open.buf(ba, qq, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc, tl), tl):
  match bf:
    case []:
      M1.gd.tt(_ii(gg, si.str(bd, rw, hs, he, pt, [], qk, sk, un, lf, at)), _sp(gg, SCon{cc, tl}, 1, tl),
        _oq(gg, bd, rw, hs, he, pt, bk, qk, sk, un, lf, at, eg), _o1(gg, cc, tl, ec, et))
    case +bh <> +bt:
      sip.flex(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, T.LQ{}, bd, rw, hs, he, pt, bh <> bt, bk, qk, sk, un, lf, at,
        eg, cc, ec)

# a forbidden control goes the old way; any other starts a span
def sip.ook(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_sp: _GG -> String -> U32 -> String -> Bool,
  ~_cp: Char -> Bool,
  ~_tx: String -> Bool,
  ~_pd: _GG -> T.Doc -> Type,
  ~_os: si.OStep(~_GG, ~_ii, ~_cp),
  ~_oo: si.OOnce(~_GG, ~_ii),
  ~_oc: si.OCons(~_GG, ~_ii, ~_cp),
  ~_oe: si.OErr(~_GG, ~_ii),
  ~_oq: si.OOpen(~_GG, ~_ii),
  ~_o1: si.OSp1(~_GG, ~_sp, ~_cp, ~_tx),
  ~_oi: si.OSpInc(~_GG, ~_sp, ~_cp, ~_tx),
  ~_ol: si.OClose(~_GG, ~_ii, ~_sp),
  ~_oy: si.OCopy(~_GG, ~_ii, ~_sp),
  ~_of: si.OFin(~_GG, ~_ii, ~_pd),
  ~_ou: si.OUnc(~_GG, ~_ii, ~_pd),
  ~_oh: si.OTxH(~_cp, ~_tx),
  ~_ot: si.OTxT(~_tx),
  +gg: _GG,
  badc: Bool,
  +ba: Bool,
  +qq: Char,
  +qk: T.QKind,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +bf: List<&2, Char>,
  +eg: {_ii(gg, T.St{bd, rw, hs, he, pt, bf, T.LQ{}, bk, qk, sk, T.HNone{}, un, lf, at, False{}}) == True{} : Bool},
  +cc: Char,
  +tl: String,
  +ec: {_cp(cc) == True{} : Bool},
  +et: {_tx(SCon{cc, tl}) == True{} : Bool}
) -> si.md(~_GG, ~_ii, ~_sp, gg, T.doc.open.ok(badc, ba, qq, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc, tl),
  tl):
  match badc:
    case True{}:
      sip.flex(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, T.LQ{}, bd, rw, hs, he, pt, bf, bk, qk, sk, un, lf, at, eg, cc,
        ec)
    case False{}:
      sip.obuf(~_GG, ~_ii, ~_sp, ~_cp, ~_tx, ~_pd, ~_os, ~_oo, ~_oc, ~_oe, ~_oq, ~_o1, ~_oi, ~_ol, ~_oy, ~_of, ~_ou,
        ~_oh,
        ~_ot, gg, bf, ba, qq, qk, bd, rw, hs, he, pt, bk, sk, un, lf, at, eg, cc, tl, ec, et)

# a backslash in a basic string goes the old way
def sip.obs(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_sp: _GG -> String -> U32 -> String -> Bool,
  ~_cp: Char -> Bool,
  ~_tx: String -> Bool,
  ~_pd: _GG -> T.Doc -> Type,
  ~_os: si.OStep(~_GG, ~_ii, ~_cp),
  ~_oo: si.OOnce(~_GG, ~_ii),
  ~_oc: si.OCons(~_GG, ~_ii, ~_cp),
  ~_oe: si.OErr(~_GG, ~_ii),
  ~_oq: si.OOpen(~_GG, ~_ii),
  ~_o1: si.OSp1(~_GG, ~_sp, ~_cp, ~_tx),
  ~_oi: si.OSpInc(~_GG, ~_sp, ~_cp, ~_tx),
  ~_ol: si.OClose(~_GG, ~_ii, ~_sp),
  ~_oy: si.OCopy(~_GG, ~_ii, ~_sp),
  ~_of: si.OFin(~_GG, ~_ii, ~_pd),
  ~_ou: si.OUnc(~_GG, ~_ii, ~_pd),
  ~_oh: si.OTxH(~_cp, ~_tx),
  ~_ot: si.OTxT(~_tx),
  +gg: _GG,
  bs: Bool,
  +qq: Char,
  +qk: T.QKind,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +bf: List<&2, Char>,
  +eg: {_ii(gg, T.St{bd, rw, hs, he, pt, bf, T.LQ{}, bk, qk, sk, T.HNone{}, un, lf, at, False{}}) == True{} : Bool},
  +cc: Char,
  +tl: String,
  +ec: {_cp(cc) == True{} : Bool},
  +et: {_tx(SCon{cc, tl}) == True{} : Bool}
) -> si.md(~_GG, ~_ii, ~_sp, gg, T.doc.open.bs(bs, qq, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc, tl), tl):
  match bs:
    case True{}:
      sip.flex(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, T.LQ{}, bd, rw, hs, he, pt, bf, bk, qk, sk, un, lf, at, eg, cc,
        ec)
    case False{}:
      sip.ook(~_GG, ~_ii, ~_sp, ~_cp, ~_tx, ~_pd, ~_os, ~_oo, ~_oc, ~_oe, ~_oq, ~_o1, ~_oi, ~_ol, ~_oy, ~_of, ~_ou,
        ~_oh,
        ~_ot, gg, T.str.bad(Char.to_u32(cc), False{}), True{}, qq, qk, bd, rw, hs, he, pt, bk, sk, un, lf, at, bf, eg,
          cc,
          tl, ec, et)

# a literal string keeps a backslash; a basic string does not
def sip.ob(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_sp: _GG -> String -> U32 -> String -> Bool,
  ~_cp: Char -> Bool,
  ~_tx: String -> Bool,
  ~_pd: _GG -> T.Doc -> Type,
  ~_os: si.OStep(~_GG, ~_ii, ~_cp),
  ~_oo: si.OOnce(~_GG, ~_ii),
  ~_oc: si.OCons(~_GG, ~_ii, ~_cp),
  ~_oe: si.OErr(~_GG, ~_ii),
  ~_oq: si.OOpen(~_GG, ~_ii),
  ~_o1: si.OSp1(~_GG, ~_sp, ~_cp, ~_tx),
  ~_oi: si.OSpInc(~_GG, ~_sp, ~_cp, ~_tx),
  ~_ol: si.OClose(~_GG, ~_ii, ~_sp),
  ~_oy: si.OCopy(~_GG, ~_ii, ~_sp),
  ~_of: si.OFin(~_GG, ~_ii, ~_pd),
  ~_ou: si.OUnc(~_GG, ~_ii, ~_pd),
  ~_oh: si.OTxH(~_cp, ~_tx),
  ~_ot: si.OTxT(~_tx),
  +gg: _GG,
  ba: Bool,
  +qq: Char,
  +qk: T.QKind,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +bf: List<&2, Char>,
  +eg: {_ii(gg, T.St{bd, rw, hs, he, pt, bf, T.LQ{}, bk, qk, sk, T.HNone{}, un, lf, at, False{}}) == True{} : Bool},
  +cc: Char,
  +tl: String,
  +ec: {_cp(cc) == True{} : Bool},
  +et: {_tx(SCon{cc, tl}) == True{} : Bool}
) -> si.md(~_GG, ~_ii, ~_sp, gg, T.doc.open.b(ba, qq, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc, tl), tl):
  match ba:
    case False{}:
      sip.ook(~_GG, ~_ii, ~_sp, ~_cp, ~_tx, ~_pd, ~_os, ~_oo, ~_oc, ~_oe, ~_oq, ~_o1, ~_oi, ~_ol, ~_oy, ~_of, ~_ou,
        ~_oh,
        ~_ot, gg, T.str.bad(Char.to_u32(cc), False{}), False{}, qq, qk, bd, rw, hs, he, pt, bk, sk, un, lf, at, bf, eg,
          cc, tl, ec, et)
    case True{}:
      sip.obs(~_GG, ~_ii, ~_sp, ~_cp, ~_tx, ~_pd, ~_os, ~_oo, ~_oc, ~_oe, ~_oq, ~_o1, ~_oi, ~_ol, ~_oy, ~_of, ~_ou,
        ~_oh,
        ~_ot, gg, Char.is_eq(cc, '\\'), qq, qk, bd, rw, hs, he, pt, bk, sk, un, lf, at, bf, eg, cc, tl, ec, et)

# a second quote goes the old way
def sip.oq(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_sp: _GG -> String -> U32 -> String -> Bool,
  ~_cp: Char -> Bool,
  ~_tx: String -> Bool,
  ~_pd: _GG -> T.Doc -> Type,
  ~_os: si.OStep(~_GG, ~_ii, ~_cp),
  ~_oo: si.OOnce(~_GG, ~_ii),
  ~_oc: si.OCons(~_GG, ~_ii, ~_cp),
  ~_oe: si.OErr(~_GG, ~_ii),
  ~_oq: si.OOpen(~_GG, ~_ii),
  ~_o1: si.OSp1(~_GG, ~_sp, ~_cp, ~_tx),
  ~_oi: si.OSpInc(~_GG, ~_sp, ~_cp, ~_tx),
  ~_ol: si.OClose(~_GG, ~_ii, ~_sp),
  ~_oy: si.OCopy(~_GG, ~_ii, ~_sp),
  ~_of: si.OFin(~_GG, ~_ii, ~_pd),
  ~_ou: si.OUnc(~_GG, ~_ii, ~_pd),
  ~_oh: si.OTxH(~_cp, ~_tx),
  ~_ot: si.OTxT(~_tx),
  +gg: _GG,
  same: Bool,
  +ba: Bool,
  +qq: Char,
  +qk: T.QKind,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +bf: List<&2, Char>,
  +eg: {_ii(gg, T.St{bd, rw, hs, he, pt, bf, T.LQ{}, bk, qk, sk, T.HNone{}, un, lf, at, False{}}) == True{} : Bool},
  +cc: Char,
  +tl: String,
  +ec: {_cp(cc) == True{} : Bool},
  +et: {_tx(SCon{cc, tl}) == True{} : Bool}
) -> si.md(~_GG, ~_ii, ~_sp, gg, T.doc.open.q(same, ba, qq, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc, tl),
  tl):
  match same:
    case True{}:
      sip.flex(~_GG, ~_ii, ~_cp, ~_os, ~_oo, ~_oc, gg, T.LQ{}, bd, rw, hs, he, pt, bf, bk, qk, sk, un, lf, at, eg, cc,
        ec)
    case False{}:
      sip.ob(~_GG, ~_ii, ~_sp, ~_cp, ~_tx, ~_pd, ~_os, ~_oo, ~_oc, ~_oe, ~_oq, ~_o1, ~_oi, ~_ol, ~_oy, ~_of, ~_ou, ~_oh,
        ~_ot, gg, ba, qq, qk, bd, rw, hs, he, pt, bk, sk, un, lf, at, bf, eg, cc, tl, ec, et)

# the span copied to the buffer, and the character read the old way
def sip.ecopy(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_sp: _GG -> String -> U32 -> String -> Bool,
  ~_cp: Char -> Bool,
  ~_tx: String -> Bool,
  ~_pd: _GG -> T.Doc -> Type,
  ~_os: si.OStep(~_GG, ~_ii, ~_cp),
  ~_oo: si.OOnce(~_GG, ~_ii),
  ~_oc: si.OCons(~_GG, ~_ii, ~_cp),
  ~_oe: si.OErr(~_GG, ~_ii),
  ~_oq: si.OOpen(~_GG, ~_ii),
  ~_o1: si.OSp1(~_GG, ~_sp, ~_cp, ~_tx),
  ~_oi: si.OSpInc(~_GG, ~_sp, ~_cp, ~_tx),
  ~_ol: si.OClose(~_GG, ~_ii, ~_sp),
  ~_oy: si.OCopy(~_GG, ~_ii, ~_sp),
  ~_of: si.OFin(~_GG, ~_ii, ~_pd),
  ~_ou: si.OUnc(~_GG, ~_ii, ~_pd),
  ~_oh: si.OTxH(~_cp, ~_tx),
  ~_ot: si.OTxT(~_tx),
  +gg: _GG,
  +ct: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +hh: Char,
  +tt: String,
  +eg: {_ii(gg, si.str(bd, rw, hs, he, pt, [], qk, sk, un, lf, at)) == True{} : Bool},
  +ep: {_sp(gg, ct, nn, SCon{hh, tt}) == True{} : Bool},
  +eh: {_cp(hh) == True{} : Bool},
  +_et: {_tx(SCon{hh, tt}) == True{} : Bool}
) -> si.md(~_GG, ~_ii, ~_sp, gg, T.eat.copy(hh, ct, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at), tt):
  _os(gg, si.str(bd, rw, hs, he, pt, T.span.rev(ct, nn, U32.is_zero(nn), []), qk, sk, un, lf, at),
    _oy(gg, bd, rw, hs, he, pt, qk, sk, un, lf, at, ct, nn, SCon{hh, tt}, eg, ep), hh, eh)

# the span one character longer
def sip.emore(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_sp: _GG -> String -> U32 -> String -> Bool,
  ~_cp: Char -> Bool,
  ~_tx: String -> Bool,
  ~_pd: _GG -> T.Doc -> Type,
  ~_os: si.OStep(~_GG, ~_ii, ~_cp),
  ~_oo: si.OOnce(~_GG, ~_ii),
  ~_oc: si.OCons(~_GG, ~_ii, ~_cp),
  ~_oe: si.OErr(~_GG, ~_ii),
  ~_oq: si.OOpen(~_GG, ~_ii),
  ~_o1: si.OSp1(~_GG, ~_sp, ~_cp, ~_tx),
  ~_oi: si.OSpInc(~_GG, ~_sp, ~_cp, ~_tx),
  ~_ol: si.OClose(~_GG, ~_ii, ~_sp),
  ~_oy: si.OCopy(~_GG, ~_ii, ~_sp),
  ~_of: si.OFin(~_GG, ~_ii, ~_pd),
  ~_ou: si.OUnc(~_GG, ~_ii, ~_pd),
  ~_oh: si.OTxH(~_cp, ~_tx),
  ~_ot: si.OTxT(~_tx),
  +gg: _GG,
  +ba: Bool,
  +qq: Char,
  +ct: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +hh: Char,
  +tt: String,
  +eg: {_ii(gg, si.str(bd, rw, hs, he, pt, [], qk, sk, un, lf, at)) == True{} : Bool},
  +ep: {_sp(gg, ct, nn, SCon{hh, tt}) == True{} : Bool},
  +eh: {_cp(hh) == True{} : Bool},
  +et: {_tx(SCon{hh, tt}) == True{} : Bool}
) -> si.md(~_GG, ~_ii, ~_sp, gg, T.MEat{ba, qq, ct, U32.add(nn, 1), bd, rw, hs, he, pt, qk, sk, un, lf, at}, tt):
  M1.gd.tt(_ii(gg, si.str(bd, rw, hs, he, pt, [], qk, sk, un, lf, at)), _sp(gg, ct, U32.add(nn, 1), tt), eg,
    _oi(gg, ct, nn, hh, tt, ep, eh, et))

# a forbidden control copies the span; a plain character extends it
def sip.ectrl(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_sp: _GG -> String -> U32 -> String -> Bool,
  ~_cp: Char -> Bool,
  ~_tx: String -> Bool,
  ~_pd: _GG -> T.Doc -> Type,
  ~_os: si.OStep(~_GG, ~_ii, ~_cp),
  ~_oo: si.OOnce(~_GG, ~_ii),
  ~_oc: si.OCons(~_GG, ~_ii, ~_cp),
  ~_oe: si.OErr(~_GG, ~_ii),
  ~_oq: si.OOpen(~_GG, ~_ii),
  ~_o1: si.OSp1(~_GG, ~_sp, ~_cp, ~_tx),
  ~_oi: si.OSpInc(~_GG, ~_sp, ~_cp, ~_tx),
  ~_ol: si.OClose(~_GG, ~_ii, ~_sp),
  ~_oy: si.OCopy(~_GG, ~_ii, ~_sp),
  ~_of: si.OFin(~_GG, ~_ii, ~_pd),
  ~_ou: si.OUnc(~_GG, ~_ii, ~_pd),
  ~_oh: si.OTxH(~_cp, ~_tx),
  ~_ot: si.OTxT(~_tx),
  +gg: _GG,
  badc: Bool,
  +ba: Bool,
  +qq: Char,
  +ct: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +hh: Char,
  +tt: String,
  +eg: {_ii(gg, si.str(bd, rw, hs, he, pt, [], qk, sk, un, lf, at)) == True{} : Bool},
  +ep: {_sp(gg, ct, nn, SCon{hh, tt}) == True{} : Bool},
  +eh: {_cp(hh) == True{} : Bool},
  +et: {_tx(SCon{hh, tt}) == True{} : Bool}
) -> si.md(~_GG, ~_ii, ~_sp, gg, T.eat.ctrl(badc, ba, qq, hh, ct, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at), tt):
  match badc:
    case True{}:
      sip.ecopy(~_GG, ~_ii, ~_sp, ~_cp, ~_tx, ~_pd, ~_os, ~_oo, ~_oc, ~_oe, ~_oq, ~_o1, ~_oi, ~_ol, ~_oy, ~_of, ~_ou,
        ~_oh,
        ~_ot, gg, ct, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at, hh, tt, eg, ep, eh, et)
    case False{}:
      sip.emore(~_GG, ~_ii, ~_sp, ~_cp, ~_tx, ~_pd, ~_os, ~_oo, ~_oc, ~_oe, ~_oq, ~_o1, ~_oi, ~_ol, ~_oy, ~_of, ~_ou,
        ~_oh,
        ~_ot, gg, ba, qq, ct, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at, hh, tt, eg, ep, eh, et)

# a backslash in a basic string copies the span
def sip.ebs(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_sp: _GG -> String -> U32 -> String -> Bool,
  ~_cp: Char -> Bool,
  ~_tx: String -> Bool,
  ~_pd: _GG -> T.Doc -> Type,
  ~_os: si.OStep(~_GG, ~_ii, ~_cp),
  ~_oo: si.OOnce(~_GG, ~_ii),
  ~_oc: si.OCons(~_GG, ~_ii, ~_cp),
  ~_oe: si.OErr(~_GG, ~_ii),
  ~_oq: si.OOpen(~_GG, ~_ii),
  ~_o1: si.OSp1(~_GG, ~_sp, ~_cp, ~_tx),
  ~_oi: si.OSpInc(~_GG, ~_sp, ~_cp, ~_tx),
  ~_ol: si.OClose(~_GG, ~_ii, ~_sp),
  ~_oy: si.OCopy(~_GG, ~_ii, ~_sp),
  ~_of: si.OFin(~_GG, ~_ii, ~_pd),
  ~_ou: si.OUnc(~_GG, ~_ii, ~_pd),
  ~_oh: si.OTxH(~_cp, ~_tx),
  ~_ot: si.OTxT(~_tx),
  +gg: _GG,
  bs: Bool,
  +ba: Bool,
  +qq: Char,
  +ct: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +hh: Char,
  +tt: String,
  +eg: {_ii(gg, si.str(bd, rw, hs, he, pt, [], qk, sk, un, lf, at)) == True{} : Bool},
  +ep: {_sp(gg, ct, nn, SCon{hh, tt}) == True{} : Bool},
  +eh: {_cp(hh) == True{} : Bool},
  +et: {_tx(SCon{hh, tt}) == True{} : Bool}
) -> si.md(~_GG, ~_ii, ~_sp, gg, T.eat.bs(bs, ba, qq, hh, ct, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at), tt):
  match bs:
    case True{}:
      sip.ecopy(~_GG, ~_ii, ~_sp, ~_cp, ~_tx, ~_pd, ~_os, ~_oo, ~_oc, ~_oe, ~_oq, ~_o1, ~_oi, ~_ol, ~_oy, ~_of, ~_ou,
        ~_oh,
        ~_ot, gg, ct, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at, hh, tt, eg, ep, eh, et)
    case False{}:
      sip.ectrl(~_GG, ~_ii, ~_sp, ~_cp, ~_tx, ~_pd, ~_os, ~_oo, ~_oc, ~_oe, ~_oq, ~_o1, ~_oi, ~_ol, ~_oy, ~_of, ~_ou,
        ~_oh,
        ~_ot, gg, T.str.bad(Char.to_u32(hh), False{}), ba, qq, ct, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at, hh, tt,
          eg,
          ep, eh, et)

# a literal string's character, or a basic string's
def sip.ebasic(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_sp: _GG -> String -> U32 -> String -> Bool,
  ~_cp: Char -> Bool,
  ~_tx: String -> Bool,
  ~_pd: _GG -> T.Doc -> Type,
  ~_os: si.OStep(~_GG, ~_ii, ~_cp),
  ~_oo: si.OOnce(~_GG, ~_ii),
  ~_oc: si.OCons(~_GG, ~_ii, ~_cp),
  ~_oe: si.OErr(~_GG, ~_ii),
  ~_oq: si.OOpen(~_GG, ~_ii),
  ~_o1: si.OSp1(~_GG, ~_sp, ~_cp, ~_tx),
  ~_oi: si.OSpInc(~_GG, ~_sp, ~_cp, ~_tx),
  ~_ol: si.OClose(~_GG, ~_ii, ~_sp),
  ~_oy: si.OCopy(~_GG, ~_ii, ~_sp),
  ~_of: si.OFin(~_GG, ~_ii, ~_pd),
  ~_ou: si.OUnc(~_GG, ~_ii, ~_pd),
  ~_oh: si.OTxH(~_cp, ~_tx),
  ~_ot: si.OTxT(~_tx),
  +gg: _GG,
  ba: Bool,
  +qq: Char,
  +ct: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +hh: Char,
  +tt: String,
  +eg: {_ii(gg, si.str(bd, rw, hs, he, pt, [], qk, sk, un, lf, at)) == True{} : Bool},
  +ep: {_sp(gg, ct, nn, SCon{hh, tt}) == True{} : Bool},
  +eh: {_cp(hh) == True{} : Bool},
  +et: {_tx(SCon{hh, tt}) == True{} : Bool}
) -> si.md(~_GG, ~_ii, ~_sp, gg, T.eat.basic(ba, qq, hh, ct, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at), tt):
  match ba:
    case False{}:
      sip.ectrl(~_GG, ~_ii, ~_sp, ~_cp, ~_tx, ~_pd, ~_os, ~_oo, ~_oc, ~_oe, ~_oq, ~_o1, ~_oi, ~_ol, ~_oy, ~_of, ~_ou,
        ~_oh,
        ~_ot, gg, T.str.bad(Char.to_u32(hh), False{}), False{}, qq, ct, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at, hh,
          tt, eg, ep, eh, et)
    case True{}:
      sip.ebs(~_GG, ~_ii, ~_sp, ~_cp, ~_tx, ~_pd, ~_os, ~_oo, ~_oc, ~_oe, ~_oq, ~_o1, ~_oi, ~_ol, ~_oy, ~_of, ~_ou,
        ~_oh,
        ~_ot, gg, Char.is_eq(hh, '\\'), True{}, qq, ct, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at, hh, tt, eg, ep,
          eh, et)

# the quote closes the span as a VSpan; any other character goes on
def sip.eq(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_sp: _GG -> String -> U32 -> String -> Bool,
  ~_cp: Char -> Bool,
  ~_tx: String -> Bool,
  ~_pd: _GG -> T.Doc -> Type,
  ~_os: si.OStep(~_GG, ~_ii, ~_cp),
  ~_oo: si.OOnce(~_GG, ~_ii),
  ~_oc: si.OCons(~_GG, ~_ii, ~_cp),
  ~_oe: si.OErr(~_GG, ~_ii),
  ~_oq: si.OOpen(~_GG, ~_ii),
  ~_o1: si.OSp1(~_GG, ~_sp, ~_cp, ~_tx),
  ~_oi: si.OSpInc(~_GG, ~_sp, ~_cp, ~_tx),
  ~_ol: si.OClose(~_GG, ~_ii, ~_sp),
  ~_oy: si.OCopy(~_GG, ~_ii, ~_sp),
  ~_of: si.OFin(~_GG, ~_ii, ~_pd),
  ~_ou: si.OUnc(~_GG, ~_ii, ~_pd),
  ~_oh: si.OTxH(~_cp, ~_tx),
  ~_ot: si.OTxT(~_tx),
  +gg: _GG,
  quote: Bool,
  +ba: Bool,
  +qq: Char,
  +ct: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +hh: Char,
  +tt: String,
  +eg: {_ii(gg, si.str(bd, rw, hs, he, pt, [], qk, sk, un, lf, at)) == True{} : Bool},
  +ep: {_sp(gg, ct, nn, SCon{hh, tt}) == True{} : Bool},
  +eh: {_cp(hh) == True{} : Bool},
  +et: {_tx(SCon{hh, tt}) == True{} : Bool}
) -> si.md(~_GG, ~_ii, ~_sp, gg, T.eat.feed.q(quote, ba, qq, hh, ct, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at), tt):
  match quote:
    case True{}:
      _ol(gg, bd, rw, hs, he, pt, qk, sk, un, lf, at, ct, nn, SCon{hh, tt}, eg, ep)
    case False{}:
      sip.ebasic(~_GG, ~_ii, ~_sp, ~_cp, ~_tx, ~_pd, ~_os, ~_oo, ~_oc, ~_oe, ~_oq, ~_o1, ~_oi, ~_ol, ~_oy, ~_of, ~_ou,
        ~_oh,
        ~_ot, gg, ba, qq, ct, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at, hh, tt, eg, ep, eh, et)

# every character keeps the mode's invariant
def sip.mstep(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_sp: _GG -> String -> U32 -> String -> Bool,
  ~_cp: Char -> Bool,
  ~_tx: String -> Bool,
  ~_pd: _GG -> T.Doc -> Type,
  ~_os: si.OStep(~_GG, ~_ii, ~_cp),
  ~_oo: si.OOnce(~_GG, ~_ii),
  ~_oc: si.OCons(~_GG, ~_ii, ~_cp),
  ~_oe: si.OErr(~_GG, ~_ii),
  ~_oq: si.OOpen(~_GG, ~_ii),
  ~_o1: si.OSp1(~_GG, ~_sp, ~_cp, ~_tx),
  ~_oi: si.OSpInc(~_GG, ~_sp, ~_cp, ~_tx),
  ~_ol: si.OClose(~_GG, ~_ii, ~_sp),
  ~_oy: si.OCopy(~_GG, ~_ii, ~_sp),
  ~_of: si.OFin(~_GG, ~_ii, ~_pd),
  ~_ou: si.OUnc(~_GG, ~_ii, ~_pd),
  ~_oh: si.OTxH(~_cp, ~_tx),
  ~_ot: si.OTxT(~_tx),
  +gg: _GG,
  +mode: T.Mode,
  +hh: Char,
  +tt: String,
  +em: si.md(~_GG, ~_ii, ~_sp, gg, mode, SCon{hh, tt}),
  +eh: {_cp(hh) == True{} : Bool},
  +et: {_tx(SCon{hh, tt}) == True{} : Bool}
) -> si.md(~_GG, ~_ii, ~_sp, gg, L1.gd.next(mode, hh, tt), tt):
  match mode:
    case T.MOpen{+ba, +qq, +qk, +bd, +rw, +hs, +he, +pt, +bf, +bk, +sk, +un, +lf, +at}:
      sip.oq(~_GG, ~_ii, ~_sp, ~_cp, ~_tx, ~_pd, ~_os, ~_oo, ~_oc, ~_oe, ~_oq, ~_o1, ~_oi, ~_ol, ~_oy, ~_of, ~_ou, ~_oh,
        ~_ot, gg, Char.is_eq(hh, qq), ba, qq, qk, bd, rw, hs, he, pt, bk, sk, un, lf, at, bf, em, hh, tt, eh, et)
    case T.MEat{+ba, +qq, +ct, +nn, +bd, +rw, +hs, +he, +pt, +qk, +sk, +un, +lf, +at}:
      sip.eq(~_GG, ~_ii, ~_sp, ~_cp, ~_tx, ~_pd, ~_os, ~_oo, ~_oc, ~_oe, ~_oq, ~_o1, ~_oi, ~_ol, ~_oy, ~_of, ~_ou, ~_oh,
        ~_ot, gg, Char.is_eq(hh, qq), ba, qq, ct, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at, hh, tt,
        M1.gd.l(_ii(gg, si.str(bd, rw, hs, he, pt, [], qk, sk, un, lf, at)), _sp(gg, ct, nn, SCon{hh, tt}), em),
        M1.gd.r(_ii(gg, si.str(bd, rw, hs, he, pt, [], qk, sk, un, lf, at)), _sp(gg, ct, nn, SCon{hh, tt}), em), eh, et)
    case T.MScan{+st}:
      sip.sdq(~_GG, ~_ii, ~_sp, ~_cp, ~_tx, ~_pd, ~_os, ~_oo, ~_oc, ~_oe, ~_oq, ~_o1, ~_oi, ~_ol, ~_oy, ~_of, ~_ou,
        ~_oh,
        ~_ot, gg, Char.is_eq(hh, '"'), Char.is_eq(hh, '\''), U32.is_eq(Char.to_u32(hh), 13), st, hh, tt, em, eh)
    case T.MCr{+st}:
      sip.dcr(~_GG, ~_ii, ~_sp, ~_cp, ~_tx, ~_pd, ~_os, ~_oo, ~_oc, ~_oe, ~_oq, ~_o1, ~_oi, ~_ol, ~_oy, ~_of, ~_ou,
        ~_oh,
        ~_ot, gg, Char.is_eq(hh, '\n'), st, hh, tt, em, eh)

# the text runs out: in a scanning state, after a carriage return, after an
# opening quote, or in a span
def sip.dend(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_sp: _GG -> String -> U32 -> String -> Bool,
  ~_cp: Char -> Bool,
  ~_tx: String -> Bool,
  ~_pd: _GG -> T.Doc -> Type,
  ~_os: si.OStep(~_GG, ~_ii, ~_cp),
  ~_oo: si.OOnce(~_GG, ~_ii),
  ~_oc: si.OCons(~_GG, ~_ii, ~_cp),
  ~_oe: si.OErr(~_GG, ~_ii),
  ~_oq: si.OOpen(~_GG, ~_ii),
  ~_o1: si.OSp1(~_GG, ~_sp, ~_cp, ~_tx),
  ~_oi: si.OSpInc(~_GG, ~_sp, ~_cp, ~_tx),
  ~_ol: si.OClose(~_GG, ~_ii, ~_sp),
  ~_oy: si.OCopy(~_GG, ~_ii, ~_sp),
  ~_of: si.OFin(~_GG, ~_ii, ~_pd),
  ~_ou: si.OUnc(~_GG, ~_ii, ~_pd),
  ~_oh: si.OTxH(~_cp, ~_tx),
  ~_ot: si.OTxT(~_tx),
  +gg: _GG,
  mode: T.Mode,
  +em: si.md(~_GG, ~_ii, ~_sp, gg, mode, SNil{})
) -> _pd(gg, T.doc.read(SNil{}, mode)):
  match mode:
    case T.MScan{+st}:
      _of(gg, T.read.once2(st), _oo(gg, st, em))
    case T.MCr{+st}:
      _of(gg, T.read.once2(T.st.err(st, "carriage return without line feed")), _oo(gg, T.st.err(st,
        "carriage return without line feed"), _oe(gg, st, "carriage return without line feed", {==}, em)))
    case T.MOpen{_ba, _qq, +qk, +bd, +rw, +hs, +he, +pt, +bf, +bk, +sk, +un, +lf, +at}:
      _of(gg, T.read.once2(T.St{bd, rw, hs, he, pt, bf, T.LQ{}, bk, qk, sk, T.HNone{}, un, lf, at, False{}}),
        _oo(gg, T.St{bd, rw, hs, he, pt, bf, T.LQ{}, bk, qk, sk, T.HNone{}, un, lf, at, False{}}, em))
    case T.MEat{_ba, _qq, +ct, +nn, +bd, +rw, +hs, +he, +pt, +qk, +sk, +un, +lf, +at}:
      _ou(gg, bd, rw, hs, he, pt, qk, sk, un, lf, at, M1.gd.l(_ii(gg, si.str(bd, rw, hs, he, pt, [], qk, sk, un, lf,
          at)),
        _sp(gg, ct, nn, SNil{}), em))

# doc.read takes a character to the mode gd.next names
def sip.next(
  +mode: T.Mode,
  +hh: Char,
  +tt: String
) -> {T.doc.read(SCon{hh, tt}, mode) == T.doc.read(tt, L1.gd.next(mode, hh, tt)) : T.Doc}:
  match mode:
    case T.MOpen{_b, _q, _k, _bd, _rw, _hs, _he, _pt, _bf, _bk, _sk, _un, _lf, _at}:
      {==}
    case T.MEat{_b, _q, _c, _n, _bd, _rw, _hs, _he, _pt, _k, _sk, _un, _lf, _at}:
      {==}
    case T.MScan{_st}:
      {==}
    case T.MCr{_st}:
      {==}

# SCAN: the induction itself. For every invariant of the scanner's state
# that the obligations above keep, doc.read of a text the text predicate
# allows, from a mode the invariant holds of, gives what pd asks
def sip.read(
  ~_GG: Data,
  ~_ii: _GG -> T.St -> Bool,
  ~_sp: _GG -> String -> U32 -> String -> Bool,
  ~_cp: Char -> Bool,
  ~_tx: String -> Bool,
  ~_pd: _GG -> T.Doc -> Type,
  ~_os: si.OStep(~_GG, ~_ii, ~_cp),
  ~_oo: si.OOnce(~_GG, ~_ii),
  ~_oc: si.OCons(~_GG, ~_ii, ~_cp),
  ~_oe: si.OErr(~_GG, ~_ii),
  ~_oq: si.OOpen(~_GG, ~_ii),
  ~_o1: si.OSp1(~_GG, ~_sp, ~_cp, ~_tx),
  ~_oi: si.OSpInc(~_GG, ~_sp, ~_cp, ~_tx),
  ~_ol: si.OClose(~_GG, ~_ii, ~_sp),
  ~_oy: si.OCopy(~_GG, ~_ii, ~_sp),
  ~_of: si.OFin(~_GG, ~_ii, ~_pd),
  ~_ou: si.OUnc(~_GG, ~_ii, ~_pd),
  ~_oh: si.OTxH(~_cp, ~_tx),
  ~_ot: si.OTxT(~_tx),
  +gg: _GG,
  +text: String,
  +mode: T.Mode,
  +em: si.md(~_GG, ~_ii, ~_sp, gg, mode, text),
  +et: {_tx(text) == True{} : Bool}
) -> _pd(gg, T.doc.read(text, mode)):
  match text:
    case SNil{}:
      sip.dend(~_GG, ~_ii, ~_sp, ~_cp, ~_tx, ~_pd, ~_os, ~_oo, ~_oc, ~_oe, ~_oq, ~_o1, ~_oi, ~_ol, ~_oy, ~_of, ~_ou,
        ~_oh,
        ~_ot, gg, mode, em)
    case SCon{+hh, +tt}:
      %Equal.sym(T.Doc, T.doc.read(SCon{hh, tt}, mode), T.doc.read(tt, L1.gd.next(mode, hh, tt)),
        sip.next(mode, hh, tt)) : _pd(gg, _)
      sip.read(~_GG, ~_ii, ~_sp, ~_cp, ~_tx, ~_pd, ~_os, ~_oo, ~_oc, ~_oe, ~_oq, ~_o1, ~_oi, ~_ol, ~_oy, ~_of, ~_ou,
        ~_oh,
        ~_ot, gg, tt, L1.gd.next(mode, hh, tt), sip.mstep(~_GG, ~_ii, ~_sp, ~_cp, ~_tx, ~_pd, ~_os, ~_oo, ~_oc,
          ~_oe, ~_oq,
          ~_o1, ~_oi, ~_ol, ~_oy, ~_of, ~_ou, ~_oh, ~_ot, gg, mode, hh, tt, em, _oh(hh, tt, et), et),
        _ot(hh, tt, et))
