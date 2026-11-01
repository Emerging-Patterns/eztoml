# once the scanner holds an error, the error and the rows stay
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/DefinesEachTableOnce.bend as L1
import ../../laws/ErrorStays.bend as L2
import ./FailedWalkNameCompare.bend as M1
import ./ScanInvariantSteps.bend as M2

# by the two newlines' tests: each is a control
def sr.nlctl.go(
  +uu: U32,
  aa: Bool,
  bb: Bool,
  ea: {U32.is_eq(uu, 10) == aa : Bool},
  eb: {U32.is_eq(uu, 13) == bb : Bool},
  ee: {T.ch.ctl(Chr{uu}) == False{} : Bool}
) -> {Bool.or(aa, bb) == False{} : Bool}:
  match aa:
    case True{}:
      Eq.bit.gone(&2, {Bool.or(True{}, bb) == False{} : Bool}, Eq.refute_char(Chr{uu}, Chr{10},
        cc => Bool.not(T.ch.ctl(cc)), ea, Equal.cong(Bool, Bool, xx => Bool.not(xx), T.ch.ctl(Chr{uu}), False{},
        ee), {==}))
    case False{}:
      match bb:
        case True{}:
          Eq.bit.gone(&2, {Bool.or(False{}, True{}) == False{} : Bool}, Eq.refute_char(Chr{uu}, Chr{13},
            cc => Bool.not(T.ch.ctl(cc)), eb, Equal.cong(Bool, Bool, xx => Bool.not(xx), T.ch.ctl(Chr{uu}),
            False{}, ee), {==}))
        case False{}:
          {==}

# a character that is no control is no newline
def sr.nlctl(+cc: Char, ee: {T.ch.ctl(cc) == False{} : Bool}) -> {T.ch.nl(cc) == False{} : Bool}:
  match cc:
    case Chr{+uu}:
      sr.nlctl.go(uu, U32.is_eq(uu, 10), U32.is_eq(uu, 13), {==}, {==}, ee)

# LStr's fast step, a basic string's character not a quote or a backslash
def sr.ff.bpush(
  bad: Bool,
  +cc: Char,
  ebad: {T.str.bad(Char.to_u32(cc), False{}) == bad : Bool},
  eq: {Char.is_eq(cc, '"') == False{} : Bool},
  eb: {Char.is_eq(cc, '\\') == False{} : Bool},
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

) -> {T.read.fast.push(bad, bd, rw, hs, he, pt, bf, T.LStr{}, bk, T.QBasic{}, sk, un, lf, at, cc)
  == T.read.fast.old(bd, rw, hs, he, pt, bf, T.LStr{}, bk, T.QBasic{}, sk, un, lf, at, cc) : T.St}:
  match bad:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, Char.is_eq(cc, '"'), False{}, eq) : {T.read.fast.cons(bd, rw, hs, he, pt, bf, T.LStr{}, bk,
        T.QBasic{}, sk, un, lf, at, cc) == T.read.once2(T.lex.str.go(_, False{}, True{}, M2.sip.S(bd, rw, hs, he, pt,
        bf, T.LStr{}, bk, T.QBasic{}, sk, un, lf, at), cc, T.QBasic{})) : T.St}
      %Equal.sym(Bool, Char.is_eq(cc, '\\'), False{}, eb) : {T.read.fast.cons(bd, rw, hs, he, pt, bf, T.LStr{}, bk,
        T.QBasic{}, sk, un, lf, at, cc) == T.read.once2(T.lex.str.bs(_, False{}, M2.sip.S(bd, rw, hs, he, pt, bf,
        T.LStr{}, bk, T.QBasic{}, sk, un, lf, at), cc, T.QBasic{})) : T.St}
      %Equal.sym(Bool, T.str.bad(Char.to_u32(cc), False{}), False{}, ebad) : {T.read.fast.cons(bd, rw, hs, he, pt,
        bf, T.LStr{}, bk, T.QBasic{}, sk, un, lf, at, cc) == T.read.once2(T.lex.str.char.go(_, M2.sip.S(bd, rw, hs,
        he, pt, bf, T.LStr{}, bk, T.QBasic{}, sk, un, lf, at), cc)) : T.St}
      {==}

# LStr's fast step in a basic string
def sr.ff.basic(
  qt: Bool,
  bs: Bool,
  +cc: Char,
  eq: {Char.is_eq(cc, '"') == qt : Bool},
  eb: {Char.is_eq(cc, '\\') == bs : Bool},
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

) -> {T.read.fast.basic(qt, bs, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc)
  == T.read.fast.old(bd, rw, hs, he, pt, bf, T.LStr{}, bk, T.QBasic{}, sk, un, lf, at, cc) : T.St}:
  match qt:
    case True{}:
      {==}
    case False{}:
      match bs:
        case True{}:
          {==}
        case False{}:
          sr.ff.bpush(T.str.bad(Char.to_u32(cc), False{}), cc, {==}, eq, eb, bd, rw, hs, he, pt, bf, bk, sk, un, lf,
            at)

# LStr's fast step in a literal string, a character not an apostrophe
def sr.ff.lpush(
  bad: Bool,
  +cc: Char,
  ebad: {T.str.bad(Char.to_u32(cc), False{}) == bad : Bool},
  eq: {Char.is_eq(cc, '\'') == False{} : Bool},
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

) -> {T.read.fast.push(bad, bd, rw, hs, he, pt, bf, T.LStr{}, bk, T.QLit{}, sk, un, lf, at, cc)
  == T.read.fast.old(bd, rw, hs, he, pt, bf, T.LStr{}, bk, T.QLit{}, sk, un, lf, at, cc) : T.St}:
  match bad:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, Char.is_eq(cc, '\''), False{}, eq) : {T.read.fast.cons(bd, rw, hs, he, pt, bf, T.LStr{}, bk,
        T.QLit{}, sk, un, lf, at, cc) == T.read.once2(T.lex.str.go(_, False{}, False{}, M2.sip.S(bd, rw, hs, he, pt,
        bf, T.LStr{}, bk, T.QLit{}, sk, un, lf, at), cc, T.QLit{})) : T.St}
      %Equal.sym(Bool, T.str.bad(Char.to_u32(cc), False{}), False{}, ebad) : {T.read.fast.cons(bd, rw, hs, he, pt,
        bf, T.LStr{}, bk, T.QLit{}, sk, un, lf, at, cc) == T.read.once2(T.lex.str.char.go(_, M2.sip.S(bd, rw, hs,
        he, pt, bf, T.LStr{}, bk, T.QLit{}, sk, un, lf, at), cc)) : T.St}
      {==}

# LStr's fast step in a literal string
def sr.ff.lit(
  qt: Bool,
  +cc: Char,
  eq: {Char.is_eq(cc, '\'') == qt : Bool},
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

) -> {T.read.fast.lit(qt, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc)
  == T.read.fast.old(bd, rw, hs, he, pt, bf, T.LStr{}, bk, T.QLit{}, sk, un, lf, at, cc) : T.St}:
  match qt:
    case True{}:
      {==}
    case False{}:
      sr.ff.lpush(T.str.bad(Char.to_u32(cc), False{}), cc, {==}, eq, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at)

# LStr's fast step, by the string's kind
def sr.ff.str(
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
  +cc: Char
) -> {T.read.fast.str(qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc)
  == T.read.fast.old(bd, rw, hs, he, pt, bf, T.LStr{}, bk, qk, sk, un, lf, at, cc) : T.St}:
  match qk:
    case T.QBasic{}:
      sr.ff.basic(Char.is_eq(cc, '"'), Char.is_eq(cc, '\\'), cc, {==}, {==}, bd, rw, hs, he, pt, bf, bk, sk, un, lf,
        at)
    case T.QLit{}:
      sr.ff.lit(Char.is_eq(cc, '\''), cc, {==}, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at)
    case T.QMulti{}:
      {==}
    case T.QMultiLit{}:
      {==}

# LKey's fast step: a bare character is pushed
def sr.ff.key(
  ok: Bool,
  +cc: Char,
  eo: {T.bare.at(cc) == ok : Bool},
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

) -> {T.read.fast.key(ok, bd, rw, hs, he, pt, bf, bk, qk, sk, un, lf, at, cc)
  == T.read.fast.old(bd, rw, hs, he, pt, bf, T.LKey{}, bk, qk, sk, un, lf, at, cc) : T.St}:
  match ok:
    case True{}:
      %Equal.sym(Bool, T.bare.at(cc), True{}, eo) : {T.read.fast.cons(bd, rw, hs, he, pt, bf, T.LKey{}, bk, qk, sk,
        un, lf, at, cc) == T.read.once2(T.lex.key.go(_, T.ch.sp(cc), Char.is_eq(cc, '.'), Char.is_eq(cc, '='),
        Char.is_eq(cc, '#'), T.ch.nl(cc), M2.sip.S(bd, rw, hs, he, pt, bf, T.LKey{}, bk, qk, sk, un, lf, at), cc))
        : T.St}
      {==}
    case False{}:
      {==}

# LBare's fast step: a character that ends no word is pushed
def sr.ff.bare(
  dl: Bool,
  +cc: Char,
  ed: {T.ch.delim(cc) == dl : Bool},
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

) -> {T.read.fast.bare(dl, bd, rw, hs, he, pt, bf, bk, qk, sk, un, lf, at, cc)
  == T.read.fast.old(bd, rw, hs, he, pt, bf, T.LBare{}, bk, qk, sk, un, lf, at, cc) : T.St}:
  match dl:
    case False{}:
      %Equal.sym(Bool, T.ch.delim(cc), False{}, ed) : {T.read.fast.cons(bd, rw, hs, he, pt, bf, T.LBare{}, bk, qk,
        sk, un, lf, at, cc) == T.read.once2(T.lex.bare.go(_, T.ch.space(cc), M2.sip.S(bd, rw, hs, he, pt, bf, T.LBare{},
        bk, qk, sk, un, lf, at), cc)) : T.St}
      {==}
    case True{}:
      {==}

# LCom's fast step: a character that is no control is passed over
def sr.ff.com(
  ct: Bool,
  +cc: Char,
  +ec: {T.ch.ctl(cc) == ct : Bool},
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

) -> {T.read.fast.com(ct, bd, rw, hs, he, pt, bf, bk, qk, sk, un, lf, at, cc)
  == T.read.fast.old(bd, rw, hs, he, pt, bf, T.LCom{}, bk, qk, sk, un, lf, at, cc) : T.St}:
  match ct:
    case False{}:
      %Equal.sym(Bool, T.ch.nl(cc), False{}, sr.nlctl(cc, ec)) : {M2.sip.S(bd, rw, hs, he, pt, bf, T.LCom{}, bk, qk,
        sk, un, lf, at) == T.read.once2(T.lex.com.go(_, T.ch.ctl(cc), U32.is_eq(Char.to_u32(cc), 9), M2.sip.S(bd, rw,
        hs, he, pt, bf, T.LCom{}, bk, qk, sk, un, lf, at), cc)) : T.St}
      %Equal.sym(Bool, T.ch.ctl(cc), False{}, ec) : {M2.sip.S(bd, rw, hs, he, pt, bf, T.LCom{}, bk, qk, sk, un, lf, at)
        == T.read.once2(T.lex.com.go(False{}, _, U32.is_eq(Char.to_u32(cc), 9), M2.sip.S(bd, rw, hs, he, pt, bf,
        T.LCom{}, bk, qk, sk, un, lf, at), cc)) : T.St}
      {==}
    case True{}:
      {==}

# LTop's fast step: blank space, and a newline, is passed over
def sr.ff.top(
  sp: Bool,
  nl: Bool,
  +cc: Char,
  es: {T.ch.sp(cc) == sp : Bool},
  en: {T.ch.nl(cc) == nl : Bool},
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
  +at: Bool
) -> {T.read.fast.ws(sp, nl, True{}, bd, rw, hs, he, pt, bf, T.LTop{}, bk, qk, sk, un, lf, at, cc)
  == T.read.fast.old(bd, rw, hs, he, pt, bf, T.LTop{}, bk, qk, sk, un, lf, at, cc) : T.St}:
  match sp:
    case True{}:
      %Equal.sym(Bool, T.ch.sp(cc), True{}, es) : {M2.sip.S(bd, rw, hs, he, pt, bf, T.LTop{}, bk, qk, sk, un, lf, at) ==
        T.read.once2(T.lex.top.go(_, T.ch.nl(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, '['), Char.is_eq(cc, '"'),
        Char.is_eq(cc, '\''), T.bare.at(cc), M2.sip.S(bd, rw, hs, he, pt, bf, T.LTop{}, bk, qk, sk, un, lf, at), cc)) :
        T.St}
      {==}
    case False{}:
      match nl:
        case True{}:
          %Equal.sym(Bool, T.ch.sp(cc), False{}, es) : {M2.sip.S(bd, rw, hs, he, pt, bf, T.LTop{}, bk, qk, sk, un, lf,
            at) == T.read.once2(T.lex.top.go(_, T.ch.nl(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, '['), Char.is_eq(cc,
            '"'), Char.is_eq(cc, '\''), T.bare.at(cc), M2.sip.S(bd, rw, hs, he, pt, bf, T.LTop{}, bk, qk, sk, un, lf,
            at), cc)) : T.St}
          %Equal.sym(Bool, T.ch.nl(cc), True{}, en) : {M2.sip.S(bd, rw, hs, he, pt, bf, T.LTop{}, bk, qk, sk, un, lf,
              at)
            == T.read.once2(T.lex.top.go(False{}, _, Char.is_eq(cc, '#'), Char.is_eq(cc, '['), Char.is_eq(cc, '"'),
            Char.is_eq(cc, '\''), T.bare.at(cc), M2.sip.S(bd, rw, hs, he, pt, bf, T.LTop{}, bk, qk, sk, un, lf, at),
                cc))
            : T.St}
          {==}
        case False{}:
          {==}

# LArr's fast step: blank space, and a newline, is passed over
def sr.ff.arr(
  sp: Bool,
  nl: Bool,
  +cc: Char,
  es: {T.ch.sp(cc) == sp : Bool},
  en: {T.ch.nl(cc) == nl : Bool},
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
  +at: Bool
) -> {T.read.fast.ws(sp, nl, True{}, bd, rw, hs, he, pt, bf, T.LArr{}, bk, qk, sk, un, lf, at, cc)
  == T.read.fast.old(bd, rw, hs, he, pt, bf, T.LArr{}, bk, qk, sk, un, lf, at, cc) : T.St}:
  match sp:
    case True{}:
      %Equal.sym(Bool, T.ch.sp(cc), True{}, es) : {M2.sip.S(bd, rw, hs, he, pt, bf, T.LArr{}, bk, qk, sk, un, lf, at) ==
        T.read.once2(T.lex.arr.go(_, T.ch.nl(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, ']'), M2.sip.S(bd, rw, hs, he, pt,
        bf, T.LArr{}, bk, qk, sk, un, lf, at), cc)) : T.St}
      {==}
    case False{}:
      match nl:
        case True{}:
          %Equal.sym(Bool, T.ch.sp(cc), False{}, es) : {M2.sip.S(bd, rw, hs, he, pt, bf, T.LArr{}, bk, qk, sk, un, lf,
            at) == T.read.once2(T.lex.arr.go(_, T.ch.nl(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, ']'), M2.sip.S(bd, rw,
            hs, he, pt, bf, T.LArr{}, bk, qk, sk, un, lf, at), cc)) : T.St}
          %Equal.sym(Bool, T.ch.nl(cc), True{}, en) : {M2.sip.S(bd, rw, hs, he, pt, bf, T.LArr{}, bk, qk, sk, un, lf,
              at)
            == T.read.once2(T.lex.arr.go(False{}, _, Char.is_eq(cc, '#'), Char.is_eq(cc, ']'), M2.sip.S(bd, rw, hs, he,
            pt, bf, T.LArr{}, bk, qk, sk, un, lf, at), cc)) : T.St}
          {==}
        case False{}:
          {==}

# LArrC's fast step: blank space, and a newline, is passed over
def sr.ff.arrc(
  sp: Bool,
  nl: Bool,
  +cc: Char,
  es: {T.ch.sp(cc) == sp : Bool},
  en: {T.ch.nl(cc) == nl : Bool},
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
  +at: Bool
) -> {T.read.fast.ws(sp, nl, True{}, bd, rw, hs, he, pt, bf, T.LArrC{}, bk, qk, sk, un, lf, at, cc)
  == T.read.fast.old(bd, rw, hs, he, pt, bf, T.LArrC{}, bk, qk, sk, un, lf, at, cc) : T.St}:
  match sp:
    case True{}:
      %Equal.sym(Bool, T.ch.sp(cc), True{}, es) : {M2.sip.S(bd, rw, hs, he, pt, bf, T.LArrC{}, bk, qk, sk, un, lf,
          at) ==
        T.read.once2(T.lex.arrc.go(_, T.ch.nl(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, ','), Char.is_eq(cc, ']'),
        M2.sip.S(bd, rw, hs, he, pt, bf, T.LArrC{}, bk, qk, sk, un, lf, at), cc)) : T.St}
      {==}
    case False{}:
      match nl:
        case True{}:
          %Equal.sym(Bool, T.ch.sp(cc), False{}, es) : {M2.sip.S(bd, rw, hs, he, pt, bf, T.LArrC{}, bk, qk, sk, un, lf,
            at) == T.read.once2(T.lex.arrc.go(_, T.ch.nl(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, ','), Char.is_eq(cc,
            ']'), M2.sip.S(bd, rw, hs, he, pt, bf, T.LArrC{}, bk, qk, sk, un, lf, at), cc)) : T.St}
          %Equal.sym(Bool, T.ch.nl(cc), True{}, en) : {M2.sip.S(bd, rw, hs, he, pt, bf, T.LArrC{}, bk, qk, sk, un, lf,
            at) == T.read.once2(T.lex.arrc.go(False{}, _, Char.is_eq(cc, '#'), Char.is_eq(cc, ','), Char.is_eq(cc,
            ']'), M2.sip.S(bd, rw, hs, he, pt, bf, T.LArrC{}, bk, qk, sk, un, lf, at), cc)) : T.St}
          {==}
        case False{}:
          {==}

# LLine's fast step: blank space is passed over
def sr.ff.line(
  sp: Bool,
  nl: Bool,
  +cc: Char,
  es: {T.ch.sp(cc) == sp : Bool},
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
  +at: Bool
) -> {T.read.fast.ws(sp, nl, False{}, bd, rw, hs, he, pt, bf, T.LLine{}, bk, qk, sk, un, lf, at, cc)
  == T.read.fast.old(bd, rw, hs, he, pt, bf, T.LLine{}, bk, qk, sk, un, lf, at, cc) : T.St}:
  match sp:
    case True{}:
      %Equal.sym(Bool, T.ch.sp(cc), True{}, es) : {M2.sip.S(bd, rw, hs, he, pt, bf, T.LLine{}, bk, qk, sk, un, lf,
          at) ==
        T.read.once2(T.lex.line.go(_, Char.is_eq(cc, '#'), T.ch.nl(cc), M2.sip.S(bd, rw, hs, he, pt, bf, T.LLine{}, bk,
        qk, sk, un, lf, at), cc)) : T.St}
      {==}
    case False{}:
      match nl:
        case True{}:
          {==}
        case False{}:
          {==}

# LVal's fast step: blank space is passed over
def sr.ff.val(
  sp: Bool,
  nl: Bool,
  +cc: Char,
  es: {T.ch.sp(cc) == sp : Bool},
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
  +at: Bool
) -> {T.read.fast.ws(sp, nl, False{}, bd, rw, hs, he, pt, bf, T.LVal{}, bk, qk, sk, un, lf, at, cc)
  == T.read.fast.old(bd, rw, hs, he, pt, bf, T.LVal{}, bk, qk, sk, un, lf, at, cc) : T.St}:
  match sp:
    case True{}:
      %Equal.sym(Bool, T.ch.sp(cc), True{}, es) : {M2.sip.S(bd, rw, hs, he, pt, bf, T.LVal{}, bk, qk, sk, un, lf, at) ==
        T.read.once2(T.lex.val.go(_, T.ch.nl(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, '"'), Char.is_eq(cc, '\''),
        Char.is_eq(cc, '['), Char.is_eq(cc, Chr{123}), M2.sip.S(bd, rw, hs, he, pt, bf, T.LVal{}, bk, qk, sk, un, lf,
        at), cc)) : T.St}
      {==}
    case False{}:
      match nl:
        case True{}:
          {==}
        case False{}:
          {==}

# LAfter's fast step: blank space is passed over
def sr.ff.after(
  sp: Bool,
  nl: Bool,
  +cc: Char,
  es: {T.ch.sp(cc) == sp : Bool},
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
  +at: Bool
) -> {T.read.fast.ws(sp, nl, False{}, bd, rw, hs, he, pt, bf, T.LAfter{}, bk, qk, sk, un, lf, at, cc)
  == T.read.fast.old(bd, rw, hs, he, pt, bf, T.LAfter{}, bk, qk, sk, un, lf, at, cc) : T.St}:
  match sp:
    case True{}:
      %Equal.sym(Bool, T.ch.sp(cc), True{}, es) : {M2.sip.S(bd, rw, hs, he, pt, bf, T.LAfter{}, bk, qk, sk, un, lf, at)
        == T.read.once2(T.lex.after.go(_, Char.is_eq(cc, '.'), Char.is_eq(cc, '='), Char.is_eq(cc, '#'), T.ch.nl(cc),
        M2.sip.S(bd, rw, hs, he, pt, bf, T.LAfter{}, bk, qk, sk, un, lf, at), cc)) : T.St}
      {==}
    case False{}:
      match nl:
        case True{}:
          {==}
        case False{}:
          {==}

# LInl's fast step: blank space is passed over
def sr.ff.inl(
  sp: Bool,
  nl: Bool,
  +cc: Char,
  es: {T.ch.sp(cc) == sp : Bool},
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
  +at: Bool
) -> {T.read.fast.ws(sp, nl, False{}, bd, rw, hs, he, pt, bf, T.LInl{}, bk, qk, sk, un, lf, at, cc)
  == T.read.fast.old(bd, rw, hs, he, pt, bf, T.LInl{}, bk, qk, sk, un, lf, at, cc) : T.St}:
  match sp:
    case True{}:
      %Equal.sym(Bool, T.ch.sp(cc), True{}, es) : {M2.sip.S(bd, rw, hs, he, pt, bf, T.LInl{}, bk, qk, sk, un, lf, at) ==
        T.read.once2(T.lex.inl.go(_, Char.is_eq(cc, '#'), Char.is_eq(cc, Chr{125}), T.ch.nl(cc), M2.sip.S(bd, rw, hs,
            he,
        pt, bf, T.LInl{}, bk, qk, sk, un, lf, at), cc)) : T.St}
      {==}
    case False{}:
      match nl:
        case True{}:
          {==}
        case False{}:
          {==}

# LInlK's fast step: blank space is passed over
def sr.ff.inlk(
  sp: Bool,
  nl: Bool,
  +cc: Char,
  es: {T.ch.sp(cc) == sp : Bool},
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
  +at: Bool
) -> {T.read.fast.ws(sp, nl, False{}, bd, rw, hs, he, pt, bf, T.LInlK{}, bk, qk, sk, un, lf, at, cc)
  == T.read.fast.old(bd, rw, hs, he, pt, bf, T.LInlK{}, bk, qk, sk, un, lf, at, cc) : T.St}:
  match sp:
    case True{}:
      %Equal.sym(Bool, T.ch.sp(cc), True{}, es) : {M2.sip.S(bd, rw, hs, he, pt, bf, T.LInlK{}, bk, qk, sk, un, lf,
          at) ==
        T.read.once2(T.lex.inlk.go(_, Char.is_eq(cc, '#'), T.ch.nl(cc), M2.sip.S(bd, rw, hs, he, pt, bf, T.LInlK{}, bk,
        qk, sk, un, lf, at), cc)) : T.St}
      {==}
    case False{}:
      match nl:
        case True{}:
          {==}
        case False{}:
          {==}

# LInlC's fast step: blank space is passed over
def sr.ff.inlc(
  sp: Bool,
  nl: Bool,
  +cc: Char,
  es: {T.ch.sp(cc) == sp : Bool},
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
  +at: Bool
) -> {T.read.fast.ws(sp, nl, False{}, bd, rw, hs, he, pt, bf, T.LInlC{}, bk, qk, sk, un, lf, at, cc)
  == T.read.fast.old(bd, rw, hs, he, pt, bf, T.LInlC{}, bk, qk, sk, un, lf, at, cc) : T.St}:
  match sp:
    case True{}:
      %Equal.sym(Bool, T.ch.sp(cc), True{}, es) : {M2.sip.S(bd, rw, hs, he, pt, bf, T.LInlC{}, bk, qk, sk, un, lf,
          at) ==
        T.read.once2(T.lex.inlc.go(_, Char.is_eq(cc, '#'), Char.is_eq(cc, ','), Char.is_eq(cc, Chr{125}), T.ch.nl(cc),
        M2.sip.S(bd, rw, hs, he, pt, bf, T.LInlC{}, bk, qk, sk, un, lf, at), cc)) : T.St}
      {==}
    case False{}:
      match nl:
        case True{}:
          {==}
        case False{}:
          {==}

# the fast step is the full step, for every lex state and character
def sr.ff(
  lx: T.Lex,
  +qk: T.QKind,
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
  +cc: Char
) -> {T.read.fast.lex(lx, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc)
  == T.read.fast.old(bd, rw, hs, he, pt, bf, lx, bk, qk, sk, un, lf, at, cc) : T.St}:
  match lx:
    case T.LStr{}:
      sr.ff.str(qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc)
    case T.LKey{}:
      sr.ff.key(T.bare.at(cc), cc, {==}, bd, rw, hs, he, pt, bf, bk, qk, sk, un, lf, at)
    case T.LBare{}:
      sr.ff.bare(T.ch.delim(cc), cc, {==}, bd, rw, hs, he, pt, bf, bk, qk, sk, un, lf, at)
    case T.LCom{}:
      sr.ff.com(T.ch.ctl(cc), cc, {==}, bd, rw, hs, he, pt, bf, bk, qk, sk, un, lf, at)
    case T.LTop{}:
      sr.ff.top(T.ch.sp(cc), T.ch.nl(cc), cc, {==}, {==}, bd, rw, hs, he, pt, bf, bk, qk, sk, un, lf,
        at)
    case T.LArr{}:
      sr.ff.arr(T.ch.sp(cc), T.ch.nl(cc), cc, {==}, {==}, bd, rw, hs, he, pt, bf, bk, qk, sk, un, lf,
        at)
    case T.LArrC{}:
      sr.ff.arrc(T.ch.sp(cc), T.ch.nl(cc), cc, {==}, {==}, bd, rw, hs, he, pt, bf, bk, qk, sk, un, lf,
        at)
    case T.LLine{}:
      sr.ff.line(T.ch.sp(cc), T.ch.nl(cc), cc, {==}, bd, rw, hs, he, pt, bf, bk, qk, sk, un, lf,
        at)
    case T.LVal{}:
      sr.ff.val(T.ch.sp(cc), T.ch.nl(cc), cc, {==}, bd, rw, hs, he, pt, bf, bk, qk, sk, un, lf,
        at)
    case T.LAfter{}:
      sr.ff.after(T.ch.sp(cc), T.ch.nl(cc), cc, {==}, bd, rw, hs, he, pt, bf, bk, qk, sk, un, lf,
        at)
    case T.LInl{}:
      sr.ff.inl(T.ch.sp(cc), T.ch.nl(cc), cc, {==}, bd, rw, hs, he, pt, bf, bk, qk, sk, un, lf,
        at)
    case T.LInlK{}:
      sr.ff.inlk(T.ch.sp(cc), T.ch.nl(cc), cc, {==}, bd, rw, hs, he, pt, bf, bk, qk, sk, un, lf,
        at)
    case T.LInlC{}:
      sr.ff.inlc(T.ch.sp(cc), T.ch.nl(cc), cc, {==}, bd, rw, hs, he, pt, bf, bk, qk, sk, un, lf,
        at)
    case T.LKeyDot{}:
      {==}
    case T.LKeyQ{}:
      {==}
    case T.LKeyE{}:
      {==}
    case T.LKeyU{}:
      {==}
    case T.LQ{}:
      {==}
    case T.LQ2{}:
      {==}
    case T.LEsc{}:
      {==}
    case T.LUni{}:
      {==}
    case T.LFold{}:
      {==}
    case T.LMq{}:
      {==}
    case T.LMqEnd{}:
      {==}
    case T.LTrim{}:
      {==}
    case T.LTrim2{}:
      {==}
    case T.LDate{}:
      {==}
    case T.LHead{}:
      {==}
    case T.LHeadGap{}:
      {==}
    case T.LHeadDot{}:
      {==}
    case T.LHeadQ{}:
      {==}
    case T.LHeadE{}:
      {==}
    case T.LHeadU{}:
      {==}
    case T.LHeadR{}:
      {==}
    case T.LSink{}:
      {==}

# WP-A: an error stays, and so do the rows. A walk that is refused (a
# duplicate key, a table defined twice) sets the scanner's error and lets it
# read on, and every later walk changes nothing (failed_walk_changes_nothing).
# So once a state has an error, every step keeps its error and its rows, and
# parse ends with the document of that error and those rows, sealed. The
# proof follows every step of the scanner: a step that fails keeps the first
# error (err.first), a step that places a value walks with the error set,
# and every other step rebuilds the state with the same error and rows.

# the error and the root's rows a state holds
type FzP is Data:
  FzP{bad: String, rows: List<&2, T.Val>}

# the error and the rows of a state
def fz.p(st: T.St) -> FzP:
  match st:
    case T.St{bd, rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
      FzP{bd, rw}

# the error of a pair
def fz.pb(pp: FzP) -> String:
  match pp:
    case FzP{bd, _rw}:
      bd

# the document of a pair, its rows sealed
def fz.dp(pp: FzP) -> T.Doc:
  match pp:
    case FzP{bd, rw}:
      T.Doc{bd, T.rows.seal(rw)}

# a state that holds the error SCon{b0, bs} and the rows rr
def fz.K(st: T.St, b0: Char, bs: String, rr: List<&2, T.Val>) -> Data:
  {fz.p(st) == FzP{SCon{b0, bs}, rr} : FzP}

# the error is not empty
def fz.ne(
  bd: String,
  rw: List<&2, T.Val>,
  b0: Char,
  bs: String,
  rr: List<&2, T.Val>,
  h: {FzP{bd, rw} == FzP{SCon{b0, bs}, rr} : FzP}
) -> {String.is_empty(bd) == False{} : Bool}:
  Equal.cong(FzP, Bool, pp => String.is_empty(fz.pb(pp)), FzP{bd, rw}, FzP{SCon{b0, bs}, rr}, h)

# a second error leaves the first
def fz.e(
  +bd: String,
  +rw: List<&2, T.Val>,
  why: String,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  +h: {FzP{bd, rw} == FzP{SCon{b0, bs}, rr} : FzP}
) -> {FzP{T.err.first(bd, why), rw} == FzP{SCon{b0, bs}, rr} : FzP}:
  %Equal.sym(Bool, String.is_empty(bd), False{}, fz.ne(bd, rw, b0, bs, rr, h)) : {FzP{T.err.first.go(_, bd, why), rw}
    == FzP{SCon{b0, bs}, rr} : FzP}
  h

# the document of a state that holds them
def fz.doc(
  +bd: String,
  +rw: List<&2, T.Val>,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: {FzP{bd, rw} == FzP{SCon{b0, bs}, rr} : FzP}
) -> {T.Doc{bd, T.rows.seal(rw)} == T.Doc{SCon{b0, bs}, T.rows.seal(rr)} : T.Doc}:
  Equal.cong(FzP, T.Doc, pp => fz.dp(pp), FzP{bd, rw}, FzP{SCon{b0, bs}, rr}, h)

# and with a second error, which leaves the first
def fz.doce(
  +bd: String,
  +rw: List<&2, T.Val>,
  +why: String,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  +h: {FzP{bd, rw} == FzP{SCon{b0, bs}, rr} : FzP}
) -> {T.Doc{T.err.first(bd, why), T.rows.seal(rw)} == T.Doc{SCon{b0, bs}, T.rows.seal(rr)} : T.Doc}:
  Equal.cong(FzP, T.Doc, pp => fz.dp(pp), FzP{T.err.first(bd, why), rw}, FzP{SCon{b0, bs}, rr}, fz.e(bd, rw, why,
    b0, bs, rr, h))

# a failed step keeps them
def fz.err(
  +st: T.St,
  +why: String,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.st.err(st, why), b0, bs, rr):
  match st:
    case T.St{bd, rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
      fz.e(bd, rw, why, b0, bs, rr, h)

# a value placed where the stack puts it: a walk with the error set
def fz.top(
  +sk: List<&2, T.Ctx>,
  +vv: T.Val,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +ld: Bool,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  +h: {FzP{bd, rw} == FzP{SCon{b0, bs}, rr} : FzP}
) -> {fz.p(T.take.top(sk, vv, bd, rw, hs, he, pt, bk, qk, un, lf, at, ld)) == FzP{SCon{b0, bs}, rr} : FzP}:
  match sk:
    case []:
      %Equal.sym(T.End, T.tree.walk(T.path.cat(he, pt), T.Tw{rw, T.JPut{vv}, [], bd, "", hs, False{}}, T.path.len(he,
        0)), T.End{rw, bd, hs}, L1.failed_walk_changes_nothing(T.path.cat(he, pt), rw, T.JPut{vv}, bd, "", hs,
          False{}, T.path.len(he, 0),
        fz.ne(bd, rw, b0, bs, rr, h))) : {fz.p(T.take.root(_, he, bk, qk, un, lf, at, ld)) == FzP{SCon{b0, bs}, rr}
        : FzP}
      h
    case T.CArr{_items, _saved, _at2} <> _rest:
      h
    case T.CInl{+inl, +saved, +at2} <> +rest:
      %Equal.sym(T.End, T.tree.walk(List.reverse(&2, String, pt), T.Tw{inl, T.JPut{vv}, [], bd, "", [], True{}}, 0),
        T.End{inl, bd, []}, L1.failed_walk_changes_nothing(List.reverse(&2, String, pt), inl, T.JPut{vv}, bd, "",
          [], True{}, 0, fz.ne(bd,
        rw, b0, bs, rr, h))) : {fz.p(T.take.inl(_, rw, hs, at2, saved, rest, bk, qk, un, lf, at, ld))
        == FzP{SCon{b0, bs}, rr} : FzP}
      h

# a value placed keeps them
def fz.take(
  +st: T.St,
  +vv: T.Val,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.val.take(st, vv), b0, bs, rr):
  match st:
    case T.St{bd, rw, hs, he, pt, _bf, _lx, bk, qk, sk, _hd, un, lf, at, ld}:
      fz.top(sk, vv, bd, rw, hs, he, pt, bk, qk, un, lf, at, ld, b0, bs, rr, h)

# a newline after a root value
def fz.bll(
  +lx: T.Lex,
  +st: T.St,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.bare.line.lex(lx, st), b0, bs, rr):
  match lx:
    case T.LTop{}:
      h
    case T.LLine{}:
      match st:
        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
          h
    case T.LKey{}:
      h
    case T.LKeyDot{}:
      h
    case T.LAfter{}:
      h
    case T.LKeyQ{}:
      h
    case T.LKeyE{}:
      h
    case T.LKeyU{}:
      h
    case T.LVal{}:
      h
    case T.LQ{}:
      h
    case T.LQ2{}:
      h
    case T.LStr{}:
      h
    case T.LEsc{}:
      h
    case T.LUni{}:
      h
    case T.LFold{}:
      h
    case T.LMq{}:
      h
    case T.LMqEnd{}:
      h
    case T.LTrim{}:
      h
    case T.LTrim2{}:
      h
    case T.LBare{}:
      h
    case T.LDate{}:
      h
    case T.LCom{}:
      h
    case T.LHead{}:
      h
    case T.LHeadGap{}:
      h
    case T.LHeadDot{}:
      h
    case T.LHeadQ{}:
      h
    case T.LHeadE{}:
      h
    case T.LHeadU{}:
      h
    case T.LHeadR{}:
      h
    case T.LArr{}:
      h
    case T.LArrC{}:
      h
    case T.LInl{}:
      h
    case T.LInlK{}:
      h
    case T.LInlC{}:
      h
    case T.LSink{}:
      h

# a newline that ended a root value
def fz.bline(
  +nl: Bool,
  +st: T.St,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.bare.line(st, nl), b0, bs, rr):
  match nl:
    case True{}:
      match st:
        case T.St{bd, rw, hs, he, pt, bf, +lx, bk, qk, sk, hd, un, lf, at, ld}:
          fz.bll(lx, T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, hd, un, lf, at, ld}, b0, bs, rr, h)
    case False{}:
      h

# the delimiter after a value, held or passed over
def fz.bhold(
  +hold: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.bare.hold(st, cc, hold), b0, bs, rr):
  match hold:
    case True{}:
      match st:
        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
          h
    case False{}:
      fz.bline(T.ch.nl(cc), st, b0, bs, rr, h)

# a bare word read
def fz.got(
  +gg: T.Got,
  +st: T.St,
  +cc: Char,
  +hold: Bool,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.bare.got(gg, st, cc, hold), b0, bs, rr):
  match gg:
    case T.GotBad{why}:
      fz.err(st, why, b0, bs, rr, h)
    case T.GotVal{vv}:
      fz.bhold(hold, T.val.take(st, vv), cc, b0, bs, rr, fz.take(st, vv, b0, bs, rr, h))

# a bare word finished
def fz.finish(
  +st: T.St,
  +cc: Char,
  +hold: Bool,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.bare.finish(st, cc, hold), b0, bs, rr):
  match st:
    case T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, hd, un, lf, at, ld}:
      fz.got(T.word.val(List.reverse(&2, Char, bf)), T.St{bd, rw, hs, he, pt, [], lx, bk, qk, sk, hd, un, lf, at, ld},
        cc, hold, b0, bs, rr, h)

# a string finished
def fz.sfin(
  +st: T.St,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.str.fin(st), b0, bs, rr):
  match st:
    case T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, hd, un, lf, at, ld}:
      fz.take(T.St{bd, rw, hs, he, pt, [], lx, bk, qk, sk, hd, un, lf, at, ld}, T.VStr{T.buf.str(bf)}, b0, bs, rr, h)

# a segment pushed
def fz.segp(
  +st: T.St,
  +lex: T.Lex,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.seg.push(st, lex), b0, bs, rr):
  match st:
    case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
      h

# a comment entered
def fz.com(
  +st: T.St,
  +back: T.Lex,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.com.enter(st, back), b0, bs, rr):
  match st:
    case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
      h

# a header's walk, with the error set
def fz.hjob(
  arr: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +segs: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ld: Bool,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  +h: {FzP{bd, rw} == FzP{SCon{b0, bs}, rr} : FzP}
) -> {fz.p(T.head.job(arr, bd, rw, hs, segs, bk, qk, un, lf, ld)) == FzP{SCon{b0, bs}, rr} : FzP}:
  match arr:
    case True{}:
      %Equal.sym(T.End, T.tree.walk(segs, T.Tw{rw, T.JAot{}, [], bd, "", hs, False{}}, 0), T.End{rw, bd, hs},
        L1.failed_walk_changes_nothing(segs, rw, T.JAot{}, bd, "", hs, False{}, 0, fz.ne(bd, rw, b0, bs, rr, h)))
        : {fz.p(T.head.apply(_, segs, bk, qk, un, lf, ld)) == FzP{SCon{b0, bs}, rr} : FzP}
      h
    case False{}:
      %Equal.sym(T.End, T.tree.walk(segs, T.Tw{rw, T.JDef{}, [], bd, "", hs, False{}}, 0), T.End{rw, bd, hs},
        L1.failed_walk_changes_nothing(segs, rw, T.JDef{}, bd, "", hs, False{}, 0, fz.ne(bd, rw, b0, bs, rr, h)))
        : {fz.p(T.head.apply(_, segs, bk, qk, un, lf, ld)) == FzP{SCon{b0, bs}, rr} : FzP}
      h

# a header ready
def fz.hgo(
  +empty: Bool,
  +st: T.St,
  +segs: List<&2, String>,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.head.go(empty, st, segs), b0, bs, rr):
  match empty:
    case True{}:
      fz.err(st, "empty key", b0, bs, rr, h)
    case False{}:
      match st:
        case T.St{bd, rw, hs, _he, _pt, _bf, _lx, bk, qk, _sk, _hd, un, lf, at, ld}:
          fz.hjob(at, bd, rw, hs, segs, bk, qk, un, lf, ld, b0, bs, rr, h)

# a header's segments
def fz.huse(
  +st: T.St,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.head.use(st), b0, bs, rr):
  match st:
    case T.St{bd, rw, hs, he, +pt, bf, lx, bk, qk, sk, hd, un, lf, at, ld}:
      fz.hgo(List.is_empty(&2, String, pt), T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, hd, un, lf, at, ld},
        List.reverse(&2, String, pt), b0, bs, rr, h)

# a header's last segment
def fz.hfb(
  +empty: Bool,
  +st: T.St,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.head.fin.buf(empty, st), b0, bs, rr):
  match empty:
    case True{}:
      fz.huse(st, b0, bs, rr, h)
    case False{}:
      fz.huse(T.seg.push(st, T.LTop{}), b0, bs, rr, fz.segp(st, T.LTop{}, b0, bs, rr, h))

# a header closed
def fz.hfin(
  +st: T.St,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.head.fin(st), b0, bs, rr):
  match st:
    case T.St{bd, rw, hs, he, pt, +bf, lx, bk, qk, sk, hd, un, lf, at, ld}:
      fz.hfb(List.is_empty(&2, Char, bf), T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, hd, un, lf, at, ld}, b0, bs,
        rr, h)

# an array closed with the error set
def fz.atop(
  +sk: List<&2, T.Ctx>,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +ld: Bool,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  +h: {FzP{bd, rw} == FzP{SCon{b0, bs}, rr} : FzP}
) -> {fz.p(T.arr.top(sk, bd, rw, hs, bk, qk, un, lf, at, ld)) == FzP{SCon{b0, bs}, rr} : FzP}:
  match sk:
    case []:
      fz.e(bd, rw, "unclosed", b0, bs, rr, h)
    case T.CArr{items, pt, he} <> rest:
      fz.take(T.St{bd, rw, hs, he, pt, [], T.LTop{}, bk, qk, rest, T.HNone{}, un, lf, at, ld}, T.VArr{List.reverse(&2,
        T.Val, items)}, b0, bs, rr, h)
    case T.CInl{_items, _pt, _he} <> _rest:
      fz.e(bd, rw, "unclosed", b0, bs, rr, h)

# an array closed
def fz.aclose(
  +st: T.St,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.arr.close(st), b0, bs, rr):
  match st:
    case T.St{bd, rw, hs, _he, _pt, _bf, _lx, bk, qk, sk, _hd, un, lf, at, ld}:
      fz.atop(sk, bd, rw, hs, bk, qk, un, lf, at, ld, b0, bs, rr, h)

# an inline table closed with the error set
def fz.itop(
  +sk: List<&2, T.Ctx>,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +ld: Bool,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  +h: {FzP{bd, rw} == FzP{SCon{b0, bs}, rr} : FzP}
) -> {fz.p(T.inl.top(sk, bd, rw, hs, bk, qk, un, lf, at, ld)) == FzP{SCon{b0, bs}, rr} : FzP}:
  match sk:
    case []:
      fz.e(bd, rw, "unclosed", b0, bs, rr, h)
    case T.CInl{items, pt, he} <> rest:
      fz.take(T.St{bd, rw, hs, he, pt, [], T.LTop{}, bk, qk, rest, T.HNone{}, un, lf, at, ld},
        T.VInl{T.inl.seal(items)}, b0, bs, rr, h)
    case T.CArr{_items, _pt, _he} <> _rest:
      fz.e(bd, rw, "unclosed", b0, bs, rr, h)

# an inline table closed
def fz.iclose(
  +st: T.St,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.inl.close(st), b0, bs, rr):
  match st:
    case T.St{bd, rw, hs, _he, _pt, _bf, _lx, bk, qk, sk, _hd, un, lf, at, ld}:
      fz.itop(sk, bd, rw, hs, bk, qk, un, lf, at, ld, b0, bs, rr, h)

# LTop
def fz.x.top(
  +sp: Bool,
  +nl: Bool,
  +hash: Bool,
  +br: Bool,
  +qq: Bool,
  +lit: Bool,
  +bare: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.top.go(sp, nl, hash, br, qq, lit, bare, st, cc), b0, bs, rr):
  match sp:
    case True{}:
      h
    case False{}:
      match nl:
        case True{}:
          h
        case False{}:
          match hash:
            case True{}:
              match st:
                case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
                  h
            case False{}:
              match br:
                case True{}:
                  match st:
                    case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
                      h
                case False{}:
                  match qq:
                    case True{}:
                      match st:
                        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
                          h
                    case False{}:
                      match lit:
                        case True{}:
                          match st:
                            case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
                              h
                        case False{}:
                          match bare:
                            case True{}:
                              match st:
                                case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
                                  h
                            case False{}:
                              fz.err(st, "invalid key", b0, bs, rr, h)

# LLine
def fz.x.line(
  +sp: Bool,
  +hash: Bool,
  +nl: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.line.go(sp, hash, nl, st, cc), b0, bs, rr):
  match sp:
    case True{}:
      h
    case False{}:
      match hash:
        case True{}:
          match st:
            case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
              h
        case False{}:
          match nl:
            case True{}:
              match st:
                case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
                  h
            case False{}:
              fz.err(st, "newline required", b0, bs, rr, h)

# a segment ended
def fz.kend.go(
  +empty: Bool,
  +st: T.St,
  +lex: T.Lex,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.key.end.go(empty, st, lex), b0, bs, rr):
  match empty:
    case True{}:
      fz.err(st, "empty key", b0, bs, rr, h)
    case False{}:
      match st:
        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
          h

# a segment ended
def fz.kend(
  +st: T.St,
  +next: T.Lex,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.key.end(st, next), b0, bs, rr):
  match st:
    case T.St{bd, rw, hs, he, pt, +bf, lx, bk, qk, sk, hd, un, lf, at, ld}:
      fz.kend.go(List.is_empty(&2, Char, bf), T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, hd, un, lf, at,
        ld}, next, b0, bs, rr, h)

# LKey
def fz.x.key(
  +bare: Bool,
  +sp: Bool,
  +dot: Bool,
  +eq: Bool,
  +hash: Bool,
  +nl: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.key.go(bare, sp, dot, eq, hash, nl, st, cc), b0, bs, rr):
  match bare:
    case True{}:
      match st:
        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
          h
    case False{}:
      match sp:
        case True{}:
          fz.kend(st, T.LAfter{}, b0, bs, rr, h)
        case False{}:
          match dot:
            case True{}:
              fz.kend(st, T.LKeyDot{}, b0, bs, rr, h)
            case False{}:
              match eq:
                case True{}:
                  fz.kend(st, T.LVal{}, b0, bs, rr, h)
                case False{}:
                  match hash:
                    case True{}:
                      fz.com(T.lex.key.end(st, T.LAfter{}), T.LAfter{}, b0, bs, rr, fz.kend(st, T.LAfter{}, b0, bs,
                        rr, h))
                    case False{}:
                      match nl:
                        case True{}:
                          fz.err(st, "newline in key", b0, bs, rr, h)
                        case False{}:
                          fz.err(st, "invalid key", b0, bs, rr, h)

# LKeyDot, a bare segment
def fz.x.kdot.bare(
  +bare: Bool,
  +dot: Bool,
  +nl: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.kdot.bare(bare, dot, nl, st, cc), b0, bs, rr):
  match bare:
    case True{}:
      match st:
        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
          h
    case False{}:
      match dot:
        case True{}:
          fz.err(st, "empty key", b0, bs, rr, h)
        case False{}:
          match nl:
            case True{}:
              fz.err(st, "newline in key", b0, bs, rr, h)
            case False{}:
              fz.err(st, "invalid key", b0, bs, rr, h)

# LKeyDot
def fz.x.kdot(
  +sp: Bool,
  +qq: Bool,
  +lit: Bool,
  +dot: Bool,
  +nl: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.kdot.go(sp, qq, lit, dot, nl, st, cc), b0, bs, rr):
  match sp:
    case True{}:
      h
    case False{}:
      match qq:
        case True{}:
          match st:
            case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
              h
        case False{}:
          match lit:
            case True{}:
              match st:
                case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
                  h
            case False{}:
              fz.x.kdot.bare(T.bare.at(cc), dot, nl, st, cc, b0, bs, rr, h)

# LAfter
def fz.x.after(
  +sp: Bool,
  +dot: Bool,
  +eq: Bool,
  +hash: Bool,
  +nl: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.after.go(sp, dot, eq, hash, nl, st, cc), b0, bs, rr):
  match sp:
    case True{}:
      h
    case False{}:
      match dot:
        case True{}:
          match st:
            case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
              h
        case False{}:
          match eq:
            case True{}:
              match st:
                case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
                  h
            case False{}:
              match hash:
                case True{}:
                  match st:
                    case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
                      h
                case False{}:
                  match nl:
                    case True{}:
                      fz.err(st, "newline in key", b0, bs, rr, h)
                    case False{}:
                      fz.err(st, "invalid key", b0, bs, rr, h)

# a quoted key's character
def fz.kq.char(
  +bad: Bool,
  +st: T.St,
  +cc: Char,
  +stay: T.Lex,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.kq.char.go(bad, st, cc, stay), b0, bs, rr):
  match bad:
    case True{}:
      fz.err(st, "invalid control", b0, bs, rr, h)
    case False{}:
      match st:
        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
          h

# a quoted key
def fz.kq.go(
  +quote: Bool,
  +bsl: Bool,
  +basic: Bool,
  +nl: Bool,
  +st: T.St,
  +cc: Char,
  +back: T.Lex,
  +stay: T.Lex,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.kq.go(quote, bsl, basic, nl, st, cc, back, stay), b0, bs, rr):
  match quote:
    case True{}:
      match st:
        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
          h
    case False{}:
      match bsl:
        case True{}:
          match basic:
            case True{}:
              match st:
                case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
                  h
            case False{}:
              match st:
                case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
                  h
        case False{}:
          match nl:
            case True{}:
              fz.err(st, "newline in key", b0, bs, rr, h)
            case False{}:
              fz.kq.char(T.str.bad(Char.to_u32(cc), False{}), st, cc, stay, b0, bs, rr, h)

# LKeyQ and LHeadQ
def fz.kq(
  +st: T.St,
  +cc: Char,
  +back: T.Lex,
  +stay: T.Lex,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.kq(st, cc, back, stay), b0, bs, rr):
  match st:
    case T.St{bd, rw, hs, he, pt, bf, lx, bk, +qk, sk, hd, un, lf, at, ld}:
      fz.kq.go(Char.is_eq(cc, T.q.char(qk)), Char.is_eq(cc, '\\'), T.q.basic(qk), T.ch.nl(cc), T.St{bd, rw,
        hs, he, pt, bf, lx, bk, qk, sk, hd, un, lf, at, ld}, cc, back, stay, b0, bs, rr, h)

# a line-ending backslash
def fz.fold.use(
  +back: T.Lex,
  +st: T.St,
  +saw: Bool,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.esc.fold.use(back, st, saw), b0, bs, rr):
  match back:
    case T.LTop{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)
    case T.LLine{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)
    case T.LKey{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)
    case T.LKeyDot{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)
    case T.LAfter{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)
    case T.LKeyQ{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)
    case T.LKeyE{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)
    case T.LKeyU{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)
    case T.LVal{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)
    case T.LQ{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)
    case T.LQ2{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)
    case T.LStr{}:
      match st:
        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, qk, _sk, _hd, _un, _lf, _at, _ld}:
          match qk:
            case T.QMulti{}:
              h
            case T.QMultiLit{}:
              h
            case T.QBasic{}:
              fz.err(st, "invalid escape", b0, bs, rr, h)
            case T.QLit{}:
              fz.err(st, "invalid escape", b0, bs, rr, h)
    case T.LEsc{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)
    case T.LUni{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)
    case T.LFold{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)
    case T.LMq{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)
    case T.LMqEnd{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)
    case T.LTrim{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)
    case T.LTrim2{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)
    case T.LBare{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)
    case T.LDate{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)
    case T.LCom{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)
    case T.LHead{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)
    case T.LHeadGap{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)
    case T.LHeadDot{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)
    case T.LHeadQ{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)
    case T.LHeadE{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)
    case T.LHeadU{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)
    case T.LHeadR{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)
    case T.LArr{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)
    case T.LArrC{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)
    case T.LInl{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)
    case T.LInlK{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)
    case T.LInlC{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)
    case T.LSink{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)

# an escape used
def fz.esc(
  +ee: T.Esc,
  +st: T.St,
  +back: T.Lex,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.esc.use(ee, st, back), b0, bs, rr):
  match ee:
    case T.EChar{_c}:
      match st:
        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
          h
    case T.EUni{_n}:
      match st:
        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
          h
    case T.EFold{saw}:
      fz.fold.use(back, st, saw, b0, bs, rr, h)
    case T.EBad{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)

# an escape's last digit
def fz.ufin(
  +ok: Bool,
  +st: T.St,
  +uu: U32,
  +back: T.Lex,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.uni.finish(ok, st, uu, back), b0, bs, rr):
  match ok:
    case True{}:
      match st:
        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
          h
    case False{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)

# an escape's digit
def fz.unext(
  +last: Bool,
  +st: T.St,
  +uu: U32,
  +back: T.Lex,
  +left: U32,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.uni.next(last, st, uu, back, left), b0, bs, rr):
  match last:
    case True{}:
      fz.ufin(T.uni.ok(uu), st, uu, back, b0, bs, rr, h)
    case False{}:
      match st:
        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
          h

# an escape's digit
def fz.ugo(
  +ok: Bool,
  +st: T.St,
  +cc: Char,
  +back: T.Lex,
  +uni: U32,
  +left: U32,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.uni.go(ok, st, cc, back, uni, left), b0, bs, rr):
  match ok:
    case True{}:
      fz.unext(U32.is_eq(left, 1), st, U32.add(U32.mul(uni, 16), T.dig.val(cc)), back, left, b0, bs, rr, h)
    case False{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)

# LKeyU, LUni and LHeadU
def fz.uni(
  +st: T.St,
  +cc: Char,
  +back: T.Lex,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.uni.step(st, cc, back), b0, bs, rr):
  match st:
    case T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, hd, +un, +lf, at, ld}:
      fz.ugo(T.dig.ok(T.dig.val(cc), 16), T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, hd, un, lf, at, ld}, cc,
        back, un, lf, b0, bs, rr, h)

# a newline before a value
def fz.vnl3(
  +inside: Bool,
  +st: T.St,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.val.nl3(inside, st), b0, bs, rr):
  match inside:
    case True{}:
      fz.err(st, "newline in inline table", b0, bs, rr, h)
    case False{}:
      fz.err(st, "newline before value", b0, bs, rr, h)

# a newline before a value
def fz.vnl2(
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.val.nl2(st, cc), b0, bs, rr):
  match st:
    case T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, +sk, hd, un, lf, at, ld}:
      fz.vnl3(T.inl.open(sk), T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, hd, un, lf, at, ld}, b0, bs, rr, h)

# LVal
def fz.x.val(
  +sp: Bool,
  +nl: Bool,
  +hash: Bool,
  +qq: Bool,
  +lit: Bool,
  +br: Bool,
  +inl: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.val.go(sp, nl, hash, qq, lit, br, inl, st, cc), b0, bs, rr):
  match sp:
    case True{}:
      h
    case False{}:
      match nl:
        case True{}:
          fz.vnl2(st, cc, b0, bs, rr, h)
        case False{}:
          match hash:
            case True{}:
              match st:
                case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
                  h
            case False{}:
              match qq:
                case True{}:
                  match st:
                    case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
                      h
                case False{}:
                  match lit:
                    case True{}:
                      match st:
                        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
                          h
                    case False{}:
                      match br:
                        case True{}:
                          match st:
                            case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
                              h
                        case False{}:
                          match inl:
                            case True{}:
                              match st:
                                case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
                                  h
                            case False{}:
                              match st:
                                case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
                                  h

# LQ
def fz.x.qgo(
  +same: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.q.go(same, st, cc), b0, bs, rr):
  match same:
    case True{}:
      match st:
        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
          h
    case False{}:
      match st:
        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
          h

# LQ
def fz.x.q(
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.q(st, cc), b0, bs, rr):
  match st:
    case T.St{bd, rw, hs, he, pt, bf, lx, bk, +qk, sk, hd, un, lf, at, ld}:
      fz.x.qgo(Char.is_eq(cc, T.q.char(qk)), T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, hd, un, lf, at, ld},
        cc, b0, bs, rr, h)

# LQ2
def fz.x.q2go(
  +same: Bool,
  +st: T.St,
  +cc: Char,
  +kind: T.QKind,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.q2.go(same, st, cc, kind), b0, bs, rr):
  match same:
    case True{}:
      match st:
        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
          h
    case False{}:
      fz.bhold(True{}, T.val.take(st, T.VStr{""}), cc, b0, bs, rr, fz.take(st, T.VStr{""}, b0, bs, rr, h))

# LQ2
def fz.x.q2(
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.q2(st, cc), b0, bs, rr):
  match st:
    case T.St{bd, rw, hs, he, pt, bf, lx, bk, +qk, sk, hd, un, lf, at, ld}:
      fz.x.q2go(Char.is_eq(cc, T.q.char(qk)), T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, hd, un, lf, at,
        ld}, cc, qk, b0, bs, rr, h)

# a string's character
def fz.x.strch(
  +bad: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.str.char.go(bad, st, cc), b0, bs, rr):
  match bad:
    case True{}:
      fz.err(st, "invalid control", b0, bs, rr, h)
    case False{}:
      match st:
        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
          h

# a backslash in a basic string
def fz.x.strbs(
  +bsl: Bool,
  +multi: Bool,
  +st: T.St,
  +cc: Char,
  +kind: T.QKind,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.str.bs(bsl, multi, st, cc, kind), b0, bs, rr):
  match bsl:
    case True{}:
      match st:
        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
          h
    case False{}:
      fz.x.strch(T.str.bad(Char.to_u32(cc), multi), st, cc, b0, bs, rr, h)

# LStr
def fz.x.strgo(
  +quote: Bool,
  +multi: Bool,
  +basic: Bool,
  +st: T.St,
  +cc: Char,
  +kind: T.QKind,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.str.go(quote, multi, basic, st, cc, kind), b0, bs, rr):
  match quote:
    case True{}:
      match multi:
        case True{}:
          match st:
            case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
              h
        case False{}:
          fz.sfin(st, b0, bs, rr, h)
    case False{}:
      match basic:
        case True{}:
          fz.x.strbs(Char.is_eq(cc, '\\'), multi, st, cc, kind, b0, bs, rr, h)
        case False{}:
          fz.x.strch(T.str.bad(Char.to_u32(cc), multi), st, cc, b0, bs, rr, h)

# LStr
def fz.x.str(
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.str(st, cc), b0, bs, rr):
  match st:
    case T.St{bd, rw, hs, he, pt, bf, lx, bk, +qk, sk, hd, un, lf, at, ld}:
      fz.x.strgo(Char.is_eq(cc, T.q.char(qk)), T.q.multi(qk), T.q.basic(qk), T.St{bd, rw, hs, he, pt, bf, lx,
        bk, qk, sk, hd, un, lf, at, ld}, cc, qk, b0, bs, rr, h)

# LFold
def fz.x.fend(
  +saw: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.fold.end.go(saw, st, cc), b0, bs, rr):
  match saw:
    case True{}:
      match st:
        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
          h
    case False{}:
      fz.err(st, "invalid escape", b0, bs, rr, h)

# LFold
def fz.x.fold(
  +sp: Bool,
  +nl: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.fold.go(sp, nl, st, cc), b0, bs, rr):
  match sp:
    case True{}:
      h
    case False{}:
      match nl:
        case True{}:
          match st:
            case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
              h
        case False{}:
          match st:
            case T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, hd, un, +lf, at, ld}:
              fz.x.fend(U32.is_eq(lf, 1), T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, hd, un, lf, at, ld}, cc, b0,
                bs, rr, h)

# LMq
def fz.x.mqgo(
  +quote: Bool,
  +one: Bool,
  +st: T.St,
  +cc: Char,
  +buf: List<&2, Char>,
  +kind: T.QKind,
  +left: U32,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.mq.go(quote, one, st, cc, buf, kind, left), b0, bs, rr):
  match quote:
    case True{}:
      match one:
        case True{}:
          match st:
            case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
              h
        case False{}:
          match st:
            case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
              h
    case False{}:
      match st:
        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
          h

# LMq
def fz.x.mq(
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.mq.step(st, cc), b0, bs, rr):
  match st:
    case T.St{bd, rw, hs, he, pt, +bf, lx, bk, +qk, sk, hd, un, +lf, at, ld}:
      fz.x.mqgo(Char.is_eq(cc, T.q.char(qk)), U32.is_eq(lf, 1), T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, hd,
        un, lf, at, ld}, cc, bf, qk, lf, b0, bs, rr, h)

# LMqEnd
def fz.x.mqe(
  +quote: Bool,
  +room: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.mq.end.go(quote, room, st, cc), b0, bs, rr):
  match quote:
    case True{}:
      match room:
        case True{}:
          match st:
            case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
              h
        case False{}:
          fz.bhold(True{}, T.str.fin(st), cc, b0, bs, rr, fz.sfin(st, b0, bs, rr, h))
    case False{}:
      fz.bhold(True{}, T.str.fin(st), cc, b0, bs, rr, fz.sfin(st, b0, bs, rr, h))

# LMqEnd
def fz.x.mqend(
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.mq.end(st, cc), b0, bs, rr):
  match st:
    case T.St{bd, rw, hs, he, pt, bf, lx, bk, +qk, sk, hd, un, +lf, at, ld}:
      fz.x.mqe(Char.is_eq(cc, T.q.char(qk)), U32.is_lt(lf, 2), T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, hd,
        un, lf, at, ld}, cc, b0, bs, rr, h)

# LTrim
def fz.x.trim(
  +cr: Bool,
  +nl: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.trim.go(cr, nl, st, cc), b0, bs, rr):
  match cr:
    case True{}:
      match st:
        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
          h
    case False{}:
      match nl:
        case True{}:
          match st:
            case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
              h
        case False{}:
          match st:
            case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
              h

# LTrim2
def fz.x.trim2(
  +lf: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.trim2.go(lf, st, cc), b0, bs, rr):
  match lf:
    case True{}:
      match st:
        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
          h
    case False{}:
      match st:
        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
          h

# a bare word's space
def fz.x.bdate(
  +date: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.bare.date.go(date, st, cc), b0, bs, rr):
  match date:
    case True{}:
      match st:
        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
          h
    case False{}:
      fz.finish(st, cc, False{}, b0, bs, rr, h)

# LBare
def fz.x.bare(
  +delim: Bool,
  +sp: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.bare.go(delim, sp, st, cc), b0, bs, rr):
  match delim:
    case True{}:
      match sp:
        case True{}:
          match st:
            case T.St{bd, rw, hs, he, pt, +bf, lx, bk, qk, sk, hd, un, lf, at, ld}:
              fz.x.bdate(T.date.shaped(bf), T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, hd, un, lf, at, ld}, cc, b0,
                bs, rr, h)
        case False{}:
          match st:
            case T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, +sk, hd, un, lf, at, ld}:
              fz.finish(T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, hd, un, lf, at, ld}, cc,
                T.lex.bare.hold(T.ch.skip(cc),
                T.ch.nl(cc), T.inl.open(sk)), b0, bs, rr, h)
    case False{}:
      match st:
        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
          h

# LDate
def fz.x.date(
  +digit: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.date.go(digit, st, cc), b0, bs, rr):
  match digit:
    case True{}:
      match st:
        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
          h
    case False{}:
      fz.finish(st, cc, True{}, b0, bs, rr, h)

# LCom
def fz.x.com(
  +nl: Bool,
  +ctl: Bool,
  +tab: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.com.go(nl, ctl, tab, st, cc), b0, bs, rr):
  match nl:
    case True{}:
      match st:
        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
          h
    case False{}:
      match ctl:
        case True{}:
          match tab:
            case True{}:
              h
            case False{}:
              fz.err(st, "invalid control in comment", b0, bs, rr, h)
        case False{}:
          h

# a second bracket
def fz.x.hbrgo(
  +fresh: Bool,
  +once: Bool,
  +st: T.St,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.head.br.go(fresh, once, st), b0, bs, rr):
  match fresh:
    case True{}:
      match once:
        case True{}:
          match st:
            case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
              h
        case False{}:
          fz.err(st, "invalid header", b0, bs, rr, h)
    case False{}:
      fz.err(st, "invalid header", b0, bs, rr, h)

# a second bracket
def fz.x.hbr(
  +st: T.St,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.head.br(st), b0, bs, rr):
  match st:
    case T.St{bd, rw, hs, he, +pt, +bf, lx, bk, qk, sk, hd, un, lf, +at, ld}:
      fz.x.hbrgo(Bool.and(List.is_empty(&2, String, pt), List.is_empty(&2, Char, bf)), Bool.not(at), T.St{bd, rw,
        hs, he, pt, bf, lx, bk, qk, sk, hd, un, lf, at, ld}, b0, bs, rr, h)

# a header's bare character
def fz.x.hchgo(
  +gap: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.head.ch.go(gap, st, cc), b0, bs, rr):
  match gap:
    case True{}:
      fz.err(st, "invalid header", b0, bs, rr, h)
    case False{}:
      match st:
        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
          h

# a header's bare character
def fz.x.hch(
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.head.ch(st, cc), b0, bs, rr):
  match st:
    case T.St{bd, rw, hs, he, +pt, +bf, lx, bk, qk, sk, hd, un, lf, at, ld}:
      fz.x.hchgo(Bool.and(Bool.not(List.is_empty(&2, String, pt)), List.is_empty(&2, Char, bf)), T.St{bd, rw, hs,
        he, pt, bf, lx, bk, qk, sk, hd, un, lf, at, ld}, cc, b0, bs, rr, h)

# blank space in a header
def fz.x.hgapgo(
  +empty: Bool,
  +st: T.St,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.head.gap.go(empty, st), b0, bs, rr):
  match empty:
    case True{}:
      match st:
        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
          h
    case False{}:
      match st:
        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
          h

# blank space in a header
def fz.x.hgap0(
  +st: T.St,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.head.gap(st), b0, bs, rr):
  match st:
    case T.St{bd, rw, hs, he, pt, +bf, lx, bk, qk, sk, hd, un, lf, at, ld}:
      fz.x.hgapgo(List.is_empty(&2, Char, bf), T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, hd, un, lf, at, ld},
        b0, bs, rr, h)

# a dot in a header
def fz.x.hdot3(
  +empty: Bool,
  +st: T.St,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.head.dot3(empty, st), b0, bs, rr):
  match empty:
    case True{}:
      fz.err(st, "empty key", b0, bs, rr, h)
    case False{}:
      match st:
        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
          h

# a dot in a header
def fz.x.hdot2(
  +st: T.St,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.head.dot2(st), b0, bs, rr):
  match st:
    case T.St{bd, rw, hs, he, pt, +bf, lx, bk, qk, sk, hd, un, lf, at, ld}:
      fz.x.hdot3(List.is_empty(&2, Char, bf), T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, hd, un, lf, at, ld},
        b0, bs, rr, h)

# a closing bracket
def fz.x.hclose2(
  +arr: Bool,
  +st: T.St,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.head.close2(arr, st), b0, bs, rr):
  match arr:
    case True{}:
      match st:
        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
          h
    case False{}:
      fz.hfin(st, b0, bs, rr, h)

# a closing bracket
def fz.x.hclosego(
  +empty: Bool,
  +arr: Bool,
  +st: T.St,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.head.close.go(empty, arr, st), b0, bs, rr):
  match empty:
    case True{}:
      fz.x.hclose2(arr, st, b0, bs, rr, h)
    case False{}:
      fz.x.hclose2(arr, T.seg.push(st, T.LHead{}), b0, bs, rr, fz.segp(st, T.LHead{}, b0, bs, rr, h))

# a closing bracket
def fz.x.hclose(
  +st: T.St,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.head.close(st), b0, bs, rr):
  match st:
    case T.St{bd, rw, hs, he, pt, +bf, lx, bk, qk, sk, hd, un, lf, +at, ld}:
      fz.x.hclosego(List.is_empty(&2, Char, bf), at, T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, hd, un, lf, at,
        ld}, b0, bs, rr, h)

# a comment in a header
def fz.x.hhash(
  +hash: Bool,
  +st: T.St,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.head.hash(hash, st), b0, bs, rr):
  match hash:
    case True{}:
      match st:
        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
          h
    case False{}:
      fz.err(st, "invalid header", b0, bs, rr, h)

# a quoted header segment
def fz.x.hqgo(
  +fresh: Bool,
  +st: T.St,
  +kind: T.QKind,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.head.quote.go(fresh, st, kind), b0, bs, rr):
  match fresh:
    case True{}:
      match st:
        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
          h
    case False{}:
      fz.err(st, "invalid header", b0, bs, rr, h)

# a quoted header segment
def fz.x.hquote(
  +st: T.St,
  +kind: T.QKind,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.head.quote(st, kind), b0, bs, rr):
  match st:
    case T.St{bd, rw, hs, he, +pt, +bf, lx, bk, qk, sk, hd, un, lf, at, ld}:
      fz.x.hqgo(Bool.and(List.is_empty(&2, Char, bf), List.is_empty(&2, String, pt)), T.St{bd, rw, hs, he, pt,
        bf, lx, bk, qk, sk, hd, un, lf, at, ld}, kind, b0, bs, rr, h)

# LHead
def fz.x.head(
  +br: Bool,
  +bare: Bool,
  +sp: Bool,
  +dot: Bool,
  +end: Bool,
  +qq: Bool,
  +lit: Bool,
  +hash: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.head.go(br, bare, sp, dot, end, qq, lit, hash, st, cc), b0, bs, rr):
  match br:
    case True{}:
      fz.x.hbr(st, b0, bs, rr, h)
    case False{}:
      match bare:
        case True{}:
          fz.x.hch(st, cc, b0, bs, rr, h)
        case False{}:
          match sp:
            case True{}:
              fz.x.hgap0(st, b0, bs, rr, h)
            case False{}:
              match dot:
                case True{}:
                  fz.x.hdot2(st, b0, bs, rr, h)
                case False{}:
                  match end:
                    case True{}:
                      fz.x.hclose(st, b0, bs, rr, h)
                    case False{}:
                      match qq:
                        case True{}:
                          fz.x.hquote(st, T.QBasic{}, b0, bs, rr, h)
                        case False{}:
                          match lit:
                            case True{}:
                              fz.x.hquote(st, T.QLit{}, b0, bs, rr, h)
                            case False{}:
                              fz.x.hhash(hash, st, b0, bs, rr, h)

# LHeadGap
def fz.x.hg(
  +sp: Bool,
  +dot: Bool,
  +end: Bool,
  +hash: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.hgap(sp, dot, end, hash, st, cc), b0, bs, rr):
  match sp:
    case True{}:
      h
    case False{}:
      match dot:
        case True{}:
          match st:
            case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
              h
        case False{}:
          match end:
            case True{}:
              fz.x.hclose(st, b0, bs, rr, h)
            case False{}:
              fz.x.hhash(hash, st, b0, bs, rr, h)

# LHeadDot
def fz.x.hd(
  +sp: Bool,
  +bare: Bool,
  +qq: Bool,
  +lit: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.hdot(sp, bare, qq, lit, st, cc), b0, bs, rr):
  match sp:
    case True{}:
      h
    case False{}:
      match bare:
        case True{}:
          match st:
            case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
              h
        case False{}:
          match qq:
            case True{}:
              match st:
                case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
                  h
            case False{}:
              match lit:
                case True{}:
                  match st:
                    case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
                      h
                case False{}:
                  fz.err(st, "invalid header", b0, bs, rr, h)

# LHeadR
def fz.x.hr(
  +end: Bool,
  +st: T.St,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.head.r.go(end, st), b0, bs, rr):
  match end:
    case True{}:
      fz.hfin(st, b0, bs, rr, h)
    case False{}:
      fz.err(st, "invalid header", b0, bs, rr, h)

# LArr
def fz.x.arr(
  +sp: Bool,
  +nl: Bool,
  +hash: Bool,
  +end: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.arr.go(sp, nl, hash, end, st, cc), b0, bs, rr):
  match sp:
    case True{}:
      h
    case False{}:
      match nl:
        case True{}:
          h
        case False{}:
          match hash:
            case True{}:
              match st:
                case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
                  h
            case False{}:
              match end:
                case True{}:
                  fz.aclose(st, b0, bs, rr, h)
                case False{}:
                  match st:
                    case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
                      h

# LArrC
def fz.x.arrc(
  +sp: Bool,
  +nl: Bool,
  +hash: Bool,
  +comma: Bool,
  +end: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.arrc.go(sp, nl, hash, comma, end, st, cc), b0, bs, rr):
  match sp:
    case True{}:
      h
    case False{}:
      match nl:
        case True{}:
          h
        case False{}:
          match hash:
            case True{}:
              match st:
                case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
                  h
            case False{}:
              match comma:
                case True{}:
                  match st:
                    case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
                      h
                case False{}:
                  match end:
                    case True{}:
                      fz.aclose(st, b0, bs, rr, h)
                    case False{}:
                      fz.err(st, "invalid array", b0, bs, rr, h)

# a key in an inline table
def fz.x.kbare(
  +ok: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.key.bare(ok, st, cc), b0, bs, rr):
  match ok:
    case True{}:
      match st:
        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
          h
    case False{}:
      fz.err(st, "invalid key", b0, bs, rr, h)

# a key in an inline table
def fz.x.klit(
  +lit: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.key.lit(lit, st, cc), b0, bs, rr):
  match lit:
    case True{}:
      match st:
        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
          h
    case False{}:
      fz.x.kbare(T.bare.at(cc), st, cc, b0, bs, rr, h)

# a key in an inline table
def fz.x.kq0(
  +qq: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.key.q(qq, st, cc), b0, bs, rr):
  match qq:
    case True{}:
      match st:
        case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
          h
    case False{}:
      fz.x.klit(Char.is_eq(cc, '\''), st, cc, b0, bs, rr, h)

# a key in an inline table
def fz.x.kclear(
  +st: T.St,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.key.clear(st), b0, bs, rr):
  match st:
    case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
      h

# a key in an inline table
def fz.x.inlnl(
  +nl: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.inl.nl(nl, st, cc), b0, bs, rr):
  match nl:
    case True{}:
      fz.err(st, "newline in inline table", b0, bs, rr, h)
    case False{}:
      fz.x.kq0(Char.is_eq(cc, '"'), T.lex.key.clear(st), cc, b0, bs, rr, fz.x.kclear(st, b0, bs, rr, h))

# LInl
def fz.x.inl(
  +sp: Bool,
  +hash: Bool,
  +end: Bool,
  +nl: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.inl.go(sp, hash, end, nl, st, cc), b0, bs, rr):
  match sp:
    case True{}:
      h
    case False{}:
      match hash:
        case True{}:
          match st:
            case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
              h
        case False{}:
          match end:
            case True{}:
              fz.iclose(st, b0, bs, rr, h)
            case False{}:
              fz.x.inlnl(nl, st, cc, b0, bs, rr, h)

# LInlK
def fz.x.inlk(
  +sp: Bool,
  +hash: Bool,
  +nl: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.inlk.go(sp, hash, nl, st, cc), b0, bs, rr):
  match sp:
    case True{}:
      h
    case False{}:
      match hash:
        case True{}:
          match st:
            case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
              h
        case False{}:
          fz.x.inlnl(nl, st, cc, b0, bs, rr, h)

# LInlC
def fz.x.inlc(
  +sp: Bool,
  +hash: Bool,
  +comma: Bool,
  +end: Bool,
  +nl: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.lex.inlc.go(sp, hash, comma, end, nl, st, cc), b0, bs, rr):
  match sp:
    case True{}:
      h
    case False{}:
      match hash:
        case True{}:
          match st:
            case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
              h
        case False{}:
          match comma:
            case True{}:
              match st:
                case T.St{_bd, _rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
                  h
            case False{}:
              match end:
                case True{}:
                  fz.iclose(st, b0, bs, rr, h)
                case False{}:
                  match nl:
                    case True{}:
                      fz.err(st, "newline in inline table", b0, bs, rr, h)
                    case False{}:
                      fz.err(st, "invalid inline table", b0, bs, rr, h)

# one character in every lex state
def fz.on(
  +lex: T.Lex,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.read.on(lex, st, cc), b0, bs, rr):
  match lex:
    case T.LTop{}:
      fz.x.top(T.ch.sp(cc), T.ch.nl(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, '['), Char.is_eq(cc, '"'),
        Char.is_eq(cc, '\''), T.bare.at(cc), st, cc, b0, bs, rr, h)
    case T.LLine{}:
      fz.x.line(T.ch.sp(cc), Char.is_eq(cc, '#'), T.ch.nl(cc), st, cc, b0, bs, rr, h)
    case T.LKey{}:
      fz.x.key(T.bare.at(cc), T.ch.sp(cc), Char.is_eq(cc, '.'), Char.is_eq(cc, '='), Char.is_eq(cc, '#'),
        T.ch.nl(cc), st, cc, b0, bs, rr, h)
    case T.LKeyDot{}:
      fz.x.kdot(T.ch.sp(cc), Char.is_eq(cc, '"'), Char.is_eq(cc, '\''), Char.is_eq(cc, '.'), T.ch.nl(cc),
        st, cc, b0, bs, rr, h)
    case T.LAfter{}:
      fz.x.after(T.ch.sp(cc), Char.is_eq(cc, '.'), Char.is_eq(cc, '='), Char.is_eq(cc, '#'), T.ch.nl(cc), st,
        cc, b0, bs, rr, h)
    case T.LKeyQ{}:
      fz.kq(st, cc, T.LAfter{}, T.LKeyQ{}, b0, bs, rr, h)
    case T.LKeyE{}:
      fz.esc(T.esc.of(cc), st, T.LKeyQ{}, b0, bs, rr, h)
    case T.LKeyU{}:
      fz.uni(st, cc, T.LKeyQ{}, b0, bs, rr, h)
    case T.LVal{}:
      fz.x.val(T.ch.sp(cc), T.ch.nl(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, '"'), Char.is_eq(cc, '\''),
        Char.is_eq(cc, '['), Char.is_eq(cc, '{'), st, cc, b0, bs, rr, h)
    case T.LQ{}:
      fz.x.q(st, cc, b0, bs, rr, h)
    case T.LQ2{}:
      fz.x.q2(st, cc, b0, bs, rr, h)
    case T.LStr{}:
      fz.x.str(st, cc, b0, bs, rr, h)
    case T.LEsc{}:
      fz.esc(T.esc.of(cc), st, T.LStr{}, b0, bs, rr, h)
    case T.LUni{}:
      fz.uni(st, cc, T.LStr{}, b0, bs, rr, h)
    case T.LFold{}:
      fz.x.fold(T.ch.sp(cc), T.ch.nl(cc), st, cc, b0, bs, rr, h)
    case T.LMq{}:
      fz.x.mq(st, cc, b0, bs, rr, h)
    case T.LMqEnd{}:
      fz.x.mqend(st, cc, b0, bs, rr, h)
    case T.LTrim{}:
      fz.x.trim(U32.is_eq(Char.to_u32(cc), 13), T.ch.nl(cc), st, cc, b0, bs, rr, h)
    case T.LTrim2{}:
      fz.x.trim2(U32.is_eq(Char.to_u32(cc), 10), st, cc, b0, bs, rr, h)
    case T.LBare{}:
      fz.x.bare(T.ch.delim(cc), T.ch.space(cc), st, cc, b0, bs, rr, h)
    case T.LDate{}:
      fz.x.date(Char.is_digit(cc), st, cc, b0, bs, rr, h)
    case T.LCom{}:
      fz.x.com(T.ch.nl(cc), T.ch.ctl(cc), U32.is_eq(Char.to_u32(cc), 9), st, cc, b0, bs, rr, h)
    case T.LHead{}:
      fz.x.head(Char.is_eq(cc, '['), T.bare.at(cc), T.ch.sp(cc), Char.is_eq(cc, '.'), Char.is_eq(cc, ']'),
        Char.is_eq(cc, '"'), Char.is_eq(cc, '\''), Char.is_eq(cc, '#'), st, cc, b0, bs, rr, h)
    case T.LHeadGap{}:
      fz.x.hg(T.ch.sp(cc), Char.is_eq(cc, '.'), Char.is_eq(cc, ']'), Char.is_eq(cc, '#'), st, cc, b0, bs, rr,
        h)
    case T.LHeadDot{}:
      fz.x.hd(T.ch.sp(cc), T.bare.at(cc), Char.is_eq(cc, '"'), Char.is_eq(cc, '\''), st, cc, b0, bs, rr,
        h)
    case T.LHeadQ{}:
      fz.kq(st, cc, T.LHeadGap{}, T.LHeadQ{}, b0, bs, rr, h)
    case T.LHeadE{}:
      fz.esc(T.esc.of(cc), st, T.LHeadQ{}, b0, bs, rr, h)
    case T.LHeadU{}:
      fz.uni(st, cc, T.LHeadQ{}, b0, bs, rr, h)
    case T.LHeadR{}:
      fz.x.hr(Char.is_eq(cc, ']'), st, b0, bs, rr, h)
    case T.LArr{}:
      fz.x.arr(T.ch.sp(cc), T.ch.nl(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, ']'), st, cc, b0, bs, rr, h)
    case T.LArrC{}:
      fz.x.arrc(T.ch.sp(cc), T.ch.nl(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, ','), Char.is_eq(cc, ']'), st,
        cc, b0, bs, rr, h)
    case T.LInl{}:
      fz.x.inl(T.ch.sp(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, '}'), T.ch.nl(cc), st, cc, b0, bs, rr, h)
    case T.LInlK{}:
      fz.x.inlk(T.ch.sp(cc), Char.is_eq(cc, '#'), T.ch.nl(cc), st, cc, b0, bs, rr, h)
    case T.LInlC{}:
      fz.x.inlc(T.ch.sp(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, ','), Char.is_eq(cc, '}'), T.ch.nl(cc), st,
        cc, b0, bs, rr, h)
    case T.LSink{}:
      h

# the full step
def fz.onst(
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.read.on.st(st, cc), b0, bs, rr):
  match st:
    case T.St{bd, rw, hs, he, pt, bf, +lx, bk, qk, sk, hd, un, lf, at, ld}:
      fz.on(lx, T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, hd, un, lf, at, ld}, cc, b0, bs, rr, h)

# a byte-order mark
def fz.sbom(
  +bom: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.read.step.bom(bom, st, cc), b0, bs, rr):
  match bom:
    case True{}:
      h
    case False{}:
      fz.onst(st, cc, b0, bs, rr, h)

# the first character
def fz.slead(
  +lead: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.read.step.lead(lead, st, cc), b0, bs, rr):
  match lead:
    case True{}:
      fz.sbom(U32.is_eq(Char.to_u32(cc), 65279), st, cc, b0, bs, rr, h)
    case False{}:
      fz.onst(st, cc, b0, bs, rr, h)

# one character of the document
def fz.step(
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.read.step(st, cc), b0, bs, rr):
  match st:
    case T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, hd, un, lf, at, ld}:
      fz.slead(ld, T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, hd, un, lf, at, False{}}, cc, b0, bs, rr, h)

# a held character
def fz.ohold(
  +hold: T.Hold,
  +st: T.St,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.read.once.hold(hold, st), b0, bs, rr):
  match hold:
    case T.HNone{}:
      h
    case T.HChar{c}:
      fz.step(st, c, b0, bs, rr, h)

# a held character
def fz.once2(
  +st: T.St,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.read.once2(st), b0, bs, rr):
  match st:
    case T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, hd, un, lf, at, ld}:
      fz.ohold(hd, T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, T.HNone{}, un, lf, at, ld}, b0, bs, rr, h)

# the fast step, past a held character
def fz.flead(
  +lead: Bool,
  +lx: T.Lex,
  +qk: T.QKind,
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
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  +h: {FzP{bd, rw} == FzP{SCon{b0, bs}, rr} : FzP}
) -> {fz.p(T.read.fast.lead(lead, lx, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc)) == FzP{SCon{b0, bs},
  rr} : FzP}:
  match lead:
    case True{}:
      fz.once2(T.read.step(T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, T.HNone{}, un, lf, at, True{}}, cc), b0, bs, rr,
        fz.step(T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, T.HNone{}, un, lf, at, True{}}, cc, b0, bs, rr, h))
    case False{}:
      %Equal.sym(T.St, T.read.fast.lex(lx, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc), T.read.fast.old(bd, rw,
        hs, he, pt, bf, lx, bk, qk, sk, un, lf, at, cc), sr.ff(lx, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc))
        : {fz.p(_) == FzP{SCon{b0, bs}, rr} : FzP}
      fz.once2(T.read.on.st(T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, T.HNone{}, un, lf, at, False{}}, cc), b0, bs,
        rr,
        fz.onst(T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, T.HNone{}, un, lf, at, False{}}, cc, b0, bs, rr, h))

# the fast step
def fz.fhold(
  +hold: T.Hold,
  +lead: Bool,
  +lx: T.Lex,
  +qk: T.QKind,
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
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  +h: {FzP{bd, rw} == FzP{SCon{b0, bs}, rr} : FzP}
) -> {fz.p(T.read.fast.hold(hold, lead, lx, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc)) == FzP{SCon{b0, bs},
  rr} : FzP}:
  match hold:
    case T.HChar{held}:
      fz.once2(T.read.step(T.read.once2(T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, T.HChar{held}, un, lf, at, lead}),
        cc), b0, bs, rr, fz.step(T.read.once2(T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, T.HChar{held}, un, lf, at,
        lead}), cc, b0, bs, rr, fz.once2(T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, T.HChar{held}, un, lf, at, lead},
        b0, bs, rr, h)))
    case T.HNone{}:
      fz.flead(lead, lx, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc, b0, bs, rr, h)

# the fast step
def fz.fast(
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.read.fast(st, cc), b0, bs, rr):
  match st:
    case T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, hd, un, lf, at, ld}:
      fz.fhold(hd, ld, lx, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc, b0, bs, rr, h)

# the error and the rows of a mode
def fz.m(md: T.Mode) -> FzP:
  match md:
    case T.MScan{st}:
      fz.p(st)
    case T.MCr{st}:
      fz.p(st)
    case T.MOpen{_b, _q, _k, bd, rw, _hs, _he, _pt, _bf, _bk, _sk, _un, _lf, _at}:
      FzP{bd, rw}
    case T.MEat{_b, _q, _c, _n, bd, rw, _hs, _he, _pt, _k, _sk, _un, _lf, _at}:
      FzP{bd, rw}

# a mode that holds the error SCon{b0, bs} and the rows rr
def fz.M(md: T.Mode, b0: Char, bs: String, rr: List<&2, T.Val>) -> Data:
  {fz.m(md) == FzP{SCon{b0, bs}, rr} : FzP}

# the document with the error SCon{b0, bs} and the rows rr, sealed
def fz.D(dd: T.Doc, b0: Char, bs: String, rr: List<&2, T.Val>) -> Data:
  {dd == T.Doc{SCon{b0, bs}, T.rows.seal(rr)} : T.Doc}

# a quote's string kind
def fz.skind(
  +qk: T.QKind,
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
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  +h: {FzP{bd, rw} == FzP{SCon{b0, bs}, rr} : FzP}
) -> fz.M(T.doc.scan.kind(qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at), b0, bs, rr):
  match qk:
    case T.QBasic{}:
      h
    case T.QLit{}:
      h
    case T.QMulti{}:
      h
    case T.QMultiLit{}:
      h

# a quote at the first character
def fz.slead2(
  +lead: Bool,
  +qk: T.QKind,
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
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  +h: {FzP{bd, rw} == FzP{SCon{b0, bs}, rr} : FzP}
) -> fz.M(T.doc.scan.lead(lead, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at), b0, bs, rr):
  match lead:
    case True{}:
      h
    case False{}:
      fz.skind(qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, b0, bs, rr, h)

# a quote with a held character
def fz.shold(
  +hold: T.Hold,
  +lead: Bool,
  +qk: T.QKind,
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
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  +h: {FzP{bd, rw} == FzP{SCon{b0, bs}, rr} : FzP}
) -> fz.M(T.doc.scan.hold(hold, lead, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at), b0, bs, rr):
  match hold:
    case T.HChar{_held}:
      h
    case T.HNone{}:
      fz.slead2(lead, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, b0, bs, rr, h)

# a quote may open a span
def fz.wlex(
  +lex: T.Lex,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +bf: List<&2, Char>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +hd: T.Hold,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +ld: Bool,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  +h: {FzP{bd, rw} == FzP{SCon{b0, bs}, rr} : FzP}
) -> fz.M(T.doc.wrap.lex(lex, bd, rw, hs, he, pt, bf, bk, qk, sk, hd, un, lf, at, ld), b0, bs, rr):
  match lex:
    case T.LTop{}:
      h
    case T.LLine{}:
      h
    case T.LKey{}:
      h
    case T.LKeyDot{}:
      h
    case T.LAfter{}:
      h
    case T.LKeyQ{}:
      h
    case T.LKeyE{}:
      h
    case T.LKeyU{}:
      h
    case T.LVal{}:
      h
    case T.LQ{}:
      fz.shold(hd, ld, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, b0, bs, rr, h)
    case T.LQ2{}:
      h
    case T.LStr{}:
      h
    case T.LEsc{}:
      h
    case T.LUni{}:
      h
    case T.LFold{}:
      h
    case T.LMq{}:
      h
    case T.LMqEnd{}:
      h
    case T.LTrim{}:
      h
    case T.LTrim2{}:
      h
    case T.LBare{}:
      h
    case T.LDate{}:
      h
    case T.LCom{}:
      h
    case T.LHead{}:
      h
    case T.LHeadGap{}:
      h
    case T.LHeadDot{}:
      h
    case T.LHeadQ{}:
      h
    case T.LHeadE{}:
      h
    case T.LHeadU{}:
      h
    case T.LHeadR{}:
      h
    case T.LArr{}:
      h
    case T.LArrC{}:
      h
    case T.LInl{}:
      h
    case T.LInlK{}:
      h
    case T.LInlC{}:
      h
    case T.LSink{}:
      h

# a quote may open a span
def fz.wrap(
  +st: T.St,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.M(T.doc.wrap(st), b0, bs, rr):
  match st:
    case T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, hd, un, lf, at, ld}:
      fz.wlex(lx, bd, rw, hs, he, pt, bf, bk, qk, sk, hd, un, lf, at, ld, b0, bs, rr, h)

# a carriage return
def fz.scr(
  +cr: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.M(T.doc.scan.cr(cr, st, cc), b0, bs, rr):
  match cr:
    case True{}:
      fz.fast(st, cc, b0, bs, rr, h)
    case False{}:
      fz.fast(st, cc, b0, bs, rr, h)

# an apostrophe
def fz.ssq(
  +sq: Bool,
  +cr: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.M(T.doc.scan.sq(sq, cr, st, cc), b0, bs, rr):
  match sq:
    case True{}:
      fz.wrap(T.read.fast(st, cc), b0, bs, rr, fz.fast(st, cc, b0, bs, rr, h))
    case False{}:
      fz.scr(cr, st, cc, b0, bs, rr, h)

# a quotation mark
def fz.sdq(
  +dq: Bool,
  +sq: Bool,
  +cr: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.M(T.doc.scan.q(dq, sq, cr, st, cc), b0, bs, rr):
  match dq:
    case True{}:
      fz.wrap(T.read.fast(st, cc), b0, bs, rr, fz.fast(st, cc, b0, bs, rr, h))
    case False{}:
      fz.ssq(sq, cr, st, cc, b0, bs, rr, h)

# a character outside a span
def fz.scan(
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.M(T.doc.scan(st, cc), b0, bs, rr):
  fz.sdq(Char.is_eq(cc, '"'), Char.is_eq(cc, '\''), U32.is_eq(Char.to_u32(cc), 13), st, cc, b0, bs, rr, h)

# the character after a carriage return
def fz.cr(
  +lf: Bool,
  +st: T.St,
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.M(T.doc.cr(lf, st, cc), b0, bs, rr):
  match lf:
    case True{}:
      fz.fast(st, cc, b0, bs, rr, h)
    case False{}:
      fz.err(st, "carriage return without line feed", b0, bs, rr, h)

# the old step after an opening quote
def fz.lq(
  +qk: T.QKind,
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
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  +h: {FzP{bd, rw} == FzP{SCon{b0, bs}, rr} : FzP}
) -> {fz.p(T.read.fast.lex(T.LQ{}, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc)) == FzP{SCon{b0, bs}, rr} : FzP}:
  fz.once2(T.read.on.st(T.St{bd, rw, hs, he, pt, bf, T.LQ{}, bk, qk, sk, T.HNone{}, un, lf, at, False{}}, cc), b0, bs,
    rr, fz.onst(T.St{bd, rw, hs, he, pt, bf, T.LQ{}, bk, qk, sk, T.HNone{}, un, lf, at, False{}}, cc, b0, bs, rr, h))

# a span starts on an empty buffer
def fz.obuf(
  +basic: Bool,
  +qq: Char,
  +qk: T.QKind,
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
  +cc: Char,
  +tail: String,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  +h: {FzP{bd, rw} == FzP{SCon{b0, bs}, rr} : FzP}
) -> fz.M(T.doc.open.buf(basic, qq, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc, tail), b0, bs, rr):
  match bf:
    case []:
      h
    case hh <> tt:
      fz.lq(qk, bd, rw, hs, he, pt, hh <> tt, bk, sk, un, lf, at, cc, b0, bs, rr, h)

# a control after an opening quote
def fz.ook(
  +badc: Bool,
  +basic: Bool,
  +qq: Char,
  +qk: T.QKind,
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
  +cc: Char,
  +tail: String,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  +h: {FzP{bd, rw} == FzP{SCon{b0, bs}, rr} : FzP}
) -> fz.M(T.doc.open.ok(badc, basic, qq, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc, tail), b0, bs, rr):
  match badc:
    case True{}:
      fz.lq(qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc, b0, bs, rr, h)
    case False{}:
      fz.obuf(basic, qq, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc, tail, b0, bs, rr, h)

# a backslash after an opening quote
def fz.obs(
  +bsl: Bool,
  +qq: Char,
  +qk: T.QKind,
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
  +cc: Char,
  +tail: String,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  +h: {FzP{bd, rw} == FzP{SCon{b0, bs}, rr} : FzP}
) -> fz.M(T.doc.open.bs(bsl, qq, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc, tail), b0, bs, rr):
  match bsl:
    case True{}:
      fz.lq(qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc, b0, bs, rr, h)
    case False{}:
      fz.ook(T.str.bad(Char.to_u32(cc), False{}), True{}, qq, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc,
        tail, b0, bs, rr, h)

# the character after an opening quote
def fz.ob(
  +basic: Bool,
  +qq: Char,
  +qk: T.QKind,
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
  +cc: Char,
  +tail: String,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  +h: {FzP{bd, rw} == FzP{SCon{b0, bs}, rr} : FzP}
) -> fz.M(T.doc.open.b(basic, qq, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc, tail), b0, bs, rr):
  match basic:
    case False{}:
      fz.ook(T.str.bad(Char.to_u32(cc), False{}), False{}, qq, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc,
        tail, b0, bs, rr, h)
    case True{}:
      fz.obs(Char.is_eq(cc, '\\'), qq, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc, tail, b0, bs, rr, h)

# a second quote
def fz.oq(
  +same: Bool,
  +basic: Bool,
  +qq: Char,
  +qk: T.QKind,
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
  +cc: Char,
  +tail: String,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  +h: {FzP{bd, rw} == FzP{SCon{b0, bs}, rr} : FzP}
) -> fz.M(T.doc.open.q(same, basic, qq, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc, tail), b0, bs, rr):
  match same:
    case True{}:
      fz.lq(qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc, b0, bs, rr, h)
    case False{}:
      fz.ob(basic, qq, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc, tail, b0, bs, rr, h)

# the character after an opening quote
def fz.open(
  +basic: Bool,
  +qq: Char,
  +qk: T.QKind,
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
  +cc: Char,
  +tail: String,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  +h: {FzP{bd, rw} == FzP{SCon{b0, bs}, rr} : FzP}
) -> fz.M(T.doc.open(basic, qq, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc, tail), b0, bs, rr):
  fz.oq(Char.is_eq(cc, qq), basic, qq, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc, tail, b0, bs, rr, h)

# a span's character: copied at a control, kept otherwise
def fz.ectrl(
  +badc: Bool,
  +basic: Bool,
  +qq: Char,
  +cc: Char,
  +cut: String,
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
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  +h: {FzP{bd, rw} == FzP{SCon{b0, bs}, rr} : FzP}
) -> fz.M(T.eat.ctrl(badc, basic, qq, cc, cut, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at), b0, bs, rr):
  match badc:
    case True{}:
      fz.x.str(T.St{bd, rw, hs, he, pt, T.span.rev(cut, nn, U32.is_zero(nn), []), T.LStr{}, T.LStr{}, qk, sk,
        T.HNone{}, un, lf, at, False{}}, cc, b0, bs, rr, h)
    case False{}:
      h

# a backslash in a span
def fz.ebs(
  +bsl: Bool,
  +basic: Bool,
  +qq: Char,
  +cc: Char,
  +cut: String,
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
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  +h: {FzP{bd, rw} == FzP{SCon{b0, bs}, rr} : FzP}
) -> fz.M(T.eat.bs(bsl, basic, qq, cc, cut, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at), b0, bs, rr):
  match bsl:
    case True{}:
      fz.x.str(T.St{bd, rw, hs, he, pt, T.span.rev(cut, nn, U32.is_zero(nn), []), T.LStr{}, T.LStr{}, qk, sk,
        T.HNone{}, un, lf, at, False{}}, cc, b0, bs, rr, h)
    case False{}:
      fz.ectrl(T.str.bad(Char.to_u32(cc), False{}), basic, qq, cc, cut, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at,
        b0, bs, rr, h)

# a span's character
def fz.ebasic(
  +basic: Bool,
  +qq: Char,
  +cc: Char,
  +cut: String,
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
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  +h: {FzP{bd, rw} == FzP{SCon{b0, bs}, rr} : FzP}
) -> fz.M(T.eat.basic(basic, qq, cc, cut, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at), b0, bs, rr):
  match basic:
    case False{}:
      fz.ectrl(T.str.bad(Char.to_u32(cc), False{}), False{}, qq, cc, cut, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at,
        b0, bs, rr, h)
    case True{}:
      fz.ebs(Char.is_eq(cc, '\\'), True{}, qq, cc, cut, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at, b0, bs, rr, h)

# a span closed
def fz.eq(
  +quote: Bool,
  +basic: Bool,
  +qq: Char,
  +cc: Char,
  +cut: String,
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
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  +h: {FzP{bd, rw} == FzP{SCon{b0, bs}, rr} : FzP}
) -> fz.M(T.eat.feed.q(quote, basic, qq, cc, cut, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at), b0, bs, rr):
  match quote:
    case True{}:
      fz.take(T.St{bd, rw, hs, he, pt, [], T.LStr{}, T.LStr{}, qk, sk, T.HNone{}, un, lf, at, False{}}, T.VSpan{cut,
        nn},
        b0, bs, rr, h)
    case False{}:
      fz.ebasic(basic, qq, cc, cut, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at, b0, bs, rr, h)

# a span's next character
def fz.eat(
  +basic: Bool,
  +qq: Char,
  +cut: String,
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
  +cc: Char,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  +h: {FzP{bd, rw} == FzP{SCon{b0, bs}, rr} : FzP}
) -> fz.M(T.eat.feed(basic, qq, cut, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at, cc), b0, bs, rr):
  fz.eq(Char.is_eq(cc, qq), basic, qq, cc, cut, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at, b0, bs, rr, h)

# a token still open at the end
def fz.flex(
  +lx: T.Lex,
  +st: T.St,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.read.fin.lex(lx, st), b0, bs, rr):
  match lx:
    case T.LTop{}:
      h
    case T.LLine{}:
      h
    case T.LKey{}:
      h
    case T.LKeyDot{}:
      h
    case T.LAfter{}:
      h
    case T.LKeyQ{}:
      h
    case T.LKeyE{}:
      h
    case T.LKeyU{}:
      h
    case T.LVal{}:
      h
    case T.LQ{}:
      h
    case T.LQ2{}:
      fz.take(st, T.VStr{""}, b0, bs, rr, h)
    case T.LStr{}:
      h
    case T.LEsc{}:
      h
    case T.LUni{}:
      h
    case T.LFold{}:
      h
    case T.LMq{}:
      h
    case T.LMqEnd{}:
      fz.sfin(st, b0, bs, rr, h)
    case T.LTrim{}:
      h
    case T.LTrim2{}:
      h
    case T.LBare{}:
      fz.finish(st, ' ', False{}, b0, bs, rr, h)
    case T.LDate{}:
      fz.finish(st, ' ', False{}, b0, bs, rr, h)
    case T.LCom{}:
      h
    case T.LHead{}:
      h
    case T.LHeadGap{}:
      h
    case T.LHeadDot{}:
      h
    case T.LHeadQ{}:
      h
    case T.LHeadE{}:
      h
    case T.LHeadU{}:
      h
    case T.LHeadR{}:
      h
    case T.LArr{}:
      h
    case T.LArrC{}:
      h
    case T.LInl{}:
      h
    case T.LInlK{}:
      h
    case T.LInlC{}:
      h
    case T.LSink{}:
      h

# a token still open at the end
def fz.fclose(
  +st: T.St,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.K(T.read.fin.close(st), b0, bs, rr):
  match st:
    case T.St{bd, rw, hs, he, pt, bf, +lx, bk, qk, sk, hd, un, lf, at, ld}:
      fz.flex(lx, T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, hd, un, lf, at, ld}, b0, bs, rr, h)

# the document at the end
def fz.fstack(
  +sk: List<&2, T.Ctx>,
  +bd: String,
  +rw: List<&2, T.Val>,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  +h: {FzP{bd, rw} == FzP{SCon{b0, bs}, rr} : FzP}
) -> fz.D(T.read.fin.stack(sk, bd, rw), b0, bs, rr):
  match sk:
    case []:
      fz.doc(bd, rw, b0, bs, rr, h)
    case _c <> _r:
      fz.doce(bd, rw, "unclosed", b0, bs, rr, h)

# the document at the end
def fz.fdoc(
  +st: T.St,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.D(T.read.fin.doc(st), b0, bs, rr):
  match st:
    case T.St{bd, rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, sk, _hd, _un, _lf, _at, _ld}:
      fz.fstack(sk, bd, rw, b0, bs, rr, h)

# an unfinished document
def fz.func(
  +st: T.St,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.D(T.read.fin.unclosed(st), b0, bs, rr):
  match st:
    case T.St{bd, rw, _hs, _he, _pt, _bf, _lx, _bk, _qk, _sk, _hd, _un, _lf, _at, _ld}:
      fz.doce(bd, rw, "unclosed", b0, bs, rr, h)

# a comment at the end
def fz.fcom(
  +ok: Bool,
  +st: T.St,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.D(T.read.fin.com(ok, st), b0, bs, rr):
  match ok:
    case True{}:
      fz.fdoc(st, b0, bs, rr, h)
    case False{}:
      fz.func(st, b0, bs, rr, h)

# the states that may end a document
def fz.fok(
  +lx: T.Lex,
  +st: T.St,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.D(T.read.fin.ok(lx, st), b0, bs, rr):
  match lx:
    case T.LTop{}:
      fz.fdoc(st, b0, bs, rr, h)
    case T.LLine{}:
      fz.fdoc(st, b0, bs, rr, h)
    case T.LKey{}:
      fz.func(st, b0, bs, rr, h)
    case T.LKeyDot{}:
      fz.func(st, b0, bs, rr, h)
    case T.LAfter{}:
      fz.func(st, b0, bs, rr, h)
    case T.LKeyQ{}:
      fz.func(st, b0, bs, rr, h)
    case T.LKeyE{}:
      fz.func(st, b0, bs, rr, h)
    case T.LKeyU{}:
      fz.func(st, b0, bs, rr, h)
    case T.LVal{}:
      fz.func(st, b0, bs, rr, h)
    case T.LQ{}:
      fz.func(st, b0, bs, rr, h)
    case T.LQ2{}:
      fz.func(st, b0, bs, rr, h)
    case T.LStr{}:
      fz.func(st, b0, bs, rr, h)
    case T.LEsc{}:
      fz.func(st, b0, bs, rr, h)
    case T.LUni{}:
      fz.func(st, b0, bs, rr, h)
    case T.LFold{}:
      fz.func(st, b0, bs, rr, h)
    case T.LMq{}:
      fz.func(st, b0, bs, rr, h)
    case T.LMqEnd{}:
      fz.func(st, b0, bs, rr, h)
    case T.LTrim{}:
      fz.func(st, b0, bs, rr, h)
    case T.LTrim2{}:
      fz.func(st, b0, bs, rr, h)
    case T.LBare{}:
      fz.func(st, b0, bs, rr, h)
    case T.LDate{}:
      fz.func(st, b0, bs, rr, h)
    case T.LCom{}:
      match st:
        case T.St{bd, rw, hs, he, pt, bf, lx, +bk, qk, sk, hd, un, lf, at, ld}:
          fz.fcom(T.read.fin.end(bk), T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, hd, un, lf, at, ld}, b0, bs, rr,
            h)
    case T.LHead{}:
      fz.func(st, b0, bs, rr, h)
    case T.LHeadGap{}:
      fz.func(st, b0, bs, rr, h)
    case T.LHeadDot{}:
      fz.func(st, b0, bs, rr, h)
    case T.LHeadQ{}:
      fz.func(st, b0, bs, rr, h)
    case T.LHeadE{}:
      fz.func(st, b0, bs, rr, h)
    case T.LHeadU{}:
      fz.func(st, b0, bs, rr, h)
    case T.LHeadR{}:
      fz.func(st, b0, bs, rr, h)
    case T.LArr{}:
      fz.func(st, b0, bs, rr, h)
    case T.LArrC{}:
      fz.func(st, b0, bs, rr, h)
    case T.LInl{}:
      fz.func(st, b0, bs, rr, h)
    case T.LInlK{}:
      fz.func(st, b0, bs, rr, h)
    case T.LInlC{}:
      fz.func(st, b0, bs, rr, h)
    case T.LSink{}:
      fz.fdoc(st, b0, bs, rr, h)

# the document at the end
def fz.fin2(
  +st: T.St,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.D(T.read.fin2(st), b0, bs, rr):
  match st:
    case T.St{bd, rw, hs, he, pt, bf, +lx, bk, qk, sk, hd, un, lf, at, ld}:
      fz.fok(lx, T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, hd, un, lf, at, ld}, b0, bs, rr, h)

# the document at the end
def fz.fin(
  +st: T.St,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.K(st, b0, bs, rr)
) -> fz.D(T.read.fin(st), b0, bs, rr):
  fz.fin2(T.read.fin.close(st), b0, bs, rr, fz.fclose(st, b0, bs, rr, h))

# by induction on the text, in every mode: each character keeps the error
# and the rows, and the end gives the document of them
def fz.read(
  tt: String,
  +md: T.Mode,
  +b0: Char,
  +bs: String,
  +rr: List<&2, T.Val>,
  h: fz.M(md, b0, bs, rr)
) -> fz.D(T.doc.read(tt, md), b0, bs, rr):
  match tt md:
    case SNil{} T.MScan{st}:
      fz.fin(T.read.once2(st), b0, bs, rr, fz.once2(st, b0, bs, rr, h))
    case SNil{} T.MCr{st}:
      fz.fin(T.read.once2(T.st.err(st, "carriage return without line feed")), b0, bs, rr, fz.once2(T.st.err(st,
        "carriage return without line feed"), b0, bs, rr, fz.err(st, "carriage return without line feed", b0, bs, rr,
        h)))
    case SNil{} T.MOpen{_b, _q, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at}:
      fz.fin(T.read.once2(T.St{bd, rw, hs, he, pt, bf, T.LQ{}, bk, qk, sk, T.HNone{}, un, lf, at, False{}}), b0, bs, rr,
        fz.once2(T.St{bd, rw, hs, he, pt, bf, T.LQ{}, bk, qk, sk, T.HNone{}, un, lf, at, False{}}, b0, bs, rr, h))
    case SNil{} T.MEat{_b, _q, _cut, _n, bd, rw, _hs, _he, _pt, _qk, _sk, _un, _lf, _at}:
      fz.doce(bd, rw, "unclosed", b0, bs, rr, h)
    case SCon{+hh, t2} T.MScan{st}:
      fz.read(t2, T.doc.scan(st, hh), b0, bs, rr, fz.scan(st, hh, b0, bs, rr, h))
    case SCon{+hh, t2} T.MCr{st}:
      fz.read(t2, T.doc.cr(Char.is_eq(hh, '\n'), st, hh), b0, bs, rr, fz.cr(Char.is_eq(hh, '\n'), st, hh, b0, bs, rr,
        h))
    case SCon{+hh, +t2} T.MOpen{basic, qq, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at}:
      fz.read(t2, T.doc.open(basic, qq, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, hh, t2), b0, bs, rr,
        fz.open(basic, qq, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, hh, t2, b0, bs, rr, h))
    case SCon{+hh, t2} T.MEat{basic, qq, cut, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at}:
      fz.read(t2, T.eat.feed(basic, qq, cut, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at, hh), b0, bs, rr,
        fz.eat(basic, qq, cut, nn, bd, rw, hs, he, pt, qk, sk, un, lf, at, hh, b0, bs, rr, h))

def L2.error_stays(bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead, e, t):
  match bad:
    case SNil{}:
      Eq.bit.absurd2(&2, {T.doc.read(t, T.MScan{T.St{SNil{}, rows, heads, here, parts, buf, lex, back, qkind, stack,
        hold,
        uni, left, arrtab, lead}}) == T.Doc{SNil{}, T.rows.seal(rows)} : T.Doc}, e)
    case SCon{+b0, +bs}:
      fz.read(t, T.MScan{T.St{SCon{b0, bs}, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left,
        arrtab, lead}}, b0, bs, rows, {==})
