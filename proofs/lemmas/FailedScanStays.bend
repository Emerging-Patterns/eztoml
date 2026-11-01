# a failed scanner stays failed through the rest of the text
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/ParsesExactlyTheGrammar.bend as L1
import ./PickAndDigitSteps.bend as M1

# the mode a failed scanner is read in: after a carriage return, or not
def sk.mode(cr: Bool, st: T.St) -> T.Mode:
  match cr:
    case True{}:
      T.MCr{st}
    case False{}:
      T.MScan{st}

# the end of the text reads the first error back, open frames or not
def sk.fin(
  stack: List<&2, T.Ctx>,
  b0: Char,
  bs: String,
  rows: List<&2, T.Val>
) -> {T.bad(T.read.fin.stack(stack, SCon{b0, bs}, rows)) == SCon{b0, bs} : String}:
  match stack:
    case []:
      {==}
    case _h <> _t:
      {==}

# a byte-order mark or not, the first character leaves the failed scanner
def sk.bom(
  bom: Bool,
  b0: Char,
  bs: String,
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  parts: List<&2, String>,
  buf: List<&2, Char>,
  back: T.Lex,
  qkind: T.QKind,
  stack: List<&2, T.Ctx>,
  uni: U32,
  left: U32,
  arrtab: Bool,
  hh: Char
) -> {T.read.once2(T.read.step.bom(bom, M1.sk(False{}, b0, bs, rows, heads, here, parts, buf,
  back, qkind, stack, uni, left, arrtab), hh)) == M1.sk(False{}, b0, bs, rows, heads, here,
  parts, buf, back, qkind, stack, uni, left, arrtab) : T.St}:
  match bom:
    case True{}:
      {==}
    case False{}:
      {==}

# one character leaves the failed scanner as it is, past the first character
def sk.fast(
  lead: Bool,
  b0: Char,
  bs: String,
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  parts: List<&2, String>,
  buf: List<&2, Char>,
  back: T.Lex,
  qkind: T.QKind,
  stack: List<&2, T.Ctx>,
  uni: U32,
  left: U32,
  arrtab: Bool,
  +hh: Char
) -> {T.read.fast(M1.sk(lead, b0, bs, rows, heads, here, parts, buf, back, qkind, stack, uni,
  left, arrtab), hh) == M1.sk(False{}, b0, bs, rows, heads, here, parts, buf, back, qkind,
  stack, uni, left, arrtab) : T.St}:
  match lead:
    case False{}:
      {==}
    case True{}:
      sk.bom(U32.is_eq(Char.to_u32(hh), 65279), b0, bs, rows, heads, here, parts, buf, back,
        qkind, stack, uni, left, arrtab, hh)

# the rest of the text reads a failed scanner's first error back
def sk.ok(
  tt: String,
  cr: Bool,
  lead: Bool,
  b0: Char,
  bs: String,
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  parts: List<&2, String>,
  buf: List<&2, Char>,
  back: T.Lex,
  qkind: T.QKind,
  stack: List<&2, T.Ctx>,
  uni: U32,
  left: U32,
  arrtab: Bool
) -> Type:
  {T.bad(T.doc.read(tt, sk.mode(cr, M1.sk(lead, b0, bs, rows, heads, here, parts, buf, back,
    qkind, stack, uni, left, arrtab)))) == SCon{b0, bs} : String}

# a character read in the scan mode: whichever way doc.scan turns, the failed
# scanner comes out as it went in
def sk.scan(
  dq: Bool,
  sq: Bool,
  cr: Bool,
  +lead: Bool,
  +b0: Char,
  +bs: String,
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
  +hh: Char,
  tt: String,
  ih0: sk.ok(tt, False{}, False{}, b0, bs, rows, heads, here, parts, buf, back, qkind, stack, uni, left, arrtab),
  ih1: sk.ok(tt, True{}, False{}, b0, bs, rows, heads, here, parts, buf, back, qkind, stack, uni, left, arrtab)
) -> {T.bad(T.doc.read(tt, T.doc.scan.q(dq, sq, cr, M1.sk(lead, b0, bs, rows, heads, here,
  parts, buf, back, qkind, stack, uni, left, arrtab), hh))) == SCon{b0, bs} : String}:
  match dq:
    case True{}:
      Equal.trans(String,
        T.bad(T.doc.read(tt, T.doc.wrap(T.read.fast(M1.sk(lead, b0, bs, rows, heads, here,
          parts, buf, back, qkind, stack, uni, left, arrtab), hh)))),
        T.bad(T.doc.read(tt, T.doc.wrap(M1.sk(False{}, b0, bs, rows, heads, here, parts, buf,
          back, qkind, stack, uni, left, arrtab)))),
        SCon{b0, bs},
        Equal.cong(T.St, String, s => T.bad(T.doc.read(tt, T.doc.wrap(s))),
          T.read.fast(M1.sk(lead, b0, bs, rows, heads, here, parts, buf, back, qkind, stack,
            uni, left, arrtab), hh),
          M1.sk(False{}, b0, bs, rows, heads, here, parts, buf, back, qkind, stack, uni, left,
            arrtab),
          sk.fast(lead, b0, bs, rows, heads, here, parts, buf, back, qkind, stack, uni,
            left, arrtab, hh)),
        ih0)
    case False{}:
      match sq:
        case True{}:
          Equal.trans(String,
            T.bad(T.doc.read(tt, T.doc.wrap(T.read.fast(M1.sk(lead, b0, bs, rows, heads, here,
              parts, buf, back, qkind, stack, uni, left, arrtab), hh)))),
            T.bad(T.doc.read(tt, T.doc.wrap(M1.sk(False{}, b0, bs, rows, heads, here, parts,
              buf, back, qkind, stack, uni, left, arrtab)))),
            SCon{b0, bs},
            Equal.cong(T.St, String, s => T.bad(T.doc.read(tt, T.doc.wrap(s))),
              T.read.fast(M1.sk(lead, b0, bs, rows, heads, here, parts, buf, back, qkind,
                stack, uni, left, arrtab), hh),
              M1.sk(False{}, b0, bs, rows, heads, here, parts, buf, back, qkind, stack, uni,
                left, arrtab),
              sk.fast(lead, b0, bs, rows, heads, here, parts, buf, back, qkind, stack, uni,
                left, arrtab, hh)),
            ih0)
        case False{}:
          match cr:
            case True{}:
              Equal.trans(String,
                T.bad(T.doc.read(tt, T.MCr{T.read.fast(M1.sk(lead, b0, bs, rows, heads, here,
                  parts, buf, back, qkind, stack, uni, left, arrtab), hh)})),
                T.bad(T.doc.read(tt, T.MCr{M1.sk(False{}, b0, bs, rows, heads, here, parts,
                  buf, back, qkind, stack, uni, left, arrtab)})),
                SCon{b0, bs},
                Equal.cong(T.St, String, s => T.bad(T.doc.read(tt, T.MCr{s})),
                  T.read.fast(M1.sk(lead, b0, bs, rows, heads, here, parts, buf, back, qkind,
                    stack, uni, left, arrtab), hh),
                  M1.sk(False{}, b0, bs, rows, heads, here, parts, buf, back, qkind, stack,
                    uni, left, arrtab),
                  sk.fast(lead, b0, bs, rows, heads, here, parts, buf, back, qkind, stack,
                    uni, left, arrtab, hh)),
                ih1)
            case False{}:
              Equal.trans(String,
                T.bad(T.doc.read(tt, T.MScan{T.read.fast(M1.sk(lead, b0, bs, rows, heads,
                  here, parts, buf, back, qkind, stack, uni, left, arrtab), hh)})),
                T.bad(T.doc.read(tt, T.MScan{M1.sk(False{}, b0, bs, rows, heads, here, parts,
                  buf, back, qkind, stack, uni, left, arrtab)})),
                SCon{b0, bs},
                Equal.cong(T.St, String, s => T.bad(T.doc.read(tt, T.MScan{s})),
                  T.read.fast(M1.sk(lead, b0, bs, rows, heads, here, parts, buf, back, qkind,
                    stack, uni, left, arrtab), hh),
                  M1.sk(False{}, b0, bs, rows, heads, here, parts, buf, back, qkind, stack,
                    uni, left, arrtab),
                  sk.fast(lead, b0, bs, rows, heads, here, parts, buf, back, qkind, stack,
                    uni, left, arrtab, hh)),
                ih0)

# the character after a carriage return: a line feed is read, anything else
# sets an error the scanner already has
def sk.cr(
  lf: Bool,
  +lead: Bool,
  +b0: Char,
  +bs: String,
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
  +hh: Char,
  tt: String,
  ih0: sk.ok(tt, False{}, False{}, b0, bs, rows, heads, here, parts, buf, back, qkind, stack, uni, left, arrtab),
  ihl: sk.ok(tt, False{}, lead, b0, bs, rows, heads, here, parts, buf, back, qkind, stack, uni, left, arrtab)
) -> {T.bad(T.doc.read(tt, T.doc.cr(lf, M1.sk(lead, b0, bs, rows, heads, here, parts, buf,
  back, qkind, stack, uni, left, arrtab), hh))) == SCon{b0, bs} : String}:
  match lf:
    case True{}:
      Equal.trans(String,
        T.bad(T.doc.read(tt, T.MScan{T.read.fast(M1.sk(lead, b0, bs, rows, heads, here,
          parts, buf, back, qkind, stack, uni, left, arrtab), hh)})),
        T.bad(T.doc.read(tt, T.MScan{M1.sk(False{}, b0, bs, rows, heads, here, parts, buf,
          back, qkind, stack, uni, left, arrtab)})),
        SCon{b0, bs},
        Equal.cong(T.St, String, s => T.bad(T.doc.read(tt, T.MScan{s})),
          T.read.fast(M1.sk(lead, b0, bs, rows, heads, here, parts, buf, back, qkind, stack,
            uni, left, arrtab), hh),
          M1.sk(False{}, b0, bs, rows, heads, here, parts, buf, back, qkind, stack, uni, left,
            arrtab),
          sk.fast(lead, b0, bs, rows, heads, here, parts, buf, back, qkind, stack, uni,
            left, arrtab, hh)),
        ih0)
    case False{}:
      ihl

# by induction on the text, in either mode, from either side of the first
# character
def sk.go(
  tt: String,
  cr: Bool,
  +lead: Bool,
  +b0: Char,
  +bs: String,
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
  +arrtab: Bool
) -> {T.bad(T.doc.read(tt, sk.mode(cr, M1.sk(lead, b0, bs, rows, heads, here, parts, buf,
  back, qkind, stack, uni, left, arrtab)))) == SCon{b0, bs} : String}:
  match tt:
    case SNil{}:
      match cr:
        case True{}:
          sk.fin(stack, b0, bs, rows)
        case False{}:
          sk.fin(stack, b0, bs, rows)
    case SCon{+hh, +rest}:
      match cr:
        case False{}:
          sk.scan(Char.is_eq(hh, '"'), Char.is_eq(hh, '\''), U32.is_eq(Char.to_u32(hh), 13),
            lead, b0, bs, rows, heads, here, parts, buf, back, qkind, stack, uni, left,
            arrtab, hh, rest,
            sk.go(rest, False{}, False{}, b0, bs, rows, heads, here, parts, buf, back,
              qkind, stack, uni, left, arrtab),
            sk.go(rest, True{}, False{}, b0, bs, rows, heads, here, parts, buf, back,
              qkind, stack, uni, left, arrtab))
        case True{}:
          sk.cr(Char.is_eq(hh, '\n'), lead, b0, bs, rows, heads, here, parts, buf, back,
            qkind, stack, uni, left, arrtab, hh, rest,
            sk.go(rest, False{}, False{}, b0, bs, rows, heads, here, parts, buf, back,
              qkind, stack, uni, left, arrtab),
            sk.go(rest, False{}, lead, b0, bs, rows, heads, here, parts, buf, back, qkind,
              stack, uni, left, arrtab))

def L1.fail_stays(
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
  lead,
  e,
  t
):
  match bad:
    case SNil{}:
      Eq.bit.absurd2(&2, {T.bad(T.doc.read(t, T.MScan{T.St{SNil{}, rows, heads, here, parts,
        buf, T.LSink{}, back, qkind, stack, T.HNone{}, uni, left, arrtab, lead}})) == SNil{}
        : String}, e)
    case SCon{b0, bs}:
      sk.go(t, False{}, lead, b0, bs, rows, heads, here, parts, buf, back, qkind, stack,
        uni, left, arrtab)

# any scanner that sets an error comes to the failed state, and the error it
# has then, its own or the new one, is never empty
def err.sinks(
  st: T.St,
  w0: Char,
  ws: String,
  +tt: String
) -> {String.is_empty(T.bad(T.doc.read(tt, T.MScan{T.st.err(st, SCon{w0, ws})})))
  == False{} : Bool}:
  match st:
    case T.St{bad, rows, heads, here, parts, buf, _lex, back, qkind, stack, _hold, uni,
      left, arrtab, lead}:
      match bad:
        case SNil{}:
          Equal.cong(String, Bool, s => String.is_empty(s),
            T.bad(T.doc.read(tt, T.MScan{M1.sk(lead, w0, ws, rows, heads, here, parts, buf,
              back, qkind, stack, uni, left, arrtab)})),
            SCon{w0, ws},
            sk.go(tt, False{}, lead, w0, ws, rows, heads, here, parts, buf, back, qkind,
              stack, uni, left, arrtab))
        case SCon{b0, bs}:
          Equal.cong(String, Bool, s => String.is_empty(s),
            T.bad(T.doc.read(tt, T.MScan{M1.sk(lead, b0, bs, rows, heads, here, parts, buf,
              back, qkind, stack, uni, left, arrtab)})),
            SCon{b0, bs},
            sk.go(tt, False{}, lead, b0, bs, rows, heads, here, parts, buf, back, qkind,
              stack, uni, left, arrtab))
