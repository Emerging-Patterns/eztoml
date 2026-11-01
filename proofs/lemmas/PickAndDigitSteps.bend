# a pair picks itself out of rows, with digit steps and escape lexing
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/defs/BareValueGrammar.bend as D1
import ../../laws/defs/DocumentSameness.bend as D2
import ./ShortTextBounds.bend as M1

# a walk that already compared LT ends there, whatever is left, and
# str.eq's walk ends False
def str.eq.step.lt(
  aa: String,
  bb: String
) -> {T.str.eq.step(aa, bb, False{}) == Cmp.is_eq(String.order.go(aa, bb, LT{})) : Bool}:
  match aa bb:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{_h, _t}:
      {==}
    case SCon{_h, _t} SNil{}:
      {==}
    case SCon{Chr{_x}, _xt} SCon{Chr{_y}, _yt}:
      {==}

# and the same for GT
def str.eq.step.gt(
  aa: String,
  bb: String
) -> {T.str.eq.step(aa, bb, False{}) == Cmp.is_eq(String.order.go(aa, bb, GT{})) : Bool}:
  match aa bb:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{_h, _t}:
      {==}
    case SCon{_h, _t} SNil{}:
      {==}
    case SCon{Chr{_x}, _xt} SCon{Chr{_y}, _yt}:
      {==}

# after two first chars that compared as cc, both walks give the same answer
# (Base 2.0.37 walks String.eq as String.order.go, carrying cc)
def str.eq.agree.cmp(
  +xt: String,
  +yt: String,
  cc: Cmp,
  ih: {T.str.eq(xt, yt) == String.eq(xt, yt) : Bool}
) -> {T.str.eq.step(xt, yt, Cmp.is_eq(cc))
  == Cmp.is_eq(String.order.go(xt, yt, cc)) : Bool}:
  match cc:
    case LT{}:
      str.eq.step.lt(xt, yt)
    case EQ{}:
      ih
    case GT{}:
      str.eq.step.gt(xt, yt)

# the code's string equality is Base's, on every pair of strings
def str.eq.agree(
  +aa: String,
  +bb: String
) -> {T.str.eq(aa, bb) == String.eq(aa, bb) : Bool}:
  match aa bb:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{_h, _t}:
      {==}
    case SCon{_h, _t} SNil{}:
      {==}
    case SCon{Chr{+uu}, +xt} SCon{Chr{+ww}, +yt}:
      str.eq.agree.cmp(xt, yt, U32.cmp(uu, ww), str.eq.agree(xt, yt))

# The scanner's refusals. A failed scanner sits in LSink with nothing held:
# every character leaves it as it is, and the end of the text reads its first
# error back. A refusal law then only follows one character from the state it
# names to that failed state.

# a failed scanner, its first error written as a first char and the rest
def sk(
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
) -> T.St:
  T.St{SCon{b0, bs}, rows, heads, here, parts, buf, T.LSink{}, back, qkind, stack,
    T.HNone{}, uni, left, arrtab, lead}

# A head that matches itself: comparing h <> t with h <> o is comparing [h]
# with [h], and then t with o. A pair picks itself, the first pair of its name,
# and any other value meets itself first.

# a head's part and then the rest, as the part alone and the rest
def at.split(
  bb: Bool,
  -xx: Bool
) -> {D2.and_then(bb, _u => xx) == Bool.and(D2.and_then(bb, _u => True{}), xx) : Bool}:
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# a pair picks itself out of rows it heads
def pick.self(
  +nn: String,
  vv: T.Val,
  tt: List<&2, T.Val>
) -> {D2.pick(T.VPair{nn, vv} <> tt, nn) == D2.Picked{vv, tt} : D2.Pick}:
  Equal.cong(Bool, D2.Pick, bb => D2.pick.step(bb, nn, vv, tt, _u => D2.pick(tt, nn)),
    String.eq(nn, nn), True{}, Eq.string_eq_self(nn))

# a pair's head cancel, whatever its comparison and its rest
def hc.pair(
  +nn: String,
  +vv: T.Val,
  +oo: List<&2, T.Val>,
  cmp: T.Val -> Bool,
  -rest: List<&2, T.Val> -> Bool
) -> {D2.same.pair(D2.pick(T.VPair{nn, vv} <> oo, nn), cmp, rest)
  == Bool.and(D2.same.pair(D2.pick(T.VPair{nn, vv} <> [], nn), cmp, rr => D2.same.go([], rr)), rest(oo))
  : Bool}:
  Equal.trans(Bool,
    D2.same.pair(D2.pick(T.VPair{nn, vv} <> oo, nn), cmp, rest),
    D2.and_then(cmp(vv), _u => rest(oo)),
    Bool.and(D2.same.pair(D2.pick(T.VPair{nn, vv} <> [], nn), cmp, rr => D2.same.go([], rr)), rest(oo)),
    Equal.cong(D2.Pick, Bool, pp => D2.same.pair(pp, cmp, rest),
      D2.pick(T.VPair{nn, vv} <> oo, nn), D2.Picked{vv, oo}, pick.self(nn, vv, oo)),
    Equal.trans(Bool,
      D2.and_then(cmp(vv), _u => rest(oo)),
      Bool.and(D2.and_then(cmp(vv), _u => True{}), rest(oo)),
      Bool.and(D2.same.pair(D2.pick(T.VPair{nn, vv} <> [], nn), cmp, rr => D2.same.go([], rr)), rest(oo)),
      at.split(cmp(vv), rest(oo)),
      Equal.cong(D2.Pick, Bool, pp => Bool.and(D2.same.pair(pp, cmp, rr => D2.same.go([], rr)), rest(oo)),
        D2.Picked{vv, []}, D2.pick(T.VPair{nn, vv} <> [], nn),
        Equal.sym(D2.Pick, D2.pick(T.VPair{nn, vv} <> [], nn), D2.Picked{vv, []}, pick.self(nn, vv, [])))))

# any other value's head cancel
def hc.item(
  +hh: T.Val,
  +oo: List<&2, T.Val>,
  cmp: T.Val -> Bool,
  -rest: List<&2, T.Val> -> Bool
) -> {D2.same.item(hh <> oo, cmp, rest)
  == Bool.and(D2.same.item(hh <> [], cmp, rr => D2.same.go([], rr)), rest(oo)) : Bool}:
  at.split(cmp(hh), rest(oo))

# a pair's head cancel, by the kind of its value
def hc.p(
  +nn: String,
  vv: T.Val,
  +tt: List<&2, T.Val>,
  +oo: List<&2, T.Val>
) -> {D2.same.go(T.VPair{nn, vv} <> tt, T.VPair{nn, vv} <> oo)
  == Bool.and(D2.same.go(T.VPair{nn, vv} <> [], T.VPair{nn, vv} <> []), D2.same.go(tt, oo)) : Bool}:
  match vv:
    case T.VStr{+a1}:
      hc.pair(nn, T.VStr{a1}, oo, ww => D2.same.atom(T.VStr{a1}, ww), rr => D2.same.go(tt, rr))
    case T.VSpan{+a1, +a2}:
      hc.pair(nn, T.VSpan{a1, a2}, oo, ww => D2.same.atom(T.VSpan{a1, a2}, ww), rr => D2.same.go(tt, rr))
    case T.VInt{+a1, +a2}:
      hc.pair(nn, T.VInt{a1, a2}, oo, ww => D2.same.atom(T.VInt{a1, a2}, ww), rr => D2.same.go(tt, rr))
    case T.VFlo{+a1, +a2}:
      hc.pair(nn, T.VFlo{a1, a2}, oo, ww => D2.same.atom(T.VFlo{a1, a2}, ww), rr => D2.same.go(tt, rr))
    case T.VBool{+a1}:
      hc.pair(nn, T.VBool{a1}, oo, ww => D2.same.atom(T.VBool{a1}, ww), rr => D2.same.go(tt, rr))
    case T.VWhen{+a1}:
      hc.pair(nn, T.VWhen{a1}, oo, ww => D2.same.atom(T.VWhen{a1}, ww), rr => D2.same.go(tt, rr))
    case T.VArr{+ls}:
      hc.pair(nn, T.VArr{ls}, oo, ww => D2.same.box(D2.KArr{}, ww, ws => D2.same.go(ls, ws)),
        rr => D2.same.go(tt, rr))
    case T.VInl{+ls}:
      hc.pair(nn, T.VInl{ls}, oo, ww => D2.same.box(D2.KInl{}, ww, ws => D2.same.go(ls, ws)),
        rr => D2.same.go(tt, rr))
    case T.VHead{+pa, +ls}:
      hc.pair(nn, T.VHead{pa, ls}, oo, ww => D2.same.box(D2.KHead{}, ww, ws => D2.same.go(ls, ws)),
        rr => D2.same.go(tt, rr))
    case T.VAot{+pa, +ls}:
      hc.pair(nn, T.VAot{pa, ls}, oo, ww => D2.same.box(D2.KAot{}, ww, ws => D2.same.go(ls, ws)),
        rr => D2.same.go(tt, rr))
    case T.VAots{+pa, +ls}:
      hc.pair(nn, T.VAots{pa, ls}, oo, ww => D2.same.box(D2.KAots{}, ww, ws => D2.same.go(ls, ws)),
        rr => D2.same.go(tt, rr))
    case T.VPair{+a1, +a2}:
      hc.pair(nn, T.VPair{a1, a2}, oo, ww => D2.same.atom(T.VPair{a1, a2}, ww), rr => D2.same.go(tt, rr))

# a head matches itself, whatever it is
def hc(
  hh: T.Val,
  +tt: List<&2, T.Val>,
  +oo: List<&2, T.Val>
) -> {D2.same.go(hh <> tt, hh <> oo) == Bool.and(D2.same.go(hh <> [], hh <> []), D2.same.go(tt, oo)) : Bool}:
  match hh:
    case T.VStr{+a1}:
      hc.item(T.VStr{a1}, oo, ww => D2.same.atom(T.VStr{a1}, ww), rr => D2.same.go(tt, rr))
    case T.VSpan{+a1, +a2}:
      hc.item(T.VSpan{a1, a2}, oo, ww => D2.same.atom(T.VSpan{a1, a2}, ww), rr => D2.same.go(tt, rr))
    case T.VInt{+a1, +a2}:
      hc.item(T.VInt{a1, a2}, oo, ww => D2.same.atom(T.VInt{a1, a2}, ww), rr => D2.same.go(tt, rr))
    case T.VFlo{+a1, +a2}:
      hc.item(T.VFlo{a1, a2}, oo, ww => D2.same.atom(T.VFlo{a1, a2}, ww), rr => D2.same.go(tt, rr))
    case T.VBool{+a1}:
      hc.item(T.VBool{a1}, oo, ww => D2.same.atom(T.VBool{a1}, ww), rr => D2.same.go(tt, rr))
    case T.VWhen{+a1}:
      hc.item(T.VWhen{a1}, oo, ww => D2.same.atom(T.VWhen{a1}, ww), rr => D2.same.go(tt, rr))
    case T.VArr{+ls}:
      hc.item(T.VArr{ls}, oo, ww => D2.same.box(D2.KArr{}, ww, ws => D2.same.go(ls, ws)), rr => D2.same.go(tt,
        rr))
    case T.VInl{+ls}:
      hc.item(T.VInl{ls}, oo, ww => D2.same.box(D2.KInl{}, ww, ws => D2.same.go(ls, ws)), rr => D2.same.go(tt,
        rr))
    case T.VHead{+pa, +ls}:
      hc.item(T.VHead{pa, ls}, oo, ww => D2.same.box(D2.KHead{}, ww, ws => D2.same.go(ls, ws)),
        rr => D2.same.go(tt, rr))
    case T.VAot{+pa, +ls}:
      hc.item(T.VAot{pa, ls}, oo, ww => D2.same.box(D2.KAot{}, ww, ws => D2.same.go(ls, ws)),
        rr => D2.same.go(tt, rr))
    case T.VAots{+pa, +ls}:
      hc.item(T.VAots{pa, ls}, oo, ww => D2.same.box(D2.KAots{}, ww, ws => D2.same.go(ls, ws)),
        rr => D2.same.go(tt, rr))
    case T.VPair{+nn, vv}:
      hc.p(nn, vv, tt, oo)

# every value of the rows matches itself alone
def selfs(xs: List<&2, T.Val>) -> Bool:
  match xs:
    case []:
      True{}
    case +hh <> tt:
      Bool.and(D2.same.go(hh <> [], hh <> []), selfs(tt))

# a front that matches itself cancels
def cancel(
  pre: List<&2, T.Val>,
  +z1: List<&2, T.Val>,
  +z2: List<&2, T.Val>,
  +ee: {selfs(pre) == True{} : Bool}
) -> {D2.same.go(List.append(&2, T.Val, pre, z1), List.append(&2, T.Val, pre, z2)) == D2.same.go(z1, z2) : Bool}:
  match pre:
    case []:
      {==}
    case +hh <> +pp:
      Equal.trans(Bool,
        D2.same.go(hh <> List.append(&2, T.Val, pp, z1), hh <> List.append(&2, T.Val, pp, z2)),
        Bool.and(D2.same.go(hh <> [], hh <> []),
          D2.same.go(List.append(&2, T.Val, pp, z1), List.append(&2, T.Val, pp, z2))),
        D2.same.go(z1, z2),
        hc(hh, List.append(&2, T.Val, pp, z1), List.append(&2, T.Val, pp, z2)),
        Equal.trans(Bool,
          Bool.and(D2.same.go(hh <> [], hh <> []),
            D2.same.go(List.append(&2, T.Val, pp, z1), List.append(&2, T.Val, pp, z2))),
          D2.same.go(List.append(&2, T.Val, pp, z1), List.append(&2, T.Val, pp, z2)),
          D2.same.go(z1, z2),
          Equal.cong(Bool, Bool,
            xx => Bool.and(xx, D2.same.go(List.append(&2, T.Val, pp, z1), List.append(&2, T.Val, pp, z2))),
            D2.same.go(hh <> [], hh <> []), True{},
            Eq.and.left(D2.same.go(hh <> [], hh <> []), selfs(pp), ee)),
          cancel(pp, z1, z2, Eq.and.right(D2.same.go(hh <> [], hh <> []), selfs(pp), ee))))

# a pair at the head compares the same against other rows that pick the same
def pick.same(
  +nn: String,
  vv: T.Val,
  +tt: List<&2, T.Val>,
  o1: List<&2, T.Val>,
  o2: List<&2, T.Val>,
  ep: {D2.pick(o1, nn) == D2.pick(o2, nn) : D2.Pick}
) -> {D2.same.go(T.VPair{nn, vv} <> tt, o1) == D2.same.go(T.VPair{nn, vv} <> tt, o2) : Bool}:
  match vv:
    case T.VStr{+a1}:
      Equal.cong(D2.Pick, Bool, pp => D2.same.pair(pp, ww => D2.same.atom(T.VStr{a1}, ww), rr => D2.same.go(tt,
        rr)),
        D2.pick(o1, nn), D2.pick(o2, nn), ep)
    case T.VSpan{+a1, +a2}:
      Equal.cong(D2.Pick, Bool, pp => D2.same.pair(pp, ww => D2.same.atom(T.VSpan{a1, a2}, ww),
        rr => D2.same.go(tt, rr)),
        D2.pick(o1, nn), D2.pick(o2, nn), ep)
    case T.VInt{+a1, +a2}:
      Equal.cong(D2.Pick, Bool, pp => D2.same.pair(pp, ww => D2.same.atom(T.VInt{a1, a2}, ww),
        rr => D2.same.go(tt, rr)),
        D2.pick(o1, nn), D2.pick(o2, nn), ep)
    case T.VFlo{+a1, +a2}:
      Equal.cong(D2.Pick, Bool, pp => D2.same.pair(pp, ww => D2.same.atom(T.VFlo{a1, a2}, ww),
        rr => D2.same.go(tt, rr)),
        D2.pick(o1, nn), D2.pick(o2, nn), ep)
    case T.VBool{+a1}:
      Equal.cong(D2.Pick, Bool, pp => D2.same.pair(pp, ww => D2.same.atom(T.VBool{a1}, ww),
        rr => D2.same.go(tt, rr)),
        D2.pick(o1, nn), D2.pick(o2, nn), ep)
    case T.VWhen{+a1}:
      Equal.cong(D2.Pick, Bool, pp => D2.same.pair(pp, ww => D2.same.atom(T.VWhen{a1}, ww),
        rr => D2.same.go(tt, rr)),
        D2.pick(o1, nn), D2.pick(o2, nn), ep)
    case T.VArr{+ls}:
      Equal.cong(D2.Pick, Bool, pp => D2.same.pair(pp, ww => D2.same.box(D2.KArr{}, ww, ws => D2.same.go(ls,
        ws)), rr => D2.same.go(tt, rr)),
        D2.pick(o1, nn), D2.pick(o2, nn), ep)
    case T.VInl{+ls}:
      Equal.cong(D2.Pick, Bool, pp => D2.same.pair(pp, ww => D2.same.box(D2.KInl{}, ww, ws => D2.same.go(ls,
        ws)), rr => D2.same.go(tt, rr)),
        D2.pick(o1, nn), D2.pick(o2, nn), ep)
    case T.VHead{+pa, +ls}:
      Equal.cong(D2.Pick, Bool, pp => D2.same.pair(pp, ww => D2.same.box(D2.KHead{}, ww, ws => D2.same.go(ls,
        ws)), rr => D2.same.go(tt, rr)),
        D2.pick(o1, nn), D2.pick(o2, nn), ep)
    case T.VAot{+pa, +ls}:
      Equal.cong(D2.Pick, Bool, pp => D2.same.pair(pp, ww => D2.same.box(D2.KAot{}, ww, ws => D2.same.go(ls,
        ws)), rr => D2.same.go(tt, rr)),
        D2.pick(o1, nn), D2.pick(o2, nn), ep)
    case T.VAots{+pa, +ls}:
      Equal.cong(D2.Pick, Bool, pp => D2.same.pair(pp, ww => D2.same.box(D2.KAots{}, ww, ws => D2.same.go(ls,
        ws)), rr => D2.same.go(tt, rr)),
        D2.pick(o1, nn), D2.pick(o2, nn), ep)
    case T.VPair{+a1, +a2}:
      Equal.cong(D2.Pick, Bool, pp => D2.same.pair(pp, ww => D2.same.atom(T.VPair{a1, a2}, ww),
        rr => D2.same.go(tt, rr)),
        D2.pick(o1, nn), D2.pick(o2, nn), ep)

# WP0: the quoted-segment family. A basic quoted segment is read the same
# way in a key (LKeyQ, with LKeyE and LKeyU for its escapes) and in a header
# (LHeadQ, with LHeadE and LHeadU); only the state each character returns to
# differs, and the state after the closing quote. The lemmas below take which
# one as a bit hd, and every field a quoted segment leaves alone as a
# parameter, so key_reads_back reads its key with them at hd = False and a
# header proof reads a segment with them at hd = True. Those fields are rw
# (the rows), hs (heads), he (here), ps (parts), sk (the stack) and ab
# (arrtab).

# the state inside a basic quoted segment: a key's, or a header's when hd
def qs.lex(hd: Bool) -> T.Lex:
  match hd:
    case False{}:
      T.LKeyQ{}
    case True{}:
      T.LHeadQ{}

# a scanner inside a basic quoted segment, its characters so far reversed in
# buf, and back wherever the last escape left it
def qs(
  hd: Bool,
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  parts: List<&2, String>,
  stack: List<&2, T.Ctx>,
  arrtab: Bool,
  back: T.Lex,
  buf: List<&2, Char>
) -> T.St:
  T.St{"", rows, heads, here, parts, buf, qs.lex(hd), back, T.QBasic{}, stack, T.HNone{},
    0, 0, arrtab, False{}}

# The escapes. Once a character needs an escape the span is copied into the
# buffer (eat.copy, span.rev) and the rest of the string is read in LStr,
# one character of escs at a time: a plain character on the fast path, an
# escape through LEsc, and a \u escape through LUni. back stays at LStr all
# the way; a \u escape leaves uni and left at 0, so a per-character step
# takes the rest of the walk as a function of those two, as qs does of back.

# a scanner inside a basic string being copied, its characters so far
# reversed in buf
def ls(
  bd: String,
  rw: List<&2, T.Val>,
  hs: List<&2, String>,
  he: List<&2, String>,
  ps: List<&2, String>,
  sk: List<&2, T.Ctx>,
  ab: Bool,
  un: U32,
  lf: U32,
  buf: List<&2, Char>
) -> T.St:
  T.St{bd, rw, hs, he, ps, buf, T.LStr{}, T.LStr{}, T.QBasic{}, sk, T.HNone{}, un, lf, ab, False{}}

# The ten values below ten. A U32 below ten has zeros above its four low bits,
# so a claim made of each of 0 to 9 is made of every U32 below ten.

# the U32 of four low bits and zeros above them
def sm.u(b0: Bool, b1: Bool, b2: Bool, b3: Bool) -> U32:
  U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, Eq.zw(28n)}}}}}

# a U32's comparison with 10, bit by bit, the bits above the fourth comparing
# as cc with zero
def sm.cp(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +cc: Cmp) -> Bool:
  Cmp.is_lt(Word.cmp.fin(b0, False{}, Word.cmp.fin(b1, True{}, Word.cmp.fin(b2, False{},
    Word.cmp.fin(b3, True{}, cc)))))

# the four low bits of a U32 below ten, highest first
def sm.bits(
  -P: U32 -> Type,
  +b3: Bool,
  +b2: Bool,
  +b1: Bool,
  +b0: Bool,
  h: {sm.cp(b0, b1, b2, b3, EQ{}) == True{} : Bool},
  p0: P(0),
  p1: P(1),
  p2: P(2),
  p3: P(3),
  p4: P(4),
  p5: P(5),
  p6: P(6),
  p7: P(7),
  p8: P(8),
  p9: P(9)
) -> P(sm.u(b0, b1, b2, b3)):
  match b3:
    case False{}:
      match b2 b1 b0:
        case False{} False{} False{}:
          p0
        case False{} False{} True{}:
          p1
        case False{} True{} False{}:
          p2
        case False{} True{} True{}:
          p3
        case True{} False{} False{}:
          p4
        case True{} False{} True{}:
          p5
        case True{} True{} False{}:
          p6
        case True{} True{} True{}:
          p7
    case True{}:
      match b2:
        case True{}:
          Eq.bit.absurd(&1, P(sm.u(b0, b1, True{}, True{})), h)
        case False{}:
          match b1:
            case True{}:
              match b0:
                case False{}:
                  Eq.bit.absurd(&1, P(sm.u(False{}, True{}, False{}, True{})), h)
                case True{}:
                  Eq.bit.absurd(&1, P(sm.u(True{}, True{}, False{}, True{})), h)
            case False{}:
              match b0:
                case False{}:
                  p8
                case True{}:
                  p9

# the bits above the fourth are zero, or the U32 is not below ten
def sm.at(
  -P: U32 -> Type,
  cc: Cmp,
  +b3: Bool,
  +b2: Bool,
  +b1: Bool,
  +b0: Bool,
  +rest: Word(28n),
  ec: {Word.cmp(28n, rest, Eq.zw(28n)) == cc : Cmp},
  h: {sm.cp(b0, b1, b2, b3, cc) == True{} : Bool},
  p0: P(0),
  p1: P(1),
  p2: P(2),
  p3: P(3),
  p4: P(4),
  p5: P(5),
  p6: P(6),
  p7: P(7),
  p8: P(8),
  p9: P(9)
) -> P(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, rest}}}}}):
  match cc:
    case LT{}:
      Eq.bit.gone(&1, P(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, rest}}}}}),
        Eq.bit.clash2(Equal.trans(Bool, True{}, Cmp.is_lt(Word.cmp(28n, rest, Eq.zw(28n))), False{},
          Equal.sym(Bool, Cmp.is_lt(Word.cmp(28n, rest, Eq.zw(28n))), True{},
            Equal.cong(Cmp, Bool, xx => Cmp.is_lt(xx), Word.cmp(28n, rest, Eq.zw(28n)), LT{}, ec)),
          Eq.zw_nlt(28n, rest))))
    case GT{}:
      Eq.bit.absurd(&1, P(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, rest}}}}}), h)
    case EQ{}:
      er = Equal.sym(Word(28n), rest, Eq.zw(28n), Eq.word_eq(28n, rest, Eq.zw(28n), ec))
      %er : P(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, _}}}}})
      sm.bits(P, b3, b2, b1, b0, h, p0, p1, p2, p3, p4, p5, p6, p7, p8, p9)

# a claim made of each of 0 to 9 is made of every U32 below ten
def sm.elim(
  -P: U32 -> Type,
  rr: U32,
  h: {U32.is_lt(rr, 10) == True{} : Bool},
  p0: P(0),
  p1: P(1),
  p2: P(2),
  p3: P(3),
  p4: P(4),
  p5: P(5),
  p6: P(6),
  p7: P(7),
  p8: P(8),
  p9: P(9)
) -> P(rr):
  match rr:
    case U32{WCon{+b0, WCon{+b1, WCon{+b2, WCon{+b3, +rest}}}}}:
      sm.at(P, Word.cmp(28n, rest, Eq.zw(28n)), b3, b2, b1, b0, rest, {==}, h,
        p0, p1, p2, p3, p4, p5, p6, p7, p8, p9)

# The digit U32.show writes for a remainder, and what the scan and the
# classifier ask of it.

# the digit of a value below ten, as U32.show writes it
def dch(+rr: U32) -> Char:
  Chr{U32.add(48, rr)}

# a character a datetime's text keeps in a bare value, with no exponent mark
def dtc(+cc: Char) -> Bool:
  Bool.and(D1.word.char(cc), Bool.not(T.word.ee.hit(cc)))

# what the scan and the classifier ask of a digit: a digit, no colon, no dash,
# no special, a character that starts a bare value, and dtc
def df5(+cc: Char) -> Bool:
  Bool.and(D1.word.first(cc), dtc(cc))

# no special, and the rest
def df4(+cc: Char) -> Bool:
  Bool.and(Bool.not(T.word.special(cc)), df5(cc))

# no dash, and the rest
def df3(+cc: Char) -> Bool:
  Bool.and(Bool.not(Char.is_eq(cc, '-')), df4(cc))

# no colon, and the rest
def df2(+cc: Char) -> Bool:
  Bool.and(Bool.not(Char.is_eq(cc, ':')), df3(cc))

# a digit, and the rest
def dfl(+cc: Char) -> Bool:
  Bool.and(Char.is_digit(cc), df2(cc))

# a step of the digit scan, a digit value and a bit
type Dt is Data:
  Dt{acc: U32, ok: Bool, val: U32, fl: Bool}

# the digit of a remainder by ten: the scan adds its value, and the facts hold
def dd(
  +nn: U32,
  +xx: U32
) -> {Dt{T.take.acc(True{}, nn, dch(U32.mod(xx, 10))), T.take.ok(True{}, dch(U32.mod(xx, 10))),
  T.dig.val(dch(U32.mod(xx, 10))), dfl(dch(U32.mod(xx, 10)))} == Dt{U32.add(U32.mul(nn, 10), U32.mod(xx, 10)), True{},
  U32.mod(xx, 10), True{}} : Dt}:
  sm.elim(rr => {Dt{T.take.acc(True{}, nn, dch(rr)), T.take.ok(True{}, dch(rr)), T.dig.val(dch(rr)), dfl(dch(rr))}
    == Dt{U32.add(U32.mul(nn, 10), rr), True{}, rr, True{}} : Dt}, U32.mod(xx, 10), M1.md(xx),
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})
