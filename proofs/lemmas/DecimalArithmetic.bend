# ten, quotient and digit arithmetic bounds used by the document induction
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../src/arith.bend as Ar
import ./FreshNamesInRows.bend as M1
import ./PickAndDigitSteps.bend as M2

# Datetimes. render writes each field with text.pad2 or text.pad4, which pad
# U32.show with zeros; U32.show writes the remainders of repeated division by
# ten, and the scan multiplies by ten and adds them back. The arithmetic is
# src/arith.bend's, ported from ezjson: a U32 is its quotient by ten times ten
# plus its remainder, as U32s, and a U32 below ten times k has a quotient below
# k. Each digit character is one of ten, so what the scan tests of it computes.

# a Nat compares equal to itself
def ncmp.refl(xx: Nat) -> {Nat.cmp(xx, xx) == EQ{} : Cmp}:
  match xx:
    case 0n:
      {==}
    case 1n+pp:
      ncmp.refl(pp)

# the words of two U32s that compare equal
def u.inj.go(aa: U32, bb: U32, ee: {U32.cmp(aa, bb) == EQ{} : Cmp}) -> {aa == bb : U32}:
  match aa bb:
    case U32{+wa} U32{+wb}:
      Equal.cong(Word(32n), U32, ww => U32{ww}, wa, wb, Eq.word_eq(32n, wa, wb, ee))

# two U32s with one count are one U32
def u.inj(+aa: U32, +bb: U32, ee: {U32.to_nat(aa) == U32.to_nat(bb) : Nat}) -> {aa == bb : U32}:
  u.inj.go(aa, bb, Equal.trans(Cmp, U32.cmp(aa, bb), Nat.cmp(U32.to_nat(aa), U32.to_nat(bb)), EQ{},
    Ar.u_cmp(aa, bb),
    Equal.trans(Cmp, Nat.cmp(U32.to_nat(aa), U32.to_nat(bb)), Nat.cmp(U32.to_nat(bb), U32.to_nat(bb)), EQ{},
      Equal.cong(Nat, Cmp, xx => Nat.cmp(xx, U32.to_nat(bb)), U32.to_nat(aa), U32.to_nat(bb), ee),
      ncmp.refl(U32.to_nat(bb)))))

# a U32 is ten times its quotient by ten plus its remainder
def dm(+uu: Unit, +nn: U32) -> {nn == U32.add(U32.mul(U32.div(nn, 10), 10), U32.mod(nn, 10)) : U32}:
  Equal.sym(U32, U32.add(U32.mul(U32.div(nn, 10), 10), U32.mod(nn, 10)), nn,
    u.inj(U32.add(U32.mul(U32.div(nn, 10), 10), U32.mod(nn, 10)), nn,
      Ar.nat_mod_small(Ar.step_ks(U32.div(nn, 10), U32.mod(nn, 10)),
        U32.to_nat(U32.add(U32.mul(U32.div(nn, 10), 10), U32.mod(nn, 10))), U32.to_nat(nn),
        Ar.pow2u(32n, uu),
        Equal.trans(Nat, Nat.add(U32.to_nat(U32.add(U32.mul(U32.div(nn, 10), 10), U32.mod(nn, 10))),
          Nat.mul(Ar.step_ks(U32.div(nn, 10), U32.mod(nn, 10)), Ar.pow2u(32n, uu))),
          Nat.add(Nat.mul(U32.to_nat(U32.div(nn, 10)), 10n), U32.to_nat(U32.mod(nn, 10))), U32.to_nat(nn),
          Ar.step_k(uu, U32.div(nn, 10), U32.mod(nn, 10)), Ar.u_div(Unit{}, nn)),
        Ar.u_bound(uu, nn))))

# below a bound is below any bound more than it
def lt.add(
  rr: Nat,
  aa: Nat,
  +kk: Nat,
  hh: {Nat.is_lt(rr, aa) == True{} : Bool}
) -> {Nat.is_lt(rr, Nat.add(aa, kk)) == True{} : Bool}:
  match rr aa:
    case 0n 0n:
      Eq.bit.absurd(&2, {Nat.is_lt(0n, Nat.add(0n, kk)) == True{} : Bool}, hh)
    case 0n 1n+_a:
      {==}
    case 1n+r1 0n:
      Eq.bit.absurd(&2, {Nat.is_lt(1n+r1, Nat.add(0n, kk)) == True{} : Bool}, hh)
    case 1n+r1 1n+a1:
      lt.add(r1, a1, kk, hh)

# nothing is below zero
def nlt.zero(xx: Nat) -> {Nat.is_lt(xx, 0n) == False{} : Bool}:
  match xx:
    case 0n:
      {==}
    case 1n+_p:
      {==}

# ten times q plus a digit is below ten times k exactly when q is below k
def ltm(
  qq: Nat,
  kk: Nat,
  +rr: Nat,
  +hr: {Nat.is_lt(rr, 10n) == True{} : Bool}
) -> {Nat.is_lt(Nat.add(Nat.mul(qq, 10n), rr), Nat.mul(kk, 10n)) == Nat.is_lt(qq, kk) : Bool}:
  match qq kk:
    case 0n 0n:
      nlt.zero(rr)
    case 0n 1n+k1:
      lt.add(rr, 10n, Nat.mul(k1, 10n), hr)
    case 1n+_q 0n:
      {==}
    case 1n+q1 1n+k1:
      ltm(q1, k1, rr, hr)

# at most k is below one more than k
def le.lt(xx: Nat, kk: Nat) -> {Cmp.is_le(Nat.cmp(xx, kk)) == Cmp.is_lt(Nat.cmp(xx, 1n+kk)) : Bool}:
  match xx kk:
    case 0n 0n:
      {==}
    case 0n 1n+_k:
      {==}
    case 1n+x1 0n:
      Equal.sym(Bool, Cmp.is_lt(Nat.cmp(x1, 0n)), False{}, nlt.zero(x1))
    case 1n+x1 1n+k1:
      le.lt(x1, k1)

# a U32 comparison below is the Nat one
def u.lt(+aa: U32, +bb: U32) -> {U32.is_lt(aa, bb) == Nat.is_lt(U32.to_nat(aa), U32.to_nat(bb)) : Bool}:
  Equal.cong(Cmp, Bool, cc => Cmp.is_lt(cc), U32.cmp(aa, bb), Nat.cmp(U32.to_nat(aa), U32.to_nat(bb)),
    Ar.u_cmp(aa, bb))

# and at most
def u.le(+aa: U32, +bb: U32) -> {U32.is_le(aa, bb) == Cmp.is_le(Nat.cmp(U32.to_nat(aa), U32.to_nat(bb))) : Bool}:
  Equal.cong(Cmp, Bool, cc => Cmp.is_le(cc), U32.cmp(aa, bb), Nat.cmp(U32.to_nat(aa), U32.to_nat(bb)),
    Ar.u_cmp(aa, bb))

# the character of a token: TD{x} is the digit of x modulo ten
def tch(tk: M1.Tk) -> Char:
  match tk:
    case M1.TD{xx}:
      M2.dch(U32.mod(xx, 10))
    case M1.TC{cc}:
      cc

# the text of tokens
def tstr(ts: List<&2, M1.Tk>) -> String:
  match ts:
    case []:
      SNil{}
    case tk <> tt:
      SCon{tch(tk), tstr(tt)}

# a value whose quotient by ten is below ten reads back from its two digits
def v2(
  +uu: Unit,
  +nn: U32,
  hq: {U32.div(U32.div(nn, 10), 10) == 0 : U32}
) -> {U32.add(U32.mul(U32.add(U32.mul(0, 10), U32.mod(U32.div(nn, 10), 10)), 10), U32.mod(nn, 10)) == nn : U32}:
  Equal.sym(U32, nn, U32.add(U32.mul(U32.add(U32.mul(0, 10), U32.mod(U32.div(nn, 10), 10)), 10), U32.mod(nn, 10)),
    Equal.trans(U32, nn, U32.add(U32.mul(U32.div(nn, 10), 10), U32.mod(nn, 10)),
      U32.add(U32.mul(U32.add(U32.mul(0, 10), U32.mod(U32.div(nn, 10), 10)), 10), U32.mod(nn, 10)),
      dm(uu, nn),
      Equal.cong(U32, U32, zz => U32.add(U32.mul(zz, 10), U32.mod(nn, 10)), U32.div(nn, 10),
        U32.add(U32.mul(0, 10), U32.mod(U32.div(nn, 10), 10)),
        Equal.trans(U32, U32.div(nn, 10), U32.add(U32.mul(U32.div(U32.div(nn, 10), 10), 10),
          U32.mod(U32.div(nn, 10), 10)), U32.add(U32.mul(0, 10), U32.mod(U32.div(nn, 10), 10)),
          dm(uu, U32.div(nn, 10)),
          Equal.cong(U32, U32, zz => U32.add(U32.mul(zz, 10), U32.mod(U32.div(nn, 10), 10)),
            U32.div(U32.div(nn, 10), 10), 0, hq)))))

# at most k is below k and one, when k and one does not wrap
def le2lt(
  +xx: U32,
  +kk: U32,
  ez: {U32.is_zero(U32.add(kk, 1)) == False{} : Bool}
) -> {U32.is_le(xx, kk) == U32.is_lt(xx, U32.add(kk, 1)) : Bool}:
  Equal.trans(Bool, U32.is_le(xx, kk), Cmp.is_le(Nat.cmp(U32.to_nat(xx), U32.to_nat(kk))),
    U32.is_lt(xx, U32.add(kk, 1)), u.le(xx, kk),
    Equal.trans(Bool, Cmp.is_le(Nat.cmp(U32.to_nat(xx), U32.to_nat(kk))),
      Cmp.is_lt(Nat.cmp(U32.to_nat(xx), 1n+U32.to_nat(kk))), U32.is_lt(xx, U32.add(kk, 1)),
      le.lt(U32.to_nat(xx), U32.to_nat(kk)),
      Equal.trans(Bool, Cmp.is_lt(Nat.cmp(U32.to_nat(xx), 1n+U32.to_nat(kk))),
        Cmp.is_lt(Nat.cmp(U32.to_nat(xx), U32.to_nat(U32.add(kk, 1)))), U32.is_lt(xx, U32.add(kk, 1)),
        Equal.cong(Nat, Bool, nn => Cmp.is_lt(Nat.cmp(U32.to_nat(xx), nn)), 1n+U32.to_nat(kk),
          U32.to_nat(U32.add(kk, 1)), Equal.sym(Nat, U32.to_nat(U32.add(kk, 1)), 1n+U32.to_nat(kk), Eq.inc.nat(kk,
            ez))),
        Equal.sym(Bool, U32.is_lt(xx, U32.add(kk, 1)), Cmp.is_lt(Nat.cmp(U32.to_nat(xx),
          U32.to_nat(U32.add(kk, 1)))), u.lt(xx, U32.add(kk, 1))))))

# The scan of a datetime's text, field by field.

# the characters of tokens
def tl(ts: List<&2, M1.Tk>) -> List<&2, Char>:
  String.to_list(tstr(ts))

# WP-D: the document induction. render writes a table's pairs that are no
# table first, one line each, then its tables and arrays of tables, each a
# header and then the same again for its rows. parse reads each line from the
# start of a line: a key line puts its value at the head of the current
# table's rows (WP-W's walk_put_at_head), and a header makes a new table or
# a new element and makes it the current table. Every line leaves back,
# qkind, uni and left wherever its last escape put them, so the start of a
# line keeps all four as parameters.

# the scanner at the start of a line in the table he
def dl(
  rw: List<&2, T.Val>,
  hs: List<&2, String>,
  he: List<&2, String>,
  bk: T.Lex,
  qk: T.QKind,
  un: U32,
  lf: U32,
  ab: Bool
) -> T.St:
  T.St{"", rw, hs, he, [], [], T.LTop{}, bk, qk, [], T.HNone{}, un, lf, ab, False{}}

# a list made a text and back is itself
def gd.tlfl(xs: List<&2, Char>) -> {String.to_list(String.from_list(xs)) == xs : List<&2, Char>}:
  match xs:
    case []:
      {==}
    case +hh <> +tt:
      Equal.cong(List<&2, Char>, List<&2, Char>, ys => hh <> ys, String.to_list(String.from_list(tt)), tt, gd.tlfl(tt))
