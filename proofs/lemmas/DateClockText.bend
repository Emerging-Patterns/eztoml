# the text of a date and a clock, their digit counts and range bounds
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../src/arith.bend as Ar
import ../../laws/DateTimeReadExactly.bend as L1
import ../../laws/WordReadsBack.bend as L2
import ../../laws/defs/BareValueGrammar.bend as D1
import ./ControlEscapeText.bend as M1
import ./DecimalArithmetic.bend as M2
import ./FreshNamesInRows.bend as M3
import ./PickAndDigitSteps.bend as M4
import ./PrefixAndTake.bend as M5
import ./ReorderedTableNames.bend as M6

# at most a, and a below b: below b
def nle(
  xx: Nat,
  aa: Nat,
  bb: Nat,
  h1: {Cmp.is_le(Nat.cmp(xx, aa)) == True{} : Bool},
  h2: {Nat.is_lt(aa, bb) == True{} : Bool}
) -> {Nat.is_lt(xx, bb) == True{} : Bool}:
  match xx aa bb:
    case 0n _a 0n:
      Eq.bit.absurd(&2, {Nat.is_lt(0n, 0n) == True{} : Bool}, Equal.trans(Bool, False{}, Nat.is_lt(aa, 0n), True{},
        Equal.sym(Bool, Nat.is_lt(aa, 0n), False{}, M2.nlt.zero(aa)), h2))
    case 0n _a 1n+_b:
      {==}
    case 1n+x1 0n _b:
      Eq.bit.absurd(&2, {Nat.is_lt(1n+x1, bb) == True{} : Bool}, h1)
    case 1n+x1 1n+a1 0n:
      Eq.bit.absurd(&2, {Nat.is_lt(1n+x1, 0n) == True{} : Bool}, h2)
    case 1n+x1 1n+a1 1n+b1:
      nle(x1, a1, b1, h1, h2)

# zero is exactly what is below one
def nz(xx: Nat) -> {Cmp.is_eq(Nat.cmp(xx, 0n)) == Cmp.is_lt(Nat.cmp(xx, 1n)) : Bool}:
  match xx:
    case 0n:
      {==}
    case 1n+x1:
      Equal.sym(Bool, Cmp.is_lt(Nat.cmp(x1, 0n)), False{}, M2.nlt.zero(x1))

# a U32 is below ten times k exactly when its quotient by ten is below k
def lt10(
  +nn: U32,
  +kk: U32,
  +k10: U32,
  +kn: Nat,
  ek: {U32.to_nat(kk) == kn : Nat},
  ek10: {U32.to_nat(k10) == Nat.mul(kn, 10n) : Nat}
) -> {U32.is_lt(nn, k10) == U32.is_lt(U32.div(nn, 10), kk) : Bool}:
  Equal.trans(Bool, U32.is_lt(nn, k10), Nat.is_lt(U32.to_nat(nn), U32.to_nat(k10)), U32.is_lt(U32.div(nn, 10), kk),
    M2.u.lt(nn, k10),
    Equal.trans(Bool, Nat.is_lt(U32.to_nat(nn), U32.to_nat(k10)),
      Nat.is_lt(Nat.add(Nat.mul(U32.to_nat(U32.div(nn, 10)), 10n), U32.to_nat(U32.mod(nn, 10))), Nat.mul(kn, 10n)),
      U32.is_lt(U32.div(nn, 10), kk),
      Equal.trans(Bool, Nat.is_lt(U32.to_nat(nn), U32.to_nat(k10)), Nat.is_lt(U32.to_nat(nn), Nat.mul(kn, 10n)),
        Nat.is_lt(Nat.add(Nat.mul(U32.to_nat(U32.div(nn, 10)), 10n), U32.to_nat(U32.mod(nn, 10))), Nat.mul(kn, 10n)),
        Equal.cong(Nat, Bool, xx => Nat.is_lt(U32.to_nat(nn), xx), U32.to_nat(k10), Nat.mul(kn, 10n), ek10),
        Equal.cong(Nat, Bool, xx => Nat.is_lt(xx, Nat.mul(kn, 10n)), U32.to_nat(nn),
          Nat.add(Nat.mul(U32.to_nat(U32.div(nn, 10)), 10n), U32.to_nat(U32.mod(nn, 10))),
          Equal.sym(Nat, Nat.add(Nat.mul(U32.to_nat(U32.div(nn, 10)), 10n), U32.to_nat(U32.mod(nn, 10))),
            U32.to_nat(nn), Ar.u_div(Unit{}, nn)))),
      Equal.trans(Bool,
        Nat.is_lt(Nat.add(Nat.mul(U32.to_nat(U32.div(nn, 10)), 10n), U32.to_nat(U32.mod(nn, 10))), Nat.mul(kn, 10n)),
        Nat.is_lt(U32.to_nat(U32.div(nn, 10)), kn), U32.is_lt(U32.div(nn, 10), kk),
        M2.ltm(U32.to_nat(U32.div(nn, 10)), kn, U32.to_nat(U32.mod(nn, 10)), Ar.u_mod(Unit{}, nn)),
        Equal.trans(Bool, Nat.is_lt(U32.to_nat(U32.div(nn, 10)), kn),
          Nat.is_lt(U32.to_nat(U32.div(nn, 10)), U32.to_nat(kk)), U32.is_lt(U32.div(nn, 10), kk),
          Equal.cong(Nat, Bool, xx => Nat.is_lt(U32.to_nat(U32.div(nn, 10)), xx), kn, U32.to_nat(kk),
            Equal.sym(Nat, U32.to_nat(kk), kn, ek)),
          Equal.sym(Bool, U32.is_lt(U32.div(nn, 10), kk), Nat.is_lt(U32.to_nat(U32.div(nn, 10)), U32.to_nat(kk)),
            M2.u.lt(U32.div(nn, 10), kk))))))

# a U32 is zero exactly when it is below one
def zlt(+qq: U32) -> {U32.is_zero(qq) == U32.is_lt(qq, 1) : Bool}:
  Equal.trans(Bool, Cmp.is_eq(U32.cmp(qq, 0)), Cmp.is_eq(Nat.cmp(U32.to_nat(qq), 0n)), U32.is_lt(qq, 1),
    Equal.cong(Cmp, Bool, cc => Cmp.is_eq(cc), U32.cmp(qq, 0), Nat.cmp(U32.to_nat(qq), 0n), Ar.u_cmp(qq, 0)),
    Equal.trans(Bool, Cmp.is_eq(Nat.cmp(U32.to_nat(qq), 0n)), Cmp.is_lt(Nat.cmp(U32.to_nat(qq), 1n)),
      U32.is_lt(qq, 1), nz(U32.to_nat(qq)), Equal.sym(Bool, U32.is_lt(qq, 1), Cmp.is_lt(Nat.cmp(U32.to_nat(qq), 1n)),
        M2.u.lt(qq, 1))))

# a U32 is below ten exactly when its quotient by ten is zero
def qz(+nn: U32) -> {U32.is_lt(nn, 10) == U32.is_zero(U32.div(nn, 10)) : Bool}:
  Equal.trans(Bool, U32.is_lt(nn, 10), U32.is_lt(U32.div(nn, 10), 1), U32.is_zero(U32.div(nn, 10)),
    lt10(nn, 1, 10, 1n, {==}, {==}), Equal.sym(Bool, U32.is_zero(U32.div(nn, 10)), U32.is_lt(U32.div(nn, 10), 1),
      zlt(U32.div(nn, 10))))

# the scan's accumulator
def dt.acc(dt: M4.Dt) -> U32:
  match dt:
    case M4.Dt{aa, _o, _v, _f}:
      aa

# the scan's flag
def dt.ok(dt: M4.Dt) -> Bool:
  match dt:
    case M4.Dt{_a, oo, _v, _f}:
      oo

# the digit's value
def dt.val(dt: M4.Dt) -> U32:
  match dt:
    case M4.Dt{_a, _o, vv, _f}:
      vv

# the facts
def dt.fl(dt: M4.Dt) -> Bool:
  match dt:
    case M4.Dt{_a, _o, _v, ff}:
      ff

# the scan adds the digit's value
def dd.acc(
  +nn: U32,
  +xx: U32
) -> {T.take.acc(True{}, nn, M4.dch(U32.mod(xx, 10))) == U32.add(U32.mul(nn, 10), U32.mod(xx, 10)) : U32}:
  Equal.cong(M4.Dt, U32, dt => dt.acc(dt), M4.Dt{T.take.acc(True{}, nn, M4.dch(U32.mod(xx, 10))),
    T.take.ok(True{}, M4.dch(U32.mod(xx, 10))), T.dig.val(M4.dch(U32.mod(xx, 10))), M4.dfl(M4.dch(U32.mod(xx, 10)))},
    M4.Dt{U32.add(U32.mul(nn, 10), U32.mod(xx, 10)), True{}, U32.mod(xx, 10), True{}}, M4.dd(nn, xx))

# and stays well
def dd.ok(+xx: U32) -> {T.take.ok(True{}, M4.dch(U32.mod(xx, 10))) == True{} : Bool}:
  Equal.cong(M4.Dt, Bool, dt => dt.ok(dt), M4.Dt{T.take.acc(True{}, 0, M4.dch(U32.mod(xx, 10))),
    T.take.ok(True{}, M4.dch(U32.mod(xx, 10))), T.dig.val(M4.dch(U32.mod(xx, 10))), M4.dfl(M4.dch(U32.mod(xx, 10)))},
    M4.Dt{U32.add(U32.mul(0, 10), U32.mod(xx, 10)), True{}, U32.mod(xx, 10), True{}}, M4.dd(0, xx))

# the digit's value
def dd.val(+xx: U32) -> {T.dig.val(M4.dch(U32.mod(xx, 10))) == U32.mod(xx, 10) : U32}:
  Equal.cong(M4.Dt, U32, dt => dt.val(dt), M4.Dt{T.take.acc(True{}, 0, M4.dch(U32.mod(xx, 10))),
    T.take.ok(True{}, M4.dch(U32.mod(xx, 10))), T.dig.val(M4.dch(U32.mod(xx, 10))), M4.dfl(M4.dch(U32.mod(xx, 10)))},
    M4.Dt{U32.add(U32.mul(0, 10), U32.mod(xx, 10)), True{}, U32.mod(xx, 10), True{}}, M4.dd(0, xx))

# the facts hold
def dd.fl(+xx: U32) -> {M4.dfl(M4.dch(U32.mod(xx, 10))) == True{} : Bool}:
  Equal.cong(M4.Dt, Bool, dt => dt.fl(dt), M4.Dt{T.take.acc(True{}, 0, M4.dch(U32.mod(xx, 10))),
    T.take.ok(True{}, M4.dch(U32.mod(xx, 10))), T.dig.val(M4.dch(U32.mod(xx, 10))), M4.dfl(M4.dch(U32.mod(xx, 10)))},
    M4.Dt{U32.add(U32.mul(0, 10), U32.mod(xx, 10)), True{}, U32.mod(xx, 10), True{}}, M4.dd(0, xx))

# the digit of a remainder is a digit
def dd.digit(+xx: U32) -> {Char.is_digit(M4.dch(U32.mod(xx, 10))) == True{} : Bool}:
  Eq.and.left(Char.is_digit(M4.dch(U32.mod(xx, 10))), M4.df2(M4.dch(U32.mod(xx, 10))), dd.fl(xx))

# the facts after the digit test
def dd.f2(+xx: U32) -> {M4.df2(M4.dch(U32.mod(xx, 10))) == True{} : Bool}:
  Eq.and.right(Char.is_digit(M4.dch(U32.mod(xx, 10))), M4.df2(M4.dch(U32.mod(xx, 10))), dd.fl(xx))

# no colon
def dd.nocolon(+xx: U32) -> {Char.is_eq(M4.dch(U32.mod(xx, 10)), ':') == False{} : Bool}:
  Eq.not.true(Char.is_eq(M4.dch(U32.mod(xx, 10)), ':'), Eq.and.left(Bool.not(Char.is_eq(M4.dch(U32.mod(xx, 10)), ':')),
    M4.df3(M4.dch(U32.mod(xx, 10))), dd.f2(xx)))

# the facts after the colon test
def dd.f3(+xx: U32) -> {M4.df3(M4.dch(U32.mod(xx, 10))) == True{} : Bool}:
  Eq.and.right(Bool.not(Char.is_eq(M4.dch(U32.mod(xx, 10)), ':')), M4.df3(M4.dch(U32.mod(xx, 10))), dd.f2(xx))

# the facts after the dash test
def dd.f4(+xx: U32) -> {M4.df4(M4.dch(U32.mod(xx, 10))) == True{} : Bool}:
  Eq.and.right(Bool.not(Char.is_eq(M4.dch(U32.mod(xx, 10)), '-')), M4.df4(M4.dch(U32.mod(xx, 10))), dd.f3(xx))

# no special
def dd.nospec(+xx: U32) -> {T.word.special(M4.dch(U32.mod(xx, 10))) == False{} : Bool}:
  Eq.not.true(T.word.special(M4.dch(U32.mod(xx, 10))), Eq.and.left(Bool.not(T.word.special(M4.dch(U32.mod(xx, 10)))),
    M4.df5(M4.dch(U32.mod(xx, 10))), dd.f4(xx)))

# the facts after the special test
def dd.f5(+xx: U32) -> {M4.df5(M4.dch(U32.mod(xx, 10))) == True{} : Bool}:
  Eq.and.right(Bool.not(T.word.special(M4.dch(U32.mod(xx, 10)))), M4.df5(M4.dch(U32.mod(xx, 10))), dd.f4(xx))

# a character that starts a bare value
def dd.first(+xx: U32) -> {D1.word.first(M4.dch(U32.mod(xx, 10))) == True{} : Bool}:
  Eq.and.left(D1.word.first(M4.dch(U32.mod(xx, 10))), M4.dtc(M4.dch(U32.mod(xx, 10))), dd.f5(xx))

# what a datetime keeps
def dd.dtc(+xx: U32) -> {M4.dtc(M4.dch(U32.mod(xx, 10))) == True{} : Bool}:
  Eq.and.right(D1.word.first(M4.dch(U32.mod(xx, 10))), M4.dtc(M4.dch(U32.mod(xx, 10))), dd.f5(xx))

# a character a bare value keeps
def dd.char(+xx: U32) -> {D1.word.char(M4.dch(U32.mod(xx, 10))) == True{} : Bool}:
  Eq.and.left(D1.word.char(M4.dch(U32.mod(xx, 10))), Bool.not(T.word.ee.hit(M4.dch(U32.mod(xx, 10)))), dd.dtc(xx))

# no exponent mark
def dd.noe(+xx: U32) -> {T.word.ee.hit(M4.dch(U32.mod(xx, 10))) == False{} : Bool}:
  Eq.not.true(T.word.ee.hit(M4.dch(U32.mod(xx, 10))), Eq.and.right(D1.word.char(M4.dch(U32.mod(xx, 10))),
    Bool.not(T.word.ee.hit(M4.dch(U32.mod(xx, 10)))), dd.dtc(xx)))

# every character written as itself is one a datetime keeps; a digit always is
def tok(ts: List<&2, M3.Tk>) -> Bool:
  match ts:
    case []:
      True{}
    case M3.TD{_x} <> tt:
      tok(tt)
    case M3.TC{+cc} <> tt:
      Bool.and(M4.dtc(cc), tok(tt))

# the tokens' text holds no exponent mark
def tk.ee(
  ts: List<&2, M3.Tk>,
  +hh: {tok(ts) == True{} : Bool}
) -> {T.word.ee(String.to_list(M2.tstr(ts))) == False{} : Bool}:
  match ts:
    case []:
      {==}
    case M3.TD{+xx} <> +tt:
      Equal.trans(Bool, T.word.or(T.word.ee.hit(M4.dch(U32.mod(xx, 10))), T.word.ee(String.to_list(M2.tstr(tt)))),
        T.word.or(False{}, T.word.ee(String.to_list(M2.tstr(tt)))), False{},
        Equal.cong(Bool, Bool, bb => T.word.or(bb, T.word.ee(String.to_list(M2.tstr(tt)))),
          T.word.ee.hit(M4.dch(U32.mod(xx, 10))), False{}, dd.noe(xx)),
        tk.ee(tt, hh))
    case M3.TC{+cc} <> +tt:
      Equal.trans(Bool, T.word.or(T.word.ee.hit(cc), T.word.ee(String.to_list(M2.tstr(tt)))),
        T.word.or(False{}, T.word.ee(String.to_list(M2.tstr(tt)))), False{},
        Equal.cong(Bool, Bool, bb => T.word.or(bb, T.word.ee(String.to_list(M2.tstr(tt)))), T.word.ee.hit(cc), False{},
          Eq.not.true(T.word.ee.hit(cc), Eq.and.right(D1.word.char(cc), Bool.not(T.word.ee.hit(cc)),
          Eq.and.left(M4.dtc(cc), tok(tt), hh)))),
        tk.ee(tt, Eq.and.right(M4.dtc(cc), tok(tt), hh)))

# the tokens' text is characters a bare value keeps
def tk.rest(ts: List<&2, M3.Tk>, +hh: {tok(ts) == True{} : Bool}) -> {L2.word.rest(M2.tstr(ts)) == True{} : Bool}:
  match ts:
    case []:
      {==}
    case M3.TD{+xx} <> +tt:
      M5.and.tt(D1.word.char(M4.dch(U32.mod(xx, 10))), L2.word.rest(M2.tstr(tt)), dd.char(xx), tk.rest(tt, hh))
    case M3.TC{+cc} <> +tt:
      M5.and.tt(D1.word.char(cc), L2.word.rest(M2.tstr(tt)), Eq.and.left(D1.word.char(cc),
        Bool.not(T.word.ee.hit(cc)), Eq.and.left(M4.dtc(cc), tok(tt), hh)),
        tk.rest(tt, Eq.and.right(M4.dtc(cc), tok(tt), hh)))

# a U32 that is zero is 0
def zero.eq(+xx: U32, hh: {U32.is_zero(xx) == True{} : Bool}) -> {xx == 0 : U32}:
  M2.u.inj(xx, 0, Eq.u32_zero_nat(xx, hh))

# a U32 not below ten is not zero
def nzero.go(
  zz: Bool,
  +nn: U32,
  ez: {U32.is_zero(nn) == zz : Bool},
  es: {U32.is_lt(nn, 10) == False{} : Bool}
) -> {zz == False{} : Bool}:
  match zz:
    case False{}:
      {==}
    case True{}:
      Eq.bit.absurd2(&2, {True{} == False{} : Bool}, Equal.trans(Bool, True{}, U32.is_lt(nn, 10), False{},
        Equal.cong(U32, Bool, xx => U32.is_lt(xx, 10), 0, nn, Equal.sym(U32, nn, 0, zero.eq(nn, ez))), es))

# a U32 not below ten is not zero
def nzero(+nn: U32, es: {U32.is_lt(nn, 10) == False{} : Bool}) -> {U32.is_zero(nn) == False{} : Bool}:
  nzero.go(U32.is_zero(nn), nn, {==}, es)

# a U32 below one hundred has a quotient below ten
def l100(+nn: U32) -> {U32.is_lt(nn, 100) == U32.is_lt(U32.div(nn, 10), 10) : Bool}:
  lt10(nn, 10, 100, 10n, {==}, {==})

# a U32 below ten is zero after one division by ten
def q.zero(+nn: U32, hh: {U32.is_lt(nn, 10) == True{} : Bool}) -> {U32.div(nn, 10) == 0 : U32}:
  zero.eq(U32.div(nn, 10), Equal.trans(Bool, U32.is_zero(U32.div(nn, 10)), U32.is_lt(nn, 10), True{},
    Equal.sym(Bool, U32.is_lt(nn, 10), U32.is_zero(U32.div(nn, 10)), qz(nn)), hh))

# its quotient by ten is not zero when it is not below ten
def q.nz(+nn: U32, hh: {U32.is_lt(nn, 10) == False{} : Bool}) -> {U32.is_zero(U32.div(nn, 10)) == False{} : Bool}:
  Equal.trans(Bool, U32.is_zero(U32.div(nn, 10)), U32.is_lt(nn, 10), False{},
    Equal.sym(Bool, U32.is_lt(nn, 10), U32.is_zero(U32.div(nn, 10)), qz(nn)), hh)

# pad2 of a value below ten: a zero, and the value itself or the digit of 0
def p2.small(
  zz: Bool,
  +nn: U32,
  ez: {U32.is_zero(nn) == zz : Bool},
  q0: {U32.div(nn, 10) == 0 : U32}
) -> {SCon{'0', U32.show.if(nn, zz)} == M2.tstr(M3.d2(nn)) : String}:
  match zz:
    case True{}:
      %Equal.sym(U32, nn, 0, zero.eq(nn, ez)) : {SCon{'0', U32.show.if(_, True{})} == M2.tstr(M3.d2(_)) : String}
      {==}
    case False{}:
      %Equal.sym(Bool, U32.is_zero(nn), False{}, ez) :
        {SCon{'0', U32.show.fin(9n, SNil{}, nn, _)} == M2.tstr(M3.d2(nn)) : String}
      %Equal.sym(U32, U32.div(nn, 10), 0, q0) :
        {SCon{'0', U32.show.go(9n, _, SCon{Chr{U32.add(48, U32.mod(nn, 10))}, SNil{}})}
          == M2.tstr([M3.TD{_}, M3.TD{nn}]) : String}
      {==}

# pad2 by whether the value is below ten
def p2.go(
  small: Bool,
  +nn: U32,
  +es: {U32.is_lt(nn, 10) == small : Bool},
  hl: {U32.is_lt(nn, 100) == True{} : Bool}
) -> {T.pad2.go(small, nn) == M2.tstr(M3.d2(nn)) : String}:
  match small:
    case True{}:
      p2.small(U32.is_zero(nn), nn, {==}, q.zero(nn, es))
    case False{}:
      %Equal.sym(Bool, U32.is_zero(nn), False{}, nzero(nn, es)) : {U32.show.if(nn, _) == M2.tstr(M3.d2(nn)) : String}
      %Equal.sym(Bool, U32.is_zero(nn), False{}, nzero(nn, es)) :
        {U32.show.fin(9n, SNil{}, nn, _) == M2.tstr(M3.d2(nn)) : String}
      %Equal.sym(Bool, U32.is_zero(U32.div(nn, 10)), False{}, q.nz(nn, es)) :
        {U32.show.fin(8n, SCon{Chr{U32.add(48, U32.mod(nn, 10))}, SNil{}}, U32.div(nn, 10), _)
          == M2.tstr(M3.d2(nn)) : String}
      %Equal.sym(U32, U32.div(U32.div(nn, 10), 10), 0, q.zero(U32.div(nn, 10),
        Equal.trans(Bool, U32.is_lt(U32.div(nn, 10), 10), U32.is_lt(nn, 100), True{},
          Equal.sym(Bool, U32.is_lt(nn, 100), U32.is_lt(U32.div(nn, 10), 10), l100(nn)), hl))) :
        {U32.show.go(8n, _, SCon{Chr{U32.add(48, U32.mod(U32.div(nn, 10), 10))},
          SCon{Chr{U32.add(48, U32.mod(nn, 10))}, SNil{}}}) == M2.tstr(M3.d2(nn)) : String}
      {==}

# pad2 of a value below one hundred is its two digits
def pad2.eq(+nn: U32, hl: {U32.is_lt(nn, 100) == True{} : Bool}) -> {T.text.pad2(nn) == M2.tstr(M3.d2(nn)) : String}:
  p2.go(U32.is_lt(nn, 10), nn, {==}, hl)

# below a thousand is a quotient below a hundred
def l1000(+nn: U32) -> {U32.is_lt(nn, 1000) == U32.is_lt(U32.div(nn, 10), 100) : Bool}:
  lt10(nn, 100, 1000, 100n, {==}, {==})

# a U32 is below ten times k exactly when its quotient by ten is below k,
# when ten times k does not overflow
def lt10m(
  +uu: Unit,
  +nn: U32,
  +kk: U32,
  hk: {Ar.umk(kk) == 0n : Nat}
) -> {U32.is_lt(nn, U32.mul(kk, 10)) == U32.is_lt(U32.div(nn, 10), kk) : Bool}:
  lt10(nn, kk, U32.mul(kk, 10), U32.to_nat(kk), {==}, Equal.trans(Nat, U32.to_nat(U32.mul(kk, 10)),
    Nat.add(U32.to_nat(U32.mul(kk, 10)), 0n), Nat.mul(U32.to_nat(kk), 10n),
    Equal.sym(Nat, Nat.add(U32.to_nat(U32.mul(kk, 10)), 0n), U32.to_nat(U32.mul(kk, 10)),
      Ar.nat_add_zero(U32.to_nat(U32.mul(kk, 10)))),
    Equal.trans(Nat, Nat.add(U32.to_nat(U32.mul(kk, 10)), 0n),
      Nat.add(U32.to_nat(U32.mul(kk, 10)), Nat.mul(Ar.umk(kk), Ar.pow2u(32n, uu))), Nat.mul(U32.to_nat(kk), 10n),
      Equal.cong(Nat, Nat, zz => Nat.add(U32.to_nat(U32.mul(kk, 10)), Nat.mul(zz, Ar.pow2u(32n, uu))), 0n,
        Ar.umk(kk), Equal.sym(Nat, Ar.umk(kk), 0n, hk)),
      Ar.u_mul10(uu, kk))))

# below ten thousand is a quotient below a thousand
def l10000(+uu: Unit, +nn: U32) -> {U32.is_lt(nn, 10000) == U32.is_lt(U32.div(nn, 10), 1000) : Bool}:
  lt10m(uu, nn, 1000, {==})

# below a thousand is a second quotient below ten
def lq2(+yy: U32) -> {U32.is_lt(yy, 1000) == U32.is_lt(U32.div(U32.div(yy, 10), 10), 10) : Bool}:
  Equal.trans(Bool, U32.is_lt(yy, 1000), U32.is_lt(U32.div(yy, 10), 100),
    U32.is_lt(U32.div(U32.div(yy, 10), 10), 10), l1000(yy), l100(U32.div(yy, 10)))

# below ten thousand is a third quotient below ten
def lq3(
  +uu: Unit,
  +yy: U32
) -> {U32.is_lt(yy, 10000) == U32.is_lt(U32.div(U32.div(U32.div(yy, 10), 10), 10), 10) : Bool}:
  Equal.trans(Bool, U32.is_lt(yy, 10000), U32.is_lt(U32.div(yy, 10), 1000),
    U32.is_lt(U32.div(U32.div(U32.div(yy, 10), 10), 10), 10), l10000(uu, yy),
    Equal.trans(Bool, U32.is_lt(U32.div(yy, 10), 1000), U32.is_lt(U32.div(U32.div(yy, 10), 10), 100),
      U32.is_lt(U32.div(U32.div(U32.div(yy, 10), 10), 10), 10), l1000(U32.div(yy, 10)),
      l100(U32.div(U32.div(yy, 10), 10))))

# pad4 of a value below ten: three zeros, and the value or the digit of 0
def p4.small(
  zz: Bool,
  +yy: U32,
  ez: {U32.is_zero(yy) == zz : Bool},
  q0: {U32.div(yy, 10) == 0 : U32}
) -> {SCon{'0', SCon{'0', SCon{'0', U32.show.if(yy, zz)}}} == M2.tstr(M3.d4(yy)) : String}:
  match zz:
    case True{}:
      %Equal.sym(U32, yy, 0, zero.eq(yy, ez)) :
        {SCon{'0', SCon{'0', SCon{'0', U32.show.if(_, True{})}}} == M2.tstr(M3.d4(_)) : String}
      {==}
    case False{}:
      %Equal.sym(Bool, U32.is_zero(yy), False{}, ez) :
        {SCon{'0', SCon{'0', SCon{'0', U32.show.fin(9n, SNil{}, yy, _)}}} == M2.tstr(M3.d4(yy)) : String}
      %Equal.sym(U32, U32.div(yy, 10), 0, q0) :
        {SCon{'0', SCon{'0', SCon{'0', U32.show.go(9n, _, SCon{Chr{U32.add(48, U32.mod(yy, 10))}, SNil{}})}}}
          == M2.tstr([M3.TD{U32.div(U32.div(_, 10), 10)}, M3.TD{U32.div(_, 10)}, M3.TD{_}, M3.TD{yy}]) : String}
      {==}

# pad4 of a value from 10 to 99
def p4.mid(
  +yy: U32,
  +es: {U32.is_lt(yy, 10) == False{} : Bool},
  em: {U32.is_lt(yy, 100) == True{} : Bool}
) -> {SCon{'0', SCon{'0', U32.show(yy)}} == M2.tstr(M3.d4(yy)) : String}:
  %Equal.sym(Bool, U32.is_zero(yy), False{}, nzero(yy, es)) :
    {SCon{'0', SCon{'0', U32.show.if(yy, _)}} == M2.tstr(M3.d4(yy)) : String}
  %Equal.sym(Bool, U32.is_zero(yy), False{}, nzero(yy, es)) :
    {SCon{'0', SCon{'0', U32.show.fin(9n, SNil{}, yy, _)}} == M2.tstr(M3.d4(yy)) : String}
  %Equal.sym(Bool, U32.is_zero(U32.div(yy, 10)), False{}, q.nz(yy, es)) :
    {SCon{'0', SCon{'0', U32.show.fin(8n, SCon{Chr{U32.add(48, U32.mod(yy, 10))}, SNil{}}, U32.div(yy, 10), _)}}
      == M2.tstr(M3.d4(yy)) : String}
  %Equal.sym(U32, U32.div(U32.div(yy, 10), 10), 0, q.zero(U32.div(yy, 10), M3.bt(U32.is_lt(yy, 100),
    U32.is_lt(U32.div(yy, 10), 10), True{}, l100(yy), em))) :
    {SCon{'0', SCon{'0', U32.show.go(8n, _, SCon{Chr{U32.add(48, U32.mod(U32.div(yy, 10), 10))},
      SCon{Chr{U32.add(48, U32.mod(yy, 10))}, SNil{}}})}}
      == M2.tstr([M3.TD{U32.div(_, 10)}, M3.TD{_}, M3.TD{U32.div(yy, 10)}, M3.TD{yy}]) : String}
  {==}

# pad4 of a value from 100 to 999
def p4.big(
  +yy: U32,
  +es: {U32.is_lt(yy, 10) == False{} : Bool},
  +em: {U32.is_lt(yy, 100) == False{} : Bool},
  eb: {U32.is_lt(yy, 1000) == True{} : Bool}
) -> {SCon{'0', U32.show(yy)} == M2.tstr(M3.d4(yy)) : String}:
  %Equal.sym(Bool, U32.is_zero(yy), False{}, nzero(yy, es)) : {SCon{'0', U32.show.if(yy,
      _)} == M2.tstr(M3.d4(yy)) : String}
  %Equal.sym(Bool, U32.is_zero(yy), False{}, nzero(yy, es)) :
    {SCon{'0', U32.show.fin(9n, SNil{}, yy, _)} == M2.tstr(M3.d4(yy)) : String}
  %Equal.sym(Bool, U32.is_zero(U32.div(yy, 10)), False{}, q.nz(yy, es)) :
    {SCon{'0', U32.show.fin(8n, SCon{Chr{U32.add(48, U32.mod(yy, 10))}, SNil{}}, U32.div(yy, 10), _)}
      == M2.tstr(M3.d4(yy)) : String}
  %Equal.sym(Bool, U32.is_zero(U32.div(U32.div(yy, 10), 10)), False{}, q.nz(U32.div(yy, 10),
    M3.bt(U32.is_lt(yy, 100), U32.is_lt(U32.div(yy, 10), 10), False{}, l100(yy), em))) :
    {SCon{'0', U32.show.fin(7n, SCon{Chr{U32.add(48, U32.mod(U32.div(yy, 10), 10))},
      SCon{Chr{U32.add(48, U32.mod(yy, 10))}, SNil{}}}, U32.div(U32.div(yy, 10), 10),
          _)} == M2.tstr(M3.d4(yy)) : String}
  %Equal.sym(U32, U32.div(U32.div(U32.div(yy, 10), 10), 10), 0, q.zero(U32.div(U32.div(yy, 10), 10),
    M3.bt(U32.is_lt(yy, 1000), U32.is_lt(U32.div(U32.div(yy, 10), 10), 10), True{}, lq2(yy), eb))) :
    {SCon{'0', U32.show.go(7n, _, SCon{Chr{U32.add(48, U32.mod(U32.div(U32.div(yy, 10), 10), 10))},
      SCon{Chr{U32.add(48, U32.mod(U32.div(yy, 10), 10))}, SCon{Chr{U32.add(48, U32.mod(yy, 10))}, SNil{}}}})}
      == M2.tstr([M3.TD{_}, M3.TD{U32.div(U32.div(yy, 10), 10)}, M3.TD{U32.div(yy, 10)}, M3.TD{yy}]) : String}
  {==}

# pad4 of a value from 1000 to 9999
def p4.full(
  +uu: Unit,
  +yy: U32,
  +es: {U32.is_lt(yy, 10) == False{} : Bool},
  +em: {U32.is_lt(yy, 100) == False{} : Bool},
  +eb: {U32.is_lt(yy, 1000) == False{} : Bool},
  hl: {U32.is_lt(yy, 10000) == True{} : Bool}
) -> {U32.show(yy) == M2.tstr(M3.d4(yy)) : String}:
  %Equal.sym(Bool, U32.is_zero(yy), False{}, nzero(yy, es)) : {U32.show.if(yy, _) == M2.tstr(M3.d4(yy)) : String}
  %Equal.sym(Bool, U32.is_zero(yy), False{}, nzero(yy, es)) :
    {U32.show.fin(9n, SNil{}, yy, _) == M2.tstr(M3.d4(yy)) : String}
  %Equal.sym(Bool, U32.is_zero(U32.div(yy, 10)), False{}, q.nz(yy, es)) :
    {U32.show.fin(8n, SCon{Chr{U32.add(48, U32.mod(yy, 10))}, SNil{}}, U32.div(yy, 10),
        _) == M2.tstr(M3.d4(yy)) : String}
  %Equal.sym(Bool, U32.is_zero(U32.div(U32.div(yy, 10), 10)), False{}, q.nz(U32.div(yy, 10),
    M3.bt(U32.is_lt(yy, 100), U32.is_lt(U32.div(yy, 10), 10), False{}, l100(yy), em))) :
    {U32.show.fin(7n, SCon{Chr{U32.add(48, U32.mod(U32.div(yy, 10), 10))},
      SCon{Chr{U32.add(48, U32.mod(yy, 10))}, SNil{}}}, U32.div(U32.div(yy, 10), 10), _) == M2.tstr(M3.d4(yy)) : String}
  %Equal.sym(Bool, U32.is_zero(U32.div(U32.div(U32.div(yy, 10), 10), 10)), False{},
    q.nz(U32.div(U32.div(yy, 10), 10), M3.bt(U32.is_lt(yy, 1000), U32.is_lt(U32.div(U32.div(yy, 10), 10), 10), False{},
    lq2(yy), eb))) :
    {U32.show.fin(6n, SCon{Chr{U32.add(48, U32.mod(U32.div(U32.div(yy, 10), 10), 10))},
      SCon{Chr{U32.add(48, U32.mod(U32.div(yy, 10), 10))}, SCon{Chr{U32.add(48, U32.mod(yy, 10))}, SNil{}}}},
      U32.div(U32.div(U32.div(yy, 10), 10), 10), _) == M2.tstr(M3.d4(yy)) : String}
  %Equal.sym(U32, U32.div(U32.div(U32.div(U32.div(yy, 10), 10), 10), 10), 0,
    q.zero(U32.div(U32.div(U32.div(yy, 10), 10), 10), M3.bt(U32.is_lt(yy, 10000),
    U32.is_lt(U32.div(U32.div(U32.div(yy, 10), 10), 10), 10), True{}, lq3(uu, yy), hl))) :
    {U32.show.go(6n, _, SCon{Chr{U32.add(48, U32.mod(U32.div(U32.div(U32.div(yy, 10), 10), 10), 10))},
      SCon{Chr{U32.add(48, U32.mod(U32.div(U32.div(yy, 10), 10), 10))},
      SCon{Chr{U32.add(48, U32.mod(U32.div(yy, 10), 10))}, SCon{Chr{U32.add(48, U32.mod(yy, 10))}, SNil{}}}}})
      == M2.tstr(M3.d4(yy)) : String}
  {==}

# pad4 by its three tests
def p4.go(
  small: Bool,
  mid: Bool,
  big: Bool,
  +uu: Unit,
  +yy: U32,
  +es: {U32.is_lt(yy, 10) == small : Bool},
  em: {U32.is_lt(yy, 100) == mid : Bool},
  eb: {U32.is_lt(yy, 1000) == big : Bool},
  hl: {U32.is_lt(yy, 10000) == True{} : Bool}
) -> {T.pad4.go(yy, small, mid, big) == M2.tstr(M3.d4(yy)) : String}:
  match small:
    case True{}:
      p4.small(U32.is_zero(yy), yy, {==}, q.zero(yy, es))
    case False{}:
      match mid:
        case True{}:
          p4.mid(yy, es, em)
        case False{}:
          match big:
            case True{}:
              p4.big(yy, es, em, eb)
            case False{}:
              p4.full(uu, yy, es, em, eb, hl)

# pad4 of a value below ten thousand is its four digits
def pad4.eq(
  +uu: Unit,
  +yy: U32,
  hl: {U32.is_lt(yy, 10000) == True{} : Bool}
) -> {T.text.pad4(yy) == M2.tstr(M3.d4(yy)) : String}:
  p4.go(U32.is_lt(yy, 10), U32.is_lt(yy, 100), U32.is_lt(yy, 1000), uu, yy, {==}, {==}, {==}, hl)

# the digit of a remainder by ten
def dx(+xx: U32) -> Char:
  M4.dch(U32.mod(xx, 10))

# the digit scan takes the digit of a remainder and adds it
def tk1(
  kk: Nat,
  +xx: U32,
  tt: List<&2, Char>,
  +nn: U32
) -> {T.take.n(1n+kk, dx(xx) <> tt, nn, True{}) == T.take.n(kk, tt, U32.add(U32.mul(nn, 10), U32.mod(xx, 10)), True{}) :
  T.Dig}:
  Equal.trans(T.Dig, T.take.n(kk, tt, T.take.acc(True{}, nn, dx(xx)), T.take.ok(True{}, dx(xx))),
    T.take.n(kk, tt, U32.add(U32.mul(nn, 10), U32.mod(xx, 10)), T.take.ok(True{}, dx(xx))),
    T.take.n(kk, tt, U32.add(U32.mul(nn, 10), U32.mod(xx, 10)), True{}),
    Equal.cong(U32, T.Dig, aa => T.take.n(kk, tt, aa, T.take.ok(True{}, dx(xx))), T.take.acc(True{}, nn, dx(xx)),
      U32.add(U32.mul(nn, 10), U32.mod(xx, 10)), dd.acc(nn, xx)),
    Equal.cong(Bool, T.Dig, bb => T.take.n(kk, tt, U32.add(U32.mul(nn, 10), U32.mod(xx, 10)), bb),
      T.take.ok(True{}, dx(xx)), True{}, dd.ok(xx)))

# two digits of remainders, taken as a two-digit field
def tk2(
  +x1: U32,
  +x2: U32,
  +tt: List<&2, Char>
) -> {T.take.n(2n, dx(x1) <> dx(x2) <> tt, 0, True{}) == T.DigOk{U32.add(U32.mul(U32.add(U32.mul(0, 10), U32.mod(x1,
  10)), 10), U32.mod(x2, 10)), tt} : T.Dig}:
  Equal.trans(T.Dig, T.take.n(2n, dx(x1) <> dx(x2) <> tt, 0, True{}),
    T.take.n(1n, dx(x2) <> tt, U32.add(U32.mul(0, 10), U32.mod(x1, 10)), True{}),
    T.DigOk{U32.add(U32.mul(U32.add(U32.mul(0, 10), U32.mod(x1, 10)), 10), U32.mod(x2, 10)), tt},
    tk1(1n, x1, dx(x2) <> tt, 0), tk1(0n, x2, tt, U32.add(U32.mul(0, 10), U32.mod(x1, 10))))

# a value below one hundred reads back from its two digits
def v2.lt(
  +uu: Unit,
  +nn: U32,
  hl: {U32.is_lt(nn, 100) == True{} : Bool}
) -> {U32.add(U32.mul(U32.add(U32.mul(0, 10), U32.mod(U32.div(nn, 10), 10)), 10), U32.mod(nn, 10)) == nn : U32}:
  M2.v2(uu, nn, q.zero(U32.div(nn, 10), M3.bt(U32.is_lt(nn, 100), U32.is_lt(U32.div(nn, 10), 10), True{}, l100(nn),
      hl)))

# a value below ten thousand reads back from its four digits, as the year's
# scan takes them: two, then one, then one
def v4(
  +uu: Unit,
  +yy: U32,
  hl: {U32.is_lt(yy, 10000) == True{} : Bool}
) -> {U32.add(U32.mul(U32.add(U32.mul(U32.add(U32.mul(U32.add(U32.mul(0, 10), U32.mod(U32.div(U32.div(U32.div(yy, 10),
  10), 10), 10)), 10), U32.mod(U32.div(U32.div(yy, 10), 10), 10)), 10), U32.mod(U32.div(yy, 10), 10)), 10), U32.mod(yy,
  10)) == yy : U32}:
  Equal.sym(U32, yy, U32.add(U32.mul(U32.add(U32.mul(U32.add(U32.mul(U32.add(U32.mul(0, 10),
    U32.mod(U32.div(U32.div(U32.div(yy, 10), 10), 10), 10)), 10), U32.mod(U32.div(U32.div(yy, 10), 10), 10)), 10),
    U32.mod(U32.div(yy, 10), 10)), 10), U32.mod(yy, 10)),
    Equal.trans(U32, yy, U32.add(U32.mul(U32.div(yy, 10), 10), U32.mod(yy, 10)),
      U32.add(U32.mul(U32.add(U32.mul(U32.add(U32.mul(U32.add(U32.mul(0, 10),
        U32.mod(U32.div(U32.div(U32.div(yy, 10), 10), 10), 10)), 10), U32.mod(U32.div(U32.div(yy, 10), 10), 10)), 10),
        U32.mod(U32.div(yy, 10), 10)), 10), U32.mod(yy, 10)),
      M2.dm(uu, yy),
      Equal.cong(U32, U32, zz => U32.add(U32.mul(zz, 10), U32.mod(yy, 10)), U32.div(yy, 10),
        U32.add(U32.mul(U32.add(U32.mul(U32.add(U32.mul(0, 10), U32.mod(U32.div(U32.div(U32.div(yy, 10), 10), 10), 10)),
          10), U32.mod(U32.div(U32.div(yy, 10), 10), 10)), 10), U32.mod(U32.div(yy, 10), 10)),
        Equal.trans(U32, U32.div(yy, 10), U32.add(U32.mul(U32.div(U32.div(yy, 10), 10), 10), U32.mod(U32.div(yy, 10),
          10)),
          U32.add(U32.mul(U32.add(U32.mul(U32.add(U32.mul(0, 10), U32.mod(U32.div(U32.div(U32.div(yy, 10), 10), 10),
            10)), 10), U32.mod(U32.div(U32.div(yy, 10), 10), 10)), 10), U32.mod(U32.div(yy, 10), 10)),
          M2.dm(uu, U32.div(yy, 10)),
          Equal.cong(U32, U32, zz => U32.add(U32.mul(zz, 10), U32.mod(U32.div(yy, 10), 10)),
            U32.div(U32.div(yy, 10), 10), U32.add(U32.mul(U32.add(U32.mul(0, 10),
            U32.mod(U32.div(U32.div(U32.div(yy, 10), 10), 10), 10)), 10), U32.mod(U32.div(U32.div(yy, 10), 10), 10)),
            Equal.sym(U32, U32.add(U32.mul(U32.add(U32.mul(0, 10), U32.mod(U32.div(U32.div(U32.div(yy, 10), 10), 10),
              10)), 10), U32.mod(U32.div(U32.div(yy, 10), 10), 10)), U32.div(U32.div(yy, 10), 10),
              M2.v2(uu, U32.div(U32.div(yy, 10), 10), q.zero(U32.div(U32.div(U32.div(yy, 10), 10), 10),
              M3.bt(U32.is_lt(yy, 10000), U32.is_lt(U32.div(U32.div(U32.div(yy, 10), 10), 10), 10), True{},
              lq3(uu, yy), hl)))))))))

# the tokens of a date, then more
def tdate(+yy: U32, +mo: U32, +dd: U32, rest: List<&2, M3.Tk>) -> List<&2, M3.Tk>:
  M3.TD{M6.dq(M6.dq(M6.dq(yy)))} <> M3.TD{M6.dq(M6.dq(yy))} <> M3.TD{M6.dq(yy)} <> M3.TD{yy} <> M3.TC{'-'} <>
    M3.TD{M6.dq(mo)} <> M3.TD{mo} <> M3.TC{'-'} <>
    M3.TD{M6.dq(dd)} <> M3.TD{dd} <> rest

# the tokens of a time of day, then more
def tclock(+hh: U32, +mi: U32, +ss: U32, rest: List<&2, M3.Tk>) -> List<&2, M3.Tk>:
  M3.TD{M6.dq(hh)} <> M3.TD{hh} <> M3.TC{':'} <> M3.TD{M6.dq(mi)} <> M3.TD{mi} <> M3.TC{':'} <> M3.TD{M6.dq(ss)} <>
    M3.TD{ss} <> rest

# the characters of a text as tokens, then more
def tcs(ss: String, rest: List<&2, M3.Tk>) -> List<&2, M3.Tk>:
  match ss:
    case SNil{}:
      rest
    case SCon{cc, tt}:
      M3.TC{cc} <> tcs(tt, rest)

# the tokens of a fraction: nothing, or a dot and its digits
def tfr(ss: String, rest: List<&2, M3.Tk>) -> List<&2, M3.Tk>:
  match ss:
    case SNil{}:
      rest
    case SCon{cc, tt}:
      M3.TC{'.'} <> tcs(SCon{cc, tt}, rest)

# the character of a zone offset's sign
def zmark(sg: T.Sign) -> Char:
  match sg:
    case T.Plus{}:
      '+'
    case T.Minus{}:
      '-'

# the tokens of a zone
def tzone(zz: T.Zone) -> List<&2, M3.Tk>:
  match zz:
    case T.Zulu{}:
      [M3.TC{'Z'}]
    case T.Shift{sg, +hh, +mi}:
      M3.TC{zmark(sg)} <> M3.TD{M6.dq(hh)} <> M3.TD{hh} <> M3.TC{':'} <> M3.TD{M6.dq(mi)} <> M3.TD{mi} <> []

# the tokens of a datetime
def tks(ww: T.When) -> List<&2, M3.Tk>:
  match ww:
    case T.WOff{T.Date{yy, mo, dd}, T.Clock{hh, mi, ss, fr}, zz}:
      tdate(yy, mo, dd, M3.TC{'T'} <> tclock(hh, mi, ss, tfr(fr, tzone(zz))))
    case T.WLocal{T.Date{yy, mo, dd}, T.Clock{hh, mi, ss, fr}}:
      tdate(yy, mo, dd, M3.TC{'T'} <> tclock(hh, mi, ss, tfr(fr, [])))
    case T.WDate{T.Date{yy, mo, dd}}:
      tdate(yy, mo, dd, [])
    case T.WTime{T.Clock{hh, mi, ss, fr}}:
      tclock(hh, mi, ss, tfr(fr, []))

# a text, then tokens, is the text's tokens then those
def tcs.eq(ss: String, rest: List<&2, M3.Tk>) -> {String.append(ss, M2.tstr(rest)) == M2.tstr(tcs(ss, rest)) : String}:
  match ss:
    case SNil{}:
      {==}
    case SCon{+cc, tt}:
      Equal.cong(String, String, zz => SCon{cc, zz}, String.append(tt, M2.tstr(rest)), M2.tstr(tcs(tt, rest)),
        tcs.eq(tt, rest))

# the fraction clock.text writes, then tokens
def fr.eq(
  ss: String,
  rest: List<&2, M3.Tk>
) -> {String.append(T.clock.frac(ss), M2.tstr(rest)) == M2.tstr(tfr(ss, rest)) : String}:
  match ss:
    case SNil{}:
      {==}
    case SCon{+cc, +tt}:
      Equal.cong(String, String, zz => SCon{'.', zz}, String.append(SCon{cc, tt}, M2.tstr(rest)),
        M2.tstr(tcs(SCon{cc, tt}, rest)), tcs.eq(SCon{cc, tt}, rest))

# the text of a date
def date.eq(
  +uu: Unit,
  +yy: U32,
  +mo: U32,
  +dd: U32,
  hy: {U32.is_lt(yy, 10000) == True{} : Bool},
  hm: {U32.is_lt(mo, 100) == True{} : Bool},
  hd: {U32.is_lt(dd, 100) == True{} : Bool}
) -> {T.date.text(T.Date{yy, mo, dd}) == M2.tstr(tdate(yy, mo, dd, [])) : String}:
  Equal.trans(String, T.text.pad4(yy) ++ "-" ++ T.text.pad2(mo) ++ "-" ++ T.text.pad2(dd),
    M2.tstr(M3.d4(yy)) ++ "-" ++ T.text.pad2(mo) ++ "-" ++ T.text.pad2(dd), M2.tstr(tdate(yy, mo, dd, [])),
    Equal.cong(String, String, zz => zz ++ "-" ++ T.text.pad2(mo) ++ "-" ++ T.text.pad2(dd), T.text.pad4(yy),
      M2.tstr(M3.d4(yy)), pad4.eq(uu, yy, hy)),
    Equal.trans(String, M2.tstr(M3.d4(yy)) ++ "-" ++ T.text.pad2(mo) ++ "-" ++ T.text.pad2(dd),
      M2.tstr(M3.d4(yy)) ++ "-" ++ M2.tstr(M3.d2(mo)) ++ "-" ++ T.text.pad2(dd), M2.tstr(tdate(yy, mo, dd, [])),
      Equal.cong(String, String, zz => M2.tstr(M3.d4(yy)) ++ "-" ++ zz ++ "-" ++ T.text.pad2(dd), T.text.pad2(mo),
        M2.tstr(M3.d2(mo)), pad2.eq(mo, hm)),
      Equal.cong(String, String, zz => M2.tstr(M3.d4(yy)) ++ "-" ++ M2.tstr(M3.d2(mo)) ++ "-" ++ zz, T.text.pad2(dd),
        M2.tstr(M3.d2(dd)), pad2.eq(dd, hd))))

# the text of a time of day, before its fraction
def clock.eq(
  +hh: U32,
  +mi: U32,
  +ss: U32,
  +fr: String,
  h1: {U32.is_lt(hh, 100) == True{} : Bool},
  h2: {U32.is_lt(mi, 100) == True{} : Bool},
  h3: {U32.is_lt(ss, 100) == True{} : Bool}
) -> {T.clock.text(T.Clock{hh, mi, ss, fr}) == String.append(M2.tstr(tclock(hh, mi, ss, [])),
    T.clock.frac(fr)) : String}:
  Equal.trans(String, T.text.pad2(hh) ++ ":" ++ T.text.pad2(mi) ++ ":" ++ T.text.pad2(ss) ++ T.clock.frac(fr),
    M2.tstr(M3.d2(hh)) ++ ":" ++ T.text.pad2(mi) ++ ":" ++ T.text.pad2(ss) ++ T.clock.frac(fr),
    String.append(M2.tstr(tclock(hh, mi, ss, [])), T.clock.frac(fr)),
    Equal.cong(String, String, zz => zz ++ ":" ++ T.text.pad2(mi) ++ ":" ++ T.text.pad2(ss) ++ T.clock.frac(fr),
      T.text.pad2(hh), M2.tstr(M3.d2(hh)), pad2.eq(hh, h1)),
    Equal.trans(String, M2.tstr(M3.d2(hh)) ++ ":" ++ T.text.pad2(mi) ++ ":" ++ T.text.pad2(ss) ++ T.clock.frac(fr),
      M2.tstr(M3.d2(hh)) ++ ":" ++ M2.tstr(M3.d2(mi)) ++ ":" ++ T.text.pad2(ss) ++ T.clock.frac(fr),
      String.append(M2.tstr(tclock(hh, mi, ss, [])), T.clock.frac(fr)),
      Equal.cong(String, String, zz => M2.tstr(M3.d2(hh)) ++ ":" ++ zz ++ ":" ++ T.text.pad2(ss) ++ T.clock.frac(fr),
        T.text.pad2(mi), M2.tstr(M3.d2(mi)), pad2.eq(mi, h2)),
      Equal.cong(String, String, zz => M2.tstr(M3.d2(hh)) ++ ":" ++ M2.tstr(M3.d2(mi)) ++ ":" ++ zz ++ T.clock.frac(fr),
        T.text.pad2(ss), M2.tstr(M3.d2(ss)), pad2.eq(ss, h3))))

# a zone's hour, 0 for Z
def zh(zz: T.Zone) -> U32:
  match zz:
    case T.Zulu{}:
      0
    case T.Shift{_s, hh, _m}:
      hh

# a zone's minute, 0 for Z
def zm(zz: T.Zone) -> U32:
  match zz:
    case T.Zulu{}:
      0
    case T.Shift{_s, _h, mi}:
      mi

# the sign written as its character
def zone.mark.eq(
  sg: T.Sign,
  +hh: U32,
  +mi: U32
) -> {T.zone.mark(sg) ++ M2.tstr(M3.d2(hh)) ++ ":" ++ M2.tstr(M3.d2(mi)) == M2.tstr(tzone(T.Shift{sg, hh,
    mi})) : String}:
  match sg:
    case T.Plus{}:
      {==}
    case T.Minus{}:
      {==}

# the text of a zone
def zone.eq(
  zz: T.Zone,
  +hz: {Bool.and(U32.is_lt(zh(zz), 100), U32.is_lt(zm(zz), 100)) == True{} : Bool}
) -> {T.zone.text(zz) == M2.tstr(tzone(zz)) : String}:
  match zz:
    case T.Zulu{}:
      {==}
    case T.Shift{sg, +hh, +mi}:
      Equal.trans(String, T.zone.mark(sg) ++ T.text.pad2(hh) ++ ":" ++ T.text.pad2(mi),
        T.zone.mark(sg) ++ M2.tstr(M3.d2(hh)) ++ ":" ++ T.text.pad2(mi), M2.tstr(tzone(T.Shift{sg, hh, mi})),
        Equal.cong(String, String, xx => T.zone.mark(sg) ++ xx ++ ":" ++ T.text.pad2(mi), T.text.pad2(hh),
          M2.tstr(M3.d2(hh)), pad2.eq(hh, Eq.and.left(U32.is_lt(hh, 100), U32.is_lt(mi, 100), hz))),
        Equal.trans(String, T.zone.mark(sg) ++ M2.tstr(M3.d2(hh)) ++ ":" ++ T.text.pad2(mi),
          T.zone.mark(sg) ++ M2.tstr(M3.d2(hh)) ++ ":" ++ M2.tstr(M3.d2(mi)), M2.tstr(tzone(T.Shift{sg, hh, mi})),
          Equal.cong(String, String, xx => T.zone.mark(sg) ++ M2.tstr(M3.d2(hh)) ++ ":" ++ xx, T.text.pad2(mi),
            M2.tstr(M3.d2(mi)), pad2.eq(mi, Eq.and.right(U32.is_lt(hh, 100), U32.is_lt(mi, 100), hz))),
          zone.mark.eq(sg, hh, mi)))

# at most a bound below one hundred is below one hundred
def lt100(
  +xx: U32,
  +kk: U32,
  hh: {U32.is_le(xx, kk) == True{} : Bool},
  hk: {Nat.is_lt(U32.to_nat(kk), 100n) == True{} : Bool}
) -> {U32.is_lt(xx, 100) == True{} : Bool}:
  Equal.trans(Bool, U32.is_lt(xx, 100), Nat.is_lt(U32.to_nat(xx), 100n), True{}, M2.u.lt(xx, 100),
    nle(U32.to_nat(xx), U32.to_nat(kk), 100n, Equal.trans(Bool, Cmp.is_le(Nat.cmp(U32.to_nat(xx), U32.to_nat(kk))),
      U32.is_le(xx, kk), True{}, Equal.sym(Bool, U32.is_le(xx, kk), Cmp.is_le(Nat.cmp(U32.to_nat(xx),
      U32.to_nat(kk))), M2.u.le(xx, kk)), hh), hk))

# February has fewer than one hundred days
def dl.feb(
  four: Bool,
  hundred: Bool,
  fh: Bool
) -> {Nat.is_lt(U32.to_nat(T.when.feb.go(four, hundred, fh)), 100n) == True{} : Bool}:
  match four hundred fh:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} _f:
      {==}
    case False{} _h _f:
      {==}

# every month has fewer than one hundred days
def dl.go(
  feb: Bool,
  short: Bool,
  +yy: U32
) -> {Nat.is_lt(U32.to_nat(T.when.days.go(feb, short, yy)), 100n) == True{} : Bool}:
  match feb:
    case True{}:
      dl.feb(U32.is_eq(U32.mod(yy, 4), 0), U32.is_eq(U32.mod(yy, 100), 0), U32.is_eq(U32.mod(yy, 400), 0))
    case False{}:
      match short:
        case True{}:
          {==}
        case False{}:
          {==}

# every month has fewer than one hundred days
def days.lt(+yy: U32, +mo: U32) -> {Nat.is_lt(U32.to_nat(T.when.days(yy, mo)), 100n) == True{} : Bool}:
  dl.go(U32.is_eq(mo, 2), T.when.short(mo), yy)

# nothing is below zero, as a comparison
def ge0n(nn: Nat) -> {Cmp.is_ge(Nat.cmp(nn, 0n)) == True{} : Bool}:
  match nn:
    case 0n:
      {==}
    case 1n+_p:
      {==}

# every U32 is at least 0
def ge0(+xx: U32) -> {U32.is_ge(xx, 0) == True{} : Bool}:
  Equal.trans(Bool, U32.is_ge(xx, 0), Cmp.is_ge(Nat.cmp(U32.to_nat(xx), 0n)), True{},
    Equal.cong(Cmp, Bool, cc => Cmp.is_ge(cc), U32.cmp(xx, 0), Nat.cmp(U32.to_nat(xx), 0n), Ar.u_cmp(xx, 0)),
    ge0n(U32.to_nat(xx)))

# at most hi is in the range from 0 to hi
def rng0(+xx: U32, +hi: U32, hh: {U32.is_le(xx, hi) == True{} : Bool}) -> {T.bound.rng(xx, 0, hi) == True{} : Bool}:
  M5.and.tt(U32.is_ge(xx, 0), U32.is_le(xx, hi), ge0(xx), hh)

# the upper half of a range
def rng.le(
  +xx: U32,
  +lo: U32,
  +hi: U32,
  hh: {T.bound.rng(xx, lo, hi) == True{} : Bool}
) -> {U32.is_le(xx, hi) == True{} : Bool}:
  Eq.and.right(U32.is_ge(xx, lo), U32.is_le(xx, hi), hh)

# a well-formed date's year is below ten thousand
def wd.y(
  +yy: U32,
  +mo: U32,
  +dd: U32,
  +hw: {T.wf.date(T.Date{yy, mo, dd}) == True{} : Bool}
) -> {U32.is_lt(yy, 10000) == True{} : Bool}:
  Equal.trans(Bool, U32.is_lt(yy, U32.add(9999, 1)), U32.is_le(yy, 9999), True{},
    Equal.sym(Bool, U32.is_le(yy, 9999), U32.is_lt(yy, U32.add(9999, 1)), M2.le2lt(yy, 9999, {==})),
    Eq.and.left(U32.is_le(yy, 9999), Bool.and(T.bound.rng(mo, 1, 12), T.bound.rng(dd, 1, T.when.days(yy, mo))), hw))

# a well-formed date's month and day ranges
def wd.md(
  +yy: U32,
  +mo: U32,
  +dd: U32,
  +hw: {T.wf.date(T.Date{yy, mo, dd}) == True{} : Bool}
) -> {Bool.and( T.bound.rng(mo, 1, 12), T.bound.rng(dd, 1, T.when.days(yy, mo))) == True{} : Bool}:
  Eq.and.right(U32.is_le(yy, 9999), Bool.and(T.bound.rng(mo, 1, 12), T.bound.rng(dd, 1, T.when.days(yy, mo))), hw)

# a well-formed date's month range
def wd.mo(
  +yy: U32,
  +mo: U32,
  +dd: U32,
  +hw: {T.wf.date(T.Date{yy, mo, dd}) == True{} : Bool}
) -> {T.bound.rng(mo, 1, 12) == True{} : Bool}:
  Eq.and.left(T.bound.rng(mo, 1, 12), T.bound.rng(dd, 1, T.when.days(yy, mo)), wd.md(yy, mo, dd, hw))

# a well-formed date's day range
def wd.dd(
  +yy: U32,
  +mo: U32,
  +dd: U32,
  +hw: {T.wf.date(T.Date{yy, mo, dd}) == True{} : Bool}
) -> {T.bound.rng(dd, 1, T.when.days(yy, mo)) == True{} : Bool}:
  Eq.and.right(T.bound.rng(mo, 1, 12), T.bound.rng(dd, 1, T.when.days(yy, mo)), wd.md(yy, mo, dd, hw))

# a well-formed date's month is below one hundred
def wd.mo100(
  +yy: U32,
  +mo: U32,
  +dd: U32,
  +hw: {T.wf.date(T.Date{yy, mo, dd}) == True{} : Bool}
) -> {U32.is_lt(mo, 100) == True{} : Bool}:
  lt100(mo, 12, rng.le(mo, 1, 12, wd.mo(yy, mo, dd, hw)), {==})

# a well-formed date's day is below one hundred
def wd.dd100(
  +yy: U32,
  +mo: U32,
  +dd: U32,
  +hw: {T.wf.date(T.Date{yy, mo, dd}) == True{} : Bool}
) -> {U32.is_lt(dd, 100) == True{} : Bool}:
  lt100(dd, T.when.days(yy, mo), rng.le(dd, 1, T.when.days(yy, mo), wd.dd(yy, mo, dd, hw)), days.lt(yy, mo))

# a well-formed clock's hour bound
def wc.h(
  +hh: U32,
  +mi: U32,
  +ss: U32,
  +fr: String,
  +hw: {T.wf.clock(T.Clock{hh, mi, ss, fr}) == True{} : Bool}
) -> {U32.is_le(hh, 23) == True{} : Bool}:
  Eq.and.left(U32.is_le(hh, 23), Bool.and(U32.is_le(mi, 59), Bool.and(U32.is_le(ss, 60), T.wf.digits(fr))), hw)

# the rest of a well-formed clock
def wc.r(
  +hh: U32,
  +mi: U32,
  +ss: U32,
  +fr: String,
  +hw: {T.wf.clock(T.Clock{hh, mi, ss, fr}) == True{} : Bool}
) -> {Bool.and(U32.is_le(mi, 59), Bool.and(U32.is_le(ss, 60), T.wf.digits(fr))) == True{} : Bool}:
  Eq.and.right(U32.is_le(hh, 23), Bool.and(U32.is_le(mi, 59), Bool.and(U32.is_le(ss, 60), T.wf.digits(fr))), hw)

# a well-formed clock's minute bound
def wc.mi(
  +hh: U32,
  +mi: U32,
  +ss: U32,
  +fr: String,
  +hw: {T.wf.clock(T.Clock{hh, mi, ss, fr}) == True{} : Bool}
) -> {U32.is_le(mi, 59) == True{} : Bool}:
  Eq.and.left(U32.is_le(mi, 59), Bool.and(U32.is_le(ss, 60), T.wf.digits(fr)), wc.r(hh, mi, ss, fr, hw))

# the second and the fraction of a well-formed clock
def wc.r2(
  +hh: U32,
  +mi: U32,
  +ss: U32,
  +fr: String,
  +hw: {T.wf.clock(T.Clock{hh, mi, ss, fr}) == True{} : Bool}
) -> {Bool.and(U32.is_le(ss, 60), T.wf.digits(fr)) == True{} : Bool}:
  Eq.and.right(U32.is_le(mi, 59), Bool.and(U32.is_le(ss, 60), T.wf.digits(fr)), wc.r(hh, mi, ss, fr, hw))

# a well-formed clock's second bound
def wc.s(
  +hh: U32,
  +mi: U32,
  +ss: U32,
  +fr: String,
  +hw: {T.wf.clock(T.Clock{hh, mi, ss, fr}) == True{} : Bool}
) -> {U32.is_le(ss, 60) == True{} : Bool}:
  Eq.and.left(U32.is_le(ss, 60), T.wf.digits(fr), wc.r2(hh, mi, ss, fr, hw))

# a well-formed clock's fraction is digits
def wc.fr(
  +hh: U32,
  +mi: U32,
  +ss: U32,
  +fr: String,
  +hw: {T.wf.clock(T.Clock{hh, mi, ss, fr}) == True{} : Bool}
) -> {T.wf.digits(fr) == True{} : Bool}:
  Eq.and.right(U32.is_le(ss, 60), T.wf.digits(fr), wc.r2(hh, mi, ss, fr, hw))

# a well-formed zone's fields are below one hundred
def wz.lt100(
  zz: T.Zone,
  +hw: {T.wf.zone(zz) == True{} : Bool}
) -> {Bool.and(U32.is_lt(zh(zz), 100), U32.is_lt(zm(zz), 100)) == True{} : Bool}:
  match zz:
    case T.Zulu{}:
      {==}
    case T.Shift{_s, +hh, +mi}:
      M5.and.tt(U32.is_lt(hh, 100), U32.is_lt(mi, 100), lt100(hh, 23, Eq.and.left(U32.is_le(hh, 23), U32.is_le(mi, 59),
        hw), {==}), lt100(mi, 59, Eq.and.right(U32.is_le(hh, 23), U32.is_le(mi, 59), hw), {==}))

# the text of a date and a clock: the date, T, the clock, and what follows
def dc.eq(
  +uu: Unit,
  +yy: U32,
  +mo: U32,
  +dd: U32,
  +hh: U32,
  +mi: U32,
  +ss: U32,
  +fr: String,
  +zt: String,
  +hd: {T.wf.date(T.Date{yy, mo, dd}) == True{} : Bool},
  +hc: {T.wf.clock(T.Clock{hh, mi, ss, fr}) == True{} : Bool}
) -> {T.date.text(T.Date{yy, mo, dd}) ++ "T" ++ T.clock.text(T.Clock{hh, mi, ss, fr}) ++ zt ==
  String.append(M2.tstr(tdate(yy, mo, dd, M3.TC{'T'} <> tclock(hh, mi, ss, []))), String.append(T.clock.frac(fr), zt)) :
  String}:
  Equal.trans(String, T.date.text(T.Date{yy, mo, dd}) ++ "T" ++ T.clock.text(T.Clock{hh, mi, ss, fr}) ++ zt,
    M2.tstr(tdate(yy, mo, dd, [])) ++ "T" ++ T.clock.text(T.Clock{hh, mi, ss, fr}) ++ zt,
    String.append(M2.tstr(tdate(yy, mo, dd, M3.TC{'T'} <> tclock(hh, mi, ss, []))), String.append(T.clock.frac(fr),
        zt)),
    Equal.cong(String, String, xx => xx ++ "T" ++ T.clock.text(T.Clock{hh, mi, ss, fr}) ++ zt,
      T.date.text(T.Date{yy, mo, dd}), M2.tstr(tdate(yy, mo, dd, [])), date.eq(uu, yy, mo, dd, wd.y(yy, mo, dd, hd),
      wd.mo100(yy, mo, dd, hd), wd.dd100(yy, mo, dd, hd))),
    Equal.cong(String, String, xx => M2.tstr(tdate(yy, mo, dd, [])) ++ "T" ++ xx ++ zt,
      T.clock.text(T.Clock{hh, mi, ss, fr}), String.append(M2.tstr(tclock(hh, mi, ss, [])), T.clock.frac(fr)),
      clock.eq(hh, mi, ss, fr, lt100(hh, 23, wc.h(hh, mi, ss, fr, hc), {==}), lt100(mi, 59, wc.mi(hh, mi, ss, fr, hc),
      {==}), lt100(ss, 60, wc.s(hh, mi, ss, fr, hc), {==}))))

# the text of a well-formed datetime is its tokens'
def when.eq(
  +uu: Unit,
  ww: T.When,
  +hw: {T.wf.when(ww) == True{} : Bool}
) -> {T.when.text(ww) == M2.tstr(tks(ww)) : String}:
  match ww:
    case T.WOff{T.Date{+yy, +mo, +dd}, T.Clock{+hh, +mi, +ss, +fr}, +zz}:
      +hd = {Eq.and.left(T.wf.date(T.Date{yy, mo, dd}), Bool.and(T.wf.clock(T.Clock{hh, mi, ss, fr}), T.wf.zone(zz)),
        hw) : {T.wf.date(T.Date{yy, mo, dd}) == True{} : Bool}}
      +hr = {Eq.and.right(T.wf.date(T.Date{yy, mo, dd}), Bool.and(T.wf.clock(T.Clock{hh, mi, ss, fr}),
        T.wf.zone(zz)), hw) : {Bool.and(T.wf.clock(T.Clock{hh, mi, ss, fr}), T.wf.zone(zz)) == True{} : Bool}}
      Equal.trans(String, T.date.text(T.Date{yy, mo, dd}) ++ "T" ++ T.clock.text(T.Clock{hh, mi, ss, fr}) ++
        T.zone.text(zz), T.date.text(T.Date{yy, mo, dd}) ++ "T" ++ T.clock.text(T.Clock{hh, mi, ss, fr}) ++
        M2.tstr(tzone(zz)), M2.tstr(tks(T.WOff{T.Date{yy, mo, dd}, T.Clock{hh, mi, ss, fr}, zz})),
        Equal.cong(String, String, xx => T.date.text(T.Date{yy, mo, dd}) ++ "T" ++ T.clock.text(T.Clock{hh, mi, ss,
          fr}) ++ xx, T.zone.text(zz), M2.tstr(tzone(zz)), zone.eq(zz, wz.lt100(zz, Eq.and.right(T.wf.clock(T.Clock{hh,
              mi,
          ss, fr}), T.wf.zone(zz), hr)))),
        Equal.trans(String, T.date.text(T.Date{yy, mo, dd}) ++ "T" ++ T.clock.text(T.Clock{hh, mi, ss, fr}) ++
          M2.tstr(tzone(zz)), String.append(M2.tstr(tdate(yy, mo, dd, M3.TC{'T'} <> tclock(hh, mi, ss, []))),
          String.append(T.clock.frac(fr), M2.tstr(tzone(zz)))),
          M2.tstr(tks(T.WOff{T.Date{yy, mo, dd}, T.Clock{hh, mi, ss, fr}, zz})),
          dc.eq(uu, yy, mo, dd, hh, mi, ss, fr, M2.tstr(tzone(zz)), hd, Eq.and.left(T.wf.clock(T.Clock{hh, mi, ss, fr}),
            T.wf.zone(zz), hr)),
          Equal.cong(String, String, xx => String.append(M2.tstr(tdate(yy, mo, dd, M3.TC{'T'} <> tclock(hh, mi, ss,
              []))),
            xx), String.append(T.clock.frac(fr), M2.tstr(tzone(zz))), M2.tstr(tfr(fr, tzone(zz))), fr.eq(fr,
                tzone(zz)))))
    case T.WLocal{T.Date{+yy, +mo, +dd}, T.Clock{+hh, +mi, +ss, +fr}}:
      Equal.trans(String, T.date.text(T.Date{yy, mo, dd}) ++ "T" ++ T.clock.text(T.Clock{hh, mi, ss, fr}),
        T.date.text(T.Date{yy, mo, dd}) ++ "T" ++ T.clock.text(T.Clock{hh, mi, ss, fr}) ++ "",
        M2.tstr(tks(T.WLocal{T.Date{yy, mo, dd}, T.Clock{hh, mi, ss, fr}})),
        Equal.cong(String, String, xx => T.date.text(T.Date{yy, mo, dd}) ++ "T" ++ xx,
          T.clock.text(T.Clock{hh, mi, ss, fr}), T.clock.text(T.Clock{hh, mi, ss, fr}) ++ "",
          Equal.sym(String, T.clock.text(T.Clock{hh, mi, ss, fr}) ++ "", T.clock.text(T.Clock{hh, mi, ss, fr}),
          Eq.append_nil(T.clock.text(T.Clock{hh, mi, ss, fr})))),
      Equal.trans(String, T.date.text(T.Date{yy, mo, dd}) ++ "T" ++ T.clock.text(T.Clock{hh, mi, ss, fr}) ++ "",
        String.append(M2.tstr(tdate(yy, mo, dd, M3.TC{'T'} <> tclock(hh, mi, ss, []))), String.append(T.clock.frac(fr),
            "")),
        M2.tstr(tks(T.WLocal{T.Date{yy, mo, dd}, T.Clock{hh, mi, ss, fr}})),
        dc.eq(uu, yy, mo, dd, hh, mi, ss, fr, "", Eq.and.left(T.wf.date(T.Date{yy, mo, dd}),
          T.wf.clock(T.Clock{hh, mi, ss, fr}), hw), Eq.and.right(T.wf.date(T.Date{yy, mo, dd}),
          T.wf.clock(T.Clock{hh, mi, ss, fr}), hw)),
        Equal.cong(String, String, xx => String.append(M2.tstr(tdate(yy, mo, dd, M3.TC{'T'} <> tclock(hh, mi, ss,
            []))), xx),
          String.append(T.clock.frac(fr), ""), M2.tstr(tfr(fr, [])), fr.eq(fr, []))))
    case T.WDate{T.Date{+yy, +mo, +dd}}:
      date.eq(uu, yy, mo, dd, wd.y(yy, mo, dd, hw), wd.mo100(yy, mo, dd, hw), wd.dd100(yy, mo, dd, hw))
    case T.WTime{T.Clock{+hh, +mi, +ss, +fr}}:
      Equal.trans(String, T.clock.text(T.Clock{hh, mi, ss, fr}), String.append(M2.tstr(tclock(hh, mi, ss, [])),
        T.clock.frac(fr)), M2.tstr(tclock(hh, mi, ss, tfr(fr, []))),
        clock.eq(hh, mi, ss, fr, lt100(hh, 23, wc.h(hh, mi, ss, fr, hw), {==}), lt100(mi, 59, wc.mi(hh, mi, ss, fr, hw),
          {==}), lt100(ss, 60, wc.s(hh, mi, ss, fr, hw), {==})),
        Equal.trans(String, String.append(M2.tstr(tclock(hh, mi, ss, [])), T.clock.frac(fr)),
          String.append(M2.tstr(tclock(hh, mi, ss, [])), String.append(T.clock.frac(fr), "")),
          M2.tstr(tclock(hh, mi, ss, tfr(fr, []))),
          Equal.cong(String, String, xx => String.append(M2.tstr(tclock(hh, mi, ss, [])), xx), T.clock.frac(fr),
            String.append(T.clock.frac(fr), ""), Equal.sym(String, String.append(T.clock.frac(fr), ""),
            T.clock.frac(fr), Eq.append_nil(T.clock.frac(fr)))),
          Equal.cong(String, String, xx => String.append(M2.tstr(tclock(hh, mi, ss, [])), xx),
            String.append(T.clock.frac(fr), ""), M2.tstr(tfr(fr, [])), fr.eq(fr, []))))

# the value of a two-digit field
def vA(+x1: U32, +x2: U32) -> U32:
  U32.add(U32.mul(U32.add(U32.mul(0, 10), U32.mod(x1, 10)), 10), U32.mod(x2, 10))

# the year's first two digits, as a field
def yA(+yy: U32) -> U32:
  vA(M6.dq(M6.dq(M6.dq(yy))), M6.dq(M6.dq(yy)))

# and the third
def yB(+yy: U32) -> U32:
  U32.add(U32.mul(yA(yy), 10), U32.mod(M6.dq(yy), 10))

# and the fourth
def yV(+yy: U32) -> U32:
  U32.add(U32.mul(yB(yy), 10), U32.mod(yy, 10))

# the year: two digits, a third that is no colon, and a fourth
def yr(
  +uu: Unit,
  +yy: U32,
  +rr: List<&2, Char>,
  +hl: {U32.is_lt(yy, 10000) == True{} : Bool}
) -> {T.when.after2(T.take.n(2n, dx(M6.dq(M6.dq(M6.dq(yy)))) <> dx(M6.dq(M6.dq(yy))) <> dx(M6.dq(yy)) <> dx(yy) <> rr,
    0, True{})) ==
  T.when.year.dash(rr, yy) : T.WhenOut}:
  Equal.trans(T.WhenOut,
    T.when.after2(T.take.n(2n, dx(M6.dq(M6.dq(M6.dq(yy)))) <> dx(M6.dq(M6.dq(yy))) <> dx(M6.dq(yy)) <> dx(yy) <> rr, 0,
        True{})),
    T.when.branch(Char.is_eq(dx(M6.dq(yy)), ':'), Char.is_digit(dx(M6.dq(yy))), yA(yy), dx(M6.dq(yy)), dx(yy) <> rr),
    T.when.year.dash(rr, yy),
    Equal.cong(T.Dig, T.WhenOut, dg => T.when.after2(dg),
      T.take.n(2n, dx(M6.dq(M6.dq(M6.dq(yy)))) <> dx(M6.dq(M6.dq(yy))) <> dx(M6.dq(yy)) <> dx(yy) <> rr, 0, True{}),
      T.DigOk{yA(yy), dx(M6.dq(yy)) <> dx(yy) <> rr}, tk2(M6.dq(M6.dq(M6.dq(yy))), M6.dq(M6.dq(yy)),
          dx(M6.dq(yy)) <> dx(yy) <> rr)),
    Equal.trans(T.WhenOut,
      T.when.branch(Char.is_eq(dx(M6.dq(yy)), ':'), Char.is_digit(dx(M6.dq(yy))), yA(yy), dx(M6.dq(yy)), dx(yy) <> rr),
      T.when.branch(False{}, True{}, yA(yy), dx(M6.dq(yy)), dx(yy) <> rr),
      T.when.year.dash(rr, yy),
      Equal.trans(T.WhenOut,
        T.when.branch(Char.is_eq(dx(M6.dq(yy)), ':'), Char.is_digit(dx(M6.dq(yy))), yA(yy), dx(M6.dq(yy)),
            dx(yy) <> rr),
        T.when.branch(False{}, Char.is_digit(dx(M6.dq(yy))), yA(yy), dx(M6.dq(yy)), dx(yy) <> rr),
        T.when.branch(False{}, True{}, yA(yy), dx(M6.dq(yy)), dx(yy) <> rr),
        Equal.cong(Bool, T.WhenOut, bb => T.when.branch(bb, Char.is_digit(dx(M6.dq(yy))), yA(yy), dx(M6.dq(yy)),
          dx(yy) <> rr),
          Char.is_eq(dx(M6.dq(yy)), ':'), False{}, dd.nocolon(M6.dq(yy))),
        Equal.cong(Bool, T.WhenOut, bb => T.when.branch(False{}, bb, yA(yy), dx(M6.dq(yy)), dx(yy) <> rr),
          Char.is_digit(dx(M6.dq(yy))), True{}, dd.digit(M6.dq(yy)))),
      Equal.trans(T.WhenOut,
        T.when.year4(T.take.n(1n, dx(yy) <> rr, U32.add(U32.mul(yA(yy), 10), T.dig.val(dx(M6.dq(yy)))), True{})),
        T.when.year4(T.take.n(1n, dx(yy) <> rr, yB(yy), True{})),
        T.when.year.dash(rr, yy),
        Equal.cong(U32, T.WhenOut, vv => T.when.year4(T.take.n(1n, dx(yy) <> rr, U32.add(U32.mul(yA(yy), 10), vv),
          True{})), T.dig.val(dx(M6.dq(yy))), U32.mod(M6.dq(yy), 10), dd.val(M6.dq(yy))),
        Equal.trans(T.WhenOut,
          T.when.year4(T.take.n(1n, dx(yy) <> rr, yB(yy), True{})),
          T.when.year.dash(rr, yV(yy)),
          T.when.year.dash(rr, yy),
          Equal.cong(T.Dig, T.WhenOut, dg => T.when.year4(dg), T.take.n(1n, dx(yy) <> rr, yB(yy), True{}),
            T.take.n(0n, rr, yV(yy), True{}), tk1(0n, yy, rr, yB(yy))),
          Equal.cong(U32, T.WhenOut, vv => T.when.year.dash(rr, vv), yV(yy), yy, v4(uu, yy, hl))))))

# the month and the day
def dmd(
  +uu: Unit,
  +yy: U32,
  +mo: U32,
  +dd: U32,
  +rr: List<&2, Char>,
  +hm: {U32.is_lt(mo, 100) == True{} : Bool},
  +hd: {U32.is_lt(dd, 100) == True{} : Bool}
) -> {T.when.year.dash('-' <> dx(M6.dq(mo)) <> dx(mo) <> '-' <> dx(M6.dq(dd)) <> dx(dd) <> rr,
    yy) == T.when.date.ok(yy, mo,
  dd, rr) : T.WhenOut}:
  Equal.trans(T.WhenOut,
    T.when.month.go(T.take.n(2n, dx(M6.dq(mo)) <> dx(mo) <> '-' <> dx(M6.dq(dd)) <> dx(dd) <> rr, 0, True{}), yy),
    T.when.day.go(True{}, T.take.n(2n, dx(M6.dq(dd)) <> dx(dd) <> rr, 0, True{}), yy, vA(M6.dq(mo), mo)),
    T.when.date.ok(yy, mo, dd, rr),
    Equal.cong(T.Dig, T.WhenOut, dg => T.when.month.go(dg, yy),
      T.take.n(2n, dx(M6.dq(mo)) <> dx(mo) <> '-' <> dx(M6.dq(dd)) <> dx(dd) <> rr, 0, True{}),
      T.DigOk{vA(M6.dq(mo), mo), '-' <> dx(M6.dq(dd)) <> dx(dd) <> rr}, tk2(M6.dq(mo), mo,
          '-' <> dx(M6.dq(dd)) <> dx(dd) <> rr)),
    Equal.trans(T.WhenOut,
      T.when.day.go(True{}, T.take.n(2n, dx(M6.dq(dd)) <> dx(dd) <> rr, 0, True{}), yy, vA(M6.dq(mo), mo)),
      T.when.date.ok(yy, vA(M6.dq(mo), mo), vA(M6.dq(dd), dd), rr),
      T.when.date.ok(yy, mo, dd, rr),
      Equal.cong(T.Dig, T.WhenOut, dg => T.when.day.go(True{}, dg, yy, vA(M6.dq(mo), mo)),
        T.take.n(2n, dx(M6.dq(dd)) <> dx(dd) <> rr, 0, True{}), T.DigOk{vA(M6.dq(dd), dd), rr}, tk2(M6.dq(dd), dd, rr)),
      Equal.trans(T.WhenOut,
        T.when.date.ok(yy, vA(M6.dq(mo), mo), vA(M6.dq(dd), dd), rr),
        T.when.date.ok(yy, mo, vA(M6.dq(dd), dd), rr),
        T.when.date.ok(yy, mo, dd, rr),
        Equal.cong(U32, T.WhenOut, vv => T.when.date.ok(yy, vv, vA(M6.dq(dd), dd), rr), vA(M6.dq(mo), mo), mo,
          v2.lt(uu, mo, hm)),
        Equal.cong(U32, T.WhenOut, vv => T.when.date.ok(yy, mo, vv, rr), vA(M6.dq(dd), dd), dd, v2.lt(uu, dd, hd)))))

# a date whose fields are in range goes on to what follows it
def dok(
  +yy: U32,
  +mo: U32,
  +dd: U32,
  +rr: List<&2, Char>,
  +h1: {T.bound.rng(mo, 1, 12) == True{} : Bool},
  +h2: {T.bound.rng(dd, 1, T.when.days(yy, mo)) == True{} : Bool}
) -> {T.when.date.ok(yy, mo, dd, rr) == T.when.after.date(T.Date{yy, mo, dd}, rr) : T.WhenOut}:
  Equal.trans(T.WhenOut,
    T.when.date.ok.go(T.bound.rng(mo, 1, 12), T.bound.rng(dd, 1, T.when.days(yy, mo)), yy, mo, dd, rr),
    T.when.date.ok.go(True{}, T.bound.rng(dd, 1, T.when.days(yy, mo)), yy, mo, dd, rr),
    T.when.after.date(T.Date{yy, mo, dd}, rr),
    Equal.cong(Bool, T.WhenOut, bb => T.when.date.ok.go(bb, T.bound.rng(dd, 1, T.when.days(yy, mo)), yy, mo, dd, rr),
      T.bound.rng(mo, 1, 12), True{}, h1),
    Equal.cong(Bool, T.WhenOut, bb => T.when.date.ok.go(True{}, bb, yy, mo, dd, rr),
      T.bound.rng(dd, 1, T.when.days(yy, mo)), True{}, h2))

# the minutes and seconds of a clock whose hour is read
def clk.mm(
  +uu: Unit,
  +hh: U32,
  +mi: U32,
  +ss: U32,
  +rr: List<&2, Char>,
  +dt: T.Date,
  +h2: {U32.is_le(mi, 59) == True{} : Bool},
  +h3: {U32.is_le(ss, 60) == True{} : Bool},
  +hr: {T.bound.rng(hh, 0, 23) == True{} : Bool}
) -> {T.when.clock.mm(T.take.n(2n, dx(M6.dq(mi)) <> dx(mi) <> ':' <> dx(M6.dq(ss)) <> dx(ss) <> rr, 0, True{}), hh,
    dt) ==
  T.when.frac(rr, T.Clock{hh, mi, ss, ""}, dt) : T.WhenOut}:
  Equal.trans(T.WhenOut,
    T.when.clock.mm(T.take.n(2n, dx(M6.dq(mi)) <> dx(mi) <> ':' <> dx(M6.dq(ss)) <> dx(ss) <> rr, 0, True{}), hh, dt),
    T.when.clock.ss(True{}, T.take.n(2n, dx(M6.dq(ss)) <> dx(ss) <> rr, 0, True{}), hh, vA(M6.dq(mi), mi), dt),
    T.when.frac(rr, T.Clock{hh, mi, ss, ""}, dt),
    Equal.cong(T.Dig, T.WhenOut, dg => T.when.clock.mm(dg, hh, dt),
      T.take.n(2n, dx(M6.dq(mi)) <> dx(mi) <> ':' <> dx(M6.dq(ss)) <> dx(ss) <> rr, 0, True{}),
      T.DigOk{vA(M6.dq(mi), mi), ':' <> dx(M6.dq(ss)) <> dx(ss) <> rr}, tk2(M6.dq(mi), mi,
          ':' <> dx(M6.dq(ss)) <> dx(ss) <> rr)),
    Equal.trans(T.WhenOut,
      T.when.clock.ss(True{}, T.take.n(2n, dx(M6.dq(ss)) <> dx(ss) <> rr, 0, True{}), hh, vA(M6.dq(mi), mi), dt),
      T.when.clock.ss(True{}, T.DigOk{vA(M6.dq(ss), ss), rr}, hh, vA(M6.dq(mi), mi), dt),
      T.when.frac(rr, T.Clock{hh, mi, ss, ""}, dt),
      Equal.cong(T.Dig, T.WhenOut, dg => T.when.clock.ss(True{}, dg, hh, vA(M6.dq(mi), mi), dt),
        T.take.n(2n, dx(M6.dq(ss)) <> dx(ss) <> rr, 0, True{}), T.DigOk{vA(M6.dq(ss), ss), rr}, tk2(M6.dq(ss), ss, rr)),
      Equal.trans(T.WhenOut,
        T.when.clock.ss(True{}, T.DigOk{vA(M6.dq(ss), ss), rr}, hh, vA(M6.dq(mi), mi), dt),
        T.when.clock.ss(True{}, T.DigOk{ss, rr}, hh, mi, dt),
        T.when.frac(rr, T.Clock{hh, mi, ss, ""}, dt),
        Equal.trans(T.WhenOut,
          T.when.clock.ss(True{}, T.DigOk{vA(M6.dq(ss), ss), rr}, hh, vA(M6.dq(mi), mi), dt),
          T.when.clock.ss(True{}, T.DigOk{vA(M6.dq(ss), ss), rr}, hh, mi, dt),
          T.when.clock.ss(True{}, T.DigOk{ss, rr}, hh, mi, dt),
          Equal.cong(U32, T.WhenOut, vv => T.when.clock.ss(True{}, T.DigOk{vA(M6.dq(ss), ss), rr}, hh, vv, dt),
            vA(M6.dq(mi), mi), mi, v2.lt(uu, mi, lt100(mi, 59, h2, {==}))),
          Equal.cong(U32, T.WhenOut, vv => T.when.clock.ss(True{}, T.DigOk{vv, rr}, hh, mi, dt), vA(M6.dq(ss), ss), ss,
            v2.lt(uu, ss, lt100(ss, 60, h3, {==})))),
        Equal.trans(T.WhenOut,
          T.when.clock.range(T.bound.rng(hh, 0, 23), T.bound.rng(mi, 0, 59), T.bound.rng(ss, 0, 60), hh, mi, ss, rr,
            dt),
          T.when.clock.range(True{}, T.bound.rng(mi, 0, 59), T.bound.rng(ss, 0, 60), hh, mi, ss, rr, dt),
          T.when.frac(rr, T.Clock{hh, mi, ss, ""}, dt),
          Equal.cong(Bool, T.WhenOut, bb => T.when.clock.range(bb, T.bound.rng(mi, 0, 59), T.bound.rng(ss, 0, 60), hh,
            mi, ss, rr, dt), T.bound.rng(hh, 0, 23), True{}, hr),
          Equal.trans(T.WhenOut,
            T.when.clock.range(True{}, T.bound.rng(mi, 0, 59), T.bound.rng(ss, 0, 60), hh, mi, ss, rr, dt),
            T.when.clock.range(True{}, True{}, T.bound.rng(ss, 0, 60), hh, mi, ss, rr, dt),
            T.when.frac(rr, T.Clock{hh, mi, ss, ""}, dt),
            Equal.cong(Bool, T.WhenOut, bb => T.when.clock.range(True{}, bb, T.bound.rng(ss, 0, 60), hh, mi, ss, rr,
              dt), T.bound.rng(mi, 0, 59), True{}, rng0(mi, 59, h2)),
            Equal.cong(Bool, T.WhenOut, bb => T.when.clock.range(True{}, True{}, bb, hh, mi, ss, rr, dt),
              T.bound.rng(ss, 0, 60), True{}, rng0(ss, 60, h3)))))))

# a clock after a date: the hour, then the rest
def clk.of(
  +uu: Unit,
  +hh: U32,
  +mi: U32,
  +ss: U32,
  +rr: List<&2, Char>,
  +dt: T.Date,
  +h1: {U32.is_le(hh, 23) == True{} : Bool},
  +h2: {U32.is_le(mi, 59) == True{} : Bool},
  +h3: {U32.is_le(ss, 60) == True{} : Bool}
) -> {T.when.clock.of(T.take.n(2n,
    dx(M6.dq(hh)) <> dx(hh) <> ':' <> dx(M6.dq(mi)) <> dx(mi) <> ':' <> dx(M6.dq(ss)) <> dx(ss) <>
  rr, 0, True{}), dt) == T.when.frac(rr, T.Clock{hh, mi, ss, ""}, dt) : T.WhenOut}:
  Equal.trans(T.WhenOut,
    T.when.clock.of(T.take.n(2n, dx(M6.dq(hh)) <> dx(hh) <> ':' <> dx(M6.dq(mi)) <> dx(mi) <> ':' <> dx(M6.dq(ss)) <>
      dx(ss) <> rr, 0, True{}), dt),
    T.when.clock.mm(T.take.n(2n, dx(M6.dq(mi)) <> dx(mi) <> ':' <> dx(M6.dq(ss)) <> dx(ss) <> rr, 0, True{}), hh, dt),
    T.when.frac(rr, T.Clock{hh, mi, ss, ""}, dt),
    Equal.trans(T.WhenOut,
      T.when.clock.of(T.take.n(2n, dx(M6.dq(hh)) <> dx(hh) <> ':' <> dx(M6.dq(mi)) <> dx(mi) <> ':' <> dx(M6.dq(ss)) <>
        dx(ss) <> rr, 0, True{}), dt),
      T.when.clock.mm(T.take.n(2n, dx(M6.dq(mi)) <> dx(mi) <> ':' <> dx(M6.dq(ss)) <> dx(ss) <> rr, 0, True{}),
        vA(M6.dq(hh), hh), dt),
      T.when.clock.mm(T.take.n(2n, dx(M6.dq(mi)) <> dx(mi) <> ':' <> dx(M6.dq(ss)) <> dx(ss) <> rr, 0, True{}), hh, dt),
      Equal.cong(T.Dig, T.WhenOut, dg => T.when.clock.of(dg, dt),
        T.take.n(2n, dx(M6.dq(hh)) <> dx(hh) <> ':' <> dx(M6.dq(mi)) <> dx(mi) <> ':' <> dx(M6.dq(ss)) <> dx(ss) <> rr,
            0,
        True{}), T.DigOk{vA(M6.dq(hh), hh), ':' <> dx(M6.dq(mi)) <> dx(mi) <> ':' <> dx(M6.dq(ss)) <> dx(ss) <> rr},
        tk2(M6.dq(hh), hh, ':' <> dx(M6.dq(mi)) <> dx(mi) <> ':' <> dx(M6.dq(ss)) <> dx(ss) <> rr)),
      Equal.cong(U32, T.WhenOut, vv => T.when.clock.mm(T.take.n(2n, dx(M6.dq(mi)) <> dx(mi) <> ':' <> dx(M6.dq(ss)) <>
        dx(ss) <> rr, 0, True{}), vv, dt), vA(M6.dq(hh), hh), hh, v2.lt(uu, hh, lt100(hh, 23, h1, {==})))),
    clk.mm(uu, hh, mi, ss, rr, dt, h2, h3, rng0(hh, 23, h1)))

# what may follow a fraction: nothing, or a character that is no digit and no
# dot
def zok(ts: List<&2, M3.Tk>) -> Bool:
  match ts:
    case []:
      True{}
    case M3.TD{_x} <> _t:
      False{}
    case M3.TC{+cc} <> _t:
      Bool.and(Bool.not(Char.is_digit(cc)), Bool.not(Char.is_eq(cc, '.')))

# a zone may follow a fraction
def zok.z(zz: T.Zone) -> {zok(tzone(zz)) == True{} : Bool}:
  match zz:
    case T.Zulu{}:
      {==}
    case T.Shift{sg, _h, _m}:
      match sg:
        case T.Plus{}:
          {==}
        case T.Minus{}:
          {==}

# the fraction's digits end at what follows them
def fend(
  zs: List<&2, M3.Tk>,
  +rev: List<&2, Char>,
  +clk: T.Clock,
  +dt: T.Date,
  hz: {zok(zs) == True{} : Bool}
) -> {T.when.frac.digits(M2.tl(zs), rev, clk, dt) == T.when.frac.end(rev, clk, dt, M2.tl(zs)) : T.WhenOut}:
  match zs:
    case []:
      {==}
    case M3.TD{xx} <> tt:
      Eq.bit.absurd(&2, {T.when.frac.digits(M2.tl(M3.TD{xx} <> tt), rev, clk, dt) == T.when.frac.end(rev, clk, dt,
        M2.tl(M3.TD{xx} <> tt)) : T.WhenOut}, hz)
    case M3.TC{+cc} <> +tt:
      Equal.cong(Bool, T.WhenOut, bb => T.when.frac.digit(bb, cc, M2.tl(tt), rev, clk, dt,
        _u => T.when.frac.digits(M2.tl(tt), cc <> rev, clk, dt)), Char.is_digit(cc), False{},
        Eq.not.true(Char.is_digit(cc), Eq.and.left(Bool.not(Char.is_digit(cc)), Bool.not(Char.is_eq(cc, '.')), hz)))

# the fraction's digits are pushed, then end at what follows them
def fdig(
  fr: String,
  +rev: List<&2, Char>,
  +zs: List<&2, M3.Tk>,
  +clk: T.Clock,
  +dt: T.Date,
  +hd: {T.wf.digits(fr) == True{} : Bool},
  +hz: {zok(zs) == True{} : Bool}
) -> {T.when.frac.digits(M2.tl(tcs(fr, zs)), rev, clk, dt) == T.when.frac.end(M3.rev.onto(fr, rev), clk, dt,
    M2.tl(zs)) :
  T.WhenOut}:
  match fr:
    case SNil{}:
      fend(zs, rev, clk, dt, hz)
    case SCon{+cc, +tt}:
      Equal.trans(T.WhenOut,
        T.when.frac.digit(Char.is_digit(cc), cc, M2.tl(tcs(tt, zs)), rev, clk, dt,
          _u => T.when.frac.digits(M2.tl(tcs(tt, zs)), cc <> rev, clk, dt)),
        T.when.frac.digits(M2.tl(tcs(tt, zs)), cc <> rev, clk, dt),
        T.when.frac.end(M3.rev.onto(tt, cc <> rev), clk, dt, M2.tl(zs)),
        Equal.cong(Bool, T.WhenOut, bb => T.when.frac.digit(bb, cc, M2.tl(tcs(tt, zs)), rev, clk, dt,
          _u => T.when.frac.digits(M2.tl(tcs(tt, zs)), cc <> rev, clk, dt)), Char.is_digit(cc), True{},
          M3.then.l(Char.is_digit(cc), tt, hd)),
        fdig(tt, cc <> rev, zs, clk, dt, M3.then.r(Char.is_digit(cc), tt, hd), hz))

# a buffer something was pushed onto has a character
def some.rev(tt: String, +cc: Char, +acc: List<&2, Char>) -> {T.cs.some(M3.rev.onto(tt, cc <> acc)) == True{} : Bool}:
  match tt:
    case SNil{}:
      {==}
    case SCon{hh, ts}:
      some.rev(ts, hh, cc <> acc)

# no fraction: the zone is read
def frac.none(
  zs: List<&2, M3.Tk>,
  +hh: U32,
  +mi: U32,
  +ss: U32,
  +dt: T.Date,
  hz: {zok(zs) == True{} : Bool}
) -> {T.when.frac(M2.tl(zs), T.Clock{hh, mi, ss, ""}, dt) == T.when.zone(M2.tl(zs), T.Clock{hh, mi, ss, ""},
    dt) : T.WhenOut}:
  match zs:
    case []:
      {==}
    case M3.TD{xx} <> tt:
      Eq.bit.absurd(&2, {T.when.frac(M2.tl(M3.TD{xx} <> tt), T.Clock{hh, mi, ss, ""},
          dt) == T.when.zone(M2.tl(M3.TD{xx} <> tt),
        T.Clock{hh, mi, ss, ""}, dt) : T.WhenOut}, hz)
    case M3.TC{+cc} <> +tt:
      Equal.cong(Bool, T.WhenOut, bb => T.when.frac.go(bb, M2.tl(tt), T.Clock{hh, mi, ss, ""}, dt, cc),
        Char.is_eq(cc, '.'), False{}, Eq.not.true(Char.is_eq(cc, '.'), Eq.and.right(Bool.not(Char.is_digit(cc)),
        Bool.not(Char.is_eq(cc, '.')), hz)))

# a fraction then what follows it: the clock takes the fraction's digits, and
# the zone is read
def frac.all(
  fr: String,
  +hh: U32,
  +mi: U32,
  +ss: U32,
  +zs: List<&2, M3.Tk>,
  +dt: T.Date,
  +hd: {T.wf.digits(fr) == True{} : Bool},
  +hz: {zok(zs) == True{} : Bool}
) -> {T.when.frac(M2.tl(tfr(fr, zs)), T.Clock{hh, mi, ss, ""}, dt) == T.when.zone(M2.tl(zs), T.Clock{hh, mi, ss, fr},
    dt) :
  T.WhenOut}:
  match fr:
    case SNil{}:
      frac.none(zs, hh, mi, ss, dt, hz)
    case SCon{+cc, +tt}:
      Equal.trans(T.WhenOut,
        T.when.frac.digits(M2.tl(tcs(SCon{cc, tt}, zs)), [], T.Clock{hh, mi, ss, ""}, dt),
        T.when.frac.end(M3.rev.onto(tt, [cc]), T.Clock{hh, mi, ss, ""}, dt, M2.tl(zs)),
        T.when.zone(M2.tl(zs), T.Clock{hh, mi, ss, SCon{cc, tt}}, dt),
        fdig(SCon{cc, tt}, [], zs, T.Clock{hh, mi, ss, ""}, dt, hd, hz),
        Equal.trans(T.WhenOut,
          T.when.frac.end.go(T.cs.some(M3.rev.onto(tt, [cc])), M3.rev.onto(tt, [cc]), T.Clock{hh, mi, ss, ""}, dt,
              M2.tl(zs)),
          T.when.zone(M2.tl(zs), T.Clock{hh, mi, ss, T.buf.str.go(M3.rev.onto(tt, [cc]), "")}, dt),
          T.when.zone(M2.tl(zs), T.Clock{hh, mi, ss, SCon{cc, tt}}, dt),
          Equal.cong(Bool, T.WhenOut, bb => T.when.frac.end.go(bb, M3.rev.onto(tt, [cc]), T.Clock{hh, mi, ss, ""}, dt,
            M2.tl(zs)), T.cs.some(M3.rev.onto(tt, [cc])), True{}, some.rev(tt, cc, [])),
          Equal.cong(String, T.WhenOut, fs => T.when.zone(M2.tl(zs), T.Clock{hh, mi, ss, fs}, dt),
            T.buf.str.go(M3.rev.onto(tt, [cc]), ""), SCon{cc, tt},
            Equal.trans(String, T.buf.str.go(M3.rev.onto(tt, [cc]), ""),
              String.from_list(List.reverse(&2, Char, M3.rev.onto(tt, [cc]))), SCon{cc, tt},
              M1.fold.nil(M3.rev.onto(tt, [cc])),
              Equal.trans(String, String.from_list(List.reverse(&2, Char, M3.rev.onto(tt, [cc]))),
                String.from_list(String.to_list(SCon{cc, tt})), SCon{cc, tt},
                Equal.cong(List<&2, Char>, String, ls => String.from_list(ls),
                  List.reverse(&2, Char, M3.rev.onto(tt, [cc])),
                  String.to_list(SCon{cc, tt}), M3.wd.order(cc, tt)), M3.ftl(SCon{cc, tt}))))))

# a numeric offset, after its sign
def zoff(
  +uu: Unit,
  +sg: T.Sign,
  +zh: U32,
  +zi: U32,
  +clk: T.Clock,
  +dt: T.Date,
  +h1: {U32.is_le(zh, 23) == True{} : Bool},
  +h2: {U32.is_le(zi, 59) == True{} : Bool}
) -> {T.when.zone.hh(T.take.n(2n, dx(M6.dq(zh)) <> dx(zh) <> ':' <> dx(M6.dq(zi)) <> dx(zi) <> [], 0, True{}), sg, clk,
    dt) ==
  T.WSome{T.WOff{dt, clk, T.Shift{sg, zh, zi}}} : T.WhenOut}:
  Equal.trans(T.WhenOut,
    T.when.zone.hh(T.take.n(2n, dx(M6.dq(zh)) <> dx(zh) <> ':' <> dx(M6.dq(zi)) <> dx(zi) <> [], 0, True{}), sg, clk,
        dt),
    T.when.zone.mm(True{}, T.take.n(2n, dx(M6.dq(zi)) <> dx(zi) <> [], 0, True{}), sg, vA(M6.dq(zh), zh), clk, dt),
    T.WSome{T.WOff{dt, clk, T.Shift{sg, zh, zi}}},
    Equal.cong(T.Dig, T.WhenOut, dg => T.when.zone.hh(dg, sg, clk, dt),
      T.take.n(2n, dx(M6.dq(zh)) <> dx(zh) <> ':' <> dx(M6.dq(zi)) <> dx(zi) <> [], 0, True{}),
      T.DigOk{vA(M6.dq(zh), zh), ':' <> dx(M6.dq(zi)) <> dx(zi) <> []}, tk2(M6.dq(zh), zh,
          ':' <> dx(M6.dq(zi)) <> dx(zi) <> [])),
    Equal.trans(T.WhenOut,
      T.when.zone.mm(True{}, T.take.n(2n, dx(M6.dq(zi)) <> dx(zi) <> [], 0, True{}), sg, vA(M6.dq(zh), zh), clk, dt),
      T.when.zone.mm.ok(T.bound.rng(vA(M6.dq(zh), zh), 0, 23), T.bound.rng(vA(M6.dq(zi), zi), 0, 59), sg, vA(M6.dq(zh),
          zh),
        vA(M6.dq(zi), zi), clk, dt),
      T.WSome{T.WOff{dt, clk, T.Shift{sg, zh, zi}}},
      Equal.cong(T.Dig, T.WhenOut, dg => T.when.zone.mm(True{}, dg, sg, vA(M6.dq(zh), zh), clk, dt),
        T.take.n(2n, dx(M6.dq(zi)) <> dx(zi) <> [], 0, True{}), T.DigOk{vA(M6.dq(zi), zi), []}, tk2(M6.dq(zi), zi, [])),
      Equal.trans(T.WhenOut,
        T.when.zone.mm.ok(T.bound.rng(vA(M6.dq(zh), zh), 0, 23), T.bound.rng(vA(M6.dq(zi), zi), 0, 59), sg,
            vA(M6.dq(zh), zh),
          vA(M6.dq(zi), zi), clk, dt),
        T.when.zone.mm.ok(T.bound.rng(zh, 0, 23), T.bound.rng(zi, 0, 59), sg, zh, zi, clk, dt),
        T.WSome{T.WOff{dt, clk, T.Shift{sg, zh, zi}}},
        Equal.trans(T.WhenOut,
          T.when.zone.mm.ok(T.bound.rng(vA(M6.dq(zh), zh), 0, 23), T.bound.rng(vA(M6.dq(zi), zi), 0, 59), sg,
            vA(M6.dq(zh), zh), vA(M6.dq(zi), zi), clk, dt),
          T.when.zone.mm.ok(T.bound.rng(zh, 0, 23), T.bound.rng(vA(M6.dq(zi), zi), 0, 59), sg, zh, vA(M6.dq(zi), zi),
              clk,
            dt),
          T.when.zone.mm.ok(T.bound.rng(zh, 0, 23), T.bound.rng(zi, 0, 59), sg, zh, zi, clk, dt),
          Equal.cong(U32, T.WhenOut, vv => T.when.zone.mm.ok(T.bound.rng(vv, 0, 23), T.bound.rng(vA(M6.dq(zi), zi), 0,
            59), sg, vv, vA(M6.dq(zi), zi), clk, dt), vA(M6.dq(zh), zh), zh, v2.lt(uu, zh, lt100(zh, 23, h1, {==}))),
          Equal.cong(U32, T.WhenOut, vv => T.when.zone.mm.ok(T.bound.rng(zh, 0, 23), T.bound.rng(vv, 0, 59), sg, zh,
            vv, clk, dt), vA(M6.dq(zi), zi), zi, v2.lt(uu, zi, lt100(zi, 59, h2, {==})))),
        Equal.trans(T.WhenOut,
          T.when.zone.mm.ok(T.bound.rng(zh, 0, 23), T.bound.rng(zi, 0, 59), sg, zh, zi, clk, dt),
          T.when.zone.mm.ok(True{}, T.bound.rng(zi, 0, 59), sg, zh, zi, clk, dt),
          T.WSome{T.WOff{dt, clk, T.Shift{sg, zh, zi}}},
          Equal.cong(Bool, T.WhenOut, bb => T.when.zone.mm.ok(bb, T.bound.rng(zi, 0, 59), sg, zh, zi, clk, dt),
            T.bound.rng(zh, 0, 23), True{}, rng0(zh, 23, h1)),
          Equal.cong(Bool, T.WhenOut, bb => T.when.zone.mm.ok(True{}, bb, sg, zh, zi, clk, dt),
            T.bound.rng(zi, 0, 59), True{}, rng0(zi, 59, h2))))))

# a numeric offset, by its sign
def zn.s(
  +uu: Unit,
  sg: T.Sign,
  +zh: U32,
  +zi: U32,
  +clk: T.Clock,
  +dt: T.Date,
  h1: {U32.is_le(zh, 23) == True{} : Bool},
  h2: {U32.is_le(zi, 59) == True{} : Bool}
) -> {T.when.zone(M2.tl(tzone(T.Shift{sg, zh, zi})), clk, dt) == T.WSome{T.WOff{dt, clk, T.Shift{sg, zh, zi}}} :
  T.WhenOut}:
  match sg:
    case T.Plus{}:
      zoff(uu, T.Plus{}, zh, zi, clk, dt, h1, h2)
    case T.Minus{}:
      zoff(uu, T.Minus{}, zh, zi, clk, dt, h1, h2)

# a well-formed zone is read as itself
def zn(
  +uu: Unit,
  zz: T.Zone,
  +clk: T.Clock,
  +dt: T.Date,
  +hw: {T.wf.zone(zz) == True{} : Bool}
) -> {T.when.zone(M2.tl(tzone(zz)), clk, dt) == T.WSome{T.WOff{dt, clk, zz}} : T.WhenOut}:
  match zz:
    case T.Zulu{}:
      {==}
    case T.Shift{sg, +zh, +zi}:
      zn.s(uu, sg, zh, zi, clk, dt, Eq.and.left(U32.is_le(zh, 23), U32.is_le(zi, 59), hw),
        Eq.and.right(U32.is_le(zh, 23), U32.is_le(zi, 59), hw))

# the characters of a date's tokens, then more
def cdate(+yy: U32, +mo: U32, +dd: U32, rr: List<&2, Char>) -> List<&2, Char>:
  dx(M6.dq(M6.dq(M6.dq(yy)))) <> dx(M6.dq(M6.dq(yy))) <> dx(M6.dq(yy)) <> dx(yy) <> '-' <> dx(M6.dq(mo)) <> dx(mo) <>
    '-' <> dx(M6.dq(dd)) <>
    dx(dd) <> rr

# a well-formed date's text, then more, is read as the date, then the more
def rd.date(
  +uu: Unit,
  +yy: U32,
  +mo: U32,
  +dd: U32,
  +rr: List<&2, Char>,
  +hw: {T.wf.date(T.Date{yy, mo, dd}) == True{} : Bool}
) -> {T.when.read(cdate(yy, mo, dd, rr)) == T.when.after.date(T.Date{yy, mo, dd}, rr) : T.WhenOut}:
  Equal.trans(T.WhenOut, T.when.read(cdate(yy, mo, dd, rr)),
    T.when.year.dash('-' <> dx(M6.dq(mo)) <> dx(mo) <> '-' <> dx(M6.dq(dd)) <> dx(dd) <> rr, yy),
    T.when.after.date(T.Date{yy, mo, dd}, rr),
    yr(uu, yy, '-' <> dx(M6.dq(mo)) <> dx(mo) <> '-' <> dx(M6.dq(dd)) <> dx(dd) <> rr, wd.y(yy, mo, dd, hw)),
    Equal.trans(T.WhenOut, T.when.year.dash('-' <> dx(M6.dq(mo)) <> dx(mo) <> '-' <> dx(M6.dq(dd)) <> dx(dd) <> rr, yy),
      T.when.date.ok(yy, mo, dd, rr), T.when.after.date(T.Date{yy, mo, dd}, rr),
      dmd(uu, yy, mo, dd, rr, wd.mo100(yy, mo, dd, hw), wd.dd100(yy, mo, dd, hw)),
      dok(yy, mo, dd, rr, wd.mo(yy, mo, dd, hw), wd.dd(yy, mo, dd, hw))))

# the characters of a clock's tokens, then more
def cclock(+hh: U32, +mi: U32, +ss: U32, rr: List<&2, Char>) -> List<&2, Char>:
  dx(M6.dq(hh)) <> dx(hh) <> ':' <> dx(M6.dq(mi)) <> dx(mi) <> ':' <> dx(M6.dq(ss)) <> dx(ss) <> rr

# a date and a clock, then what follows the clock's fraction
def rd.dc(
  +uu: Unit,
  +yy: U32,
  +mo: U32,
  +dd: U32,
  +hh: U32,
  +mi: U32,
  +ss: U32,
  +fr: String,
  +zs: List<&2, M3.Tk>,
  +hd: {T.wf.date(T.Date{yy, mo, dd}) == True{} : Bool},
  +hc: {T.wf.clock(T.Clock{hh, mi, ss, fr}) == True{} : Bool},
  +hz: {zok(zs) == True{} : Bool}
) -> {T.when.read(M2.tl(tdate(yy, mo, dd, M3.TC{'T'} <> tclock(hh, mi, ss, tfr(fr, zs))))) == T.when.zone(M2.tl(zs),
    T.Clock{hh,
  mi, ss, fr}, T.Date{yy, mo, dd}) : T.WhenOut}:
  Equal.trans(T.WhenOut, T.when.read(cdate(yy, mo, dd, 'T' <> cclock(hh, mi, ss, M2.tl(tfr(fr, zs))))),
    T.when.after.date(T.Date{yy, mo, dd}, 'T' <> cclock(hh, mi, ss, M2.tl(tfr(fr, zs)))),
    T.when.zone(M2.tl(zs), T.Clock{hh, mi, ss, fr}, T.Date{yy, mo, dd}),
    rd.date(uu, yy, mo, dd, 'T' <> cclock(hh, mi, ss, M2.tl(tfr(fr, zs))), hd),
    Equal.trans(T.WhenOut, T.when.clock.of(T.take.n(2n, cclock(hh, mi, ss, M2.tl(tfr(fr, zs))), 0, True{}),
      T.Date{yy, mo, dd}),
      T.when.frac(M2.tl(tfr(fr, zs)), T.Clock{hh, mi, ss, ""}, T.Date{yy, mo, dd}),
      T.when.zone(M2.tl(zs), T.Clock{hh, mi, ss, fr}, T.Date{yy, mo, dd}),
      clk.of(uu, hh, mi, ss, M2.tl(tfr(fr, zs)), T.Date{yy, mo, dd}, wc.h(hh, mi, ss, fr, hc), wc.mi(hh, mi, ss, fr,
          hc),
        wc.s(hh, mi, ss, fr, hc)),
      frac.all(fr, hh, mi, ss, zs, T.Date{yy, mo, dd}, wc.fr(hh, mi, ss, fr, hc), hz)))

# a local time: the hour, a colon, and the rest of the clock, on a placeholder
# date that only the clock is kept from
def rd.time(
  +uu: Unit,
  +hh: U32,
  +mi: U32,
  +ss: U32,
  +fr: String,
  +hc: {T.wf.clock(T.Clock{hh, mi, ss, fr}) == True{} : Bool}
) -> {T.when.read(M2.tl(tclock(hh, mi, ss, tfr(fr, [])))) == T.WSome{T.WTime{T.Clock{hh, mi, ss, fr}}} : T.WhenOut}:
  Equal.trans(T.WhenOut, T.when.after2(T.take.n(2n, cclock(hh, mi, ss, M2.tl(tfr(fr, []))), 0, True{})),
    T.when.time.only(T.when.clock.mm(T.take.n(2n, dx(M6.dq(mi)) <> dx(mi) <> ':' <> dx(M6.dq(ss)) <> dx(ss) <>
      M2.tl(tfr(fr, [])), 0, True{}), vA(M6.dq(hh), hh), T.Date{0, 1, 1})),
    T.WSome{T.WTime{T.Clock{hh, mi, ss, fr}}},
    Equal.cong(T.Dig, T.WhenOut, dg => T.when.after2(dg), T.take.n(2n, cclock(hh, mi, ss, M2.tl(tfr(fr, []))), 0,
        True{}),
      T.DigOk{vA(M6.dq(hh), hh), ':' <> dx(M6.dq(mi)) <> dx(mi) <> ':' <> dx(M6.dq(ss)) <> dx(ss) <> M2.tl(tfr(fr,
          []))},
      tk2(M6.dq(hh), hh, ':' <> dx(M6.dq(mi)) <> dx(mi) <> ':' <> dx(M6.dq(ss)) <> dx(ss) <> M2.tl(tfr(fr, [])))),
    Equal.trans(T.WhenOut,
      T.when.time.only(T.when.clock.mm(T.take.n(2n, dx(M6.dq(mi)) <> dx(mi) <> ':' <> dx(M6.dq(ss)) <> dx(ss) <>
        M2.tl(tfr(fr, [])), 0, True{}), vA(M6.dq(hh), hh), T.Date{0, 1, 1})),
      T.when.time.only(T.when.clock.mm(T.take.n(2n, dx(M6.dq(mi)) <> dx(mi) <> ':' <> dx(M6.dq(ss)) <> dx(ss) <>
        M2.tl(tfr(fr, [])), 0, True{}), hh, T.Date{0, 1, 1})),
      T.WSome{T.WTime{T.Clock{hh, mi, ss, fr}}},
      Equal.cong(U32, T.WhenOut, vv => T.when.time.only(T.when.clock.mm(T.take.n(2n, dx(M6.dq(mi)) <> dx(mi) <> ':' <>
        dx(M6.dq(ss)) <> dx(ss) <> M2.tl(tfr(fr, [])), 0, True{}), vv, T.Date{0, 1, 1})), vA(M6.dq(hh), hh), hh,
        v2.lt(uu, hh, lt100(hh, 23, wc.h(hh, mi, ss, fr, hc), {==}))),
      Equal.cong(T.WhenOut, T.WhenOut, ww => T.when.time.only(ww), T.when.clock.mm(T.take.n(2n,
          dx(M6.dq(mi)) <> dx(mi) <>
        ':' <> dx(M6.dq(ss)) <> dx(ss) <> M2.tl(tfr(fr, [])), 0, True{}), hh, T.Date{0, 1, 1}),
        T.WSome{T.WLocal{T.Date{0, 1, 1}, T.Clock{hh, mi, ss, fr}}},
        Equal.trans(T.WhenOut, T.when.clock.mm(T.take.n(2n, dx(M6.dq(mi)) <> dx(mi) <> ':' <> dx(M6.dq(ss)) <> dx(ss) <>
          M2.tl(tfr(fr, [])), 0, True{}), hh, T.Date{0, 1, 1}),
          T.when.frac(M2.tl(tfr(fr, [])), T.Clock{hh, mi, ss, ""}, T.Date{0, 1, 1}),
          T.WSome{T.WLocal{T.Date{0, 1, 1}, T.Clock{hh, mi, ss, fr}}},
          clk.mm(uu, hh, mi, ss, M2.tl(tfr(fr, [])), T.Date{0, 1, 1}, wc.mi(hh, mi, ss, fr, hc), wc.s(hh, mi, ss, fr,
              hc),
            rng0(hh, 23, wc.h(hh, mi, ss, fr, hc))),
          frac.all(fr, hh, mi, ss, [], T.Date{0, 1, 1}, wc.fr(hh, mi, ss, fr, hc), {==})))))

# a well-formed datetime's tokens are read as the datetime
def read.all(
  +uu: Unit,
  ww: T.When,
  +hw: {T.wf.when(ww) == True{} : Bool}
) -> {T.when.read(M2.tl(tks(ww))) == T.WSome{ww} : T.WhenOut}:
  match ww:
    case T.WOff{T.Date{+yy, +mo, +dd}, T.Clock{+hh, +mi, +ss, +fr}, +zz}:
      +hd = {Eq.and.left(T.wf.date(T.Date{yy, mo, dd}), Bool.and(T.wf.clock(T.Clock{hh, mi, ss, fr}), T.wf.zone(zz)),
        hw) : {T.wf.date(T.Date{yy, mo, dd}) == True{} : Bool}}
      +hr = {Eq.and.right(T.wf.date(T.Date{yy, mo, dd}), Bool.and(T.wf.clock(T.Clock{hh, mi, ss, fr}),
        T.wf.zone(zz)), hw) : {Bool.and(T.wf.clock(T.Clock{hh, mi, ss, fr}), T.wf.zone(zz)) == True{} : Bool}}
      Equal.trans(T.WhenOut, T.when.read(M2.tl(tdate(yy, mo, dd, M3.TC{'T'} <> tclock(hh, mi, ss, tfr(fr,
          tzone(zz)))))),
        T.when.zone(M2.tl(tzone(zz)), T.Clock{hh, mi, ss, fr}, T.Date{yy, mo, dd}),
        T.WSome{T.WOff{T.Date{yy, mo, dd}, T.Clock{hh, mi, ss, fr}, zz}},
        rd.dc(uu, yy, mo, dd, hh, mi, ss, fr, tzone(zz), hd, Eq.and.left(T.wf.clock(T.Clock{hh, mi, ss, fr}),
          T.wf.zone(zz), hr), zok.z(zz)),
        zn(uu, zz, T.Clock{hh, mi, ss, fr}, T.Date{yy, mo, dd}, Eq.and.right(T.wf.clock(T.Clock{hh, mi, ss, fr}),
          T.wf.zone(zz), hr)))
    case T.WLocal{T.Date{+yy, +mo, +dd}, T.Clock{+hh, +mi, +ss, +fr}}:
      rd.dc(uu, yy, mo, dd, hh, mi, ss, fr, [], Eq.and.left(T.wf.date(T.Date{yy, mo, dd}),
        T.wf.clock(T.Clock{hh, mi, ss, fr}), hw), Eq.and.right(T.wf.date(T.Date{yy, mo, dd}),
        T.wf.clock(T.Clock{hh, mi, ss, fr}), hw), {==})
    case T.WDate{T.Date{+yy, +mo, +dd}}:
      rd.date(uu, yy, mo, dd, [], hw)
    case T.WTime{T.Clock{+hh, +mi, +ss, +fr}}:
      rd.time(uu, hh, mi, ss, fr, hw)

# The classifier routes a datetime's text to the datetime scan: its first
# character is a digit, so no special; a dash after its year, or a colon
# after its hour, makes it a datetime; and it holds no exponent mark.

# an `or` with a True right half
def wor.t(aa: Bool) -> {T.word.or(aa, True{}) == True{} : Bool}:
  match aa:
    case True{}:
      {==}
    case False{}:
      {==}

# a text that starts with four digits and a dash is routed to the datetime scan
def dsh(
  +x1: U32,
  +x2: U32,
  +x3: U32,
  +x4: U32,
  +rest: List<&2, Char>
) -> {T.word.or(T.word.colon(dx(x1) <> dx(x2) <> dx(x3) <> dx(x4) <> '-' <> rest), T.word.dash(dx(x1) <> dx(x2) <>
  dx(x3) <> dx(x4) <> '-' <> rest, True{})) == True{} : Bool}:
  Equal.trans(Bool, T.word.or(T.word.colon(dx(x1) <> dx(x2) <> dx(x3) <> dx(x4) <> '-' <> rest),
    T.word.dash(dx(x1) <> dx(x2) <> dx(x3) <> dx(x4) <> '-' <> rest, True{})),
    T.word.or(T.word.colon(dx(x1) <> dx(x2) <> dx(x3) <> dx(x4) <> '-' <> rest), True{}), True{},
    Equal.cong(Bool, Bool, bb => T.word.or(T.word.colon(dx(x1) <> dx(x2) <> dx(x3) <> dx(x4) <> '-' <> rest), bb),
      T.word.dash(dx(x1) <> dx(x2) <> dx(x3) <> dx(x4) <> '-' <> rest, True{}), True{},
      Equal.trans(Bool, T.word.or(Char.is_eq(dx(x2), '-'), T.word.dash(dx(x3) <> dx(x4) <> '-' <> rest, False{})),
        T.word.or(Char.is_eq(dx(x2), '-'), True{}), True{},
        Equal.cong(Bool, Bool, bb => T.word.or(Char.is_eq(dx(x2), '-'), bb),
          T.word.dash(dx(x3) <> dx(x4) <> '-' <> rest, False{}), True{},
          Equal.trans(Bool, T.word.or(Char.is_eq(dx(x3), '-'), T.word.dash(dx(x4) <> '-' <> rest, False{})),
            T.word.or(Char.is_eq(dx(x3), '-'), True{}), True{},
            Equal.cong(Bool, Bool, bb => T.word.or(Char.is_eq(dx(x3), '-'), bb),
              T.word.dash(dx(x4) <> '-' <> rest, False{}), True{}, wor.t(Char.is_eq(dx(x4), '-'))),
            wor.t(Char.is_eq(dx(x3), '-')))),
        wor.t(Char.is_eq(dx(x2), '-')))),
    wor.t(T.word.colon(dx(x1) <> dx(x2) <> dx(x3) <> dx(x4) <> '-' <> rest)))

# a text that starts with two digits and a colon is routed to the datetime
# scan
def tcl(
  +x1: U32,
  +x2: U32,
  +rest: List<&2, Char>
) -> {T.word.or(T.word.colon(dx(x1) <> dx(x2) <> ':' <> rest), T.word.dash(dx(x1) <> dx(x2) <> ':' <> rest, True{})) ==
  True{} : Bool}:
  Equal.cong(Bool, Bool, bb => T.word.or(bb, T.word.dash(dx(x1) <> dx(x2) <> ':' <> rest, True{})),
    T.word.colon(dx(x1) <> dx(x2) <> ':' <> rest), True{},
    Equal.trans(Bool, T.word.or(Char.is_eq(dx(x1), ':'), T.word.colon(dx(x2) <> ':' <> rest)),
      T.word.or(Char.is_eq(dx(x1), ':'), True{}), True{},
      Equal.cong(Bool, Bool, bb => T.word.or(Char.is_eq(dx(x1), ':'), bb), T.word.colon(dx(x2) <> ':' <> rest), True{},
        wor.t(Char.is_eq(dx(x2), ':'))),
      wor.t(Char.is_eq(dx(x1), ':'))))

# a digit is a character a datetime keeps
def dg.dtc(cc: Char, hc: {Char.is_digit(cc) == True{} : Bool}) -> {M4.dtc(cc) == True{} : Bool}:
  M3.dg.elim(zz => {M4.dtc(zz) == True{} : Bool}, cc, hc, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# a fraction's digits are characters a datetime keeps
def tok.tcs(
  fr: String,
  +zs: List<&2, M3.Tk>,
  +hd: {T.wf.digits(fr) == True{} : Bool},
  +hz: {tok(zs) == True{} : Bool}
) -> {tok(tcs(fr, zs)) == True{} : Bool}:
  match fr:
    case SNil{}:
      hz
    case SCon{+cc, +tt}:
      M5.and.tt(M4.dtc(cc), tok(tcs(tt, zs)), dg.dtc(cc, M3.then.l(Char.is_digit(cc), tt, hd)),
        tok.tcs(tt, zs, M3.then.r(Char.is_digit(cc), tt, hd), hz))

# and so is its dot
def tok.fr(
  fr: String,
  +zs: List<&2, M3.Tk>,
  +hd: {T.wf.digits(fr) == True{} : Bool},
  +hz: {tok(zs) == True{} : Bool}
) -> {tok(tfr(fr, zs)) == True{} : Bool}:
  match fr:
    case SNil{}:
      hz
    case SCon{+cc, +tt}:
      tok.tcs(SCon{cc, tt}, zs, hd, hz)

# a zone is characters a datetime keeps
def tok.z(zz: T.Zone) -> {tok(tzone(zz)) == True{} : Bool}:
  match zz:
    case T.Zulu{}:
      {==}
    case T.Shift{sg, _h, _m}:
      match sg:
        case T.Plus{}:
          {==}
        case T.Minus{}:
          {==}

# a well-formed datetime's tokens are characters a datetime keeps
def tok.all(ww: T.When, +hw: {T.wf.when(ww) == True{} : Bool}) -> {tok(tks(ww)) == True{} : Bool}:
  match ww:
    case T.WOff{T.Date{yy, mo, dd}, T.Clock{+hh, +mi, +ss, +fr}, +zz}:
      tok.fr(fr, tzone(zz), wc.fr(hh, mi, ss, fr, Eq.and.left(T.wf.clock(T.Clock{hh, mi, ss, fr}), T.wf.zone(zz),
        Eq.and.right(T.wf.date(T.Date{yy, mo, dd}), Bool.and(T.wf.clock(T.Clock{hh, mi, ss, fr}), T.wf.zone(zz)), hw))),
        tok.z(zz))
    case T.WLocal{T.Date{yy, mo, dd}, T.Clock{+hh, +mi, +ss, +fr}}:
      tok.fr(fr, [], wc.fr(hh, mi, ss, fr, Eq.and.right(T.wf.date(T.Date{yy, mo, dd}),
        T.wf.clock(T.Clock{hh, mi, ss, fr}), hw)), {==})
    case T.WDate{T.Date{_y, _m, _d}}:
      {==}
    case T.WTime{T.Clock{+hh, +mi, +ss, +fr}}:
      tok.fr(fr, [], wc.fr(hh, mi, ss, fr, hw), {==})

# a text routed to the datetime scan, read as a datetime, is classified as it
def wv.gen(
  +x0: U32,
  +rest: List<&2, Char>,
  +ww: T.When,
  hdate: {T.word.or(T.word.colon(dx(x0) <> rest), T.word.dash(dx(x0) <> rest, True{})) == True{} : Bool},
  hee: {T.word.ee(dx(x0) <> rest) == False{} : Bool},
  hrd: {T.when.read(dx(x0) <> rest) == T.WSome{ww} : T.WhenOut}
) -> {T.word.val(dx(x0) <> rest) == T.GotVal{T.VWhen{ww}} : T.Got}:
  Equal.trans(T.Got, T.word.val.pick(T.word.special(dx(x0)), dx(x0) <> rest),
    T.word.route(T.GotBad{""}, T.word.or(T.word.colon(dx(x0) <> rest), T.word.dash(dx(x0) <> rest, True{})),
      dx(x0) <> rest), T.GotVal{T.VWhen{ww}},
    Equal.cong(Bool, T.Got, bb => T.word.val.pick(bb, dx(x0) <> rest), T.word.special(dx(x0)), False{},
      dd.nospec(x0)),
    Equal.trans(T.Got,
      T.word.route(T.GotBad{""}, T.word.or(T.word.colon(dx(x0) <> rest), T.word.dash(dx(x0) <> rest, True{})),
        dx(x0) <> rest),
      T.word.route.date(T.word.as_date(True{}, T.word.ee(dx(x0) <> rest)), dx(x0) <> rest), T.GotVal{T.VWhen{ww}},
      Equal.cong(Bool, T.Got, bb => T.word.route(T.GotBad{""}, bb, dx(x0) <> rest),
        T.word.or(T.word.colon(dx(x0) <> rest), T.word.dash(dx(x0) <> rest, True{})), True{}, hdate),
      Equal.trans(T.Got, T.word.route.date(T.word.as_date(True{}, T.word.ee(dx(x0) <> rest)), dx(x0) <> rest),
        T.word.from.when(T.when.read(dx(x0) <> rest)), T.GotVal{T.VWhen{ww}},
        Equal.cong(Bool, T.Got, bb => T.word.route.date(T.word.as_date(True{}, bb), dx(x0) <> rest),
          T.word.ee(dx(x0) <> rest), False{}, hee),
        Equal.cong(T.WhenOut, T.Got, wo => T.word.from.when(wo), T.when.read(dx(x0) <> rest), T.WSome{ww}, hrd))))

# a well-formed datetime's tokens are classified as the datetime
def wv.tks(
  ww: T.When,
  +hw: {T.wf.when(ww) == True{} : Bool}
) -> {T.word.val(M2.tl(tks(ww))) == T.GotVal{T.VWhen{ww}} : T.Got}:
  match ww:
    case T.WOff{T.Date{+yy, +mo, +dd}, T.Clock{+hh, +mi, +ss, +fr}, +zz}:
      wv.gen(M6.dq(M6.dq(M6.dq(yy))),
          M2.tl(M3.TD{M6.dq(M6.dq(yy))} <> M3.TD{M6.dq(yy)} <> M3.TD{yy} <> M3.TC{'-'} <> M3.TD{M6.dq(mo)} <>
            M3.TD{mo} <> M3.TC{'-'} <>
        M3.TD{M6.dq(dd)} <> M3.TD{dd} <> M3.TC{'T'} <> tclock(hh, mi, ss, tfr(fr, tzone(zz)))),
        T.WOff{T.Date{yy, mo, dd}, T.Clock{hh, mi, ss, fr}, zz},
        dsh(M6.dq(M6.dq(M6.dq(yy))), M6.dq(M6.dq(yy)), M6.dq(yy), yy,
            M2.tl(M3.TD{M6.dq(mo)} <> M3.TD{mo} <> M3.TC{'-'} <> M3.TD{M6.dq(dd)} <> M3.TD{dd} <>
          M3.TC{'T'} <> tclock(hh, mi, ss, tfr(fr, tzone(zz))))),
        tk.ee(tks(T.WOff{T.Date{yy, mo, dd}, T.Clock{hh, mi, ss, fr}, zz}),
          tok.all(T.WOff{T.Date{yy, mo, dd}, T.Clock{hh, mi, ss, fr}, zz}, hw)),
        read.all(Unit{}, T.WOff{T.Date{yy, mo, dd}, T.Clock{hh, mi, ss, fr}, zz}, hw))
    case T.WLocal{T.Date{+yy, +mo, +dd}, T.Clock{+hh, +mi, +ss, +fr}}:
      wv.gen(M6.dq(M6.dq(M6.dq(yy))),
          M2.tl(M3.TD{M6.dq(M6.dq(yy))} <> M3.TD{M6.dq(yy)} <> M3.TD{yy} <> M3.TC{'-'} <> M3.TD{M6.dq(mo)} <>
            M3.TD{mo} <> M3.TC{'-'} <>
        M3.TD{M6.dq(dd)} <> M3.TD{dd} <> M3.TC{'T'} <> tclock(hh, mi, ss, tfr(fr, []))),
        T.WLocal{T.Date{yy, mo, dd}, T.Clock{hh, mi, ss, fr}},
        dsh(M6.dq(M6.dq(M6.dq(yy))), M6.dq(M6.dq(yy)), M6.dq(yy), yy,
            M2.tl(M3.TD{M6.dq(mo)} <> M3.TD{mo} <> M3.TC{'-'} <> M3.TD{M6.dq(dd)} <> M3.TD{dd} <>
          M3.TC{'T'} <> tclock(hh, mi, ss, tfr(fr, [])))),
        tk.ee(tks(T.WLocal{T.Date{yy, mo, dd}, T.Clock{hh, mi, ss, fr}}),
          tok.all(T.WLocal{T.Date{yy, mo, dd}, T.Clock{hh, mi, ss, fr}}, hw)),
        read.all(Unit{}, T.WLocal{T.Date{yy, mo, dd}, T.Clock{hh, mi, ss, fr}}, hw))
    case T.WDate{T.Date{+yy, +mo, +dd}}:
      wv.gen(M6.dq(M6.dq(M6.dq(yy))),
          M2.tl(M3.TD{M6.dq(M6.dq(yy))} <> M3.TD{M6.dq(yy)} <> M3.TD{yy} <> M3.TC{'-'} <> M3.TD{M6.dq(mo)} <>
            M3.TD{mo} <> M3.TC{'-'} <>
        M3.TD{M6.dq(dd)} <> M3.TD{dd} <> []), T.WDate{T.Date{yy, mo, dd}},
        dsh(M6.dq(M6.dq(M6.dq(yy))), M6.dq(M6.dq(yy)), M6.dq(yy), yy,
            M2.tl(M3.TD{M6.dq(mo)} <> M3.TD{mo} <> M3.TC{'-'} <> M3.TD{M6.dq(dd)} <> M3.TD{dd} <> [])),
        tk.ee(tks(T.WDate{T.Date{yy, mo, dd}}), {==}), read.all(Unit{}, T.WDate{T.Date{yy, mo, dd}}, hw))
    case T.WTime{T.Clock{+hh, +mi, +ss, +fr}}:
      wv.gen(M6.dq(hh),
          M2.tl(M3.TD{hh} <> M3.TC{':'} <> M3.TD{M6.dq(mi)} <> M3.TD{mi} <> M3.TC{':'} <> M3.TD{M6.dq(ss)} <>
            M3.TD{ss} <> tfr(fr, [])),
        T.WTime{T.Clock{hh, mi, ss, fr}},
        tcl(M6.dq(hh), hh,
            M2.tl(M3.TD{M6.dq(mi)} <> M3.TD{mi} <> M3.TC{':'} <> M3.TD{M6.dq(ss)} <> M3.TD{ss} <> tfr(fr, []))),
        tk.ee(tks(T.WTime{T.Clock{hh, mi, ss, fr}}), tok.all(T.WTime{T.Clock{hh, mi, ss, fr}}, hw)),
        read.all(Unit{}, T.WTime{T.Clock{hh, mi, ss, fr}}, hw))

def L1.when_word(w, h):
  Equal.trans(T.Got, T.word.val(String.to_list(T.when.text(w))), T.word.val(M2.tl(tks(w))), T.GotVal{T.VWhen{w}},
    Equal.cong(String, T.Got, ss => T.word.val(String.to_list(ss)), T.when.text(w), M2.tstr(tks(w)),
      when.eq(Unit{}, w, h)), wv.tks(w, h))

# tokens that start with a digit are a bare value
def wch.gen(
  +x0: U32,
  +ts: List<&2, M3.Tk>,
  +hh: {tok(ts) == True{} : Bool}
) -> {L2.word.chars(M2.tstr(M3.TD{x0} <> ts)) == True{} : Bool}:
  M5.and.tt(D1.word.first(dx(x0)), L2.word.rest(M2.tstr(ts)), dd.first(x0), tk.rest(ts, hh))

# a well-formed datetime's tokens are a bare value
def wch.all(ww: T.When, +hw: {T.wf.when(ww) == True{} : Bool}) -> {L2.word.chars(M2.tstr(tks(ww))) == True{} : Bool}:
  match ww:
    case T.WOff{T.Date{+yy, +mo, +dd}, T.Clock{+hh, +mi, +ss, +fr}, +zz}:
      wch.gen(M6.dq(M6.dq(M6.dq(yy))),
          M3.TD{M6.dq(M6.dq(yy))} <> M3.TD{M6.dq(yy)} <> M3.TD{yy} <> M3.TC{'-'} <> M3.TD{M6.dq(mo)} <> M3.TD{mo} <>
            M3.TC{'-'} <>
        M3.TD{M6.dq(dd)} <> M3.TD{dd} <> M3.TC{'T'} <> tclock(hh, mi, ss, tfr(fr, tzone(zz))),
        tok.all(T.WOff{T.Date{yy, mo, dd}, T.Clock{hh, mi, ss, fr}, zz}, hw))
    case T.WLocal{T.Date{+yy, +mo, +dd}, T.Clock{+hh, +mi, +ss, +fr}}:
      wch.gen(M6.dq(M6.dq(M6.dq(yy))),
          M3.TD{M6.dq(M6.dq(yy))} <> M3.TD{M6.dq(yy)} <> M3.TD{yy} <> M3.TC{'-'} <> M3.TD{M6.dq(mo)} <> M3.TD{mo} <>
            M3.TC{'-'} <>
        M3.TD{M6.dq(dd)} <> M3.TD{dd} <> M3.TC{'T'} <> tclock(hh, mi, ss, tfr(fr, [])),
        tok.all(T.WLocal{T.Date{yy, mo, dd}, T.Clock{hh, mi, ss, fr}}, hw))
    case T.WDate{T.Date{+yy, +mo, +dd}}:
      wch.gen(M6.dq(M6.dq(M6.dq(yy))),
          M3.TD{M6.dq(M6.dq(yy))} <> M3.TD{M6.dq(yy)} <> M3.TD{yy} <> M3.TC{'-'} <> M3.TD{M6.dq(mo)} <> M3.TD{mo} <>
            M3.TC{'-'} <>
        M3.TD{M6.dq(dd)} <> M3.TD{dd} <> [], {==})
    case T.WTime{T.Clock{+hh, +mi, +ss, +fr}}:
      wch.gen(M6.dq(hh),
          M3.TD{hh} <> M3.TC{':'} <> M3.TD{M6.dq(mi)} <> M3.TD{mi} <> M3.TC{':'} <> M3.TD{M6.dq(ss)} <> M3.TD{ss} <>
            tfr(fr, []),
        tok.all(T.WTime{T.Clock{hh, mi, ss, fr}}, hw))
