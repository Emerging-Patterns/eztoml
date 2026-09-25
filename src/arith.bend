# eztoml/arith: U32 arithmetic read as Nats, ported from ezjson's proofs of
# JSON-TREE-6. A U32 sum or a U32 times ten, with its overflow counted in
# multiples of 2^32, is the Nat sum or product; a U32 over ten and modulo ten
# are the Nat quotient and remainder; and a U32 comparison is the Nat one. The
# round trip's datetime read-back uses them to read a year's digits back.
import Base

# Unit for True, Empty for False: tells them apart
def true_ty(bb: Bool) -> Type:
  match bb:
    case False{}:
      Empty
    case True{}:
      Unit

# True is never False

# True is never False
law true_false:
  for e: {True{} == False{} : Bool}
  Empty

# the proof of the law above
def true_false(e):
  %e : true_ty(_)
  Unit{}

# Unit for False, Empty for True
def false_ty(bb: Bool) -> Type:
  match bb:
    case False{}:
      Unit
    case True{}:
      Empty

# False is never True

# False is never True
law false_true:
  for e: {False{} == True{} : Bool}
  Empty

# the proof of the law above
def false_true(e):
  %e : false_ty(_)
  Unit{}

# both sides of a true and: the left

# the predecessor of a Nat
def npred(nn: Nat) -> Nat:
  match nn:
    case 0n:
      0n
    case 1n+(+pp):
      pp

# adding 0 on the right

# adding 0 on the right
law nat_add_zero:
  for +aa: Nat
  {Nat.add(aa, 0n) == aa : Nat}

# the proof of the law above
def nat_add_zero(aa):
  match aa:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.add(pp, 0n), pp, nat_add_zero(pp))

# adding one more on the right

# adding one more on the right
law nat_add_succ:
  for +aa: Nat
  for +bb: Nat
  {Nat.add(aa, 1n+bb) == 1n+Nat.add(aa, bb) : Nat}

# the proof of the law above
def nat_add_succ(aa, bb):
  match aa:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.add(pp, 1n+bb), 1n+Nat.add(pp, bb), nat_add_succ(pp, bb))

# addition commutes

# addition commutes
law nat_add_comm:
  for +aa: Nat
  for +bb: Nat
  {Nat.add(aa, bb) == Nat.add(bb, aa) : Nat}

# the proof of the law above
def nat_add_comm(aa, bb):
  match aa:
    case 0n:
      Equal.sym(Nat, Nat.add(bb, 0n), bb, nat_add_zero(bb))
    case 1n+(+pp):
      Equal.trans(Nat, 1n+Nat.add(pp, bb), 1n+Nat.add(bb, pp), Nat.add(bb, 1n+pp),
        Equal.cong(Nat, Nat, xx => 1n+xx, Nat.add(pp, bb), Nat.add(bb, pp), nat_add_comm(pp, bb)),
        Equal.sym(Nat, Nat.add(bb, 1n+pp), 1n+Nat.add(bb, pp), nat_add_succ(bb, pp)))

# addition associates

# addition associates
law nat_add_assoc:
  for +aa: Nat
  for +bb: Nat
  for +cc: Nat
  {Nat.add(Nat.add(aa, bb), cc) == Nat.add(aa, Nat.add(bb, cc)) : Nat}

# the proof of the law above
def nat_add_assoc(aa, bb, cc):
  match aa:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.add(Nat.add(pp, bb), cc), Nat.add(pp, Nat.add(bb, cc)),
        nat_add_assoc(pp, bb, cc))

# the first two of three addends swap

# the first two of three addends swap
law nat_add_lcomm:
  for +aa: Nat
  for +bb: Nat
  for +cc: Nat
  {Nat.add(aa, Nat.add(bb, cc)) == Nat.add(bb, Nat.add(aa, cc)) : Nat}

# the proof of the law above
def nat_add_lcomm(aa, bb, cc):
  Equal.trans(Nat, Nat.add(aa, Nat.add(bb, cc)), Nat.add(Nat.add(aa, bb), cc), Nat.add(bb, Nat.add(aa, cc)),
    Equal.sym(Nat, Nat.add(Nat.add(aa, bb), cc), Nat.add(aa, Nat.add(bb, cc)), nat_add_assoc(aa, bb, cc)),
    Equal.trans(Nat, Nat.add(Nat.add(aa, bb), cc), Nat.add(Nat.add(bb, aa), cc), Nat.add(bb, Nat.add(aa, cc)),
      Equal.cong(Nat, Nat, xx => Nat.add(xx, cc), Nat.add(aa, bb), Nat.add(bb, aa), nat_add_comm(aa, bb)),
      nat_add_assoc(bb, aa, cc)))

# a common left addend cancels

# a common left addend cancels
law nat_add_cancel:
  for +aa: Nat
  for +bb: Nat
  for +cc: Nat
  for h: {Nat.add(aa, bb) == Nat.add(aa, cc) : Nat}
  {bb == cc : Nat}

# the proof of the law above
def nat_add_cancel(aa, bb, cc, h):
  match aa:
    case 0n:
      h
    case 1n+(+pp):
      nat_add_cancel(pp, bb, cc, Equal.cong(Nat, Nat, xx => npred(xx), 1n+Nat.add(pp, bb), 1n+Nat.add(pp, cc), h))

# doubling is adding to itself

# doubling is adding to itself
law nat_double:
  for +aa: Nat
  {Nat.double(aa) == Nat.add(aa, aa) : Nat}

# the proof of the law above
def nat_double(aa):
  match aa:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.trans(Nat, 2n+Nat.double(pp), 2n+Nat.add(pp, pp), 1n+Nat.add(pp, 1n+pp),
        Equal.cong(Nat, Nat, xx => 2n+xx, Nat.double(pp), Nat.add(pp, pp), nat_double(pp)),
        Equal.cong(Nat, Nat, xx => 1n+xx, 1n+Nat.add(pp, pp), Nat.add(pp, 1n+pp),
          Equal.sym(Nat, Nat.add(pp, 1n+pp), 1n+Nat.add(pp, pp), nat_add_succ(pp, pp))))

# doubling a sum doubles each addend

# doubling a sum doubles each addend
law nat_double_add:
  for +aa: Nat
  for +bb: Nat
  {Nat.double(Nat.add(aa, bb)) == Nat.add(Nat.double(aa), Nat.double(bb)) : Nat}

# the proof of the law above
def nat_double_add(aa, bb):
  match aa:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.cong(Nat, Nat, xx => 2n+xx, Nat.double(Nat.add(pp, bb)), Nat.add(Nat.double(pp), Nat.double(bb)),
        nat_double_add(pp, bb))

# multiplication distributes over a sum on the left

# multiplication distributes over a sum on the left
law nat_mul_add_r:
  for +aa: Nat
  for +bb: Nat
  for +cc: Nat
  {Nat.mul(Nat.add(aa, bb), cc) == Nat.add(Nat.mul(aa, cc), Nat.mul(bb, cc)) : Nat}

# the proof of the law above
def nat_mul_add_r(aa, bb, cc):
  match aa:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.trans(Nat, Nat.add(cc, Nat.mul(Nat.add(pp, bb), cc)),
        Nat.add(cc, Nat.add(Nat.mul(pp, cc), Nat.mul(bb, cc))),
        Nat.add(Nat.add(cc, Nat.mul(pp, cc)), Nat.mul(bb, cc)),
        Equal.cong(Nat, Nat, xx => Nat.add(cc, xx), Nat.mul(Nat.add(pp, bb), cc),
          Nat.add(Nat.mul(pp, cc), Nat.mul(bb, cc)), nat_mul_add_r(pp, bb, cc)),
        Equal.sym(Nat, Nat.add(Nat.add(cc, Nat.mul(pp, cc)), Nat.mul(bb, cc)),
          Nat.add(cc, Nat.add(Nat.mul(pp, cc), Nat.mul(bb, cc))), nat_add_assoc(cc, Nat.mul(pp, cc), Nat.mul(bb, cc))))

# multiplication distributes over a sum on the right

# multiplication distributes over a sum on the right
law nat_mul_add_l:
  for +aa: Nat
  for +bb: Nat
  for +cc: Nat
  {Nat.mul(aa, Nat.add(bb, cc)) == Nat.add(Nat.mul(aa, bb), Nat.mul(aa, cc)) : Nat}

# the proof of the law above
def nat_mul_add_l(aa, bb, cc):
  match aa:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.trans(Nat, Nat.add(Nat.add(bb, cc), Nat.mul(pp, Nat.add(bb, cc))),
        Nat.add(Nat.add(bb, cc), Nat.add(Nat.mul(pp, bb), Nat.mul(pp, cc))), Nat.add(Nat.add(bb, Nat.mul(pp, bb)),
          Nat.add(cc, Nat.mul(pp, cc))),
        Equal.cong(Nat, Nat, xx => Nat.add(Nat.add(bb, cc), xx), Nat.mul(pp, Nat.add(bb, cc)),
          Nat.add(Nat.mul(pp, bb), Nat.mul(pp, cc)), nat_mul_add_l(pp, bb, cc)),
        Equal.trans(Nat, Nat.add(Nat.add(bb, cc), Nat.add(Nat.mul(pp, bb), Nat.mul(pp, cc))), Nat.add(Nat.mul(pp, bb),
          Nat.add(Nat.mul(pp, cc), Nat.add(bb, cc))), Nat.add(Nat.add(bb, Nat.mul(pp, bb)), Nat.add(cc, Nat.mul(pp,
          cc))), Equal.trans(Nat, Nat.add(Nat.add(bb, cc), Nat.add(Nat.mul(pp, bb), Nat.mul(pp, cc))),
          Nat.add(Nat.add(bb, cc), Nat.add(Nat.mul(pp, bb), Nat.mul(pp, cc))), Nat.add(Nat.mul(pp, bb),
          Nat.add(Nat.mul(pp, cc), Nat.add(bb, cc))), Equal.cong(Nat, Nat, z1 => Nat.add(z1, Nat.add(Nat.mul(pp, bb),
          Nat.mul(pp, cc))), Nat.add(bb, cc), Nat.add(bb, cc), {==}), Equal.trans(Nat, Nat.add(Nat.add(bb, cc),
          Nat.add(Nat.mul(pp, bb), Nat.mul(pp, cc))), Nat.add(Nat.add(bb, cc), Nat.add(Nat.mul(pp, bb), Nat.mul(pp,
          cc))), Nat.add(Nat.mul(pp, bb), Nat.add(Nat.mul(pp, cc), Nat.add(bb, cc))), Equal.cong(Nat, Nat,
          z2 => Nat.add(Nat.add(bb, cc), z2), Nat.add(Nat.mul(pp, bb), Nat.mul(pp, cc)), Nat.add(Nat.mul(pp, bb),
          Nat.mul(pp, cc)), {==}), Equal.trans(Nat, Nat.add(Nat.add(bb, cc), Nat.add(Nat.mul(pp, bb), Nat.mul(pp,
          cc))), Nat.add(bb, Nat.add(cc, Nat.add(Nat.mul(pp, bb), Nat.mul(pp, cc)))), Nat.add(Nat.mul(pp, bb),
          Nat.add(Nat.mul(pp, cc), Nat.add(bb, cc))), nat_add_assoc(bb, cc, Nat.add(Nat.mul(pp, bb), Nat.mul(pp, cc))),
          Equal.trans(Nat, Nat.add(bb, Nat.add(cc, Nat.add(Nat.mul(pp, bb), Nat.mul(pp, cc)))), Nat.add(bb,
          Nat.add(Nat.mul(pp, bb), Nat.add(Nat.mul(pp, cc), cc))), Nat.add(Nat.mul(pp, bb), Nat.add(Nat.mul(pp, cc),
          Nat.add(bb, cc))), Equal.cong(Nat, Nat, z4 => Nat.add(bb, z4), Nat.add(cc, Nat.add(Nat.mul(pp, bb),
          Nat.mul(pp, cc))), Nat.add(Nat.mul(pp, bb), Nat.add(Nat.mul(pp, cc), cc)), Equal.trans(Nat, Nat.add(cc,
          Nat.add(Nat.mul(pp, bb), Nat.mul(pp, cc))), Nat.add(Nat.mul(pp, bb), Nat.add(cc, Nat.mul(pp, cc))),
          Nat.add(Nat.mul(pp, bb), Nat.add(Nat.mul(pp, cc), cc)), nat_add_lcomm(cc, Nat.mul(pp, bb), Nat.mul(pp, cc)),
          Equal.cong(Nat, Nat, z3 => Nat.add(Nat.mul(pp, bb), z3), Nat.add(cc, Nat.mul(pp, cc)), Nat.add(Nat.mul(pp,
          cc), cc), nat_add_comm(cc, Nat.mul(pp, cc))))), Equal.trans(Nat, Nat.add(bb, Nat.add(Nat.mul(pp, bb),
          Nat.add(Nat.mul(pp, cc), cc))), Nat.add(Nat.mul(pp, bb), Nat.add(bb, Nat.add(Nat.mul(pp, cc), cc))),
          Nat.add(Nat.mul(pp, bb), Nat.add(Nat.mul(pp, cc), Nat.add(bb, cc))), nat_add_lcomm(bb, Nat.mul(pp, bb),
          Nat.add(Nat.mul(pp, cc), cc)), Equal.cong(Nat, Nat, z5 => Nat.add(Nat.mul(pp, bb), z5), Nat.add(bb,
          Nat.add(Nat.mul(pp, cc), cc)), Nat.add(Nat.mul(pp, cc), Nat.add(bb, cc)), nat_add_lcomm(bb, Nat.mul(pp, cc),
          cc))))))), Equal.sym(Nat, Nat.add(Nat.add(bb, Nat.mul(pp, bb)), Nat.add(cc, Nat.mul(pp, cc))),
          Nat.add(Nat.mul(pp, bb), Nat.add(Nat.mul(pp, cc), Nat.add(bb, cc))), Equal.trans(Nat, Nat.add(Nat.add(bb,
          Nat.mul(pp, bb)), Nat.add(cc, Nat.mul(pp, cc))), Nat.add(Nat.add(Nat.mul(pp, bb), bb), Nat.add(cc,
          Nat.mul(pp, cc))), Nat.add(Nat.mul(pp, bb), Nat.add(Nat.mul(pp, cc), Nat.add(bb, cc))), Equal.cong(Nat, Nat,
          z6 => Nat.add(z6, Nat.add(cc, Nat.mul(pp, cc))), Nat.add(bb, Nat.mul(pp, bb)), Nat.add(Nat.mul(pp, bb), bb),
          nat_add_comm(bb, Nat.mul(pp, bb))), Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(pp, bb), bb), Nat.add(cc,
          Nat.mul(pp, cc))), Nat.add(Nat.add(Nat.mul(pp, bb), bb), Nat.add(Nat.mul(pp, cc), cc)), Nat.add(Nat.mul(pp,
          bb), Nat.add(Nat.mul(pp, cc), Nat.add(bb, cc))), Equal.cong(Nat, Nat, z7 => Nat.add(Nat.add(Nat.mul(pp, bb),
          bb), z7), Nat.add(cc, Nat.mul(pp, cc)), Nat.add(Nat.mul(pp, cc), cc), nat_add_comm(cc, Nat.mul(pp, cc))),
          Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(pp, bb), bb), Nat.add(Nat.mul(pp, cc), cc)), Nat.add(Nat.mul(pp,
          bb), Nat.add(bb, Nat.add(Nat.mul(pp, cc), cc))), Nat.add(Nat.mul(pp, bb), Nat.add(Nat.mul(pp, cc),
          Nat.add(bb, cc))), nat_add_assoc(Nat.mul(pp, bb), bb, Nat.add(Nat.mul(pp, cc), cc)), Equal.cong(Nat, Nat,
          z8 => Nat.add(Nat.mul(pp, bb), z8), Nat.add(bb, Nat.add(Nat.mul(pp, cc), cc)), Nat.add(Nat.mul(pp, cc),
          Nat.add(bb, cc)), nat_add_lcomm(bb, Nat.mul(pp, cc), cc))))))))

# twice a on the left

# twice a on the left
law nat_mul_double_l:
  for +aa: Nat
  for +bb: Nat
  {Nat.mul(Nat.double(aa), bb) == Nat.double(Nat.mul(aa, bb)) : Nat}

# the proof of the law above
def nat_mul_double_l(aa, bb):
  Equal.trans(Nat, Nat.mul(Nat.double(aa), bb), Nat.mul(Nat.add(aa, aa), bb), Nat.double(Nat.mul(aa, bb)),
    Equal.cong(Nat, Nat, xx => Nat.mul(xx, bb), Nat.double(aa), Nat.add(aa, aa), nat_double(aa)),
    Equal.trans(Nat, Nat.mul(Nat.add(aa, aa), bb), Nat.add(Nat.mul(aa, bb), Nat.mul(aa, bb)),
      Nat.double(Nat.mul(aa, bb)), nat_mul_add_r(aa, aa, bb),
      Equal.sym(Nat, Nat.double(Nat.mul(aa, bb)), Nat.add(Nat.mul(aa, bb), Nat.mul(aa, bb)),
        nat_double(Nat.mul(aa, bb)))))

# twice b on the right

# twice b on the right
law nat_mul_double_r:
  for +aa: Nat
  for +bb: Nat
  {Nat.mul(aa, Nat.double(bb)) == Nat.double(Nat.mul(aa, bb)) : Nat}

# the proof of the law above
def nat_mul_double_r(aa, bb):
  Equal.trans(Nat, Nat.mul(aa, Nat.double(bb)), Nat.mul(aa, Nat.add(bb, bb)), Nat.double(Nat.mul(aa, bb)),
    Equal.cong(Nat, Nat, xx => Nat.mul(aa, xx), Nat.double(bb), Nat.add(bb, bb), nat_double(bb)),
    Equal.trans(Nat, Nat.mul(aa, Nat.add(bb, bb)), Nat.add(Nat.mul(aa, bb), Nat.mul(aa, bb)),
      Nat.double(Nat.mul(aa, bb)), nat_mul_add_l(aa, bb, bb),
      Equal.sym(Nat, Nat.double(Nat.mul(aa, bb)), Nat.add(Nat.mul(aa, bb), Nat.mul(aa, bb)),
        nat_double(Nat.mul(aa, bb)))))

# multiplication associates

# multiplication associates
law nat_mul_assoc:
  for +aa: Nat
  for +bb: Nat
  for +cc: Nat
  {Nat.mul(Nat.mul(aa, bb), cc) == Nat.mul(aa, Nat.mul(bb, cc)) : Nat}

# the proof of the law above
def nat_mul_assoc(aa, bb, cc):
  match aa:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.trans(Nat, Nat.mul(Nat.add(bb, Nat.mul(pp, bb)), cc),
        Nat.add(Nat.mul(bb, cc), Nat.mul(Nat.mul(pp, bb), cc)), Nat.add(Nat.mul(bb, cc), Nat.mul(pp, Nat.mul(bb, cc))),
        nat_mul_add_r(bb, Nat.mul(pp, bb), cc),
        Equal.cong(Nat, Nat, xx => Nat.add(Nat.mul(bb, cc), xx), Nat.mul(Nat.mul(pp, bb), cc),
          Nat.mul(pp, Nat.mul(bb, cc)), nat_mul_assoc(pp, bb, cc)))

# a multiple of 0 is 0

# 1 times a
law nat_mul_one:
  for +aa: Nat
  {Nat.mul(aa, 1n) == aa : Nat}

# the proof of the law above
def nat_mul_one(aa):
  match aa:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.mul(pp, 1n), pp, nat_mul_one(pp))

# a Nat compares equal to itself

# nothing is below 0
law nat_nlt_zero:
  for +aa: Nat
  {Nat.is_lt(aa, 0n) == False{} : Bool}

# the proof of the law above
def nat_nlt_zero(aa):
  match aa:
    case 0n:
      {==}
    case 1n+_pp:
      {==}

# a sum is never below its left addend

# a sum is never below its left addend
law nat_nlt_add:
  for +aa: Nat
  for +bb: Nat
  {Nat.is_lt(Nat.add(aa, bb), aa) == False{} : Bool}

# the proof of the law above
def nat_nlt_add(aa, bb):
  match aa:
    case 0n:
      nat_nlt_zero(bb)
    case 1n+(+pp):
      nat_nlt_add(pp, bb)

# a sum whose left addend is not below c is not below c

# below c is below c + 1
law nat_lt_succ:
  for +aa: Nat
  for +cc: Nat
  for h: {Nat.is_lt(aa, cc) == True{} : Bool}
  {Nat.is_lt(aa, 1n+cc) == True{} : Bool}

# the proof of the law above
def nat_lt_succ(aa, cc, h):
  match aa cc:
    case 0n 0n:
      {==}
    case 0n 1n+_cp:
      {==}
    case 1n+_ap 0n:
      Empty.absurd({Nat.is_lt(aa, 1n) == True{} : Bool}, false_true(h))
    case 1n+(+ap) 1n+(+cp):
      nat_lt_succ(ap, cp, h)

# below c, the right addend of a sum below c is below c too

# below c, the right addend of a sum below c is below c too
law nat_lt_add_l:
  for +aa: Nat
  for +bb: Nat
  for +cc: Nat
  for h: {Nat.is_lt(Nat.add(aa, bb), cc) == True{} : Bool}
  {Nat.is_lt(bb, cc) == True{} : Bool}

# the proof of the law above
def nat_lt_add_l(aa, bb, cc, h):
  match aa:
    case 0n:
      h
    case 1n+(+ap):
      match cc:
        case 0n:
          Empty.absurd({Nat.is_lt(bb, 0n) == True{} : Bool}, false_true(h))
        case 1n+(+cp):
          nat_lt_succ(bb, cp, nat_lt_add_l(ap, bb, cp, h))

# a Nat below c is below c + y

# the witness of a >= b: a is b and a - b
law nat_ge_ex:
  for +aa: Nat
  for +bb: Nat
  for h: {Nat.is_lt(aa, bb) == False{} : Bool}
  {Nat.add(bb, Nat.sub(aa, bb)) == aa : Nat}

# the proof of the law above
def nat_ge_ex(aa, bb, h):
  match aa bb:
    case 0n 0n:
      {==}
    case 0n 1n+_bp:
      Empty.absurd({Nat.add(bb, Nat.sub(0n, bb)) == 0n : Nat}, true_false(h))
    case 1n+_ap 0n:
      {==}
    case 1n+(+ap) 1n+(+bp):
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.add(bp, Nat.sub(ap, bp)), ap, nat_ge_ex(ap, bp, h))

# a + 1 + z is never a

# a sum a + (c + y) is below c only when false
law nat_nlt_add2:
  for +aa: Nat
  for +cc: Nat
  for +yy: Nat
  {Nat.is_lt(Nat.add(aa, Nat.add(cc, yy)), cc) == False{} : Bool}

# the proof of the law above
def nat_nlt_add2(aa, cc, yy):
  lc = Equal.sym(Nat, Nat.add(aa, Nat.add(cc, yy)), Nat.add(cc, Nat.add(aa, yy)), nat_add_lcomm(aa, cc, yy))
  %lc : {Nat.is_lt(_, cc) == False{} : Bool}
  nat_nlt_add(cc, Nat.add(aa, yy))

# s + k*t is e and e is below t: k is 0, and s is e

# s + k*t is e and e is below t: k is 0, and s is e
law nat_mod_small:
  for +kk: Nat
  for +ss: Nat
  for +ee: Nat
  for +tt: Nat
  for h: {Nat.add(ss, Nat.mul(kk, tt)) == ee : Nat}
  for he: {Nat.is_lt(ee, tt) == True{} : Bool}
  {ss == ee : Nat}

# the proof of the law above
def nat_mod_small(kk, ss, ee, tt, h, he):
  match kk:
    case 0n:
      Equal.trans(Nat, ss, Nat.add(ss, 0n), ee, Equal.sym(Nat, Nat.add(ss, 0n), ss, nat_add_zero(ss)), h)
    case 1n+(+kp):
      Empty.absurd({ss == ee : Nat},
        true_false(Equal.trans(Bool, True{}, Nat.is_lt(ee, tt), False{},
          Equal.sym(Bool, Nat.is_lt(ee, tt), True{}, he),
          Equal.trans(Bool, Nat.is_lt(ee, tt), Nat.is_lt(Nat.add(ss, Nat.add(tt, Nat.mul(kp, tt))), tt), False{},
            Equal.cong(Nat, Bool, xx => Nat.is_lt(xx, tt), ee, Nat.add(ss, Nat.add(tt, Nat.mul(kp, tt))),
              Equal.sym(Nat, Nat.add(ss, Nat.add(tt, Nat.mul(kp, tt))), ee, h)),
            nat_nlt_add2(ss, tt, Nat.mul(kp, tt))))))

# JSON-TREE-6: words as Nats

# a bit as a Nat

# a bit as a Nat
def bit_nat(bb: Bool) -> Nat:
  match bb:
    case False{}:
      0n
    case True{}:
      1n

# 2^nn

# 2^nn
def pow2(nn: Nat) -> Nat:
  match nn:
    case 0n:
      1n
    case 1n+pp:
      Nat.double(pow2(pp))

# 2^nn once uu is known. The checker expands a closed Nat to unary to compare
# it, and 2^32 is too large for that, so a lemma about U32s takes a unit uu
# and names 2^32 as pow2u(32n, uu), which stays unexpanded

# 2^nn once uu is known. The checker expands a closed Nat to unary to compare
# it, and 2^32 is too large for that, so a lemma about U32s takes a unit uu
# and names 2^32 as pow2u(32n, uu), which stays unexpanded
def pow2u(nn: Nat, uu: Unit) -> Nat:
  match uu:
    case Unit{}:
      pow2(nn)

# a word one bit wider, as a Nat: its low bit and twice the rest

# a word one bit wider, as a Nat: its low bit and twice the rest
law w_nat_con:
  for pp: Nat
  for bb: Bool
  for ww: Word(pp)
  {Word.to_nat(1n+pp, WCon{bb, ww}) == Nat.add(bit_nat(bb), Nat.double(Word.to_nat(pp, ww))) : Nat}

# the proof of the law above
def w_nat_con(_pp, bb, _ww):
  match bb:
    case False{}:
      {==}
    case True{}:
      {==}

# below y, twice x is below twice y

# below y, twice x is below twice y
law nat_lt_dbl:
  for +xx: Nat
  for +yy: Nat
  for h: {Nat.is_lt(xx, yy) == True{} : Bool}
  {Nat.is_lt(Nat.double(xx), Nat.double(yy)) == True{} : Bool}

# the proof of the law above
def nat_lt_dbl(xx, yy, h):
  match xx yy:
    case 0n 0n:
      h
    case 0n 1n+_yp:
      {==}
    case 1n+_xp 0n:
      Empty.absurd({Nat.is_lt(Nat.double(xx), 0n) == True{} : Bool}, false_true(h))
    case 1n+(+xp) 1n+(+yp):
      nat_lt_dbl(xp, yp, h)

# below y, twice x and one is below twice y

# below y, twice x and one is below twice y
law nat_lt_dbl1:
  for +xx: Nat
  for +yy: Nat
  for h: {Nat.is_lt(xx, yy) == True{} : Bool}
  {Nat.is_lt(1n+Nat.double(xx), Nat.double(yy)) == True{} : Bool}

# the proof of the law above
def nat_lt_dbl1(xx, yy, h):
  match xx yy:
    case 0n 0n:
      h
    case 0n 1n+_yp:
      {==}
    case 1n+_xp 0n:
      Empty.absurd({Nat.is_lt(1n+Nat.double(xx), 0n) == True{} : Bool}, false_true(h))
    case 1n+(+xp) 1n+(+yp):
      nat_lt_dbl1(xp, yp, h)

# a word of nn bits is below 2^nn

# a word of nn bits is below 2^nn
law w_bound:
  for +nn: Nat
  for ww: Word(nn)
  {Nat.is_lt(Word.to_nat(nn, ww), pow2(nn)) == True{} : Bool}

# the proof of the law above
def w_bound(nn, ww):
  match nn:
    case 0n:
      match ww:
        case WNil{}:
          {==}
    case 1n+(+pp):
      match ww:
        case WCon{False{}, +tt}:
          nat_lt_dbl(Word.to_nat(pp, tt), pow2(pp), w_bound(pp, tt))
        case WCon{True{}, +tt}:
          nat_lt_dbl1(Word.to_nat(pp, tt), pow2(pp), w_bound(pp, tt))

# w_bound, with 2^nn named through uu

# w_bound, with 2^nn named through uu
law w_bound_u:
  for +nn: Nat
  for uu: Unit
  for ww: Word(nn)
  {Nat.is_lt(Word.to_nat(nn, ww), pow2u(nn, uu)) == True{} : Bool}

# the proof of the law above
def w_bound_u(nn, uu, ww):
  match uu:
    case Unit{}:
      w_bound(nn, ww)

# comparing a bit and twice a Nat: the rest decides, the bit breaks a tie

# comparing a bit and twice a Nat: the rest decides, the bit breaks a tie
law nat_cmp_bits:
  for +aa: Nat
  for +bb: Nat
  for xx: Bool
  for yy: Bool
  {Nat.cmp(Nat.add(bit_nat(xx), Nat.double(aa)), Nat.add(bit_nat(yy), Nat.double(bb))) ==
    Word.cmp.fin(xx, yy, Nat.cmp(aa, bb)) : Cmp}

# the proof of the law above
def nat_cmp_bits(aa, bb, xx, yy):
  match aa bb:
    case 0n 0n:
      match xx yy:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case 1n+(+ap) 0n:
      match xx yy:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case 0n 1n+(+bp):
      match xx yy:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case 1n+(+ap) 1n+(+bp):
      match xx yy:
        case False{} False{}:
          nat_cmp_bits(ap, bp, False{}, False{})
        case False{} True{}:
          nat_cmp_bits(ap, bp, False{}, True{})
        case True{} False{}:
          nat_cmp_bits(ap, bp, True{}, False{})
        case True{} True{}:
          nat_cmp_bits(ap, bp, True{}, True{})

# words compare as the Nats they are

# words compare as the Nats they are
law w_cmp:
  for +nn: Nat
  for aa: Word(nn)
  for bb: Word(nn)
  {Word.cmp(nn, aa, bb) == Nat.cmp(Word.to_nat(nn, aa), Word.to_nat(nn, bb)) : Cmp}

# the proof of the law above
def w_cmp(nn, aa, bb):
  match nn:
    case 0n:
      match aa bb:
        case WNil{} WNil{}:
          {==}
    case 1n+(+pp):
      match aa bb:
        case WCon{False{}, +at} WCon{False{}, +bt}:
          Equal.trans(Cmp, Word.cmp.fin(False{}, False{}, Word.cmp(pp, at, bt)), Word.cmp.fin(False{}, False{},
            Nat.cmp(Word.to_nat(pp, at), Word.to_nat(pp, bt))),
            Nat.cmp(Nat.add(bit_nat(False{}), Nat.double(Word.to_nat(pp, at))), Nat.add(bit_nat(False{}),
              Nat.double(Word.to_nat(pp, bt)))),
            Equal.cong(Cmp, Cmp, zz => Word.cmp.fin(False{}, False{}, zz), Word.cmp(pp, at, bt),
              Nat.cmp(Word.to_nat(pp, at), Word.to_nat(pp, bt)),
              w_cmp(pp, at, bt)),
            Equal.sym(Cmp, Nat.cmp(Nat.add(bit_nat(False{}), Nat.double(Word.to_nat(pp, at))),
              Nat.add(bit_nat(False{}), Nat.double(Word.to_nat(pp, bt)))),
              Word.cmp.fin(False{}, False{}, Nat.cmp(Word.to_nat(pp, at), Word.to_nat(pp, bt))),
                nat_cmp_bits(Word.to_nat(pp, at), Word.to_nat(pp, bt), False{}, False{})))
        case WCon{False{}, +at} WCon{True{}, +bt}:
          Equal.trans(Cmp, Word.cmp.fin(False{}, True{}, Word.cmp(pp, at, bt)), Word.cmp.fin(False{}, True{},
            Nat.cmp(Word.to_nat(pp, at), Word.to_nat(pp, bt))),
            Nat.cmp(Nat.add(bit_nat(False{}), Nat.double(Word.to_nat(pp, at))), Nat.add(bit_nat(True{}),
              Nat.double(Word.to_nat(pp, bt)))),
            Equal.cong(Cmp, Cmp, zz => Word.cmp.fin(False{}, True{}, zz), Word.cmp(pp, at, bt), Nat.cmp(Word.to_nat(pp,
              at), Word.to_nat(pp, bt)),
              w_cmp(pp, at, bt)),
            Equal.sym(Cmp, Nat.cmp(Nat.add(bit_nat(False{}), Nat.double(Word.to_nat(pp, at))), Nat.add(bit_nat(True{}),
              Nat.double(Word.to_nat(pp, bt)))),
              Word.cmp.fin(False{}, True{}, Nat.cmp(Word.to_nat(pp, at), Word.to_nat(pp, bt))),
                nat_cmp_bits(Word.to_nat(pp, at), Word.to_nat(pp, bt), False{}, True{})))
        case WCon{True{}, +at} WCon{False{}, +bt}:
          Equal.trans(Cmp, Word.cmp.fin(True{}, False{}, Word.cmp(pp, at, bt)), Word.cmp.fin(True{}, False{},
            Nat.cmp(Word.to_nat(pp, at), Word.to_nat(pp, bt))),
            Nat.cmp(Nat.add(bit_nat(True{}), Nat.double(Word.to_nat(pp, at))), Nat.add(bit_nat(False{}),
              Nat.double(Word.to_nat(pp, bt)))),
            Equal.cong(Cmp, Cmp, zz => Word.cmp.fin(True{}, False{}, zz), Word.cmp(pp, at, bt), Nat.cmp(Word.to_nat(pp,
              at), Word.to_nat(pp, bt)),
              w_cmp(pp, at, bt)),
            Equal.sym(Cmp, Nat.cmp(Nat.add(bit_nat(True{}), Nat.double(Word.to_nat(pp, at))), Nat.add(bit_nat(False{}),
              Nat.double(Word.to_nat(pp, bt)))),
              Word.cmp.fin(True{}, False{}, Nat.cmp(Word.to_nat(pp, at), Word.to_nat(pp, bt))),
                nat_cmp_bits(Word.to_nat(pp, at), Word.to_nat(pp, bt), True{}, False{})))
        case WCon{True{}, +at} WCon{True{}, +bt}:
          Equal.trans(Cmp, Word.cmp.fin(True{}, True{}, Word.cmp(pp, at, bt)), Word.cmp.fin(True{}, True{},
            Nat.cmp(Word.to_nat(pp, at), Word.to_nat(pp, bt))),
            Nat.cmp(Nat.add(bit_nat(True{}), Nat.double(Word.to_nat(pp, at))), Nat.add(bit_nat(True{}),
              Nat.double(Word.to_nat(pp, bt)))),
            Equal.cong(Cmp, Cmp, zz => Word.cmp.fin(True{}, True{}, zz), Word.cmp(pp, at, bt), Nat.cmp(Word.to_nat(pp,
              at), Word.to_nat(pp, bt)),
              w_cmp(pp, at, bt)),
            Equal.sym(Cmp, Nat.cmp(Nat.add(bit_nat(True{}), Nat.double(Word.to_nat(pp, at))), Nat.add(bit_nat(True{}),
              Nat.double(Word.to_nat(pp, bt)))),
              Word.cmp.fin(True{}, True{}, Nat.cmp(Word.to_nat(pp, at), Word.to_nat(pp, bt))),
                nat_cmp_bits(Word.to_nat(pp, at), Word.to_nat(pp, bt), True{}, True{})))

# U32s compare as the Nats they are

# U32s compare as the Nats they are
law u_cmp:
  for aa: U32
  for bb: U32
  {U32.cmp(aa, bb) == Nat.cmp(U32.to_nat(aa), U32.to_nat(bb)) : Cmp}

# the proof of the law above
def u_cmp(aa, bb):
  match aa bb:
    case U32{xw} U32{yw}:
      w_cmp(32n, xw, yw)

# a word, its complement and one make 2^nn

# a word, its complement and one make 2^nn
law w_not:
  for +nn: Nat
  for ww: Word(nn)
  {Nat.add(Word.to_nat(nn, Word.not(nn, ww)), Nat.add(Word.to_nat(nn, ww), 1n)) == pow2(nn) : Nat}

# the proof of the law above
def w_not(nn, ww):
  match nn:
    case 0n:
      match ww:
        case WNil{}:
          {==}
    case 1n+(+pp):
      match ww:
        case WCon{False{}, +tt}:
          Equal.trans(Nat, 1n+Nat.add(Nat.double(Word.to_nat(pp, Word.not(pp, tt))), Nat.add(Nat.double(Word.to_nat(pp,
            tt)), 1n)), Nat.add(Nat.double(Word.to_nat(pp, Word.not(pp, tt))), 1n+Nat.add(Nat.double(Word.to_nat(pp,
            tt)), 1n)), Nat.double(pow2(pp)), Equal.sym(Nat, Nat.add(Nat.double(Word.to_nat(pp, Word.not(pp, tt))),
            1n+Nat.add(Nat.double(Word.to_nat(pp, tt)), 1n)), 1n+Nat.add(Nat.double(Word.to_nat(pp, Word.not(pp, tt))),
            Nat.add(Nat.double(Word.to_nat(pp, tt)), 1n)), nat_add_succ(Nat.double(Word.to_nat(pp, Word.not(pp, tt))),
            Nat.add(Nat.double(Word.to_nat(pp, tt)), 1n))), Equal.trans(Nat, Nat.add(Nat.double(Word.to_nat(pp,
            Word.not(pp, tt))), 1n+Nat.add(Nat.double(Word.to_nat(pp, tt)), 1n)), Nat.add(Nat.double(Word.to_nat(pp,
            Word.not(pp, tt))), Nat.add(Nat.double(Word.to_nat(pp, tt)), 2n)), Nat.double(pow2(pp)), Equal.cong(Nat,
            Nat, z9 => Nat.add(Nat.double(Word.to_nat(pp, Word.not(pp, tt))), z9),
            1n+Nat.add(Nat.double(Word.to_nat(pp, tt)), 1n), Nat.add(Nat.double(Word.to_nat(pp, tt)), 2n),
            Equal.sym(Nat, Nat.add(Nat.double(Word.to_nat(pp, tt)), 2n), 1n+Nat.add(Nat.double(Word.to_nat(pp, tt)),
            1n), nat_add_succ(Nat.double(Word.to_nat(pp, tt)), 1n))), Equal.trans(Nat,
            Nat.add(Nat.double(Word.to_nat(pp, Word.not(pp, tt))), Nat.add(Nat.double(Word.to_nat(pp, tt)), 2n)),
            Nat.add(Nat.double(Word.to_nat(pp, Word.not(pp, tt))), Nat.double(Nat.add(Word.to_nat(pp, tt), 1n))),
            Nat.double(pow2(pp)), Equal.cong(Nat, Nat, z10 => Nat.add(Nat.double(Word.to_nat(pp, Word.not(pp, tt))),
            z10), Nat.add(Nat.double(Word.to_nat(pp, tt)), 2n), Nat.double(Nat.add(Word.to_nat(pp, tt), 1n)),
            Equal.sym(Nat, Nat.double(Nat.add(Word.to_nat(pp, tt), 1n)), Nat.add(Nat.double(Word.to_nat(pp, tt)), 2n),
            nat_double_add(Word.to_nat(pp, tt), 1n))), Equal.trans(Nat, Nat.add(Nat.double(Word.to_nat(pp, Word.not(pp,
            tt))), Nat.double(Nat.add(Word.to_nat(pp, tt), 1n))), Nat.double(Nat.add(Word.to_nat(pp, Word.not(pp, tt)),
            Nat.add(Word.to_nat(pp, tt), 1n))), Nat.double(pow2(pp)), Equal.sym(Nat, Nat.double(Nat.add(Word.to_nat(pp,
            Word.not(pp, tt)), Nat.add(Word.to_nat(pp, tt), 1n))), Nat.add(Nat.double(Word.to_nat(pp, Word.not(pp,
            tt))), Nat.double(Nat.add(Word.to_nat(pp, tt), 1n))), nat_double_add(Word.to_nat(pp, Word.not(pp, tt)),
            Nat.add(Word.to_nat(pp, tt), 1n))), Equal.cong(Nat, Nat, z11 => Nat.double(z11), Nat.add(Word.to_nat(pp,
            Word.not(pp, tt)), Nat.add(Word.to_nat(pp, tt), 1n)), pow2(pp), w_not(pp, tt))))))
        case WCon{True{}, +tt}:
          Equal.trans(Nat, Nat.add(Nat.double(Word.to_nat(pp, Word.not(pp, tt))), 1n+Nat.add(Nat.double(Word.to_nat(pp,
            tt)), 1n)), Nat.add(Nat.double(Word.to_nat(pp, Word.not(pp, tt))), Nat.add(Nat.double(Word.to_nat(pp, tt)),
            2n)), Nat.double(pow2(pp)), Equal.cong(Nat, Nat, z9 => Nat.add(Nat.double(Word.to_nat(pp, Word.not(pp,
            tt))), z9), 1n+Nat.add(Nat.double(Word.to_nat(pp, tt)), 1n), Nat.add(Nat.double(Word.to_nat(pp, tt)), 2n),
            Equal.sym(Nat, Nat.add(Nat.double(Word.to_nat(pp, tt)), 2n), 1n+Nat.add(Nat.double(Word.to_nat(pp, tt)),
            1n), nat_add_succ(Nat.double(Word.to_nat(pp, tt)), 1n))), Equal.trans(Nat,
            Nat.add(Nat.double(Word.to_nat(pp, Word.not(pp, tt))), Nat.add(Nat.double(Word.to_nat(pp, tt)), 2n)),
            Nat.add(Nat.double(Word.to_nat(pp, Word.not(pp, tt))), Nat.double(Nat.add(Word.to_nat(pp, tt), 1n))),
            Nat.double(pow2(pp)), Equal.cong(Nat, Nat, z10 => Nat.add(Nat.double(Word.to_nat(pp, Word.not(pp, tt))),
            z10), Nat.add(Nat.double(Word.to_nat(pp, tt)), 2n), Nat.double(Nat.add(Word.to_nat(pp, tt), 1n)),
            Equal.sym(Nat, Nat.double(Nat.add(Word.to_nat(pp, tt), 1n)), Nat.add(Nat.double(Word.to_nat(pp, tt)), 2n),
            nat_double_add(Word.to_nat(pp, tt), 1n))), Equal.trans(Nat, Nat.add(Nat.double(Word.to_nat(pp, Word.not(pp,
            tt))), Nat.double(Nat.add(Word.to_nat(pp, tt), 1n))), Nat.double(Nat.add(Word.to_nat(pp, Word.not(pp, tt)),
            Nat.add(Word.to_nat(pp, tt), 1n))), Nat.double(pow2(pp)), Equal.sym(Nat, Nat.double(Nat.add(Word.to_nat(pp,
            Word.not(pp, tt)), Nat.add(Word.to_nat(pp, tt), 1n))), Nat.add(Nat.double(Word.to_nat(pp, Word.not(pp,
            tt))), Nat.double(Nat.add(Word.to_nat(pp, tt), 1n))), nat_double_add(Word.to_nat(pp, Word.not(pp, tt)),
            Nat.add(Word.to_nat(pp, tt), 1n))), Equal.cong(Nat, Nat, z11 => Nat.double(z11), Nat.add(Word.to_nat(pp,
            Word.not(pp, tt)), Nat.add(Word.to_nat(pp, tt), 1n)), pow2(pp), w_not(pp, tt)))))

# w_not, with 2^nn named through uu

# w_not, with 2^nn named through uu
law w_not_u:
  for +nn: Nat
  for uu: Unit
  for ww: Word(nn)
  {Nat.add(Word.to_nat(nn, Word.not(nn, ww)), Nat.add(Word.to_nat(nn, ww), 1n)) == pow2u(nn, uu) : Nat}

# the proof of the law above
def w_not_u(nn, uu, ww):
  match uu:
    case Unit{}:
      w_not(nn, ww)

# JSON-TREE-6: word addition as Nat addition

# the sum bit of a full add

# the sum bit of a full add
def fa_s(sk: Bool & Bool) -> Bool:
  (ss, _kk) = sk
  ss

# the carry bit of a full add

# the carry bit of a full add
def fa_k(sk: Bool & Bool) -> Bool:
  (_ss, kk) = sk
  kk

# the word adc adds: b, or its complement when ff

# the word adc adds: b, or its complement when ff
def adc_sel(nn: Nat, ww: Word(nn), ff: Bool) -> Word(nn):
  match ff:
    case False{}:
      ww
    case True{}:
      Word.not(nn, ww)

# how many times 2^nn adc's sum passes: its carry out

# how many times 2^nn adc's sum passes: its carry out
def adc_k(nn: Nat, aa: Word(nn), bb: Word(nn), ff: Bool, cc: Bool) -> Nat:
  match nn:
    case 0n:
      bit_nat(cc)
    case 1n+pp:
      match aa bb ff:
        case WCon{ab, at} WCon{bb2, bt} False{}:
          adc_k(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc)))
        case WCon{ab, at} WCon{bb2, bt} True{}:
          adc_k(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))

# a full add's sum and twice its carry are its three bits

# a full add's sum and twice its carry are its three bits
law fa_nat:
  for xx: Bool
  for yy: Bool
  for cc: Bool
  {Nat.add(bit_nat(fa_s(Bool.full_add(xx, yy, cc))), Nat.double(bit_nat(fa_k(Bool.full_add(xx, yy, cc))))) ==
    Nat.add(bit_nat(xx), Nat.add(bit_nat(yy), bit_nat(cc))) : Nat}

# the proof of the law above
def fa_nat(xx, yy, cc):
  match xx yy cc:
    case False{} False{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      {==}

# adc's cell, from a full add not yet known

# adc's cell, from a full add not yet known
law adc_eta:
  for pp: Nat
  for at: Word(pp)
  for bt: Word(pp)
  for ff: Bool
  for sk: Bool & Bool
  {Word.adc.con(pp, at, bt, ff, sk) == WCon{fa_s(sk), Word.adc(pp, at, bt, ff, fa_k(sk))} : Word(1n+pp)}

# the proof of the law above
def adc_eta(_pp, _at, _bt, _ff, sk):
  (_ss, _kk) = sk
  {==}

# adc as Nats: the sum, and its carry out times 2^nn, is a, b (or its
# complement) and the carry in

# adc as Nats: the sum, and its carry out times 2^nn, is a, b (or its
# complement) and the carry in
law w_adc:
  for +nn: Nat
  for aa: Word(nn)
  for bb: Word(nn)
  for ff: Bool
  for +cc: Bool
  {Nat.add(Word.to_nat(nn, Word.adc(nn, aa, bb, ff, cc)), Nat.mul(adc_k(nn, aa, bb, ff, cc), pow2(nn))) ==
    Nat.add(Word.to_nat(nn, aa), Nat.add(Word.to_nat(nn, adc_sel(nn, bb, ff)), bit_nat(cc))) : Nat}

# the proof of the law above
def w_adc(nn, aa, bb, ff, cc):
  match nn:
    case 0n:
      match aa bb:
        case WNil{} WNil{}:
          nat_mul_one(bit_nat(cc))
    case 1n+(+pp):
      match aa bb ff:
        case WCon{+ab, +at} WCon{+bb2, +bt} False{}:
          Equal.trans(Nat, Nat.add(Word.to_nat(1n+pp, Word.adc.con(pp, at, bt, False{}, Bool.full_add(ab, bb2, cc))),
            Nat.mul(adc_k(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc))), Nat.double(pow2(pp)))),
            Nat.add(Word.to_nat(1n+pp, WCon{fa_s(Bool.full_add(ab, bb2, cc)), Word.adc(pp, at, bt, False{},
            fa_k(Bool.full_add(ab, bb2, cc)))}), Nat.mul(adc_k(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc))),
            Nat.double(pow2(pp)))), Nat.add(Word.to_nat(1n+pp, WCon{ab, at}), Nat.add(Word.to_nat(1n+pp, WCon{bb2,
            bt}), bit_nat(cc))), Equal.cong(Word(1n+pp), Nat, z12 => Nat.add(Word.to_nat(1n+pp, z12), Nat.mul(adc_k(pp,
            at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc))), Nat.double(pow2(pp)))), Word.adc.con(pp, at, bt,
            False{}, Bool.full_add(ab, bb2, cc)), WCon{fa_s(Bool.full_add(ab, bb2, cc)), Word.adc(pp, at, bt, False{},
            fa_k(Bool.full_add(ab, bb2, cc)))}, adc_eta(pp, at, bt, False{}, Bool.full_add(ab, bb2, cc))),
            Equal.trans(Nat, Nat.add(Word.to_nat(1n+pp, WCon{fa_s(Bool.full_add(ab, bb2, cc)), Word.adc(pp, at, bt,
            False{}, fa_k(Bool.full_add(ab, bb2, cc)))}), Nat.mul(adc_k(pp, at, bt, False{}, fa_k(Bool.full_add(ab,
            bb2, cc))), Nat.double(pow2(pp)))), Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))),
            Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc)))))),
            Nat.mul(adc_k(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc))), Nat.double(pow2(pp)))),
            Nat.add(Word.to_nat(1n+pp, WCon{ab, at}), Nat.add(Word.to_nat(1n+pp, WCon{bb2, bt}), bit_nat(cc))),
            Equal.cong(Nat, Nat, z13 => Nat.add(z13, Nat.mul(adc_k(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2,
            cc))), Nat.double(pow2(pp)))), Word.to_nat(1n+pp, WCon{fa_s(Bool.full_add(ab, bb2, cc)), Word.adc(pp, at,
            bt, False{}, fa_k(Bool.full_add(ab, bb2, cc)))}), Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))),
            Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc)))))),
            w_nat_con(pp, fa_s(Bool.full_add(ab, bb2, cc)), Word.adc(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2,
            cc))))), Equal.trans(Nat, Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))),
            Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc)))))),
            Nat.mul(adc_k(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc))), Nat.double(pow2(pp)))),
            Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt,
            False{}, fa_k(Bool.full_add(ab, bb2, cc)))))), Nat.double(Nat.mul(adc_k(pp, at, bt, False{},
            fa_k(Bool.full_add(ab, bb2, cc))), pow2(pp)))), Nat.add(Word.to_nat(1n+pp, WCon{ab, at}),
            Nat.add(Word.to_nat(1n+pp, WCon{bb2, bt}), bit_nat(cc))), Equal.cong(Nat, Nat,
            z14 => Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.double(Word.to_nat(pp, Word.adc(pp,
            at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc)))))), z14), Nat.mul(adc_k(pp, at, bt, False{},
            fa_k(Bool.full_add(ab, bb2, cc))), Nat.double(pow2(pp))), Nat.double(Nat.mul(adc_k(pp, at, bt, False{},
            fa_k(Bool.full_add(ab, bb2, cc))), pow2(pp))), nat_mul_double_r(adc_k(pp, at, bt, False{},
            fa_k(Bool.full_add(ab, bb2, cc))), pow2(pp))), Equal.trans(Nat,
            Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt,
            False{}, fa_k(Bool.full_add(ab, bb2, cc)))))), Nat.double(Nat.mul(adc_k(pp, at, bt, False{},
            fa_k(Bool.full_add(ab, bb2, cc))), pow2(pp)))), Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))),
            Nat.add(Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc))))),
            Nat.double(Nat.mul(adc_k(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc))), pow2(pp))))),
            Nat.add(Word.to_nat(1n+pp, WCon{ab, at}), Nat.add(Word.to_nat(1n+pp, WCon{bb2, bt}), bit_nat(cc))),
            nat_add_assoc(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt,
            False{}, fa_k(Bool.full_add(ab, bb2, cc))))), Nat.double(Nat.mul(adc_k(pp, at, bt, False{},
            fa_k(Bool.full_add(ab, bb2, cc))), pow2(pp)))), Equal.trans(Nat, Nat.add(bit_nat(fa_s(Bool.full_add(ab,
            bb2, cc))), Nat.add(Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2,
            cc))))), Nat.double(Nat.mul(adc_k(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc))), pow2(pp))))),
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.double(Nat.add(Word.to_nat(pp, Word.adc(pp, at, bt,
            False{}, fa_k(Bool.full_add(ab, bb2, cc)))), Nat.mul(adc_k(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2,
            cc))), pow2(pp))))), Nat.add(Word.to_nat(1n+pp, WCon{ab, at}), Nat.add(Word.to_nat(1n+pp, WCon{bb2, bt}),
            bit_nat(cc))), Equal.cong(Nat, Nat, z15 => Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), z15),
            Nat.add(Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc))))),
            Nat.double(Nat.mul(adc_k(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc))), pow2(pp)))),
            Nat.double(Nat.add(Word.to_nat(pp, Word.adc(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc)))),
            Nat.mul(adc_k(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc))), pow2(pp)))), Equal.sym(Nat,
            Nat.double(Nat.add(Word.to_nat(pp, Word.adc(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc)))),
            Nat.mul(adc_k(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc))), pow2(pp)))),
            Nat.add(Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc))))),
            Nat.double(Nat.mul(adc_k(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc))), pow2(pp)))),
            nat_double_add(Word.to_nat(pp, Word.adc(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc)))),
            Nat.mul(adc_k(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc))), pow2(pp))))), Equal.trans(Nat,
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.double(Nat.add(Word.to_nat(pp, Word.adc(pp, at, bt,
            False{}, fa_k(Bool.full_add(ab, bb2, cc)))), Nat.mul(adc_k(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2,
            cc))), pow2(pp))))), Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.double(Nat.add(Word.to_nat(pp,
            at), Nat.add(Word.to_nat(pp, adc_sel(pp, bt, False{})), bit_nat(fa_k(Bool.full_add(ab, bb2, cc))))))),
            Nat.add(Word.to_nat(1n+pp, WCon{ab, at}), Nat.add(Word.to_nat(1n+pp, WCon{bb2, bt}), bit_nat(cc))),
            Equal.cong(Nat, Nat, z16 => Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.double(z16)),
            Nat.add(Word.to_nat(pp, Word.adc(pp, at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc)))), Nat.mul(adc_k(pp,
            at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc))), pow2(pp))), Nat.add(Word.to_nat(pp, at),
            Nat.add(Word.to_nat(pp, adc_sel(pp, bt, False{})), bit_nat(fa_k(Bool.full_add(ab, bb2, cc))))), w_adc(pp,
            at, bt, False{}, fa_k(Bool.full_add(ab, bb2, cc)))), Equal.trans(Nat,
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.double(Nat.add(Word.to_nat(pp, at),
            Nat.add(Word.to_nat(pp, adc_sel(pp, bt, False{})), bit_nat(fa_k(Bool.full_add(ab, bb2, cc))))))),
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Nat.add(Word.to_nat(pp, adc_sel(pp, bt, False{})), bit_nat(fa_k(Bool.full_add(ab, bb2,
            cc))))))), Nat.add(Word.to_nat(1n+pp, WCon{ab, at}), Nat.add(Word.to_nat(1n+pp, WCon{bb2, bt}),
            bit_nat(cc))), Equal.cong(Nat, Nat, z17 => Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), z17),
            Nat.double(Nat.add(Word.to_nat(pp, at), Nat.add(Word.to_nat(pp, adc_sel(pp, bt, False{})),
            bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Nat.add(Word.to_nat(pp, adc_sel(pp, bt, False{})), bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))))),
            nat_double_add(Word.to_nat(pp, at), Nat.add(Word.to_nat(pp, adc_sel(pp, bt, False{})),
            bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))))), Equal.trans(Nat, Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Nat.add(Word.to_nat(pp, adc_sel(pp, bt,
            False{})), bit_nat(fa_k(Bool.full_add(ab, bb2, cc))))))), Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc))))))), Nat.add(Word.to_nat(1n+pp, WCon{ab,
            at}), Nat.add(Word.to_nat(1n+pp, WCon{bb2, bt}), bit_nat(cc))), Equal.cong(Nat, Nat,
            z18 => Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.add(Nat.double(Word.to_nat(pp, at)), z18)),
            Nat.double(Nat.add(Word.to_nat(pp, adc_sel(pp, bt, False{})), bit_nat(fa_k(Bool.full_add(ab, bb2, cc))))),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            bb2, cc))))), nat_double_add(Word.to_nat(pp, adc_sel(pp, bt, False{})), bit_nat(fa_k(Bool.full_add(ab, bb2,
            cc))))), Equal.trans(Nat, Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc))))))), Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab,
            bb2, cc))), Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc))))), Nat.add(Nat.double(Word.to_nat(pp,
            at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))), Nat.add(Word.to_nat(1n+pp, WCon{ab, at}),
            Nat.add(Word.to_nat(1n+pp, WCon{bb2, bt}), bit_nat(cc))), Equal.trans(Nat,
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            bb2, cc))))))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{}))), Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), bit_nat(fa_s(Bool.full_add(ab,
            bb2, cc)))))), Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))), Equal.trans(Nat,
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            bb2, cc))))))), Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            bb2, cc))))))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{}))), Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), bit_nat(fa_s(Bool.full_add(ab,
            bb2, cc)))))), Equal.cong(Nat, Nat, z20 => Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), z20),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            bb2, cc)))))), Equal.cong(Nat, Nat, z19 => Nat.add(Nat.double(Word.to_nat(pp, at)), z19),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            bb2, cc))))), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc))))), {==})), Equal.trans(Nat,
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            bb2, cc))))))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            bb2, cc))))))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{}))), Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), bit_nat(fa_s(Bool.full_add(ab,
            bb2, cc)))))), nat_add_lcomm(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            bb2, cc)))))), Equal.cong(Nat, Nat, z22 => Nat.add(Nat.double(Word.to_nat(pp, at)), z22),
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))))), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, False{}))), Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))),
            bit_nat(fa_s(Bool.full_add(ab, bb2, cc))))), Equal.trans(Nat, Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc))), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))))), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{}))), Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            bb2, cc)))))), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), bit_nat(fa_s(Bool.full_add(ab, bb2, cc))))),
            nat_add_lcomm(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc))))), Equal.cong(Nat, Nat,
            z21 => Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), z21),
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc))))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), bit_nat(fa_s(Bool.full_add(ab, bb2, cc)))),
            nat_add_comm(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2,
            cc)))))))))), Equal.sym(Nat, Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc)))))), Equal.trans(Nat, Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))),
            Nat.add(Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc)))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc)))))), Equal.cong(Nat, Nat, z23 => Nat.add(z23, Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))), Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc))))), Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            bb2, cc)))), bit_nat(fa_s(Bool.full_add(ab, bb2, cc)))), nat_add_comm(bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc))), Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))))), Equal.trans(Nat,
            Nat.add(Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc)))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))),
            Nat.add(Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc)))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc)))))), Equal.cong(Nat, Nat, z24 => Nat.add(Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2,
            cc)))), bit_nat(fa_s(Bool.full_add(ab, bb2, cc)))), z24), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))), {==}), Equal.trans(Nat,
            Nat.add(Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc)))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc)))))), nat_add_assoc(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))),
            bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))), Equal.trans(Nat,
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc)))))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{}))), Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), bit_nat(fa_s(Bool.full_add(ab,
            bb2, cc)))))), Equal.cong(Nat, Nat, z26 => Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))),
            z26), Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), bit_nat(fa_s(Bool.full_add(ab, bb2, cc))))),
            Equal.trans(Nat, Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.add(Nat.double(Word.to_nat(pp,
            at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))),
            bit_nat(fa_s(Bool.full_add(ab, bb2, cc))))), nat_add_lcomm(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))),
            Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))), Equal.cong(Nat,
            Nat, z25 => Nat.add(Nat.double(Word.to_nat(pp, at)), z25), Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc))), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, False{}))), bit_nat(fa_s(Bool.full_add(ab, bb2, cc)))),
            nat_add_comm(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))), Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{}))))))), Equal.trans(Nat, Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))),
            bit_nat(fa_s(Bool.full_add(ab, bb2, cc)))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, False{}))), bit_nat(fa_s(Bool.full_add(ab, bb2, cc)))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc)))))), nat_add_lcomm(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), Nat.double(Word.to_nat(pp,
            at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc))))), Equal.cong(Nat, Nat, z27 => Nat.add(Nat.double(Word.to_nat(pp, at)), z27),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, False{}))), bit_nat(fa_s(Bool.full_add(ab, bb2, cc))))), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, False{}))), Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc)))),
            bit_nat(fa_s(Bool.full_add(ab, bb2, cc))))), nat_add_lcomm(Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2,
            cc)))), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), bit_nat(fa_s(Bool.full_add(ab, bb2,
            cc)))))))))))), Equal.trans(Nat, Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))), Nat.add(Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2),
            bit_nat(cc))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{}))))), Nat.add(Word.to_nat(1n+pp, WCon{ab, at}), Nat.add(Word.to_nat(1n+pp, WCon{bb2, bt}),
            bit_nat(cc))), Equal.cong(Nat, Nat, z28 => Nat.add(z28, Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))), Nat.add(bit_nat(fa_s(Bool.full_add(ab, bb2, cc))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, bb2, cc))))), Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2),
            bit_nat(cc))), fa_nat(ab, bb2, cc)), Equal.trans(Nat, Nat.add(Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2),
            bit_nat(cc))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{}))))), Nat.add(Nat.add(bit_nat(ab), Nat.double(Word.to_nat(pp, at))), Nat.add(Nat.add(bit_nat(bb2),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))), bit_nat(cc))), Nat.add(Word.to_nat(1n+pp, WCon{ab,
            at}), Nat.add(Word.to_nat(1n+pp, WCon{bb2, bt}), bit_nat(cc))), Equal.trans(Nat,
            Nat.add(Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2), bit_nat(cc))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2),
            bit_nat(cc))))), Nat.add(Nat.add(bit_nat(ab), Nat.double(Word.to_nat(pp, at))),
            Nat.add(Nat.add(bit_nat(bb2), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))), bit_nat(cc))),
            Equal.trans(Nat, Nat.add(Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2), bit_nat(cc))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))),
            Nat.add(Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2), bit_nat(cc))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2),
            bit_nat(cc))))), Equal.cong(Nat, Nat, z30 => Nat.add(z30, Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))), Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2),
            bit_nat(cc))), Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2), bit_nat(cc))), Equal.cong(Nat, Nat,
            z29 => Nat.add(bit_nat(ab), z29), Nat.add(bit_nat(bb2), bit_nat(cc)), Nat.add(bit_nat(bb2), bit_nat(cc)),
            {==})), Equal.trans(Nat, Nat.add(Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2), bit_nat(cc))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))),
            Nat.add(Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2), bit_nat(cc))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2),
            bit_nat(cc))))), Equal.cong(Nat, Nat, z31 => Nat.add(Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2),
            bit_nat(cc))), z31), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{})))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{})))), {==}), Equal.trans(Nat, Nat.add(Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2), bit_nat(cc))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))),
            Nat.add(bit_nat(ab), Nat.add(Nat.add(bit_nat(bb2), bit_nat(cc)), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2),
            bit_nat(cc))))), nat_add_assoc(bit_nat(ab), Nat.add(bit_nat(bb2), bit_nat(cc)),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))),
            Equal.trans(Nat, Nat.add(bit_nat(ab), Nat.add(Nat.add(bit_nat(bb2), bit_nat(cc)),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))))),
            Nat.add(bit_nat(ab), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, False{}))), Nat.add(bit_nat(bb2), bit_nat(cc))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2),
            bit_nat(cc))))), Equal.cong(Nat, Nat, z35 => Nat.add(bit_nat(ab), z35), Nat.add(Nat.add(bit_nat(bb2),
            bit_nat(cc)), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{}))))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{}))), Nat.add(bit_nat(bb2), bit_nat(cc)))), Equal.trans(Nat, Nat.add(Nat.add(bit_nat(bb2),
            bit_nat(cc)), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{}))))), Nat.add(bit_nat(bb2), Nat.add(bit_nat(cc), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(bb2), bit_nat(cc)))),
            nat_add_assoc(bit_nat(bb2), bit_nat(cc), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))), Equal.trans(Nat, Nat.add(bit_nat(bb2),
            Nat.add(bit_nat(cc), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{})))))), Nat.add(bit_nat(bb2), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), bit_nat(cc)))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))),
            Nat.add(bit_nat(bb2), bit_nat(cc)))), Equal.cong(Nat, Nat, z33 => Nat.add(bit_nat(bb2), z33),
            Nat.add(bit_nat(cc), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{}))))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{}))), bit_nat(cc))), Equal.trans(Nat, Nat.add(bit_nat(cc), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(bit_nat(cc), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))),
            bit_nat(cc))), nat_add_lcomm(bit_nat(cc), Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, False{})))), Equal.cong(Nat, Nat, z32 => Nat.add(Nat.double(Word.to_nat(pp, at)), z32),
            Nat.add(bit_nat(cc), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), bit_nat(cc)), nat_add_comm(bit_nat(cc),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))))))), Equal.trans(Nat, Nat.add(bit_nat(bb2),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))),
            bit_nat(cc)))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(bit_nat(bb2),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), bit_nat(cc)))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))),
            Nat.add(bit_nat(bb2), bit_nat(cc)))), nat_add_lcomm(bit_nat(bb2), Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), bit_nat(cc))), Equal.cong(Nat, Nat,
            z34 => Nat.add(Nat.double(Word.to_nat(pp, at)), z34), Nat.add(bit_nat(bb2),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), bit_nat(cc))),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(bb2), bit_nat(cc))),
            nat_add_lcomm(bit_nat(bb2), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), bit_nat(cc))))))),
            Equal.trans(Nat, Nat.add(bit_nat(ab), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(bb2), bit_nat(cc))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(bit_nat(ab), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, False{}))), Nat.add(bit_nat(bb2), bit_nat(cc))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2),
            bit_nat(cc))))), nat_add_lcomm(bit_nat(ab), Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(bb2), bit_nat(cc)))),
            Equal.cong(Nat, Nat, z36 => Nat.add(Nat.double(Word.to_nat(pp, at)), z36), Nat.add(bit_nat(ab),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(bb2), bit_nat(cc)))),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2),
            bit_nat(cc)))), nat_add_lcomm(bit_nat(ab), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))),
            Nat.add(bit_nat(bb2), bit_nat(cc))))))))), Equal.sym(Nat, Nat.add(Nat.add(bit_nat(ab),
            Nat.double(Word.to_nat(pp, at))), Nat.add(Nat.add(bit_nat(bb2), Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{})))), bit_nat(cc))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, False{}))), Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2), bit_nat(cc))))), Equal.trans(Nat,
            Nat.add(Nat.add(bit_nat(ab), Nat.double(Word.to_nat(pp, at))), Nat.add(Nat.add(bit_nat(bb2),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))), bit_nat(cc))),
            Nat.add(Nat.add(Nat.double(Word.to_nat(pp, at)), bit_nat(ab)), Nat.add(Nat.add(bit_nat(bb2),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))), bit_nat(cc))), Nat.add(Nat.double(Word.to_nat(pp,
            at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(ab),
            Nat.add(bit_nat(bb2), bit_nat(cc))))), Equal.cong(Nat, Nat, z38 => Nat.add(z38,
            Nat.add(Nat.add(bit_nat(bb2), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))), bit_nat(cc))),
            Nat.add(bit_nat(ab), Nat.double(Word.to_nat(pp, at))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            bit_nat(ab)), nat_add_comm(bit_nat(ab), Nat.double(Word.to_nat(pp, at)))), Equal.trans(Nat,
            Nat.add(Nat.add(Nat.double(Word.to_nat(pp, at)), bit_nat(ab)), Nat.add(Nat.add(bit_nat(bb2),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))), bit_nat(cc))),
            Nat.add(Nat.add(Nat.double(Word.to_nat(pp, at)), bit_nat(ab)), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, False{}))), Nat.add(bit_nat(bb2), bit_nat(cc)))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2),
            bit_nat(cc))))), Equal.cong(Nat, Nat, z39 => Nat.add(Nat.add(Nat.double(Word.to_nat(pp, at)), bit_nat(ab)),
            z39), Nat.add(Nat.add(bit_nat(bb2), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))), bit_nat(cc)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(bb2), bit_nat(cc))),
            Equal.trans(Nat, Nat.add(Nat.add(bit_nat(bb2), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))),
            bit_nat(cc)), Nat.add(Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), bit_nat(bb2)),
            bit_nat(cc)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(bb2),
            bit_nat(cc))), Equal.cong(Nat, Nat, z37 => Nat.add(z37, bit_nat(cc)), Nat.add(bit_nat(bb2),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{}))), bit_nat(bb2)), nat_add_comm(bit_nat(bb2), Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{}))))), nat_add_assoc(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), bit_nat(bb2),
            bit_nat(cc)))), Equal.trans(Nat, Nat.add(Nat.add(Nat.double(Word.to_nat(pp, at)), bit_nat(ab)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(bb2), bit_nat(cc)))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(bit_nat(ab), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, False{}))), Nat.add(bit_nat(bb2), bit_nat(cc))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2),
            bit_nat(cc))))), nat_add_assoc(Nat.double(Word.to_nat(pp, at)), bit_nat(ab),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(bb2), bit_nat(cc)))),
            Equal.cong(Nat, Nat, z40 => Nat.add(Nat.double(Word.to_nat(pp, at)), z40), Nat.add(bit_nat(ab),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(bb2), bit_nat(cc)))),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))), Nat.add(bit_nat(ab), Nat.add(bit_nat(bb2),
            bit_nat(cc)))), nat_add_lcomm(bit_nat(ab), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{}))),
            Nat.add(bit_nat(bb2), bit_nat(cc))))))))), Equal.trans(Nat, Nat.add(Nat.add(bit_nat(ab),
            Nat.double(Word.to_nat(pp, at))), Nat.add(Nat.add(bit_nat(bb2), Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            False{})))), bit_nat(cc))), Nat.add(Word.to_nat(1n+pp, WCon{ab, at}), Nat.add(Nat.add(bit_nat(bb2),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))), bit_nat(cc))), Nat.add(Word.to_nat(1n+pp, WCon{ab,
            at}), Nat.add(Word.to_nat(1n+pp, WCon{bb2, bt}), bit_nat(cc))), Equal.cong(Nat, Nat, z41 => Nat.add(z41,
            Nat.add(Nat.add(bit_nat(bb2), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))), bit_nat(cc))),
            Nat.add(bit_nat(ab), Nat.double(Word.to_nat(pp, at))), Word.to_nat(1n+pp, WCon{ab, at}), Equal.sym(Nat,
            Word.to_nat(1n+pp, WCon{ab, at}), Nat.add(bit_nat(ab), Nat.double(Word.to_nat(pp, at))), w_nat_con(pp, ab,
            at))), Equal.cong(Nat, Nat, z42 => Nat.add(Word.to_nat(1n+pp, WCon{ab, at}), Nat.add(z42, bit_nat(cc))),
            Nat.add(bit_nat(bb2), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, False{})))), Word.to_nat(1n+pp, WCon{bb2,
            bt}), Equal.sym(Nat, Word.to_nat(1n+pp, WCon{bb2, bt}), Nat.add(bit_nat(bb2), Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, False{})))), w_nat_con(pp, bb2, bt)))))))))))))))
        case WCon{+ab, +at} WCon{+bb2, +bt} True{}:
          Equal.trans(Nat, Nat.add(Word.to_nat(1n+pp, Word.adc.con(pp, at, bt, True{}, Bool.full_add(ab, Bool.not(bb2),
            cc))), Nat.mul(adc_k(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))),
            Nat.double(pow2(pp)))), Nat.add(Word.to_nat(1n+pp, WCon{fa_s(Bool.full_add(ab, Bool.not(bb2), cc)),
            Word.adc(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))}), Nat.mul(adc_k(pp, at, bt,
            True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.double(pow2(pp)))), Nat.add(Word.to_nat(1n+pp,
            WCon{ab, at}), Nat.add(Word.to_nat(1n+pp, WCon{Bool.not(bb2), Word.not(pp, bt)}), bit_nat(cc))),
            Equal.cong(Word(1n+pp), Nat, z43 => Nat.add(Word.to_nat(1n+pp, z43), Nat.mul(adc_k(pp, at, bt, True{},
            fa_k(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.double(pow2(pp)))), Word.adc.con(pp, at, bt, True{},
            Bool.full_add(ab, Bool.not(bb2), cc)), WCon{fa_s(Bool.full_add(ab, Bool.not(bb2), cc)), Word.adc(pp, at,
            bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))}, adc_eta(pp, at, bt, True{}, Bool.full_add(ab,
            Bool.not(bb2), cc))), Equal.trans(Nat, Nat.add(Word.to_nat(1n+pp, WCon{fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc)), Word.adc(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))}),
            Nat.mul(adc_k(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.double(pow2(pp)))),
            Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.double(Word.to_nat(pp,
            Word.adc(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))))), Nat.mul(adc_k(pp, at, bt,
            True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.double(pow2(pp)))), Nat.add(Word.to_nat(1n+pp,
            WCon{ab, at}), Nat.add(Word.to_nat(1n+pp, WCon{Bool.not(bb2), Word.not(pp, bt)}), bit_nat(cc))),
            Equal.cong(Nat, Nat, z44 => Nat.add(z44, Nat.mul(adc_k(pp, at, bt, True{}, fa_k(Bool.full_add(ab,
            Bool.not(bb2), cc))), Nat.double(pow2(pp)))), Word.to_nat(1n+pp, WCon{fa_s(Bool.full_add(ab, Bool.not(bb2),
            cc)), Word.adc(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))}),
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.double(Word.to_nat(pp, Word.adc(pp, at,
            bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))))), w_nat_con(pp, fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc)), Word.adc(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))),
            Equal.trans(Nat, Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))),
            Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))))),
            Nat.mul(adc_k(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.double(pow2(pp)))),
            Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.double(Word.to_nat(pp,
            Word.adc(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))))), Nat.double(Nat.mul(adc_k(pp,
            at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))), pow2(pp)))), Nat.add(Word.to_nat(1n+pp,
            WCon{ab, at}), Nat.add(Word.to_nat(1n+pp, WCon{Bool.not(bb2), Word.not(pp, bt)}), bit_nat(cc))),
            Equal.cong(Nat, Nat, z45 => Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))),
            Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))))),
            z45), Nat.mul(adc_k(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.double(pow2(pp))),
            Nat.double(Nat.mul(adc_k(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))), pow2(pp))),
            nat_mul_double_r(adc_k(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))), pow2(pp))),
            Equal.trans(Nat, Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))),
            Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))))),
            Nat.double(Nat.mul(adc_k(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))), pow2(pp)))),
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.add(Nat.double(Word.to_nat(pp,
            Word.adc(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))), Nat.double(Nat.mul(adc_k(pp,
            at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))), pow2(pp))))), Nat.add(Word.to_nat(1n+pp,
            WCon{ab, at}), Nat.add(Word.to_nat(1n+pp, WCon{Bool.not(bb2), Word.not(pp, bt)}), bit_nat(cc))),
            nat_add_assoc(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.double(Word.to_nat(pp, Word.adc(pp,
            at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))), Nat.double(Nat.mul(adc_k(pp, at, bt, True{},
            fa_k(Bool.full_add(ab, Bool.not(bb2), cc))), pow2(pp)))), Equal.trans(Nat,
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.add(Nat.double(Word.to_nat(pp,
            Word.adc(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))), Nat.double(Nat.mul(adc_k(pp,
            at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))), pow2(pp))))),
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.double(Nat.add(Word.to_nat(pp,
            Word.adc(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))), Nat.mul(adc_k(pp, at, bt,
            True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))), pow2(pp))))), Nat.add(Word.to_nat(1n+pp, WCon{ab,
            at}), Nat.add(Word.to_nat(1n+pp, WCon{Bool.not(bb2), Word.not(pp, bt)}), bit_nat(cc))), Equal.cong(Nat,
            Nat, z46 => Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), z46),
            Nat.add(Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2),
            cc))))), Nat.double(Nat.mul(adc_k(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))),
            pow2(pp)))), Nat.double(Nat.add(Word.to_nat(pp, Word.adc(pp, at, bt, True{}, fa_k(Bool.full_add(ab,
            Bool.not(bb2), cc)))), Nat.mul(adc_k(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))),
            pow2(pp)))), Equal.sym(Nat, Nat.double(Nat.add(Word.to_nat(pp, Word.adc(pp, at, bt, True{},
            fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))), Nat.mul(adc_k(pp, at, bt, True{}, fa_k(Bool.full_add(ab,
            Bool.not(bb2), cc))), pow2(pp)))), Nat.add(Nat.double(Word.to_nat(pp, Word.adc(pp, at, bt, True{},
            fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))), Nat.double(Nat.mul(adc_k(pp, at, bt, True{},
            fa_k(Bool.full_add(ab, Bool.not(bb2), cc))), pow2(pp)))), nat_double_add(Word.to_nat(pp, Word.adc(pp, at,
            bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))), Nat.mul(adc_k(pp, at, bt, True{},
            fa_k(Bool.full_add(ab, Bool.not(bb2), cc))), pow2(pp))))), Equal.trans(Nat,
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.double(Nat.add(Word.to_nat(pp,
            Word.adc(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))), Nat.mul(adc_k(pp, at, bt,
            True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))), pow2(pp))))), Nat.add(bit_nat(fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc))), Nat.double(Nat.add(Word.to_nat(pp, at), Nat.add(Word.to_nat(pp, adc_sel(pp, bt,
            True{})), bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))))), Nat.add(Word.to_nat(1n+pp, WCon{ab,
            at}), Nat.add(Word.to_nat(1n+pp, WCon{Bool.not(bb2), Word.not(pp, bt)}), bit_nat(cc))), Equal.cong(Nat,
            Nat, z47 => Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.double(z47)),
            Nat.add(Word.to_nat(pp, Word.adc(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))),
            Nat.mul(adc_k(pp, at, bt, True{}, fa_k(Bool.full_add(ab, Bool.not(bb2), cc))), pow2(pp))),
            Nat.add(Word.to_nat(pp, at), Nat.add(Word.to_nat(pp, adc_sel(pp, bt, True{})),
            bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))), w_adc(pp, at, bt, True{}, fa_k(Bool.full_add(ab,
            Bool.not(bb2), cc)))), Equal.trans(Nat, Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))),
            Nat.double(Nat.add(Word.to_nat(pp, at), Nat.add(Word.to_nat(pp, adc_sel(pp, bt, True{})),
            bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))))), Nat.add(bit_nat(fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Nat.add(Word.to_nat(pp,
            adc_sel(pp, bt, True{})), bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))))),
            Nat.add(Word.to_nat(1n+pp, WCon{ab, at}), Nat.add(Word.to_nat(1n+pp, WCon{Bool.not(bb2), Word.not(pp,
            bt)}), bit_nat(cc))), Equal.cong(Nat, Nat, z48 => Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2),
            cc))), z48), Nat.double(Nat.add(Word.to_nat(pp, at), Nat.add(Word.to_nat(pp, adc_sel(pp, bt, True{})),
            bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Nat.add(Word.to_nat(pp, adc_sel(pp, bt, True{})), bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2),
            cc)))))), nat_double_add(Word.to_nat(pp, at), Nat.add(Word.to_nat(pp, adc_sel(pp, bt, True{})),
            bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))))), Equal.trans(Nat,
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Nat.add(Word.to_nat(pp, adc_sel(pp, bt, True{})), bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2),
            cc))))))), Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.add(Nat.double(Word.to_nat(pp,
            at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))))), Nat.add(Word.to_nat(1n+pp, WCon{ab,
            at}), Nat.add(Word.to_nat(1n+pp, WCon{Bool.not(bb2), Word.not(pp, bt)}), bit_nat(cc))), Equal.cong(Nat,
            Nat, z49 => Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.add(Nat.double(Word.to_nat(pp,
            at)), z49)), Nat.double(Nat.add(Word.to_nat(pp, adc_sel(pp, bt, True{})), bit_nat(fa_k(Bool.full_add(ab,
            Bool.not(bb2), cc))))), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))), nat_double_add(Word.to_nat(pp,
            adc_sel(pp, bt, True{})), bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))), Equal.trans(Nat,
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            Bool.not(bb2), cc))))))), Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))), Nat.add(Word.to_nat(1n+pp, WCon{ab, at}),
            Nat.add(Word.to_nat(1n+pp, WCon{Bool.not(bb2), Word.not(pp, bt)}), bit_nat(cc))), Equal.trans(Nat,
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            Bool.not(bb2), cc))))))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{}))), Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))),
            bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc)))))), Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc))), Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))),
            Equal.trans(Nat, Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))))), Nat.add(bit_nat(fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))), bit_nat(fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc)))))), Equal.cong(Nat, Nat, z51 => Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2),
            cc))), z51), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            True{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))))), Equal.cong(Nat, Nat,
            z50 => Nat.add(Nat.double(Word.to_nat(pp, at)), z50), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            True{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            Bool.not(bb2), cc))))), {==})), Equal.trans(Nat, Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2),
            cc))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            True{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            Bool.not(bb2), cc))))))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{}))), Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))),
            bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc)))))), nat_add_lcomm(bit_nat(fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc))), Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            True{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))))), Equal.cong(Nat, Nat,
            z53 => Nat.add(Nat.double(Word.to_nat(pp, at)), z53), Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2),
            cc))), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))))), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{}))), Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))),
            bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))))), Equal.trans(Nat,
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp,
            bt, True{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))))),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc))), Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))))),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))), bit_nat(fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc))))), nat_add_lcomm(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            Bool.not(bb2), cc))))), Equal.cong(Nat, Nat, z52 => Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            True{}))), z52), Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))), bit_nat(fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc)))), nat_add_comm(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))))))))), Equal.sym(Nat,
            Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))), bit_nat(fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc)))))), Equal.trans(Nat, Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2),
            cc))), Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))), Nat.add(Nat.double(Word.to_nat(pp,
            at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))),
            Nat.add(Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))),
            bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc)))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))), bit_nat(fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc)))))), Equal.cong(Nat, Nat, z54 => Nat.add(z54, Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))), Nat.add(bit_nat(fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc))), Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))), bit_nat(fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc)))), nat_add_comm(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))))), Equal.trans(Nat,
            Nat.add(Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))),
            bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc)))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))),
            Nat.add(Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))),
            bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc)))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))), bit_nat(fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc)))))), Equal.cong(Nat, Nat,
            z55 => Nat.add(Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))),
            bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc)))), z55), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))), {==}), Equal.trans(Nat,
            Nat.add(Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))),
            bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc)))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))), Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            Bool.not(bb2), cc)))), Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))), bit_nat(fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc)))))), nat_add_assoc(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))),
            bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))), Equal.trans(Nat,
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))),
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))))), Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            Bool.not(bb2), cc)))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{}))), bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc)))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))), bit_nat(fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc)))))), Equal.cong(Nat, Nat, z57 => Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            Bool.not(bb2), cc)))), z57), Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))))), Equal.trans(Nat,
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            True{}))))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            True{}))), bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))))),
            nat_add_lcomm(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))), Equal.cong(Nat, Nat,
            z56 => Nat.add(Nat.double(Word.to_nat(pp, at)), z56), Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2),
            cc))), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{}))), bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc)))),
            nat_add_comm(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))), Nat.double(Word.to_nat(pp, adc_sel(pp,
            bt, True{}))))))), Equal.trans(Nat, Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2),
            cc)))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            True{}))), bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc)))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{}))), bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc)))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))), bit_nat(fa_s(Bool.full_add(ab,
            Bool.not(bb2), cc)))))), nat_add_lcomm(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))),
            Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))))), Equal.cong(Nat, Nat,
            z58 => Nat.add(Nat.double(Word.to_nat(pp, at)), z58), Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab,
            Bool.not(bb2), cc)))), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))))), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            True{}))), Nat.add(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))),
            bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))))),
            nat_add_lcomm(Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc)))), Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{}))), bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc)))))))))))), Equal.trans(Nat,
            Nat.add(Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))), Nat.add(Nat.add(bit_nat(ab),
            Nat.add(bit_nat(Bool.not(bb2)), bit_nat(cc))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))), Nat.add(Word.to_nat(1n+pp, WCon{ab, at}),
            Nat.add(Word.to_nat(1n+pp, WCon{Bool.not(bb2), Word.not(pp, bt)}), bit_nat(cc))), Equal.cong(Nat, Nat,
            z59 => Nat.add(z59, Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            True{}))))), Nat.add(bit_nat(fa_s(Bool.full_add(ab, Bool.not(bb2), cc))),
            Nat.double(bit_nat(fa_k(Bool.full_add(ab, Bool.not(bb2), cc))))), Nat.add(bit_nat(ab),
            Nat.add(bit_nat(Bool.not(bb2)), bit_nat(cc))), fa_nat(ab, Bool.not(bb2), cc)), Equal.trans(Nat,
            Nat.add(Nat.add(bit_nat(ab), Nat.add(bit_nat(Bool.not(bb2)), bit_nat(cc))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))),
            Nat.add(Nat.add(bit_nat(ab), Nat.double(Word.to_nat(pp, at))), Nat.add(Nat.add(bit_nat(Bool.not(bb2)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))), bit_nat(cc))), Nat.add(Word.to_nat(1n+pp, WCon{ab,
            at}), Nat.add(Word.to_nat(1n+pp, WCon{Bool.not(bb2), Word.not(pp, bt)}), bit_nat(cc))), Equal.trans(Nat,
            Nat.add(Nat.add(bit_nat(ab), Nat.add(bit_nat(Bool.not(bb2)), bit_nat(cc))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.add(bit_nat(Bool.not(bb2)), Nat.add(bit_nat(ab), bit_nat(cc))))), Nat.add(Nat.add(bit_nat(ab),
            Nat.double(Word.to_nat(pp, at))), Nat.add(Nat.add(bit_nat(Bool.not(bb2)), Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{})))), bit_nat(cc))), Equal.trans(Nat, Nat.add(Nat.add(bit_nat(ab),
            Nat.add(bit_nat(Bool.not(bb2)), bit_nat(cc))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))), Nat.add(Nat.add(bit_nat(Bool.not(bb2)),
            Nat.add(bit_nat(ab), bit_nat(cc))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{}))))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{}))), Nat.add(bit_nat(Bool.not(bb2)), Nat.add(bit_nat(ab), bit_nat(cc))))),
            Equal.cong(Nat, Nat, z61 => Nat.add(z61, Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))), Nat.add(bit_nat(ab),
            Nat.add(bit_nat(Bool.not(bb2)), bit_nat(cc))), Nat.add(bit_nat(Bool.not(bb2)), Nat.add(bit_nat(ab),
            bit_nat(cc))), Equal.trans(Nat, Nat.add(bit_nat(ab), Nat.add(bit_nat(Bool.not(bb2)), bit_nat(cc))),
            Nat.add(bit_nat(ab), Nat.add(bit_nat(Bool.not(bb2)), bit_nat(cc))), Nat.add(bit_nat(Bool.not(bb2)),
            Nat.add(bit_nat(ab), bit_nat(cc))), Equal.cong(Nat, Nat, z60 => Nat.add(bit_nat(ab), z60),
            Nat.add(bit_nat(Bool.not(bb2)), bit_nat(cc)), Nat.add(bit_nat(Bool.not(bb2)), bit_nat(cc)), {==}),
            nat_add_lcomm(bit_nat(ab), bit_nat(Bool.not(bb2)), bit_nat(cc)))), Equal.trans(Nat,
            Nat.add(Nat.add(bit_nat(Bool.not(bb2)), Nat.add(bit_nat(ab), bit_nat(cc))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))),
            Nat.add(Nat.add(bit_nat(Bool.not(bb2)), Nat.add(bit_nat(ab), bit_nat(cc))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.add(bit_nat(Bool.not(bb2)), Nat.add(bit_nat(ab), bit_nat(cc))))), Equal.cong(Nat, Nat,
            z62 => Nat.add(Nat.add(bit_nat(Bool.not(bb2)), Nat.add(bit_nat(ab), bit_nat(cc))), z62),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))), {==}),
            Equal.trans(Nat, Nat.add(Nat.add(bit_nat(Bool.not(bb2)), Nat.add(bit_nat(ab), bit_nat(cc))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))),
            Nat.add(bit_nat(Bool.not(bb2)), Nat.add(Nat.add(bit_nat(ab), bit_nat(cc)),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.add(bit_nat(Bool.not(bb2)), Nat.add(bit_nat(ab), bit_nat(cc))))), nat_add_assoc(bit_nat(Bool.not(bb2)),
            Nat.add(bit_nat(ab), bit_nat(cc)), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{}))))), Equal.trans(Nat, Nat.add(bit_nat(Bool.not(bb2)), Nat.add(Nat.add(bit_nat(ab),
            bit_nat(cc)), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            True{})))))), Nat.add(bit_nat(Bool.not(bb2)), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(ab), bit_nat(cc))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.add(bit_nat(Bool.not(bb2)), Nat.add(bit_nat(ab), bit_nat(cc))))), Equal.cong(Nat, Nat,
            z66 => Nat.add(bit_nat(Bool.not(bb2)), z66), Nat.add(Nat.add(bit_nat(ab), bit_nat(cc)),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.add(bit_nat(ab), bit_nat(cc)))), Equal.trans(Nat, Nat.add(Nat.add(bit_nat(ab), bit_nat(cc)),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))),
            Nat.add(bit_nat(ab), Nat.add(bit_nat(cc), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(ab), bit_nat(cc)))),
            nat_add_assoc(bit_nat(ab), bit_nat(cc), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{}))))), Equal.trans(Nat, Nat.add(bit_nat(ab), Nat.add(bit_nat(cc),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))))),
            Nat.add(bit_nat(ab), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{}))), bit_nat(cc)))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(ab), bit_nat(cc)))),
            Equal.cong(Nat, Nat, z64 => Nat.add(bit_nat(ab), z64), Nat.add(bit_nat(cc),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            bit_nat(cc))), Equal.trans(Nat, Nat.add(bit_nat(cc), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(bit_nat(cc), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            bit_nat(cc))), nat_add_lcomm(bit_nat(cc), Nat.double(Word.to_nat(pp, at)), Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{})))), Equal.cong(Nat, Nat, z63 => Nat.add(Nat.double(Word.to_nat(pp, at)), z63),
            Nat.add(bit_nat(cc), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), bit_nat(cc)), nat_add_comm(bit_nat(cc),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))))), Equal.trans(Nat, Nat.add(bit_nat(ab),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            bit_nat(cc)))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(bit_nat(ab),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), bit_nat(cc)))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.add(bit_nat(ab), bit_nat(cc)))), nat_add_lcomm(bit_nat(ab), Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), bit_nat(cc))), Equal.cong(Nat, Nat,
            z65 => Nat.add(Nat.double(Word.to_nat(pp, at)), z65), Nat.add(bit_nat(ab),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), bit_nat(cc))),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(ab), bit_nat(cc))),
            nat_add_lcomm(bit_nat(ab), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), bit_nat(cc))))))),
            Equal.trans(Nat, Nat.add(bit_nat(Bool.not(bb2)), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(ab), bit_nat(cc))))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(bit_nat(Bool.not(bb2)), Nat.add(Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{}))), Nat.add(bit_nat(ab), bit_nat(cc))))), Nat.add(Nat.double(Word.to_nat(pp, at)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(Bool.not(bb2)),
            Nat.add(bit_nat(ab), bit_nat(cc))))), nat_add_lcomm(bit_nat(Bool.not(bb2)), Nat.double(Word.to_nat(pp,
            at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(ab), bit_nat(cc)))),
            Equal.cong(Nat, Nat, z67 => Nat.add(Nat.double(Word.to_nat(pp, at)), z67), Nat.add(bit_nat(Bool.not(bb2)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(ab), bit_nat(cc)))),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(Bool.not(bb2)),
            Nat.add(bit_nat(ab), bit_nat(cc)))), nat_add_lcomm(bit_nat(Bool.not(bb2)), Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{}))), Nat.add(bit_nat(ab), bit_nat(cc))))))))), Equal.sym(Nat,
            Nat.add(Nat.add(bit_nat(ab), Nat.double(Word.to_nat(pp, at))), Nat.add(Nat.add(bit_nat(Bool.not(bb2)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))), bit_nat(cc))), Nat.add(Nat.double(Word.to_nat(pp,
            at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(Bool.not(bb2)),
            Nat.add(bit_nat(ab), bit_nat(cc))))), Equal.trans(Nat, Nat.add(Nat.add(bit_nat(ab),
            Nat.double(Word.to_nat(pp, at))), Nat.add(Nat.add(bit_nat(Bool.not(bb2)), Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{})))), bit_nat(cc))), Nat.add(Nat.add(Nat.double(Word.to_nat(pp, at)), bit_nat(ab)),
            Nat.add(Nat.add(bit_nat(Bool.not(bb2)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))),
            bit_nat(cc))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            True{}))), Nat.add(bit_nat(Bool.not(bb2)), Nat.add(bit_nat(ab), bit_nat(cc))))), Equal.cong(Nat, Nat,
            z69 => Nat.add(z69, Nat.add(Nat.add(bit_nat(Bool.not(bb2)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            True{})))), bit_nat(cc))), Nat.add(bit_nat(ab), Nat.double(Word.to_nat(pp, at))),
            Nat.add(Nat.double(Word.to_nat(pp, at)), bit_nat(ab)), nat_add_comm(bit_nat(ab), Nat.double(Word.to_nat(pp,
            at)))), Equal.trans(Nat, Nat.add(Nat.add(Nat.double(Word.to_nat(pp, at)), bit_nat(ab)),
            Nat.add(Nat.add(bit_nat(Bool.not(bb2)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))),
            bit_nat(cc))), Nat.add(Nat.add(Nat.double(Word.to_nat(pp, at)), bit_nat(ab)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(Bool.not(bb2)),
            bit_nat(cc)))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            True{}))), Nat.add(bit_nat(Bool.not(bb2)), Nat.add(bit_nat(ab), bit_nat(cc))))), Equal.cong(Nat, Nat,
            z70 => Nat.add(Nat.add(Nat.double(Word.to_nat(pp, at)), bit_nat(ab)), z70),
            Nat.add(Nat.add(bit_nat(Bool.not(bb2)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))),
            bit_nat(cc)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(Bool.not(bb2)),
            bit_nat(cc))), Equal.trans(Nat, Nat.add(Nat.add(bit_nat(Bool.not(bb2)), Nat.double(Word.to_nat(pp,
            adc_sel(pp, bt, True{})))), bit_nat(cc)), Nat.add(Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            True{}))), bit_nat(Bool.not(bb2))), bit_nat(cc)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            True{}))), Nat.add(bit_nat(Bool.not(bb2)), bit_nat(cc))), Equal.cong(Nat, Nat, z68 => Nat.add(z68,
            bit_nat(cc)), Nat.add(bit_nat(Bool.not(bb2)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), bit_nat(Bool.not(bb2))),
            nat_add_comm(bit_nat(Bool.not(bb2)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))))),
            nat_add_assoc(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), bit_nat(Bool.not(bb2)), bit_nat(cc)))),
            Equal.trans(Nat, Nat.add(Nat.add(Nat.double(Word.to_nat(pp, at)), bit_nat(ab)),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(Bool.not(bb2)),
            bit_nat(cc)))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(bit_nat(ab),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(Bool.not(bb2)),
            bit_nat(cc))))), Nat.add(Nat.double(Word.to_nat(pp, at)), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp,
            bt, True{}))), Nat.add(bit_nat(Bool.not(bb2)), Nat.add(bit_nat(ab), bit_nat(cc))))),
            nat_add_assoc(Nat.double(Word.to_nat(pp, at)), bit_nat(ab), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp,
            bt, True{}))), Nat.add(bit_nat(Bool.not(bb2)), bit_nat(cc)))), Equal.cong(Nat, Nat,
            z72 => Nat.add(Nat.double(Word.to_nat(pp, at)), z72), Nat.add(bit_nat(ab),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(Bool.not(bb2)),
            bit_nat(cc)))), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))),
            Nat.add(bit_nat(Bool.not(bb2)), Nat.add(bit_nat(ab), bit_nat(cc)))), Equal.trans(Nat, Nat.add(bit_nat(ab),
            Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(Bool.not(bb2)),
            bit_nat(cc)))), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(ab),
            Nat.add(bit_nat(Bool.not(bb2)), bit_nat(cc)))), Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            True{}))), Nat.add(bit_nat(Bool.not(bb2)), Nat.add(bit_nat(ab), bit_nat(cc)))), nat_add_lcomm(bit_nat(ab),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), Nat.add(bit_nat(Bool.not(bb2)), bit_nat(cc))),
            Equal.cong(Nat, Nat, z71 => Nat.add(Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{}))), z71),
            Nat.add(bit_nat(ab), Nat.add(bit_nat(Bool.not(bb2)), bit_nat(cc))), Nat.add(bit_nat(Bool.not(bb2)),
            Nat.add(bit_nat(ab), bit_nat(cc))), nat_add_lcomm(bit_nat(ab), bit_nat(Bool.not(bb2)),
            bit_nat(cc)))))))))), Equal.trans(Nat, Nat.add(Nat.add(bit_nat(ab), Nat.double(Word.to_nat(pp, at))),
            Nat.add(Nat.add(bit_nat(Bool.not(bb2)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))),
            bit_nat(cc))), Nat.add(Word.to_nat(1n+pp, WCon{ab, at}), Nat.add(Nat.add(bit_nat(Bool.not(bb2)),
            Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))), bit_nat(cc))), Nat.add(Word.to_nat(1n+pp, WCon{ab,
            at}), Nat.add(Word.to_nat(1n+pp, WCon{Bool.not(bb2), Word.not(pp, bt)}), bit_nat(cc))), Equal.cong(Nat,
            Nat, z73 => Nat.add(z73, Nat.add(Nat.add(bit_nat(Bool.not(bb2)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt,
            True{})))), bit_nat(cc))), Nat.add(bit_nat(ab), Nat.double(Word.to_nat(pp, at))), Word.to_nat(1n+pp,
            WCon{ab, at}), Equal.sym(Nat, Word.to_nat(1n+pp, WCon{ab, at}), Nat.add(bit_nat(ab),
            Nat.double(Word.to_nat(pp, at))), w_nat_con(pp, ab, at))), Equal.cong(Nat, Nat,
            z74 => Nat.add(Word.to_nat(1n+pp, WCon{ab, at}), Nat.add(z74, bit_nat(cc))),
            Nat.add(bit_nat(Bool.not(bb2)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))), Word.to_nat(1n+pp,
            WCon{Bool.not(bb2), Word.not(pp, bt)}), Equal.sym(Nat, Word.to_nat(1n+pp, WCon{Bool.not(bb2), Word.not(pp,
            bt)}), Nat.add(bit_nat(Bool.not(bb2)), Nat.double(Word.to_nat(pp, adc_sel(pp, bt, True{})))), w_nat_con(pp,
            Bool.not(bb2), Word.not(pp, bt))))))))))))))))

# w_adc, with 2^nn named through uu

# w_adc, with 2^nn named through uu
law w_adc_u:
  for +nn: Nat
  for uu: Unit
  for aa: Word(nn)
  for bb: Word(nn)
  for ff: Bool
  for cc: Bool
  {Nat.add(Word.to_nat(nn, Word.adc(nn, aa, bb, ff, cc)), Nat.mul(adc_k(nn, aa, bb, ff, cc), pow2u(nn, uu))) ==
    Nat.add(Word.to_nat(nn, aa), Nat.add(Word.to_nat(nn, adc_sel(nn, bb, ff)), bit_nat(cc))) : Nat}

# the proof of the law above
def w_adc_u(nn, uu, aa, bb, ff, cc):
  match uu:
    case Unit{}:
      w_adc(nn, aa, bb, ff, cc)

# the carry out of a U32 sum

# the carry out of a U32 sum
def uadd_k(aa: U32, bb: U32) -> Nat:
  match aa bb:
    case U32{xw} U32{yw}:
      adc_k(32n, xw, yw, False{}, False{})

# a U32 sum, and its carry times 2^32, is the Nat sum

# a U32 sum, and its carry times 2^32, is the Nat sum
law u_add:
  for +uu: Unit
  for aa: U32
  for bb: U32
  {Nat.add(U32.to_nat(U32.add(aa, bb)), Nat.mul(uadd_k(aa, bb), pow2u(32n, uu))) ==
    Nat.add(U32.to_nat(aa), U32.to_nat(bb)) : Nat}

# the proof of the law above
def u_add(uu, aa, bb):
  match aa bb:
    case U32{+xw} U32{+yw}:
      Equal.trans(Nat, Nat.add(Word.to_nat(32n, Word.adc(32n, xw, yw, False{}, False{})),
        Nat.mul(adc_k(32n, xw, yw, False{}, False{}), pow2u(32n, uu))),
        Nat.add(Word.to_nat(32n, xw), Nat.add(Word.to_nat(32n, yw), 0n)),
        Nat.add(Word.to_nat(32n, xw), Word.to_nat(32n, yw)),
        w_adc_u(32n, uu, xw, yw, False{}, False{}),
        Equal.cong(Nat, Nat, zz => Nat.add(Word.to_nat(32n, xw), zz), Nat.add(Word.to_nat(32n, yw), 0n),
          Word.to_nat(32n, yw), nat_add_zero(Word.to_nat(32n, yw))))

# the borrow count of a U32 difference

# the borrow count of a U32 difference
def usub_k(aa: U32, bb: U32) -> Nat:
  match aa bb:
    case U32{xw} U32{yw}:
      adc_k(32n, xw, yw, True{}, True{})

# a U32 difference, its borrow count times 2^32 and what it takes away make
# the first U32 and 2^32

# a U32 difference, its borrow count times 2^32 and what it takes away make
# the first U32 and 2^32
law u_sub:
  for +uu: Unit
  for aa: U32
  for bb: U32
  {Nat.add(U32.to_nat(U32.sub(aa, bb)), Nat.add(Nat.mul(usub_k(aa, bb), pow2u(32n, uu)), U32.to_nat(bb))) ==
    Nat.add(U32.to_nat(aa), pow2u(32n, uu)) : Nat}

# the proof of the law above
def u_sub(uu, aa, bb):
  match aa bb:
    case U32{+xw} U32{+yw}:
      Equal.trans(Nat, Nat.add(Word.to_nat(32n, Word.adc(32n, xw, yw, True{}, True{})), Nat.add(Nat.mul(adc_k(32n, xw,
        yw, True{}, True{}), pow2u(32n, uu)), Word.to_nat(32n, yw))), Nat.add(Nat.add(Word.to_nat(32n, Word.adc(32n,
        xw, yw, True{}, True{})), Nat.mul(adc_k(32n, xw, yw, True{}, True{}), pow2u(32n, uu))), Word.to_nat(32n, yw)),
        Nat.add(Word.to_nat(32n, xw), pow2u(32n, uu)), Equal.sym(Nat, Nat.add(Nat.add(Word.to_nat(32n, Word.adc(32n,
        xw, yw, True{}, True{})), Nat.mul(adc_k(32n, xw, yw, True{}, True{}), pow2u(32n, uu))), Word.to_nat(32n, yw)),
        Nat.add(Word.to_nat(32n, Word.adc(32n, xw, yw, True{}, True{})), Nat.add(Nat.mul(adc_k(32n, xw, yw, True{},
        True{}), pow2u(32n, uu)), Word.to_nat(32n, yw))), nat_add_assoc(Word.to_nat(32n, Word.adc(32n, xw, yw, True{},
        True{})), Nat.mul(adc_k(32n, xw, yw, True{}, True{}), pow2u(32n, uu)), Word.to_nat(32n, yw))), Equal.trans(Nat,
        Nat.add(Nat.add(Word.to_nat(32n, Word.adc(32n, xw, yw, True{}, True{})), Nat.mul(adc_k(32n, xw, yw, True{},
        True{}), pow2u(32n, uu))), Word.to_nat(32n, yw)), Nat.add(Nat.add(Word.to_nat(32n, xw),
        Nat.add(Word.to_nat(32n, Word.not(32n, yw)), 1n)), Word.to_nat(32n, yw)), Nat.add(Word.to_nat(32n, xw),
        pow2u(32n, uu)), Equal.cong(Nat, Nat, z75 => Nat.add(z75, Word.to_nat(32n, yw)), Nat.add(Word.to_nat(32n,
        Word.adc(32n, xw, yw, True{}, True{})), Nat.mul(adc_k(32n, xw, yw, True{}, True{}), pow2u(32n, uu))),
        Nat.add(Word.to_nat(32n, xw), Nat.add(Word.to_nat(32n, Word.not(32n, yw)), 1n)), w_adc_u(32n, uu, xw, yw,
        True{}, True{})), Equal.trans(Nat, Nat.add(Nat.add(Word.to_nat(32n, xw), Nat.add(Word.to_nat(32n, Word.not(32n,
        yw)), 1n)), Word.to_nat(32n, yw)), Nat.add(Word.to_nat(32n, xw), Nat.add(Word.to_nat(32n, Word.not(32n, yw)),
        Nat.add(Word.to_nat(32n, yw), 1n))), Nat.add(Word.to_nat(32n, xw), pow2u(32n, uu)), Equal.trans(Nat,
        Nat.add(Nat.add(Word.to_nat(32n, xw), Nat.add(Word.to_nat(32n, Word.not(32n, yw)), 1n)), Word.to_nat(32n, yw)),
        Nat.add(1n, Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Nat.add(Word.to_nat(32n, xw), Word.to_nat(32n, yw)))),
        Nat.add(Word.to_nat(32n, xw), Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Nat.add(Word.to_nat(32n, yw), 1n))),
        Equal.trans(Nat, Nat.add(Nat.add(Word.to_nat(32n, xw), Nat.add(Word.to_nat(32n, Word.not(32n, yw)), 1n)),
        Word.to_nat(32n, yw)), Nat.add(Nat.add(1n, Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Word.to_nat(32n, xw))),
        Word.to_nat(32n, yw)), Nat.add(1n, Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Nat.add(Word.to_nat(32n, xw),
        Word.to_nat(32n, yw)))), Equal.cong(Nat, Nat, z78 => Nat.add(z78, Word.to_nat(32n, yw)),
        Nat.add(Word.to_nat(32n, xw), Nat.add(Word.to_nat(32n, Word.not(32n, yw)), 1n)), Nat.add(1n,
        Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Word.to_nat(32n, xw))), Equal.trans(Nat, Nat.add(Word.to_nat(32n,
        xw), Nat.add(Word.to_nat(32n, Word.not(32n, yw)), 1n)), Nat.add(Word.to_nat(32n, xw), Nat.add(1n,
        Word.to_nat(32n, Word.not(32n, yw)))), Nat.add(1n, Nat.add(Word.to_nat(32n, Word.not(32n, yw)),
        Word.to_nat(32n, xw))), Equal.cong(Nat, Nat, z76 => Nat.add(Word.to_nat(32n, xw), z76),
        Nat.add(Word.to_nat(32n, Word.not(32n, yw)), 1n), Nat.add(1n, Word.to_nat(32n, Word.not(32n, yw))),
        nat_add_comm(Word.to_nat(32n, Word.not(32n, yw)), 1n)), Equal.trans(Nat, Nat.add(Word.to_nat(32n, xw),
        Nat.add(1n, Word.to_nat(32n, Word.not(32n, yw)))), Nat.add(1n, Nat.add(Word.to_nat(32n, xw), Word.to_nat(32n,
        Word.not(32n, yw)))), Nat.add(1n, Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Word.to_nat(32n, xw))),
        nat_add_lcomm(Word.to_nat(32n, xw), 1n, Word.to_nat(32n, Word.not(32n, yw))), Equal.cong(Nat, Nat,
        z77 => Nat.add(1n, z77), Nat.add(Word.to_nat(32n, xw), Word.to_nat(32n, Word.not(32n, yw))),
        Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Word.to_nat(32n, xw)), nat_add_comm(Word.to_nat(32n, xw),
        Word.to_nat(32n, Word.not(32n, yw))))))), Equal.trans(Nat, Nat.add(Nat.add(1n, Nat.add(Word.to_nat(32n,
        Word.not(32n, yw)), Word.to_nat(32n, xw))), Word.to_nat(32n, yw)), Nat.add(1n, Nat.add(Nat.add(Word.to_nat(32n,
        Word.not(32n, yw)), Word.to_nat(32n, xw)), Word.to_nat(32n, yw))), Nat.add(1n, Nat.add(Word.to_nat(32n,
        Word.not(32n, yw)), Nat.add(Word.to_nat(32n, xw), Word.to_nat(32n, yw)))), nat_add_assoc(1n,
        Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Word.to_nat(32n, xw)), Word.to_nat(32n, yw)), Equal.cong(Nat, Nat,
        z79 => Nat.add(1n, z79), Nat.add(Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Word.to_nat(32n, xw)),
        Word.to_nat(32n, yw)), Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Nat.add(Word.to_nat(32n, xw),
        Word.to_nat(32n, yw))), nat_add_assoc(Word.to_nat(32n, Word.not(32n, yw)), Word.to_nat(32n, xw),
        Word.to_nat(32n, yw))))), Equal.sym(Nat, Nat.add(Word.to_nat(32n, xw), Nat.add(Word.to_nat(32n, Word.not(32n,
        yw)), Nat.add(Word.to_nat(32n, yw), 1n))), Nat.add(1n, Nat.add(Word.to_nat(32n, Word.not(32n, yw)),
        Nat.add(Word.to_nat(32n, xw), Word.to_nat(32n, yw)))), Equal.trans(Nat, Nat.add(Word.to_nat(32n, xw),
        Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Nat.add(Word.to_nat(32n, yw), 1n))), Nat.add(Word.to_nat(32n, xw),
        Nat.add(1n, Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Word.to_nat(32n, yw)))), Nat.add(1n,
        Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Nat.add(Word.to_nat(32n, xw), Word.to_nat(32n, yw)))),
        Equal.cong(Nat, Nat, z81 => Nat.add(Word.to_nat(32n, xw), z81), Nat.add(Word.to_nat(32n, Word.not(32n, yw)),
        Nat.add(Word.to_nat(32n, yw), 1n)), Nat.add(1n, Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Word.to_nat(32n,
        yw))), Equal.trans(Nat, Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Nat.add(Word.to_nat(32n, yw), 1n)),
        Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Nat.add(1n, Word.to_nat(32n, yw))), Nat.add(1n,
        Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Word.to_nat(32n, yw))), Equal.cong(Nat, Nat,
        z80 => Nat.add(Word.to_nat(32n, Word.not(32n, yw)), z80), Nat.add(Word.to_nat(32n, yw), 1n), Nat.add(1n,
        Word.to_nat(32n, yw)), nat_add_comm(Word.to_nat(32n, yw), 1n)), nat_add_lcomm(Word.to_nat(32n, Word.not(32n,
        yw)), 1n, Word.to_nat(32n, yw)))), Equal.trans(Nat, Nat.add(Word.to_nat(32n, xw), Nat.add(1n,
        Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Word.to_nat(32n, yw)))), Nat.add(1n, Nat.add(Word.to_nat(32n, xw),
        Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Word.to_nat(32n, yw)))), Nat.add(1n, Nat.add(Word.to_nat(32n,
        Word.not(32n, yw)), Nat.add(Word.to_nat(32n, xw), Word.to_nat(32n, yw)))), nat_add_lcomm(Word.to_nat(32n, xw),
        1n, Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Word.to_nat(32n, yw))), Equal.cong(Nat, Nat,
        z82 => Nat.add(1n, z82), Nat.add(Word.to_nat(32n, xw), Nat.add(Word.to_nat(32n, Word.not(32n, yw)),
        Word.to_nat(32n, yw))), Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Nat.add(Word.to_nat(32n, xw),
        Word.to_nat(32n, yw))), nat_add_lcomm(Word.to_nat(32n, xw), Word.to_nat(32n, Word.not(32n, yw)),
        Word.to_nat(32n, yw))))))), Equal.cong(Nat, Nat, z83 => Nat.add(Word.to_nat(32n, xw), z83),
        Nat.add(Word.to_nat(32n, Word.not(32n, yw)), Nat.add(Word.to_nat(32n, yw), 1n)), pow2u(32n, uu), w_not_u(32n,
        uu, yw)))))

# JSON-TREE-6: word multiplication as Nat multiplication

# the bit shl.put shifts out, as a Nat

# the bit shl.put shifts out, as a Nat
def put_top(nn: Nat, ww: Word(nn), cc: Bool) -> Nat:
  match nn:
    case 0n:
      bit_nat(cc)
    case 1n+pp:
      match ww:
        case WCon{bb, tt}:
          put_top(pp, tt, bb)

# shl.put as Nats: c and twice w, less the bit shifted out

# shl.put as Nats: c and twice w, less the bit shifted out
law w_put:
  for +nn: Nat
  for ww: Word(nn)
  for +cc: Bool
  {Nat.add(Word.to_nat(nn, Word.shl.put(nn, cc, ww)), Nat.mul(put_top(nn, ww, cc), pow2(nn))) ==
    Nat.add(bit_nat(cc), Nat.double(Word.to_nat(nn, ww))) : Nat}

# the proof of the law above
def w_put(nn, ww, cc):
  match nn:
    case 0n:
      match ww:
        case WNil{}:
          Equal.trans(Nat, Nat.mul(bit_nat(cc), 1n), bit_nat(cc), Nat.add(bit_nat(cc), 0n), nat_mul_one(bit_nat(cc)),
            Equal.sym(Nat, Nat.add(bit_nat(cc), 0n), bit_nat(cc), nat_add_zero(bit_nat(cc))))
    case 1n+(+pp):
      match ww:
        case WCon{+bb, +tt}:
          Equal.trans(Nat, Nat.add(Word.to_nat(1n+pp, WCon{cc, Word.shl.put(pp, bb, tt)}), Nat.mul(put_top(pp, tt, bb),
            Nat.double(pow2(pp)))), Nat.add(Nat.add(bit_nat(cc), Nat.double(Word.to_nat(pp, Word.shl.put(pp, bb,
            tt)))), Nat.mul(put_top(pp, tt, bb), Nat.double(pow2(pp)))), Nat.add(bit_nat(cc),
            Nat.double(Word.to_nat(1n+pp, WCon{bb, tt}))), Equal.cong(Nat, Nat, z84 => Nat.add(z84, Nat.mul(put_top(pp,
            tt, bb), Nat.double(pow2(pp)))), Word.to_nat(1n+pp, WCon{cc, Word.shl.put(pp, bb, tt)}),
            Nat.add(bit_nat(cc), Nat.double(Word.to_nat(pp, Word.shl.put(pp, bb, tt)))), w_nat_con(pp, cc,
            Word.shl.put(pp, bb, tt))), Equal.trans(Nat, Nat.add(Nat.add(bit_nat(cc), Nat.double(Word.to_nat(pp,
            Word.shl.put(pp, bb, tt)))), Nat.mul(put_top(pp, tt, bb), Nat.double(pow2(pp)))),
            Nat.add(Nat.add(bit_nat(cc), Nat.double(Word.to_nat(pp, Word.shl.put(pp, bb, tt)))),
            Nat.double(Nat.mul(put_top(pp, tt, bb), pow2(pp)))), Nat.add(bit_nat(cc), Nat.double(Word.to_nat(1n+pp,
            WCon{bb, tt}))), Equal.cong(Nat, Nat, z85 => Nat.add(Nat.add(bit_nat(cc), Nat.double(Word.to_nat(pp,
            Word.shl.put(pp, bb, tt)))), z85), Nat.mul(put_top(pp, tt, bb), Nat.double(pow2(pp))),
            Nat.double(Nat.mul(put_top(pp, tt, bb), pow2(pp))), nat_mul_double_r(put_top(pp, tt, bb), pow2(pp))),
            Equal.trans(Nat, Nat.add(Nat.add(bit_nat(cc), Nat.double(Word.to_nat(pp, Word.shl.put(pp, bb, tt)))),
            Nat.double(Nat.mul(put_top(pp, tt, bb), pow2(pp)))), Nat.add(bit_nat(cc),
            Nat.add(Nat.double(Word.to_nat(pp, Word.shl.put(pp, bb, tt))), Nat.double(Nat.mul(put_top(pp, tt, bb),
            pow2(pp))))), Nat.add(bit_nat(cc), Nat.double(Word.to_nat(1n+pp, WCon{bb, tt}))),
            nat_add_assoc(bit_nat(cc), Nat.double(Word.to_nat(pp, Word.shl.put(pp, bb, tt))),
            Nat.double(Nat.mul(put_top(pp, tt, bb), pow2(pp)))), Equal.trans(Nat, Nat.add(bit_nat(cc),
            Nat.add(Nat.double(Word.to_nat(pp, Word.shl.put(pp, bb, tt))), Nat.double(Nat.mul(put_top(pp, tt, bb),
            pow2(pp))))), Nat.add(bit_nat(cc), Nat.double(Nat.add(Word.to_nat(pp, Word.shl.put(pp, bb, tt)),
            Nat.mul(put_top(pp, tt, bb), pow2(pp))))), Nat.add(bit_nat(cc), Nat.double(Word.to_nat(1n+pp, WCon{bb,
            tt}))), Equal.cong(Nat, Nat, z86 => Nat.add(bit_nat(cc), z86), Nat.add(Nat.double(Word.to_nat(pp,
            Word.shl.put(pp, bb, tt))), Nat.double(Nat.mul(put_top(pp, tt, bb), pow2(pp)))),
            Nat.double(Nat.add(Word.to_nat(pp, Word.shl.put(pp, bb, tt)), Nat.mul(put_top(pp, tt, bb), pow2(pp)))),
            Equal.sym(Nat, Nat.double(Nat.add(Word.to_nat(pp, Word.shl.put(pp, bb, tt)), Nat.mul(put_top(pp, tt, bb),
            pow2(pp)))), Nat.add(Nat.double(Word.to_nat(pp, Word.shl.put(pp, bb, tt))), Nat.double(Nat.mul(put_top(pp,
            tt, bb), pow2(pp)))), nat_double_add(Word.to_nat(pp, Word.shl.put(pp, bb, tt)), Nat.mul(put_top(pp, tt,
            bb), pow2(pp))))), Equal.trans(Nat, Nat.add(bit_nat(cc), Nat.double(Nat.add(Word.to_nat(pp,
            Word.shl.put(pp, bb, tt)), Nat.mul(put_top(pp, tt, bb), pow2(pp))))), Nat.add(bit_nat(cc),
            Nat.double(Nat.add(bit_nat(bb), Nat.double(Word.to_nat(pp, tt))))), Nat.add(bit_nat(cc),
            Nat.double(Word.to_nat(1n+pp, WCon{bb, tt}))), Equal.cong(Nat, Nat, z87 => Nat.add(bit_nat(cc),
            Nat.double(z87)), Nat.add(Word.to_nat(pp, Word.shl.put(pp, bb, tt)), Nat.mul(put_top(pp, tt, bb),
            pow2(pp))), Nat.add(bit_nat(bb), Nat.double(Word.to_nat(pp, tt))), w_put(pp, tt, bb)), Equal.cong(Nat, Nat,
            z88 => Nat.add(bit_nat(cc), Nat.double(z88)), Nat.add(bit_nat(bb), Nat.double(Word.to_nat(pp, tt))),
            Word.to_nat(1n+pp, WCon{bb, tt}), Equal.sym(Nat, Word.to_nat(1n+pp, WCon{bb, tt}), Nat.add(bit_nat(bb),
            Nat.double(Word.to_nat(pp, tt))), w_nat_con(pp, bb, tt))))))))

# the bit shl shifts out, as a Nat

# the bit shl shifts out, as a Nat
def shl_top(nn: Nat, ww: Word(nn)) -> Nat:
  match nn:
    case 0n:
      0n
    case 1n+pp:
      match ww:
        case WCon{bb, tt}:
          put_top(pp, tt, bb)

# shl as Nats: twice w, less the bit shifted out

# shl as Nats: twice w, less the bit shifted out
law w_shl:
  for +nn: Nat
  for ww: Word(nn)
  {Nat.add(Word.to_nat(nn, Word.shl(nn, ww)), Nat.mul(shl_top(nn, ww), pow2(nn))) ==
    Nat.double(Word.to_nat(nn, ww)) : Nat}

# the proof of the law above
def w_shl(nn, ww):
  match nn:
    case 0n:
      match ww:
        case WNil{}:
          {==}
    case 1n+(+pp):
      match ww:
        case WCon{+bb, +tt}:
          Equal.trans(Nat, Nat.add(Nat.double(Word.to_nat(pp, Word.shl.put(pp, bb, tt))), Nat.mul(put_top(pp, tt, bb),
            Nat.double(pow2(pp)))), Nat.add(Nat.double(Word.to_nat(pp, Word.shl.put(pp, bb, tt))),
            Nat.double(Nat.mul(put_top(pp, tt, bb), pow2(pp)))), Nat.double(Word.to_nat(1n+pp, WCon{bb, tt})),
            Equal.cong(Nat, Nat, z89 => Nat.add(Nat.double(Word.to_nat(pp, Word.shl.put(pp, bb, tt))), z89),
            Nat.mul(put_top(pp, tt, bb), Nat.double(pow2(pp))), Nat.double(Nat.mul(put_top(pp, tt, bb), pow2(pp))),
            nat_mul_double_r(put_top(pp, tt, bb), pow2(pp))), Equal.trans(Nat, Nat.add(Nat.double(Word.to_nat(pp,
            Word.shl.put(pp, bb, tt))), Nat.double(Nat.mul(put_top(pp, tt, bb), pow2(pp)))),
            Nat.double(Nat.add(Word.to_nat(pp, Word.shl.put(pp, bb, tt)), Nat.mul(put_top(pp, tt, bb), pow2(pp)))),
            Nat.double(Word.to_nat(1n+pp, WCon{bb, tt})), Equal.sym(Nat, Nat.double(Nat.add(Word.to_nat(pp,
            Word.shl.put(pp, bb, tt)), Nat.mul(put_top(pp, tt, bb), pow2(pp)))), Nat.add(Nat.double(Word.to_nat(pp,
            Word.shl.put(pp, bb, tt))), Nat.double(Nat.mul(put_top(pp, tt, bb), pow2(pp)))),
            nat_double_add(Word.to_nat(pp, Word.shl.put(pp, bb, tt)), Nat.mul(put_top(pp, tt, bb), pow2(pp)))),
            Equal.trans(Nat, Nat.double(Nat.add(Word.to_nat(pp, Word.shl.put(pp, bb, tt)), Nat.mul(put_top(pp, tt, bb),
            pow2(pp)))), Nat.double(Nat.add(bit_nat(bb), Nat.double(Word.to_nat(pp, tt)))),
            Nat.double(Word.to_nat(1n+pp, WCon{bb, tt})), Equal.cong(Nat, Nat, z90 => Nat.double(z90),
            Nat.add(Word.to_nat(pp, Word.shl.put(pp, bb, tt)), Nat.mul(put_top(pp, tt, bb), pow2(pp))),
            Nat.add(bit_nat(bb), Nat.double(Word.to_nat(pp, tt))), w_put(pp, tt, bb)), Equal.cong(Nat, Nat,
            z91 => Nat.double(z91), Nat.add(bit_nat(bb), Nat.double(Word.to_nat(pp, tt))), Word.to_nat(1n+pp, WCon{bb,
            tt}), Equal.sym(Nat, Word.to_nat(1n+pp, WCon{bb, tt}), Nat.add(bit_nat(bb), Nat.double(Word.to_nat(pp,
            tt))), w_nat_con(pp, bb, tt))))))

# how many times 2^nn mul.go's product passes

# how many times 2^nn mul.go's product passes
def mul_k(+nn: Nat, mm: Nat, aa: Word(mm), +bb: Word(nn), +acc: Word(nn)) -> Nat:
  match mm:
    case 0n:
      0n
    case 1n+(+mp):
      match aa:
        case WCon{False{}, +at}:
          Nat.add(mul_k(nn, mp, at, Word.shl(nn, bb), acc), Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)))
        case WCon{True{}, +at}:
          Nat.add(mul_k(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb)),
            Nat.add(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), adc_k(nn, acc, bb, False{}, False{})))

# mul.go as Nats: the product, and how many times it passes 2^nn, is acc and
# a times b

# mul.go as Nats: the product, and how many times it passes 2^nn, is acc and
# a times b
law w_mulgo:
  for +nn: Nat
  for mm: Nat
  for aa: Word(mm)
  for +bb: Word(nn)
  for +acc: Word(nn)
  {Nat.add(Word.to_nat(nn, Word.mul.go(nn, mm, aa, bb, acc)), Nat.mul(mul_k(nn, mm, aa, bb, acc), pow2(nn))) ==
    Nat.add(Word.to_nat(nn, acc), Nat.mul(Word.to_nat(mm, aa), Word.to_nat(nn, bb))) : Nat}

# the proof of the law above
def w_mulgo(nn, mm, aa, bb, acc):
  match mm:
    case 0n:
      match aa:
        case WNil{}:
          {==}
    case 1n+(+mp):
      match aa:
        case WCon{False{}, +at}:
          Equal.trans(Nat, Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp, at, Word.shl(nn, bb), acc)),
            Nat.mul(Nat.add(mul_k(nn, mp, at, Word.shl(nn, bb), acc), Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb))),
            pow2(nn))), Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp, at, Word.shl(nn, bb), acc)),
            Nat.add(Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), acc), pow2(nn)), Nat.mul(Nat.mul(Word.to_nat(mp, at),
            shl_top(nn, bb)), pow2(nn)))), Nat.add(Word.to_nat(nn, acc), Nat.mul(Nat.double(Word.to_nat(mp, at)),
            Word.to_nat(nn, bb))), Equal.cong(Nat, Nat, z92 => Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp, at,
            Word.shl(nn, bb), acc)), z92), Nat.mul(Nat.add(mul_k(nn, mp, at, Word.shl(nn, bb), acc),
            Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb))), pow2(nn)), Nat.add(Nat.mul(mul_k(nn, mp, at, Word.shl(nn,
            bb), acc), pow2(nn)), Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn))),
            nat_mul_add_r(mul_k(nn, mp, at, Word.shl(nn, bb), acc), Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)),
            pow2(nn))), Equal.trans(Nat, Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp, at, Word.shl(nn, bb), acc)),
            Nat.add(Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), acc), pow2(nn)), Nat.mul(Nat.mul(Word.to_nat(mp, at),
            shl_top(nn, bb)), pow2(nn)))), Nat.add(Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp, at, Word.shl(nn, bb),
            acc)), Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), acc), pow2(nn))), Nat.mul(Nat.mul(Word.to_nat(mp, at),
            shl_top(nn, bb)), pow2(nn))), Nat.add(Word.to_nat(nn, acc), Nat.mul(Nat.double(Word.to_nat(mp, at)),
            Word.to_nat(nn, bb))), Equal.sym(Nat, Nat.add(Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp, at, Word.shl(nn,
            bb), acc)), Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), acc), pow2(nn))), Nat.mul(Nat.mul(Word.to_nat(mp,
            at), shl_top(nn, bb)), pow2(nn))), Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp, at, Word.shl(nn, bb), acc)),
            Nat.add(Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), acc), pow2(nn)), Nat.mul(Nat.mul(Word.to_nat(mp, at),
            shl_top(nn, bb)), pow2(nn)))), nat_add_assoc(Word.to_nat(nn, Word.mul.go(nn, mp, at, Word.shl(nn, bb),
            acc)), Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), acc), pow2(nn)), Nat.mul(Nat.mul(Word.to_nat(mp, at),
            shl_top(nn, bb)), pow2(nn)))), Equal.trans(Nat, Nat.add(Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp, at,
            Word.shl(nn, bb), acc)), Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), acc), pow2(nn))),
            Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn))), Nat.add(Nat.add(Word.to_nat(nn, acc),
            Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb)))), Nat.mul(Nat.mul(Word.to_nat(mp, at),
            shl_top(nn, bb)), pow2(nn))), Nat.add(Word.to_nat(nn, acc), Nat.mul(Nat.double(Word.to_nat(mp, at)),
            Word.to_nat(nn, bb))), Equal.cong(Nat, Nat, z93 => Nat.add(z93, Nat.mul(Nat.mul(Word.to_nat(mp, at),
            shl_top(nn, bb)), pow2(nn))), Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp, at, Word.shl(nn, bb), acc)),
            Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), acc), pow2(nn))), Nat.add(Word.to_nat(nn, acc),
            Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb)))), w_mulgo(nn, mp, at, Word.shl(nn, bb),
            acc)), Equal.trans(Nat, Nat.add(Nat.add(Word.to_nat(nn, acc), Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn,
            Word.shl(nn, bb)))), Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn))),
            Nat.add(Nat.add(Word.to_nat(nn, acc), Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb)))),
            Nat.mul(Word.to_nat(mp, at), Nat.mul(shl_top(nn, bb), pow2(nn)))), Nat.add(Word.to_nat(nn, acc),
            Nat.mul(Nat.double(Word.to_nat(mp, at)), Word.to_nat(nn, bb))), Equal.cong(Nat, Nat,
            z94 => Nat.add(Nat.add(Word.to_nat(nn, acc), Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn,
            bb)))), z94), Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)), Nat.mul(Word.to_nat(mp,
            at), Nat.mul(shl_top(nn, bb), pow2(nn))), nat_mul_assoc(Word.to_nat(mp, at), shl_top(nn, bb), pow2(nn))),
            Equal.trans(Nat, Nat.add(Nat.add(Word.to_nat(nn, acc), Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn,
            Word.shl(nn, bb)))), Nat.mul(Word.to_nat(mp, at), Nat.mul(shl_top(nn, bb), pow2(nn)))),
            Nat.add(Word.to_nat(nn, acc), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))),
            Nat.mul(Word.to_nat(mp, at), Nat.mul(shl_top(nn, bb), pow2(nn))))), Nat.add(Word.to_nat(nn, acc),
            Nat.mul(Nat.double(Word.to_nat(mp, at)), Word.to_nat(nn, bb))), nat_add_assoc(Word.to_nat(nn, acc),
            Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), Nat.mul(Word.to_nat(mp, at),
            Nat.mul(shl_top(nn, bb), pow2(nn)))), Equal.trans(Nat, Nat.add(Word.to_nat(nn, acc),
            Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), Nat.mul(Word.to_nat(mp, at),
            Nat.mul(shl_top(nn, bb), pow2(nn))))), Nat.add(Word.to_nat(nn, acc), Nat.mul(Word.to_nat(mp, at),
            Nat.add(Word.to_nat(nn, Word.shl(nn, bb)), Nat.mul(shl_top(nn, bb), pow2(nn))))), Nat.add(Word.to_nat(nn,
            acc), Nat.mul(Nat.double(Word.to_nat(mp, at)), Word.to_nat(nn, bb))), Equal.cong(Nat, Nat,
            z95 => Nat.add(Word.to_nat(nn, acc), z95), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn,
            Word.shl(nn, bb))), Nat.mul(Word.to_nat(mp, at), Nat.mul(shl_top(nn, bb), pow2(nn)))),
            Nat.mul(Word.to_nat(mp, at), Nat.add(Word.to_nat(nn, Word.shl(nn, bb)), Nat.mul(shl_top(nn, bb),
            pow2(nn)))), Equal.sym(Nat, Nat.mul(Word.to_nat(mp, at), Nat.add(Word.to_nat(nn, Word.shl(nn, bb)),
            Nat.mul(shl_top(nn, bb), pow2(nn)))), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn,
            bb))), Nat.mul(Word.to_nat(mp, at), Nat.mul(shl_top(nn, bb), pow2(nn)))), nat_mul_add_l(Word.to_nat(mp,
            at), Word.to_nat(nn, Word.shl(nn, bb)), Nat.mul(shl_top(nn, bb), pow2(nn))))), Equal.trans(Nat,
            Nat.add(Word.to_nat(nn, acc), Nat.mul(Word.to_nat(mp, at), Nat.add(Word.to_nat(nn, Word.shl(nn, bb)),
            Nat.mul(shl_top(nn, bb), pow2(nn))))), Nat.add(Word.to_nat(nn, acc), Nat.mul(Word.to_nat(mp, at),
            Nat.double(Word.to_nat(nn, bb)))), Nat.add(Word.to_nat(nn, acc), Nat.mul(Nat.double(Word.to_nat(mp, at)),
            Word.to_nat(nn, bb))), Equal.cong(Nat, Nat, z96 => Nat.add(Word.to_nat(nn, acc), Nat.mul(Word.to_nat(mp,
            at), z96)), Nat.add(Word.to_nat(nn, Word.shl(nn, bb)), Nat.mul(shl_top(nn, bb), pow2(nn))),
            Nat.double(Word.to_nat(nn, bb)), w_shl(nn, bb)), Equal.trans(Nat, Nat.add(Word.to_nat(nn, acc),
            Nat.mul(Word.to_nat(mp, at), Nat.double(Word.to_nat(nn, bb)))), Nat.add(Word.to_nat(nn, acc),
            Nat.double(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, bb)))), Nat.add(Word.to_nat(nn, acc),
            Nat.mul(Nat.double(Word.to_nat(mp, at)), Word.to_nat(nn, bb))), Equal.cong(Nat, Nat,
            z97 => Nat.add(Word.to_nat(nn, acc), z97), Nat.mul(Word.to_nat(mp, at), Nat.double(Word.to_nat(nn, bb))),
            Nat.double(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, bb))), nat_mul_double_r(Word.to_nat(mp, at),
            Word.to_nat(nn, bb))), Equal.cong(Nat, Nat, z98 => Nat.add(Word.to_nat(nn, acc), z98),
            Nat.double(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, bb))), Nat.mul(Nat.double(Word.to_nat(mp, at)),
            Word.to_nat(nn, bb)), Equal.sym(Nat, Nat.mul(Nat.double(Word.to_nat(mp, at)), Word.to_nat(nn, bb)),
            Nat.double(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, bb))), nat_mul_double_l(Word.to_nat(mp, at),
            Word.to_nat(nn, bb))))))))))))
        case WCon{True{}, +at}:
          Equal.trans(Nat, Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb))),
            Nat.mul(Nat.add(mul_k(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb)), Nat.add(Nat.mul(Word.to_nat(mp,
            at), shl_top(nn, bb)), adc_k(nn, acc, bb, False{}, False{}))), pow2(nn))), Nat.add(Word.to_nat(nn,
            Word.mul.go(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb))), Nat.add(Nat.mul(mul_k(nn, mp, at,
            Word.shl(nn, bb), Word.add(nn, acc, bb)), pow2(nn)), Nat.mul(Nat.add(Nat.mul(Word.to_nat(mp, at),
            shl_top(nn, bb)), adc_k(nn, acc, bb, False{}, False{})), pow2(nn)))), Nat.add(Word.to_nat(nn, acc),
            Nat.add(Word.to_nat(nn, bb), Nat.mul(Nat.double(Word.to_nat(mp, at)), Word.to_nat(nn, bb)))),
            Equal.cong(Nat, Nat, z99 => Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp, at, Word.shl(nn, bb), Word.add(nn,
            acc, bb))), z99), Nat.mul(Nat.add(mul_k(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb)),
            Nat.add(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), adc_k(nn, acc, bb, False{}, False{}))), pow2(nn)),
            Nat.add(Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb)), pow2(nn)),
            Nat.mul(Nat.add(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), adc_k(nn, acc, bb, False{}, False{})),
            pow2(nn))), nat_mul_add_r(mul_k(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb)),
            Nat.add(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), adc_k(nn, acc, bb, False{}, False{})), pow2(nn))),
            Equal.trans(Nat, Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb))),
            Nat.add(Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb)), pow2(nn)),
            Nat.mul(Nat.add(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), adc_k(nn, acc, bb, False{}, False{})),
            pow2(nn)))), Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb))),
            Nat.add(Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb)), pow2(nn)),
            Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)), Nat.mul(adc_k(nn, acc, bb,
            False{}, False{}), pow2(nn))))), Nat.add(Word.to_nat(nn, acc), Nat.add(Word.to_nat(nn, bb),
            Nat.mul(Nat.double(Word.to_nat(mp, at)), Word.to_nat(nn, bb)))), Equal.cong(Nat, Nat,
            z100 => Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb))),
            Nat.add(Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb)), pow2(nn)), z100)),
            Nat.mul(Nat.add(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), adc_k(nn, acc, bb, False{}, False{})),
            pow2(nn)), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)), Nat.mul(adc_k(nn, acc,
            bb, False{}, False{}), pow2(nn))), nat_mul_add_r(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), adc_k(nn,
            acc, bb, False{}, False{}), pow2(nn))), Equal.trans(Nat, Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp, at,
            Word.shl(nn, bb), Word.add(nn, acc, bb))), Nat.add(Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), Word.add(nn,
            acc, bb)), pow2(nn)), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)),
            Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn))))), Nat.add(Nat.add(Word.to_nat(nn, Word.mul.go(nn,
            mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb))), Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), Word.add(nn,
            acc, bb)), pow2(nn))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)),
            Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn)))), Nat.add(Word.to_nat(nn, acc),
            Nat.add(Word.to_nat(nn, bb), Nat.mul(Nat.double(Word.to_nat(mp, at)), Word.to_nat(nn, bb)))),
            Equal.sym(Nat, Nat.add(Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc,
            bb))), Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb)), pow2(nn))),
            Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)), Nat.mul(adc_k(nn, acc, bb,
            False{}, False{}), pow2(nn)))), Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp, at, Word.shl(nn, bb),
            Word.add(nn, acc, bb))), Nat.add(Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb)),
            pow2(nn)), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)), Nat.mul(adc_k(nn, acc,
            bb, False{}, False{}), pow2(nn))))), nat_add_assoc(Word.to_nat(nn, Word.mul.go(nn, mp, at, Word.shl(nn,
            bb), Word.add(nn, acc, bb))), Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb)),
            pow2(nn)), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)), Nat.mul(adc_k(nn, acc,
            bb, False{}, False{}), pow2(nn))))), Equal.trans(Nat, Nat.add(Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp,
            at, Word.shl(nn, bb), Word.add(nn, acc, bb))), Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), Word.add(nn,
            acc, bb)), pow2(nn))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)),
            Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn)))), Nat.add(Nat.add(Word.to_nat(nn, Word.add(nn,
            acc, bb)), Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb)))),
            Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)), Nat.mul(adc_k(nn, acc, bb,
            False{}, False{}), pow2(nn)))), Nat.add(Word.to_nat(nn, acc), Nat.add(Word.to_nat(nn, bb),
            Nat.mul(Nat.double(Word.to_nat(mp, at)), Word.to_nat(nn, bb)))), Equal.cong(Nat, Nat, z101 => Nat.add(z101,
            Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)), Nat.mul(adc_k(nn, acc, bb,
            False{}, False{}), pow2(nn)))), Nat.add(Word.to_nat(nn, Word.mul.go(nn, mp, at, Word.shl(nn, bb),
            Word.add(nn, acc, bb))), Nat.mul(mul_k(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb)), pow2(nn))),
            Nat.add(Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn,
            bb)))), w_mulgo(nn, mp, at, Word.shl(nn, bb), Word.add(nn, acc, bb))), Equal.trans(Nat,
            Nat.add(Nat.add(Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn,
            Word.shl(nn, bb)))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)),
            Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn)))), Nat.add(Nat.add(Word.to_nat(nn, Word.add(nn,
            acc, bb)), Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn))), Nat.add(Nat.mul(Word.to_nat(mp, at),
            Word.to_nat(nn, Word.shl(nn, bb))), Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)))),
            Nat.add(Word.to_nat(nn, acc), Nat.add(Word.to_nat(nn, bb), Nat.mul(Nat.double(Word.to_nat(mp, at)),
            Word.to_nat(nn, bb)))), Equal.trans(Nat, Nat.add(Nat.add(Word.to_nat(nn, Word.add(nn, acc, bb)),
            Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb)))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp,
            at), shl_top(nn, bb)), pow2(nn)), Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn)))),
            Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)), Nat.add(Nat.mul(Word.to_nat(mp,
            at), Word.to_nat(nn, Word.shl(nn, bb))), Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn)),
            Word.to_nat(nn, Word.add(nn, acc, bb))))), Nat.add(Nat.add(Word.to_nat(nn, Word.add(nn, acc, bb)),
            Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn))), Nat.add(Nat.mul(Word.to_nat(mp, at),
            Word.to_nat(nn, Word.shl(nn, bb))), Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)))),
            Equal.trans(Nat, Nat.add(Nat.add(Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.mul(Word.to_nat(mp, at),
            Word.to_nat(nn, Word.shl(nn, bb)))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)),
            pow2(nn)), Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn)))),
            Nat.add(Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), Word.to_nat(nn,
            Word.add(nn, acc, bb))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)),
            Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn)))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at),
            shl_top(nn, bb)), pow2(nn)), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))),
            Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn)), Word.to_nat(nn, Word.add(nn, acc, bb))))),
            Equal.cong(Nat, Nat, z102 => Nat.add(z102, Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)),
            pow2(nn)), Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn)))), Nat.add(Word.to_nat(nn, Word.add(nn,
            acc, bb)), Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb)))),
            Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), Word.to_nat(nn, Word.add(nn, acc,
            bb))), nat_add_comm(Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn,
            Word.shl(nn, bb))))), Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn,
            Word.shl(nn, bb))), Word.to_nat(nn, Word.add(nn, acc, bb))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at),
            shl_top(nn, bb)), pow2(nn)), Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn)))),
            Nat.add(Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), Word.to_nat(nn,
            Word.add(nn, acc, bb))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)),
            Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn)))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at),
            shl_top(nn, bb)), pow2(nn)), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))),
            Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn)), Word.to_nat(nn, Word.add(nn, acc, bb))))),
            Equal.cong(Nat, Nat, z103 => Nat.add(Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn,
            bb))), Word.to_nat(nn, Word.add(nn, acc, bb))), z103), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at),
            shl_top(nn, bb)), pow2(nn)), Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn))),
            Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)), Nat.mul(adc_k(nn, acc, bb,
            False{}, False{}), pow2(nn))), {==}), Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(Word.to_nat(mp, at),
            Word.to_nat(nn, Word.shl(nn, bb))), Word.to_nat(nn, Word.add(nn, acc, bb))),
            Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)), Nat.mul(adc_k(nn, acc, bb,
            False{}, False{}), pow2(nn)))), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))),
            Nat.add(Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn,
            bb)), pow2(nn)), Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn))))),
            Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)), Nat.add(Nat.mul(Word.to_nat(mp,
            at), Word.to_nat(nn, Word.shl(nn, bb))), Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn)),
            Word.to_nat(nn, Word.add(nn, acc, bb))))), nat_add_assoc(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn,
            Word.shl(nn, bb))), Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at),
            shl_top(nn, bb)), pow2(nn)), Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn)))), Equal.trans(Nat,
            Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), Nat.add(Word.to_nat(nn,
            Word.add(nn, acc, bb)), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)),
            Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn))))), Nat.add(Nat.mul(Word.to_nat(mp, at),
            Word.to_nat(nn, Word.shl(nn, bb))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)),
            pow2(nn)), Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn)), Word.to_nat(nn, Word.add(nn,
            acc, bb))))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)),
            Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), Nat.add(Nat.mul(adc_k(nn, acc, bb,
            False{}, False{}), pow2(nn)), Word.to_nat(nn, Word.add(nn, acc, bb))))), Equal.cong(Nat, Nat,
            z105 => Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), z105),
            Nat.add(Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn,
            bb)), pow2(nn)), Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn)))),
            Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)), Nat.add(Nat.mul(adc_k(nn, acc,
            bb, False{}, False{}), pow2(nn)), Word.to_nat(nn, Word.add(nn, acc, bb)))), Equal.trans(Nat,
            Nat.add(Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn,
            bb)), pow2(nn)), Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn)))),
            Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)), Nat.add(Word.to_nat(nn,
            Word.add(nn, acc, bb)), Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn)))),
            Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)), Nat.add(Nat.mul(adc_k(nn, acc,
            bb, False{}, False{}), pow2(nn)), Word.to_nat(nn, Word.add(nn, acc, bb)))), nat_add_lcomm(Word.to_nat(nn,
            Word.add(nn, acc, bb)), Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)), Nat.mul(adc_k(nn,
            acc, bb, False{}, False{}), pow2(nn))), Equal.cong(Nat, Nat,
            z104 => Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)), z104),
            Nat.add(Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn))),
            Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn)), Word.to_nat(nn, Word.add(nn, acc, bb))),
            nat_add_comm(Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.mul(adc_k(nn, acc, bb, False{}, False{}),
            pow2(nn)))))), nat_add_lcomm(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))),
            Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)), Nat.add(Nat.mul(adc_k(nn, acc, bb,
            False{}, False{}), pow2(nn)), Word.to_nat(nn, Word.add(nn, acc, bb)))))))), Equal.sym(Nat,
            Nat.add(Nat.add(Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.mul(adc_k(nn, acc, bb, False{}, False{}),
            pow2(nn))), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))),
            Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp,
            at), shl_top(nn, bb)), pow2(nn)), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))),
            Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn)), Word.to_nat(nn, Word.add(nn, acc, bb))))),
            Equal.trans(Nat, Nat.add(Nat.add(Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.mul(adc_k(nn, acc, bb,
            False{}, False{}), pow2(nn))), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))),
            Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)))), Nat.add(Nat.add(Nat.mul(adc_k(nn, acc,
            bb, False{}, False{}), pow2(nn)), Word.to_nat(nn, Word.add(nn, acc, bb))), Nat.add(Nat.mul(Word.to_nat(mp,
            at), Word.to_nat(nn, Word.shl(nn, bb))), Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)),
            pow2(nn)))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)),
            Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), Nat.add(Nat.mul(adc_k(nn, acc, bb,
            False{}, False{}), pow2(nn)), Word.to_nat(nn, Word.add(nn, acc, bb))))), Equal.cong(Nat, Nat,
            z106 => Nat.add(z106, Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))),
            Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)))), Nat.add(Word.to_nat(nn, Word.add(nn,
            acc, bb)), Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn))), Nat.add(Nat.mul(adc_k(nn, acc, bb,
            False{}, False{}), pow2(nn)), Word.to_nat(nn, Word.add(nn, acc, bb))), nat_add_comm(Word.to_nat(nn,
            Word.add(nn, acc, bb)), Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn)))), Equal.trans(Nat,
            Nat.add(Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn)), Word.to_nat(nn, Word.add(nn, acc,
            bb))), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))),
            Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)))), Nat.add(Nat.add(Nat.mul(adc_k(nn, acc,
            bb, False{}, False{}), pow2(nn)), Word.to_nat(nn, Word.add(nn, acc, bb))),
            Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)), Nat.mul(Word.to_nat(mp, at),
            Word.to_nat(nn, Word.shl(nn, bb))))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)),
            pow2(nn)), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))),
            Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn)), Word.to_nat(nn, Word.add(nn, acc, bb))))),
            Equal.cong(Nat, Nat, z107 => Nat.add(Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn)),
            Word.to_nat(nn, Word.add(nn, acc, bb))), z107), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn,
            Word.shl(nn, bb))), Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn))),
            Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)), Nat.mul(Word.to_nat(mp, at),
            Word.to_nat(nn, Word.shl(nn, bb)))), nat_add_comm(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn,
            bb))), Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)))), Equal.trans(Nat,
            Nat.add(Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn)), Word.to_nat(nn, Word.add(nn, acc,
            bb))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)), Nat.mul(Word.to_nat(mp,
            at), Word.to_nat(nn, Word.shl(nn, bb))))), Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn)),
            Nat.add(Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn,
            bb)), pow2(nn)), Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb)))))),
            Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)), Nat.add(Nat.mul(Word.to_nat(mp,
            at), Word.to_nat(nn, Word.shl(nn, bb))), Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn)),
            Word.to_nat(nn, Word.add(nn, acc, bb))))), nat_add_assoc(Nat.mul(adc_k(nn, acc, bb, False{}, False{}),
            pow2(nn)), Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn,
            bb)), pow2(nn)), Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))))), Equal.trans(Nat,
            Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn)), Nat.add(Word.to_nat(nn, Word.add(nn, acc,
            bb)), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)), Nat.mul(Word.to_nat(mp,
            at), Word.to_nat(nn, Word.shl(nn, bb)))))), Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}),
            pow2(nn)), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)),
            Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), Word.to_nat(nn, Word.add(nn, acc,
            bb))))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)),
            Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), Nat.add(Nat.mul(adc_k(nn, acc, bb,
            False{}, False{}), pow2(nn)), Word.to_nat(nn, Word.add(nn, acc, bb))))), Equal.cong(Nat, Nat,
            z109 => Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn)), z109), Nat.add(Word.to_nat(nn,
            Word.add(nn, acc, bb)), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)),
            Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp,
            at), shl_top(nn, bb)), pow2(nn)), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))),
            Word.to_nat(nn, Word.add(nn, acc, bb)))), Equal.trans(Nat, Nat.add(Word.to_nat(nn, Word.add(nn, acc, bb)),
            Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)), Nat.mul(Word.to_nat(mp, at),
            Word.to_nat(nn, Word.shl(nn, bb))))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)),
            pow2(nn)), Nat.add(Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn,
            Word.shl(nn, bb))))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)),
            Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), Word.to_nat(nn, Word.add(nn, acc,
            bb)))), nat_add_lcomm(Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.mul(Nat.mul(Word.to_nat(mp, at),
            shl_top(nn, bb)), pow2(nn)), Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb)))),
            Equal.cong(Nat, Nat, z108 => Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)),
            z108), Nat.add(Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn,
            Word.shl(nn, bb)))), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))),
            Word.to_nat(nn, Word.add(nn, acc, bb))), nat_add_comm(Word.to_nat(nn, Word.add(nn, acc, bb)),
            Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))))))), Equal.trans(Nat,
            Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn)), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp,
            at), shl_top(nn, bb)), pow2(nn)), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))),
            Word.to_nat(nn, Word.add(nn, acc, bb))))), Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)),
            pow2(nn)), Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn)), Nat.add(Nat.mul(Word.to_nat(mp,
            at), Word.to_nat(nn, Word.shl(nn, bb))), Word.to_nat(nn, Word.add(nn, acc, bb))))),
            Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)), Nat.add(Nat.mul(Word.to_nat(mp,
            at), Word.to_nat(nn, Word.shl(nn, bb))), Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn)),
            Word.to_nat(nn, Word.add(nn, acc, bb))))), nat_add_lcomm(Nat.mul(adc_k(nn, acc, bb, False{}, False{}),
            pow2(nn)), Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)),
            Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), Word.to_nat(nn, Word.add(nn, acc,
            bb)))), Equal.cong(Nat, Nat, z110 => Nat.add(Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)),
            pow2(nn)), z110), Nat.add(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn)),
            Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), Word.to_nat(nn, Word.add(nn, acc,
            bb)))), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), Nat.add(Nat.mul(adc_k(nn,
            acc, bb, False{}, False{}), pow2(nn)), Word.to_nat(nn, Word.add(nn, acc, bb)))),
            nat_add_lcomm(Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn)), Nat.mul(Word.to_nat(mp, at),
            Word.to_nat(nn, Word.shl(nn, bb))), Word.to_nat(nn, Word.add(nn, acc, bb))))))))))), Equal.trans(Nat,
            Nat.add(Nat.add(Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.mul(adc_k(nn, acc, bb, False{}, False{}),
            pow2(nn))), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))),
            Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)))), Nat.add(Nat.add(Word.to_nat(nn, acc),
            Nat.add(Word.to_nat(nn, bb), 0n)), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))),
            Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)))), Nat.add(Word.to_nat(nn, acc),
            Nat.add(Word.to_nat(nn, bb), Nat.mul(Nat.double(Word.to_nat(mp, at)), Word.to_nat(nn, bb)))),
            Equal.cong(Nat, Nat, z111 => Nat.add(z111, Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn,
            Word.shl(nn, bb))), Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)))),
            Nat.add(Word.to_nat(nn, Word.add(nn, acc, bb)), Nat.mul(adc_k(nn, acc, bb, False{}, False{}), pow2(nn))),
            Nat.add(Word.to_nat(nn, acc), Nat.add(Word.to_nat(nn, bb), 0n)), w_adc(nn, acc, bb, False{}, False{})),
            Equal.trans(Nat, Nat.add(Nat.add(Word.to_nat(nn, acc), Nat.add(Word.to_nat(nn, bb), 0n)),
            Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), Nat.mul(Nat.mul(Word.to_nat(mp,
            at), shl_top(nn, bb)), pow2(nn)))), Nat.add(Nat.add(Word.to_nat(nn, acc), Word.to_nat(nn, bb)),
            Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), Nat.mul(Nat.mul(Word.to_nat(mp,
            at), shl_top(nn, bb)), pow2(nn)))), Nat.add(Word.to_nat(nn, acc), Nat.add(Word.to_nat(nn, bb),
            Nat.mul(Nat.double(Word.to_nat(mp, at)), Word.to_nat(nn, bb)))), Equal.cong(Nat, Nat,
            z112 => Nat.add(Nat.add(Word.to_nat(nn, acc), z112), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn,
            Word.shl(nn, bb))), Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)))),
            Nat.add(Word.to_nat(nn, bb), 0n), Word.to_nat(nn, bb), nat_add_zero(Word.to_nat(nn, bb))), Equal.trans(Nat,
            Nat.add(Nat.add(Word.to_nat(nn, acc), Word.to_nat(nn, bb)), Nat.add(Nat.mul(Word.to_nat(mp, at),
            Word.to_nat(nn, Word.shl(nn, bb))), Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)))),
            Nat.add(Nat.add(Word.to_nat(nn, acc), Word.to_nat(nn, bb)), Nat.add(Nat.mul(Word.to_nat(mp, at),
            Word.to_nat(nn, Word.shl(nn, bb))), Nat.mul(Word.to_nat(mp, at), Nat.mul(shl_top(nn, bb), pow2(nn))))),
            Nat.add(Word.to_nat(nn, acc), Nat.add(Word.to_nat(nn, bb), Nat.mul(Nat.double(Word.to_nat(mp, at)),
            Word.to_nat(nn, bb)))), Equal.cong(Nat, Nat, z113 => Nat.add(Nat.add(Word.to_nat(nn, acc), Word.to_nat(nn,
            bb)), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), z113)),
            Nat.mul(Nat.mul(Word.to_nat(mp, at), shl_top(nn, bb)), pow2(nn)), Nat.mul(Word.to_nat(mp, at),
            Nat.mul(shl_top(nn, bb), pow2(nn))), nat_mul_assoc(Word.to_nat(mp, at), shl_top(nn, bb), pow2(nn))),
            Equal.trans(Nat, Nat.add(Nat.add(Word.to_nat(nn, acc), Word.to_nat(nn, bb)),
            Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))), Nat.mul(Word.to_nat(mp, at),
            Nat.mul(shl_top(nn, bb), pow2(nn))))), Nat.add(Nat.add(Word.to_nat(nn, acc), Word.to_nat(nn, bb)),
            Nat.mul(Word.to_nat(mp, at), Nat.add(Word.to_nat(nn, Word.shl(nn, bb)), Nat.mul(shl_top(nn, bb),
            pow2(nn))))), Nat.add(Word.to_nat(nn, acc), Nat.add(Word.to_nat(nn, bb), Nat.mul(Nat.double(Word.to_nat(mp,
            at)), Word.to_nat(nn, bb)))), Equal.cong(Nat, Nat, z114 => Nat.add(Nat.add(Word.to_nat(nn, acc),
            Word.to_nat(nn, bb)), z114), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))),
            Nat.mul(Word.to_nat(mp, at), Nat.mul(shl_top(nn, bb), pow2(nn)))), Nat.mul(Word.to_nat(mp, at),
            Nat.add(Word.to_nat(nn, Word.shl(nn, bb)), Nat.mul(shl_top(nn, bb), pow2(nn)))), Equal.sym(Nat,
            Nat.mul(Word.to_nat(mp, at), Nat.add(Word.to_nat(nn, Word.shl(nn, bb)), Nat.mul(shl_top(nn, bb),
            pow2(nn)))), Nat.add(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, Word.shl(nn, bb))),
            Nat.mul(Word.to_nat(mp, at), Nat.mul(shl_top(nn, bb), pow2(nn)))), nat_mul_add_l(Word.to_nat(mp, at),
            Word.to_nat(nn, Word.shl(nn, bb)), Nat.mul(shl_top(nn, bb), pow2(nn))))), Equal.trans(Nat,
            Nat.add(Nat.add(Word.to_nat(nn, acc), Word.to_nat(nn, bb)), Nat.mul(Word.to_nat(mp, at),
            Nat.add(Word.to_nat(nn, Word.shl(nn, bb)), Nat.mul(shl_top(nn, bb), pow2(nn))))),
            Nat.add(Nat.add(Word.to_nat(nn, acc), Word.to_nat(nn, bb)), Nat.mul(Word.to_nat(mp, at),
            Nat.double(Word.to_nat(nn, bb)))), Nat.add(Word.to_nat(nn, acc), Nat.add(Word.to_nat(nn, bb),
            Nat.mul(Nat.double(Word.to_nat(mp, at)), Word.to_nat(nn, bb)))), Equal.cong(Nat, Nat,
            z115 => Nat.add(Nat.add(Word.to_nat(nn, acc), Word.to_nat(nn, bb)), Nat.mul(Word.to_nat(mp, at), z115)),
            Nat.add(Word.to_nat(nn, Word.shl(nn, bb)), Nat.mul(shl_top(nn, bb), pow2(nn))), Nat.double(Word.to_nat(nn,
            bb)), w_shl(nn, bb)), Equal.trans(Nat, Nat.add(Nat.add(Word.to_nat(nn, acc), Word.to_nat(nn, bb)),
            Nat.mul(Word.to_nat(mp, at), Nat.double(Word.to_nat(nn, bb)))), Nat.add(Nat.add(Word.to_nat(nn, acc),
            Word.to_nat(nn, bb)), Nat.double(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, bb)))),
            Nat.add(Word.to_nat(nn, acc), Nat.add(Word.to_nat(nn, bb), Nat.mul(Nat.double(Word.to_nat(mp, at)),
            Word.to_nat(nn, bb)))), Equal.cong(Nat, Nat, z116 => Nat.add(Nat.add(Word.to_nat(nn, acc), Word.to_nat(nn,
            bb)), z116), Nat.mul(Word.to_nat(mp, at), Nat.double(Word.to_nat(nn, bb))),
            Nat.double(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, bb))), nat_mul_double_r(Word.to_nat(mp, at),
            Word.to_nat(nn, bb))), Equal.trans(Nat, Nat.add(Nat.add(Word.to_nat(nn, acc), Word.to_nat(nn, bb)),
            Nat.double(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, bb)))), Nat.add(Nat.add(Word.to_nat(nn, acc),
            Word.to_nat(nn, bb)), Nat.mul(Nat.double(Word.to_nat(mp, at)), Word.to_nat(nn, bb))),
            Nat.add(Word.to_nat(nn, acc), Nat.add(Word.to_nat(nn, bb), Nat.mul(Nat.double(Word.to_nat(mp, at)),
            Word.to_nat(nn, bb)))), Equal.cong(Nat, Nat, z117 => Nat.add(Nat.add(Word.to_nat(nn, acc), Word.to_nat(nn,
            bb)), z117), Nat.double(Nat.mul(Word.to_nat(mp, at), Word.to_nat(nn, bb))),
            Nat.mul(Nat.double(Word.to_nat(mp, at)), Word.to_nat(nn, bb)), Equal.sym(Nat,
            Nat.mul(Nat.double(Word.to_nat(mp, at)), Word.to_nat(nn, bb)), Nat.double(Nat.mul(Word.to_nat(mp, at),
            Word.to_nat(nn, bb))), nat_mul_double_l(Word.to_nat(mp, at), Word.to_nat(nn, bb)))),
            nat_add_assoc(Word.to_nat(nn, acc), Word.to_nat(nn, bb), Nat.mul(Nat.double(Word.to_nat(mp, at)),
            Word.to_nat(nn, bb)))))))))))))))

# w_mulgo, with 2^nn named through uu

# w_mulgo, with 2^nn named through uu
law w_mulgo_u:
  for +nn: Nat
  for uu: Unit
  for mm: Nat
  for aa: Word(mm)
  for +bb: Word(nn)
  for +acc: Word(nn)
  {Nat.add(Word.to_nat(nn, Word.mul.go(nn, mm, aa, bb, acc)), Nat.mul(mul_k(nn, mm, aa, bb, acc), pow2u(nn, uu))) ==
    Nat.add(Word.to_nat(nn, acc), Nat.mul(Word.to_nat(mm, aa), Word.to_nat(nn, bb))) : Nat}

# the proof of the law above
def w_mulgo_u(nn, uu, mm, aa, bb, acc):
  match uu:
    case Unit{}:
      w_mulgo(nn, mm, aa, bb, acc)

# a U32's word

# a U32's word
def u32w(uu: U32) -> Word(32n):
  match uu:
    case U32{ww}:
      ww

# how many times 2^32 a U32 times ten passes

# how many times 2^32 a U32 times ten passes
def umk(aa: U32) -> Nat:
  match aa:
    case U32{xw}:
      mul_k(32n, 32n, xw, u32w(10), Word.zero(32n))

# a U32 times ten, and how many times it passes 2^32, is the Nat times ten

# a U32 times ten, and how many times it passes 2^32, is the Nat times ten
law u_mul10:
  for +uu: Unit
  for aa: U32
  {Nat.add(U32.to_nat(U32.mul(aa, 10)), Nat.mul(umk(aa), pow2u(32n, uu))) == Nat.mul(U32.to_nat(aa), 10n) : Nat}

# the proof of the law above
def u_mul10(uu, aa):
  match aa:
    case U32{xw}:
      w_mulgo_u(32n, uu, 32n, xw, u32w(10), Word.zero(32n))

# JSON-TREE-6: 2^32 is large, a U32 is below it

# 2^nn is one more than something

# 2^nn is one more than something
law p2_pos:
  for +nn: Nat
  {pow2(nn) == 1n+Nat.sub(pow2(nn), 1n) : Nat}

# the proof of the law above
def p2_pos(nn):
  match nn:
    case 0n:
      {==}
    case 1n+(+pp):
      ee = Equal.sym(Nat, pow2(pp), 1n+Nat.sub(pow2(pp), 1n), p2_pos(pp))
      %ee : {Nat.double(_) == 1n+Nat.sub(Nat.double(_), 1n) : Nat}
      {==}

# six doublings

# six doublings
def dbl6(nn: Nat) -> Nat:
  Nat.double(Nat.double(Nat.double(Nat.double(Nat.double(Nat.double(nn))))))

# what 2^(6 + mm) is past 64, once uu is known

# what 2^(6 + mm) is past 64, once uu is known
def pz6(mm: Nat, uu: Unit) -> Nat:
  match uu:
    case Unit{}:
      dbl6(Nat.sub(pow2(mm), 1n))

# 2^(6 + mm) is 64 and more

# 2^(6 + mm) is 64 and more
law pw_big:
  for +mm: Nat
  for uu: Unit
  {pow2u(6n+mm, uu) == Nat.add(64n, pz6(mm, uu)) : Nat}

# the proof of the law above
def pw_big(mm, uu):
  match uu:
    case Unit{}:
      Equal.cong(Nat, Nat, xx => dbl6(xx), pow2(mm), 1n+Nat.sub(pow2(mm), 1n), p2_pos(mm))

# below 64 is below 2^32

# a U32 is below 2^32
law u_bound:
  for +uu: Unit
  for aa: U32
  {Nat.is_lt(U32.to_nat(aa), pow2u(32n, uu)) == True{} : Bool}

# the proof of the law above
def u_bound(uu, aa):
  match aa:
    case U32{ww}:
      w_bound_u(32n, uu, ww)

# s + k*t is e + t, both below t: s is e

# s + k*t is e + t, both below t: s is e
law nat_mod_one:
  for kk: Nat
  for +ss: Nat
  for +ee: Nat
  for +tt: Nat
  for h: {Nat.add(ss, Nat.mul(kk, tt)) == Nat.add(ee, tt) : Nat}
  for hs: {Nat.is_lt(ss, tt) == True{} : Bool}
  for he: {Nat.is_lt(ee, tt) == True{} : Bool}
  {ss == ee : Nat}

# the proof of the law above
def nat_mod_one(kk, ss, ee, tt, h, hs, he):
  match kk:
    case 0n:
      Empty.absurd({ss == ee : Nat}, true_false(Equal.trans(Bool, True{}, Nat.is_lt(ss, tt), False{}, Equal.sym(Bool,
        Nat.is_lt(ss, tt), True{}, hs), Equal.trans(Bool, Nat.is_lt(ss, tt), Nat.is_lt(Nat.add(ss, 0n), tt), False{},
        Equal.cong(Nat, Bool, z118 => Nat.is_lt(z118, tt), ss, Nat.add(ss, 0n), Equal.sym(Nat, Nat.add(ss, 0n), ss,
        nat_add_zero(ss))), Equal.trans(Bool, Nat.is_lt(Nat.add(ss, 0n), tt), Nat.is_lt(Nat.add(ee, tt), tt), False{},
        Equal.cong(Nat, Bool, z119 => Nat.is_lt(z119, tt), Nat.add(ss, 0n), Nat.add(ee, tt), h), Equal.trans(Bool,
        Nat.is_lt(Nat.add(ee, tt), tt), Nat.is_lt(Nat.add(tt, ee), tt), False{}, Equal.cong(Nat, Bool,
        z120 => Nat.is_lt(z120, tt), Nat.add(ee, tt), Nat.add(tt, ee), nat_add_comm(ee, tt)), nat_nlt_add(tt, ee)))))))
    case 1n+(+kp):
      nat_mod_small(kp, ss, ee, tt, nat_add_cancel(tt, Nat.add(ss, Nat.mul(kp, tt)), ee, Equal.trans(Nat, Nat.add(tt,
        Nat.add(ss, Nat.mul(kp, tt))), Nat.add(ss, Nat.add(tt, Nat.mul(kp, tt))), Nat.add(tt, ee), Equal.sym(Nat,
        Nat.add(ss, Nat.add(tt, Nat.mul(kp, tt))), Nat.add(tt, Nat.add(ss, Nat.mul(kp, tt))), nat_add_lcomm(ss, tt,
        Nat.mul(kp, tt))), Equal.trans(Nat, Nat.add(ss, Nat.add(tt, Nat.mul(kp, tt))), Nat.add(ee, tt), Nat.add(tt,
        ee), h, nat_add_comm(ee, tt)))), he)

# a U32 difference that does not pass below 0 is the Nat difference

# a U32 difference that does not pass below 0 is the Nat difference
law u_sub_ge:
  for +uu: Unit
  for +aa: U32
  for +bb: U32
  for +h: {Nat.is_lt(U32.to_nat(aa), U32.to_nat(bb)) == False{} : Bool}
  {Nat.add(U32.to_nat(U32.sub(aa, bb)), U32.to_nat(bb)) == U32.to_nat(aa) : Nat}

# the proof of the law above
def u_sub_ge(uu, aa, bb, h):
  Equal.trans(Nat, Nat.add(U32.to_nat(U32.sub(aa, bb)), U32.to_nat(bb)), Nat.add(Nat.sub(U32.to_nat(aa),
    U32.to_nat(bb)), U32.to_nat(bb)), U32.to_nat(aa), Equal.cong(Nat, Nat, z126 => Nat.add(z126, U32.to_nat(bb)),
    U32.to_nat(U32.sub(aa, bb)), Nat.sub(U32.to_nat(aa), U32.to_nat(bb)), nat_mod_one(usub_k(aa, bb),
    U32.to_nat(U32.sub(aa, bb)), Nat.sub(U32.to_nat(aa), U32.to_nat(bb)), pow2u(32n, uu),
    nat_add_cancel(U32.to_nat(bb), Nat.add(U32.to_nat(U32.sub(aa, bb)), Nat.mul(usub_k(aa, bb), pow2u(32n, uu))),
    Nat.add(Nat.sub(U32.to_nat(aa), U32.to_nat(bb)), pow2u(32n, uu)), Equal.trans(Nat, Nat.add(U32.to_nat(bb),
    Nat.add(U32.to_nat(U32.sub(aa, bb)), Nat.mul(usub_k(aa, bb), pow2u(32n, uu)))), Nat.add(U32.to_nat(U32.sub(aa,
    bb)), Nat.add(Nat.mul(usub_k(aa, bb), pow2u(32n, uu)), U32.to_nat(bb))), Nat.add(U32.to_nat(bb),
    Nat.add(Nat.sub(U32.to_nat(aa), U32.to_nat(bb)), pow2u(32n, uu))), Equal.trans(Nat, Nat.add(U32.to_nat(bb),
    Nat.add(U32.to_nat(U32.sub(aa, bb)), Nat.mul(usub_k(aa, bb), pow2u(32n, uu)))), Nat.add(Nat.mul(usub_k(aa, bb),
    pow2u(32n, uu)), Nat.add(U32.to_nat(U32.sub(aa, bb)), U32.to_nat(bb))), Nat.add(U32.to_nat(U32.sub(aa, bb)),
    Nat.add(Nat.mul(usub_k(aa, bb), pow2u(32n, uu)), U32.to_nat(bb))), Equal.trans(Nat, Nat.add(U32.to_nat(bb),
    Nat.add(U32.to_nat(U32.sub(aa, bb)), Nat.mul(usub_k(aa, bb), pow2u(32n, uu)))), Nat.add(U32.to_nat(bb),
    Nat.add(Nat.mul(usub_k(aa, bb), pow2u(32n, uu)), U32.to_nat(U32.sub(aa, bb)))), Nat.add(Nat.mul(usub_k(aa, bb),
    pow2u(32n, uu)), Nat.add(U32.to_nat(U32.sub(aa, bb)), U32.to_nat(bb))), Equal.cong(Nat, Nat,
    z121 => Nat.add(U32.to_nat(bb), z121), Nat.add(U32.to_nat(U32.sub(aa, bb)), Nat.mul(usub_k(aa, bb), pow2u(32n,
    uu))), Nat.add(Nat.mul(usub_k(aa, bb), pow2u(32n, uu)), U32.to_nat(U32.sub(aa, bb))),
    nat_add_comm(U32.to_nat(U32.sub(aa, bb)), Nat.mul(usub_k(aa, bb), pow2u(32n, uu)))), Equal.trans(Nat,
    Nat.add(U32.to_nat(bb), Nat.add(Nat.mul(usub_k(aa, bb), pow2u(32n, uu)), U32.to_nat(U32.sub(aa, bb)))),
    Nat.add(Nat.mul(usub_k(aa, bb), pow2u(32n, uu)), Nat.add(U32.to_nat(bb), U32.to_nat(U32.sub(aa, bb)))),
    Nat.add(Nat.mul(usub_k(aa, bb), pow2u(32n, uu)), Nat.add(U32.to_nat(U32.sub(aa, bb)), U32.to_nat(bb))),
    nat_add_lcomm(U32.to_nat(bb), Nat.mul(usub_k(aa, bb), pow2u(32n, uu)), U32.to_nat(U32.sub(aa, bb))),
    Equal.cong(Nat, Nat, z122 => Nat.add(Nat.mul(usub_k(aa, bb), pow2u(32n, uu)), z122), Nat.add(U32.to_nat(bb),
    U32.to_nat(U32.sub(aa, bb))), Nat.add(U32.to_nat(U32.sub(aa, bb)), U32.to_nat(bb)), nat_add_comm(U32.to_nat(bb),
    U32.to_nat(U32.sub(aa, bb)))))), Equal.sym(Nat, Nat.add(U32.to_nat(U32.sub(aa, bb)), Nat.add(Nat.mul(usub_k(aa,
    bb), pow2u(32n, uu)), U32.to_nat(bb))), Nat.add(Nat.mul(usub_k(aa, bb), pow2u(32n, uu)),
    Nat.add(U32.to_nat(U32.sub(aa, bb)), U32.to_nat(bb))), Equal.trans(Nat, Nat.add(U32.to_nat(U32.sub(aa, bb)),
    Nat.add(Nat.mul(usub_k(aa, bb), pow2u(32n, uu)), U32.to_nat(bb))), Nat.add(U32.to_nat(U32.sub(aa, bb)),
    Nat.add(Nat.mul(usub_k(aa, bb), pow2u(32n, uu)), U32.to_nat(bb))), Nat.add(Nat.mul(usub_k(aa, bb), pow2u(32n, uu)),
    Nat.add(U32.to_nat(U32.sub(aa, bb)), U32.to_nat(bb))), Equal.cong(Nat, Nat, z123 => Nat.add(U32.to_nat(U32.sub(aa,
    bb)), z123), Nat.add(Nat.mul(usub_k(aa, bb), pow2u(32n, uu)), U32.to_nat(bb)), Nat.add(Nat.mul(usub_k(aa, bb),
    pow2u(32n, uu)), U32.to_nat(bb)), {==}), nat_add_lcomm(U32.to_nat(U32.sub(aa, bb)), Nat.mul(usub_k(aa, bb),
    pow2u(32n, uu)), U32.to_nat(bb))))), Equal.trans(Nat, Nat.add(U32.to_nat(U32.sub(aa, bb)),
    Nat.add(Nat.mul(usub_k(aa, bb), pow2u(32n, uu)), U32.to_nat(bb))), Nat.add(U32.to_nat(aa), pow2u(32n, uu)),
    Nat.add(U32.to_nat(bb), Nat.add(Nat.sub(U32.to_nat(aa), U32.to_nat(bb)), pow2u(32n, uu))), u_sub(uu, aa, bb),
    Equal.trans(Nat, Nat.add(U32.to_nat(aa), pow2u(32n, uu)), Nat.add(Nat.add(U32.to_nat(bb), Nat.sub(U32.to_nat(aa),
    U32.to_nat(bb))), pow2u(32n, uu)), Nat.add(U32.to_nat(bb), Nat.add(Nat.sub(U32.to_nat(aa), U32.to_nat(bb)),
    pow2u(32n, uu))), Equal.cong(Nat, Nat, z124 => Nat.add(z124, pow2u(32n, uu)), U32.to_nat(aa),
    Nat.add(U32.to_nat(bb), Nat.sub(U32.to_nat(aa), U32.to_nat(bb))), Equal.sym(Nat, Nat.add(U32.to_nat(bb),
    Nat.sub(U32.to_nat(aa), U32.to_nat(bb))), U32.to_nat(aa), nat_ge_ex(U32.to_nat(aa), U32.to_nat(bb), h))),
    nat_add_assoc(U32.to_nat(bb), Nat.sub(U32.to_nat(aa), U32.to_nat(bb)), pow2u(32n, uu)))))), u_bound(uu, U32.sub(aa,
    bb)), nat_lt_add_l(U32.to_nat(bb), Nat.sub(U32.to_nat(aa), U32.to_nat(bb)), pow2u(32n, uu), Equal.trans(Bool,
    Nat.is_lt(Nat.add(U32.to_nat(bb), Nat.sub(U32.to_nat(aa), U32.to_nat(bb))), pow2u(32n, uu)),
    Nat.is_lt(U32.to_nat(aa), pow2u(32n, uu)), True{}, Equal.cong(Nat, Bool, z125 => Nat.is_lt(z125, pow2u(32n, uu)),
    Nat.add(U32.to_nat(bb), Nat.sub(U32.to_nat(aa), U32.to_nat(bb))), U32.to_nat(aa), nat_ge_ex(U32.to_nat(aa),
    U32.to_nat(bb), h)), u_bound(uu, aa))))), Equal.trans(Nat, Nat.add(Nat.sub(U32.to_nat(aa), U32.to_nat(bb)),
    U32.to_nat(bb)), Nat.add(U32.to_nat(bb), Nat.sub(U32.to_nat(aa), U32.to_nat(bb))), U32.to_nat(aa),
    nat_add_comm(Nat.sub(U32.to_nat(aa), U32.to_nat(bb)), U32.to_nat(bb)), nat_ge_ex(U32.to_nat(aa), U32.to_nat(bb),
    h)))

# s + (k*t + y) is x + t and y is past x: k is 0

# a Cmp at least EQ is not LT
law cmp_ge_nlt:
  for cc: Cmp
  for h: {Cmp.is_ge(cc) == True{} : Bool}
  {Cmp.is_lt(cc) == False{} : Bool}

# the proof of the law above
def cmp_ge_nlt(cc, h):
  match cc:
    case LT{}:
      Empty.absurd({True{} == False{} : Bool}, false_true(h))
    case EQ{}:
      {==}
    case GT{}:
      {==}

# a Cmp below EQ is LT

# a Cmp below EQ is LT
law cmp_nge_lt:
  for cc: Cmp
  for h: {Cmp.is_ge(cc) == False{} : Bool}
  {Cmp.is_lt(cc) == True{} : Bool}

# the proof of the law above
def cmp_nge_lt(cc, h):
  match cc:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({False{} == True{} : Bool}, true_false(h))
    case GT{}:
      Empty.absurd({False{} == True{} : Bool}, true_false(h))

# the bit shl.out shifts out

# the bit shl.out shifts out
def so_hi(nn: Nat, pr: Bool & Word(nn)) -> Bool:
  (hi, _ww) = pr
  hi

# the word shl.out leaves

# the word shl.out leaves
def so_w(nn: Nat, pr: Bool & Word(nn)) -> Word(nn):
  (_hi, ww) = pr
  ww

# shl.out's cell, from a shift not yet known

# shl.out's cell, from a shift not yet known
law sho_eta:
  for pp: Nat
  for cc: Bool
  for rr: Bool & Word(pp)
  {Word.shl.out.con(pp, cc, rr) == (so_hi(pp, rr), WCon{cc, so_w(pp, rr)}) : Bool & Word(1n+pp)}

# the proof of the law above
def sho_eta(_pp, _cc, rr):
  (_hi, _ww) = rr
  {==}

# shl.out as Nats: c and twice w, less the bit shifted out

# shl.out as Nats: c and twice w, less the bit shifted out
law w_sho:
  for +nn: Nat
  for ww: Word(nn)
  for +cc: Bool
  {Nat.add(Word.to_nat(nn, so_w(nn, Word.shl.out(nn, cc, ww))), Nat.mul(bit_nat(so_hi(nn, Word.shl.out(nn, cc, ww))),
    pow2(nn))) == Nat.add(bit_nat(cc), Nat.double(Word.to_nat(nn, ww))) : Nat}

# the proof of the law above
def w_sho(nn, ww, cc):
  match nn:
    case 0n:
      match ww:
        case WNil{}:
          Equal.trans(Nat, Nat.mul(bit_nat(cc), 1n), bit_nat(cc), Nat.add(bit_nat(cc), 0n), nat_mul_one(bit_nat(cc)),
            Equal.sym(Nat, Nat.add(bit_nat(cc), 0n), bit_nat(cc), nat_add_zero(bit_nat(cc))))
    case 1n+(+pp):
      match ww:
        case WCon{+bb, +tt}:
          ee = Equal.sym(Bool & Word(1n+pp), Word.shl.out.con(pp, cc, Word.shl.out(pp, bb, tt)),
            (so_hi(pp, Word.shl.out(pp, bb, tt)), WCon{cc, so_w(pp, Word.shl.out(pp, bb, tt))}), sho_eta(pp, cc,
              Word.shl.out(pp, bb, tt)))
          %ee : {Nat.add(Word.to_nat(1n+pp, so_w(1n+pp, _)), Nat.mul(bit_nat(so_hi(1n+pp, _)), Nat.double(pow2(pp)))) ==
            Nat.add(bit_nat(cc), Nat.double(Word.to_nat(1n+pp, WCon{bb, tt}))) : Nat}
          Equal.trans(Nat, Nat.add(Word.to_nat(1n+pp, WCon{cc, so_w(pp, Word.shl.out(pp, bb, tt))}),
            Nat.mul(bit_nat(so_hi(pp, Word.shl.out(pp, bb, tt))), Nat.double(pow2(pp)))), Nat.add(Nat.add(bit_nat(cc),
            Nat.double(Word.to_nat(pp, so_w(pp, Word.shl.out(pp, bb, tt))))), Nat.mul(bit_nat(so_hi(pp,
            Word.shl.out(pp, bb, tt))), Nat.double(pow2(pp)))), Nat.add(bit_nat(cc), Nat.double(Word.to_nat(1n+pp,
            WCon{bb, tt}))), Equal.cong(Nat, Nat, z145 => Nat.add(z145, Nat.mul(bit_nat(so_hi(pp, Word.shl.out(pp, bb,
            tt))), Nat.double(pow2(pp)))), Word.to_nat(1n+pp, WCon{cc, so_w(pp, Word.shl.out(pp, bb, tt))}),
            Nat.add(bit_nat(cc), Nat.double(Word.to_nat(pp, so_w(pp, Word.shl.out(pp, bb, tt))))), w_nat_con(pp, cc,
            so_w(pp, Word.shl.out(pp, bb, tt)))), Equal.trans(Nat, Nat.add(Nat.add(bit_nat(cc),
            Nat.double(Word.to_nat(pp, so_w(pp, Word.shl.out(pp, bb, tt))))), Nat.mul(bit_nat(so_hi(pp,
            Word.shl.out(pp, bb, tt))), Nat.double(pow2(pp)))), Nat.add(Nat.add(bit_nat(cc), Nat.double(Word.to_nat(pp,
            so_w(pp, Word.shl.out(pp, bb, tt))))), Nat.double(Nat.mul(bit_nat(so_hi(pp, Word.shl.out(pp, bb, tt))),
            pow2(pp)))), Nat.add(bit_nat(cc), Nat.double(Word.to_nat(1n+pp, WCon{bb, tt}))), Equal.cong(Nat, Nat,
            z146 => Nat.add(Nat.add(bit_nat(cc), Nat.double(Word.to_nat(pp, so_w(pp, Word.shl.out(pp, bb, tt))))),
            z146), Nat.mul(bit_nat(so_hi(pp, Word.shl.out(pp, bb, tt))), Nat.double(pow2(pp))),
            Nat.double(Nat.mul(bit_nat(so_hi(pp, Word.shl.out(pp, bb, tt))), pow2(pp))),
            nat_mul_double_r(bit_nat(so_hi(pp, Word.shl.out(pp, bb, tt))), pow2(pp))), Equal.trans(Nat,
            Nat.add(Nat.add(bit_nat(cc), Nat.double(Word.to_nat(pp, so_w(pp, Word.shl.out(pp, bb, tt))))),
            Nat.double(Nat.mul(bit_nat(so_hi(pp, Word.shl.out(pp, bb, tt))), pow2(pp)))), Nat.add(bit_nat(cc),
            Nat.add(Nat.double(Word.to_nat(pp, so_w(pp, Word.shl.out(pp, bb, tt)))),
            Nat.double(Nat.mul(bit_nat(so_hi(pp, Word.shl.out(pp, bb, tt))), pow2(pp))))), Nat.add(bit_nat(cc),
            Nat.double(Word.to_nat(1n+pp, WCon{bb, tt}))), nat_add_assoc(bit_nat(cc), Nat.double(Word.to_nat(pp,
            so_w(pp, Word.shl.out(pp, bb, tt)))), Nat.double(Nat.mul(bit_nat(so_hi(pp, Word.shl.out(pp, bb, tt))),
            pow2(pp)))), Equal.trans(Nat, Nat.add(bit_nat(cc), Nat.add(Nat.double(Word.to_nat(pp, so_w(pp,
            Word.shl.out(pp, bb, tt)))), Nat.double(Nat.mul(bit_nat(so_hi(pp, Word.shl.out(pp, bb, tt))), pow2(pp))))),
            Nat.add(bit_nat(cc), Nat.double(Nat.add(Word.to_nat(pp, so_w(pp, Word.shl.out(pp, bb, tt))),
            Nat.mul(bit_nat(so_hi(pp, Word.shl.out(pp, bb, tt))), pow2(pp))))), Nat.add(bit_nat(cc),
            Nat.double(Word.to_nat(1n+pp, WCon{bb, tt}))), Equal.cong(Nat, Nat, z147 => Nat.add(bit_nat(cc), z147),
            Nat.add(Nat.double(Word.to_nat(pp, so_w(pp, Word.shl.out(pp, bb, tt)))),
            Nat.double(Nat.mul(bit_nat(so_hi(pp, Word.shl.out(pp, bb, tt))), pow2(pp)))),
            Nat.double(Nat.add(Word.to_nat(pp, so_w(pp, Word.shl.out(pp, bb, tt))), Nat.mul(bit_nat(so_hi(pp,
            Word.shl.out(pp, bb, tt))), pow2(pp)))), Equal.sym(Nat, Nat.double(Nat.add(Word.to_nat(pp, so_w(pp,
            Word.shl.out(pp, bb, tt))), Nat.mul(bit_nat(so_hi(pp, Word.shl.out(pp, bb, tt))), pow2(pp)))),
            Nat.add(Nat.double(Word.to_nat(pp, so_w(pp, Word.shl.out(pp, bb, tt)))),
            Nat.double(Nat.mul(bit_nat(so_hi(pp, Word.shl.out(pp, bb, tt))), pow2(pp)))),
            nat_double_add(Word.to_nat(pp, so_w(pp, Word.shl.out(pp, bb, tt))), Nat.mul(bit_nat(so_hi(pp,
            Word.shl.out(pp, bb, tt))), pow2(pp))))), Equal.trans(Nat, Nat.add(bit_nat(cc),
            Nat.double(Nat.add(Word.to_nat(pp, so_w(pp, Word.shl.out(pp, bb, tt))), Nat.mul(bit_nat(so_hi(pp,
            Word.shl.out(pp, bb, tt))), pow2(pp))))), Nat.add(bit_nat(cc), Nat.double(Nat.add(bit_nat(bb),
            Nat.double(Word.to_nat(pp, tt))))), Nat.add(bit_nat(cc), Nat.double(Word.to_nat(1n+pp, WCon{bb, tt}))),
            Equal.cong(Nat, Nat, z148 => Nat.add(bit_nat(cc), Nat.double(z148)), Nat.add(Word.to_nat(pp, so_w(pp,
            Word.shl.out(pp, bb, tt))), Nat.mul(bit_nat(so_hi(pp, Word.shl.out(pp, bb, tt))), pow2(pp))),
            Nat.add(bit_nat(bb), Nat.double(Word.to_nat(pp, tt))), w_sho(pp, tt, bb)), Equal.cong(Nat, Nat,
            z149 => Nat.add(bit_nat(cc), Nat.double(z149)), Nat.add(bit_nat(bb), Nat.double(Word.to_nat(pp, tt))),
            Word.to_nat(1n+pp, WCon{bb, tt}), Equal.sym(Nat, Word.to_nat(1n+pp, WCon{bb, tt}), Nat.add(bit_nat(bb),
            Nat.double(Word.to_nat(pp, tt))), w_nat_con(pp, bb, tt))))))))

# w_sho, with 2^nn named through uu

# w_sho, with 2^nn named through uu
law w_sho_u:
  for +nn: Nat
  for uu: Unit
  for ww: Word(nn)
  for +cc: Bool
  {Nat.add(Word.to_nat(nn, so_w(nn, Word.shl.out(nn, cc, ww))), Nat.mul(bit_nat(so_hi(nn, Word.shl.out(nn, cc, ww))),
    pow2u(nn, uu))) == Nat.add(bit_nat(cc), Nat.double(Word.to_nat(nn, ww))) : Nat}

# the proof of the law above
def w_sho_u(nn, uu, ww, cc):
  match uu:
    case Unit{}:
      w_sho(nn, ww, cc)

# a quotient from divmod.go

# a quotient from divmod.go
def dmq(mm: Nat, pr: Word(mm) & U32) -> Word(mm):
  (qq, _rr) = pr
  qq

# a remainder from divmod.go

# a remainder from divmod.go
def dmr(mm: Nat, pr: Word(mm) & U32) -> U32:
  (_qq, rr) = pr
  rr

# below y, a bit and twice x is below twice y

# below y, a bit and twice x is below twice y
law nat_lt_bd:
  for bb: Bool
  for +xx: Nat
  for +yy: Nat
  for h: {Nat.is_lt(xx, yy) == True{} : Bool}
  {Nat.is_lt(Nat.add(bit_nat(bb), Nat.double(xx)), Nat.double(yy)) == True{} : Bool}

# the proof of the law above
def nat_lt_bd(bb, xx, yy, h):
  match bb:
    case False{}:
      nat_lt_dbl(xx, yy, h)
    case True{}:
      nat_lt_dbl1(xx, yy, h)

# below c, the left addend of a sum below c is below c too

# below c, the left addend of a sum below c is below c too
law nat_lt_add_rl:
  for +aa: Nat
  for +bb: Nat
  for +cc: Nat
  for h: {Nat.is_lt(Nat.add(aa, bb), cc) == True{} : Bool}
  {Nat.is_lt(aa, cc) == True{} : Bool}

# the proof of the law above
def nat_lt_add_rl(aa, bb, cc, h):
  nat_lt_add_l(bb, aa, cc, Equal.trans(Bool, Nat.is_lt(Nat.add(bb, aa), cc), Nat.is_lt(Nat.add(aa, bb), cc), True{},
    Equal.cong(Nat, Bool, xx => Nat.is_lt(xx, cc), Nat.add(bb, aa), Nat.add(aa, bb), nat_add_comm(bb, aa)), h))

# the last step of divmod.go: the new remainder is below ten

# the last step of divmod.go: the new remainder is below ten
law dm_fin_b:
  for +uu: Unit
  for pp: Nat
  for qq: Word(pp)
  for +ss: Word(32n)
  for gg: Bool
  for eg: {U32.is_ge(U32{ss}, 10) == gg : Bool}
  for hs: {Nat.is_lt(Word.to_nat(32n, ss), 20n) == True{} : Bool}
  {Nat.is_lt(U32.to_nat(dmr(1n+pp, U32.divmod.go.fin(pp, qq, U32{ss}, 10, gg))), 10n) == True{} : Bool}

# the proof of the law above
def dm_fin_b(uu, _pp, _qq, ss, gg, eg, hs):
  match gg:
    case True{}:
      Equal.trans(Bool, Nat.is_lt(U32.to_nat(U32.sub(U32{ss}, 10)), 10n), Nat.is_lt(Nat.add(U32.to_nat(U32.sub(U32{ss},
        10)), 10n), 20n), True{}, Equal.cong(Nat, Bool, z152 => Nat.is_lt(z152, 20n), Nat.add(10n,
        U32.to_nat(U32.sub(U32{ss}, 10))), Nat.add(U32.to_nat(U32.sub(U32{ss}, 10)), 10n), nat_add_comm(10n,
        U32.to_nat(U32.sub(U32{ss}, 10)))), Equal.trans(Bool, Nat.is_lt(Nat.add(U32.to_nat(U32.sub(U32{ss}, 10)), 10n),
        20n), Nat.is_lt(Word.to_nat(32n, ss), 20n), True{}, Equal.cong(Nat, Bool, z153 => Nat.is_lt(z153, 20n),
        Nat.add(U32.to_nat(U32.sub(U32{ss}, 10)), 10n), Word.to_nat(32n, ss), u_sub_ge(uu, U32{ss}, 10,
        cmp_ge_nlt(Nat.cmp(Word.to_nat(32n, ss), 10n), Equal.trans(Bool, Cmp.is_ge(Nat.cmp(Word.to_nat(32n, ss), 10n)),
        Cmp.is_ge(U32.cmp(U32{ss}, 10)), True{}, Equal.cong(Cmp, Bool, z150 => Cmp.is_ge(z150),
        Nat.cmp(Word.to_nat(32n, ss), 10n), U32.cmp(U32{ss}, 10), Equal.sym(Cmp, U32.cmp(U32{ss}, 10),
        Nat.cmp(Word.to_nat(32n, ss), 10n), u_cmp(U32{ss}, 10))), eg)))), hs))
    case False{}:
      cmp_nge_lt(Nat.cmp(Word.to_nat(32n, ss), 10n), Equal.trans(Bool, Cmp.is_ge(Nat.cmp(Word.to_nat(32n, ss), 10n)),
        Cmp.is_ge(U32.cmp(U32{ss}, 10)), False{}, Equal.cong(Cmp, Bool, z151 => Cmp.is_ge(z151),
        Nat.cmp(Word.to_nat(32n, ss), 10n), U32.cmp(U32{ss}, 10), Equal.sym(Cmp, U32.cmp(U32{ss}, 10),
        Nat.cmp(Word.to_nat(32n, ss), 10n), u_cmp(U32{ss}, 10))), eg))

# the last step of divmod.go: ten times the new quotient and the new
# remainder are twenty times the quotient and what was shifted in

# the last step of divmod.go: ten times the new quotient and the new
# remainder are twenty times the quotient and what was shifted in
law dm_fin_e:
  for +uu: Unit
  for +pp: Nat
  for +qq: Word(pp)
  for +ss: Word(32n)
  for gg: Bool
  for eg: {U32.is_ge(U32{ss}, 10) == gg : Bool}
  for hs: {Nat.is_lt(Word.to_nat(32n, ss), 20n) == True{} : Bool}
  {Nat.add(Nat.mul(Word.to_nat(1n+pp, dmq(1n+pp, U32.divmod.go.fin(pp, qq, U32{ss}, 10, gg))), 10n),
    U32.to_nat(dmr(1n+pp, U32.divmod.go.fin(pp, qq, U32{ss}, 10, gg)))) ==
    Nat.add(Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n), Word.to_nat(32n, ss)) : Nat}

# the proof of the law above
def dm_fin_e(uu, pp, qq, ss, gg, eg, _hs):
  match gg:
    case True{}:
      Equal.trans(Nat, Nat.add(Nat.add(10n, Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n)), U32.to_nat(U32.sub(U32{ss},
        10))), Nat.add(Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n), Nat.add(U32.to_nat(U32.sub(U32{ss}, 10)), 10n)),
        Nat.add(Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n), Word.to_nat(32n, ss)), Equal.trans(Nat,
        Nat.add(Nat.add(10n, Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n)), U32.to_nat(U32.sub(U32{ss}, 10))),
        Nat.add(10n, Nat.add(Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n), U32.to_nat(U32.sub(U32{ss}, 10)))),
        Nat.add(Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n), Nat.add(U32.to_nat(U32.sub(U32{ss}, 10)), 10n)),
        Equal.trans(Nat, Nat.add(Nat.add(10n, Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n)),
        U32.to_nat(U32.sub(U32{ss}, 10))), Nat.add(Nat.add(10n, Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n)),
        U32.to_nat(U32.sub(U32{ss}, 10))), Nat.add(10n, Nat.add(Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n),
        U32.to_nat(U32.sub(U32{ss}, 10)))), Equal.cong(Nat, Nat, z154 => Nat.add(z154, U32.to_nat(U32.sub(U32{ss},
        10))), Nat.add(10n, Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n)), Nat.add(10n,
        Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n)), {==}), nat_add_assoc(10n, Nat.mul(Nat.double(Word.to_nat(pp,
        qq)), 10n), U32.to_nat(U32.sub(U32{ss}, 10)))), Equal.sym(Nat, Nat.add(Nat.mul(Nat.double(Word.to_nat(pp, qq)),
        10n), Nat.add(U32.to_nat(U32.sub(U32{ss}, 10)), 10n)), Nat.add(10n, Nat.add(Nat.mul(Nat.double(Word.to_nat(pp,
        qq)), 10n), U32.to_nat(U32.sub(U32{ss}, 10)))), Equal.trans(Nat, Nat.add(Nat.mul(Nat.double(Word.to_nat(pp,
        qq)), 10n), Nat.add(U32.to_nat(U32.sub(U32{ss}, 10)), 10n)), Nat.add(Nat.mul(Nat.double(Word.to_nat(pp, qq)),
        10n), Nat.add(10n, U32.to_nat(U32.sub(U32{ss}, 10)))), Nat.add(10n, Nat.add(Nat.mul(Nat.double(Word.to_nat(pp,
        qq)), 10n), U32.to_nat(U32.sub(U32{ss}, 10)))), Equal.cong(Nat, Nat,
        z155 => Nat.add(Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n), z155), Nat.add(U32.to_nat(U32.sub(U32{ss}, 10)),
        10n), Nat.add(10n, U32.to_nat(U32.sub(U32{ss}, 10))), nat_add_comm(U32.to_nat(U32.sub(U32{ss}, 10)), 10n)),
        nat_add_lcomm(Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n), 10n, U32.to_nat(U32.sub(U32{ss}, 10)))))),
        Equal.cong(Nat, Nat, z156 => Nat.add(Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n), z156),
        Nat.add(U32.to_nat(U32.sub(U32{ss}, 10)), 10n), Word.to_nat(32n, ss), u_sub_ge(uu, U32{ss}, 10,
        cmp_ge_nlt(Nat.cmp(Word.to_nat(32n, ss), 10n), Equal.trans(Bool, Cmp.is_ge(Nat.cmp(Word.to_nat(32n, ss), 10n)),
        Cmp.is_ge(U32.cmp(U32{ss}, 10)), True{}, Equal.cong(Cmp, Bool, z150 => Cmp.is_ge(z150),
        Nat.cmp(Word.to_nat(32n, ss), 10n), U32.cmp(U32{ss}, 10), Equal.sym(Cmp, U32.cmp(U32{ss}, 10),
        Nat.cmp(Word.to_nat(32n, ss), 10n), u_cmp(U32{ss}, 10))), eg)))))
    case False{}:
      {==}

# divmod.go's shift, when it shifts out 0: the remainder is below ten

# divmod.go's shift, when it shifts out 0: the remainder is below ten
law dm_ts2_b:
  for +uu: Unit
  for +pp: Nat
  for +qq: Word(pp)
  for tt: Bool
  for +ss: Word(32n)
  for ht: {tt == False{} : Bool}
  for hs: {Nat.is_lt(Word.to_nat(32n, ss), 20n) == True{} : Bool}
  {Nat.is_lt(U32.to_nat(dmr(1n+pp, U32.divmod.go.shl(pp, qq, 10, (tt, ss)))), 10n) == True{} : Bool}

# the proof of the law above
def dm_ts2_b(uu, pp, qq, tt, ss, ht, hs):
  match tt:
    case False{}:
      dm_fin_b(uu, pp, qq, ss, U32.is_ge(U32{ss}, 10), {==}, hs)
    case True{}:
      Empty.absurd({Nat.is_lt(U32.to_nat(dmr(1n+pp, U32.divmod.go.shl(pp, qq, 10, (True{}, ss)))),
        10n) == True{} : Bool},
        true_false(ht))

# divmod.go's shift, when it shifts out 0: ten times the quotient and the
# remainder

# divmod.go's shift, when it shifts out 0: ten times the quotient and the
# remainder
law dm_ts2_e:
  for +uu: Unit
  for +pp: Nat
  for +qq: Word(pp)
  for tt: Bool
  for +ss: Word(32n)
  for ht: {tt == False{} : Bool}
  for hs: {Nat.is_lt(Word.to_nat(32n, ss), 20n) == True{} : Bool}
  {Nat.add(Nat.mul(Word.to_nat(1n+pp, dmq(1n+pp, U32.divmod.go.shl(pp, qq, 10, (tt, ss)))), 10n), U32.to_nat(dmr(1n+pp,
    U32.divmod.go.shl(pp, qq, 10, (tt, ss))))) ==
    Nat.add(Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n), Word.to_nat(32n, ss)) : Nat}

# the proof of the law above
def dm_ts2_e(uu, pp, qq, tt, ss, ht, hs):
  match tt:
    case False{}:
      dm_fin_e(uu, pp, qq, ss, U32.is_ge(U32{ss}, 10), {==}, hs)
    case True{}:
      Empty.absurd({Nat.add(Nat.mul(Word.to_nat(1n+pp, dmq(1n+pp, U32.divmod.go.shl(pp, qq, 10, (True{}, ss)))), 10n),
        U32.to_nat(dmr(1n+pp, U32.divmod.go.shl(pp, qq, 10, (True{}, ss))))) ==
        Nat.add(Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n), Word.to_nat(32n, ss)) : Nat}, true_false(ht))

# a step of the division, as the law after it states it
law dm_ts_b:
  for +uu: Unit
  for +pp: Nat
  for +qq: Word(pp)
  for ts: Bool & Word(32n)
  for ht: {so_hi(32n, ts) == False{} : Bool}
  for hs: {Nat.is_lt(Word.to_nat(32n, so_w(32n, ts)), 20n) == True{} : Bool}
  {Nat.is_lt(U32.to_nat(dmr(1n+pp, U32.divmod.go.shl(pp, qq, 10, ts))), 10n) == True{} : Bool}

# the proof of the law above
def dm_ts_b(uu, pp, qq, ts, ht, hs):
  (tt, ss) = ts
  dm_ts2_b(uu, pp, qq, tt, ss, ht, hs)

# a step of the division, as the law after it states it
law dm_ts_e:
  for +uu: Unit
  for +pp: Nat
  for +qq: Word(pp)
  for ts: Bool & Word(32n)
  for ht: {so_hi(32n, ts) == False{} : Bool}
  for hs: {Nat.is_lt(Word.to_nat(32n, so_w(32n, ts)), 20n) == True{} : Bool}
  {Nat.add(Nat.mul(Word.to_nat(1n+pp, dmq(1n+pp, U32.divmod.go.shl(pp, qq, 10, ts))), 10n), U32.to_nat(dmr(1n+pp,
    U32.divmod.go.shl(pp, qq, 10, ts)))) ==
    Nat.add(Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n), Word.to_nat(32n, so_w(32n, ts))) : Nat}

# the proof of the law above
def dm_ts_e(uu, pp, qq, ts, ht, hs):
  (tt, ss) = ts
  dm_ts2_e(uu, pp, qq, tt, ss, ht, hs)

# the bit shifted out of a remainder below ten is 0: past it, 2^32 is too
# large for the sum to be below twenty

# the bit shifted out of a remainder below ten is 0: past it, 2^32 is too
# large for the sum to be below twenty
law hi_false:
  for +uu: Unit
  for hb: Bool
  for +ww: Nat
  for +vv: Nat
  for h: {Nat.add(ww, Nat.mul(bit_nat(hb), pow2u(32n, uu))) == vv : Nat}
  for hv: {Nat.is_lt(vv, 20n) == True{} : Bool}
  {hb == False{} : Bool}

# the proof of the law above
def hi_false(uu, hb, ww, vv, h, hv):
  match hb:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, true_false(Equal.trans(Bool, True{}, Nat.is_lt(vv, 20n),
        Nat.is_lt(Nat.add(Nat.add(Nat.add(64n, pz6(26n, uu)), 0n), ww), 20n), Equal.sym(Bool, Nat.is_lt(vv, 20n),
        True{}, hv), Equal.trans(Bool, Nat.is_lt(vv, 20n), Nat.is_lt(Nat.add(ww, Nat.add(pow2u(32n, uu), 0n)), 20n),
        Nat.is_lt(Nat.add(Nat.add(Nat.add(64n, pz6(26n, uu)), 0n), ww), 20n), Equal.cong(Nat, Bool,
        z157 => Nat.is_lt(z157, 20n), vv, Nat.add(ww, Nat.add(pow2u(32n, uu), 0n)), Equal.sym(Nat, Nat.add(ww,
        Nat.add(pow2u(32n, uu), 0n)), vv, h)), Equal.trans(Bool, Nat.is_lt(Nat.add(ww, Nat.add(pow2u(32n, uu), 0n)),
        20n), Nat.is_lt(Nat.add(Nat.add(pow2u(32n, uu), 0n), ww), 20n), Nat.is_lt(Nat.add(Nat.add(Nat.add(64n, pz6(26n,
        uu)), 0n), ww), 20n), Equal.cong(Nat, Bool, z158 => Nat.is_lt(z158, 20n), Nat.add(ww, Nat.add(pow2u(32n, uu),
        0n)), Nat.add(Nat.add(pow2u(32n, uu), 0n), ww), nat_add_comm(ww, Nat.add(pow2u(32n, uu), 0n))), Equal.cong(Nat,
        Bool, z159 => Nat.is_lt(Nat.add(Nat.add(z159, 0n), ww), 20n), pow2u(32n, uu), Nat.add(64n, pz6(26n, uu)),
        pw_big(26n, uu)))))))

# one step of divmod.go on a remainder below ten: the new remainder is below
# ten

# one step of divmod.go on a remainder below ten: the new remainder is below
# ten
law dm_rec_b:
  for +uu: Unit
  for +pp: Nat
  for +a0: Bool
  for +qq: Word(pp)
  for +rw: Word(32n)
  for +hr: {Nat.is_lt(Word.to_nat(32n, rw), 10n) == True{} : Bool}
  {Nat.is_lt(U32.to_nat(dmr(1n+pp, U32.divmod.go.rec(pp, a0, 10, (qq, U32{rw})))), 10n) == True{} : Bool}

# the proof of the law above
def dm_rec_b(uu, pp, a0, qq, rw, hr):
  dm_ts_b(uu, pp, qq, Word.shl.out(32n, a0, rw), hi_false(uu, so_hi(32n, Word.shl.out(32n, a0, rw)), Word.to_nat(32n,
    so_w(32n, Word.shl.out(32n, a0, rw))), Nat.add(bit_nat(a0), Nat.double(Word.to_nat(32n, rw))), w_sho_u(32n, uu, rw,
    a0), nat_lt_bd(a0, Word.to_nat(32n, rw), 10n, hr)), nat_lt_add_rl(Word.to_nat(32n, so_w(32n, Word.shl.out(32n, a0,
    rw))), Nat.mul(bit_nat(so_hi(32n, Word.shl.out(32n, a0, rw))), pow2u(32n, uu)), 20n, Equal.trans(Bool,
    Nat.is_lt(Nat.add(Word.to_nat(32n, so_w(32n, Word.shl.out(32n, a0, rw))), Nat.mul(bit_nat(so_hi(32n,
    Word.shl.out(32n, a0, rw))), pow2u(32n, uu))), 20n), Nat.is_lt(Nat.add(bit_nat(a0), Nat.double(Word.to_nat(32n,
    rw))), 20n), True{}, Equal.cong(Nat, Bool, z160 => Nat.is_lt(z160, 20n), Nat.add(Word.to_nat(32n, so_w(32n,
    Word.shl.out(32n, a0, rw))), Nat.mul(bit_nat(so_hi(32n, Word.shl.out(32n, a0, rw))), pow2u(32n, uu))),
    Nat.add(bit_nat(a0), Nat.double(Word.to_nat(32n, rw))), w_sho_u(32n, uu, rw, a0)), nat_lt_bd(a0, Word.to_nat(32n,
    rw), 10n, hr))))

# one step of divmod.go on a remainder below ten: ten times the quotient and
# the remainder take in one more bit

# one step of divmod.go on a remainder below ten: ten times the quotient and
# the remainder take in one more bit
law dm_rec_e:
  for +uu: Unit
  for +pp: Nat
  for +a0: Bool
  for +qq: Word(pp)
  for +rw: Word(32n)
  for +hr: {Nat.is_lt(Word.to_nat(32n, rw), 10n) == True{} : Bool}
  {Nat.add(Nat.mul(Word.to_nat(1n+pp, dmq(1n+pp, U32.divmod.go.rec(pp, a0, 10, (qq, U32{rw})))), 10n),
    U32.to_nat(dmr(1n+pp, U32.divmod.go.rec(pp, a0, 10, (qq, U32{rw}))))) == Nat.add(bit_nat(a0),
    Nat.double(Nat.add(Nat.mul(Word.to_nat(pp, qq), 10n), Word.to_nat(32n, rw)))) : Nat}

# the proof of the law above
def dm_rec_e(uu, pp, a0, qq, rw, hr):
  Equal.trans(Nat, Nat.add(Nat.mul(Word.to_nat(1n+pp, dmq(1n+pp, U32.divmod.go.rec(pp, a0, 10, (qq, U32{rw})))), 10n),
    U32.to_nat(dmr(1n+pp, U32.divmod.go.rec(pp, a0, 10, (qq, U32{rw}))))), Nat.add(Nat.mul(Nat.double(Word.to_nat(pp,
    qq)), 10n), Word.to_nat(32n, so_w(32n, Word.shl.out(32n, a0, rw)))), Nat.add(bit_nat(a0),
    Nat.double(Nat.add(Nat.mul(Word.to_nat(pp, qq), 10n), Word.to_nat(32n, rw)))), dm_ts_e(uu, pp, qq,
    Word.shl.out(32n, a0, rw), hi_false(uu, so_hi(32n, Word.shl.out(32n, a0, rw)), Word.to_nat(32n, so_w(32n,
    Word.shl.out(32n, a0, rw))), Nat.add(bit_nat(a0), Nat.double(Word.to_nat(32n, rw))), w_sho_u(32n, uu, rw, a0),
    nat_lt_bd(a0, Word.to_nat(32n, rw), 10n, hr)), nat_lt_add_rl(Word.to_nat(32n, so_w(32n, Word.shl.out(32n, a0,
    rw))), Nat.mul(bit_nat(so_hi(32n, Word.shl.out(32n, a0, rw))), pow2u(32n, uu)), 20n, Equal.trans(Bool,
    Nat.is_lt(Nat.add(Word.to_nat(32n, so_w(32n, Word.shl.out(32n, a0, rw))), Nat.mul(bit_nat(so_hi(32n,
    Word.shl.out(32n, a0, rw))), pow2u(32n, uu))), 20n), Nat.is_lt(Nat.add(bit_nat(a0), Nat.double(Word.to_nat(32n,
    rw))), 20n), True{}, Equal.cong(Nat, Bool, z160 => Nat.is_lt(z160, 20n), Nat.add(Word.to_nat(32n, so_w(32n,
    Word.shl.out(32n, a0, rw))), Nat.mul(bit_nat(so_hi(32n, Word.shl.out(32n, a0, rw))), pow2u(32n, uu))),
    Nat.add(bit_nat(a0), Nat.double(Word.to_nat(32n, rw))), w_sho_u(32n, uu, rw, a0)), nat_lt_bd(a0, Word.to_nat(32n,
    rw), 10n, hr)))), Equal.trans(Nat, Nat.add(Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n), Word.to_nat(32n,
    so_w(32n, Word.shl.out(32n, a0, rw)))), Nat.add(Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n), Nat.add(bit_nat(a0),
    Nat.double(Word.to_nat(32n, rw)))), Nat.add(bit_nat(a0), Nat.double(Nat.add(Nat.mul(Word.to_nat(pp, qq), 10n),
    Word.to_nat(32n, rw)))), Equal.cong(Nat, Nat, z162 => Nat.add(Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n), z162),
    Word.to_nat(32n, so_w(32n, Word.shl.out(32n, a0, rw))), Nat.add(bit_nat(a0), Nat.double(Word.to_nat(32n, rw))),
    Equal.trans(Nat, Word.to_nat(32n, so_w(32n, Word.shl.out(32n, a0, rw))), Nat.add(Word.to_nat(32n, so_w(32n,
    Word.shl.out(32n, a0, rw))), 0n), Nat.add(bit_nat(a0), Nat.double(Word.to_nat(32n, rw))), Equal.sym(Nat,
    Nat.add(Word.to_nat(32n, so_w(32n, Word.shl.out(32n, a0, rw))), 0n), Word.to_nat(32n, so_w(32n, Word.shl.out(32n,
    a0, rw))), nat_add_zero(Word.to_nat(32n, so_w(32n, Word.shl.out(32n, a0, rw))))), Equal.trans(Nat,
    Nat.add(Word.to_nat(32n, so_w(32n, Word.shl.out(32n, a0, rw))), 0n), Nat.add(Word.to_nat(32n, so_w(32n,
    Word.shl.out(32n, a0, rw))), Nat.mul(bit_nat(so_hi(32n, Word.shl.out(32n, a0, rw))), pow2u(32n, uu))),
    Nat.add(bit_nat(a0), Nat.double(Word.to_nat(32n, rw))), Equal.cong(Bool, Nat, z161 => Nat.add(Word.to_nat(32n,
    so_w(32n, Word.shl.out(32n, a0, rw))), Nat.mul(bit_nat(z161), pow2u(32n, uu))), False{}, so_hi(32n,
    Word.shl.out(32n, a0, rw)), Equal.sym(Bool, so_hi(32n, Word.shl.out(32n, a0, rw)), False{}, hi_false(uu, so_hi(32n,
    Word.shl.out(32n, a0, rw)), Word.to_nat(32n, so_w(32n, Word.shl.out(32n, a0, rw))), Nat.add(bit_nat(a0),
    Nat.double(Word.to_nat(32n, rw))), w_sho_u(32n, uu, rw, a0), nat_lt_bd(a0, Word.to_nat(32n, rw), 10n, hr)))),
    w_sho_u(32n, uu, rw, a0)))), Equal.trans(Nat, Nat.add(Nat.mul(Nat.double(Word.to_nat(pp, qq)), 10n),
    Nat.add(bit_nat(a0), Nat.double(Word.to_nat(32n, rw)))), Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)),
    Nat.add(bit_nat(a0), Nat.double(Word.to_nat(32n, rw)))), Nat.add(bit_nat(a0),
    Nat.double(Nat.add(Nat.mul(Word.to_nat(pp, qq), 10n), Word.to_nat(32n, rw)))), Equal.cong(Nat, Nat,
    z163 => Nat.add(z163, Nat.add(bit_nat(a0), Nat.double(Word.to_nat(32n, rw)))), Nat.mul(Nat.double(Word.to_nat(pp,
    qq)), 10n), Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)), nat_mul_double_l(Word.to_nat(pp, qq), 10n)),
    Equal.trans(Nat, Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)), Nat.add(bit_nat(a0),
    Nat.double(Word.to_nat(32n, rw)))), Nat.add(bit_nat(a0), Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)),
    Nat.double(Word.to_nat(32n, rw)))), Nat.add(bit_nat(a0), Nat.double(Nat.add(Nat.mul(Word.to_nat(pp, qq), 10n),
    Word.to_nat(32n, rw)))), Equal.trans(Nat, Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)),
    Nat.add(bit_nat(a0), Nat.double(Word.to_nat(32n, rw)))), Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)),
    Nat.add(Nat.double(Word.to_nat(32n, rw)), bit_nat(a0))), Nat.add(bit_nat(a0),
    Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)), Nat.double(Word.to_nat(32n, rw)))), Equal.cong(Nat, Nat,
    z164 => Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)), z164), Nat.add(bit_nat(a0),
    Nat.double(Word.to_nat(32n, rw))), Nat.add(Nat.double(Word.to_nat(32n, rw)), bit_nat(a0)),
    nat_add_comm(bit_nat(a0), Nat.double(Word.to_nat(32n, rw)))), Equal.sym(Nat, Nat.add(bit_nat(a0),
    Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)), Nat.double(Word.to_nat(32n, rw)))),
    Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)), Nat.add(Nat.double(Word.to_nat(32n, rw)), bit_nat(a0))),
    Equal.trans(Nat, Nat.add(bit_nat(a0), Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)),
    Nat.double(Word.to_nat(32n, rw)))), Nat.add(bit_nat(a0), Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)),
    Nat.double(Word.to_nat(32n, rw)))), Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)),
    Nat.add(Nat.double(Word.to_nat(32n, rw)), bit_nat(a0))), Equal.cong(Nat, Nat, z165 => Nat.add(bit_nat(a0), z165),
    Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)), Nat.double(Word.to_nat(32n, rw))),
    Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)), Nat.double(Word.to_nat(32n, rw))), {==}), Equal.trans(Nat,
    Nat.add(bit_nat(a0), Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)), Nat.double(Word.to_nat(32n, rw)))),
    Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)), Nat.add(bit_nat(a0), Nat.double(Word.to_nat(32n, rw)))),
    Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)), Nat.add(Nat.double(Word.to_nat(32n, rw)), bit_nat(a0))),
    nat_add_lcomm(bit_nat(a0), Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)), Nat.double(Word.to_nat(32n, rw))),
    Equal.cong(Nat, Nat, z166 => Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)), z166), Nat.add(bit_nat(a0),
    Nat.double(Word.to_nat(32n, rw))), Nat.add(Nat.double(Word.to_nat(32n, rw)), bit_nat(a0)),
    nat_add_comm(bit_nat(a0), Nat.double(Word.to_nat(32n, rw)))))))), Equal.cong(Nat, Nat, z167 => Nat.add(bit_nat(a0),
    z167), Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)), Nat.double(Word.to_nat(32n, rw))),
    Nat.double(Nat.add(Nat.mul(Word.to_nat(pp, qq), 10n), Word.to_nat(32n, rw))), Equal.sym(Nat,
    Nat.double(Nat.add(Nat.mul(Word.to_nat(pp, qq), 10n), Word.to_nat(32n, rw))),
    Nat.add(Nat.double(Nat.mul(Word.to_nat(pp, qq), 10n)), Nat.double(Word.to_nat(32n, rw))),
    nat_double_add(Nat.mul(Word.to_nat(pp, qq), 10n), Word.to_nat(32n, rw))))))))

# a step of the division, as the law after it states it
law dm_qr_b:
  for +uu: Unit
  for +pp: Nat
  for +a0: Bool
  for +qq: Word(pp)
  for rr: U32
  for hr: {Nat.is_lt(U32.to_nat(rr), 10n) == True{} : Bool}
  {Nat.is_lt(U32.to_nat(dmr(1n+pp, U32.divmod.go.rec(pp, a0, 10, (qq, rr)))), 10n) == True{} : Bool}

# the proof of the law above
def dm_qr_b(uu, pp, a0, qq, rr, hr):
  match rr:
    case U32{rw}:
      dm_rec_b(uu, pp, a0, qq, rw, hr)

# a step of the division, as the law after it states it
law dm_qr_e:
  for +uu: Unit
  for +pp: Nat
  for +a0: Bool
  for +qq: Word(pp)
  for rr: U32
  for hr: {Nat.is_lt(U32.to_nat(rr), 10n) == True{} : Bool}
  {Nat.add(Nat.mul(Word.to_nat(1n+pp, dmq(1n+pp, U32.divmod.go.rec(pp, a0, 10, (qq, rr)))), 10n), U32.to_nat(dmr(1n+pp,
    U32.divmod.go.rec(pp, a0, 10, (qq, rr))))) ==
    Nat.add(bit_nat(a0), Nat.double(Nat.add(Nat.mul(Word.to_nat(pp, qq), 10n), U32.to_nat(rr)))) : Nat}

# the proof of the law above
def dm_qr_e(uu, pp, a0, qq, rr, hr):
  match rr:
    case U32{rw}:
      dm_rec_e(uu, pp, a0, qq, rw, hr)

# a step of the division, as the law after it states it
law dm_pr_b:
  for +uu: Unit
  for +pp: Nat
  for +a0: Bool
  for pr: Word(pp) & U32
  for hr: {Nat.is_lt(U32.to_nat(dmr(pp, pr)), 10n) == True{} : Bool}
  {Nat.is_lt(U32.to_nat(dmr(1n+pp, U32.divmod.go.rec(pp, a0, 10, pr))), 10n) == True{} : Bool}

# the proof of the law above
def dm_pr_b(uu, pp, a0, pr, hr):
  (qq, rr) = pr
  dm_qr_b(uu, pp, a0, qq, rr, hr)

# a step of the division, as the law after it states it
law dm_pr_e:
  for +uu: Unit
  for +pp: Nat
  for +a0: Bool
  for pr: Word(pp) & U32
  for hr: {Nat.is_lt(U32.to_nat(dmr(pp, pr)), 10n) == True{} : Bool}
  {Nat.add(Nat.mul(Word.to_nat(1n+pp, dmq(1n+pp, U32.divmod.go.rec(pp, a0, 10, pr))), 10n), U32.to_nat(dmr(1n+pp,
    U32.divmod.go.rec(pp, a0, 10, pr)))) ==
    Nat.add(bit_nat(a0), Nat.double(Nat.add(Nat.mul(Word.to_nat(pp, dmq(pp, pr)), 10n), U32.to_nat(dmr(pp,
      pr))))) : Nat}

# the proof of the law above
def dm_pr_e(uu, pp, a0, pr, hr):
  (qq, rr) = pr
  dm_qr_e(uu, pp, a0, qq, rr, hr)

# divmod.go by ten leaves a remainder below ten

# divmod.go by ten leaves a remainder below ten
law dm_b:
  for +uu: Unit
  for mm: Nat
  for aa: Word(mm)
  {Nat.is_lt(U32.to_nat(dmr(mm, U32.divmod.go(mm, aa, 10))), 10n) == True{} : Bool}

# the proof of the law above
def dm_b(uu, mm, aa):
  match mm aa:
    case 0n WNil{}:
      {==}
    case 1n+(+pp) WCon{+a0, +hi}:
      dm_pr_b(uu, pp, a0, U32.divmod.go(pp, hi, 10), dm_b(uu, pp, hi))

# divmod.go by ten: ten times the quotient and the remainder are the word

# divmod.go by ten: ten times the quotient and the remainder are the word
law dm_e:
  for +uu: Unit
  for mm: Nat
  for aa: Word(mm)
  {Nat.add(Nat.mul(Word.to_nat(mm, dmq(mm, U32.divmod.go(mm, aa, 10))), 10n),
    U32.to_nat(dmr(mm, U32.divmod.go(mm, aa, 10)))) == Word.to_nat(mm, aa) : Nat}

# the proof of the law above
def dm_e(uu, mm, aa):
  match mm aa:
    case 0n WNil{}:
      {==}
    case 1n+(+pp) WCon{+a0, +hi}:
      Equal.trans(Nat, Nat.add(Nat.mul(Word.to_nat(1n+pp, dmq(1n+pp, U32.divmod.go.rec(pp, a0, 10, U32.divmod.go(pp,
        hi, 10)))), 10n), U32.to_nat(dmr(1n+pp, U32.divmod.go.rec(pp, a0, 10, U32.divmod.go(pp, hi, 10))))),
        Nat.add(bit_nat(a0), Nat.double(Nat.add(Nat.mul(Word.to_nat(pp, dmq(pp, U32.divmod.go(pp, hi, 10))), 10n),
        U32.to_nat(dmr(pp, U32.divmod.go(pp, hi, 10)))))), Word.to_nat(1n+pp, WCon{a0, hi}), dm_pr_e(uu, pp, a0,
        U32.divmod.go(pp, hi, 10), dm_b(uu, pp, hi)), Equal.trans(Nat, Nat.add(bit_nat(a0),
        Nat.double(Nat.add(Nat.mul(Word.to_nat(pp, dmq(pp, U32.divmod.go(pp, hi, 10))), 10n), U32.to_nat(dmr(pp,
        U32.divmod.go(pp, hi, 10)))))), Nat.add(bit_nat(a0), Nat.double(Word.to_nat(pp, hi))), Word.to_nat(1n+pp,
        WCon{a0, hi}), Equal.cong(Nat, Nat, z168 => Nat.add(bit_nat(a0), Nat.double(z168)),
        Nat.add(Nat.mul(Word.to_nat(pp, dmq(pp, U32.divmod.go(pp, hi, 10))), 10n), U32.to_nat(dmr(pp, U32.divmod.go(pp,
        hi, 10)))), Word.to_nat(pp, hi), dm_e(uu, pp, hi)), Equal.sym(Nat, Word.to_nat(1n+pp, WCon{a0, hi}),
        Nat.add(bit_nat(a0), Nat.double(Word.to_nat(pp, hi))), w_nat_con(pp, a0, hi))))

# U32.div's result, from a division not yet known

# U32.div's result, from a division not yet known
law div_fin_eta:
  for pr: Word(32n) & U32
  {U32.div.fin(pr) == U32{dmq(32n, pr)} : U32}

# the proof of the law above
def div_fin_eta(pr):
  (_qq, _rr) = pr
  {==}

# U32.mod's result, from a division not yet known

# U32.mod's result, from a division not yet known
law mod_fin_eta:
  for pr: Word(32n) & U32
  {U32.mod.fin(pr) == dmr(32n, pr) : U32}

# the proof of the law above
def mod_fin_eta(pr):
  (_qq, _rr) = pr
  {==}

# ten times a U32 over ten, and the remainder, are the U32

# ten times a U32 over ten, and the remainder, are the U32
law u_div:
  for +uu: Unit
  for nn: U32
  {Nat.add(Nat.mul(U32.to_nat(U32.div(nn, 10)), 10n), U32.to_nat(U32.mod(nn, 10))) == U32.to_nat(nn) : Nat}

# the proof of the law above
def u_div(uu, nn):
  match nn:
    case U32{+nw}:
      Equal.trans(Nat, Nat.add(Nat.mul(U32.to_nat(U32.div.fin(U32.divmod.go(32n, nw, 10))), 10n),
        U32.to_nat(U32.mod.fin(U32.divmod.go(32n, nw, 10)))), Nat.add(Nat.mul(U32.to_nat(U32{dmq(32n,
        U32.divmod.go(32n, nw, 10))}), 10n), U32.to_nat(U32.mod.fin(U32.divmod.go(32n, nw, 10)))), Word.to_nat(32n,
        nw), Equal.cong(U32, Nat, z169 => Nat.add(Nat.mul(U32.to_nat(z169), 10n),
        U32.to_nat(U32.mod.fin(U32.divmod.go(32n, nw, 10)))), U32.div.fin(U32.divmod.go(32n, nw, 10)), U32{dmq(32n,
        U32.divmod.go(32n, nw, 10))}, div_fin_eta(U32.divmod.go(32n, nw, 10))), Equal.trans(Nat,
        Nat.add(Nat.mul(U32.to_nat(U32{dmq(32n, U32.divmod.go(32n, nw, 10))}), 10n),
        U32.to_nat(U32.mod.fin(U32.divmod.go(32n, nw, 10)))), Nat.add(Nat.mul(U32.to_nat(U32{dmq(32n,
        U32.divmod.go(32n, nw, 10))}), 10n), U32.to_nat(dmr(32n, U32.divmod.go(32n, nw, 10)))), Word.to_nat(32n, nw),
        Equal.cong(U32, Nat, z170 => Nat.add(Nat.mul(U32.to_nat(U32{dmq(32n, U32.divmod.go(32n, nw, 10))}), 10n),
        U32.to_nat(z170)), U32.mod.fin(U32.divmod.go(32n, nw, 10)), dmr(32n, U32.divmod.go(32n, nw, 10)),
        mod_fin_eta(U32.divmod.go(32n, nw, 10))), dm_e(uu, 32n, nw)))

# a U32's remainder over ten is below ten

# a U32's remainder over ten is below ten
law u_mod:
  for +uu: Unit
  for nn: U32
  {Nat.is_lt(U32.to_nat(U32.mod(nn, 10)), 10n) == True{} : Bool}

# the proof of the law above
def u_mod(uu, nn):
  match nn:
    case U32{+nw}:
      Equal.trans(Bool, Nat.is_lt(U32.to_nat(U32.mod.fin(U32.divmod.go(32n, nw, 10))), 10n),
        Nat.is_lt(U32.to_nat(dmr(32n, U32.divmod.go(32n, nw, 10))), 10n), True{}, Equal.cong(U32, Bool,
        z171 => Nat.is_lt(U32.to_nat(z171), 10n), U32.mod.fin(U32.divmod.go(32n, nw, 10)), dmr(32n, U32.divmod.go(32n,
        nw, 10)), mod_fin_eta(U32.divmod.go(32n, nw, 10))), dm_b(uu, 32n, nw))

# JSON-TREE-6: one step of U32.read

# ten times q and r below ten is ten times a and d below ten: q is a

# how many times 2^32 a step of U32.read passes
def step_ks(+aa: U32, dd: U32) -> Nat:
  Nat.add(uadd_k(U32.mul(aa, 10), dd), umk(aa))

# a step of U32.read as Nats: the new accumulator, and how many times it
# passes 2^32, is ten times the old one and the digit

# a step of U32.read as Nats: the new accumulator, and how many times it
# passes 2^32, is ten times the old one and the digit
law step_k:
  for +uu: Unit
  for +acc: U32
  for +dd: U32
  {Nat.add(U32.to_nat(U32.add(U32.mul(acc, 10), dd)), Nat.mul(step_ks(acc, dd), pow2u(32n,
    uu))) == Nat.add(Nat.mul(U32.to_nat(acc), 10n), U32.to_nat(dd)) : Nat}

# the proof of the law above
def step_k(uu, acc, dd):
  Equal.trans(Nat, Nat.add(U32.to_nat(U32.add(U32.mul(acc, 10), dd)), Nat.mul(Nat.add(uadd_k(U32.mul(acc, 10), dd),
    umk(acc)), pow2u(32n, uu))), Nat.add(U32.to_nat(U32.add(U32.mul(acc, 10), dd)), Nat.add(Nat.mul(uadd_k(U32.mul(acc,
    10), dd), pow2u(32n, uu)), Nat.mul(umk(acc), pow2u(32n, uu)))), Nat.add(Nat.mul(U32.to_nat(acc), 10n),
    U32.to_nat(dd)), Equal.cong(Nat, Nat, z172 => Nat.add(U32.to_nat(U32.add(U32.mul(acc, 10), dd)), z172),
    Nat.mul(Nat.add(uadd_k(U32.mul(acc, 10), dd), umk(acc)), pow2u(32n, uu)), Nat.add(Nat.mul(uadd_k(U32.mul(acc, 10),
    dd), pow2u(32n, uu)), Nat.mul(umk(acc), pow2u(32n, uu))), nat_mul_add_r(uadd_k(U32.mul(acc, 10), dd), umk(acc),
    pow2u(32n, uu))), Equal.trans(Nat, Nat.add(U32.to_nat(U32.add(U32.mul(acc, 10), dd)),
    Nat.add(Nat.mul(uadd_k(U32.mul(acc, 10), dd), pow2u(32n, uu)), Nat.mul(umk(acc), pow2u(32n, uu)))),
    Nat.add(Nat.add(U32.to_nat(U32.add(U32.mul(acc, 10), dd)), Nat.mul(uadd_k(U32.mul(acc, 10), dd), pow2u(32n, uu))),
    Nat.mul(umk(acc), pow2u(32n, uu))), Nat.add(Nat.mul(U32.to_nat(acc), 10n), U32.to_nat(dd)), Equal.sym(Nat,
    Nat.add(Nat.add(U32.to_nat(U32.add(U32.mul(acc, 10), dd)), Nat.mul(uadd_k(U32.mul(acc, 10), dd), pow2u(32n, uu))),
    Nat.mul(umk(acc), pow2u(32n, uu))), Nat.add(U32.to_nat(U32.add(U32.mul(acc, 10), dd)),
    Nat.add(Nat.mul(uadd_k(U32.mul(acc, 10), dd), pow2u(32n, uu)), Nat.mul(umk(acc), pow2u(32n, uu)))),
    nat_add_assoc(U32.to_nat(U32.add(U32.mul(acc, 10), dd)), Nat.mul(uadd_k(U32.mul(acc, 10), dd), pow2u(32n, uu)),
    Nat.mul(umk(acc), pow2u(32n, uu)))), Equal.trans(Nat, Nat.add(Nat.add(U32.to_nat(U32.add(U32.mul(acc, 10), dd)),
    Nat.mul(uadd_k(U32.mul(acc, 10), dd), pow2u(32n, uu))), Nat.mul(umk(acc), pow2u(32n, uu))),
    Nat.add(Nat.add(U32.to_nat(U32.mul(acc, 10)), U32.to_nat(dd)), Nat.mul(umk(acc), pow2u(32n, uu))),
    Nat.add(Nat.mul(U32.to_nat(acc), 10n), U32.to_nat(dd)), Equal.cong(Nat, Nat, z173 => Nat.add(z173,
    Nat.mul(umk(acc), pow2u(32n, uu))), Nat.add(U32.to_nat(U32.add(U32.mul(acc, 10), dd)), Nat.mul(uadd_k(U32.mul(acc,
    10), dd), pow2u(32n, uu))), Nat.add(U32.to_nat(U32.mul(acc, 10)), U32.to_nat(dd)), u_add(uu, U32.mul(acc, 10),
    dd)), Equal.trans(Nat, Nat.add(Nat.add(U32.to_nat(U32.mul(acc, 10)), U32.to_nat(dd)), Nat.mul(umk(acc), pow2u(32n,
    uu))), Nat.add(Nat.add(U32.to_nat(U32.mul(acc, 10)), Nat.mul(umk(acc), pow2u(32n, uu))), U32.to_nat(dd)),
    Nat.add(Nat.mul(U32.to_nat(acc), 10n), U32.to_nat(dd)), Equal.trans(Nat, Nat.add(Nat.add(U32.to_nat(U32.mul(acc,
    10)), U32.to_nat(dd)), Nat.mul(umk(acc), pow2u(32n, uu))), Nat.add(Nat.mul(umk(acc), pow2u(32n, uu)),
    Nat.add(U32.to_nat(U32.mul(acc, 10)), U32.to_nat(dd))), Nat.add(Nat.add(U32.to_nat(U32.mul(acc, 10)),
    Nat.mul(umk(acc), pow2u(32n, uu))), U32.to_nat(dd)), Equal.trans(Nat, Nat.add(Nat.add(U32.to_nat(U32.mul(acc, 10)),
    U32.to_nat(dd)), Nat.mul(umk(acc), pow2u(32n, uu))), Nat.add(Nat.add(U32.to_nat(U32.mul(acc, 10)), U32.to_nat(dd)),
    Nat.mul(umk(acc), pow2u(32n, uu))), Nat.add(Nat.mul(umk(acc), pow2u(32n, uu)), Nat.add(U32.to_nat(U32.mul(acc,
    10)), U32.to_nat(dd))), Equal.cong(Nat, Nat, z174 => Nat.add(z174, Nat.mul(umk(acc), pow2u(32n, uu))),
    Nat.add(U32.to_nat(U32.mul(acc, 10)), U32.to_nat(dd)), Nat.add(U32.to_nat(U32.mul(acc, 10)), U32.to_nat(dd)),
    {==}), Equal.trans(Nat, Nat.add(Nat.add(U32.to_nat(U32.mul(acc, 10)), U32.to_nat(dd)), Nat.mul(umk(acc), pow2u(32n,
    uu))), Nat.add(U32.to_nat(U32.mul(acc, 10)), Nat.add(U32.to_nat(dd), Nat.mul(umk(acc), pow2u(32n, uu)))),
    Nat.add(Nat.mul(umk(acc), pow2u(32n, uu)), Nat.add(U32.to_nat(U32.mul(acc, 10)), U32.to_nat(dd))),
    nat_add_assoc(U32.to_nat(U32.mul(acc, 10)), U32.to_nat(dd), Nat.mul(umk(acc), pow2u(32n, uu))), Equal.trans(Nat,
    Nat.add(U32.to_nat(U32.mul(acc, 10)), Nat.add(U32.to_nat(dd), Nat.mul(umk(acc), pow2u(32n, uu)))),
    Nat.add(U32.to_nat(U32.mul(acc, 10)), Nat.add(Nat.mul(umk(acc), pow2u(32n, uu)), U32.to_nat(dd))),
    Nat.add(Nat.mul(umk(acc), pow2u(32n, uu)), Nat.add(U32.to_nat(U32.mul(acc, 10)), U32.to_nat(dd))), Equal.cong(Nat,
    Nat, z175 => Nat.add(U32.to_nat(U32.mul(acc, 10)), z175), Nat.add(U32.to_nat(dd), Nat.mul(umk(acc), pow2u(32n,
    uu))), Nat.add(Nat.mul(umk(acc), pow2u(32n, uu)), U32.to_nat(dd)), nat_add_comm(U32.to_nat(dd), Nat.mul(umk(acc),
    pow2u(32n, uu)))), nat_add_lcomm(U32.to_nat(U32.mul(acc, 10)), Nat.mul(umk(acc), pow2u(32n, uu)),
    U32.to_nat(dd))))), Equal.sym(Nat, Nat.add(Nat.add(U32.to_nat(U32.mul(acc, 10)), Nat.mul(umk(acc), pow2u(32n,
    uu))), U32.to_nat(dd)), Nat.add(Nat.mul(umk(acc), pow2u(32n, uu)), Nat.add(U32.to_nat(U32.mul(acc, 10)),
    U32.to_nat(dd))), Equal.trans(Nat, Nat.add(Nat.add(U32.to_nat(U32.mul(acc, 10)), Nat.mul(umk(acc), pow2u(32n,
    uu))), U32.to_nat(dd)), Nat.add(Nat.add(Nat.mul(umk(acc), pow2u(32n, uu)), U32.to_nat(U32.mul(acc, 10))),
    U32.to_nat(dd)), Nat.add(Nat.mul(umk(acc), pow2u(32n, uu)), Nat.add(U32.to_nat(U32.mul(acc, 10)), U32.to_nat(dd))),
    Equal.cong(Nat, Nat, z176 => Nat.add(z176, U32.to_nat(dd)), Nat.add(U32.to_nat(U32.mul(acc, 10)), Nat.mul(umk(acc),
    pow2u(32n, uu))), Nat.add(Nat.mul(umk(acc), pow2u(32n, uu)), U32.to_nat(U32.mul(acc, 10))),
    nat_add_comm(U32.to_nat(U32.mul(acc, 10)), Nat.mul(umk(acc), pow2u(32n, uu)))), nat_add_assoc(Nat.mul(umk(acc),
    pow2u(32n, uu)), U32.to_nat(U32.mul(acc, 10)), U32.to_nat(dd))))), Equal.cong(Nat, Nat, z177 => Nat.add(z177,
    U32.to_nat(dd)), Nat.add(U32.to_nat(U32.mul(acc, 10)), Nat.mul(umk(acc), pow2u(32n, uu))), Nat.mul(U32.to_nat(acc),
    10n), u_mul10(uu, acc))))))

# a step that stays below 2^32 is exact
