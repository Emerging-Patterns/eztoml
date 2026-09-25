# eztoml/eq: the Base facts a proof needs and Base does not state. A value
# equals itself: Bend compares strings structurally, and every lookup asks
# whether a key it just wrote is the key it is looking for, so the proofs
# need that answer to be yes rather than to assume it.
import Base

# LAW: a bit compares equal to itself
law bool_cmp_self:
  for +b: Bool
  {Bool.cmp(b, b) == EQ{} : Cmp}

# the two bits, each compared with itself
def bool_cmp_self(b):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

# LAW: a word compares equal to itself
law word_cmp_self:
  for n: Nat
  for +w: Word(n)
  {Word.cmp(n, w, w) == EQ{} : Cmp}

# by induction on the width: a word of no bits and a bit carried over one
def word_cmp_self(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          Equal.trans(Cmp, Word.cmp.fin(b, b, Word.cmp(p, t, t)),
            Word.cmp.fin(b, b, EQ{}), EQ{},
            Equal.cong(Cmp, Cmp, c => Word.cmp.fin(b, b, c),
              Word.cmp(p, t, t), EQ{}, word_cmp_self(p, t)),
            bool_cmp_self(b))

# LAW: a number compares equal to itself
law u32_cmp_self:
  for +u: U32
  {U32.cmp(u, u) == EQ{} : Cmp}

# a number is a word of thirty-two bits, so the word's law answers for it
def u32_cmp_self(u):
  match u:
    case U32{+w}:
      word_cmp_self(32n, w)

# LAW: a char compares equal to itself
law char_cmp_self:
  for +c: Char
  {Char.cmp(c, c) == ((c, c), EQ{}) : (Char & Char) & Cmp}

# a char is a code point, and the pair it is compared inside rides along
def char_cmp_self(c):
  match c:
    case Chr{+x}:
      Equal.cong(Cmp, (Char & Char) & Cmp, r => ((Chr{x}, Chr{x}), r),
        U32.cmp(x, x), EQ{}, u32_cmp_self(x))

# LAW: a string compares equal to itself
law string_cmp_self:
  for +s: String
  {String.cmp(s, s) == ((s, s), EQ{}) : (String & String) & Cmp}

# by induction on the string: the head's law and the tail's, composed the
# way String.cmp composes them
def string_cmp_self(s):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.trans((String & String) & Cmp,
        String.cmp.fin(t, t, Char.cmp(h, h)),
        String.cmp.rec(h, h, String.cmp(t, t)),
        ((SCon{h, t}, SCon{h, t}), EQ{}),
        Equal.cong((Char & Char) & Cmp, (String & String) & Cmp,
          hc => String.cmp.fin(t, t, hc), Char.cmp(h, h), ((h, h), EQ{}),
          char_cmp_self(h)),
        Equal.cong((String & String) & Cmp, (String & String) & Cmp,
          r => String.cmp.rec(h, h, r), String.cmp(t, t), ((t, t), EQ{}),
          string_cmp_self(t)))

# LAW: a string equals itself. Every lookup in this project turns on it.
law string_eq_self:
  for +s: String
  {String.eq(s, s) == True{} : Bool}

# equality is the comparison read as a bit, so the comparison's law answers
def string_eq_self(s):
  Equal.cong((String & String) & Cmp, Bool, r => String.eq.fin(r),
    String.cmp(s, s), ((s, s), EQ{}), string_cmp_self(s))

# LAW: a char equals itself
law char_eq_self:
  for +c: Char
  {Char.is_eq(c, c) == True{} : Bool}

# and the same for a char
def char_eq_self(c):
  match c:
    case Chr{+x}:
      Equal.cong(Cmp, Bool, r => Cmp.is_eq(r), U32.cmp(x, x), EQ{},
        u32_cmp_self(x))

# A bit is one thing or the other, never both, so an equation between the two
# holds anything at all. Every proof that lifts a computed condition into a
# parameter reaches an arm the hypothesis has ruled out, and this is how that
# arm is closed. It belongs here, beside the other Base facts Base does not
# state.

# the type that is empty exactly where a bit is True
def bit.emp(bb: Bool) -> Type:
  match bb:
    case False{}:
      Unit
    case True{}:
      Empty

def bit.clash(ee: {False{} == True{} : Bool}) -> Empty:
  %ee : bit.emp(_)
  Unit{}

def bit.gone(a, -A: Kind(a), ee: Empty) -> A:
  match ee:

def bit.absurd(a, -A: Kind(a), ee: {False{} == True{} : Bool}) -> A:
  bit.gone(a, A, bit.clash(ee))

# and the same read the other way round
def bit.emp2(bb: Bool) -> Type:
  match bb:
    case False{}:
      Empty
    case True{}:
      Unit

def bit.clash2(ee: {True{} == False{} : Bool}) -> Empty:
  %ee : bit.emp2(_)
  Unit{}

def bit.absurd2(a, -A: Kind(a), ee: {True{} == False{} : Bool}) -> A:
  bit.gone(a, A, bit.clash2(ee))

# LAW: the left half of an `and` that answered True
law and.left:
  for u: Bool
  for v: Bool
  for e: {Bool.and(u, v) == True{} : Bool}
  {u == True{} : Bool}

def and.left(u, _v, e):
  match u:
    case True{}:
      {==}
    case False{}:
      e

# LAW: the right half of an `and` that answered True
law and.right:
  for u: Bool
  for v: Bool
  for e: {Bool.and(u, v) == True{} : Bool}
  {v == True{} : Bool}

def and.right(u, v, e):
  match u:
    case True{}:
      e
    case False{}:
      bit.absurd(&2, {v == True{} : Bool}, e)

# LAW: what a negation that answered True was told
law not.true:
  for u: Bool
  for e: {Bool.not(u) == True{} : Bool}
  {u == False{} : Bool}

def not.true(u, e):
  match u:
    case True{}:
      bit.absurd(&2, {True{} == False{} : Bool}, e)
    case False{}:
      {==}

# LAW: every string starts with the empty string
law starts_nil:
  for s: String
  {String.starts_with(s, "") == True{} : Bool}

# the prefix runs out first whatever the string is, so both arms answer True
def starts_nil(s):
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      {==}

# LAW: one string appended to another leaves the first a prefix of the whole
law starts_append:
  for +a: String
  for b: String
  {String.starts_with(String.append(a, b), a) == True{} : Bool}

# by induction on the prefix, with each character compared against itself
def starts_append(a, b):
  match a:
    case SNil{}:
      starts_nil(b)
    case SCon{+h, +t}:
      Equal.trans(Bool,
        String.starts_with.if(String.append(t, b), t, Char.is_eq(h, h)),
        String.starts_with.if(String.append(t, b), t, True{}),
        True{},
        Equal.cong(Bool, Bool,
          x => String.starts_with.if(String.append(t, b), t, x),
          Char.is_eq(h, h), True{}, char_eq_self(h)),
        starts_append(t, b))

# LAW: nothing appended to a string leaves the string.
law append_nil:
  for s: String
  {String.append(s, SNil{}) == s : String}

# by induction on the string, with each character carried over the tail's law
def append_nil(s):
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      Equal.cong(String, String, x => SCon{h, x},
        String.append(t, SNil{}), t, append_nil(t))

# LAW: where the brackets fall in a run of appends does not change the run.
# This is what lets the chunk loop drop its accumulator: appending each chunk
# onto what came before it and appending each chunk onto what comes after it
# give the same string, and only the second is linear in the body.
law append_assoc:
  for a: String
  for b: String
  for c: String
  {String.append(String.append(a, b), c)
    == String.append(a, String.append(b, c)) : String}

# by induction on the left string, which is the one both runs copy
def append_assoc(a, b, c):
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      Equal.cong(String, String, x => SCon{h, x},
        String.append(String.append(t, b), c),
        String.append(t, String.append(b, c)),
        append_assoc(t, b, c))

# LAW: which of two bits an `or` reads first does not change its answer
law or_comm:
  for a: Bool
  for b: Bool
  {Bool.or(a, b) == Bool.or(b, a) : Bool}

# the four pairs of bits, each answered by computing both sides
def or_comm(a, b):
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

# Counting. A U32 counts down to zero one subtraction at a time, and a proof
# about a walk that counts that way reads the count as a Nat: zero is 0n, and
# a count that is not zero is one more than the count less one.

# the type that is empty exactly where a Nat is a successor
def nat.emp(nn: Nat) -> Type:
  match nn:
    case 0n:
      Unit
    case 1n+_p:
      Empty

# zero is no successor
def nat.clash(-kk: Nat, ee: {0n == 1n+kk : Nat}) -> Empty:
  %ee : nat.emp(_)
  Unit{}

# and the same read the other way round
def nat.clash2(-kk: Nat, ee: {1n+kk == 0n : Nat}) -> Empty:
  nat.clash(kk, Equal.sym(Nat, 1n+kk, 0n, ee))

# the Nat one less, and zero for zero
def nat.pred(nn: Nat) -> Nat:
  match nn:
    case 0n:
      0n
    case 1n+pp:
      pp

# LAW: two successors that are equal were one more than equal Nats
law succ_inj:
  for a: Nat
  for b: Nat
  for e: {1n+a == 1n+b : Nat}
  {a == b : Nat}

# the predecessor of each side
def succ_inj(a, b, e):
  Equal.cong(Nat, Nat, x => nat.pred(x), 1n+a, 1n+b, e)

# the type that is empty exactly where a comparison answered EQ
def cmp.emp(ans: Cmp) -> Type:
  match ans:
    case LT{}:
      Unit
    case EQ{}:
      Empty
    case GT{}:
      Unit

# LT is not EQ
def cmp.lt(eq: {LT{} == EQ{} : Cmp}) -> Empty:
  %eq : cmp.emp(_)
  Unit{}

# GT is not EQ
def cmp.gt(eq: {GT{} == EQ{} : Cmp}) -> Empty:
  %eq : cmp.emp(_)
  Unit{}

# LAW: a comparison that reads as equal is EQ
law cmp_is_eq:
  for c: Cmp
  for e: {Cmp.is_eq(c) == True{} : Bool}
  {c == EQ{} : Cmp}

# the two other answers read as False
def cmp_is_eq(c, e):
  match c:
    case LT{}:
      bit.absurd(&2, {LT{} == EQ{} : Cmp}, e)
    case EQ{}:
      {==}
    case GT{}:
      bit.absurd(&2, {GT{} == EQ{} : Cmp}, e)

# LAW: two bits that compare equal are one bit
law bool_eq:
  for a: Bool
  for b: Bool
  for e: {Bool.cmp(a, b) == EQ{} : Cmp}
  {a == b : Bool}

# the two bits that differ compare LT or GT
def bool_eq(a, b, e):
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      bit.gone(&2, {False{} == True{} : Bool}, cmp.lt(e))
    case True{} False{}:
      bit.gone(&2, {True{} == False{} : Bool}, cmp.gt(e))
    case True{} True{}:
      {==}

# LAW: a word comparison that ends EQ had tails that compared EQ
law fin_tail:
  for ab: Bool
  for bb: Bool
  for t: Cmp
  for e: {Word.cmp.fin(ab, bb, t) == EQ{} : Cmp}
  {t == EQ{} : Cmp}

# an answer of LT or GT from the tails is the answer, never EQ
def fin_tail(_ab, _bb, t, e):
  match t:
    case LT{}:
      bit.gone(&2, {LT{} == EQ{} : Cmp}, cmp.lt(e))
    case EQ{}:
      {==}
    case GT{}:
      bit.gone(&2, {GT{} == EQ{} : Cmp}, cmp.gt(e))

# LAW: and heads that compared EQ
law fin_head:
  for ab: Bool
  for bb: Bool
  for t: Cmp
  for e: {Word.cmp.fin(ab, bb, t) == EQ{} : Cmp}
  {Bool.cmp(ab, bb) == EQ{} : Cmp}

# and an EQ from the tails leaves the heads to answer
def fin_head(ab, bb, t, e):
  match t:
    case LT{}:
      bit.gone(&2, {Bool.cmp(ab, bb) == EQ{} : Cmp}, cmp.lt(e))
    case EQ{}:
      e
    case GT{}:
      bit.gone(&2, {Bool.cmp(ab, bb) == EQ{} : Cmp}, cmp.gt(e))

# LAW: two words that compare equal are one word
law word_eq:
  for +n: Nat
  for a: Word(n)
  for b: Word(n)
  for +e: {Word.cmp(n, a, b) == EQ{} : Cmp}
  {a == b : Word(n)}

# by induction on the width: the heads by the bit law, then the tails
def word_eq(n, a, b, e):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          Equal.trans(Word(1n+p), WCon{ab, at}, WCon{bb, at}, WCon{bb, bt},
            Equal.cong(Bool, Word(1n+p), x => WCon{x, at}, ab, bb,
              bool_eq(ab, bb, fin_head(ab, bb, Word.cmp(p, at, bt), e))),
            Equal.cong(Word(p), Word(1n+p), y => WCon{bb, y}, at, bt,
              word_eq(p, at, bt, fin_tail(ab, bb, Word.cmp(p, at, bt), e))))

# twice a Nat is zero only for zero
def dbl.zero(xx: Nat, ee: {Nat.double(xx) == 0n : Nat}) -> {xx == 0n : Nat}:
  match xx:
    case 0n:
      {==}
    case 1n+pp:
      bit.gone(&2, {1n+pp == 0n : Nat}, nat.clash2(1n+Nat.double(pp), ee))

# LAW: a word that counts zero is the zero word
law word_nat_zero:
  for +n: Nat
  for +w: Word(n)
  for e: {Word.to_nat(n, w) == 0n : Nat}
  {w == Word.zero(n) : Word(n)}

# by induction on the width: a set low bit counts at least one, and a clear
# one leaves the rest to count zero
def word_nat_zero(n, w, e):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          Equal.cong(Word(p), Word(1n+p), y => WCon{False{}, y}, t,
            Word.zero(p),
            word_nat_zero(p, t, dbl.zero(Word.to_nat(p, t), e)))
        case WCon{True{}, +t}:
          bit.gone(&2, {WCon{True{}, t} == Word.zero(1n+p) : Word(1n+p)},
            nat.clash2(Nat.double(Word.to_nat(p, t)), e))

# LAW: taking all ones from a word with a carry in leaves the word. This is
# the rest of a subtraction once the borrow has been paid.
law sub_paid:
  for +n: Nat
  for +w: Word(n)
  {Word.adc(n, w, Word.zero(n), True{}, True{}) == w : Word(n)}

# by induction on the width: each bit comes through with the carry still set
def sub_paid(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          Equal.cong(Word(p), Word(1n+p), y => WCon{False{}, y},
            Word.adc(p, t, Word.zero(p), True{}, True{}), t, sub_paid(p, t))
        case WCon{True{}, +t}:
          Equal.cong(Word(p), Word(1n+p), y => WCon{True{}, y},
            Word.adc(p, t, Word.zero(p), True{}, True{}), t, sub_paid(p, t))

# one less than a word, as the subtraction computes it with a borrow owed
def word.dec(+nn: Nat, ww: Word(nn)) -> Word(nn):
  Word.adc(nn, ww, Word.zero(nn), True{}, False{})

# what the rest of a word promises once its width is known: one taken from a
# count of one more than j leaves j
def word_dec.Ih(-pp: Nat, -tt: Word(pp)) -> Type:
  @jj: Nat -> {Word.to_nat(pp, tt) == 1n+jj : Nat}
    -> {Word.to_nat(pp, word.dec(pp, tt)) == jj : Nat}

# the low bit was clear, so the borrow goes on to the rest: the rest counted
# at least one, and one less than it counts one less
def word_dec.low(
  -pp: Nat,
  -tt: Word(pp),
  xx: Nat,
  kk: Nat,
  ex: {Word.to_nat(pp, tt) == xx : Nat},
  ee: {Nat.double(xx) == 1n+kk : Nat},
  ih: word_dec.Ih(pp, tt)
) -> {1n+Nat.double(Word.to_nat(pp, word.dec(pp, tt))) == kk : Nat}:
  match xx:
    case 0n:
      bit.gone(&2,
        {1n+Nat.double(Word.to_nat(pp, word.dec(pp, tt))) == kk : Nat},
        nat.clash(kk, ee))
    case 1n+(+jj):
      Equal.trans(Nat, 1n+Nat.double(Word.to_nat(pp, word.dec(pp, tt))),
        1n+Nat.double(jj), kk,
        Equal.cong(Nat, Nat, x => 1n+Nat.double(x),
          Word.to_nat(pp, word.dec(pp, tt)), jj, ih(jj, ex)),
        succ_inj(1n+Nat.double(jj), kk, ee))

# LAW: a word that counts one more than k counts k once one is taken from it
law word_dec:
  for +n: Nat
  for +w: Word(n)
  for +k: Nat
  for e: {Word.to_nat(n, w) == 1n+k : Nat}
  {Word.to_nat(n, word.dec(n, w)) == k : Nat}

# by induction on the width: a set low bit is cleared and the borrow is paid,
# and a clear one is set and the borrow goes on to the rest
def word_dec(n, w, k, e):
  match n:
    case 0n:
      match w:
        case WNil{}:
          bit.gone(&2, {0n == k : Nat}, nat.clash(k, e))
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          word_dec.low(p, t, Word.to_nat(p, t), k, {==}, e,
            jj => ej => word_dec(p, t, jj, ej))
        case WCon{True{}, +t}:
          Equal.trans(Nat,
            Nat.double(Word.to_nat(p, Word.adc(p, t, Word.zero(p), True{},
              True{}))),
            Nat.double(Word.to_nat(p, t)), k,
            Equal.cong(Word(p), Nat, y => Nat.double(Word.to_nat(p, y)),
              Word.adc(p, t, Word.zero(p), True{}, True{}), t, sub_paid(p, t)),
            succ_inj(Nat.double(Word.to_nat(p, t)), k, e))

# a word that counts something counts one more than one less than it: it is
# not the zero word, since that compares equal to zero
def word_dec_nat.go(
  +nn: Nat,
  +ww: Word(nn),
  xx: Nat,
  +ex: {Word.to_nat(nn, ww) == xx : Nat},
  ne: {Cmp.is_eq(Word.cmp(nn, ww, Word.zero(nn))) == False{} : Bool}
) -> {Word.to_nat(nn, ww) == 1n+Word.to_nat(nn, word.dec(nn, ww)) : Nat}:
  match xx:
    case 0n:
      bit.absurd(&2,
        {Word.to_nat(nn, ww) == 1n+Word.to_nat(nn, word.dec(nn, ww)) : Nat},
        Equal.trans(Bool, False{},
          Cmp.is_eq(Word.cmp(nn, ww, Word.zero(nn))), True{},
          Equal.sym(Bool, Cmp.is_eq(Word.cmp(nn, ww, Word.zero(nn))), False{},
            ne),
          Equal.trans(Bool, Cmp.is_eq(Word.cmp(nn, ww, Word.zero(nn))),
            Cmp.is_eq(Word.cmp(nn, Word.zero(nn), Word.zero(nn))), True{},
            Equal.cong(Word(nn), Bool,
              y => Cmp.is_eq(Word.cmp(nn, y, Word.zero(nn))), ww,
              Word.zero(nn), word_nat_zero(nn, ww, ex)),
            Equal.cong(Cmp, Bool, c => Cmp.is_eq(c),
              Word.cmp(nn, Word.zero(nn), Word.zero(nn)), EQ{},
              word_cmp_self(nn, Word.zero(nn))))))
    case 1n+(+kk):
      Equal.trans(Nat, Word.to_nat(nn, ww), 1n+kk,
        1n+Word.to_nat(nn, word.dec(nn, ww)), ex,
        Equal.cong(Nat, Nat, x => 1n+x, kk,
          Word.to_nat(nn, word.dec(nn, ww)),
          Equal.sym(Nat, Word.to_nat(nn, word.dec(nn, ww)), kk,
            word_dec(nn, ww, kk, ex))))

# LAW: taking one from a U32 is the word one less, with the borrow owed from
# the first bit on
law sub_one:
  for +w: Word(32n)
  {U32.sub(U32{w}, 1) == U32{word.dec(32n, w)} : U32}

# the low bit decides the first step and the two agree after it
def sub_one(w):
  match w:
    case WCon{False{}, t}:
      {==}
    case WCon{True{}, t}:
      {==}

# LAW: a U32 that is zero counts zero
law u32_zero_nat:
  for +x: U32
  for e: {U32.is_zero(x) == True{} : Bool}
  {U32.to_nat(x) == 0n : Nat}

# a word that compares equal to the zero word is it
def u32_zero_nat(x, e):
  match x:
    case U32{+w}:
      Equal.cong(Word(32n), Nat, y => Word.to_nat(32n, y), w, Word.zero(32n),
        word_eq(32n, w, Word.zero(32n),
          cmp_is_eq(Word.cmp(32n, w, Word.zero(32n)), e)))

# LAW: a U32 that is not zero counts one more than itself less one
law u32_dec_nat:
  for +x: U32
  for e: {U32.is_zero(x) == False{} : Bool}
  {U32.to_nat(x) == 1n+U32.to_nat(U32.sub(x, 1)) : Nat}

# the word's law, with the subtraction read as the word one less
def u32_dec_nat(x, e):
  match x:
    case U32{+w}:
      Equal.trans(Nat, Word.to_nat(32n, w),
        1n+Word.to_nat(32n, word.dec(32n, w)),
        1n+U32.to_nat(U32.sub(U32{w}, 1)),
        word_dec_nat.go(32n, w, Word.to_nat(32n, w), {==}, e),
        Equal.cong(U32, Nat, u => 1n+U32.to_nat(u), U32{word.dec(32n, w)},
          U32.sub(U32{w}, 1),
          Equal.sym(U32, U32.sub(U32{w}, 1), U32{word.dec(32n, w)},
            sub_one(w))))

# LAW: the left half of an `or` that answered False
law or.false_left:
  for u: Bool
  for v: Bool
  for e: {Bool.or(u, v) == False{} : Bool}
  {u == False{} : Bool}

def or.false_left(u, _v, e):
  match u:
    case False{}:
      {==}
    case True{}:
      e

# LAW: the right half of an `or` that answered False
law or.false_right:
  for u: Bool
  for v: Bool
  for e: {Bool.or(u, v) == False{} : Bool}
  {v == False{} : Bool}

def or.false_right(u, v, e):
  match u:
    case False{}:
      e
    case True{}:
      bit.absurd2(&2, {v == False{} : Bool}, e)

# LAW: a string comparison read as a bit reads only the comparison, so the
# chars it rebuilt in front do not change it
law eq_fin_rec:
  for h1: Char
  for h2: Char
  for r: (String & String) & Cmp
  {String.eq.fin(String.cmp.rec(h1, h2, r)) == String.eq.fin(r) : Bool}

# the comparison, taken apart and put back together
def eq_fin_rec(_h1, _h2, r):
  match r:
    case (ts, c):
      match ts:
        case (t1, t2):
          {==}

# A test that answered True was given one thing twice. Base states no such
# fact, so a proof that follows the scanner past a comparison with a
# character it did not match needs these: two words that compare equal are
# one word by induction on the width, and two chars are two code points.
# They are ez's check/str.bend lemmas, restated here.

# LAW: two code points that compare equal are one char
law u32_eq:
  for xx: U32
  for yy: U32
  for ee: {U32.is_eq(xx, yy) == True{} : Bool}
  {Chr{xx} == Chr{yy} : Char}

# a code point is a word of thirty-two bits
def u32_eq(xx, yy, ee):
  match xx yy:
    case U32{+wx} U32{+wy}:
      Equal.cong(Word(32n), Char, w => Chr{U32{w}}, wx, wy,
        word_eq(32n, wx, wy, cmp_is_eq(Word.cmp(32n, wx, wy), ee)))

# LAW: two chars that compare equal are one char
law char_eq_true:
  for aa: Char
  for bb: Char
  for ee: {Char.is_eq(aa, bb) == True{} : Bool}
  {aa == bb : Char}

# a char is a code point
def char_eq_true(aa, bb, ee):
  match aa bb:
    case Chr{x} Chr{y}:
      u32_eq(x, y, ee)

# LAW: a char a test found equal to k passes a predicate only where k does.
# This is how a proof leaves a branch the scanner takes on one character: the
# character it tested for fails the predicate the law gave the character.
law refute_char:
  for cc: Char
  for kk: Char
  for pp: Char -> Bool
  for ee: {Char.is_eq(cc, kk) == True{} : Bool}
  for yes: {pp(cc) == True{} : Bool}
  for no: {pp(kk) == False{} : Bool}
  Empty

# the char is k, so the predicate's two answers are one answer
def refute_char(cc, kk, pp, ee, yes, no):
  bit.clash(Equal.trans(Bool, False{}, pp(kk), True{},
    Equal.sym(Bool, pp(kk), False{}, no),
    Equal.trans(Bool, pp(kk), pp(cc), True{},
      Equal.cong(Char, Bool, pp, kk, cc,
        Equal.sym(Char, cc, kk, char_eq_true(cc, kk, ee))),
      yes)))

# LAW: an `or` that answered False had a left half that answered False
law or.left_false:
  for u: Bool
  for v: Bool
  for e: {Bool.or(u, v) == False{} : Bool}
  {u == False{} : Bool}

def or.left_false(u, _v, e):
  match u:
    case True{}:
      bit.absurd2(&2, {True{} == False{} : Bool}, e)
    case False{}:
      {==}

# LAW: and a right half that answered False
law or.right_false:
  for u: Bool
  for v: Bool
  for e: {Bool.or(u, v) == False{} : Bool}
  {v == False{} : Bool}

def or.right_false(u, v, e):
  match u:
    case True{}:
      bit.absurd2(&2, {v == False{} : Bool}, e)
    case False{}:
      e

# WP0: Base-only lemmas the round-trip proofs share. The U32 arithmetic and
# word comparisons came here from PROOF.bend under their old names, and the
# controls U+0000 to U+001F and U+007F are taken one at a time over a motive,
# so a proof about every control gives one answer per control instead of
# copying the enumeration.

# LAW: adding a carry to a word and then taking one with the other carry as
# the borrow leaves the word
law inc.dec:
  for nn: Nat
  for ww: Word(nn)
  for cc: Bool
  {Word.adc(nn, Word.adc(nn, ww, Word.zero(nn), False{}, cc), Word.zero(nn), True{},
    Bool.not(cc)) == ww : Word(nn)}

# bit by bit: the carry and the borrow cancel at each bit
def inc.dec(nn, ww, cc):
  match nn:
    case 0n:
      match ww:
        case WNil{}:
          {==}
    case 1n+pp:
      match ww:
        case WCon{bb, +tt}:
          match bb cc:
            case False{} False{}:
              Equal.cong(Word(pp), Word(1n+pp), yy => WCon{False{}, yy},
                Word.adc(pp, Word.adc(pp, tt, Word.zero(pp), False{}, False{}), Word.zero(pp),
                  True{}, True{}), tt, inc.dec(pp, tt, False{}))
            case False{} True{}:
              Equal.cong(Word(pp), Word(1n+pp), yy => WCon{False{}, yy},
                Word.adc(pp, Word.adc(pp, tt, Word.zero(pp), False{}, False{}), Word.zero(pp),
                  True{}, True{}), tt, inc.dec(pp, tt, False{}))
            case True{} False{}:
              Equal.cong(Word(pp), Word(1n+pp), yy => WCon{True{}, yy},
                Word.adc(pp, Word.adc(pp, tt, Word.zero(pp), False{}, False{}), Word.zero(pp),
                  True{}, True{}), tt, inc.dec(pp, tt, False{}))
            case True{} True{}:
              Equal.cong(Word(pp), Word(1n+pp), yy => WCon{True{}, yy},
                Word.adc(pp, Word.adc(pp, tt, Word.zero(pp), False{}, True{}), Word.zero(pp),
                  True{}, False{}), tt, inc.dec(pp, tt, True{}))

# LAW: one taken from one more than a U32 is the U32
law sub.inc:
  for xx: U32
  {U32.sub(U32.add(xx, 1), 1) == xx : U32}

# the low bit decides the carry, and the word's law does the rest
def sub.inc(xx):
  match xx:
    case U32{ww}:
      match ww:
        case WCon{bb, +tt}:
          match bb:
            case False{}:
              Equal.cong(Word(31n), U32, yy => U32{WCon{False{}, yy}},
                Word.adc(31n, Word.adc(31n, tt, Word.zero(31n), False{}, False{}),
                  Word.zero(31n), True{}, True{}), tt, inc.dec(31n, tt, False{}))
            case True{}:
              Equal.cong(Word(31n), U32, yy => U32{WCon{True{}, yy}},
                Word.adc(31n, Word.adc(31n, tt, Word.zero(31n), False{}, True{}),
                  Word.zero(31n), True{}, False{}), tt, inc.dec(31n, tt, True{}))

# LAW: one more than a U32, when that is not zero, counts one more
law inc.nat:
  for +xx: U32
  for ez: {U32.is_zero(U32.add(xx, 1)) == False{} : Bool}
  {U32.to_nat(U32.add(xx, 1)) == 1n+U32.to_nat(xx) : Nat}

# the count of a U32 that is not zero, then sub.inc
def inc.nat(xx, ez):
  Equal.trans(Nat, U32.to_nat(U32.add(xx, 1)), 1n+U32.to_nat(U32.sub(U32.add(xx, 1), 1)),
    1n+U32.to_nat(xx),
    u32_dec_nat(U32.add(xx, 1), ez),
    Equal.cong(U32, Nat, uu => 1n+U32.to_nat(uu), U32.sub(U32.add(xx, 1), 1), xx, sub.inc(xx)))

# a word of n zero bits
def zw(nn: Nat) -> Word(nn):
  match nn:
    case 0n:
      WNil{}
    case 1n+pp:
      WCon{False{}, zw(pp)}

# LAW: against a 0 bit, a word is below exactly when the bits above are
law lt_fin_f:
  for cc: Cmp
  for aa: Bool
  {Cmp.is_lt(Word.cmp.fin(aa, False{}, cc)) == Cmp.is_lt(cc) : Bool}

# the three answers, and for EQ the two bits
def lt_fin_f(cc, aa):
  match cc:
    case LT{}:
      {==}
    case GT{}:
      {==}
    case EQ{}:
      match aa:
        case False{}:
          {==}
        case True{}:
          {==}

# LAW: a word is never below zero
law zw_nlt:
  for nn: Nat
  for ww: Word(nn)
  {Cmp.is_lt(Word.cmp(nn, ww, zw(nn))) == False{} : Bool}

# by induction on the width, each bit against a 0 bit
def zw_nlt(nn, ww):
  match nn:
    case 0n:
      match ww:
        case WNil{}:
          {==}
    case 1n+(+pp):
      match ww:
        case WCon{bb, +tt}:
          Equal.trans(Bool, Cmp.is_lt(Word.cmp.fin(bb, False{}, Word.cmp(pp, tt, zw(pp)))),
            Cmp.is_lt(Word.cmp(pp, tt, zw(pp))), False{},
            lt_fin_f(Word.cmp(pp, tt, zw(pp)), bb), zw_nlt(pp, tt))

# LAW: below a word whose low bit is 0, the bits above are below
law lt_up:
  for aa: Bool
  for +cc: Cmp
  for h_lt: {Cmp.is_lt(Word.cmp.fin(aa, False{}, cc)) == True{} : Bool}
  {Cmp.is_lt(cc) == True{} : Bool}

# lt_fin_f read the other way round
def lt_up(aa, cc, h_lt):
  Equal.trans(Bool, Cmp.is_lt(cc), Cmp.is_lt(Word.cmp.fin(aa, False{}, cc)), True{},
    Equal.sym(Bool, Cmp.is_lt(Word.cmp.fin(aa, False{}, cc)), Cmp.is_lt(cc), lt_fin_f(cc, aa)),
    h_lt)

# The controls. A code point below 32 has zeros above its five low bits, so
# the thirty-two of them are told apart by those bits; U+007F is one more.

# a code point below 32, by its five low bits
def ctl.low(b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool) -> U32:
  U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{False{}, zw(26n)}}}}}}}

# a claim for each code point below 32, as a function of its five low bits
def ctl.Low(PP: U32 -> Type) -> Type:
  @b0: Bool -> @b1: Bool -> @b2: Bool -> @b3: Bool -> @b4: Bool ->
    PP(ctl.low(b0, b1, b2, b3, b4))

# the bits above the fifth are zero and the fifth is 0, else the code point
# is not below 32
def ctl.at(
  -PP: U32 -> Type,
  cc: Cmp,
  b5: Bool,
  +b0: Bool,
  +b1: Bool,
  +b2: Bool,
  +b3: Bool,
  +b4: Bool,
  +hi: Word(26n),
  ec: {Word.cmp(26n, hi, zw(26n)) == cc : Cmp},
  h_lt: {Cmp.is_lt(Word.cmp.fin(b5, True{}, cc)) == True{} : Bool},
  low: ctl.Low(PP)
) -> PP(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, hi}}}}}}}):
  match cc:
    case LT{}:
      bit.gone(&1, PP(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, hi}}}}}}}),
        bit.clash2(Equal.trans(Bool, True{}, Cmp.is_lt(Word.cmp(26n, hi, zw(26n))), False{},
          Equal.sym(Bool, Cmp.is_lt(Word.cmp(26n, hi, zw(26n))), True{},
            Equal.cong(Cmp, Bool, xx => Cmp.is_lt(xx), Word.cmp(26n, hi, zw(26n)), LT{}, ec)),
          zw_nlt(26n, hi))))
    case GT{}:
      match b5:
        case False{}:
          bit.absurd(&1, PP(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{False{},
            hi}}}}}}}), h_lt)
        case True{}:
          bit.absurd(&1, PP(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{True{},
            hi}}}}}}}), h_lt)
    case EQ{}:
      match b5:
        case True{}:
          bit.absurd(&1, PP(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{True{},
            hi}}}}}}}), h_lt)
        case False{}:
          er = Equal.sym(Word(26n), hi, zw(26n), word_eq(26n, hi, zw(26n), ec))
          %er : PP(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{False{}, _}}}}}}})
          low(b0, b1, b2, b3, b4)

# a code point below 32 is one of the thirty-two
def ctl.lt(
  -PP: U32 -> Type,
  uu: U32,
  h_lt: {U32.is_lt(uu, 32) == True{} : Bool},
  low: ctl.Low(PP)
) -> PP(uu):
  match uu:
    case U32{WCon{+b0, WCon{+b1, WCon{+b2, WCon{+b3, WCon{+b4, WCon{+b5, +hi}}}}}}}:
      +c5 = Word.cmp.fin(b5, True{}, Word.cmp(26n, hi, zw(26n)))
      +c4 = Word.cmp.fin(b4, False{}, c5)
      +c3 = Word.cmp.fin(b3, False{}, c4)
      +c2 = Word.cmp.fin(b2, False{}, c3)
      +c1 = Word.cmp.fin(b1, False{}, c2)
      h5 = lt_up(b4, c5, lt_up(b3, c4, lt_up(b2, c3, lt_up(b1, c2, lt_up(b0, c1, h_lt)))))
      ctl.at(PP, Word.cmp(26n, hi, zw(26n)), b5, b0, b1, b2, b3, b4, hi, {==}, h5, low)

# a control is below U+0020 or is U+007F
def ctl.each(
  -PP: U32 -> Type,
  +uu: U32,
  lt: Bool,
  eq: Bool,
  elt: {U32.is_lt(uu, 32) == lt : Bool},
  eeq: {U32.is_eq(uu, 127) == eq : Bool},
  eo: {Bool.or(lt, eq) == True{} : Bool},
  low: ctl.Low(PP),
  del: PP(127)
) -> PP(uu):
  match lt:
    case True{}:
      ctl.lt(PP, uu, elt, low)
    case False{}:
      match eq:
        case True{}:
          eu = Equal.cong(Char, U32, cc => Char.to_u32(cc), Chr{uu}, Chr{127},
            u32_eq(uu, 127, eeq))
          %Equal.sym(U32, uu, 127, eu) : PP(_)
          del
        case False{}:
          bit.absurd(&1, PP(uu), eo)

# the answer for one code point below 32, picked by its five low bits
def ctl.pick(
  -PP: U32 -> Type,
  c00: PP(0),
  c01: PP(1),
  c02: PP(2),
  c03: PP(3),
  c04: PP(4),
  c05: PP(5),
  c06: PP(6),
  c07: PP(7),
  c08: PP(8),
  c09: PP(9),
  c10: PP(10),
  c11: PP(11),
  c12: PP(12),
  c13: PP(13),
  c14: PP(14),
  c15: PP(15),
  c16: PP(16),
  c17: PP(17),
  c18: PP(18),
  c19: PP(19),
  c20: PP(20),
  c21: PP(21),
  c22: PP(22),
  c23: PP(23),
  c24: PP(24),
  c25: PP(25),
  c26: PP(26),
  c27: PP(27),
  c28: PP(28),
  c29: PP(29),
  c30: PP(30),
  c31: PP(31),
  b0: Bool,
  b1: Bool,
  b2: Bool,
  b3: Bool,
  b4: Bool
) -> PP(ctl.low(b0, b1, b2, b3, b4)):
  match b0 b1 b2 b3 b4:
    case False{} False{} False{} False{} False{}:
      c00
    case True{} False{} False{} False{} False{}:
      c01
    case False{} True{} False{} False{} False{}:
      c02
    case True{} True{} False{} False{} False{}:
      c03
    case False{} False{} True{} False{} False{}:
      c04
    case True{} False{} True{} False{} False{}:
      c05
    case False{} True{} True{} False{} False{}:
      c06
    case True{} True{} True{} False{} False{}:
      c07
    case False{} False{} False{} True{} False{}:
      c08
    case True{} False{} False{} True{} False{}:
      c09
    case False{} True{} False{} True{} False{}:
      c10
    case True{} True{} False{} True{} False{}:
      c11
    case False{} False{} True{} True{} False{}:
      c12
    case True{} False{} True{} True{} False{}:
      c13
    case False{} True{} True{} True{} False{}:
      c14
    case True{} True{} True{} True{} False{}:
      c15
    case False{} False{} False{} False{} True{}:
      c16
    case True{} False{} False{} False{} True{}:
      c17
    case False{} True{} False{} False{} True{}:
      c18
    case True{} True{} False{} False{} True{}:
      c19
    case False{} False{} True{} False{} True{}:
      c20
    case True{} False{} True{} False{} True{}:
      c21
    case False{} True{} True{} False{} True{}:
      c22
    case True{} True{} True{} False{} True{}:
      c23
    case False{} False{} False{} True{} True{}:
      c24
    case True{} False{} False{} True{} True{}:
      c25
    case False{} True{} False{} True{} True{}:
      c26
    case True{} True{} False{} True{} True{}:
      c27
    case False{} False{} True{} True{} True{}:
      c28
    case True{} False{} True{} True{} True{}:
      c29
    case False{} True{} True{} True{} True{}:
      c30
    case True{} True{} True{} True{} True{}:
      c31

# LAW: a claim about a code point holds for every control once it holds for
# each of the thirty-three: U+0000 to U+001F and U+007F
law ctl.all:
  for -PP: U32 -> Type
  for +uu: U32
  for h_c: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == True{} : Bool}
  for c00: PP(0)
  for c01: PP(1)
  for c02: PP(2)
  for c03: PP(3)
  for c04: PP(4)
  for c05: PP(5)
  for c06: PP(6)
  for c07: PP(7)
  for c08: PP(8)
  for c09: PP(9)
  for c10: PP(10)
  for c11: PP(11)
  for c12: PP(12)
  for c13: PP(13)
  for c14: PP(14)
  for c15: PP(15)
  for c16: PP(16)
  for c17: PP(17)
  for c18: PP(18)
  for c19: PP(19)
  for c20: PP(20)
  for c21: PP(21)
  for c22: PP(22)
  for c23: PP(23)
  for c24: PP(24)
  for c25: PP(25)
  for c26: PP(26)
  for c27: PP(27)
  for c28: PP(28)
  for c29: PP(29)
  for c30: PP(30)
  for c31: PP(31)
  for c127: PP(127)
  PP(uu)

# split below 32 or U+007F, and below 32 pick the answer by the five low bits
def ctl.all(
  PP,
  uu,
  h_c,
  c00,
  c01,
  c02,
  c03,
  c04,
  c05,
  c06,
  c07,
  c08,
  c09,
  c10,
  c11,
  c12,
  c13,
  c14,
  c15,
  c16,
  c17,
  c18,
  c19,
  c20,
  c21,
  c22,
  c23,
  c24,
  c25,
  c26,
  c27,
  c28,
  c29,
  c30,
  c31,
  c127
):
  ctl.each(PP, uu, U32.is_lt(uu, 32), U32.is_eq(uu, 127), {==}, {==}, h_c,
    b0 => b1 => b2 => b3 => b4 => ctl.pick(PP,
      c00, c01, c02, c03, c04, c05, c06, c07,
      c08, c09, c10, c11, c12, c13, c14, c15,
      c16, c17, c18, c19, c20, c21, c22, c23,
      c24, c25, c26, c27, c28, c29, c30, c31,
      b0, b1, b2, b3, b4),
    c127)
