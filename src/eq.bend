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
