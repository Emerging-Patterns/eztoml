# how a grammar claim about a word is matched against its characters and
# digits
import Base
import ../../src/eq.bend as Eq
import ../../laws/defs/AbnfGrammar.bend as D1
import ../../laws/defs/BareValueGrammar.bend as D2
import ./DigitsWrittenBack.bend as M1
import ./FreshNamesInRows.bend as M2
import ./PrefixAndTake.bend as M3

# The word rules are disjoint. A boolean is one of two fixed words. An
# integer or a float's integer part holds only DIGITs and underscores after
# its sign, and a date-time has a - or a : after its first DIGITs, which such
# a word cannot have; the prefixes 0x, 0o and 0b, a sign, and the letters of
# inf and nan are each ruled out by the character where they stand.

# an or that holds: a claim from either half that holds is a claim
def gp.or(
  -P: Type,
  aa: Bool,
  bb: Bool,
  +h: {Bool.or(aa, bb) == True{} : Bool},
  ka: {aa == True{} : Bool} -> P,
  kb: {bb == True{} : Bool} -> P
) -> P:
  match aa:
    case True{}:
      ka({==})
    case False{}:
      kb(h)

# a claim of what a word is equal to is a claim of the word
def gp.subst(
  -P: List<&2, Char> -> Type,
  +aa: List<&2, Char>,
  +bb: List<&2, Char>,
  ee: {aa == bb : List<&2, Char>},
  pb: P(bb)
) -> P(aa):
  %Equal.sym(List<&2, Char>, aa, bb, ee) : P(_)
  pb

# a claim of the character a word starts with, when it is known
def gp.head(
  -P: List<&2, Char> -> Type,
  +hh: Char,
  +kk: Char,
  +tt: List<&2, Char>,
  ee: {hh == kk : Char},
  pk: P(kk <> tt)
) -> P(hh <> tt):
  %Equal.sym(Char, hh, kk, ee) : P(_ <> tt)
  pk

# a word a %x string matched is that string's characters
def gp.chars(
  cs: List<&2, Char>,
  ss: String,
  +h: {D2.abnf.chars_are(cs, ss) == True{} : Bool}
) -> {cs == String.to_list(ss) : List<&2, Char>}:
  match cs ss:
    case Nil{} SNil{}:
      {==}
    case +hh <> +tt SCon{+h2, +t2}:
      +e1 = {Eq.char_eq_true(hh, h2, Eq.and.left(Char.is_eq(hh, h2), D2.abnf.chars_are(tt, t2), h))
        : {hh == h2 : Char}}
      Equal.trans(List<&2, Char>, hh <> tt, h2 <> tt, h2 <> String.to_list(t2),
        Equal.cong(Char, List<&2, Char>, zz => zz <> tt, hh, h2, e1),
        Equal.cong(List<&2, Char>, List<&2, Char>, zz => h2 <> zz, tt, String.to_list(t2),
          gp.chars(tt, t2, Eq.and.right(Char.is_eq(hh, h2), D2.abnf.chars_are(tt, t2), h))))
    case Nil{} SCon{+xx, +yy}:
      Eq.bit.absurd(&2, {[] == String.to_list(SCon{xx, yy}) : List<&2, Char>}, h)
    case +xx <> +yy SNil{}:
      Eq.bit.absurd(&2, {xx <> yy == String.to_list(SNil{}) : List<&2, Char>}, h)

# a claim of true and of false is a claim of every boolean word
def gp.bool(
  -P: List<&2, Char> -> Type,
  +cs: List<&2, Char>,
  +h: {D2.abnf.boolean(cs) == True{} : Bool},
  pt: P(String.to_list("true")),
  pf: P(String.to_list("false"))
) -> P(cs):
  gp.or(P(cs), D2.abnf.true(cs), D2.abnf.false(cs), h,
    ht => gp.subst(P, cs, String.to_list("true"), gp.chars(cs, "true", ht), pt),
    hf => gp.subst(P, cs, String.to_list("false"), gp.chars(cs, "false", hf), pf))

# a character of a dec-int's digits: a DIGIT or an underscore
def gp.dc(+cc: Char) -> Bool:
  Bool.or(D1.abnf.DIGIT(cc), D1.abnf.underscore(cc))

# every character of a word is one
def gp.decs(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      True{}
    case hh <> tt:
      Bool.and(gp.dc(hh), gp.decs(tt))

# a claim of the underscore is a claim of what an underscore test passed
def gp.us.elim(
  -P: Char -> Type,
  +cc: Char,
  +h: {D1.abnf.underscore(cc) == True{} : Bool},
  pu: P('_')
) -> P(cc):
  %Equal.sym(Char, cc, '_', M1.gs.us(cc, h)) : P(_)
  pu

# a claim of each digit and of the underscore is a claim of every such
# character
def gp.dc.elim(
  -P: Char -> Type,
  +cc: Char,
  +h: {gp.dc(cc) == True{} : Bool},
  p0: P('0'),
  p1: P('1'),
  p2: P('2'),
  p3: P('3'),
  p4: P('4'),
  p5: P('5'),
  p6: P('6'),
  p7: P('7'),
  p8: P('8'),
  p9: P('9'),
  pu: P('_')
) -> P(cc):
  gp.or(P(cc), D1.abnf.DIGIT(cc), D1.abnf.underscore(cc), h,
    hd => M2.dg.elim(P, cc, M1.gs.dig(cc, hd), p0, p1, p2, p3, p4, p5, p6, p7, p8, p9),
    hu => gp.us.elim(P, cc, hu, pu))

# a DIGIT is such a character
def gp.dc.digit(+cc: Char, +h: {D1.abnf.DIGIT(cc) == True{} : Bool}) -> {gp.dc(cc) == True{} : Bool}:
  %Equal.sym(Bool, D1.abnf.DIGIT(cc), True{}, h) : {Bool.or(_, D1.abnf.underscore(cc)) == True{} : Bool}
  {==}

# so is a digit
def gp.dc.is_digit(+cc: Char, +h: {Char.is_digit(cc) == True{} : Bool}) -> {gp.dc(cc) == True{} : Bool}:
  M2.dg.elim(zz => {gp.dc(zz) == True{} : Bool}, cc, h, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# the repetition *( DIGIT / underscore DIGIT ) holds only such characters
def gp.rep.decs(cs: List<&2, Char>, +h: {D1.abnf.dec_rep(cs) == True{} : Bool}) -> {gp.decs(cs) == True{} : Bool}:
  match cs:
    case []:
      {==}
    case +hh <> tt:
      match tt:
        case []:
          M3.and.tt(gp.dc(hh), True{}, gp.dc.digit(hh, h), {==})
        case +h2 <> +t2:
          M1.gs.rep.two(zs => {gp.decs(zs) == True{} : Bool}, hh, h2, t2, D1.abnf.DIGIT(hh), {==}, h,
            hx => hr => M3.and.tt(gp.dc(hh), gp.decs(h2 <> t2), gp.dc.is_digit(hh, hx), gp.rep.decs(h2 <> t2, hr)),
            hx => hr => M3.and.tt(gp.dc(h2), gp.decs(t2), gp.dc.is_digit(h2, hx), gp.rep.decs(t2, hr)))

# a digit1-9 is a DIGIT
def gp.d19(+cc: Char, +h: {D1.abnf.digit1_9(cc) == True{} : Bool}) -> {D1.abnf.DIGIT(cc) == True{} : Bool}:
  M2.dg.elim(zz => {D1.abnf.DIGIT(zz) == True{} : Bool}, cc, M1.gs.d19(cc, h),
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# a DIGIT alone holds only such characters
def gp.one.decs(
  +hh: Char,
  tt: List<&2, Char>,
  +ha: {Bool.and(D1.abnf.DIGIT(hh), List.is_empty(&2, Char, tt)) == True{} : Bool}
) -> {gp.decs(hh <> tt) == True{} : Bool}:
  match tt:
    case []:
      M3.and.tt(gp.dc(hh), True{}, gp.dc.digit(hh, Eq.and.left(D1.abnf.DIGIT(hh), True{}, ha)), {==})
    case +xx <> +yy:
      Eq.bit.absurd(&2, {gp.decs(hh <> xx <> yy) == True{} : Bool},
        Eq.and.right(D1.abnf.DIGIT(hh), False{}, ha))

# a digit1-9 then one or more of the repetition
def gp.many.decs(
  +hh: Char,
  tt: List<&2, Char>,
  +hb: {Bool.and(D1.abnf.digit1_9(hh), D1.abnf.dec_rep1(tt)) == True{} : Bool}
) -> {gp.decs(hh <> tt) == True{} : Bool}:
  match tt:
    case []:
      Eq.bit.absurd(&2, {gp.decs([hh]) == True{} : Bool}, Eq.and.right(D1.abnf.digit1_9(hh), False{}, hb))
    case +xx <> +yy:
      M3.and.tt(gp.dc(hh), gp.decs(xx <> yy),
        gp.dc.digit(hh, gp.d19(hh, Eq.and.left(D1.abnf.digit1_9(hh), D1.abnf.dec_rep(xx <> yy), hb))),
        gp.rep.decs(xx <> yy, Eq.and.right(D1.abnf.digit1_9(hh), D1.abnf.dec_rep(xx <> yy), hb)))

# an unsigned-dec-int holds only such characters
def gp.udi.decs(
  cs: List<&2, Char>,
  +h: {D1.abnf.unsigned_dec_int(cs) == True{} : Bool}
) -> {gp.decs(cs) == True{} : Bool}:
  match cs:
    case []:
      Eq.bit.absurd(&2, {gp.decs([]) == True{} : Bool}, h)
    case +hh <> +tt:
      gp.or({gp.decs(hh <> tt) == True{} : Bool}, Bool.and(D1.abnf.DIGIT(hh), List.is_empty(&2, Char, tt)),
        Bool.and(D1.abnf.digit1_9(hh), D1.abnf.dec_rep1(tt)), h,
        ha => gp.one.decs(hh, tt, ha), hb => gp.many.decs(hh, tt, hb))

# a prefixed integer's word, taken apart: a claim of each word that starts
# with 0 and the prefix letter ll is a claim of it
def gp.pre.case(
  -P: List<&2, Char> -> Type,
  cs: List<&2, Char>,
  +ll: U32,
  +rx: D1.ARadix,
  +h: {D1.abnf.prefixed(cs, ll, rx) == True{} : Bool},
  kk: @c2: Char -> @rest: List<&2, Char> -> P('0' <> Chr{ll} <> c2 <> rest)
) -> P(cs):
  match cs:
    case []:
      Eq.bit.absurd(&1, P([]), h)
    case +c0 <> t0:
      match t0:
        case []:
          Eq.bit.absurd(&1, P([c0]), h)
        case +c1 <> t1:
          match t1:
            case []:
              Eq.bit.absurd(&1, P([c0, c1]), h)
            case +c2 <> +rest:
              +hr = {Bool.and(D1.abnf.cp(c1, ll), Bool.and(D1.abnf.radix_digit(rx, c2),
                D1.abnf.radix_rep(rest, rx))) : Bool}
              +e0 = {M1.gp.cp(c0, 48, Eq.and.left(D1.abnf.cp(c0, 48), hr, h)) : {c0 == Chr{48} : Char}}
              +e1 = {M1.gp.cp(c1, ll, Eq.and.left(D1.abnf.cp(c1, ll), Bool.and(D1.abnf.radix_digit(rx, c2),
                D1.abnf.radix_rep(rest, rx)), Eq.and.right(D1.abnf.cp(c0, 48), hr, h))) : {c1 == Chr{ll} : Char}}
              gp.head(P, c0, Chr{48}, c1 <> c2 <> rest, e0,
                gp.head(zs => P(Chr{48} <> zs), c1, Chr{ll}, c2 <> rest, e1, kk(c2, rest)))
