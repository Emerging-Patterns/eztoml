# the characters a number scan refuses, and why a failed scan stays failed
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/defs/AbnfGrammar.bend as D1
import ./DigitsWrittenBack.bend as M1
import ./FreshNamesInRows.bend as M2
import ./SpecialWordCompare.bend as M3

# WP-N1: the integer, float and boolean words, exact in both directions
# (docs/rfc/eztoml-grammar-proofs.md). The numeral scan is followed state by
# state. From each state the scan finishes as a float exactly when the rest of
# the word matches what toml.abnf's float rule asks for from the position
# that state stands for, and as an integer likewise: one Bool equation per
# state gives both the accept and the refuse direction. The routing lemmas
# show that a word the scan does not fail is sent to it, and the value
# lemmas that the scan's value is the one g.val says the word denotes.

# a digit is a DIGIT, whatever the character
def n1.dig(cc: Char) -> {Char.is_digit(cc) == D1.abnf.DIGIT(cc) : Bool}:
  match cc:
    case Chr{+cp}:
      {==}

# the character _ is an underscore, whatever the character
def n1.us(cc: Char) -> {Char.is_eq(cc, '_') == D1.abnf.underscore(cc) : Bool}:
  match cc:
    case Chr{+cp}:
      {==}

# an or with False on its right is its left
def n1.orf(aa: Bool) -> {Bool.or(aa, False{}) == aa : Bool}:
  match aa:
    case True{}:
      {==}
    case False{}:
      {==}

# a digit fits base ten
def n1.dok10(cc: Char, hc: {Char.is_digit(cc) == True{} : Bool}) -> {T.dig.ok(T.dig.val(cc), 10) == True{} : Bool}:
  M2.dg.elim(zz => {T.dig.ok(T.dig.val(zz), 10) == True{} : Bool}, cc, hc,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# a digit is no underscore
def n1.nous(cc: Char, hc: {Char.is_digit(cc) == True{} : Bool}) -> {Char.is_eq(cc, '_') == False{} : Bool}:
  M2.dg.elim(zz => {Char.is_eq(zz, '_') == False{} : Bool}, cc, hc,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# an or of a claim and False is the claim
def n1.orf.eq(
  +aa: Bool,
  +bb: Bool,
  ee: {aa == bb : Bool}
) -> {aa == Bool.or(bb, False{}) : Bool}:
  Equal.trans(Bool, aa, bb, Bool.or(bb, False{}), ee, Equal.sym(Bool, Bool.or(bb, False{}), bb, n1.orf(bb)))

# the scan after an exponent's e
def n1.se(+sg: T.Sign) -> T.Num:
  T.Num{T.NExp{}, sg, 10, [], False{}, False{}, ""}

# the character - is the minus of the grammar, whatever the character
def n1.minus(cc: Char) -> {Char.is_eq(cc, '-') == D1.abnf.minus(cc) : Bool}:
  match cc:
    case Chr{+cp}:
      {==}

# and + the plus
def n1.plus(cc: Char) -> {Char.is_eq(cc, '+') == D1.abnf.plus(cc) : Bool}:
  match cc:
    case Chr{+cp}:
      {==}

# the repetition after a digit is the repetition
def n1.rep.d(
  +cc: Char,
  xs: List<&2, Char>,
  +hc: {Char.is_digit(cc) == True{} : Bool}
) -> {D1.abnf.dec_rep(xs) == D1.abnf.dec_rep(cc <> xs) : Bool}:
  match xs:
    case []:
      Equal.trans(Bool, True{}, Char.is_digit(cc), D1.abnf.DIGIT(cc), Equal.sym(Bool, Char.is_digit(cc), True{}, hc),
        n1.dig(cc))
    case +h2 <> +t2:
      %Equal.trans(Bool, True{}, Char.is_digit(cc), D1.abnf.DIGIT(cc), Equal.sym(Bool, Char.is_digit(cc), True{},
        hc), n1.dig(cc)) : {D1.abnf.dec_rep(h2 <> t2) == Bool.or(Bool.and(_, D1.abnf.dec_rep(h2 <> t2)),
        Bool.and(D1.abnf.underscore(cc), Bool.and(D1.abnf.DIGIT(h2), D1.abnf.dec_rep(t2)))) : Bool}
      %Equal.trans(Bool, False{}, Char.is_eq(cc, '_'), D1.abnf.underscore(cc), Equal.sym(Bool, Char.is_eq(cc, '_'),
        False{}, n1.nous(cc, hc)), n1.us(cc)) : {D1.abnf.dec_rep(h2 <> t2) == Bool.or(D1.abnf.dec_rep(h2 <> t2),
        Bool.and(_, Bool.and(D1.abnf.DIGIT(h2), D1.abnf.dec_rep(t2)))) : Bool}
      n1.orf.eq(D1.abnf.dec_rep(h2 <> t2), D1.abnf.dec_rep(h2 <> t2), {==})

# the repetition after an underscore is a DIGIT and the repetition
def n1.rep.u(xs: List<&2, Char>) -> {D1.abnf.zero_prefixable_int(xs) == D1.abnf.dec_rep('_' <> xs) : Bool}:
  match xs:
    case []:
      {==}
    case +h2 <> +t2:
      {==}

# no repetition starts with a character that is no digit and no underscore
def n1.rep.n(
  +cc: Char,
  xs: List<&2, Char>,
  hd: {Char.is_digit(cc) == False{} : Bool},
  hu: {Char.is_eq(cc, '_') == False{} : Bool}
) -> {False{} == D1.abnf.dec_rep(cc <> xs) : Bool}:
  match xs:
    case []:
      Equal.trans(Bool, False{}, Char.is_digit(cc), D1.abnf.DIGIT(cc), Equal.sym(Bool, Char.is_digit(cc), False{},
        hd), n1.dig(cc))
    case +h2 <> +t2:
      %Equal.trans(Bool, False{}, Char.is_digit(cc), D1.abnf.DIGIT(cc), Equal.sym(Bool, Char.is_digit(cc), False{},
        hd), n1.dig(cc)) : {False{} == Bool.or(Bool.and(_, D1.abnf.dec_rep(h2 <> t2)),
        Bool.and(D1.abnf.underscore(cc), Bool.and(D1.abnf.DIGIT(h2), D1.abnf.dec_rep(t2)))) : Bool}
      %Equal.trans(Bool, False{}, Char.is_eq(cc, '_'), D1.abnf.underscore(cc), Equal.sym(Bool, Char.is_eq(cc, '_'),
        False{}, hu), n1.us(cc)) : {False{} == Bool.or(False{}, Bool.and(_, Bool.and(D1.abnf.DIGIT(h2),
        D1.abnf.dec_rep(t2)))) : Bool}
      {==}

# a zero-prefixable-int that starts with a digit is its repetition
def n1.zpi.d(
  +cc: Char,
  +xs: List<&2, Char>,
  hc: {Char.is_digit(cc) == True{} : Bool}
) -> {D1.abnf.dec_rep(xs) == D1.abnf.zero_prefixable_int(cc <> xs) : Bool}:
  %Equal.trans(Bool, True{}, Char.is_digit(cc), D1.abnf.DIGIT(cc), Equal.sym(Bool, Char.is_digit(cc), True{}, hc),
    n1.dig(cc)) : {D1.abnf.dec_rep(xs) == Bool.and(_, D1.abnf.dec_rep(xs)) : Bool}
  {==}

# a zero-prefixable-int that does not start with a digit is none
def n1.zpi.n(
  +cc: Char,
  +xs: List<&2, Char>,
  hc: {Char.is_digit(cc) == False{} : Bool}
) -> {False{} == D1.abnf.zero_prefixable_int(cc <> xs) : Bool}:
  %Equal.trans(Bool, False{}, Char.is_digit(cc), D1.abnf.DIGIT(cc), Equal.sym(Bool, Char.is_digit(cc), False{}, hc),
    n1.dig(cc)) : {False{} == Bool.and(_, D1.abnf.dec_rep(xs)) : Bool}
  {==}

# the scan after a decimal point
def n1.sf0(+sg: T.Sign) -> T.Num:
  T.Num{T.NFrac{}, sg, 10, [], False{}, False{}, ""}

# the scan after a digit of an integer part
def n1.sd(+sg: T.Sign, +ds: List<&2, U32>, +why: String) -> T.Num:
  T.Num{T.NDig{}, sg, 10, ds, False{}, True{}, why}

# The leading zero, the sign and the start.

# the scan after a leading zero
def n1.sz(+sg: T.Sign) -> T.Num:
  T.Num{T.NZero{}, sg, 10, [], False{}, True{}, ""}

# no digit is a digit1-9 unless it is one
def n1.d19.n.go(
  bb: Bool,
  +cc: Char,
  +eb: {D1.abnf.digit1_9(cc) == bb : Bool},
  hd: {Char.is_digit(cc) == False{} : Bool}
) -> {D1.abnf.digit1_9(cc) == False{} : Bool}:
  match bb:
    case True{}:
      Eq.bit.absurd2(&2, {D1.abnf.digit1_9(cc) == False{} : Bool}, Equal.trans(Bool, True{}, Char.is_digit(cc),
        False{}, Equal.sym(Bool, Char.is_digit(cc), True{}, M1.gs.d19(cc, eb)), hd))
    case False{}:
      eb

# a character that is no digit is no digit1-9
def n1.d19.n(+cc: Char, hd: {Char.is_digit(cc) == False{} : Bool}) -> {D1.abnf.digit1_9(cc) == False{} : Bool}:
  n1.d19.n.go(D1.abnf.digit1_9(cc), cc, {==}, hd)

# a digit that is not 0 is a digit1-9
def n1.d19.y(
  cc: Char,
  hd: {Char.is_digit(cc) == True{} : Bool},
  hz: {Char.is_eq(cc, '0') == False{} : Bool}
) -> {D1.abnf.digit1_9(cc) == True{} : Bool}:
  M2.dg.elim(zz => {Char.is_eq(zz, '0') == False{} : Bool} -> {D1.abnf.digit1_9(zz) == True{} : Bool}, cc, hd,
    ee => Eq.bit.absurd2(&2, {D1.abnf.digit1_9('0') == True{} : Bool}, ee),
    _e => {==}, _e => {==}, _e => {==}, _e => {==}, _e => {==}, _e => {==}, _e => {==}, _e => {==},
    _e => {==})(hz)

# the same, once the character's DIGIT and digit1-9 are known to be False
def n1.udi.n.go(
  xs: List<&2, Char>,
  +cc: Char,
  +e1: {False{} == D1.abnf.DIGIT(cc) : Bool},
  +e2: {False{} == D1.abnf.digit1_9(cc) : Bool}
) -> {False{} == D1.abnf.unsigned_dec_int(cc <> xs) : Bool}:
  match xs:
    case []:
      %e1 : {False{} == Bool.or(Bool.and(_, True{}), Bool.and(D1.abnf.digit1_9(cc), False{})) : Bool}
      %e2 : {False{} == Bool.or(False{}, Bool.and(_, False{})) : Bool}
      {==}
    case +h2 <> +t2:
      %e1 : {False{} == Bool.or(Bool.and(_, False{}), Bool.and(D1.abnf.digit1_9(cc), D1.abnf.dec_rep(h2 <> t2)))
        : Bool}
      %e2 : {False{} == Bool.or(False{}, Bool.and(_, D1.abnf.dec_rep(h2 <> t2))) : Bool}
      {==}

# no unsigned-dec-int starts with a character that is no digit
def n1.udi.n(
  +cc: Char,
  xs: List<&2, Char>,
  +hd: {Char.is_digit(cc) == False{} : Bool}
) -> {False{} == D1.abnf.unsigned_dec_int(cc <> xs) : Bool}:
  +e1 = {Equal.trans(Bool, False{}, Char.is_digit(cc), D1.abnf.DIGIT(cc), Equal.sym(Bool, Char.is_digit(cc), False{},
    hd), n1.dig(cc)) : {False{} == D1.abnf.DIGIT(cc) : Bool}}
  +e2 = {Equal.sym(Bool, D1.abnf.digit1_9(cc), False{}, n1.d19.n(cc, hd)) : {False{} == D1.abnf.digit1_9(cc)
    : Bool}}
  n1.udi.n.go(xs, cc, e1, e2)

# the same, once the character's DIGIT and digit1-9 are known to be True
def n1.udi.d.go(
  xs: List<&2, Char>,
  +cc: Char,
  +e1: {True{} == D1.abnf.DIGIT(cc) : Bool},
  +e2: {True{} == D1.abnf.digit1_9(cc) : Bool}
) -> {D1.abnf.dec_rep(xs) == D1.abnf.unsigned_dec_int(cc <> xs) : Bool}:
  match xs:
    case []:
      %e1 : {True{} == Bool.or(Bool.and(_, True{}), Bool.and(D1.abnf.digit1_9(cc), False{})) : Bool}
      {==}
    case +h2 <> +t2:
      %e1 : {D1.abnf.dec_rep(h2 <> t2) == Bool.or(Bool.and(_, False{}), Bool.and(D1.abnf.digit1_9(cc),
        D1.abnf.dec_rep(h2 <> t2))) : Bool}
      %e2 : {D1.abnf.dec_rep(h2 <> t2) == Bool.or(False{}, Bool.and(_, D1.abnf.dec_rep(h2 <> t2))) : Bool}
      {==}

# an unsigned-dec-int that starts with a digit1-9 is it and the repetition
def n1.udi.d(
  +cc: Char,
  xs: List<&2, Char>,
  +e9: {D1.abnf.digit1_9(cc) == True{} : Bool}
) -> {D1.abnf.dec_rep(xs) == D1.abnf.unsigned_dec_int(cc <> xs) : Bool}:
  +e1 = {Equal.trans(Bool, True{}, Char.is_digit(cc), D1.abnf.DIGIT(cc), Equal.sym(Bool, Char.is_digit(cc), True{},
    M1.gs.d19(cc, e9)), n1.dig(cc)) : {True{} == D1.abnf.DIGIT(cc) : Bool}}
  n1.udi.d.go(xs, cc, e1, Equal.sym(Bool, D1.abnf.digit1_9(cc), True{}, e9))

# the scan after a sign
def n1.ss(+sg: T.Sign) -> T.Num:
  T.Num{T.NSign{}, sg, 10, [], False{}, False{}, ""}

# the scan before an unsigned numeral's first character, with its sign
def n1.sl(+sg: T.Sign) -> T.Num:
  T.Num{T.NLead{}, sg, 10, [], False{}, False{}, ""}

# Routing. A colon anywhere, or a dash after the first character with no e or
# E in the word, fails the numeral scan: so a word the scan reads as a value
# is never sent to the datetime reader. Every state keeps a base that 99, the
# value dig.val gives any character that is no digit, does not fit.

# whether a scan has failed
def n1.isbad(st: T.Num) -> Bool:
  match st:
    case T.Num{nk, _sign, _base, _ds, _us, _saw, _why}:
      match nk:
        case T.NBad{}:
          True{}
        case _k:
          False{}

# a failed scan stays failed
def n1.isbad.go(
  rest: List<&2, Char>,
  +st: T.Num,
  hs: {n1.isbad(st) == True{} : Bool}
) -> {n1.isbad(T.num.go(rest, st)) == True{} : Bool}:
  match rest:
    case []:
      hs
    case +hh <> tt:
      match st:
        case T.Num{nk, +sg, +base, +ds, +us, +saw, +why}:
          match nk:
            case T.NBad{}:
              n1.isbad.go(tt, T.Num{T.NBad{}, sg, base, ds, us, saw, why}, {==})
            case T.NLead{}:
              Eq.bit.absurd(&2, {n1.isbad(T.num.go(hh <> tt, T.Num{T.NLead{}, sg, base, ds, us, saw, why})) == True{}
                : Bool}, hs)
            case T.NSign{}:
              Eq.bit.absurd(&2, {n1.isbad(T.num.go(hh <> tt, T.Num{T.NSign{}, sg, base, ds, us, saw, why})) == True{}
                : Bool}, hs)
            case T.NZero{}:
              Eq.bit.absurd(&2, {n1.isbad(T.num.go(hh <> tt, T.Num{T.NZero{}, sg, base, ds, us, saw, why})) == True{}
                : Bool}, hs)
            case T.NDig{}:
              Eq.bit.absurd(&2, {n1.isbad(T.num.go(hh <> tt, T.Num{T.NDig{}, sg, base, ds, us, saw, why})) == True{}
                : Bool}, hs)
            case T.NBase{}:
              Eq.bit.absurd(&2, {n1.isbad(T.num.go(hh <> tt, T.Num{T.NBase{}, sg, base, ds, us, saw, why})) == True{}
                : Bool}, hs)
            case T.NFrac{}:
              Eq.bit.absurd(&2, {n1.isbad(T.num.go(hh <> tt, T.Num{T.NFrac{}, sg, base, ds, us, saw, why})) == True{}
                : Bool}, hs)
            case T.NExp{}:
              Eq.bit.absurd(&2, {n1.isbad(T.num.go(hh <> tt, T.Num{T.NExp{}, sg, base, ds, us, saw, why})) == True{}
                : Bool}, hs)
            case T.NEDig{}:
              Eq.bit.absurd(&2, {n1.isbad(T.num.go(hh <> tt, T.Num{T.NEDig{}, sg, base, ds, us, saw, why})) == True{}
                : Bool}, hs)

# whether a scan's base leaves out 99: the value dig.val gives any character
# that is no digit of any base
def n1.bok(st: T.Num) -> Bool:
  match st:
    case T.Num{_nk, _sign, base, _ds, _us, _saw, _why}:
      Bool.not(U32.is_lt(99, base))

# a digit joined or refused keeps the base
def n1.bok.digit(
  ok: Bool,
  +cc: Char,
  +nk: T.NK,
  +sg: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  hb: {Bool.not(U32.is_lt(99, base)) == True{} : Bool}
) -> {n1.bok(T.num.digit.ok(ok, cc, nk, sg, base, ds)) == True{} : Bool}:
  match ok:
    case True{}:
      hb
    case False{}:
      {==}

# an underscore taken or refused keeps the base
def n1.bok.us(
  ok: Bool,
  +nk: T.NK,
  +sg: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +why: String,
  hb: {Bool.not(U32.is_lt(99, base)) == True{} : Bool}
) -> {n1.bok(T.num.us.go(ok, nk, sg, base, ds, why)) == True{} : Bool}:
  match ok:
    case True{}:
      hb
    case False{}:
      {==}

# a dot or an exponent mark taken or refused sets base ten
def n1.bok.ten(
  ok: Bool,
  +sg: T.Sign
) -> {Bool.and(n1.bok(T.num.dot.go(ok, sg)), n1.bok(T.num.exp.go(ok, sg))) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

# the first character of an unsigned numeral keeps a base
def n1.bok.lead(
  pp: Bool,
  mm: Bool,
  zz: Bool,
  dd: Bool,
  +cc: Char,
  +sg: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String,
  hb: {Bool.not(U32.is_lt(99, base)) == True{} : Bool}
) -> {n1.bok(T.num.lead.go(pp, mm, zz, dd, T.Num{T.NLead{}, sg, base, ds, us, saw, why}, cc)) == True{} : Bool}:
  match pp:
    case True{}:
      {==}
    case False{}:
      match mm:
        case True{}:
          {==}
        case False{}:
          match zz:
            case True{}:
              {==}
            case False{}:
              match dd:
                case True{}:
                  n1.bok.digit(T.dig.ok(T.dig.val(cc), base), cc, T.NDig{}, sg, base, ds, hb)
                case False{}:
                  {==}

# the character after a sign keeps a base
def n1.bok.sign(
  tw: Bool,
  +cc: Char,
  +sg: T.Sign
) -> {n1.bok(T.num.after.sign.go(tw, sg, cc)) == True{} : Bool}:
  match tw:
    case True{}:
      {==}
    case False{}:
      n1.bok.lead(Char.is_eq(cc, '+'), Char.is_eq(cc, '-'), Char.is_eq(cc, '0'), Char.is_digit(cc), cc, sg, 10, [],
        False{}, False{}, "", {==})

# the character after a leading zero keeps a base
def n1.bok.zero(
  xx: Bool,
  oo: Bool,
  bb: Bool,
  pp: Bool,
  e1: Bool,
  e2: Bool,
  +cc: Char,
  +sg: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String
) -> {n1.bok(T.num.zero.go(xx, oo, bb, pp, e1, e2, T.Num{T.NZero{}, sg, base, ds, us, saw, why}, cc)) == True{}
  : Bool}:
  match xx oo bb pp:
    case True{} _o _b _p:
      {==}
    case False{} True{} _b _p:
      {==}
    case False{} False{} True{} _p:
      {==}
    case False{} False{} False{} True{}:
      Eq.and.left(n1.bok(T.num.dot.go(Bool.and(saw, Bool.not(us)), sg)), n1.bok(T.num.exp.go(Bool.and(saw,
        Bool.not(us)), sg)), n1.bok.ten(Bool.and(saw, Bool.not(us)), sg))
    case False{} False{} False{} False{}:
      match e1:
        case True{}:
          Eq.and.right(n1.bok(T.num.dot.go(Bool.and(saw, Bool.not(us)), sg)), n1.bok(T.num.exp.go(Bool.and(saw,
            Bool.not(us)), sg)), n1.bok.ten(Bool.and(saw, Bool.not(us)), sg))
        case False{}:
          match e2:
            case True{}:
              Eq.and.right(n1.bok(T.num.dot.go(Bool.and(saw, Bool.not(us)), sg)), n1.bok(T.num.exp.go(Bool.and(saw,
                Bool.not(us)), sg)), n1.bok.ten(Bool.and(saw, Bool.not(us)), sg))
            case False{}:
              {==}

# the character after a digit of an integer part keeps a base
def n1.bok.digs(
  dd: Bool,
  uu: Bool,
  pp: Bool,
  e1: Bool,
  e2: Bool,
  +cc: Char,
  +sg: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String,
  hb: {Bool.not(U32.is_lt(99, base)) == True{} : Bool}
) -> {n1.bok(T.num.digs.go(dd, uu, pp, e1, e2, T.Num{T.NDig{}, sg, base, ds, us, saw, why}, cc)) == True{} : Bool}:
  match dd uu pp:
    case True{} _u _p:
      n1.bok.digit(T.dig.ok(T.dig.val(cc), base), cc, T.NDig{}, sg, base, ds, hb)
    case False{} True{} _p:
      n1.bok.us(Bool.and(saw, Bool.not(us)), T.NDig{}, sg, base, ds, why, hb)
    case False{} False{} True{}:
      Eq.and.left(n1.bok(T.num.dot.go(Bool.and(saw, Bool.not(us)), sg)), n1.bok(T.num.exp.go(Bool.and(saw,
        Bool.not(us)), sg)), n1.bok.ten(Bool.and(saw, Bool.not(us)), sg))
    case False{} False{} False{}:
      match e1 e2:
        case True{} _e:
          Eq.and.right(n1.bok(T.num.dot.go(Bool.and(saw, Bool.not(us)), sg)), n1.bok(T.num.exp.go(Bool.and(saw,
            Bool.not(us)), sg)), n1.bok.ten(Bool.and(saw, Bool.not(us)), sg))
        case False{} True{}:
          Eq.and.right(n1.bok(T.num.dot.go(Bool.and(saw, Bool.not(us)), sg)), n1.bok(T.num.exp.go(Bool.and(saw,
            Bool.not(us)), sg)), n1.bok.ten(Bool.and(saw, Bool.not(us)), sg))
        case False{} False{}:
          {==}

# the character after a prefixed integer's digit keeps a base
def n1.bok.based(
  uu: Bool,
  +cc: Char,
  +sg: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String,
  hb: {Bool.not(U32.is_lt(99, base)) == True{} : Bool}
) -> {n1.bok(T.num.based.go(uu, T.Num{T.NBase{}, sg, base, ds, us, saw, why}, cc)) == True{} : Bool}:
  match uu:
    case True{}:
      n1.bok.us(Bool.and(saw, Bool.not(us)), T.NBase{}, sg, base, ds, why, hb)
    case False{}:
      n1.bok.digit(T.dig.ok(T.dig.val(cc), base), cc, T.NBase{}, sg, base, ds, hb)

# the character after a fraction's digit keeps a base
def n1.bok.frac(
  dd: Bool,
  uu: Bool,
  e1: Bool,
  e2: Bool,
  +cc: Char,
  +sg: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String,
  hb: {Bool.not(U32.is_lt(99, base)) == True{} : Bool}
) -> {n1.bok(T.num.frac.go(dd, uu, e1, e2, T.Num{T.NFrac{}, sg, base, ds, us, saw, why}, cc)) == True{} : Bool}:
  match dd uu:
    case True{} _u:
      n1.bok.digit(T.dig.ok(T.dig.val(cc), base), cc, T.NFrac{}, sg, base, ds, hb)
    case False{} True{}:
      n1.bok.us(Bool.and(saw, Bool.not(us)), T.NFrac{}, sg, base, ds, why, hb)
    case False{} False{}:
      match e1 e2:
        case True{} _e:
          Eq.and.right(n1.bok(T.num.dot.go(Bool.and(saw, Bool.not(us)), sg)), n1.bok(T.num.exp.go(Bool.and(saw,
            Bool.not(us)), sg)), n1.bok.ten(Bool.and(saw, Bool.not(us)), sg))
        case False{} True{}:
          Eq.and.right(n1.bok(T.num.dot.go(Bool.and(saw, Bool.not(us)), sg)), n1.bok(T.num.exp.go(Bool.and(saw,
            Bool.not(us)), sg)), n1.bok.ten(Bool.and(saw, Bool.not(us)), sg))
        case False{} False{}:
          {==}

# the character after an exponent's e keeps a base
def n1.bok.expon(
  pp: Bool,
  mm: Bool,
  dd: Bool,
  +cc: Char,
  +sg: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String,
  hb: {Bool.not(U32.is_lt(99, base)) == True{} : Bool}
) -> {n1.bok(T.num.expon.go(pp, mm, dd, T.Num{T.NExp{}, sg, base, ds, us, saw, why}, cc)) == True{} : Bool}:
  match pp mm dd:
    case True{} _m _d:
      {==}
    case False{} True{} _d:
      {==}
    case False{} False{} True{}:
      n1.bok.digit(T.dig.ok(T.dig.val(cc), base), cc, T.NEDig{}, sg, base, ds, hb)
    case False{} False{} False{}:
      {==}

# the character after an exponent's digit keeps a base
def n1.bok.edig(
  dd: Bool,
  uu: Bool,
  +cc: Char,
  +sg: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String,
  hb: {Bool.not(U32.is_lt(99, base)) == True{} : Bool}
) -> {n1.bok(T.num.edig.go(dd, uu, T.Num{T.NEDig{}, sg, base, ds, us, saw, why}, cc)) == True{} : Bool}:
  match dd uu:
    case True{} _u:
      n1.bok.digit(T.dig.ok(T.dig.val(cc), base), cc, T.NEDig{}, sg, base, ds, hb)
    case False{} True{}:
      n1.bok.us(Bool.and(saw, Bool.not(us)), T.NEDig{}, sg, base, ds, why, hb)
    case False{} False{}:
      {==}

# every step keeps a base that 99 does not fit
def n1.bok.step(
  +st: T.Num,
  +cc: Char,
  hb: {n1.bok(st) == True{} : Bool}
) -> {n1.bok(T.num.step(st, cc)) == True{} : Bool}:
  match st:
    case T.Num{nk, +sg, +base, +ds, +us, +saw, +why}:
      match nk:
        case T.NLead{}:
          n1.bok.lead(Char.is_eq(cc, '+'), Char.is_eq(cc, '-'), Char.is_eq(cc, '0'), Char.is_digit(cc), cc, sg, base,
            ds, us, saw, why, hb)
        case T.NSign{}:
          n1.bok.sign(Bool.or(Char.is_eq(cc, '+'), Char.is_eq(cc, '-')), cc, sg)
        case T.NZero{}:
          n1.bok.zero(Char.is_eq(cc, 'x'), Char.is_eq(cc, 'o'), Char.is_eq(cc, 'b'), Char.is_eq(cc, '.'),
            Char.is_eq(cc, 'e'), Char.is_eq(cc, 'E'), cc, sg, base, ds, us, saw, why)
        case T.NDig{}:
          n1.bok.digs(Char.is_digit(cc), Char.is_eq(cc, '_'), Char.is_eq(cc, '.'), Char.is_eq(cc, 'e'),
            Char.is_eq(cc, 'E'), cc, sg, base, ds, us, saw, why, hb)
        case T.NBase{}:
          n1.bok.based(Char.is_eq(cc, '_'), cc, sg, base, ds, us, saw, why, hb)
        case T.NFrac{}:
          n1.bok.frac(Char.is_digit(cc), Char.is_eq(cc, '_'), Char.is_eq(cc, 'e'), Char.is_eq(cc, 'E'), cc, sg, base,
            ds, us, saw, why, hb)
        case T.NExp{}:
          n1.bok.expon(Char.is_eq(cc, '+'), Char.is_eq(cc, '-'), Char.is_digit(cc), cc, sg, base, ds, us, saw, why, hb)
        case T.NEDig{}:
          n1.bok.edig(Char.is_digit(cc), Char.is_eq(cc, '_'), cc, sg, base, ds, us, saw, why, hb)
        case T.NBad{}:
          hb

# a not that answered True had False under it
def n1.not.t(+aa: Bool, hh: {Bool.not(aa) == True{} : Bool}) -> {aa == False{} : Bool}:
  match aa:
    case True{}:
      Eq.bit.absurd(&2, {True{} == False{} : Bool}, hh)
    case False{}:
      {==}

# a character no base takes, where the base leaves out 99, fails a prefixed
# integer
def n1.bad.based(
  +cc: Char,
  +sg: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  e9: {T.dig.val(cc) == 99 : U32},
  hb: {Bool.not(U32.is_lt(99, base)) == True{} : Bool}
) -> {n1.isbad(T.num.digit.ok(T.dig.ok(T.dig.val(cc), base), cc, T.NBase{}, sg, base, ds)) == True{} : Bool}:
  %Equal.sym(U32, T.dig.val(cc), 99, e9) : {n1.isbad(T.num.digit.ok(T.dig.ok(_, base), cc, T.NBase{}, sg, base, ds))
    == True{} : Bool}
  %Equal.sym(Bool, U32.is_lt(99, base), False{}, n1.not.t(U32.is_lt(99, base), hb)) :
    {n1.isbad(T.num.digit.ok(_, cc, T.NBase{}, sg, base, ds)) == True{} : Bool}
  {==}

# a colon fails every scan
def n1.colon.step(+st: T.Num, hb: {n1.bok(st) == True{} : Bool}) -> {n1.isbad(T.num.step(st, ':')) == True{} : Bool}:
  match st:
    case T.Num{nk, +sg, +base, +ds, +us, +saw, +why}:
      match nk:
        case T.NLead{}:
          {==}
        case T.NSign{}:
          {==}
        case T.NZero{}:
          {==}
        case T.NDig{}:
          {==}
        case T.NBase{}:
          n1.bad.based(':', sg, base, ds, {==}, hb)
        case T.NFrac{}:
          {==}
        case T.NExp{}:
          {==}
        case T.NEDig{}:
          {==}
        case T.NBad{}:
          {==}

# a colon anywhere in the rest fails the scan
def n1.colon.go.c(
  cl: Bool,
  +hh: Char,
  tt: List<&2, Char>,
  +st: T.Num,
  hb: {n1.bok(st) == True{} : Bool},
  +ec: {Char.is_eq(hh, ':') == cl : Bool},
  hc: {T.word.or(cl, T.word.colon(tt)) == True{} : Bool},
  ih: {T.word.colon(tt) == True{} : Bool} -> {n1.isbad(T.num.go(tt, T.num.step(st, hh))) == True{} : Bool}
) -> {n1.isbad(T.num.go(tt, T.num.step(st, hh))) == True{} : Bool}:
  match cl:
    case True{}:
      %Equal.sym(Char, hh, ':', Eq.char_eq_true(hh, ':', ec)) : {n1.isbad(T.num.go(tt, T.num.step(st, _))) == True{}
        : Bool}
      n1.isbad.go(tt, T.num.step(st, ':'), n1.colon.step(st, hb))
    case False{}:
      ih(hc)

# a colon anywhere in the rest fails the scan
def n1.colon.go(
  rest: List<&2, Char>,
  +st: T.Num,
  +hb: {n1.bok(st) == True{} : Bool},
  hc: {T.word.colon(rest) == True{} : Bool}
) -> {n1.isbad(T.num.go(rest, st)) == True{} : Bool}:
  match rest:
    case []:
      Eq.bit.absurd(&2, {n1.isbad(st) == True{} : Bool}, hc)
    case +hh <> +tt:
      n1.colon.go.c(Char.is_eq(hh, ':'), hh, tt, st, hb, {==}, hc,
        h2 => n1.colon.go(tt, T.num.step(st, hh), n1.bok.step(st, hh, hb), h2))

# whether a numeral kind is past the first character and not an exponent's
def n1.noe.nk(nk: T.NK) -> Bool:
  match nk:
    case T.NLead{}:
      False{}
    case T.NExp{}:
      False{}
    case T.NEDig{}:
      False{}
    case _k:
      True{}

# whether a scan is past its first character and not in an exponent: there a
# dash fails it
def n1.noe(st: T.Num) -> Bool:
  match st:
    case T.Num{nk, _sign, _base, _ds, _us, _saw, _why}:
      n1.noe.nk(nk)

# a digit joined or refused leaves no exponent's state, in a kind that is none
def n1.noe.digit(
  ok: Bool,
  +cc: Char,
  +nk: T.NK,
  +sg: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  hn: {n1.noe.nk(nk) == True{} : Bool}
) -> {n1.noe(T.num.digit.ok(ok, cc, nk, sg, base, ds)) == True{} : Bool}:
  match ok:
    case True{}:
      hn
    case False{}:
      {==}

# an underscore taken or refused keeps a kind that is no exponent's
def n1.noe.us(
  ok: Bool,
  +nk: T.NK,
  +sg: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +why: String,
  hn: {n1.noe.nk(nk) == True{} : Bool}
) -> {n1.noe(T.num.us.go(ok, nk, sg, base, ds, why)) == True{} : Bool}:
  match ok:
    case True{}:
      hn
    case False{}:
      {==}

# a dot taken or refused leaves no exponent's state
def n1.noe.dot(ok: Bool, +sg: T.Sign) -> {n1.noe(T.num.dot.go(ok, sg)) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

# the first character of an unsigned numeral leaves no exponent's state
def n1.noe.lead(
  pp: Bool,
  mm: Bool,
  zz: Bool,
  dd: Bool,
  +cc: Char,
  +sg: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String
) -> {n1.noe(T.num.lead.go(pp, mm, zz, dd, T.Num{T.NLead{}, sg, base, ds, us, saw, why}, cc)) == True{} : Bool}:
  match pp mm zz dd:
    case True{} _m _z _d:
      {==}
    case False{} True{} _z _d:
      {==}
    case False{} False{} True{} _d:
      {==}
    case False{} False{} False{} True{}:
      n1.noe.digit(T.dig.ok(T.dig.val(cc), base), cc, T.NDig{}, sg, base, ds, {==})
    case False{} False{} False{} False{}:
      {==}

# the character after a sign leaves no exponent's state
def n1.noe.sign(tw: Bool, +cc: Char, +sg: T.Sign) -> {n1.noe(T.num.after.sign.go(tw, sg, cc)) == True{} : Bool}:
  match tw:
    case True{}:
      {==}
    case False{}:
      n1.noe.lead(Char.is_eq(cc, '+'), Char.is_eq(cc, '-'), Char.is_eq(cc, '0'), Char.is_digit(cc), cc, sg, 10, [],
        False{}, False{}, "")

# a character that is no e and no E after a leading zero leaves no exponent's
# state
def n1.noe.zero(
  xx: Bool,
  oo: Bool,
  bb: Bool,
  pp: Bool,
  e1: Bool,
  e2: Bool,
  +cc: Char,
  +sg: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String,
  h1: {e1 == False{} : Bool},
  h2: {e2 == False{} : Bool}
) -> {n1.noe(T.num.zero.go(xx, oo, bb, pp, e1, e2, T.Num{T.NZero{}, sg, base, ds, us, saw, why}, cc)) == True{}
  : Bool}:
  match xx oo bb pp:
    case True{} _o _b _p:
      {==}
    case False{} True{} _b _p:
      {==}
    case False{} False{} True{} _p:
      {==}
    case False{} False{} False{} True{}:
      n1.noe.dot(Bool.and(saw, Bool.not(us)), sg)
    case False{} False{} False{} False{}:
      match e1 e2:
        case True{} _e:
          Eq.bit.absurd2(&2, {n1.noe(T.num.zero.go(False{}, False{}, False{}, False{}, True{}, e2, T.Num{T.NZero{}, sg,
            base, ds, us, saw, why}, cc)) == True{} : Bool}, h1)
        case False{} True{}:
          Eq.bit.absurd2(&2, {n1.noe(T.num.zero.go(False{}, False{}, False{}, False{}, False{}, True{}, T.Num{T.NZero{},
            sg, base, ds, us, saw, why}, cc)) == True{} : Bool}, h2)
        case False{} False{}:
          {==}

# a character that is no e and no E after a digit of an integer part leaves
# no exponent's state
def n1.noe.digs(
  dd: Bool,
  uu: Bool,
  pp: Bool,
  e1: Bool,
  e2: Bool,
  +cc: Char,
  +sg: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String,
  h1: {e1 == False{} : Bool},
  h2: {e2 == False{} : Bool}
) -> {n1.noe(T.num.digs.go(dd, uu, pp, e1, e2, T.Num{T.NDig{}, sg, base, ds, us, saw, why}, cc)) == True{} : Bool}:
  match dd uu pp:
    case True{} _u _p:
      n1.noe.digit(T.dig.ok(T.dig.val(cc), base), cc, T.NDig{}, sg, base, ds, {==})
    case False{} True{} _p:
      n1.noe.us(Bool.and(saw, Bool.not(us)), T.NDig{}, sg, base, ds, why, {==})
    case False{} False{} True{}:
      n1.noe.dot(Bool.and(saw, Bool.not(us)), sg)
    case False{} False{} False{}:
      match e1 e2:
        case True{} _e:
          Eq.bit.absurd2(&2, {n1.noe(T.num.digs.go(False{}, False{}, False{}, True{}, e2, T.Num{T.NDig{}, sg, base, ds,
            us, saw, why}, cc)) == True{} : Bool}, h1)
        case False{} True{}:
          Eq.bit.absurd2(&2, {n1.noe(T.num.digs.go(False{}, False{}, False{}, False{}, True{}, T.Num{T.NDig{}, sg, base,
            ds, us, saw, why}, cc)) == True{} : Bool}, h2)
        case False{} False{}:
          {==}

# the character after a prefixed integer's digit leaves no exponent's state
def n1.noe.based(
  uu: Bool,
  +cc: Char,
  +sg: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String
) -> {n1.noe(T.num.based.go(uu, T.Num{T.NBase{}, sg, base, ds, us, saw, why}, cc)) == True{} : Bool}:
  match uu:
    case True{}:
      n1.noe.us(Bool.and(saw, Bool.not(us)), T.NBase{}, sg, base, ds, why, {==})
    case False{}:
      n1.noe.digit(T.dig.ok(T.dig.val(cc), base), cc, T.NBase{}, sg, base, ds, {==})

# a character that is no e and no E after a fraction's digit leaves no
# exponent's state
def n1.noe.frac(
  dd: Bool,
  uu: Bool,
  e1: Bool,
  e2: Bool,
  +cc: Char,
  +sg: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String,
  h1: {e1 == False{} : Bool},
  h2: {e2 == False{} : Bool}
) -> {n1.noe(T.num.frac.go(dd, uu, e1, e2, T.Num{T.NFrac{}, sg, base, ds, us, saw, why}, cc)) == True{} : Bool}:
  match dd uu:
    case True{} _u:
      n1.noe.digit(T.dig.ok(T.dig.val(cc), base), cc, T.NFrac{}, sg, base, ds, {==})
    case False{} True{}:
      n1.noe.us(Bool.and(saw, Bool.not(us)), T.NFrac{}, sg, base, ds, why, {==})
    case False{} False{}:
      match e1 e2:
        case True{} _e:
          Eq.bit.absurd2(&2, {n1.noe(T.num.frac.go(False{}, False{}, True{}, e2, T.Num{T.NFrac{}, sg, base, ds, us,
            saw, why}, cc)) == True{} : Bool}, h1)
        case False{} True{}:
          Eq.bit.absurd2(&2, {n1.noe(T.num.frac.go(False{}, False{}, False{}, True{}, T.Num{T.NFrac{}, sg, base, ds, us,
            saw, why}, cc)) == True{} : Bool}, h2)
        case False{} False{}:
          {==}

# a character that is no e and no E leaves no exponent's state
def n1.noe.step(
  +st: T.Num,
  +cc: Char,
  hn: {n1.noe(st) == True{} : Bool},
  h1: {Char.is_eq(cc, 'e') == False{} : Bool},
  h2: {Char.is_eq(cc, 'E') == False{} : Bool}
) -> {n1.noe(T.num.step(st, cc)) == True{} : Bool}:
  match st:
    case T.Num{nk, +sg, +base, +ds, +us, +saw, +why}:
      match nk:
        case T.NLead{}:
          Eq.bit.absurd(&2, {n1.noe(T.num.step(T.Num{T.NLead{}, sg, base, ds, us, saw, why}, cc)) == True{} : Bool},
            hn)
        case T.NSign{}:
          n1.noe.sign(Bool.or(Char.is_eq(cc, '+'), Char.is_eq(cc, '-')), cc, sg)
        case T.NZero{}:
          n1.noe.zero(Char.is_eq(cc, 'x'), Char.is_eq(cc, 'o'), Char.is_eq(cc, 'b'), Char.is_eq(cc, '.'),
            Char.is_eq(cc, 'e'), Char.is_eq(cc, 'E'), cc, sg, base, ds, us, saw, why, h1, h2)
        case T.NDig{}:
          n1.noe.digs(Char.is_digit(cc), Char.is_eq(cc, '_'), Char.is_eq(cc, '.'), Char.is_eq(cc, 'e'),
            Char.is_eq(cc, 'E'), cc, sg, base, ds, us, saw, why, h1, h2)
        case T.NBase{}:
          n1.noe.based(Char.is_eq(cc, '_'), cc, sg, base, ds, us, saw, why)
        case T.NFrac{}:
          n1.noe.frac(Char.is_digit(cc), Char.is_eq(cc, '_'), Char.is_eq(cc, 'e'), Char.is_eq(cc, 'E'), cc, sg, base,
            ds, us, saw, why, h1, h2)
        case T.NExp{}:
          Eq.bit.absurd(&2, {n1.noe(T.num.step(T.Num{T.NExp{}, sg, base, ds, us, saw, why}, cc)) == True{} : Bool}, hn)
        case T.NEDig{}:
          Eq.bit.absurd(&2, {n1.noe(T.num.step(T.Num{T.NEDig{}, sg, base, ds, us, saw, why}, cc)) == True{} : Bool},
            hn)
        case T.NBad{}:
          {==}

# a dash fails a scan past its first character and not in an exponent
def n1.dash.step(
  +st: T.Num,
  hb: {n1.bok(st) == True{} : Bool},
  hn: {n1.noe(st) == True{} : Bool}
) -> {n1.isbad(T.num.step(st, '-')) == True{} : Bool}:
  match st:
    case T.Num{nk, +sg, +base, +ds, +us, +saw, +why}:
      match nk:
        case T.NLead{}:
          Eq.bit.absurd(&2, {n1.isbad(T.num.step(T.Num{T.NLead{}, sg, base, ds, us, saw, why}, '-')) == True{} : Bool},
            hn)
        case T.NSign{}:
          {==}
        case T.NZero{}:
          {==}
        case T.NDig{}:
          {==}
        case T.NBase{}:
          n1.bad.based('-', sg, base, ds, {==}, hb)
        case T.NFrac{}:
          {==}
        case T.NExp{}:
          Eq.bit.absurd(&2, {n1.isbad(T.num.step(T.Num{T.NExp{}, sg, base, ds, us, saw, why}, '-')) == True{} : Bool},
            hn)
        case T.NEDig{}:
          Eq.bit.absurd(&2, {n1.isbad(T.num.step(T.Num{T.NEDig{}, sg, base, ds, us, saw, why}, '-')) == True{} : Bool},
            hn)
        case T.NBad{}:
          {==}

# a word or answered False: its right half did
def n1.wor.r(aa: Bool, bb: Bool, ee: {T.word.or(aa, bb) == False{} : Bool}) -> {bb == False{} : Bool}:
  match aa:
    case True{}:
      Eq.bit.absurd2(&2, {bb == False{} : Bool}, ee)
    case False{}:
      ee

# what the dash lemma claims of the rest after a character: that a dash in
# it, with no e or E, fails the scan
def n1.dash.IH(+hh: Char, +tt: List<&2, Char>, +st: T.Num) -> Type:
  {n1.noe(T.num.step(st, hh)) == True{} : Bool} -> {T.word.dash(tt, False{}) == True{} : Bool} ->
    {T.word.ee(tt) == False{} : Bool} -> {n1.isbad(T.num.go(tt, T.num.step(st, hh))) == True{} : Bool}

# a character of the rest: a dash fails, and anything else that is no e or E
# goes on
def n1.dash.go.c(
  dm: Bool,
  e1: Bool,
  e2: Bool,
  +hh: Char,
  +tt: List<&2, Char>,
  +st: T.Num,
  hb: {n1.bok(st) == True{} : Bool},
  hn: {n1.noe(st) == True{} : Bool},
  +edm: {Char.is_eq(hh, '-') == dm : Bool},
  +ee1: {Char.is_eq(hh, 'e') == e1 : Bool},
  +ee2: {Char.is_eq(hh, 'E') == e2 : Bool},
  hd: {T.word.or(dm, T.word.dash(tt, False{})) == True{} : Bool},
  he: {T.word.or(Bool.or(e1, e2), T.word.ee(tt)) == False{} : Bool},
  ih: n1.dash.IH(hh, tt, st)
) -> {n1.isbad(T.num.go(tt, T.num.step(st, hh))) == True{} : Bool}:
  match dm:
    case True{}:
      %Equal.sym(Char, hh, '-', Eq.char_eq_true(hh, '-', edm)) : {n1.isbad(T.num.go(tt, T.num.step(st, _))) == True{}
        : Bool}
      n1.isbad.go(tt, T.num.step(st, '-'), n1.dash.step(st, hb, hn))
    case False{}:
      match e1:
        case True{}:
          Eq.bit.absurd2(&2, {n1.isbad(T.num.go(tt, T.num.step(st, hh))) == True{} : Bool}, he)
        case False{}:
          match e2:
            case True{}:
              Eq.bit.absurd2(&2, {n1.isbad(T.num.go(tt, T.num.step(st, hh))) == True{} : Bool}, he)
            case False{}:
              ih(n1.noe.step(st, hh, hn, ee1, ee2), hd, he)

# a dash in the rest, with no e or E in it, fails a scan past its first
# character and not in an exponent
def n1.dash.go(
  rest: List<&2, Char>,
  +st: T.Num,
  +hb: {n1.bok(st) == True{} : Bool},
  hn: {n1.noe(st) == True{} : Bool},
  hd: {T.word.dash(rest, False{}) == True{} : Bool},
  he: {T.word.ee(rest) == False{} : Bool}
) -> {n1.isbad(T.num.go(rest, st)) == True{} : Bool}:
  match rest:
    case []:
      Eq.bit.absurd(&2, {n1.isbad(st) == True{} : Bool}, hd)
    case +hh <> +tt:
      n1.dash.go.c(Char.is_eq(hh, '-'), Char.is_eq(hh, 'e'), Char.is_eq(hh, 'E'), hh, tt, st, hb, hn, {==}, {==}, {==},
        hd, he, a => b => c => n1.dash.go(tt, T.num.step(st, hh), n1.bok.step(st, hh, hb), a, b, c))

# every special word fails the numeral scan
def n1.spec.bad(
  +cs: List<&2, Char>,
  +hs: {M3.n1.isspec(cs) == True{} : Bool}
) -> {n1.isbad(T.num.go(cs, T.num.start())) == True{} : Bool}:
  M3.n1.spec.split(xs => {n1.isbad(T.num.go(xs, T.num.start())) == True{} : Bool}, cs, hs,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# so a word the scan does not fail is no special word
def n1.spec.nb.go(
  sp: Bool,
  +cs: List<&2, Char>,
  +es: {M3.n1.isspec(cs) == sp : Bool},
  +hg: {n1.isbad(T.num.go(cs, T.num.start())) == False{} : Bool}
) -> {M3.n1.isspec(cs) == False{} : Bool}:
  match sp:
    case True{}:
      Eq.bit.absurd2(&2, {M3.n1.isspec(cs) == False{} : Bool}, Equal.trans(Bool, True{}, n1.isbad(T.num.go(cs,
        T.num.start())), False{}, Equal.sym(Bool, n1.isbad(T.num.go(cs, T.num.start())), True{}, n1.spec.bad(cs, es)),
        hg))
    case False{}:
      es

# a word the scan does not fail has no colon
def n1.colon.nb(
  cl: Bool,
  +cs: List<&2, Char>,
  +ec: {T.word.colon(cs) == cl : Bool},
  +hg: {n1.isbad(T.num.go(cs, T.num.start())) == False{} : Bool}
) -> {T.word.colon(cs) == False{} : Bool}:
  match cl:
    case True{}:
      Eq.bit.absurd2(&2, {T.word.colon(cs) == False{} : Bool}, Equal.trans(Bool, True{}, n1.isbad(T.num.go(cs,
        T.num.start())), False{}, Equal.sym(Bool, n1.isbad(T.num.go(cs, T.num.start())), True{}, n1.colon.go(cs,
        T.num.start(), {==}, ec)), hg))
    case False{}:
      ec

# and no dash after its first character, unless it has an e or an E
def n1.dash.nb(
  dv: Bool,
  +hh: Char,
  +tt: List<&2, Char>,
  +ed: {T.word.dash(tt, False{}) == dv : Bool},
  +he: {T.word.ee(tt) == False{} : Bool},
  +hg: {n1.isbad(T.num.go(hh <> tt, T.num.start())) == False{} : Bool}
) -> {T.word.dash(tt, False{}) == False{} : Bool}:
  match dv:
    case True{}:
      Eq.bit.absurd2(&2, {T.word.dash(tt, False{}) == False{} : Bool}, Equal.trans(Bool, True{},
        n1.isbad(T.num.go(hh <> tt, T.num.start())), False{}, Equal.sym(Bool, n1.isbad(T.num.go(hh <> tt,
        T.num.start())), True{}, n1.dash.go(tt, T.num.step(T.num.start(), hh), n1.bok.step(T.num.start(), hh, {==}),
        n1.noe.lead(Char.is_eq(hh, '+'), Char.is_eq(hh, '-'), Char.is_eq(hh, '0'), Char.is_digit(hh), hh, T.Plus{},
        10, [], False{}, False{}, ""), ed, he)), hg))
    case False{}:
      ed

# a word with an e or an E is no datetime
def n1.nodate.e(
  ex: Bool,
  +cs: List<&2, Char>,
  +ee: {T.word.ee(cs) == ex : Bool},
  +hg: {n1.isbad(T.num.go(cs, T.num.start())) == False{} : Bool}
) -> {T.word.as_date(T.word.dash(cs, True{}), ex) == False{} : Bool}:
  match ex:
    case True{}:
      {==}
    case False{}:
      match cs:
        case []:
          {==}
        case +hh <> +tt:
          n1.dash.nb(T.word.dash(tt, False{}), hh, tt, {==}, n1.wor.r(T.word.ee.hit(hh), T.word.ee(tt), ee), hg)

# a word the scan does not fail goes to the scan, not the datetime reader
def n1.nodate(
  +cs: List<&2, Char>,
  +hg: {n1.isbad(T.num.go(cs, T.num.start())) == False{} : Bool}
) -> {T.word.as_date(T.word.or(T.word.colon(cs), T.word.dash(cs, True{})), T.word.ee(cs)) == False{} : Bool}:
  %Equal.sym(Bool, T.word.colon(cs), False{}, n1.colon.nb(T.word.colon(cs), cs, {==}, hg)) :
    {T.word.as_date(T.word.or(_, T.word.dash(cs, True{})), T.word.ee(cs)) == False{} : Bool}
  n1.nodate.e(T.word.ee(cs), cs, {==}, hg)

# a word the scan does not fail, special or not, is read by the scan
def n1.wv.go(
  ld: Bool,
  +cs: List<&2, Char>,
  +hg: {n1.isbad(T.num.go(cs, T.num.start())) == False{} : Bool}
) -> {T.word.val.pick(ld, cs) == T.word.num(cs) : T.Got}:
  match ld:
    case True{}:
      %Equal.sym(T.Got, T.word.spec(String.from_list(cs)), T.GotBad{""}, M3.n1.spec.no(cs,
          n1.spec.nb.go(M3.n1.isspec(cs), cs,
        {==}, hg))) : {T.word.route(_, T.word.or(T.word.colon(cs), T.word.dash(cs, True{})), cs) == T.word.num(cs)
        : T.Got}
      %Equal.sym(Bool, T.word.as_date(T.word.or(T.word.colon(cs), T.word.dash(cs, True{})), T.word.ee(cs)), False{},
        n1.nodate(cs, hg)) : {T.word.route.date(_, cs) == T.word.num(cs) : T.Got}
      {==}
    case False{}:
      %Equal.sym(Bool, T.word.as_date(T.word.or(T.word.colon(cs), T.word.dash(cs, True{})), T.word.ee(cs)), False{},
        n1.nodate(cs, hg)) : {T.word.route.date(_, cs) == T.word.num(cs) : T.Got}
      {==}

# a word the scan does not fail is read by the scan
def n1.wv(
  +cs: List<&2, Char>,
  +hg: {n1.isbad(T.num.go(cs, T.num.start())) == False{} : Bool}
) -> {T.word.val(cs) == T.word.num(cs) : T.Got}:
  match cs:
    case []:
      {==}
    case +hh <> +tt:
      n1.wv.go(T.word.special(hh), hh <> tt, hg)
