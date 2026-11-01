# the float scan accepts exactly the words the float grammar spells
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/FloatReadExactly.bend as L1
import ../../laws/defs/AbnfGrammar.bend as D1
import ../../laws/defs/BareValueGrammar.bend as D2
import ../../laws/defs/DocumentSameness.bend as D3
import ../../laws/defs/GrammarDerivations.bend as D4
import ./DigitsWrittenBack.bend as M1
import ./FreshNamesInRows.bend as M2
import ./NumberScanRefusals.bend as M3
import ./SpecialWordCompare.bend as M4

# a character that is both a digit and an underscore is not there
def n1.du(
  -A: Type,
  cc: Char,
  hd: {Char.is_digit(cc) == True{} : Bool},
  hu: {Char.is_eq(cc, '_') == True{} : Bool}
) -> A:
  Eq.bit.absurd2(&1, A, Equal.trans(Bool, True{}, Char.is_eq(cc, '_'), False{}, Equal.sym(Bool, Char.is_eq(cc, '_'),
    True{}, hu), M3.n1.nous(cc, hd)))

# a failed scan stays failed, whatever follows
def n1.bad.go(
  rest: List<&2, Char>,
  +sg: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String
) -> {T.num.go(rest, T.Num{T.NBad{}, sg, base, ds, us, saw, why}) == T.Num{T.NBad{}, sg, base, ds, us, saw,
  why} : T.Num}:
  match rest:
    case []:
      {==}
    case _h <> tt:
      n1.bad.go(tt, sg, base, ds, us, saw, why)

# a finished numeral scan holds a float: a fraction or an exponent with a
# digit read
def n1.fsh.nk(nk: T.NK, saw: Bool) -> Bool:
  match nk:
    case T.NFrac{}:
      saw
    case T.NEDig{}:
      saw
    case _k:
      False{}

# whether a finished numeral scan holds a float, with no underscore last
def n1.fsh(st: T.Num) -> Bool:
  match st:
    case T.Num{nk, _sign, _base, _ds, us, saw, _why}:
      Bool.and(n1.fsh.nk(nk, saw), Bool.not(us))

# a failed scan holds no float, whatever follows
def n1.fsh.bad(
  rest: List<&2, Char>,
  +why: String
) -> {n1.fsh(T.num.go(rest, T.Num{T.NBad{}, T.Plus{}, 10, [], False{}, False{}, why})) == False{} : Bool}:
  %Equal.sym(T.Num, T.num.go(rest, T.Num{T.NBad{}, T.Plus{}, 10, [], False{}, False{}, why}), T.Num{T.NBad{}, T.Plus{},
    10, [], False{}, False{}, why}, n1.bad.go(rest, T.Plus{}, 10, [], False{}, False{}, why)) : {n1.fsh(_) == False{}
    : Bool}
  {==}

# the scan after a digit of an exponent
def n1.sx(+sg: T.Sign, +ds: List<&2, U32>, +why: String) -> T.Num:
  T.Num{T.NEDig{}, sg, 10, ds, False{}, True{}, why}

# what the exponent-digit lemma claims: after a digit of an exponent, the
# scan finishes as a float exactly when the rest is *( DIGIT / underscore
# DIGIT )
def n1.X.G(rest: List<&2, Char>, +sg: T.Sign, +ds: List<&2, U32>, +why: String) -> Type:
  {n1.fsh(T.num.go(rest, n1.sx(sg, ds, why))) == D1.abnf.dec_rep(rest) : Bool}

# one character left
def n1.X.one(
  dd: Bool,
  uu: Bool,
  +cc: Char,
  +sg: T.Sign,
  +ds: List<&2, U32>,
  +why: String,
  ed: {Char.is_digit(cc) == dd : Bool}
) -> {n1.fsh(T.num.edig.go(dd, uu, n1.sx(sg, ds, why), cc)) == dd : Bool}:
  match dd:
    case True{}:
      %Equal.sym(Bool, T.dig.ok(T.dig.val(cc), 10), True{}, M3.n1.dok10(cc, ed)) :
        {n1.fsh(T.num.digit.ok(_, cc, T.NEDig{}, sg, 10, ds)) == True{} : Bool}
      {==}
    case False{}:
      match uu:
        case True{}:
          {==}
        case False{}:
          {==}

# an exponent's state where an underscore fails (after an underscore, or
# before the first digit): a digit goes on, anything else fails
def n1.X.us(
  dd: Bool,
  uu: Bool,
  +cc: Char,
  +tt: List<&2, Char>,
  +sg: T.Sign,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String,
  ed: {Char.is_digit(cc) == dd : Bool},
  hq: {Bool.and(saw, Bool.not(us)) == False{} : Bool},
  ih: n1.X.G(tt, sg, T.dec.go(ds, 10, T.dig.val(cc)), "")
) -> {n1.fsh(T.num.go(tt, T.num.edig.go(dd, uu, T.Num{T.NEDig{}, sg, 10, ds, us, saw, why}, cc)))
  == Bool.and(dd, D1.abnf.dec_rep(tt)) : Bool}:
  match dd:
    case True{}:
      %Equal.sym(Bool, T.dig.ok(T.dig.val(cc), 10), True{}, M3.n1.dok10(cc, ed)) :
        {n1.fsh(T.num.go(tt, T.num.digit.ok(_, cc, T.NEDig{}, sg, 10, ds))) == D1.abnf.dec_rep(tt) : Bool}
      ih
    case False{}:
      match uu:
        case True{}:
          %Equal.sym(Bool, Bool.and(saw, Bool.not(us)), False{}, hq) :
            {n1.fsh(T.num.go(tt, T.num.us.go(_, T.NEDig{}, sg, 10, ds, why))) == False{} : Bool}
          n1.fsh.bad(tt, "invalid underscore")
        case False{}:
          n1.fsh.bad(tt, "invalid exponent")

# what the exponent's underscore lemma claims: after an underscore, the scan
# finishes as a float exactly when a digit and the repetition follow
def n1.X.U(+h2: Char, +t2: List<&2, Char>, +sg: T.Sign, +ds: List<&2, U32>, +why: String) -> Type:
  {n1.fsh(T.num.go(h2 <> t2, T.Num{T.NEDig{}, sg, 10, ds, True{}, True{}, why})) == Bool.and(Char.is_digit(h2),
    D1.abnf.dec_rep(t2)) : Bool}

# two or more characters left
def n1.X.two(
  dd: Bool,
  uu: Bool,
  +cc: Char,
  +h2: Char,
  +t2: List<&2, Char>,
  +sg: T.Sign,
  +ds: List<&2, U32>,
  +why: String,
  ed: {Char.is_digit(cc) == dd : Bool},
  eu: {Char.is_eq(cc, '_') == uu : Bool},
  ihd: n1.X.G(h2 <> t2, sg, T.dec.go(ds, 10, T.dig.val(cc)), ""),
  ihu: n1.X.U(h2, t2, sg, ds, why)
) -> {n1.fsh(T.num.go(h2 <> t2, T.num.edig.go(dd, uu, n1.sx(sg, ds, why), cc))) == Bool.or(Bool.and(dd,
  D1.abnf.dec_rep(h2 <> t2)), Bool.and(uu, Bool.and(Char.is_digit(h2), D1.abnf.dec_rep(t2)))) : Bool}:
  match dd:
    case True{}:
      match uu:
        case True{}:
          n1.du({n1.fsh(T.num.go(h2 <> t2, T.num.edig.go(True{}, True{}, n1.sx(sg, ds, why), cc)))
            == Bool.or(D1.abnf.dec_rep(h2 <> t2), Bool.and(Char.is_digit(h2), D1.abnf.dec_rep(t2))) : Bool}, cc, ed,
            eu)
        case False{}:
          %Equal.sym(Bool, T.dig.ok(T.dig.val(cc), 10), True{}, M3.n1.dok10(cc, ed)) :
            {n1.fsh(T.num.go(h2 <> t2, T.num.digit.ok(_, cc, T.NEDig{}, sg, 10, ds))) == Bool.or(D1.abnf.dec_rep(h2
              <> t2), False{}) : Bool}
          Equal.trans(Bool, n1.fsh(T.num.go(h2 <> t2, n1.sx(sg, T.dec.go(ds, 10, T.dig.val(cc)), ""))),
            D1.abnf.dec_rep(h2 <> t2), Bool.or(D1.abnf.dec_rep(h2 <> t2), False{}), ihd,
            Equal.sym(Bool, Bool.or(D1.abnf.dec_rep(h2 <> t2), False{}), D1.abnf.dec_rep(h2 <> t2),
              M3.n1.orf(D1.abnf.dec_rep(h2 <> t2))))
    case False{}:
      match uu:
        case True{}:
          ihu
        case False{}:
          n1.fsh.bad(h2 <> t2, "invalid exponent")

# after a digit of an exponent, the scan finishes as a float exactly when the
# rest is *( DIGIT / underscore DIGIT )
def n1.X(rest: List<&2, Char>, +sg: T.Sign, +ds: List<&2, U32>, +why: String) -> n1.X.G(rest, sg, ds, why):
  match rest:
    case []:
      {==}
    case +hh <> tt:
      match tt:
        case []:
          %M3.n1.dig(hh) : {n1.fsh(T.num.go([hh], n1.sx(sg, ds, why))) == _ : Bool}
          n1.X.one(Char.is_digit(hh), Char.is_eq(hh, '_'), hh, sg, ds, why, {==})
        case +h2 <> +t2:
          %M3.n1.dig(hh) : {n1.fsh(T.num.go(hh <> h2 <> t2, n1.sx(sg, ds, why))) == Bool.or(Bool.and(_,
            D1.abnf.dec_rep(h2 <> t2)), Bool.and(D1.abnf.underscore(hh), Bool.and(D1.abnf.DIGIT(h2),
            D1.abnf.dec_rep(t2)))) : Bool}
          %M3.n1.us(hh) : {n1.fsh(T.num.go(hh <> h2 <> t2, n1.sx(sg, ds, why))) == Bool.or(Bool.and(Char.is_digit(hh),
            D1.abnf.dec_rep(h2 <> t2)), Bool.and(_, Bool.and(D1.abnf.DIGIT(h2), D1.abnf.dec_rep(t2)))) : Bool}
          %M3.n1.dig(h2) : {n1.fsh(T.num.go(hh <> h2 <> t2, n1.sx(sg, ds, why))) == Bool.or(Bool.and(Char.is_digit(hh),
            D1.abnf.dec_rep(h2 <> t2)), Bool.and(Char.is_eq(hh, '_'), Bool.and(_, D1.abnf.dec_rep(t2)))) : Bool}
          n1.X.two(Char.is_digit(hh), Char.is_eq(hh, '_'), hh, h2, t2, sg, ds, why, {==}, {==},
            n1.X(h2 <> t2, sg, T.dec.go(ds, 10, T.dig.val(hh)), ""),
            n1.X.us(Char.is_digit(h2), Char.is_eq(h2, '_'), h2, t2, sg, ds, True{}, True{}, why, {==}, {==},
              n1.X(t2, sg, T.dec.go(ds, 10, T.dig.val(h2)), "")))

# a character a test found equal to k, where k fails a predicate the
# character passes, is not there
def n1.no(
  -A: Type,
  cc: Char,
  kk: Char,
  pp: Char -> Bool,
  ee: {Char.is_eq(cc, kk) == True{} : Bool},
  yes: {pp(cc) == True{} : Bool},
  no: {pp(kk) == False{} : Bool}
) -> A:
  Eq.bit.gone(&1, A, Eq.refute_char(cc, kk, pp, ee, yes, no))

# the scan before an exponent's first digit, after its sign
def n1.ses(+sg: T.Sign) -> T.Num:
  T.Num{T.NEDig{}, sg, 10, [], False{}, False{}, ""}

# after an exponent's sign, the scan finishes as a float exactly when the
# rest is a zero-prefixable-int
def n1.Es(
  rest: List<&2, Char>,
  +sg: T.Sign
) -> {n1.fsh(T.num.go(rest, n1.ses(sg))) == D1.abnf.zero_prefixable_int(rest) : Bool}:
  match rest:
    case []:
      {==}
    case +hh <> +tt:
      %M3.n1.dig(hh) : {n1.fsh(T.num.go(hh <> tt, n1.ses(sg))) == Bool.and(_, D1.abnf.dec_rep(tt)) : Bool}
      n1.X.us(Char.is_digit(hh), Char.is_eq(hh, '_'), hh, tt, sg, [], False{}, False{}, "", {==}, {==},
        n1.X(tt, sg, T.dec.go([], 10, T.dig.val(hh)), ""))

# the character after e: a sign, a digit, or anything else, which fails
def n1.E.go(
  pp: Bool,
  mm: Bool,
  dd: Bool,
  +cc: Char,
  +tt: List<&2, Char>,
  +sg: T.Sign,
  ep: {Char.is_eq(cc, '+') == pp : Bool},
  em: {Char.is_eq(cc, '-') == mm : Bool},
  ed: {Char.is_digit(cc) == dd : Bool},
  ihs: {n1.fsh(T.num.go(tt, n1.ses(sg))) == D1.abnf.zero_prefixable_int(tt) : Bool},
  ihx: n1.X.G(tt, sg, T.dec.go([], 10, T.dig.val(cc)), "")
) -> {n1.fsh(T.num.go(tt, T.num.expon.go(pp, mm, dd, M3.n1.se(sg), cc))) == Bool.or(Bool.and(Bool.or(mm, pp),
  D1.abnf.zero_prefixable_int(tt)), Bool.and(dd, D1.abnf.dec_rep(tt))) : Bool}:
  match pp:
    case True{}:
      match mm:
        case True{}:
          n1.no({n1.fsh(T.num.go(tt, T.num.expon.go(True{}, True{}, dd, M3.n1.se(sg), cc))) == Bool.or(
            D1.abnf.zero_prefixable_int(tt), Bool.and(dd, D1.abnf.dec_rep(tt))) : Bool}, cc, '+',
            xx => Char.is_eq(xx, '-'), ep, em, {==})
        case False{}:
          match dd:
            case True{}:
              n1.no({n1.fsh(T.num.go(tt, T.num.expon.go(True{}, False{}, True{}, M3.n1.se(sg), cc))) ==
                Bool.or(D1.abnf.zero_prefixable_int(tt), D1.abnf.dec_rep(tt)) : Bool}, cc, '+',
                xx => Char.is_digit(xx), ep, ed, {==})
            case False{}:
              M3.n1.orf.eq(n1.fsh(T.num.go(tt, n1.ses(sg))), D1.abnf.zero_prefixable_int(tt), ihs)
    case False{}:
      match mm:
        case True{}:
          match dd:
            case True{}:
              n1.no({n1.fsh(T.num.go(tt, T.num.expon.go(False{}, True{}, True{}, M3.n1.se(sg), cc))) ==
                Bool.or(D1.abnf.zero_prefixable_int(tt), D1.abnf.dec_rep(tt)) : Bool}, cc, '-',
                xx => Char.is_digit(xx), em, ed, {==})
            case False{}:
              M3.n1.orf.eq(n1.fsh(T.num.go(tt, n1.ses(sg))), D1.abnf.zero_prefixable_int(tt), ihs)
        case False{}:
          match dd:
            case True{}:
              %Equal.sym(Bool, T.dig.ok(T.dig.val(cc), 10), True{}, M3.n1.dok10(cc, ed)) :
                {n1.fsh(T.num.go(tt, T.num.digit.ok(_, cc, T.NEDig{}, sg, 10, []))) == D1.abnf.dec_rep(tt) : Bool}
              ihx
            case False{}:
              n1.fsh.bad(tt, "invalid exponent")

# after an exponent's e, the scan finishes as a float exactly when the rest
# is a float-exp-part
def n1.E(
  rest: List<&2, Char>,
  +sg: T.Sign
) -> {n1.fsh(T.num.go(rest, M3.n1.se(sg))) == D1.abnf.float_exp_part(rest) : Bool}:
  match rest:
    case []:
      {==}
    case +hh <> +tt:
      %M3.n1.minus(hh) : {n1.fsh(T.num.go(hh <> tt, M3.n1.se(sg))) == Bool.or(Bool.and(Bool.or(_, D1.abnf.plus(hh)),
        D1.abnf.zero_prefixable_int(tt)), D1.abnf.zero_prefixable_int(hh <> tt)) : Bool}
      %M3.n1.plus(hh) : {n1.fsh(T.num.go(hh <> tt, M3.n1.se(sg))) == Bool.or(Bool.and(Bool.or(Char.is_eq(hh, '-'), _),
        D1.abnf.zero_prefixable_int(tt)), D1.abnf.zero_prefixable_int(hh <> tt)) : Bool}
      %M3.n1.dig(hh) : {n1.fsh(T.num.go(hh <> tt, M3.n1.se(sg))) == Bool.or(Bool.and(Bool.or(Char.is_eq(hh, '-'),
        Char.is_eq(hh, '+')), D1.abnf.zero_prefixable_int(tt)), Bool.and(_, D1.abnf.dec_rep(tt))) : Bool}
      n1.E.go(Char.is_eq(hh, '+'), Char.is_eq(hh, '-'), Char.is_digit(hh), hh, tt, sg, {==}, {==}, {==},
        n1.Es(tt, sg), n1.X(tt, sg, T.dec.go([], 10, T.dig.val(hh)), ""))

# The cut of a float's text. A character where no cut falls is kept in front
# of the part before the cut, and the part from the cut on is the rest's.

# a character where no cut falls stays in front of the part before the cut
def n1.pre.no(
  +ct: D1.ACut,
  +cc: Char,
  +xs: List<&2, Char>,
  hc: {D1.abnf.cut.at(ct, cc) == False{} : Bool}
) -> {cc <> D1.abnf.cut.pre(xs, ct) == D1.abnf.cut.pre(cc <> xs, ct) : List<&2, Char>}:
  %Equal.sym(Bool, D1.abnf.cut.at(ct, cc), False{}, hc) : {cc <> D1.abnf.cut.pre(xs, ct)
    == D1.abnf.cut.pre.pick(_, cc, D1.abnf.cut.pre(xs, ct)) : List<&2, Char>}
  {==}

# and the part from the cut on is the rest's
def n1.post.no(
  +ct: D1.ACut,
  +cc: Char,
  +xs: List<&2, Char>,
  hc: {D1.abnf.cut.at(ct, cc) == False{} : Bool}
) -> {D1.abnf.cut.post(xs, ct) == D1.abnf.cut.post(cc <> xs, ct) : List<&2, Char>}:
  %Equal.sym(Bool, D1.abnf.cut.at(ct, cc), False{}, hc) : {D1.abnf.cut.post(xs, ct)
    == D1.abnf.cut.post.pick(_, cc, xs, D1.abnf.cut.post(xs, ct)) : List<&2, Char>}
  {==}

# no cut falls at a digit
def n1.at.dig(
  ct: D1.ACut,
  cc: Char,
  hc: {Char.is_digit(cc) == True{} : Bool}
) -> {D1.abnf.cut.at(ct, cc) == False{} : Bool}:
  match ct:
    case D1.ACutDot{}:
      M2.dg.elim(zz => {D1.abnf.cut.at(D1.ACutDot{}, zz) == False{} : Bool}, cc, hc,
        {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})
    case D1.ACutExp{}:
      M2.dg.elim(zz => {D1.abnf.cut.at(D1.ACutExp{}, zz) == False{} : Bool}, cc, hc,
        {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# no exponent's cut falls at a character that is no e and no E
def n1.at.e(
  cc: Char,
  e1: {Char.is_eq(cc, 'e') == False{} : Bool},
  e2: {Char.is_eq(cc, 'E') == False{} : Bool}
) -> {D1.abnf.cut.at(D1.ACutExp{}, cc) == False{} : Bool}:
  match cc:
    case Chr{+cp}:
      %Equal.sym(Bool, Char.is_eq(Chr{cp}, 'e'), False{}, e1) : {Bool.or(_, Char.is_eq(Chr{cp}, 'E')) == False{}
        : Bool}
      e2

# no float's cut falls at a character that is no dot, e or E
def n1.at.d(
  cc: Char,
  e0: {Char.is_eq(cc, '.') == False{} : Bool},
  e1: {Char.is_eq(cc, 'e') == False{} : Bool},
  e2: {Char.is_eq(cc, 'E') == False{} : Bool}
) -> {D1.abnf.cut.at(D1.ACutDot{}, cc) == False{} : Bool}:
  match cc:
    case Chr{+cp}:
      %Equal.sym(Bool, Char.is_eq(Chr{cp}, '.'), False{}, e0) : {Bool.or(_, D1.abnf.e(Chr{cp})) == False{} : Bool}
      n1.at.e(Chr{cp}, e1, e2)

# a zero-prefixable-int cut at c, where c is no digit, is none, whatever
# follows
def n1.zpi.cut(
  cut: Bool,
  +cc: Char,
  +xs: List<&2, Char>,
  +more: Bool,
  hc: {Char.is_digit(cc) == False{} : Bool}
) -> {False{} == Bool.and(D1.abnf.zero_prefixable_int(D1.abnf.cut.pre.pick(cut, cc, xs)), more) : Bool}:
  match cut:
    case True{}:
      {==}
    case False{}:
      %M3.n1.zpi.n(cc, xs, hc) :
        {False{} == Bool.and(_, more) : Bool}
      {==}

# The fraction. After a digit of the fraction the scan finishes as a float
# exactly when the rest, cut at its first e, is the repetition and then an
# optional exp.

# the scan after a digit of a fraction
def n1.sf(+sg: T.Sign, +ds: List<&2, U32>, +why: String) -> T.Num:
  T.Num{T.NFrac{}, sg, 10, ds, False{}, True{}, why}

# what the fraction lemma claims
def n1.F.G(rest: List<&2, Char>, +sg: T.Sign, +ds: List<&2, U32>, +why: String) -> Type:
  {n1.fsh(T.num.go(rest, n1.sf(sg, ds, why))) == Bool.and(D1.abnf.dec_rep(D1.abnf.cut.pre(rest, D1.ACutExp{})),
    D1.abnf.opt_exp(D1.abnf.cut.post(rest, D1.ACutExp{}))) : Bool}

# a fraction's state where an underscore fails (after an underscore, or before
# the first digit), with a character that is no digit: it fails, and no
# zero-prefixable-int starts there
def n1.Fu.bad(
  uu: Bool,
  e1: Bool,
  e2: Bool,
  +cc: Char,
  +tt: List<&2, Char>,
  +sg: T.Sign,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String,
  hq: {Bool.and(saw, Bool.not(us)) == False{} : Bool}
) -> {n1.fsh(T.num.go(tt, T.num.frac.go(False{}, uu, e1, e2, T.Num{T.NFrac{}, sg, 10, ds, us, saw, why}, cc)))
  == False{} : Bool}:
  match uu:
    case True{}:
      %Equal.sym(Bool, Bool.and(saw, Bool.not(us)), False{}, hq) :
        {n1.fsh(T.num.go(tt, T.num.us.go(_, T.NFrac{}, sg, 10, ds, why))) == False{} : Bool}
      n1.fsh.bad(tt, "invalid underscore")
    case False{}:
      match e1:
        case True{}:
          %Equal.sym(Bool, Bool.and(saw, Bool.not(us)), False{}, hq) :
            {n1.fsh(T.num.go(tt, T.num.exp.go(_, sg))) == False{} : Bool}
          n1.fsh.bad(tt, "invalid exponent")
        case False{}:
          match e2:
            case True{}:
              %Equal.sym(Bool, Bool.and(saw, Bool.not(us)), False{}, hq) :
                {n1.fsh(T.num.go(tt, T.num.exp.go(_, sg))) == False{} : Bool}
              n1.fsh.bad(tt, "invalid exponent")
            case False{}:
              n1.fsh.bad(tt, "invalid fraction")

# the character after such a state
def n1.Fu.go(
  dd: Bool,
  uu: Bool,
  e1: Bool,
  e2: Bool,
  +cc: Char,
  +tt: List<&2, Char>,
  +sg: T.Sign,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String,
  +ed: {Char.is_digit(cc) == dd : Bool},
  hq: {Bool.and(saw, Bool.not(us)) == False{} : Bool},
  ih: n1.F.G(tt, sg, T.dec.go(ds, 10, T.dig.val(cc)), "")
) -> {n1.fsh(T.num.go(tt, T.num.frac.go(dd, uu, e1, e2, T.Num{T.NFrac{}, sg, 10, ds, us, saw, why}, cc)))
  == Bool.and(D1.abnf.zero_prefixable_int(D1.abnf.cut.pre(cc <> tt, D1.ACutExp{})),
  D1.abnf.opt_exp(D1.abnf.cut.post(cc <> tt, D1.ACutExp{}))) : Bool}:
  match dd:
    case True{}:
      %n1.pre.no(D1.ACutExp{}, cc, tt, n1.at.dig(D1.ACutExp{}, cc, ed)) : {n1.fsh(T.num.go(tt,
        T.num.digit.ok(T.dig.ok(T.dig.val(cc), 10), cc, T.NFrac{}, sg, 10, ds))) ==
        Bool.and(D1.abnf.zero_prefixable_int(_), D1.abnf.opt_exp(D1.abnf.cut.post(cc <> tt, D1.ACutExp{})))
        : Bool}
      %n1.post.no(D1.ACutExp{}, cc, tt, n1.at.dig(D1.ACutExp{}, cc, ed)) : {n1.fsh(T.num.go(tt,
        T.num.digit.ok(T.dig.ok(T.dig.val(cc), 10), cc, T.NFrac{}, sg, 10, ds))) ==
        Bool.and(D1.abnf.zero_prefixable_int(cc <> D1.abnf.cut.pre(tt, D1.ACutExp{})), D1.abnf.opt_exp(_))
        : Bool}
      %M3.n1.zpi.d(cc, D1.abnf.cut.pre(tt, D1.ACutExp{}), ed) : {n1.fsh(T.num.go(tt,
        T.num.digit.ok(T.dig.ok(T.dig.val(cc), 10), cc, T.NFrac{}, sg, 10, ds))) == Bool.and(_,
        D1.abnf.opt_exp(D1.abnf.cut.post(tt, D1.ACutExp{}))) : Bool}
      %Equal.sym(Bool, T.dig.ok(T.dig.val(cc), 10), True{}, M3.n1.dok10(cc, ed)) : {n1.fsh(T.num.go(tt,
        T.num.digit.ok(_, cc, T.NFrac{}, sg, 10, ds))) == Bool.and(D1.abnf.dec_rep(D1.abnf.cut.pre(tt,
        D1.ACutExp{})), D1.abnf.opt_exp(D1.abnf.cut.post(tt, D1.ACutExp{}))) : Bool}
      ih
    case False{}:
      Equal.trans(Bool, n1.fsh(T.num.go(tt, T.num.frac.go(False{}, uu, e1, e2, T.Num{T.NFrac{}, sg, 10, ds, us, saw,
        why}, cc))), False{}, Bool.and(D1.abnf.zero_prefixable_int(D1.abnf.cut.pre(cc <> tt, D1.ACutExp{})),
        D1.abnf.opt_exp(D1.abnf.cut.post(cc <> tt, D1.ACutExp{}))),
        n1.Fu.bad(uu, e1, e2, cc, tt, sg, ds, us, saw, why, hq),
        n1.zpi.cut(D1.abnf.cut.at(D1.ACutExp{}, cc), cc, D1.abnf.cut.pre(tt, D1.ACutExp{}),
          D1.abnf.opt_exp(D1.abnf.cut.post(cc <> tt, D1.ACutExp{})), ed))

# a fraction's state where an underscore fails, with a character and the rest
def n1.Fu(
  +cc: Char,
  +tt: List<&2, Char>,
  +sg: T.Sign,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String,
  hq: {Bool.and(saw, Bool.not(us)) == False{} : Bool},
  ih: n1.F.G(tt, sg, T.dec.go(ds, 10, T.dig.val(cc)), "")
) -> {n1.fsh(T.num.go(cc <> tt, T.Num{T.NFrac{}, sg, 10, ds, us, saw, why}))
  == Bool.and(D1.abnf.zero_prefixable_int(D1.abnf.cut.pre(cc <> tt, D1.ACutExp{})),
  D1.abnf.opt_exp(D1.abnf.cut.post(cc <> tt, D1.ACutExp{}))) : Bool}:
  n1.Fu.go(Char.is_digit(cc), Char.is_eq(cc, '_'), Char.is_eq(cc, 'e'), Char.is_eq(cc, 'E'), cc, tt, sg, ds, us, saw,
    why, {==}, hq, ih)

# what the fraction's underscore lemma claims: after an underscore, the scan
# finishes as a float exactly when the rest, cut at its first e, is a
# zero-prefixable-int and then an optional exp
def n1.F.U(+tt: List<&2, Char>, +sg: T.Sign, +ds: List<&2, U32>, +why: String) -> Type:
  {n1.fsh(T.num.go(tt, T.Num{T.NFrac{}, sg, 10, ds, True{}, True{}, why}))
    == Bool.and(D1.abnf.zero_prefixable_int(D1.abnf.cut.pre(tt, D1.ACutExp{})),
    D1.abnf.opt_exp(D1.abnf.cut.post(tt, D1.ACutExp{}))) : Bool}

# the character after a fraction's digit
def n1.F.go(
  dd: Bool,
  uu: Bool,
  e1: Bool,
  e2: Bool,
  +cc: Char,
  +tt: List<&2, Char>,
  +sg: T.Sign,
  +ds: List<&2, U32>,
  +why: String,
  +ed: {Char.is_digit(cc) == dd : Bool},
  eu: {Char.is_eq(cc, '_') == uu : Bool},
  ee1: {Char.is_eq(cc, 'e') == e1 : Bool},
  ee2: {Char.is_eq(cc, 'E') == e2 : Bool},
  ihd: n1.F.G(tt, sg, T.dec.go(ds, 10, T.dig.val(cc)), ""),
  ihu: n1.F.U(tt, sg, ds, why),
  ihe: {n1.fsh(T.num.go(tt, M3.n1.se(sg))) == D1.abnf.float_exp_part(tt) : Bool}
) -> {n1.fsh(T.num.go(tt, T.num.frac.go(dd, uu, e1, e2, n1.sf(sg, ds, why), cc))) == Bool.and(
  D1.abnf.dec_rep(D1.abnf.cut.pre(cc <> tt, D1.ACutExp{})),
  D1.abnf.opt_exp(D1.abnf.cut.post(cc <> tt, D1.ACutExp{}))) : Bool}:
  match dd:
    case True{}:
      %n1.pre.no(D1.ACutExp{}, cc, tt, n1.at.dig(D1.ACutExp{}, cc, ed)) : {n1.fsh(T.num.go(tt,
        T.num.digit.ok(T.dig.ok(T.dig.val(cc), 10), cc, T.NFrac{}, sg, 10, ds))) ==
        Bool.and(D1.abnf.dec_rep(_), D1.abnf.opt_exp(D1.abnf.cut.post(cc <> tt, D1.ACutExp{}))) : Bool}
      %n1.post.no(D1.ACutExp{}, cc, tt, n1.at.dig(D1.ACutExp{}, cc, ed)) : {n1.fsh(T.num.go(tt,
        T.num.digit.ok(T.dig.ok(T.dig.val(cc), 10), cc, T.NFrac{}, sg, 10, ds))) ==
        Bool.and(D1.abnf.dec_rep(cc <> D1.abnf.cut.pre(tt, D1.ACutExp{})), D1.abnf.opt_exp(_)) : Bool}
      %M3.n1.rep.d(cc, D1.abnf.cut.pre(tt, D1.ACutExp{}), ed) : {n1.fsh(T.num.go(tt,
        T.num.digit.ok(T.dig.ok(T.dig.val(cc), 10), cc, T.NFrac{}, sg, 10, ds))) == Bool.and(_,
        D1.abnf.opt_exp(D1.abnf.cut.post(tt, D1.ACutExp{}))) : Bool}
      %Equal.sym(Bool, T.dig.ok(T.dig.val(cc), 10), True{}, M3.n1.dok10(cc, ed)) : {n1.fsh(T.num.go(tt,
        T.num.digit.ok(_, cc, T.NFrac{}, sg, 10, ds))) == Bool.and(D1.abnf.dec_rep(D1.abnf.cut.pre(tt,
        D1.ACutExp{})), D1.abnf.opt_exp(D1.abnf.cut.post(tt, D1.ACutExp{}))) : Bool}
      ihd
    case False{}:
      match uu:
        case True{}:
          %Equal.sym(Char, cc, '_', Eq.char_eq_true(cc, '_', eu)) : {n1.fsh(T.num.go(tt,
            T.Num{T.NFrac{}, sg, 10, ds, True{}, True{}, why})) == Bool.and(D1.abnf.dec_rep(D1.abnf.cut.pre(_ <> tt,
            D1.ACutExp{})), D1.abnf.opt_exp(D1.abnf.cut.post(_ <> tt, D1.ACutExp{}))) : Bool}
          %M3.n1.rep.u(D1.abnf.cut.pre(tt, D1.ACutExp{})) : {n1.fsh(T.num.go(tt,
            T.Num{T.NFrac{}, sg, 10, ds, True{}, True{}, why})) == Bool.and(_, D1.abnf.opt_exp(D1.abnf.cut.post(tt,
            D1.ACutExp{}))) : Bool}
          ihu
        case False{}:
          match e1:
            case True{}:
              %Equal.sym(Char, cc, 'e', Eq.char_eq_true(cc, 'e', ee1)) : {n1.fsh(T.num.go(tt, M3.n1.se(sg))) ==
                Bool.and(D1.abnf.dec_rep(D1.abnf.cut.pre(_ <> tt, D1.ACutExp{})),
                D1.abnf.opt_exp(D1.abnf.cut.post(_ <> tt, D1.ACutExp{}))) : Bool}
              ihe
            case False{}:
              match e2:
                case True{}:
                  %Equal.sym(Char, cc, 'E', Eq.char_eq_true(cc, 'E', ee2)) : {n1.fsh(T.num.go(tt, M3.n1.se(sg))) ==
                    Bool.and(D1.abnf.dec_rep(D1.abnf.cut.pre(_ <> tt, D1.ACutExp{})),
                    D1.abnf.opt_exp(D1.abnf.cut.post(_ <> tt, D1.ACutExp{}))) : Bool}
                  ihe
                case False{}:
                  %n1.pre.no(D1.ACutExp{}, cc, tt, n1.at.e(cc, ee1, ee2)) : {n1.fsh(T.num.go(tt,
                    T.num.bad(n1.sf(sg, ds, why), "invalid fraction"))) == Bool.and(D1.abnf.dec_rep(_),
                    D1.abnf.opt_exp(D1.abnf.cut.post(cc <> tt, D1.ACutExp{}))) : Bool}
                  %M3.n1.rep.n(cc, D1.abnf.cut.pre(tt, D1.ACutExp{}), ed, eu) : {n1.fsh(T.num.go(tt,
                    T.num.bad(n1.sf(sg, ds, why), "invalid fraction"))) == Bool.and(_,
                    D1.abnf.opt_exp(D1.abnf.cut.post(cc <> tt, D1.ACutExp{}))) : Bool}
                  n1.fsh.bad(tt, "invalid fraction")

# after a digit of a fraction, the scan finishes as a float exactly when the
# rest, cut at its first e, is the repetition and then an optional exp
def n1.F(rest: List<&2, Char>, +sg: T.Sign, +ds: List<&2, U32>, +why: String) -> n1.F.G(rest, sg, ds, why):
  match rest:
    case []:
      {==}
    case +hh <> tt:
      match tt:
        case []:
          n1.F.go(Char.is_digit(hh), Char.is_eq(hh, '_'), Char.is_eq(hh, 'e'), Char.is_eq(hh, 'E'), hh, [], sg, ds, why,
            {==}, {==}, {==}, {==}, n1.F([], sg, T.dec.go(ds, 10, T.dig.val(hh)), ""), {==}, n1.E([], sg))
        case +h2 <> +t2:
          n1.F.go(Char.is_digit(hh), Char.is_eq(hh, '_'), Char.is_eq(hh, 'e'), Char.is_eq(hh, 'E'), hh, h2 <> t2, sg,
            ds, why, {==}, {==}, {==}, {==}, n1.F(h2 <> t2, sg, T.dec.go(ds, 10, T.dig.val(hh)), ""),
            n1.Fu(h2, t2, sg, ds, True{}, True{}, why, {==}, n1.F(t2, sg, T.dec.go(ds, 10, T.dig.val(h2)), "")),
            n1.E(h2 <> t2, sg))

# what the decimal point lemma claims
def n1.F0.G(+rest: List<&2, Char>, +sg: T.Sign) -> Type:
  {n1.fsh(T.num.go(rest, M3.n1.sf0(sg))) == Bool.and(D1.abnf.zero_prefixable_int(D1.abnf.cut.pre(rest,
    D1.ACutExp{})), D1.abnf.opt_exp(D1.abnf.cut.post(rest, D1.ACutExp{}))) : Bool}

# after a decimal point, the scan finishes as a float exactly when the rest,
# cut at its first e, is a zero-prefixable-int and then an optional exp
def n1.F0(
  rest: List<&2, Char>,
  +sg: T.Sign
) -> {n1.fsh(T.num.go(rest, M3.n1.sf0(sg))) == Bool.and( D1.abnf.zero_prefixable_int(D1.abnf.cut.pre(rest,
  D1.ACutExp{})), D1.abnf.opt_exp(D1.abnf.cut.post(rest, D1.ACutExp{}))) : Bool}:
  match rest:
    case []:
      {==}
    case +hh <> +tt:
      n1.Fu(hh, tt, sg, [], False{}, False{}, "", {==}, n1.F(tt, sg, T.dec.go([], 10, T.dig.val(hh)), ""))

# A prefixed integer's scan. Its state stays NBase until it fails, so it never
# holds a float.

# whether a numeral kind is a prefixed integer's, or a failure
def n1.isb.nk(nk: T.NK) -> Bool:
  match nk:
    case T.NBase{}:
      True{}
    case T.NBad{}:
      True{}
    case _k:
      False{}

# whether a numeral scan is in a prefixed integer or has failed
def n1.isb(st: T.Num) -> Bool:
  match st:
    case T.Num{nk, _sign, _base, _ds, _us, _saw, _why}:
      n1.isb.nk(nk)

# a digit of a prefixed integer, taken or refused
def n1.isb.digit(
  ok: Bool,
  +cc: Char,
  +sg: T.Sign,
  +base: U32,
  +ds: List<&2, U32>
) -> {n1.isb(T.num.digit.ok(ok, cc, T.NBase{}, sg, base, ds)) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

# an underscore of a prefixed integer, taken or refused
def n1.isb.us(
  ok: Bool,
  +sg: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +why: String
) -> {n1.isb(T.num.us.go(ok, T.NBase{}, sg, base, ds, why)) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

# the character after a prefixed integer's digit or underscore
def n1.isb.based(
  uu: Bool,
  +cc: Char,
  +sg: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String
) -> {n1.isb(T.num.based.go(uu, T.Num{T.NBase{}, sg, base, ds, us, saw, why}, cc)) == True{} : Bool}:
  match uu:
    case True{}:
      n1.isb.us(Bool.and(saw, Bool.not(us)), sg, base, ds, why)
    case False{}:
      n1.isb.digit(T.dig.ok(T.dig.val(cc), base), cc, sg, base, ds)

# a step keeps a scan in a prefixed integer or failed
def n1.isb.step(
  +st: T.Num,
  +cc: Char,
  hs: {n1.isb(st) == True{} : Bool}
) -> {n1.isb(T.num.step(st, cc)) == True{} : Bool}:
  match st:
    case T.Num{nk, +sg, +base, +ds, +us, +saw, +why}:
      match nk:
        case T.NBase{}:
          n1.isb.based(Char.is_eq(cc, '_'), cc, sg, base, ds, us, saw, why)
        case T.NBad{}:
          {==}
        case T.NLead{}:
          Eq.bit.absurd(&2, {n1.isb(T.num.step(T.Num{T.NLead{}, sg, base, ds, us, saw, why}, cc)) == True{} : Bool}, hs)
        case T.NSign{}:
          Eq.bit.absurd(&2, {n1.isb(T.num.step(T.Num{T.NSign{}, sg, base, ds, us, saw, why}, cc)) == True{} : Bool}, hs)
        case T.NZero{}:
          Eq.bit.absurd(&2, {n1.isb(T.num.step(T.Num{T.NZero{}, sg, base, ds, us, saw, why}, cc)) == True{} : Bool}, hs)
        case T.NDig{}:
          Eq.bit.absurd(&2, {n1.isb(T.num.step(T.Num{T.NDig{}, sg, base, ds, us, saw, why}, cc)) == True{} : Bool}, hs)
        case T.NFrac{}:
          Eq.bit.absurd(&2, {n1.isb(T.num.step(T.Num{T.NFrac{}, sg, base, ds, us, saw, why}, cc)) == True{} : Bool}, hs)
        case T.NExp{}:
          Eq.bit.absurd(&2, {n1.isb(T.num.step(T.Num{T.NExp{}, sg, base, ds, us, saw, why}, cc)) == True{} : Bool}, hs)
        case T.NEDig{}:
          Eq.bit.absurd(&2, {n1.isb(T.num.step(T.Num{T.NEDig{}, sg, base, ds, us, saw, why}, cc)) == True{} : Bool}, hs)

# a scan in a prefixed integer or failed never finishes as a float
def n1.bcls(
  rest: List<&2, Char>,
  +st: T.Num,
  hs: {n1.isb(st) == True{} : Bool}
) -> {n1.fsh(T.num.go(rest, st)) == False{} : Bool}:
  match rest:
    case []:
      match st:
        case T.Num{nk, _sign, _base, _ds, us, saw, _why}:
          match nk:
            case T.NBase{}:
              {==}
            case T.NBad{}:
              {==}
            case T.NLead{}:
              Eq.bit.absurd(&2, {Bool.and(n1.fsh.nk(T.NLead{}, saw), Bool.not(us)) == False{} : Bool}, hs)
            case T.NSign{}:
              Eq.bit.absurd(&2, {Bool.and(n1.fsh.nk(T.NSign{}, saw), Bool.not(us)) == False{} : Bool}, hs)
            case T.NZero{}:
              Eq.bit.absurd(&2, {Bool.and(n1.fsh.nk(T.NZero{}, saw), Bool.not(us)) == False{} : Bool}, hs)
            case T.NDig{}:
              Eq.bit.absurd(&2, {Bool.and(n1.fsh.nk(T.NDig{}, saw), Bool.not(us)) == False{} : Bool}, hs)
            case T.NFrac{}:
              Eq.bit.absurd(&2, {Bool.and(n1.fsh.nk(T.NFrac{}, saw), Bool.not(us)) == False{} : Bool}, hs)
            case T.NExp{}:
              Eq.bit.absurd(&2, {Bool.and(n1.fsh.nk(T.NExp{}, saw), Bool.not(us)) == False{} : Bool}, hs)
            case T.NEDig{}:
              Eq.bit.absurd(&2, {Bool.and(n1.fsh.nk(T.NEDig{}, saw), Bool.not(us)) == False{} : Bool}, hs)
    case +hh <> tt:
      n1.bcls(tt, T.num.step(st, hh), n1.isb.step(st, hh, hs))

# The integer part. After a digit of it the scan finishes as a float exactly
# when the rest, cut at its first dot or e, is the repetition and then an exp
# or a frac with an optional exp.

# the exp or frac [ exp ] a float's integer part is followed by
def n1.fq(+pp: List<&2, Char>) -> Bool:
  Bool.or(D1.abnf.exp(pp), D1.abnf.frac_exp(pp))

# what the integer-part lemma claims
def n1.D.G(rest: List<&2, Char>, +sg: T.Sign, +ds: List<&2, U32>, +why: String) -> Type:
  {n1.fsh(T.num.go(rest, M3.n1.sd(sg, ds, why))) == Bool.and(D1.abnf.dec_rep(D1.abnf.cut.pre(rest, D1.ACutDot{})),
    n1.fq(D1.abnf.cut.post(rest, D1.ACutDot{}))) : Bool}

# after an underscore in an integer part, a character that is no digit fails
def n1.Du.bad(
  uu: Bool,
  pp: Bool,
  e1: Bool,
  e2: Bool,
  +cc: Char,
  +tt: List<&2, Char>,
  +sg: T.Sign,
  +ds: List<&2, U32>,
  +why: String
) -> {n1.fsh(T.num.go(tt, T.num.digs.go(False{}, uu, pp, e1, e2, T.Num{T.NDig{}, sg, 10, ds, True{}, True{}, why},
  cc))) == False{} : Bool}:
  match uu:
    case True{}:
      n1.fsh.bad(tt, "invalid underscore")
    case False{}:
      match pp:
        case True{}:
          n1.fsh.bad(tt, "invalid fraction")
        case False{}:
          match e1:
            case True{}:
              n1.fsh.bad(tt, "invalid exponent")
            case False{}:
              match e2:
                case True{}:
                  n1.fsh.bad(tt, "invalid exponent")
                case False{}:
                  n1.fsh.bad(tt, "invalid number")

# the character after an underscore in an integer part
def n1.Du.go(
  dd: Bool,
  uu: Bool,
  pp: Bool,
  e1: Bool,
  e2: Bool,
  +cc: Char,
  +tt: List<&2, Char>,
  +sg: T.Sign,
  +ds: List<&2, U32>,
  +why: String,
  +ed: {Char.is_digit(cc) == dd : Bool},
  ih: n1.D.G(tt, sg, T.dec.go(ds, 10, T.dig.val(cc)), "")
) -> {n1.fsh(T.num.go(tt, T.num.digs.go(dd, uu, pp, e1, e2, T.Num{T.NDig{}, sg, 10, ds, True{}, True{}, why}, cc)))
  == Bool.and(D1.abnf.zero_prefixable_int(D1.abnf.cut.pre(cc <> tt, D1.ACutDot{})),
  n1.fq(D1.abnf.cut.post(cc <> tt, D1.ACutDot{}))) : Bool}:
  match dd:
    case True{}:
      %n1.pre.no(D1.ACutDot{}, cc, tt, n1.at.dig(D1.ACutDot{}, cc, ed)) : {n1.fsh(T.num.go(tt,
        T.num.digit.ok(T.dig.ok(T.dig.val(cc), 10), cc, T.NDig{}, sg, 10, ds))) ==
        Bool.and(D1.abnf.zero_prefixable_int(_), n1.fq(D1.abnf.cut.post(cc <> tt, D1.ACutDot{}))) : Bool}
      %n1.post.no(D1.ACutDot{}, cc, tt, n1.at.dig(D1.ACutDot{}, cc, ed)) : {n1.fsh(T.num.go(tt,
        T.num.digit.ok(T.dig.ok(T.dig.val(cc), 10), cc, T.NDig{}, sg, 10, ds))) ==
        Bool.and(D1.abnf.zero_prefixable_int(cc <> D1.abnf.cut.pre(tt, D1.ACutDot{})), n1.fq(_)) : Bool}
      %M3.n1.zpi.d(cc, D1.abnf.cut.pre(tt, D1.ACutDot{}), ed) : {n1.fsh(T.num.go(tt,
        T.num.digit.ok(T.dig.ok(T.dig.val(cc), 10), cc, T.NDig{}, sg, 10, ds))) == Bool.and(_,
        n1.fq(D1.abnf.cut.post(tt, D1.ACutDot{}))) : Bool}
      %Equal.sym(Bool, T.dig.ok(T.dig.val(cc), 10), True{}, M3.n1.dok10(cc, ed)) : {n1.fsh(T.num.go(tt,
        T.num.digit.ok(_, cc, T.NDig{}, sg, 10, ds))) == Bool.and(D1.abnf.dec_rep(D1.abnf.cut.pre(tt,
        D1.ACutDot{})), n1.fq(D1.abnf.cut.post(tt, D1.ACutDot{}))) : Bool}
      ih
    case False{}:
      Equal.trans(Bool, n1.fsh(T.num.go(tt, T.num.digs.go(False{}, uu, pp, e1, e2, T.Num{T.NDig{}, sg, 10, ds, True{},
        True{}, why}, cc))), False{}, Bool.and(D1.abnf.zero_prefixable_int(D1.abnf.cut.pre(cc <> tt,
        D1.ACutDot{})), n1.fq(D1.abnf.cut.post(cc <> tt, D1.ACutDot{}))),
        n1.Du.bad(uu, pp, e1, e2, cc, tt, sg, ds, why),
        n1.zpi.cut(D1.abnf.cut.at(D1.ACutDot{}, cc), cc, D1.abnf.cut.pre(tt, D1.ACutDot{}),
          n1.fq(D1.abnf.cut.post(cc <> tt, D1.ACutDot{})), ed))

# after an underscore in an integer part, with a character and the rest
def n1.Du(
  +cc: Char,
  +tt: List<&2, Char>,
  +sg: T.Sign,
  +ds: List<&2, U32>,
  +why: String,
  ih: n1.D.G(tt, sg, T.dec.go(ds, 10, T.dig.val(cc)), "")
) -> {n1.fsh(T.num.go(cc <> tt, T.Num{T.NDig{}, sg, 10, ds, True{}, True{}, why}))
  == Bool.and(D1.abnf.zero_prefixable_int(D1.abnf.cut.pre(cc <> tt, D1.ACutDot{})),
  n1.fq(D1.abnf.cut.post(cc <> tt, D1.ACutDot{}))) : Bool}:
  n1.Du.go(Char.is_digit(cc), Char.is_eq(cc, '_'), Char.is_eq(cc, '.'), Char.is_eq(cc, 'e'), Char.is_eq(cc, 'E'), cc,
    tt, sg, ds, why, {==}, ih)

# what the integer part's underscore lemma claims: after an underscore, the
# scan finishes as a float exactly when the rest, cut at its first dot or e,
# is a zero-prefixable-int and then an exp or a frac with an optional exp
def n1.D.U(+tt: List<&2, Char>, +sg: T.Sign, +ds: List<&2, U32>, +why: String) -> Type:
  {n1.fsh(T.num.go(tt, T.Num{T.NDig{}, sg, 10, ds, True{}, True{}, why}))
    == Bool.and(D1.abnf.zero_prefixable_int(D1.abnf.cut.pre(tt, D1.ACutDot{})),
    n1.fq(D1.abnf.cut.post(tt, D1.ACutDot{}))) : Bool}

# the character after a digit of an integer part
def n1.D.go(
  dd: Bool,
  uu: Bool,
  pp: Bool,
  e1: Bool,
  e2: Bool,
  +cc: Char,
  +tt: List<&2, Char>,
  +sg: T.Sign,
  +ds: List<&2, U32>,
  +why: String,
  +ed: {Char.is_digit(cc) == dd : Bool},
  +eu: {Char.is_eq(cc, '_') == uu : Bool},
  +ep: {Char.is_eq(cc, '.') == pp : Bool},
  +ee1: {Char.is_eq(cc, 'e') == e1 : Bool},
  +ee2: {Char.is_eq(cc, 'E') == e2 : Bool},
  ihd: n1.D.G(tt, sg, T.dec.go(ds, 10, T.dig.val(cc)), ""),
  ihu: n1.D.U(tt, sg, ds, why),
  ihp: n1.F0.G(tt, sg),
  ihe: {n1.fsh(T.num.go(tt, M3.n1.se(sg))) == D1.abnf.float_exp_part(tt) : Bool}
) -> {n1.fsh(T.num.go(tt, T.num.digs.go(dd, uu, pp, e1, e2, M3.n1.sd(sg, ds, why), cc))) == Bool.and(
  D1.abnf.dec_rep(D1.abnf.cut.pre(cc <> tt, D1.ACutDot{})), n1.fq(D1.abnf.cut.post(cc <> tt, D1.ACutDot{})))
  : Bool}:
  match dd:
    case True{}:
      %n1.pre.no(D1.ACutDot{}, cc, tt, n1.at.dig(D1.ACutDot{}, cc, ed)) : {n1.fsh(T.num.go(tt,
        T.num.digit.ok(T.dig.ok(T.dig.val(cc), 10), cc, T.NDig{}, sg, 10, ds))) ==
        Bool.and(D1.abnf.dec_rep(_), n1.fq(D1.abnf.cut.post(cc <> tt, D1.ACutDot{}))) : Bool}
      %n1.post.no(D1.ACutDot{}, cc, tt, n1.at.dig(D1.ACutDot{}, cc, ed)) : {n1.fsh(T.num.go(tt,
        T.num.digit.ok(T.dig.ok(T.dig.val(cc), 10), cc, T.NDig{}, sg, 10, ds))) ==
        Bool.and(D1.abnf.dec_rep(cc <> D1.abnf.cut.pre(tt, D1.ACutDot{})), n1.fq(_)) : Bool}
      %M3.n1.rep.d(cc, D1.abnf.cut.pre(tt, D1.ACutDot{}), ed) : {n1.fsh(T.num.go(tt,
        T.num.digit.ok(T.dig.ok(T.dig.val(cc), 10), cc, T.NDig{}, sg, 10, ds))) == Bool.and(_,
        n1.fq(D1.abnf.cut.post(tt, D1.ACutDot{}))) : Bool}
      %Equal.sym(Bool, T.dig.ok(T.dig.val(cc), 10), True{}, M3.n1.dok10(cc, ed)) : {n1.fsh(T.num.go(tt,
        T.num.digit.ok(_, cc, T.NDig{}, sg, 10, ds))) == Bool.and(D1.abnf.dec_rep(D1.abnf.cut.pre(tt,
        D1.ACutDot{})), n1.fq(D1.abnf.cut.post(tt, D1.ACutDot{}))) : Bool}
      ihd
    case False{}:
      match uu:
        case True{}:
          %Equal.sym(Char, cc, '_', Eq.char_eq_true(cc, '_', eu)) : {n1.fsh(T.num.go(tt,
            T.Num{T.NDig{}, sg, 10, ds, True{}, True{}, why})) == Bool.and(D1.abnf.dec_rep(D1.abnf.cut.pre(_ <> tt,
            D1.ACutDot{})), n1.fq(D1.abnf.cut.post(_ <> tt, D1.ACutDot{}))) : Bool}
          %M3.n1.rep.u(D1.abnf.cut.pre(tt, D1.ACutDot{})) : {n1.fsh(T.num.go(tt,
            T.Num{T.NDig{}, sg, 10, ds, True{}, True{}, why})) == Bool.and(_, n1.fq(D1.abnf.cut.post(tt,
            D1.ACutDot{}))) : Bool}
          ihu
        case False{}:
          match pp:
            case True{}:
              %Equal.sym(Char, cc, '.', Eq.char_eq_true(cc, '.', ep)) : {n1.fsh(T.num.go(tt, M3.n1.sf0(sg))) ==
                Bool.and(D1.abnf.dec_rep(D1.abnf.cut.pre(_ <> tt, D1.ACutDot{})),
                n1.fq(D1.abnf.cut.post(_ <> tt, D1.ACutDot{}))) : Bool}
              ihp
            case False{}:
              match e1:
                case True{}:
                  %Equal.sym(Char, cc, 'e', Eq.char_eq_true(cc, 'e', ee1)) : {n1.fsh(T.num.go(tt, M3.n1.se(sg))) ==
                    Bool.and(D1.abnf.dec_rep(D1.abnf.cut.pre(_ <> tt, D1.ACutDot{})),
                    n1.fq(D1.abnf.cut.post(_ <> tt, D1.ACutDot{}))) : Bool}
                  M3.n1.orf.eq(n1.fsh(T.num.go(tt, M3.n1.se(sg))), D1.abnf.float_exp_part(tt), ihe)
                case False{}:
                  match e2:
                    case True{}:
                      %Equal.sym(Char, cc, 'E', Eq.char_eq_true(cc, 'E', ee2)) : {n1.fsh(T.num.go(tt, M3.n1.se(sg))) ==
                        Bool.and(D1.abnf.dec_rep(D1.abnf.cut.pre(_ <> tt, D1.ACutDot{})),
                        n1.fq(D1.abnf.cut.post(_ <> tt, D1.ACutDot{}))) : Bool}
                      M3.n1.orf.eq(n1.fsh(T.num.go(tt, M3.n1.se(sg))), D1.abnf.float_exp_part(tt), ihe)
                    case False{}:
                      %n1.pre.no(D1.ACutDot{}, cc, tt, n1.at.d(cc, ep, ee1, ee2)) : {n1.fsh(T.num.go(tt,
                        T.num.bad(M3.n1.sd(sg, ds, why), "invalid number"))) == Bool.and(D1.abnf.dec_rep(_),
                        n1.fq(D1.abnf.cut.post(cc <> tt, D1.ACutDot{}))) : Bool}
                      %M3.n1.rep.n(cc, D1.abnf.cut.pre(tt, D1.ACutDot{}), ed, eu) : {n1.fsh(T.num.go(tt,
                        T.num.bad(M3.n1.sd(sg, ds, why), "invalid number"))) == Bool.and(_,
                        n1.fq(D1.abnf.cut.post(cc <> tt, D1.ACutDot{}))) : Bool}
                      n1.fsh.bad(tt, "invalid number")

# after a digit of an integer part, the scan finishes as a float exactly when
# the rest, cut at its first dot or e, is the repetition and then an exp or a
# frac with an optional exp
def n1.D(rest: List<&2, Char>, +sg: T.Sign, +ds: List<&2, U32>, +why: String) -> n1.D.G(rest, sg, ds, why):
  match rest:
    case []:
      {==}
    case +hh <> tt:
      match tt:
        case []:
          n1.D.go(Char.is_digit(hh), Char.is_eq(hh, '_'), Char.is_eq(hh, '.'), Char.is_eq(hh, 'e'), Char.is_eq(hh, 'E'),
            hh, [], sg, ds, why, {==}, {==}, {==}, {==}, {==}, n1.D([], sg, T.dec.go(ds, 10, T.dig.val(hh)), ""), {==},
            n1.F0([], sg), n1.E([], sg))
        case +h2 <> +t2:
          n1.D.go(Char.is_digit(hh), Char.is_eq(hh, '_'), Char.is_eq(hh, '.'), Char.is_eq(hh, 'e'), Char.is_eq(hh, 'E'),
            hh, h2 <> t2, sg, ds, why, {==}, {==}, {==}, {==}, {==},
            n1.D(h2 <> t2, sg, T.dec.go(ds, 10, T.dig.val(hh)), ""),
            n1.Du(h2, t2, sg, ds, why, n1.D(t2, sg, T.dec.go(ds, 10, T.dig.val(h2)), "")),
            n1.F0(h2 <> t2, sg), n1.E(h2 <> t2, sg))

# what the leading zero lemma claims
def n1.Z.G(+rest: List<&2, Char>, +sg: T.Sign) -> Type:
  {n1.fsh(T.num.go(rest, M3.n1.sz(sg))) == Bool.and(List.is_empty(&2, Char, D1.abnf.cut.pre(rest, D1.ACutDot{})),
    n1.fq(D1.abnf.cut.post(rest, D1.ACutDot{}))) : Bool}

# the character after a leading zero: a prefix, a dot, an exponent, or
# anything else, which fails
def n1.Z.go(
  xx: Bool,
  oo: Bool,
  bb: Bool,
  pp: Bool,
  e1: Bool,
  e2: Bool,
  +cc: Char,
  +tt: List<&2, Char>,
  +sg: T.Sign,
  +exx: {Char.is_eq(cc, 'x') == xx : Bool},
  +eoo: {Char.is_eq(cc, 'o') == oo : Bool},
  +ebb: {Char.is_eq(cc, 'b') == bb : Bool},
  +ep: {Char.is_eq(cc, '.') == pp : Bool},
  +ee1: {Char.is_eq(cc, 'e') == e1 : Bool},
  +ee2: {Char.is_eq(cc, 'E') == e2 : Bool},
  ihp: n1.F0.G(tt, sg),
  ihe: {n1.fsh(T.num.go(tt, M3.n1.se(sg))) == D1.abnf.float_exp_part(tt) : Bool}
) -> {n1.fsh(T.num.go(tt, T.num.zero.go(xx, oo, bb, pp, e1, e2, M3.n1.sz(sg), cc))) == Bool.and(List.is_empty(&2, Char,
  D1.abnf.cut.pre(cc <> tt, D1.ACutDot{})), n1.fq(D1.abnf.cut.post(cc <> tt, D1.ACutDot{}))) : Bool}:
  match xx:
    case True{}:
      %Equal.sym(Char, cc, 'x', Eq.char_eq_true(cc, 'x', exx)) : {n1.fsh(T.num.go(tt, T.num.base(M3.n1.sz(sg), 16))) ==
        Bool.and(List.is_empty(&2, Char, D1.abnf.cut.pre(_ <> tt, D1.ACutDot{})),
        n1.fq(D1.abnf.cut.post(_ <> tt, D1.ACutDot{}))) : Bool}
      n1.bcls(tt, T.num.base(M3.n1.sz(sg), 16), {==})
    case False{}:
      match oo:
        case True{}:
          %Equal.sym(Char, cc, 'o', Eq.char_eq_true(cc, 'o', eoo)) : {n1.fsh(T.num.go(tt, T.num.base(M3.n1.sz(sg),
              8))) ==
            Bool.and(List.is_empty(&2, Char, D1.abnf.cut.pre(_ <> tt, D1.ACutDot{})),
            n1.fq(D1.abnf.cut.post(_ <> tt, D1.ACutDot{}))) : Bool}
          n1.bcls(tt, T.num.base(M3.n1.sz(sg), 8), {==})
        case False{}:
          match bb:
            case True{}:
              %Equal.sym(Char, cc, 'b', Eq.char_eq_true(cc, 'b', ebb)) : {n1.fsh(T.num.go(tt, T.num.base(M3.n1.sz(sg),
                2))) == Bool.and(List.is_empty(&2, Char, D1.abnf.cut.pre(_ <> tt, D1.ACutDot{})),
                n1.fq(D1.abnf.cut.post(_ <> tt, D1.ACutDot{}))) : Bool}
              n1.bcls(tt, T.num.base(M3.n1.sz(sg), 2), {==})
            case False{}:
              match pp:
                case True{}:
                  %Equal.sym(Char, cc, '.', Eq.char_eq_true(cc, '.', ep)) : {n1.fsh(T.num.go(tt, M3.n1.sf0(sg))) ==
                    Bool.and(List.is_empty(&2, Char, D1.abnf.cut.pre(_ <> tt, D1.ACutDot{})),
                    n1.fq(D1.abnf.cut.post(_ <> tt, D1.ACutDot{}))) : Bool}
                  ihp
                case False{}:
                  match e1:
                    case True{}:
                      %Equal.sym(Char, cc, 'e', Eq.char_eq_true(cc, 'e', ee1)) : {n1.fsh(T.num.go(tt, M3.n1.se(sg))) ==
                        Bool.and(List.is_empty(&2, Char, D1.abnf.cut.pre(_ <> tt, D1.ACutDot{})),
                        n1.fq(D1.abnf.cut.post(_ <> tt, D1.ACutDot{}))) : Bool}
                      M3.n1.orf.eq(n1.fsh(T.num.go(tt, M3.n1.se(sg))), D1.abnf.float_exp_part(tt), ihe)
                    case False{}:
                      match e2:
                        case True{}:
                          %Equal.sym(Char, cc, 'E', Eq.char_eq_true(cc, 'E', ee2)) : {n1.fsh(T.num.go(tt,
                            M3.n1.se(sg))) == Bool.and(List.is_empty(&2, Char, D1.abnf.cut.pre(_ <> tt,
                            D1.ACutDot{})), n1.fq(D1.abnf.cut.post(_ <> tt, D1.ACutDot{}))) : Bool}
                          M3.n1.orf.eq(n1.fsh(T.num.go(tt, M3.n1.se(sg))), D1.abnf.float_exp_part(tt), ihe)
                        case False{}:
                          %n1.pre.no(D1.ACutDot{}, cc, tt, n1.at.d(cc, ep, ee1, ee2)) : {n1.fsh(T.num.go(tt,
                            T.num.bad(M3.n1.sz(sg), "invalid number"))) == Bool.and(List.is_empty(&2, Char, _),
                            n1.fq(D1.abnf.cut.post(cc <> tt, D1.ACutDot{}))) : Bool}
                          n1.fsh.bad(tt, "invalid number")

# after a leading zero, the scan finishes as a float exactly when the rest
# starts at a cut, with an exp or a frac and an optional exp from there
def n1.Z(
  rest: List<&2, Char>,
  +sg: T.Sign
) -> {n1.fsh(T.num.go(rest, M3.n1.sz(sg))) == Bool.and(List.is_empty(&2, Char, D1.abnf.cut.pre(rest, D1.ACutDot{})),
  n1.fq(D1.abnf.cut.post(rest, D1.ACutDot{}))) : Bool}:
  match rest:
    case []:
      {==}
    case +hh <> +tt:
      n1.Z.go(Char.is_eq(hh, 'x'), Char.is_eq(hh, 'o'), Char.is_eq(hh, 'b'), Char.is_eq(hh, '.'), Char.is_eq(hh, 'e'),
        Char.is_eq(hh, 'E'), hh, tt, sg, {==}, {==}, {==}, {==}, {==}, {==}, n1.F0(tt, sg), n1.E(tt, sg))

# an unsigned-dec-int that starts with 0 is 0 alone
def n1.udi.z(xs: List<&2, Char>) -> {List.is_empty(&2, Char, xs) == D1.abnf.unsigned_dec_int('0' <> xs) : Bool}:
  match xs:
    case []:
      {==}
    case _h <> _t:
      {==}

# an unsigned-dec-int cut at c, where c is no digit, is none, whatever
# follows
def n1.udi.cut(
  cut: Bool,
  +cc: Char,
  +xs: List<&2, Char>,
  +more: Bool,
  hc: {Char.is_digit(cc) == False{} : Bool}
) -> {False{} == Bool.and(D1.abnf.unsigned_dec_int(D1.abnf.cut.pre.pick(cut, cc, xs)), more) : Bool}:
  match cut:
    case True{}:
      {==}
    case False{}:
      %M3.n1.udi.n(cc, xs, hc) : {False{} == Bool.and(_, more) : Bool}
      {==}

# what the after-sign lemma claims: the scan finishes as a float exactly when
# the rest, cut at its first dot or e, is an unsigned-dec-int and then an exp
# or a frac with an optional exp
def n1.S.R(+rest: List<&2, Char>) -> Bool:
  Bool.and(D1.abnf.unsigned_dec_int(D1.abnf.cut.pre(rest, D1.ACutDot{})),
    n1.fq(D1.abnf.cut.post(rest, D1.ACutDot{})))

# the first character of an unsigned numeral that is no sign: a zero, a
# digit, or anything else, which fails
def n1.S2.go(
  zz: Bool,
  dd: Bool,
  +cc: Char,
  +tt: List<&2, Char>,
  +sg: T.Sign,
  +ez: {Char.is_eq(cc, '0') == zz : Bool},
  +ed: {Char.is_digit(cc) == dd : Bool},
  ihz: n1.Z.G(tt, sg),
  ihd: n1.D.G(tt, sg, T.dec.go([], 10, T.dig.val(cc)), "")
) -> {n1.fsh(T.num.go(tt, T.num.lead.go(False{}, False{}, zz, dd, M3.n1.sl(sg), cc))) == n1.S.R(cc <> tt) : Bool}:
  match zz:
    case True{}:
      %Equal.sym(Char, cc, '0', Eq.char_eq_true(cc, '0', ez)) : {n1.fsh(T.num.go(tt, M3.n1.sz(sg))) == n1.S.R(_ <> tt)
        : Bool}
      %n1.udi.z(D1.abnf.cut.pre(tt, D1.ACutDot{})) : {n1.fsh(T.num.go(tt, M3.n1.sz(sg))) == Bool.and(_,
        n1.fq(D1.abnf.cut.post(tt, D1.ACutDot{}))) : Bool}
      ihz
    case False{}:
      match dd:
        case True{}:
          %n1.pre.no(D1.ACutDot{}, cc, tt, n1.at.dig(D1.ACutDot{}, cc, ed)) : {n1.fsh(T.num.go(tt,
            T.num.digit.ok(T.dig.ok(T.dig.val(cc), 10), cc, T.NDig{}, sg, 10, []))) ==
            Bool.and(D1.abnf.unsigned_dec_int(_), n1.fq(D1.abnf.cut.post(cc <> tt, D1.ACutDot{}))) : Bool}
          %n1.post.no(D1.ACutDot{}, cc, tt, n1.at.dig(D1.ACutDot{}, cc, ed)) : {n1.fsh(T.num.go(tt,
            T.num.digit.ok(T.dig.ok(T.dig.val(cc), 10), cc, T.NDig{}, sg, 10, []))) ==
            Bool.and(D1.abnf.unsigned_dec_int(cc <> D1.abnf.cut.pre(tt, D1.ACutDot{})), n1.fq(_)) : Bool}
          %M3.n1.udi.d(cc, D1.abnf.cut.pre(tt, D1.ACutDot{}), M3.n1.d19.y(cc, ed, ez)) : {n1.fsh(T.num.go(tt,
            T.num.digit.ok(T.dig.ok(T.dig.val(cc), 10), cc, T.NDig{}, sg, 10, []))) == Bool.and(_,
            n1.fq(D1.abnf.cut.post(tt, D1.ACutDot{}))) : Bool}
          %Equal.sym(Bool, T.dig.ok(T.dig.val(cc), 10), True{}, M3.n1.dok10(cc, ed)) : {n1.fsh(T.num.go(tt,
            T.num.digit.ok(_, cc, T.NDig{}, sg, 10, []))) == Bool.and(D1.abnf.dec_rep(D1.abnf.cut.pre(tt,
            D1.ACutDot{})), n1.fq(D1.abnf.cut.post(tt, D1.ACutDot{}))) : Bool}
          ihd
        case False{}:
          Equal.trans(Bool, n1.fsh(T.num.go(tt, T.num.bad(M3.n1.sl(sg), "invalid number"))), False{},
            n1.S.R(cc <> tt), n1.fsh.bad(tt, "invalid number"),
            n1.udi.cut(D1.abnf.cut.at(D1.ACutDot{}, cc), cc, D1.abnf.cut.pre(tt, D1.ACutDot{}),
              n1.fq(D1.abnf.cut.post(cc <> tt, D1.ACutDot{})), ed))

# the character after a sign: a second sign fails
def n1.S.go(
  pp: Bool,
  mm: Bool,
  +cc: Char,
  +tt: List<&2, Char>,
  +sg: T.Sign,
  +ep: {Char.is_eq(cc, '+') == pp : Bool},
  +em: {Char.is_eq(cc, '-') == mm : Bool},
  ihz: n1.Z.G(tt, sg),
  ihd: n1.D.G(tt, sg, T.dec.go([], 10, T.dig.val(cc)), "")
) -> {n1.fsh(T.num.go(tt, T.num.after.sign.go(Bool.or(pp, mm), sg, cc))) == n1.S.R(cc <> tt) : Bool}:
  match pp:
    case True{}:
      %Equal.sym(Char, cc, '+', Eq.char_eq_true(cc, '+', ep)) : {n1.fsh(T.num.go(tt, T.num.bad(T.num.start(),
        "invalid number"))) == n1.S.R(_ <> tt) : Bool}
      %M3.n1.udi.n('+', D1.abnf.cut.pre(tt, D1.ACutDot{}), {==}) : {n1.fsh(T.num.go(tt, T.num.bad(T.num.start(),
        "invalid number"))) == Bool.and(_, n1.fq(D1.abnf.cut.post(tt, D1.ACutDot{}))) : Bool}
      n1.fsh.bad(tt, "invalid number")
    case False{}:
      match mm:
        case True{}:
          %Equal.sym(Char, cc, '-', Eq.char_eq_true(cc, '-', em)) : {n1.fsh(T.num.go(tt, T.num.bad(T.num.start(),
            "invalid number"))) == n1.S.R(_ <> tt) : Bool}
          %M3.n1.udi.n('-', D1.abnf.cut.pre(tt, D1.ACutDot{}), {==}) : {n1.fsh(T.num.go(tt,
            T.num.bad(T.num.start(), "invalid number"))) == Bool.and(_, n1.fq(D1.abnf.cut.post(tt,
            D1.ACutDot{}))) : Bool}
          n1.fsh.bad(tt, "invalid number")
        case False{}:
          %Equal.sym(Bool, Char.is_eq(cc, '+'), False{}, ep) : {n1.fsh(T.num.go(tt, T.num.lead.go(_,
            Char.is_eq(cc, '-'), Char.is_eq(cc, '0'), Char.is_digit(cc), M3.n1.sl(sg), cc))) == n1.S.R(cc <> tt) : Bool}
          %Equal.sym(Bool, Char.is_eq(cc, '-'), False{}, em) : {n1.fsh(T.num.go(tt, T.num.lead.go(False{}, _,
            Char.is_eq(cc, '0'), Char.is_digit(cc), M3.n1.sl(sg), cc))) == n1.S.R(cc <> tt) : Bool}
          n1.S2.go(Char.is_eq(cc, '0'), Char.is_digit(cc), cc, tt, sg, {==}, {==}, ihz, ihd)

# after a sign, the scan finishes as a float exactly when the rest, cut at
# its first dot or e, is an unsigned-dec-int and then an exp or a frac with
# an optional exp
def n1.S(rest: List<&2, Char>, +sg: T.Sign) -> {n1.fsh(T.num.go(rest, M3.n1.ss(sg))) == n1.S.R(rest) : Bool}:
  match rest:
    case []:
      {==}
    case +hh <> +tt:
      n1.S.go(Char.is_eq(hh, '+'), Char.is_eq(hh, '-'), hh, tt, sg, {==}, {==}, n1.Z(tt, sg),
        n1.D(tt, sg, T.dec.go([], 10, T.dig.val(hh)), ""))

# a dec-int cut at c, where c is no sign and no digit, is none, whatever
# follows
def n1.dint.cut(
  cut: Bool,
  +cc: Char,
  +xs: List<&2, Char>,
  +more: Bool,
  +em: {False{} == D1.abnf.minus(cc) : Bool},
  +ep: {False{} == D1.abnf.plus(cc) : Bool},
  hc: {Char.is_digit(cc) == False{} : Bool}
) -> {False{} == Bool.and(D1.abnf.dec_int(D1.abnf.cut.pre.pick(cut, cc, xs)), more) : Bool}:
  match cut:
    case True{}:
      {==}
    case False{}:
      %em : {False{} == Bool.and(Bool.or(Bool.and(Bool.or(_, D1.abnf.plus(cc)), D1.abnf.unsigned_dec_int(xs)),
        D1.abnf.unsigned_dec_int(cc <> xs)), more) : Bool}
      %ep : {False{} == Bool.and(Bool.or(Bool.and(Bool.or(False{}, _), D1.abnf.unsigned_dec_int(xs)),
        D1.abnf.unsigned_dec_int(cc <> xs)), more) : Bool}
      %M3.n1.udi.n(cc, xs, hc) : {False{} == Bool.and(Bool.or(False{}, _), more) : Bool}
      {==}

# a dec-int that starts with a sign is the unsigned-dec-int after it
def n1.dint.sgn(
  +cc: Char,
  +xs: List<&2, Char>,
  +more: Bool,
  hd: {Char.is_digit(cc) == False{} : Bool}
) -> {Bool.and(D1.abnf.unsigned_dec_int(xs), more) == Bool.and(Bool.or(D1.abnf.unsigned_dec_int(xs),
  D1.abnf.unsigned_dec_int(cc <> xs)), more) : Bool}:
  %M3.n1.udi.n(cc, xs, hd) : {Bool.and(D1.abnf.unsigned_dec_int(xs), more) == Bool.and(Bool.or(
    D1.abnf.unsigned_dec_int(xs), _), more) : Bool}
  %Equal.sym(Bool, Bool.or(D1.abnf.unsigned_dec_int(xs), False{}), D1.abnf.unsigned_dec_int(xs),
    M3.n1.orf(D1.abnf.unsigned_dec_int(xs))) : {Bool.and(D1.abnf.unsigned_dec_int(xs), more) == Bool.and(_, more)
    : Bool}
  {==}

# a first character that is no sign and no zero: a digit, or anything else
def n1.L.go2(
  dd: Bool,
  +cc: Char,
  +tt: List<&2, Char>,
  +ez: {Char.is_eq(cc, '0') == False{} : Bool},
  +ed: {Char.is_digit(cc) == dd : Bool},
  +fm: {False{} == D1.abnf.minus(cc) : Bool},
  +fp: {False{} == D1.abnf.plus(cc) : Bool},
  ihd: n1.D.G(tt, T.Plus{}, T.dec.go([], 10, T.dig.val(cc)), "")
) -> {n1.fsh(T.num.go(tt, T.num.lead.go(False{}, False{}, False{}, dd, T.num.start(), cc)))
  == D1.abnf.float_std(cc <> tt) : Bool}:
  match dd:
    case True{}:
      %n1.pre.no(D1.ACutDot{}, cc, tt, n1.at.dig(D1.ACutDot{}, cc, ed)) : {n1.fsh(T.num.go(tt,
        T.num.digit.ok(T.dig.ok(T.dig.val(cc), 10), cc, T.NDig{}, T.Plus{}, 10, []))) ==
        Bool.and(D1.abnf.dec_int(_), n1.fq(D1.abnf.cut.post(cc <> tt, D1.ACutDot{}))) : Bool}
      %n1.post.no(D1.ACutDot{}, cc, tt, n1.at.dig(D1.ACutDot{}, cc, ed)) : {n1.fsh(T.num.go(tt,
        T.num.digit.ok(T.dig.ok(T.dig.val(cc), 10), cc, T.NDig{}, T.Plus{}, 10, []))) ==
        Bool.and(D1.abnf.dec_int(cc <> D1.abnf.cut.pre(tt, D1.ACutDot{})), n1.fq(_)) : Bool}
      %fm : {n1.fsh(T.num.go(tt, T.num.digit.ok(T.dig.ok(T.dig.val(cc), 10), cc, T.NDig{}, T.Plus{}, 10, []))) ==
        Bool.and(Bool.or(Bool.and(Bool.or(_, D1.abnf.plus(cc)), D1.abnf.unsigned_dec_int(D1.abnf.cut.pre(tt,
        D1.ACutDot{}))), D1.abnf.unsigned_dec_int(cc <> D1.abnf.cut.pre(tt, D1.ACutDot{}))),
        n1.fq(D1.abnf.cut.post(tt, D1.ACutDot{}))) : Bool}
      %fp : {n1.fsh(T.num.go(tt, T.num.digit.ok(T.dig.ok(T.dig.val(cc), 10), cc, T.NDig{}, T.Plus{}, 10, []))) ==
        Bool.and(Bool.or(Bool.and(Bool.or(False{}, _), D1.abnf.unsigned_dec_int(D1.abnf.cut.pre(tt,
        D1.ACutDot{}))), D1.abnf.unsigned_dec_int(cc <> D1.abnf.cut.pre(tt, D1.ACutDot{}))),
        n1.fq(D1.abnf.cut.post(tt, D1.ACutDot{}))) : Bool}
      %M3.n1.udi.d(cc, D1.abnf.cut.pre(tt, D1.ACutDot{}), M3.n1.d19.y(cc, ed, ez)) : {n1.fsh(T.num.go(tt,
        T.num.digit.ok(T.dig.ok(T.dig.val(cc), 10), cc, T.NDig{}, T.Plus{}, 10, []))) == Bool.and(Bool.or(False{}, _),
        n1.fq(D1.abnf.cut.post(tt, D1.ACutDot{}))) : Bool}
      %Equal.sym(Bool, T.dig.ok(T.dig.val(cc), 10), True{}, M3.n1.dok10(cc, ed)) : {n1.fsh(T.num.go(tt,
        T.num.digit.ok(_, cc, T.NDig{}, T.Plus{}, 10, []))) == Bool.and(D1.abnf.dec_rep(D1.abnf.cut.pre(tt,
        D1.ACutDot{})), n1.fq(D1.abnf.cut.post(tt, D1.ACutDot{}))) : Bool}
      ihd
    case False{}:
      Equal.trans(Bool, n1.fsh(T.num.go(tt, T.num.bad(T.num.start(), "invalid number"))), False{},
        D1.abnf.float_std(cc <> tt), n1.fsh.bad(tt, "invalid number"),
        n1.dint.cut(D1.abnf.cut.at(D1.ACutDot{}, cc), cc, D1.abnf.cut.pre(tt, D1.ACutDot{}),
          n1.fq(D1.abnf.cut.post(cc <> tt, D1.ACutDot{})), fm, fp, ed))

# the first character of a word: a sign, a zero, a digit, or anything else,
# which fails
def n1.L.go(
  pp: Bool,
  mm: Bool,
  zz: Bool,
  dd: Bool,
  +cc: Char,
  +tt: List<&2, Char>,
  +ep: {Char.is_eq(cc, '+') == pp : Bool},
  +em: {Char.is_eq(cc, '-') == mm : Bool},
  +ez: {Char.is_eq(cc, '0') == zz : Bool},
  +ed: {Char.is_digit(cc) == dd : Bool},
  ihp: {n1.fsh(T.num.go(tt, M3.n1.ss(T.Plus{}))) == n1.S.R(tt) : Bool},
  ihm: {n1.fsh(T.num.go(tt, M3.n1.ss(T.Minus{}))) == n1.S.R(tt) : Bool},
  ihz: n1.Z.G(tt, T.Plus{}),
  ihd: n1.D.G(tt, T.Plus{}, T.dec.go([], 10, T.dig.val(cc)), "")
) -> {n1.fsh(T.num.go(tt, T.num.lead.go(pp, mm, zz, dd, T.num.start(), cc))) == D1.abnf.float_std(cc <> tt)
  : Bool}:
  match pp:
    case True{}:
      %Equal.sym(Char, cc, '+', Eq.char_eq_true(cc, '+', ep)) : {n1.fsh(T.num.go(tt, M3.n1.ss(T.Plus{})))
        == D1.abnf.float_std(_ <> tt) : Bool}
      %n1.dint.sgn('+', D1.abnf.cut.pre(tt, D1.ACutDot{}), n1.fq(D1.abnf.cut.post(tt, D1.ACutDot{})), {==}) :
        {n1.fsh(T.num.go(tt, M3.n1.ss(T.Plus{}))) == _ : Bool}
      ihp
    case False{}:
      match mm:
        case True{}:
          %Equal.sym(Char, cc, '-', Eq.char_eq_true(cc, '-', em)) : {n1.fsh(T.num.go(tt, M3.n1.ss(T.Minus{})))
            == D1.abnf.float_std(_ <> tt) : Bool}
          %n1.dint.sgn('-', D1.abnf.cut.pre(tt, D1.ACutDot{}), n1.fq(D1.abnf.cut.post(tt, D1.ACutDot{})),
            {==}) : {n1.fsh(T.num.go(tt, M3.n1.ss(T.Minus{}))) == _ : Bool}
          ihm
        case False{}:
          match zz:
            case True{}:
              %Equal.sym(Char, cc, '0', Eq.char_eq_true(cc, '0', ez)) : {n1.fsh(T.num.go(tt, M3.n1.sz(T.Plus{})))
                == D1.abnf.float_std(_ <> tt) : Bool}
              %n1.udi.z(D1.abnf.cut.pre(tt, D1.ACutDot{})) : {n1.fsh(T.num.go(tt, M3.n1.sz(T.Plus{}))) == Bool.and(_,
                n1.fq(D1.abnf.cut.post(tt, D1.ACutDot{}))) : Bool}
              ihz
            case False{}:
              +fm = {Equal.trans(Bool, False{}, Char.is_eq(cc, '-'), D1.abnf.minus(cc), Equal.sym(Bool,
                Char.is_eq(cc, '-'), False{}, em), M3.n1.minus(cc)) : {False{} == D1.abnf.minus(cc) : Bool}}
              +fp = {Equal.trans(Bool, False{}, Char.is_eq(cc, '+'), D1.abnf.plus(cc), Equal.sym(Bool,
                Char.is_eq(cc, '+'), False{}, ep), M3.n1.plus(cc)) : {False{} == D1.abnf.plus(cc) : Bool}}
              n1.L.go2(dd, cc, tt, ez, ed, fm, fp, ihd)

# the numeral scan finishes as a float exactly when the word matches
# toml.abnf's float rule less its special floats
def n1.flo.sh(cs: List<&2, Char>) -> {n1.fsh(T.num.go(cs, T.num.start())) == D1.abnf.float_std(cs) : Bool}:
  match cs:
    case []:
      {==}
    case +hh <> +tt:
      n1.L.go(Char.is_eq(hh, '+'), Char.is_eq(hh, '-'), Char.is_eq(hh, '0'), Char.is_digit(hh), hh, tt, {==}, {==},
        {==}, {==}, n1.S(tt, T.Plus{}), n1.S(tt, T.Minus{}), n1.Z(tt, T.Plus{}),
        n1.D(tt, T.Plus{}, T.dec.go([], 10, T.dig.val(hh)), ""))

# a failed scan holds no float
def n1.isbad.fsh(+st: T.Num, hs: {M3.n1.isbad(st) == True{} : Bool}) -> {n1.fsh(st) == False{} : Bool}:
  match st:
    case T.Num{nk, _sign, _base, _ds, us, saw, _why}:
      match nk:
        case T.NBad{}:
          {==}
        case T.NLead{}:
          Eq.bit.absurd(&2, {Bool.and(n1.fsh.nk(T.NLead{}, saw), Bool.not(us)) == False{} : Bool}, hs)
        case T.NSign{}:
          Eq.bit.absurd(&2, {Bool.and(n1.fsh.nk(T.NSign{}, saw), Bool.not(us)) == False{} : Bool}, hs)
        case T.NZero{}:
          Eq.bit.absurd(&2, {Bool.and(n1.fsh.nk(T.NZero{}, saw), Bool.not(us)) == False{} : Bool}, hs)
        case T.NDig{}:
          Eq.bit.absurd(&2, {Bool.and(n1.fsh.nk(T.NDig{}, saw), Bool.not(us)) == False{} : Bool}, hs)
        case T.NBase{}:
          Eq.bit.absurd(&2, {Bool.and(n1.fsh.nk(T.NBase{}, saw), Bool.not(us)) == False{} : Bool}, hs)
        case T.NFrac{}:
          Eq.bit.absurd(&2, {Bool.and(n1.fsh.nk(T.NFrac{}, saw), Bool.not(us)) == False{} : Bool}, hs)
        case T.NExp{}:
          Eq.bit.absurd(&2, {Bool.and(n1.fsh.nk(T.NExp{}, saw), Bool.not(us)) == False{} : Bool}, hs)
        case T.NEDig{}:
          Eq.bit.absurd(&2, {Bool.and(n1.fsh.nk(T.NEDig{}, saw), Bool.not(us)) == False{} : Bool}, hs)

# The float's value. A finished scan that holds a float is read as a float of
# the scan's sign and word.body's spelling; the sign is the word's first
# sign, and word.body's spelling is abnf.dec_digits'.

# a scan's sign
def n1.sgn(st: T.Num) -> T.Sign:
  match st:
    case T.Num{_nk, sign, _base, _ds, _us, _saw, _why}:
      sign

# a finished scan that holds a float is read as its sign and the spelling,
# by its fields
def n1.fin.flo.go(
  nk: T.NK,
  saw: Bool,
  uz: Bool,
  +sn: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +why: String,
  +cs: List<&2, Char>,
  +hf: {n1.fsh(T.Num{nk, sn, base, ds, uz, saw, why}) == True{} : Bool}
) -> {T.num.fin(T.Num{nk, sn, base, ds, uz, saw, why}, cs) == T.GotVal{T.VFlo{sn, T.word.body(cs)}} : T.Got}:
  match nk:
    case T.NFrac{}:
      match saw:
        case True{}:
          match uz:
            case True{}:
              Eq.bit.absurd(&2, {T.num.fin(T.Num{T.NFrac{}, sn, base, ds, True{}, True{}, why},
                cs) == T.GotVal{T.VFlo{sn, T.word.body(cs)}} : T.Got},
                hf)
            case False{}:
              {==}
        case False{}:
          Eq.bit.absurd(&2, {T.num.fin(T.Num{T.NFrac{}, sn, base, ds, uz, False{}, why}, cs) == T.GotVal{T.VFlo{sn,
            T.word.body(cs)}} : T.Got}, hf)
    case T.NEDig{}:
      match saw:
        case True{}:
          match uz:
            case True{}:
              Eq.bit.absurd(&2, {T.num.fin(T.Num{T.NEDig{}, sn, base, ds, True{}, True{}, why},
                cs) == T.GotVal{T.VFlo{sn, T.word.body(cs)}} : T.Got},
                hf)
            case False{}:
              {==}
        case False{}:
          Eq.bit.absurd(&2, {T.num.fin(T.Num{T.NEDig{}, sn, base, ds, uz, False{}, why}, cs) == T.GotVal{T.VFlo{sn,
            T.word.body(cs)}} : T.Got}, hf)
    case T.NLead{}:
      Eq.bit.absurd(&2, {T.num.fin(T.Num{T.NLead{}, sn, base, ds, uz, saw, why}, cs) == T.GotVal{T.VFlo{sn,
        T.word.body(cs)}} : T.Got}, hf)
    case T.NSign{}:
      Eq.bit.absurd(&2, {T.num.fin(T.Num{T.NSign{}, sn, base, ds, uz, saw, why}, cs) == T.GotVal{T.VFlo{sn,
        T.word.body(cs)}} : T.Got}, hf)
    case T.NZero{}:
      Eq.bit.absurd(&2, {T.num.fin(T.Num{T.NZero{}, sn, base, ds, uz, saw, why}, cs) == T.GotVal{T.VFlo{sn,
        T.word.body(cs)}} : T.Got}, hf)
    case T.NDig{}:
      Eq.bit.absurd(&2, {T.num.fin(T.Num{T.NDig{}, sn, base, ds, uz, saw, why}, cs) == T.GotVal{T.VFlo{sn,
        T.word.body(cs)}} : T.Got}, hf)
    case T.NBase{}:
      Eq.bit.absurd(&2, {T.num.fin(T.Num{T.NBase{}, sn, base, ds, uz, saw, why}, cs) == T.GotVal{T.VFlo{sn,
        T.word.body(cs)}} : T.Got}, hf)
    case T.NExp{}:
      Eq.bit.absurd(&2, {T.num.fin(T.Num{T.NExp{}, sn, base, ds, uz, saw, why}, cs) == T.GotVal{T.VFlo{sn,
        T.word.body(cs)}} : T.Got}, hf)
    case T.NBad{}:
      Eq.bit.absurd(&2, {T.num.fin(T.Num{T.NBad{}, sn, base, ds, uz, saw, why}, cs) == T.GotVal{T.VFlo{sn,
        T.word.body(cs)}} : T.Got}, hf)

# a finished scan that holds a float is read as its sign and the spelling
def n1.fin.flo(
  +st: T.Num,
  +cs: List<&2, Char>,
  +hf: {n1.fsh(st) == True{} : Bool}
) -> {T.num.fin(st, cs) == T.GotVal{T.VFlo{n1.sgn(st), T.word.body(cs)}} : T.Got}:
  match st:
    case T.Num{nk, +sg, +base, +ds, us, saw, +why}:
      n1.fin.flo.go(nk, saw, us, sg, base, ds, why, cs, hf)

# an integer read or refused is no float
def n1.range.nflo(
  ok: Bool,
  +sg: T.Sign,
  +digits: String,
  +vv: T.Val
) -> {L1.n1.got.flo(T.num.fin.range(ok, sg, digits), vv) == False{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

# an integer, finished or refused, is no float
def n1.int.nflo(
  saw: Bool,
  +sg: T.Sign,
  +digits: String,
  +vv: T.Val
) -> {L1.n1.got.flo(T.num.fin.int(saw, sg, digits), vv) == False{} : Bool}:
  match saw:
    case True{}:
      n1.range.nflo(T.i64.fits(sg, digits), sg, digits, vv)
    case False{}:
      {==}

# a prefixed integer, finished or refused, is no float
def n1.base.nflo(
  sd: Bool,
  saw: Bool,
  +sg: T.Sign,
  +ds: List<&2, U32>,
  +vv: T.Val
) -> {L1.n1.got.flo(T.num.fin.base(sd, saw, sg, ds), vv) == False{} : Bool}:
  match sd:
    case True{}:
      {==}
    case False{}:
      n1.int.nflo(saw, sg, T.dec.text(ds), vv)

# a finished scan that holds no float is read as no float, by its fields
def n1.fin.nflo.go(
  uz: Bool,
  nk: T.NK,
  saw: Bool,
  +sn: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +why: String,
  +cs: List<&2, Char>,
  +vv: T.Val,
  +hf: {n1.fsh(T.Num{nk, sn, base, ds, uz, saw, why}) == False{} : Bool}
) -> {L1.n1.got.flo(T.num.fin(T.Num{nk, sn, base, ds, uz, saw, why}, cs), vv) == False{} : Bool}:
  match uz:
    case True{}:
      {==}
    case False{}:
      match nk saw:
        case T.NFrac{} True{}:
          Eq.bit.absurd2(&2, {L1.n1.got.flo(T.num.fin(T.Num{T.NFrac{}, sn, base, ds, False{}, True{}, why}, cs),
            vv) == False{} : Bool}, hf)
        case T.NEDig{} True{}:
          Eq.bit.absurd2(&2, {L1.n1.got.flo(T.num.fin(T.Num{T.NEDig{}, sn, base, ds, False{}, True{}, why}, cs),
            vv) == False{} : Bool}, hf)
        case T.NFrac{} False{}:
          {==}
        case T.NEDig{} False{}:
          {==}
        case T.NLead{} s0:
          {==}
        case T.NSign{} s0:
          {==}
        case T.NZero{} s0:
          {==}
        case T.NDig{} s0:
          n1.int.nflo(s0, sn, T.dec.text(ds), vv)
        case T.NBase{} s0:
          n1.base.nflo(T.num.signed(cs), s0, sn, ds, vv)
        case T.NExp{} s0:
          {==}
        case T.NBad{} s0:
          {==}

# a finished scan that holds no float is read as no float
def n1.fin.nflo(
  +st: T.Num,
  +cs: List<&2, Char>,
  +vv: T.Val,
  +hf: {n1.fsh(st) == False{} : Bool}
) -> {L1.n1.got.flo(T.num.fin(st, cs), vv) == False{} : Bool}:
  match st:
    case T.Num{nk, +sg, +base, +ds, us, saw, +why}:
      n1.fin.nflo.go(us, nk, saw, sg, base, ds, why, cs, vv, hf)

# The sign. After the first character every step keeps the scan's sign or
# fails it.

# whether a scan kind has the sign sg: a failed scan has any, and the state
# before the first character none
def n1.sgo.nk(nk: T.NK, +ss: T.Sign, +sg: T.Sign) -> Bool:
  match nk:
    case T.NBad{}:
      True{}
    case T.NLead{}:
      False{}
    case _k:
      D3.sign.eq(ss, sg)

# whether a scan has the sign sg, or has failed
def n1.sgo(st: T.Num, +sg: T.Sign) -> Bool:
  match st:
    case T.Num{nk, ss, _base, _ds, _us, _saw, _why}:
      n1.sgo.nk(nk, ss, sg)

# a digit joined or refused keeps the sign
def n1.sgo.digit(
  ok: Bool,
  +cc: Char,
  +nk: T.NK,
  +ss: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +sg: T.Sign,
  hn: {n1.sgo.nk(nk, ss, sg) == True{} : Bool}
) -> {n1.sgo(T.num.digit.ok(ok, cc, nk, ss, base, ds), sg) == True{} : Bool}:
  match ok:
    case True{}:
      hn
    case False{}:
      {==}

# an underscore taken or refused keeps the sign
def n1.sgo.us(
  ok: Bool,
  +nk: T.NK,
  +ss: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +why: String,
  +sg: T.Sign,
  hn: {n1.sgo.nk(nk, ss, sg) == True{} : Bool}
) -> {n1.sgo(T.num.us.go(ok, nk, ss, base, ds, why), sg) == True{} : Bool}:
  match ok:
    case True{}:
      hn
    case False{}:
      {==}

# a dot taken or refused keeps the sign
def n1.sgo.dot(
  ok: Bool,
  +ss: T.Sign,
  +sg: T.Sign,
  hs: {D3.sign.eq(ss, sg) == True{} : Bool}
) -> {n1.sgo(T.num.dot.go(ok, ss), sg) == True{} : Bool}:
  match ok:
    case True{}:
      hs
    case False{}:
      {==}

# an exponent mark taken or refused keeps the sign
def n1.sgo.exp(
  ok: Bool,
  +ss: T.Sign,
  +sg: T.Sign,
  hs: {D3.sign.eq(ss, sg) == True{} : Bool}
) -> {n1.sgo(T.num.exp.go(ok, ss), sg) == True{} : Bool}:
  match ok:
    case True{}:
      hs
    case False{}:
      {==}

# the first character of an unsigned numeral after a sign keeps the sign
def n1.sgo.lead2(
  zz: Bool,
  dd: Bool,
  +cc: Char,
  +ss: T.Sign,
  +sg: T.Sign,
  +hs: {D3.sign.eq(ss, sg) == True{} : Bool}
) -> {n1.sgo(T.num.lead.go(False{}, False{}, zz, dd, M3.n1.sl(ss), cc), sg) == True{} : Bool}:
  match zz:
    case True{}:
      hs
    case False{}:
      match dd:
        case True{}:
          n1.sgo.digit(T.dig.ok(T.dig.val(cc), 10), cc, T.NDig{}, ss, 10, [], sg, hs)
        case False{}:
          {==}

# the character after a sign keeps the sign
def n1.sgo.sign(
  pp: Bool,
  mm: Bool,
  +cc: Char,
  +ss: T.Sign,
  +sg: T.Sign,
  +ep: {Char.is_eq(cc, '+') == pp : Bool},
  +em: {Char.is_eq(cc, '-') == mm : Bool},
  +hs: {D3.sign.eq(ss, sg) == True{} : Bool}
) -> {n1.sgo(T.num.after.sign.go(Bool.or(pp, mm), ss, cc), sg) == True{} : Bool}:
  match pp:
    case True{}:
      {==}
    case False{}:
      match mm:
        case True{}:
          {==}
        case False{}:
          %Equal.sym(Bool, Char.is_eq(cc, '+'), False{}, ep) : {n1.sgo(T.num.lead.go(_, Char.is_eq(cc, '-'),
            Char.is_eq(cc, '0'), Char.is_digit(cc), M3.n1.sl(ss), cc), sg) == True{} : Bool}
          %Equal.sym(Bool, Char.is_eq(cc, '-'), False{}, em) : {n1.sgo(T.num.lead.go(False{}, _,
            Char.is_eq(cc, '0'), Char.is_digit(cc), M3.n1.sl(ss), cc), sg) == True{} : Bool}
          n1.sgo.lead2(Char.is_eq(cc, '0'), Char.is_digit(cc), cc, ss, sg, hs)

# the character after a leading zero keeps the sign
def n1.sgo.zero(
  xx: Bool,
  oo: Bool,
  bb: Bool,
  pp: Bool,
  e1: Bool,
  e2: Bool,
  +cc: Char,
  +ss: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String,
  +sg: T.Sign,
  +hs: {D3.sign.eq(ss, sg) == True{} : Bool}
) -> {n1.sgo(T.num.zero.go(xx, oo, bb, pp, e1, e2, T.Num{T.NZero{}, ss, base, ds, us, saw, why}, cc), sg) == True{}
  : Bool}:
  match xx oo bb pp:
    case True{} _o _b _p:
      hs
    case False{} True{} _b _p:
      hs
    case False{} False{} True{} _p:
      hs
    case False{} False{} False{} True{}:
      n1.sgo.dot(Bool.and(saw, Bool.not(us)), ss, sg, hs)
    case False{} False{} False{} False{}:
      match e1 e2:
        case True{} _e:
          n1.sgo.exp(Bool.and(saw, Bool.not(us)), ss, sg, hs)
        case False{} True{}:
          n1.sgo.exp(Bool.and(saw, Bool.not(us)), ss, sg, hs)
        case False{} False{}:
          {==}

# the character after a digit of an integer part keeps the sign
def n1.sgo.digs(
  dd: Bool,
  uu: Bool,
  pp: Bool,
  e1: Bool,
  e2: Bool,
  +cc: Char,
  +ss: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String,
  +sg: T.Sign,
  +hs: {D3.sign.eq(ss, sg) == True{} : Bool}
) -> {n1.sgo(T.num.digs.go(dd, uu, pp, e1, e2, T.Num{T.NDig{}, ss, base, ds, us, saw, why}, cc), sg) == True{}
  : Bool}:
  match dd uu pp:
    case True{} _u _p:
      n1.sgo.digit(T.dig.ok(T.dig.val(cc), base), cc, T.NDig{}, ss, base, ds, sg, hs)
    case False{} True{} _p:
      n1.sgo.us(Bool.and(saw, Bool.not(us)), T.NDig{}, ss, base, ds, why, sg, hs)
    case False{} False{} True{}:
      n1.sgo.dot(Bool.and(saw, Bool.not(us)), ss, sg, hs)
    case False{} False{} False{}:
      match e1 e2:
        case True{} _e:
          n1.sgo.exp(Bool.and(saw, Bool.not(us)), ss, sg, hs)
        case False{} True{}:
          n1.sgo.exp(Bool.and(saw, Bool.not(us)), ss, sg, hs)
        case False{} False{}:
          {==}

# the character after a prefixed integer's digit keeps the sign
def n1.sgo.based(
  uu: Bool,
  +cc: Char,
  +ss: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String,
  +sg: T.Sign,
  +hs: {D3.sign.eq(ss, sg) == True{} : Bool}
) -> {n1.sgo(T.num.based.go(uu, T.Num{T.NBase{}, ss, base, ds, us, saw, why}, cc), sg) == True{} : Bool}:
  match uu:
    case True{}:
      n1.sgo.us(Bool.and(saw, Bool.not(us)), T.NBase{}, ss, base, ds, why, sg, hs)
    case False{}:
      n1.sgo.digit(T.dig.ok(T.dig.val(cc), base), cc, T.NBase{}, ss, base, ds, sg, hs)

# the character after a fraction's digit keeps the sign
def n1.sgo.frac(
  dd: Bool,
  uu: Bool,
  e1: Bool,
  e2: Bool,
  +cc: Char,
  +ss: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String,
  +sg: T.Sign,
  +hs: {D3.sign.eq(ss, sg) == True{} : Bool}
) -> {n1.sgo(T.num.frac.go(dd, uu, e1, e2, T.Num{T.NFrac{}, ss, base, ds, us, saw, why}, cc), sg) == True{} : Bool}:
  match dd uu:
    case True{} _u:
      n1.sgo.digit(T.dig.ok(T.dig.val(cc), base), cc, T.NFrac{}, ss, base, ds, sg, hs)
    case False{} True{}:
      n1.sgo.us(Bool.and(saw, Bool.not(us)), T.NFrac{}, ss, base, ds, why, sg, hs)
    case False{} False{}:
      match e1 e2:
        case True{} _e:
          n1.sgo.exp(Bool.and(saw, Bool.not(us)), ss, sg, hs)
        case False{} True{}:
          n1.sgo.exp(Bool.and(saw, Bool.not(us)), ss, sg, hs)
        case False{} False{}:
          {==}

# the character after an exponent's e keeps the sign
def n1.sgo.expon(
  pp: Bool,
  mm: Bool,
  dd: Bool,
  +cc: Char,
  +ss: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String,
  +sg: T.Sign,
  +hs: {D3.sign.eq(ss, sg) == True{} : Bool}
) -> {n1.sgo(T.num.expon.go(pp, mm, dd, T.Num{T.NExp{}, ss, base, ds, us, saw, why}, cc), sg) == True{} : Bool}:
  match pp mm dd:
    case True{} _m _d:
      hs
    case False{} True{} _d:
      hs
    case False{} False{} True{}:
      n1.sgo.digit(T.dig.ok(T.dig.val(cc), base), cc, T.NEDig{}, ss, base, ds, sg, hs)
    case False{} False{} False{}:
      {==}

# the character after an exponent's digit keeps the sign
def n1.sgo.edig(
  dd: Bool,
  uu: Bool,
  +cc: Char,
  +ss: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String,
  +sg: T.Sign,
  +hs: {D3.sign.eq(ss, sg) == True{} : Bool}
) -> {n1.sgo(T.num.edig.go(dd, uu, T.Num{T.NEDig{}, ss, base, ds, us, saw, why}, cc), sg) == True{} : Bool}:
  match dd uu:
    case True{} _u:
      n1.sgo.digit(T.dig.ok(T.dig.val(cc), base), cc, T.NEDig{}, ss, base, ds, sg, hs)
    case False{} True{}:
      n1.sgo.us(Bool.and(saw, Bool.not(us)), T.NEDig{}, ss, base, ds, why, sg, hs)
    case False{} False{}:
      {==}

# every step after the first keeps the sign or fails
def n1.sgo.step(
  +st: T.Num,
  +cc: Char,
  +sg: T.Sign,
  hs: {n1.sgo(st, sg) == True{} : Bool}
) -> {n1.sgo(T.num.step(st, cc), sg) == True{} : Bool}:
  match st:
    case T.Num{nk, +ss, +base, +ds, +us, +saw, +why}:
      match nk:
        case T.NLead{}:
          Eq.bit.absurd(&2, {n1.sgo(T.num.step(T.Num{T.NLead{}, ss, base, ds, us, saw, why}, cc), sg) == True{}
            : Bool}, hs)
        case T.NSign{}:
          n1.sgo.sign(Char.is_eq(cc, '+'), Char.is_eq(cc, '-'), cc, ss, sg, {==}, {==}, hs)
        case T.NZero{}:
          n1.sgo.zero(Char.is_eq(cc, 'x'), Char.is_eq(cc, 'o'), Char.is_eq(cc, 'b'), Char.is_eq(cc, '.'),
            Char.is_eq(cc, 'e'), Char.is_eq(cc, 'E'), cc, ss, base, ds, us, saw, why, sg, hs)
        case T.NDig{}:
          n1.sgo.digs(Char.is_digit(cc), Char.is_eq(cc, '_'), Char.is_eq(cc, '.'), Char.is_eq(cc, 'e'),
            Char.is_eq(cc, 'E'), cc, ss, base, ds, us, saw, why, sg, hs)
        case T.NBase{}:
          n1.sgo.based(Char.is_eq(cc, '_'), cc, ss, base, ds, us, saw, why, sg, hs)
        case T.NFrac{}:
          n1.sgo.frac(Char.is_digit(cc), Char.is_eq(cc, '_'), Char.is_eq(cc, 'e'), Char.is_eq(cc, 'E'), cc, ss, base,
            ds, us, saw, why, sg, hs)
        case T.NExp{}:
          n1.sgo.expon(Char.is_eq(cc, '+'), Char.is_eq(cc, '-'), Char.is_digit(cc), cc, ss, base, ds, us, saw, why, sg,
            hs)
        case T.NEDig{}:
          n1.sgo.edig(Char.is_digit(cc), Char.is_eq(cc, '_'), cc, ss, base, ds, us, saw, why, sg, hs)
        case T.NBad{}:
          {==}

# the rest keeps the sign or fails
def n1.sgo.go(
  rest: List<&2, Char>,
  +st: T.Num,
  +sg: T.Sign,
  hs: {n1.sgo(st, sg) == True{} : Bool}
) -> {n1.sgo(T.num.go(rest, st), sg) == True{} : Bool}:
  match rest:
    case []:
      hs
    case +hh <> tt:
      n1.sgo.go(tt, T.num.step(st, hh), sg, n1.sgo.step(st, hh, sg, hs))

# a scan that holds a float and keeps the sign sg has the sign sg, by its
# fields
def n1.sgo.fsh.go(
  nk: T.NK,
  saw: Bool,
  us: Bool,
  +ss: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +why: String,
  +sg: T.Sign,
  hs: {n1.sgo(T.Num{nk, ss, base, ds, us, saw, why}, sg) == True{} : Bool},
  hf: {n1.fsh(T.Num{nk, ss, base, ds, us, saw, why}) == True{} : Bool}
) -> {ss == sg : T.Sign}:
  match nk:
    case T.NFrac{}:
      M1.n1.sign.eq(ss, sg, hs)
    case T.NEDig{}:
      M1.n1.sign.eq(ss, sg, hs)
    case T.NLead{}:
      Eq.bit.absurd(&2, {ss == sg : T.Sign}, hs)
    case T.NSign{}:
      Eq.bit.absurd(&2, {ss == sg : T.Sign}, hf)
    case T.NZero{}:
      Eq.bit.absurd(&2, {ss == sg : T.Sign}, hf)
    case T.NDig{}:
      Eq.bit.absurd(&2, {ss == sg : T.Sign}, hf)
    case T.NBase{}:
      Eq.bit.absurd(&2, {ss == sg : T.Sign}, hf)
    case T.NExp{}:
      Eq.bit.absurd(&2, {ss == sg : T.Sign}, hf)
    case T.NBad{}:
      Eq.bit.absurd(&2, {ss == sg : T.Sign}, hf)

# a scan that holds a float and keeps the sign sg has the sign sg
def n1.sgo.fsh(
  +st: T.Num,
  +sg: T.Sign,
  hs: {n1.sgo(st, sg) == True{} : Bool},
  hf: {n1.fsh(st) == True{} : Bool}
) -> {n1.sgn(st) == sg : T.Sign}:
  match st:
    case T.Num{nk, +ss, +base, +ds, us, saw, +why}:
      n1.sgo.fsh.go(nk, saw, us, ss, base, ds, why, sg, hs, hf)

# the first character of a word gives the sign abnf.dec_sign reads
def n1.sgo.start(
  pp: Bool,
  mm: Bool,
  zz: Bool,
  dd: Bool,
  +hh: Char,
  +tt: List<&2, Char>,
  +ep: {Char.is_eq(hh, '+') == pp : Bool},
  +em: {Char.is_eq(hh, '-') == mm : Bool}
) -> {n1.sgo(T.num.lead.go(pp, mm, zz, dd, T.num.start(), hh), D1.abnf.dec_sign(hh <> tt)) == True{} : Bool}:
  match pp:
    case True{}:
      %Equal.sym(Char, hh, '+', Eq.char_eq_true(hh, '+', ep)) : {n1.sgo(M3.n1.ss(T.Plus{}), D1.abnf.dec_sign(_ <> tt))
        == True{} : Bool}
      {==}
    case False{}:
      match mm:
        case True{}:
          %Equal.sym(Char, hh, '-', Eq.char_eq_true(hh, '-', em)) : {n1.sgo(M3.n1.ss(T.Minus{}),
            D1.abnf.dec_sign(_ <> tt)) == True{} : Bool}
          {==}
        case False{}:
          +fm = {Equal.trans(Bool, False{}, Char.is_eq(hh, '-'), D1.abnf.minus(hh), Equal.sym(Bool,
            Char.is_eq(hh, '-'), False{}, em), M3.n1.minus(hh)) : {False{} == D1.abnf.minus(hh) : Bool}}
          %fm : {n1.sgo(T.num.lead.go(False{}, False{}, zz, dd, T.num.start(), hh), D1.abnf.sign.pick(_)) == True{}
            : Bool}
          n1.sgo.lead2(zz, dd, hh, T.Plus{}, T.Plus{}, {==})

# a word the scan reads as a float has the sign abnf.dec_sign reads
def n1.flo.sign(
  +hh: Char,
  +tt: List<&2, Char>,
  hf: {n1.fsh(T.num.go(hh <> tt, T.num.start())) == True{} : Bool}
) -> {n1.sgn(T.num.go(hh <> tt, T.num.start())) == D1.abnf.dec_sign(hh <> tt) : T.Sign}:
  n1.sgo.fsh(T.num.go(hh <> tt, T.num.start()), D1.abnf.dec_sign(hh <> tt), n1.sgo.go(tt, T.num.step(T.num.start(),
    hh), D1.abnf.dec_sign(hh <> tt), n1.sgo.start(Char.is_eq(hh, '+'), Char.is_eq(hh, '-'), Char.is_eq(hh, '0'),
    Char.is_digit(hh), hh, tt, {==}, {==})), hf)

# The spelling. word.body drops a leading sign and every underscore, as
# abnf.dec_digits does, for a word that does not start with an underscore.

# what the spelling lemma claims: after the first character, the spelling is
# the characters with the underscores removed, after what was kept
def n1.body.G(+cs: List<&2, Char>, +out: List<&2, Char>) -> Type:
  {T.word.body.go(cs, False{}, out) == List.reverse.go(&2, Char, out, String.to_list(D1.abnf.no_us(cs)))
    : List<&2, Char>}

# one character after the first
def n1.body.c(
  uu: Bool,
  +hh: Char,
  +tt: List<&2, Char>,
  +out: List<&2, Char>,
  ih1: n1.body.G(tt, out),
  ih2: n1.body.G(tt, hh <> out)
) -> {T.word.body.go(tt, False{}, T.word.body.put.us(uu, hh, out)) == List.reverse.go(&2, Char, out,
  String.to_list(D1.abnf.no_us.pick(uu, hh, D1.abnf.no_us(tt)))) : List<&2, Char>}:
  match uu:
    case True{}:
      ih1
    case False{}:
      ih2

# after the first character, the spelling is the characters with the
# underscores removed, after what was kept
def n1.body.go(
  cs: List<&2, Char>,
  +out: List<&2, Char>
) -> {T.word.body.go(cs, False{}, out) == List.reverse.go(&2, Char, out,
  String.to_list(D1.abnf.no_us(cs))) : List<&2, Char>}:
  match cs:
    case []:
      {==}
    case +hh <> +tt:
      %M3.n1.us(hh) : {T.word.body.go(tt, False{}, T.word.body.put.us(Char.is_eq(hh, '_'), hh, out))
        == List.reverse.go(&2, Char, out, String.to_list(D1.abnf.no_us.pick(_, hh, D1.abnf.no_us(tt))))
        : List<&2, Char>}
      n1.body.c(Char.is_eq(hh, '_'), hh, tt, out, n1.body.go(tt, out), n1.body.go(tt, hh <> out))

# the spelling after the first character, by whether it is a sign
def n1.body.s(
  pp: Bool,
  mm: Bool,
  +hh: Char,
  +tt: List<&2, Char>,
  hu: {D1.abnf.underscore(hh) == False{} : Bool}
) -> {String.from_list(T.word.body.go(tt, False{}, T.word.body.put.sign(Bool.or(pp, mm), hh, [])))
  == D1.abnf.digits.pick(Bool.or(mm, pp), hh, tt) : String}:
  match pp mm:
    case True{} True{}:
      %Equal.sym(List<&2, Char>, T.word.body.go(tt, False{}, []), String.to_list(D1.abnf.no_us(tt)),
        n1.body.go(tt, [])) : {String.from_list(_) == D1.abnf.no_us(tt) : String}
      M2.ftl(D1.abnf.no_us(tt))
    case True{} False{}:
      %Equal.sym(List<&2, Char>, T.word.body.go(tt, False{}, []), String.to_list(D1.abnf.no_us(tt)),
        n1.body.go(tt, [])) : {String.from_list(_) == D1.abnf.no_us(tt) : String}
      M2.ftl(D1.abnf.no_us(tt))
    case False{} True{}:
      %Equal.sym(List<&2, Char>, T.word.body.go(tt, False{}, []), String.to_list(D1.abnf.no_us(tt)),
        n1.body.go(tt, [])) : {String.from_list(_) == D1.abnf.no_us(tt) : String}
      M2.ftl(D1.abnf.no_us(tt))
    case False{} False{}:
      %Equal.sym(List<&2, Char>, T.word.body.go(tt, False{}, [hh]), hh <> String.to_list(D1.abnf.no_us(tt)),
        n1.body.go(tt, [hh])) : {String.from_list(_) == D1.abnf.no_us(hh <> tt) : String}
      %Equal.sym(Bool, D1.abnf.underscore(hh), False{}, hu) : {SCon{hh, String.from_list(String.to_list(
        D1.abnf.no_us(tt)))} == D1.abnf.no_us.pick(_, hh, D1.abnf.no_us(tt)) : String}
      %Equal.sym(String, String.from_list(String.to_list(D1.abnf.no_us(tt))), D1.abnf.no_us(tt),
        M2.ftl(D1.abnf.no_us(tt))) : {SCon{hh, _} == SCon{hh, D1.abnf.no_us(tt)} : String}
      {==}

# a word that does not start with an underscore is spelled as abnf.dec_digits
# reads it
def n1.body(
  +hh: Char,
  +tt: List<&2, Char>,
  hu: {Char.is_eq(hh, '_') == False{} : Bool}
) -> {T.word.body(hh <> tt) == D1.abnf.dec_digits(hh <> tt) : String}:
  %M3.n1.minus(hh) : {String.from_list(T.word.body.go(tt, False{}, T.word.body.put.sign(Bool.or(Char.is_eq(hh, '+'),
    Char.is_eq(hh, '-')), hh, []))) == D1.abnf.digits.pick(Bool.or(_, D1.abnf.plus(hh)), hh, tt) : String}
  %M3.n1.plus(hh) : {String.from_list(T.word.body.go(tt, False{}, T.word.body.put.sign(Bool.or(Char.is_eq(hh, '+'),
    Char.is_eq(hh, '-')), hh, []))) == D1.abnf.digits.pick(Bool.or(Char.is_eq(hh, '-'), _), hh, tt) : String}
  n1.body.s(Char.is_eq(hh, '+'), Char.is_eq(hh, '-'), hh, tt, Equal.trans(Bool, D1.abnf.underscore(hh),
    Char.is_eq(hh, '_'), False{}, Equal.sym(Bool, Char.is_eq(hh, '_'), D1.abnf.underscore(hh), M3.n1.us(hh)), hu))

# a word that starts with an underscore fails the scan
def n1.us.first(
  uu: Bool,
  +hh: Char,
  +tt: List<&2, Char>,
  eu: {Char.is_eq(hh, '_') == uu : Bool},
  hf: {n1.fsh(T.num.go(hh <> tt, T.num.start())) == True{} : Bool}
) -> {Char.is_eq(hh, '_') == False{} : Bool}:
  match uu:
    case True{}:
      +ee = {Equal.sym(Char, hh, '_', Eq.char_eq_true(hh, '_', eu)) : {'_' == hh : Char}}
      Eq.bit.absurd2(&2, {Char.is_eq(hh, '_') == False{} : Bool}, Equal.trans(Bool, True{}, n1.fsh(T.num.go(hh <> tt,
        T.num.start())), False{}, Equal.sym(Bool, n1.fsh(T.num.go(hh <> tt, T.num.start())), True{}, hf),
        Equal.trans(Bool, n1.fsh(T.num.go(hh <> tt, T.num.start())), n1.fsh(T.num.go('_' <> tt, T.num.start())),
          False{},
        Equal.cong(Char, Bool, xx => n1.fsh(T.num.go(xx <> tt, T.num.start())), hh, '_', Equal.sym(Char, '_', hh, ee)),
        n1.fsh.bad(tt, "invalid number"))))
    case False{}:
      eu

# the second half of special-float: inf or nan, with no sign
def n1.sf.bare(
  -P: List<&2, Char> -> Type,
  ii: Bool,
  +cs: List<&2, Char>,
  ei: {D2.abnf.chars_are(cs, "inf") == ii : Bool},
  hh: {Bool.or(ii, D2.abnf.chars_are(cs, "nan")) == True{} : Bool},
  p3: P(String.to_list("inf")),
  p6: P(String.to_list("nan"))
) -> P(cs):
  match ii:
    case True{}:
      %Equal.sym(List<&2, Char>, cs, String.to_list("inf"), M4.n1.ca.eq(cs, "inf", ei)) : P(_)
      p3
    case False{}:
      %Equal.sym(List<&2, Char>, cs, String.to_list("nan"), M4.n1.ca.eq(cs, "nan", hh)) : P(_)
      p6

# a sign's inf or nan
def n1.sf.sgn(
  -P: List<&2, Char> -> Type,
  ii: Bool,
  +cc: Char,
  +tt: List<&2, Char>,
  ei: {D2.abnf.chars_are(tt, "inf") == ii : Bool},
  hh: {Bool.or(ii, D2.abnf.chars_are(tt, "nan")) == True{} : Bool},
  pi: P(cc <> String.to_list("inf")),
  pn: P(cc <> String.to_list("nan"))
) -> P(cc <> tt):
  match ii:
    case True{}:
      %Equal.sym(List<&2, Char>, tt, String.to_list("inf"), M4.n1.ca.eq(tt, "inf", ei)) : P(cc <> _)
      pi
    case False{}:
      %Equal.sym(List<&2, Char>, tt, String.to_list("nan"), M4.n1.ca.eq(tt, "nan", hh)) : P(cc <> _)
      pn

# the sign of a signed special-float
def n1.sf.sign(
  -P: List<&2, Char> -> Type,
  mm: Bool,
  +hh: Char,
  +tt: List<&2, Char>,
  em: {D1.abnf.minus(hh) == mm : Bool},
  hp: {Bool.or(mm, D1.abnf.plus(hh)) == True{} : Bool},
  hb: {Bool.or(D2.abnf.chars_are(tt, "inf"), D2.abnf.chars_are(tt, "nan")) == True{} : Bool},
  p4: P(String.to_list("+inf")),
  p5: P(String.to_list("-inf")),
  p7: P(String.to_list("+nan")),
  p8: P(String.to_list("-nan"))
) -> P(hh <> tt):
  match mm:
    case True{}:
      %Equal.sym(Char, hh, '-', Eq.char_eq_true(hh, '-', Equal.trans(Bool, Char.is_eq(hh, '-'), D1.abnf.minus(hh),
        True{}, M3.n1.minus(hh), em))) : P(_ <> tt)
      n1.sf.sgn(P, D2.abnf.chars_are(tt, "inf"), '-', tt, {==}, hb, p5, p8)
    case False{}:
      %Equal.sym(Char, hh, '+', Eq.char_eq_true(hh, '+', Equal.trans(Bool, Char.is_eq(hh, '+'), D1.abnf.plus(hh),
        True{}, M3.n1.plus(hh), hp))) : P(_ <> tt)
      n1.sf.sgn(P, D2.abnf.chars_are(tt, "inf"), '+', tt, {==}, hb, p4, p7)

# special-float with its sign test and the test after the sign lifted out
def n1.sf.H(aa: Bool, +bb: Bool, +cs: List<&2, Char>) -> Bool:
  Bool.or(Bool.and(aa, bb), Bool.or(D2.abnf.chars_are(cs, "inf"), D2.abnf.chars_are(cs, "nan")))

# special-float's two halves
def n1.sf.go(
  -P: List<&2, Char> -> Type,
  aa: Bool,
  bb: Bool,
  +hh: Char,
  +tt: List<&2, Char>,
  ea: {Bool.or(D1.abnf.minus(hh), D1.abnf.plus(hh)) == aa : Bool},
  eb: {Bool.or(D2.abnf.chars_are(tt, "inf"), D2.abnf.chars_are(tt, "nan")) == bb : Bool},
  hs: {n1.sf.H(aa, bb, hh <> tt) == True{} : Bool},
  p3: P(String.to_list("inf")),
  p4: P(String.to_list("+inf")),
  p5: P(String.to_list("-inf")),
  p6: P(String.to_list("nan")),
  p7: P(String.to_list("+nan")),
  p8: P(String.to_list("-nan"))
) -> P(hh <> tt):
  match aa bb:
    case True{} True{}:
      n1.sf.sign(P, D1.abnf.minus(hh), hh, tt, {==}, ea, eb, p4, p5, p7, p8)
    case True{} False{}:
      n1.sf.bare(P, D2.abnf.chars_are(hh <> tt, "inf"), hh <> tt, {==}, hs, p3, p6)
    case False{} _b:
      n1.sf.bare(P, D2.abnf.chars_are(hh <> tt, "inf"), hh <> tt, {==}, hs, p3, p6)

# a claim made of each special-float is made of every word that matches
# special-float
def n1.sf.split(
  -P: List<&2, Char> -> Type,
  +cs: List<&2, Char>,
  hs: {D1.abnf.special_float(cs) == True{} : Bool},
  p3: P(String.to_list("inf")),
  p4: P(String.to_list("+inf")),
  p5: P(String.to_list("-inf")),
  p6: P(String.to_list("nan")),
  p7: P(String.to_list("+nan")),
  p8: P(String.to_list("-nan"))
) -> P(cs):
  match cs:
    case []:
      Eq.bit.absurd(&1, P([]), hs)
    case +hh <> +tt:
      n1.sf.go(P, Bool.or(D1.abnf.minus(hh), D1.abnf.plus(hh)), Bool.or(D2.abnf.chars_are(tt, "inf"),
        D2.abnf.chars_are(tt, "nan")), hh, tt, {==}, {==}, hs, p3, p4, p5, p6, p7, p8)

# a word that matches special-float is a special word
def n1.sf.spec(
  +cs: List<&2, Char>,
  hs: {D1.abnf.special_float(cs) == True{} : Bool}
) -> {M4.n1.isspec(cs) == True{} : Bool}:
  n1.sf.split(xs => {M4.n1.isspec(xs) == True{} : Bool}, cs, hs, {==}, {==}, {==}, {==}, {==}, {==})

# a word that is no special word matches no special-float
def n1.sf.no(
  sf: Bool,
  +cs: List<&2, Char>,
  es: {D1.abnf.special_float(cs) == sf : Bool},
  hs: {M4.n1.isspec(cs) == False{} : Bool}
) -> {D1.abnf.special_float(cs) == False{} : Bool}:
  match sf:
    case True{}:
      Eq.bit.absurd2(&2, {D1.abnf.special_float(cs) == False{} : Bool}, Equal.trans(Bool, True{}, M4.n1.isspec(cs),
        False{}, Equal.sym(Bool, M4.n1.isspec(cs), True{}, n1.sf.spec(cs, es)), hs))
    case False{}:
      es

# The float law.

# no datetime is a float
def n1.when.nflo(ww: T.WhenOut, +vv: T.Val) -> {L1.n1.got.flo(T.word.from.when(ww), vv) == False{} : Bool}:
  match ww:
    case T.WSome{_w}:
      {==}
    case T.WFail{_y}:
      {==}
    case T.WSkip{}:
      {==}

# what the float law claims of a word
def n1.flo.G(+cs: List<&2, Char>, +vv: T.Val) -> Type:
  {L1.n1.got.flo(T.word.val(cs), vv) == Bool.and(D1.abnf.float(cs), D1.g.val(D4.GvFloat{cs}, vv)) : Bool}

# a float's reading holds the value exactly when the value is the one the
# word denotes
def n1.flo.same(
  vv: T.Val,
  +cs: List<&2, Char>
) -> {L1.n1.got.flo(T.GotVal{T.VFlo{D1.abnf.dec_sign(cs), D1.abnf.dec_digits(cs)}}, vv) == D1.g.flo.is(vv,
  cs) : Bool}:
  match vv:
    case T.VFlo{_s, _t}:
      {==}
    case T.VStr{_t}:
      {==}
    case T.VSpan{_s, _n}:
      {==}
    case T.VInt{_s, _d}:
      {==}
    case T.VBool{_b}:
      {==}
    case T.VWhen{_w}:
      {==}
    case T.VArr{_i}:
      {==}
    case T.VInl{_r}:
      {==}
    case T.VHead{_p, _r}:
      {==}
    case T.VAot{_p, _r}:
      {==}
    case T.VAots{_p, _e}:
      {==}
    case T.VPair{_n, _v}:
      {==}

# a special word's reading, for each special word
def n1.flo.spec(+vv: T.Val, +cs: List<&2, Char>, hs: {M4.n1.isspec(cs) == True{} : Bool}) -> n1.flo.G(cs, vv):
  M4.n1.spec.split(xs => n1.flo.G(xs, vv), cs, hs, {==}, {==}, n1.flo.same(vv, String.to_list("inf")),
    n1.flo.same(vv, String.to_list("+inf")), n1.flo.same(vv, String.to_list("-inf")),
    n1.flo.same(vv, String.to_list("nan")), n1.flo.same(vv, String.to_list("+nan")),
    n1.flo.same(vv, String.to_list("-nan")))

# a scan that holds a float has not failed
def n1.fsh.nb(
  bb: Bool,
  +st: T.Num,
  +eb: {M3.n1.isbad(st) == bb : Bool},
  +hf: {n1.fsh(st) == True{} : Bool}
) -> {M3.n1.isbad(st) == False{} : Bool}:
  match bb:
    case True{}:
      Eq.bit.absurd(&2, {M3.n1.isbad(st) == False{} : Bool}, Equal.trans(Bool, False{}, n1.fsh(st), True{},
        Equal.sym(Bool, n1.fsh(st), False{}, n1.isbad.fsh(st, eb)), hf))
    case False{}:
      eb

# a word that matches float-int-part ( exp / frac [ exp ] ) is read as the
# float it denotes
def n1.flo.std(
  +hh: Char,
  +tt: List<&2, Char>,
  +vv: T.Val,
  +efs: {D1.abnf.float_std(hh <> tt) == True{} : Bool}
) -> n1.flo.G(hh <> tt, vv):
  +hf = {Equal.trans(Bool, n1.fsh(T.num.go(hh <> tt, T.num.start())), D1.abnf.float_std(hh <> tt), True{},
    n1.flo.sh(hh <> tt), efs) : {n1.fsh(T.num.go(hh <> tt, T.num.start())) == True{} : Bool}}
  +fin = T.num.go(hh <> tt, T.num.start())
  +ew = {Equal.trans(T.Got, T.word.val(hh <> tt), T.num.fin(fin, hh <> tt),
    T.GotVal{T.VFlo{D1.abnf.dec_sign(hh <> tt),
    D1.abnf.dec_digits(hh <> tt)}}, M3.n1.wv(hh <> tt, n1.fsh.nb(M3.n1.isbad(fin), fin, {==}, hf)),
    Equal.trans(T.Got, T.num.fin(fin, hh <> tt), T.GotVal{T.VFlo{n1.sgn(fin), T.word.body(hh <> tt)}},
    T.GotVal{T.VFlo{D1.abnf.dec_sign(hh <> tt), D1.abnf.dec_digits(hh <> tt)}}, n1.fin.flo(fin, hh <> tt, hf),
    Equal.trans(T.Got, T.GotVal{T.VFlo{n1.sgn(fin), T.word.body(hh <> tt)}}, T.GotVal{T.VFlo{D1.abnf.dec_sign(hh <>
    tt), T.word.body(hh <> tt)}}, T.GotVal{T.VFlo{D1.abnf.dec_sign(hh <> tt), D1.abnf.dec_digits(hh <> tt)}},
    Equal.cong(T.Sign, T.Got, ss => T.GotVal{T.VFlo{ss, T.word.body(hh <> tt)}}, n1.sgn(fin),
    D1.abnf.dec_sign(hh <> tt), n1.flo.sign(hh, tt, hf)),
    Equal.cong(String, T.Got, ss => T.GotVal{T.VFlo{D1.abnf.dec_sign(hh <> tt), ss}}, T.word.body(hh <> tt),
    D1.abnf.dec_digits(hh <> tt), n1.body(hh, tt, n1.us.first(Char.is_eq(hh, '_'), hh, tt, {==}, hf))))))
    : {T.word.val(hh <> tt) == T.GotVal{T.VFlo{D1.abnf.dec_sign(hh <> tt), D1.abnf.dec_digits(hh <> tt)}}
    : T.Got}}
  %Equal.sym(T.Got, T.word.val(hh <> tt), T.GotVal{T.VFlo{D1.abnf.dec_sign(hh <> tt), D1.abnf.dec_digits(hh <>
    tt)}}, ew) : {L1.n1.got.flo(_, vv) == Bool.and(D1.abnf.float(hh <> tt), D1.g.val(D4.GvFloat{hh <> tt}, vv))
    : Bool}
  %Equal.sym(Bool, D1.abnf.float_std(hh <> tt), True{}, efs) : {L1.n1.got.flo(T.GotVal{T.VFlo{
    D1.abnf.dec_sign(hh <> tt), D1.abnf.dec_digits(hh <> tt)}}, vv) == Bool.and(Bool.or(_,
    D1.abnf.special_float(hh <> tt)), D1.g.val(D4.GvFloat{hh <> tt}, vv)) : Bool}
  n1.flo.same(vv, hh <> tt)

# a word sent to the datetime reader or the numeral scan that holds no float
# is read as no float
def n1.flo.ns.go(
  ad: Bool,
  +cs: List<&2, Char>,
  +vv: T.Val,
  +hf: {n1.fsh(T.num.go(cs, T.num.start())) == False{} : Bool}
) -> {L1.n1.got.flo(T.word.route.date(ad, cs), vv) == False{} : Bool}:
  match ad:
    case True{}:
      n1.when.nflo(T.when.read(cs), vv)
    case False{}:
      n1.fin.nflo(T.num.go(cs, T.num.start()), cs, vv, hf)

# a word that is no special word and matches no float-int-part ( exp / frac
# [ exp ] ) is read as no float, and matches no float
def n1.flo.ns(
  +cs: List<&2, Char>,
  +vv: T.Val,
  +efs: {D1.abnf.float_std(cs) == False{} : Bool},
  +hs: {M4.n1.isspec(cs) == False{} : Bool}
) -> n1.flo.G(cs, vv):
  %Equal.sym(T.Got, T.word.val(cs), T.word.route.date(T.word.as_date(T.word.or(T.word.colon(cs), T.word.dash(cs,
    True{})), T.word.ee(cs)), cs), M4.n1.wv.ns(cs, hs)) : {L1.n1.got.flo(_, vv) == Bool.and(D1.abnf.float(cs),
    D1.g.val(D4.GvFloat{cs}, vv)) : Bool}
  %Equal.sym(Bool, D1.abnf.float_std(cs), False{}, efs) : {L1.n1.got.flo(T.word.route.date(T.word.as_date(
    T.word.or(T.word.colon(cs), T.word.dash(cs, True{})), T.word.ee(cs)), cs), vv) == Bool.and(Bool.or(_,
    D1.abnf.special_float(cs)), D1.g.val(D4.GvFloat{cs}, vv)) : Bool}
  %Equal.sym(Bool, D1.abnf.special_float(cs), False{}, n1.sf.no(D1.abnf.special_float(cs), cs, {==}, hs)) :
    {L1.n1.got.flo(T.word.route.date(T.word.as_date(T.word.or(T.word.colon(cs), T.word.dash(cs, True{})),
    T.word.ee(cs)), cs), vv) == Bool.and(Bool.or(False{}, _), D1.g.val(D4.GvFloat{cs}, vv)) : Bool}
  n1.flo.ns.go(T.word.as_date(T.word.or(T.word.colon(cs), T.word.dash(cs, True{})), T.word.ee(cs)), cs, vv,
    Equal.trans(Bool, n1.fsh(T.num.go(cs, T.num.start())), D1.abnf.float_std(cs), False{}, n1.flo.sh(cs), efs))

# a word that matches no float-int-part ( exp / frac [ exp ] ): a special
# word, or no float at all
def n1.flo.nstd(
  sp: Bool,
  +cs: List<&2, Char>,
  +vv: T.Val,
  +es: {M4.n1.isspec(cs) == sp : Bool},
  +efs: {D1.abnf.float_std(cs) == False{} : Bool}
) -> n1.flo.G(cs, vv):
  match sp:
    case True{}:
      n1.flo.spec(vv, cs, es)
    case False{}:
      n1.flo.ns(cs, vv, efs, es)

# the float law, by whether the word matches float-int-part ( exp / frac
# [ exp ] )
def n1.flo.law(
  fs: Bool,
  +cs: List<&2, Char>,
  +vv: T.Val,
  +efs: {D1.abnf.float_std(cs) == fs : Bool}
) -> n1.flo.G(cs, vv):
  match fs:
    case True{}:
      match cs:
        case []:
          Eq.bit.absurd(&1, n1.flo.G([], vv), efs)
        case +hh <> +tt:
          n1.flo.std(hh, tt, vv, efs)
    case False{}:
      n1.flo.nstd(M4.n1.isspec(cs), cs, vv, {==}, efs)

def L1.float_word_exact(cs, v):
  n1.flo.law(D1.abnf.float_std(cs), cs, v, {==})
