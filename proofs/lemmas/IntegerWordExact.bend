# the integer scan accepts exactly the words the integer grammar spells
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../src/arith.bend as Ar
import ../../laws/IntegerReadExactly.bend as L1
import ../../laws/defs/AbnfGrammar.bend as D1
import ../../laws/defs/DocumentSameness.bend as D2
import ../../laws/defs/GrammarDerivations.bend as D3
import ./DateClockText.bend as M1
import ./DecimalArithmetic.bend as M2
import ./DigitsNotDelimiters.bend as M3
import ./DigitsWrittenBack.bend as M4
import ./FailedWalkNameCompare.bend as M5
import ./FreshNamesInRows.bend as M6
import ./NumberScanRefusals.bend as M7
import ./PickAndDigitSteps.bend as M8
import ./PrefixAndTake.bend as M9
import ./ShortTextBounds.bend as M10
import ./SpecialWordCompare.bend as M11

# and is not 48
def gs.eq01(
  +b0: Bool,
  tt: Cmp,
  +h: {Cmp.is_ge(Word.cmp.fin(b0, True{}, tt)) == True{} : Bool}
) -> {Cmp.is_eq(Word.cmp.fin(b0, False{}, tt)) == False{} : Bool}:
  match b0 tt:
    case _b LT{}:
      {==}
    case True{} EQ{}:
      {==}
    case False{} EQ{}:
      Eq.bit.absurd(&2, {True{} == False{} : Bool}, h)
    case _b GT{}:
      {==}

# and is not 0
def gs.d19z(cc: Char, h: {D1.abnf.digit1_9(cc) == True{} : Bool}) -> {Char.is_eq(cc, '0') == False{} : Bool}:
  match cc:
    case Chr{U32{WCon{+b0, +rr}}}:
      gs.eq01(b0, Word.cmp(31n, rr, M4.gs.up(48)), Eq.and.left(Cmp.is_ge(Word.cmp.fin(b0, True{}, Word.cmp(31n, rr,
        M4.gs.up(48)))), Cmp.is_le(Word.cmp.fin(b0, True{}, Word.cmp(31n, rr, M4.gs.up(57)))), h))

# a digit joins the numeral
def gs.join(
  +sg: T.Sign,
  +acc: List<&2, Char>,
  +hh: Char,
  +hx: {Char.is_digit(hh) == True{} : Bool},
  +hn: {M4.nzl(acc) == True{} : Bool}
) -> {T.num.step(M4.ndig(sg, M4.vals(acc)), hh) == M4.ndig(sg, M4.vals(hh <> acc)) : T.Num}:
  Equal.trans(T.Num, T.num.step(M4.ndig(sg, M4.vals(acc)), hh), M4.ndig(sg, T.dec.go(M4.vals(acc), 10, T.dig.val(hh))),
    M4.ndig(sg, M4.vals(hh <> acc)), M4.nw.step(sg, M4.vals(acc), hh, hx),
    Equal.cong(List<&2, U32>, T.Num, ds => M4.ndig(sg, ds), T.dec.go(M4.vals(acc), 10, T.dig.val(hh)),
        M4.vals(hh <> acc),
      M4.dgo(acc, hh, hx, hn)))

# an underscore then a digit: the underscore leaves the numeral as it was
def gs.us.step(
  +sg: T.Sign,
  +ds: List<&2, U32>,
  dd: Char,
  +hd: {Char.is_digit(dd) == True{} : Bool}
) -> {T.num.step(T.num.step(M4.ndig(sg, ds), '_'), dd) == M4.ndig(sg, T.dec.go(ds, 10, T.dig.val(dd))) : T.Num}:
  M6.dg.elim(zz => {T.num.step(T.num.step(M4.ndig(sg, ds), '_'), zz) == M4.ndig(sg, T.dec.go(ds, 10,
      T.dig.val(zz))) : T.Num},
    dd, hd, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# and so the digit joins it
def gs.join2(
  +sg: T.Sign,
  +acc: List<&2, Char>,
  +h2: Char,
  +hx: {Char.is_digit(h2) == True{} : Bool},
  +hn: {M4.nzl(acc) == True{} : Bool}
) -> {T.num.step(T.num.step(M4.ndig(sg, M4.vals(acc)), '_'), h2) == M4.ndig(sg, M4.vals(h2 <> acc)) : T.Num}:
  Equal.trans(T.Num, T.num.step(T.num.step(M4.ndig(sg, M4.vals(acc)), '_'), h2),
    M4.ndig(sg, T.dec.go(M4.vals(acc), 10, T.dig.val(h2))), M4.ndig(sg, M4.vals(h2 <> acc)), gs.us.step(sg,
        M4.vals(acc), h2, hx),
    Equal.cong(List<&2, U32>, T.Num, ds => M4.ndig(sg, ds), T.dec.go(M4.vals(acc), 10, T.dig.val(h2)),
        M4.vals(h2 <> acc),
      M4.dgo(acc, h2, hx, hn)))

# what the scan over the repetition claims: it reads the digits, underscores
# removed, onto the numeral
def gs.Scan(cs: List<&2, Char>, acc: List<&2, Char>, sg: T.Sign) -> Type:
  {T.num.go(cs, M4.ndig(sg, M4.vals(acc))) == M4.ndig(sg, M4.vals(M6.rev.onto(D1.abnf.no_us(cs), acc))) : T.Num}

# a DIGIT first
def gs.scan.d(
  +hh: Char,
  +h2: Char,
  +t2: List<&2, Char>,
  +acc: List<&2, Char>,
  +sg: T.Sign,
  +hx: {Char.is_digit(hh) == True{} : Bool},
  +hn: {M4.nzl(acc) == True{} : Bool},
  ih: {M4.nzl(hh <> acc) == True{} : Bool} -> gs.Scan(h2 <> t2, hh <> acc, sg)
) -> gs.Scan(hh <> h2 <> t2, acc, sg):
  %Equal.sym(Bool, D1.abnf.underscore(hh), False{}, M4.gs.nous(hh, hx)) : {T.num.go(hh <> h2 <> t2, M4.ndig(sg,
    M4.vals(acc))) == M4.ndig(sg, M4.vals(M6.rev.onto(D1.abnf.no_us.pick(_, hh, D1.abnf.no_us(h2 <> t2)),
        acc))) : T.Num}
  Equal.trans(T.Num, T.num.go(h2 <> t2, T.num.step(M4.ndig(sg, M4.vals(acc)), hh)),
    T.num.go(h2 <> t2, M4.ndig(sg, M4.vals(hh <> acc))), M4.ndig(sg, M4.vals(M6.rev.onto(D1.abnf.no_us(h2 <> t2),
        hh <> acc))),
    Equal.cong(T.Num, T.Num, nn => T.num.go(h2 <> t2, nn), T.num.step(M4.ndig(sg, M4.vals(acc)), hh),
      M4.ndig(sg, M4.vals(hh <> acc)), gs.join(sg, acc, hh, hx, hn)),
    ih(M3.nzl.cons(hh, acc, hx, hn)))

# an underscore and a DIGIT first
def gs.scan.u(
  +h2: Char,
  +t2: List<&2, Char>,
  +acc: List<&2, Char>,
  +sg: T.Sign,
  +hx: {Char.is_digit(h2) == True{} : Bool},
  +hn: {M4.nzl(acc) == True{} : Bool},
  ih: {M4.nzl(h2 <> acc) == True{} : Bool} -> gs.Scan(t2, h2 <> acc, sg)
) -> gs.Scan('_' <> h2 <> t2, acc, sg):
  %Equal.sym(Bool, D1.abnf.underscore(h2), False{}, M4.gs.nous(h2, hx)) : {T.num.go('_' <> h2 <> t2, M4.ndig(sg,
    M4.vals(acc))) == M4.ndig(sg, M4.vals(M6.rev.onto(D1.abnf.no_us.pick(_, h2, D1.abnf.no_us(t2)), acc))) : T.Num}
  Equal.trans(T.Num, T.num.go(t2, T.num.step(T.num.step(M4.ndig(sg, M4.vals(acc)), '_'), h2)),
    T.num.go(t2, M4.ndig(sg, M4.vals(h2 <> acc))), M4.ndig(sg, M4.vals(M6.rev.onto(D1.abnf.no_us(t2), h2 <> acc))),
    Equal.cong(T.Num, T.Num, nn => T.num.go(t2, nn), T.num.step(T.num.step(M4.ndig(sg, M4.vals(acc)), '_'), h2),
      M4.ndig(sg, M4.vals(h2 <> acc)), gs.join2(sg, acc, h2, hx, hn)),
    ih(M3.nzl.cons(h2, acc, hx, hn)))

# the numeral scan reads the repetition *( DIGIT / underscore DIGIT ) as its
# digits with the underscores removed
def gs.scan(
  cs: List<&2, Char>,
  +acc: List<&2, Char>,
  +sg: T.Sign,
  +h: {D1.abnf.dec_rep(cs) == True{} : Bool},
  +hn: {M4.nzl(acc) == True{} : Bool}
) -> gs.Scan(cs, acc, sg):
  match cs:
    case []:
      {==}
    case +hh <> tt:
      match tt:
        case []:
          +hx = {M4.gs.dig(hh, h) : {Char.is_digit(hh) == True{} : Bool}}
          %Equal.sym(Bool, D1.abnf.underscore(hh), False{}, M4.gs.nous(hh, hx)) : {T.num.go([hh], M4.ndig(sg,
            M4.vals(acc))) == M4.ndig(sg, M4.vals(M6.rev.onto(D1.abnf.no_us.pick(_, hh, ""), acc))) : T.Num}
          gs.join(sg, acc, hh, hx, hn)
        case +h2 <> +t2:
          M4.gs.rep.two(zs => gs.Scan(zs, acc, sg), hh, h2, t2, D1.abnf.DIGIT(hh), {==}, h,
            hx => hr => gs.scan.d(hh, h2, t2, acc, sg, hx, hn, ha => gs.scan(h2 <> t2, hh <> acc, sg, hr, ha)),
            hx => hr => gs.scan.u(h2, t2, acc, sg, hx, hn, ha => gs.scan(t2, h2 <> acc, sg, hr, ha)))

# what the digits lemma claims
def gs.Dg(cs: List<&2, Char>) -> Type:
  {T.wf.digits(D1.abnf.no_us(cs)) == True{} : Bool}

# a DIGIT first
def gs.digits.d(
  +hh: Char,
  +h2: Char,
  +t2: List<&2, Char>,
  +hx: {Char.is_digit(hh) == True{} : Bool},
  ih: gs.Dg(h2 <> t2)
) -> gs.Dg(hh <> h2 <> t2):
  %Equal.sym(Bool, D1.abnf.underscore(hh), False{}, M4.gs.nous(hh, hx)) :
    {T.wf.digits(D1.abnf.no_us.pick(_, hh, D1.abnf.no_us(h2 <> t2))) == True{} : Bool}
  M3.dgs.cons(hh, D1.abnf.no_us(h2 <> t2), hx, ih)

# an underscore and a DIGIT first
def gs.digits.u(
  +h2: Char,
  +t2: List<&2, Char>,
  +hx: {Char.is_digit(h2) == True{} : Bool},
  ih: gs.Dg(t2)
) -> gs.Dg('_' <> h2 <> t2):
  %Equal.sym(Bool, D1.abnf.underscore(h2), False{}, M4.gs.nous(h2, hx)) :
    {T.wf.digits(D1.abnf.no_us.pick(_, h2, D1.abnf.no_us(t2))) == True{} : Bool}
  M3.dgs.cons(h2, D1.abnf.no_us(t2), hx, ih)

# the repetition with its underscores removed is digits
def gs.digits(cs: List<&2, Char>, +h: {D1.abnf.dec_rep(cs) == True{} : Bool}) -> gs.Dg(cs):
  match cs:
    case []:
      {==}
    case +hh <> tt:
      match tt:
        case []:
          +hx = {M4.gs.dig(hh, h) : {Char.is_digit(hh) == True{} : Bool}}
          %Equal.sym(Bool, D1.abnf.underscore(hh), False{}, M4.gs.nous(hh, hx)) :
            {T.wf.digits(D1.abnf.no_us.pick(_, hh, "")) == True{} : Bool}
          M3.dgs.cons(hh, "", hx, {==})
        case +h2 <> +t2:
          M4.gs.rep.two(zs => gs.Dg(zs), hh, h2, t2, D1.abnf.DIGIT(hh), {==}, h,
            hx => hr => gs.digits.d(hh, h2, t2, hx, gs.digits(h2 <> t2, hr)),
            hx => hr => gs.digits.u(h2, t2, hx, gs.digits(t2, hr)))

# what the colon lemma claims
def gs.Cl(cs: List<&2, Char>) -> Type:
  {T.word.colon(cs) == False{} : Bool}

# a DIGIT first
def gs.colon.d(
  +hh: Char,
  +h2: Char,
  +t2: List<&2, Char>,
  +hx: {Char.is_digit(hh) == True{} : Bool},
  ih: gs.Cl(h2 <> t2)
) -> gs.Cl(hh <> h2 <> t2):
  %Equal.sym(Bool, Char.is_eq(hh, ':'), False{}, M3.dg.nocolon(hh, hx)) :
    {T.word.or(_, T.word.colon(h2 <> t2)) == False{} : Bool}
  ih

# an underscore and a DIGIT first
def gs.colon.u(
  +h2: Char,
  +t2: List<&2, Char>,
  +hx: {Char.is_digit(h2) == True{} : Bool},
  ih: gs.Cl(t2)
) -> gs.Cl('_' <> h2 <> t2):
  %Equal.sym(Bool, Char.is_eq(h2, ':'), False{}, M3.dg.nocolon(h2, hx)) :
    {T.word.or(_, T.word.colon(t2)) == False{} : Bool}
  ih

# the repetition holds no colon
def gs.colon(cs: List<&2, Char>, +h: {D1.abnf.dec_rep(cs) == True{} : Bool}) -> gs.Cl(cs):
  match cs:
    case []:
      {==}
    case +hh <> tt:
      match tt:
        case []:
          %Equal.sym(Bool, Char.is_eq(hh, ':'), False{}, M3.dg.nocolon(hh, M4.gs.dig(hh, h))) :
            {T.word.or(_, T.word.colon([])) == False{} : Bool}
          {==}
        case +h2 <> +t2:
          M4.gs.rep.two(zs => gs.Cl(zs), hh, h2, t2, D1.abnf.DIGIT(hh), {==}, h,
            hx => hr => gs.colon.d(hh, h2, t2, hx, gs.colon(h2 <> t2, hr)),
            hx => hr => gs.colon.u(h2, t2, hx, gs.colon(t2, hr)))

# what the dash lemma claims
def gs.Ds(cs: List<&2, Char>) -> Type:
  {T.word.dash(cs, False{}) == False{} : Bool}

# a DIGIT first
def gs.dash.d(
  +hh: Char,
  +h2: Char,
  +t2: List<&2, Char>,
  +hx: {Char.is_digit(hh) == True{} : Bool},
  ih: gs.Ds(h2 <> t2)
) -> gs.Ds(hh <> h2 <> t2):
  %Equal.sym(Bool, T.word.dash.hit(False{}, hh), False{}, M3.dash.hit.f(False{}, hh, hx)) :
    {T.word.or(_, T.word.dash(h2 <> t2, False{})) == False{} : Bool}
  ih

# an underscore and a DIGIT first
def gs.dash.u(
  +h2: Char,
  +t2: List<&2, Char>,
  +hx: {Char.is_digit(h2) == True{} : Bool},
  ih: gs.Ds(t2)
) -> gs.Ds('_' <> h2 <> t2):
  %Equal.sym(Bool, T.word.dash.hit(False{}, h2), False{}, M3.dash.hit.f(False{}, h2, hx)) :
    {T.word.or(_, T.word.dash(t2, False{})) == False{} : Bool}
  ih

# the repetition holds no dash
def gs.dash(cs: List<&2, Char>, +h: {D1.abnf.dec_rep(cs) == True{} : Bool}) -> gs.Ds(cs):
  match cs:
    case []:
      {==}
    case +hh <> tt:
      match tt:
        case []:
          %Equal.sym(Bool, T.word.dash.hit(False{}, hh), False{}, M3.dash.hit.f(False{}, hh, M4.gs.dig(hh, h))) :
            {T.word.or(_, T.word.dash([], False{})) == False{} : Bool}
          {==}
        case +h2 <> +t2:
          M4.gs.rep.two(zs => gs.Ds(zs), hh, h2, t2, D1.abnf.DIGIT(hh), {==}, h,
            hx => hr => gs.dash.d(hh, h2, t2, hx, gs.dash(h2 <> t2, hr)),
            hx => hr => gs.dash.u(h2, t2, hx, gs.dash(t2, hr)))

# a digit then the repetition holds no colon
def gs.hc(
  +hh: Char,
  +rest: List<&2, Char>,
  +hx: {Char.is_digit(hh) == True{} : Bool},
  +hr: {D1.abnf.dec_rep(rest) == True{} : Bool}
) -> {T.word.colon(hh <> rest) == False{} : Bool}:
  %Equal.sym(Bool, Char.is_eq(hh, ':'), False{}, M3.dg.nocolon(hh, hx)) :
    {T.word.or(_, T.word.colon(rest)) == False{} : Bool}
  gs.colon(rest, hr)

# and no dash after its first character
def gs.hd1(
  +hh: Char,
  +rest: List<&2, Char>,
  +hx: {Char.is_digit(hh) == True{} : Bool},
  +hr: {D1.abnf.dec_rep(rest) == True{} : Bool}
) -> {T.word.dash(hh <> rest, False{}) == False{} : Bool}:
  %Equal.sym(Bool, T.word.dash.hit(False{}, hh), False{}, M3.dash.hit.f(False{}, hh, hx)) :
    {T.word.or(_, T.word.dash(rest, False{})) == False{} : Bool}
  gs.dash(rest, hr)

# a word that starts with a plus and a digit is no special: it differs from
# +inf and +nan at the digit, and from the others at the plus
def gs.spec.p(
  +hh: Char,
  +rest: List<&2, Char>,
  +ei: {False{} == Char.is_eq(hh, 'i') : Bool},
  +en: {False{} == Char.is_eq(hh, 'n') : Bool}
) -> {T.word.spec(String.from_list('+' <> hh <> rest)) == T.GotBad{""} : T.Got}:
  Equal.trans(T.Got,
    T.word.spec.inf2(T.str.eq.step(String.from_list(rest), "nf", Char.is_eq(hh, 'i')), False{},
      String.from_list('+' <> hh <> rest)),
    T.word.spec.inf2(False{}, False{}, String.from_list('+' <> hh <> rest)),
    T.GotBad{""},
    Equal.cong(Bool, T.Got, bb => T.word.spec.inf2(bb, False{}, String.from_list('+' <> hh <> rest)),
      T.str.eq.step(String.from_list(rest), "nf", Char.is_eq(hh, 'i')), False{},
      M10.str.eq.off2(String.from_list(rest), "nf", Char.is_eq(hh, 'i'), ei)),
    Equal.cong(Bool, T.Got, bb => T.word.spec.nan2(bb, False{}),
      T.str.eq.step(String.from_list(rest), "an", Char.is_eq(hh, 'n')), False{},
      M10.str.eq.off2(String.from_list(rest), "an", Char.is_eq(hh, 'n'), en)))

# a digit that is no underscore is kept in front of the rest
def gs.nu(
  +hh: Char,
  +tt: List<&2, Char>,
  +hu: {D1.abnf.underscore(hh) == False{} : Bool}
) -> {SCon{hh, D1.abnf.no_us(tt)} == D1.abnf.no_us(hh <> tt) : String}:
  %Equal.sym(Bool, D1.abnf.underscore(hh), False{}, hu) :
    {SCon{hh, D1.abnf.no_us(tt)} == D1.abnf.no_us.pick(_, hh, D1.abnf.no_us(tt)) : String}
  {==}

# a lone character that is an unsigned-dec-int is a DIGIT
def gs.body.z(
  +hh: Char,
  +ed: {D1.abnf.DIGIT(hh) == False{} : Bool}
) -> {False{} == D1.abnf.unsigned_dec_int([hh]) : Bool}:
  %Equal.sym(Bool, D1.abnf.DIGIT(hh), False{}, ed) : {False{} == Bool.or(Bool.and(_, True{}),
    Bool.and(D1.abnf.digit1_9(hh), False{})) : Bool}
  Equal.sym(Bool, Bool.and(D1.abnf.digit1_9(hh), False{}), False{}, M4.gs.andf(D1.abnf.digit1_9(hh)))

# so it is a digit
def gs.body.one(
  +hh: Char,
  dd: Bool,
  +ed: {D1.abnf.DIGIT(hh) == dd : Bool},
  +hu: {D1.abnf.unsigned_dec_int([hh]) == True{} : Bool}
) -> {Char.is_digit(hh) == True{} : Bool}:
  match dd:
    case True{}:
      M4.gs.dig(hh, ed)
    case False{}:
      Eq.bit.absurd(&2, {Char.is_digit(hh) == True{} : Bool}, Equal.trans(Bool, False{},
        D1.abnf.unsigned_dec_int([hh]), True{}, gs.body.z(hh, ed), hu))

# a longer one is a digit1-9 and the repetition
def gs.body.e(
  +hh: Char,
  +t1: Char,
  +ts: List<&2, Char>
) -> {Bool.and(D1.abnf.digit1_9(hh), D1.abnf.dec_rep(t1 <> ts)) == D1.abnf.unsigned_dec_int(hh <> t1 <> ts)
  : Bool}:
  %Equal.sym(Bool, Bool.and(D1.abnf.DIGIT(hh), False{}), False{}, M4.gs.andf(D1.abnf.DIGIT(hh))) :
    {Bool.and(D1.abnf.digit1_9(hh), D1.abnf.dec_rep(t1 <> ts)) == Bool.or(_, Bool.and(D1.abnf.digit1_9(hh),
    D1.abnf.dec_rep(t1 <> ts))) : Bool}
  {==}

# so a longer one's first character is a digit1-9
def gs.body.l(
  +hh: Char,
  +t1: Char,
  +ts: List<&2, Char>,
  hu: {D1.abnf.unsigned_dec_int(hh <> t1 <> ts) == True{} : Bool}
) -> {D1.abnf.digit1_9(hh) == True{} : Bool}:
  Eq.and.left(D1.abnf.digit1_9(hh), D1.abnf.dec_rep(t1 <> ts), Equal.trans(Bool, Bool.and(D1.abnf.digit1_9(hh),
    D1.abnf.dec_rep(t1 <> ts)), D1.abnf.unsigned_dec_int(hh <> t1 <> ts), True{}, gs.body.e(hh, t1, ts), hu))

# and the rest is the repetition
def gs.body.r(
  +hh: Char,
  +t1: Char,
  +ts: List<&2, Char>,
  hu: {D1.abnf.unsigned_dec_int(hh <> t1 <> ts) == True{} : Bool}
) -> {D1.abnf.dec_rep(t1 <> ts) == True{} : Bool}:
  Eq.and.right(D1.abnf.digit1_9(hh), D1.abnf.dec_rep(t1 <> ts), Equal.trans(Bool, Bool.and(D1.abnf.digit1_9(hh),
    D1.abnf.dec_rep(t1 <> ts)), D1.abnf.unsigned_dec_int(hh <> t1 <> ts), True{}, gs.body.e(hh, t1, ts), hu))

# with no sign, dec-int is unsigned-dec-int
def gs.top.hu(
  +hh: Char,
  +tt: List<&2, Char>,
  +em: {D1.abnf.minus(hh) == False{} : Bool},
  +ep: {D1.abnf.plus(hh) == False{} : Bool}
) -> {D1.abnf.unsigned_dec_int(hh <> tt) == D1.abnf.dec_int(hh <> tt) : Bool}:
  %Equal.sym(Bool, D1.abnf.minus(hh), False{}, em) : {D1.abnf.unsigned_dec_int(hh <> tt)
    == Bool.or(Bool.and(Bool.or(_, D1.abnf.plus(hh)), D1.abnf.unsigned_dec_int(tt)),
    D1.abnf.unsigned_dec_int(hh <> tt)) : Bool}
  %Equal.sym(Bool, D1.abnf.plus(hh), False{}, ep) : {D1.abnf.unsigned_dec_int(hh <> tt)
    == Bool.or(Bool.and(Bool.or(False{}, _), D1.abnf.unsigned_dec_int(tt)),
    D1.abnf.unsigned_dec_int(hh <> tt)) : Bool}
  {==}

# The digits of a prefixed integer. dig.val reads a digit, or a letter a to f
# in either case, as its value, and anything else as 99; dig.ok takes the
# value when it fits the base, which is exactly the radix's digit rule. The
# six letters of each case are taken one at a time, as dg.elim takes digits.

# a code point's comparisons with 97 and 102, seven bits each, the bits above
# the seventh comparing as cc with zero
def lw.cp(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +cc: Cmp) -> Bool:
  Bool.and(Cmp.is_ge(Word.cmp.fin(b0, True{}, Word.cmp.fin(b1, False{}, Word.cmp.fin(b2, False{}, Word.cmp.fin(b3,
    False{}, Word.cmp.fin(b4, False{}, Word.cmp.fin(b5, True{}, Word.cmp.fin(b6, True{}, cc)))))))),
    Cmp.is_le(Word.cmp.fin(b0, False{}, Word.cmp.fin(b1, True{}, Word.cmp.fin(b2, True{}, Word.cmp.fin(b3, False{},
      Word.cmp.fin(b4, False{}, Word.cmp.fin(b5, True{}, Word.cmp.fin(b6, True{}, cc)))))))))

# the char of seven low bits and zeros above them
def lw.ch(b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool, b6: Bool) -> Char:
  Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, Eq.zw(25n)}}}}}}}}}

# the seven low bits of a lower case letter from a to f, highest first: six
# patterns are the letters, and the others compare out of the range
def lw.bits(
  -P: Char -> Type,
  +b6: Bool,
  +b5: Bool,
  +b4: Bool,
  +b3: Bool,
  +b2: Bool,
  +b1: Bool,
  +b0: Bool,
  h: {lw.cp(b0, b1, b2, b3, b4, b5, b6, EQ{}) == True{} : Bool},
  pa: P('a'),
  pb: P('b'),
  pc: P('c'),
  pd: P('d'),
  pe: P('e'),
  pf: P('f')
) -> P(lw.ch(b0, b1, b2, b3, b4, b5, b6)):
  match b6:
    case False{}:
      Eq.bit.absurd(&1, P(lw.ch(b0, b1, b2, b3, b4, b5, False{})), h)
    case True{}:
      match b5:
        case False{}:
          Eq.bit.absurd(&1, P(lw.ch(b0, b1, b2, b3, b4, False{}, True{})), h)
        case True{}:
          match b4:
            case True{}:
              Eq.bit.absurd(&1, P(lw.ch(b0, b1, b2, b3, True{}, True{}, True{})), h)
            case False{}:
              match b3:
                case True{}:
                  Eq.bit.absurd(&1, P(lw.ch(b0, b1, b2, True{}, False{}, True{}, True{})), h)
                case False{}:
                  match b2 b1 b0:
                    case False{} False{} False{}:
                      Eq.bit.absurd(&1, P(lw.ch(False{}, False{}, False{}, False{}, False{}, True{}, True{})), h)
                    case False{} False{} True{}:
                      pa
                    case False{} True{} False{}:
                      pb
                    case False{} True{} True{}:
                      pc
                    case True{} False{} False{}:
                      pd
                    case True{} False{} True{}:
                      pe
                    case True{} True{} False{}:
                      pf
                    case True{} True{} True{}:
                      Eq.bit.absurd(&1, P(lw.ch(True{}, True{}, True{}, False{}, False{}, True{}, True{})), h)

# the bits above the seventh are zero, or the code point is out of the range
def lw.at(
  -P: Char -> Type,
  cc: Cmp,
  +b6: Bool,
  +b5: Bool,
  +b4: Bool,
  +b3: Bool,
  +b2: Bool,
  +b1: Bool,
  +b0: Bool,
  +rest: Word(25n),
  ec: {Word.cmp(25n, rest, Eq.zw(25n)) == cc : Cmp},
  h: {lw.cp(b0, b1, b2, b3, b4, b5, b6, cc) == True{} : Bool},
  pa: P('a'),
  pb: P('b'),
  pc: P('c'),
  pd: P('d'),
  pe: P('e'),
  pf: P('f')
) -> P(Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, rest}}}}}}}}}):
  match cc:
    case LT{}:
      Eq.bit.gone(&1, P(Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, rest}}}}}}}}}),
        Eq.bit.clash2(Equal.trans(Bool, True{}, Cmp.is_lt(Word.cmp(25n, rest, Eq.zw(25n))), False{},
          Equal.sym(Bool, Cmp.is_lt(Word.cmp(25n, rest, Eq.zw(25n))), True{},
            Equal.cong(Cmp, Bool, xx => Cmp.is_lt(xx), Word.cmp(25n, rest, Eq.zw(25n)), LT{}, ec)),
          Eq.zw_nlt(25n, rest))))
    case GT{}:
      Eq.bit.absurd(&1, P(Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, rest}}}}}}}}}), h)
    case EQ{}:
      er = Equal.sym(Word(25n), rest, Eq.zw(25n), Eq.word_eq(25n, rest, Eq.zw(25n), ec))
      %er : P(Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, _}}}}}}}}})
      lw.bits(P, b6, b5, b4, b3, b2, b1, b0, h, pa, pb, pc, pd, pe, pf)

# a claim made of each lower case letter from a to f is made of every
# character from 97 to 102
def lw.elim(
  -P: Char -> Type,
  cc: Char,
  h: {Bool.and(U32.is_ge(Char.to_u32(cc), 97), U32.is_le(Char.to_u32(cc), 102)) == True{} : Bool},
  pa: P('a'),
  pb: P('b'),
  pc: P('c'),
  pd: P('d'),
  pe: P('e'),
  pf: P('f')
) -> P(cc):
  match cc:
    case Chr{U32{WCon{+b0, WCon{+b1, WCon{+b2, WCon{+b3, WCon{+b4, WCon{+b5, WCon{+b6, +rest}}}}}}}}}:
      lw.at(P, Word.cmp(25n, rest, Eq.zw(25n)), b6, b5, b4, b3, b2, b1, b0, rest, {==}, h, pa, pb, pc, pd, pe, pf)

# a code point's comparisons with 65 and 70, seven bits each, the bits above
# the seventh comparing as cc with zero
def up.cp(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +cc: Cmp) -> Bool:
  Bool.and(Cmp.is_ge(Word.cmp.fin(b0, True{}, Word.cmp.fin(b1, False{}, Word.cmp.fin(b2, False{}, Word.cmp.fin(b3,
    False{}, Word.cmp.fin(b4, False{}, Word.cmp.fin(b5, False{}, Word.cmp.fin(b6, True{}, cc)))))))),
    Cmp.is_le(Word.cmp.fin(b0, False{}, Word.cmp.fin(b1, True{}, Word.cmp.fin(b2, True{}, Word.cmp.fin(b3, False{},
      Word.cmp.fin(b4, False{}, Word.cmp.fin(b5, False{}, Word.cmp.fin(b6, True{}, cc)))))))))

# the char of seven low bits and zeros above them
def up.ch(b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool, b6: Bool) -> Char:
  Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, Eq.zw(25n)}}}}}}}}}

# the seven low bits of an upper case letter from A to F, highest first: six
# patterns are the letters, and the others compare out of the range
def up.bits(
  -P: Char -> Type,
  +b6: Bool,
  +b5: Bool,
  +b4: Bool,
  +b3: Bool,
  +b2: Bool,
  +b1: Bool,
  +b0: Bool,
  h: {up.cp(b0, b1, b2, b3, b4, b5, b6, EQ{}) == True{} : Bool},
  pA: P('A'),
  pB: P('B'),
  pC: P('C'),
  pD: P('D'),
  pE: P('E'),
  pF: P('F')
) -> P(up.ch(b0, b1, b2, b3, b4, b5, b6)):
  match b6:
    case False{}:
      Eq.bit.absurd(&1, P(up.ch(b0, b1, b2, b3, b4, b5, False{})), h)
    case True{}:
      match b5:
        case True{}:
          Eq.bit.absurd(&1, P(up.ch(b0, b1, b2, b3, b4, True{}, True{})), h)
        case False{}:
          match b4:
            case True{}:
              Eq.bit.absurd(&1, P(up.ch(b0, b1, b2, b3, True{}, False{}, True{})), h)
            case False{}:
              match b3:
                case True{}:
                  Eq.bit.absurd(&1, P(up.ch(b0, b1, b2, True{}, False{}, False{}, True{})), h)
                case False{}:
                  match b2 b1 b0:
                    case False{} False{} False{}:
                      Eq.bit.absurd(&1, P(up.ch(False{}, False{}, False{}, False{}, False{}, False{}, True{})), h)
                    case False{} False{} True{}:
                      pA
                    case False{} True{} False{}:
                      pB
                    case False{} True{} True{}:
                      pC
                    case True{} False{} False{}:
                      pD
                    case True{} False{} True{}:
                      pE
                    case True{} True{} False{}:
                      pF
                    case True{} True{} True{}:
                      Eq.bit.absurd(&1, P(up.ch(True{}, True{}, True{}, False{}, False{}, False{}, True{})), h)

# the bits above the seventh are zero, or the code point is out of the range
def up.at(
  -P: Char -> Type,
  cc: Cmp,
  +b6: Bool,
  +b5: Bool,
  +b4: Bool,
  +b3: Bool,
  +b2: Bool,
  +b1: Bool,
  +b0: Bool,
  +rest: Word(25n),
  ec: {Word.cmp(25n, rest, Eq.zw(25n)) == cc : Cmp},
  h: {up.cp(b0, b1, b2, b3, b4, b5, b6, cc) == True{} : Bool},
  pA: P('A'),
  pB: P('B'),
  pC: P('C'),
  pD: P('D'),
  pE: P('E'),
  pF: P('F')
) -> P(Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, rest}}}}}}}}}):
  match cc:
    case LT{}:
      Eq.bit.gone(&1, P(Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, rest}}}}}}}}}),
        Eq.bit.clash2(Equal.trans(Bool, True{}, Cmp.is_lt(Word.cmp(25n, rest, Eq.zw(25n))), False{},
          Equal.sym(Bool, Cmp.is_lt(Word.cmp(25n, rest, Eq.zw(25n))), True{},
            Equal.cong(Cmp, Bool, xx => Cmp.is_lt(xx), Word.cmp(25n, rest, Eq.zw(25n)), LT{}, ec)),
          Eq.zw_nlt(25n, rest))))
    case GT{}:
      Eq.bit.absurd(&1, P(Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, rest}}}}}}}}}), h)
    case EQ{}:
      er = Equal.sym(Word(25n), rest, Eq.zw(25n), Eq.word_eq(25n, rest, Eq.zw(25n), ec))
      %er : P(Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, _}}}}}}}}})
      up.bits(P, b6, b5, b4, b3, b2, b1, b0, h, pA, pB, pC, pD, pE, pF)

# a claim made of each upper case letter from A to F is made of every
# character from 65 to 70
def up.elim(
  -P: Char -> Type,
  cc: Char,
  h: {Bool.and(U32.is_ge(Char.to_u32(cc), 65), U32.is_le(Char.to_u32(cc), 70)) == True{} : Bool},
  pA: P('A'),
  pB: P('B'),
  pC: P('C'),
  pD: P('D'),
  pE: P('E'),
  pF: P('F')
) -> P(cc):
  match cc:
    case Chr{U32{WCon{+b0, WCon{+b1, WCon{+b2, WCon{+b3, WCon{+b4, WCon{+b5, WCon{+b6, +rest}}}}}}}}}:
      up.at(P, Word.cmp(25n, rest, Eq.zw(25n)), b6, b5, b4, b3, b2, b1, b0, rest, {==}, h, pA, pB, pC, pD, pE, pF)

# the base of a radix: 16, 8 or 2
def n1.rb(rx: D1.ARadix) -> U32:
  match rx:
    case D1.AHex{}:
      16
    case D1.AOct{}:
      8
    case D1.ABin{}:
      2

# what the classification claims of a character: dig.ok takes its value in
# the radix's base exactly when it is one of the radix's digits
def n1.cls.P(+rx: D1.ARadix, +cc: Char) -> Type:
  {T.dig.ok(T.dig.val(cc), n1.rb(rx)) == D1.abnf.radix_digit(rx, cc) : Bool}

# a digit
def n1.cls.dig(rx: D1.ARadix, cc: Char, hc: {Char.is_digit(cc) == True{} : Bool}) -> n1.cls.P(rx, cc):
  match rx:
    case D1.AHex{}:
      M6.dg.elim(zz => n1.cls.P(D1.AHex{}, zz), cc, hc, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})
    case D1.AOct{}:
      M6.dg.elim(zz => n1.cls.P(D1.AOct{}, zz), cc, hc, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})
    case D1.ABin{}:
      M6.dg.elim(zz => n1.cls.P(D1.ABin{}, zz), cc, hc, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# a lower case letter a to f
def n1.cls.low(
  rx: D1.ARadix,
  cc: Char,
  hc: {Bool.and(U32.is_ge(Char.to_u32(cc), 97), U32.is_le(Char.to_u32(cc), 102)) == True{} : Bool}
) -> n1.cls.P(rx, cc):
  match rx:
    case D1.AHex{}:
      lw.elim(zz => n1.cls.P(D1.AHex{}, zz), cc, hc, {==}, {==}, {==}, {==}, {==}, {==})
    case D1.AOct{}:
      lw.elim(zz => n1.cls.P(D1.AOct{}, zz), cc, hc, {==}, {==}, {==}, {==}, {==}, {==})
    case D1.ABin{}:
      lw.elim(zz => n1.cls.P(D1.ABin{}, zz), cc, hc, {==}, {==}, {==}, {==}, {==}, {==})

# an upper case letter A to F
def n1.cls.up(
  rx: D1.ARadix,
  cc: Char,
  hc: {Bool.and(U32.is_ge(Char.to_u32(cc), 65), U32.is_le(Char.to_u32(cc), 70)) == True{} : Bool}
) -> n1.cls.P(rx, cc):
  match rx:
    case D1.AHex{}:
      up.elim(zz => n1.cls.P(D1.AHex{}, zz), cc, hc, {==}, {==}, {==}, {==}, {==}, {==})
    case D1.AOct{}:
      up.elim(zz => n1.cls.P(D1.AOct{}, zz), cc, hc, {==}, {==}, {==}, {==}, {==}, {==})
    case D1.ABin{}:
      up.elim(zz => n1.cls.P(D1.ABin{}, zz), cc, hc, {==}, {==}, {==}, {==}, {==}, {==})

# zero is at most anything
def n1.le0(xx: Nat) -> {Cmp.is_le(Nat.cmp(0n, xx)) == True{} : Bool}:
  match xx:
    case 0n:
      {==}
    case 1n+_x:
      {==}

# at most a is at most a + k
def n1.le.add(
  nn: Nat,
  aa: Nat,
  +kk: Nat,
  hh: {Cmp.is_le(Nat.cmp(nn, aa)) == True{} : Bool}
) -> {Cmp.is_le(Nat.cmp(nn, Nat.add(aa, kk))) == True{} : Bool}:
  match nn aa:
    case 0n a0:
      n1.le0(Nat.add(a0, kk))
    case 1n+m1 0n:
      Eq.bit.absurd(&2, {Cmp.is_le(Nat.cmp(1n+m1, Nat.add(0n, kk))) == True{} : Bool}, hh)
    case 1n+m1 1n+a1:
      n1.le.add(m1, a1, kk, hh)

# a code point past aa + kk is past aa
def n1.le.no(
  bb: Bool,
  +nn: Nat,
  +aa: Nat,
  +kk: Nat,
  eb: {Cmp.is_le(Nat.cmp(nn, aa)) == bb : Bool},
  hh: {Cmp.is_le(Nat.cmp(nn, Nat.add(aa, kk))) == False{} : Bool}
) -> {Cmp.is_le(Nat.cmp(nn, aa)) == False{} : Bool}:
  match bb:
    case True{}:
      Eq.bit.absurd2(&2, {Cmp.is_le(Nat.cmp(nn, aa)) == False{} : Bool}, Equal.trans(Bool, True{},
        Cmp.is_le(Nat.cmp(nn, Nat.add(aa, kk))), False{}, Equal.sym(Bool, Cmp.is_le(Nat.cmp(nn, Nat.add(aa, kk))),
        True{},
        n1.le.add(nn, aa, kk, eb)), hh))
    case False{}:
      eb

# a code point that is no digit is none from 48 to hi, for hi at most 57
def n1.rng.nd(
  gg: Bool,
  +cp: U32,
  +hi: Nat,
  +kk: Nat,
  +hu: U32,
  eh: {U32.to_nat(hu) == hi : Nat},
  ek: {Nat.add(hi, kk) == 57n : Nat},
  +eg: {U32.is_ge(cp, 48) == gg : Bool},
  hd: {Bool.and(U32.is_ge(cp, 48), U32.is_le(cp, 57)) == False{} : Bool}
) -> {Bool.and(U32.is_ge(cp, 48), U32.is_le(cp, hu)) == False{} : Bool}:
  match gg:
    case True{}:
      +hle = {Equal.trans(Bool, U32.is_le(cp, 57), Bool.and(U32.is_ge(cp, 48), U32.is_le(cp, 57)), False{},
        Equal.cong(Bool, Bool, xx => Bool.and(xx, U32.is_le(cp, 57)), True{}, U32.is_ge(cp, 48), Equal.sym(Bool,
        U32.is_ge(cp, 48), True{}, eg)), hd) : {U32.is_le(cp, 57) == False{} : Bool}}
      +h57 = {Equal.trans(Bool, Cmp.is_le(Nat.cmp(U32.to_nat(cp), Nat.add(hi, kk))), U32.is_le(cp, 57), False{},
        Equal.trans(Bool, Cmp.is_le(Nat.cmp(U32.to_nat(cp), Nat.add(hi, kk))), Cmp.is_le(Nat.cmp(U32.to_nat(cp), 57n)),
        U32.is_le(cp, 57), Equal.cong(Nat, Bool, xx => Cmp.is_le(Nat.cmp(U32.to_nat(cp), xx)), Nat.add(hi, kk), 57n,
        ek), Equal.sym(Bool, U32.is_le(cp, 57), Cmp.is_le(Nat.cmp(U32.to_nat(cp), 57n)), M2.u.le(cp, 57))), hle)
        : {Cmp.is_le(Nat.cmp(U32.to_nat(cp), Nat.add(hi, kk))) == False{} : Bool}}
      %Equal.sym(Bool, U32.is_ge(cp, 48), True{}, eg) : {Bool.and(_, U32.is_le(cp, hu)) == False{} : Bool}
      Equal.trans(Bool, U32.is_le(cp, hu), Cmp.is_le(Nat.cmp(U32.to_nat(cp), hi)), False{}, Equal.trans(Bool,
        U32.is_le(cp, hu), Cmp.is_le(Nat.cmp(U32.to_nat(cp), U32.to_nat(hu))), Cmp.is_le(Nat.cmp(U32.to_nat(cp), hi)),
        M2.u.le(cp, hu), Equal.cong(Nat, Bool, xx => Cmp.is_le(Nat.cmp(U32.to_nat(cp), xx)), U32.to_nat(hu), hi, eh)),
        n1.le.no(Cmp.is_le(Nat.cmp(U32.to_nat(cp), hi)), U32.to_nat(cp), hi, kk, {==}, h57))
    case False{}:
      %Equal.sym(Bool, U32.is_ge(cp, 48), False{}, eg) : {Bool.and(_, U32.is_le(cp, hu)) == False{} : Bool}
      {==}

# no digit of any base is 99
def n1.cls.none.go(
  rx: D1.ARadix,
  +cp: U32,
  +ed: {Bool.and(U32.is_ge(cp, 48), U32.is_le(cp, 57)) == False{} : Bool},
  +el: {Bool.and(U32.is_ge(cp, 97), U32.is_le(cp, 102)) == False{} : Bool},
  +eu: {Bool.and(U32.is_ge(cp, 65), U32.is_le(cp, 70)) == False{} : Bool}
) -> {T.dig.ok(99, n1.rb(rx)) == D1.abnf.radix_digit(rx, Chr{cp}) : Bool}:
  match rx:
    case D1.AHex{}:
      %Equal.sym(Bool, Bool.and(U32.is_ge(cp, 48), U32.is_le(cp, 57)), False{}, ed) : {False{} == Bool.or(_,
        Bool.or(D1.abnf.range(cp, 65, 70), D1.abnf.range(cp, 97, 102))) : Bool}
      %Equal.sym(Bool, Bool.and(U32.is_ge(cp, 65), U32.is_le(cp, 70)), False{}, eu) : {False{} == Bool.or(False{},
        Bool.or(_, D1.abnf.range(cp, 97, 102))) : Bool}
      %Equal.sym(Bool, Bool.and(U32.is_ge(cp, 97), U32.is_le(cp, 102)), False{}, el) : {False{} == Bool.or(False{},
        Bool.or(False{}, _)) : Bool}
      {==}
    case D1.AOct{}:
      Equal.sym(Bool, Bool.and(U32.is_ge(cp, 48), U32.is_le(cp, 55)), False{}, n1.rng.nd(U32.is_ge(cp, 48), cp, 55n,
        2n, 55, {==}, {==}, {==}, ed))
    case D1.ABin{}:
      Equal.sym(Bool, Bool.and(U32.is_ge(cp, 48), U32.is_le(cp, 49)), False{}, n1.rng.nd(U32.is_ge(cp, 48), cp, 49n,
        8n, 49, {==}, {==}, {==}, ed))

# a character that is no digit and no letter a to f in either case
def n1.cls.none(
  rx: D1.ARadix,
  +cp: U32,
  +ed: {Bool.and(U32.is_ge(cp, 48), U32.is_le(cp, 57)) == False{} : Bool},
  +el: {Bool.and(U32.is_ge(cp, 97), U32.is_le(cp, 102)) == False{} : Bool},
  +eu: {Bool.and(U32.is_ge(cp, 65), U32.is_le(cp, 70)) == False{} : Bool}
) -> n1.cls.P(rx, Chr{cp}):
  %Equal.sym(Bool, Bool.and(U32.is_ge(cp, 48), U32.is_le(cp, 57)), False{}, ed) : {T.dig.ok(T.dig.dec(_, cp),
    n1.rb(rx)) == D1.abnf.radix_digit(rx, Chr{cp}) : Bool}
  %Equal.sym(Bool, Bool.and(U32.is_ge(cp, 97), U32.is_le(cp, 102)), False{}, el) : {T.dig.ok(T.dig.low(_, cp),
    n1.rb(rx)) == D1.abnf.radix_digit(rx, Chr{cp}) : Bool}
  %Equal.sym(Bool, Bool.and(U32.is_ge(cp, 65), U32.is_le(cp, 70)), False{}, eu) : {T.dig.ok(T.dig.up(_, cp),
    n1.rb(rx)) == D1.abnf.radix_digit(rx, Chr{cp}) : Bool}
  n1.cls.none.go(rx, cp, ed, el, eu)

# a character of a code point that is a digit, a letter a to f, a letter A
# to F, or none of them
def n1.cls.go(
  dd: Bool,
  ll: Bool,
  uu: Bool,
  rx: D1.ARadix,
  +cp: U32,
  +ed: {Bool.and(U32.is_ge(cp, 48), U32.is_le(cp, 57)) == dd : Bool},
  +el: {Bool.and(U32.is_ge(cp, 97), U32.is_le(cp, 102)) == ll : Bool},
  +eu: {Bool.and(U32.is_ge(cp, 65), U32.is_le(cp, 70)) == uu : Bool}
) -> n1.cls.P(rx, Chr{cp}):
  match dd:
    case True{}:
      n1.cls.dig(rx, Chr{cp}, ed)
    case False{}:
      match ll:
        case True{}:
          n1.cls.low(rx, Chr{cp}, el)
        case False{}:
          match uu:
            case True{}:
              n1.cls.up(rx, Chr{cp}, eu)
            case False{}:
              n1.cls.none(rx, cp, ed, el, eu)

# dig.ok takes a character's value in the radix's base exactly when it is one
# of the radix's digits
def n1.cls(rx: D1.ARadix, cc: Char) -> n1.cls.P(rx, cc):
  match cc:
    case Chr{+cp}:
      n1.cls.go(Bool.and(U32.is_ge(cp, 48), U32.is_le(cp, 57)), Bool.and(U32.is_ge(cp, 97), U32.is_le(cp, 102)),
        Bool.and(U32.is_ge(cp, 65), U32.is_le(cp, 70)), rx, cp, {==}, {==}, {==})

# The integer's shape. A finished scan holds an integer, or one out of range,
# when it ends after a leading zero, after a digit of a decimal integer, or
# after a digit of a prefixed integer that no sign came before.

# whether a finished scan's kind holds an integer, sd saying whether the word
# starts with a sign
def n1.ish.nk(nk: T.NK, saw: Bool, us: Bool, +sd: Bool) -> Bool:
  match nk:
    case T.NZero{}:
      Bool.not(us)
    case T.NDig{}:
      Bool.and(saw, Bool.not(us))
    case T.NBase{}:
      Bool.and(saw, Bool.and(Bool.not(us), Bool.not(sd)))
    case _k:
      False{}

# whether a finished scan holds an integer
def n1.ish(st: T.Num, +sd: Bool) -> Bool:
  match st:
    case T.Num{nk, _sign, _base, _ds, us, saw, _why}:
      n1.ish.nk(nk, saw, us, sd)

# whether a numeral kind is a float's, or a failure
def n1.isf.nk(nk: T.NK) -> Bool:
  match nk:
    case T.NFrac{}:
      True{}
    case T.NExp{}:
      True{}
    case T.NEDig{}:
      True{}
    case T.NBad{}:
      True{}
    case _k:
      False{}

# whether a numeral scan is in a float or has failed
def n1.isf(st: T.Num) -> Bool:
  match st:
    case T.Num{nk, _sign, _base, _ds, _us, _saw, _why}:
      n1.isf.nk(nk)

# a digit of a float, taken or refused
def n1.isf.digit(
  ok: Bool,
  +cc: Char,
  +nk: T.NK,
  +sg: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  hn: {n1.isf.nk(nk) == True{} : Bool}
) -> {n1.isf(T.num.digit.ok(ok, cc, nk, sg, base, ds)) == True{} : Bool}:
  match ok:
    case True{}:
      hn
    case False{}:
      {==}

# an underscore of a float, taken or refused
def n1.isf.us(
  ok: Bool,
  +nk: T.NK,
  +sg: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +why: String,
  hn: {n1.isf.nk(nk) == True{} : Bool}
) -> {n1.isf(T.num.us.go(ok, nk, sg, base, ds, why)) == True{} : Bool}:
  match ok:
    case True{}:
      hn
    case False{}:
      {==}

# an exponent mark in a float, taken or refused
def n1.isf.exp(ok: Bool, +sg: T.Sign) -> {n1.isf(T.num.exp.go(ok, sg)) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

# the character after a fraction's digit keeps a float's state
def n1.isf.frac(
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
  +why: String
) -> {n1.isf(T.num.frac.go(dd, uu, e1, e2, T.Num{T.NFrac{}, sg, base, ds, us, saw, why}, cc)) == True{} : Bool}:
  match dd uu:
    case True{} _u:
      n1.isf.digit(T.dig.ok(T.dig.val(cc), base), cc, T.NFrac{}, sg, base, ds, {==})
    case False{} True{}:
      n1.isf.us(Bool.and(saw, Bool.not(us)), T.NFrac{}, sg, base, ds, why, {==})
    case False{} False{}:
      match e1 e2:
        case True{} _e:
          n1.isf.exp(Bool.and(saw, Bool.not(us)), sg)
        case False{} True{}:
          n1.isf.exp(Bool.and(saw, Bool.not(us)), sg)
        case False{} False{}:
          {==}

# the character after an exponent's e keeps a float's state
def n1.isf.expon(
  pp: Bool,
  mm: Bool,
  dd: Bool,
  +cc: Char,
  +sg: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String
) -> {n1.isf(T.num.expon.go(pp, mm, dd, T.Num{T.NExp{}, sg, base, ds, us, saw, why}, cc)) == True{} : Bool}:
  match pp mm dd:
    case True{} _m _d:
      {==}
    case False{} True{} _d:
      {==}
    case False{} False{} True{}:
      n1.isf.digit(T.dig.ok(T.dig.val(cc), base), cc, T.NEDig{}, sg, base, ds, {==})
    case False{} False{} False{}:
      {==}

# the character after an exponent's digit keeps a float's state
def n1.isf.edig(
  dd: Bool,
  uu: Bool,
  +cc: Char,
  +sg: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String
) -> {n1.isf(T.num.edig.go(dd, uu, T.Num{T.NEDig{}, sg, base, ds, us, saw, why}, cc)) == True{} : Bool}:
  match dd uu:
    case True{} _u:
      n1.isf.digit(T.dig.ok(T.dig.val(cc), base), cc, T.NEDig{}, sg, base, ds, {==})
    case False{} True{}:
      n1.isf.us(Bool.and(saw, Bool.not(us)), T.NEDig{}, sg, base, ds, why, {==})
    case False{} False{}:
      {==}

# a step keeps a scan in a float or failed
def n1.isf.step(
  +st: T.Num,
  +cc: Char,
  hs: {n1.isf(st) == True{} : Bool}
) -> {n1.isf(T.num.step(st, cc)) == True{} : Bool}:
  match st:
    case T.Num{nk, +sg, +base, +ds, +us, +saw, +why}:
      match nk:
        case T.NFrac{}:
          n1.isf.frac(Char.is_digit(cc), Char.is_eq(cc, '_'), Char.is_eq(cc, 'e'), Char.is_eq(cc, 'E'), cc, sg, base,
            ds, us, saw, why)
        case T.NExp{}:
          n1.isf.expon(Char.is_eq(cc, '+'), Char.is_eq(cc, '-'), Char.is_digit(cc), cc, sg, base, ds, us, saw, why)
        case T.NEDig{}:
          n1.isf.edig(Char.is_digit(cc), Char.is_eq(cc, '_'), cc, sg, base, ds, us, saw, why)
        case T.NBad{}:
          {==}
        case T.NLead{}:
          Eq.bit.absurd(&2, {n1.isf(T.num.step(T.Num{T.NLead{}, sg, base, ds, us, saw, why}, cc)) == True{} : Bool}, hs)
        case T.NSign{}:
          Eq.bit.absurd(&2, {n1.isf(T.num.step(T.Num{T.NSign{}, sg, base, ds, us, saw, why}, cc)) == True{} : Bool}, hs)
        case T.NZero{}:
          Eq.bit.absurd(&2, {n1.isf(T.num.step(T.Num{T.NZero{}, sg, base, ds, us, saw, why}, cc)) == True{} : Bool}, hs)
        case T.NDig{}:
          Eq.bit.absurd(&2, {n1.isf(T.num.step(T.Num{T.NDig{}, sg, base, ds, us, saw, why}, cc)) == True{} : Bool}, hs)
        case T.NBase{}:
          Eq.bit.absurd(&2, {n1.isf(T.num.step(T.Num{T.NBase{}, sg, base, ds, us, saw, why}, cc)) == True{} : Bool}, hs)

# a scan in a float or failed never finishes as an integer
def n1.fcls(
  rest: List<&2, Char>,
  +st: T.Num,
  +sd: Bool,
  hs: {n1.isf(st) == True{} : Bool}
) -> {n1.ish(T.num.go(rest, st), sd) == False{} : Bool}:
  match rest:
    case []:
      match st:
        case T.Num{nk, _sign, _base, _ds, us, saw, _why}:
          match nk:
            case T.NFrac{}:
              {==}
            case T.NExp{}:
              {==}
            case T.NEDig{}:
              {==}
            case T.NBad{}:
              {==}
            case T.NLead{}:
              Eq.bit.absurd(&2, {n1.ish.nk(T.NLead{}, saw, us, sd) == False{} : Bool}, hs)
            case T.NSign{}:
              Eq.bit.absurd(&2, {n1.ish.nk(T.NSign{}, saw, us, sd) == False{} : Bool}, hs)
            case T.NZero{}:
              Eq.bit.absurd(&2, {n1.ish.nk(T.NZero{}, saw, us, sd) == False{} : Bool}, hs)
            case T.NDig{}:
              Eq.bit.absurd(&2, {n1.ish.nk(T.NDig{}, saw, us, sd) == False{} : Bool}, hs)
            case T.NBase{}:
              Eq.bit.absurd(&2, {n1.ish.nk(T.NBase{}, saw, us, sd) == False{} : Bool}, hs)
    case +hh <> tt:
      n1.fcls(tt, T.num.step(st, hh), sd, n1.isf.step(st, hh, hs))

# a failed scan holds no integer, whatever follows
def n1.ish.bad(
  rest: List<&2, Char>,
  +sd: Bool,
  +why: String
) -> {n1.ish(T.num.go(rest, T.Num{T.NBad{}, T.Plus{}, 10, [], False{}, False{}, why}), sd) == False{} : Bool}:
  n1.fcls(rest, T.Num{T.NBad{}, T.Plus{}, 10, [], False{}, False{}, why}, sd, {==})

# The decimal integer part. After a digit of it the scan finishes as an
# integer exactly when the rest is the repetition.

# after an underscore in an integer part, a character that is no digit fails
def n1.Dui.bad(
  uu: Bool,
  pp: Bool,
  e1: Bool,
  e2: Bool,
  +cc: Char,
  +tt: List<&2, Char>,
  +sg: T.Sign,
  +ds: List<&2, U32>,
  +why: String,
  +sd: Bool
) -> {n1.ish(T.num.go(tt, T.num.digs.go(False{}, uu, pp, e1, e2, T.Num{T.NDig{}, sg, 10, ds, True{}, True{}, why},
  cc)), sd) == False{} : Bool}:
  match uu:
    case True{}:
      n1.ish.bad(tt, sd, "invalid underscore")
    case False{}:
      match pp:
        case True{}:
          n1.ish.bad(tt, sd, "invalid fraction")
        case False{}:
          match e1:
            case True{}:
              n1.ish.bad(tt, sd, "invalid exponent")
            case False{}:
              match e2:
                case True{}:
                  n1.ish.bad(tt, sd, "invalid exponent")
                case False{}:
                  n1.ish.bad(tt, sd, "invalid number")

# what the integer-part lemma claims
def n1.Di.G(+rest: List<&2, Char>, +sg: T.Sign, +ds: List<&2, U32>, +why: String, +sd: Bool) -> Type:
  {n1.ish(T.num.go(rest, M7.n1.sd(sg, ds, why)), sd) == D1.abnf.dec_rep(rest) : Bool}

# the character after an underscore in an integer part
def n1.Dui.go(
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
  +sd: Bool,
  +ed: {Char.is_digit(cc) == dd : Bool},
  ih: n1.Di.G(tt, sg, T.dec.go(ds, 10, T.dig.val(cc)), "", sd)
) -> {n1.ish(T.num.go(tt, T.num.digs.go(dd, uu, pp, e1, e2, T.Num{T.NDig{}, sg, 10, ds, True{}, True{}, why}, cc)),
  sd) == D1.abnf.zero_prefixable_int(cc <> tt) : Bool}:
  match dd:
    case True{}:
      %M7.n1.zpi.d(cc, tt, ed) : {n1.ish(T.num.go(tt, T.num.digit.ok(T.dig.ok(T.dig.val(cc), 10), cc, T.NDig{}, sg, 10,
        ds)), sd) == _ : Bool}
      %Equal.sym(Bool, T.dig.ok(T.dig.val(cc), 10), True{}, M7.n1.dok10(cc, ed)) : {n1.ish(T.num.go(tt,
          T.num.digit.ok(_,
        cc, T.NDig{}, sg, 10, ds)), sd) == D1.abnf.dec_rep(tt) : Bool}
      ih
    case False{}:
      Equal.trans(Bool, n1.ish(T.num.go(tt, T.num.digs.go(False{}, uu, pp, e1, e2, T.Num{T.NDig{}, sg, 10, ds, True{},
        True{}, why}, cc)), sd), False{}, D1.abnf.zero_prefixable_int(cc <> tt), n1.Dui.bad(uu, pp, e1, e2, cc, tt,
        sg, ds, why, sd), M7.n1.zpi.n(cc, tt, ed))

# the type of n1.Di.go's ihu
def n1.Di.go.P1(+tt: List<&2, Char>, +sg: T.Sign, +ds: List<&2, U32>, +why: String, +sd: Bool) -> Type:
  {n1.ish(T.num.go(tt, T.Num{T.NDig{}, sg, 10, ds, True{}, True{}, why}),
    sd) == D1.abnf.zero_prefixable_int(tt) : Bool}

# the character after a digit of an integer part
def n1.Di.go(
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
  +sd: Bool,
  +ed: {Char.is_digit(cc) == dd : Bool},
  +eu: {Char.is_eq(cc, '_') == uu : Bool},
  _ep: {Char.is_eq(cc, '.') == pp : Bool},
  _ee1: {Char.is_eq(cc, 'e') == e1 : Bool},
  _ee2: {Char.is_eq(cc, 'E') == e2 : Bool},
  ihd: n1.Di.G(tt, sg, T.dec.go(ds, 10, T.dig.val(cc)), "", sd),
  ihu: n1.Di.go.P1(tt, sg, ds, why, sd)
) -> {n1.ish(T.num.go(tt, T.num.digs.go(dd, uu, pp, e1, e2, M7.n1.sd(sg, ds, why), cc)), sd)
  == D1.abnf.dec_rep(cc <> tt) : Bool}:
  match dd:
    case True{}:
      %M7.n1.rep.d(cc, tt, ed) : {n1.ish(T.num.go(tt, T.num.digit.ok(T.dig.ok(T.dig.val(cc), 10), cc, T.NDig{}, sg, 10,
        ds)), sd) == _ : Bool}
      %Equal.sym(Bool, T.dig.ok(T.dig.val(cc), 10), True{}, M7.n1.dok10(cc, ed)) : {n1.ish(T.num.go(tt,
          T.num.digit.ok(_,
        cc, T.NDig{}, sg, 10, ds)), sd) == D1.abnf.dec_rep(tt) : Bool}
      ihd
    case False{}:
      match uu:
        case True{}:
          %Equal.sym(Char, cc, '_', Eq.char_eq_true(cc, '_', eu)) : {n1.ish(T.num.go(tt, T.Num{T.NDig{}, sg, 10, ds,
            True{}, True{}, why}), sd) == D1.abnf.dec_rep(_ <> tt) : Bool}
          %M7.n1.rep.u(tt) : {n1.ish(T.num.go(tt, T.Num{T.NDig{}, sg, 10, ds, True{}, True{}, why}), sd) == _ : Bool}
          ihu
        case False{}:
          match pp:
            case True{}:
              %M7.n1.rep.n(cc, tt, ed, eu) : {n1.ish(T.num.go(tt, M7.n1.sf0(sg)), sd) == _ : Bool}
              n1.fcls(tt, M7.n1.sf0(sg), sd, {==})
            case False{}:
              match e1:
                case True{}:
                  %M7.n1.rep.n(cc, tt, ed, eu) : {n1.ish(T.num.go(tt, M7.n1.se(sg)), sd) == _ : Bool}
                  n1.fcls(tt, M7.n1.se(sg), sd, {==})
                case False{}:
                  match e2:
                    case True{}:
                      %M7.n1.rep.n(cc, tt, ed, eu) : {n1.ish(T.num.go(tt, M7.n1.se(sg)), sd) == _ : Bool}
                      n1.fcls(tt, M7.n1.se(sg), sd, {==})
                    case False{}:
                      %M7.n1.rep.n(cc, tt, ed, eu) : {n1.ish(T.num.go(tt, T.num.bad(M7.n1.sd(sg, ds, why),
                        "invalid number")), sd) == _ : Bool}
                      n1.ish.bad(tt, sd, "invalid number")

# after a digit of an integer part, the scan finishes as an integer exactly
# when the rest is the repetition
def n1.Di(
  rest: List<&2, Char>,
  +sg: T.Sign,
  +ds: List<&2, U32>,
  +why: String,
  +sd: Bool
) -> n1.Di.G(rest, sg, ds, why, sd):
  match rest:
    case []:
      {==}
    case +hh <> tt:
      match tt:
        case []:
          n1.Di.go(Char.is_digit(hh), Char.is_eq(hh, '_'), Char.is_eq(hh, '.'), Char.is_eq(hh, 'e'),
            Char.is_eq(hh, 'E'), hh, [], sg, ds, why, sd, {==}, {==}, {==}, {==}, {==},
            n1.Di([], sg, T.dec.go(ds, 10, T.dig.val(hh)), "", sd), {==})
        case +h2 <> +t2:
          n1.Di.go(Char.is_digit(hh), Char.is_eq(hh, '_'), Char.is_eq(hh, '.'), Char.is_eq(hh, 'e'),
            Char.is_eq(hh, 'E'), hh, h2 <> t2, sg, ds, why, sd, {==}, {==}, {==}, {==}, {==},
            n1.Di(h2 <> t2, sg, T.dec.go(ds, 10, T.dig.val(hh)), "", sd),
            n1.Dui.go(Char.is_digit(h2), Char.is_eq(h2, '_'), Char.is_eq(h2, '.'), Char.is_eq(h2, 'e'),
              Char.is_eq(h2, 'E'), h2, t2, sg, ds, why, sd, {==}, n1.Di(t2, sg, T.dec.go(ds, 10, T.dig.val(h2)), "",
              sd)))

# The prefixed integer. After its prefix, and after each digit, the scan
# finishes as an integer exactly when the rest is the radix's repetition and
# no sign came before the prefix.

# a digit of the radix and then the repetition
def n1.bg(tt: List<&2, Char>, +rx: D1.ARadix) -> Bool:
  match tt:
    case []:
      False{}
    case h2 <> t2:
      Bool.and(D1.abnf.radix_digit(rx, h2), D1.abnf.radix_rep(t2, rx))

# no radix has the underscore as a digit
def n1.rd.us(rx: D1.ARadix) -> {D1.abnf.radix_digit(rx, '_') == False{} : Bool}:
  match rx:
    case D1.AHex{}:
      {==}
    case D1.AOct{}:
      {==}
    case D1.ABin{}:
      {==}

# a radix's digit is no underscore
def n1.rd.nus(
  uu: Bool,
  +rx: D1.ARadix,
  +cc: Char,
  eu: {Char.is_eq(cc, '_') == uu : Bool},
  hd: {D1.abnf.radix_digit(rx, cc) == True{} : Bool}
) -> {False{} == D1.abnf.underscore(cc) : Bool}:
  match uu:
    case True{}:
      Eq.bit.absurd2(&2, {False{} == D1.abnf.underscore(cc) : Bool}, Equal.trans(Bool, True{},
        D1.abnf.radix_digit(rx, cc), False{}, Equal.sym(Bool, D1.abnf.radix_digit(rx, cc), True{}, hd),
        Equal.trans(Bool, D1.abnf.radix_digit(rx, cc), D1.abnf.radix_digit(rx, '_'), False{}, Equal.cong(Char,
        Bool, xx => D1.abnf.radix_digit(rx, xx), cc, '_', Eq.char_eq_true(cc, '_', eu)), n1.rd.us(rx))))
    case False{}:
      Equal.trans(Bool, False{}, Char.is_eq(cc, '_'), D1.abnf.underscore(cc), Equal.sym(Bool, Char.is_eq(cc, '_'),
        False{}, eu), M7.n1.us(cc))

# the repetition after a radix's digit is the repetition
def n1.rrep.d(
  +rx: D1.ARadix,
  +cc: Char,
  tt: List<&2, Char>,
  +hd: {D1.abnf.radix_digit(rx, cc) == True{} : Bool}
) -> {D1.abnf.radix_rep(tt, rx) == D1.abnf.radix_rep(cc <> tt, rx) : Bool}:
  match tt:
    case []:
      Equal.sym(Bool, D1.abnf.radix_digit(rx, cc), True{}, hd)
    case +h2 <> +t2:
      %Equal.sym(Bool, D1.abnf.radix_digit(rx, cc), True{}, hd) : {D1.abnf.radix_rep(h2 <> t2, rx) == Bool.or(
        Bool.and(_, D1.abnf.radix_rep(h2 <> t2, rx)), Bool.and(D1.abnf.underscore(cc),
        Bool.and(D1.abnf.radix_digit(rx, h2), D1.abnf.radix_rep(t2, rx)))) : Bool}
      %n1.rd.nus(Char.is_eq(cc, '_'), rx, cc, {==}, hd) : {D1.abnf.radix_rep(h2 <> t2, rx) == Bool.or(
        D1.abnf.radix_rep(h2 <> t2, rx), Bool.and(_, Bool.and(D1.abnf.radix_digit(rx, h2), D1.abnf.radix_rep(t2,
        rx)))) : Bool}
      M7.n1.orf.eq(D1.abnf.radix_rep(h2 <> t2, rx), D1.abnf.radix_rep(h2 <> t2, rx), {==})

# the repetition after an underscore is a radix's digit and the repetition
def n1.rrep.u(+rx: D1.ARadix, tt: List<&2, Char>) -> {n1.bg(tt, rx) == D1.abnf.radix_rep('_' <> tt, rx) : Bool}:
  match tt:
    case []:
      Equal.sym(Bool, D1.abnf.radix_digit(rx, '_'), False{}, n1.rd.us(rx))
    case +h2 <> +t2:
      %Equal.sym(Bool, D1.abnf.radix_digit(rx, '_'), False{}, n1.rd.us(rx)) : {n1.bg(h2 <> t2, rx) == Bool.or(
        Bool.and(_, D1.abnf.radix_rep(h2 <> t2, rx)), Bool.and(True{}, Bool.and(D1.abnf.radix_digit(rx, h2),
        D1.abnf.radix_rep(t2, rx)))) : Bool}
      {==}

# no repetition starts with a character that is no radix digit and no
# underscore
def n1.rrep.n(
  +rx: D1.ARadix,
  +cc: Char,
  tt: List<&2, Char>,
  +hd: {D1.abnf.radix_digit(rx, cc) == False{} : Bool},
  +hu: {Char.is_eq(cc, '_') == False{} : Bool}
) -> {False{} == D1.abnf.radix_rep(cc <> tt, rx) : Bool}:
  match tt:
    case []:
      Equal.sym(Bool, D1.abnf.radix_digit(rx, cc), False{}, hd)
    case +h2 <> +t2:
      %Equal.sym(Bool, D1.abnf.radix_digit(rx, cc), False{}, hd) : {False{} == Bool.or(Bool.and(_,
        D1.abnf.radix_rep(h2 <> t2, rx)), Bool.and(D1.abnf.underscore(cc), Bool.and(D1.abnf.radix_digit(rx, h2),
        D1.abnf.radix_rep(t2, rx)))) : Bool}
      %Equal.trans(Bool, False{}, Char.is_eq(cc, '_'), D1.abnf.underscore(cc), Equal.sym(Bool, Char.is_eq(cc, '_'),
        False{}, hu), M7.n1.us(cc)) : {False{} == Bool.or(False{}, Bool.and(_, Bool.and(D1.abnf.radix_digit(rx, h2),
        D1.abnf.radix_rep(t2, rx)))) : Bool}
      {==}

# the scan after a digit of a prefixed integer
def n1.sb(+sg: T.Sign, +rx: D1.ARadix, +ds: List<&2, U32>) -> T.Num:
  T.Num{T.NBase{}, sg, n1.rb(rx), ds, False{}, True{}, ""}

# what the prefixed-digit lemma claims
def n1.Bi.G(+rest: List<&2, Char>, +sg: T.Sign, +rx: D1.ARadix, +ds: List<&2, U32>, +sd: Bool) -> Type:
  {n1.ish(T.num.go(rest, n1.sb(sg, rx, ds)), sd) == Bool.and(Bool.not(sd), D1.abnf.radix_rep(rest, rx)) : Bool}

# a digit of the radix is one dig.ok takes
def n1.cls.t(
  +rx: D1.ARadix,
  +cc: Char,
  eo: {T.dig.ok(T.dig.val(cc), n1.rb(rx)) == True{} : Bool}
) -> {D1.abnf.radix_digit(rx, cc) == True{} : Bool}:
  Equal.trans(Bool, D1.abnf.radix_digit(rx, cc), T.dig.ok(T.dig.val(cc), n1.rb(rx)), True{}, Equal.sym(Bool,
    T.dig.ok(T.dig.val(cc), n1.rb(rx)), D1.abnf.radix_digit(rx, cc), n1.cls(rx, cc)), eo)

# and no other character is
def n1.cls.f(
  +rx: D1.ARadix,
  +cc: Char,
  eo: {T.dig.ok(T.dig.val(cc), n1.rb(rx)) == False{} : Bool}
) -> {D1.abnf.radix_digit(rx, cc) == False{} : Bool}:
  Equal.trans(Bool, D1.abnf.radix_digit(rx, cc), T.dig.ok(T.dig.val(cc), n1.rb(rx)), False{}, Equal.sym(Bool,
    T.dig.ok(T.dig.val(cc), n1.rb(rx)), D1.abnf.radix_digit(rx, cc), n1.cls(rx, cc)), eo)

# a prefixed integer's state where an underscore fails (after an underscore,
# or before the first digit), with a character: a digit goes on, anything
# else fails
def n1.Bui.go(
  uu: Bool,
  ok: Bool,
  +cc: Char,
  +tt: List<&2, Char>,
  +sg: T.Sign,
  +rx: D1.ARadix,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String,
  +sd: Bool,
  +eu: {Char.is_eq(cc, '_') == uu : Bool},
  +eo: {T.dig.ok(T.dig.val(cc), n1.rb(rx)) == ok : Bool},
  hq: {Bool.and(saw, Bool.not(us)) == False{} : Bool},
  ih: n1.Bi.G(tt, sg, rx, T.dec.go(ds, n1.rb(rx), T.dig.val(cc)), sd)
) -> {n1.ish(T.num.go(tt, T.num.based.go(uu, T.Num{T.NBase{}, sg, n1.rb(rx), ds, us, saw, why}, cc)), sd)
  == Bool.and(Bool.not(sd), n1.bg(cc <> tt, rx)) : Bool}:
  match uu:
    case True{}:
      %Equal.sym(Char, cc, '_', Eq.char_eq_true(cc, '_', eu)) : {n1.ish(T.num.go(tt, T.num.us.go(Bool.and(saw,
        Bool.not(us)), T.NBase{}, sg, n1.rb(rx), ds, why)), sd) == Bool.and(Bool.not(sd), n1.bg(_ <> tt, rx)) : Bool}
      %Equal.sym(Bool, Bool.and(saw, Bool.not(us)), False{}, hq) : {n1.ish(T.num.go(tt, T.num.us.go(_, T.NBase{}, sg,
        n1.rb(rx), ds, why)), sd) == Bool.and(Bool.not(sd), n1.bg('_' <> tt, rx)) : Bool}
      %Equal.sym(Bool, D1.abnf.radix_digit(rx, '_'), False{}, n1.rd.us(rx)) : {n1.ish(T.num.go(tt,
        T.num.bad(T.Num{T.NLead{}, T.Plus{}, 10, [], False{}, False{}, ""}, "invalid underscore")), sd)
        == Bool.and(Bool.not(sd), Bool.and(_, D1.abnf.radix_rep(tt, rx))) : Bool}
      %Equal.sym(Bool, Bool.and(Bool.not(sd), False{}), False{}, M4.gs.andf(Bool.not(sd))) : {n1.ish(T.num.go(tt,
        T.num.bad(T.Num{T.NLead{}, T.Plus{}, 10, [], False{}, False{}, ""},
        "invalid underscore")), sd) == _ : Bool}
      n1.ish.bad(tt, sd, "invalid underscore")
    case False{}:
      match ok:
        case True{}:
          %Equal.sym(Bool, T.dig.ok(T.dig.val(cc), n1.rb(rx)), True{}, eo) : {n1.ish(T.num.go(tt, T.num.digit.ok(_, cc,
            T.NBase{}, sg, n1.rb(rx), ds)), sd) == Bool.and(Bool.not(sd), n1.bg(cc <> tt, rx)) : Bool}
          %Equal.sym(Bool, D1.abnf.radix_digit(rx, cc), True{}, n1.cls.t(rx, cc, eo)) : {n1.ish(T.num.go(tt,
            n1.sb(sg, rx, T.dec.go(ds, n1.rb(rx), T.dig.val(cc)))), sd) == Bool.and(Bool.not(sd), Bool.and(_,
            D1.abnf.radix_rep(tt, rx))) : Bool}
          ih
        case False{}:
          %Equal.sym(Bool, T.dig.ok(T.dig.val(cc), n1.rb(rx)), False{}, eo) : {n1.ish(T.num.go(tt, T.num.digit.ok(_,
            cc, T.NBase{}, sg, n1.rb(rx), ds)), sd) == Bool.and(Bool.not(sd), n1.bg(cc <> tt, rx)) : Bool}
          %Equal.sym(Bool, D1.abnf.radix_digit(rx, cc), False{}, n1.cls.f(rx, cc, eo)) : {n1.ish(T.num.go(tt,
            T.num.bad(T.Num{T.NLead{}, T.Plus{}, 10, [], False{}, False{}, ""}, "invalid digit")), sd)
            == Bool.and(Bool.not(sd), Bool.and(_, D1.abnf.radix_rep(tt, rx))) : Bool}
          %Equal.sym(Bool, Bool.and(Bool.not(sd), False{}), False{}, M4.gs.andf(Bool.not(sd))) : {n1.ish(T.num.go(tt,
            T.num.bad(T.Num{T.NLead{}, T.Plus{}, 10, [], False{},
            False{}, ""}, "invalid digit")), sd) == _ : Bool}
          n1.ish.bad(tt, sd, "invalid digit")

# a prefixed integer's state where an underscore fails, with a character and
# the rest
def n1.Bui(
  +cc: Char,
  +tt: List<&2, Char>,
  +sg: T.Sign,
  +rx: D1.ARadix,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String,
  +sd: Bool,
  hq: {Bool.and(saw, Bool.not(us)) == False{} : Bool},
  ih: n1.Bi.G(tt, sg, rx, T.dec.go(ds, n1.rb(rx), T.dig.val(cc)), sd)
) -> {n1.ish(T.num.go(cc <> tt, T.Num{T.NBase{}, sg, n1.rb(rx), ds, us, saw, why}), sd)
  == Bool.and(Bool.not(sd), n1.bg(cc <> tt, rx)) : Bool}:
  n1.Bui.go(Char.is_eq(cc, '_'), T.dig.ok(T.dig.val(cc), n1.rb(rx)), cc, tt, sg, rx, ds, us, saw, why, sd, {==}, {==},
    hq, ih)

# the type of n1.Bi.go's ihu
def n1.Bi.go.P1(+tt: List<&2, Char>, +sg: T.Sign, +rx: D1.ARadix, +ds: List<&2, U32>, +sd: Bool) -> Type:
  {n1.ish(T.num.go(tt, T.Num{T.NBase{}, sg, n1.rb(rx), ds, True{}, True{}, ""}), sd) == Bool.and(Bool.not(sd),
    n1.bg(tt, rx)) : Bool}

# the character after a digit of a prefixed integer
def n1.Bi.go(
  uu: Bool,
  ok: Bool,
  +cc: Char,
  +tt: List<&2, Char>,
  +sg: T.Sign,
  +rx: D1.ARadix,
  +ds: List<&2, U32>,
  +sd: Bool,
  +eu: {Char.is_eq(cc, '_') == uu : Bool},
  +eo: {T.dig.ok(T.dig.val(cc), n1.rb(rx)) == ok : Bool},
  ihd: n1.Bi.G(tt, sg, rx, T.dec.go(ds, n1.rb(rx), T.dig.val(cc)), sd),
  ihu: n1.Bi.go.P1(tt, sg, rx, ds, sd)
) -> {n1.ish(T.num.go(tt, T.num.based.go(uu, n1.sb(sg, rx, ds), cc)), sd)
  == Bool.and(Bool.not(sd), D1.abnf.radix_rep(cc <> tt, rx)) : Bool}:
  match uu:
    case True{}:
      %Equal.sym(Char, cc, '_', Eq.char_eq_true(cc, '_', eu)) : {n1.ish(T.num.go(tt, T.Num{T.NBase{}, sg, n1.rb(rx),
        ds, True{}, True{}, ""}), sd) == Bool.and(Bool.not(sd), D1.abnf.radix_rep(_ <> tt, rx)) : Bool}
      %n1.rrep.u(rx, tt) : {n1.ish(T.num.go(tt, T.Num{T.NBase{}, sg, n1.rb(rx), ds, True{}, True{}, ""}), sd)
        == Bool.and(Bool.not(sd), _) : Bool}
      ihu
    case False{}:
      match ok:
        case True{}:
          %Equal.sym(Bool, T.dig.ok(T.dig.val(cc), n1.rb(rx)), True{}, eo) : {n1.ish(T.num.go(tt, T.num.digit.ok(_, cc,
            T.NBase{}, sg, n1.rb(rx), ds)), sd) == Bool.and(Bool.not(sd), D1.abnf.radix_rep(cc <> tt, rx)) : Bool}
          %n1.rrep.d(rx, cc, tt, n1.cls.t(rx, cc, eo)) : {n1.ish(T.num.go(tt, n1.sb(sg, rx, T.dec.go(ds, n1.rb(rx),
            T.dig.val(cc)))), sd) == Bool.and(Bool.not(sd), _) : Bool}
          ihd
        case False{}:
          %Equal.sym(Bool, T.dig.ok(T.dig.val(cc), n1.rb(rx)), False{}, eo) : {n1.ish(T.num.go(tt, T.num.digit.ok(_,
            cc, T.NBase{}, sg, n1.rb(rx), ds)), sd) == Bool.and(Bool.not(sd), D1.abnf.radix_rep(cc <> tt, rx)) : Bool}
          %n1.rrep.n(rx, cc, tt, n1.cls.f(rx, cc, eo), eu) : {n1.ish(T.num.go(tt, T.num.bad(T.Num{T.NLead{}, T.Plus{},
            10, [], False{}, False{}, ""}, "invalid digit")), sd) == Bool.and(Bool.not(sd), _) : Bool}
          %Equal.sym(Bool, Bool.and(Bool.not(sd), False{}), False{}, M4.gs.andf(Bool.not(sd))) : {n1.ish(T.num.go(tt,
            T.num.bad(T.Num{T.NLead{}, T.Plus{}, 10, [], False{}, False{},
            ""}, "invalid digit")), sd) == _ : Bool}
          n1.ish.bad(tt, sd, "invalid digit")

# after a digit of a prefixed integer, the scan finishes as an integer
# exactly when the rest is the radix's repetition and no sign came first
def n1.Bi(
  rest: List<&2, Char>,
  +sg: T.Sign,
  +rx: D1.ARadix,
  +ds: List<&2, U32>,
  +sd: Bool
) -> n1.Bi.G(rest, sg, rx, ds, sd):
  match rest:
    case []:
      match sd:
        case True{}:
          {==}
        case False{}:
          {==}
    case +hh <> tt:
      match tt:
        case []:
          n1.Bi.go(Char.is_eq(hh, '_'), T.dig.ok(T.dig.val(hh), n1.rb(rx)), hh, [], sg, rx, ds, sd, {==}, {==},
            n1.Bi([], sg, rx, T.dec.go(ds, n1.rb(rx), T.dig.val(hh)), sd), Equal.sym(Bool, Bool.and(Bool.not(sd),
            False{}), False{}, M4.gs.andf(Bool.not(sd))))
        case +h2 <> +t2:
          n1.Bi.go(Char.is_eq(hh, '_'), T.dig.ok(T.dig.val(hh), n1.rb(rx)), hh, h2 <> t2, sg, rx, ds, sd, {==}, {==},
            n1.Bi(h2 <> t2, sg, rx, T.dec.go(ds, n1.rb(rx), T.dig.val(hh)), sd),
            n1.Bui(h2, t2, sg, rx, ds, True{}, True{}, "", sd, {==}, n1.Bi(t2, sg, rx, T.dec.go(ds, n1.rb(rx),
              T.dig.val(h2)), sd)))

# after a prefix, the scan finishes as an integer exactly when a digit of the
# radix and the repetition follow and no sign came first
def n1.B0(
  rest: List<&2, Char>,
  +sg: T.Sign,
  +rx: D1.ARadix,
  +sd: Bool
) -> {n1.ish(T.num.go(rest, T.Num{T.NBase{}, sg, n1.rb(rx), [], False{}, False{}, ""}), sd)
  == Bool.and(Bool.not(sd), n1.bg(rest, rx)) : Bool}:
  match rest:
    case []:
      Equal.sym(Bool, Bool.and(Bool.not(sd), False{}), False{}, M4.gs.andf(Bool.not(sd)))
    case +hh <> +tt:
      n1.Bui(hh, tt, sg, rx, [], False{}, False{}, "", sd, {==}, n1.Bi(tt, sg, rx, T.dec.go([], n1.rb(rx),
        T.dig.val(hh)), sd))

# The leading zero, the sign and the start, for integers.

# the prefixed integers a word 0 and the rest can be
def n1.pfx(+rest: List<&2, Char>) -> Bool:
  Bool.or(D1.abnf.hex_int('0' <> rest), Bool.or(D1.abnf.oct_int('0' <> rest), D1.abnf.bin_int('0' <> rest)))

# 0x and the rest is a hex-int exactly when a hex digit and the repetition
# follow
def n1.pfx.x(tt: List<&2, Char>) -> {n1.bg(tt, D1.AHex{}) == n1.pfx('x' <> tt) : Bool}:
  match tt:
    case []:
      {==}
    case +c2 <> +rr:
      M7.n1.orf.eq(n1.bg(c2 <> rr, D1.AHex{}), n1.bg(c2 <> rr, D1.AHex{}), {==})

# 0o and the rest is an oct-int exactly when an octal digit and the
# repetition follow
def n1.pfx.o(tt: List<&2, Char>) -> {n1.bg(tt, D1.AOct{}) == n1.pfx('o' <> tt) : Bool}:
  match tt:
    case []:
      {==}
    case +c2 <> +rr:
      M7.n1.orf.eq(n1.bg(c2 <> rr, D1.AOct{}), n1.bg(c2 <> rr, D1.AOct{}), {==})

# 0b and the rest is a bin-int exactly when a binary digit and the
# repetition follow
def n1.pfx.b(tt: List<&2, Char>) -> {n1.bg(tt, D1.ABin{}) == n1.pfx('b' <> tt) : Bool}:
  match tt:
    case []:
      {==}
    case _c <> _r:
      {==}

# a character's test against the code point nn, as the grammar and the code
# write it
def n1.cp(+cc: Char, +nn: U32) -> {Char.is_eq(cc, Chr{nn}) == D1.abnf.cp(cc, nn) : Bool}:
  match cc:
    case Chr{+cp}:
      {==}

# 0 and a character that is no x, o or b starts no prefixed integer
def n1.pfx.n(
  +cc: Char,
  tt: List<&2, Char>,
  +hx: {Char.is_eq(cc, 'x') == False{} : Bool},
  +ho: {Char.is_eq(cc, 'o') == False{} : Bool},
  +hb: {Char.is_eq(cc, 'b') == False{} : Bool}
) -> {False{} == n1.pfx(cc <> tt) : Bool}:
  match tt:
    case []:
      {==}
    case +c2 <> +rr:
      %Equal.trans(Bool, False{}, Char.is_eq(cc, 'x'), D1.abnf.cp(cc, 120), Equal.sym(Bool, Char.is_eq(cc, 'x'),
        False{}, hx), n1.cp(cc, 120)) : {False{} == Bool.or(Bool.and(True{}, Bool.and(_,
        Bool.and(D1.abnf.HEXDIG(c2), D1.abnf.radix_rep(rr, D1.AHex{})))), Bool.or(D1.abnf.oct_int('0' <> cc <>
        c2 <> rr), D1.abnf.bin_int('0' <> cc <> c2 <> rr))) : Bool}
      %Equal.trans(Bool, False{}, Char.is_eq(cc, 'o'), D1.abnf.cp(cc, 111), Equal.sym(Bool, Char.is_eq(cc, 'o'),
        False{}, ho), n1.cp(cc, 111)) : {False{} == Bool.or(False{}, Bool.or(Bool.and(True{}, Bool.and(_,
        Bool.and(D1.abnf.digit0_7(c2), D1.abnf.radix_rep(rr, D1.AOct{})))), D1.abnf.bin_int('0' <> cc <> c2 <>
        rr))) : Bool}
      %Equal.trans(Bool, False{}, Char.is_eq(cc, 'b'), D1.abnf.cp(cc, 98), Equal.sym(Bool, Char.is_eq(cc, 'b'),
        False{}, hb), n1.cp(cc, 98)) : {False{} == Bool.or(False{}, Bool.or(False{}, Bool.and(True{}, Bool.and(_,
        Bool.and(D1.abnf.digit0_1(c2), D1.abnf.radix_rep(rr, D1.ABin{})))))) : Bool}
      {==}

# what the leading zero lemma claims for integers
def n1.Zi.G(+rest: List<&2, Char>, +sg: T.Sign, +sd: Bool) -> Type:
  {n1.ish(T.num.go(rest, M7.n1.sz(sg)), sd) == Bool.or(D1.abnf.unsigned_dec_int('0' <> rest), Bool.and(Bool.not(sd),
    n1.pfx(rest))) : Bool}

# after a leading zero, a character that starts no prefix holds no integer
def n1.Zi.no(
  +cc: Char,
  +tt: List<&2, Char>,
  +st: T.Num,
  +sd: Bool,
  hl: {n1.ish(T.num.go(tt, st), sd) == False{} : Bool},
  +hx: {Char.is_eq(cc, 'x') == False{} : Bool},
  +ho: {Char.is_eq(cc, 'o') == False{} : Bool},
  +hb: {Char.is_eq(cc, 'b') == False{} : Bool}
) -> {n1.ish(T.num.go(tt, st), sd) == Bool.or(D1.abnf.unsigned_dec_int('0' <> cc <> tt), Bool.and(Bool.not(sd),
  n1.pfx(cc <> tt))) : Bool}:
  %n1.pfx.n(cc, tt, hx, ho, hb) : {n1.ish(T.num.go(tt, st), sd) == Bool.or(False{}, Bool.and(Bool.not(sd), _)) : Bool}
  %Equal.sym(Bool, Bool.and(Bool.not(sd), False{}), False{}, M4.gs.andf(Bool.not(sd))) : {n1.ish(T.num.go(tt, st), sd)
    == Bool.or(False{}, _) : Bool}
  hl

# the type of n1.Zi.go's ihx
def n1.Zi.go.P1(+tt: List<&2, Char>, +sg: T.Sign, +sd: Bool) -> Type:
  {n1.ish(T.num.go(tt, T.Num{T.NBase{}, sg, 16, [], False{}, False{}, ""}), sd) == Bool.and(Bool.not(sd), n1.bg(tt,
    D1.AHex{})) : Bool}

# the type of n1.Zi.go's iho
def n1.Zi.go.P2(+tt: List<&2, Char>, +sg: T.Sign, +sd: Bool) -> Type:
  {n1.ish(T.num.go(tt, T.Num{T.NBase{}, sg, 8, [], False{}, False{}, ""}), sd) == Bool.and(Bool.not(sd), n1.bg(tt,
    D1.AOct{})) : Bool}

# the type of n1.Zi.go's ihb
def n1.Zi.go.P3(+tt: List<&2, Char>, +sg: T.Sign, +sd: Bool) -> Type:
  {n1.ish(T.num.go(tt, T.Num{T.NBase{}, sg, 2, [], False{}, False{}, ""}), sd) == Bool.and(Bool.not(sd), n1.bg(tt,
    D1.ABin{})) : Bool}

# the character after a leading zero, for integers
def n1.Zi.go(
  xx: Bool,
  oo: Bool,
  bb: Bool,
  pp: Bool,
  e1: Bool,
  e2: Bool,
  +cc: Char,
  +tt: List<&2, Char>,
  +sg: T.Sign,
  +sd: Bool,
  +exx: {Char.is_eq(cc, 'x') == xx : Bool},
  +eoo: {Char.is_eq(cc, 'o') == oo : Bool},
  +ebb: {Char.is_eq(cc, 'b') == bb : Bool},
  ihx: n1.Zi.go.P1(tt, sg, sd),
  iho: n1.Zi.go.P2(tt, sg, sd),
  ihb: n1.Zi.go.P3(tt, sg, sd)
) -> {n1.ish(T.num.go(tt, T.num.zero.go(xx, oo, bb, pp, e1, e2, M7.n1.sz(sg), cc)), sd) == Bool.or(
  D1.abnf.unsigned_dec_int('0' <> cc <> tt), Bool.and(Bool.not(sd), n1.pfx(cc <> tt))) : Bool}:
  match xx:
    case True{}:
      %Equal.sym(Char, cc, 'x', Eq.char_eq_true(cc, 'x', exx)) : {n1.ish(T.num.go(tt, T.num.base(M7.n1.sz(sg), 16)), sd)
        == Bool.or(D1.abnf.unsigned_dec_int('0' <> _ <> tt), Bool.and(Bool.not(sd), n1.pfx(_ <> tt))) : Bool}
      %n1.pfx.x(tt) : {n1.ish(T.num.go(tt, T.num.base(M7.n1.sz(sg), 16)), sd) == Bool.and(Bool.not(sd), _) : Bool}
      ihx
    case False{}:
      match oo:
        case True{}:
          %Equal.sym(Char, cc, 'o', Eq.char_eq_true(cc, 'o', eoo)) : {n1.ish(T.num.go(tt, T.num.base(M7.n1.sz(sg), 8)),
              sd)
            == Bool.or(D1.abnf.unsigned_dec_int('0' <> _ <> tt), Bool.and(Bool.not(sd), n1.pfx(_ <> tt))) : Bool}
          %n1.pfx.o(tt) : {n1.ish(T.num.go(tt, T.num.base(M7.n1.sz(sg), 8)), sd) == Bool.and(Bool.not(sd), _) : Bool}
          iho
        case False{}:
          match bb:
            case True{}:
              %Equal.sym(Char, cc, 'b', Eq.char_eq_true(cc, 'b', ebb)) : {n1.ish(T.num.go(tt, T.num.base(M7.n1.sz(sg),
                  2)),
                sd) == Bool.or(D1.abnf.unsigned_dec_int('0' <> _ <> tt), Bool.and(Bool.not(sd), n1.pfx(_ <> tt)))
                : Bool}
              %n1.pfx.b(tt) : {n1.ish(T.num.go(tt, T.num.base(M7.n1.sz(sg), 2)), sd) == Bool.and(Bool.not(sd),
                  _) : Bool}
              ihb
            case False{}:
              match pp:
                case True{}:
                  n1.Zi.no(cc, tt, M7.n1.sf0(sg), sd, n1.fcls(tt, M7.n1.sf0(sg), sd, {==}), exx, eoo, ebb)
                case False{}:
                  match e1:
                    case True{}:
                      n1.Zi.no(cc, tt, M7.n1.se(sg), sd, n1.fcls(tt, M7.n1.se(sg), sd, {==}), exx, eoo, ebb)
                    case False{}:
                      match e2:
                        case True{}:
                          n1.Zi.no(cc, tt, M7.n1.se(sg), sd, n1.fcls(tt, M7.n1.se(sg), sd, {==}), exx, eoo, ebb)
                        case False{}:
                          n1.Zi.no(cc, tt, T.num.bad(M7.n1.sz(sg), "invalid number"), sd, n1.ish.bad(tt, sd,
                            "invalid number"), exx, eoo, ebb)

# after a leading zero, the scan finishes as an integer exactly when nothing
# follows, or a prefix and its digits follow and no sign came first
def n1.Zi(rest: List<&2, Char>, +sg: T.Sign, +sd: Bool) -> n1.Zi.G(rest, sg, sd):
  match rest:
    case []:
      {==}
    case +hh <> +tt:
      n1.Zi.go(Char.is_eq(hh, 'x'), Char.is_eq(hh, 'o'), Char.is_eq(hh, 'b'), Char.is_eq(hh, '.'), Char.is_eq(hh, 'e'),
        Char.is_eq(hh, 'E'), hh, tt, sg, sd, {==}, {==}, {==}, n1.B0(tt, sg, D1.AHex{}, sd),
        n1.B0(tt, sg, D1.AOct{}, sd), n1.B0(tt, sg, D1.ABin{}, sd))

# the first character of an unsigned numeral after a sign, for integers
def n1.Si2.go(
  zz: Bool,
  dd: Bool,
  +cc: Char,
  +tt: List<&2, Char>,
  +sg: T.Sign,
  +ez: {Char.is_eq(cc, '0') == zz : Bool},
  +ed: {Char.is_digit(cc) == dd : Bool},
  ihz: n1.Zi.G(tt, sg, True{}),
  ihd: n1.Di.G(tt, sg, T.dec.go([], 10, T.dig.val(cc)), "", True{})
) -> {n1.ish(T.num.go(tt, T.num.lead.go(False{}, False{}, zz, dd, M7.n1.sl(sg), cc)), True{})
  == D1.abnf.unsigned_dec_int(cc <> tt) : Bool}:
  match zz:
    case True{}:
      %Equal.sym(Char, cc, '0', Eq.char_eq_true(cc, '0', ez)) : {n1.ish(T.num.go(tt, M7.n1.sz(sg)), True{})
        == D1.abnf.unsigned_dec_int(_ <> tt) : Bool}
      Equal.trans(Bool, n1.ish(T.num.go(tt, M7.n1.sz(sg)), True{}), Bool.or(D1.abnf.unsigned_dec_int('0' <> tt),
        False{}), D1.abnf.unsigned_dec_int('0' <> tt), ihz, M7.n1.orf(D1.abnf.unsigned_dec_int('0' <> tt)))
    case False{}:
      match dd:
        case True{}:
          %M7.n1.udi.d(cc, tt, M7.n1.d19.y(cc, ed, ez)) : {n1.ish(T.num.go(tt, T.num.digit.ok(T.dig.ok(T.dig.val(cc),
              10),
            cc, T.NDig{}, sg, 10, [])), True{}) == _ : Bool}
          %Equal.sym(Bool, T.dig.ok(T.dig.val(cc), 10), True{}, M7.n1.dok10(cc, ed)) : {n1.ish(T.num.go(tt,
            T.num.digit.ok(_, cc, T.NDig{}, sg, 10, [])), True{}) == D1.abnf.dec_rep(tt) : Bool}
          ihd
        case False{}:
          %M7.n1.udi.n(cc, tt, ed) : {n1.ish(T.num.go(tt, T.num.bad(M7.n1.sl(sg), "invalid number")),
              True{}) == _ : Bool}
          n1.ish.bad(tt, True{}, "invalid number")

# the character after a sign, for integers: a second sign fails
def n1.Si.go(
  pp: Bool,
  mm: Bool,
  +cc: Char,
  +tt: List<&2, Char>,
  +sg: T.Sign,
  +ep: {Char.is_eq(cc, '+') == pp : Bool},
  +em: {Char.is_eq(cc, '-') == mm : Bool},
  ihz: n1.Zi.G(tt, sg, True{}),
  ihd: n1.Di.G(tt, sg, T.dec.go([], 10, T.dig.val(cc)), "", True{})
) -> {n1.ish(T.num.go(tt, T.num.after.sign.go(Bool.or(pp, mm), sg, cc)), True{})
  == D1.abnf.unsigned_dec_int(cc <> tt) : Bool}:
  match pp:
    case True{}:
      %Equal.sym(Char, cc, '+', Eq.char_eq_true(cc, '+', ep)) : {n1.ish(T.num.go(tt, T.num.bad(T.num.start(),
        "invalid number")), True{}) == D1.abnf.unsigned_dec_int(_ <> tt) : Bool}
      %M7.n1.udi.n('+', tt, {==}) : {n1.ish(T.num.go(tt, T.num.bad(T.num.start(), "invalid number")),
          True{}) == _ : Bool}
      n1.ish.bad(tt, True{}, "invalid number")
    case False{}:
      match mm:
        case True{}:
          %Equal.sym(Char, cc, '-', Eq.char_eq_true(cc, '-', em)) : {n1.ish(T.num.go(tt, T.num.bad(T.num.start(),
            "invalid number")), True{}) == D1.abnf.unsigned_dec_int(_ <> tt) : Bool}
          %M7.n1.udi.n('-', tt, {==}) : {n1.ish(T.num.go(tt, T.num.bad(T.num.start(), "invalid number")), True{}) == _
            : Bool}
          n1.ish.bad(tt, True{}, "invalid number")
        case False{}:
          %Equal.sym(Bool, Char.is_eq(cc, '+'), False{}, ep) : {n1.ish(T.num.go(tt, T.num.lead.go(_,
            Char.is_eq(cc, '-'), Char.is_eq(cc, '0'), Char.is_digit(cc), M7.n1.sl(sg), cc)), True{})
            == D1.abnf.unsigned_dec_int(cc <> tt) : Bool}
          %Equal.sym(Bool, Char.is_eq(cc, '-'), False{}, em) : {n1.ish(T.num.go(tt, T.num.lead.go(False{}, _,
            Char.is_eq(cc, '0'), Char.is_digit(cc), M7.n1.sl(sg), cc)), True{}) == D1.abnf.unsigned_dec_int(cc <> tt)
            : Bool}
          n1.Si2.go(Char.is_eq(cc, '0'), Char.is_digit(cc), cc, tt, sg, {==}, {==}, ihz, ihd)

# after a sign, the scan finishes as an integer exactly when the rest is an
# unsigned-dec-int
def n1.Si(
  rest: List<&2, Char>,
  +sg: T.Sign
) -> {n1.ish(T.num.go(rest, M7.n1.ss(sg)), True{}) == D1.abnf.unsigned_dec_int(rest) : Bool}:
  match rest:
    case []:
      {==}
    case +hh <> +tt:
      n1.Si.go(Char.is_eq(hh, '+'), Char.is_eq(hh, '-'), hh, tt, sg, {==}, {==}, n1.Zi(tt, sg, True{}),
        n1.Di(tt, sg, T.dec.go([], 10, T.dig.val(hh)), "", True{}))

# no prefixed integer starts with a character that is no 0
def n1.pre.n0(
  +cc: Char,
  tt: List<&2, Char>,
  +ll: U32,
  +rx: D1.ARadix,
  +h0: {Char.is_eq(cc, '0') == False{} : Bool}
) -> {False{} == D1.abnf.prefixed(cc <> tt, ll, rx) : Bool}:
  match tt:
    case []:
      {==}
    case +c1 <> rr:
      match rr:
        case []:
          {==}
        case +c2 <> +r2:
          %Equal.trans(Bool, False{}, Char.is_eq(cc, '0'), D1.abnf.cp(cc, 48), Equal.sym(Bool, Char.is_eq(cc, '0'),
            False{}, h0), n1.cp(cc, 48)) : {False{} == Bool.and(_, Bool.and(D1.abnf.cp(c1, ll),
            Bool.and(D1.abnf.radix_digit(rx, c2), D1.abnf.radix_rep(r2, rx)))) : Bool}
          {==}

# a sign and an unsigned-dec-int are an integer, and nothing else after a
# sign is
def n1.int.sgn(
  +cc: Char,
  +tt: List<&2, Char>,
  hd: {Char.is_digit(cc) == False{} : Bool},
  +h0: {Char.is_eq(cc, '0') == False{} : Bool},
  hs: {Bool.or(D1.abnf.minus(cc), D1.abnf.plus(cc)) == True{} : Bool}
) -> {D1.abnf.unsigned_dec_int(tt) == D1.abnf.integer(cc <> tt) : Bool}:
  %Equal.sym(Bool, Bool.or(D1.abnf.minus(cc), D1.abnf.plus(cc)), True{}, hs) : {D1.abnf.unsigned_dec_int(tt)
    == Bool.or(Bool.or(Bool.and(_, D1.abnf.unsigned_dec_int(tt)), D1.abnf.unsigned_dec_int(cc <> tt)),
    Bool.or(D1.abnf.hex_int(cc <> tt), Bool.or(D1.abnf.oct_int(cc <> tt), D1.abnf.bin_int(cc <> tt)))) : Bool}
  %M7.n1.udi.n(cc, tt, hd) : {D1.abnf.unsigned_dec_int(tt) == Bool.or(Bool.or(D1.abnf.unsigned_dec_int(tt), _),
    Bool.or(D1.abnf.hex_int(cc <> tt), Bool.or(D1.abnf.oct_int(cc <> tt), D1.abnf.bin_int(cc <> tt)))) : Bool}
  %n1.pre.n0(cc, tt, 120, D1.AHex{}, h0) : {D1.abnf.unsigned_dec_int(tt) == Bool.or(Bool.or(
    D1.abnf.unsigned_dec_int(tt), False{}), Bool.or(_, Bool.or(D1.abnf.oct_int(cc <> tt), D1.abnf.bin_int(cc <>
    tt)))) : Bool}
  %n1.pre.n0(cc, tt, 111, D1.AOct{}, h0) : {D1.abnf.unsigned_dec_int(tt) == Bool.or(Bool.or(
    D1.abnf.unsigned_dec_int(tt), False{}), Bool.or(False{}, Bool.or(_, D1.abnf.bin_int(cc <> tt)))) : Bool}
  %n1.pre.n0(cc, tt, 98, D1.ABin{}, h0) : {D1.abnf.unsigned_dec_int(tt) == Bool.or(Bool.or(
    D1.abnf.unsigned_dec_int(tt), False{}), Bool.or(False{}, Bool.or(False{}, _))) : Bool}
  %Equal.sym(Bool, Bool.or(D1.abnf.unsigned_dec_int(tt), False{}), D1.abnf.unsigned_dec_int(tt),
    M7.n1.orf(D1.abnf.unsigned_dec_int(tt))) : {D1.abnf.unsigned_dec_int(tt) == Bool.or(_, False{}) : Bool}
  M7.n1.orf.eq(D1.abnf.unsigned_dec_int(tt), D1.abnf.unsigned_dec_int(tt), {==})

# a digit that is not 0 and the repetition are an integer
def n1.int.dig(
  +cc: Char,
  +tt: List<&2, Char>,
  +hd: {Char.is_digit(cc) == True{} : Bool},
  +h0: {Char.is_eq(cc, '0') == False{} : Bool},
  em: {False{} == D1.abnf.minus(cc) : Bool},
  ep: {False{} == D1.abnf.plus(cc) : Bool}
) -> {D1.abnf.dec_rep(tt) == D1.abnf.integer(cc <> tt) : Bool}:
  %em : {D1.abnf.dec_rep(tt) == Bool.or(Bool.or(Bool.and(Bool.or(_, D1.abnf.plus(cc)),
    D1.abnf.unsigned_dec_int(tt)), D1.abnf.unsigned_dec_int(cc <> tt)), Bool.or(D1.abnf.hex_int(cc <> tt),
    Bool.or(D1.abnf.oct_int(cc <> tt), D1.abnf.bin_int(cc <> tt)))) : Bool}
  %ep : {D1.abnf.dec_rep(tt) == Bool.or(Bool.or(Bool.and(Bool.or(False{}, _), D1.abnf.unsigned_dec_int(tt)),
    D1.abnf.unsigned_dec_int(cc <> tt)), Bool.or(D1.abnf.hex_int(cc <> tt), Bool.or(D1.abnf.oct_int(cc <> tt),
    D1.abnf.bin_int(cc <> tt)))) : Bool}
  %M7.n1.udi.d(cc, tt, M7.n1.d19.y(cc, hd, h0)) : {D1.abnf.dec_rep(tt) == Bool.or(Bool.or(False{}, _),
    Bool.or(D1.abnf.hex_int(cc <> tt), Bool.or(D1.abnf.oct_int(cc <> tt), D1.abnf.bin_int(cc <> tt)))) : Bool}
  %n1.pre.n0(cc, tt, 120, D1.AHex{}, h0) : {D1.abnf.dec_rep(tt) == Bool.or(D1.abnf.dec_rep(tt), Bool.or(_,
    Bool.or(D1.abnf.oct_int(cc <> tt), D1.abnf.bin_int(cc <> tt)))) : Bool}
  %n1.pre.n0(cc, tt, 111, D1.AOct{}, h0) : {D1.abnf.dec_rep(tt) == Bool.or(D1.abnf.dec_rep(tt), Bool.or(False{},
    Bool.or(_, D1.abnf.bin_int(cc <> tt)))) : Bool}
  %n1.pre.n0(cc, tt, 98, D1.ABin{}, h0) : {D1.abnf.dec_rep(tt) == Bool.or(D1.abnf.dec_rep(tt), Bool.or(False{},
    Bool.or(False{}, _))) : Bool}
  M7.n1.orf.eq(D1.abnf.dec_rep(tt), D1.abnf.dec_rep(tt), {==})

# a first character that is no sign, no digit is no integer
def n1.int.no(
  +cc: Char,
  +tt: List<&2, Char>,
  hd: {Char.is_digit(cc) == False{} : Bool},
  +h0: {Char.is_eq(cc, '0') == False{} : Bool},
  em: {False{} == D1.abnf.minus(cc) : Bool},
  ep: {False{} == D1.abnf.plus(cc) : Bool}
) -> {False{} == D1.abnf.integer(cc <> tt) : Bool}:
  %em : {False{} == Bool.or(Bool.or(Bool.and(Bool.or(_, D1.abnf.plus(cc)), D1.abnf.unsigned_dec_int(tt)),
    D1.abnf.unsigned_dec_int(cc <> tt)), Bool.or(D1.abnf.hex_int(cc <> tt), Bool.or(D1.abnf.oct_int(cc <> tt),
    D1.abnf.bin_int(cc <> tt)))) : Bool}
  %ep : {False{} == Bool.or(Bool.or(Bool.and(Bool.or(False{}, _), D1.abnf.unsigned_dec_int(tt)),
    D1.abnf.unsigned_dec_int(cc <> tt)), Bool.or(D1.abnf.hex_int(cc <> tt), Bool.or(D1.abnf.oct_int(cc <> tt),
    D1.abnf.bin_int(cc <> tt)))) : Bool}
  %M7.n1.udi.n(cc, tt, hd) : {False{} == Bool.or(Bool.or(False{}, _), Bool.or(D1.abnf.hex_int(cc <> tt),
    Bool.or(D1.abnf.oct_int(cc <> tt), D1.abnf.bin_int(cc <> tt)))) : Bool}
  %n1.pre.n0(cc, tt, 120, D1.AHex{}, h0) : {False{} == Bool.or(False{}, Bool.or(_, Bool.or(D1.abnf.oct_int(cc <>
    tt), D1.abnf.bin_int(cc <> tt)))) : Bool}
  %n1.pre.n0(cc, tt, 111, D1.AOct{}, h0) : {False{} == Bool.or(False{}, Bool.or(False{}, Bool.or(_,
    D1.abnf.bin_int(cc <> tt)))) : Bool}
  %n1.pre.n0(cc, tt, 98, D1.ABin{}, h0) : {False{} == Bool.or(False{}, Bool.or(False{}, Bool.or(False{}, _)))
    : Bool}
  {==}

# a first character that is no sign and no zero, for integers
def n1.Li2.go(
  dd: Bool,
  +cc: Char,
  +tt: List<&2, Char>,
  +ez: {Char.is_eq(cc, '0') == False{} : Bool},
  +ed: {Char.is_digit(cc) == dd : Bool},
  +fm: {False{} == D1.abnf.minus(cc) : Bool},
  +fp: {False{} == D1.abnf.plus(cc) : Bool},
  ihd: n1.Di.G(tt, T.Plus{}, T.dec.go([], 10, T.dig.val(cc)), "", False{})
) -> {n1.ish(T.num.go(tt, T.num.lead.go(False{}, False{}, False{}, dd, T.num.start(), cc)), False{})
  == D1.abnf.integer(cc <> tt) : Bool}:
  match dd:
    case True{}:
      %n1.int.dig(cc, tt, ed, ez, fm, fp) : {n1.ish(T.num.go(tt, T.num.digit.ok(T.dig.ok(T.dig.val(cc), 10), cc,
        T.NDig{}, T.Plus{}, 10, [])), False{}) == _ : Bool}
      %Equal.sym(Bool, T.dig.ok(T.dig.val(cc), 10), True{}, M7.n1.dok10(cc, ed)) : {n1.ish(T.num.go(tt,
        T.num.digit.ok(_, cc, T.NDig{}, T.Plus{}, 10, [])), False{}) == D1.abnf.dec_rep(tt) : Bool}
      ihd
    case False{}:
      %n1.int.no(cc, tt, ed, ez, fm, fp) : {n1.ish(T.num.go(tt, T.num.bad(T.num.start(), "invalid number")), False{})
        == _ : Bool}
      n1.ish.bad(tt, False{}, "invalid number")

# the first character of a word, for integers
def n1.Li.go(
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
  ihp: {n1.ish(T.num.go(tt, M7.n1.ss(T.Plus{})), True{}) == D1.abnf.unsigned_dec_int(tt) : Bool},
  ihm: {n1.ish(T.num.go(tt, M7.n1.ss(T.Minus{})), True{}) == D1.abnf.unsigned_dec_int(tt) : Bool},
  ihz: n1.Zi.G(tt, T.Plus{}, False{}),
  ihd: n1.Di.G(tt, T.Plus{}, T.dec.go([], 10, T.dig.val(cc)), "", False{})
) -> {n1.ish(T.num.go(tt, T.num.lead.go(pp, mm, zz, dd, T.num.start(), cc)), Bool.or(pp, mm))
  == D1.abnf.integer(cc <> tt) : Bool}:
  match pp:
    case True{}:
      %Equal.sym(Char, cc, '+', Eq.char_eq_true(cc, '+', ep)) : {n1.ish(T.num.go(tt, M7.n1.ss(T.Plus{})), True{})
        == D1.abnf.integer(_ <> tt) : Bool}
      %n1.int.sgn('+', tt, {==}, {==}, {==}) : {n1.ish(T.num.go(tt, M7.n1.ss(T.Plus{})), True{}) == _ : Bool}
      ihp
    case False{}:
      match mm:
        case True{}:
          %Equal.sym(Char, cc, '-', Eq.char_eq_true(cc, '-', em)) : {n1.ish(T.num.go(tt, M7.n1.ss(T.Minus{})), True{})
            == D1.abnf.integer(_ <> tt) : Bool}
          %n1.int.sgn('-', tt, {==}, {==}, {==}) : {n1.ish(T.num.go(tt, M7.n1.ss(T.Minus{})), True{}) == _ : Bool}
          ihm
        case False{}:
          match zz:
            case True{}:
              %Equal.sym(Char, cc, '0', Eq.char_eq_true(cc, '0', ez)) : {n1.ish(T.num.go(tt, M7.n1.sz(T.Plus{})),
                  False{})
                == D1.abnf.integer(_ <> tt) : Bool}
              ihz
            case False{}:
              n1.Li2.go(dd, cc, tt, ez, ed, Equal.trans(Bool, False{}, Char.is_eq(cc, '-'), D1.abnf.minus(cc),
                Equal.sym(Bool, Char.is_eq(cc, '-'), False{}, em), M7.n1.minus(cc)), Equal.trans(Bool, False{},
                Char.is_eq(cc, '+'), D1.abnf.plus(cc), Equal.sym(Bool, Char.is_eq(cc, '+'), False{}, ep),
                M7.n1.plus(cc)), ihd)

# the numeral scan finishes as an integer, or one out of range, exactly when
# the word matches toml.abnf's integer rule
def n1.int.sh(
  cs: List<&2, Char>
) -> {n1.ish(T.num.go(cs, T.num.start()), T.num.signed(cs)) == D1.abnf.integer(cs) : Bool}:
  match cs:
    case []:
      {==}
    case +hh <> +tt:
      n1.Li.go(Char.is_eq(hh, '+'), Char.is_eq(hh, '-'), Char.is_eq(hh, '0'), Char.is_digit(hh), hh, tt, {==}, {==},
        {==}, {==}, n1.Si(tt, T.Plus{}), n1.Si(tt, T.Minus{}), n1.Zi(tt, T.Plus{}, False{}),
        n1.Di(tt, T.Plus{}, T.dec.go([], 10, T.dig.val(hh)), "", False{}))

# Arithmetic. An integer's value is a Nat, compared and never computed: every
# Nat here stays symbolic, and a large constant is reached only through a
# lemma stated for any Nat.

# a times zero is zero
def n1.mul0(aa: Nat) -> {Nat.mul(aa, 0n) == 0n : Nat}:
  match aa:
    case 0n:
      {==}
    case 1n+(+pp):
      n1.mul0(pp)

# a times one more than b is a and a times b
def n1.muls(aa: Nat, +bb: Nat) -> {Nat.mul(aa, 1n+bb) == Nat.add(aa, Nat.mul(aa, bb)) : Nat}:
  match aa:
    case 0n:
      {==}
    case 1n+(+pp):
      %Equal.sym(Nat, Nat.mul(pp, 1n+bb), Nat.add(pp, Nat.mul(pp, bb)), n1.muls(pp, bb)) : {1n+Nat.add(bb, _)
        == 1n+Nat.add(pp, Nat.add(bb, Nat.mul(pp, bb))) : Nat}
      Equal.cong(Nat, Nat, xx => 1n+xx, Nat.add(bb, Nat.add(pp, Nat.mul(pp, bb))), Nat.add(pp, Nat.add(bb,
        Nat.mul(pp, bb))), Ar.nat_add_lcomm(bb, pp, Nat.mul(pp, bb)))

# multiplication commutes
def n1.mulc(aa: Nat, +bb: Nat) -> {Nat.mul(aa, bb) == Nat.mul(bb, aa) : Nat}:
  match aa:
    case 0n:
      Equal.sym(Nat, Nat.mul(bb, 0n), 0n, n1.mul0(bb))
    case 1n+(+pp):
      %Equal.sym(Nat, Nat.mul(pp, bb), Nat.mul(bb, pp), n1.mulc(pp, bb)) : {Nat.add(bb, _) == Nat.mul(bb, 1n+pp) : Nat}
      Equal.sym(Nat, Nat.mul(bb, 1n+pp), Nat.add(bb, Nat.mul(bb, pp)), n1.muls(bb, pp))

# a common left addend leaves a comparison as it is
def n1.cmp.add(mm: Nat, +xx: Nat, +yy: Nat) -> {Nat.cmp(Nat.add(mm, xx), Nat.add(mm, yy)) == Nat.cmp(xx, yy) : Cmp}:
  match mm:
    case 0n:
      {==}
    case 1n+(+pp):
      n1.cmp.add(pp, xx, yy)

# a Nat below another compares LT with it
def n1.cmp.lt(aa: Nat, bb: Nat, hh: {Nat.is_lt(aa, bb) == True{} : Bool}) -> {Nat.cmp(aa, bb) == LT{} : Cmp}:
  match aa bb:
    case 0n 0n:
      Eq.bit.absurd(&2, {Nat.cmp(0n, 0n) == LT{} : Cmp}, hh)
    case 0n 1n+_b:
      {==}
    case 1n+(+a1) 0n:
      Eq.bit.absurd(&2, {Nat.cmp(1n+a1, 0n) == LT{} : Cmp}, hh)
    case 1n+(+a1) 1n+(+b1):
      n1.cmp.lt(a1, b1, hh)

# a Nat above another compares GT with it
def n1.cmp.gt(aa: Nat, bb: Nat, hh: {Nat.is_lt(bb, aa) == True{} : Bool}) -> {Nat.cmp(aa, bb) == GT{} : Cmp}:
  match aa bb:
    case 0n 0n:
      Eq.bit.absurd(&2, {Nat.cmp(0n, 0n) == GT{} : Cmp}, hh)
    case 0n 1n+(+b1):
      Eq.bit.absurd(&2, {Nat.cmp(0n, 1n+b1) == GT{} : Cmp}, hh)
    case 1n+_a 0n:
      {==}
    case 1n+(+a1) 1n+(+b1):
      n1.cmp.gt(a1, b1, hh)

# the ones and the rest: comparing a times M and A with b times M and B, for A
# and B below M, compares a with b and then A with B, as i64.ord folds a
# comparison of digits
def n1.ka(
  aa: Nat,
  bb: Nat,
  +mm: Nat,
  +xa: Nat,
  +xb: Nat,
  +ha: {Nat.is_lt(xa, mm) == True{} : Bool},
  +hb: {Nat.is_lt(xb, mm) == True{} : Bool}
) -> {Nat.cmp(Nat.add(Nat.mul(aa, mm), xa), Nat.add(Nat.mul(bb, mm), xb)) == T.i64.ord(Nat.cmp(aa, bb), Nat.cmp(xa,
  xb)) : Cmp}:
  match aa bb:
    case 0n 0n:
      {==}
    case 0n 1n+(+b1):
      n1.cmp.lt(xa, Nat.add(Nat.add(mm, Nat.mul(b1, mm)), xb), M2.lt.add(xa, Nat.add(mm, Nat.mul(b1, mm)), xb,
          M2.lt.add(xa,
        mm, Nat.mul(b1, mm), ha)))
    case 1n+(+a1) 0n:
      n1.cmp.gt(Nat.add(Nat.add(mm, Nat.mul(a1, mm)), xa), xb, M2.lt.add(xb, Nat.add(mm, Nat.mul(a1, mm)), xa,
          M2.lt.add(xb,
        mm, Nat.mul(a1, mm), hb)))
    case 1n+(+a1) 1n+(+b1):
      %Equal.sym(Nat, Nat.add(Nat.add(mm, Nat.mul(a1, mm)), xa), Nat.add(mm, Nat.add(Nat.mul(a1, mm), xa)),
        Ar.nat_add_assoc(mm, Nat.mul(a1, mm), xa)) : {Nat.cmp(_, Nat.add(Nat.add(mm, Nat.mul(b1, mm)), xb))
        == T.i64.ord(Nat.cmp(a1, b1), Nat.cmp(xa, xb)) : Cmp}
      %Equal.sym(Nat, Nat.add(Nat.add(mm, Nat.mul(b1, mm)), xb), Nat.add(mm, Nat.add(Nat.mul(b1, mm), xb)),
        Ar.nat_add_assoc(mm, Nat.mul(b1, mm), xb)) : {Nat.cmp(Nat.add(mm, Nat.add(Nat.mul(a1, mm), xa)), _)
        == T.i64.ord(Nat.cmp(a1, b1), Nat.cmp(xa, xb)) : Cmp}
      Equal.trans(Cmp, Nat.cmp(Nat.add(mm, Nat.add(Nat.mul(a1, mm), xa)), Nat.add(mm, Nat.add(Nat.mul(b1, mm), xb))),
        Nat.cmp(Nat.add(Nat.mul(a1, mm), xa), Nat.add(Nat.mul(b1, mm), xb)), T.i64.ord(Nat.cmp(a1, b1), Nat.cmp(xa,
        xb)), n1.cmp.add(mm, Nat.add(Nat.mul(a1, mm), xa), Nat.add(Nat.mul(b1, mm), xb)), n1.ka(a1, b1, mm, xa, xb,
        ha, hb))

# at most is transitive
def n1.le.trans(
  aa: Nat,
  bb: Nat,
  cc: Nat,
  +h1: {Nat.is_le(aa, bb) == True{} : Bool},
  +h2: {Nat.is_le(bb, cc) == True{} : Bool}
) -> {Nat.is_le(aa, cc) == True{} : Bool}:
  match aa bb cc:
    case 0n _b _c:
      n1.le0(_c)
    case 1n+(+a1) 0n _c:
      Eq.bit.absurd(&2, {Nat.is_le(1n+a1, _c) == True{} : Bool}, h1)
    case 1n+(+a1) 1n+(+b1) 0n:
      Eq.bit.absurd(&2, {Nat.is_le(1n+a1, 0n) == True{} : Bool}, h2)
    case 1n+(+a1) 1n+(+b1) 1n+(+c1):
      n1.le.trans(a1, b1, c1, h1, h2)

# below then at most is below
def n1.lt.le(
  aa: Nat,
  bb: Nat,
  cc: Nat,
  +h1: {Nat.is_lt(aa, bb) == True{} : Bool},
  +h2: {Nat.is_le(bb, cc) == True{} : Bool}
) -> {Nat.is_lt(aa, cc) == True{} : Bool}:
  match aa bb cc:
    case _a 0n _c:
      Eq.bit.absurd(&2, {Nat.is_lt(_a, _c) == True{} : Bool}, Equal.trans(Bool, False{}, Nat.is_lt(_a, 0n), True{},
        Equal.sym(Bool, Nat.is_lt(_a, 0n), False{}, M2.nlt.zero(_a)), h1))
    case _a 1n+(+b1) 0n:
      Eq.bit.absurd(&2, {Nat.is_lt(_a, 0n) == True{} : Bool}, h2)
    case 0n 1n+(+b1) 1n+(+c1):
      {==}
    case 1n+(+a1) 1n+(+b1) 1n+(+c1):
      n1.lt.le(a1, b1, c1, h1, h2)

# a Nat is at most itself and more
def n1.le.addr(xx: Nat, +yy: Nat) -> {Nat.is_le(xx, Nat.add(xx, yy)) == True{} : Bool}:
  match xx:
    case 0n:
      n1.le0(yy)
    case 1n+(+x1):
      n1.le.addr(x1, yy)

# below b, one more is at most b
def n1.lt.suc(aa: Nat, bb: Nat, hh: {Nat.is_lt(aa, bb) == True{} : Bool}) -> {Nat.is_le(1n+aa, bb) == True{} : Bool}:
  match aa bb:
    case _a 0n:
      Eq.bit.absurd(&2, {Nat.is_le(1n+_a, 0n) == True{} : Bool}, Equal.trans(Bool, False{}, Nat.is_lt(_a, 0n), True{},
        Equal.sym(Bool, Nat.is_lt(_a, 0n), False{}, M2.nlt.zero(_a)), hh))
    case 0n 1n+(+b1):
      n1.le0(b1)
    case 1n+(+a1) 1n+(+b1):
      n1.lt.suc(a1, b1, hh)

# a times P is at most b times P for a at most b
def n1.le.mul(
  aa: Nat,
  bb: Nat,
  +pp: Nat,
  +hh: {Nat.is_le(aa, bb) == True{} : Bool}
) -> {Nat.is_le(Nat.mul(aa, pp), Nat.mul(bb, pp)) == True{} : Bool}:
  match aa bb:
    case 0n _b:
      n1.le0(Nat.mul(_b, pp))
    case 1n+(+a1) 0n:
      Eq.bit.absurd(&2, {Nat.is_le(Nat.mul(1n+a1, pp), 0n) == True{} : Bool}, hh)
    case 1n+(+a1) 1n+(+b1):
      Equal.trans(Bool, Nat.is_le(Nat.add(pp, Nat.mul(a1, pp)), Nat.add(pp, Nat.mul(b1, pp))),
        Nat.is_le(Nat.mul(a1, pp), Nat.mul(b1, pp)), True{}, Equal.cong(Cmp, Bool, xx => Cmp.is_le(xx),
        Nat.cmp(Nat.add(pp, Nat.mul(a1, pp)), Nat.add(pp, Nat.mul(b1, pp))), Nat.cmp(Nat.mul(a1, pp), Nat.mul(b1, pp)),
        n1.cmp.add(pp, Nat.mul(a1, pp), Nat.mul(b1, pp))), n1.le.mul(a1, b1, pp, hh))

# no underscore among the characters
def n1.nou(xs: List<&2, Char>) -> Bool:
  match xs:
    case []:
      True{}
    case hh <> tt:
      Bool.and(Bool.not(D1.abnf.underscore(hh)), n1.nou(tt))

# every character's value is below r
def n1.dlt(xs: List<&2, Char>, +rr: Nat) -> Bool:
  match xs:
    case []:
      True{}
    case hh <> tt:
      Bool.and(Nat.is_lt(D1.g.hexdig.val(hh), rr), n1.dlt(tt, rr))

# a character that is no underscore is one more place of the value
def n1.gn.step(
  +hh: Char,
  +tt: List<&2, Char>,
  +rr: Nat,
  +acc: Nat,
  +hu: {Bool.not(D1.abnf.underscore(hh)) == True{} : Bool}
) -> {D1.g.num.nat(hh <> tt, rr, acc) == D1.g.num.nat(tt, rr, Nat.add(Nat.mul(acc, rr), D1.g.hexdig.val(hh)))
  : Nat}:
  %Equal.sym(Bool, D1.abnf.underscore(hh), False{}, M7.n1.not.t(D1.abnf.underscore(hh), hu)) :
    {D1.g.num.nat(tt, rr, D1.g.num.nat.step(_, hh, rr, acc)) == D1.g.num.nat(tt, rr, Nat.add(Nat.mul(acc, rr),
    D1.g.hexdig.val(hh))) : Nat}
  {==}

# what the value of the digits before contributes: the value from acc is acc
# times the radix to the number of digits, and the value from 0
def n1.hl(
  xs: List<&2, Char>,
  +rr: Nat,
  +acc: Nat,
  +hn: {n1.nou(xs) == True{} : Bool}
) -> {D1.g.num.nat(xs, rr, acc) == Nat.add(Nat.mul(acc, Nat.pow(rr, List.length(&2, Char, xs))),
  D1.g.num.nat(xs, rr, 0n)) : Nat}:
  match xs:
    case []:
      %Equal.sym(Nat, Nat.add(Nat.mul(acc, 1n), 0n), Nat.mul(acc, 1n), Ar.nat_add_zero(Nat.mul(acc, 1n))) :
        {acc == _ : Nat}
      Equal.sym(Nat, Nat.mul(acc, 1n), acc, Ar.nat_mul_one(acc))
    case +hh <> +tt:
      +hu = {Eq.and.left(Bool.not(D1.abnf.underscore(hh)), n1.nou(tt), hn) : {Bool.not(D1.abnf.underscore(hh))
        == True{} : Bool}}
      +ht = {Eq.and.right(Bool.not(D1.abnf.underscore(hh)), n1.nou(tt), hn) : {n1.nou(tt) == True{} : Bool}}
      +dd = D1.g.hexdig.val(hh)
      +pp = Nat.pow(rr, List.length(&2, Char, tt))
      +gg = D1.g.num.nat(tt, rr, 0n)
      %Equal.sym(Nat, D1.g.num.nat(hh <> tt, rr, acc), D1.g.num.nat(tt, rr, Nat.add(Nat.mul(acc, rr), dd)),
        n1.gn.step(hh, tt, rr, acc, hu)) : {_ == Nat.add(Nat.mul(acc, Nat.mul(rr, pp)), D1.g.num.nat(hh <> tt, rr,
        0n)) : Nat}
      %Equal.sym(Nat, D1.g.num.nat(hh <> tt, rr, 0n), D1.g.num.nat(tt, rr, dd), n1.gn.step(hh, tt, rr, 0n, hu)) :
        {D1.g.num.nat(tt, rr, Nat.add(Nat.mul(acc, rr), dd)) == Nat.add(Nat.mul(acc, Nat.mul(rr, pp)), _) : Nat}
      %Equal.sym(Nat, D1.g.num.nat(tt, rr, Nat.add(Nat.mul(acc, rr), dd)), Nat.add(Nat.mul(Nat.add(Nat.mul(acc, rr),
        dd), pp), gg), n1.hl(tt, rr, Nat.add(Nat.mul(acc, rr), dd), ht)) : {_ == Nat.add(Nat.mul(acc, Nat.mul(rr,
        pp)), D1.g.num.nat(tt, rr, dd)) : Nat}
      %Equal.sym(Nat, D1.g.num.nat(tt, rr, dd), Nat.add(Nat.mul(dd, pp), gg), n1.hl(tt, rr, dd, ht)) :
        {Nat.add(Nat.mul(Nat.add(Nat.mul(acc, rr), dd), pp), gg) == Nat.add(Nat.mul(acc, Nat.mul(rr, pp)), _) : Nat}
      %Equal.sym(Nat, Nat.mul(Nat.add(Nat.mul(acc, rr), dd), pp), Nat.add(Nat.mul(Nat.mul(acc, rr), pp), Nat.mul(dd,
        pp)), Ar.nat_mul_add_r(Nat.mul(acc, rr), dd, pp)) : {Nat.add(_, gg) == Nat.add(Nat.mul(acc, Nat.mul(rr, pp)),
        Nat.add(Nat.mul(dd, pp), gg)) : Nat}
      %Equal.sym(Nat, Nat.mul(Nat.mul(acc, rr), pp), Nat.mul(acc, Nat.mul(rr, pp)), Ar.nat_mul_assoc(acc, rr, pp)) :
        {Nat.add(Nat.add(_, Nat.mul(dd, pp)), gg) == Nat.add(Nat.mul(acc, Nat.mul(rr, pp)), Nat.add(Nat.mul(dd, pp),
        gg)) : Nat}
      Ar.nat_add_assoc(Nat.mul(acc, Nat.mul(rr, pp)), Nat.mul(dd, pp), gg)

# a Nat is at most itself
def n1.le.refl(xx: Nat) -> {Nat.is_le(xx, xx) == True{} : Bool}:
  Equal.cong(Cmp, Bool, cc => Cmp.is_le(cc), Nat.cmp(xx, xx), EQ{}, M2.ncmp.refl(xx))

# the value of digits below the radix, from 0, is below the radix to the
# number of digits
def n1.hb(
  xs: List<&2, Char>,
  +rr: Nat,
  +hn: {n1.nou(xs) == True{} : Bool},
  +hd: {n1.dlt(xs, rr) == True{} : Bool}
) -> {Nat.is_lt(D1.g.num.nat(xs, rr, 0n), Nat.pow(rr, List.length(&2, Char, xs))) == True{} : Bool}:
  match xs:
    case []:
      {==}
    case +hh <> +tt:
      +hu = {Eq.and.left(Bool.not(D1.abnf.underscore(hh)), n1.nou(tt), hn) : {Bool.not(D1.abnf.underscore(hh))
        == True{} : Bool}}
      +ht = {Eq.and.right(Bool.not(D1.abnf.underscore(hh)), n1.nou(tt), hn) : {n1.nou(tt) == True{} : Bool}}
      +hdh = {Eq.and.left(Nat.is_lt(D1.g.hexdig.val(hh), rr), n1.dlt(tt, rr), hd) : {Nat.is_lt(D1.g.hexdig.val(hh),
        rr) == True{} : Bool}}
      +hdt = {Eq.and.right(Nat.is_lt(D1.g.hexdig.val(hh), rr), n1.dlt(tt, rr), hd) : {n1.dlt(tt, rr) == True{}
        : Bool}}
      +dd = D1.g.hexdig.val(hh)
      +pp = Nat.pow(rr, List.length(&2, Char, tt))
      +gg = D1.g.num.nat(tt, rr, 0n)
      %Equal.sym(Nat, D1.g.num.nat(hh <> tt, rr, 0n), D1.g.num.nat(tt, rr, dd), n1.gn.step(hh, tt, rr, 0n, hu)) :
        {Nat.is_lt(_, Nat.mul(rr, pp)) == True{} : Bool}
      %Equal.sym(Nat, D1.g.num.nat(tt, rr, dd), Nat.add(Nat.mul(dd, pp), gg), n1.hl(tt, rr, dd, ht)) :
        {Nat.is_lt(_, Nat.mul(rr, pp)) == True{} : Bool}
      n1.lt.le(Nat.add(Nat.mul(dd, pp), gg), Nat.add(Nat.mul(dd, pp), pp), Nat.mul(rr, pp),
        Equal.trans(Bool, Nat.is_lt(Nat.add(Nat.mul(dd, pp), gg), Nat.add(Nat.mul(dd, pp), pp)), Nat.is_lt(gg, pp),
        True{}, Equal.cong(Cmp, Bool, cc => Cmp.is_lt(cc), Nat.cmp(Nat.add(Nat.mul(dd, pp), gg), Nat.add(Nat.mul(dd,
        pp), pp)), Nat.cmp(gg, pp), n1.cmp.add(Nat.mul(dd, pp), gg, pp)), n1.hb(tt, rr, ht, hdt)),
        Equal.trans(Bool, Nat.is_le(Nat.add(Nat.mul(dd, pp), pp), Nat.mul(rr, pp)), Nat.is_le(Nat.mul(1n+dd, pp),
        Nat.mul(rr, pp)), True{}, Equal.cong(Nat, Bool, xx => Nat.is_le(xx, Nat.mul(rr, pp)), Nat.add(Nat.mul(dd, pp),
        pp), Nat.add(pp, Nat.mul(dd, pp)), Ar.nat_add_comm(Nat.mul(dd, pp), pp)), n1.le.mul(1n+dd, rr, pp,
        n1.lt.suc(dd, rr, hdh))))

# digits whose first is not 0 are worth at least the radix to the number of
# digits after the first
def n1.low(
  +hh: Char,
  +tt: List<&2, Char>,
  +rr: Nat,
  +hn: {n1.nou(hh <> tt) == True{} : Bool},
  +hf: {Nat.is_lt(0n, D1.g.hexdig.val(hh)) == True{} : Bool}
) -> {Nat.is_le(Nat.pow(rr, List.length(&2, Char, tt)), D1.g.num.nat(hh <> tt, rr, 0n)) == True{} : Bool}:
  +hu = {Eq.and.left(Bool.not(D1.abnf.underscore(hh)), n1.nou(tt), hn) : {Bool.not(D1.abnf.underscore(hh))
    == True{} : Bool}}
  +ht = {Eq.and.right(Bool.not(D1.abnf.underscore(hh)), n1.nou(tt), hn) : {n1.nou(tt) == True{} : Bool}}
  +dd = D1.g.hexdig.val(hh)
  +pp = Nat.pow(rr, List.length(&2, Char, tt))
  +gg = D1.g.num.nat(tt, rr, 0n)
  %Equal.sym(Nat, D1.g.num.nat(hh <> tt, rr, 0n), D1.g.num.nat(tt, rr, dd), n1.gn.step(hh, tt, rr, 0n, hu)) :
    {Nat.is_le(pp, _) == True{} : Bool}
  %Equal.sym(Nat, D1.g.num.nat(tt, rr, dd), Nat.add(Nat.mul(dd, pp), gg), n1.hl(tt, rr, dd, ht)) :
    {Nat.is_le(pp, _) == True{} : Bool}
  n1.le.trans(pp, Nat.mul(dd, pp), Nat.add(Nat.mul(dd, pp), gg), Equal.trans(Bool, Nat.is_le(pp, Nat.mul(dd, pp)),
    Nat.is_le(Nat.add(pp, 0n), Nat.mul(dd, pp)), True{}, Equal.cong(Nat, Bool, xx => Nat.is_le(xx, Nat.mul(dd, pp)),
    pp, Nat.add(pp, 0n), Equal.sym(Nat, Nat.add(pp, 0n), pp, Ar.nat_add_zero(pp))), n1.le.mul(1n, dd, pp,
    n1.lt.suc(0n, dd, hf))), n1.le.addr(Nat.mul(dd, pp), gg))

# a power grows with its exponent, for a radix above 0
def n1.pw.le(
  rr: Nat,
  +aa: Nat,
  kk: Nat,
  +hr: {Nat.is_lt(0n, rr) == True{} : Bool}
) -> {Nat.is_le(Nat.pow(rr, aa), Nat.pow(rr, Nat.add(aa, kk))) == True{} : Bool}:
  match rr kk:
    case 0n _k:
      Eq.bit.absurd(&2, {Nat.is_le(Nat.pow(0n, aa), Nat.pow(0n, Nat.add(aa, _k))) == True{} : Bool}, hr)
    case 1n+(+r1) 0n:
      %Equal.sym(Nat, Nat.add(aa, 0n), aa, Ar.nat_add_zero(aa)) : {Nat.is_le(Nat.pow(1n+r1, aa), Nat.pow(1n+r1, _))
        == True{} : Bool}
      n1.le.refl(Nat.pow(1n+r1, aa))
    case 1n+(+r1) 1n+(+k1):
      %Equal.sym(Nat, Nat.add(aa, 1n+k1), 1n+Nat.add(aa, k1), Ar.nat_add_succ(aa, k1)) : {Nat.is_le(Nat.pow(1n+r1,
        aa), Nat.pow(1n+r1, _)) == True{} : Bool}
      n1.le.trans(Nat.pow(1n+r1, aa), Nat.pow(1n+r1, Nat.add(aa, k1)), Nat.mul(1n+r1, Nat.pow(1n+r1, Nat.add(aa, k1))),
        n1.pw.le(1n+r1, aa, k1, hr), n1.le.addr(Nat.pow(1n+r1, Nat.add(aa, k1)), Nat.mul(r1, Nat.pow(1n+r1,
        Nat.add(aa, k1)))))

# An integer's value. A digit of a radix is one of 22 characters, and what
# the scan and the grammar compute of each is checked one by one.

# a claim of a character under its being a digit of the radix
def n1.rd.Q(P: Char -> Type, rx: D1.ARadix, cc: Char) -> Type:
  {D1.abnf.radix_digit(rx, cc) == True{} : Bool} -> P(cc)

# 99 is no digit of any base
def n1.no99(rx: D1.ARadix) -> {T.dig.ok(99, n1.rb(rx)) == False{} : Bool}:
  match rx:
    case D1.AHex{}:
      {==}
    case D1.AOct{}:
      {==}
    case D1.ABin{}:
      {==}

# a code point that is a digit, a letter a to f, a letter A to F, or none of
# them, and a digit of the radix
def n1.rd.go(
  dd: Bool,
  ll: Bool,
  uu: Bool,
  -P: Char -> Type,
  +rx: D1.ARadix,
  +cp: U32,
  +ed: {Bool.and(U32.is_ge(cp, 48), U32.is_le(cp, 57)) == dd : Bool},
  +el: {Bool.and(U32.is_ge(cp, 97), U32.is_le(cp, 102)) == ll : Bool},
  +eu: {Bool.and(U32.is_ge(cp, 65), U32.is_le(cp, 70)) == uu : Bool},
  +h: {D1.abnf.radix_digit(rx, Chr{cp}) == True{} : Bool},
  p0: n1.rd.Q(P, rx, '0'),
  p1: n1.rd.Q(P, rx, '1'),
  p2: n1.rd.Q(P, rx, '2'),
  p3: n1.rd.Q(P, rx, '3'),
  p4: n1.rd.Q(P, rx, '4'),
  p5: n1.rd.Q(P, rx, '5'),
  p6: n1.rd.Q(P, rx, '6'),
  p7: n1.rd.Q(P, rx, '7'),
  p8: n1.rd.Q(P, rx, '8'),
  p9: n1.rd.Q(P, rx, '9'),
  pa: n1.rd.Q(P, rx, 'a'),
  pb: n1.rd.Q(P, rx, 'b'),
  pc: n1.rd.Q(P, rx, 'c'),
  pd: n1.rd.Q(P, rx, 'd'),
  pe: n1.rd.Q(P, rx, 'e'),
  pf: n1.rd.Q(P, rx, 'f'),
  pA: n1.rd.Q(P, rx, 'A'),
  pB: n1.rd.Q(P, rx, 'B'),
  pC: n1.rd.Q(P, rx, 'C'),
  pD: n1.rd.Q(P, rx, 'D'),
  pE: n1.rd.Q(P, rx, 'E'),
  pF: n1.rd.Q(P, rx, 'F')
) -> P(Chr{cp}):
  match dd:
    case True{}:
      M6.dg.elim(zz => n1.rd.Q(P, rx, zz), Chr{cp}, ed, p0, p1, p2, p3, p4, p5, p6, p7, p8, p9)(h)
    case False{}:
      match ll:
        case True{}:
          lw.elim(zz => n1.rd.Q(P, rx, zz), Chr{cp}, el, pa, pb, pc, pd, pe, pf)(h)
        case False{}:
          match uu:
            case True{}:
              up.elim(zz => n1.rd.Q(P, rx, zz), Chr{cp}, eu, pA, pB, pC, pD, pE, pF)(h)
            case False{}:
              Eq.bit.absurd(&1, P(Chr{cp}), Equal.trans(Bool, False{}, T.dig.ok(99, n1.rb(rx)), True{},
                Equal.sym(Bool, T.dig.ok(99, n1.rb(rx)), False{}, n1.no99(rx)), Equal.trans(Bool,
                T.dig.ok(99, n1.rb(rx)), D1.abnf.radix_digit(rx, Chr{cp}), True{}, n1.cls.none.go(rx, cp, ed, el,
                eu), h)))

# a claim made of each of the 22 characters, under its being a digit of the
# radix, is made of every digit of the radix
def n1.rd.elim(
  -P: Char -> Type,
  +rx: D1.ARadix,
  cc: Char,
  +h: {D1.abnf.radix_digit(rx, cc) == True{} : Bool},
  p0: n1.rd.Q(P, rx, '0'),
  p1: n1.rd.Q(P, rx, '1'),
  p2: n1.rd.Q(P, rx, '2'),
  p3: n1.rd.Q(P, rx, '3'),
  p4: n1.rd.Q(P, rx, '4'),
  p5: n1.rd.Q(P, rx, '5'),
  p6: n1.rd.Q(P, rx, '6'),
  p7: n1.rd.Q(P, rx, '7'),
  p8: n1.rd.Q(P, rx, '8'),
  p9: n1.rd.Q(P, rx, '9'),
  pa: n1.rd.Q(P, rx, 'a'),
  pb: n1.rd.Q(P, rx, 'b'),
  pc: n1.rd.Q(P, rx, 'c'),
  pd: n1.rd.Q(P, rx, 'd'),
  pe: n1.rd.Q(P, rx, 'e'),
  pf: n1.rd.Q(P, rx, 'f'),
  pA: n1.rd.Q(P, rx, 'A'),
  pB: n1.rd.Q(P, rx, 'B'),
  pC: n1.rd.Q(P, rx, 'C'),
  pD: n1.rd.Q(P, rx, 'D'),
  pE: n1.rd.Q(P, rx, 'E'),
  pF: n1.rd.Q(P, rx, 'F')
) -> P(cc):
  match cc:
    case Chr{+cp}:
      n1.rd.go(Bool.and(U32.is_ge(cp, 48), U32.is_le(cp, 57)), Bool.and(U32.is_ge(cp, 97), U32.is_le(cp, 102)),
        Bool.and(U32.is_ge(cp, 65), U32.is_le(cp, 70)), P, rx, cp, {==}, {==}, {==}, h, p0, p1, p2, p3, p4, p5, p6,
        p7, p8, p9, pa, pb, pc, pd, pe, pf, pA, pB, pC, pD, pE, pF)

# the scan's value of a digit of the radix is the grammar's
def n1.dv(
  +rx: D1.ARadix,
  cc: Char,
  +h: {D1.abnf.radix_digit(rx, cc) == True{} : Bool}
) -> {U32.to_nat(T.dig.val(cc)) == D1.g.hexdig.val(cc) : Nat}:
  n1.rd.elim(zz => {U32.to_nat(T.dig.val(zz)) == D1.g.hexdig.val(zz) : Nat}, rx, cc, h,
    _h => {==}, _h => {==}, _h => {==}, _h => {==}, _h => {==}, _h => {==}, _h => {==}, _h => {==}, _h => {==},
    _h => {==}, _h => {==}, _h => {==}, _h => {==}, _h => {==}, _h => {==}, _h => {==}, _h => {==}, _h => {==},
    _h => {==}, _h => {==}, _h => {==}, _h => {==})

# a digit of the radix other than 0 is worth more than 0
def n1.d0(
  +rx: D1.ARadix,
  cc: Char,
  +h: {D1.abnf.radix_digit(rx, cc) == True{} : Bool},
  +hz: {D1.abnf.cp(cc, 48) == False{} : Bool}
) -> {Nat.is_lt(0n, D1.g.hexdig.val(cc)) == True{} : Bool}:
  n1.rd.elim(zz => {D1.abnf.cp(zz, 48) == False{} : Bool} -> {Nat.is_lt(0n, D1.g.hexdig.val(zz)) == True{}
    : Bool}, rx, cc, h,
    _h => ee => Eq.bit.absurd2(&2, {Nat.is_lt(0n, D1.g.hexdig.val('0')) == True{} : Bool}, ee),
    _h => _e => {==}, _h => _e => {==}, _h => _e => {==}, _h => _e => {==}, _h => _e => {==}, _h => _e => {==},
    _h => _e => {==}, _h => _e => {==}, _h => _e => {==}, _h => _e => {==}, _h => _e => {==}, _h => _e => {==},
    _h => _e => {==}, _h => _e => {==}, _h => _e => {==}, _h => _e => {==}, _h => _e => {==}, _h => _e => {==},
    _h => _e => {==}, _h => _e => {==}, _h => _e => {==})(hz)

# a hexadecimal digit is from 0 to 7 exactly when it is worth less than 8
def n1.d07(
  cc: Char,
  +h: {D1.abnf.radix_digit(D1.AHex{}, cc) == True{} : Bool}
) -> {D1.abnf.digit0_7(cc) == Nat.is_lt(D1.g.hexdig.val(cc), 8n) : Bool}:
  n1.rd.elim(zz => {D1.abnf.digit0_7(zz) == Nat.is_lt(D1.g.hexdig.val(zz), 8n) : Bool}, D1.AHex{}, cc, h,
    _h => {==}, _h => {==}, _h => {==}, _h => {==}, _h => {==}, _h => {==}, _h => {==}, _h => {==}, _h => {==},
    _h => {==}, _h => {==}, _h => {==}, _h => {==}, _h => {==}, _h => {==}, _h => {==}, _h => {==}, _h => {==},
    _h => {==}, _h => {==}, _h => {==}, _h => {==})

# a digit of the radix is worth less than the radix
def n1.dlr(
  +rx: D1.ARadix,
  +cc: Char,
  +h: {D1.abnf.radix_digit(rx, cc) == True{} : Bool}
) -> {Nat.is_lt(D1.g.hexdig.val(cc), U32.to_nat(n1.rb(rx))) == True{} : Bool}:
  %n1.dv(rx, cc, h) :
    {Nat.is_lt(_, U32.to_nat(n1.rb(rx))) == True{} : Bool}
  Equal.trans(Bool, Nat.is_lt(U32.to_nat(T.dig.val(cc)), U32.to_nat(n1.rb(rx))), U32.is_lt(T.dig.val(cc), n1.rb(rx)),
    True{}, Equal.sym(Bool, U32.is_lt(T.dig.val(cc), n1.rb(rx)), Nat.is_lt(U32.to_nat(T.dig.val(cc)),
    U32.to_nat(n1.rb(rx))), M2.u.lt(T.dig.val(cc), n1.rb(rx))), Equal.trans(Bool, T.dig.ok(T.dig.val(cc), n1.rb(rx)),
    D1.abnf.radix_digit(rx, cc), True{}, n1.cls(rx, cc), h))

# Decimal digits and their value. Of two numerals of decimal digits with no
# leading zero, i64.step's walk over the characters compares their values,
# and str.eq's walk finds them equal exactly when their values are.

# a numeral's value in base 10
def n1.h10(ss: String) -> Nat:
  D1.g.num.nat(String.to_list(ss), 10n, 0n)

# a DIGIT is no underscore
def n1.dg.nu(
  +cc: Char,
  +hd: {D1.abnf.DIGIT(cc) == True{} : Bool}
) -> {Bool.not(D1.abnf.underscore(cc)) == True{} : Bool}:
  %Equal.sym(Bool, D1.abnf.underscore(cc), False{}, M4.gs.nous(cc, M4.gs.dig(cc, hd))) : {Bool.not(_) == True{} : Bool}
  {==}

# a DIGIT is worth less than 10
def n1.dg.lt(
  +cc: Char,
  +hd: {D1.abnf.DIGIT(cc) == True{} : Bool}
) -> {Nat.is_lt(D1.g.hexdig.val(cc), 10n) == True{} : Bool}:
  M6.dg.elim(zz => {Nat.is_lt(D1.g.hexdig.val(zz), 10n) == True{} : Bool}, cc, M4.gs.dig(cc, hd), {==}, {==}, {==},
      {==},
    {==}, {==}, {==}, {==}, {==}, {==})

# a DIGIT's value and 48 is its code point
def n1.v48(
  +cc: Char,
  +hd: {D1.abnf.DIGIT(cc) == True{} : Bool}
) -> {Nat.add(48n, D1.g.hexdig.val(cc)) == U32.to_nat(Char.to_u32(cc)) : Nat}:
  M6.dg.elim(zz => {Nat.add(48n, D1.g.hexdig.val(zz)) == U32.to_nat(Char.to_u32(zz)) : Nat}, cc, M4.gs.dig(cc, hd),
      {==},
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# DIGITs compare by code point as their values compare
def n1.dcmp(
  +xx: Char,
  +yy: Char,
  +hx: {D1.abnf.DIGIT(xx) == True{} : Bool},
  +hy: {D1.abnf.DIGIT(yy) == True{} : Bool}
) -> {U32.cmp(Char.to_u32(xx), Char.to_u32(yy)) == Nat.cmp(D1.g.hexdig.val(xx), D1.g.hexdig.val(yy)) : Cmp}:
  %Equal.sym(Cmp, U32.cmp(Char.to_u32(xx), Char.to_u32(yy)), Nat.cmp(U32.to_nat(Char.to_u32(xx)),
    U32.to_nat(Char.to_u32(yy))), Ar.u_cmp(Char.to_u32(xx), Char.to_u32(yy))) : {_ == Nat.cmp(D1.g.hexdig.val(xx),
    D1.g.hexdig.val(yy)) : Cmp}
  %n1.v48(xx, hx) : {Nat.cmp(_, U32.to_nat(Char.to_u32(yy))) == Nat.cmp(D1.g.hexdig.val(xx),
    D1.g.hexdig.val(yy)) : Cmp}
  %n1.v48(yy, hy) : {Nat.cmp(Nat.add(48n, D1.g.hexdig.val(xx)), _) == Nat.cmp(D1.g.hexdig.val(xx),
    D1.g.hexdig.val(yy)) : Cmp}
  n1.cmp.add(48n, D1.g.hexdig.val(xx), D1.g.hexdig.val(yy))

# two characters are equal as their code points compare equal
def n1.ceq(
  +xx: Char,
  +yy: Char
) -> {Char.is_eq(xx, yy) == Cmp.is_eq(U32.cmp(Char.to_u32(xx), Char.to_u32(yy))) : Bool}:
  match xx yy:
    case Chr{_x} Chr{_y}:
      {==}

# every character a DIGIT: none an underscore
def n1.all.nou(
  ss: String,
  +hs: {D1.g.dec.all(ss) == True{} : Bool}
) -> {n1.nou(String.to_list(ss)) == True{} : Bool}:
  match ss:
    case SNil{}:
      {==}
    case SCon{+hh, +tt}:
      M9.and.tt(Bool.not(D1.abnf.underscore(hh)), n1.nou(String.to_list(tt)), n1.dg.nu(hh, Eq.and.left(
        D1.abnf.DIGIT(hh), D1.g.dec.all(tt), hs)), n1.all.nou(tt, Eq.and.right(D1.abnf.DIGIT(hh),
        D1.g.dec.all(tt), hs)))

# and each worth less than 10
def n1.all.dlt(
  ss: String,
  +hs: {D1.g.dec.all(ss) == True{} : Bool}
) -> {n1.dlt(String.to_list(ss), 10n) == True{} : Bool}:
  match ss:
    case SNil{}:
      {==}
    case SCon{+hh, +tt}:
      M9.and.tt(Nat.is_lt(D1.g.hexdig.val(hh), 10n), n1.dlt(String.to_list(tt), 10n), n1.dg.lt(hh, Eq.and.left(
        D1.abnf.DIGIT(hh), D1.g.dec.all(tt), hs)), n1.all.dlt(tt, Eq.and.right(D1.abnf.DIGIT(hh),
        D1.g.dec.all(tt), hs)))

# i64.ord groups either way
def n1.oa(
  aa: Cmp,
  +bb: Cmp,
  +cc: Cmp
) -> {T.i64.ord(T.i64.ord(aa, bb), cc) == T.i64.ord(aa, T.i64.ord(bb, cc)) : Cmp}:
  match aa:
    case EQ{}:
      {==}
    case LT{}:
      {==}
    case GT{}:
      {==}

# whether two strings have one length
def n1.samel(aa: String, bb: String) -> Bool:
  match aa bb:
    case SNil{} SNil{}:
      True{}
    case SCon{_x, xt} SCon{_y, yt}:
      n1.samel(xt, yt)
    case _a _b:
      False{}

# the length of a string's characters
def n1.len(ss: String) -> Nat:
  List.length(&2, Char, String.to_list(ss))

# strings of one length have characters of one length
def n1.samel.len(
  aa: String,
  bb: String,
  +hl: {n1.samel(aa, bb) == True{} : Bool}
) -> {n1.len(aa) == n1.len(bb) : Nat}:
  match aa bb:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{_y, _yt}:
      Eq.bit.absurd(&2, {n1.len(SNil{}) == n1.len(SCon{_y, _yt}) : Nat}, hl)
    case SCon{_x, _xt} SNil{}:
      Eq.bit.absurd(&2, {n1.len(SCon{_x, _xt}) == n1.len(SNil{}) : Nat}, hl)
    case SCon{_x, +xt} SCon{_y, +yt}:
      Equal.cong(Nat, Nat, nn => 1n+nn, n1.len(xt), n1.len(yt), n1.samel.len(xt, yt, hl))

# and strings whose lengths compare equal have one length
def n1.samel.of(
  aa: String,
  bb: String,
  +hl: {Nat.cmp(n1.len(aa), n1.len(bb)) == EQ{} : Cmp}
) -> {n1.samel(aa, bb) == True{} : Bool}:
  match aa bb:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{_y, _yt}:
      Eq.bit.absurd(&2, {n1.samel(SNil{}, SCon{_y, _yt}) == True{} : Bool}, Equal.cong(Cmp, Bool,
        cc => Cmp.is_eq(cc), Nat.cmp(n1.len(SNil{}), n1.len(SCon{_y, _yt})), EQ{}, hl))
    case SCon{_x, _xt} SNil{}:
      Eq.bit.absurd(&2, {n1.samel(SCon{_x, _xt}, SNil{}) == True{} : Bool}, Equal.cong(Cmp, Bool,
        cc => Cmp.is_eq(cc), Nat.cmp(n1.len(SCon{_x, _xt}), n1.len(SNil{})), EQ{}, hl))
    case SCon{_x, +xt} SCon{_y, +yt}:
      n1.samel.of(xt, yt, hl)

# a DIGIT in front is its value times ten to the rest's length, and the
# rest's value
def n1.hcons(
  +xx: Char,
  +xt: String,
  +hx: {D1.abnf.DIGIT(xx) == True{} : Bool},
  +ht: {D1.g.dec.all(xt) == True{} : Bool}
) -> {n1.h10(SCon{xx, xt}) == Nat.add(Nat.mul(D1.g.hexdig.val(xx), Nat.pow(10n, n1.len(xt))), n1.h10(xt)) : Nat}:
  Equal.trans(Nat, n1.h10(SCon{xx, xt}), D1.g.num.nat(String.to_list(xt), 10n, D1.g.hexdig.val(xx)),
    Nat.add(Nat.mul(D1.g.hexdig.val(xx), Nat.pow(10n, n1.len(xt))), n1.h10(xt)), n1.gn.step(xx,
    String.to_list(xt), 10n, 0n, n1.dg.nu(xx, hx)), n1.hl(String.to_list(xt), 10n, D1.g.hexdig.val(xx),
    n1.all.nou(xt, ht)))

# DIGITs are worth less than ten to their number
def n1.hb10(
  +ss: String,
  +hs: {D1.g.dec.all(ss) == True{} : Bool}
) -> {Nat.is_lt(n1.h10(ss), Nat.pow(10n, n1.len(ss))) == True{} : Bool}:
  n1.hb(String.to_list(ss), 10n, n1.all.nou(ss, hs), n1.all.dlt(ss, hs))

# of two strings of DIGITs of one length, i64.step's walk from an order
# already seen finishes as that order, and then their values' order, allows
def n1.lex(
  aa: String,
  bb: String,
  +oo: Cmp,
  +ha: {D1.g.dec.all(aa) == True{} : Bool},
  +hb: {D1.g.dec.all(bb) == True{} : Bool},
  +hl: {n1.samel(aa, bb) == True{} : Bool}
) -> {T.i64.step(aa, bb, oo) == Cmp.is_le(T.i64.ord(oo, Nat.cmp(n1.h10(aa), n1.h10(bb)))) : Bool}:
  match aa bb:
    case SNil{} SNil{}:
      match oo:
        case EQ{}:
          {==}
        case LT{}:
          {==}
        case GT{}:
          {==}
    case SNil{} SCon{_y, _yt}:
      Eq.bit.absurd(&2, {T.i64.step(SNil{}, SCon{_y, _yt}, oo) == Cmp.is_le(T.i64.ord(oo, Nat.cmp(n1.h10(SNil{}),
        n1.h10(SCon{_y, _yt})))) : Bool}, hl)
    case SCon{_x, _xt} SNil{}:
      Eq.bit.absurd(&2, {T.i64.step(SCon{_x, _xt}, SNil{}, oo) == Cmp.is_le(T.i64.ord(oo, Nat.cmp(n1.h10(SCon{_x,
        _xt}), n1.h10(SNil{})))) : Bool}, hl)
    case SCon{+xx, +xt} SCon{+yy, +yt}:
      +hx = {Eq.and.left(D1.abnf.DIGIT(xx), D1.g.dec.all(xt), ha) : {D1.abnf.DIGIT(xx) == True{} : Bool}}
      +hxt = {Eq.and.right(D1.abnf.DIGIT(xx), D1.g.dec.all(xt), ha) : {D1.g.dec.all(xt) == True{} : Bool}}
      +hy = {Eq.and.left(D1.abnf.DIGIT(yy), D1.g.dec.all(yt), hb) : {D1.abnf.DIGIT(yy) == True{} : Bool}}
      +hyt = {Eq.and.right(D1.abnf.DIGIT(yy), D1.g.dec.all(yt), hb) : {D1.g.dec.all(yt) == True{} : Bool}}
      +vx = D1.g.hexdig.val(xx)
      +vy = D1.g.hexdig.val(yy)
      +pp = Nat.pow(10n, n1.len(xt))
      +el = {Equal.cong(Nat, Nat, nn => Nat.pow(10n, nn), n1.len(xt), n1.len(yt), n1.samel.len(xt, yt, hl))
        : {pp == Nat.pow(10n, n1.len(yt)) : Nat}}
      +hty = {Equal.trans(Bool, Nat.is_lt(n1.h10(yt), pp), Nat.is_lt(n1.h10(yt), Nat.pow(10n, n1.len(yt))), True{},
        Equal.cong(Nat, Bool, nn => Nat.is_lt(n1.h10(yt), nn), pp, Nat.pow(10n, n1.len(yt)), el), n1.hb10(yt, hyt))
        : {Nat.is_lt(n1.h10(yt), pp) == True{} : Bool}}
      %Equal.sym(Nat, n1.h10(SCon{xx, xt}), Nat.add(Nat.mul(vx, pp), n1.h10(xt)), n1.hcons(xx, xt, hx, hxt)) :
        {T.i64.step(SCon{xx, xt}, SCon{yy, yt}, oo) == Cmp.is_le(T.i64.ord(oo, Nat.cmp(_, n1.h10(SCon{yy, yt}))))
        : Bool}
      %Equal.sym(Nat, n1.h10(SCon{yy, yt}), Nat.add(Nat.mul(vy, Nat.pow(10n, n1.len(yt))), n1.h10(yt)),
        n1.hcons(yy, yt, hy, hyt)) : {T.i64.step(SCon{xx, xt}, SCon{yy, yt}, oo) == Cmp.is_le(T.i64.ord(oo,
        Nat.cmp(Nat.add(Nat.mul(vx, pp), n1.h10(xt)), _))) : Bool}
      %el : {T.i64.step(SCon{xx, xt}, SCon{yy, yt}, oo) == Cmp.is_le(T.i64.ord(oo, Nat.cmp(Nat.add(Nat.mul(vx, pp),
        n1.h10(xt)), Nat.add(Nat.mul(vy, _), n1.h10(yt))))) : Bool}
      %Equal.sym(Cmp, Nat.cmp(Nat.add(Nat.mul(vx, pp), n1.h10(xt)), Nat.add(Nat.mul(vy, pp), n1.h10(yt))),
        T.i64.ord(Nat.cmp(vx, vy), Nat.cmp(n1.h10(xt), n1.h10(yt))), n1.ka(vx, vy, pp, n1.h10(xt), n1.h10(yt),
        n1.hb10(xt, hxt), hty)) : {T.i64.step(SCon{xx, xt}, SCon{yy, yt}, oo) == Cmp.is_le(T.i64.ord(oo, _)) : Bool}
      %n1.oa(oo, Nat.cmp(vx, vy), Nat.cmp(n1.h10(xt), n1.h10(yt))) : {T.i64.step(SCon{xx, xt}, SCon{yy, yt}, oo)
        == Cmp.is_le(_) : Bool}
      %Equal.sym(Cmp, U32.cmp(Char.to_u32(xx), Char.to_u32(yy)), Nat.cmp(vx, vy), n1.dcmp(xx, yy, hx, hy)) :
        {T.i64.step(xt, yt, T.i64.ord(oo, _)) == Cmp.is_le(T.i64.ord(T.i64.ord(oo, Nat.cmp(vx, vy)),
        Nat.cmp(n1.h10(xt), n1.h10(yt)))) : Bool}
      n1.lex(xt, yt, T.i64.ord(oo, Nat.cmp(vx, vy)), hxt, hyt, hl)

# a string shorter than the limit fits, whatever came before
def n1.st.lt(
  aa: String,
  bb: String,
  +oo: Cmp,
  +hl: {Nat.is_lt(n1.len(aa), n1.len(bb)) == True{} : Bool}
) -> {T.i64.step(aa, bb, oo) == True{} : Bool}:
  match aa bb:
    case SNil{} SNil{}:
      Eq.bit.absurd(&2, {T.i64.step(SNil{}, SNil{}, oo) == True{} : Bool}, hl)
    case SNil{} SCon{_y, _yt}:
      {==}
    case SCon{_x, _xt} SNil{}:
      Eq.bit.absurd(&2, {T.i64.step(SCon{_x, _xt}, SNil{}, oo) == True{} : Bool}, hl)
    case SCon{+xx, +xt} SCon{+yy, +yt}:
      n1.st.lt(xt, yt, T.i64.ord(oo, U32.cmp(Char.to_u32(xx), Char.to_u32(yy))), hl)

# and a longer one does not
def n1.st.gt(
  aa: String,
  bb: String,
  +oo: Cmp,
  +hl: {Nat.is_lt(n1.len(bb), n1.len(aa)) == True{} : Bool}
) -> {T.i64.step(aa, bb, oo) == False{} : Bool}:
  match aa bb:
    case SNil{} SNil{}:
      Eq.bit.absurd(&2, {T.i64.step(SNil{}, SNil{}, oo) == False{} : Bool}, hl)
    case SNil{} SCon{_y, _yt}:
      Eq.bit.absurd(&2, {T.i64.step(SNil{}, SCon{_y, _yt}, oo) == False{} : Bool}, hl)
    case SCon{_x, _xt} SNil{}:
      {==}
    case SCon{+xx, +xt} SCon{+yy, +yt}:
      n1.st.gt(xt, yt, T.i64.ord(oo, U32.cmp(Char.to_u32(xx), Char.to_u32(yy))), hl)

# at most b is not more than b
def n1.le.nlt(aa: Nat, bb: Nat, +hh: {Nat.is_le(aa, bb) == True{} : Bool}) -> {Nat.is_lt(bb, aa) == False{} : Bool}:
  match aa bb:
    case 0n _b:
      M2.nlt.zero(_b)
    case 1n+(+a1) 0n:
      Eq.bit.absurd(&2, {Nat.is_lt(0n, 1n+a1) == False{} : Bool}, hh)
    case 1n+(+a1) 1n+(+b1):
      n1.le.nlt(a1, b1, hh)

# below is at most
def n1.lt.lte(aa: Nat, bb: Nat, +hh: {Nat.is_lt(aa, bb) == True{} : Bool}) -> {Nat.is_le(aa, bb) == True{} : Bool}:
  match aa bb:
    case 0n _b:
      n1.le0(_b)
    case 1n+(+a1) 0n:
      Eq.bit.absurd(&2, {Nat.is_le(1n+a1, 0n) == True{} : Bool}, hh)
    case 1n+(+a1) 1n+(+b1):
      n1.lt.lte(a1, b1, hh)

# below b is not at least b
def n1.lt.nle(aa: Nat, bb: Nat, +hh: {Nat.is_lt(aa, bb) == True{} : Bool}) -> {Nat.is_le(bb, aa) == False{} : Bool}:
  match aa bb:
    case _a 0n:
      Eq.bit.absurd(&2, {Nat.is_le(0n, _a) == False{} : Bool}, Equal.trans(Bool, False{}, Nat.is_lt(_a, 0n), True{},
        Equal.sym(Bool, Nat.is_lt(_a, 0n), False{}, M2.nlt.zero(_a)), hh))
    case 0n 1n+_b:
      {==}
    case 1n+(+a1) 1n+(+b1):
      n1.lt.nle(a1, b1, hh)

# below b is not b
def n1.lt.ne(aa: Nat, bb: Nat, +hh: {Nat.is_lt(aa, bb) == True{} : Bool}) -> {Nat.is_eq(aa, bb) == False{} : Bool}:
  match aa bb:
    case _a 0n:
      Eq.bit.absurd(&2, {Nat.is_eq(_a, 0n) == False{} : Bool}, Equal.trans(Bool, False{}, Nat.is_lt(_a, 0n), True{},
        Equal.sym(Bool, Nat.is_lt(_a, 0n), False{}, M2.nlt.zero(_a)), hh))
    case 0n 1n+_b:
      {==}
    case 1n+(+a1) 1n+(+b1):
      n1.lt.ne(a1, b1, hh)

# above b is not b
def n1.gt.ne(aa: Nat, bb: Nat, +hh: {Nat.is_lt(bb, aa) == True{} : Bool}) -> {Nat.is_eq(aa, bb) == False{} : Bool}:
  match aa bb:
    case 0n _b:
      Eq.bit.absurd(&2, {Nat.is_eq(0n, _b) == False{} : Bool}, Equal.trans(Bool, False{}, Nat.is_lt(_b, 0n), True{},
        Equal.sym(Bool, Nat.is_lt(_b, 0n), False{}, M2.nlt.zero(_b)), hh))
    case 1n+_a 0n:
      {==}
    case 1n+(+a1) 1n+(+b1):
      n1.gt.ne(a1, b1, hh)

# a comparison GT is the other way below
def n1.gt.lt(aa: Nat, bb: Nat, +hh: {Nat.cmp(aa, bb) == GT{} : Cmp}) -> {Nat.is_lt(bb, aa) == True{} : Bool}:
  match aa bb:
    case 0n 0n:
      Eq.bit.absurd(&2, {Nat.is_lt(0n, 0n) == True{} : Bool}, Equal.cong(Cmp, Bool, cc => Cmp.is_gt(cc), EQ{}, GT{},
        hh))
    case 0n 1n+_b:
      Eq.bit.absurd(&2, {Nat.is_lt(1n+_b, 0n) == True{} : Bool}, Equal.cong(Cmp, Bool, cc => Cmp.is_gt(cc), LT{},
        GT{}, hh))
    case 1n+_a 0n:
      {==}
    case 1n+(+a1) 1n+(+b1):
      n1.gt.lt(a1, b1, hh)

# a power grows with its exponent
def n1.pw.mono(
  +rr: Nat,
  +aa: Nat,
  +bb: Nat,
  +hr: {Nat.is_lt(0n, rr) == True{} : Bool},
  +hh: {Nat.is_le(aa, bb) == True{} : Bool}
) -> {Nat.is_le(Nat.pow(rr, aa), Nat.pow(rr, bb)) == True{} : Bool}:
  %Ar.nat_ge_ex(bb, aa, n1.le.nlt(aa, bb, hh)) : {Nat.is_le(Nat.pow(rr, aa), Nat.pow(rr, _)) == True{} : Bool}
  n1.pw.le(rr, aa, Nat.sub(bb, aa), hr)

# of `and(a, false)` or b, b
def n1.oaf(aa: Bool, +bb: Bool, +hh: {Bool.or(Bool.and(aa, False{}), bb) == True{} : Bool}) -> {bb == True{} : Bool}:
  match aa:
    case True{}:
      hh
    case False{}:
      hh

# the type of n1.canon.tl's ho
def n1.canon.tl.P1(+hh: Char, +tt: String) -> Type:
  {Bool.or(Bool.and(D1.abnf.cp(hh, 48), String.is_empty(tt)), Bool.and(D1.abnf.digit1_9(hh),
    D1.g.dec.all(tt))) == True{} : Bool}

# after the first character of a canonical numeral, only DIGITs
def n1.canon.tl(
  +hh: Char,
  tt: String,
  ho: n1.canon.tl.P1(hh, tt)
) -> {D1.g.dec.all(tt) == True{} : Bool}:
  match tt:
    case SNil{}:
      {==}
    case SCon{+t1, +ts}:
      Eq.and.right(D1.abnf.digit1_9(hh), D1.g.dec.all(SCon{t1, ts}), n1.oaf(D1.abnf.cp(hh, 48),
        Bool.and(D1.abnf.digit1_9(hh), D1.g.dec.all(SCon{t1, ts})), ho))

# a canonical numeral is DIGITs
def n1.canon.all(ss: String, +hs: {D1.g.dec.canon(ss) == True{} : Bool}) -> {D1.g.dec.all(ss) == True{} : Bool}:
  match ss:
    case SNil{}:
      Eq.bit.absurd(&2, {D1.g.dec.all(SNil{}) == True{} : Bool}, hs)
    case SCon{+hh, +tt}:
      M9.and.tt(D1.abnf.DIGIT(hh), D1.g.dec.all(tt), Eq.and.left(D1.abnf.DIGIT(hh), Bool.or(Bool.and(
        D1.abnf.cp(hh, 48), String.is_empty(tt)), Bool.and(D1.abnf.digit1_9(hh), D1.g.dec.all(tt))), hs),
        n1.canon.tl(hh, tt, Eq.and.right(D1.abnf.DIGIT(hh), Bool.or(Bool.and(D1.abnf.cp(hh, 48),
        String.is_empty(tt)), Bool.and(D1.abnf.digit1_9(hh), D1.g.dec.all(tt))), hs)))

# a canonical numeral of two characters or more starts with a digit1-9
def n1.canon.d19(
  +hh: Char,
  +t1: Char,
  +ts: String,
  +hs: {D1.g.dec.canon(SCon{hh, SCon{t1, ts}}) == True{} : Bool}
) -> {D1.abnf.digit1_9(hh) == True{} : Bool}:
  Eq.and.left(D1.abnf.digit1_9(hh), D1.g.dec.all(SCon{t1, ts}), n1.oaf(D1.abnf.cp(hh, 48),
    Bool.and(D1.abnf.digit1_9(hh), D1.g.dec.all(SCon{t1, ts})), Eq.and.right(D1.abnf.DIGIT(hh),
    Bool.or(Bool.and(D1.abnf.cp(hh, 48), False{}), Bool.and(D1.abnf.digit1_9(hh), D1.g.dec.all(SCon{t1,
    ts}))), hs)))

# a digit1-9 is worth more than 0
def n1.d19.pos(
  +cc: Char,
  +hd: {D1.abnf.digit1_9(cc) == True{} : Bool}
) -> {Nat.is_lt(0n, D1.g.hexdig.val(cc)) == True{} : Bool}:
  M6.dg.elim(zz => {Char.is_eq(zz, '0') == False{} : Bool} -> {Nat.is_lt(0n, D1.g.hexdig.val(zz)) == True{} : Bool},
    cc, M4.gs.d19(cc, hd), ee => Eq.bit.absurd2(&2, {Nat.is_lt(0n, D1.g.hexdig.val('0')) == True{} : Bool}, ee),
    _e => {==}, _e => {==}, _e => {==}, _e => {==}, _e => {==}, _e => {==}, _e => {==}, _e => {==},
    _e => {==})(gs.d19z(cc, hd))

# of two canonical numerals, the shorter is worth less: the longer starts
# with a digit1-9 and has at least as many after it as the shorter has
def n1.short.go(
  +ah: Char,
  +at: String,
  +bh: Char,
  bt: String,
  +ha: {D1.g.dec.canon(SCon{ah, at}) == True{} : Bool},
  +hb: {D1.g.dec.canon(SCon{bh, bt}) == True{} : Bool},
  +hl: {Nat.is_lt(n1.len(at), n1.len(bt)) == True{} : Bool}
) -> {Nat.is_lt(n1.h10(SCon{ah, at}), n1.h10(SCon{bh, bt})) == True{} : Bool}:
  match bt:
    case SNil{}:
      Eq.bit.absurd(&2, {Nat.is_lt(n1.h10(SCon{ah, at}), n1.h10(SCon{bh, SNil{}})) == True{} : Bool},
        Equal.trans(Bool, False{}, Nat.is_lt(n1.len(at), 0n), True{}, Equal.sym(Bool, Nat.is_lt(n1.len(at), 0n),
        False{}, M2.nlt.zero(n1.len(at))), hl))
    case SCon{+b1, +bs}:
      n1.lt.le(n1.h10(SCon{ah, at}), Nat.pow(10n, n1.len(SCon{ah, at})), n1.h10(SCon{bh, SCon{b1, bs}}),
        n1.hb10(SCon{ah, at}, n1.canon.all(SCon{ah, at}, ha)), n1.le.trans(Nat.pow(10n, n1.len(SCon{ah, at})),
        Nat.pow(10n, n1.len(SCon{b1, bs})), n1.h10(SCon{bh, SCon{b1, bs}}), n1.pw.mono(10n, n1.len(SCon{ah, at}),
        n1.len(SCon{b1, bs}), {==}, n1.lt.suc(n1.len(at), n1.len(SCon{b1, bs}), hl)), n1.low(bh,
        String.to_list(SCon{b1, bs}), 10n, n1.all.nou(SCon{bh, SCon{b1, bs}}, n1.canon.all(SCon{bh, SCon{b1, bs}},
        hb)), n1.d19.pos(bh, n1.canon.d19(bh, b1, bs, hb)))))

# of two canonical numerals, the shorter is worth less
def n1.short(
  aa: String,
  bb: String,
  +ha: {D1.g.dec.canon(aa) == True{} : Bool},
  +hb: {D1.g.dec.canon(bb) == True{} : Bool},
  +hl: {Nat.is_lt(n1.len(aa), n1.len(bb)) == True{} : Bool}
) -> {Nat.is_lt(n1.h10(aa), n1.h10(bb)) == True{} : Bool}:
  match aa bb:
    case SNil{} _b:
      Eq.bit.absurd(&2, {Nat.is_lt(n1.h10(SNil{}), n1.h10(_b)) == True{} : Bool}, ha)
    case SCon{+ah, +at} SNil{}:
      Eq.bit.absurd(&2, {Nat.is_lt(n1.h10(SCon{ah, at}), n1.h10(SNil{})) == True{} : Bool}, hl)
    case SCon{+ah, +at} SCon{+bh, +bt}:
      n1.short.go(ah, at, bh, bt, ha, hb, hl)

# i64.step against a canonical limit, by how the lengths compare: a shorter
# numeral fits and is worth less, a longer one does not and is worth more,
# and one of the same length compares its digits
def n1.fh.go(
  cc: Cmp,
  +dd: String,
  +ll: String,
  +ec: {Nat.cmp(n1.len(dd), n1.len(ll)) == cc : Cmp},
  +hd: {D1.g.dec.canon(dd) == True{} : Bool},
  +hl: {D1.g.dec.canon(ll) == True{} : Bool}
) -> {T.i64.step(dd, ll, EQ{}) == Nat.is_le(n1.h10(dd), n1.h10(ll)) : Bool}:
  match cc:
    case LT{}:
      +hs = {Equal.cong(Cmp, Bool, xx => Cmp.is_lt(xx), Nat.cmp(n1.len(dd), n1.len(ll)), LT{}, ec)
        : {Nat.is_lt(n1.len(dd), n1.len(ll)) == True{} : Bool}}
      Equal.trans(Bool, T.i64.step(dd, ll, EQ{}), True{}, Nat.is_le(n1.h10(dd), n1.h10(ll)), n1.st.lt(dd, ll, EQ{},
        hs), Equal.sym(Bool, Nat.is_le(n1.h10(dd), n1.h10(ll)), True{}, n1.lt.lte(n1.h10(dd), n1.h10(ll),
        n1.short(dd, ll, hd, hl, hs))))
    case EQ{}:
      n1.lex(dd, ll, EQ{}, n1.canon.all(dd, hd), n1.canon.all(ll, hl), n1.samel.of(dd, ll, ec))
    case GT{}:
      +hs = {n1.gt.lt(n1.len(dd), n1.len(ll), ec) : {Nat.is_lt(n1.len(ll), n1.len(dd)) == True{} : Bool}}
      Equal.trans(Bool, T.i64.step(dd, ll, EQ{}), False{}, Nat.is_le(n1.h10(dd), n1.h10(ll)), n1.st.gt(dd, ll, EQ{},
        hs), Equal.sym(Bool, Nat.is_le(n1.h10(dd), n1.h10(ll)), False{}, n1.lt.nle(n1.h10(ll), n1.h10(dd),
        n1.short(ll, dd, hl, hd, hs))))

# of two canonical numerals, i64.step's walk allows the first exactly when it
# is worth at most the second
def n1.fh(
  +dd: String,
  +ll: String,
  +hd: {D1.g.dec.canon(dd) == True{} : Bool},
  +hl: {D1.g.dec.canon(ll) == True{} : Bool}
) -> {T.i64.step(dd, ll, EQ{}) == Nat.is_le(n1.h10(dd), n1.h10(ll)) : Bool}:
  n1.fh.go(Nat.cmp(n1.len(dd), n1.len(ll)), dd, ll, {==}, hd, hl)

# after first characters that compare as cc, str.eq's walk goes on exactly
# when cc is EQ, and then answers as the rest's values compare
def n1.seq.c(
  cc: Cmp,
  +xt: String,
  +yt: String,
  +ih: {T.str.eq(xt, yt) == Nat.is_eq(n1.h10(xt), n1.h10(yt)) : Bool}
) -> {T.str.eq.step(xt, yt, Cmp.is_eq(cc)) == Cmp.is_eq(T.i64.ord(cc, Nat.cmp(n1.h10(xt), n1.h10(yt)))) : Bool}:
  match cc:
    case EQ{}:
      ih
    case LT{}:
      M5.str.eq.step.false(xt, yt)
    case GT{}:
      M5.str.eq.step.false(xt, yt)

# two strings of DIGITs of one length are equal exactly when their values are
def n1.seq(
  aa: String,
  bb: String,
  +ha: {D1.g.dec.all(aa) == True{} : Bool},
  +hb: {D1.g.dec.all(bb) == True{} : Bool},
  +hl: {n1.samel(aa, bb) == True{} : Bool}
) -> {T.str.eq(aa, bb) == Nat.is_eq(n1.h10(aa), n1.h10(bb)) : Bool}:
  match aa bb:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{_y, _yt}:
      Eq.bit.absurd(&2, {T.str.eq(SNil{}, SCon{_y, _yt}) == Nat.is_eq(n1.h10(SNil{}), n1.h10(SCon{_y, _yt}))
        : Bool}, hl)
    case SCon{_x, _xt} SNil{}:
      Eq.bit.absurd(&2, {T.str.eq(SCon{_x, _xt}, SNil{}) == Nat.is_eq(n1.h10(SCon{_x, _xt}), n1.h10(SNil{}))
        : Bool}, hl)
    case SCon{+xx, +xt} SCon{+yy, +yt}:
      +hx = {Eq.and.left(D1.abnf.DIGIT(xx), D1.g.dec.all(xt), ha) : {D1.abnf.DIGIT(xx) == True{} : Bool}}
      +hxt = {Eq.and.right(D1.abnf.DIGIT(xx), D1.g.dec.all(xt), ha) : {D1.g.dec.all(xt) == True{} : Bool}}
      +hy = {Eq.and.left(D1.abnf.DIGIT(yy), D1.g.dec.all(yt), hb) : {D1.abnf.DIGIT(yy) == True{} : Bool}}
      +hyt = {Eq.and.right(D1.abnf.DIGIT(yy), D1.g.dec.all(yt), hb) : {D1.g.dec.all(yt) == True{} : Bool}}
      +vx = D1.g.hexdig.val(xx)
      +vy = D1.g.hexdig.val(yy)
      +pp = Nat.pow(10n, n1.len(xt))
      +el = {Equal.cong(Nat, Nat, nn => Nat.pow(10n, nn), n1.len(xt), n1.len(yt), n1.samel.len(xt, yt, hl))
        : {pp == Nat.pow(10n, n1.len(yt)) : Nat}}
      +hty = {Equal.trans(Bool, Nat.is_lt(n1.h10(yt), pp), Nat.is_lt(n1.h10(yt), Nat.pow(10n, n1.len(yt))), True{},
        Equal.cong(Nat, Bool, nn => Nat.is_lt(n1.h10(yt), nn), pp, Nat.pow(10n, n1.len(yt)), el), n1.hb10(yt, hyt))
        : {Nat.is_lt(n1.h10(yt), pp) == True{} : Bool}}
      %Equal.sym(Nat, n1.h10(SCon{xx, xt}), Nat.add(Nat.mul(vx, pp), n1.h10(xt)), n1.hcons(xx, xt, hx, hxt)) :
        {T.str.eq(SCon{xx, xt}, SCon{yy, yt}) == Cmp.is_eq(Nat.cmp(_, n1.h10(SCon{yy, yt}))) : Bool}
      %Equal.sym(Nat, n1.h10(SCon{yy, yt}), Nat.add(Nat.mul(vy, Nat.pow(10n, n1.len(yt))), n1.h10(yt)),
        n1.hcons(yy, yt, hy, hyt)) : {T.str.eq(SCon{xx, xt}, SCon{yy, yt}) == Cmp.is_eq(Nat.cmp(Nat.add(Nat.mul(vx,
        pp), n1.h10(xt)), _)) : Bool}
      %el : {T.str.eq(SCon{xx, xt}, SCon{yy, yt}) == Cmp.is_eq(Nat.cmp(Nat.add(Nat.mul(vx, pp), n1.h10(xt)),
        Nat.add(Nat.mul(vy, _), n1.h10(yt)))) : Bool}
      %Equal.sym(Cmp, Nat.cmp(Nat.add(Nat.mul(vx, pp), n1.h10(xt)), Nat.add(Nat.mul(vy, pp), n1.h10(yt))),
        T.i64.ord(Nat.cmp(vx, vy), Nat.cmp(n1.h10(xt), n1.h10(yt))), n1.ka(vx, vy, pp, n1.h10(xt), n1.h10(yt),
        n1.hb10(xt, hxt), hty)) : {T.str.eq(SCon{xx, xt}, SCon{yy, yt}) == Cmp.is_eq(_) : Bool}
      %Equal.sym(Bool, Char.is_eq(xx, yy), Cmp.is_eq(U32.cmp(Char.to_u32(xx), Char.to_u32(yy))), n1.ceq(xx, yy)) :
        {T.str.eq.step(xt, yt, _) == Cmp.is_eq(T.i64.ord(Nat.cmp(vx, vy), Nat.cmp(n1.h10(xt), n1.h10(yt)))) : Bool}
      %Equal.sym(Cmp, U32.cmp(Char.to_u32(xx), Char.to_u32(yy)), Nat.cmp(vx, vy), n1.dcmp(xx, yy, hx, hy)) :
        {T.str.eq.step(xt, yt, Cmp.is_eq(_)) == Cmp.is_eq(T.i64.ord(Nat.cmp(vx, vy), Nat.cmp(n1.h10(xt),
        n1.h10(yt)))) : Bool}
      n1.seq.c(Nat.cmp(vx, vy), xt, yt, n1.seq(xt, yt, hxt, hyt, hl))

# strings str.eq finds equal have lengths that compare equal
def n1.str.len(
  +aa: String,
  +bb: String,
  +hh: {T.str.eq(aa, bb) == True{} : Bool}
) -> {Nat.cmp(n1.len(aa), n1.len(bb)) == EQ{} : Cmp}:
  %M5.str.eq.true(aa, bb, hh) : {Nat.cmp(n1.len(aa), n1.len(_)) == EQ{} : Cmp}
  M2.ncmp.refl(n1.len(aa))

# strings whose lengths do not compare equal are not equal
def n1.str.nf(
  se: Bool,
  +aa: String,
  +bb: String,
  +es: {T.str.eq(aa, bb) == se : Bool},
  +hn: {Cmp.is_eq(Nat.cmp(n1.len(aa), n1.len(bb))) == False{} : Bool}
) -> {T.str.eq(aa, bb) == False{} : Bool}:
  match se:
    case True{}:
      Eq.bit.absurd2(&2, {T.str.eq(aa, bb) == False{} : Bool}, Equal.trans(Bool, True{},
        Cmp.is_eq(Nat.cmp(n1.len(aa), n1.len(bb))), False{}, Equal.sym(Bool, Cmp.is_eq(Nat.cmp(n1.len(aa),
        n1.len(bb))), True{}, Equal.cong(Cmp, Bool, xx => Cmp.is_eq(xx), Nat.cmp(n1.len(aa), n1.len(bb)), EQ{},
        n1.str.len(aa, bb, es))), hn))
    case False{}:
      es

# of two canonical numerals, by how their lengths compare
def n1.uq.t(
  cc: Cmp,
  +d2: String,
  +dd: String,
  +ec: {Nat.cmp(n1.len(d2), n1.len(dd)) == cc : Cmp},
  +h2: {D1.g.dec.canon(d2) == True{} : Bool},
  +hd: {D1.g.dec.canon(dd) == True{} : Bool}
) -> {T.str.eq(d2, dd) == Nat.is_eq(n1.h10(d2), n1.h10(dd)) : Bool}:
  match cc:
    case LT{}:
      +hs = {Equal.cong(Cmp, Bool, xx => Cmp.is_lt(xx), Nat.cmp(n1.len(d2), n1.len(dd)), LT{}, ec)
        : {Nat.is_lt(n1.len(d2), n1.len(dd)) == True{} : Bool}}
      Equal.trans(Bool, T.str.eq(d2, dd), False{}, Nat.is_eq(n1.h10(d2), n1.h10(dd)), n1.str.nf(T.str.eq(d2, dd),
        d2, dd, {==}, Equal.cong(Cmp, Bool, xx => Cmp.is_eq(xx), Nat.cmp(n1.len(d2), n1.len(dd)), LT{}, ec)),
        Equal.sym(Bool, Nat.is_eq(n1.h10(d2), n1.h10(dd)), False{}, n1.lt.ne(n1.h10(d2), n1.h10(dd), n1.short(d2,
        dd, h2, hd, hs))))
    case EQ{}:
      n1.seq(d2, dd, n1.canon.all(d2, h2), n1.canon.all(dd, hd), n1.samel.of(d2, dd, ec))
    case GT{}:
      +hs = {n1.gt.lt(n1.len(d2), n1.len(dd), ec) : {Nat.is_lt(n1.len(dd), n1.len(d2)) == True{} : Bool}}
      Equal.trans(Bool, T.str.eq(d2, dd), False{}, Nat.is_eq(n1.h10(d2), n1.h10(dd)), n1.str.nf(T.str.eq(d2, dd),
        d2, dd, {==}, Equal.cong(Cmp, Bool, xx => Cmp.is_eq(xx), Nat.cmp(n1.len(d2), n1.len(dd)), GT{}, ec)),
        Equal.sym(Bool, Nat.is_eq(n1.h10(d2), n1.h10(dd)), False{}, n1.gt.ne(n1.h10(d2), n1.h10(dd), n1.short(dd,
        d2, hd, h2, hs))))

# a string that is no canonical numeral is not one that is
def n1.uq.f(
  se: Bool,
  +d2: String,
  +dd: String,
  +es: {T.str.eq(d2, dd) == se : Bool},
  +h2: {D1.g.dec.canon(d2) == False{} : Bool},
  +hd: {D1.g.dec.canon(dd) == True{} : Bool}
) -> {T.str.eq(d2, dd) == False{} : Bool}:
  match se:
    case True{}:
      Eq.bit.absurd(&2, {T.str.eq(d2, dd) == False{} : Bool}, Equal.trans(Bool, False{}, D1.g.dec.canon(d2),
        True{}, Equal.sym(Bool, D1.g.dec.canon(d2), False{}, h2), Equal.trans(Bool, D1.g.dec.canon(d2),
        D1.g.dec.canon(dd), True{}, Equal.cong(String, Bool, ss => D1.g.dec.canon(ss), d2, dd, M5.str.eq.true(d2,
        dd, es)), hd)))
    case False{}:
      es

# by whether the first string is canonical
def n1.uq.go(
  kk: Bool,
  +d2: String,
  +dd: String,
  +ek: {D1.g.dec.canon(d2) == kk : Bool},
  +hd: {D1.g.dec.canon(dd) == True{} : Bool}
) -> {T.str.eq(d2, dd) == Bool.and(D1.g.dec.canon(d2), Nat.is_eq(n1.h10(d2), n1.h10(dd))) : Bool}:
  match kk:
    case True{}:
      %Equal.sym(Bool, D1.g.dec.canon(d2), True{}, ek) : {T.str.eq(d2, dd) == Bool.and(_, Nat.is_eq(n1.h10(d2),
        n1.h10(dd))) : Bool}
      n1.uq.t(Nat.cmp(n1.len(d2), n1.len(dd)), d2, dd, {==}, ek, hd)
    case False{}:
      %Equal.sym(Bool, D1.g.dec.canon(d2), False{}, ek) : {T.str.eq(d2, dd) == Bool.and(_, Nat.is_eq(n1.h10(d2),
        n1.h10(dd))) : Bool}
      n1.uq.f(T.str.eq(d2, dd), d2, dd, {==}, ek, hd)

# a string is a canonical numeral D exactly when it is canonical and worth
# what D is
def n1.uq(
  +d2: String,
  +dd: String,
  +hd: {D1.g.dec.canon(dd) == True{} : Bool}
) -> {String.eq(d2, dd) == Bool.and(D1.g.dec.canon(d2), Nat.is_eq(n1.h10(d2), n1.h10(dd))) : Bool}:
  %M8.str.eq.agree(d2, dd) : {_ == Bool.and(D1.g.dec.canon(d2), Nat.is_eq(n1.h10(d2), n1.h10(dd))) : Bool}
  n1.uq.go(D1.g.dec.canon(d2), d2, dd, {==}, hd)

# The numeral a scan builds: decimal digits as U32s, least-significant
# first. dec.go multiplies it by the radix and adds a digit; dec.text writes
# it as a canonical numeral worth what the digits are.

# appending groups either way
def n1.app.assoc(
  xs: List<&2, U32>,
  +ys: List<&2, U32>,
  +zs: List<&2, U32>
) -> {List.append(&2, U32, List.append(&2, U32, xs, ys), zs) == List.append(&2, U32, xs, List.append(&2, U32, ys, zs))
  : List<&2, U32>}:
  match xs:
    case []:
      {==}
    case +xx <> +xt:
      Equal.cong(List<&2, U32>, List<&2, U32>, ls => xx <> ls, List.append(&2, U32, List.append(&2, U32, xt, ys), zs),
        List.append(&2, U32, xt, List.append(&2, U32, ys, zs)), n1.app.assoc(xt, ys, zs))

# reversing onto a list is reversing, and then the list
def n1.rgo(
  xs: List<&2, U32>,
  +acc: List<&2, U32>
) -> {List.reverse.go(&2, U32, xs, acc) == List.append(&2, U32, List.reverse.go(&2, U32, xs, []), acc)
  : List<&2, U32>}:
  match xs:
    case []:
      {==}
    case +xx <> +xt:
      Equal.trans(List<&2, U32>, List.reverse.go(&2, U32, xt, xx <> acc), List.append(&2, U32, List.reverse.go(&2,
        U32, xt, []), xx <> acc), List.append(&2, U32, List.reverse.go(&2, U32, xt, [xx]), acc), n1.rgo(xt,
        xx <> acc), Equal.sym(List<&2, U32>, List.append(&2, U32, List.reverse.go(&2, U32, xt, [xx]), acc),
        List.append(&2, U32, List.reverse.go(&2, U32, xt, []), xx <> acc), Equal.trans(List<&2, U32>,
        List.append(&2, U32, List.reverse.go(&2, U32, xt, [xx]), acc), List.append(&2, U32, List.append(&2, U32,
        List.reverse.go(&2, U32, xt, []), [xx]), acc), List.append(&2, U32, List.reverse.go(&2, U32, xt, []),
        xx <> acc), Equal.cong(List<&2, U32>, List<&2, U32>, ls => List.append(&2, U32, ls, acc),
        List.reverse.go(&2, U32, xt, [xx]), List.append(&2, U32, List.reverse.go(&2, U32, xt, []), [xx]),
        n1.rgo(xt, [xx])), n1.app.assoc(List.reverse.go(&2, U32, xt, []), [xx], acc))))

# digits written one after the other are the lists written
def n1.dch.app(
  xs: List<&2, U32>,
  +ys: List<&2, U32>
) -> {T.dec.chars(List.append(&2, U32, xs, ys)) == List.append(&2, Char, T.dec.chars(xs), T.dec.chars(ys))
  : List<&2, Char>}:
  match xs:
    case []:
      {==}
    case +xx <> +xt:
      Equal.cong(List<&2, Char>, List<&2, Char>, ls => T.dec.ch(xx) <> ls, T.dec.chars(List.append(&2, U32, xt, ys)),
        List.append(&2, Char, T.dec.chars(xt), T.dec.chars(ys)), n1.dch.app(xt, ys))

# the value of characters one after the other goes on from the first's
def n1.gn.app(
  xs: List<&2, Char>,
  +ys: List<&2, Char>,
  +rr: Nat,
  +acc: Nat
) -> {D1.g.num.nat(List.append(&2, Char, xs, ys), rr, acc) == D1.g.num.nat(ys, rr, D1.g.num.nat(xs, rr, acc))
  : Nat}:
  match xs:
    case []:
      {==}
    case +hh <> +tt:
      n1.gn.app(tt, ys, rr, D1.g.num.nat.step(D1.abnf.underscore(hh), hh, rr, acc))

# a digit below ten, written, is one more place of the value
def n1.dch1(
  +dd: U32,
  +acc: Nat,
  +hd: {U32.is_lt(dd, 10) == True{} : Bool}
) -> {D1.g.num.nat([T.dec.ch(dd)], 10n, acc) == Nat.add(Nat.mul(acc, 10n), U32.to_nat(dd)) : Nat}:
  M8.sm.elim(zz => {D1.g.num.nat([T.dec.ch(zz)], 10n, acc) == Nat.add(Nat.mul(acc, 10n), U32.to_nat(zz)) : Nat}, dd,
    hd, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# the value of a numeral's digits, least-significant first, as written
def n1.V(ds: List<&2, U32>) -> Nat:
  D1.g.num.nat(T.dec.chars(List.reverse(&2, U32, ds)), 10n, 0n)

# the value of a numeral's digits, least-significant first, as counted
def n1.W(ds: List<&2, U32>) -> Nat:
  match ds:
    case []:
      0n
    case dd <> tt:
      Nat.add(Nat.mul(n1.W(tt), 10n), U32.to_nat(dd))

# whether every digit is below ten
def n1.d10(ds: List<&2, U32>) -> Bool:
  match ds:
    case []:
      True{}
    case dd <> tt:
      Bool.and(U32.is_lt(dd, 10), n1.d10(tt))

# a digit below ten in front is one more place of what the rest is written
# as
def n1.Vc(
  +dd: U32,
  +tt: List<&2, U32>,
  +hd: {U32.is_lt(dd, 10) == True{} : Bool}
) -> {n1.V(dd <> tt) == Nat.add(Nat.mul(n1.V(tt), 10n), U32.to_nat(dd)) : Nat}:
  %Equal.sym(List<&2, U32>, List.reverse.go(&2, U32, tt, [dd]), List.append(&2, U32, List.reverse.go(&2, U32, tt, []),
    [dd]), n1.rgo(tt, [dd])) : {D1.g.num.nat(T.dec.chars(_), 10n, 0n) == Nat.add(Nat.mul(n1.V(tt), 10n),
    U32.to_nat(dd)) : Nat}
  %Equal.sym(List<&2, Char>, T.dec.chars(List.append(&2, U32, List.reverse.go(&2, U32, tt, []), [dd])),
    List.append(&2, Char, T.dec.chars(List.reverse.go(&2, U32, tt, [])), [T.dec.ch(dd)]),
    n1.dch.app(List.reverse.go(&2, U32, tt, []), [dd])) : {D1.g.num.nat(_, 10n, 0n) == Nat.add(Nat.mul(n1.V(tt),
    10n), U32.to_nat(dd)) : Nat}
  %Equal.sym(Nat, D1.g.num.nat(List.append(&2, Char, T.dec.chars(List.reverse.go(&2, U32, tt, [])),
    [T.dec.ch(dd)]), 10n, 0n), D1.g.num.nat([T.dec.ch(dd)], 10n, n1.V(tt)),
    n1.gn.app(T.dec.chars(List.reverse.go(&2, U32, tt, [])), [T.dec.ch(dd)], 10n, 0n)) : {_ ==
    Nat.add(Nat.mul(n1.V(tt), 10n), U32.to_nat(dd)) : Nat}
  n1.dch1(dd, n1.V(tt), hd)

# digits below ten are written as they are counted
def n1.VW(ds: List<&2, U32>, +hd: {n1.d10(ds) == True{} : Bool}) -> {n1.V(ds) == n1.W(ds) : Nat}:
  match ds:
    case []:
      {==}
    case +dd <> +tt:
      Equal.trans(Nat, n1.V(dd <> tt), Nat.add(Nat.mul(n1.V(tt), 10n), U32.to_nat(dd)), n1.W(dd <> tt), n1.Vc(dd,
        tt, Eq.and.left(U32.is_lt(dd, 10), n1.d10(tt), hd)), Equal.cong(Nat, Nat, nn => Nat.add(Nat.mul(nn, 10n),
        U32.to_nat(dd)), n1.V(tt), n1.W(tt), n1.VW(tt, Eq.and.right(U32.is_lt(dd, 10), n1.d10(tt), hd))))

# a Nat that compares equal to zero is zero
def n1.ceq0(nn: Nat, +hh: {Cmp.is_eq(Nat.cmp(nn, 0n)) == True{} : Bool}) -> {nn == 0n : Nat}:
  match nn:
    case 0n:
      {==}
    case 1n+(+n1):
      Eq.bit.absurd(&2, {1n+n1 == 0n : Nat}, hh)

# a U32 that is zero counts 0
def n1.uz(+qq: U32, +hh: {U32.is_zero(qq) == True{} : Bool}) -> {U32.to_nat(qq) == 0n : Nat}:
  n1.ceq0(U32.to_nat(qq), Equal.trans(Bool, Cmp.is_eq(Nat.cmp(U32.to_nat(qq), 0n)), Cmp.is_eq(U32.cmp(qq, 0)), True{},
    Equal.cong(Cmp, Bool, cc => Cmp.is_eq(cc), Nat.cmp(U32.to_nat(qq), 0n), U32.cmp(qq, 0), Equal.sym(Cmp,
    U32.cmp(qq, 0), Nat.cmp(U32.to_nat(qq), 0n), Ar.u_cmp(qq, 0))), hh))

# below ten, the quotient by ten is zero
def n1.q0(+qq: U32, +hq: {U32.is_lt(qq, 10) == True{} : Bool}) -> {U32.is_zero(U32.div(qq, 10)) == True{} : Bool}:
  Equal.trans(Bool, U32.is_zero(U32.div(qq, 10)), U32.is_lt(qq, 10), True{}, Equal.sym(Bool, U32.is_lt(qq, 10),
    U32.is_zero(U32.div(qq, 10)), M1.qz(qq)), hq)

# below ten, the remainder by ten counts what the U32 does
def n1.m0(
  +qq: U32,
  +hq: {U32.is_lt(qq, 10) == True{} : Bool}
) -> {U32.to_nat(U32.mod(qq, 10)) == U32.to_nat(qq) : Nat}:
  Equal.trans(Nat, U32.to_nat(U32.mod(qq, 10)), Nat.add(Nat.mul(U32.to_nat(U32.div(qq, 10)), 10n),
    U32.to_nat(U32.mod(qq, 10))), U32.to_nat(qq), Equal.cong(Nat, Nat, nn => Nat.add(Nat.mul(nn, 10n),
    U32.to_nat(U32.mod(qq, 10))), 0n, U32.to_nat(U32.div(qq, 10)), Equal.sym(Nat, U32.to_nat(U32.div(qq, 10)), 0n,
    n1.uz(U32.div(qq, 10), n1.q0(qq, hq)))), Ar.u_div(Unit{}, qq))

# the digits of a carry's quotient below ten count the quotient
def n1.carry.b(
  zz: Bool,
  +qq: U32,
  +ez: {U32.is_zero(qq) == zz : Bool},
  +hq: {U32.is_lt(qq, 10) == True{} : Bool}
) -> {n1.W(T.dec.carry.b0(zz, qq)) == U32.to_nat(qq) : Nat}:
  match zz:
    case True{}:
      Equal.sym(Nat, U32.to_nat(qq), 0n, n1.uz(qq, ez))
    case False{}:
      %Equal.sym(Bool, U32.is_zero(U32.div(qq, 10)), True{}, n1.q0(qq, hq)) : {n1.W(U32.mod(qq, 10) <>
        T.dec.carry.c0(_, U32.div(qq, 10))) == U32.to_nat(qq) : Nat}
      n1.m0(qq, hq)

# and are digits below ten
def n1.carry.okb(
  zz: Bool,
  +qq: U32,
  +hq: {U32.is_lt(qq, 10) == True{} : Bool}
) -> {n1.d10(T.dec.carry.b0(zz, qq)) == True{} : Bool}:
  match zz:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, U32.is_zero(U32.div(qq, 10)), True{}, n1.q0(qq, hq)) : {n1.d10(U32.mod(qq, 10) <>
        T.dec.carry.c0(_, U32.div(qq, 10))) == True{} : Bool}
      M9.and.tt(U32.is_lt(U32.mod(qq, 10), 10), True{}, M10.md(qq), {==})

# below 100, a carry's quotient by ten is below ten
def n1.c10(+cc: U32, +hc: {U32.is_lt(cc, 100) == True{} : Bool}) -> {U32.is_lt(U32.div(cc, 10), 10) == True{} : Bool}:
  Equal.trans(Bool, U32.is_lt(U32.div(cc, 10), 10), U32.is_lt(cc, 100), True{}, Equal.sym(Bool, U32.is_lt(cc, 100),
    U32.is_lt(U32.div(cc, 10), 10), M1.lt10(cc, 10, 100, 10n, {==}, {==})), hc)

# the digits of a carry below 100 count the carry
def n1.carry.a(
  zz: Bool,
  +cc: U32,
  +ez: {U32.is_zero(cc) == zz : Bool},
  +hc: {U32.is_lt(cc, 100) == True{} : Bool}
) -> {n1.W(T.dec.carry.a(zz, cc)) == U32.to_nat(cc) : Nat}:
  match zz:
    case True{}:
      Equal.sym(Nat, U32.to_nat(cc), 0n, n1.uz(cc, ez))
    case False{}:
      %Equal.sym(Nat, n1.W(T.dec.carry.b(U32.div(cc, 10))), U32.to_nat(U32.div(cc, 10)), n1.carry.b(
        U32.is_zero(U32.div(cc, 10)), U32.div(cc, 10), {==}, n1.c10(cc, hc))) : {Nat.add(Nat.mul(_, 10n),
        U32.to_nat(U32.mod(cc, 10))) == U32.to_nat(cc) : Nat}
      Ar.u_div(Unit{}, cc)

# and are digits below ten
def n1.carry.oka(
  zz: Bool,
  +cc: U32,
  +hc: {U32.is_lt(cc, 100) == True{} : Bool}
) -> {n1.d10(T.dec.carry.a(zz, cc)) == True{} : Bool}:
  match zz:
    case True{}:
      {==}
    case False{}:
      M9.and.tt(U32.is_lt(U32.mod(cc, 10), 10), n1.d10(T.dec.carry.b(U32.div(cc, 10))), M10.md(cc),
        n1.carry.okb(U32.is_zero(U32.div(cc, 10)), U32.div(cc, 10), n1.c10(cc, hc)))

# eight doublings
def n1.dbl8(nn: Nat) -> Nat:
  Nat.double(Nat.double(Nat.double(Nat.double(Nat.double(Nat.double(Nat.double(Nat.double(nn))))))))

# what 2^(8 + mm) is past 256, once uu is known
def n1.pz8(mm: Nat, uu: Unit) -> Nat:
  match uu:
    case Unit{}:
      n1.dbl8(Nat.sub(Ar.pow2(mm), 1n))

# 2^(8 + mm) is 256 and more
def n1.pw8(+mm: Nat, uu: Unit) -> {Ar.pow2u(8n+mm, uu) == Nat.add(256n, n1.pz8(mm, uu)) : Nat}:
  match uu:
    case Unit{}:
      Equal.cong(Nat, Nat, xx => n1.dbl8(xx), Ar.pow2(mm), 1n+Nat.sub(Ar.pow2(mm), 1n), Ar.p2_pos(mm))

# below 256 is below 2^32
def n1.lt256(
  +uu: Unit,
  +kk: Nat,
  +hk: {Nat.is_lt(kk, 256n) == True{} : Bool}
) -> {Nat.is_lt(kk, Ar.pow2u(32n, uu)) == True{} : Bool}:
  %Equal.sym(Nat, Ar.pow2u(32n, uu), Nat.add(256n, n1.pz8(24n, uu)), n1.pw8(24n, uu)) : {Nat.is_lt(kk, _) == True{}
    : Bool}
  M2.lt.add(kk, 256n, n1.pz8(24n, uu), hk)

# a digit times r and a carry, below r, is below ten times r
def n1.dig.bd(
  dn: Nat,
  kk: Nat,
  +rn: Nat,
  +cn: Nat,
  +hd: {Nat.is_lt(dn, kk) == True{} : Bool},
  +hc: {Nat.is_lt(cn, rn) == True{} : Bool}
) -> {Nat.is_lt(Nat.add(Nat.mul(dn, rn), cn), Nat.mul(kk, rn)) == True{} : Bool}:
  match dn kk:
    case _d 0n:
      Eq.bit.absurd(&2, {Nat.is_lt(Nat.add(Nat.mul(_d, rn), cn), 0n) == True{} : Bool}, Equal.trans(Bool, False{},
        Nat.is_lt(_d, 0n), True{}, Equal.sym(Bool, Nat.is_lt(_d, 0n), False{}, M2.nlt.zero(_d)), hd))
    case 0n 1n+(+k1):
      M2.lt.add(cn, rn, Nat.mul(k1, rn), hc)
    case 1n+(+d1) 1n+(+k1):
      %Equal.sym(Nat, Nat.add(Nat.add(rn, Nat.mul(d1, rn)), cn), Nat.add(rn, Nat.add(Nat.mul(d1, rn), cn)),
        Ar.nat_add_assoc(rn, Nat.mul(d1, rn), cn)) : {Nat.is_lt(_, Nat.add(rn, Nat.mul(k1, rn))) == True{} : Bool}
      Equal.trans(Bool, Nat.is_lt(Nat.add(rn, Nat.add(Nat.mul(d1, rn), cn)), Nat.add(rn, Nat.mul(k1, rn))),
        Nat.is_lt(Nat.add(Nat.mul(d1, rn), cn), Nat.mul(k1, rn)), True{}, Equal.cong(Cmp, Bool, xx => Cmp.is_lt(xx),
        Nat.cmp(Nat.add(rn, Nat.add(Nat.mul(d1, rn), cn)), Nat.add(rn, Nat.mul(k1, rn))), Nat.cmp(Nat.add(Nat.mul(d1,
        rn), cn), Nat.mul(k1, rn)), n1.cmp.add(rn, Nat.add(Nat.mul(d1, rn), cn), Nat.mul(k1, rn))), n1.dig.bd(d1, k1,
        rn, cn, hd, hc))

# ten times a radix's base
def n1.rb10(rx: D1.ARadix) -> U32:
  match rx:
    case D1.AHex{}:
      160
    case D1.AOct{}:
      80
    case D1.ABin{}:
      20

# what ten times a radix's base counts
def n1.rb10.n(rx: D1.ARadix) -> {U32.to_nat(n1.rb10(rx)) == Nat.mul(U32.to_nat(n1.rb(rx)), 10n) : Nat}:
  match rx:
    case D1.AHex{}:
      {==}
    case D1.AOct{}:
      {==}
    case D1.ABin{}:
      {==}

# and it is at most 256
def n1.rb.k(rx: D1.ARadix) -> {Nat.is_le(Nat.mul(10n, U32.to_nat(n1.rb(rx))), 256n) == True{} : Bool}:
  match rx:
    case D1.AHex{}:
      {==}
    case D1.AOct{}:
      {==}
    case D1.ABin{}:
      {==}

# a base is at most 100
def n1.rb.h(rx: D1.ARadix) -> {Nat.is_le(U32.to_nat(n1.rb(rx)), 100n) == True{} : Bool}:
  match rx:
    case D1.AHex{}:
      {==}
    case D1.AOct{}:
      {==}
    case D1.ABin{}:
      {==}

# a digit below ten times a base counts the digit times the base
def n1.mR(
  rx: D1.ARadix,
  +dd: U32,
  +hd: {U32.is_lt(dd, 10) == True{} : Bool}
) -> {U32.to_nat(U32.mul(dd, n1.rb(rx))) == Nat.mul(U32.to_nat(dd), U32.to_nat(n1.rb(rx))) : Nat}:
  match rx:
    case D1.AHex{}:
      M8.sm.elim(zz => {U32.to_nat(U32.mul(zz, 16)) == Nat.mul(U32.to_nat(zz), 16n) : Nat}, dd, hd, {==}, {==}, {==},
        {==}, {==}, {==}, {==}, {==}, {==}, {==})
    case D1.AOct{}:
      M8.sm.elim(zz => {U32.to_nat(U32.mul(zz, 8)) == Nat.mul(U32.to_nat(zz), 8n) : Nat}, dd, hd, {==}, {==}, {==},
        {==}, {==}, {==}, {==}, {==}, {==}, {==})
    case D1.ABin{}:
      M8.sm.elim(zz => {U32.to_nat(U32.mul(zz, 2)) == Nat.mul(U32.to_nat(zz), 2n) : Nat}, dd, hd, {==}, {==}, {==},
        {==}, {==}, {==}, {==}, {==}, {==}, {==})

# a U32 comparison below, as Nats
def n1.ul(
  +aa: U32,
  +bb: U32,
  +hh: {U32.is_lt(aa, bb) == True{} : Bool}
) -> {Nat.is_lt(U32.to_nat(aa), U32.to_nat(bb)) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(U32.to_nat(aa), U32.to_nat(bb)), U32.is_lt(aa, bb), True{}, Equal.sym(Bool,
    U32.is_lt(aa, bb), Nat.is_lt(U32.to_nat(aa), U32.to_nat(bb)), M2.u.lt(aa, bb)), hh)

# a digit below ten times a base and a carry below the base is below ten
# times the base
def n1.rs.bd(
  +rx: D1.ARadix,
  +dd: U32,
  +cc: U32,
  +hd: {U32.is_lt(dd, 10) == True{} : Bool},
  +hc: {U32.is_lt(cc, n1.rb(rx)) == True{} : Bool}
) -> {Nat.is_lt(Nat.add(Nat.mul(U32.to_nat(dd), U32.to_nat(n1.rb(rx))), U32.to_nat(cc)), Nat.mul(10n,
  U32.to_nat(n1.rb(rx)))) == True{} : Bool}:
  n1.dig.bd(U32.to_nat(dd), 10n, U32.to_nat(n1.rb(rx)), U32.to_nat(cc), n1.ul(dd, 10, hd), n1.ul(cc, n1.rb(rx), hc))

# the U32 a step of dec.go computes counts the digit times the base and the
# carry
def n1.xn(
  +uu: Unit,
  +rx: D1.ARadix,
  +dd: U32,
  +cc: U32,
  +hd: {U32.is_lt(dd, 10) == True{} : Bool},
  +hc: {U32.is_lt(cc, n1.rb(rx)) == True{} : Bool}
) -> {U32.to_nat(U32.add(U32.mul(dd, n1.rb(rx)), cc)) == Nat.add(Nat.mul(U32.to_nat(dd), U32.to_nat(n1.rb(rx))),
  U32.to_nat(cc)) : Nat}:
  +mm = U32.mul(dd, n1.rb(rx))
  +em = {n1.mR(rx, dd, hd) : {U32.to_nat(mm) == Nat.mul(U32.to_nat(dd), U32.to_nat(n1.rb(rx))) : Nat}}
  +e2 = {Equal.cong(Nat, Nat, nn => Nat.add(nn, U32.to_nat(cc)), U32.to_nat(mm), Nat.mul(U32.to_nat(dd),
    U32.to_nat(n1.rb(rx))), em) : {Nat.add(U32.to_nat(mm), U32.to_nat(cc)) == Nat.add(Nat.mul(U32.to_nat(dd),
    U32.to_nat(n1.rb(rx))), U32.to_nat(cc)) : Nat}}
  +hb = {n1.lt.le(Nat.add(Nat.mul(U32.to_nat(dd), U32.to_nat(n1.rb(rx))), U32.to_nat(cc)), Nat.mul(10n,
    U32.to_nat(n1.rb(rx))), 256n, n1.rs.bd(rx, dd, cc, hd, hc), n1.rb.k(rx)) : {Nat.is_lt(Nat.add(Nat.mul(
    U32.to_nat(dd), U32.to_nat(n1.rb(rx))), U32.to_nat(cc)), 256n) == True{} : Bool}}
  Equal.trans(Nat, U32.to_nat(U32.add(mm, cc)), Nat.add(U32.to_nat(mm), U32.to_nat(cc)), Nat.add(Nat.mul(
    U32.to_nat(dd), U32.to_nat(n1.rb(rx))), U32.to_nat(cc)), Ar.nat_mod_small(Ar.uadd_k(mm, cc),
    U32.to_nat(U32.add(mm, cc)), Nat.add(U32.to_nat(mm), U32.to_nat(cc)), Ar.pow2u(32n, uu), Ar.u_add(uu, mm, cc),
    n1.lt256(uu, Nat.add(U32.to_nat(mm), U32.to_nat(cc)), Equal.trans(Bool, Nat.is_lt(Nat.add(U32.to_nat(mm),
    U32.to_nat(cc)), 256n), Nat.is_lt(Nat.add(Nat.mul(U32.to_nat(dd), U32.to_nat(n1.rb(rx))), U32.to_nat(cc)),
    256n), True{}, Equal.cong(Nat, Bool, nn => Nat.is_lt(nn, 256n), Nat.add(U32.to_nat(mm), U32.to_nat(cc)),
    Nat.add(Nat.mul(U32.to_nat(dd), U32.to_nat(n1.rb(rx))), U32.to_nat(cc)), e2), hb))), e2)

# the new digit and carry of a step count the digit times the base and the
# old carry
def n1.rs.v(
  +uu: Unit,
  +rx: D1.ARadix,
  +dd: U32,
  +cc: U32,
  +hd: {U32.is_lt(dd, 10) == True{} : Bool},
  +hc: {U32.is_lt(cc, n1.rb(rx)) == True{} : Bool}
) -> {Nat.add(Nat.mul(U32.to_nat(U32.div(U32.add(U32.mul(dd, n1.rb(rx)), cc), 10)), 10n),
  U32.to_nat(U32.mod(U32.add(U32.mul(dd, n1.rb(rx)), cc), 10))) == Nat.add(Nat.mul(U32.to_nat(dd),
  U32.to_nat(n1.rb(rx))), U32.to_nat(cc)) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.mul(U32.to_nat(U32.div(U32.add(U32.mul(dd, n1.rb(rx)), cc), 10)), 10n),
    U32.to_nat(U32.mod(U32.add(U32.mul(dd, n1.rb(rx)), cc), 10))), U32.to_nat(U32.add(U32.mul(dd, n1.rb(rx)), cc)),
    Nat.add(Nat.mul(U32.to_nat(dd), U32.to_nat(n1.rb(rx))), U32.to_nat(cc)), Ar.u_div(Unit{},
    U32.add(U32.mul(dd, n1.rb(rx)), cc)), n1.xn(uu, rx, dd, cc, hd, hc))

# and the new carry is below the base
def n1.rs.q(
  +uu: Unit,
  +rx: D1.ARadix,
  +dd: U32,
  +cc: U32,
  +hd: {U32.is_lt(dd, 10) == True{} : Bool},
  +hc: {U32.is_lt(cc, n1.rb(rx)) == True{} : Bool}
) -> {U32.is_lt(U32.div(U32.add(U32.mul(dd, n1.rb(rx)), cc), 10), n1.rb(rx)) == True{} : Bool}:
  +xx = U32.add(U32.mul(dd, n1.rb(rx)), cc)
  Equal.trans(Bool, U32.is_lt(U32.div(xx, 10), n1.rb(rx)), U32.is_lt(xx, n1.rb10(rx)), True{}, Equal.sym(Bool,
    U32.is_lt(xx, n1.rb10(rx)), U32.is_lt(U32.div(xx, 10), n1.rb(rx)), M1.lt10(xx, n1.rb(rx), n1.rb10(rx),
    U32.to_nat(n1.rb(rx)), {==}, n1.rb10.n(rx))), Equal.trans(Bool, U32.is_lt(xx, n1.rb10(rx)),
    Nat.is_lt(U32.to_nat(xx), U32.to_nat(n1.rb10(rx))), True{}, M2.u.lt(xx, n1.rb10(rx)), Equal.trans(Bool,
    Nat.is_lt(U32.to_nat(xx), U32.to_nat(n1.rb10(rx))), Nat.is_lt(Nat.add(Nat.mul(U32.to_nat(dd),
    U32.to_nat(n1.rb(rx))), U32.to_nat(cc)), Nat.mul(10n, U32.to_nat(n1.rb(rx)))), True{}, Equal.trans(Bool,
    Nat.is_lt(U32.to_nat(xx), U32.to_nat(n1.rb10(rx))), Nat.is_lt(U32.to_nat(xx), Nat.mul(10n,
    U32.to_nat(n1.rb(rx)))), Nat.is_lt(Nat.add(Nat.mul(U32.to_nat(dd), U32.to_nat(n1.rb(rx))), U32.to_nat(cc)),
    Nat.mul(10n, U32.to_nat(n1.rb(rx)))), Equal.cong(Nat, Bool, nn => Nat.is_lt(U32.to_nat(xx), nn),
    U32.to_nat(n1.rb10(rx)), Nat.mul(10n, U32.to_nat(n1.rb(rx))), Equal.trans(Nat, U32.to_nat(n1.rb10(rx)),
    Nat.mul(U32.to_nat(n1.rb(rx)), 10n), Nat.mul(10n, U32.to_nat(n1.rb(rx))), n1.rb10.n(rx),
    n1.mulc(U32.to_nat(n1.rb(rx)), 10n))), Equal.cong(Nat, Bool, nn => Nat.is_lt(nn, Nat.mul(10n,
    U32.to_nat(n1.rb(rx)))), U32.to_nat(xx), Nat.add(Nat.mul(U32.to_nat(dd), U32.to_nat(n1.rb(rx))),
    U32.to_nat(cc)), n1.xn(uu, rx, dd, cc, hd, hc))), n1.rs.bd(rx, dd, cc, hd, hc))))

# a carry below a base is below 100
def n1.c100(
  +rx: D1.ARadix,
  +cc: U32,
  +hc: {U32.is_lt(cc, n1.rb(rx)) == True{} : Bool}
) -> {U32.is_lt(cc, 100) == True{} : Bool}:
  Equal.trans(Bool, U32.is_lt(cc, 100), Nat.is_lt(U32.to_nat(cc), 100n), True{}, M2.u.lt(cc, 100), n1.lt.le(
    U32.to_nat(cc), U32.to_nat(n1.rb(rx)), 100n, n1.ul(cc, n1.rb(rx), hc), n1.rb.h(rx)))

# a step's value: the digits before times the base and the carry, the new
# carry times ten and the new digit
def n1.alg(
  +vv: Nat,
  +rr: Nat,
  +qq: Nat,
  +mm: Nat,
  +dd: Nat,
  +cc: Nat,
  +hs: {Nat.add(Nat.mul(qq, 10n), mm) == Nat.add(Nat.mul(dd, rr), cc) : Nat}
) -> {Nat.add(Nat.mul(Nat.add(Nat.mul(vv, rr), qq), 10n), mm) == Nat.add(Nat.mul(Nat.add(Nat.mul(vv, 10n), dd), rr),
  cc) : Nat}:
  %Equal.sym(Nat, Nat.mul(Nat.add(Nat.mul(vv, rr), qq), 10n), Nat.add(Nat.mul(Nat.mul(vv, rr), 10n), Nat.mul(qq,
    10n)), Ar.nat_mul_add_r(Nat.mul(vv, rr), qq, 10n)) : {Nat.add(_, mm) == Nat.add(Nat.mul(Nat.add(Nat.mul(vv,
    10n), dd), rr), cc) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(Nat.mul(vv, rr), 10n), Nat.mul(qq, 10n)), mm), Nat.add(Nat.mul(Nat.mul(vv,
    rr), 10n), Nat.add(Nat.mul(qq, 10n), mm)), Ar.nat_add_assoc(Nat.mul(Nat.mul(vv, rr), 10n), Nat.mul(qq, 10n),
    mm)) : {_ == Nat.add(Nat.mul(Nat.add(Nat.mul(vv, 10n), dd), rr), cc) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(qq, 10n), mm), Nat.add(Nat.mul(dd, rr), cc), hs) : {Nat.add(Nat.mul(Nat.mul(vv, rr),
    10n), _) == Nat.add(Nat.mul(Nat.add(Nat.mul(vv, 10n), dd), rr), cc) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.add(Nat.mul(vv, 10n), dd), rr), Nat.add(Nat.mul(Nat.mul(vv, 10n), rr), Nat.mul(dd,
    rr)), Ar.nat_mul_add_r(Nat.mul(vv, 10n), dd, rr)) : {Nat.add(Nat.mul(Nat.mul(vv, rr), 10n), Nat.add(Nat.mul(dd,
    rr), cc)) == Nat.add(_, cc) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(Nat.mul(vv, 10n), rr), Nat.mul(dd, rr)), cc), Nat.add(Nat.mul(Nat.mul(vv,
    10n), rr), Nat.add(Nat.mul(dd, rr), cc)), Ar.nat_add_assoc(Nat.mul(Nat.mul(vv, 10n), rr), Nat.mul(dd, rr),
    cc)) : {Nat.add(Nat.mul(Nat.mul(vv, rr), 10n), Nat.add(Nat.mul(dd, rr), cc)) == _ : Nat}
  Equal.cong(Nat, Nat, nn => Nat.add(nn, Nat.add(Nat.mul(dd, rr), cc)), Nat.mul(Nat.mul(vv, rr), 10n),
    Nat.mul(Nat.mul(vv, 10n), rr), Equal.trans(Nat, Nat.mul(Nat.mul(vv, rr), 10n), Nat.mul(vv, Nat.mul(rr, 10n)),
    Nat.mul(Nat.mul(vv, 10n), rr), Ar.nat_mul_assoc(vv, rr, 10n), Equal.trans(Nat, Nat.mul(vv, Nat.mul(rr, 10n)),
    Nat.mul(vv, Nat.mul(10n, rr)), Nat.mul(Nat.mul(vv, 10n), rr), Equal.cong(Nat, Nat, nn => Nat.mul(vv, nn),
    Nat.mul(rr, 10n), Nat.mul(10n, rr), n1.mulc(rr, 10n)), Equal.sym(Nat, Nat.mul(Nat.mul(vv, 10n), rr),
    Nat.mul(vv, Nat.mul(10n, rr)), Ar.nat_mul_assoc(vv, 10n, rr)))))

# dec.go multiplies what digits below ten count by the base and adds a carry
# below the base
def n1.Wgo(
  +uu: Unit,
  ds: List<&2, U32>,
  +rx: D1.ARadix,
  +cc: U32,
  +hd: {n1.d10(ds) == True{} : Bool},
  +hc: {U32.is_lt(cc, n1.rb(rx)) == True{} : Bool}
) -> {n1.W(T.dec.go(ds, n1.rb(rx), cc)) == Nat.add(Nat.mul(n1.W(ds), U32.to_nat(n1.rb(rx))), U32.to_nat(cc)) : Nat}:
  match ds:
    case []:
      n1.carry.a(U32.is_zero(cc), cc, {==}, n1.c100(rx, cc, hc))
    case +dd <> +tt:
      +hdd = {Eq.and.left(U32.is_lt(dd, 10), n1.d10(tt), hd) : {U32.is_lt(dd, 10) == True{} : Bool}}
      +hdt = {Eq.and.right(U32.is_lt(dd, 10), n1.d10(tt), hd) : {n1.d10(tt) == True{} : Bool}}
      +xx = U32.add(U32.mul(dd, n1.rb(rx)), cc)
      %Equal.sym(Nat, n1.W(T.dec.go(tt, n1.rb(rx), U32.div(xx, 10))), Nat.add(Nat.mul(n1.W(tt), U32.to_nat(n1.rb(rx))),
        U32.to_nat(U32.div(xx, 10))), n1.Wgo(uu, tt, rx, U32.div(xx, 10), hdt, n1.rs.q(uu, rx, dd, cc, hdd, hc))) :
        {Nat.add(Nat.mul(_, 10n), U32.to_nat(U32.mod(xx, 10))) == Nat.add(Nat.mul(Nat.add(Nat.mul(n1.W(tt), 10n),
        U32.to_nat(dd)), U32.to_nat(n1.rb(rx))), U32.to_nat(cc)) : Nat}
      n1.alg(n1.W(tt), U32.to_nat(n1.rb(rx)), U32.to_nat(U32.div(xx, 10)), U32.to_nat(U32.mod(xx, 10)),
        U32.to_nat(dd), U32.to_nat(cc), n1.rs.v(uu, rx, dd, cc, hdd, hc))

# and leaves digits below ten
def n1.Wok(
  +uu: Unit,
  ds: List<&2, U32>,
  +rx: D1.ARadix,
  +cc: U32,
  +hd: {n1.d10(ds) == True{} : Bool},
  +hc: {U32.is_lt(cc, n1.rb(rx)) == True{} : Bool}
) -> {n1.d10(T.dec.go(ds, n1.rb(rx), cc)) == True{} : Bool}:
  match ds:
    case []:
      n1.carry.oka(U32.is_zero(cc), cc, n1.c100(rx, cc, hc))
    case +dd <> +tt:
      +hdd = {Eq.and.left(U32.is_lt(dd, 10), n1.d10(tt), hd) : {U32.is_lt(dd, 10) == True{} : Bool}}
      +hdt = {Eq.and.right(U32.is_lt(dd, 10), n1.d10(tt), hd) : {n1.d10(tt) == True{} : Bool}}
      +xx = U32.add(U32.mul(dd, n1.rb(rx)), cc)
      M9.and.tt(U32.is_lt(U32.mod(xx, 10), 10), n1.d10(T.dec.go(tt, n1.rb(rx), U32.div(xx, 10))), M10.md(xx),
          n1.Wok(uu, tt,
        rx, U32.div(xx, 10), hdt, n1.rs.q(uu, rx, dd, cc, hdd, hc)))

# whether every character is a DIGIT
def n1.lall(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      True{}
    case hh <> tt:
      Bool.and(D1.abnf.DIGIT(hh), n1.lall(tt))

# a digit below ten is written as a DIGIT
def n1.dch.d(+dd: U32, +hd: {U32.is_lt(dd, 10) == True{} : Bool}) -> {D1.abnf.DIGIT(T.dec.ch(dd)) == True{} : Bool}:
  M8.sm.elim(zz => {D1.abnf.DIGIT(T.dec.ch(zz)) == True{} : Bool}, dd, hd, {==}, {==}, {==}, {==}, {==}, {==}, {==},
    {==}, {==}, {==})

# digits below ten are written as DIGITs
def n1.dall.ch(ds: List<&2, U32>, +hd: {n1.d10(ds) == True{} : Bool}) -> {n1.lall(T.dec.chars(ds)) == True{} : Bool}:
  match ds:
    case []:
      {==}
    case +dd <> +tt:
      M9.and.tt(D1.abnf.DIGIT(T.dec.ch(dd)), n1.lall(T.dec.chars(tt)), n1.dch.d(dd, Eq.and.left(U32.is_lt(dd, 10),
        n1.d10(tt), hd)), n1.dall.ch(tt, Eq.and.right(U32.is_lt(dd, 10), n1.d10(tt), hd)))

# reversed onto digits below ten, digits below ten stay so
def n1.d10.rev(
  ds: List<&2, U32>,
  +acc: List<&2, U32>,
  +hd: {n1.d10(ds) == True{} : Bool},
  +ha: {n1.d10(acc) == True{} : Bool}
) -> {n1.d10(List.reverse.go(&2, U32, ds, acc)) == True{} : Bool}:
  match ds:
    case []:
      ha
    case +dd <> +tt:
      n1.d10.rev(tt, dd <> acc, Eq.and.right(U32.is_lt(dd, 10), n1.d10(tt), hd), M9.and.tt(U32.is_lt(dd, 10),
        n1.d10(acc), Eq.and.left(U32.is_lt(dd, 10), n1.d10(tt), hd), ha))

# DIGITs make a string of DIGITs
def n1.lall.fl(
  cs: List<&2, Char>,
  +hc: {n1.lall(cs) == True{} : Bool}
) -> {D1.g.dec.all(String.from_list(cs)) == True{} : Bool}:
  match cs:
    case []:
      {==}
    case +hh <> +tt:
      M9.and.tt(D1.abnf.DIGIT(hh), D1.g.dec.all(String.from_list(tt)), Eq.and.left(D1.abnf.DIGIT(hh),
        n1.lall(tt), hc), n1.lall.fl(tt, Eq.and.right(D1.abnf.DIGIT(hh), n1.lall(tt), hc)))

# a DIGIT that is not 0 is a digit1-9
def n1.nzd(
  +cc: Char,
  +hd: {D1.abnf.DIGIT(cc) == True{} : Bool},
  +hz: {Char.is_eq(cc, '0') == False{} : Bool}
) -> {D1.abnf.digit1_9(cc) == True{} : Bool}:
  M6.dg.elim(zz => {Char.is_eq(zz, '0') == False{} : Bool} -> {D1.abnf.digit1_9(zz) == True{} : Bool}, cc,
    M4.gs.dig(cc, hd), ee => Eq.bit.absurd2(&2, {D1.abnf.digit1_9('0') == True{} : Bool}, ee), _e => {==}, _e => {==},
    _e => {==}, _e => {==}, _e => {==}, _e => {==}, _e => {==}, _e => {==}, _e => {==})(hz)

# a character that is not 0, then DIGITs, is canonical
def n1.nzc(
  +hh: Char,
  +tt: List<&2, Char>,
  +hd: {D1.abnf.DIGIT(hh) == True{} : Bool},
  +hz: {Char.is_eq(hh, '0') == False{} : Bool},
  +ht: {n1.lall(tt) == True{} : Bool}
) -> {D1.g.dec.canon(String.from_list(hh <> tt)) == True{} : Bool}:
  %Equal.sym(Bool, D1.abnf.DIGIT(hh), True{}, hd) : {Bool.and(_, Bool.or(Bool.and(D1.abnf.cp(hh, 48),
    String.is_empty(String.from_list(tt))), Bool.and(D1.abnf.digit1_9(hh), D1.g.dec.all(String.from_list(tt)))))
    == True{} : Bool}
  %Equal.sym(Bool, D1.abnf.cp(hh, 48), False{}, Equal.trans(Bool, D1.abnf.cp(hh, 48), Char.is_eq(hh, '0'),
    False{}, Equal.sym(Bool, Char.is_eq(hh, Chr{48}), D1.abnf.cp(hh, 48), n1.cp(hh, 48)), hz)) :
    {Bool.and(True{}, Bool.or(Bool.and(_, String.is_empty(String.from_list(tt))), Bool.and(D1.abnf.digit1_9(hh),
    D1.g.dec.all(String.from_list(tt))))) == True{} : Bool}
  %Equal.sym(Bool, D1.abnf.digit1_9(hh), True{}, n1.nzd(hh, hd, hz)) : {Bool.and(True{}, Bool.or(Bool.and(False{},
    String.is_empty(String.from_list(tt))), Bool.and(_, D1.g.dec.all(String.from_list(tt))))) == True{} : Bool}
  n1.lall.fl(tt, ht)

# after the first character, with dec.drop's lead: a 0 is dropped, and any
# other DIGIT starts the canonical numeral
def n1.drop.go.c(
  zz: Bool,
  +hh: Char,
  +tt: List<&2, Char>,
  +ez: {Char.is_eq(hh, '0') == zz : Bool},
  +hd: {D1.abnf.DIGIT(hh) == True{} : Bool},
  +ht: {n1.lall(tt) == True{} : Bool},
  +ih: {D1.g.dec.canon(T.dec.drop(tt, True{}, [])) == True{} : Bool}
) -> {D1.g.dec.canon(T.dec.drop(tt, zz, T.dec.drop.outz(zz, hh, []))) == True{} : Bool}:
  match zz:
    case True{}:
      ih
    case False{}:
      %Equal.sym(String, T.dec.drop(tt, False{}, [hh]), String.from_list(hh <> tt), M4.dd.kept(tt, [hh])) :
        {D1.g.dec.canon(_) == True{} : Bool}
      n1.nzc(hh, tt, hd, ez, ht)

# dec.drop of DIGITs from the lead is canonical
def n1.drop.c(
  cs: List<&2, Char>,
  +hc: {n1.lall(cs) == True{} : Bool}
) -> {D1.g.dec.canon(T.dec.drop(cs, True{}, [])) == True{} : Bool}:
  match cs:
    case []:
      {==}
    case +hh <> +tt:
      +ht = {Eq.and.right(D1.abnf.DIGIT(hh), n1.lall(tt), hc) : {n1.lall(tt) == True{} : Bool}}
      n1.drop.go.c(Char.is_eq(hh, '0'), hh, tt, {==}, Eq.and.left(D1.abnf.DIGIT(hh), n1.lall(tt), hc), ht,
        n1.drop.c(tt, ht))

# and worth what the DIGITs are
def n1.drop.go.v(
  zz: Bool,
  +hh: Char,
  +tt: List<&2, Char>,
  +ez: {Char.is_eq(hh, '0') == zz : Bool},
  +ih: {n1.h10(T.dec.drop(tt, True{}, [])) == D1.g.num.nat(tt, 10n, 0n) : Nat}
) -> {n1.h10(T.dec.drop(tt, zz, T.dec.drop.outz(zz, hh, []))) == D1.g.num.nat(hh <> tt, 10n, 0n) : Nat}:
  match zz:
    case True{}:
      %Equal.sym(Char, hh, '0', Eq.char_eq_true(hh, '0', ez)) : {n1.h10(T.dec.drop(tt, True{}, [])) ==
        D1.g.num.nat(_ <> tt, 10n, 0n) : Nat}
      ih
    case False{}:
      %Equal.sym(String, T.dec.drop(tt, False{}, [hh]), String.from_list(hh <> tt), M4.dd.kept(tt, [hh])) :
        {n1.h10(_) == D1.g.num.nat(hh <> tt, 10n, 0n) : Nat}
      %Equal.sym(List<&2, Char>, String.to_list(String.from_list(tt)), tt, M2.gd.tlfl(tt)) : {D1.g.num.nat(hh <> _,
        10n, 0n) == D1.g.num.nat(hh <> tt, 10n, 0n) : Nat}
      {==}

# dec.drop of DIGITs from the lead is worth what they are
def n1.drop.v(cs: List<&2, Char>) -> {n1.h10(T.dec.drop(cs, True{}, [])) == D1.g.num.nat(cs, 10n, 0n) : Nat}:
  match cs:
    case []:
      {==}
    case +hh <> +tt:
      n1.drop.go.v(Char.is_eq(hh, '0'), hh, tt, {==}, n1.drop.v(tt))

# dec.text of digits below ten is canonical
def n1.text.c(
  +ds: List<&2, U32>,
  +hd: {n1.d10(ds) == True{} : Bool}
) -> {D1.g.dec.canon(T.dec.text(ds)) == True{} : Bool}:
  n1.drop.c(T.dec.chars(List.reverse(&2, U32, ds)), n1.dall.ch(List.reverse(&2, U32, ds), n1.d10.rev(ds, [], hd,
    {==})))

# and worth what they count
def n1.text.v(+ds: List<&2, U32>, +hd: {n1.d10(ds) == True{} : Bool}) -> {n1.h10(T.dec.text(ds)) == n1.W(ds) : Nat}:
  Equal.trans(Nat, n1.h10(T.dec.text(ds)), n1.V(ds), n1.W(ds), n1.drop.v(T.dec.chars(List.reverse(&2, U32, ds))),
    n1.VW(ds, hd))

# The prefixed integer's numeral. After the prefix the scan reads each digit
# of the radix into the numeral with dec.go and passes over each underscore;
# n1.cv is that reading, and it counts the digits' value in the radix.

# one character of the reading: an underscore is passed over, and a digit
# goes into the numeral
def n1.cv.s(uu: Bool, +rx: D1.ARadix, +hh: Char, ds: List<&2, U32>) -> List<&2, U32>:
  match uu:
    case True{}:
      ds
    case False{}:
      T.dec.go(ds, n1.rb(rx), T.dig.val(hh))

# the numeral the scan reads from a prefixed integer's digits
def n1.cv(+rx: D1.ARadix, xs: List<&2, Char>, ds: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case []:
      ds
    case +hh <> tt:
      n1.cv(rx, tt, n1.cv.s(Char.is_eq(hh, '_'), rx, hh, ds))

# the type of n1.Bv.go's ihd
def n1.Bv.go.P1(+cc: Char, +tt: List<&2, Char>, +sg: T.Sign, +rx: D1.ARadix, +ds: List<&2, U32>) -> Type:
  {D1.abnf.radix_rep(tt, rx) == True{} : Bool} -> {T.num.go(tt, n1.sb(sg, rx, T.dec.go(ds, n1.rb(rx),
    T.dig.val(cc)))) == n1.sb(sg, rx, n1.cv(rx, tt, T.dec.go(ds, n1.rb(rx), T.dig.val(cc)))) : T.Num}

# the type of n1.Bv.go's ihu
def n1.Bv.go.P2(+tt: List<&2, Char>, +sg: T.Sign, +rx: D1.ARadix, +ds: List<&2, U32>) -> Type:
  {n1.bg(tt, rx) == True{} : Bool} -> {T.num.go(tt, T.Num{T.NBase{}, sg, n1.rb(rx), ds, True{}, True{},
    ""}) == n1.sb(sg, rx, n1.cv(rx, tt, ds)) : T.Num}

# the character after a digit of a prefixed integer that is the radix's
# repetition: an underscore goes on to a digit, and a digit goes into the
# numeral
def n1.Bv.go(
  uu: Bool,
  ok: Bool,
  +cc: Char,
  +tt: List<&2, Char>,
  +sg: T.Sign,
  +rx: D1.ARadix,
  +ds: List<&2, U32>,
  +eu: {Char.is_eq(cc, '_') == uu : Bool},
  +eo: {T.dig.ok(T.dig.val(cc), n1.rb(rx)) == ok : Bool},
  +hr: {D1.abnf.radix_rep(cc <> tt, rx) == True{} : Bool},
  ihd: n1.Bv.go.P1(cc, tt, sg, rx, ds),
  ihu: n1.Bv.go.P2(tt, sg, rx, ds)
) -> {T.num.go(tt, T.num.based.go(uu, n1.sb(sg, rx, ds), cc)) == n1.sb(sg, rx, n1.cv(rx, tt, n1.cv.s(uu, rx, cc, ds)))
  : T.Num}:
  match uu:
    case True{}:
      ihu(Equal.trans(Bool, n1.bg(tt, rx), D1.abnf.radix_rep('_' <> tt, rx), True{}, n1.rrep.u(rx, tt),
        Equal.trans(Bool, D1.abnf.radix_rep('_' <> tt, rx), D1.abnf.radix_rep(cc <> tt, rx), True{},
        Equal.cong(Char, Bool, xx => D1.abnf.radix_rep(xx <> tt, rx), '_', cc, Equal.sym(Char, cc, '_',
        Eq.char_eq_true(cc, '_', eu))), hr)))
    case False{}:
      match ok:
        case True{}:
          %Equal.sym(Bool, T.dig.ok(T.dig.val(cc), n1.rb(rx)), True{}, eo) : {T.num.go(tt, T.num.digit.ok(_, cc,
            T.NBase{}, sg, n1.rb(rx), ds)) == n1.sb(sg, rx, n1.cv(rx, tt, T.dec.go(ds, n1.rb(rx), T.dig.val(cc))))
            : T.Num}
          ihd(Equal.trans(Bool, D1.abnf.radix_rep(tt, rx), D1.abnf.radix_rep(cc <> tt, rx), True{},
            n1.rrep.d(rx, cc, tt, n1.cls.t(rx, cc, eo)), hr))
        case False{}:
          Eq.bit.absurd(&2, {T.num.go(tt, T.num.based.go(False{}, n1.sb(sg, rx, ds), cc)) == n1.sb(sg, rx, n1.cv(rx,
            tt, n1.cv.s(False{}, rx, cc, ds))) : T.Num}, Equal.trans(Bool, False{}, D1.abnf.radix_rep(cc <> tt,
            rx), True{}, n1.rrep.n(rx, cc, tt, n1.cls.f(rx, cc, eo), eu), hr))

# the type of n1.Buv.go's ih
def n1.Buv.go.P1(+cc: Char, +tt: List<&2, Char>, +sg: T.Sign, +rx: D1.ARadix, +ds: List<&2, U32>) -> Type:
  {D1.abnf.radix_rep(tt, rx) == True{} : Bool} -> {T.num.go(tt, n1.sb(sg, rx, T.dec.go(ds, n1.rb(rx),
    T.dig.val(cc)))) == n1.sb(sg, rx, n1.cv(rx, tt, T.dec.go(ds, n1.rb(rx), T.dig.val(cc)))) : T.Num}

# a prefixed integer's state where an underscore fails, before a digit of
# the radix and the repetition: the digit goes into the numeral
def n1.Buv.go(
  uu: Bool,
  ok: Bool,
  +cc: Char,
  +tt: List<&2, Char>,
  +sg: T.Sign,
  +rx: D1.ARadix,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String,
  +eu: {Char.is_eq(cc, '_') == uu : Bool},
  +eo: {T.dig.ok(T.dig.val(cc), n1.rb(rx)) == ok : Bool},
  +hr: {n1.bg(cc <> tt, rx) == True{} : Bool},
  ih: n1.Buv.go.P1(cc, tt, sg, rx, ds)
) -> {T.num.go(tt, T.num.based.go(uu, T.Num{T.NBase{}, sg, n1.rb(rx), ds, us, saw, why}, cc)) == n1.sb(sg, rx,
  n1.cv(rx, tt, n1.cv.s(uu, rx, cc, ds))) : T.Num}:
  match uu:
    case True{}:
      Eq.bit.absurd(&2, {T.num.go(tt, T.num.based.go(True{}, T.Num{T.NBase{}, sg, n1.rb(rx), ds, us, saw, why}, cc))
        == n1.sb(sg, rx, n1.cv(rx, tt, n1.cv.s(True{}, rx, cc, ds))) : T.Num}, Equal.trans(Bool, False{},
        D1.abnf.radix_digit(rx, cc), True{}, Equal.trans(Bool, False{}, D1.abnf.radix_digit(rx, '_'),
        D1.abnf.radix_digit(rx, cc), Equal.sym(Bool, D1.abnf.radix_digit(rx, '_'), False{}, n1.rd.us(rx)),
        Equal.cong(Char, Bool, xx => D1.abnf.radix_digit(rx, xx), '_', cc, Equal.sym(Char, cc, '_',
        Eq.char_eq_true(cc, '_', eu)))), Eq.and.left(D1.abnf.radix_digit(rx, cc), D1.abnf.radix_rep(tt, rx), hr)))
    case False{}:
      match ok:
        case True{}:
          %Equal.sym(Bool, T.dig.ok(T.dig.val(cc), n1.rb(rx)), True{}, eo) : {T.num.go(tt, T.num.digit.ok(_, cc,
            T.NBase{}, sg, n1.rb(rx), ds)) == n1.sb(sg, rx, n1.cv(rx, tt, T.dec.go(ds, n1.rb(rx), T.dig.val(cc))))
            : T.Num}
          ih(Eq.and.right(D1.abnf.radix_digit(rx, cc), D1.abnf.radix_rep(tt, rx), hr))
        case False{}:
          Eq.bit.absurd(&2, {T.num.go(tt, T.num.based.go(False{}, T.Num{T.NBase{}, sg, n1.rb(rx), ds, us, saw, why},
            cc)) == n1.sb(sg, rx, n1.cv(rx, tt, n1.cv.s(False{}, rx, cc, ds))) : T.Num}, Equal.trans(Bool, False{},
            D1.abnf.radix_digit(rx, cc), True{}, Equal.sym(Bool, D1.abnf.radix_digit(rx, cc), False{},
            n1.cls.f(rx, cc, eo)), Eq.and.left(D1.abnf.radix_digit(rx, cc), D1.abnf.radix_rep(tt, rx), hr)))

# the type of n1.Buv's ih
def n1.Buv.P1(+cc: Char, +tt: List<&2, Char>, +sg: T.Sign, +rx: D1.ARadix, +ds: List<&2, U32>) -> Type:
  {D1.abnf.radix_rep(tt, rx) == True{} : Bool} -> {T.num.go(tt, n1.sb(sg, rx, T.dec.go(ds, n1.rb(rx),
    T.dig.val(cc)))) == n1.sb(sg, rx, n1.cv(rx, tt, T.dec.go(ds, n1.rb(rx), T.dig.val(cc)))) : T.Num}

# with a character and the rest
def n1.Buv(
  +cc: Char,
  +tt: List<&2, Char>,
  +sg: T.Sign,
  +rx: D1.ARadix,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String,
  +hr: {n1.bg(cc <> tt, rx) == True{} : Bool},
  ih: n1.Buv.P1(cc, tt, sg, rx, ds)
) -> {T.num.go(cc <> tt, T.Num{T.NBase{}, sg, n1.rb(rx), ds, us, saw, why}) == n1.sb(sg, rx, n1.cv(rx, cc <> tt, ds))
  : T.Num}:
  n1.Buv.go(Char.is_eq(cc, '_'), T.dig.ok(T.dig.val(cc), n1.rb(rx)), cc, tt, sg, rx, ds, us, saw, why, {==}, {==}, hr,
    ih)

# after a digit of a prefixed integer, the radix's repetition is read into
# the numeral
def n1.Bv(
  rest: List<&2, Char>,
  +sg: T.Sign,
  +rx: D1.ARadix,
  +ds: List<&2, U32>,
  +hr: {D1.abnf.radix_rep(rest, rx) == True{} : Bool}
) -> {T.num.go(rest, n1.sb(sg, rx, ds)) == n1.sb(sg, rx, n1.cv(rx, rest, ds)) : T.Num}:
  match rest:
    case []:
      {==}
    case +hh <> tt:
      match tt:
        case []:
          n1.Bv.go(Char.is_eq(hh, '_'), T.dig.ok(T.dig.val(hh), n1.rb(rx)), hh, [], sg, rx, ds, {==}, {==}, hr,
            _h => {==}, hb => Eq.bit.absurd(&2, {T.num.go([], T.Num{T.NBase{}, sg, n1.rb(rx), ds, True{}, True{}, ""})
            == n1.sb(sg, rx, n1.cv(rx, [], ds)) : T.Num}, hb))
        case +h2 <> +t2:
          n1.Bv.go(Char.is_eq(hh, '_'), T.dig.ok(T.dig.val(hh), n1.rb(rx)), hh, h2 <> t2, sg, rx, ds, {==}, {==}, hr,
            hd => n1.Bv(h2 <> t2, sg, rx, T.dec.go(ds, n1.rb(rx), T.dig.val(hh)), hd), hb => n1.Buv(h2, t2, sg, rx,
            ds, True{}, True{}, "", hb, h3 => n1.Bv(t2, sg, rx, T.dec.go(ds, n1.rb(rx), T.dig.val(h2)), h3)))

# after a prefix, a digit of the radix and the repetition are read into the
# numeral
def n1.B0v(
  rest: List<&2, Char>,
  +sg: T.Sign,
  +rx: D1.ARadix,
  +hr: {n1.bg(rest, rx) == True{} : Bool}
) -> {T.num.go(rest, T.Num{T.NBase{}, sg, n1.rb(rx), [], False{}, False{}, ""}) == n1.sb(sg, rx, n1.cv(rx, rest, []))
  : T.Num}:
  match rest:
    case []:
      Eq.bit.absurd(&2, {T.num.go([], T.Num{T.NBase{}, sg, n1.rb(rx), [], False{}, False{}, ""}) == n1.sb(sg, rx,
        n1.cv(rx, [], [])) : T.Num}, hr)
    case +hh <> +tt:
      n1.Buv(hh, tt, sg, rx, [], False{}, False{}, "", hr, hd => n1.Bv(tt, sg, rx, T.dec.go([], n1.rb(rx),
        T.dig.val(hh)), hd))

# whether each character is an underscore or a digit of the radix
def n1.rr(+rx: D1.ARadix, xs: List<&2, Char>) -> Bool:
  match xs:
    case []:
      True{}
    case +hh <> tt:
      Bool.and(Bool.or(Char.is_eq(hh, '_'), D1.abnf.radix_digit(rx, hh)), n1.rr(rx, tt))

# an or with True on its right is True
def n1.or.t(aa: Bool) -> {Bool.or(aa, True{}) == True{} : Bool}:
  match aa:
    case True{}:
      {==}
    case False{}:
      {==}

# a character of the repetition, by whether it is an underscore or a digit
def n1.rr.go(
  uu: Bool,
  dd: Bool,
  +hh: Char,
  +h2: Char,
  +t2: List<&2, Char>,
  +rx: D1.ARadix,
  +eu: {Char.is_eq(hh, '_') == uu : Bool},
  +ed: {D1.abnf.radix_digit(rx, hh) == dd : Bool},
  +hr: {D1.abnf.radix_rep(hh <> h2 <> t2, rx) == True{} : Bool},
  i1: {D1.abnf.radix_rep(h2 <> t2, rx) == True{} : Bool} -> {n1.rr(rx, h2 <> t2) == True{} : Bool},
  i2: {D1.abnf.radix_rep(t2, rx) == True{} : Bool} -> {n1.rr(rx, t2) == True{} : Bool}
) -> {n1.rr(rx, hh <> h2 <> t2) == True{} : Bool}:
  match uu:
    case True{}:
      +hb = {Equal.trans(Bool, n1.bg(h2 <> t2, rx), D1.abnf.radix_rep('_' <> h2 <> t2, rx), True{},
        n1.rrep.u(rx, h2 <> t2), Equal.trans(Bool, D1.abnf.radix_rep('_' <> h2 <> t2, rx),
        D1.abnf.radix_rep(hh <> h2 <> t2, rx), True{}, Equal.cong(Char, Bool, xx => D1.abnf.radix_rep(xx <> h2 <>
        t2, rx), '_', hh, Equal.sym(Char, hh, '_', Eq.char_eq_true(hh, '_', eu))), hr)) : {n1.bg(h2 <> t2, rx)
        == True{} : Bool}}
      %Equal.sym(Bool, Char.is_eq(hh, '_'), True{}, eu) : {Bool.and(Bool.or(_, D1.abnf.radix_digit(rx, hh)),
        n1.rr(rx, h2 <> t2)) == True{} : Bool}
      %Equal.sym(Bool, D1.abnf.radix_digit(rx, h2), True{}, Eq.and.left(D1.abnf.radix_digit(rx, h2),
        D1.abnf.radix_rep(t2, rx), hb)) : {Bool.and(Bool.or(True{}, D1.abnf.radix_digit(rx, hh)),
        Bool.and(Bool.or(Char.is_eq(h2, '_'), _), n1.rr(rx, t2))) == True{} : Bool}
      %Equal.sym(Bool, Bool.or(Char.is_eq(h2, '_'), True{}), True{}, n1.or.t(Char.is_eq(h2, '_'))) :
        {Bool.and(True{}, Bool.and(_, n1.rr(rx, t2))) == True{} : Bool}
      i2(Eq.and.right(D1.abnf.radix_digit(rx, h2), D1.abnf.radix_rep(t2, rx), hb))
    case False{}:
      match dd:
        case True{}:
          %Equal.sym(Bool, Char.is_eq(hh, '_'), False{}, eu) : {Bool.and(Bool.or(_, D1.abnf.radix_digit(rx, hh)),
            n1.rr(rx, h2 <> t2)) == True{} : Bool}
          %Equal.sym(Bool, D1.abnf.radix_digit(rx, hh), True{}, ed) : {Bool.and(Bool.or(False{}, _),
            n1.rr(rx, h2 <> t2)) == True{} : Bool}
          %Equal.sym(Bool, n1.rr(rx, h2 <> t2), True{}, i1(Equal.trans(Bool, D1.abnf.radix_rep(h2 <> t2, rx),
            D1.abnf.radix_rep(hh <> h2 <> t2, rx), True{}, n1.rrep.d(rx, hh, h2 <> t2, ed), hr))) :
            {Bool.and(Bool.or(False{}, True{}), _) == True{} : Bool}
          {==}
        case False{}:
          Eq.bit.absurd(&2, {n1.rr(rx, hh <> h2 <> t2) == True{} : Bool}, Equal.trans(Bool, False{},
            D1.abnf.radix_rep(hh <> h2 <> t2, rx), True{}, n1.rrep.n(rx, hh, h2 <> t2, ed, eu), hr))

# the radix's repetition is underscores and digits of the radix
def n1.rr.rep(
  xs: List<&2, Char>,
  +rx: D1.ARadix,
  +hr: {D1.abnf.radix_rep(xs, rx) == True{} : Bool}
) -> {n1.rr(rx, xs) == True{} : Bool}:
  match xs:
    case []:
      {==}
    case +hh <> tt:
      match tt:
        case []:
          %Equal.sym(Bool, D1.abnf.radix_digit(rx, hh), True{}, hr) : {Bool.and(Bool.or(Char.is_eq(hh, '_'), _),
            True{}) == True{} : Bool}
          %Equal.sym(Bool, Bool.or(Char.is_eq(hh, '_'), True{}), True{}, n1.or.t(Char.is_eq(hh, '_'))) :
            {Bool.and(_, True{}) == True{} : Bool}
          {==}
        case +h2 <> +t2:
          n1.rr.go(Char.is_eq(hh, '_'), D1.abnf.radix_digit(rx, hh), hh, h2, t2, rx, {==}, {==}, hr,
            h1 => n1.rr.rep(h2 <> t2, rx, h1), h3 => n1.rr.rep(t2, rx, h3))

# and so is a digit of the radix and the repetition
def n1.rr.bg(
  xs: List<&2, Char>,
  +rx: D1.ARadix,
  +hb: {n1.bg(xs, rx) == True{} : Bool}
) -> {n1.rr(rx, xs) == True{} : Bool}:
  match xs:
    case []:
      Eq.bit.absurd(&2, {n1.rr(rx, []) == True{} : Bool}, hb)
    case +hh <> +tt:
      %Equal.sym(Bool, D1.abnf.radix_digit(rx, hh), True{}, Eq.and.left(D1.abnf.radix_digit(rx, hh),
        D1.abnf.radix_rep(tt, rx), hb)) : {Bool.and(Bool.or(Char.is_eq(hh, '_'), _), n1.rr(rx, tt)) == True{}
        : Bool}
      %Equal.sym(Bool, Bool.or(Char.is_eq(hh, '_'), True{}), True{}, n1.or.t(Char.is_eq(hh, '_'))) :
        {Bool.and(_, n1.rr(rx, tt)) == True{} : Bool}
      n1.rr.rep(tt, rx, Eq.and.right(D1.abnf.radix_digit(rx, hh), D1.abnf.radix_rep(tt, rx), hb))

# a character that is no underscore, of the underscores and digits, is a
# digit of the radix
def n1.rr.d(
  +hh: Char,
  +rx: D1.ARadix,
  +eu: {Char.is_eq(hh, '_') == False{} : Bool},
  +ho: {Bool.or(Char.is_eq(hh, '_'), D1.abnf.radix_digit(rx, hh)) == True{} : Bool}
) -> {D1.abnf.radix_digit(rx, hh) == True{} : Bool}:
  Equal.trans(Bool, D1.abnf.radix_digit(rx, hh), Bool.or(False{}, D1.abnf.radix_digit(rx, hh)), True{}, {==},
    Equal.trans(Bool, Bool.or(False{}, D1.abnf.radix_digit(rx, hh)), Bool.or(Char.is_eq(hh, '_'),
    D1.abnf.radix_digit(rx, hh)), True{}, Equal.cong(Bool, Bool, bb => Bool.or(bb, D1.abnf.radix_digit(rx,
    hh)), False{}, Char.is_eq(hh, '_'), Equal.sym(Bool, Char.is_eq(hh, '_'), False{}, eu)), ho))

# what cvW claims of the rest, from a numeral es
def n1.cvW.go.P1(+rx: D1.ARadix, +tt: List<&2, Char>, +es: List<&2, U32>) -> Type:
  {n1.d10(es) == True{} : Bool} -> {n1.W(n1.cv(rx, tt, es)) == D1.g.num.nat(tt, U32.to_nat(n1.rb(rx)), n1.W(es))
    : Nat}

# a character of the reading, by whether it is an underscore: its value goes
# on from what the numeral counts
def n1.cvW.go(
  uu: Bool,
  +vv: Unit,
  +rx: D1.ARadix,
  +hh: Char,
  +tt: List<&2, Char>,
  +ds: List<&2, U32>,
  +eu: {Char.is_eq(hh, '_') == uu : Bool},
  +hd: {n1.d10(ds) == True{} : Bool},
  +ho: {Bool.or(Char.is_eq(hh, '_'), D1.abnf.radix_digit(rx, hh)) == True{} : Bool},
  ih: @es:List<&2, U32> -> n1.cvW.go.P1(rx, tt, es)
) -> {n1.W(n1.cv(rx, tt, n1.cv.s(uu, rx, hh, ds))) == D1.g.num.nat(tt, U32.to_nat(n1.rb(rx)),
  D1.g.num.nat.step(D1.abnf.underscore(hh), hh, U32.to_nat(n1.rb(rx)), n1.W(ds))) : Nat}:
  match uu:
    case True{}:
      %Equal.sym(Bool, D1.abnf.underscore(hh), True{}, Equal.trans(Bool, D1.abnf.underscore(hh),
        Char.is_eq(hh, '_'), True{}, Equal.sym(Bool, Char.is_eq(hh, '_'), D1.abnf.underscore(hh), M7.n1.us(hh)), eu)) :
        {n1.W(n1.cv(rx, tt, ds)) == D1.g.num.nat(tt, U32.to_nat(n1.rb(rx)), D1.g.num.nat.step(_, hh,
        U32.to_nat(n1.rb(rx)), n1.W(ds))) : Nat}
      ih(ds, hd)
    case False{}:
      +hr = {n1.rr.d(hh, rx, eu, ho) : {D1.abnf.radix_digit(rx, hh) == True{} : Bool}}
      +hc = {Equal.trans(Bool, T.dig.ok(T.dig.val(hh), n1.rb(rx)), D1.abnf.radix_digit(rx, hh), True{}, n1.cls(rx,
        hh), hr) : {U32.is_lt(T.dig.val(hh), n1.rb(rx)) == True{} : Bool}}
      %Equal.sym(Bool, D1.abnf.underscore(hh), False{}, Equal.trans(Bool, D1.abnf.underscore(hh),
        Char.is_eq(hh, '_'), False{}, Equal.sym(Bool, Char.is_eq(hh, '_'), D1.abnf.underscore(hh), M7.n1.us(hh)), eu)) :
        {n1.W(n1.cv(rx, tt, T.dec.go(ds, n1.rb(rx), T.dig.val(hh)))) == D1.g.num.nat(tt, U32.to_nat(n1.rb(rx)),
        D1.g.num.nat.step(_, hh, U32.to_nat(n1.rb(rx)), n1.W(ds))) : Nat}
      %n1.dv(rx, hh, hr) : {n1.W(n1.cv(rx, tt, T.dec.go(ds, n1.rb(rx), T.dig.val(hh)))) == D1.g.num.nat(tt,
        U32.to_nat(n1.rb(rx)), Nat.add(Nat.mul(n1.W(ds), U32.to_nat(n1.rb(rx))), _)) : Nat}
      %n1.Wgo(vv, ds, rx, T.dig.val(hh), hd, hc) : {n1.W(n1.cv(rx, tt, T.dec.go(ds, n1.rb(rx), T.dig.val(hh))))
        == D1.g.num.nat(tt, U32.to_nat(n1.rb(rx)), _) : Nat}
      ih(T.dec.go(ds, n1.rb(rx), T.dig.val(hh)), n1.Wok(vv, ds, rx, T.dig.val(hh), hd, hc))

# the reading counts the digits' value in the radix, after what the numeral
# counts
def n1.cvW(
  +vv: Unit,
  +rx: D1.ARadix,
  xs: List<&2, Char>,
  +ds: List<&2, U32>,
  +hd: {n1.d10(ds) == True{} : Bool},
  +hx: {n1.rr(rx, xs) == True{} : Bool}
) -> {n1.W(n1.cv(rx, xs, ds)) == D1.g.num.nat(xs, U32.to_nat(n1.rb(rx)), n1.W(ds)) : Nat}:
  match xs:
    case []:
      {==}
    case +hh <> +tt:
      n1.cvW.go(Char.is_eq(hh, '_'), vv, rx, hh, tt, ds, {==}, hd, Eq.and.left(Bool.or(Char.is_eq(hh, '_'),
        D1.abnf.radix_digit(rx, hh)), n1.rr(rx, tt), hx), es => he => n1.cvW(vv, rx, tt, es, he,
        Eq.and.right(Bool.or(Char.is_eq(hh, '_'), D1.abnf.radix_digit(rx, hh)), n1.rr(rx, tt), hx)))

# a character of the reading leaves digits below ten
def n1.cvok.go(
  uu: Bool,
  +vv: Unit,
  +rx: D1.ARadix,
  +hh: Char,
  +tt: List<&2, Char>,
  +ds: List<&2, U32>,
  +eu: {Char.is_eq(hh, '_') == uu : Bool},
  +hd: {n1.d10(ds) == True{} : Bool},
  +ho: {Bool.or(Char.is_eq(hh, '_'), D1.abnf.radix_digit(rx, hh)) == True{} : Bool},
  ih: @es:List<&2, U32> -> {n1.d10(es) == True{} : Bool} -> {n1.d10(n1.cv(rx, tt, es)) == True{} : Bool}
) -> {n1.d10(n1.cv(rx, tt, n1.cv.s(uu, rx, hh, ds))) == True{} : Bool}:
  match uu:
    case True{}:
      ih(ds, hd)
    case False{}:
      ih(T.dec.go(ds, n1.rb(rx), T.dig.val(hh)), n1.Wok(vv, ds, rx, T.dig.val(hh), hd, Equal.trans(Bool,
        T.dig.ok(T.dig.val(hh), n1.rb(rx)), D1.abnf.radix_digit(rx, hh), True{}, n1.cls(rx, hh), n1.rr.d(hh, rx,
        eu, ho))))

# the reading is digits below ten
def n1.cvok(
  +vv: Unit,
  +rx: D1.ARadix,
  xs: List<&2, Char>,
  +ds: List<&2, U32>,
  +hd: {n1.d10(ds) == True{} : Bool},
  +hx: {n1.rr(rx, xs) == True{} : Bool}
) -> {n1.d10(n1.cv(rx, xs, ds)) == True{} : Bool}:
  match xs:
    case []:
      hd
    case +hh <> +tt:
      n1.cvok.go(Char.is_eq(hh, '_'), vv, rx, hh, tt, ds, {==}, hd, Eq.and.left(Bool.or(Char.is_eq(hh, '_'),
        D1.abnf.radix_digit(rx, hh)), n1.rr(rx, tt), hx), es => he => n1.cvok(vv, rx, tt, es, he,
        Eq.and.right(Bool.or(Char.is_eq(hh, '_'), D1.abnf.radix_digit(rx, hh)), n1.rr(rx, tt), hx)))

# The limits. 2^63 is 8 * 16^15, 8^21 and 2^63, and the checker would
# expand any of them, or the value of "9223372036854775808", to unary to
# compare it. So each is named behind a unit uu, and the digits of each are
# computed as small Nats: 8 multiplied by 16 fifteen times, 1 by 8 twenty-one
# times, 1 by 2 sixty-three times, least-significant digit first, and checked
# against the limit's characters.

# whether two Nats are equal
def n1.eqn(aa: Nat, bb: Nat, +hh: {Nat.is_eq(aa, bb) == True{} : Bool}) -> {aa == bb : Nat}:
  match aa bb:
    case 0n 0n:
      {==}
    case 0n 1n+_b:
      Eq.bit.absurd(&2, {0n == 1n+_b : Nat}, hh)
    case 1n+_a 0n:
      Eq.bit.absurd(&2, {1n+_a == 0n : Nat}, hh)
    case 1n+(+a1) 1n+(+b1):
      Equal.cong(Nat, Nat, nn => 1n+nn, a1, b1, n1.eqn(a1, b1, hh))

# one more than a quotient and remainder by ten: the remainder goes up, or
# after 9 the quotient does
def n1.dq.t(nine: Bool, qq: Nat, mm: Nat) -> Nat & Nat:
  match nine:
    case True{}:
      (1n+qq, 0n)
    case False{}:
      (qq, 1n+mm)

# one more than a quotient and remainder
def n1.dq.n(pr: Nat & Nat) -> Nat & Nat:
  match pr:
    case (+qq, +mm):
      n1.dq.t(Nat.is_eq(mm, 9n), qq, mm)

# a Nat's quotient and remainder by ten, counted up one at a time
def n1.dq(xx: Nat) -> Nat & Nat:
  match xx:
    case 0n:
      (0n, 0n)
    case 1n+pp:
      n1.dq.n(n1.dq(pp))

# the quotient of a pair
def n1.pq(pr: Nat & Nat) -> Nat:
  match pr:
    case (qq, _m):
      qq

# the remainder of a pair
def n1.pm(pr: Nat & Nat) -> Nat:
  match pr:
    case (_q, mm):
      mm

# what a quotient and remainder by ten are worth
def n1.pv(pr: Nat & Nat) -> Nat:
  match pr:
    case (qq, mm):
      Nat.add(Nat.mul(qq, 10n), mm)

# which is the quotient's and the remainder's
def n1.pv.e(pr: Nat & Nat) -> {n1.pv(pr) == Nat.add(Nat.mul(n1.pq(pr), 10n), n1.pm(pr)) : Nat}:
  match pr:
    case (_q, _m):
      {==}

# one more, by whether the remainder was 9
def n1.dq.tv(
  nine: Bool,
  +qq: Nat,
  +mm: Nat,
  +en: {Nat.is_eq(mm, 9n) == nine : Bool}
) -> {n1.pv(n1.dq.t(nine, qq, mm)) == 1n+Nat.add(Nat.mul(qq, 10n), mm) : Nat}:
  match nine:
    case True{}:
      %Equal.sym(Nat, mm, 9n, n1.eqn(mm, 9n, en)) : {Nat.add(Nat.mul(1n+qq, 10n), 0n) == 1n+Nat.add(Nat.mul(qq, 10n), _)
        : Nat}
      %Equal.sym(Nat, Nat.add(Nat.mul(qq, 10n), 9n), Nat.add(9n, Nat.mul(qq, 10n)), Ar.nat_add_comm(Nat.mul(qq, 10n),
        9n)) : {Nat.add(Nat.mul(1n+qq, 10n), 0n) == 1n+_ : Nat}
      Ar.nat_add_zero(Nat.mul(1n+qq, 10n))
    case False{}:
      Ar.nat_add_succ(Nat.mul(qq, 10n), mm)

# one more than a pair is worth one more
def n1.dq.nv(pr: Nat & Nat) -> {n1.pv(n1.dq.n(pr)) == 1n+n1.pv(pr) : Nat}:
  match pr:
    case (+qq, +mm):
      n1.dq.tv(Nat.is_eq(mm, 9n), qq, mm, {==})

# a Nat is its quotient by ten times ten and its remainder
def n1.qr(xx: Nat) -> {n1.pv(n1.dq(xx)) == xx : Nat}:
  match xx:
    case 0n:
      {==}
    case 1n+(+pp):
      Equal.trans(Nat, n1.pv(n1.dq.n(n1.dq(pp))), 1n+n1.pv(n1.dq(pp)), 1n+pp, n1.dq.nv(n1.dq(pp)), Equal.cong(Nat,
        Nat, nn => 1n+nn, n1.pv(n1.dq(pp)), pp, n1.qr(pp)))

# small Nats as the digits of a numeral, least-significant first
def n1.nv(ds: List<&2, Nat>) -> Nat:
  match ds:
    case []:
      0n
    case dd <> tt:
      Nat.add(Nat.mul(n1.nv(tt), 10n), dd)

# a carry below 100 as its digits, least-significant first: none for 0
def n1.ec(zq: Bool, zm: Bool, qq: Nat, mm: Nat) -> List<&2, Nat>:
  match zq zm:
    case True{} True{}:
      []
    case True{} False{}:
      [mm]
    case False{} _z:
      [mm, qq]

# a carry's quotient and remainder as its digits
def n1.ep(pr: Nat & Nat) -> List<&2, Nat>:
  match pr:
    case (+qq, +mm):
      n1.ec(Nat.is_eq(qq, 0n), Nat.is_eq(mm, 0n), qq, mm)

# the digit a step leaves, and the rest times r after the step's carry
def n1.mq(ds: List<&2, Nat>, pr: Nat & Nat, +rr: Nat) -> List<&2, Nat>:
  match ds:
    case []:
      match pr:
        case (qq, mm):
          mm <> n1.ep(n1.dq(qq))
    case dd <> tt:
      match pr:
        case (qq, mm):
          mm <> n1.mq(tt, n1.dq(Nat.add(Nat.mul(dd, rr), qq)), rr)

# small-Nat digits times r and a carry
def n1.mr(ds: List<&2, Nat>, +rr: Nat, cc: Nat) -> List<&2, Nat>:
  match ds:
    case []:
      n1.ep(n1.dq(cc))
    case dd <> tt:
      n1.mq(tt, n1.dq(Nat.add(Nat.mul(dd, rr), cc)), rr)

# a carry's digits are worth its quotient and remainder
def n1.ec.v(
  zq: Bool,
  zm: Bool,
  +qq: Nat,
  +mm: Nat,
  +eq: {Nat.is_eq(qq, 0n) == zq : Bool},
  +em: {Nat.is_eq(mm, 0n) == zm : Bool}
) -> {n1.nv(n1.ec(zq, zm, qq, mm)) == Nat.add(Nat.mul(qq, 10n), mm) : Nat}:
  match zq zm:
    case True{} True{}:
      %Equal.sym(Nat, qq, 0n, n1.eqn(qq, 0n, eq)) : {0n == Nat.add(Nat.mul(_, 10n), mm) : Nat}
      Equal.sym(Nat, mm, 0n, n1.eqn(mm, 0n, em))
    case True{} False{}:
      %Equal.sym(Nat, qq, 0n, n1.eqn(qq, 0n, eq)) : {n1.nv([mm]) == Nat.add(Nat.mul(_, 10n), mm) : Nat}
      {==}
    case False{} _z:
      {==}

# a pair's digits are worth the pair
def n1.ep.pv(pr: Nat & Nat) -> {n1.nv(n1.ep(pr)) == n1.pv(pr) : Nat}:
  match pr:
    case (+qq, +mm):
      n1.ec.v(Nat.is_eq(qq, 0n), Nat.is_eq(mm, 0n), qq, mm, {==}, {==})

# a Nat is its quotient and remainder by ten
def n1.pq.x(+xx: Nat) -> {Nat.add(Nat.mul(n1.pq(n1.dq(xx)), 10n), n1.pm(n1.dq(xx))) == xx : Nat}:
  Equal.trans(Nat, Nat.add(Nat.mul(n1.pq(n1.dq(xx)), 10n), n1.pm(n1.dq(xx))), n1.pv(n1.dq(xx)), xx, Equal.sym(Nat,
    n1.pv(n1.dq(xx)), Nat.add(Nat.mul(n1.pq(n1.dq(xx)), 10n), n1.pm(n1.dq(xx))), n1.pv.e(n1.dq(xx))), n1.qr(xx))

# a carry's digits are worth the carry
def n1.ep.v(+xx: Nat) -> {n1.nv(n1.ep(n1.dq(xx))) == xx : Nat}:
  Equal.trans(Nat, n1.nv(n1.ep(n1.dq(xx))), n1.pv(n1.dq(xx)), xx, n1.ep.pv(n1.dq(xx)), n1.qr(xx))

# a step's value
def n1.mq.v(
  ds: List<&2, Nat>,
  pr: Nat & Nat,
  +rr: Nat
) -> {n1.nv(n1.mq(ds, pr, rr)) == Nat.add(Nat.mul(Nat.add(Nat.mul(n1.nv(ds), rr), n1.pq(pr)), 10n), n1.pm(pr)) : Nat}:
  match ds:
    case []:
      match pr:
        case (+qq, +mm):
          Equal.cong(Nat, Nat, nn => Nat.add(Nat.mul(nn, 10n), mm), n1.nv(n1.ep(n1.dq(qq))), qq, n1.ep.v(qq))
    case +dd <> +tt:
      match pr:
        case (+qq, +mm):
          %Equal.sym(Nat, n1.nv(n1.mq(tt, n1.dq(Nat.add(Nat.mul(dd, rr), qq)), rr)), Nat.add(Nat.mul(Nat.add(
            Nat.mul(n1.nv(tt), rr), n1.pq(n1.dq(Nat.add(Nat.mul(dd, rr), qq)))), 10n), n1.pm(n1.dq(Nat.add(
            Nat.mul(dd, rr), qq)))), n1.mq.v(tt, n1.dq(Nat.add(Nat.mul(dd, rr), qq)), rr)) : {Nat.add(Nat.mul(_,
            10n), mm) == Nat.add(Nat.mul(Nat.add(Nat.mul(n1.nv(dd <> tt), rr), qq), 10n), mm) : Nat}
          Equal.cong(Nat, Nat, nn => Nat.add(Nat.mul(nn, 10n), mm), Nat.add(Nat.mul(Nat.add(Nat.mul(n1.nv(tt), rr),
            n1.pq(n1.dq(Nat.add(Nat.mul(dd, rr), qq)))), 10n), n1.pm(n1.dq(Nat.add(Nat.mul(dd, rr), qq)))),
            Nat.add(Nat.mul(n1.nv(dd <> tt), rr), qq), n1.alg(n1.nv(tt), rr, n1.pq(n1.dq(Nat.add(Nat.mul(dd, rr),
            qq))), n1.pm(n1.dq(Nat.add(Nat.mul(dd, rr), qq))), dd, qq, n1.pq.x(Nat.add(Nat.mul(dd, rr), qq))))

# the digits times r and a carry are worth their value times r and the carry
def n1.mrv(
  ds: List<&2, Nat>,
  +rr: Nat,
  +cc: Nat
) -> {n1.nv(n1.mr(ds, rr, cc)) == Nat.add(Nat.mul(n1.nv(ds), rr), cc) : Nat}:
  match ds:
    case []:
      n1.ep.v(cc)
    case +dd <> +tt:
      Equal.trans(Nat, n1.nv(n1.mq(tt, n1.dq(Nat.add(Nat.mul(dd, rr), cc)), rr)), Nat.add(Nat.mul(Nat.add(Nat.mul(
        n1.nv(tt), rr), n1.pq(n1.dq(Nat.add(Nat.mul(dd, rr), cc)))), 10n), n1.pm(n1.dq(Nat.add(Nat.mul(dd, rr), cc)))),
        Nat.add(Nat.mul(n1.nv(dd <> tt), rr), cc), n1.mq.v(tt, n1.dq(Nat.add(Nat.mul(dd, rr), cc)), rr),
        n1.alg(n1.nv(tt), rr, n1.pq(n1.dq(Nat.add(Nat.mul(dd, rr), cc))), n1.pm(n1.dq(Nat.add(Nat.mul(dd, rr), cc))),
        dd, cc, n1.pq.x(Nat.add(Nat.mul(dd, rr), cc))))

# small-Nat digits times r, k times
def n1.mi(ds: List<&2, Nat>, +rr: Nat, kk: Nat) -> List<&2, Nat>:
  match kk:
    case 0n:
      ds
    case 1n+pp:
      n1.mr(n1.mi(ds, rr, pp), rr, 0n)

# are worth their value times r to the k
def n1.miv(
  +ds: List<&2, Nat>,
  +rr: Nat,
  kk: Nat
) -> {n1.nv(n1.mi(ds, rr, kk)) == Nat.mul(n1.nv(ds), Nat.pow(rr, kk)) : Nat}:
  match kk:
    case 0n:
      Equal.sym(Nat, Nat.mul(n1.nv(ds), 1n), n1.nv(ds), Ar.nat_mul_one(n1.nv(ds)))
    case 1n+(+pp):
      %Equal.sym(Nat, n1.nv(n1.mr(n1.mi(ds, rr, pp), rr, 0n)), Nat.add(Nat.mul(n1.nv(n1.mi(ds, rr, pp)), rr), 0n),
        n1.mrv(n1.mi(ds, rr, pp), rr, 0n)) : {_ == Nat.mul(n1.nv(ds), Nat.mul(rr, Nat.pow(rr, pp))) : Nat}
      %Equal.sym(Nat, Nat.add(Nat.mul(n1.nv(n1.mi(ds, rr, pp)), rr), 0n), Nat.mul(n1.nv(n1.mi(ds, rr, pp)), rr),
        Ar.nat_add_zero(Nat.mul(n1.nv(n1.mi(ds, rr, pp)), rr))) : {_ == Nat.mul(n1.nv(ds), Nat.mul(rr, Nat.pow(rr,
        pp))) : Nat}
      %Equal.sym(Nat, n1.nv(n1.mi(ds, rr, pp)), Nat.mul(n1.nv(ds), Nat.pow(rr, pp)), n1.miv(ds, rr, pp)) :
        {Nat.mul(_, rr) == Nat.mul(n1.nv(ds), Nat.mul(rr, Nat.pow(rr, pp))) : Nat}
      Equal.trans(Nat, Nat.mul(Nat.mul(n1.nv(ds), Nat.pow(rr, pp)), rr), Nat.mul(n1.nv(ds), Nat.mul(Nat.pow(rr, pp),
        rr)), Nat.mul(n1.nv(ds), Nat.mul(rr, Nat.pow(rr, pp))), Ar.nat_mul_assoc(n1.nv(ds), Nat.pow(rr, pp), rr),
        Equal.cong(Nat, Nat, nn => Nat.mul(n1.nv(ds), nn), Nat.mul(Nat.pow(rr, pp), rr), Nat.mul(rr, Nat.pow(rr,
        pp)), n1.mulc(Nat.pow(rr, pp), rr)))

# small Nats' value from the most significant, after acc
def n1.gm(ns: List<&2, Nat>, acc: Nat) -> Nat:
  match ns:
    case []:
      acc
    case mm <> nt:
      n1.gm(nt, Nat.add(Nat.mul(acc, 10n), mm))

# reversed onto acc, least-significant digits are acc's after their value
def n1.rvg(
  ds: List<&2, Nat>,
  +acc: List<&2, Nat>
) -> {n1.gm(List.reverse.go(&2, Nat, ds, acc), 0n) == n1.gm(acc, n1.nv(ds)) : Nat}:
  match ds:
    case []:
      {==}
    case +dd <> +tt:
      n1.rvg(tt, dd <> acc)

# whether characters spell small Nats, each a digit no underscore of that
# value
def n1.spl(cs: List<&2, Char>, ns: List<&2, Nat>) -> Bool:
  match cs:
    case []:
      List.is_empty(&2, Nat, ns)
    case +hh <> ct:
      match ns:
        case []:
          False{}
        case mm <> nt:
          Bool.and(Bool.not(D1.abnf.underscore(hh)), Bool.and(Nat.is_eq(D1.g.hexdig.val(hh), mm), n1.spl(ct,
            nt)))

# characters that spell small Nats are worth what they are
def n1.splv(
  cs: List<&2, Char>,
  ns: List<&2, Nat>,
  +acc: Nat,
  +hs: {n1.spl(cs, ns) == True{} : Bool}
) -> {D1.g.num.nat(cs, 10n, acc) == n1.gm(ns, acc) : Nat}:
  match cs:
    case []:
      match ns:
        case []:
          {==}
        case _m <> _mt:
          Eq.bit.absurd(&2, {D1.g.num.nat([], 10n, acc) == n1.gm(_m <> _mt, acc) : Nat}, hs)
    case +hh <> +ct:
      match ns:
        case []:
          Eq.bit.absurd(&2, {D1.g.num.nat(hh <> ct, 10n, acc) == n1.gm([], acc) : Nat}, hs)
        case +mm <> +nt:
          +hu = {Eq.and.left(Bool.not(D1.abnf.underscore(hh)), Bool.and(Nat.is_eq(D1.g.hexdig.val(hh), mm),
            n1.spl(ct, nt)), hs) : {Bool.not(D1.abnf.underscore(hh)) == True{} : Bool}}
          +hr = {Eq.and.right(Bool.not(D1.abnf.underscore(hh)), Bool.and(Nat.is_eq(D1.g.hexdig.val(hh), mm),
            n1.spl(ct, nt)), hs) : {Bool.and(Nat.is_eq(D1.g.hexdig.val(hh), mm), n1.spl(ct, nt)) == True{} : Bool}}
          Equal.trans(Nat, D1.g.num.nat(hh <> ct, 10n, acc), D1.g.num.nat(ct, 10n, Nat.add(Nat.mul(acc, 10n),
            D1.g.hexdig.val(hh))), n1.gm(mm <> nt, acc), n1.gn.step(hh, ct, 10n, acc, hu), Equal.trans(Nat,
            D1.g.num.nat(ct, 10n, Nat.add(Nat.mul(acc, 10n), D1.g.hexdig.val(hh))), n1.gm(nt,
            Nat.add(Nat.mul(acc, 10n), D1.g.hexdig.val(hh))), n1.gm(nt, Nat.add(Nat.mul(acc, 10n), mm)),
            n1.splv(ct, nt, Nat.add(Nat.mul(acc, 10n), D1.g.hexdig.val(hh)), Eq.and.right(Nat.is_eq(
            D1.g.hexdig.val(hh), mm), n1.spl(ct, nt), hr)), Equal.cong(Nat, Nat, nn => n1.gm(nt,
            Nat.add(Nat.mul(acc, 10n), nn)), D1.g.hexdig.val(hh), mm, n1.eqn(D1.g.hexdig.val(hh), mm,
            Eq.and.left(Nat.is_eq(D1.g.hexdig.val(hh), mm), n1.spl(ct, nt), hr)))))

# a numeral's value in base 10, once uu is known
def n1.hu(+ss: String, uu: Unit) -> Nat:
  match uu:
    case Unit{}:
      n1.h10(ss)

# small-Nat digits' value, once uu is known
def n1.nvu(+ds: List<&2, Nat>, uu: Unit) -> Nat:
  match uu:
    case Unit{}:
      n1.nv(ds)

# a numeral that spells small-Nat digits, the most significant first, is
# worth what they are
def n1.cert(
  +ss: String,
  +ds: List<&2, Nat>,
  +hs: {n1.spl(String.to_list(ss), List.reverse(&2, Nat, ds)) == True{} : Bool},
  uu: Unit
) -> {n1.hu(ss, uu) == n1.nvu(ds, uu) : Nat}:
  match uu:
    case Unit{}:
      Equal.trans(Nat, n1.h10(ss), n1.gm(List.reverse(&2, Nat, ds), 0n), n1.nv(ds), n1.splv(String.to_list(ss),
        List.reverse(&2, Nat, ds), 0n, hs), n1.rvg(ds, []))

# a small Nat's digits times r to the k, once uu is known
def n1.pb(+ds: List<&2, Nat>, +rr: Nat, +kk: Nat, uu: Unit) -> Nat:
  match uu:
    case Unit{}:
      Nat.mul(n1.nv(ds), Nat.pow(rr, kk))

# digits times r, k times, once uu is known, are worth their value times r
# to the k
def n1.miu(
  +ds: List<&2, Nat>,
  +rr: Nat,
  +kk: Nat,
  uu: Unit
) -> {n1.nvu(n1.mi(ds, rr, kk), uu) == n1.pb(ds, rr, kk, uu) : Nat}:
  match uu:
    case Unit{}:
      n1.miv(ds, rr, kk)

# the type of n1.lim's hs
def n1.lim.P1(+ds: List<&2, Nat>, +rr: Nat, +kk: Nat) -> Type:
  {n1.spl(String.to_list(T.i64.limit(T.Minus{})), List.reverse(&2, Nat, n1.mi(ds, rr, kk))) == True{} : Bool}

# the limit of a minus, as digits times a radix to a power
def n1.lim(
  +ds: List<&2, Nat>,
  +rr: Nat,
  +kk: Nat,
  hs: n1.lim.P1(ds, rr, kk),
  +uu: Unit
) -> {n1.hu(T.i64.limit(T.Minus{}), uu) == n1.pb(ds, rr, kk, uu) : Nat}:
  Equal.trans(Nat, n1.hu(T.i64.limit(T.Minus{}), uu), n1.nvu(n1.mi(ds, rr, kk), uu), n1.pb(ds, rr, kk, uu),
    n1.cert(T.i64.limit(T.Minus{}), n1.mi(ds, rr, kk), hs, uu), n1.miu(ds, rr, kk, uu))

# 2^63 is 8 * 16^15
def n1.lim.x(+uu: Unit) -> {n1.hu(T.i64.limit(T.Minus{}), uu) == n1.pb([8n], 16n, 15n, uu) : Nat}:
  n1.lim([8n], 16n, 15n, {==}, uu)

# and 8^21
def n1.lim.o(+uu: Unit) -> {n1.hu(T.i64.limit(T.Minus{}), uu) == n1.pb([1n], 8n, 21n, uu) : Nat}:
  n1.lim([1n], 8n, 21n, {==}, uu)

# and 2^63
def n1.lim.b(+uu: Unit) -> {n1.hu(T.i64.limit(T.Minus{}), uu) == n1.pb([1n], 2n, 63n, uu) : Nat}:
  n1.lim([1n], 2n, 63n, {==}, uu)

# A prefixed integer's significant digits (prose.sig: its underscores and
# leading zeros removed) are worth what its digits are, start with a digit
# other than 0, and bound its value by their number.

# whether every character is a digit of the radix
def n1.rdl(+rx: D1.ARadix, xs: List<&2, Char>) -> Bool:
  match xs:
    case []:
      True{}
    case hh <> tt:
      Bool.and(D1.abnf.radix_digit(rx, hh), n1.rdl(rx, tt))

# whether characters are digits of the radix, the first not 0
def n1.sgk(+rx: D1.ARadix, xs: List<&2, Char>) -> Bool:
  match xs:
    case []:
      True{}
    case +hh <> tt:
      Bool.and(Bool.not(D1.abnf.cp(hh, 48)), Bool.and(D1.abnf.radix_digit(rx, hh), n1.rdl(rx, tt)))

# the left of an `or` that answered False
def n1.orF.l(aa: Bool, +bb: Bool, +hh: {Bool.or(aa, bb) == False{} : Bool}) -> {aa == False{} : Bool}:
  match aa:
    case True{}:
      hh
    case False{}:
      {==}

# and its right
def n1.orF.r(aa: Bool, +bb: Bool, +hh: {Bool.or(aa, bb) == False{} : Bool}) -> {bb == False{} : Bool}:
  match aa:
    case True{}:
      Eq.bit.absurd2(&2, {bb == False{} : Bool}, hh)
    case False{}:
      hh

# a character by whether it is an underscore: the value goes on as over the
# characters with the underscores removed
def n1.gnu.go(
  uu: Bool,
  +hh: Char,
  +tt: List<&2, Char>,
  +rr: Nat,
  +acc: Nat,
  +eu: {D1.abnf.underscore(hh) == uu : Bool},
  ih: @aa:Nat -> {D1.g.num.nat(tt, rr, aa) == D1.g.num.nat(String.to_list(D1.abnf.no_us(tt)), rr, aa) : Nat}
) -> {D1.g.num.nat(tt, rr, D1.g.num.nat.step(uu, hh, rr, acc)) == D1.g.num.nat(String.to_list(
  D1.abnf.no_us.pick(uu, hh, D1.abnf.no_us(tt))), rr, acc) : Nat}:
  match uu:
    case True{}:
      ih(acc)
    case False{}:
      %Equal.sym(Bool, D1.abnf.underscore(hh), False{}, eu) : {D1.g.num.nat(tt, rr, Nat.add(Nat.mul(acc, rr),
        D1.g.hexdig.val(hh))) == D1.g.num.nat(String.to_list(D1.abnf.no_us(tt)), rr, D1.g.num.nat.step(_, hh,
        rr, acc)) : Nat}
      ih(Nat.add(Nat.mul(acc, rr), D1.g.hexdig.val(hh)))

# underscores add nothing to the value
def n1.gnu(
  xs: List<&2, Char>,
  +rr: Nat,
  +acc: Nat
) -> {D1.g.num.nat(xs, rr, acc) == D1.g.num.nat(String.to_list(D1.abnf.no_us(xs)), rr, acc) : Nat}:
  match xs:
    case []:
      {==}
    case +hh <> +tt:
      n1.gnu.go(D1.abnf.underscore(hh), hh, tt, rr, acc, {==}, aa => n1.gnu(tt, rr, aa))

# an underscore or a 0 from 0 leaves 0
def n1.st0(
  uu: Bool,
  +hh: Char,
  +rr: Nat,
  +eu: {D1.abnf.underscore(hh) == uu : Bool},
  +ho: {Bool.or(D1.abnf.underscore(hh), D1.abnf.cp(hh, 48)) == True{} : Bool}
) -> {D1.g.num.nat.step(D1.abnf.underscore(hh), hh, rr, 0n) == 0n : Nat}:
  match uu:
    case True{}:
      %Equal.sym(Bool, D1.abnf.underscore(hh), True{}, eu) : {D1.g.num.nat.step(_, hh, rr, 0n) == 0n : Nat}
      {==}
    case False{}:
      +hz = {Equal.trans(Bool, D1.abnf.cp(hh, 48), Bool.or(False{}, D1.abnf.cp(hh, 48)), True{}, {==},
        Equal.trans(Bool, Bool.or(False{}, D1.abnf.cp(hh, 48)), Bool.or(D1.abnf.underscore(hh),
        D1.abnf.cp(hh, 48)), True{}, Equal.cong(Bool, Bool, bb => Bool.or(bb, D1.abnf.cp(hh, 48)), False{},
        D1.abnf.underscore(hh), Equal.sym(Bool, D1.abnf.underscore(hh), False{}, eu)), ho)) :
        {D1.abnf.cp(hh, 48) == True{} : Bool}}
      %Equal.sym(Char, hh, '0', Eq.char_eq_true(hh, '0', Equal.trans(Bool, Char.is_eq(hh, Chr{48}),
        D1.abnf.cp(hh, 48), True{}, n1.cp(hh, 48), hz))) : {D1.g.num.nat.step(D1.abnf.underscore(_), _, rr, 0n)
        == 0n : Nat}
      {==}

# a character by whether it is an underscore or a 0
def n1.gsig.go(
  bb: Bool,
  +hh: Char,
  +tt: List<&2, Char>,
  +rr: Nat,
  +eb: {Bool.or(D1.abnf.underscore(hh), D1.abnf.cp(hh, 48)) == bb : Bool},
  +ih: {D1.g.num.nat(tt, rr, 0n) == D1.g.num.nat(D1.prose.sig(tt), rr, 0n) : Nat}
) -> {D1.g.num.nat(hh <> tt, rr, 0n) == D1.g.num.nat(D1.prose.sig.pick(bb, hh, tt, D1.prose.sig(tt)), rr, 0n)
  : Nat}:
  match bb:
    case True{}:
      %Equal.sym(Nat, D1.g.num.nat.step(D1.abnf.underscore(hh), hh, rr, 0n), 0n, n1.st0(D1.abnf.underscore(hh),
        hh, rr, {==}, eb)) : {D1.g.num.nat(tt, rr, _) == D1.g.num.nat(D1.prose.sig(tt), rr, 0n) : Nat}
      ih
    case False{}:
      n1.gnu(hh <> tt, rr, 0n)

# the significant digits are worth what the digits are
def n1.gsig(
  xs: List<&2, Char>,
  +rr: Nat
) -> {D1.g.num.nat(xs, rr, 0n) == D1.g.num.nat(D1.prose.sig(xs), rr, 0n) : Nat}:
  match xs:
    case []:
      {==}
    case +hh <> +tt:
      n1.gsig.go(Bool.or(D1.abnf.underscore(hh), D1.abnf.cp(hh, 48)), hh, tt, rr, {==}, n1.gsig(tt, rr))

# a character by whether it is an underscore: with the underscores removed,
# digits of the radix
def n1.nurdl.go(
  uu: Bool,
  +rx: D1.ARadix,
  +hh: Char,
  +tt: List<&2, Char>,
  +eu: {D1.abnf.underscore(hh) == uu : Bool},
  +ho: {Bool.or(Char.is_eq(hh, '_'), D1.abnf.radix_digit(rx, hh)) == True{} : Bool},
  +ih: {n1.rdl(rx, String.to_list(D1.abnf.no_us(tt))) == True{} : Bool}
) -> {n1.rdl(rx, String.to_list(D1.abnf.no_us.pick(uu, hh, D1.abnf.no_us(tt)))) == True{} : Bool}:
  match uu:
    case True{}:
      ih
    case False{}:
      M9.and.tt(D1.abnf.radix_digit(rx, hh), n1.rdl(rx, String.to_list(D1.abnf.no_us(tt))), n1.rr.d(hh, rx,
        Equal.trans(Bool, Char.is_eq(hh, '_'), D1.abnf.underscore(hh), False{}, M7.n1.us(hh), eu), ho), ih)

# underscores and digits of the radix, with the underscores removed, are
# digits of the radix
def n1.nurdl(
  +rx: D1.ARadix,
  xs: List<&2, Char>,
  +hx: {n1.rr(rx, xs) == True{} : Bool}
) -> {n1.rdl(rx, String.to_list(D1.abnf.no_us(xs))) == True{} : Bool}:
  match xs:
    case []:
      {==}
    case +hh <> +tt:
      n1.nurdl.go(D1.abnf.underscore(hh), rx, hh, tt, {==}, Eq.and.left(Bool.or(Char.is_eq(hh, '_'),
        D1.abnf.radix_digit(rx, hh)), n1.rr(rx, tt), hx), n1.nurdl(rx, tt, Eq.and.right(Bool.or(Char.is_eq(hh, '_'),
        D1.abnf.radix_digit(rx, hh)), n1.rr(rx, tt), hx)))

# a character by whether it is an underscore or a 0: the significant digits
# start with a digit other than 0
def n1.sigk.go(
  bb: Bool,
  +rx: D1.ARadix,
  +hh: Char,
  +tt: List<&2, Char>,
  +eb: {Bool.or(D1.abnf.underscore(hh), D1.abnf.cp(hh, 48)) == bb : Bool},
  +ho: {Bool.or(Char.is_eq(hh, '_'), D1.abnf.radix_digit(rx, hh)) == True{} : Bool},
  +hr: {n1.rr(rx, tt) == True{} : Bool},
  +ih: {n1.sgk(rx, D1.prose.sig(tt)) == True{} : Bool}
) -> {n1.sgk(rx, D1.prose.sig.pick(bb, hh, tt, D1.prose.sig(tt))) == True{} : Bool}:
  match bb:
    case True{}:
      ih
    case False{}:
      +eu = {n1.orF.l(D1.abnf.underscore(hh), D1.abnf.cp(hh, 48), eb) : {D1.abnf.underscore(hh) == False{}
        : Bool}}
      +ez = {n1.orF.r(D1.abnf.underscore(hh), D1.abnf.cp(hh, 48), eb) : {D1.abnf.cp(hh, 48) == False{} : Bool}}
      %Equal.sym(Bool, D1.abnf.underscore(hh), False{}, eu) : {n1.sgk(rx, String.to_list(D1.abnf.no_us.pick(_, hh,
        D1.abnf.no_us(tt)))) == True{} : Bool}
      %Equal.sym(Bool, D1.abnf.cp(hh, 48), False{}, ez) : {Bool.and(Bool.not(_), Bool.and(D1.abnf.radix_digit(rx,
        hh), n1.rdl(rx, String.to_list(D1.abnf.no_us(tt))))) == True{} : Bool}
      M9.and.tt(D1.abnf.radix_digit(rx, hh), n1.rdl(rx, String.to_list(D1.abnf.no_us(tt))), n1.rr.d(hh, rx,
        Equal.trans(Bool, Char.is_eq(hh, '_'), D1.abnf.underscore(hh), False{}, M7.n1.us(hh), eu), ho), n1.nurdl(rx,
        tt, hr))

# the significant digits of underscores and digits of the radix are digits
# of the radix, the first not 0
def n1.sigk(
  +rx: D1.ARadix,
  xs: List<&2, Char>,
  +hx: {n1.rr(rx, xs) == True{} : Bool}
) -> {n1.sgk(rx, D1.prose.sig(xs)) == True{} : Bool}:
  match xs:
    case []:
      {==}
    case +hh <> +tt:
      +hr = {Eq.and.right(Bool.or(Char.is_eq(hh, '_'), D1.abnf.radix_digit(rx, hh)), n1.rr(rx, tt), hx)
        : {n1.rr(rx, tt) == True{} : Bool}}
      n1.sigk.go(Bool.or(D1.abnf.underscore(hh), D1.abnf.cp(hh, 48)), rx, hh, tt, {==}, Eq.and.left(Bool.or(
        Char.is_eq(hh, '_'), D1.abnf.radix_digit(rx, hh)), n1.rr(rx, tt), hx), hr, n1.sigk(rx, tt, hr))

# digits of the radix are no underscores
def n1.rdl.nou(
  +rx: D1.ARadix,
  xs: List<&2, Char>,
  +hx: {n1.rdl(rx, xs) == True{} : Bool}
) -> {n1.nou(xs) == True{} : Bool}:
  match xs:
    case []:
      {==}
    case +hh <> +tt:
      M9.and.tt(Bool.not(D1.abnf.underscore(hh)), n1.nou(tt), Equal.cong(Bool, Bool, bb => Bool.not(bb),
        D1.abnf.underscore(hh),
        False{}, Equal.sym(Bool, False{}, D1.abnf.underscore(hh), n1.rd.nus(Char.is_eq(hh, '_'), rx, hh, {==},
        Eq.and.left(D1.abnf.radix_digit(rx, hh), n1.rdl(rx, tt), hx)))), n1.rdl.nou(rx, tt,
        Eq.and.right(D1.abnf.radix_digit(rx, hh), n1.rdl(rx, tt), hx)))

# and worth less than the base
def n1.rdl.dlt(
  +rx: D1.ARadix,
  xs: List<&2, Char>,
  +hx: {n1.rdl(rx, xs) == True{} : Bool}
) -> {n1.dlt(xs, U32.to_nat(n1.rb(rx))) == True{} : Bool}:
  match xs:
    case []:
      {==}
    case +hh <> +tt:
      M9.and.tt(Nat.is_lt(D1.g.hexdig.val(hh), U32.to_nat(n1.rb(rx))), n1.dlt(tt, U32.to_nat(n1.rb(rx))), n1.dlr(rx,
        hh, Eq.and.left(D1.abnf.radix_digit(rx, hh), n1.rdl(rx, tt), hx)), n1.rdl.dlt(rx, tt,
        Eq.and.right(D1.abnf.radix_digit(rx, hh), n1.rdl(rx, tt), hx)))

# a power of a radix above 0 is above 0
def n1.pow.pos(
  +rr: Nat,
  +kk: Nat,
  +hr: {Nat.is_lt(0n, rr) == True{} : Bool}
) -> {Nat.is_lt(0n, Nat.pow(rr, kk)) == True{} : Bool}:
  n1.lt.le(0n, 1n, Nat.pow(rr, kk), {==}, Equal.trans(Bool, Nat.is_le(1n, Nat.pow(rr, kk)), Nat.is_le(Nat.pow(rr, 0n),
    Nat.pow(rr, kk)), True{}, {==}, n1.pw.mono(rr, 0n, kk, hr, n1.le0(kk))))

# a times P is below b times P for a below b and P above 0
def n1.mul.lt(
  aa: Nat,
  bb: Nat,
  +pp: Nat,
  +hh: {Nat.is_lt(aa, bb) == True{} : Bool},
  +hp: {Nat.is_lt(0n, pp) == True{} : Bool}
) -> {Nat.is_lt(Nat.mul(aa, pp), Nat.mul(bb, pp)) == True{} : Bool}:
  match aa bb:
    case _a 0n:
      Eq.bit.absurd(&2, {Nat.is_lt(Nat.mul(_a, pp), 0n) == True{} : Bool}, Equal.trans(Bool, False{}, Nat.is_lt(_a,
        0n), True{}, Equal.sym(Bool, Nat.is_lt(_a, 0n), False{}, M2.nlt.zero(_a)), hh))
    case 0n 1n+(+b1):
      M2.lt.add(0n, pp, Nat.mul(b1, pp), hp)
    case 1n+(+a1) 1n+(+b1):
      Equal.trans(Bool, Nat.is_lt(Nat.add(pp, Nat.mul(a1, pp)), Nat.add(pp, Nat.mul(b1, pp))),
        Nat.is_lt(Nat.mul(a1, pp), Nat.mul(b1, pp)), True{}, Equal.cong(Cmp, Bool, xx => Cmp.is_lt(xx),
        Nat.cmp(Nat.add(pp, Nat.mul(a1, pp)), Nat.add(pp, Nat.mul(b1, pp))), Nat.cmp(Nat.mul(a1, pp), Nat.mul(b1, pp)),
        n1.cmp.add(pp, Nat.mul(a1, pp), Nat.mul(b1, pp))), n1.mul.lt(a1, b1, pp, hh, hp))

# one more than a is at most b exactly when a is below b
def n1.les(aa: Nat, bb: Nat) -> {Nat.is_le(1n+aa, bb) == Nat.is_lt(aa, bb) : Bool}:
  match aa bb:
    case 0n 0n:
      {==}
    case 0n 1n+(+b1):
      n1.le0(b1)
    case 1n+_a 0n:
      {==}
    case 1n+(+a1) 1n+(+b1):
      n1.les(a1, b1)

# not below b is at least b
def n1.nlt.le(aa: Nat, bb: Nat, +hh: {Nat.is_lt(aa, bb) == False{} : Bool}) -> {Nat.is_le(bb, aa) == True{} : Bool}:
  match aa bb:
    case _a 0n:
      n1.le0(_a)
    case 0n 1n+_b:
      Eq.bit.absurd2(&2, {Nat.is_le(1n+_b, 0n) == True{} : Bool}, hh)
    case 1n+(+a1) 1n+(+b1):
      n1.nlt.le(a1, b1, hh)

# a Nat below itself is not
def n1.ltirr(aa: Nat) -> {Nat.is_lt(aa, aa) == False{} : Bool}:
  match aa:
    case 0n:
      {==}
    case 1n+(+a1):
      n1.ltirr(a1)

# a Nat equals itself
def n1.eqrefl(aa: Nat) -> {Nat.is_eq(aa, aa) == True{} : Bool}:
  match aa:
    case 0n:
      {==}
    case 1n+(+a1):
      n1.eqrefl(a1)

# Nats that compare equal are equal
def n1.ceqn(aa: Nat, bb: Nat, +hh: {Nat.cmp(aa, bb) == EQ{} : Cmp}) -> {aa == bb : Nat}:
  n1.eqn(aa, bb, Equal.cong(Cmp, Bool, cc => Cmp.is_eq(cc), Nat.cmp(aa, bb), EQ{}, hh))

# a comparison with 0 is never LT, so after an order it keeps being LT
# exactly when the order was
def n1.ord0(cc: Cmp, +xx: Nat) -> {Cmp.is_lt(T.i64.ord(cc, Nat.cmp(xx, 0n))) == Cmp.is_lt(cc) : Bool}:
  match cc:
    case EQ{}:
      M2.nlt.zero(xx)
    case LT{}:
      {==}
    case GT{}:
      {==}

# the value of a digit other than 0 of the radix and more after it
def n1.hsplit(
  +ff: Char,
  +tt: List<&2, Char>,
  +rr: Nat,
  +hn: {n1.nou(ff <> tt) == True{} : Bool}
) -> {D1.g.num.nat(ff <> tt, rr, 0n) == Nat.add(Nat.mul(D1.g.hexdig.val(ff), Nat.pow(rr, List.length(&2, Char,
  tt))), D1.g.num.nat(tt, rr, 0n)) : Nat}:
  Equal.trans(Nat, D1.g.num.nat(ff <> tt, rr, 0n), D1.g.num.nat(tt, rr, D1.g.hexdig.val(ff)),
    Nat.add(Nat.mul(D1.g.hexdig.val(ff), Nat.pow(rr, List.length(&2, Char, tt))), D1.g.num.nat(tt, rr, 0n)),
    n1.gn.step(ff, tt, rr, 0n, Eq.and.left(Bool.not(D1.abnf.underscore(ff)), n1.nou(tt), hn)), n1.hl(tt, rr,
    D1.g.hexdig.val(ff), Eq.and.right(Bool.not(D1.abnf.underscore(ff)), n1.nou(tt), hn)))

# a base is above 0
def n1.rb.pos(rx: D1.ARadix) -> {Nat.is_lt(0n, U32.to_nat(n1.rb(rx))) == True{} : Bool}:
  match rx:
    case D1.AHex{}:
      {==}
    case D1.AOct{}:
      {==}
    case D1.ABin{}:
      {==}

# significant digits of a radix, more than k of them, are worth at least
# the radix to the k
def n1.b.hi(
  +rx: D1.ARadix,
  +ff: Char,
  +tt: List<&2, Char>,
  +kk: Nat,
  +hs: {n1.sgk(rx, ff <> tt) == True{} : Bool},
  +hk: {Nat.is_le(kk, List.length(&2, Char, tt)) == True{} : Bool}
) -> {Nat.is_le(Nat.pow(U32.to_nat(n1.rb(rx)), kk), D1.g.num.nat(ff <> tt, U32.to_nat(n1.rb(rx)), 0n)) == True{}
  : Bool}:
  +hr = {Eq.and.right(Bool.not(D1.abnf.cp(ff, 48)), Bool.and(D1.abnf.radix_digit(rx, ff), n1.rdl(rx, tt)), hs)
    : {Bool.and(D1.abnf.radix_digit(rx, ff), n1.rdl(rx, tt)) == True{} : Bool}}
  n1.le.trans(Nat.pow(U32.to_nat(n1.rb(rx)), kk), Nat.pow(U32.to_nat(n1.rb(rx)), List.length(&2, Char, tt)),
    D1.g.num.nat(ff <> tt, U32.to_nat(n1.rb(rx)), 0n), n1.pw.mono(U32.to_nat(n1.rb(rx)), kk, List.length(&2, Char,
    tt), n1.rb.pos(rx), hk), n1.low(ff, tt, U32.to_nat(n1.rb(rx)), n1.rdl.nou(rx, ff <> tt, hr), n1.d0(rx, ff,
    Eq.and.left(D1.abnf.radix_digit(rx, ff), n1.rdl(rx, tt), hr), Eq.not.true(D1.abnf.cp(ff, 48),
    Eq.and.left(Bool.not(D1.abnf.cp(ff, 48)), Bool.and(D1.abnf.radix_digit(rx, ff), n1.rdl(rx, tt)), hs)))))

# and digits of a radix, at most k of them, are worth less than the radix to
# the k
def n1.b.lo(
  +rx: D1.ARadix,
  +xs: List<&2, Char>,
  +kk: Nat,
  +hx: {n1.rdl(rx, xs) == True{} : Bool},
  +hk: {Nat.is_le(List.length(&2, Char, xs), kk) == True{} : Bool}
) -> {Nat.is_lt(D1.g.num.nat(xs, U32.to_nat(n1.rb(rx)), 0n), Nat.pow(U32.to_nat(n1.rb(rx)), kk)) == True{} : Bool}:
  n1.lt.le(D1.g.num.nat(xs, U32.to_nat(n1.rb(rx)), 0n), Nat.pow(U32.to_nat(n1.rb(rx)), List.length(&2, Char, xs)),
    Nat.pow(U32.to_nat(n1.rb(rx)), kk), n1.hb(xs, U32.to_nat(n1.rb(rx)), n1.rdl.nou(rx, xs, hx), n1.rdl.dlt(rx, xs,
    hx)), n1.pw.mono(U32.to_nat(n1.rb(rx)), List.length(&2, Char, xs), kk, n1.rb.pos(rx), hk))

# the significant digits of an octal or binary integer, by whether the ones
# after the first are fewer than k: they are worth less than the radix to
# the k exactly when they are at most k
def n1.bo.go(
  bb: Bool,
  +rx: D1.ARadix,
  +ff: Char,
  +tt: List<&2, Char>,
  +kk: Nat,
  +eb: {Nat.is_lt(List.length(&2, Char, tt), kk) == bb : Bool},
  +hs: {n1.sgk(rx, ff <> tt) == True{} : Bool}
) -> {Nat.is_lt(D1.g.num.nat(ff <> tt, U32.to_nat(n1.rb(rx)), 0n), Nat.pow(U32.to_nat(n1.rb(rx)), kk))
  == Nat.is_lt(List.length(&2, Char, tt), kk) : Bool}:
  match bb:
    case True{}:
      Equal.trans(Bool, Nat.is_lt(D1.g.num.nat(ff <> tt, U32.to_nat(n1.rb(rx)), 0n), Nat.pow(U32.to_nat(n1.rb(rx)),
        kk)), True{}, Nat.is_lt(List.length(&2, Char, tt), kk), n1.b.lo(rx, ff <> tt, kk, Eq.and.right(Bool.not(
        D1.abnf.cp(ff, 48)), Bool.and(D1.abnf.radix_digit(rx, ff), n1.rdl(rx, tt)), hs), Equal.trans(Bool,
        Nat.is_le(1n+List.length(&2, Char, tt), kk), Nat.is_lt(List.length(&2, Char, tt), kk), True{},
        n1.les(List.length(&2, Char, tt), kk), eb)), Equal.sym(Bool, Nat.is_lt(List.length(&2, Char, tt), kk), True{},
        eb))
    case False{}:
      Equal.trans(Bool, Nat.is_lt(D1.g.num.nat(ff <> tt, U32.to_nat(n1.rb(rx)), 0n), Nat.pow(U32.to_nat(n1.rb(rx)),
        kk)), False{}, Nat.is_lt(List.length(&2, Char, tt), kk), n1.le.nlt(Nat.pow(U32.to_nat(n1.rb(rx)), kk),
        D1.g.num.nat(ff <> tt, U32.to_nat(n1.rb(rx)), 0n), n1.b.hi(rx, ff, tt, kk, hs, n1.nlt.le(List.length(&2,
        Char, tt), kk, eb))), Equal.sym(Bool, Nat.is_lt(List.length(&2, Char, tt), kk), False{}, eb))

# significant digits of a radix are worth less than the radix to the k
# exactly when there are at most k of them
def n1.bo(
  +rx: D1.ARadix,
  xs: List<&2, Char>,
  +kk: Nat,
  +hs: {n1.sgk(rx, xs) == True{} : Bool}
) -> {Nat.is_lt(D1.g.num.nat(xs, U32.to_nat(n1.rb(rx)), 0n), Nat.mul(1n, Nat.pow(U32.to_nat(n1.rb(rx)), kk)))
  == Nat.is_le(List.length(&2, Char, xs), kk) : Bool}:
  match xs:
    case []:
      %Equal.sym(Nat, Nat.mul(1n, Nat.pow(U32.to_nat(n1.rb(rx)), kk)), Nat.pow(U32.to_nat(n1.rb(rx)), kk),
        Ar.nat_add_zero(Nat.pow(U32.to_nat(n1.rb(rx)), kk))) : {Nat.is_lt(D1.g.num.nat([], U32.to_nat(n1.rb(rx)),
        0n), _) == Nat.is_le(List.length(&2, Char, []), kk) : Bool}
      Equal.trans(Bool, Nat.is_lt(0n, Nat.pow(U32.to_nat(n1.rb(rx)), kk)), True{}, Nat.is_le(0n, kk),
        n1.pow.pos(U32.to_nat(n1.rb(rx)), kk, n1.rb.pos(rx)), Equal.sym(Bool, Nat.is_le(0n, kk), True{}, n1.le0(kk)))
    case +ff <> +tt:
      %Equal.sym(Nat, Nat.mul(1n, Nat.pow(U32.to_nat(n1.rb(rx)), kk)), Nat.pow(U32.to_nat(n1.rb(rx)), kk),
        Ar.nat_add_zero(Nat.pow(U32.to_nat(n1.rb(rx)), kk))) : {Nat.is_lt(D1.g.num.nat(ff <> tt,
        U32.to_nat(n1.rb(rx)),
        0n), _) == Nat.is_le(List.length(&2, Char, ff <> tt), kk) : Bool}
      %Equal.sym(Bool, Nat.is_le(1n+List.length(&2, Char, tt), kk), Nat.is_lt(List.length(&2, Char, tt), kk),
        n1.les(List.length(&2, Char, tt), kk)) : {Nat.is_lt(D1.g.num.nat(ff <> tt, U32.to_nat(n1.rb(rx)), 0n),
        Nat.pow(U32.to_nat(n1.rb(rx)), kk)) == _ : Bool}
      n1.bo.go(Nat.is_lt(List.length(&2, Char, tt), kk), rx, ff, tt, kk, {==}, hs)

# the significant digits of a hexadecimal integer, by how the number after
# the first compares with k: fewer are worth less than 8 * 16^k, as many are
# exactly when the first is at most 7, and more are not
def n1.bx.go(
  cc: Cmp,
  +ff: Char,
  +tt: List<&2, Char>,
  +kk: Nat,
  +ec: {Nat.cmp(List.length(&2, Char, tt), kk) == cc : Cmp},
  +hs: {n1.sgk(D1.AHex{}, ff <> tt) == True{} : Bool}
) -> {Nat.is_lt(D1.g.num.nat(ff <> tt, 16n, 0n), Nat.mul(8n, Nat.pow(16n, kk))) == Bool.or(Nat.is_lt(List.length(&2,
  Char, tt), kk), Bool.and(Nat.is_eq(List.length(&2, Char, tt), kk), D1.abnf.digit0_7(ff))) : Bool}:
  match cc:
    case LT{}:
      +hl = {Equal.cong(Cmp, Bool, xx => Cmp.is_lt(xx), Nat.cmp(List.length(&2, Char, tt), kk), LT{}, ec)
        : {Nat.is_lt(List.length(&2, Char, tt), kk) == True{} : Bool}}
      %Equal.sym(Bool, Nat.is_lt(List.length(&2, Char, tt), kk), True{}, hl) : {Nat.is_lt(D1.g.num.nat(ff <> tt,
        16n, 0n), Nat.mul(8n, Nat.pow(16n, kk))) == Bool.or(_, Bool.and(Nat.is_eq(List.length(&2, Char, tt), kk),
        D1.abnf.digit0_7(ff))) : Bool}
      n1.lt.le(D1.g.num.nat(ff <> tt, 16n, 0n), Nat.pow(16n, kk), Nat.mul(8n, Nat.pow(16n, kk)), n1.b.lo(D1.AHex{},
        ff <> tt, kk, Eq.and.right(Bool.not(D1.abnf.cp(ff, 48)), Bool.and(D1.abnf.radix_digit(D1.AHex{}, ff),
        n1.rdl(D1.AHex{}, tt)), hs), n1.lt.suc(List.length(&2, Char, tt), kk, hl)), n1.le.addr(Nat.pow(16n, kk),
        Nat.mul(7n, Nat.pow(16n, kk))))
    case EQ{}:
      +hr = {Eq.and.right(Bool.not(D1.abnf.cp(ff, 48)), Bool.and(D1.abnf.radix_digit(D1.AHex{}, ff),
        n1.rdl(D1.AHex{}, tt)), hs) : {Bool.and(D1.abnf.radix_digit(D1.AHex{}, ff), n1.rdl(D1.AHex{}, tt))
        == True{} : Bool}}
      +el = {n1.ceqn(List.length(&2, Char, tt), kk, ec) : {List.length(&2, Char, tt) == kk : Nat}}
      +ht = {n1.b.lo(D1.AHex{}, tt, kk, Eq.and.right(D1.abnf.radix_digit(D1.AHex{}, ff), n1.rdl(D1.AHex{},
        tt), hr), Equal.cong(Cmp, Bool, xx => Cmp.is_le(xx), Nat.cmp(List.length(&2, Char, tt), kk), EQ{}, ec))
        : {Nat.is_lt(D1.g.num.nat(tt, 16n, 0n), Nat.pow(16n, kk)) == True{} : Bool}}
      %Equal.sym(Nat, D1.g.num.nat(ff <> tt, 16n, 0n), Nat.add(Nat.mul(D1.g.hexdig.val(ff), Nat.pow(16n,
        List.length(&2, Char, tt))), D1.g.num.nat(tt, 16n, 0n)), n1.hsplit(ff, tt, 16n, n1.rdl.nou(D1.AHex{},
        ff <> tt, hr))) : {Nat.is_lt(_, Nat.mul(8n, Nat.pow(16n, kk))) == Bool.or(Nat.is_lt(List.length(&2, Char,
        tt), kk), Bool.and(Nat.is_eq(List.length(&2, Char, tt), kk), D1.abnf.digit0_7(ff))) : Bool}
      %Equal.sym(Nat, List.length(&2, Char, tt), kk, el) : {Nat.is_lt(Nat.add(Nat.mul(D1.g.hexdig.val(ff),
        Nat.pow(16n, _)), D1.g.num.nat(tt, 16n, 0n)), Nat.mul(8n, Nat.pow(16n, kk))) == Bool.or(Nat.is_lt(_, kk),
        Bool.and(Nat.is_eq(_, kk), D1.abnf.digit0_7(ff))) : Bool}
      %Equal.sym(Bool, Nat.is_lt(kk, kk), False{}, n1.ltirr(kk)) : {Nat.is_lt(Nat.add(Nat.mul(D1.g.hexdig.val(ff),
        Nat.pow(16n, kk)), D1.g.num.nat(tt, 16n, 0n)), Nat.mul(8n, Nat.pow(16n, kk))) == Bool.or(_,
        Bool.and(Nat.is_eq(kk, kk), D1.abnf.digit0_7(ff))) : Bool}
      %Equal.sym(Bool, Nat.is_eq(kk, kk), True{}, n1.eqrefl(kk)) : {Nat.is_lt(Nat.add(Nat.mul(D1.g.hexdig.val(ff),
        Nat.pow(16n, kk)), D1.g.num.nat(tt, 16n, 0n)), Nat.mul(8n, Nat.pow(16n, kk))) == Bool.or(False{},
        Bool.and(_, D1.abnf.digit0_7(ff))) : Bool}
      %Equal.sym(Bool, D1.abnf.digit0_7(ff), Nat.is_lt(D1.g.hexdig.val(ff), 8n), n1.d07(ff,
        Eq.and.left(D1.abnf.radix_digit(D1.AHex{}, ff), n1.rdl(D1.AHex{}, tt), hr))) : {Nat.is_lt(Nat.add(
        Nat.mul(D1.g.hexdig.val(ff), Nat.pow(16n, kk)), D1.g.num.nat(tt, 16n, 0n)), Nat.mul(8n, Nat.pow(16n,
        kk))) == Bool.or(False{}, Bool.and(True{}, _)) : Bool}
      %Ar.nat_add_zero(Nat.mul(8n, Nat.pow(16n, kk))) : {Nat.is_lt(Nat.add(Nat.mul(D1.g.hexdig.val(ff),
        Nat.pow(16n, kk)), D1.g.num.nat(tt, 16n, 0n)), _) == Nat.is_lt(D1.g.hexdig.val(ff), 8n) : Bool}
      Equal.trans(Bool, Nat.is_lt(Nat.add(Nat.mul(D1.g.hexdig.val(ff), Nat.pow(16n, kk)), D1.g.num.nat(tt, 16n,
        0n)), Nat.add(Nat.mul(8n, Nat.pow(16n, kk)), 0n)), Cmp.is_lt(T.i64.ord(Nat.cmp(D1.g.hexdig.val(ff), 8n),
        Nat.cmp(D1.g.num.nat(tt, 16n, 0n), 0n))), Nat.is_lt(D1.g.hexdig.val(ff), 8n), Equal.cong(Cmp, Bool,
        xx => Cmp.is_lt(xx), Nat.cmp(Nat.add(Nat.mul(D1.g.hexdig.val(ff), Nat.pow(16n, kk)), D1.g.num.nat(tt,
        16n, 0n)), Nat.add(Nat.mul(8n, Nat.pow(16n, kk)), 0n)), T.i64.ord(Nat.cmp(D1.g.hexdig.val(ff), 8n),
        Nat.cmp(D1.g.num.nat(tt, 16n, 0n), 0n)), n1.ka(D1.g.hexdig.val(ff), 8n, Nat.pow(16n, kk),
        D1.g.num.nat(tt, 16n, 0n), 0n, ht, n1.pow.pos(16n, kk, {==}))), n1.ord0(Nat.cmp(D1.g.hexdig.val(ff),
        8n), D1.g.num.nat(tt, 16n, 0n)))
    case GT{}:
      %Equal.sym(Bool, Nat.is_lt(List.length(&2, Char, tt), kk), False{}, Equal.cong(Cmp, Bool, xx => Cmp.is_lt(xx),
        Nat.cmp(List.length(&2, Char, tt), kk), GT{}, ec)) : {Nat.is_lt(D1.g.num.nat(ff <> tt, 16n, 0n),
        Nat.mul(8n, Nat.pow(16n, kk))) == Bool.or(_, Bool.and(Nat.is_eq(List.length(&2, Char, tt), kk),
        D1.abnf.digit0_7(ff))) : Bool}
      %Equal.sym(Bool, Nat.is_eq(List.length(&2, Char, tt), kk), False{}, Equal.cong(Cmp, Bool, xx => Cmp.is_eq(xx),
        Nat.cmp(List.length(&2, Char, tt), kk), GT{}, ec)) : {Nat.is_lt(D1.g.num.nat(ff <> tt, 16n, 0n),
        Nat.mul(8n, Nat.pow(16n, kk))) == Bool.or(False{}, Bool.and(_, D1.abnf.digit0_7(ff))) : Bool}
      n1.le.nlt(Nat.mul(8n, Nat.pow(16n, kk)), D1.g.num.nat(ff <> tt, 16n, 0n), n1.lt.lte(Nat.mul(8n, Nat.pow(16n,
        kk)), D1.g.num.nat(ff <> tt, 16n, 0n), n1.lt.le(Nat.mul(8n, Nat.pow(16n, kk)), Nat.mul(16n, Nat.pow(16n,
        kk)), D1.g.num.nat(ff <> tt, 16n, 0n), n1.mul.lt(8n, 16n, Nat.pow(16n, kk), {==}, n1.pow.pos(16n, kk, {==})),
        n1.b.hi(D1.AHex{}, ff, tt, 1n+kk, hs, n1.lt.suc(kk, List.length(&2, Char, tt), n1.gt.lt(List.length(&2,
        Char, tt), kk, ec))))))

# significant hexadecimal digits are worth less than 8 * 16^k exactly when
# there are at most k, or k + 1 and the first is at most 7
def n1.bx(
  xs: List<&2, Char>,
  +kk: Nat,
  +hs: {n1.sgk(D1.AHex{}, xs) == True{} : Bool}
) -> {Nat.is_lt( D1.g.num.nat(xs, 16n, 0n), Nat.mul(8n, Nat.pow(16n, kk))) == Bool.or(Nat.is_lt(List.length(&2,
  Char, xs), 1n+kk), Bool.and(Nat.is_eq(List.length(&2, Char, xs), 1n+kk), D1.prose.first_le7(xs))) : Bool}:
  match xs:
    case []:
      M2.lt.add(0n, Nat.pow(16n, kk), Nat.mul(7n, Nat.pow(16n, kk)), n1.pow.pos(16n, kk, {==}))
    case +ff <> +tt:
      n1.bx.go(Nat.cmp(List.length(&2, Char, tt), kk), ff, tt, kk, {==}, hs)

# significant digits of a radix, against its limit once uu is known: at most
# k, for octal and binary
def n1.bo.u(
  +rx: D1.ARadix,
  +xs: List<&2, Char>,
  +kk: Nat,
  +hs: {n1.sgk(rx, xs) == True{} : Bool},
  uu: Unit
) -> {Nat.is_lt(D1.g.num.nat(xs, U32.to_nat(n1.rb(rx)), 0n), n1.pb([1n], U32.to_nat(n1.rb(rx)), kk, uu))
  == Nat.is_le(List.length(&2, Char, xs), kk) : Bool}:
  match uu:
    case Unit{}:
      n1.bo(rx, xs, kk, hs)

# and for hexadecimal
def n1.bx.u(
  +xs: List<&2, Char>,
  +kk: Nat,
  +hs: {n1.sgk(D1.AHex{}, xs) == True{} : Bool},
  uu: Unit
) -> {Nat.is_lt(D1.g.num.nat(xs, 16n, 0n), n1.pb([8n], 16n, kk, uu)) == Bool.or(Nat.is_lt(List.length(&2, Char, xs),
  1n+kk), Bool.and(Nat.is_eq(List.length(&2, Char, xs), 1n+kk), D1.prose.first_le7(xs))) : Bool}:
  match uu:
    case Unit{}:
      n1.bx(xs, kk, hs)

# i64.step against a canonical limit, once uu is known
def n1.fhu(
  +dd: String,
  +ll: String,
  +hd: {D1.g.dec.canon(dd) == True{} : Bool},
  +hl: {D1.g.dec.canon(ll) == True{} : Bool},
  uu: Unit
) -> {T.i64.step(dd, ll, EQ{}) == Nat.is_le(n1.h10(dd), n1.hu(ll, uu)) : Bool}:
  match uu:
    case Unit{}:
      n1.fh(dd, ll, hd, hl)

# a string's characters, appended, are the characters of each
def n1.tla(
  aa: String,
  +bb: String
) -> {String.to_list(String.append(aa, bb)) == List.append(&2, Char, String.to_list(aa),
  String.to_list(bb)) : List<&2, Char>}:
  match aa:
    case SNil{}:
      {==}
    case SCon{+hh, +tt}:
      Equal.cong(List<&2, Char>, List<&2, Char>, ls => hh <> ls, String.to_list(String.append(tt, bb)),
        List.append(&2, Char, String.to_list(tt), String.to_list(bb)), n1.tla(tt, bb))

# a numeral and a last digit is worth ten times the numeral and the digit
def n1.last(
  +pre: String,
  +dd: Char
) -> {n1.h10(String.append(pre, SCon{dd, SNil{}})) == D1.g.num.nat([dd], 10n, n1.h10(pre)) : Nat}:
  Equal.trans(Nat, n1.h10(String.append(pre, SCon{dd, SNil{}})), D1.g.num.nat(List.append(&2, Char,
    String.to_list(pre), [dd]), 10n, 0n), D1.g.num.nat([dd], 10n, n1.h10(pre)), Equal.cong(List<&2, Char>, Nat,
    ls => D1.g.num.nat(ls, 10n, 0n), String.to_list(String.append(pre, SCon{dd, SNil{}})), List.append(&2, Char,
    String.to_list(pre), [dd]), n1.tla(pre, SCon{dd, SNil{}})), n1.gn.app(String.to_list(pre), [dd], 10n, 0n))

# a numeral ending in 8 is worth one more than the one ending in 7, once uu
# is known
def n1.l78(
  +pre: String,
  uu: Unit
) -> {n1.hu(String.append(pre, "8"), uu) == 1n+n1.hu(String.append(pre, "7"), uu) : Nat}:
  match uu:
    case Unit{}:
      Equal.trans(Nat, n1.h10(String.append(pre, "8")), Nat.add(Nat.mul(n1.h10(pre), 10n), 8n),
        1n+n1.h10(String.append(pre, "7")), n1.last(pre, '8'), Equal.trans(Nat, Nat.add(Nat.mul(n1.h10(pre), 10n),
        8n), 1n+Nat.add(Nat.mul(n1.h10(pre), 10n), 7n), 1n+n1.h10(String.append(pre, "7")),
        Ar.nat_add_succ(Nat.mul(n1.h10(pre), 10n), 7n), Equal.cong(Nat, Nat, nn => 1n+nn, Nat.add(Nat.mul(n1.h10(pre),
        10n), 7n), n1.h10(String.append(pre, "7")), Equal.sym(Nat, n1.h10(String.append(pre, "7")),
        Nat.add(Nat.mul(n1.h10(pre), 10n), 7n), n1.last(pre, '7')))))

# the limits of a plus and a minus differ by one, once uu is known
def n1.lpm(+uu: Unit) -> {n1.hu(T.i64.limit(T.Minus{}), uu) == 1n+n1.hu(T.i64.limit(T.Plus{}), uu) : Nat}:
  n1.l78("922337203685477580", uu)

# a prefixed integer's numeral, as dec.text writes it, fits exactly when its
# significant digits are worth less than 2^63
def n1.rng.c(
  +uu: Unit,
  +rx: D1.ARadix,
  +rest: List<&2, Char>,
  +hb: {n1.bg(rest, rx) == True{} : Bool}
) -> {T.i64.fits(T.Plus{}, T.dec.text(n1.cv(rx, rest, []))) == Nat.is_lt(D1.g.num.nat(D1.prose.sig(rest),
  U32.to_nat(n1.rb(rx)), 0n), n1.hu(T.i64.limit(T.Minus{}), uu)) : Bool}:
  +hr = {n1.rr.bg(rest, rx, hb) : {n1.rr(rx, rest) == True{} : Bool}}
  +ds = n1.cv(rx, rest, [])
  +hd = {n1.cvok(uu, rx, rest, [], {==}, hr) : {n1.d10(ds) == True{} : Bool}}
  %Equal.sym(Nat, n1.hu(T.i64.limit(T.Minus{}), uu), 1n+n1.hu(T.i64.limit(T.Plus{}), uu), n1.lpm(uu)) :
    {T.i64.fits(T.Plus{}, T.dec.text(ds)) == Nat.is_lt(D1.g.num.nat(D1.prose.sig(rest), U32.to_nat(n1.rb(rx)),
    0n), _) : Bool}
  %n1.gsig(rest, U32.to_nat(n1.rb(rx))) : {T.i64.fits(T.Plus{}, T.dec.text(ds)) == Nat.is_lt(_,
    1n+n1.hu(T.i64.limit(T.Plus{}), uu)) : Bool}
  %n1.cvW(uu, rx, rest, [], {==}, hr) : {T.i64.fits(T.Plus{}, T.dec.text(ds)) == Nat.is_lt(_,
    1n+n1.hu(T.i64.limit(T.Plus{}), uu)) : Bool}
  %n1.text.v(ds, hd) : {T.i64.fits(T.Plus{}, T.dec.text(ds)) == Nat.is_lt(_, 1n+n1.hu(T.i64.limit(T.Plus{}), uu))
    : Bool}
  Equal.trans(Bool, T.i64.step(T.dec.text(ds), T.i64.limit(T.Plus{}), EQ{}), Nat.is_le(n1.h10(T.dec.text(ds)),
    n1.hu(T.i64.limit(T.Plus{}), uu)), Nat.is_lt(n1.h10(T.dec.text(ds)), 1n+n1.hu(T.i64.limit(T.Plus{}), uu)),
    n1.fhu(T.dec.text(ds), T.i64.limit(T.Plus{}), n1.text.c(ds, hd), {==}, uu), M2.le.lt(n1.h10(T.dec.text(ds)),
    n1.hu(T.i64.limit(T.Plus{}), uu)))

# dropping nothing leaves the list
def n1.drop0(xs: List<&2, Char>) -> {List.drop(&2, Char, xs, 0n) == xs : List<&2, Char>}:
  match xs:
    case []:
      {==}
    case _h <> _t:
      {==}

# the prose's bound after a prefix is its bound on the rest
def n1.rif(
  +rx: D1.ARadix,
  +rest: List<&2, Char>
) -> {D1.prose.radix_fits(rx, List.length(&2, Char, D1.prose.sig(rest)),
  D1.prose.sig(rest)) == D1.prose.radix_fits(rx, List.length(&2, Char, D1.prose.sig( List.drop(&2, Char, rest,
    0n))), D1.prose.sig(List.drop(&2, Char, rest, 0n))) : Bool}:
  Equal.cong(List<&2, Char>, Bool, ys => D1.prose.radix_fits(rx, List.length(&2, Char, D1.prose.sig(ys)),
    D1.prose.sig(ys)), rest, List.drop(&2, Char, rest, 0n), Equal.sym(List<&2, Char>, List.drop(&2, Char, rest,
    0n), rest, n1.drop0(rest)))

# a hexadecimal integer's numeral fits exactly when the prose's bound allows
def n1.rng.x(
  +uu: Unit,
  +rest: List<&2, Char>,
  +hb: {n1.bg(rest, D1.AHex{}) == True{} : Bool}
) -> {T.i64.fits(T.Plus{}, T.dec.text(n1.cv(D1.AHex{}, rest, []))) == D1.prose.radix_in_range(D1.AHex{},
  '0' <> 'x' <> rest) : Bool}:
  Equal.trans(Bool, T.i64.fits(T.Plus{}, T.dec.text(n1.cv(D1.AHex{}, rest, []))), Nat.is_lt(D1.g.num.nat(
    D1.prose.sig(rest), 16n, 0n), n1.hu(T.i64.limit(T.Minus{}), uu)), D1.prose.radix_in_range(D1.AHex{},
    '0' <> 'x' <> rest), n1.rng.c(uu, D1.AHex{}, rest, hb), Equal.trans(Bool, Nat.is_lt(D1.g.num.nat(
    D1.prose.sig(rest), 16n, 0n), n1.hu(T.i64.limit(T.Minus{}), uu)), Nat.is_lt(D1.g.num.nat(D1.prose.sig(rest),
    16n, 0n), n1.pb([8n], 16n, 15n, uu)), D1.prose.radix_in_range(D1.AHex{}, '0' <> 'x' <> rest),
    Equal.cong(Nat, Bool, nn => Nat.is_lt(D1.g.num.nat(D1.prose.sig(rest), 16n, 0n), nn),
    n1.hu(T.i64.limit(T.Minus{}), uu), n1.pb([8n], 16n, 15n, uu), n1.lim.x(uu)), Equal.trans(Bool,
    Nat.is_lt(D1.g.num.nat(D1.prose.sig(rest), 16n, 0n), n1.pb([8n], 16n, 15n, uu)), D1.prose.radix_fits(
    D1.AHex{}, List.length(&2, Char, D1.prose.sig(rest)), D1.prose.sig(rest)), D1.prose.radix_in_range(
    D1.AHex{}, '0' <> 'x' <> rest), n1.bx.u(D1.prose.sig(rest), 15n, n1.sigk(D1.AHex{}, rest, n1.rr.bg(rest,
    D1.AHex{}, hb)), uu), n1.rif(D1.AHex{}, rest))))

# an octal one
def n1.rng.o(
  +uu: Unit,
  +rest: List<&2, Char>,
  +hb: {n1.bg(rest, D1.AOct{}) == True{} : Bool}
) -> {T.i64.fits(T.Plus{}, T.dec.text(n1.cv(D1.AOct{}, rest, []))) == D1.prose.radix_in_range(D1.AOct{},
  '0' <> 'o' <> rest) : Bool}:
  Equal.trans(Bool, T.i64.fits(T.Plus{}, T.dec.text(n1.cv(D1.AOct{}, rest, []))), Nat.is_lt(D1.g.num.nat(
    D1.prose.sig(rest), 8n, 0n), n1.hu(T.i64.limit(T.Minus{}), uu)), D1.prose.radix_in_range(D1.AOct{},
    '0' <> 'o' <> rest), n1.rng.c(uu, D1.AOct{}, rest, hb), Equal.trans(Bool, Nat.is_lt(D1.g.num.nat(
    D1.prose.sig(rest), 8n, 0n), n1.hu(T.i64.limit(T.Minus{}), uu)), Nat.is_lt(D1.g.num.nat(D1.prose.sig(rest),
    8n, 0n), n1.pb([1n], 8n, 21n, uu)), D1.prose.radix_in_range(D1.AOct{}, '0' <> 'o' <> rest),
    Equal.cong(Nat, Bool, nn => Nat.is_lt(D1.g.num.nat(D1.prose.sig(rest), 8n, 0n), nn),
    n1.hu(T.i64.limit(T.Minus{}), uu), n1.pb([1n], 8n, 21n, uu), n1.lim.o(uu)), Equal.trans(Bool,
    Nat.is_lt(D1.g.num.nat(D1.prose.sig(rest), 8n, 0n), n1.pb([1n], 8n, 21n, uu)), D1.prose.radix_fits(
    D1.AOct{}, List.length(&2, Char, D1.prose.sig(rest)), D1.prose.sig(rest)), D1.prose.radix_in_range(
    D1.AOct{}, '0' <> 'o' <> rest), n1.bo.u(D1.AOct{}, D1.prose.sig(rest), 21n, n1.sigk(D1.AOct{}, rest,
    n1.rr.bg(rest, D1.AOct{}, hb)), uu), n1.rif(D1.AOct{}, rest))))

# a binary one
def n1.rng.b(
  +uu: Unit,
  +rest: List<&2, Char>,
  +hb: {n1.bg(rest, D1.ABin{}) == True{} : Bool}
) -> {T.i64.fits(T.Plus{}, T.dec.text(n1.cv(D1.ABin{}, rest, []))) == D1.prose.radix_in_range(D1.ABin{},
  '0' <> 'b' <> rest) : Bool}:
  Equal.trans(Bool, T.i64.fits(T.Plus{}, T.dec.text(n1.cv(D1.ABin{}, rest, []))), Nat.is_lt(D1.g.num.nat(
    D1.prose.sig(rest), 2n, 0n), n1.hu(T.i64.limit(T.Minus{}), uu)), D1.prose.radix_in_range(D1.ABin{},
    '0' <> 'b' <> rest), n1.rng.c(uu, D1.ABin{}, rest, hb), Equal.trans(Bool, Nat.is_lt(D1.g.num.nat(
    D1.prose.sig(rest), 2n, 0n), n1.hu(T.i64.limit(T.Minus{}), uu)), Nat.is_lt(D1.g.num.nat(D1.prose.sig(rest),
    2n, 0n), n1.pb([1n], 2n, 63n, uu)), D1.prose.radix_in_range(D1.ABin{}, '0' <> 'b' <> rest),
    Equal.cong(Nat, Bool, nn => Nat.is_lt(D1.g.num.nat(D1.prose.sig(rest), 2n, 0n), nn),
    n1.hu(T.i64.limit(T.Minus{}), uu), n1.pb([1n], 2n, 63n, uu), n1.lim.b(uu)), Equal.trans(Bool,
    Nat.is_lt(D1.g.num.nat(D1.prose.sig(rest), 2n, 0n), n1.pb([1n], 2n, 63n, uu)), D1.prose.radix_fits(
    D1.ABin{}, List.length(&2, Char, D1.prose.sig(rest)), D1.prose.sig(rest)), D1.prose.radix_in_range(
    D1.ABin{}, '0' <> 'b' <> rest), n1.bo.u(D1.ABin{}, D1.prose.sig(rest), 63n, n1.sigk(D1.ABin{}, rest,
    n1.rr.bg(rest, D1.ABin{}, hb)), uu), n1.rif(D1.ABin{}, rest))))

# The dec-int word, in or out of range. The spike's scan (gs.*) reads a
# dec-int's digits; here its reading is finished with the range test left
# open, so a word out of range is refused.

# what the dec-int reading claims: the scan's integer, tested for range
def n1.dw.G(+sg: T.Sign, +ds: String) -> T.Got:
  T.num.fin.range(T.i64.fits(sg, ds), sg, ds)

# the finished numeral is the integer, tested for range
def n1.dw.fin(
  +sg: T.Sign,
  +hh: Char,
  +tt: String,
  +hx: {Char.is_digit(hh) == True{} : Bool},
  +hz: {Char.is_eq(hh, '0') == False{} : Bool},
  +ht: {T.wf.digits(tt) == True{} : Bool},
  +cs: List<&2, Char>
) -> {T.num.fin(M4.ndig(sg, M4.vals(M6.rev.onto(tt, [hh]))), cs) == n1.dw.G(sg, SCon{hh, tt}) : T.Got}:
  Equal.cong(String, T.Got, ss => T.num.fin.range(T.i64.fits(sg, ss), sg, ss), T.dec.text(M4.vals(M6.rev.onto(tt,
      [hh]))),
    SCon{hh, tt}, M4.dtext(hh, tt, hx, hz, ht))

# after a first digit that is not 0, the scan reads the repetition and
# finishes as the integer, tested for range
def n1.dw.scan(
  +sg: T.Sign,
  +hh: Char,
  +t1: Char,
  +ts: List<&2, Char>,
  +st0: T.Num,
  +e0: {T.num.step(st0, hh) == M4.ndig(sg, M4.vals([hh])) : T.Num},
  +hx: {Char.is_digit(hh) == True{} : Bool},
  +hz: {Char.is_eq(hh, '0') == False{} : Bool},
  +hr: {D1.abnf.dec_rep(t1 <> ts) == True{} : Bool},
  +cs: List<&2, Char>
) -> {T.num.fin(T.num.go(t1 <> ts, T.num.step(st0, hh)), cs) == n1.dw.G(sg, SCon{hh, D1.abnf.no_us(t1 <> ts)})
  : T.Got}:
  Equal.trans(T.Got, T.num.fin(T.num.go(t1 <> ts, T.num.step(st0, hh)), cs),
    T.num.fin(M4.ndig(sg, M4.vals(M6.rev.onto(D1.abnf.no_us(t1 <> ts), [hh]))), cs),
    n1.dw.G(sg, SCon{hh, D1.abnf.no_us(t1 <> ts)}),
    Equal.cong(T.Num, T.Got, nn => T.num.fin(nn, cs), T.num.go(t1 <> ts, T.num.step(st0, hh)),
      M4.ndig(sg, M4.vals(M6.rev.onto(D1.abnf.no_us(t1 <> ts), [hh]))),
      Equal.trans(T.Num, T.num.go(t1 <> ts, T.num.step(st0, hh)), T.num.go(t1 <> ts, M4.ndig(sg, M4.vals([hh]))),
        M4.ndig(sg, M4.vals(M6.rev.onto(D1.abnf.no_us(t1 <> ts), [hh]))),
        Equal.cong(T.Num, T.Num, nn => T.num.go(t1 <> ts, nn), T.num.step(st0, hh), M4.ndig(sg, M4.vals([hh])), e0),
        gs.scan(t1 <> ts, [hh], sg, hr, M3.nzl.one(hh, hx, hz)))),
    n1.dw.fin(sg, hh, D1.abnf.no_us(t1 <> ts), hx, hz, gs.digits(t1 <> ts, hr), cs))

# an unsigned-dec-int of more than one character
def n1.dw.mu(
  +hh: Char,
  +t1: Char,
  +ts: List<&2, Char>,
  +hd: {D1.abnf.digit1_9(hh) == True{} : Bool},
  +hr: {D1.abnf.dec_rep(t1 <> ts) == True{} : Bool}
) -> {T.word.val(hh <> t1 <> ts) == n1.dw.G(T.Plus{}, D1.abnf.no_us(hh <> t1 <> ts)) : T.Got}:
  +hx = {M4.gs.d19(hh, hd) : {Char.is_digit(hh) == True{} : Bool}}
  +hz = {gs.d19z(hh, hd) : {Char.is_eq(hh, '0') == False{} : Bool}}
  %gs.nu(hh, t1 <> ts, M4.gs.nous(hh, hx)) : {T.word.val(hh <> t1 <> ts) == n1.dw.G(T.Plus{}, _) : T.Got}
  Equal.trans(T.Got, T.word.val.pick(T.word.special(hh), hh <> t1 <> ts), T.word.val.pick(False{}, hh <> t1 <> ts),
    n1.dw.G(T.Plus{}, SCon{hh, D1.abnf.no_us(t1 <> ts)}),
    Equal.cong(Bool, T.Got, bb => T.word.val.pick(bb, hh <> t1 <> ts), T.word.special(hh), False{},
      M3.dg.nospec(hh, hx)),
    Equal.trans(T.Got, T.word.route(T.GotBad{""}, T.word.or(T.word.colon(hh <> t1 <> ts),
      T.word.dash(hh <> t1 <> ts, True{})), hh <> t1 <> ts), T.word.num(hh <> t1 <> ts),
      n1.dw.G(T.Plus{}, SCon{hh, D1.abnf.no_us(t1 <> ts)}),
      M3.route.num(hh <> t1 <> ts, gs.hc(hh, t1 <> ts, hx, hr), gs.dash(t1 <> ts, hr)),
      n1.dw.scan(T.Plus{}, hh, t1, ts, T.num.start(), M4.nw.lead(T.Plus{}, hh, hx, hz), hx, hz, hr, hh <> t1 <> ts)))

# and after a minus
def n1.dw.mm(
  +hh: Char,
  +t1: Char,
  +ts: List<&2, Char>,
  +hd: {D1.abnf.digit1_9(hh) == True{} : Bool},
  +hr: {D1.abnf.dec_rep(t1 <> ts) == True{} : Bool}
) -> {T.word.val('-' <> hh <> t1 <> ts) == n1.dw.G(T.Minus{}, D1.abnf.no_us(hh <> t1 <> ts)) : T.Got}:
  +hx = {M4.gs.d19(hh, hd) : {Char.is_digit(hh) == True{} : Bool}}
  +hz = {gs.d19z(hh, hd) : {Char.is_eq(hh, '0') == False{} : Bool}}
  %gs.nu(hh, t1 <> ts, M4.gs.nous(hh, hx)) : {T.word.val('-' <> hh <> t1 <> ts) == n1.dw.G(T.Minus{}, _) : T.Got}
  Equal.trans(T.Got, T.word.route(T.word.spec(String.from_list('-' <> hh <> t1 <> ts)),
    T.word.or(T.word.colon('-' <> hh <> t1 <> ts), T.word.dash('-' <> hh <> t1 <> ts, True{})), '-' <> hh <> t1 <> ts),
    T.word.route(T.GotBad{""}, T.word.or(T.word.colon('-' <> hh <> t1 <> ts), T.word.dash('-' <> hh <> t1 <> ts,
      True{})), '-' <> hh <> t1 <> ts),
    n1.dw.G(T.Minus{}, SCon{hh, D1.abnf.no_us(t1 <> ts)}),
    Equal.cong(T.Got, T.Got, gg => T.word.route(gg, T.word.or(T.word.colon('-' <> hh <> t1 <> ts),
      T.word.dash('-' <> hh <> t1 <> ts, True{})), '-' <> hh <> t1 <> ts),
      T.word.spec(String.from_list('-' <> hh <> t1 <> ts)), T.GotBad{""},
      M3.spec.m(hh, t1 <> ts, M3.dg.noi(hh, hx), M3.dg.non(hh, hx))),
    Equal.trans(T.Got, T.word.route(T.GotBad{""}, T.word.or(T.word.colon('-' <> hh <> t1 <> ts),
      T.word.dash('-' <> hh <> t1 <> ts, True{})), '-' <> hh <> t1 <> ts), T.word.num('-' <> hh <> t1 <> ts),
      n1.dw.G(T.Minus{}, SCon{hh, D1.abnf.no_us(t1 <> ts)}),
      M3.route.num('-' <> hh <> t1 <> ts, gs.hc(hh, t1 <> ts, hx, hr), gs.hd1(hh, t1 <> ts, hx, hr)),
      n1.dw.scan(T.Minus{}, hh, t1, ts, T.Num{T.NSign{}, T.Minus{}, 10, [], False{}, False{}, ""},
        M4.nw.sign(T.Minus{}, hh, hx, hz), hx, hz, hr, '-' <> hh <> t1 <> ts)))

# and after a plus
def n1.dw.mp(
  +hh: Char,
  +t1: Char,
  +ts: List<&2, Char>,
  +hd: {D1.abnf.digit1_9(hh) == True{} : Bool},
  +hr: {D1.abnf.dec_rep(t1 <> ts) == True{} : Bool}
) -> {T.word.val('+' <> hh <> t1 <> ts) == n1.dw.G(T.Plus{}, D1.abnf.no_us(hh <> t1 <> ts)) : T.Got}:
  +hx = {M4.gs.d19(hh, hd) : {Char.is_digit(hh) == True{} : Bool}}
  +hz = {gs.d19z(hh, hd) : {Char.is_eq(hh, '0') == False{} : Bool}}
  %gs.nu(hh, t1 <> ts, M4.gs.nous(hh, hx)) : {T.word.val('+' <> hh <> t1 <> ts) == n1.dw.G(T.Plus{}, _) : T.Got}
  Equal.trans(T.Got, T.word.route(T.word.spec(String.from_list('+' <> hh <> t1 <> ts)),
    T.word.or(T.word.colon('+' <> hh <> t1 <> ts), T.word.dash('+' <> hh <> t1 <> ts, True{})), '+' <> hh <> t1 <> ts),
    T.word.route(T.GotBad{""}, T.word.or(T.word.colon('+' <> hh <> t1 <> ts), T.word.dash('+' <> hh <> t1 <> ts,
      True{})), '+' <> hh <> t1 <> ts),
    n1.dw.G(T.Plus{}, SCon{hh, D1.abnf.no_us(t1 <> ts)}),
    Equal.cong(T.Got, T.Got, gg => T.word.route(gg, T.word.or(T.word.colon('+' <> hh <> t1 <> ts),
      T.word.dash('+' <> hh <> t1 <> ts, True{})), '+' <> hh <> t1 <> ts),
      T.word.spec(String.from_list('+' <> hh <> t1 <> ts)), T.GotBad{""},
      gs.spec.p(hh, t1 <> ts, M3.dg.noi(hh, hx), M3.dg.non(hh, hx))),
    Equal.trans(T.Got, T.word.route(T.GotBad{""}, T.word.or(T.word.colon('+' <> hh <> t1 <> ts),
      T.word.dash('+' <> hh <> t1 <> ts, True{})), '+' <> hh <> t1 <> ts), T.word.num('+' <> hh <> t1 <> ts),
      n1.dw.G(T.Plus{}, SCon{hh, D1.abnf.no_us(t1 <> ts)}),
      M3.route.num('+' <> hh <> t1 <> ts, gs.hc(hh, t1 <> ts, hx, hr), gs.hd1(hh, t1 <> ts, hx, hr)),
      n1.dw.scan(T.Plus{}, hh, t1, ts, T.Num{T.NSign{}, T.Plus{}, 10, [], False{}, False{}, ""},
        M4.nw.sign(T.Plus{}, hh, hx, hz), hx, hz, hr, '+' <> hh <> t1 <> ts)))

# a lone DIGIT, with no sign, a minus or a plus, is in range
def n1.dw.ou(
  hh: Char,
  hx: {Char.is_digit(hh) == True{} : Bool}
) -> {T.word.val([hh]) == n1.dw.G(T.Plus{}, D1.abnf.no_us([hh])) : T.Got}:
  M6.dg.elim(zz => {T.word.val([zz]) == n1.dw.G(T.Plus{}, D1.abnf.no_us([zz])) : T.Got}, hh, hx,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# after a minus
def n1.dw.om(
  hh: Char,
  hx: {Char.is_digit(hh) == True{} : Bool}
) -> {T.word.val(['-', hh]) == n1.dw.G(T.Minus{}, D1.abnf.no_us([hh])) : T.Got}:
  M6.dg.elim(zz => {T.word.val(['-', zz]) == n1.dw.G(T.Minus{}, D1.abnf.no_us([zz])) : T.Got}, hh, hx,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# after a plus
def n1.dw.op(
  hh: Char,
  hx: {Char.is_digit(hh) == True{} : Bool}
) -> {T.word.val(['+', hh]) == n1.dw.G(T.Plus{}, D1.abnf.no_us([hh])) : T.Got}:
  M6.dg.elim(zz => {T.word.val(['+', zz]) == n1.dw.G(T.Plus{}, D1.abnf.no_us([zz])) : T.Got}, hh, hx,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# an unsigned-dec-int with no sign
def n1.dw.uns(
  +hh: Char,
  tt: List<&2, Char>,
  +hu: {D1.abnf.unsigned_dec_int(hh <> tt) == True{} : Bool}
) -> {T.word.val(hh <> tt) == n1.dw.G(T.Plus{}, D1.abnf.no_us(hh <> tt)) : T.Got}:
  match tt:
    case []:
      n1.dw.ou(hh, gs.body.one(hh, D1.abnf.DIGIT(hh), {==}, hu))
    case +t1 <> +ts:
      n1.dw.mu(hh, t1, ts, gs.body.l(hh, t1, ts, hu), gs.body.r(hh, t1, ts, hu))

# after a minus
def n1.dw.neg.go(
  +hh: Char,
  tt: List<&2, Char>,
  +hu: {D1.abnf.unsigned_dec_int(hh <> tt) == True{} : Bool}
) -> {T.word.val('-' <> hh <> tt) == n1.dw.G(T.Minus{}, D1.abnf.no_us(hh <> tt)) : T.Got}:
  match tt:
    case []:
      n1.dw.om(hh, gs.body.one(hh, D1.abnf.DIGIT(hh), {==}, hu))
    case +t1 <> +ts:
      n1.dw.mm(hh, t1, ts, gs.body.l(hh, t1, ts, hu), gs.body.r(hh, t1, ts, hu))

# a minus and an unsigned-dec-int
def n1.dw.neg(
  tt: List<&2, Char>,
  +hu: {D1.abnf.unsigned_dec_int(tt) == True{} : Bool}
) -> {T.word.val('-' <> tt) == n1.dw.G(T.Minus{}, D1.abnf.no_us(tt)) : T.Got}:
  match tt:
    case []:
      Eq.bit.absurd(&2, {T.word.val(['-']) == n1.dw.G(T.Minus{}, D1.abnf.no_us([])) : T.Got}, hu)
    case +hh <> +tl:
      n1.dw.neg.go(hh, tl, hu)

# after a plus
def n1.dw.pos.go(
  +hh: Char,
  tt: List<&2, Char>,
  +hu: {D1.abnf.unsigned_dec_int(hh <> tt) == True{} : Bool}
) -> {T.word.val('+' <> hh <> tt) == n1.dw.G(T.Plus{}, D1.abnf.no_us(hh <> tt)) : T.Got}:
  match tt:
    case []:
      n1.dw.op(hh, gs.body.one(hh, D1.abnf.DIGIT(hh), {==}, hu))
    case +t1 <> +ts:
      n1.dw.mp(hh, t1, ts, gs.body.l(hh, t1, ts, hu), gs.body.r(hh, t1, ts, hu))

# a plus and an unsigned-dec-int
def n1.dw.pos(
  tt: List<&2, Char>,
  +hu: {D1.abnf.unsigned_dec_int(tt) == True{} : Bool}
) -> {T.word.val('+' <> tt) == n1.dw.G(T.Plus{}, D1.abnf.no_us(tt)) : T.Got}:
  match tt:
    case []:
      Eq.bit.absurd(&2, {T.word.val(['+']) == n1.dw.G(T.Plus{}, D1.abnf.no_us([])) : T.Got}, hu)
    case +hh <> +tl:
      n1.dw.pos.go(hh, tl, hu)

# what the dec-int reading claims of a word
def n1.dw.W(+cs: List<&2, Char>) -> Type:
  {T.word.val(cs) == n1.dw.G(D1.abnf.dec_sign(cs), D1.abnf.dec_digits(cs)) : T.Got}

# by the first character: a minus, a plus, or the first digit
def n1.dw.top(
  +hh: Char,
  +tt: List<&2, Char>,
  mm: Bool,
  +em: {D1.abnf.minus(hh) == mm : Bool},
  pp: Bool,
  +ep: {D1.abnf.plus(hh) == pp : Bool},
  +h: {D1.abnf.dec_int(hh <> tt) == True{} : Bool}
) -> n1.dw.W(hh <> tt):
  match mm:
    case True{}:
      +ee = {Equal.sym(Char, hh, '-', M4.gs.minus(hh, em)) : {'-' == hh : Char}}
      %ee : n1.dw.W(_ <> tt)
      n1.dw.neg(tt, M4.or.fl(D1.abnf.unsigned_dec_int(tt), Equal.trans(Bool, D1.abnf.dec_int('-' <> tt),
        D1.abnf.dec_int(hh <> tt), True{}, Equal.cong(Char, Bool, cc => D1.abnf.dec_int(cc <> tt), '-', hh, ee),
        h)))
    case False{}:
      match pp:
        case True{}:
          +ee = {Equal.sym(Char, hh, '+', M4.gs.plus(hh, ep)) : {'+' == hh : Char}}
          %ee : n1.dw.W(_ <> tt)
          n1.dw.pos(tt, M4.or.fl(D1.abnf.unsigned_dec_int(tt), Equal.trans(Bool, D1.abnf.dec_int('+' <> tt),
            D1.abnf.dec_int(hh <> tt), True{}, Equal.cong(Char, Bool, cc => D1.abnf.dec_int(cc <> tt), '+', hh,
            ee), h)))
        case False{}:
          %Equal.sym(Bool, D1.abnf.minus(hh), False{}, em) : {T.word.val(hh <> tt)
            == n1.dw.G(D1.abnf.sign.pick(_), D1.abnf.digits.pick(Bool.or(_, D1.abnf.plus(hh)), hh, tt))
            : T.Got}
          %Equal.sym(Bool, D1.abnf.plus(hh), False{}, ep) : {T.word.val(hh <> tt)
            == n1.dw.G(T.Plus{}, D1.abnf.digits.pick(Bool.or(False{}, _), hh, tt)) : T.Got}
          n1.dw.uns(hh, tt, Equal.trans(Bool, D1.abnf.unsigned_dec_int(hh <> tt), D1.abnf.dec_int(hh <> tt),
            True{}, gs.top.hu(hh, tt, em, ep), h))

# a dec-int word is read as its sign and digits, tested for range
def n1.dw(+cs: List<&2, Char>, +h: {D1.abnf.dec_int(cs) == True{} : Bool}) -> n1.dw.W(cs):
  match cs:
    case []:
      Eq.bit.absurd(&1, n1.dw.W([]), h)
    case +hh <> +tt:
      n1.dw.top(hh, tt, D1.abnf.minus(hh), {==}, D1.abnf.plus(hh), {==}, h)

# The integer law. An integer word read in range is its sign and its value's
# canonical digits, so a value matches the reading exactly when it is
# canonical and worth what the word's digits are; out of range, and outside
# the integer rule, a word is read as no integer.

# what an integer word denotes, by its sign, its digits and their radix
def n1.gi(vv: T.Val, +sg: T.Sign, +bd: List<&2, Char>, +rr: Nat) -> Bool:
  match vv:
    case T.VInt{sv, +dv}:
      Bool.and(D2.sign.eq(sv, sg), Bool.and(D1.g.dec.canon(dv), Nat.is_eq(D1.g.num.nat(String.to_list(dv), 10n,
        0n), D1.g.num.nat(bd, rr, 0n))))
    case _v:
      False{}

# which is what the grammar's value relation asks of an integer word
def n1.gv(
  vv: T.Val,
  +cs: List<&2, Char>
) -> {D1.g.val(D3.GvInteger{cs}, vv) == n1.gi(vv, D1.abnf.dec_sign(cs), D1.g.int.body(cs),
  D1.g.int.radix(cs)) : Bool}:
  match vv:
    case T.VInt{_s, _d}:
      {==}
    case T.VStr{_t}:
      {==}
    case T.VSpan{_s, _n}:
      {==}
    case T.VFlo{_s, _t}:
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

# an integer, tested for range, is read as a value exactly when it is in
# range and the value is canonical and worth what its digits are
def n1.core(
  rg: Bool,
  vv: T.Val,
  +sg: T.Sign,
  +dd: String,
  +bd: List<&2, Char>,
  +rr: Nat,
  +hd: {D1.g.dec.canon(dd) == True{} : Bool},
  +hv: {n1.h10(dd) == D1.g.num.nat(bd, rr, 0n) : Nat}
) -> {L1.n1.got.int(T.num.fin.range(rg, sg, dd), vv) == Bool.and(rg, n1.gi(vv, sg, bd, rr)) : Bool}:
  match rg:
    case True{}:
      match vv:
        case T.VInt{+sv, +dv}:
          %hv : {Bool.and(D2.sign.eq(sv, sg), String.eq(dv, dd)) == Bool.and(D2.sign.eq(sv, sg),
            Bool.and(D1.g.dec.canon(dv), Nat.is_eq(n1.h10(dv), _))) : Bool}
          Equal.cong(Bool, Bool, bb => Bool.and(D2.sign.eq(sv, sg), bb), String.eq(dv, dd),
            Bool.and(D1.g.dec.canon(dv), Nat.is_eq(n1.h10(dv), n1.h10(dd))), n1.uq(dv, dd, hd))
        case T.VStr{_t}:
          {==}
        case T.VSpan{_s, _n}:
          {==}
        case T.VFlo{_s, _t}:
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
    case False{}:
      {==}

# the type of n1.px.v's es
def n1.px.v.P1(+rx: D1.ARadix, +cx: Char, +rest: List<&2, Char>) -> Type:
  {T.num.go('0' <> cx <> rest, T.num.start()) == T.num.go(rest, T.Num{T.NBase{}, T.Plus{}, n1.rb(rx), [], False{},
    False{}, ""}) : T.Num}

# a prefixed integer's word is read as its numeral, tested for range
def n1.px.v(
  +uu: Unit,
  +rx: D1.ARadix,
  +cx: Char,
  +rest: List<&2, Char>,
  +vv: T.Val,
  +hb: {n1.bg(rest, rx) == True{} : Bool},
  es: n1.px.v.P1(rx, cx, rest)
) -> {L1.n1.got.int(T.word.val('0' <> cx <> rest), vv) == Bool.and(T.i64.fits(T.Plus{}, T.dec.text(n1.cv(rx, rest,
  []))), n1.gi(vv, T.Plus{}, rest, U32.to_nat(n1.rb(rx)))) : Bool}:
  +hr = {n1.rr.bg(rest, rx, hb) : {n1.rr(rx, rest) == True{} : Bool}}
  +ds = n1.cv(rx, rest, [])
  +hd = {n1.cvok(uu, rx, rest, [], {==}, hr) : {n1.d10(ds) == True{} : Bool}}
  +est = {Equal.trans(T.Num, T.num.go('0' <> cx <> rest, T.num.start()), T.num.go(rest, T.Num{T.NBase{}, T.Plus{},
    n1.rb(rx), [], False{}, False{}, ""}), n1.sb(T.Plus{}, rx, ds), es, n1.B0v(rest, T.Plus{}, rx, hb))
    : {T.num.go('0' <> cx <> rest, T.num.start()) == n1.sb(T.Plus{}, rx, ds) : T.Num}}
  %Equal.sym(T.Got, T.word.val('0' <> cx <> rest), T.num.fin(n1.sb(T.Plus{}, rx, ds), '0' <> cx <> rest),
    Equal.trans(T.Got, T.word.val('0' <> cx <> rest), T.word.num('0' <> cx <> rest), T.num.fin(n1.sb(T.Plus{}, rx,
    ds), '0' <> cx <> rest), M7.n1.wv('0' <> cx <> rest, Equal.cong(T.Num, Bool, nn => M7.n1.isbad(nn),
    T.num.go('0' <> cx <> rest, T.num.start()), n1.sb(T.Plus{}, rx, ds), est)), Equal.cong(T.Num, T.Got,
    nn => T.num.fin(nn, '0' <> cx <> rest), T.num.go('0' <> cx <> rest, T.num.start()), n1.sb(T.Plus{}, rx, ds),
    est))) : {L1.n1.got.int(_, vv) == Bool.and(T.i64.fits(T.Plus{}, T.dec.text(ds)), n1.gi(vv, T.Plus{}, rest,
    U32.to_nat(n1.rb(rx)))) : Bool}
  n1.core(T.i64.fits(T.Plus{}, T.dec.text(ds)), vv, T.Plus{}, T.dec.text(ds), rest, U32.to_nat(n1.rb(rx)),
    n1.text.c(ds, hd), Equal.trans(Nat, n1.h10(T.dec.text(ds)), n1.W(ds), D1.g.num.nat(rest, U32.to_nat(n1.rb(rx)),
    0n), n1.text.v(ds, hd), n1.cvW(uu, rx, rest, [], {==}, hr)))

# the prose's order and i64.ord agree
def n1.ordeq(aa: Cmp, +bb: Cmp) -> {D1.prose.dec_le.ord(aa, bb) == T.i64.ord(aa, bb) : Cmp}:
  match aa:
    case EQ{}:
      {==}
    case LT{}:
      {==}
    case GT{}:
      {==}

# the prose's walk over a numeral against a limit is i64.step's
def n1.dle(aa: String, bb: String, +oo: Cmp) -> {D1.prose.dec_le(aa, bb, oo) == T.i64.step(aa, bb, oo) : Bool}:
  match aa bb:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{_h, _t}:
      {==}
    case SCon{_h, _t} SNil{}:
      {==}
    case SCon{+xx, +xt} SCon{+yy, +yt}:
      %Equal.sym(Cmp, D1.prose.dec_le.ord(oo, U32.cmp(Char.to_u32(xx), Char.to_u32(yy))), T.i64.ord(oo,
        U32.cmp(Char.to_u32(xx), Char.to_u32(yy))), n1.ordeq(oo, U32.cmp(Char.to_u32(xx),
          Char.to_u32(yy)))) : {D1.prose.dec_le(xt, yt, _) == T.i64.step(xt, yt,
        T.i64.ord(oo, U32.cmp(Char.to_u32(xx), Char.to_u32(yy)))) : Bool}
      n1.dle(xt, yt, T.i64.ord(oo, U32.cmp(Char.to_u32(xx), Char.to_u32(yy))))

# the prose's limits are the code's
def n1.dlim(sg: T.Sign) -> {D1.prose.i64.limit(sg) == T.i64.limit(sg) : String}:
  match sg:
    case T.Plus{}:
      {==}
    case T.Minus{}:
      {==}

# so the prose's range of a dec-int is i64.fits
def n1.dfit(
  +sg: T.Sign,
  +dd: String
) -> {D1.prose.dec_le(dd, D1.prose.i64.limit(sg), EQ{}) == T.i64.fits(sg, dd) : Bool}:
  %Equal.sym(String, D1.prose.i64.limit(sg), T.i64.limit(sg), n1.dlim(sg)) : {D1.prose.dec_le(dd, _, EQ{})
    == T.i64.fits(sg, dd) : Bool}
  n1.dle(dd, T.i64.limit(sg), EQ{})

# a digit by the code is a DIGIT
def n1.dig.D(cc: Char, +hc: {Char.is_digit(cc) == True{} : Bool}) -> {D1.abnf.DIGIT(cc) == True{} : Bool}:
  match cc:
    case Chr{_c}:
      hc

# digits by the code are DIGITs
def n1.wfall(ss: String, +hs: {T.wf.digits(ss) == True{} : Bool}) -> {D1.g.dec.all(ss) == True{} : Bool}:
  match ss:
    case SNil{}:
      {==}
    case SCon{+hh, +tt}:
      M9.and.tt(D1.abnf.DIGIT(hh), D1.g.dec.all(tt), n1.dig.D(hh, M6.then.l(Char.is_digit(hh), tt, hs)), n1.wfall(tt,
        M6.then.r(Char.is_digit(hh), tt, hs)))

# an unsigned-dec-int's digits, its underscores removed, are canonical
def n1.ucanon(
  +hh: Char,
  tt: List<&2, Char>,
  +hu: {D1.abnf.unsigned_dec_int(hh <> tt) == True{} : Bool}
) -> {D1.g.dec.canon(D1.abnf.no_us(hh <> tt)) == True{} : Bool}:
  match tt:
    case []:
      M6.dg.elim(zz => {D1.g.dec.canon(D1.abnf.no_us([zz])) == True{} : Bool}, hh, gs.body.one(hh,
        D1.abnf.DIGIT(hh), {==}, hu), {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})
    case +t1 <> +ts:
      +hd = {gs.body.l(hh, t1, ts, hu) : {D1.abnf.digit1_9(hh) == True{} : Bool}}
      +hx = {M4.gs.d19(hh, hd) : {Char.is_digit(hh) == True{} : Bool}}
      %gs.nu(hh, t1 <> ts, M4.gs.nous(hh, hx)) : {D1.g.dec.canon(_) == True{} : Bool}
      %Equal.sym(Bool, D1.abnf.DIGIT(hh), True{}, n1.dig.D(hh, hx)) : {Bool.and(_, Bool.or(Bool.and(
        D1.abnf.cp(hh, 48), String.is_empty(D1.abnf.no_us(t1 <> ts))), Bool.and(D1.abnf.digit1_9(hh),
        D1.g.dec.all(D1.abnf.no_us(t1 <> ts))))) == True{} : Bool}
      %Equal.sym(Bool, D1.abnf.cp(hh, 48), False{}, Equal.trans(Bool, D1.abnf.cp(hh, 48), Char.is_eq(hh, '0'),
        False{}, Equal.sym(Bool, Char.is_eq(hh, Chr{48}), D1.abnf.cp(hh, 48), n1.cp(hh, 48)), gs.d19z(hh, hd))) :
        {Bool.and(True{}, Bool.or(Bool.and(_, String.is_empty(D1.abnf.no_us(t1 <> ts))),
        Bool.and(D1.abnf.digit1_9(hh), D1.g.dec.all(D1.abnf.no_us(t1 <> ts))))) == True{} : Bool}
      %Equal.sym(Bool, D1.abnf.digit1_9(hh), True{}, hd) : {Bool.and(True{}, Bool.or(Bool.and(False{},
        String.is_empty(D1.abnf.no_us(t1 <> ts))), Bool.and(_, D1.g.dec.all(D1.abnf.no_us(t1 <> ts))))) ==
        True{} : Bool}
      n1.wfall(D1.abnf.no_us(t1 <> ts), gs.digits(t1 <> ts, gs.body.r(hh, t1, ts, hu)))

# an unsigned-dec-int's digits are canonical
def n1.ucan(
  tt: List<&2, Char>,
  +hu: {D1.abnf.unsigned_dec_int(tt) == True{} : Bool}
) -> {D1.g.dec.canon( D1.abnf.no_us(tt)) == True{} : Bool}:
  match tt:
    case []:
      Eq.bit.absurd(&2, {D1.g.dec.canon(D1.abnf.no_us([])) == True{} : Bool}, hu)
    case +hh <> +tl:
      n1.ucanon(hh, tl, hu)

# what the canonical lemma claims of a word
def n1.dcan.W(+cs: List<&2, Char>) -> Type:
  {D1.g.dec.canon(D1.abnf.dec_digits(cs)) == True{} : Bool}

# a dec-int's digits are canonical, by its first character: a minus, a plus,
# or the first digit
def n1.dcan.top(
  +hh: Char,
  +tt: List<&2, Char>,
  mm: Bool,
  +em: {D1.abnf.minus(hh) == mm : Bool},
  pp: Bool,
  +ep: {D1.abnf.plus(hh) == pp : Bool},
  +h: {D1.abnf.dec_int(hh <> tt) == True{} : Bool}
) -> n1.dcan.W(hh <> tt):
  match mm:
    case True{}:
      +ee = {Equal.sym(Char, hh, '-', M4.gs.minus(hh, em)) : {'-' == hh : Char}}
      %ee : n1.dcan.W(_ <> tt)
      n1.ucan(tt, M4.or.fl(D1.abnf.unsigned_dec_int(tt), Equal.trans(Bool, D1.abnf.dec_int('-' <> tt),
        D1.abnf.dec_int(hh <> tt), True{}, Equal.cong(Char, Bool, cc => D1.abnf.dec_int(cc <> tt), '-', hh, ee),
        h)))
    case False{}:
      match pp:
        case True{}:
          +ee = {Equal.sym(Char, hh, '+', M4.gs.plus(hh, ep)) : {'+' == hh : Char}}
          %ee : n1.dcan.W(_ <> tt)
          n1.ucan(tt, M4.or.fl(D1.abnf.unsigned_dec_int(tt), Equal.trans(Bool, D1.abnf.dec_int('+' <> tt),
            D1.abnf.dec_int(hh <> tt), True{}, Equal.cong(Char, Bool, cc => D1.abnf.dec_int(cc <> tt), '+', hh,
            ee), h)))
        case False{}:
          %Equal.sym(Bool, D1.abnf.minus(hh), False{}, em) : {D1.g.dec.canon(D1.abnf.digits.pick(Bool.or(_,
            D1.abnf.plus(hh)), hh, tt)) == True{} : Bool}
          %Equal.sym(Bool, D1.abnf.plus(hh), False{}, ep) : {D1.g.dec.canon(D1.abnf.digits.pick(Bool.or(False{},
            _), hh, tt)) == True{} : Bool}
          n1.ucan(hh <> tt, Equal.trans(Bool, D1.abnf.unsigned_dec_int(hh <> tt), D1.abnf.dec_int(hh <> tt),
            True{}, gs.top.hu(hh, tt, em, ep), h))

# a dec-int's digits are canonical
def n1.dcan(+cs: List<&2, Char>, +h: {D1.abnf.dec_int(cs) == True{} : Bool}) -> n1.dcan.W(cs):
  match cs:
    case []:
      Eq.bit.absurd(&1, n1.dcan.W([]), h)
    case +hh <> +tt:
      n1.dcan.top(hh, tt, D1.abnf.minus(hh), {==}, D1.abnf.plus(hh), {==}, h)

# what the integer law claims of a word
def n1.int.G(+cs: List<&2, Char>, +vv: T.Val) -> Type:
  {L1.n1.got.int(T.word.val(cs), vv) == Bool.and(Bool.and(D1.abnf.integer(cs), D1.prose.int_in_range(cs)),
    D1.g.val(D3.GvInteger{cs}, vv)) : Bool}

# no datetime is an integer
def n1.when.nint(ww: T.WhenOut, +vv: T.Val) -> {L1.n1.got.int(T.word.from.when(ww), vv) == False{} : Bool}:
  match ww:
    case T.WSome{_w}:
      {==}
    case T.WFail{_y}:
      {==}
    case T.WSkip{}:
      {==}

# a finished scan with no integer's shape is read as no integer, by its
# fields
def n1.fin.nint.go(
  uz: Bool,
  nk: T.NK,
  saw: Bool,
  sd: Bool,
  +sn: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +why: String,
  +cs: List<&2, Char>,
  +vv: T.Val,
  +esd: {T.num.signed(cs) == sd : Bool},
  +hh: {n1.ish.nk(nk, saw, uz, sd) == False{} : Bool}
) -> {L1.n1.got.int(T.num.fin(T.Num{nk, sn, base, ds, uz, saw, why}, cs), vv) == False{} : Bool}:
  match uz:
    case True{}:
      {==}
    case False{}:
      match nk:
        case T.NZero{}:
          Eq.bit.absurd2(&2, {L1.n1.got.int(T.num.fin(T.Num{T.NZero{}, sn, base, ds, False{}, saw, why}, cs), vv)
            == False{} : Bool}, hh)
        case T.NDig{}:
          match saw:
            case True{}:
              Eq.bit.absurd2(&2, {L1.n1.got.int(T.num.fin(T.Num{T.NDig{}, sn, base, ds, False{}, True{}, why}, cs),
                vv) == False{} : Bool}, hh)
            case False{}:
              {==}
        case T.NBase{}:
          match saw sd:
            case True{} True{}:
              %Equal.sym(Bool, T.num.signed(cs), True{}, esd) : {L1.n1.got.int(T.num.fin.base(_, True{}, sn, ds), vv)
                == False{} : Bool}
              {==}
            case True{} False{}:
              Eq.bit.absurd2(&2, {L1.n1.got.int(T.num.fin(T.Num{T.NBase{}, sn, base, ds, False{}, True{}, why}, cs),
                vv) == False{} : Bool}, hh)
            case False{} True{}:
              %Equal.sym(Bool, T.num.signed(cs), True{}, esd) : {L1.n1.got.int(T.num.fin.base(_, False{}, sn, ds),
                vv) == False{} : Bool}
              {==}
            case False{} False{}:
              %Equal.sym(Bool, T.num.signed(cs), False{}, esd) : {L1.n1.got.int(T.num.fin.base(_, False{}, sn, ds),
                vv) == False{} : Bool}
              {==}
        case T.NFrac{}:
          match saw:
            case True{}:
              {==}
            case False{}:
              {==}
        case T.NEDig{}:
          match saw:
            case True{}:
              {==}
            case False{}:
              {==}
        case T.NLead{}:
          {==}
        case T.NSign{}:
          {==}
        case T.NExp{}:
          {==}
        case T.NBad{}:
          {==}

# a finished scan with no integer's shape is read as no integer
def n1.fin.nint(
  st: T.Num,
  +cs: List<&2, Char>,
  +vv: T.Val,
  +hh: {n1.ish(st, T.num.signed(cs)) == False{} : Bool}
) -> {L1.n1.got.int(T.num.fin(st, cs), vv) == False{} : Bool}:
  match st:
    case T.Num{nk, +sg, +base, +ds, us, saw, +why}:
      n1.fin.nint.go(us, nk, saw, T.num.signed(cs), sg, base, ds, why, cs, vv, {==}, hh)

# a word sent to the datetime reader, or to the numeral scan with no
# integer's shape, is read as no integer
def n1.int.ns.go(
  ad: Bool,
  +cs: List<&2, Char>,
  +vv: T.Val,
  +hh: {n1.ish(T.num.go(cs, T.num.start()), T.num.signed(cs)) == False{} : Bool}
) -> {L1.n1.got.int(T.word.route.date(ad, cs), vv) == False{} : Bool}:
  match ad:
    case True{}:
      n1.when.nint(T.when.read(cs), vv)
    case False{}:
      n1.fin.nint(T.num.go(cs, T.num.start()), cs, vv, hh)

# a word outside the integer rule, special or not, is read as no integer
def n1.int.out.go(
  sp: Bool,
  +cs: List<&2, Char>,
  +vv: T.Val,
  +es: {M11.n1.isspec(cs) == sp : Bool},
  +hh: {n1.ish(T.num.go(cs, T.num.start()), T.num.signed(cs)) == False{} : Bool}
) -> {L1.n1.got.int(T.word.val(cs), vv) == False{} : Bool}:
  match sp:
    case True{}:
      M11.n1.spec.split(xs => {L1.n1.got.int(T.word.val(xs), vv) == False{} : Bool}, cs, es, {==}, {==}, {==}, {==},
        {==}, {==}, {==}, {==})
    case False{}:
      %Equal.sym(T.Got, T.word.val(cs), T.word.route.date(T.word.as_date(T.word.or(T.word.colon(cs), T.word.dash(cs,
        True{})), T.word.ee(cs)), cs), M11.n1.wv.ns(cs, es)) : {L1.n1.got.int(_, vv) == False{} : Bool}
      n1.int.ns.go(T.word.as_date(T.word.or(T.word.colon(cs), T.word.dash(cs, True{})), T.word.ee(cs)), cs, vv, hh)

# a word outside the integer rule is read as no integer, and matches none
def n1.int.out(+cs: List<&2, Char>, +vv: T.Val, +ei: {D1.abnf.integer(cs) == False{} : Bool}) -> n1.int.G(cs, vv):
  %Equal.sym(Bool, D1.abnf.integer(cs), False{}, ei) : {L1.n1.got.int(T.word.val(cs), vv) == Bool.and(Bool.and(_,
    D1.prose.int_in_range(cs)), D1.g.val(D3.GvInteger{cs}, vv)) : Bool}
  n1.int.out.go(M11.n1.isspec(cs), cs, vv, {==}, Equal.trans(Bool, n1.ish(T.num.go(cs, T.num.start()),
      T.num.signed(cs)),
    D1.abnf.integer(cs), False{}, n1.int.sh(cs), ei))

# what a hexadecimal integer word matches: the prose's range, and the value
# of its digits after the prefix in base 16
def n1.rhs.x(
  +c2: Char,
  +rest: List<&2, Char>,
  +vv: T.Val,
  +hb: {n1.bg(c2 <> rest, D1.AHex{}) == True{} : Bool}
) -> {Bool.and(Bool.and(D1.abnf.integer('0' <> 'x' <> c2 <> rest), D1.prose.int_in_range('0' <> 'x' <> c2 <> rest)),
  D1.g.val(D3.GvInteger{'0' <> 'x' <> c2 <> rest}, vv)) == Bool.and(D1.prose.radix_in_range(D1.AHex{},
  '0' <> 'x' <> c2 <> rest), n1.gi(vv, T.Plus{}, c2 <> rest, 16n)) : Bool}:
  +cs = {'0' <> 'x' <> c2 <> rest : List<&2, Char>}
  %Equal.sym(Bool, D1.g.val(D3.GvInteger{cs}, vv), n1.gi(vv, D1.abnf.dec_sign(cs), D1.g.int.body(cs),
    D1.g.int.radix(cs)), n1.gv(vv, cs)) : {Bool.and(Bool.and(D1.abnf.integer(cs), D1.prose.int_in_range(cs)), _)
    == Bool.and(D1.prose.radix_in_range(D1.AHex{}, cs), n1.gi(vv, T.Plus{}, c2 <> rest, 16n)) : Bool}
  %Equal.sym(Bool, D1.abnf.hex_int(cs), True{}, hb) : {Bool.and(Bool.and(Bool.or(D1.abnf.dec_int(cs), Bool.or(_,
    Bool.or(D1.abnf.oct_int(cs), D1.abnf.bin_int(cs)))), D1.prose.int_in_range.pick(_, D1.abnf.oct_int(cs),
    D1.abnf.bin_int(cs), cs)), n1.gi(vv, D1.abnf.dec_sign(cs), D1.g.int.body.pick(Bool.or(_,
    Bool.or(D1.abnf.oct_int(cs), D1.abnf.bin_int(cs))), cs), D1.g.int.radix.pick(_, D1.abnf.oct_int(cs),
    D1.abnf.bin_int(cs)))) == Bool.and(D1.prose.radix_in_range(D1.AHex{}, cs), n1.gi(vv, T.Plus{}, c2 <> rest,
    16n)) : Bool}
  {==}

# and an octal one, in base 8
def n1.rhs.o(
  +c2: Char,
  +rest: List<&2, Char>,
  +vv: T.Val,
  +hb: {n1.bg(c2 <> rest, D1.AOct{}) == True{} : Bool}
) -> {Bool.and(Bool.and(D1.abnf.integer('0' <> 'o' <> c2 <> rest), D1.prose.int_in_range('0' <> 'o' <> c2 <> rest)),
  D1.g.val(D3.GvInteger{'0' <> 'o' <> c2 <> rest}, vv)) == Bool.and(D1.prose.radix_in_range(D1.AOct{},
  '0' <> 'o' <> c2 <> rest), n1.gi(vv, T.Plus{}, c2 <> rest, 8n)) : Bool}:
  +cs = {'0' <> 'o' <> c2 <> rest : List<&2, Char>}
  %Equal.sym(Bool, D1.g.val(D3.GvInteger{cs}, vv), n1.gi(vv, D1.abnf.dec_sign(cs), D1.g.int.body(cs),
    D1.g.int.radix(cs)), n1.gv(vv, cs)) : {Bool.and(Bool.and(D1.abnf.integer(cs), D1.prose.int_in_range(cs)), _)
    == Bool.and(D1.prose.radix_in_range(D1.AOct{}, cs), n1.gi(vv, T.Plus{}, c2 <> rest, 8n)) : Bool}
  %Equal.sym(Bool, D1.abnf.oct_int(cs), True{}, hb) : {Bool.and(Bool.and(Bool.or(D1.abnf.dec_int(cs),
    Bool.or(D1.abnf.hex_int(cs), Bool.or(_, D1.abnf.bin_int(cs)))), D1.prose.int_in_range.pick(
    D1.abnf.hex_int(cs), _, D1.abnf.bin_int(cs), cs)), n1.gi(vv, D1.abnf.dec_sign(cs), D1.g.int.body.pick(
    Bool.or(D1.abnf.hex_int(cs), Bool.or(_, D1.abnf.bin_int(cs))), cs), D1.g.int.radix.pick(
    D1.abnf.hex_int(cs), _, D1.abnf.bin_int(cs)))) == Bool.and(D1.prose.radix_in_range(D1.AOct{}, cs),
    n1.gi(vv, T.Plus{}, c2 <> rest, 8n)) : Bool}
  {==}

# and a binary one, in base 2
def n1.rhs.b(
  +c2: Char,
  +rest: List<&2, Char>,
  +vv: T.Val,
  +hb: {n1.bg(c2 <> rest, D1.ABin{}) == True{} : Bool}
) -> {Bool.and(Bool.and(D1.abnf.integer('0' <> 'b' <> c2 <> rest), D1.prose.int_in_range('0' <> 'b' <> c2 <> rest)),
  D1.g.val(D3.GvInteger{'0' <> 'b' <> c2 <> rest}, vv)) == Bool.and(D1.prose.radix_in_range(D1.ABin{},
  '0' <> 'b' <> c2 <> rest), n1.gi(vv, T.Plus{}, c2 <> rest, 2n)) : Bool}:
  +cs = {'0' <> 'b' <> c2 <> rest : List<&2, Char>}
  %Equal.sym(Bool, D1.g.val(D3.GvInteger{cs}, vv), n1.gi(vv, D1.abnf.dec_sign(cs), D1.g.int.body(cs),
    D1.g.int.radix(cs)), n1.gv(vv, cs)) : {Bool.and(Bool.and(D1.abnf.integer(cs), D1.prose.int_in_range(cs)), _)
    == Bool.and(D1.prose.radix_in_range(D1.ABin{}, cs), n1.gi(vv, T.Plus{}, c2 <> rest, 2n)) : Bool}
  %Equal.sym(Bool, D1.abnf.bin_int(cs), True{}, hb) : {Bool.and(Bool.and(Bool.or(D1.abnf.dec_int(cs),
    Bool.or(D1.abnf.hex_int(cs), Bool.or(D1.abnf.oct_int(cs), _))), D1.prose.int_in_range.pick(
    D1.abnf.hex_int(cs), D1.abnf.oct_int(cs), _, cs)), n1.gi(vv, D1.abnf.dec_sign(cs), D1.g.int.body.pick(
    Bool.or(D1.abnf.hex_int(cs), Bool.or(D1.abnf.oct_int(cs), _)), cs), D1.g.int.radix.pick(
    D1.abnf.hex_int(cs), D1.abnf.oct_int(cs), _))) == Bool.and(D1.prose.radix_in_range(D1.ABin{}, cs),
    n1.gi(vv, T.Plus{}, c2 <> rest, 2n)) : Bool}
  {==}

# a character that the prefix's rule takes as a code point is that character
def n1.cpc(+cc: Char, +nn: U32, +hh: {D1.abnf.cp(cc, nn) == True{} : Bool}) -> {Chr{nn} == cc : Char}:
  Equal.sym(Char, cc, Chr{nn}, Eq.char_eq_true(cc, Chr{nn}, Equal.trans(Bool, Char.is_eq(cc, Chr{nn}),
    D1.abnf.cp(cc, nn), True{}, n1.cp(cc, nn), hh)))

# a hexadecimal integer word: read as its numeral, in range as the prose
# says, and worth its digits' value in base 16
def n1.px.x(
  +uu: Unit,
  +c0: Char,
  +c1: Char,
  +c2: Char,
  +rest: List<&2, Char>,
  +vv: T.Val,
  +hp: {D1.abnf.hex_int(c0 <> c1 <> c2 <> rest) == True{} : Bool}
) -> n1.int.G(c0 <> c1 <> c2 <> rest, vv):
  +h12 = {Eq.and.right(D1.abnf.cp(c0, 48), Bool.and(D1.abnf.cp(c1, 120), n1.bg(c2 <> rest, D1.AHex{})), hp)
    : {Bool.and(D1.abnf.cp(c1, 120), n1.bg(c2 <> rest, D1.AHex{})) == True{} : Bool}}
  +hb = {Eq.and.right(D1.abnf.cp(c1, 120), n1.bg(c2 <> rest, D1.AHex{}), h12) : {n1.bg(c2 <> rest, D1.AHex{})
    == True{} : Bool}}
  %n1.cpc(c0, 48, Eq.and.left(D1.abnf.cp(c0, 48), Bool.and(D1.abnf.cp(c1, 120), n1.bg(c2 <> rest, D1.AHex{})),
    hp)) : n1.int.G(_ <> c1 <> c2 <> rest, vv)
  %n1.cpc(c1, 120, Eq.and.left(D1.abnf.cp(c1, 120), n1.bg(c2 <> rest, D1.AHex{}), h12)) : n1.int.G('0' <> _ <> c2
    <> rest, vv)
  Equal.trans(Bool, L1.n1.got.int(T.word.val('0' <> 'x' <> c2 <> rest), vv), Bool.and(T.i64.fits(T.Plus{},
    T.dec.text(n1.cv(D1.AHex{}, c2 <> rest, []))), n1.gi(vv, T.Plus{}, c2 <> rest, 16n)), Bool.and(Bool.and(
    D1.abnf.integer('0' <> 'x' <> c2 <> rest), D1.prose.int_in_range('0' <> 'x' <> c2 <> rest)),
    D1.g.val(D3.GvInteger{'0' <> 'x' <> c2 <> rest}, vv)), n1.px.v(uu, D1.AHex{}, 'x', c2 <> rest, vv, hb,
    {==}), Equal.trans(Bool, Bool.and(T.i64.fits(T.Plus{}, T.dec.text(n1.cv(D1.AHex{}, c2 <> rest, []))),
    n1.gi(vv, T.Plus{}, c2 <> rest, 16n)), Bool.and(D1.prose.radix_in_range(D1.AHex{}, '0' <> 'x' <> c2 <> rest),
    n1.gi(vv, T.Plus{}, c2 <> rest, 16n)), Bool.and(Bool.and(D1.abnf.integer('0' <> 'x' <> c2 <> rest),
    D1.prose.int_in_range('0' <> 'x' <> c2 <> rest)), D1.g.val(D3.GvInteger{'0' <> 'x' <> c2 <> rest}, vv)),
    Equal.cong(Bool, Bool, bb => Bool.and(bb, n1.gi(vv, T.Plus{}, c2 <> rest, 16n)), T.i64.fits(T.Plus{},
    T.dec.text(n1.cv(D1.AHex{}, c2 <> rest, []))), D1.prose.radix_in_range(D1.AHex{}, '0' <> 'x' <> c2 <>
    rest), n1.rng.x(uu, c2 <> rest, hb)), Equal.sym(Bool, Bool.and(Bool.and(D1.abnf.integer('0' <> 'x' <> c2 <>
    rest), D1.prose.int_in_range('0' <> 'x' <> c2 <> rest)), D1.g.val(D3.GvInteger{'0' <> 'x' <> c2 <> rest},
    vv)), Bool.and(D1.prose.radix_in_range(D1.AHex{}, '0' <> 'x' <> c2 <> rest), n1.gi(vv, T.Plus{}, c2 <> rest,
    16n)), n1.rhs.x(c2, rest, vv, hb))))

# an octal integer word, in base 8
def n1.px.o(
  +uu: Unit,
  +c0: Char,
  +c1: Char,
  +c2: Char,
  +rest: List<&2, Char>,
  +vv: T.Val,
  +hp: {D1.abnf.oct_int(c0 <> c1 <> c2 <> rest) == True{} : Bool}
) -> n1.int.G(c0 <> c1 <> c2 <> rest, vv):
  +h12 = {Eq.and.right(D1.abnf.cp(c0, 48), Bool.and(D1.abnf.cp(c1, 111), n1.bg(c2 <> rest, D1.AOct{})), hp)
    : {Bool.and(D1.abnf.cp(c1, 111), n1.bg(c2 <> rest, D1.AOct{})) == True{} : Bool}}
  +hb = {Eq.and.right(D1.abnf.cp(c1, 111), n1.bg(c2 <> rest, D1.AOct{}), h12) : {n1.bg(c2 <> rest, D1.AOct{})
    == True{} : Bool}}
  %n1.cpc(c0, 48, Eq.and.left(D1.abnf.cp(c0, 48), Bool.and(D1.abnf.cp(c1, 111), n1.bg(c2 <> rest, D1.AOct{})),
    hp)) : n1.int.G(_ <> c1 <> c2 <> rest, vv)
  %n1.cpc(c1, 111, Eq.and.left(D1.abnf.cp(c1, 111), n1.bg(c2 <> rest, D1.AOct{}), h12)) : n1.int.G('0' <> _ <> c2
    <> rest, vv)
  Equal.trans(Bool, L1.n1.got.int(T.word.val('0' <> 'o' <> c2 <> rest), vv), Bool.and(T.i64.fits(T.Plus{},
    T.dec.text(n1.cv(D1.AOct{}, c2 <> rest, []))), n1.gi(vv, T.Plus{}, c2 <> rest, 8n)), Bool.and(Bool.and(
    D1.abnf.integer('0' <> 'o' <> c2 <> rest), D1.prose.int_in_range('0' <> 'o' <> c2 <> rest)),
    D1.g.val(D3.GvInteger{'0' <> 'o' <> c2 <> rest}, vv)), n1.px.v(uu, D1.AOct{}, 'o', c2 <> rest, vv, hb,
    {==}), Equal.trans(Bool, Bool.and(T.i64.fits(T.Plus{}, T.dec.text(n1.cv(D1.AOct{}, c2 <> rest, []))),
    n1.gi(vv, T.Plus{}, c2 <> rest, 8n)), Bool.and(D1.prose.radix_in_range(D1.AOct{}, '0' <> 'o' <> c2 <> rest),
    n1.gi(vv, T.Plus{}, c2 <> rest, 8n)), Bool.and(Bool.and(D1.abnf.integer('0' <> 'o' <> c2 <> rest),
    D1.prose.int_in_range('0' <> 'o' <> c2 <> rest)), D1.g.val(D3.GvInteger{'0' <> 'o' <> c2 <> rest}, vv)),
    Equal.cong(Bool, Bool, bb => Bool.and(bb, n1.gi(vv, T.Plus{}, c2 <> rest, 8n)), T.i64.fits(T.Plus{},
    T.dec.text(n1.cv(D1.AOct{}, c2 <> rest, []))), D1.prose.radix_in_range(D1.AOct{}, '0' <> 'o' <> c2 <>
    rest), n1.rng.o(uu, c2 <> rest, hb)), Equal.sym(Bool, Bool.and(Bool.and(D1.abnf.integer('0' <> 'o' <> c2 <>
    rest), D1.prose.int_in_range('0' <> 'o' <> c2 <> rest)), D1.g.val(D3.GvInteger{'0' <> 'o' <> c2 <> rest},
    vv)), Bool.and(D1.prose.radix_in_range(D1.AOct{}, '0' <> 'o' <> c2 <> rest), n1.gi(vv, T.Plus{}, c2 <> rest,
    8n)), n1.rhs.o(c2, rest, vv, hb))))

# a binary integer word, in base 2
def n1.px.b(
  +uu: Unit,
  +c0: Char,
  +c1: Char,
  +c2: Char,
  +rest: List<&2, Char>,
  +vv: T.Val,
  +hp: {D1.abnf.bin_int(c0 <> c1 <> c2 <> rest) == True{} : Bool}
) -> n1.int.G(c0 <> c1 <> c2 <> rest, vv):
  +h12 = {Eq.and.right(D1.abnf.cp(c0, 48), Bool.and(D1.abnf.cp(c1, 98), n1.bg(c2 <> rest, D1.ABin{})), hp)
    : {Bool.and(D1.abnf.cp(c1, 98), n1.bg(c2 <> rest, D1.ABin{})) == True{} : Bool}}
  +hb = {Eq.and.right(D1.abnf.cp(c1, 98), n1.bg(c2 <> rest, D1.ABin{}), h12) : {n1.bg(c2 <> rest, D1.ABin{})
    == True{} : Bool}}
  %n1.cpc(c0, 48, Eq.and.left(D1.abnf.cp(c0, 48), Bool.and(D1.abnf.cp(c1, 98), n1.bg(c2 <> rest, D1.ABin{})),
    hp)) : n1.int.G(_ <> c1 <> c2 <> rest, vv)
  %n1.cpc(c1, 98, Eq.and.left(D1.abnf.cp(c1, 98), n1.bg(c2 <> rest, D1.ABin{}), h12)) : n1.int.G('0' <> _ <> c2
    <> rest, vv)
  Equal.trans(Bool, L1.n1.got.int(T.word.val('0' <> 'b' <> c2 <> rest), vv), Bool.and(T.i64.fits(T.Plus{},
    T.dec.text(n1.cv(D1.ABin{}, c2 <> rest, []))), n1.gi(vv, T.Plus{}, c2 <> rest, 2n)), Bool.and(Bool.and(
    D1.abnf.integer('0' <> 'b' <> c2 <> rest), D1.prose.int_in_range('0' <> 'b' <> c2 <> rest)),
    D1.g.val(D3.GvInteger{'0' <> 'b' <> c2 <> rest}, vv)), n1.px.v(uu, D1.ABin{}, 'b', c2 <> rest, vv, hb,
    {==}), Equal.trans(Bool, Bool.and(T.i64.fits(T.Plus{}, T.dec.text(n1.cv(D1.ABin{}, c2 <> rest, []))),
    n1.gi(vv, T.Plus{}, c2 <> rest, 2n)), Bool.and(D1.prose.radix_in_range(D1.ABin{}, '0' <> 'b' <> c2 <> rest),
    n1.gi(vv, T.Plus{}, c2 <> rest, 2n)), Bool.and(Bool.and(D1.abnf.integer('0' <> 'b' <> c2 <> rest),
    D1.prose.int_in_range('0' <> 'b' <> c2 <> rest)), D1.g.val(D3.GvInteger{'0' <> 'b' <> c2 <> rest}, vv)),
    Equal.cong(Bool, Bool, bb => Bool.and(bb, n1.gi(vv, T.Plus{}, c2 <> rest, 2n)), T.i64.fits(T.Plus{},
    T.dec.text(n1.cv(D1.ABin{}, c2 <> rest, []))), D1.prose.radix_in_range(D1.ABin{}, '0' <> 'b' <> c2 <>
    rest), n1.rng.b(uu, c2 <> rest, hb)), Equal.sym(Bool, Bool.and(Bool.and(D1.abnf.integer('0' <> 'b' <> c2 <>
    rest), D1.prose.int_in_range('0' <> 'b' <> c2 <> rest)), D1.g.val(D3.GvInteger{'0' <> 'b' <> c2 <> rest},
    vv)), Bool.and(D1.prose.radix_in_range(D1.ABin{}, '0' <> 'b' <> c2 <> rest), n1.gi(vv, T.Plus{}, c2 <> rest,
    2n)), n1.rhs.b(c2, rest, vv, hb))))

# the code point of a radix's prefix letter: x, o or b
def n1.pc(rx: D1.ARadix) -> U32:
  match rx:
    case D1.AHex{}:
      120
    case D1.AOct{}:
      111
    case D1.ABin{}:
      98

# the law for a prefixed word of each radix
def n1.int.px.go(
  +uu: Unit,
  rx: D1.ARadix,
  +c0: Char,
  +c1: Char,
  +c2: Char,
  +rest: List<&2, Char>,
  +vv: T.Val,
  +hp: {D1.abnf.prefixed(c0 <> c1 <> c2 <> rest, n1.pc(rx), rx) == True{} : Bool}
) -> n1.int.G(c0 <> c1 <> c2 <> rest, vv):
  match rx:
    case D1.AHex{}:
      n1.px.x(uu, c0, c1, c2, rest, vv, hp)
    case D1.AOct{}:
      n1.px.o(uu, c0, c1, c2, rest, vv, hp)
    case D1.ABin{}:
      n1.px.b(uu, c0, c1, c2, rest, vv, hp)

# a prefixed word of the radix has a prefix and a first digit: the law for
# each radix, from its prefix rule
def n1.int.px(
  +uu: Unit,
  +rx: D1.ARadix,
  cs: List<&2, Char>,
  +vv: T.Val,
  +hp: {D1.abnf.prefixed(cs, n1.pc(rx), rx) == True{} : Bool}
) -> n1.int.G(cs, vv):
  match cs:
    case []:
      Eq.bit.absurd(&1, n1.int.G([], vv), hp)
    case +c0 <> t0:
      match t0:
        case []:
          Eq.bit.absurd(&1, n1.int.G([c0], vv), hp)
        case +c1 <> t1:
          match t1:
            case []:
              Eq.bit.absurd(&1, n1.int.G([c0, c1], vv), hp)
            case +c2 <> +rest:
              n1.int.px.go(uu, rx, c0, c1, c2, rest, vv, hp)

# what the dec-int's side of the law is, when no prefix rule matches
def n1.dec.rhs(
  +cs: List<&2, Char>,
  +vv: T.Val,
  +ex: {D1.abnf.hex_int(cs) == False{} : Bool},
  +eo: {D1.abnf.oct_int(cs) == False{} : Bool},
  +eb: {D1.abnf.bin_int(cs) == False{} : Bool},
  +ed: {D1.abnf.dec_int(cs) == True{} : Bool}
) -> {Bool.and(Bool.and(D1.abnf.integer(cs), D1.prose.int_in_range(cs)), D1.g.val(D3.GvInteger{cs}, vv))
  == Bool.and(T.i64.fits(D1.abnf.dec_sign(cs), D1.abnf.dec_digits(cs)), n1.gi(vv, D1.abnf.dec_sign(cs),
  String.to_list(D1.abnf.dec_digits(cs)), 10n)) : Bool}:
  %Equal.sym(Bool, D1.g.val(D3.GvInteger{cs}, vv), n1.gi(vv, D1.abnf.dec_sign(cs), D1.g.int.body(cs),
    D1.g.int.radix(cs)), n1.gv(vv, cs)) : {Bool.and(Bool.and(D1.abnf.integer(cs), D1.prose.int_in_range(cs)), _)
    == Bool.and(T.i64.fits(D1.abnf.dec_sign(cs), D1.abnf.dec_digits(cs)), n1.gi(vv, D1.abnf.dec_sign(cs),
    String.to_list(D1.abnf.dec_digits(cs)), 10n)) : Bool}
  %Equal.sym(Bool, D1.abnf.hex_int(cs), False{}, ex) : {Bool.and(Bool.and(Bool.or(D1.abnf.dec_int(cs), Bool.or(_,
    Bool.or(D1.abnf.oct_int(cs), D1.abnf.bin_int(cs)))), D1.prose.int_in_range.pick(_, D1.abnf.oct_int(cs),
    D1.abnf.bin_int(cs), cs)), n1.gi(vv, D1.abnf.dec_sign(cs), D1.g.int.body.pick(Bool.or(_,
    Bool.or(D1.abnf.oct_int(cs), D1.abnf.bin_int(cs))), cs), D1.g.int.radix.pick(_, D1.abnf.oct_int(cs),
    D1.abnf.bin_int(cs)))) == Bool.and(T.i64.fits(D1.abnf.dec_sign(cs), D1.abnf.dec_digits(cs)), n1.gi(vv,
    D1.abnf.dec_sign(cs), String.to_list(D1.abnf.dec_digits(cs)), 10n)) : Bool}
  %Equal.sym(Bool, D1.abnf.oct_int(cs), False{}, eo) : {Bool.and(Bool.and(Bool.or(D1.abnf.dec_int(cs),
    Bool.or(False{}, Bool.or(_, D1.abnf.bin_int(cs)))), D1.prose.int_in_range.pick(False{}, _,
    D1.abnf.bin_int(cs), cs)), n1.gi(vv, D1.abnf.dec_sign(cs), D1.g.int.body.pick(Bool.or(False{}, Bool.or(_,
    D1.abnf.bin_int(cs))), cs), D1.g.int.radix.pick(False{}, _, D1.abnf.bin_int(cs)))) == Bool.and(
    T.i64.fits(D1.abnf.dec_sign(cs), D1.abnf.dec_digits(cs)), n1.gi(vv, D1.abnf.dec_sign(cs),
    String.to_list(D1.abnf.dec_digits(cs)), 10n)) : Bool}
  %Equal.sym(Bool, D1.abnf.bin_int(cs), False{}, eb) : {Bool.and(Bool.and(Bool.or(D1.abnf.dec_int(cs),
    Bool.or(False{}, Bool.or(False{}, _))), D1.prose.int_in_range.pick(False{}, False{}, _, cs)), n1.gi(vv,
    D1.abnf.dec_sign(cs), D1.g.int.body.pick(Bool.or(False{}, Bool.or(False{}, _)), cs), D1.g.int.radix.pick(
    False{}, False{}, _))) == Bool.and(T.i64.fits(D1.abnf.dec_sign(cs), D1.abnf.dec_digits(cs)), n1.gi(vv,
    D1.abnf.dec_sign(cs), String.to_list(D1.abnf.dec_digits(cs)), 10n)) : Bool}
  %Equal.sym(Bool, D1.abnf.dec_int(cs), True{}, ed) : {Bool.and(Bool.and(Bool.or(_, False{}),
    D1.prose.dec_le(D1.abnf.dec_digits(cs), D1.prose.i64.limit(D1.abnf.dec_sign(cs)), EQ{})), n1.gi(vv,
    D1.abnf.dec_sign(cs), String.to_list(D1.abnf.dec_digits(cs)), 10n)) == Bool.and(T.i64.fits(
    D1.abnf.dec_sign(cs), D1.abnf.dec_digits(cs)), n1.gi(vv, D1.abnf.dec_sign(cs),
    String.to_list(D1.abnf.dec_digits(cs)), 10n)) : Bool}
  Equal.cong(Bool, Bool, bb => Bool.and(bb, n1.gi(vv, D1.abnf.dec_sign(cs), String.to_list(D1.abnf.dec_digits(cs)),
    10n)), D1.prose.dec_le(D1.abnf.dec_digits(cs), D1.prose.i64.limit(D1.abnf.dec_sign(cs)), EQ{}),
    T.i64.fits(D1.abnf.dec_sign(cs), D1.abnf.dec_digits(cs)), n1.dfit(D1.abnf.dec_sign(cs),
    D1.abnf.dec_digits(cs)))

# a dec-int word that no prefix rule matches
def n1.int.dec(
  +cs: List<&2, Char>,
  +vv: T.Val,
  +ex: {D1.abnf.hex_int(cs) == False{} : Bool},
  +eo: {D1.abnf.oct_int(cs) == False{} : Bool},
  +eb: {D1.abnf.bin_int(cs) == False{} : Bool},
  +ed: {D1.abnf.dec_int(cs) == True{} : Bool}
) -> n1.int.G(cs, vv):
  %Equal.sym(T.Got, T.word.val(cs), n1.dw.G(D1.abnf.dec_sign(cs), D1.abnf.dec_digits(cs)), n1.dw(cs, ed)) :
    {L1.n1.got.int(_, vv) == Bool.and(Bool.and(D1.abnf.integer(cs), D1.prose.int_in_range(cs)),
    D1.g.val(D3.GvInteger{cs}, vv)) : Bool}
  Equal.trans(Bool, L1.n1.got.int(n1.dw.G(D1.abnf.dec_sign(cs), D1.abnf.dec_digits(cs)), vv),
    Bool.and(T.i64.fits(D1.abnf.dec_sign(cs), D1.abnf.dec_digits(cs)), n1.gi(vv, D1.abnf.dec_sign(cs),
    String.to_list(D1.abnf.dec_digits(cs)), 10n)), Bool.and(Bool.and(D1.abnf.integer(cs),
    D1.prose.int_in_range(cs)), D1.g.val(D3.GvInteger{cs}, vv)), n1.core(T.i64.fits(D1.abnf.dec_sign(cs),
    D1.abnf.dec_digits(cs)), vv, D1.abnf.dec_sign(cs), D1.abnf.dec_digits(cs),
    String.to_list(D1.abnf.dec_digits(cs)), 10n, n1.dcan(cs, ed), {==}), Equal.sym(Bool, Bool.and(Bool.and(
    D1.abnf.integer(cs), D1.prose.int_in_range(cs)), D1.g.val(D3.GvInteger{cs}, vv)), Bool.and(T.i64.fits(
    D1.abnf.dec_sign(cs), D1.abnf.dec_digits(cs)), n1.gi(vv, D1.abnf.dec_sign(cs),
    String.to_list(D1.abnf.dec_digits(cs)), 10n)), n1.dec.rhs(cs, vv, ex, eo, eb, ed)))

# a word that matches none of the four integer forms
def n1.int.none(
  +cs: List<&2, Char>,
  +ex: {D1.abnf.hex_int(cs) == False{} : Bool},
  +eo: {D1.abnf.oct_int(cs) == False{} : Bool},
  +eb: {D1.abnf.bin_int(cs) == False{} : Bool},
  +ed: {D1.abnf.dec_int(cs) == False{} : Bool}
) -> {D1.abnf.integer(cs) == False{} : Bool}:
  %Equal.sym(Bool, D1.abnf.dec_int(cs), False{}, ed) : {Bool.or(_, Bool.or(D1.abnf.hex_int(cs),
    Bool.or(D1.abnf.oct_int(cs), D1.abnf.bin_int(cs)))) == False{} : Bool}
  %Equal.sym(Bool, D1.abnf.hex_int(cs), False{}, ex) : {Bool.or(False{}, Bool.or(_, Bool.or(D1.abnf.oct_int(cs),
    D1.abnf.bin_int(cs)))) == False{} : Bool}
  %Equal.sym(Bool, D1.abnf.oct_int(cs), False{}, eo) : {Bool.or(False{}, Bool.or(False{}, Bool.or(_,
    D1.abnf.bin_int(cs)))) == False{} : Bool}
  %Equal.sym(Bool, D1.abnf.bin_int(cs), False{}, eb) : {Bool.or(False{}, Bool.or(False{}, Bool.or(False{}, _)))
    == False{} : Bool}
  {==}

# the integer law, by which of the integer forms the word matches: a
# hexadecimal, octal or binary prefix first, as prose.int_in_range asks,
# then dec-int, or none
def n1.int.law(
  hx: Bool,
  ho: Bool,
  hb: Bool,
  hd: Bool,
  +uu: Unit,
  +cs: List<&2, Char>,
  +vv: T.Val,
  +ex: {D1.abnf.hex_int(cs) == hx : Bool},
  +eo: {D1.abnf.oct_int(cs) == ho : Bool},
  +eb: {D1.abnf.bin_int(cs) == hb : Bool},
  +ed: {D1.abnf.dec_int(cs) == hd : Bool}
) -> n1.int.G(cs, vv):
  match hx:
    case True{}:
      n1.int.px(uu, D1.AHex{}, cs, vv, ex)
    case False{}:
      match ho:
        case True{}:
          n1.int.px(uu, D1.AOct{}, cs, vv, eo)
        case False{}:
          match hb:
            case True{}:
              n1.int.px(uu, D1.ABin{}, cs, vv, eb)
            case False{}:
              match hd:
                case True{}:
                  n1.int.dec(cs, vv, ex, eo, eb, ed)
                case False{}:
                  n1.int.out(cs, vv, n1.int.none(cs, ex, eo, eb, ed))

def L1.integer_word_exact(cs, v):
  n1.int.law(D1.abnf.hex_int(cs), D1.abnf.oct_int(cs), D1.abnf.bin_int(cs), D1.abnf.dec_int(cs), Unit{}, cs, v,
    {==}, {==}, {==}, {==})
