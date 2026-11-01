# digits are never delimiters, colons or dashes of a bare value
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/IntegerReadExactly.bend as L1
import ../../laws/WordReadsBack.bend as L2
import ../../laws/defs/BareValueGrammar.bend as D1
import ./DigitsWrittenBack.bend as M1
import ./FreshNamesInRows.bend as M2
import ./PrefixAndTake.bend as M3
import ./ShortTextBounds.bend as M4

# a digit in front of such digits keeps them such digits
def nzl.cons(
  +cc: Char,
  +acc: List<&2, Char>,
  hc: {Char.is_digit(cc) == True{} : Bool},
  hn: {M1.nzl(acc) == True{} : Bool}
) -> {M1.nzl(cc <> acc) == True{} : Bool}:
  M3.and.tt(Char.is_digit(cc), Bool.or(M1.nzl(acc), Bool.and(List.is_empty(&2, Char, acc),
    Bool.not(Char.is_eq(cc, '0')))), hc,
    Equal.cong(Bool, Bool, bb => Bool.or(bb, Bool.and(List.is_empty(&2, Char, acc), Bool.not(Char.is_eq(cc, '0')))),
      M1.nzl(acc), True{}, hn))

# the digits after the first, one at a time
def nw(
  tt: String,
  +acc: List<&2, Char>,
  +sg: T.Sign,
  +ht: {T.wf.digits(tt) == True{} : Bool},
  +hn: {M1.nzl(acc) == True{} : Bool}
) -> {T.num.go(String.to_list(tt), M1.ndig(sg, M1.vals(acc))) == M1.ndig(sg, M1.vals(M2.rev.onto(tt, acc))) : T.Num}:
  match tt:
    case SNil{}:
      {==}
    case SCon{+cc, +ts}:
      +hc = {M2.then.l(Char.is_digit(cc), ts, ht) : {Char.is_digit(cc) == True{} : Bool}}
      Equal.trans(T.Num, T.num.go(String.to_list(ts), T.num.step(M1.ndig(sg, M1.vals(acc)), cc)),
        T.num.go(String.to_list(ts), M1.ndig(sg, M1.vals(cc <> acc))), M1.ndig(sg, M1.vals(M2.rev.onto(ts, cc <> acc))),
        Equal.cong(T.Num, T.Num, nn => T.num.go(String.to_list(ts), nn), T.num.step(M1.ndig(sg, M1.vals(acc)), cc),
          M1.ndig(sg, M1.vals(cc <> acc)),
          Equal.trans(T.Num, T.num.step(M1.ndig(sg, M1.vals(acc)), cc), M1.ndig(sg, T.dec.go(M1.vals(acc), 10,
              T.dig.val(cc))),
            M1.ndig(sg, M1.vals(cc <> acc)), M1.nw.step(sg, M1.vals(acc), cc, hc),
            Equal.cong(List<&2, U32>, T.Num, ds => M1.ndig(sg, ds), T.dec.go(M1.vals(acc), 10, T.dig.val(cc)),
              M1.vals(cc <> acc), M1.dgo(acc, cc, hc, hn)))),
        nw(ts, cc <> acc, sg, M2.then.r(Char.is_digit(cc), ts, ht), nzl.cons(cc, acc, hc, hn)))

# a digit is no character that starts or ends a word differently
def dg.first(
  cc: Char,
  hc: {Char.is_digit(cc) == True{} : Bool}
) -> {D1.word.first(cc) == True{} : Bool}:
  M2.dg.elim(zz => {D1.word.first(zz) == True{} : Bool}, cc, hc,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# a digit is a character a bare value keeps
def dg.char(
  cc: Char,
  hc: {Char.is_digit(cc) == True{} : Bool}
) -> {D1.word.char(cc) == True{} : Bool}:
  M2.dg.elim(zz => {D1.word.char(zz) == True{} : Bool}, cc, hc,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# digits are characters a bare value keeps
def dg.rest(
  tt: String,
  +ht: {T.wf.digits(tt) == True{} : Bool}
) -> {L2.word.rest(tt) == True{} : Bool}:
  match tt:
    case SNil{}:
      {==}
    case SCon{+cc, +ts}:
      M3.and.tt(D1.word.char(cc), L2.word.rest(ts), dg.char(cc, M2.then.l(Char.is_digit(cc), ts, ht)),
        dg.rest(ts, M2.then.r(Char.is_digit(cc), ts, ht)))

# a digit starts no special word
def dg.nospec(
  cc: Char,
  hc: {Char.is_digit(cc) == True{} : Bool}
) -> {T.word.special(cc) == False{} : Bool}:
  M2.dg.elim(zz => {T.word.special(zz) == False{} : Bool}, cc, hc,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# a digit is no colon
def dg.nocolon(
  cc: Char,
  hc: {Char.is_digit(cc) == True{} : Bool}
) -> {Char.is_eq(cc, ':') == False{} : Bool}:
  M2.dg.elim(zz => {Char.is_eq(zz, ':') == False{} : Bool}, cc, hc,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# a digit is no dash
def dg.nodash(
  cc: Char,
  hc: {Char.is_digit(cc) == True{} : Bool}
) -> {Char.is_eq(cc, '-') == False{} : Bool}:
  M2.dg.elim(zz => {Char.is_eq(zz, '-') == False{} : Bool}, cc, hc,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# a digit is no i
def dg.noi(
  cc: Char,
  hc: {Char.is_digit(cc) == True{} : Bool}
) -> {False{} == Char.is_eq(cc, 'i') : Bool}:
  M2.dg.elim(zz => {False{} == Char.is_eq(zz, 'i') : Bool}, cc, hc,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# a digit is no n
def dg.non(
  cc: Char,
  hc: {Char.is_digit(cc) == True{} : Bool}
) -> {False{} == Char.is_eq(cc, 'n') : Bool}:
  M2.dg.elim(zz => {False{} == Char.is_eq(zz, 'n') : Bool}, cc, hc,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# a digit after the first character is no dash, and the first is never
# counted
def dash.hit.f(
  ff: Bool,
  cc: Char,
  hc: {Char.is_digit(cc) == True{} : Bool}
) -> {T.word.dash.hit(ff, cc) == False{} : Bool}:
  match ff:
    case True{}:
      {==}
    case False{}:
      dg.nodash(cc, hc)

# digits hold no colon
def dg.colon(
  tt: String,
  +ht: {T.wf.digits(tt) == True{} : Bool}
) -> {T.word.colon(String.to_list(tt)) == False{} : Bool}:
  match tt:
    case SNil{}:
      {==}
    case SCon{+cc, +ts}:
      Equal.trans(Bool, T.word.or(Char.is_eq(cc, ':'), T.word.colon(String.to_list(ts))),
        T.word.or(False{}, T.word.colon(String.to_list(ts))), False{},
        Equal.cong(Bool, Bool, bb => T.word.or(bb, T.word.colon(String.to_list(ts))), Char.is_eq(cc, ':'), False{},
          dg.nocolon(cc, M2.then.l(Char.is_digit(cc), ts, ht))),
        dg.colon(ts, M2.then.r(Char.is_digit(cc), ts, ht)))

# digits hold no dash after the first character
def dg.dash(
  tt: String,
  +ff: Bool,
  +ht: {T.wf.digits(tt) == True{} : Bool}
) -> {T.word.dash(String.to_list(tt), ff) == False{} : Bool}:
  match tt:
    case SNil{}:
      {==}
    case SCon{+cc, +ts}:
      Equal.trans(Bool, T.word.or(T.word.dash.hit(ff, cc), T.word.dash(String.to_list(ts), False{})),
        T.word.or(False{}, T.word.dash(String.to_list(ts), False{})), False{},
        Equal.cong(Bool, Bool, bb => T.word.or(bb, T.word.dash(String.to_list(ts), False{})),
          T.word.dash.hit(ff, cc), False{}, dash.hit.f(ff, cc, M2.then.l(Char.is_digit(cc), ts, ht))),
        dg.dash(ts, False{}, M2.then.r(Char.is_digit(cc), ts, ht)))

# a word that is neither a datetime by its colons and dashes nor an exponent
# numeral goes to the numeral scan
def asd.f(ee: Bool) -> {T.word.as_date(False{}, ee) == False{} : Bool}:
  match ee:
    case True{}:
      {==}
    case False{}:
      {==}

# a word with no colon and no dash after its first character, special or
# not, is a numeral
def route.num(
  +cs: List<&2, Char>,
  hc: {T.word.colon(cs) == False{} : Bool},
  hd: {T.word.dash(cs, True{}) == False{} : Bool}
) -> {T.word.route(T.GotBad{""}, T.word.or(T.word.colon(cs), T.word.dash(cs, True{})), cs) == T.word.num(cs) : T.Got}:
  %Equal.sym(Bool, T.word.colon(cs), False{}, hc) :
    {T.word.route(T.GotBad{""}, T.word.or(_, T.word.dash(cs, True{})), cs) == T.word.num(cs) : T.Got}
  %Equal.sym(Bool, T.word.dash(cs, True{}), False{}, hd) :
    {T.word.route(T.GotBad{""}, T.word.or(False{}, _), cs) == T.word.num(cs) : T.Got}
  %Equal.sym(Bool, T.word.as_date(False{}, T.word.ee(cs)), False{}, asd.f(T.word.ee(cs))) :
    {T.word.route.date(_, cs) == T.word.num(cs) : T.Got}
  {==}

# a word that starts with a minus and a digit is no special: it differs from
# -inf and -nan at the digit, and from the others at the minus
def spec.m(
  +hh: Char,
  +rest: List<&2, Char>,
  ei: {False{} == Char.is_eq(hh, 'i') : Bool},
  en: {False{} == Char.is_eq(hh, 'n') : Bool}
) -> {T.word.spec(String.from_list('-' <> hh <> rest)) == T.GotBad{""} : T.Got}:
  Equal.trans(T.Got,
    T.word.spec.inf3(T.str.eq.step(String.from_list(rest), "nf", Char.is_eq(hh, 'i')),
      String.from_list('-' <> hh <> rest)),
    T.word.spec.inf3(False{}, String.from_list('-' <> hh <> rest)),
    T.GotBad{""},
    Equal.cong(Bool, T.Got, bb => T.word.spec.inf3(bb, String.from_list('-' <> hh <> rest)),
      T.str.eq.step(String.from_list(rest), "nf", Char.is_eq(hh, 'i')), False{},
      M4.str.eq.off2(String.from_list(rest), "nf", Char.is_eq(hh, 'i'), ei)),
    Equal.cong(Bool, T.Got, bb => T.word.spec.nan3(bb),
      T.str.eq.step(String.from_list(rest), "an", Char.is_eq(hh, 'n')), False{},
      M4.str.eq.off2(String.from_list(rest), "an", Char.is_eq(hh, 'n'), en)))

# a digit and digits are digits
def dgs.cons(
  +hh: Char,
  +tt: String,
  hx: {Char.is_digit(hh) == True{} : Bool},
  ht: {T.wf.digits(tt) == True{} : Bool}
) -> {T.wf.digits(SCon{hh, tt}) == True{} : Bool}:
  Equal.trans(Bool, T.wf.then(Char.is_digit(hh), _u => T.wf.digits(tt)),
    T.wf.then(True{}, _u => T.wf.digits(tt)), True{},
    Equal.cong(Bool, Bool, bb => T.wf.then(bb, _u => T.wf.digits(tt)), Char.is_digit(hh), True{}, hx), ht)

# a first digit that is not 0 starts such digits
def nzl.one(
  +hh: Char,
  hx: {Char.is_digit(hh) == True{} : Bool},
  hz: {Char.is_eq(hh, '0') == False{} : Bool}
) -> {M1.nzl([hh]) == True{} : Bool}:
  M3.and.tt(Char.is_digit(hh), Bool.or(False{}, Bool.and(True{}, Bool.not(Char.is_eq(hh, '0')))), hx,
    Equal.cong(Bool, Bool, bb => Bool.or(False{}, Bool.and(True{}, Bool.not(bb))), Char.is_eq(hh, '0'), False{},
      hz))

# the numeral scan over the digits of an integer, from the first one on
def int.scan(
  +sg: T.Sign,
  st0: T.Num,
  +hh: Char,
  +tt: String,
  e0: {T.num.step(st0, hh) == M1.ndig(sg, M1.vals([hh])) : T.Num},
  +hx: {Char.is_digit(hh) == True{} : Bool},
  +hz: {Char.is_eq(hh, '0') == False{} : Bool},
  +ht: {T.wf.digits(tt) == True{} : Bool}
) -> {T.num.go(String.to_list(tt), T.num.step(st0, hh)) == M1.ndig(sg, M1.vals(M2.rev.onto(tt, [hh]))) : T.Num}:
  Equal.trans(T.Num, T.num.go(String.to_list(tt), T.num.step(st0, hh)),
    T.num.go(String.to_list(tt), M1.ndig(sg, M1.vals([hh]))), M1.ndig(sg, M1.vals(M2.rev.onto(tt, [hh]))),
    Equal.cong(T.Num, T.Num, nn => T.num.go(String.to_list(tt), nn), T.num.step(st0, hh), M1.ndig(sg, M1.vals([hh])),
        e0),
    nw(tt, [hh], sg, ht, nzl.one(hh, hx, hz)))

# what int_word claims
def int.Goal(+sg: T.Sign, +ds: String) -> Type:
  {T.word.val(String.to_list(T.render.atom(T.VInt{sg, ds}))) == T.GotVal{T.VInt{sg, ds}} : T.Got}

# a positive integer whose first digit is not 0: no special, no datetime, and
# the numeral scan reads its digits
def int.plus(
  +hh: Char,
  +tt: String,
  +hx: {Char.is_digit(hh) == True{} : Bool},
  +hz: {Char.is_eq(hh, '0') == False{} : Bool},
  +ht: {T.wf.digits(tt) == True{} : Bool},
  +hf: {T.i64.fits(T.Plus{}, SCon{hh, tt}) == True{} : Bool}
) -> int.Goal(T.Plus{}, SCon{hh, tt}):
  +hd = {dgs.cons(hh, tt, hx, ht) : {T.wf.digits(SCon{hh, tt}) == True{} : Bool}}
  Equal.trans(T.Got, T.word.val.pick(T.word.special(hh), hh <> String.to_list(tt)),
    T.word.val.pick(False{}, hh <> String.to_list(tt)), T.GotVal{T.VInt{T.Plus{}, SCon{hh, tt}}},
    Equal.cong(Bool, T.Got, bb => T.word.val.pick(bb, hh <> String.to_list(tt)), T.word.special(hh), False{},
      dg.nospec(hh, hx)),
    Equal.trans(T.Got, T.word.route(T.GotBad{""}, T.word.or(T.word.colon(hh <> String.to_list(tt)),
      T.word.dash(hh <> String.to_list(tt), True{})), hh <> String.to_list(tt)),
      T.word.num(hh <> String.to_list(tt)), T.GotVal{T.VInt{T.Plus{}, SCon{hh, tt}}},
      route.num(hh <> String.to_list(tt), dg.colon(SCon{hh, tt}, hd), dg.dash(SCon{hh, tt}, True{}, hd)),
      Equal.trans(T.Got, T.num.fin(T.num.go(String.to_list(tt), T.num.step(T.num.start(), hh)),
        hh <> String.to_list(tt)),
        T.num.fin(M1.ndig(T.Plus{}, M1.vals(M2.rev.onto(tt, [hh]))), hh <> String.to_list(tt)),
        T.GotVal{T.VInt{T.Plus{}, SCon{hh, tt}}},
        Equal.cong(T.Num, T.Got, nn => T.num.fin(nn, hh <> String.to_list(tt)),
          T.num.go(String.to_list(tt), T.num.step(T.num.start(), hh)), M1.ndig(T.Plus{}, M1.vals(M2.rev.onto(tt,
              [hh]))),
          int.scan(T.Plus{}, T.num.start(), hh, tt, M1.nw.lead(T.Plus{}, hh, hx, hz), hx, hz, ht)),
        M1.int.fin(T.Plus{}, hh, tt, hx, hz, ht, hf, hh <> String.to_list(tt)))))

# a negative integer whose first digit is not 0: the minus makes it a
# special candidate, which it is not, and then it reads as a positive one
# does, from the state after the sign
def int.minus(
  +hh: Char,
  +tt: String,
  +hx: {Char.is_digit(hh) == True{} : Bool},
  +hz: {Char.is_eq(hh, '0') == False{} : Bool},
  +ht: {T.wf.digits(tt) == True{} : Bool},
  +hf: {T.i64.fits(T.Minus{}, SCon{hh, tt}) == True{} : Bool}
) -> int.Goal(T.Minus{}, SCon{hh, tt}):
  +hd = {dgs.cons(hh, tt, hx, ht) : {T.wf.digits(SCon{hh, tt}) == True{} : Bool}}
  Equal.trans(T.Got, T.word.route(T.word.spec(String.from_list('-' <> hh <> String.to_list(tt))),
    T.word.or(T.word.colon('-' <> hh <> String.to_list(tt)), T.word.dash('-' <> hh <> String.to_list(tt),
    True{})), '-' <> hh <> String.to_list(tt)),
    T.word.route(T.GotBad{""}, T.word.or(T.word.colon('-' <> hh <> String.to_list(tt)),
      T.word.dash('-' <> hh <> String.to_list(tt), True{})), '-' <> hh <> String.to_list(tt)),
    T.GotVal{T.VInt{T.Minus{}, SCon{hh, tt}}},
    Equal.cong(T.Got, T.Got, gg => T.word.route(gg, T.word.or(T.word.colon('-' <> hh <> String.to_list(tt)),
      T.word.dash('-' <> hh <> String.to_list(tt), True{})), '-' <> hh <> String.to_list(tt)),
      T.word.spec(String.from_list('-' <> hh <> String.to_list(tt))), T.GotBad{""},
      spec.m(hh, String.to_list(tt), dg.noi(hh, hx), dg.non(hh, hx))),
    Equal.trans(T.Got, T.word.route(T.GotBad{""}, T.word.or(T.word.colon('-' <> hh <> String.to_list(tt)),
      T.word.dash('-' <> hh <> String.to_list(tt), True{})), '-' <> hh <> String.to_list(tt)),
      T.word.num('-' <> hh <> String.to_list(tt)), T.GotVal{T.VInt{T.Minus{}, SCon{hh, tt}}},
      route.num('-' <> hh <> String.to_list(tt), dg.colon(SCon{hh, tt}, hd), dg.dash(SCon{hh, tt}, False{}, hd)),
      Equal.trans(T.Got, T.num.fin(T.num.go(String.to_list(tt), T.num.step(T.Num{T.NSign{}, T.Minus{}, 10, [],
        False{}, False{}, ""}, hh)), '-' <> hh <> String.to_list(tt)),
        T.num.fin(M1.ndig(T.Minus{}, M1.vals(M2.rev.onto(tt, [hh]))), '-' <> hh <> String.to_list(tt)),
        T.GotVal{T.VInt{T.Minus{}, SCon{hh, tt}}},
        Equal.cong(T.Num, T.Got, nn => T.num.fin(nn, '-' <> hh <> String.to_list(tt)),
          T.num.go(String.to_list(tt), T.num.step(T.Num{T.NSign{}, T.Minus{}, 10, [], False{}, False{}, ""}, hh)),
          M1.ndig(T.Minus{}, M1.vals(M2.rev.onto(tt, [hh]))),
          int.scan(T.Minus{}, T.Num{T.NSign{}, T.Minus{}, 10, [], False{}, False{}, ""}, hh, tt,
            M1.nw.sign(T.Minus{}, hh, hx, hz), hx, hz, ht)),
        M1.int.fin(T.Minus{}, hh, tt, hx, hz, ht, hf, '-' <> hh <> String.to_list(tt)))))

# a first digit that is not 0, by the sign
def int.nz(
  +sg: T.Sign,
  +hh: Char,
  +tt: String,
  +hx: {Char.is_digit(hh) == True{} : Bool},
  +hz: {Char.is_eq(hh, '0') == False{} : Bool},
  +ht: {T.wf.digits(tt) == True{} : Bool},
  +hf: {T.i64.fits(sg, SCon{hh, tt}) == True{} : Bool}
) -> int.Goal(sg, SCon{hh, tt}):
  match sg:
    case T.Plus{}:
      int.plus(hh, tt, hx, hz, ht, hf)
    case T.Minus{}:
      int.minus(hh, tt, hx, hz, ht, hf)

# a lone 0, with either sign
def int.zero(
  tt: String,
  +sg: T.Sign,
  hd: {String.is_empty(tt) == True{} : Bool}
) -> int.Goal(sg, SCon{'0', tt}):
  match tt:
    case SNil{}:
      match sg:
        case T.Plus{}:
          {==}
        case T.Minus{}:
          {==}
    case SCon{ch, ct}:
      Eq.bit.absurd(&1, int.Goal(sg, SCon{'0', SCon{ch, ct}}), hd)

# a well-formed integer, by its first digit: a lone 0, with either sign, is a
# fixed text; any other first digit starts the numeral
def int.lead(
  +hh: Char,
  zz: Bool,
  ez: {Char.is_eq(hh, '0') == zz : Bool},
  +tt: String,
  +sg: T.Sign,
  +hd: {T.wf.dec.lead(zz, hh, tt) == True{} : Bool},
  +hf: {T.i64.fits(sg, SCon{hh, tt}) == True{} : Bool}
) -> int.Goal(sg, SCon{hh, tt}):
  match zz:
    case True{}:
      %Equal.sym(Char, hh, '0', Eq.char_eq_true(hh, '0', ez)) : int.Goal(sg, SCon{_, tt})
      int.zero(tt, sg, hd)
    case False{}:
      int.nz(sg, hh, tt, Eq.and.left(Char.is_digit(hh), T.wf.digits(tt), hd), ez,
        Eq.and.right(Char.is_digit(hh), T.wf.digits(tt), hd), hf)

def L1.int_word(sg, ds, w):
  match ds:
    case SNil{}:
      Eq.bit.absurd(&1, int.Goal(sg, SNil{}), w)
    case SCon{+hh, +tt}:
      int.lead(hh, Char.is_eq(hh, '0'), {==}, tt, sg, Eq.and.left(T.wf.dec(SCon{hh, tt}),
        T.i64.fits(sg, SCon{hh, tt}), w), Eq.and.right(T.wf.dec(SCon{hh, tt}), T.i64.fits(sg, SCon{hh, tt}), w))

# what int.chars claims
def int.Chars(+sg: T.Sign, +ds: String) -> Type:
  {L2.word.chars(T.render.atom(T.VInt{sg, ds})) == True{} : Bool}

# the digits of an integer whose first digit is not 0 are a bare value, by
# the sign
def int.chars.nz(
  +sg: T.Sign,
  +hh: Char,
  +tt: String,
  +hx: {Char.is_digit(hh) == True{} : Bool},
  +ht: {T.wf.digits(tt) == True{} : Bool}
) -> int.Chars(sg, SCon{hh, tt}):
  match sg:
    case T.Plus{}:
      M3.and.tt(D1.word.first(hh), L2.word.rest(tt), dg.first(hh, hx), dg.rest(tt, ht))
    case T.Minus{}:
      M3.and.tt(D1.word.first('-'), L2.word.rest(SCon{hh, tt}), {==},
        dg.rest(SCon{hh, tt}, dgs.cons(hh, tt, hx, ht)))

# a lone 0 is a bare value, with either sign
def int.chars.zero(
  tt: String,
  +sg: T.Sign,
  hd: {String.is_empty(tt) == True{} : Bool}
) -> int.Chars(sg, SCon{'0', tt}):
  match tt:
    case SNil{}:
      match sg:
        case T.Plus{}:
          {==}
        case T.Minus{}:
          {==}
    case SCon{ch, ct}:
      Eq.bit.absurd(&1, int.Chars(sg, SCon{'0', SCon{ch, ct}}), hd)

# a well-formed integer's text is a bare value, by its first digit
def int.chars.lead(
  +hh: Char,
  zz: Bool,
  ez: {Char.is_eq(hh, '0') == zz : Bool},
  +tt: String,
  +sg: T.Sign,
  +hd: {T.wf.dec.lead(zz, hh, tt) == True{} : Bool}
) -> int.Chars(sg, SCon{hh, tt}):
  match zz:
    case True{}:
      %Equal.sym(Char, hh, '0', Eq.char_eq_true(hh, '0', ez)) : int.Chars(sg, SCon{_, tt})
      int.chars.zero(tt, sg, hd)
    case False{}:
      int.chars.nz(sg, hh, tt, Eq.and.left(Char.is_digit(hh), T.wf.digits(tt), hd),
        Eq.and.right(Char.is_digit(hh), T.wf.digits(tt), hd))

# a well-formed integer's text is a bare value
def int.chars(
  +sg: T.Sign,
  ds: String,
  hd: {T.wf.dec(ds) == True{} : Bool}
) -> int.Chars(sg, ds):
  match ds:
    case SNil{}:
      Eq.bit.absurd(&1, int.Chars(sg, SNil{}), hd)
    case SCon{+hh, +tt}:
      int.chars.lead(hh, Char.is_eq(hh, '0'), {==}, tt, sg, hd)
