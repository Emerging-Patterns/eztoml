# lemmas that numbers and signed words are never date-times
import Base
import ../../src/eq.bend as Eq
import ../../laws/defs/AbnfGrammar.bend as D1
import ./DigitsWrittenBack.bend as M1
import ./GrammarWordMatching.bend as M2

# whether the first character that is no DIGIT or underscore, if there is
# one, is no - and no : (%x2D is 45, %x3A is 58)
def gp.nd.pick(dc: Bool, +hh: Char, rest: Bool) -> Bool:
  match dc:
    case True{}:
      rest
    case False{}:
      Bool.not(Bool.or(D1.abnf.cp(hh, 45), D1.abnf.cp(hh, 58)))

# whether a word's first character that is no DIGIT or underscore is no -
# and no :
def gp.nd(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      True{}
    case +hh <> tt:
      gp.nd.pick(M2.gp.dc(hh), hh, gp.nd(tt))

# what is left after DIGITs of such a word is such a word, or no match
def gp.ndr(rr: D1.ARest) -> Bool:
  match rr:
    case D1.ALeft{cs}:
      gp.nd(cs)
    case D1.ANone{}:
      True{}

# its first character is no - and no :
def gp.nd.head(
  +hh: Char,
  +tt: List<&2, Char>,
  dd: Bool,
  +ed: {M2.gp.dc(hh) == dd : Bool},
  +h: {gp.nd(hh <> tt) == True{} : Bool}
) -> {Bool.or(D1.abnf.cp(hh, 45), D1.abnf.cp(hh, 58)) == False{} : Bool}:
  match dd:
    case True{}:
      M2.gp.dc.elim(zz => {Bool.or(D1.abnf.cp(zz, 45), D1.abnf.cp(zz, 58)) == False{} : Bool}, hh, ed,
        {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})
    case False{}:
      Eq.not.true(Bool.or(D1.abnf.cp(hh, 45), D1.abnf.cp(hh, 58)),
        Equal.trans(Bool, gp.nd.pick(False{}, hh, gp.nd(tt)), gp.nd.pick(M2.gp.dc(hh), hh, gp.nd(tt)), True{},
          Equal.cong(Bool, Bool, xx => gp.nd.pick(xx, hh, gp.nd(tt)), False{}, M2.gp.dc(hh),
            Equal.sym(Bool, M2.gp.dc(hh), False{}, ed)), h))

# a DIGIT taken keeps the rest such a word
def gp.ndr.digit.go(
  +hh: Char,
  +tt: List<&2, Char>,
  dd: Bool,
  +ed: {D1.abnf.DIGIT(hh) == dd : Bool},
  +h: {gp.nd(hh <> tt) == True{} : Bool}
) -> {gp.ndr(D1.abnf.keep(D1.abnf.DIGIT(hh), tt)) == True{} : Bool}:
  match dd:
    case True{}:
      %Equal.sym(Bool, D1.abnf.DIGIT(hh), True{}, ed) : {gp.ndr(D1.abnf.keep(_, tt)) == True{} : Bool}
      Equal.trans(Bool, gp.nd(tt), gp.nd.pick(M2.gp.dc(hh), hh, gp.nd(tt)), True{},
        Equal.cong(Bool, Bool, xx => gp.nd.pick(xx, hh, gp.nd(tt)), True{}, M2.gp.dc(hh),
          Equal.sym(Bool, M2.gp.dc(hh), True{}, M2.gp.dc.digit(hh, ed))), h)
    case False{}:
      %Equal.sym(Bool, D1.abnf.DIGIT(hh), False{}, ed) : {gp.ndr(D1.abnf.keep(_, tt)) == True{} : Bool}
      {==}

# DIGIT from the front keeps such a word such a word
def gp.ndr.digit(rr: D1.ARest, +h: {gp.ndr(rr) == True{} : Bool}) -> {gp.ndr(D1.abnf.digit_r(rr)) == True{} : Bool}:
  match rr:
    case D1.ALeft{cs}:
      match cs:
        case []:
          {==}
        case +hh <> +tt:
          gp.ndr.digit.go(hh, tt, D1.abnf.DIGIT(hh), {==}, h)
    case D1.ANone{}:
      {==}

# no - from the front of such a word
def gp.ndr.dash(
  rr: D1.ARest,
  +h: {gp.ndr(rr) == True{} : Bool}
) -> {D1.abnf.char_r(rr, 45) == D1.ANone{} : D1.ARest}:
  match rr:
    case D1.ALeft{cs}:
      match cs:
        case []:
          {==}
        case +hh <> +tt:
          %Equal.sym(Bool, D1.abnf.cp(hh, 45), False{}, Eq.or.false_left(D1.abnf.cp(hh, 45), D1.abnf.cp(hh, 58),
            gp.nd.head(hh, tt, M2.gp.dc(hh), {==}, h))) : {D1.abnf.keep(_, tt) == D1.ANone{} : D1.ARest}
          {==}
    case D1.ANone{}:
      {==}

# no : from the front of such a word
def gp.ndr.colon(
  rr: D1.ARest,
  +h: {gp.ndr(rr) == True{} : Bool}
) -> {D1.abnf.char_r(rr, 58) == D1.ANone{} : D1.ARest}:
  match rr:
    case D1.ALeft{cs}:
      match cs:
        case []:
          {==}
        case +hh <> +tt:
          %Equal.sym(Bool, D1.abnf.cp(hh, 58), False{}, Eq.or.false_right(D1.abnf.cp(hh, 45), D1.abnf.cp(hh, 58),
            gp.nd.head(hh, tt, M2.gp.dc(hh), {==}, h))) : {D1.abnf.keep(_, tt) == D1.ANone{} : D1.ARest}
          {==}
    case D1.ANone{}:
      {==}

# date-time, from what is left after a full-date's first four DIGITs (d4)
# and a partial-time's first two (d2) and the character after each
def gp.dt.g(d4: D1.ARest, d2: D1.ARest) -> Bool:
  +fd = D1.abnf.date_mday(D1.abnf.char_r(D1.abnf.date_month(d4), 45))
  Bool.or(D1.abnf.all_r(D1.abnf.full_time(D1.abnf.time_delim(fd))),
    Bool.or(D1.abnf.all_r(D1.abnf.partial_time(D1.abnf.time_delim(fd))), Bool.or(D1.abnf.all_r(fd),
      D1.abnf.all_r(D1.abnf.opt_secfrac(D1.abnf.time_second(D1.abnf.char_r(D1.abnf.time_minute(d2),
      58)))))))

# a word whose first character that is no DIGIT or underscore is no - and
# no : is no date-time: a full-date has a - after four DIGITs, and a
# partial-time a : after two
def gp.nd.dt(+cs: List<&2, Char>, +h: {gp.nd(cs) == True{} : Bool}) -> {D1.abnf.date_time(cs) == False{} : Bool}:
  +r2 = D1.abnf.digit_r(D1.abnf.digit_r(D1.ALeft{cs}))
  +n2 = gp.ndr.digit(D1.abnf.digit_r(D1.ALeft{cs}), gp.ndr.digit(D1.ALeft{cs}, h))
  +r4 = D1.abnf.digit_r(D1.abnf.digit_r(r2))
  Equal.trans(Bool, gp.dt.g(D1.abnf.char_r(r4, 45), D1.abnf.char_r(r2, 58)),
    gp.dt.g(D1.ANone{}, D1.abnf.char_r(r2, 58)), False{},
    Equal.cong(D1.ARest, Bool, xx => gp.dt.g(xx, D1.abnf.char_r(r2, 58)), D1.abnf.char_r(r4, 45), D1.ANone{},
      gp.ndr.dash(r4, gp.ndr.digit(D1.abnf.digit_r(r2), gp.ndr.digit(r2, n2)))),
    Equal.trans(Bool, gp.dt.g(D1.ANone{}, D1.abnf.char_r(r2, 58)), gp.dt.g(D1.ANone{}, D1.ANone{}), False{},
      Equal.cong(D1.ARest, Bool, xx => gp.dt.g(D1.ANone{}, xx), D1.abnf.char_r(r2, 58), D1.ANone{},
        gp.ndr.colon(r2, n2)),
      {==}))

# a word that starts with a sign is no date-time
def gp.dt.sign(
  +hh: Char,
  +tt: List<&2, Char>,
  +hs: {Bool.or(D1.abnf.minus(hh), D1.abnf.plus(hh)) == True{} : Bool}
) -> {D1.abnf.date_time(hh <> tt) == False{} : Bool}:
  M2.gp.or({D1.abnf.date_time(hh <> tt) == False{} : Bool}, D1.abnf.minus(hh), D1.abnf.plus(hh), hs,
    hm => M2.gp.head(zs => {D1.abnf.date_time(zs) == False{} : Bool}, hh, '-', tt, M1.gs.minus(hh, hm), {==}),
    hp => M2.gp.head(zs => {D1.abnf.date_time(zs) == False{} : Bool}, hh, '+', tt, M1.gs.plus(hh, hp), {==}))
