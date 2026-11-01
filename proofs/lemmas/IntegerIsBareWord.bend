# an integer is a bare word, with its digit and radix tests
import Base
import ../../src/eq.bend as Eq
import ../../laws/IntegerReadExactly.bend as L1
import ../../laws/defs/AbnfGrammar.bend as D1
import ../../laws/defs/BareValueGrammar.bend as D2
import ./BareValueCharTests.bend as M1
import ./BooleanIsBareWord.bend as M2
import ./GrammarWordMatching.bend as M3
import ./PrefixAndTake.bend as M4

# and an underscore
def vl.q.us(cc: Char, hh: {D1.abnf.underscore(cc) == True{} : Bool}) -> {D2.word.first(cc) == True{} : Bool}:
  match cc:
    case Chr{+xx}:
      M1.vl.fq(~(ch => D1.abnf.underscore(ch)), xx, hh, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==},
          {==},
        {==})

# a digit of radix bin
def vl.q.bin(
  cc: Char,
  hh: {D1.abnf.radix_digit(D1.ABin{}, cc) == True{} : Bool}
) -> {D2.word.first(cc) == True{} : Bool}:
  match cc:
    case Chr{+xx}:
      M1.vl.fq(~(ch => D1.abnf.radix_digit(D1.ABin{}, ch)), xx, hh, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==},
        {==}, {==},
        {==}, {==})

# a digit of radix oct
def vl.q.oct(
  cc: Char,
  hh: {D1.abnf.radix_digit(D1.AOct{}, cc) == True{} : Bool}
) -> {D2.word.first(cc) == True{} : Bool}:
  match cc:
    case Chr{+xx}:
      M1.vl.fq(~(ch => D1.abnf.radix_digit(D1.AOct{}, ch)), xx, hh, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==},
        {==}, {==},
        {==}, {==})

# a digit of radix hex
def vl.q.hex(
  cc: Char,
  hh: {D1.abnf.radix_digit(D1.AHex{}, cc) == True{} : Bool}
) -> {D2.word.first(cc) == True{} : Bool}:
  match cc:
    case Chr{+xx}:
      M1.vl.fq(~(ch => D1.abnf.radix_digit(D1.AHex{}, ch)), xx, hh, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==},
        {==}, {==},
        {==}, {==})

# and a digit of every radix
def vl.q.rd(
  rx: D1.ARadix,
  cc: Char,
  hh: {D1.abnf.radix_digit(rx, cc) == True{} : Bool}
) -> {D2.word.first(cc) == True{} : Bool}:
  match rx:
    case D1.AHex{}:
      vl.q.hex(cc, hh)
    case D1.AOct{}:
      vl.q.oct(cc, hh)
    case D1.ABin{}:
      vl.q.bin(cc, hh)

# so do a prefixed integer's digits and underscores
def vl.qs.rrep(
  cs: List<&2, Char>,
  +rx: D1.ARadix,
  +hh: {D1.abnf.radix_rep(cs, rx) == True{} : Bool}
) -> {M2.vl.qs(cs) == True{} : Bool}:
  match cs:
    case []:
      {==}
    case +xx <> tt:
      match tt:
        case []:
          M4.and.tt(D2.word.first(xx), True{}, vl.q.rd(rx, xx, hh), {==})
        case +x2 <> +t2:
          M3.gp.or({M2.vl.qs(xx <> x2 <> t2) == True{} : Bool}, Bool.and(D1.abnf.radix_digit(rx, xx),
            D1.abnf.radix_rep(x2 <> t2, rx)), Bool.and(D1.abnf.underscore(xx), Bool.and(D1.abnf.radix_digit(rx,
            x2), D1.abnf.radix_rep(t2, rx))), hh,
            +ha => M4.and.tt(D2.word.first(xx), M2.vl.qs(x2 <> t2), vl.q.rd(rx, xx, Eq.and.left(D1.abnf.radix_digit(rx,
              xx), D1.abnf.radix_rep(x2 <> t2, rx), ha)), vl.qs.rrep(x2 <> t2, rx,
              Eq.and.right(D1.abnf.radix_digit(rx, xx), D1.abnf.radix_rep(x2 <> t2, rx), ha))),
            +hb => M4.and.tt(D2.word.first(xx), M2.vl.qs(x2 <> t2), vl.q.us(xx, Eq.and.left(D1.abnf.underscore(xx),
              Bool.and(D1.abnf.radix_digit(rx, x2), D1.abnf.radix_rep(t2, rx)), hb)), M4.and.tt(D2.word.first(x2),
              M2.vl.qs(t2), vl.q.rd(rx, x2, Eq.and.left(D1.abnf.radix_digit(rx, x2), D1.abnf.radix_rep(t2, rx),
              Eq.and.right(D1.abnf.underscore(xx), Bool.and(D1.abnf.radix_digit(rx, x2), D1.abnf.radix_rep(t2,
              rx)), hb))), vl.qs.rrep(t2, rx, Eq.and.right(D1.abnf.radix_digit(rx, x2), D1.abnf.radix_rep(t2, rx),
              Eq.and.right(D1.abnf.underscore(xx), Bool.and(D1.abnf.radix_digit(rx, x2), D1.abnf.radix_rep(t2,
              rx)), hb))))))

# and a prefixed integer's prefix, whose letter starts a bare value
def vl.qs.pre(
  cs: List<&2, Char>,
  +ll: U32,
  +rx: D1.ARadix,
  hl: {D2.word.first(Chr{ll}) == True{} : Bool},
  +hh: {D1.abnf.prefixed(cs, ll, rx) == True{} : Bool}
) -> {M2.vl.qs(cs) == True{} : Bool}:
  match cs:
    case []:
      Eq.bit.absurd(&2, {M2.vl.qs([]) == True{} : Bool}, hh)
    case +c0 <> t0:
      match t0:
        case []:
          Eq.bit.absurd(&2, {M2.vl.qs([c0]) == True{} : Bool}, hh)
        case +c1 <> t1:
          match t1:
            case []:
              Eq.bit.absurd(&2, {M2.vl.qs([c0, c1]) == True{} : Bool}, hh)
            case +c2 <> +rest:
              +h1 = {Eq.and.right(D1.abnf.cp(c0, 48), Bool.and(D1.abnf.cp(c1, ll), Bool.and(
                D1.abnf.radix_digit(rx, c2), D1.abnf.radix_rep(rest, rx))), hh) : {Bool.and(D1.abnf.cp(c1, ll),
                Bool.and(D1.abnf.radix_digit(rx, c2), D1.abnf.radix_rep(rest, rx))) == True{} : Bool}}
              +h2 = {Eq.and.right(D1.abnf.cp(c1, ll), Bool.and(D1.abnf.radix_digit(rx, c2),
                D1.abnf.radix_rep(rest, rx)), h1) : {Bool.and(D1.abnf.radix_digit(rx, c2), D1.abnf.radix_rep(rest,
                rx)) == True{} : Bool}}
              M4.and.tt(D2.word.first(c0), M2.vl.qs(c1 <> c2 <> rest), M1.vl.q.cp(c0, 48, Eq.and.left(D1.abnf.cp(c0,
                  48),
                Bool.and(D1.abnf.cp(c1, ll), Bool.and(D1.abnf.radix_digit(rx, c2), D1.abnf.radix_rep(rest, rx))),
                hh), {==}), M4.and.tt(D2.word.first(c1), M2.vl.qs(c2 <> rest), M1.vl.q.cp(c1, ll, Eq.and.left(
                D1.abnf.cp(c1, ll), Bool.and(D1.abnf.radix_digit(rx, c2), D1.abnf.radix_rep(rest, rx)), h1), hl),
                M4.and.tt(D2.word.first(c2), M2.vl.qs(rest), vl.q.rd(rx, c2, Eq.and.left(D1.abnf.radix_digit(rx, c2),
                D1.abnf.radix_rep(rest, rx), h2)), vl.qs.rrep(rest, rx, Eq.and.right(D1.abnf.radix_digit(rx, c2),
                D1.abnf.radix_rep(rest, rx), h2)))))

# every character of an integer starts a bare value
def vl.qs.int(+cs: List<&2, Char>, +hh: {D1.abnf.integer(cs) == True{} : Bool}) -> {M2.vl.qs(cs) == True{} : Bool}:
  M3.gp.or({M2.vl.qs(cs) == True{} : Bool}, D1.abnf.dec_int(cs), Bool.or(D1.abnf.hex_int(cs),
    Bool.or(D1.abnf.oct_int(cs), D1.abnf.bin_int(cs))), hh,
    hd => M1.vl.qs.dec(cs, hd),
    hr => M3.gp.or({M2.vl.qs(cs) == True{} : Bool}, D1.abnf.hex_int(cs), Bool.or(D1.abnf.oct_int(cs),
      D1.abnf.bin_int(cs)), hr,
      hx => vl.qs.pre(cs, 120, D1.AHex{}, {==}, hx),
      hq => M3.gp.or({M2.vl.qs(cs) == True{} : Bool}, D1.abnf.oct_int(cs), D1.abnf.bin_int(cs), hq,
        ho => vl.qs.pre(cs, 111, D1.AOct{}, {==}, ho),
        hb => vl.qs.pre(cs, 98, D1.ABin{}, {==}, hb))))

def L1.integer_is_bare_word(w, h):
  match w:
    case SNil{}:
      Eq.bit.absurd(&2, {D2.bw.word(SNil{}) == True{} : Bool}, h)
    case SCon{+hh, +tt}:
      M2.vl.bw.qs(SCon{hh, tt}, vl.qs.int(hh <> String.to_list(tt), h), {==})
