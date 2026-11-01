# the character tests that decide where a bare value starts and continues
import Base
import ../../src/eq.bend as Eq
import ../../laws/defs/AbnfGrammar.bend as D1
import ../../laws/defs/BareValueGrammar.bend as D2
import ./BareWordReadsOn.bend as M1
import ./BooleanIsBareWord.bend as M2
import ./DigitsWrittenBack.bend as M3
import ./GrammarWordMatching.bend as M4
import ./PrefixAndTake.bend as M5

# the character tests of a bare value, given false for each of the twelve
# characters that do not start one: the eight that end one, both quotes, [
# and {
def vl.fq.fin(
  b1: Bool,
  b2: Bool,
  b3: Bool,
  b4: Bool,
  b5: Bool,
  b6: Bool,
  b7: Bool,
  b8: Bool,
  b9: Bool,
  b10: Bool,
  b11: Bool,
  b12: Bool,
  e1: {b1 == False{} : Bool},
  e2: {b2 == False{} : Bool},
  e3: {b3 == False{} : Bool},
  e4: {b4 == False{} : Bool},
  e5: {b5 == False{} : Bool},
  e6: {b6 == False{} : Bool},
  e7: {b7 == False{} : Bool},
  e8: {b8 == False{} : Bool},
  e9: {b9 == False{} : Bool},
  e10: {b10 == False{} : Bool},
  e11: {b11 == False{} : Bool},
  e12: {b12 == False{} : Bool}
) -> {Bool.and(Bool.and(Bool.not(Bool.or(Bool.or(b1, b2), Bool.or(Bool.or(b3, b4), Bool.or(b5, Bool.or(b6,
  Bool.or(b7, b8)))))), Bool.not(Bool.or(b9, b10))), Bool.not(Bool.or(b11, b12))) == True{} : Bool}:
  match b1:
    case True{}:
      Eq.bit.absurd2(&2, {Bool.and(Bool.and(Bool.not(Bool.or(Bool.or(True{}, b2), Bool.or(Bool.or(b3, b4), Bool.or(b5,
        Bool.or(b6, Bool.or(b7, b8)))))), Bool.not(Bool.or(b9, b10))), Bool.not(Bool.or(b11, b12))) == True{} : Bool},
        e1)
    case False{}:
      match b2:
        case True{}:
          Eq.bit.absurd2(&2, {Bool.and(Bool.and(Bool.not(Bool.or(Bool.or(False{}, True{}), Bool.or(Bool.or(b3, b4),
            Bool.or(b5, Bool.or(b6, Bool.or(b7, b8)))))), Bool.not(Bool.or(b9, b10))), Bool.not(Bool.or(b11, b12))) ==
            True{} : Bool}, e2)
        case False{}:
          match b3:
            case True{}:
              Eq.bit.absurd2(&2, {Bool.and(Bool.and(Bool.not(Bool.or(Bool.or(False{}, False{}), Bool.or(Bool.or(True{},
                b4), Bool.or(b5, Bool.or(b6, Bool.or(b7, b8)))))), Bool.not(Bool.or(b9, b10))), Bool.not(Bool.or(b11,
                b12))) == True{} : Bool}, e3)
            case False{}:
              match b4:
                case True{}:
                  Eq.bit.absurd2(&2, {Bool.and(Bool.and(Bool.not(Bool.or(Bool.or(False{}, False{}),
                    Bool.or(Bool.or(False{}, True{}), Bool.or(b5, Bool.or(b6, Bool.or(b7, b8)))))),
                    Bool.not(Bool.or(b9, b10))), Bool.not(Bool.or(b11, b12))) == True{} : Bool}, e4)
                case False{}:
                  match b5:
                    case True{}:
                      Eq.bit.absurd2(&2, {Bool.and(Bool.and(Bool.not(Bool.or(Bool.or(False{}, False{}),
                        Bool.or(Bool.or(False{}, False{}), Bool.or(True{}, Bool.or(b6, Bool.or(b7, b8)))))),
                        Bool.not(Bool.or(b9, b10))), Bool.not(Bool.or(b11, b12))) == True{} : Bool}, e5)
                    case False{}:
                      match b6:
                        case True{}:
                          Eq.bit.absurd2(&2, {Bool.and(Bool.and(Bool.not(Bool.or(Bool.or(False{}, False{}),
                            Bool.or(Bool.or(False{}, False{}), Bool.or(False{}, Bool.or(True{}, Bool.or(b7, b8)))))),
                            Bool.not(Bool.or(b9, b10))), Bool.not(Bool.or(b11, b12))) == True{} : Bool}, e6)
                        case False{}:
                          match b7:
                            case True{}:
                              Eq.bit.absurd2(&2, {Bool.and(Bool.and(Bool.not(Bool.or(Bool.or(False{}, False{}),
                                Bool.or(Bool.or(False{}, False{}), Bool.or(False{}, Bool.or(False{}, Bool.or(True{},
                                b8)))))), Bool.not(Bool.or(b9, b10))), Bool.not(Bool.or(b11, b12))) == True{} : Bool},
                                e7)
                            case False{}:
                              match b8:
                                case True{}:
                                  Eq.bit.absurd2(&2, {Bool.and(Bool.and(Bool.not(Bool.or(Bool.or(False{}, False{}),
                                    Bool.or(Bool.or(False{}, False{}), Bool.or(False{}, Bool.or(False{},
                                    Bool.or(False{}, True{})))))), Bool.not(Bool.or(b9, b10))), Bool.not(Bool.or(b11,
                                    b12))) == True{} : Bool}, e8)
                                case False{}:
                                  match b9:
                                    case True{}:
                                      Eq.bit.absurd2(&2, {Bool.and(Bool.and(Bool.not(Bool.or(Bool.or(False{}, False{}),
                                        Bool.or(Bool.or(False{}, False{}), Bool.or(False{}, Bool.or(False{},
                                        Bool.or(False{}, False{})))))), Bool.not(Bool.or(True{}, b10))),
                                        Bool.not(Bool.or(b11, b12))) == True{} : Bool}, e9)
                                    case False{}:
                                      match b10:
                                        case True{}:
                                          Eq.bit.absurd2(&2, {Bool.and(Bool.and(Bool.not(Bool.or(Bool.or(False{},
                                            False{}), Bool.or(Bool.or(False{}, False{}), Bool.or(False{},
                                            Bool.or(False{}, Bool.or(False{}, False{})))))), Bool.not(Bool.or(False{},
                                            True{}))), Bool.not(Bool.or(b11, b12))) == True{} : Bool}, e10)
                                        case False{}:
                                          match b11:
                                            case True{}:
                                              Eq.bit.absurd2(&2, {Bool.and(Bool.and(Bool.not(Bool.or(Bool.or(False{},
                                                False{}), Bool.or(Bool.or(False{}, False{}), Bool.or(False{},
                                                Bool.or(False{}, Bool.or(False{}, False{})))))),
                                                Bool.not(Bool.or(False{}, False{}))), Bool.not(Bool.or(True{}, b12)))
                                                == True{} : Bool}, e11)
                                            case False{}:
                                              match b12:
                                                case True{}:
                                                  Eq.bit.absurd2(&2,
                                                    {Bool.and(Bool.and(Bool.not(Bool.or(Bool.or(False{}, False{}),
                                                    Bool.or(Bool.or(False{}, False{}), Bool.or(False{},
                                                    Bool.or(False{}, Bool.or(False{}, False{})))))),
                                                    Bool.not(Bool.or(False{}, False{}))), Bool.not(Bool.or(False{},
                                                    True{}))) == True{} : Bool}, e12)
                                                case False{}:
                                                  {==}

# a character a predicate passes is not one it fails
def vl.ne.go(
  ~_pp: Char -> Bool,
  bb: Bool,
  +xx: U32,
  +kk: U32,
  ee: {U32.is_eq(xx, kk) == bb : Bool},
  yes: {_pp(Chr{xx}) == True{} : Bool},
  no: {_pp(Chr{kk}) == False{} : Bool}
) -> {bb == False{} : Bool}:
  match bb:
    case True{}:
      Eq.bit.gone(&2, {True{} == False{} : Bool}, Eq.refute_char(Chr{xx}, Chr{kk}, _pp, ee, yes, no))
    case False{}:
      {==}

# the code point of a character a predicate passes is none it fails
def vl.ne(
  ~_pp: Char -> Bool,
  +xx: U32,
  +kk: U32,
  yes: {_pp(Chr{xx}) == True{} : Bool},
  no: {_pp(Chr{kk}) == False{} : Bool}
) -> {U32.is_eq(xx, kk) == False{} : Bool}:
  Equal.trans(Bool, U32.is_eq(xx, kk), U32.is_eq(xx, kk), False{}, {==}, vl.ne.go(~_pp, U32.is_eq(xx, kk), xx, kk,
    {==}, yes, no))

# a character a predicate passes starts a bare value, when the predicate
# fails the twelve that do not
def vl.fq(
  ~_pp: Char -> Bool,
  +xx: U32,
  +yes: {_pp(Chr{xx}) == True{} : Bool},
  n1: {_pp(Chr{32}) == False{} : Bool},
  n2: {_pp(Chr{9}) == False{} : Bool},
  n3: {_pp(Chr{10}) == False{} : Bool},
  n4: {_pp(Chr{13}) == False{} : Bool},
  n5: {_pp(Chr{35}) == False{} : Bool},
  n6: {_pp(Chr{44}) == False{} : Bool},
  n7: {_pp(Chr{93}) == False{} : Bool},
  n8: {_pp(Chr{125}) == False{} : Bool},
  n9: {_pp(Chr{34}) == False{} : Bool},
  n10: {_pp(Chr{39}) == False{} : Bool},
  n11: {_pp(Chr{91}) == False{} : Bool},
  n12: {_pp(Chr{123}) == False{} : Bool}
) -> {D2.word.first(Chr{xx}) == True{} : Bool}:
  vl.fq.fin(U32.is_eq(xx, 32), U32.is_eq(xx, 9), U32.is_eq(xx, 10), U32.is_eq(xx, 13), U32.is_eq(xx, 35),
    U32.is_eq(xx, 44), U32.is_eq(xx, 93), U32.is_eq(xx, 125), U32.is_eq(xx, 34), U32.is_eq(xx, 39), U32.is_eq(xx, 91),
    U32.is_eq(xx, 123), vl.ne(~_pp, xx, 32, yes, n1), vl.ne(~_pp, xx, 9, yes, n2), vl.ne(~_pp, xx, 10, yes, n3),
    vl.ne(~_pp, xx, 13, yes, n4), vl.ne(~_pp, xx, 35, yes, n5), vl.ne(~_pp, xx, 44, yes, n6), vl.ne(~_pp, xx, 93, yes,
      n7),
    vl.ne(~_pp, xx, 125, yes, n8), vl.ne(~_pp, xx, 34, yes, n9), vl.ne(~_pp, xx, 39, yes, n10), vl.ne(~_pp, xx, 91,
      yes, n11),
    vl.ne(~_pp, xx, 123, yes, n12))

# a DIGIT starts a bare value
def vl.q.dig(cc: Char, hh: {D1.abnf.DIGIT(cc) == True{} : Bool}) -> {D2.word.first(cc) == True{} : Bool}:
  match cc:
    case Chr{+xx}:
      vl.fq(~(ch => D1.abnf.DIGIT(ch)), xx, hh, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==},
        {==})

# so does a DIGIT or an underscore
def vl.q.dc(cc: Char, hh: {M4.gp.dc(cc) == True{} : Bool}) -> {D2.word.first(cc) == True{} : Bool}:
  match cc:
    case Chr{+xx}:
      vl.fq(~(ch => M4.gp.dc(ch)), xx, hh, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# and a sign
def vl.q.sign(
  cc: Char,
  hh: {Bool.or(D1.abnf.minus(cc), D1.abnf.plus(cc)) == True{} : Bool}
) -> {D2.word.first(cc) == True{} : Bool}:
  match cc:
    case Chr{+xx}:
      vl.fq(~(+ch => Bool.or(D1.abnf.minus(ch), D1.abnf.plus(ch))), xx, hh, {==}, {==}, {==}, {==}, {==}, {==},
        {==},
        {==}, {==}, {==}, {==}, {==})

# a character a code point test passed starts a bare value when that code
# point's character does
def vl.q.cp(
  +cc: Char,
  +nn: U32,
  +hh: {D1.abnf.cp(cc, nn) == True{} : Bool},
  hn: {D2.word.first(Chr{nn}) == True{} : Bool}
) -> {D2.word.first(cc) == True{} : Bool}:
  M1.vl.chs(ch => {D2.word.first(ch) == True{} : Bool}, cc, Chr{nn}, M3.gp.cp(cc, nn, hh), hn)

# the characters of a list of DIGITs and underscores start bare values
def vl.qs.decs(cs: List<&2, Char>, +hh: {M4.gp.decs(cs) == True{} : Bool}) -> {M2.vl.qs(cs) == True{} : Bool}:
  match cs:
    case []:
      {==}
    case +xx <> +tt:
      M5.and.tt(D2.word.first(xx), M2.vl.qs(tt), vl.q.dc(xx, Eq.and.left(M4.gp.dc(xx), M4.gp.decs(tt), hh)),
        vl.qs.decs(tt, Eq.and.right(M4.gp.dc(xx), M4.gp.decs(tt), hh)))

# so do a dec-int's
def vl.qs.dec(cs: List<&2, Char>, +hh: {D1.abnf.dec_int(cs) == True{} : Bool}) -> {M2.vl.qs(cs) == True{} : Bool}:
  match cs:
    case []:
      Eq.bit.absurd(&2, {M2.vl.qs([]) == True{} : Bool}, hh)
    case +xx <> +tt:
      M4.gp.or({M2.vl.qs(xx <> tt) == True{} : Bool}, Bool.and(Bool.or(D1.abnf.minus(xx), D1.abnf.plus(xx)),
        D1.abnf.unsigned_dec_int(tt)), D1.abnf.unsigned_dec_int(xx <> tt), hh,
        +ha => M5.and.tt(D2.word.first(xx), M2.vl.qs(tt), vl.q.sign(xx, Eq.and.left(Bool.or(D1.abnf.minus(xx),
          D1.abnf.plus(xx)), D1.abnf.unsigned_dec_int(tt), ha)), vl.qs.decs(tt, M4.gp.udi.decs(tt,
          Eq.and.right(Bool.or(D1.abnf.minus(xx), D1.abnf.plus(xx)), D1.abnf.unsigned_dec_int(tt), ha)))),
        hb => vl.qs.decs(xx <> tt, M4.gp.udi.decs(xx <> tt, hb)))
