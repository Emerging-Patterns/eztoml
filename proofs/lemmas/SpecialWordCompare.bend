# the special words true, false, inf and nan and how a word is compared with
# them
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/defs/BareValueGrammar.bend as D1

# The special words. word.spec compares the word with each of true, false,
# inf, nan and their signed forms, one character at a time, as abnf.chars_are
# does.

# comparing a word's text with a string is abnf.chars_are, while it still
# matches
def n1.streq(
  cs: List<&2, Char>,
  ss: String,
  ok: Bool
) -> {T.str.eq.step(String.from_list(cs), ss, ok) == Bool.and(ok, D1.abnf.chars_are(cs, ss)) : Bool}:
  match cs ss:
    case [] SNil{}:
      match ok:
        case True{}:
          {==}
        case False{}:
          {==}
    case [] SCon{_h, _t}:
      match ok:
        case True{}:
          {==}
        case False{}:
          {==}
    case _h <> _t SNil{}:
      match ok:
        case True{}:
          {==}
        case False{}:
          {==}
    case +hh <> tt SCon{+h2, t2}:
      match ok:
        case True{}:
          n1.streq(tt, t2, Char.is_eq(hh, h2))
        case False{}:
          {==}

# a word whose characters are those of a string is that string's characters
def n1.ca.eq(
  cs: List<&2, Char>,
  ss: String,
  +hh: {D1.abnf.chars_are(cs, ss) == True{} : Bool}
) -> {cs == String.to_list(ss) : List<&2, Char>}:
  match cs ss:
    case [] SNil{}:
      {==}
    case [] SCon{h0, t0}:
      Eq.bit.absurd(&2, {[] == String.to_list(SCon{h0, t0}) : List<&2, Char>}, hh)
    case h0 <> t0 SNil{}:
      Eq.bit.absurd(&2, {h0 <> t0 == [] : List<&2, Char>}, hh)
    case +h1 <> +t1 SCon{+h2, +t2}:
      +e1 = {Eq.char_eq_true(h1, h2, Eq.and.left(Char.is_eq(h1, h2), D1.abnf.chars_are(t1, t2), hh)) : {h1 == h2
        : Char}}
      +e2 = {n1.ca.eq(t1, t2, Eq.and.right(Char.is_eq(h1, h2), D1.abnf.chars_are(t1, t2), hh)) : {t1
        == String.to_list(t2) : List<&2, Char>}}
      %e1 : {h1 <> t1 == _ <> String.to_list(t2) : List<&2, Char>}
      %e2 : {h1 <> t1 == h1 <> _ : List<&2, Char>}
      {==}

# whether a word is one of the special words word.spec reads
def n1.isspec(+cs: List<&2, Char>) -> Bool:
  Bool.or(D1.abnf.chars_are(cs, "true"), Bool.or(D1.abnf.chars_are(cs, "false"), Bool.or(D1.abnf.chars_are(cs,
    "inf"), Bool.or(D1.abnf.chars_are(cs, "+inf"), Bool.or(D1.abnf.chars_are(cs, "-inf"),
    Bool.or(D1.abnf.chars_are(cs, "nan"), Bool.or(D1.abnf.chars_are(cs, "+nan"), D1.abnf.chars_are(cs,
    "-nan"))))))))

# a word's comparison with a special word, when abnf.chars_are refuses it
def n1.streq.f(
  +cs: List<&2, Char>,
  +ss: String,
  +hh: {D1.abnf.chars_are(cs, ss) == False{} : Bool}
) -> {False{} == T.str.eq(String.from_list(cs), ss) : Bool}:
  Equal.sym(Bool, T.str.eq(String.from_list(cs), ss), False{}, Equal.trans(Bool, T.str.eq(String.from_list(cs), ss),
    D1.abnf.chars_are(cs, ss), False{}, n1.streq(cs, ss, True{}), hh))

# a word that is none of the special words is no special value
def n1.spec.no(
  +cs: List<&2, Char>,
  +hs: {n1.isspec(cs) == False{} : Bool}
) -> {T.word.spec(String.from_list(cs)) == T.GotBad{""} : T.Got}:
  +ss = String.from_list(cs)
  +r1 = {Eq.or.right_false(D1.abnf.chars_are(cs, "true"), Bool.or(D1.abnf.chars_are(cs, "false"),
    Bool.or(D1.abnf.chars_are(cs, "inf"), Bool.or(D1.abnf.chars_are(cs, "+inf"), Bool.or(D1.abnf.chars_are(cs,
    "-inf"), Bool.or(D1.abnf.chars_are(cs, "nan"), Bool.or(D1.abnf.chars_are(cs, "+nan"),
    D1.abnf.chars_are(cs, "-nan"))))))), hs) : {Bool.or(D1.abnf.chars_are(cs, "false"),
    Bool.or(D1.abnf.chars_are(cs, "inf"), Bool.or(D1.abnf.chars_are(cs, "+inf"), Bool.or(D1.abnf.chars_are(cs,
    "-inf"), Bool.or(D1.abnf.chars_are(cs, "nan"), Bool.or(D1.abnf.chars_are(cs, "+nan"),
    D1.abnf.chars_are(cs, "-nan"))))))) == False{} : Bool}}
  +r2 = {Eq.or.right_false(D1.abnf.chars_are(cs, "false"), Bool.or(D1.abnf.chars_are(cs, "inf"),
    Bool.or(D1.abnf.chars_are(cs, "+inf"), Bool.or(D1.abnf.chars_are(cs, "-inf"), Bool.or(D1.abnf.chars_are(cs,
    "nan"), Bool.or(D1.abnf.chars_are(cs, "+nan"), D1.abnf.chars_are(cs, "-nan")))))), r1) :
    {Bool.or(D1.abnf.chars_are(cs, "inf"), Bool.or(D1.abnf.chars_are(cs, "+inf"), Bool.or(D1.abnf.chars_are(cs,
    "-inf"), Bool.or(D1.abnf.chars_are(cs, "nan"), Bool.or(D1.abnf.chars_are(cs, "+nan"),
    D1.abnf.chars_are(cs, "-nan")))))) == False{} : Bool}}
  +r3 = {Eq.or.right_false(D1.abnf.chars_are(cs, "inf"), Bool.or(D1.abnf.chars_are(cs, "+inf"),
    Bool.or(D1.abnf.chars_are(cs, "-inf"), Bool.or(D1.abnf.chars_are(cs, "nan"), Bool.or(D1.abnf.chars_are(cs,
    "+nan"), D1.abnf.chars_are(cs, "-nan"))))), r2) : {Bool.or(D1.abnf.chars_are(cs, "+inf"),
    Bool.or(D1.abnf.chars_are(cs, "-inf"), Bool.or(D1.abnf.chars_are(cs, "nan"), Bool.or(D1.abnf.chars_are(cs,
    "+nan"), D1.abnf.chars_are(cs, "-nan"))))) == False{} : Bool}}
  +r4 = {Eq.or.right_false(D1.abnf.chars_are(cs, "+inf"), Bool.or(D1.abnf.chars_are(cs, "-inf"),
    Bool.or(D1.abnf.chars_are(cs, "nan"), Bool.or(D1.abnf.chars_are(cs, "+nan"), D1.abnf.chars_are(cs,
    "-nan")))), r3) : {Bool.or(D1.abnf.chars_are(cs, "-inf"), Bool.or(D1.abnf.chars_are(cs, "nan"),
    Bool.or(D1.abnf.chars_are(cs, "+nan"), D1.abnf.chars_are(cs, "-nan")))) == False{} : Bool}}
  +r5 = {Eq.or.right_false(D1.abnf.chars_are(cs, "-inf"), Bool.or(D1.abnf.chars_are(cs, "nan"),
    Bool.or(D1.abnf.chars_are(cs, "+nan"), D1.abnf.chars_are(cs, "-nan"))), r4) : {Bool.or(D1.abnf.chars_are(cs,
    "nan"), Bool.or(D1.abnf.chars_are(cs, "+nan"), D1.abnf.chars_are(cs, "-nan"))) == False{} : Bool}}
  +r6 = {Eq.or.right_false(D1.abnf.chars_are(cs, "nan"), Bool.or(D1.abnf.chars_are(cs, "+nan"),
    D1.abnf.chars_are(cs, "-nan")), r5) : {Bool.or(D1.abnf.chars_are(cs, "+nan"), D1.abnf.chars_are(cs, "-nan"))
    == False{} : Bool}}
  %n1.streq.f(cs, "true", Eq.or.left_false(D1.abnf.chars_are(cs, "true"), Bool.or(D1.abnf.chars_are(cs, "false"),
    Bool.or(D1.abnf.chars_are(cs, "inf"), Bool.or(D1.abnf.chars_are(cs, "+inf"), Bool.or(D1.abnf.chars_are(cs,
    "-inf"), Bool.or(D1.abnf.chars_are(cs, "nan"), Bool.or(D1.abnf.chars_are(cs, "+nan"), D1.abnf.chars_are(cs,
    "-nan"))))))), hs)) : {T.word.spec.t(_, T.str.eq(ss, "false"), ss) == T.GotBad{""} : T.Got}
  %n1.streq.f(cs, "false", Eq.or.left_false(D1.abnf.chars_are(cs, "false"), Bool.or(D1.abnf.chars_are(cs, "inf"),
    Bool.or(D1.abnf.chars_are(cs, "+inf"), Bool.or(D1.abnf.chars_are(cs, "-inf"), Bool.or(D1.abnf.chars_are(cs,
    "nan"), Bool.or(D1.abnf.chars_are(cs, "+nan"), D1.abnf.chars_are(cs, "-nan")))))), r1)) :
    {T.word.spec.f(_, ss) == T.GotBad{""} : T.Got}
  %n1.streq.f(cs, "inf", Eq.or.left_false(D1.abnf.chars_are(cs, "inf"), Bool.or(D1.abnf.chars_are(cs, "+inf"),
    Bool.or(D1.abnf.chars_are(cs, "-inf"), Bool.or(D1.abnf.chars_are(cs, "nan"), Bool.or(D1.abnf.chars_are(cs,
    "+nan"), D1.abnf.chars_are(cs, "-nan"))))), r2)) :
    {T.word.spec.inf(_, T.str.eq(ss, "+inf"), T.str.eq(ss, "-inf"), ss) == T.GotBad{""} : T.Got}
  %n1.streq.f(cs, "+inf", Eq.or.left_false(D1.abnf.chars_are(cs, "+inf"), Bool.or(D1.abnf.chars_are(cs, "-inf"),
    Bool.or(D1.abnf.chars_are(cs, "nan"), Bool.or(D1.abnf.chars_are(cs, "+nan"), D1.abnf.chars_are(cs,
    "-nan")))), r3)) : {T.word.spec.inf2(_, T.str.eq(ss, "-inf"), ss) == T.GotBad{""} : T.Got}
  %n1.streq.f(cs, "-inf", Eq.or.left_false(D1.abnf.chars_are(cs, "-inf"), Bool.or(D1.abnf.chars_are(cs, "nan"),
    Bool.or(D1.abnf.chars_are(cs, "+nan"), D1.abnf.chars_are(cs, "-nan"))), r4)) :
    {T.word.spec.inf3(_, ss) == T.GotBad{""} : T.Got}
  %n1.streq.f(cs, "nan", Eq.or.left_false(D1.abnf.chars_are(cs, "nan"), Bool.or(D1.abnf.chars_are(cs, "+nan"),
    D1.abnf.chars_are(cs, "-nan")), r5)) : {T.word.spec.nan(_, T.str.eq(ss, "+nan"), T.str.eq(ss, "-nan"))
    == T.GotBad{""} : T.Got}
  %n1.streq.f(cs, "+nan", Eq.or.left_false(D1.abnf.chars_are(cs, "+nan"), D1.abnf.chars_are(cs, "-nan"), r6)) :
    {T.word.spec.nan2(_, T.str.eq(ss, "-nan")) == T.GotBad{""} : T.Got}
  %n1.streq.f(cs, "-nan", Eq.or.right_false(D1.abnf.chars_are(cs, "+nan"), D1.abnf.chars_are(cs, "-nan"), r6)) :
    {T.word.spec.nan3(_) == T.GotBad{""} : T.Got}
  {==}

# a claim made of each special word is made of every special word
def n1.spec.split.go(
  -P: List<&2, Char> -> Type,
  b1: Bool,
  b2: Bool,
  b3: Bool,
  b4: Bool,
  b5: Bool,
  b6: Bool,
  b7: Bool,
  b8: Bool,
  cs: List<&2, Char>,
  +e1: {D1.abnf.chars_are(cs, "true") == b1 : Bool},
  +e2: {D1.abnf.chars_are(cs, "false") == b2 : Bool},
  +e3: {D1.abnf.chars_are(cs, "inf") == b3 : Bool},
  +e4: {D1.abnf.chars_are(cs, "+inf") == b4 : Bool},
  +e5: {D1.abnf.chars_are(cs, "-inf") == b5 : Bool},
  +e6: {D1.abnf.chars_are(cs, "nan") == b6 : Bool},
  +e7: {D1.abnf.chars_are(cs, "+nan") == b7 : Bool},
  +e8: {D1.abnf.chars_are(cs, "-nan") == b8 : Bool},
  +hs: {Bool.or(b1, Bool.or(b2, Bool.or(b3, Bool.or(b4, Bool.or(b5, Bool.or(b6, Bool.or(b7, b8))))))) == True{} : Bool},
  p1: P(String.to_list("true")),
  p2: P(String.to_list("false")),
  p3: P(String.to_list("inf")),
  p4: P(String.to_list("+inf")),
  p5: P(String.to_list("-inf")),
  p6: P(String.to_list("nan")),
  p7: P(String.to_list("+nan")),
  p8: P(String.to_list("-nan"))
) -> P(cs):
  match b1:
    case True{}:
      %Equal.sym(List<&2, Char>, cs, String.to_list("true"), n1.ca.eq(cs, "true", e1)) : P(_)
      p1
    case False{}:
      match b2:
        case True{}:
          %Equal.sym(List<&2, Char>, cs, String.to_list("false"), n1.ca.eq(cs, "false", e2)) : P(_)
          p2
        case False{}:
          match b3:
            case True{}:
              %Equal.sym(List<&2, Char>, cs, String.to_list("inf"), n1.ca.eq(cs, "inf", e3)) : P(_)
              p3
            case False{}:
              match b4:
                case True{}:
                  %Equal.sym(List<&2, Char>, cs, String.to_list("+inf"), n1.ca.eq(cs, "+inf", e4)) : P(_)
                  p4
                case False{}:
                  match b5:
                    case True{}:
                      %Equal.sym(List<&2, Char>, cs, String.to_list("-inf"), n1.ca.eq(cs, "-inf", e5)) : P(_)
                      p5
                    case False{}:
                      match b6:
                        case True{}:
                          %Equal.sym(List<&2, Char>, cs, String.to_list("nan"), n1.ca.eq(cs, "nan", e6)) : P(_)
                          p6
                        case False{}:
                          match b7:
                            case True{}:
                              %Equal.sym(List<&2, Char>, cs, String.to_list("+nan"), n1.ca.eq(cs, "+nan", e7)) : P(_)
                              p7
                            case False{}:
                              match b8:
                                case True{}:
                                  %Equal.sym(List<&2, Char>, cs, String.to_list("-nan"), n1.ca.eq(cs, "-nan",
                                    e8)) : P(_)
                                  p8
                                case False{}:
                                  Eq.bit.absurd(&1, P(cs), hs)

# a claim made of each special word is made of every special word
def n1.spec.split(
  -P: List<&2, Char> -> Type,
  +cs: List<&2, Char>,
  +hs: {n1.isspec(cs) == True{} : Bool},
  p1: P(String.to_list("true")),
  p2: P(String.to_list("false")),
  p3: P(String.to_list("inf")),
  p4: P(String.to_list("+inf")),
  p5: P(String.to_list("-inf")),
  p6: P(String.to_list("nan")),
  p7: P(String.to_list("+nan")),
  p8: P(String.to_list("-nan"))
) -> P(cs):
  n1.spec.split.go(P, D1.abnf.chars_are(cs, "true"), D1.abnf.chars_are(cs, "false"), D1.abnf.chars_are(cs, "inf"),
    D1.abnf.chars_are(cs, "+inf"), D1.abnf.chars_are(cs, "-inf"), D1.abnf.chars_are(cs, "nan"),
    D1.abnf.chars_are(cs, "+nan"), D1.abnf.chars_are(cs, "-nan"), cs, {==}, {==}, {==}, {==}, {==}, {==}, {==},
    {==}, hs, p1, p2, p3, p4, p5, p6, p7, p8)

# The words word.val reads by their routes: a special word is read as itself,
# and any other word by the datetime reader or the numeral scan.

# a word that is none of the special words goes to the datetime reader or the
# numeral scan, special first character or not
def n1.wv.ns.go(
  ld: Bool,
  +cs: List<&2, Char>,
  hs: {n1.isspec(cs) == False{} : Bool}
) -> {T.word.val.pick(ld, cs) == T.word.route.date(T.word.as_date(T.word.or(T.word.colon(cs), T.word.dash(cs,
  True{})), T.word.ee(cs)), cs) : T.Got}:
  match ld:
    case True{}:
      %Equal.sym(T.Got, T.word.spec(String.from_list(cs)), T.GotBad{""}, n1.spec.no(cs, hs)) : {T.word.route(_,
        T.word.or(T.word.colon(cs), T.word.dash(cs, True{})), cs) == T.word.route.date(T.word.as_date(T.word.or(
        T.word.colon(cs), T.word.dash(cs, True{})), T.word.ee(cs)), cs) : T.Got}
      {==}
    case False{}:
      {==}

# a word that is none of the special words goes to the datetime reader or the
# numeral scan
def n1.wv.ns(
  +cs: List<&2, Char>,
  hs: {n1.isspec(cs) == False{} : Bool}
) -> {T.word.val(cs) == T.word.route.date(T.word.as_date(T.word.or(T.word.colon(cs), T.word.dash(cs, True{})),
  T.word.ee(cs)), cs) : T.Got}:
  match cs:
    case []:
      {==}
    case +hh <> +tt:
      n1.wv.ns.go(T.word.special(hh), hh <> tt, hs)
