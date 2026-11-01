# a float is a bare word, with its character tests and cuts
import Base
import ../../src/eq.bend as Eq
import ../../laws/FloatReadExactly.bend as L1
import ../../laws/defs/AbnfGrammar.bend as D1
import ../../laws/defs/BareValueGrammar.bend as D2
import ./BareValueCharTests.bend as M1
import ./BooleanIsBareWord.bend as M2
import ./GrammarWordMatching.bend as M3
import ./PrefixAndTake.bend as M4

# and an exponent mark
def vl.q.e(cc: Char, hh: {D1.abnf.e(cc) == True{} : Bool}) -> {D2.word.first(cc) == True{} : Bool}:
  match cc:
    case Chr{+xx}:
      M1.vl.fq(~(ch => D1.abnf.e(ch)), xx, hh, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# every character of a zero-prefixable-int starts a bare value
def vl.qs.zpi(
  cs: List<&2, Char>,
  +hh: {D1.abnf.zero_prefixable_int(cs) == True{} : Bool}
) -> {M2.vl.qs(cs) == True{} : Bool}:
  match cs:
    case []:
      Eq.bit.absurd(&2, {M2.vl.qs([]) == True{} : Bool}, hh)
    case +xx <> +tt:
      M4.and.tt(D2.word.first(xx), M2.vl.qs(tt), M1.vl.q.dig(xx, Eq.and.left(D1.abnf.DIGIT(xx), D1.abnf.dec_rep(tt),
          hh)),
        M1.vl.qs.decs(tt, M3.gp.rep.decs(tt, Eq.and.right(D1.abnf.DIGIT(xx), D1.abnf.dec_rep(tt), hh))))

# and of a float-exp-part
def vl.qs.fep(
  cs: List<&2, Char>,
  hh: {D1.abnf.float_exp_part(cs) == True{} : Bool}
) -> {M2.vl.qs(cs) == True{} : Bool}:
  match cs:
    case []:
      Eq.bit.absurd(&2, {M2.vl.qs([]) == True{} : Bool}, hh)
    case +xx <> +tt:
      M3.gp.or({M2.vl.qs(xx <> tt) == True{} : Bool}, Bool.and(Bool.or(D1.abnf.minus(xx), D1.abnf.plus(xx)),
        D1.abnf.zero_prefixable_int(tt)), D1.abnf.zero_prefixable_int(xx <> tt), hh,
        +ha => M4.and.tt(D2.word.first(xx), M2.vl.qs(tt), M1.vl.q.sign(xx, Eq.and.left(Bool.or(D1.abnf.minus(xx),
          D1.abnf.plus(xx)), D1.abnf.zero_prefixable_int(tt), ha)), vl.qs.zpi(tt, Eq.and.right(Bool.or(
          D1.abnf.minus(xx), D1.abnf.plus(xx)), D1.abnf.zero_prefixable_int(tt), ha))),
        hb => vl.qs.zpi(xx <> tt, hb))

# and of an exp
def vl.qs.exp(cs: List<&2, Char>, +hh: {D1.abnf.exp(cs) == True{} : Bool}) -> {M2.vl.qs(cs) == True{} : Bool}:
  match cs:
    case []:
      Eq.bit.absurd(&2, {M2.vl.qs([]) == True{} : Bool}, hh)
    case +xx <> +tt:
      M4.and.tt(D2.word.first(xx), M2.vl.qs(tt), vl.q.e(xx, Eq.and.left(D1.abnf.e(xx), D1.abnf.float_exp_part(tt), hh)),
        vl.qs.fep(tt, Eq.and.right(D1.abnf.e(xx), D1.abnf.float_exp_part(tt), hh)))

# and of a frac
def vl.qs.frac(cs: List<&2, Char>, +hh: {D1.abnf.frac(cs) == True{} : Bool}) -> {M2.vl.qs(cs) == True{} : Bool}:
  match cs:
    case []:
      Eq.bit.absurd(&2, {M2.vl.qs([]) == True{} : Bool}, hh)
    case +xx <> +tt:
      M4.and.tt(D2.word.first(xx), M2.vl.qs(tt), M1.vl.q.cp(xx, 46, Eq.and.left(D1.abnf.cp(xx, 46),
        D1.abnf.zero_prefixable_int(tt), hh), {==}), vl.qs.zpi(tt, Eq.and.right(D1.abnf.cp(xx, 46),
        D1.abnf.zero_prefixable_int(tt), hh)))

# and of an optional exp
def vl.qs.oexp(cs: List<&2, Char>, hh: {D1.abnf.opt_exp(cs) == True{} : Bool}) -> {M2.vl.qs(cs) == True{} : Bool}:
  match cs:
    case []:
      {==}
    case +xx <> +tt:
      vl.qs.exp(xx <> tt, hh)

# the claim for the rest of a cut word: both parts of such characters make
# it of such characters
def vl.CutIh(+tt: List<&2, Char>, +ct: D1.ACut) -> Type:
  {M2.vl.qs(D1.abnf.cut.pre(tt, ct)) == True{} : Bool} -> {M2.vl.qs(D1.abnf.cut.post(tt, ct)) == True{} : Bool} ->
    {M2.vl.qs(tt) == True{} : Bool}

# a word cut in two, both parts of such characters, is of such characters
def vl.qs.cut.go(
  cc: Bool,
  +xx: Char,
  +tt: List<&2, Char>,
  +ct: D1.ACut,
  +ec: {D1.abnf.cut.at(ct, xx) == cc : Bool},
  hp: {M2.vl.qs(D1.abnf.cut.pre(xx <> tt, ct)) == True{} : Bool},
  hq: {M2.vl.qs(D1.abnf.cut.post(xx <> tt, ct)) == True{} : Bool},
  ih: vl.CutIh(tt, ct)
) -> {M2.vl.qs(xx <> tt) == True{} : Bool}:
  match cc:
    case True{}:
      Equal.trans(Bool, M2.vl.qs(xx <> tt), M2.vl.qs(D1.abnf.cut.post.pick(True{}, xx, tt, D1.abnf.cut.post(tt, ct))),
        True{}, {==}, Equal.trans(Bool, M2.vl.qs(D1.abnf.cut.post.pick(True{}, xx, tt, D1.abnf.cut.post(tt, ct))),
        M2.vl.qs(D1.abnf.cut.post(xx <> tt, ct)), True{}, Equal.cong(Bool, Bool,
            bb => M2.vl.qs(D1.abnf.cut.post.pick(bb,
        xx, tt, D1.abnf.cut.post(tt, ct))), True{}, D1.abnf.cut.at(ct, xx), Equal.sym(Bool, D1.abnf.cut.at(ct,
        xx), True{}, ec)), hq))
    case False{}:
      +hp2 = {Equal.trans(Bool, M2.vl.qs(xx <> D1.abnf.cut.pre(tt, ct)), M2.vl.qs(D1.abnf.cut.pre(xx <> tt, ct)),
          True{},
        Equal.cong(Bool, Bool, bb => M2.vl.qs(D1.abnf.cut.pre.pick(bb, xx, D1.abnf.cut.pre(tt, ct))), False{},
        D1.abnf.cut.at(ct, xx), Equal.sym(Bool, D1.abnf.cut.at(ct, xx), False{}, ec)), hp)
        : {M2.vl.qs(xx <> D1.abnf.cut.pre(tt, ct)) == True{} : Bool}}
      +hq2 = {Equal.trans(Bool, M2.vl.qs(D1.abnf.cut.post(tt, ct)), M2.vl.qs(D1.abnf.cut.post(xx <> tt, ct)), True{},
        Equal.cong(Bool, Bool, bb => M2.vl.qs(D1.abnf.cut.post.pick(bb, xx, tt, D1.abnf.cut.post(tt, ct))), False{},
        D1.abnf.cut.at(ct, xx), Equal.sym(Bool, D1.abnf.cut.at(ct, xx), False{}, ec)), hq)
        : {M2.vl.qs(D1.abnf.cut.post(tt, ct)) == True{} : Bool}}
      M4.and.tt(D2.word.first(xx), M2.vl.qs(tt), Eq.and.left(D2.word.first(xx), M2.vl.qs(D1.abnf.cut.pre(tt, ct)), hp2),
        ih(Eq.and.right(D2.word.first(xx), M2.vl.qs(D1.abnf.cut.pre(tt, ct)), hp2), hq2))

# the same, by induction over the word
def vl.qs.cut(
  cs: List<&2, Char>,
  +ct: D1.ACut,
  hp: {M2.vl.qs(D1.abnf.cut.pre(cs, ct)) == True{} : Bool},
  hq: {M2.vl.qs(D1.abnf.cut.post(cs, ct)) == True{} : Bool}
) -> {M2.vl.qs(cs) == True{} : Bool}:
  match cs:
    case []:
      {==}
    case +xx <> +tt:
      vl.qs.cut.go(D1.abnf.cut.at(ct, xx), xx, tt, ct, {==}, hp, hq, h1 => h2 => vl.qs.cut(tt, ct, h1, h2))

# every character of frac [ exp ] starts a bare value
def vl.qs.fe(+cs: List<&2, Char>, +hh: {D1.abnf.frac_exp(cs) == True{} : Bool}) -> {M2.vl.qs(cs) == True{} : Bool}:
  vl.qs.cut(cs, D1.ACutExp{}, vl.qs.frac(D1.abnf.cut.pre(cs, D1.ACutExp{}), Eq.and.left(D1.abnf.frac(
    D1.abnf.cut.pre(cs, D1.ACutExp{})), D1.abnf.opt_exp(D1.abnf.cut.post(cs, D1.ACutExp{})), hh)),
    vl.qs.oexp(D1.abnf.cut.post(cs, D1.ACutExp{}), Eq.and.right(D1.abnf.frac(D1.abnf.cut.pre(cs,
    D1.ACutExp{})), D1.abnf.opt_exp(D1.abnf.cut.post(cs, D1.ACutExp{})), hh)))

# and of a float that is no special-float
def vl.qs.fstd(+cs: List<&2, Char>, +hh: {D1.abnf.float_std(cs) == True{} : Bool}) -> {M2.vl.qs(cs) == True{} : Bool}:
  vl.qs.cut(cs, D1.ACutDot{}, M1.vl.qs.dec(D1.abnf.cut.pre(cs, D1.ACutDot{}), Eq.and.left(D1.abnf.dec_int(
    D1.abnf.cut.pre(cs, D1.ACutDot{})), Bool.or(D1.abnf.exp(D1.abnf.cut.post(cs, D1.ACutDot{})),
    D1.abnf.frac_exp(D1.abnf.cut.post(cs, D1.ACutDot{}))), hh)),
    M3.gp.or({M2.vl.qs(D1.abnf.cut.post(cs, D1.ACutDot{})) == True{} : Bool}, D1.abnf.exp(D1.abnf.cut.post(cs,
      D1.ACutDot{})), D1.abnf.frac_exp(D1.abnf.cut.post(cs, D1.ACutDot{})), Eq.and.right(D1.abnf.dec_int(
      D1.abnf.cut.pre(cs, D1.ACutDot{})), Bool.or(D1.abnf.exp(D1.abnf.cut.post(cs, D1.ACutDot{})),
      D1.abnf.frac_exp(D1.abnf.cut.post(cs, D1.ACutDot{}))), hh),
      he => vl.qs.exp(D1.abnf.cut.post(cs, D1.ACutDot{}), he),
      hf => vl.qs.fe(D1.abnf.cut.post(cs, D1.ACutDot{}), hf)))

# inf or nan
def vl.qs.in(
  +cs: List<&2, Char>,
  +hh: {Bool.or(D1.abnf.inf(cs), D1.abnf.nan(cs)) == True{} : Bool}
) -> {M2.vl.qs(cs) == True{} : Bool}:
  M3.gp.or({M2.vl.qs(cs) == True{} : Bool}, D1.abnf.inf(cs), D1.abnf.nan(cs), hh,
    hi => M3.gp.subst(zs => {M2.vl.qs(zs) == True{} : Bool}, cs, String.to_list("inf"), M3.gp.chars(cs, "inf", hi),
        {==}),
    hn => M3.gp.subst(zs => {M2.vl.qs(zs) == True{} : Bool}, cs, String.to_list("nan"), M3.gp.chars(cs, "nan", hn),
        {==}))

# and of a special-float
def vl.qs.sf(cs: List<&2, Char>, hh: {D1.abnf.special_float(cs) == True{} : Bool}) -> {M2.vl.qs(cs) == True{} : Bool}:
  match cs:
    case []:
      Eq.bit.absurd(&2, {M2.vl.qs([]) == True{} : Bool}, hh)
    case +xx <> +tt:
      M3.gp.or({M2.vl.qs(xx <> tt) == True{} : Bool}, Bool.and(Bool.or(D1.abnf.minus(xx), D1.abnf.plus(xx)),
        Bool.or(D1.abnf.inf(tt), D1.abnf.nan(tt))), Bool.or(D1.abnf.inf(xx <> tt), D1.abnf.nan(xx <> tt)), hh,
        +ha => M4.and.tt(D2.word.first(xx), M2.vl.qs(tt), M1.vl.q.sign(xx, Eq.and.left(Bool.or(D1.abnf.minus(xx),
          D1.abnf.plus(xx)), Bool.or(D1.abnf.inf(tt), D1.abnf.nan(tt)), ha)), vl.qs.in(tt, Eq.and.right(Bool.or(
          D1.abnf.minus(xx), D1.abnf.plus(xx)), Bool.or(D1.abnf.inf(tt), D1.abnf.nan(tt)), ha))),
        hb => vl.qs.in(xx <> tt, hb))

# every character of a float starts a bare value
def vl.qs.flo(+cs: List<&2, Char>, +hh: {D1.abnf.float(cs) == True{} : Bool}) -> {M2.vl.qs(cs) == True{} : Bool}:
  M3.gp.or({M2.vl.qs(cs) == True{} : Bool}, D1.abnf.float_std(cs), D1.abnf.special_float(cs), hh,
    hs => vl.qs.fstd(cs, hs), hp => vl.qs.sf(cs, hp))

def L1.float_is_bare_word(w, h):
  match w:
    case SNil{}:
      Eq.bit.absurd(&2, {D2.bw.word(SNil{}) == True{} : Bool}, h)
    case SCon{+hh, +tt}:
      M2.vl.bw.qs(SCon{hh, tt}, vl.qs.flo(hh <> String.to_list(tt), h), {==})
