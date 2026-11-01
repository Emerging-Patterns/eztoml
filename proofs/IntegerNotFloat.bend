# proofs of laws/IntegerNotFloat.bend
import Base
import ../src/eq.bend as Eq
import ../laws/IntegerNotFloat.bend as Laws
import ../laws/defs/AbnfGrammar.bend as D1
import ./lemmas/DigitsWrittenBack.bend as M1
import ./lemmas/GrammarWordMatching.bend as M2

# a word is no float when nothing follows a first decimal-point or e (there
# is none) and it is no special-float
def gp.flo.zero(
  +cs: List<&2, Char>,
  ep: {D1.abnf.cut.post(cs, D1.ACutDot{}) == [] : List<&2, Char>},
  es: {D1.abnf.special_float(cs) == False{} : Bool}
) -> {D1.abnf.float(cs) == False{} : Bool}:
  +aa = D1.abnf.dec_int(D1.abnf.cut.pre(cs, D1.ACutDot{}))
  +post = D1.abnf.cut.post(cs, D1.ACutDot{})
  Equal.trans(Bool, Bool.or(Bool.and(aa, Bool.or(D1.abnf.exp(post), D1.abnf.frac_exp(post))),
    D1.abnf.special_float(cs)), Bool.or(Bool.and(aa, False{}), D1.abnf.special_float(cs)), False{},
    Equal.cong(List<&2, Char>, Bool, pp => Bool.or(Bool.and(aa, Bool.or(D1.abnf.exp(pp), D1.abnf.frac_exp(pp))),
      D1.abnf.special_float(cs)), post, [], ep),
    Equal.trans(Bool, Bool.or(Bool.and(aa, False{}), D1.abnf.special_float(cs)),
      Bool.or(Bool.and(aa, False{}), False{}), False{},
      Equal.cong(Bool, Bool, ss => Bool.or(Bool.and(aa, False{}), ss), D1.abnf.special_float(cs), False{}, es),
      Equal.cong(Bool, Bool, xx => Bool.or(xx, False{}), Bool.and(aa, False{}), False{}, M1.gs.andf(aa))))

# a word of DIGITs and underscores has no decimal-point or e
def gp.decs.post(
  cs: List<&2, Char>,
  +h: {M2.gp.decs(cs) == True{} : Bool}
) -> {D1.abnf.cut.post(cs, D1.ACutDot{}) == [] : List<&2, Char>}:
  match cs:
    case []:
      {==}
    case +hh <> +tt:
      +ec = {M2.gp.dc.elim(zz => {D1.abnf.cut.at(D1.ACutDot{}, zz) == False{} : Bool}, hh,
        Eq.and.left(M2.gp.dc(hh), M2.gp.decs(tt), h), {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})
        : {D1.abnf.cut.at(D1.ACutDot{}, hh) == False{} : Bool}}
      %Equal.sym(Bool, D1.abnf.cut.at(D1.ACutDot{}, hh), False{}, ec) :
        {D1.abnf.cut.post.pick(_, hh, tt, D1.abnf.cut.post(tt, D1.ACutDot{})) == [] : List<&2, Char>}
      gp.decs.post(tt, Eq.and.right(M2.gp.dc(hh), M2.gp.decs(tt), h))

# and it is no inf and no nan
def gp.decs.noinf(
  tt: List<&2, Char>,
  +h: {M2.gp.decs(tt) == True{} : Bool}
) -> {Bool.or(D1.abnf.inf(tt), D1.abnf.nan(tt)) == False{} : Bool}:
  match tt:
    case []:
      {==}
    case +xx <> +yy:
      M2.gp.dc.elim(zz => {Bool.or(D1.abnf.inf(zz <> yy), D1.abnf.nan(zz <> yy)) == False{} : Bool}, xx,
        Eq.and.left(M2.gp.dc(xx), M2.gp.decs(yy), h), {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# after a sign, a word of DIGITs and underscores is no special-float
def gp.flo.sp(
  +tt: List<&2, Char>,
  +h: {M2.gp.decs(tt) == True{} : Bool}
) -> {Bool.or(Bool.or(D1.abnf.inf(tt), D1.abnf.nan(tt)), False{}) == False{} : Bool}:
  Equal.cong(Bool, Bool, xx => Bool.or(xx, False{}), Bool.or(D1.abnf.inf(tt), D1.abnf.nan(tt)), False{},
    gp.decs.noinf(tt, h))

# a sign and an unsigned-dec-int is no float
def gp.flo.signed(
  +hh: Char,
  +tt: List<&2, Char>,
  +ha: {Bool.and(Bool.or(D1.abnf.minus(hh), D1.abnf.plus(hh)), D1.abnf.unsigned_dec_int(tt)) == True{} : Bool}
) -> {D1.abnf.float(hh <> tt) == False{} : Bool}:
  +hd = {M2.gp.udi.decs(tt, Eq.and.right(Bool.or(D1.abnf.minus(hh), D1.abnf.plus(hh)),
    D1.abnf.unsigned_dec_int(tt), ha)) : {M2.gp.decs(tt) == True{} : Bool}}
  M2.gp.or({D1.abnf.float(hh <> tt) == False{} : Bool}, D1.abnf.minus(hh), D1.abnf.plus(hh),
    Eq.and.left(Bool.or(D1.abnf.minus(hh), D1.abnf.plus(hh)), D1.abnf.unsigned_dec_int(tt), ha),
    hm => M2.gp.head(zs => {D1.abnf.float(zs) == False{} : Bool}, hh, '-', tt, M1.gs.minus(hh, hm),
      gp.flo.zero('-' <> tt, gp.decs.post(tt, hd), gp.flo.sp(tt, hd))),
    hp => M2.gp.head(zs => {D1.abnf.float(zs) == False{} : Bool}, hh, '+', tt, M1.gs.plus(hh, hp),
      gp.flo.zero('+' <> tt, gp.decs.post(tt, hd), gp.flo.sp(tt, hd))))

# a word of DIGITs and underscores is no float
def gp.flo.unsigned(
  +hh: Char,
  +tt: List<&2, Char>,
  +hd: {M2.gp.decs(hh <> tt) == True{} : Bool}
) -> {D1.abnf.float(hh <> tt) == False{} : Bool}:
  gp.flo.zero(hh <> tt, gp.decs.post(hh <> tt, hd),
    M2.gp.dc.elim(zz => {D1.abnf.special_float(zz <> tt) == False{} : Bool}, hh,
      Eq.and.left(M2.gp.dc(hh), M2.gp.decs(tt), hd), {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}))

# a dec-int is no float
def gp.decint.flo(
  cs: List<&2, Char>,
  +h: {D1.abnf.dec_int(cs) == True{} : Bool}
) -> {D1.abnf.float(cs) == False{} : Bool}:
  match cs:
    case []:
      Eq.bit.absurd(&2, {D1.abnf.float([]) == False{} : Bool}, h)
    case +hh <> +tt:
      M2.gp.or({D1.abnf.float(hh <> tt) == False{} : Bool},
        Bool.and(Bool.or(D1.abnf.minus(hh), D1.abnf.plus(hh)), D1.abnf.unsigned_dec_int(tt)),
        D1.abnf.unsigned_dec_int(hh <> tt), h,
        ha => gp.flo.signed(hh, tt, ha),
        hb => gp.flo.unsigned(hh, tt, M2.gp.udi.decs(hh <> tt, hb)))

def Laws.integer_not_float(cs, h):
  M2.gp.or({D1.abnf.float(cs) == False{} : Bool}, D1.abnf.dec_int(cs),
    Bool.or(D1.abnf.hex_int(cs), Bool.or(D1.abnf.oct_int(cs), D1.abnf.bin_int(cs))), h,
    hd => gp.decint.flo(cs, hd),
    hr => M2.gp.or({D1.abnf.float(cs) == False{} : Bool}, D1.abnf.hex_int(cs),
      Bool.or(D1.abnf.oct_int(cs), D1.abnf.bin_int(cs)), hr,
      hx => M2.gp.pre.case(zs => {D1.abnf.float(zs) == False{} : Bool}, cs, 120, D1.AHex{}, hx, _c => _r => {==}),
      hq => M2.gp.or({D1.abnf.float(cs) == False{} : Bool}, D1.abnf.oct_int(cs), D1.abnf.bin_int(cs), hq,
        ho => M2.gp.pre.case(zs => {D1.abnf.float(zs) == False{} : Bool}, cs, 111, D1.AOct{}, ho, _c => _r => {==}),
        hb => M2.gp.pre.case(zs => {D1.abnf.float(zs) == False{} : Bool}, cs, 98, D1.ABin{}, hb,
          _c => _r => {==}))))
