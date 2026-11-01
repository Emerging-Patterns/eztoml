# proofs of laws/FloatNotDateTime.bend
import Base
import ../src/eq.bend as Eq
import ../laws/FloatNotDateTime.bend as Laws
import ../laws/defs/AbnfGrammar.bend as D1
import ../laws/defs/BareValueGrammar.bend as D2
import ./lemmas/DigitsWrittenBack.bend as M1
import ./lemmas/GrammarWordMatching.bend as M2
import ./lemmas/NumberNotDateTime.bend as M3

# a special-float is no date-time: it starts with a sign, an i or an n
def gp.spec.dt(
  cs: List<&2, Char>,
  +h: {D1.abnf.special_float(cs) == True{} : Bool}
) -> {D1.abnf.date_time(cs) == False{} : Bool}:
  match cs:
    case []:
      Eq.bit.absurd(&2, {D1.abnf.date_time([]) == False{} : Bool}, h)
    case +hh <> +tt:
      M2.gp.or({D1.abnf.date_time(hh <> tt) == False{} : Bool},
        Bool.and(Bool.or(D1.abnf.minus(hh), D1.abnf.plus(hh)), Bool.or(D1.abnf.inf(tt), D1.abnf.nan(tt))),
        Bool.or(D1.abnf.inf(hh <> tt), D1.abnf.nan(hh <> tt)), h,
        ha => M3.gp.dt.sign(hh, tt, Eq.and.left(Bool.or(D1.abnf.minus(hh), D1.abnf.plus(hh)),
          Bool.or(D1.abnf.inf(tt), D1.abnf.nan(tt)), ha)),
        hb => M2.gp.or({D1.abnf.date_time(hh <> tt) == False{} : Bool}, D1.abnf.inf(hh <> tt),
          D1.abnf.nan(hh <> tt), hb,
          hi => M2.gp.head(zs => {D1.abnf.date_time(zs) == False{} : Bool}, hh, 'i', tt,
            Eq.char_eq_true(hh, 'i', Eq.and.left(Char.is_eq(hh, 'i'), D2.abnf.chars_are(tt, "nf"), hi)), {==}),
          hn => M2.gp.head(zs => {D1.abnf.date_time(zs) == False{} : Bool}, hh, 'n', tt,
            Eq.char_eq_true(hh, 'n', Eq.and.left(Char.is_eq(hh, 'n'), D2.abnf.chars_are(tt, "an"), hn)), {==})))

# the step of gp.pre.nd: a decimal-point or e first is no - or :, and a DIGIT
# or underscore first leaves the rest
def gp.pre.nd.go(
  +hh: Char,
  +tt: List<&2, Char>,
  cc: Bool,
  +ec: {D1.abnf.cut.at(D1.ACutDot{}, hh) == cc : Bool},
  +h: {M2.gp.decs(D1.abnf.cut.pre(hh <> tt, D1.ACutDot{})) == True{} : Bool},
  ih: {M2.gp.decs(D1.abnf.cut.pre(tt, D1.ACutDot{})) == True{} : Bool} -> {M3.gp.nd(tt) == True{} : Bool}
) -> {M3.gp.nd(hh <> tt) == True{} : Bool}:
  match cc:
    case True{}:
      M2.gp.or({M3.gp.nd(hh <> tt) == True{} : Bool}, D1.abnf.cp(hh, 46),
        Bool.or(D1.abnf.cp(hh, 101), D1.abnf.cp(hh, 69)), ec,
        hd => M2.gp.head(zs => {M3.gp.nd(zs) == True{} : Bool}, hh, Chr{46}, tt, M1.gp.cp(hh, 46, hd), {==}),
        he => M2.gp.or({M3.gp.nd(hh <> tt) == True{} : Bool}, D1.abnf.cp(hh, 101), D1.abnf.cp(hh, 69), he,
          hl => M2.gp.head(zs => {M3.gp.nd(zs) == True{} : Bool}, hh, Chr{101}, tt, M1.gp.cp(hh, 101, hl), {==}),
          hu => M2.gp.head(zs => {M3.gp.nd(zs) == True{} : Bool}, hh, Chr{69}, tt, M1.gp.cp(hh, 69, hu), {==})))
    case False{}:
      +pt = D1.abnf.cut.pre(tt, D1.ACutDot{})
      +hq = {Equal.trans(Bool, M2.gp.decs(hh <> pt),
        M2.gp.decs(D1.abnf.cut.pre.pick(D1.abnf.cut.at(D1.ACutDot{}, hh), hh, pt)), True{},
        Equal.cong(Bool, Bool, xx => M2.gp.decs(D1.abnf.cut.pre.pick(xx, hh, pt)), False{},
          D1.abnf.cut.at(D1.ACutDot{}, hh), Equal.sym(Bool, D1.abnf.cut.at(D1.ACutDot{}, hh), False{}, ec)), h)
        : {M2.gp.decs(hh <> pt) == True{} : Bool}}
      %Equal.sym(Bool, M2.gp.dc(hh), True{}, Eq.and.left(M2.gp.dc(hh), M2.gp.decs(pt), hq)) :
        {M3.gp.nd.pick(_, hh, M3.gp.nd(tt)) == True{} : Bool}
      ih(Eq.and.right(M2.gp.dc(hh), M2.gp.decs(pt), hq))

# a word whose part before its first decimal-point or e holds only DIGITs and
# underscores has no - or : before a character that is none of those
def gp.pre.nd(
  cs: List<&2, Char>,
  +h: {M2.gp.decs(D1.abnf.cut.pre(cs, D1.ACutDot{})) == True{} : Bool}
) -> {M3.gp.nd(cs) == True{} : Bool}:
  match cs:
    case []:
      {==}
    case +hh <> +tt:
      gp.pre.nd.go(hh, tt, D1.abnf.cut.at(D1.ACutDot{}, hh), {==}, h, hr => gp.pre.nd(tt, hr))

# a word whose integer part is unsigned, before its first decimal-point or e,
# is no date-time
def gp.pre.dt.u(
  +hh: Char,
  +tt: List<&2, Char>,
  +hd: {M2.gp.decs(hh <> D1.abnf.cut.pre(tt, D1.ACutDot{})) == True{} : Bool}
) -> {D1.abnf.date_time(hh <> tt) == False{} : Bool}:
  +pt = D1.abnf.cut.pre(tt, D1.ACutDot{})
  M3.gp.nd.dt(hh <> tt, Equal.trans(Bool, M3.gp.nd(hh <> tt), M3.gp.nd(tt), True{},
    Equal.cong(Bool, Bool, xx => M3.gp.nd.pick(xx, hh, M3.gp.nd(tt)), M2.gp.dc(hh), True{},
      Eq.and.left(M2.gp.dc(hh), M2.gp.decs(pt), hd)),
    gp.pre.nd(tt, Eq.and.right(M2.gp.dc(hh), M2.gp.decs(pt), hd))))

# the step of gp.pre.dt: a decimal-point or e first leaves no integer part,
# and otherwise the integer part starts with this character
def gp.pre.dt.go(
  +hh: Char,
  +tt: List<&2, Char>,
  cc: Bool,
  +ec: {D1.abnf.cut.at(D1.ACutDot{}, hh) == cc : Bool},
  +h: {D1.abnf.dec_int(D1.abnf.cut.pre(hh <> tt, D1.ACutDot{})) == True{} : Bool}
) -> {D1.abnf.date_time(hh <> tt) == False{} : Bool}:
  match cc:
    case True{}:
      +pt = D1.abnf.cut.pre(tt, D1.ACutDot{})
      Eq.bit.absurd(&2, {D1.abnf.date_time(hh <> tt) == False{} : Bool},
        Equal.trans(Bool, False{}, D1.abnf.dec_int(D1.abnf.cut.pre.pick(D1.abnf.cut.at(D1.ACutDot{}, hh),
          hh, pt)), True{},
          Equal.cong(Bool, Bool, xx => D1.abnf.dec_int(D1.abnf.cut.pre.pick(xx, hh, pt)), True{},
            D1.abnf.cut.at(D1.ACutDot{}, hh), Equal.sym(Bool, D1.abnf.cut.at(D1.ACutDot{}, hh), True{}, ec)),
          h))
    case False{}:
      +pt = D1.abnf.cut.pre(tt, D1.ACutDot{})
      +hq = {Equal.trans(Bool, D1.abnf.dec_int(hh <> pt),
        D1.abnf.dec_int(D1.abnf.cut.pre.pick(D1.abnf.cut.at(D1.ACutDot{}, hh), hh, pt)), True{},
        Equal.cong(Bool, Bool, xx => D1.abnf.dec_int(D1.abnf.cut.pre.pick(xx, hh, pt)), False{},
          D1.abnf.cut.at(D1.ACutDot{}, hh), Equal.sym(Bool, D1.abnf.cut.at(D1.ACutDot{}, hh), False{}, ec)), h)
        : {D1.abnf.dec_int(hh <> pt) == True{} : Bool}}
      M2.gp.or({D1.abnf.date_time(hh <> tt) == False{} : Bool},
        Bool.and(Bool.or(D1.abnf.minus(hh), D1.abnf.plus(hh)), D1.abnf.unsigned_dec_int(pt)),
        D1.abnf.unsigned_dec_int(hh <> pt), hq,
        ha => M3.gp.dt.sign(hh, tt, Eq.and.left(Bool.or(D1.abnf.minus(hh), D1.abnf.plus(hh)),
          D1.abnf.unsigned_dec_int(pt), ha)),
        hb => gp.pre.dt.u(hh, tt, M2.gp.udi.decs(hh <> pt, hb)))

# a word whose part before its first decimal-point or e is a dec-int is no
# date-time
def gp.pre.dt(
  cs: List<&2, Char>,
  +h: {D1.abnf.dec_int(D1.abnf.cut.pre(cs, D1.ACutDot{})) == True{} : Bool}
) -> {D1.abnf.date_time(cs) == False{} : Bool}:
  match cs:
    case []:
      Eq.bit.absurd(&2, {D1.abnf.date_time([]) == False{} : Bool}, h)
    case +hh <> +tt:
      gp.pre.dt.go(hh, tt, D1.abnf.cut.at(D1.ACutDot{}, hh), {==}, h)

def Laws.float_not_date_time(cs, h):
  +post = D1.abnf.cut.post(cs, D1.ACutDot{})
  +aa = D1.abnf.dec_int(D1.abnf.cut.pre(cs, D1.ACutDot{}))
  +bb = Bool.or(D1.abnf.exp(post), D1.abnf.frac_exp(post))
  M2.gp.or({D1.abnf.date_time(cs) == False{} : Bool}, Bool.and(aa, bb), D1.abnf.special_float(cs), h,
    hs => gp.pre.dt(cs, Eq.and.left(aa, bb, hs)),
    hp => gp.spec.dt(cs, hp))
