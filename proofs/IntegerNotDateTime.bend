# proofs of laws/IntegerNotDateTime.bend
import Base
import ../src/eq.bend as Eq
import ../laws/IntegerNotDateTime.bend as Laws
import ../laws/defs/AbnfGrammar.bend as D1
import ./lemmas/GrammarWordMatching.bend as M1
import ./lemmas/NumberNotDateTime.bend as M2

# a word of only such characters is one
def gp.decs.nd(cs: List<&2, Char>, +h: {M1.gp.decs(cs) == True{} : Bool}) -> {M2.gp.nd(cs) == True{} : Bool}:
  match cs:
    case []:
      {==}
    case +hh <> +tt:
      %Equal.sym(Bool, M1.gp.dc(hh), True{}, Eq.and.left(M1.gp.dc(hh), M1.gp.decs(tt), h)) :
        {M2.gp.nd.pick(_, hh, M2.gp.nd(tt)) == True{} : Bool}
      gp.decs.nd(tt, Eq.and.right(M1.gp.dc(hh), M1.gp.decs(tt), h))

# a dec-int is no date-time
def gp.decint.dt(
  cs: List<&2, Char>,
  +h: {D1.abnf.dec_int(cs) == True{} : Bool}
) -> {D1.abnf.date_time(cs) == False{} : Bool}:
  match cs:
    case []:
      Eq.bit.absurd(&2, {D1.abnf.date_time([]) == False{} : Bool}, h)
    case +hh <> +tt:
      M1.gp.or({D1.abnf.date_time(hh <> tt) == False{} : Bool},
        Bool.and(Bool.or(D1.abnf.minus(hh), D1.abnf.plus(hh)), D1.abnf.unsigned_dec_int(tt)),
        D1.abnf.unsigned_dec_int(hh <> tt), h,
        ha => M2.gp.dt.sign(hh, tt, Eq.and.left(Bool.or(D1.abnf.minus(hh), D1.abnf.plus(hh)),
          D1.abnf.unsigned_dec_int(tt), ha)),
        hb => M2.gp.nd.dt(hh <> tt, gp.decs.nd(hh <> tt, M1.gp.udi.decs(hh <> tt, hb))))

def Laws.integer_not_date_time(cs, h):
  M1.gp.or({D1.abnf.date_time(cs) == False{} : Bool}, D1.abnf.dec_int(cs),
    Bool.or(D1.abnf.hex_int(cs), Bool.or(D1.abnf.oct_int(cs), D1.abnf.bin_int(cs))), h,
    hd => gp.decint.dt(cs, hd),
    hr => M1.gp.or({D1.abnf.date_time(cs) == False{} : Bool}, D1.abnf.hex_int(cs),
      Bool.or(D1.abnf.oct_int(cs), D1.abnf.bin_int(cs)), hr,
      hx => M1.gp.pre.case(zs => {D1.abnf.date_time(zs) == False{} : Bool}, cs, 120, D1.AHex{}, hx,
        _c => _r => {==}),
      hq => M1.gp.or({D1.abnf.date_time(cs) == False{} : Bool}, D1.abnf.oct_int(cs), D1.abnf.bin_int(cs), hq,
        ho => M1.gp.pre.case(zs => {D1.abnf.date_time(zs) == False{} : Bool}, cs, 111, D1.AOct{}, ho,
          _c => _r => {==}),
        hb => M1.gp.pre.case(zs => {D1.abnf.date_time(zs) == False{} : Bool}, cs, 98, D1.ABin{}, hb,
          _c => _r => {==}))))
