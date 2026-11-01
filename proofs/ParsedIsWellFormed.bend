# proofs of laws/ParsedIsWellFormed.bend
import Base
import ../laws/ParsedIsWellFormed.bend as Laws
import ./lemmas/ParsedWellFormedness.bend as M1
import ./lemmas/WellFormedTextWalk.bend as M2

def Laws.gd_seal(rows, at, ee):
  M1.gd.S(rows, at, ee)

def Laws.gd_take(st, eg, val, ev):
  M2.gd.g.take(st, val, eg, ev)

def Laws.gd_fast_step(st, eg, cc, ec) :
  M2.gd.fast(st, cc, eg, ec)

def Laws.gd_held(st, eg) :
  M2.gd.once2(st, eg)
