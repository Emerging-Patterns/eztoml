# proofs of laws/BooleanParsesAsDenotedInArray.bend
import Base
import ../laws/BooleanIsBareWord.bend as L1
import ../laws/BooleanParsesAsDenotedInArray.bend as Laws
import ./lemmas/BareWordInArray.bend as M1
import ./lemmas/BooleanIsBareWord.bend as M2
import ./lemmas/BooleanWordExact.bend as M3

def Laws.boolean_parses_as_denoted_in_array(k, ek, w, hw, v, hv):
  M1.vl.acc.a(k, ek, w, L1.boolean_is_bare_word(w, hw), v, M3.vl.hv.bool(String.to_list(w), hw, v, hv),
    M2.vl.sc.of(String.to_list(w), v, M3.vl.hv.bool(String.to_list(w), hw, v, hv)))
