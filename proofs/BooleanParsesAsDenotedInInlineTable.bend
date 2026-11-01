# proofs of laws/BooleanParsesAsDenotedInInlineTable.bend
import Base
import ../laws/BooleanIsBareWord.bend as L1
import ../laws/BooleanParsesAsDenotedInInlineTable.bend as Laws
import ./lemmas/BooleanIsBareWord.bend as M1
import ./lemmas/BooleanWordExact.bend as M2

def Laws.boolean_parses_as_denoted_in_inline_table(k, ek, w, hw, v, hv):
  M1.vl.acc.i(k, ek, w, L1.boolean_is_bare_word(w, hw), v, M2.vl.hv.bool(String.to_list(w), hw, v, hv),
    M1.vl.sc.of(String.to_list(w), v, M2.vl.hv.bool(String.to_list(w), hw, v, hv)))
