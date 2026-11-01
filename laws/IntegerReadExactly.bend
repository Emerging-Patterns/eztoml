# An integer is read exactly when it matches toml.abnf's `integer` rule and
# lies within signed 64 bits, and reads to its sign and its value's decimal
# digits, with no leading zero unless the value is 0
#
# also rests on: laws/BareWordReadsOn.bend, laws/BareWordReadsOnInArray.bend,
# laws/BareWordRefused.bend, laws/BareWordRefusedInArray.bend,
# laws/NumOneSign.bend, laws/NumSignedZeroUnderscore.bend,
# laws/NumTwoSigns.bend, laws/NumZeroUnderscore.bend,
# laws/WordRefusedInDocument.bend, laws/WordSignedZeroUnderscore.bend,
# laws/WordTwoSigns.bend, laws/WordZeroUnderscore.bend
import Base
import ../main.bend as T
import ./defs/AbnfGrammar.bend as D1
import ./defs/BareValueGrammar.bend as D2
import ./defs/DocumentSameness.bend as D3
import ./defs/GrammarDerivations.bend as D4

# LAW: a well-formed integer's text is classified as its sign and its digits:
# render writes the sign (a minus only) and the digits, and the scan reads
# them back, a lone 0 and -0 as well as digits with no leading zero, up to the
# signed 64-bit bounds
law int_word:
  for +sg: T.Sign
  for +ds: String
  for +w: {T.wf.int(sg, ds) == True{} : Bool}
  {T.word.val(String.to_list(T.render.atom(T.VInt{sg, ds}))) == T.GotVal{T.VInt{sg, ds}} : T.Got}

#
# The integer, float and boolean words, exact in both directions
# (docs/rfc/eztoml-grammar-proofs.md, WP-N1): word.val reads a bare word as a
# value of one of these kinds exactly when the word matches that kind's rule
# of toml.abnf (an integer within signed 64 bits, as prose.int_in_range
# says), and the value is the one g.val says the word denotes. Each law holds
# for every value, so a word with no rule of the kind reads as no value of
# it.

# whether a bare word's reading is the integer vv: vv's sign and digits are
# the reading's
def n1.got.int(gg: T.Got, vv: T.Val) -> Bool:
  match gg vv:
    case T.GotVal{T.VInt{s1, d1}} T.VInt{s2, d2}:
      Bool.and(D3.sign.eq(s2, s1), String.eq(d2, d1))
    case _g _v:
      False{}

# LAW: a bare word reads as the integer v exactly when it matches toml.abnf's
# integer rule, lies within signed 64 bits, and denotes v: its sign, and its
# value's decimal digits with no leading zero
law integer_word_exact:
  for +cs: List<&2, Char>
  for +v: T.Val
  {n1.got.int(T.word.val(cs), v) == Bool.and(Bool.and(D1.abnf.integer(cs), D1.prose.int_in_range(cs)),
    D1.g.val(D4.GvInteger{cs}, v)) : Bool}

# LAW: a bare word is read as an integer in a document exactly as it is on
# its own: for every bare key k and bare word w, k = w and a newline parse
# with no error to one pair named k holding the integer v exactly when w
# matches toml.abnf's integer rule, lies within signed 64 bits and denotes v
law integer_parses_exactly:
  for +k: String
  for ek: {T.bare(k) == True{} : Bool}
  for +w: String
  for hw: {D2.bw.word(w) == True{} : Bool}
  for +v: T.Val
  {n1.got.int(D2.bw.got(T.parse(D1.bw.kv(k, w)), k), v) == Bool.and(Bool.and(D1.abnf.integer(String.to_list(w)),
    D1.prose.int_in_range(String.to_list(w))), D1.g.val(D4.GvInteger{String.to_list(w)}, v)) : Bool}

# LAW: every word toml.abnf's integer rule matches is a bare word: every
# character of it starts a bare value, so the scan reads it whole
law integer_is_bare_word:
  for +w: String
  for h: {D1.abnf.integer(String.to_list(w)) == True{} : Bool}
  {D2.bw.word(w) == True{} : Bool}

# LAW: an integer word in a document: for every bare key k and every word w
# that matches toml.abnf's integer rule within signed 64 bits and denotes v, k
# = w and a newline parse with no error to one pair named k holding v
law integer_parses_as_denoted:
  for +k: String
  for ek: {T.bare(k) == True{} : Bool}
  for +w: String
  for +hw: {Bool.and(D1.abnf.integer(String.to_list(w)), D1.prose.int_in_range(String.to_list(w))) == True{} : Bool}
  for +v: T.Val
  for +hv: {D1.g.val(D4.GvInteger{String.to_list(w)}, v) == True{} : Bool}
  {T.parse(D1.bw.kv(k, w)) == T.Doc{"", [T.VPair{k, v}]} : T.Doc}

# LAW: an integer word as an array's item: for every bare key k and every word
# w that matches toml.abnf's integer rule within signed 64 bits and denotes v,
# k = [w] and a newline parse with no error to one pair named k holding an
# array of v
law integer_parses_as_denoted_in_array:
  for +k: String
  for ek: {T.bare(k) == True{} : Bool}
  for +w: String
  for +hw: {Bool.and(D1.abnf.integer(String.to_list(w)), D1.prose.int_in_range(String.to_list(w))) == True{} : Bool}
  for +v: T.Val
  for +hv: {D1.g.val(D4.GvInteger{String.to_list(w)}, v) == True{} : Bool}
  {T.parse(D1.bw.kva(k, w)) == T.Doc{"", [T.VPair{k, T.VArr{[v]}}]} : T.Doc}

# LAW: an integer word as an inline table's value: for every bare key k and
# every word w that matches toml.abnf's integer rule within signed 64 bits and
# denotes v, k = {v = w} and a newline parse with no error to one pair named k
# holding an inline table whose pair v holds v
law integer_parses_as_denoted_in_inline_table:
  for +k: String
  for ek: {T.bare(k) == True{} : Bool}
  for +w: String
  for +hw: {Bool.and(D1.abnf.integer(String.to_list(w)), D1.prose.int_in_range(String.to_list(w))) == True{} : Bool}
  for +v: T.Val
  for +hv: {D1.g.val(D4.GvInteger{String.to_list(w)}, v) == True{} : Bool}
  {T.parse(D1.bw.kvi(k, w)) == T.Doc{"", [T.VPair{k, T.VInl{[T.VPair{"v", v}]}}]} : T.Doc}
