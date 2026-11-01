# A float is read exactly when it matches toml.abnf's `float` rule, and reads
# to its sign and its spelling with the sign and every `_` removed; `render`
# writes the sign (`-` only) and that spelling
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

# LAW: a well-formed float's text is classified as its sign and its spelling:
# render writes the sign (a minus only) and the spelling, inf, nan, or
# toml.abnf's float with no sign and no underscore, and the scan reads them
# back with the spelling kept
law flo_word:
  for +sg: T.Sign
  for +text: String
  for +w: {T.wf.flo(text) == True{} : Bool}
  {T.word.val(String.to_list(T.render.atom(T.VFlo{sg, text}))) == T.GotVal{T.VFlo{sg, text}} : T.Got}

# whether a bare word's reading is the float vv: vv's sign and spelling are
# the reading's
def n1.got.flo(gg: T.Got, vv: T.Val) -> Bool:
  match gg vv:
    case T.GotVal{T.VFlo{s1, t1}} T.VFlo{s2, t2}:
      Bool.and(D3.sign.eq(s2, s1), String.eq(t2, t1))
    case _g _v:
      False{}

# LAW: a bare word reads as the float v exactly when it matches toml.abnf's
# float rule and denotes v: its sign, and its spelling with the sign and
# every underscore removed
law float_word_exact:
  for +cs: List<&2, Char>
  for +v: T.Val
  {n1.got.flo(T.word.val(cs), v) == Bool.and(D1.abnf.float(cs), D1.g.val(D4.GvFloat{cs}, v)) : Bool}

# LAW: and as a float: k = w parses to the float v exactly when w matches
# toml.abnf's float rule and denotes v
law float_parses_exactly:
  for +k: String
  for ek: {T.bare(k) == True{} : Bool}
  for +w: String
  for hw: {D2.bw.word(w) == True{} : Bool}
  for +v: T.Val
  {n1.got.flo(D2.bw.got(T.parse(D1.bw.kv(k, w)), k), v) == Bool.and(D1.abnf.float(String.to_list(w)),
    D1.g.val(D4.GvFloat{String.to_list(w)}, v)) : Bool}

# the sign as render writes it: nothing for plus, a minus for minus
def bw.sign(sg: T.Sign) -> String:
  match sg:
    case T.Plus{}:
      ""
    case T.Minus{}:
      "-"

# LAW: render writes a float as its sign, a minus only and nothing for a
# plus, then its spelling as it is
law float_render:
  for +sg: T.Sign
  for +t: String
  {T.render.atom(T.VFlo{sg, t}) == String.append(bw.sign(sg), t) : String}

# LAW: and so is every word the float rule matches
law float_is_bare_word:
  for +w: String
  for h: {D1.abnf.float(String.to_list(w)) == True{} : Bool}
  {D2.bw.word(w) == True{} : Bool}

# LAW: a float word in a document: for every bare key k and every word w that
# matches toml.abnf's float rule and denotes v, k = w and a newline parse with
# no error to one pair named k holding v
law float_parses_as_denoted:
  for +k: String
  for ek: {T.bare(k) == True{} : Bool}
  for +w: String
  for +hw: {D1.abnf.float(String.to_list(w)) == True{} : Bool}
  for +v: T.Val
  for +hv: {D1.g.val(D4.GvFloat{String.to_list(w)}, v) == True{} : Bool}
  {T.parse(D1.bw.kv(k, w)) == T.Doc{"", [T.VPair{k, v}]} : T.Doc}

# LAW: a float word as an array's item: for every bare key k and every word w
# that matches toml.abnf's float rule and denotes v, k = [w] and a newline
# parse with no error to one pair named k holding an array of v
law float_parses_as_denoted_in_array:
  for +k: String
  for ek: {T.bare(k) == True{} : Bool}
  for +w: String
  for +hw: {D1.abnf.float(String.to_list(w)) == True{} : Bool}
  for +v: T.Val
  for +hv: {D1.g.val(D4.GvFloat{String.to_list(w)}, v) == True{} : Bool}
  {T.parse(D1.bw.kva(k, w)) == T.Doc{"", [T.VPair{k, T.VArr{[v]}}]} : T.Doc}

# LAW: a float word as an inline table's value: for every bare key k and every
# word w that matches toml.abnf's float rule and denotes v, k = {v = w} and a
# newline parse with no error to one pair named k holding an inline table whose
# pair v holds v
law float_parses_as_denoted_in_inline_table:
  for +k: String
  for ek: {T.bare(k) == True{} : Bool}
  for +w: String
  for +hw: {D1.abnf.float(String.to_list(w)) == True{} : Bool}
  for +v: T.Val
  for +hv: {D1.g.val(D4.GvFloat{String.to_list(w)}, v) == True{} : Bool}
  {T.parse(D1.bw.kvi(k, w)) == T.Doc{"", [T.VPair{k, T.VInl{[T.VPair{"v", v}]}}]} : T.Doc}
