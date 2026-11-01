# part of: laws/IntegerReadExactly.bend, laws/FloatReadExactly.bend,
# laws/DateTimeReadExactly.bend
import Base
import ../main.bend as T
import ./defs/BareValueGrammar.bend as D1

# LAW: and a bare word word.val refuses, as an array's item, leaves an error
law bare_word_refused_in_array:
  for +w: String
  for +hw: {D1.bw.word(w) == True{} : Bool}
  for +why: String
  for hv: {T.word.val(String.to_list(w)) == T.GotBad{why} : T.Got}
  for +rw: List<&2, T.Val>
  for +hs: List<&2, String>
  for +he: List<&2, String>
  for +ps: List<&2, String>
  for +bk: T.Lex
  for +qk: T.QKind
  for +sk: List<&2, T.Ctx>
  for +un: U32
  for +lf: U32
  for +ab: Bool
  for +rest: String
  for ee: {D1.bw.end(D1.bw.rev(w, []), rest) == True{} : Bool}
  {String.is_empty(T.bad(T.doc.read(String.append(w, rest), T.MScan{D1.s1.apos(rw, hs, he, ps, bk, qk, sk, un, lf,
    ab)}))) == False{} : Bool}
