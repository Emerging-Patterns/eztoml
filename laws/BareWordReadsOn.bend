import Base
import ../main.bend as T
import ./defs/BareValueGrammar.bend as D1

# LAW: a bare word is read as word.val classifies it: from every state that
# waits for a value, a bare word whose characters word.val reads as the value
# v, then a text that ends it (a space, a tab, a newline, a carriage return,
# #, a comma, ] or }, or nothing, but not a date's space before a digit),
# reads on as that text from the state with v placed
law bare_word_reads_on:
  for +w: String
  for hw: {D1.bw.word(w) == True{} : Bool}
  for +v: T.Val
  for hv: {T.word.val(String.to_list(w)) == T.GotVal{v} : T.Got}
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
  {T.doc.read(String.append(w, rest), T.MScan{D1.vpos(rw, hs, he, ps, bk, qk, sk, un, lf, ab)})
    == T.doc.read(rest, T.MScan{D1.bw.put(sk, v, rw, hs, he, ps, bk, qk, un, lf, ab)}) : T.Doc}
