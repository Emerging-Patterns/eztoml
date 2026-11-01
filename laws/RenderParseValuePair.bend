import Base
import ../main.bend as T
import ./defs/BareValueGrammar.bend as D1
import ./defs/DocumentSameness.bend as D2

# LAW: a document of one pair, a bare key and a value that is no table (a
# scalar, a string, or an array or an inline table nested to any depth),
# well-formed and with every string in it shorter than 2^32 characters, reads
# back with no error as the same document
law render_parse_value_pair:
  for +e: String
  for +k: String
  for +ek: {T.bare(k) == True{} : Bool}
  for +v: T.Val
  for w: {T.wf(T.Doc{e, [T.VPair{k, v}]}) == True{} : Bool}
  for +hv: {D1.cv.wf(v) == True{} : Bool}
  for hl: {D1.cv.short1(v) == True{} : Bool}
  {Bool.and(String.is_empty(T.bad(T.parse(T.render(T.Doc{e, [T.VPair{k, v}]})))),
    D2.same(T.parse(T.render(T.Doc{e, [T.VPair{k, v}]})), T.Doc{e, [T.VPair{k, v}]})) == True{} : Bool}
