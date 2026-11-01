# For every document `d` with `wf(d)` whose rendered text `render(d)` is
# shorter than 2^32 characters: `bad(parse(render(d)))` is `""`, and
# `parse(render(d))` is `same` as `d`
import Base
import ../main.bend as T
import ./defs/BareValueGrammar.bend as D1
import ./defs/DocumentSameness.bend as D2

# LAW: for every well-formed document whose rendered text is shorter than
# 2^32 characters, the document parse reads back from that text, every span
# read out, is canon of it: no error, and every table's pairs that are no
# table in order, before its tables and arrays of tables in order
law render_parse_canon:
  for +d: T.Doc
  for +w: {T.wf(d) == True{} : Bool}
  for h_s: {D1.short(T.render(d)) == True{} : Bool}
  {D1.own(T.parse(T.render(d))) == D2.canon(d) : T.Doc}

# LAW: a well-formed document is the same as canon of it: moving a table's
# pairs that are no table in front of its tables, and reading every span
# out, changes no value same compares
law canon_same:
  for +d: T.Doc
  for +w: {T.wf(d) == True{} : Bool}
  {D2.same(D2.canon(d), d) == True{} : Bool}

# LAW: render then parse is the same document: for every well-formed document
# whose rendered text is shorter than 2^32 characters, parse reads that text
# back with no error, as a document the same as the one render was given
law render_parse:
  for +d: T.Doc
  for +w: {T.wf(d) == True{} : Bool}
  for h_s: {D1.short(T.render(d)) == True{} : Bool}
  {Bool.and(String.is_empty(T.bad(T.parse(T.render(d)))), D2.same(T.parse(T.render(d)), d)) == True{} : Bool}
