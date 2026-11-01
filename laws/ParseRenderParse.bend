# For every text `t` of Unicode scalar values, shorter than 2^32 characters
# and with `render(parse(t))` shorter than 2^32 characters, with
# `bad(parse(t)) == ""`: `parse(render(parse(t)))` is `same` as `parse(t)`,
# and `render` of it is `render(parse(t))`
import Base
import ../main.bend as T
import ./defs/BareValueGrammar.bend as D1
import ./defs/DocumentSameness.bend as D2

# WP-R2: a parsed document renders, reparses and renders again unchanged.
# The first half is laws/RenderThenParse.bend at parse(t), which laws/ParsedIsWellFormed.bend makes well-formed;
# the second is render_parse_canon read through render: render writes a span
# as its characters, and already writes each table's pairs that are no table
# before its tables, so render(canon(d)) is render(d).

# LAW: for every text of Unicode scalar values shorter than 2^32 characters
# that parse reads with no error, and whose parse renders to a text shorter
# than 2^32 characters, parse reads that rendering back as the same document,
# which renders to the same text again
law parse_render_parse:
  for +t: String
  for h_u: {T.wf.text(t) == True{} : Bool}
  for h_s: {D1.short(t) == True{} : Bool}
  for +h_r: {D1.short(T.render(T.parse(t))) == True{} : Bool}
  for ok: {String.is_empty(T.bad(T.parse(t))) == True{} : Bool}
  {Bool.and(D2.same(T.parse(T.render(T.parse(t))), T.parse(t)),
    String.eq(T.render(T.parse(T.render(T.parse(t)))), T.render(T.parse(t)))) == True{} : Bool}
