# eztoml: the laws. The human states them; PROOF.bend must prove them. The
# slice is string-valued sectioned docs, so what matters is that a lookup
# answers with what was written for it, and that parse, render and the
# classifiers do what they claim.
import Base
import ./toml.bend as T
import ./main.bend as Toml

# LAW: a table answers a key with the value written for it, whatever pairs
# follow. A later pair of the same name never shadows an earlier one.
law value_first:
  for +k: String
  for v: String
  for ps: List<&2, T.Kv>
  {T.value(T.Kv{k, v} <> ps, k) == v : String}

# LAW: whatever a document quotes, the parser takes back out of the quotes
# unchanged. Every value is written quoted and a file path may be a quoted
# key, so this round trip is what makes a document readable by the writer.
law quote_strip:
  for +s: String
  {T.strip(T.quote(s), '"', '"') == s : String}

# The shapes toml.bend had before the cost rewrite, kept here so that the
# rewrites' one real risk can be stated rather than sampled: that the cheaper
# definitions answer exactly what the old ones answered, on every input.
# These are the specification and toml.bend is the implementation. Nothing
# but the laws below reads them.
#
# What was wrong with them is not what they answer, it is what they cost.
# `Bool.pick`, `Bool.and` and `Bool.or` are ordinary functions, so every arm
# and both sides are reduced before the answer is chosen.

# the line classifier, before: four picks nested, so `head_of(s, ...)` and
# `pair_of(String.split(s, '='))` were built for every line, including the
# blanks and the comments the first two arms exist to answer
def old.line_of(+s: String) -> T.Line:
  Bool.pick(T.Line, String.is_empty(s), T.LSkip{},
    Bool.pick(T.Line, String.starts_with(s, "#"), T.LSkip{},
      Bool.pick(T.Line, String.starts_with(s, "["),
        T.head_of(s, String.ends_with(s, "]")),
        Bool.pick(T.Line, String.contains(s, "="),
          T.pair_of(String.split(s, '=')),
          T.LBad{s ++ " is neither a section header nor a key"}))))

# the bare-key walk, before: `Bool.and` runs both sides, so the first char a
# bare key may not hold still cost a walk of the rest of the key
def old.bare.all(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      True{}
    case +h <> t:
      Bool.and(T.bare.at(h), old.bare.all(t))

# LAW: the cascade of matches answers what the nest of picks answered, on
# every line. This is the whole risk of the rewrite, and it is not a
# theoretical one: the nest tests for a blank line first, and a cascade that
# dropped that test would call an empty line neither a header nor a key.
law line_of_agrees:
  for +s: String
  {old.line_of(s) == T.line_of(s) : T.Line}

# LAW: and the walk that now really does stop at the first char a bare key
# may not hold answers what the walk that did not stop answered
law bare_all_agrees:
  for cs: List<&2, Char>
  {old.bare.all(cs) == T.bare.all(cs) : Bool}

# the section a half-read document is still filling
def toml.open(t: T.Toml) -> String:
  T.Toml{bad, name, pairs, done} = t
  name

# LAW: a space at the front of a line is not part of the line. The trim runs
# before the line is classified, so a `[section]` indented by a space is still
# a section header and a key indented by a space is still that key.
law trim_drops_leading_space:
  for s: String
  {T.trim(SCon{' ', s}) == T.trim(s) : String}

# LAW: the first error a document holds is the one it reports; a later one
# never replaces it. A syntax error puts the parser in a state every line
# after it is read in, so the last error is the least informative one there
# is.
law first_error_wins:
  for +bad: String
  for why: String
  for e: {False{} == String.is_empty(bad) : Bool}
  {T.first(bad, why) == bad : String}

# LAW: the pairs written before the first header are not a section. There is
# no top-level table here, and inventing one named "" would give a lookup a
# section to find.
law flush_skips_unnamed:
  for pairs: List<&2, T.Kv>
  for done: List<&2, T.Sect>
  {T.flush("", pairs, done) == done : List<&2, T.Sect>}

# LAW: and a header that was written is a section whether or not anything was
# written under it, with its pairs back in the order they were written.
law flush_keeps_named:
  for +name: String
  for pairs: List<&2, T.Kv>
  for done: List<&2, T.Sect>
  for e: {False{} == String.is_empty(name) : Bool}
  {T.flush(name, pairs, done)
    == T.Sect{name, List.reverse(&2, T.Kv, pairs)} <> done : List<&2, T.Sect>}

# LAW: a pair written before any header is an error and is not filed anywhere.
# Silently keeping it would put it in whatever section came next.
law put_outside_section_is_bad:
  for bad: String
  for pairs: List<&2, T.Kv>
  for done: List<&2, T.Sect>
  for +key: String
  for val: String
  {T.put(T.Toml{bad, "", pairs, done}, key, val)
    == T.Toml{T.first(bad, key ++ " = is outside any section"), "", pairs, done}
    : T.Toml}

# LAW: and a pair written under a header joins that header's section, with the
# key and the value it was written with.
law put_in_section:
  for bad: String
  for +name: String
  for pairs: List<&2, T.Kv>
  for done: List<&2, T.Sect>
  for key: String
  for val: String
  for e: {False{} == String.is_empty(name) : Bool}
  {T.put(T.Toml{bad, name, pairs, done}, key, val)
    == T.Toml{bad, name, T.Kv{key, val} <> pairs, done} : T.Toml}

# LAW: a blank line changes nothing about a document being read. This is the
# first question `line_of` asks and the reason it asks it first: an empty
# string starts with nothing and holds nothing, so every later test would miss
# it and the line would be called neither a header nor a key.
law step_skips_blank:
  for st: T.Toml
  {T.step(st, "") == st : T.Toml}

# LAW: a comment changes nothing about a document being read either. The
# classifier answers a line that opens with `#` before anything is read
# out of it, so a comment may hold anything and still leave the state as
# it was.
law step_skips_comment:
  for st: T.Toml
  for +s: String
  for e: {True{} == String.starts_with(T.trim(s), "#") : Bool}
  {T.step(st, s) == st : T.Toml}

# LAW: a header that never shut is not a section, and the reason is the
# line as it was written. A `[package` with no `]` is not half a section
# and not a key; it is this error.
law unclosed_header:
  for +s: String
  for e: {False{} == String.ends_with(s, "]") : Bool}
  {T.head_of(s, String.ends_with(s, "]"))
    == T.LBad{s ++ " is not a section header"} : T.Line}

# LAW: a document leaves no section open. Whatever the last line did, `parse`
# flushes what it was filling, so `sects` is every section the document held
# and not every section but the last.
law parse_closes_sections:
  for text: String
  {toml.open(T.parse(text)) == "" : String}

# LAW: the sections a parse found are the ones it finished
law sects_is_done:
  for bad: String
  for name: String
  for pairs: List<&2, T.Kv>
  for done: List<&2, T.Sect>
  {T.sects(T.Toml{bad, name, pairs, done}) == done : List<&2, T.Sect>}

# LAW: a header always cuts into at least one segment, so a lookup that reads
# the first of them never reads off the end of the list.
law segments_never_empty:
  for s: String
  {List.is_empty(&2, String, T.segments(s)) == False{} : Bool}

# LAW: a quote is never part of a segment: it toggles the quoting and nothing
# else, so a pair of them cuts nothing and leaves nothing behind. This is half
# of why `packages."0x0a".files` is three segments rather than four.
law segments_quotes_toggle:
  for s: String
  {T.segments(SCon{'"', SCon{'"', s}}) == T.segments(s) : List<&2, String>}

# LAW: a quoted dot is kept as part of the segment being gathered, and
# does not cut. This is the other half of why `packages."0x0a".files` is
# three segments rather than four: the quotes toggle and the dot between
# them is a character of the segment.
law segments_quoted_dot:
  for s: String
  {T.segments(SCon{'"', SCon{'.', SCon{'"', s}}})
    == T.seg.fin(T.seg.walk(String.to_list(s), T.Split{False{}, ['.'], []}))
    : List<&2, String>}

# LAW: a key with nothing in it is never bare, so it is written quoted and
# reads back as the key it was rather than as the start of the next line.
law bare_needs_a_char:
  for +s: String
  for e: {True{} == String.is_empty(s) : Bool}
  {T.bare(s) == False{} : Bool}

# LAW: a key that can be written without quotes is written without them
law key_is_bare_when_it_can:
  for +s: String
  for e: {True{} == T.bare(s) : Bool}
  {T.key(s) == s : String}

# LAW: and one that cannot is quoted, whole. Nothing in between: a key is
# never written half-escaped, which is what makes `quote_strip` reach every
# key a document holds.
law key_is_quoted_when_it_must:
  for +s: String
  for e: {False{} == T.bare(s) : Bool}
  {T.key(s) == T.quote(s) : String}

# LAW: a document of one table is that table's header and then its pairs, with
# nothing before it and no separator after it.
law render_one_table:
  for +n: String
  for ps: List<&2, T.Kv>
  {T.render([T.Sect{n, ps}]) == "[" ++ n ++ "]\n" ++ T.render.pairs(ps)
    : String}

# LAW: the package entry's `parse` is the implementation's
law parse_is_toml:
  for text: String
  {Toml.parse(text) == T.parse(text) : T.Toml}

# LAW: the package entry's `render` is the implementation's
law render_is_toml:
  for ss: List<&2, T.Sect>
  {Toml.render(ss) == T.render(ss) : String}

# LAW: the package entry's `value` is the implementation's
law value_is_toml:
  for pairs: List<&2, T.Kv>
  for +key: String
  {Toml.value(pairs, key) == T.value(pairs, key) : String}

# LAW: the package entry's `sects` is the implementation's
law sects_is_toml:
  for t: T.Toml
  {Toml.sects(t) == T.sects(t) : List<&2, T.Sect>}

# LAW: the package entry's `segments` is the implementation's
law segments_is_toml:
  for s: String
  {Toml.segments(s) == T.segments(s) : List<&2, String>}

# LAW: the package entry's `quote` is the implementation's
law quote_is_toml:
  for +s: String
  {Toml.quote(s) == T.quote(s) : String}

# LAW: the package entry's `key` is the implementation's
law key_is_toml:
  for +s: String
  {Toml.key(s) == T.key(s) : String}

# LAW: `Kv` is the pair of its key and value
law kv_is_pair:
  for +key: String
  for +val: String
  {Toml.Kv(key, val) == T.Kv{key, val} : T.Kv}

# LAW: `Sect` is the section of its name and pairs
law sect_is_section:
  for +name: String
  for pairs: List<&2, T.Kv>
  {Toml.Sect(name, pairs) == T.Sect{name, pairs} : T.Sect}

# LAW: `toml` is the document of its fields
law toml_is_document:
  for bad: String
  for name: String
  for pairs: List<&2, T.Kv>
  for done: List<&2, T.Sect>
  {Toml.toml(bad, name, pairs, done) == T.Toml{bad, name, pairs, done} : T.Toml}
