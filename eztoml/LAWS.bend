# eztoml: the laws. PROOF.bend proves them.
import Base
import ./value.bend as V
import ./text.bend as Txt
import ./lex.bend as L
import ./parse.bend as P
import ./print.bend as R
import ./main.bend as Toml

# a table answers a key with the value written for it
law lookup:
  for +k: String
  for v: V.Val
  {V.get(V.table(V.pair(k, v, V.nil())), k) == v : V.Val}

# an empty table has no keys
law empty_lookup:
  for k: String
  {V.get(V.empty(), k) == V.miss() : V.Val}

# the first cell of an array is the value written there
law head:
  for v: V.Val
  {V.at(V.array(V.cons(v, V.nil())), 0n) == v : V.Val}

# a string value reads back as the text it was built from
law str_reads:
  for +s: String
  {V.str(V.string(s)) == Some{s} : Maybe<&2, String>}

# an integer value reads back as the digits it was built from
law integer_reads:
  for +s: String
  {V.integer(V.int(s)) == Some{s} : Maybe<&2, String>}

# a float value reads back as the digits it was built from
law float_reads:
  for +s: String
  {V.float(V.num(s)) == Some{s} : Maybe<&2, String>}

# a boolean value reads back as the bit it was built from
law boolean_reads:
  for b: Bool
  {V.boolean(V.flag(b)) == Some{b} : Maybe<&2, Bool>}

# an offset datetime reads back as the text it was built from
law datetime_reads:
  for +s: String
  {V.datetime(V.offset(s)) == Some{s} : Maybe<&2, String>}

# a local datetime reads back as the text it was built from
law local_reads:
  for +s: String
  {V.datetime(V.local(s)) == Some{s} : Maybe<&2, String>}

# a local date reads back as the text it was built from
law day_reads:
  for +s: String
  {V.datetime(V.day(s)) == Some{s} : Maybe<&2, String>}

# a local time reads back as the text it was built from
law time_reads:
  for +s: String
  {V.datetime(V.time(s)) == Some{s} : Maybe<&2, String>}

# quoting nothing is a pair of quotes
law quote_empty:
  for u: Unit
  {Txt.quote("") == "\"\"" : String}

# a header always cuts into at least one segment
law segments_never_empty:
  for s: String
  {List.is_empty(&2, String, Txt.segments(s)) == False{} : Bool}

# a pair of quotes toggles quoting and leaves the segments unchanged
law segments_quotes_toggle:
  for s: String
  {Txt.segments(SCon{'"', SCon{'"', s}}) == Txt.segments(s) : List<&2, String>}

# a quoted dot stays inside the segment being gathered
law segments_quoted_dot:
  for s: String
  {Txt.segments(SCon{'"', SCon{'.', SCon{'"', s}}})
    == Txt.seg.fin(Txt.seg.walk(String.to_list(s), Txt.Split{False{}, ['.'],
      []})) : List<&2, String>}

# a key with nothing in it is never bare
law bare_needs_a_char:
  for +s: String
  for e: {True{} == String.is_empty(s) : Bool}
  {Txt.bare(s) == False{} : Bool}

# a key that can be written without quotes is written without them
law key_is_bare_when_it_can:
  for +s: String
  for e: {True{} == Txt.bare(s) : Bool}
  {Txt.key(s) == s : String}

# a key that cannot be written without quotes is quoted
law key_is_quoted_when_it_must:
  for +s: String
  for e: {False{} == Txt.bare(s) : Bool}
  {Txt.key(s) == Txt.quote(s) : String}

# the tokens of an empty text
law tokens_empty:
  for u: Unit
  {L.tokens("") == [] : List<&2, L.Tok>}

# an empty text is an empty table
law parse_empty:
  for u: Unit
  {P.parse("") == P.Doc{"", V.empty()} : P.Doc}

# an empty table is written as nothing
law render_empty:
  for u: Unit
  {R.render(V.empty()) == "" : String}

# the package entry's `parse` is the implementation's
law parse_is:
  for text: String
  {Toml.parse(text) == P.parse(text) : P.Doc}

# the package entry's `render` is the implementation's
law render_is:
  for v: V.Val
  {Toml.render(v) == R.render(v) : String}

# the package entry's `root` is the table of a document
law root_is:
  for e: String
  for rt: V.Val
  {Toml.root(P.Doc{e, rt}) == rt : V.Val}

# the package entry's `err` is the error of a document
law err_is:
  for e: String
  for rt: V.Val
  {Toml.err(P.Doc{e, rt}) == e : String}

# the package entry's `get` is the implementation's
law get_is:
  for v: V.Val
  for key: String
  {Toml.get(v, key) == V.get(v, key) : V.Val}

# the package entry's `at` is the implementation's
law at_is:
  for v: V.Val
  for n: Nat
  {Toml.at(v, n) == V.at(v, n) : V.Val}

# the package entry's `str` is the implementation's
law str_is:
  for v: V.Val
  {Toml.str(v) == V.str(v) : Maybe<&2, String>}

# the package entry's `integer` is the implementation's
law integer_is:
  for v: V.Val
  {Toml.integer(v) == V.integer(v) : Maybe<&2, String>}

# the package entry's `float` is the implementation's
law float_is:
  for v: V.Val
  {Toml.float(v) == V.float(v) : Maybe<&2, String>}

# the package entry's `boolean` is the implementation's
law boolean_is:
  for v: V.Val
  {Toml.boolean(v) == V.boolean(v) : Maybe<&2, Bool>}

# the package entry's `datetime` is the implementation's
law datetime_is:
  for v: V.Val
  {Toml.datetime(v) == V.datetime(v) : Maybe<&2, String>}

# the package entry's `empty` is the implementation's
law empty_is:
  for u: Unit
  {Toml.empty() == V.empty() : V.Val}

# the package entry's `miss` is the implementation's
law miss_is:
  for u: Unit
  {Toml.miss() == V.miss() : V.Val}

# the package entry's `nil` is the implementation's
law nil_is:
  for u: Unit
  {Toml.nil() == V.nil() : V.Val}

# the package entry's `cons` is the implementation's
law cons_is:
  for head: V.Val
  for tail: V.Val
  {Toml.cons(head, tail) == V.cons(head, tail) : V.Val}

# the package entry's `pair` is the implementation's
law pair_is:
  for +key: String
  for val: V.Val
  for rest: V.Val
  {Toml.pair(key, val, rest) == V.pair(key, val, rest) : V.Val}

# the package entry's `table` is the implementation's
law table_is:
  for pairs: V.Val
  {Toml.table(pairs) == V.table(pairs) : V.Val}

# the package entry's `array` is the implementation's
law array_is:
  for items: V.Val
  {Toml.array(items) == V.array(items) : V.Val}

# the package entry's `string` is the implementation's
law string_is:
  for +s: String
  {Toml.string(s) == V.string(s) : V.Val}

# the package entry's `int` is the implementation's
law int_is:
  for +raw: String
  {Toml.int(raw) == V.int(raw) : V.Val}

# the package entry's `num` is the implementation's
law num_is:
  for +raw: String
  {Toml.num(raw) == V.num(raw) : V.Val}

# the package entry's `flag` is the implementation's
law flag_is:
  for b: Bool
  {Toml.flag(b) == V.flag(b) : V.Val}

# the package entry's `offset` is the implementation's
law offset_is:
  for +raw: String
  {Toml.offset(raw) == V.offset(raw) : V.Val}

# the package entry's `local` is the implementation's
law local_is:
  for +raw: String
  {Toml.local(raw) == V.local(raw) : V.Val}

# the package entry's `day` is the implementation's
law day_is:
  for +raw: String
  {Toml.day(raw) == V.day(raw) : V.Val}

# the package entry's `time` is the implementation's
law time_is:
  for +raw: String
  {Toml.time(raw) == V.time(raw) : V.Val}

# the package entry's `segments` is the implementation's
law segments_is:
  for s: String
  {Toml.segments(s) == Txt.segments(s) : List<&2, String>}

# the package entry's `quote` is the implementation's
law quote_is:
  for +s: String
  {Toml.quote(s) == Txt.quote(s) : String}

# the package entry's `key` is the implementation's
law key_is:
  for +s: String
  {Toml.key(s) == Txt.key(s) : String}
