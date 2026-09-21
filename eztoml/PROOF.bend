# eztoml: the proofs. `bend PROOF.bend` is the gate.
import Base
import ./toml.bend as T
import ./eq.bend as Eq
import ./LAWS.bend as Laws

# LAW: the chars of two strings joined are the chars of each, joined
law to_list_append:
  for a: String
  for +b: String
  {String.to_list(String.append(a, b))
    == List.append(&2, Char, String.to_list(a), String.to_list(b))
    : List<&2, Char>}

def to_list_append(a, b):
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.cong(List<&2, Char>, List<&2, Char>, y => h <> y,
        String.to_list(String.append(t, b)),
        List.append(&2, Char, String.to_list(t), String.to_list(b)),
        to_list_append(t, b))

# LAW: a string taken apart into chars and put back together is itself
law from_to:
  for +s: String
  {String.from_list(String.to_list(s)) == s : String}

def from_to(s):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.cong(String, String, y => SCon{h, y},
        String.from_list(String.to_list(t)), t, from_to(t))

# LAW: the walk to the end drops the char it was told to drop, and keeps the
# one it was carrying
law back_snoc.go:
  for t: List<&2, Char>
  for +h: Char
  for +c: Char
  {T.strip.back.go(List.append(&2, Char, t, [c]), h, c) == h <> t
    : List<&2, Char>}

def back_snoc.go(t, h, c):
  match t:
    case []:
      Equal.cong(Bool, List<&2, Char>, x => h <> T.strip.cut(x, c, []),
        Char.is_eq(c, c), True{}, Eq.char_eq_self(c))
    case +h2 <> t2:
      Equal.cong(List<&2, Char>, List<&2, Char>, y => h <> y,
        T.strip.back.go(List.append(&2, Char, t2, [c]), h2, c), h2 <> t2,
        back_snoc.go(t2, h2, c))

# LAW: a char put on the end of a list is the char the back strip takes off
law back_snoc:
  for cs: List<&2, Char>
  for +c: Char
  {T.strip.back(List.append(&2, Char, cs, [c]), c) == cs : List<&2, Char>}

def back_snoc(cs, c):
  match cs:
    case []:
      Equal.cong(Bool, List<&2, Char>, x => T.strip.cut(x, c, []),
        Char.is_eq(c, c), True{}, Eq.char_eq_self(c))
    case +h <> t:
      back_snoc.go(t, h, c)

def Laws.quote_strip(s):
  Equal.trans(String,
    T.strip(T.quote(s), '"', '"'),
    String.from_list(String.to_list(s)),
    s,
    Equal.trans(String,
      T.strip(T.quote(s), '"', '"'),
      String.from_list(T.strip.back(
        List.append(&2, Char, String.to_list(s), ['"']), '"')),
      String.from_list(String.to_list(s)),
      Equal.cong(List<&2, Char>, String,
        y => String.from_list(T.strip.back(y, '"')),
        String.to_list(String.append(s, "\"")),
        List.append(&2, Char, String.to_list(s), ['"']),
        to_list_append(s, "\"")),
      Equal.cong(List<&2, Char>, String, y => String.from_list(y),
        T.strip.back(List.append(&2, Char, String.to_list(s), ['"']), '"'),
        String.to_list(s),
        back_snoc(String.to_list(s), '"'))),
    from_to(s))

def Laws.value_first(k, v, ps):
  Equal.cong(Bool, String, b => Bool.pick(String, b, v, T.value(ps, k)),
    String.eq(k, k), True{}, Eq.string_eq_self(k))

# The agreement laws, which say that the rewrites for cost did not change
# an answer. Each is the same argument: a `match` may not scrutinise a
# computed value, so the branch is lifted into a parameter and the law is
# then applied to the branch the code computes. The classifier takes four
# of them, one a level, in the order the cascade asks its questions.

# LAW: the last question, with the branch given as a parameter
law line_of_agrees.pair:
  for +s: String
  for p: Bool
  {Bool.pick(T.Line, p, T.pair_of(String.split(s, '=')),
    T.LBad{s ++ " is neither a section header nor a key"})
    == T.line_of.pair(p, s) : T.Line}

def line_of_agrees.pair(_s, p):
  match p:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: the section header, with the pair question's agreement alongside
law line_of_agrees.head:
  for +s: String
  for p: Bool
  for ih: {Bool.pick(T.Line, String.contains(s, "="),
    T.pair_of(String.split(s, '=')),
    T.LBad{s ++ " is neither a section header nor a key"})
    == T.line_of.pair(String.contains(s, "="), s) : T.Line}
  {Bool.pick(T.Line, p, T.head_of(s, String.ends_with(s, "]")),
    Bool.pick(T.Line, String.contains(s, "="),
      T.pair_of(String.split(s, '=')),
      T.LBad{s ++ " is neither a section header nor a key"}))
    == T.line_of.head(p, s) : T.Line}

def line_of_agrees.head(_s, p, ih):
  match p:
    case True{}:
      {==}
    case False{}:
      ih

# LAW: the comment, with the header question's agreement alongside
law line_of_agrees.comment:
  for +s: String
  for p: Bool
  for ih: {Bool.pick(T.Line, String.starts_with(s, "["),
    T.head_of(s, String.ends_with(s, "]")),
    Bool.pick(T.Line, String.contains(s, "="),
      T.pair_of(String.split(s, '=')),
      T.LBad{s ++ " is neither a section header nor a key"}))
    == T.line_of.head(String.starts_with(s, "["), s) : T.Line}
  {Bool.pick(T.Line, p, T.LSkip{},
    Bool.pick(T.Line, String.starts_with(s, "["),
      T.head_of(s, String.ends_with(s, "]")),
      Bool.pick(T.Line, String.contains(s, "="),
        T.pair_of(String.split(s, '=')),
        T.LBad{s ++ " is neither a section header nor a key"})))
    == T.line_of.comment(p, s) : T.Line}

def line_of_agrees.comment(_s, p, ih):
  match p:
    case True{}:
      {==}
    case False{}:
      ih

# LAW: the blank line, with the comment question's agreement alongside. This
# is the arm that matters most: a cascade without it would fall through to
# calling an empty line neither a header nor a key.
law line_of_agrees.blank:
  for +s: String
  for p: Bool
  for ih: {Bool.pick(T.Line, String.starts_with(s, "#"), T.LSkip{},
    Bool.pick(T.Line, String.starts_with(s, "["),
      T.head_of(s, String.ends_with(s, "]")),
      Bool.pick(T.Line, String.contains(s, "="),
        T.pair_of(String.split(s, '=')),
        T.LBad{s ++ " is neither a section header nor a key"})))
    == T.line_of.comment(String.starts_with(s, "#"), s) : T.Line}
  {Bool.pick(T.Line, p, T.LSkip{},
    Bool.pick(T.Line, String.starts_with(s, "#"), T.LSkip{},
      Bool.pick(T.Line, String.starts_with(s, "["),
        T.head_of(s, String.ends_with(s, "]")),
        Bool.pick(T.Line, String.contains(s, "="),
          T.pair_of(String.split(s, '=')),
          T.LBad{s ++ " is neither a section header nor a key"}))))
    == T.line_of.blank(p, s) : T.Line}

def line_of_agrees.blank(_s, p, ih):
  match p:
    case True{}:
      {==}
    case False{}:
      ih

def Laws.line_of_agrees(s):
  line_of_agrees.blank(s, String.is_empty(s),
    line_of_agrees.comment(s, String.starts_with(s, "#"),
      line_of_agrees.head(s, String.starts_with(s, "["),
        line_of_agrees.pair(s, String.contains(s, "=")))))

# LAW: one step of the bare-key walk, with the head's answer given as a
# parameter and the rest of the walk's agreement alongside
law bare_all_agrees.arm:
  for t: List<&2, Char>
  for p: Bool
  for ih: {Laws.old.bare.all(t) == T.bare.all(t) : Bool}
  {Bool.and(p, Laws.old.bare.all(t))
    == T.bare.all.step(p, _u => T.bare.all(t)) : Bool}

def bare_all_agrees.arm(_t, p, ih):
  match p:
    case True{}:
      ih
    case False{}:
      {==}

def Laws.bare_all_agrees(cs):
  match cs:
    case []:
      {==}
    case +h <> +t:
      bare_all_agrees.arm(t, T.bare.at(h), Laws.bare_all_agrees(t))

# LAW: a list reversed onto something is never empty
law reverse_onto_nonempty:
  for ys: List<&2, String>
  for x: String
  for xs: List<&2, String>
  {List.is_empty(&2, String, List.reverse.go(&2, String, ys, x <> xs))
    == False{} : Bool}

def reverse_onto_nonempty(ys, x, xs):
  match ys:
    case []:
      {==}
    case +y <> +t:
      reverse_onto_nonempty(t, y, x <> xs)

# A leading space is dropped by the first pass and never reaches the second,
# so both passes compute down to the passes over the rest of the line.
def Laws.trim_drops_leading_space(_s):
  {==}

def Laws.first_error_wins(bad, why, e):
  %e : {Bool.pick(String, _, why, bad) == bad : String}
  {==}

def Laws.flush_skips_unnamed(_pairs, _done):
  {==}

def Laws.flush_keeps_named(name, pairs, done, e):
  %e : {T.flush.put(_, name, pairs, done)
    == T.Sect{name, List.reverse(&2, T.Kv, pairs)} <> done : List<&2, T.Sect>}
  {==}

def Laws.put_outside_section_is_bad(_bad, _pairs, _done, _key, _val):
  {==}

def Laws.put_in_section(bad, name, pairs, done, key, val, e):
  %e : {T.put.go(_, bad, name, pairs, done, key, val)
    == T.Toml{bad, name, T.Kv{key, val} <> pairs, done} : T.Toml}
  {==}

# A blank line trims to a blank line, which `line_of` answers on its first
# question; the state is then handed back field for field, which is the state
# only once it is matched.
def Laws.step_skips_blank(st):
  match st:
    case T.Toml{bad, name, pairs, done}:
      {==}

# LAW: a line that opens with `#` is a skip, whatever it holds. An empty
# line is a skip too, so the emptiness question does not matter here.
law line_of_comment:
  for +s: String
  for e: {True{} == String.starts_with(s, "#") : Bool}
  {T.line_of(s) == T.LSkip{} : T.Line}

# LAW: the same, with the emptiness question given as a parameter
law line_of_comment.at:
  for +s: String
  for empty: Bool
  for e: {True{} == String.starts_with(s, "#") : Bool}
  {T.line_of.blank(empty, s) == T.LSkip{} : T.Line}

def line_of_comment.at(s, empty, e):
  match empty:
    case True{}:
      {==}
    case False{}:
      Equal.trans(T.Line,
        T.line_of.comment(String.starts_with(s, "#"), s),
        T.line_of.comment(True{}, s),
        T.LSkip{},
        Equal.cong(Bool, T.Line, b => T.line_of.comment(b, s),
          String.starts_with(s, "#"), True{},
          Equal.sym(Bool, True{}, String.starts_with(s, "#"), e)),
        {==})

def line_of_comment(s, e):
  line_of_comment.at(s, String.is_empty(s), e)

# A comment trims to a comment; the classifier skips it and the state
# comes back field for field, the way a blank line does.
def Laws.step_skips_comment(st, s, e):
  match st:
    case T.Toml{bad, name, pairs, done}:
      Equal.cong(T.Line, T.Toml,
        line => T.step.go(T.Toml{bad, name, pairs, done}, line),
        T.line_of(T.trim(s)), T.LSkip{}, line_of_comment(T.trim(s), e))

def Laws.unclosed_header(s, e):
  %e : {T.head_of(s, _) == T.LBad{s ++ " is not a section header"} : T.Line}
  {==}

# LAW: whatever a walk left open, the flush at the end closes
law parse_closes_sections.fin:
  for r: T.Toml
  {Laws.toml.open(T.parse.fin(r)) == "" : String}

def parse_closes_sections.fin(r):
  match r:
    case T.Toml{bad, name, pairs, done}:
      {==}

def Laws.parse_closes_sections(text):
  parse_closes_sections.fin(
    T.parse.walk(String.lines(text), T.Toml{"", "", [], []}))

def Laws.sects_is_done(_bad, _name, _pairs, _done):
  {==}

# LAW: a finished header walk always has a segment to close
law segments_never_empty.fin:
  for st: T.Split
  {List.is_empty(&2, String, T.seg.fin(st)) == False{} : Bool}

def segments_never_empty.fin(st):
  match st:
    case T.Split{quoted, cur, out}:
      reverse_onto_nonempty(out, T.seg.done(cur), [])

def Laws.segments_never_empty(s):
  segments_never_empty.fin(
    T.seg.walk(String.to_list(s), T.Split{False{}, [], []}))

# A quote is answered by `seg.sym` on the character alone, and the two
# togglings cancel before the rest of the header is read.
def Laws.segments_quotes_toggle(_s):
  {==}

# A quote, a dot, a quote: the quotes toggle and the dot is kept, so the
# rest of the header is read with that one character already gathered.
def Laws.segments_quoted_dot(_s):
  {==}

def Laws.bare_needs_a_char(s, e):
  %e : {Bool.and(Bool.not(_), T.bare.all(String.to_list(s))) == False{}
    : Bool}
  {==}

def Laws.key_is_bare_when_it_can(s, e):
  %e : {Bool.pick(String, _, s, T.quote(s)) == s : String}
  {==}

def Laws.key_is_quoted_when_it_must(s, e):
  %e : {Bool.pick(String, _, s, T.quote(s)) == T.quote(s) : String}
  {==}

# One table is joined with nothing after it, so the separator is never
# written.
def Laws.render_one_table(_n, _ps):
  {==}

def Laws.parse_is_toml(_text):
  {==}

def Laws.render_is_toml(_ss):
  {==}

def Laws.value_is_toml(_pairs, _key):
  {==}

def Laws.sects_is_toml(_t):
  {==}

def Laws.segments_is_toml(_s):
  {==}

def Laws.quote_is_toml(_s):
  {==}

def Laws.key_is_toml(_s):
  {==}

def Laws.kv_is_pair(_key, _val):
  {==}

def Laws.sect_is_section(_name, _pairs):
  {==}

def Laws.toml_is_document(_bad, _name, _pairs, _done):
  {==}
