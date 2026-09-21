# Proofs of the eztoml laws.
import Base
import ./toml.bend as T
import ./eq.bend as Eq
import ./LAWS.bend as Laws

# the chars of two strings joined are the chars of each, joined
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

# a string taken apart into chars and put back together is itself
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

# the walk to the end drops the char it was told to drop, and keeps the one it
# was carrying
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

# a char put on the end of a list is the char the back strip takes off
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

def Laws.get_first(name, v, rest):
  Equal.cong(Bool, T.Hit,
    b => T.find.step(b, v, _u => T.rows.find(rest, name)),
    String.eq(name, name), True{}, Eq.string_eq_self(name))

def Laws.value_string(name, text, rest):
  Equal.cong(Bool, String,
    b => T.string(T.hit.val(T.find.step(b, T.VStr{text},
      _u => T.rows.find(rest, name)))),
    String.eq(name, name), True{}, Eq.string_eq_self(name))

# a list reversed onto something is never empty
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

# a finished header walk always has a segment to close
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

def Laws.segments_quotes_toggle(_s):
  {==}

def Laws.segments_quoted_dot(_s):
  {==}

def Laws.bare_needs_a_char(s, e):
  %e : {Bool.and(Bool.not(_), T.bare.all(String.to_list(s))) == False{}
    : Bool}
  {==}

def Laws.key_is_bare_when_it_can(s, e):
  %e : {T.key.go(_, s) == s : String}
  {==}

def Laws.key_is_quoted_when_it_must(s, e):
  %e : {T.key.go(_, s) == T.key.basic(s) : String}
  {==}

def Laws.parse_empty(s, e):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Eq.bit.absurd2(&2, {T.parse(SCon{h, t}) == T.Doc{"", []} : T.Doc}, e)

def Laws.render_empty(_bad):
  {==}

def Laws.string_of(_text):
  {==}

def Laws.digits_of(_sign, _text):
  {==}

def Laws.flag_of(_bit):
  {==}

def Laws.at_one(_rows, _name):
  {==}

def Laws.at_empty(_rows):
  {==}

def Laws.root_rows(_bad, _rows):
  {==}

def Laws.bad_text(_text, _rows):
  {==}

def Laws.str_builds(_text):
  {==}

def Laws.integer_builds(_sign, _text):
  {==}

def Laws.float_builds(_sign, _text):
  {==}

def Laws.boolean_builds(_bit):
  {==}

def Laws.array_builds(_items):
  {==}

def Laws.inline_builds(_rows):
  {==}

def Laws.table_builds(_path, _rows):
  {==}

def Laws.pair_builds(_name, _val):
  {==}

def Laws.parse_is(_text):
  {==}

def Laws.render_is(_doc):
  {==}

def Laws.get_is(_rows, _name):
  {==}

def Laws.at_is(_rows, _path):
  {==}

def Laws.value_is(_rows, _name):
  {==}

def Laws.root_is(_doc):
  {==}

def Laws.bad_is(_doc):
  {==}

def Laws.string_is(_v):
  {==}

def Laws.digits_is(_v):
  {==}

def Laws.flag_is(_v):
  {==}

def Laws.str_is(_text):
  {==}

def Laws.integer_is(_sign, _text):
  {==}

def Laws.float_is(_sign, _text):
  {==}

def Laws.boolean_is(_bit):
  {==}

def Laws.array_is(_items):
  {==}

def Laws.inline_is(_rows):
  {==}

def Laws.table_is(_path, _rows):
  {==}

def Laws.pair_is(_name, _val):
  {==}

def Laws.segments_is(_s):
  {==}

def Laws.quote_is(_s):
  {==}

def Laws.key_is(_s):
  {==}
