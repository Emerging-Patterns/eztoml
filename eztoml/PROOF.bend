# Proofs of the eztoml laws.
import Base
import ./main.bend as T
import ./eq.bend as Eq
import ./LAWS.bend as Laws

def Laws.get_first(name, v, rest):
  Equal.cong(Bool, T.Hit,
    b => T.find.step(b, v, _u => T.rows.find(rest, name)),
    String.eq(name, name), True{}, Eq.string_eq_self(name))

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
