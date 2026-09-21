# eztoml: the proofs.
import Base
import ./value.bend as V
import ./text.bend as Txt
import ./eq.bend as Eq
import ./LAWS.bend as Laws

# the value written for a key is the value a one-pair table answers with
def Laws.lookup(k, v):
  Equal.cong(Bool, V.Val, b => Bool.pick(V.Val, b, v, V.get.go(V.nil(), k)),
    String.eq(k, k), True{}, Eq.string_eq_self(k))

def Laws.empty_lookup(_k):
  {==}

def Laws.head(_v):
  {==}

def Laws.str_reads(_s):
  {==}

def Laws.integer_reads(_s):
  {==}

def Laws.float_reads(_s):
  {==}

def Laws.boolean_reads(_b):
  {==}

def Laws.datetime_reads(_s):
  {==}

def Laws.local_reads(_s):
  {==}

def Laws.day_reads(_s):
  {==}

def Laws.time_reads(_s):
  {==}

def Laws.quote_empty(_u):
  {==}

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
  for st: Txt.Split
  {List.is_empty(&2, String, Txt.seg.fin(st)) == False{} : Bool}

def segments_never_empty.fin(st):
  match st:
    case Txt.Split{quoted, cur, out}:
      reverse_onto_nonempty(out, Txt.seg.done(cur), [])

def Laws.segments_never_empty(s):
  segments_never_empty.fin(Txt.seg.walk(String.to_list(s),
    Txt.Split{False{}, [], []}))

def Laws.segments_quotes_toggle(_s):
  {==}

def Laws.segments_quoted_dot(_s):
  {==}

def Laws.bare_needs_a_char(s, e):
  %e : {Bool.and(Bool.not(_), Txt.bare.all(String.to_list(s))) == False{}
    : Bool}
  {==}

def Laws.key_is_bare_when_it_can(s, e):
  %e : {Txt.key.pick(_, s, _u => Txt.quote(s)) == s : String}
  {==}

def Laws.key_is_quoted_when_it_must(s, e):
  %e : {Txt.key.pick(_, s, _u => Txt.quote(s)) == Txt.quote(s) : String}
  {==}

def Laws.tokens_empty(_u):
  {==}

def Laws.parse_empty(_u):
  {==}

def Laws.render_empty(_u):
  {==}

def Laws.parse_is(_text):
  {==}

def Laws.render_is(_v):
  {==}

def Laws.root_is(_e, _rt):
  {==}

def Laws.err_is(_e, _rt):
  {==}

def Laws.get_is(_v, _key):
  {==}

def Laws.at_is(_v, _n):
  {==}

def Laws.str_is(_v):
  {==}

def Laws.integer_is(_v):
  {==}

def Laws.float_is(_v):
  {==}

def Laws.boolean_is(_v):
  {==}

def Laws.datetime_is(_v):
  {==}

def Laws.empty_is(_u):
  {==}

def Laws.miss_is(_u):
  {==}

def Laws.nil_is(_u):
  {==}

def Laws.cons_is(_head, _tail):
  {==}

def Laws.pair_is(_key, _val, _rest):
  {==}

def Laws.table_is(_pairs):
  {==}

def Laws.array_is(_items):
  {==}

def Laws.string_is(_s):
  {==}

def Laws.int_is(_raw):
  {==}

def Laws.num_is(_raw):
  {==}

def Laws.flag_is(_b):
  {==}

def Laws.offset_is(_raw):
  {==}

def Laws.local_is(_raw):
  {==}

def Laws.day_is(_raw):
  {==}

def Laws.time_is(_raw):
  {==}

def Laws.segments_is(_s):
  {==}

def Laws.quote_is(_s):
  {==}

def Laws.key_is(_s):
  {==}
