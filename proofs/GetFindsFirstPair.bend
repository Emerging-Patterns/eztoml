# proofs of laws/GetFindsFirstPair.bend
import Base
import ../main.bend as T
import ../src/eq.bend as Eq
import ../laws/GetFindsFirstPair.bend as Laws
import ../laws/defs/PairPresence.bend as D1
import ./lemmas/PickAndDigitSteps.bend as M1
import ./lemmas/StringEqualsItself.bend as M2

# a pair whose name is not k is passed over
def get.skip(
  +nn: String,
  -vv: T.Val,
  -rest: List<&2, T.Val>,
  +kk: String,
  ee: {String.eq(nn, kk) == False{} : Bool}
) -> {T.get(T.VPair{nn, vv} <> rest, kk) == T.get(rest, kk) : T.Hit}:
  Equal.cong(Bool, T.Hit, b => T.find.step(b, vv, _u => T.rows.find(rest, kk)),
    T.str.eq(nn, kk), False{},
    Equal.trans(Bool, T.str.eq(nn, kk), String.eq(nn, kk), False{},
      M1.str.eq.agree(nn, kk), ee))

def Laws.get_skips_other_name(n, v, rest, k, e):
  get.skip(n, v, rest, k, e)

def Laws.get_skips_non_pair(x, rest, k, e):
  match x:
    case T.VPair{nn, vv}:
      Eq.bit.absurd2(&2,
        {T.get(T.VPair{nn, vv} <> rest, k) == T.get(rest, k) : T.Hit}, e)
    case T.VStr{_a}:
      {==}
    case T.VSpan{_a, _b}:
      {==}
    case T.VInt{_a, _b}:
      {==}
    case T.VFlo{_a, _b}:
      {==}
    case T.VBool{_a}:
      {==}
    case T.VWhen{_a}:
      {==}
    case T.VArr{_a}:
      {==}
    case T.VInl{_a}:
      {==}
    case T.VHead{_a, _b}:
      {==}
    case T.VAot{_a, _b}:
      {==}
    case T.VAots{_a, _b}:
      {==}

# by induction on the rows before the pair: a pair there has another name,
# and anything else is passed over
def Laws.get_finds_first(pre, k, v, post, e):
  match pre:
    case []:
      Laws.get_first(k, v, post)
    case T.VPair{+nn, +vv} <> +tt:
      Equal.trans(T.Hit,
        T.get(T.VPair{nn, vv}
          <> List.append(&2, T.Val, tt, T.VPair{k, v} <> post), k),
        T.get(List.append(&2, T.Val, tt, T.VPair{k, v} <> post), k),
        T.Found{v},
        get.skip(nn, vv, List.append(&2, T.Val, tt, T.VPair{k, v} <> post), k,
          Eq.or.false_left(String.eq(nn, k), D1.has_pair(tt, k), e)),
        Laws.get_finds_first(tt, k, v, post,
          Eq.or.false_right(String.eq(nn, k), D1.has_pair(tt, k), e)))
    case T.VStr{_a} <> tt:
      Laws.get_finds_first(tt, k, v, post, e)
    case T.VSpan{_a, _b} <> tt:
      Laws.get_finds_first(tt, k, v, post, e)
    case T.VInt{_a, _b} <> tt:
      Laws.get_finds_first(tt, k, v, post, e)
    case T.VFlo{_a, _b} <> tt:
      Laws.get_finds_first(tt, k, v, post, e)
    case T.VBool{_a} <> tt:
      Laws.get_finds_first(tt, k, v, post, e)
    case T.VWhen{_a} <> tt:
      Laws.get_finds_first(tt, k, v, post, e)
    case T.VArr{_a} <> tt:
      Laws.get_finds_first(tt, k, v, post, e)
    case T.VInl{_a} <> tt:
      Laws.get_finds_first(tt, k, v, post, e)
    case T.VHead{_a, _b} <> tt:
      Laws.get_finds_first(tt, k, v, post, e)
    case T.VAot{_a, _b} <> tt:
      Laws.get_finds_first(tt, k, v, post, e)
    case T.VAots{_a, _b} <> tt:
      Laws.get_finds_first(tt, k, v, post, e)

# by induction on the rows: every pair has another name, and anything else
# is passed over
def Laws.get_misses(rows, k, e):
  match rows:
    case []:
      {==}
    case T.VPair{+nn, +vv} <> +tt:
      Equal.trans(T.Hit, T.get(T.VPair{nn, vv} <> tt, k), T.get(tt, k),
        T.Miss{},
        get.skip(nn, vv, tt, k,
          Eq.or.false_left(String.eq(nn, k), D1.has_pair(tt, k), e)),
        Laws.get_misses(tt, k,
          Eq.or.false_right(String.eq(nn, k), D1.has_pair(tt, k), e)))
    case T.VStr{_a} <> tt:
      Laws.get_misses(tt, k, e)
    case T.VSpan{_a, _b} <> tt:
      Laws.get_misses(tt, k, e)
    case T.VInt{_a, _b} <> tt:
      Laws.get_misses(tt, k, e)
    case T.VFlo{_a, _b} <> tt:
      Laws.get_misses(tt, k, e)
    case T.VBool{_a} <> tt:
      Laws.get_misses(tt, k, e)
    case T.VWhen{_a} <> tt:
      Laws.get_misses(tt, k, e)
    case T.VArr{_a} <> tt:
      Laws.get_misses(tt, k, e)
    case T.VInl{_a} <> tt:
      Laws.get_misses(tt, k, e)
    case T.VHead{_a, _b} <> tt:
      Laws.get_misses(tt, k, e)
    case T.VAot{_a, _b} <> tt:
      Laws.get_misses(tt, k, e)
    case T.VAots{_a, _b} <> tt:
      Laws.get_misses(tt, k, e)
