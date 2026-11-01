# proofs of laws/AtWalksKeys.bend
import Base
import ../main.bend as T
import ../src/eq.bend as Eq
import ../laws/AtWalksKeys.bend as Laws

# laws/AtWalksKeys.bend.

# a miss stays a miss however much of the path is left
def at.step.miss(
  ks: List<&2, String>
) -> {T.at.step(ks, T.Miss{}) == T.Miss{} : T.Hit}:
  match ks:
    case []:
      {==}
    case _nn <> tt:
      at.step.miss(tt)

def Laws.at_empty(_rows):
  {==}

def Laws.at_one(_rows, _k):
  {==}

def Laws.at_table(rows, k, path, sub, next, ks, e):
  Equal.cong(T.Hit, T.Hit, hh => T.at.step(next <> ks, hh), T.get(rows, k),
    T.Found{T.VHead{path, sub}}, e)

def Laws.at_inline(rows, k, sub, next, ks, e):
  Equal.cong(T.Hit, T.Hit, hh => T.at.step(next <> ks, hh), T.get(rows, k),
    T.Found{T.VInl{sub}}, e)

def Laws.at_aot(rows, k, path, sub, next, ks, e):
  Equal.cong(T.Hit, T.Hit, hh => T.at.step(next <> ks, hh), T.get(rows, k),
    T.Found{T.VAot{path, sub}}, e)

def Laws.at_miss(rows, k, next, ks, e):
  Equal.trans(T.Hit, T.at.step(next <> ks, T.get(rows, k)),
    T.at.step(next <> ks, T.Miss{}), T.Miss{},
    Equal.cong(T.Hit, T.Hit, hh => T.at.step(next <> ks, hh), T.get(rows, k),
      T.Miss{}, e),
    at.step.miss(next <> ks))

# a value with no rows gives the next key no rows to be found in
def leaf.miss(
  vv: T.Val,
  nx: String,
  ks: List<&2, String>,
  ff: {Laws.holds_no_rows(vv) == True{} : Bool}
) -> {T.at.step(nx <> ks, T.Found{vv}) == T.Miss{} : T.Hit}:
  match vv:
    case T.VHead{pp, rr}:
      Eq.bit.absurd(&2,
        {T.at.step(nx <> ks, T.Found{T.VHead{pp, rr}}) == T.Miss{} : T.Hit},
        ff)
    case T.VInl{rr}:
      Eq.bit.absurd(&2,
        {T.at.step(nx <> ks, T.Found{T.VInl{rr}}) == T.Miss{} : T.Hit}, ff)
    case T.VAot{pp, rr}:
      Eq.bit.absurd(&2,
        {T.at.step(nx <> ks, T.Found{T.VAot{pp, rr}}) == T.Miss{} : T.Hit},
        ff)
    case T.VStr{_a}:
      at.step.miss(ks)
    case T.VSpan{_a, _b}:
      at.step.miss(ks)
    case T.VInt{_a, _b}:
      at.step.miss(ks)
    case T.VFlo{_a, _b}:
      at.step.miss(ks)
    case T.VBool{_a}:
      at.step.miss(ks)
    case T.VWhen{_a}:
      at.step.miss(ks)
    case T.VArr{_a}:
      at.step.miss(ks)
    case T.VAots{_a, _b}:
      at.step.miss(ks)
    case T.VPair{_a, _b}:
      at.step.miss(ks)

def Laws.at_leaf(rows, k, v, next, ks, e, f):
  Equal.trans(T.Hit, T.at.step(next <> ks, T.get(rows, k)),
    T.at.step(next <> ks, T.Found{v}), T.Miss{},
    Equal.cong(T.Hit, T.Hit, hh => T.at.step(next <> ks, hh), T.get(rows, k),
      T.Found{v}, e),
    leaf.miss(v, next, ks, f))
