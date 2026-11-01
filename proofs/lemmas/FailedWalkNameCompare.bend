# a failed walk changes nothing, and the code's name comparison is str.eq
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/DefinesEachTableOnce.bend as L1

# laws/GetFindsFirstPair.bend. The code compares names with its own `str.eq`, and the laws
# with Base's `String.eq`; the first lemma says they always agree.

# a mismatch ends str.eq's walk with False whatever is left
def str.eq.step.false(
  aa: String,
  bb: String
) -> {T.str.eq.step(aa, bb, False{}) == False{} : Bool}:
  match aa bb:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{_h, _t}:
      {==}
    case SCon{_h, _t} SNil{}:
      {==}
    case SCon{_x, _xt} SCon{_y, _yt}:
      {==}

# laws/DefinesEachTableOnce.bend, each element of an array of tables its own scope. That a path
# is no longer defined turns on str.eq answering True only for one string.

# a step of str.eq that answered True was handed True
def str.eq.step.true(
  aa: String,
  bb: String,
  same: Bool,
  ee: {T.str.eq.step(aa, bb, same) == True{} : Bool}
) -> {same == True{} : Bool}:
  match same:
    case True{}:
      {==}
    case False{}:
      Eq.bit.absurd(&2, {False{} == True{} : Bool},
        Equal.trans(Bool, False{}, T.str.eq.step(aa, bb, False{}), True{},
          Equal.sym(Bool, T.str.eq.step(aa, bb, False{}), False{},
            str.eq.step.false(aa, bb)),
          ee))

# and the rest of the walk answered True too
def str.eq.step.rest(
  aa: String,
  bb: String,
  same: Bool,
  ee: {T.str.eq.step(aa, bb, same) == True{} : Bool}
) -> {T.str.eq(aa, bb) == True{} : Bool}:
  match same:
    case True{}:
      ee
    case False{}:
      Eq.bit.absurd(&2, {T.str.eq(aa, bb) == True{} : Bool},
        Equal.trans(Bool, False{}, T.str.eq.step(aa, bb, False{}), True{},
          Equal.sym(Bool, T.str.eq.step(aa, bb, False{}), False{},
            str.eq.step.false(aa, bb)),
          ee))

# two strings str.eq calls equal are one string
def str.eq.true(
  aa: String,
  bb: String,
  +ee: {T.str.eq(aa, bb) == True{} : Bool}
) -> {aa == bb : String}:
  match aa bb:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{hh, tt}:
      Eq.bit.absurd(&2, {SNil{} == SCon{hh, tt} : String}, ee)
    case SCon{hh, tt} SNil{}:
      Eq.bit.absurd(&2, {SCon{hh, tt} == SNil{} : String}, ee)
    case SCon{+xh, +xt} SCon{+yh, +yt}:
      Equal.trans(String, SCon{xh, xt}, SCon{yh, xt}, SCon{yh, yt},
        Equal.cong(Char, String, cc => SCon{cc, xt}, xh, yh,
          Eq.char_eq_true(xh, yh, str.eq.step.true(xt, yt, Char.is_eq(xh, yh), ee))),
        Equal.cong(String, String, ss => SCon{yh, ss}, xt, yt,
          str.eq.true(xt, yt, str.eq.step.rest(xt, yt, Char.is_eq(xh, yh), ee))))

# a walk that starts with an error ends with the rows, the error and the
# recorded definitions it started with
def failed.Goal(
  path: List<&2, String>,
  +rows: List<&2, T.Val>,
  +job: T.Job,
  +bad: String,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +skip: U32
) -> Type:
  {T.tree.walk(path, T.Tw{rows, job, [], bad, pre, heads, inl}, skip) == T.End{rows, bad, heads}
    : T.End}

# a failed walk past one more segment: the step changes nothing, and neither
# does the rest of the walk
def failed.more(
  rest: List<&2, String>,
  +name: String,
  +rows: List<&2, T.Val>,
  +job: T.Job,
  +bad: String,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +skip: U32,
  eb: {String.is_empty(bad) == False{} : Bool},
  ih: failed.Goal(rest, rows, job, bad, pre, heads, inl, T.path.dec(skip))
) -> failed.Goal(name <> rest, rows, job, bad, pre, heads, inl, skip):
  match rest:
    case []:
      Equal.cong(Bool, T.End, bb => T.tree.leaf.bad(bb, name, rows, job, [], bad, pre, heads),
        String.is_empty(bad), False{}, eb)
    case +r <> +rr:
      Equal.trans(T.End,
        T.tree.walk(r <> rr, T.tree.sub.bad(String.is_empty(bad), name, rows, job, [], bad, pre, heads,
          inl, U32.is_zero(skip)), T.path.dec(skip)),
        T.tree.walk(r <> rr, T.Tw{rows, job, [], bad, pre, heads, inl}, T.path.dec(skip)),
        T.End{rows, bad, heads},
        Equal.cong(Bool, T.End,
          bb => T.tree.walk(r <> rr, T.tree.sub.bad(bb, name, rows, job, [], bad, pre, heads, inl,
            U32.is_zero(skip)), T.path.dec(skip)),
          String.is_empty(bad), False{}, eb),
        ih)

# by induction on the path
def L1.failed_walk_changes_nothing(path, rows, job, bad, pre, heads, inl, skip, eb):
  match path:
    case []:
      Equal.cong(Bool, T.End, bb => T.End{rows, T.err.first.go(bb, bad, "empty key"), heads},
        String.is_empty(bad), False{}, eb)
    case name <> +rest:
      failed.more(rest, name, rows, job, bad, pre, heads, inl, skip, eb,
        L1.failed_walk_changes_nothing(rest, rows, job, bad, pre, heads, inl, T.path.dec(skip), eb))
