# proofs of laws/SameSwap.bend
import Base
import ../main.bend as T
import ../src/eq.bend as Eq
import ../laws/SameSwap.bend as Laws
import ../laws/defs/DocumentSameness.bend as D1
import ./lemmas/PickAndDigitSteps.bend as M1
import ./lemmas/PrefixAndTake.bend as M2
import ./lemmas/ValueSelfEquality.bend as M3

# Order. A row matches itself wherever it stands, so rows that differ only by
# a swap of two pairs of different names match.

# every value of the front of some rows matches itself
def selfs.pre(
  pre: List<&2, T.Val>,
  +zz: List<&2, T.Val>,
  +ee: {M1.selfs(List.append(&2, T.Val, pre, zz)) == True{} : Bool}
) -> {M1.selfs(pre) == True{} : Bool}:
  match pre:
    case []:
      {==}
    case +hh <> +pp:
      M2.and.tt(D1.same.go(hh <> [], hh <> []), M1.selfs(pp),
        Eq.and.left(D1.same.go(hh <> [], hh <> []), M1.selfs(List.append(&2, T.Val, pp, zz)), ee),
        selfs.pre(pp, zz, Eq.and.right(D1.same.go(hh <> [], hh <> []), M1.selfs(List.append(&2, T.Val, pp, zz)), ee)))

# and of the back
def selfs.suf(
  pre: List<&2, T.Val>,
  +zz: List<&2, T.Val>,
  ee: {M1.selfs(List.append(&2, T.Val, pre, zz)) == True{} : Bool}
) -> {M1.selfs(zz) == True{} : Bool}:
  match pre:
    case []:
      ee
    case +hh <> +pp:
      selfs.suf(pp, zz, Eq.and.right(D1.same.go(hh <> [], hh <> []), M1.selfs(List.append(&2, T.Val, pp, zz)), ee))

# a pair of another name in front is kept, and the pair behind it picked
def pick.skip(
  +nx: String,
  +vx: T.Val,
  +ny: String,
  +vy: T.Val,
  +post: List<&2, T.Val>,
  ne: {String.eq(ny, nx) == False{} : Bool}
) -> {D1.pick(T.VPair{ny, vy} <> T.VPair{nx, vx} <> post, nx) == D1.Picked{vx, T.VPair{ny, vy} <> post}
  : D1.Pick}:
  Equal.trans(D1.Pick, D1.pick(T.VPair{ny, vy} <> T.VPair{nx, vx} <> post, nx),
    D1.pick.cons(T.VPair{ny, vy}, D1.pick(T.VPair{nx, vx} <> post, nx)),
    D1.Picked{vx, T.VPair{ny, vy} <> post},
    Equal.cong(Bool, D1.Pick,
      bb => D1.pick.step(bb, ny, vy, T.VPair{nx, vx} <> post, _u => D1.pick(T.VPair{nx, vx} <> post, nx)),
      String.eq(ny, nx), False{}, ne),
    Equal.cong(D1.Pick, D1.Pick, pp => D1.pick.cons(T.VPair{ny, vy}, pp),
      D1.pick(T.VPair{nx, vx} <> post, nx), D1.Picked{vx, post}, M1.pick.self(nx, vx, post)))

# either order of the two pairs picks the first one the same
def pick.swap(
  +nx: String,
  +vx: T.Val,
  +ny: String,
  +vy: T.Val,
  +post: List<&2, T.Val>,
  ne: {String.eq(ny, nx) == False{} : Bool}
) -> {D1.pick(T.VPair{ny, vy} <> T.VPair{nx, vx} <> post, nx)
  == D1.pick(T.VPair{nx, vx} <> T.VPair{ny, vy} <> post, nx) : D1.Pick}:
  Equal.trans(D1.Pick, D1.pick(T.VPair{ny, vy} <> T.VPair{nx, vx} <> post, nx),
    D1.Picked{vx, T.VPair{ny, vy} <> post}, D1.pick(T.VPair{nx, vx} <> T.VPair{ny, vy} <> post, nx),
    pick.skip(nx, vx, ny, vy, post, ne),
    Equal.sym(D1.Pick, D1.pick(T.VPair{nx, vx} <> T.VPair{ny, vy} <> post, nx),
      D1.Picked{vx, T.VPair{ny, vy} <> post}, M1.pick.self(nx, vx, T.VPair{ny, vy} <> post)))

# Base's string equality answers the same either way round
def string.sym(+aa: String, +bb: String) -> {String.eq(aa, bb) == String.eq(bb, aa) : Bool}:
  Equal.trans(Bool, String.eq(aa, bb), T.str.eq(aa, bb), String.eq(bb, aa),
    Equal.sym(Bool, T.str.eq(aa, bb), String.eq(aa, bb), M1.str.eq.agree(aa, bb)),
    Equal.trans(Bool, T.str.eq(aa, bb), T.str.eq(bb, aa), String.eq(bb, aa),
      M3.str.eq.sym(aa, bb, True{}), M1.str.eq.agree(bb, aa)))

# the two orders of two pairs of different names match, after a front that
# matches itself
def swap.fin(
  +e: String,
  +pre: List<&2, T.Val>,
  +nx: String,
  +vx: T.Val,
  +ny: String,
  +vy: T.Val,
  +post: List<&2, T.Val>,
  +ne: {String.eq(nx, ny) == False{} : Bool},
  +sp: {M1.selfs(pre) == True{} : Bool},
  +sx: {M1.selfs(T.VPair{nx, vx} <> T.VPair{ny, vy} <> post) == True{} : Bool}
) -> {D1.same(T.Doc{e, List.append(&2, T.Val, pre, T.VPair{nx, vx} <> T.VPair{ny, vy} <> post)},
  T.Doc{e, List.append(&2, T.Val, pre, T.VPair{ny, vy} <> T.VPair{nx, vx} <> post)}) == True{} : Bool}:
  M2.and.tt(
    D1.same.go(List.append(&2, T.Val, pre, T.VPair{nx, vx} <> T.VPair{ny, vy} <> post),
      List.append(&2, T.Val, pre, T.VPair{ny, vy} <> T.VPair{nx, vx} <> post)),
    D1.same.go(List.append(&2, T.Val, pre, T.VPair{ny, vy} <> T.VPair{nx, vx} <> post),
      List.append(&2, T.Val, pre, T.VPair{nx, vx} <> T.VPair{ny, vy} <> post)),
    Equal.trans(Bool,
      D1.same.go(List.append(&2, T.Val, pre, T.VPair{nx, vx} <> T.VPair{ny, vy} <> post),
        List.append(&2, T.Val, pre, T.VPair{ny, vy} <> T.VPair{nx, vx} <> post)),
      D1.same.go(T.VPair{nx, vx} <> T.VPair{ny, vy} <> post, T.VPair{ny, vy} <> T.VPair{nx, vx} <> post),
      True{},
      M1.cancel(pre, T.VPair{nx, vx} <> T.VPair{ny, vy} <> post, T.VPair{ny, vy} <> T.VPair{nx, vx} <> post, sp),
      Equal.trans(Bool,
        D1.same.go(T.VPair{nx, vx} <> T.VPair{ny, vy} <> post, T.VPair{ny, vy} <> T.VPair{nx, vx} <> post),
        D1.same.go(T.VPair{nx, vx} <> T.VPair{ny, vy} <> post, T.VPair{nx, vx} <> T.VPair{ny, vy} <> post),
        True{},
        M1.pick.same(nx, vx, T.VPair{ny, vy} <> post, T.VPair{ny, vy} <> T.VPair{nx, vx} <> post,
          T.VPair{nx, vx} <> T.VPair{ny, vy} <> post,
          pick.swap(nx, vx, ny, vy, post,
            Equal.trans(Bool, String.eq(ny, nx), String.eq(nx, ny), False{}, string.sym(ny, nx), ne))),
        M3.refl.rows(T.VPair{nx, vx} <> T.VPair{ny, vy} <> post, sx))),
    Equal.trans(Bool,
      D1.same.go(List.append(&2, T.Val, pre, T.VPair{ny, vy} <> T.VPair{nx, vx} <> post),
        List.append(&2, T.Val, pre, T.VPair{nx, vx} <> T.VPair{ny, vy} <> post)),
      D1.same.go(T.VPair{ny, vy} <> T.VPair{nx, vx} <> post, T.VPair{nx, vx} <> T.VPair{ny, vy} <> post),
      True{},
      M1.cancel(pre, T.VPair{ny, vy} <> T.VPair{nx, vx} <> post, T.VPair{nx, vx} <> T.VPair{ny, vy} <> post, sp),
      Equal.trans(Bool,
        D1.same.go(T.VPair{ny, vy} <> T.VPair{nx, vx} <> post, T.VPair{nx, vx} <> T.VPair{ny, vy} <> post),
        D1.same.go(T.VPair{ny, vy} <> T.VPair{nx, vx} <> post, T.VPair{ny, vy} <> T.VPair{nx, vx} <> post),
        True{},
        M1.pick.same(ny, vy, T.VPair{nx, vx} <> post, T.VPair{nx, vx} <> T.VPair{ny, vy} <> post,
          T.VPair{ny, vy} <> T.VPair{nx, vx} <> post, pick.swap(ny, vy, nx, vx, post, ne)),
        M3.refl.rows(T.VPair{ny, vy} <> T.VPair{nx, vx} <> post,
          M2.and.tt(D1.same.go(T.VPair{ny, vy} <> [], T.VPair{ny, vy} <> []),
            Bool.and(D1.same.go(T.VPair{nx, vx} <> [], T.VPair{nx, vx} <> []), M1.selfs(post)),
            Eq.and.left(D1.same.go(T.VPair{ny, vy} <> [], T.VPair{ny, vy} <> []), M1.selfs(post),
              Eq.and.right(D1.same.go(T.VPair{nx, vx} <> [], T.VPair{nx, vx} <> []),
                M1.selfs(T.VPair{ny, vy} <> post), sx)),
            M2.and.tt(D1.same.go(T.VPair{nx, vx} <> [], T.VPair{nx, vx} <> []), M1.selfs(post),
              Eq.and.left(D1.same.go(T.VPair{nx, vx} <> [], T.VPair{nx, vx} <> []),
                M1.selfs(T.VPair{ny, vy} <> post), sx),
              Eq.and.right(D1.same.go(T.VPair{ny, vy} <> [], T.VPair{ny, vy} <> []), M1.selfs(post),
                Eq.and.right(D1.same.go(T.VPair{nx, vx} <> [], T.VPair{nx, vx} <> []),
                  M1.selfs(T.VPair{ny, vy} <> post), sx))))))))

# a well-formed document's rows each match themselves; the front cancels
# the rows before the two pairs cancel; each order then picks its first pair
# as the other order would, and what is left matches itself
def Laws.same_swap(e, pre, nx, vx, ny, vy, post, w, ne):
  +sa = {M3.wf.selfs(List.append(&2, T.Val, pre, T.VPair{nx, vx} <> T.VPair{ny, vy} <> post), T.WfRows{""}, w)
    : {M1.selfs(List.append(&2, T.Val, pre, T.VPair{nx, vx} <> T.VPair{ny, vy} <> post)) == True{} : Bool}}
  +sp = {selfs.pre(pre, T.VPair{nx, vx} <> T.VPair{ny, vy} <> post, sa) : {M1.selfs(pre) == True{} : Bool}}
  +sx = {selfs.suf(pre, T.VPair{nx, vx} <> T.VPair{ny, vy} <> post, sa)
    : {M1.selfs(T.VPair{nx, vx} <> T.VPair{ny, vy} <> post) == True{} : Bool}}
  swap.fin(e, pre, nx, vx, ny, vy, post, ne, sp, sx)
