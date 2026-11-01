# the induction over the text showing the walk keeps a document well formed
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../src/arith.bend as Ar
import ../../laws/DefinesEachTableOnce.bend as L1
import ../../laws/ParsedIsWellFormed.bend as L2
import ../../laws/defs/BareValueGrammar.bend as D1
import ./ControlEscapeText.bend as M1
import ./DecimalArithmetic.bend as M2
import ./FailedWalkNameCompare.bend as M3
import ./FreshNamesInRows.bend as M4
import ./PickAndDigitSteps.bend as M5
import ./ShortTextBounds.bend as M6
import ./StringEqualsItself.bend as M7

# WP-R3: short names for long premises, so each parameter fits on its line

# rows well-formed under a prefix
def gd.wo(vs: List<&2, T.Val>, pre: String) -> Bool:
  T.wf.go(vs, T.WfRows{pre})

# a frame wrapped round rows, well-formed under a prefix
def gd.ww(fr: T.Fr, vs: List<&2, T.Val>, pre: String) -> Bool:
  T.wf.go(T.tree.wrap(fr, vs), T.WfRows{pre})

# the root's rows, an open array's items and the frames below, all good
def gd.ra(rows: List<&2, T.Val>, items: List<&2, T.Val>, rest: List<&2, T.Ctx>) -> Bool:
  Bool.and(T.wf.go(rows, T.WfRows{""}), Bool.and(T.wf.go(items, T.WfItems{}), L2.gd.vals(rest)))

# the root's rows, an open inline table's rows and the frames below, all good
def gd.ri(rows: List<&2, T.Val>, inl: List<&2, T.Val>, rest: List<&2, T.Ctx>) -> Bool:
  Bool.and(T.wf.go(rows, T.WfRows{""}), Bool.and(L2.gd.inl(inl), L2.gd.vals(rest)))

# WP-R3: laws/ParsedIsWellFormed.bend's invariant (LAWS.bend's good) kept by the header states
# and by tree.walk. Every name here starts with gd. The kit: the invariant's
# facts are Bools that answered True, joined with gd.tt and split with gd.l
# and gd.r; the one shape wf.go gives a pair at the head of a table's rows is
# gd.pair.eq, so each lemma about rows splits Val's constructors once.

# both halves answered True
def gd.tt(
  aa: Bool,
  bb: Bool,
  +ea: {aa == True{} : Bool},
  +eb: {bb == True{} : Bool}
) -> {Bool.and(aa, bb) == True{} : Bool}:
  match aa:
    case True{}:
      eb
    case False{}:
      Eq.bit.absurd(&2, {Bool.and(False{}, bb) == True{} : Bool}, ea)

# the left half of an and that answered True
def gd.l(aa: Bool, bb: Bool, +ee: {Bool.and(aa, bb) == True{} : Bool}) -> {aa == True{} : Bool}:
  Eq.and.left(aa, bb, ee)

# the right half of an and that answered True
def gd.r(aa: Bool, bb: Bool, +ee: {Bool.and(aa, bb) == True{} : Bool}) -> {bb == True{} : Bool}:
  Eq.and.right(aa, bb, ee)

# a failed scanner is good whatever the rest says
def gd.off(
  ok: Bool,
  rest: Bool,
  +ee: {ok == False{} : Bool}
) -> {L2.gd.ifok(ok, rest) == True{} : Bool}:
  match ok:
    case False{}:
      {==}
    case True{}:
      Eq.bit.absurd2(&2, {L2.gd.ifok(True{}, rest) == True{} : Bool}, ee)

# WP-R3: the walk's lemmas: the rows a walk reads and rebuilds stay
# well-formed, one frame at a time.

# wf.go on a table's rows, a pair at their head: what the pair's value needs
# where it sits, its key, and the rest
def gd.pv(+pre: String, +nn: String, vv: T.Val) -> Bool:
  match vv:
    case T.VHead{+p, rows}:
      Bool.and(T.str.eq(p, T.tree.pre(pre, nn)), T.wf.go(rows, T.WfRows{p}))
    case T.VAots{+p, +el}:
      Bool.and(Bool.not(List.is_empty(&2, T.Val, el)),
        Bool.and(T.str.eq(p, T.tree.pre(pre, nn)), T.wf.go(el, T.WfElems{p})))
    case T.VArr{items}:
      T.wf.go(items, T.WfItems{})
    case T.VInl{rows}:
      T.wf.go(rows, T.WfInl{})
    case other:
      T.wf.atom(other)

# the four shapes wf.go gives a pair, as one and
def gd.sh.head(
  kk: Bool,
  ee: Bool,
  gg: Bool,
  dd: Bool
) -> {T.wf.then(Bool.and(kk, ee), _u => T.wf.then(gg, _v => dd))
    == Bool.and(Bool.and(kk, Bool.and(ee, gg)), dd) : Bool}:
  match kk ee gg:
    case False{} _e _g:
      {==}
    case True{} False{} _g:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      {==}

def gd.sh.aots(
  ss: Bool,
  kk: Bool,
  ee: Bool,
  gg: Bool,
  dd: Bool
) -> {T.wf.then(Bool.and(ss, Bool.and(kk, ee)), _u => T.wf.then(gg, _v => dd))
    == Bool.and(Bool.and(kk, Bool.and(ss, Bool.and(ee, gg))), dd) : Bool}:
  match ss kk ee gg:
    case False{} False{} _e _g:
      {==}
    case False{} True{} _e _g:
      {==}
    case True{} False{} _e _g:
      {==}
    case True{} True{} False{} _g:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def gd.sh.arr(
  kk: Bool,
  gg: Bool,
  dd: Bool
) -> {T.wf.then(kk, _u => T.wf.then(gg, _v => dd)) == Bool.and(Bool.and(kk, gg), dd) : Bool}:
  match kk gg:
    case False{} _g:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def gd.sh.atom(
  aa: Bool,
  kk: Bool,
  dd: Bool
) -> {T.wf.then(Bool.and(aa, kk), _u => dd) == Bool.and(Bool.and(kk, aa), dd) : Bool}:
  match aa kk:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

# a pair at the head of a table's rows is well-formed exactly when its key
# is, its value is where it sits, and the rest are
def gd.pair.eq(
  +pre: String,
  +nn: String,
  vv: T.Val,
  +tt: List<&2, T.Val>
) -> {T.wf.go(T.VPair{nn, vv} <> tt, T.WfRows{pre})
    == Bool.and(Bool.and(T.wf.key(nn, tt), gd.pv(pre, nn, vv)), T.wf.go(tt, T.WfRows{pre})) : Bool}:
  match vv:
    case T.VHead{+p, +rows}:
      gd.sh.head(T.wf.key(nn, tt), T.str.eq(p, T.tree.pre(pre, nn)), T.wf.go(rows, T.WfRows{p}),
        T.wf.go(tt, T.WfRows{pre}))
    case T.VAots{+p, +el}:
      gd.sh.aots(Bool.not(List.is_empty(&2, T.Val, el)), T.wf.key(nn, tt),
        T.str.eq(p, T.tree.pre(pre, nn)), T.wf.go(el, T.WfElems{p}), T.wf.go(tt, T.WfRows{pre}))
    case T.VArr{+items}:
      gd.sh.arr(T.wf.key(nn, tt), T.wf.go(items, T.WfItems{}), T.wf.go(tt, T.WfRows{pre}))
    case T.VInl{+rows}:
      gd.sh.arr(T.wf.key(nn, tt), T.wf.go(rows, T.WfInl{}), T.wf.go(tt, T.WfRows{pre}))
    case T.VStr{+a}:
      gd.sh.atom(T.wf.atom(T.VStr{a}), T.wf.key(nn, tt), T.wf.go(tt, T.WfRows{pre}))
    case T.VSpan{+a, +b}:
      gd.sh.atom(T.wf.atom(T.VSpan{a, b}), T.wf.key(nn, tt), T.wf.go(tt, T.WfRows{pre}))
    case T.VInt{+a, +b}:
      gd.sh.atom(T.wf.atom(T.VInt{a, b}), T.wf.key(nn, tt), T.wf.go(tt, T.WfRows{pre}))
    case T.VFlo{+a, +b}:
      gd.sh.atom(T.wf.atom(T.VFlo{a, b}), T.wf.key(nn, tt), T.wf.go(tt, T.WfRows{pre}))
    case T.VBool{+a}:
      gd.sh.atom(T.wf.atom(T.VBool{a}), T.wf.key(nn, tt), T.wf.go(tt, T.WfRows{pre}))
    case T.VWhen{+a}:
      gd.sh.atom(T.wf.atom(T.VWhen{a}), T.wf.key(nn, tt), T.wf.go(tt, T.WfRows{pre}))
    case T.VAot{+a, +b}:
      gd.sh.atom(T.wf.atom(T.VAot{a, b}), T.wf.key(nn, tt), T.wf.go(tt, T.WfRows{pre}))
    case T.VPair{+a, +b}:
      gd.sh.atom(T.wf.atom(T.VPair{a, b}), T.wf.key(nn, tt), T.wf.go(tt, T.WfRows{pre}))

# the pair's parts, read off a well-formed head
def gd.pr.un(
  +pre: String,
  +nn: String,
  +vv: T.Val,
  +tt: List<&2, T.Val>,
  +ew: {T.wf.go(T.VPair{nn, vv} <> tt, T.WfRows{pre}) == True{} : Bool}
) -> {Bool.and(Bool.and(T.wf.key(nn, tt), gd.pv(pre, nn, vv)), T.wf.go(tt, T.WfRows{pre})) == True{} : Bool}:
  Equal.trans(Bool, Bool.and(Bool.and(T.wf.key(nn, tt), gd.pv(pre, nn, vv)), T.wf.go(tt, T.WfRows{pre})),
    T.wf.go(T.VPair{nn, vv} <> tt, T.WfRows{pre}), True{},
    Equal.sym(Bool, T.wf.go(T.VPair{nn, vv} <> tt, T.WfRows{pre}),
      Bool.and(Bool.and(T.wf.key(nn, tt), gd.pv(pre, nn, vv)), T.wf.go(tt, T.WfRows{pre})),
      gd.pair.eq(pre, nn, vv, tt)),
    ew)

# the rest of the rows
def gd.pr.d(
  +pre: String,
  +nn: String,
  +vv: T.Val,
  +tt: List<&2, T.Val>,
  +ew: {T.wf.go(T.VPair{nn, vv} <> tt, T.WfRows{pre}) == True{} : Bool}
) -> {T.wf.go(tt, T.WfRows{pre}) == True{} : Bool}:
  gd.r(Bool.and(T.wf.key(nn, tt), gd.pv(pre, nn, vv)), T.wf.go(tt, T.WfRows{pre}),
    gd.pr.un(pre, nn, vv, tt, ew))

# the key
def gd.pr.k(
  +pre: String,
  +nn: String,
  +vv: T.Val,
  +tt: List<&2, T.Val>,
  +ew: {T.wf.go(T.VPair{nn, vv} <> tt, T.WfRows{pre}) == True{} : Bool}
) -> {T.wf.key(nn, tt) == True{} : Bool}:
  gd.l(T.wf.key(nn, tt), gd.pv(pre, nn, vv),
    gd.l(Bool.and(T.wf.key(nn, tt), gd.pv(pre, nn, vv)), T.wf.go(tt, T.WfRows{pre}),
      gd.pr.un(pre, nn, vv, tt, ew)))

# the value
def gd.pr.v(
  +pre: String,
  +nn: String,
  +vv: T.Val,
  +tt: List<&2, T.Val>,
  +ew: {T.wf.go(T.VPair{nn, vv} <> tt, T.WfRows{pre}) == True{} : Bool}
) -> {gd.pv(pre, nn, vv) == True{} : Bool}:
  gd.r(T.wf.key(nn, tt), gd.pv(pre, nn, vv),
    gd.l(Bool.and(T.wf.key(nn, tt), gd.pv(pre, nn, vv)), T.wf.go(tt, T.WfRows{pre}),
      gd.pr.un(pre, nn, vv, tt, ew)))

# and a pair is put together from its parts
def gd.pr.mk(
  +pre: String,
  +nn: String,
  +vv: T.Val,
  +tt: List<&2, T.Val>,
  +ek: {T.wf.key(nn, tt) == True{} : Bool},
  +ev: {gd.pv(pre, nn, vv) == True{} : Bool},
  +ed: {T.wf.go(tt, T.WfRows{pre}) == True{} : Bool}
) -> {T.wf.go(T.VPair{nn, vv} <> tt, T.WfRows{pre}) == True{} : Bool}:
  Equal.trans(Bool, T.wf.go(T.VPair{nn, vv} <> tt, T.WfRows{pre}),
    Bool.and(Bool.and(T.wf.key(nn, tt), gd.pv(pre, nn, vv)), T.wf.go(tt, T.WfRows{pre})), True{},
    gd.pair.eq(pre, nn, vv, tt),
    gd.tt(Bool.and(T.wf.key(nn, tt), gd.pv(pre, nn, vv)), T.wf.go(tt, T.WfRows{pre}),
      gd.tt(T.wf.key(nn, tt), gd.pv(pre, nn, vv), ek, ev), ed))

# a value's needs at one name are its needs at an equal name
def gd.pv.name(
  +pre: String,
  +aa: String,
  +bb: String,
  +vv: T.Val,
  +eq: {T.str.eq(aa, bb) == True{} : Bool},
  +ev: {gd.pv(pre, bb, vv) == True{} : Bool}
) -> {gd.pv(pre, aa, vv) == True{} : Bool}:
  Equal.trans(Bool, gd.pv(pre, aa, vv), gd.pv(pre, bb, vv), True{},
    Equal.cong(String, Bool, xx => gd.pv(pre, xx, vv), aa, bb, M3.str.eq.true(aa, bb, eq)), ev)

# what a walk step learns from looking a name up in well-formed rows: a name
# that is missing is fresh, a table or an array of tables sits at the path
# the name gives and is well-formed there, and a refusal names its reason
def gd.lk(hit: T.Hit, +pre: String, +name: String, look: T.Look) -> Bool:
  match look:
    case T.KMiss{}:
      T.wf.fresh(hit)
    case T.KHead{p, rows}:
      gd.pv(pre, name, T.VHead{p, rows})
    case T.KAots{p, el}:
      gd.pv(pre, name, T.VAots{p, el})
    case T.KInl{}:
      True{}
    case T.KNo{why}:
      Bool.not(String.is_empty(why))

# what look.of makes of a value well-formed at the name
def gd.lk.of(
  hit: T.Hit,
  +pre: String,
  +name: String,
  vv: T.Val,
  +ep: {gd.pv(pre, name, vv) == True{} : Bool}
) -> {gd.lk(hit, pre, name, T.look.of(vv)) == True{} : Bool}:
  match vv:
    case T.VHead{_p, _r}:
      ep
    case T.VAots{_p, _e}:
      ep
    case T.VInl{_r}:
      {==}
    case T.VArr{_i}:
      {==}
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
    case T.VAot{_a, _b}:
      {==}
    case T.VPair{_a, _b}:
      {==}

# one pair of the rows: the lookup stops at it or goes on
def gd.lk.step(
  bb: Bool,
  +nn: String,
  +vv: T.Val,
  +tt: List<&2, T.Val>,
  +pre: String,
  +name: String,
  +eb: {T.str.eq(nn, name) == bb : Bool},
  +ew: {T.wf.go(T.VPair{nn, vv} <> tt, T.WfRows{pre}) == True{} : Bool},
  ih: {gd.lk(T.get(tt, name), pre, name, T.rows.look(tt, name)) == True{} : Bool}
) -> {gd.lk(T.find.step(bb, vv, _u => T.rows.find(tt, name)), pre, name,
  T.look.step(bb, vv, _u => T.rows.look(tt, name))) == True{} : Bool}:
  match bb:
    case True{}:
      gd.lk.of(T.Found{vv}, pre, name, vv,
        Equal.trans(Bool, gd.pv(pre, name, vv), gd.pv(pre, nn, vv), True{},
          Equal.cong(String, Bool, xx => gd.pv(pre, xx, vv), name, nn,
            Equal.sym(String, nn, name, M3.str.eq.true(nn, name, eb))),
          gd.pr.v(pre, nn, vv, tt, ew)))
    case False{}:
      ih

# rows with anything but a pair at their head are no table's
def gd.lk.bad(
  +hh: T.Val,
  +tt: List<&2, T.Val>,
  +pre: String,
  +name: String,
  +ee: {False{} == True{} : Bool}
) -> {gd.lk(T.get(hh <> tt, name), pre, name, T.rows.look(hh <> tt, name)) == True{} : Bool}:
  Eq.bit.absurd(&2, {gd.lk(T.get(hh <> tt, name), pre, name, T.rows.look(hh <> tt, name))
    == True{} : Bool}, ee)

# looking a name up in well-formed rows
def gd.lk.ok(
  vs: List<&2, T.Val>,
  +pre: String,
  +name: String,
  +ew: {T.wf.go(vs, T.WfRows{pre}) == True{} : Bool}
) -> {gd.lk(T.get(vs, name), pre, name, T.rows.look(vs, name)) == True{} : Bool}:
  match vs:
    case []:
      {==}
    case T.VPair{+nn, +vv} <> +tt:
      gd.lk.step(T.str.eq(nn, name), nn, vv, tt, pre, name, {==}, ew,
        gd.lk.ok(tt, pre, name, gd.pr.d(pre, nn, vv, tt, ew)))
    case T.VStr{a} <> tt:
      gd.lk.bad(T.VStr{a}, tt, pre, name, ew)
    case T.VSpan{a, b} <> tt:
      gd.lk.bad(T.VSpan{a, b}, tt, pre, name, ew)
    case T.VInt{a, b} <> tt:
      gd.lk.bad(T.VInt{a, b}, tt, pre, name, ew)
    case T.VFlo{a, b} <> tt:
      gd.lk.bad(T.VFlo{a, b}, tt, pre, name, ew)
    case T.VBool{a} <> tt:
      gd.lk.bad(T.VBool{a}, tt, pre, name, ew)
    case T.VWhen{a} <> tt:
      gd.lk.bad(T.VWhen{a}, tt, pre, name, ew)
    case T.VArr{a} <> tt:
      gd.lk.bad(T.VArr{a}, tt, pre, name, ew)
    case T.VInl{a} <> tt:
      gd.lk.bad(T.VInl{a}, tt, pre, name, ew)
    case T.VHead{a, b} <> tt:
      gd.lk.bad(T.VHead{a, b}, tt, pre, name, ew)
    case T.VAot{a, b} <> tt:
      gd.lk.bad(T.VAot{a, b}, tt, pre, name, ew)
    case T.VAots{a, b} <> tt:
      gd.lk.bad(T.VAots{a, b}, tt, pre, name, ew)

# a lookup that stops at one pair or goes on, over two rows that agree after it
def gd.fr.b2(
  b2: Bool,
  v1: T.Val,
  v2: T.Val,
  r1: List<&2, T.Val>,
  r2: List<&2, T.Val>,
  +xx: String,
  ih: {T.wf.fresh(T.rows.find(r1, xx)) == T.wf.fresh(T.rows.find(r2, xx)) : Bool}
) -> {T.wf.fresh(T.find.step(b2, v1, _u => T.rows.find(r1, xx)))
  == T.wf.fresh(T.find.step(b2, v2, _u => T.rows.find(r2, xx))) : Bool}:
  match b2:
    case True{}:
      {==}
    case False{}:
      ih

# a pair rows.repl may replace keeps its name
def gd.fr.rstep(
  b1: Bool,
  +nn: String,
  +old: T.Val,
  +vv: T.Val,
  +t2: List<&2, T.Val>,
  +name: String,
  +xx: String,
  ih: {T.wf.fresh(T.get(T.rows.repl(t2, name, vv), xx)) == T.wf.fresh(T.get(t2, xx)) : Bool}
) -> {T.wf.fresh(T.rows.find(T.rows.repl.step(b1, nn, old, vv, _u => T.rows.repl(t2, name, vv)), xx))
  == T.wf.fresh(T.find.step(T.str.eq(nn, xx), old, _u => T.rows.find(t2, xx))) : Bool}:
  match b1:
    case True{}:
      gd.fr.b2(T.str.eq(nn, xx), vv, old, T.rows.repl(t2, name, vv), t2, xx, ih)
    case False{}:
      gd.fr.b2(T.str.eq(nn, xx), old, old, T.rows.repl(t2, name, vv), t2, xx, ih)

# replacing a pair's value leaves every name where it was, so a name is fresh
# in the rows after exactly when it was before
def gd.fr.repl(
  t: List<&2, T.Val>,
  +name: String,
  +vv: T.Val,
  +xx: String
) -> {T.wf.fresh(T.get(T.rows.repl(t, name, vv), xx)) == T.wf.fresh(T.get(t, xx)) : Bool}:
  match t:
    case []:
      {==}
    case T.VPair{+nn, +old} <> +t2:
      gd.fr.rstep(T.str.eq(nn, name), nn, old, vv, t2, name, xx, gd.fr.repl(t2, name, vv, xx))
    case T.VStr{a} <> t2:
      gd.fr.repl(t2, name, vv, xx)
    case T.VSpan{a, b} <> t2:
      gd.fr.repl(t2, name, vv, xx)
    case T.VInt{a, b} <> t2:
      gd.fr.repl(t2, name, vv, xx)
    case T.VFlo{a, b} <> t2:
      gd.fr.repl(t2, name, vv, xx)
    case T.VBool{a} <> t2:
      gd.fr.repl(t2, name, vv, xx)
    case T.VWhen{a} <> t2:
      gd.fr.repl(t2, name, vv, xx)
    case T.VArr{a} <> t2:
      gd.fr.repl(t2, name, vv, xx)
    case T.VInl{a} <> t2:
      gd.fr.repl(t2, name, vv, xx)
    case T.VHead{a, b} <> t2:
      gd.fr.repl(t2, name, vv, xx)
    case T.VAot{a, b} <> t2:
      gd.fr.repl(t2, name, vv, xx)
    case T.VAots{a, b} <> t2:
      gd.fr.repl(t2, name, vv, xx)

# the key of a pair whose rest rows.repl rewrote is as fresh as before
def gd.rp.key(
  +nn: String,
  +tt: List<&2, T.Val>,
  +name: String,
  +vv: T.Val,
  +ek: {T.wf.key(nn, tt) == True{} : Bool}
) -> {T.wf.key(nn, T.rows.repl(tt, name, vv)) == True{} : Bool}:
  Equal.trans(Bool, T.wf.key(nn, T.rows.repl(tt, name, vv)), T.wf.key(nn, tt), True{},
    Equal.cong(Bool, Bool, xx => Bool.and(T.wf.text(nn), xx),
      T.wf.fresh(T.get(T.rows.repl(tt, name, vv), nn)), T.wf.fresh(T.get(tt, nn)),
      gd.fr.repl(tt, name, vv, nn)),
    ek)

# one pair: replaced by the new value when the name is its, else kept
def gd.rp.step(
  bb: Bool,
  +nn: String,
  +old: T.Val,
  +tt: List<&2, T.Val>,
  +pre: String,
  +name: String,
  +vv: T.Val,
  +eb: {T.str.eq(nn, name) == bb : Bool},
  +ew: {T.wf.go(T.VPair{nn, old} <> tt, T.WfRows{pre}) == True{} : Bool},
  +ev: {gd.pv(pre, name, vv) == True{} : Bool},
  +ih: {T.wf.go(T.rows.repl(tt, name, vv), T.WfRows{pre}) == True{} : Bool}
) -> {T.wf.go(T.rows.repl.step(bb, nn, old, vv, _u => T.rows.repl(tt, name, vv)), T.WfRows{pre})
  == True{} : Bool}:
  match bb:
    case True{}:
      gd.pr.mk(pre, nn, vv, T.rows.repl(tt, name, vv),
        gd.rp.key(nn, tt, name, vv, gd.pr.k(pre, nn, old, tt, ew)),
        gd.pv.name(pre, nn, name, vv, eb, ev), ih)
    case False{}:
      gd.pr.mk(pre, nn, old, T.rows.repl(tt, name, vv),
        gd.rp.key(nn, tt, name, vv, gd.pr.k(pre, nn, old, tt, ew)),
        gd.pr.v(pre, nn, old, tt, ew), ih)

# rows with anything but a pair at their head are no table's
def gd.rp.bad(
  +hh: T.Val,
  +tt: List<&2, T.Val>,
  +pre: String,
  +name: String,
  +vv: T.Val,
  +ee: {False{} == True{} : Bool}
) -> {T.wf.go(T.rows.repl(hh <> tt, name, vv), T.WfRows{pre}) == True{} : Bool}:
  Eq.bit.absurd(&2, {T.wf.go(T.rows.repl(hh <> tt, name, vv), T.WfRows{pre}) == True{} : Bool}, ee)

# replacing the value of a name in well-formed rows by one well-formed at that
# name keeps them well-formed
def gd.repl.ok(
  vs: List<&2, T.Val>,
  +pre: String,
  +name: String,
  +vv: T.Val,
  +ew: {T.wf.go(vs, T.WfRows{pre}) == True{} : Bool},
  +ev: {gd.pv(pre, name, vv) == True{} : Bool}
) -> {T.wf.go(T.rows.repl(vs, name, vv), T.WfRows{pre}) == True{} : Bool}:
  match vs:
    case []:
      {==}
    case T.VPair{+nn, +old} <> +tt:
      gd.rp.step(T.str.eq(nn, name), nn, old, tt, pre, name, vv, {==}, ew, ev,
        gd.repl.ok(tt, pre, name, vv, gd.pr.d(pre, nn, old, tt, ew), ev))
    case T.VStr{a} <> tt:
      gd.rp.bad(T.VStr{a}, tt, pre, name, vv, ew)
    case T.VSpan{a, b} <> tt:
      gd.rp.bad(T.VSpan{a, b}, tt, pre, name, vv, ew)
    case T.VInt{a, b} <> tt:
      gd.rp.bad(T.VInt{a, b}, tt, pre, name, vv, ew)
    case T.VFlo{a, b} <> tt:
      gd.rp.bad(T.VFlo{a, b}, tt, pre, name, vv, ew)
    case T.VBool{a} <> tt:
      gd.rp.bad(T.VBool{a}, tt, pre, name, vv, ew)
    case T.VWhen{a} <> tt:
      gd.rp.bad(T.VWhen{a}, tt, pre, name, vv, ew)
    case T.VArr{a} <> tt:
      gd.rp.bad(T.VArr{a}, tt, pre, name, vv, ew)
    case T.VInl{a} <> tt:
      gd.rp.bad(T.VInl{a}, tt, pre, name, vv, ew)
    case T.VHead{a, b} <> tt:
      gd.rp.bad(T.VHead{a, b}, tt, pre, name, vv, ew)
    case T.VAot{a, b} <> tt:
      gd.rp.bad(T.VAot{a, b}, tt, pre, name, vv, ew)
    case T.VAots{a, b} <> tt:
      gd.rp.bad(T.VAots{a, b}, tt, pre, name, vv, ew)

# the newest element of a well-formed array of tables: the older elements
# and the element's rows are well-formed at the array's path, and a refusal
# names its reason
def gd.ll(+pp: String, last: T.Last) -> Bool:
  match last:
    case T.LastSome{_q, older, rows}:
      Bool.and(T.wf.go(older, T.WfElems{pp}), T.wf.go(rows, T.WfRows{pp}))
    case T.LastNo{why}:
      Bool.not(String.is_empty(why))

# an element of an array of tables, read off a well-formed head
def gd.el.un(
  +qq: String,
  +rows: List<&2, T.Val>,
  +tt: List<&2, T.Val>,
  +pp: String,
  +ew: {T.wf.go(T.VAot{qq, rows} <> tt, T.WfElems{pp}) == True{} : Bool}
) -> {Bool.and(Bool.and(T.str.eq(qq, pp), T.wf.go(rows, T.WfRows{qq})), T.wf.go(tt, T.WfElems{pp}))
    == True{} : Bool}:
  Equal.trans(Bool,
    Bool.and(Bool.and(T.str.eq(qq, pp), T.wf.go(rows, T.WfRows{qq})), T.wf.go(tt, T.WfElems{pp})),
    T.wf.go(T.VAot{qq, rows} <> tt, T.WfElems{pp}), True{},
    Equal.sym(Bool, T.wf.go(T.VAot{qq, rows} <> tt, T.WfElems{pp}),
      Bool.and(Bool.and(T.str.eq(qq, pp), T.wf.go(rows, T.WfRows{qq})), T.wf.go(tt, T.WfElems{pp})),
      gd.sh.arr(T.str.eq(qq, pp), T.wf.go(rows, T.WfRows{qq}), T.wf.go(tt, T.WfElems{pp}))),
    ew)

# and an element is put together from its parts
def gd.el.mk(
  +pp: String,
  +rows: List<&2, T.Val>,
  +tt: List<&2, T.Val>,
  +er: {T.wf.go(rows, T.WfRows{pp}) == True{} : Bool},
  +et: {T.wf.go(tt, T.WfElems{pp}) == True{} : Bool}
) -> {T.wf.go(T.VAot{pp, rows} <> tt, T.WfElems{pp}) == True{} : Bool}:
  Equal.trans(Bool, T.wf.go(T.VAot{pp, rows} <> tt, T.WfElems{pp}),
    Bool.and(Bool.and(T.str.eq(pp, pp), T.wf.go(rows, T.WfRows{pp})), T.wf.go(tt, T.WfElems{pp})),
    True{},
    gd.sh.arr(T.str.eq(pp, pp), T.wf.go(rows, T.WfRows{pp}), T.wf.go(tt, T.WfElems{pp})),
    gd.tt(Bool.and(T.str.eq(pp, pp), T.wf.go(rows, T.WfRows{pp})), T.wf.go(tt, T.WfElems{pp}),
      gd.tt(T.str.eq(pp, pp), T.wf.go(rows, T.WfRows{pp}), M7.str.eq.self(pp), er), et))

# rows well-formed at one path are well-formed at an equal one
def gd.at.path(
  +aa: String,
  +bb: String,
  +rows: List<&2, T.Val>,
  +eq: {aa == bb : String},
  +ew: {T.wf.go(rows, T.WfRows{aa}) == True{} : Bool}
) -> {T.wf.go(rows, T.WfRows{bb}) == True{} : Bool}:
  Equal.trans(Bool, T.wf.go(rows, T.WfRows{bb}), T.wf.go(rows, T.WfRows{aa}), True{},
    Equal.cong(String, Bool, xx => T.wf.go(rows, T.WfRows{xx}), bb, aa, Equal.sym(String, aa, bb, eq)),
    ew)

# and elements too
def gd.el.path(
  +aa: String,
  +bb: String,
  +el: List<&2, T.Val>,
  +eq: {aa == bb : String},
  +ew: {T.wf.go(el, T.WfElems{aa}) == True{} : Bool}
) -> {T.wf.go(el, T.WfElems{bb}) == True{} : Bool}:
  Equal.trans(Bool, T.wf.go(el, T.WfElems{bb}), T.wf.go(el, T.WfElems{aa}), True{},
    Equal.cong(String, Bool, xx => T.wf.go(el, T.WfElems{xx}), bb, aa, Equal.sym(String, aa, bb, eq)),
    ew)

# the newest element of a well-formed array of tables
def gd.ll.ok(
  el: List<&2, T.Val>,
  +pp: String,
  +ew: {T.wf.go(el, T.WfElems{pp}) == True{} : Bool}
) -> {gd.ll(pp, T.look.last(el, pp)) == True{} : Bool}:
  match el:
    case []:
      {==}
    case T.VAot{+qq, +rows} <> +tt:
      gd.tt(T.wf.go(tt, T.WfElems{pp}), T.wf.go(rows, T.WfRows{pp}),
        gd.r(Bool.and(T.str.eq(qq, pp), T.wf.go(rows, T.WfRows{qq})), T.wf.go(tt, T.WfElems{pp}),
          gd.el.un(qq, rows, tt, pp, ew)),
        gd.at.path(qq, pp, rows,
          M3.str.eq.true(qq, pp, gd.l(T.str.eq(qq, pp), T.wf.go(rows, T.WfRows{qq}),
            gd.l(Bool.and(T.str.eq(qq, pp), T.wf.go(rows, T.WfRows{qq})), T.wf.go(tt, T.WfElems{pp}),
              gd.el.un(qq, rows, tt, pp, ew)))),
          gd.r(T.str.eq(qq, pp), T.wf.go(rows, T.WfRows{qq}),
            gd.l(Bool.and(T.str.eq(qq, pp), T.wf.go(rows, T.WfRows{qq})), T.wf.go(tt, T.WfElems{pp}),
              gd.el.un(qq, rows, tt, pp, ew)))))
    case T.VStr{_a} <> _t:
      {==}
    case T.VSpan{_a, _b} <> _t:
      {==}
    case T.VInt{_a, _b} <> _t:
      {==}
    case T.VFlo{_a, _b} <> _t:
      {==}
    case T.VBool{_a} <> _t:
      {==}
    case T.VWhen{_a} <> _t:
      {==}
    case T.VArr{_a} <> _t:
      {==}
    case T.VInl{_a} <> _t:
      {==}
    case T.VHead{_a, _b} <> _t:
      {==}
    case T.VAots{_a, _b} <> _t:
      {==}
    case T.VPair{_a, _b} <> _t:
      {==}

# WP-R3: the walk. The frames above the table a walk is in are a promise:
# rows well-formed at the table's path rebuild into a well-formed root. The
# promise starts as the root itself and grows by one frame per step.
def gd.K(stack: List<&2, T.Fr>, +pre: String) -> Type:
  @vs: List<&2, T.Val> -> @bad: String -> @hs: List<&2, String> ->
    {L2.gd.ifok(String.is_empty(bad), T.wf.go(vs, T.WfRows{pre})) == True{} : Bool} ->
    {L2.gd.end(T.tree.rebuild(stack, vs, bad, hs)) == True{} : Bool}

# at the root the rows are the root's
def gd.k.root() -> gd.K([], ""):
  _vs => _bad => _hs => ee => ee

# a frame's rows put back are well-formed where the frame sits
def gd.k.lift(
  bad: String,
  +vs: List<&2, T.Val>,
  +fr: T.Fr,
  +pre: String,
  +pre2: String,
  +ee: {L2.gd.ifok(String.is_empty(bad), T.wf.go(vs, T.WfRows{pre2})) == True{} : Bool},
  ff: @ch: List<&2, T.Val> -> {gd.wo(ch, pre2) == True{} : Bool} -> {gd.ww(fr, ch, pre) == True{} : Bool}
) -> {L2.gd.ifok(String.is_empty(bad), T.wf.go(T.tree.wrap(fr, vs), T.WfRows{pre})) == True{} : Bool}:
  match bad:
    case SNil{}:
      ff(vs, ee)
    case SCon{_h, _t}:
      {==}

# one more frame, applied
def gd.k.pushgo(
  +fr: T.Fr,
  stack: List<&2, T.Fr>,
  +pre: String,
  +pre2: String,
  kk: gd.K(stack, pre),
  ff: @ch: List<&2, T.Val> -> {gd.wo(ch, pre2) == True{} : Bool} -> {gd.ww(fr, ch, pre) == True{} : Bool},
  +vs: List<&2, T.Val>,
  +bad: String,
  hs: List<&2, String>,
  +ee: {L2.gd.ifok(String.is_empty(bad), T.wf.go(vs, T.WfRows{pre2})) == True{} : Bool}
) -> {L2.gd.end(T.tree.rebuild(fr <> stack, vs, bad, hs)) == True{} : Bool}:
  kk(T.tree.wrap(fr, vs), bad, hs, gd.k.lift(bad, vs, fr, pre, pre2, ee, ff))

# one more frame
def gd.k.push(
  +fr: T.Fr,
  stack: List<&2, T.Fr>,
  +pre: String,
  +pre2: String,
  kk: gd.K(stack, pre),
  ff: @ch: List<&2, T.Val> -> {gd.wo(ch, pre2) == True{} : Bool} -> {gd.ww(fr, ch, pre) == True{} : Bool}
) -> gd.K(fr <> stack, pre2):
  vs => bad => hs => ee => gd.k.pushgo(fr, stack, pre, pre2, kk, ff, vs, bad, hs, ee)

# a table the walk makes on its way
def gd.ff.new(
  +name: String,
  +vs: List<&2, T.Val>,
  +pre: String,
  +et: {T.wf.text(name) == True{} : Bool},
  +ef: {T.wf.fresh(T.get(vs, name)) == True{} : Bool},
  +ew: {T.wf.go(vs, T.WfRows{pre}) == True{} : Bool},
  +ch: List<&2, T.Val>,
  +ec: {T.wf.go(ch, T.WfRows{T.tree.pre(pre, name)}) == True{} : Bool}
) -> {T.wf.go(T.tree.wrap(T.FrNew{name, vs, T.tree.pre(pre, name)}, ch), T.WfRows{pre}) == True{} : Bool}:
  gd.pr.mk(pre, name, T.VHead{T.tree.pre(pre, name), ch}, vs,
    gd.tt(T.wf.text(name), T.wf.fresh(T.get(vs, name)), et, ef),
    gd.tt(T.str.eq(T.tree.pre(pre, name), T.tree.pre(pre, name)),
      T.wf.go(ch, T.WfRows{T.tree.pre(pre, name)}), M7.str.eq.self(T.tree.pre(pre, name)), ec),
    ew)

# a table the walk enters
def gd.ff.rep(
  +name: String,
  +vs: List<&2, T.Val>,
  +pre: String,
  +pp: String,
  +es: {T.str.eq(pp, T.tree.pre(pre, name)) == True{} : Bool},
  +ew: {T.wf.go(vs, T.WfRows{pre}) == True{} : Bool},
  +ch: List<&2, T.Val>,
  +ec: {T.wf.go(ch, T.WfRows{T.tree.pre(pre, name)}) == True{} : Bool}
) -> {T.wf.go(T.tree.wrap(T.FrRep{name, vs, pp}, ch), T.WfRows{pre}) == True{} : Bool}:
  gd.repl.ok(vs, pre, name, T.VHead{pp, ch}, ew,
    gd.tt(T.str.eq(pp, T.tree.pre(pre, name)), T.wf.go(ch, T.WfRows{pp}), es,
      gd.at.path(T.tree.pre(pre, name), pp, ch,
        Equal.sym(String, pp, T.tree.pre(pre, name), M3.str.eq.true(pp, T.tree.pre(pre, name), es)), ec)))

# the newest element of an array of tables the walk enters
def gd.ff.aot(
  +name: String,
  +vs: List<&2, T.Val>,
  +pre: String,
  +pp: String,
  +older: List<&2, T.Val>,
  +es: {T.str.eq(pp, T.tree.pre(pre, name)) == True{} : Bool},
  +eo: {T.wf.go(older, T.WfElems{pp}) == True{} : Bool},
  +ew: {T.wf.go(vs, T.WfRows{pre}) == True{} : Bool},
  +ch: List<&2, T.Val>,
  +ec: {T.wf.go(ch, T.WfRows{T.tree.pre(pre, name)}) == True{} : Bool}
) -> {T.wf.go(T.tree.wrap(T.FrAot{name, vs, older, pp}, ch), T.WfRows{pre}) == True{} : Bool}:
  gd.repl.ok(vs, pre, name, T.VAots{pp, T.VAot{pp, ch} <> older}, ew,
    gd.tt(True{}, Bool.and(T.str.eq(pp, T.tree.pre(pre, name)),
      T.wf.go(T.VAot{pp, ch} <> older, T.WfElems{pp})), {==},
      gd.tt(T.str.eq(pp, T.tree.pre(pre, name)), T.wf.go(T.VAot{pp, ch} <> older, T.WfElems{pp}), es,
        gd.el.mk(pp, ch, older,
          gd.at.path(T.tree.pre(pre, name), pp, ch,
            Equal.sym(String, pp, T.tree.pre(pre, name), M3.str.eq.true(pp, T.tree.pre(pre, name), es)),
            ec),
          eo))))

# what the rest of a walk is owed: any table it goes on in, with a promise
def gd.wk.IH(rest: List<&2, String>, +job: T.Job, +inl: Bool, +skip: U32) -> Type:
  @vs: List<&2, T.Val> -> @stack: List<&2, T.Fr> -> @bad: String -> @pre: String ->
    @hs: List<&2, String> ->
    {L2.gd.ifok(String.is_empty(bad), T.wf.go(vs, T.WfRows{pre})) == True{} : Bool} ->
    gd.K(stack, pre) ->
    {L2.gd.end(T.tree.walk(rest, T.Tw{vs, job, stack, bad, pre, hs, inl}, skip)) == True{} : Bool}

# a refusal's reason is no empty text, so the walk has failed
def gd.why(
  +why: String,
  +vs: List<&2, T.Val>,
  +pre: String,
  +ee: {Bool.not(String.is_empty(why)) == True{} : Bool}
) -> {L2.gd.ifok(String.is_empty(why), T.wf.go(vs, T.WfRows{pre})) == True{} : Bool}:
  gd.off(String.is_empty(why), T.wf.go(vs, T.WfRows{pre}), Eq.not.true(String.is_empty(why), ee))

# a step into a table that may be shut to a dotted key
def gd.wk.hgo(
  shut: Bool,
  +pp: String,
  +rows: List<&2, T.Val>,
  +name: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +mark: Bool,
  rest: List<&2, String>,
  +skip: U32,
  +eh: {gd.pv(pre, name, T.VHead{pp, rows}) == True{} : Bool},
  +ew: {T.wf.go(vs, T.WfRows{pre}) == True{} : Bool},
  kk: gd.K(stack, pre),
  ih: gd.wk.IH(rest, job, inl, skip)
) -> {L2.gd.end(T.tree.walk(rest, T.tree.sub.head.go(shut, pp, rows, name, vs, job, stack, pre, heads,
  inl, mark), skip)) == True{} : Bool}:
  match shut:
    case True{}:
      ih(vs, stack, "duplicate table", pre, heads, {==}, kk)
    case False{}:
      ih(rows, T.FrRep{name, vs, pp} <> stack, "", T.tree.pre(pre, name),
        T.heads.define(T.tree.sub.job(mark, job), T.tree.pre(pre, name), heads),
        gd.at.path(pp, T.tree.pre(pre, name), rows,
          M3.str.eq.true(pp, T.tree.pre(pre, name),
            gd.l(T.str.eq(pp, T.tree.pre(pre, name)), T.wf.go(rows, T.WfRows{pp}), eh)),
          gd.r(T.str.eq(pp, T.tree.pre(pre, name)), T.wf.go(rows, T.WfRows{pp}), eh)),
        gd.k.push(T.FrRep{name, vs, pp}, stack, pre, T.tree.pre(pre, name), kk,
          ch => ec => gd.ff.rep(name, vs, pre, pp,
            gd.l(T.str.eq(pp, T.tree.pre(pre, name)), T.wf.go(rows, T.WfRows{pp}), eh), ew, ch, ec)))

# a step into a table: a dotted key asks whether a header defined it
def gd.wk.head(
  dot: Bool,
  +pp: String,
  +rows: List<&2, T.Val>,
  +name: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +mark: Bool,
  rest: List<&2, String>,
  +skip: U32,
  +eh: {gd.pv(pre, name, T.VHead{pp, rows}) == True{} : Bool},
  +ew: {T.wf.go(vs, T.WfRows{pre}) == True{} : Bool},
  kk: gd.K(stack, pre),
  ih: gd.wk.IH(rest, job, inl, skip)
) -> {L2.gd.end(T.tree.walk(rest, T.tree.sub.head(dot, pp, rows, name, vs, job, stack, pre, heads,
  inl, mark), skip)) == True{} : Bool}:
  match dot:
    case True{}:
      gd.wk.hgo(T.heads.head(heads, T.tree.pre(pre, name)), pp, rows, name, vs, job, stack, pre, heads,
        inl, mark, rest, skip, eh, ew, kk, ih)
    case False{}:
      gd.wk.hgo(False{}, pp, rows, name, vs, job, stack, pre, heads, inl, mark, rest, skip, eh, ew, kk, ih)

# a step into the newest element of an array of tables
def gd.wk.last(
  last: T.Last,
  +pp: String,
  +name: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  rest: List<&2, String>,
  +skip: U32,
  +el: {gd.ll(pp, last) == True{} : Bool},
  +es: {T.str.eq(pp, T.tree.pre(pre, name)) == True{} : Bool},
  +ew: {T.wf.go(vs, T.WfRows{pre}) == True{} : Bool},
  kk: gd.K(stack, pre),
  ih: gd.wk.IH(rest, job, inl, skip)
) -> {L2.gd.end(T.tree.walk(rest, T.tree.sub.aots(last, name, vs, job, stack, pre, heads, inl, pp),
  skip)) == True{} : Bool}:
  match last:
    case T.LastSome{_q, +older, +rows}:
      ih(rows, T.FrAot{name, vs, older, pp} <> stack, "", T.tree.pre(pre, name), heads,
        gd.at.path(pp, T.tree.pre(pre, name), rows, M3.str.eq.true(pp, T.tree.pre(pre, name), es),
          gd.r(T.wf.go(older, T.WfElems{pp}), T.wf.go(rows, T.WfRows{pp}), el)),
        gd.k.push(T.FrAot{name, vs, older, pp}, stack, pre, T.tree.pre(pre, name), kk,
          ch => ec => gd.ff.aot(name, vs, pre, pp, older, es,
            gd.l(T.wf.go(older, T.WfElems{pp}), T.wf.go(rows, T.WfRows{pp}), el), ew, ch, ec)))
    case T.LastNo{+why}:
      ih(vs, stack, why, pre, heads, gd.why(why, vs, pre, el), kk)

# a step into an array of tables: a dotted key may not
def gd.wk.arr(
  dot: Bool,
  +pp: String,
  +es: List<&2, T.Val>,
  +name: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  rest: List<&2, String>,
  +skip: U32,
  +eh: {gd.pv(pre, name, T.VAots{pp, es}) == True{} : Bool},
  +ew: {T.wf.go(vs, T.WfRows{pre}) == True{} : Bool},
  kk: gd.K(stack, pre),
  ih: gd.wk.IH(rest, job, inl, skip)
) -> {L2.gd.end(T.tree.walk(rest, T.tree.sub.arr(dot, pp, es, name, vs, job, stack, pre, heads, inl),
  skip)) == True{} : Bool}:
  match dot:
    case True{}:
      ih(vs, stack, "duplicate table", pre, heads, {==}, kk)
    case False{}:
      gd.wk.last(T.look.last(es, pp), pp, name, vs, job, stack, pre, heads, inl, rest, skip,
        gd.ll.ok(es, pp, gd.r(T.str.eq(pp, T.tree.pre(pre, name)), T.wf.go(es, T.WfElems{pp}),
          gd.r(Bool.not(List.is_empty(&2, T.Val, es)),
            Bool.and(T.str.eq(pp, T.tree.pre(pre, name)), T.wf.go(es, T.WfElems{pp})), eh))),
        gd.l(T.str.eq(pp, T.tree.pre(pre, name)), T.wf.go(es, T.WfElems{pp}),
          gd.r(Bool.not(List.is_empty(&2, T.Val, es)),
            Bool.and(T.str.eq(pp, T.tree.pre(pre, name)), T.wf.go(es, T.WfElems{pp})), eh)),
        ew, kk, ih)

# a navigation step, by what the name refers to
def gd.wk.sub(
  hit: T.Look,
  +name: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +mark: Bool,
  rest: List<&2, String>,
  +skip: U32,
  +eh: {gd.lk(T.get(vs, name), pre, name, hit) == True{} : Bool},
  +ew: {T.wf.go(vs, T.WfRows{pre}) == True{} : Bool},
  +et: {T.wf.text(name) == True{} : Bool},
  kk: gd.K(stack, pre),
  ih: gd.wk.IH(rest, job, inl, skip)
) -> {L2.gd.end(T.tree.walk(rest, T.tree.sub.look(hit, name, vs, job, stack, pre, heads, inl, mark),
  skip)) == True{} : Bool}:
  match hit:
    case T.KMiss{}:
      ih([], T.FrNew{name, vs, T.tree.pre(pre, name)} <> stack, "", T.tree.pre(pre, name),
        T.heads.define(T.tree.sub.job(mark, job), T.tree.pre(pre, name), heads), {==},
        gd.k.push(T.FrNew{name, vs, T.tree.pre(pre, name)}, stack, pre, T.tree.pre(pre, name), kk,
          ch => ec => gd.ff.new(name, vs, pre, et, eh, ew, ch, ec)))
    case T.KHead{+pp, +rows}:
      gd.wk.head(T.tree.sub.dot(T.tree.sub.job(mark, job)), pp, rows, name, vs, job, stack, pre, heads,
        inl, mark, rest, skip, eh, ew, kk, ih)
    case T.KInl{}:
      ih(vs, stack, "inline table is closed", pre, heads, {==}, kk)
    case T.KAots{+pp, +es}:
      gd.wk.arr(T.tree.sub.dot(T.tree.sub.job(mark, job)), pp, es, name, vs, job, stack, pre, heads,
        inl, rest, skip, eh, ew, kk, ih)
    case T.KNo{+why}:
      ih(vs, stack, why, pre, heads, gd.why(why, vs, pre, eh), kk)

# a navigation step, unless the walk has failed
def gd.wk.step(
  +bad: String,
  +name: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +mark: Bool,
  rest: List<&2, String>,
  +skip: U32,
  +ew: {L2.gd.ifok(String.is_empty(bad), T.wf.go(vs, T.WfRows{pre})) == True{} : Bool},
  +et: {T.wf.text(name) == True{} : Bool},
  kk: gd.K(stack, pre),
  ih: gd.wk.IH(rest, job, inl, skip)
) -> {L2.gd.end(T.tree.walk(rest, T.tree.sub(name, T.Tw{vs, job, stack, bad, pre, heads, inl}, mark),
  skip)) == True{} : Bool}:
  match bad:
    case SNil{}:
      gd.wk.sub(T.rows.look(vs, name), name, vs, job, stack, pre, heads, inl, mark, rest, skip,
        gd.lk.ok(vs, pre, name, ew), ew, et, kk, ih)
    case SCon{+hh, +tt}:
      ih(vs, stack, SCon{hh, tt}, pre, heads, {==}, kk)

# a value a key may hold is well-formed as a pair's value under any name
def gd.vok.pv(
  vv: T.Val,
  +pre: String,
  +name: String,
  +ej: {L2.gd.vok(vv) == True{} : Bool}
) -> {gd.pv(pre, name, vv) == True{} : Bool}:
  match vv:
    case T.VHead{pp, rr}:
      Eq.bit.absurd(&2, {gd.pv(pre, name, T.VHead{pp, rr}) == True{} : Bool}, ej)
    case T.VAots{pp, rr}:
      Eq.bit.absurd(&2, {gd.pv(pre, name, T.VAots{pp, rr}) == True{} : Bool}, ej)
    case T.VArr{_i}:
      ej
    case T.VInl{_r}:
      ej
    case T.VStr{_a}:
      ej
    case T.VSpan{_a, _b}:
      ej
    case T.VInt{_a, _b}:
      ej
    case T.VFlo{_a, _b}:
      ej
    case T.VBool{_a}:
      ej
    case T.VWhen{_a}:
      ej
    case T.VAot{_a, _b}:
      ej
    case T.VPair{_a, _b}:
      ej

# a value put: a duplicate key fails, a fresh one goes in front
def gd.wk.put(
  hit: T.Hit,
  +name: String,
  +vs: List<&2, T.Val>,
  +val: T.Val,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +eg: {T.get(vs, name) == hit : T.Hit},
  +ev: {gd.pv(pre, name, val) == True{} : Bool},
  +ew: {T.wf.go(vs, T.WfRows{pre}) == True{} : Bool},
  +et: {T.wf.text(name) == True{} : Bool},
  kk: gd.K(stack, pre)
) -> {L2.gd.end(T.tree.leaf.put(hit, name, vs, val, stack, "", heads)) == True{} : Bool}:
  match hit:
    case T.Found{_v}:
      kk(vs, "duplicate key", heads, {==})
    case T.Miss{}:
      kk(T.VPair{name, val} <> vs, "", heads,
        gd.pr.mk(pre, name, val, vs,
          gd.tt(T.wf.text(name), T.wf.fresh(T.get(vs, name)), et,
            Equal.cong(T.Hit, Bool, hh => T.wf.fresh(hh), T.get(vs, name), T.Miss{}, eg)),
          ev, ew))

# a [table] header on a table only made on the way: defined unless defined
def gd.wk.dh(
  seen: Bool,
  +name: String,
  +vs: List<&2, T.Val>,
  +rows: List<&2, T.Val>,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +er: {T.wf.go(rows, T.WfRows{T.tree.pre(pre, name)}) == True{} : Bool},
  +ew: {T.wf.go(vs, T.WfRows{pre}) == True{} : Bool},
  kk: gd.K(stack, pre)
) -> {L2.gd.end(T.tree.leaf.def.head(seen, name, vs, rows, stack, "", T.tree.pre(pre, name), heads))
  == True{} : Bool}:
  match seen:
    case True{}:
      kk(vs, "duplicate table", heads, {==})
    case False{}:
      kk(T.rows.repl(vs, name, T.VHead{T.tree.pre(pre, name), rows}), "",
        T.heads.by.head(T.tree.pre(pre, name)) <> heads,
        gd.repl.ok(vs, pre, name, T.VHead{T.tree.pre(pre, name), rows}, ew,
          gd.tt(T.str.eq(T.tree.pre(pre, name), T.tree.pre(pre, name)),
            T.wf.go(rows, T.WfRows{T.tree.pre(pre, name)}), M7.str.eq.self(T.tree.pre(pre, name)), er)))

# a [table] header's last segment
def gd.wk.def(
  hit: T.Look,
  +name: String,
  +vs: List<&2, T.Val>,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +eh: {gd.lk(T.get(vs, name), pre, name, hit) == True{} : Bool},
  +ew: {T.wf.go(vs, T.WfRows{pre}) == True{} : Bool},
  +et: {T.wf.text(name) == True{} : Bool},
  kk: gd.K(stack, pre)
) -> {L2.gd.end(T.tree.leaf.def.hit(hit, name, vs, stack, "", T.tree.pre(pre, name), heads))
  == True{} : Bool}:
  match hit:
    case T.KMiss{}:
      kk(T.VPair{name, T.VHead{T.tree.pre(pre, name), []}} <> vs, "",
        T.heads.by.head(T.tree.pre(pre, name)) <> heads,
        gd.pr.mk(pre, name, T.VHead{T.tree.pre(pre, name), []}, vs,
          gd.tt(T.wf.text(name), T.wf.fresh(T.get(vs, name)), et, eh),
          gd.tt(T.str.eq(T.tree.pre(pre, name), T.tree.pre(pre, name)), True{},
            M7.str.eq.self(T.tree.pre(pre, name)), {==}),
          ew))
    case T.KHead{+pp, +rows}:
      gd.wk.dh(T.heads.has(heads, T.tree.pre(pre, name)), name, vs, rows, stack, pre, heads,
        gd.at.path(pp, T.tree.pre(pre, name), rows,
          M3.str.eq.true(pp, T.tree.pre(pre, name),
            gd.l(T.str.eq(pp, T.tree.pre(pre, name)), T.wf.go(rows, T.WfRows{pp}), eh)),
          gd.r(T.str.eq(pp, T.tree.pre(pre, name)), T.wf.go(rows, T.WfRows{pp}), eh)),
        ew, kk)
    case T.KInl{}:
      kk(vs, "inline table is closed", heads, {==})
    case T.KAots{_p, _e}:
      kk(vs, "not a table", heads, {==})
    case T.KNo{+why}:
      kk(vs, why, heads, gd.why(why, vs, pre, eh))

# an [[array]] header's last segment
def gd.wk.aot(
  hit: T.Look,
  +name: String,
  +vs: List<&2, T.Val>,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +eh: {gd.lk(T.get(vs, name), pre, name, hit) == True{} : Bool},
  +ew: {T.wf.go(vs, T.WfRows{pre}) == True{} : Bool},
  +et: {T.wf.text(name) == True{} : Bool},
  kk: gd.K(stack, pre)
) -> {L2.gd.end(T.tree.leaf.aot.hit(hit, name, vs, stack, "", T.tree.pre(pre, name), heads))
  == True{} : Bool}:
  match hit:
    case T.KMiss{}:
      kk(T.VPair{name, T.VAots{T.tree.pre(pre, name), [T.VAot{T.tree.pre(pre, name), []}]}} <> vs, "",
        heads,
        gd.pr.mk(pre, name, T.VAots{T.tree.pre(pre, name), [T.VAot{T.tree.pre(pre, name), []}]}, vs,
          gd.tt(T.wf.text(name), T.wf.fresh(T.get(vs, name)), et, eh),
          gd.tt(True{}, Bool.and(T.str.eq(T.tree.pre(pre, name), T.tree.pre(pre, name)),
            T.wf.go([T.VAot{T.tree.pre(pre, name), []}], T.WfElems{T.tree.pre(pre, name)})), {==},
            gd.tt(T.str.eq(T.tree.pre(pre, name), T.tree.pre(pre, name)),
              T.wf.go([T.VAot{T.tree.pre(pre, name), []}], T.WfElems{T.tree.pre(pre, name)}),
              M7.str.eq.self(T.tree.pre(pre, name)),
              gd.el.mk(T.tree.pre(pre, name), [], [], {==}, {==}))),
          ew))
    case T.KAots{+pp, +es}:
      kk(T.rows.repl(vs, name, T.VAots{T.tree.pre(pre, name), T.VAot{T.tree.pre(pre, name), []} <> es}),
        "", T.heads.drop(heads, String.append(T.tree.pre(pre, name), ".")),
        gd.repl.ok(vs, pre, name, T.VAots{T.tree.pre(pre, name), T.VAot{T.tree.pre(pre, name), []} <> es},
          ew,
          gd.tt(True{}, Bool.and(T.str.eq(T.tree.pre(pre, name), T.tree.pre(pre, name)),
            T.wf.go(T.VAot{T.tree.pre(pre, name), []} <> es, T.WfElems{T.tree.pre(pre, name)})), {==},
            gd.tt(T.str.eq(T.tree.pre(pre, name), T.tree.pre(pre, name)),
              T.wf.go(T.VAot{T.tree.pre(pre, name), []} <> es, T.WfElems{T.tree.pre(pre, name)}),
              M7.str.eq.self(T.tree.pre(pre, name)),
              gd.el.mk(T.tree.pre(pre, name), [], es, {==},
                gd.el.path(pp, T.tree.pre(pre, name), es,
                  M3.str.eq.true(pp, T.tree.pre(pre, name),
                    gd.l(T.str.eq(pp, T.tree.pre(pre, name)), T.wf.go(es, T.WfElems{pp}),
                      gd.r(Bool.not(List.is_empty(&2, T.Val, es)),
                        Bool.and(T.str.eq(pp, T.tree.pre(pre, name)), T.wf.go(es, T.WfElems{pp})), eh))),
                  gd.r(T.str.eq(pp, T.tree.pre(pre, name)), T.wf.go(es, T.WfElems{pp}),
                    gd.r(Bool.not(List.is_empty(&2, T.Val, es)),
                      Bool.and(T.str.eq(pp, T.tree.pre(pre, name)), T.wf.go(es, T.WfElems{pp})),
                      eh))))))))
    case T.KHead{_p, _r}:
      kk(vs, "not a table", heads, {==})
    case T.KInl{}:
      kk(vs, "inline table is closed", heads, {==})
    case T.KNo{+why}:
      kk(vs, why, heads, gd.why(why, vs, pre, eh))

# the job at the end of the path
def gd.wk.job(
  job: T.Job,
  +name: String,
  +vs: List<&2, T.Val>,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +ej: {L2.gd.job(job) == True{} : Bool},
  +ew: {T.wf.go(vs, T.WfRows{pre}) == True{} : Bool},
  +et: {T.wf.text(name) == True{} : Bool},
  kk: gd.K(stack, pre)
) -> {L2.gd.end(T.tree.leaf.job(job, name, vs, stack, "", pre, heads)) == True{} : Bool}:
  match job:
    case T.JPut{+val}:
      gd.wk.put(T.get(vs, name), name, vs, val, stack, pre, heads, {==}, gd.vok.pv(val, pre, name, ej), ew,
        et, kk)
    case T.JDef{}:
      gd.wk.def(T.rows.look(vs, name), name, vs, stack, pre, heads, gd.lk.ok(vs, pre, name, ew), ew, et, kk)
    case T.JAot{}:
      gd.wk.aot(T.rows.look(vs, name), name, vs, stack, pre, heads, gd.lk.ok(vs, pre, name, ew), ew, et, kk)

# the last segment, unless the walk has failed
def gd.wk.leaf(
  +bad: String,
  +name: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +ej: {L2.gd.job(job) == True{} : Bool},
  +ew: {L2.gd.ifok(String.is_empty(bad), T.wf.go(vs, T.WfRows{pre})) == True{} : Bool},
  +et: {T.wf.text(name) == True{} : Bool},
  kk: gd.K(stack, pre)
) -> {L2.gd.end(T.tree.leaf(name, T.Tw{vs, job, stack, bad, pre, heads, inl})) == True{} : Bool}:
  match bad:
    case SNil{}:
      gd.wk.job(job, name, vs, stack, pre, heads, ej, ew, et, kk)
    case SCon{+hh, +tt}:
      kk(vs, SCon{hh, tt}, heads, {==})

# an error is never the empty text
def gd.err.ne(+bad: String) -> {String.is_empty(T.err.first(bad, "empty key")) == False{} : Bool}:
  match bad:
    case SNil{}:
      {==}
    case SCon{_h, _t}:
      {==}

# the walk, by induction on the path
def gd.wk(
  path: List<&2, String>,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +bad: String,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +skip: U32,
  +ep: {L2.gd.segs(path) == True{} : Bool},
  +ej: {L2.gd.job(job) == True{} : Bool},
  +ew: {L2.gd.ifok(String.is_empty(bad), T.wf.go(vs, T.WfRows{pre})) == True{} : Bool},
  kk: gd.K(stack, pre)
) -> {L2.gd.end(T.tree.walk(path, T.Tw{vs, job, stack, bad, pre, heads, inl}, skip)) == True{} : Bool}:
  match path:
    case []:
      kk(vs, T.err.first(bad, "empty key"), heads,
        gd.off(String.is_empty(T.err.first(bad, "empty key")), T.wf.go(vs, T.WfRows{pre}), gd.err.ne(bad)))
    case +name <> +rest:
      match rest:
        case []:
          gd.wk.leaf(bad, name, vs, job, stack, pre, heads, inl, ej, ew,
            gd.l(T.wf.text(name), L2.gd.segs([]), ep), kk)
        case +r1 <> +r2:
          gd.wk.step(bad, name, vs, job, stack, pre, heads, inl, U32.is_zero(skip), r1 <> r2, T.path.dec(skip),
            ew, gd.l(T.wf.text(name), L2.gd.segs(r1 <> r2), ep), kk,
            v2 => s2 => b2 => p2 => h2 => e2 => k2 => gd.wk(r1 <> r2, v2, job, s2, b2, p2, h2, inl, T.path.dec(skip),
              gd.r(T.wf.text(name), L2.gd.segs(r1 <> r2), ep), ej, e2, k2))

def L2.gd_walk(path, rows, job, bad, heads, inl, skip, ew, ep, ej):
  gd.wk(path, rows, job, [], bad, "", heads, inl, skip, ep, ej, ew, gd.k.root())

# WP-R3: the scanner's steps. A state is taken apart once; each step that
# only moves the lex state, back, qkind, the escape's digits or arrtab leaves
# good exactly as it was, and the others change one part of it.

# the parts of gd.lx
def gd.lx.h(
  +h: List<&2, String>,
  +p: List<&2, String>,
  +b: List<&2, Char>,
  +s: List<&2, T.Ctx>,
  +o: T.Hold,
  +ee: {L2.gd.lx(h, p, b, s, o) == True{} : Bool}
) -> {L2.gd.segs(h) == True{} : Bool}:
  gd.l(L2.gd.segs(h), Bool.and(L2.gd.segs(p), Bool.and(L2.gd.cs(b), Bool.and(L2.gd.keys(s),
    L2.gd.hold(o)))), ee)

def gd.lx.p1(
  +h: List<&2, String>,
  +p: List<&2, String>,
  +b: List<&2, Char>,
  +s: List<&2, T.Ctx>,
  +o: T.Hold,
  +ee: {L2.gd.lx(h, p, b, s, o) == True{} : Bool}
) -> {Bool.and(L2.gd.segs(p), Bool.and(L2.gd.cs(b), Bool.and(L2.gd.keys(s), L2.gd.hold(o))))
    == True{} : Bool}:
  gd.r(L2.gd.segs(h), Bool.and(L2.gd.segs(p), Bool.and(L2.gd.cs(b), Bool.and(L2.gd.keys(s),
    L2.gd.hold(o)))), ee)

def gd.lx.p(
  +h: List<&2, String>,
  +p: List<&2, String>,
  +b: List<&2, Char>,
  +s: List<&2, T.Ctx>,
  +o: T.Hold,
  +ee: {L2.gd.lx(h, p, b, s, o) == True{} : Bool}
) -> {L2.gd.segs(p) == True{} : Bool}:
  gd.l(L2.gd.segs(p), Bool.and(L2.gd.cs(b), Bool.and(L2.gd.keys(s), L2.gd.hold(o))),
    gd.lx.p1(h, p, b, s, o, ee))

def gd.lx.b1(
  +h: List<&2, String>,
  +p: List<&2, String>,
  +b: List<&2, Char>,
  +s: List<&2, T.Ctx>,
  +o: T.Hold,
  +ee: {L2.gd.lx(h, p, b, s, o) == True{} : Bool}
) -> {Bool.and(L2.gd.cs(b), Bool.and(L2.gd.keys(s), L2.gd.hold(o))) == True{} : Bool}:
  gd.r(L2.gd.segs(p), Bool.and(L2.gd.cs(b), Bool.and(L2.gd.keys(s), L2.gd.hold(o))),
    gd.lx.p1(h, p, b, s, o, ee))

def gd.lx.b(
  +h: List<&2, String>,
  +p: List<&2, String>,
  +b: List<&2, Char>,
  +s: List<&2, T.Ctx>,
  +o: T.Hold,
  +ee: {L2.gd.lx(h, p, b, s, o) == True{} : Bool}
) -> {L2.gd.cs(b) == True{} : Bool}:
  gd.l(L2.gd.cs(b), Bool.and(L2.gd.keys(s), L2.gd.hold(o)), gd.lx.b1(h, p, b, s, o, ee))

def gd.lx.s1(
  +h: List<&2, String>,
  +p: List<&2, String>,
  +b: List<&2, Char>,
  +s: List<&2, T.Ctx>,
  +o: T.Hold,
  +ee: {L2.gd.lx(h, p, b, s, o) == True{} : Bool}
) -> {Bool.and(L2.gd.keys(s), L2.gd.hold(o)) == True{} : Bool}:
  gd.r(L2.gd.cs(b), Bool.and(L2.gd.keys(s), L2.gd.hold(o)), gd.lx.b1(h, p, b, s, o, ee))

def gd.lx.s(
  +h: List<&2, String>,
  +p: List<&2, String>,
  +b: List<&2, Char>,
  +s: List<&2, T.Ctx>,
  +o: T.Hold,
  +ee: {L2.gd.lx(h, p, b, s, o) == True{} : Bool}
) -> {L2.gd.keys(s) == True{} : Bool}:
  gd.l(L2.gd.keys(s), L2.gd.hold(o), gd.lx.s1(h, p, b, s, o, ee))

# and put back together
def gd.lx.mk(
  +h: List<&2, String>,
  +p: List<&2, String>,
  +b: List<&2, Char>,
  +s: List<&2, T.Ctx>,
  +o: T.Hold,
  +eh: {L2.gd.segs(h) == True{} : Bool},
  +ep: {L2.gd.segs(p) == True{} : Bool},
  +eb: {L2.gd.cs(b) == True{} : Bool},
  +es: {L2.gd.keys(s) == True{} : Bool},
  +eo: {L2.gd.hold(o) == True{} : Bool}
) -> {L2.gd.lx(h, p, b, s, o) == True{} : Bool}:
  gd.tt(L2.gd.segs(h), Bool.and(L2.gd.segs(p), Bool.and(L2.gd.cs(b), Bool.and(L2.gd.keys(s),
    L2.gd.hold(o)))), eh,
    gd.tt(L2.gd.segs(p), Bool.and(L2.gd.cs(b), Bool.and(L2.gd.keys(s), L2.gd.hold(o))), ep,
      gd.tt(L2.gd.cs(b), Bool.and(L2.gd.keys(s), L2.gd.hold(o)), eb,
        gd.tt(L2.gd.keys(s), L2.gd.hold(o), es, eo))))

# a wf.then whose test and rest answered True
def gd.then(
  aa: Bool,
  mm: Unit -> Bool,
  +ea: {aa == True{} : Bool},
  +em: {mm(Unit{}) == True{} : Bool}
) -> {T.wf.then(aa, mm) == True{} : Bool}:
  match aa:
    case True{}:
      em
    case False{}:
      Eq.bit.absurd(&2, {T.wf.then(False{}, mm) == True{} : Bool}, ea)

# a buffer of scalar values read out, in order, onto a text of them
def gd.bs.ok(
  buf: List<&2, Char>,
  +acc: String,
  +eb: {L2.gd.cs(buf) == True{} : Bool},
  +ea: {T.wf.text(acc) == True{} : Bool}
) -> {T.wf.text(T.buf.str.go(buf, acc)) == True{} : Bool}:
  match buf:
    case []:
      ea
    case +h <> +t:
      gd.bs.ok(t, SCon{h, acc}, gd.r(T.wf.char(h), L2.gd.cs(t), eb),
        gd.then(T.wf.char(h), _u => T.wf.text(acc), gd.l(T.wf.char(h), L2.gd.cs(t), eb), ea))

# segments of scalar values reversed onto more of them
def gd.segs.rev(
  xs: List<&2, String>,
  +acc: List<&2, String>,
  +ex: {L2.gd.segs(xs) == True{} : Bool},
  +ea: {L2.gd.segs(acc) == True{} : Bool}
) -> {L2.gd.segs(List.reverse.go(&2, String, xs, acc)) == True{} : Bool}:
  match xs:
    case []:
      ea
    case +h <> +t:
      gd.segs.rev(t, h <> acc, gd.r(T.wf.text(h), L2.gd.segs(t), ex),
        gd.tt(T.wf.text(h), L2.gd.segs(acc), gd.l(T.wf.text(h), L2.gd.segs(t), ex), ea))

# the rows while the scanner has not failed, without the frames
def gd.ifok.l(
  ok: Bool,
  xx: Bool,
  yy: Bool,
  +ee: {L2.gd.ifok(ok, Bool.and(xx, yy)) == True{} : Bool}
) -> {L2.gd.ifok(ok, xx) == True{} : Bool}:
  match ok:
    case True{}:
      gd.l(xx, yy, ee)
    case False{}:
      {==}

# a failed scanner's first error is no empty text
def gd.err.ne2(
  +bad: String,
  +why: String,
  +ew: {String.is_empty(why) == False{} : Bool}
) -> {String.is_empty(T.err.first(bad, why)) == False{} : Bool}:
  match bad:
    case SNil{}:
      ew
    case SCon{_h, _t}:
      {==}

# a step that fails
def gd.g.err(
  +st: T.St,
  +why: String,
  +ew: {String.is_empty(why) == False{} : Bool},
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.st.err(st, why)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.tt(L2.gd.tr(T.err.first(bad, why), rows, stack), L2.gd.lx(here, parts, buf, stack, T.HNone{}),
        gd.off(String.is_empty(T.err.first(bad, why)),
          Bool.and(T.wf.go(rows, T.WfRows{""}), L2.gd.vals(stack)), gd.err.ne2(bad, why, ew)),
        gd.lx.mk(here, parts, buf, stack, T.HNone{},
          gd.lx.h(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack),
            L2.gd.lx(here, parts, buf, stack, hold), eg)),
          gd.lx.p(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack),
            L2.gd.lx(here, parts, buf, stack, hold), eg)),
          gd.lx.b(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack),
            L2.gd.lx(here, parts, buf, stack, hold), eg)),
          gd.lx.s(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack),
            L2.gd.lx(here, parts, buf, stack, hold), eg)),
          {==}))

# a step that only moves the lex state
def gd.g.lex(
  +st: T.St,
  +lex2: T.Lex,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.st.lex(st, lex2)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      eg

# a step that pushes a character of scalar value
def gd.g.push(
  +st: T.St,
  +cc: Char,
  +lex2: T.Lex,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.st.push(st, cc, lex2)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.tt(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, cc <> buf, stack, hold),
        gd.l(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg),
        gd.lx.mk(here, parts, cc <> buf, stack, hold,
          gd.lx.h(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack),
            L2.gd.lx(here, parts, buf, stack, hold), eg)),
          gd.lx.p(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack),
            L2.gd.lx(here, parts, buf, stack, hold), eg)),
          gd.tt(T.wf.char(cc), L2.gd.cs(buf), ec,
            gd.lx.b(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack),
              L2.gd.lx(here, parts, buf, stack, hold), eg))),
          gd.lx.s(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack),
            L2.gd.lx(here, parts, buf, stack, hold), eg)),
          gd.r(L2.gd.keys(stack), L2.gd.hold(hold),
            gd.lx.s1(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack),
              L2.gd.lx(here, parts, buf, stack, hold), eg)))))

# a step that ends a segment: the buffer joins the key's segments
def gd.g.seg(
  +st: T.St,
  +lex2: T.Lex,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.seg.push(st, lex2)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.tt(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, T.buf.str(buf) <> parts, [], stack, hold),
        gd.l(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg),
        gd.lx.mk(here, T.buf.str(buf) <> parts, [], stack, hold,
          gd.lx.h(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack),
            L2.gd.lx(here, parts, buf, stack, hold), eg)),
          gd.tt(T.wf.text(T.buf.str(buf)), L2.gd.segs(parts),
            gd.bs.ok(buf, "", gd.lx.b(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack),
              L2.gd.lx(here, parts, buf, stack, hold), eg)), {==}),
            gd.lx.p(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack),
              L2.gd.lx(here, parts, buf, stack, hold), eg))),
          {==},
          gd.lx.s(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack),
            L2.gd.lx(here, parts, buf, stack, hold), eg)),
          gd.r(L2.gd.keys(stack), L2.gd.hold(hold),
            gd.lx.s1(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack),
              L2.gd.lx(here, parts, buf, stack, hold), eg)))))

# a step that opens a quoted segment with an empty buffer
def gd.g.qkey(
  +st: T.St,
  +kind: T.QKind,
  +lex2: T.Lex,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.qkey(st, kind, lex2)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.tt(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, [], stack, hold),
        gd.l(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg),
        gd.lx.mk(here, parts, [], stack, hold,
          gd.lx.h(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack),
            L2.gd.lx(here, parts, buf, stack, hold), eg)),
          gd.lx.p(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack),
            L2.gd.lx(here, parts, buf, stack, hold), eg)),
          {==},
          gd.lx.s(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack),
            L2.gd.lx(here, parts, buf, stack, hold), eg)),
          gd.r(L2.gd.keys(stack), L2.gd.hold(hold),
            gd.lx.s1(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack),
              L2.gd.lx(here, parts, buf, stack, hold), eg)))))

# the frames and the error stay out of the rows' half
def gd.ifok.t(
  ok: Bool,
  xx: Bool,
  +ee: {L2.gd.ifok(ok, xx) == True{} : Bool}
) -> {L2.gd.ifok(ok, Bool.and(xx, True{})) == True{} : Bool}:
  match ok:
    case True{}:
      gd.tt(xx, True{}, ee, {==})
    case False{}:
      {==}

# a header's walk done: the root it returned, the header's path as the
# current table, and nothing pending
def gd.g.apply(
  end: T.End,
  +segs: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +uni: U32,
  +left: U32,
  +lead: Bool,
  +ee: {L2.gd.end(end) == True{} : Bool},
  +es: {L2.gd.segs(segs) == True{} : Bool}
) -> {L2.good(T.head.apply(end, segs, back, qkind, uni, left, lead)) == True{} : Bool}:
  match end:
    case T.End{+vs, +bad, +hs}:
      gd.tt(L2.gd.tr(bad, vs, []), L2.gd.lx(segs, [], [], [], T.HNone{}),
        gd.ifok.t(String.is_empty(bad), T.wf.go(vs, T.WfRows{""}), ee),
        gd.tt(L2.gd.segs(segs), True{}, es, {==}))

# a header opens a table or an array of tables
def gd.g.job(
  arr: Bool,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +segs: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +uni: U32,
  +left: U32,
  +lead: Bool,
  +ew: {L2.gd.ifok(String.is_empty(bad), T.wf.go(rows, T.WfRows{""})) == True{} : Bool},
  +es: {L2.gd.segs(segs) == True{} : Bool}
) -> {L2.good(T.head.job(arr, bad, rows, heads, segs, back, qkind, uni, left, lead)) == True{} : Bool}:
  match arr:
    case True{}:
      gd.g.apply(T.tree.walk(segs, T.Tw{rows, T.JAot{}, [], bad, "", heads, False{}}, 0), segs, back, qkind,
        uni, left, lead, L2.gd_walk(segs, rows, T.JAot{}, bad, heads, False{}, 0, ew, es, {==}), es)
    case False{}:
      gd.g.apply(T.tree.walk(segs, T.Tw{rows, T.JDef{}, [], bad, "", heads, False{}}, 0), segs, back, qkind,
        uni, left, lead, L2.gd_walk(segs, rows, T.JDef{}, bad, heads, False{}, 0, ew, es, {==}), es)

# the header's walk runs on the state's rows
def gd.g.on(
  +st: T.St,
  +segs: List<&2, String>,
  +eg: {L2.good(st) == True{} : Bool},
  +es: {L2.gd.segs(segs) == True{} : Bool}
) -> {L2.good(T.head.on(st, segs)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.g.job(arrtab, bad, rows, heads, segs, back, qkind, uni, left, lead,
        gd.ifok.l(String.is_empty(bad), T.wf.go(rows, T.WfRows{""}), L2.gd.vals(stack),
          gd.l(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)),
        es)

# a header with no segment fails
def gd.g.go(
  empty: Bool,
  +st: T.St,
  +segs: List<&2, String>,
  +eg: {L2.good(st) == True{} : Bool},
  +es: {L2.gd.segs(segs) == True{} : Bool}
) -> {L2.good(T.head.go(empty, st, segs)) == True{} : Bool}:
  match empty:
    case True{}:
      gd.g.err(st, "empty key", {==}, eg)
    case False{}:
      gd.g.on(st, segs, eg, es)

# the key's segments, in order, name the header
def gd.g.use(+st: T.St, +eg: {L2.good(st) == True{} : Bool}) -> {L2.good(T.head.use(st)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.g.go(List.is_empty(&2, String, parts),
        T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead},
        List.reverse(&2, String, parts), eg,
        gd.segs.rev(parts, [], gd.lx.p(here, parts, buf, stack, hold,
          gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)), {==}))

# the buffer is the last segment when it holds one
def gd.g.finbuf(
  empty: Bool,
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.head.fin.buf(empty, st)) == True{} : Bool}:
  match empty:
    case True{}:
      gd.g.use(st, eg)
    case False{}:
      gd.g.use(T.seg.push(st, T.LTop{}), gd.g.seg(st, T.LTop{}, eg))

# a header closed
def gd.g.fin(+st: T.St, +eg: {L2.good(st) == True{} : Bool}) -> {L2.good(T.head.fin(st)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.g.finbuf(List.is_empty(&2, Char, buf),
        T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead}, eg)

# ] with an array of tables waits for the second
def gd.g.close2(
  arr: Bool,
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.head.close2(arr, st)) == True{} : Bool}:
  match arr:
    case True{}:
      gd.g.lex(st, T.LHeadR{}, eg)
    case False{}:
      gd.g.fin(st, eg)

# ] pushes the open segment first
def gd.g.closego(
  empty: Bool,
  arr: Bool,
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.head.close.go(empty, arr, st)) == True{} : Bool}:
  match empty:
    case True{}:
      gd.g.close2(arr, st, eg)
    case False{}:
      gd.g.close2(arr, T.seg.push(st, T.LHead{}), gd.g.seg(st, T.LHead{}, eg))

# ]
def gd.g.close(
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.head.close(st)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.g.closego(List.is_empty(&2, Char, buf), arrtab,
        T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead}, eg)

# a comment in a header, or a refusal
def gd.g.hash(
  hash: Bool,
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.head.hash(hash, st)) == True{} : Bool}:
  match hash:
    case True{}:
      match st:
        case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
          +arrtab, +lead}:
          eg
    case False{}:
      gd.g.err(st, "invalid header", {==}, eg)

# a quote opens a segment only at the start
def gd.g.quotego(
  fresh: Bool,
  +st: T.St,
  +kind: T.QKind,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.head.quote.go(fresh, st, kind)) == True{} : Bool}:
  match fresh:
    case True{}:
      gd.g.qkey(st, kind, T.LHeadQ{}, eg)
    case False{}:
      gd.g.err(st, "invalid header", {==}, eg)

def gd.g.quote(
  +st: T.St,
  +kind: T.QKind,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.head.quote(st, kind)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.g.quotego(Bool.and(List.is_empty(&2, Char, buf), List.is_empty(&2, String, parts)),
        T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead},
        kind, eg)

# [[ marks an array of tables once, at the start
def gd.g.br2(
  once: Bool,
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.head.br2(once, st)) == True{} : Bool}:
  match once:
    case False{}:
      gd.g.err(st, "invalid header", {==}, eg)
    case True{}:
      match st:
        case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
          +arrtab, +lead}:
          eg

def gd.g.brgo(
  fresh: Bool,
  once: Bool,
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.head.br.go(fresh, once, st)) == True{} : Bool}:
  match fresh:
    case False{}:
      gd.g.err(st, "invalid header", {==}, eg)
    case True{}:
      gd.g.br2(once, st, eg)

def gd.g.br(
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.head.br(st)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.g.brgo(Bool.and(List.is_empty(&2, String, parts), List.is_empty(&2, Char, buf)), Bool.not(arrtab),
        T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead}, eg)

# a bare character: a segment goes on, or starts
def gd.g.chgo(
  gap: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.head.ch.go(gap, st, cc)) == True{} : Bool}:
  match gap:
    case True{}:
      gd.g.err(st, "invalid header", {==}, eg)
    case False{}:
      gd.g.push(st, cc, T.LHead{}, eg, ec)

def gd.g.ch(
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.head.ch(st, cc)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.g.chgo(Bool.and(Bool.not(List.is_empty(&2, String, parts)), List.is_empty(&2, Char, buf)),
        T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead},
        cc, eg, ec)

# blank space ends an open segment
def gd.g.gapgo(
  empty: Bool,
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.head.gap.go(empty, st)) == True{} : Bool}:
  match empty:
    case True{}:
      gd.g.lex(st, T.LHeadDot{}, eg)
    case False{}:
      gd.g.seg(st, T.LHeadGap{}, eg)

def gd.g.gap(
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.head.gap(st)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.g.gapgo(List.is_empty(&2, Char, buf),
        T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead}, eg)

# a dot ends the open segment
def gd.g.dot3(
  empty: Bool,
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.head.dot3(empty, st)) == True{} : Bool}:
  match empty:
    case True{}:
      gd.g.err(st, "empty key", {==}, eg)
    case False{}:
      gd.g.seg(st, T.LHeadDot{}, eg)

def gd.g.dot2(
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.head.dot2(st)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.g.dot3(List.is_empty(&2, Char, buf),
        T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead}, eg)

# LHead's dispatch, one test at a time
def gd.g.hlit(
  lit: Bool,
  hash: Bool,
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.head.lit(lit, hash, st)) == True{} : Bool}:
  match lit:
    case True{}:
      gd.g.quote(st, T.QLit{}, eg)
    case False{}:
      gd.g.hash(hash, st, eg)

def gd.g.hq(
  qq: Bool,
  lit: Bool,
  hash: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.head.q(qq, lit, hash, st, cc)) == True{} : Bool}:
  match qq:
    case True{}:
      gd.g.quote(st, T.QBasic{}, eg)
    case False{}:
      gd.g.hlit(lit, hash, st, eg)

def gd.g.hend(
  end: Bool,
  qq: Bool,
  lit: Bool,
  hash: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.head.end(end, qq, lit, hash, st, cc)) == True{} : Bool}:
  match end:
    case True{}:
      gd.g.close(st, eg)
    case False{}:
      gd.g.hq(qq, lit, hash, st, cc, eg)

def gd.g.hdot(
  dot: Bool,
  end: Bool,
  qq: Bool,
  lit: Bool,
  hash: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.head.dot(dot, end, qq, lit, hash, st, cc)) == True{} : Bool}:
  match dot:
    case True{}:
      gd.g.dot2(st, eg)
    case False{}:
      gd.g.hend(end, qq, lit, hash, st, cc, eg)

def gd.g.hsp(
  sp: Bool,
  dot: Bool,
  end: Bool,
  qq: Bool,
  lit: Bool,
  hash: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.head.sp(sp, dot, end, qq, lit, hash, st, cc)) == True{} : Bool}:
  match sp:
    case True{}:
      gd.g.gap(st, eg)
    case False{}:
      gd.g.hdot(dot, end, qq, lit, hash, st, cc, eg)

def gd.g.hbare(
  bare: Bool,
  sp: Bool,
  dot: Bool,
  end: Bool,
  qq: Bool,
  lit: Bool,
  hash: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.head.bare(bare, sp, dot, end, qq, lit, hash, st, cc)) == True{} : Bool}:
  match bare:
    case True{}:
      gd.g.ch(st, cc, eg, ec)
    case False{}:
      gd.g.hsp(sp, dot, end, qq, lit, hash, st, cc, eg)

def gd.g.hgo(
  br: Bool,
  bare: Bool,
  sp: Bool,
  dot: Bool,
  end: Bool,
  qq: Bool,
  lit: Bool,
  hash: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.head.go(br, bare, sp, dot, end, qq, lit, hash, st, cc)) == True{} : Bool}:
  match br:
    case True{}:
      gd.g.br(st, eg)
    case False{}:
      gd.g.hbare(bare, sp, dot, end, qq, lit, hash, st, cc, eg, ec)

# LHead
def gd.g.head(
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.head(st, cc)) == True{} : Bool}:
  gd.g.hgo(Char.is_eq(cc, '['), T.bare.at(cc), T.ch.sp(cc), Char.is_eq(cc, '.'), Char.is_eq(cc, ']'),
    Char.is_eq(cc, '"'), Char.is_eq(cc, '\''), Char.is_eq(cc, '#'), st, cc, eg, ec)

# LHeadGap
def gd.g.hgend(
  end: Bool,
  hash: Bool,
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.hgap.end(end, hash, st)) == True{} : Bool}:
  match end:
    case True{}:
      gd.g.close(st, eg)
    case False{}:
      gd.g.hash(hash, st, eg)

def gd.g.hgdot(
  dot: Bool,
  end: Bool,
  hash: Bool,
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.hgap.dot(dot, end, hash, st)) == True{} : Bool}:
  match dot:
    case True{}:
      gd.g.lex(st, T.LHeadDot{}, eg)
    case False{}:
      gd.g.hgend(end, hash, st, eg)

def gd.g.hgap(
  sp: Bool,
  dot: Bool,
  end: Bool,
  hash: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.hgap(sp, dot, end, hash, st, cc)) == True{} : Bool}:
  match sp:
    case True{}:
      eg
    case False{}:
      gd.g.hgdot(dot, end, hash, st, eg)

# LHeadDot
def gd.g.hdlit(
  lit: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.hdot.lit(lit, st, cc)) == True{} : Bool}:
  match lit:
    case True{}:
      gd.g.qkey(st, T.QLit{}, T.LHeadQ{}, eg)
    case False{}:
      gd.g.err(st, "invalid header", {==}, eg)

def gd.g.hdq(
  qq: Bool,
  lit: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.hdot.q(qq, lit, st, cc)) == True{} : Bool}:
  match qq:
    case True{}:
      gd.g.qkey(st, T.QBasic{}, T.LHeadQ{}, eg)
    case False{}:
      gd.g.hdlit(lit, st, cc, eg)

def gd.g.hdbare(
  bare: Bool,
  qq: Bool,
  lit: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.hdot.bare(bare, qq, lit, st, cc)) == True{} : Bool}:
  match bare:
    case True{}:
      gd.g.push(st, cc, T.LHead{}, eg, ec)
    case False{}:
      gd.g.hdq(qq, lit, st, cc, eg)

def gd.g.hdot2(
  sp: Bool,
  bare: Bool,
  qq: Bool,
  lit: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.hdot(sp, bare, qq, lit, st, cc)) == True{} : Bool}:
  match sp:
    case True{}:
      eg
    case False{}:
      gd.g.hdbare(bare, qq, lit, st, cc, eg, ec)

# LHeadR
def gd.g.hr(
  end: Bool,
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.head.r.go(end, st)) == True{} : Bool}:
  match end:
    case True{}:
      gd.g.fin(st, eg)
    case False{}:
      gd.g.err(st, "invalid header", {==}, eg)

# a quoted segment's character: the closer ends it, a backslash escapes in a
# basic segment, a newline or a control fails, anything else is pushed
def gd.g.kqch(
  bad: Bool,
  +st: T.St,
  +cc: Char,
  +stay: T.Lex,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.kq.char.go(bad, st, cc, stay)) == True{} : Bool}:
  match bad:
    case True{}:
      gd.g.err(st, "invalid control", {==}, eg)
    case False{}:
      gd.g.push(st, cc, stay, eg, ec)

def gd.g.kqnl(
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +stay: T.Lex,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.kq.nl(nl, st, cc, stay)) == True{} : Bool}:
  match nl:
    case True{}:
      gd.g.err(st, "newline in key", {==}, eg)
    case False{}:
      gd.g.kqch(T.str.bad(Char.to_u32(cc), False{}), st, cc, stay, eg, ec)

def gd.g.kqesc(
  basic: Bool,
  +st: T.St,
  +stay: T.Lex,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.kq.esc(basic, st, stay)) == True{} : Bool}:
  match basic:
    case True{}:
      match st:
        case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
          eg
    case False{}:
      gd.g.push(st, '\\', stay, eg, {==})

def gd.g.kqbs(
  bs: Bool,
  basic: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +stay: T.Lex,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.kq.bs(bs, basic, nl, st, cc, stay)) == True{} : Bool}:
  match bs:
    case True{}:
      gd.g.kqesc(basic, st, stay, eg)
    case False{}:
      gd.g.kqnl(nl, st, cc, stay, eg, ec)

def gd.g.kqgo(
  quote: Bool,
  bs: Bool,
  basic: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +back: T.Lex,
  +stay: T.Lex,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.kq.go(quote, bs, basic, nl, st, cc, back, stay)) == True{} : Bool}:
  match quote:
    case True{}:
      gd.g.seg(st, back, eg)
    case False{}:
      gd.g.kqbs(bs, basic, nl, st, cc, stay, eg, ec)

# a quoted segment, a key's or a header's
def gd.g.kq(
  +st: T.St,
  +cc: Char,
  +back2: T.Lex,
  +stay: T.Lex,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.kq(st, cc, back2, stay)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.g.kqgo(Char.is_eq(cc, T.q.char(qkind)), Char.is_eq(cc, '\\'), T.q.basic(qkind), T.ch.nl(cc),
        T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead},
        cc, back2, stay, eg, ec)

# what an escape stands for: a character of scalar value, when it is one
def gd.esc(ee: T.Esc) -> Bool:
  match ee:
    case T.EChar{+c}:
      T.wf.char(c)
    case _:
      True{}

# every escape's character is a scalar value
def gd.e.go(
  qq: Bool,
  bs: Bool,
  nl: Bool,
  sp: Bool,
  bb: Bool,
  tt: Bool,
  nn: Bool,
  ff: Bool,
  rr: Bool,
  uuu: Bool,
  uu: Bool
) -> {gd.esc(T.esc.of.go(qq, bs, bb, tt, nn, ff, rr, uuu, uu, nl, sp)) == True{} : Bool}:
  match qq:
    case True{}:
      {==}
    case False{}:
      match bs:
        case True{}:
          {==}
        case False{}:
          match nl:
            case True{}:
              {==}
            case False{}:
              match sp:
                case True{}:
                  {==}
                case False{}:
                  match bb:
                    case True{}:
                      {==}
                    case False{}:
                      match tt:
                        case True{}:
                          {==}
                        case False{}:
                          match nn:
                            case True{}:
                              {==}
                            case False{}:
                              match ff:
                                case True{}:
                                  {==}
                                case False{}:
                                  match rr:
                                    case True{}:
                                      {==}
                                    case False{}:
                                      match uuu:
                                        case True{}:
                                          {==}
                                        case False{}:
                                          match uu:
                                            case True{}:
                                              {==}
                                            case False{}:
                                              {==}

def gd.e.of(+cc: Char) -> {gd.esc(T.esc.of(cc)) == True{} : Bool}:
  gd.e.go(Char.is_eq(cc, '"'), Char.is_eq(cc, '\\'), T.ch.nl(cc), T.ch.sp(cc), Char.is_eq(cc, 'b'),
    Char.is_eq(cc, 't'), Char.is_eq(cc, 'n'), Char.is_eq(cc, 'f'), Char.is_eq(cc, 'r'), Char.is_eq(cc, 'u'),
    Char.is_eq(cc, 'U'))

# a line-ending backslash belongs to a string only
def gd.g.fold(
  back: T.Lex,
  +st: T.St,
  +saw: Bool,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.esc.fold.use(back, st, saw)) == True{} : Bool}:
  match back:
    case T.LTop{}:
      gd.g.err(st, "invalid escape", {==}, eg)
    case T.LLine{}:
      gd.g.err(st, "invalid escape", {==}, eg)
    case T.LKey{}:
      gd.g.err(st, "invalid escape", {==}, eg)
    case T.LKeyDot{}:
      gd.g.err(st, "invalid escape", {==}, eg)
    case T.LAfter{}:
      gd.g.err(st, "invalid escape", {==}, eg)
    case T.LKeyQ{}:
      gd.g.err(st, "invalid escape", {==}, eg)
    case T.LKeyE{}:
      gd.g.err(st, "invalid escape", {==}, eg)
    case T.LKeyU{}:
      gd.g.err(st, "invalid escape", {==}, eg)
    case T.LVal{}:
      gd.g.err(st, "invalid escape", {==}, eg)
    case T.LQ{}:
      gd.g.err(st, "invalid escape", {==}, eg)
    case T.LQ2{}:
      gd.g.err(st, "invalid escape", {==}, eg)
    case T.LStr{}:
      match st:
        case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, qkind, +stack, +hold, +uni, +left,
          +arrtab, +lead}:
          match qkind:
            case T.QMulti{}:
              eg
            case T.QMultiLit{}:
              eg
            case T.QBasic{}:
              gd.g.err(T.St{bad, rows, heads, here, parts, buf, lex, back, T.QBasic{}, stack, hold, uni, left, arrtab,
                lead}, "invalid escape", {==}, eg)
            case T.QLit{}:
              gd.g.err(T.St{bad, rows, heads, here, parts, buf, lex, back, T.QLit{}, stack, hold, uni, left, arrtab,
                lead}, "invalid escape", {==}, eg)
    case T.LEsc{}:
      gd.g.err(st, "invalid escape", {==}, eg)
    case T.LUni{}:
      gd.g.err(st, "invalid escape", {==}, eg)
    case T.LFold{}:
      gd.g.err(st, "invalid escape", {==}, eg)
    case T.LMq{}:
      gd.g.err(st, "invalid escape", {==}, eg)
    case T.LMqEnd{}:
      gd.g.err(st, "invalid escape", {==}, eg)
    case T.LTrim{}:
      gd.g.err(st, "invalid escape", {==}, eg)
    case T.LTrim2{}:
      gd.g.err(st, "invalid escape", {==}, eg)
    case T.LBare{}:
      gd.g.err(st, "invalid escape", {==}, eg)
    case T.LDate{}:
      gd.g.err(st, "invalid escape", {==}, eg)
    case T.LCom{}:
      gd.g.err(st, "invalid escape", {==}, eg)
    case T.LHead{}:
      gd.g.err(st, "invalid escape", {==}, eg)
    case T.LHeadGap{}:
      gd.g.err(st, "invalid escape", {==}, eg)
    case T.LHeadDot{}:
      gd.g.err(st, "invalid escape", {==}, eg)
    case T.LHeadQ{}:
      gd.g.err(st, "invalid escape", {==}, eg)
    case T.LHeadE{}:
      gd.g.err(st, "invalid escape", {==}, eg)
    case T.LHeadU{}:
      gd.g.err(st, "invalid escape", {==}, eg)
    case T.LHeadR{}:
      gd.g.err(st, "invalid escape", {==}, eg)
    case T.LArr{}:
      gd.g.err(st, "invalid escape", {==}, eg)
    case T.LArrC{}:
      gd.g.err(st, "invalid escape", {==}, eg)
    case T.LInl{}:
      gd.g.err(st, "invalid escape", {==}, eg)
    case T.LInlK{}:
      gd.g.err(st, "invalid escape", {==}, eg)
    case T.LInlC{}:
      gd.g.err(st, "invalid escape", {==}, eg)
    case T.LSink{}:
      gd.g.err(st, "invalid escape", {==}, eg)

# an escape applied
def gd.g.esc(
  ee: T.Esc,
  +st: T.St,
  +back: T.Lex,
  +eg: {L2.good(st) == True{} : Bool},
  +ex: {gd.esc(ee) == True{} : Bool}
) -> {L2.good(T.esc.use(ee, st, back)) == True{} : Bool}:
  match ee:
    case T.EChar{+c}:
      gd.g.push(st, c, back, eg, ex)
    case T.EUni{+n}:
      match st:
        case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
          +arrtab, +lead}:
          eg
    case T.EFold{+saw}:
      gd.g.fold(back, st, saw, eg)
    case T.EBad{}:
      gd.g.err(st, "invalid escape", {==}, eg)

# a finished \u escape pushes its character, a scalar value
def gd.g.uon(
  +st: T.St,
  +uu: U32,
  +back: T.Lex,
  +eg: {L2.good(st) == True{} : Bool},
  +eu: {T.uni.ok(uu) == True{} : Bool}
) -> {L2.good(T.uni.finish.on(st, uu, back)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.tt(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, Char.from_u32(uu) <> buf, stack, T.HNone{}),
        gd.l(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg),
        gd.lx.mk(here, parts, Char.from_u32(uu) <> buf, stack, T.HNone{},
          gd.lx.h(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack),
            L2.gd.lx(here, parts, buf, stack, hold), eg)),
          gd.lx.p(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack),
            L2.gd.lx(here, parts, buf, stack, hold), eg)),
          gd.tt(T.wf.char(Char.from_u32(uu)), L2.gd.cs(buf), eu,
            gd.lx.b(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack),
              L2.gd.lx(here, parts, buf, stack, hold), eg))),
          gd.lx.s(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack),
            L2.gd.lx(here, parts, buf, stack, hold), eg)),
          {==}))

def gd.g.ufin(
  ok: Bool,
  +st: T.St,
  +uu: U32,
  +back: T.Lex,
  +eg: {L2.good(st) == True{} : Bool},
  +eo: {T.uni.ok(uu) == ok : Bool}
) -> {L2.good(T.uni.finish(ok, st, uu, back)) == True{} : Bool}:
  match ok:
    case True{}:
      gd.g.uon(st, uu, back, eg, eo)
    case False{}:
      gd.g.err(st, "invalid escape", {==}, eg)

def gd.g.unext(
  last: Bool,
  +st: T.St,
  +uu: U32,
  +back: T.Lex,
  +left: U32,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.uni.next(last, st, uu, back, left)) == True{} : Bool}:
  match last:
    case True{}:
      gd.g.ufin(T.uni.ok(uu), st, uu, back, eg, {==})
    case False{}:
      match st:
        case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
          +arrtab, +lead}:
          eg

def gd.g.ugo(
  ok: Bool,
  +st: T.St,
  +cc: Char,
  +back: T.Lex,
  +uni: U32,
  +left: U32,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.uni.go(ok, st, cc, back, uni, left)) == True{} : Bool}:
  match ok:
    case False{}:
      gd.g.err(st, "invalid escape", {==}, eg)
    case True{}:
      gd.g.unext(U32.is_eq(left, 1), st, U32.add(U32.mul(uni, 16), T.dig.val(cc)), back, left, eg)

# a hex digit of a \u escape
def gd.g.uni(
  +st: T.St,
  +cc: Char,
  +back2: T.Lex,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.uni.step(st, cc, back2)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.g.ugo(T.dig.ok(T.dig.val(cc), 16),
        T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead},
        cc, back2, uni, left, eg)

def L2.gd_header_steps(lex, hl, st, eg, cc, ec):
  match lex:
    case T.LTop{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LTop{}, st, cc)) == True{} : Bool}, hl)
    case T.LLine{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LLine{}, st, cc)) == True{} : Bool}, hl)
    case T.LKey{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LKey{}, st, cc)) == True{} : Bool}, hl)
    case T.LKeyDot{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LKeyDot{}, st, cc)) == True{} : Bool}, hl)
    case T.LAfter{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LAfter{}, st, cc)) == True{} : Bool}, hl)
    case T.LKeyQ{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LKeyQ{}, st, cc)) == True{} : Bool}, hl)
    case T.LKeyE{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LKeyE{}, st, cc)) == True{} : Bool}, hl)
    case T.LKeyU{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LKeyU{}, st, cc)) == True{} : Bool}, hl)
    case T.LVal{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LVal{}, st, cc)) == True{} : Bool}, hl)
    case T.LQ{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LQ{}, st, cc)) == True{} : Bool}, hl)
    case T.LQ2{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LQ2{}, st, cc)) == True{} : Bool}, hl)
    case T.LStr{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LStr{}, st, cc)) == True{} : Bool}, hl)
    case T.LEsc{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LEsc{}, st, cc)) == True{} : Bool}, hl)
    case T.LUni{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LUni{}, st, cc)) == True{} : Bool}, hl)
    case T.LFold{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LFold{}, st, cc)) == True{} : Bool}, hl)
    case T.LMq{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LMq{}, st, cc)) == True{} : Bool}, hl)
    case T.LMqEnd{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LMqEnd{}, st, cc)) == True{} : Bool}, hl)
    case T.LTrim{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LTrim{}, st, cc)) == True{} : Bool}, hl)
    case T.LTrim2{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LTrim2{}, st, cc)) == True{} : Bool}, hl)
    case T.LBare{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LBare{}, st, cc)) == True{} : Bool}, hl)
    case T.LDate{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LDate{}, st, cc)) == True{} : Bool}, hl)
    case T.LCom{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LCom{}, st, cc)) == True{} : Bool}, hl)
    case T.LHead{}:
      gd.g.head(st, cc, eg, ec)
    case T.LHeadGap{}:
      gd.g.hgap(T.ch.sp(cc), Char.is_eq(cc, '.'), Char.is_eq(cc, ']'), Char.is_eq(cc, '#'), st, cc, eg)
    case T.LHeadDot{}:
      gd.g.hdot2(T.ch.sp(cc), T.bare.at(cc), Char.is_eq(cc, '"'), Char.is_eq(cc, '\''), st, cc, eg, ec)
    case T.LHeadQ{}:
      gd.g.kq(st, cc, T.LHeadGap{}, T.LHeadQ{}, eg, ec)
    case T.LHeadE{}:
      gd.g.esc(T.esc.of(cc), st, T.LHeadQ{}, eg, gd.e.of(cc))
    case T.LHeadU{}:
      gd.g.uni(st, cc, T.LHeadQ{}, eg)
    case T.LHeadR{}:
      gd.g.hr(Char.is_eq(cc, ']'), st, eg)
    case T.LArr{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LArr{}, st, cc)) == True{} : Bool}, hl)
    case T.LArrC{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LArrC{}, st, cc)) == True{} : Bool}, hl)
    case T.LInl{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LInl{}, st, cc)) == True{} : Bool}, hl)
    case T.LInlK{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LInlK{}, st, cc)) == True{} : Bool}, hl)
    case T.LInlC{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LInlC{}, st, cc)) == True{} : Bool}, hl)
    case T.LSink{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LSink{}, st, cc)) == True{} : Bool}, hl)

# WP-R3: the key states. A key is read into the buffer and the key's
# segments, the same parts of good a header's segments use.

# a comment only moves the lex state
def gd.g.com(
  +st: T.St,
  +back2: T.Lex,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.com.enter(st, back2)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      eg

# [ starts a header with a clear key
def gd.g.bracket(
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.bracket(st)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.tt(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, [], [], stack, hold),
        gd.l(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg),
        gd.lx.mk(here, [], [], stack, hold,
          gd.lx.h(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack),
            L2.gd.lx(here, parts, buf, stack, hold), eg)),
          {==}, {==},
          gd.lx.s(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack),
            L2.gd.lx(here, parts, buf, stack, hold), eg)),
          gd.r(L2.gd.keys(stack), L2.gd.hold(hold),
            gd.lx.s1(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack),
              L2.gd.lx(here, parts, buf, stack, hold), eg)))))

def gd.g.tbare(
  bare: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.top.bare(bare, st, cc)) == True{} : Bool}:
  match bare:
    case True{}:
      gd.g.push(st, cc, T.LKey{}, eg, ec)
    case False{}:
      gd.g.err(st, "invalid key", {==}, eg)

def gd.g.tlit(
  lit: Bool,
  bare: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.top.lit(lit, bare, st, cc)) == True{} : Bool}:
  match lit:
    case True{}:
      gd.g.qkey(st, T.QLit{}, T.LKeyQ{}, eg)
    case False{}:
      gd.g.tbare(bare, st, cc, eg, ec)

def gd.g.tq(
  qq: Bool,
  lit: Bool,
  bare: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.top.q(qq, lit, bare, st, cc)) == True{} : Bool}:
  match qq:
    case True{}:
      gd.g.qkey(st, T.QBasic{}, T.LKeyQ{}, eg)
    case False{}:
      gd.g.tlit(lit, bare, st, cc, eg, ec)

def gd.g.tbr(
  br: Bool,
  qq: Bool,
  lit: Bool,
  bare: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.top.br(br, qq, lit, bare, st, cc)) == True{} : Bool}:
  match br:
    case True{}:
      gd.g.bracket(st, eg)
    case False{}:
      gd.g.tq(qq, lit, bare, st, cc, eg, ec)

def gd.g.thash(
  hash: Bool,
  br: Bool,
  qq: Bool,
  lit: Bool,
  bare: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.top.hash(hash, br, qq, lit, bare, st, cc)) == True{} : Bool}:
  match hash:
    case True{}:
      gd.g.com(st, T.LTop{}, eg)
    case False{}:
      gd.g.tbr(br, qq, lit, bare, st, cc, eg, ec)

def gd.g.tnl(
  nl: Bool,
  hash: Bool,
  br: Bool,
  qq: Bool,
  lit: Bool,
  bare: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.top.nl(nl, hash, br, qq, lit, bare, st, cc)) == True{} : Bool}:
  match nl:
    case True{}:
      eg
    case False{}:
      gd.g.thash(hash, br, qq, lit, bare, st, cc, eg, ec)

def gd.g.tgo(
  sp: Bool,
  nl: Bool,
  hash: Bool,
  br: Bool,
  qq: Bool,
  lit: Bool,
  bare: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.top.go(sp, nl, hash, br, qq, lit, bare, st, cc)) == True{} : Bool}:
  match sp:
    case True{}:
      eg
    case False{}:
      gd.g.tnl(nl, hash, br, qq, lit, bare, st, cc, eg, ec)

def gd.g.lnl(
  nl: Bool,
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.line.nl(nl, st)) == True{} : Bool}:
  match nl:
    case True{}:
      gd.g.lex(st, T.LTop{}, eg)
    case False{}:
      gd.g.err(st, "newline required", {==}, eg)

def gd.g.lhash(
  hash: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.line.hash(hash, nl, st, cc)) == True{} : Bool}:
  match hash:
    case True{}:
      gd.g.com(st, T.LLine{}, eg)
    case False{}:
      gd.g.lnl(nl, st, eg)

def gd.g.lgo(
  sp: Bool,
  hash: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.line.go(sp, hash, nl, st, cc)) == True{} : Bool}:
  match sp:
    case True{}:
      eg
    case False{}:
      gd.g.lhash(hash, nl, st, cc, eg)

def gd.g.kendgo(
  empty: Bool,
  +st: T.St,
  +next: T.Lex,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.key.end.go(empty, st, next)) == True{} : Bool}:
  match empty:
    case True{}:
      gd.g.err(st, "empty key", {==}, eg)
    case False{}:
      gd.g.seg(st, next, eg)

def gd.g.kend(
  +st: T.St,
  +next: T.Lex,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.key.end(st, next)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.g.kendgo(List.is_empty(&2, Char, buf),
        T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead}, next, eg)

def gd.g.knl(
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.key.nl(nl, st, cc)) == True{} : Bool}:
  match nl:
    case True{}:
      gd.g.err(st, "newline in key", {==}, eg)
    case False{}:
      gd.g.err(st, "invalid key", {==}, eg)

def gd.g.khash(
  hash: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.key.hash(hash, nl, st, cc)) == True{} : Bool}:
  match hash:
    case True{}:
      gd.g.com(T.lex.key.end(st, T.LAfter{}), T.LAfter{}, gd.g.kend(st, T.LAfter{}, eg))
    case False{}:
      gd.g.knl(nl, st, cc, eg)

def gd.g.keq(
  eq: Bool,
  hash: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.key.eq(eq, hash, nl, st, cc)) == True{} : Bool}:
  match eq:
    case True{}:
      gd.g.kend(st, T.LVal{}, eg)
    case False{}:
      gd.g.khash(hash, nl, st, cc, eg)

def gd.g.kdot(
  dot: Bool,
  eq: Bool,
  hash: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.key.dot(dot, eq, hash, nl, st, cc)) == True{} : Bool}:
  match dot:
    case True{}:
      gd.g.kend(st, T.LKeyDot{}, eg)
    case False{}:
      gd.g.keq(eq, hash, nl, st, cc, eg)

def gd.g.ksp(
  sp: Bool,
  dot: Bool,
  eq: Bool,
  hash: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.key.sp(sp, dot, eq, hash, nl, st, cc)) == True{} : Bool}:
  match sp:
    case True{}:
      gd.g.kend(st, T.LAfter{}, eg)
    case False{}:
      gd.g.kdot(dot, eq, hash, nl, st, cc, eg)

def gd.g.kgo(
  bare: Bool,
  sp: Bool,
  dot: Bool,
  eq: Bool,
  hash: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.key.go(bare, sp, dot, eq, hash, nl, st, cc)) == True{} : Bool}:
  match bare:
    case True{}:
      gd.g.push(st, cc, T.LKey{}, eg, ec)
    case False{}:
      gd.g.ksp(sp, dot, eq, hash, nl, st, cc, eg)

def gd.g.anl(
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.after.nl(nl, st, cc)) == True{} : Bool}:
  match nl:
    case True{}:
      gd.g.err(st, "newline in key", {==}, eg)
    case False{}:
      gd.g.err(st, "invalid key", {==}, eg)

def gd.g.ahash(
  hash: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.after.hash(hash, nl, st, cc)) == True{} : Bool}:
  match hash:
    case True{}:
      gd.g.com(st, T.LAfter{}, eg)
    case False{}:
      gd.g.anl(nl, st, cc, eg)

def gd.g.aeq(
  eq: Bool,
  hash: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.after.eq(eq, hash, nl, st, cc)) == True{} : Bool}:
  match eq:
    case True{}:
      gd.g.lex(st, T.LVal{}, eg)
    case False{}:
      gd.g.ahash(hash, nl, st, cc, eg)

def gd.g.adot(
  dot: Bool,
  eq: Bool,
  hash: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.after.dot(dot, eq, hash, nl, st, cc)) == True{} : Bool}:
  match dot:
    case True{}:
      gd.g.lex(st, T.LKeyDot{}, eg)
    case False{}:
      gd.g.aeq(eq, hash, nl, st, cc, eg)

def gd.g.ago(
  sp: Bool,
  dot: Bool,
  eq: Bool,
  hash: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.after.go(sp, dot, eq, hash, nl, st, cc)) == True{} : Bool}:
  match sp:
    case True{}:
      eg
    case False{}:
      gd.g.adot(dot, eq, hash, nl, st, cc, eg)

def gd.g.dnl(
  nl: Bool,
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.kdot.nl(nl, st)) == True{} : Bool}:
  match nl:
    case True{}:
      gd.g.err(st, "newline in key", {==}, eg)
    case False{}:
      gd.g.err(st, "invalid key", {==}, eg)

def gd.g.ddot(
  dot: Bool,
  nl: Bool,
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.kdot.dot(dot, nl, st)) == True{} : Bool}:
  match dot:
    case True{}:
      gd.g.err(st, "empty key", {==}, eg)
    case False{}:
      gd.g.dnl(nl, st, eg)

def gd.g.dbare(
  bare: Bool,
  dot: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.kdot.bare(bare, dot, nl, st, cc)) == True{} : Bool}:
  match bare:
    case True{}:
      gd.g.push(st, cc, T.LKey{}, eg, ec)
    case False{}:
      gd.g.ddot(dot, nl, st, eg)

def gd.g.dlit(
  lit: Bool,
  dot: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.kdot.lit(lit, dot, nl, st, cc)) == True{} : Bool}:
  match lit:
    case True{}:
      gd.g.qkey(st, T.QLit{}, T.LKeyQ{}, eg)
    case False{}:
      gd.g.dbare(T.bare.at(cc), dot, nl, st, cc, eg, ec)

def gd.g.dq(
  qq: Bool,
  lit: Bool,
  dot: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.kdot.q(qq, lit, dot, nl, st, cc)) == True{} : Bool}:
  match qq:
    case True{}:
      gd.g.qkey(st, T.QBasic{}, T.LKeyQ{}, eg)
    case False{}:
      gd.g.dlit(lit, dot, nl, st, cc, eg, ec)

def gd.g.dgo(
  sp: Bool,
  qq: Bool,
  lit: Bool,
  dot: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.kdot.go(sp, qq, lit, dot, nl, st, cc)) == True{} : Bool}:
  match sp:
    case True{}:
      eg
    case False{}:
      gd.g.dq(qq, lit, dot, nl, st, cc, eg, ec)

def L2.gd_key_steps(lex, hl, st, eg, cc, ec):
  match lex:
    case T.LTop{}:
      gd.g.tgo(T.ch.sp(cc), T.ch.nl(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, '['), Char.is_eq(cc, '"'),
        Char.is_eq(cc, '\''), T.bare.at(cc), st, cc, eg, ec)
    case T.LLine{}:
      gd.g.lgo(T.ch.sp(cc), Char.is_eq(cc, '#'), T.ch.nl(cc), st, cc, eg)
    case T.LKey{}:
      gd.g.kgo(T.bare.at(cc), T.ch.sp(cc), Char.is_eq(cc, '.'), Char.is_eq(cc, '='), Char.is_eq(cc, '#'),
        T.ch.nl(cc), st, cc, eg, ec)
    case T.LKeyDot{}:
      gd.g.dgo(T.ch.sp(cc), Char.is_eq(cc, '"'), Char.is_eq(cc, '\''), Char.is_eq(cc, '.'), T.ch.nl(cc), st,
        cc, eg, ec)
    case T.LAfter{}:
      gd.g.ago(T.ch.sp(cc), Char.is_eq(cc, '.'), Char.is_eq(cc, '='), Char.is_eq(cc, '#'), T.ch.nl(cc), st, cc,
        eg)
    case T.LKeyQ{}:
      gd.g.kq(st, cc, T.LAfter{}, T.LKeyQ{}, eg, ec)
    case T.LKeyE{}:
      gd.g.esc(T.esc.of(cc), st, T.LKeyQ{}, eg, gd.e.of(cc))
    case T.LKeyU{}:
      gd.g.uni(st, cc, T.LKeyQ{}, eg)
    case T.LVal{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LVal{}, st, cc)) == True{} : Bool}, hl)
    case T.LQ{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LQ{}, st, cc)) == True{} : Bool}, hl)
    case T.LQ2{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LQ2{}, st, cc)) == True{} : Bool}, hl)
    case T.LStr{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LStr{}, st, cc)) == True{} : Bool}, hl)
    case T.LEsc{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LEsc{}, st, cc)) == True{} : Bool}, hl)
    case T.LUni{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LUni{}, st, cc)) == True{} : Bool}, hl)
    case T.LFold{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LFold{}, st, cc)) == True{} : Bool}, hl)
    case T.LMq{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LMq{}, st, cc)) == True{} : Bool}, hl)
    case T.LMqEnd{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LMqEnd{}, st, cc)) == True{} : Bool}, hl)
    case T.LTrim{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LTrim{}, st, cc)) == True{} : Bool}, hl)
    case T.LTrim2{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LTrim2{}, st, cc)) == True{} : Bool}, hl)
    case T.LBare{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LBare{}, st, cc)) == True{} : Bool}, hl)
    case T.LDate{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LDate{}, st, cc)) == True{} : Bool}, hl)
    case T.LCom{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LCom{}, st, cc)) == True{} : Bool}, hl)
    case T.LHead{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LHead{}, st, cc)) == True{} : Bool}, hl)
    case T.LHeadGap{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LHeadGap{}, st, cc)) == True{} : Bool}, hl)
    case T.LHeadDot{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LHeadDot{}, st, cc)) == True{} : Bool}, hl)
    case T.LHeadQ{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LHeadQ{}, st, cc)) == True{} : Bool}, hl)
    case T.LHeadE{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LHeadE{}, st, cc)) == True{} : Bool}, hl)
    case T.LHeadU{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LHeadU{}, st, cc)) == True{} : Bool}, hl)
    case T.LHeadR{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LHeadR{}, st, cc)) == True{} : Bool}, hl)
    case T.LArr{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LArr{}, st, cc)) == True{} : Bool}, hl)
    case T.LArrC{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LArrC{}, st, cc)) == True{} : Bool}, hl)
    case T.LInl{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LInl{}, st, cc)) == True{} : Bool}, hl)
    case T.LInlK{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LInlK{}, st, cc)) == True{} : Bool}, hl)
    case T.LInlC{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LInlC{}, st, cc)) == True{} : Bool}, hl)
    case T.LSink{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LSink{}, st, cc)) == True{} : Bool}, hl)

# WP-R3: the end. parse seals the rows, which reverses every table; a key is
# fresh in the rows after it exactly when every pair after it has another
# name, and a table's names are a set, so the order does not matter. gd.h1 is
# what wf.go asks of the head of any list, wherever it sits.

# what a pair's value needs wherever a list sits
def gd.pa(at: T.WfAt, +n: String, vv: T.Val) -> Bool:
  match at:
    case T.WfRows{+h}:
      gd.pv(h, n, vv)
    case T.WfInl{}:
      L2.gd.vok(vv)
    case T.WfItems{}:
      False{}
    case T.WfElems{_h}:
      False{}

# an element of an array of tables where it sits
def gd.it.aot(at: T.WfAt, +p: String, rows: List<&2, T.Val>) -> Bool:
  match at:
    case T.WfElems{+h}:
      Bool.and(T.str.eq(p, h), T.wf.go(rows, T.WfRows{p}))
    case _:
      False{}

# an array's item where it sits
def gd.it.box(at: T.WfAt, ok: Bool) -> Bool:
  match at:
    case T.WfItems{}:
      ok
    case _:
      False{}

# what wf.go asks of a value that is no pair at the head of a list
def gd.it(vv: T.Val, at: T.WfAt) -> Bool:
  match vv:
    case T.VAot{+p, rows}:
      gd.it.aot(at, p, rows)
    case T.VArr{items}:
      gd.it.box(at, T.wf.go(items, T.WfItems{}))
    case T.VInl{rows}:
      gd.it.box(at, T.wf.go(rows, T.WfInl{}))
    case T.VPair{_n, _v}:
      False{}
    case other:
      gd.it.box(at, T.wf.atom(other))

# what wf.go asks of the head of a list: a pair's key is fresh in the rest
def gd.h1(vv: T.Val, +t: List<&2, T.Val>, at: T.WfAt) -> Bool:
  match vv:
    case T.VPair{+n, v}:
      Bool.and(T.wf.key(n, t), gd.pa(at, n, v))
    case other:
      gd.it(other, at)

# the shapes that are False wherever the list sits
def gd.sh.f2(kk: Bool, dd: Bool) -> {False{} == Bool.and(Bool.and(kk, False{}), dd) : Bool}:
  match kk:
    case True{}:
      {==}
    case False{}:
      {==}

def gd.sh.it(gg: Bool, dd: Bool) -> {T.wf.then(gg, _u => dd) == Bool.and(gg, dd) : Bool}:
  match gg:
    case True{}:
      {==}
    case False{}:
      {==}

# wf.go of a list is its head's needs and its rest's, wherever it sits
def gd.gen.eq(
  vv: T.Val,
  +t: List<&2, T.Val>,
  at: T.WfAt
) -> {T.wf.go(vv <> t, at) == Bool.and(gd.h1(vv, t, at), T.wf.go(t, at)) : Bool}:
  match vv:
    case T.VPair{+n, v}:
      match v:
        case T.VStr{+r}:
          match at:
            case T.WfRows{+h}:
              gd.sh.atom(T.wf.atom(T.VStr{r}), T.wf.key(n, t), T.wf.go(t, T.WfRows{h}))
            case T.WfInl{}:
              gd.sh.atom(T.wf.atom(T.VStr{r}), T.wf.key(n, t), T.wf.go(t, T.WfInl{}))
            case T.WfItems{}:
              gd.sh.f2(T.wf.key(n, t), T.wf.go(t, T.WfItems{}))
            case T.WfElems{+h}:
              gd.sh.f2(T.wf.key(n, t), T.wf.go(t, T.WfElems{h}))
        case T.VSpan{+p, +r}:
          match at:
            case T.WfRows{+h}:
              gd.sh.atom(T.wf.atom(T.VSpan{p, r}), T.wf.key(n, t), T.wf.go(t, T.WfRows{h}))
            case T.WfInl{}:
              gd.sh.atom(T.wf.atom(T.VSpan{p, r}), T.wf.key(n, t), T.wf.go(t, T.WfInl{}))
            case T.WfItems{}:
              gd.sh.f2(T.wf.key(n, t), T.wf.go(t, T.WfItems{}))
            case T.WfElems{+h}:
              gd.sh.f2(T.wf.key(n, t), T.wf.go(t, T.WfElems{h}))
        case T.VInt{+p, +r}:
          match at:
            case T.WfRows{+h}:
              gd.sh.atom(T.wf.atom(T.VInt{p, r}), T.wf.key(n, t), T.wf.go(t, T.WfRows{h}))
            case T.WfInl{}:
              gd.sh.atom(T.wf.atom(T.VInt{p, r}), T.wf.key(n, t), T.wf.go(t, T.WfInl{}))
            case T.WfItems{}:
              gd.sh.f2(T.wf.key(n, t), T.wf.go(t, T.WfItems{}))
            case T.WfElems{+h}:
              gd.sh.f2(T.wf.key(n, t), T.wf.go(t, T.WfElems{h}))
        case T.VFlo{+p, +r}:
          match at:
            case T.WfRows{+h}:
              gd.sh.atom(T.wf.atom(T.VFlo{p, r}), T.wf.key(n, t), T.wf.go(t, T.WfRows{h}))
            case T.WfInl{}:
              gd.sh.atom(T.wf.atom(T.VFlo{p, r}), T.wf.key(n, t), T.wf.go(t, T.WfInl{}))
            case T.WfItems{}:
              gd.sh.f2(T.wf.key(n, t), T.wf.go(t, T.WfItems{}))
            case T.WfElems{+h}:
              gd.sh.f2(T.wf.key(n, t), T.wf.go(t, T.WfElems{h}))
        case T.VBool{+r}:
          match at:
            case T.WfRows{+h}:
              gd.sh.atom(T.wf.atom(T.VBool{r}), T.wf.key(n, t), T.wf.go(t, T.WfRows{h}))
            case T.WfInl{}:
              gd.sh.atom(T.wf.atom(T.VBool{r}), T.wf.key(n, t), T.wf.go(t, T.WfInl{}))
            case T.WfItems{}:
              gd.sh.f2(T.wf.key(n, t), T.wf.go(t, T.WfItems{}))
            case T.WfElems{+h}:
              gd.sh.f2(T.wf.key(n, t), T.wf.go(t, T.WfElems{h}))
        case T.VWhen{+r}:
          match at:
            case T.WfRows{+h}:
              gd.sh.atom(T.wf.atom(T.VWhen{r}), T.wf.key(n, t), T.wf.go(t, T.WfRows{h}))
            case T.WfInl{}:
              gd.sh.atom(T.wf.atom(T.VWhen{r}), T.wf.key(n, t), T.wf.go(t, T.WfInl{}))
            case T.WfItems{}:
              gd.sh.f2(T.wf.key(n, t), T.wf.go(t, T.WfItems{}))
            case T.WfElems{+h}:
              gd.sh.f2(T.wf.key(n, t), T.wf.go(t, T.WfElems{h}))
        case T.VArr{+r}:
          match at:
            case T.WfRows{+h}:
              gd.sh.arr(T.wf.key(n, t), T.wf.go(r, T.WfItems{}), T.wf.go(t, T.WfRows{h}))
            case T.WfInl{}:
              gd.sh.arr(T.wf.key(n, t), T.wf.go(r, T.WfItems{}), T.wf.go(t, T.WfInl{}))
            case T.WfItems{}:
              gd.sh.f2(T.wf.key(n, t), T.wf.go(t, T.WfItems{}))
            case T.WfElems{+h}:
              gd.sh.f2(T.wf.key(n, t), T.wf.go(t, T.WfElems{h}))
        case T.VInl{+r}:
          match at:
            case T.WfRows{+h}:
              gd.sh.arr(T.wf.key(n, t), T.wf.go(r, T.WfInl{}), T.wf.go(t, T.WfRows{h}))
            case T.WfInl{}:
              gd.sh.arr(T.wf.key(n, t), T.wf.go(r, T.WfInl{}), T.wf.go(t, T.WfInl{}))
            case T.WfItems{}:
              gd.sh.f2(T.wf.key(n, t), T.wf.go(t, T.WfItems{}))
            case T.WfElems{+h}:
              gd.sh.f2(T.wf.key(n, t), T.wf.go(t, T.WfElems{h}))
        case T.VHead{+p, +r}:
          match at:
            case T.WfRows{+h}:
              gd.sh.head(T.wf.key(n, t), T.str.eq(p, T.tree.pre(h, n)), T.wf.go(r, T.WfRows{p}), T.wf.go(t,
                T.WfRows{h}))
            case T.WfInl{}:
              gd.sh.f2(T.wf.key(n, t), T.wf.go(t, T.WfInl{}))
            case T.WfItems{}:
              gd.sh.f2(T.wf.key(n, t), T.wf.go(t, T.WfItems{}))
            case T.WfElems{+h}:
              gd.sh.f2(T.wf.key(n, t), T.wf.go(t, T.WfElems{h}))
        case T.VAot{+p, +r}:
          match at:
            case T.WfRows{+h}:
              gd.sh.atom(T.wf.atom(T.VAot{p, r}), T.wf.key(n, t), T.wf.go(t, T.WfRows{h}))
            case T.WfInl{}:
              gd.sh.atom(T.wf.atom(T.VAot{p, r}), T.wf.key(n, t), T.wf.go(t, T.WfInl{}))
            case T.WfItems{}:
              gd.sh.f2(T.wf.key(n, t), T.wf.go(t, T.WfItems{}))
            case T.WfElems{+h}:
              gd.sh.f2(T.wf.key(n, t), T.wf.go(t, T.WfElems{h}))
        case T.VAots{+p, +r}:
          match at:
            case T.WfRows{+h}:
              gd.sh.aots(Bool.not(List.is_empty(&2, T.Val, r)), T.wf.key(n, t), T.str.eq(p, T.tree.pre(h, n)),
                T.wf.go(r, T.WfElems{p}), T.wf.go(t, T.WfRows{h}))
            case T.WfInl{}:
              gd.sh.f2(T.wf.key(n, t), T.wf.go(t, T.WfInl{}))
            case T.WfItems{}:
              gd.sh.f2(T.wf.key(n, t), T.wf.go(t, T.WfItems{}))
            case T.WfElems{+h}:
              gd.sh.f2(T.wf.key(n, t), T.wf.go(t, T.WfElems{h}))
        case T.VPair{+p, +r}:
          match at:
            case T.WfRows{+h}:
              gd.sh.atom(T.wf.atom(T.VPair{p, r}), T.wf.key(n, t), T.wf.go(t, T.WfRows{h}))
            case T.WfInl{}:
              gd.sh.atom(T.wf.atom(T.VPair{p, r}), T.wf.key(n, t), T.wf.go(t, T.WfInl{}))
            case T.WfItems{}:
              gd.sh.f2(T.wf.key(n, t), T.wf.go(t, T.WfItems{}))
            case T.WfElems{+h}:
              gd.sh.f2(T.wf.key(n, t), T.wf.go(t, T.WfElems{h}))
    case T.VStr{+r}:
      match at:
        case T.WfRows{+h}:
          {==}
        case T.WfInl{}:
          {==}
        case T.WfItems{}:
          gd.sh.it(T.wf.atom(T.VStr{r}), T.wf.go(t, T.WfItems{}))
        case T.WfElems{+h}:
          {==}
    case T.VSpan{+p, +r}:
      match at:
        case T.WfRows{+h}:
          {==}
        case T.WfInl{}:
          {==}
        case T.WfItems{}:
          gd.sh.it(T.wf.atom(T.VSpan{p, r}), T.wf.go(t, T.WfItems{}))
        case T.WfElems{+h}:
          {==}
    case T.VInt{+p, +r}:
      match at:
        case T.WfRows{+h}:
          {==}
        case T.WfInl{}:
          {==}
        case T.WfItems{}:
          gd.sh.it(T.wf.atom(T.VInt{p, r}), T.wf.go(t, T.WfItems{}))
        case T.WfElems{+h}:
          {==}
    case T.VFlo{+p, +r}:
      match at:
        case T.WfRows{+h}:
          {==}
        case T.WfInl{}:
          {==}
        case T.WfItems{}:
          gd.sh.it(T.wf.atom(T.VFlo{p, r}), T.wf.go(t, T.WfItems{}))
        case T.WfElems{+h}:
          {==}
    case T.VBool{+r}:
      match at:
        case T.WfRows{+h}:
          {==}
        case T.WfInl{}:
          {==}
        case T.WfItems{}:
          gd.sh.it(T.wf.atom(T.VBool{r}), T.wf.go(t, T.WfItems{}))
        case T.WfElems{+h}:
          {==}
    case T.VWhen{+r}:
      match at:
        case T.WfRows{+h}:
          {==}
        case T.WfInl{}:
          {==}
        case T.WfItems{}:
          gd.sh.it(T.wf.atom(T.VWhen{r}), T.wf.go(t, T.WfItems{}))
        case T.WfElems{+h}:
          {==}
    case T.VArr{+r}:
      match at:
        case T.WfRows{+h}:
          {==}
        case T.WfInl{}:
          {==}
        case T.WfItems{}:
          gd.sh.it(T.wf.go(r, T.WfItems{}), T.wf.go(t, T.WfItems{}))
        case T.WfElems{+h}:
          {==}
    case T.VInl{+r}:
      match at:
        case T.WfRows{+h}:
          {==}
        case T.WfInl{}:
          {==}
        case T.WfItems{}:
          gd.sh.it(T.wf.go(r, T.WfInl{}), T.wf.go(t, T.WfItems{}))
        case T.WfElems{+h}:
          {==}
    case T.VHead{+p, +r}:
      match at:
        case T.WfRows{+h}:
          {==}
        case T.WfInl{}:
          {==}
        case T.WfItems{}:
          gd.sh.it(T.wf.atom(T.VHead{p, r}), T.wf.go(t, T.WfItems{}))
        case T.WfElems{+h}:
          {==}
    case T.VAot{+p, +r}:
      match at:
        case T.WfRows{+h}:
          {==}
        case T.WfInl{}:
          {==}
        case T.WfItems{}:
          {==}
        case T.WfElems{+h}:
          gd.sh.arr(T.str.eq(p, h), T.wf.go(r, T.WfRows{p}), T.wf.go(t, T.WfElems{h}))
    case T.VAots{+p, +r}:
      match at:
        case T.WfRows{+h}:
          {==}
        case T.WfInl{}:
          {==}
        case T.WfItems{}:
          gd.sh.it(T.wf.atom(T.VAots{p, r}), T.wf.go(t, T.WfItems{}))
        case T.WfElems{+h}:
          {==}

# the head's needs and the rest's, read off a well-formed list
def gd.gen.un(
  +vv: T.Val,
  +t: List<&2, T.Val>,
  +at: T.WfAt,
  +ee: {T.wf.go(vv <> t, at) == True{} : Bool}
) -> {Bool.and(gd.h1(vv, t, at), T.wf.go(t, at)) == True{} : Bool}:
  Equal.trans(Bool, Bool.and(gd.h1(vv, t, at), T.wf.go(t, at)), T.wf.go(vv <> t, at), True{},
    Equal.sym(Bool, T.wf.go(vv <> t, at), Bool.and(gd.h1(vv, t, at), T.wf.go(t, at)), gd.gen.eq(vv, t, at)),
    ee)

# and a list put together from them
def gd.gen.mk(
  +vv: T.Val,
  +t: List<&2, T.Val>,
  +at: T.WfAt,
  +eh: {gd.h1(vv, t, at) == True{} : Bool},
  +ed: {T.wf.go(t, at) == True{} : Bool}
) -> {T.wf.go(vv <> t, at) == True{} : Bool}:
  Equal.trans(Bool, T.wf.go(vv <> t, at), Bool.and(gd.h1(vv, t, at), T.wf.go(t, at)), True{},
    gd.gen.eq(vv, t, at), gd.tt(gd.h1(vv, t, at), T.wf.go(t, at), eh, ed))

# an array's item needs nothing of the items after it
def gd.it.tail(
  xx: T.Val,
  +t: List<&2, T.Val>,
  +acc: List<&2, T.Val>,
  +ee: {gd.h1(xx, t, T.WfItems{}) == True{} : Bool}
) -> {gd.h1(xx, acc, T.WfItems{}) == True{} : Bool}:
  match xx:
    case T.VPair{+n, +v}:
      Eq.bit.absurd(&2, {gd.h1(T.VPair{n, v}, acc, T.WfItems{}) == True{} : Bool},
        gd.r(T.wf.key(n, t), False{}, ee))
    case T.VStr{_a0}:
      ee
    case T.VSpan{_a0, _a1}:
      ee
    case T.VInt{_a0, _a1}:
      ee
    case T.VFlo{_a0, _a1}:
      ee
    case T.VBool{_a0}:
      ee
    case T.VWhen{_a0}:
      ee
    case T.VArr{_a0}:
      ee
    case T.VInl{_a0}:
      ee
    case T.VHead{_a0, _a1}:
      ee
    case T.VAot{_a0, _a1}:
      ee
    case T.VAots{_a0, _a1}:
      ee

# an array's items in any order: reversed onto more items
def gd.rev.it(
  ll: List<&2, T.Val>,
  +acc: List<&2, T.Val>,
  +el: {T.wf.go(ll, T.WfItems{}) == True{} : Bool},
  +ea: {T.wf.go(acc, T.WfItems{}) == True{} : Bool}
) -> {T.wf.go(List.reverse.go(&2, T.Val, ll, acc), T.WfItems{}) == True{} : Bool}:
  match ll:
    case []:
      ea
    case +x <> +t:
      gd.rev.it(t, x <> acc,
        gd.r(gd.h1(x, t, T.WfItems{}), T.wf.go(t, T.WfItems{}), gd.gen.un(x, t, T.WfItems{}, el)),
        gd.gen.mk(x, acc, T.WfItems{},
          gd.it.tail(x, t, acc, gd.l(gd.h1(x, t, T.WfItems{}), T.wf.go(t, T.WfItems{}),
            gd.gen.un(x, t, T.WfItems{}, el))), ea))

# WP-R3: an open inline table's rows. Its dotted keys walk from "" as a
# root's do (gd_walk), and a put's walk makes no array of tables (gd.nw), so
# its rows seal into an inline table's (gd.is).

# the root after a walk has no array of tables, unless the walk failed
def gd.endn(end: T.End) -> Bool:
  match end:
    case T.End{vs, +bad, _h}:
      L2.gd.ifok(String.is_empty(bad), L2.gd.na(vs))

# the frames' promise, for arrays of tables
def gd.Kn(stack: List<&2, T.Fr>) -> Type:
  @vs: List<&2, T.Val> -> @bad: String -> @hs: List<&2, String> ->
    {L2.gd.ifok(String.is_empty(bad), L2.gd.na(vs)) == True{} : Bool} ->
    {gd.endn(T.tree.rebuild(stack, vs, bad, hs)) == True{} : Bool}

def gd.kn.root() -> gd.Kn([]):
  _vs => _bad => _hs => ee => ee

def gd.kn.lift(
  bad: String,
  +vs: List<&2, T.Val>,
  +fr: T.Fr,
  ee: {L2.gd.ifok(String.is_empty(bad), L2.gd.na(vs)) == True{} : Bool},
  ff: @ch: List<&2, T.Val> -> {L2.gd.na(ch) == True{} : Bool} -> {L2.gd.na(T.tree.wrap(fr, ch)) == True{} : Bool}
) -> {L2.gd.ifok(String.is_empty(bad), L2.gd.na(T.tree.wrap(fr, vs))) == True{} : Bool}:
  match bad:
    case SNil{}:
      ff(vs, ee)
    case SCon{_h, _t}:
      {==}

def gd.kn.pushgo(
  +fr: T.Fr,
  stack: List<&2, T.Fr>,
  kk: gd.Kn(stack),
  ff: @ch: List<&2, T.Val> -> {L2.gd.na(ch) == True{} : Bool} -> {L2.gd.na(T.tree.wrap(fr, ch)) == True{} : Bool},
  +vs: List<&2, T.Val>,
  +bad: String,
  hs: List<&2, String>,
  ee: {L2.gd.ifok(String.is_empty(bad), L2.gd.na(vs)) == True{} : Bool}
) -> {gd.endn(T.tree.rebuild(fr <> stack, vs, bad, hs)) == True{} : Bool}:
  kk(T.tree.wrap(fr, vs), bad, hs, gd.kn.lift(bad, vs, fr, ee, ff))

def gd.kn.push(
  +fr: T.Fr,
  stack: List<&2, T.Fr>,
  kk: gd.Kn(stack),
  ff: @ch: List<&2, T.Val> -> {L2.gd.na(ch) == True{} : Bool} -> {L2.gd.na(T.tree.wrap(fr, ch)) == True{} : Bool}
) -> gd.Kn(fr <> stack):
  vs => bad => hs => ee => gd.kn.pushgo(fr, stack, kk, ff, vs, bad, hs, ee)

# either answer, when the rest holds
def gd.ifok.any(ok: Bool, xx: Bool, +ex: {xx == True{} : Bool}) -> {L2.gd.ifok(ok, xx) == True{} : Bool}:
  match ok:
    case True{}:
      ex
    case False{}:
      {==}

# a pair of the name replaced or kept
def gd.na.rstep(
  bb: Bool,
  +nn: String,
  +old: T.Val,
  +vv: T.Val,
  +t: List<&2, T.Val>,
  +name: String,
  +enew: {L2.gd.na(T.VPair{nn, vv} <> T.rows.repl(t, name, vv)) == True{} : Bool},
  +eold: {L2.gd.na(T.VPair{nn, old} <> T.rows.repl(t, name, vv)) == True{} : Bool}
) -> {L2.gd.na(T.rows.repl.step(bb, nn, old, vv, _u => T.rows.repl(t, name, vv))) == True{} : Bool}:
  match bb:
    case True{}:
      enew
    case False{}:
      eold

# a table put in place of a name keeps rows free of arrays of tables
def gd.na.repl(
  vs: List<&2, T.Val>,
  +name: String,
  +pp: String,
  +ch: List<&2, T.Val>,
  +ev: {L2.gd.na(vs) == True{} : Bool},
  +ec: {L2.gd.na(ch) == True{} : Bool}
) -> {L2.gd.na(T.rows.repl(vs, name, T.VHead{pp, ch})) == True{} : Bool}:
  match vs:
    case []:
      {==}
    case T.VPair{+n, T.VStr{+s}} <> +t:
      gd.na.rstep(T.str.eq(n, name), n, T.VStr{s}, T.VHead{pp, ch}, t, name,
        gd.tt(L2.gd.na(ch), L2.gd.na(T.rows.repl(t, name, T.VHead{pp, ch})), ec, gd.na.repl(t, name, pp, ch, ev,
          ec)),
        gd.na.repl(t, name, pp, ch, ev, ec))
    case T.VPair{+n, T.VSpan{+q, +s}} <> +t:
      gd.na.rstep(T.str.eq(n, name), n, T.VSpan{q, s}, T.VHead{pp, ch}, t, name,
        gd.tt(L2.gd.na(ch), L2.gd.na(T.rows.repl(t, name, T.VHead{pp, ch})), ec, gd.na.repl(t, name, pp, ch, ev,
          ec)),
        gd.na.repl(t, name, pp, ch, ev, ec))
    case T.VPair{+n, T.VInt{+q, +s}} <> +t:
      gd.na.rstep(T.str.eq(n, name), n, T.VInt{q, s}, T.VHead{pp, ch}, t, name,
        gd.tt(L2.gd.na(ch), L2.gd.na(T.rows.repl(t, name, T.VHead{pp, ch})), ec, gd.na.repl(t, name, pp, ch, ev,
          ec)),
        gd.na.repl(t, name, pp, ch, ev, ec))
    case T.VPair{+n, T.VFlo{+q, +s}} <> +t:
      gd.na.rstep(T.str.eq(n, name), n, T.VFlo{q, s}, T.VHead{pp, ch}, t, name,
        gd.tt(L2.gd.na(ch), L2.gd.na(T.rows.repl(t, name, T.VHead{pp, ch})), ec, gd.na.repl(t, name, pp, ch, ev,
          ec)),
        gd.na.repl(t, name, pp, ch, ev, ec))
    case T.VPair{+n, T.VBool{+s}} <> +t:
      gd.na.rstep(T.str.eq(n, name), n, T.VBool{s}, T.VHead{pp, ch}, t, name,
        gd.tt(L2.gd.na(ch), L2.gd.na(T.rows.repl(t, name, T.VHead{pp, ch})), ec, gd.na.repl(t, name, pp, ch, ev,
          ec)),
        gd.na.repl(t, name, pp, ch, ev, ec))
    case T.VPair{+n, T.VWhen{+s}} <> +t:
      gd.na.rstep(T.str.eq(n, name), n, T.VWhen{s}, T.VHead{pp, ch}, t, name,
        gd.tt(L2.gd.na(ch), L2.gd.na(T.rows.repl(t, name, T.VHead{pp, ch})), ec, gd.na.repl(t, name, pp, ch, ev,
          ec)),
        gd.na.repl(t, name, pp, ch, ev, ec))
    case T.VPair{+n, T.VArr{+s}} <> +t:
      gd.na.rstep(T.str.eq(n, name), n, T.VArr{s}, T.VHead{pp, ch}, t, name,
        gd.tt(L2.gd.na(ch), L2.gd.na(T.rows.repl(t, name, T.VHead{pp, ch})), ec, gd.na.repl(t, name, pp, ch, ev,
          ec)),
        gd.na.repl(t, name, pp, ch, ev, ec))
    case T.VPair{+n, T.VInl{+s}} <> +t:
      gd.na.rstep(T.str.eq(n, name), n, T.VInl{s}, T.VHead{pp, ch}, t, name,
        gd.tt(L2.gd.na(ch), L2.gd.na(T.rows.repl(t, name, T.VHead{pp, ch})), ec, gd.na.repl(t, name, pp, ch, ev,
          ec)),
        gd.na.repl(t, name, pp, ch, ev, ec))
    case T.VPair{+n, T.VHead{+q, +s}} <> +t:
      gd.na.rstep(T.str.eq(n, name), n, T.VHead{q, s}, T.VHead{pp, ch}, t, name,
        gd.tt(L2.gd.na(ch), L2.gd.na(T.rows.repl(t, name, T.VHead{pp, ch})), ec, gd.na.repl(t, name, pp, ch,
          gd.r(L2.gd.na(s), L2.gd.na(t), ev), ec)),
        gd.tt(L2.gd.na(s), L2.gd.na(T.rows.repl(t, name, T.VHead{pp, ch})), gd.l(L2.gd.na(s), L2.gd.na(t), ev),
          gd.na.repl(t, name, pp, ch, gd.r(L2.gd.na(s), L2.gd.na(t), ev), ec)))
    case T.VPair{+n, T.VAot{+q, +s}} <> +t:
      gd.na.rstep(T.str.eq(n, name), n, T.VAot{q, s}, T.VHead{pp, ch}, t, name,
        gd.tt(L2.gd.na(ch), L2.gd.na(T.rows.repl(t, name, T.VHead{pp, ch})), ec, gd.na.repl(t, name, pp, ch, ev,
          ec)),
        gd.na.repl(t, name, pp, ch, ev, ec))
    case T.VPair{+n, T.VAots{+q, +s}} <> +t:
      Eq.bit.absurd(&2, {L2.gd.na(T.rows.repl(T.VPair{n, T.VAots{q, s}} <> t, name, T.VHead{pp,
        ch})) == True{} : Bool}, ev)
    case T.VPair{+n, T.VPair{+q, +s}} <> +t:
      gd.na.rstep(T.str.eq(n, name), n, T.VPair{q, s}, T.VHead{pp, ch}, t, name,
        gd.tt(L2.gd.na(ch), L2.gd.na(T.rows.repl(t, name, T.VHead{pp, ch})), ec, gd.na.repl(t, name, pp, ch, ev,
          ec)),
        gd.na.repl(t, name, pp, ch, ev, ec))
    case T.VStr{_r} <> +t:
      gd.na.repl(t, name, pp, ch, ev, ec)
    case T.VSpan{_p, _r} <> +t:
      gd.na.repl(t, name, pp, ch, ev, ec)
    case T.VInt{_p, _r} <> +t:
      gd.na.repl(t, name, pp, ch, ev, ec)
    case T.VFlo{_p, _r} <> +t:
      gd.na.repl(t, name, pp, ch, ev, ec)
    case T.VBool{_r} <> +t:
      gd.na.repl(t, name, pp, ch, ev, ec)
    case T.VWhen{_r} <> +t:
      gd.na.repl(t, name, pp, ch, ev, ec)
    case T.VArr{_r} <> +t:
      gd.na.repl(t, name, pp, ch, ev, ec)
    case T.VInl{_r} <> +t:
      gd.na.repl(t, name, pp, ch, ev, ec)
    case T.VHead{_p, _r} <> +t:
      gd.na.repl(t, name, pp, ch, ev, ec)
    case T.VAot{_p, _r} <> +t:
      gd.na.repl(t, name, pp, ch, ev, ec)
    case T.VAots{_p, _r} <> +t:
      gd.na.repl(t, name, pp, ch, ev, ec)

# what a lookup finds in rows with no array of tables
def gd.nlk(look: T.Look) -> Bool:
  match look:
    case T.KHead{_p, sub}:
      L2.gd.na(sub)
    case T.KAots{_p, _e}:
      False{}
    case _:
      True{}

def gd.nlk.step(
  bb: Bool,
  vv: T.Val,
  t: List<&2, T.Val>,
  +name: String,
  +ehit: {gd.nlk(T.look.of(vv)) == True{} : Bool},
  +ih: {gd.nlk(T.rows.look(t, name)) == True{} : Bool}
) -> {gd.nlk(T.look.step(bb, vv, _u => T.rows.look(t, name))) == True{} : Bool}:
  match bb:
    case True{}:
      ehit
    case False{}:
      ih

def gd.na.lk(
  vs: List<&2, T.Val>,
  +name: String,
  +ev: {L2.gd.na(vs) == True{} : Bool}
) -> {gd.nlk(T.rows.look(vs, name)) == True{} : Bool}:
  match vs:
    case []:
      {==}
    case T.VPair{+n, T.VStr{+s}} <> +t:
      gd.nlk.step(T.str.eq(n, name), T.VStr{s}, t, name, {==}, gd.na.lk(t, name, ev))
    case T.VPair{+n, T.VSpan{+q, +s}} <> +t:
      gd.nlk.step(T.str.eq(n, name), T.VSpan{q, s}, t, name, {==}, gd.na.lk(t, name, ev))
    case T.VPair{+n, T.VInt{+q, +s}} <> +t:
      gd.nlk.step(T.str.eq(n, name), T.VInt{q, s}, t, name, {==}, gd.na.lk(t, name, ev))
    case T.VPair{+n, T.VFlo{+q, +s}} <> +t:
      gd.nlk.step(T.str.eq(n, name), T.VFlo{q, s}, t, name, {==}, gd.na.lk(t, name, ev))
    case T.VPair{+n, T.VBool{+s}} <> +t:
      gd.nlk.step(T.str.eq(n, name), T.VBool{s}, t, name, {==}, gd.na.lk(t, name, ev))
    case T.VPair{+n, T.VWhen{+s}} <> +t:
      gd.nlk.step(T.str.eq(n, name), T.VWhen{s}, t, name, {==}, gd.na.lk(t, name, ev))
    case T.VPair{+n, T.VArr{+s}} <> +t:
      gd.nlk.step(T.str.eq(n, name), T.VArr{s}, t, name, {==}, gd.na.lk(t, name, ev))
    case T.VPair{+n, T.VInl{+s}} <> +t:
      gd.nlk.step(T.str.eq(n, name), T.VInl{s}, t, name, {==}, gd.na.lk(t, name, ev))
    case T.VPair{+n, T.VHead{+q, +s}} <> +t:
      gd.nlk.step(T.str.eq(n, name), T.VHead{q, s}, t, name, gd.l(L2.gd.na(s), L2.gd.na(t), ev),
        gd.na.lk(t, name, gd.r(L2.gd.na(s), L2.gd.na(t), ev)))
    case T.VPair{+n, T.VAot{+q, +s}} <> +t:
      gd.nlk.step(T.str.eq(n, name), T.VAot{q, s}, t, name, {==}, gd.na.lk(t, name, ev))
    case T.VPair{+n, T.VAots{+q, +s}} <> +t:
      Eq.bit.absurd(&2, {gd.nlk(T.rows.look(T.VPair{n, T.VAots{q, s}} <> t, name)) == True{} : Bool}, ev)
    case T.VPair{+n, T.VPair{+q, +s}} <> +t:
      gd.nlk.step(T.str.eq(n, name), T.VPair{q, s}, t, name, {==}, gd.na.lk(t, name, ev))
    case T.VStr{_r} <> +t:
      gd.na.lk(t, name, ev)
    case T.VSpan{_p, _r} <> +t:
      gd.na.lk(t, name, ev)
    case T.VInt{_p, _r} <> +t:
      gd.na.lk(t, name, ev)
    case T.VFlo{_p, _r} <> +t:
      gd.na.lk(t, name, ev)
    case T.VBool{_r} <> +t:
      gd.na.lk(t, name, ev)
    case T.VWhen{_r} <> +t:
      gd.na.lk(t, name, ev)
    case T.VArr{_r} <> +t:
      gd.na.lk(t, name, ev)
    case T.VInl{_r} <> +t:
      gd.na.lk(t, name, ev)
    case T.VHead{_p, _r} <> +t:
      gd.na.lk(t, name, ev)
    case T.VAot{_p, _r} <> +t:
      gd.na.lk(t, name, ev)
    case T.VAots{_p, _r} <> +t:
      gd.na.lk(t, name, ev)

# a value put in front: no table of either kind
def gd.na.put(
  vv: T.Val,
  +name: String,
  +vs: List<&2, T.Val>,
  +evk: {L2.gd.vok(vv) == True{} : Bool},
  +ev: {L2.gd.na(vs) == True{} : Bool}
) -> {L2.gd.na(T.VPair{name, vv} <> vs) == True{} : Bool}:
  match vv:
    case T.VStr{+r}:
      ev
    case T.VSpan{+p, +r}:
      ev
    case T.VInt{+p, +r}:
      ev
    case T.VFlo{+p, +r}:
      ev
    case T.VBool{+r}:
      ev
    case T.VWhen{+r}:
      ev
    case T.VArr{+r}:
      ev
    case T.VInl{+r}:
      ev
    case T.VHead{+p, +r}:
      Eq.bit.absurd(&2, {L2.gd.na(T.VPair{name, T.VHead{p, r}} <> vs) == True{} : Bool}, evk)
    case T.VAot{+p, +r}:
      ev
    case T.VAots{+p, +r}:
      Eq.bit.absurd(&2, {L2.gd.na(T.VPair{name, T.VAots{p, r}} <> vs) == True{} : Bool}, evk)
    case T.VPair{+p, +r}:
      ev

# the rest of a put's walk, owed for any table it goes on in
def gd.nIH(rest: List<&2, String>, +val: T.Val, +inl: Bool, +skip: U32) -> Type:
  @vs: List<&2, T.Val> -> @stack: List<&2, T.Fr> -> @bad: String -> @pre: String ->
    @hs: List<&2, String> ->
    {L2.gd.ifok(String.is_empty(bad), L2.gd.na(vs)) == True{} : Bool} ->
    gd.Kn(stack) ->
    {gd.endn(T.tree.walk(rest, T.Tw{vs, T.JPut{val}, stack, bad, pre, hs, inl}, skip)) == True{} : Bool}

def gd.nw.hgo(
  shut: Bool,
  +pp: String,
  +rows: List<&2, T.Val>,
  +name: String,
  +vs: List<&2, T.Val>,
  +val: T.Val,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +mark: Bool,
  rest: List<&2, String>,
  +skip: U32,
  +ens: {L2.gd.na(rows) == True{} : Bool},
  +ev: {L2.gd.na(vs) == True{} : Bool},
  kk: gd.Kn(stack),
  ih: gd.nIH(rest, val, inl, skip)
) -> {gd.endn(T.tree.walk(rest, T.tree.sub.head.go(shut, pp, rows, name, vs, T.JPut{val}, stack, pre, heads,
  inl, mark), skip)) == True{} : Bool}:
  match shut:
    case True{}:
      ih(vs, stack, "duplicate table", pre, heads, {==}, kk)
    case False{}:
      ih(rows, T.FrRep{name, vs, pp} <> stack, "", T.tree.pre(pre, name),
        T.heads.define(T.tree.sub.job(mark, T.JPut{val}), T.tree.pre(pre, name), heads), ens,
        gd.kn.push(T.FrRep{name, vs, pp}, stack, kk, ch => ec => gd.na.repl(vs, name, pp, ch, ev, ec)))

def gd.nw.head(
  dot: Bool,
  +pp: String,
  +rows: List<&2, T.Val>,
  +name: String,
  +vs: List<&2, T.Val>,
  +val: T.Val,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +mark: Bool,
  rest: List<&2, String>,
  +skip: U32,
  +ens: {L2.gd.na(rows) == True{} : Bool},
  +ev: {L2.gd.na(vs) == True{} : Bool},
  kk: gd.Kn(stack),
  ih: gd.nIH(rest, val, inl, skip)
) -> {gd.endn(T.tree.walk(rest, T.tree.sub.head(dot, pp, rows, name, vs, T.JPut{val}, stack, pre, heads,
  inl, mark), skip)) == True{} : Bool}:
  match dot:
    case True{}:
      gd.nw.hgo(T.heads.head(heads, T.tree.pre(pre, name)), pp, rows, name, vs, val, stack, pre, heads,
        inl, mark, rest, skip, ens, ev, kk, ih)
    case False{}:
      gd.nw.hgo(False{}, pp, rows, name, vs, val, stack, pre, heads, inl, mark, rest, skip, ens, ev, kk, ih)

def gd.nw.sub(
  hit: T.Look,
  +name: String,
  +vs: List<&2, T.Val>,
  +val: T.Val,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +mark: Bool,
  rest: List<&2, String>,
  +skip: U32,
  +eh: {gd.nlk(hit) == True{} : Bool},
  +ev: {L2.gd.na(vs) == True{} : Bool},
  kk: gd.Kn(stack),
  ih: gd.nIH(rest, val, inl, skip)
) -> {gd.endn(T.tree.walk(rest, T.tree.sub.look(hit, name, vs, T.JPut{val}, stack, pre, heads, inl, mark),
  skip)) == True{} : Bool}:
  match hit:
    case T.KMiss{}:
      ih([], T.FrNew{name, vs, T.tree.pre(pre, name)} <> stack, "", T.tree.pre(pre, name),
        T.heads.define(T.tree.sub.job(mark, T.JPut{val}), T.tree.pre(pre, name), heads), {==},
        gd.kn.push(T.FrNew{name, vs, T.tree.pre(pre, name)}, stack, kk,
          ch => ec => gd.tt(L2.gd.na(ch), L2.gd.na(vs), ec, ev)))
    case T.KHead{+pp, +rows}:
      gd.nw.head(T.tree.sub.dot(T.tree.sub.job(mark, T.JPut{val})), pp, rows, name, vs, val, stack, pre, heads,
        inl, mark, rest, skip, eh, ev, kk, ih)
    case T.KInl{}:
      ih(vs, stack, "inline table is closed", pre, heads, {==}, kk)
    case T.KAots{+pp, +es}:
      Eq.bit.absurd(&2, {gd.endn(T.tree.walk(rest, T.tree.sub.look(T.KAots{pp, es}, name, vs, T.JPut{val},
        stack, pre, heads, inl, mark), skip)) == True{} : Bool}, eh)
    case T.KNo{+why}:
      ih(vs, stack, why, pre, heads, gd.ifok.any(String.is_empty(why), L2.gd.na(vs), ev), kk)

def gd.nw.step(
  +bad: String,
  +name: String,
  +vs: List<&2, T.Val>,
  +val: T.Val,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +mark: Bool,
  rest: List<&2, String>,
  +skip: U32,
  +ev: {L2.gd.ifok(String.is_empty(bad), L2.gd.na(vs)) == True{} : Bool},
  kk: gd.Kn(stack),
  ih: gd.nIH(rest, val, inl, skip)
) -> {gd.endn(T.tree.walk(rest, T.tree.sub(name, T.Tw{vs, T.JPut{val}, stack, bad, pre, heads, inl}, mark),
  skip)) == True{} : Bool}:
  match bad:
    case SNil{}:
      gd.nw.sub(T.rows.look(vs, name), name, vs, val, stack, pre, heads, inl, mark, rest, skip,
        gd.na.lk(vs, name, ev), ev, kk, ih)
    case SCon{+hh, +tt}:
      ih(vs, stack, SCon{hh, tt}, pre, heads, {==}, kk)

def gd.nw.put(
  hit: T.Hit,
  +name: String,
  +vs: List<&2, T.Val>,
  +val: T.Val,
  +stack: List<&2, T.Fr>,
  +heads: List<&2, String>,
  +ev: {L2.gd.na(vs) == True{} : Bool},
  +evk: {L2.gd.vok(val) == True{} : Bool},
  kk: gd.Kn(stack)
) -> {gd.endn(T.tree.leaf.put(hit, name, vs, val, stack, "", heads)) == True{} : Bool}:
  match hit:
    case T.Found{_v}:
      kk(vs, "duplicate key", heads, {==})
    case T.Miss{}:
      kk(T.VPair{name, val} <> vs, "", heads, gd.na.put(val, name, vs, evk, ev))

def gd.nw.leaf(
  +bad: String,
  +name: String,
  +vs: List<&2, T.Val>,
  +val: T.Val,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +ev: {L2.gd.ifok(String.is_empty(bad), L2.gd.na(vs)) == True{} : Bool},
  +evk: {L2.gd.vok(val) == True{} : Bool},
  kk: gd.Kn(stack)
) -> {gd.endn(T.tree.leaf(name, T.Tw{vs, T.JPut{val}, stack, bad, pre, heads, inl})) == True{} : Bool}:
  match bad:
    case SNil{}:
      gd.nw.put(T.get(vs, name), name, vs, val, stack, heads, ev, evk, kk)
    case SCon{+hh, +tt}:
      kk(vs, SCon{hh, tt}, heads, {==})

# a put's walk makes no array of tables
def gd.nw(
  path: List<&2, String>,
  +vs: List<&2, T.Val>,
  +val: T.Val,
  +stack: List<&2, T.Fr>,
  +bad: String,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +skip: U32,
  +evk: {L2.gd.vok(val) == True{} : Bool},
  +ev: {L2.gd.ifok(String.is_empty(bad), L2.gd.na(vs)) == True{} : Bool},
  kk: gd.Kn(stack)
) -> {gd.endn(T.tree.walk(path, T.Tw{vs, T.JPut{val}, stack, bad, pre, heads, inl}, skip)) == True{} : Bool}:
  match path:
    case []:
      kk(vs, T.err.first(bad, "empty key"), heads,
        gd.off(String.is_empty(T.err.first(bad, "empty key")), L2.gd.na(vs), gd.err.ne(bad)))
    case +name <> +rest:
      match rest:
        case []:
          gd.nw.leaf(bad, name, vs, val, stack, pre, heads, inl, ev, evk, kk)
        case +r1 <> +r2:
          gd.nw.step(bad, name, vs, val, stack, pre, heads, inl, U32.is_zero(skip), r1 <> r2, T.path.dec(skip),
            ev, kk,
            v2 => s2 => b2 => p2 => h2 => e2 => k2 => gd.nw(r1 <> r2, v2, val, s2, b2, p2, h2, inl,
              T.path.dec(skip), evk, e2, k2))

# inl.seal keeps every name
def gd.is.names(
  tt: List<&2, T.Val>,
  +kk: String
) -> {T.wf.fresh(T.get(T.inl.seal(tt), kk)) == T.wf.fresh(T.get(tt, kk)) : Bool}:
  match tt:
    case []:
      {==}
    case T.VPair{+n, T.VStr{+s}} <> +t:
      gd.fr.b2(T.str.eq(n, kk), T.VStr{s}, T.VStr{s}, T.inl.seal(t), t, kk, gd.is.names(t, kk))
    case T.VPair{+n, T.VSpan{+q, +s}} <> +t:
      gd.fr.b2(T.str.eq(n, kk), T.VSpan{q, s}, T.VSpan{q, s}, T.inl.seal(t), t, kk, gd.is.names(t, kk))
    case T.VPair{+n, T.VInt{+q, +s}} <> +t:
      gd.fr.b2(T.str.eq(n, kk), T.VInt{q, s}, T.VInt{q, s}, T.inl.seal(t), t, kk, gd.is.names(t, kk))
    case T.VPair{+n, T.VFlo{+q, +s}} <> +t:
      gd.fr.b2(T.str.eq(n, kk), T.VFlo{q, s}, T.VFlo{q, s}, T.inl.seal(t), t, kk, gd.is.names(t, kk))
    case T.VPair{+n, T.VBool{+s}} <> +t:
      gd.fr.b2(T.str.eq(n, kk), T.VBool{s}, T.VBool{s}, T.inl.seal(t), t, kk, gd.is.names(t, kk))
    case T.VPair{+n, T.VWhen{+s}} <> +t:
      gd.fr.b2(T.str.eq(n, kk), T.VWhen{s}, T.VWhen{s}, T.inl.seal(t), t, kk, gd.is.names(t, kk))
    case T.VPair{+n, T.VArr{+s}} <> +t:
      gd.fr.b2(T.str.eq(n, kk), T.VArr{s}, T.VArr{s}, T.inl.seal(t), t, kk, gd.is.names(t, kk))
    case T.VPair{+n, T.VInl{+s}} <> +t:
      gd.fr.b2(T.str.eq(n, kk), T.VInl{s}, T.VInl{s}, T.inl.seal(t), t, kk, gd.is.names(t, kk))
    case T.VPair{+n, T.VHead{+q, +s}} <> +t:
      gd.fr.b2(T.str.eq(n, kk), T.VInl{T.inl.seal(s)}, T.VHead{q, s}, T.inl.seal(t), t, kk, gd.is.names(t, kk))
    case T.VPair{+n, T.VAot{+q, +s}} <> +t:
      gd.fr.b2(T.str.eq(n, kk), T.VAot{q, s}, T.VAot{q, s}, T.inl.seal(t), t, kk, gd.is.names(t, kk))
    case T.VPair{+n, T.VAots{+q, +s}} <> +t:
      gd.fr.b2(T.str.eq(n, kk), T.VAots{q, s}, T.VAots{q, s}, T.inl.seal(t), t, kk, gd.is.names(t, kk))
    case T.VPair{+n, T.VPair{+q, +s}} <> +t:
      gd.fr.b2(T.str.eq(n, kk), T.VPair{q, s}, T.VPair{q, s}, T.inl.seal(t), t, kk, gd.is.names(t, kk))
    case T.VStr{_r} <> +t:
      gd.is.names(t, kk)
    case T.VSpan{_p, _r} <> +t:
      gd.is.names(t, kk)
    case T.VInt{_p, _r} <> +t:
      gd.is.names(t, kk)
    case T.VFlo{_p, _r} <> +t:
      gd.is.names(t, kk)
    case T.VBool{_r} <> +t:
      gd.is.names(t, kk)
    case T.VWhen{_r} <> +t:
      gd.is.names(t, kk)
    case T.VArr{_r} <> +t:
      gd.is.names(t, kk)
    case T.VInl{_r} <> +t:
      gd.is.names(t, kk)
    case T.VHead{_p, _r} <> +t:
      gd.is.names(t, kk)
    case T.VAot{_p, _r} <> +t:
      gd.is.names(t, kk)
    case T.VAots{_p, _r} <> +t:
      gd.is.names(t, kk)

# a table's rows with no array of tables seal into an inline table's
def gd.is(
  rows: List<&2, T.Val>,
  +pp: String,
  +ew: {T.wf.go(rows, T.WfRows{pp}) == True{} : Bool},
  +en: {L2.gd.na(rows) == True{} : Bool}
) -> {T.wf.go(T.inl.seal(rows), T.WfInl{}) == True{} : Bool}:
  match rows:
    case []:
      {==}
    case T.VPair{+n, T.VStr{+s}} <> +t:
      gd.gen.mk(T.VPair{n, T.VStr{s}}, T.inl.seal(t), T.WfInl{},
        gd.tt(T.wf.key(n, T.inl.seal(t)), L2.gd.vok(T.VStr{s}),
          Equal.trans(Bool, T.wf.key(n, T.inl.seal(t)), T.wf.key(n, t), True{},
          Equal.cong(Bool, Bool, xx => Bool.and(T.wf.text(n), xx), T.wf.fresh(T.get(T.inl.seal(t), n)),
            T.wf.fresh(T.get(t, n)), gd.is.names(t, n)),
          gd.pr.k(pp, n, T.VStr{s}, t, ew)),
          gd.pr.v(pp, n, T.VStr{s}, t, ew)),
        gd.is(t, pp, gd.pr.d(pp, n, T.VStr{s}, t, ew), en))
    case T.VPair{+n, T.VSpan{+q, +s}} <> +t:
      gd.gen.mk(T.VPair{n, T.VSpan{q, s}}, T.inl.seal(t), T.WfInl{},
        gd.tt(T.wf.key(n, T.inl.seal(t)), L2.gd.vok(T.VSpan{q, s}),
          Equal.trans(Bool, T.wf.key(n, T.inl.seal(t)), T.wf.key(n, t), True{},
          Equal.cong(Bool, Bool, xx => Bool.and(T.wf.text(n), xx), T.wf.fresh(T.get(T.inl.seal(t), n)),
            T.wf.fresh(T.get(t, n)), gd.is.names(t, n)),
          gd.pr.k(pp, n, T.VSpan{q, s}, t, ew)),
          gd.pr.v(pp, n, T.VSpan{q, s}, t, ew)),
        gd.is(t, pp, gd.pr.d(pp, n, T.VSpan{q, s}, t, ew), en))
    case T.VPair{+n, T.VInt{+q, +s}} <> +t:
      gd.gen.mk(T.VPair{n, T.VInt{q, s}}, T.inl.seal(t), T.WfInl{},
        gd.tt(T.wf.key(n, T.inl.seal(t)), L2.gd.vok(T.VInt{q, s}),
          Equal.trans(Bool, T.wf.key(n, T.inl.seal(t)), T.wf.key(n, t), True{},
          Equal.cong(Bool, Bool, xx => Bool.and(T.wf.text(n), xx), T.wf.fresh(T.get(T.inl.seal(t), n)),
            T.wf.fresh(T.get(t, n)), gd.is.names(t, n)),
          gd.pr.k(pp, n, T.VInt{q, s}, t, ew)),
          gd.pr.v(pp, n, T.VInt{q, s}, t, ew)),
        gd.is(t, pp, gd.pr.d(pp, n, T.VInt{q, s}, t, ew), en))
    case T.VPair{+n, T.VFlo{+q, +s}} <> +t:
      gd.gen.mk(T.VPair{n, T.VFlo{q, s}}, T.inl.seal(t), T.WfInl{},
        gd.tt(T.wf.key(n, T.inl.seal(t)), L2.gd.vok(T.VFlo{q, s}),
          Equal.trans(Bool, T.wf.key(n, T.inl.seal(t)), T.wf.key(n, t), True{},
          Equal.cong(Bool, Bool, xx => Bool.and(T.wf.text(n), xx), T.wf.fresh(T.get(T.inl.seal(t), n)),
            T.wf.fresh(T.get(t, n)), gd.is.names(t, n)),
          gd.pr.k(pp, n, T.VFlo{q, s}, t, ew)),
          gd.pr.v(pp, n, T.VFlo{q, s}, t, ew)),
        gd.is(t, pp, gd.pr.d(pp, n, T.VFlo{q, s}, t, ew), en))
    case T.VPair{+n, T.VBool{+s}} <> +t:
      gd.gen.mk(T.VPair{n, T.VBool{s}}, T.inl.seal(t), T.WfInl{},
        gd.tt(T.wf.key(n, T.inl.seal(t)), L2.gd.vok(T.VBool{s}),
          Equal.trans(Bool, T.wf.key(n, T.inl.seal(t)), T.wf.key(n, t), True{},
          Equal.cong(Bool, Bool, xx => Bool.and(T.wf.text(n), xx), T.wf.fresh(T.get(T.inl.seal(t), n)),
            T.wf.fresh(T.get(t, n)), gd.is.names(t, n)),
          gd.pr.k(pp, n, T.VBool{s}, t, ew)),
          gd.pr.v(pp, n, T.VBool{s}, t, ew)),
        gd.is(t, pp, gd.pr.d(pp, n, T.VBool{s}, t, ew), en))
    case T.VPair{+n, T.VWhen{+s}} <> +t:
      gd.gen.mk(T.VPair{n, T.VWhen{s}}, T.inl.seal(t), T.WfInl{},
        gd.tt(T.wf.key(n, T.inl.seal(t)), L2.gd.vok(T.VWhen{s}),
          Equal.trans(Bool, T.wf.key(n, T.inl.seal(t)), T.wf.key(n, t), True{},
          Equal.cong(Bool, Bool, xx => Bool.and(T.wf.text(n), xx), T.wf.fresh(T.get(T.inl.seal(t), n)),
            T.wf.fresh(T.get(t, n)), gd.is.names(t, n)),
          gd.pr.k(pp, n, T.VWhen{s}, t, ew)),
          gd.pr.v(pp, n, T.VWhen{s}, t, ew)),
        gd.is(t, pp, gd.pr.d(pp, n, T.VWhen{s}, t, ew), en))
    case T.VPair{+n, T.VArr{+s}} <> +t:
      gd.gen.mk(T.VPair{n, T.VArr{s}}, T.inl.seal(t), T.WfInl{},
        gd.tt(T.wf.key(n, T.inl.seal(t)), L2.gd.vok(T.VArr{s}),
          Equal.trans(Bool, T.wf.key(n, T.inl.seal(t)), T.wf.key(n, t), True{},
          Equal.cong(Bool, Bool, xx => Bool.and(T.wf.text(n), xx), T.wf.fresh(T.get(T.inl.seal(t), n)),
            T.wf.fresh(T.get(t, n)), gd.is.names(t, n)),
          gd.pr.k(pp, n, T.VArr{s}, t, ew)),
          gd.pr.v(pp, n, T.VArr{s}, t, ew)),
        gd.is(t, pp, gd.pr.d(pp, n, T.VArr{s}, t, ew), en))
    case T.VPair{+n, T.VInl{+s}} <> +t:
      gd.gen.mk(T.VPair{n, T.VInl{s}}, T.inl.seal(t), T.WfInl{},
        gd.tt(T.wf.key(n, T.inl.seal(t)), L2.gd.vok(T.VInl{s}),
          Equal.trans(Bool, T.wf.key(n, T.inl.seal(t)), T.wf.key(n, t), True{},
          Equal.cong(Bool, Bool, xx => Bool.and(T.wf.text(n), xx), T.wf.fresh(T.get(T.inl.seal(t), n)),
            T.wf.fresh(T.get(t, n)), gd.is.names(t, n)),
          gd.pr.k(pp, n, T.VInl{s}, t, ew)),
          gd.pr.v(pp, n, T.VInl{s}, t, ew)),
        gd.is(t, pp, gd.pr.d(pp, n, T.VInl{s}, t, ew), en))
    case T.VPair{+n, T.VHead{+q, +s}} <> +t:
      gd.gen.mk(T.VPair{n, T.VInl{T.inl.seal(s)}}, T.inl.seal(t), T.WfInl{},
        gd.tt(T.wf.key(n, T.inl.seal(t)), T.wf.go(T.inl.seal(s), T.WfInl{}),
          Equal.trans(Bool, T.wf.key(n, T.inl.seal(t)), T.wf.key(n, t), True{},
          Equal.cong(Bool, Bool, xx => Bool.and(T.wf.text(n), xx), T.wf.fresh(T.get(T.inl.seal(t), n)),
            T.wf.fresh(T.get(t, n)), gd.is.names(t, n)),
          gd.pr.k(pp, n, T.VHead{q, s}, t, ew)),
          gd.is(s, q, gd.r(T.str.eq(q, T.tree.pre(pp, n)), T.wf.go(s, T.WfRows{q}), gd.pr.v(pp, n, T.VHead{q, s}, t,
            ew)), gd.l(L2.gd.na(s), L2.gd.na(t), en))),
        gd.is(t, pp, gd.pr.d(pp, n, T.VHead{q, s}, t, ew), gd.r(L2.gd.na(s), L2.gd.na(t), en)))
    case T.VPair{+n, T.VAot{+q, +s}} <> +t:
      gd.gen.mk(T.VPair{n, T.VAot{q, s}}, T.inl.seal(t), T.WfInl{},
        gd.tt(T.wf.key(n, T.inl.seal(t)), L2.gd.vok(T.VAot{q, s}),
          Equal.trans(Bool, T.wf.key(n, T.inl.seal(t)), T.wf.key(n, t), True{},
          Equal.cong(Bool, Bool, xx => Bool.and(T.wf.text(n), xx), T.wf.fresh(T.get(T.inl.seal(t), n)),
            T.wf.fresh(T.get(t, n)), gd.is.names(t, n)),
          gd.pr.k(pp, n, T.VAot{q, s}, t, ew)),
          gd.pr.v(pp, n, T.VAot{q, s}, t, ew)),
        gd.is(t, pp, gd.pr.d(pp, n, T.VAot{q, s}, t, ew), en))
    case T.VPair{+n, T.VAots{+q, +s}} <> +t:
      Eq.bit.absurd(&2, {T.wf.go(T.inl.seal(T.VPair{n, T.VAots{q, s}} <> t), T.WfInl{}) == True{} : Bool}, en)
    case T.VPair{+n, T.VPair{+q, +s}} <> +t:
      gd.gen.mk(T.VPair{n, T.VPair{q, s}}, T.inl.seal(t), T.WfInl{},
        gd.tt(T.wf.key(n, T.inl.seal(t)), L2.gd.vok(T.VPair{q, s}),
          Equal.trans(Bool, T.wf.key(n, T.inl.seal(t)), T.wf.key(n, t), True{},
          Equal.cong(Bool, Bool, xx => Bool.and(T.wf.text(n), xx), T.wf.fresh(T.get(T.inl.seal(t), n)),
            T.wf.fresh(T.get(t, n)), gd.is.names(t, n)),
          gd.pr.k(pp, n, T.VPair{q, s}, t, ew)),
          gd.pr.v(pp, n, T.VPair{q, s}, t, ew)),
        gd.is(t, pp, gd.pr.d(pp, n, T.VPair{q, s}, t, ew), en))
    case T.VStr{+r} <> +t:
      Eq.bit.absurd(&2, {T.wf.go(T.inl.seal(T.VStr{r} <> t), T.WfInl{}) == True{} : Bool}, ew)
    case T.VSpan{+p, +r} <> +t:
      Eq.bit.absurd(&2, {T.wf.go(T.inl.seal(T.VSpan{p, r} <> t), T.WfInl{}) == True{} : Bool}, ew)
    case T.VInt{+p, +r} <> +t:
      Eq.bit.absurd(&2, {T.wf.go(T.inl.seal(T.VInt{p, r} <> t), T.WfInl{}) == True{} : Bool}, ew)
    case T.VFlo{+p, +r} <> +t:
      Eq.bit.absurd(&2, {T.wf.go(T.inl.seal(T.VFlo{p, r} <> t), T.WfInl{}) == True{} : Bool}, ew)
    case T.VBool{+r} <> +t:
      Eq.bit.absurd(&2, {T.wf.go(T.inl.seal(T.VBool{r} <> t), T.WfInl{}) == True{} : Bool}, ew)
    case T.VWhen{+r} <> +t:
      Eq.bit.absurd(&2, {T.wf.go(T.inl.seal(T.VWhen{r} <> t), T.WfInl{}) == True{} : Bool}, ew)
    case T.VArr{+r} <> +t:
      Eq.bit.absurd(&2, {T.wf.go(T.inl.seal(T.VArr{r} <> t), T.WfInl{}) == True{} : Bool}, ew)
    case T.VInl{+r} <> +t:
      Eq.bit.absurd(&2, {T.wf.go(T.inl.seal(T.VInl{r} <> t), T.WfInl{}) == True{} : Bool}, ew)
    case T.VHead{+p, +r} <> +t:
      Eq.bit.absurd(&2, {T.wf.go(T.inl.seal(T.VHead{p, r} <> t), T.WfInl{}) == True{} : Bool}, ew)
    case T.VAot{+p, +r} <> +t:
      Eq.bit.absurd(&2, {T.wf.go(T.inl.seal(T.VAot{p, r} <> t), T.WfInl{}) == True{} : Bool}, ew)
    case T.VAots{+p, +r} <> +t:
      Eq.bit.absurd(&2, {T.wf.go(T.inl.seal(T.VAots{p, r} <> t), T.WfInl{}) == True{} : Bool}, ew)

# WP-R3: a finished value placed. At the root its key's walk puts it
# (gd_walk); in an array it goes in front of the items; in an inline table
# its key walks from "" in the inline table's rows (gd_walk and gd.nw).

# segments of scalar values joined
def gd.segs.app(
  aa: List<&2, String>,
  +bb: List<&2, String>,
  +ea: {L2.gd.segs(aa) == True{} : Bool},
  +eb: {L2.gd.segs(bb) == True{} : Bool}
) -> {L2.gd.segs(List.append(&2, String, aa, bb)) == True{} : Bool}:
  match aa:
    case []:
      eb
    case +h <> +t:
      gd.tt(T.wf.text(h), L2.gd.segs(List.append(&2, String, t, bb)), gd.l(T.wf.text(h), L2.gd.segs(t), ea),
        gd.segs.app(t, bb, gd.r(T.wf.text(h), L2.gd.segs(t), ea), eb))

# a value a key may hold may be an array's item
def gd.vok.h1(
  vv: T.Val,
  +t: List<&2, T.Val>,
  +ev: {L2.gd.vok(vv) == True{} : Bool}
) -> {gd.h1(vv, t, T.WfItems{}) == True{} : Bool}:
  match vv:
    case T.VStr{+r}:
      ev
    case T.VSpan{+p, +r}:
      ev
    case T.VInt{+p, +r}:
      ev
    case T.VFlo{+p, +r}:
      ev
    case T.VBool{+r}:
      ev
    case T.VWhen{+r}:
      ev
    case T.VArr{+r}:
      ev
    case T.VInl{+r}:
      ev
    case T.VHead{+p, +r}:
      Eq.bit.absurd(&2, {gd.h1(T.VHead{p, r}, t, T.WfItems{}) == True{} : Bool}, ev)
    case T.VAot{+p, +r}:
      Eq.bit.absurd(&2, {gd.h1(T.VAot{p, r}, t, T.WfItems{}) == True{} : Bool}, ev)
    case T.VAots{+p, +r}:
      Eq.bit.absurd(&2, {gd.h1(T.VAots{p, r}, t, T.WfItems{}) == True{} : Bool}, ev)
    case T.VPair{+p, +r}:
      Eq.bit.absurd(&2, {gd.h1(T.VPair{p, r}, t, T.WfItems{}) == True{} : Bool}, ev)

# a value put at the root: the root the walk returned, the key's table as the
# current one, and nothing pending
def gd.g.troot(
  end: T.End,
  +here: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +lead: Bool,
  +ee: {L2.gd.end(end) == True{} : Bool},
  +eh: {L2.gd.segs(here) == True{} : Bool}
) -> {L2.good(T.take.root(end, here, back, qkind, uni, left, arrtab, lead)) == True{} : Bool}:
  match end:
    case T.End{+vs, +bad, +hs}:
      gd.tt(L2.gd.tr(bad, vs, []), L2.gd.lx(here, [], [], [], T.HNone{}),
        gd.ifok.t(String.is_empty(bad), T.wf.go(vs, T.WfRows{""}), ee),
        gd.tt(L2.gd.segs(here), True{}, eh, {==}))

# the frames' keys, and the current table's and the key's taken from the top
def gd.keys3(
  +saved: List<&2, String>,
  +at: List<&2, String>,
  +rest: List<&2, T.Ctx>,
  +ek: {Bool.and(L2.gd.segs(saved), Bool.and(L2.gd.segs(at), L2.gd.keys(rest))) == True{} : Bool}
) -> {Bool.and(L2.gd.segs(at), Bool.and(L2.gd.segs(saved),
    Bool.and(Bool.and(L2.gd.segs(saved), Bool.and(L2.gd.segs(at), L2.gd.keys(rest))), True{}))) == True{} : Bool}:
  gd.tt(L2.gd.segs(at), Bool.and(L2.gd.segs(saved),
    Bool.and(Bool.and(L2.gd.segs(saved), Bool.and(L2.gd.segs(at), L2.gd.keys(rest))), True{})),
    gd.l(L2.gd.segs(at), L2.gd.keys(rest),
      gd.r(L2.gd.segs(saved), Bool.and(L2.gd.segs(at), L2.gd.keys(rest)), ek)),
    gd.tt(L2.gd.segs(saved), Bool.and(Bool.and(L2.gd.segs(saved), Bool.and(L2.gd.segs(at),
      L2.gd.keys(rest))), True{}),
      gd.l(L2.gd.segs(saved), Bool.and(L2.gd.segs(at), L2.gd.keys(rest)), ek),
      gd.tt(Bool.and(L2.gd.segs(saved), Bool.and(L2.gd.segs(at), L2.gd.keys(rest))), True{}, ek, {==})))

# an item in front of an array's items
def gd.tarr.tr(
  ok: Bool,
  +rows: List<&2, T.Val>,
  +items: List<&2, T.Val>,
  +vv: T.Val,
  +rest: List<&2, T.Ctx>,
  +et: {L2.gd.ifok(ok, gd.ra(rows, items, rest)) == True{} : Bool},
  +ev: {L2.gd.ifok(ok, L2.gd.vok(vv)) == True{} : Bool}
) -> {L2.gd.ifok(ok, Bool.and(T.wf.go(rows, T.WfRows{""}), Bool.and(T.wf.go(vv <> items, T.WfItems{}),
    L2.gd.vals(rest)))) == True{} : Bool}:
  match ok:
    case False{}:
      {==}
    case True{}:
      gd.tt(T.wf.go(rows, T.WfRows{""}), Bool.and(T.wf.go(vv <> items, T.WfItems{}), L2.gd.vals(rest)),
        gd.l(T.wf.go(rows, T.WfRows{""}), Bool.and(T.wf.go(items, T.WfItems{}), L2.gd.vals(rest)), et),
        gd.tt(T.wf.go(vv <> items, T.WfItems{}), L2.gd.vals(rest),
          gd.gen.mk(vv, items, T.WfItems{}, gd.vok.h1(vv, items, ev),
            gd.l(T.wf.go(items, T.WfItems{}), L2.gd.vals(rest),
              gd.r(T.wf.go(rows, T.WfRows{""}), Bool.and(T.wf.go(items, T.WfItems{}), L2.gd.vals(rest)), et))),
          gd.r(T.wf.go(items, T.WfItems{}), L2.gd.vals(rest),
            gd.r(T.wf.go(rows, T.WfRows{""}), Bool.and(T.wf.go(items, T.WfItems{}), L2.gd.vals(rest)), et))))

# an inline table's rows after its key's walk, under the walk's error
def gd.ifok.inl(
  ok: Bool,
  +rows: List<&2, T.Val>,
  +inl: List<&2, T.Val>,
  +rest: List<&2, T.Ctx>,
  +ew: {L2.gd.ifok(ok, T.wf.go(inl, T.WfRows{""})) == True{} : Bool},
  +en: {L2.gd.ifok(ok, L2.gd.na(inl)) == True{} : Bool},
  +eo: {Bool.and(T.wf.go(rows, T.WfRows{""}), L2.gd.vals(rest)) == True{} : Bool}
) -> {L2.gd.ifok(ok, Bool.and(T.wf.go(rows, T.WfRows{""}), Bool.and(Bool.and(T.wf.go(inl, T.WfRows{""}),
    L2.gd.na(inl)), L2.gd.vals(rest)))) == True{} : Bool}:
  match ok:
    case False{}:
      {==}
    case True{}:
      gd.tt(T.wf.go(rows, T.WfRows{""}), Bool.and(Bool.and(T.wf.go(inl, T.WfRows{""}), L2.gd.na(inl)),
        L2.gd.vals(rest)),
        gd.l(T.wf.go(rows, T.WfRows{""}), L2.gd.vals(rest), eo),
        gd.tt(Bool.and(T.wf.go(inl, T.WfRows{""}), L2.gd.na(inl)), L2.gd.vals(rest),
          gd.tt(T.wf.go(inl, T.WfRows{""}), L2.gd.na(inl), ew, en),
          gd.r(T.wf.go(rows, T.WfRows{""}), L2.gd.vals(rest), eo)))

# a value put in an inline table: its rows after the walk, the frame back
def gd.g.tinl(
  end: T.End,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +at: List<&2, String>,
  +saved: List<&2, String>,
  +rest: List<&2, T.Ctx>,
  +back: T.Lex,
  +qkind: T.QKind,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +lead: Bool,
  +ee: {L2.gd.end(end) == True{} : Bool},
  +en: {gd.endn(end) == True{} : Bool},
  +eo: {Bool.and(T.wf.go(rows, T.WfRows{""}), L2.gd.vals(rest)) == True{} : Bool},
  +ek: {Bool.and(L2.gd.segs(saved), Bool.and(L2.gd.segs(at), L2.gd.keys(rest))) == True{} : Bool}
) -> {L2.good(T.take.inl(end, rows, heads, at, saved, rest, back, qkind, uni, left, arrtab, lead))
    == True{} : Bool}:
  match end:
    case T.End{+inl, +bad, +hs}:
      gd.tt(L2.gd.tr(bad, rows, T.CInl{inl, saved, at} <> rest),
        L2.gd.lx(at, [], [], T.CInl{inl, saved, at} <> rest, T.HNone{}),
        gd.ifok.inl(String.is_empty(bad), rows, inl, rest, ee, en, eo),
        gd.tt(L2.gd.segs(at), Bool.and(Bool.and(L2.gd.segs(saved), Bool.and(L2.gd.segs(at),
          L2.gd.keys(rest))), True{}),
          gd.l(L2.gd.segs(at), L2.gd.keys(rest),
            gd.r(L2.gd.segs(saved), Bool.and(L2.gd.segs(at), L2.gd.keys(rest)), ek)),
          gd.tt(Bool.and(L2.gd.segs(saved), Bool.and(L2.gd.segs(at), L2.gd.keys(rest))), True{}, ek, {==})))

# the inline table's key walks, unless the scanner has failed
def gd.g.tinl.bad(
  +bad: String,
  +val: T.Val,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +parts: List<&2, String>,
  +inl: List<&2, T.Val>,
  +saved: List<&2, String>,
  +at: List<&2, String>,
  +rest: List<&2, T.Ctx>,
  +back: T.Lex,
  +qkind: T.QKind,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +lead: Bool,
  +et: {L2.gd.tr(bad, rows, T.CInl{inl, saved, at} <> rest) == True{} : Bool},
  +ep: {L2.gd.segs(parts) == True{} : Bool},
  +ek: {Bool.and(L2.gd.segs(saved), Bool.and(L2.gd.segs(at), L2.gd.keys(rest))) == True{} : Bool},
  +ev: {L2.gd.ifok(String.is_empty(bad), L2.gd.vok(val)) == True{} : Bool}
) -> {L2.good(T.take.inl(T.tree.walk(List.reverse(&2, String, parts), T.Tw{inl, T.JPut{val}, [], bad, "", [],
  True{}}, 0), rows, heads, at, saved, rest, back, qkind, uni, left, arrtab, lead)) == True{} : Bool}:
  match bad:
    case SNil{}:
      gd.g.tinl(T.tree.walk(List.reverse(&2, String, parts), T.Tw{inl, T.JPut{val}, [], "", "", [], True{}}, 0),
        rows, heads, at, saved, rest, back, qkind, uni, left, arrtab, lead,
        L2.gd_walk(List.reverse(&2, String, parts), inl, T.JPut{val}, "", [], True{}, 0,
          gd.l(T.wf.go(inl, T.WfRows{""}), L2.gd.na(inl),
            gd.l(Bool.and(T.wf.go(inl, T.WfRows{""}), L2.gd.na(inl)), L2.gd.vals(rest),
              gd.r(T.wf.go(rows, T.WfRows{""}), Bool.and(Bool.and(T.wf.go(inl, T.WfRows{""}), L2.gd.na(inl)),
                L2.gd.vals(rest)), et))),
          gd.segs.rev(parts, [], ep, {==}), ev),
        gd.nw(List.reverse(&2, String, parts), inl, val, [], "", "", [], True{}, 0, ev,
          gd.r(T.wf.go(inl, T.WfRows{""}), L2.gd.na(inl),
            gd.l(Bool.and(T.wf.go(inl, T.WfRows{""}), L2.gd.na(inl)), L2.gd.vals(rest),
              gd.r(T.wf.go(rows, T.WfRows{""}), Bool.and(Bool.and(T.wf.go(inl, T.WfRows{""}), L2.gd.na(inl)),
                L2.gd.vals(rest)), et))),
          gd.kn.root()),
        gd.tt(T.wf.go(rows, T.WfRows{""}), L2.gd.vals(rest),
          gd.l(T.wf.go(rows, T.WfRows{""}), Bool.and(Bool.and(T.wf.go(inl, T.WfRows{""}), L2.gd.na(inl)),
            L2.gd.vals(rest)), et),
          gd.r(Bool.and(T.wf.go(inl, T.WfRows{""}), L2.gd.na(inl)), L2.gd.vals(rest),
            gd.r(T.wf.go(rows, T.WfRows{""}), Bool.and(Bool.and(T.wf.go(inl, T.WfRows{""}), L2.gd.na(inl)),
              L2.gd.vals(rest)), et))),
        ek)
    case SCon{+hh, +tt}:
      Equal.trans(Bool,
        L2.good(T.take.inl(T.tree.walk(List.reverse(&2, String, parts), T.Tw{inl, T.JPut{val}, [], SCon{hh, tt},
          "", [], True{}}, 0), rows, heads, at, saved, rest, back, qkind, uni, left, arrtab, lead)),
        L2.good(T.take.inl(T.End{inl, SCon{hh, tt}, []}, rows, heads, at, saved, rest, back, qkind, uni, left,
          arrtab, lead)),
        True{},
        Equal.cong(T.End, Bool, ee => L2.good(T.take.inl(ee, rows, heads, at, saved, rest, back, qkind, uni, left,
          arrtab, lead)),
          T.tree.walk(List.reverse(&2, String, parts), T.Tw{inl, T.JPut{val}, [], SCon{hh, tt}, "", [], True{}}, 0),
          T.End{inl, SCon{hh, tt}, []},
          L1.failed_walk_changes_nothing(List.reverse(&2, String, parts), inl, T.JPut{val}, SCon{hh, tt}, "", [],
            True{}, 0, {==})),
        gd.tt(True{}, L2.gd.lx(at, [], [], T.CInl{inl, saved, at} <> rest, T.HNone{}), {==},
          gd.tt(L2.gd.segs(at), Bool.and(Bool.and(L2.gd.segs(saved), Bool.and(L2.gd.segs(at),
            L2.gd.keys(rest))), True{}),
            gd.l(L2.gd.segs(at), L2.gd.keys(rest),
              gd.r(L2.gd.segs(saved), Bool.and(L2.gd.segs(at), L2.gd.keys(rest)), ek)),
            gd.tt(Bool.and(L2.gd.segs(saved), Bool.and(L2.gd.segs(at), L2.gd.keys(rest))), True{}, ek, {==}))))

# a value put at the root, unless the scanner has failed
def gd.g.troot.bad(
  +bad: String,
  +val: T.Val,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +buf: List<&2, Char>,
  +hold: T.Hold,
  +back: T.Lex,
  +qkind: T.QKind,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +lead: Bool,
  +et: {L2.gd.tr(bad, rows, []) == True{} : Bool},
  +el: {L2.gd.lx(here, parts, buf, [], hold) == True{} : Bool},
  +ev: {L2.gd.ifok(String.is_empty(bad), L2.gd.vok(val)) == True{} : Bool}
) -> {L2.good(T.take.root(T.tree.walk(T.path.cat(here, parts), T.Tw{rows, T.JPut{val}, [], bad, "", heads,
  False{}}, T.path.len(here, 0)), here, back, qkind, uni, left, arrtab, lead)) == True{} : Bool}:
  match bad:
    case SNil{}:
      gd.g.troot(T.tree.walk(T.path.cat(here, parts), T.Tw{rows, T.JPut{val}, [], "", "", heads, False{}},
        T.path.len(here, 0)), here, back, qkind, uni, left, arrtab, lead,
        L2.gd_walk(T.path.cat(here, parts), rows, T.JPut{val}, "", heads, False{}, T.path.len(here, 0),
          gd.ifok.l(True{}, T.wf.go(rows, T.WfRows{""}), True{}, et),
          gd.segs.app(here, List.reverse(&2, String, parts), gd.lx.h(here, parts, buf, [], hold, el),
            gd.segs.rev(parts, [], gd.lx.p(here, parts, buf, [], hold, el), {==})),
          ev),
        gd.lx.h(here, parts, buf, [], hold, el))
    case SCon{+hh, +tt}:
      Equal.trans(Bool,
        L2.good(T.take.root(T.tree.walk(T.path.cat(here, parts), T.Tw{rows, T.JPut{val}, [], SCon{hh, tt}, "",
          heads, False{}}, T.path.len(here, 0)), here, back, qkind, uni, left, arrtab, lead)),
        L2.good(T.take.root(T.End{rows, SCon{hh, tt}, heads}, here, back, qkind, uni, left, arrtab, lead)),
        True{},
        Equal.cong(T.End, Bool, ee => L2.good(T.take.root(ee, here, back, qkind, uni, left, arrtab, lead)),
          T.tree.walk(T.path.cat(here, parts), T.Tw{rows, T.JPut{val}, [], SCon{hh, tt}, "", heads, False{}},
            T.path.len(here, 0)),
          T.End{rows, SCon{hh, tt}, heads},
          L1.failed_walk_changes_nothing(T.path.cat(here, parts), rows, T.JPut{val}, SCon{hh, tt}, "", heads,
            False{}, T.path.len(here, 0), {==})),
        gd.g.troot(T.End{rows, SCon{hh, tt}, heads}, here, back, qkind, uni, left, arrtab, lead, {==},
          gd.lx.h(here, parts, buf, [], hold, el)))

# where a finished value goes
def gd.g.ttop(
  stack: List<&2, T.Ctx>,
  +val: T.Val,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +buf: List<&2, Char>,
  +hold: T.Hold,
  +back: T.Lex,
  +qkind: T.QKind,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +lead: Bool,
  +et: {L2.gd.tr(bad, rows, stack) == True{} : Bool},
  +el: {L2.gd.lx(here, parts, buf, stack, hold) == True{} : Bool},
  +ev: {L2.gd.ifok(String.is_empty(bad), L2.gd.vok(val)) == True{} : Bool}
) -> {L2.good(T.take.top(stack, val, bad, rows, heads, here, parts, back, qkind, uni, left, arrtab, lead))
  == True{} : Bool}:
  match stack:
    case []:
      gd.g.troot.bad(bad, val, rows, heads, here, parts, buf, hold, back, qkind, uni, left, arrtab, lead, et, el, ev)
    case T.CArr{+items, +saved, +at} <> +rest:
      gd.tt(L2.gd.tr(bad, rows, T.CArr{val <> items, saved, at} <> rest),
        L2.gd.lx(at, saved, [], T.CArr{val <> items, saved, at} <> rest, T.HNone{}),
        gd.tarr.tr(String.is_empty(bad), rows, items, val, rest, et, ev),
        gd.keys3(saved, at, rest, gd.lx.s(here, parts, buf, T.CArr{items, saved, at} <> rest, hold, el)))
    case T.CInl{+inl, +saved, +at} <> +rest:
      gd.g.tinl.bad(bad, val, rows, heads, parts, inl, saved, at, rest, back, qkind, uni, left, arrtab, lead, et,
        gd.lx.p(here, parts, buf, T.CInl{inl, saved, at} <> rest, hold, el),
        gd.lx.s(here, parts, buf, T.CInl{inl, saved, at} <> rest, hold, el), ev)

# a finished value placed, from any good state
def gd.g.take(
  +st: T.St,
  +val: T.Val,
  +eg: {L2.good(st) == True{} : Bool},
  +ev: {L2.gd.okv(st, val) == True{} : Bool}
) -> {L2.good(T.val.take(st, val)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.g.ttop(stack, val, bad, rows, heads, here, parts, buf, hold, back, qkind, uni, left, arrtab, lead,
        gd.l(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg),
        gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg), ev)

# WP-R3: the value states other than a bare value's. Strings push scalar
# values and end in val.take (gd.g.take), arrays and inline tables open a
# frame and close into a value that seals well-formed.

def gd.g.hold(
  +st: T.St,
  +lex2: T.Lex,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.st.hold(st, lex2, cc)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.tt(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, T.HChar{cc}), gd.l(L2.gd.tr(bad, rows,
        stack), L2.gd.lx(here, parts, buf, stack, hold), eg),
        gd.lx.mk(here, parts, buf, stack, T.HChar{cc}, gd.lx.h(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad,
          rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)), gd.lx.p(here, parts, buf, stack, hold,
          gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)), gd.lx.b(here, parts,
          buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)),
          gd.lx.s(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf,
          stack, hold), eg)), ec))

def gd.g.hold.on(
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.bare.hold.on(st, cc)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.tt(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, T.HChar{cc}), gd.l(L2.gd.tr(bad, rows,
        stack), L2.gd.lx(here, parts, buf, stack, hold), eg),
        gd.lx.mk(here, parts, buf, stack, T.HChar{cc}, gd.lx.h(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad,
          rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)), gd.lx.p(here, parts, buf, stack, hold,
          gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)), gd.lx.b(here, parts,
          buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)),
          gd.lx.s(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf,
          stack, hold), eg)), ec))

def gd.g.comnl(
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.com.nl(st, cc)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.tt(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, T.HChar{cc}), gd.l(L2.gd.tr(bad, rows,
        stack), L2.gd.lx(here, parts, buf, stack, hold), eg),
        gd.lx.mk(here, parts, buf, stack, T.HChar{cc}, gd.lx.h(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad,
          rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)), gd.lx.p(here, parts, buf, stack, hold,
          gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)), gd.lx.b(here, parts,
          buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)),
          gd.lx.s(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf,
          stack, hold), eg)), ec))

def gd.g.multi(
  +st: T.St,
  +kind: T.QKind,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.multi(st, kind)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      eg

def gd.g.mq(
  +st: T.St,
  +nn: U32,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.mq(st, nn)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      eg

def gd.g.mqshut(
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.mq.shut(st)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      eg

def gd.g.foldsaw(
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.fold.saw(st)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      eg

def gd.g.strfin(
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.str.fin(st)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.g.take(T.St{bad, rows, heads, here, parts, [], lex, back, qkind, stack, hold, uni, left, arrtab, lead},
        T.VStr{T.buf.str(buf)},
        gd.tt(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, [], stack, hold), gd.l(L2.gd.tr(bad, rows,
          stack), L2.gd.lx(here, parts, buf, stack, hold), eg),
          gd.lx.mk(here, parts, [], stack, hold, gd.lx.h(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows,
            stack), L2.gd.lx(here, parts, buf, stack, hold), eg)), gd.lx.p(here, parts, buf, stack, hold,
            gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)), {==}, gd.lx.s(here,
            parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold),
            eg)), gd.r(L2.gd.keys(stack), L2.gd.hold(hold), gd.lx.s1(here, parts, buf, stack, hold,
            gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg))))),
        gd.ifok.any(String.is_empty(bad), T.wf.text(T.buf.str(buf)), gd.bs.ok(buf, "", gd.lx.b(here, parts, buf, stack,
          hold, gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)), {==})))

# the quotes that did not close a multiline string are scalar values
def gd.mqput(
  one: Bool,
  kind: T.QKind,
  +buf: List<&2, Char>,
  +eb: {L2.gd.cs(buf) == True{} : Bool}
) -> {L2.gd.cs(T.mq.put(one, T.q.char(kind), buf)) == True{} : Bool}:
  match one:
    case True{}:
      match kind:
        case T.QBasic{}:
          eb
        case T.QLit{}:
          eb
        case T.QMulti{}:
          eb
        case T.QMultiLit{}:
          eb
    case False{}:
      match kind:
        case T.QBasic{}:
          eb
        case T.QLit{}:
          eb
        case T.QMulti{}:
          eb
        case T.QMultiLit{}:
          eb

def gd.g.mqback(
  +st: T.St,
  +cc: Char,
  +b2: List<&2, Char>,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool},
  +eb: {L2.gd.cs(b2) == True{} : Bool}
) -> {L2.good(T.lex.mq.back(st, cc, b2)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.tt(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, b2, stack, T.HChar{cc}), gd.l(L2.gd.tr(bad, rows,
        stack), L2.gd.lx(here, parts, buf, stack, hold), eg),
        gd.lx.mk(here, parts, b2, stack, T.HChar{cc}, gd.lx.h(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows,
          stack), L2.gd.lx(here, parts, buf, stack, hold), eg)), gd.lx.p(here, parts, buf, stack, hold,
          gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)), eb, gd.lx.s(here,
          parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold),
          eg)), ec))

def gd.g.mqmore(
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.mq.more(st, cc)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.tt(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, cc <> buf, stack, hold), gd.l(L2.gd.tr(bad, rows,
        stack), L2.gd.lx(here, parts, buf, stack, hold), eg),
        gd.lx.mk(here, parts, cc <> buf, stack, hold, gd.lx.h(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows,
          stack), L2.gd.lx(here, parts, buf, stack, hold), eg)), gd.lx.p(here, parts, buf, stack, hold,
          gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)), gd.tt(T.wf.char(cc),
          L2.gd.cs(buf), ec, gd.lx.b(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack),
          L2.gd.lx(here, parts, buf, stack, hold), eg))), gd.lx.s(here, parts, buf, stack, hold,
          gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)),
          gd.r(L2.gd.keys(stack), L2.gd.hold(hold), gd.lx.s1(here, parts, buf, stack, hold,
          gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)))))

def gd.g.array(
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.array(st)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.tt(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, [], [], T.CArr{[], parts, here} <> stack, hold),
        gd.l(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg),
        gd.lx.mk(here, [], [], T.CArr{[], parts, here} <> stack, hold, gd.lx.h(here, parts, buf, stack, hold,
          gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)), {==}, {==},
          gd.tt(L2.gd.segs(parts), Bool.and(L2.gd.segs(here), L2.gd.keys(stack)), gd.lx.p(here, parts, buf,
            stack, hold, gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)),
            gd.tt(L2.gd.segs(here), L2.gd.keys(stack), gd.lx.h(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad,
              rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)), gd.lx.s(here, parts, buf, stack, hold,
              gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)))),
          gd.r(L2.gd.keys(stack), L2.gd.hold(hold), gd.lx.s1(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad,
            rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)))))

def gd.g.inline(
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.inline(st)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.tt(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, [], [], T.CInl{[], parts, here} <> stack, hold),
        gd.l(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg),
        gd.lx.mk(here, [], [], T.CInl{[], parts, here} <> stack, hold, gd.lx.h(here, parts, buf, stack, hold,
          gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)), {==}, {==},
          gd.tt(L2.gd.segs(parts), Bool.and(L2.gd.segs(here), L2.gd.keys(stack)), gd.lx.p(here, parts, buf,
            stack, hold, gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)),
            gd.tt(L2.gd.segs(here), L2.gd.keys(stack), gd.lx.h(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad,
              rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)), gd.lx.s(here, parts, buf, stack, hold,
              gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)))),
          gd.r(L2.gd.keys(stack), L2.gd.hold(hold), gd.lx.s1(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad,
            rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)))))

def gd.g.kclear(
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.key.clear(st)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.tt(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, [], [], stack, hold), gd.l(L2.gd.tr(bad, rows, stack),
        L2.gd.lx(here, parts, buf, stack, hold), eg),
        gd.lx.mk(here, [], [], stack, hold, gd.lx.h(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack),
          L2.gd.lx(here, parts, buf, stack, hold), eg)), {==}, {==}, gd.lx.s(here, parts, buf, stack, hold,
          gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)),
          gd.r(L2.gd.keys(stack), L2.gd.hold(hold), gd.lx.s1(here, parts, buf, stack, hold,
          gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)))))

# a frame's value taken out of the rows' half
def gd.ifok.drop(
  ok: Bool,
  +aa: Bool,
  +bb: Bool,
  +cc: Bool,
  +ee: {L2.gd.ifok(ok, Bool.and(aa, Bool.and(bb, cc))) == True{} : Bool}
) -> {L2.gd.ifok(ok, Bool.and(aa, cc)) == True{} : Bool}:
  match ok:
    case True{}:
      gd.tt(aa, cc, gd.l(aa, Bool.and(bb, cc), ee), gd.r(bb, cc, gd.r(aa, Bool.and(bb, cc), ee)))
    case False{}:
      {==}

# the array's items, in order, are its value's
def gd.ifok.arr(
  ok: Bool,
  +rows: List<&2, T.Val>,
  +items: List<&2, T.Val>,
  +rest: List<&2, T.Ctx>,
  +ee: {L2.gd.ifok(ok, gd.ra(rows, items, rest)) == True{} : Bool}
) -> {L2.gd.ifok(ok, L2.gd.vok(T.VArr{List.reverse(&2, T.Val, items)})) == True{} : Bool}:
  match ok:
    case True{}:
      gd.rev.it(items, [], gd.l(T.wf.go(items, T.WfItems{}), L2.gd.vals(rest),
        gd.r(T.wf.go(rows, T.WfRows{""}), Bool.and(T.wf.go(items, T.WfItems{}), L2.gd.vals(rest)), ee)), {==})
    case False{}:
      {==}

# the inline table's rows, sealed, are its value's
def gd.ifok.inlv(
  ok: Bool,
  +rows: List<&2, T.Val>,
  +inl: List<&2, T.Val>,
  +rest: List<&2, T.Ctx>,
  +ee: {L2.gd.ifok(ok, gd.ri(rows, inl, rest)) == True{} : Bool}
) -> {L2.gd.ifok(ok, L2.gd.vok(T.VInl{T.inl.seal(inl)})) == True{} : Bool}:
  match ok:
    case True{}:
      gd.is(inl, "",
        gd.l(T.wf.go(inl, T.WfRows{""}), L2.gd.na(inl), gd.l(L2.gd.inl(inl), L2.gd.vals(rest),
          gd.r(T.wf.go(rows, T.WfRows{""}), Bool.and(L2.gd.inl(inl), L2.gd.vals(rest)), ee))),
        gd.r(T.wf.go(inl, T.WfRows{""}), L2.gd.na(inl), gd.l(L2.gd.inl(inl), L2.gd.vals(rest),
          gd.r(T.wf.go(rows, T.WfRows{""}), Bool.and(L2.gd.inl(inl), L2.gd.vals(rest)), ee))))
    case False{}:
      {==}

def gd.g.arrtop(
  stack: List<&2, T.Ctx>,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +lead: Bool,
  +et: {L2.gd.tr(bad, rows, stack) == True{} : Bool},
  +ek: {L2.gd.keys(stack) == True{} : Bool}
) -> {L2.good(T.arr.top(stack, bad, rows, heads, back, qkind, uni, left, arrtab, lead)) == True{} : Bool}:
  match stack:
    case []:
      gd.tt(L2.gd.tr(T.err.first(bad, "unclosed"), rows, []), True{},
        gd.off(String.is_empty(T.err.first(bad, "unclosed")), Bool.and(T.wf.go(rows, T.WfRows{""}), True{}),
          gd.err.ne2(bad, "unclosed", {==})), {==})
    case T.CArr{+x0, +p0, +h0} <> +rest:
      gd.g.take(T.St{bad, rows, heads, h0, p0, [], T.LTop{}, back, qkind, rest, T.HNone{}, uni, left, arrtab, lead},
        T.VArr{List.reverse(&2, T.Val, x0)},
        gd.tt(L2.gd.tr(bad, rows, rest), L2.gd.lx(h0, p0, [], rest, T.HNone{}),
          gd.ifok.drop(String.is_empty(bad), T.wf.go(rows, T.WfRows{""}), T.wf.go(x0, T.WfItems{}), L2.gd.vals(rest),
            et),
          gd.lx.mk(h0, p0, [], rest, T.HNone{}, gd.l(L2.gd.segs(h0), L2.gd.keys(rest), gd.r(L2.gd.segs(p0),
            Bool.and(L2.gd.segs(h0), L2.gd.keys(rest)), ek)),
            gd.l(L2.gd.segs(p0), Bool.and(L2.gd.segs(h0), L2.gd.keys(rest)), ek), {==},
            gd.r(L2.gd.segs(h0), L2.gd.keys(rest), gd.r(L2.gd.segs(p0), Bool.and(L2.gd.segs(h0),
              L2.gd.keys(rest)), ek)), {==})),
        gd.ifok.arr(String.is_empty(bad), rows, x0, rest, et))
    case T.CInl{+x0, +p0, +h0} <> +rest:
      gd.tt(L2.gd.tr(T.err.first(bad, "unclosed"), rows, []), True{},
        gd.off(String.is_empty(T.err.first(bad, "unclosed")), Bool.and(T.wf.go(rows, T.WfRows{""}), True{}),
          gd.err.ne2(bad, "unclosed", {==})), {==})

def gd.g.inltop(
  stack: List<&2, T.Ctx>,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +lead: Bool,
  +et: {L2.gd.tr(bad, rows, stack) == True{} : Bool},
  +ek: {L2.gd.keys(stack) == True{} : Bool}
) -> {L2.good(T.inl.top(stack, bad, rows, heads, back, qkind, uni, left, arrtab, lead)) == True{} : Bool}:
  match stack:
    case []:
      gd.tt(L2.gd.tr(T.err.first(bad, "unclosed"), rows, []), True{},
        gd.off(String.is_empty(T.err.first(bad, "unclosed")), Bool.and(T.wf.go(rows, T.WfRows{""}), True{}),
          gd.err.ne2(bad, "unclosed", {==})), {==})
    case T.CArr{+x0, +p0, +h0} <> +rest:
      gd.tt(L2.gd.tr(T.err.first(bad, "unclosed"), rows, []), True{},
        gd.off(String.is_empty(T.err.first(bad, "unclosed")), Bool.and(T.wf.go(rows, T.WfRows{""}), True{}),
          gd.err.ne2(bad, "unclosed", {==})), {==})
    case T.CInl{+x0, +p0, +h0} <> +rest:
      gd.g.take(T.St{bad, rows, heads, h0, p0, [], T.LTop{}, back, qkind, rest, T.HNone{}, uni, left, arrtab, lead},
        T.VInl{T.inl.seal(x0)},
        gd.tt(L2.gd.tr(bad, rows, rest), L2.gd.lx(h0, p0, [], rest, T.HNone{}),
          gd.ifok.drop(String.is_empty(bad), T.wf.go(rows, T.WfRows{""}), L2.gd.inl(x0), L2.gd.vals(rest), et),
          gd.lx.mk(h0, p0, [], rest, T.HNone{}, gd.l(L2.gd.segs(h0), L2.gd.keys(rest), gd.r(L2.gd.segs(p0),
            Bool.and(L2.gd.segs(h0), L2.gd.keys(rest)), ek)),
            gd.l(L2.gd.segs(p0), Bool.and(L2.gd.segs(h0), L2.gd.keys(rest)), ek), {==},
            gd.r(L2.gd.segs(h0), L2.gd.keys(rest), gd.r(L2.gd.segs(p0), Bool.and(L2.gd.segs(h0),
              L2.gd.keys(rest)), ek)), {==})),
        gd.ifok.inlv(String.is_empty(bad), rows, x0, rest, et))

def gd.g.arrclose(
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.arr.close(st)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.g.arrtop(stack, bad, rows, heads, back, qkind, uni, left, arrtab, lead, gd.l(L2.gd.tr(bad, rows, stack),
        L2.gd.lx(here, parts, buf, stack, hold), eg), gd.lx.s(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad,
        rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)))

def gd.g.inlclose(
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.inl.close(st)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.g.inltop(stack, bad, rows, heads, back, qkind, uni, left, arrtab, lead, gd.l(L2.gd.tr(bad, rows, stack),
        L2.gd.lx(here, parts, buf, stack, hold), eg), gd.lx.s(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad,
        rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)))

def gd.g.vnl3(
  inside: Bool,
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.val.nl3(inside, st)) == True{} : Bool}:
  match inside:
    case True{}:
      gd.g.err(st, "newline in inline table", {==}, eg)
    case False{}:
      gd.g.err(st, "newline before value", {==}, eg)

def gd.g.vnl2(
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.val.nl2(st, cc)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.g.vnl3(T.inl.open(stack), T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left,
        arrtab, lead}, eg)

def gd.g.vinl(
  inl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.val.inl(inl, st, cc)) == True{} : Bool}:
  match inl:
    case True{}:
      gd.g.inline(st, eg)
    case False{}:
      gd.g.push(st, cc, T.LBare{}, eg, ec)

def gd.g.vbr(
  br: Bool,
  inl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.val.br(br, inl, st, cc)) == True{} : Bool}:
  match br:
    case True{}:
      gd.g.array(st, eg)
    case False{}:
      gd.g.vinl(inl, st, cc, eg, ec)

def gd.g.vlit(
  lit: Bool,
  br: Bool,
  inl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.val.lit(lit, br, inl, st, cc)) == True{} : Bool}:
  match lit:
    case True{}:
      gd.g.qkey(st, T.QLit{}, T.LQ{}, eg)
    case False{}:
      gd.g.vbr(br, inl, st, cc, eg, ec)

def gd.g.vq(
  qq: Bool,
  lit: Bool,
  br: Bool,
  inl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.val.q(qq, lit, br, inl, st, cc)) == True{} : Bool}:
  match qq:
    case True{}:
      gd.g.qkey(st, T.QBasic{}, T.LQ{}, eg)
    case False{}:
      gd.g.vlit(lit, br, inl, st, cc, eg, ec)

def gd.g.vhash(
  hash: Bool,
  qq: Bool,
  lit: Bool,
  br: Bool,
  inl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.val.hash(hash, qq, lit, br, inl, st, cc)) == True{} : Bool}:
  match hash:
    case True{}:
      gd.g.com(st, T.LVal{}, eg)
    case False{}:
      gd.g.vq(qq, lit, br, inl, st, cc, eg, ec)

def gd.g.vnl(
  nl: Bool,
  hash: Bool,
  qq: Bool,
  lit: Bool,
  br: Bool,
  inl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.val.nl(nl, hash, qq, lit, br, inl, st, cc)) == True{} : Bool}:
  match nl:
    case True{}:
      gd.g.vnl2(st, cc, eg)
    case False{}:
      gd.g.vhash(hash, qq, lit, br, inl, st, cc, eg, ec)

def gd.g.vgo(
  sp: Bool,
  nl: Bool,
  hash: Bool,
  qq: Bool,
  lit: Bool,
  br: Bool,
  inl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.val.go(sp, nl, hash, qq, lit, br, inl, st, cc)) == True{} : Bool}:
  match sp:
    case True{}:
      eg
    case False{}:
      gd.g.vnl(nl, hash, qq, lit, br, inl, st, cc, eg, ec)

def gd.g.qgo(
  same: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.q.go(same, st, cc)) == True{} : Bool}:
  match same:
    case True{}:
      gd.g.lex(st, T.LQ2{}, eg)
    case False{}:
      gd.g.hold(T.st.lex(st, T.LStr{}), T.LStr{}, cc, gd.g.lex(st, T.LStr{}, eg), ec)

def gd.g.q(
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.q(st, cc)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.g.qgo(Char.is_eq(cc, T.q.char(qkind)), T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold,
        uni, left, arrtab, lead}, cc, eg, ec)

def gd.g.q2go(
  same: Bool,
  +st: T.St,
  +cc: Char,
  +kind: T.QKind,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool},
  +eo: {L2.gd.okv(st, T.VStr{""}) == True{} : Bool}
) -> {L2.good(T.lex.q2.go(same, st, cc, kind)) == True{} : Bool}:
  match same:
    case True{}:
      gd.g.multi(st, kind, eg)
    case False{}:
      gd.g.hold.on(T.val.take(st, T.VStr{""}), cc, gd.g.take(st, T.VStr{""}, eg, eo), ec)

def gd.g.q2(
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.q2(st, cc)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.g.q2go(Char.is_eq(cc, T.q.char(qkind)), T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack,
        hold, uni, left, arrtab, lead}, cc, qkind, eg, ec,
        gd.ifok.any(String.is_empty(bad), True{}, {==}))

def gd.g.schgo(
  bad: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.str.char.go(bad, st, cc)) == True{} : Bool}:
  match bad:
    case True{}:
      gd.g.err(st, "invalid control", {==}, eg)
    case False{}:
      gd.g.push(st, cc, T.LStr{}, eg, ec)

def gd.g.sch(
  +multi: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.str.char(multi, st, cc)) == True{} : Bool}:
  gd.g.schgo(T.str.bad(Char.to_u32(cc), multi), st, cc, eg, ec)

def gd.g.sbs(
  bs: Bool,
  +multi: Bool,
  +st: T.St,
  +cc: Char,
  +kind: T.QKind,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.str.bs(bs, multi, st, cc, kind)) == True{} : Bool}:
  match bs:
    case True{}:
      gd.g.lex(st, T.LEsc{}, eg)
    case False{}:
      gd.g.sch(multi, st, cc, eg, ec)

def gd.g.sesc(
  basic: Bool,
  +multi: Bool,
  +st: T.St,
  +cc: Char,
  +kind: T.QKind,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.str.esc(basic, multi, st, cc, kind)) == True{} : Bool}:
  match basic:
    case True{}:
      gd.g.sbs(Char.is_eq(cc, '\\'), multi, st, cc, kind, eg, ec)
    case False{}:
      gd.g.sch(multi, st, cc, eg, ec)

def gd.g.squote(
  multi: Bool,
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.str.quote(multi, st)) == True{} : Bool}:
  match multi:
    case False{}:
      gd.g.strfin(st, eg)
    case True{}:
      gd.g.mq(st, 1, eg)

def gd.g.sgo(
  quote: Bool,
  +multi: Bool,
  +basic: Bool,
  +st: T.St,
  +cc: Char,
  +kind: T.QKind,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.str.go(quote, multi, basic, st, cc, kind)) == True{} : Bool}:
  match quote:
    case True{}:
      gd.g.squote(multi, st, eg)
    case False{}:
      gd.g.sesc(basic, multi, st, cc, kind, eg, ec)

def gd.g.str(
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.str(st, cc)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.g.sgo(Char.is_eq(cc, T.q.char(qkind)), T.q.multi(qkind), T.q.basic(qkind),
        T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead}, cc, qkind,
          eg, ec)

def gd.g.fendgo(
  saw: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.fold.end.go(saw, st, cc)) == True{} : Bool}:
  match saw:
    case True{}:
      gd.g.hold(T.st.lex(st, T.LStr{}), T.LStr{}, cc, gd.g.lex(st, T.LStr{}, eg), ec)
    case False{}:
      gd.g.err(st, "invalid escape", {==}, eg)

def gd.g.fend(
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.fold.end(st, cc)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.g.fendgo(U32.is_eq(left, 1), T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni,
        left, arrtab, lead}, cc, eg, ec)

def gd.g.fnl(
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.fold.nl(nl, st, cc)) == True{} : Bool}:
  match nl:
    case True{}:
      gd.g.foldsaw(st, eg)
    case False{}:
      gd.g.fend(st, cc, eg, ec)

def gd.g.fgo(
  sp: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.fold.go(sp, nl, st, cc)) == True{} : Bool}:
  match sp:
    case True{}:
      eg
    case False{}:
      gd.g.fnl(nl, st, cc, eg, ec)

def gd.g.mqone(
  one: Bool,
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.mq.one(one, st)) == True{} : Bool}:
  match one:
    case True{}:
      gd.g.mq(st, 2, eg)
    case False{}:
      gd.g.mqshut(st, eg)

def gd.g.mqgo(
  quote: Bool,
  +one: Bool,
  +st: T.St,
  +cc: Char,
  +buf: List<&2, Char>,
  +kind: T.QKind,
  +left: U32,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool},
  +eb: {L2.gd.cs(buf) == True{} : Bool}
) -> {L2.good(T.lex.mq.go(quote, one, st, cc, buf, kind, left)) == True{} : Bool}:
  match quote:
    case True{}:
      gd.g.mqone(one, st, eg)
    case False{}:
      gd.g.mqback(st, cc, T.mq.put(one, T.q.char(kind), buf), eg, ec, gd.mqput(one, kind, buf, eb))

def gd.g.mqstep(
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.mq.step(st, cc)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.g.mqgo(Char.is_eq(cc, T.q.char(qkind)), U32.is_eq(left, 1), T.St{bad, rows, heads, here, parts, buf, lex,
        back, qkind, stack, hold, uni, left, arrtab, lead}, cc, buf, qkind, left, eg, ec,
        gd.lx.b(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack,
          hold), eg)))

def gd.g.mqfin(
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.mq.fin(st, cc)) == True{} : Bool}:
  gd.g.hold.on(T.str.fin(st), cc, gd.g.strfin(st, eg), ec)

def gd.g.mqroom(
  room: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.mq.room(room, st, cc)) == True{} : Bool}:
  match room:
    case True{}:
      gd.g.mqmore(st, cc, eg, ec)
    case False{}:
      gd.g.mqfin(st, cc, eg, ec)

def gd.g.mqendgo(
  quote: Bool,
  +room: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.mq.end.go(quote, room, st, cc)) == True{} : Bool}:
  match quote:
    case True{}:
      gd.g.mqroom(room, st, cc, eg, ec)
    case False{}:
      gd.g.mqfin(st, cc, eg, ec)

def gd.g.mqend(
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.mq.end(st, cc)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.g.mqendgo(Char.is_eq(cc, T.q.char(qkind)), U32.is_lt(left, 2), T.St{bad, rows, heads, here, parts, buf, lex,
        back, qkind, stack, hold, uni, left, arrtab, lead}, cc, eg, ec)

def gd.g.tnl2(
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.trim.nl(nl, st, cc)) == True{} : Bool}:
  match nl:
    case True{}:
      gd.g.lex(st, T.LStr{}, eg)
    case False{}:
      gd.g.hold(T.st.lex(st, T.LStr{}), T.LStr{}, cc, gd.g.lex(st, T.LStr{}, eg), ec)

def gd.g.trimgo(
  cr: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.trim.go(cr, nl, st, cc)) == True{} : Bool}:
  match cr:
    case True{}:
      gd.g.lex(st, T.LTrim2{}, eg)
    case False{}:
      gd.g.tnl2(nl, st, cc, eg, ec)

def gd.g.trim2go(
  lf: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.trim2.go(lf, st, cc)) == True{} : Bool}:
  match lf:
    case True{}:
      gd.g.lex(st, T.LStr{}, eg)
    case False{}:
      gd.g.hold(T.st.lex(st, T.LStr{}), T.LStr{}, cc, gd.g.lex(st, T.LStr{}, eg), ec)

def gd.g.ctab(
  tab: Bool,
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.com.tab(tab, st)) == True{} : Bool}:
  match tab:
    case True{}:
      eg
    case False{}:
      gd.g.err(st, "invalid control in comment", {==}, eg)

def gd.g.cctl(
  ctl: Bool,
  tab: Bool,
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.com.ctl(ctl, tab, st)) == True{} : Bool}:
  match ctl:
    case False{}:
      eg
    case True{}:
      gd.g.ctab(tab, st, eg)

def gd.g.cgo(
  nl: Bool,
  ctl: Bool,
  tab: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.com.go(nl, ctl, tab, st, cc)) == True{} : Bool}:
  match nl:
    case False{}:
      gd.g.cctl(ctl, tab, st, eg)
    case True{}:
      gd.g.comnl(st, cc, eg, ec)

def gd.g.aend(
  end: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.arr.end(end, st, cc)) == True{} : Bool}:
  match end:
    case True{}:
      gd.g.arrclose(st, eg)
    case False{}:
      gd.g.hold(T.st.lex(st, T.LVal{}), T.LVal{}, cc, gd.g.lex(st, T.LVal{}, eg), ec)

def gd.g.aahash(
  hash: Bool,
  end: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.arr.hash(hash, end, st, cc)) == True{} : Bool}:
  match hash:
    case True{}:
      gd.g.com(st, T.LArr{}, eg)
    case False{}:
      gd.g.aend(end, st, cc, eg, ec)

def gd.g.aanl(
  nl: Bool,
  hash: Bool,
  end: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.arr.nl(nl, hash, end, st, cc)) == True{} : Bool}:
  match nl:
    case True{}:
      eg
    case False{}:
      gd.g.aahash(hash, end, st, cc, eg, ec)

def gd.g.aago(
  sp: Bool,
  nl: Bool,
  hash: Bool,
  end: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.arr.go(sp, nl, hash, end, st, cc)) == True{} : Bool}:
  match sp:
    case True{}:
      eg
    case False{}:
      gd.g.aanl(nl, hash, end, st, cc, eg, ec)

def gd.g.acend(
  end: Bool,
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.arrc.end(end, st)) == True{} : Bool}:
  match end:
    case True{}:
      gd.g.arrclose(st, eg)
    case False{}:
      gd.g.err(st, "invalid array", {==}, eg)

def gd.g.accomma(
  comma: Bool,
  end: Bool,
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.arrc.comma(comma, end, st)) == True{} : Bool}:
  match comma:
    case True{}:
      gd.g.lex(st, T.LArr{}, eg)
    case False{}:
      gd.g.acend(end, st, eg)

def gd.g.achash(
  hash: Bool,
  comma: Bool,
  end: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.arrc.hash(hash, comma, end, st, cc)) == True{} : Bool}:
  match hash:
    case True{}:
      gd.g.com(st, T.LArrC{}, eg)
    case False{}:
      gd.g.accomma(comma, end, st, eg)

def gd.g.acnl(
  nl: Bool,
  hash: Bool,
  comma: Bool,
  end: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.arrc.nl(nl, hash, comma, end, st, cc)) == True{} : Bool}:
  match nl:
    case True{}:
      eg
    case False{}:
      gd.g.achash(hash, comma, end, st, cc, eg)

def gd.g.acgo(
  sp: Bool,
  nl: Bool,
  hash: Bool,
  comma: Bool,
  end: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.arrc.go(sp, nl, hash, comma, end, st, cc)) == True{} : Bool}:
  match sp:
    case True{}:
      eg
    case False{}:
      gd.g.acnl(nl, hash, comma, end, st, cc, eg)

def gd.g.kbare(
  ok: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.key.bare(ok, st, cc)) == True{} : Bool}:
  match ok:
    case True{}:
      gd.g.push(st, cc, T.LKey{}, eg, ec)
    case False{}:
      gd.g.err(st, "invalid key", {==}, eg)

def gd.g.klit(
  lit: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.key.lit(lit, st, cc)) == True{} : Bool}:
  match lit:
    case True{}:
      gd.g.qkey(st, T.QLit{}, T.LKeyQ{}, eg)
    case False{}:
      gd.g.kbare(T.bare.at(cc), st, cc, eg, ec)

def gd.g.kq0(
  qq: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.key.q(qq, st, cc)) == True{} : Bool}:
  match qq:
    case True{}:
      gd.g.qkey(st, T.QBasic{}, T.LKeyQ{}, eg)
    case False{}:
      gd.g.klit(Char.is_eq(cc, '\''), st, cc, eg, ec)

def gd.g.kstart(
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.key.start(st, cc)) == True{} : Bool}:
  gd.g.kq0(Char.is_eq(cc, '"'), T.lex.key.clear(st), cc, gd.g.kclear(st, eg), ec)

def gd.g.inlnl(
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.inl.nl(nl, st, cc)) == True{} : Bool}:
  match nl:
    case True{}:
      gd.g.err(st, "newline in inline table", {==}, eg)
    case False{}:
      gd.g.kstart(st, cc, eg, ec)

def gd.g.inlend(
  end: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.inl.end(end, nl, st, cc)) == True{} : Bool}:
  match end:
    case True{}:
      gd.g.inlclose(st, eg)
    case False{}:
      gd.g.inlnl(nl, st, cc, eg, ec)

def gd.g.inlhash(
  hash: Bool,
  end: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.inl.hash(hash, end, nl, st, cc)) == True{} : Bool}:
  match hash:
    case True{}:
      gd.g.com(st, T.LInl{}, eg)
    case False{}:
      gd.g.inlend(end, nl, st, cc, eg, ec)

def gd.g.inlgo(
  sp: Bool,
  hash: Bool,
  end: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.inl.go(sp, hash, end, nl, st, cc)) == True{} : Bool}:
  match sp:
    case True{}:
      eg
    case False{}:
      gd.g.inlhash(hash, end, nl, st, cc, eg, ec)

def gd.g.ikhash(
  hash: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.inlk.hash(hash, nl, st, cc)) == True{} : Bool}:
  match hash:
    case True{}:
      gd.g.com(st, T.LInlK{}, eg)
    case False{}:
      gd.g.inlnl(nl, st, cc, eg, ec)

def gd.g.ikgo(
  sp: Bool,
  hash: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.inlk.go(sp, hash, nl, st, cc)) == True{} : Bool}:
  match sp:
    case True{}:
      eg
    case False{}:
      gd.g.ikhash(hash, nl, st, cc, eg, ec)

def gd.g.icnl(
  nl: Bool,
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.inlc.nl(nl, st)) == True{} : Bool}:
  match nl:
    case True{}:
      gd.g.err(st, "newline in inline table", {==}, eg)
    case False{}:
      gd.g.err(st, "invalid inline table", {==}, eg)

def gd.g.icend(
  end: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.inlc.end(end, nl, st, cc)) == True{} : Bool}:
  match end:
    case True{}:
      gd.g.inlclose(st, eg)
    case False{}:
      gd.g.icnl(nl, st, eg)

def gd.g.iccomma(
  comma: Bool,
  end: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.inlc.comma(comma, end, nl, st, cc)) == True{} : Bool}:
  match comma:
    case True{}:
      gd.g.lex(st, T.LInlK{}, eg)
    case False{}:
      gd.g.icend(end, nl, st, cc, eg)

def gd.g.ichash(
  hash: Bool,
  comma: Bool,
  end: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.inlc.hash(hash, comma, end, nl, st, cc)) == True{} : Bool}:
  match hash:
    case True{}:
      gd.g.com(st, T.LInlC{}, eg)
    case False{}:
      gd.g.iccomma(comma, end, nl, st, cc, eg)

def gd.g.icgo(
  sp: Bool,
  hash: Bool,
  comma: Bool,
  end: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.lex.inlc.go(sp, hash, comma, end, nl, st, cc)) == True{} : Bool}:
  match sp:
    case True{}:
      eg
    case False{}:
      gd.g.ichash(hash, comma, end, nl, st, cc, eg)

def L2.gd_value_steps(lex, hl, st, eg, cc, ec):
  match lex:
    case T.LTop{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LTop{}, st, cc)) == True{} : Bool}, hl)
    case T.LLine{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LLine{}, st, cc)) == True{} : Bool}, hl)
    case T.LKey{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LKey{}, st, cc)) == True{} : Bool}, hl)
    case T.LKeyDot{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LKeyDot{}, st, cc)) == True{} : Bool}, hl)
    case T.LAfter{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LAfter{}, st, cc)) == True{} : Bool}, hl)
    case T.LKeyQ{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LKeyQ{}, st, cc)) == True{} : Bool}, hl)
    case T.LKeyE{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LKeyE{}, st, cc)) == True{} : Bool}, hl)
    case T.LKeyU{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LKeyU{}, st, cc)) == True{} : Bool}, hl)
    case T.LVal{}:
      gd.g.vgo(T.ch.sp(cc), T.ch.nl(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, '"'), Char.is_eq(cc, '\''),
        Char.is_eq(cc, '['), Char.is_eq(cc, '{'), st, cc, eg, ec)
    case T.LQ{}:
      gd.g.q(st, cc, eg, ec)
    case T.LQ2{}:
      gd.g.q2(st, cc, eg, ec)
    case T.LStr{}:
      gd.g.str(st, cc, eg, ec)
    case T.LEsc{}:
      gd.g.esc(T.esc.of(cc), st, T.LStr{}, eg, gd.e.of(cc))
    case T.LUni{}:
      gd.g.uni(st, cc, T.LStr{}, eg)
    case T.LFold{}:
      gd.g.fgo(T.ch.sp(cc), T.ch.nl(cc), st, cc, eg, ec)
    case T.LMq{}:
      gd.g.mqstep(st, cc, eg, ec)
    case T.LMqEnd{}:
      gd.g.mqend(st, cc, eg, ec)
    case T.LTrim{}:
      gd.g.trimgo(U32.is_eq(Char.to_u32(cc), 13), T.ch.nl(cc), st, cc, eg, ec)
    case T.LTrim2{}:
      gd.g.trim2go(U32.is_eq(Char.to_u32(cc), 10), st, cc, eg, ec)
    case T.LBare{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LBare{}, st, cc)) == True{} : Bool}, hl)
    case T.LDate{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LDate{}, st, cc)) == True{} : Bool}, hl)
    case T.LCom{}:
      gd.g.cgo(T.ch.nl(cc), T.ch.ctl(cc), U32.is_eq(Char.to_u32(cc), 9), st, cc, eg, ec)
    case T.LHead{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LHead{}, st, cc)) == True{} : Bool}, hl)
    case T.LHeadGap{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LHeadGap{}, st, cc)) == True{} : Bool}, hl)
    case T.LHeadDot{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LHeadDot{}, st, cc)) == True{} : Bool}, hl)
    case T.LHeadQ{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LHeadQ{}, st, cc)) == True{} : Bool}, hl)
    case T.LHeadE{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LHeadE{}, st, cc)) == True{} : Bool}, hl)
    case T.LHeadU{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LHeadU{}, st, cc)) == True{} : Bool}, hl)
    case T.LHeadR{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LHeadR{}, st, cc)) == True{} : Bool}, hl)
    case T.LArr{}:
      gd.g.aago(T.ch.sp(cc), T.ch.nl(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, ']'), st, cc, eg, ec)
    case T.LArrC{}:
      gd.g.acgo(T.ch.sp(cc), T.ch.nl(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, ','), Char.is_eq(cc, ']'), st, cc,
        eg)
    case T.LInl{}:
      gd.g.inlgo(T.ch.sp(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, '}'), T.ch.nl(cc), st, cc, eg, ec)
    case T.LInlK{}:
      gd.g.ikgo(T.ch.sp(cc), Char.is_eq(cc, '#'), T.ch.nl(cc), st, cc, eg, ec)
    case T.LInlC{}:
      gd.g.icgo(T.ch.sp(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, ','), Char.is_eq(cc, '}'), T.ch.nl(cc), st, cc,
        eg)
    case T.LSink{}:
      eg

# WP-R3: a bare word's value is well-formed. word.val reads a special word, a
# datetime or a numeral; each of them builds only well-formed values, which is
# what gd_take asks of a bare word's value. Datetimes first: the scan checks
# every field's range as wf.when does, except the year, which is four digits
# and so below ten thousand.

# what a datetime scan gives is well-formed when it gives a datetime
def gd.wot(ww: T.WhenOut) -> Bool:
  match ww:
    case T.WSome{w}:
      T.wf.when(w)
    case _:
      True{}

# a take of digits below a bound, when it took them
def gd.dk(dd: T.Dig, +kk: U32) -> Bool:
  match dd:
    case T.DigOk{nn, _cs}:
      U32.is_lt(nn, kk)
    case T.DigBad{}:
      True{}

# below a bound that a sum starts below
def gd.n.lt.addl(
  aa: Nat,
  bb: Nat,
  cc: Nat,
  +hh: {Nat.is_lt(Nat.add(aa, bb), cc) == True{} : Bool}
) -> {Nat.is_lt(aa, cc) == True{} : Bool}:
  match aa cc:
    case 0n 0n:
      Eq.bit.absurd(&2, {Nat.is_lt(0n, 0n) == True{} : Bool},
        Equal.trans(Bool, False{}, Nat.is_lt(bb, 0n), True{}, Equal.sym(Bool, Nat.is_lt(bb, 0n), False{},
          M2.nlt.zero(bb)), hh))
    case 0n 1n+_c:
      {==}
    case 1n+a1 0n:
      Eq.bit.absurd(&2, {Nat.is_lt(1n+a1, 0n) == True{} : Bool}, hh)
    case 1n+a1 1n+c1:
      gd.n.lt.addl(a1, bb, c1, hh)

# ten times a U32 below k plus a digit is below ten times k, when ten times k
# does not overflow
def gd.u.step(
  +uu: Unit,
  +nn: U32,
  +dd: U32,
  +kk: U32,
  en: {U32.is_lt(nn, kk) == True{} : Bool},
  ed: {U32.is_lt(dd, 10) == True{} : Bool},
  hk: {Ar.umk(kk) == 0n : Nat}
) -> {U32.is_lt(U32.add(U32.mul(nn, 10), dd), U32.mul(kk, 10)) == True{} : Bool}:
  Equal.trans(Bool, U32.is_lt(U32.add(U32.mul(nn, 10), dd), U32.mul(kk, 10)),
    Nat.is_lt(U32.to_nat(U32.add(U32.mul(nn, 10), dd)), U32.to_nat(U32.mul(kk, 10))), True{},
    M2.u.lt(U32.add(U32.mul(nn, 10), dd), U32.mul(kk, 10)),
    Equal.trans(Bool, Nat.is_lt(U32.to_nat(U32.add(U32.mul(nn, 10), dd)), U32.to_nat(U32.mul(kk, 10))),
      Nat.is_lt(U32.to_nat(U32.add(U32.mul(nn, 10), dd)), Nat.mul(U32.to_nat(kk), 10n)), True{},
      Equal.cong(Nat, Bool, xx => Nat.is_lt(U32.to_nat(U32.add(U32.mul(nn, 10), dd)), xx),
        U32.to_nat(U32.mul(kk, 10)), Nat.mul(U32.to_nat(kk), 10n),
        Equal.trans(Nat, U32.to_nat(U32.mul(kk, 10)), Nat.add(U32.to_nat(U32.mul(kk, 10)), 0n),
          Nat.mul(U32.to_nat(kk), 10n),
          Equal.sym(Nat, Nat.add(U32.to_nat(U32.mul(kk, 10)), 0n), U32.to_nat(U32.mul(kk, 10)),
            Ar.nat_add_zero(U32.to_nat(U32.mul(kk, 10)))),
          Equal.trans(Nat, Nat.add(U32.to_nat(U32.mul(kk, 10)), 0n),
            Nat.add(U32.to_nat(U32.mul(kk, 10)), Nat.mul(Ar.umk(kk), Ar.pow2u(32n, uu))),
            Nat.mul(U32.to_nat(kk), 10n),
            Equal.cong(Nat, Nat, zz => Nat.add(U32.to_nat(U32.mul(kk, 10)), Nat.mul(zz, Ar.pow2u(32n, uu))), 0n,
              Ar.umk(kk), Equal.sym(Nat, Ar.umk(kk), 0n, hk)),
            Ar.u_mul10(uu, kk)))),
      gd.n.lt.addl(U32.to_nat(U32.add(U32.mul(nn, 10), dd)), Nat.mul(Ar.step_ks(nn, dd), Ar.pow2u(32n, uu)),
        Nat.mul(U32.to_nat(kk), 10n),
        Equal.trans(Bool,
          Nat.is_lt(Nat.add(U32.to_nat(U32.add(U32.mul(nn, 10), dd)), Nat.mul(Ar.step_ks(nn, dd),
            Ar.pow2u(32n, uu))), Nat.mul(U32.to_nat(kk), 10n)),
          Nat.is_lt(Nat.add(Nat.mul(U32.to_nat(nn), 10n), U32.to_nat(dd)), Nat.mul(U32.to_nat(kk), 10n)), True{},
          Equal.cong(Nat, Bool, xx => Nat.is_lt(xx, Nat.mul(U32.to_nat(kk), 10n)),
            Nat.add(U32.to_nat(U32.add(U32.mul(nn, 10), dd)), Nat.mul(Ar.step_ks(nn, dd), Ar.pow2u(32n, uu))),
            Nat.add(Nat.mul(U32.to_nat(nn), 10n), U32.to_nat(dd)), Ar.step_k(uu, nn, dd)),
          Equal.trans(Bool, Nat.is_lt(Nat.add(Nat.mul(U32.to_nat(nn), 10n), U32.to_nat(dd)),
            Nat.mul(U32.to_nat(kk), 10n)), Nat.is_lt(U32.to_nat(nn), U32.to_nat(kk)), True{},
            M2.ltm(U32.to_nat(nn), U32.to_nat(kk), U32.to_nat(dd),
              Equal.trans(Bool, Nat.is_lt(U32.to_nat(dd), 10n), U32.is_lt(dd, 10), True{},
                Equal.sym(Bool, U32.is_lt(dd, 10), Nat.is_lt(U32.to_nat(dd), U32.to_nat(10)), M2.u.lt(dd, 10)), ed)),
            Equal.trans(Bool, Nat.is_lt(U32.to_nat(nn), U32.to_nat(kk)), U32.is_lt(nn, kk), True{},
              Equal.sym(Bool, U32.is_lt(nn, kk), Nat.is_lt(U32.to_nat(nn), U32.to_nat(kk)), M2.u.lt(nn, kk)), en))))))

# a digit character's code less 48 is below ten
def gd.dg.sub(
  +cc: Char,
  ed: {Char.is_digit(cc) == True{} : Bool}
) -> {U32.is_lt(U32.sub(Char.to_u32(cc), 48), 10) == True{} : Bool}:
  M4.dg.elim(xx => {U32.is_lt(U32.sub(Char.to_u32(xx), 48), 10) == True{} : Bool}, cc, ed,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# and so is its digit value
def gd.dg.val(+cc: Char, ed: {Char.is_digit(cc) == True{} : Bool}) -> {U32.is_lt(T.dig.val(cc), 10) == True{} : Bool}:
  M4.dg.elim(xx => {U32.is_lt(T.dig.val(xx), 10) == True{} : Bool}, cc, ed,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# one character of a take: a digit keeps the count below ten times the bound
def gd.tk.accd(
  digit: Bool,
  +nn: U32,
  +cc: Char,
  +kk: U32,
  ed: {Char.is_digit(cc) == digit : Bool},
  +en: {U32.is_lt(nn, kk) == True{} : Bool},
  +hk: {Ar.umk(kk) == 0n : Nat}
) -> {L2.gd.ifok(digit, U32.is_lt(T.take.acc.d(digit, nn, cc), U32.mul(kk, 10))) == True{} : Bool}:
  match digit:
    case True{}:
      gd.u.step(Unit{}, nn, U32.sub(Char.to_u32(cc), 48), kk, en, gd.dg.sub(cc, ed), hk)
    case False{}:
      {==}

# one character of a take, while the take is well
def gd.tk.acc(
  ok: Bool,
  +nn: U32,
  +cc: Char,
  +kk: U32,
  +en: {L2.gd.ifok(ok, U32.is_lt(nn, kk)) == True{} : Bool},
  +hk: {Ar.umk(kk) == 0n : Nat}
) -> {L2.gd.ifok(T.take.ok(ok, cc), U32.is_lt(T.take.acc(ok, nn, cc), U32.mul(kk, 10))) == True{} : Bool}:
  match ok:
    case True{}:
      gd.tk.accd(Char.is_digit(cc), nn, cc, kk, {==}, en, hk)
    case False{}:
      {==}

# the end of a take
def gd.tk.fin(
  ok: Bool,
  +nn: U32,
  +cs: List<&2, Char>,
  +kk: U32,
  +en: {L2.gd.ifok(ok, U32.is_lt(nn, kk)) == True{} : Bool}
) -> {gd.dk(T.take.fin(ok, nn, cs), kk) == True{} : Bool}:
  match ok:
    case True{}:
      en
    case False{}:
      {==}

# a take of one digit onto a count below k is below ten times k
def gd.tk1(
  cs: List<&2, Char>,
  +nn: U32,
  +ok: Bool,
  +kk: U32,
  +en: {L2.gd.ifok(ok, U32.is_lt(nn, kk)) == True{} : Bool},
  +hk: {Ar.umk(kk) == 0n : Nat}
) -> {gd.dk(T.take.n(1n, cs, nn, ok), U32.mul(kk, 10)) == True{} : Bool}:
  match cs:
    case []:
      {==}
    case +hh <> +tt:
      gd.tk.fin(T.take.ok(ok, hh), T.take.acc(ok, nn, hh), tt, U32.mul(kk, 10), gd.tk.acc(ok, nn, hh, kk, en, hk))

# a take of two digits from zero is below one hundred
def gd.tk2(cs: List<&2, Char>) -> {gd.dk(T.take.n(2n, cs, 0, True{}), 100) == True{} : Bool}:
  match cs:
    case []:
      {==}
    case +hh <> +tt:
      gd.tk1(tt, T.take.acc(True{}, 0, hh), T.take.ok(True{}, hh), 10, gd.tk.acc(True{}, 0, hh, 1, {==}, {==}), {==})

# the upper half of a range check
def gd.rng.hi(
  +nn: U32,
  +lo: U32,
  +hi: U32,
  +ee: {T.bound.rng(nn, lo, hi) == True{} : Bool}
) -> {U32.is_le(nn, hi) == True{} : Bool}:
  gd.r(U32.is_ge(nn, lo), U32.is_le(nn, hi), ee)

# a zone Z after a date and a clock
def gd.wz.z(
  tt: List<&2, Char>,
  +clock: T.Clock,
  +date: T.Date,
  +ed: {T.wf.date(date) == True{} : Bool},
  +ec: {T.wf.clock(clock) == True{} : Bool}
) -> {gd.wot(T.when.zone.z(tt, clock, date)) == True{} : Bool}:
  match tt:
    case []:
      gd.tt(T.wf.date(date), Bool.and(T.wf.clock(clock), True{}), ed, gd.tt(T.wf.clock(clock), True{}, ec, {==}))
    case _h <> _t:
      {==}

# a numeric offset whose minute is in range
def gd.wz.ok2(
  mi_ok: Bool,
  +sign: T.Sign,
  +hh: U32,
  +mi: U32,
  +clock: T.Clock,
  +date: T.Date,
  +ed: {T.wf.date(date) == True{} : Bool},
  +ec: {T.wf.clock(clock) == True{} : Bool},
  +eh: {U32.is_le(hh, 23) == True{} : Bool},
  +em: {T.bound.rng(mi, 0, 59) == mi_ok : Bool}
) -> {gd.wot(T.when.zone.mm.ok2(mi_ok, sign, hh, mi, clock, date)) == True{} : Bool}:
  match mi_ok:
    case False{}:
      {==}
    case True{}:
      gd.tt(T.wf.date(date), Bool.and(T.wf.clock(clock), Bool.and(U32.is_le(hh, 23), U32.is_le(mi, 59))), ed,
        gd.tt(T.wf.clock(clock), Bool.and(U32.is_le(hh, 23), U32.is_le(mi, 59)), ec,
          gd.tt(U32.is_le(hh, 23), U32.is_le(mi, 59), eh, gd.rng.hi(mi, 0, 59, em))))

# and whose hour is
def gd.wz.ok(
  h_ok: Bool,
  +mi_ok: Bool,
  +sign: T.Sign,
  +hh: U32,
  +mi: U32,
  +clock: T.Clock,
  +date: T.Date,
  +ed: {T.wf.date(date) == True{} : Bool},
  +ec: {T.wf.clock(clock) == True{} : Bool},
  +eh: {T.bound.rng(hh, 0, 23) == h_ok : Bool},
  +em: {T.bound.rng(mi, 0, 59) == mi_ok : Bool}
) -> {gd.wot(T.when.zone.mm.ok(h_ok, mi_ok, sign, hh, mi, clock, date)) == True{} : Bool}:
  match h_ok:
    case False{}:
      {==}
    case True{}:
      gd.wz.ok2(mi_ok, sign, hh, mi, clock, date, ed, ec, gd.rng.hi(hh, 0, 23, eh), em)

# nothing after an offset
def gd.wz.end(
  cs: List<&2, Char>,
  +h_ok: Bool,
  +mi_ok: Bool,
  +sign: T.Sign,
  +hh: U32,
  +mi: U32,
  +clock: T.Clock,
  +date: T.Date,
  +ed: {T.wf.date(date) == True{} : Bool},
  +ec: {T.wf.clock(clock) == True{} : Bool},
  +eh: {T.bound.rng(hh, 0, 23) == h_ok : Bool},
  +em: {T.bound.rng(mi, 0, 59) == mi_ok : Bool}
) -> {gd.wot(T.when.zone.mm.end(cs, h_ok, mi_ok, sign, hh, mi, clock, date)) == True{} : Bool}:
  match cs:
    case []:
      gd.wz.ok(h_ok, mi_ok, sign, hh, mi, clock, date, ed, ec, eh, em)
    case _h <> _t:
      {==}

# the offset minute
def gd.wz.mmgo(
  dd: T.Dig,
  +sign: T.Sign,
  +hh: U32,
  +clock: T.Clock,
  +date: T.Date,
  +ed: {T.wf.date(date) == True{} : Bool},
  +ec: {T.wf.clock(clock) == True{} : Bool}
) -> {gd.wot(T.when.zone.mm.go(dd, sign, hh, clock, date)) == True{} : Bool}:
  match dd:
    case T.DigBad{}:
      {==}
    case T.DigOk{+nn, +cs}:
      gd.wz.end(cs, T.bound.rng(hh, 0, 23), T.bound.rng(nn, 0, 59), sign, hh, nn, clock, date, ed, ec, {==}, {==})

# the offset minute, after a colon
def gd.wz.mm(
  hit: Bool,
  +dd: T.Dig,
  +sign: T.Sign,
  +hh: U32,
  +clock: T.Clock,
  +date: T.Date,
  +ed: {T.wf.date(date) == True{} : Bool},
  +ec: {T.wf.clock(clock) == True{} : Bool}
) -> {gd.wot(T.when.zone.mm(hit, dd, sign, hh, clock, date)) == True{} : Bool}:
  match hit:
    case False{}:
      {==}
    case True{}:
      gd.wz.mmgo(dd, sign, hh, clock, date, ed, ec)

# the colon of an offset
def gd.wz.colon(
  cs: List<&2, Char>,
  +sign: T.Sign,
  +hh: U32,
  +clock: T.Clock,
  +date: T.Date,
  +ed: {T.wf.date(date) == True{} : Bool},
  +ec: {T.wf.clock(clock) == True{} : Bool}
) -> {gd.wot(T.when.zone.hh.colon(cs, sign, hh, clock, date)) == True{} : Bool}:
  match cs:
    case []:
      {==}
    case +cc <> +tt:
      gd.wz.mm(Char.is_eq(cc, ':'), T.take.n(2n, tt, 0, True{}), sign, hh, clock, date, ed, ec)

# the offset hour
def gd.wz.hh(
  dd: T.Dig,
  +sign: T.Sign,
  +clock: T.Clock,
  +date: T.Date,
  +ed: {T.wf.date(date) == True{} : Bool},
  +ec: {T.wf.clock(clock) == True{} : Bool}
) -> {gd.wot(T.when.zone.hh(dd, sign, clock, date)) == True{} : Bool}:
  match dd:
    case T.DigBad{}:
      {==}
    case T.DigOk{+nn, +cs}:
      gd.wz.colon(cs, sign, nn, clock, date, ed, ec)

# a minus offset
def gd.wz.minus(
  minus: Bool,
  +tt: List<&2, Char>,
  +clock: T.Clock,
  +date: T.Date,
  +ed: {T.wf.date(date) == True{} : Bool},
  +ec: {T.wf.clock(clock) == True{} : Bool}
) -> {gd.wot(T.when.zone.minus(minus, tt, clock, date)) == True{} : Bool}:
  match minus:
    case True{}:
      gd.wz.hh(T.take.n(2n, tt, 0, True{}), T.Minus{}, clock, date, ed, ec)
    case False{}:
      {==}

# a signed offset
def gd.wz.sign(
  plus: Bool,
  +minus: Bool,
  +tt: List<&2, Char>,
  +clock: T.Clock,
  +date: T.Date,
  +ed: {T.wf.date(date) == True{} : Bool},
  +ec: {T.wf.clock(clock) == True{} : Bool}
) -> {gd.wot(T.when.zone.sign(plus, minus, tt, clock, date)) == True{} : Bool}:
  match plus:
    case True{}:
      gd.wz.hh(T.take.n(2n, tt, 0, True{}), T.Plus{}, clock, date, ed, ec)
    case False{}:
      gd.wz.minus(minus, tt, clock, date, ed, ec)

# Z or an offset
def gd.wz.go(
  zee: Bool,
  +plus: Bool,
  +minus: Bool,
  +tt: List<&2, Char>,
  +clock: T.Clock,
  +date: T.Date,
  +ed: {T.wf.date(date) == True{} : Bool},
  +ec: {T.wf.clock(clock) == True{} : Bool}
) -> {gd.wot(T.when.zone.go(zee, plus, minus, tt, clock, date)) == True{} : Bool}:
  match zee:
    case True{}:
      gd.wz.z(tt, clock, date, ed, ec)
    case False{}:
      gd.wz.sign(plus, minus, tt, clock, date, ed, ec)

# a zone after a well-formed date and clock, or none
def gd.wz(
  cs: List<&2, Char>,
  +clock: T.Clock,
  +date: T.Date,
  +ed: {T.wf.date(date) == True{} : Bool},
  +ec: {T.wf.clock(clock) == True{} : Bool}
) -> {gd.wot(T.when.zone(cs, clock, date)) == True{} : Bool}:
  match cs:
    case []:
      gd.tt(T.wf.date(date), T.wf.clock(clock), ed, ec)
    case +cc <> +tt:
      gd.wz.go(Bool.or(Char.is_eq(cc, 'Z'), Char.is_eq(cc, 'z')), Char.is_eq(cc, '+'), Char.is_eq(cc, '-'), tt,
        clock, date, ed, ec)

# every character is a digit
def gd.dl(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      True{}
    case +hh <> tt:
      Bool.and(Char.is_digit(hh), gd.dl(tt))

# digits reversed onto a text of digits are a text of digits
def gd.dl.rev(
  cs: List<&2, Char>,
  +acc: List<&2, Char>,
  +ec: {gd.dl(cs) == True{} : Bool},
  +ea: {T.wf.digits(String.from_list(acc)) == True{} : Bool}
) -> {T.wf.digits(String.from_list(List.reverse.go(&2, Char, cs, acc))) == True{} : Bool}:
  match cs:
    case []:
      ea
    case +hh <> +tt:
      gd.dl.rev(tt, hh <> acc, gd.r(Char.is_digit(hh), gd.dl(tt), ec),
        gd.then(Char.is_digit(hh), _u => T.wf.digits(String.from_list(acc)), gd.l(Char.is_digit(hh), gd.dl(tt), ec),
          ea))

# a clock with a fraction of digits is well-formed
def gd.clock.with(
  clock: T.Clock,
  +frac: String,
  +ec: {T.wf.clock(clock) == True{} : Bool},
  +ef: {T.wf.digits(frac) == True{} : Bool}
) -> {T.wf.clock(T.clock.with(clock, frac)) == True{} : Bool}:
  match clock:
    case T.Clock{+hh, +mi, +ss, +fr}:
      gd.tt(U32.is_le(hh, 23), Bool.and(U32.is_le(mi, 59), Bool.and(U32.is_le(ss, 60), T.wf.digits(frac))),
        gd.l(U32.is_le(hh, 23), Bool.and(U32.is_le(mi, 59), Bool.and(U32.is_le(ss, 60), T.wf.digits(fr))), ec),
        gd.tt(U32.is_le(mi, 59), Bool.and(U32.is_le(ss, 60), T.wf.digits(frac)),
          gd.l(U32.is_le(mi, 59), Bool.and(U32.is_le(ss, 60), T.wf.digits(fr)),
            gd.r(U32.is_le(hh, 23), Bool.and(U32.is_le(mi, 59), Bool.and(U32.is_le(ss, 60), T.wf.digits(fr))), ec)),
          gd.tt(U32.is_le(ss, 60), T.wf.digits(frac),
            gd.l(U32.is_le(ss, 60), T.wf.digits(fr), gd.r(U32.is_le(mi, 59), Bool.and(U32.is_le(ss, 60),
              T.wf.digits(fr)), gd.r(U32.is_le(hh, 23), Bool.and(U32.is_le(mi, 59), Bool.and(U32.is_le(ss, 60),
              T.wf.digits(fr))), ec))),
            ef)))

# the fraction's end: it must hold a digit
def gd.wf.endgo(
  some: Bool,
  +rev: List<&2, Char>,
  +clock: T.Clock,
  +date: T.Date,
  +rest: List<&2, Char>,
  +ed: {T.wf.date(date) == True{} : Bool},
  +ec: {T.wf.clock(clock) == True{} : Bool},
  +er: {gd.dl(rev) == True{} : Bool}
) -> {gd.wot(T.when.frac.end.go(some, rev, clock, date, rest)) == True{} : Bool}:
  match some:
    case False{}:
      {==}
    case True{}:
      gd.wz(rest, T.clock.with(clock, T.buf.str.go(rev, "")), date, ed,
        gd.clock.with(clock, T.buf.str.go(rev, ""), ec,
          Equal.trans(Bool,
            T.wf.digits(T.buf.str.go(rev, "")),
            T.wf.digits(String.from_list(List.reverse(&2, Char, rev))),
            True{},
            Equal.cong(String, Bool, fs => T.wf.digits(fs),
              T.buf.str.go(rev, ""),
              String.from_list(List.reverse(&2, Char, rev)),
              M1.fold.nil(rev)),
            gd.dl.rev(rev, [], er, {==}))))

# the fraction's digits, one at a time
def gd.wf.dig(
  digit: Bool,
  +cc: Char,
  +tt: List<&2, Char>,
  +rev: List<&2, Char>,
  +clock: T.Clock,
  +date: T.Date,
  +ed: {T.wf.date(date) == True{} : Bool},
  +ec: {T.wf.clock(clock) == True{} : Bool},
  +er: {gd.dl(rev) == True{} : Bool},
  +eg: {Char.is_digit(cc) == digit : Bool},
  ih: {gd.dl(cc <> rev) == True{} : Bool} -> {gd.wot(T.when.frac.digits(tt, cc <> rev, clock, date)) == True{} : Bool}
) -> {gd.wot(T.when.frac.digit(digit, cc, tt, rev, clock, date, _u => T.when.frac.digits(tt, cc <> rev, clock,
  date))) == True{} : Bool}:
  match digit:
    case True{}:
      ih(gd.tt(Char.is_digit(cc), gd.dl(rev), eg, er))
    case False{}:
      gd.wf.endgo(T.cs.some(rev), rev, clock, date, cc <> tt, ed, ec, er)

# the fraction's digits
def gd.wf.digits(
  cs: List<&2, Char>,
  +rev: List<&2, Char>,
  +clock: T.Clock,
  +date: T.Date,
  +ed: {T.wf.date(date) == True{} : Bool},
  +ec: {T.wf.clock(clock) == True{} : Bool},
  +er: {gd.dl(rev) == True{} : Bool}
) -> {gd.wot(T.when.frac.digits(cs, rev, clock, date)) == True{} : Bool}:
  match cs:
    case []:
      gd.wf.endgo(T.cs.some(rev), rev, clock, date, [], ed, ec, er)
    case +cc <> +tt:
      gd.wf.dig(Char.is_digit(cc), cc, tt, rev, clock, date, ed, ec, er, {==},
        e2 => gd.wf.digits(tt, cc <> rev, clock, date, ed, ec, e2))

# a dot starts the fraction
def gd.wf.go(
  dot: Bool,
  +tt: List<&2, Char>,
  +clock: T.Clock,
  +date: T.Date,
  +cc: Char,
  +ed: {T.wf.date(date) == True{} : Bool},
  +ec: {T.wf.clock(clock) == True{} : Bool}
) -> {gd.wot(T.when.frac.go(dot, tt, clock, date, cc)) == True{} : Bool}:
  match dot:
    case True{}:
      gd.wf.digits(tt, [], clock, date, ed, ec, {==})
    case False{}:
      gd.wz(cc <> tt, clock, date, ed, ec)

# an optional fraction
def gd.wfr(
  cs: List<&2, Char>,
  +clock: T.Clock,
  +date: T.Date,
  +ed: {T.wf.date(date) == True{} : Bool},
  +ec: {T.wf.clock(clock) == True{} : Bool}
) -> {gd.wot(T.when.frac(cs, clock, date)) == True{} : Bool}:
  match cs:
    case []:
      gd.tt(T.wf.date(date), T.wf.clock(clock), ed, ec)
    case +cc <> +tt:
      gd.wf.go(Char.is_eq(cc, '.'), tt, clock, date, cc, ed, ec)

# the second's range
def gd.wc.rs(
  s_ok: Bool,
  +hh: U32,
  +mi: U32,
  +ss: U32,
  +cs: List<&2, Char>,
  +date: T.Date,
  +ed: {T.wf.date(date) == True{} : Bool},
  +eh: {U32.is_le(hh, 23) == True{} : Bool},
  +em: {U32.is_le(mi, 59) == True{} : Bool},
  +es: {T.bound.rng(ss, 0, 60) == s_ok : Bool}
) -> {gd.wot(T.when.clock.range.s(s_ok, hh, mi, ss, cs, date)) == True{} : Bool}:
  match s_ok:
    case False{}:
      {==}
    case True{}:
      gd.wfr(cs, T.Clock{hh, mi, ss, ""}, date, ed,
        gd.tt(U32.is_le(hh, 23), Bool.and(U32.is_le(mi, 59), Bool.and(U32.is_le(ss, 60), True{})), eh,
          gd.tt(U32.is_le(mi, 59), Bool.and(U32.is_le(ss, 60), True{}), em,
            gd.tt(U32.is_le(ss, 60), True{}, gd.rng.hi(ss, 0, 60, es), {==}))))

# the minute's range
def gd.wc.rm(
  mi_ok: Bool,
  +s_ok: Bool,
  +hh: U32,
  +mi: U32,
  +ss: U32,
  +cs: List<&2, Char>,
  +date: T.Date,
  +ed: {T.wf.date(date) == True{} : Bool},
  +eh: {U32.is_le(hh, 23) == True{} : Bool},
  +em: {T.bound.rng(mi, 0, 59) == mi_ok : Bool},
  +es: {T.bound.rng(ss, 0, 60) == s_ok : Bool}
) -> {gd.wot(T.when.clock.range.m(mi_ok, s_ok, hh, mi, ss, cs, date)) == True{} : Bool}:
  match mi_ok:
    case False{}:
      {==}
    case True{}:
      gd.wc.rs(s_ok, hh, mi, ss, cs, date, ed, eh, gd.rng.hi(mi, 0, 59, em), es)

# the hour's range
def gd.wc.r(
  h_ok: Bool,
  +mi_ok: Bool,
  +s_ok: Bool,
  +hh: U32,
  +mi: U32,
  +ss: U32,
  +cs: List<&2, Char>,
  +date: T.Date,
  +ed: {T.wf.date(date) == True{} : Bool},
  +eh: {T.bound.rng(hh, 0, 23) == h_ok : Bool},
  +em: {T.bound.rng(mi, 0, 59) == mi_ok : Bool},
  +es: {T.bound.rng(ss, 0, 60) == s_ok : Bool}
) -> {gd.wot(T.when.clock.range(h_ok, mi_ok, s_ok, hh, mi, ss, cs, date)) == True{} : Bool}:
  match h_ok:
    case False{}:
      {==}
    case True{}:
      gd.wc.rm(mi_ok, s_ok, hh, mi, ss, cs, date, ed, gd.rng.hi(hh, 0, 23, eh), em, es)

# the seconds
def gd.wc.ssgo(
  dd: T.Dig,
  +hh: U32,
  +mi: U32,
  +date: T.Date,
  +ed: {T.wf.date(date) == True{} : Bool}
) -> {gd.wot(T.when.clock.ss.go(dd, hh, mi, date)) == True{} : Bool}:
  match dd:
    case T.DigBad{}:
      {==}
    case T.DigOk{+nn, +cs}:
      gd.wc.r(T.bound.rng(hh, 0, 23), T.bound.rng(mi, 0, 59), T.bound.rng(nn, 0, 60), hh, mi, nn, cs, date, ed, {==},
        {==}, {==})

# the seconds, after a colon
def gd.wc.ss(
  hit: Bool,
  +dd: T.Dig,
  +hh: U32,
  +mi: U32,
  +date: T.Date,
  +ed: {T.wf.date(date) == True{} : Bool}
) -> {gd.wot(T.when.clock.ss(hit, dd, hh, mi, date)) == True{} : Bool}:
  match hit:
    case False{}:
      {==}
    case True{}:
      gd.wc.ssgo(dd, hh, mi, date, ed)

# the colon after the minutes
def gd.wc.mmcolon(
  cs: List<&2, Char>,
  +hh: U32,
  +mi: U32,
  +date: T.Date,
  +ed: {T.wf.date(date) == True{} : Bool}
) -> {gd.wot(T.when.clock.mm.colon(cs, hh, mi, date)) == True{} : Bool}:
  match cs:
    case []:
      {==}
    case +cc <> +tt:
      gd.wc.ss(Char.is_eq(cc, ':'), T.take.n(2n, tt, 0, True{}), hh, mi, date, ed)

# the minutes
def gd.wc.mm(
  dd: T.Dig,
  +hh: U32,
  +date: T.Date,
  +ed: {T.wf.date(date) == True{} : Bool}
) -> {gd.wot(T.when.clock.mm(dd, hh, date)) == True{} : Bool}:
  match dd:
    case T.DigBad{}:
      {==}
    case T.DigOk{+nn, +cs}:
      gd.wc.mmcolon(cs, hh, nn, date, ed)

# the colon after the hour
def gd.wc.colongo(
  hit: Bool,
  +hh: U32,
  +tt: List<&2, Char>,
  +date: T.Date,
  +ed: {T.wf.date(date) == True{} : Bool}
) -> {gd.wot(T.when.clock.colon.go(hit, hh, tt, date)) == True{} : Bool}:
  match hit:
    case False{}:
      {==}
    case True{}:
      gd.wc.mm(T.take.n(2n, tt, 0, True{}), hh, date, ed)

# the character after the hour
def gd.wc.colon(
  cs: List<&2, Char>,
  +hh: U32,
  +date: T.Date,
  +ed: {T.wf.date(date) == True{} : Bool}
) -> {gd.wot(T.when.clock.colon(cs, hh, date)) == True{} : Bool}:
  match cs:
    case []:
      {==}
    case +cc <> +tt:
      gd.wc.colongo(Char.is_eq(cc, ':'), hh, tt, date, ed)

# a clock after a date
def gd.wc.of(
  dd: T.Dig,
  +date: T.Date,
  +ed: {T.wf.date(date) == True{} : Bool}
) -> {gd.wot(T.when.clock.of(dd, date)) == True{} : Bool}:
  match dd:
    case T.DigBad{}:
      {==}
    case T.DigOk{+nn, +cs}:
      gd.wc.colon(cs, nn, date, ed)

# a space before the time
def gd.wd.sp(
  sp: Bool,
  +date: T.Date,
  +tt: List<&2, Char>,
  +ed: {T.wf.date(date) == True{} : Bool}
) -> {gd.wot(T.when.after.sp(sp, date, tt)) == True{} : Bool}:
  match sp:
    case True{}:
      gd.wc.of(T.take.n(2n, tt, 0, True{}), date, ed)
    case False{}:
      {==}

# T or a space before the time
def gd.wd.sep(
  tee: Bool,
  +sp: Bool,
  +date: T.Date,
  +tt: List<&2, Char>,
  +ed: {T.wf.date(date) == True{} : Bool}
) -> {gd.wot(T.when.after.sep(tee, sp, date, tt)) == True{} : Bool}:
  match tee:
    case True{}:
      gd.wc.of(T.take.n(2n, tt, 0, True{}), date, ed)
    case False{}:
      gd.wd.sp(sp, date, tt, ed)

# what follows a well-formed date
def gd.wd.after(
  +date: T.Date,
  cs: List<&2, Char>,
  +ed: {T.wf.date(date) == True{} : Bool}
) -> {gd.wot(T.when.after.date(date, cs)) == True{} : Bool}:
  match cs:
    case []:
      ed
    case +cc <> +tt:
      gd.wd.sep(Bool.or(Char.is_eq(cc, 'T'), Char.is_eq(cc, 't')), Char.is_eq(cc, ' '), date, tt, ed)

# the day's range
def gd.wd.okd(
  d_ok: Bool,
  +yy: U32,
  +mo: U32,
  +dd: U32,
  +cs: List<&2, Char>,
  +ey: {U32.is_le(yy, 9999) == True{} : Bool},
  +em: {T.bound.rng(mo, 1, 12) == True{} : Bool},
  +ed: {T.bound.rng(dd, 1, T.when.days(yy, mo)) == d_ok : Bool}
) -> {gd.wot(T.when.date.ok.d(d_ok, yy, mo, dd, cs)) == True{} : Bool}:
  match d_ok:
    case False{}:
      {==}
    case True{}:
      gd.wd.after(T.Date{yy, mo, dd}, cs,
        gd.tt(U32.is_le(yy, 9999), Bool.and(T.bound.rng(mo, 1, 12), T.bound.rng(dd, 1, T.when.days(yy, mo))), ey,
          gd.tt(T.bound.rng(mo, 1, 12), T.bound.rng(dd, 1, T.when.days(yy, mo)), em, ed)))

# the month's range
def gd.wd.okgo(
  mo_ok: Bool,
  +d_ok: Bool,
  +yy: U32,
  +mo: U32,
  +dd: U32,
  +cs: List<&2, Char>,
  +ey: {U32.is_le(yy, 9999) == True{} : Bool},
  +em: {T.bound.rng(mo, 1, 12) == mo_ok : Bool},
  +ed: {T.bound.rng(dd, 1, T.when.days(yy, mo)) == d_ok : Bool}
) -> {gd.wot(T.when.date.ok.go(mo_ok, d_ok, yy, mo, dd, cs)) == True{} : Bool}:
  match mo_ok:
    case False{}:
      {==}
    case True{}:
      gd.wd.okd(d_ok, yy, mo, dd, cs, ey, em, ed)

# a date whose year is below ten thousand
def gd.wd.ok(
  +yy: U32,
  +mo: U32,
  +dd: U32,
  +cs: List<&2, Char>,
  +ey: {U32.is_le(yy, 9999) == True{} : Bool}
) -> {gd.wot(T.when.date.ok(yy, mo, dd, cs)) == True{} : Bool}:
  gd.wd.okgo(T.bound.rng(mo, 1, 12), T.bound.rng(dd, 1, T.when.days(yy, mo)), yy, mo, dd, cs, ey, {==}, {==})

# the day's digits
def gd.wd.dayend(
  dd: T.Dig,
  +yy: U32,
  +mo: U32,
  +ey: {U32.is_le(yy, 9999) == True{} : Bool}
) -> {gd.wot(T.when.day.end(dd, yy, mo)) == True{} : Bool}:
  match dd:
    case T.DigBad{}:
      {==}
    case T.DigOk{+nn, +cs}:
      gd.wd.ok(yy, mo, nn, cs, ey)

# the dash before the day
def gd.wd.daygo(
  hit: Bool,
  +dd: T.Dig,
  +yy: U32,
  +mo: U32,
  +ey: {U32.is_le(yy, 9999) == True{} : Bool}
) -> {gd.wot(T.when.day.go(hit, dd, yy, mo)) == True{} : Bool}:
  match hit:
    case False{}:
      {==}
    case True{}:
      gd.wd.dayend(dd, yy, mo, ey)

# the day
def gd.wd.day(
  cs: List<&2, Char>,
  +yy: U32,
  +mo: U32,
  +ey: {U32.is_le(yy, 9999) == True{} : Bool}
) -> {gd.wot(T.when.day(cs, yy, mo)) == True{} : Bool}:
  match cs:
    case []:
      {==}
    case +cc <> +tt:
      gd.wd.daygo(Char.is_eq(cc, '-'), T.take.n(2n, tt, 0, True{}), yy, mo, ey)

# the month's digits
def gd.wd.mogo(
  dd: T.Dig,
  +yy: U32,
  +ey: {U32.is_le(yy, 9999) == True{} : Bool}
) -> {gd.wot(T.when.month.go(dd, yy)) == True{} : Bool}:
  match dd:
    case T.DigBad{}:
      {==}
    case T.DigOk{+nn, +cs}:
      gd.wd.day(cs, yy, nn, ey)

# the dash before the month
def gd.wd.mo(
  hit: Bool,
  +dd: T.Dig,
  +yy: U32,
  +ey: {U32.is_le(yy, 9999) == True{} : Bool}
) -> {gd.wot(T.when.month(hit, dd, yy)) == True{} : Bool}:
  match hit:
    case False{}:
      {==}
    case True{}:
      gd.wd.mogo(dd, yy, ey)

# the month
def gd.wd.ydash(
  cs: List<&2, Char>,
  +yy: U32,
  +ey: {U32.is_le(yy, 9999) == True{} : Bool}
) -> {gd.wot(T.when.year.dash(cs, yy)) == True{} : Bool}:
  match cs:
    case []:
      {==}
    case +cc <> +tt:
      gd.wd.mo(Char.is_eq(cc, '-'), T.take.n(2n, tt, 0, True{}), yy, ey)

# four digits of year are below ten thousand
def gd.wd.y4(dd: T.Dig, +ek: {gd.dk(dd, 10000) == True{} : Bool}) -> {gd.wot(T.when.year4(dd)) == True{} : Bool}:
  match dd:
    case T.DigBad{}:
      {==}
    case T.DigOk{+nn, +cs}:
      gd.wd.ydash(cs, nn, Equal.trans(Bool, U32.is_le(nn, 9999), U32.is_lt(nn, U32.add(9999, 1)), True{},
        M2.le2lt(nn, 9999, {==}), ek))

# the third digit of a year
def gd.wd.ymore(
  digit: Bool,
  +nn: U32,
  +cc: Char,
  +tt: List<&2, Char>,
  +en: {U32.is_lt(nn, 100) == True{} : Bool},
  +eg: {Char.is_digit(cc) == digit : Bool}
) -> {gd.wot(T.when.year.more(digit, nn, cc, tt)) == True{} : Bool}:
  match digit:
    case False{}:
      {==}
    case True{}:
      gd.wd.y4(T.take.n(1n, tt, U32.add(U32.mul(nn, 10), T.dig.val(cc)), True{}),
        gd.tk1(tt, U32.add(U32.mul(nn, 10), T.dig.val(cc)), True{}, 1000,
          gd.u.step(Unit{}, nn, T.dig.val(cc), 100, en, gd.dg.val(cc, eg), {==}), {==}))

# a local time: its dummy date is well-formed, and only the clock is kept
def gd.wt.only(ww: T.WhenOut, +ee: {gd.wot(ww) == True{} : Bool}) -> {gd.wot(T.when.time.only(ww)) == True{} : Bool}:
  match ww:
    case T.WSome{w}:
      match w:
        case T.WLocal{+d0, +c0}:
          gd.r(T.wf.date(d0), T.wf.clock(c0), ee)
        case T.WOff{_d, _c, _z}:
          {==}
        case T.WDate{_d}:
          {==}
        case T.WTime{_c}:
          {==}
    case T.WFail{_why}:
      {==}
    case T.WSkip{}:
      {==}

# a time or a date after two digits
def gd.wd.branch(
  colon: Bool,
  +digit: Bool,
  +nn: U32,
  +cc: Char,
  +tt: List<&2, Char>,
  +en: {U32.is_lt(nn, 100) == True{} : Bool},
  +eg: {Char.is_digit(cc) == digit : Bool}
) -> {gd.wot(T.when.branch(colon, digit, nn, cc, tt)) == True{} : Bool}:
  match colon:
    case True{}:
      gd.wt.only(T.when.time.rest(tt, nn), gd.wc.mm(T.take.n(2n, tt, 0, True{}), nn, T.Date{0, 1, 1}, {==}))
    case False{}:
      gd.wd.ymore(digit, nn, cc, tt, en, eg)

# the character after two digits
def gd.wd.a2go(
  cs: List<&2, Char>,
  +nn: U32,
  +en: {U32.is_lt(nn, 100) == True{} : Bool}
) -> {gd.wot(T.when.after2.go(cs, nn)) == True{} : Bool}:
  match cs:
    case []:
      {==}
    case +cc <> +tt:
      gd.wd.branch(Char.is_eq(cc, ':'), Char.is_digit(cc), nn, cc, tt, en, {==})

# two digits
def gd.wd.a2(dd: T.Dig, +ek: {gd.dk(dd, 100) == True{} : Bool}) -> {gd.wot(T.when.after2(dd)) == True{} : Bool}:
  match dd:
    case T.DigBad{}:
      {==}
    case T.DigOk{+nn, +cs}:
      gd.wd.a2go(cs, nn, ek)

# every datetime the scan reads is well-formed
def gd.when(+cs: List<&2, Char>) -> {gd.wot(T.when.read(cs)) == True{} : Bool}:
  gd.wd.a2(T.take.n(2n, cs, 0, True{}), gd.tk2(cs))

# Numerals. An integer's digits are decimal digits written with no leading
# zero, since every digit dec.go makes is a remainder by ten and dec.drop
# drops the leading zeros; its range is checked as wf.int does. A float's
# spelling, its sign and underscores dropped, is read by wf.flo's automaton
# in step with the numeral scan: gd.nk says which state of each the two are in.

# every value is below ten
def gd.d10(ds: List<&2, U32>) -> Bool:
  match ds:
    case []:
      True{}
    case +dd <> tt:
      Bool.and(U32.is_lt(dd, 10), gd.d10(tt))

# a remainder by ten, then the rest
def gd.d10.cons(
  +xx: U32,
  +tt: List<&2, U32>,
  +et: {gd.d10(tt) == True{} : Bool}
) -> {gd.d10(U32.mod(xx, 10) <> tt) == True{} : Bool}:
  gd.tt(U32.is_lt(U32.mod(xx, 10), 10), gd.d10(tt), M6.md(xx), et)

# the last digit of a carry
def gd.d10.c0(zz: Bool, +cc: U32) -> {gd.d10(T.dec.carry.c0(zz, cc)) == True{} : Bool}:
  match zz:
    case True{}:
      {==}
    case False{}:
      gd.d10.cons(cc, [], {==})

# the middle digit of a carry
def gd.d10.b0(zz: Bool, +cc: U32) -> {gd.d10(T.dec.carry.b0(zz, cc)) == True{} : Bool}:
  match zz:
    case True{}:
      {==}
    case False{}:
      gd.d10.cons(cc, T.dec.carry.c(U32.div(cc, 10)), gd.d10.c0(U32.is_zero(U32.div(cc, 10)), U32.div(cc, 10)))

# the first digit of a carry
def gd.d10.a(zz: Bool, +cc: U32) -> {gd.d10(T.dec.carry.a(zz, cc)) == True{} : Bool}:
  match zz:
    case True{}:
      {==}
    case False{}:
      gd.d10.cons(cc, T.dec.carry.b(U32.div(cc, 10)), gd.d10.b0(U32.is_zero(U32.div(cc, 10)), U32.div(cc, 10)))

# every digit dec.go makes is below ten
def gd.d10.go(ds: List<&2, U32>, +radix: U32, +carry: U32) -> {gd.d10(T.dec.go(ds, radix, carry)) == True{} : Bool}:
  match ds:
    case []:
      gd.d10.a(U32.is_zero(carry), carry)
    case +dd <> +tt:
      gd.d10.cons(U32.add(U32.mul(dd, radix), carry),
        T.dec.go(tt, radix, U32.div(U32.add(U32.mul(dd, radix), carry), 10)),
        gd.d10.go(tt, radix, U32.div(U32.add(U32.mul(dd, radix), carry), 10)))

# digits below ten reversed onto more
def gd.d10.rev(
  ds: List<&2, U32>,
  +acc: List<&2, U32>,
  +ed: {gd.d10(ds) == True{} : Bool},
  +ea: {gd.d10(acc) == True{} : Bool}
) -> {gd.d10(List.reverse.go(&2, U32, ds, acc)) == True{} : Bool}:
  match ds:
    case []:
      ea
    case +dd <> +tt:
      gd.d10.rev(tt, dd <> acc, gd.r(U32.is_lt(dd, 10), gd.d10(tt), ed),
        gd.tt(U32.is_lt(dd, 10), gd.d10(acc), gd.l(U32.is_lt(dd, 10), gd.d10(tt), ed), ea))

# a value below ten is written as a digit
def gd.dch(+dd: U32, +ed: {U32.is_lt(dd, 10) == True{} : Bool}) -> {Char.is_digit(T.dec.ch(dd)) == True{} : Bool}:
  M5.sm.elim(xx => {Char.is_digit(T.dec.ch(xx)) == True{} : Bool}, dd, ed,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# values below ten are written as digits
def gd.dl.chars(ds: List<&2, U32>, +ed: {gd.d10(ds) == True{} : Bool}) -> {gd.dl(T.dec.chars(ds)) == True{} : Bool}:
  match ds:
    case []:
      {==}
    case +dd <> +tt:
      gd.tt(Char.is_digit(T.dec.ch(dd)), gd.dl(T.dec.chars(tt)),
        gd.dch(dd, gd.l(U32.is_lt(dd, 10), gd.d10(tt), ed)), gd.dl.chars(tt, gd.r(U32.is_lt(dd, 10), gd.d10(tt), ed)))

# the rest of gd.rd: none left, so the digit was the first written
def gd.rd.tail(tt: List<&2, Char>, +hh: Char) -> Bool:
  match tt:
    case []:
      Bool.not(Char.is_eq(hh, '0'))
    case +h2 <> t2:
      Bool.and(Char.is_digit(h2), gd.rd.tail(t2, h2))

# digits whose last, the first written, is not a zero
def gd.rd(out: List<&2, Char>) -> Bool:
  match out:
    case []:
      False{}
    case +hh <> tt:
      Bool.and(Char.is_digit(hh), gd.rd.tail(tt, hh))

# the first written digit, not a zero, then digits
def gd.rd.first(
  zz: Bool,
  +hh: Char,
  +acc: String,
  _ez: {Char.is_eq(hh, '0') == zz : Bool},
  +en: {Bool.not(zz) == True{} : Bool},
  +ed: {Char.is_digit(hh) == True{} : Bool},
  +ea: {T.wf.digits(acc) == True{} : Bool}
) -> {T.wf.dec.lead(zz, hh, acc) == True{} : Bool}:
  match zz:
    case True{}:
      Eq.bit.absurd2(&2, {T.wf.dec.lead(True{}, hh, acc) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, en))
    case False{}:
      gd.tt(Char.is_digit(hh), T.wf.digits(acc), ed, ea)

# digits reversed onto digits, the first written not a zero, are decimal
def gd.rd.dec(
  tt: List<&2, Char>,
  +hh: Char,
  +acc: List<&2, Char>,
  +ed: {Bool.and(Char.is_digit(hh), gd.rd.tail(tt, hh)) == True{} : Bool},
  +ea: {T.wf.digits(String.from_list(acc)) == True{} : Bool}
) -> {T.wf.dec(String.from_list(List.reverse.go(&2, Char, tt, hh <> acc))) == True{} : Bool}:
  match tt:
    case []:
      gd.rd.first(Char.is_eq(hh, '0'), hh, String.from_list(acc), {==},
        gd.r(Char.is_digit(hh), Bool.not(Char.is_eq(hh, '0')), ed), gd.l(Char.is_digit(hh), Bool.not(Char.is_eq(hh,
          '0')), ed), ea)
    case +h2 <> +t2:
      gd.rd.dec(t2, h2, hh <> acc, gd.r(Char.is_digit(hh), Bool.and(Char.is_digit(h2), gd.rd.tail(t2, h2)), ed),
        gd.then(Char.is_digit(hh), _u => T.wf.digits(String.from_list(acc)), gd.l(Char.is_digit(hh),
          Bool.and(Char.is_digit(h2), gd.rd.tail(t2, h2)), ed), ea))

# the rest of the digits once a nonzero one was kept
def gd.drop.f(
  cs: List<&2, Char>,
  +out: List<&2, Char>,
  +ec: {gd.dl(cs) == True{} : Bool},
  +eo: {gd.rd(out) == True{} : Bool}
) -> {T.wf.dec(T.dec.drop(cs, False{}, out)) == True{} : Bool}:
  match cs:
    case []:
      match out:
        case []:
          Eq.bit.absurd(&2, {T.wf.dec(T.dec.drop([], False{}, [])) == True{} : Bool}, eo)
        case +o1 <> +ot:
          Equal.trans(Bool,
            T.wf.dec(T.buf.str.go(ot, SCon{o1, ""})),
            T.wf.dec(String.from_list(List.reverse.go(&2, Char, ot, [o1]))),
            True{},
            Equal.cong(String, Bool, ss => T.wf.dec(ss),
              T.buf.str.go(ot, SCon{o1, ""}),
              String.from_list(List.reverse.go(&2, Char, ot, [o1])),
              M1.fold.nil(o1 <> ot)),
            gd.rd.dec(ot, o1, [], eo, {==}))
    case +hh <> +tt:
      match out:
        case []:
          Eq.bit.absurd(&2, {T.wf.dec(T.dec.drop(hh <> tt, False{}, [])) == True{} : Bool}, eo)
        case +o1 <> +ot:
          gd.drop.f(tt, hh <> (o1 <> ot), gd.r(Char.is_digit(hh), gd.dl(tt), ec),
            gd.tt(Char.is_digit(hh), gd.rd.tail(o1 <> ot, hh), gd.l(Char.is_digit(hh), gd.dl(tt), ec), eo))

# the leading zeros are dropped
def gd.drop.z(
  zz: Bool,
  +hh: Char,
  +tt: List<&2, Char>,
  +ez: {Char.is_eq(hh, '0') == zz : Bool},
  +eh: {Char.is_digit(hh) == True{} : Bool},
  +ec: {gd.dl(tt) == True{} : Bool},
  +ih: {T.wf.dec(T.dec.drop(tt, True{}, [])) == True{} : Bool}
) -> {T.wf.dec(T.dec.drop(tt, zz, T.dec.drop.outz(zz, hh, []))) == True{} : Bool}:
  match zz:
    case True{}:
      ih
    case False{}:
      gd.drop.f(tt, [hh], ec, gd.tt(Char.is_digit(hh), Bool.not(Char.is_eq(hh, '0')), eh,
        Equal.cong(Bool, Bool, bb => Bool.not(bb), Char.is_eq(hh, '0'), False{}, ez)))

# digits with the leading zeros dropped are decimal
def gd.drop.t(
  cs: List<&2, Char>,
  +ec: {gd.dl(cs) == True{} : Bool}
) -> {T.wf.dec(T.dec.drop(cs, True{}, [])) == True{} : Bool}:
  match cs:
    case []:
      {==}
    case +hh <> +tt:
      gd.drop.z(Char.is_eq(hh, '0'), hh, tt, {==}, gd.l(Char.is_digit(hh), gd.dl(tt), ec),
        gd.r(Char.is_digit(hh), gd.dl(tt), ec), gd.drop.t(tt, gd.r(Char.is_digit(hh), gd.dl(tt), ec)))

# an integer's text is decimal
def gd.dec.text(+ds: List<&2, U32>, +ed: {gd.d10(ds) == True{} : Bool}) -> {T.wf.dec(T.dec.text(ds)) == True{} : Bool}:
  gd.drop.t(T.dec.chars(List.reverse(&2, U32, ds)),
    gd.dl.chars(List.reverse(&2, U32, ds), gd.d10.rev(ds, [], ed, {==})))

# which state of wf.flo's automaton a spelling is in
def gd.flq(aa: T.Fl, bb: T.Fl) -> Bool:
  match aa bb:
    case T.FlStart{} T.FlStart{}:
      True{}
    case T.FlZero{} T.FlZero{}:
      True{}
    case T.FlInt{} T.FlInt{}:
      True{}
    case T.FlDot{} T.FlDot{}:
      True{}
    case T.FlFrac{} T.FlFrac{}:
      True{}
    case T.FlE{} T.FlE{}:
      True{}
    case T.FlESign{} T.FlESign{}:
      True{}
    case T.FlExp{} T.FlExp{}:
      True{}
    case T.FlNo{} T.FlNo{}:
      True{}
    case _a _b:
      False{}

# the numeral scan's state and the automaton's state agree: the scan has read
# the spelling the automaton has, and a numeral's first character, a sign,
# is not part of a float's spelling
def gd.nk(nk: T.NK, +lead: Bool, +saw: Bool, +fl: T.Fl) -> Bool:
  match nk:
    case T.NLead{}:
      Bool.and(lead, gd.flq(fl, T.FlStart{}))
    case T.NSign{}:
      Bool.and(Bool.not(lead), gd.flq(fl, T.FlStart{}))
    case T.NZero{}:
      Bool.and(Bool.not(lead), gd.flq(fl, T.FlZero{}))
    case T.NDig{}:
      Bool.and(Bool.not(lead), gd.flq(fl, T.FlInt{}))
    case T.NBase{}:
      True{}
    case T.NFrac{}:
      Bool.and(Bool.not(lead), gd.flq(fl, Bool.pick(T.Fl, saw, T.FlFrac{}, T.FlDot{})))
    case T.NExp{}:
      Bool.and(Bool.not(lead), gd.flq(fl, T.FlE{}))
    case T.NEDig{}:
      Bool.and(Bool.not(lead), gd.flq(fl, Bool.pick(T.Fl, saw, T.FlExp{}, T.FlESign{})))
    case T.NBad{}:
      True{}

# a numeral scan's state: its digits below ten, and its agreement
def gd.nm(st: T.Num, +lead: Bool, +fl: T.Fl) -> Bool:
  match st:
    case T.Num{nk, _sign, _base, ds, _us, +saw, _why}:
      Bool.and(gd.d10(ds), gd.nk(nk, lead, saw, fl))

# one of two states
def gd.fsel(bb: Bool, xx: T.Fl, yy: T.Fl) -> T.Fl:
  match bb:
    case True{}:
      xx
    case False{}:
      yy

# the automaton after one character of the spelling: word.body drops a
# leading sign and every underscore
def gd.fput(lead: Bool, +cc: Char, +fl: T.Fl) -> T.Fl:
  match lead:
    case True{}:
      gd.fsel(Bool.or(Char.is_eq(cc, '+'), Char.is_eq(cc, '-')), fl, T.wf.flo.step(fl, cc))
    case False{}:
      gd.fsel(Char.is_eq(cc, '_'), fl, T.wf.flo.step(fl, cc))

# the automaton after the spelling of these characters
def gd.fb(cs: List<&2, Char>, +lead: Bool, +fl: T.Fl) -> T.Fl:
  match cs:
    case []:
      fl
    case +hh <> tt:
      gd.fb(tt, False{}, gd.fput(lead, hh, fl))

# a digit joined to the numeral
def gd.n.digit(
  ok: Bool,
  +cc: Char,
  +nk: T.NK,
  +sign: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +fl: T.Fl,
  _ed: {gd.d10(ds) == True{} : Bool},
  +efl: {gd.nk(nk, False{}, True{}, fl) == True{} : Bool}
) -> {gd.nm(T.num.digit.ok(ok, cc, nk, sign, base, ds), False{}, fl) == True{} : Bool}:
  match ok:
    case False{}:
      {==}
    case True{}:
      gd.tt(gd.d10(T.dec.go(ds, base, T.dig.val(cc))), gd.nk(nk, False{}, True{}, fl),
        gd.d10.go(ds, base, T.dig.val(cc)), efl)

# an underscore between digits
def gd.n.us(
  ok: Bool,
  +nk: T.NK,
  +sign: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +why: String,
  +fl: T.Fl,
  +ed: {gd.d10(ds) == True{} : Bool},
  +efl: {L2.gd.ifok(ok, gd.nk(nk, False{}, True{}, fl)) == True{} : Bool}
) -> {gd.nm(T.num.us.go(ok, nk, sign, base, ds, why), False{}, fl) == True{} : Bool}:
  match ok:
    case False{}:
      {==}
    case True{}:
      gd.tt(gd.d10(ds), gd.nk(nk, False{}, True{}, fl), ed, efl)

# a dot
def gd.n.dot(
  ok: Bool,
  +sign: T.Sign,
  +fl: T.Fl,
  +efl: {L2.gd.ifok(ok, gd.nk(T.NFrac{}, False{}, False{}, fl)) == True{} : Bool}
) -> {gd.nm(T.num.dot.go(ok, sign), False{}, fl) == True{} : Bool}:
  match ok:
    case False{}:
      {==}
    case True{}:
      efl

# an exponent mark
def gd.n.exp(
  ok: Bool,
  +sign: T.Sign,
  +fl: T.Fl,
  +efl: {L2.gd.ifok(ok, gd.nk(T.NExp{}, False{}, False{}, fl)) == True{} : Bool}
) -> {gd.nm(T.num.exp.go(ok, sign), False{}, fl) == True{} : Bool}:
  match ok:
    case False{}:
      {==}
    case True{}:
      efl

# a digit's step of the automaton
def gd.dst.lead(
  +cc: Char,
  +eD: {Char.is_digit(cc) == True{} : Bool}
) -> {gd.fput(True{}, cc, T.FlStart{}) == Bool.pick(T.Fl, Char.is_eq(cc, '0'), T.FlZero{}, T.FlInt{}) : T.Fl}:
  M4.dg.elim(xx => {gd.fput(True{}, xx, T.FlStart{}) == Bool.pick(T.Fl, Char.is_eq(xx, '0'), T.FlZero{},
    T.FlInt{}) : T.Fl}, cc, eD, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==},
    {==})

# a digit's step of the automaton
def gd.dst.int(
  +cc: Char,
  +eD: {Char.is_digit(cc) == True{} : Bool}
) -> {gd.fput(False{}, cc, T.FlInt{}) == T.FlInt{} : T.Fl}:
  M4.dg.elim(xx => {gd.fput(False{}, xx, T.FlInt{}) == T.FlInt{} : T.Fl}, cc, eD, {==}, {==}, {==}, {==}, {==}, {==},
    {==}, {==}, {==},
    {==})

# a digit's step of the automaton
def gd.dst.dot(
  +cc: Char,
  +eD: {Char.is_digit(cc) == True{} : Bool}
) -> {gd.fput(False{}, cc, T.FlDot{}) == T.FlFrac{} : T.Fl}:
  M4.dg.elim(xx => {gd.fput(False{}, xx, T.FlDot{}) == T.FlFrac{} : T.Fl}, cc, eD, {==}, {==}, {==}, {==}, {==}, {==},
    {==}, {==}, {==},
    {==})

# a digit's step of the automaton
def gd.dst.frac(
  +cc: Char,
  +eD: {Char.is_digit(cc) == True{} : Bool}
) -> {gd.fput(False{}, cc, T.FlFrac{}) == T.FlFrac{} : T.Fl}:
  M4.dg.elim(xx => {gd.fput(False{}, xx, T.FlFrac{}) == T.FlFrac{} : T.Fl}, cc, eD, {==}, {==}, {==}, {==}, {==}, {==},
    {==}, {==}, {==},
    {==})

# a digit's step of the automaton
def gd.dst.e(
  +cc: Char,
  +eD: {Char.is_digit(cc) == True{} : Bool}
) -> {gd.fput(False{}, cc, T.FlE{}) == T.FlExp{} : T.Fl}:
  M4.dg.elim(xx => {gd.fput(False{}, xx, T.FlE{}) == T.FlExp{} : T.Fl}, cc, eD, {==}, {==}, {==}, {==}, {==}, {==},
      {==},
    {==}, {==},
    {==})

# a digit's step of the automaton
def gd.dst.esign(
  +cc: Char,
  +eD: {Char.is_digit(cc) == True{} : Bool}
) -> {gd.fput(False{}, cc, T.FlESign{}) == T.FlExp{} : T.Fl}:
  M4.dg.elim(xx => {gd.fput(False{}, xx, T.FlESign{}) == T.FlExp{} : T.Fl}, cc, eD, {==}, {==}, {==}, {==}, {==}, {==},
    {==}, {==}, {==},
    {==})

# a digit's step of the automaton
def gd.dst.exp(
  +cc: Char,
  +eD: {Char.is_digit(cc) == True{} : Bool}
) -> {gd.fput(False{}, cc, T.FlExp{}) == T.FlExp{} : T.Fl}:
  M4.dg.elim(xx => {gd.fput(False{}, xx, T.FlExp{}) == T.FlExp{} : T.Fl}, cc, eD, {==}, {==}, {==}, {==}, {==}, {==},
    {==}, {==}, {==},
    {==})

# the scan and the automaton after one character, in NLead
def gd.nd.NLead(
  P: Bool,
  M: Bool,
  Z: Bool,
  D: Bool,
  +sign: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String,
  +cc: Char,
  +eP: {Char.is_eq(cc, '+') == P : Bool},
  +eM: {Char.is_eq(cc, '-') == M : Bool},
  +eZ: {Char.is_eq(cc, '0') == Z : Bool},
  +eD: {Char.is_digit(cc) == D : Bool},
  +ed: {gd.d10(ds) == True{} : Bool}
) -> {gd.nm(T.num.lead.go(P, M, Z, D, T.Num{T.NLead{}, sign, base, ds, us, saw, why}, cc), False{}, gd.fput(True{},
  cc, T.FlStart{})) == True{} : Bool}:
  match P:
    case True{}:
      Equal.trans(Bool, gd.nm(T.num.sign(T.Num{T.NLead{}, sign, base, ds, us, saw, why}, T.Plus{}), False{},
        gd.fput(True{}, cc, T.FlStart{})), gd.nm(T.num.sign(T.Num{T.NLead{}, sign, base, ds, us, saw, why}, T.Plus{}),
          False{}, gd.fput(True{}, '+', T.FlStart{})), True{},
        Equal.cong(Char, Bool, xx => gd.nm(T.num.sign(T.Num{T.NLead{}, sign, base, ds, us, saw, why}, T.Plus{}),
          False{}, gd.fput(True{}, xx, T.FlStart{})), cc, '+', Eq.char_eq_true(cc, '+', eP)),
        {==})
    case False{}:
      match M:
        case True{}:
          Equal.trans(Bool, gd.nm(T.num.sign(T.Num{T.NLead{}, sign, base, ds, us, saw, why}, T.Minus{}), False{},
            gd.fput(True{}, cc, T.FlStart{})), gd.nm(T.num.sign(T.Num{T.NLead{}, sign, base, ds, us, saw, why},
              T.Minus{}), False{}, gd.fput(True{}, '-', T.FlStart{})), True{},
            Equal.cong(Char, Bool, xx => gd.nm(T.num.sign(T.Num{T.NLead{}, sign, base, ds, us, saw, why}, T.Minus{}),
              False{}, gd.fput(True{}, xx, T.FlStart{})), cc, '-', Eq.char_eq_true(cc, '-', eM)),
            {==})
        case False{}:
          match Z:
            case True{}:
              Equal.trans(Bool, gd.nm(T.Num{T.NZero{}, T.num.sign.of(T.Num{T.NLead{}, sign, base, ds, us, saw, why}),
                10, [], False{}, True{}, ""}, False{}, gd.fput(True{}, cc, T.FlStart{})), gd.nm(T.Num{T.NZero{},
                  T.num.sign.of(T.Num{T.NLead{}, sign, base, ds, us, saw, why}), 10, [], False{}, True{}, ""},
                    False{}, gd.fput(True{}, '0', T.FlStart{})), True{},
                Equal.cong(Char, Bool, xx => gd.nm(T.Num{T.NZero{}, T.num.sign.of(T.Num{T.NLead{}, sign, base, ds, us,
                  saw, why}), 10, [], False{}, True{}, ""}, False{}, gd.fput(True{}, xx, T.FlStart{})), cc, '0',
                    Eq.char_eq_true(cc, '0', eZ)),
                {==})
            case False{}:
              match D:
                case True{}:
                  gd.n.digit(T.dig.ok(T.dig.val(cc), base), cc, T.NDig{}, sign, base, ds, gd.fput(True{}, cc,
                    T.FlStart{}), ed,
                    Equal.trans(Bool, gd.nk(T.NDig{}, False{}, True{}, gd.fput(True{}, cc, T.FlStart{})),
                      gd.nk(T.NDig{}, False{}, True{}, T.FlInt{}), True{},
                    Equal.cong(T.Fl, Bool, ff => gd.nk(T.NDig{}, False{}, True{}, ff), gd.fput(True{}, cc,
                      T.FlStart{}), T.FlInt{}, Equal.trans(T.Fl, gd.fput(True{}, cc, T.FlStart{}), Bool.pick(T.Fl,
                        Char.is_eq(cc, '0'), T.FlZero{}, T.FlInt{}), T.FlInt{}, gd.dst.lead(cc, eD), Equal.cong(Bool,
                          T.Fl, bb => Bool.pick(T.Fl, bb, T.FlZero{}, T.FlInt{}), Char.is_eq(cc, '0'), False{}, eZ))),
                            {==}))
                case False{}:
                  {==}

# the scan and the automaton after one character, in NZero
def gd.nd.NZero(
  X: Bool,
  O: Bool,
  B: Bool,
  DOT: Bool,
  E1: Bool,
  E2: Bool,
  +sign: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String,
  +cc: Char,
  +eX: {Char.is_eq(cc, 'x') == X : Bool},
  +eO: {Char.is_eq(cc, 'o') == O : Bool},
  +eB: {Char.is_eq(cc, 'b') == B : Bool},
  +eDOT: {Char.is_eq(cc, '.') == DOT : Bool},
  +eE1: {Char.is_eq(cc, 'e') == E1 : Bool},
  +eE2: {Char.is_eq(cc, 'E') == E2 : Bool},
  _ed: {gd.d10(ds) == True{} : Bool}
) -> {gd.nm(T.num.zero.go(X, O, B, DOT, E1, E2, T.Num{T.NZero{}, sign, base, ds, us, saw, why}, cc), False{},
  gd.fput(False{}, cc, T.FlZero{})) == True{} : Bool}:
  match X:
    case True{}:
      Equal.trans(Bool, gd.nm(T.num.base(T.Num{T.NZero{}, sign, base, ds, us, saw, why}, 16), False{},
        gd.fput(False{}, cc, T.FlZero{})), gd.nm(T.num.base(T.Num{T.NZero{}, sign, base, ds, us, saw, why}, 16),
          False{}, gd.fput(False{}, 'x', T.FlZero{})), True{},
        Equal.cong(Char, Bool, xx => gd.nm(T.num.base(T.Num{T.NZero{}, sign, base, ds, us, saw, why}, 16), False{},
          gd.fput(False{}, xx, T.FlZero{})), cc, 'x', Eq.char_eq_true(cc, 'x', eX)),
        {==})
    case False{}:
      match O:
        case True{}:
          Equal.trans(Bool, gd.nm(T.num.base(T.Num{T.NZero{}, sign, base, ds, us, saw, why}, 8), False{},
            gd.fput(False{}, cc, T.FlZero{})), gd.nm(T.num.base(T.Num{T.NZero{}, sign, base, ds, us, saw, why}, 8),
              False{}, gd.fput(False{}, 'o', T.FlZero{})), True{},
            Equal.cong(Char, Bool, xx => gd.nm(T.num.base(T.Num{T.NZero{}, sign, base, ds, us, saw, why}, 8), False{},
              gd.fput(False{}, xx, T.FlZero{})), cc, 'o', Eq.char_eq_true(cc, 'o', eO)),
            {==})
        case False{}:
          match B:
            case True{}:
              Equal.trans(Bool, gd.nm(T.num.base(T.Num{T.NZero{}, sign, base, ds, us, saw, why}, 2), False{},
                gd.fput(False{}, cc, T.FlZero{})), gd.nm(T.num.base(T.Num{T.NZero{}, sign, base, ds, us, saw, why},
                  2), False{}, gd.fput(False{}, 'b', T.FlZero{})), True{},
                Equal.cong(Char, Bool, xx => gd.nm(T.num.base(T.Num{T.NZero{}, sign, base, ds, us, saw, why}, 2),
                  False{}, gd.fput(False{}, xx, T.FlZero{})), cc, 'b', Eq.char_eq_true(cc, 'b', eB)),
                {==})
            case False{}:
              match DOT:
                case True{}:
                  Equal.trans(Bool, gd.nm(T.num.dot(T.Num{T.NZero{}, sign, base, ds, us, saw, why}), False{},
                    gd.fput(False{}, cc, T.FlZero{})), gd.nm(T.num.dot(T.Num{T.NZero{}, sign, base, ds, us, saw,
                      why}), False{}, gd.fput(False{}, '.', T.FlZero{})), True{},
                    Equal.cong(Char, Bool, xx => gd.nm(T.num.dot(T.Num{T.NZero{}, sign, base, ds, us, saw, why}),
                      False{}, gd.fput(False{}, xx, T.FlZero{})), cc, '.', Eq.char_eq_true(cc, '.', eDOT)),
                    gd.n.dot(Bool.and(saw, Bool.not(us)), sign, gd.fput(False{}, '.', T.FlZero{}),
                      gd.ifok.any(Bool.and(saw, Bool.not(us)), gd.nk(T.NFrac{}, False{}, False{}, gd.fput(False{},
                        '.', T.FlZero{})), {==})))
                case False{}:
                  match E1:
                    case True{}:
                      Equal.trans(Bool, gd.nm(T.num.exp(T.Num{T.NZero{}, sign, base, ds, us, saw, why}), False{},
                        gd.fput(False{}, cc, T.FlZero{})), gd.nm(T.num.exp(T.Num{T.NZero{}, sign, base, ds, us, saw,
                          why}), False{}, gd.fput(False{}, 'e', T.FlZero{})), True{},
                        Equal.cong(Char, Bool, xx => gd.nm(T.num.exp(T.Num{T.NZero{}, sign, base, ds, us, saw, why}),
                          False{}, gd.fput(False{}, xx, T.FlZero{})), cc, 'e', Eq.char_eq_true(cc, 'e', eE1)),
                        gd.n.exp(Bool.and(saw, Bool.not(us)), sign, gd.fput(False{}, 'e', T.FlZero{}),
                          gd.ifok.any(Bool.and(saw, Bool.not(us)), gd.nk(T.NExp{}, False{}, False{}, gd.fput(False{},
                            'e', T.FlZero{})), {==})))
                    case False{}:
                      match E2:
                        case True{}:
                          Equal.trans(Bool, gd.nm(T.num.exp(T.Num{T.NZero{}, sign, base, ds, us, saw, why}), False{},
                            gd.fput(False{}, cc, T.FlZero{})), gd.nm(T.num.exp(T.Num{T.NZero{}, sign, base, ds, us,
                              saw, why}), False{}, gd.fput(False{}, 'E', T.FlZero{})), True{},
                            Equal.cong(Char, Bool, xx => gd.nm(T.num.exp(T.Num{T.NZero{}, sign, base, ds, us, saw,
                              why}), False{}, gd.fput(False{}, xx, T.FlZero{})), cc, 'E', Eq.char_eq_true(cc, 'E',
                                eE2)),
                            gd.n.exp(Bool.and(saw, Bool.not(us)), sign, gd.fput(False{}, 'E', T.FlZero{}),
                              gd.ifok.any(Bool.and(saw, Bool.not(us)), gd.nk(T.NExp{}, False{}, False{},
                                gd.fput(False{}, 'E', T.FlZero{})), {==})))
                        case False{}:
                          {==}

# the scan and the automaton after one character, in NDig
def gd.nd.NDig(
  D: Bool,
  U: Bool,
  DOT: Bool,
  E1: Bool,
  E2: Bool,
  +sign: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String,
  +cc: Char,
  +eD: {Char.is_digit(cc) == D : Bool},
  +eU: {Char.is_eq(cc, '_') == U : Bool},
  +eDOT: {Char.is_eq(cc, '.') == DOT : Bool},
  +eE1: {Char.is_eq(cc, 'e') == E1 : Bool},
  +eE2: {Char.is_eq(cc, 'E') == E2 : Bool},
  +ed: {gd.d10(ds) == True{} : Bool}
) -> {gd.nm(T.num.digs.go(D, U, DOT, E1, E2, T.Num{T.NDig{}, sign, base, ds, us, saw, why}, cc), False{},
  gd.fput(False{}, cc, T.FlInt{})) == True{} : Bool}:
  match D:
    case True{}:
      gd.n.digit(T.dig.ok(T.dig.val(cc), base), cc, T.NDig{}, sign, base, ds, gd.fput(False{}, cc, T.FlInt{}), ed,
        Equal.trans(Bool, gd.nk(T.NDig{}, False{}, True{}, gd.fput(False{}, cc, T.FlInt{})), gd.nk(T.NDig{}, False{},
          True{}, T.FlInt{}), True{},
        Equal.cong(T.Fl, Bool, ff => gd.nk(T.NDig{}, False{}, True{}, ff), gd.fput(False{}, cc, T.FlInt{}), T.FlInt{},
          gd.dst.int(cc, eD)), {==}))
    case False{}:
      match U:
        case True{}:
          Equal.trans(Bool, gd.nm(T.num.us(T.Num{T.NDig{}, sign, base, ds, us, saw, why}), False{}, gd.fput(False{},
            cc, T.FlInt{})), gd.nm(T.num.us(T.Num{T.NDig{}, sign, base, ds, us, saw, why}), False{}, gd.fput(False{},
              '_', T.FlInt{})), True{},
            Equal.cong(Char, Bool, xx => gd.nm(T.num.us(T.Num{T.NDig{}, sign, base, ds, us, saw, why}), False{},
              gd.fput(False{}, xx, T.FlInt{})), cc, '_', Eq.char_eq_true(cc, '_', eU)),
            gd.n.us(Bool.and(saw, Bool.not(us)), T.NDig{}, sign, base, ds, why, gd.fput(False{}, '_', T.FlInt{}), ed,
              gd.ifok.any(Bool.and(saw, Bool.not(us)), gd.nk(T.NDig{}, False{}, True{}, gd.fput(False{}, '_',
                T.FlInt{})), {==})))
        case False{}:
          match DOT:
            case True{}:
              Equal.trans(Bool, gd.nm(T.num.dot(T.Num{T.NDig{}, sign, base, ds, us, saw, why}), False{},
                gd.fput(False{}, cc, T.FlInt{})), gd.nm(T.num.dot(T.Num{T.NDig{}, sign, base, ds, us, saw, why}),
                  False{}, gd.fput(False{}, '.', T.FlInt{})), True{},
                Equal.cong(Char, Bool, xx => gd.nm(T.num.dot(T.Num{T.NDig{}, sign, base, ds, us, saw, why}), False{},
                  gd.fput(False{}, xx, T.FlInt{})), cc, '.', Eq.char_eq_true(cc, '.', eDOT)),
                gd.n.dot(Bool.and(saw, Bool.not(us)), sign, gd.fput(False{}, '.', T.FlInt{}),
                  gd.ifok.any(Bool.and(saw, Bool.not(us)), gd.nk(T.NFrac{}, False{}, False{}, gd.fput(False{}, '.',
                    T.FlInt{})), {==})))
            case False{}:
              match E1:
                case True{}:
                  Equal.trans(Bool, gd.nm(T.num.exp(T.Num{T.NDig{}, sign, base, ds, us, saw, why}), False{},
                    gd.fput(False{}, cc, T.FlInt{})), gd.nm(T.num.exp(T.Num{T.NDig{}, sign, base, ds, us, saw, why}),
                      False{}, gd.fput(False{}, 'e', T.FlInt{})), True{},
                    Equal.cong(Char, Bool, xx => gd.nm(T.num.exp(T.Num{T.NDig{}, sign, base, ds, us, saw, why}),
                      False{}, gd.fput(False{}, xx, T.FlInt{})), cc, 'e', Eq.char_eq_true(cc, 'e', eE1)),
                    gd.n.exp(Bool.and(saw, Bool.not(us)), sign, gd.fput(False{}, 'e', T.FlInt{}),
                      gd.ifok.any(Bool.and(saw, Bool.not(us)), gd.nk(T.NExp{}, False{}, False{}, gd.fput(False{}, 'e',
                        T.FlInt{})), {==})))
                case False{}:
                  match E2:
                    case True{}:
                      Equal.trans(Bool, gd.nm(T.num.exp(T.Num{T.NDig{}, sign, base, ds, us, saw, why}), False{},
                        gd.fput(False{}, cc, T.FlInt{})), gd.nm(T.num.exp(T.Num{T.NDig{}, sign, base, ds, us, saw,
                          why}), False{}, gd.fput(False{}, 'E', T.FlInt{})), True{},
                        Equal.cong(Char, Bool, xx => gd.nm(T.num.exp(T.Num{T.NDig{}, sign, base, ds, us, saw, why}),
                          False{}, gd.fput(False{}, xx, T.FlInt{})), cc, 'E', Eq.char_eq_true(cc, 'E', eE2)),
                        gd.n.exp(Bool.and(saw, Bool.not(us)), sign, gd.fput(False{}, 'E', T.FlInt{}),
                          gd.ifok.any(Bool.and(saw, Bool.not(us)), gd.nk(T.NExp{}, False{}, False{}, gd.fput(False{},
                            'E', T.FlInt{})), {==})))
                    case False{}:
                      {==}

# the scan after one character, in NBase: an underscore or a digit of the base
def gd.nd.NBase(
  U: Bool,
  +sign: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String,
  +cc: Char,
  +flx: T.Fl,
  +ed: {gd.d10(ds) == True{} : Bool}
) -> {gd.nm(T.num.based.go(U, T.Num{T.NBase{}, sign, base, ds, us, saw, why}, cc), False{}, flx) == True{} : Bool}:
  match U:
    case True{}:
      gd.n.us(Bool.and(saw, Bool.not(us)), T.NBase{}, sign, base, ds, why, flx, ed,
        gd.ifok.any(Bool.and(saw, Bool.not(us)), True{}, {==}))
    case False{}:
      gd.n.digit(T.dig.ok(T.dig.val(cc), base), cc, T.NBase{}, sign, base, ds, flx, ed, {==})

# the scan and the automaton after one character, in NFrac
def gd.nd.NFracT(
  D: Bool,
  U: Bool,
  E1: Bool,
  E2: Bool,
  +sign: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +why: String,
  +cc: Char,
  +eD: {Char.is_digit(cc) == D : Bool},
  +eU: {Char.is_eq(cc, '_') == U : Bool},
  +eE1: {Char.is_eq(cc, 'e') == E1 : Bool},
  +eE2: {Char.is_eq(cc, 'E') == E2 : Bool},
  +ed: {gd.d10(ds) == True{} : Bool}
) -> {gd.nm(T.num.frac.go(D, U, E1, E2, T.Num{T.NFrac{}, sign, base, ds, us, True{}, why}, cc), False{},
  gd.fput(False{}, cc, T.FlFrac{})) == True{} : Bool}:
  match D:
    case True{}:
      gd.n.digit(T.dig.ok(T.dig.val(cc), base), cc, T.NFrac{}, sign, base, ds, gd.fput(False{}, cc, T.FlFrac{}), ed,
        Equal.trans(Bool, gd.nk(T.NFrac{}, False{}, True{}, gd.fput(False{}, cc, T.FlFrac{})), gd.nk(T.NFrac{},
          False{}, True{}, T.FlFrac{}), True{},
        Equal.cong(T.Fl, Bool, ff => gd.nk(T.NFrac{}, False{}, True{}, ff), gd.fput(False{}, cc, T.FlFrac{}),
          T.FlFrac{}, gd.dst.frac(cc, eD)), {==}))
    case False{}:
      match U:
        case True{}:
          Equal.trans(Bool, gd.nm(T.num.us(T.Num{T.NFrac{}, sign, base, ds, us, True{}, why}), False{},
            gd.fput(False{}, cc, T.FlFrac{})), gd.nm(T.num.us(T.Num{T.NFrac{}, sign, base, ds, us, True{}, why}),
              False{}, gd.fput(False{}, '_', T.FlFrac{})), True{},
            Equal.cong(Char, Bool, xx => gd.nm(T.num.us(T.Num{T.NFrac{}, sign, base, ds, us, True{}, why}), False{},
              gd.fput(False{}, xx, T.FlFrac{})), cc, '_', Eq.char_eq_true(cc, '_', eU)),
            gd.n.us(Bool.and(True{}, Bool.not(us)), T.NFrac{}, sign, base, ds, why, gd.fput(False{}, '_', T.FlFrac{}),
              ed, gd.ifok.any(Bool.and(True{}, Bool.not(us)), gd.nk(T.NFrac{}, False{}, True{}, gd.fput(False{}, '_',
                T.FlFrac{})), {==})))
        case False{}:
          match E1:
            case True{}:
              Equal.trans(Bool, gd.nm(T.num.exp(T.Num{T.NFrac{}, sign, base, ds, us, True{}, why}), False{},
                gd.fput(False{}, cc, T.FlFrac{})), gd.nm(T.num.exp(T.Num{T.NFrac{}, sign, base, ds, us, True{}, why}),
                  False{}, gd.fput(False{}, 'e', T.FlFrac{})), True{},
                Equal.cong(Char, Bool, xx => gd.nm(T.num.exp(T.Num{T.NFrac{}, sign, base, ds, us, True{}, why}),
                  False{}, gd.fput(False{}, xx, T.FlFrac{})), cc, 'e', Eq.char_eq_true(cc, 'e', eE1)),
                gd.n.exp(Bool.and(True{}, Bool.not(us)), sign, gd.fput(False{}, 'e', T.FlFrac{}),
                  gd.ifok.any(Bool.and(True{}, Bool.not(us)), gd.nk(T.NExp{}, False{}, False{}, gd.fput(False{}, 'e',
                    T.FlFrac{})), {==})))
            case False{}:
              match E2:
                case True{}:
                  Equal.trans(Bool, gd.nm(T.num.exp(T.Num{T.NFrac{}, sign, base, ds, us, True{}, why}), False{},
                    gd.fput(False{}, cc, T.FlFrac{})), gd.nm(T.num.exp(T.Num{T.NFrac{}, sign, base, ds, us, True{},
                      why}), False{}, gd.fput(False{}, 'E', T.FlFrac{})), True{},
                    Equal.cong(Char, Bool, xx => gd.nm(T.num.exp(T.Num{T.NFrac{}, sign, base, ds, us, True{}, why}),
                      False{}, gd.fput(False{}, xx, T.FlFrac{})), cc, 'E', Eq.char_eq_true(cc, 'E', eE2)),
                    gd.n.exp(Bool.and(True{}, Bool.not(us)), sign, gd.fput(False{}, 'E', T.FlFrac{}),
                      gd.ifok.any(Bool.and(True{}, Bool.not(us)), gd.nk(T.NExp{}, False{}, False{}, gd.fput(False{},
                        'E', T.FlFrac{})), {==})))
                case False{}:
                  {==}

# the scan and the automaton after one character, in NFrac
def gd.nd.NFracF(
  D: Bool,
  U: Bool,
  E1: Bool,
  E2: Bool,
  +sign: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +why: String,
  +cc: Char,
  +eD: {Char.is_digit(cc) == D : Bool},
  +eU: {Char.is_eq(cc, '_') == U : Bool},
  +eE1: {Char.is_eq(cc, 'e') == E1 : Bool},
  +eE2: {Char.is_eq(cc, 'E') == E2 : Bool},
  +ed: {gd.d10(ds) == True{} : Bool}
) -> {gd.nm(T.num.frac.go(D, U, E1, E2, T.Num{T.NFrac{}, sign, base, ds, us, False{}, why}, cc), False{},
  gd.fput(False{}, cc, T.FlDot{})) == True{} : Bool}:
  match D:
    case True{}:
      gd.n.digit(T.dig.ok(T.dig.val(cc), base), cc, T.NFrac{}, sign, base, ds, gd.fput(False{}, cc, T.FlDot{}), ed,
        Equal.trans(Bool, gd.nk(T.NFrac{}, False{}, True{}, gd.fput(False{}, cc, T.FlDot{})), gd.nk(T.NFrac{},
          False{}, True{}, T.FlFrac{}), True{},
        Equal.cong(T.Fl, Bool, ff => gd.nk(T.NFrac{}, False{}, True{}, ff), gd.fput(False{}, cc, T.FlDot{}),
          T.FlFrac{}, gd.dst.dot(cc, eD)), {==}))
    case False{}:
      match U:
        case True{}:
          Equal.trans(Bool, gd.nm(T.num.us(T.Num{T.NFrac{}, sign, base, ds, us, False{}, why}), False{},
            gd.fput(False{}, cc, T.FlDot{})), gd.nm(T.num.us(T.Num{T.NFrac{}, sign, base, ds, us, False{}, why}),
              False{}, gd.fput(False{}, '_', T.FlDot{})), True{},
            Equal.cong(Char, Bool, xx => gd.nm(T.num.us(T.Num{T.NFrac{}, sign, base, ds, us, False{}, why}), False{},
              gd.fput(False{}, xx, T.FlDot{})), cc, '_', Eq.char_eq_true(cc, '_', eU)),
            gd.n.us(Bool.and(False{}, Bool.not(us)), T.NFrac{}, sign, base, ds, why, gd.fput(False{}, '_', T.FlDot{}),
              ed, {==}))
        case False{}:
          match E1:
            case True{}:
              Equal.trans(Bool, gd.nm(T.num.exp(T.Num{T.NFrac{}, sign, base, ds, us, False{}, why}), False{},
                gd.fput(False{}, cc, T.FlDot{})), gd.nm(T.num.exp(T.Num{T.NFrac{}, sign, base, ds, us, False{}, why}),
                  False{}, gd.fput(False{}, 'e', T.FlDot{})), True{},
                Equal.cong(Char, Bool, xx => gd.nm(T.num.exp(T.Num{T.NFrac{}, sign, base, ds, us, False{}, why}),
                  False{}, gd.fput(False{}, xx, T.FlDot{})), cc, 'e', Eq.char_eq_true(cc, 'e', eE1)),
                gd.n.exp(Bool.and(False{}, Bool.not(us)), sign, gd.fput(False{}, 'e', T.FlDot{}), {==}))
            case False{}:
              match E2:
                case True{}:
                  Equal.trans(Bool, gd.nm(T.num.exp(T.Num{T.NFrac{}, sign, base, ds, us, False{}, why}), False{},
                    gd.fput(False{}, cc, T.FlDot{})), gd.nm(T.num.exp(T.Num{T.NFrac{}, sign, base, ds, us, False{},
                      why}), False{}, gd.fput(False{}, 'E', T.FlDot{})), True{},
                    Equal.cong(Char, Bool, xx => gd.nm(T.num.exp(T.Num{T.NFrac{}, sign, base, ds, us, False{}, why}),
                      False{}, gd.fput(False{}, xx, T.FlDot{})), cc, 'E', Eq.char_eq_true(cc, 'E', eE2)),
                    gd.n.exp(Bool.and(False{}, Bool.not(us)), sign, gd.fput(False{}, 'E', T.FlDot{}), {==}))
                case False{}:
                  {==}

# the scan and the automaton after one character, in NExp
def gd.nd.NExp(
  P: Bool,
  M: Bool,
  D: Bool,
  +sign: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String,
  +cc: Char,
  +eP: {Char.is_eq(cc, '+') == P : Bool},
  +eM: {Char.is_eq(cc, '-') == M : Bool},
  +eD: {Char.is_digit(cc) == D : Bool},
  +ed: {gd.d10(ds) == True{} : Bool}
) -> {gd.nm(T.num.expon.go(P, M, D, T.Num{T.NExp{}, sign, base, ds, us, saw, why}, cc), False{}, gd.fput(False{}, cc,
  T.FlE{})) == True{} : Bool}:
  match P:
    case True{}:
      Equal.trans(Bool, gd.nm(T.num.exp.sign(T.Num{T.NExp{}, sign, base, ds, us, saw, why}), False{}, gd.fput(False{},
        cc, T.FlE{})), gd.nm(T.num.exp.sign(T.Num{T.NExp{}, sign, base, ds, us, saw, why}), False{}, gd.fput(False{},
          '+', T.FlE{})), True{},
        Equal.cong(Char, Bool, xx => gd.nm(T.num.exp.sign(T.Num{T.NExp{}, sign, base, ds, us, saw, why}), False{},
          gd.fput(False{}, xx, T.FlE{})), cc, '+', Eq.char_eq_true(cc, '+', eP)),
        {==})
    case False{}:
      match M:
        case True{}:
          Equal.trans(Bool, gd.nm(T.num.exp.sign(T.Num{T.NExp{}, sign, base, ds, us, saw, why}), False{},
            gd.fput(False{}, cc, T.FlE{})), gd.nm(T.num.exp.sign(T.Num{T.NExp{}, sign, base, ds, us, saw, why}),
              False{}, gd.fput(False{}, '-', T.FlE{})), True{},
            Equal.cong(Char, Bool, xx => gd.nm(T.num.exp.sign(T.Num{T.NExp{}, sign, base, ds, us, saw, why}), False{},
              gd.fput(False{}, xx, T.FlE{})), cc, '-', Eq.char_eq_true(cc, '-', eM)),
            {==})
        case False{}:
          match D:
            case True{}:
              gd.n.digit(T.dig.ok(T.dig.val(cc), base), cc, T.NEDig{}, sign, base, ds, gd.fput(False{}, cc, T.FlE{}),
                ed,
                Equal.trans(Bool, gd.nk(T.NEDig{}, False{}, True{}, gd.fput(False{}, cc, T.FlE{})), gd.nk(T.NEDig{},
                  False{}, True{}, T.FlExp{}), True{},
                Equal.cong(T.Fl, Bool, ff => gd.nk(T.NEDig{}, False{}, True{}, ff), gd.fput(False{}, cc, T.FlE{}),
                  T.FlExp{}, gd.dst.e(cc, eD)), {==}))
            case False{}:
              {==}

# the scan and the automaton after one character, in NEDig
def gd.nd.NEDigT(
  D: Bool,
  U: Bool,
  +sign: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +why: String,
  +cc: Char,
  +eD: {Char.is_digit(cc) == D : Bool},
  +eU: {Char.is_eq(cc, '_') == U : Bool},
  +ed: {gd.d10(ds) == True{} : Bool}
) -> {gd.nm(T.num.edig.go(D, U, T.Num{T.NEDig{}, sign, base, ds, us, True{}, why}, cc), False{}, gd.fput(False{}, cc,
  T.FlExp{})) == True{} : Bool}:
  match D:
    case True{}:
      gd.n.digit(T.dig.ok(T.dig.val(cc), base), cc, T.NEDig{}, sign, base, ds, gd.fput(False{}, cc, T.FlExp{}), ed,
        Equal.trans(Bool, gd.nk(T.NEDig{}, False{}, True{}, gd.fput(False{}, cc, T.FlExp{})), gd.nk(T.NEDig{},
          False{}, True{}, T.FlExp{}), True{},
        Equal.cong(T.Fl, Bool, ff => gd.nk(T.NEDig{}, False{}, True{}, ff), gd.fput(False{}, cc, T.FlExp{}),
          T.FlExp{}, gd.dst.exp(cc, eD)), {==}))
    case False{}:
      match U:
        case True{}:
          Equal.trans(Bool, gd.nm(T.num.us(T.Num{T.NEDig{}, sign, base, ds, us, True{}, why}), False{},
            gd.fput(False{}, cc, T.FlExp{})), gd.nm(T.num.us(T.Num{T.NEDig{}, sign, base, ds, us, True{}, why}),
              False{}, gd.fput(False{}, '_', T.FlExp{})), True{},
            Equal.cong(Char, Bool, xx => gd.nm(T.num.us(T.Num{T.NEDig{}, sign, base, ds, us, True{}, why}), False{},
              gd.fput(False{}, xx, T.FlExp{})), cc, '_', Eq.char_eq_true(cc, '_', eU)),
            gd.n.us(Bool.and(True{}, Bool.not(us)), T.NEDig{}, sign, base, ds, why, gd.fput(False{}, '_', T.FlExp{}),
              ed, gd.ifok.any(Bool.and(True{}, Bool.not(us)), gd.nk(T.NEDig{}, False{}, True{}, gd.fput(False{}, '_',
                T.FlExp{})), {==})))
        case False{}:
          {==}

# the scan and the automaton after one character, in NEDig
def gd.nd.NEDigF(
  D: Bool,
  U: Bool,
  +sign: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +why: String,
  +cc: Char,
  +eD: {Char.is_digit(cc) == D : Bool},
  +eU: {Char.is_eq(cc, '_') == U : Bool},
  +ed: {gd.d10(ds) == True{} : Bool}
) -> {gd.nm(T.num.edig.go(D, U, T.Num{T.NEDig{}, sign, base, ds, us, False{}, why}, cc), False{}, gd.fput(False{}, cc,
  T.FlESign{})) == True{} : Bool}:
  match D:
    case True{}:
      gd.n.digit(T.dig.ok(T.dig.val(cc), base), cc, T.NEDig{}, sign, base, ds, gd.fput(False{}, cc, T.FlESign{}), ed,
        Equal.trans(Bool, gd.nk(T.NEDig{}, False{}, True{}, gd.fput(False{}, cc, T.FlESign{})), gd.nk(T.NEDig{},
          False{}, True{}, T.FlExp{}), True{},
        Equal.cong(T.Fl, Bool, ff => gd.nk(T.NEDig{}, False{}, True{}, ff), gd.fput(False{}, cc, T.FlESign{}),
          T.FlExp{}, gd.dst.esign(cc, eD)), {==}))
    case False{}:
      match U:
        case True{}:
          Equal.trans(Bool, gd.nm(T.num.us(T.Num{T.NEDig{}, sign, base, ds, us, False{}, why}), False{},
            gd.fput(False{}, cc, T.FlESign{})), gd.nm(T.num.us(T.Num{T.NEDig{}, sign, base, ds, us, False{}, why}),
              False{}, gd.fput(False{}, '_', T.FlESign{})), True{},
            Equal.cong(Char, Bool, xx => gd.nm(T.num.us(T.Num{T.NEDig{}, sign, base, ds, us, False{}, why}), False{},
              gd.fput(False{}, xx, T.FlESign{})), cc, '_', Eq.char_eq_true(cc, '_', eU)),
            gd.n.us(Bool.and(False{}, Bool.not(us)), T.NEDig{}, sign, base, ds, why, gd.fput(False{}, '_',
              T.FlESign{}), ed, {==}))
        case False{}:
          {==}

# the scan after one character, in NSign: a second sign fails, an underscore
# fails, and any other character is read as a numeral's first
def gd.nd.NSign(
  TW: Bool,
  U: Bool,
  +sign: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String,
  +cc: Char,
  +etw: {Bool.or(Char.is_eq(cc, '+'), Char.is_eq(cc, '-')) == TW : Bool},
  +eU: {Char.is_eq(cc, '_') == U : Bool},
  _ed: {gd.d10(ds) == True{} : Bool}
) -> {gd.nm(T.num.after.sign.go(TW, T.num.sign.of(T.Num{T.NSign{}, sign, base, ds, us, saw, why}), cc), False{},
  gd.fput(False{}, cc, T.FlStart{})) == True{} : Bool}:
  match TW:
    case True{}:
      {==}
    case False{}:
      match U:
        case True{}:
          Equal.trans(Bool, gd.nm(T.num.after.sign.go(False{}, T.num.sign.of(T.Num{T.NSign{}, sign, base, ds, us, saw,
            why}), cc), False{}, gd.fput(False{}, cc, T.FlStart{})),
            gd.nm(T.num.after.sign.go(False{}, T.num.sign.of(T.Num{T.NSign{}, sign, base, ds, us, saw, why}), '_'),
              False{}, gd.fput(False{}, '_', T.FlStart{})), True{},
            Equal.cong(Char, Bool, xx => gd.nm(T.num.after.sign.go(False{}, T.num.sign.of(T.Num{T.NSign{}, sign, base,
              ds, us, saw, why}), xx), False{}, gd.fput(False{}, xx, T.FlStart{})), cc,
              '_', Eq.char_eq_true(cc, '_', eU)),
            {==})
        case False{}:
          Equal.trans(Bool, gd.nm(T.num.lead(T.Num{T.NLead{}, sign, 10, [], False{}, False{}, ""}, cc), False{},
            gd.fput(False{}, cc, T.FlStart{})), gd.nm(T.num.lead(T.Num{T.NLead{}, sign, 10, [], False{}, False{}, ""},
              cc), False{}, gd.fput(True{}, cc, T.FlStart{})), True{},
            Equal.cong(T.Fl, Bool, ff => gd.nm(T.num.lead(T.Num{T.NLead{}, sign, 10, [], False{}, False{}, ""}, cc),
              False{}, ff), gd.fput(False{}, cc, T.FlStart{}), gd.fput(True{}, cc, T.FlStart{}),
              Equal.trans(T.Fl, gd.fput(False{}, cc, T.FlStart{}), T.wf.flo.step(T.FlStart{}, cc), gd.fput(True{}, cc,
                T.FlStart{}),
                Equal.cong(Bool, T.Fl, bb => gd.fsel(bb, T.FlStart{}, T.wf.flo.step(T.FlStart{}, cc)), Char.is_eq(cc,
                  '_'), False{}, eU),
                Equal.sym(T.Fl, gd.fput(True{}, cc, T.FlStart{}), T.wf.flo.step(T.FlStart{}, cc), Equal.cong(Bool,
                  T.Fl, bb => gd.fsel(bb, T.FlStart{}, T.wf.flo.step(T.FlStart{}, cc)),
                  Bool.or(Char.is_eq(cc, '+'), Char.is_eq(cc, '-')), False{}, etw)))),
            gd.nd.NLead(Char.is_eq(cc, '+'), Char.is_eq(cc, '-'), Char.is_eq(cc, '0'), Char.is_digit(cc), sign, 10, [],
              False{}, False{}, "", cc, {==}, {==}, {==}, {==}, {==}))

# the scan and the automaton in NLead: the one pair of states that agree
def gd.nx.NLead(
  lead: Bool,
  fl: T.Fl,
  +sign: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String,
  +cc: Char,
  +e: {Bool.and(gd.d10(ds), gd.nk(T.NLead{}, lead, saw, fl)) == True{} : Bool}
) -> {gd.nm(T.num.on(T.NLead{}, T.Num{T.NLead{}, sign, base, ds, us, saw, why}, cc), False{}, gd.fput(lead, cc,
  fl)) == True{} : Bool}:
  match lead:
    case True{}:
      match fl:
        case T.FlStart{}:
          gd.nd.NLead(Char.is_eq(cc, '+'), Char.is_eq(cc, '-'), Char.is_eq(cc, '0'), Char.is_digit(cc), sign, base,
            ds, us, saw, why, cc, {==}, {==}, {==}, {==}, gd.l(gd.d10(ds), gd.nk(T.NLead{}, True{}, saw, T.FlStart{}),
              e))
        case T.FlZero{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NLead{}, T.Num{T.NLead{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlZero{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NLead{}, True{}, saw, T.FlZero{}), e))
        case T.FlInt{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NLead{}, T.Num{T.NLead{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlInt{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NLead{}, True{}, saw, T.FlInt{}), e))
        case T.FlDot{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NLead{}, T.Num{T.NLead{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlDot{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NLead{}, True{}, saw, T.FlDot{}), e))
        case T.FlFrac{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NLead{}, T.Num{T.NLead{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlFrac{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NLead{}, True{}, saw, T.FlFrac{}), e))
        case T.FlE{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NLead{}, T.Num{T.NLead{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlE{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NLead{}, True{}, saw, T.FlE{}), e))
        case T.FlESign{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NLead{}, T.Num{T.NLead{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlESign{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NLead{}, True{}, saw, T.FlESign{}), e))
        case T.FlExp{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NLead{}, T.Num{T.NLead{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlExp{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NLead{}, True{}, saw, T.FlExp{}), e))
        case T.FlNo{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NLead{}, T.Num{T.NLead{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlNo{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NLead{}, True{}, saw, T.FlNo{}), e))
    case False{}:
      match fl:
        case T.FlStart{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NLead{}, T.Num{T.NLead{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlStart{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NLead{}, False{}, saw, T.FlStart{}), e))
        case T.FlZero{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NLead{}, T.Num{T.NLead{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlZero{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NLead{}, False{}, saw, T.FlZero{}), e))
        case T.FlInt{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NLead{}, T.Num{T.NLead{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlInt{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NLead{}, False{}, saw, T.FlInt{}), e))
        case T.FlDot{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NLead{}, T.Num{T.NLead{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlDot{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NLead{}, False{}, saw, T.FlDot{}), e))
        case T.FlFrac{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NLead{}, T.Num{T.NLead{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlFrac{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NLead{}, False{}, saw, T.FlFrac{}), e))
        case T.FlE{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NLead{}, T.Num{T.NLead{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlE{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NLead{}, False{}, saw, T.FlE{}), e))
        case T.FlESign{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NLead{}, T.Num{T.NLead{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlESign{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NLead{}, False{}, saw, T.FlESign{}), e))
        case T.FlExp{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NLead{}, T.Num{T.NLead{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlExp{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NLead{}, False{}, saw, T.FlExp{}), e))
        case T.FlNo{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NLead{}, T.Num{T.NLead{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlNo{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NLead{}, False{}, saw, T.FlNo{}), e))

# the scan and the automaton in NSign: the one pair of states that agree
def gd.nx.NSign(
  lead: Bool,
  fl: T.Fl,
  +sign: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String,
  +cc: Char,
  +e: {Bool.and(gd.d10(ds), gd.nk(T.NSign{}, lead, saw, fl)) == True{} : Bool}
) -> {gd.nm(T.num.on(T.NSign{}, T.Num{T.NSign{}, sign, base, ds, us, saw, why}, cc), False{}, gd.fput(lead, cc,
  fl)) == True{} : Bool}:
  match lead:
    case True{}:
      match fl:
        case T.FlStart{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NSign{}, T.Num{T.NSign{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlStart{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NSign{}, True{}, saw, T.FlStart{}), e))
        case T.FlZero{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NSign{}, T.Num{T.NSign{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlZero{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NSign{}, True{}, saw, T.FlZero{}), e))
        case T.FlInt{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NSign{}, T.Num{T.NSign{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlInt{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NSign{}, True{}, saw, T.FlInt{}), e))
        case T.FlDot{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NSign{}, T.Num{T.NSign{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlDot{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NSign{}, True{}, saw, T.FlDot{}), e))
        case T.FlFrac{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NSign{}, T.Num{T.NSign{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlFrac{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NSign{}, True{}, saw, T.FlFrac{}), e))
        case T.FlE{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NSign{}, T.Num{T.NSign{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlE{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NSign{}, True{}, saw, T.FlE{}), e))
        case T.FlESign{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NSign{}, T.Num{T.NSign{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlESign{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NSign{}, True{}, saw, T.FlESign{}), e))
        case T.FlExp{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NSign{}, T.Num{T.NSign{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlExp{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NSign{}, True{}, saw, T.FlExp{}), e))
        case T.FlNo{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NSign{}, T.Num{T.NSign{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlNo{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NSign{}, True{}, saw, T.FlNo{}), e))
    case False{}:
      match fl:
        case T.FlStart{}:
          gd.nd.NSign(Bool.or(Char.is_eq(cc, '+'), Char.is_eq(cc, '-')), Char.is_eq(cc, '_'), sign, base, ds, us, saw,
            why, cc, {==}, {==}, gd.l(gd.d10(ds), gd.nk(T.NSign{}, False{}, saw, T.FlStart{}), e))
        case T.FlZero{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NSign{}, T.Num{T.NSign{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlZero{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NSign{}, False{}, saw, T.FlZero{}), e))
        case T.FlInt{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NSign{}, T.Num{T.NSign{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlInt{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NSign{}, False{}, saw, T.FlInt{}), e))
        case T.FlDot{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NSign{}, T.Num{T.NSign{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlDot{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NSign{}, False{}, saw, T.FlDot{}), e))
        case T.FlFrac{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NSign{}, T.Num{T.NSign{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlFrac{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NSign{}, False{}, saw, T.FlFrac{}), e))
        case T.FlE{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NSign{}, T.Num{T.NSign{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlE{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NSign{}, False{}, saw, T.FlE{}), e))
        case T.FlESign{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NSign{}, T.Num{T.NSign{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlESign{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NSign{}, False{}, saw, T.FlESign{}), e))
        case T.FlExp{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NSign{}, T.Num{T.NSign{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlExp{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NSign{}, False{}, saw, T.FlExp{}), e))
        case T.FlNo{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NSign{}, T.Num{T.NSign{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlNo{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NSign{}, False{}, saw, T.FlNo{}), e))

# the scan and the automaton in NZero: the one pair of states that agree
def gd.nx.NZero(
  lead: Bool,
  fl: T.Fl,
  +sign: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String,
  +cc: Char,
  +e: {Bool.and(gd.d10(ds), gd.nk(T.NZero{}, lead, saw, fl)) == True{} : Bool}
) -> {gd.nm(T.num.on(T.NZero{}, T.Num{T.NZero{}, sign, base, ds, us, saw, why}, cc), False{}, gd.fput(lead, cc,
  fl)) == True{} : Bool}:
  match lead:
    case True{}:
      match fl:
        case T.FlStart{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NZero{}, T.Num{T.NZero{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlStart{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NZero{}, True{}, saw, T.FlStart{}), e))
        case T.FlZero{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NZero{}, T.Num{T.NZero{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlZero{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NZero{}, True{}, saw, T.FlZero{}), e))
        case T.FlInt{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NZero{}, T.Num{T.NZero{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlInt{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NZero{}, True{}, saw, T.FlInt{}), e))
        case T.FlDot{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NZero{}, T.Num{T.NZero{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlDot{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NZero{}, True{}, saw, T.FlDot{}), e))
        case T.FlFrac{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NZero{}, T.Num{T.NZero{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlFrac{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NZero{}, True{}, saw, T.FlFrac{}), e))
        case T.FlE{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NZero{}, T.Num{T.NZero{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlE{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NZero{}, True{}, saw, T.FlE{}), e))
        case T.FlESign{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NZero{}, T.Num{T.NZero{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlESign{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NZero{}, True{}, saw, T.FlESign{}), e))
        case T.FlExp{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NZero{}, T.Num{T.NZero{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlExp{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NZero{}, True{}, saw, T.FlExp{}), e))
        case T.FlNo{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NZero{}, T.Num{T.NZero{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlNo{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NZero{}, True{}, saw, T.FlNo{}), e))
    case False{}:
      match fl:
        case T.FlStart{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NZero{}, T.Num{T.NZero{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlStart{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NZero{}, False{}, saw, T.FlStart{}), e))
        case T.FlZero{}:
          gd.nd.NZero(Char.is_eq(cc, 'x'), Char.is_eq(cc, 'o'), Char.is_eq(cc, 'b'), Char.is_eq(cc, '.'),
            Char.is_eq(cc, 'e'), Char.is_eq(cc, 'E'), sign, base, ds, us, saw, why, cc, {==}, {==}, {==}, {==}, {==},
              {==}, gd.l(gd.d10(ds), gd.nk(T.NZero{}, False{}, saw, T.FlZero{}), e))
        case T.FlInt{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NZero{}, T.Num{T.NZero{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlInt{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NZero{}, False{}, saw, T.FlInt{}), e))
        case T.FlDot{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NZero{}, T.Num{T.NZero{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlDot{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NZero{}, False{}, saw, T.FlDot{}), e))
        case T.FlFrac{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NZero{}, T.Num{T.NZero{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlFrac{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NZero{}, False{}, saw, T.FlFrac{}), e))
        case T.FlE{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NZero{}, T.Num{T.NZero{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlE{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NZero{}, False{}, saw, T.FlE{}), e))
        case T.FlESign{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NZero{}, T.Num{T.NZero{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlESign{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NZero{}, False{}, saw, T.FlESign{}), e))
        case T.FlExp{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NZero{}, T.Num{T.NZero{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlExp{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NZero{}, False{}, saw, T.FlExp{}), e))
        case T.FlNo{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NZero{}, T.Num{T.NZero{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlNo{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NZero{}, False{}, saw, T.FlNo{}), e))

# the scan and the automaton in NDig: the one pair of states that agree
def gd.nx.NDig(
  lead: Bool,
  fl: T.Fl,
  +sign: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String,
  +cc: Char,
  +e: {Bool.and(gd.d10(ds), gd.nk(T.NDig{}, lead, saw, fl)) == True{} : Bool}
) -> {gd.nm(T.num.on(T.NDig{}, T.Num{T.NDig{}, sign, base, ds, us, saw, why}, cc), False{}, gd.fput(lead, cc,
  fl)) == True{} : Bool}:
  match lead:
    case True{}:
      match fl:
        case T.FlStart{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NDig{}, T.Num{T.NDig{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlStart{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NDig{}, True{}, saw, T.FlStart{}), e))
        case T.FlZero{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NDig{}, T.Num{T.NDig{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlZero{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NDig{}, True{}, saw, T.FlZero{}), e))
        case T.FlInt{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NDig{}, T.Num{T.NDig{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlInt{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NDig{}, True{}, saw, T.FlInt{}), e))
        case T.FlDot{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NDig{}, T.Num{T.NDig{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlDot{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NDig{}, True{}, saw, T.FlDot{}), e))
        case T.FlFrac{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NDig{}, T.Num{T.NDig{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlFrac{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NDig{}, True{}, saw, T.FlFrac{}), e))
        case T.FlE{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NDig{}, T.Num{T.NDig{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlE{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NDig{}, True{}, saw, T.FlE{}), e))
        case T.FlESign{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NDig{}, T.Num{T.NDig{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlESign{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NDig{}, True{}, saw, T.FlESign{}), e))
        case T.FlExp{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NDig{}, T.Num{T.NDig{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlExp{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NDig{}, True{}, saw, T.FlExp{}), e))
        case T.FlNo{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NDig{}, T.Num{T.NDig{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlNo{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NDig{}, True{}, saw, T.FlNo{}), e))
    case False{}:
      match fl:
        case T.FlStart{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NDig{}, T.Num{T.NDig{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlStart{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NDig{}, False{}, saw, T.FlStart{}), e))
        case T.FlZero{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NDig{}, T.Num{T.NDig{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlZero{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NDig{}, False{}, saw, T.FlZero{}), e))
        case T.FlInt{}:
          gd.nd.NDig(Char.is_digit(cc), Char.is_eq(cc, '_'), Char.is_eq(cc, '.'), Char.is_eq(cc, 'e'), Char.is_eq(cc,
            'E'), sign, base, ds, us, saw, why, cc, {==}, {==}, {==}, {==}, {==}, gd.l(gd.d10(ds), gd.nk(T.NDig{},
              False{}, saw, T.FlInt{}), e))
        case T.FlDot{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NDig{}, T.Num{T.NDig{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlDot{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NDig{}, False{}, saw, T.FlDot{}), e))
        case T.FlFrac{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NDig{}, T.Num{T.NDig{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlFrac{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NDig{}, False{}, saw, T.FlFrac{}), e))
        case T.FlE{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NDig{}, T.Num{T.NDig{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlE{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NDig{}, False{}, saw, T.FlE{}), e))
        case T.FlESign{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NDig{}, T.Num{T.NDig{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlESign{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NDig{}, False{}, saw, T.FlESign{}), e))
        case T.FlExp{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NDig{}, T.Num{T.NDig{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlExp{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NDig{}, False{}, saw, T.FlExp{}), e))
        case T.FlNo{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NDig{}, T.Num{T.NDig{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlNo{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NDig{}, False{}, saw, T.FlNo{}), e))

# the scan and the automaton in NExp: the one pair of states that agree
def gd.nx.NExp(
  lead: Bool,
  fl: T.Fl,
  +sign: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String,
  +cc: Char,
  +e: {Bool.and(gd.d10(ds), gd.nk(T.NExp{}, lead, saw, fl)) == True{} : Bool}
) -> {gd.nm(T.num.on(T.NExp{}, T.Num{T.NExp{}, sign, base, ds, us, saw, why}, cc), False{}, gd.fput(lead, cc,
  fl)) == True{} : Bool}:
  match lead:
    case True{}:
      match fl:
        case T.FlStart{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NExp{}, T.Num{T.NExp{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlStart{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NExp{}, True{}, saw, T.FlStart{}), e))
        case T.FlZero{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NExp{}, T.Num{T.NExp{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlZero{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NExp{}, True{}, saw, T.FlZero{}), e))
        case T.FlInt{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NExp{}, T.Num{T.NExp{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlInt{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NExp{}, True{}, saw, T.FlInt{}), e))
        case T.FlDot{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NExp{}, T.Num{T.NExp{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlDot{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NExp{}, True{}, saw, T.FlDot{}), e))
        case T.FlFrac{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NExp{}, T.Num{T.NExp{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlFrac{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NExp{}, True{}, saw, T.FlFrac{}), e))
        case T.FlE{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NExp{}, T.Num{T.NExp{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlE{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NExp{}, True{}, saw, T.FlE{}), e))
        case T.FlESign{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NExp{}, T.Num{T.NExp{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlESign{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NExp{}, True{}, saw, T.FlESign{}), e))
        case T.FlExp{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NExp{}, T.Num{T.NExp{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlExp{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NExp{}, True{}, saw, T.FlExp{}), e))
        case T.FlNo{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NExp{}, T.Num{T.NExp{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(True{}, cc, T.FlNo{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NExp{}, True{}, saw, T.FlNo{}), e))
    case False{}:
      match fl:
        case T.FlStart{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NExp{}, T.Num{T.NExp{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlStart{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NExp{}, False{}, saw, T.FlStart{}), e))
        case T.FlZero{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NExp{}, T.Num{T.NExp{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlZero{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NExp{}, False{}, saw, T.FlZero{}), e))
        case T.FlInt{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NExp{}, T.Num{T.NExp{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlInt{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NExp{}, False{}, saw, T.FlInt{}), e))
        case T.FlDot{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NExp{}, T.Num{T.NExp{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlDot{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NExp{}, False{}, saw, T.FlDot{}), e))
        case T.FlFrac{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NExp{}, T.Num{T.NExp{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlFrac{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NExp{}, False{}, saw, T.FlFrac{}), e))
        case T.FlE{}:
          gd.nd.NExp(Char.is_eq(cc, '+'), Char.is_eq(cc, '-'), Char.is_digit(cc), sign, base, ds, us, saw, why, cc,
            {==}, {==}, {==}, gd.l(gd.d10(ds), gd.nk(T.NExp{}, False{}, saw, T.FlE{}), e))
        case T.FlESign{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NExp{}, T.Num{T.NExp{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlESign{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NExp{}, False{}, saw, T.FlESign{}), e))
        case T.FlExp{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NExp{}, T.Num{T.NExp{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlExp{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NExp{}, False{}, saw, T.FlExp{}), e))
        case T.FlNo{}:
          Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NExp{}, T.Num{T.NExp{}, sign, base, ds, us, saw, why}, cc), False{},
            gd.fput(False{}, cc, T.FlNo{})) == True{} : Bool},
            gd.r(gd.d10(ds), gd.nk(T.NExp{}, False{}, saw, T.FlNo{}), e))

# the scan and the automaton in NFrac, by whether a digit was seen
def gd.nx.NFrac(
  lead: Bool,
  saw: Bool,
  fl: T.Fl,
  +sign: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +why: String,
  +cc: Char,
  +e: {Bool.and(gd.d10(ds), gd.nk(T.NFrac{}, lead, saw, fl)) == True{} : Bool}
) -> {gd.nm(T.num.on(T.NFrac{}, T.Num{T.NFrac{}, sign, base, ds, us, saw, why}, cc), False{}, gd.fput(lead, cc,
  fl)) == True{} : Bool}:
  match lead:
    case True{}:
      match saw:
        case True{}:
          match fl:
            case T.FlStart{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NFrac{}, T.Num{T.NFrac{}, sign, base, ds, us, True{}, why}, cc),
                False{}, gd.fput(True{}, cc, T.FlStart{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NFrac{}, True{}, True{}, T.FlStart{}), e))
            case T.FlZero{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NFrac{}, T.Num{T.NFrac{}, sign, base, ds, us, True{}, why}, cc),
                False{}, gd.fput(True{}, cc, T.FlZero{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NFrac{}, True{}, True{}, T.FlZero{}), e))
            case T.FlInt{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NFrac{}, T.Num{T.NFrac{}, sign, base, ds, us, True{}, why}, cc),
                False{}, gd.fput(True{}, cc, T.FlInt{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NFrac{}, True{}, True{}, T.FlInt{}), e))
            case T.FlDot{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NFrac{}, T.Num{T.NFrac{}, sign, base, ds, us, True{}, why}, cc),
                False{}, gd.fput(True{}, cc, T.FlDot{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NFrac{}, True{}, True{}, T.FlDot{}), e))
            case T.FlFrac{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NFrac{}, T.Num{T.NFrac{}, sign, base, ds, us, True{}, why}, cc),
                False{}, gd.fput(True{}, cc, T.FlFrac{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NFrac{}, True{}, True{}, T.FlFrac{}), e))
            case T.FlE{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NFrac{}, T.Num{T.NFrac{}, sign, base, ds, us, True{}, why}, cc),
                False{}, gd.fput(True{}, cc, T.FlE{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NFrac{}, True{}, True{}, T.FlE{}), e))
            case T.FlESign{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NFrac{}, T.Num{T.NFrac{}, sign, base, ds, us, True{}, why}, cc),
                False{}, gd.fput(True{}, cc, T.FlESign{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NFrac{}, True{}, True{}, T.FlESign{}), e))
            case T.FlExp{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NFrac{}, T.Num{T.NFrac{}, sign, base, ds, us, True{}, why}, cc),
                False{}, gd.fput(True{}, cc, T.FlExp{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NFrac{}, True{}, True{}, T.FlExp{}), e))
            case T.FlNo{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NFrac{}, T.Num{T.NFrac{}, sign, base, ds, us, True{}, why}, cc),
                False{}, gd.fput(True{}, cc, T.FlNo{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NFrac{}, True{}, True{}, T.FlNo{}), e))
        case False{}:
          match fl:
            case T.FlStart{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NFrac{}, T.Num{T.NFrac{}, sign, base, ds, us, False{}, why}, cc),
                False{}, gd.fput(True{}, cc, T.FlStart{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NFrac{}, True{}, False{}, T.FlStart{}), e))
            case T.FlZero{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NFrac{}, T.Num{T.NFrac{}, sign, base, ds, us, False{}, why}, cc),
                False{}, gd.fput(True{}, cc, T.FlZero{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NFrac{}, True{}, False{}, T.FlZero{}), e))
            case T.FlInt{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NFrac{}, T.Num{T.NFrac{}, sign, base, ds, us, False{}, why}, cc),
                False{}, gd.fput(True{}, cc, T.FlInt{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NFrac{}, True{}, False{}, T.FlInt{}), e))
            case T.FlDot{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NFrac{}, T.Num{T.NFrac{}, sign, base, ds, us, False{}, why}, cc),
                False{}, gd.fput(True{}, cc, T.FlDot{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NFrac{}, True{}, False{}, T.FlDot{}), e))
            case T.FlFrac{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NFrac{}, T.Num{T.NFrac{}, sign, base, ds, us, False{}, why}, cc),
                False{}, gd.fput(True{}, cc, T.FlFrac{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NFrac{}, True{}, False{}, T.FlFrac{}), e))
            case T.FlE{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NFrac{}, T.Num{T.NFrac{}, sign, base, ds, us, False{}, why}, cc),
                False{}, gd.fput(True{}, cc, T.FlE{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NFrac{}, True{}, False{}, T.FlE{}), e))
            case T.FlESign{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NFrac{}, T.Num{T.NFrac{}, sign, base, ds, us, False{}, why}, cc),
                False{}, gd.fput(True{}, cc, T.FlESign{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NFrac{}, True{}, False{}, T.FlESign{}), e))
            case T.FlExp{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NFrac{}, T.Num{T.NFrac{}, sign, base, ds, us, False{}, why}, cc),
                False{}, gd.fput(True{}, cc, T.FlExp{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NFrac{}, True{}, False{}, T.FlExp{}), e))
            case T.FlNo{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NFrac{}, T.Num{T.NFrac{}, sign, base, ds, us, False{}, why}, cc),
                False{}, gd.fput(True{}, cc, T.FlNo{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NFrac{}, True{}, False{}, T.FlNo{}), e))
    case False{}:
      match saw:
        case True{}:
          match fl:
            case T.FlStart{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NFrac{}, T.Num{T.NFrac{}, sign, base, ds, us, True{}, why}, cc),
                False{}, gd.fput(False{}, cc, T.FlStart{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NFrac{}, False{}, True{}, T.FlStart{}), e))
            case T.FlZero{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NFrac{}, T.Num{T.NFrac{}, sign, base, ds, us, True{}, why}, cc),
                False{}, gd.fput(False{}, cc, T.FlZero{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NFrac{}, False{}, True{}, T.FlZero{}), e))
            case T.FlInt{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NFrac{}, T.Num{T.NFrac{}, sign, base, ds, us, True{}, why}, cc),
                False{}, gd.fput(False{}, cc, T.FlInt{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NFrac{}, False{}, True{}, T.FlInt{}), e))
            case T.FlDot{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NFrac{}, T.Num{T.NFrac{}, sign, base, ds, us, True{}, why}, cc),
                False{}, gd.fput(False{}, cc, T.FlDot{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NFrac{}, False{}, True{}, T.FlDot{}), e))
            case T.FlFrac{}:
              gd.nd.NFracT(Char.is_digit(cc), Char.is_eq(cc, '_'), Char.is_eq(cc, 'e'), Char.is_eq(cc, 'E'), sign,
                base, ds, us, why, cc, {==}, {==}, {==}, {==}, gd.l(gd.d10(ds), gd.nk(T.NFrac{}, False{}, True{},
                  T.FlFrac{}), e))
            case T.FlE{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NFrac{}, T.Num{T.NFrac{}, sign, base, ds, us, True{}, why}, cc),
                False{}, gd.fput(False{}, cc, T.FlE{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NFrac{}, False{}, True{}, T.FlE{}), e))
            case T.FlESign{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NFrac{}, T.Num{T.NFrac{}, sign, base, ds, us, True{}, why}, cc),
                False{}, gd.fput(False{}, cc, T.FlESign{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NFrac{}, False{}, True{}, T.FlESign{}), e))
            case T.FlExp{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NFrac{}, T.Num{T.NFrac{}, sign, base, ds, us, True{}, why}, cc),
                False{}, gd.fput(False{}, cc, T.FlExp{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NFrac{}, False{}, True{}, T.FlExp{}), e))
            case T.FlNo{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NFrac{}, T.Num{T.NFrac{}, sign, base, ds, us, True{}, why}, cc),
                False{}, gd.fput(False{}, cc, T.FlNo{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NFrac{}, False{}, True{}, T.FlNo{}), e))
        case False{}:
          match fl:
            case T.FlStart{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NFrac{}, T.Num{T.NFrac{}, sign, base, ds, us, False{}, why}, cc),
                False{}, gd.fput(False{}, cc, T.FlStart{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NFrac{}, False{}, False{}, T.FlStart{}), e))
            case T.FlZero{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NFrac{}, T.Num{T.NFrac{}, sign, base, ds, us, False{}, why}, cc),
                False{}, gd.fput(False{}, cc, T.FlZero{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NFrac{}, False{}, False{}, T.FlZero{}), e))
            case T.FlInt{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NFrac{}, T.Num{T.NFrac{}, sign, base, ds, us, False{}, why}, cc),
                False{}, gd.fput(False{}, cc, T.FlInt{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NFrac{}, False{}, False{}, T.FlInt{}), e))
            case T.FlDot{}:
              gd.nd.NFracF(Char.is_digit(cc), Char.is_eq(cc, '_'), Char.is_eq(cc, 'e'), Char.is_eq(cc, 'E'), sign,
                base, ds, us, why, cc, {==}, {==}, {==}, {==}, gd.l(gd.d10(ds), gd.nk(T.NFrac{}, False{}, False{},
                  T.FlDot{}), e))
            case T.FlFrac{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NFrac{}, T.Num{T.NFrac{}, sign, base, ds, us, False{}, why}, cc),
                False{}, gd.fput(False{}, cc, T.FlFrac{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NFrac{}, False{}, False{}, T.FlFrac{}), e))
            case T.FlE{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NFrac{}, T.Num{T.NFrac{}, sign, base, ds, us, False{}, why}, cc),
                False{}, gd.fput(False{}, cc, T.FlE{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NFrac{}, False{}, False{}, T.FlE{}), e))
            case T.FlESign{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NFrac{}, T.Num{T.NFrac{}, sign, base, ds, us, False{}, why}, cc),
                False{}, gd.fput(False{}, cc, T.FlESign{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NFrac{}, False{}, False{}, T.FlESign{}), e))
            case T.FlExp{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NFrac{}, T.Num{T.NFrac{}, sign, base, ds, us, False{}, why}, cc),
                False{}, gd.fput(False{}, cc, T.FlExp{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NFrac{}, False{}, False{}, T.FlExp{}), e))
            case T.FlNo{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NFrac{}, T.Num{T.NFrac{}, sign, base, ds, us, False{}, why}, cc),
                False{}, gd.fput(False{}, cc, T.FlNo{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NFrac{}, False{}, False{}, T.FlNo{}), e))

# the scan and the automaton in NEDig, by whether a digit was seen
def gd.nx.NEDig(
  lead: Bool,
  saw: Bool,
  fl: T.Fl,
  +sign: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +why: String,
  +cc: Char,
  +e: {Bool.and(gd.d10(ds), gd.nk(T.NEDig{}, lead, saw, fl)) == True{} : Bool}
) -> {gd.nm(T.num.on(T.NEDig{}, T.Num{T.NEDig{}, sign, base, ds, us, saw, why}, cc), False{}, gd.fput(lead, cc,
  fl)) == True{} : Bool}:
  match lead:
    case True{}:
      match saw:
        case True{}:
          match fl:
            case T.FlStart{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NEDig{}, T.Num{T.NEDig{}, sign, base, ds, us, True{}, why}, cc),
                False{}, gd.fput(True{}, cc, T.FlStart{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NEDig{}, True{}, True{}, T.FlStart{}), e))
            case T.FlZero{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NEDig{}, T.Num{T.NEDig{}, sign, base, ds, us, True{}, why}, cc),
                False{}, gd.fput(True{}, cc, T.FlZero{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NEDig{}, True{}, True{}, T.FlZero{}), e))
            case T.FlInt{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NEDig{}, T.Num{T.NEDig{}, sign, base, ds, us, True{}, why}, cc),
                False{}, gd.fput(True{}, cc, T.FlInt{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NEDig{}, True{}, True{}, T.FlInt{}), e))
            case T.FlDot{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NEDig{}, T.Num{T.NEDig{}, sign, base, ds, us, True{}, why}, cc),
                False{}, gd.fput(True{}, cc, T.FlDot{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NEDig{}, True{}, True{}, T.FlDot{}), e))
            case T.FlFrac{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NEDig{}, T.Num{T.NEDig{}, sign, base, ds, us, True{}, why}, cc),
                False{}, gd.fput(True{}, cc, T.FlFrac{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NEDig{}, True{}, True{}, T.FlFrac{}), e))
            case T.FlE{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NEDig{}, T.Num{T.NEDig{}, sign, base, ds, us, True{}, why}, cc),
                False{}, gd.fput(True{}, cc, T.FlE{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NEDig{}, True{}, True{}, T.FlE{}), e))
            case T.FlESign{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NEDig{}, T.Num{T.NEDig{}, sign, base, ds, us, True{}, why}, cc),
                False{}, gd.fput(True{}, cc, T.FlESign{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NEDig{}, True{}, True{}, T.FlESign{}), e))
            case T.FlExp{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NEDig{}, T.Num{T.NEDig{}, sign, base, ds, us, True{}, why}, cc),
                False{}, gd.fput(True{}, cc, T.FlExp{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NEDig{}, True{}, True{}, T.FlExp{}), e))
            case T.FlNo{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NEDig{}, T.Num{T.NEDig{}, sign, base, ds, us, True{}, why}, cc),
                False{}, gd.fput(True{}, cc, T.FlNo{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NEDig{}, True{}, True{}, T.FlNo{}), e))
        case False{}:
          match fl:
            case T.FlStart{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NEDig{}, T.Num{T.NEDig{}, sign, base, ds, us, False{}, why}, cc),
                False{}, gd.fput(True{}, cc, T.FlStart{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NEDig{}, True{}, False{}, T.FlStart{}), e))
            case T.FlZero{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NEDig{}, T.Num{T.NEDig{}, sign, base, ds, us, False{}, why}, cc),
                False{}, gd.fput(True{}, cc, T.FlZero{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NEDig{}, True{}, False{}, T.FlZero{}), e))
            case T.FlInt{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NEDig{}, T.Num{T.NEDig{}, sign, base, ds, us, False{}, why}, cc),
                False{}, gd.fput(True{}, cc, T.FlInt{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NEDig{}, True{}, False{}, T.FlInt{}), e))
            case T.FlDot{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NEDig{}, T.Num{T.NEDig{}, sign, base, ds, us, False{}, why}, cc),
                False{}, gd.fput(True{}, cc, T.FlDot{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NEDig{}, True{}, False{}, T.FlDot{}), e))
            case T.FlFrac{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NEDig{}, T.Num{T.NEDig{}, sign, base, ds, us, False{}, why}, cc),
                False{}, gd.fput(True{}, cc, T.FlFrac{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NEDig{}, True{}, False{}, T.FlFrac{}), e))
            case T.FlE{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NEDig{}, T.Num{T.NEDig{}, sign, base, ds, us, False{}, why}, cc),
                False{}, gd.fput(True{}, cc, T.FlE{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NEDig{}, True{}, False{}, T.FlE{}), e))
            case T.FlESign{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NEDig{}, T.Num{T.NEDig{}, sign, base, ds, us, False{}, why}, cc),
                False{}, gd.fput(True{}, cc, T.FlESign{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NEDig{}, True{}, False{}, T.FlESign{}), e))
            case T.FlExp{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NEDig{}, T.Num{T.NEDig{}, sign, base, ds, us, False{}, why}, cc),
                False{}, gd.fput(True{}, cc, T.FlExp{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NEDig{}, True{}, False{}, T.FlExp{}), e))
            case T.FlNo{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NEDig{}, T.Num{T.NEDig{}, sign, base, ds, us, False{}, why}, cc),
                False{}, gd.fput(True{}, cc, T.FlNo{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NEDig{}, True{}, False{}, T.FlNo{}), e))
    case False{}:
      match saw:
        case True{}:
          match fl:
            case T.FlStart{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NEDig{}, T.Num{T.NEDig{}, sign, base, ds, us, True{}, why}, cc),
                False{}, gd.fput(False{}, cc, T.FlStart{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NEDig{}, False{}, True{}, T.FlStart{}), e))
            case T.FlZero{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NEDig{}, T.Num{T.NEDig{}, sign, base, ds, us, True{}, why}, cc),
                False{}, gd.fput(False{}, cc, T.FlZero{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NEDig{}, False{}, True{}, T.FlZero{}), e))
            case T.FlInt{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NEDig{}, T.Num{T.NEDig{}, sign, base, ds, us, True{}, why}, cc),
                False{}, gd.fput(False{}, cc, T.FlInt{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NEDig{}, False{}, True{}, T.FlInt{}), e))
            case T.FlDot{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NEDig{}, T.Num{T.NEDig{}, sign, base, ds, us, True{}, why}, cc),
                False{}, gd.fput(False{}, cc, T.FlDot{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NEDig{}, False{}, True{}, T.FlDot{}), e))
            case T.FlFrac{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NEDig{}, T.Num{T.NEDig{}, sign, base, ds, us, True{}, why}, cc),
                False{}, gd.fput(False{}, cc, T.FlFrac{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NEDig{}, False{}, True{}, T.FlFrac{}), e))
            case T.FlE{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NEDig{}, T.Num{T.NEDig{}, sign, base, ds, us, True{}, why}, cc),
                False{}, gd.fput(False{}, cc, T.FlE{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NEDig{}, False{}, True{}, T.FlE{}), e))
            case T.FlESign{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NEDig{}, T.Num{T.NEDig{}, sign, base, ds, us, True{}, why}, cc),
                False{}, gd.fput(False{}, cc, T.FlESign{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NEDig{}, False{}, True{}, T.FlESign{}), e))
            case T.FlExp{}:
              gd.nd.NEDigT(Char.is_digit(cc), Char.is_eq(cc, '_'), sign, base, ds, us, why, cc, {==}, {==},
                gd.l(gd.d10(ds), gd.nk(T.NEDig{}, False{}, True{}, T.FlExp{}), e))
            case T.FlNo{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NEDig{}, T.Num{T.NEDig{}, sign, base, ds, us, True{}, why}, cc),
                False{}, gd.fput(False{}, cc, T.FlNo{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NEDig{}, False{}, True{}, T.FlNo{}), e))
        case False{}:
          match fl:
            case T.FlStart{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NEDig{}, T.Num{T.NEDig{}, sign, base, ds, us, False{}, why}, cc),
                False{}, gd.fput(False{}, cc, T.FlStart{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NEDig{}, False{}, False{}, T.FlStart{}), e))
            case T.FlZero{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NEDig{}, T.Num{T.NEDig{}, sign, base, ds, us, False{}, why}, cc),
                False{}, gd.fput(False{}, cc, T.FlZero{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NEDig{}, False{}, False{}, T.FlZero{}), e))
            case T.FlInt{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NEDig{}, T.Num{T.NEDig{}, sign, base, ds, us, False{}, why}, cc),
                False{}, gd.fput(False{}, cc, T.FlInt{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NEDig{}, False{}, False{}, T.FlInt{}), e))
            case T.FlDot{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NEDig{}, T.Num{T.NEDig{}, sign, base, ds, us, False{}, why}, cc),
                False{}, gd.fput(False{}, cc, T.FlDot{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NEDig{}, False{}, False{}, T.FlDot{}), e))
            case T.FlFrac{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NEDig{}, T.Num{T.NEDig{}, sign, base, ds, us, False{}, why}, cc),
                False{}, gd.fput(False{}, cc, T.FlFrac{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NEDig{}, False{}, False{}, T.FlFrac{}), e))
            case T.FlE{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NEDig{}, T.Num{T.NEDig{}, sign, base, ds, us, False{}, why}, cc),
                False{}, gd.fput(False{}, cc, T.FlE{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NEDig{}, False{}, False{}, T.FlE{}), e))
            case T.FlESign{}:
              gd.nd.NEDigF(Char.is_digit(cc), Char.is_eq(cc, '_'), sign, base, ds, us, why, cc, {==}, {==},
                gd.l(gd.d10(ds), gd.nk(T.NEDig{}, False{}, False{}, T.FlESign{}), e))
            case T.FlExp{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NEDig{}, T.Num{T.NEDig{}, sign, base, ds, us, False{}, why}, cc),
                False{}, gd.fput(False{}, cc, T.FlExp{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NEDig{}, False{}, False{}, T.FlExp{}), e))
            case T.FlNo{}:
              Eq.bit.absurd(&2, {gd.nm(T.num.on(T.NEDig{}, T.Num{T.NEDig{}, sign, base, ds, us, False{}, why}, cc),
                False{}, gd.fput(False{}, cc, T.FlNo{})) == True{} : Bool},
                gd.r(gd.d10(ds), gd.nk(T.NEDig{}, False{}, False{}, T.FlNo{}), e))

# the scan after one character, in NBase: the automaton's state is not asked
def gd.nx.NBase(
  +lead: Bool,
  +fl: T.Fl,
  +sign: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String,
  +cc: Char,
  +e: {Bool.and(gd.d10(ds), gd.nk(T.NBase{}, lead, saw, fl)) == True{} : Bool}
) -> {gd.nm(T.num.on(T.NBase{}, T.Num{T.NBase{}, sign, base, ds, us, saw, why}, cc), False{}, gd.fput(lead, cc,
  fl)) == True{} : Bool}:
  gd.nd.NBase(Char.is_eq(cc, '_'), sign, base, ds, us, saw, why, cc, gd.fput(lead, cc, fl), gd.l(gd.d10(ds), True{}, e))

# a failed scan stays failed
def gd.nx.NBad(
  +lead: Bool,
  +fl: T.Fl,
  +sign: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String,
  +cc: Char,
  +e: {Bool.and(gd.d10(ds), gd.nk(T.NBad{}, lead, saw, fl)) == True{} : Bool}
) -> {gd.nm(T.num.on(T.NBad{}, T.Num{T.NBad{}, sign, base, ds, us, saw, why}, cc), False{}, gd.fput(lead, cc,
  fl)) == True{} : Bool}:
  gd.tt(gd.d10(ds), True{}, gd.l(gd.d10(ds), True{}, e), {==})

# the scan and the automaton after one character, by the scan's state
def gd.ns.nk(
  nk: T.NK,
  +lead: Bool,
  +fl: T.Fl,
  +sign: T.Sign,
  +base: U32,
  +ds: List<&2, U32>,
  +us: Bool,
  +saw: Bool,
  +why: String,
  +cc: Char,
  +e: {Bool.and(gd.d10(ds), gd.nk(nk, lead, saw, fl)) == True{} : Bool}
) -> {gd.nm(T.num.on(nk, T.Num{nk, sign, base, ds, us, saw, why}, cc), False{}, gd.fput(lead, cc,
  fl)) == True{} : Bool}:
  match nk:
    case T.NLead{}:
      gd.nx.NLead(lead, fl, sign, base, ds, us, saw, why, cc, e)
    case T.NSign{}:
      gd.nx.NSign(lead, fl, sign, base, ds, us, saw, why, cc, e)
    case T.NZero{}:
      gd.nx.NZero(lead, fl, sign, base, ds, us, saw, why, cc, e)
    case T.NDig{}:
      gd.nx.NDig(lead, fl, sign, base, ds, us, saw, why, cc, e)
    case T.NBase{}:
      gd.nx.NBase(lead, fl, sign, base, ds, us, saw, why, cc, e)
    case T.NFrac{}:
      gd.nx.NFrac(lead, saw, fl, sign, base, ds, us, why, cc, e)
    case T.NExp{}:
      gd.nx.NExp(lead, fl, sign, base, ds, us, saw, why, cc, e)
    case T.NEDig{}:
      gd.nx.NEDig(lead, saw, fl, sign, base, ds, us, why, cc, e)
    case T.NBad{}:
      gd.nx.NBad(lead, fl, sign, base, ds, us, saw, why, cc, e)

# one step of the numeral scan keeps it in step with the automaton
def gd.ns(
  st: T.Num,
  +lead: Bool,
  +fl: T.Fl,
  +cc: Char,
  +e: {gd.nm(st, lead, fl) == True{} : Bool}
) -> {gd.nm(T.num.step(st, cc), False{}, gd.fput(lead, cc, fl)) == True{} : Bool}:
  match st:
    case T.Num{+nk, +sign, +base, +ds, +us, +saw, +why}:
      gd.ns.nk(nk, lead, fl, sign, base, ds, us, saw, why, cc, e)

# the first character of a spelling, then none
def gd.nlead(cs: List<&2, Char>, lead: Bool) -> Bool:
  match cs:
    case []:
      lead
    case _h <> tt:
      gd.nlead(tt, False{})

# the whole scan keeps it in step
def gd.ngo(
  cs: List<&2, Char>,
  +st: T.Num,
  +lead: Bool,
  +fl: T.Fl,
  +e: {gd.nm(st, lead, fl) == True{} : Bool}
) -> {gd.nm(T.num.go(cs, st), gd.nlead(cs, lead), gd.fb(cs, lead, fl)) == True{} : Bool}:
  match cs:
    case []:
      e
    case +hh <> +tt:
      gd.ngo(tt, T.num.step(st, hh), False{}, gd.fput(lead, hh, fl), gd.ns(st, lead, fl, hh, e))

# the automaton over characters reversed onto more
def gd.rg(
  xs: List<&2, Char>,
  +acc: List<&2, Char>,
  +ss: T.Fl
) -> {T.wf.flo.go(List.reverse.go(&2, Char, xs, acc), ss) == T.wf.flo.go(acc, T.wf.flo.go(List.reverse.go(&2, Char,
  xs, []), ss)) : T.Fl}:
  match xs:
    case []:
      {==}
    case +xx <> +rr:
      Equal.trans(T.Fl, T.wf.flo.go(List.reverse.go(&2, Char, rr, xx <> acc), ss),
        T.wf.flo.go(acc, T.wf.flo.step(T.wf.flo.go(List.reverse.go(&2, Char, rr, []), ss), xx)),
        T.wf.flo.go(acc, T.wf.flo.go(List.reverse.go(&2, Char, rr, [xx]), ss)),
        gd.rg(rr, xx <> acc, ss),
        Equal.sym(T.Fl, T.wf.flo.go(acc, T.wf.flo.go(List.reverse.go(&2, Char, rr, [xx]), ss)),
          T.wf.flo.go(acc, T.wf.flo.step(T.wf.flo.go(List.reverse.go(&2, Char, rr, []), ss), xx)),
          Equal.cong(T.Fl, T.Fl, yy => T.wf.flo.go(acc, yy), T.wf.flo.go(List.reverse.go(&2, Char, rr, [xx]), ss),
            T.wf.flo.step(T.wf.flo.go(List.reverse.go(&2, Char, rr, []), ss), xx), gd.rg(rr, [xx], ss))))

# a character kept or dropped by the spelling of a sign
def gd.fbput.s(
  bb: Bool,
  +cc: Char,
  +out: List<&2, Char>,
  +ss: T.Fl
) -> {T.wf.flo.go(List.reverse(&2, Char, T.word.body.put.sign(bb, cc, out)), ss) == gd.fsel(bb,
  T.wf.flo.go(List.reverse(&2, Char, out), ss), T.wf.flo.step(T.wf.flo.go(List.reverse(&2, Char, out), ss),
    cc)) : T.Fl}:
  match bb:
    case True{}:
      {==}
    case False{}:
      gd.rg(out, [cc], ss)

# a character kept or dropped by the spelling of an underscore
def gd.fbput.u(
  bb: Bool,
  +cc: Char,
  +out: List<&2, Char>,
  +ss: T.Fl
) -> {T.wf.flo.go(List.reverse(&2, Char, T.word.body.put.us(bb, cc, out)), ss) == gd.fsel(bb,
  T.wf.flo.go(List.reverse(&2, Char, out), ss), T.wf.flo.step(T.wf.flo.go(List.reverse(&2, Char, out), ss),
    cc)) : T.Fl}:
  match bb:
    case True{}:
      {==}
    case False{}:
      gd.rg(out, [cc], ss)

# one character of the spelling
def gd.fbput(
  lead: Bool,
  +cc: Char,
  +out: List<&2, Char>,
  +ss: T.Fl
) -> {T.wf.flo.go(List.reverse(&2, Char, T.word.body.put(lead, cc, out)), ss) == gd.fput(lead, cc,
  T.wf.flo.go(List.reverse(&2, Char, out), ss)) : T.Fl}:
  match lead:
    case True{}:
      gd.fbput.s(Bool.or(Char.is_eq(cc, '+'), Char.is_eq(cc, '-')), cc, out, ss)
    case False{}:
      gd.fbput.u(Char.is_eq(cc, '_'), cc, out, ss)

# the automaton over a spelling is gd.fb
def gd.fbl(
  cs: List<&2, Char>,
  +lead: Bool,
  +out: List<&2, Char>,
  +ss: T.Fl
) -> {T.wf.flo.go(T.word.body.go(cs, lead, out), ss) == gd.fb(cs, lead, T.wf.flo.go(List.reverse(&2, Char, out),
  ss)) : T.Fl}:
  match cs:
    case []:
      {==}
    case +hh <> +tt:
      Equal.trans(T.Fl, T.wf.flo.go(T.word.body.go(tt, False{}, T.word.body.put(lead, hh, out)), ss),
        gd.fb(tt, False{}, T.wf.flo.go(List.reverse(&2, Char, T.word.body.put(lead, hh, out)), ss)),
        gd.fb(tt, False{}, gd.fput(lead, hh, T.wf.flo.go(List.reverse(&2, Char, out), ss))),
        gd.fbl(tt, False{}, T.word.body.put(lead, hh, out), ss),
        Equal.cong(T.Fl, T.Fl, yy => gd.fb(tt, False{}, yy),
          T.wf.flo.go(List.reverse(&2, Char, T.word.body.put(lead, hh, out)), ss),
          gd.fput(lead, hh, T.wf.flo.go(List.reverse(&2, Char, out), ss)), gd.fbput(lead, hh, out, ss)))

# a spelling the automaton ends in a fraction's digit reads as a float
def gd.fl.frac(fl: T.Fl, +ee: {gd.flq(fl, T.FlFrac{}) == True{} : Bool}) -> {T.wf.flo.end(fl) == True{} : Bool}:
  match fl:
    case T.FlFrac{}:
      {==}
    case T.FlStart{}:
      Eq.bit.absurd(&2, {T.wf.flo.end(T.FlStart{}) == True{} : Bool}, ee)
    case T.FlZero{}:
      Eq.bit.absurd(&2, {T.wf.flo.end(T.FlZero{}) == True{} : Bool}, ee)
    case T.FlInt{}:
      Eq.bit.absurd(&2, {T.wf.flo.end(T.FlInt{}) == True{} : Bool}, ee)
    case T.FlDot{}:
      Eq.bit.absurd(&2, {T.wf.flo.end(T.FlDot{}) == True{} : Bool}, ee)
    case T.FlE{}:
      Eq.bit.absurd(&2, {T.wf.flo.end(T.FlE{}) == True{} : Bool}, ee)
    case T.FlESign{}:
      Eq.bit.absurd(&2, {T.wf.flo.end(T.FlESign{}) == True{} : Bool}, ee)
    case T.FlExp{}:
      {==}
    case T.FlNo{}:
      Eq.bit.absurd(&2, {T.wf.flo.end(T.FlNo{}) == True{} : Bool}, ee)

# or an exponent's digit
def gd.fl.exp(fl: T.Fl, +ee: {gd.flq(fl, T.FlExp{}) == True{} : Bool}) -> {T.wf.flo.end(fl) == True{} : Bool}:
  match fl:
    case T.FlExp{}:
      {==}
    case T.FlStart{}:
      Eq.bit.absurd(&2, {T.wf.flo.end(T.FlStart{}) == True{} : Bool}, ee)
    case T.FlZero{}:
      Eq.bit.absurd(&2, {T.wf.flo.end(T.FlZero{}) == True{} : Bool}, ee)
    case T.FlInt{}:
      Eq.bit.absurd(&2, {T.wf.flo.end(T.FlInt{}) == True{} : Bool}, ee)
    case T.FlDot{}:
      Eq.bit.absurd(&2, {T.wf.flo.end(T.FlDot{}) == True{} : Bool}, ee)
    case T.FlFrac{}:
      {==}
    case T.FlE{}:
      Eq.bit.absurd(&2, {T.wf.flo.end(T.FlE{}) == True{} : Bool}, ee)
    case T.FlESign{}:
      Eq.bit.absurd(&2, {T.wf.flo.end(T.FlESign{}) == True{} : Bool}, ee)
    case T.FlNo{}:
      Eq.bit.absurd(&2, {T.wf.flo.end(T.FlNo{}) == True{} : Bool}, ee)

# the last of three ors
def gd.or3(
  aa: Bool,
  bb: Bool,
  +cc: Bool,
  +ec: {cc == True{} : Bool}
) -> {Bool.or(aa, Bool.or(bb, cc)) == True{} : Bool}:
  match aa bb:
    case True{} _b:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      ec

# a float's spelling that the automaton ends well in is well-formed
def gd.flo.ok(
  +text: String,
  +fl: T.Fl,
  +ef: {fl == T.wf.flo.go(String.to_list(text), T.FlStart{}) : T.Fl},
  +ee: {T.wf.flo.end(fl) == True{} : Bool}
) -> {T.wf.flo(text) == True{} : Bool}:
  gd.or3(T.str.eq(text, "inf"), T.str.eq(text, "nan"), T.wf.flo.end(T.wf.flo.go(String.to_list(text), T.FlStart{})),
    Equal.trans(Bool, T.wf.flo.end(T.wf.flo.go(String.to_list(text), T.FlStart{})), T.wf.flo.end(fl), True{},
      Equal.cong(T.Fl, Bool, ff => T.wf.flo.end(ff), T.wf.flo.go(String.to_list(text), T.FlStart{}), fl,
        Equal.sym(T.Fl, fl, T.wf.flo.go(String.to_list(text), T.FlStart{}), ef)), ee))

# an integer whose range was checked
def gd.nfin.rng(
  ok: Bool,
  +sign: T.Sign,
  +digits: String,
  +ew: {T.wf.dec(digits) == True{} : Bool},
  +eo: {T.i64.fits(sign, digits) == ok : Bool}
) -> {L2.gd.gok(T.num.fin.range(ok, sign, digits)) == True{} : Bool}:
  match ok:
    case True{}:
      gd.tt(T.wf.dec(digits), T.i64.fits(sign, digits), ew, eo)
    case False{}:
      {==}

# an integer, when a digit was seen
def gd.nfin.int(
  saw: Bool,
  +sign: T.Sign,
  +ds: List<&2, U32>,
  +ed: {gd.d10(ds) == True{} : Bool}
) -> {L2.gd.gok(T.num.fin.int(saw, sign, T.dec.text(ds))) == True{} : Bool}:
  match saw:
    case True{}:
      gd.nfin.rng(T.i64.fits(sign, T.dec.text(ds)), sign, T.dec.text(ds), gd.dec.text(ds, ed), {==})
    case False{}:
      {==}

# a prefixed integer, when no sign was written
def gd.nfin.base(
  signed: Bool,
  +saw: Bool,
  +sign: T.Sign,
  +ds: List<&2, U32>,
  +ed: {gd.d10(ds) == True{} : Bool}
) -> {L2.gd.gok(T.num.fin.base(signed, saw, sign, ds)) == True{} : Bool}:
  match signed:
    case True{}:
      {==}
    case False{}:
      gd.nfin.int(saw, sign, ds, ed)

# a float, when a digit was seen
def gd.nfin.flo(
  saw: Bool,
  +sign: T.Sign,
  +text: String,
  +ee: {L2.gd.ifok(saw, T.wf.flo(text)) == True{} : Bool}
) -> {L2.gd.gok(T.num.fin.saw(saw, T.VFlo{sign, text})) == True{} : Bool}:
  match saw:
    case True{}:
      ee
    case False{}:
      {==}

# a zero
def gd.nfin.zero(sign: T.Sign) -> {L2.gd.gok(T.GotVal{T.VInt{sign, "0"}}) == True{} : Bool}:
  match sign:
    case T.Plus{}:
      {==}
    case T.Minus{}:
      {==}

# the float's end state from the scan's
def gd.nfin.fe(
  saw: Bool,
  +lead: Bool,
  +fl: T.Fl,
  +text: String,
  +ef: {fl == T.wf.flo.go(String.to_list(text), T.FlStart{}) : T.Fl},
  +ee: {gd.nk(T.NFrac{}, lead, saw, fl) == True{} : Bool}
) -> {L2.gd.ifok(saw, T.wf.flo(text)) == True{} : Bool}:
  match saw:
    case True{}:
      gd.flo.ok(text, fl, ef, gd.fl.frac(fl, gd.r(Bool.not(lead), gd.flq(fl, T.FlFrac{}), ee)))
    case False{}:
      {==}

# and an exponent's
def gd.nfin.ee(
  saw: Bool,
  +lead: Bool,
  +fl: T.Fl,
  +text: String,
  +ef: {fl == T.wf.flo.go(String.to_list(text), T.FlStart{}) : T.Fl},
  +ee: {gd.nk(T.NEDig{}, lead, saw, fl) == True{} : Bool}
) -> {L2.gd.ifok(saw, T.wf.flo(text)) == True{} : Bool}:
  match saw:
    case True{}:
      gd.flo.ok(text, fl, ef, gd.fl.exp(fl, gd.r(Bool.not(lead), gd.flq(fl, T.FlExp{}), ee)))
    case False{}:
      {==}

# the value a finished scan gives, by its state
def gd.nfin.nk(
  nk: T.NK,
  +sign: T.Sign,
  +ds: List<&2, U32>,
  +saw: Bool,
  +why: String,
  +cs: List<&2, Char>,
  +lead: Bool,
  +fl: T.Fl,
  +e: {Bool.and(gd.d10(ds), gd.nk(nk, lead, saw, fl)) == True{} : Bool},
  +ef: {fl == T.wf.flo.go(String.to_list(T.word.body(cs)), T.FlStart{}) : T.Fl}
) -> {L2.gd.gok(T.num.fin.nk(nk, sign, ds, saw, why, cs)) == True{} : Bool}:
  match nk:
    case T.NBad{}:
      {==}
    case T.NLead{}:
      {==}
    case T.NSign{}:
      {==}
    case T.NZero{}:
      gd.nfin.zero(sign)
    case T.NDig{}:
      gd.nfin.int(saw, sign, ds, gd.l(gd.d10(ds), gd.nk(T.NDig{}, lead, saw, fl), e))
    case T.NBase{}:
      gd.nfin.base(T.num.signed(cs), saw, sign, ds, gd.l(gd.d10(ds), True{}, e))
    case T.NFrac{}:
      gd.nfin.flo(saw, sign, T.word.body(cs),
        gd.nfin.fe(saw, lead, fl, T.word.body(cs), ef, gd.r(gd.d10(ds), gd.nk(T.NFrac{}, lead, saw, fl), e)))
    case T.NExp{}:
      {==}
    case T.NEDig{}:
      gd.nfin.flo(saw, sign, T.word.body(cs),
        gd.nfin.ee(saw, lead, fl, T.word.body(cs), ef, gd.r(gd.d10(ds), gd.nk(T.NEDig{}, lead, saw, fl), e)))

# no trailing underscore
def gd.nfin.us(
  us: Bool,
  +nk: T.NK,
  +sign: T.Sign,
  +ds: List<&2, U32>,
  +saw: Bool,
  +why: String,
  +cs: List<&2, Char>,
  +lead: Bool,
  +fl: T.Fl,
  +e: {Bool.and(gd.d10(ds), gd.nk(nk, lead, saw, fl)) == True{} : Bool},
  +ef: {fl == T.wf.flo.go(String.to_list(T.word.body(cs)), T.FlStart{}) : T.Fl}
) -> {L2.gd.gok(T.num.fin.us(us, nk, sign, ds, saw, why, cs)) == True{} : Bool}:
  match us:
    case True{}:
      {==}
    case False{}:
      gd.nfin.nk(nk, sign, ds, saw, why, cs, lead, fl, e, ef)

# a finished scan's value is well-formed
def gd.nfin(
  st: T.Num,
  +cs: List<&2, Char>,
  +lead: Bool,
  +fl: T.Fl,
  +e: {gd.nm(st, lead, fl) == True{} : Bool},
  +ef: {fl == T.wf.flo.go(String.to_list(T.word.body(cs)), T.FlStart{}) : T.Fl}
) -> {L2.gd.gok(T.num.fin(st, cs)) == True{} : Bool}:
  match st:
    case T.Num{+nk, +sign, _b, +ds, +us, +saw, +why}:
      gd.nfin.us(us, nk, sign, ds, saw, why, cs, lead, fl, e, ef)

# every numeral's value is well-formed
def gd.num(+cs: List<&2, Char>) -> {L2.gd.gok(T.word.num(cs)) == True{} : Bool}:
  gd.nfin(T.num.go(cs, T.num.start()), cs, gd.nlead(cs, True{}), gd.fb(cs, True{}, T.FlStart{}),
    gd.ngo(cs, T.num.start(), True{}, T.FlStart{}, {==}),
    Equal.sym(T.Fl, T.wf.flo.go(String.to_list(T.word.body(cs)), T.FlStart{}), gd.fb(cs, True{}, T.FlStart{}),
      Equal.trans(T.Fl, T.wf.flo.go(String.to_list(T.word.body(cs)), T.FlStart{}),
        T.wf.flo.go(T.word.body.go(cs, True{}, []), T.FlStart{}), gd.fb(cs, True{}, T.FlStart{}),
        Equal.cong(List<&2, Char>, T.Fl, xs => T.wf.flo.go(xs, T.FlStart{}),
          String.to_list(String.from_list(T.word.body.go(cs, True{}, []))), T.word.body.go(cs, True{}, []),
          M2.gd.tlfl(T.word.body.go(cs, True{}, []))),
        gd.fbl(cs, True{}, [], T.FlStart{}))))

# the specials: true, false, inf and nan, signed or not
def gd.w.nan(aa: Bool, bb: Bool, cc: Bool) -> {L2.gd.gok(T.word.spec.nan(aa, bb, cc)) == True{} : Bool}:
  match aa bb cc:
    case True{} _b _c:
      {==}
    case False{} True{} _c:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

# inf, or nan
def gd.w.inf(
  aa: Bool,
  bb: Bool,
  cc: Bool,
  +ss: String
) -> {L2.gd.gok(T.word.spec.inf(aa, bb, cc, ss)) == True{} : Bool}:
  match aa bb cc:
    case True{} _b _c:
      {==}
    case False{} True{} _c:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      gd.w.nan(T.str.eq(ss, "nan"), T.str.eq(ss, "+nan"), T.str.eq(ss, "-nan"))

# true, false, or the rest
def gd.w.st(hit: Bool, other: Bool, +ss: String) -> {L2.gd.gok(T.word.spec.t(hit, other, ss)) == True{} : Bool}:
  match hit other:
    case True{} _o:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      gd.w.inf(T.str.eq(ss, "inf"), T.str.eq(ss, "+inf"), T.str.eq(ss, "-inf"), ss)

# every special's value is well-formed
def gd.w.spec(+ss: String) -> {L2.gd.gok(T.word.spec(ss)) == True{} : Bool}:
  gd.w.st(T.str.eq(ss, "true"), T.str.eq(ss, "false"), ss)

# a datetime's value
def gd.w.when(
  ww: T.WhenOut,
  +ee: {gd.wot(ww) == True{} : Bool}
) -> {L2.gd.gok(T.word.from.when(ww)) == True{} : Bool}:
  match ww:
    case T.WSome{_w}:
      ee
    case T.WFail{_why}:
      {==}
    case T.WSkip{}:
      {==}

# a datetime or a numeral
def gd.w.rdate(dt: Bool, +cs: List<&2, Char>) -> {L2.gd.gok(T.word.route.date(dt, cs)) == True{} : Bool}:
  match dt:
    case True{}:
      gd.w.when(T.when.read(cs), gd.when(cs))
    case False{}:
      gd.num(cs)

# a special's value, or a datetime or a numeral
def gd.w.route(
  gg: T.Got,
  +dt: Bool,
  +cs: List<&2, Char>,
  +eg: {L2.gd.gok(gg) == True{} : Bool}
) -> {L2.gd.gok(T.word.route(gg, dt, cs)) == True{} : Bool}:
  match gg:
    case T.GotVal{_v}:
      eg
    case T.GotBad{_why}:
      gd.w.rdate(T.word.as_date(dt, T.word.ee(cs)), cs)

# a word that may be special, or not
def gd.w.pick(special: Bool, +cs: List<&2, Char>) -> {L2.gd.gok(T.word.val.pick(special, cs)) == True{} : Bool}:
  match special:
    case True{}:
      gd.w.route(T.word.spec(String.from_list(cs)), T.word.or(T.word.colon(cs), T.word.dash(cs, True{})), cs,
        gd.w.spec(String.from_list(cs)))
    case False{}:
      gd.w.route(T.GotBad{""}, T.word.or(T.word.colon(cs), T.word.dash(cs, True{})), cs, {==})

def L2.gd_word(cs) :
  gd.w.pick(T.word.lead(cs), cs)

# WP-R3: a bare word's states. A bare word ends through word.val (gd_word)
# and gd_take; the character that ended it is held, or a newline that ended a
# root value moves the line on.

# a failed step, for any reason
def gd.g.err2(
  +st: T.St,
  +why: String,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.st.err(st, why)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      match bad:
        case SNil{}:
          gd.tt(L2.gd.tr(why, rows, stack), L2.gd.lx(here, parts, buf, stack, T.HNone{}),
            gd.ifok.any(String.is_empty(why), Bool.and(T.wf.go(rows, T.WfRows{""}), L2.gd.vals(stack)),
              gd.l(L2.gd.tr("", rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)),
            gd.lx.mk(here, parts, buf, stack, T.HNone{}, gd.lx.h(here, parts, buf, stack, hold, gd.r(L2.gd.tr("",
              rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)), gd.lx.p(here, parts, buf, stack, hold,
                gd.r(L2.gd.tr("", rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)), gd.lx.b(here,
                  parts, buf, stack, hold, gd.r(L2.gd.tr("", rows, stack), L2.gd.lx(here, parts, buf, stack,
                    hold), eg)), gd.lx.s(here, parts, buf, stack, hold, gd.r(L2.gd.tr("", rows, stack),
                      L2.gd.lx(here, parts, buf, stack, hold), eg)), {==}))
        case SCon{+bh, +bt}:
          gd.tt(L2.gd.tr(SCon{bh, bt}, rows, stack), L2.gd.lx(here, parts, buf, stack, T.HNone{}), {==},
            gd.lx.mk(here, parts, buf, stack, T.HNone{}, gd.lx.h(here, parts, buf, stack, hold,
              gd.r(L2.gd.tr(SCon{bh, bt}, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)),
                gd.lx.p(here, parts, buf, stack, hold, gd.r(L2.gd.tr(SCon{bh, bt}, rows, stack), L2.gd.lx(here,
                  parts, buf, stack, hold), eg)), gd.lx.b(here, parts, buf, stack, hold, gd.r(L2.gd.tr(SCon{bh, bt},
                    rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)), gd.lx.s(here, parts, buf, stack,
                      hold, gd.r(L2.gd.tr(SCon{bh, bt}, rows, stack), L2.gd.lx(here, parts, buf, stack, hold),
                        eg)), {==}))

# a value a key may hold is one gd_take may put, whatever the state
def gd.okv.of(+st: T.St, +vv: T.Val, +ev: {L2.gd.vok(vv) == True{} : Bool}) -> {L2.gd.okv(st, vv) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.ifok.any(String.is_empty(bad), L2.gd.vok(vv), ev)

# a newline that ended a root value moves the line on; any other state stays
def gd.g.bline.lex(
  lex: T.Lex,
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.bare.line.lex(lex, st)) == True{} : Bool}:
  match lex:
    case T.LTop{}:
      eg
    case T.LLine{}:
      gd.g.lex(st, T.LTop{}, eg)
    case T.LKey{}:
      eg
    case T.LKeyDot{}:
      eg
    case T.LAfter{}:
      eg
    case T.LKeyQ{}:
      eg
    case T.LKeyE{}:
      eg
    case T.LKeyU{}:
      eg
    case T.LVal{}:
      eg
    case T.LQ{}:
      eg
    case T.LQ2{}:
      eg
    case T.LStr{}:
      eg
    case T.LEsc{}:
      eg
    case T.LUni{}:
      eg
    case T.LFold{}:
      eg
    case T.LMq{}:
      eg
    case T.LMqEnd{}:
      eg
    case T.LTrim{}:
      eg
    case T.LTrim2{}:
      eg
    case T.LBare{}:
      eg
    case T.LDate{}:
      eg
    case T.LCom{}:
      eg
    case T.LHead{}:
      eg
    case T.LHeadGap{}:
      eg
    case T.LHeadDot{}:
      eg
    case T.LHeadQ{}:
      eg
    case T.LHeadE{}:
      eg
    case T.LHeadU{}:
      eg
    case T.LHeadR{}:
      eg
    case T.LArr{}:
      eg
    case T.LArrC{}:
      eg
    case T.LInl{}:
      eg
    case T.LInlK{}:
      eg
    case T.LInlC{}:
      eg
    case T.LSink{}:
      eg

# the newline, read off the state
def gd.g.bline.go(+st: T.St, +eg: {L2.good(st) == True{} : Bool}) -> {L2.good(T.bare.line.go(st)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.g.bline.lex(lex, T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab,
        lead}, eg)

# a newline, or another delimiter
def gd.g.bline(
  nl: Bool,
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool}
) -> {L2.good(T.bare.line(st, nl)) == True{} : Bool}:
  match nl:
    case True{}:
      gd.g.bline.go(st, eg)
    case False{}:
      eg

# the delimiter held, or not
def gd.g.bhold(
  +st: T.St,
  +cc: Char,
  hold: Bool,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.bare.hold(st, cc, hold)) == True{} : Bool}:
  match hold:
    case False{}:
      gd.g.bline(T.ch.nl(cc), st, eg)
    case True{}:
      gd.g.hold.on(st, cc, eg, ec)

# a bare word's value placed, or its refusal
def gd.g.bgot(
  gg: T.Got,
  +st: T.St,
  +cc: Char,
  +hold: Bool,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool},
  +ev: {L2.gd.gok(gg) == True{} : Bool}
) -> {L2.good(T.bare.got(gg, st, cc, hold)) == True{} : Bool}:
  match gg:
    case T.GotBad{+why}:
      gd.g.err2(st, why, eg)
    case T.GotVal{+vv}:
      gd.g.bhold(T.val.take(st, vv), cc, hold, gd.g.take(st, vv, eg, gd.okv.of(st, vv, ev)), ec)

# a bare word ends: its buffer read as a value
def gd.g.bfin(
  +st: T.St,
  +cc: Char,
  +hd: Bool,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.bare.finish(st, cc, hd)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.g.bgot(T.word.val(List.reverse(&2, Char, buf)),
        T.St{bad, rows, heads, here, parts, [], lex, back, qkind, stack, hold, uni, left, arrtab, lead}, cc, hd,
        gd.tt(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, [], stack, hold), gd.l(L2.gd.tr(bad, rows,
          stack), L2.gd.lx(here, parts, buf, stack, hold), eg),
          gd.lx.mk(here, parts, [], stack, hold, gd.lx.h(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows,
            stack), L2.gd.lx(here, parts, buf, stack, hold), eg)), gd.lx.p(here, parts, buf, stack, hold,
              gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)), {==}, gd.lx.s(here,
                parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold),
                  eg)), gd.r(L2.gd.keys(stack), L2.gd.hold(hold), gd.lx.s1(here, parts, buf, stack, hold,
                    gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg))))),
        ec, L2.gd_word(List.reverse(&2, Char, buf)))

# a step of a bare word: bdgo
def gd.g.bdgo(
  date: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.bare.date.go(date, st, cc)) == True{} : Bool}:
  match date:
    case True{}:
      gd.g.lex(st, T.LDate{}, eg)
    case False{}:
      gd.g.bfin(st, cc, False{}, eg, ec)

# a step of a bare word: bdate
def gd.g.bdate(
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.bare.date(st, cc)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.g.bdgo(T.date.shaped(buf), T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left,
        arrtab, lead}, cc, eg, ec)

# a step of a bare word: bend
def gd.g.bend(
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.bare.end(st, cc)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.g.bfin(T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead}, cc,
        T.lex.bare.hold(T.ch.skip(cc), T.ch.nl(cc), T.inl.open(stack)), eg, ec)

# a step of a bare word: bsp
def gd.g.bsp(
  sp: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.bare.sp(sp, st, cc)) == True{} : Bool}:
  match sp:
    case True{}:
      gd.g.bdate(st, cc, eg, ec)
    case False{}:
      gd.g.bend(st, cc, eg, ec)

# a step of a bare word: bgo
def gd.g.bgo(
  delim: Bool,
  +sp: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.bare.go(delim, sp, st, cc)) == True{} : Bool}:
  match delim:
    case False{}:
      gd.g.push(st, cc, T.LBare{}, eg, ec)
    case True{}:
      gd.g.bsp(sp, st, cc, eg, ec)

# a step of a bare word: datedig
def gd.g.datedig(
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.date.digit(st, cc)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.tt(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, cc <> (' ' <> buf), stack, hold),
        gd.l(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg),
        gd.lx.mk(here, parts, cc <> (' ' <> buf), stack, hold, gd.lx.h(here, parts, buf, stack, hold,
          gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)), gd.lx.p(here, parts,
            buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)),
          gd.tt(T.wf.char(cc), Bool.and(T.wf.char(' '), L2.gd.cs(buf)), ec,
            gd.tt(T.wf.char(' '), L2.gd.cs(buf), {==}, gd.lx.b(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad,
              rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)))), gd.lx.s(here, parts, buf, stack, hold,
                gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)),
                  gd.r(L2.gd.keys(stack), L2.gd.hold(hold), gd.lx.s1(here, parts, buf, stack, hold,
                    gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg)))))

# a step of a bare word: datego
def gd.g.datego(
  digit: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.lex.date.go(digit, st, cc)) == True{} : Bool}:
  match digit:
    case True{}:
      gd.g.datedig(st, cc, eg, ec)
    case False{}:
      gd.g.bfin(st, cc, True{}, eg, ec)

def L2.gd_bare_steps(lex, hl, st, eg, cc, ec) :
  match lex:
    case T.LTop{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LTop{}, st, cc)) == True{} : Bool}, hl)
    case T.LLine{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LLine{}, st, cc)) == True{} : Bool}, hl)
    case T.LKey{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LKey{}, st, cc)) == True{} : Bool}, hl)
    case T.LKeyDot{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LKeyDot{}, st, cc)) == True{} : Bool}, hl)
    case T.LAfter{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LAfter{}, st, cc)) == True{} : Bool}, hl)
    case T.LKeyQ{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LKeyQ{}, st, cc)) == True{} : Bool}, hl)
    case T.LKeyE{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LKeyE{}, st, cc)) == True{} : Bool}, hl)
    case T.LKeyU{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LKeyU{}, st, cc)) == True{} : Bool}, hl)
    case T.LVal{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LVal{}, st, cc)) == True{} : Bool}, hl)
    case T.LQ{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LQ{}, st, cc)) == True{} : Bool}, hl)
    case T.LQ2{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LQ2{}, st, cc)) == True{} : Bool}, hl)
    case T.LStr{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LStr{}, st, cc)) == True{} : Bool}, hl)
    case T.LEsc{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LEsc{}, st, cc)) == True{} : Bool}, hl)
    case T.LUni{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LUni{}, st, cc)) == True{} : Bool}, hl)
    case T.LFold{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LFold{}, st, cc)) == True{} : Bool}, hl)
    case T.LMq{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LMq{}, st, cc)) == True{} : Bool}, hl)
    case T.LMqEnd{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LMqEnd{}, st, cc)) == True{} : Bool}, hl)
    case T.LTrim{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LTrim{}, st, cc)) == True{} : Bool}, hl)
    case T.LTrim2{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LTrim2{}, st, cc)) == True{} : Bool}, hl)
    case T.LBare{}:
      gd.g.bgo(T.ch.delim(cc), T.ch.space(cc), st, cc, eg, ec)
    case T.LDate{}:
      gd.g.datego(Char.is_digit(cc), st, cc, eg, ec)
    case T.LCom{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LCom{}, st, cc)) == True{} : Bool}, hl)
    case T.LHead{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LHead{}, st, cc)) == True{} : Bool}, hl)
    case T.LHeadGap{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LHeadGap{}, st, cc)) == True{} : Bool}, hl)
    case T.LHeadDot{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LHeadDot{}, st, cc)) == True{} : Bool}, hl)
    case T.LHeadQ{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LHeadQ{}, st, cc)) == True{} : Bool}, hl)
    case T.LHeadE{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LHeadE{}, st, cc)) == True{} : Bool}, hl)
    case T.LHeadU{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LHeadU{}, st, cc)) == True{} : Bool}, hl)
    case T.LHeadR{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LHeadR{}, st, cc)) == True{} : Bool}, hl)
    case T.LArr{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LArr{}, st, cc)) == True{} : Bool}, hl)
    case T.LArrC{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LArrC{}, st, cc)) == True{} : Bool}, hl)
    case T.LInl{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LInl{}, st, cc)) == True{} : Bool}, hl)
    case T.LInlK{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LInlK{}, st, cc)) == True{} : Bool}, hl)
    case T.LInlC{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LInlC{}, st, cc)) == True{} : Bool}, hl)
    case T.LSink{}:
      Eq.bit.absurd(&2, {L2.good(T.read.on(T.LSink{}, st, cc)) == True{} : Bool}, hl)

# WP-R3: the dispatch. read.fast keeps a plain character in the buffer or
# ignores it, and gives every other character, and a held one, to read.on:
# every state good (gd_header_steps, gd_key_steps, gd_value_steps,
# gd_bare_steps). A byte-order mark is dropped.

# a state good, as the fast step builds it: good reads no other field
def gd.gf(
  +bad: String,
  +rows: List<&2, T.Val>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +buf: List<&2, Char>,
  +stack: List<&2, T.Ctx>
) -> Bool:
  L2.good(T.St{bad, rows, [], here, parts, buf, T.LTop{}, T.LTop{}, T.QBasic{}, stack, T.HNone{}, 0, 0, False{},
    False{}})

# one character in any state
def gd.on(
  lex: T.Lex,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.read.on(lex, st, cc)) == True{} : Bool}:
  match lex:
    case T.LTop{}:
      L2.gd_key_steps(T.LTop{}, {==}, st, eg, cc, ec)
    case T.LLine{}:
      L2.gd_key_steps(T.LLine{}, {==}, st, eg, cc, ec)
    case T.LKey{}:
      L2.gd_key_steps(T.LKey{}, {==}, st, eg, cc, ec)
    case T.LKeyDot{}:
      L2.gd_key_steps(T.LKeyDot{}, {==}, st, eg, cc, ec)
    case T.LAfter{}:
      L2.gd_key_steps(T.LAfter{}, {==}, st, eg, cc, ec)
    case T.LKeyQ{}:
      L2.gd_key_steps(T.LKeyQ{}, {==}, st, eg, cc, ec)
    case T.LKeyE{}:
      L2.gd_key_steps(T.LKeyE{}, {==}, st, eg, cc, ec)
    case T.LKeyU{}:
      L2.gd_key_steps(T.LKeyU{}, {==}, st, eg, cc, ec)
    case T.LVal{}:
      L2.gd_value_steps(T.LVal{}, {==}, st, eg, cc, ec)
    case T.LQ{}:
      L2.gd_value_steps(T.LQ{}, {==}, st, eg, cc, ec)
    case T.LQ2{}:
      L2.gd_value_steps(T.LQ2{}, {==}, st, eg, cc, ec)
    case T.LStr{}:
      L2.gd_value_steps(T.LStr{}, {==}, st, eg, cc, ec)
    case T.LEsc{}:
      L2.gd_value_steps(T.LEsc{}, {==}, st, eg, cc, ec)
    case T.LUni{}:
      L2.gd_value_steps(T.LUni{}, {==}, st, eg, cc, ec)
    case T.LFold{}:
      L2.gd_value_steps(T.LFold{}, {==}, st, eg, cc, ec)
    case T.LMq{}:
      L2.gd_value_steps(T.LMq{}, {==}, st, eg, cc, ec)
    case T.LMqEnd{}:
      L2.gd_value_steps(T.LMqEnd{}, {==}, st, eg, cc, ec)
    case T.LTrim{}:
      L2.gd_value_steps(T.LTrim{}, {==}, st, eg, cc, ec)
    case T.LTrim2{}:
      L2.gd_value_steps(T.LTrim2{}, {==}, st, eg, cc, ec)
    case T.LBare{}:
      L2.gd_bare_steps(T.LBare{}, {==}, st, eg, cc, ec)
    case T.LDate{}:
      L2.gd_bare_steps(T.LDate{}, {==}, st, eg, cc, ec)
    case T.LCom{}:
      L2.gd_value_steps(T.LCom{}, {==}, st, eg, cc, ec)
    case T.LHead{}:
      L2.gd_header_steps(T.LHead{}, {==}, st, eg, cc, ec)
    case T.LHeadGap{}:
      L2.gd_header_steps(T.LHeadGap{}, {==}, st, eg, cc, ec)
    case T.LHeadDot{}:
      L2.gd_header_steps(T.LHeadDot{}, {==}, st, eg, cc, ec)
    case T.LHeadQ{}:
      L2.gd_header_steps(T.LHeadQ{}, {==}, st, eg, cc, ec)
    case T.LHeadE{}:
      L2.gd_header_steps(T.LHeadE{}, {==}, st, eg, cc, ec)
    case T.LHeadU{}:
      L2.gd_header_steps(T.LHeadU{}, {==}, st, eg, cc, ec)
    case T.LHeadR{}:
      L2.gd_header_steps(T.LHeadR{}, {==}, st, eg, cc, ec)
    case T.LArr{}:
      L2.gd_value_steps(T.LArr{}, {==}, st, eg, cc, ec)
    case T.LArrC{}:
      L2.gd_value_steps(T.LArrC{}, {==}, st, eg, cc, ec)
    case T.LInl{}:
      L2.gd_value_steps(T.LInl{}, {==}, st, eg, cc, ec)
    case T.LInlK{}:
      L2.gd_value_steps(T.LInlK{}, {==}, st, eg, cc, ec)
    case T.LInlC{}:
      L2.gd_value_steps(T.LInlC{}, {==}, st, eg, cc, ec)
    case T.LSink{}:
      L2.gd_value_steps(T.LSink{}, {==}, st, eg, cc, ec)

# one character, the state read off
def gd.onst(
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.read.on.st(st, cc)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.on(lex, T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead}, cc,
        eg, ec)

# a byte-order mark is dropped
def gd.sbom(
  bom: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.read.step.bom(bom, st, cc)) == True{} : Bool}:
  match bom:
    case True{}:
      eg
    case False{}:
      gd.onst(st, cc, eg, ec)

# the first character may be a byte-order mark
def gd.slead(
  lead: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.read.step.lead(lead, st, cc)) == True{} : Bool}:
  match lead:
    case False{}:
      gd.onst(st, cc, eg, ec)
    case True{}:
      gd.sbom(U32.is_eq(Char.to_u32(cc), 65279), st, cc, eg, ec)

# one character of the document by the full step
def gd.step(
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.read.step(st, cc)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.slead(lead, T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab,
        False{}},
        cc, eg, ec)

# a held character is read once
def gd.ohold(
  hold: T.Hold,
  +st: T.St,
  +eg: {L2.good(st) == True{} : Bool},
  +eh: {L2.gd.hold(hold) == True{} : Bool}
) -> {L2.good(T.read.once.hold(hold, st)) == True{} : Bool}:
  match hold:
    case T.HNone{}:
      eg
    case T.HChar{+c0}:
      gd.step(st, c0, eg, eh)

# the held character, read off the state
def gd.once2(+st: T.St, +eg: {L2.good(st) == True{} : Bool}) -> {L2.good(T.read.once2(st)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.ohold(hold, T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, T.HNone{}, uni, left, arrtab,
        lead},
        gd.tt(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, T.HNone{}),
          gd.l(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg),
          gd.lx.mk(here, parts, buf, stack, T.HNone{},
            gd.lx.h(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf,
              stack,
              hold), eg)),
            gd.lx.p(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf,
              stack,
              hold), eg)),
            gd.lx.b(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf,
              stack,
              hold), eg)),
            gd.lx.s(here, parts, buf, stack, hold, gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf,
              stack,
              hold), eg)),
            {==})),
        gd.r(L2.gd.keys(stack), L2.gd.hold(hold), gd.lx.s1(here, parts, buf, stack, hold,
          gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, hold), eg))))

# one character, then a held one
def gd.once(
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.read.once(st, cc)) == True{} : Bool}:
  gd.once2(T.read.step(st, cc), gd.step(st, cc, eg, ec))

# the full step, from the fast step's state
def gd.fold(
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +buf: List<&2, Char>,
  +lex: T.Lex,
  +back: T.Lex,
  +qkind: T.QKind,
  +stack: List<&2, T.Ctx>,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +eg: {gd.gf(bad, rows, here, parts, buf, stack) == True{} : Bool},
  +cc: Char,
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.read.fast.old(bad, rows, heads, here, parts, buf, lex, back, qkind, stack, uni, left, arrtab,
  cc)) == True{} : Bool}:
  gd.once2(T.read.on.st(T.read.fast.st(bad, rows, heads, here, parts, buf, lex, back, qkind, stack, uni, left,
    arrtab), cc), gd.onst(T.read.fast.st(bad, rows, heads, here, parts, buf, lex, back, qkind, stack, uni, left,
      arrtab), cc, eg, ec))

# the character joins the buffer
def gd.fcons(
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +buf: List<&2, Char>,
  +lex: T.Lex,
  +back: T.Lex,
  +qkind: T.QKind,
  +stack: List<&2, T.Ctx>,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +eg: {gd.gf(bad, rows, here, parts, buf, stack) == True{} : Bool},
  +cc: Char,
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.read.fast.cons(bad, rows, heads, here, parts, buf, lex, back, qkind, stack, uni, left, arrtab,
  cc)) == True{} : Bool}:
  gd.tt(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, cc <> buf, stack, T.HNone{}),
    gd.l(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, T.HNone{}), eg),
    gd.lx.mk(here, parts, cc <> buf, stack, T.HNone{},
      gd.lx.h(here, parts, buf, stack, T.HNone{}, gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack,
        T.HNone{}), eg)),
      gd.lx.p(here, parts, buf, stack, T.HNone{}, gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack,
        T.HNone{}), eg)),
      gd.tt(T.wf.char(cc), L2.gd.cs(buf), ec, gd.lx.b(here, parts, buf, stack, T.HNone{},
        gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack, T.HNone{}), eg))),
      gd.lx.s(here, parts, buf, stack, T.HNone{}, gd.r(L2.gd.tr(bad, rows, stack), L2.gd.lx(here, parts, buf, stack,
        T.HNone{}), eg)),
      {==}))

# a control takes the full step; a plain character is kept
def gd.fpush(
  ctrl: Bool,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +buf: List<&2, Char>,
  +lex: T.Lex,
  +back: T.Lex,
  +qkind: T.QKind,
  +stack: List<&2, T.Ctx>,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +eg: {gd.gf(bad, rows, here, parts, buf, stack) == True{} : Bool},
  +cc: Char,
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.read.fast.push(ctrl, bad, rows, heads, here, parts, buf, lex, back, qkind, stack, uni, left, arrtab,
  cc)) == True{} : Bool}:
  match ctrl:
    case False{}:
      gd.fcons(bad, rows, heads, here, parts, buf, lex, back, qkind, stack, uni, left, arrtab, eg, cc, ec)
    case True{}:
      gd.fold(bad, rows, heads, here, parts, buf, lex, back, qkind, stack, uni, left, arrtab, eg, cc, ec)

# a backslash in a basic string takes the full step
def gd.fbbs(
  bs: Bool,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +buf: List<&2, Char>,
  +back: T.Lex,
  +stack: List<&2, T.Ctx>,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +eg: {gd.gf(bad, rows, here, parts, buf, stack) == True{} : Bool},
  +cc: Char,
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.read.fast.basic.bs(bs, bad, rows, heads, here, parts, buf, back, stack, uni, left, arrtab,
  cc)) == True{} : Bool}:
  match bs:
    case True{}:
      gd.fold(bad, rows, heads, here, parts, buf, T.LStr{}, back, T.QBasic{}, stack, uni, left, arrtab, eg, cc, ec)
    case False{}:
      gd.fpush(T.str.bad(Char.to_u32(cc), False{}), bad, rows, heads, here, parts, buf, T.LStr{}, back, T.QBasic{},
        stack, uni, left, arrtab, eg, cc, ec)

# a quote in a basic string takes the full step
def gd.fbasic(
  quote: Bool,
  +bs: Bool,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +buf: List<&2, Char>,
  +back: T.Lex,
  +stack: List<&2, T.Ctx>,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +eg: {gd.gf(bad, rows, here, parts, buf, stack) == True{} : Bool},
  +cc: Char,
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.read.fast.basic(quote, bs, bad, rows, heads, here, parts, buf, back, stack, uni, left, arrtab,
  cc)) == True{} : Bool}:
  match quote:
    case True{}:
      gd.fold(bad, rows, heads, here, parts, buf, T.LStr{}, back, T.QBasic{}, stack, uni, left, arrtab, eg, cc, ec)
    case False{}:
      gd.fbbs(bs, bad, rows, heads, here, parts, buf, back, stack, uni, left, arrtab, eg, cc, ec)

# a quote in a literal string takes the full step
def gd.flit(
  quote: Bool,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +buf: List<&2, Char>,
  +back: T.Lex,
  +stack: List<&2, T.Ctx>,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +eg: {gd.gf(bad, rows, here, parts, buf, stack) == True{} : Bool},
  +cc: Char,
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.read.fast.lit(quote, bad, rows, heads, here, parts, buf, back, stack, uni, left, arrtab,
  cc)) == True{} : Bool}:
  match quote:
    case True{}:
      gd.fold(bad, rows, heads, here, parts, buf, T.LStr{}, back, T.QLit{}, stack, uni, left, arrtab, eg, cc, ec)
    case False{}:
      gd.fpush(T.str.bad(Char.to_u32(cc), False{}), bad, rows, heads, here, parts, buf, T.LStr{}, back, T.QLit{},
        stack, uni, left, arrtab, eg, cc, ec)

# one character of a string on the fast step
def gd.fstr(
  qkind: T.QKind,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +buf: List<&2, Char>,
  +back: T.Lex,
  +stack: List<&2, T.Ctx>,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +eg: {gd.gf(bad, rows, here, parts, buf, stack) == True{} : Bool},
  +cc: Char,
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.read.fast.str(qkind, bad, rows, heads, here, parts, buf, back, stack, uni, left, arrtab,
  cc)) == True{} : Bool}:
  match qkind:
    case T.QBasic{}:
      gd.fbasic(Char.is_eq(cc, '"'), Char.is_eq(cc, '\\'), bad, rows, heads, here, parts, buf, back, stack, uni, left,
        arrtab, eg, cc, ec)
    case T.QLit{}:
      gd.flit(Char.is_eq(cc, '\''), bad, rows, heads, here, parts, buf, back, stack, uni, left, arrtab, eg, cc, ec)
    case T.QMulti{}:
      gd.fold(bad, rows, heads, here, parts, buf, T.LStr{}, back, T.QMulti{}, stack, uni, left, arrtab, eg, cc, ec)
    case T.QMultiLit{}:
      gd.fold(bad, rows, heads, here, parts, buf, T.LStr{}, back, T.QMultiLit{}, stack, uni, left, arrtab, eg, cc, ec)

# one character of a bare key on the fast step
def gd.fkey(
  ok: Bool,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +buf: List<&2, Char>,
  +back: T.Lex,
  +qkind: T.QKind,
  +stack: List<&2, T.Ctx>,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +eg: {gd.gf(bad, rows, here, parts, buf, stack) == True{} : Bool},
  +cc: Char,
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.read.fast.key(ok, bad, rows, heads, here, parts, buf, back, qkind, stack, uni, left, arrtab,
  cc)) == True{} : Bool}:
  match ok:
    case True{}:
      gd.fcons(bad, rows, heads, here, parts, buf, T.LKey{}, back, qkind, stack, uni, left, arrtab, eg, cc, ec)
    case False{}:
      gd.fold(bad, rows, heads, here, parts, buf, T.LKey{}, back, qkind, stack, uni, left, arrtab, eg, cc, ec)

# one character of a bare value on the fast step
def gd.fbare(
  delim: Bool,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +buf: List<&2, Char>,
  +back: T.Lex,
  +qkind: T.QKind,
  +stack: List<&2, T.Ctx>,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +eg: {gd.gf(bad, rows, here, parts, buf, stack) == True{} : Bool},
  +cc: Char,
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.read.fast.bare(delim, bad, rows, heads, here, parts, buf, back, qkind, stack, uni, left, arrtab,
  cc)) == True{} : Bool}:
  match delim:
    case True{}:
      gd.fold(bad, rows, heads, here, parts, buf, T.LBare{}, back, qkind, stack, uni, left, arrtab, eg, cc, ec)
    case False{}:
      gd.fcons(bad, rows, heads, here, parts, buf, T.LBare{}, back, qkind, stack, uni, left, arrtab, eg, cc, ec)

# one character of a comment on the fast step
def gd.fcom(
  ctl: Bool,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +buf: List<&2, Char>,
  +back: T.Lex,
  +qkind: T.QKind,
  +stack: List<&2, T.Ctx>,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +eg: {gd.gf(bad, rows, here, parts, buf, stack) == True{} : Bool},
  +cc: Char,
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.read.fast.com(ctl, bad, rows, heads, here, parts, buf, back, qkind, stack, uni, left, arrtab,
  cc)) == True{} : Bool}:
  match ctl:
    case True{}:
      gd.fold(bad, rows, heads, here, parts, buf, T.LCom{}, back, qkind, stack, uni, left, arrtab, eg, cc, ec)
    case False{}:
      eg

# a newline this state ignores
def gd.fkeep(
  keep: Bool,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +buf: List<&2, Char>,
  +lex: T.Lex,
  +back: T.Lex,
  +qkind: T.QKind,
  +stack: List<&2, T.Ctx>,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +eg: {gd.gf(bad, rows, here, parts, buf, stack) == True{} : Bool},
  +cc: Char,
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.read.fast.ws.keep(keep, bad, rows, heads, here, parts, buf, lex, back, qkind, stack, uni, left,
  arrtab, cc)) == True{} : Bool}:
  match keep:
    case True{}:
      eg
    case False{}:
      gd.fold(bad, rows, heads, here, parts, buf, lex, back, qkind, stack, uni, left, arrtab, eg, cc, ec)

# a newline, or the full step
def gd.fwsnl(
  nl: Bool,
  +keep: Bool,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +buf: List<&2, Char>,
  +lex: T.Lex,
  +back: T.Lex,
  +qkind: T.QKind,
  +stack: List<&2, T.Ctx>,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +eg: {gd.gf(bad, rows, here, parts, buf, stack) == True{} : Bool},
  +cc: Char,
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.read.fast.ws.nl(nl, keep, bad, rows, heads, here, parts, buf, lex, back, qkind, stack, uni, left,
  arrtab, cc)) == True{} : Bool}:
  match nl:
    case True{}:
      gd.fkeep(keep, bad, rows, heads, here, parts, buf, lex, back, qkind, stack, uni, left, arrtab, eg, cc, ec)
    case False{}:
      gd.fold(bad, rows, heads, here, parts, buf, lex, back, qkind, stack, uni, left, arrtab, eg, cc, ec)

# blank space this state ignores
def gd.fws(
  sp: Bool,
  +nl: Bool,
  +keep: Bool,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +buf: List<&2, Char>,
  +lex: T.Lex,
  +back: T.Lex,
  +qkind: T.QKind,
  +stack: List<&2, T.Ctx>,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +eg: {gd.gf(bad, rows, here, parts, buf, stack) == True{} : Bool},
  +cc: Char,
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.read.fast.ws(sp, nl, keep, bad, rows, heads, here, parts, buf, lex, back, qkind, stack, uni, left,
  arrtab, cc)) == True{} : Bool}:
  match sp:
    case True{}:
      eg
    case False{}:
      gd.fwsnl(nl, keep, bad, rows, heads, here, parts, buf, lex, back, qkind, stack, uni, left, arrtab, eg, cc, ec)

# the fast step, by the state
def gd.flex(
  lex: T.Lex,
  +qkind: T.QKind,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +buf: List<&2, Char>,
  +back: T.Lex,
  +stack: List<&2, T.Ctx>,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +eg: {gd.gf(bad, rows, here, parts, buf, stack) == True{} : Bool},
  +cc: Char,
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.read.fast.lex(lex, qkind, bad, rows, heads, here, parts, buf, back, stack, uni, left, arrtab,
  cc)) == True{} : Bool}:
  match lex:
    case T.LTop{}:
      gd.fws(T.ch.sp(cc), T.ch.nl(cc), True{}, bad, rows, heads, here, parts, buf, T.LTop{}, back, qkind, stack, uni,
        left, arrtab, eg, cc, ec)
    case T.LLine{}:
      gd.fws(T.ch.sp(cc), T.ch.nl(cc), False{}, bad, rows, heads, here, parts, buf, T.LLine{}, back, qkind, stack,
        uni, left, arrtab, eg, cc, ec)
    case T.LKey{}:
      gd.fkey(T.bare.at(cc), bad, rows, heads, here, parts, buf, back, qkind, stack, uni, left, arrtab, eg, cc, ec)
    case T.LKeyDot{}:
      gd.fold(bad, rows, heads, here, parts, buf, T.LKeyDot{}, back, qkind, stack, uni, left, arrtab, eg, cc, ec)
    case T.LAfter{}:
      gd.fws(T.ch.sp(cc), T.ch.nl(cc), False{}, bad, rows, heads, here, parts, buf, T.LAfter{}, back, qkind, stack,
        uni, left, arrtab, eg, cc, ec)
    case T.LKeyQ{}:
      gd.fold(bad, rows, heads, here, parts, buf, T.LKeyQ{}, back, qkind, stack, uni, left, arrtab, eg, cc, ec)
    case T.LKeyE{}:
      gd.fold(bad, rows, heads, here, parts, buf, T.LKeyE{}, back, qkind, stack, uni, left, arrtab, eg, cc, ec)
    case T.LKeyU{}:
      gd.fold(bad, rows, heads, here, parts, buf, T.LKeyU{}, back, qkind, stack, uni, left, arrtab, eg, cc, ec)
    case T.LVal{}:
      gd.fws(T.ch.sp(cc), T.ch.nl(cc), False{}, bad, rows, heads, here, parts, buf, T.LVal{}, back, qkind, stack, uni,
        left, arrtab, eg, cc, ec)
    case T.LQ{}:
      gd.fold(bad, rows, heads, here, parts, buf, T.LQ{}, back, qkind, stack, uni, left, arrtab, eg, cc, ec)
    case T.LQ2{}:
      gd.fold(bad, rows, heads, here, parts, buf, T.LQ2{}, back, qkind, stack, uni, left, arrtab, eg, cc, ec)
    case T.LStr{}:
      gd.fstr(qkind, bad, rows, heads, here, parts, buf, back, stack, uni, left, arrtab, eg, cc, ec)
    case T.LEsc{}:
      gd.fold(bad, rows, heads, here, parts, buf, T.LEsc{}, back, qkind, stack, uni, left, arrtab, eg, cc, ec)
    case T.LUni{}:
      gd.fold(bad, rows, heads, here, parts, buf, T.LUni{}, back, qkind, stack, uni, left, arrtab, eg, cc, ec)
    case T.LFold{}:
      gd.fold(bad, rows, heads, here, parts, buf, T.LFold{}, back, qkind, stack, uni, left, arrtab, eg, cc, ec)
    case T.LMq{}:
      gd.fold(bad, rows, heads, here, parts, buf, T.LMq{}, back, qkind, stack, uni, left, arrtab, eg, cc, ec)
    case T.LMqEnd{}:
      gd.fold(bad, rows, heads, here, parts, buf, T.LMqEnd{}, back, qkind, stack, uni, left, arrtab, eg, cc, ec)
    case T.LTrim{}:
      gd.fold(bad, rows, heads, here, parts, buf, T.LTrim{}, back, qkind, stack, uni, left, arrtab, eg, cc, ec)
    case T.LTrim2{}:
      gd.fold(bad, rows, heads, here, parts, buf, T.LTrim2{}, back, qkind, stack, uni, left, arrtab, eg, cc, ec)
    case T.LBare{}:
      gd.fbare(T.ch.delim(cc), bad, rows, heads, here, parts, buf, back, qkind, stack, uni, left, arrtab, eg, cc, ec)
    case T.LDate{}:
      gd.fold(bad, rows, heads, here, parts, buf, T.LDate{}, back, qkind, stack, uni, left, arrtab, eg, cc, ec)
    case T.LCom{}:
      gd.fcom(T.ch.ctl(cc), bad, rows, heads, here, parts, buf, back, qkind, stack, uni, left, arrtab, eg, cc, ec)
    case T.LHead{}:
      gd.fold(bad, rows, heads, here, parts, buf, T.LHead{}, back, qkind, stack, uni, left, arrtab, eg, cc, ec)
    case T.LHeadGap{}:
      gd.fold(bad, rows, heads, here, parts, buf, T.LHeadGap{}, back, qkind, stack, uni, left, arrtab, eg, cc, ec)
    case T.LHeadDot{}:
      gd.fold(bad, rows, heads, here, parts, buf, T.LHeadDot{}, back, qkind, stack, uni, left, arrtab, eg, cc, ec)
    case T.LHeadQ{}:
      gd.fold(bad, rows, heads, here, parts, buf, T.LHeadQ{}, back, qkind, stack, uni, left, arrtab, eg, cc, ec)
    case T.LHeadE{}:
      gd.fold(bad, rows, heads, here, parts, buf, T.LHeadE{}, back, qkind, stack, uni, left, arrtab, eg, cc, ec)
    case T.LHeadU{}:
      gd.fold(bad, rows, heads, here, parts, buf, T.LHeadU{}, back, qkind, stack, uni, left, arrtab, eg, cc, ec)
    case T.LHeadR{}:
      gd.fold(bad, rows, heads, here, parts, buf, T.LHeadR{}, back, qkind, stack, uni, left, arrtab, eg, cc, ec)
    case T.LArr{}:
      gd.fws(T.ch.sp(cc), T.ch.nl(cc), True{}, bad, rows, heads, here, parts, buf, T.LArr{}, back, qkind, stack, uni,
        left, arrtab, eg, cc, ec)
    case T.LArrC{}:
      gd.fws(T.ch.sp(cc), T.ch.nl(cc), True{}, bad, rows, heads, here, parts, buf, T.LArrC{}, back, qkind, stack, uni,
        left, arrtab, eg, cc, ec)
    case T.LInl{}:
      gd.fws(T.ch.sp(cc), T.ch.nl(cc), False{}, bad, rows, heads, here, parts, buf, T.LInl{}, back, qkind, stack, uni,
        left, arrtab, eg, cc, ec)
    case T.LInlK{}:
      gd.fws(T.ch.sp(cc), T.ch.nl(cc), False{}, bad, rows, heads, here, parts, buf, T.LInlK{}, back, qkind, stack,
        uni, left, arrtab, eg, cc, ec)
    case T.LInlC{}:
      gd.fws(T.ch.sp(cc), T.ch.nl(cc), False{}, bad, rows, heads, here, parts, buf, T.LInlC{}, back, qkind, stack,
        uni, left, arrtab, eg, cc, ec)
    case T.LSink{}:
      gd.fold(bad, rows, heads, here, parts, buf, T.LSink{}, back, qkind, stack, uni, left, arrtab, eg, cc, ec)

# the first character takes the full step
def gd.flead(
  lead: Bool,
  +lex: T.Lex,
  +qkind: T.QKind,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +buf: List<&2, Char>,
  +back: T.Lex,
  +stack: List<&2, T.Ctx>,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +eg: {gd.gf(bad, rows, here, parts, buf, stack) == True{} : Bool},
  +cc: Char,
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.read.fast.lead(lead, lex, qkind, bad, rows, heads, here, parts, buf, back, stack, uni, left, arrtab,
  cc)) == True{} : Bool}:
  match lead:
    case True{}:
      gd.once(T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, T.HNone{}, uni, left, arrtab, True{}},
        cc, eg, ec)
    case False{}:
      gd.flex(lex, qkind, bad, rows, heads, here, parts, buf, back, stack, uni, left, arrtab, eg, cc, ec)

# a held character takes the full step first
def gd.fhold(
  hd: T.Hold,
  +ld: Bool,
  +lx: T.Lex,
  +qk: T.QKind,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pt: List<&2, String>,
  +bf: List<&2, Char>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +at: Bool,
  +cc: Char,
  +ec: {T.wf.char(cc) == True{} : Bool},
  +eg: {L2.good(T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, hd, un, lf, at, ld}) == True{} : Bool}
) -> {L2.good(T.read.fast.hold(hd, ld, lx, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, cc)) == True{} : Bool}:
  match hd:
    case T.HChar{+held}:
      gd.once(T.read.once2(T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, T.HChar{held}, un, lf, at, ld}), cc,
        gd.once2(T.St{bd, rw, hs, he, pt, bf, lx, bk, qk, sk, T.HChar{held}, un, lf, at, ld}, eg), ec)
    case T.HNone{}:
      gd.flead(ld, lx, qk, bd, rw, hs, he, pt, bf, bk, sk, un, lf, at, eg, cc, ec)

# one character by the fast step
def gd.fast(
  +st: T.St,
  +cc: Char,
  +eg: {L2.good(st) == True{} : Bool},
  +ec: {T.wf.char(cc) == True{} : Bool}
) -> {L2.good(T.read.fast(st, cc)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      gd.fhold(hold, lead, lex, qkind, bad, rows, heads, here, parts, buf, back, stack, uni, left, arrtab, cc, ec, eg)

# a Bool whose negation holds is False
def gd.not.f(bb: Bool, +ee: {Bool.not(bb) == True{} : Bool}) -> {bb == False{} : Bool}:
  match bb:
    case True{}:
      Eq.bit.absurd(&2, {True{} == False{} : Bool}, ee)
    case False{}:
      {==}

# WP-R3: the induction over the text. Each character keeps doc.read's mode
# good (gd_mode_step); the text runs out in a scanning state, one after a
# carriage return, or an opening quote's, whose token is closed and held
# character read before gd_fin seals it, or in a string's span, which is an
# error. Every end that is not an error is well-formed

# counting from one more without wrapping counts from one less too
def gd.cm(
  ss: String,
  +mm: U32,
  +hz: {U32.is_zero(U32.add(mm, 1)) == False{} : Bool},
  +hc: {D1.counts(ss, U32.add(mm, 1)) == True{} : Bool}
) -> {D1.counts(ss, mm) == True{} : Bool}:
  match ss:
    case SNil{}:
      {==}
    case SCon{_h, +st}:
      gd.tt(Bool.not(U32.is_zero(U32.add(mm, 1))), D1.counts(st, U32.add(mm, 1)),
        Equal.cong(Bool, Bool, bb => Bool.not(bb), U32.is_zero(U32.add(mm, 1)), False{}, hz),
        gd.cm(st, U32.add(mm, 1),
          gd.not.f(U32.is_zero(U32.add(U32.add(mm, 1), 1)),
            gd.l(Bool.not(U32.is_zero(U32.add(U32.add(mm, 1), 1))), D1.counts(st, U32.add(U32.add(mm, 1), 1)), hc)),
          gd.r(Bool.not(U32.is_zero(U32.add(U32.add(mm, 1), 1))), D1.counts(st, U32.add(U32.add(mm, 1), 1)), hc)))

# the rest of a short text is short
def gd.short.tail(
  +hh: Char,
  +tt: String,
  +es: {D1.short(SCon{hh, tt}) == True{} : Bool}
) -> {D1.short(tt) == True{} : Bool}:
  gd.cm(tt, 0, {==}, gd.r(Bool.not(U32.is_zero(1)), D1.counts(tt, 1), es))
