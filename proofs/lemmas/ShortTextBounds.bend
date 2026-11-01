# strings, escapes and table paths stay short enough to count
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../src/arith.bend as Ar
import ../../laws/StringRenderEscapes.bend as L1
import ../../laws/defs/BareValueGrammar.bend as D1
import ./ControlEscapeText.bend as M1

# a comparison that has already found a difference answers False
def str.eq.off(aa: String, bb: String) -> {T.str.eq.step(aa, bb, False{}) == False{} : Bool}:
  match aa:
    case SNil{}:
      match bb:
        case SNil{}:
          {==}
        case SCon{_h, _t}:
          {==}
    case SCon{_x, _xt}:
      match bb:
        case SNil{}:
          {==}
        case SCon{_y, _yt}:
          {==}

# and the same once the characters compared last were told apart
def str.eq.off2(
  aa: String,
  bb: String,
  ff: Bool,
  ef: {False{} == ff : Bool}
) -> {T.str.eq.step(aa, bb, ff) == False{} : Bool}:
  %ef : {T.str.eq.step(aa, bb, _) == False{} : Bool}
  str.eq.off(aa, bb)

# the other half of a then that answered True
def wt.more(
  ok: Bool,
  -more: Unit -> Bool,
  ee: {T.wf.then(ok, more) == True{} : Bool}
) -> {more(Unit{}) == True{} : Bool}:
  match ok:
    case True{}:
      ee
    case False{}:
      Eq.bit.absurd(&2, {more(Unit{}) == True{} : Bool}, ee)

# the first half of a then that answered True
def wt.ok(
  ok: Bool,
  -more: Unit -> Bool,
  ee: {T.wf.then(ok, more) == True{} : Bool}
) -> {ok == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      ee

# a Nat count after these characters, from n
def plus(ss: String, nn: Nat) -> Nat:
  match ss:
    case SNil{}:
      nn
    case SCon{_hh, tt}:
      plus(tt, 1n+nn)

# a remainder by ten is below ten
def md(+nn: U32) -> {U32.is_lt(U32.mod(nn, 10), 10) == True{} : Bool}:
  Equal.trans(Bool, Cmp.is_lt(U32.cmp(U32.mod(nn, 10), 10)), Cmp.is_lt(Nat.cmp(U32.to_nat(U32.mod(nn, 10)), 10n)),
    True{},
    Equal.cong(Cmp, Bool, cc => Cmp.is_lt(cc), U32.cmp(U32.mod(nn, 10), 10),
      Nat.cmp(U32.to_nat(U32.mod(nn, 10)), 10n), Ar.u_cmp(U32.mod(nn, 10), 10)),
    Ar.u_mod(Unit{}, nn))

# both halves of an and
def cv.and2(
  aa: Bool,
  bb: Bool,
  ha: {aa == True{} : Bool},
  hb: {bb == True{} : Bool}
) -> {Bool.and(aa, bb) == True{} : Bool}:
  match aa:
    case True{}:
      hb
    case False{}:
      Eq.bit.absurd(&2, {Bool.and(False{}, bb) == True{} : Bool}, ha)

# a text short from one more is short from one less, when one more is no wrap
def cd.drop(
  ys: String,
  +mm: U32,
  +ez: {U32.is_zero(U32.add(mm, 1)) == False{} : Bool},
  +ee: {D1.counts(ys, U32.add(mm, 1)) == True{} : Bool}
) -> {D1.counts(ys, mm) == True{} : Bool}:
  match ys:
    case SNil{}:
      {==}
    case SCon{_h, +t}:
      cv.and2(Bool.not(U32.is_zero(U32.add(mm, 1))), D1.counts(t, U32.add(mm, 1)),
        Equal.cong(Bool, Bool, bb => Bool.not(bb), U32.is_zero(U32.add(mm, 1)), False{}, ez),
        cd.drop(t, U32.add(mm, 1), Eq.not.true(U32.is_zero(U32.add(U32.add(mm, 1), 1)),
          Eq.and.left(Bool.not(U32.is_zero(U32.add(U32.add(mm, 1), 1))), D1.counts(t, U32.add(U32.add(mm, 1), 1)),
            ee)),
          Eq.and.right(Bool.not(U32.is_zero(U32.add(U32.add(mm, 1), 1))), D1.counts(t, U32.add(U32.add(mm, 1), 1)),
            ee)))

# the end of a short text is short
def cd.dp(
  aa: String,
  +bb: String,
  +mm: U32,
  +ee: {D1.counts(String.append(aa, bb), mm) == True{} : Bool}
) -> {D1.counts(bb, mm) == True{} : Bool}:
  match aa:
    case SNil{}:
      ee
    case SCon{_h, +t}:
      cd.drop(bb, mm, Eq.not.true(U32.is_zero(U32.add(mm, 1)), Eq.and.left(Bool.not(U32.is_zero(U32.add(mm, 1))),
        D1.counts(String.append(t, bb), U32.add(mm, 1)), ee)),
        cd.dp(t, bb, U32.add(mm, 1), Eq.and.right(Bool.not(U32.is_zero(U32.add(mm, 1))),
          D1.counts(String.append(t, bb), U32.add(mm, 1)), ee)))

# Every string's bound, and every table path's, from the bound on the whole
# text: a piece of a short text is short, from either end, and a string's
# escapes are at least as many characters as the string.

# the start of a short text is short
def cn.pf(
  aa: String,
  +bb: String,
  +mm: U32,
  +ee: {D1.counts(String.append(aa, bb), mm) == True{} : Bool}
) -> {D1.counts(aa, mm) == True{} : Bool}:
  match aa:
    case SNil{}:
      {==}
    case SCon{_h, +t}:
      cv.and2(Bool.not(U32.is_zero(U32.add(mm, 1))), D1.counts(t, U32.add(mm, 1)),
        Eq.and.left(Bool.not(U32.is_zero(U32.add(mm, 1))), D1.counts(String.append(t, bb), U32.add(mm, 1)), ee),
        cn.pf(t, bb, U32.add(mm, 1), Eq.and.right(Bool.not(U32.is_zero(U32.add(mm, 1))), D1.counts(String.append(t,
          bb),
          U32.add(mm, 1)), ee)))

# a character's escape is at least one character, whatever its class
def esc.ne.k(
  kk: T.BK,
  +cc: Char,
  +uu: U32
) -> {String.is_empty(String.from_list(List.reverse(&2, Char, T.basic.disp(kk,
  cc, uu, [])))) == False{} : Bool}:
  match kk:
    case T.BKCh{}:
      {==}
    case T.BKEsc{_m}:
      {==}
    case T.BKHex{}:
      {==}

# a character's escape is at least one character
def esc.ne(+cc: Char) -> {String.is_empty(L1.esc(cc)) == False{} : Bool}:
  esc.ne.k(T.basic.cls(Char.to_u32(cc)), cc, Char.to_u32(cc))

# a text of at least one character, then more: counting it passes one
def esc.cnt(
  ee: String,
  +ww: String,
  +mm: U32,
  ne: {String.is_empty(ee) == False{} : Bool},
  +hh: {D1.counts(String.append(ee, ww), mm) == True{} : Bool}
) -> {Bool.and(Bool.not(U32.is_zero(U32.add(mm, 1))), D1.counts(ww, U32.add(mm, 1))) == True{} : Bool}:
  match ee:
    case SNil{}:
      Eq.bit.absurd2(&2, {Bool.and(Bool.not(U32.is_zero(U32.add(mm, 1))), D1.counts(ww, U32.add(mm, 1))) == True{}
        : Bool}, ne)
    case SCon{_h, +r}:
      cv.and2(Bool.not(U32.is_zero(U32.add(mm, 1))), D1.counts(ww, U32.add(mm, 1)),
        Eq.and.left(Bool.not(U32.is_zero(U32.add(mm, 1))), D1.counts(String.append(r, ww), U32.add(mm, 1)), hh),
        cd.dp(r, ww, U32.add(mm, 1), Eq.and.right(Bool.not(U32.is_zero(U32.add(mm, 1))), D1.counts(String.append(r,
          ww),
          U32.add(mm, 1)), hh)))

# a string whose escapes are short is short
def esc.cs(
  ss: String,
  +mm: U32,
  +hh: {D1.counts(L1.escs(ss), mm) == True{} : Bool}
) -> {D1.counts(ss, mm) == True{} : Bool}:
  match ss:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +h2 = {esc.cnt(L1.esc(c), L1.escs(t), mm, esc.ne(c), hh) : {Bool.and(Bool.not(U32.is_zero(U32.add(mm, 1))),
        D1.counts(L1.escs(t), U32.add(mm, 1))) == True{} : Bool}}
      cv.and2(Bool.not(U32.is_zero(U32.add(mm, 1))), D1.counts(t, U32.add(mm, 1)),
        Eq.and.left(Bool.not(U32.is_zero(U32.add(mm, 1))), D1.counts(L1.escs(t), U32.add(mm, 1)), h2),
        esc.cs(t, U32.add(mm, 1), Eq.and.right(Bool.not(U32.is_zero(U32.add(mm, 1))), D1.counts(L1.escs(t),
          U32.add(mm, 1)), h2)))

# a string whose basic form starts a short text is short
def sb(
  +ss: String,
  +ww: String,
  +hh: {D1.counts(String.append(T.key.basic(ss), ww), 0) == True{} : Bool}
) -> {D1.short(ss) == True{} : Bool}:
  +x1 = {String.append(String.append(L1.escs(ss), "\""), ww) : String}
  +c1 = {Equal.trans(Bool, D1.counts(SCon{'"', x1}, 0), D1.counts(String.append(T.key.basic(ss), ww), 0), True{},
    Equal.cong(String, Bool, x2 => D1.counts(String.append(x2, ww), 0), "\"" ++ L1.escs(ss) ++ "\"",
      T.key.basic(ss),
      Equal.sym(String, T.key.basic(ss), "\"" ++ L1.escs(ss) ++ "\"", L1.basic_escs(ss))),
        hh) : {D1.counts(SCon{'"', x1}, 0) == True{} : Bool}}
  esc.cs(ss, 0, cn.pf(L1.escs(ss), "\"", 0, cn.pf(String.append(L1.escs(ss), "\""), ww, 0, cd.dp("\"", x1, 0, c1))))

# and so is a span whose quoted form starts one
def ssp(
  +src: String,
  +kk: U32,
  +ww: String,
  +hh: {D1.counts(String.append(T.span.quote(src, kk), ww), 0) == True{} : Bool}
) -> {D1.short(T.span.str(src, kk, U32.is_zero(kk))) == True{} : Bool}:
  sb(T.span.str(src, kk, U32.is_zero(kk)), ww, Equal.trans(Bool, D1.counts(String.append(T.key.basic(T.span.str(src,
    kk, U32.is_zero(kk))), ww), 0),
    D1.counts(String.append(T.span.quote(src, kk), ww), 0), True{}, Equal.cong(String, Bool,
      x2 => D1.counts(String.append(x2, ww), 0),
    T.key.basic(T.span.str(src, kk, U32.is_zero(kk))), T.span.quote(src, kk), Equal.sym(String, T.span.quote(src, kk),
    T.key.basic(T.span.str(src, kk, U32.is_zero(kk))), L1.span_quote_basic(src, kk))), hh))

# which list sg reads: an array's items, or an inline table's pairs
def sg.at(md: Bool) -> T.WfAt:
  match md:
    case False{}:
      T.WfItems{}
    case True{}:
      T.WfInl{}

# every string in the values of an array or an inline table, as render.go
# writes them, is short when their text is
def sg(
  vs: List<&2, T.Val>,
  md: Bool,
  +hw: {T.wf.go(vs, sg.at(md)) == True{} : Bool},
  +hh: {D1.counts(T.render.go(vs, ", ", False{}), 0) == True{} : Bool}
) -> {D1.cv.shorts(vs) == True{} : Bool}:
  match vs md:
    case [] _m:
      {==}
    case T.VPair{+kk, T.VStr{+a1}} <> +t True{}:
      cv.and2(D1.short(a1), D1.cv.shorts(t), sb(a1, String.append(T.render.suf(", ", False{}, List.is_empty(&2,
        T.Val, t)), T.render.go(t, ", ", False{})), cd.dp(" = ", String.append(T.render.atom(T.VStr{a1}),
        String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{}))), 0,
        cd.dp(T.key(kk), String.append(" = ", String.append(T.render.atom(T.VStr{a1}), String.append(T.render.suf(", ",
        False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{})))), 0, hh))), sg(t, True{},
        wt.more(Bool.and(T.wf.atom(T.VStr{a1}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfInl{}), hw),
        cd.dp(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{}), 0,
        cd.dp(T.render.atom(T.VStr{a1}), String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)),
        T.render.go(t, ", ", False{})), 0, cd.dp(" = ", String.append(T.render.atom(T.VStr{a1}),
        String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{}))), 0,
        cd.dp(T.key(kk), String.append(" = ", String.append(T.render.atom(T.VStr{a1}), String.append(T.render.suf(", ",
        False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{})))), 0, hh))))))
    case T.VPair{+kk, T.VStr{+a1}} <> +t False{}:
      Eq.bit.absurd(&2, {D1.cv.shorts(T.VPair{kk, T.VStr{a1}} <> t) == True{} : Bool}, hw)
    case T.VPair{+kk, T.VSpan{+a1, +a2}} <> +t True{}:
      cv.and2(D1.short(T.span.str(a1, a2, U32.is_zero(a2))), D1.cv.shorts(t), ssp(a1, a2,
        String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{})),
        cd.dp(" = ", String.append(T.render.atom(T.VSpan{a1, a2}), String.append(T.render.suf(", ", False{},
        List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{}))), 0, cd.dp(T.key(kk), String.append(" = ",
        String.append(T.render.atom(T.VSpan{a1, a2}), String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val,
        t)), T.render.go(t, ", ", False{})))), 0, hh))), sg(t, True{}, wt.more(Bool.and(T.wf.atom(T.VSpan{a1, a2}),
        T.wf.key(kk, t)), _u => T.wf.go(t, T.WfInl{}), hw), cd.dp(T.render.suf(", ", False{}, List.is_empty(&2, T.Val,
        t)), T.render.go(t, ", ", False{}), 0, cd.dp(T.render.atom(T.VSpan{a1, a2}), String.append(T.render.suf(", ",
        False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{})), 0, cd.dp(" = ",
        String.append(T.render.atom(T.VSpan{a1, a2}), String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val,
        t)), T.render.go(t, ", ", False{}))), 0, cd.dp(T.key(kk), String.append(" = ",
        String.append(T.render.atom(T.VSpan{a1, a2}), String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val,
        t)), T.render.go(t, ", ", False{})))), 0, hh))))))
    case T.VPair{+kk, T.VSpan{+a1, +a2}} <> +t False{}:
      Eq.bit.absurd(&2, {D1.cv.shorts(T.VPair{kk, T.VSpan{a1, a2}} <> t) == True{} : Bool}, hw)
    case T.VPair{+kk, T.VInt{+a1, +a2}} <> +t True{}:
      sg(t, True{}, wt.more(Bool.and(T.wf.atom(T.VInt{a1, a2}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfInl{}), hw),
        cd.dp(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{}), 0,
        cd.dp(T.render.atom(T.VInt{a1, a2}), String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)),
        T.render.go(t, ", ", False{})), 0, cd.dp(" = ", String.append(T.render.atom(T.VInt{a1, a2}),
        String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{}))), 0,
        cd.dp(T.key(kk), String.append(" = ", String.append(T.render.atom(T.VInt{a1, a2}),
        String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{})))), 0,
        hh)))))
    case T.VPair{+kk, T.VInt{+a1, +a2}} <> +t False{}:
      Eq.bit.absurd(&2, {D1.cv.shorts(T.VPair{kk, T.VInt{a1, a2}} <> t) == True{} : Bool}, hw)
    case T.VPair{+kk, T.VFlo{+a1, +a2}} <> +t True{}:
      sg(t, True{}, wt.more(Bool.and(T.wf.atom(T.VFlo{a1, a2}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfInl{}), hw),
        cd.dp(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{}), 0,
        cd.dp(T.render.atom(T.VFlo{a1, a2}), String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)),
        T.render.go(t, ", ", False{})), 0, cd.dp(" = ", String.append(T.render.atom(T.VFlo{a1, a2}),
        String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{}))), 0,
        cd.dp(T.key(kk), String.append(" = ", String.append(T.render.atom(T.VFlo{a1, a2}),
        String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{})))), 0,
        hh)))))
    case T.VPair{+kk, T.VFlo{+a1, +a2}} <> +t False{}:
      Eq.bit.absurd(&2, {D1.cv.shorts(T.VPair{kk, T.VFlo{a1, a2}} <> t) == True{} : Bool}, hw)
    case T.VPair{+kk, T.VBool{+a1}} <> +t True{}:
      sg(t, True{}, wt.more(Bool.and(T.wf.atom(T.VBool{a1}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfInl{}), hw),
        cd.dp(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{}), 0,
        cd.dp(T.render.atom(T.VBool{a1}), String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)),
        T.render.go(t, ", ", False{})), 0, cd.dp(" = ", String.append(T.render.atom(T.VBool{a1}),
        String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{}))), 0,
        cd.dp(T.key(kk), String.append(" = ", String.append(T.render.atom(T.VBool{a1}), String.append(T.render.suf(", ",
        False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{})))), 0, hh)))))
    case T.VPair{+kk, T.VBool{+a1}} <> +t False{}:
      Eq.bit.absurd(&2, {D1.cv.shorts(T.VPair{kk, T.VBool{a1}} <> t) == True{} : Bool}, hw)
    case T.VPair{+kk, T.VWhen{+a1}} <> +t True{}:
      sg(t, True{}, wt.more(Bool.and(T.wf.atom(T.VWhen{a1}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfInl{}), hw),
        cd.dp(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{}), 0,
        cd.dp(T.render.atom(T.VWhen{a1}), String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)),
        T.render.go(t, ", ", False{})), 0, cd.dp(" = ", String.append(T.render.atom(T.VWhen{a1}),
        String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{}))), 0,
        cd.dp(T.key(kk), String.append(" = ", String.append(T.render.atom(T.VWhen{a1}), String.append(T.render.suf(", ",
        False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{})))), 0, hh)))))
    case T.VPair{+kk, T.VWhen{+a1}} <> +t False{}:
      Eq.bit.absurd(&2, {D1.cv.shorts(T.VPair{kk, T.VWhen{a1}} <> t) == True{} : Bool}, hw)
    case T.VPair{+kk, T.VArr{+a1}} <> +t True{}:
      +hin = {wt.more(T.wf.key(kk, t), _u => T.wf.then(T.wf.go(a1, T.WfItems{}), _v => T.wf.go(t, T.WfInl{})), hw)
        : {T.wf.then(T.wf.go(a1, T.WfItems{}), _v => T.wf.go(t, T.WfInl{})) == True{} : Bool}}
      cv.and2(D1.cv.shorts(a1), D1.cv.shorts(t),
        sg(a1, False{}, wt.ok(T.wf.go(a1, T.WfItems{}), _v => T.wf.go(t, T.WfInl{}), hin), cn.pf(T.render.go(a1, ", ",
          False{}), String.append("]", String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)),
          T.render.go(t, ", ", False{}))), 0, cd.dp(" = [", String.append(T.render.go(a1, ", ", False{}),
          String.append("]", String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)), T.render.go(t,
          ", ", False{})))), 0, cd.dp(T.key(kk), String.append(" = [", String.append(T.render.go(a1, ", ", False{}),
          String.append("]", String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)), T.render.go(t,
          ", ", False{}))))), 0, hh)))),
        sg(t, True{}, wt.more(T.wf.go(a1, T.WfItems{}), _v => T.wf.go(t, T.WfInl{}), hin), cd.dp(T.render.suf(", ",
          False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{}), 0, cd.dp("]",
          String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{})), 0,
          cd.dp(T.render.go(a1, ", ", False{}), String.append("]", String.append(T.render.suf(", ", False{},
          List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{}))), 0, cd.dp(" = [", String.append(T.render.go(a1,
          ", ", False{}), String.append("]", String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)),
          T.render.go(t, ", ", False{})))), 0, cd.dp(T.key(kk), String.append(" = [", String.append(T.render.go(a1,
          ", ", False{}), String.append("]", String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)),
          T.render.go(t, ", ", False{}))))), 0, hh)))))))
    case T.VPair{+kk, T.VArr{+a1}} <> +t False{}:
      Eq.bit.absurd(&2, {D1.cv.shorts(T.VPair{kk, T.VArr{a1}} <> t) == True{} : Bool}, hw)
    case T.VPair{+kk, T.VInl{+a1}} <> +t True{}:
      +hin = {wt.more(T.wf.key(kk, t), _u => T.wf.then(T.wf.go(a1, T.WfInl{}), _v => T.wf.go(t, T.WfInl{})), hw)
        : {T.wf.then(T.wf.go(a1, T.WfInl{}), _v => T.wf.go(t, T.WfInl{})) == True{} : Bool}}
      cv.and2(D1.cv.shorts(a1), D1.cv.shorts(t),
        sg(a1, True{}, wt.ok(T.wf.go(a1, T.WfInl{}), _v => T.wf.go(t, T.WfInl{}), hin), cn.pf(T.render.go(a1, ", ",
          False{}), String.append("}", String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)),
          T.render.go(t, ", ", False{}))), 0, cd.dp(" = {", String.append(T.render.go(a1, ", ", False{}),
          String.append("}", String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)), T.render.go(t,
          ", ", False{})))), 0, cd.dp(T.key(kk), String.append(" = {", String.append(T.render.go(a1, ", ", False{}),
          String.append("}", String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)), T.render.go(t,
          ", ", False{}))))), 0, hh)))),
        sg(t, True{}, wt.more(T.wf.go(a1, T.WfInl{}), _v => T.wf.go(t, T.WfInl{}), hin), cd.dp(T.render.suf(", ",
          False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{}), 0, cd.dp("}",
          String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{})), 0,
          cd.dp(T.render.go(a1, ", ", False{}), String.append("}", String.append(T.render.suf(", ", False{},
          List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{}))), 0, cd.dp(" = {", String.append(T.render.go(a1,
          ", ", False{}), String.append("}", String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)),
          T.render.go(t, ", ", False{})))), 0, cd.dp(T.key(kk), String.append(" = {", String.append(T.render.go(a1,
          ", ", False{}), String.append("}", String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)),
          T.render.go(t, ", ", False{}))))), 0, hh)))))))
    case T.VPair{+kk, T.VInl{+a1}} <> +t False{}:
      Eq.bit.absurd(&2, {D1.cv.shorts(T.VPair{kk, T.VInl{a1}} <> t) == True{} : Bool}, hw)
    case T.VPair{+kk, T.VHead{+a1, +a2}} <> +t True{}:
      Eq.bit.absurd(&2, {D1.cv.shorts(T.VPair{kk, T.VHead{a1, a2}} <> t) == True{} : Bool}, hw)
    case T.VPair{+kk, T.VHead{+a1, +a2}} <> +t False{}:
      Eq.bit.absurd(&2, {D1.cv.shorts(T.VPair{kk, T.VHead{a1, a2}} <> t) == True{} : Bool}, hw)
    case T.VPair{+kk, T.VAot{+a1, +a2}} <> +t True{}:
      Eq.bit.absurd(&2, {D1.cv.shorts(T.VPair{kk, T.VAot{a1, a2}} <> t) == True{} : Bool}, hw)
    case T.VPair{+kk, T.VAot{+a1, +a2}} <> +t False{}:
      Eq.bit.absurd(&2, {D1.cv.shorts(T.VPair{kk, T.VAot{a1, a2}} <> t) == True{} : Bool}, hw)
    case T.VPair{+kk, T.VAots{+a1, +a2}} <> +t True{}:
      Eq.bit.absurd(&2, {D1.cv.shorts(T.VPair{kk, T.VAots{a1, a2}} <> t) == True{} : Bool}, hw)
    case T.VPair{+kk, T.VAots{+a1, +a2}} <> +t False{}:
      Eq.bit.absurd(&2, {D1.cv.shorts(T.VPair{kk, T.VAots{a1, a2}} <> t) == True{} : Bool}, hw)
    case T.VPair{+kk, T.VPair{+a1, +a2}} <> +t True{}:
      Eq.bit.absurd(&2, {D1.cv.shorts(T.VPair{kk, T.VPair{a1, a2}} <> t) == True{} : Bool}, hw)
    case T.VPair{+kk, T.VPair{+a1, +a2}} <> +t False{}:
      Eq.bit.absurd(&2, {D1.cv.shorts(T.VPair{kk, T.VPair{a1, a2}} <> t) == True{} : Bool}, hw)
    case T.VStr{+a1} <> +t True{}:
      Eq.bit.absurd(&2, {D1.cv.shorts(T.VStr{a1} <> t) == True{} : Bool}, hw)
    case T.VStr{+a1} <> +t False{}:
      cv.and2(D1.short(a1), D1.cv.shorts(t), sb(a1, String.append(T.render.suf(", ", False{}, List.is_empty(&2,
        T.Val, t)), T.render.go(t, ", ", False{})), hh), sg(t, False{}, wt.more(T.wf.atom(T.VStr{a1}), _u => T.wf.go(t,
        T.WfItems{}), hw), cd.dp(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ",
        False{}), 0, cd.dp(T.render.atom(T.VStr{a1}), String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val,
        t)), T.render.go(t, ", ", False{})), 0, hh))))
    case T.VSpan{+a1, +a2} <> +t True{}:
      Eq.bit.absurd(&2, {D1.cv.shorts(T.VSpan{a1, a2} <> t) == True{} : Bool}, hw)
    case T.VSpan{+a1, +a2} <> +t False{}:
      cv.and2(D1.short(T.span.str(a1, a2, U32.is_zero(a2))), D1.cv.shorts(t), ssp(a1, a2,
        String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{})), hh),
        sg(t, False{}, wt.more(T.wf.atom(T.VSpan{a1, a2}), _u => T.wf.go(t, T.WfItems{}), hw), cd.dp(T.render.suf(", ",
        False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{}), 0, cd.dp(T.render.atom(T.VSpan{a1, a2}),
        String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{})), 0,
        hh))))
    case T.VInt{+a1, +a2} <> +t True{}:
      Eq.bit.absurd(&2, {D1.cv.shorts(T.VInt{a1, a2} <> t) == True{} : Bool}, hw)
    case T.VInt{+a1, +a2} <> +t False{}:
      sg(t, False{}, wt.more(T.wf.atom(T.VInt{a1, a2}), _u => T.wf.go(t, T.WfItems{}), hw), cd.dp(T.render.suf(", ",
        False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{}), 0, cd.dp(T.render.atom(T.VInt{a1, a2}),
        String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{})), 0, hh)))
    case T.VFlo{+a1, +a2} <> +t True{}:
      Eq.bit.absurd(&2, {D1.cv.shorts(T.VFlo{a1, a2} <> t) == True{} : Bool}, hw)
    case T.VFlo{+a1, +a2} <> +t False{}:
      sg(t, False{}, wt.more(T.wf.atom(T.VFlo{a1, a2}), _u => T.wf.go(t, T.WfItems{}), hw), cd.dp(T.render.suf(", ",
        False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{}), 0, cd.dp(T.render.atom(T.VFlo{a1, a2}),
        String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{})), 0, hh)))
    case T.VBool{+a1} <> +t True{}:
      Eq.bit.absurd(&2, {D1.cv.shorts(T.VBool{a1} <> t) == True{} : Bool}, hw)
    case T.VBool{+a1} <> +t False{}:
      sg(t, False{}, wt.more(T.wf.atom(T.VBool{a1}), _u => T.wf.go(t, T.WfItems{}), hw), cd.dp(T.render.suf(", ",
        False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{}), 0, cd.dp(T.render.atom(T.VBool{a1}),
        String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{})), 0, hh)))
    case T.VWhen{+a1} <> +t True{}:
      Eq.bit.absurd(&2, {D1.cv.shorts(T.VWhen{a1} <> t) == True{} : Bool}, hw)
    case T.VWhen{+a1} <> +t False{}:
      sg(t, False{}, wt.more(T.wf.atom(T.VWhen{a1}), _u => T.wf.go(t, T.WfItems{}), hw), cd.dp(T.render.suf(", ",
        False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{}), 0, cd.dp(T.render.atom(T.VWhen{a1}),
        String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{})), 0, hh)))
    case T.VArr{+a1} <> +t True{}:
      Eq.bit.absurd(&2, {D1.cv.shorts(T.VArr{a1} <> t) == True{} : Bool}, hw)
    case T.VArr{+a1} <> +t False{}:
      cv.and2(D1.cv.shorts(a1), D1.cv.shorts(t),
        sg(a1, False{}, wt.ok(T.wf.go(a1, T.WfItems{}), _v => T.wf.go(t, T.WfItems{}), hw), cn.pf(T.render.go(a1, ", ",
          False{}), String.append("]", String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)),
          T.render.go(t, ", ", False{}))), 0, cd.dp("[", String.append(T.render.go(a1, ", ", False{}),
          String.append("]", String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)), T.render.go(t,
          ", ", False{})))), 0, hh))),
        sg(t, False{}, wt.more(T.wf.go(a1, T.WfItems{}), _v => T.wf.go(t, T.WfItems{}), hw), cd.dp(T.render.suf(", ",
          False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{}), 0, cd.dp("]",
          String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{})), 0,
          cd.dp(T.render.go(a1, ", ", False{}), String.append("]", String.append(T.render.suf(", ", False{},
          List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{}))), 0, cd.dp("[", String.append(T.render.go(a1,
          ", ", False{}), String.append("]", String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)),
          T.render.go(t, ", ", False{})))), 0, hh))))))
    case T.VInl{+a1} <> +t True{}:
      Eq.bit.absurd(&2, {D1.cv.shorts(T.VInl{a1} <> t) == True{} : Bool}, hw)
    case T.VInl{+a1} <> +t False{}:
      cv.and2(D1.cv.shorts(a1), D1.cv.shorts(t),
        sg(a1, True{}, wt.ok(T.wf.go(a1, T.WfInl{}), _v => T.wf.go(t, T.WfItems{}), hw), cn.pf(T.render.go(a1, ", ",
          False{}), String.append("}", String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)),
          T.render.go(t, ", ", False{}))), 0, cd.dp("{", String.append(T.render.go(a1, ", ", False{}),
          String.append("}", String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)), T.render.go(t,
          ", ", False{})))), 0, hh))),
        sg(t, False{}, wt.more(T.wf.go(a1, T.WfInl{}), _v => T.wf.go(t, T.WfItems{}), hw), cd.dp(T.render.suf(", ",
          False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{}), 0, cd.dp("}",
          String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{})), 0,
          cd.dp(T.render.go(a1, ", ", False{}), String.append("}", String.append(T.render.suf(", ", False{},
          List.is_empty(&2, T.Val, t)), T.render.go(t, ", ", False{}))), 0, cd.dp("{", String.append(T.render.go(a1,
          ", ", False{}), String.append("}", String.append(T.render.suf(", ", False{}, List.is_empty(&2, T.Val, t)),
          T.render.go(t, ", ", False{})))), 0, hh))))))
    case T.VHead{+a1, +a2} <> +t True{}:
      Eq.bit.absurd(&2, {D1.cv.shorts(T.VHead{a1, a2} <> t) == True{} : Bool}, hw)
    case T.VHead{+a1, +a2} <> +t False{}:
      Eq.bit.absurd(&2, {D1.cv.shorts(T.VHead{a1, a2} <> t) == True{} : Bool}, hw)
    case T.VAot{+a1, +a2} <> +t True{}:
      Eq.bit.absurd(&2, {D1.cv.shorts(T.VAot{a1, a2} <> t) == True{} : Bool}, hw)
    case T.VAot{+a1, +a2} <> +t False{}:
      Eq.bit.absurd(&2, {D1.cv.shorts(T.VAot{a1, a2} <> t) == True{} : Bool}, hw)
    case T.VAots{+a1, +a2} <> +t True{}:
      Eq.bit.absurd(&2, {D1.cv.shorts(T.VAots{a1, a2} <> t) == True{} : Bool}, hw)
    case T.VAots{+a1, +a2} <> +t False{}:
      Eq.bit.absurd(&2, {D1.cv.shorts(T.VAots{a1, a2} <> t) == True{} : Bool}, hw)
