# words after a sign or minus that a number scan refuses
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/NumSignedZeroUnderscore.bend as L1
import ../../laws/NumTwoSigns.bend as L2
import ../../laws/NumZeroUnderscore.bend as L3
import ../../laws/defs/DocumentSameness.bend as D1
import ../../laws/defs/RefusedScan.bend as D2
import ./FreshNamesInRows.bend as M1
import ./PickAndDigitSteps.bend as M2
import ./ShortTextBounds.bend as M3
import ./ValueSelfEquality.bend as M4

# a scan refused with this reason
def num.dead(why: String) -> T.Num:
  T.Num{T.NBad{}, T.Plus{}, 10, [], False{}, False{}, why}

# the claim that a refused scan stays as it is
def num.Stays(rest: List<&2, Char>, +why: String) -> Type:
  {T.num.go(rest, num.dead(why)) == num.dead(why) : T.Num}

# a refused scan stays refused whatever follows, by induction on what follows
def num.stays(rest: List<&2, Char>, +why: String) -> num.Stays(rest, why):
  match rest:
    case []:
      {==}
    case _h <> tt:
      num.stays(tt, why)

# each pair of signs is refused at its second sign, and stays refused
def L2.num_two_signs(s1, s2, rest):
  match s1 s2:
    case T.Plus{} T.Plus{}:
      Equal.cong(T.Num, Bool,
        xx => D2.refused(T.num.fin(xx, '+' <> '+' <> rest)),
        T.num.go(rest, num.dead("invalid number")), num.dead("invalid number"),
        num.stays(rest, "invalid number"))
    case T.Plus{} T.Minus{}:
      Equal.cong(T.Num, Bool,
        xx => D2.refused(T.num.fin(xx, '+' <> '-' <> rest)),
        T.num.go(rest, num.dead("invalid number")), num.dead("invalid number"),
        num.stays(rest, "invalid number"))
    case T.Minus{} T.Plus{}:
      Equal.cong(T.Num, Bool,
        xx => D2.refused(T.num.fin(xx, '-' <> '+' <> rest)),
        T.num.go(rest, num.dead("invalid number")), num.dead("invalid number"),
        num.stays(rest, "invalid number"))
    case T.Minus{} T.Minus{}:
      Equal.cong(T.Num, Bool,
        xx => D2.refused(T.num.fin(xx, '-' <> '-' <> rest)),
        T.num.go(rest, num.dead("invalid number")), num.dead("invalid number"),
        num.stays(rest, "invalid number"))

# the underscore after the zero is refused, and the scan stays refused
def L3.num_zero_underscore(rest):
  Equal.cong(T.Num, Bool,
    xx => D2.refused(T.num.fin(xx, '0' <> '_' <> rest)),
    T.num.go(rest, num.dead("invalid number")), num.dead("invalid number"),
    num.stays(rest, "invalid number"))

# the same after either sign
def L1.num_signed_zero_underscore(sg, rest):
  match sg:
    case T.Plus{}:
      Equal.cong(T.Num, Bool,
        xx => D2.refused(T.num.fin(xx, '+' <> '0' <> '_' <> rest)),
        T.num.go(rest, num.dead("invalid number")), num.dead("invalid number"),
        num.stays(rest, "invalid number"))
    case T.Minus{}:
      Equal.cong(T.Num, Bool,
        xx => D2.refused(T.num.fin(xx, '-' <> '0' <> '_' <> rest)),
        T.num.go(rest, num.dead("invalid number")), num.dead("invalid number"),
        num.stays(rest, "invalid number"))

# the claim that a word holds no value
def word.No(gg: T.Got) -> Type:
  {D2.refused(gg) == True{} : Bool}

# a word neither route reads is refused, whichever route it takes
def route.no(
  bb: Bool,
  +cs: List<&2, Char>,
  et: word.No(T.word.from.when(T.when.read(cs))),
  en: word.No(T.word.num(cs))
) -> word.No(T.word.route.date(bb, cs)):
  match bb:
    case True{}:
      et
    case False{}:
      en

# whether a word is routed to the datetime scan
def word.date(+cs: List<&2, Char>) -> Bool:
  T.word.or(T.word.colon(cs), T.word.dash(cs, True{}))

# a word after a minus, read up to its comparison with -inf
def minus.At(aa: Bool, +c2: Char, +rest: List<&2, Char>) -> Type:
  word.No(T.word.route(T.word.spec.inf3(aa, String.from_list('-' <> c2 <> rest)),
    word.date('-' <> c2 <> rest), '-' <> c2 <> rest))

# a word that starts with a minus and a character other than i and n is no
# special, since it differs from -inf and -nan at that character; it then
# reaches both routes, and the datetime scan wants a digit first
def minus.no(
  +c2: Char,
  +rest: List<&2, Char>,
  ei: {False{} == Char.is_eq(c2, 'i') : Bool},
  en: {False{} == Char.is_eq(c2, 'n') : Bool},
  nu: word.No(T.word.num('-' <> c2 <> rest))
) -> minus.At(T.str.eq.step(String.from_list(rest), "nf", Char.is_eq(c2, 'i')), c2, rest):
  Equal.trans(Bool,
    D2.refused(T.word.route(T.word.spec.inf3(
      T.str.eq.step(String.from_list(rest), "nf", Char.is_eq(c2, 'i')),
      String.from_list('-' <> c2 <> rest)), word.date('-' <> c2 <> rest), '-' <> c2 <> rest)),
    D2.refused(T.word.route(T.word.spec.inf3(False{}, String.from_list('-' <> c2 <> rest)),
      word.date('-' <> c2 <> rest), '-' <> c2 <> rest)),
    True{},
    Equal.cong(Bool, Bool,
      xx => D2.refused(T.word.route(T.word.spec.inf3(xx, String.from_list('-' <> c2 <> rest)),
        word.date('-' <> c2 <> rest), '-' <> c2 <> rest)),
      T.str.eq.step(String.from_list(rest), "nf", Char.is_eq(c2, 'i')), False{},
      M3.str.eq.off2(String.from_list(rest), "nf", Char.is_eq(c2, 'i'), ei)),
    Equal.trans(Bool,
      D2.refused(T.word.route(T.word.spec.nan3(
        T.str.eq.step(String.from_list(rest), "an", Char.is_eq(c2, 'n'))),
        word.date('-' <> c2 <> rest), '-' <> c2 <> rest)),
      D2.refused(T.word.route(T.word.spec.nan3(False{}), word.date('-' <> c2 <> rest), '-' <> c2 <> rest)),
      True{},
      Equal.cong(Bool, Bool,
        xx => D2.refused(T.word.route(T.word.spec.nan3(xx), word.date('-' <> c2 <> rest), '-' <> c2 <> rest)),
        T.str.eq.step(String.from_list(rest), "an", Char.is_eq(c2, 'n')), False{},
        M3.str.eq.off2(String.from_list(rest), "an", Char.is_eq(c2, 'n'), en)),
      route.no(T.word.as_date(word.date('-' <> c2 <> rest), T.word.ee('-' <> c2 <> rest)),
        '-' <> c2 <> rest, {==}, nu)))

# a word after a plus, read up to its comparison with +inf
def plus.At(aa: Bool, +c2: Char, +rest: List<&2, Char>) -> Type:
  word.No(T.word.route(T.word.spec.inf2(aa, False{}, String.from_list('+' <> c2 <> rest)),
    word.date('+' <> c2 <> rest), '+' <> c2 <> rest))

# a word after a plus, and a character other than i and n: the same as after
# a minus, with +inf and +nan
def plus.no(
  +c2: Char,
  +rest: List<&2, Char>,
  ei: {False{} == Char.is_eq(c2, 'i') : Bool},
  en: {False{} == Char.is_eq(c2, 'n') : Bool},
  nu: word.No(T.word.num('+' <> c2 <> rest))
) -> plus.At(T.str.eq.step(String.from_list(rest), "nf", Char.is_eq(c2, 'i')), c2, rest):
  Equal.trans(Bool,
    D2.refused(T.word.route(T.word.spec.inf2(
      T.str.eq.step(String.from_list(rest), "nf", Char.is_eq(c2, 'i')), False{},
      String.from_list('+' <> c2 <> rest)), word.date('+' <> c2 <> rest), '+' <> c2 <> rest)),
    D2.refused(T.word.route(T.word.spec.inf2(False{}, False{}, String.from_list('+' <> c2 <> rest)),
      word.date('+' <> c2 <> rest), '+' <> c2 <> rest)),
    True{},
    Equal.cong(Bool, Bool,
      xx => D2.refused(T.word.route(T.word.spec.inf2(xx, False{}, String.from_list('+' <> c2 <> rest)),
        word.date('+' <> c2 <> rest), '+' <> c2 <> rest)),
      T.str.eq.step(String.from_list(rest), "nf", Char.is_eq(c2, 'i')), False{},
      M3.str.eq.off2(String.from_list(rest), "nf", Char.is_eq(c2, 'i'), ei)),
    Equal.trans(Bool,
      D2.refused(T.word.route(T.word.spec.nan2(
        T.str.eq.step(String.from_list(rest), "an", Char.is_eq(c2, 'n')), False{}),
        word.date('+' <> c2 <> rest), '+' <> c2 <> rest)),
      D2.refused(T.word.route(T.word.spec.nan2(False{}, False{}), word.date('+' <> c2 <> rest), '+' <> c2 <> rest)),
      True{},
      Equal.cong(Bool, Bool,
        xx => D2.refused(T.word.route(T.word.spec.nan2(xx, False{}),
          word.date('+' <> c2 <> rest), '+' <> c2 <> rest)),
        T.str.eq.step(String.from_list(rest), "an", Char.is_eq(c2, 'n')), False{},
        M3.str.eq.off2(String.from_list(rest), "an", Char.is_eq(c2, 'n'), en)),
      route.no(T.word.as_date(word.date('+' <> c2 <> rest), T.word.ee('+' <> c2 <> rest)),
        '+' <> c2 <> rest, {==}, nu)))

# a table's rows as they are against them reordered (md false), or an
# array's elements (md true)
def s2.r(md: Bool, +xs: List<&2, T.Val>, +hp: String) -> List<&2, T.Val>:
  match md:
    case False{}:
      D1.canon.rows(xs)
    case True{}:
      D1.canon.go(xs, D1.CElems{hp})

# each pair picks its own, reordered, and an element meets its own
def s2(
  xs: List<&2, T.Val>,
  md: Bool,
  +hp: String,
  +hw: {T.wf.go(xs, M4.st.at(md, hp)) == True{} : Bool},
  +hs: {M2.selfs(xs) == True{} : Bool}
) -> {D1.same.go(xs, s2.r(md, xs, hp)) == True{} : Bool}:
  match xs md:
    case [] False{}:
      {==}
    case [] True{}:
      {==}
    case T.VPair{+kk, T.VHead{+p, +r}} <> +t False{}:
      +hin = {M3.wt.more(Bool.and(T.wf.key(kk, t), T.str.eq(p, T.tree.pre(hp, kk))), _u => T.wf.then(T.wf.go(r,
        T.WfRows{p}), _v => T.wf.go(t, T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(r, T.WfRows{p}), _v => T.wf.go(t,
        T.WfRows{hp})) == True{} : Bool}}
      +fr = {Eq.and.right(T.wf.text(kk), T.wf.fresh(T.get(t, kk)), Eq.and.left(T.wf.key(kk, t), T.str.eq(p,
        T.tree.pre(hp, kk)), M3.wt.ok(Bool.and(T.wf.key(kk, t), T.str.eq(p, T.tree.pre(hp, kk))),
        _u => T.wf.then(T.wf.go(r, T.WfRows{p}), _v => T.wf.go(t, T.WfRows{hp})), hw))) : {T.wf.fresh(T.get(t,
        kk)) == True{} : Bool}}
      Equal.trans(Bool, D1.same.go(T.VPair{kk, T.VHead{p, r}} <> t, List.append(&2, T.Val, D1.canon.keys(t),
        T.VPair{kk, T.VHead{p, D1.canon.rows(r)}} <> D1.canon.tabs(t))),
        D1.same.pair(D1.Picked{T.VHead{p, D1.canon.rows(r)}, List.append(&2, T.Val, D1.canon.keys(t),
          D1.canon.tabs(t))}, ww => D1.same.box(D1.KHead{}, ww, ws => D1.same.go(r, ws)),
          rr => D1.same.go(t, rr)), True{},
        Equal.cong(D1.Pick, Bool, pk2 => D1.same.pair(pk2, ww => D1.same.box(D1.KHead{}, ww,
          ws => D1.same.go(r, ws)),
          rr => D1.same.go(t, rr)), D1.pick(List.append(&2, T.Val, D1.canon.keys(t), T.VPair{kk, T.VHead{p,
            D1.canon.rows(r)}} <> D1.canon.tabs(t)), kk), D1.Picked{T.VHead{p, D1.canon.rows(r)},
            List.append(&2, T.Val, D1.canon.keys(t), D1.canon.tabs(t))},
          M1.pk.af(D1.canon.keys(t), kk, T.VHead{p, D1.canon.rows(r)}, D1.canon.tabs(t), M1.fr.keys(t, kk, fr))),
        M4.at.tt(D1.same.go(r, D1.canon.rows(r)), _u => D1.same.go(t, List.append(&2, T.Val, D1.canon.keys(t),
          D1.canon.tabs(t))), s2(r, False{}, p, M3.wt.ok(T.wf.go(r, T.WfRows{p}), _v => T.wf.go(t, T.WfRows{hp}), hin),
          M4.wf.selfs(r, T.WfRows{p}, M3.wt.ok(T.wf.go(r, T.WfRows{p}), _v => T.wf.go(t, T.WfRows{hp}), hin))),
          s2(t, False{}, hp, M3.wt.more(T.wf.go(r, T.WfRows{p}), _v => T.wf.go(t, T.WfRows{hp}), hin),
            Eq.and.right(D1.same.go(
            T.VPair{kk, T.VHead{p, r}} <> [], T.VPair{kk, T.VHead{p, r}} <> []), M2.selfs(t), hs))))
    case T.VPair{+kk, T.VAots{+p, +r}} <> +t False{}:
      +hin = {M3.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, r)), Bool.and(T.wf.key(kk, t), T.str.eq(p,
        T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(r, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp})),
        hw) : {T.wf.then(T.wf.go(r, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp})) == True{} : Bool}}
      +fr = {Eq.and.right(T.wf.text(kk), T.wf.fresh(T.get(t, kk)), Eq.and.left(T.wf.key(kk, t), T.str.eq(p,
        T.tree.pre(hp, kk)), Eq.and.right(Bool.not(List.is_empty(&2, T.Val, r)), Bool.and(T.wf.key(kk, t), T.str.eq(p,
        T.tree.pre(hp, kk))), M3.wt.ok(Bool.and(Bool.not(List.is_empty(&2, T.Val, r)), Bool.and(T.wf.key(kk, t),
        T.str.eq(p, T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(r, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp})),
        hw)))) : {T.wf.fresh(T.get(t, kk)) == True{} : Bool}}
      Equal.trans(Bool, D1.same.go(T.VPair{kk, T.VAots{p, r}} <> t, List.append(&2, T.Val, D1.canon.keys(t),
        T.VPair{kk, T.VAots{p, D1.canon.go(r, D1.CElems{p})}} <> D1.canon.tabs(t))),
        D1.same.pair(D1.Picked{T.VAots{p, D1.canon.go(r, D1.CElems{p})}, List.append(&2, T.Val,
          D1.canon.keys(t), D1.canon.tabs(t))}, ww => D1.same.box(D1.KAots{}, ww, ws => D1.same.go(r, ws)),
          rr => D1.same.go(t, rr)), True{},
        Equal.cong(D1.Pick, Bool, pk2 => D1.same.pair(pk2, ww => D1.same.box(D1.KAots{}, ww,
          ws => D1.same.go(r, ws)),
          rr => D1.same.go(t, rr)), D1.pick(List.append(&2, T.Val, D1.canon.keys(t), T.VPair{kk, T.VAots{p,
            D1.canon.go(r, D1.CElems{p})}} <> D1.canon.tabs(t)), kk), D1.Picked{T.VAots{p, D1.canon.go(r,
            D1.CElems{p})}, List.append(&2, T.Val, D1.canon.keys(t), D1.canon.tabs(t))},
          M1.pk.af(D1.canon.keys(t), kk, T.VAots{p, D1.canon.go(r, D1.CElems{p})}, D1.canon.tabs(t), M1.fr.keys(t, kk,
            fr))),
        M4.at.tt(D1.same.go(r, D1.canon.go(r, D1.CElems{p})), _u => D1.same.go(t, List.append(&2, T.Val,
          D1.canon.keys(t), D1.canon.tabs(t))), s2(r, True{}, p, M3.wt.ok(T.wf.go(r, T.WfElems{p}), _v => T.wf.go(t,
          T.WfRows{hp}), hin), M4.wf.selfs(r, T.WfElems{p}, M3.wt.ok(T.wf.go(r, T.WfElems{p}), _v => T.wf.go(t,
              T.WfRows{hp}),
          hin))),
          s2(t, False{}, hp, M3.wt.more(T.wf.go(r, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}), hin),
            Eq.and.right(D1.same.go(
            T.VPair{kk, T.VAots{p, r}} <> [], T.VPair{kk, T.VAots{p, r}} <> []), M2.selfs(t), hs))))
    case T.VPair{+kk, T.VStr{+a1}} <> +t False{}:
      Equal.trans(Bool, D1.same.go(T.VPair{kk, T.VStr{a1}} <> t, T.VPair{kk, T.VStr{a1}} <> List.append(&2, T.Val,
        D1.canon.keys(t), D1.canon.tabs(t))),
        Bool.and(D1.same.go(T.VPair{kk, T.VStr{a1}} <> [], T.VPair{kk, T.VStr{a1}} <> []), D1.same.go(t,
          List.append(&2, T.Val, D1.canon.keys(t), D1.canon.tabs(t)))), True{},
        M2.hc.p(kk, T.VStr{a1}, t, List.append(&2, T.Val, D1.canon.keys(t), D1.canon.tabs(t))),
        M3.cv.and2(D1.same.go(T.VPair{kk, T.VStr{a1}} <> [], T.VPair{kk, T.VStr{a1}} <> []), D1.same.go(t,
          List.append(&2, T.Val, D1.canon.keys(t), D1.canon.tabs(t))),
          Eq.and.left(D1.same.go(T.VPair{kk, T.VStr{a1}} <> [], T.VPair{kk, T.VStr{a1}} <> []), M2.selfs(t), hs),
          s2(t, False{}, hp, M3.wt.more(Bool.and(T.wf.atom(T.VStr{a1}), T.wf.key(kk, t)), _u => T.wf.go(t,
              T.WfRows{hp}),
            hw), Eq.and.right(D1.same.go(T.VPair{kk, T.VStr{a1}} <> [], T.VPair{kk, T.VStr{a1}} <> []), M2.selfs(t),
            hs))))
    case T.VPair{+kk, T.VSpan{+a1, +a2}} <> +t False{}:
      Equal.trans(Bool, D1.same.go(T.VPair{kk, T.VSpan{a1, a2}} <> t, T.VPair{kk, T.VSpan{a1, a2}} <> List.append(&2,
        T.Val, D1.canon.keys(t), D1.canon.tabs(t))),
        Bool.and(D1.same.go(T.VPair{kk, T.VSpan{a1, a2}} <> [], T.VPair{kk, T.VSpan{a1, a2}} <> []), D1.same.go(t,
          List.append(&2, T.Val, D1.canon.keys(t), D1.canon.tabs(t)))), True{},
        M2.hc.p(kk, T.VSpan{a1, a2}, t, List.append(&2, T.Val, D1.canon.keys(t), D1.canon.tabs(t))),
        M3.cv.and2(D1.same.go(T.VPair{kk, T.VSpan{a1, a2}} <> [], T.VPair{kk, T.VSpan{a1, a2}} <> []), D1.same.go(t,
          List.append(&2, T.Val, D1.canon.keys(t), D1.canon.tabs(t))),
          Eq.and.left(D1.same.go(T.VPair{kk, T.VSpan{a1, a2}} <> [], T.VPair{kk, T.VSpan{a1, a2}} <> []), M2.selfs(t),
            hs),
          s2(t, False{}, hp, M3.wt.more(Bool.and(T.wf.atom(T.VSpan{a1, a2}), T.wf.key(kk, t)), _u => T.wf.go(t,
            T.WfRows{hp}), hw), Eq.and.right(D1.same.go(T.VPair{kk, T.VSpan{a1, a2}} <> [], T.VPair{kk, T.VSpan{a1,
            a2}} <> []), M2.selfs(t), hs))))
    case T.VPair{+kk, T.VInt{+a1, +a2}} <> +t False{}:
      Equal.trans(Bool, D1.same.go(T.VPair{kk, T.VInt{a1, a2}} <> t, T.VPair{kk, T.VInt{a1, a2}} <> List.append(&2,
        T.Val, D1.canon.keys(t), D1.canon.tabs(t))),
        Bool.and(D1.same.go(T.VPair{kk, T.VInt{a1, a2}} <> [], T.VPair{kk, T.VInt{a1, a2}} <> []), D1.same.go(t,
          List.append(&2, T.Val, D1.canon.keys(t), D1.canon.tabs(t)))), True{},
        M2.hc.p(kk, T.VInt{a1, a2}, t, List.append(&2, T.Val, D1.canon.keys(t), D1.canon.tabs(t))),
        M3.cv.and2(D1.same.go(T.VPair{kk, T.VInt{a1, a2}} <> [], T.VPair{kk, T.VInt{a1, a2}} <> []), D1.same.go(t,
          List.append(&2, T.Val, D1.canon.keys(t), D1.canon.tabs(t))),
          Eq.and.left(D1.same.go(T.VPair{kk, T.VInt{a1, a2}} <> [], T.VPair{kk, T.VInt{a1, a2}} <> []), M2.selfs(t),
              hs),
          s2(t, False{}, hp, M3.wt.more(Bool.and(T.wf.atom(T.VInt{a1, a2}), T.wf.key(kk, t)), _u => T.wf.go(t,
            T.WfRows{hp}), hw), Eq.and.right(D1.same.go(T.VPair{kk, T.VInt{a1, a2}} <> [], T.VPair{kk, T.VInt{a1,
            a2}} <> []), M2.selfs(t), hs))))
    case T.VPair{+kk, T.VFlo{+a1, +a2}} <> +t False{}:
      Equal.trans(Bool, D1.same.go(T.VPair{kk, T.VFlo{a1, a2}} <> t, T.VPair{kk, T.VFlo{a1, a2}} <> List.append(&2,
        T.Val, D1.canon.keys(t), D1.canon.tabs(t))),
        Bool.and(D1.same.go(T.VPair{kk, T.VFlo{a1, a2}} <> [], T.VPair{kk, T.VFlo{a1, a2}} <> []), D1.same.go(t,
          List.append(&2, T.Val, D1.canon.keys(t), D1.canon.tabs(t)))), True{},
        M2.hc.p(kk, T.VFlo{a1, a2}, t, List.append(&2, T.Val, D1.canon.keys(t), D1.canon.tabs(t))),
        M3.cv.and2(D1.same.go(T.VPair{kk, T.VFlo{a1, a2}} <> [], T.VPair{kk, T.VFlo{a1, a2}} <> []), D1.same.go(t,
          List.append(&2, T.Val, D1.canon.keys(t), D1.canon.tabs(t))),
          Eq.and.left(D1.same.go(T.VPair{kk, T.VFlo{a1, a2}} <> [], T.VPair{kk, T.VFlo{a1, a2}} <> []), M2.selfs(t),
              hs),
          s2(t, False{}, hp, M3.wt.more(Bool.and(T.wf.atom(T.VFlo{a1, a2}), T.wf.key(kk, t)), _u => T.wf.go(t,
            T.WfRows{hp}), hw), Eq.and.right(D1.same.go(T.VPair{kk, T.VFlo{a1, a2}} <> [], T.VPair{kk, T.VFlo{a1,
            a2}} <> []), M2.selfs(t), hs))))
    case T.VPair{+kk, T.VBool{+a1}} <> +t False{}:
      Equal.trans(Bool, D1.same.go(T.VPair{kk, T.VBool{a1}} <> t, T.VPair{kk, T.VBool{a1}} <> List.append(&2, T.Val,
        D1.canon.keys(t), D1.canon.tabs(t))),
        Bool.and(D1.same.go(T.VPair{kk, T.VBool{a1}} <> [], T.VPair{kk, T.VBool{a1}} <> []), D1.same.go(t,
          List.append(&2, T.Val, D1.canon.keys(t), D1.canon.tabs(t)))), True{},
        M2.hc.p(kk, T.VBool{a1}, t, List.append(&2, T.Val, D1.canon.keys(t), D1.canon.tabs(t))),
        M3.cv.and2(D1.same.go(T.VPair{kk, T.VBool{a1}} <> [], T.VPair{kk, T.VBool{a1}} <> []), D1.same.go(t,
          List.append(&2, T.Val, D1.canon.keys(t), D1.canon.tabs(t))),
          Eq.and.left(D1.same.go(T.VPair{kk, T.VBool{a1}} <> [], T.VPair{kk, T.VBool{a1}} <> []), M2.selfs(t), hs),
          s2(t, False{}, hp, M3.wt.more(Bool.and(T.wf.atom(T.VBool{a1}), T.wf.key(kk, t)), _u => T.wf.go(t,
              T.WfRows{hp}),
            hw), Eq.and.right(D1.same.go(T.VPair{kk, T.VBool{a1}} <> [], T.VPair{kk, T.VBool{a1}} <> []), M2.selfs(t),
            hs))))
    case T.VPair{+kk, T.VWhen{+a1}} <> +t False{}:
      Equal.trans(Bool, D1.same.go(T.VPair{kk, T.VWhen{a1}} <> t, T.VPair{kk, T.VWhen{a1}} <> List.append(&2, T.Val,
        D1.canon.keys(t), D1.canon.tabs(t))),
        Bool.and(D1.same.go(T.VPair{kk, T.VWhen{a1}} <> [], T.VPair{kk, T.VWhen{a1}} <> []), D1.same.go(t,
          List.append(&2, T.Val, D1.canon.keys(t), D1.canon.tabs(t)))), True{},
        M2.hc.p(kk, T.VWhen{a1}, t, List.append(&2, T.Val, D1.canon.keys(t), D1.canon.tabs(t))),
        M3.cv.and2(D1.same.go(T.VPair{kk, T.VWhen{a1}} <> [], T.VPair{kk, T.VWhen{a1}} <> []), D1.same.go(t,
          List.append(&2, T.Val, D1.canon.keys(t), D1.canon.tabs(t))),
          Eq.and.left(D1.same.go(T.VPair{kk, T.VWhen{a1}} <> [], T.VPair{kk, T.VWhen{a1}} <> []), M2.selfs(t), hs),
          s2(t, False{}, hp, M3.wt.more(Bool.and(T.wf.atom(T.VWhen{a1}), T.wf.key(kk, t)), _u => T.wf.go(t,
              T.WfRows{hp}),
            hw), Eq.and.right(D1.same.go(T.VPair{kk, T.VWhen{a1}} <> [], T.VPair{kk, T.VWhen{a1}} <> []), M2.selfs(t),
            hs))))
    case T.VPair{+kk, T.VArr{+a1}} <> +t False{}:
      Equal.trans(Bool, D1.same.go(T.VPair{kk, T.VArr{a1}} <> t, T.VPair{kk, T.VArr{a1}} <> List.append(&2, T.Val,
        D1.canon.keys(t), D1.canon.tabs(t))),
        Bool.and(D1.same.go(T.VPair{kk, T.VArr{a1}} <> [], T.VPair{kk, T.VArr{a1}} <> []), D1.same.go(t,
          List.append(&2, T.Val, D1.canon.keys(t), D1.canon.tabs(t)))), True{},
        M2.hc.p(kk, T.VArr{a1}, t, List.append(&2, T.Val, D1.canon.keys(t), D1.canon.tabs(t))),
        M3.cv.and2(D1.same.go(T.VPair{kk, T.VArr{a1}} <> [], T.VPair{kk, T.VArr{a1}} <> []), D1.same.go(t,
          List.append(&2, T.Val, D1.canon.keys(t), D1.canon.tabs(t))),
          Eq.and.left(D1.same.go(T.VPair{kk, T.VArr{a1}} <> [], T.VPair{kk, T.VArr{a1}} <> []), M2.selfs(t), hs),
          s2(t, False{}, hp, M3.wt.more(T.wf.go(a1, T.WfItems{}), _v => T.wf.go(t, T.WfRows{hp}),
              M3.wt.more(T.wf.key(kk, t),
            _u => T.wf.then(T.wf.go(a1, T.WfItems{}), _v => T.wf.go(t, T.WfRows{hp})), hw)),
            Eq.and.right(D1.same.go(T.VPair{kk, T.VArr{a1}} <> [], T.VPair{kk, T.VArr{a1}} <> []), M2.selfs(t), hs))))
    case T.VPair{+kk, T.VInl{+a1}} <> +t False{}:
      Equal.trans(Bool, D1.same.go(T.VPair{kk, T.VInl{a1}} <> t, T.VPair{kk, T.VInl{a1}} <> List.append(&2, T.Val,
        D1.canon.keys(t), D1.canon.tabs(t))),
        Bool.and(D1.same.go(T.VPair{kk, T.VInl{a1}} <> [], T.VPair{kk, T.VInl{a1}} <> []), D1.same.go(t,
          List.append(&2, T.Val, D1.canon.keys(t), D1.canon.tabs(t)))), True{},
        M2.hc.p(kk, T.VInl{a1}, t, List.append(&2, T.Val, D1.canon.keys(t), D1.canon.tabs(t))),
        M3.cv.and2(D1.same.go(T.VPair{kk, T.VInl{a1}} <> [], T.VPair{kk, T.VInl{a1}} <> []), D1.same.go(t,
          List.append(&2, T.Val, D1.canon.keys(t), D1.canon.tabs(t))),
          Eq.and.left(D1.same.go(T.VPair{kk, T.VInl{a1}} <> [], T.VPair{kk, T.VInl{a1}} <> []), M2.selfs(t), hs),
          s2(t, False{}, hp, M3.wt.more(T.wf.go(a1, T.WfInl{}), _v => T.wf.go(t, T.WfRows{hp}), M3.wt.more(T.wf.key(kk,
              t),
            _u => T.wf.then(T.wf.go(a1, T.WfInl{}), _v => T.wf.go(t, T.WfRows{hp})), hw)),
            Eq.and.right(D1.same.go(T.VPair{kk, T.VInl{a1}} <> [], T.VPair{kk, T.VInl{a1}} <> []), M2.selfs(t), hs))))
    case T.VPair{+kk, T.VAot{+a1, +a2}} <> +t False{}:
      Eq.bit.absurd(&2, {D1.same.go(T.VPair{kk, T.VAot{a1, a2}} <> t, s2.r(False{}, T.VPair{kk, T.VAot{a1, a2}} <> t,
        hp)) == True{} : Bool}, hw)
    case T.VPair{+kk, T.VPair{+a1, +a2}} <> +t False{}:
      Eq.bit.absurd(&2, {D1.same.go(T.VPair{kk, T.VPair{a1, a2}} <> t, s2.r(False{}, T.VPair{kk, T.VPair{a1,
        a2}} <> t, hp)) == True{} : Bool}, hw)
    case T.VStr{+a1} <> +t False{}:
      Eq.bit.absurd(&2, {D1.same.go(T.VStr{a1} <> t, s2.r(False{}, T.VStr{a1} <> t, hp)) == True{} : Bool}, hw)
    case T.VSpan{+a1, +a2} <> +t False{}:
      Eq.bit.absurd(&2, {D1.same.go(T.VSpan{a1, a2} <> t, s2.r(False{}, T.VSpan{a1, a2} <> t, hp)) == True{} : Bool},
        hw)
    case T.VInt{+a1, +a2} <> +t False{}:
      Eq.bit.absurd(&2, {D1.same.go(T.VInt{a1, a2} <> t, s2.r(False{}, T.VInt{a1, a2} <> t, hp)) == True{} : Bool},
        hw)
    case T.VFlo{+a1, +a2} <> +t False{}:
      Eq.bit.absurd(&2, {D1.same.go(T.VFlo{a1, a2} <> t, s2.r(False{}, T.VFlo{a1, a2} <> t, hp)) == True{} : Bool},
        hw)
    case T.VBool{+a1} <> +t False{}:
      Eq.bit.absurd(&2, {D1.same.go(T.VBool{a1} <> t, s2.r(False{}, T.VBool{a1} <> t, hp)) == True{} : Bool}, hw)
    case T.VWhen{+a1} <> +t False{}:
      Eq.bit.absurd(&2, {D1.same.go(T.VWhen{a1} <> t, s2.r(False{}, T.VWhen{a1} <> t, hp)) == True{} : Bool}, hw)
    case T.VArr{+a1} <> +t False{}:
      Eq.bit.absurd(&2, {D1.same.go(T.VArr{a1} <> t, s2.r(False{}, T.VArr{a1} <> t, hp)) == True{} : Bool}, hw)
    case T.VInl{+a1} <> +t False{}:
      Eq.bit.absurd(&2, {D1.same.go(T.VInl{a1} <> t, s2.r(False{}, T.VInl{a1} <> t, hp)) == True{} : Bool}, hw)
    case T.VHead{+a1, +a2} <> +t False{}:
      Eq.bit.absurd(&2, {D1.same.go(T.VHead{a1, a2} <> t, s2.r(False{}, T.VHead{a1, a2} <> t, hp)) == True{} : Bool},
        hw)
    case T.VAot{+a1, +a2} <> +t False{}:
      Eq.bit.absurd(&2, {D1.same.go(T.VAot{a1, a2} <> t, s2.r(False{}, T.VAot{a1, a2} <> t, hp)) == True{} : Bool},
        hw)
    case T.VAots{+a1, +a2} <> +t False{}:
      Eq.bit.absurd(&2, {D1.same.go(T.VAots{a1, a2} <> t, s2.r(False{}, T.VAots{a1, a2} <> t, hp)) == True{} : Bool},
        hw)
    case T.VAot{+q, +r} <> +t True{}:
      +hin = {M3.wt.more(T.str.eq(q, hp), _u => T.wf.then(T.wf.go(r, T.WfRows{q}), _v => T.wf.go(t, T.WfElems{hp})), hw)
        : {T.wf.then(T.wf.go(r, T.WfRows{q}), _v => T.wf.go(t, T.WfElems{hp})) == True{} : Bool}}
      +hwr = {M3.wt.ok(T.wf.go(r, T.WfRows{q}), _v => T.wf.go(t, T.WfElems{hp}), hin) : {T.wf.go(r,
          T.WfRows{q}) == True{}
        : Bool}}
      M4.at.tt(D1.same.go(r, D1.canon.rows(r)), _u => D1.same.go(t, D1.canon.go(t, D1.CElems{hp})),
        s2(r, False{}, q, hwr, M4.wf.selfs(r, T.WfRows{q}, hwr)),
        s2(t, True{}, hp, M3.wt.more(T.wf.go(r, T.WfRows{q}), _v => T.wf.go(t, T.WfElems{hp}), hin),
          Eq.and.right(D1.same.go(T.VAot{q, r} <> [], T.VAot{q, r} <> []), M2.selfs(t), hs)))
    case T.VStr{+a1} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(T.VStr{a1} <> t, s2.r(True{}, T.VStr{a1} <> t, hp)) == True{} : Bool}, hw)
    case T.VSpan{+a1, +a2} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(T.VSpan{a1, a2} <> t, s2.r(True{}, T.VSpan{a1, a2} <> t, hp)) == True{} : Bool},
        hw)
    case T.VInt{+a1, +a2} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(T.VInt{a1, a2} <> t, s2.r(True{}, T.VInt{a1, a2} <> t, hp)) == True{} : Bool}, hw)
    case T.VFlo{+a1, +a2} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(T.VFlo{a1, a2} <> t, s2.r(True{}, T.VFlo{a1, a2} <> t, hp)) == True{} : Bool}, hw)
    case T.VBool{+a1} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(T.VBool{a1} <> t, s2.r(True{}, T.VBool{a1} <> t, hp)) == True{} : Bool}, hw)
    case T.VWhen{+a1} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(T.VWhen{a1} <> t, s2.r(True{}, T.VWhen{a1} <> t, hp)) == True{} : Bool}, hw)
    case T.VArr{+a1} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(T.VArr{a1} <> t, s2.r(True{}, T.VArr{a1} <> t, hp)) == True{} : Bool}, hw)
    case T.VInl{+a1} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(T.VInl{a1} <> t, s2.r(True{}, T.VInl{a1} <> t, hp)) == True{} : Bool}, hw)
    case T.VHead{+a1, +a2} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(T.VHead{a1, a2} <> t, s2.r(True{}, T.VHead{a1, a2} <> t, hp)) == True{} : Bool},
        hw)
    case T.VAots{+a1, +a2} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(T.VAots{a1, a2} <> t, s2.r(True{}, T.VAots{a1, a2} <> t, hp)) == True{} : Bool},
        hw)
    case T.VPair{+a1, T.VStr{+b1}} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(T.VPair{a1, T.VStr{b1}} <> t, s2.r(True{}, T.VPair{a1, T.VStr{b1}} <> t,
        hp)) == True{} : Bool}, hw)
    case T.VPair{+a1, T.VSpan{+b1, +b2}} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(T.VPair{a1, T.VSpan{b1, b2}} <> t, s2.r(True{}, T.VPair{a1, T.VSpan{b1, b2}} <> t,
        hp)) == True{} : Bool}, hw)
    case T.VPair{+a1, T.VInt{+b1, +b2}} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(T.VPair{a1, T.VInt{b1, b2}} <> t, s2.r(True{}, T.VPair{a1, T.VInt{b1, b2}} <> t,
        hp)) == True{} : Bool}, hw)
    case T.VPair{+a1, T.VFlo{+b1, +b2}} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(T.VPair{a1, T.VFlo{b1, b2}} <> t, s2.r(True{}, T.VPair{a1, T.VFlo{b1, b2}} <> t,
        hp)) == True{} : Bool}, hw)
    case T.VPair{+a1, T.VBool{+b1}} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(T.VPair{a1, T.VBool{b1}} <> t, s2.r(True{}, T.VPair{a1, T.VBool{b1}} <> t,
        hp)) == True{} : Bool}, hw)
    case T.VPair{+a1, T.VWhen{+b1}} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(T.VPair{a1, T.VWhen{b1}} <> t, s2.r(True{}, T.VPair{a1, T.VWhen{b1}} <> t,
        hp)) == True{} : Bool}, hw)
    case T.VPair{+a1, T.VArr{+b1}} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(T.VPair{a1, T.VArr{b1}} <> t, s2.r(True{}, T.VPair{a1, T.VArr{b1}} <> t,
        hp)) == True{} : Bool}, hw)
    case T.VPair{+a1, T.VInl{+b1}} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(T.VPair{a1, T.VInl{b1}} <> t, s2.r(True{}, T.VPair{a1, T.VInl{b1}} <> t,
        hp)) == True{} : Bool}, hw)
    case T.VPair{+a1, T.VHead{+b1, +b2}} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(T.VPair{a1, T.VHead{b1, b2}} <> t, s2.r(True{}, T.VPair{a1, T.VHead{b1, b2}} <> t,
        hp)) == True{} : Bool}, hw)
    case T.VPair{+a1, T.VAot{+b1, +b2}} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(T.VPair{a1, T.VAot{b1, b2}} <> t, s2.r(True{}, T.VPair{a1, T.VAot{b1, b2}} <> t,
        hp)) == True{} : Bool}, hw)
    case T.VPair{+a1, T.VAots{+b1, +b2}} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(T.VPair{a1, T.VAots{b1, b2}} <> t, s2.r(True{}, T.VPair{a1, T.VAots{b1, b2}} <> t,
        hp)) == True{} : Bool}, hw)
    case T.VPair{+a1, T.VPair{+b1, +b2}} <> +t True{}:
      Eq.bit.absurd(&2, {D1.same.go(T.VPair{a1, T.VPair{b1, b2}} <> t, s2.r(True{}, T.VPair{a1, T.VPair{b1, b2}} <> t,
        hp)) == True{} : Bool}, hw)
