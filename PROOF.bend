# Proofs of the eztoml laws. The gate: `bend PROOF.bend` prints exactly
# `All terms check.` as its first line.
import Base
import ./main.bend as T
import ./src/eq.bend as Eq
import ./LAWS.bend as Laws

# a text equals itself when equality does not rebuild the text
def str.eq.self(+s: String) -> {T.str.eq(s, s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.trans(Bool,
        T.str.eq.step(t, t, Char.is_eq(h, h)),
        T.str.eq.step(t, t, True{}),
        True{},
        Equal.cong(Bool, Bool,
          x => T.str.eq.step(t, t, x),
          Char.is_eq(h, h), True{}, Eq.char_eq_self(h)),
        str.eq.self(t))

def Laws.get_first(name, v, rest):
  Equal.cong(Bool, T.Hit,
    b => T.find.step(b, v, _u => T.rows.find(rest, name)),
    T.str.eq(name, name), True{}, str.eq.self(name))

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

def Laws.string_of(_text):
  {==}

# TOML-KEY-1. The code asks Base's ASCII classes and then `_` and `-`; the
# ABNF lists `-` before `_`, which is the one place the two read differently.

# a character the code lets into a bare key is one the ABNF does
def bare.at.abnf(
  cc: Char
) -> {T.bare.at(cc) == Laws.abnf.unquoted_key_char(cc) : Bool}:
  match cc:
    case Chr{+cp}:
      Equal.cong(Bool, Bool,
        y => Bool.or(Laws.abnf.alpha(cp), Bool.or(Laws.abnf.digit(cp), y)),
        Bool.or(U32.is_eq(cp, 95), U32.is_eq(cp, 45)),
        Bool.or(U32.is_eq(cp, 45), U32.is_eq(cp, 95)),
        Eq.or_comm(U32.is_eq(cp, 95), U32.is_eq(cp, 45)))

# one step of the walk is an `and` of the head's answer and the rest's
def bare.step.and(
  bb: Bool,
  rr: Bool
) -> {T.bare.all.step(bb, _u => rr) == Bool.and(bb, rr) : Bool}:
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# the code's walk and the ABNF's repetition agree on every string
def bare.all.abnf(
  ss: String
) -> {T.bare.all(String.to_list(ss))
  == Laws.abnf.all_unquoted_key_chars(ss) : Bool}:
  match ss:
    case SNil{}:
      {==}
    case SCon{+hh, +tt}:
      Equal.trans(Bool,
        T.bare.all.step(T.bare.at(hh), _u => T.bare.all(String.to_list(tt))),
        Bool.and(T.bare.at(hh), T.bare.all(String.to_list(tt))),
        Bool.and(Laws.abnf.unquoted_key_char(hh),
          Laws.abnf.all_unquoted_key_chars(tt)),
        bare.step.and(T.bare.at(hh), T.bare.all(String.to_list(tt))),
        Equal.trans(Bool,
          Bool.and(T.bare.at(hh), T.bare.all(String.to_list(tt))),
          Bool.and(Laws.abnf.unquoted_key_char(hh),
            T.bare.all(String.to_list(tt))),
          Bool.and(Laws.abnf.unquoted_key_char(hh),
            Laws.abnf.all_unquoted_key_chars(tt)),
          Equal.cong(Bool, Bool,
            y => Bool.and(y, T.bare.all(String.to_list(tt))),
            T.bare.at(hh), Laws.abnf.unquoted_key_char(hh), bare.at.abnf(hh)),
          Equal.cong(Bool, Bool,
            y => Bool.and(Laws.abnf.unquoted_key_char(hh), y),
            T.bare.all(String.to_list(tt)),
            Laws.abnf.all_unquoted_key_chars(tt), bare.all.abnf(tt))))

# the empty string is neither, and a nonempty one is its walk on both sides
def Laws.bare_is_unquoted_key(s):
  match s:
    case SNil{}:
      {==}
    case SCon{+hh, +tt}:
      bare.all.abnf(SCon{hh, tt})

# TOML-GET-1. The code compares names with its own `str.eq`, and the laws
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

# after two first chars that compared as cc, both walks give the same answer
def str.eq.agree.cmp(
  +xt: String,
  +yt: String,
  hx: Char,
  hy: Char,
  cc: Cmp,
  ih: {T.str.eq(xt, yt) == String.eq(xt, yt) : Bool}
) -> {T.str.eq.step(xt, yt, Cmp.is_eq(cc))
  == String.eq.fin(String.cmp.fin(xt, yt, ((hx, hy), cc))) : Bool}:
  match cc:
    case LT{}:
      str.eq.step.false(xt, yt)
    case EQ{}:
      Equal.trans(Bool, T.str.eq(xt, yt), String.eq(xt, yt),
        String.eq.fin(String.cmp.rec(hx, hy, String.cmp(xt, yt))), ih,
        Equal.sym(Bool,
          String.eq.fin(String.cmp.rec(hx, hy, String.cmp(xt, yt))),
          String.eq(xt, yt), Eq.eq_fin_rec(hx, hy, String.cmp(xt, yt))))
    case GT{}:
      str.eq.step.false(xt, yt)

# the code's string equality is Base's, on every pair of strings
def str.eq.agree(
  +aa: String,
  +bb: String
) -> {T.str.eq(aa, bb) == String.eq(aa, bb) : Bool}:
  match aa bb:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{_h, _t}:
      {==}
    case SCon{_h, _t} SNil{}:
      {==}
    case SCon{Chr{+uu}, +xt} SCon{Chr{+ww}, +yt}:
      str.eq.agree.cmp(xt, yt, Chr{uu}, Chr{ww}, U32.cmp(uu, ww),
        str.eq.agree(xt, yt))

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
      str.eq.agree(nn, kk), ee))

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
          Eq.or.false_left(String.eq(nn, k), Laws.has_pair(tt, k), e)),
        Laws.get_finds_first(tt, k, v, post,
          Eq.or.false_right(String.eq(nn, k), Laws.has_pair(tt, k), e)))
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
          Eq.or.false_left(String.eq(nn, k), Laws.has_pair(tt, k), e)),
        Laws.get_misses(tt, k,
          Eq.or.false_right(String.eq(nn, k), Laws.has_pair(tt, k), e)))
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

# TOML-GET-2.

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

# TOML-READ-1.

# a span's walk counts its U32 down while Base's take counts a Nat, and the
# two counts agree at every step: zero is 0n, and anything else is one more
# than itself less one
def span.take(
  src: String,
  +nn: U32,
  zz: Bool,
  ez: {U32.is_zero(nn) == zz : Bool}
) -> {T.span.str(src, nn, zz) == String.take(src, U32.to_nat(nn)) : String}:
  match src zz:
    case SNil{} True{}:
      {==}
    case SNil{} False{}:
      {==}
    case SCon{+hh, +tt} True{}:
      Equal.cong(Nat, String, mm => String.take(SCon{hh, tt}, mm), 0n,
        U32.to_nat(nn),
        Equal.sym(Nat, U32.to_nat(nn), 0n, Eq.u32_zero_nat(nn, ez)))
    case SCon{+hh, +tt} False{}:
      Equal.trans(String,
        SCon{hh, T.span.str(tt, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)))},
        SCon{hh, String.take(tt, U32.to_nat(U32.sub(nn, 1)))},
        String.take(SCon{hh, tt}, U32.to_nat(nn)),
        Equal.cong(String, String, s2 => SCon{hh, s2},
          T.span.str(tt, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1))),
          String.take(tt, U32.to_nat(U32.sub(nn, 1))),
          span.take(tt, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)), {==})),
        Equal.cong(Nat, String, mm => String.take(SCon{hh, tt}, mm),
          1n+U32.to_nat(U32.sub(nn, 1)), U32.to_nat(nn),
          Equal.sym(Nat, U32.to_nat(nn), 1n+U32.to_nat(U32.sub(nn, 1)),
            Eq.u32_dec_nat(nn, ez))))

def Laws.string_of_span(src, n):
  span.take(src, n, U32.is_zero(n), {==})

def Laws.string_of_other(v, e):
  match v:
    case T.VStr{a}:
      Eq.bit.absurd2(&2, {T.string(T.VStr{a}) == "" : String}, e)
    case T.VSpan{a, b}:
      Eq.bit.absurd2(&2, {T.string(T.VSpan{a, b}) == "" : String}, e)
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
    case T.VPair{_a, _b}:
      {==}

def Laws.digits_of(_sign, _text):
  {==}

def Laws.digits_of_other(v, e):
  match v:
    case T.VInt{a, b}:
      Eq.bit.absurd2(&2, {T.digits(T.VInt{a, b}) == "" : String}, e)
    case T.VStr{_a}:
      {==}
    case T.VSpan{_a, _b}:
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
    case T.VPair{_a, _b}:
      {==}

def Laws.flag_of(_bit):
  {==}

def Laws.flag_of_other(v, e):
  match v:
    case T.VBool{a}:
      Eq.bit.absurd2(&2, {T.flag(T.VBool{a}) == False{} : Bool}, e)
    case T.VStr{_a}:
      {==}
    case T.VSpan{_a, _b}:
      {==}
    case T.VInt{_a, _b}:
      {==}
    case T.VFlo{_a, _b}:
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
    case T.VPair{_a, _b}:
      {==}

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
def Laws.num_two_signs(s1, s2, rest):
  match s1 s2:
    case T.Plus{} T.Plus{}:
      Equal.cong(T.Num, Bool,
        xx => Laws.refused(T.num.fin(xx, '+' <> '+' <> rest)),
        T.num.go(rest, num.dead("invalid number")), num.dead("invalid number"),
        num.stays(rest, "invalid number"))
    case T.Plus{} T.Minus{}:
      Equal.cong(T.Num, Bool,
        xx => Laws.refused(T.num.fin(xx, '+' <> '-' <> rest)),
        T.num.go(rest, num.dead("invalid number")), num.dead("invalid number"),
        num.stays(rest, "invalid number"))
    case T.Minus{} T.Plus{}:
      Equal.cong(T.Num, Bool,
        xx => Laws.refused(T.num.fin(xx, '-' <> '+' <> rest)),
        T.num.go(rest, num.dead("invalid number")), num.dead("invalid number"),
        num.stays(rest, "invalid number"))
    case T.Minus{} T.Minus{}:
      Equal.cong(T.Num, Bool,
        xx => Laws.refused(T.num.fin(xx, '-' <> '-' <> rest)),
        T.num.go(rest, num.dead("invalid number")), num.dead("invalid number"),
        num.stays(rest, "invalid number"))

# the underscore after the zero is refused, and the scan stays refused
def Laws.num_zero_underscore(rest):
  Equal.cong(T.Num, Bool,
    xx => Laws.refused(T.num.fin(xx, '0' <> '_' <> rest)),
    T.num.go(rest, num.dead("invalid number")), num.dead("invalid number"),
    num.stays(rest, "invalid number"))

# the same after either sign
def Laws.num_signed_zero_underscore(sg, rest):
  match sg:
    case T.Plus{}:
      Equal.cong(T.Num, Bool,
        xx => Laws.refused(T.num.fin(xx, '+' <> '0' <> '_' <> rest)),
        T.num.go(rest, num.dead("invalid number")), num.dead("invalid number"),
        num.stays(rest, "invalid number"))
    case T.Minus{}:
      Equal.cong(T.Num, Bool,
        xx => Laws.refused(T.num.fin(xx, '-' <> '0' <> '_' <> rest)),
        T.num.go(rest, num.dead("invalid number")), num.dead("invalid number"),
        num.stays(rest, "invalid number"))

# the character is not a sign, so the second-sign check lets it through
def Laws.num_one_sign(sg, cc, e):
  match sg:
    case T.Plus{}:
      %e : {T.num.after.sign.go(_, T.Plus{}, cc)
        == T.num.lead(T.Num{T.NLead{}, T.Plus{}, 10, [], False{}, False{}, ""}, cc) : T.Num}
      {==}
    case T.Minus{}:
      %e : {T.num.after.sign.go(_, T.Minus{}, cc)
        == T.num.lead(T.Num{T.NLead{}, T.Minus{}, 10, [], False{}, False{}, ""}, cc) : T.Num}
      {==}

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

# the claim that a word holds no value
def word.No(gg: T.Got) -> Type:
  {Laws.refused(gg) == True{} : Bool}

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

# a word after a minus, read up to its comparison with -nan
def minus.Nan(aa: Bool, +c2: Char, +rest: List<&2, Char>) -> Type:
  word.No(T.word.route(T.word.spec.nan3(aa), word.date('-' <> c2 <> rest), '-' <> c2 <> rest))

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
    Laws.refused(T.word.route(T.word.spec.inf3(
      T.str.eq.step(String.from_list(rest), "nf", Char.is_eq(c2, 'i')),
      String.from_list('-' <> c2 <> rest)), word.date('-' <> c2 <> rest), '-' <> c2 <> rest)),
    Laws.refused(T.word.route(T.word.spec.inf3(False{}, String.from_list('-' <> c2 <> rest)),
      word.date('-' <> c2 <> rest), '-' <> c2 <> rest)),
    True{},
    Equal.cong(Bool, Bool,
      xx => Laws.refused(T.word.route(T.word.spec.inf3(xx, String.from_list('-' <> c2 <> rest)),
        word.date('-' <> c2 <> rest), '-' <> c2 <> rest)),
      T.str.eq.step(String.from_list(rest), "nf", Char.is_eq(c2, 'i')), False{},
      str.eq.off2(String.from_list(rest), "nf", Char.is_eq(c2, 'i'), ei)),
    Equal.trans(Bool,
      Laws.refused(T.word.route(T.word.spec.nan3(
        T.str.eq.step(String.from_list(rest), "an", Char.is_eq(c2, 'n'))),
        word.date('-' <> c2 <> rest), '-' <> c2 <> rest)),
      Laws.refused(T.word.route(T.word.spec.nan3(False{}), word.date('-' <> c2 <> rest), '-' <> c2 <> rest)),
      True{},
      Equal.cong(Bool, Bool,
        xx => Laws.refused(T.word.route(T.word.spec.nan3(xx), word.date('-' <> c2 <> rest), '-' <> c2 <> rest)),
        T.str.eq.step(String.from_list(rest), "an", Char.is_eq(c2, 'n')), False{},
        str.eq.off2(String.from_list(rest), "an", Char.is_eq(c2, 'n'), en)),
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
    Laws.refused(T.word.route(T.word.spec.inf2(
      T.str.eq.step(String.from_list(rest), "nf", Char.is_eq(c2, 'i')), False{},
      String.from_list('+' <> c2 <> rest)), word.date('+' <> c2 <> rest), '+' <> c2 <> rest)),
    Laws.refused(T.word.route(T.word.spec.inf2(False{}, False{}, String.from_list('+' <> c2 <> rest)),
      word.date('+' <> c2 <> rest), '+' <> c2 <> rest)),
    True{},
    Equal.cong(Bool, Bool,
      xx => Laws.refused(T.word.route(T.word.spec.inf2(xx, False{}, String.from_list('+' <> c2 <> rest)),
        word.date('+' <> c2 <> rest), '+' <> c2 <> rest)),
      T.str.eq.step(String.from_list(rest), "nf", Char.is_eq(c2, 'i')), False{},
      str.eq.off2(String.from_list(rest), "nf", Char.is_eq(c2, 'i'), ei)),
    Equal.trans(Bool,
      Laws.refused(T.word.route(T.word.spec.nan2(
        T.str.eq.step(String.from_list(rest), "an", Char.is_eq(c2, 'n')), False{}),
        word.date('+' <> c2 <> rest), '+' <> c2 <> rest)),
      Laws.refused(T.word.route(T.word.spec.nan2(False{}, False{}), word.date('+' <> c2 <> rest), '+' <> c2 <> rest)),
      True{},
      Equal.cong(Bool, Bool,
        xx => Laws.refused(T.word.route(T.word.spec.nan2(xx, False{}),
          word.date('+' <> c2 <> rest), '+' <> c2 <> rest)),
        T.str.eq.step(String.from_list(rest), "an", Char.is_eq(c2, 'n')), False{},
        str.eq.off2(String.from_list(rest), "an", Char.is_eq(c2, 'n'), en)),
      route.no(T.word.as_date(word.date('+' <> c2 <> rest), T.word.ee('+' <> c2 <> rest)),
        '+' <> c2 <> rest, {==}, nu)))

# each pair of signs: no special, and both routes refuse it
def Laws.word_two_signs(s1, s2, rest):
  match s1 s2:
    case T.Plus{} T.Plus{}:
      plus.no('+', rest, {==}, {==}, Laws.num_two_signs(T.Plus{}, T.Plus{}, rest))
    case T.Plus{} T.Minus{}:
      plus.no('-', rest, {==}, {==}, Laws.num_two_signs(T.Plus{}, T.Minus{}, rest))
    case T.Minus{} T.Plus{}:
      minus.no('+', rest, {==}, {==}, Laws.num_two_signs(T.Minus{}, T.Plus{}, rest))
    case T.Minus{} T.Minus{}:
      minus.no('-', rest, {==}, {==}, Laws.num_two_signs(T.Minus{}, T.Minus{}, rest))

# a word that starts with a digit is no special, and both routes refuse it
def Laws.word_zero_underscore(rest):
  route.no(T.word.as_date(word.date('0' <> '_' <> rest), T.word.ee('0' <> '_' <> rest)),
    '0' <> '_' <> rest, {==}, Laws.num_zero_underscore(rest))

# after either sign, as for two signs
def Laws.word_signed_zero_underscore(sg, rest):
  match sg:
    case T.Plus{}:
      plus.no('0', '_' <> rest, {==}, {==}, Laws.num_signed_zero_underscore(T.Plus{}, rest))
    case T.Minus{}:
      minus.no('0', '_' <> rest, {==}, {==}, Laws.num_signed_zero_underscore(T.Minus{}, rest))

# February's days by the three divisibility tests, the code's way and the
# table's way, for every answer the tests can give
def feb.same(
  four: Bool,
  hundred: Bool,
  four_hundred: Bool
) -> {T.when.feb.go(four, hundred, four_hundred)
  == Laws.feb_days(Bool.and(four, Bool.or(Bool.not(hundred), four_hundred))) : U32}:
  match four hundred four_hundred:
    case False{} _h _q:
      {==}
    case True{} False{} _q:
      {==}
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}

# the code's days of a month are the table's, month by month
def days.same(+yy: U32, mm: Laws.Month) -> {T.when.days(yy, Laws.month.num(mm)) == Laws.days_in(yy, mm) : U32}:
  match mm:
    case Laws.Jan{}:
      {==}
    case Laws.Feb{}:
      feb.same(U32.is_eq(U32.mod(yy, 4), 0), U32.is_eq(U32.mod(yy, 100), 0),
        U32.is_eq(U32.mod(yy, 400), 0))
    case Laws.Mar{}:
      {==}
    case Laws.Apr{}:
      {==}
    case Laws.May{}:
      {==}
    case Laws.Jun{}:
      {==}
    case Laws.Jul{}:
      {==}
    case Laws.Aug{}:
      {==}
    case Laws.Sep{}:
      {==}
    case Laws.Oct{}:
      {==}
    case Laws.Nov{}:
      {==}
    case Laws.Dec{}:
      {==}

# every month's number is from 1 to 12
def month.ok(mm: Laws.Month) -> {True{} == T.bound.rng(Laws.month.num(mm), 1, 12) : Bool}:
  match mm:
    case Laws.Jan{}:
      {==}
    case Laws.Feb{}:
      {==}
    case Laws.Mar{}:
      {==}
    case Laws.Apr{}:
      {==}
    case Laws.May{}:
      {==}
    case Laws.Jun{}:
      {==}
    case Laws.Jul{}:
      {==}
    case Laws.Aug{}:
      {==}
    case Laws.Sep{}:
      {==}
    case Laws.Oct{}:
      {==}
    case Laws.Nov{}:
      {==}
    case Laws.Dec{}:
      {==}

# the day test, with the code's days of the month turned into the table's
def day.test(
  +yy: U32,
  +mm: Laws.Month,
  +dd: U32
) -> {Bool.and(U32.is_ge(dd, 1), U32.is_le(dd, Laws.days_in(yy, mm)))
  == T.bound.rng(dd, 1, T.when.days(yy, Laws.month.num(mm))) : Bool}:
  Equal.cong(U32, Bool, xx => Bool.and(U32.is_ge(dd, 1), U32.is_le(dd, xx)),
    Laws.days_in(yy, mm), T.when.days(yy, Laws.month.num(mm)),
    Equal.sym(U32, T.when.days(yy, Laws.month.num(mm)), Laws.days_in(yy, mm), days.same(yy, mm)))

# the claim that a date is accepted and the rest read after it
def date.In(mo_ok: Bool, d_ok: Bool, +yy: U32, +mo: U32, +dd: U32, rest: List<&2, Char>) -> Type:
  {T.when.date.ok.go(mo_ok, d_ok, yy, mo, dd, rest) == T.when.after.date(T.Date{yy, mo, dd}, rest) : T.WhenOut}

# both tests passed, so the date is accepted
def date.in(
  mo_ok: Bool,
  d_ok: Bool,
  em: {True{} == mo_ok : Bool},
  ed: {True{} == d_ok : Bool},
  +yy: U32,
  +mo: U32,
  +dd: U32,
  rest: List<&2, Char>
) -> date.In(mo_ok, d_ok, yy, mo, dd, rest):
  match mo_ok d_ok:
    case True{} True{}:
      {==}
    case True{} False{}:
      Eq.bit.absurd2(&1, date.In(True{}, False{}, yy, mo, dd, rest), ed)
    case False{} dk:
      Eq.bit.absurd2(&1, date.In(False{}, dk, yy, mo, dd, rest), em)

# the claim that a date is refused
def date.Out(mo_ok: Bool, d_ok: Bool, +yy: U32, +mo: U32, +dd: U32, rest: List<&2, Char>) -> Type:
  {Laws.when_refused(T.when.date.ok.go(mo_ok, d_ok, yy, mo, dd, rest)) == True{} : Bool}

# the day test failed, so the date is refused whatever the month test said
def date.out(
  mo_ok: Bool,
  d_ok: Bool,
  ed: {False{} == d_ok : Bool},
  +yy: U32,
  +mo: U32,
  +dd: U32,
  rest: List<&2, Char>
) -> date.Out(mo_ok, d_ok, yy, mo, dd, rest):
  match mo_ok d_ok:
    case True{} False{}:
      {==}
    case True{} True{}:
      Eq.bit.absurd(&1, date.Out(True{}, True{}, yy, mo, dd, rest), ed)
    case False{} dk:
      {==}

# the month is in range, and the day test is the table's
def Laws.date_day_in_month(yy, mm, dd, rest, e):
  date.in(T.bound.rng(Laws.month.num(mm), 1, 12), T.bound.rng(dd, 1, T.when.days(yy, Laws.month.num(mm))),
    month.ok(mm),
    Equal.trans(Bool, True{}, Bool.and(U32.is_ge(dd, 1), U32.is_le(dd, Laws.days_in(yy, mm))),
      T.bound.rng(dd, 1, T.when.days(yy, Laws.month.num(mm))), e, day.test(yy, mm, dd)),
    yy, Laws.month.num(mm), dd, rest)

# the day test is the table's, and it failed
def Laws.date_day_past_month(yy, mm, dd, rest, e):
  date.out(T.bound.rng(Laws.month.num(mm), 1, 12), T.bound.rng(dd, 1, T.when.days(yy, Laws.month.num(mm))),
    Equal.trans(Bool, False{}, Bool.and(U32.is_ge(dd, 1), U32.is_le(dd, Laws.days_in(yy, mm))),
      T.bound.rng(dd, 1, T.when.days(yy, Laws.month.num(mm))), e, day.test(yy, mm, dd)),
    yy, Laws.month.num(mm), dd, rest)

# The scanner's refusals. A failed scanner sits in LSink with nothing held:
# every character leaves it as it is, and the end of the text reads its first
# error back. A refusal law then only follows one character from the state it
# names to that failed state.

# a failed scanner, its first error written as a first char and the rest
def sk(
  lead: Bool,
  b0: Char,
  bs: String,
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  parts: List<&2, String>,
  buf: List<&2, Char>,
  back: T.Lex,
  qkind: T.QKind,
  stack: List<&2, T.Ctx>,
  uni: U32,
  left: U32,
  arrtab: Bool
) -> T.St:
  T.St{SCon{b0, bs}, rows, heads, here, parts, buf, T.LSink{}, back, qkind, stack,
    T.HNone{}, uni, left, arrtab, lead}

# the mode a failed scanner is read in: after a carriage return, or not
def sk.mode(cr: Bool, st: T.St) -> T.Mode:
  match cr:
    case True{}:
      T.MCr{st}
    case False{}:
      T.MScan{st}

# the end of the text reads the first error back, open frames or not
def sk.fin(
  stack: List<&2, T.Ctx>,
  b0: Char,
  bs: String,
  rows: List<&2, T.Val>
) -> {T.bad(T.read.fin.stack(stack, SCon{b0, bs}, rows)) == SCon{b0, bs} : String}:
  match stack:
    case []:
      {==}
    case _h <> _t:
      {==}

# a byte-order mark or not, the first character leaves the failed scanner
def sk.bom(
  bom: Bool,
  b0: Char,
  bs: String,
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  parts: List<&2, String>,
  buf: List<&2, Char>,
  back: T.Lex,
  qkind: T.QKind,
  stack: List<&2, T.Ctx>,
  uni: U32,
  left: U32,
  arrtab: Bool,
  hh: Char
) -> {T.read.once2(T.read.step.bom(bom, sk(False{}, b0, bs, rows, heads, here, parts, buf,
  back, qkind, stack, uni, left, arrtab), hh)) == sk(False{}, b0, bs, rows, heads, here,
  parts, buf, back, qkind, stack, uni, left, arrtab) : T.St}:
  match bom:
    case True{}:
      {==}
    case False{}:
      {==}

# one character leaves the failed scanner as it is, past the first character
def sk.fast(
  lead: Bool,
  b0: Char,
  bs: String,
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  parts: List<&2, String>,
  buf: List<&2, Char>,
  back: T.Lex,
  qkind: T.QKind,
  stack: List<&2, T.Ctx>,
  uni: U32,
  left: U32,
  arrtab: Bool,
  +hh: Char
) -> {T.read.fast(sk(lead, b0, bs, rows, heads, here, parts, buf, back, qkind, stack, uni,
  left, arrtab), hh) == sk(False{}, b0, bs, rows, heads, here, parts, buf, back, qkind,
  stack, uni, left, arrtab) : T.St}:
  match lead:
    case False{}:
      {==}
    case True{}:
      sk.bom(U32.is_eq(Char.to_u32(hh), 65279), b0, bs, rows, heads, here, parts, buf, back,
        qkind, stack, uni, left, arrtab, hh)

# the rest of the text reads a failed scanner's first error back
def sk.ok(
  tt: String,
  cr: Bool,
  lead: Bool,
  b0: Char,
  bs: String,
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  parts: List<&2, String>,
  buf: List<&2, Char>,
  back: T.Lex,
  qkind: T.QKind,
  stack: List<&2, T.Ctx>,
  uni: U32,
  left: U32,
  arrtab: Bool
) -> Type:
  {T.bad(T.doc.read(tt, sk.mode(cr, sk(lead, b0, bs, rows, heads, here, parts, buf, back,
    qkind, stack, uni, left, arrtab)))) == SCon{b0, bs} : String}

# a character read in the scan mode: whichever way doc.scan turns, the failed
# scanner comes out as it went in
def sk.scan(
  dq: Bool,
  sq: Bool,
  cr: Bool,
  +lead: Bool,
  +b0: Char,
  +bs: String,
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
  +hh: Char,
  tt: String,
  ih0: sk.ok(tt, False{}, False{}, b0, bs, rows, heads, here, parts, buf, back, qkind, stack, uni, left, arrtab),
  ih1: sk.ok(tt, True{}, False{}, b0, bs, rows, heads, here, parts, buf, back, qkind, stack, uni, left, arrtab)
) -> {T.bad(T.doc.read(tt, T.doc.scan.q(dq, sq, cr, sk(lead, b0, bs, rows, heads, here,
  parts, buf, back, qkind, stack, uni, left, arrtab), hh))) == SCon{b0, bs} : String}:
  match dq:
    case True{}:
      Equal.trans(String,
        T.bad(T.doc.read(tt, T.doc.wrap(T.read.fast(sk(lead, b0, bs, rows, heads, here,
          parts, buf, back, qkind, stack, uni, left, arrtab), hh)))),
        T.bad(T.doc.read(tt, T.doc.wrap(sk(False{}, b0, bs, rows, heads, here, parts, buf,
          back, qkind, stack, uni, left, arrtab)))),
        SCon{b0, bs},
        Equal.cong(T.St, String, s => T.bad(T.doc.read(tt, T.doc.wrap(s))),
          T.read.fast(sk(lead, b0, bs, rows, heads, here, parts, buf, back, qkind, stack,
            uni, left, arrtab), hh),
          sk(False{}, b0, bs, rows, heads, here, parts, buf, back, qkind, stack, uni, left,
            arrtab),
          sk.fast(lead, b0, bs, rows, heads, here, parts, buf, back, qkind, stack, uni,
            left, arrtab, hh)),
        ih0)
    case False{}:
      match sq:
        case True{}:
          Equal.trans(String,
            T.bad(T.doc.read(tt, T.doc.wrap(T.read.fast(sk(lead, b0, bs, rows, heads, here,
              parts, buf, back, qkind, stack, uni, left, arrtab), hh)))),
            T.bad(T.doc.read(tt, T.doc.wrap(sk(False{}, b0, bs, rows, heads, here, parts,
              buf, back, qkind, stack, uni, left, arrtab)))),
            SCon{b0, bs},
            Equal.cong(T.St, String, s => T.bad(T.doc.read(tt, T.doc.wrap(s))),
              T.read.fast(sk(lead, b0, bs, rows, heads, here, parts, buf, back, qkind,
                stack, uni, left, arrtab), hh),
              sk(False{}, b0, bs, rows, heads, here, parts, buf, back, qkind, stack, uni,
                left, arrtab),
              sk.fast(lead, b0, bs, rows, heads, here, parts, buf, back, qkind, stack, uni,
                left, arrtab, hh)),
            ih0)
        case False{}:
          match cr:
            case True{}:
              Equal.trans(String,
                T.bad(T.doc.read(tt, T.MCr{T.read.fast(sk(lead, b0, bs, rows, heads, here,
                  parts, buf, back, qkind, stack, uni, left, arrtab), hh)})),
                T.bad(T.doc.read(tt, T.MCr{sk(False{}, b0, bs, rows, heads, here, parts,
                  buf, back, qkind, stack, uni, left, arrtab)})),
                SCon{b0, bs},
                Equal.cong(T.St, String, s => T.bad(T.doc.read(tt, T.MCr{s})),
                  T.read.fast(sk(lead, b0, bs, rows, heads, here, parts, buf, back, qkind,
                    stack, uni, left, arrtab), hh),
                  sk(False{}, b0, bs, rows, heads, here, parts, buf, back, qkind, stack,
                    uni, left, arrtab),
                  sk.fast(lead, b0, bs, rows, heads, here, parts, buf, back, qkind, stack,
                    uni, left, arrtab, hh)),
                ih1)
            case False{}:
              Equal.trans(String,
                T.bad(T.doc.read(tt, T.MScan{T.read.fast(sk(lead, b0, bs, rows, heads,
                  here, parts, buf, back, qkind, stack, uni, left, arrtab), hh)})),
                T.bad(T.doc.read(tt, T.MScan{sk(False{}, b0, bs, rows, heads, here, parts,
                  buf, back, qkind, stack, uni, left, arrtab)})),
                SCon{b0, bs},
                Equal.cong(T.St, String, s => T.bad(T.doc.read(tt, T.MScan{s})),
                  T.read.fast(sk(lead, b0, bs, rows, heads, here, parts, buf, back, qkind,
                    stack, uni, left, arrtab), hh),
                  sk(False{}, b0, bs, rows, heads, here, parts, buf, back, qkind, stack,
                    uni, left, arrtab),
                  sk.fast(lead, b0, bs, rows, heads, here, parts, buf, back, qkind, stack,
                    uni, left, arrtab, hh)),
                ih0)

# the character after a carriage return: a line feed is read, anything else
# sets an error the scanner already has
def sk.cr(
  lf: Bool,
  +lead: Bool,
  +b0: Char,
  +bs: String,
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
  +hh: Char,
  tt: String,
  ih0: sk.ok(tt, False{}, False{}, b0, bs, rows, heads, here, parts, buf, back, qkind, stack, uni, left, arrtab),
  ihl: sk.ok(tt, False{}, lead, b0, bs, rows, heads, here, parts, buf, back, qkind, stack, uni, left, arrtab)
) -> {T.bad(T.doc.read(tt, T.doc.cr(lf, sk(lead, b0, bs, rows, heads, here, parts, buf,
  back, qkind, stack, uni, left, arrtab), hh))) == SCon{b0, bs} : String}:
  match lf:
    case True{}:
      Equal.trans(String,
        T.bad(T.doc.read(tt, T.MScan{T.read.fast(sk(lead, b0, bs, rows, heads, here,
          parts, buf, back, qkind, stack, uni, left, arrtab), hh)})),
        T.bad(T.doc.read(tt, T.MScan{sk(False{}, b0, bs, rows, heads, here, parts, buf,
          back, qkind, stack, uni, left, arrtab)})),
        SCon{b0, bs},
        Equal.cong(T.St, String, s => T.bad(T.doc.read(tt, T.MScan{s})),
          T.read.fast(sk(lead, b0, bs, rows, heads, here, parts, buf, back, qkind, stack,
            uni, left, arrtab), hh),
          sk(False{}, b0, bs, rows, heads, here, parts, buf, back, qkind, stack, uni, left,
            arrtab),
          sk.fast(lead, b0, bs, rows, heads, here, parts, buf, back, qkind, stack, uni,
            left, arrtab, hh)),
        ih0)
    case False{}:
      ihl

# by induction on the text, in either mode, from either side of the first
# character
def sk.go(
  tt: String,
  cr: Bool,
  +lead: Bool,
  +b0: Char,
  +bs: String,
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
  +arrtab: Bool
) -> {T.bad(T.doc.read(tt, sk.mode(cr, sk(lead, b0, bs, rows, heads, here, parts, buf,
  back, qkind, stack, uni, left, arrtab)))) == SCon{b0, bs} : String}:
  match tt:
    case SNil{}:
      match cr:
        case True{}:
          sk.fin(stack, b0, bs, rows)
        case False{}:
          sk.fin(stack, b0, bs, rows)
    case SCon{+hh, +rest}:
      match cr:
        case False{}:
          sk.scan(Char.is_eq(hh, '"'), Char.is_eq(hh, '\''), U32.is_eq(Char.to_u32(hh), 13),
            lead, b0, bs, rows, heads, here, parts, buf, back, qkind, stack, uni, left,
            arrtab, hh, rest,
            sk.go(rest, False{}, False{}, b0, bs, rows, heads, here, parts, buf, back,
              qkind, stack, uni, left, arrtab),
            sk.go(rest, True{}, False{}, b0, bs, rows, heads, here, parts, buf, back,
              qkind, stack, uni, left, arrtab))
        case True{}:
          sk.cr(Char.is_eq(hh, '\n'), lead, b0, bs, rows, heads, here, parts, buf, back,
            qkind, stack, uni, left, arrtab, hh, rest,
            sk.go(rest, False{}, False{}, b0, bs, rows, heads, here, parts, buf, back,
              qkind, stack, uni, left, arrtab),
            sk.go(rest, False{}, lead, b0, bs, rows, heads, here, parts, buf, back, qkind,
              stack, uni, left, arrtab))

def Laws.fail_stays(
  bad,
  rows,
  heads,
  here,
  parts,
  buf,
  back,
  qkind,
  stack,
  uni,
  left,
  arrtab,
  lead,
  e,
  t
):
  match bad:
    case SNil{}:
      Eq.bit.absurd2(&2, {T.bad(T.doc.read(t, T.MScan{T.St{SNil{}, rows, heads, here, parts,
        buf, T.LSink{}, back, qkind, stack, T.HNone{}, uni, left, arrtab, lead}})) == SNil{}
        : String}, e)
    case SCon{b0, bs}:
      sk.go(t, False{}, lead, b0, bs, rows, heads, here, parts, buf, back, qkind, stack,
        uni, left, arrtab)

# any scanner that sets an error comes to the failed state, and the error it
# has then, its own or the new one, is never empty
def err.sinks(
  st: T.St,
  w0: Char,
  ws: String,
  +tt: String
) -> {String.is_empty(T.bad(T.doc.read(tt, T.MScan{T.st.err(st, SCon{w0, ws})})))
  == False{} : Bool}:
  match st:
    case T.St{bad, rows, heads, here, parts, buf, _lex, back, qkind, stack, _hold, uni,
      left, arrtab, lead}:
      match bad:
        case SNil{}:
          Equal.cong(String, Bool, s => String.is_empty(s),
            T.bad(T.doc.read(tt, T.MScan{sk(lead, w0, ws, rows, heads, here, parts, buf,
              back, qkind, stack, uni, left, arrtab)})),
            SCon{w0, ws},
            sk.go(tt, False{}, lead, w0, ws, rows, heads, here, parts, buf, back, qkind,
              stack, uni, left, arrtab))
        case SCon{b0, bs}:
          Equal.cong(String, Bool, s => String.is_empty(s),
            T.bad(T.doc.read(tt, T.MScan{sk(lead, b0, bs, rows, heads, here, parts, buf,
              back, qkind, stack, uni, left, arrtab)})),
            SCon{b0, bs},
            sk.go(tt, False{}, lead, b0, bs, rows, heads, here, parts, buf, back, qkind,
              stack, uni, left, arrtab))

# a character that is neither quote nor a carriage return is read in the scan
# mode. A law names such a character by a predicate that the three fail
def scan.other(
  dq: Bool,
  sq: Bool,
  cr: Bool,
  st: T.St,
  +cc: Char,
  edq: {Char.is_eq(cc, '"') == dq : Bool},
  esq: {Char.is_eq(cc, '\'') == sq : Bool},
  ecr: {Char.is_eq(cc, Chr{13}) == cr : Bool},
  pp: Char -> Bool,
  yes: {pp(cc) == True{} : Bool},
  n1: {pp('"') == False{} : Bool},
  n2: {pp('\'') == False{} : Bool},
  n3: {pp(Chr{13}) == False{} : Bool}
) -> {T.doc.scan.q(dq, sq, cr, st, cc) == T.MScan{T.read.fast(st, cc)} : T.Mode}:
  match dq:
    case True{}:
      Eq.bit.gone(&2, {T.doc.scan.q(True{}, sq, cr, st, cc) == T.MScan{T.read.fast(st, cc)}
        : T.Mode}, Eq.refute_char(cc, '"', pp, edq, yes, n1))
    case False{}:
      match sq:
        case True{}:
          Eq.bit.gone(&2, {T.doc.scan.q(False{}, True{}, cr, st, cc)
            == T.MScan{T.read.fast(st, cc)} : T.Mode},
            Eq.refute_char(cc, '\'', pp, esq, yes, n2))
        case False{}:
          match cr:
            case True{}:
              Eq.bit.gone(&2, {T.doc.scan.q(False{}, False{}, True{}, st, cc)
                == T.MScan{T.read.fast(st, cc)} : T.Mode},
                Eq.refute_char(cc, Chr{13}, pp, ecr, yes, n3))
            case False{}:
              {==}

# an equation between the two bits proves anything
def clash(a, -A: Kind(a), no: {False{} == True{} : Bool}) -> A:
  Eq.bit.absurd(a, A, no)

# a comment character that is a control, no newline and no tab fails the step
def com.go(
  nl: Bool,
  ctl: Bool,
  tab: Bool,
  st: T.St,
  cc: Char,
  enl: {T.ch.nl(cc) == nl : Bool},
  ectl: {T.ch.ctl(cc) == ctl : Bool},
  etab: {U32.is_eq(Char.to_u32(cc), 9) == tab : Bool},
  no_nl: {T.ch.nl(cc) == False{} : Bool},
  is_ctl: {T.ch.ctl(cc) == True{} : Bool},
  no_tab: {U32.is_eq(Char.to_u32(cc), 9) == False{} : Bool}
) -> {T.lex.com.go(nl, ctl, tab, st, cc) == T.st.err(st, "invalid control in comment")
  : T.St}:
  match nl:
    case True{}:
      clash(&2, {T.lex.com.go(True{}, ctl, tab, st, cc)
        == T.st.err(st, "invalid control in comment") : T.St},
        Equal.trans(Bool, False{}, T.ch.nl(cc), True{},
          Equal.sym(Bool, T.ch.nl(cc), False{}, no_nl), enl))
    case False{}:
      match ctl:
        case False{}:
          clash(&2, {T.lex.com.go(False{}, False{}, tab, st, cc)
            == T.st.err(st, "invalid control in comment") : T.St},
            Equal.trans(Bool, False{}, T.ch.ctl(cc), True{},
              Equal.sym(Bool, T.ch.ctl(cc), False{}, ectl), is_ctl))
        case True{}:
          match tab:
            case True{}:
              clash(&2, {T.lex.com.go(False{}, True{}, True{}, st, cc)
                == T.st.err(st, "invalid control in comment") : T.St},
                Equal.trans(Bool, False{}, U32.is_eq(Char.to_u32(cc), 9), True{},
                  Equal.sym(Bool, U32.is_eq(Char.to_u32(cc), 9), False{}, no_tab), etab))
            case False{}:
              {==}

# the fast path sends a control in a comment to the full step, which fails it
def com.fast(
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
  +xx: U32,
  ectl: {T.ch.ctl(Chr{xx}) == ctl : Bool},
  no_nl: {T.ch.nl(Chr{xx}) == False{} : Bool},
  is_ctl: {T.ch.ctl(Chr{xx}) == True{} : Bool},
  no_tab: {U32.is_eq(xx, 9) == False{} : Bool}
) -> {T.read.fast.com(ctl, bad, rows, heads, here, parts, buf, back, qkind, stack, uni,
  left, arrtab, Chr{xx}) == T.st.err(T.St{bad, rows, heads, here, parts, buf, T.LCom{},
  back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}}, "invalid control in comment")
  : T.St}:
  match ctl:
    case False{}:
      clash(&2, {T.read.fast.com(False{}, bad, rows, heads, here, parts, buf, back, qkind,
        stack, uni, left, arrtab, Chr{xx}) == T.st.err(T.St{bad, rows, heads, here, parts,
        buf, T.LCom{}, back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}},
        "invalid control in comment") : T.St},
        Equal.trans(Bool, False{}, T.ch.ctl(Chr{xx}), True{},
          Equal.sym(Bool, T.ch.ctl(Chr{xx}), False{}, ectl), is_ctl))
    case True{}:
      Equal.cong(T.St, T.St, s => T.read.once2(s),
        T.lex.com.go(T.ch.nl(Chr{xx}), T.ch.ctl(Chr{xx}), U32.is_eq(xx, 9),
          T.St{bad, rows, heads, here, parts, buf, T.LCom{}, back, qkind, stack, T.HNone{},
            uni, left, arrtab, False{}}, Chr{xx}),
        T.st.err(T.St{bad, rows, heads, here, parts, buf, T.LCom{}, back, qkind, stack,
          T.HNone{}, uni, left, arrtab, False{}}, "invalid control in comment"),
        com.go(T.ch.nl(Chr{xx}), T.ch.ctl(Chr{xx}), U32.is_eq(xx, 9),
          T.St{bad, rows, heads, here, parts, buf, T.LCom{}, back, qkind, stack, T.HNone{},
            uni, left, arrtab, False{}}, Chr{xx}, {==}, {==}, {==}, no_nl, is_ctl, no_tab))

# one comment character: the scan step and then the fast step, each past the
# branches the character cannot take
def com.step(
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
  +xx: U32,
  +ee: {Laws.com.ctl(Chr{xx}) == True{} : Bool}
) -> {T.doc.scan(T.St{bad, rows, heads, here, parts, buf, T.LCom{}, back, qkind, stack,
  T.HNone{}, uni, left, arrtab, False{}}, Chr{xx}) == T.MScan{T.st.err(T.St{bad, rows,
  heads, here, parts, buf, T.LCom{}, back, qkind, stack, T.HNone{}, uni, left, arrtab,
  False{}}, "invalid control in comment")} : T.Mode}:
  +nots = {Eq.and.right(T.ch.ctl(Chr{xx}), Bool.not(Bool.or(T.ch.nl(Chr{xx}),
    U32.is_eq(xx, 9))), ee) : {Bool.not(Bool.or(T.ch.nl(Chr{xx}), U32.is_eq(xx, 9)))
    == True{} : Bool}}
  +ors = {Eq.not.true(Bool.or(T.ch.nl(Chr{xx}), U32.is_eq(xx, 9)), nots)
    : {Bool.or(T.ch.nl(Chr{xx}), U32.is_eq(xx, 9)) == False{} : Bool}}
  Equal.trans(T.Mode,
    T.doc.scan(T.St{bad, rows, heads, here, parts, buf, T.LCom{}, back, qkind, stack,
      T.HNone{}, uni, left, arrtab, False{}}, Chr{xx}),
    T.MScan{T.read.fast(T.St{bad, rows, heads, here, parts, buf, T.LCom{}, back, qkind,
      stack, T.HNone{}, uni, left, arrtab, False{}}, Chr{xx})},
    T.MScan{T.st.err(T.St{bad, rows, heads, here, parts, buf, T.LCom{}, back, qkind, stack,
      T.HNone{}, uni, left, arrtab, False{}}, "invalid control in comment")},
    scan.other(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), U32.is_eq(xx, 13),
      T.St{bad, rows, heads, here, parts, buf, T.LCom{}, back, qkind, stack, T.HNone{},
        uni, left, arrtab, False{}}, Chr{xx}, {==}, {==}, {==}, ch => Laws.com.ctl(ch), ee, {==},
      {==}, {==}),
    Equal.cong(T.St, T.Mode, s => T.MScan{s},
      T.read.fast(T.St{bad, rows, heads, here, parts, buf, T.LCom{}, back, qkind, stack,
        T.HNone{}, uni, left, arrtab, False{}}, Chr{xx}),
      T.st.err(T.St{bad, rows, heads, here, parts, buf, T.LCom{}, back, qkind, stack,
        T.HNone{}, uni, left, arrtab, False{}}, "invalid control in comment"),
      com.fast(T.ch.ctl(Chr{xx}), bad, rows, heads, here, parts, buf, back, qkind, stack,
        uni, left, arrtab, xx, {==}, Eq.or.left_false(T.ch.nl(Chr{xx}), U32.is_eq(xx, 9),
        ors), Eq.and.left(T.ch.ctl(Chr{xx}), Bool.not(Bool.or(T.ch.nl(Chr{xx}),
        U32.is_eq(xx, 9))), ee), Eq.or.right_false(T.ch.nl(Chr{xx}), U32.is_eq(xx, 9),
        ors))))

def Laws.comment_control_refused(
  bad,
  rows,
  heads,
  here,
  parts,
  buf,
  back,
  qkind,
  stack,
  uni,
  left,
  arrtab,
  c,
  e,
  t
):
  match c:
    case Chr{+xx}:
      Equal.trans(Bool,
        String.is_empty(T.bad(T.doc.read(t, T.doc.scan(T.St{bad, rows, heads, here, parts,
          buf, T.LCom{}, back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}},
          Chr{xx})))),
        String.is_empty(T.bad(T.doc.read(t, T.MScan{T.st.err(T.St{bad, rows, heads, here,
          parts, buf, T.LCom{}, back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}},
          "invalid control in comment")}))),
        False{},
        Equal.cong(T.Mode, Bool, m => String.is_empty(T.bad(T.doc.read(t, m))),
          T.doc.scan(T.St{bad, rows, heads, here, parts, buf, T.LCom{}, back, qkind, stack,
            T.HNone{}, uni, left, arrtab, False{}}, Chr{xx}),
          T.MScan{T.st.err(T.St{bad, rows, heads, here, parts, buf, T.LCom{}, back, qkind,
            stack, T.HNone{}, uni, left, arrtab, False{}}, "invalid control in comment")},
          com.step(bad, rows, heads, here, parts, buf, back, qkind, stack, uni, left, arrtab,
            xx, e)),
        err.sinks(T.St{bad, rows, heads, here, parts, buf, T.LCom{}, back, qkind, stack,
          T.HNone{}, uni, left, arrtab, False{}}, 'i', "nvalid control in comment", t))

def Laws.lone_cr_refused(st, c, e, t):
  Equal.trans(Bool,
    String.is_empty(T.bad(T.doc.read(t, T.doc.cr(Char.is_eq(c, '\n'),
      T.read.fast(st, '\r'), c)))),
    String.is_empty(T.bad(T.doc.read(t, T.doc.cr(False{}, T.read.fast(st, '\r'), c)))),
    False{},
    Equal.cong(Bool, Bool,
      bb => String.is_empty(T.bad(T.doc.read(t, T.doc.cr(bb, T.read.fast(st, '\r'), c)))),
      Char.is_eq(c, '\n'), False{}, e),
    err.sinks(T.read.fast(st, '\r'), 'c', "arriage return without line feed", t))

def Laws.last_cr_refused(st):
  err.sinks(T.read.fast(st, '\r'), 'c', "arriage return without line feed", "")

# a line feed where the value should start fails the step, inside an inline
# table or not
def val.nl(
  stack: List<&2, T.Ctx>,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +buf: List<&2, Char>,
  +back: T.Lex,
  +qkind: T.QKind,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +tt: String
) -> {String.is_empty(T.bad(T.doc.read(tt, T.MScan{T.read.fast(T.St{bad, rows, heads,
  here, parts, buf, T.LVal{}, back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}},
  '\n')}))) == False{} : Bool}:
  match stack:
    case []:
      err.sinks(T.St{bad, rows, heads, here, parts, buf, T.LVal{}, back, qkind, [],
        T.HNone{}, uni, left, arrtab, False{}}, 'n', "ewline before value", tt)
    case T.CArr{items, ps, hs} <> rest:
      err.sinks(T.St{bad, rows, heads, here, parts, buf, T.LVal{}, back, qkind,
        T.CArr{items, ps, hs} <> rest, T.HNone{}, uni, left, arrtab, False{}}, 'n',
        "ewline before value", tt)
    case T.CInl{items, ps, hs} <> rest:
      err.sinks(T.St{bad, rows, heads, here, parts, buf, T.LVal{}, back, qkind,
        T.CInl{items, ps, hs} <> rest, T.HNone{}, uni, left, arrtab, False{}}, 'n',
        "ewline in inline table", tt)

def Laws.value_on_key_line(
  bad,
  rows,
  heads,
  here,
  parts,
  buf,
  back,
  qkind,
  stack,
  uni,
  left,
  arrtab,
  t
):
  val.nl(stack, bad, rows, heads, here, parts, buf, back, qkind, uni, left, arrtab, t)

# the carriage return fails the step, and the line feed after it changes nothing
def val.crlf(
  stack: List<&2, T.Ctx>,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +buf: List<&2, Char>,
  +back: T.Lex,
  +qkind: T.QKind,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +tt: String
) -> {String.is_empty(T.bad(T.doc.read(tt, T.MScan{T.read.fast(T.read.fast(T.St{bad, rows,
  heads, here, parts, buf, T.LVal{}, back, qkind, stack, T.HNone{}, uni, left, arrtab,
  False{}}, '\r'), '\n')}))) == False{} : Bool}:
  match stack:
    case []:
      err.sinks(T.St{bad, rows, heads, here, parts, buf, T.LVal{}, back, qkind, [],
        T.HNone{}, uni, left, arrtab, False{}}, 'n', "ewline before value", tt)
    case T.CArr{items, ps, hs} <> rest:
      err.sinks(T.St{bad, rows, heads, here, parts, buf, T.LVal{}, back, qkind,
        T.CArr{items, ps, hs} <> rest, T.HNone{}, uni, left, arrtab, False{}}, 'n',
        "ewline before value", tt)
    case T.CInl{items, ps, hs} <> rest:
      err.sinks(T.St{bad, rows, heads, here, parts, buf, T.LVal{}, back, qkind,
        T.CInl{items, ps, hs} <> rest, T.HNone{}, uni, left, arrtab, False{}}, 'n',
        "ewline in inline table", tt)

def Laws.value_on_key_line_crlf(
  bad,
  rows,
  heads,
  here,
  parts,
  buf,
  back,
  qkind,
  stack,
  uni,
  left,
  arrtab,
  t
):
  val.crlf(stack, bad, rows, heads, here, parts, buf, back, qkind, uni, left, arrtab, t)

# Multi-line strings. A body character a law calls plain is pushed onto the
# buffer, whichever kind the string is; the closing quotes are then read as
# plain text, since they are the same five or six characters for every body.

# the kind of a multi-line string: literal or basic
def mk(lit: Bool) -> T.QKind:
  match lit:
    case True{}:
      T.QMultiLit{}
    case False{}:
      T.QMulti{}

# a scanner inside a multi-line string, its body so far reversed in buf
def ms(
  lit: Bool,
  buf: List<&2, Char>,
  back: T.Lex,
  bad: String,
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  parts: List<&2, String>,
  stack: List<&2, T.Ctx>,
  uni: U32,
  left: U32,
  arrtab: Bool
) -> T.St:
  T.St{bad, rows, heads, here, parts, buf, T.LStr{}, back, mk(lit), stack, T.HNone{}, uni,
    left, arrtab, False{}}

# the characters of a text pushed one by one onto a buffer
def rev.onto(xs: String, acc: List<&2, Char>) -> List<&2, Char>:
  match xs:
    case SNil{}:
      acc
    case SCon{hh, tt}:
      rev.onto(tt, hh <> acc)

# a buffer the body was pushed onto reads back as the body, then what follows
def ml.rev(
  xs: String,
  acc: List<&2, Char>,
  tail: String
) -> {T.buf.str.go(rev.onto(xs, acc), tail) == T.buf.str.go(acc, String.append(xs, tail))
  : String}:
  match xs:
    case SNil{}:
      {==}
    case SCon{hh, tt}:
      ml.rev(tt, hh <> acc, tail)

# a code point that is one of two a predicate fails fails it too
def or2.no(
  +xx: U32,
  +k1: U32,
  +k2: U32,
  aa: Bool,
  bb: Bool,
  ea: {U32.is_eq(xx, k1) == aa : Bool},
  eb: {U32.is_eq(xx, k2) == bb : Bool},
  ee: {Bool.or(aa, bb) == True{} : Bool},
  pp: Char -> Bool,
  yes: {pp(Chr{xx}) == True{} : Bool},
  n1: {pp(Chr{k1}) == False{} : Bool},
  n2: {pp(Chr{k2}) == False{} : Bool}
) -> Empty:
  match aa:
    case True{}:
      Eq.refute_char(Chr{xx}, Chr{k1}, pp, ea, yes, n1)
    case False{}:
      Eq.refute_char(Chr{xx}, Chr{k2}, pp, Equal.trans(Bool, U32.is_eq(xx, k2), bb, True{},
        eb, ee), yes, n2)

# a raw character that is no control is pushed
def ml.ctl(
  ctrl: Bool,
  st: T.St,
  +xx: U32,
  ectl: {Bool.or(U32.is_lt(xx, 32), U32.is_eq(xx, 127)) == ctrl : Bool},
  noctl: {Bool.or(U32.is_lt(xx, 32), U32.is_eq(xx, 127)) == False{} : Bool}
) -> {T.lex.str.char.go(T.str.bad.go(ctrl, U32.is_eq(xx, 9), Bool.or(U32.is_eq(xx, 10),
  U32.is_eq(xx, 13)), True{}), st, Chr{xx}) == T.st.push(st, Chr{xx}, T.LStr{}) : T.St}:
  match ctrl:
    case True{}:
      clash(&2, {T.lex.str.char.go(T.str.bad.go(True{}, U32.is_eq(xx, 9),
        Bool.or(U32.is_eq(xx, 10), U32.is_eq(xx, 13)), True{}), st, Chr{xx})
        == T.st.push(st, Chr{xx}, T.LStr{}) : T.St},
        Equal.trans(Bool, False{}, Bool.or(U32.is_lt(xx, 32), U32.is_eq(xx, 127)), True{},
          Equal.sym(Bool, Bool.or(U32.is_lt(xx, 32), U32.is_eq(xx, 127)), False{}, noctl),
          ectl))
    case False{}:
      {==}

# no backslash in a basic string: the character is raw
def ml.bbs(
  bs: Bool,
  st: T.St,
  +xx: U32,
  ebs: {Char.is_eq(Chr{xx}, '\\') == bs : Bool},
  pp: Char -> Bool,
  yes: {pp(Chr{xx}) == True{} : Bool},
  nb: {pp('\\') == False{} : Bool},
  noctl: {Bool.or(U32.is_lt(xx, 32), U32.is_eq(xx, 127)) == False{} : Bool}
) -> {T.lex.str.bs(bs, True{}, st, Chr{xx}, T.QMulti{}) == T.st.push(st, Chr{xx}, T.LStr{})
  : T.St}:
  match bs:
    case True{}:
      Eq.bit.gone(&2, {T.lex.str.bs(True{}, True{}, st, Chr{xx}, T.QMulti{})
        == T.st.push(st, Chr{xx}, T.LStr{}) : T.St},
        Eq.refute_char(Chr{xx}, '\\', pp, ebs, yes, nb))
    case False{}:
      ml.ctl(Bool.or(U32.is_lt(xx, 32), U32.is_eq(xx, 127)), st, xx, {==}, noctl)

# no quote in a multi-line basic string: the character is not the closer
def ml.bq(
  quote: Bool,
  st: T.St,
  +xx: U32,
  eq: {Char.is_eq(Chr{xx}, '"') == quote : Bool},
  pp: Char -> Bool,
  +yes: {pp(Chr{xx}) == True{} : Bool},
  nq: {pp('"') == False{} : Bool},
  nb: {pp('\\') == False{} : Bool},
  noctl: {Bool.or(U32.is_lt(xx, 32), U32.is_eq(xx, 127)) == False{} : Bool}
) -> {T.lex.str.go(quote, True{}, True{}, st, Chr{xx}, T.QMulti{})
  == T.st.push(st, Chr{xx}, T.LStr{}) : T.St}:
  match quote:
    case True{}:
      Eq.bit.gone(&2, {T.lex.str.go(True{}, True{}, True{}, st, Chr{xx}, T.QMulti{})
        == T.st.push(st, Chr{xx}, T.LStr{}) : T.St},
        Eq.refute_char(Chr{xx}, '"', pp, eq, yes, nq))
    case False{}:
      ml.bbs(Char.is_eq(Chr{xx}, '\\'), st, xx, {==}, pp, yes, nb, noctl)

# no apostrophe in a multi-line literal string: the character is not the closer
def ml.lq(
  quote: Bool,
  st: T.St,
  +xx: U32,
  eq: {Char.is_eq(Chr{xx}, '\'') == quote : Bool},
  pp: Char -> Bool,
  yes: {pp(Chr{xx}) == True{} : Bool},
  nq: {pp('\'') == False{} : Bool},
  noctl: {Bool.or(U32.is_lt(xx, 32), U32.is_eq(xx, 127)) == False{} : Bool}
) -> {T.lex.str.go(quote, True{}, False{}, st, Chr{xx}, T.QMultiLit{})
  == T.st.push(st, Chr{xx}, T.LStr{}) : T.St}:
  match quote:
    case True{}:
      Eq.bit.gone(&2, {T.lex.str.go(True{}, True{}, False{}, st, Chr{xx}, T.QMultiLit{})
        == T.st.push(st, Chr{xx}, T.LStr{}) : T.St},
        Eq.refute_char(Chr{xx}, '\'', pp, eq, yes, nq))
    case False{}:
      ml.ctl(Bool.or(U32.is_lt(xx, 32), U32.is_eq(xx, 127)), st, xx, {==}, noctl)

# the controls a plain character is not
def ml.noctl(
  +xx: U32,
  ee: {Laws.ml.plain(Chr{xx}) == True{} : Bool}
) -> {Bool.or(U32.is_lt(xx, 32), U32.is_eq(xx, 127)) == False{} : Bool}:
  Eq.not.true(Bool.or(U32.is_lt(xx, 32), U32.is_eq(xx, 127)),
    Eq.and.left(Bool.not(Bool.or(U32.is_lt(xx, 32), U32.is_eq(xx, 127))),
      Bool.not(Bool.or(Char.is_eq(Chr{xx}, '"'), Bool.or(Char.is_eq(Chr{xx}, '\''),
        Char.is_eq(Chr{xx}, '\\')))), ee))

# a plain character inside a multi-line string of either kind is pushed
def ml.char(
  lit: Bool,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +buf: List<&2, Char>,
  +lx: T.Lex,
  +back: T.Lex,
  +stack: List<&2, T.Ctx>,
  +hold: T.Hold,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +lead: Bool,
  +xx: U32,
  +ee: {Laws.ml.plain(Chr{xx}) == True{} : Bool}
) -> {T.lex.str(T.St{bad, rows, heads, here, parts, buf, lx, back, mk(lit), stack, hold,
  uni, left, arrtab, lead}, Chr{xx}) == T.st.push(T.St{bad, rows, heads, here, parts, buf,
  lx, back, mk(lit), stack, hold, uni, left, arrtab, lead}, Chr{xx}, T.LStr{}) : T.St}:
  match lit:
    case False{}:
      ml.bq(Char.is_eq(Chr{xx}, '"'), T.St{bad, rows, heads, here, parts, buf, lx, back,
        T.QMulti{}, stack, hold, uni, left, arrtab, lead}, xx, {==},
        ch => Laws.ml.plain(ch), ee, {==}, {==}, ml.noctl(xx, ee))
    case True{}:
      ml.lq(Char.is_eq(Chr{xx}, '\''), T.St{bad, rows, heads, here, parts, buf, lx, back,
        T.QMultiLit{}, stack, hold, uni, left, arrtab, lead}, xx, {==},
        ch => Laws.ml.plain(ch), ee, {==}, ml.noctl(xx, ee))

# the fast path sends a multi-line string's character to the full step
def ml.fast(
  lit: Bool,
  +buf: List<&2, Char>,
  +back: T.Lex,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +stack: List<&2, T.Ctx>,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +xx: U32,
  +ee: {Laws.ml.plain(Chr{xx}) == True{} : Bool}
) -> {T.read.fast(ms(lit, buf, back, bad, rows, heads, here, parts, stack, uni, left,
  arrtab), Chr{xx}) == ms(lit, Chr{xx} <> buf, back, bad, rows, heads, here, parts, stack,
  uni, left, arrtab) : T.St}:
  match lit:
    case False{}:
      Equal.cong(T.St, T.St, s => T.read.once2(s),
        T.lex.str(T.St{bad, rows, heads, here, parts, buf, T.LStr{}, back, mk(False{}),
          stack, T.HNone{}, uni, left, arrtab, False{}}, Chr{xx}),
        T.st.push(T.St{bad, rows, heads, here, parts, buf, T.LStr{}, back, mk(False{}),
          stack, T.HNone{}, uni, left, arrtab, False{}}, Chr{xx}, T.LStr{}),
        ml.char(False{}, bad, rows, heads, here, parts, buf, T.LStr{}, back, stack,
          T.HNone{}, uni, left, arrtab, False{}, xx, ee))
    case True{}:
      Equal.cong(T.St, T.St, s => T.read.once2(s),
        T.lex.str(T.St{bad, rows, heads, here, parts, buf, T.LStr{}, back, mk(True{}),
          stack, T.HNone{}, uni, left, arrtab, False{}}, Chr{xx}),
        T.st.push(T.St{bad, rows, heads, here, parts, buf, T.LStr{}, back, mk(True{}),
          stack, T.HNone{}, uni, left, arrtab, False{}}, Chr{xx}, T.LStr{}),
        ml.char(True{}, bad, rows, heads, here, parts, buf, T.LStr{}, back, stack,
          T.HNone{}, uni, left, arrtab, False{}, xx, ee))

# one plain character of a multi-line string, from the scan mode
def ml.step(
  +lit: Bool,
  +buf: List<&2, Char>,
  +back: T.Lex,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +stack: List<&2, T.Ctx>,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +xx: U32,
  +ee: {Laws.ml.plain(Chr{xx}) == True{} : Bool}
) -> {T.doc.scan(ms(lit, buf, back, bad, rows, heads, here, parts, stack, uni, left,
  arrtab), Chr{xx}) == T.MScan{ms(lit, Chr{xx} <> buf, back, bad, rows, heads, here,
  parts, stack, uni, left, arrtab)} : T.Mode}:
  Equal.trans(T.Mode,
    T.doc.scan(ms(lit, buf, back, bad, rows, heads, here, parts, stack, uni, left, arrtab),
      Chr{xx}),
    T.MScan{T.read.fast(ms(lit, buf, back, bad, rows, heads, here, parts, stack, uni, left,
      arrtab), Chr{xx})},
    T.MScan{ms(lit, Chr{xx} <> buf, back, bad, rows, heads, here, parts, stack, uni, left,
      arrtab)},
    scan.other(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), U32.is_eq(xx, 13),
      ms(lit, buf, back, bad, rows, heads, here, parts, stack, uni, left, arrtab), Chr{xx},
      {==}, {==}, {==}, ch => Laws.ml.plain(ch), ee, {==}, {==}, {==}),
    Equal.cong(T.St, T.Mode, s => T.MScan{s},
      T.read.fast(ms(lit, buf, back, bad, rows, heads, here, parts, stack, uni, left,
        arrtab), Chr{xx}),
      ms(lit, Chr{xx} <> buf, back, bad, rows, heads, here, parts, stack, uni, left, arrtab),
      ml.fast(lit, buf, back, bad, rows, heads, here, parts, stack, uni, left, arrtab, xx,
        ee)))

# a body of plain characters is pushed onto the buffer, whatever follows it
def ml.body(
  xs: String,
  +rr: String,
  +lit: Bool,
  +buf: List<&2, Char>,
  +back: T.Lex,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +stack: List<&2, T.Ctx>,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +ee: {Laws.ml.text(xs) == True{} : Bool}
) -> {T.doc.read(String.append(xs, rr), T.MScan{ms(lit, buf, back, bad, rows, heads, here,
  parts, stack, uni, left, arrtab)}) == T.doc.read(rr, T.MScan{ms(lit, rev.onto(xs, buf),
  back, bad, rows, heads, here, parts, stack, uni, left, arrtab)}) : T.Doc}:
  match xs:
    case SNil{}:
      {==}
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          Equal.trans(T.Doc,
            T.doc.read(String.append(tt, rr), T.doc.scan(ms(lit, buf, back, bad, rows, heads,
              here, parts, stack, uni, left, arrtab), Chr{xx})),
            T.doc.read(String.append(tt, rr), T.MScan{ms(lit, Chr{xx} <> buf, back, bad,
              rows, heads, here, parts, stack, uni, left, arrtab)}),
            T.doc.read(rr, T.MScan{ms(lit, rev.onto(tt, Chr{xx} <> buf), back, bad, rows,
              heads, here, parts, stack, uni, left, arrtab)}),
            Equal.cong(T.Mode, T.Doc, m => T.doc.read(String.append(tt, rr), m),
              T.doc.scan(ms(lit, buf, back, bad, rows, heads, here, parts, stack, uni, left,
                arrtab), Chr{xx}),
              T.MScan{ms(lit, Chr{xx} <> buf, back, bad, rows, heads, here, parts, stack, uni,
                left, arrtab)},
              ml.step(lit, buf, back, bad, rows, heads, here, parts, stack, uni, left, arrtab,
                xx, Eq.and.left(Laws.ml.plain(Chr{xx}), Laws.ml.text(tt), ee))),
            ml.body(tt, rr, lit, Chr{xx} <> buf, back, bad, rows, heads, here, parts, stack,
              uni, left, arrtab, Eq.and.right(Laws.ml.plain(Chr{xx}), Laws.ml.text(tt), ee)))

# a multi-line string about to trim one opening newline
def mt(
  lit: Bool,
  buf: List<&2, Char>,
  back: T.Lex,
  bad: String,
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  parts: List<&2, String>,
  stack: List<&2, T.Ctx>,
  uni: U32,
  left: U32,
  arrtab: Bool
) -> T.St:
  T.St{bad, rows, heads, here, parts, buf, T.LTrim{}, back, mk(lit), stack, T.HNone{}, uni,
    left, arrtab, False{}}

# a plain first character is no newline to trim: it is held, then pushed
def ml.tgo(
  cr: Bool,
  nl: Bool,
  +lit: Bool,
  +buf: List<&2, Char>,
  +back: T.Lex,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +stack: List<&2, T.Ctx>,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +xx: U32,
  ecr: {U32.is_eq(xx, 13) == cr : Bool},
  enl: {T.ch.nl(Chr{xx}) == nl : Bool},
  +ee: {Laws.ml.plain(Chr{xx}) == True{} : Bool}
) -> {T.read.once2(T.lex.trim.go(cr, nl, mt(lit, buf, back, bad, rows, heads, here, parts,
  stack, uni, left, arrtab), Chr{xx})) == ms(lit, Chr{xx} <> buf, T.LStr{}, bad, rows,
  heads, here, parts, stack, uni, left, arrtab) : T.St}:
  match cr:
    case True{}:
      Eq.bit.gone(&2, {T.read.once2(T.lex.trim.go(True{}, nl, mt(lit, buf, back, bad, rows,
        heads, here, parts, stack, uni, left, arrtab), Chr{xx})) == ms(lit, Chr{xx} <> buf,
        T.LStr{}, bad, rows, heads, here, parts, stack, uni, left, arrtab) : T.St},
        Eq.refute_char(Chr{xx}, Chr{13}, ch => Laws.ml.plain(ch), ecr, ee, {==}))
    case False{}:
      match nl:
        case True{}:
          Eq.bit.gone(&2, {T.read.once2(T.lex.trim.go(False{}, True{}, mt(lit, buf, back,
            bad, rows, heads, here, parts, stack, uni, left, arrtab), Chr{xx}))
            == ms(lit, Chr{xx} <> buf, T.LStr{}, bad, rows, heads, here, parts, stack, uni,
            left, arrtab) : T.St},
            or2.no(xx, 10, 13, U32.is_eq(xx, 10), U32.is_eq(xx, 13), {==}, {==}, enl,
              ch => Laws.ml.plain(ch), ee, {==}, {==}))
        case False{}:
          ml.char(lit, bad, rows, heads, here, parts, buf, T.LStr{}, T.LStr{}, stack,
            T.HNone{}, uni, left, arrtab, False{}, xx, ee)

# the first plain character of a multi-line string, from the scan mode
def ml.first(
  +lit: Bool,
  +buf: List<&2, Char>,
  +back: T.Lex,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +stack: List<&2, T.Ctx>,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +xx: U32,
  +ee: {Laws.ml.plain(Chr{xx}) == True{} : Bool}
) -> {T.doc.scan(mt(lit, buf, back, bad, rows, heads, here, parts, stack, uni, left,
  arrtab), Chr{xx}) == T.MScan{ms(lit, Chr{xx} <> buf, T.LStr{}, bad, rows, heads, here,
  parts, stack, uni, left, arrtab)} : T.Mode}:
  Equal.trans(T.Mode,
    T.doc.scan(mt(lit, buf, back, bad, rows, heads, here, parts, stack, uni, left, arrtab),
      Chr{xx}),
    T.MScan{T.read.fast(mt(lit, buf, back, bad, rows, heads, here, parts, stack, uni, left,
      arrtab), Chr{xx})},
    T.MScan{ms(lit, Chr{xx} <> buf, T.LStr{}, bad, rows, heads, here, parts, stack, uni,
      left, arrtab)},
    scan.other(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), U32.is_eq(xx, 13),
      mt(lit, buf, back, bad, rows, heads, here, parts, stack, uni, left, arrtab), Chr{xx},
      {==}, {==}, {==}, ch => Laws.ml.plain(ch), ee, {==}, {==}, {==}),
    Equal.cong(T.St, T.Mode, s => T.MScan{s},
      T.read.fast(mt(lit, buf, back, bad, rows, heads, here, parts, stack, uni, left,
        arrtab), Chr{xx}),
      ms(lit, Chr{xx} <> buf, T.LStr{}, bad, rows, heads, here, parts, stack, uni, left,
        arrtab),
      ml.tgo(U32.is_eq(xx, 13), T.ch.nl(Chr{xx}), lit, buf, back, bad, rows, heads, here,
        parts, stack, uni, left, arrtab, xx, {==}, {==}, ee)))

# the document of one key `a` holding a string
def doc.a(ss: String) -> T.Doc:
  T.Doc{"", [T.VPair{"a", T.VStr{ss}}]}

# the closing quotes after a body pushed onto the buffer: the string closes
# with the quotes before the delimiter as its last characters
def ml.ends(
  lit: Bool,
  tail: String,
  extra: String,
  bb: List<&2, Char>
) -> Type:
  {T.doc.read(tail, T.MScan{ms(lit, bb, T.LStr{}, "", [], [], [], ["a"], [], 0, 0,
    False{})}) == doc.a(T.buf.str.go(bb, extra)) : T.Doc}

# a key `a` and a multi-line string of plain characters, from the character
# after the opening delimiter: the first character, the body, and then the
# closing quotes the law names, which `ends` reads
def ml.law(
  +lit: Bool,
  +tail: String,
  +extra: String,
  +xx: U32,
  +tt: String,
  +ee: {Bool.and(Laws.ml.plain(Chr{xx}), Laws.ml.text(tt)) == True{} : Bool},
  ends: ml.ends(lit, tail, extra, rev.onto(tt, [Chr{xx}]))
) -> {T.doc.read(String.append(tt, tail), T.doc.scan(mt(lit, [], T.LTop{}, "", [], [], [],
  ["a"], [], 0, 0, False{}), Chr{xx})) == T.Doc{"", [T.VPair{"a", T.VStr{SCon{Chr{xx},
  String.append(tt, extra)}}}]} : T.Doc}:
  Equal.trans(T.Doc,
    T.doc.read(String.append(tt, tail), T.doc.scan(mt(lit, [], T.LTop{}, "", [], [], [],
      ["a"], [], 0, 0, False{}), Chr{xx})),
    T.doc.read(String.append(tt, tail), T.MScan{ms(lit, [Chr{xx}], T.LStr{}, "", [], [], [],
      ["a"], [], 0, 0, False{})}),
    T.Doc{"", [T.VPair{"a", T.VStr{SCon{Chr{xx}, String.append(tt, extra)}}}]},
    Equal.cong(T.Mode, T.Doc, m => T.doc.read(String.append(tt, tail), m),
      T.doc.scan(mt(lit, [], T.LTop{}, "", [], [], [], ["a"], [], 0, 0, False{}), Chr{xx}),
      T.MScan{ms(lit, [Chr{xx}], T.LStr{}, "", [], [], [], ["a"], [], 0, 0, False{})},
      ml.first(lit, [], T.LTop{}, "", [], [], [], ["a"], [], 0, 0, False{}, xx,
        Eq.and.left(Laws.ml.plain(Chr{xx}), Laws.ml.text(tt), ee))),
    Equal.trans(T.Doc,
      T.doc.read(String.append(tt, tail), T.MScan{ms(lit, [Chr{xx}], T.LStr{}, "", [], [],
        [], ["a"], [], 0, 0, False{})}),
      T.doc.read(tail, T.MScan{ms(lit, rev.onto(tt, [Chr{xx}]), T.LStr{}, "", [], [], [],
        ["a"], [], 0, 0, False{})}),
      T.Doc{"", [T.VPair{"a", T.VStr{SCon{Chr{xx}, String.append(tt, extra)}}}]},
      ml.body(tt, tail, lit, [Chr{xx}], T.LStr{}, "", [], [], [], ["a"], [], 0, 0, False{},
        Eq.and.right(Laws.ml.plain(Chr{xx}), Laws.ml.text(tt), ee)),
      Equal.trans(T.Doc,
        T.doc.read(tail, T.MScan{ms(lit, rev.onto(tt, [Chr{xx}]), T.LStr{}, "", [], [], [],
          ["a"], [], 0, 0, False{})}),
        T.Doc{"", [T.VPair{"a", T.VStr{T.buf.str.go(rev.onto(tt, [Chr{xx}]), extra)}}]},
        T.Doc{"", [T.VPair{"a", T.VStr{SCon{Chr{xx}, String.append(tt, extra)}}}]},
        ends,
        Equal.cong(String, T.Doc, s => doc.a(s),
          T.buf.str.go(rev.onto(tt, [Chr{xx}]), extra),
          SCon{Chr{xx}, String.append(tt, extra)},
          ml.rev(tt, [Chr{xx}], extra)))))

def Laws.ml_basic_one_quote(x, e):
  match x:
    case SNil{}:
      {==}
    case SCon{hh, tt}:
      match hh:
        case Chr{xx}:
          ml.law(False{}, "\"\"\"\"\n", "\"", xx, tt, e, {==})

def Laws.ml_basic_two_quotes(x, e):
  match x:
    case SNil{}:
      {==}
    case SCon{hh, tt}:
      match hh:
        case Chr{xx}:
          ml.law(False{}, "\"\"\"\"\"", "\"\"", xx, tt, e, {==})

def Laws.ml_literal_one_quote(x, e):
  match x:
    case SNil{}:
      {==}
    case SCon{hh, tt}:
      match hh:
        case Chr{xx}:
          ml.law(True{}, "''''\n", "'", xx, tt, e, {==})

def Laws.ml_literal_two_quotes(x, e):
  match x:
    case SNil{}:
      {==}
    case SCon{hh, tt}:
      match hh:
        case Chr{xx}:
          ml.law(True{}, "'''''", "''", xx, tt, e, {==})

# Bare keys. A text of bare-key characters at the start of a document is
# pushed onto the buffer of a key; the first character comes through the
# byte-order-mark check and the top-level dispatch, every later one through
# the key's fast path.

# a scanner reading the first key of an empty document
def ky(buf: List<&2, Char>) -> T.St:
  T.St{"", [], [], [], [], buf, T.LKey{}, T.LTop{}, T.QBasic{}, [], T.HNone{}, 0, 0,
    False{}, False{}}

# the top-level dispatch sends a bare-key character to a new key
def key.top(
  sp: Bool,
  nl: Bool,
  hash: Bool,
  br: Bool,
  qq: Bool,
  lit: Bool,
  bare: Bool,
  st: T.St,
  +xx: U32,
  esp: {T.ch.sp(Chr{xx}) == sp : Bool},
  enl: {T.ch.nl(Chr{xx}) == nl : Bool},
  ehash: {Char.is_eq(Chr{xx}, '#') == hash : Bool},
  ebr: {Char.is_eq(Chr{xx}, '[') == br : Bool},
  eqq: {Char.is_eq(Chr{xx}, '"') == qq : Bool},
  elit: {Char.is_eq(Chr{xx}, '\'') == lit : Bool},
  ebare: {T.bare.at(Chr{xx}) == bare : Bool},
  +ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.lex.top.go(sp, nl, hash, br, qq, lit, bare, st, Chr{xx})
  == T.st.push(st, Chr{xx}, T.LKey{}) : T.St}:
  match sp:
    case True{}:
      Eq.bit.gone(&2, {T.lex.top.go(True{}, nl, hash, br, qq, lit, bare, st, Chr{xx})
        == T.st.push(st, Chr{xx}, T.LKey{}) : T.St},
        or2.no(xx, 32, 9, U32.is_eq(xx, 32), U32.is_eq(xx, 9), {==}, {==}, esp,
          ch => T.bare.at(ch), ee, {==}, {==}))
    case False{}:
      match nl:
        case True{}:
          Eq.bit.gone(&2, {T.lex.top.go(False{}, True{}, hash, br, qq, lit, bare, st,
            Chr{xx}) == T.st.push(st, Chr{xx}, T.LKey{}) : T.St},
            or2.no(xx, 10, 13, U32.is_eq(xx, 10), U32.is_eq(xx, 13), {==}, {==}, enl,
              ch => T.bare.at(ch), ee, {==}, {==}))
        case False{}:
          match hash:
            case True{}:
              Eq.bit.gone(&2, {T.lex.top.go(False{}, False{}, True{}, br, qq, lit, bare,
                st, Chr{xx}) == T.st.push(st, Chr{xx}, T.LKey{}) : T.St},
                Eq.refute_char(Chr{xx}, '#', ch => T.bare.at(ch), ehash, ee, {==}))
            case False{}:
              match br:
                case True{}:
                  Eq.bit.gone(&2, {T.lex.top.go(False{}, False{}, False{}, True{}, qq, lit,
                    bare, st, Chr{xx}) == T.st.push(st, Chr{xx}, T.LKey{}) : T.St},
                    Eq.refute_char(Chr{xx}, '[', ch => T.bare.at(ch), ebr, ee, {==}))
                case False{}:
                  match qq:
                    case True{}:
                      Eq.bit.gone(&2, {T.lex.top.go(False{}, False{}, False{}, False{},
                        True{}, lit, bare, st, Chr{xx}) == T.st.push(st, Chr{xx},
                        T.LKey{}) : T.St},
                        Eq.refute_char(Chr{xx}, '"', ch => T.bare.at(ch), eqq, ee, {==}))
                    case False{}:
                      match lit:
                        case True{}:
                          Eq.bit.gone(&2, {T.lex.top.go(False{}, False{}, False{}, False{},
                            False{}, True{}, bare, st, Chr{xx}) == T.st.push(st, Chr{xx},
                            T.LKey{}) : T.St},
                            Eq.refute_char(Chr{xx}, '\'', ch => T.bare.at(ch), elit, ee,
                              {==}))
                        case False{}:
                          match bare:
                            case True{}:
                              {==}
                            case False{}:
                              clash(&2, {T.lex.top.go(False{}, False{}, False{}, False{},
                                False{}, False{}, False{}, st, Chr{xx})
                                == T.st.push(st, Chr{xx}, T.LKey{}) : T.St},
                                Equal.trans(Bool, False{}, T.bare.at(Chr{xx}), True{},
                                  Equal.sym(Bool, T.bare.at(Chr{xx}), False{}, ebare), ee))

# the first character of the document: no byte-order mark, so a new key
def key.bom(
  bom: Bool,
  +xx: U32,
  ebom: {U32.is_eq(xx, 65279) == bom : Bool},
  +ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.read.once2(T.read.step.bom(bom, T.St{"", [], [], [], [], [], T.LTop{}, T.LTop{},
  T.QBasic{}, [], T.HNone{}, 0, 0, False{}, False{}}, Chr{xx})) == ky([Chr{xx}]) : T.St}:
  match bom:
    case True{}:
      Eq.bit.gone(&2, {T.read.once2(T.read.step.bom(True{}, T.St{"", [], [], [], [], [],
        T.LTop{}, T.LTop{}, T.QBasic{}, [], T.HNone{}, 0, 0, False{}, False{}}, Chr{xx}))
        == ky([Chr{xx}]) : T.St},
        Eq.refute_char(Chr{xx}, Chr{65279}, ch => T.bare.at(ch), ebom, ee, {==}))
    case False{}:
      Equal.cong(T.St, T.St, s => T.read.once2(s),
        T.lex.top.go(T.ch.sp(Chr{xx}), T.ch.nl(Chr{xx}), Char.is_eq(Chr{xx}, '#'),
          Char.is_eq(Chr{xx}, '['), Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''),
          T.bare.at(Chr{xx}), T.St{"", [], [], [], [], [], T.LTop{}, T.LTop{}, T.QBasic{},
          [], T.HNone{}, 0, 0, False{}, False{}}, Chr{xx}),
        T.st.push(T.St{"", [], [], [], [], [], T.LTop{}, T.LTop{}, T.QBasic{}, [],
          T.HNone{}, 0, 0, False{}, False{}}, Chr{xx}, T.LKey{}),
        key.top(T.ch.sp(Chr{xx}), T.ch.nl(Chr{xx}), Char.is_eq(Chr{xx}, '#'),
          Char.is_eq(Chr{xx}, '['), Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''),
          T.bare.at(Chr{xx}), T.St{"", [], [], [], [], [], T.LTop{}, T.LTop{}, T.QBasic{},
          [], T.HNone{}, 0, 0, False{}, False{}}, xx, {==}, {==}, {==}, {==}, {==}, {==},
          {==}, ee))

# the first character of the document starts a key
def key.first(
  +xx: U32,
  +ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.doc.scan(T.st.start(), Chr{xx}) == T.MScan{ky([Chr{xx}])} : T.Mode}:
  Equal.trans(T.Mode,
    T.doc.scan(T.st.start(), Chr{xx}),
    T.MScan{T.read.fast(T.st.start(), Chr{xx})},
    T.MScan{ky([Chr{xx}])},
    scan.other(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), U32.is_eq(xx, 13),
      T.st.start(), Chr{xx}, {==}, {==}, {==}, ch => T.bare.at(ch), ee, {==}, {==}, {==}),
    Equal.cong(T.St, T.Mode, s => T.MScan{s},
      T.read.fast(T.st.start(), Chr{xx}), ky([Chr{xx}]),
      key.bom(U32.is_eq(xx, 65279), xx, {==}, ee)))

# a later bare-key character stays on the key's fast path
def key.fast(
  ok: Bool,
  +buf: List<&2, Char>,
  +xx: U32,
  eok: {T.bare.at(Chr{xx}) == ok : Bool},
  ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.read.fast.key(ok, "", [], [], [], [], buf, T.LTop{}, T.QBasic{}, [], 0, 0, False{},
  Chr{xx}) == ky(Chr{xx} <> buf) : T.St}:
  match ok:
    case True{}:
      {==}
    case False{}:
      clash(&2, {T.read.fast.key(False{}, "", [], [], [], [], buf, T.LTop{}, T.QBasic{}, [],
        0, 0, False{}, Chr{xx}) == ky(Chr{xx} <> buf) : T.St},
        Equal.trans(Bool, False{}, T.bare.at(Chr{xx}), True{},
          Equal.sym(Bool, T.bare.at(Chr{xx}), False{}, eok), ee))

# one later character of the key, from the scan mode
def key.step(
  +buf: List<&2, Char>,
  +xx: U32,
  +ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.doc.scan(ky(buf), Chr{xx}) == T.MScan{ky(Chr{xx} <> buf)} : T.Mode}:
  Equal.trans(T.Mode,
    T.doc.scan(ky(buf), Chr{xx}),
    T.MScan{T.read.fast(ky(buf), Chr{xx})},
    T.MScan{ky(Chr{xx} <> buf)},
    scan.other(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), U32.is_eq(xx, 13),
      ky(buf), Chr{xx}, {==}, {==}, {==}, ch => T.bare.at(ch), ee, {==}, {==}, {==}),
    Equal.cong(T.St, T.Mode, s => T.MScan{s},
      T.read.fast(ky(buf), Chr{xx}), ky(Chr{xx} <> buf),
      key.fast(T.bare.at(Chr{xx}), buf, xx, {==}, ee)))

# the head of a bare-key walk that answered True answered True
def ball.head(
  here: Bool,
  tt: List<&2, Char>,
  ee: {T.bare.all.step(here, _u => T.bare.all(tt)) == True{} : Bool}
) -> {here == True{} : Bool}:
  match here:
    case True{}:
      {==}
    case False{}:
      ee

# and so did the rest of it
def ball.tail(
  here: Bool,
  tt: List<&2, Char>,
  ee: {T.bare.all.step(here, _u => T.bare.all(tt)) == True{} : Bool}
) -> {T.bare.all(tt) == True{} : Bool}:
  match here:
    case True{}:
      ee
    case False{}:
      Eq.bit.absurd(&2, {T.bare.all(tt) == True{} : Bool}, ee)

# a key of bare characters is pushed onto the buffer, whatever follows it
def key.body(
  ks: String,
  +rr: String,
  +buf: List<&2, Char>,
  +ee: {T.bare.all(String.to_list(ks)) == True{} : Bool}
) -> {T.doc.read(String.append(ks, rr), T.MScan{ky(buf)})
  == T.doc.read(rr, T.MScan{ky(rev.onto(ks, buf))}) : T.Doc}:
  match ks:
    case SNil{}:
      {==}
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          Equal.trans(T.Doc,
            T.doc.read(String.append(tt, rr), T.doc.scan(ky(buf), Chr{xx})),
            T.doc.read(String.append(tt, rr), T.MScan{ky(Chr{xx} <> buf)}),
            T.doc.read(rr, T.MScan{ky(rev.onto(tt, Chr{xx} <> buf))}),
            Equal.cong(T.Mode, T.Doc, m => T.doc.read(String.append(tt, rr), m),
              T.doc.scan(ky(buf), Chr{xx}), T.MScan{ky(Chr{xx} <> buf)},
              key.step(buf, xx, ball.head(T.bare.at(Chr{xx}), String.to_list(tt), ee))),
            key.body(tt, rr, Chr{xx} <> buf,
              ball.tail(T.bare.at(Chr{xx}), String.to_list(tt), ee)))

# a buffer something was pushed onto is not empty
def rev.full(
  xs: String,
  hh: Char,
  acc: List<&2, Char>
) -> {List.is_empty(&2, Char, rev.onto(xs, hh <> acc)) == False{} : Bool}:
  match xs:
    case SNil{}:
      {==}
    case SCon{h2, t2}:
      rev.full(t2, h2, hh <> acc)

# the document of one key holding the empty string
def doc.empty(ss: String) -> T.Doc:
  T.Doc{"", [T.VPair{ss, T.VStr{""}}]}

# the rest of the text after `=` ends the key: the document is the key and an
# empty string
def key.done(rest: String, bb: List<&2, Char>) -> Type:
  {T.doc.read(rest, T.MScan{T.read.once2(T.lex.key.end.go(False{}, ky(bb), T.LVal{}))})
    == doc.empty(T.buf.str.go(bb, "")) : T.Doc}

# `=` ends a nonempty key, and the rest of the text (an empty string of
# either kind) is read to the end: the document is the key and the value
def key.end(
  +rest: String,
  +bb: List<&2, Char>,
  full: {List.is_empty(&2, Char, bb) == False{} : Bool},
  done: key.done(rest, bb)
) -> {T.doc.read(SCon{'=', rest}, T.MScan{ky(bb)}) == T.Doc{"", [T.VPair{T.buf.str.go(bb,
  ""), T.VStr{""}}]} : T.Doc}:
  Equal.trans(T.Doc,
    T.doc.read(rest, T.MScan{T.read.once2(T.lex.key.end.go(List.is_empty(&2, Char, bb),
      ky(bb), T.LVal{}))}),
    T.doc.read(rest, T.MScan{T.read.once2(T.lex.key.end.go(False{}, ky(bb), T.LVal{}))}),
    T.Doc{"", [T.VPair{T.buf.str.go(bb, ""), T.VStr{""}}]},
    Equal.cong(Bool, T.Doc,
      b => T.doc.read(rest, T.MScan{T.read.once2(T.lex.key.end.go(b, ky(bb), T.LVal{}))}),
      List.is_empty(&2, Char, bb), False{}, full),
    done)

# a bare key, then `=` and an empty string that ends the text
def key.law(
  +rest: String,
  +xx: U32,
  +tt: String,
  +ee: {T.bare.all.step(T.bare.at(Chr{xx}), _u => T.bare.all(String.to_list(tt))) == True{} : Bool},
  done: key.done(rest, rev.onto(tt, [Chr{xx}]))
) -> {T.doc.read(String.append(tt, SCon{'=', rest}), T.doc.scan(T.st.start(), Chr{xx}))
  == doc.empty(SCon{Chr{xx}, tt}) : T.Doc}:
  Equal.trans(T.Doc,
    T.doc.read(String.append(tt, SCon{'=', rest}), T.doc.scan(T.st.start(), Chr{xx})),
    T.doc.read(String.append(tt, SCon{'=', rest}), T.MScan{ky([Chr{xx}])}),
    doc.empty(SCon{Chr{xx}, tt}),
    Equal.cong(T.Mode, T.Doc, m => T.doc.read(String.append(tt, SCon{'=', rest}), m),
      T.doc.scan(T.st.start(), Chr{xx}), T.MScan{ky([Chr{xx}])},
      key.first(xx, ball.head(T.bare.at(Chr{xx}), String.to_list(tt), ee))),
    Equal.trans(T.Doc,
      T.doc.read(String.append(tt, SCon{'=', rest}), T.MScan{ky([Chr{xx}])}),
      T.doc.read(SCon{'=', rest}, T.MScan{ky(rev.onto(tt, [Chr{xx}]))}),
      doc.empty(SCon{Chr{xx}, tt}),
      key.body(tt, SCon{'=', rest}, [Chr{xx}],
        ball.tail(T.bare.at(Chr{xx}), String.to_list(tt), ee)),
      Equal.trans(T.Doc,
        T.doc.read(SCon{'=', rest}, T.MScan{ky(rev.onto(tt, [Chr{xx}]))}),
        doc.empty(T.buf.str.go(rev.onto(tt, [Chr{xx}]), "")),
        doc.empty(SCon{Chr{xx}, tt}),
        key.end(rest, rev.onto(tt, [Chr{xx}]), rev.full(tt, Chr{xx}, []), done),
        Equal.cong(String, T.Doc, s => doc.empty(s),
          T.buf.str.go(rev.onto(tt, [Chr{xx}]), ""), SCon{Chr{xx}, tt},
          Equal.trans(String, T.buf.str.go(rev.onto(tt, [Chr{xx}]), ""),
            SCon{Chr{xx}, String.append(tt, "")}, SCon{Chr{xx}, tt},
            ml.rev(tt, [Chr{xx}], ""),
            Equal.cong(String, String, s => SCon{Chr{xx}, s}, String.append(tt, ""), tt,
              Eq.append_nil(tt)))))))

def Laws.empty_basic_at_end(k, e):
  match k:
    case SNil{}:
      Eq.bit.absurd(&2, {T.parse(String.append(SNil{}, "=\"\""))
        == T.Doc{"", [T.VPair{SNil{}, T.VStr{""}}]} : T.Doc}, e)
    case SCon{hh, tt}:
      match hh:
        case Chr{xx}:
          key.law("\"\"", xx, tt, e, {==})

def Laws.empty_literal_at_end(k, e):
  match k:
    case SNil{}:
      Eq.bit.absurd(&2, {T.parse(String.append(SNil{}, "=''"))
        == T.Doc{"", [T.VPair{SNil{}, T.VStr{""}}]} : T.Doc}, e)
    case SCon{hh, tt}:
      match hh:
        case Chr{xx}:
          key.law("''", xx, tt, e, {==})
# A head that matches itself: comparing h <> t with h <> o is comparing [h]
# with [h], and then t with o. A pair picks itself, the first pair of its name,
# and any other value meets itself first.

# a head's part and then the rest, as the part alone and the rest
def at.split(
  bb: Bool,
  -xx: Bool
) -> {Laws.and_then(bb, _u => xx) == Bool.and(Laws.and_then(bb, _u => True{}), xx) : Bool}:
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# a pair picks itself out of rows it heads
def pick.self(
  +nn: String,
  vv: T.Val,
  tt: List<&2, T.Val>
) -> {Laws.pick(T.VPair{nn, vv} <> tt, nn) == Laws.Picked{vv, tt} : Laws.Pick}:
  Equal.cong(Bool, Laws.Pick, bb => Laws.pick.step(bb, nn, vv, tt, _u => Laws.pick(tt, nn)),
    String.eq(nn, nn), True{}, Eq.string_eq_self(nn))

# a pair's head cancel, whatever its comparison and its rest
def hc.pair(
  +nn: String,
  +vv: T.Val,
  +oo: List<&2, T.Val>,
  cmp: T.Val -> Bool,
  -rest: List<&2, T.Val> -> Bool
) -> {Laws.same.pair(Laws.pick(T.VPair{nn, vv} <> oo, nn), cmp, rest)
  == Bool.and(Laws.same.pair(Laws.pick(T.VPair{nn, vv} <> [], nn), cmp, rr => Laws.same.go([], rr)), rest(oo))
  : Bool}:
  Equal.trans(Bool,
    Laws.same.pair(Laws.pick(T.VPair{nn, vv} <> oo, nn), cmp, rest),
    Laws.and_then(cmp(vv), _u => rest(oo)),
    Bool.and(Laws.same.pair(Laws.pick(T.VPair{nn, vv} <> [], nn), cmp, rr => Laws.same.go([], rr)), rest(oo)),
    Equal.cong(Laws.Pick, Bool, pp => Laws.same.pair(pp, cmp, rest),
      Laws.pick(T.VPair{nn, vv} <> oo, nn), Laws.Picked{vv, oo}, pick.self(nn, vv, oo)),
    Equal.trans(Bool,
      Laws.and_then(cmp(vv), _u => rest(oo)),
      Bool.and(Laws.and_then(cmp(vv), _u => True{}), rest(oo)),
      Bool.and(Laws.same.pair(Laws.pick(T.VPair{nn, vv} <> [], nn), cmp, rr => Laws.same.go([], rr)), rest(oo)),
      at.split(cmp(vv), rest(oo)),
      Equal.cong(Laws.Pick, Bool, pp => Bool.and(Laws.same.pair(pp, cmp, rr => Laws.same.go([], rr)), rest(oo)),
        Laws.Picked{vv, []}, Laws.pick(T.VPair{nn, vv} <> [], nn),
        Equal.sym(Laws.Pick, Laws.pick(T.VPair{nn, vv} <> [], nn), Laws.Picked{vv, []}, pick.self(nn, vv, [])))))

# any other value's head cancel
def hc.item(
  +hh: T.Val,
  +oo: List<&2, T.Val>,
  cmp: T.Val -> Bool,
  -rest: List<&2, T.Val> -> Bool
) -> {Laws.same.item(hh <> oo, cmp, rest)
  == Bool.and(Laws.same.item(hh <> [], cmp, rr => Laws.same.go([], rr)), rest(oo)) : Bool}:
  at.split(cmp(hh), rest(oo))

# a pair's head cancel, by the kind of its value
def hc.p(
  +nn: String,
  vv: T.Val,
  +tt: List<&2, T.Val>,
  +oo: List<&2, T.Val>
) -> {Laws.same.go(T.VPair{nn, vv} <> tt, T.VPair{nn, vv} <> oo)
  == Bool.and(Laws.same.go(T.VPair{nn, vv} <> [], T.VPair{nn, vv} <> []), Laws.same.go(tt, oo)) : Bool}:
  match vv:
    case T.VStr{+a1}:
      hc.pair(nn, T.VStr{a1}, oo, ww => Laws.same.atom(T.VStr{a1}, ww), rr => Laws.same.go(tt, rr))
    case T.VSpan{+a1, +a2}:
      hc.pair(nn, T.VSpan{a1, a2}, oo, ww => Laws.same.atom(T.VSpan{a1, a2}, ww), rr => Laws.same.go(tt, rr))
    case T.VInt{+a1, +a2}:
      hc.pair(nn, T.VInt{a1, a2}, oo, ww => Laws.same.atom(T.VInt{a1, a2}, ww), rr => Laws.same.go(tt, rr))
    case T.VFlo{+a1, +a2}:
      hc.pair(nn, T.VFlo{a1, a2}, oo, ww => Laws.same.atom(T.VFlo{a1, a2}, ww), rr => Laws.same.go(tt, rr))
    case T.VBool{+a1}:
      hc.pair(nn, T.VBool{a1}, oo, ww => Laws.same.atom(T.VBool{a1}, ww), rr => Laws.same.go(tt, rr))
    case T.VWhen{+a1}:
      hc.pair(nn, T.VWhen{a1}, oo, ww => Laws.same.atom(T.VWhen{a1}, ww), rr => Laws.same.go(tt, rr))
    case T.VArr{+ls}:
      hc.pair(nn, T.VArr{ls}, oo, ww => Laws.same.box(Laws.KArr{}, ww, ws => Laws.same.go(ls, ws)),
        rr => Laws.same.go(tt, rr))
    case T.VInl{+ls}:
      hc.pair(nn, T.VInl{ls}, oo, ww => Laws.same.box(Laws.KInl{}, ww, ws => Laws.same.go(ls, ws)),
        rr => Laws.same.go(tt, rr))
    case T.VHead{+pa, +ls}:
      hc.pair(nn, T.VHead{pa, ls}, oo, ww => Laws.same.box(Laws.KHead{}, ww, ws => Laws.same.go(ls, ws)),
        rr => Laws.same.go(tt, rr))
    case T.VAot{+pa, +ls}:
      hc.pair(nn, T.VAot{pa, ls}, oo, ww => Laws.same.box(Laws.KAot{}, ww, ws => Laws.same.go(ls, ws)),
        rr => Laws.same.go(tt, rr))
    case T.VAots{+pa, +ls}:
      hc.pair(nn, T.VAots{pa, ls}, oo, ww => Laws.same.box(Laws.KAots{}, ww, ws => Laws.same.go(ls, ws)),
        rr => Laws.same.go(tt, rr))
    case T.VPair{+a1, +a2}:
      hc.pair(nn, T.VPair{a1, a2}, oo, ww => Laws.same.atom(T.VPair{a1, a2}, ww), rr => Laws.same.go(tt, rr))

# a head matches itself, whatever it is
def hc(
  hh: T.Val,
  +tt: List<&2, T.Val>,
  +oo: List<&2, T.Val>
) -> {Laws.same.go(hh <> tt, hh <> oo) == Bool.and(Laws.same.go(hh <> [], hh <> []), Laws.same.go(tt, oo)) : Bool}:
  match hh:
    case T.VStr{+a1}:
      hc.item(T.VStr{a1}, oo, ww => Laws.same.atom(T.VStr{a1}, ww), rr => Laws.same.go(tt, rr))
    case T.VSpan{+a1, +a2}:
      hc.item(T.VSpan{a1, a2}, oo, ww => Laws.same.atom(T.VSpan{a1, a2}, ww), rr => Laws.same.go(tt, rr))
    case T.VInt{+a1, +a2}:
      hc.item(T.VInt{a1, a2}, oo, ww => Laws.same.atom(T.VInt{a1, a2}, ww), rr => Laws.same.go(tt, rr))
    case T.VFlo{+a1, +a2}:
      hc.item(T.VFlo{a1, a2}, oo, ww => Laws.same.atom(T.VFlo{a1, a2}, ww), rr => Laws.same.go(tt, rr))
    case T.VBool{+a1}:
      hc.item(T.VBool{a1}, oo, ww => Laws.same.atom(T.VBool{a1}, ww), rr => Laws.same.go(tt, rr))
    case T.VWhen{+a1}:
      hc.item(T.VWhen{a1}, oo, ww => Laws.same.atom(T.VWhen{a1}, ww), rr => Laws.same.go(tt, rr))
    case T.VArr{+ls}:
      hc.item(T.VArr{ls}, oo, ww => Laws.same.box(Laws.KArr{}, ww, ws => Laws.same.go(ls, ws)), rr => Laws.same.go(tt,
        rr))
    case T.VInl{+ls}:
      hc.item(T.VInl{ls}, oo, ww => Laws.same.box(Laws.KInl{}, ww, ws => Laws.same.go(ls, ws)), rr => Laws.same.go(tt,
        rr))
    case T.VHead{+pa, +ls}:
      hc.item(T.VHead{pa, ls}, oo, ww => Laws.same.box(Laws.KHead{}, ww, ws => Laws.same.go(ls, ws)),
        rr => Laws.same.go(tt, rr))
    case T.VAot{+pa, +ls}:
      hc.item(T.VAot{pa, ls}, oo, ww => Laws.same.box(Laws.KAot{}, ww, ws => Laws.same.go(ls, ws)),
        rr => Laws.same.go(tt, rr))
    case T.VAots{+pa, +ls}:
      hc.item(T.VAots{pa, ls}, oo, ww => Laws.same.box(Laws.KAots{}, ww, ws => Laws.same.go(ls, ws)),
        rr => Laws.same.go(tt, rr))
    case T.VPair{+nn, vv}:
      hc.p(nn, vv, tt, oo)

# every value of the rows matches itself alone
def selfs(xs: List<&2, T.Val>) -> Bool:
  match xs:
    case []:
      True{}
    case +hh <> tt:
      Bool.and(Laws.same.go(hh <> [], hh <> []), selfs(tt))

# an `and` of two parts that hold
def and.tt(
  aa: Bool,
  bb: Bool,
  ea: {aa == True{} : Bool},
  eb: {bb == True{} : Bool}
) -> {Bool.and(aa, bb) == True{} : Bool}:
  Equal.trans(Bool, Bool.and(aa, bb), Bool.and(True{}, bb), True{},
    Equal.cong(Bool, Bool, xx => Bool.and(xx, bb), aa, True{}, ea), eb)

# rows whose every value matches itself match themselves
def refl.rows(
  xs: List<&2, T.Val>,
  +ee: {selfs(xs) == True{} : Bool}
) -> {Laws.same.go(xs, xs) == True{} : Bool}:
  match xs:
    case []:
      {==}
    case +hh <> +tt:
      Equal.trans(Bool, Laws.same.go(hh <> tt, hh <> tt),
        Bool.and(Laws.same.go(hh <> [], hh <> []), Laws.same.go(tt, tt)), True{},
        hc(hh, tt, tt),
        and.tt(Laws.same.go(hh <> [], hh <> []), Laws.same.go(tt, tt),
          Eq.and.left(Laws.same.go(hh <> [], hh <> []), selfs(tt), ee),
          refl.rows(tt, Eq.and.right(Laws.same.go(hh <> [], hh <> []), selfs(tt), ee))))

# a part that holds, then a rest that holds
def at.tt(
  -bb: Bool,
  -more: Unit -> Bool,
  eb: {bb == True{} : Bool},
  em: {more(Unit{}) == True{} : Bool}
) -> {Laws.and_then(bb, more) == True{} : Bool}:
  Equal.trans(Bool, Laws.and_then(bb, more), Laws.and_then(True{}, more), True{},
    Equal.cong(Bool, Bool, xx => Laws.and_then(xx, more), bb, True{}, eb), em)

# a pair alone matches itself when its value does
def pair.self.tt(
  +nn: String,
  +vv: T.Val,
  -cmp: T.Val -> Bool,
  ec: {cmp(vv) == True{} : Bool}
) -> {Laws.same.pair(Laws.pick(T.VPair{nn, vv} <> [], nn), cmp, rr => Laws.same.go([], rr)) == True{} : Bool}:
  Equal.trans(Bool, Laws.same.pair(Laws.pick(T.VPair{nn, vv} <> [], nn), cmp, rr => Laws.same.go([], rr)),
    Laws.same.pair(Laws.Picked{vv, []}, cmp, rr => Laws.same.go([], rr)), True{},
    Equal.cong(Laws.Pick, Bool, pp => Laws.same.pair(pp, cmp, rr => Laws.same.go([], rr)),
      Laws.pick(T.VPair{nn, vv} <> [], nn), Laws.Picked{vv, []}, pick.self(nn, vv, [])),
    at.tt(cmp(vv), _u => True{}, ec, {==}))

# a value alone matches itself when it does
def item.self.tt(
  +hh: T.Val,
  -cmp: T.Val -> Bool,
  ec: {cmp(hh) == True{} : Bool}
) -> {Laws.same.item(hh <> [], cmp, rr => Laws.same.go([], rr)) == True{} : Bool}:
  at.tt(cmp(hh), _u => True{}, ec, {==})

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

# a well-formed table as a pair's value: the rest holds
def wf.head.more(
  at: T.WfAt,
  +name: String,
  +path: String,
  +rest: List<&2, T.Val>,
  -more: Unit -> Bool,
  ee: {T.wf.head(at, name, path, rest, more) == True{} : Bool}
) -> {more(Unit{}) == True{} : Bool}:
  match at:
    case T.WfRows{+here}:
      wt.more(Bool.and(T.wf.key(name, rest), T.str.eq(path, T.tree.pre(here, name))), more, ee)
    case T.WfInl{}:
      Eq.bit.absurd(&2, {more(Unit{}) == True{} : Bool}, ee)
    case T.WfItems{}:
      Eq.bit.absurd(&2, {more(Unit{}) == True{} : Bool}, ee)
    case T.WfElems{_h}:
      Eq.bit.absurd(&2, {more(Unit{}) == True{} : Bool}, ee)

# a well-formed array of tables as a pair's value: the rest holds
def wf.aots.more(
  at: T.WfAt,
  +name: String,
  +path: String,
  some: Bool,
  +rest: List<&2, T.Val>,
  -more: Unit -> Bool,
  ee: {T.wf.aots(at, name, path, some, rest, more) == True{} : Bool}
) -> {more(Unit{}) == True{} : Bool}:
  match at:
    case T.WfRows{+here}:
      wt.more(Bool.and(some, Bool.and(T.wf.key(name, rest), T.str.eq(path, T.tree.pre(here, name)))), more, ee)
    case T.WfInl{}:
      Eq.bit.absurd(&2, {more(Unit{}) == True{} : Bool}, ee)
    case T.WfItems{}:
      Eq.bit.absurd(&2, {more(Unit{}) == True{} : Bool}, ee)
    case T.WfElems{_h}:
      Eq.bit.absurd(&2, {more(Unit{}) == True{} : Bool}, ee)

# a well-formed element of an array of tables: the rest holds
def wf.aot.more(
  at: T.WfAt,
  +path: String,
  -more: Unit -> Bool,
  ee: {T.wf.aot(at, path, more) == True{} : Bool}
) -> {more(Unit{}) == True{} : Bool}:
  match at:
    case T.WfElems{+here}:
      wt.more(T.str.eq(path, here), more, ee)
    case T.WfRows{_h}:
      Eq.bit.absurd(&2, {more(Unit{}) == True{} : Bool}, ee)
    case T.WfInl{}:
      Eq.bit.absurd(&2, {more(Unit{}) == True{} : Bool}, ee)
    case T.WfItems{}:
      Eq.bit.absurd(&2, {more(Unit{}) == True{} : Bool}, ee)

# a well-formed pair of any other value: the rest holds
def wf.pair.more(
  at: T.WfAt,
  +name: String,
  +rest: List<&2, T.Val>,
  ok: Bool,
  -more: Unit -> Bool,
  ee: {T.wf.pair(at, name, rest, ok, more) == True{} : Bool}
) -> {more(Unit{}) == True{} : Bool}:
  match at:
    case T.WfRows{_h}:
      wt.more(Bool.and(ok, T.wf.key(name, rest)), more, ee)
    case T.WfInl{}:
      wt.more(Bool.and(ok, T.wf.key(name, rest)), more, ee)
    case T.WfItems{}:
      Eq.bit.absurd(&2, {more(Unit{}) == True{} : Bool}, ee)
    case T.WfElems{_h}:
      Eq.bit.absurd(&2, {more(Unit{}) == True{} : Bool}, ee)

# a well-formed pair of any other value: its value is well-formed
def wf.pair.ok(
  at: T.WfAt,
  +name: String,
  +rest: List<&2, T.Val>,
  +ok: Bool,
  -more: Unit -> Bool,
  ee: {T.wf.pair(at, name, rest, ok, more) == True{} : Bool}
) -> {ok == True{} : Bool}:
  match at:
    case T.WfRows{_h}:
      Eq.and.left(ok, T.wf.key(name, rest), wt.ok(Bool.and(ok, T.wf.key(name, rest)), more, ee))
    case T.WfInl{}:
      Eq.and.left(ok, T.wf.key(name, rest), wt.ok(Bool.and(ok, T.wf.key(name, rest)), more, ee))
    case T.WfItems{}:
      Eq.bit.absurd(&2, {ok == True{} : Bool}, ee)
    case T.WfElems{_h}:
      Eq.bit.absurd(&2, {ok == True{} : Bool}, ee)

# a well-formed item: the rest holds
def wf.item.more(
  at: T.WfAt,
  ok: Bool,
  -more: Unit -> Bool,
  ee: {T.wf.item(at, ok, more) == True{} : Bool}
) -> {more(Unit{}) == True{} : Bool}:
  match at:
    case T.WfItems{}:
      wt.more(ok, more, ee)
    case T.WfRows{_h}:
      Eq.bit.absurd(&2, {more(Unit{}) == True{} : Bool}, ee)
    case T.WfInl{}:
      Eq.bit.absurd(&2, {more(Unit{}) == True{} : Bool}, ee)
    case T.WfElems{_h}:
      Eq.bit.absurd(&2, {more(Unit{}) == True{} : Bool}, ee)

# a well-formed item: it is well-formed itself
def wf.item.ok(
  at: T.WfAt,
  ok: Bool,
  -more: Unit -> Bool,
  ee: {T.wf.item(at, ok, more) == True{} : Bool}
) -> {ok == True{} : Bool}:
  match at:
    case T.WfItems{}:
      wt.ok(ok, more, ee)
    case T.WfRows{_h}:
      Eq.bit.absurd(&2, {ok == True{} : Bool}, ee)
    case T.WfInl{}:
      Eq.bit.absurd(&2, {ok == True{} : Bool}, ee)
    case T.WfElems{_h}:
      Eq.bit.absurd(&2, {ok == True{} : Bool}, ee)

# a number equals itself
def u32.self(+xx: U32) -> {U32.is_eq(xx, xx) == True{} : Bool}:
  Equal.cong(Cmp, Bool, cc => Cmp.is_eq(cc), U32.cmp(xx, xx), EQ{}, Eq.u32_cmp_self(xx))

# a sign equals itself
def sign.self(sg: T.Sign) -> {Laws.sign.eq(sg, sg) == True{} : Bool}:
  match sg:
    case T.Plus{}:
      {==}
    case T.Minus{}:
      {==}

# a bit equals itself
def bit.self(bb: Bool) -> {Laws.bit.eq(bb, bb) == True{} : Bool}:
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# a date equals itself
def date.self(dd: T.Date) -> {Laws.date.eq(dd, dd) == True{} : Bool}:
  match dd:
    case T.Date{+yy, +mo, +dy}:
      and.tt(U32.is_eq(yy, yy), Bool.and(U32.is_eq(mo, mo), U32.is_eq(dy, dy)), u32.self(yy),
        and.tt(U32.is_eq(mo, mo), U32.is_eq(dy, dy), u32.self(mo), u32.self(dy)))

# a clock equals itself
def clock.self(cc: T.Clock) -> {Laws.clock.eq(cc, cc) == True{} : Bool}:
  match cc:
    case T.Clock{+hh, +mi, +ss, +fr}:
      and.tt(U32.is_eq(hh, hh), Bool.and(U32.is_eq(mi, mi), Bool.and(U32.is_eq(ss, ss), String.eq(fr, fr))),
        u32.self(hh),
        and.tt(U32.is_eq(mi, mi), Bool.and(U32.is_eq(ss, ss), String.eq(fr, fr)), u32.self(mi),
          and.tt(U32.is_eq(ss, ss), String.eq(fr, fr), u32.self(ss), Eq.string_eq_self(fr))))

# a zone equals itself
def zone.self(zz: T.Zone) -> {Laws.zone.eq(zz, zz) == True{} : Bool}:
  match zz:
    case T.Zulu{}:
      {==}
    case T.Shift{+sg, +hh, +mi}:
      and.tt(Laws.sign.eq(sg, sg), Bool.and(U32.is_eq(hh, hh), U32.is_eq(mi, mi)), sign.self(sg),
        and.tt(U32.is_eq(hh, hh), U32.is_eq(mi, mi), u32.self(hh), u32.self(mi)))

# a datetime equals itself
def when.self(ww: T.When) -> {Laws.when.eq(ww, ww) == True{} : Bool}:
  match ww:
    case T.WOff{+dd, +cc, +zz}:
      and.tt(Laws.date.eq(dd, dd), Bool.and(Laws.clock.eq(cc, cc), Laws.zone.eq(zz, zz)), date.self(dd),
        and.tt(Laws.clock.eq(cc, cc), Laws.zone.eq(zz, zz), clock.self(cc), zone.self(zz)))
    case T.WLocal{+dd, +cc}:
      and.tt(Laws.date.eq(dd, dd), Laws.clock.eq(cc, cc), date.self(dd), clock.self(cc))
    case T.WDate{+dd}:
      date.self(dd)
    case T.WTime{+cc}:
      clock.self(cc)

# a well-formed scalar is the same scalar as itself
def atom.self(
  vv: T.Val,
  ee: {T.wf.atom(vv) == True{} : Bool}
) -> {Laws.same.atom(vv, vv) == True{} : Bool}:
  match vv:
    case T.VStr{+a1}:
      Eq.string_eq_self(a1)
    case T.VSpan{+a1, +a2}:
      Eq.string_eq_self(T.span.str(a1, a2, U32.is_zero(a2)))
    case T.VInt{+a1, +a2}:
      and.tt(Laws.sign.eq(a1, a1), String.eq(a2, a2), sign.self(a1), Eq.string_eq_self(a2))
    case T.VFlo{+a1, +a2}:
      and.tt(Laws.sign.eq(a1, a1), String.eq(a2, a2), sign.self(a1), Eq.string_eq_self(a2))
    case T.VBool{+a1}:
      bit.self(a1)
    case T.VWhen{+a1}:
      when.self(a1)
    case T.VArr{+ls}:
      Eq.bit.absurd(&2, {Laws.same.atom(T.VArr{ls}, T.VArr{ls}) == True{} : Bool}, ee)
    case T.VInl{+ls}:
      Eq.bit.absurd(&2, {Laws.same.atom(T.VInl{ls}, T.VInl{ls}) == True{} : Bool}, ee)
    case T.VHead{+pa, +ls}:
      Eq.bit.absurd(&2, {Laws.same.atom(T.VHead{pa, ls}, T.VHead{pa, ls}) == True{} : Bool}, ee)
    case T.VAot{+pa, +ls}:
      Eq.bit.absurd(&2, {Laws.same.atom(T.VAot{pa, ls}, T.VAot{pa, ls}) == True{} : Bool}, ee)
    case T.VAots{+pa, +ls}:
      Eq.bit.absurd(&2, {Laws.same.atom(T.VAots{pa, ls}, T.VAots{pa, ls}) == True{} : Bool}, ee)
    case T.VPair{+a1, +a2}:
      Eq.bit.absurd(&2, {Laws.same.atom(T.VPair{a1, a2}, T.VPair{a1, a2}) == True{} : Bool}, ee)

# the values of well-formed rows each match themselves alone, by induction
# on the rows: a table, an inline table, an array or an array of tables
# matches itself by its list, a scalar by its fields, and wf rules out the
# rest
def wf.selfs(
  xs: List<&2, T.Val>,
  +at: T.WfAt,
  +ee: {T.wf.go(xs, at) == True{} : Bool}
) -> {selfs(xs) == True{} : Bool}:
  match xs:
    case []:
      {==}
    case T.VPair{+nn, T.VStr{+a1}} <> +tt:
      and.tt(Laws.same.go(T.VPair{nn, T.VStr{a1}} <> [], T.VPair{nn, T.VStr{a1}} <> []), selfs(tt),
        pair.self.tt(nn, T.VStr{a1}, ww => Laws.same.atom(T.VStr{a1}, ww), atom.self(T.VStr{a1}, wf.pair.ok(at, nn, tt,
          T.wf.atom(T.VStr{a1}), _u => T.wf.go(tt, at), ee))),
        wf.selfs(tt, at, wf.pair.more(at, nn, tt, T.wf.atom(T.VStr{a1}), _u => T.wf.go(tt, at), ee)))
    case T.VPair{+nn, T.VSpan{+a1, +a2}} <> +tt:
      and.tt(Laws.same.go(T.VPair{nn, T.VSpan{a1, a2}} <> [], T.VPair{nn, T.VSpan{a1, a2}} <> []), selfs(tt),
        pair.self.tt(nn, T.VSpan{a1, a2}, ww => Laws.same.atom(T.VSpan{a1, a2}, ww), atom.self(T.VSpan{a1, a2},
          wf.pair.ok(at, nn, tt, T.wf.atom(T.VSpan{a1, a2}), _u => T.wf.go(tt, at), ee))),
        wf.selfs(tt, at, wf.pair.more(at, nn, tt, T.wf.atom(T.VSpan{a1, a2}), _u => T.wf.go(tt, at), ee)))
    case T.VPair{+nn, T.VInt{+a1, +a2}} <> +tt:
      and.tt(Laws.same.go(T.VPair{nn, T.VInt{a1, a2}} <> [], T.VPair{nn, T.VInt{a1, a2}} <> []), selfs(tt),
        pair.self.tt(nn, T.VInt{a1, a2}, ww => Laws.same.atom(T.VInt{a1, a2}, ww), atom.self(T.VInt{a1, a2},
          wf.pair.ok(at, nn, tt, T.wf.atom(T.VInt{a1, a2}), _u => T.wf.go(tt, at), ee))),
        wf.selfs(tt, at, wf.pair.more(at, nn, tt, T.wf.atom(T.VInt{a1, a2}), _u => T.wf.go(tt, at), ee)))
    case T.VPair{+nn, T.VFlo{+a1, +a2}} <> +tt:
      and.tt(Laws.same.go(T.VPair{nn, T.VFlo{a1, a2}} <> [], T.VPair{nn, T.VFlo{a1, a2}} <> []), selfs(tt),
        pair.self.tt(nn, T.VFlo{a1, a2}, ww => Laws.same.atom(T.VFlo{a1, a2}, ww), atom.self(T.VFlo{a1, a2},
          wf.pair.ok(at, nn, tt, T.wf.atom(T.VFlo{a1, a2}), _u => T.wf.go(tt, at), ee))),
        wf.selfs(tt, at, wf.pair.more(at, nn, tt, T.wf.atom(T.VFlo{a1, a2}), _u => T.wf.go(tt, at), ee)))
    case T.VPair{+nn, T.VBool{+a1}} <> +tt:
      and.tt(Laws.same.go(T.VPair{nn, T.VBool{a1}} <> [], T.VPair{nn, T.VBool{a1}} <> []), selfs(tt),
        pair.self.tt(nn, T.VBool{a1}, ww => Laws.same.atom(T.VBool{a1}, ww), atom.self(T.VBool{a1}, wf.pair.ok(at, nn,
          tt, T.wf.atom(T.VBool{a1}), _u => T.wf.go(tt, at), ee))),
        wf.selfs(tt, at, wf.pair.more(at, nn, tt, T.wf.atom(T.VBool{a1}), _u => T.wf.go(tt, at), ee)))
    case T.VPair{+nn, T.VWhen{+a1}} <> +tt:
      and.tt(Laws.same.go(T.VPair{nn, T.VWhen{a1}} <> [], T.VPair{nn, T.VWhen{a1}} <> []), selfs(tt),
        pair.self.tt(nn, T.VWhen{a1}, ww => Laws.same.atom(T.VWhen{a1}, ww), atom.self(T.VWhen{a1}, wf.pair.ok(at, nn,
          tt, T.wf.atom(T.VWhen{a1}), _u => T.wf.go(tt, at), ee))),
        wf.selfs(tt, at, wf.pair.more(at, nn, tt, T.wf.atom(T.VWhen{a1}), _u => T.wf.go(tt, at), ee)))
    case T.VPair{+nn, T.VArr{+ls}} <> +tt:
      and.tt(Laws.same.go(T.VPair{nn, T.VArr{ls}} <> [], T.VPair{nn, T.VArr{ls}} <> []), selfs(tt),
        pair.self.tt(nn, T.VArr{ls}, ww => Laws.same.box(Laws.KArr{}, ww, ws => Laws.same.go(ls, ws)), refl.rows(ls,
          wf.selfs(ls, T.WfItems{}, wt.ok(T.wf.go(ls, T.WfItems{}), _v => T.wf.go(tt, at), wf.pair.more(at, nn, tt,
          True{}, _u => T.wf.then(T.wf.go(ls, T.WfItems{}), _v => T.wf.go(tt, at)), ee))))),
        wf.selfs(tt, at, wt.more(T.wf.go(ls, T.WfItems{}), _v => T.wf.go(tt, at), wf.pair.more(at, nn, tt, True{},
          _u => T.wf.then(T.wf.go(ls, T.WfItems{}), _v => T.wf.go(tt, at)), ee))))
    case T.VPair{+nn, T.VInl{+ls}} <> +tt:
      and.tt(Laws.same.go(T.VPair{nn, T.VInl{ls}} <> [], T.VPair{nn, T.VInl{ls}} <> []), selfs(tt),
        pair.self.tt(nn, T.VInl{ls}, ww => Laws.same.box(Laws.KInl{}, ww, ws => Laws.same.go(ls, ws)), refl.rows(ls,
          wf.selfs(ls, T.WfInl{}, wt.ok(T.wf.go(ls, T.WfInl{}), _v => T.wf.go(tt, at), wf.pair.more(at, nn, tt, True{},
          _u => T.wf.then(T.wf.go(ls, T.WfInl{}), _v => T.wf.go(tt, at)), ee))))),
        wf.selfs(tt, at, wt.more(T.wf.go(ls, T.WfInl{}), _v => T.wf.go(tt, at), wf.pair.more(at, nn, tt, True{},
          _u => T.wf.then(T.wf.go(ls, T.WfInl{}), _v => T.wf.go(tt, at)), ee))))
    case T.VPair{+nn, T.VHead{+pa, +ls}} <> +tt:
      and.tt(Laws.same.go(T.VPair{nn, T.VHead{pa, ls}} <> [], T.VPair{nn, T.VHead{pa, ls}} <> []), selfs(tt),
        pair.self.tt(nn, T.VHead{pa, ls}, ww => Laws.same.box(Laws.KHead{}, ww, ws => Laws.same.go(ls, ws)),
          refl.rows(ls, wf.selfs(ls, T.WfRows{pa}, wt.ok(T.wf.go(ls, T.WfRows{pa}), _v => T.wf.go(tt, at),
          wf.head.more(at, nn, pa, tt, _u => T.wf.then(T.wf.go(ls, T.WfRows{pa}), _v => T.wf.go(tt, at)), ee))))),
        wf.selfs(tt, at, wt.more(T.wf.go(ls, T.WfRows{pa}), _v => T.wf.go(tt, at), wf.head.more(at, nn, pa, tt,
          _u => T.wf.then(T.wf.go(ls, T.WfRows{pa}), _v => T.wf.go(tt, at)), ee))))
    case T.VPair{+nn, T.VAot{+pa, +ls}} <> +tt:
      Eq.bit.absurd(&2, {selfs(T.VPair{nn, T.VAot{pa, ls}} <> tt) == True{} : Bool}, wf.pair.ok(at, nn, tt,
        T.wf.atom(T.VAot{pa, ls}), _u => T.wf.go(tt, at), ee))
    case T.VPair{+nn, T.VAots{+pa, +ls}} <> +tt:
      and.tt(Laws.same.go(T.VPair{nn, T.VAots{pa, ls}} <> [], T.VPair{nn, T.VAots{pa, ls}} <> []), selfs(tt),
        pair.self.tt(nn, T.VAots{pa, ls}, ww => Laws.same.box(Laws.KAots{}, ww, ws => Laws.same.go(ls, ws)),
          refl.rows(ls, wf.selfs(ls, T.WfElems{pa}, wt.ok(T.wf.go(ls, T.WfElems{pa}), _v => T.wf.go(tt, at),
          wf.aots.more(at, nn, pa, Bool.not(List.is_empty(&2, T.Val, ls)), tt, _u => T.wf.then(T.wf.go(ls,
          T.WfElems{pa}), _v => T.wf.go(tt, at)), ee))))),
        wf.selfs(tt, at, wt.more(T.wf.go(ls, T.WfElems{pa}), _v => T.wf.go(tt, at), wf.aots.more(at, nn, pa,
          Bool.not(List.is_empty(&2, T.Val, ls)), tt, _u => T.wf.then(T.wf.go(ls, T.WfElems{pa}), _v => T.wf.go(tt,
          at)), ee))))
    case T.VPair{+nn, T.VPair{+a1, +a2}} <> +tt:
      Eq.bit.absurd(&2, {selfs(T.VPair{nn, T.VPair{a1, a2}} <> tt) == True{} : Bool}, wf.pair.ok(at, nn, tt,
        T.wf.atom(T.VPair{a1, a2}), _u => T.wf.go(tt, at), ee))
    case T.VStr{+a1} <> +tt:
      and.tt(Laws.same.go(T.VStr{a1} <> [], T.VStr{a1} <> []), selfs(tt),
        item.self.tt(T.VStr{a1}, ww => Laws.same.atom(T.VStr{a1}, ww), atom.self(T.VStr{a1}, wf.item.ok(at,
          T.wf.atom(T.VStr{a1}), _u => T.wf.go(tt, at), ee))),
        wf.selfs(tt, at, wf.item.more(at, T.wf.atom(T.VStr{a1}), _u => T.wf.go(tt, at), ee)))
    case T.VSpan{+a1, +a2} <> +tt:
      and.tt(Laws.same.go(T.VSpan{a1, a2} <> [], T.VSpan{a1, a2} <> []), selfs(tt),
        item.self.tt(T.VSpan{a1, a2}, ww => Laws.same.atom(T.VSpan{a1, a2}, ww), atom.self(T.VSpan{a1, a2},
          wf.item.ok(at, T.wf.atom(T.VSpan{a1, a2}), _u => T.wf.go(tt, at), ee))),
        wf.selfs(tt, at, wf.item.more(at, T.wf.atom(T.VSpan{a1, a2}), _u => T.wf.go(tt, at), ee)))
    case T.VInt{+a1, +a2} <> +tt:
      and.tt(Laws.same.go(T.VInt{a1, a2} <> [], T.VInt{a1, a2} <> []), selfs(tt),
        item.self.tt(T.VInt{a1, a2}, ww => Laws.same.atom(T.VInt{a1, a2}, ww), atom.self(T.VInt{a1, a2}, wf.item.ok(at,
          T.wf.atom(T.VInt{a1, a2}), _u => T.wf.go(tt, at), ee))),
        wf.selfs(tt, at, wf.item.more(at, T.wf.atom(T.VInt{a1, a2}), _u => T.wf.go(tt, at), ee)))
    case T.VFlo{+a1, +a2} <> +tt:
      and.tt(Laws.same.go(T.VFlo{a1, a2} <> [], T.VFlo{a1, a2} <> []), selfs(tt),
        item.self.tt(T.VFlo{a1, a2}, ww => Laws.same.atom(T.VFlo{a1, a2}, ww), atom.self(T.VFlo{a1, a2}, wf.item.ok(at,
          T.wf.atom(T.VFlo{a1, a2}), _u => T.wf.go(tt, at), ee))),
        wf.selfs(tt, at, wf.item.more(at, T.wf.atom(T.VFlo{a1, a2}), _u => T.wf.go(tt, at), ee)))
    case T.VBool{+a1} <> +tt:
      and.tt(Laws.same.go(T.VBool{a1} <> [], T.VBool{a1} <> []), selfs(tt),
        item.self.tt(T.VBool{a1}, ww => Laws.same.atom(T.VBool{a1}, ww), atom.self(T.VBool{a1}, wf.item.ok(at,
          T.wf.atom(T.VBool{a1}), _u => T.wf.go(tt, at), ee))),
        wf.selfs(tt, at, wf.item.more(at, T.wf.atom(T.VBool{a1}), _u => T.wf.go(tt, at), ee)))
    case T.VWhen{+a1} <> +tt:
      and.tt(Laws.same.go(T.VWhen{a1} <> [], T.VWhen{a1} <> []), selfs(tt),
        item.self.tt(T.VWhen{a1}, ww => Laws.same.atom(T.VWhen{a1}, ww), atom.self(T.VWhen{a1}, wf.item.ok(at,
          T.wf.atom(T.VWhen{a1}), _u => T.wf.go(tt, at), ee))),
        wf.selfs(tt, at, wf.item.more(at, T.wf.atom(T.VWhen{a1}), _u => T.wf.go(tt, at), ee)))
    case T.VArr{+ls} <> +tt:
      and.tt(Laws.same.go(T.VArr{ls} <> [], T.VArr{ls} <> []), selfs(tt),
        item.self.tt(T.VArr{ls}, ww => Laws.same.box(Laws.KArr{}, ww, ws => Laws.same.go(ls, ws)), refl.rows(ls,
          wf.selfs(ls, T.WfItems{}, wt.ok(T.wf.go(ls, T.WfItems{}), _v => T.wf.go(tt, at), wf.item.more(at, True{},
          _u => T.wf.then(T.wf.go(ls, T.WfItems{}), _v => T.wf.go(tt, at)), ee))))),
        wf.selfs(tt, at, wt.more(T.wf.go(ls, T.WfItems{}), _v => T.wf.go(tt, at), wf.item.more(at, True{},
          _u => T.wf.then(T.wf.go(ls, T.WfItems{}), _v => T.wf.go(tt, at)), ee))))
    case T.VInl{+ls} <> +tt:
      and.tt(Laws.same.go(T.VInl{ls} <> [], T.VInl{ls} <> []), selfs(tt),
        item.self.tt(T.VInl{ls}, ww => Laws.same.box(Laws.KInl{}, ww, ws => Laws.same.go(ls, ws)), refl.rows(ls,
          wf.selfs(ls, T.WfInl{}, wt.ok(T.wf.go(ls, T.WfInl{}), _v => T.wf.go(tt, at), wf.item.more(at, True{},
          _u => T.wf.then(T.wf.go(ls, T.WfInl{}), _v => T.wf.go(tt, at)), ee))))),
        wf.selfs(tt, at, wt.more(T.wf.go(ls, T.WfInl{}), _v => T.wf.go(tt, at), wf.item.more(at, True{},
          _u => T.wf.then(T.wf.go(ls, T.WfInl{}), _v => T.wf.go(tt, at)), ee))))
    case T.VHead{+pa, +ls} <> +tt:
      Eq.bit.absurd(&2, {selfs(T.VHead{pa, ls} <> tt) == True{} : Bool}, wf.item.ok(at, T.wf.atom(T.VHead{pa, ls}),
        _u => T.wf.go(tt, at), ee))
    case T.VAot{+pa, +ls} <> +tt:
      and.tt(Laws.same.go(T.VAot{pa, ls} <> [], T.VAot{pa, ls} <> []), selfs(tt),
        item.self.tt(T.VAot{pa, ls}, ww => Laws.same.box(Laws.KAot{}, ww, ws => Laws.same.go(ls, ws)), refl.rows(ls,
          wf.selfs(ls, T.WfRows{pa}, wt.ok(T.wf.go(ls, T.WfRows{pa}), _v => T.wf.go(tt, at), wf.aot.more(at, pa,
          _u => T.wf.then(T.wf.go(ls, T.WfRows{pa}), _v => T.wf.go(tt, at)), ee))))),
        wf.selfs(tt, at, wt.more(T.wf.go(ls, T.WfRows{pa}), _v => T.wf.go(tt, at), wf.aot.more(at, pa,
          _u => T.wf.then(T.wf.go(ls, T.WfRows{pa}), _v => T.wf.go(tt, at)), ee))))
    case T.VAots{+pa, +ls} <> +tt:
      Eq.bit.absurd(&2, {selfs(T.VAots{pa, ls} <> tt) == True{} : Bool}, wf.item.ok(at, T.wf.atom(T.VAots{pa, ls}),
        _u => T.wf.go(tt, at), ee))

# `own` changes no answer of `same`. own.rows reads a span out as an owned
# string of the same characters, and same compares strings by characters.

# one value with its spans read out, as own.rows writes a value it holds
def own.val(vv: T.Val) -> T.Val:
  match vv:
    case T.VSpan{src, +kk}:
      T.VStr{T.span.str(src, kk, U32.is_zero(kk))}
    case T.VArr{ls}:
      T.VArr{Laws.own.rows(ls)}
    case T.VInl{ls}:
      T.VInl{Laws.own.rows(ls)}
    case T.VHead{pa, ls}:
      T.VHead{pa, Laws.own.rows(ls)}
    case T.VAot{pa, ls}:
      T.VAot{pa, Laws.own.rows(ls)}
    case T.VAots{pa, ls}:
      T.VAots{pa, Laws.own.rows(ls)}
    case other:
      other

# one row with its spans read out: a pair's value, or the value itself
def own.elem(hh: T.Val) -> T.Val:
  match hh:
    case T.VPair{nn, vv}:
      T.VPair{nn, own.val(vv)}
    case other:
      own.val(other)

# a pick with its spans read out
def pick.own(pp: Laws.Pick) -> Laws.Pick:
  match pp:
    case Laws.Picked{vv, rest}:
      Laws.Picked{own.val(vv), Laws.own.rows(rest)}
    case Laws.NoPick{}:
      Laws.NoPick{}

# a box with its spans read out
def box.own(bx: Laws.Box) -> Laws.Box:
  match bx:
    case Laws.Boxed{kk, ls}:
      Laws.Boxed{kk, Laws.own.rows(ls)}
    case Laws.Unboxed{}:
      Laws.Unboxed{}

# own.rows reads out one row at a time
def own.cons(
  hh: T.Val,
  tt: List<&2, T.Val>
) -> {Laws.own.rows(hh <> tt) == own.elem(hh) <> Laws.own.rows(tt) : List<&2, T.Val>}:
  match hh:
    case T.VPair{nn, vv}:
      match vv:
        case T.VStr{a1}:
          {==}
        case T.VSpan{a1, a2}:
          {==}
        case T.VInt{a1, a2}:
          {==}
        case T.VFlo{a1, a2}:
          {==}
        case T.VBool{a1}:
          {==}
        case T.VWhen{a1}:
          {==}
        case T.VArr{ls}:
          {==}
        case T.VInl{ls}:
          {==}
        case T.VHead{pa, ls}:
          {==}
        case T.VAot{pa, ls}:
          {==}
        case T.VAots{pa, ls}:
          {==}
        case T.VPair{a1, a2}:
          {==}
    case T.VStr{a1}:
      {==}
    case T.VSpan{a1, a2}:
      {==}
    case T.VInt{a1, a2}:
      {==}
    case T.VFlo{a1, a2}:
      {==}
    case T.VBool{a1}:
      {==}
    case T.VWhen{a1}:
      {==}
    case T.VArr{ls}:
      {==}
    case T.VInl{ls}:
      {==}
    case T.VHead{pa, ls}:
      {==}
    case T.VAot{pa, ls}:
      {==}
    case T.VAots{pa, ls}:
      {==}

# the list a value holds, read out
def kids.own(ww: T.Val) -> {Laws.kids(own.val(ww)) == box.own(Laws.kids(ww)) : Laws.Box}:
  match ww:
    case T.VStr{a1}:
      {==}
    case T.VSpan{a1, a2}:
      {==}
    case T.VInt{a1, a2}:
      {==}
    case T.VFlo{a1, a2}:
      {==}
    case T.VBool{a1}:
      {==}
    case T.VWhen{a1}:
      {==}
    case T.VArr{ls}:
      {==}
    case T.VInl{ls}:
      {==}
    case T.VHead{pa, ls}:
      {==}
    case T.VAot{pa, ls}:
      {==}
    case T.VAots{pa, ls}:
      {==}
    case T.VPair{a1, a2}:
      {==}

# the list a row holds, read out
def kids.own.e(ww: T.Val) -> {Laws.kids(own.elem(ww)) == box.own(Laws.kids(ww)) : Laws.Box}:
  match ww:
    case T.VStr{a1}:
      {==}
    case T.VSpan{a1, a2}:
      {==}
    case T.VInt{a1, a2}:
      {==}
    case T.VFlo{a1, a2}:
      {==}
    case T.VBool{a1}:
      {==}
    case T.VWhen{a1}:
      {==}
    case T.VArr{ls}:
      {==}
    case T.VInl{ls}:
      {==}
    case T.VHead{pa, ls}:
      {==}
    case T.VAot{pa, ls}:
      {==}
    case T.VAots{pa, ls}:
      {==}
    case T.VPair{a1, a2}:
      {==}

# reading out keeps a scalar's fields
def scal.own(ww: T.Val) -> {Laws.scal(own.val(ww)) == Laws.scal(ww) : Laws.Sc}:
  match ww:
    case T.VStr{a1}:
      {==}
    case T.VSpan{a1, a2}:
      {==}
    case T.VInt{a1, a2}:
      {==}
    case T.VFlo{a1, a2}:
      {==}
    case T.VBool{a1}:
      {==}
    case T.VWhen{a1}:
      {==}
    case T.VArr{ls}:
      {==}
    case T.VInl{ls}:
      {==}
    case T.VHead{pa, ls}:
      {==}
    case T.VAot{pa, ls}:
      {==}
    case T.VAots{pa, ls}:
      {==}
    case T.VPair{a1, a2}:
      {==}

# and a row's
def scal.own.e(ww: T.Val) -> {Laws.scal(own.elem(ww)) == Laws.scal(ww) : Laws.Sc}:
  match ww:
    case T.VStr{a1}:
      {==}
    case T.VSpan{a1, a2}:
      {==}
    case T.VInt{a1, a2}:
      {==}
    case T.VFlo{a1, a2}:
      {==}
    case T.VBool{a1}:
      {==}
    case T.VWhen{a1}:
      {==}
    case T.VArr{ls}:
      {==}
    case T.VInl{ls}:
      {==}
    case T.VHead{pa, ls}:
      {==}
    case T.VAot{pa, ls}:
      {==}
    case T.VAots{pa, ls}:
      {==}
    case T.VPair{a1, a2}:
      {==}

# a then whose rests agree
def at.cong2(
  bb: Bool,
  -m1: Unit -> Bool,
  -m2: Unit -> Bool,
  em: {m1(Unit{}) == m2(Unit{}) : Bool}
) -> {Laws.and_then(bb, m1) == Laws.and_then(bb, m2) : Bool}:
  match bb:
    case True{}:
      em
    case False{}:
      {==}

# a then whose parts and rests agree
def at.cong(
  -b1: Bool,
  b2: Bool,
  eb: {b1 == b2 : Bool},
  -m1: Unit -> Bool,
  -m2: Unit -> Bool,
  em: {m1(Unit{}) == m2(Unit{}) : Bool}
) -> {Laws.and_then(b1, m1) == Laws.and_then(b2, m2) : Bool}:
  Equal.trans(Bool, Laws.and_then(b1, m1), Laws.and_then(b2, m1), Laws.and_then(b2, m2),
    Equal.cong(Bool, Bool, xx => Laws.and_then(xx, m1), b1, b2, eb), at.cong2(b2, m1, m2, em))

# a box compared by comparisons that agree on every list
def boxed.cong(
  kk: Laws.Kin,
  bx: Laws.Box,
  -f1: List<&2, T.Val> -> Bool,
  -f2: List<&2, T.Val> -> Bool,
  hf: @ls: List<&2, T.Val> -> {f1(ls) == f2(ls) : Bool}
) -> {Laws.same.boxed(kk, bx, f1) == Laws.same.boxed(kk, bx, f2) : Bool}:
  match bx:
    case Laws.Boxed{+k2, +ls}:
      at.cong2(Laws.kin.eq(kk, k2), _u => f1(ls), _u => f2(ls), hf(ls))
    case Laws.Unboxed{}:
      {==}

# a value compared by comparisons that agree on every list
def box.cong(
  kk: Laws.Kin,
  ww: T.Val,
  -f1: List<&2, T.Val> -> Bool,
  -f2: List<&2, T.Val> -> Bool,
  hf: @ls: List<&2, T.Val> -> {f1(ls) == f2(ls) : Bool}
) -> {Laws.same.box(kk, ww, f1) == Laws.same.box(kk, ww, f2) : Bool}:
  boxed.cong(kk, Laws.kids(ww), f1, f2, hf)

# a pick compared by comparisons and rests that agree
def pair.cong(
  pp: Laws.Pick,
  -c1: T.Val -> Bool,
  c2: T.Val -> Bool,
  -r1: List<&2, T.Val> -> Bool,
  -r2: List<&2, T.Val> -> Bool,
  hc: @vv: T.Val -> {c1(vv) == c2(vv) : Bool},
  hr: @ls: List<&2, T.Val> -> {r1(ls) == r2(ls) : Bool}
) -> {Laws.same.pair(pp, c1, r1) == Laws.same.pair(pp, c2, r2) : Bool}:
  match pp:
    case Laws.Picked{+ww, +left}:
      at.cong(c1(ww), c2(ww), hc(ww), _u => r1(left), _u => r2(left), hr(left))
    case Laws.NoPick{}:
      {==}

# the other rows' first value compared by comparisons and rests that agree
def item.cong(
  oo: List<&2, T.Val>,
  -c1: T.Val -> Bool,
  c2: T.Val -> Bool,
  -r1: List<&2, T.Val> -> Bool,
  -r2: List<&2, T.Val> -> Bool,
  hc: @vv: T.Val -> {c1(vv) == c2(vv) : Bool},
  hr: @ls: List<&2, T.Val> -> {r1(ls) == r2(ls) : Bool}
) -> {Laws.same.item(oo, c1, r1) == Laws.same.item(oo, c2, r2) : Bool}:
  match oo:
    case []:
      {==}
    case +ww <> +left:
      at.cong(c1(ww), c2(ww), hc(ww), _u => r1(left), _u => r2(left), hr(left))

# rows read out compare as the rows do, against any other rows
def own.l(
  xs: List<&2, T.Val>,
  +oo: List<&2, T.Val>
) -> {Laws.same.go(Laws.own.rows(xs), oo) == Laws.same.go(xs, oo) : Bool}:
  match xs:
    case []:
      {==}
    case T.VPair{+nn, T.VStr{+a1}} <> +tt:
      pair.cong(Laws.pick(oo, nn), ww => Laws.same.atom(T.VStr{a1}, ww),
        ww => Laws.same.atom(T.VStr{a1}, ww),
        rr => Laws.same.go(Laws.own.rows(tt), rr), rr => Laws.same.go(tt, rr),
        _ww => {==},
        rr => own.l(tt, rr))
    case T.VPair{+nn, T.VSpan{+a1, +a2}} <> +tt:
      pair.cong(Laws.pick(oo, nn), ww => Laws.same.atom(T.VStr{T.span.str(a1, a2, U32.is_zero(a2))}, ww),
        ww => Laws.same.atom(T.VSpan{a1, a2}, ww),
        rr => Laws.same.go(Laws.own.rows(tt), rr), rr => Laws.same.go(tt, rr),
        _ww => {==},
        rr => own.l(tt, rr))
    case T.VPair{+nn, T.VInt{+a1, +a2}} <> +tt:
      pair.cong(Laws.pick(oo, nn), ww => Laws.same.atom(T.VInt{a1, a2}, ww),
        ww => Laws.same.atom(T.VInt{a1, a2}, ww),
        rr => Laws.same.go(Laws.own.rows(tt), rr), rr => Laws.same.go(tt, rr),
        _ww => {==},
        rr => own.l(tt, rr))
    case T.VPair{+nn, T.VFlo{+a1, +a2}} <> +tt:
      pair.cong(Laws.pick(oo, nn), ww => Laws.same.atom(T.VFlo{a1, a2}, ww),
        ww => Laws.same.atom(T.VFlo{a1, a2}, ww),
        rr => Laws.same.go(Laws.own.rows(tt), rr), rr => Laws.same.go(tt, rr),
        _ww => {==},
        rr => own.l(tt, rr))
    case T.VPair{+nn, T.VBool{+a1}} <> +tt:
      pair.cong(Laws.pick(oo, nn), ww => Laws.same.atom(T.VBool{a1}, ww),
        ww => Laws.same.atom(T.VBool{a1}, ww),
        rr => Laws.same.go(Laws.own.rows(tt), rr), rr => Laws.same.go(tt, rr),
        _ww => {==},
        rr => own.l(tt, rr))
    case T.VPair{+nn, T.VWhen{+a1}} <> +tt:
      pair.cong(Laws.pick(oo, nn), ww => Laws.same.atom(T.VWhen{a1}, ww),
        ww => Laws.same.atom(T.VWhen{a1}, ww),
        rr => Laws.same.go(Laws.own.rows(tt), rr), rr => Laws.same.go(tt, rr),
        _ww => {==},
        rr => own.l(tt, rr))
    case T.VPair{+nn, T.VArr{+ls}} <> +tt:
      pair.cong(Laws.pick(oo, nn), ww => Laws.same.box(Laws.KArr{}, ww, ws => Laws.same.go(Laws.own.rows(ls), ws)),
        ww => Laws.same.box(Laws.KArr{}, ww, ws => Laws.same.go(ls, ws)),
        rr => Laws.same.go(Laws.own.rows(tt), rr), rr => Laws.same.go(tt, rr),
        ww => box.cong(Laws.KArr{}, ww, ws => Laws.same.go(Laws.own.rows(ls), ws), ws => Laws.same.go(ls, ws),
          ws => own.l(ls, ws)),
        rr => own.l(tt, rr))
    case T.VPair{+nn, T.VInl{+ls}} <> +tt:
      pair.cong(Laws.pick(oo, nn), ww => Laws.same.box(Laws.KInl{}, ww, ws => Laws.same.go(Laws.own.rows(ls), ws)),
        ww => Laws.same.box(Laws.KInl{}, ww, ws => Laws.same.go(ls, ws)),
        rr => Laws.same.go(Laws.own.rows(tt), rr), rr => Laws.same.go(tt, rr),
        ww => box.cong(Laws.KInl{}, ww, ws => Laws.same.go(Laws.own.rows(ls), ws), ws => Laws.same.go(ls, ws),
          ws => own.l(ls, ws)),
        rr => own.l(tt, rr))
    case T.VPair{+nn, T.VHead{+pa, +ls}} <> +tt:
      pair.cong(Laws.pick(oo, nn), ww => Laws.same.box(Laws.KHead{}, ww, ws => Laws.same.go(Laws.own.rows(ls), ws)),
        ww => Laws.same.box(Laws.KHead{}, ww, ws => Laws.same.go(ls, ws)),
        rr => Laws.same.go(Laws.own.rows(tt), rr), rr => Laws.same.go(tt, rr),
        ww => box.cong(Laws.KHead{}, ww, ws => Laws.same.go(Laws.own.rows(ls), ws), ws => Laws.same.go(ls, ws),
          ws => own.l(ls, ws)),
        rr => own.l(tt, rr))
    case T.VPair{+nn, T.VAot{+pa, +ls}} <> +tt:
      pair.cong(Laws.pick(oo, nn), ww => Laws.same.box(Laws.KAot{}, ww, ws => Laws.same.go(Laws.own.rows(ls), ws)),
        ww => Laws.same.box(Laws.KAot{}, ww, ws => Laws.same.go(ls, ws)),
        rr => Laws.same.go(Laws.own.rows(tt), rr), rr => Laws.same.go(tt, rr),
        ww => box.cong(Laws.KAot{}, ww, ws => Laws.same.go(Laws.own.rows(ls), ws), ws => Laws.same.go(ls, ws),
          ws => own.l(ls, ws)),
        rr => own.l(tt, rr))
    case T.VPair{+nn, T.VAots{+pa, +ls}} <> +tt:
      pair.cong(Laws.pick(oo, nn), ww => Laws.same.box(Laws.KAots{}, ww, ws => Laws.same.go(Laws.own.rows(ls), ws)),
        ww => Laws.same.box(Laws.KAots{}, ww, ws => Laws.same.go(ls, ws)),
        rr => Laws.same.go(Laws.own.rows(tt), rr), rr => Laws.same.go(tt, rr),
        ww => box.cong(Laws.KAots{}, ww, ws => Laws.same.go(Laws.own.rows(ls), ws), ws => Laws.same.go(ls, ws),
          ws => own.l(ls, ws)),
        rr => own.l(tt, rr))
    case T.VPair{+nn, T.VPair{+a1, +a2}} <> +tt:
      pair.cong(Laws.pick(oo, nn), ww => Laws.same.atom(T.VPair{a1, a2}, ww),
        ww => Laws.same.atom(T.VPair{a1, a2}, ww),
        rr => Laws.same.go(Laws.own.rows(tt), rr), rr => Laws.same.go(tt, rr),
        _ww => {==},
        rr => own.l(tt, rr))
    case T.VStr{+a1} <> +tt:
      item.cong(oo, ww => Laws.same.atom(T.VStr{a1}, ww),
        ww => Laws.same.atom(T.VStr{a1}, ww),
        rr => Laws.same.go(Laws.own.rows(tt), rr), rr => Laws.same.go(tt, rr),
        _ww => {==},
        rr => own.l(tt, rr))
    case T.VSpan{+a1, +a2} <> +tt:
      item.cong(oo, ww => Laws.same.atom(T.VStr{T.span.str(a1, a2, U32.is_zero(a2))}, ww),
        ww => Laws.same.atom(T.VSpan{a1, a2}, ww),
        rr => Laws.same.go(Laws.own.rows(tt), rr), rr => Laws.same.go(tt, rr),
        _ww => {==},
        rr => own.l(tt, rr))
    case T.VInt{+a1, +a2} <> +tt:
      item.cong(oo, ww => Laws.same.atom(T.VInt{a1, a2}, ww),
        ww => Laws.same.atom(T.VInt{a1, a2}, ww),
        rr => Laws.same.go(Laws.own.rows(tt), rr), rr => Laws.same.go(tt, rr),
        _ww => {==},
        rr => own.l(tt, rr))
    case T.VFlo{+a1, +a2} <> +tt:
      item.cong(oo, ww => Laws.same.atom(T.VFlo{a1, a2}, ww),
        ww => Laws.same.atom(T.VFlo{a1, a2}, ww),
        rr => Laws.same.go(Laws.own.rows(tt), rr), rr => Laws.same.go(tt, rr),
        _ww => {==},
        rr => own.l(tt, rr))
    case T.VBool{+a1} <> +tt:
      item.cong(oo, ww => Laws.same.atom(T.VBool{a1}, ww),
        ww => Laws.same.atom(T.VBool{a1}, ww),
        rr => Laws.same.go(Laws.own.rows(tt), rr), rr => Laws.same.go(tt, rr),
        _ww => {==},
        rr => own.l(tt, rr))
    case T.VWhen{+a1} <> +tt:
      item.cong(oo, ww => Laws.same.atom(T.VWhen{a1}, ww),
        ww => Laws.same.atom(T.VWhen{a1}, ww),
        rr => Laws.same.go(Laws.own.rows(tt), rr), rr => Laws.same.go(tt, rr),
        _ww => {==},
        rr => own.l(tt, rr))
    case T.VArr{+ls} <> +tt:
      item.cong(oo, ww => Laws.same.box(Laws.KArr{}, ww, ws => Laws.same.go(Laws.own.rows(ls), ws)),
        ww => Laws.same.box(Laws.KArr{}, ww, ws => Laws.same.go(ls, ws)),
        rr => Laws.same.go(Laws.own.rows(tt), rr), rr => Laws.same.go(tt, rr),
        ww => box.cong(Laws.KArr{}, ww, ws => Laws.same.go(Laws.own.rows(ls), ws), ws => Laws.same.go(ls, ws),
          ws => own.l(ls, ws)),
        rr => own.l(tt, rr))
    case T.VInl{+ls} <> +tt:
      item.cong(oo, ww => Laws.same.box(Laws.KInl{}, ww, ws => Laws.same.go(Laws.own.rows(ls), ws)),
        ww => Laws.same.box(Laws.KInl{}, ww, ws => Laws.same.go(ls, ws)),
        rr => Laws.same.go(Laws.own.rows(tt), rr), rr => Laws.same.go(tt, rr),
        ww => box.cong(Laws.KInl{}, ww, ws => Laws.same.go(Laws.own.rows(ls), ws), ws => Laws.same.go(ls, ws),
          ws => own.l(ls, ws)),
        rr => own.l(tt, rr))
    case T.VHead{+pa, +ls} <> +tt:
      item.cong(oo, ww => Laws.same.box(Laws.KHead{}, ww, ws => Laws.same.go(Laws.own.rows(ls), ws)),
        ww => Laws.same.box(Laws.KHead{}, ww, ws => Laws.same.go(ls, ws)),
        rr => Laws.same.go(Laws.own.rows(tt), rr), rr => Laws.same.go(tt, rr),
        ww => box.cong(Laws.KHead{}, ww, ws => Laws.same.go(Laws.own.rows(ls), ws), ws => Laws.same.go(ls, ws),
          ws => own.l(ls, ws)),
        rr => own.l(tt, rr))
    case T.VAot{+pa, +ls} <> +tt:
      item.cong(oo, ww => Laws.same.box(Laws.KAot{}, ww, ws => Laws.same.go(Laws.own.rows(ls), ws)),
        ww => Laws.same.box(Laws.KAot{}, ww, ws => Laws.same.go(ls, ws)),
        rr => Laws.same.go(Laws.own.rows(tt), rr), rr => Laws.same.go(tt, rr),
        ww => box.cong(Laws.KAot{}, ww, ws => Laws.same.go(Laws.own.rows(ls), ws), ws => Laws.same.go(ls, ws),
          ws => own.l(ls, ws)),
        rr => own.l(tt, rr))
    case T.VAots{+pa, +ls} <> +tt:
      item.cong(oo, ww => Laws.same.box(Laws.KAots{}, ww, ws => Laws.same.go(Laws.own.rows(ls), ws)),
        ww => Laws.same.box(Laws.KAots{}, ww, ws => Laws.same.go(ls, ws)),
        rr => Laws.same.go(Laws.own.rows(tt), rr), rr => Laws.same.go(tt, rr),
        ww => box.cong(Laws.KAots{}, ww, ws => Laws.same.go(Laws.own.rows(ls), ws), ws => Laws.same.go(ls, ws),
          ws => own.l(ls, ws)),
        rr => own.l(tt, rr))

# a pick read out, cons'd onto a row read out
def cons.own(
  +hh: T.Val,
  pp: Laws.Pick
) -> {Laws.pick.cons(own.elem(hh), pick.own(pp)) == pick.own(Laws.pick.cons(hh, pp)) : Laws.Pick}:
  match pp:
    case Laws.Picked{+vv, +rest}:
      Equal.cong(List<&2, T.Val>, Laws.Pick, ls => Laws.Picked{own.val(vv), ls},
        own.elem(hh) <> Laws.own.rows(rest), Laws.own.rows(hh <> rest),
        Equal.sym(List<&2, T.Val>, Laws.own.rows(hh <> rest), own.elem(hh) <> Laws.own.rows(rest),
          own.cons(hh, rest)))
    case Laws.NoPick{}:
      {==}

# a pair of the name is picked the same way from rows read out
def po.step(
  bb: Bool,
  +mm: String,
  +vv: T.Val,
  +uu: List<&2, T.Val>,
  +nn: String,
  ih: {Laws.pick(Laws.own.rows(uu), nn) == pick.own(Laws.pick(uu, nn)) : Laws.Pick}
) -> {Laws.pick.step(bb, mm, own.val(vv), Laws.own.rows(uu), _u => Laws.pick(Laws.own.rows(uu), nn))
  == pick.own(Laws.pick.step(bb, mm, vv, uu, _u => Laws.pick(uu, nn))) : Laws.Pick}:
  match bb:
    case True{}:
      {==}
    case False{}:
      Equal.trans(Laws.Pick,
        Laws.pick.cons(T.VPair{mm, own.val(vv)}, Laws.pick(Laws.own.rows(uu), nn)),
        Laws.pick.cons(T.VPair{mm, own.val(vv)}, pick.own(Laws.pick(uu, nn))),
        pick.own(Laws.pick.cons(T.VPair{mm, vv}, Laws.pick(uu, nn))),
        Equal.cong(Laws.Pick, Laws.Pick, pp => Laws.pick.cons(T.VPair{mm, own.val(vv)}, pp),
          Laws.pick(Laws.own.rows(uu), nn), pick.own(Laws.pick(uu, nn)), ih),
        cons.own(T.VPair{mm, vv}, Laws.pick(uu, nn)))

# one row of a pick from rows read out
def po.cell(
  kk: T.Val,
  +uu: List<&2, T.Val>,
  +nn: String,
  +ih: {Laws.pick(Laws.own.rows(uu), nn) == pick.own(Laws.pick(uu, nn)) : Laws.Pick}
) -> {Laws.pick(own.elem(kk) <> Laws.own.rows(uu), nn) == pick.own(Laws.pick(kk <> uu, nn)) : Laws.Pick}:
  match kk:
    case T.VPair{+mm, +vv}:
      po.step(String.eq(mm, nn), mm, vv, uu, nn, ih)
    case T.VStr{+a1}:
      Equal.trans(Laws.Pick,
        Laws.pick.cons(own.elem(T.VStr{a1}), Laws.pick(Laws.own.rows(uu), nn)),
        Laws.pick.cons(own.elem(T.VStr{a1}), pick.own(Laws.pick(uu, nn))),
        pick.own(Laws.pick.cons(T.VStr{a1}, Laws.pick(uu, nn))),
        Equal.cong(Laws.Pick, Laws.Pick, pp => Laws.pick.cons(own.elem(T.VStr{a1}), pp),
          Laws.pick(Laws.own.rows(uu), nn), pick.own(Laws.pick(uu, nn)), ih),
        cons.own(T.VStr{a1}, Laws.pick(uu, nn)))
    case T.VSpan{+a1, +a2}:
      Equal.trans(Laws.Pick,
        Laws.pick.cons(own.elem(T.VSpan{a1, a2}), Laws.pick(Laws.own.rows(uu), nn)),
        Laws.pick.cons(own.elem(T.VSpan{a1, a2}), pick.own(Laws.pick(uu, nn))),
        pick.own(Laws.pick.cons(T.VSpan{a1, a2}, Laws.pick(uu, nn))),
        Equal.cong(Laws.Pick, Laws.Pick, pp => Laws.pick.cons(own.elem(T.VSpan{a1, a2}), pp),
          Laws.pick(Laws.own.rows(uu), nn), pick.own(Laws.pick(uu, nn)), ih),
        cons.own(T.VSpan{a1, a2}, Laws.pick(uu, nn)))
    case T.VInt{+a1, +a2}:
      Equal.trans(Laws.Pick,
        Laws.pick.cons(own.elem(T.VInt{a1, a2}), Laws.pick(Laws.own.rows(uu), nn)),
        Laws.pick.cons(own.elem(T.VInt{a1, a2}), pick.own(Laws.pick(uu, nn))),
        pick.own(Laws.pick.cons(T.VInt{a1, a2}, Laws.pick(uu, nn))),
        Equal.cong(Laws.Pick, Laws.Pick, pp => Laws.pick.cons(own.elem(T.VInt{a1, a2}), pp),
          Laws.pick(Laws.own.rows(uu), nn), pick.own(Laws.pick(uu, nn)), ih),
        cons.own(T.VInt{a1, a2}, Laws.pick(uu, nn)))
    case T.VFlo{+a1, +a2}:
      Equal.trans(Laws.Pick,
        Laws.pick.cons(own.elem(T.VFlo{a1, a2}), Laws.pick(Laws.own.rows(uu), nn)),
        Laws.pick.cons(own.elem(T.VFlo{a1, a2}), pick.own(Laws.pick(uu, nn))),
        pick.own(Laws.pick.cons(T.VFlo{a1, a2}, Laws.pick(uu, nn))),
        Equal.cong(Laws.Pick, Laws.Pick, pp => Laws.pick.cons(own.elem(T.VFlo{a1, a2}), pp),
          Laws.pick(Laws.own.rows(uu), nn), pick.own(Laws.pick(uu, nn)), ih),
        cons.own(T.VFlo{a1, a2}, Laws.pick(uu, nn)))
    case T.VBool{+a1}:
      Equal.trans(Laws.Pick,
        Laws.pick.cons(own.elem(T.VBool{a1}), Laws.pick(Laws.own.rows(uu), nn)),
        Laws.pick.cons(own.elem(T.VBool{a1}), pick.own(Laws.pick(uu, nn))),
        pick.own(Laws.pick.cons(T.VBool{a1}, Laws.pick(uu, nn))),
        Equal.cong(Laws.Pick, Laws.Pick, pp => Laws.pick.cons(own.elem(T.VBool{a1}), pp),
          Laws.pick(Laws.own.rows(uu), nn), pick.own(Laws.pick(uu, nn)), ih),
        cons.own(T.VBool{a1}, Laws.pick(uu, nn)))
    case T.VWhen{+a1}:
      Equal.trans(Laws.Pick,
        Laws.pick.cons(own.elem(T.VWhen{a1}), Laws.pick(Laws.own.rows(uu), nn)),
        Laws.pick.cons(own.elem(T.VWhen{a1}), pick.own(Laws.pick(uu, nn))),
        pick.own(Laws.pick.cons(T.VWhen{a1}, Laws.pick(uu, nn))),
        Equal.cong(Laws.Pick, Laws.Pick, pp => Laws.pick.cons(own.elem(T.VWhen{a1}), pp),
          Laws.pick(Laws.own.rows(uu), nn), pick.own(Laws.pick(uu, nn)), ih),
        cons.own(T.VWhen{a1}, Laws.pick(uu, nn)))
    case T.VArr{+ls}:
      Equal.trans(Laws.Pick,
        Laws.pick.cons(own.elem(T.VArr{ls}), Laws.pick(Laws.own.rows(uu), nn)),
        Laws.pick.cons(own.elem(T.VArr{ls}), pick.own(Laws.pick(uu, nn))),
        pick.own(Laws.pick.cons(T.VArr{ls}, Laws.pick(uu, nn))),
        Equal.cong(Laws.Pick, Laws.Pick, pp => Laws.pick.cons(own.elem(T.VArr{ls}), pp),
          Laws.pick(Laws.own.rows(uu), nn), pick.own(Laws.pick(uu, nn)), ih),
        cons.own(T.VArr{ls}, Laws.pick(uu, nn)))
    case T.VInl{+ls}:
      Equal.trans(Laws.Pick,
        Laws.pick.cons(own.elem(T.VInl{ls}), Laws.pick(Laws.own.rows(uu), nn)),
        Laws.pick.cons(own.elem(T.VInl{ls}), pick.own(Laws.pick(uu, nn))),
        pick.own(Laws.pick.cons(T.VInl{ls}, Laws.pick(uu, nn))),
        Equal.cong(Laws.Pick, Laws.Pick, pp => Laws.pick.cons(own.elem(T.VInl{ls}), pp),
          Laws.pick(Laws.own.rows(uu), nn), pick.own(Laws.pick(uu, nn)), ih),
        cons.own(T.VInl{ls}, Laws.pick(uu, nn)))
    case T.VHead{+pa, +ls}:
      Equal.trans(Laws.Pick,
        Laws.pick.cons(own.elem(T.VHead{pa, ls}), Laws.pick(Laws.own.rows(uu), nn)),
        Laws.pick.cons(own.elem(T.VHead{pa, ls}), pick.own(Laws.pick(uu, nn))),
        pick.own(Laws.pick.cons(T.VHead{pa, ls}, Laws.pick(uu, nn))),
        Equal.cong(Laws.Pick, Laws.Pick, pp => Laws.pick.cons(own.elem(T.VHead{pa, ls}), pp),
          Laws.pick(Laws.own.rows(uu), nn), pick.own(Laws.pick(uu, nn)), ih),
        cons.own(T.VHead{pa, ls}, Laws.pick(uu, nn)))
    case T.VAot{+pa, +ls}:
      Equal.trans(Laws.Pick,
        Laws.pick.cons(own.elem(T.VAot{pa, ls}), Laws.pick(Laws.own.rows(uu), nn)),
        Laws.pick.cons(own.elem(T.VAot{pa, ls}), pick.own(Laws.pick(uu, nn))),
        pick.own(Laws.pick.cons(T.VAot{pa, ls}, Laws.pick(uu, nn))),
        Equal.cong(Laws.Pick, Laws.Pick, pp => Laws.pick.cons(own.elem(T.VAot{pa, ls}), pp),
          Laws.pick(Laws.own.rows(uu), nn), pick.own(Laws.pick(uu, nn)), ih),
        cons.own(T.VAot{pa, ls}, Laws.pick(uu, nn)))
    case T.VAots{+pa, +ls}:
      Equal.trans(Laws.Pick,
        Laws.pick.cons(own.elem(T.VAots{pa, ls}), Laws.pick(Laws.own.rows(uu), nn)),
        Laws.pick.cons(own.elem(T.VAots{pa, ls}), pick.own(Laws.pick(uu, nn))),
        pick.own(Laws.pick.cons(T.VAots{pa, ls}, Laws.pick(uu, nn))),
        Equal.cong(Laws.Pick, Laws.Pick, pp => Laws.pick.cons(own.elem(T.VAots{pa, ls}), pp),
          Laws.pick(Laws.own.rows(uu), nn), pick.own(Laws.pick(uu, nn)), ih),
        cons.own(T.VAots{pa, ls}, Laws.pick(uu, nn)))

# a pick from rows read out is the pick read out
def pick.own.rows(
  oo: List<&2, T.Val>,
  +nn: String
) -> {Laws.pick(Laws.own.rows(oo), nn) == pick.own(Laws.pick(oo, nn)) : Laws.Pick}:
  match oo:
    case []:
      {==}
    case +kk <> +uu:
      Equal.trans(Laws.Pick, Laws.pick(Laws.own.rows(kk <> uu), nn),
        Laws.pick(own.elem(kk) <> Laws.own.rows(uu), nn), pick.own(Laws.pick(kk <> uu, nn)),
        Equal.cong(List<&2, T.Val>, Laws.Pick, ls => Laws.pick(ls, nn), Laws.own.rows(kk <> uu),
          own.elem(kk) <> Laws.own.rows(uu), own.cons(kk, uu)),
        po.cell(kk, uu, nn, pick.own.rows(uu, nn)))

# rows read out are empty exactly when the rows are
def empty.own(
  oo: List<&2, T.Val>
) -> {List.is_empty(&2, T.Val, Laws.own.rows(oo)) == List.is_empty(&2, T.Val, oo) : Bool}:
  match oo:
    case []:
      {==}
    case +kk <> +uu:
      Equal.cong(List<&2, T.Val>, Bool, ls => List.is_empty(&2, T.Val, ls), Laws.own.rows(kk <> uu),
        own.elem(kk) <> Laws.own.rows(uu), own.cons(kk, uu))

# a box read out, compared by a comparison that does not see reading out
def boxed.own(
  kk: Laws.Kin,
  bx: Laws.Box,
  -ff: List<&2, T.Val> -> Bool,
  hf: @ls: List<&2, T.Val> -> {ff(Laws.own.rows(ls)) == ff(ls) : Bool}
) -> {Laws.same.boxed(kk, box.own(bx), ff) == Laws.same.boxed(kk, bx, ff) : Bool}:
  match bx:
    case Laws.Boxed{+k2, +ls}:
      at.cong2(Laws.kin.eq(kk, k2), _u => ff(Laws.own.rows(ls)), _u => ff(ls), hf(ls))
    case Laws.Unboxed{}:
      {==}

# a value read out, compared as a box
def box.own.v(
  kk: Laws.Kin,
  +ww: T.Val,
  -ff: List<&2, T.Val> -> Bool,
  hf: @ls: List<&2, T.Val> -> {ff(Laws.own.rows(ls)) == ff(ls) : Bool}
) -> {Laws.same.box(kk, own.val(ww), ff) == Laws.same.box(kk, ww, ff) : Bool}:
  Equal.trans(Bool, Laws.same.boxed(kk, Laws.kids(own.val(ww)), ff), Laws.same.boxed(kk, box.own(Laws.kids(ww)), ff),
    Laws.same.boxed(kk, Laws.kids(ww), ff),
    Equal.cong(Laws.Box, Bool, bx => Laws.same.boxed(kk, bx, ff), Laws.kids(own.val(ww)), box.own(Laws.kids(ww)),
      kids.own(ww)),
    boxed.own(kk, Laws.kids(ww), ff, hf))

# a row read out, compared as a box
def box.own.e(
  kk: Laws.Kin,
  +ww: T.Val,
  -ff: List<&2, T.Val> -> Bool,
  hf: @ls: List<&2, T.Val> -> {ff(Laws.own.rows(ls)) == ff(ls) : Bool}
) -> {Laws.same.box(kk, own.elem(ww), ff) == Laws.same.box(kk, ww, ff) : Bool}:
  Equal.trans(Bool, Laws.same.boxed(kk, Laws.kids(own.elem(ww)), ff), Laws.same.boxed(kk, box.own(Laws.kids(ww)), ff),
    Laws.same.boxed(kk, Laws.kids(ww), ff),
    Equal.cong(Laws.Box, Bool, bx => Laws.same.boxed(kk, bx, ff), Laws.kids(own.elem(ww)), box.own(Laws.kids(ww)),
      kids.own.e(ww)),
    boxed.own(kk, Laws.kids(ww), ff, hf))

# a value read out is the same scalar
def atom.own.v(
  +vv: T.Val,
  +ww: T.Val
) -> {Laws.same.atom(vv, own.val(ww)) == Laws.same.atom(vv, ww) : Bool}:
  Equal.cong(Laws.Sc, Bool, sc => Laws.sc.eq(Laws.scal(vv), sc), Laws.scal(own.val(ww)), Laws.scal(ww), scal.own(ww))

# a row read out is the same scalar
def atom.own.e(
  +vv: T.Val,
  +ww: T.Val
) -> {Laws.same.atom(vv, own.elem(ww)) == Laws.same.atom(vv, ww) : Bool}:
  Equal.cong(Laws.Sc, Bool, sc => Laws.sc.eq(Laws.scal(vv), sc), Laws.scal(own.elem(ww)), Laws.scal(ww), scal.own.e(ww))

# a pick read out compares as the pick
def pair.own(
  pp: Laws.Pick,
  cmp: T.Val -> Bool,
  -rest: List<&2, T.Val> -> Bool,
  hc: @vv: T.Val -> {cmp(own.val(vv)) == cmp(vv) : Bool},
  hr: @ls: List<&2, T.Val> -> {rest(Laws.own.rows(ls)) == rest(ls) : Bool}
) -> {Laws.same.pair(pick.own(pp), cmp, rest) == Laws.same.pair(pp, cmp, rest) : Bool}:
  match pp:
    case Laws.Picked{+ww, +left}:
      at.cong(cmp(own.val(ww)), cmp(ww), hc(ww), _u => rest(Laws.own.rows(left)), _u => rest(left), hr(left))
    case Laws.NoPick{}:
      {==}

# other rows read out give their first value read out
def item.own(
  oo: List<&2, T.Val>,
  cmp: T.Val -> Bool,
  -rest: List<&2, T.Val> -> Bool,
  hc: @vv: T.Val -> {cmp(own.elem(vv)) == cmp(vv) : Bool},
  hr: @ls: List<&2, T.Val> -> {rest(Laws.own.rows(ls)) == rest(ls) : Bool}
) -> {Laws.same.item(Laws.own.rows(oo), cmp, rest) == Laws.same.item(oo, cmp, rest) : Bool}:
  match oo:
    case []:
      {==}
    case +kk <> +uu:
      Equal.trans(Bool, Laws.same.item(Laws.own.rows(kk <> uu), cmp, rest),
        Laws.same.item(own.elem(kk) <> Laws.own.rows(uu), cmp, rest), Laws.same.item(kk <> uu, cmp, rest),
        Equal.cong(List<&2, T.Val>, Bool, ls => Laws.same.item(ls, cmp, rest), Laws.own.rows(kk <> uu),
          own.elem(kk) <> Laws.own.rows(uu), own.cons(kk, uu)),
        at.cong(cmp(own.elem(kk)), cmp(kk), hc(kk), _u => rest(Laws.own.rows(uu)), _u => rest(uu), hr(uu)))

# rows compare against other rows read out as against the rows
def own.r(
  xs: List<&2, T.Val>,
  +oo: List<&2, T.Val>
) -> {Laws.same.go(xs, Laws.own.rows(oo)) == Laws.same.go(xs, oo) : Bool}:
  match xs:
    case []:
      empty.own(oo)
    case T.VPair{+nn, T.VStr{+a1}} <> +tt:
      Equal.trans(Bool, Laws.same.pair(Laws.pick(Laws.own.rows(oo), nn), ww => Laws.same.atom(T.VStr{a1}, ww),
        rr => Laws.same.go(tt, rr)),
        Laws.same.pair(pick.own(Laws.pick(oo, nn)), ww => Laws.same.atom(T.VStr{a1}, ww), rr => Laws.same.go(tt, rr)),
        Laws.same.pair(Laws.pick(oo, nn), ww => Laws.same.atom(T.VStr{a1}, ww), rr => Laws.same.go(tt, rr)),
        Equal.cong(Laws.Pick, Bool, pp => Laws.same.pair(pp, ww => Laws.same.atom(T.VStr{a1}, ww),
          rr => Laws.same.go(tt, rr)),
          Laws.pick(Laws.own.rows(oo), nn), pick.own(Laws.pick(oo, nn)), pick.own.rows(oo, nn)),
        pair.own(Laws.pick(oo, nn), ww => Laws.same.atom(T.VStr{a1}, ww), rr => Laws.same.go(tt, rr),
          ww => atom.own.v(T.VStr{a1}, ww), rr => own.r(tt, rr)))
    case T.VPair{+nn, T.VSpan{+a1, +a2}} <> +tt:
      Equal.trans(Bool, Laws.same.pair(Laws.pick(Laws.own.rows(oo), nn), ww => Laws.same.atom(T.VSpan{a1, a2}, ww),
        rr => Laws.same.go(tt, rr)),
        Laws.same.pair(pick.own(Laws.pick(oo, nn)), ww => Laws.same.atom(T.VSpan{a1, a2}, ww), rr => Laws.same.go(tt,
          rr)),
        Laws.same.pair(Laws.pick(oo, nn), ww => Laws.same.atom(T.VSpan{a1, a2}, ww), rr => Laws.same.go(tt, rr)),
        Equal.cong(Laws.Pick, Bool, pp => Laws.same.pair(pp, ww => Laws.same.atom(T.VSpan{a1, a2}, ww),
          rr => Laws.same.go(tt, rr)),
          Laws.pick(Laws.own.rows(oo), nn), pick.own(Laws.pick(oo, nn)), pick.own.rows(oo, nn)),
        pair.own(Laws.pick(oo, nn), ww => Laws.same.atom(T.VSpan{a1, a2}, ww), rr => Laws.same.go(tt, rr),
          ww => atom.own.v(T.VSpan{a1, a2}, ww), rr => own.r(tt, rr)))
    case T.VPair{+nn, T.VInt{+a1, +a2}} <> +tt:
      Equal.trans(Bool, Laws.same.pair(Laws.pick(Laws.own.rows(oo), nn), ww => Laws.same.atom(T.VInt{a1, a2}, ww),
        rr => Laws.same.go(tt, rr)),
        Laws.same.pair(pick.own(Laws.pick(oo, nn)), ww => Laws.same.atom(T.VInt{a1, a2}, ww), rr => Laws.same.go(tt,
          rr)),
        Laws.same.pair(Laws.pick(oo, nn), ww => Laws.same.atom(T.VInt{a1, a2}, ww), rr => Laws.same.go(tt, rr)),
        Equal.cong(Laws.Pick, Bool, pp => Laws.same.pair(pp, ww => Laws.same.atom(T.VInt{a1, a2}, ww),
          rr => Laws.same.go(tt, rr)),
          Laws.pick(Laws.own.rows(oo), nn), pick.own(Laws.pick(oo, nn)), pick.own.rows(oo, nn)),
        pair.own(Laws.pick(oo, nn), ww => Laws.same.atom(T.VInt{a1, a2}, ww), rr => Laws.same.go(tt, rr),
          ww => atom.own.v(T.VInt{a1, a2}, ww), rr => own.r(tt, rr)))
    case T.VPair{+nn, T.VFlo{+a1, +a2}} <> +tt:
      Equal.trans(Bool, Laws.same.pair(Laws.pick(Laws.own.rows(oo), nn), ww => Laws.same.atom(T.VFlo{a1, a2}, ww),
        rr => Laws.same.go(tt, rr)),
        Laws.same.pair(pick.own(Laws.pick(oo, nn)), ww => Laws.same.atom(T.VFlo{a1, a2}, ww), rr => Laws.same.go(tt,
          rr)),
        Laws.same.pair(Laws.pick(oo, nn), ww => Laws.same.atom(T.VFlo{a1, a2}, ww), rr => Laws.same.go(tt, rr)),
        Equal.cong(Laws.Pick, Bool, pp => Laws.same.pair(pp, ww => Laws.same.atom(T.VFlo{a1, a2}, ww),
          rr => Laws.same.go(tt, rr)),
          Laws.pick(Laws.own.rows(oo), nn), pick.own(Laws.pick(oo, nn)), pick.own.rows(oo, nn)),
        pair.own(Laws.pick(oo, nn), ww => Laws.same.atom(T.VFlo{a1, a2}, ww), rr => Laws.same.go(tt, rr),
          ww => atom.own.v(T.VFlo{a1, a2}, ww), rr => own.r(tt, rr)))
    case T.VPair{+nn, T.VBool{+a1}} <> +tt:
      Equal.trans(Bool, Laws.same.pair(Laws.pick(Laws.own.rows(oo), nn), ww => Laws.same.atom(T.VBool{a1}, ww),
        rr => Laws.same.go(tt, rr)),
        Laws.same.pair(pick.own(Laws.pick(oo, nn)), ww => Laws.same.atom(T.VBool{a1}, ww), rr => Laws.same.go(tt, rr)),
        Laws.same.pair(Laws.pick(oo, nn), ww => Laws.same.atom(T.VBool{a1}, ww), rr => Laws.same.go(tt, rr)),
        Equal.cong(Laws.Pick, Bool, pp => Laws.same.pair(pp, ww => Laws.same.atom(T.VBool{a1}, ww),
          rr => Laws.same.go(tt, rr)),
          Laws.pick(Laws.own.rows(oo), nn), pick.own(Laws.pick(oo, nn)), pick.own.rows(oo, nn)),
        pair.own(Laws.pick(oo, nn), ww => Laws.same.atom(T.VBool{a1}, ww), rr => Laws.same.go(tt, rr),
          ww => atom.own.v(T.VBool{a1}, ww), rr => own.r(tt, rr)))
    case T.VPair{+nn, T.VWhen{+a1}} <> +tt:
      Equal.trans(Bool, Laws.same.pair(Laws.pick(Laws.own.rows(oo), nn), ww => Laws.same.atom(T.VWhen{a1}, ww),
        rr => Laws.same.go(tt, rr)),
        Laws.same.pair(pick.own(Laws.pick(oo, nn)), ww => Laws.same.atom(T.VWhen{a1}, ww), rr => Laws.same.go(tt, rr)),
        Laws.same.pair(Laws.pick(oo, nn), ww => Laws.same.atom(T.VWhen{a1}, ww), rr => Laws.same.go(tt, rr)),
        Equal.cong(Laws.Pick, Bool, pp => Laws.same.pair(pp, ww => Laws.same.atom(T.VWhen{a1}, ww),
          rr => Laws.same.go(tt, rr)),
          Laws.pick(Laws.own.rows(oo), nn), pick.own(Laws.pick(oo, nn)), pick.own.rows(oo, nn)),
        pair.own(Laws.pick(oo, nn), ww => Laws.same.atom(T.VWhen{a1}, ww), rr => Laws.same.go(tt, rr),
          ww => atom.own.v(T.VWhen{a1}, ww), rr => own.r(tt, rr)))
    case T.VPair{+nn, T.VArr{+ls}} <> +tt:
      Equal.trans(Bool, Laws.same.pair(Laws.pick(Laws.own.rows(oo), nn), ww => Laws.same.box(Laws.KArr{}, ww,
        ws => Laws.same.go(ls, ws)), rr => Laws.same.go(tt, rr)),
        Laws.same.pair(pick.own(Laws.pick(oo, nn)), ww => Laws.same.box(Laws.KArr{}, ww, ws => Laws.same.go(ls, ws)),
          rr => Laws.same.go(tt, rr)),
        Laws.same.pair(Laws.pick(oo, nn), ww => Laws.same.box(Laws.KArr{}, ww, ws => Laws.same.go(ls, ws)),
          rr => Laws.same.go(tt, rr)),
        Equal.cong(Laws.Pick, Bool, pp => Laws.same.pair(pp, ww => Laws.same.box(Laws.KArr{}, ww,
          ws => Laws.same.go(ls, ws)), rr => Laws.same.go(tt, rr)),
          Laws.pick(Laws.own.rows(oo), nn), pick.own(Laws.pick(oo, nn)), pick.own.rows(oo, nn)),
        pair.own(Laws.pick(oo, nn), ww => Laws.same.box(Laws.KArr{}, ww, ws => Laws.same.go(ls, ws)),
          rr => Laws.same.go(tt, rr), ww => box.own.v(Laws.KArr{}, ww, ws => Laws.same.go(ls, ws), ws => own.r(ls,
          ws)), rr => own.r(tt, rr)))
    case T.VPair{+nn, T.VInl{+ls}} <> +tt:
      Equal.trans(Bool, Laws.same.pair(Laws.pick(Laws.own.rows(oo), nn), ww => Laws.same.box(Laws.KInl{}, ww,
        ws => Laws.same.go(ls, ws)), rr => Laws.same.go(tt, rr)),
        Laws.same.pair(pick.own(Laws.pick(oo, nn)), ww => Laws.same.box(Laws.KInl{}, ww, ws => Laws.same.go(ls, ws)),
          rr => Laws.same.go(tt, rr)),
        Laws.same.pair(Laws.pick(oo, nn), ww => Laws.same.box(Laws.KInl{}, ww, ws => Laws.same.go(ls, ws)),
          rr => Laws.same.go(tt, rr)),
        Equal.cong(Laws.Pick, Bool, pp => Laws.same.pair(pp, ww => Laws.same.box(Laws.KInl{}, ww,
          ws => Laws.same.go(ls, ws)), rr => Laws.same.go(tt, rr)),
          Laws.pick(Laws.own.rows(oo), nn), pick.own(Laws.pick(oo, nn)), pick.own.rows(oo, nn)),
        pair.own(Laws.pick(oo, nn), ww => Laws.same.box(Laws.KInl{}, ww, ws => Laws.same.go(ls, ws)),
          rr => Laws.same.go(tt, rr), ww => box.own.v(Laws.KInl{}, ww, ws => Laws.same.go(ls, ws), ws => own.r(ls,
          ws)), rr => own.r(tt, rr)))
    case T.VPair{+nn, T.VHead{+pa, +ls}} <> +tt:
      Equal.trans(Bool, Laws.same.pair(Laws.pick(Laws.own.rows(oo), nn), ww => Laws.same.box(Laws.KHead{}, ww,
        ws => Laws.same.go(ls, ws)), rr => Laws.same.go(tt, rr)),
        Laws.same.pair(pick.own(Laws.pick(oo, nn)), ww => Laws.same.box(Laws.KHead{}, ww, ws => Laws.same.go(ls, ws)),
          rr => Laws.same.go(tt, rr)),
        Laws.same.pair(Laws.pick(oo, nn), ww => Laws.same.box(Laws.KHead{}, ww, ws => Laws.same.go(ls, ws)),
          rr => Laws.same.go(tt, rr)),
        Equal.cong(Laws.Pick, Bool, pp => Laws.same.pair(pp, ww => Laws.same.box(Laws.KHead{}, ww,
          ws => Laws.same.go(ls, ws)), rr => Laws.same.go(tt, rr)),
          Laws.pick(Laws.own.rows(oo), nn), pick.own(Laws.pick(oo, nn)), pick.own.rows(oo, nn)),
        pair.own(Laws.pick(oo, nn), ww => Laws.same.box(Laws.KHead{}, ww, ws => Laws.same.go(ls, ws)),
          rr => Laws.same.go(tt, rr), ww => box.own.v(Laws.KHead{}, ww, ws => Laws.same.go(ls, ws), ws => own.r(ls,
          ws)), rr => own.r(tt, rr)))
    case T.VPair{+nn, T.VAot{+pa, +ls}} <> +tt:
      Equal.trans(Bool, Laws.same.pair(Laws.pick(Laws.own.rows(oo), nn), ww => Laws.same.box(Laws.KAot{}, ww,
        ws => Laws.same.go(ls, ws)), rr => Laws.same.go(tt, rr)),
        Laws.same.pair(pick.own(Laws.pick(oo, nn)), ww => Laws.same.box(Laws.KAot{}, ww, ws => Laws.same.go(ls, ws)),
          rr => Laws.same.go(tt, rr)),
        Laws.same.pair(Laws.pick(oo, nn), ww => Laws.same.box(Laws.KAot{}, ww, ws => Laws.same.go(ls, ws)),
          rr => Laws.same.go(tt, rr)),
        Equal.cong(Laws.Pick, Bool, pp => Laws.same.pair(pp, ww => Laws.same.box(Laws.KAot{}, ww,
          ws => Laws.same.go(ls, ws)), rr => Laws.same.go(tt, rr)),
          Laws.pick(Laws.own.rows(oo), nn), pick.own(Laws.pick(oo, nn)), pick.own.rows(oo, nn)),
        pair.own(Laws.pick(oo, nn), ww => Laws.same.box(Laws.KAot{}, ww, ws => Laws.same.go(ls, ws)),
          rr => Laws.same.go(tt, rr), ww => box.own.v(Laws.KAot{}, ww, ws => Laws.same.go(ls, ws), ws => own.r(ls,
          ws)), rr => own.r(tt, rr)))
    case T.VPair{+nn, T.VAots{+pa, +ls}} <> +tt:
      Equal.trans(Bool, Laws.same.pair(Laws.pick(Laws.own.rows(oo), nn), ww => Laws.same.box(Laws.KAots{}, ww,
        ws => Laws.same.go(ls, ws)), rr => Laws.same.go(tt, rr)),
        Laws.same.pair(pick.own(Laws.pick(oo, nn)), ww => Laws.same.box(Laws.KAots{}, ww, ws => Laws.same.go(ls, ws)),
          rr => Laws.same.go(tt, rr)),
        Laws.same.pair(Laws.pick(oo, nn), ww => Laws.same.box(Laws.KAots{}, ww, ws => Laws.same.go(ls, ws)),
          rr => Laws.same.go(tt, rr)),
        Equal.cong(Laws.Pick, Bool, pp => Laws.same.pair(pp, ww => Laws.same.box(Laws.KAots{}, ww,
          ws => Laws.same.go(ls, ws)), rr => Laws.same.go(tt, rr)),
          Laws.pick(Laws.own.rows(oo), nn), pick.own(Laws.pick(oo, nn)), pick.own.rows(oo, nn)),
        pair.own(Laws.pick(oo, nn), ww => Laws.same.box(Laws.KAots{}, ww, ws => Laws.same.go(ls, ws)),
          rr => Laws.same.go(tt, rr), ww => box.own.v(Laws.KAots{}, ww, ws => Laws.same.go(ls, ws), ws => own.r(ls,
          ws)), rr => own.r(tt, rr)))
    case T.VPair{+nn, T.VPair{+a1, +a2}} <> +tt:
      Equal.trans(Bool, Laws.same.pair(Laws.pick(Laws.own.rows(oo), nn), ww => Laws.same.atom(T.VPair{a1, a2}, ww),
        rr => Laws.same.go(tt, rr)),
        Laws.same.pair(pick.own(Laws.pick(oo, nn)), ww => Laws.same.atom(T.VPair{a1, a2}, ww), rr => Laws.same.go(tt,
          rr)),
        Laws.same.pair(Laws.pick(oo, nn), ww => Laws.same.atom(T.VPair{a1, a2}, ww), rr => Laws.same.go(tt, rr)),
        Equal.cong(Laws.Pick, Bool, pp => Laws.same.pair(pp, ww => Laws.same.atom(T.VPair{a1, a2}, ww),
          rr => Laws.same.go(tt, rr)),
          Laws.pick(Laws.own.rows(oo), nn), pick.own(Laws.pick(oo, nn)), pick.own.rows(oo, nn)),
        pair.own(Laws.pick(oo, nn), ww => Laws.same.atom(T.VPair{a1, a2}, ww), rr => Laws.same.go(tt, rr),
          ww => atom.own.v(T.VPair{a1, a2}, ww), rr => own.r(tt, rr)))
    case T.VStr{+a1} <> +tt:
      item.own(oo, ww => Laws.same.atom(T.VStr{a1}, ww), rr => Laws.same.go(tt, rr), ww => atom.own.e(T.VStr{a1}, ww),
        rr => own.r(tt, rr))
    case T.VSpan{+a1, +a2} <> +tt:
      item.own(oo, ww => Laws.same.atom(T.VSpan{a1, a2}, ww), rr => Laws.same.go(tt, rr), ww => atom.own.e(T.VSpan{a1,
        a2}, ww), rr => own.r(tt, rr))
    case T.VInt{+a1, +a2} <> +tt:
      item.own(oo, ww => Laws.same.atom(T.VInt{a1, a2}, ww), rr => Laws.same.go(tt, rr), ww => atom.own.e(T.VInt{a1,
        a2}, ww), rr => own.r(tt, rr))
    case T.VFlo{+a1, +a2} <> +tt:
      item.own(oo, ww => Laws.same.atom(T.VFlo{a1, a2}, ww), rr => Laws.same.go(tt, rr), ww => atom.own.e(T.VFlo{a1,
        a2}, ww), rr => own.r(tt, rr))
    case T.VBool{+a1} <> +tt:
      item.own(oo, ww => Laws.same.atom(T.VBool{a1}, ww), rr => Laws.same.go(tt, rr), ww => atom.own.e(T.VBool{a1},
        ww), rr => own.r(tt, rr))
    case T.VWhen{+a1} <> +tt:
      item.own(oo, ww => Laws.same.atom(T.VWhen{a1}, ww), rr => Laws.same.go(tt, rr), ww => atom.own.e(T.VWhen{a1},
        ww), rr => own.r(tt, rr))
    case T.VArr{+ls} <> +tt:
      item.own(oo, ww => Laws.same.box(Laws.KArr{}, ww, ws => Laws.same.go(ls, ws)), rr => Laws.same.go(tt, rr),
        ww => box.own.e(Laws.KArr{}, ww, ws => Laws.same.go(ls, ws), ws => own.r(ls, ws)), rr => own.r(tt, rr))
    case T.VInl{+ls} <> +tt:
      item.own(oo, ww => Laws.same.box(Laws.KInl{}, ww, ws => Laws.same.go(ls, ws)), rr => Laws.same.go(tt, rr),
        ww => box.own.e(Laws.KInl{}, ww, ws => Laws.same.go(ls, ws), ws => own.r(ls, ws)), rr => own.r(tt, rr))
    case T.VHead{+pa, +ls} <> +tt:
      item.own(oo, ww => Laws.same.box(Laws.KHead{}, ww, ws => Laws.same.go(ls, ws)), rr => Laws.same.go(tt, rr),
        ww => box.own.e(Laws.KHead{}, ww, ws => Laws.same.go(ls, ws), ws => own.r(ls, ws)), rr => own.r(tt, rr))
    case T.VAot{+pa, +ls} <> +tt:
      item.own(oo, ww => Laws.same.box(Laws.KAot{}, ww, ws => Laws.same.go(ls, ws)), rr => Laws.same.go(tt, rr),
        ww => box.own.e(Laws.KAot{}, ww, ws => Laws.same.go(ls, ws), ws => own.r(ls, ws)), rr => own.r(tt, rr))
    case T.VAots{+pa, +ls} <> +tt:
      item.own(oo, ww => Laws.same.box(Laws.KAots{}, ww, ws => Laws.same.go(ls, ws)), rr => Laws.same.go(tt, rr),
        ww => box.own.e(Laws.KAots{}, ww, ws => Laws.same.go(ls, ws), ws => own.r(ls, ws)), rr => own.r(tt, rr))

# Order. A row matches itself wherever it stands, so rows that differ only by
# a swap of two pairs of different names match.

# every value of the front of some rows matches itself
def selfs.pre(
  pre: List<&2, T.Val>,
  +zz: List<&2, T.Val>,
  +ee: {selfs(List.append(&2, T.Val, pre, zz)) == True{} : Bool}
) -> {selfs(pre) == True{} : Bool}:
  match pre:
    case []:
      {==}
    case +hh <> +pp:
      and.tt(Laws.same.go(hh <> [], hh <> []), selfs(pp),
        Eq.and.left(Laws.same.go(hh <> [], hh <> []), selfs(List.append(&2, T.Val, pp, zz)), ee),
        selfs.pre(pp, zz, Eq.and.right(Laws.same.go(hh <> [], hh <> []), selfs(List.append(&2, T.Val, pp, zz)), ee)))

# and of the back
def selfs.suf(
  pre: List<&2, T.Val>,
  +zz: List<&2, T.Val>,
  ee: {selfs(List.append(&2, T.Val, pre, zz)) == True{} : Bool}
) -> {selfs(zz) == True{} : Bool}:
  match pre:
    case []:
      ee
    case +hh <> +pp:
      selfs.suf(pp, zz, Eq.and.right(Laws.same.go(hh <> [], hh <> []), selfs(List.append(&2, T.Val, pp, zz)), ee))

# a front that matches itself cancels
def cancel(
  pre: List<&2, T.Val>,
  +z1: List<&2, T.Val>,
  +z2: List<&2, T.Val>,
  +ee: {selfs(pre) == True{} : Bool}
) -> {Laws.same.go(List.append(&2, T.Val, pre, z1), List.append(&2, T.Val, pre, z2)) == Laws.same.go(z1, z2) : Bool}:
  match pre:
    case []:
      {==}
    case +hh <> +pp:
      Equal.trans(Bool,
        Laws.same.go(hh <> List.append(&2, T.Val, pp, z1), hh <> List.append(&2, T.Val, pp, z2)),
        Bool.and(Laws.same.go(hh <> [], hh <> []),
          Laws.same.go(List.append(&2, T.Val, pp, z1), List.append(&2, T.Val, pp, z2))),
        Laws.same.go(z1, z2),
        hc(hh, List.append(&2, T.Val, pp, z1), List.append(&2, T.Val, pp, z2)),
        Equal.trans(Bool,
          Bool.and(Laws.same.go(hh <> [], hh <> []),
            Laws.same.go(List.append(&2, T.Val, pp, z1), List.append(&2, T.Val, pp, z2))),
          Laws.same.go(List.append(&2, T.Val, pp, z1), List.append(&2, T.Val, pp, z2)),
          Laws.same.go(z1, z2),
          Equal.cong(Bool, Bool,
            xx => Bool.and(xx, Laws.same.go(List.append(&2, T.Val, pp, z1), List.append(&2, T.Val, pp, z2))),
            Laws.same.go(hh <> [], hh <> []), True{},
            Eq.and.left(Laws.same.go(hh <> [], hh <> []), selfs(pp), ee)),
          cancel(pp, z1, z2, Eq.and.right(Laws.same.go(hh <> [], hh <> []), selfs(pp), ee))))

# a pair at the head compares the same against other rows that pick the same
def pick.same(
  +nn: String,
  vv: T.Val,
  +tt: List<&2, T.Val>,
  o1: List<&2, T.Val>,
  o2: List<&2, T.Val>,
  ep: {Laws.pick(o1, nn) == Laws.pick(o2, nn) : Laws.Pick}
) -> {Laws.same.go(T.VPair{nn, vv} <> tt, o1) == Laws.same.go(T.VPair{nn, vv} <> tt, o2) : Bool}:
  match vv:
    case T.VStr{+a1}:
      Equal.cong(Laws.Pick, Bool, pp => Laws.same.pair(pp, ww => Laws.same.atom(T.VStr{a1}, ww), rr => Laws.same.go(tt,
        rr)),
        Laws.pick(o1, nn), Laws.pick(o2, nn), ep)
    case T.VSpan{+a1, +a2}:
      Equal.cong(Laws.Pick, Bool, pp => Laws.same.pair(pp, ww => Laws.same.atom(T.VSpan{a1, a2}, ww),
        rr => Laws.same.go(tt, rr)),
        Laws.pick(o1, nn), Laws.pick(o2, nn), ep)
    case T.VInt{+a1, +a2}:
      Equal.cong(Laws.Pick, Bool, pp => Laws.same.pair(pp, ww => Laws.same.atom(T.VInt{a1, a2}, ww),
        rr => Laws.same.go(tt, rr)),
        Laws.pick(o1, nn), Laws.pick(o2, nn), ep)
    case T.VFlo{+a1, +a2}:
      Equal.cong(Laws.Pick, Bool, pp => Laws.same.pair(pp, ww => Laws.same.atom(T.VFlo{a1, a2}, ww),
        rr => Laws.same.go(tt, rr)),
        Laws.pick(o1, nn), Laws.pick(o2, nn), ep)
    case T.VBool{+a1}:
      Equal.cong(Laws.Pick, Bool, pp => Laws.same.pair(pp, ww => Laws.same.atom(T.VBool{a1}, ww),
        rr => Laws.same.go(tt, rr)),
        Laws.pick(o1, nn), Laws.pick(o2, nn), ep)
    case T.VWhen{+a1}:
      Equal.cong(Laws.Pick, Bool, pp => Laws.same.pair(pp, ww => Laws.same.atom(T.VWhen{a1}, ww),
        rr => Laws.same.go(tt, rr)),
        Laws.pick(o1, nn), Laws.pick(o2, nn), ep)
    case T.VArr{+ls}:
      Equal.cong(Laws.Pick, Bool, pp => Laws.same.pair(pp, ww => Laws.same.box(Laws.KArr{}, ww, ws => Laws.same.go(ls,
        ws)), rr => Laws.same.go(tt, rr)),
        Laws.pick(o1, nn), Laws.pick(o2, nn), ep)
    case T.VInl{+ls}:
      Equal.cong(Laws.Pick, Bool, pp => Laws.same.pair(pp, ww => Laws.same.box(Laws.KInl{}, ww, ws => Laws.same.go(ls,
        ws)), rr => Laws.same.go(tt, rr)),
        Laws.pick(o1, nn), Laws.pick(o2, nn), ep)
    case T.VHead{+pa, +ls}:
      Equal.cong(Laws.Pick, Bool, pp => Laws.same.pair(pp, ww => Laws.same.box(Laws.KHead{}, ww, ws => Laws.same.go(ls,
        ws)), rr => Laws.same.go(tt, rr)),
        Laws.pick(o1, nn), Laws.pick(o2, nn), ep)
    case T.VAot{+pa, +ls}:
      Equal.cong(Laws.Pick, Bool, pp => Laws.same.pair(pp, ww => Laws.same.box(Laws.KAot{}, ww, ws => Laws.same.go(ls,
        ws)), rr => Laws.same.go(tt, rr)),
        Laws.pick(o1, nn), Laws.pick(o2, nn), ep)
    case T.VAots{+pa, +ls}:
      Equal.cong(Laws.Pick, Bool, pp => Laws.same.pair(pp, ww => Laws.same.box(Laws.KAots{}, ww, ws => Laws.same.go(ls,
        ws)), rr => Laws.same.go(tt, rr)),
        Laws.pick(o1, nn), Laws.pick(o2, nn), ep)
    case T.VPair{+a1, +a2}:
      Equal.cong(Laws.Pick, Bool, pp => Laws.same.pair(pp, ww => Laws.same.atom(T.VPair{a1, a2}, ww),
        rr => Laws.same.go(tt, rr)),
        Laws.pick(o1, nn), Laws.pick(o2, nn), ep)

# a pair of another name in front is kept, and the pair behind it picked
def pick.skip(
  +nx: String,
  +vx: T.Val,
  +ny: String,
  +vy: T.Val,
  +post: List<&2, T.Val>,
  ne: {String.eq(ny, nx) == False{} : Bool}
) -> {Laws.pick(T.VPair{ny, vy} <> T.VPair{nx, vx} <> post, nx) == Laws.Picked{vx, T.VPair{ny, vy} <> post}
  : Laws.Pick}:
  Equal.trans(Laws.Pick, Laws.pick(T.VPair{ny, vy} <> T.VPair{nx, vx} <> post, nx),
    Laws.pick.cons(T.VPair{ny, vy}, Laws.pick(T.VPair{nx, vx} <> post, nx)),
    Laws.Picked{vx, T.VPair{ny, vy} <> post},
    Equal.cong(Bool, Laws.Pick,
      bb => Laws.pick.step(bb, ny, vy, T.VPair{nx, vx} <> post, _u => Laws.pick(T.VPair{nx, vx} <> post, nx)),
      String.eq(ny, nx), False{}, ne),
    Equal.cong(Laws.Pick, Laws.Pick, pp => Laws.pick.cons(T.VPair{ny, vy}, pp),
      Laws.pick(T.VPair{nx, vx} <> post, nx), Laws.Picked{vx, post}, pick.self(nx, vx, post)))

# either order of the two pairs picks the first one the same
def pick.swap(
  +nx: String,
  +vx: T.Val,
  +ny: String,
  +vy: T.Val,
  +post: List<&2, T.Val>,
  ne: {String.eq(ny, nx) == False{} : Bool}
) -> {Laws.pick(T.VPair{ny, vy} <> T.VPair{nx, vx} <> post, nx)
  == Laws.pick(T.VPair{nx, vx} <> T.VPair{ny, vy} <> post, nx) : Laws.Pick}:
  Equal.trans(Laws.Pick, Laws.pick(T.VPair{ny, vy} <> T.VPair{nx, vx} <> post, nx),
    Laws.Picked{vx, T.VPair{ny, vy} <> post}, Laws.pick(T.VPair{nx, vx} <> T.VPair{ny, vy} <> post, nx),
    pick.skip(nx, vx, ny, vy, post, ne),
    Equal.sym(Laws.Pick, Laws.pick(T.VPair{nx, vx} <> T.VPair{ny, vy} <> post, nx),
      Laws.Picked{vx, T.VPair{ny, vy} <> post}, pick.self(nx, vx, T.VPair{ny, vy} <> post)))

# two chars compare the same either way round
def char.sym.go(
  +xx: Char,
  +yy: Char,
  b1: Bool,
  b2: Bool,
  e1: {Char.is_eq(xx, yy) == b1 : Bool},
  e2: {Char.is_eq(yy, xx) == b2 : Bool}
) -> {b1 == b2 : Bool}:
  match b1 b2:
    case True{} True{}:
      {==}
    case False{} False{}:
      {==}
    case True{} False{}:
      Equal.trans(Bool, True{}, Char.is_eq(yy, yy), False{},
        Equal.sym(Bool, Char.is_eq(yy, yy), True{}, Eq.char_eq_self(yy)),
        Equal.trans(Bool, Char.is_eq(yy, yy), Char.is_eq(yy, xx), False{},
          Equal.cong(Char, Bool, zz => Char.is_eq(yy, zz), yy, xx,
            Equal.sym(Char, xx, yy, Eq.char_eq_true(xx, yy, e1))),
          e2))
    case False{} True{}:
      Equal.trans(Bool, False{}, Char.is_eq(xx, yy), True{},
        Equal.sym(Bool, Char.is_eq(xx, yy), False{}, e1),
        Equal.trans(Bool, Char.is_eq(xx, yy), Char.is_eq(xx, xx), True{},
          Equal.cong(Char, Bool, zz => Char.is_eq(xx, zz), yy, xx, Eq.char_eq_true(yy, xx, e2)),
          Eq.char_eq_self(xx)))

# two chars compare the same either way round
def char.sym(+xx: Char, +yy: Char) -> {Char.is_eq(xx, yy) == Char.is_eq(yy, xx) : Bool}:
  char.sym.go(xx, yy, Char.is_eq(xx, yy), Char.is_eq(yy, xx), {==}, {==})

# the code's string walk answers the same either way round
def str.eq.sym(
  aa: String,
  bb: String,
  ss: Bool
) -> {T.str.eq.step(aa, bb, ss) == T.str.eq.step(bb, aa, ss) : Bool}:
  match aa bb ss:
    case SNil{} SNil{} True{}:
      {==}
    case SNil{} SNil{} False{}:
      {==}
    case SNil{} SCon{_h, _t} _s:
      {==}
    case SCon{_h, _t} SNil{} _s:
      {==}
    case SCon{+xx, +xt} SCon{+yy, +yt} True{}:
      Equal.trans(Bool, T.str.eq.step(xt, yt, Char.is_eq(xx, yy)), T.str.eq.step(xt, yt, Char.is_eq(yy, xx)),
        T.str.eq.step(yt, xt, Char.is_eq(yy, xx)),
        Equal.cong(Bool, Bool, bb2 => T.str.eq.step(xt, yt, bb2), Char.is_eq(xx, yy), Char.is_eq(yy, xx),
          char.sym(xx, yy)),
        str.eq.sym(xt, yt, Char.is_eq(yy, xx)))
    case SCon{_x, _xt} SCon{_y, _yt} False{}:
      {==}

# Base's string equality answers the same either way round
def string.sym(+aa: String, +bb: String) -> {String.eq(aa, bb) == String.eq(bb, aa) : Bool}:
  Equal.trans(Bool, String.eq(aa, bb), T.str.eq(aa, bb), String.eq(bb, aa),
    Equal.sym(Bool, T.str.eq(aa, bb), String.eq(aa, bb), str.eq.agree(aa, bb)),
    Equal.trans(Bool, T.str.eq(aa, bb), T.str.eq(bb, aa), String.eq(bb, aa),
      str.eq.sym(aa, bb, True{}), str.eq.agree(bb, aa)))

# which of two bits an `and` reads first does not change its answer
def and.comm(xx: Bool, yy: Bool) -> {Bool.and(xx, yy) == Bool.and(yy, xx) : Bool}:
  match xx yy:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# a well-formed document's rows match themselves: each value does
def Laws.same_refl(d, e):
  match d:
    case T.Doc{_e0, +rows}:
      +rr = {refl.rows(rows, wf.selfs(rows, T.WfRows{""}, e)) : {Laws.same.go(rows, rows) == True{} : Bool}}
      and.tt(Laws.same.go(rows, rows), Laws.same.go(rows, rows), rr, rr)

# same is an `and` of the two directions
def Laws.same_sym(a, b):
  match a b:
    case T.Doc{_e1, +r1} T.Doc{_e2, +r2}:
      and.comm(Laws.same.go(r1, r2), Laws.same.go(r2, r1))

# reading out changes neither direction, and the rows match themselves
def Laws.same_own(d, e):
  match d:
    case T.Doc{_e0, +rows}:
      +rr = {refl.rows(rows, wf.selfs(rows, T.WfRows{""}, e)) : {Laws.same.go(rows, rows) == True{} : Bool}}
      Equal.trans(Bool,
        Bool.and(Laws.same.go(rows, Laws.own.rows(rows)), Laws.same.go(Laws.own.rows(rows), rows)),
        Bool.and(Laws.same.go(rows, rows), Laws.same.go(rows, rows)), True{},
        Equal.trans(Bool,
          Bool.and(Laws.same.go(rows, Laws.own.rows(rows)), Laws.same.go(Laws.own.rows(rows), rows)),
          Bool.and(Laws.same.go(rows, rows), Laws.same.go(Laws.own.rows(rows), rows)),
          Bool.and(Laws.same.go(rows, rows), Laws.same.go(rows, rows)),
          Equal.cong(Bool, Bool, xx => Bool.and(xx, Laws.same.go(Laws.own.rows(rows), rows)),
            Laws.same.go(rows, Laws.own.rows(rows)), Laws.same.go(rows, rows), own.r(rows, rows)),
          Equal.cong(Bool, Bool, yy => Bool.and(Laws.same.go(rows, rows), yy),
            Laws.same.go(Laws.own.rows(rows), rows), Laws.same.go(rows, rows), own.l(rows, rows))),
        and.tt(Laws.same.go(rows, rows), Laws.same.go(rows, rows), rr, rr))

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
  +sp: {selfs(pre) == True{} : Bool},
  +sx: {selfs(T.VPair{nx, vx} <> T.VPair{ny, vy} <> post) == True{} : Bool}
) -> {Laws.same(T.Doc{e, List.append(&2, T.Val, pre, T.VPair{nx, vx} <> T.VPair{ny, vy} <> post)},
  T.Doc{e, List.append(&2, T.Val, pre, T.VPair{ny, vy} <> T.VPair{nx, vx} <> post)}) == True{} : Bool}:
  and.tt(
    Laws.same.go(List.append(&2, T.Val, pre, T.VPair{nx, vx} <> T.VPair{ny, vy} <> post),
      List.append(&2, T.Val, pre, T.VPair{ny, vy} <> T.VPair{nx, vx} <> post)),
    Laws.same.go(List.append(&2, T.Val, pre, T.VPair{ny, vy} <> T.VPair{nx, vx} <> post),
      List.append(&2, T.Val, pre, T.VPair{nx, vx} <> T.VPair{ny, vy} <> post)),
    Equal.trans(Bool,
      Laws.same.go(List.append(&2, T.Val, pre, T.VPair{nx, vx} <> T.VPair{ny, vy} <> post),
        List.append(&2, T.Val, pre, T.VPair{ny, vy} <> T.VPair{nx, vx} <> post)),
      Laws.same.go(T.VPair{nx, vx} <> T.VPair{ny, vy} <> post, T.VPair{ny, vy} <> T.VPair{nx, vx} <> post),
      True{},
      cancel(pre, T.VPair{nx, vx} <> T.VPair{ny, vy} <> post, T.VPair{ny, vy} <> T.VPair{nx, vx} <> post, sp),
      Equal.trans(Bool,
        Laws.same.go(T.VPair{nx, vx} <> T.VPair{ny, vy} <> post, T.VPair{ny, vy} <> T.VPair{nx, vx} <> post),
        Laws.same.go(T.VPair{nx, vx} <> T.VPair{ny, vy} <> post, T.VPair{nx, vx} <> T.VPair{ny, vy} <> post),
        True{},
        pick.same(nx, vx, T.VPair{ny, vy} <> post, T.VPair{ny, vy} <> T.VPair{nx, vx} <> post,
          T.VPair{nx, vx} <> T.VPair{ny, vy} <> post,
          pick.swap(nx, vx, ny, vy, post,
            Equal.trans(Bool, String.eq(ny, nx), String.eq(nx, ny), False{}, string.sym(ny, nx), ne))),
        refl.rows(T.VPair{nx, vx} <> T.VPair{ny, vy} <> post, sx))),
    Equal.trans(Bool,
      Laws.same.go(List.append(&2, T.Val, pre, T.VPair{ny, vy} <> T.VPair{nx, vx} <> post),
        List.append(&2, T.Val, pre, T.VPair{nx, vx} <> T.VPair{ny, vy} <> post)),
      Laws.same.go(T.VPair{ny, vy} <> T.VPair{nx, vx} <> post, T.VPair{nx, vx} <> T.VPair{ny, vy} <> post),
      True{},
      cancel(pre, T.VPair{ny, vy} <> T.VPair{nx, vx} <> post, T.VPair{nx, vx} <> T.VPair{ny, vy} <> post, sp),
      Equal.trans(Bool,
        Laws.same.go(T.VPair{ny, vy} <> T.VPair{nx, vx} <> post, T.VPair{nx, vx} <> T.VPair{ny, vy} <> post),
        Laws.same.go(T.VPair{ny, vy} <> T.VPair{nx, vx} <> post, T.VPair{ny, vy} <> T.VPair{nx, vx} <> post),
        True{},
        pick.same(ny, vy, T.VPair{nx, vx} <> post, T.VPair{nx, vx} <> T.VPair{ny, vy} <> post,
          T.VPair{ny, vy} <> T.VPair{nx, vx} <> post, pick.swap(ny, vy, nx, vx, post, ne)),
        refl.rows(T.VPair{ny, vy} <> T.VPair{nx, vx} <> post,
          and.tt(Laws.same.go(T.VPair{ny, vy} <> [], T.VPair{ny, vy} <> []),
            Bool.and(Laws.same.go(T.VPair{nx, vx} <> [], T.VPair{nx, vx} <> []), selfs(post)),
            Eq.and.left(Laws.same.go(T.VPair{ny, vy} <> [], T.VPair{ny, vy} <> []), selfs(post),
              Eq.and.right(Laws.same.go(T.VPair{nx, vx} <> [], T.VPair{nx, vx} <> []),
                selfs(T.VPair{ny, vy} <> post), sx)),
            and.tt(Laws.same.go(T.VPair{nx, vx} <> [], T.VPair{nx, vx} <> []), selfs(post),
              Eq.and.left(Laws.same.go(T.VPair{nx, vx} <> [], T.VPair{nx, vx} <> []),
                selfs(T.VPair{ny, vy} <> post), sx),
              Eq.and.right(Laws.same.go(T.VPair{ny, vy} <> [], T.VPair{ny, vy} <> []), selfs(post),
                Eq.and.right(Laws.same.go(T.VPair{nx, vx} <> [], T.VPair{nx, vx} <> []),
                  selfs(T.VPair{ny, vy} <> post), sx))))))))

# a well-formed document's rows each match themselves; the front cancels
# the rows before the two pairs cancel; each order then picks its first pair
# as the other order would, and what is left matches itself
def Laws.same_swap(e, pre, nx, vx, ny, vy, post, w, ne):
  +sa = {wf.selfs(List.append(&2, T.Val, pre, T.VPair{nx, vx} <> T.VPair{ny, vy} <> post), T.WfRows{""}, w)
    : {selfs(List.append(&2, T.Val, pre, T.VPair{nx, vx} <> T.VPair{ny, vy} <> post)) == True{} : Bool}}
  +sp = {selfs.pre(pre, T.VPair{nx, vx} <> T.VPair{ny, vy} <> post, sa) : {selfs(pre) == True{} : Bool}}
  +sx = {selfs.suf(pre, T.VPair{nx, vx} <> T.VPair{ny, vy} <> post, sa)
    : {selfs(T.VPair{nx, vx} <> T.VPair{ny, vy} <> post) == True{} : Bool}}
  swap.fin(e, pre, nx, vx, ny, vy, post, ne, sp, sx)

# TOML-STR-2. esc reads back what basic.one writes for one character.

# the short escapes: the character is the one the law names
def Laws.esc_quote(c, h):
  ec = Equal.sym(Char, c, '"', h)
  %ec : {Laws.esc(_) == "\\\"" : String}
  {==}

# a backslash
def Laws.esc_backslash(c, h):
  ec = Equal.sym(Char, c, '\\', h)
  %ec : {Laws.esc(_) == "\\\\" : String}
  {==}

# a backspace
def Laws.esc_b(c, h):
  ec = Equal.sym(Char, c, '\u{8}', h)
  %ec : {Laws.esc(_) == "\\b" : String}
  {==}

# a tab
def Laws.esc_t(c, h):
  ec = Equal.sym(Char, c, '\t', h)
  %ec : {Laws.esc(_) == "\\t" : String}
  {==}

# a line feed
def Laws.esc_n(c, h):
  ec = Equal.sym(Char, c, '\n', h)
  %ec : {Laws.esc(_) == "\\n" : String}
  {==}

# a form feed
def Laws.esc_f(c, h):
  ec = Equal.sym(Char, c, '\u{c}', h)
  %ec : {Laws.esc(_) == "\\f" : String}
  {==}

# a carriage return
def Laws.esc_r(c, h):
  ec = Equal.sym(Char, c, '\r', h)
  %ec : {Laws.esc(_) == "\\r" : String}
  {==}

# CTL: the escape of each control, computed once. Laws.esc runs basic.hex,
# four U32 divisions by 16, so computing a control's escape is the costly
# part of every proof that takes the controls one at a time. ctl.esc.lit
# computes it once per control, as ctl.txt, which reads the escape straight
# off the code point's bits; ctl.esc.all then hands each family that text.

# one lowercase hex digit, from its four bits, low bit first
def ctl.hx(b0: Bool, b1: Bool, b2: Bool, b3: Bool) -> Char:
  match b0 b1 b2 b3:
    case False{} False{} False{} False{}:
      '0'
    case True{} False{} False{} False{}:
      '1'
    case False{} True{} False{} False{}:
      '2'
    case True{} True{} False{} False{}:
      '3'
    case False{} False{} True{} False{}:
      '4'
    case True{} False{} True{} False{}:
      '5'
    case False{} True{} True{} False{}:
      '6'
    case True{} True{} True{} False{}:
      '7'
    case False{} False{} False{} True{}:
      '8'
    case True{} False{} False{} True{}:
      '9'
    case False{} True{} False{} True{}:
      'a'
    case True{} True{} False{} True{}:
      'b'
    case False{} False{} True{} True{}:
      'c'
    case True{} False{} True{} True{}:
      'd'
    case False{} True{} True{} True{}:
      'e'
    case True{} True{} True{} True{}:
      'f'

# u00 and two hex digits, the high one first
def ctl.u00(hi: Char, lo: Char) -> String:
  SCon{'u', SCon{'0', SCon{'0', SCon{hi, SCon{lo, SNil{}}}}}}

# what follows the backslash for a code point below 16, from its four bits:
# the five with a letter, and u000 and a digit for the rest
def ctl.txt.lo(b0: Bool, b1: Bool, b2: Bool, b3: Bool) -> String:
  match b0 b1 b2 b3:
    case False{} False{} False{} True{}:
      "b"
    case True{} False{} False{} True{}:
      "t"
    case False{} True{} False{} True{}:
      "n"
    case False{} False{} True{} True{}:
      "f"
    case True{} False{} True{} True{}:
      "r"
    case _ _ _ _:
      ctl.u00('0', ctl.hx(b0, b1, b2, b3))

# below 16, or u00 and both hex digits of the low byte
def ctl.txt.hi(
  high: Bool,
  b0: Bool,
  b1: Bool,
  b2: Bool,
  b3: Bool,
  b4: Bool,
  b5: Bool,
  b6: Bool,
  b7: Bool
) -> String:
  match high:
    case False{}:
      ctl.txt.lo(b0, b1, b2, b3)
    case True{}:
      ctl.u00(ctl.hx(b4, b5, b6, b7), ctl.hx(b0, b1, b2, b3))

# what follows the backslash, read off the low byte
def ctl.tl(uu: U32) -> String:
  match uu:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{+b4, WCon{+b5, WCon{+b6, WCon{+b7, _hi}}}}}}}}}:
      ctl.txt.hi(Bool.or(Bool.or(b4, b5), Bool.or(b6, b7)), b0, b1, b2, b3, b4, b5, b6, b7)

# the text render writes for a control: a backslash, then ctl.tl
def ctl.txt(uu: U32) -> String:
  SCon{'\\', ctl.tl(uu)}

# the escape of each control is ctl.txt: the only place a control's escape
# is computed
def ctl.esc.lit(
  +uu: U32,
  h_c: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == True{} : Bool}
) -> {ctl.txt(uu) == Laws.esc(Chr{uu}) : String}:
  Eq.ctl.all(kk => {ctl.txt(kk) == Laws.esc(Chr{kk}) : String}, uu, h_c,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==},
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==},
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==},
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==},
    {==})

# a claim about a control and its escape holds for every control once it
# holds for each of the thirty-three at its ctl.txt
def ctl.esc.all(
  -PP: U32 -> String -> Type,
  +uu: U32,
  +h_c: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == True{} : Bool},
  c00: PP(0, ctl.txt(0)),
  c01: PP(1, ctl.txt(1)),
  c02: PP(2, ctl.txt(2)),
  c03: PP(3, ctl.txt(3)),
  c04: PP(4, ctl.txt(4)),
  c05: PP(5, ctl.txt(5)),
  c06: PP(6, ctl.txt(6)),
  c07: PP(7, ctl.txt(7)),
  c08: PP(8, ctl.txt(8)),
  c09: PP(9, ctl.txt(9)),
  c10: PP(10, ctl.txt(10)),
  c11: PP(11, ctl.txt(11)),
  c12: PP(12, ctl.txt(12)),
  c13: PP(13, ctl.txt(13)),
  c14: PP(14, ctl.txt(14)),
  c15: PP(15, ctl.txt(15)),
  c16: PP(16, ctl.txt(16)),
  c17: PP(17, ctl.txt(17)),
  c18: PP(18, ctl.txt(18)),
  c19: PP(19, ctl.txt(19)),
  c20: PP(20, ctl.txt(20)),
  c21: PP(21, ctl.txt(21)),
  c22: PP(22, ctl.txt(22)),
  c23: PP(23, ctl.txt(23)),
  c24: PP(24, ctl.txt(24)),
  c25: PP(25, ctl.txt(25)),
  c26: PP(26, ctl.txt(26)),
  c27: PP(27, ctl.txt(27)),
  c28: PP(28, ctl.txt(28)),
  c29: PP(29, ctl.txt(29)),
  c30: PP(30, ctl.txt(30)),
  c31: PP(31, ctl.txt(31)),
  c127: PP(127, ctl.txt(127))
) -> PP(uu, Laws.esc(Chr{uu})):
  %ctl.esc.lit(uu, h_c) : PP(uu, _)
  Eq.ctl.all(kk => PP(kk, ctl.txt(kk)), uu, h_c,
    c00, c01, c02, c03, c04, c05, c06, c07,
    c08, c09, c10, c11, c12, c13, c14, c15,
    c16, c17, c18, c19, c20, c21, c22, c23,
    c24, c25, c26, c27, c28, c29, c30, c31,
    c127)

# WP0: the other controls, one at a time through ctl.esc.all: the five with
# short escapes are ruled out by their hypotheses, and the others compute
# from ctl.txt.

# what esc_ctl says of a code point, with its escape written as ss
def ctl.eqs(+uu: U32, ss: String) -> Type:
  {ss == "\\u00" ++ String.from_list([Laws.char_at(Laws.hex_lower(), U32.to_nat(U32.div(uu, 16))),
    Laws.char_at(Laws.hex_lower(), U32.to_nat(U32.mod(uu, 16)))]) : String}

# and with its other hypotheses first
def ctl.goals(+uu: U32, ss: String) -> Type:
  {Chr{uu} != '\u{8}' : Char} -> {Chr{uu} != '\t' : Char} -> {Chr{uu} != '\n' : Char} ->
    {Chr{uu} != '\u{c}' : Char} -> {Chr{uu} != '\r' : Char} -> ctl.eqs(uu, ss)

# every other control is \u00 and two lowercase hex digits
def Laws.esc_ctl(c, h_c, h_b, h_t, h_n, h_f, h_r):
  match c:
    case Chr{+uu}:
      ctl.esc.all(kk => ss => ctl.goals(kk, ss), uu, h_c,
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        hb => _ht => _hn => _hf => _hr =>
          Eq.bit.gone(&1, ctl.eqs(8, ctl.txt(8)), hb({==})),
        _hb => ht => _hn => _hf => _hr =>
          Eq.bit.gone(&1, ctl.eqs(9, ctl.txt(9)), ht({==})),
        _hb => _ht => hn => _hf => _hr =>
          Eq.bit.gone(&1, ctl.eqs(10, ctl.txt(10)), hn({==})),
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => hf => _hr =>
          Eq.bit.gone(&1, ctl.eqs(12, ctl.txt(12)), hf({==})),
        _hb => _ht => _hn => _hf => hr =>
          Eq.bit.gone(&1, ctl.eqs(13, ctl.txt(13)), hr({==})),
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==})(h_b, h_t, h_n, h_f, h_r)

# Every other character. Each test basic.cls makes answers False.

# a code point a char is not is not equal to it
def neq.go(
  +uu: U32,
  +kk: U32,
  bb: Bool,
  eb: {U32.is_eq(uu, kk) == bb : Bool},
  hn: {Chr{uu} != Chr{kk} : Char}
) -> {bb == False{} : Bool}:
  match bb:
    case False{}:
      {==}
    case True{}:
      Eq.bit.gone(&2, {True{} == False{} : Bool}, hn(Eq.u32_eq(uu, kk, eb)))

# a code point a char is not is not equal to it
def neq.off(
  +uu: U32,
  +kk: U32,
  hn: {Chr{uu} != Chr{kk} : Char}
) -> {U32.is_eq(uu, kk) == False{} : Bool}:
  neq.go(uu, kk, U32.is_eq(uu, kk), {==}, hn)

# a code point that is no control is not a control's
def ctl.off(
  +uu: U32,
  +kk: U32,
  eu: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool},
  ek: {Bool.or(U32.is_lt(kk, 32), U32.is_eq(kk, 127)) == True{} : Bool}
) -> {U32.is_eq(uu, kk) == False{} : Bool}:
  neq.off(uu, kk, ee => Eq.bit.clash(Equal.trans(Bool, False{}, Laws.is_ctl(Chr{uu}), True{},
    Equal.sym(Bool, Laws.is_ctl(Chr{uu}), False{}, eu),
    Equal.trans(Bool, Laws.is_ctl(Chr{uu}), Laws.is_ctl(Chr{kk}), True{},
      Equal.cong(Char, Bool, cc => Laws.is_ctl(cc), Chr{uu}, Chr{kk}, ee), ek))))

# a code point that passes none of basic.cls's tests is written as itself
def cls.plain(
  +uu: U32,
  e8: {U32.is_eq(uu, 8) == False{} : Bool},
  e9: {U32.is_eq(uu, 9) == False{} : Bool},
  e10: {U32.is_eq(uu, 10) == False{} : Bool},
  e12: {U32.is_eq(uu, 12) == False{} : Bool},
  e13: {U32.is_eq(uu, 13) == False{} : Bool},
  e34: {U32.is_eq(uu, 34) == False{} : Bool},
  e92: {U32.is_eq(uu, 92) == False{} : Bool},
  ec: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool}
) -> {T.basic.cls(uu) == T.BKCh{} : T.BK}:
  %Equal.sym(Bool, U32.is_eq(uu, 8), False{}, e8) : {T.basic.cls.8(_, uu) == T.BKCh{} : T.BK}
  %Equal.sym(Bool, U32.is_eq(uu, 9), False{}, e9) : {T.basic.cls.9(_, uu) == T.BKCh{} : T.BK}
  %Equal.sym(Bool, U32.is_eq(uu, 10), False{}, e10) : {T.basic.cls.10(_, uu) == T.BKCh{} : T.BK}
  %Equal.sym(Bool, U32.is_eq(uu, 12), False{}, e12) : {T.basic.cls.12(_, uu) == T.BKCh{} : T.BK}
  %Equal.sym(Bool, U32.is_eq(uu, 13), False{}, e13) : {T.basic.cls.13(_, uu) == T.BKCh{} : T.BK}
  %Equal.sym(Bool, U32.is_eq(uu, 34), False{}, e34) : {T.basic.cls.34(_, uu) == T.BKCh{} : T.BK}
  %Equal.sym(Bool, U32.is_eq(uu, 92), False{}, e92) : {T.basic.cls.92(_, uu) == T.BKCh{} : T.BK}
  %Equal.sym(Bool, Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), False{},
    ec) : {T.basic.cls.hex(_) == T.BKCh{} : T.BK}
  {==}

# no control, no quotation mark and no backslash: written as itself
def Laws.esc_plain(c, h_c, h_q, h_b):
  match c:
    case Chr{+uu}:
      ek = cls.plain(uu, ctl.off(uu, 8, h_c, {==}), ctl.off(uu, 9, h_c, {==}), ctl.off(uu, 10, h_c, {==}),
        ctl.off(uu, 12, h_c, {==}), ctl.off(uu, 13, h_c, {==}), neq.off(uu, 34, h_q), neq.off(uu, 92, h_b), h_c)
      %Equal.sym(T.BK, T.basic.cls(uu), T.BKCh{}, ek) :
        {String.from_list(List.reverse(&2, Char, T.basic.disp(_, Chr{uu}, uu,
          []))) == String.from_list([Chr{uu}]) : String}
      {==}

# The whole string. An output list is kept reversed; its text is read back
# with reverse.

# a list reversed onto what is already there reads as the list reversed, then
# that
def txt.onto(
  xs: List<&2, Char>,
  +acc: List<&2, Char>
) -> {String.from_list(List.reverse.go(&2, Char, xs, acc))
  == String.append(String.from_list(List.reverse.go(&2, Char, xs, [])), String.from_list(acc)) : String}:
  match xs:
    case []:
      {==}
    case +yy <> +ys:
      Equal.trans(String, String.from_list(List.reverse.go(&2, Char, ys, yy <> acc)),
        String.append(String.from_list(List.reverse.go(&2, Char, ys, [])), String.from_list(yy <> acc)),
        String.append(String.from_list(List.reverse.go(&2, Char, ys, [yy])), String.from_list(acc)),
        txt.onto(ys, yy <> acc),
        Equal.sym(String, String.append(String.from_list(List.reverse.go(&2, Char, ys, [yy])), String.from_list(acc)),
          String.append(String.from_list(List.reverse.go(&2, Char, ys, [])), String.from_list(yy <> acc)),
          Equal.trans(String,
            String.append(String.from_list(List.reverse.go(&2, Char, ys, [yy])), String.from_list(acc)),
            String.append(String.append(String.from_list(List.reverse.go(&2, Char, ys, [])), String.from_list([yy])),
              String.from_list(acc)),
            String.append(String.from_list(List.reverse.go(&2, Char, ys, [])),
              String.append(String.from_list([yy]), String.from_list(acc))),
            Equal.cong(String, String, zz => String.append(zz, String.from_list(acc)),
              String.from_list(List.reverse.go(&2, Char, ys, [yy])),
              String.append(String.from_list(List.reverse.go(&2, Char, ys, [])), String.from_list([yy])),
              txt.onto(ys, [yy])),
            Eq.append_assoc(String.from_list(List.reverse.go(&2, Char, ys, [])), String.from_list([yy]),
              String.from_list(acc)))))

# one character of each class written onto an output reads as the output,
# then the character's text
def disp.txt(
  kk: T.BK,
  +cc: Char,
  +uu: U32,
  +out: List<&2, Char>
) -> {String.from_list(List.reverse(&2, Char, T.basic.disp(kk, cc, uu, out)))
  == String.append(String.from_list(List.reverse(&2, Char, out)),
    String.from_list(List.reverse(&2, Char, T.basic.disp(kk, cc, uu, [])))) : String}:
  match kk:
    case T.BKCh{}:
      txt.onto(out, [cc])
    case T.BKEsc{+mark}:
      txt.onto(out, ['\\', mark])
    case T.BKHex{}:
      txt.onto(out, ['\\', 'u', T.hex.char(U32.mod(U32.shrn(uu, 12n), 16)), T.hex.char(U32.mod(U32.shrn(uu, 8n), 16)),
        T.hex.char(U32.mod(U32.shrn(uu, 4n), 16)), T.hex.char(U32.mod(uu, 16))])

# one character written onto an output reads as the output, then its escape
def one.txt(
  +cc: Char,
  +out: List<&2, Char>
) -> {String.from_list(List.reverse(&2, Char, T.basic.one(cc, out)))
  == String.append(String.from_list(List.reverse(&2, Char, out)), Laws.esc(cc)) : String}:
  disp.txt(T.basic.cls(Char.to_u32(cc)), cc, Char.to_u32(cc), out)

# a string's characters written onto an output read as the output, then escs
def go.txt(
  ss: String,
  +out: List<&2, Char>
) -> {String.from_list(List.reverse(&2, Char, T.basic.go(String.to_list(ss), out)))
  == String.append(String.from_list(List.reverse(&2, Char, out)), Laws.escs(ss)) : String}:
  match ss:
    case SNil{}:
      Equal.sym(String, String.append(String.from_list(List.reverse(&2, Char, out)), SNil{}),
        String.from_list(List.reverse(&2, Char, out)), Eq.append_nil(String.from_list(List.reverse(&2, Char, out))))
    case SCon{+hh, +tt}:
      Equal.trans(String,
        String.from_list(List.reverse(&2, Char, T.basic.go(String.to_list(tt), T.basic.one(hh, out)))),
        String.append(String.from_list(List.reverse(&2, Char, T.basic.one(hh, out))), Laws.escs(tt)),
        String.append(String.from_list(List.reverse(&2, Char, out)), String.append(Laws.esc(hh), Laws.escs(tt))),
        go.txt(tt, T.basic.one(hh, out)),
        Equal.trans(String,
          String.append(String.from_list(List.reverse(&2, Char, T.basic.one(hh, out))), Laws.escs(tt)),
          String.append(String.append(String.from_list(List.reverse(&2, Char, out)), Laws.esc(hh)), Laws.escs(tt)),
          String.append(String.from_list(List.reverse(&2, Char, out)), String.append(Laws.esc(hh), Laws.escs(tt))),
          Equal.cong(String, String, zz => String.append(zz, Laws.escs(tt)),
            String.from_list(List.reverse(&2, Char, T.basic.one(hh, out))),
            String.append(String.from_list(List.reverse(&2, Char, out)), Laws.esc(hh)), one.txt(hh, out)),
          Eq.append_assoc(String.from_list(List.reverse(&2, Char, out)), Laws.esc(hh), Laws.escs(tt))))

# key.basic is the quotes around escs
def Laws.basic_escs(s):
  Equal.cong(String, String, zz => String.append("\"", String.append(zz, "\"")),
    String.from_list(List.reverse(&2, Char, T.basic.go(String.to_list(s), []))), Laws.escs(s), go.txt(s, []))

# The span fast path. span.quote copies a span's characters until one needs an
# escape, and then gives up to key.basic.

# a quoting walk that has stopped stays stopped
def push.stop(bb: Bool, hh: Char) -> {T.span.quote.push(bb, T.SqStop{}, hh) == T.SqStop{} : T.SqAcc}:
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# a stopped walk ends with no copy, whatever is left
def sq.stop(src: String, +nn: U32, zz: Bool) -> {T.span.quote.go(src, nn, zz, T.SqStop{}) == T.SqNo{} : T.Sq}:
  match src zz:
    case SNil{} True{}:
      {==}
    case SNil{} False{}:
      {==}
    case SCon{_h, _t} True{}:
      {==}
    case SCon{+hh, +tt} False{}:
      Equal.trans(T.Sq,
        T.span.quote.go(tt, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)),
          T.span.quote.push(T.span.esc(Char.to_u32(hh)), T.SqStop{}, hh)),
        T.span.quote.go(tt, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)), T.SqStop{}), T.SqNo{},
        Equal.cong(T.SqAcc, T.Sq, aa => T.span.quote.go(tt, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)), aa),
          T.span.quote.push(T.span.esc(Char.to_u32(hh)), T.SqStop{}, hh), T.SqStop{},
          push.stop(T.span.esc(Char.to_u32(hh)), hh)),
        sq.stop(tt, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1))))

# the walk's answer on a text: a copy, reversed onto rr, when no character
# needs an escape
def sq.want.step(esc: Bool, more: Unit -> T.Sq) -> T.Sq:
  match esc:
    case True{}:
      T.SqNo{}
    case False{}:
      more(Unit{})

# the walk's answer on a text
def sq.want(ss: String, rr: List<&2, Char>) -> T.Sq:
  match ss:
    case SNil{}:
      T.SqOk{rr}
    case SCon{+hh, tt}:
      sq.want.step(T.span.esc(Char.to_u32(hh)), _u => sq.want(tt, hh <> rr))

# the walk's claim for the rest of a span, one character copied
def sq.Ih(tt: String, +mm: U32, hh: Char, rr: List<&2, Char>) -> Type:
  {T.span.quote.go(tt, mm, U32.is_zero(mm), T.SqRun{hh <> rr})
    == sq.want(T.span.str(tt, mm, U32.is_zero(mm)), hh <> rr) : T.Sq}

# one character of the walk: an escape stops it, anything else is copied
def sq.go.step(
  bb: Bool,
  +hh: Char,
  +tt: String,
  +mm: U32,
  +rr: List<&2, Char>,
  ih: sq.Ih(tt, mm, hh, rr)
) -> {T.span.quote.go(tt, mm, U32.is_zero(mm), T.span.quote.push(bb, T.SqRun{rr}, hh))
  == sq.want.step(bb, _u => sq.want(T.span.str(tt, mm, U32.is_zero(mm)), hh <> rr)) : T.Sq}:
  match bb:
    case True{}:
      sq.stop(tt, mm, U32.is_zero(mm))
    case False{}:
      ih

# the walk over a span answers what its characters give
def sq.go.want(
  src: String,
  +nn: U32,
  zz: Bool,
  +rr: List<&2, Char>
) -> {T.span.quote.go(src, nn, zz, T.SqRun{rr}) == sq.want(T.span.str(src, nn, zz), rr) : T.Sq}:
  match src zz:
    case SNil{} True{}:
      {==}
    case SNil{} False{}:
      {==}
    case SCon{_h, _t} True{}:
      {==}
    case SCon{+hh, +tt} False{}:
      sq.go.step(T.span.esc(Char.to_u32(hh)), hh, tt, U32.sub(nn, 1), rr,
        sq.go.want(tt, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)), hh <> rr))

# a text none of whose characters needs an escape
def plain(ss: String) -> Bool:
  match ss:
    case SNil{}:
      True{}
    case SCon{+hh, tt}:
      Bool.and(Bool.not(T.span.esc(Char.to_u32(hh))), plain(tt))

# a copy when the text is plain, and no copy otherwise
def sq.gate(ok: Bool, rr: List<&2, Char>) -> T.Sq:
  match ok:
    case True{}:
      T.SqOk{rr}
    case False{}:
      T.SqNo{}

# a character that needs no escape passes every test of basic.cls
def esc.no.ctl(
  +uu: U32,
  +ee: {T.span.esc(uu) == False{} : Bool}
) -> {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool}:
  Equal.trans(Bool, Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), Bool.or(False{}, U32.is_eq(uu, 127)), False{},
    Equal.cong(Bool, Bool, xx => Bool.or(xx, U32.is_eq(uu, 127)), U32.is_lt(uu, 32), False{},
      Eq.or.false_left(U32.is_lt(uu, 32),
        Bool.or(U32.is_eq(uu, 34), Bool.or(U32.is_eq(uu, 92), U32.is_eq(uu, 127))), ee)),
    Eq.or.false_right(U32.is_eq(uu, 92), U32.is_eq(uu, 127),
      Eq.or.false_right(U32.is_eq(uu, 34), Bool.or(U32.is_eq(uu, 92), U32.is_eq(uu, 127)),
        Eq.or.false_right(U32.is_lt(uu, 32),
          Bool.or(U32.is_eq(uu, 34), Bool.or(U32.is_eq(uu, 92), U32.is_eq(uu, 127))), ee))))

# a character that needs no escape is written as itself
def one.plain(
  +cc: Char,
  rr: List<&2, Char>,
  +ee: {T.span.esc(Char.to_u32(cc)) == False{} : Bool}
) -> {T.basic.one(cc, rr) == cc <> rr : List<&2, Char>}:
  match cc:
    case Chr{+uu}:
      Equal.cong(T.BK, List<&2, Char>, kk => T.basic.disp(kk, Chr{uu}, uu, rr), T.basic.cls(uu), T.BKCh{},
        cls.plain(uu, ctl.off(uu, 8, esc.no.ctl(uu, ee), {==}), ctl.off(uu, 9, esc.no.ctl(uu, ee), {==}),
          ctl.off(uu, 10, esc.no.ctl(uu, ee), {==}), ctl.off(uu, 12, esc.no.ctl(uu, ee), {==}),
          ctl.off(uu, 13, esc.no.ctl(uu, ee), {==}),
          Eq.or.false_left(U32.is_eq(uu, 34), Bool.or(U32.is_eq(uu, 92), U32.is_eq(uu, 127)),
            Eq.or.false_right(U32.is_lt(uu, 32),
              Bool.or(U32.is_eq(uu, 34), Bool.or(U32.is_eq(uu, 92), U32.is_eq(uu, 127))), ee)),
          Eq.or.false_left(U32.is_eq(uu, 92), U32.is_eq(uu, 127),
            Eq.or.false_right(U32.is_eq(uu, 34), Bool.or(U32.is_eq(uu, 92), U32.is_eq(uu, 127)),
              Eq.or.false_right(U32.is_lt(uu, 32),
                Bool.or(U32.is_eq(uu, 34), Bool.or(U32.is_eq(uu, 92), U32.is_eq(uu, 127))), ee))),
          esc.no.ctl(uu, ee)))

# one character of the answer: an escape gives no copy, and anything else is
# written as itself
def sq.gate.step(
  bb: Bool,
  +hh: Char,
  +tt: String,
  +rr: List<&2, Char>,
  eb: {T.span.esc(Char.to_u32(hh)) == bb : Bool},
  ih: {sq.want(tt, hh <> rr) == sq.gate(plain(tt), T.basic.go(String.to_list(tt), hh <> rr)) : T.Sq}
) -> {sq.want.step(bb, _u => sq.want(tt, hh <> rr))
  == sq.gate(Bool.and(Bool.not(bb), plain(tt)), T.basic.go(String.to_list(tt), T.basic.one(hh, rr))) : T.Sq}:
  match bb:
    case True{}:
      {==}
    case False{}:
      Equal.trans(T.Sq, sq.want(tt, hh <> rr), sq.gate(plain(tt), T.basic.go(String.to_list(tt), hh <> rr)),
        sq.gate(plain(tt), T.basic.go(String.to_list(tt), T.basic.one(hh, rr))), ih,
        Equal.cong(List<&2, Char>, T.Sq, ll => sq.gate(plain(tt), T.basic.go(String.to_list(tt), ll)),
          hh <> rr, T.basic.one(hh, rr),
          Equal.sym(List<&2, Char>, T.basic.one(hh, rr), hh <> rr, one.plain(hh, rr, eb))))

# the answer on a text is basic.go's output when the text is plain
def sq.want.gate(
  ss: String,
  +rr: List<&2, Char>
) -> {sq.want(ss, rr) == sq.gate(plain(ss), T.basic.go(String.to_list(ss), rr)) : T.Sq}:
  match ss:
    case SNil{}:
      {==}
    case SCon{+hh, +tt}:
      sq.gate.step(T.span.esc(Char.to_u32(hh)), hh, tt, rr, {==}, sq.want.gate(tt, hh <> rr))

# a copy is the quotes around the characters written as themselves
def sq.fin(
  bb: Bool,
  +src: String,
  +nn: U32
) -> {T.span.quote.fin(sq.gate(bb, T.basic.go(String.to_list(T.span.str(src, nn, U32.is_zero(nn))), ['"'])), src, nn)
  == T.key.basic(T.span.str(src, nn, U32.is_zero(nn))) : String}:
  match bb:
    case False{}:
      {==}
    case True{}:
      Equal.trans(String,
        String.from_list(List.reverse.go(&2, Char,
          T.basic.go(String.to_list(T.span.str(src, nn, U32.is_zero(nn))), ['"']), ['"'])),
        String.append(String.from_list(List.reverse(&2, Char,
          T.basic.go(String.to_list(T.span.str(src, nn, U32.is_zero(nn))), ['"']))), "\""),
        T.key.basic(T.span.str(src, nn, U32.is_zero(nn))),
        txt.onto(T.basic.go(String.to_list(T.span.str(src, nn, U32.is_zero(nn))), ['"']), ['"']),
        Equal.trans(String,
          String.append(String.from_list(List.reverse(&2, Char,
            T.basic.go(String.to_list(T.span.str(src, nn, U32.is_zero(nn))), ['"']))), "\""),
          String.append(String.append("\"", Laws.escs(T.span.str(src, nn, U32.is_zero(nn)))), "\""),
          T.key.basic(T.span.str(src, nn, U32.is_zero(nn))),
          Equal.cong(String, String, zz => String.append(zz, "\""),
            String.from_list(List.reverse(&2, Char,
              T.basic.go(String.to_list(T.span.str(src, nn, U32.is_zero(nn))), ['"']))),
            String.append("\"", Laws.escs(T.span.str(src, nn, U32.is_zero(nn)))),
            go.txt(T.span.str(src, nn, U32.is_zero(nn)), ['"'])),
          Equal.sym(String, T.key.basic(T.span.str(src, nn, U32.is_zero(nn))),
            String.append("\"", String.append(Laws.escs(T.span.str(src, nn, U32.is_zero(nn))), "\"")),
            Laws.basic_escs(T.span.str(src, nn, U32.is_zero(nn))))))

# the walk answers what the characters give, which is key.basic's text
def Laws.span_quote_basic(src, n):
  Equal.trans(String, T.span.quote(src, n),
    T.span.quote.fin(sq.want(T.span.str(src, n, U32.is_zero(n)), ['"']), src, n),
    T.key.basic(T.span.str(src, n, U32.is_zero(n))),
    Equal.cong(T.Sq, String, qq => T.span.quote.fin(qq, src, n),
      T.span.quote.go(src, n, U32.is_zero(n), T.SqRun{['"']}),
      sq.want(T.span.str(src, n, U32.is_zero(n)), ['"']), sq.go.want(src, n, U32.is_zero(n), ['"'])),
    Equal.trans(String,
      T.span.quote.fin(sq.want(T.span.str(src, n, U32.is_zero(n)), ['"']), src, n),
      T.span.quote.fin(sq.gate(plain(T.span.str(src, n, U32.is_zero(n))),
        T.basic.go(String.to_list(T.span.str(src, n, U32.is_zero(n))), ['"'])), src, n),
      T.key.basic(T.span.str(src, n, U32.is_zero(n))),
      Equal.cong(T.Sq, String, qq => T.span.quote.fin(qq, src, n),
        sq.want(T.span.str(src, n, U32.is_zero(n)), ['"']),
        sq.gate(plain(T.span.str(src, n, U32.is_zero(n))),
          T.basic.go(String.to_list(T.span.str(src, n, U32.is_zero(n))), ['"'])),
        sq.want.gate(T.span.str(src, n, U32.is_zero(n)), ['"'])),
      sq.fin(plain(T.span.str(src, n, U32.is_zero(n))), src, n)))

# the root table's first pair, then the rest: the appends regrouped
def render.regroup(
  +kk: String,
  +bb: String,
  +pf: String,
  +pt: String
) -> {String.append(String.append(String.append(kk, " = " ++ bb), "\n" ++ pf), pt)
  == kk ++ " = " ++ bb ++ "\n" ++ String.append(pf, pt) : String}:
  Equal.trans(String, String.append(String.append(String.append(kk, " = " ++ bb), "\n" ++ pf), pt),
    String.append(String.append(kk, " = " ++ bb), String.append("\n" ++ pf, pt)),
    kk ++ " = " ++ bb ++ "\n" ++ String.append(pf, pt),
    Eq.append_assoc(String.append(kk, " = " ++ bb), "\n" ++ pf, pt),
    Eq.append_assoc(kk, " = " ++ bb, String.append("\n" ++ pf, pt)))

# a string pair first in the root table
def Laws.render_string(e, name, v, rest, h):
  match v:
    case T.VStr{+a1}:
      render.regroup(T.key(name), T.key.basic(a1), T.render.pass(rest, "\n", True{}, False{}),
        T.render.pass(rest, "\n", True{}, True{}))
    case T.VSpan{+a1, +a2}:
      Equal.trans(String,
        String.append(String.append(String.append(T.key(name), " = " ++ T.span.quote(a1, a2)),
          "\n" ++ T.render.pass(rest, "\n", True{}, False{})), T.render.pass(rest, "\n", True{}, True{})),
        String.append(String.append(String.append(T.key(name), " = " ++ T.key.basic(T.span.str(a1, a2,
          U32.is_zero(a2)))),
          "\n" ++ T.render.pass(rest, "\n", True{}, False{})), T.render.pass(rest, "\n", True{}, True{})),
        T.key(name) ++ " = " ++ T.key.basic(T.span.str(a1, a2, U32.is_zero(a2))) ++ "\n" ++
          String.append(T.render.pass(rest, "\n", True{}, False{}), T.render.pass(rest, "\n", True{}, True{})),
        Equal.cong(String, String, zz => String.append(String.append(String.append(T.key(name), " = " ++ zz),
          "\n" ++ T.render.pass(rest, "\n", True{}, False{})), T.render.pass(rest, "\n", True{}, True{})),
          T.span.quote(a1, a2), T.key.basic(T.span.str(a1, a2, U32.is_zero(a2))), Laws.span_quote_basic(a1, a2)),
        render.regroup(T.key(name), T.key.basic(T.span.str(a1, a2, U32.is_zero(a2))),
          T.render.pass(rest, "\n", True{}, False{}), T.render.pass(rest, "\n", True{}, True{})))
    case T.VInt{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render(T.Doc{e, T.VPair{name, T.VInt{a1, a2}} <> rest})
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VInt{a1, a2})) ++ "\n" ++ T.render(T.Doc{e,
          rest}) : String}, h)
    case T.VFlo{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render(T.Doc{e, T.VPair{name, T.VFlo{a1, a2}} <> rest})
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VFlo{a1, a2})) ++ "\n" ++ T.render(T.Doc{e,
          rest}) : String}, h)
    case T.VBool{+a1}:
      Eq.bit.absurd(&2, {T.render(T.Doc{e, T.VPair{name, T.VBool{a1}} <> rest})
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VBool{a1})) ++ "\n" ++ T.render(T.Doc{e, rest}) : String}, h)
    case T.VWhen{+a1}:
      Eq.bit.absurd(&2, {T.render(T.Doc{e, T.VPair{name, T.VWhen{a1}} <> rest})
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VWhen{a1})) ++ "\n" ++ T.render(T.Doc{e, rest}) : String}, h)
    case T.VArr{+a1}:
      Eq.bit.absurd(&2, {T.render(T.Doc{e, T.VPair{name, T.VArr{a1}} <> rest})
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VArr{a1})) ++ "\n" ++ T.render(T.Doc{e, rest}) : String}, h)
    case T.VInl{+a1}:
      Eq.bit.absurd(&2, {T.render(T.Doc{e, T.VPair{name, T.VInl{a1}} <> rest})
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VInl{a1})) ++ "\n" ++ T.render(T.Doc{e, rest}) : String}, h)
    case T.VHead{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render(T.Doc{e, T.VPair{name, T.VHead{a1, a2}} <> rest})
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VHead{a1, a2})) ++ "\n" ++ T.render(T.Doc{e,
          rest}) : String}, h)
    case T.VAot{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render(T.Doc{e, T.VPair{name, T.VAot{a1, a2}} <> rest})
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VAot{a1, a2})) ++ "\n" ++ T.render(T.Doc{e,
          rest}) : String}, h)
    case T.VAots{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render(T.Doc{e, T.VPair{name, T.VAots{a1, a2}} <> rest})
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VAots{a1, a2})) ++ "\n" ++ T.render(T.Doc{e,
          rest}) : String}, h)
    case T.VPair{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render(T.Doc{e, T.VPair{name, T.VPair{a1, a2}} <> rest})
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VPair{a1, a2})) ++ "\n" ++ T.render(T.Doc{e,
          rest}) : String}, h)

# a string pair in the pass that writes keys
def Laws.pass_string(name, v, rest, gap, trail, h):
  match v:
    case T.VStr{_a1}:
      {==}
    case T.VSpan{+a1, +a2}:
      Equal.cong(String, String, zz => (T.key(name) ++ " = " ++ zz) ++
        T.render.suf(gap, trail, List.is_empty(&2, T.Val, rest)) ++ T.render.pass(rest, gap, trail, False{}),
        T.span.quote(a1, a2), T.key.basic(T.span.str(a1, a2, U32.is_zero(a2))), Laws.span_quote_basic(a1, a2))
    case T.VInt{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VInt{a1, a2}} <> rest, gap, trail, False{})
        == (T.key(name) ++ " = " ++ T.key.basic(T.string(T.VInt{a1, a2}))) ++ T.render.suf(gap, trail,
          List.is_empty(&2, T.Val, rest)) ++ T.render.pass(rest, gap, trail, False{}) : String}, h)
    case T.VFlo{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VFlo{a1, a2}} <> rest, gap, trail, False{})
        == (T.key(name) ++ " = " ++ T.key.basic(T.string(T.VFlo{a1, a2}))) ++ T.render.suf(gap, trail,
          List.is_empty(&2, T.Val, rest)) ++ T.render.pass(rest, gap, trail, False{}) : String}, h)
    case T.VBool{+a1}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VBool{a1}} <> rest, gap, trail, False{})
        == (T.key(name) ++ " = " ++ T.key.basic(T.string(T.VBool{a1}))) ++ T.render.suf(gap, trail, List.is_empty(&2,
          T.Val, rest)) ++ T.render.pass(rest, gap, trail, False{}) : String}, h)
    case T.VWhen{+a1}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VWhen{a1}} <> rest, gap, trail, False{})
        == (T.key(name) ++ " = " ++ T.key.basic(T.string(T.VWhen{a1}))) ++ T.render.suf(gap, trail, List.is_empty(&2,
          T.Val, rest)) ++ T.render.pass(rest, gap, trail, False{}) : String}, h)
    case T.VArr{+a1}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VArr{a1}} <> rest, gap, trail, False{})
        == (T.key(name) ++ " = " ++ T.key.basic(T.string(T.VArr{a1}))) ++ T.render.suf(gap, trail, List.is_empty(&2,
          T.Val, rest)) ++ T.render.pass(rest, gap, trail, False{}) : String}, h)
    case T.VInl{+a1}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VInl{a1}} <> rest, gap, trail, False{})
        == (T.key(name) ++ " = " ++ T.key.basic(T.string(T.VInl{a1}))) ++ T.render.suf(gap, trail, List.is_empty(&2,
          T.Val, rest)) ++ T.render.pass(rest, gap, trail, False{}) : String}, h)
    case T.VHead{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VHead{a1, a2}} <> rest, gap, trail, False{})
        == (T.key(name) ++ " = " ++ T.key.basic(T.string(T.VHead{a1, a2}))) ++ T.render.suf(gap, trail,
          List.is_empty(&2, T.Val, rest)) ++ T.render.pass(rest, gap, trail, False{}) : String}, h)
    case T.VAot{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VAot{a1, a2}} <> rest, gap, trail, False{})
        == (T.key(name) ++ " = " ++ T.key.basic(T.string(T.VAot{a1, a2}))) ++ T.render.suf(gap, trail,
          List.is_empty(&2, T.Val, rest)) ++ T.render.pass(rest, gap, trail, False{}) : String}, h)
    case T.VAots{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VAots{a1, a2}} <> rest, gap, trail, False{})
        == (T.key(name) ++ " = " ++ T.key.basic(T.string(T.VAots{a1, a2}))) ++ T.render.suf(gap, trail,
          List.is_empty(&2, T.Val, rest)) ++ T.render.pass(rest, gap, trail, False{}) : String}, h)
    case T.VPair{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VPair{a1, a2}} <> rest, gap, trail, False{})
        == (T.key(name) ++ " = " ++ T.key.basic(T.string(T.VPair{a1, a2}))) ++ T.render.suf(gap, trail,
          List.is_empty(&2, T.Val, rest)) ++ T.render.pass(rest, gap, trail, False{}) : String}, h)

# a string pair in the pass that writes tables
def Laws.pass_string_tables(name, v, rest, gap, trail, h):
  match v:
    case T.VStr{_a1}:
      {==}
    case T.VSpan{_a1, _a2}:
      {==}
    case T.VInt{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VInt{a1, a2}} <> rest, gap, trail, True{})
        == T.render.pass(rest, gap, trail, True{}) : String}, h)
    case T.VFlo{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VFlo{a1, a2}} <> rest, gap, trail, True{})
        == T.render.pass(rest, gap, trail, True{}) : String}, h)
    case T.VBool{+a1}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VBool{a1}} <> rest, gap, trail, True{})
        == T.render.pass(rest, gap, trail, True{}) : String}, h)
    case T.VWhen{+a1}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VWhen{a1}} <> rest, gap, trail, True{})
        == T.render.pass(rest, gap, trail, True{}) : String}, h)
    case T.VArr{+a1}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VArr{a1}} <> rest, gap, trail, True{})
        == T.render.pass(rest, gap, trail, True{}) : String}, h)
    case T.VInl{+a1}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VInl{a1}} <> rest, gap, trail, True{})
        == T.render.pass(rest, gap, trail, True{}) : String}, h)
    case T.VHead{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VHead{a1, a2}} <> rest, gap, trail, True{})
        == T.render.pass(rest, gap, trail, True{}) : String}, h)
    case T.VAot{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VAot{a1, a2}} <> rest, gap, trail, True{})
        == T.render.pass(rest, gap, trail, True{}) : String}, h)
    case T.VAots{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VAots{a1, a2}} <> rest, gap, trail, True{})
        == T.render.pass(rest, gap, trail, True{}) : String}, h)
    case T.VPair{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VPair{a1, a2}} <> rest, gap, trail, True{})
        == T.render.pass(rest, gap, trail, True{}) : String}, h)

# a string pair in an inline table
def Laws.inline_string(name, v, rest, gap, trail, h):
  match v:
    case T.VStr{_a1}:
      {==}
    case T.VSpan{+a1, +a2}:
      Equal.cong(String, String, zz => T.key(name) ++ " = " ++ zz ++
        T.render.suf(gap, trail, List.is_empty(&2, T.Val, rest)) ++ T.render.go(rest, gap, trail),
        T.span.quote(a1, a2), T.key.basic(T.span.str(a1, a2, U32.is_zero(a2))), Laws.span_quote_basic(a1, a2))
    case T.VInt{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.go(T.VPair{name, T.VInt{a1, a2}} <> rest, gap, trail)
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VInt{a1, a2})) ++ T.render.suf(gap, trail, List.is_empty(&2,
          T.Val, rest)) ++ T.render.go(rest, gap, trail) : String}, h)
    case T.VFlo{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.go(T.VPair{name, T.VFlo{a1, a2}} <> rest, gap, trail)
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VFlo{a1, a2})) ++ T.render.suf(gap, trail, List.is_empty(&2,
          T.Val, rest)) ++ T.render.go(rest, gap, trail) : String}, h)
    case T.VBool{+a1}:
      Eq.bit.absurd(&2, {T.render.go(T.VPair{name, T.VBool{a1}} <> rest, gap, trail)
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VBool{a1})) ++ T.render.suf(gap, trail, List.is_empty(&2,
          T.Val, rest)) ++ T.render.go(rest, gap, trail) : String}, h)
    case T.VWhen{+a1}:
      Eq.bit.absurd(&2, {T.render.go(T.VPair{name, T.VWhen{a1}} <> rest, gap, trail)
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VWhen{a1})) ++ T.render.suf(gap, trail, List.is_empty(&2,
          T.Val, rest)) ++ T.render.go(rest, gap, trail) : String}, h)
    case T.VArr{+a1}:
      Eq.bit.absurd(&2, {T.render.go(T.VPair{name, T.VArr{a1}} <> rest, gap, trail)
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VArr{a1})) ++ T.render.suf(gap, trail, List.is_empty(&2,
          T.Val, rest)) ++ T.render.go(rest, gap, trail) : String}, h)
    case T.VInl{+a1}:
      Eq.bit.absurd(&2, {T.render.go(T.VPair{name, T.VInl{a1}} <> rest, gap, trail)
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VInl{a1})) ++ T.render.suf(gap, trail, List.is_empty(&2,
          T.Val, rest)) ++ T.render.go(rest, gap, trail) : String}, h)
    case T.VHead{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.go(T.VPair{name, T.VHead{a1, a2}} <> rest, gap, trail)
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VHead{a1, a2})) ++ T.render.suf(gap, trail, List.is_empty(&2,
          T.Val, rest)) ++ T.render.go(rest, gap, trail) : String}, h)
    case T.VAot{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.go(T.VPair{name, T.VAot{a1, a2}} <> rest, gap, trail)
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VAot{a1, a2})) ++ T.render.suf(gap, trail, List.is_empty(&2,
          T.Val, rest)) ++ T.render.go(rest, gap, trail) : String}, h)
    case T.VAots{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.go(T.VPair{name, T.VAots{a1, a2}} <> rest, gap, trail)
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VAots{a1, a2})) ++ T.render.suf(gap, trail, List.is_empty(&2,
          T.Val, rest)) ++ T.render.go(rest, gap, trail) : String}, h)
    case T.VPair{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.go(T.VPair{name, T.VPair{a1, a2}} <> rest, gap, trail)
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VPair{a1, a2})) ++ T.render.suf(gap, trail, List.is_empty(&2,
          T.Val, rest)) ++ T.render.go(rest, gap, trail) : String}, h)

# a string item in an array
def Laws.array_string(v, rest, gap, trail, h):
  match v:
    case T.VStr{_a1}:
      {==}
    case T.VSpan{+a1, +a2}:
      Equal.cong(String, String, zz => zz ++
        T.render.suf(gap, trail, List.is_empty(&2, T.Val, rest)) ++ T.render.go(rest, gap, trail),
        T.span.quote(a1, a2), T.key.basic(T.span.str(a1, a2, U32.is_zero(a2))), Laws.span_quote_basic(a1, a2))
    case T.VInt{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.go(T.VInt{a1, a2} <> rest, gap, trail)
        == T.key.basic(T.string(T.VInt{a1, a2})) ++ T.render.suf(gap, trail, List.is_empty(&2, T.Val,
          rest)) ++ T.render.go(rest, gap, trail) : String}, h)
    case T.VFlo{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.go(T.VFlo{a1, a2} <> rest, gap, trail)
        == T.key.basic(T.string(T.VFlo{a1, a2})) ++ T.render.suf(gap, trail, List.is_empty(&2, T.Val,
          rest)) ++ T.render.go(rest, gap, trail) : String}, h)
    case T.VBool{+a1}:
      Eq.bit.absurd(&2, {T.render.go(T.VBool{a1} <> rest, gap, trail)
        == T.key.basic(T.string(T.VBool{a1})) ++ T.render.suf(gap, trail, List.is_empty(&2, T.Val,
          rest)) ++ T.render.go(rest, gap, trail) : String}, h)
    case T.VWhen{+a1}:
      Eq.bit.absurd(&2, {T.render.go(T.VWhen{a1} <> rest, gap, trail)
        == T.key.basic(T.string(T.VWhen{a1})) ++ T.render.suf(gap, trail, List.is_empty(&2, T.Val,
          rest)) ++ T.render.go(rest, gap, trail) : String}, h)
    case T.VArr{+a1}:
      Eq.bit.absurd(&2, {T.render.go(T.VArr{a1} <> rest, gap, trail)
        == T.key.basic(T.string(T.VArr{a1})) ++ T.render.suf(gap, trail, List.is_empty(&2, T.Val,
          rest)) ++ T.render.go(rest, gap, trail) : String}, h)
    case T.VInl{+a1}:
      Eq.bit.absurd(&2, {T.render.go(T.VInl{a1} <> rest, gap, trail)
        == T.key.basic(T.string(T.VInl{a1})) ++ T.render.suf(gap, trail, List.is_empty(&2, T.Val,
          rest)) ++ T.render.go(rest, gap, trail) : String}, h)
    case T.VHead{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.go(T.VHead{a1, a2} <> rest, gap, trail)
        == T.key.basic(T.string(T.VHead{a1, a2})) ++ T.render.suf(gap, trail, List.is_empty(&2, T.Val,
          rest)) ++ T.render.go(rest, gap, trail) : String}, h)
    case T.VAot{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.go(T.VAot{a1, a2} <> rest, gap, trail)
        == T.key.basic(T.string(T.VAot{a1, a2})) ++ T.render.suf(gap, trail, List.is_empty(&2, T.Val,
          rest)) ++ T.render.go(rest, gap, trail) : String}, h)
    case T.VAots{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.go(T.VAots{a1, a2} <> rest, gap, trail)
        == T.key.basic(T.string(T.VAots{a1, a2})) ++ T.render.suf(gap, trail, List.is_empty(&2, T.Val,
          rest)) ++ T.render.go(rest, gap, trail) : String}, h)
    case T.VPair{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.go(T.VPair{a1, a2} <> rest, gap, trail)
        == T.key.basic(T.string(T.VPair{a1, a2})) ++ T.render.suf(gap, trail, List.is_empty(&2, T.Val,
          rest)) ++ T.render.go(rest, gap, trail) : String}, h)

# TOML-TEXT-2. The walk steps that decide whether a key may add to a table.

# rebuilding the tables above a walk leaves the recorded definitions alone
def rebuild.heads(
  stack: List<&2, T.Fr>,
  vs: List<&2, T.Val>,
  bad: String,
  heads: List<&2, String>
) -> {Laws.end_heads(T.tree.rebuild(stack, vs, bad, heads)) == heads
  : List<&2, String>}:
  match stack:
    case []:
      {==}
    case fr <> tt:
      rebuild.heads(tt, T.tree.wrap(fr, vs), bad, heads)

# a table a header just recorded is one a header defined
def heads.head.first(
  +pp: String,
  hs: List<&2, String>
) -> {T.heads.head(T.heads.by.head(pp) <> hs, pp) == True{} : Bool}:
  Equal.cong(Bool, Bool, bb => T.heads.or(bb, T.heads.head(hs, pp)),
    T.str.eq(pp, pp), True{}, str.eq.self(pp))

# and it is still there once the walk is rebuilt
def rebuild.head(
  stack: List<&2, T.Fr>,
  vs: List<&2, T.Val>,
  bad: String,
  +pp: String,
  +hs: List<&2, String>
) -> {T.heads.head(Laws.end_heads(T.tree.rebuild(stack, vs, bad, T.heads.by.head(pp) <> hs)),
  pp) == True{} : Bool}:
  Equal.trans(Bool,
    T.heads.head(Laws.end_heads(T.tree.rebuild(stack, vs, bad, T.heads.by.head(pp) <> hs)), pp),
    T.heads.head(T.heads.by.head(pp) <> hs, pp),
    True{},
    Equal.cong(List<&2, String>, Bool, ll => T.heads.head(ll, pp),
      Laws.end_heads(T.tree.rebuild(stack, vs, bad, T.heads.by.head(pp) <> hs)),
      T.heads.by.head(pp) <> hs, rebuild.heads(stack, vs, bad, T.heads.by.head(pp) <> hs)),
    heads.head.first(pp, hs))

def Laws.dotted_key_refused_in_header_table(path, rows, name, vs, val, stack, pre, heads, inl, e):
  %Equal.sym(Bool, T.heads.head(heads, T.tree.pre(pre, name)), True{}, e)
    : {String.is_empty(Laws.tw_bad(T.tree.sub.head.go(_, path, rows, name, vs,
      T.JPut{val}, stack, pre, heads, inl, True{}))) == False{} : Bool}
  {==}

def Laws.dotted_key_enters_other_table(path, rows, name, vs, val, stack, pre, heads, inl, e):
  %Equal.sym(Bool, T.heads.head(heads, T.tree.pre(pre, name)), False{}, e)
    : {Laws.tw_bad(T.tree.sub.head.go(_, path, rows, name, vs, T.JPut{val}, stack,
      pre, heads, inl, True{})) == "" : String}
  {==}

def Laws.dotted_key_refused_in_array_of_tables(_path, _elems, _name, _vs, _val, _stack, _pre, _heads, _inl):
  {==}

# a header's job never asks who defined the table, wherever the walk is
def Laws.header_enters_any_table(_path, _rows, _name, _vs, arr, _stack, _pre, _heads, _inl, mark):
  match arr mark:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def Laws.header_records_new_table(name, vs, stack, bad, path, heads):
  rebuild.head(stack, T.VPair{name, T.VHead{path, []}} <> vs, bad, path, heads)

def Laws.header_records_implicit_table(p, rows, name, vs, stack, bad, path, heads, e):
  Equal.trans(Bool,
    T.heads.head(Laws.end_heads(T.tree.leaf.def.hit(T.KHead{p, rows}, name, vs, stack,
      bad, path, heads)), path),
    T.heads.head(Laws.end_heads(T.tree.leaf.def.head(False{}, name, vs, rows, stack,
      bad, path, heads)), path),
    True{},
    Equal.cong(Bool, Bool,
      ss => T.heads.head(Laws.end_heads(T.tree.leaf.def.head(ss, name, vs, rows, stack,
        bad, path, heads)), path),
      T.heads.has(heads, path), False{}, e),
    rebuild.head(stack, T.rows.repl(vs, name, T.VHead{path, rows}), bad, path, heads))

# TOML-TEXT-2, each element of an array of tables its own scope. That a path
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

# a table the drop kept does not name a path under the prefix
def drop.kept.gone(
  bb: Bool,
  +hh: String,
  +pre: String,
  +ss: String,
  rest: List<&2, String>,
  eb: {T.str.eq(hh, String.append(pre, ss)) == bb : Bool},
  eu: {String.starts_with(hh, pre) == False{} : Bool},
  ih: {T.heads.has(rest, String.append(pre, ss)) == False{} : Bool}
) -> {T.heads.or(bb, T.heads.has(rest, String.append(pre, ss))) == False{} : Bool}:
  match bb:
    case False{}:
      ih
    case True{}:
      Eq.bit.absurd(&2,
        {T.heads.or(True{}, T.heads.has(rest, String.append(pre, ss))) == False{}
          : Bool},
        Equal.trans(Bool, False{}, String.starts_with(hh, pre), True{},
          Equal.sym(Bool, String.starts_with(hh, pre), False{}, eu),
          Equal.trans(Bool, String.starts_with(hh, pre),
            String.starts_with(String.append(pre, ss), pre), True{},
            Equal.cong(String, Bool, xx => String.starts_with(xx, pre), hh,
              String.append(pre, ss), str.eq.true(hh, String.append(pre, ss), eb)),
            Eq.starts_append(pre, ss))))

# one step of the drop keeps no table under the prefix
def drop.step.gone(
  under: Bool,
  mm: Char,
  +hh: String,
  +pre: String,
  +ss: String,
  rest: List<&2, String>,
  eu: {String.starts_with(hh, pre) == under : Bool},
  ih: {T.heads.has(rest, String.append(pre, ss)) == False{} : Bool}
) -> {T.heads.has(T.heads.drop.step(under, mm, hh, rest), String.append(pre, ss))
  == False{} : Bool}:
  match under:
    case True{}:
      ih
    case False{}:
      drop.kept.gone(T.str.eq(hh, String.append(pre, ss)), hh, pre, ss, rest, {==}, eu,
        ih)

# the drop keeps no table under the prefix
def drop.gone(
  hs: List<&2, String>,
  +pre: String,
  +ss: String
) -> {T.heads.has(T.heads.drop(hs, pre), String.append(pre, ss)) == False{} : Bool}:
  match hs:
    case []:
      {==}
    case SCon{mm, +hh} <> +tt:
      drop.step.gone(String.starts_with(hh, pre), mm, hh, pre, ss, T.heads.drop(tt, pre),
        {==}, drop.gone(tt, pre, ss))
    case SNil{} <> tt:
      drop.gone(tt, pre, ss)

# a table the drop removed does not name a path outside the prefix
def drop.under.keeps(
  bb: Bool,
  +hh: String,
  +pre: String,
  +qq: String,
  rest: List<&2, String>,
  tt: List<&2, String>,
  eb: {T.str.eq(hh, qq) == bb : Bool},
  eu: {String.starts_with(hh, pre) == True{} : Bool},
  ee: {String.starts_with(qq, pre) == False{} : Bool},
  ih: {T.heads.has(rest, qq) == T.heads.has(tt, qq) : Bool}
) -> {T.heads.has(rest, qq) == T.heads.or(bb, T.heads.has(tt, qq)) : Bool}:
  match bb:
    case False{}:
      ih
    case True{}:
      Eq.bit.absurd(&2,
        {T.heads.has(rest, qq) == T.heads.or(True{}, T.heads.has(tt, qq)) : Bool},
        Equal.trans(Bool, False{}, String.starts_with(qq, pre), True{},
          Equal.sym(Bool, String.starts_with(qq, pre), False{}, ee),
          Equal.trans(Bool, String.starts_with(qq, pre), String.starts_with(hh, pre),
            True{},
            Equal.cong(String, Bool, xx => String.starts_with(xx, pre), qq, hh,
              Equal.sym(String, hh, qq, str.eq.true(hh, qq, eb))),
            eu)))

# one step of the drop leaves a path outside the prefix as defined as it was
def drop.step.keeps(
  under: Bool,
  mm: Char,
  +hh: String,
  +pre: String,
  +qq: String,
  rest: List<&2, String>,
  tt: List<&2, String>,
  eu: {String.starts_with(hh, pre) == under : Bool},
  ee: {String.starts_with(qq, pre) == False{} : Bool},
  ih: {T.heads.has(rest, qq) == T.heads.has(tt, qq) : Bool}
) -> {T.heads.has(T.heads.drop.step(under, mm, hh, rest), qq)
  == T.heads.has(SCon{mm, hh} <> tt, qq) : Bool}:
  match under:
    case True{}:
      drop.under.keeps(T.str.eq(hh, qq), hh, pre, qq, rest, tt, {==}, eu, ee, ih)
    case False{}:
      Equal.cong(Bool, Bool, xx => T.heads.or(T.str.eq(hh, qq), xx),
        T.heads.has(rest, qq), T.heads.has(tt, qq), ih)

# the drop leaves a path outside the prefix as defined as it was
def drop.keeps(
  hs: List<&2, String>,
  +pre: String,
  +qq: String,
  +ee: {String.starts_with(qq, pre) == False{} : Bool}
) -> {T.heads.has(T.heads.drop(hs, pre), qq) == T.heads.has(hs, qq) : Bool}:
  match hs:
    case []:
      {==}
    case SCon{mm, +hh} <> +tt:
      drop.step.keeps(String.starts_with(hh, pre), mm, hh, pre, qq,
        T.heads.drop(tt, pre), tt, {==}, ee, drop.keeps(tt, pre, qq, ee))
    case SNil{} <> tt:
      drop.keeps(tt, pre, qq, ee)

# a new element's tables are the old ones with those under the array dropped
def aot.heads(
  pp: String,
  elems: List<&2, T.Val>,
  name: String,
  vs: List<&2, T.Val>,
  stack: List<&2, T.Fr>,
  bad: String,
  +path: String,
  heads: List<&2, String>
) -> {Laws.end_heads(T.tree.leaf.aot.hit(T.KAots{pp, elems}, name, vs, stack, bad, path,
  heads)) == T.heads.drop(heads, String.append(path, ".")) : List<&2, String>}:
  rebuild.heads(stack, T.rows.repl(vs, name, T.VAots{path, T.VAot{path, []} <> elems}),
    bad, T.heads.drop(heads, String.append(path, ".")))

def Laws.new_element_forgets_tables_under_it(p, elems, name, vs, stack, bad, path, heads, rest):
  Equal.trans(Bool,
    T.heads.has(Laws.end_heads(T.tree.leaf.aot.hit(T.KAots{p, elems}, name, vs, stack,
      bad, path, heads)), String.append(String.append(path, "."), rest)),
    T.heads.has(T.heads.drop(heads, String.append(path, ".")),
      String.append(String.append(path, "."), rest)),
    False{},
    Equal.cong(List<&2, String>, Bool,
      ll => T.heads.has(ll, String.append(String.append(path, "."), rest)),
      Laws.end_heads(T.tree.leaf.aot.hit(T.KAots{p, elems}, name, vs, stack, bad, path,
        heads)),
      T.heads.drop(heads, String.append(path, ".")),
      aot.heads(p, elems, name, vs, stack, bad, path, heads)),
    drop.gone(heads, String.append(path, "."), rest))

def Laws.new_element_keeps_other_tables(p, elems, name, vs, stack, bad, path, heads, q, e):
  Equal.trans(Bool,
    T.heads.has(Laws.end_heads(T.tree.leaf.aot.hit(T.KAots{p, elems}, name, vs, stack,
      bad, path, heads)), q),
    T.heads.has(T.heads.drop(heads, String.append(path, ".")), q),
    T.heads.has(heads, q),
    Equal.cong(List<&2, String>, Bool, ll => T.heads.has(ll, q),
      Laws.end_heads(T.tree.leaf.aot.hit(T.KAots{p, elems}, name, vs, stack, bad, path,
        heads)),
      T.heads.drop(heads, String.append(path, ".")),
      aot.heads(p, elems, name, vs, stack, bad, path, heads)),
    drop.keeps(heads, String.append(path, "."), q, e))

# TOML-TEXT-1 and TOML-TEXT-2 for inline tables.

# a pair whose name is not k is passed over by rows.look
def look.skip(
  +nn: String,
  -vv: T.Val,
  -rest: List<&2, T.Val>,
  +kk: String,
  ee: {String.eq(nn, kk) == False{} : Bool}
) -> {T.rows.look(T.VPair{nn, vv} <> rest, kk) == T.rows.look(rest, kk) : T.Look}:
  Equal.cong(Bool, T.Look, bb => T.look.step(bb, vv, _u => T.rows.look(rest, kk)),
    T.str.eq(nn, kk), False{},
    Equal.trans(Bool, T.str.eq(nn, kk), String.eq(nn, kk), False{},
      str.eq.agree(nn, kk), ee))

# rows.look misses when no pair in the rows is named k
def look.misses(
  rows: List<&2, T.Val>,
  +kk: String,
  +ee: {Laws.has_pair(rows, kk) == False{} : Bool}
) -> {T.rows.look(rows, kk) == T.KMiss{} : T.Look}:
  match rows:
    case []:
      {==}
    case T.VPair{+nn, +vv} <> +tt:
      Equal.trans(T.Look, T.rows.look(T.VPair{nn, vv} <> tt, kk), T.rows.look(tt, kk),
        T.KMiss{},
        look.skip(nn, vv, tt, kk,
          Eq.or.false_left(String.eq(nn, kk), Laws.has_pair(tt, kk), ee)),
        look.misses(tt, kk,
          Eq.or.false_right(String.eq(nn, kk), Laws.has_pair(tt, kk), ee)))
    case T.VStr{_a} <> tt:
      look.misses(tt, kk, ee)
    case T.VSpan{_a, _b} <> tt:
      look.misses(tt, kk, ee)
    case T.VInt{_a, _b} <> tt:
      look.misses(tt, kk, ee)
    case T.VFlo{_a, _b} <> tt:
      look.misses(tt, kk, ee)
    case T.VBool{_a} <> tt:
      look.misses(tt, kk, ee)
    case T.VWhen{_a} <> tt:
      look.misses(tt, kk, ee)
    case T.VArr{_a} <> tt:
      look.misses(tt, kk, ee)
    case T.VInl{_a} <> tt:
      look.misses(tt, kk, ee)
    case T.VHead{_a, _b} <> tt:
      look.misses(tt, kk, ee)
    case T.VAot{_a, _b} <> tt:
      look.misses(tt, kk, ee)
    case T.VAots{_a, _b} <> tt:
      look.misses(tt, kk, ee)

# the first key of an inline table makes a table there, and the key is in it
def inl.first(
  inl: List<&2, T.Val>,
  +bb: String,
  cc: String,
  vv: T.Val,
  ee: {Laws.has_pair(inl, bb) == False{} : Bool}
) -> {Laws.end_rows(T.tree.walk([bb, cc], T.Tw{inl, T.JPut{vv}, [], "", "", [], True{}},
  0)) == T.VPair{bb, T.VHead{T.tree.pre("", bb), [T.VPair{cc, vv}]}} <> inl
  : List<&2, T.Val>}:
  Equal.cong(T.Look, List<&2, T.Val>,
    hh => Laws.end_rows(T.tree.leaf(cc, T.tree.sub.look(hh, bb, inl, T.JPut{vv}, [], "",
      [], True{}, True{}))),
    T.rows.look(inl, bb), T.KMiss{}, look.misses(inl, bb, ee))

# the second key goes on in that table: bb finds it, and dd is not cc
def inl.second(
  inl: List<&2, T.Val>,
  +bb: String,
  +cc: String,
  +dd: String,
  vv: T.Val,
  ww: T.Val,
  ff: {String.eq(cc, dd) == False{} : Bool}
) -> {Laws.end_bad(T.tree.walk([bb, dd], T.Tw{T.VPair{bb, T.VHead{T.tree.pre("", bb),
  [T.VPair{cc, vv}]}} <> inl, T.JPut{ww}, [], "", "", [], True{}}, 0)) == "" : String}:
  Equal.trans(String,
    Laws.end_bad(T.tree.leaf(dd, T.tree.sub.look(T.look.step(T.str.eq(bb, bb),
      T.VHead{T.tree.pre("", bb), [T.VPair{cc, vv}]}, _u => T.rows.look(inl, bb)), bb,
      T.VPair{bb, T.VHead{T.tree.pre("", bb), [T.VPair{cc, vv}]}} <> inl, T.JPut{ww},
      [], "", [], True{}, True{}))),
    Laws.end_bad(T.tree.leaf(dd, T.tree.sub.look(T.KHead{T.tree.pre("", bb),
      [T.VPair{cc, vv}]}, bb,
      T.VPair{bb, T.VHead{T.tree.pre("", bb), [T.VPair{cc, vv}]}} <> inl, T.JPut{ww},
      [], "", [], True{}, True{}))),
    "",
    Equal.cong(Bool, String,
      xx => Laws.end_bad(T.tree.leaf(dd, T.tree.sub.look(T.look.step(xx,
        T.VHead{T.tree.pre("", bb), [T.VPair{cc, vv}]}, _u => T.rows.look(inl, bb)), bb,
        T.VPair{bb, T.VHead{T.tree.pre("", bb), [T.VPair{cc, vv}]}} <> inl, T.JPut{ww},
        [], "", [], True{}, True{}))),
      T.str.eq(bb, bb), True{}, str.eq.self(bb)),
    Equal.cong(Bool, String,
      xx => Laws.end_bad(T.tree.leaf.put(T.find.step(xx, vv, _u => T.rows.find([], dd)),
        dd, [T.VPair{cc, vv}], ww,
        [T.FrRep{bb, T.VPair{bb, T.VHead{T.tree.pre("", bb), [T.VPair{cc, vv}]}} <> inl,
          T.tree.pre("", bb)}],
        "", T.heads.define(T.JPut{ww}, T.tree.pre("", bb), []))),
      T.str.eq(cc, dd), False{},
      Equal.trans(Bool, T.str.eq(cc, dd), String.eq(cc, dd), False{},
        str.eq.agree(cc, dd), ff)))

def Laws.inline_dotted_keys_share_a_prefix(inl, b, c, d, v, w, e, f):
  Equal.trans(String,
    Laws.end_bad(T.tree.walk([b, d], T.Tw{Laws.end_rows(T.tree.walk([b, c],
      T.Tw{inl, T.JPut{v}, [], "", "", [], True{}}, 0)), T.JPut{w}, [], "", "", [],
      True{}}, 0)),
    Laws.end_bad(T.tree.walk([b, d], T.Tw{T.VPair{b, T.VHead{T.tree.pre("", b),
      [T.VPair{c, v}]}} <> inl, T.JPut{w}, [], "", "", [], True{}}, 0)),
    "",
    Equal.cong(List<&2, T.Val>, String,
      rr => Laws.end_bad(T.tree.walk([b, d], T.Tw{rr, T.JPut{w}, [], "", "", [], True{}},
        0)),
      Laws.end_rows(T.tree.walk([b, c], T.Tw{inl, T.JPut{v}, [], "", "", [], True{}}, 0)),
      T.VPair{b, T.VHead{T.tree.pre("", b), [T.VPair{c, v}]}} <> inl,
      inl.first(inl, b, c, v, e)),
    inl.second(inl, b, c, d, v, w, f))

# by induction on the rows, each case as inl.seal takes it
def Laws.closed_inline_table_holds_no_open_table(rows):
  match rows:
    case []:
      {==}
    case T.VPair{_n, T.VHead{_p, _r}} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VPair{_n, T.VStr{_a}} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VPair{_n, T.VSpan{_a, _b}} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VPair{_n, T.VInt{_a, _b}} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VPair{_n, T.VFlo{_a, _b}} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VPair{_n, T.VBool{_a}} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VPair{_n, T.VWhen{_a}} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VPair{_n, T.VArr{_a}} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VPair{_n, T.VInl{_a}} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VPair{_n, T.VAot{_a, _b}} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VPair{_n, T.VAots{_a, _b}} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VPair{_n, T.VPair{_a, _b}} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VStr{_a} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VSpan{_a, _b} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VInt{_a, _b} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VFlo{_a, _b} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VBool{_a} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VWhen{_a} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VArr{_a} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VInl{_a} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VHead{_a, _b} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VAot{_a, _b} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)
    case T.VAots{_a, _b} <> tt:
      Laws.closed_inline_table_holds_no_open_table(tt)

def Laws.inline_table_refuses_keys(_name, _vs, _job, _stack, _pre, _heads, _inl, _mark):
  {==}


# TOML-TEXT-1 and TOML-KEY-3: the header scanner. Each character computes to
# its step, and a refusal comes to the failed state through err.sinks.

def Laws.header_quote_after_bare_refused(
  bad,
  rows,
  heads,
  here,
  parts,
  c,
  cs,
  back,
  qkind,
  stack,
  uni,
  left,
  arrtab,
  lit,
  t
):
  match lit:
    case True{}:
      err.sinks(T.St{bad, rows, heads, here, parts, c <> cs, T.LHead{}, back, qkind,
        stack, T.HNone{}, uni, left, arrtab, False{}}, 'i', "nvalid header", t)
    case False{}:
      err.sinks(T.St{bad, rows, heads, here, parts, c <> cs, T.LHead{}, back, qkind,
        stack, T.HNone{}, uni, left, arrtab, False{}}, 'i', "nvalid header", t)

def Laws.header_quote_at_start_opens_segment(
  _bad,
  _rows,
  _heads,
  _here,
  _back,
  _qkind,
  _stack,
  _uni,
  _left,
  _arrtab,
  lit
):
  match lit:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.header_blank_then_bracket_refused(
  bad,
  rows,
  heads,
  here,
  parts,
  back,
  qkind,
  stack,
  uni,
  left,
  arrtab,
  tab,
  t
):
  match tab:
    case True{}:
      err.sinks(T.St{bad, rows, heads, here, parts, [], T.LHeadDot{}, back, qkind, stack,
        T.HNone{}, uni, left, arrtab, False{}}, 'i', "nvalid header", t)
    case False{}:
      err.sinks(T.St{bad, rows, heads, here, parts, [], T.LHeadDot{}, back, qkind, stack,
        T.HNone{}, uni, left, arrtab, False{}}, 'i', "nvalid header", t)

def Laws.header_blank_waits_for_segment(
  _bad,
  _rows,
  _heads,
  _here,
  _parts,
  _back,
  _qkind,
  _stack,
  _uni,
  _left,
  _arrtab,
  tab
):
  match tab:
    case True{}:
      {==}
    case False{}:
      {==}

# TOML-KEY-2's read-back. A quoted key is read in LKeyQ, one character of
# escs at a time: a plain character on the fast path, an escape through
# LKeyE, and a \u escape through LKeyU. After each character's escape the
# scanner is back in LKeyQ with that character pushed onto its buffer; only
# where an escape last returned it (back) differs, and nothing after the key
# reads that. A per-character step takes the rest of the walk as a function
# of back, so no lemma has to name it. The per-character lemmas are WP0's
# quoted-segment family (qs, below), taken at a key's state.

# a scanner inside the first quoted key of a document, its characters so far
# reversed in buf
def kq(back: T.Lex, buf: List<&2, Char>) -> T.St:
  T.St{"", [], [], [], [], buf, T.LKeyQ{}, back, T.QBasic{}, [], T.HNone{}, 0, 0,
    False{}, False{}}

# the document of one pair named by a buffer, holding the integer 1
def kq.doc(buf: List<&2, Char>) -> T.Doc:
  T.Doc{"", [T.VPair{T.buf.str.go(buf, ""), T.VInt{T.Plus{}, "1"}}]}

# an `or` of two bits that each answered False
def or.ff(
  aa: Bool,
  bb: Bool,
  ea: {aa == False{} : Bool},
  eb: {bb == False{} : Bool}
) -> {Bool.or(aa, bb) == False{} : Bool}:
  match aa:
    case True{}:
      Eq.bit.absurd2(&2, {Bool.or(True{}, bb) == False{} : Bool}, ea)
    case False{}:
      eb

# WP0: the quoted-segment family. A basic quoted segment is read the same
# way in a key (LKeyQ, with LKeyE and LKeyU for its escapes) and in a header
# (LHeadQ, with LHeadE and LHeadU); only the state each character returns to
# differs, and the state after the closing quote. The lemmas below take which
# one as a bit hd, and every field a quoted segment leaves alone as a
# parameter, so key_reads_back reads its key with them at hd = False and a
# header proof reads a segment with them at hd = True. Those fields are rw
# (the rows), hs (heads), he (here), ps (parts), sk (the stack) and ab
# (arrtab).

# the state inside a basic quoted segment: a key's, or a header's when hd
def qs.lex(hd: Bool) -> T.Lex:
  match hd:
    case False{}:
      T.LKeyQ{}
    case True{}:
      T.LHeadQ{}

# the state after the segment's closing quote
def qs.close(hd: Bool) -> T.Lex:
  match hd:
    case False{}:
      T.LAfter{}
    case True{}:
      T.LHeadGap{}

# a scanner inside a basic quoted segment, its characters so far reversed in
# buf, and back wherever the last escape left it
def qs(
  hd: Bool,
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  parts: List<&2, String>,
  stack: List<&2, T.Ctx>,
  arrtab: Bool,
  back: T.Lex,
  buf: List<&2, Char>
) -> T.St:
  T.St{"", rows, heads, here, parts, buf, qs.lex(hd), back, T.QBasic{}, stack, T.HNone{},
    0, 0, arrtab, False{}}

# one character's escape read from a quoted segment, then the rest of the
# text: the rest is read with the character pushed, from wherever the escape
# left back
def qs.Goal(
  +uu: U32,
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>,
  +rest: String,
  +goal: T.Doc
) -> Type:
  (@bk: T.Lex -> {T.doc.read(rest, T.MScan{qs(hd, rw, hs, he, ps, sk, ab, bk, Chr{uu} <> buf)}) == goal
    : T.Doc}) ->
    {T.doc.read(String.append(Laws.esc(Chr{uu}), rest), T.MScan{qs(hd, rw, hs, he, ps, sk, ab, back, buf)})
      == goal : T.Doc}

# the fast step of a character in a quoted segment is the segment's full step
def qs.fast(
  +uu: U32,
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>
) -> {T.read.fast(qs(hd, rw, hs, he, ps, sk, ab, back, buf), Chr{uu}) == T.read.once2(T.lex.kq.go(U32.is_eq(uu, 34),
  U32.is_eq(uu, 92), True{}, Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)),
  qs(hd, rw, hs, he, ps, sk, ab, back, buf), Chr{uu}, qs.close(hd), qs.lex(hd))) : T.St}:
  match hd:
    case False{}:
      {==}
    case True{}:
      {==}

# a quoted segment's state is no quote that opens a string
def qs.wrap(
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>
) -> {T.doc.wrap(qs(hd, rw, hs, he, ps, sk, ab, back, buf)) == T.MScan{qs(hd, rw, hs, he, ps, sk, ab, back, buf)}
  : T.Mode}:
  match hd:
    case False{}:
      {==}
    case True{}:
      {==}

# a character that is no control is pushed: str.bad passes it
def qs.char(
  ctl: Bool,
  +uu: U32,
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>,
  hc: {ctl == False{} : Bool}
) -> {T.read.once2(T.lex.kq.char.go(T.str.bad.go(ctl, U32.is_eq(uu, 9),
  Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)), False{}), qs(hd, rw, hs, he, ps, sk, ab, back, buf), Chr{uu},
  qs.lex(hd))) == qs(hd, rw, hs, he, ps, sk, ab, back, Chr{uu} <> buf) : T.St}:
  match ctl:
    case False{}:
      {==}
    case True{}:
      Eq.bit.absurd2(&2, {T.read.once2(T.lex.kq.char.go(T.str.bad.go(True{},
        U32.is_eq(uu, 9), Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)), False{}),
        qs(hd, rw, hs, he, ps, sk, ab, back, buf), Chr{uu}, qs.lex(hd)))
        == qs(hd, rw, hs, he, ps, sk, ab, back, Chr{uu} <> buf) : T.St}, hc)

# a character that is no quote, no backslash and no newline is no closer and
# no escape
def qs.go(
  quote: Bool,
  bs: Bool,
  nl: Bool,
  +uu: U32,
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>,
  hq: {quote == False{} : Bool},
  hb: {bs == False{} : Bool},
  hn: {nl == False{} : Bool},
  hc: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool}
) -> {T.read.once2(T.lex.kq.go(quote, bs, True{}, nl, qs(hd, rw, hs, he, ps, sk, ab, back, buf), Chr{uu},
  qs.close(hd), qs.lex(hd))) == qs(hd, rw, hs, he, ps, sk, ab, back, Chr{uu} <> buf) : T.St}:
  match quote:
    case True{}:
      Eq.bit.absurd2(&2, {T.read.once2(T.lex.kq.go(True{}, bs, True{}, nl,
        qs(hd, rw, hs, he, ps, sk, ab, back, buf), Chr{uu}, qs.close(hd), qs.lex(hd)))
        == qs(hd, rw, hs, he, ps, sk, ab, back, Chr{uu} <> buf) : T.St}, hq)
    case False{}:
      match bs:
        case True{}:
          Eq.bit.absurd2(&2, {T.read.once2(T.lex.kq.go(False{}, True{}, True{}, nl,
            qs(hd, rw, hs, he, ps, sk, ab, back, buf), Chr{uu}, qs.close(hd), qs.lex(hd)))
            == qs(hd, rw, hs, he, ps, sk, ab, back, Chr{uu} <> buf) : T.St}, hb)
        case False{}:
          match nl:
            case True{}:
              Eq.bit.absurd2(&2, {T.read.once2(T.lex.kq.go(False{}, False{}, True{}, True{},
                qs(hd, rw, hs, he, ps, sk, ab, back, buf), Chr{uu}, qs.close(hd), qs.lex(hd)))
                == qs(hd, rw, hs, he, ps, sk, ab, back, Chr{uu} <> buf) : T.St}, hn)
            case False{}:
              qs.char(Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), uu, hd, rw, hs, he, ps, sk, ab, back, buf,
                hc)

# the fast step pushes a character
def qs.Fast(
  +uu: U32,
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>
) -> Type:
  {T.read.fast(qs(hd, rw, hs, he, ps, sk, ab, back, buf), Chr{uu})
    == qs(hd, rw, hs, he, ps, sk, ab, back, Chr{uu} <> buf) : T.St}

# the doc.scan dispatch sends such a character to the fast step, and an
# apostrophe comes back from doc.wrap in the segment's state
def qs.q(
  dq: Bool,
  sq: Bool,
  cr: Bool,
  +uu: U32,
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>,
  hq: {dq == False{} : Bool},
  hr: {cr == False{} : Bool},
  fast: qs.Fast(uu, hd, rw, hs, he, ps, sk, ab, back, buf)
) -> {T.doc.scan.q(dq, sq, cr, qs(hd, rw, hs, he, ps, sk, ab, back, buf), Chr{uu})
  == T.MScan{qs(hd, rw, hs, he, ps, sk, ab, back, Chr{uu} <> buf)} : T.Mode}:
  match dq:
    case True{}:
      Eq.bit.absurd2(&2, {T.doc.scan.q(True{}, sq, cr, qs(hd, rw, hs, he, ps, sk, ab, back, buf), Chr{uu})
        == T.MScan{qs(hd, rw, hs, he, ps, sk, ab, back, Chr{uu} <> buf)} : T.Mode}, hq)
    case False{}:
      match sq:
        case True{}:
          Equal.trans(T.Mode, T.doc.wrap(T.read.fast(qs(hd, rw, hs, he, ps, sk, ab, back, buf), Chr{uu})),
            T.doc.wrap(qs(hd, rw, hs, he, ps, sk, ab, back, Chr{uu} <> buf)),
            T.MScan{qs(hd, rw, hs, he, ps, sk, ab, back, Chr{uu} <> buf)},
            Equal.cong(T.St, T.Mode, st => T.doc.wrap(st),
              T.read.fast(qs(hd, rw, hs, he, ps, sk, ab, back, buf), Chr{uu}),
              qs(hd, rw, hs, he, ps, sk, ab, back, Chr{uu} <> buf), fast),
            qs.wrap(hd, rw, hs, he, ps, sk, ab, back, Chr{uu} <> buf))
        case False{}:
          match cr:
            case True{}:
              Eq.bit.absurd2(&2, {T.doc.scan.q(False{}, False{}, True{}, qs(hd, rw, hs, he, ps, sk, ab, back, buf),
                Chr{uu}) == T.MScan{qs(hd, rw, hs, he, ps, sk, ab, back, Chr{uu} <> buf)} : T.Mode}, hr)
            case False{}:
              Equal.cong(T.St, T.Mode, st => T.MScan{st},
                T.read.fast(qs(hd, rw, hs, he, ps, sk, ab, back, buf), Chr{uu}),
                qs(hd, rw, hs, he, ps, sk, ab, back, Chr{uu} <> buf), fast)

# a character written as itself is pushed, and back stays where it was
def qs.plain(
  +uu: U32,
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>,
  +rest: String,
  +goal: T.Doc,
  +e34: {U32.is_eq(uu, 34) == False{} : Bool},
  +e92: {U32.is_eq(uu, 92) == False{} : Bool},
  +ec: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool},
  ih: @bk: T.Lex -> {T.doc.read(rest, T.MScan{qs(hd, rw, hs, he, ps, sk, ab, bk, Chr{uu} <> buf)}) == goal : T.Doc}
) -> {T.doc.read(String.append(Laws.esc(Chr{uu}), rest), T.MScan{qs(hd, rw, hs, he, ps, sk, ab, back, buf)})
  == goal : T.Doc}:
  +e10 = {ctl.off(uu, 10, ec, {==}) : {U32.is_eq(uu, 10) == False{} : Bool}}
  +e13 = {ctl.off(uu, 13, ec, {==}) : {U32.is_eq(uu, 13) == False{} : Bool}}
  ek = cls.plain(uu, ctl.off(uu, 8, ec, {==}), ctl.off(uu, 9, ec, {==}), e10,
    ctl.off(uu, 12, ec, {==}), e13, e34, e92, ec)
  %Equal.sym(T.BK, T.basic.cls(uu), T.BKCh{}, ek) : {T.doc.read(String.append(
    String.from_list(List.reverse(&2, Char, T.basic.disp(_, Chr{uu}, uu, []))), rest),
    T.MScan{qs(hd, rw, hs, he, ps, sk, ab, back, buf)}) == goal : T.Doc}
  Equal.trans(T.Doc,
    T.doc.read(rest, T.doc.scan(qs(hd, rw, hs, he, ps, sk, ab, back, buf), Chr{uu})),
    T.doc.read(rest, T.MScan{qs(hd, rw, hs, he, ps, sk, ab, back, Chr{uu} <> buf)}),
    goal,
    Equal.cong(T.Mode, T.Doc, md => T.doc.read(rest, md),
      T.doc.scan(qs(hd, rw, hs, he, ps, sk, ab, back, buf), Chr{uu}),
      T.MScan{qs(hd, rw, hs, he, ps, sk, ab, back, Chr{uu} <> buf)},
      qs.q(U32.is_eq(uu, 34), U32.is_eq(uu, 39), U32.is_eq(uu, 13), uu, hd, rw, hs, he, ps, sk, ab, back, buf, e34,
        e13, Equal.trans(T.St, T.read.fast(qs(hd, rw, hs, he, ps, sk, ab, back, buf), Chr{uu}),
          T.read.once2(T.lex.kq.go(U32.is_eq(uu, 34), U32.is_eq(uu, 92), True{},
            Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)), qs(hd, rw, hs, he, ps, sk, ab, back, buf), Chr{uu},
            qs.close(hd), qs.lex(hd))),
          qs(hd, rw, hs, he, ps, sk, ab, back, Chr{uu} <> buf),
          qs.fast(uu, hd, rw, hs, he, ps, sk, ab, back, buf),
          qs.go(U32.is_eq(uu, 34), U32.is_eq(uu, 92), Bool.or(U32.is_eq(uu, 10),
            U32.is_eq(uu, 13)), uu, hd, rw, hs, he, ps, sk, ab, back, buf, e34, e92, or.ff(U32.is_eq(uu, 10),
            U32.is_eq(uu, 13), e10, e13), ec)))),
    ih(back))

# a quotation mark: its escape reads back by computation, and leaves back at
# the segment's state
def qs.q34(
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>,
  +rest: String,
  +goal: T.Doc
) -> qs.Goal(34, hd, rw, hs, he, ps, sk, ab, back, buf, rest, goal):
  match hd:
    case False{}:
      ih => ih(T.LKeyQ{})
    case True{}:
      ih => ih(T.LHeadQ{})

# and a backslash
def qs.q92(
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>,
  +rest: String,
  +goal: T.Doc
) -> qs.Goal(92, hd, rw, hs, he, ps, sk, ab, back, buf, rest, goal):
  match hd:
    case False{}:
      ih => ih(T.LKeyQ{})
    case True{}:
      ih => ih(T.LHeadQ{})

# CTL: qs.Goal with the escape's text as ss, for ctl.esc.all
def qs.GoalS(
  +uu: U32,
  ss: String,
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>,
  +rest: String,
  +goal: T.Doc
) -> Type:
  (@bk: T.Lex -> {T.doc.read(rest, T.MScan{qs(hd, rw, hs, he, ps, sk, ab, bk, Chr{uu} <> buf)}) == goal
    : T.Doc}) ->
    {T.doc.read(String.append(ss, rest), T.MScan{qs(hd, rw, hs, he, ps, sk, ab, back, buf)}) == goal : T.Doc}

# a control: each of the thirty-three escapes reads back by computation, and
# leaves back at the segment's state
def qs.ctl(
  +uu: U32,
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>,
  +rest: String,
  +goal: T.Doc,
  h_c: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == True{} : Bool}
) -> qs.Goal(uu, hd, rw, hs, he, ps, sk, ab, back, buf, rest, goal):
  match hd:
    case False{}:
      ctl.esc.all(kk => ss => qs.GoalS(kk, ss, False{}, rw, hs, he, ps, sk, ab, back, buf, rest, goal), uu,
        h_c,
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}))
    case True{}:
      ctl.esc.all(kk => ss => qs.GoalS(kk, ss, True{}, rw, hs, he, ps, sk, ab, back, buf, rest, goal), uu,
        h_c,
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}))

# one code point k that the test found: its answer answers for the character
def qs.is(
  +uu: U32,
  +kk: U32,
  ee: {U32.is_eq(uu, kk) == True{} : Bool},
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>,
  +rest: String,
  +goal: T.Doc,
  at: qs.Goal(kk, hd, rw, hs, he, ps, sk, ab, back, buf, rest, goal)
) -> qs.Goal(uu, hd, rw, hs, he, ps, sk, ab, back, buf, rest, goal):
  eu = Equal.cong(Char, U32, cc => Char.to_u32(cc), Chr{uu}, Chr{kk}, Eq.u32_eq(uu, kk, ee))
  %Equal.sym(U32, uu, kk, eu) : qs.Goal(_, hd, rw, hs, he, ps, sk, ab, back, buf, rest, goal)
  at

# every character: a quote, a backslash, a control, or one written as itself
def qs.split(
  +uu: U32,
  q34: Bool,
  b92: Bool,
  ctl: Bool,
  +e34: {U32.is_eq(uu, 34) == q34 : Bool},
  +e92: {U32.is_eq(uu, 92) == b92 : Bool},
  +ec: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == ctl : Bool},
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>,
  +rest: String,
  +goal: T.Doc
) -> qs.Goal(uu, hd, rw, hs, he, ps, sk, ab, back, buf, rest, goal):
  match q34:
    case True{}:
      qs.is(uu, 34, e34, hd, rw, hs, he, ps, sk, ab, back, buf, rest, goal,
        qs.q34(hd, rw, hs, he, ps, sk, ab, back, buf, rest, goal))
    case False{}:
      match b92:
        case True{}:
          qs.is(uu, 92, e92, hd, rw, hs, he, ps, sk, ab, back, buf, rest, goal,
            qs.q92(hd, rw, hs, he, ps, sk, ab, back, buf, rest, goal))
        case False{}:
          match ctl:
            case True{}:
              qs.ctl(uu, hd, rw, hs, he, ps, sk, ab, back, buf, rest, goal, ec)
            case False{}:
              ih => qs.plain(uu, hd, rw, hs, he, ps, sk, ab, back, buf, rest, goal, e34, e92, ec, ih)

# one character of a quoted segment
def qs.one(
  +uu: U32,
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>,
  +rest: String,
  +goal: T.Doc
) -> qs.Goal(uu, hd, rw, hs, he, ps, sk, ab, back, buf, rest, goal):
  qs.split(uu, U32.is_eq(uu, 34), U32.is_eq(uu, 92), Bool.or(U32.is_lt(uu, 32),
    U32.is_eq(uu, 127)), {==}, {==}, {==}, hd, rw, hs, he, ps, sk, ab, back, buf, rest, goal)

# every character of a name, as escs writes it, read from a quoted segment:
# the rest is read with the name's characters pushed, from wherever the last
# escape left back
def qs.escs(
  ss: String,
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>,
  +rest: String,
  +goal: T.Doc,
  ih: @bk: T.Lex -> {T.doc.read(rest, T.MScan{qs(hd, rw, hs, he, ps, sk, ab, bk, rev.onto(ss, buf))}) == goal : T.Doc}
) -> {T.doc.read(String.append(Laws.escs(ss), rest), T.MScan{qs(hd, rw, hs, he, ps, sk, ab, back, buf)}) == goal
  : T.Doc}:
  match ss:
    case SNil{}:
      ih(back)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+uu}:
          Equal.trans(T.Doc,
            T.doc.read(String.append(String.append(Laws.esc(Chr{uu}), Laws.escs(tt)), rest),
              T.MScan{qs(hd, rw, hs, he, ps, sk, ab, back, buf)}),
            T.doc.read(String.append(Laws.esc(Chr{uu}), String.append(Laws.escs(tt), rest)),
              T.MScan{qs(hd, rw, hs, he, ps, sk, ab, back, buf)}),
            goal,
            Equal.cong(String, T.Doc, xs => T.doc.read(xs, T.MScan{qs(hd, rw, hs, he, ps, sk, ab, back, buf)}),
              String.append(String.append(Laws.esc(Chr{uu}), Laws.escs(tt)), rest),
              String.append(Laws.esc(Chr{uu}), String.append(Laws.escs(tt), rest)),
              Eq.append_assoc(Laws.esc(Chr{uu}), Laws.escs(tt), rest)),
            qs.one(uu, hd, rw, hs, he, ps, sk, ab, back, buf, String.append(Laws.escs(tt), rest), goal)(
              bk => qs.escs(tt, hd, rw, hs, he, ps, sk, ab, bk, Chr{uu} <> buf, rest, goal, ih)))

# every character of a name, as escs writes it, then the closing quote and
# " = 1": the document is one pair named by the buffer, whatever the last
# escape left in back
def kq.body(
  +ss: String,
  +back: T.Lex,
  +buf: List<&2, Char>
) -> {T.doc.read(String.append(Laws.escs(ss), "\" = 1"), T.MScan{kq(back, buf)})
  == kq.doc(rev.onto(ss, buf)) : T.Doc}:
  qs.escs(ss, False{}, [], [], [], [], [], False{}, back, buf, "\" = 1",
    kq.doc(rev.onto(ss, buf)), _bk => {==})

# a buffer of a name's characters names the pair by the name
def kq.name(
  +ss: String
) -> {kq.doc(rev.onto(ss, [])) == T.Doc{"", [T.VPair{ss, T.VInt{T.Plus{}, "1"}}]} : T.Doc}:
  Equal.cong(String, T.Doc, nm => T.Doc{"", [T.VPair{nm, T.VInt{T.Plus{}, "1"}}]},
    T.buf.str.go(rev.onto(ss, []), ""), ss,
    Equal.trans(String, T.buf.str.go(rev.onto(ss, []), ""), String.append(ss, ""), ss,
      ml.rev(ss, [], ""), Eq.append_nil(ss)))

# a quoted key: key.basic is quotes around escs, and the scanner reads them
def kq.quoted(
  +ss: String
) -> {T.parse(String.append(T.key.basic(ss), " = 1"))
  == T.Doc{"", [T.VPair{ss, T.VInt{T.Plus{}, "1"}}]} : T.Doc}:
  Equal.trans(T.Doc,
    T.parse(String.append(T.key.basic(ss), " = 1")),
    T.parse(String.append("\"" ++ Laws.escs(ss) ++ "\"", " = 1")),
    T.Doc{"", [T.VPair{ss, T.VInt{T.Plus{}, "1"}}]},
    Equal.cong(String, T.Doc, xs => T.parse(String.append(xs, " = 1")), T.key.basic(ss),
      "\"" ++ Laws.escs(ss) ++ "\"", Laws.basic_escs(ss)),
    Equal.trans(T.Doc,
      T.doc.read(String.append(String.append(Laws.escs(ss), "\""), " = 1"),
        T.MScan{kq(T.LTop{}, [])}),
      T.doc.read(String.append(Laws.escs(ss), "\" = 1"), T.MScan{kq(T.LTop{}, [])}),
      T.Doc{"", [T.VPair{ss, T.VInt{T.Plus{}, "1"}}]},
      Equal.cong(String, T.Doc, xs => T.doc.read(xs, T.MScan{kq(T.LTop{}, [])}),
        String.append(String.append(Laws.escs(ss), "\""), " = 1"),
        String.append(Laws.escs(ss), "\" = 1"),
        Eq.append_assoc(Laws.escs(ss), "\"", " = 1")),
      Equal.trans(T.Doc,
        T.doc.read(String.append(Laws.escs(ss), "\" = 1"), T.MScan{kq(T.LTop{}, [])}),
        kq.doc(rev.onto(ss, [])),
        T.Doc{"", [T.VPair{ss, T.VInt{T.Plus{}, "1"}}]},
        kq.body(ss, T.LTop{}, []),
        kq.name(ss))))

# a space ends a nonempty bare key, and " = 1" is read to the end
def key.sp(
  +bb: List<&2, Char>,
  full: {List.is_empty(&2, Char, bb) == False{} : Bool}
) -> {T.doc.read(" = 1", T.MScan{ky(bb)}) == kq.doc(bb) : T.Doc}:
  Equal.trans(T.Doc,
    T.doc.read("= 1", T.MScan{T.read.once2(T.lex.key.end.go(List.is_empty(&2, Char, bb),
      ky(bb), T.LAfter{}))}),
    T.doc.read("= 1", T.MScan{T.read.once2(T.lex.key.end.go(False{}, ky(bb), T.LAfter{}))}),
    kq.doc(bb),
    Equal.cong(Bool, T.Doc,
      bt => T.doc.read("= 1", T.MScan{T.read.once2(T.lex.key.end.go(bt, ky(bb), T.LAfter{}))}),
      List.is_empty(&2, Char, bb), False{}, full),
    {==})

# a bare key: its characters are read on the key's fast path, as for
# empty_basic_at_end
def kq.bare(
  +xx: U32,
  +tt: String,
  +ee: {T.bare.all.step(T.bare.at(Chr{xx}), _u => T.bare.all(String.to_list(tt))) == True{} : Bool}
) -> {T.parse(String.append(SCon{Chr{xx}, tt}, " = 1"))
  == T.Doc{"", [T.VPair{SCon{Chr{xx}, tt}, T.VInt{T.Plus{}, "1"}}]} : T.Doc}:
  Equal.trans(T.Doc,
    T.doc.read(String.append(tt, " = 1"), T.doc.scan(T.st.start(), Chr{xx})),
    T.doc.read(String.append(tt, " = 1"), T.MScan{ky([Chr{xx}])}),
    T.Doc{"", [T.VPair{SCon{Chr{xx}, tt}, T.VInt{T.Plus{}, "1"}}]},
    Equal.cong(T.Mode, T.Doc, md => T.doc.read(String.append(tt, " = 1"), md),
      T.doc.scan(T.st.start(), Chr{xx}), T.MScan{ky([Chr{xx}])},
      key.first(xx, ball.head(T.bare.at(Chr{xx}), String.to_list(tt), ee))),
    Equal.trans(T.Doc,
      T.doc.read(String.append(tt, " = 1"), T.MScan{ky([Chr{xx}])}),
      T.doc.read(" = 1", T.MScan{ky(rev.onto(tt, [Chr{xx}]))}),
      T.Doc{"", [T.VPair{SCon{Chr{xx}, tt}, T.VInt{T.Plus{}, "1"}}]},
      key.body(tt, " = 1", [Chr{xx}], ball.tail(T.bare.at(Chr{xx}), String.to_list(tt), ee)),
      Equal.trans(T.Doc,
        T.doc.read(" = 1", T.MScan{ky(rev.onto(tt, [Chr{xx}]))}),
        kq.doc(rev.onto(tt, [Chr{xx}])),
        T.Doc{"", [T.VPair{SCon{Chr{xx}, tt}, T.VInt{T.Plus{}, "1"}}]},
        key.sp(rev.onto(tt, [Chr{xx}]), rev.full(tt, Chr{xx}, [])),
        kq.name(SCon{Chr{xx}, tt}))))

# bare or quoted, as key picks
def kq.law(
  bb: Bool,
  +ss: String,
  eb: {T.bare(ss) == bb : Bool}
) -> {T.parse(String.append(T.key.go(bb, ss), " = 1"))
  == T.Doc{"", [T.VPair{ss, T.VInt{T.Plus{}, "1"}}]} : T.Doc}:
  match bb:
    case False{}:
      kq.quoted(ss)
    case True{}:
      match ss:
        case SNil{}:
          Eq.bit.absurd(&2, {T.parse(String.append(SNil{}, " = 1"))
            == T.Doc{"", [T.VPair{SNil{}, T.VInt{T.Plus{}, "1"}}]} : T.Doc}, eb)
        case SCon{hh, +tt}:
          match hh:
            case Chr{+xx}:
              kq.bare(xx, tt, eb)

def Laws.key_reads_back(s):
  kq.law(T.bare(s), s, {==})

# TOML-RT-1 for a document of one pair: a bare key and a string render writes
# with no escape. The key is read as for key_reads_back; the string opens a
# span on its first character, each later one adds one to the span's U32
# count, and the closing quote stores the span. The span then reads as the
# string because its count is the string's length, which needs the count not
# to wrap.

# the count a span holds after these characters, from n
def addn(ss: String, nn: U32) -> U32:
  match ss:
    case SNil{}:
      nn
    case SCon{_hh, tt}:
      addn(tt, U32.add(nn, 1))

# a Nat count after these characters, from n
def plus(ss: String, nn: Nat) -> Nat:
  match ss:
    case SNil{}:
      nn
    case SCon{_hh, tt}:
      plus(tt, 1n+nn)

# a count that does not wrap counts the characters
def cnt(
  ss: String,
  +nn: U32,
  +ee: {Laws.counts(ss, nn) == True{} : Bool}
) -> {U32.to_nat(addn(ss, nn)) == plus(ss, U32.to_nat(nn)) : Nat}:
  match ss:
    case SNil{}:
      {==}
    case SCon{_hh, +tt}:
      Equal.trans(Nat, U32.to_nat(addn(tt, U32.add(nn, 1))), plus(tt, U32.to_nat(U32.add(nn, 1))),
        plus(tt, 1n+U32.to_nat(nn)),
        cnt(tt, U32.add(nn, 1), Eq.and.right(Bool.not(U32.is_zero(U32.add(nn, 1))),
          Laws.counts(tt, U32.add(nn, 1)), ee)),
        Equal.cong(Nat, Nat, mm => plus(tt, mm), U32.to_nat(U32.add(nn, 1)), 1n+U32.to_nat(nn),
          Eq.inc.nat(nn, Eq.not.true(U32.is_zero(U32.add(nn, 1)),
            Eq.and.left(Bool.not(U32.is_zero(U32.add(nn, 1))), Laws.counts(tt, U32.add(nn, 1)),
              ee)))))

# the first n characters of a text
def take(ss: String, nn: Nat) -> String:
  match ss nn:
    case SNil{} _nn:
      SNil{}
    case SCon{_hh, _tt} 0n:
      SNil{}
    case SCon{hh, tt} 1n+pp:
      SCon{hh, take(tt, pp)}

# span.str of no characters, whatever the count
def sp.nil(nn: U32, bz: Bool) -> {T.span.str(SNil{}, nn, bz) == take(SNil{}, U32.to_nat(nn)) : String}:
  match bz:
    case True{}:
      {==}
    case False{}:
      {==}

# span.str of a character and the rest, once the zero test's answer is named
def sp.cons(
  +hd: Char,
  +tl: String,
  +nn: U32,
  bz: Bool,
  ez: {U32.is_zero(nn) == bz : Bool},
  ih: {T.span.str(tl, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1))) == take(tl, U32.to_nat(U32.sub(nn, 1))) : String}
) -> {T.span.str(SCon{hd, tl}, nn, bz) == take(SCon{hd, tl}, U32.to_nat(nn)) : String}:
  match bz:
    case True{}:
      e0 = Equal.cong(Char, U32, cc => Char.to_u32(cc), Chr{nn}, Chr{0}, Eq.u32_eq(nn, 0, ez))
      %Equal.sym(U32, nn, 0, e0) : {T.span.str(SCon{hd, tl}, nn, True{}) == take(SCon{hd, tl},
        U32.to_nat(_)) : String}
      {==}
    case False{}:
      en = Equal.sym(Nat, U32.to_nat(nn), 1n+U32.to_nat(U32.sub(nn, 1)), Eq.u32_dec_nat(nn, ez))
      %en : {SCon{hd, T.span.str(tl, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)))}
        == take(SCon{hd, tl}, _) : String}
      Equal.cong(String, String, xs => SCon{hd, xs},
        T.span.str(tl, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1))),
        take(tl, U32.to_nat(U32.sub(nn, 1))), ih)

# a span's characters are the first n characters of its source
def sp.take(
  src: String,
  +nn: U32
) -> {T.span.str(src, nn, U32.is_zero(nn)) == take(src, U32.to_nat(nn)) : String}:
  match src:
    case SNil{}:
      sp.nil(nn, U32.is_zero(nn))
    case SCon{+hd, +tl}:
      sp.cons(hd, tl, nn, U32.is_zero(nn), {==}, sp.take(tl, U32.sub(nn, 1)))

# a count one further on
def plus.succ(ss: String, nn: Nat) -> {plus(ss, 1n+nn) == 1n+plus(ss, nn) : Nat}:
  match ss:
    case SNil{}:
      {==}
    case SCon{_hh, tt}:
      plus.succ(tt, 1n+nn)

# taking a text's count of characters from the text and more takes the text
def take.app(
  ss: String,
  +xs: String,
  +kk: Nat
) -> {take(String.append(ss, xs), plus(ss, kk)) == String.append(ss, take(xs, kk)) : String}:
  match ss:
    case SNil{}:
      {==}
    case SCon{+hh, +tt}:
      %Equal.sym(Nat, plus(tt, 1n+kk), 1n+plus(tt, kk), plus.succ(tt, kk)) :
        {take(SCon{hh, String.append(tt, xs)}, _) == SCon{hh, String.append(tt, take(xs, kk))}
          : String}
      Equal.cong(String, String, ys => SCon{hh, ys}, take(String.append(tt, xs), plus(tt, kk)),
        String.append(tt, take(xs, kk)), take.app(tt, xs, kk))

# the span parse stores for a string whose count does not wrap is the string
def sp.whole(
  +c0: Char,
  +ps: String,
  +es: {Laws.counts(ps, U32.add(0, 1)) == True{} : Bool}
) -> {T.span.str(SCon{c0, String.append(ps, "\"\n")}, addn(ps, U32.add(0, 1)),
  U32.is_zero(addn(ps, U32.add(0, 1)))) == SCon{c0, ps} : String}:
  Equal.trans(String,
    T.span.str(SCon{c0, String.append(ps, "\"\n")}, addn(ps, U32.add(0, 1)),
      U32.is_zero(addn(ps, U32.add(0, 1)))),
    take(SCon{c0, String.append(ps, "\"\n")}, U32.to_nat(addn(ps, U32.add(0, 1)))),
    SCon{c0, ps},
    sp.take(SCon{c0, String.append(ps, "\"\n")}, addn(ps, U32.add(0, 1))),
    Equal.trans(String,
      take(SCon{c0, String.append(ps, "\"\n")}, U32.to_nat(addn(ps, U32.add(0, 1)))),
      take(String.append(SCon{c0, ps}, "\"\n"), plus(SCon{c0, ps}, 0n)),
      SCon{c0, ps},
      Equal.cong(Nat, String, mm => take(SCon{c0, String.append(ps, "\"\n")}, mm),
        U32.to_nat(addn(ps, U32.add(0, 1))), plus(ps, 1n), cnt(ps, U32.add(0, 1), es)),
      Equal.trans(String,
        take(String.append(SCon{c0, ps}, "\"\n"), plus(SCon{c0, ps}, 0n)),
        String.append(SCon{c0, ps}, ""),
        SCon{c0, ps},
        take.app(SCon{c0, ps}, "\"\n", 0n),
        Eq.append_nil(SCon{c0, ps}))))

# What a plain character is not.

# no control
def pc.ctl(
  +uu: U32,
  hp: {Laws.plain.char(Chr{uu}) == True{} : Bool}
) -> {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool}:
  Eq.or.left_false(Laws.is_ctl(Chr{uu}), Bool.or(U32.is_eq(uu, 34), U32.is_eq(uu, 92)),
    Eq.not.true(Bool.or(Laws.is_ctl(Chr{uu}), Bool.or(U32.is_eq(uu, 34), U32.is_eq(uu, 92))), hp))

# no quotation mark or backslash
def pc.qb(
  +uu: U32,
  hp: {Laws.plain.char(Chr{uu}) == True{} : Bool}
) -> {Bool.or(U32.is_eq(uu, 34), U32.is_eq(uu, 92)) == False{} : Bool}:
  Eq.or.right_false(Laws.is_ctl(Chr{uu}), Bool.or(U32.is_eq(uu, 34), U32.is_eq(uu, 92)),
    Eq.not.true(Bool.or(Laws.is_ctl(Chr{uu}), Bool.or(U32.is_eq(uu, 34), U32.is_eq(uu, 92))), hp))

# a plain character is written as itself
def esc.pl(
  +uu: U32,
  +hp: {Laws.plain.char(Chr{uu}) == True{} : Bool}
) -> {Laws.esc(Chr{uu}) == String.from_list([Chr{uu}]) : String}:
  +ec = {pc.ctl(uu, hp) : {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool}}
  +eqb = {pc.qb(uu, hp) : {Bool.or(U32.is_eq(uu, 34), U32.is_eq(uu, 92)) == False{} : Bool}}
  ek = cls.plain(uu, ctl.off(uu, 8, ec, {==}), ctl.off(uu, 9, ec, {==}), ctl.off(uu, 10, ec, {==}),
    ctl.off(uu, 12, ec, {==}), ctl.off(uu, 13, ec, {==}),
    Eq.or.left_false(U32.is_eq(uu, 34), U32.is_eq(uu, 92), eqb),
    Eq.or.right_false(U32.is_eq(uu, 34), U32.is_eq(uu, 92), eqb), ec)
  %Equal.sym(T.BK, T.basic.cls(uu), T.BKCh{}, ek) :
    {String.from_list(List.reverse(&2, Char, T.basic.disp(_, Chr{uu}, uu, [])))
      == String.from_list([Chr{uu}]) : String}
  {==}

# a plain text is written as itself
def escs.pl(
  ss: String,
  +ee: {Laws.plain.text(ss) == True{} : Bool}
) -> {Laws.escs(ss) == ss : String}:
  match ss:
    case SNil{}:
      {==}
    case SCon{hh, +tt}:
      match hh:
        case Chr{+uu}:
          Equal.trans(String, String.append(Laws.esc(Chr{uu}), Laws.escs(tt)),
            String.append(String.from_list([Chr{uu}]), Laws.escs(tt)), SCon{Chr{uu}, tt},
            Equal.cong(String, String, xs => String.append(xs, Laws.escs(tt)), Laws.esc(Chr{uu}),
              String.from_list([Chr{uu}]),
              esc.pl(uu, Eq.and.left(Laws.plain.char(Chr{uu}), Laws.plain.text(tt), ee))),
            Equal.cong(String, String, xs => SCon{Chr{uu}, xs}, Laws.escs(tt), tt,
              escs.pl(tt, Eq.and.right(Laws.plain.char(Chr{uu}), Laws.plain.text(tt), ee))))

# The span. vo is the scanner at the opening quote of the key's value; ve is
# it inside the span, cut being the text from the string's first character.

# the scanner just past the opening quote of a root key's string
def vo(name: String) -> T.Mode:
  T.MOpen{True{}, '"', T.QBasic{}, "", [], [], [], [name], [], T.LTop{}, [], 0, 0, False{}}

# the scanner inside the span of a root key's string, n characters in
def ve(cut: String, nn: U32, name: String) -> T.Mode:
  T.MEat{True{}, '"', cut, nn, "", [], [], [], [name], T.QBasic{}, [], 0, 0, False{}}

# the first character: no control, so the span starts
def op.ok(
  badc: Bool,
  +uu: U32,
  +tail: String,
  +name: String,
  hc: {badc == False{} : Bool}
) -> {T.doc.open.ok(T.str.bad.go(badc, U32.is_eq(uu, 9), Bool.or(U32.is_eq(uu, 10),
  U32.is_eq(uu, 13)), False{}), True{}, '"', T.QBasic{}, "", [], [], [], [name], [], T.LTop{},
  [], 0, 0, False{}, Chr{uu}, tail) == ve(SCon{Chr{uu}, tail}, 1, name) : T.Mode}:
  match badc:
    case False{}:
      {==}
    case True{}:
      Eq.bit.absurd2(&2, {T.doc.open.ok(T.str.bad.go(True{}, U32.is_eq(uu, 9),
        Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)), False{}), True{}, '"', T.QBasic{}, "", [],
        [], [], [name], [], T.LTop{}, [], 0, 0, False{}, Chr{uu}, tail)
        == ve(SCon{Chr{uu}, tail}, 1, name) : T.Mode}, hc)

# no backslash
def op.bs(
  bs: Bool,
  +uu: U32,
  +tail: String,
  +name: String,
  hb: {bs == False{} : Bool},
  hc: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool}
) -> {T.doc.open.bs(bs, '"', T.QBasic{}, "", [], [], [], [name], [], T.LTop{}, [], 0, 0, False{},
  Chr{uu}, tail) == ve(SCon{Chr{uu}, tail}, 1, name) : T.Mode}:
  match bs:
    case False{}:
      op.ok(Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), uu, tail, name, hc)
    case True{}:
      Eq.bit.absurd2(&2, {T.doc.open.bs(True{}, '"', T.QBasic{}, "", [], [], [], [name], [],
        T.LTop{}, [], 0, 0, False{}, Chr{uu}, tail) == ve(SCon{Chr{uu}, tail}, 1, name) : T.Mode},
        hb)

# no quotation mark
def op.q(
  same: Bool,
  +uu: U32,
  +tail: String,
  +name: String,
  hq: {same == False{} : Bool},
  hb: {U32.is_eq(uu, 92) == False{} : Bool},
  hc: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool}
) -> {T.doc.open.q(same, True{}, '"', T.QBasic{}, "", [], [], [], [name], [], T.LTop{}, [], 0, 0,
  False{}, Chr{uu}, tail) == ve(SCon{Chr{uu}, tail}, 1, name) : T.Mode}:
  match same:
    case False{}:
      op.bs(U32.is_eq(uu, 92), uu, tail, name, hb, hc)
    case True{}:
      Eq.bit.absurd2(&2, {T.doc.open.q(True{}, True{}, '"', T.QBasic{}, "", [], [], [], [name], [],
        T.LTop{}, [], 0, 0, False{}, Chr{uu}, tail) == ve(SCon{Chr{uu}, tail}, 1, name) : T.Mode},
        hq)

# a plain first character opens the span
def op.one(
  +uu: U32,
  +tail: String,
  +name: String,
  +hp: {Laws.plain.char(Chr{uu}) == True{} : Bool}
) -> {T.doc.read(SCon{Chr{uu}, tail}, vo(name)) == T.doc.read(tail, ve(SCon{Chr{uu}, tail}, 1,
  name)) : T.Doc}:
  +eqb = {pc.qb(uu, hp) : {Bool.or(U32.is_eq(uu, 34), U32.is_eq(uu, 92)) == False{} : Bool}}
  Equal.cong(T.Mode, T.Doc, md => T.doc.read(tail, md),
    T.doc.open(True{}, '"', T.QBasic{}, "", [], [], [], [name], [], T.LTop{}, [], 0, 0, False{},
      Chr{uu}, tail),
    ve(SCon{Chr{uu}, tail}, 1, name),
    op.q(U32.is_eq(uu, 34), uu, tail, name,
      Eq.or.left_false(U32.is_eq(uu, 34), U32.is_eq(uu, 92), eqb),
      Eq.or.right_false(U32.is_eq(uu, 34), U32.is_eq(uu, 92), eqb), pc.ctl(uu, hp)))

# a later character: no control, so the span grows
def ef.ctl(
  ctl: Bool,
  +uu: U32,
  +cut: String,
  +nn: U32,
  +name: String,
  hc: {ctl == False{} : Bool}
) -> {T.eat.ctrl(T.str.bad.go(ctl, U32.is_eq(uu, 9), Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)),
  False{}), True{}, '"', Chr{uu}, cut, nn, "", [], [], [], [name], T.QBasic{}, [], 0, 0, False{})
  == ve(cut, U32.add(nn, 1), name) : T.Mode}:
  match ctl:
    case False{}:
      {==}
    case True{}:
      Eq.bit.absurd2(&2, {T.eat.ctrl(T.str.bad.go(True{}, U32.is_eq(uu, 9),
        Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)), False{}), True{}, '"', Chr{uu}, cut, nn, "",
        [], [], [], [name], T.QBasic{}, [], 0, 0, False{}) == ve(cut, U32.add(nn, 1), name)
        : T.Mode}, hc)

# no backslash
def ef.bs(
  bs: Bool,
  +uu: U32,
  +cut: String,
  +nn: U32,
  +name: String,
  hb: {bs == False{} : Bool},
  hc: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool}
) -> {T.eat.bs(bs, True{}, '"', Chr{uu}, cut, nn, "", [], [], [], [name], T.QBasic{}, [], 0, 0,
  False{}) == ve(cut, U32.add(nn, 1), name) : T.Mode}:
  match bs:
    case False{}:
      ef.ctl(Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), uu, cut, nn, name, hc)
    case True{}:
      Eq.bit.absurd2(&2, {T.eat.bs(True{}, True{}, '"', Chr{uu}, cut, nn, "", [], [], [], [name],
        T.QBasic{}, [], 0, 0, False{}) == ve(cut, U32.add(nn, 1), name) : T.Mode}, hb)

# no quotation mark
def ef.q(
  quote: Bool,
  +uu: U32,
  +cut: String,
  +nn: U32,
  +name: String,
  hq: {quote == False{} : Bool},
  hb: {U32.is_eq(uu, 92) == False{} : Bool},
  hc: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool}
) -> {T.eat.feed.q(quote, True{}, '"', Chr{uu}, cut, nn, "", [], [], [], [name], T.QBasic{}, [], 0,
  0, False{}) == ve(cut, U32.add(nn, 1), name) : T.Mode}:
  match quote:
    case False{}:
      ef.bs(U32.is_eq(uu, 92), uu, cut, nn, name, hb, hc)
    case True{}:
      Eq.bit.absurd2(&2, {T.eat.feed.q(True{}, True{}, '"', Chr{uu}, cut, nn, "", [], [], [],
        [name], T.QBasic{}, [], 0, 0, False{}) == ve(cut, U32.add(nn, 1), name) : T.Mode}, hq)

# the plain characters of a string grow the span by one each
def ef.run(
  ps: String,
  +rest: String,
  +cut: String,
  +nn: U32,
  +name: String,
  +ee: {Laws.plain.text(ps) == True{} : Bool}
) -> {T.doc.read(String.append(ps, rest), ve(cut, nn, name))
  == T.doc.read(rest, ve(cut, addn(ps, nn), name)) : T.Doc}:
  match ps:
    case SNil{}:
      {==}
    case SCon{hh, +tt}:
      match hh:
        case Chr{+uu}:
          +hp = {Eq.and.left(Laws.plain.char(Chr{uu}), Laws.plain.text(tt), ee)
            : {Laws.plain.char(Chr{uu}) == True{} : Bool}}
          +eqb = {pc.qb(uu, hp) : {Bool.or(U32.is_eq(uu, 34), U32.is_eq(uu, 92)) == False{} : Bool}}
          Equal.trans(T.Doc,
            T.doc.read(String.append(tt, rest), T.eat.feed(True{}, '"', cut, nn, "", [], [], [],
              [name], T.QBasic{}, [], 0, 0, False{}, Chr{uu})),
            T.doc.read(String.append(tt, rest), ve(cut, U32.add(nn, 1), name)),
            T.doc.read(rest, ve(cut, addn(tt, U32.add(nn, 1)), name)),
            Equal.cong(T.Mode, T.Doc, md => T.doc.read(String.append(tt, rest), md),
              T.eat.feed(True{}, '"', cut, nn, "", [], [], [], [name], T.QBasic{}, [], 0, 0,
                False{}, Chr{uu}),
              ve(cut, U32.add(nn, 1), name),
              ef.q(U32.is_eq(uu, 34), uu, cut, nn, name,
                Eq.or.left_false(U32.is_eq(uu, 34), U32.is_eq(uu, 92), eqb),
                Eq.or.right_false(U32.is_eq(uu, 34), U32.is_eq(uu, 92), eqb), pc.ctl(uu, hp))),
            ef.run(tt, rest, cut, U32.add(nn, 1), name,
              Eq.and.right(Laws.plain.char(Chr{uu}), Laws.plain.text(tt), ee)))

# The key. A space ends a nonempty bare key, and " = " and the opening quote
# bring the scanner to vo
def kv.eq(
  +bb: List<&2, Char>,
  full: {List.is_empty(&2, Char, bb) == False{} : Bool},
  +vv: String
) -> {T.doc.read(SCon{' ', SCon{'=', SCon{' ', SCon{'"', vv}}}}, T.MScan{ky(bb)})
  == T.doc.read(vv, vo(T.buf.str.go(bb, ""))) : T.Doc}:
  Equal.trans(T.Doc,
    T.doc.read(SCon{'=', SCon{' ', SCon{'"', vv}}}, T.MScan{T.read.once2(T.lex.key.end.go(
      List.is_empty(&2, Char, bb), ky(bb), T.LAfter{}))}),
    T.doc.read(SCon{'=', SCon{' ', SCon{'"', vv}}}, T.MScan{T.read.once2(T.lex.key.end.go(
      False{}, ky(bb), T.LAfter{}))}),
    T.doc.read(vv, vo(T.buf.str.go(bb, ""))),
    Equal.cong(Bool, T.Doc,
      bt => T.doc.read(SCon{'=', SCon{' ', SCon{'"', vv}}}, T.MScan{T.read.once2(
        T.lex.key.end.go(bt, ky(bb), T.LAfter{}))}),
      List.is_empty(&2, Char, bb), False{}, full),
    {==})

# a bare key, then " = " and a quote: the scanner at vo, named by the key
def kv.key(
  +xx: U32,
  +tt: String,
  +vv: String,
  +ee: {T.bare.all.step(T.bare.at(Chr{xx}), _u => T.bare.all(String.to_list(tt))) == True{} : Bool}
) -> {T.parse(String.append(SCon{Chr{xx}, tt}, SCon{' ', SCon{'=', SCon{' ', SCon{'"', vv}}}}))
  == T.doc.read(vv, vo(SCon{Chr{xx}, tt})) : T.Doc}:
  Equal.trans(T.Doc,
    T.doc.read(String.append(tt, SCon{' ', SCon{'=', SCon{' ', SCon{'"', vv}}}}),
      T.doc.scan(T.st.start(), Chr{xx})),
    T.doc.read(String.append(tt, SCon{' ', SCon{'=', SCon{' ', SCon{'"', vv}}}}),
      T.MScan{ky([Chr{xx}])}),
    T.doc.read(vv, vo(SCon{Chr{xx}, tt})),
    Equal.cong(T.Mode, T.Doc,
      md => T.doc.read(String.append(tt, SCon{' ', SCon{'=', SCon{' ', SCon{'"', vv}}}}), md),
      T.doc.scan(T.st.start(), Chr{xx}), T.MScan{ky([Chr{xx}])},
      key.first(xx, ball.head(T.bare.at(Chr{xx}), String.to_list(tt), ee))),
    Equal.trans(T.Doc,
      T.doc.read(String.append(tt, SCon{' ', SCon{'=', SCon{' ', SCon{'"', vv}}}}),
        T.MScan{ky([Chr{xx}])}),
      T.doc.read(SCon{' ', SCon{'=', SCon{' ', SCon{'"', vv}}}},
        T.MScan{ky(rev.onto(tt, [Chr{xx}]))}),
      T.doc.read(vv, vo(SCon{Chr{xx}, tt})),
      key.body(tt, SCon{' ', SCon{'=', SCon{' ', SCon{'"', vv}}}}, [Chr{xx}],
        ball.tail(T.bare.at(Chr{xx}), String.to_list(tt), ee)),
      Equal.trans(T.Doc,
        T.doc.read(SCon{' ', SCon{'=', SCon{' ', SCon{'"', vv}}}},
          T.MScan{ky(rev.onto(tt, [Chr{xx}]))}),
        T.doc.read(vv, vo(T.buf.str.go(rev.onto(tt, [Chr{xx}]), ""))),
        T.doc.read(vv, vo(SCon{Chr{xx}, tt})),
        kv.eq(rev.onto(tt, [Chr{xx}]), rev.full(tt, Chr{xx}, []), vv),
        Equal.cong(String, T.Doc, nm => T.doc.read(vv, vo(nm)),
          T.buf.str.go(rev.onto(tt, [Chr{xx}]), ""), SCon{Chr{xx}, tt},
          Equal.trans(String, T.buf.str.go(rev.onto(tt, [Chr{xx}]), ""),
            SCon{Chr{xx}, String.append(tt, "")}, SCon{Chr{xx}, tt},
            ml.rev(tt, [Chr{xx}], ""),
            Equal.cong(String, String, ss => SCon{Chr{xx}, ss}, String.append(tt, ""), tt,
              Eq.append_nil(tt)))))))

# the rendered text of the pair: the key, " = ", the string in quotes, and a
# newline
def rp.text(
  +e: String,
  +k: String,
  ek: {T.bare(k) == True{} : Bool},
  +s: String,
  ep: {Laws.plain.text(s) == True{} : Bool}
) -> {T.render(T.Doc{e, [T.VPair{k, T.VStr{s}}]})
  == String.append(k, SCon{' ', SCon{'=', SCon{' ', SCon{'"', String.append(s, "\"\n")}}}})
  : String}:
  Equal.trans(String,
    T.render(T.Doc{e, [T.VPair{k, T.VStr{s}}]}),
    T.key(k) ++ " = " ++ T.key.basic(s) ++ "\n" ++ T.render(T.Doc{e, []}),
    String.append(k, SCon{' ', SCon{'=', SCon{' ', SCon{'"', String.append(s, "\"\n")}}}}),
    Laws.render_string(e, k, T.VStr{s}, [], {==}),
    Equal.trans(String,
      T.key(k) ++ " = " ++ T.key.basic(s) ++ "\n" ++ T.render(T.Doc{e, []}),
      k ++ " = " ++ T.key.basic(s) ++ "\n",
      String.append(k, SCon{' ', SCon{'=', SCon{' ', SCon{'"', String.append(s, "\"\n")}}}}),
      Equal.cong(String, String, kk => kk ++ " = " ++ T.key.basic(s) ++ "\n", T.key(k), k,
        Laws.key_is_bare_when_it_can(k, Equal.sym(Bool, T.bare(k), True{}, ek))),
      Equal.trans(String,
        k ++ " = " ++ T.key.basic(s) ++ "\n",
        k ++ " = " ++ ("\"" ++ Laws.escs(s) ++ "\"") ++ "\n",
        String.append(k, SCon{' ', SCon{'=', SCon{' ', SCon{'"', String.append(s, "\"\n")}}}}),
        Equal.cong(String, String, bb => k ++ " = " ++ bb ++ "\n", T.key.basic(s),
          "\"" ++ Laws.escs(s) ++ "\"", Laws.basic_escs(s)),
        Equal.trans(String,
          k ++ " = " ++ ("\"" ++ Laws.escs(s) ++ "\"") ++ "\n",
          k ++ " = " ++ ("\"" ++ s ++ "\"") ++ "\n",
          String.append(k, SCon{' ', SCon{'=', SCon{' ', SCon{'"', String.append(s, "\"\n")}}}}),
          Equal.cong(String, String, bb => k ++ " = " ++ ("\"" ++ bb ++ "\"") ++ "\n",
            Laws.escs(s), s, escs.pl(s, ep)),
          Equal.cong(String, String,
            bb => String.append(k, SCon{' ', SCon{'=', SCon{' ', SCon{'"', bb}}}}),
            String.append(String.append(s, "\""), "\n"), String.append(s, "\"\n"),
            Eq.append_assoc(s, "\"", "\n"))))))

# a row whose owned form is a string pair is the same as that pair, both ways
def rp.same(
  +e: String,
  +k: String,
  +vv: T.Val,
  +s: String,
  +ho: {Laws.own.rows([T.VPair{k, vv}]) == [T.VPair{k, T.VStr{s}}] : List<&2, T.Val>}
) -> {Laws.same(T.Doc{"", [T.VPair{k, vv}]}, T.Doc{e, [T.VPair{k, T.VStr{s}}]}) == True{} : Bool}:
  +self = {pair.self.tt(k, T.VStr{s}, ww => Laws.same.atom(T.VStr{s}, ww), Eq.string_eq_self(s))
    : {Laws.same.go([T.VPair{k, T.VStr{s}}], [T.VPair{k, T.VStr{s}}]) == True{} : Bool}}
  and.tt(Laws.same.go([T.VPair{k, vv}], [T.VPair{k, T.VStr{s}}]),
    Laws.same.go([T.VPair{k, T.VStr{s}}], [T.VPair{k, vv}]),
    Equal.trans(Bool, Laws.same.go([T.VPair{k, vv}], [T.VPair{k, T.VStr{s}}]),
      Laws.same.go(Laws.own.rows([T.VPair{k, vv}]), [T.VPair{k, T.VStr{s}}]), True{},
      Equal.sym(Bool, Laws.same.go(Laws.own.rows([T.VPair{k, vv}]), [T.VPair{k, T.VStr{s}}]),
        Laws.same.go([T.VPair{k, vv}], [T.VPair{k, T.VStr{s}}]),
        own.l([T.VPair{k, vv}], [T.VPair{k, T.VStr{s}}])),
      Equal.trans(Bool, Laws.same.go(Laws.own.rows([T.VPair{k, vv}]), [T.VPair{k, T.VStr{s}}]),
        Laws.same.go([T.VPair{k, T.VStr{s}}], [T.VPair{k, T.VStr{s}}]), True{},
        Equal.cong(List<&2, T.Val>, Bool, xs => Laws.same.go(xs, [T.VPair{k, T.VStr{s}}]),
          Laws.own.rows([T.VPair{k, vv}]), [T.VPair{k, T.VStr{s}}], ho),
        self)),
    Equal.trans(Bool, Laws.same.go([T.VPair{k, T.VStr{s}}], [T.VPair{k, vv}]),
      Laws.same.go([T.VPair{k, T.VStr{s}}], Laws.own.rows([T.VPair{k, vv}])), True{},
      Equal.sym(Bool, Laws.same.go([T.VPair{k, T.VStr{s}}], Laws.own.rows([T.VPair{k, vv}])),
        Laws.same.go([T.VPair{k, T.VStr{s}}], [T.VPair{k, vv}]),
        own.r([T.VPair{k, T.VStr{s}}], [T.VPair{k, vv}])),
      Equal.trans(Bool, Laws.same.go([T.VPair{k, T.VStr{s}}], Laws.own.rows([T.VPair{k, vv}])),
        Laws.same.go([T.VPair{k, T.VStr{s}}], [T.VPair{k, T.VStr{s}}]), True{},
        Equal.cong(List<&2, T.Val>, Bool, xs => Laws.same.go([T.VPair{k, T.VStr{s}}], xs),
          Laws.own.rows([T.VPair{k, vv}]), [T.VPair{k, T.VStr{s}}], ho),
        self)))

# the parsed value: the empty string, or a span of the text from the string's
# first character
def rp.val(ss: String) -> T.Val:
  match ss:
    case SNil{}:
      T.VStr{""}
    case SCon{c0, +ps}:
      T.VSpan{SCon{c0, String.append(ps, "\"\n")}, addn(ps, U32.add(0, 1))}

# the string and the newline after the opening quote read to one pair
def rp.read(
  ss: String,
  +name: String,
  +ep: {Laws.plain.text(ss) == True{} : Bool}
) -> {T.doc.read(String.append(ss, "\"\n"), vo(name)) == T.Doc{"", [T.VPair{name, rp.val(ss)}]}
  : T.Doc}:
  match ss:
    case SNil{}:
      {==}
    case SCon{hh, +ps}:
      match hh:
        case Chr{+uu}:
          Equal.trans(T.Doc,
            T.doc.read(SCon{Chr{uu}, String.append(ps, "\"\n")}, vo(name)),
            T.doc.read(String.append(ps, "\"\n"), ve(SCon{Chr{uu}, String.append(ps, "\"\n")}, 1,
              name)),
            T.Doc{"", [T.VPair{name, rp.val(SCon{Chr{uu}, ps})}]},
            op.one(uu, String.append(ps, "\"\n"), name,
              Eq.and.left(Laws.plain.char(Chr{uu}), Laws.plain.text(ps), ep)),
            Equal.trans(T.Doc,
              T.doc.read(String.append(ps, "\"\n"), ve(SCon{Chr{uu}, String.append(ps, "\"\n")}, 1,
                name)),
              T.doc.read("\"\n", ve(SCon{Chr{uu}, String.append(ps, "\"\n")}, addn(ps, 1), name)),
              T.Doc{"", [T.VPair{name, rp.val(SCon{Chr{uu}, ps})}]},
              ef.run(ps, "\"\n", SCon{Chr{uu}, String.append(ps, "\"\n")}, 1, name,
                Eq.and.right(Laws.plain.char(Chr{uu}), Laws.plain.text(ps), ep)),
              {==}))

# the owned form of the parsed pair is the pair
def rp.own(
  ss: String,
  +name: String,
  es: {Laws.short(ss) == True{} : Bool}
) -> {Laws.own.rows([T.VPair{name, rp.val(ss)}]) == [T.VPair{name, T.VStr{ss}}]
  : List<&2, T.Val>}:
  match ss:
    case SNil{}:
      {==}
    case SCon{+c0, +ps}:
      Equal.cong(String, List<&2, T.Val>, xs => [T.VPair{name, T.VStr{xs}}],
        T.span.str(SCon{c0, String.append(ps, "\"\n")}, addn(ps, U32.add(0, 1)),
          U32.is_zero(addn(ps, U32.add(0, 1)))),
        SCon{c0, ps},
        sp.whole(c0, ps, Eq.and.right(Bool.not(U32.is_zero(U32.add(0, 1))),
          Laws.counts(ps, U32.add(0, 1)), es)))

# parse of the rendered pair
def rp.parse(
  +e: String,
  +k: String,
  +ek: {T.bare(k) == True{} : Bool},
  +s: String,
  +ep: {Laws.plain.text(s) == True{} : Bool}
) -> {T.parse(T.render(T.Doc{e, [T.VPair{k, T.VStr{s}}]})) == T.Doc{"", [T.VPair{k, rp.val(s)}]}
  : T.Doc}:
  match k:
    case SNil{}:
      Eq.bit.absurd(&2, {T.parse(T.render(T.Doc{e, [T.VPair{SNil{}, T.VStr{s}}]}))
        == T.Doc{"", [T.VPair{SNil{}, rp.val(s)}]} : T.Doc}, ek)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          Equal.trans(T.Doc,
            T.parse(T.render(T.Doc{e, [T.VPair{SCon{Chr{xx}, tt}, T.VStr{s}}]})),
            T.parse(String.append(SCon{Chr{xx}, tt}, SCon{' ', SCon{'=', SCon{' ', SCon{'"',
              String.append(s, "\"\n")}}}})),
            T.Doc{"", [T.VPair{SCon{Chr{xx}, tt}, rp.val(s)}]},
            Equal.cong(String, T.Doc, xs => T.parse(xs),
              T.render(T.Doc{e, [T.VPair{SCon{Chr{xx}, tt}, T.VStr{s}}]}),
              String.append(SCon{Chr{xx}, tt}, SCon{' ', SCon{'=', SCon{' ', SCon{'"',
                String.append(s, "\"\n")}}}}),
              rp.text(e, SCon{Chr{xx}, tt}, ek, s, ep)),
            Equal.trans(T.Doc,
              T.parse(String.append(SCon{Chr{xx}, tt}, SCon{' ', SCon{'=', SCon{' ', SCon{'"',
                String.append(s, "\"\n")}}}})),
              T.doc.read(String.append(s, "\"\n"), vo(SCon{Chr{xx}, tt})),
              T.Doc{"", [T.VPair{SCon{Chr{xx}, tt}, rp.val(s)}]},
              kv.key(xx, tt, String.append(s, "\"\n"), ek),
              rp.read(s, SCon{Chr{xx}, tt}, ep)))

def Laws.render_parse_plain_pair(e, k, ek, s, ep, es):
  Equal.trans(Bool,
    Bool.and(String.is_empty(T.bad(T.parse(T.render(T.Doc{e, [T.VPair{k, T.VStr{s}}]})))),
      Laws.same(T.parse(T.render(T.Doc{e, [T.VPair{k, T.VStr{s}}]})), T.Doc{e, [T.VPair{k,
        T.VStr{s}}]})),
    Laws.same(T.Doc{"", [T.VPair{k, rp.val(s)}]}, T.Doc{e, [T.VPair{k, T.VStr{s}}]}),
    True{},
    Equal.cong(T.Doc, Bool, dd => Bool.and(String.is_empty(T.bad(dd)), Laws.same(dd, T.Doc{e,
      [T.VPair{k, T.VStr{s}}]})), T.parse(T.render(T.Doc{e, [T.VPair{k, T.VStr{s}}]})),
      T.Doc{"", [T.VPair{k, rp.val(s)}]}, rp.parse(e, k, ek, s, ep)),
    rp.same(e, k, rp.val(s), s, rp.own(s, k, es)))

# WP-W: contracts of the walk. A walk along a path is one navigation step per
# segment before the last (nav.walk), then the job at the last (tree.leaf),
# then the frames rebuilt back to the root (nav.rebuild). A step goes through
# what rows.look finds, and the laws' premises are what get finds, so the two
# lookups are shown to agree first.

# what the walk asks a table for a name, read off what get finds
def tb.look(hh: T.Hit) -> T.Look:
  match hh:
    case T.Found{vv}:
      T.look.of(vv)
    case T.Miss{}:
      T.KMiss{}

# one pair of the rows: both lookups stop at it or both pass it
def look.get.step(
  bb: Bool,
  vv: T.Val,
  tt: List<&2, T.Val>,
  +kk: String,
  ih: {T.rows.look(tt, kk) == tb.look(T.rows.find(tt, kk)) : T.Look}
) -> {T.look.step(bb, vv, _u => T.rows.look(tt, kk))
  == tb.look(T.find.step(bb, vv, _u => T.rows.find(tt, kk))) : T.Look}:
  match bb:
    case True{}:
      {==}
    case False{}:
      ih

# rows.look finds what get finds, by induction on the rows
def look.get(
  rows: List<&2, T.Val>,
  +kk: String
) -> {T.rows.look(rows, kk) == tb.look(T.get(rows, kk)) : T.Look}:
  match rows:
    case []:
      {==}
    case T.VPair{nn, vv} <> +tt:
      look.get.step(T.str.eq(nn, kk), vv, tt, kk, look.get(tt, kk))
    case T.VStr{_a} <> tt:
      look.get(tt, kk)
    case T.VSpan{_a, _b} <> tt:
      look.get(tt, kk)
    case T.VInt{_a, _b} <> tt:
      look.get(tt, kk)
    case T.VFlo{_a, _b} <> tt:
      look.get(tt, kk)
    case T.VBool{_a} <> tt:
      look.get(tt, kk)
    case T.VWhen{_a} <> tt:
      look.get(tt, kk)
    case T.VArr{_a} <> tt:
      look.get(tt, kk)
    case T.VInl{_a} <> tt:
      look.get(tt, kk)
    case T.VHead{_a, _b} <> tt:
      look.get(tt, kk)
    case T.VAot{_a, _b} <> tt:
      look.get(tt, kk)
    case T.VAots{_a, _b} <> tt:
      look.get(tt, kk)

# so a premise about get is one about rows.look
def look.via(
  +rows: List<&2, T.Val>,
  +kk: String,
  hh: T.Hit,
  ee: {T.get(rows, kk) == hh : T.Hit}
) -> {T.rows.look(rows, kk) == tb.look(hh) : T.Look}:
  Equal.trans(T.Look, T.rows.look(rows, kk), tb.look(T.get(rows, kk)), tb.look(hh),
    look.get(rows, kk), Equal.cong(T.Hit, T.Look, xx => tb.look(xx), T.get(rows, kk), hh, ee))

# rebuilding the tables above a walk leaves its error alone
def rebuild.bad(
  stack: List<&2, T.Fr>,
  vs: List<&2, T.Val>,
  bad: String,
  heads: List<&2, String>
) -> {Laws.end_bad(T.tree.rebuild(stack, vs, bad, heads)) == bad : String}:
  match stack:
    case []:
      {==}
    case fr <> tt:
      rebuild.bad(tt, T.tree.wrap(fr, vs), bad, heads)

# and whether it has one
def rebuild.empty(
  stack: List<&2, T.Fr>,
  vs: List<&2, T.Val>,
  bad: String,
  heads: List<&2, String>
) -> {String.is_empty(Laws.end_bad(T.tree.rebuild(stack, vs, bad, heads)))
  == String.is_empty(bad) : Bool}:
  Equal.cong(String, Bool, ss => String.is_empty(ss),
    Laws.end_bad(T.tree.rebuild(stack, vs, bad, heads)), bad, rebuild.bad(stack, vs, bad, heads))

# a navigation step's job records no definition
def define.quiet(
  sj: T.Job,
  pp: String,
  hs: List<&2, String>,
  ee: {T.tree.sub.dot(sj) == False{} : Bool}
) -> {T.heads.define(sj, pp, hs) == hs : List<&2, String>}:
  match sj:
    case T.JPut{vv}:
      Eq.bit.absurd2(&2, {T.heads.define(T.JPut{vv}, pp, hs) == hs : List<&2, String>}, ee)
    case T.JDef{}:
      {==}
    case T.JAot{}:
      {==}

# the frame a navigation step pushes for what the name refers to
def tb.last.fr(last: T.Last, name: String, vs: List<&2, T.Val>, pp: String) -> T.Fr:
  match last:
    case T.LastSome{_q, older, _r}:
      T.FrAot{name, vs, older, pp}
    case T.LastNo{_why}:
      T.FrRep{name, vs, pp}

# the frame a navigation step pushes for what the name refers to
def tb.fr(look: T.Look, +name: String, vs: List<&2, T.Val>, +pre: String) -> T.Fr:
  match look:
    case T.KMiss{}:
      T.FrNew{name, vs, T.tree.pre(pre, name)}
    case T.KHead{p, _r}:
      T.FrRep{name, vs, p}
    case T.KAots{+p, elems}:
      tb.last.fr(T.look.last(elems, p), name, vs, p)
    case _:
      T.FrRep{name, vs, pre}

# the frames a walk along the path pushes, the innermost first
def nav.frs(
  path: List<&2, String>,
  +pre: String,
  +rows: List<&2, T.Val>,
  stack: List<&2, T.Fr>
) -> List<&2, T.Fr>:
  match path:
    case []:
      stack
    case +seg <> rest:
      nav.frs(rest, T.tree.pre(pre, seg), Laws.tb.into(T.rows.look(rows, seg)),
        tb.fr(T.rows.look(rows, seg), seg, rows, pre) <> stack)

# whether every segment of the path is navigation for the job: no step asks
# who defined a table or records one
def nav.quiet(path: List<&2, String>, +job: T.Job, +skip: U32) -> Bool:
  match path:
    case []:
      True{}
    case _seg <> rest:
      Bool.and(Bool.not(T.tree.sub.dot(T.tree.sub.job(U32.is_zero(skip), job))),
        nav.quiet(rest, job, T.path.dec(skip)))

# where one navigation step leaves the walk
def sub.Goal(
  +look: T.Look,
  +seg: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +mark: Bool
) -> Type:
  {T.tree.sub.look(look, seg, vs, job, stack, pre, heads, inl, mark)
    == T.Tw{Laws.tb.into(look), job, tb.fr(look, seg, vs, pre) <> stack, "", T.tree.pre(pre, seg),
      heads, inl} : T.Tw}

# a step into an array of tables enters its newest element
def sub.step.last(
  last: T.Last,
  +pp: String,
  +seg: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  ec: {Laws.tb.last.can(last) == True{} : Bool}
) -> {T.tree.sub.aots(last, seg, vs, job, stack, pre, heads, inl, pp)
  == T.Tw{Laws.tb.last.rows(last), job, tb.last.fr(last, seg, vs, pp) <> stack, "",
    T.tree.pre(pre, seg), heads, inl} : T.Tw}:
  match last:
    case T.LastSome{_q, _older, _r}:
      {==}
    case T.LastNo{why}:
      Eq.bit.absurd(&2, {T.tree.sub.aots(T.LastNo{why}, seg, vs, job, stack, pre, heads, inl, pp)
        == T.Tw{Laws.tb.last.rows(T.LastNo{why}), job, tb.last.fr(T.LastNo{why}, seg, vs, pp)
          <> stack, "", T.tree.pre(pre, seg), heads, inl} : T.Tw}, ec)

# a navigation step enters the table the name refers to, pushes its frame, and
# leaves the error and the recorded definitions alone
def sub.step(
  +look: T.Look,
  +seg: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +mark: Bool,
  ec: {Laws.tb.can(look) == True{} : Bool},
  +eq: {T.tree.sub.dot(T.tree.sub.job(mark, job)) == False{} : Bool}
) -> sub.Goal(look, seg, vs, job, stack, pre, heads, inl, mark):
  match look:
    case T.KMiss{}:
      Equal.cong(List<&2, String>, T.Tw,
        hh => T.Tw{[], job, T.FrNew{seg, vs, T.tree.pre(pre, seg)} <> stack, "", T.tree.pre(pre, seg),
          hh, inl},
        T.heads.define(T.tree.sub.job(mark, job), T.tree.pre(pre, seg), heads), heads,
        define.quiet(T.tree.sub.job(mark, job), T.tree.pre(pre, seg), heads, eq))
    case T.KHead{+p, +rr}:
      Equal.trans(T.Tw,
        T.tree.sub.head(T.tree.sub.dot(T.tree.sub.job(mark, job)), p, rr, seg, vs, job, stack, pre,
          heads, inl, mark),
        T.tree.sub.head(False{}, p, rr, seg, vs, job, stack, pre, heads, inl, mark),
        T.Tw{rr, job, T.FrRep{seg, vs, p} <> stack, "", T.tree.pre(pre, seg), heads, inl},
        Equal.cong(Bool, T.Tw,
          bb => T.tree.sub.head(bb, p, rr, seg, vs, job, stack, pre, heads, inl, mark),
          T.tree.sub.dot(T.tree.sub.job(mark, job)), False{}, eq),
        Equal.cong(List<&2, String>, T.Tw,
          hh => T.Tw{rr, job, T.FrRep{seg, vs, p} <> stack, "", T.tree.pre(pre, seg), hh, inl},
          T.heads.define(T.tree.sub.job(mark, job), T.tree.pre(pre, seg), heads), heads,
          define.quiet(T.tree.sub.job(mark, job), T.tree.pre(pre, seg), heads, eq)))
    case T.KAots{+p, +es}:
      Equal.trans(T.Tw,
        T.tree.sub.arr(T.tree.sub.dot(T.tree.sub.job(mark, job)), p, es, seg, vs, job, stack, pre,
          heads, inl),
        T.tree.sub.aots(T.look.last(es, p), seg, vs, job, stack, pre, heads, inl, p),
        T.Tw{Laws.tb.last.rows(T.look.last(es, p)), job, tb.last.fr(T.look.last(es, p), seg, vs, p)
          <> stack, "", T.tree.pre(pre, seg), heads, inl},
        Equal.cong(Bool, T.Tw,
          bb => T.tree.sub.arr(bb, p, es, seg, vs, job, stack, pre, heads, inl),
          T.tree.sub.dot(T.tree.sub.job(mark, job)), False{}, eq),
        sub.step.last(T.look.last(es, p), p, seg, vs, job, stack, pre, heads, inl, ec))
    case T.KInl{}:
      Eq.bit.absurd(&2, {T.tree.sub.look(T.KInl{}, seg, vs, job, stack, pre, heads, inl, mark)
        == T.Tw{Laws.tb.into(T.KInl{}), job, tb.fr(T.KInl{}, seg, vs, pre) <> stack, "",
          T.tree.pre(pre, seg), heads, inl} : T.Tw}, ec)
    case T.KNo{why}:
      Eq.bit.absurd(&2, {T.tree.sub.look(T.KNo{why}, seg, vs, job, stack, pre, heads, inl, mark)
        == T.Tw{Laws.tb.into(T.KNo{why}), job, tb.fr(T.KNo{why}, seg, vs, pre) <> stack, "",
          T.tree.pre(pre, seg), heads, inl} : T.Tw}, ec)

# the walk goes on past a segment with the rest of the path
def walk.cons(
  +seg: String,
  rest: List<&2, String>,
  +kk: String,
  +tw: T.Tw,
  +skip: U32
) -> {T.tree.walk(seg <> List.append(&2, String, rest, [kk]), tw, skip)
  == T.tree.walk(List.append(&2, String, rest, [kk]), T.tree.sub(seg, tw, U32.is_zero(skip)),
    T.path.dec(skip)) : T.End}:
  match rest:
    case []:
      {==}
    case _r <> _rr:
      {==}

# where a walk along the path to one more name comes to that name
def nav.Goal(
  path: List<&2, String>,
  +kk: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +skip: U32
) -> Type:
  {T.tree.walk(List.append(&2, String, path, [kk]), T.Tw{vs, job, stack, "", pre, heads, inl}, skip)
    == T.tree.leaf(kk, T.Tw{Laws.tb.rows(path, vs), job, nav.frs(path, pre, vs, stack), "",
      Laws.tb.join(path, pre), heads, inl}) : T.End}

# by induction on the path: each segment is one navigation step
def nav.walk(
  path: List<&2, String>,
  +kk: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +skip: U32,
  +eo: {Laws.tb.open(path, vs) == True{} : Bool},
  +eq: {nav.quiet(path, job, skip) == True{} : Bool}
) -> nav.Goal(path, kk, vs, job, stack, pre, heads, inl, skip):
  match path:
    case []:
      {==}
    case +seg <> +rest:
      Equal.trans(T.End,
        T.tree.walk(seg <> List.append(&2, String, rest, [kk]), T.Tw{vs, job, stack, "", pre, heads,
          inl}, skip),
        T.tree.walk(List.append(&2, String, rest, [kk]), T.Tw{Laws.tb.into(T.rows.look(vs, seg)), job,
          tb.fr(T.rows.look(vs, seg), seg, vs, pre) <> stack, "", T.tree.pre(pre, seg), heads, inl},
          T.path.dec(skip)),
        T.tree.leaf(kk, T.Tw{Laws.tb.rows(rest, Laws.tb.into(T.rows.look(vs, seg))), job,
          nav.frs(rest, T.tree.pre(pre, seg), Laws.tb.into(T.rows.look(vs, seg)),
            tb.fr(T.rows.look(vs, seg), seg, vs, pre) <> stack), "",
          Laws.tb.join(rest, T.tree.pre(pre, seg)), heads, inl}),
        Equal.trans(T.End,
          T.tree.walk(seg <> List.append(&2, String, rest, [kk]), T.Tw{vs, job, stack, "", pre, heads,
            inl}, skip),
          T.tree.walk(List.append(&2, String, rest, [kk]), T.tree.sub(seg, T.Tw{vs, job, stack, "",
            pre, heads, inl}, U32.is_zero(skip)), T.path.dec(skip)),
          T.tree.walk(List.append(&2, String, rest, [kk]), T.Tw{Laws.tb.into(T.rows.look(vs, seg)),
            job, tb.fr(T.rows.look(vs, seg), seg, vs, pre) <> stack, "", T.tree.pre(pre, seg), heads,
            inl}, T.path.dec(skip)),
          walk.cons(seg, rest, kk, T.Tw{vs, job, stack, "", pre, heads, inl}, skip),
          Equal.cong(T.Tw, T.End,
            tw => T.tree.walk(List.append(&2, String, rest, [kk]), tw, T.path.dec(skip)),
            T.tree.sub(seg, T.Tw{vs, job, stack, "", pre, heads, inl}, U32.is_zero(skip)),
            T.Tw{Laws.tb.into(T.rows.look(vs, seg)), job, tb.fr(T.rows.look(vs, seg), seg, vs, pre)
              <> stack, "", T.tree.pre(pre, seg), heads, inl},
            sub.step(T.rows.look(vs, seg), seg, vs, job, stack, pre, heads, inl, U32.is_zero(skip),
              Eq.and.left(Laws.tb.can(T.rows.look(vs, seg)),
                Laws.tb.open(rest, Laws.tb.into(T.rows.look(vs, seg))), eo),
              Eq.not.true(T.tree.sub.dot(T.tree.sub.job(U32.is_zero(skip), job)),
                Eq.and.left(Bool.not(T.tree.sub.dot(T.tree.sub.job(U32.is_zero(skip), job))),
                  nav.quiet(rest, job, T.path.dec(skip)), eq))))),
        nav.walk(rest, kk, Laws.tb.into(T.rows.look(vs, seg)), job,
          tb.fr(T.rows.look(vs, seg), seg, vs, pre) <> stack, T.tree.pre(pre, seg), heads, inl,
          T.path.dec(skip),
          Eq.and.right(Laws.tb.can(T.rows.look(vs, seg)),
            Laws.tb.open(rest, Laws.tb.into(T.rows.look(vs, seg))), eo),
          Eq.and.right(Bool.not(T.tree.sub.dot(T.tree.sub.job(U32.is_zero(skip), job))),
            nav.quiet(rest, job, T.path.dec(skip)), eq)))

# rebuilding the frame of an array of tables' element puts the element back
def wrap.last(
  last: T.Last,
  +pp: String,
  +seg: String,
  +vs: List<&2, T.Val>,
  +child: List<&2, T.Val>,
  ec: {Laws.tb.last.can(last) == True{} : Bool}
) -> {T.tree.wrap(tb.last.fr(last, seg, vs, pp), child)
  == Laws.tb.last.put(last, seg, vs, pp, child) : List<&2, T.Val>}:
  match last:
    case T.LastSome{_q, _older, _r}:
      {==}
    case T.LastNo{why}:
      Eq.bit.absurd(&2, {T.tree.wrap(tb.last.fr(T.LastNo{why}, seg, vs, pp), child)
        == Laws.tb.last.put(T.LastNo{why}, seg, vs, pp, child) : List<&2, T.Val>}, ec)

# rebuilding a navigation step's frame puts the table back where it was
def wrap.step(
  +look: T.Look,
  +seg: String,
  +vs: List<&2, T.Val>,
  +pre: String,
  +child: List<&2, T.Val>,
  ec: {Laws.tb.can(look) == True{} : Bool}
) -> {T.tree.wrap(tb.fr(look, seg, vs, pre), child)
  == Laws.tb.put.in(look, seg, vs, pre, child) : List<&2, T.Val>}:
  match look:
    case T.KMiss{}:
      {==}
    case T.KHead{_p, _r}:
      {==}
    case T.KAots{+p, +es}:
      wrap.last(T.look.last(es, p), p, seg, vs, child, ec)
    case T.KInl{}:
      Eq.bit.absurd(&2, {T.tree.wrap(tb.fr(T.KInl{}, seg, vs, pre), child)
        == Laws.tb.put.in(T.KInl{}, seg, vs, pre, child) : List<&2, T.Val>}, ec)
    case T.KNo{why}:
      Eq.bit.absurd(&2, {T.tree.wrap(tb.fr(T.KNo{why}, seg, vs, pre), child)
        == Laws.tb.put.in(T.KNo{why}, seg, vs, pre, child) : List<&2, T.Val>}, ec)

# by induction on the path: rebuilding the frames a walk pushed sets the table
# at the path's end to what the leaf left, and puts every table above it back
def nav.rebuild(
  path: List<&2, String>,
  +pre: String,
  +vs: List<&2, T.Val>,
  +stack: List<&2, T.Fr>,
  +child: List<&2, T.Val>,
  +bad: String,
  +heads: List<&2, String>,
  +eo: {Laws.tb.open(path, vs) == True{} : Bool}
) -> {T.tree.rebuild(nav.frs(path, pre, vs, stack), child, bad, heads)
  == T.tree.rebuild(stack, Laws.tb.set(path, pre, vs, child), bad, heads) : T.End}:
  match path:
    case []:
      {==}
    case +seg <> +rest:
      Equal.trans(T.End,
        T.tree.rebuild(nav.frs(rest, T.tree.pre(pre, seg), Laws.tb.into(T.rows.look(vs, seg)),
          tb.fr(T.rows.look(vs, seg), seg, vs, pre) <> stack), child, bad, heads),
        T.tree.rebuild(tb.fr(T.rows.look(vs, seg), seg, vs, pre) <> stack,
          Laws.tb.set(rest, T.tree.pre(pre, seg), Laws.tb.into(T.rows.look(vs, seg)), child), bad,
          heads),
        T.tree.rebuild(stack, Laws.tb.put.in(T.rows.look(vs, seg), seg, vs, pre,
          Laws.tb.set(rest, T.tree.pre(pre, seg), Laws.tb.into(T.rows.look(vs, seg)), child)), bad,
          heads),
        nav.rebuild(rest, T.tree.pre(pre, seg), Laws.tb.into(T.rows.look(vs, seg)),
          tb.fr(T.rows.look(vs, seg), seg, vs, pre) <> stack, child, bad, heads,
          Eq.and.right(Laws.tb.can(T.rows.look(vs, seg)),
            Laws.tb.open(rest, Laws.tb.into(T.rows.look(vs, seg))), eo)),
        Equal.cong(List<&2, T.Val>, T.End, xx => T.tree.rebuild(stack, xx, bad, heads),
          T.tree.wrap(tb.fr(T.rows.look(vs, seg), seg, vs, pre),
            Laws.tb.set(rest, T.tree.pre(pre, seg), Laws.tb.into(T.rows.look(vs, seg)), child)),
          Laws.tb.put.in(T.rows.look(vs, seg), seg, vs, pre,
            Laws.tb.set(rest, T.tree.pre(pre, seg), Laws.tb.into(T.rows.look(vs, seg)), child)),
          wrap.step(T.rows.look(vs, seg), seg, vs, pre,
            Laws.tb.set(rest, T.tree.pre(pre, seg), Laws.tb.into(T.rows.look(vs, seg)), child),
            Eq.and.left(Laws.tb.can(T.rows.look(vs, seg)),
              Laws.tb.open(rest, Laws.tb.into(T.rows.look(vs, seg))), eo))))

# a segment the walk counts down past is navigation for a put
def quiet.put.step(
  zz: Bool,
  vv: T.Val,
  qq: Bool,
  ez: {Bool.not(zz) == True{} : Bool},
  eq: {qq == True{} : Bool}
) -> {Bool.and(Bool.not(T.tree.sub.dot(T.tree.sub.job(zz, T.JPut{vv}))), qq) == True{} : Bool}:
  match zz:
    case True{}:
      Eq.bit.absurd(&2, {Bool.and(Bool.not(T.tree.sub.dot(T.tree.sub.job(True{}, T.JPut{vv}))), qq)
        == True{} : Bool}, ez)
    case False{}:
      eq

# every segment the walk counts down past is navigation for a put
def quiet.put(
  path: List<&2, String>,
  +vv: T.Val,
  +skip: U32,
  +ec: {Laws.counts.down(path, skip) == True{} : Bool}
) -> {nav.quiet(path, T.JPut{vv}, skip) == True{} : Bool}:
  match path:
    case []:
      {==}
    case _seg <> +rest:
      quiet.put.step(U32.is_zero(skip), vv, nav.quiet(rest, T.JPut{vv}, T.path.dec(skip)),
        Eq.and.left(Bool.not(U32.is_zero(skip)), Laws.counts.down(rest, T.path.dec(skip)), ec),
        quiet.put(rest, vv, T.path.dec(skip),
          Eq.and.right(Bool.not(U32.is_zero(skip)), Laws.counts.down(rest, T.path.dec(skip)), ec)))

# every segment of a header is navigation
def quiet.def(path: List<&2, String>) -> {nav.quiet(path, T.JDef{}, 0) == True{} : Bool}:
  match path:
    case []:
      {==}
    case _seg <> rest:
      quiet.def(rest)

# a put's job at the last name: a new pair, or an error for a name held
def put.exact(
  hh: T.Hit,
  kk: String,
  vs: List<&2, T.Val>,
  vv: T.Val,
  stack: List<&2, T.Fr>,
  heads: List<&2, String>
) -> {String.is_empty(Laws.end_bad(T.tree.leaf.put(hh, kk, vs, vv, stack, "", heads)))
  == Laws.is_miss(hh) : Bool}:
  match hh:
    case T.Found{_x}:
      rebuild.empty(stack, vs, T.err.first("", "duplicate key"), heads)
    case T.Miss{}:
      rebuild.empty(stack, T.VPair{kk, vv} <> vs, "", heads)

def Laws.walk_put_at_head(here, k, v, rows, heads, skip, inl, eo, ec, em):
  Equal.trans(T.End,
    T.tree.walk(List.append(&2, String, here, [k]), T.Tw{rows, T.JPut{v}, [], "", "", heads, inl},
      skip),
    T.tree.leaf(k, T.Tw{Laws.tb.rows(here, rows), T.JPut{v}, nav.frs(here, "", rows, []), "",
      Laws.tb.join(here, ""), heads, inl}),
    T.End{Laws.tb.set(here, "", rows, T.VPair{k, v} <> Laws.tb.rows(here, rows)), "", heads},
    nav.walk(here, k, rows, T.JPut{v}, [], "", heads, inl, skip, eo, quiet.put(here, v, skip, ec)),
    Equal.trans(T.End,
      T.tree.leaf(k, T.Tw{Laws.tb.rows(here, rows), T.JPut{v}, nav.frs(here, "", rows, []), "",
        Laws.tb.join(here, ""), heads, inl}),
      T.tree.rebuild(nav.frs(here, "", rows, []), T.VPair{k, v} <> Laws.tb.rows(here, rows), "",
        heads),
      T.End{Laws.tb.set(here, "", rows, T.VPair{k, v} <> Laws.tb.rows(here, rows)), "", heads},
      Equal.cong(T.Hit, T.End,
        hh => T.tree.leaf.put(hh, k, Laws.tb.rows(here, rows), v, nav.frs(here, "", rows, []), "",
          heads),
        T.get(Laws.tb.rows(here, rows), k), T.Miss{}, em),
      nav.rebuild(here, "", rows, [], T.VPair{k, v} <> Laws.tb.rows(here, rows), "", heads, eo)))

def Laws.walk_put_refused_exactly(here, k, v, rows, heads, skip, inl, eo, ec):
  Equal.trans(Bool,
    String.is_empty(Laws.end_bad(T.tree.walk(List.append(&2, String, here, [k]),
      T.Tw{rows, T.JPut{v}, [], "", "", heads, inl}, skip))),
    String.is_empty(Laws.end_bad(T.tree.leaf(k, T.Tw{Laws.tb.rows(here, rows), T.JPut{v},
      nav.frs(here, "", rows, []), "", Laws.tb.join(here, ""), heads, inl}))),
    Laws.is_miss(T.get(Laws.tb.rows(here, rows), k)),
    Equal.cong(T.End, Bool, ee => String.is_empty(Laws.end_bad(ee)),
      T.tree.walk(List.append(&2, String, here, [k]), T.Tw{rows, T.JPut{v}, [], "", "", heads, inl},
        skip),
      T.tree.leaf(k, T.Tw{Laws.tb.rows(here, rows), T.JPut{v}, nav.frs(here, "", rows, []), "",
        Laws.tb.join(here, ""), heads, inl}),
      nav.walk(here, k, rows, T.JPut{v}, [], "", heads, inl, skip, eo, quiet.put(here, v, skip, ec))),
    put.exact(T.get(Laws.tb.rows(here, rows), k), k, Laws.tb.rows(here, rows), v,
      nav.frs(here, "", rows, []), heads))

def Laws.header_defines_new_table(segs, k, rows, heads, eo, em):
  Equal.trans(T.End,
    T.tree.walk(List.append(&2, String, segs, [k]), T.Tw{rows, T.JDef{}, [], "", "", heads, False{}},
      0),
    T.tree.leaf(k, T.Tw{Laws.tb.rows(segs, rows), T.JDef{}, nav.frs(segs, "", rows, []), "",
      Laws.tb.join(segs, ""), heads, False{}}),
    T.End{Laws.tb.set(segs, "", rows, T.VPair{k, T.VHead{T.tree.pre(Laws.tb.join(segs, ""), k), []}}
      <> Laws.tb.rows(segs, rows)), "", T.heads.by.head(T.tree.pre(Laws.tb.join(segs, ""), k))
      <> heads},
    nav.walk(segs, k, rows, T.JDef{}, [], "", heads, False{}, 0, eo, quiet.def(segs)),
    Equal.trans(T.End,
      T.tree.leaf(k, T.Tw{Laws.tb.rows(segs, rows), T.JDef{}, nav.frs(segs, "", rows, []), "",
        Laws.tb.join(segs, ""), heads, False{}}),
      T.tree.rebuild(nav.frs(segs, "", rows, []), T.VPair{k, T.VHead{T.tree.pre(Laws.tb.join(segs,
        ""), k), []}} <> Laws.tb.rows(segs, rows), "",
        T.heads.by.head(T.tree.pre(Laws.tb.join(segs, ""), k)) <> heads),
      T.End{Laws.tb.set(segs, "", rows, T.VPair{k, T.VHead{T.tree.pre(Laws.tb.join(segs, ""), k),
        []}} <> Laws.tb.rows(segs, rows)), "",
        T.heads.by.head(T.tree.pre(Laws.tb.join(segs, ""), k)) <> heads},
      Equal.cong(T.Look, T.End,
        ll => T.tree.leaf.def.hit(ll, k, Laws.tb.rows(segs, rows), nav.frs(segs, "", rows, []), "",
          T.tree.pre(Laws.tb.join(segs, ""), k), heads),
        T.rows.look(Laws.tb.rows(segs, rows), k), T.KMiss{},
        look.via(Laws.tb.rows(segs, rows), k, T.Miss{}, em)),
      nav.rebuild(segs, "", rows, [], T.VPair{k, T.VHead{T.tree.pre(Laws.tb.join(segs, ""), k), []}}
        <> Laws.tb.rows(segs, rows), "", T.heads.by.head(T.tree.pre(Laws.tb.join(segs, ""), k))
        <> heads, eo)))

def Laws.header_defines_implicit_table(segs, k, rows, heads, p, sub, eo, ef, eh):
  Equal.trans(T.End,
    T.tree.walk(List.append(&2, String, segs, [k]), T.Tw{rows, T.JDef{}, [], "", "", heads, False{}},
      0),
    T.tree.leaf(k, T.Tw{Laws.tb.rows(segs, rows), T.JDef{}, nav.frs(segs, "", rows, []), "",
      Laws.tb.join(segs, ""), heads, False{}}),
    T.End{Laws.tb.set(segs, "", rows, T.rows.repl(Laws.tb.rows(segs, rows), k,
      T.VHead{T.tree.pre(Laws.tb.join(segs, ""), k), sub})), "",
      T.heads.by.head(T.tree.pre(Laws.tb.join(segs, ""), k)) <> heads},
    nav.walk(segs, k, rows, T.JDef{}, [], "", heads, False{}, 0, eo, quiet.def(segs)),
    Equal.trans(T.End,
      T.tree.leaf(k, T.Tw{Laws.tb.rows(segs, rows), T.JDef{}, nav.frs(segs, "", rows, []), "",
        Laws.tb.join(segs, ""), heads, False{}}),
      T.tree.leaf.def.head(T.heads.has(heads, T.tree.pre(Laws.tb.join(segs, ""), k)), k,
        Laws.tb.rows(segs, rows), sub, nav.frs(segs, "", rows, []), "",
        T.tree.pre(Laws.tb.join(segs, ""), k), heads),
      T.End{Laws.tb.set(segs, "", rows, T.rows.repl(Laws.tb.rows(segs, rows), k,
        T.VHead{T.tree.pre(Laws.tb.join(segs, ""), k), sub})), "",
        T.heads.by.head(T.tree.pre(Laws.tb.join(segs, ""), k)) <> heads},
      Equal.cong(T.Look, T.End,
        ll => T.tree.leaf.def.hit(ll, k, Laws.tb.rows(segs, rows), nav.frs(segs, "", rows, []), "",
          T.tree.pre(Laws.tb.join(segs, ""), k), heads),
        T.rows.look(Laws.tb.rows(segs, rows), k), T.KHead{p, sub},
        look.via(Laws.tb.rows(segs, rows), k, T.Found{T.VHead{p, sub}}, ef)),
      Equal.trans(T.End,
        T.tree.leaf.def.head(T.heads.has(heads, T.tree.pre(Laws.tb.join(segs, ""), k)), k,
          Laws.tb.rows(segs, rows), sub, nav.frs(segs, "", rows, []), "",
          T.tree.pre(Laws.tb.join(segs, ""), k), heads),
        T.tree.rebuild(nav.frs(segs, "", rows, []), T.rows.repl(Laws.tb.rows(segs, rows), k,
          T.VHead{T.tree.pre(Laws.tb.join(segs, ""), k), sub}), "",
          T.heads.by.head(T.tree.pre(Laws.tb.join(segs, ""), k)) <> heads),
        T.End{Laws.tb.set(segs, "", rows, T.rows.repl(Laws.tb.rows(segs, rows), k,
          T.VHead{T.tree.pre(Laws.tb.join(segs, ""), k), sub})), "",
          T.heads.by.head(T.tree.pre(Laws.tb.join(segs, ""), k)) <> heads},
        Equal.cong(Bool, T.End,
          bb => T.tree.leaf.def.head(bb, k, Laws.tb.rows(segs, rows), sub,
            nav.frs(segs, "", rows, []), "", T.tree.pre(Laws.tb.join(segs, ""), k), heads),
          T.heads.has(heads, T.tree.pre(Laws.tb.join(segs, ""), k)), False{}, eh),
        nav.rebuild(segs, "", rows, [], T.rows.repl(Laws.tb.rows(segs, rows), k,
          T.VHead{T.tree.pre(Laws.tb.join(segs, ""), k), sub}), "",
          T.heads.by.head(T.tree.pre(Laws.tb.join(segs, ""), k)) <> heads, eo))))

# a header of a table that exists: refused when a header or dotted keys
# defined it
def hdr.seen(
  seen: Bool,
  kk: String,
  vs: List<&2, T.Val>,
  rr: List<&2, T.Val>,
  stack: List<&2, T.Fr>,
  +pp: String,
  heads: List<&2, String>
) -> {String.is_empty(Laws.end_bad(T.tree.leaf.def.head(seen, kk, vs, rr, stack, "", pp, heads)))
  == Bool.not(seen) : Bool}:
  match seen:
    case True{}:
      rebuild.empty(stack, vs, T.err.first("", "duplicate table"), heads)
    case False{}:
      rebuild.empty(stack, T.rows.repl(vs, kk, T.VHead{pp, rr}), "", T.heads.by.head(pp) <> heads)

# a [table] header's job at the last name, for each thing get can find there
def hdr.exact(
  hh: T.Hit,
  +kk: String,
  +vs: List<&2, T.Val>,
  +stack: List<&2, T.Fr>,
  +pp: String,
  +heads: List<&2, String>
) -> {String.is_empty(Laws.end_bad(T.tree.leaf.def.hit(tb.look(hh), kk, vs, stack, "", pp, heads)))
  == Laws.hdr.ok(hh, heads, pp) : Bool}:
  match hh:
    case T.Miss{}:
      rebuild.empty(stack, T.VPair{kk, T.VHead{pp, []}} <> vs, "", T.heads.by.head(pp) <> heads)
    case T.Found{T.VHead{_p, rr}}:
      hdr.seen(T.heads.has(heads, pp), kk, vs, rr, stack, pp, heads)
    case T.Found{T.VInl{_a}}:
      rebuild.empty(stack, vs, T.err.first("", "inline table is closed"), heads)
    case T.Found{T.VAots{_a, _b}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)
    case T.Found{T.VStr{_a}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)
    case T.Found{T.VSpan{_a, _b}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)
    case T.Found{T.VInt{_a, _b}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)
    case T.Found{T.VFlo{_a, _b}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)
    case T.Found{T.VBool{_a}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)
    case T.Found{T.VWhen{_a}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)
    case T.Found{T.VArr{_a}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)
    case T.Found{T.VAot{_a, _b}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)
    case T.Found{T.VPair{_a, _b}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)

def Laws.header_refused_exactly(segs, k, rows, heads, eo):
  Equal.trans(Bool,
    String.is_empty(Laws.end_bad(T.tree.walk(List.append(&2, String, segs, [k]),
      T.Tw{rows, T.JDef{}, [], "", "", heads, False{}}, 0))),
    String.is_empty(Laws.end_bad(T.tree.leaf(k, T.Tw{Laws.tb.rows(segs, rows), T.JDef{},
      nav.frs(segs, "", rows, []), "", Laws.tb.join(segs, ""), heads, False{}}))),
    Laws.hdr.ok(T.get(Laws.tb.rows(segs, rows), k), heads, T.tree.pre(Laws.tb.join(segs, ""), k)),
    Equal.cong(T.End, Bool, ee => String.is_empty(Laws.end_bad(ee)),
      T.tree.walk(List.append(&2, String, segs, [k]), T.Tw{rows, T.JDef{}, [], "", "", heads,
        False{}}, 0),
      T.tree.leaf(k, T.Tw{Laws.tb.rows(segs, rows), T.JDef{}, nav.frs(segs, "", rows, []), "",
        Laws.tb.join(segs, ""), heads, False{}}),
      nav.walk(segs, k, rows, T.JDef{}, [], "", heads, False{}, 0, eo, quiet.def(segs))),
    Equal.trans(Bool,
      String.is_empty(Laws.end_bad(T.tree.leaf.def.hit(T.rows.look(Laws.tb.rows(segs, rows), k), k,
        Laws.tb.rows(segs, rows), nav.frs(segs, "", rows, []), "",
        T.tree.pre(Laws.tb.join(segs, ""), k), heads))),
      String.is_empty(Laws.end_bad(T.tree.leaf.def.hit(tb.look(T.get(Laws.tb.rows(segs, rows), k)),
        k, Laws.tb.rows(segs, rows), nav.frs(segs, "", rows, []), "",
        T.tree.pre(Laws.tb.join(segs, ""), k), heads))),
      Laws.hdr.ok(T.get(Laws.tb.rows(segs, rows), k), heads, T.tree.pre(Laws.tb.join(segs, ""), k)),
      Equal.cong(T.Look, Bool,
        ll => String.is_empty(Laws.end_bad(T.tree.leaf.def.hit(ll, k, Laws.tb.rows(segs, rows),
          nav.frs(segs, "", rows, []), "", T.tree.pre(Laws.tb.join(segs, ""), k), heads))),
        T.rows.look(Laws.tb.rows(segs, rows), k), tb.look(T.get(Laws.tb.rows(segs, rows), k)),
        look.get(Laws.tb.rows(segs, rows), k)),
      hdr.exact(T.get(Laws.tb.rows(segs, rows), k), k, Laws.tb.rows(segs, rows),
        nav.frs(segs, "", rows, []), T.tree.pre(Laws.tb.join(segs, ""), k), heads)))

# every segment of an array-of-tables header is navigation
def quiet.aot(path: List<&2, String>) -> {nav.quiet(path, T.JAot{}, 0) == True{} : Bool}:
  match path:
    case []:
      {==}
    case _seg <> rest:
      quiet.aot(rest)

def Laws.aot_header_starts_array(segs, k, rows, heads, eo, em):
  Equal.trans(T.End,
    T.tree.walk(List.append(&2, String, segs, [k]), T.Tw{rows, T.JAot{}, [], "", "", heads, False{}},
      0),
    T.tree.leaf(k, T.Tw{Laws.tb.rows(segs, rows), T.JAot{}, nav.frs(segs, "", rows, []), "",
      Laws.tb.join(segs, ""), heads, False{}}),
    T.End{Laws.tb.set(segs, "", rows, T.VPair{k, T.VAots{T.tree.pre(Laws.tb.join(segs, ""), k),
      [T.VAot{T.tree.pre(Laws.tb.join(segs, ""), k), []}]}} <> Laws.tb.rows(segs, rows)), "", heads},
    nav.walk(segs, k, rows, T.JAot{}, [], "", heads, False{}, 0, eo, quiet.aot(segs)),
    Equal.trans(T.End,
      T.tree.leaf(k, T.Tw{Laws.tb.rows(segs, rows), T.JAot{}, nav.frs(segs, "", rows, []), "",
        Laws.tb.join(segs, ""), heads, False{}}),
      T.tree.rebuild(nav.frs(segs, "", rows, []), T.VPair{k, T.VAots{T.tree.pre(Laws.tb.join(segs,
        ""), k), [T.VAot{T.tree.pre(Laws.tb.join(segs, ""), k), []}]}} <> Laws.tb.rows(segs, rows),
        "", heads),
      T.End{Laws.tb.set(segs, "", rows, T.VPair{k, T.VAots{T.tree.pre(Laws.tb.join(segs, ""), k),
        [T.VAot{T.tree.pre(Laws.tb.join(segs, ""), k), []}]}} <> Laws.tb.rows(segs, rows)), "",
        heads},
      Equal.cong(T.Look, T.End,
        ll => T.tree.leaf.aot.hit(ll, k, Laws.tb.rows(segs, rows), nav.frs(segs, "", rows, []), "",
          T.tree.pre(Laws.tb.join(segs, ""), k), heads),
        T.rows.look(Laws.tb.rows(segs, rows), k), T.KMiss{},
        look.via(Laws.tb.rows(segs, rows), k, T.Miss{}, em)),
      nav.rebuild(segs, "", rows, [], T.VPair{k, T.VAots{T.tree.pre(Laws.tb.join(segs, ""), k),
        [T.VAot{T.tree.pre(Laws.tb.join(segs, ""), k), []}]}} <> Laws.tb.rows(segs, rows), "", heads,
        eo)))

def Laws.aot_header_extends_array(segs, k, rows, heads, p, elems, eo, ef):
  Equal.trans(T.End,
    T.tree.walk(List.append(&2, String, segs, [k]), T.Tw{rows, T.JAot{}, [], "", "", heads, False{}},
      0),
    T.tree.leaf(k, T.Tw{Laws.tb.rows(segs, rows), T.JAot{}, nav.frs(segs, "", rows, []), "",
      Laws.tb.join(segs, ""), heads, False{}}),
    T.End{Laws.tb.set(segs, "", rows, T.rows.repl(Laws.tb.rows(segs, rows), k,
      T.VAots{T.tree.pre(Laws.tb.join(segs, ""), k), T.VAot{T.tree.pre(Laws.tb.join(segs, ""), k), []}
        <> elems})), "",
      T.heads.drop(heads, String.append(T.tree.pre(Laws.tb.join(segs, ""), k), "."))},
    nav.walk(segs, k, rows, T.JAot{}, [], "", heads, False{}, 0, eo, quiet.aot(segs)),
    Equal.trans(T.End,
      T.tree.leaf(k, T.Tw{Laws.tb.rows(segs, rows), T.JAot{}, nav.frs(segs, "", rows, []), "",
        Laws.tb.join(segs, ""), heads, False{}}),
      T.tree.rebuild(nav.frs(segs, "", rows, []), T.rows.repl(Laws.tb.rows(segs, rows), k,
        T.VAots{T.tree.pre(Laws.tb.join(segs, ""), k), T.VAot{T.tree.pre(Laws.tb.join(segs, ""), k),
          []} <> elems}), "",
        T.heads.drop(heads, String.append(T.tree.pre(Laws.tb.join(segs, ""), k), "."))),
      T.End{Laws.tb.set(segs, "", rows, T.rows.repl(Laws.tb.rows(segs, rows), k,
        T.VAots{T.tree.pre(Laws.tb.join(segs, ""), k), T.VAot{T.tree.pre(Laws.tb.join(segs, ""), k),
          []} <> elems})), "",
        T.heads.drop(heads, String.append(T.tree.pre(Laws.tb.join(segs, ""), k), "."))},
      Equal.cong(T.Look, T.End,
        ll => T.tree.leaf.aot.hit(ll, k, Laws.tb.rows(segs, rows), nav.frs(segs, "", rows, []), "",
          T.tree.pre(Laws.tb.join(segs, ""), k), heads),
        T.rows.look(Laws.tb.rows(segs, rows), k), T.KAots{p, elems},
        look.via(Laws.tb.rows(segs, rows), k, T.Found{T.VAots{p, elems}}, ef)),
      nav.rebuild(segs, "", rows, [], T.rows.repl(Laws.tb.rows(segs, rows), k,
        T.VAots{T.tree.pre(Laws.tb.join(segs, ""), k), T.VAot{T.tree.pre(Laws.tb.join(segs, ""), k),
          []} <> elems}), "",
        T.heads.drop(heads, String.append(T.tree.pre(Laws.tb.join(segs, ""), k), ".")), eo)))

# an [[array]] header's job at the last name, for each thing get can find there
def aot.exact(
  hh: T.Hit,
  +kk: String,
  +vs: List<&2, T.Val>,
  +stack: List<&2, T.Fr>,
  +pp: String,
  +heads: List<&2, String>
) -> {String.is_empty(Laws.end_bad(T.tree.leaf.aot.hit(tb.look(hh), kk, vs, stack, "", pp, heads)))
  == Laws.aot.ok(hh) : Bool}:
  match hh:
    case T.Miss{}:
      rebuild.empty(stack, T.VPair{kk, T.VAots{pp, [T.VAot{pp, []}]}} <> vs, "", heads)
    case T.Found{T.VAots{_p, es}}:
      rebuild.empty(stack, T.rows.repl(vs, kk, T.VAots{pp, T.VAot{pp, []} <> es}), "",
        T.heads.drop(heads, String.append(pp, ".")))
    case T.Found{T.VHead{_a, _b}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)
    case T.Found{T.VInl{_a}}:
      rebuild.empty(stack, vs, T.err.first("", "inline table is closed"), heads)
    case T.Found{T.VStr{_a}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)
    case T.Found{T.VSpan{_a, _b}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)
    case T.Found{T.VInt{_a, _b}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)
    case T.Found{T.VFlo{_a, _b}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)
    case T.Found{T.VBool{_a}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)
    case T.Found{T.VWhen{_a}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)
    case T.Found{T.VArr{_a}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)
    case T.Found{T.VAot{_a, _b}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)
    case T.Found{T.VPair{_a, _b}}:
      rebuild.empty(stack, vs, T.err.first("", "not a table"), heads)

def Laws.aot_header_refused_exactly(segs, k, rows, heads, eo):
  Equal.trans(Bool,
    String.is_empty(Laws.end_bad(T.tree.walk(List.append(&2, String, segs, [k]),
      T.Tw{rows, T.JAot{}, [], "", "", heads, False{}}, 0))),
    String.is_empty(Laws.end_bad(T.tree.leaf(k, T.Tw{Laws.tb.rows(segs, rows), T.JAot{},
      nav.frs(segs, "", rows, []), "", Laws.tb.join(segs, ""), heads, False{}}))),
    Laws.aot.ok(T.get(Laws.tb.rows(segs, rows), k)),
    Equal.cong(T.End, Bool, ee => String.is_empty(Laws.end_bad(ee)),
      T.tree.walk(List.append(&2, String, segs, [k]), T.Tw{rows, T.JAot{}, [], "", "", heads,
        False{}}, 0),
      T.tree.leaf(k, T.Tw{Laws.tb.rows(segs, rows), T.JAot{}, nav.frs(segs, "", rows, []), "",
        Laws.tb.join(segs, ""), heads, False{}}),
      nav.walk(segs, k, rows, T.JAot{}, [], "", heads, False{}, 0, eo, quiet.aot(segs))),
    Equal.trans(Bool,
      String.is_empty(Laws.end_bad(T.tree.leaf.aot.hit(T.rows.look(Laws.tb.rows(segs, rows), k), k,
        Laws.tb.rows(segs, rows), nav.frs(segs, "", rows, []), "",
        T.tree.pre(Laws.tb.join(segs, ""), k), heads))),
      String.is_empty(Laws.end_bad(T.tree.leaf.aot.hit(tb.look(T.get(Laws.tb.rows(segs, rows), k)),
        k, Laws.tb.rows(segs, rows), nav.frs(segs, "", rows, []), "",
        T.tree.pre(Laws.tb.join(segs, ""), k), heads))),
      Laws.aot.ok(T.get(Laws.tb.rows(segs, rows), k)),
      Equal.cong(T.Look, Bool,
        ll => String.is_empty(Laws.end_bad(T.tree.leaf.aot.hit(ll, k, Laws.tb.rows(segs, rows),
          nav.frs(segs, "", rows, []), "", T.tree.pre(Laws.tb.join(segs, ""), k), heads))),
        T.rows.look(Laws.tb.rows(segs, rows), k), tb.look(T.get(Laws.tb.rows(segs, rows), k)),
        look.get(Laws.tb.rows(segs, rows), k)),
      aot.exact(T.get(Laws.tb.rows(segs, rows), k), k, Laws.tb.rows(segs, rows),
        nav.frs(segs, "", rows, []), T.tree.pre(Laws.tb.join(segs, ""), k), heads)))

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
def Laws.failed_walk_changes_nothing(path, rows, job, bad, pre, heads, inl, skip, eb):
  match path:
    case []:
      Equal.cong(Bool, T.End, bb => T.End{rows, T.err.first.go(bb, bad, "empty key"), heads},
        String.is_empty(bad), False{}, eb)
    case name <> +rest:
      failed.more(rest, name, rows, job, bad, pre, heads, inl, skip, eb,
        Laws.failed_walk_changes_nothing(rest, rows, job, bad, pre, heads, inl, T.path.dec(skip), eb))

# rows.seal. Its one pass conses each value, sealed, onto an accumulator and
# reverses a table's accumulator by not reversing it back.

# the value rows.seal.go conses for a value
def seal.y(+vv: T.Val) -> T.Val:
  match vv:
    case T.VPair{nn, T.VHead{pp, rows}}:
      T.VPair{nn, T.VHead{pp, T.rows.seal(rows)}}
    case T.VPair{nn, T.VAots{pp, elems}}:
      T.VPair{nn, T.VAots{pp, T.rows.seal(elems)}}
    case T.VPair{nn, T.VInl{rows}}:
      T.VPair{nn, T.VInl{T.rows.seal(rows)}}
    case T.VPair{nn, T.VArr{items}}:
      T.VPair{nn, T.VArr{T.rows.seal.go(items, False{}, [])}}
    case T.VAot{pp, rows}:
      T.VAot{pp, T.rows.seal(rows)}
    case T.VAots{pp, elems}:
      T.VAots{pp, T.rows.seal(elems)}
    case T.VInl{rows}:
      T.VInl{T.rows.seal(rows)}
    case T.VArr{items}:
      T.VArr{T.rows.seal.go(items, False{}, [])}
    case _:
      vv

# one step of the pass, for each value it can meet
def go.cons(
  xx: T.Val,
  tt: List<&2, T.Val>,
  rev: Bool,
  acc: List<&2, T.Val>
) -> {T.rows.seal.go(xx <> tt, rev, acc) == T.rows.seal.go(tt, rev, seal.y(xx) <> acc)
  : List<&2, T.Val>}:
  match xx:
    case T.VPair{_n, T.VStr{_a}}:
      {==}
    case T.VPair{_n, T.VSpan{_a, _b}}:
      {==}
    case T.VPair{_n, T.VInt{_a, _b}}:
      {==}
    case T.VPair{_n, T.VFlo{_a, _b}}:
      {==}
    case T.VPair{_n, T.VBool{_a}}:
      {==}
    case T.VPair{_n, T.VWhen{_a}}:
      {==}
    case T.VPair{_n, T.VArr{_a}}:
      {==}
    case T.VPair{_n, T.VInl{_a}}:
      {==}
    case T.VPair{_n, T.VHead{_a, _b}}:
      {==}
    case T.VPair{_n, T.VAot{_a, _b}}:
      {==}
    case T.VPair{_n, T.VAots{_a, _b}}:
      {==}
    case T.VPair{_n, T.VPair{_a, _b}}:
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

# appending one value and then a list is appending the list with it in front
def app.snoc(
  aa: List<&2, T.Val>,
  +yy: T.Val,
  +bb: List<&2, T.Val>
) -> {List.append(&2, T.Val, List.append(&2, T.Val, aa, [yy]), bb)
  == List.append(&2, T.Val, aa, yy <> bb) : List<&2, T.Val>}:
  match aa:
    case []:
      {==}
    case hh <> tt:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, ll => hh <> ll,
        List.append(&2, T.Val, List.append(&2, T.Val, tt, [yy]), bb),
        List.append(&2, T.Val, tt, yy <> bb), app.snoc(tt, yy, bb))

# a table's pass onto an accumulator is the pass onto nothing, then the
# accumulator
def go.acc(
  vs: List<&2, T.Val>,
  +acc: List<&2, T.Val>
) -> {T.rows.seal.go(vs, True{}, acc)
  == List.append(&2, T.Val, T.rows.seal.go(vs, True{}, []), acc) : List<&2, T.Val>}:
  match vs:
    case []:
      {==}
    case +xx <> +tt:
      Equal.trans(List<&2, T.Val>,
        T.rows.seal.go(xx <> tt, True{}, acc),
        T.rows.seal.go(tt, True{}, seal.y(xx) <> acc),
        List.append(&2, T.Val, T.rows.seal.go(xx <> tt, True{}, []), acc),
        go.cons(xx, tt, True{}, acc),
        Equal.trans(List<&2, T.Val>,
          T.rows.seal.go(tt, True{}, seal.y(xx) <> acc),
          List.append(&2, T.Val, T.rows.seal.go(tt, True{}, []), seal.y(xx) <> acc),
          List.append(&2, T.Val, T.rows.seal.go(xx <> tt, True{}, []), acc),
          go.acc(tt, seal.y(xx) <> acc),
          Equal.sym(List<&2, T.Val>,
            List.append(&2, T.Val, T.rows.seal.go(xx <> tt, True{}, []), acc),
            List.append(&2, T.Val, T.rows.seal.go(tt, True{}, []), seal.y(xx) <> acc),
            Equal.trans(List<&2, T.Val>,
              List.append(&2, T.Val, T.rows.seal.go(xx <> tt, True{}, []), acc),
              List.append(&2, T.Val, T.rows.seal.go(tt, True{}, [seal.y(xx)]), acc),
              List.append(&2, T.Val, T.rows.seal.go(tt, True{}, []), seal.y(xx) <> acc),
              Equal.cong(List<&2, T.Val>, List<&2, T.Val>, ll => List.append(&2, T.Val, ll, acc),
                T.rows.seal.go(xx <> tt, True{}, []), T.rows.seal.go(tt, True{}, [seal.y(xx)]),
                go.cons(xx, tt, True{}, [])),
              Equal.trans(List<&2, T.Val>,
                List.append(&2, T.Val, T.rows.seal.go(tt, True{}, [seal.y(xx)]), acc),
                List.append(&2, T.Val, List.append(&2, T.Val, T.rows.seal.go(tt, True{}, []),
                  [seal.y(xx)]), acc),
                List.append(&2, T.Val, T.rows.seal.go(tt, True{}, []), seal.y(xx) <> acc),
                Equal.cong(List<&2, T.Val>, List<&2, T.Val>, ll => List.append(&2, T.Val, ll, acc),
                  T.rows.seal.go(tt, True{}, [seal.y(xx)]),
                  List.append(&2, T.Val, T.rows.seal.go(tt, True{}, []), [seal.y(xx)]),
                  go.acc(tt, [seal.y(xx)])),
                app.snoc(T.rows.seal.go(tt, True{}, []), seal.y(xx), acc))))))

# an array's pass keeps the order: it is a table's pass reversed back
def go.false(
  vs: List<&2, T.Val>,
  +acc: List<&2, T.Val>
) -> {T.rows.seal.go(vs, False{}, acc)
  == List.reverse(&2, T.Val, T.rows.seal.go(vs, True{}, acc)) : List<&2, T.Val>}:
  match vs:
    case []:
      {==}
    case +xx <> +tt:
      Equal.trans(List<&2, T.Val>,
        T.rows.seal.go(xx <> tt, False{}, acc),
        T.rows.seal.go(tt, False{}, seal.y(xx) <> acc),
        List.reverse(&2, T.Val, T.rows.seal.go(xx <> tt, True{}, acc)),
        go.cons(xx, tt, False{}, acc),
        Equal.trans(List<&2, T.Val>,
          T.rows.seal.go(tt, False{}, seal.y(xx) <> acc),
          List.reverse(&2, T.Val, T.rows.seal.go(tt, True{}, seal.y(xx) <> acc)),
          List.reverse(&2, T.Val, T.rows.seal.go(xx <> tt, True{}, acc)),
          go.false(tt, seal.y(xx) <> acc),
          Equal.cong(List<&2, T.Val>, List<&2, T.Val>, ll => List.reverse(&2, T.Val, ll),
            T.rows.seal.go(tt, True{}, seal.y(xx) <> acc), T.rows.seal.go(xx <> tt, True{}, acc),
            Equal.sym(List<&2, T.Val>, T.rows.seal.go(xx <> tt, True{}, acc),
              T.rows.seal.go(tt, True{}, seal.y(xx) <> acc), go.cons(xx, tt, True{}, acc)))))

# the value the pass conses is the value sealed
def y.sealed(xx: T.Val) -> {seal.y(xx) == Laws.sealed(xx) : T.Val}:
  match xx:
    case T.VPair{_n, T.VStr{_a}}:
      {==}
    case T.VPair{_n, T.VSpan{_a, _b}}:
      {==}
    case T.VPair{_n, T.VInt{_a, _b}}:
      {==}
    case T.VPair{_n, T.VFlo{_a, _b}}:
      {==}
    case T.VPair{_n, T.VBool{_a}}:
      {==}
    case T.VPair{_n, T.VWhen{_a}}:
      {==}
    case T.VPair{+nn, T.VArr{+items}}:
      Equal.cong(List<&2, T.Val>, T.Val, ii => T.VPair{nn, T.VArr{ii}},
        T.rows.seal.go(items, False{}, []), List.reverse(&2, T.Val, T.rows.seal(items)),
        go.false(items, []))
    case T.VPair{_n, T.VInl{_a}}:
      {==}
    case T.VPair{_n, T.VHead{_a, _b}}:
      {==}
    case T.VPair{_n, T.VAot{_a, _b}}:
      {==}
    case T.VPair{_n, T.VAots{_a, _b}}:
      {==}
    case T.VPair{_n, T.VPair{_a, _b}}:
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
    case T.VArr{+items}:
      Equal.cong(List<&2, T.Val>, T.Val, ii => T.VArr{ii},
        T.rows.seal.go(items, False{}, []), List.reverse(&2, T.Val, T.rows.seal(items)),
        go.false(items, []))
    case T.VInl{_a}:
      {==}
    case T.VHead{_a, _b}:
      {==}
    case T.VAot{_a, _b}:
      {==}
    case T.VAots{_a, _b}:
      {==}

def Laws.seal_puts_newest_last(x, rows):
  Equal.trans(List<&2, T.Val>,
    T.rows.seal.go(x <> rows, True{}, []),
    T.rows.seal.go(rows, True{}, [seal.y(x)]),
    List.append(&2, T.Val, T.rows.seal(rows), [Laws.sealed(x)]),
    go.cons(x, rows, True{}, []),
    Equal.trans(List<&2, T.Val>,
      T.rows.seal.go(rows, True{}, [seal.y(x)]),
      List.append(&2, T.Val, T.rows.seal(rows), [seal.y(x)]),
      List.append(&2, T.Val, T.rows.seal(rows), [Laws.sealed(x)]),
      go.acc(rows, [seal.y(x)]),
      Equal.cong(T.Val, List<&2, T.Val>, yy => List.append(&2, T.Val, T.rows.seal(rows), [yy]),
        seal.y(x), Laws.sealed(x), y.sealed(x))))

# Reading a table back once it is set. rows.repl puts a value in every pair of
# the name, so rows.look, which stops at the first, finds the new value.

# whether rows.look found a pair
def look.some(look: T.Look) -> Bool:
  match look:
    case T.KMiss{}:
      False{}
    case _:
      True{}

# the rest of the rows, as the induction hypothesis
def repl.Ih(+tt: List<&2, T.Val>, +seg: String, +xx: T.Val) -> Type:
  {look.some(T.rows.look(tt, seg)) == True{} : Bool} ->
    {T.rows.look(T.rows.repl(tt, seg, xx), seg) == T.look.of(xx) : T.Look}

# one pair: the name's first pair now holds the new value, and another name's
# pair is passed over on both walks
def repl.look.pair(
  bb: Bool,
  +nn: String,
  vv: T.Val,
  +tt: List<&2, T.Val>,
  +seg: String,
  +xx: T.Val,
  +eb: {T.str.eq(nn, seg) == bb : Bool},
  ee: {look.some(T.look.step(T.str.eq(nn, seg), vv, _u => T.rows.look(tt, seg))) == True{} : Bool},
  ih: repl.Ih(tt, seg, xx)
) -> {T.rows.look(T.rows.repl.step(bb, nn, vv, xx, _u => T.rows.repl(tt, seg, xx)), seg)
  == T.look.of(xx) : T.Look}:
  match bb:
    case True{}:
      Equal.cong(Bool, T.Look,
        cc => T.look.step(cc, xx, _u => T.rows.look(T.rows.repl(tt, seg, xx), seg)),
        T.str.eq(nn, seg), True{}, eb)
    case False{}:
      Equal.trans(T.Look,
        T.look.step(T.str.eq(nn, seg), vv, _u => T.rows.look(T.rows.repl(tt, seg, xx), seg)),
        T.rows.look(T.rows.repl(tt, seg, xx), seg),
        T.look.of(xx),
        Equal.cong(Bool, T.Look,
          cc => T.look.step(cc, vv, _u => T.rows.look(T.rows.repl(tt, seg, xx), seg)),
          T.str.eq(nn, seg), False{}, eb),
        ih(Equal.trans(Bool,
          look.some(T.rows.look(tt, seg)),
          look.some(T.look.step(T.str.eq(nn, seg), vv, _u => T.rows.look(tt, seg))),
          True{},
          Equal.sym(Bool, look.some(T.look.step(T.str.eq(nn, seg), vv, _u => T.rows.look(tt, seg))),
            look.some(T.rows.look(tt, seg)),
            Equal.cong(Bool, Bool, cc => look.some(T.look.step(cc, vv, _u => T.rows.look(tt, seg))),
              T.str.eq(nn, seg), False{}, eb)),
          ee)))

# once a name's pairs are replaced, rows.look finds the new value, by
# induction on the rows
def repl.look(
  rows: List<&2, T.Val>,
  +seg: String,
  +xx: T.Val,
  ee: {look.some(T.rows.look(rows, seg)) == True{} : Bool}
) -> {T.rows.look(T.rows.repl(rows, seg, xx), seg) == T.look.of(xx) : T.Look}:
  match rows:
    case []:
      Eq.bit.absurd(&2, {T.rows.look(T.rows.repl([], seg, xx), seg) == T.look.of(xx) : T.Look}, ee)
    case T.VPair{+nn, vv} <> +tt:
      repl.look.pair(T.str.eq(nn, seg), nn, vv, tt, seg, xx, {==}, ee,
        pp => repl.look(tt, seg, xx, pp))
    case T.VStr{_a} <> tt:
      repl.look(tt, seg, xx, ee)
    case T.VSpan{_a, _b} <> tt:
      repl.look(tt, seg, xx, ee)
    case T.VInt{_a, _b} <> tt:
      repl.look(tt, seg, xx, ee)
    case T.VFlo{_a, _b} <> tt:
      repl.look(tt, seg, xx, ee)
    case T.VBool{_a} <> tt:
      repl.look(tt, seg, xx, ee)
    case T.VWhen{_a} <> tt:
      repl.look(tt, seg, xx, ee)
    case T.VArr{_a} <> tt:
      repl.look(tt, seg, xx, ee)
    case T.VInl{_a} <> tt:
      repl.look(tt, seg, xx, ee)
    case T.VHead{_a, _b} <> tt:
      repl.look(tt, seg, xx, ee)
    case T.VAot{_a, _b} <> tt:
      repl.look(tt, seg, xx, ee)
    case T.VAots{_a, _b} <> tt:
      repl.look(tt, seg, xx, ee)

# what rows.look finds for a name once tb.put.in has set its table
def put.after.last(last: T.Last, +pp: String, child: List<&2, T.Val>) -> T.Look:
  match last:
    case T.LastSome{_q, older, _r}:
      T.KAots{pp, T.VAot{pp, child} <> older}
    case T.LastNo{_why}:
      T.KMiss{}

# what rows.look finds for a name once tb.put.in has set its table
def put.after(look: T.Look, +pre: String, +seg: String, child: List<&2, T.Val>) -> T.Look:
  match look:
    case T.KMiss{}:
      T.KHead{T.tree.pre(pre, seg), child}
    case T.KHead{p, _r}:
      T.KHead{p, child}
    case T.KAots{+p, es}:
      put.after.last(T.look.last(es, p), p, child)
    case _:
      T.KMiss{}

# the newest element of an array of tables, set
def put.look.last(
  last: T.Last,
  +pp: String,
  +rows: List<&2, T.Val>,
  +seg: String,
  +child: List<&2, T.Val>,
  el: {look.some(T.rows.look(rows, seg)) == True{} : Bool},
  ec: {Laws.tb.last.can(last) == True{} : Bool}
) -> {T.rows.look(Laws.tb.last.put(last, seg, rows, pp, child), seg)
  == put.after.last(last, pp, child) : T.Look}:
  match last:
    case T.LastSome{_q, older, _r}:
      repl.look(rows, seg, T.VAots{pp, T.VAot{pp, child} <> older}, el)
    case T.LastNo{why}:
      Eq.bit.absurd(&2, {T.rows.look(Laws.tb.last.put(T.LastNo{why}, seg, rows, pp, child), seg)
        == put.after.last(T.LastNo{why}, pp, child) : T.Look}, ec)

# a table set by tb.put.in is what rows.look then finds for its name
def put.look(
  +look: T.Look,
  +rows: List<&2, T.Val>,
  +seg: String,
  +pre: String,
  +child: List<&2, T.Val>,
  el: {T.rows.look(rows, seg) == look : T.Look},
  ec: {Laws.tb.can(look) == True{} : Bool}
) -> {T.rows.look(Laws.tb.put.in(look, seg, rows, pre, child), seg)
  == put.after(look, pre, seg, child) : T.Look}:
  match look:
    case T.KMiss{}:
      Equal.cong(Bool, T.Look,
        cc => T.look.step(cc, T.VHead{T.tree.pre(pre, seg), child}, _u => T.rows.look(rows, seg)),
        T.str.eq(seg, seg), True{}, str.eq.self(seg))
    case T.KHead{+p, rr}:
      repl.look(rows, seg, T.VHead{p, child},
        Equal.cong(T.Look, Bool, ll => look.some(ll), T.rows.look(rows, seg), T.KHead{p, rr}, el))
    case T.KAots{+p, +es}:
      put.look.last(T.look.last(es, p), p, rows, seg, child,
        Equal.cong(T.Look, Bool, ll => look.some(ll), T.rows.look(rows, seg), T.KAots{p, es}, el), ec)
    case T.KInl{}:
      Eq.bit.absurd(&2, {T.rows.look(Laws.tb.put.in(T.KInl{}, seg, rows, pre, child), seg)
        == put.after(T.KInl{}, pre, seg, child) : T.Look}, ec)
    case T.KNo{why}:
      Eq.bit.absurd(&2, {T.rows.look(Laws.tb.put.in(T.KNo{why}, seg, rows, pre, child), seg)
        == put.after(T.KNo{why}, pre, seg, child) : T.Look}, ec)

# the newest element, set, holds the child
def after.last.into(
  last: T.Last,
  +pp: String,
  +child: List<&2, T.Val>,
  ec: {Laws.tb.last.can(last) == True{} : Bool}
) -> {Laws.tb.into(put.after.last(last, pp, child)) == child : List<&2, T.Val>}:
  match last:
    case T.LastSome{_q, _older, _r}:
      {==}
    case T.LastNo{why}:
      Eq.bit.absurd(&2, {Laws.tb.into(put.after.last(T.LastNo{why}, pp, child)) == child
        : List<&2, T.Val>}, ec)

# a table set holds the child
def after.into(
  +look: T.Look,
  +pre: String,
  +seg: String,
  +child: List<&2, T.Val>,
  ec: {Laws.tb.can(look) == True{} : Bool}
) -> {Laws.tb.into(put.after(look, pre, seg, child)) == child : List<&2, T.Val>}:
  match look:
    case T.KMiss{}:
      {==}
    case T.KHead{_p, _r}:
      {==}
    case T.KAots{+p, es}:
      after.last.into(T.look.last(es, p), p, child, ec)
    case T.KInl{}:
      Eq.bit.absurd(&2, {Laws.tb.into(put.after(T.KInl{}, pre, seg, child)) == child
        : List<&2, T.Val>}, ec)
    case T.KNo{why}:
      Eq.bit.absurd(&2, {Laws.tb.into(put.after(T.KNo{why}, pre, seg, child)) == child
        : List<&2, T.Val>}, ec)

# the newest element, set, can be entered
def after.last.can(
  last: T.Last,
  +pp: String,
  +child: List<&2, T.Val>,
  ec: {Laws.tb.last.can(last) == True{} : Bool}
) -> {Laws.tb.can(put.after.last(last, pp, child)) == True{} : Bool}:
  match last:
    case T.LastSome{_q, _older, _r}:
      {==}
    case T.LastNo{why}:
      Eq.bit.absurd(&2, {Laws.tb.can(put.after.last(T.LastNo{why}, pp, child)) == True{} : Bool}, ec)

# a table set can be entered
def after.can(
  +look: T.Look,
  +pre: String,
  +seg: String,
  +child: List<&2, T.Val>,
  ec: {Laws.tb.can(look) == True{} : Bool}
) -> {Laws.tb.can(put.after(look, pre, seg, child)) == True{} : Bool}:
  match look:
    case T.KMiss{}:
      {==}
    case T.KHead{_p, _r}:
      {==}
    case T.KAots{+p, es}:
      after.last.can(T.look.last(es, p), p, child, ec)
    case T.KInl{}:
      Eq.bit.absurd(&2, {Laws.tb.can(put.after(T.KInl{}, pre, seg, child)) == True{} : Bool}, ec)
    case T.KNo{why}:
      Eq.bit.absurd(&2, {Laws.tb.can(put.after(T.KNo{why}, pre, seg, child)) == True{} : Bool}, ec)

# by induction on the path: each segment finds the table it set
def Laws.tb_rows_after_set(path, pre, rows, new, eo):
  match path:
    case []:
      {==}
    case +seg <> +rest:
      Equal.trans(List<&2, T.Val>,
        Laws.tb.rows(rest, Laws.tb.into(T.rows.look(Laws.tb.put.in(T.rows.look(rows, seg), seg, rows,
          pre, Laws.tb.set(rest, T.tree.pre(pre, seg), Laws.tb.into(T.rows.look(rows, seg)), new)),
          seg))),
        Laws.tb.rows(rest, Laws.tb.set(rest, T.tree.pre(pre, seg), Laws.tb.into(T.rows.look(rows,
          seg)), new)),
        new,
        Equal.cong(List<&2, T.Val>, List<&2, T.Val>, xx => Laws.tb.rows(rest, xx),
          Laws.tb.into(T.rows.look(Laws.tb.put.in(T.rows.look(rows, seg), seg, rows, pre,
            Laws.tb.set(rest, T.tree.pre(pre, seg), Laws.tb.into(T.rows.look(rows, seg)), new)),
            seg)),
          Laws.tb.set(rest, T.tree.pre(pre, seg), Laws.tb.into(T.rows.look(rows, seg)), new),
          Equal.trans(List<&2, T.Val>,
            Laws.tb.into(T.rows.look(Laws.tb.put.in(T.rows.look(rows, seg), seg, rows, pre,
              Laws.tb.set(rest, T.tree.pre(pre, seg), Laws.tb.into(T.rows.look(rows, seg)), new)),
              seg)),
            Laws.tb.into(put.after(T.rows.look(rows, seg), pre, seg, Laws.tb.set(rest,
              T.tree.pre(pre, seg), Laws.tb.into(T.rows.look(rows, seg)), new))),
            Laws.tb.set(rest, T.tree.pre(pre, seg), Laws.tb.into(T.rows.look(rows, seg)), new),
            Equal.cong(T.Look, List<&2, T.Val>, ll => Laws.tb.into(ll),
              T.rows.look(Laws.tb.put.in(T.rows.look(rows, seg), seg, rows, pre,
                Laws.tb.set(rest, T.tree.pre(pre, seg), Laws.tb.into(T.rows.look(rows, seg)), new)),
                seg),
              put.after(T.rows.look(rows, seg), pre, seg, Laws.tb.set(rest, T.tree.pre(pre, seg),
                Laws.tb.into(T.rows.look(rows, seg)), new)),
              put.look(T.rows.look(rows, seg), rows, seg, pre, Laws.tb.set(rest, T.tree.pre(pre, seg),
                Laws.tb.into(T.rows.look(rows, seg)), new), {==},
                Eq.and.left(Laws.tb.can(T.rows.look(rows, seg)),
                  Laws.tb.open(rest, Laws.tb.into(T.rows.look(rows, seg))), eo))),
            after.into(T.rows.look(rows, seg), pre, seg, Laws.tb.set(rest, T.tree.pre(pre, seg),
              Laws.tb.into(T.rows.look(rows, seg)), new),
              Eq.and.left(Laws.tb.can(T.rows.look(rows, seg)),
                Laws.tb.open(rest, Laws.tb.into(T.rows.look(rows, seg))), eo)))),
        Laws.tb_rows_after_set(rest, T.tree.pre(pre, seg), Laws.tb.into(T.rows.look(rows, seg)), new,
          Eq.and.right(Laws.tb.can(T.rows.look(rows, seg)),
            Laws.tb.open(rest, Laws.tb.into(T.rows.look(rows, seg))), eo)))

# by induction on the path: each segment can still be entered, and leads to
# the table it set
def Laws.tb_open_after_set(path, pre, rows, new, eo):
  match path:
    case []:
      {==}
    case +seg <> +rest:
      Equal.trans(Bool,
        Bool.and(Laws.tb.can(T.rows.look(Laws.tb.put.in(T.rows.look(rows, seg), seg, rows, pre,
          Laws.tb.set(rest, T.tree.pre(pre, seg), Laws.tb.into(T.rows.look(rows, seg)), new)), seg)),
          Laws.tb.open(rest, Laws.tb.into(T.rows.look(Laws.tb.put.in(T.rows.look(rows, seg), seg,
            rows, pre, Laws.tb.set(rest, T.tree.pre(pre, seg), Laws.tb.into(T.rows.look(rows, seg)),
              new)), seg)))),
        Bool.and(Laws.tb.can(put.after(T.rows.look(rows, seg), pre, seg, Laws.tb.set(rest,
          T.tree.pre(pre, seg), Laws.tb.into(T.rows.look(rows, seg)), new))),
          Laws.tb.open(rest, Laws.tb.into(put.after(T.rows.look(rows, seg), pre, seg,
            Laws.tb.set(rest, T.tree.pre(pre, seg), Laws.tb.into(T.rows.look(rows, seg)), new))))),
        True{},
        Equal.cong(T.Look, Bool, ll => Bool.and(Laws.tb.can(ll), Laws.tb.open(rest, Laws.tb.into(ll))),
          T.rows.look(Laws.tb.put.in(T.rows.look(rows, seg), seg, rows, pre,
            Laws.tb.set(rest, T.tree.pre(pre, seg), Laws.tb.into(T.rows.look(rows, seg)), new)), seg),
          put.after(T.rows.look(rows, seg), pre, seg, Laws.tb.set(rest, T.tree.pre(pre, seg),
            Laws.tb.into(T.rows.look(rows, seg)), new)),
          put.look(T.rows.look(rows, seg), rows, seg, pre, Laws.tb.set(rest, T.tree.pre(pre, seg),
            Laws.tb.into(T.rows.look(rows, seg)), new), {==},
            Eq.and.left(Laws.tb.can(T.rows.look(rows, seg)),
              Laws.tb.open(rest, Laws.tb.into(T.rows.look(rows, seg))), eo))),
        Equal.trans(Bool,
          Bool.and(Laws.tb.can(put.after(T.rows.look(rows, seg), pre, seg, Laws.tb.set(rest,
            T.tree.pre(pre, seg), Laws.tb.into(T.rows.look(rows, seg)), new))),
            Laws.tb.open(rest, Laws.tb.into(put.after(T.rows.look(rows, seg), pre, seg,
              Laws.tb.set(rest, T.tree.pre(pre, seg), Laws.tb.into(T.rows.look(rows, seg)), new))))),
          Laws.tb.open(rest, Laws.tb.into(put.after(T.rows.look(rows, seg), pre, seg,
            Laws.tb.set(rest, T.tree.pre(pre, seg), Laws.tb.into(T.rows.look(rows, seg)), new)))),
          True{},
          Equal.cong(Bool, Bool,
            bb => Bool.and(bb, Laws.tb.open(rest, Laws.tb.into(put.after(T.rows.look(rows, seg), pre,
              seg, Laws.tb.set(rest, T.tree.pre(pre, seg), Laws.tb.into(T.rows.look(rows, seg)),
                new))))),
            Laws.tb.can(put.after(T.rows.look(rows, seg), pre, seg, Laws.tb.set(rest,
              T.tree.pre(pre, seg), Laws.tb.into(T.rows.look(rows, seg)), new))),
            True{},
            after.can(T.rows.look(rows, seg), pre, seg, Laws.tb.set(rest, T.tree.pre(pre, seg),
              Laws.tb.into(T.rows.look(rows, seg)), new),
              Eq.and.left(Laws.tb.can(T.rows.look(rows, seg)),
                Laws.tb.open(rest, Laws.tb.into(T.rows.look(rows, seg))), eo))),
          Equal.trans(Bool,
            Laws.tb.open(rest, Laws.tb.into(put.after(T.rows.look(rows, seg), pre, seg,
              Laws.tb.set(rest, T.tree.pre(pre, seg), Laws.tb.into(T.rows.look(rows, seg)), new)))),
            Laws.tb.open(rest, Laws.tb.set(rest, T.tree.pre(pre, seg),
              Laws.tb.into(T.rows.look(rows, seg)), new)),
            True{},
            Equal.cong(List<&2, T.Val>, Bool, xx => Laws.tb.open(rest, xx),
              Laws.tb.into(put.after(T.rows.look(rows, seg), pre, seg, Laws.tb.set(rest,
                T.tree.pre(pre, seg), Laws.tb.into(T.rows.look(rows, seg)), new))),
              Laws.tb.set(rest, T.tree.pre(pre, seg), Laws.tb.into(T.rows.look(rows, seg)), new),
              after.into(T.rows.look(rows, seg), pre, seg, Laws.tb.set(rest, T.tree.pre(pre, seg),
                Laws.tb.into(T.rows.look(rows, seg)), new),
                Eq.and.left(Laws.tb.can(T.rows.look(rows, seg)),
                  Laws.tb.open(rest, Laws.tb.into(T.rows.look(rows, seg))), eo))),
            Laws.tb_open_after_set(rest, T.tree.pre(pre, seg), Laws.tb.into(T.rows.look(rows, seg)),
              new, Eq.and.right(Laws.tb.can(T.rows.look(rows, seg)),
                Laws.tb.open(rest, Laws.tb.into(T.rows.look(rows, seg))), eo)))))

# WP-H: headers read back. A header is read one segment at a time: a bare
# segment's characters are pushed onto the buffer in LHead, a quoted one is
# read by WP0's quoted-segment family at hd = True, and the dot or bracket
# after it pushes the segment onto parts. The closing bracket runs the walk,
# which the law takes as a premise (WP-W's contracts discharge it), and the
# newline returns to the start of a line. Every lemma takes the rest of the
# text as read from every back and qkind, as qs.escs does.

# a scanner inside a header: the segments read so far in parts, newest
# first, and the open bare segment reversed in buf
def wh.st(
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  parts: List<&2, String>,
  buf: List<&2, Char>,
  lex: T.Lex,
  back: T.Lex,
  qkind: T.QKind,
  arrtab: Bool
) -> T.St:
  T.St{"", rows, heads, here, parts, buf, lex, back, qkind, [], T.HNone{}, 0, 0, arrtab,
    False{}}

# where a segment starts: right after the bracket, or after a dot
def wh.lex0(dt: Bool) -> T.Lex:
  match dt:
    case False{}:
      T.LHead{}
    case True{}:
      T.LHeadDot{}

# the segments before it: none right after the bracket
def wh.ps(dt: Bool, parts: List<&2, String>) -> List<&2, String>:
  match dt:
    case False{}:
      []
    case True{}:
      parts

# what follows a segment: a dot, or the closing bracket
def wh.dl(cl: Bool) -> Char:
  match cl:
    case False{}:
      '.'
    case True{}:
      ']'

# the scanner after a segment and what follows it: waiting for the next
# segment after a dot, or closed after the bracket
def wh.aft(
  cl: Bool,
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  parts: List<&2, String>,
  back: T.Lex,
  qkind: T.QKind,
  +arrtab: Bool
) -> T.St:
  match cl:
    case False{}:
      wh.st(rows, heads, here, parts, [], T.LHeadDot{}, back, qkind, arrtab)
    case True{}:
      T.read.once2(T.lex.head.close2(arrtab, wh.st(rows, heads, here, parts, [],
        T.LHeadGap{}, back, qkind, arrtab)))

# the rest of the text after a segment, read from every back and qkind
def wh.Then(
  cl: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +arrtab: Bool,
  +rest: String,
  +goal: T.Doc
) -> Type:
  @bk: T.Lex -> @qk: T.QKind ->
    {T.doc.read(rest, T.MScan{wh.aft(cl, rows, heads, here, parts, bk, qk, arrtab)}) == goal
      : T.Doc}

# in a header, a bare character is no second bracket and so is a key character
def wh.go.bare(
  br: Bool,
  bare: Bool,
  sp: Bool,
  dot: Bool,
  end: Bool,
  qq: Bool,
  lit: Bool,
  hash: Bool,
  st: T.St,
  +xx: U32,
  ebr: {Char.is_eq(Chr{xx}, '[') == br : Bool},
  ebare: {T.bare.at(Chr{xx}) == bare : Bool},
  +ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.lex.head.go(br, bare, sp, dot, end, qq, lit, hash, st, Chr{xx})
  == T.lex.head.ch(st, Chr{xx}) : T.St}:
  match br:
    case True{}:
      Eq.bit.gone(&2, {T.lex.head.go(True{}, bare, sp, dot, end, qq, lit, hash, st, Chr{xx})
        == T.lex.head.ch(st, Chr{xx}) : T.St},
        Eq.refute_char(Chr{xx}, '[', ch => T.bare.at(ch), ebr, ee, {==}))
    case False{}:
      match bare:
        case True{}:
          {==}
        case False{}:
          clash(&2, {T.lex.head.go(False{}, False{}, sp, dot, end, qq, lit, hash, st, Chr{xx})
            == T.lex.head.ch(st, Chr{xx}) : T.St},
            Equal.trans(Bool, False{}, T.bare.at(Chr{xx}), True{},
              Equal.sym(Bool, T.bare.at(Chr{xx}), False{}, ebare), ee))

# after a dot, a bare character is no blank and so starts a bare segment
def wh.dot.bare(
  sp: Bool,
  bare: Bool,
  qq: Bool,
  lit: Bool,
  st: T.St,
  +xx: U32,
  esp: {T.ch.sp(Chr{xx}) == sp : Bool},
  ebare: {T.bare.at(Chr{xx}) == bare : Bool},
  +ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.lex.hdot(sp, bare, qq, lit, st, Chr{xx}) == T.st.push(st, Chr{xx}, T.LHead{}) : T.St}:
  match sp:
    case True{}:
      Eq.bit.gone(&2, {T.lex.hdot(True{}, bare, qq, lit, st, Chr{xx})
        == T.st.push(st, Chr{xx}, T.LHead{}) : T.St},
        or2.no(xx, 32, 9, U32.is_eq(xx, 32), U32.is_eq(xx, 9), {==}, {==}, esp,
          ch => T.bare.at(ch), ee, {==}, {==}))
    case False{}:
      match bare:
        case True{}:
          {==}
        case False{}:
          clash(&2, {T.lex.hdot(False{}, False{}, qq, lit, st, Chr{xx})
            == T.st.push(st, Chr{xx}, T.LHead{}) : T.St},
            Equal.trans(Bool, False{}, T.bare.at(Chr{xx}), True{},
              Equal.sym(Bool, T.bare.at(Chr{xx}), False{}, ebare), ee))

# the first character of a bare segment starts its buffer
def wh.b1.fast(
  dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +xx: U32,
  +ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.read.fast(wh.st(rows, heads, here, wh.ps(dt, parts), [], wh.lex0(dt), back, qkind,
  arrtab), Chr{xx}) == wh.st(rows, heads, here, wh.ps(dt, parts), [Chr{xx}], T.LHead{}, back,
  qkind, arrtab) : T.St}:
  match dt:
    case False{}:
      Equal.cong(T.St, T.St, st => T.read.once2(st),
        T.lex.head.go(Char.is_eq(Chr{xx}, '['), T.bare.at(Chr{xx}), T.ch.sp(Chr{xx}),
          Char.is_eq(Chr{xx}, '.'), Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '"'),
          Char.is_eq(Chr{xx}, '\''), Char.is_eq(Chr{xx}, '#'),
          wh.st(rows, heads, here, [], [], T.LHead{}, back, qkind, arrtab), Chr{xx}),
        T.lex.head.ch(wh.st(rows, heads, here, [], [], T.LHead{}, back, qkind, arrtab),
          Chr{xx}),
        wh.go.bare(Char.is_eq(Chr{xx}, '['), T.bare.at(Chr{xx}), T.ch.sp(Chr{xx}),
          Char.is_eq(Chr{xx}, '.'), Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '"'),
          Char.is_eq(Chr{xx}, '\''), Char.is_eq(Chr{xx}, '#'),
          wh.st(rows, heads, here, [], [], T.LHead{}, back, qkind, arrtab), xx, {==}, {==},
          ee))
    case True{}:
      Equal.cong(T.St, T.St, st => T.read.once2(st),
        T.lex.hdot(T.ch.sp(Chr{xx}), T.bare.at(Chr{xx}), Char.is_eq(Chr{xx}, '"'),
          Char.is_eq(Chr{xx}, '\''),
          wh.st(rows, heads, here, parts, [], T.LHeadDot{}, back, qkind, arrtab), Chr{xx}),
        T.st.push(wh.st(rows, heads, here, parts, [], T.LHeadDot{}, back, qkind, arrtab),
          Chr{xx}, T.LHead{}),
        wh.dot.bare(T.ch.sp(Chr{xx}), T.bare.at(Chr{xx}), Char.is_eq(Chr{xx}, '"'),
          Char.is_eq(Chr{xx}, '\''),
          wh.st(rows, heads, here, parts, [], T.LHeadDot{}, back, qkind, arrtab), xx, {==},
          {==}, ee))

# and the scan mode sends it there
def wh.b1(
  +dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +xx: U32,
  +ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.doc.scan(wh.st(rows, heads, here, wh.ps(dt, parts), [], wh.lex0(dt), back, qkind,
  arrtab), Chr{xx}) == T.MScan{wh.st(rows, heads, here, wh.ps(dt, parts), [Chr{xx}], T.LHead{},
  back, qkind, arrtab)} : T.Mode}:
  Equal.trans(T.Mode,
    T.doc.scan(wh.st(rows, heads, here, wh.ps(dt, parts), [], wh.lex0(dt), back, qkind,
      arrtab), Chr{xx}),
    T.MScan{T.read.fast(wh.st(rows, heads, here, wh.ps(dt, parts), [], wh.lex0(dt), back,
      qkind, arrtab), Chr{xx})},
    T.MScan{wh.st(rows, heads, here, wh.ps(dt, parts), [Chr{xx}], T.LHead{}, back, qkind,
      arrtab)},
    scan.other(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), U32.is_eq(xx, 13),
      wh.st(rows, heads, here, wh.ps(dt, parts), [], wh.lex0(dt), back, qkind, arrtab),
      Chr{xx}, {==}, {==}, {==}, ch => T.bare.at(ch), ee, {==}, {==}, {==}),
    Equal.cong(T.St, T.Mode, st => T.MScan{st},
      T.read.fast(wh.st(rows, heads, here, wh.ps(dt, parts), [], wh.lex0(dt), back, qkind,
        arrtab), Chr{xx}),
      wh.st(rows, heads, here, wh.ps(dt, parts), [Chr{xx}], T.LHead{}, back, qkind, arrtab),
      wh.b1.fast(dt, rows, heads, here, parts, back, qkind, arrtab, xx, ee)))

# with a segment open, the next bare character joins it, whatever came before
def wh.ch.later(
  parts: List<&2, String>,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +dd: Char,
  +bb: List<&2, Char>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +cc: Char
) -> {T.read.once2(T.lex.head.ch(wh.st(rows, heads, here, parts, dd <> bb, T.LHead{}, back,
  qkind, arrtab), cc)) == wh.st(rows, heads, here, parts, cc <> dd <> bb, T.LHead{}, back,
  qkind, arrtab) : T.St}:
  match parts:
    case []:
      {==}
    case _p <> _ps:
      {==}

# a later character of a bare segment, from the scan mode
def wh.b2(
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +dd: Char,
  +bb: List<&2, Char>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +xx: U32,
  +ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.doc.scan(wh.st(rows, heads, here, parts, dd <> bb, T.LHead{}, back, qkind, arrtab),
  Chr{xx}) == T.MScan{wh.st(rows, heads, here, parts, Chr{xx} <> dd <> bb, T.LHead{}, back,
  qkind, arrtab)} : T.Mode}:
  Equal.trans(T.Mode,
    T.doc.scan(wh.st(rows, heads, here, parts, dd <> bb, T.LHead{}, back, qkind, arrtab),
      Chr{xx}),
    T.MScan{T.read.fast(wh.st(rows, heads, here, parts, dd <> bb, T.LHead{}, back, qkind,
      arrtab), Chr{xx})},
    T.MScan{wh.st(rows, heads, here, parts, Chr{xx} <> dd <> bb, T.LHead{}, back, qkind,
      arrtab)},
    scan.other(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), U32.is_eq(xx, 13),
      wh.st(rows, heads, here, parts, dd <> bb, T.LHead{}, back, qkind, arrtab),
      Chr{xx}, {==}, {==}, {==}, ch => T.bare.at(ch), ee, {==}, {==}, {==}),
    Equal.cong(T.St, T.Mode, st => T.MScan{st},
      T.read.fast(wh.st(rows, heads, here, parts, dd <> bb, T.LHead{}, back, qkind, arrtab),
        Chr{xx}),
      wh.st(rows, heads, here, parts, Chr{xx} <> dd <> bb, T.LHead{}, back, qkind, arrtab),
      Equal.trans(T.St,
        T.read.once2(T.lex.head.go(Char.is_eq(Chr{xx}, '['), T.bare.at(Chr{xx}),
          T.ch.sp(Chr{xx}), Char.is_eq(Chr{xx}, '.'), Char.is_eq(Chr{xx}, ']'),
          Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), Char.is_eq(Chr{xx}, '#'),
          wh.st(rows, heads, here, parts, dd <> bb, T.LHead{}, back, qkind, arrtab), Chr{xx})),
        T.read.once2(T.lex.head.ch(wh.st(rows, heads, here, parts, dd <> bb, T.LHead{}, back,
          qkind, arrtab), Chr{xx})),
        wh.st(rows, heads, here, parts, Chr{xx} <> dd <> bb, T.LHead{}, back, qkind, arrtab),
        Equal.cong(T.St, T.St, st => T.read.once2(st),
          T.lex.head.go(Char.is_eq(Chr{xx}, '['), T.bare.at(Chr{xx}), T.ch.sp(Chr{xx}),
            Char.is_eq(Chr{xx}, '.'), Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '"'),
            Char.is_eq(Chr{xx}, '\''), Char.is_eq(Chr{xx}, '#'),
            wh.st(rows, heads, here, parts, dd <> bb, T.LHead{}, back, qkind, arrtab),
            Chr{xx}),
          T.lex.head.ch(wh.st(rows, heads, here, parts, dd <> bb, T.LHead{}, back, qkind,
            arrtab), Chr{xx}),
          wh.go.bare(Char.is_eq(Chr{xx}, '['), T.bare.at(Chr{xx}), T.ch.sp(Chr{xx}),
            Char.is_eq(Chr{xx}, '.'), Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '"'),
            Char.is_eq(Chr{xx}, '\''), Char.is_eq(Chr{xx}, '#'),
            wh.st(rows, heads, here, parts, dd <> bb, T.LHead{}, back, qkind, arrtab), xx,
            {==}, {==}, ee)),
        wh.ch.later(parts, rows, heads, here, dd, bb, back, qkind, arrtab, Chr{xx}))))

# the rest of a bare segment is pushed onto its buffer, whatever follows it
def wh.bbody(
  ks: String,
  +rr: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +dd: Char,
  +bb: List<&2, Char>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +ee: {T.bare.all(String.to_list(ks)) == True{} : Bool}
) -> {T.doc.read(String.append(ks, rr), T.MScan{wh.st(rows, heads, here, parts, dd <> bb,
  T.LHead{}, back, qkind, arrtab)}) == T.doc.read(rr, T.MScan{wh.st(rows, heads, here, parts,
  rev.onto(ks, dd <> bb), T.LHead{}, back, qkind, arrtab)}) : T.Doc}:
  match ks:
    case SNil{}:
      {==}
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          Equal.trans(T.Doc,
            T.doc.read(String.append(tt, rr), T.doc.scan(wh.st(rows, heads, here, parts,
              dd <> bb, T.LHead{}, back, qkind, arrtab), Chr{xx})),
            T.doc.read(String.append(tt, rr), T.MScan{wh.st(rows, heads, here, parts,
              Chr{xx} <> dd <> bb, T.LHead{}, back, qkind, arrtab)}),
            T.doc.read(rr, T.MScan{wh.st(rows, heads, here, parts,
              rev.onto(tt, Chr{xx} <> dd <> bb), T.LHead{}, back, qkind, arrtab)}),
            Equal.cong(T.Mode, T.Doc, md => T.doc.read(String.append(tt, rr), md),
              T.doc.scan(wh.st(rows, heads, here, parts, dd <> bb, T.LHead{}, back, qkind,
                arrtab), Chr{xx}),
              T.MScan{wh.st(rows, heads, here, parts, Chr{xx} <> dd <> bb, T.LHead{}, back,
                qkind, arrtab)},
              wh.b2(rows, heads, here, parts, dd, bb, back, qkind, arrtab, xx,
                ball.head(T.bare.at(Chr{xx}), String.to_list(tt), ee))),
            wh.bbody(tt, rr, rows, heads, here, parts, Chr{xx}, dd <> bb, back, qkind, arrtab,
              ball.tail(T.bare.at(Chr{xx}), String.to_list(tt), ee)))

# the bracket closes the header the same way whatever state the last segment
# ended in
def wh.lexfree(
  arrtab: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +pp: String,
  +ps: List<&2, String>,
  +lx: T.Lex,
  +back: T.Lex,
  +qkind: T.QKind
) -> {T.read.once2(T.lex.head.close2(arrtab, wh.st(rows, heads, here, pp <> ps, [], lx, back,
  qkind, arrtab))) == T.read.once2(T.lex.head.close2(arrtab, wh.st(rows, heads, here, pp <> ps,
  [], T.LHeadGap{}, back, qkind, arrtab))) : T.St}:
  match arrtab:
    case False{}:
      {==}
    case True{}:
      {==}

# a dot or the bracket ends an open bare segment and pushes it
def wh.bdl(
  cl: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +bf: List<&2, Char>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +rest: String,
  full: {List.is_empty(&2, Char, bf) == False{} : Bool}
) -> {T.doc.read(SCon{wh.dl(cl), rest}, T.MScan{wh.st(rows, heads, here, parts, bf, T.LHead{},
  back, qkind, arrtab)}) == T.doc.read(rest, T.MScan{wh.aft(cl, rows, heads, here,
  T.buf.str(bf) <> parts, back, qkind, arrtab)}) : T.Doc}:
  match cl:
    case False{}:
      Equal.cong(Bool, T.Doc,
        bt => T.doc.read(rest, T.MScan{T.read.once2(T.lex.head.dot3(bt, wh.st(rows, heads,
          here, parts, bf, T.LHead{}, back, qkind, arrtab)))}),
        List.is_empty(&2, Char, bf), False{}, full)
    case True{}:
      Equal.trans(T.Doc,
        T.doc.read(rest, T.MScan{T.read.once2(T.lex.head.close.go(List.is_empty(&2, Char, bf),
          arrtab, wh.st(rows, heads, here, parts, bf, T.LHead{}, back, qkind, arrtab)))}),
        T.doc.read(rest, T.MScan{T.read.once2(T.lex.head.close.go(False{}, arrtab,
          wh.st(rows, heads, here, parts, bf, T.LHead{}, back, qkind, arrtab)))}),
        T.doc.read(rest, T.MScan{wh.aft(True{}, rows, heads, here, T.buf.str(bf) <> parts, back,
          qkind, arrtab)}),
        Equal.cong(Bool, T.Doc,
          bt => T.doc.read(rest, T.MScan{T.read.once2(T.lex.head.close.go(bt, arrtab,
            wh.st(rows, heads, here, parts, bf, T.LHead{}, back, qkind, arrtab)))}),
          List.is_empty(&2, Char, bf), False{}, full),
        Equal.cong(T.St, T.Doc, st => T.doc.read(rest, T.MScan{st}),
          T.read.once2(T.lex.head.close2(arrtab, wh.st(rows, heads, here, T.buf.str(bf) <> parts,
            [], T.LHead{}, back, qkind, arrtab))),
          T.read.once2(T.lex.head.close2(arrtab, wh.st(rows, heads, here, T.buf.str(bf) <> parts,
            [], T.LHeadGap{}, back, qkind, arrtab))),
          wh.lexfree(arrtab, rows, heads, here, T.buf.str(bf), parts, T.LHead{}, back, qkind)))

# a bare segment's buffer reads back as its characters
def wh.bname(
  +xx: U32,
  +tt: String
) -> {T.buf.str(rev.onto(tt, [Chr{xx}])) == SCon{Chr{xx}, tt} : String}:
  Equal.trans(String, T.buf.str.go(rev.onto(tt, [Chr{xx}]), ""),
    T.buf.str.go([Chr{xx}], String.append(tt, "")), SCon{Chr{xx}, tt},
    ml.rev(tt, [Chr{xx}], ""),
    Equal.cong(String, String, zz => SCon{Chr{xx}, zz}, String.append(tt, ""), tt,
      Eq.append_nil(tt)))

# a bare segment and the dot or bracket after it: the rest is read with the
# segment pushed, and back and qkind as they were
def wh.bseg(
  +xx: U32,
  +tt: String,
  +cl: Bool,
  +dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +rest: String,
  +goal: T.Doc,
  +ee: {T.bare.all.step(T.bare.at(Chr{xx}), _u => T.bare.all(String.to_list(tt))) == True{} : Bool},
  ih: wh.Then(cl, rows, heads, here, SCon{Chr{xx}, tt} <> wh.ps(dt, parts), arrtab, rest, goal)
) -> {T.doc.read(String.append(SCon{Chr{xx}, tt}, SCon{wh.dl(cl), rest}), T.MScan{wh.st(rows,
  heads, here, wh.ps(dt, parts), [], wh.lex0(dt), back, qkind, arrtab)}) == goal : T.Doc}:
  Equal.trans(T.Doc,
    T.doc.read(String.append(tt, SCon{wh.dl(cl), rest}), T.doc.scan(wh.st(rows, heads, here,
      wh.ps(dt, parts), [], wh.lex0(dt), back, qkind, arrtab), Chr{xx})),
    T.doc.read(String.append(tt, SCon{wh.dl(cl), rest}), T.MScan{wh.st(rows, heads, here,
      wh.ps(dt, parts), [Chr{xx}], T.LHead{}, back, qkind, arrtab)}),
    goal,
    Equal.cong(T.Mode, T.Doc, md => T.doc.read(String.append(tt, SCon{wh.dl(cl), rest}), md),
      T.doc.scan(wh.st(rows, heads, here, wh.ps(dt, parts), [], wh.lex0(dt), back, qkind,
        arrtab), Chr{xx}),
      T.MScan{wh.st(rows, heads, here, wh.ps(dt, parts), [Chr{xx}], T.LHead{}, back, qkind,
        arrtab)},
      wh.b1(dt, rows, heads, here, parts, back, qkind, arrtab, xx,
        ball.head(T.bare.at(Chr{xx}), String.to_list(tt), ee))),
    Equal.trans(T.Doc,
      T.doc.read(String.append(tt, SCon{wh.dl(cl), rest}), T.MScan{wh.st(rows, heads, here,
        wh.ps(dt, parts), [Chr{xx}], T.LHead{}, back, qkind, arrtab)}),
      T.doc.read(SCon{wh.dl(cl), rest}, T.MScan{wh.st(rows, heads, here, wh.ps(dt, parts),
        rev.onto(tt, [Chr{xx}]), T.LHead{}, back, qkind, arrtab)}),
      goal,
      wh.bbody(tt, SCon{wh.dl(cl), rest}, rows, heads, here, wh.ps(dt, parts), Chr{xx}, [],
        back, qkind, arrtab, ball.tail(T.bare.at(Chr{xx}), String.to_list(tt), ee)),
      Equal.trans(T.Doc,
        T.doc.read(SCon{wh.dl(cl), rest}, T.MScan{wh.st(rows, heads, here, wh.ps(dt, parts),
          rev.onto(tt, [Chr{xx}]), T.LHead{}, back, qkind, arrtab)}),
        T.doc.read(rest, T.MScan{wh.aft(cl, rows, heads, here,
          T.buf.str(rev.onto(tt, [Chr{xx}])) <> wh.ps(dt, parts), back, qkind, arrtab)}),
        goal,
        wh.bdl(cl, rows, heads, here, wh.ps(dt, parts), rev.onto(tt, [Chr{xx}]), back, qkind,
          arrtab, rest, rev.full(tt, Chr{xx}, [])),
        Equal.trans(T.Doc,
          T.doc.read(rest, T.MScan{wh.aft(cl, rows, heads, here,
            T.buf.str(rev.onto(tt, [Chr{xx}])) <> wh.ps(dt, parts), back, qkind, arrtab)}),
          T.doc.read(rest, T.MScan{wh.aft(cl, rows, heads, here,
            SCon{Chr{xx}, tt} <> wh.ps(dt, parts), back, qkind, arrtab)}),
          goal,
          Equal.cong(String, T.Doc, nm => T.doc.read(rest, T.MScan{wh.aft(cl, rows, heads,
            here, nm <> wh.ps(dt, parts), back, qkind, arrtab)}),
            T.buf.str(rev.onto(tt, [Chr{xx}])), SCon{Chr{xx}, tt}, wh.bname(xx, tt)),
          ih(back, qkind)))))

# a segment as key writes it, when that is bare
def wh.seg.bare(
  +ss: String,
  +cl: Bool,
  +dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +rest: String,
  +goal: T.Doc,
  eb: {T.bare(ss) == True{} : Bool},
  ih: wh.Then(cl, rows, heads, here, ss <> wh.ps(dt, parts), arrtab, rest, goal)
) -> {T.doc.read(String.append(T.key.go(True{}, ss), SCon{wh.dl(cl), rest}), T.MScan{wh.st(
  rows, heads, here, wh.ps(dt, parts), [], wh.lex0(dt), back, qkind, arrtab)}) == goal
  : T.Doc}:
  match ss:
    case SNil{}:
      Eq.bit.absurd(&2, {T.doc.read(String.append(T.key.go(True{}, SNil{}), SCon{wh.dl(cl),
        rest}), T.MScan{wh.st(rows, heads, here, wh.ps(dt, parts), [], wh.lex0(dt), back,
        qkind, arrtab)}) == goal : T.Doc}, eb)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          wh.bseg(xx, tt, cl, dt, rows, heads, here, parts, back, qkind, arrtab, rest, goal,
            eb, ih)

# the rest of the text after the closing bracket: a newline, after a second
# bracket for an array of tables
def wh.tail(arrtab: Bool, rest: String) -> String:
  match arrtab:
    case False{}:
      SCon{'\n', rest}
    case True{}:
      SCon{']', SCon{'\n', rest}}

# the walk a header runs, with what it returns
def wh.Walk(
  arrtab: Bool,
  path: List<&2, String>,
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  rows2: List<&2, T.Val>,
  heads2: List<&2, String>
) -> Type:
  {T.tree.walk(path, T.Tw{rows, Laws.header_job(arrtab), [], "", "", heads, False{}}, 0)
    == T.End{rows2, "", heads2} : T.End}

# the bracket runs the header's walk along the segments read, and the newline
# returns to the start of a line in the header's table
def wh.fin(
  arrtab: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +path: List<&2, String>,
  +rows2: List<&2, T.Val>,
  +heads2: List<&2, String>,
  +rest: String,
  ne: {List.is_empty(&2, String, parts) == False{} : Bool},
  er: {List.reverse(&2, String, parts) == path : List<&2, String>},
  ew: wh.Walk(arrtab, path, rows, heads, rows2, heads2)
) -> {T.doc.read(wh.tail(arrtab, rest), T.MScan{wh.aft(True{}, rows, heads, here, parts, back,
  qkind, arrtab)}) == T.doc.read(rest, T.MScan{Laws.hb.line(rows2, heads2, path, back, qkind,
  False{})}) : T.Doc}:
  match arrtab:
    case False{}:
      Equal.trans(T.Doc,
        T.doc.read(SCon{'\n', rest}, T.MScan{T.read.once2(T.head.go(List.is_empty(&2, String,
          parts), wh.st(rows, heads, here, parts, [], T.LHeadGap{}, back, qkind, False{}),
          List.reverse(&2, String, parts)))}),
        T.doc.read(SCon{'\n', rest}, T.MScan{T.read.once2(T.head.apply(T.tree.walk(
          List.reverse(&2, String, parts), T.Tw{rows, T.JDef{}, [], "", "", heads, False{}}, 0),
          List.reverse(&2, String, parts), back, qkind, 0, 0, False{}))}),
        T.doc.read(rest, T.MScan{Laws.hb.line(rows2, heads2, path, back, qkind, False{})}),
        Equal.cong(Bool, T.Doc, bt => T.doc.read(SCon{'\n', rest},
          T.MScan{T.read.once2(T.head.go(bt, wh.st(rows, heads, here, parts, [], T.LHeadGap{},
          back, qkind, False{}), List.reverse(&2, String, parts)))}),
          List.is_empty(&2, String, parts), False{}, ne),
        Equal.trans(T.Doc,
          T.doc.read(SCon{'\n', rest}, T.MScan{T.read.once2(T.head.apply(T.tree.walk(
            List.reverse(&2, String, parts), T.Tw{rows, T.JDef{}, [], "", "", heads, False{}}, 0),
            List.reverse(&2, String, parts), back, qkind, 0, 0, False{}))}),
          T.doc.read(SCon{'\n', rest}, T.MScan{T.read.once2(T.head.apply(T.tree.walk(path,
            T.Tw{rows, T.JDef{}, [], "", "", heads, False{}}, 0), path, back, qkind, 0, 0,
            False{}))}),
          T.doc.read(rest, T.MScan{Laws.hb.line(rows2, heads2, path, back, qkind, False{})}),
          Equal.cong(List<&2, String>, T.Doc, sg => T.doc.read(SCon{'\n', rest},
            T.MScan{T.read.once2(T.head.apply(T.tree.walk(sg, T.Tw{rows, T.JDef{}, [], "", "",
            heads, False{}}, 0), sg, back, qkind, 0, 0, False{}))}),
            List.reverse(&2, String, parts), path, er),
          Equal.cong(T.End, T.Doc, en => T.doc.read(SCon{'\n', rest},
            T.MScan{T.read.once2(T.head.apply(en, path, back, qkind, 0, 0, False{}))}),
            T.tree.walk(path, T.Tw{rows, T.JDef{}, [], "", "", heads, False{}}, 0),
            T.End{rows2, "", heads2}, ew)))
    case True{}:
      Equal.trans(T.Doc,
        T.doc.read(SCon{'\n', rest}, T.MScan{T.read.once2(T.head.go(List.is_empty(&2, String,
          parts), wh.st(rows, heads, here, parts, [], T.LHeadR{}, back, qkind, True{}),
          List.reverse(&2, String, parts)))}),
        T.doc.read(SCon{'\n', rest}, T.MScan{T.read.once2(T.head.apply(T.tree.walk(
          List.reverse(&2, String, parts), T.Tw{rows, T.JAot{}, [], "", "", heads, False{}}, 0),
          List.reverse(&2, String, parts), back, qkind, 0, 0, False{}))}),
        T.doc.read(rest, T.MScan{Laws.hb.line(rows2, heads2, path, back, qkind, False{})}),
        Equal.cong(Bool, T.Doc, bt => T.doc.read(SCon{'\n', rest},
          T.MScan{T.read.once2(T.head.go(bt, wh.st(rows, heads, here, parts, [], T.LHeadR{},
          back, qkind, True{}), List.reverse(&2, String, parts)))}),
          List.is_empty(&2, String, parts), False{}, ne),
        Equal.trans(T.Doc,
          T.doc.read(SCon{'\n', rest}, T.MScan{T.read.once2(T.head.apply(T.tree.walk(
            List.reverse(&2, String, parts), T.Tw{rows, T.JAot{}, [], "", "", heads, False{}}, 0),
            List.reverse(&2, String, parts), back, qkind, 0, 0, False{}))}),
          T.doc.read(SCon{'\n', rest}, T.MScan{T.read.once2(T.head.apply(T.tree.walk(path,
            T.Tw{rows, T.JAot{}, [], "", "", heads, False{}}, 0), path, back, qkind, 0, 0,
            False{}))}),
          T.doc.read(rest, T.MScan{Laws.hb.line(rows2, heads2, path, back, qkind, False{})}),
          Equal.cong(List<&2, String>, T.Doc, sg => T.doc.read(SCon{'\n', rest},
            T.MScan{T.read.once2(T.head.apply(T.tree.walk(sg, T.Tw{rows, T.JAot{}, [], "", "",
            heads, False{}}, 0), sg, back, qkind, 0, 0, False{}))}),
            List.reverse(&2, String, parts), path, er),
          Equal.cong(T.End, T.Doc, en => T.doc.read(SCon{'\n', rest},
            T.MScan{T.read.once2(T.head.apply(en, path, back, qkind, 0, 0, False{}))}),
            T.tree.walk(path, T.Tw{rows, T.JAot{}, [], "", "", heads, False{}}, 0),
            T.End{rows2, "", heads2}, ew)))

# a quote where a segment starts opens a quoted segment with an empty buffer
def wh.qopen(
  dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool
) -> {T.doc.scan(wh.st(rows, heads, here, wh.ps(dt, parts), [], wh.lex0(dt), back, qkind,
  arrtab), '"') == T.MScan{qs(True{}, rows, heads, here, wh.ps(dt, parts), [], arrtab, back, [])}
  : T.Mode}:
  match dt:
    case False{}:
      {==}
    case True{}:
      {==}

# the closing quote pushes the segment, and the dot or bracket after it
# follows, whatever back the last escape left
def wh.qend(
  cl: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +arrtab: Bool,
  +back: T.Lex,
  +bf: List<&2, Char>,
  +rest: String
) -> {T.doc.read(SCon{'"', SCon{wh.dl(cl), rest}}, T.MScan{qs(True{}, rows, heads, here, parts, [],
  arrtab, back, bf)}) == T.doc.read(rest, T.MScan{wh.aft(cl, rows, heads, here, T.buf.str(bf) <> parts,
  back, T.QBasic{}, arrtab)}) : T.Doc}:
  match cl:
    case False{}:
      {==}
    case True{}:
      {==}

# a quoted segment's buffer reads back as its name
def wh.qname(+ss: String) -> {T.buf.str(rev.onto(ss, [])) == ss : String}:
  Equal.trans(String, T.buf.str.go(rev.onto(ss, []), ""), String.append(ss, ""), ss,
    ml.rev(ss, [], ""), Eq.append_nil(ss))

# a quoted segment as key writes it, then a dot or the bracket: the rest is
# read with the segment pushed under its name, from wherever the last escape
# left back and with qkind basic
def wh.qseg(
  +ss: String,
  +cl: Bool,
  +dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +rest: String,
  +goal: T.Doc,
  ih: wh.Then(cl, rows, heads, here, ss <> wh.ps(dt, parts), arrtab, rest, goal)
) -> {T.doc.read(String.append(T.key.go(False{}, ss), SCon{wh.dl(cl), rest}), T.MScan{wh.st(rows,
  heads, here, wh.ps(dt, parts), [], wh.lex0(dt), back, qkind, arrtab)}) == goal : T.Doc}:
  Equal.trans(T.Doc,
    T.doc.read(String.append(T.key.basic(ss), SCon{wh.dl(cl), rest}), T.MScan{wh.st(rows, heads,
      here, wh.ps(dt, parts), [], wh.lex0(dt), back, qkind, arrtab)}),
    T.doc.read(String.append(String.append(Laws.escs(ss), "\""), SCon{wh.dl(cl), rest}),
      T.doc.scan(wh.st(rows, heads, here, wh.ps(dt, parts), [], wh.lex0(dt), back, qkind, arrtab),
      '"')),
    goal,
    Equal.cong(String, T.Doc, zz => T.doc.read(String.append(zz, SCon{wh.dl(cl), rest}),
      T.MScan{wh.st(rows, heads, here, wh.ps(dt, parts), [], wh.lex0(dt), back, qkind, arrtab)}),
      T.key.basic(ss), "\"" ++ Laws.escs(ss) ++ "\"", Laws.basic_escs(ss)),
    Equal.trans(T.Doc,
      T.doc.read(String.append(String.append(Laws.escs(ss), "\""), SCon{wh.dl(cl), rest}),
        T.doc.scan(wh.st(rows, heads, here, wh.ps(dt, parts), [], wh.lex0(dt), back, qkind,
        arrtab), '"')),
      T.doc.read(String.append(Laws.escs(ss), SCon{'"', SCon{wh.dl(cl), rest}}),
        T.MScan{qs(True{}, rows, heads, here, wh.ps(dt, parts), [], arrtab, back, [])}),
      goal,
      Equal.trans(T.Doc,
        T.doc.read(String.append(String.append(Laws.escs(ss), "\""), SCon{wh.dl(cl), rest}),
          T.doc.scan(wh.st(rows, heads, here, wh.ps(dt, parts), [], wh.lex0(dt), back, qkind,
          arrtab), '"')),
        T.doc.read(String.append(Laws.escs(ss), SCon{'"', SCon{wh.dl(cl), rest}}),
          T.doc.scan(wh.st(rows, heads, here, wh.ps(dt, parts), [], wh.lex0(dt), back, qkind,
          arrtab), '"')),
        T.doc.read(String.append(Laws.escs(ss), SCon{'"', SCon{wh.dl(cl), rest}}),
          T.MScan{qs(True{}, rows, heads, here, wh.ps(dt, parts), [], arrtab, back, [])}),
        Equal.cong(String, T.Doc, zz => T.doc.read(zz, T.doc.scan(wh.st(rows, heads, here,
          wh.ps(dt, parts), [], wh.lex0(dt), back, qkind, arrtab), '"')),
          String.append(String.append(Laws.escs(ss), "\""), SCon{wh.dl(cl), rest}),
          String.append(Laws.escs(ss), SCon{'"', SCon{wh.dl(cl), rest}}),
          Eq.append_assoc(Laws.escs(ss), "\"", SCon{wh.dl(cl), rest})),
        Equal.cong(T.Mode, T.Doc, md => T.doc.read(String.append(Laws.escs(ss), SCon{'"',
          SCon{wh.dl(cl), rest}}), md),
          T.doc.scan(wh.st(rows, heads, here, wh.ps(dt, parts), [], wh.lex0(dt), back, qkind,
            arrtab), '"'),
          T.MScan{qs(True{}, rows, heads, here, wh.ps(dt, parts), [], arrtab, back, [])},
          wh.qopen(dt, rows, heads, here, parts, back, qkind, arrtab))),
      qs.escs(ss, True{}, rows, heads, here, wh.ps(dt, parts), [], arrtab, back, [],
        SCon{'"', SCon{wh.dl(cl), rest}}, goal,
        +bk => Equal.trans(T.Doc,
          T.doc.read(SCon{'"', SCon{wh.dl(cl), rest}}, T.MScan{qs(True{}, rows, heads, here,
            wh.ps(dt, parts), [], arrtab, bk, rev.onto(ss, []))}),
          T.doc.read(rest, T.MScan{wh.aft(cl, rows, heads, here, T.buf.str(rev.onto(ss, [])) <>
            wh.ps(dt, parts), bk, T.QBasic{}, arrtab)}),
          goal,
          wh.qend(cl, rows, heads, here, wh.ps(dt, parts), arrtab, bk, rev.onto(ss, []), rest),
          Equal.trans(T.Doc,
            T.doc.read(rest, T.MScan{wh.aft(cl, rows, heads, here, T.buf.str(rev.onto(ss, [])) <>
              wh.ps(dt, parts), bk, T.QBasic{}, arrtab)}),
            T.doc.read(rest, T.MScan{wh.aft(cl, rows, heads, here, ss <> wh.ps(dt, parts), bk,
              T.QBasic{}, arrtab)}),
            goal,
            Equal.cong(String, T.Doc, nm => T.doc.read(rest, T.MScan{wh.aft(cl, rows, heads, here,
              nm <> wh.ps(dt, parts), bk, T.QBasic{}, arrtab)}),
              T.buf.str(rev.onto(ss, [])), ss, wh.qname(ss)),
            ih(bk, T.QBasic{}))))))

# a segment as key writes it, bare or quoted, then a dot or the bracket
def wh.seg.go(
  bb: Bool,
  +ss: String,
  +cl: Bool,
  +dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +rest: String,
  +goal: T.Doc,
  eb: {T.bare(ss) == bb : Bool},
  ih: wh.Then(cl, rows, heads, here, ss <> wh.ps(dt, parts), arrtab, rest, goal)
) -> {T.doc.read(String.append(T.key.go(bb, ss), SCon{wh.dl(cl), rest}), T.MScan{wh.st(rows,
  heads, here, wh.ps(dt, parts), [], wh.lex0(dt), back, qkind, arrtab)}) == goal : T.Doc}:
  match bb:
    case True{}:
      wh.seg.bare(ss, cl, dt, rows, heads, here, parts, back, qkind, arrtab, rest, goal, eb, ih)
    case False{}:
      wh.qseg(ss, cl, dt, rows, heads, here, parts, back, qkind, arrtab, rest, goal, ih)

# a segment as key writes it, then a dot or the bracket
def wh.seg(
  +ss: String,
  +cl: Bool,
  +dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +rest: String,
  +goal: T.Doc,
  ih: wh.Then(cl, rows, heads, here, ss <> wh.ps(dt, parts), arrtab, rest, goal)
) -> {T.doc.read(String.append(T.key(ss), SCon{wh.dl(cl), rest}), T.MScan{wh.st(rows, heads,
  here, wh.ps(dt, parts), [], wh.lex0(dt), back, qkind, arrtab)}) == goal : T.Doc}:
  wh.seg.go(T.bare(ss), ss, cl, dt, rows, heads, here, parts, back, qkind, arrtab, rest, goal, {==},
    ih)

# the segments after the first, each after a dot, as the rendered path
# writes them
def wh.more(segs: List<&2, String>) -> String:
  match segs:
    case []:
      ""
    case +seg <> rest:
      SCon{'.', String.append(T.key(seg), wh.more(rest))}

# segments pushed one by one onto parts
def wh.Segs(
  t: List<&2, String>,
  +ss: String,
  +dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +rest: String,
  +goal: T.Doc
) -> Type:
  wh.Then(True{}, rows, heads, here, List.reverse.go(&2, String, t, ss <> wh.ps(dt, parts)),
    arrtab, rest, goal) ->
    {T.doc.read(String.append(T.key(ss), String.append(wh.more(t), SCon{']', rest})),
      T.MScan{wh.st(rows, heads, here, wh.ps(dt, parts), [], wh.lex0(dt), back, qkind, arrtab)})
      == goal : T.Doc}

# a path's segments and the bracket after them: the rest is read with every
# segment pushed
def wh.segs(
  t: List<&2, String>,
  +ss: String,
  +dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +rest: String,
  +goal: T.Doc
) -> wh.Segs(t, ss, dt, rows, heads, here, parts, back, qkind, arrtab, rest, goal):
  match t:
    case []:
      ih => wh.seg(ss, True{}, dt, rows, heads, here, parts, back, qkind, arrtab, rest, goal, ih)
    case +xx <> +xs:
      ih => wh.seg(ss, False{}, dt, rows, heads, here, parts, back, qkind, arrtab,
        String.append(String.append(T.key(xx), wh.more(xs)), SCon{']', rest}), goal,
        +bk => +qk => Equal.trans(T.Doc,
          T.doc.read(String.append(String.append(T.key(xx), wh.more(xs)), SCon{']', rest}),
            T.MScan{wh.st(rows, heads, here, ss <> wh.ps(dt, parts), [], T.LHeadDot{}, bk, qk,
            arrtab)}),
          T.doc.read(String.append(T.key(xx), String.append(wh.more(xs), SCon{']', rest})),
            T.MScan{wh.st(rows, heads, here, ss <> wh.ps(dt, parts), [], T.LHeadDot{}, bk, qk,
            arrtab)}),
          goal,
          Equal.cong(String, T.Doc, zz => T.doc.read(zz, T.MScan{wh.st(rows, heads, here,
            ss <> wh.ps(dt, parts), [], T.LHeadDot{}, bk, qk, arrtab)}),
            String.append(String.append(T.key(xx), wh.more(xs)), SCon{']', rest}),
            String.append(T.key(xx), String.append(wh.more(xs), SCon{']', rest})),
            Eq.append_assoc(T.key(xx), wh.more(xs), SCon{']', rest})),
          wh.segs(xs, xx, True{}, rows, heads, here, ss <> wh.ps(dt, parts), bk, qk, arrtab,
            rest, goal)(ih)))

# reversing a list reversed onto acc puts acc's reversal first
def wh.rr(
  t: List<&2, String>,
  +acc: List<&2, String>,
  +ys: List<&2, String>
) -> {List.reverse.go(&2, String, List.reverse.go(&2, String, t, acc), ys)
  == List.reverse.go(&2, String, acc, List.append(&2, String, t, ys)) : List<&2, String>}:
  match t:
    case []:
      {==}
    case +xx <> xs:
      wh.rr(xs, xx <> acc, ys)

# appending nothing to a list of segments leaves it
def wh.lnil(t: List<&2, String>) -> {List.append(&2, String, t, []) == t : List<&2, String>}:
  match t:
    case []:
      {==}
    case +xx <> xs:
      Equal.cong(List<&2, String>, List<&2, String>, zz => xx <> zz,
        List.append(&2, String, xs, []), xs, wh.lnil(xs))

# the segments pushed onto parts, reversed, are the path in order
def wh.rev2(
  +t: List<&2, String>,
  +ss: String
) -> {List.reverse(&2, String, List.reverse.go(&2, String, t, [ss])) == ss <> t
  : List<&2, String>}:
  Equal.trans(List<&2, String>,
    List.reverse.go(&2, String, List.reverse.go(&2, String, t, [ss]), []),
    ss <> List.append(&2, String, t, []),
    ss <> t,
    wh.rr(t, [ss], []),
    Equal.cong(List<&2, String>, List<&2, String>, zz => ss <> zz,
      List.append(&2, String, t, []), t, wh.lnil(t)))

# and they are not empty
def wh.rne(
  t: List<&2, String>,
  +ss: String,
  +acc: List<&2, String>
) -> {List.is_empty(&2, String, List.reverse.go(&2, String, t, ss <> acc)) == False{} : Bool}:
  match t:
    case []:
      {==}
    case +xx <> xs:
      wh.rne(xs, xx, ss <> acc)

# a path joined onto a nonempty prefix is the prefix, a dot and the segment
def wh.pre(
  +pp: String,
  +xx: String,
  ep: {String.is_empty(pp) == False{} : Bool}
) -> {T.tree.pre(pp, xx) == String.append(pp, SCon{'.', T.key(xx)}) : String}:
  Equal.cong(Bool, String, bt => T.tree.pre.go(bt, pp, xx), String.is_empty(pp), False{}, ep)

# a nonempty prefix stays nonempty
def wh.ne(
  pp: String,
  +yy: String,
  ep: {String.is_empty(pp) == False{} : Bool}
) -> {String.is_empty(String.append(pp, yy)) == False{} : Bool}:
  match pp:
    case SNil{}:
      Eq.bit.absurd2(&2, {String.is_empty(String.append(SNil{}, yy)) == False{} : Bool}, ep)
    case SCon{_h, _t}:
      {==}

# the stored path of a header, from a nonempty prefix, is the prefix and the
# later segments, each after a dot
def wh.join(
  ss: List<&2, String>,
  +pp: String,
  +kk: String,
  +ep: {String.is_empty(pp) == False{} : Bool}
) -> {T.tree.pre(Laws.tb.join(ss, pp), kk) == String.append(pp, wh.more(List.append(&2, String, ss,
  [kk]))) : String}:
  match ss:
    case []:
      Equal.trans(String, T.tree.pre(pp, kk), String.append(pp, SCon{'.', T.key(kk)}),
        String.append(pp, SCon{'.', String.append(T.key(kk), "")}),
        wh.pre(pp, kk, ep),
        Equal.cong(String, String, zz => String.append(pp, SCon{'.', zz}), T.key(kk),
          String.append(T.key(kk), ""), Equal.sym(String, String.append(T.key(kk), ""), T.key(kk),
          Eq.append_nil(T.key(kk)))))
    case +xx <> +xs:
      Equal.trans(String,
        T.tree.pre(Laws.tb.join(xs, T.tree.pre(pp, xx)), kk),
        T.tree.pre(Laws.tb.join(xs, String.append(pp, SCon{'.', T.key(xx)})), kk),
        String.append(pp, wh.more(xx <> List.append(&2, String, xs, [kk]))),
        Equal.cong(String, String, qq => T.tree.pre(Laws.tb.join(xs, qq), kk), T.tree.pre(pp, xx),
          String.append(pp, SCon{'.', T.key(xx)}), wh.pre(pp, xx, ep)),
        Equal.trans(String,
          T.tree.pre(Laws.tb.join(xs, String.append(pp, SCon{'.', T.key(xx)})), kk),
          String.append(String.append(pp, SCon{'.', T.key(xx)}), wh.more(List.append(&2, String, xs,
            [kk]))),
          String.append(pp, wh.more(xx <> List.append(&2, String, xs, [kk]))),
          wh.join(xs, String.append(pp, SCon{'.', T.key(xx)}), kk, wh.ne(pp, SCon{'.', T.key(xx)},
            ep)),
          Eq.append_assoc(pp, SCon{'.', T.key(xx)}, wh.more(List.append(&2, String, xs, [kk])))))

# a key is never empty: a bare one has a character, a quoted one its quotes
def wh.key.ne.go(
  bb: Bool,
  +ss: String,
  eb: {T.bare(ss) == bb : Bool}
) -> {String.is_empty(T.key.go(bb, ss)) == False{} : Bool}:
  match bb:
    case False{}:
      {==}
    case True{}:
      match ss:
        case SNil{}:
          Eq.bit.absurd(&2, {String.is_empty(T.key.go(True{}, SNil{})) == False{} : Bool}, eb)
        case SCon{_h, _t}:
          {==}

# a key is never empty
def wh.key.ne(+ss: String) -> {String.is_empty(T.key(ss)) == False{} : Bool}:
  wh.key.ne.go(T.bare(ss), ss, {==})

# the brackets that open a header: one, or two for an array of tables
def wh.open(arrtab: Bool, rest: String) -> String:
  match arrtab:
    case False{}:
      SCon{'[', rest}
    case True{}:
      SCon{'[', SCon{'[', rest}}

# the rest of the text after the header, from the start of the next line
def wh.Line(
  +rows2: List<&2, T.Val>,
  +heads2: List<&2, String>,
  +path: List<&2, String>,
  +rest: String,
  +goal: T.Doc
) -> Type:
  @bk: T.Lex -> @qk: T.QKind ->
    {T.doc.read(rest, T.MScan{Laws.hb.line(rows2, heads2, path, bk, qk, False{})}) == goal
      : T.Doc}

# a whole header line of the segments ss then t, from the start of a line
def wh.core(
  arrtab: Bool,
  +ss: String,
  +t: List<&2, String>,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +a0: Bool,
  +rows2: List<&2, T.Val>,
  +heads2: List<&2, String>,
  +rest: String,
  +goal: T.Doc,
  ew: wh.Walk(arrtab, ss <> t, rows, heads, rows2, heads2),
  ih: wh.Line(rows2, heads2, ss <> t, rest, goal)
) -> {T.doc.read(wh.open(arrtab, String.append(T.key(ss), String.append(wh.more(t), SCon{']',
  wh.tail(arrtab, rest)}))), T.MScan{Laws.hb.line(rows, heads, here, back, qkind, a0)}) == goal
  : T.Doc}:
  match arrtab:
    case False{}:
      wh.segs(t, ss, False{}, rows, heads, here, [], back, qkind, False{}, wh.tail(False{}, rest),
        goal)(+bk => +qk => Equal.trans(T.Doc,
          T.doc.read(SCon{'\n', rest}, T.MScan{wh.aft(True{}, rows, heads, here,
            List.reverse.go(&2, String, t, [ss]), bk, qk, False{})}),
          T.doc.read(rest, T.MScan{Laws.hb.line(rows2, heads2, ss <> t, bk, qk, False{})}),
          goal,
          wh.fin(False{}, rows, heads, here, List.reverse.go(&2, String, t, [ss]), bk, qk, ss <> t,
            rows2, heads2, rest, wh.rne(t, ss, []), wh.rev2(t, ss), ew),
          ih(bk, qk)))
    case True{}:
      wh.segs(t, ss, False{}, rows, heads, here, [], back, qkind, True{}, wh.tail(True{}, rest),
        goal)(+bk => +qk => Equal.trans(T.Doc,
          T.doc.read(SCon{']', SCon{'\n', rest}}, T.MScan{wh.aft(True{}, rows, heads, here,
            List.reverse.go(&2, String, t, [ss]), bk, qk, True{})}),
          T.doc.read(rest, T.MScan{Laws.hb.line(rows2, heads2, ss <> t, bk, qk, False{})}),
          goal,
          wh.fin(True{}, rows, heads, here, List.reverse.go(&2, String, t, [ss]), bk, qk, ss <> t,
            rows2, heads2, rest, wh.rne(t, ss, []), wh.rev2(t, ss), ew),
          ih(bk, qk)))

# a header line as render writes it: the stored path, which is the parent's
# path joined with the last segment
def wh.law(
  +arrtab: Bool,
  segs: List<&2, String>,
  +kk: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +a0: Bool,
  +rows2: List<&2, T.Val>,
  +heads2: List<&2, String>,
  +rest: String,
  +goal: T.Doc,
  ew: wh.Walk(arrtab, List.append(&2, String, segs, [kk]), rows, heads, rows2, heads2),
  ih: wh.Line(rows2, heads2, List.append(&2, String, segs, [kk]), rest, goal)
) -> {T.doc.read(wh.open(arrtab, String.append(T.tree.pre(Laws.tb.join(segs, ""), kk), SCon{']',
  wh.tail(arrtab, rest)})), T.MScan{Laws.hb.line(rows, heads, here, back, qkind, a0)}) == goal
  : T.Doc}:
  match segs:
    case []:
      wh.core(arrtab, kk, [], rows, heads, here, back, qkind, a0, rows2, heads2, rest, goal, ew, ih)
    case +s0 <> +ss:
      Equal.trans(T.Doc,
        T.doc.read(wh.open(arrtab, String.append(T.tree.pre(Laws.tb.join(ss, T.key(s0)), kk),
          SCon{']', wh.tail(arrtab, rest)})), T.MScan{Laws.hb.line(rows, heads, here, back, qkind,
          a0)}),
        T.doc.read(wh.open(arrtab, String.append(String.append(T.key(s0), wh.more(List.append(&2,
          String, ss, [kk]))), SCon{']', wh.tail(arrtab, rest)})), T.MScan{Laws.hb.line(rows,
          heads, here, back, qkind, a0)}),
        goal,
        Equal.cong(String, T.Doc, pt => T.doc.read(wh.open(arrtab, String.append(pt, SCon{']',
          wh.tail(arrtab, rest)})), T.MScan{Laws.hb.line(rows, heads, here, back, qkind, a0)}),
          T.tree.pre(Laws.tb.join(ss, T.key(s0)), kk),
          String.append(T.key(s0), wh.more(List.append(&2, String, ss, [kk]))),
          wh.join(ss, T.key(s0), kk, wh.key.ne(s0))),
        Equal.trans(T.Doc,
          T.doc.read(wh.open(arrtab, String.append(String.append(T.key(s0), wh.more(List.append(&2,
            String, ss, [kk]))), SCon{']', wh.tail(arrtab, rest)})), T.MScan{Laws.hb.line(rows,
            heads, here, back, qkind, a0)}),
          T.doc.read(wh.open(arrtab, String.append(T.key(s0), String.append(wh.more(List.append(&2,
            String, ss, [kk])), SCon{']', wh.tail(arrtab, rest)}))), T.MScan{Laws.hb.line(rows,
            heads, here, back, qkind, a0)}),
          goal,
          Equal.cong(String, T.Doc, pt => T.doc.read(wh.open(arrtab, pt), T.MScan{Laws.hb.line(rows,
            heads, here, back, qkind, a0)}),
            String.append(String.append(T.key(s0), wh.more(List.append(&2, String, ss, [kk]))),
              SCon{']', wh.tail(arrtab, rest)}),
            String.append(T.key(s0), String.append(wh.more(List.append(&2, String, ss, [kk])),
              SCon{']', wh.tail(arrtab, rest)})),
            Eq.append_assoc(T.key(s0), wh.more(List.append(&2, String, ss, [kk])), SCon{']',
              wh.tail(arrtab, rest)})),
          wh.core(arrtab, s0, List.append(&2, String, ss, [kk]), rows, heads, here, back, qkind, a0,
            rows2, heads2, rest, goal, ew, ih)))

def Laws.header_reads_back(
  segs,
  k,
  rows,
  heads,
  here,
  back,
  qkind,
  arrtab,
  rows2,
  heads2,
  ew,
  rest,
  goal,
  ih
):
  wh.law(False{}, segs, k, rows, heads, here, back, qkind, arrtab, rows2, heads2, rest, goal, ew, ih)

def Laws.header_new_table_reads_back(
  segs,
  k,
  rows,
  heads,
  eo,
  em,
  here,
  back,
  qkind,
  arrtab,
  rest,
  goal,
  ih
):
  Laws.header_reads_back(segs, k, rows, heads, here, back, qkind, arrtab,
    Laws.tb.set(segs, "", rows, T.VPair{k, T.VHead{T.tree.pre(Laws.tb.join(segs, ""), k), []}}
      <> Laws.tb.rows(segs, rows)),
    T.heads.by.head(T.tree.pre(Laws.tb.join(segs, ""), k)) <> heads,
    Laws.header_defines_new_table(segs, k, rows, heads, eo, em), rest, goal, ih)

def Laws.header_implicit_table_reads_back(
  segs,
  k,
  rows,
  heads,
  p,
  sub,
  eo,
  ef,
  eh,
  here,
  back,
  qkind,
  arrtab,
  rest,
  goal,
  ih
):
  Laws.header_reads_back(segs, k, rows, heads, here, back, qkind, arrtab,
    Laws.tb.set(segs, "", rows, T.rows.repl(Laws.tb.rows(segs, rows), k,
      T.VHead{T.tree.pre(Laws.tb.join(segs, ""), k), sub})),
    T.heads.by.head(T.tree.pre(Laws.tb.join(segs, ""), k)) <> heads,
    Laws.header_defines_implicit_table(segs, k, rows, heads, p, sub, eo, ef, eh), rest, goal, ih)

def Laws.aot_header_reads_back(
  segs,
  k,
  rows,
  heads,
  here,
  back,
  qkind,
  arrtab,
  rows2,
  heads2,
  ew,
  rest,
  goal,
  ih
):
  wh.law(True{}, segs, k, rows, heads, here, back, qkind, arrtab, rows2, heads2, rest, goal, ew, ih)

def Laws.aot_header_new_array_reads_back(
  segs,
  k,
  rows,
  heads,
  eo,
  em,
  here,
  back,
  qkind,
  arrtab,
  rest,
  goal,
  ih
):
  Laws.aot_header_reads_back(segs, k, rows, heads, here, back, qkind, arrtab,
    Laws.tb.set(segs, "", rows, T.VPair{k, T.VAots{T.tree.pre(Laws.tb.join(segs, ""), k),
      [T.VAot{T.tree.pre(Laws.tb.join(segs, ""), k), []}]}} <> Laws.tb.rows(segs, rows)),
    heads, Laws.aot_header_starts_array(segs, k, rows, heads, eo, em), rest, goal, ih)

def Laws.aot_header_extends_array_reads_back(
  segs,
  k,
  rows,
  heads,
  p,
  elems,
  eo,
  ef,
  here,
  back,
  qkind,
  arrtab,
  rest,
  goal,
  ih
):
  Laws.aot_header_reads_back(segs, k, rows, heads, here, back, qkind, arrtab,
    Laws.tb.set(segs, "", rows, T.rows.repl(Laws.tb.rows(segs, rows), k,
      T.VAots{T.tree.pre(Laws.tb.join(segs, ""), k), T.VAot{T.tree.pre(Laws.tb.join(segs, ""), k), []}
        <> elems})),
    T.heads.drop(heads, String.append(T.tree.pre(Laws.tb.join(segs, ""), k), ".")),
    Laws.aot_header_extends_array(segs, k, rows, heads, p, elems, eo, ef), rest, goal, ih)

# WP-S: a rendered string read back in any value position. render writes a
# string as key.basic of its characters (TOML-STR-2); the lemmas below read
# that text back from the scanner just past the opening quote of a value, in
# a root pair, an array item or an inline table's pair alike: every field the
# string leaves alone is a parameter (bd the error, rw the rows, hs heads, he
# here, ps parts, sk the stack of open arrays and inline tables, ab arrtab).
# The string ends with its value placed by take.top, which is where the three
# positions part: the rest of the walk is a function of the value and of the
# fields the string may change (back, and uni and left after a \u escape), as
# in WP0's quoted-segment family. The value is a span of the text while no
# character needs an escape, and an owned string once one does; either way
# it holds the string's characters (sv.Is), and own reads it as them
# (sv.own.pair, sv.own.item). The rest of the walk ends in a motive PP over
# the document, so a caller proves what it needs of it (its owned form, for
# WP-D's exact lemma) whichever value the string became.

# the scanner just past the opening quote of a basic string in a value
# position
def sv.open(
  bd: String,
  rw: List<&2, T.Val>,
  hs: List<&2, String>,
  he: List<&2, String>,
  ps: List<&2, String>,
  bk: T.Lex,
  sk: List<&2, T.Ctx>,
  un: U32,
  lf: U32,
  ab: Bool
) -> T.Mode:
  T.MOpen{True{}, '"', T.QBasic{}, bd, rw, hs, he, ps, [], bk, sk, un, lf, ab}

# the scanner inside the span of such a string: cut is the text from its
# first character, nn the characters counted so far
def sv.eat(
  cut: String,
  nn: U32,
  bd: String,
  rw: List<&2, T.Val>,
  hs: List<&2, String>,
  he: List<&2, String>,
  ps: List<&2, String>,
  sk: List<&2, T.Ctx>,
  un: U32,
  lf: U32,
  ab: Bool
) -> T.Mode:
  T.MEat{True{}, '"', cut, nn, bd, rw, hs, he, ps, T.QBasic{}, sk, un, lf, ab}

# the scanner once the string's value vv is placed: take.top puts it into the
# root table, the open array or the open inline table, as sk says
def sv.took(
  sk: List<&2, T.Ctx>,
  vv: T.Val,
  bd: String,
  rw: List<&2, T.Val>,
  hs: List<&2, String>,
  +he: List<&2, String>,
  ps: List<&2, String>,
  bk: T.Lex,
  un: U32,
  lf: U32,
  ab: Bool
) -> T.St:
  T.take.top(sk, vv, bd, rw, hs, he, ps, bk, T.QBasic{}, un, lf, ab, False{})

# a string value holding the characters ss: an owned string of them, or a
# span of a text whose first n characters they are. No other value is one
def sv.Is(vv: T.Val, ss: String) -> Type:
  match vv:
    case T.VStr{tt}:
      {tt == ss : String}
    case T.VSpan{src, +nn}:
      {T.span.str(src, nn, U32.is_zero(nn)) == ss : String}
    case _:
      Empty

# the rest of the walk, for the string ss: reading rest from the scanner with
# any string value holding ss placed (sv.Is), and any back, uni and left, gives a
# document PP holds of. PP is what the caller proves of the document: its
# owned form, say, as WP-D's exact lemma needs, since the value itself is a
# span or an owned string depending on the escapes
def sv.Then(
  +ss: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  @vv: T.Val -> @bk: T.Lex -> @un: U32 -> @lf: U32 ->
    sv.Is(vv, ss) ->
    PP(T.doc.read(rest, T.MScan{sv.took(sk, vv, bd, rw, hs, he, ps, bk, un, lf, ab)}))

# what holds of a document holds of one equal to it
def pp.step(
  -PP: T.Doc -> Type,
  aa: T.Doc,
  bb: T.Doc,
  ee: {aa == bb : T.Doc},
  kk: PP(bb)
) -> PP(aa):
  %Equal.sym(T.Doc, aa, bb, ee) : PP(_)
  kk

# the rest of the walk for one string serves for another equal to it
def sv.then.cast(
  +s1: String,
  +s2: String,
  e12: {s1 == s2 : String},
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  ih: sv.Then(s1, bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> sv.Then(s2, bd, rw, hs, he, ps, sk, ab, rest, PP):
  %e12 : sv.Then(_, bd, rw, hs, he, ps, sk, ab, rest, PP)
  ih

# A placed value holds no character for the next step to read again, and it
# is no quote that opens a string: the full step's read.once2 and doc.wrap
# leave it as it is. The walk's result is a parameter, so this holds
# whatever the walk did.

# at the root
def tk.root(
  end: T.End,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +ld: Bool
) -> {T.doc.wrap(T.read.once2(T.take.root(end, he, bk, qk, un, lf, ab, ld)))
  == T.MScan{T.take.root(end, he, bk, qk, un, lf, ab, ld)} : T.Mode}:
  match end:
    case T.End{_vs, _bad, _heads}:
      {==}

# in an inline table
def tk.inl(
  end: T.End,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +rest: List<&2, T.Ctx>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +ld: Bool
) -> {T.doc.wrap(T.read.once2(T.take.inl(end, rw, hs, he, ps, rest, bk, qk, un, lf, ab, ld)))
  == T.MScan{T.take.inl(end, rw, hs, he, ps, rest, bk, qk, un, lf, ab, ld)} : T.Mode}:
  match end:
    case T.End{_vs, _bad, _heads}:
      {==}

# wherever the value goes
def tk.fix(
  sk: List<&2, T.Ctx>,
  +vv: T.Val,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +ld: Bool
) -> {T.doc.wrap(T.read.once2(T.take.top(sk, vv, bd, rw, hs, he, ps, bk, qk, un, lf, ab, ld)))
  == T.MScan{T.take.top(sk, vv, bd, rw, hs, he, ps, bk, qk, un, lf, ab, ld)} : T.Mode}:
  match sk:
    case []:
      tk.root(T.tree.walk(T.path.cat(he, ps), T.Tw{rw, T.JPut{vv}, [], bd, "", hs, False{}},
        T.path.len(he, 0)), he, bk, qk, un, lf, ab, ld)
    case T.CArr{_items, _saved, _at} <> _rest:
      {==}
    case T.CInl{inl, +saved, +at} <> +rest:
      tk.inl(T.tree.walk(List.reverse(&2, String, ps), T.Tw{inl, T.JPut{vv}, [], bd, "", [],
        True{}}, 0), rw, hs, at, saved, rest, bk, qk, un, lf, ab, ld)

# The span. A first character written as itself opens it, each later one
# adds one to its count, and the closing quote places it.

# the first character: no control, so the span starts
def so.ok(
  badc: Bool,
  +uu: U32,
  +tail: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  hc: {badc == False{} : Bool}
) -> {T.doc.open.ok(T.str.bad.go(badc, U32.is_eq(uu, 9), Bool.or(U32.is_eq(uu, 10),
  U32.is_eq(uu, 13)), False{}), True{}, '"', T.QBasic{}, bd, rw, hs, he, ps, [], bk, sk, un, lf,
  ab, Chr{uu}, tail) == sv.eat(SCon{Chr{uu}, tail}, 1, bd, rw, hs, he, ps, sk, un, lf, ab) : T.Mode}:
  match badc:
    case False{}:
      {==}
    case True{}:
      Eq.bit.absurd2(&2, {T.doc.open.ok(T.str.bad.go(True{}, U32.is_eq(uu, 9),
        Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)), False{}), True{}, '"', T.QBasic{}, bd, rw,
        hs, he, ps, [], bk, sk, un, lf, ab, Chr{uu}, tail)
        == sv.eat(SCon{Chr{uu}, tail}, 1, bd, rw, hs, he, ps, sk, un, lf, ab) : T.Mode}, hc)

# no backslash
def so.bs(
  bs: Bool,
  +uu: U32,
  +tail: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  hb: {bs == False{} : Bool},
  hc: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool}
) -> {T.doc.open.bs(bs, '"', T.QBasic{}, bd, rw, hs, he, ps, [], bk, sk, un, lf, ab, Chr{uu}, tail)
  == sv.eat(SCon{Chr{uu}, tail}, 1, bd, rw, hs, he, ps, sk, un, lf, ab) : T.Mode}:
  match bs:
    case False{}:
      so.ok(Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), uu, tail, bd, rw, hs, he, ps, bk, sk,
        un, lf, ab, hc)
    case True{}:
      Eq.bit.absurd2(&2, {T.doc.open.bs(True{}, '"', T.QBasic{}, bd, rw, hs, he, ps, [], bk, sk,
        un, lf, ab, Chr{uu}, tail) == sv.eat(SCon{Chr{uu}, tail}, 1, bd, rw, hs, he, ps, sk, un, lf,
        ab) : T.Mode}, hb)

# no quotation mark
def so.q(
  same: Bool,
  +uu: U32,
  +tail: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  hq: {same == False{} : Bool},
  hb: {U32.is_eq(uu, 92) == False{} : Bool},
  hc: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool}
) -> {T.doc.open.q(same, True{}, '"', T.QBasic{}, bd, rw, hs, he, ps, [], bk, sk, un, lf, ab,
  Chr{uu}, tail) == sv.eat(SCon{Chr{uu}, tail}, 1, bd, rw, hs, he, ps, sk, un, lf, ab) : T.Mode}:
  match same:
    case False{}:
      so.bs(U32.is_eq(uu, 92), uu, tail, bd, rw, hs, he, ps, bk, sk, un, lf, ab, hb, hc)
    case True{}:
      Eq.bit.absurd2(&2, {T.doc.open.q(True{}, True{}, '"', T.QBasic{}, bd, rw, hs, he, ps, [], bk,
        sk, un, lf, ab, Chr{uu}, tail) == sv.eat(SCon{Chr{uu}, tail}, 1, bd, rw, hs, he, ps, sk, un,
        lf, ab) : T.Mode}, hq)

# a first character that is no quotation mark, backslash or control opens the
# span
def so.one(
  +uu: U32,
  +tail: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  e34: {U32.is_eq(uu, 34) == False{} : Bool},
  e92: {U32.is_eq(uu, 92) == False{} : Bool},
  ec: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool}
) -> {T.doc.read(SCon{Chr{uu}, tail}, sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab))
  == T.doc.read(tail, sv.eat(SCon{Chr{uu}, tail}, 1, bd, rw, hs, he, ps, sk, un, lf, ab)) : T.Doc}:
  Equal.cong(T.Mode, T.Doc, md => T.doc.read(tail, md),
    T.doc.open(True{}, '"', T.QBasic{}, bd, rw, hs, he, ps, [], bk, sk, un, lf, ab, Chr{uu}, tail),
    sv.eat(SCon{Chr{uu}, tail}, 1, bd, rw, hs, he, ps, sk, un, lf, ab),
    so.q(U32.is_eq(uu, 34), uu, tail, bd, rw, hs, he, ps, bk, sk, un, lf, ab, e34, e92, ec))

# a later character: no control, so the span grows
def se.ctl(
  ctl: Bool,
  +uu: U32,
  +cut: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  hc: {ctl == False{} : Bool}
) -> {T.eat.ctrl(T.str.bad.go(ctl, U32.is_eq(uu, 9), Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)),
  False{}), True{}, '"', Chr{uu}, cut, nn, bd, rw, hs, he, ps, T.QBasic{}, sk, un, lf, ab)
  == sv.eat(cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un, lf, ab) : T.Mode}:
  match ctl:
    case False{}:
      {==}
    case True{}:
      Eq.bit.absurd2(&2, {T.eat.ctrl(T.str.bad.go(True{}, U32.is_eq(uu, 9),
        Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)), False{}), True{}, '"', Chr{uu}, cut, nn, bd,
        rw, hs, he, ps, T.QBasic{}, sk, un, lf, ab)
        == sv.eat(cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un, lf, ab) : T.Mode}, hc)

# no backslash
def se.bs(
  bs: Bool,
  +uu: U32,
  +cut: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  hb: {bs == False{} : Bool},
  hc: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool}
) -> {T.eat.bs(bs, True{}, '"', Chr{uu}, cut, nn, bd, rw, hs, he, ps, T.QBasic{}, sk, un, lf, ab)
  == sv.eat(cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un, lf, ab) : T.Mode}:
  match bs:
    case False{}:
      se.ctl(Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), uu, cut, nn, bd, rw, hs, he, ps, sk,
        un, lf, ab, hc)
    case True{}:
      Eq.bit.absurd2(&2, {T.eat.bs(True{}, True{}, '"', Chr{uu}, cut, nn, bd, rw, hs, he, ps,
        T.QBasic{}, sk, un, lf, ab) == sv.eat(cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un, lf,
        ab) : T.Mode}, hb)

# no quotation mark
def se.q(
  quote: Bool,
  +uu: U32,
  +cut: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  hq: {quote == False{} : Bool},
  hb: {U32.is_eq(uu, 92) == False{} : Bool},
  hc: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool}
) -> {T.eat.feed.q(quote, True{}, '"', Chr{uu}, cut, nn, bd, rw, hs, he, ps, T.QBasic{}, sk, un,
  lf, ab) == sv.eat(cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un, lf, ab) : T.Mode}:
  match quote:
    case False{}:
      se.bs(U32.is_eq(uu, 92), uu, cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab, hb, hc)
    case True{}:
      Eq.bit.absurd2(&2, {T.eat.feed.q(True{}, True{}, '"', Chr{uu}, cut, nn, bd, rw, hs, he, ps,
        T.QBasic{}, sk, un, lf, ab) == sv.eat(cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un, lf,
        ab) : T.Mode}, hq)

# a later character written as itself grows the span by one
def se.one(
  +uu: U32,
  +tail: String,
  +cut: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  e34: {U32.is_eq(uu, 34) == False{} : Bool},
  e92: {U32.is_eq(uu, 92) == False{} : Bool},
  ec: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool}
) -> {T.doc.read(SCon{Chr{uu}, tail}, sv.eat(cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab))
  == T.doc.read(tail, sv.eat(cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un, lf, ab)) : T.Doc}:
  Equal.cong(T.Mode, T.Doc, md => T.doc.read(tail, md),
    T.eat.feed(True{}, '"', cut, nn, bd, rw, hs, he, ps, T.QBasic{}, sk, un, lf, ab, Chr{uu}),
    sv.eat(cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un, lf, ab),
    se.q(U32.is_eq(uu, 34), uu, cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab, e34, e92, ec))

# the closing quote places the span, with back at LStr
def se.close(
  +rest: String,
  +cut: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool
) -> {T.doc.read(SCon{'"', rest}, sv.eat(cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab))
  == T.doc.read(rest, T.MScan{sv.took(sk, T.VSpan{cut, nn}, bd, rw, hs, he, ps, T.LStr{}, un, lf,
    ab)}) : T.Doc}:
  {==}

# The span's characters. Counting a text's characters in a Nat (plus, from
# render_parse_plain_pair's proof) runs through an append one part at a time.

# the count after two texts is the count after the second, from the count
# after the first
def plus.app(
  xs: String,
  +ys: String,
  nn: Nat
) -> {plus(String.append(xs, ys), nn) == plus(ys, plus(xs, nn)) : Nat}:
  match xs:
    case SNil{}:
      {==}
    case SCon{_hh, tt}:
      plus.app(tt, ys, 1n+nn)

# no characters of any text
def take.zero(ss: String) -> {take(ss, 0n) == SNil{} : String}:
  match ss:
    case SNil{}:
      {==}
    case SCon{_hh, _tt}:
      {==}

# a span of a text that starts with pre, counting pre's characters, is pre
def sp.pre(
  +pre: String,
  +cut: String,
  +more: String,
  +nn: U32,
  hc: {cut == String.append(pre, more) : String},
  hn: {U32.to_nat(nn) == plus(pre, 0n) : Nat}
) -> {take(cut, U32.to_nat(nn)) == pre : String}:
  Equal.trans(String, take(cut, U32.to_nat(nn)), take(String.append(pre, more), plus(pre, 0n)), pre,
    Equal.trans(String, take(cut, U32.to_nat(nn)), take(String.append(pre, more), U32.to_nat(nn)),
      take(String.append(pre, more), plus(pre, 0n)),
      Equal.cong(String, String, xs => take(xs, U32.to_nat(nn)), cut, String.append(pre, more), hc),
      Equal.cong(Nat, String, kk => take(String.append(pre, more), kk), U32.to_nat(nn), plus(pre, 0n),
        hn)),
    Equal.trans(String, take(String.append(pre, more), plus(pre, 0n)),
      String.append(pre, take(more, 0n)), pre,
      take.app(pre, more, 0n),
      Equal.trans(String, String.append(pre, take(more, 0n)), String.append(pre, SNil{}), pre,
        Equal.cong(String, String, xs => String.append(pre, xs), take(more, 0n), SNil{},
          take.zero(more)),
        Eq.append_nil(pre))))

# the placed span holds the characters counted into it
def se.own(
  +pre: String,
  +cut: String,
  +more: String,
  +nn: U32,
  hc: {cut == String.append(pre, more) : String},
  hn: {U32.to_nat(nn) == plus(pre, 0n) : Nat}
) -> sv.Is(T.VSpan{cut, nn}, pre):
  Equal.trans(String, T.span.str(cut, nn, U32.is_zero(nn)), take(cut, U32.to_nat(nn)), pre,
    sp.take(cut, nn), sp.pre(pre, cut, more, nn, hc, hn))

# The escapes. Once a character needs an escape the span is copied into the
# buffer (eat.copy, span.rev) and the rest of the string is read in LStr,
# one character of escs at a time: a plain character on the fast path, an
# escape through LEsc, and a \u escape through LUni. back stays at LStr all
# the way; a \u escape leaves uni and left at 0, so a per-character step
# takes the rest of the walk as a function of those two, as qs does of back.

# a scanner inside a basic string being copied, its characters so far
# reversed in buf
def ls(
  bd: String,
  rw: List<&2, T.Val>,
  hs: List<&2, String>,
  he: List<&2, String>,
  ps: List<&2, String>,
  sk: List<&2, T.Ctx>,
  ab: Bool,
  un: U32,
  lf: U32,
  buf: List<&2, Char>
) -> T.St:
  T.St{bd, rw, hs, he, ps, buf, T.LStr{}, T.LStr{}, T.QBasic{}, sk, T.HNone{}, un, lf, ab, False{}}

# the rest of the walk from a string with buf in its buffer, whatever uni
# and left are
def ls.Then(
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  @u2: U32 -> @l2: U32 ->
    PP(T.doc.read(rest, T.MScan{ls(bd, rw, hs, he, ps, sk, ab, u2, l2, buf)}))

# one character's escape read in a string, then the rest of the text: the
# rest is read with the character pushed, from whatever uni and left the
# escape left
def ls.Goal(
  +uu: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  (@u2: U32 -> @l2: U32 ->
    PP(T.doc.read(rest, T.MScan{ls(bd, rw, hs, he, ps, sk, ab, u2, l2, Chr{uu} <> buf)}))) ->
    PP(T.doc.read(String.append(Laws.esc(Chr{uu}), rest), T.MScan{ls(bd, rw, hs, he, ps, sk, ab, un, lf, buf)}))

# a character that is no control is pushed: str.bad passes it
def ls.push(
  ctl: Bool,
  +uu: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  hc: {ctl == False{} : Bool}
) -> {T.read.fast.push(T.str.bad.go(ctl, U32.is_eq(uu, 9), Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)),
  False{}), bd, rw, hs, he, ps, buf, T.LStr{}, T.LStr{}, T.QBasic{}, sk, un, lf, ab, Chr{uu})
  == ls(bd, rw, hs, he, ps, sk, ab, un, lf, Chr{uu} <> buf) : T.St}:
  match ctl:
    case False{}:
      {==}
    case True{}:
      Eq.bit.absurd2(&2, {T.read.fast.push(T.str.bad.go(True{}, U32.is_eq(uu, 9),
        Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)), False{}), bd, rw, hs, he, ps, buf, T.LStr{},
        T.LStr{}, T.QBasic{}, sk, un, lf, ab, Chr{uu}) == ls(bd, rw, hs, he, ps, sk, ab, un, lf,
        Chr{uu} <> buf) : T.St}, hc)

# a character that is no quote and no backslash is no closer and no escape
def ls.go(
  quote: Bool,
  bs: Bool,
  +uu: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  hq: {quote == False{} : Bool},
  hb: {bs == False{} : Bool},
  hc: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool}
) -> {T.read.fast.basic(quote, bs, bd, rw, hs, he, ps, buf, T.LStr{}, sk, un, lf, ab, Chr{uu})
  == ls(bd, rw, hs, he, ps, sk, ab, un, lf, Chr{uu} <> buf) : T.St}:
  match quote:
    case True{}:
      Eq.bit.absurd2(&2, {T.read.fast.basic(True{}, bs, bd, rw, hs, he, ps, buf, T.LStr{}, sk, un,
        lf, ab, Chr{uu}) == ls(bd, rw, hs, he, ps, sk, ab, un, lf, Chr{uu} <> buf) : T.St}, hq)
    case False{}:
      match bs:
        case True{}:
          Eq.bit.absurd2(&2, {T.read.fast.basic(False{}, True{}, bd, rw, hs, he, ps, buf, T.LStr{},
            sk, un, lf, ab, Chr{uu}) == ls(bd, rw, hs, he, ps, sk, ab, un, lf, Chr{uu} <> buf)
            : T.St}, hb)
        case False{}:
          ls.push(Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), uu, bd, rw, hs, he, ps, sk, ab, un,
            lf, buf, hc)

# the fast step pushes a character
def ls.Fast(
  +uu: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>
) -> Type:
  {T.read.fast(ls(bd, rw, hs, he, ps, sk, ab, un, lf, buf), Chr{uu})
    == ls(bd, rw, hs, he, ps, sk, ab, un, lf, Chr{uu} <> buf) : T.St}

# the doc.scan dispatch sends such a character to the fast step, and an
# apostrophe comes back from doc.wrap in the string's state
def ls.q(
  dq: Bool,
  sq: Bool,
  cr: Bool,
  +uu: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  hq: {dq == False{} : Bool},
  hr: {cr == False{} : Bool},
  fast: ls.Fast(uu, bd, rw, hs, he, ps, sk, ab, un, lf, buf)
) -> {T.doc.scan.q(dq, sq, cr, ls(bd, rw, hs, he, ps, sk, ab, un, lf, buf), Chr{uu})
  == T.MScan{ls(bd, rw, hs, he, ps, sk, ab, un, lf, Chr{uu} <> buf)} : T.Mode}:
  match dq:
    case True{}:
      Eq.bit.absurd2(&2, {T.doc.scan.q(True{}, sq, cr, ls(bd, rw, hs, he, ps, sk, ab, un, lf, buf),
        Chr{uu}) == T.MScan{ls(bd, rw, hs, he, ps, sk, ab, un, lf, Chr{uu} <> buf)} : T.Mode}, hq)
    case False{}:
      match sq:
        case True{}:
          Equal.cong(T.St, T.Mode, st => T.doc.wrap(st),
            T.read.fast(ls(bd, rw, hs, he, ps, sk, ab, un, lf, buf), Chr{uu}),
            ls(bd, rw, hs, he, ps, sk, ab, un, lf, Chr{uu} <> buf), fast)
        case False{}:
          match cr:
            case True{}:
              Eq.bit.absurd2(&2, {T.doc.scan.q(False{}, False{}, True{}, ls(bd, rw, hs, he, ps, sk,
                ab, un, lf, buf), Chr{uu}) == T.MScan{ls(bd, rw, hs, he, ps, sk, ab, un, lf,
                Chr{uu} <> buf)} : T.Mode}, hr)
            case False{}:
              Equal.cong(T.St, T.Mode, st => T.MScan{st},
                T.read.fast(ls(bd, rw, hs, he, ps, sk, ab, un, lf, buf), Chr{uu}),
                ls(bd, rw, hs, he, ps, sk, ab, un, lf, Chr{uu} <> buf), fast)

# a character that is no control, quotation mark or backslash is written as
# itself
def esc.pl2(
  +uu: U32,
  e34: {U32.is_eq(uu, 34) == False{} : Bool},
  e92: {U32.is_eq(uu, 92) == False{} : Bool},
  +ec: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool}
) -> {Laws.esc(Chr{uu}) == SCon{Chr{uu}, SNil{}} : String}:
  ek = cls.plain(uu, ctl.off(uu, 8, ec, {==}), ctl.off(uu, 9, ec, {==}), ctl.off(uu, 10, ec, {==}),
    ctl.off(uu, 12, ec, {==}), ctl.off(uu, 13, ec, {==}), e34, e92, ec)
  %Equal.sym(T.BK, T.basic.cls(uu), T.BKCh{}, ek) :
    {String.from_list(List.reverse(&2, Char, T.basic.disp(_, Chr{uu}, uu, []))) == SCon{Chr{uu}, SNil{}}
      : String}
  {==}

# a character written as itself is pushed, and uni and left stay as they
# were
def ls.plain(
  +uu: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  +e34: {U32.is_eq(uu, 34) == False{} : Bool},
  +e92: {U32.is_eq(uu, 92) == False{} : Bool},
  +ec: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool},
  ih: ls.Then(bd, rw, hs, he, ps, sk, ab, Chr{uu} <> buf, rest, PP)
) -> PP(T.doc.read(String.append(Laws.esc(Chr{uu}), rest), T.MScan{ls(bd, rw, hs, he, ps, sk, ab, un, lf, buf)})):
  +e13 = {ctl.off(uu, 13, ec, {==}) : {U32.is_eq(uu, 13) == False{} : Bool}}
  %Equal.sym(String, Laws.esc(Chr{uu}), SCon{Chr{uu}, SNil{}}, esc.pl2(uu, e34, e92, ec)) :
    PP(T.doc.read(String.append(_, rest), T.MScan{ls(bd, rw, hs, he, ps, sk, ab, un, lf, buf)}))
  pp.step(PP,
    T.doc.read(rest, T.doc.scan(ls(bd, rw, hs, he, ps, sk, ab, un, lf, buf), Chr{uu})),
    T.doc.read(rest, T.MScan{ls(bd, rw, hs, he, ps, sk, ab, un, lf, Chr{uu} <> buf)}),
    Equal.cong(T.Mode, T.Doc, md => T.doc.read(rest, md),
      T.doc.scan(ls(bd, rw, hs, he, ps, sk, ab, un, lf, buf), Chr{uu}),
      T.MScan{ls(bd, rw, hs, he, ps, sk, ab, un, lf, Chr{uu} <> buf)},
      ls.q(U32.is_eq(uu, 34), U32.is_eq(uu, 39), U32.is_eq(uu, 13), uu, bd, rw, hs, he, ps, sk, ab, un,
        lf, buf, e34, e13,
        ls.go(U32.is_eq(uu, 34), U32.is_eq(uu, 92), uu, bd, rw, hs, he, ps, sk, ab, un, lf, buf, e34,
          e92, ec))),
    ih(un, lf))

# a quotation mark: its escape reads back by computation, and leaves uni and
# left as they were
def ls.q34(
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type
) -> ls.Goal(34, bd, rw, hs, he, ps, sk, ab, un, lf, buf, rest, PP):
  ih => ih(un, lf)

# and a backslash
def ls.q92(
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type
) -> ls.Goal(92, bd, rw, hs, he, ps, sk, ab, un, lf, buf, rest, PP):
  ih => ih(un, lf)

# CTL: ls.Goal with the escape's text as ss, for ctl.esc.all
def ls.GoalS(
  +uu: U32,
  ss: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  (@u2: U32 -> @l2: U32 ->
    PP(T.doc.read(rest, T.MScan{ls(bd, rw, hs, he, ps, sk, ab, u2, l2, Chr{uu} <> buf)}))) ->
    PP(T.doc.read(String.append(ss, rest), T.MScan{ls(bd, rw, hs, he, ps, sk, ab, un, lf, buf)}))

# a control: each of the thirty-three escapes reads back by computation. The
# five with a letter (\b, \t, \n, \f, \r) leave uni and left as they were; a
# \u escape leaves both at 0
def ls.ctl(
  +uu: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  h_c: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == True{} : Bool}
) -> ls.Goal(uu, bd, rw, hs, he, ps, sk, ab, un, lf, buf, rest, PP):
  ctl.esc.all(kk => ss => ls.GoalS(kk, ss, bd, rw, hs, he, ps, sk, ab, un, lf, buf, rest, PP), uu, h_c,
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(un, lf),
    ih => ih(un, lf),
    ih => ih(un, lf),
    ih => ih(0, 0),
    ih => ih(un, lf),
    ih => ih(un, lf),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0),
    ih => ih(0, 0))

# one code point k that the test found: its answer answers for the character
def ls.is(
  +uu: U32,
  +kk: U32,
  ee: {U32.is_eq(uu, kk) == True{} : Bool},
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  at: ls.Goal(kk, bd, rw, hs, he, ps, sk, ab, un, lf, buf, rest, PP)
) -> ls.Goal(uu, bd, rw, hs, he, ps, sk, ab, un, lf, buf, rest, PP):
  eu = Equal.cong(Char, U32, cc => Char.to_u32(cc), Chr{uu}, Chr{kk}, Eq.u32_eq(uu, kk, ee))
  %Equal.sym(U32, uu, kk, eu) : ls.Goal(_, bd, rw, hs, he, ps, sk, ab, un, lf, buf, rest, PP)
  at

# every character: a quote, a backslash, a control, or one written as itself
def ls.split(
  +uu: U32,
  q34: Bool,
  b92: Bool,
  ctl: Bool,
  +e34: {U32.is_eq(uu, 34) == q34 : Bool},
  +e92: {U32.is_eq(uu, 92) == b92 : Bool},
  +ec: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == ctl : Bool},
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type
) -> ls.Goal(uu, bd, rw, hs, he, ps, sk, ab, un, lf, buf, rest, PP):
  match q34:
    case True{}:
      ls.is(uu, 34, e34, bd, rw, hs, he, ps, sk, ab, un, lf, buf, rest, PP,
        ls.q34(bd, rw, hs, he, ps, sk, ab, un, lf, buf, rest, PP))
    case False{}:
      match b92:
        case True{}:
          ls.is(uu, 92, e92, bd, rw, hs, he, ps, sk, ab, un, lf, buf, rest, PP,
            ls.q92(bd, rw, hs, he, ps, sk, ab, un, lf, buf, rest, PP))
        case False{}:
          match ctl:
            case True{}:
              ls.ctl(uu, bd, rw, hs, he, ps, sk, ab, un, lf, buf, rest, PP, ec)
            case False{}:
              ih => ls.plain(uu, bd, rw, hs, he, ps, sk, ab, un, lf, buf, rest, PP, e34, e92, ec, ih)

# one character of a string
def ls.one(
  +uu: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type
) -> ls.Goal(uu, bd, rw, hs, he, ps, sk, ab, un, lf, buf, rest, PP):
  ls.split(uu, U32.is_eq(uu, 34), U32.is_eq(uu, 92), Bool.or(U32.is_lt(uu, 32),
    U32.is_eq(uu, 127)), {==}, {==}, {==}, bd, rw, hs, he, ps, sk, ab, un, lf, buf, rest, PP)

# every character of a string, as escs writes it, read in LStr: the rest is
# read with the characters pushed, from whatever uni and left the last escape
# left
def ls.escs(
  ss: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  ih: ls.Then(bd, rw, hs, he, ps, sk, ab, rev.onto(ss, buf), rest, PP)
) -> PP(T.doc.read(String.append(Laws.escs(ss), rest), T.MScan{ls(bd, rw, hs, he, ps, sk, ab, un, lf, buf)})):
  match ss:
    case SNil{}:
      ih(un, lf)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+uu}:
          pp.step(PP,
            T.doc.read(String.append(String.append(Laws.esc(Chr{uu}), Laws.escs(tt)), rest),
              T.MScan{ls(bd, rw, hs, he, ps, sk, ab, un, lf, buf)}),
            T.doc.read(String.append(Laws.esc(Chr{uu}), String.append(Laws.escs(tt), rest)),
              T.MScan{ls(bd, rw, hs, he, ps, sk, ab, un, lf, buf)}),
            Equal.cong(String, T.Doc, xs => T.doc.read(xs, T.MScan{ls(bd, rw, hs, he, ps, sk, ab, un, lf,
              buf)}),
              String.append(String.append(Laws.esc(Chr{uu}), Laws.escs(tt)), rest),
              String.append(Laws.esc(Chr{uu}), String.append(Laws.escs(tt), rest)),
              Eq.append_assoc(Laws.esc(Chr{uu}), Laws.escs(tt), rest)),
            ls.one(uu, bd, rw, hs, he, ps, sk, ab, un, lf, buf, String.append(Laws.escs(tt), rest), PP)(
              u2 => l2 => ls.escs(tt, bd, rw, hs, he, ps, sk, ab, u2, l2, Chr{uu} <> buf, rest, PP, ih)))

# the closing quote places the owned string, with back at LStr
def ls.close(
  +rest: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>
) -> {T.doc.read(SCon{'"', rest}, T.MScan{ls(bd, rw, hs, he, ps, sk, ab, un, lf, buf)})
  == T.doc.read(rest, T.MScan{sv.took(sk, T.VStr{T.buf.str(buf)}, bd, rw, hs, he, ps, T.LStr{}, un, lf,
    ab)}) : T.Doc}:
  Equal.cong(T.Mode, T.Doc, md => T.doc.read(rest, md),
    T.doc.wrap(T.read.once2(sv.took(sk, T.VStr{T.buf.str(buf)}, bd, rw, hs, he, ps, T.LStr{}, un, lf,
      ab))),
    T.MScan{sv.took(sk, T.VStr{T.buf.str(buf)}, bd, rw, hs, he, ps, T.LStr{}, un, lf, ab)},
    tk.fix(sk, T.VStr{T.buf.str(buf)}, bd, rw, hs, he, ps, T.LStr{}, T.QBasic{}, un, lf, ab, False{}))

# a buffer the text pre and then ss were pushed onto holds pre and ss
def ls.own(
  +pre: String,
  +ss: String
) -> sv.Is(T.VStr{T.buf.str(rev.onto(ss, rev.onto(pre, [])))}, String.append(pre, ss)):
  Equal.trans(String, T.buf.str.go(rev.onto(ss, rev.onto(pre, [])), ""),
    T.buf.str.go(rev.onto(pre, []), String.append(ss, "")), String.append(pre, ss),
    ml.rev(ss, rev.onto(pre, []), ""),
    Equal.trans(String, T.buf.str.go(rev.onto(pre, []), String.append(ss, "")),
      String.append(pre, String.append(ss, "")), String.append(pre, ss),
      ml.rev(pre, [], String.append(ss, "")),
      Equal.cong(String, String, xs => String.append(pre, xs), String.append(ss, ""), ss,
        Eq.append_nil(ss))))

# the rest of a string, from a buffer holding pre: the escapes of ss and the
# closing quote read to the value pre and ss placed
def ls.fin(
  +ss: String,
  +pre: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +un: U32,
  +lf: U32,
  +rest: String,
  -PP: T.Doc -> Type,
  ih: sv.Then(String.append(pre, ss), bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(String.append(Laws.escs(ss), SCon{'"', rest}),
  T.MScan{ls(bd, rw, hs, he, ps, sk, ab, un, lf, rev.onto(pre, []))})):
  ls.escs(ss, bd, rw, hs, he, ps, sk, ab, un, lf, rev.onto(pre, []), SCon{'"', rest}, PP,
    +u2 => +l2 => pp.step(PP,
      T.doc.read(SCon{'"', rest}, T.MScan{ls(bd, rw, hs, he, ps, sk, ab, u2, l2,
        rev.onto(ss, rev.onto(pre, [])))}),
      T.doc.read(rest, T.MScan{sv.took(sk, T.VStr{T.buf.str(rev.onto(ss, rev.onto(pre, [])))}, bd, rw,
        hs, he, ps, T.LStr{}, u2, l2, ab)}),
      ls.close(rest, bd, rw, hs, he, ps, sk, ab, u2, l2, rev.onto(ss, rev.onto(pre, []))),
      ih(T.VStr{T.buf.str(rev.onto(ss, rev.onto(pre, [])))}, T.LStr{}, u2, l2, ls.own(pre, ss))))

# A character that needs an escape starts it with a backslash, whichever it
# is, so the span meets a backslash there and copies itself.

# a text with its first character dropped
def str.tl(ss: String) -> String:
  match ss:
    case SNil{}:
      SNil{}
    case SCon{_hh, tt}:
      tt

# render writes the character with a backslash first
def esc.Lead(+uu: U32) -> Type:
  {Laws.esc(Chr{uu}) == SCon{'\\', str.tl(Laws.esc(Chr{uu}))} : String}

# one code point k that the test found
def esc.lead.is(
  +uu: U32,
  +kk: U32,
  ee: {U32.is_eq(uu, kk) == True{} : Bool},
  at: esc.Lead(kk)
) -> esc.Lead(uu):
  eu = Equal.cong(Char, U32, cc => Char.to_u32(cc), Chr{uu}, Chr{kk}, Eq.u32_eq(uu, kk, ee))
  %Equal.sym(U32, uu, kk, eu) : esc.Lead(_)
  at

# every control: its escape is ctl.txt, a backslash first
def esc.lead.ctl(
  +uu: U32,
  h_c: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == True{} : Bool}
) -> esc.Lead(uu):
  %ctl.esc.lit(uu, h_c) : {_ == SCon{'\\', str.tl(_)} : String}
  {==}

# span.rev copies the span's first n characters, reversed onto acc
def sp.Rv(+src: String, +nn: U32, +acc: List<&2, Char>) -> Type:
  {T.span.rev(src, nn, U32.is_zero(nn), acc) == rev.onto(take(src, U32.to_nat(nn)), acc) : List<&2, Char>}

# the span's first n characters, reversed onto acc, are what span.rev copies
def sp.rv.nil(
  nn: U32,
  bz: Bool,
  +acc: List<&2, Char>
) -> {T.span.rev(SNil{}, nn, bz, acc) == rev.onto(take(SNil{}, U32.to_nat(nn)), acc) : List<&2, Char>}:
  match bz:
    case True{}:
      {==}
    case False{}:
      {==}

# a character and the rest, once the zero test's answer is named
def sp.rv.cons(
  +hd: Char,
  +tl: String,
  +nn: U32,
  bz: Bool,
  ez: {U32.is_zero(nn) == bz : Bool},
  +acc: List<&2, Char>,
  ih: sp.Rv(tl, U32.sub(nn, 1), hd <> acc)
) -> {T.span.rev(SCon{hd, tl}, nn, bz, acc) == rev.onto(take(SCon{hd, tl}, U32.to_nat(nn)), acc)
  : List<&2, Char>}:
  match bz:
    case True{}:
      e0 = Equal.cong(Char, U32, cc => Char.to_u32(cc), Chr{nn}, Chr{0}, Eq.u32_eq(nn, 0, ez))
      %Equal.sym(U32, nn, 0, e0) : {T.span.rev(SCon{hd, tl}, nn, True{}, acc) == rev.onto(take(SCon{hd, tl},
        U32.to_nat(_)), acc) : List<&2, Char>}
      {==}
    case False{}:
      en = Equal.sym(Nat, U32.to_nat(nn), 1n+U32.to_nat(U32.sub(nn, 1)), Eq.u32_dec_nat(nn, ez))
      %en : {T.span.rev(tl, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)), hd <> acc)
        == rev.onto(take(SCon{hd, tl}, _), acc) : List<&2, Char>}
      ih

# span.rev copies the span's characters, reversed
def sp.rv(
  src: String,
  +nn: U32,
  +acc: List<&2, Char>
) -> {T.span.rev(src, nn, U32.is_zero(nn), acc) == rev.onto(take(src, U32.to_nat(nn)), acc)
  : List<&2, Char>}:
  match src:
    case SNil{}:
      sp.rv.nil(nn, U32.is_zero(nn), acc)
    case SCon{+hd, +tl}:
      sp.rv.cons(hd, tl, nn, U32.is_zero(nn), {==}, acc, sp.rv(tl, U32.sub(nn, 1), hd <> acc))

# the copied span of a text that starts with pre, counting pre's characters,
# is pre reversed
def se.rev(
  +pre: String,
  +cut: String,
  +more: String,
  +nn: U32,
  hc: {cut == String.append(pre, more) : String},
  hn: {U32.to_nat(nn) == plus(pre, 0n) : Nat}
) -> {T.span.rev(cut, nn, U32.is_zero(nn), []) == rev.onto(pre, []) : List<&2, Char>}:
  Equal.trans(List<&2, Char>, T.span.rev(cut, nn, U32.is_zero(nn), []), rev.onto(take(cut, U32.to_nat(nn)), []),
    rev.onto(pre, []),
    sp.rv(cut, nn, []),
    Equal.cong(String, List<&2, Char>, xs => rev.onto(xs, []), take(cut, U32.to_nat(nn)), pre,
      sp.pre(pre, cut, more, nn, hc, hn)))

# a backslash in the span copies it and starts an escape, as a backslash in
# the copied string does
def se.copy(
  +xx: String,
  +cut: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool
) -> {T.doc.read(SCon{'\\', xx}, sv.eat(cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab))
  == T.doc.read(SCon{'\\', xx}, T.MScan{ls(bd, rw, hs, he, ps, sk, ab, un, lf,
    T.span.rev(cut, nn, U32.is_zero(nn), []))}) : T.Doc}:
  {==}

# so does a character that needs an escape, then the rest of the string
def se.copy.esc(
  +uu: U32,
  ee: esc.Lead(uu),
  +tt: String,
  +rest: String,
  +cut: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool
) -> {T.doc.read(String.append(String.append(Laws.esc(Chr{uu}), Laws.escs(tt)), SCon{'"', rest}),
  sv.eat(cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab))
  == T.doc.read(String.append(String.append(Laws.esc(Chr{uu}), Laws.escs(tt)), SCon{'"', rest}),
    T.MScan{ls(bd, rw, hs, he, ps, sk, ab, un, lf, T.span.rev(cut, nn, U32.is_zero(nn), []))}) : T.Doc}:
  %Equal.sym(String, Laws.esc(Chr{uu}), SCon{'\\', str.tl(Laws.esc(Chr{uu}))}, ee) :
    {T.doc.read(String.append(String.append(_, Laws.escs(tt)), SCon{'"', rest}),
      sv.eat(cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab))
      == T.doc.read(String.append(String.append(_, Laws.escs(tt)), SCon{'"', rest}),
        T.MScan{ls(bd, rw, hs, he, ps, sk, ab, un, lf, T.span.rev(cut, nn, U32.is_zero(nn), []))}) : T.Doc}
  se.copy(String.append(String.append(str.tl(Laws.esc(Chr{uu})), Laws.escs(tt)), SCon{'"', rest}), cut, nn,
    bd, rw, hs, he, ps, sk, un, lf, ab)

# a character that needs an escape ends the span: the copy holds pre, and the
# rest of the string is read in LStr
def se.esc(
  +uu: U32,
  ee: esc.Lead(uu),
  +tt: String,
  +pre: String,
  +cut: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  hc: {cut == String.append(pre, String.append(Laws.escs(SCon{Chr{uu}, tt}), SCon{'"', rest})) : String},
  hn: {U32.to_nat(nn) == plus(pre, 0n) : Nat},
  ih: sv.Then(String.append(pre, SCon{Chr{uu}, tt}), bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(String.append(Laws.escs(SCon{Chr{uu}, tt}), SCon{'"', rest}),
  sv.eat(cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab))):
  pp.step(PP,
    T.doc.read(String.append(Laws.escs(SCon{Chr{uu}, tt}), SCon{'"', rest}),
      sv.eat(cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab)),
    T.doc.read(String.append(Laws.escs(SCon{Chr{uu}, tt}), SCon{'"', rest}),
      T.MScan{ls(bd, rw, hs, he, ps, sk, ab, un, lf, T.span.rev(cut, nn, U32.is_zero(nn), []))}),
    se.copy.esc(uu, ee, tt, rest, cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab),
    pp.step(PP,
      T.doc.read(String.append(Laws.escs(SCon{Chr{uu}, tt}), SCon{'"', rest}),
        T.MScan{ls(bd, rw, hs, he, ps, sk, ab, un, lf, T.span.rev(cut, nn, U32.is_zero(nn), []))}),
      T.doc.read(String.append(Laws.escs(SCon{Chr{uu}, tt}), SCon{'"', rest}),
        T.MScan{ls(bd, rw, hs, he, ps, sk, ab, un, lf, rev.onto(pre, []))}),
      Equal.cong(List<&2, Char>, T.Doc, bb => T.doc.read(String.append(Laws.escs(SCon{Chr{uu}, tt}),
        SCon{'"', rest}), T.MScan{ls(bd, rw, hs, he, ps, sk, ab, un, lf, bb)}),
        T.span.rev(cut, nn, U32.is_zero(nn), []), rev.onto(pre, []),
        se.rev(pre, cut, String.append(Laws.escs(SCon{Chr{uu}, tt}), SCon{'"', rest}), nn, hc, hn)),
      ls.fin(SCon{Chr{uu}, tt}, pre, bd, rw, hs, he, ps, sk, ab, un, lf, rest, PP, ih)))

# the text of the span after pre and a plain character: the character joins
# pre
def se.cut(
  +uu: U32,
  +tt: String,
  +pre: String,
  +cut: String,
  +rest: String,
  ep: {Laws.esc(Chr{uu}) == SCon{Chr{uu}, SNil{}} : String},
  hc: {cut == String.append(pre, String.append(Laws.escs(SCon{Chr{uu}, tt}), SCon{'"', rest})) : String}
) -> {cut == String.append(String.append(pre, SCon{Chr{uu}, SNil{}}),
  String.append(Laws.escs(tt), SCon{'"', rest})) : String}:
  Equal.trans(String, cut,
    String.append(pre, SCon{Chr{uu}, String.append(Laws.escs(tt), SCon{'"', rest})}),
    String.append(String.append(pre, SCon{Chr{uu}, SNil{}}), String.append(Laws.escs(tt), SCon{'"', rest})),
    Equal.trans(String, cut,
      String.append(pre, String.append(String.append(Laws.esc(Chr{uu}), Laws.escs(tt)), SCon{'"', rest})),
      String.append(pre, SCon{Chr{uu}, String.append(Laws.escs(tt), SCon{'"', rest})}),
      hc,
      Equal.cong(String, String, xs => String.append(pre, String.append(String.append(xs, Laws.escs(tt)),
        SCon{'"', rest})), Laws.esc(Chr{uu}), SCon{Chr{uu}, SNil{}}, ep)),
    Equal.sym(String,
      String.append(String.append(pre, SCon{Chr{uu}, SNil{}}), String.append(Laws.escs(tt), SCon{'"', rest})),
      String.append(pre, SCon{Chr{uu}, String.append(Laws.escs(tt), SCon{'"', rest})}),
      Eq.append_assoc(pre, SCon{Chr{uu}, SNil{}}, String.append(Laws.escs(tt), SCon{'"', rest}))))

# the rest of the string after a plain character, read from the span grown
# by it: the induction hypothesis of se.go, given the text it was cut from
# and the rest of the walk
def se.Rec(
  +uu: U32,
  +tt: String,
  +pre: String,
  +cut: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  {cut == String.append(String.append(pre, SCon{Chr{uu}, SNil{}}),
    String.append(Laws.escs(tt), SCon{'"', rest})) : String} ->
    sv.Then(String.append(String.append(pre, SCon{Chr{uu}, SNil{}}), tt), bd, rw, hs, he, ps, sk, ab, rest,
      PP) ->
    PP(T.doc.read(String.append(Laws.escs(tt), SCon{'"', rest}),
      sv.eat(cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un, lf, ab)))

# a plain character grows the span, and the rest of the string is read from
# there
def se.plain(
  +uu: U32,
  +e34: {U32.is_eq(uu, 34) == False{} : Bool},
  +e92: {U32.is_eq(uu, 92) == False{} : Bool},
  +ec: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool},
  +tt: String,
  +pre: String,
  +cut: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  hc: {cut == String.append(pre, String.append(Laws.escs(SCon{Chr{uu}, tt}), SCon{'"', rest})) : String},
  ih: sv.Then(String.append(pre, SCon{Chr{uu}, tt}), bd, rw, hs, he, ps, sk, ab, rest, PP),
  rec: se.Rec(uu, tt, pre, cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab, rest, PP)
) -> PP(T.doc.read(String.append(Laws.escs(SCon{Chr{uu}, tt}), SCon{'"', rest}),
  sv.eat(cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab))):
  +ep = {esc.pl2(uu, e34, e92, ec) : {Laws.esc(Chr{uu}) == SCon{Chr{uu}, SNil{}} : String}}
  %Equal.sym(String, Laws.esc(Chr{uu}), SCon{Chr{uu}, SNil{}}, ep) :
    PP(T.doc.read(String.append(String.append(_, Laws.escs(tt)), SCon{'"', rest}),
      sv.eat(cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab)))
  pp.step(PP,
    T.doc.read(SCon{Chr{uu}, String.append(Laws.escs(tt), SCon{'"', rest})},
      sv.eat(cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab)),
    T.doc.read(String.append(Laws.escs(tt), SCon{'"', rest}),
      sv.eat(cut, U32.add(nn, 1), bd, rw, hs, he, ps, sk, un, lf, ab)),
    se.one(uu, String.append(Laws.escs(tt), SCon{'"', rest}), cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab,
      e34, e92, ec),
    rec(se.cut(uu, tt, pre, cut, rest, ep, hc),
      sv.then.cast(String.append(pre, SCon{Chr{uu}, tt}), String.append(String.append(pre, SCon{Chr{uu},
        SNil{}}), tt), Equal.sym(String, String.append(String.append(pre, SCon{Chr{uu}, SNil{}}), tt),
        String.append(pre, SCon{Chr{uu}, tt}), Eq.append_assoc(pre, SCon{Chr{uu}, SNil{}}, tt)),
        bd, rw, hs, he, ps, sk, ab, rest, PP, ih)))

# one character of the string inside the span: a quote, a backslash or a
# control ends the span, and any other grows it
def se.step(
  +uu: U32,
  q34: Bool,
  b92: Bool,
  ctl: Bool,
  +e34: {U32.is_eq(uu, 34) == q34 : Bool},
  +e92: {U32.is_eq(uu, 92) == b92 : Bool},
  +ec: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == ctl : Bool},
  +tt: String,
  +pre: String,
  +cut: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  +hc: {cut == String.append(pre, String.append(Laws.escs(SCon{Chr{uu}, tt}), SCon{'"', rest})) : String},
  +hn: {U32.to_nat(nn) == plus(pre, 0n) : Nat},
  ih: sv.Then(String.append(pre, SCon{Chr{uu}, tt}), bd, rw, hs, he, ps, sk, ab, rest, PP),
  rec: se.Rec(uu, tt, pre, cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab, rest, PP)
) -> PP(T.doc.read(String.append(Laws.escs(SCon{Chr{uu}, tt}), SCon{'"', rest}),
  sv.eat(cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab))):
  match q34:
    case True{}:
      se.esc(uu, esc.lead.is(uu, 34, e34, {==}), tt, pre, cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab, rest,
        PP, hc, hn, ih)
    case False{}:
      match b92:
        case True{}:
          se.esc(uu, esc.lead.is(uu, 92, e92, {==}), tt, pre, cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab,
            rest, PP, hc, hn, ih)
        case False{}:
          match ctl:
            case True{}:
              se.esc(uu, esc.lead.ctl(uu, ec), tt, pre, cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab, rest,
                PP, hc, hn, ih)
            case False{}:
              se.plain(uu, e34, e92, ec, tt, pre, cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab, rest, PP,
                hc, ih, rec)

# the rest ss of a string inside its span, pre read so far: cut is the text
# from the string's first character, and nn counts pre's characters without
# wrapping. The string reads to a value holding pre and ss (sv.Is): the span
# itself when ss needs no escape, and the copied string otherwise
def se.go(
  ss: String,
  +pre: String,
  +cut: String,
  +nn: U32,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  +hc: {cut == String.append(pre, String.append(Laws.escs(ss), SCon{'"', rest})) : String},
  +hn: {U32.to_nat(nn) == plus(pre, 0n) : Nat},
  +hk: {Laws.counts(ss, nn) == True{} : Bool},
  ih: sv.Then(String.append(pre, ss), bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(String.append(Laws.escs(ss), SCon{'"', rest}),
  sv.eat(cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab))):
  match ss:
    case SNil{}:
      pp.step(PP,
        T.doc.read(SCon{'"', rest}, sv.eat(cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab)),
        T.doc.read(rest, T.MScan{sv.took(sk, T.VSpan{cut, nn}, bd, rw, hs, he, ps, T.LStr{}, un, lf, ab)}),
        se.close(rest, cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab),
        sv.then.cast(String.append(pre, SNil{}), pre, Eq.append_nil(pre), bd, rw, hs, he, ps, sk, ab, rest,
          PP, ih)(T.VSpan{cut, nn}, T.LStr{}, un, lf, se.own(pre, cut, SCon{'"', rest}, nn, hc, hn)))
    case SCon{hh, +tt}:
      match hh:
        case Chr{+uu}:
          se.step(uu, U32.is_eq(uu, 34), U32.is_eq(uu, 92), Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)),
            {==}, {==}, {==}, tt, pre, cut, nn, bd, rw, hs, he, ps, sk, un, lf, ab, rest, PP, hc, hn, ih,
            hc2 => ih2 => se.go(tt, String.append(pre, SCon{Chr{uu}, SNil{}}), cut, U32.add(nn, 1), bd, rw,
              hs, he, ps, sk, un, lf, ab, rest, PP, hc2,
              Equal.trans(Nat, U32.to_nat(U32.add(nn, 1)), 1n+U32.to_nat(nn),
                plus(String.append(pre, SCon{Chr{uu}, SNil{}}), 0n),
                Eq.inc.nat(nn, Eq.not.true(U32.is_zero(U32.add(nn, 1)),
                  Eq.and.left(Bool.not(U32.is_zero(U32.add(nn, 1))), Laws.counts(tt, U32.add(nn, 1)), hk))),
                Equal.trans(Nat, 1n+U32.to_nat(nn), 1n+plus(pre, 0n),
                  plus(String.append(pre, SCon{Chr{uu}, SNil{}}), 0n),
                  Equal.cong(Nat, Nat, kk => 1n+kk, U32.to_nat(nn), plus(pre, 0n), hn),
                  Equal.sym(Nat, plus(String.append(pre, SCon{Chr{uu}, SNil{}}), 0n), 1n+plus(pre, 0n),
                    plus.app(pre, SCon{Chr{uu}, SNil{}}, 0n)))),
              Eq.and.right(Bool.not(U32.is_zero(U32.add(nn, 1))), Laws.counts(tt, U32.add(nn, 1)), hk),
              ih2))

# The first character decides the path: one written as itself opens the
# span, and one that needs an escape starts the copied string at once.

# a backslash right after the opening quote starts an escape, as it does in
# a string being copied with nothing in its buffer
def so.copy(
  +xx: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool
) -> {T.doc.read(SCon{'\\', xx}, sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab))
  == T.doc.read(SCon{'\\', xx}, T.MScan{ls(bd, rw, hs, he, ps, sk, ab, un, lf, [])}) : T.Doc}:
  {==}

# and so does a first character that needs an escape
def so.copy.esc(
  +uu: U32,
  ee: esc.Lead(uu),
  +tt: String,
  +rest: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool
) -> {T.doc.read(String.append(String.append(Laws.esc(Chr{uu}), Laws.escs(tt)), SCon{'"', rest}),
  sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab))
  == T.doc.read(String.append(String.append(Laws.esc(Chr{uu}), Laws.escs(tt)), SCon{'"', rest}),
    T.MScan{ls(bd, rw, hs, he, ps, sk, ab, un, lf, [])}) : T.Doc}:
  %Equal.sym(String, Laws.esc(Chr{uu}), SCon{'\\', str.tl(Laws.esc(Chr{uu}))}, ee) :
    {T.doc.read(String.append(String.append(_, Laws.escs(tt)), SCon{'"', rest}),
      sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab))
      == T.doc.read(String.append(String.append(_, Laws.escs(tt)), SCon{'"', rest}),
        T.MScan{ls(bd, rw, hs, he, ps, sk, ab, un, lf, [])}) : T.Doc}
  so.copy(String.append(String.append(str.tl(Laws.esc(Chr{uu})), Laws.escs(tt)), SCon{'"', rest}), bd, rw,
    hs, he, ps, bk, sk, un, lf, ab)

# a first character that needs an escape: the string is read in LStr from an
# empty buffer
def so.esc(
  +uu: U32,
  ee: esc.Lead(uu),
  +tt: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  ih: sv.Then(SCon{Chr{uu}, tt}, bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(String.append(Laws.escs(SCon{Chr{uu}, tt}), SCon{'"', rest}),
  sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab))):
  pp.step(PP,
    T.doc.read(String.append(Laws.escs(SCon{Chr{uu}, tt}), SCon{'"', rest}),
      sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab)),
    T.doc.read(String.append(Laws.escs(SCon{Chr{uu}, tt}), SCon{'"', rest}),
      T.MScan{ls(bd, rw, hs, he, ps, sk, ab, un, lf, [])}),
    so.copy.esc(uu, ee, tt, rest, bd, rw, hs, he, ps, bk, sk, un, lf, ab),
    ls.fin(SCon{Chr{uu}, tt}, SNil{}, bd, rw, hs, he, ps, sk, ab, un, lf, rest, PP, ih))

# a first character written as itself opens the span, and the rest of the
# string is read from there
def so.plain(
  +uu: U32,
  +e34: {U32.is_eq(uu, 34) == False{} : Bool},
  +e92: {U32.is_eq(uu, 92) == False{} : Bool},
  +ec: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool},
  +tt: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  +hk: {Laws.counts(tt, 1) == True{} : Bool},
  ih: sv.Then(SCon{Chr{uu}, tt}, bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(String.append(Laws.escs(SCon{Chr{uu}, tt}), SCon{'"', rest}),
  sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab))):
  %Equal.sym(String, Laws.esc(Chr{uu}), SCon{Chr{uu}, SNil{}}, esc.pl2(uu, e34, e92, ec)) :
    PP(T.doc.read(String.append(String.append(_, Laws.escs(tt)), SCon{'"', rest}),
      sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab)))
  pp.step(PP,
    T.doc.read(SCon{Chr{uu}, String.append(Laws.escs(tt), SCon{'"', rest})},
      sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab)),
    T.doc.read(String.append(Laws.escs(tt), SCon{'"', rest}),
      sv.eat(SCon{Chr{uu}, String.append(Laws.escs(tt), SCon{'"', rest})}, 1, bd, rw, hs, he, ps, sk, un, lf,
        ab)),
    so.one(uu, String.append(Laws.escs(tt), SCon{'"', rest}), bd, rw, hs, he, ps, bk, sk, un, lf, ab, e34,
      e92, ec),
    se.go(tt, SCon{Chr{uu}, SNil{}}, SCon{Chr{uu}, String.append(Laws.escs(tt), SCon{'"', rest})}, 1, bd, rw,
      hs, he, ps, sk, un, lf, ab, rest, PP, {==}, {==}, hk, ih))

# the first character: a quote, a backslash or a control starts the copied
# string, and any other opens the span
def so.first(
  +uu: U32,
  q34: Bool,
  b92: Bool,
  ctl: Bool,
  +e34: {U32.is_eq(uu, 34) == q34 : Bool},
  +e92: {U32.is_eq(uu, 92) == b92 : Bool},
  +ec: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == ctl : Bool},
  +tt: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  +hk: {Laws.counts(tt, 1) == True{} : Bool},
  ih: sv.Then(SCon{Chr{uu}, tt}, bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(String.append(Laws.escs(SCon{Chr{uu}, tt}), SCon{'"', rest}),
  sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab))):
  match q34:
    case True{}:
      so.esc(uu, esc.lead.is(uu, 34, e34, {==}), tt, bd, rw, hs, he, ps, bk, sk, un, lf, ab, rest, PP, ih)
    case False{}:
      match b92:
        case True{}:
          so.esc(uu, esc.lead.is(uu, 92, e92, {==}), tt, bd, rw, hs, he, ps, bk, sk, un, lf, ab, rest, PP,
            ih)
        case False{}:
          match ctl:
            case True{}:
              so.esc(uu, esc.lead.ctl(uu, ec), tt, bd, rw, hs, he, ps, bk, sk, un, lf, ab, rest, PP, ih)
            case False{}:
              so.plain(uu, e34, e92, ec, tt, bd, rw, hs, he, ps, bk, sk, un, lf, ab, rest, PP, hk, ih)

# a nonempty string, as render writes it after the opening quote, then the
# closing quote and any rest: from every value position the rest is read with
# a value holding the string placed (sv.Is), back at LStr and uni and left as
# the last escape left them
def sv.more(
  +uu: U32,
  +tt: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  es: {Laws.short(SCon{Chr{uu}, tt}) == True{} : Bool},
  ih: sv.Then(SCon{Chr{uu}, tt}, bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(String.append(Laws.escs(SCon{Chr{uu}, tt}), SCon{'"', rest}),
  sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab))):
  so.first(uu, U32.is_eq(uu, 34), U32.is_eq(uu, 92), Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), {==},
    {==}, {==}, tt, bd, rw, hs, he, ps, bk, sk, un, lf, ab, rest, PP,
    Eq.and.right(Bool.not(U32.is_zero(U32.add(0, 1))), Laws.counts(tt, U32.add(0, 1)), es), ih)

# The empty string. `""` goes through LQ2, which waits for the character
# after the second quote to tell it from `"""`: that character is held and
# read again by the full step from the state with "" placed, where every
# other string's next character takes the fast step. The two agree in every
# state a value leaves (LLine, LArrC, LInlC), on every character, so ""
# followed by any rest that does not start with a quote reads as the others
# do.

# a scanner with no character held, past the first character of the text
def fs.st(
  bd: String,
  rw: List<&2, T.Val>,
  hs: List<&2, String>,
  he: List<&2, String>,
  ps: List<&2, String>,
  buf: List<&2, Char>,
  lx: T.Lex,
  bk: T.Lex,
  qk: T.QKind,
  sk: List<&2, T.Ctx>,
  un: U32,
  lf: U32,
  ab: Bool
) -> T.St:
  T.St{bd, rw, hs, he, ps, buf, lx, bk, qk, sk, T.HNone{}, un, lf, ab, False{}}

# A placed value holds no character, so read.once2 leaves it as it is.

# at the root
def tk.once.root(
  end: T.End,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +ld: Bool
) -> {T.take.root(end, he, bk, qk, un, lf, ab, ld) == T.read.once2(T.take.root(end, he, bk, qk, un, lf, ab, ld))
  : T.St}:
  match end:
    case T.End{_vs, _bad, _heads}:
      {==}

# in an inline table
def tk.once.inl(
  end: T.End,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +rest: List<&2, T.Ctx>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +ld: Bool
) -> {T.take.inl(end, rw, hs, he, ps, rest, bk, qk, un, lf, ab, ld)
  == T.read.once2(T.take.inl(end, rw, hs, he, ps, rest, bk, qk, un, lf, ab, ld)) : T.St}:
  match end:
    case T.End{_vs, _bad, _heads}:
      {==}

# wherever the value goes
def tk.once(
  sk: List<&2, T.Ctx>,
  +vv: T.Val,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +ld: Bool
) -> {T.take.top(sk, vv, bd, rw, hs, he, ps, bk, qk, un, lf, ab, ld)
  == T.read.once2(T.take.top(sk, vv, bd, rw, hs, he, ps, bk, qk, un, lf, ab, ld)) : T.St}:
  match sk:
    case []:
      tk.once.root(T.tree.walk(T.path.cat(he, ps), T.Tw{rw, T.JPut{vv}, [], bd, "", hs, False{}},
        T.path.len(he, 0)), he, bk, qk, un, lf, ab, ld)
    case T.CArr{_items, _saved, _at} <> _rest:
      {==}
    case T.CInl{inl, +saved, +at} <> +rest:
      tk.once.inl(T.tree.walk(List.reverse(&2, String, ps), T.Tw{inl, T.JPut{vv}, [], bd, "", [],
        True{}}, 0), rw, hs, at, saved, rest, bk, qk, un, lf, ab, ld)

# and read.fin.close leaves it as it is too, at the end of the text
def tk.fin.root(
  end: T.End,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +ld: Bool
) -> {T.take.root(end, he, bk, qk, un, lf, ab, ld)
  == T.read.fin.close(T.read.once2(T.take.root(end, he, bk, qk, un, lf, ab, ld))) : T.St}:
  match end:
    case T.End{_vs, _bad, _heads}:
      {==}

# in an inline table
def tk.fin.inl(
  end: T.End,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +rest: List<&2, T.Ctx>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +ld: Bool
) -> {T.take.inl(end, rw, hs, he, ps, rest, bk, qk, un, lf, ab, ld)
  == T.read.fin.close(T.read.once2(T.take.inl(end, rw, hs, he, ps, rest, bk, qk, un, lf, ab, ld))) : T.St}:
  match end:
    case T.End{_vs, _bad, _heads}:
      {==}

# wherever the value goes
def tk.fin(
  sk: List<&2, T.Ctx>,
  +vv: T.Val,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +ld: Bool
) -> {T.take.top(sk, vv, bd, rw, hs, he, ps, bk, qk, un, lf, ab, ld)
  == T.read.fin.close(T.read.once2(T.take.top(sk, vv, bd, rw, hs, he, ps, bk, qk, un, lf, ab, ld))) : T.St}:
  match sk:
    case []:
      tk.fin.root(T.tree.walk(T.path.cat(he, ps), T.Tw{rw, T.JPut{vv}, [], bd, "", hs, False{}},
        T.path.len(he, 0)), he, bk, qk, un, lf, ab, ld)
    case T.CArr{_items, _saved, _at} <> _rest:
      {==}
    case T.CInl{inl, +saved, +at} <> +rest:
      tk.fin.inl(T.tree.walk(List.reverse(&2, String, ps), T.Tw{inl, T.JPut{vv}, [], bd, "", [],
        True{}}, 0), rw, hs, at, saved, rest, bk, qk, un, lf, ab, ld)

# closing an array places it, so it holds no character either
def arr.once(
  sk: List<&2, T.Ctx>,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +ld: Bool
) -> {T.arr.top(sk, bd, rw, hs, bk, qk, un, lf, ab, ld)
  == T.read.once2(T.arr.top(sk, bd, rw, hs, bk, qk, un, lf, ab, ld)) : T.St}:
  match sk:
    case []:
      {==}
    case T.CArr{items, +parts, +here} <> rest:
      tk.once(rest, T.VArr{List.reverse(&2, T.Val, items)}, bd, rw, hs, here, parts, bk, qk, un, lf, ab, ld)
    case T.CInl{_rows, _parts, _here} <> _rest:
      {==}

# and so does closing an inline table
def inl.once(
  sk: List<&2, T.Ctx>,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +ld: Bool
) -> {T.inl.top(sk, bd, rw, hs, bk, qk, un, lf, ab, ld)
  == T.read.once2(T.inl.top(sk, bd, rw, hs, bk, qk, un, lf, ab, ld)) : T.St}:
  match sk:
    case []:
      {==}
    case T.CArr{_items, _parts, _here} <> _rest:
      {==}
    case T.CInl{inl, +parts, +here} <> rest:
      tk.once(rest, T.VInl{T.inl.seal(inl)}, bd, rw, hs, here, parts, bk, qk, un, lf, ab, ld)

# every step after a root pair's value holds no character
def once.line(
  sp: Bool,
  hash: Bool,
  nl: Bool,
  +cc: Char,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +buf: List<&2, Char>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool
) -> {T.lex.line.go(sp, hash, nl, fs.st(bd, rw, hs, he, ps, buf, T.LLine{}, bk, qk, sk, un, lf, ab), cc)
  == T.read.once2(T.lex.line.go(sp, hash, nl, fs.st(bd, rw, hs, he, ps, buf, T.LLine{}, bk, qk, sk, un, lf,
    ab), cc)) : T.St}:
  match sp:
    case True{}:
      {==}
    case False{}:
      match hash:
        case True{}:
          {==}
        case False{}:
          match nl:
            case True{}:
              {==}
            case False{}:
              {==}

# every step after an array item
def once.arrc(
  sp: Bool,
  nl: Bool,
  hash: Bool,
  comma: Bool,
  end: Bool,
  +cc: Char,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +buf: List<&2, Char>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool
) -> {T.lex.arrc.go(sp, nl, hash, comma, end, fs.st(bd, rw, hs, he, ps, buf, T.LArrC{}, bk, qk, sk, un, lf,
  ab), cc) == T.read.once2(T.lex.arrc.go(sp, nl, hash, comma, end, fs.st(bd, rw, hs, he, ps, buf, T.LArrC{},
  bk, qk, sk, un, lf, ab), cc)) : T.St}:
  match sp:
    case True{}:
      {==}
    case False{}:
      match nl:
        case True{}:
          {==}
        case False{}:
          match hash:
            case True{}:
              {==}
            case False{}:
              match comma:
                case True{}:
                  {==}
                case False{}:
                  match end:
                    case True{}:
                      arr.once(sk, bd, rw, hs, bk, qk, un, lf, ab, False{})
                    case False{}:
                      {==}

# every step after an inline table's value
def once.inlc(
  sp: Bool,
  hash: Bool,
  comma: Bool,
  end: Bool,
  nl: Bool,
  +cc: Char,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +buf: List<&2, Char>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool
) -> {T.lex.inlc.go(sp, hash, comma, end, nl, fs.st(bd, rw, hs, he, ps, buf, T.LInlC{}, bk, qk, sk, un, lf,
  ab), cc) == T.read.once2(T.lex.inlc.go(sp, hash, comma, end, nl, fs.st(bd, rw, hs, he, ps, buf, T.LInlC{},
  bk, qk, sk, un, lf, ab), cc)) : T.St}:
  match sp:
    case True{}:
      {==}
    case False{}:
      match hash:
        case True{}:
          {==}
        case False{}:
          match comma:
            case True{}:
              {==}
            case False{}:
              match end:
                case True{}:
                  inl.once(sk, bd, rw, hs, bk, qk, un, lf, ab, False{})
                case False{}:
                  match nl:
                    case True{}:
                      {==}
                    case False{}:
                      {==}

# after a root pair's value the full step is the fast step
def fs.line(
  sp: Bool,
  nl: Bool,
  +cc: Char,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +buf: List<&2, Char>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  es: {T.ch.sp(cc) == sp : Bool}
) -> {T.lex.line(fs.st(bd, rw, hs, he, ps, buf, T.LLine{}, bk, qk, sk, un, lf, ab), cc)
  == T.read.fast.ws(sp, nl, False{}, bd, rw, hs, he, ps, buf, T.LLine{}, bk, qk, sk, un, lf, ab, cc) : T.St}:
  match sp:
    case True{}:
      %Equal.sym(Bool, T.ch.sp(cc), True{}, es) :
        {T.lex.line.go(_, Char.is_eq(cc, '#'), T.ch.nl(cc), fs.st(bd, rw, hs, he, ps, buf, T.LLine{}, bk, qk,
          sk, un, lf, ab), cc) == T.read.fast.ws(True{}, nl, False{}, bd, rw, hs, he, ps, buf, T.LLine{}, bk,
          qk, sk, un, lf, ab, cc) : T.St}
      {==}
    case False{}:
      match nl:
        case True{}:
          once.line(T.ch.sp(cc), Char.is_eq(cc, '#'), T.ch.nl(cc), cc, bd, rw, hs, he, ps, buf, bk, qk, sk, un,
            lf, ab)
        case False{}:
          once.line(T.ch.sp(cc), Char.is_eq(cc, '#'), T.ch.nl(cc), cc, bd, rw, hs, he, ps, buf, bk, qk, sk, un,
            lf, ab)

# after an array item
def fs.arrc(
  sp: Bool,
  nl: Bool,
  +cc: Char,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +buf: List<&2, Char>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  es: {T.ch.sp(cc) == sp : Bool},
  en: {T.ch.nl(cc) == nl : Bool}
) -> {T.lex.arrc(fs.st(bd, rw, hs, he, ps, buf, T.LArrC{}, bk, qk, sk, un, lf, ab), cc)
  == T.read.fast.ws(sp, nl, True{}, bd, rw, hs, he, ps, buf, T.LArrC{}, bk, qk, sk, un, lf, ab, cc) : T.St}:
  match sp:
    case True{}:
      %Equal.sym(Bool, T.ch.sp(cc), True{}, es) :
        {T.lex.arrc.go(_, T.ch.nl(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, ','), Char.is_eq(cc, ']'),
          fs.st(bd, rw, hs, he, ps, buf, T.LArrC{}, bk, qk, sk, un, lf, ab), cc) == T.read.fast.ws(True{}, nl,
          True{}, bd, rw, hs, he, ps, buf, T.LArrC{}, bk, qk, sk, un, lf, ab, cc) : T.St}
      {==}
    case False{}:
      match nl:
        case True{}:
          %Equal.sym(Bool, T.ch.sp(cc), False{}, es) :
            {T.lex.arrc.go(_, T.ch.nl(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, ','), Char.is_eq(cc, ']'),
              fs.st(bd, rw, hs, he, ps, buf, T.LArrC{}, bk, qk, sk, un, lf, ab), cc) == T.read.fast.ws(False{},
              True{}, True{}, bd, rw, hs, he, ps, buf, T.LArrC{}, bk, qk, sk, un, lf, ab, cc) : T.St}
          %Equal.sym(Bool, T.ch.nl(cc), True{}, en) :
            {T.lex.arrc.go(False{}, _, Char.is_eq(cc, '#'), Char.is_eq(cc, ','), Char.is_eq(cc, ']'),
              fs.st(bd, rw, hs, he, ps, buf, T.LArrC{}, bk, qk, sk, un, lf, ab), cc) == T.read.fast.ws(False{},
              True{}, True{}, bd, rw, hs, he, ps, buf, T.LArrC{}, bk, qk, sk, un, lf, ab, cc) : T.St}
          {==}
        case False{}:
          once.arrc(T.ch.sp(cc), T.ch.nl(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, ','), Char.is_eq(cc, ']'), cc,
            bd, rw, hs, he, ps, buf, bk, qk, sk, un, lf, ab)

# after an inline table's value
def fs.inlc(
  sp: Bool,
  nl: Bool,
  +cc: Char,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +buf: List<&2, Char>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  es: {T.ch.sp(cc) == sp : Bool}
) -> {T.lex.inlc(fs.st(bd, rw, hs, he, ps, buf, T.LInlC{}, bk, qk, sk, un, lf, ab), cc)
  == T.read.fast.ws(sp, nl, False{}, bd, rw, hs, he, ps, buf, T.LInlC{}, bk, qk, sk, un, lf, ab, cc) : T.St}:
  match sp:
    case True{}:
      %Equal.sym(Bool, T.ch.sp(cc), True{}, es) :
        {T.lex.inlc.go(_, Char.is_eq(cc, '#'), Char.is_eq(cc, ','), Char.is_eq(cc, '}'), T.ch.nl(cc),
          fs.st(bd, rw, hs, he, ps, buf, T.LInlC{}, bk, qk, sk, un, lf, ab), cc) == T.read.fast.ws(True{}, nl,
          False{}, bd, rw, hs, he, ps, buf, T.LInlC{}, bk, qk, sk, un, lf, ab, cc) : T.St}
      {==}
    case False{}:
      match nl:
        case True{}:
          once.inlc(T.ch.sp(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, ','), Char.is_eq(cc, '}'), T.ch.nl(cc), cc,
            bd, rw, hs, he, ps, buf, bk, qk, sk, un, lf, ab)
        case False{}:
          once.inlc(T.ch.sp(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, ','), Char.is_eq(cc, '}'), T.ch.nl(cc), cc,
            bd, rw, hs, he, ps, buf, bk, qk, sk, un, lf, ab)

# a character held after a root pair's value is read as the fast step reads it
def fs.held.root(
  end: T.End,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +cc: Char
) -> {T.read.once2(T.bare.hold.on(T.take.root(end, he, bk, qk, un, lf, ab, False{}), cc))
  == T.read.fast(T.take.root(end, he, bk, qk, un, lf, ab, False{}), cc) : T.St}:
  match end:
    case T.End{+vs, +bad, +heads}:
      fs.line(T.ch.sp(cc), T.ch.nl(cc), cc, bad, vs, heads, he, [], [], bk, qk, [], un, lf, ab, {==})

# after an inline table's value
def fs.held.inl(
  end: T.End,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +rest: List<&2, T.Ctx>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +cc: Char
) -> {T.read.once2(T.bare.hold.on(T.take.inl(end, rw, hs, he, ps, rest, bk, qk, un, lf, ab, False{}), cc))
  == T.read.fast(T.take.inl(end, rw, hs, he, ps, rest, bk, qk, un, lf, ab, False{}), cc) : T.St}:
  match end:
    case T.End{+inl, +bad, _heads}:
      fs.inlc(T.ch.sp(cc), T.ch.nl(cc), cc, bad, rw, hs, he, [], [], bk, qk, T.CInl{inl, ps, he} <> rest, un,
        lf, ab, {==})

# wherever the value went
def fs.held(
  sk: List<&2, T.Ctx>,
  +vv: T.Val,
  +cc: Char,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool
) -> {T.read.once2(T.bare.hold.on(T.take.top(sk, vv, bd, rw, hs, he, ps, bk, qk, un, lf, ab, False{}), cc))
  == T.read.fast(T.take.top(sk, vv, bd, rw, hs, he, ps, bk, qk, un, lf, ab, False{}), cc) : T.St}:
  match sk:
    case []:
      fs.held.root(T.tree.walk(T.path.cat(he, ps), T.Tw{rw, T.JPut{vv}, [], bd, "", hs, False{}},
        T.path.len(he, 0)), he, bk, qk, un, lf, ab, cc)
    case T.CArr{items, +saved, +at} <> +rest:
      fs.arrc(T.ch.sp(cc), T.ch.nl(cc), cc, bd, rw, hs, at, saved, [], bk, qk,
        T.CArr{vv <> items, saved, at} <> rest, un, lf, ab, {==}, {==})
    case T.CInl{inl, +saved, +at} <> +rest:
      fs.held.inl(T.tree.walk(List.reverse(&2, String, ps), T.Tw{inl, T.JPut{vv}, [], bd, "", [],
        True{}}, 0), rw, hs, at, saved, rest, bk, qk, un, lf, ab, cc)

# the scanner after `""`, waiting for the next character
def sv.q2(
  bd: String,
  rw: List<&2, T.Val>,
  hs: List<&2, String>,
  he: List<&2, String>,
  ps: List<&2, String>,
  bk: T.Lex,
  sk: List<&2, T.Ctx>,
  un: U32,
  lf: U32,
  ab: Bool
) -> T.St:
  T.St{bd, rw, hs, he, ps, [], T.LQ2{}, bk, T.QBasic{}, sk, T.HNone{}, un, lf, ab, False{}}

# a character after `""` that is no quote places the empty string and is
# read as the fast step would read it with the string placed
def fs.q2(
  same: Bool,
  +cc: Char,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  hq: {same == False{} : Bool}
) -> {T.read.once2(T.lex.q2.go(same, sv.q2(bd, rw, hs, he, ps, bk, sk, un, lf, ab), cc, T.QBasic{}))
  == T.read.fast(sv.took(sk, T.VStr{""}, bd, rw, hs, he, ps, bk, un, lf, ab), cc) : T.St}:
  match same:
    case False{}:
      fs.held(sk, T.VStr{""}, cc, bd, rw, hs, he, ps, bk, T.QBasic{}, un, lf, ab)
    case True{}:
      Eq.bit.absurd2(&2, {T.read.once2(T.lex.q2.go(True{}, sv.q2(bd, rw, hs, he, ps, bk, sk, un, lf, ab), cc,
        T.QBasic{})) == T.read.fast(sv.took(sk, T.VStr{""}, bd, rw, hs, he, ps, bk, un, lf, ab), cc) : T.St}, hq)

# two states whose fast steps agree on a character are read alike from it
def scan.fast(
  dq: Bool,
  sq: Bool,
  cr: Bool,
  +s1: T.St,
  +s2: T.St,
  +cc: Char,
  ee: {T.read.fast(s1, cc) == T.read.fast(s2, cc) : T.St}
) -> {T.doc.scan.q(dq, sq, cr, s1, cc) == T.doc.scan.q(dq, sq, cr, s2, cc) : T.Mode}:
  match dq:
    case True{}:
      Equal.cong(T.St, T.Mode, st => T.doc.wrap(st), T.read.fast(s1, cc), T.read.fast(s2, cc), ee)
    case False{}:
      match sq:
        case True{}:
          Equal.cong(T.St, T.Mode, st => T.doc.wrap(st), T.read.fast(s1, cc), T.read.fast(s2, cc), ee)
        case False{}:
          match cr:
            case True{}:
              Equal.cong(T.St, T.Mode, st => T.MCr{st}, T.read.fast(s1, cc), T.read.fast(s2, cc), ee)
            case False{}:
              Equal.cong(T.St, T.Mode, st => T.MScan{st}, T.read.fast(s1, cc), T.read.fast(s2, cc), ee)

# a text that does not start with a quote: what may follow `""`
def sv.free(rest: String) -> Bool:
  match rest:
    case SNil{}:
      True{}
    case SCon{hh, _tt}:
      Bool.not(Char.is_eq(hh, '"'))

# `""` then any rest that does not start with a quote: the rest is read with
# the empty string placed, back where the value position left it
def sv.empty(
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  rest: String,
  -PP: T.Doc -> Type,
  hr: {sv.free(rest) == True{} : Bool},
  ih: sv.Then(SNil{}, bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(SCon{'"', rest}, sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab))):
  match rest:
    case SNil{}:
      pp.step(PP, T.doc.read(SCon{'"', SNil{}}, sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab)),
        T.doc.read(SNil{}, T.MScan{sv.took(sk, T.VStr{""}, bd, rw, hs, he, ps, bk, un, lf, ab)}),
        Equal.cong(T.St, T.Doc, st => T.read.fin2(st), sv.took(sk, T.VStr{""}, bd, rw, hs, he, ps, bk, un, lf, ab),
          T.read.fin.close(T.read.once2(sv.took(sk, T.VStr{""}, bd, rw, hs, he, ps, bk, un, lf, ab))),
          tk.fin(sk, T.VStr{""}, bd, rw, hs, he, ps, bk, T.QBasic{}, un, lf, ab, False{})),
        ih(T.VStr{""}, bk, un, lf, {==}))
    case SCon{hh, +tt}:
      match hh:
        case Chr{+uu}:
          pp.step(PP, T.doc.read(SCon{'"', SCon{Chr{uu}, tt}}, sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab)),
            T.doc.read(SCon{Chr{uu}, tt}, T.MScan{sv.took(sk, T.VStr{""}, bd, rw, hs, he, ps, bk, un, lf, ab)}),
            Equal.cong(T.Mode, T.Doc, md => T.doc.read(tt, md),
              T.doc.scan(sv.q2(bd, rw, hs, he, ps, bk, sk, un, lf, ab), Chr{uu}),
              T.doc.scan(sv.took(sk, T.VStr{""}, bd, rw, hs, he, ps, bk, un, lf, ab), Chr{uu}),
              scan.fast(U32.is_eq(uu, 34), U32.is_eq(uu, 39), U32.is_eq(uu, 13),
                sv.q2(bd, rw, hs, he, ps, bk, sk, un, lf, ab),
                sv.took(sk, T.VStr{""}, bd, rw, hs, he, ps, bk, un, lf, ab), Chr{uu},
                fs.q2(U32.is_eq(uu, 34), Chr{uu}, bd, rw, hs, he, ps, bk, sk, un, lf, ab,
                  Eq.not.true(U32.is_eq(uu, 34), hr)))),
            ih(T.VStr{""}, bk, un, lf, {==}))

# The whole string, from each value position.

# every string as render writes it after the opening quote, then the closing
# quote and any rest that does not start with a quote: the rest is read with
# a string value holding it placed, and whatever back, uni and left
def sv.read(
  ss: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  es: {Laws.short(ss) == True{} : Bool},
  hr: {sv.free(rest) == True{} : Bool},
  ih: sv.Then(ss, bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> PP(T.doc.read(String.append(Laws.escs(ss), SCon{'"', rest}), sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab))):
  match ss:
    case SNil{}:
      sv.empty(bd, rw, hs, he, ps, bk, sk, un, lf, ab, rest, PP, hr, ih)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+uu}:
          sv.more(uu, tt, bd, rw, hs, he, ps, bk, sk, un, lf, ab, rest, PP, es, ih)

# key.basic(s) then rest, read from a scanner in state q: the premise form
# WP-C and WP-D call
def sv.Read(
  +ss: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +buf: List<&2, Char>,
  +lx: T.Lex,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  PP: T.Doc -> Type
) -> Type:
  PP(T.doc.read(String.append(T.key.basic(ss), rest), T.MScan{fs.st(bd, rw, hs, he, ps, buf, lx, bk, qk, sk, un,
    lf, ab)}))

# the quotes around escs, and the text after them
def sv.text(
  +ss: String,
  +rest: String,
  -PP: T.Doc -> Type,
  +md: T.Mode,
  kk: PP(T.doc.read(String.append(Laws.escs(ss), SCon{'"', rest}), md))
) -> PP(T.doc.read(String.append(Laws.escs(ss), String.append("\"", rest)), md)):
  kk

# a value position: after `=` in a root pair or an inline table's pair, the
# scanner waits for the value in LVal; the opening quote opens the string
# with back where the pair left it
def sv.val(
  +ss: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +buf: List<&2, Char>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  es: {Laws.short(ss) == True{} : Bool},
  hr: {sv.free(rest) == True{} : Bool},
  ih: sv.Then(ss, bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> sv.Read(ss, bd, rw, hs, he, ps, buf, T.LVal{}, bk, qk, sk, un, lf, ab, rest, PP):
  %Equal.sym(String, T.key.basic(ss), "\"" ++ Laws.escs(ss) ++ "\"", Laws.basic_escs(ss)) :
    PP(T.doc.read(String.append(_, rest), T.MScan{fs.st(bd, rw, hs, he, ps, buf, T.LVal{}, bk, qk, sk, un, lf,
      ab)}))
  %Equal.sym(String, String.append(String.append(Laws.escs(ss), "\""), rest),
    String.append(Laws.escs(ss), String.append("\"", rest)), Eq.append_assoc(Laws.escs(ss), "\"", rest)) :
    PP(T.doc.read(_, sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab)))
  sv.text(ss, rest, PP, sv.open(bd, rw, hs, he, ps, bk, sk, un, lf, ab),
    sv.read(ss, bd, rw, hs, he, ps, bk, sk, un, lf, ab, rest, PP, es, hr, ih))

# an array item: in LArr the quote is held, read in LVal, and opens the
# string with back at LVal
def sv.arr(
  +ss: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +buf: List<&2, Char>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  es: {Laws.short(ss) == True{} : Bool},
  hr: {sv.free(rest) == True{} : Bool},
  ih: sv.Then(ss, bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> sv.Read(ss, bd, rw, hs, he, ps, buf, T.LArr{}, bk, qk, sk, un, lf, ab, rest, PP):
  %Equal.sym(String, T.key.basic(ss), "\"" ++ Laws.escs(ss) ++ "\"", Laws.basic_escs(ss)) :
    PP(T.doc.read(String.append(_, rest), T.MScan{fs.st(bd, rw, hs, he, ps, buf, T.LArr{}, bk, qk, sk, un, lf,
      ab)}))
  %Equal.sym(String, String.append(String.append(Laws.escs(ss), "\""), rest),
    String.append(Laws.escs(ss), String.append("\"", rest)), Eq.append_assoc(Laws.escs(ss), "\"", rest)) :
    PP(T.doc.read(_, sv.open(bd, rw, hs, he, ps, T.LVal{}, sk, un, lf, ab)))
  sv.text(ss, rest, PP, sv.open(bd, rw, hs, he, ps, T.LVal{}, sk, un, lf, ab),
    sv.read(ss, bd, rw, hs, he, ps, T.LVal{}, sk, un, lf, ab, rest, PP, es, hr, ih))

# A string value holding ss reads as the owned string ss, in a table's pair
# or as an item: what WP-D needs to take own off the parsed side.

# as a pair's value
def sv.own.pair(
  vv: T.Val,
  +ss: String,
  +kk: String,
  +tt: List<&2, T.Val>,
  hv: sv.Is(vv, ss)
) -> {Laws.own.rows(T.VPair{kk, vv} <> tt) == T.VPair{kk, T.VStr{ss}} <> Laws.own.rows(tt) : List<&2, T.Val>}:
  match vv:
    case T.VStr{st}:
      Equal.cong(String, List<&2, T.Val>, xs => T.VPair{kk, T.VStr{xs}} <> Laws.own.rows(tt), st, ss, hv)
    case T.VSpan{src, +nn}:
      Equal.cong(String, List<&2, T.Val>, xs => T.VPair{kk, T.VStr{xs}} <> Laws.own.rows(tt),
        T.span.str(src, nn, U32.is_zero(nn)), ss, hv)
    case T.VInt{_sign, _digits}:
      match hv:
    case T.VFlo{_sign, _text}:
      match hv:
    case T.VBool{_bit}:
      match hv:
    case T.VWhen{_when}:
      match hv:
    case T.VArr{_items}:
      match hv:
    case T.VInl{_rows}:
      match hv:
    case T.VHead{_path, _rows}:
      match hv:
    case T.VAot{_path, _rows}:
      match hv:
    case T.VAots{_path, _elems}:
      match hv:
    case T.VPair{_name, _val}:
      match hv:

# as an item
def sv.own.item(
  vv: T.Val,
  +ss: String,
  +tt: List<&2, T.Val>,
  hv: sv.Is(vv, ss)
) -> {Laws.own.rows(vv <> tt) == T.VStr{ss} <> Laws.own.rows(tt) : List<&2, T.Val>}:
  match vv:
    case T.VStr{st}:
      Equal.cong(String, List<&2, T.Val>, xs => T.VStr{xs} <> Laws.own.rows(tt), st, ss, hv)
    case T.VSpan{src, +nn}:
      Equal.cong(String, List<&2, T.Val>, xs => T.VStr{xs} <> Laws.own.rows(tt),
        T.span.str(src, nn, U32.is_zero(nn)), ss, hv)
    case T.VInt{_sign, _digits}:
      match hv:
    case T.VFlo{_sign, _text}:
      match hv:
    case T.VBool{_bit}:
      match hv:
    case T.VWhen{_when}:
      match hv:
    case T.VArr{_items}:
      match hv:
    case T.VInl{_rows}:
      match hv:
    case T.VHead{_path, _rows}:
      match hv:
    case T.VAot{_path, _rows}:
      match hv:
    case T.VAots{_path, _elems}:
      match hv:
    case T.VPair{_name, _val}:
      match hv:

# The laws. A bare key, then " = " and whatever opens the value, bring the
# scanner to the value position; the string is read there by sv.val or
# sv.arr; the text after it closes the document, which own reads as the
# document of s once the value is known to be a string.

# a space ends a nonempty bare key, and " = " leaves the scanner waiting for
# the value
def kv.eq2(
  +bb: List<&2, Char>,
  full: {List.is_empty(&2, Char, bb) == False{} : Bool},
  +vv: String
) -> {T.doc.read(SCon{' ', SCon{'=', SCon{' ', vv}}}, T.MScan{ky(bb)})
  == T.doc.read(vv, T.MScan{fs.st("", [], [], [], [T.buf.str.go(bb, "")], [], T.LVal{}, T.LTop{}, T.QBasic{}, [], 0,
    0, False{})}) : T.Doc}:
  Equal.trans(T.Doc,
    T.doc.read(SCon{'=', SCon{' ', vv}}, T.MScan{T.read.once2(T.lex.key.end.go(
      List.is_empty(&2, Char, bb), ky(bb), T.LAfter{}))}),
    T.doc.read(SCon{'=', SCon{' ', vv}}, T.MScan{T.read.once2(T.lex.key.end.go(
      False{}, ky(bb), T.LAfter{}))}),
    T.doc.read(vv, T.MScan{fs.st("", [], [], [], [T.buf.str.go(bb, "")], [], T.LVal{}, T.LTop{}, T.QBasic{}, [], 0,
      0, False{})}),
    Equal.cong(Bool, T.Doc,
      bt => T.doc.read(SCon{'=', SCon{' ', vv}}, T.MScan{T.read.once2(
        T.lex.key.end.go(bt, ky(bb), T.LAfter{}))}),
      List.is_empty(&2, Char, bb), False{}, full),
    {==})

# a bare key, then " = ": the scanner waits for the value, the key its name
def kv.key2(
  +xx: U32,
  +tt: String,
  +vv: String,
  +ee: {T.bare.all.step(T.bare.at(Chr{xx}), _u => T.bare.all(String.to_list(tt))) == True{} : Bool}
) -> {T.parse(String.append(SCon{Chr{xx}, tt}, SCon{' ', SCon{'=', SCon{' ', vv}}}))
  == T.doc.read(vv, T.MScan{fs.st("", [], [], [], [SCon{Chr{xx}, tt}], [], T.LVal{}, T.LTop{}, T.QBasic{}, [], 0,
    0, False{})}) : T.Doc}:
  Equal.trans(T.Doc,
    T.doc.read(String.append(tt, SCon{' ', SCon{'=', SCon{' ', vv}}}), T.doc.scan(T.st.start(), Chr{xx})),
    T.doc.read(String.append(tt, SCon{' ', SCon{'=', SCon{' ', vv}}}), T.MScan{ky([Chr{xx}])}),
    T.doc.read(vv, T.MScan{fs.st("", [], [], [], [SCon{Chr{xx}, tt}], [], T.LVal{}, T.LTop{}, T.QBasic{}, [], 0,
      0, False{})}),
    Equal.cong(T.Mode, T.Doc, md => T.doc.read(String.append(tt, SCon{' ', SCon{'=', SCon{' ', vv}}}), md),
      T.doc.scan(T.st.start(), Chr{xx}), T.MScan{ky([Chr{xx}])},
      key.first(xx, ball.head(T.bare.at(Chr{xx}), String.to_list(tt), ee))),
    Equal.trans(T.Doc,
      T.doc.read(String.append(tt, SCon{' ', SCon{'=', SCon{' ', vv}}}), T.MScan{ky([Chr{xx}])}),
      T.doc.read(SCon{' ', SCon{'=', SCon{' ', vv}}}, T.MScan{ky(rev.onto(tt, [Chr{xx}]))}),
      T.doc.read(vv, T.MScan{fs.st("", [], [], [], [SCon{Chr{xx}, tt}], [], T.LVal{}, T.LTop{}, T.QBasic{}, [], 0,
        0, False{})}),
      key.body(tt, SCon{' ', SCon{'=', SCon{' ', vv}}}, [Chr{xx}],
        ball.tail(T.bare.at(Chr{xx}), String.to_list(tt), ee)),
      Equal.trans(T.Doc,
        T.doc.read(SCon{' ', SCon{'=', SCon{' ', vv}}}, T.MScan{ky(rev.onto(tt, [Chr{xx}]))}),
        T.doc.read(vv, T.MScan{fs.st("", [], [], [], [T.buf.str.go(rev.onto(tt, [Chr{xx}]), "")], [], T.LVal{},
          T.LTop{}, T.QBasic{}, [], 0, 0, False{})}),
        T.doc.read(vv, T.MScan{fs.st("", [], [], [], [SCon{Chr{xx}, tt}], [], T.LVal{}, T.LTop{}, T.QBasic{}, [],
          0, 0, False{})}),
        kv.eq2(rev.onto(tt, [Chr{xx}]), rev.full(tt, Chr{xx}, []), vv),
        Equal.cong(String, T.Doc, nm => T.doc.read(vv, T.MScan{fs.st("", [], [], [], [nm], [], T.LVal{},
          T.LTop{}, T.QBasic{}, [], 0, 0, False{})}),
          T.buf.str.go(rev.onto(tt, [Chr{xx}]), ""), SCon{Chr{xx}, tt},
          Equal.trans(String, T.buf.str.go(rev.onto(tt, [Chr{xx}]), ""),
            SCon{Chr{xx}, String.append(tt, "")}, SCon{Chr{xx}, tt},
            ml.rev(tt, [Chr{xx}], ""),
            Equal.cong(String, String, ss => SCon{Chr{xx}, ss}, String.append(tt, ""), tt,
              Eq.append_nil(tt)))))))

# the owned document is the one named
def sw.Own(+want: T.Doc, dd: T.Doc) -> Type:
  {Laws.own(dd) == want : T.Doc}

# a root pair's string value, then a newline, end the document
def sw.root(
  vv: T.Val,
  +kk: String,
  +ss: String,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  hv: sv.Is(vv, ss)
) -> sw.Own(T.Doc{"", [T.VPair{kk, T.VStr{ss}}]}, T.doc.read("\n", T.MScan{sv.took([], vv, "", [], [], [], [kk],
  bk, un, lf, False{})})):
  match vv:
    case T.VStr{st}:
      Equal.cong(String, T.Doc, xs => T.Doc{"", [T.VPair{kk, T.VStr{xs}}]}, st, ss, hv)
    case T.VSpan{src, +nn}:
      Equal.cong(String, T.Doc, xs => T.Doc{"", [T.VPair{kk, T.VStr{xs}}]}, T.span.str(src, nn, U32.is_zero(nn)),
        ss, hv)
    case T.VInt{_sign, _digits}:
      match hv:
    case T.VFlo{_sign, _text}:
      match hv:
    case T.VBool{_bit}:
      match hv:
    case T.VWhen{_when}:
      match hv:
    case T.VArr{_items}:
      match hv:
    case T.VInl{_rows}:
      match hv:
    case T.VHead{_path, _rows}:
      match hv:
    case T.VAot{_path, _rows}:
      match hv:
    case T.VAots{_path, _elems}:
      match hv:
    case T.VPair{_name, _val}:
      match hv:

# the root pair
def sw.pair(
  kk: String,
  ek: {T.bare(kk) == True{} : Bool},
  +ss: String,
  es: {Laws.short(ss) == True{} : Bool}
) -> sw.Own(T.Doc{"", [T.VPair{kk, T.VStr{ss}}]}, T.parse(String.append(kk, String.append(" = ",
  String.append(T.key.basic(ss), "\n"))))):
  match kk:
    case SNil{}:
      Eq.bit.absurd(&1, sw.Own(T.Doc{"", [T.VPair{SNil{}, T.VStr{ss}}]}, T.parse(String.append(SNil{},
        String.append(" = ", String.append(T.key.basic(ss), "\n"))))), ek)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          pp.step(dd => sw.Own(T.Doc{"", [T.VPair{SCon{Chr{xx}, tt}, T.VStr{ss}}]}, dd),
            T.parse(String.append(SCon{Chr{xx}, tt}, String.append(" = ", String.append(T.key.basic(ss), "\n")))),
            T.doc.read(String.append(T.key.basic(ss), "\n"), T.MScan{fs.st("", [], [], [], [SCon{Chr{xx}, tt}], [],
              T.LVal{}, T.LTop{}, T.QBasic{}, [], 0, 0, False{})}),
            kv.key2(xx, tt, String.append(T.key.basic(ss), "\n"), ek),
            sv.val(ss, "", [], [], [], [SCon{Chr{xx}, tt}], [], T.LTop{}, T.QBasic{}, [], 0, 0, False{}, "\n",
              dd => sw.Own(T.Doc{"", [T.VPair{SCon{Chr{xx}, tt}, T.VStr{ss}}]}, dd), es, {==},
              vv => bk => un => lf => hv => sw.root(vv, SCon{Chr{xx}, tt}, ss, bk, un, lf, hv)))

def Laws.basic_string_reads_back(k, ek, s, es):
  sw.pair(k, ek, s, es)

# an array item's string value, then `]` and a newline, end the document
def sw.item(
  vv: T.Val,
  +kk: String,
  +ss: String,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  hv: sv.Is(vv, ss)
) -> sw.Own(T.Doc{"", [T.VPair{kk, T.VArr{[T.VStr{ss}]}}]}, T.doc.read("]\n",
  T.MScan{sv.took([T.CArr{[], [kk], []}], vv, "", [], [], [], [], bk, un, lf, False{})})):
  match vv:
    case T.VStr{st}:
      Equal.cong(String, T.Doc, xs => T.Doc{"", [T.VPair{kk, T.VArr{[T.VStr{xs}]}}]}, st, ss, hv)
    case T.VSpan{src, +nn}:
      Equal.cong(String, T.Doc, xs => T.Doc{"", [T.VPair{kk, T.VArr{[T.VStr{xs}]}}]},
        T.span.str(src, nn, U32.is_zero(nn)), ss, hv)
    case T.VInt{_sign, _digits}:
      match hv:
    case T.VFlo{_sign, _text}:
      match hv:
    case T.VBool{_bit}:
      match hv:
    case T.VWhen{_when}:
      match hv:
    case T.VArr{_items}:
      match hv:
    case T.VInl{_rows}:
      match hv:
    case T.VHead{_path, _rows}:
      match hv:
    case T.VAot{_path, _rows}:
      match hv:
    case T.VAots{_path, _elems}:
      match hv:
    case T.VPair{_name, _val}:
      match hv:

# the array
def sw.arr(
  kk: String,
  ek: {T.bare(kk) == True{} : Bool},
  +ss: String,
  es: {Laws.short(ss) == True{} : Bool}
) -> sw.Own(T.Doc{"", [T.VPair{kk, T.VArr{[T.VStr{ss}]}}]}, T.parse(String.append(kk, String.append(" = [",
  String.append(T.key.basic(ss), "]\n"))))):
  match kk:
    case SNil{}:
      Eq.bit.absurd(&1, sw.Own(T.Doc{"", [T.VPair{SNil{}, T.VArr{[T.VStr{ss}]}}]}, T.parse(String.append(SNil{},
        String.append(" = [", String.append(T.key.basic(ss), "]\n"))))), ek)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          pp.step(dd => sw.Own(T.Doc{"", [T.VPair{SCon{Chr{xx}, tt}, T.VArr{[T.VStr{ss}]}}]}, dd),
            T.parse(String.append(SCon{Chr{xx}, tt}, String.append(" = [", String.append(T.key.basic(ss),
              "]\n")))),
            T.doc.read(String.append(T.key.basic(ss), "]\n"), T.MScan{fs.st("", [], [], [], [], [], T.LArr{},
              T.LTop{}, T.QBasic{}, [T.CArr{[], [SCon{Chr{xx}, tt}], []}], 0, 0, False{})}),
            kv.key2(xx, tt, SCon{'[', String.append(T.key.basic(ss), "]\n")}, ek),
            sv.arr(ss, "", [], [], [], [], [], T.LTop{}, T.QBasic{}, [T.CArr{[], [SCon{Chr{xx}, tt}], []}], 0, 0,
              False{}, "]\n", dd => sw.Own(T.Doc{"", [T.VPair{SCon{Chr{xx}, tt}, T.VArr{[T.VStr{ss}]}}]}, dd), es,
              {==}, vv => bk => un => lf => hv => sw.item(vv, SCon{Chr{xx}, tt}, ss, bk, un, lf, hv)))

def Laws.basic_string_reads_back_in_array(k, ek, s, es):
  sw.arr(k, ek, s, es)

# an inline table's string value, then `}` and a newline, end the document
def sw.inl.val(
  vv: T.Val,
  +kk: String,
  +ss: String,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  hv: sv.Is(vv, ss)
) -> sw.Own(T.Doc{"", [T.VPair{kk, T.VInl{[T.VPair{"v", T.VStr{ss}}]}}]}, T.doc.read("}\n",
  T.MScan{sv.took([T.CInl{[], [kk], []}], vv, "", [], [], [], ["v"], bk, un, lf, False{})})):
  match vv:
    case T.VStr{st}:
      Equal.cong(String, T.Doc, xs => T.Doc{"", [T.VPair{kk, T.VInl{[T.VPair{"v", T.VStr{xs}}]}}]}, st, ss, hv)
    case T.VSpan{src, +nn}:
      Equal.cong(String, T.Doc, xs => T.Doc{"", [T.VPair{kk, T.VInl{[T.VPair{"v", T.VStr{xs}}]}}]},
        T.span.str(src, nn, U32.is_zero(nn)), ss, hv)
    case T.VInt{_sign, _digits}:
      match hv:
    case T.VFlo{_sign, _text}:
      match hv:
    case T.VBool{_bit}:
      match hv:
    case T.VWhen{_when}:
      match hv:
    case T.VArr{_items}:
      match hv:
    case T.VInl{_rows}:
      match hv:
    case T.VHead{_path, _rows}:
      match hv:
    case T.VAot{_path, _rows}:
      match hv:
    case T.VAots{_path, _elems}:
      match hv:
    case T.VPair{_name, _val}:
      match hv:

# the inline table
def sw.inl(
  kk: String,
  ek: {T.bare(kk) == True{} : Bool},
  +ss: String,
  es: {Laws.short(ss) == True{} : Bool}
) -> sw.Own(T.Doc{"", [T.VPair{kk, T.VInl{[T.VPair{"v", T.VStr{ss}}]}}]}, T.parse(String.append(kk,
  String.append(" = {v = ", String.append(T.key.basic(ss), "}\n"))))):
  match kk:
    case SNil{}:
      Eq.bit.absurd(&1, sw.Own(T.Doc{"", [T.VPair{SNil{}, T.VInl{[T.VPair{"v", T.VStr{ss}}]}}]},
        T.parse(String.append(SNil{}, String.append(" = {v = ", String.append(T.key.basic(ss), "}\n"))))), ek)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          pp.step(dd => sw.Own(T.Doc{"", [T.VPair{SCon{Chr{xx}, tt}, T.VInl{[T.VPair{"v", T.VStr{ss}}]}}]}, dd),
            T.parse(String.append(SCon{Chr{xx}, tt}, String.append(" = {v = ", String.append(T.key.basic(ss),
              "}\n")))),
            T.doc.read(String.append(T.key.basic(ss), "}\n"), T.MScan{fs.st("", [], [], [], ["v"], [], T.LVal{},
              T.LTop{}, T.QBasic{}, [T.CInl{[], [SCon{Chr{xx}, tt}], []}], 0, 0, False{})}),
            kv.key2(xx, tt, SCon{'{', SCon{'v', SCon{' ', SCon{'=', SCon{' ', String.append(T.key.basic(ss),
              "}\n")}}}}}, ek),
            sv.val(ss, "", [], [], [], ["v"], [], T.LTop{}, T.QBasic{}, [T.CInl{[], [SCon{Chr{xx}, tt}], []}], 0, 0,
              False{}, "}\n", dd => sw.Own(T.Doc{"", [T.VPair{SCon{Chr{xx}, tt}, T.VInl{[T.VPair{"v",
              T.VStr{ss}}]}}]}, dd), es, {==},
              vv => bk => un => lf => hv => sw.inl.val(vv, SCon{Chr{xx}, tt}, ss, bk, un, lf, hv)))

def Laws.basic_string_reads_back_in_inline_table(k, ek, s, es):
  sw.inl(k, ek, s, es)

# WP-N: a scalar reads back as itself. A bare value is read from the value
# state one character at a time on the fast path, ended by a newline, and
# classified by word.val; the classification is proved kind by kind.

# The ten digits. A digit is a code point from 48 to 57, so its bits above
# the sixth are zero and its six low bits are one of ten patterns; a claim
# made of each of the ten digit characters is made of every digit.

# a code point's comparisons with 48 and 57, bit by bit, the bits above the
# sixth comparing as cc with zero
def dg.cp(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +cc: Cmp) -> Bool:
  Bool.and(Cmp.is_ge(Word.cmp.fin(b0, False{}, Word.cmp.fin(b1, False{}, Word.cmp.fin(b2, False{},
    Word.cmp.fin(b3, False{}, Word.cmp.fin(b4, True{}, Word.cmp.fin(b5, True{}, cc))))))),
    Cmp.is_le(Word.cmp.fin(b0, True{}, Word.cmp.fin(b1, False{}, Word.cmp.fin(b2, False{},
    Word.cmp.fin(b3, True{}, Word.cmp.fin(b4, True{}, Word.cmp.fin(b5, True{}, cc))))))))

# the char of six low bits and zeros above them
def dg.ch(b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool) -> Char:
  Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, Eq.zw(26n)}}}}}}}}

# the six low bits of a digit, highest first: ten patterns are the digits,
# and the others compare below 48 or above 57
def dg.bits(
  -P: Char -> Type,
  +b5: Bool,
  +b4: Bool,
  +b3: Bool,
  +b2: Bool,
  +b1: Bool,
  +b0: Bool,
  h: {dg.cp(b0, b1, b2, b3, b4, b5, EQ{}) == True{} : Bool},
  p0: P('0'),
  p1: P('1'),
  p2: P('2'),
  p3: P('3'),
  p4: P('4'),
  p5: P('5'),
  p6: P('6'),
  p7: P('7'),
  p8: P('8'),
  p9: P('9')
) -> P(dg.ch(b0, b1, b2, b3, b4, b5)):
  match b5:
    case False{}:
      Eq.bit.absurd(&1, P(dg.ch(b0, b1, b2, b3, b4, False{})), h)
    case True{}:
      match b4:
        case False{}:
          Eq.bit.absurd(&1, P(dg.ch(b0, b1, b2, b3, False{}, True{})), h)
        case True{}:
          match b3:
            case False{}:
              match b2 b1 b0:
                case False{} False{} False{}:
                  p0
                case False{} False{} True{}:
                  p1
                case False{} True{} False{}:
                  p2
                case False{} True{} True{}:
                  p3
                case True{} False{} False{}:
                  p4
                case True{} False{} True{}:
                  p5
                case True{} True{} False{}:
                  p6
                case True{} True{} True{}:
                  p7
            case True{}:
              match b2:
                case True{}:
                  Eq.bit.absurd(&1, P(dg.ch(b0, b1, True{}, True{}, True{}, True{})), h)
                case False{}:
                  match b1:
                    case True{}:
                      Eq.bit.absurd(&1, P(dg.ch(b0, True{}, False{}, True{}, True{}, True{})), h)
                    case False{}:
                      match b0:
                        case False{}:
                          p8
                        case True{}:
                          p9

# the bits above the sixth compare as cc with zero: they are zero, or the
# code point is above 57
def dg.at(
  -P: Char -> Type,
  cc: Cmp,
  +b5: Bool,
  +b4: Bool,
  +b3: Bool,
  +b2: Bool,
  +b1: Bool,
  +b0: Bool,
  +rest: Word(26n),
  ec: {Word.cmp(26n, rest, Eq.zw(26n)) == cc : Cmp},
  h: {dg.cp(b0, b1, b2, b3, b4, b5, cc) == True{} : Bool},
  p0: P('0'),
  p1: P('1'),
  p2: P('2'),
  p3: P('3'),
  p4: P('4'),
  p5: P('5'),
  p6: P('6'),
  p7: P('7'),
  p8: P('8'),
  p9: P('9')
) -> P(Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}}}):
  match cc:
    case LT{}:
      Eq.bit.gone(&1, P(Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}}}),
        Eq.bit.clash2(Equal.trans(Bool, True{}, Cmp.is_lt(Word.cmp(26n, rest, Eq.zw(26n))), False{},
          Equal.sym(Bool, Cmp.is_lt(Word.cmp(26n, rest, Eq.zw(26n))), True{},
            Equal.cong(Cmp, Bool, xx => Cmp.is_lt(xx), Word.cmp(26n, rest, Eq.zw(26n)), LT{}, ec)),
          Eq.zw_nlt(26n, rest))))
    case GT{}:
      Eq.bit.absurd(&1, P(Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}}}), h)
    case EQ{}:
      er = Equal.sym(Word(26n), rest, Eq.zw(26n), Eq.word_eq(26n, rest, Eq.zw(26n), ec))
      %er : P(Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, _}}}}}}}})
      dg.bits(P, b5, b4, b3, b2, b1, b0, h, p0, p1, p2, p3, p4, p5, p6, p7, p8, p9)

# a claim made of each of the ten digits is made of every digit
def dg.elim(
  -P: Char -> Type,
  cc: Char,
  h: {Char.is_digit(cc) == True{} : Bool},
  p0: P('0'),
  p1: P('1'),
  p2: P('2'),
  p3: P('3'),
  p4: P('4'),
  p5: P('5'),
  p6: P('6'),
  p7: P('7'),
  p8: P('8'),
  p9: P('9')
) -> P(cc):
  match cc:
    case Chr{U32{WCon{+b0, WCon{+b1, WCon{+b2, WCon{+b3, WCon{+b4, WCon{+b5, +rest}}}}}}}}:
      dg.at(P, Word.cmp(26n, rest, Eq.zw(26n)), b5, b4, b3, b2, b1, b0, rest, {==}, h,
        p0, p1, p2, p3, p4, p5, p6, p7, p8, p9)

# The scan of a bare value. It starts in the value state, stays on the fast
# path for each character it keeps, and a newline ends it.

# a character a bare value keeps is no delimiter
def wd.delim(+cc: Char, hw: {Laws.word.char(cc) == True{} : Bool}) -> {T.ch.delim(cc) == False{} : Bool}:
  Eq.not.true(T.ch.delim(cc), Eq.and.left(Bool.not(T.ch.delim(cc)),
    Bool.not(Bool.or(Char.is_eq(cc, '"'), Char.is_eq(cc, '\''))), hw))

# a character that is no delimiter is pushed on the fast path
def wd.fast(
  +fx: Laws.Vf,
  +buf: List<&2, Char>,
  +cc: Char,
  hd: {T.ch.delim(cc) == False{} : Bool}
) -> {T.MScan{T.read.fast(Laws.vst(fx, buf, T.LBare{}), cc)} == T.MScan{Laws.vst(fx, cc <> buf, T.LBare{})}
  : T.Mode}:
  match fx:
    case Laws.Vf{bad, rows, heads, here, parts, back, qkind, stack, uni, left, arrtab}:
      Equal.cong(Bool, T.Mode, bb => T.MScan{T.read.fast.bare(bb, bad, rows, heads, here, parts, buf, back,
        qkind, stack, uni, left, arrtab, cc)}, T.ch.delim(cc), False{}, hd)

# a later character of a bare value is pushed and the value goes on
def wd.step(
  +fx: Laws.Vf,
  +buf: List<&2, Char>,
  +xx: U32,
  +hw: {Laws.word.char(Chr{xx}) == True{} : Bool}
) -> {T.doc.scan(Laws.vst(fx, buf, T.LBare{}), Chr{xx}) == T.MScan{Laws.vst(fx, Chr{xx} <> buf, T.LBare{})}
  : T.Mode}:
  Equal.trans(T.Mode,
    T.doc.scan(Laws.vst(fx, buf, T.LBare{}), Chr{xx}),
    T.MScan{T.read.fast(Laws.vst(fx, buf, T.LBare{}), Chr{xx})},
    T.MScan{Laws.vst(fx, Chr{xx} <> buf, T.LBare{})},
    scan.other(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), U32.is_eq(xx, 13),
      Laws.vst(fx, buf, T.LBare{}), Chr{xx}, {==}, {==}, {==}, ch => Laws.word.char(ch), hw, {==}, {==}, {==}),
    wd.fast(fx, buf, Chr{xx}, wd.delim(Chr{xx}, hw)))

# the characters a bare value keeps are pushed one by one, whatever follows
def wd.run(
  ks: String,
  +rr: String,
  +fx: Laws.Vf,
  +buf: List<&2, Char>,
  +ee: {Laws.word.rest(ks) == True{} : Bool}
) -> {T.doc.read(String.append(ks, rr), T.MScan{Laws.vst(fx, buf, T.LBare{})})
  == T.doc.read(rr, T.MScan{Laws.vst(fx, rev.onto(ks, buf), T.LBare{})}) : T.Doc}:
  match ks:
    case SNil{}:
      {==}
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          Equal.trans(T.Doc,
            T.doc.read(String.append(tt, rr), T.doc.scan(Laws.vst(fx, buf, T.LBare{}), Chr{xx})),
            T.doc.read(String.append(tt, rr), T.MScan{Laws.vst(fx, Chr{xx} <> buf, T.LBare{})}),
            T.doc.read(rr, T.MScan{Laws.vst(fx, rev.onto(tt, Chr{xx} <> buf), T.LBare{})}),
            Equal.cong(T.Mode, T.Doc, md => T.doc.read(String.append(tt, rr), md),
              T.doc.scan(Laws.vst(fx, buf, T.LBare{}), Chr{xx}),
              T.MScan{Laws.vst(fx, Chr{xx} <> buf, T.LBare{})},
              wd.step(fx, buf, xx, Eq.and.left(Laws.word.char(Chr{xx}), Laws.word.rest(tt), ee))),
            wd.run(tt, rr, fx, Chr{xx} <> buf, Eq.and.right(Laws.word.char(Chr{xx}), Laws.word.rest(tt), ee)))

# the value state's dispatch sends a character that starts a bare value to
# the bare state
def wd.go(
  sp: Bool,
  nl: Bool,
  hash: Bool,
  qq: Bool,
  lit: Bool,
  br: Bool,
  inl: Bool,
  +st: T.St,
  +cc: Char,
  hsp: {sp == False{} : Bool},
  hnl: {nl == False{} : Bool},
  hhs: {hash == False{} : Bool},
  hqq: {qq == False{} : Bool},
  hlt: {lit == False{} : Bool},
  hbr: {br == False{} : Bool},
  hin: {inl == False{} : Bool}
) -> {T.lex.val.go(sp, nl, hash, qq, lit, br, inl, st, cc) == T.st.push(st, cc, T.LBare{}) : T.St}:
  match sp:
    case True{}:
      Eq.bit.absurd2(&2, {T.lex.val.go(True{}, nl, hash, qq, lit, br, inl, st, cc)
        == T.st.push(st, cc, T.LBare{}) : T.St}, hsp)
    case False{}:
      match nl:
        case True{}:
          Eq.bit.absurd2(&2, {T.lex.val.go(False{}, True{}, hash, qq, lit, br, inl, st, cc)
            == T.st.push(st, cc, T.LBare{}) : T.St}, hnl)
        case False{}:
          match hash:
            case True{}:
              Eq.bit.absurd2(&2, {T.lex.val.go(False{}, False{}, True{}, qq, lit, br, inl, st, cc)
                == T.st.push(st, cc, T.LBare{}) : T.St}, hhs)
            case False{}:
              match qq:
                case True{}:
                  Eq.bit.absurd2(&2, {T.lex.val.go(False{}, False{}, False{}, True{}, lit, br, inl, st, cc)
                    == T.st.push(st, cc, T.LBare{}) : T.St}, hqq)
                case False{}:
                  match lit:
                    case True{}:
                      Eq.bit.absurd2(&2, {T.lex.val.go(False{}, False{}, False{}, False{}, True{}, br, inl, st,
                        cc) == T.st.push(st, cc, T.LBare{}) : T.St}, hlt)
                    case False{}:
                      match br:
                        case True{}:
                          Eq.bit.absurd2(&2, {T.lex.val.go(False{}, False{}, False{}, False{}, False{}, True{},
                            inl, st, cc) == T.st.push(st, cc, T.LBare{}) : T.St}, hbr)
                        case False{}:
                          match inl:
                            case True{}:
                              Eq.bit.absurd2(&2, {T.lex.val.go(False{}, False{}, False{}, False{}, False{},
                                False{}, True{}, st, cc) == T.st.push(st, cc, T.LBare{}) : T.St}, hin)
                            case False{}:
                              {==}

# the value state passes a character that is no space and no newline to its
# dispatch, which sends it to the bare state
def wd.ws(
  sp: Bool,
  nl: Bool,
  bad: String,
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  parts: List<&2, String>,
  back: T.Lex,
  qkind: T.QKind,
  stack: List<&2, T.Ctx>,
  uni: U32,
  left: U32,
  arrtab: Bool,
  +cc: Char,
  hsp: {sp == False{} : Bool},
  hnl: {nl == False{} : Bool},
  fsp: {T.ch.sp(cc) == False{} : Bool},
  fnl: {T.ch.nl(cc) == False{} : Bool},
  fhs: {Char.is_eq(cc, '#') == False{} : Bool},
  fqq: {Char.is_eq(cc, '"') == False{} : Bool},
  flt: {Char.is_eq(cc, '\'') == False{} : Bool},
  fbr: {Char.is_eq(cc, '[') == False{} : Bool},
  fin: {Char.is_eq(cc, '{') == False{} : Bool}
) -> {T.read.fast.ws(sp, nl, False{}, bad, rows, heads, here, parts, [], T.LVal{}, back, qkind, stack, uni,
  left, arrtab, cc) == T.St{bad, rows, heads, here, parts, [cc], T.LBare{}, back, qkind, stack, T.HNone{},
  uni, left, arrtab, False{}} : T.St}:
  match sp:
    case True{}:
      Eq.bit.absurd2(&2, {T.read.fast.ws(True{}, nl, False{}, bad, rows, heads, here, parts, [], T.LVal{}, back,
        qkind, stack, uni, left, arrtab, cc) == T.St{bad, rows, heads, here, parts, [cc], T.LBare{}, back, qkind,
        stack, T.HNone{}, uni, left, arrtab, False{}} : T.St}, hsp)
    case False{}:
      match nl:
        case True{}:
          Eq.bit.absurd2(&2, {T.read.fast.ws(False{}, True{}, False{}, bad, rows, heads, here, parts, [],
            T.LVal{}, back, qkind, stack, uni, left, arrtab, cc) == T.St{bad, rows, heads, here, parts, [cc],
            T.LBare{}, back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}} : T.St}, hnl)
        case False{}:
          Equal.cong(T.St, T.St, ss => T.read.once2(ss),
            T.lex.val.go(T.ch.sp(cc), T.ch.nl(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, '"'),
              Char.is_eq(cc, '\''), Char.is_eq(cc, '['), Char.is_eq(cc, '{'), T.St{bad, rows, heads, here, parts,
              [], T.LVal{}, back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}}, cc),
            T.st.push(T.St{bad, rows, heads, here, parts, [], T.LVal{}, back, qkind, stack, T.HNone{}, uni, left,
              arrtab, False{}}, cc, T.LBare{}),
            wd.go(T.ch.sp(cc), T.ch.nl(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, '"'), Char.is_eq(cc, '\''),
              Char.is_eq(cc, '['), Char.is_eq(cc, '{'), T.St{bad, rows, heads, here, parts, [], T.LVal{}, back,
              qkind, stack, T.HNone{}, uni, left, arrtab, False{}}, cc, fsp, fnl, fhs, fqq, flt, fbr, fin))

# the first character of a bare value, read from the value state, is pushed
def wd.lval(
  +fx: Laws.Vf,
  +cc: Char,
  +fsp: {T.ch.sp(cc) == False{} : Bool},
  +fnl: {T.ch.nl(cc) == False{} : Bool},
  +fhs: {Char.is_eq(cc, '#') == False{} : Bool},
  +fqq: {Char.is_eq(cc, '"') == False{} : Bool},
  +flt: {Char.is_eq(cc, '\'') == False{} : Bool},
  +fbr: {Char.is_eq(cc, '[') == False{} : Bool},
  +fin: {Char.is_eq(cc, '{') == False{} : Bool}
) -> {T.MScan{T.read.fast(Laws.vst(fx, [], T.LVal{}), cc)} == T.MScan{Laws.vst(fx, [cc], T.LBare{})} : T.Mode}:
  match fx:
    case Laws.Vf{bad, rows, heads, here, parts, back, qkind, stack, uni, left, arrtab}:
      Equal.cong(T.St, T.Mode, ss => T.MScan{ss},
        T.read.fast.ws(T.ch.sp(cc), T.ch.nl(cc), False{}, bad, rows, heads, here, parts, [], T.LVal{}, back,
          qkind, stack, uni, left, arrtab, cc),
        T.St{bad, rows, heads, here, parts, [cc], T.LBare{}, back, qkind, stack, T.HNone{}, uni, left, arrtab,
          False{}},
        wd.ws(T.ch.sp(cc), T.ch.nl(cc), bad, rows, heads, here, parts, back, qkind, stack, uni, left, arrtab, cc,
          fsp, fnl, fsp, fnl, fhs, fqq, flt, fbr, fin))

# the facts wd.lval takes, from a character that starts a bare value. The
# delimiters are a space, a newline, #, a comma and the closers, in that order
def wd.first(
  +fx: Laws.Vf,
  +xx: U32,
  +h1: {Laws.word.first(Chr{xx}) == True{} : Bool}
) -> {T.doc.scan(Laws.vst(fx, [], T.LVal{}), Chr{xx}) == T.MScan{Laws.vst(fx, [Chr{xx}], T.LBare{})} : T.Mode}:
  +hw = {Eq.and.left(Laws.word.char(Chr{xx}), Bool.not(Bool.or(Char.is_eq(Chr{xx}, '['),
    Char.is_eq(Chr{xx}, '{'))), h1) : {Laws.word.char(Chr{xx}) == True{} : Bool}}
  +hd = {wd.delim(Chr{xx}, hw) : {T.ch.delim(Chr{xx}) == False{} : Bool}}
  +hq = {Eq.not.true(Bool.or(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\'')),
    Eq.and.right(Bool.not(T.ch.delim(Chr{xx})), Bool.not(Bool.or(Char.is_eq(Chr{xx}, '"'),
    Char.is_eq(Chr{xx}, '\''))), hw))
    : {Bool.or(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\'')) == False{} : Bool}}
  +hb = {Eq.not.true(Bool.or(Char.is_eq(Chr{xx}, '['), Char.is_eq(Chr{xx}, '{')),
    Eq.and.right(Laws.word.char(Chr{xx}), Bool.not(Bool.or(Char.is_eq(Chr{xx}, '['),
    Char.is_eq(Chr{xx}, '{'))), h1)) : {Bool.or(Char.is_eq(Chr{xx}, '['), Char.is_eq(Chr{xx}, '{')) == False{} : Bool}}
  +d1 = {Eq.or.right_false(T.ch.sp(Chr{xx}), Bool.or(T.ch.nl(Chr{xx}), Bool.or(Char.is_eq(Chr{xx}, '#'),
    Bool.or(Char.is_eq(Chr{xx}, ','), Bool.or(Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '}'))))), hd)
    : {Bool.or(T.ch.nl(Chr{xx}), Bool.or(Char.is_eq(Chr{xx}, '#'), Bool.or(Char.is_eq(Chr{xx}, ','),
    Bool.or(Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '}'))))) == False{} : Bool}}
  +d2 = {Eq.or.right_false(T.ch.nl(Chr{xx}), Bool.or(Char.is_eq(Chr{xx}, '#'), Bool.or(Char.is_eq(Chr{xx}, ','),
    Bool.or(Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '}')))), d1)
    : {Bool.or(Char.is_eq(Chr{xx}, '#'), Bool.or(Char.is_eq(Chr{xx}, ','), Bool.or(Char.is_eq(Chr{xx}, ']'),
    Char.is_eq(Chr{xx}, '}')))) == False{} : Bool}}
  Equal.trans(T.Mode,
    T.doc.scan(Laws.vst(fx, [], T.LVal{}), Chr{xx}),
    T.MScan{T.read.fast(Laws.vst(fx, [], T.LVal{}), Chr{xx})},
    T.MScan{Laws.vst(fx, [Chr{xx}], T.LBare{})},
    scan.other(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), U32.is_eq(xx, 13),
      Laws.vst(fx, [], T.LVal{}), Chr{xx}, {==}, {==}, {==}, ch => Laws.word.first(ch), h1, {==}, {==}, {==}),
    wd.lval(fx, Chr{xx},
      Eq.or.left_false(T.ch.sp(Chr{xx}), Bool.or(T.ch.nl(Chr{xx}), Bool.or(Char.is_eq(Chr{xx}, '#'),
        Bool.or(Char.is_eq(Chr{xx}, ','), Bool.or(Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '}'))))), hd),
      Eq.or.left_false(T.ch.nl(Chr{xx}), Bool.or(Char.is_eq(Chr{xx}, '#'), Bool.or(Char.is_eq(Chr{xx}, ','),
        Bool.or(Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '}')))), d1),
      Eq.or.left_false(Char.is_eq(Chr{xx}, '#'), Bool.or(Char.is_eq(Chr{xx}, ','),
        Bool.or(Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '}'))), d2),
      Eq.or.left_false(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), hq),
      Eq.or.right_false(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), hq),
      Eq.or.left_false(Char.is_eq(Chr{xx}, '['), Char.is_eq(Chr{xx}, '{'), hb),
      Eq.or.right_false(Char.is_eq(Chr{xx}, '['), Char.is_eq(Chr{xx}, '{'), hb)))

# a newline ends a bare value: word.val classifies the characters pushed, in
# the order they came, and a value is put where the state puts values
def wd.end(
  +fx: Laws.Vf,
  +buf: List<&2, Char>
) -> {T.doc.scan(Laws.vst(fx, buf, T.LBare{}), '\n') == T.MScan{T.read.once2(T.bare.got(
  T.word.val(List.reverse(&2, Char, buf)), Laws.vst(fx, [], T.LBare{}), '\n', Laws.vf.inl(fx)))} : T.Mode}:
  match fx:
    case Laws.Vf{bad, rows, heads, here, parts, back, qkind, stack, uni, left, arrtab}:
      {==}

# the characters of a text, onto a list
def tl.onto(ss: String, ys: List<&2, Char>) -> List<&2, Char>:
  match ss:
    case SNil{}:
      ys
    case SCon{hh, tt}:
      hh <> tl.onto(tt, ys)

# reversing what a text was pushed onto puts the text back in front
def wd.rev(
  ss: String,
  acc: List<&2, Char>,
  ys: List<&2, Char>
) -> {List.reverse.go(&2, Char, rev.onto(ss, acc), ys) == List.reverse.go(&2, Char, acc, tl.onto(ss, ys))
  : List<&2, Char>}:
  match ss:
    case SNil{}:
      {==}
    case SCon{hh, tt}:
      wd.rev(tt, hh <> acc, ys)

# a text's characters onto nothing are its characters
def tl.nil(ss: String) -> {tl.onto(ss, []) == String.to_list(ss) : List<&2, Char>}:
  match ss:
    case SNil{}:
      {==}
    case SCon{+hh, tt}:
      Equal.cong(List<&2, Char>, List<&2, Char>, ys => hh <> ys, tl.onto(tt, []), String.to_list(tt), tl.nil(tt))

# a bare value's first character and the rest, pushed, read back in order
def wd.order(
  +cc: Char,
  +tt: String
) -> {List.reverse(&2, Char, rev.onto(tt, [cc])) == String.to_list(SCon{cc, tt}) : List<&2, Char>}:
  Equal.trans(List<&2, Char>, List.reverse.go(&2, Char, rev.onto(tt, [cc]), []),
    List.reverse.go(&2, Char, [cc], tl.onto(tt, [])), String.to_list(SCon{cc, tt}),
    wd.rev(tt, [cc], []),
    Equal.cong(List<&2, Char>, List<&2, Char>, ys => cc <> ys, tl.onto(tt, []), String.to_list(tt), tl.nil(tt)))

def Laws.word_reads_back(v, s, hc, hv, fx, rest):
  match s:
    case SNil{}:
      Eq.bit.absurd(&2, {Laws.from_val(fx, String.append(SNil{}, SCon{'\n', rest})) == Laws.after_val(fx, v, rest)
        : T.Doc}, hc)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          +h1 = {Eq.and.left(Laws.word.first(Chr{xx}), Laws.word.rest(tt), hc)
            : {Laws.word.first(Chr{xx}) == True{} : Bool}}
          +hr = {Eq.and.right(Laws.word.first(Chr{xx}), Laws.word.rest(tt), hc) : {Laws.word.rest(tt) == True{} : Bool}}
          +ho = {Equal.trans(T.Got, T.word.val(List.reverse(&2, Char, rev.onto(tt, [Chr{xx}]))),
            T.word.val(String.to_list(SCon{Chr{xx}, tt})), T.GotVal{v},
            Equal.cong(List<&2, Char>, T.Got, cs => T.word.val(cs), List.reverse(&2, Char, rev.onto(tt, [Chr{xx}])),
              String.to_list(SCon{Chr{xx}, tt}), wd.order(Chr{xx}, tt)), hv)
            : {T.word.val(List.reverse(&2, Char, rev.onto(tt, [Chr{xx}]))) == T.GotVal{v} : T.Got}}
          Equal.trans(T.Doc,
            T.doc.read(String.append(tt, SCon{'\n', rest}), T.doc.scan(Laws.vst(fx, [], T.LVal{}), Chr{xx})),
            T.doc.read(String.append(tt, SCon{'\n', rest}), T.MScan{Laws.vst(fx, [Chr{xx}], T.LBare{})}),
            Laws.after_val(fx, v, rest),
            Equal.cong(T.Mode, T.Doc, md => T.doc.read(String.append(tt, SCon{'\n', rest}), md),
              T.doc.scan(Laws.vst(fx, [], T.LVal{}), Chr{xx}), T.MScan{Laws.vst(fx, [Chr{xx}], T.LBare{})},
              wd.first(fx, xx, h1)),
            Equal.trans(T.Doc,
              T.doc.read(String.append(tt, SCon{'\n', rest}), T.MScan{Laws.vst(fx, [Chr{xx}], T.LBare{})}),
              T.doc.read(SCon{'\n', rest}, T.MScan{Laws.vst(fx, rev.onto(tt, [Chr{xx}]), T.LBare{})}),
              Laws.after_val(fx, v, rest),
              wd.run(tt, SCon{'\n', rest}, fx, [Chr{xx}], hr),
              Equal.trans(T.Doc,
                T.doc.read(rest, T.doc.scan(Laws.vst(fx, rev.onto(tt, [Chr{xx}]), T.LBare{}), '\n')),
                T.doc.read(rest, T.MScan{T.read.once2(T.bare.got(T.word.val(List.reverse(&2, Char,
                  rev.onto(tt, [Chr{xx}]))), Laws.vst(fx, [], T.LBare{}), '\n', Laws.vf.inl(fx)))}),
                Laws.after_val(fx, v, rest),
                Equal.cong(T.Mode, T.Doc, md => T.doc.read(rest, md),
                  T.doc.scan(Laws.vst(fx, rev.onto(tt, [Chr{xx}]), T.LBare{}), '\n'),
                  T.MScan{T.read.once2(T.bare.got(T.word.val(List.reverse(&2, Char, rev.onto(tt, [Chr{xx}]))),
                    Laws.vst(fx, [], T.LBare{}), '\n', Laws.vf.inl(fx)))},
                  wd.end(fx, rev.onto(tt, [Chr{xx}]))),
                Equal.cong(T.Got, T.Doc, gg => T.doc.read(rest, T.MScan{T.read.once2(T.bare.got(gg,
                  Laws.vst(fx, [], T.LBare{}), '\n', Laws.vf.inl(fx)))}),
                  T.word.val(List.reverse(&2, Char, rev.onto(tt, [Chr{xx}]))), T.GotVal{v}, ho))))

# Booleans. Both texts are fixed, so both facts compute.

def Laws.bool_word(b):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.bool_reads_back(b, fx, rest):
  match b:
    case True{}:
      Laws.word_reads_back(T.VBool{True{}}, "true", {==}, {==}, fx, rest)
    case False{}:
      Laws.word_reads_back(T.VBool{False{}}, "false", {==}, {==}, fx, rest)

# Integers. render writes the sign (a minus only) and the digits. The scan
# reads a first digit that is not 0 into a one-digit numeral, and each later
# digit multiplies the numeral by ten and adds it, least-significant digit
# first; dec.text writes the numeral back as the digits. A lone 0 and -0
# are fixed texts.

# the digit values of characters, in the same order
def vals(cs: List<&2, Char>) -> List<&2, U32>:
  match cs:
    case []:
      []
    case cc <> tt:
      T.dig.val(cc) <> vals(tt)

# a numeral's digits, least-significant first: all digits, and the last one,
# the most significant, is not 0
def nzl(xs: List<&2, Char>) -> Bool:
  match xs:
    case []:
      False{}
    case +xx <> +tt:
      Bool.and(Char.is_digit(xx), Bool.or(nzl(tt), Bool.and(List.is_empty(&2, Char, tt),
        Bool.not(Char.is_eq(xx, '0')))))

# the scan inside the digits of an integer
def ndig(+sg: T.Sign, ds: List<&2, U32>) -> T.Num:
  T.Num{T.NDig{}, sg, 10, ds, False{}, True{}, ""}

# the head of an all-digits walk that answered True is a digit
def then.l(
  ok: Bool,
  tt: String,
  ee: {T.wf.then(ok, _u => T.wf.digits(tt)) == True{} : Bool}
) -> {ok == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      ee

# and the rest of it is all digits
def then.r(
  ok: Bool,
  tt: String,
  ee: {T.wf.then(ok, _u => T.wf.digits(tt)) == True{} : Bool}
) -> {T.wf.digits(tt) == True{} : Bool}:
  match ok:
    case True{}:
      ee
    case False{}:
      Eq.bit.absurd(&2, {T.wf.digits(tt) == True{} : Bool}, ee)

# an `or` whose right half answered False answered its left half
def or.fl(aa: Bool, ee: {Bool.or(aa, False{}) == True{} : Bool}) -> {aa == True{} : Bool}:
  match aa:
    case True{}:
      {==}
    case False{}:
      ee

# ten times a digit plus a digit, over ten and modulo ten, is the two digits:
# one decimal step of the numeral, for each of the hundred pairs
def dgo.step(
  xx: Char,
  +cc: Char,
  +rest: List<&2, U32>,
  hx: {Char.is_digit(xx) == True{} : Bool},
  +hc: {Char.is_digit(cc) == True{} : Bool}
) -> {T.dec.go(T.dig.val(xx) <> rest, 10, T.dig.val(cc)) == T.dig.val(cc) <> T.dec.go(rest, 10, T.dig.val(xx))
  : List<&2, U32>}:
  dg.elim(zz => {T.dec.go(T.dig.val(zz) <> rest, 10, T.dig.val(cc))
    == T.dig.val(cc) <> T.dec.go(rest, 10, T.dig.val(zz)) : List<&2, U32>}, xx, hx,
    dg.elim(yy => {T.dec.go(T.dig.val('0') <> rest, 10, T.dig.val(yy))
      == T.dig.val(yy) <> T.dec.go(rest, 10, T.dig.val('0')) : List<&2, U32>}, cc, hc,
      {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}),
    dg.elim(yy => {T.dec.go(T.dig.val('1') <> rest, 10, T.dig.val(yy))
      == T.dig.val(yy) <> T.dec.go(rest, 10, T.dig.val('1')) : List<&2, U32>}, cc, hc,
      {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}),
    dg.elim(yy => {T.dec.go(T.dig.val('2') <> rest, 10, T.dig.val(yy))
      == T.dig.val(yy) <> T.dec.go(rest, 10, T.dig.val('2')) : List<&2, U32>}, cc, hc,
      {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}),
    dg.elim(yy => {T.dec.go(T.dig.val('3') <> rest, 10, T.dig.val(yy))
      == T.dig.val(yy) <> T.dec.go(rest, 10, T.dig.val('3')) : List<&2, U32>}, cc, hc,
      {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}),
    dg.elim(yy => {T.dec.go(T.dig.val('4') <> rest, 10, T.dig.val(yy))
      == T.dig.val(yy) <> T.dec.go(rest, 10, T.dig.val('4')) : List<&2, U32>}, cc, hc,
      {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}),
    dg.elim(yy => {T.dec.go(T.dig.val('5') <> rest, 10, T.dig.val(yy))
      == T.dig.val(yy) <> T.dec.go(rest, 10, T.dig.val('5')) : List<&2, U32>}, cc, hc,
      {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}),
    dg.elim(yy => {T.dec.go(T.dig.val('6') <> rest, 10, T.dig.val(yy))
      == T.dig.val(yy) <> T.dec.go(rest, 10, T.dig.val('6')) : List<&2, U32>}, cc, hc,
      {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}),
    dg.elim(yy => {T.dec.go(T.dig.val('7') <> rest, 10, T.dig.val(yy))
      == T.dig.val(yy) <> T.dec.go(rest, 10, T.dig.val('7')) : List<&2, U32>}, cc, hc,
      {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}),
    dg.elim(yy => {T.dec.go(T.dig.val('8') <> rest, 10, T.dig.val(yy))
      == T.dig.val(yy) <> T.dec.go(rest, 10, T.dig.val('8')) : List<&2, U32>}, cc, hc,
      {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}),
    dg.elim(yy => {T.dec.go(T.dig.val('9') <> rest, 10, T.dig.val(yy))
      == T.dig.val(yy) <> T.dec.go(rest, 10, T.dig.val('9')) : List<&2, U32>}, cc, hc,
      {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}))

# the carry left once the numeral runs out is its last digit, when that is
# not 0
def dgo.last(
  xx: Char,
  hx: {Char.is_digit(xx) == True{} : Bool},
  hz: {Char.is_eq(xx, '0') == False{} : Bool}
) -> {T.dec.go([], 10, T.dig.val(xx)) == [T.dig.val(xx)] : List<&2, U32>}:
  dg.elim(zz => {Char.is_eq(zz, '0') == False{} : Bool} -> {T.dec.go([], 10, T.dig.val(zz)) == [T.dig.val(zz)]
    : List<&2, U32>}, xx, hx,
    ee => Eq.bit.absurd2(&2, {T.dec.go([], 10, T.dig.val('0')) == [T.dig.val('0')] : List<&2, U32>}, ee),
    _e => {==}, _e => {==}, _e => {==}, _e => {==}, _e => {==}, _e => {==}, _e => {==}, _e => {==},
    _e => {==})(hz)

# a numeral's digits whose last is not 0: the carry reaches the end as that
# digit, so one more digit only goes in front
def dgo.rest(
  +xx: Char,
  tt: List<&2, Char>,
  +hx: {Char.is_digit(xx) == True{} : Bool},
  +hn: {Bool.or(nzl(tt), Bool.and(List.is_empty(&2, Char, tt), Bool.not(Char.is_eq(xx, '0')))) == True{} : Bool},
  ih: {nzl(tt) == True{} : Bool} -> {T.dec.go(vals(tt), 10, T.dig.val(xx)) == vals(xx <> tt) : List<&2, U32>}
) -> {T.dec.go(vals(tt), 10, T.dig.val(xx)) == vals(xx <> tt) : List<&2, U32>}:
  match tt:
    case []:
      dgo.last(xx, hx, Eq.not.true(Char.is_eq(xx, '0'), hn))
    case yy <> ys:
      ih(or.fl(nzl(yy <> ys), hn))

# one more digit in front of a numeral's digits is the numeral times ten plus
# the digit
def dgo(
  acc: List<&2, Char>,
  +cc: Char,
  +hc: {Char.is_digit(cc) == True{} : Bool},
  +hn: {nzl(acc) == True{} : Bool}
) -> {T.dec.go(vals(acc), 10, T.dig.val(cc)) == vals(cc <> acc) : List<&2, U32>}:
  match acc:
    case []:
      Eq.bit.absurd(&2, {T.dec.go([], 10, T.dig.val(cc)) == [T.dig.val(cc)] : List<&2, U32>}, hn)
    case +xx <> +tt:
      +hx = {Eq.and.left(Char.is_digit(xx), Bool.or(nzl(tt), Bool.and(List.is_empty(&2, Char, tt),
        Bool.not(Char.is_eq(xx, '0')))), hn) : {Char.is_digit(xx) == True{} : Bool}}
      Equal.trans(List<&2, U32>, T.dec.go(T.dig.val(xx) <> vals(tt), 10, T.dig.val(cc)),
        T.dig.val(cc) <> T.dec.go(vals(tt), 10, T.dig.val(xx)), T.dig.val(cc) <> vals(xx <> tt),
        dgo.step(xx, cc, vals(tt), hx, hc),
        Equal.cong(List<&2, U32>, List<&2, U32>, ys => T.dig.val(cc) <> ys, T.dec.go(vals(tt), 10, T.dig.val(xx)),
          vals(xx <> tt), dgo.rest(xx, tt, hx, Eq.and.right(Char.is_digit(xx), Bool.or(nzl(tt),
          Bool.and(List.is_empty(&2, Char, tt), Bool.not(Char.is_eq(xx, '0')))), hn),
          ht => dgo(tt, xx, hx, ht))))

# a digit in front of such digits keeps them such digits
def nzl.cons(
  +cc: Char,
  +acc: List<&2, Char>,
  hc: {Char.is_digit(cc) == True{} : Bool},
  hn: {nzl(acc) == True{} : Bool}
) -> {nzl(cc <> acc) == True{} : Bool}:
  and.tt(Char.is_digit(cc), Bool.or(nzl(acc), Bool.and(List.is_empty(&2, Char, acc),
    Bool.not(Char.is_eq(cc, '0')))), hc,
    Equal.cong(Bool, Bool, bb => Bool.or(bb, Bool.and(List.is_empty(&2, Char, acc), Bool.not(Char.is_eq(cc, '0')))),
      nzl(acc), True{}, hn))

# a later digit in the digits of an integer joins the numeral
def nw.step(
  +sg: T.Sign,
  +ds: List<&2, U32>,
  cc: Char,
  hc: {Char.is_digit(cc) == True{} : Bool}
) -> {T.num.step(ndig(sg, ds), cc) == ndig(sg, T.dec.go(ds, 10, T.dig.val(cc))) : T.Num}:
  dg.elim(zz => {T.num.step(ndig(sg, ds), zz) == ndig(sg, T.dec.go(ds, 10, T.dig.val(zz))) : T.Num}, cc, hc,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# the digits after the first, one at a time
def nw(
  tt: String,
  +acc: List<&2, Char>,
  +sg: T.Sign,
  +ht: {T.wf.digits(tt) == True{} : Bool},
  +hn: {nzl(acc) == True{} : Bool}
) -> {T.num.go(String.to_list(tt), ndig(sg, vals(acc))) == ndig(sg, vals(rev.onto(tt, acc))) : T.Num}:
  match tt:
    case SNil{}:
      {==}
    case SCon{+cc, +ts}:
      +hc = {then.l(Char.is_digit(cc), ts, ht) : {Char.is_digit(cc) == True{} : Bool}}
      Equal.trans(T.Num, T.num.go(String.to_list(ts), T.num.step(ndig(sg, vals(acc)), cc)),
        T.num.go(String.to_list(ts), ndig(sg, vals(cc <> acc))), ndig(sg, vals(rev.onto(ts, cc <> acc))),
        Equal.cong(T.Num, T.Num, nn => T.num.go(String.to_list(ts), nn), T.num.step(ndig(sg, vals(acc)), cc),
          ndig(sg, vals(cc <> acc)),
          Equal.trans(T.Num, T.num.step(ndig(sg, vals(acc)), cc), ndig(sg, T.dec.go(vals(acc), 10, T.dig.val(cc))),
            ndig(sg, vals(cc <> acc)), nw.step(sg, vals(acc), cc, hc),
            Equal.cong(List<&2, U32>, T.Num, ds => ndig(sg, ds), T.dec.go(vals(acc), 10, T.dig.val(cc)),
              vals(cc <> acc), dgo(acc, cc, hc, hn)))),
        nw(ts, cc <> acc, sg, then.r(Char.is_digit(cc), ts, ht), nzl.cons(cc, acc, hc, hn)))

# the first digit, not 0, after no sign
def nw.lead(
  +sg: T.Sign,
  cc: Char,
  hc: {Char.is_digit(cc) == True{} : Bool},
  hz: {Char.is_eq(cc, '0') == False{} : Bool}
) -> {T.num.step(T.Num{T.NLead{}, sg, 10, [], False{}, False{}, ""}, cc) == ndig(sg, vals([cc])) : T.Num}:
  dg.elim(zz => {Char.is_eq(zz, '0') == False{} : Bool} -> {T.num.step(T.Num{T.NLead{}, sg, 10, [], False{},
    False{}, ""}, zz) == ndig(sg, vals([zz])) : T.Num}, cc, hc,
    ee => Eq.bit.absurd2(&2, {T.num.step(T.Num{T.NLead{}, sg, 10, [], False{}, False{}, ""}, '0')
      == ndig(sg, vals(['0'])) : T.Num}, ee),
    _e => {==}, _e => {==}, _e => {==}, _e => {==}, _e => {==}, _e => {==}, _e => {==}, _e => {==},
    _e => {==})(hz)

# and after a sign
def nw.sign(
  +sg: T.Sign,
  cc: Char,
  hc: {Char.is_digit(cc) == True{} : Bool},
  hz: {Char.is_eq(cc, '0') == False{} : Bool}
) -> {T.num.step(T.Num{T.NSign{}, sg, 10, [], False{}, False{}, ""}, cc) == ndig(sg, vals([cc])) : T.Num}:
  dg.elim(zz => {Char.is_eq(zz, '0') == False{} : Bool} -> {T.num.step(T.Num{T.NSign{}, sg, 10, [], False{},
    False{}, ""}, zz) == ndig(sg, vals([zz])) : T.Num}, cc, hc,
    ee => Eq.bit.absurd2(&2, {T.num.step(T.Num{T.NSign{}, sg, 10, [], False{}, False{}, ""}, '0')
      == ndig(sg, vals(['0'])) : T.Num}, ee),
    _e => {==}, _e => {==}, _e => {==}, _e => {==}, _e => {==}, _e => {==}, _e => {==}, _e => {==},
    _e => {==})(hz)

# reversing digit values is reversing the digits
def vals.rev(
  xs: List<&2, Char>,
  ys: List<&2, Char>
) -> {List.reverse.go(&2, U32, vals(xs), vals(ys)) == vals(List.reverse.go(&2, Char, xs, ys)) : List<&2, U32>}:
  match xs:
    case []:
      {==}
    case xx <> xt:
      vals.rev(xt, xx <> ys)

# a digit's value written as a digit is the digit
def dg.back(
  cc: Char,
  hc: {Char.is_digit(cc) == True{} : Bool}
) -> {T.dec.ch(T.dig.val(cc)) == cc : Char}:
  dg.elim(zz => {T.dec.ch(T.dig.val(zz)) == zz : Char}, cc, hc,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# digits' values written as digits are the digits
def dg.backs(
  tt: String,
  +ht: {T.wf.digits(tt) == True{} : Bool}
) -> {T.dec.chars(vals(String.to_list(tt))) == String.to_list(tt) : List<&2, Char>}:
  match tt:
    case SNil{}:
      {==}
    case SCon{+cc, +ts}:
      Equal.trans(List<&2, Char>, T.dec.ch(T.dig.val(cc)) <> T.dec.chars(vals(String.to_list(ts))),
        cc <> T.dec.chars(vals(String.to_list(ts))), cc <> String.to_list(ts),
        Equal.cong(Char, List<&2, Char>, zz => zz <> T.dec.chars(vals(String.to_list(ts))),
          T.dec.ch(T.dig.val(cc)), cc, dg.back(cc, then.l(Char.is_digit(cc), ts, ht))),
        Equal.cong(List<&2, Char>, List<&2, Char>, zs => cc <> zs, T.dec.chars(vals(String.to_list(ts))),
          String.to_list(ts), dg.backs(ts, then.r(Char.is_digit(cc), ts, ht))))

# once no zero is being skipped, the digits are kept in order
def dd.kept(
  cs: List<&2, Char>,
  out: List<&2, Char>
) -> {T.dec.drop(cs, False{}, out) == String.from_list(List.reverse.go(&2, Char, out, cs)) : String}:
  match cs:
    case []:
      {==}
    case hh <> tt:
      dd.kept(tt, hh <> out)

# a text's characters make the text again
def ftl(ss: String) -> {String.from_list(String.to_list(ss)) == ss : String}:
  match ss:
    case SNil{}:
      {==}
    case SCon{+hh, tt}:
      Equal.cong(String, String, zs => SCon{hh, zs}, String.from_list(String.to_list(tt)), tt, ftl(tt))

# dec.text of the numeral read from digits whose first is not 0 is the digits
def dtext(
  +hh: Char,
  +tt: String,
  +hx: {Char.is_digit(hh) == True{} : Bool},
  +hz: {Char.is_eq(hh, '0') == False{} : Bool},
  +ht: {T.wf.digits(tt) == True{} : Bool}
) -> {T.dec.text(vals(rev.onto(tt, [hh]))) == SCon{hh, tt} : String}:
  +ro = {wd.order(hh, tt) : {List.reverse(&2, Char, rev.onto(tt, [hh])) == hh <> String.to_list(tt)
    : List<&2, Char>}}
  +hd = {Equal.trans(Bool, T.wf.then(Char.is_digit(hh), _u => T.wf.digits(tt)),
    T.wf.then(True{}, _u => T.wf.digits(tt)), True{},
    Equal.cong(Bool, Bool, bb => T.wf.then(bb, _u => T.wf.digits(tt)), Char.is_digit(hh), True{}, hx), ht)
    : {T.wf.digits(SCon{hh, tt}) == True{} : Bool}}
  Equal.trans(String, T.dec.drop(T.dec.chars(List.reverse.go(&2, U32, vals(rev.onto(tt, [hh])), [])), True{}, []),
    T.dec.drop(T.dec.chars(vals(hh <> String.to_list(tt))), True{}, []), SCon{hh, tt},
    Equal.cong(List<&2, U32>, String, ds => T.dec.drop(T.dec.chars(ds), True{}, []),
      List.reverse.go(&2, U32, vals(rev.onto(tt, [hh])), []), vals(hh <> String.to_list(tt)),
      Equal.trans(List<&2, U32>, List.reverse.go(&2, U32, vals(rev.onto(tt, [hh])), []),
        vals(List.reverse(&2, Char, rev.onto(tt, [hh]))), vals(hh <> String.to_list(tt)),
        vals.rev(rev.onto(tt, [hh]), []),
        Equal.cong(List<&2, Char>, List<&2, U32>, xs => vals(xs), List.reverse(&2, Char, rev.onto(tt, [hh])),
          hh <> String.to_list(tt), ro))),
    Equal.trans(String, T.dec.drop(T.dec.chars(vals(hh <> String.to_list(tt))), True{}, []),
      T.dec.drop(hh <> String.to_list(tt), True{}, []), SCon{hh, tt},
      Equal.cong(List<&2, Char>, String, cs => T.dec.drop(cs, True{}, []),
        T.dec.chars(vals(hh <> String.to_list(tt))), hh <> String.to_list(tt), dg.backs(SCon{hh, tt}, hd)),
      Equal.trans(String, T.dec.drop(String.to_list(tt), Char.is_eq(hh, '0'),
        T.dec.drop.outz(Char.is_eq(hh, '0'), hh, [])),
        T.dec.drop(String.to_list(tt), False{}, [hh]), SCon{hh, tt},
        Equal.cong(Bool, String, bb => T.dec.drop(String.to_list(tt), bb, T.dec.drop.outz(bb, hh, [])),
          Char.is_eq(hh, '0'), False{}, hz),
        Equal.trans(String, T.dec.drop(String.to_list(tt), False{}, [hh]),
          String.from_list(hh <> String.to_list(tt)), SCon{hh, tt},
          dd.kept(String.to_list(tt), [hh]), ftl(SCon{hh, tt})))))

# a digit is no character that starts or ends a word differently
def dg.first(
  cc: Char,
  hc: {Char.is_digit(cc) == True{} : Bool}
) -> {Laws.word.first(cc) == True{} : Bool}:
  dg.elim(zz => {Laws.word.first(zz) == True{} : Bool}, cc, hc,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# a digit is a character a bare value keeps
def dg.char(
  cc: Char,
  hc: {Char.is_digit(cc) == True{} : Bool}
) -> {Laws.word.char(cc) == True{} : Bool}:
  dg.elim(zz => {Laws.word.char(zz) == True{} : Bool}, cc, hc,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# digits are characters a bare value keeps
def dg.rest(
  tt: String,
  +ht: {T.wf.digits(tt) == True{} : Bool}
) -> {Laws.word.rest(tt) == True{} : Bool}:
  match tt:
    case SNil{}:
      {==}
    case SCon{+cc, +ts}:
      and.tt(Laws.word.char(cc), Laws.word.rest(ts), dg.char(cc, then.l(Char.is_digit(cc), ts, ht)),
        dg.rest(ts, then.r(Char.is_digit(cc), ts, ht)))

# a digit starts no special word
def dg.nospec(
  cc: Char,
  hc: {Char.is_digit(cc) == True{} : Bool}
) -> {T.word.special(cc) == False{} : Bool}:
  dg.elim(zz => {T.word.special(zz) == False{} : Bool}, cc, hc,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# a digit is no colon
def dg.nocolon(
  cc: Char,
  hc: {Char.is_digit(cc) == True{} : Bool}
) -> {Char.is_eq(cc, ':') == False{} : Bool}:
  dg.elim(zz => {Char.is_eq(zz, ':') == False{} : Bool}, cc, hc,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# a digit is no dash
def dg.nodash(
  cc: Char,
  hc: {Char.is_digit(cc) == True{} : Bool}
) -> {Char.is_eq(cc, '-') == False{} : Bool}:
  dg.elim(zz => {Char.is_eq(zz, '-') == False{} : Bool}, cc, hc,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# a digit is no i
def dg.noi(
  cc: Char,
  hc: {Char.is_digit(cc) == True{} : Bool}
) -> {False{} == Char.is_eq(cc, 'i') : Bool}:
  dg.elim(zz => {False{} == Char.is_eq(zz, 'i') : Bool}, cc, hc,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# a digit is no n
def dg.non(
  cc: Char,
  hc: {Char.is_digit(cc) == True{} : Bool}
) -> {False{} == Char.is_eq(cc, 'n') : Bool}:
  dg.elim(zz => {False{} == Char.is_eq(zz, 'n') : Bool}, cc, hc,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# a digit after the first character is no dash, and the first is never
# counted
def dash.hit.f(
  ff: Bool,
  cc: Char,
  hc: {Char.is_digit(cc) == True{} : Bool}
) -> {T.word.dash.hit(ff, cc) == False{} : Bool}:
  match ff:
    case True{}:
      {==}
    case False{}:
      dg.nodash(cc, hc)

# digits hold no colon
def dg.colon(
  tt: String,
  +ht: {T.wf.digits(tt) == True{} : Bool}
) -> {T.word.colon(String.to_list(tt)) == False{} : Bool}:
  match tt:
    case SNil{}:
      {==}
    case SCon{+cc, +ts}:
      Equal.trans(Bool, T.word.or(Char.is_eq(cc, ':'), T.word.colon(String.to_list(ts))),
        T.word.or(False{}, T.word.colon(String.to_list(ts))), False{},
        Equal.cong(Bool, Bool, bb => T.word.or(bb, T.word.colon(String.to_list(ts))), Char.is_eq(cc, ':'), False{},
          dg.nocolon(cc, then.l(Char.is_digit(cc), ts, ht))),
        dg.colon(ts, then.r(Char.is_digit(cc), ts, ht)))

# digits hold no dash after the first character
def dg.dash(
  tt: String,
  +ff: Bool,
  +ht: {T.wf.digits(tt) == True{} : Bool}
) -> {T.word.dash(String.to_list(tt), ff) == False{} : Bool}:
  match tt:
    case SNil{}:
      {==}
    case SCon{+cc, +ts}:
      Equal.trans(Bool, T.word.or(T.word.dash.hit(ff, cc), T.word.dash(String.to_list(ts), False{})),
        T.word.or(False{}, T.word.dash(String.to_list(ts), False{})), False{},
        Equal.cong(Bool, Bool, bb => T.word.or(bb, T.word.dash(String.to_list(ts), False{})),
          T.word.dash.hit(ff, cc), False{}, dash.hit.f(ff, cc, then.l(Char.is_digit(cc), ts, ht))),
        dg.dash(ts, False{}, then.r(Char.is_digit(cc), ts, ht)))

# a word that is neither a datetime by its colons and dashes nor an exponent
# numeral goes to the numeral scan
def asd.f(ee: Bool) -> {T.word.as_date(False{}, ee) == False{} : Bool}:
  match ee:
    case True{}:
      {==}
    case False{}:
      {==}

# a word with no colon and no dash after its first character, special or
# not, is a numeral
def route.num(
  +cs: List<&2, Char>,
  hc: {T.word.colon(cs) == False{} : Bool},
  hd: {T.word.dash(cs, True{}) == False{} : Bool}
) -> {T.word.route(T.GotBad{""}, T.word.or(T.word.colon(cs), T.word.dash(cs, True{})), cs) == T.word.num(cs)
  : T.Got}:
  %Equal.sym(Bool, T.word.colon(cs), False{}, hc) :
    {T.word.route(T.GotBad{""}, T.word.or(_, T.word.dash(cs, True{})), cs) == T.word.num(cs) : T.Got}
  %Equal.sym(Bool, T.word.dash(cs, True{}), False{}, hd) :
    {T.word.route(T.GotBad{""}, T.word.or(False{}, _), cs) == T.word.num(cs) : T.Got}
  %Equal.sym(Bool, T.word.as_date(False{}, T.word.ee(cs)), False{}, asd.f(T.word.ee(cs))) :
    {T.word.route.date(_, cs) == T.word.num(cs) : T.Got}
  {==}


# a word that starts with a minus and a digit is no special: it differs from
# -inf and -nan at the digit, and from the others at the minus
def spec.m(
  +hh: Char,
  +rest: List<&2, Char>,
  ei: {False{} == Char.is_eq(hh, 'i') : Bool},
  en: {False{} == Char.is_eq(hh, 'n') : Bool}
) -> {T.word.spec(String.from_list('-' <> hh <> rest)) == T.GotBad{""} : T.Got}:
  Equal.trans(T.Got,
    T.word.spec.inf3(T.str.eq.step(String.from_list(rest), "nf", Char.is_eq(hh, 'i')),
      String.from_list('-' <> hh <> rest)),
    T.word.spec.inf3(False{}, String.from_list('-' <> hh <> rest)),
    T.GotBad{""},
    Equal.cong(Bool, T.Got, bb => T.word.spec.inf3(bb, String.from_list('-' <> hh <> rest)),
      T.str.eq.step(String.from_list(rest), "nf", Char.is_eq(hh, 'i')), False{},
      str.eq.off2(String.from_list(rest), "nf", Char.is_eq(hh, 'i'), ei)),
    Equal.cong(Bool, T.Got, bb => T.word.spec.nan3(bb),
      T.str.eq.step(String.from_list(rest), "an", Char.is_eq(hh, 'n')), False{},
      str.eq.off2(String.from_list(rest), "an", Char.is_eq(hh, 'n'), en)))

# a digit and digits are digits
def dgs.cons(
  +hh: Char,
  +tt: String,
  hx: {Char.is_digit(hh) == True{} : Bool},
  ht: {T.wf.digits(tt) == True{} : Bool}
) -> {T.wf.digits(SCon{hh, tt}) == True{} : Bool}:
  Equal.trans(Bool, T.wf.then(Char.is_digit(hh), _u => T.wf.digits(tt)),
    T.wf.then(True{}, _u => T.wf.digits(tt)), True{},
    Equal.cong(Bool, Bool, bb => T.wf.then(bb, _u => T.wf.digits(tt)), Char.is_digit(hh), True{}, hx), ht)

# a first digit that is not 0 starts such digits
def nzl.one(
  +hh: Char,
  hx: {Char.is_digit(hh) == True{} : Bool},
  hz: {Char.is_eq(hh, '0') == False{} : Bool}
) -> {nzl([hh]) == True{} : Bool}:
  and.tt(Char.is_digit(hh), Bool.or(False{}, Bool.and(True{}, Bool.not(Char.is_eq(hh, '0')))), hx,
    Equal.cong(Bool, Bool, bb => Bool.or(False{}, Bool.and(True{}, Bool.not(bb))), Char.is_eq(hh, '0'), False{},
      hz))

# the numeral scan over the digits of an integer, from the first one on
def int.scan(
  +sg: T.Sign,
  st0: T.Num,
  +hh: Char,
  +tt: String,
  e0: {T.num.step(st0, hh) == ndig(sg, vals([hh])) : T.Num},
  +hx: {Char.is_digit(hh) == True{} : Bool},
  +hz: {Char.is_eq(hh, '0') == False{} : Bool},
  +ht: {T.wf.digits(tt) == True{} : Bool}
) -> {T.num.go(String.to_list(tt), T.num.step(st0, hh)) == ndig(sg, vals(rev.onto(tt, [hh]))) : T.Num}:
  Equal.trans(T.Num, T.num.go(String.to_list(tt), T.num.step(st0, hh)),
    T.num.go(String.to_list(tt), ndig(sg, vals([hh]))), ndig(sg, vals(rev.onto(tt, [hh]))),
    Equal.cong(T.Num, T.Num, nn => T.num.go(String.to_list(tt), nn), T.num.step(st0, hh), ndig(sg, vals([hh])), e0),
    nw(tt, [hh], sg, ht, nzl.one(hh, hx, hz)))

# the finished numeral is the integer, in range
def int.fin(
  +sg: T.Sign,
  +hh: Char,
  +tt: String,
  +hx: {Char.is_digit(hh) == True{} : Bool},
  +hz: {Char.is_eq(hh, '0') == False{} : Bool},
  +ht: {T.wf.digits(tt) == True{} : Bool},
  hf: {T.i64.fits(sg, SCon{hh, tt}) == True{} : Bool},
  cs: List<&2, Char>
) -> {T.num.fin(ndig(sg, vals(rev.onto(tt, [hh]))), cs) == T.GotVal{T.VInt{sg, SCon{hh, tt}}} : T.Got}:
  Equal.trans(T.Got,
    T.num.fin.range(T.i64.fits(sg, T.dec.text(vals(rev.onto(tt, [hh])))), sg, T.dec.text(vals(rev.onto(tt, [hh])))),
    T.num.fin.range(T.i64.fits(sg, SCon{hh, tt}), sg, SCon{hh, tt}),
    T.GotVal{T.VInt{sg, SCon{hh, tt}}},
    Equal.cong(String, T.Got, ss => T.num.fin.range(T.i64.fits(sg, ss), sg, ss),
      T.dec.text(vals(rev.onto(tt, [hh]))), SCon{hh, tt}, dtext(hh, tt, hx, hz, ht)),
    Equal.cong(Bool, T.Got, bb => T.num.fin.range(bb, sg, SCon{hh, tt}), T.i64.fits(sg, SCon{hh, tt}), True{},
      hf))

# what int_word claims
def int.Goal(+sg: T.Sign, +ds: String) -> Type:
  {T.word.val(String.to_list(T.render.atom(T.VInt{sg, ds}))) == T.GotVal{T.VInt{sg, ds}} : T.Got}

# a positive integer whose first digit is not 0: no special, no datetime, and
# the numeral scan reads its digits
def int.plus(
  +hh: Char,
  +tt: String,
  +hx: {Char.is_digit(hh) == True{} : Bool},
  +hz: {Char.is_eq(hh, '0') == False{} : Bool},
  +ht: {T.wf.digits(tt) == True{} : Bool},
  +hf: {T.i64.fits(T.Plus{}, SCon{hh, tt}) == True{} : Bool}
) -> int.Goal(T.Plus{}, SCon{hh, tt}):
  +hd = {dgs.cons(hh, tt, hx, ht) : {T.wf.digits(SCon{hh, tt}) == True{} : Bool}}
  Equal.trans(T.Got, T.word.val.pick(T.word.special(hh), hh <> String.to_list(tt)),
    T.word.val.pick(False{}, hh <> String.to_list(tt)), T.GotVal{T.VInt{T.Plus{}, SCon{hh, tt}}},
    Equal.cong(Bool, T.Got, bb => T.word.val.pick(bb, hh <> String.to_list(tt)), T.word.special(hh), False{},
      dg.nospec(hh, hx)),
    Equal.trans(T.Got, T.word.route(T.GotBad{""}, T.word.or(T.word.colon(hh <> String.to_list(tt)),
      T.word.dash(hh <> String.to_list(tt), True{})), hh <> String.to_list(tt)),
      T.word.num(hh <> String.to_list(tt)), T.GotVal{T.VInt{T.Plus{}, SCon{hh, tt}}},
      route.num(hh <> String.to_list(tt), dg.colon(SCon{hh, tt}, hd), dg.dash(SCon{hh, tt}, True{}, hd)),
      Equal.trans(T.Got, T.num.fin(T.num.go(String.to_list(tt), T.num.step(T.num.start(), hh)),
        hh <> String.to_list(tt)),
        T.num.fin(ndig(T.Plus{}, vals(rev.onto(tt, [hh]))), hh <> String.to_list(tt)),
        T.GotVal{T.VInt{T.Plus{}, SCon{hh, tt}}},
        Equal.cong(T.Num, T.Got, nn => T.num.fin(nn, hh <> String.to_list(tt)),
          T.num.go(String.to_list(tt), T.num.step(T.num.start(), hh)), ndig(T.Plus{}, vals(rev.onto(tt, [hh]))),
          int.scan(T.Plus{}, T.num.start(), hh, tt, nw.lead(T.Plus{}, hh, hx, hz), hx, hz, ht)),
        int.fin(T.Plus{}, hh, tt, hx, hz, ht, hf, hh <> String.to_list(tt)))))

# a negative integer whose first digit is not 0: the minus makes it a
# special candidate, which it is not, and then it reads as a positive one
# does, from the state after the sign
def int.minus(
  +hh: Char,
  +tt: String,
  +hx: {Char.is_digit(hh) == True{} : Bool},
  +hz: {Char.is_eq(hh, '0') == False{} : Bool},
  +ht: {T.wf.digits(tt) == True{} : Bool},
  +hf: {T.i64.fits(T.Minus{}, SCon{hh, tt}) == True{} : Bool}
) -> int.Goal(T.Minus{}, SCon{hh, tt}):
  +hd = {dgs.cons(hh, tt, hx, ht) : {T.wf.digits(SCon{hh, tt}) == True{} : Bool}}
  Equal.trans(T.Got, T.word.route(T.word.spec(String.from_list('-' <> hh <> String.to_list(tt))),
    T.word.or(T.word.colon('-' <> hh <> String.to_list(tt)), T.word.dash('-' <> hh <> String.to_list(tt),
    True{})), '-' <> hh <> String.to_list(tt)),
    T.word.route(T.GotBad{""}, T.word.or(T.word.colon('-' <> hh <> String.to_list(tt)),
      T.word.dash('-' <> hh <> String.to_list(tt), True{})), '-' <> hh <> String.to_list(tt)),
    T.GotVal{T.VInt{T.Minus{}, SCon{hh, tt}}},
    Equal.cong(T.Got, T.Got, gg => T.word.route(gg, T.word.or(T.word.colon('-' <> hh <> String.to_list(tt)),
      T.word.dash('-' <> hh <> String.to_list(tt), True{})), '-' <> hh <> String.to_list(tt)),
      T.word.spec(String.from_list('-' <> hh <> String.to_list(tt))), T.GotBad{""},
      spec.m(hh, String.to_list(tt), dg.noi(hh, hx), dg.non(hh, hx))),
    Equal.trans(T.Got, T.word.route(T.GotBad{""}, T.word.or(T.word.colon('-' <> hh <> String.to_list(tt)),
      T.word.dash('-' <> hh <> String.to_list(tt), True{})), '-' <> hh <> String.to_list(tt)),
      T.word.num('-' <> hh <> String.to_list(tt)), T.GotVal{T.VInt{T.Minus{}, SCon{hh, tt}}},
      route.num('-' <> hh <> String.to_list(tt), dg.colon(SCon{hh, tt}, hd), dg.dash(SCon{hh, tt}, False{}, hd)),
      Equal.trans(T.Got, T.num.fin(T.num.go(String.to_list(tt), T.num.step(T.Num{T.NSign{}, T.Minus{}, 10, [],
        False{}, False{}, ""}, hh)), '-' <> hh <> String.to_list(tt)),
        T.num.fin(ndig(T.Minus{}, vals(rev.onto(tt, [hh]))), '-' <> hh <> String.to_list(tt)),
        T.GotVal{T.VInt{T.Minus{}, SCon{hh, tt}}},
        Equal.cong(T.Num, T.Got, nn => T.num.fin(nn, '-' <> hh <> String.to_list(tt)),
          T.num.go(String.to_list(tt), T.num.step(T.Num{T.NSign{}, T.Minus{}, 10, [], False{}, False{}, ""}, hh)),
          ndig(T.Minus{}, vals(rev.onto(tt, [hh]))),
          int.scan(T.Minus{}, T.Num{T.NSign{}, T.Minus{}, 10, [], False{}, False{}, ""}, hh, tt,
            nw.sign(T.Minus{}, hh, hx, hz), hx, hz, ht)),
        int.fin(T.Minus{}, hh, tt, hx, hz, ht, hf, '-' <> hh <> String.to_list(tt)))))

# a first digit that is not 0, by the sign
def int.nz(
  +sg: T.Sign,
  +hh: Char,
  +tt: String,
  +hx: {Char.is_digit(hh) == True{} : Bool},
  +hz: {Char.is_eq(hh, '0') == False{} : Bool},
  +ht: {T.wf.digits(tt) == True{} : Bool},
  +hf: {T.i64.fits(sg, SCon{hh, tt}) == True{} : Bool}
) -> int.Goal(sg, SCon{hh, tt}):
  match sg:
    case T.Plus{}:
      int.plus(hh, tt, hx, hz, ht, hf)
    case T.Minus{}:
      int.minus(hh, tt, hx, hz, ht, hf)

# a lone 0, with either sign
def int.zero(
  tt: String,
  +sg: T.Sign,
  hd: {String.is_empty(tt) == True{} : Bool}
) -> int.Goal(sg, SCon{'0', tt}):
  match tt:
    case SNil{}:
      match sg:
        case T.Plus{}:
          {==}
        case T.Minus{}:
          {==}
    case SCon{ch, ct}:
      Eq.bit.absurd(&1, int.Goal(sg, SCon{'0', SCon{ch, ct}}), hd)

# a well-formed integer, by its first digit: a lone 0, with either sign, is a
# fixed text; any other first digit starts the numeral
def int.lead(
  +hh: Char,
  zz: Bool,
  ez: {Char.is_eq(hh, '0') == zz : Bool},
  +tt: String,
  +sg: T.Sign,
  +hd: {T.wf.dec.lead(zz, hh, tt) == True{} : Bool},
  +hf: {T.i64.fits(sg, SCon{hh, tt}) == True{} : Bool}
) -> int.Goal(sg, SCon{hh, tt}):
  match zz:
    case True{}:
      %Equal.sym(Char, hh, '0', Eq.char_eq_true(hh, '0', ez)) : int.Goal(sg, SCon{_, tt})
      int.zero(tt, sg, hd)
    case False{}:
      int.nz(sg, hh, tt, Eq.and.left(Char.is_digit(hh), T.wf.digits(tt), hd), ez,
        Eq.and.right(Char.is_digit(hh), T.wf.digits(tt), hd), hf)

def Laws.int_word(sg, ds, w):
  match ds:
    case SNil{}:
      Eq.bit.absurd(&1, int.Goal(sg, SNil{}), w)
    case SCon{+hh, +tt}:
      int.lead(hh, Char.is_eq(hh, '0'), {==}, tt, sg, Eq.and.left(T.wf.dec(SCon{hh, tt}),
        T.i64.fits(sg, SCon{hh, tt}), w), Eq.and.right(T.wf.dec(SCon{hh, tt}), T.i64.fits(sg, SCon{hh, tt}), w))

# what int.chars claims
def int.Chars(+sg: T.Sign, +ds: String) -> Type:
  {Laws.word.chars(T.render.atom(T.VInt{sg, ds})) == True{} : Bool}

# the digits of an integer whose first digit is not 0 are a bare value, by
# the sign
def int.chars.nz(
  +sg: T.Sign,
  +hh: Char,
  +tt: String,
  +hx: {Char.is_digit(hh) == True{} : Bool},
  +ht: {T.wf.digits(tt) == True{} : Bool}
) -> int.Chars(sg, SCon{hh, tt}):
  match sg:
    case T.Plus{}:
      and.tt(Laws.word.first(hh), Laws.word.rest(tt), dg.first(hh, hx), dg.rest(tt, ht))
    case T.Minus{}:
      and.tt(Laws.word.first('-'), Laws.word.rest(SCon{hh, tt}), {==},
        dg.rest(SCon{hh, tt}, dgs.cons(hh, tt, hx, ht)))

# a lone 0 is a bare value, with either sign
def int.chars.zero(
  tt: String,
  +sg: T.Sign,
  hd: {String.is_empty(tt) == True{} : Bool}
) -> int.Chars(sg, SCon{'0', tt}):
  match tt:
    case SNil{}:
      match sg:
        case T.Plus{}:
          {==}
        case T.Minus{}:
          {==}
    case SCon{ch, ct}:
      Eq.bit.absurd(&1, int.Chars(sg, SCon{'0', SCon{ch, ct}}), hd)

# a well-formed integer's text is a bare value, by its first digit
def int.chars.lead(
  +hh: Char,
  zz: Bool,
  ez: {Char.is_eq(hh, '0') == zz : Bool},
  +tt: String,
  +sg: T.Sign,
  +hd: {T.wf.dec.lead(zz, hh, tt) == True{} : Bool}
) -> int.Chars(sg, SCon{hh, tt}):
  match zz:
    case True{}:
      %Equal.sym(Char, hh, '0', Eq.char_eq_true(hh, '0', ez)) : int.Chars(sg, SCon{_, tt})
      int.chars.zero(tt, sg, hd)
    case False{}:
      int.chars.nz(sg, hh, tt, Eq.and.left(Char.is_digit(hh), T.wf.digits(tt), hd),
        Eq.and.right(Char.is_digit(hh), T.wf.digits(tt), hd))

# a well-formed integer's text is a bare value
def int.chars(
  +sg: T.Sign,
  ds: String,
  hd: {T.wf.dec(ds) == True{} : Bool}
) -> int.Chars(sg, ds):
  match ds:
    case SNil{}:
      Eq.bit.absurd(&1, int.Chars(sg, SNil{}), hd)
    case SCon{+hh, +tt}:
      int.chars.lead(hh, Char.is_eq(hh, '0'), {==}, tt, sg, hd)

def Laws.int_reads_back(sg, ds, w, fx, rest):
  Laws.word_reads_back(T.VInt{sg, ds}, T.render.atom(T.VInt{sg, ds}),
    int.chars(sg, ds, Eq.and.left(T.wf.dec(ds), T.i64.fits(sg, ds), w)), Laws.int_word(sg, ds, w), fx, rest)

# Floats. wf.flo reads a float's spelling with an automaton of states Fl; the
# numeral scan reads the same spelling with its own states. nm names the scan
# state that matches each Fl state, and one lemma per state and character (a
# bundle) says the two step together, with the facts about the character the
# classifier needs. inf and nan are fixed texts.

# the numeral scan state that matches a float automaton state; ds is the
# numeral the scan has built, which only integer and float digits keep
def nm(fl: T.Fl, +sg: T.Sign, ds: List<&2, U32>) -> T.Num:
  match fl:
    case T.FlStart{}:
      T.Num{T.NLead{}, sg, 10, [], False{}, False{}, ""}
    case T.FlZero{}:
      T.Num{T.NZero{}, sg, 10, [], False{}, True{}, ""}
    case T.FlInt{}:
      T.Num{T.NDig{}, sg, 10, ds, False{}, True{}, ""}
    case T.FlDot{}:
      T.Num{T.NFrac{}, sg, 10, [], False{}, False{}, ""}
    case T.FlFrac{}:
      T.Num{T.NFrac{}, sg, 10, ds, False{}, True{}, ""}
    case T.FlE{}:
      T.Num{T.NExp{}, sg, 10, [], False{}, False{}, ""}
    case T.FlESign{}:
      T.Num{T.NEDig{}, sg, 10, [], False{}, False{}, ""}
    case T.FlExp{}:
      T.Num{T.NEDig{}, sg, 10, ds, False{}, True{}, ""}
    case T.FlNo{}:
      T.Num{T.NBad{}, sg, 10, [], False{}, False{}, ""}

# the numeral a scan state keeps
def nm.ds(fl: T.Fl, ds: List<&2, U32>) -> List<&2, U32>:
  match fl:
    case T.FlInt{}:
      ds
    case T.FlFrac{}:
      ds
    case T.FlExp{}:
      ds
    case _:
      []

# the numeral after a spelling, as the scan builds it
def nds(cs: List<&2, Char>, +fl: T.Fl, ds: List<&2, U32>) -> List<&2, U32>:
  match cs:
    case []:
      ds
    case +cc <> tt:
      nds(tt, T.wf.flo.step(fl, cc), T.dec.go(nm.ds(fl, ds), 10, T.dig.val(cc)))

# a state the automaton can still accept from
def fl.live(fl: T.Fl) -> Bool:
  match fl:
    case T.FlNo{}:
      False{}
    case _:
      True{}

# a state before the exponent
def fl.pre(fl: T.Fl) -> Bool:
  match fl:
    case T.FlStart{}:
      True{}
    case T.FlZero{}:
      True{}
    case T.FlInt{}:
      True{}
    case T.FlDot{}:
      True{}
    case T.FlFrac{}:
      True{}
    case _:
      False{}

# the first state
def fl.start(fl: T.Fl) -> Bool:
  match fl:
    case T.FlStart{}:
      True{}
    case _:
      False{}

# two bits are one bit
def beq(aa: Bool, bb: Bool) -> Bool:
  match aa bb:
    case True{} True{}:
      True{}
    case False{} False{}:
      True{}
    case _ _:
      False{}

# two bits beq calls equal are one bit
def beq.eq(aa: Bool, bb: Bool, ee: {beq(aa, bb) == True{} : Bool}) -> {aa == bb : Bool}:
  match aa bb:
    case True{} True{}:
      {==}
    case False{} False{}:
      {==}
    case True{} False{}:
      Eq.bit.absurd(&2, {True{} == False{} : Bool}, ee)
    case False{} True{}:
      Eq.bit.absurd(&2, {False{} == True{} : Bool}, ee)

# a sign
def fq.pm(+cc: Char) -> Bool:
  Bool.or(Char.is_eq(cc, '+'), Char.is_eq(cc, '-'))

# a capital exponent mark or a sign
def fq.big(+cc: Char) -> Bool:
  Bool.or(Char.is_eq(cc, 'E'), fq.pm(cc))

# an exponent mark or a sign
def fq.e(+cc: Char) -> Bool:
  Bool.or(Char.is_eq(cc, 'e'), fq.big(cc))

# a dot, an exponent mark or a sign
def fq.dot(+cc: Char) -> Bool:
  Bool.or(Char.is_eq(cc, '.'), fq.e(cc))

# a character of the float alphabet: a digit, a dot, an exponent mark or a
# sign
def fch(+cc: Char) -> Bool:
  Bool.or(Char.is_digit(cc), Bool.or(Char.is_eq(cc, '.'), Bool.or(Char.is_eq(cc, 'e'), Bool.or(Char.is_eq(cc, 'E'),
    Bool.or(Char.is_eq(cc, '+'), Char.is_eq(cc, '-'))))))

# what a live step says of its character: a character a bare value keeps, no
# underscore and no colon, no minus before the exponent, a digit first, and
# the step leaves the exponent's part only at an exponent mark
def fa6(+fl: T.Fl, +cc: Char) -> Bool:
  beq(fl.pre(T.wf.flo.step(fl, cc)), Bool.and(fl.pre(fl), Bool.not(T.word.ee.hit(cc))))

def fa5(+fl: T.Fl, +cc: Char) -> Bool:
  Bool.and(Bool.or(Bool.not(fl.start(fl)), Char.is_digit(cc)), fa6(fl, cc))

def fa4(+fl: T.Fl, +cc: Char) -> Bool:
  Bool.and(Bool.not(Bool.and(fl.pre(fl), Char.is_eq(cc, '-'))), fa5(fl, cc))

def fa3(+fl: T.Fl, +cc: Char) -> Bool:
  Bool.and(Bool.not(Char.is_eq(cc, ':')), fa4(fl, cc))

def fa2(+fl: T.Fl, +cc: Char) -> Bool:
  Bool.and(Bool.not(Char.is_eq(cc, '_')), fa3(fl, cc))

def fl.facts(+fl: T.Fl, +cc: Char) -> Bool:
  Bool.and(Laws.word.char(cc), fa2(fl, cc))

# a scan state and a bit
type Fs is Data:
  Fs{n: T.Num, b: Bool}

# the scan state
def fs.n(fs: Fs) -> T.Num:
  match fs:
    case Fs{nn, _b}:
      nn

# the bit
def fs.b(fs: Fs) -> Bool:
  match fs:
    case Fs{_n, bb}:
      bb

# the bundle: on a live step the scan steps as the automaton does, and the
# facts hold
def fb(+fl: T.Fl, +sg: T.Sign, +ds: List<&2, U32>, +cc: Char) -> Type:
  {Fs{T.num.step(nm(fl, sg, ds), cc), fl.facts(fl, cc)}
    == Fs{nm(T.wf.flo.step(fl, cc), sg, T.dec.go(nm.ds(fl, ds), 10, T.dig.val(cc))), True{}} : Fs}

# a sign of the float alphabet
def fe.pm(
  -P: Char -> Type,
  +cc: Char,
  pl: Bool,
  epl: {Char.is_eq(cc, '+') == pl : Bool},
  h: {Bool.or(pl, Char.is_eq(cc, '-')) == True{} : Bool},
  pp: P('+'),
  pm: P('-')
) -> P(cc):
  match pl:
    case True{}:
      %Equal.sym(Char, cc, '+', Eq.char_eq_true(cc, '+', epl)) : P(_)
      pp
    case False{}:
      %Equal.sym(Char, cc, '-', Eq.char_eq_true(cc, '-', h)) : P(_)
      pm

# a capital exponent mark or a sign
def fe.big(
  -P: Char -> Type,
  +cc: Char,
  be: Bool,
  ebe: {Char.is_eq(cc, 'E') == be : Bool},
  h: {Bool.or(be, Bool.or(Char.is_eq(cc, '+'), Char.is_eq(cc, '-'))) == True{} : Bool},
  pE: P('E'),
  pp: P('+'),
  pm: P('-')
) -> P(cc):
  match be:
    case True{}:
      %Equal.sym(Char, cc, 'E', Eq.char_eq_true(cc, 'E', ebe)) : P(_)
      pE
    case False{}:
      fe.pm(P, cc, Char.is_eq(cc, '+'), {==}, h, pp, pm)

# an exponent mark or a sign
def fe.e(
  -P: Char -> Type,
  +cc: Char,
  e1: Bool,
  ee1: {Char.is_eq(cc, 'e') == e1 : Bool},
  h: {Bool.or(e1, fq.big(cc)) == True{} : Bool},
  pe: P('e'),
  pE: P('E'),
  pp: P('+'),
  pm: P('-')
) -> P(cc):
  match e1:
    case True{}:
      %Equal.sym(Char, cc, 'e', Eq.char_eq_true(cc, 'e', ee1)) : P(_)
      pe
    case False{}:
      fe.big(P, cc, Char.is_eq(cc, 'E'), {==}, h, pE, pp, pm)

# the fifteen characters of the float alphabet, from the dot on
def fe.rest(
  -P: Char -> Type,
  +cc: Char,
  dt: Bool,
  edt: {Char.is_eq(cc, '.') == dt : Bool},
  h: {Bool.or(dt, fq.e(cc)) == True{} : Bool},
  pdt: P('.'),
  pe: P('e'),
  pE: P('E'),
  pp: P('+'),
  pm: P('-')
) -> P(cc):
  match dt:
    case True{}:
      %Equal.sym(Char, cc, '.', Eq.char_eq_true(cc, '.', edt)) : P(_)
      pdt
    case False{}:
      fe.e(P, cc, Char.is_eq(cc, 'e'), {==}, h, pe, pE, pp, pm)

# a digit, or one of the others
def fe.go(
  -P: Char -> Type,
  +cc: Char,
  dg: Bool,
  edg: {Char.is_digit(cc) == dg : Bool},
  h: {Bool.or(dg, fq.dot(cc)) == True{} : Bool},
  p0: P('0'),
  p1: P('1'),
  p2: P('2'),
  p3: P('3'),
  p4: P('4'),
  p5: P('5'),
  p6: P('6'),
  p7: P('7'),
  p8: P('8'),
  p9: P('9'),
  pdt: P('.'),
  pe: P('e'),
  pE: P('E'),
  pp: P('+'),
  pm: P('-')
) -> P(cc):
  match dg:
    case True{}:
      dg.elim(P, cc, edg, p0, p1, p2, p3, p4, p5, p6, p7, p8, p9)
    case False{}:
      fe.rest(P, cc, Char.is_eq(cc, '.'), {==}, h, pdt, pe, pE, pp, pm)

# a claim made of each character of the float alphabet is made of every
# character of it
def fe.elim(
  -P: Char -> Type,
  +cc: Char,
  h: {fch(cc) == True{} : Bool},
  p0: P('0'),
  p1: P('1'),
  p2: P('2'),
  p3: P('3'),
  p4: P('4'),
  p5: P('5'),
  p6: P('6'),
  p7: P('7'),
  p8: P('8'),
  p9: P('9'),
  pdt: P('.'),
  pe: P('e'),
  pE: P('E'),
  pp: P('+'),
  pm: P('-')
) -> P(cc):
  fe.go(P, cc, Char.is_digit(cc), {==}, h, p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, pdt, pe, pE, pp, pm)

# a character that is no digit is no 0
def z0.go(
  cc: Char,
  zz: Bool,
  ez: {Char.is_eq(cc, '0') == zz : Bool},
  nd: {Char.is_digit(cc) == False{} : Bool}
) -> {zz == False{} : Bool}:
  match zz:
    case False{}:
      {==}
    case True{}:
      Eq.bit.absurd2(&2, {True{} == False{} : Bool}, Equal.trans(Bool, True{}, Char.is_digit(cc), False{},
        Equal.cong(Char, Bool, ch => Char.is_digit(ch), '0', cc,
          Equal.sym(Char, cc, '0', Eq.char_eq_true(cc, '0', ez))), nd))

# no exponent mark
def nie(
  +cc: Char,
  ne: {Char.is_eq(cc, 'e') == False{} : Bool},
  nE: {Char.is_eq(cc, 'E') == False{} : Bool}
) -> {T.wf.flo.is_e(cc) == False{} : Bool}:
  Equal.trans(Bool, T.wf.flo.is_e(cc), Bool.or(False{}, Char.is_eq(cc, 'E')), False{},
    Equal.cong(Bool, Bool, bb => Bool.or(bb, Char.is_eq(cc, 'E')), Char.is_eq(cc, 'e'), False{}, ne), nE)

# no dot and no exponent mark: nothing may follow the integer part
def tail.no(
  +cc: Char,
  ndt: {Char.is_eq(cc, '.') == False{} : Bool},
  ne: {T.wf.flo.is_e(cc) == False{} : Bool}
) -> {T.wf.flo.tail(cc) == T.FlNo{} : T.Fl}:
  Equal.trans(T.Fl, T.wf.flo.tail(cc), Bool.pick(T.Fl, T.wf.flo.is_e(cc), T.FlE{}, T.FlNo{}), T.FlNo{},
    Equal.cong(Bool, T.Fl, bb => Bool.pick(T.Fl, bb, T.FlDot{}, Bool.pick(T.Fl, T.wf.flo.is_e(cc), T.FlE{},
      T.FlNo{})), Char.is_eq(cc, '.'), False{}, ndt),
    Equal.cong(Bool, T.Fl, bb => Bool.pick(T.Fl, bb, T.FlE{}, T.FlNo{}), T.wf.flo.is_e(cc), False{}, ne))

# a character outside the float alphabet ends every state's walk
def step.no(
  fl: T.Fl,
  +cc: Char,
  n0: {Char.is_eq(cc, '0') == False{} : Bool},
  +nd: {Char.is_digit(cc) == False{} : Bool},
  +ndt: {Char.is_eq(cc, '.') == False{} : Bool},
  +ne: {T.wf.flo.is_e(cc) == False{} : Bool},
  ns: {Bool.or(Char.is_eq(cc, '+'), Char.is_eq(cc, '-')) == False{} : Bool}
) -> {T.wf.flo.step(fl, cc) == T.FlNo{} : T.Fl}:
  match fl:
    case T.FlStart{}:
      Equal.trans(T.Fl, T.wf.flo.step(T.FlStart{}, cc), Bool.pick(T.Fl, Char.is_digit(cc), T.FlInt{}, T.FlNo{}),
        T.FlNo{},
        Equal.cong(Bool, T.Fl, bb => Bool.pick(T.Fl, bb, T.FlZero{}, Bool.pick(T.Fl, Char.is_digit(cc), T.FlInt{},
          T.FlNo{})), Char.is_eq(cc, '0'), False{}, n0),
        Equal.cong(Bool, T.Fl, bb => Bool.pick(T.Fl, bb, T.FlInt{}, T.FlNo{}), Char.is_digit(cc), False{}, nd))
    case T.FlZero{}:
      tail.no(cc, ndt, ne)
    case T.FlInt{}:
      Equal.trans(T.Fl, T.wf.flo.step(T.FlInt{}, cc), T.wf.flo.tail(cc), T.FlNo{},
        Equal.cong(Bool, T.Fl, bb => Bool.pick(T.Fl, bb, T.FlInt{}, T.wf.flo.tail(cc)), Char.is_digit(cc), False{},
          nd), tail.no(cc, ndt, ne))
    case T.FlDot{}:
      Equal.cong(Bool, T.Fl, bb => Bool.pick(T.Fl, bb, T.FlFrac{}, T.FlNo{}), Char.is_digit(cc), False{}, nd)
    case T.FlFrac{}:
      Equal.trans(T.Fl, T.wf.flo.step(T.FlFrac{}, cc), Bool.pick(T.Fl, T.wf.flo.is_e(cc), T.FlE{}, T.FlNo{}),
        T.FlNo{},
        Equal.cong(Bool, T.Fl, bb => Bool.pick(T.Fl, bb, T.FlFrac{}, Bool.pick(T.Fl, T.wf.flo.is_e(cc), T.FlE{},
          T.FlNo{})), Char.is_digit(cc), False{}, nd),
        Equal.cong(Bool, T.Fl, bb => Bool.pick(T.Fl, bb, T.FlE{}, T.FlNo{}), T.wf.flo.is_e(cc), False{}, ne))
    case T.FlE{}:
      Equal.trans(T.Fl, T.wf.flo.step(T.FlE{}, cc), Bool.pick(T.Fl, Char.is_digit(cc), T.FlExp{}, T.FlNo{}),
        T.FlNo{},
        Equal.cong(Bool, T.Fl, bb => Bool.pick(T.Fl, bb, T.FlESign{}, Bool.pick(T.Fl, Char.is_digit(cc), T.FlExp{},
          T.FlNo{})), Bool.or(Char.is_eq(cc, '+'), Char.is_eq(cc, '-')), False{}, ns),
        Equal.cong(Bool, T.Fl, bb => Bool.pick(T.Fl, bb, T.FlExp{}, T.FlNo{}), Char.is_digit(cc), False{}, nd))
    case T.FlESign{}:
      Equal.cong(Bool, T.Fl, bb => Bool.pick(T.Fl, bb, T.FlExp{}, T.FlNo{}), Char.is_digit(cc), False{}, nd)
    case T.FlExp{}:
      Equal.cong(Bool, T.Fl, bb => Bool.pick(T.Fl, bb, T.FlExp{}, T.FlNo{}), Char.is_digit(cc), False{}, nd)
    case T.FlNo{}:
      {==}

# a live step reads a character of the float alphabet
def fch.go(
  fl: T.Fl,
  +cc: Char,
  bb: Bool,
  +eb: {fch(cc) == bb : Bool},
  hl: {fl.live(T.wf.flo.step(fl, cc)) == True{} : Bool}
) -> {fch(cc) == True{} : Bool}:
  match bb:
    case True{}:
      eb
    case False{}:
      +r1 = {Eq.or.right_false(Char.is_digit(cc), Bool.or(Char.is_eq(cc, '.'), Bool.or(Char.is_eq(cc, 'e'),
        Bool.or(Char.is_eq(cc, 'E'), Bool.or(Char.is_eq(cc, '+'), Char.is_eq(cc, '-'))))), eb)
        : {Bool.or(Char.is_eq(cc, '.'), Bool.or(Char.is_eq(cc, 'e'), Bool.or(Char.is_eq(cc, 'E'),
        Bool.or(Char.is_eq(cc, '+'), Char.is_eq(cc, '-'))))) == False{} : Bool}}
      +r2 = {Eq.or.right_false(Char.is_eq(cc, '.'), Bool.or(Char.is_eq(cc, 'e'), Bool.or(Char.is_eq(cc, 'E'),
        Bool.or(Char.is_eq(cc, '+'), Char.is_eq(cc, '-')))), r1)
        : {Bool.or(Char.is_eq(cc, 'e'), Bool.or(Char.is_eq(cc, 'E'), Bool.or(Char.is_eq(cc, '+'),
        Char.is_eq(cc, '-')))) == False{} : Bool}}
      +r3 = {Eq.or.right_false(Char.is_eq(cc, 'e'), Bool.or(Char.is_eq(cc, 'E'), Bool.or(Char.is_eq(cc, '+'),
        Char.is_eq(cc, '-'))), r2)
        : {Bool.or(Char.is_eq(cc, 'E'), Bool.or(Char.is_eq(cc, '+'), Char.is_eq(cc, '-'))) == False{} : Bool}}
      +nd = {Eq.or.left_false(Char.is_digit(cc), Bool.or(Char.is_eq(cc, '.'), Bool.or(Char.is_eq(cc, 'e'),
        Bool.or(Char.is_eq(cc, 'E'), Bool.or(Char.is_eq(cc, '+'), Char.is_eq(cc, '-'))))), eb)
        : {Char.is_digit(cc) == False{} : Bool}}
      +sn = {step.no(fl, cc, z0.go(cc, Char.is_eq(cc, '0'), {==}, nd), nd,
        Eq.or.left_false(Char.is_eq(cc, '.'), Bool.or(Char.is_eq(cc, 'e'), Bool.or(Char.is_eq(cc, 'E'),
          Bool.or(Char.is_eq(cc, '+'), Char.is_eq(cc, '-')))), r1),
        nie(cc, Eq.or.left_false(Char.is_eq(cc, 'e'), Bool.or(Char.is_eq(cc, 'E'), Bool.or(Char.is_eq(cc, '+'),
          Char.is_eq(cc, '-'))), r2), Eq.or.left_false(Char.is_eq(cc, 'E'), Bool.or(Char.is_eq(cc, '+'),
          Char.is_eq(cc, '-')), r3)),
        Eq.or.right_false(Char.is_eq(cc, 'E'), Bool.or(Char.is_eq(cc, '+'), Char.is_eq(cc, '-')), r3))
        : {T.wf.flo.step(fl, cc) == T.FlNo{} : T.Fl}}
      Eq.bit.absurd(&2, {fch(cc) == True{} : Bool}, Equal.trans(Bool, False{}, fl.live(T.wf.flo.step(fl, cc)),
        True{}, Equal.cong(T.Fl, Bool, ff => fl.live(ff), T.FlNo{}, T.wf.flo.step(fl, cc),
          Equal.sym(T.Fl, T.wf.flo.step(fl, cc), T.FlNo{}, sn)), hl))
# the bundle from FlStart, one character of the float alphabet at a time
def fb.start(
  +sg: T.Sign,
  +ds: List<&2, U32>,
  cc: Char,
  hf: {fch(cc) == True{} : Bool},
  hl: {fl.live(T.wf.flo.step(T.FlStart{}, cc)) == True{} : Bool}
) -> fb(T.FlStart{}, sg, ds, cc):
  fe.elim(zz => {fl.live(T.wf.flo.step(T.FlStart{}, zz)) == True{} : Bool} -> fb(T.FlStart{}, sg, ds, zz), cc, hf,
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    ll => Eq.bit.absurd(&1, fb(T.FlStart{}, sg, ds, '.'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlStart{}, sg, ds, 'e'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlStart{}, sg, ds, 'E'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlStart{}, sg, ds, '+'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlStart{}, sg, ds, '-'), ll))(hl)

# the bundle from FlZero, one character of the float alphabet at a time
def fb.zero(
  +sg: T.Sign,
  +ds: List<&2, U32>,
  cc: Char,
  hf: {fch(cc) == True{} : Bool},
  hl: {fl.live(T.wf.flo.step(T.FlZero{}, cc)) == True{} : Bool}
) -> fb(T.FlZero{}, sg, ds, cc):
  fe.elim(zz => {fl.live(T.wf.flo.step(T.FlZero{}, zz)) == True{} : Bool} -> fb(T.FlZero{}, sg, ds, zz), cc, hf,
    ll => Eq.bit.absurd(&1, fb(T.FlZero{}, sg, ds, '0'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlZero{}, sg, ds, '1'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlZero{}, sg, ds, '2'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlZero{}, sg, ds, '3'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlZero{}, sg, ds, '4'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlZero{}, sg, ds, '5'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlZero{}, sg, ds, '6'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlZero{}, sg, ds, '7'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlZero{}, sg, ds, '8'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlZero{}, sg, ds, '9'), ll),
    _l => {==},
    _l => {==},
    _l => {==},
    ll => Eq.bit.absurd(&1, fb(T.FlZero{}, sg, ds, '+'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlZero{}, sg, ds, '-'), ll))(hl)

# the bundle from FlInt, one character of the float alphabet at a time
def fb.int(
  +sg: T.Sign,
  +ds: List<&2, U32>,
  cc: Char,
  hf: {fch(cc) == True{} : Bool},
  hl: {fl.live(T.wf.flo.step(T.FlInt{}, cc)) == True{} : Bool}
) -> fb(T.FlInt{}, sg, ds, cc):
  fe.elim(zz => {fl.live(T.wf.flo.step(T.FlInt{}, zz)) == True{} : Bool} -> fb(T.FlInt{}, sg, ds, zz), cc, hf,
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    ll => Eq.bit.absurd(&1, fb(T.FlInt{}, sg, ds, '+'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlInt{}, sg, ds, '-'), ll))(hl)

# the bundle from FlDot, one character of the float alphabet at a time
def fb.dot(
  +sg: T.Sign,
  +ds: List<&2, U32>,
  cc: Char,
  hf: {fch(cc) == True{} : Bool},
  hl: {fl.live(T.wf.flo.step(T.FlDot{}, cc)) == True{} : Bool}
) -> fb(T.FlDot{}, sg, ds, cc):
  fe.elim(zz => {fl.live(T.wf.flo.step(T.FlDot{}, zz)) == True{} : Bool} -> fb(T.FlDot{}, sg, ds, zz), cc, hf,
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    ll => Eq.bit.absurd(&1, fb(T.FlDot{}, sg, ds, '.'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlDot{}, sg, ds, 'e'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlDot{}, sg, ds, 'E'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlDot{}, sg, ds, '+'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlDot{}, sg, ds, '-'), ll))(hl)

# the bundle from FlFrac, one character of the float alphabet at a time
def fb.frac(
  +sg: T.Sign,
  +ds: List<&2, U32>,
  cc: Char,
  hf: {fch(cc) == True{} : Bool},
  hl: {fl.live(T.wf.flo.step(T.FlFrac{}, cc)) == True{} : Bool}
) -> fb(T.FlFrac{}, sg, ds, cc):
  fe.elim(zz => {fl.live(T.wf.flo.step(T.FlFrac{}, zz)) == True{} : Bool} -> fb(T.FlFrac{}, sg, ds, zz), cc, hf,
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    ll => Eq.bit.absurd(&1, fb(T.FlFrac{}, sg, ds, '.'), ll),
    _l => {==},
    _l => {==},
    ll => Eq.bit.absurd(&1, fb(T.FlFrac{}, sg, ds, '+'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlFrac{}, sg, ds, '-'), ll))(hl)

# the bundle from FlE, one character of the float alphabet at a time
def fb.e(
  +sg: T.Sign,
  +ds: List<&2, U32>,
  cc: Char,
  hf: {fch(cc) == True{} : Bool},
  hl: {fl.live(T.wf.flo.step(T.FlE{}, cc)) == True{} : Bool}
) -> fb(T.FlE{}, sg, ds, cc):
  fe.elim(zz => {fl.live(T.wf.flo.step(T.FlE{}, zz)) == True{} : Bool} -> fb(T.FlE{}, sg, ds, zz), cc, hf,
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    ll => Eq.bit.absurd(&1, fb(T.FlE{}, sg, ds, '.'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlE{}, sg, ds, 'e'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlE{}, sg, ds, 'E'), ll),
    _l => {==},
    _l => {==})(hl)

# the bundle from FlESign, one character of the float alphabet at a time
def fb.esign(
  +sg: T.Sign,
  +ds: List<&2, U32>,
  cc: Char,
  hf: {fch(cc) == True{} : Bool},
  hl: {fl.live(T.wf.flo.step(T.FlESign{}, cc)) == True{} : Bool}
) -> fb(T.FlESign{}, sg, ds, cc):
  fe.elim(zz => {fl.live(T.wf.flo.step(T.FlESign{}, zz)) == True{} : Bool} -> fb(T.FlESign{}, sg, ds, zz), cc, hf,
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    ll => Eq.bit.absurd(&1, fb(T.FlESign{}, sg, ds, '.'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlESign{}, sg, ds, 'e'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlESign{}, sg, ds, 'E'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlESign{}, sg, ds, '+'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlESign{}, sg, ds, '-'), ll))(hl)

# the bundle from FlExp, one character of the float alphabet at a time
def fb.exp(
  +sg: T.Sign,
  +ds: List<&2, U32>,
  cc: Char,
  hf: {fch(cc) == True{} : Bool},
  hl: {fl.live(T.wf.flo.step(T.FlExp{}, cc)) == True{} : Bool}
) -> fb(T.FlExp{}, sg, ds, cc):
  fe.elim(zz => {fl.live(T.wf.flo.step(T.FlExp{}, zz)) == True{} : Bool} -> fb(T.FlExp{}, sg, ds, zz), cc, hf,
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    _l => {==},
    ll => Eq.bit.absurd(&1, fb(T.FlExp{}, sg, ds, '.'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlExp{}, sg, ds, 'e'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlExp{}, sg, ds, 'E'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlExp{}, sg, ds, '+'), ll),
    ll => Eq.bit.absurd(&1, fb(T.FlExp{}, sg, ds, '-'), ll))(hl)

# the bundle for every state and every character of a live step
def fb.at(
  fl: T.Fl,
  +sg: T.Sign,
  +ds: List<&2, U32>,
  +cc: Char,
  +hl: {fl.live(T.wf.flo.step(fl, cc)) == True{} : Bool}
) -> fb(fl, sg, ds, cc):
  match fl:
    case T.FlStart{}:
      fb.start(sg, ds, cc, fch.go(T.FlStart{}, cc, fch(cc), {==}, hl), hl)
    case T.FlZero{}:
      fb.zero(sg, ds, cc, fch.go(T.FlZero{}, cc, fch(cc), {==}, hl), hl)
    case T.FlInt{}:
      fb.int(sg, ds, cc, fch.go(T.FlInt{}, cc, fch(cc), {==}, hl), hl)
    case T.FlDot{}:
      fb.dot(sg, ds, cc, fch.go(T.FlDot{}, cc, fch(cc), {==}, hl), hl)
    case T.FlFrac{}:
      fb.frac(sg, ds, cc, fch.go(T.FlFrac{}, cc, fch(cc), {==}, hl), hl)
    case T.FlE{}:
      fb.e(sg, ds, cc, fch.go(T.FlE{}, cc, fch(cc), {==}, hl), hl)
    case T.FlESign{}:
      fb.esign(sg, ds, cc, fch.go(T.FlESign{}, cc, fch(cc), {==}, hl), hl)
    case T.FlExp{}:
      fb.exp(sg, ds, cc, fch.go(T.FlExp{}, cc, fch(cc), {==}, hl), hl)
    case T.FlNo{}:
      Eq.bit.absurd(&1, fb(T.FlNo{}, sg, ds, cc), hl)

# a walk from the dead state stays there
def go.no(cs: List<&2, Char>) -> {T.wf.flo.go(cs, T.FlNo{}) == T.FlNo{} : T.Fl}:
  match cs:
    case []:
      {==}
    case _c <> tt:
      go.no(tt)

# a walk that ends accepting starts from a live state
def live.of(
  fl: T.Fl,
  cs: List<&2, Char>,
  hh: {T.wf.flo.end(T.wf.flo.go(cs, fl)) == True{} : Bool}
) -> {fl.live(fl) == True{} : Bool}:
  match fl:
    case T.FlNo{}:
      Eq.bit.absurd(&2, {False{} == True{} : Bool}, Equal.trans(Bool, False{},
        T.wf.flo.end(T.wf.flo.go(cs, T.FlNo{})), True{},
        Equal.cong(T.Fl, Bool, ff => T.wf.flo.end(ff), T.FlNo{}, T.wf.flo.go(cs, T.FlNo{}),
          Equal.sym(T.Fl, T.wf.flo.go(cs, T.FlNo{}), T.FlNo{}, go.no(cs))), hh))
    case T.FlStart{}:
      {==}
    case T.FlZero{}:
      {==}
    case T.FlInt{}:
      {==}
    case T.FlDot{}:
      {==}
    case T.FlFrac{}:
      {==}
    case T.FlE{}:
      {==}
    case T.FlESign{}:
      {==}
    case T.FlExp{}:
      {==}

# the facts of a step on a walk that ends accepting
def ffacts(
  +fl: T.Fl,
  +cc: Char,
  tt: List<&2, Char>,
  hh: {T.wf.flo.end(T.wf.flo.go(tt, T.wf.flo.step(fl, cc))) == True{} : Bool}
) -> {fl.facts(fl, cc) == True{} : Bool}:
  Equal.cong(Fs, Bool, fs => fs.b(fs),
    Fs{T.num.step(nm(fl, T.Plus{}, []), cc), fl.facts(fl, cc)},
    Fs{nm(T.wf.flo.step(fl, cc), T.Plus{}, T.dec.go(nm.ds(fl, []), 10, T.dig.val(cc))), True{}},
    fb.at(fl, T.Plus{}, [], cc, live.of(T.wf.flo.step(fl, cc), tt, hh)))

# the numeral scan walks a float's spelling as the automaton does
def fw.num(
  cs: List<&2, Char>,
  +fl: T.Fl,
  +sg: T.Sign,
  +ds: List<&2, U32>,
  +hh: {T.wf.flo.end(T.wf.flo.go(cs, fl)) == True{} : Bool}
) -> {T.num.go(cs, nm(fl, sg, ds)) == nm(T.wf.flo.go(cs, fl), sg, nds(cs, fl, ds)) : T.Num}:
  match cs:
    case []:
      {==}
    case +cc <> +tt:
      Equal.trans(T.Num, T.num.go(tt, T.num.step(nm(fl, sg, ds), cc)),
        T.num.go(tt, nm(T.wf.flo.step(fl, cc), sg, T.dec.go(nm.ds(fl, ds), 10, T.dig.val(cc)))),
        nm(T.wf.flo.go(tt, T.wf.flo.step(fl, cc)), sg, nds(tt, T.wf.flo.step(fl, cc),
          T.dec.go(nm.ds(fl, ds), 10, T.dig.val(cc)))),
        Equal.cong(T.Num, T.Num, nn => T.num.go(tt, nn), T.num.step(nm(fl, sg, ds), cc),
          nm(T.wf.flo.step(fl, cc), sg, T.dec.go(nm.ds(fl, ds), 10, T.dig.val(cc))),
          Equal.cong(Fs, T.Num, fs => fs.n(fs), Fs{T.num.step(nm(fl, sg, ds), cc), fl.facts(fl, cc)},
            Fs{nm(T.wf.flo.step(fl, cc), sg, T.dec.go(nm.ds(fl, ds), 10, T.dig.val(cc))), True{}},
            fb.at(fl, sg, ds, cc, live.of(T.wf.flo.step(fl, cc), tt, hh)))),
        fw.num(tt, T.wf.flo.step(fl, cc), sg, T.dec.go(nm.ds(fl, ds), 10, T.dig.val(cc)), hh))

# a float's spelling is characters a bare value keeps
def fw.rest(
  tt: String,
  +fl: T.Fl,
  +hh: {T.wf.flo.end(T.wf.flo.go(String.to_list(tt), fl)) == True{} : Bool}
) -> {Laws.word.rest(tt) == True{} : Bool}:
  match tt:
    case SNil{}:
      {==}
    case SCon{+cc, +ts}:
      and.tt(Laws.word.char(cc), Laws.word.rest(ts), Eq.and.left(Laws.word.char(cc), fa2(fl, cc),
        ffacts(fl, cc, String.to_list(ts), hh)), fw.rest(ts, T.wf.flo.step(fl, cc), hh))

# a float's spelling holds no underscore, so its body is itself
def fw.body(
  cs: List<&2, Char>,
  +fl: T.Fl,
  +out: List<&2, Char>,
  +hh: {T.wf.flo.end(T.wf.flo.go(cs, fl)) == True{} : Bool}
) -> {T.word.body.go(cs, False{}, out) == List.reverse.go(&2, Char, out, cs) : List<&2, Char>}:
  match cs:
    case []:
      {==}
    case +cc <> +tt:
      +f2 = {Eq.and.right(Laws.word.char(cc), fa2(fl, cc), ffacts(fl, cc, tt, hh)) : {fa2(fl, cc) == True{} : Bool}}
      Equal.trans(List<&2, Char>, T.word.body.go(tt, False{}, T.word.body.put.us(Char.is_eq(cc, '_'), cc, out)),
        T.word.body.go(tt, False{}, cc <> out), List.reverse.go(&2, Char, cc <> out, tt),
        Equal.cong(Bool, List<&2, Char>, bb => T.word.body.go(tt, False{}, T.word.body.put.us(bb, cc, out)),
          Char.is_eq(cc, '_'), False{}, Eq.not.true(Char.is_eq(cc, '_'), Eq.and.left(Bool.not(Char.is_eq(cc, '_')),
          fa3(fl, cc), f2))),
        fw.body(tt, T.wf.flo.step(fl, cc), cc <> out, hh))

# a float's spelling holds no colon
def fw.colon(
  cs: List<&2, Char>,
  +fl: T.Fl,
  +hh: {T.wf.flo.end(T.wf.flo.go(cs, fl)) == True{} : Bool}
) -> {T.word.colon(cs) == False{} : Bool}:
  match cs:
    case []:
      {==}
    case +cc <> +tt:
      +f3 = {Eq.and.right(Bool.not(Char.is_eq(cc, '_')), fa3(fl, cc), Eq.and.right(Laws.word.char(cc), fa2(fl, cc),
        ffacts(fl, cc, tt, hh))) : {fa3(fl, cc) == True{} : Bool}}
      Equal.trans(Bool, T.word.or(Char.is_eq(cc, ':'), T.word.colon(tt)), T.word.or(False{}, T.word.colon(tt)),
        False{},
        Equal.cong(Bool, Bool, bb => T.word.or(bb, T.word.colon(tt)), Char.is_eq(cc, ':'), False{},
          Eq.not.true(Char.is_eq(cc, ':'), Eq.and.left(Bool.not(Char.is_eq(cc, ':')), fa4(fl, cc), f3))),
        fw.colon(tt, T.wf.flo.step(fl, cc), hh))

# the left flag of a word.or that answered False
def wor.l(aa: Bool, bb: Bool, ee: {T.word.or(aa, bb) == False{} : Bool}) -> {aa == False{} : Bool}:
  match aa:
    case True{}:
      ee
    case False{}:
      {==}

# and the right one
def wor.r(aa: Bool, bb: Bool, ee: {T.word.or(aa, bb) == False{} : Bool}) -> {bb == False{} : Bool}:
  match aa:
    case True{}:
      Eq.bit.absurd2(&2, {bb == False{} : Bool}, ee)
    case False{}:
      ee

# a character that is no minus is no dash, first or not
def dhit(
  ff: Bool,
  cc: Char,
  hm: {Char.is_eq(cc, '-') == False{} : Bool}
) -> {T.word.dash.hit(ff, cc) == False{} : Bool}:
  match ff:
    case True{}:
      {==}
    case False{}:
      hm

# before the exponent, a spelling with no exponent mark holds no minus, and
# its walk stays before the exponent
def fw.dash(
  cs: List<&2, Char>,
  +fl: T.Fl,
  ff: Bool,
  +hh: {T.wf.flo.end(T.wf.flo.go(cs, fl)) == True{} : Bool},
  +hp: {fl.pre(fl) == True{} : Bool},
  +he: {T.word.ee(cs) == False{} : Bool}
) -> {T.word.dash(cs, ff) == False{} : Bool}:
  match cs:
    case []:
      {==}
    case +cc <> +tt:
      +f4 = {Eq.and.right(Bool.not(Char.is_eq(cc, ':')), fa4(fl, cc), Eq.and.right(Bool.not(Char.is_eq(cc, '_')),
        fa3(fl, cc), Eq.and.right(Laws.word.char(cc), fa2(fl, cc), ffacts(fl, cc, tt, hh))))
        : {fa4(fl, cc) == True{} : Bool}}
      +f5 = {Eq.and.right(Bool.not(Bool.and(fl.pre(fl), Char.is_eq(cc, '-'))), fa5(fl, cc), f4)
        : {fa5(fl, cc) == True{} : Bool}}
      +hx = {wor.l(T.word.ee.hit(cc), T.word.ee(tt), he) : {T.word.ee.hit(cc) == False{} : Bool}}
      +hm = {Equal.trans(Bool, Char.is_eq(cc, '-'), Bool.and(fl.pre(fl), Char.is_eq(cc, '-')), False{},
        Equal.cong(Bool, Bool, bb => Bool.and(bb, Char.is_eq(cc, '-')), True{}, fl.pre(fl),
          Equal.sym(Bool, fl.pre(fl), True{}, hp)),
        Eq.not.true(Bool.and(fl.pre(fl), Char.is_eq(cc, '-')), Eq.and.left(Bool.not(Bool.and(fl.pre(fl),
          Char.is_eq(cc, '-'))), fa5(fl, cc), f4))) : {Char.is_eq(cc, '-') == False{} : Bool}}
      +hq = {Equal.trans(Bool, fl.pre(T.wf.flo.step(fl, cc)), Bool.and(fl.pre(fl), Bool.not(T.word.ee.hit(cc))),
        True{},
        beq.eq(fl.pre(T.wf.flo.step(fl, cc)), Bool.and(fl.pre(fl), Bool.not(T.word.ee.hit(cc))),
          Eq.and.right(Bool.or(Bool.not(fl.start(fl)), Char.is_digit(cc)), fa6(fl, cc), f5)),
        Equal.trans(Bool, Bool.and(fl.pre(fl), Bool.not(T.word.ee.hit(cc))),
          Bool.and(True{}, Bool.not(T.word.ee.hit(cc))), True{},
          Equal.cong(Bool, Bool, bb => Bool.and(bb, Bool.not(T.word.ee.hit(cc))), fl.pre(fl), True{}, hp),
          Equal.cong(Bool, Bool, bb => Bool.and(True{}, Bool.not(bb)), T.word.ee.hit(cc), False{}, hx)))
        : {fl.pre(T.wf.flo.step(fl, cc)) == True{} : Bool}}
      Equal.trans(Bool, T.word.or(T.word.dash.hit(ff, cc), T.word.dash(tt, False{})),
        T.word.or(False{}, T.word.dash(tt, False{})), False{},
        Equal.cong(Bool, Bool, bb => T.word.or(bb, T.word.dash(tt, False{})), T.word.dash.hit(ff, cc), False{},
          dhit(ff, cc, hm)),
        fw.dash(tt, T.wf.flo.step(fl, cc), False{}, hh, hq, wor.r(T.word.ee.hit(cc), T.word.ee(tt), he)))

# a finished walk that accepts is a float, spelled by the body of the word
def fin.end(
  fl: T.Fl,
  +sg: T.Sign,
  ds: List<&2, U32>,
  cs: List<&2, Char>,
  hh: {T.wf.flo.end(fl) == True{} : Bool}
) -> {T.num.fin(nm(fl, sg, ds), cs) == T.GotVal{T.VFlo{sg, T.word.body(cs)}} : T.Got}:
  match fl:
    case T.FlFrac{}:
      {==}
    case T.FlExp{}:
      {==}
    case T.FlStart{}:
      Eq.bit.absurd(&2, {T.num.fin(nm(T.FlStart{}, sg, ds), cs) == T.GotVal{T.VFlo{sg, T.word.body(cs)}} : T.Got}, hh)
    case T.FlZero{}:
      Eq.bit.absurd(&2, {T.num.fin(nm(T.FlZero{}, sg, ds), cs) == T.GotVal{T.VFlo{sg, T.word.body(cs)}} : T.Got}, hh)
    case T.FlInt{}:
      Eq.bit.absurd(&2, {T.num.fin(nm(T.FlInt{}, sg, ds), cs) == T.GotVal{T.VFlo{sg, T.word.body(cs)}} : T.Got}, hh)
    case T.FlDot{}:
      Eq.bit.absurd(&2, {T.num.fin(nm(T.FlDot{}, sg, ds), cs) == T.GotVal{T.VFlo{sg, T.word.body(cs)}} : T.Got}, hh)
    case T.FlE{}:
      Eq.bit.absurd(&2, {T.num.fin(nm(T.FlE{}, sg, ds), cs) == T.GotVal{T.VFlo{sg, T.word.body(cs)}} : T.Got}, hh)
    case T.FlESign{}:
      Eq.bit.absurd(&2, {T.num.fin(nm(T.FlESign{}, sg, ds), cs) == T.GotVal{T.VFlo{sg, T.word.body(cs)}} : T.Got},
        hh)
    case T.FlNo{}:
      Eq.bit.absurd(&2, {T.num.fin(nm(T.FlNo{}, sg, ds), cs) == T.GotVal{T.VFlo{sg, T.word.body(cs)}} : T.Got}, hh)

# a word the datetime route could take only by a dash in its exponent: an
# exponent mark keeps it a numeral, and with none it has no dash
def flo.route(
  +cs: List<&2, Char>,
  ex: Bool,
  eex: {T.word.ee(cs) == ex : Bool},
  hc: {T.word.colon(cs) == False{} : Bool},
  hd: {T.word.ee(cs) == False{} : Bool} -> {T.word.dash(cs, True{}) == False{} : Bool}
) -> {T.word.route(T.GotBad{""}, T.word.or(T.word.colon(cs), T.word.dash(cs, True{})), cs) == T.word.num(cs)
  : T.Got}:
  match ex:
    case True{}:
      %Equal.sym(Bool, T.word.ee(cs), True{}, eex) :
        {T.word.route.date(T.word.as_date(T.word.or(T.word.colon(cs), T.word.dash(cs, True{})), _), cs)
          == T.word.num(cs) : T.Got}
      {==}
    case False{}:
      route.num(cs, hc, hd(eex))

# a digit is no sign
def dg.nosign(
  cc: Char,
  hc: {Char.is_digit(cc) == True{} : Bool}
) -> {Bool.or(Char.is_eq(cc, '+'), Char.is_eq(cc, '-')) == False{} : Bool}:
  dg.elim(zz => {Bool.or(Char.is_eq(zz, '+'), Char.is_eq(zz, '-')) == False{} : Bool}, cc, hc,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# after a minus, a digit is read as the first character of an unsigned
# numeral with the minus kept
def sign.skip(
  cc: Char,
  hc: {Char.is_digit(cc) == True{} : Bool}
) -> {T.num.step(T.Num{T.NSign{}, T.Minus{}, 10, [], False{}, False{}, ""}, cc)
  == T.num.step(nm(T.FlStart{}, T.Minus{}, []), cc) : T.Num}:
  dg.elim(zz => {T.num.step(T.Num{T.NSign{}, T.Minus{}, 10, [], False{}, False{}, ""}, zz)
    == T.num.step(nm(T.FlStart{}, T.Minus{}, []), zz) : T.Num}, cc, hc,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# what flo_word claims
def flo.Goal(+sg: T.Sign, +text: String) -> Type:
  {T.word.val(String.to_list(T.render.atom(T.VFlo{sg, text}))) == T.GotVal{T.VFlo{sg, text}} : T.Got}

# a float's spelling starts with a digit
def fl.dig(
  +hh: Char,
  tt: String,
  hw: {T.wf.flo.end(T.wf.flo.go(hh <> String.to_list(tt), T.FlStart{})) == True{} : Bool}
) -> {Char.is_digit(hh) == True{} : Bool}:
  Eq.and.left(Char.is_digit(hh), fa6(T.FlStart{}, hh), Eq.and.right(Bool.not(Bool.and(True{},
    Char.is_eq(hh, '-'))), fa5(T.FlStart{}, hh), Eq.and.right(Bool.not(Char.is_eq(hh, ':')), fa4(T.FlStart{}, hh),
    Eq.and.right(Bool.not(Char.is_eq(hh, '_')), fa3(T.FlStart{}, hh), Eq.and.right(Laws.word.char(hh),
    fa2(T.FlStart{}, hh), ffacts(T.FlStart{}, hh, String.to_list(tt), hw))))))

# a positive float spelled by the automaton
def flo.plus(
  +hh: Char,
  +tt: String,
  +hw: {T.wf.flo.end(T.wf.flo.go(hh <> String.to_list(tt), T.FlStart{})) == True{} : Bool}
) -> flo.Goal(T.Plus{}, SCon{hh, tt}):
  +hd = {fl.dig(hh, tt, hw) : {Char.is_digit(hh) == True{} : Bool}}
  +cs = {hh <> String.to_list(tt) : List<&2, Char>}
  Equal.trans(T.Got, T.word.val.pick(T.word.special(hh), cs), T.word.val.pick(False{}, cs),
    T.GotVal{T.VFlo{T.Plus{}, SCon{hh, tt}}},
    Equal.cong(Bool, T.Got, bb => T.word.val.pick(bb, cs), T.word.special(hh), False{}, dg.nospec(hh, hd)),
    Equal.trans(T.Got, T.word.route(T.GotBad{""}, T.word.or(T.word.colon(cs), T.word.dash(cs, True{})), cs),
      T.word.num(cs), T.GotVal{T.VFlo{T.Plus{}, SCon{hh, tt}}},
      flo.route(cs, T.word.ee(cs), {==}, fw.colon(cs, T.FlStart{}, hw),
        ee => fw.dash(cs, T.FlStart{}, True{}, hw, {==}, ee)),
      Equal.trans(T.Got, T.num.fin(T.num.go(cs, nm(T.FlStart{}, T.Plus{}, [])), cs),
        T.num.fin(nm(T.wf.flo.go(cs, T.FlStart{}), T.Plus{}, nds(cs, T.FlStart{}, [])), cs),
        T.GotVal{T.VFlo{T.Plus{}, SCon{hh, tt}}},
        Equal.cong(T.Num, T.Got, nn => T.num.fin(nn, cs), T.num.go(cs, nm(T.FlStart{}, T.Plus{}, [])),
          nm(T.wf.flo.go(cs, T.FlStart{}), T.Plus{}, nds(cs, T.FlStart{}, [])),
          fw.num(cs, T.FlStart{}, T.Plus{}, [], hw)),
        Equal.trans(T.Got, T.num.fin(nm(T.wf.flo.go(cs, T.FlStart{}), T.Plus{}, nds(cs, T.FlStart{}, [])), cs),
          T.GotVal{T.VFlo{T.Plus{}, T.word.body(cs)}}, T.GotVal{T.VFlo{T.Plus{}, SCon{hh, tt}}},
          fin.end(T.wf.flo.go(cs, T.FlStart{}), T.Plus{}, nds(cs, T.FlStart{}, []), cs, hw),
          Equal.cong(String, T.Got, ss => T.GotVal{T.VFlo{T.Plus{}, ss}}, T.word.body(cs), SCon{hh, tt},
            Equal.trans(String, String.from_list(T.word.body.go(String.to_list(tt), False{},
              T.word.body.put.sign(Bool.or(Char.is_eq(hh, '+'), Char.is_eq(hh, '-')), hh, []))),
              String.from_list(T.word.body.go(String.to_list(tt), False{}, [hh])), SCon{hh, tt},
              Equal.cong(Bool, String, bb => String.from_list(T.word.body.go(String.to_list(tt), False{},
                T.word.body.put.sign(bb, hh, []))), Bool.or(Char.is_eq(hh, '+'), Char.is_eq(hh, '-')), False{},
                dg.nosign(hh, hd)),
              Equal.trans(String, String.from_list(T.word.body.go(String.to_list(tt), False{}, [hh])),
                String.from_list(hh <> String.to_list(tt)), SCon{hh, tt},
                Equal.cong(List<&2, Char>, String, ls => String.from_list(ls),
                  T.word.body.go(String.to_list(tt), False{}, [hh]), hh <> String.to_list(tt),
                  fw.body(String.to_list(tt), T.wf.flo.step(T.FlStart{}, hh), [hh], hw)),
                ftl(SCon{hh, tt}))))))))

# a negative float spelled by the automaton: the minus makes the word a
# special candidate, which it is not, and the scan keeps the minus as the sign
def flo.minus(
  +hh: Char,
  +tt: String,
  +hw: {T.wf.flo.end(T.wf.flo.go(hh <> String.to_list(tt), T.FlStart{})) == True{} : Bool}
) -> flo.Goal(T.Minus{}, SCon{hh, tt}):
  +hd = {fl.dig(hh, tt, hw) : {Char.is_digit(hh) == True{} : Bool}}
  +cs = {hh <> String.to_list(tt) : List<&2, Char>}
  Equal.trans(T.Got, T.word.route(T.word.spec(String.from_list('-' <> cs)),
    T.word.or(T.word.colon('-' <> cs), T.word.dash('-' <> cs, True{})), '-' <> cs),
    T.word.route(T.GotBad{""}, T.word.or(T.word.colon('-' <> cs), T.word.dash('-' <> cs, True{})), '-' <> cs),
    T.GotVal{T.VFlo{T.Minus{}, SCon{hh, tt}}},
    Equal.cong(T.Got, T.Got, gg => T.word.route(gg, T.word.or(T.word.colon('-' <> cs),
      T.word.dash('-' <> cs, True{})), '-' <> cs), T.word.spec(String.from_list('-' <> cs)), T.GotBad{""},
      spec.m(hh, String.to_list(tt), dg.noi(hh, hd), dg.non(hh, hd))),
    Equal.trans(T.Got, T.word.route(T.GotBad{""}, T.word.or(T.word.colon('-' <> cs), T.word.dash('-' <> cs,
      True{})), '-' <> cs), T.word.num('-' <> cs), T.GotVal{T.VFlo{T.Minus{}, SCon{hh, tt}}},
      flo.route('-' <> cs, T.word.ee(cs), {==}, fw.colon(cs, T.FlStart{}, hw),
        ee => fw.dash(cs, T.FlStart{}, False{}, hw, {==}, ee)),
      Equal.trans(T.Got, T.num.fin(T.num.go(String.to_list(tt), T.num.step(T.Num{T.NSign{}, T.Minus{}, 10, [],
        False{}, False{}, ""}, hh)), '-' <> cs),
        T.num.fin(nm(T.wf.flo.go(cs, T.FlStart{}), T.Minus{}, nds(cs, T.FlStart{}, [])), '-' <> cs),
        T.GotVal{T.VFlo{T.Minus{}, SCon{hh, tt}}},
        Equal.cong(T.Num, T.Got, nn => T.num.fin(nn, '-' <> cs),
          T.num.go(String.to_list(tt), T.num.step(T.Num{T.NSign{}, T.Minus{}, 10, [], False{}, False{}, ""}, hh)),
          nm(T.wf.flo.go(cs, T.FlStart{}), T.Minus{}, nds(cs, T.FlStart{}, [])),
          Equal.trans(T.Num,
            T.num.go(String.to_list(tt), T.num.step(T.Num{T.NSign{}, T.Minus{}, 10, [], False{}, False{}, ""}, hh)),
            T.num.go(cs, nm(T.FlStart{}, T.Minus{}, [])),
            nm(T.wf.flo.go(cs, T.FlStart{}), T.Minus{}, nds(cs, T.FlStart{}, [])),
            Equal.cong(T.Num, T.Num, nn => T.num.go(String.to_list(tt), nn),
              T.num.step(T.Num{T.NSign{}, T.Minus{}, 10, [], False{}, False{}, ""}, hh),
              T.num.step(nm(T.FlStart{}, T.Minus{}, []), hh), sign.skip(hh, hd)),
            fw.num(cs, T.FlStart{}, T.Minus{}, [], hw))),
        Equal.trans(T.Got, T.num.fin(nm(T.wf.flo.go(cs, T.FlStart{}), T.Minus{}, nds(cs, T.FlStart{}, [])),
          '-' <> cs),
          T.GotVal{T.VFlo{T.Minus{}, T.word.body('-' <> cs)}}, T.GotVal{T.VFlo{T.Minus{}, SCon{hh, tt}}},
          fin.end(T.wf.flo.go(cs, T.FlStart{}), T.Minus{}, nds(cs, T.FlStart{}, []), '-' <> cs, hw),
          Equal.cong(String, T.Got, ss => T.GotVal{T.VFlo{T.Minus{}, ss}}, T.word.body('-' <> cs), SCon{hh, tt},
            Equal.trans(String, String.from_list(T.word.body.go(cs, False{}, [])), String.from_list(cs),
              SCon{hh, tt},
              Equal.cong(List<&2, Char>, String, ls => String.from_list(ls), T.word.body.go(cs, False{}, []), cs,
                fw.body(cs, T.FlStart{}, [], hw)),
              ftl(SCon{hh, tt})))))))


# a spelling the automaton accepts, with its first character, by the sign
def flo.auto.sg(
  +sg: T.Sign,
  +hh: Char,
  +tt: String,
  +hw: {T.wf.flo.end(T.wf.flo.go(hh <> String.to_list(tt), T.FlStart{})) == True{} : Bool}
) -> flo.Goal(sg, SCon{hh, tt}):
  match sg:
    case T.Plus{}:
      flo.plus(hh, tt, hw)
    case T.Minus{}:
      flo.minus(hh, tt, hw)

# a spelling the automaton accepts
def flo.auto(
  text: String,
  +sg: T.Sign,
  +hw: {T.wf.flo.end(T.wf.flo.go(String.to_list(text), T.FlStart{})) == True{} : Bool}
) -> flo.Goal(sg, text):
  match text:
    case SNil{}:
      Eq.bit.absurd(&1, flo.Goal(sg, SNil{}), hw)
    case SCon{+hh, +tt}:
      flo.auto.sg(sg, hh, tt, hw)

# inf or nan
def flo.name(aa: Bool) -> String:
  match aa:
    case True{}:
      "inf"
    case False{}:
      "nan"

# inf and nan, by the sign
def flo.fixed(+sg: T.Sign, aa: Bool) -> flo.Goal(sg, flo.name(aa)):
  match sg:
    case T.Plus{}:
      match aa:
        case True{}:
          {==}
        case False{}:
          {==}
    case T.Minus{}:
      match aa:
        case True{}:
          {==}
        case False{}:
          {==}

# a well-formed float: inf, nan, or a spelling the automaton accepts
def flo.spec(
  +sg: T.Sign,
  +text: String,
  aa: Bool,
  ea: {T.str.eq(text, "inf") == aa : Bool},
  bb: Bool,
  eb: {T.str.eq(text, "nan") == bb : Bool},
  +hw: {Bool.or(aa, Bool.or(bb, T.wf.flo.end(T.wf.flo.go(String.to_list(text), T.FlStart{})))) == True{} : Bool}
) -> flo.Goal(sg, text):
  match aa:
    case True{}:
      %Equal.sym(String, text, "inf", str.eq.true(text, "inf", ea)) : flo.Goal(sg, _)
      flo.fixed(sg, True{})
    case False{}:
      match bb:
        case True{}:
          %Equal.sym(String, text, "nan", str.eq.true(text, "nan", eb)) : flo.Goal(sg, _)
          flo.fixed(sg, False{})
        case False{}:
          flo.auto(text, sg, hw)

def Laws.flo_word(sg, text, w):
  flo.spec(sg, text, T.str.eq(text, "inf"), {==}, T.str.eq(text, "nan"), {==}, w)

# what flo.chars claims
def flo.Chars(+sg: T.Sign, +text: String) -> Type:
  {Laws.word.chars(T.render.atom(T.VFlo{sg, text})) == True{} : Bool}

# a spelling the automaton accepts is a bare value, by the sign
def flo.chars.sg(
  +sg: T.Sign,
  +hh: Char,
  +tt: String,
  +hw: {T.wf.flo.end(T.wf.flo.go(hh <> String.to_list(tt), T.FlStart{})) == True{} : Bool}
) -> flo.Chars(sg, SCon{hh, tt}):
  match sg:
    case T.Plus{}:
      and.tt(Laws.word.first(hh), Laws.word.rest(tt), dg.first(hh, fl.dig(hh, tt, hw)),
        fw.rest(tt, T.wf.flo.step(T.FlStart{}, hh), hw))
    case T.Minus{}:
      and.tt(Laws.word.first('-'), Laws.word.rest(SCon{hh, tt}), {==}, fw.rest(SCon{hh, tt}, T.FlStart{}, hw))

# a spelling the automaton accepts is a bare value
def flo.chars.auto(
  text: String,
  +sg: T.Sign,
  +hw: {T.wf.flo.end(T.wf.flo.go(String.to_list(text), T.FlStart{})) == True{} : Bool}
) -> flo.Chars(sg, text):
  match text:
    case SNil{}:
      Eq.bit.absurd(&1, flo.Chars(sg, SNil{}), hw)
    case SCon{+hh, +tt}:
      flo.chars.sg(sg, hh, tt, hw)

# inf and nan are bare values, with either sign
def flo.chars.fixed(+sg: T.Sign, aa: Bool) -> flo.Chars(sg, flo.name(aa)):
  match sg:
    case T.Plus{}:
      match aa:
        case True{}:
          {==}
        case False{}:
          {==}
    case T.Minus{}:
      match aa:
        case True{}:
          {==}
        case False{}:
          {==}

# a well-formed float is a bare value
def flo.chars(
  +sg: T.Sign,
  +text: String,
  aa: Bool,
  ea: {T.str.eq(text, "inf") == aa : Bool},
  bb: Bool,
  eb: {T.str.eq(text, "nan") == bb : Bool},
  +hw: {Bool.or(aa, Bool.or(bb, T.wf.flo.end(T.wf.flo.go(String.to_list(text), T.FlStart{})))) == True{} : Bool}
) -> flo.Chars(sg, text):
  match aa:
    case True{}:
      %Equal.sym(String, text, "inf", str.eq.true(text, "inf", ea)) : flo.Chars(sg, _)
      flo.chars.fixed(sg, True{})
    case False{}:
      match bb:
        case True{}:
          %Equal.sym(String, text, "nan", str.eq.true(text, "nan", eb)) : flo.Chars(sg, _)
          flo.chars.fixed(sg, False{})
        case False{}:
          flo.chars.auto(text, sg, hw)

def Laws.flo_reads_back(sg, text, w, fx, rest):
  Laws.word_reads_back(T.VFlo{sg, text}, T.render.atom(T.VFlo{sg, text}),
    flo.chars(sg, text, T.str.eq(text, "inf"), {==}, T.str.eq(text, "nan"), {==}, w), Laws.flo_word(sg, text, w),
    fx, rest)
