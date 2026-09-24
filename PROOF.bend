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
