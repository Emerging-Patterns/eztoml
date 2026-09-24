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

# The other controls. A code point below 32 has zeros above its five low bits,
# so the thirty-two of them can be taken one at a time; U+007F is one more.

# a word of n zero bits
def zw(nn: Nat) -> Word(nn):
  match nn:
    case 0n:
      WNil{}
    case 1n+pp:
      WCon{False{}, zw(pp)}

# against a 0 bit, a word is below exactly when the bits above are
def lt_fin_f(cc: Cmp, aa: Bool) -> {Cmp.is_lt(Word.cmp.fin(aa, False{}, cc)) == Cmp.is_lt(cc) : Bool}:
  match cc:
    case LT{}:
      {==}
    case GT{}:
      {==}
    case EQ{}:
      match aa:
        case False{}:
          {==}
        case True{}:
          {==}

# a word is never below zero
def zw_nlt(nn: Nat, ww: Word(nn)) -> {Cmp.is_lt(Word.cmp(nn, ww, zw(nn))) == False{} : Bool}:
  match nn:
    case 0n:
      match ww:
        case WNil{}:
          {==}
    case 1n+(+pp):
      match ww:
        case WCon{bb, +tt}:
          Equal.trans(Bool, Cmp.is_lt(Word.cmp.fin(bb, False{}, Word.cmp(pp, tt, zw(pp)))),
            Cmp.is_lt(Word.cmp(pp, tt, zw(pp))), False{}, lt_fin_f(Word.cmp(pp, tt, zw(pp)), bb), zw_nlt(pp, tt))

# below a word whose low bit is 0, the bits above are below
def lt_up(
  aa: Bool,
  cc: Cmp,
  h_lt: {Cmp.is_lt(Word.cmp.fin(aa, False{}, cc)) == True{} : Bool}
) -> {Cmp.is_lt(cc) == True{} : Bool}:
  Equal.trans(Bool, Cmp.is_lt(cc), Cmp.is_lt(Word.cmp.fin(aa, False{}, cc)), True{},
    Equal.sym(Bool, Cmp.is_lt(Word.cmp.fin(aa, False{}, cc)), Cmp.is_lt(cc), lt_fin_f(cc, aa)), h_lt)

# what esc_ctl says of a code point
def ctl.eq(+uu: U32) -> Type:
  {Laws.esc(Chr{uu}) == "\\u00" ++ String.from_list([Laws.char_at(Laws.hex_lower(), U32.to_nat(U32.div(uu, 16))),
    Laws.char_at(Laws.hex_lower(), U32.to_nat(U32.mod(uu, 16)))]) : String}

# and with its other hypotheses first
def ctl.goal(+uu: U32) -> Type:
  {Chr{uu} != '\u{8}' : Char} -> {Chr{uu} != '\t' : Char} -> {Chr{uu} != '\n' : Char} ->
    {Chr{uu} != '\u{c}' : Char} -> {Chr{uu} != '\r' : Char} -> ctl.eq(uu)

# the controls below U+0020, one at a time: the five with short escapes are
# ruled out by their hypotheses, and the others compute
def ctl5(
  b0: Bool,
  b1: Bool,
  b2: Bool,
  b3: Bool,
  b4: Bool
) -> ctl.goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{False{}, zw(26n)}}}}}}}):
  match b0 b1 b2 b3 b4:
    case False{} False{} False{} False{} False{}:
      _hb => _ht => _hn => _hf => _hr => {==}
    case True{} False{} False{} False{} False{}:
      _hb => _ht => _hn => _hf => _hr => {==}
    case False{} True{} False{} False{} False{}:
      _hb => _ht => _hn => _hf => _hr => {==}
    case True{} True{} False{} False{} False{}:
      _hb => _ht => _hn => _hf => _hr => {==}
    case False{} False{} True{} False{} False{}:
      _hb => _ht => _hn => _hf => _hr => {==}
    case True{} False{} True{} False{} False{}:
      _hb => _ht => _hn => _hf => _hr => {==}
    case False{} True{} True{} False{} False{}:
      _hb => _ht => _hn => _hf => _hr => {==}
    case True{} True{} True{} False{} False{}:
      _hb => _ht => _hn => _hf => _hr => {==}
    case False{} False{} False{} True{} False{}:
      hb => _ht => _hn => _hf => _hr =>
        Eq.bit.gone(&1, ctl.eq(U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{},
          zw(26n)}}}}}}}), hb({==}))
    case True{} False{} False{} True{} False{}:
      _hb => ht => _hn => _hf => _hr =>
        Eq.bit.gone(&1, ctl.eq(U32{WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{},
          zw(26n)}}}}}}}), ht({==}))
    case False{} True{} False{} True{} False{}:
      _hb => _ht => hn => _hf => _hr =>
        Eq.bit.gone(&1, ctl.eq(U32{WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{},
          zw(26n)}}}}}}}), hn({==}))
    case True{} True{} False{} True{} False{}:
      _hb => _ht => _hn => _hf => _hr => {==}
    case False{} False{} True{} True{} False{}:
      _hb => _ht => _hn => hf => _hr =>
        Eq.bit.gone(&1, ctl.eq(U32{WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{},
          zw(26n)}}}}}}}), hf({==}))
    case True{} False{} True{} True{} False{}:
      _hb => _ht => _hn => _hf => hr =>
        Eq.bit.gone(&1, ctl.eq(U32{WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{},
          zw(26n)}}}}}}}), hr({==}))
    case False{} True{} True{} True{} False{}:
      _hb => _ht => _hn => _hf => _hr => {==}
    case True{} True{} True{} True{} False{}:
      _hb => _ht => _hn => _hf => _hr => {==}
    case False{} False{} False{} False{} True{}:
      _hb => _ht => _hn => _hf => _hr => {==}
    case True{} False{} False{} False{} True{}:
      _hb => _ht => _hn => _hf => _hr => {==}
    case False{} True{} False{} False{} True{}:
      _hb => _ht => _hn => _hf => _hr => {==}
    case True{} True{} False{} False{} True{}:
      _hb => _ht => _hn => _hf => _hr => {==}
    case False{} False{} True{} False{} True{}:
      _hb => _ht => _hn => _hf => _hr => {==}
    case True{} False{} True{} False{} True{}:
      _hb => _ht => _hn => _hf => _hr => {==}
    case False{} True{} True{} False{} True{}:
      _hb => _ht => _hn => _hf => _hr => {==}
    case True{} True{} True{} False{} True{}:
      _hb => _ht => _hn => _hf => _hr => {==}
    case False{} False{} False{} True{} True{}:
      _hb => _ht => _hn => _hf => _hr => {==}
    case True{} False{} False{} True{} True{}:
      _hb => _ht => _hn => _hf => _hr => {==}
    case False{} True{} False{} True{} True{}:
      _hb => _ht => _hn => _hf => _hr => {==}
    case True{} True{} False{} True{} True{}:
      _hb => _ht => _hn => _hf => _hr => {==}
    case False{} False{} True{} True{} True{}:
      _hb => _ht => _hn => _hf => _hr => {==}
    case True{} False{} True{} True{} True{}:
      _hb => _ht => _hn => _hf => _hr => {==}
    case False{} True{} True{} True{} True{}:
      _hb => _ht => _hn => _hf => _hr => {==}
    case True{} True{} True{} True{} True{}:
      _hb => _ht => _hn => _hf => _hr => {==}

# the bits above the fifth are zero and the fifth is 0, else the code point
# is not below 32
def ctl.at(
  cc: Cmp,
  b5: Bool,
  +b0: Bool,
  +b1: Bool,
  +b2: Bool,
  +b3: Bool,
  +b4: Bool,
  +rest: Word(26n),
  ec: {Word.cmp(26n, rest, zw(26n)) == cc : Cmp},
  h_lt: {Cmp.is_lt(Word.cmp.fin(b5, True{}, cc)) == True{} : Bool}
) -> ctl.goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}}):
  match cc:
    case LT{}:
      Eq.bit.gone(&1, ctl.goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}}),
        Eq.bit.clash2(Equal.trans(Bool, True{}, Cmp.is_lt(Word.cmp(26n, rest, zw(26n))), False{},
          Equal.sym(Bool, Cmp.is_lt(Word.cmp(26n, rest, zw(26n))), True{},
            Equal.cong(Cmp, Bool, xx => Cmp.is_lt(xx), Word.cmp(26n, rest, zw(26n)), LT{}, ec)),
          zw_nlt(26n, rest))))
    case GT{}:
      match b5:
        case False{}:
          Eq.bit.absurd(&1, ctl.goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{False{}, rest}}}}}}}),
            h_lt)
        case True{}:
          Eq.bit.absurd(&1, ctl.goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{True{}, rest}}}}}}}),
            h_lt)
    case EQ{}:
      match b5:
        case True{}:
          Eq.bit.absurd(&1, ctl.goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{True{}, rest}}}}}}}),
            h_lt)
        case False{}:
          er = Equal.sym(Word(26n), rest, zw(26n), Eq.word_eq(26n, rest, zw(26n), ec))
          %er : ctl.goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{False{}, _}}}}}}})
          ctl5(b0, b1, b2, b3, b4)

# a control below U+0020
def ctl.lt(
  uu: U32,
  h_lt: {U32.is_lt(uu, 32) == True{} : Bool}
) -> ctl.goal(uu):
  match uu:
    case U32{WCon{+b0, WCon{+b1, WCon{+b2, WCon{+b3, WCon{+b4, WCon{+b5, +rest}}}}}}}:
      +c5 = Word.cmp.fin(b5, True{}, Word.cmp(26n, rest, zw(26n)))
      +c4 = Word.cmp.fin(b4, False{}, c5)
      +c3 = Word.cmp.fin(b3, False{}, c4)
      +c2 = Word.cmp.fin(b2, False{}, c3)
      +c1 = Word.cmp.fin(b1, False{}, c2)
      h5 = lt_up(b4, c5, lt_up(b3, c4, lt_up(b2, c3, lt_up(b1, c2, lt_up(b0, c1, h_lt)))))
      ctl.at(Word.cmp(26n, rest, zw(26n)), b5, b0, b1, b2, b3, b4, rest, {==}, h5)

# U+007F
def ctl.del(
  +uu: U32,
  ee: {U32.is_eq(uu, 127) == True{} : Bool}
) -> ctl.goal(uu):
  eu = Equal.cong(Char, U32, cc => Char.to_u32(cc), Chr{uu}, Chr{127}, Eq.u32_eq(uu, 127, ee))
  %Equal.sym(U32, uu, 127, eu) : ctl.goal(_)
  _hb => _ht => _hn => _hf => _hr => {==}

# a control is below U+0020 or is U+007F
def ctl.split(
  +uu: U32,
  lt: Bool,
  eq: Bool,
  elt: {U32.is_lt(uu, 32) == lt : Bool},
  eeq: {U32.is_eq(uu, 127) == eq : Bool},
  eo: {Bool.or(lt, eq) == True{} : Bool}
) -> ctl.goal(uu):
  match lt:
    case True{}:
      ctl.lt(uu, elt)
    case False{}:
      match eq:
        case True{}:
          ctl.del(uu, eeq)
        case False{}:
          Eq.bit.absurd(&1, ctl.goal(uu), eo)

# every other control is \u00 and two lowercase hex digits
def Laws.esc_ctl(c, h_c, h_b, h_t, h_n, h_f, h_r):
  match c:
    case Chr{+uu}:
      ctl.split(uu, U32.is_lt(uu, 32), U32.is_eq(uu, 127), {==}, {==}, h_c)(h_b, h_t, h_n, h_f, h_r)

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
