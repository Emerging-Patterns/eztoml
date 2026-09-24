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
