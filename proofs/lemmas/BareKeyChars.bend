# a bare key's characters are exactly the unquoted-key characters
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/BareKey.bend as L1
import ../../laws/defs/BareValueGrammar.bend as D1

# laws/BareKey.bend. The code asks Base's ASCII classes and then `_` and `-`; the
# ABNF lists `-` before `_`, which is the one place the two read differently.

# a character the code lets into a bare key is one the ABNF does
def bare.at.abnf(
  cc: Char
) -> {T.bare.at(cc) == D1.abnf.unquoted_key_char(cc) : Bool}:
  match cc:
    case Chr{+cp}:
      Equal.cong(Bool, Bool,
        y => Bool.or(D1.abnf.alpha(cp), Bool.or(D1.abnf.digit(cp), y)),
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
  == D1.abnf.all_unquoted_key_chars(ss) : Bool}:
  match ss:
    case SNil{}:
      {==}
    case SCon{+hh, +tt}:
      Equal.trans(Bool,
        T.bare.all.step(T.bare.at(hh), _u => T.bare.all(String.to_list(tt))),
        Bool.and(T.bare.at(hh), T.bare.all(String.to_list(tt))),
        Bool.and(D1.abnf.unquoted_key_char(hh),
          D1.abnf.all_unquoted_key_chars(tt)),
        bare.step.and(T.bare.at(hh), T.bare.all(String.to_list(tt))),
        Equal.trans(Bool,
          Bool.and(T.bare.at(hh), T.bare.all(String.to_list(tt))),
          Bool.and(D1.abnf.unquoted_key_char(hh),
            T.bare.all(String.to_list(tt))),
          Bool.and(D1.abnf.unquoted_key_char(hh),
            D1.abnf.all_unquoted_key_chars(tt)),
          Equal.cong(Bool, Bool,
            y => Bool.and(y, T.bare.all(String.to_list(tt))),
            T.bare.at(hh), D1.abnf.unquoted_key_char(hh), bare.at.abnf(hh)),
          Equal.cong(Bool, Bool,
            y => Bool.and(D1.abnf.unquoted_key_char(hh), y),
            T.bare.all(String.to_list(tt)),
            D1.abnf.all_unquoted_key_chars(tt), bare.all.abnf(tt))))

# the empty string is neither, and a nonempty one is its walk on both sides
def L1.bare_is_unquoted_key(s):
  match s:
    case SNil{}:
      {==}
    case SCon{+hh, +tt}:
      bare.all.abnf(SCon{hh, tt})
