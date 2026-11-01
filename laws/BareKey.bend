# `bare(s)` holds exactly when `s` is nonempty and every character of `s` is
# an ASCII letter, an ASCII digit, `_` or `-` (toml.abnf `unquoted-key`)
import Base
import ../main.bend as T
import ./defs/BareValueGrammar.bend as D1

# LAW: an empty key is not bare
law bare_needs_a_char:
  for +s: String
  for e: {True{} == String.is_empty(s) : Bool}
  {T.bare(s) == False{} : Bool}

# LAW: a key is bare exactly when it matches toml.abnf's unquoted-key
law bare_is_unquoted_key:
  for +s: String
  {T.bare(s) == D1.abnf.unquoted_key(s) : Bool}
