# `key(s)` is `s` when `bare(s)`; otherwise it is a basic string, and for
# every `s` of Unicode scalar values, `parse(key(s) ++ " = 1")` has no error
# and one pair, named `s`
import Base
import ../main.bend as T

# LAW: a bare key is written as itself
law key_is_bare_when_it_can:
  for +s: String
  for e: {True{} == T.bare(s) : Bool}
  {T.key(s) == s : String}

# LAW: a key that is not bare is written as a basic string
law key_is_quoted_when_it_must:
  for +s: String
  for e: {False{} == T.bare(s) : Bool}
  {T.key(s) == T.key.basic(s) : String}

# laws/KeyRendersAndReadsBack.bend's read-back. key writes a name bare, or as a basic string; the
# scanner reads either back as the name's characters.

# LAW: a key reads back as its name: for every string s, key(s) followed by
# " = 1" parses with no error to one pair, named s, holding the integer 1
law key_reads_back:
  for +s: String
  {T.parse(String.append(T.key(s), " = 1"))
    == T.Doc{"", [T.VPair{s, T.VInt{T.Plus{}, "1"}}]} : T.Doc}
