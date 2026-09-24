# eztoml: the laws. Each law carries the SPEC.md row it proves, or proves part
# of, on its own comment line. PROOF.bend fills them; `bend PROOF.bend` is
# the gate.
import Base
import ./main.bend as T

# LAW: a pair at the head of a table's rows is what get finds for its name
# TOML-GET-1
law get_first:
  for +name: String
  for +v: T.Val
  for rest: List<&2, T.Val>
  {T.get(T.VPair{name, v} <> rest, name) == T.Found{v} : T.Hit}

# LAW: an empty key is not bare
# TOML-KEY-1
law bare_needs_a_char:
  for +s: String
  for e: {True{} == String.is_empty(s) : Bool}
  {T.bare(s) == False{} : Bool}

# LAW: a bare key is written as itself
# TOML-KEY-2
law key_is_bare_when_it_can:
  for +s: String
  for e: {True{} == T.bare(s) : Bool}
  {T.key(s) == s : String}

# LAW: a key that is not bare is written as a basic string
# TOML-KEY-2
law key_is_quoted_when_it_must:
  for +s: String
  for e: {False{} == T.bare(s) : Bool}
  {T.key(s) == T.key.basic(s) : String}

# LAW: string reads the text of an owned string value
# TOML-READ-1
law string_of:
  for text: String
  {T.string(T.VStr{text}) == text : String}
