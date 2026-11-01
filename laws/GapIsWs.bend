import Base
import ./defs/AbnfWhitespace.bend as D1
import ./defs/BlankAndControlChars.bend as D2

# Basic facts of the transcription (WP-G).

# LAW: laws/KeyNameIsItsCharacters.bend's blank space, spaces and tabs, is ws
law gap_is_ws:
  for +gs: List<&2, Bool>
  {D1.abnf.ws(D2.gap(gs)) == True{} : Bool}
