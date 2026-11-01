import Base
import ../main.bend as T
import ./defs/AbnfGrammar.bend as D1
import ./defs/BareValueGrammar.bend as D2
import ./defs/DerivationReplay.bend as D3
import ./defs/GrammarDerivations.bend as D4

# WP-A, keyvals. The scanner keeps a string as a span of the text where the
# replay holds its characters, so a document with keyvals is compared as
# own reads it.

# LAW: the accept direction: every short derivation of the grammar parses,
# with its strings read out (own), to its replay. For every derivation of
# toml.abnf's toml rule with the prose's restrictions (g.ok) whose text is
# shorter than 2^32 characters, with keyvals of every spelling (dotted or
# not, each key segment bare, basic or literal, at the root, after a header
# or in an inline table), values of every kind (strings of the four forms,
# booleans, date-times, floats, integers, and arrays and inline tables
# nested to any depth, with blank space, comments and newlines anywhere
# ws-comment-newline allows them in an array, and a trailing comma), table
# headers and blank lines in any order, joined by LF or CRLF, parse gives
# what the expressions' walks give in text order: each value put at its
# key's path in the table its lines are in, a word word.val refuses setting
# the error, the first error kept, and the rows sealed
law text_reads_as_replay:
  for +d: D4.Gd
  for +ok: {D1.g.ok(d) == True{} : Bool}
  for +es: {D2.short(D4.g.text(d)) == True{} : Bool}
  {D2.own(T.parse(D4.g.text(d))) == D3.replay(d) : T.Doc}
