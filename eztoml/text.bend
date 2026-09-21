# eztoml/text: keys and basic strings. A bare key is letters, digits, `_`
# and `-`. `segments` splits a dotted name on unquoted dots. `quote` writes a
# basic string. `key` writes a name bare when it can.
import Base

# what a header's next character is: the quoting toggles, an unquoted dot
# cuts, anything else is kept
type Sym is Data:
  SQuote{}
  SDot{}
  SKeep{c: Char}

# a header being cut apart: `quoted` is true inside quotes, `cur` is the
# segment being gathered and `out` the finished ones, both reversed
type Split is Data:
  Split{quoted: Bool, cur: List<&2, Char>, out: List<&2, String>}

# a header char classified
def seg.sym(+c: Char) -> Sym:
  Bool.pick(Sym, Char.is_eq(c, '"'), SQuote{},
    Bool.pick(Sym, Char.is_eq(c, '.'), SDot{}, SKeep{c}))

# the segment gathered so far, in order
def seg.done(cur: List<&2, Char>) -> String:
  String.from_list(List.reverse(&2, Char, cur))

# a dot inside quotes is part of the segment; outside, it ends one
def seg.dot(quoted: Bool, cur: List<&2, Char>, out: List<&2, String>) -> Split:
  match quoted:
    case True{}:
      Split{True{}, '.' <> cur, out}
    case False{}:
      Split{False{}, [], seg.done(cur) <> out}

# the state once a char has been classified
def seg.go(st: Split, s: Sym) -> Split:
  Split{quoted, cur, out} = st
  match s:
    case SQuote{}:
      Split{Bool.not(quoted), cur, out}
    case SDot{}:
      seg.dot(quoted, cur, out)
    case SKeep{c}:
      Split{quoted, c <> cur, out}

# one char of a header against the state
def seg.step(st: Split, c: Char) -> Split:
  seg.go(st, seg.sym(c))

# the segment still being gathered, closed, and the rest put back in order
def seg.fin(st: Split) -> List<&2, String>:
  Split{_quoted, cur, out} = st
  List.reverse(&2, String, seg.done(cur) <> out)

# the walk one char at a time
def seg.walk(cs: List<&2, Char>, st: Split) -> Split:
  match cs:
    case []:
      st
    case h <> t:
      seg.walk(t, seg.step(st, h))

# a header's segments, unquoted
def segments(s: String) -> List<&2, String>:
  seg.fin(seg.walk(String.to_list(s), Split{False{}, [], []}))

# one hex digit
def hex.dig(+d: U32) -> Char:
  Bool.pick(Char, U32.is_lt(d, 10), Char.from_u32((d + 48 : U32)),
    Char.from_u32((d + 87 : U32)))

# four hex digits of a code point
def hex.four(+x: U32) -> String:
  String.from_list([
    hex.dig(U32.div(x, 4096)),
    hex.dig(U32.mod(U32.div(x, 256), 16)),
    hex.dig(U32.mod(U32.div(x, 16), 16)),
    hex.dig(U32.mod(x, 16))])

# a char inside a basic string
def quote.char(+c: Char) -> String:
  +x = Char.to_u32(c)
  Bool.pick(String, U32.is_eq(x, 34), "\\\"",
  Bool.pick(String, U32.is_eq(x, 92), "\\\\",
  Bool.pick(String, U32.is_eq(x, 10), "\\n",
  Bool.pick(String, U32.is_eq(x, 13), "\\r",
  Bool.pick(String, U32.is_eq(x, 9), "\\t",
  Bool.pick(String, U32.is_eq(x, 8), "\\b",
  Bool.pick(String, U32.is_eq(x, 12), "\\f",
  Bool.pick(String, Bool.or(U32.is_lt(x, 32), U32.is_eq(x, 127)),
    "\\u" ++ hex.four(x), String.from_list([c])))))))))

# the chars of a basic string, escaped
def quote.chars(cs: List<&2, Char>) -> String:
  match cs:
    case []:
      ""
    case +h <> t:
      quote.char(h) ++ quote.chars(t)

# a basic string in quotes
def quote(+s: String) -> String:
  "\"" ++ quote.chars(String.to_list(s)) ++ "\""

# a char a bare key may hold
def bare.at(+c: Char) -> Bool:
  Bool.or(Char.is_alpha(c), Bool.or(Char.is_digit(c),
    Bool.or(Char.is_eq(c, '_'), Char.is_eq(c, '-'))))

# one step of the walk, with the head's answer in hand
def bare.all.step(here: Bool, rest: Unit -> Bool) -> Bool:
  match here:
    case True{}:
      rest(Unit{})
    case False{}:
      False{}

# whether every char of a key is one a bare key may hold
def bare.all(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      True{}
    case +h <> t:
      bare.all.step(bare.at(h), _u => bare.all(t))

# whether a key can be written without quotes
def bare(+s: String) -> Bool:
  Bool.and(Bool.not(String.is_empty(s)), bare.all(String.to_list(s)))

# a key, once it is known whether it can be bare
def key.pick(ok: Bool, +s: String, quoted: Unit -> String) -> String:
  match ok:
    case True{}:
      s
    case False{}:
      quoted(Unit{})

# a key as it is written: bare when it can be, quoted when it must be
def key(+s: String) -> String:
  key.pick(bare(s), s, _u => quote(s))
