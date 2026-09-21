# eztoml/lex: TOML text to tokens, one character at a time.
import Base

# a token. A newline is kept; a comment is not.
type Tok is Data:
  TStr{s: String}
  TBare{s: String}
  TLBr{}
  TRBr{}
  TLBc{}
  TRBc{}
  TComma{}
  TEq{}
  TDot{}
  TNl{}
  TBad{why: String}

# what a character is outside a string
type Class is Data:
  CSp{}
  CNl{}
  CCr{}
  CHash{}
  CQuote{}
  CApos{}
  CSlash{}
  CBr{}
  CKet{}
  CBc{}
  CBe{}
  CComma{}
  CEq{}
  CDot{}
  CWord{}

# where the lexer is
type Mode is Data:
  Idle{}
  Word{}
  Comment{}
  Cr{}
  Q1{}
  Q2{}
  A1{}
  A2{}
  Str{}
  Esc{}
  Lit{}
  Uni{left: Nat, acc: U32, ml: Bool}
  MlDrop{}
  MlDropCr{}
  Ml{}
  Ml1{}
  Ml2{}
  MlEsc{}
  MlEscCr{}
  MlTrim{}
  ADrop{}
  ADropCr{}
  ALit{}
  ALit1{}
  ALit2{}

# the lexer: buf and toks are both reversed
type Lex is Data:
  Lex{mode: Mode, buf: List<&2, Char>, toks: List<&2, Tok>}

# a character's class, by code point
def lex.classify(+x: U32) -> Class:
  Bool.pick(Class, U32.is_eq(x, 32), CSp{},
  Bool.pick(Class, U32.is_eq(x, 9), CSp{},
  Bool.pick(Class, U32.is_eq(x, 10), CNl{},
  Bool.pick(Class, U32.is_eq(x, 13), CCr{},
  Bool.pick(Class, U32.is_eq(x, 35), CHash{},
  Bool.pick(Class, U32.is_eq(x, 34), CQuote{},
  Bool.pick(Class, U32.is_eq(x, 39), CApos{},
  Bool.pick(Class, U32.is_eq(x, 92), CSlash{},
  Bool.pick(Class, U32.is_eq(x, 91), CBr{},
  Bool.pick(Class, U32.is_eq(x, 93), CKet{},
  Bool.pick(Class, U32.is_eq(x, 123), CBc{},
  Bool.pick(Class, U32.is_eq(x, 125), CBe{},
  Bool.pick(Class, U32.is_eq(x, 44), CComma{},
  Bool.pick(Class, U32.is_eq(x, 61), CEq{},
  Bool.pick(Class, U32.is_eq(x, 46), CDot{},
    CWord{})))))))))))))))

# the buffered characters, in order
def lex.text(buf: List<&2, Char>) -> String:
  String.from_list(List.reverse(&2, Char, buf))

# a code point that a basic string may not hold raw
def lex.bad_basic(+x: U32) -> Bool:
  Bool.and(Bool.not(U32.is_eq(x, 9)),
    Bool.or(U32.is_lt(x, 32), U32.is_eq(x, 127)))

# a code point that a multiline string may not hold raw
def lex.bad_multi(+x: U32) -> Bool:
  Bool.and(Bool.not(U32.is_eq(x, 9)),
    Bool.and(Bool.not(U32.is_eq(x, 10)),
      Bool.and(Bool.not(U32.is_eq(x, 13)),
        Bool.or(U32.is_lt(x, 32), U32.is_eq(x, 127)))))

# a hex digit, or nothing
def lex.hex(+x: U32) -> Maybe<&2, U32>:
  Bool.pick(Maybe<&2, U32>, Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57)),
    Some{(x - 48 : U32)},
  Bool.pick(Maybe<&2, U32>, Bool.and(U32.is_ge(x, 97), U32.is_le(x, 102)),
    Some{(x - 87 : U32)},
  Bool.pick(Maybe<&2, U32>, Bool.and(U32.is_ge(x, 65), U32.is_le(x, 70)),
    Some{(x - 55 : U32)}, None{})))

# whether a code point is a unicode scalar value
def lex.scalar(+x: U32) -> Bool:
  Bool.and(Bool.not(U32.is_gt(x, 1114111)),
    Bool.not(Bool.and(U32.is_ge(x, 55296), U32.is_le(x, 57343))))

# the mode a string returns to
def lex.str_mode(ml: Bool) -> Mode:
  match ml:
    case True{}:
      Ml{}
    case False{}:
      Str{}

# an escape in a basic or multiline string
def lex.escaped(+x: U32) -> Maybe<&2, Char>:
  Bool.pick(Maybe<&2, Char>, U32.is_eq(x, 110), Some{Char.from_u32(10)},
  Bool.pick(Maybe<&2, Char>, U32.is_eq(x, 114), Some{Char.from_u32(13)},
  Bool.pick(Maybe<&2, Char>, U32.is_eq(x, 116), Some{Char.from_u32(9)},
  Bool.pick(Maybe<&2, Char>, U32.is_eq(x, 98), Some{Char.from_u32(8)},
  Bool.pick(Maybe<&2, Char>, U32.is_eq(x, 102), Some{Char.from_u32(12)},
  Bool.pick(Maybe<&2, Char>, U32.is_eq(x, 34), Some{Char.from_u32(34)},
  Bool.pick(Maybe<&2, Char>, U32.is_eq(x, 92), Some{Char.from_u32(92)},
    None{})))))))

# one token in front of the rest
def lex.emit(t: Tok, toks: List<&2, Tok>) -> List<&2, Tok>:
  t <> toks

# a finished bare word
def lex.emit_word(buf: List<&2, Char>, toks: List<&2, Tok>) -> List<&2, Tok>:
  lex.emit(TBare{lex.text(buf)}, toks)

# a finished string
def lex.emit_str(buf: List<&2, Char>, toks: List<&2, Tok>) -> List<&2, Tok>:
  lex.emit(TStr{lex.text(buf)}, toks)

# idle, once the character's class is known
def lex.idle(cls: Class, +c: Char, toks: List<&2, Tok>) -> Lex:
  match cls:
    case CSp{}:
      Lex{Idle{}, [], toks}
    case CNl{}:
      Lex{Idle{}, [], lex.emit(TNl{}, toks)}
    case CCr{}:
      Lex{Cr{}, [], lex.emit(TNl{}, toks)}
    case CHash{}:
      Lex{Comment{}, [], toks}
    case CQuote{}:
      Lex{Q1{}, [], toks}
    case CApos{}:
      Lex{A1{}, [], toks}
    case CSlash{}:
      Lex{Idle{}, [], lex.emit(TBad{"backslash"}, toks)}
    case CBr{}:
      Lex{Idle{}, [], lex.emit(TLBr{}, toks)}
    case CKet{}:
      Lex{Idle{}, [], lex.emit(TRBr{}, toks)}
    case CBc{}:
      Lex{Idle{}, [], lex.emit(TLBc{}, toks)}
    case CBe{}:
      Lex{Idle{}, [], lex.emit(TRBc{}, toks)}
    case CComma{}:
      Lex{Idle{}, [], lex.emit(TComma{}, toks)}
    case CEq{}:
      Lex{Idle{}, [], lex.emit(TEq{}, toks)}
    case CDot{}:
      Lex{Idle{}, [], lex.emit(TDot{}, toks)}
    case CWord{}:
      Lex{Word{}, [c], toks}

# a word, once the next character's class is known
def lex.word(cls: Class, +c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match cls:
    case CWord{}:
      Lex{Word{}, c <> buf, toks}
    case CSp{}:
      Lex{Idle{}, [], lex.emit_word(buf, toks)}
    case CNl{}:
      Lex{Idle{}, [], lex.emit(TNl{}, lex.emit_word(buf, toks))}
    case CCr{}:
      Lex{Cr{}, [], lex.emit(TNl{}, lex.emit_word(buf, toks))}
    case CHash{}:
      Lex{Comment{}, [], lex.emit_word(buf, toks)}
    case other:
      lex.idle(cls, c, lex.emit_word(buf, toks))

# one more quote that belongs to the string, then the character
def lex.push_quotes(n: Nat, buf: List<&2, Char>) -> List<&2, Char>:
  match n:
    case 0n:
      buf
    case 1n+p:
      lex.push_quotes(p, Char.from_u32(34) <> buf)

# one more apostrophe that belongs to the string, then the character
def lex.push_apos(n: Nat, buf: List<&2, Char>) -> List<&2, Char>:
  match n:
    case 0n:
      buf
    case 1n+p:
      lex.push_apos(p, Char.from_u32(39) <> buf)

# a raw control character, or the character kept
def lex.keep(bad: Bool, mode: Mode, +c: Char, buf: List<&2, Char>,
  toks: List<&2, Tok>) -> Lex:
  match bad:
    case True{}:
      Lex{Idle{}, [], lex.emit(TBad{"control"}, toks)}
    case False{}:
      Lex{mode, c <> buf, toks}

# a basic string character
def lex.str_char(+c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  lex.keep(lex.bad_basic(Char.to_u32(c)), Str{}, c, buf, toks)

# a multiline body character
def lex.ml_char(+c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  lex.keep(lex.bad_multi(Char.to_u32(c)), Ml{}, c, buf, toks)

# a literal string character
def lex.lit_char(+c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  lex.keep(lex.bad_basic(Char.to_u32(c)), Lit{}, c, buf, toks)

# a multiline literal character
def lex.alit_char(+c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  lex.keep(lex.bad_multi(Char.to_u32(c)), ALit{}, c, buf, toks)

# the last hex digit closes the escape
def lex.uni_end(ok: Bool, acc: U32, buf: List<&2, Char>, toks: List<&2, Tok>,
  ml: Bool) -> Lex:
  match ok:
    case True{}:
      Lex{lex.str_mode(ml), Char.from_u32(acc) <> buf, toks}
    case False{}:
      Lex{Idle{}, [], lex.emit(TBad{"unicode"}, toks)}

# the hex digit just consumed, when some digits remain or this was the last
def lex.uni.at(p: Nat, +acc: U32, buf: List<&2, Char>, toks: List<&2, Tok>,
  ml: Bool) -> Lex:
  match p:
    case 0n:
      lex.uni_end(lex.scalar(acc), acc, buf, toks, ml)
    case 1n+_q:
      Lex{Uni{p, acc, ml}, buf, toks}

# one hex digit, with the new accumulator
def lex.uni.go(left: Nat, +acc: U32, buf: List<&2, Char>, toks: List<&2, Tok>,
  ml: Bool) -> Lex:
  match left:
    case 0n:
      Lex{Idle{}, [], lex.emit(TBad{"unicode"}, toks)}
    case 1n+p:
      lex.uni.at(p, acc, buf, toks, ml)

# one hex digit of a unicode escape, once the digit is known
def lex.uni.dig(m: Maybe<&2, U32>, left: Nat, acc: U32, buf: List<&2, Char>,
  toks: List<&2, Tok>, ml: Bool) -> Lex:
  match m:
    case None{}:
      Lex{Idle{}, [], lex.emit(TBad{"unicode"}, toks)}
    case Some{d}:
      lex.uni.go(left, (acc * 16 + d : U32), buf, toks, ml)

# one hex digit of a unicode escape
def lex.uni(left: Nat, acc: U32, +x: U32, buf: List<&2, Char>,
  toks: List<&2, Tok>, ml: Bool) -> Lex:
  lex.uni.dig(lex.hex(x), left, acc, buf, toks, ml)

# a short escape's character
def lex.esc.char(m: Maybe<&2, Char>, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match m:
    case Some{ch}:
      Lex{Str{}, ch <> buf, toks}
    case None{}:
      Lex{Idle{}, [], lex.emit(TBad{"escape"}, toks)}

# a `\U`, or a short escape
def lex.esc.u(big: Bool, +x: U32, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match big:
    case True{}:
      Lex{Uni{8n, 0, False{}}, buf, toks}
    case False{}:
      lex.esc.char(lex.escaped(x), buf, toks)

# a `\u`, or the other escapes
def lex.esc.go(small: Bool, +x: U32, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match small:
    case True{}:
      Lex{Uni{4n, 0, False{}}, buf, toks}
    case False{}:
      lex.esc.u(U32.is_eq(x, 85), x, buf, toks)

# a backslash's follower in a basic string
def lex.esc(+x: U32, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  lex.esc.go(U32.is_eq(x, 117), x, buf, toks)

# a short multiline escape
def lex.ml_esc.char(m: Maybe<&2, Char>, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match m:
    case Some{ch}:
      Lex{Ml{}, ch <> buf, toks}
    case None{}:
      Lex{Idle{}, [], lex.emit(TBad{"escape"}, toks)}

# a multiline `\U` or a short escape
def lex.ml_esc.big(big: Bool, +x: U32, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match big:
    case True{}:
      Lex{Uni{8n, 0, True{}}, buf, toks}
    case False{}:
      lex.ml_esc.char(lex.escaped(x), buf, toks)

# a multiline `\u` or `\U` or short escape
def lex.ml_esc.u(small: Bool, +x: U32, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match small:
    case True{}:
      Lex{Uni{4n, 0, True{}}, buf, toks}
    case False{}:
      lex.ml_esc.big(U32.is_eq(x, 85), x, buf, toks)

# a carriage return after a multiline backslash, or another escape
def lex.ml_esc.cr(cr: Bool, +x: U32, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match cr:
    case True{}:
      Lex{MlEscCr{}, buf, toks}
    case False{}:
      lex.ml_esc.u(U32.is_eq(x, 117), x, buf, toks)

# a newline after a multiline backslash, or another escape
def lex.ml_esc.go(nl: Bool, +x: U32, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match nl:
    case True{}:
      Lex{MlTrim{}, buf, toks}
    case False{}:
      lex.ml_esc.cr(U32.is_eq(x, 13), x, buf, toks)

# a backslash's follower in a multiline string
def lex.ml_esc(+x: U32, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  lex.ml_esc.go(U32.is_eq(x, 10), x, buf, toks)

# whitespace skipped after a line-ending backslash
def lex.trimming(+x: U32) -> Bool:
  Bool.or(U32.is_eq(x, 32), Bool.or(U32.is_eq(x, 9),
    Bool.or(U32.is_eq(x, 10), U32.is_eq(x, 13))))

# a backslash or a body character
def lex.ml.sl(sl: Bool, +c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match sl:
    case True{}:
      Lex{MlEsc{}, buf, toks}
    case False{}:
      lex.ml_char(c, buf, toks)

# a quote, or a body character
def lex.ml.go(q: Bool, +c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match q:
    case True{}:
      Lex{Ml1{}, buf, toks}
    case False{}:
      lex.ml.sl(U32.is_eq(Char.to_u32(c), 92), c, buf, toks)

# a multiline body, including the quote that may start the closer
def lex.ml(+c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  lex.ml.go(U32.is_eq(Char.to_u32(c), 34), c, buf, toks)

# a second quote, or one quote of body
def lex.ml1.go(q: Bool, +c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match q:
    case True{}:
      Lex{Ml2{}, buf, toks}
    case False{}:
      lex.ml(c, lex.push_quotes(1n, buf), toks)

# one quote seen in a multiline string
def lex.ml1(+c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  lex.ml1.go(U32.is_eq(Char.to_u32(c), 34), c, buf, toks)

# the closing quotes, or two quotes of body
def lex.ml2.go(q: Bool, +c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match q:
    case True{}:
      Lex{Idle{}, [], lex.emit_str(buf, toks)}
    case False{}:
      lex.ml(c, lex.push_quotes(2n, buf), toks)

# two quotes seen in a multiline string
def lex.ml2(+c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  lex.ml2.go(U32.is_eq(Char.to_u32(c), 34), c, buf, toks)

# an apostrophe, or a literal body character
def lex.alit.go(q: Bool, +c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match q:
    case True{}:
      Lex{ALit1{}, buf, toks}
    case False{}:
      lex.alit_char(c, buf, toks)

# a multiline literal body
def lex.alit(+c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  lex.alit.go(U32.is_eq(Char.to_u32(c), 39), c, buf, toks)

# a second apostrophe, or one apostrophe of body
def lex.alit1.go(q: Bool, +c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match q:
    case True{}:
      Lex{ALit2{}, buf, toks}
    case False{}:
      lex.alit(c, lex.push_apos(1n, buf), toks)

# one apostrophe seen in a multiline literal
def lex.alit1(+c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  lex.alit1.go(U32.is_eq(Char.to_u32(c), 39), c, buf, toks)

# the closing apostrophes, or two of body
def lex.alit2.go(q: Bool, +c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match q:
    case True{}:
      Lex{Idle{}, [], lex.emit_str(buf, toks)}
    case False{}:
      lex.alit(c, lex.push_apos(2n, buf), toks)

# two apostrophes seen in a multiline literal
def lex.alit2(+c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  lex.alit2.go(U32.is_eq(Char.to_u32(c), 39), c, buf, toks)

# a carriage return right after `"""`
def lex.ml_drop.cr(cr: Bool, +c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match cr:
    case True{}:
      Lex{MlDropCr{}, buf, toks}
    case False{}:
      lex.ml(c, buf, toks)

# a newline right after `"""`, or the first body character
def lex.ml_drop.go(nl: Bool, +c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match nl:
    case True{}:
      Lex{Ml{}, buf, toks}
    case False{}:
      lex.ml_drop.cr(U32.is_eq(Char.to_u32(c), 13), c, buf, toks)

# the first character after `"""`
def lex.ml_drop(+c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  lex.ml_drop.go(U32.is_eq(Char.to_u32(c), 10), c, buf, toks)

# a carriage return right after `'''`
def lex.a_drop.cr(cr: Bool, +c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match cr:
    case True{}:
      Lex{ADropCr{}, buf, toks}
    case False{}:
      lex.alit(c, buf, toks)

# a newline right after `'''`, or the first body character
def lex.a_drop.go(nl: Bool, +c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match nl:
    case True{}:
      Lex{ALit{}, buf, toks}
    case False{}:
      lex.a_drop.cr(U32.is_eq(Char.to_u32(c), 13), c, buf, toks)

# the first character after `'''`
def lex.a_drop(+c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  lex.a_drop.go(U32.is_eq(Char.to_u32(c), 10), c, buf, toks)

# two quotes, waiting to see if they open a multiline string
def lex.q2(cls: Class, +c: Char, toks: List<&2, Tok>) -> Lex:
  match cls:
    case CQuote{}:
      Lex{MlDrop{}, [], toks}
    case other:
      lex.idle(cls, c, lex.emit(TStr{""}, toks))

# one quote, waiting for a basic string or a second quote
def lex.q1(cls: Class, +c: Char, toks: List<&2, Tok>) -> Lex:
  match cls:
    case CQuote{}:
      Lex{Q2{}, [], toks}
    case CSlash{}:
      Lex{Esc{}, [], toks}
    case CNl{}:
      Lex{Idle{}, [], lex.emit(TBad{"newline"}, toks)}
    case CCr{}:
      Lex{Idle{}, [], lex.emit(TBad{"newline"}, toks)}
    case other:
      lex.str_char(c, [], toks)

# two apostrophes, waiting to see if they open a multiline literal
def lex.a2(cls: Class, +c: Char, toks: List<&2, Tok>) -> Lex:
  match cls:
    case CApos{}:
      Lex{ADrop{}, [], toks}
    case other:
      lex.idle(cls, c, lex.emit(TStr{""}, toks))

# one apostrophe, waiting for a literal string or a second apostrophe
def lex.a1(cls: Class, +c: Char, toks: List<&2, Tok>) -> Lex:
  match cls:
    case CApos{}:
      Lex{A2{}, [], toks}
    case CNl{}:
      Lex{Idle{}, [], lex.emit(TBad{"newline"}, toks)}
    case CCr{}:
      Lex{Idle{}, [], lex.emit(TBad{"newline"}, toks)}
    case other:
      lex.lit_char(c, [], toks)

# a comment eats through the line
def lex.feed.comment(cls: Class, toks: List<&2, Tok>) -> Lex:
  match cls:
    case CNl{}:
      Lex{Idle{}, [], lex.emit(TNl{}, toks)}
    case CCr{}:
      Lex{Cr{}, [], lex.emit(TNl{}, toks)}
    case _:
      Lex{Comment{}, [], toks}

# the character after a carriage return
def lex.feed.cr(cls: Class, +c: Char, toks: List<&2, Tok>) -> Lex:
  match cls:
    case CNl{}:
      Lex{Idle{}, [], toks}
    case other:
      lex.idle(cls, c, toks)

# a basic string
def lex.feed.str(cls: Class, +c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match cls:
    case CQuote{}:
      Lex{Idle{}, [], lex.emit_str(buf, toks)}
    case CSlash{}:
      Lex{Esc{}, buf, toks}
    case CNl{}:
      Lex{Idle{}, [], lex.emit(TBad{"newline"}, toks)}
    case CCr{}:
      Lex{Idle{}, [], lex.emit(TBad{"newline"}, toks)}
    case _:
      lex.str_char(c, buf, toks)

# a literal string
def lex.feed.lit(cls: Class, +c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match cls:
    case CApos{}:
      Lex{Idle{}, [], lex.emit_str(buf, toks)}
    case CNl{}:
      Lex{Idle{}, [], lex.emit(TBad{"newline"}, toks)}
    case CCr{}:
      Lex{Idle{}, [], lex.emit(TBad{"newline"}, toks)}
    case _:
      lex.lit_char(c, buf, toks)

# the newline of a `\r` that opened a multiline string
def lex.feed.ml_cr(cls: Class, +c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match cls:
    case CNl{}:
      Lex{Ml{}, buf, toks}
    case other:
      lex.ml(c, buf, toks)

# the newline of a `\r` that opened a multiline literal
def lex.feed.a_cr(cls: Class, +c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match cls:
    case CNl{}:
      Lex{ALit{}, buf, toks}
    case other:
      lex.alit(c, buf, toks)

# the character after `\` `\r` in a multiline string
def lex.feed.esc_cr(cls: Class, +x: U32, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match cls:
    case CNl{}:
      Lex{MlTrim{}, buf, toks}
    case other:
      lex.ml_esc(x, buf, toks)

# whitespace after a line-ending backslash, or the next body character
def lex.feed.trim(skip: Bool, +c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  match skip:
    case True{}:
      Lex{MlTrim{}, buf, toks}
    case False{}:
      lex.ml(c, buf, toks)

# one character, once its code point is known
def lex.feed.on(md: Mode, +x: U32, +c: Char, buf: List<&2, Char>,
  toks: List<&2, Tok>) -> Lex:
  match md:
    case Idle{}:
      lex.idle(lex.classify(x), c, toks)
    case Word{}:
      lex.word(lex.classify(x), c, buf, toks)
    case Comment{}:
      lex.feed.comment(lex.classify(x), toks)
    case Cr{}:
      lex.feed.cr(lex.classify(x), c, toks)
    case Q1{}:
      lex.q1(lex.classify(x), c, toks)
    case Q2{}:
      lex.q2(lex.classify(x), c, toks)
    case A1{}:
      lex.a1(lex.classify(x), c, toks)
    case A2{}:
      lex.a2(lex.classify(x), c, toks)
    case Str{}:
      lex.feed.str(lex.classify(x), c, buf, toks)
    case Esc{}:
      lex.esc(x, buf, toks)
    case Lit{}:
      lex.feed.lit(lex.classify(x), c, buf, toks)
    case Uni{left, acc, ml}:
      lex.uni(left, acc, x, buf, toks, ml)
    case MlDrop{}:
      lex.ml_drop(c, buf, toks)
    case MlDropCr{}:
      lex.feed.ml_cr(lex.classify(x), c, buf, toks)
    case Ml{}:
      lex.ml(c, buf, toks)
    case Ml1{}:
      lex.ml1(c, buf, toks)
    case Ml2{}:
      lex.ml2(c, buf, toks)
    case MlEsc{}:
      lex.ml_esc(x, buf, toks)
    case MlEscCr{}:
      lex.feed.esc_cr(lex.classify(x), x, buf, toks)
    case MlTrim{}:
      lex.feed.trim(lex.trimming(x), c, buf, toks)
    case ADrop{}:
      lex.a_drop(c, buf, toks)
    case ADropCr{}:
      lex.feed.a_cr(lex.classify(x), c, buf, toks)
    case ALit{}:
      lex.alit(c, buf, toks)
    case ALit1{}:
      lex.alit1(c, buf, toks)
    case ALit2{}:
      lex.alit2(c, buf, toks)

# one character, by the mode
def lex.feed(md: Mode, +c: Char, buf: List<&2, Char>, toks: List<&2, Tok>) -> Lex:
  lex.feed.on(md, Char.to_u32(c), c, buf, toks)

# one character against a lexer
def lex.feed.lex(st: Lex, +c: Char) -> Lex:
  match st:
    case Lex{md, buf, toks}:
      lex.feed(md, c, buf, toks)

# every character
def lex.run(cs: List<&2, Char>, st: Lex) -> Lex:
  match cs:
    case []:
      st
    case +h <> t:
      lex.run(t, lex.feed.lex(st, h))

# tokens still open, once the mode is known
def lex.finish.go(md: Mode, buf: List<&2, Char>, toks: List<&2, Tok>) -> List<&2, Tok>:
  match md:
    case Idle{}:
      List.reverse(&2, Tok, toks)
    case Word{}:
      List.reverse(&2, Tok, lex.emit_word(buf, toks))
    case Comment{}:
      List.reverse(&2, Tok, toks)
    case Cr{}:
      List.reverse(&2, Tok, toks)
    case Q2{}:
      List.reverse(&2, Tok, lex.emit(TStr{""}, toks))
    case A2{}:
      List.reverse(&2, Tok, lex.emit(TStr{""}, toks))
    case _:
      List.reverse(&2, Tok, lex.emit(TBad{"unclosed"}, toks))

# tokens still open at the end of the text
def lex.finish(st: Lex) -> List<&2, Tok>:
  match st:
    case Lex{md, buf, toks}:
      lex.finish.go(md, buf, toks)

# the tokens of a text, in order
def tokens(s: String) -> List<&2, Tok>:
  lex.finish(lex.run(String.to_list(s), Lex{Idle{}, [], []}))
