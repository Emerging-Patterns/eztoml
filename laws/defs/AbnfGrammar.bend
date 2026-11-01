# the TOML ABNF rules and definition rules as Bend definitions
import Base
import ../../main.bend as T
import ./AbnfWhitespace.bend as D1
import ./BareValueGrammar.bend as D2
import ./DocumentSameness.bend as D3
import ./GrammarDerivations.bend as D4
import ./KeySegmentSpelling.bend as D5

# The date check (I4). The day of a date is within its month in its year.

# the twelve months, so a law can range over every one
type Month is Data:
  Jan{}
  Feb{}
  Mar{}
  Apr{}
  May{}
  Jun{}
  Jul{}
  Aug{}
  Sep{}
  Oct{}
  Nov{}
  Dec{}

# RFC 3339, Appendix C: a leap year is
#   (year % 4 == 0 && (year % 100 != 0 || year % 400 == 0))
def leap(+yy: U32) -> Bool:
  Bool.and(U32.is_eq(U32.mod(yy, 4), 0),
    Bool.or(Bool.not(U32.is_eq(U32.mod(yy, 100), 0)), U32.is_eq(U32.mod(yy, 400), 0)))

# February's row of the table below
def feb_days(is_leap: Bool) -> U32:
  match is_leap:
    case True{}:
      29
    case False{}:
      28

# RFC 3339, section 5.7:
#   Month Number  Month/Year           Maximum value of date-mday
#   ------------  ----------           --------------------------
#   01            January              31
#   02            February, normal     28
#   02            February, leap year  29
#   03            March                31
#   04            April                30
#   05            May                  31
#   06            June                 30
#   07            July                 31
#   08            August               31
#   09            September            30
#   10            October              31
#   11            November             30
#   12            December             31
def days_in(+yy: U32, mm: Month) -> U32:
  match mm:
    case Jan{}:
      31
    case Feb{}:
      feb_days(leap(yy))
    case Mar{}:
      31
    case Apr{}:
      30
    case May{}:
      31
    case Jun{}:
      30
    case Jul{}:
      31
    case Aug{}:
      31
    case Sep{}:
      30
    case Oct{}:
      31
    case Nov{}:
      30
    case Dec{}:
      31

# GRAMMAR SPIKE
#
# One rule of toml.abnf (TOML v1.0.0), dec-int, transcribed as a Bool
# recognizer over a bare word's characters, one def per rule with the rule
# quoted above it, as laws/BareKey.bend's unquoted-key is. It tries the leaf form of
# the grammar relation (docs/rfc/eztoml-grammar-proofs.md) against the numeral
# scan. Bend has no hex literals, so each bound is in decimal with its hex
# beside it.

# minus = %x2D ; -
# (%x2D is 45)
def abnf.minus(cc: Char) -> Bool:
  match cc:
    case Chr{+cp}:
      U32.is_eq(cp, 45)

# plus = %x2B ; +
# (%x2B is 43)
def abnf.plus(cc: Char) -> Bool:
  match cc:
    case Chr{+cp}:
      U32.is_eq(cp, 43)

# underscore = %x5F ; _
# (%x5F is 95)
def abnf.underscore(cc: Char) -> Bool:
  match cc:
    case Chr{+cp}:
      U32.is_eq(cp, 95)

# digit1-9 = %x31-39 ; 1-9
# (%x31 is 49, %x39 is 57)
def abnf.digit1_9(cc: Char) -> Bool:
  match cc:
    case Chr{+cp}:
      Bool.and(U32.is_ge(cp, 49), U32.is_le(cp, 57))

# DIGIT = %x30-39 ; 0-9, over a character (abnf.digit is over a code point)
def abnf.DIGIT(cc: Char) -> Bool:
  match cc:
    case Chr{+cp}:
      D2.abnf.digit(cp)

# *( DIGIT / underscore DIGIT ): nothing, or one of the two and the rest. A
# lone character left can only be a DIGIT, since underscore needs one after it
def abnf.dec_rep(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      True{}
    case +hh <> tt:
      match tt:
        case []:
          abnf.DIGIT(hh)
        case +h2 <> +t2:
          Bool.or(Bool.and(abnf.DIGIT(hh), abnf.dec_rep(h2 <> t2)),
            Bool.and(abnf.underscore(hh), Bool.and(abnf.DIGIT(h2), abnf.dec_rep(t2))))

# 1*( DIGIT / underscore DIGIT ): the repetition, at least once
def abnf.dec_rep1(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      False{}
    case +hh <> tt:
      abnf.dec_rep(hh <> tt)

# unsigned-dec-int = DIGIT / digit1-9 1*( DIGIT / underscore DIGIT )
def abnf.unsigned_dec_int(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      False{}
    case +hh <> +tt:
      Bool.or(Bool.and(abnf.DIGIT(hh), List.is_empty(&2, Char, tt)),
        Bool.and(abnf.digit1_9(hh), abnf.dec_rep1(tt)))

# dec-int = [ minus / plus ] unsigned-dec-int
def abnf.dec_int(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      False{}
    case +hh <> +tt:
      Bool.or(Bool.and(Bool.or(abnf.minus(hh), abnf.plus(hh)), abnf.unsigned_dec_int(tt)),
        abnf.unsigned_dec_int(hh <> tt))

# a character of a numeral kept unless it is an underscore
def abnf.no_us.pick(us: Bool, cc: Char, rest: String) -> String:
  match us:
    case True{}:
      rest
    case False{}:
      SCon{cc, rest}

# a numeral's characters with its underscores removed
def abnf.no_us(cs: List<&2, Char>) -> String:
  match cs:
    case []:
      ""
    case +hh <> tt:
      abnf.no_us.pick(abnf.underscore(hh), hh, abnf.no_us(tt))

# the sign a leading minus gives, and plus otherwise
def abnf.sign.pick(minus: Bool) -> T.Sign:
  match minus:
    case True{}:
      T.Minus{}
    case False{}:
      T.Plus{}

# the sign a dec-int is read with: minus when it starts with one, else plus
def abnf.dec_sign(cs: List<&2, Char>) -> T.Sign:
  match cs:
    case []:
      T.Plus{}
    case +hh <> _:
      abnf.sign.pick(abnf.minus(hh))

# the characters after a leading sign, or all of them
def abnf.digits.pick(signed: Bool, cc: Char, rest: List<&2, Char>) -> String:
  match signed:
    case True{}:
      abnf.no_us(rest)
    case False{}:
      abnf.no_us(cc <> rest)

# the digits a dec-int is read as: after its sign, with the underscores
# removed. unsigned-dec-int allows no leading zero except in 0 itself, so these
# are its value's decimal digits
def abnf.dec_digits(cs: List<&2, Char>) -> String:
  match cs:
    case []:
      ""
    case +hh <> tt:
      abnf.digits.pick(Bool.or(abnf.minus(hh), abnf.plus(hh)), hh, tt)

# GRAMMAR
#
# toml.abnf (TOML v1.0.0; github.com/toml-lang/toml at tag 1.0.0) transcribed
# as the grammar relation of laws/ParsesExactlyTheGrammar.bend (docs/rfc/eztoml-grammar-proofs.md,
# WP-G). The context-free structure is data, a derivation (Gd) whose
# constructors are named after the rules they spell; the regular rules are
# Bool recognizers at its leaves, over a leaf's characters. A text matches
# the grammar when, with one leading U+FEFF taken off (bom.drop), it is
# g.text(d) for a derivation d with g.ok(d). g.ok asks each leaf to match its
# rule and to keep the four restrictions the specification's prose adds
# (prose.*). g.val says what a value derivation denotes, and defs is the
# prose's definition rules, which laws/DefinesEachTableOnce.bend states.
#
# Each rule is quoted verbatim above the def or constructor that transcribes
# it; a rule the GRAMMAR SPIKE or laws/BareKey.bend already transcribed is reused
# (DIGIT, minus, plus, underscore, digit1-9, dec-int, unsigned-dec-int,
# unquoted-key), and laws/KeyNameIsItsCharacters.bend's KPiece and KSeg are a basic string's
# pieces and a simple-key. Two traps: a quoted string in ABNF is
# case-insensitive (RFC 5234, section 2.3), so "T", "Z", "e" and HEXDIG's "A"
# to "F" match either case, while a %x string such as hex-prefix, true or inf
# matches only itself; and Bend has no mutual recursion, so the mutually
# recursive rules val, array-values, inline-table-keyvals and keyval are
# constructors of one type, GVal, and a def over it takes a mode (GRule)
# saying which rule a node spells. Bend has no hex literals, so each bound is
# in decimal with its hex beside it.

# whether a character is the one with code point nn
def abnf.cp(cc: Char, +nn: U32) -> Bool:
  match cc:
    case Chr{+cp}:
      U32.is_eq(cp, nn)

# whether a code point is from lo to hi, both included: RFC 5234's %xLO-HI
def abnf.range(+cp: U32, +lo: U32, +hi: U32) -> Bool:
  Bool.and(U32.is_ge(cp, lo), U32.is_le(cp, hi))

# newline =  %x0A     ; LF
# newline =/ %x0D.0A  ; CRLF
# (%x0A is 10, %x0D is 13)
def abnf.newline(ss: String) -> Bool:
  match ss:
    case SNil{}:
      False{}
    case SCon{hh, tt}:
      match tt:
        case SNil{}:
          abnf.cp(hh, 10)
        case SCon{h2, t2}:
          Bool.and(abnf.cp(hh, 13), Bool.and(abnf.cp(h2, 10), String.is_empty(t2)))

# [ newline ]: nothing, or a newline
def abnf.opt_newline(ss: String) -> Bool:
  match ss:
    case SNil{}:
      True{}
    case SCon{hh, tt}:
      abnf.newline(SCon{hh, tt})

# non-ascii = %x80-D7FF / %xE000-10FFFF
# (%x80 is 128, %xD7FF is 55295, %xE000 is 57344, %x10FFFF is 1114111)
def abnf.non_ascii(cc: Char) -> Bool:
  match cc:
    case Chr{+cp}:
      Bool.or(abnf.range(cp, 128, 55295), abnf.range(cp, 57344, 1114111))

# non-eol = %x09 / %x20-7F / non-ascii
# (%x09 is 9, %x20 is 32, %x7F is 127)
def abnf.non_eol(cc: Char) -> Bool:
  match cc:
    case Chr{+cp}:
      Bool.or(U32.is_eq(cp, 9), Bool.or(abnf.range(cp, 32, 127), abnf.non_ascii(Chr{cp})))

# comment-start-symbol = %x23 ; #
# comment = comment-start-symbol *non-eol
# over the characters after the # (g.com.text writes the #)
def abnf.comment(ss: String) -> Bool:
  match ss:
    case SNil{}:
      True{}
    case SCon{hh, tt}:
      Bool.and(abnf.non_eol(hh), abnf.comment(tt))

# *( wschar / newline ), the tail of mlb-escaped-nl. A newline is LF or CR
# LF, so a CR is taken with the LF after it
def abnf.ws_newlines(ss: String) -> Bool:
  match ss:
    case SNil{}:
      True{}
    case SCon{+hh, tt}:
      match tt:
        case SNil{}:
          Bool.or(D1.abnf.wschar(hh), abnf.cp(hh, 10))
        case SCon{+h2, +t2}:
          Bool.or(Bool.and(Bool.or(D1.abnf.wschar(hh), abnf.cp(hh, 10)), abnf.ws_newlines(SCon{h2, t2})),
            Bool.and(abnf.cp(hh, 13), Bool.and(abnf.cp(h2, 10), abnf.ws_newlines(t2))))

# Strings. A basic string's pieces are laws/KeyNameIsItsCharacters.bend's KPiece: KpChar is a
# basic-unescaped character, KpEsc the seven escape-seq-char letters (KMark),
# and KpU4 and KpU8 the %x75 4HEXDIG and %x55 8HEXDIG forms, each digit a
# KHex, a HEXDIG in either case.

# basic-unescaped = wschar / %x21 / %x23-5B / %x5D-7E / non-ascii
# (%x21 is 33, %x23 is 35, %x5B is 91, %x5D is 93, %x7E is 126)
def abnf.basic_unescaped(cc: Char) -> Bool:
  match cc:
    case Chr{+cp}:
      Bool.or(D1.abnf.wschar(Chr{cp}), Bool.or(U32.is_eq(cp, 33), Bool.or(abnf.range(cp, 35, 91),
        Bool.or(abnf.range(cp, 93, 126), abnf.non_ascii(Chr{cp})))))

# basic-char = basic-unescaped / escaped
# escaped = escape escape-seq-char
# escape = %x5C                   ; \
# escape-seq-char =  %x22         ; "    quotation mark  U+0022
# escape-seq-char =/ %x5C         ; \    reverse solidus U+005C
# escape-seq-char =/ %x62         ; b    backspace       U+0008
# escape-seq-char =/ %x66         ; f    form feed       U+000C
# escape-seq-char =/ %x6E         ; n    line feed       U+000A
# escape-seq-char =/ %x72         ; r    carriage return U+000D
# escape-seq-char =/ %x74         ; t    tab             U+0009
# escape-seq-char =/ %x75 4HEXDIG ; uXXXX                U+XXXX
# escape-seq-char =/ %x55 8HEXDIG ; UXXXXXXXX            U+XXXXXXXX
# every escaped piece is one of these by its type; a character written as
# itself must be basic-unescaped
def abnf.basic_char(pp: D5.KPiece) -> Bool:
  match pp:
    case D5.KpChar{cc}:
      abnf.basic_unescaped(cc)
    case D5.KpEsc{_mm}:
      True{}
    case D5.KpU4{_d, _c, _b, _a}:
      True{}
    case D5.KpU8{_h, _g, _f, _e, _d, _c, _b, _a}:
      True{}

# basic-string = quotation-mark *basic-char quotation-mark
# quotation-mark = %x22            ; "
# over the pieces between the quotation marks
def abnf.basic_string(ps: List<&2, D5.KPiece>) -> Bool:
  match ps:
    case []:
      True{}
    case pp <> rest:
      Bool.and(abnf.basic_char(pp), abnf.basic_string(rest))

# mlb-unescaped = wschar / %x21 / %x23-5B / %x5D-7E / non-ascii
# (the set basic-unescaped is)
def abnf.mlb_unescaped(cc: Char) -> Bool:
  match cc:
    case Chr{+cp}:
      Bool.or(D1.abnf.wschar(Chr{cp}), Bool.or(U32.is_eq(cp, 33), Bool.or(abnf.range(cp, 35, 91),
        Bool.or(abnf.range(cp, 93, 126), abnf.non_ascii(Chr{cp})))))

# mlb-char = mlb-unescaped / escaped
def abnf.mlb_char(pp: D5.KPiece) -> Bool:
  match pp:
    case D5.KpChar{cc}:
      abnf.mlb_unescaped(cc)
    case D5.KpEsc{_mm}:
      True{}
    case D5.KpU4{_d, _c, _b, _a}:
      True{}
    case D5.KpU8{_h, _g, _f, _e, _d, _c, _b, _a}:
      True{}

# mlb-escaped-nl = escape ws newline *( wschar / newline )
# over the ws, the newline and what follows them
def abnf.mlb_escaped_nl(w1: String, nl: String, more: String) -> Bool:
  Bool.and(D1.abnf.ws(w1), Bool.and(abnf.newline(nl), abnf.ws_newlines(more)))

# mlb-content = mlb-char / newline / mlb-escaped-nl
def abnf.mlb_content(pp: D4.GMlb) -> Bool:
  match pp:
    case D4.GmChar{kp}:
      abnf.mlb_char(kp)
    case D4.GmNewline{nl}:
      abnf.newline(nl)
    case D4.GmEscapedNl{w1, nl, more}:
      abnf.mlb_escaped_nl(w1, nl, more)
    case D4.GmQuotes{_two}:
      False{}

# ml-basic-body = *mlb-content *( mlb-quotes 1*mlb-content ) [ mlb-quotes ]
# A list of pieces matches exactly when each is an mlb-content or an
# mlb-quotes and no two mlb-quotes are next to each other; qq says the piece
# before was an mlb-quotes
def abnf.ml_basic_body(ps: List<&2, D4.GMlb>, qq: Bool) -> Bool:
  match ps:
    case []:
      True{}
    case D4.GmQuotes{_two} <> rest:
      Bool.and(Bool.not(qq), abnf.ml_basic_body(rest, True{}))
    case pp <> rest:
      Bool.and(abnf.mlb_content(pp), abnf.ml_basic_body(rest, False{}))

# literal-char = %x09 / %x20-26 / %x28-7E / non-ascii
# (%x09 is 9, %x20 is 32, %x26 is 38, %x28 is 40, %x7E is 126)
def abnf.literal_char(cc: Char) -> Bool:
  match cc:
    case Chr{+cp}:
      Bool.or(U32.is_eq(cp, 9), Bool.or(abnf.range(cp, 32, 38), Bool.or(abnf.range(cp, 40, 126),
        abnf.non_ascii(Chr{cp}))))

# literal-string = apostrophe *literal-char apostrophe
# apostrophe = %x27 ; ' apostrophe
# over the characters between the apostrophes
def abnf.literal_string(ss: String) -> Bool:
  match ss:
    case SNil{}:
      True{}
    case SCon{hh, tt}:
      Bool.and(abnf.literal_char(hh), abnf.literal_string(tt))

# mll-char = %x09 / %x20-26 / %x28-7E / non-ascii
def abnf.mll_char(cc: Char) -> Bool:
  match cc:
    case Chr{+cp}:
      Bool.or(U32.is_eq(cp, 9), Bool.or(abnf.range(cp, 32, 38), Bool.or(abnf.range(cp, 40, 126),
        abnf.non_ascii(Chr{cp}))))

# mll-content = mll-char / newline
def abnf.mll_content(pp: D4.GMll) -> Bool:
  match pp:
    case D4.GlChar{cc}:
      abnf.mll_char(cc)
    case D4.GlNewline{nl}:
      abnf.newline(nl)
    case D4.GlQuotes{_two}:
      False{}

# ml-literal-body = *mll-content *( mll-quotes 1*mll-content ) [ mll-quotes ]
# as ml-basic-body: no two mll-quotes next to each other
def abnf.ml_literal_body(ps: List<&2, D4.GMll>, qq: Bool) -> Bool:
  match ps:
    case []:
      True{}
    case D4.GlQuotes{_two} <> rest:
      Bool.and(Bool.not(qq), abnf.ml_literal_body(rest, True{}))
    case pp <> rest:
      Bool.and(abnf.mll_content(pp), abnf.ml_literal_body(rest, False{}))

# Integer. dec-int, unsigned-dec-int, minus, plus, underscore, digit1-9 and
# DIGIT are the GRAMMAR SPIKE's.

# HEXDIG = DIGIT / "A" / "B" / "C" / "D" / "E" / "F"
# The quoted letters are case-insensitive, so a to f match too
# (%x41 is 65, %x46 is 70, %x61 is 97, %x66 is 102)
def abnf.HEXDIG(cc: Char) -> Bool:
  match cc:
    case Chr{+cp}:
      Bool.or(D2.abnf.digit(cp), Bool.or(abnf.range(cp, 65, 70), abnf.range(cp, 97, 102)))

# digit0-7 = %x30-37                 ; 0-7
# (%x30 is 48, %x37 is 55)
def abnf.digit0_7(cc: Char) -> Bool:
  match cc:
    case Chr{+cp}:
      abnf.range(cp, 48, 55)

# digit0-1 = %x30-31                 ; 0-1
# (%x30 is 48, %x31 is 49)
def abnf.digit0_1(cc: Char) -> Bool:
  match cc:
    case Chr{+cp}:
      abnf.range(cp, 48, 49)

# the digit rule of a prefixed integer: HEXDIG, digit0-7 or digit0-1
type ARadix is Data:
  AHex{}
  AOct{}
  ABin{}

# a character of the radix's digit rule
def abnf.radix_digit(rx: ARadix, cc: Char) -> Bool:
  match rx:
    case AHex{}:
      abnf.HEXDIG(cc)
    case AOct{}:
      abnf.digit0_7(cc)
    case ABin{}:
      abnf.digit0_1(cc)

# *( D / underscore D ), for D the radix's digit rule, as abnf.dec_rep is for
# DIGIT: a lone character left can only be a D
def abnf.radix_rep(cs: List<&2, Char>, +rx: ARadix) -> Bool:
  match cs:
    case []:
      True{}
    case +hh <> tt:
      match tt:
        case []:
          abnf.radix_digit(rx, hh)
        case +h2 <> +t2:
          Bool.or(Bool.and(abnf.radix_digit(rx, hh), abnf.radix_rep(h2 <> t2, rx)),
            Bool.and(abnf.underscore(hh), Bool.and(abnf.radix_digit(rx, h2), abnf.radix_rep(t2, rx))))

# a prefix of 0 and the letter with code point ll, then one D, then
# *( D / underscore D )
def abnf.prefixed(cs: List<&2, Char>, +ll: U32, +rx: ARadix) -> Bool:
  match cs:
    case +c0 <> +c1 <> +c2 <> rest:
      Bool.and(abnf.cp(c0, 48), Bool.and(abnf.cp(c1, ll), Bool.and(abnf.radix_digit(rx, c2),
        abnf.radix_rep(rest, rx))))
    case _:
      False{}

# hex-int = hex-prefix HEXDIG *( HEXDIG / underscore HEXDIG )
# hex-prefix = %x30.78               ; 0x
# (%x78 is 120; a %x string, so 0X is no prefix)
def abnf.hex_int(cs: List<&2, Char>) -> Bool:
  abnf.prefixed(cs, 120, AHex{})

# oct-int = oct-prefix digit0-7 *( digit0-7 / underscore digit0-7 )
# oct-prefix = %x30.6F               ; 0o
# (%x6F is 111)
def abnf.oct_int(cs: List<&2, Char>) -> Bool:
  abnf.prefixed(cs, 111, AOct{})

# bin-int = bin-prefix digit0-1 *( digit0-1 / underscore digit0-1 )
# bin-prefix = %x30.62               ; 0b
# (%x62 is 98)
def abnf.bin_int(cs: List<&2, Char>) -> Bool:
  abnf.prefixed(cs, 98, ABin{})

# integer = dec-int / hex-int / oct-int / bin-int
def abnf.integer(+cs: List<&2, Char>) -> Bool:
  Bool.or(abnf.dec_int(cs), Bool.or(abnf.hex_int(cs), Bool.or(abnf.oct_int(cs), abnf.bin_int(cs))))

# Float.

# decimal-point = %x2E               ; .
# (%x2E is 46)
def abnf.decimal_point(cc: Char) -> Bool:
  abnf.cp(cc, 46)

# the "e" of exp: a quoted string, so e or E
# (%x65 is 101, %x45 is 69)
def abnf.e(+cc: Char) -> Bool:
  Bool.or(abnf.cp(cc, 101), abnf.cp(cc, 69))

# where a float's parts are cut: at the first decimal-point or e (Dot), or at
# the first e (Exp)
type ACut is Data:
  ACutDot{}
  ACutExp{}

# whether a character is where the cut falls
def abnf.cut.at(ct: ACut, +cc: Char) -> Bool:
  match ct:
    case ACutDot{}:
      Bool.or(abnf.decimal_point(cc), abnf.e(cc))
    case ACutExp{}:
      abnf.e(cc)

# a character kept before the cut, or the cut reached
def abnf.cut.pre.pick(at: Bool, cc: Char, rest: List<&2, Char>) -> List<&2, Char>:
  match at:
    case True{}:
      []
    case False{}:
      cc <> rest

# the characters before the cut
def abnf.cut.pre(cs: List<&2, Char>, +ct: ACut) -> List<&2, Char>:
  match cs:
    case []:
      []
    case +hh <> tt:
      abnf.cut.pre.pick(abnf.cut.at(ct, hh), hh, abnf.cut.pre(tt, ct))

# the characters after a kept one, or all of them from the cut on
def abnf.cut.post.pick(at: Bool, cc: Char, tt: List<&2, Char>, rest: List<&2, Char>) -> List<&2, Char>:
  match at:
    case True{}:
      cc <> tt
    case False{}:
      rest

# the characters from the cut on, the cut's character first; none when there
# is no cut
def abnf.cut.post(cs: List<&2, Char>, +ct: ACut) -> List<&2, Char>:
  match cs:
    case []:
      []
    case +hh <> +tt:
      abnf.cut.post.pick(abnf.cut.at(ct, hh), hh, tt, abnf.cut.post(tt, ct))

# zero-prefixable-int = DIGIT *( DIGIT / underscore DIGIT )
def abnf.zero_prefixable_int(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      False{}
    case hh <> tt:
      Bool.and(abnf.DIGIT(hh), abnf.dec_rep(tt))

# frac = decimal-point zero-prefixable-int
def abnf.frac(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      False{}
    case hh <> tt:
      Bool.and(abnf.decimal_point(hh), abnf.zero_prefixable_int(tt))

# float-exp-part = [ minus / plus ] zero-prefixable-int
def abnf.float_exp_part(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      False{}
    case +hh <> +tt:
      Bool.or(Bool.and(Bool.or(abnf.minus(hh), abnf.plus(hh)), abnf.zero_prefixable_int(tt)),
        abnf.zero_prefixable_int(hh <> tt))

# exp = "e" float-exp-part
def abnf.exp(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      False{}
    case hh <> tt:
      Bool.and(abnf.e(hh), abnf.float_exp_part(tt))

# [ exp ]: nothing, or an exp
def abnf.opt_exp(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      True{}
    case hh <> tt:
      abnf.exp(hh <> tt)

# frac [ exp ], cut at the first e: a frac holds none, so no other cut can
# match
def abnf.frac_exp(+cs: List<&2, Char>) -> Bool:
  Bool.and(abnf.frac(abnf.cut.pre(cs, ACutExp{})), abnf.opt_exp(abnf.cut.post(cs, ACutExp{})))

# float-int-part = dec-int
def abnf.float_int_part(cs: List<&2, Char>) -> Bool:
  abnf.dec_int(cs)

# float = float-int-part ( exp / frac [ exp ] ), cut at the first
# decimal-point or e: a float-int-part (a dec-int) holds neither, and exp and
# frac each start with one, so no other cut can match
def abnf.float_std(+cs: List<&2, Char>) -> Bool:
  +post = abnf.cut.post(cs, ACutDot{})
  Bool.and(abnf.float_int_part(abnf.cut.pre(cs, ACutDot{})), Bool.or(abnf.exp(post), abnf.frac_exp(post)))

# inf = %x69.6e.66  ; inf
def abnf.inf(cs: List<&2, Char>) -> Bool:
  D2.abnf.chars_are(cs, "inf")

# nan = %x6e.61.6e  ; nan
def abnf.nan(cs: List<&2, Char>) -> Bool:
  D2.abnf.chars_are(cs, "nan")

# special-float = [ minus / plus ] ( inf / nan )
def abnf.special_float(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      False{}
    case +hh <> +tt:
      Bool.or(Bool.and(Bool.or(abnf.minus(hh), abnf.plus(hh)), Bool.or(abnf.inf(tt), abnf.nan(tt))),
        Bool.or(abnf.inf(hh <> tt), abnf.nan(hh <> tt)))

# float = float-int-part ( exp / frac [ exp ] )
# float =/ special-float
def abnf.float(+cs: List<&2, Char>) -> Bool:
  Bool.or(abnf.float_std(cs), abnf.special_float(cs))

# Date and Time. Each rule is read from the front of a word and gives what is
# left of it (ALeft), or no match (ANone). Every alternative and option here
# is told apart by its first character, so at most one way can match.

# what is left of a word after a rule matched a prefix of it, or no match
type ARest is Data:
  ALeft{cs: List<&2, Char>}
  ANone{}

# the rest after a character that passed a test
def abnf.keep(ok: Bool, tt: List<&2, Char>) -> ARest:
  match ok:
    case True{}:
      ALeft{tt}
    case False{}:
      ANone{}

# DIGIT, from the front
def abnf.digit_r(rr: ARest) -> ARest:
  match rr:
    case ALeft{cs}:
      match cs:
        case []:
          ANone{}
        case hh <> tt:
          abnf.keep(abnf.DIGIT(hh), tt)
    case ANone{}:
      ANone{}

# the character with code point nn, from the front: a %x character, or a
# quoted one that is no letter
def abnf.char_r(rr: ARest, +nn: U32) -> ARest:
  match rr:
    case ALeft{cs}:
      match cs:
        case []:
          ANone{}
        case hh <> tt:
          abnf.keep(abnf.cp(hh, nn), tt)
    case ANone{}:
      ANone{}

# a quoted letter, from the front: its upper case (code point up) or its
# lower case (low)
def abnf.letter_r(rr: ARest, +up: U32, +low: U32) -> ARest:
  match rr:
    case ALeft{cs}:
      match cs:
        case []:
          ANone{}
        case +hh <> tt:
          abnf.keep(Bool.or(abnf.cp(hh, up), abnf.cp(hh, low)), tt)
    case ANone{}:
      ANone{}

# the first of two alternatives that matched
def abnf.or_r(aa: ARest, bb: ARest) -> ARest:
  match aa:
    case ALeft{cs}:
      ALeft{cs}
    case ANone{}:
      bb

# whether a rule matched the whole word
def abnf.all_r(rr: ARest) -> Bool:
  match rr:
    case ALeft{cs}:
      List.is_empty(&2, Char, cs)
    case ANone{}:
      False{}

# a word with its leading DIGITs taken off, or kept when the first is none
def abnf.drop_digits.pick(dg: Bool, hh: Char, tt: List<&2, Char>, after: List<&2, Char>) -> List<&2, Char>:
  match dg:
    case True{}:
      after
    case False{}:
      hh <> tt

# the word after its leading DIGITs
def abnf.drop_digits(cs: List<&2, Char>) -> List<&2, Char>:
  match cs:
    case []:
      []
    case +hh <> +tt:
      abnf.drop_digits.pick(abnf.DIGIT(hh), hh, tt, abnf.drop_digits(tt))

# 1*DIGIT, taking every DIGIT there is: in a date-time what follows it is a
# time-offset or the end, which starts with no DIGIT
def abnf.digits1_r(rr: ARest) -> ARest:
  match rr:
    case ALeft{cs}:
      match cs:
        case []:
          ANone{}
        case +hh <> +tt:
          abnf.keep(abnf.DIGIT(hh), abnf.drop_digits(tt))
    case ANone{}:
      ANone{}

# date-fullyear  = 4DIGIT
def abnf.date_fullyear(rr: ARest) -> ARest:
  abnf.digit_r(abnf.digit_r(abnf.digit_r(abnf.digit_r(rr))))

# date-month     = 2DIGIT  ; 01-12
# (the range is prose.date_time_in_range's)
def abnf.date_month(rr: ARest) -> ARest:
  abnf.digit_r(abnf.digit_r(rr))

# date-mday      = 2DIGIT  ; 01-28, 01-29, 01-30, 01-31 based on month/year
def abnf.date_mday(rr: ARest) -> ARest:
  abnf.digit_r(abnf.digit_r(rr))

# time-delim     = "T" / %x20 ; T, t, or space
# (%x54 is 84, %x74 is 116, %x20 is 32)
def abnf.time_delim(+rr: ARest) -> ARest:
  abnf.or_r(abnf.letter_r(rr, 84, 116), abnf.char_r(rr, 32))

# time-hour      = 2DIGIT  ; 00-23
def abnf.time_hour(rr: ARest) -> ARest:
  abnf.digit_r(abnf.digit_r(rr))

# time-minute    = 2DIGIT  ; 00-59
def abnf.time_minute(rr: ARest) -> ARest:
  abnf.digit_r(abnf.digit_r(rr))

# time-second    = 2DIGIT  ; 00-58, 00-59, 00-60 based on leap second rules
def abnf.time_second(rr: ARest) -> ARest:
  abnf.digit_r(abnf.digit_r(rr))

# time-secfrac   = "." 1*DIGIT
# (%x2E is 46)
def abnf.time_secfrac(rr: ARest) -> ARest:
  abnf.digits1_r(abnf.char_r(rr, 46))

# time-numoffset = ( "+" / "-" ) time-hour ":" time-minute
# (%x2B is 43, %x2D is 45, %x3A is 58)
def abnf.time_numoffset(+rr: ARest) -> ARest:
  abnf.time_minute(abnf.char_r(abnf.time_hour(abnf.or_r(abnf.char_r(rr, 43), abnf.char_r(rr, 45))), 58))

# time-offset    = "Z" / time-numoffset
# (%x5A is 90, %x7A is 122)
def abnf.time_offset(+rr: ARest) -> ARest:
  abnf.or_r(abnf.letter_r(rr, 90, 122), abnf.time_numoffset(rr))

# a time-secfrac when the word goes on with ".", and nothing otherwise
def abnf.opt_secfrac.pick(dot: Bool, cs: List<&2, Char>) -> ARest:
  match dot:
    case True{}:
      abnf.time_secfrac(ALeft{cs})
    case False{}:
      ALeft{cs}

# [ time-secfrac ]: taken when the next character is ".", since what follows
# a partial-time (a time-offset or the end) never starts with one
def abnf.opt_secfrac(rr: ARest) -> ARest:
  match rr:
    case ALeft{cs}:
      match cs:
        case []:
          ALeft{[]}
        case +hh <> +tt:
          abnf.opt_secfrac.pick(abnf.cp(hh, 46), hh <> tt)
    case ANone{}:
      ANone{}

# partial-time   = time-hour ":" time-minute ":" time-second [ time-secfrac ]
def abnf.partial_time(rr: ARest) -> ARest:
  abnf.opt_secfrac(abnf.time_second(abnf.char_r(abnf.time_minute(abnf.char_r(abnf.time_hour(rr), 58)), 58)))

# full-date      = date-fullyear "-" date-month "-" date-mday
def abnf.full_date(rr: ARest) -> ARest:
  abnf.date_mday(abnf.char_r(abnf.date_month(abnf.char_r(abnf.date_fullyear(rr), 45)), 45))

# full-time      = partial-time time-offset
def abnf.full_time(rr: ARest) -> ARest:
  abnf.time_offset(abnf.partial_time(rr))

# offset-date-time = full-date time-delim full-time
def abnf.offset_date_time(rr: ARest) -> ARest:
  abnf.full_time(abnf.time_delim(abnf.full_date(rr)))

# local-date-time = full-date time-delim partial-time
def abnf.local_date_time(rr: ARest) -> ARest:
  abnf.partial_time(abnf.time_delim(abnf.full_date(rr)))

# local-date = full-date
def abnf.local_date(rr: ARest) -> ARest:
  abnf.full_date(rr)

# local-time = partial-time
def abnf.local_time(rr: ARest) -> ARest:
  abnf.partial_time(rr)

# date-time      = offset-date-time / local-date-time / local-date / local-time
# a whole word matches one of the four
def abnf.date_time(+cs: List<&2, Char>) -> Bool:
  Bool.or(abnf.all_r(abnf.offset_date_time(ALeft{cs})), Bool.or(abnf.all_r(abnf.local_date_time(ALeft{cs})),
    Bool.or(abnf.all_r(abnf.local_date(ALeft{cs})), abnf.all_r(abnf.local_time(ALeft{cs})))))

# The four restrictions the specification's prose adds to toml.abnf
# (REVIEW-G1), each with its sentence of TOML v1.0.0.

# the largest integer, 2^63 - 1, and the largest magnitude of a negative one,
# 2^63, in decimal
def prose.i64.limit(sign: T.Sign) -> String:
  match sign:
    case T.Plus{}:
      "9223372036854775807"
    case T.Minus{}:
      "9223372036854775808"

# the first differing digit decides; a tie keeps what came before
def prose.dec_le.ord(seen: Cmp, now: Cmp) -> Cmp:
  match seen:
    case EQ{}:
      now
    case LT{}:
      LT{}
    case GT{}:
      GT{}

# whether a string of decimal digits with no leading zero is at most the
# limit: shorter is less, longer is more, and the same length compares digit
# by digit from the most significant
def prose.dec_le(ds: String, lim: String, ord: Cmp) -> Bool:
  match ds lim:
    case SNil{} SNil{}:
      Cmp.is_le(ord)
    case SNil{} SCon{_h, _t}:
      True{}
    case SCon{_h, _t} SNil{}:
      False{}
    case SCon{xx, xt} SCon{yy, yt}:
      prose.dec_le(xt, yt, prose.dec_le.ord(ord, U32.cmp(Char.to_u32(xx), Char.to_u32(yy))))

# a leading underscore or zero dropped, or the rest kept as it is, its
# underscores removed
def prose.sig.pick(skip: Bool, hh: Char, tt: List<&2, Char>, after: List<&2, Char>) -> List<&2, Char>:
  match skip:
    case True{}:
      after
    case False{}:
      String.to_list(abnf.no_us(hh <> tt))

# a numeral's characters with its underscores and leading zeros removed: its
# significant digits
def prose.sig(cs: List<&2, Char>) -> List<&2, Char>:
  match cs:
    case []:
      []
    case +hh <> +tt:
      prose.sig.pick(Bool.or(abnf.underscore(hh), abnf.cp(hh, 48)), hh, tt, prose.sig(tt))

# whether a list starts with a digit from 0 to 7
def prose.first_le7(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      True{}
    case hh <> _tt:
      abnf.digit0_7(hh)

# whether significant digits in a radix are at most 2^63 - 1: in hexadecimal
# 7FFFFFFFFFFFFFFF, at most 15 digits or 16 whose first is at most 7; in
# octal 777777777777777777777, at most 21 digits; in binary, at most 63
def prose.radix_fits(rx: ARadix, +nn: Nat, sig: List<&2, Char>) -> Bool:
  match rx:
    case AHex{}:
      Bool.or(Nat.is_lt(nn, 16n), Bool.and(Nat.is_eq(nn, 16n), prose.first_le7(sig)))
    case AOct{}:
      Nat.is_le(nn, 21n)
    case ABin{}:
      Nat.is_le(nn, 63n)

# the significant digits after a two-character prefix, against the radix's
# bound
def prose.radix_in_range(rx: ARadix, +cs: List<&2, Char>) -> Bool:
  +sig = prose.sig(List.drop(&2, Char, cs, 2n))
  prose.radix_fits(rx, List.length(&2, Char, sig), sig)

# the range of a prefixed integer, by its radix, or of a dec-int: its digits
# against the limit of its sign
def prose.int_in_range.pick(hx: Bool, oc: Bool, bi: Bool, +cs: List<&2, Char>) -> Bool:
  match hx oc bi:
    case True{} _o _b:
      prose.radix_in_range(AHex{}, cs)
    case False{} True{} _b:
      prose.radix_in_range(AOct{}, cs)
    case False{} False{} True{}:
      prose.radix_in_range(ABin{}, cs)
    case False{} False{} False{}:
      prose.dec_le(abnf.dec_digits(cs), prose.i64.limit(abnf.dec_sign(cs)), EQ{})

# TOML v1.0.0, Integer: "Arbitrary 64-bit signed integers (from -2^63 to
# 2^63-1) should be accepted and handled losslessly. If an integer cannot be
# represented losslessly, an error must be thrown." Over an integer word: a
# dec-int's digits (its sign and underscores removed; unsigned-dec-int has no
# leading zero) against the limit of its sign, and a prefixed one's
# significant digits against 2^63 - 1 in its radix (laws/IntegerReadExactly.bend)
def prose.int_in_range(+cs: List<&2, Char>) -> Bool:
  prose.int_in_range.pick(abnf.hex_int(cs), abnf.oct_int(cs), abnf.bin_int(cs), cs)

# the value of a DIGIT, as a U32
def g.dig(cc: Char) -> U32:
  U32.sub(Char.to_u32(cc), 48)

# the number two DIGITs at the front of a word write
def g.two(cs: List<&2, Char>) -> U32:
  match cs:
    case aa <> bb <> _rest:
      U32.add(U32.mul(g.dig(aa), 10), g.dig(bb))
    case _:
      0

# the number four DIGITs at the front of a word write
def g.four(cs: List<&2, Char>) -> U32:
  match cs:
    case aa <> bb <> cc <> dd <> _rest:
      U32.add(U32.mul(U32.add(U32.mul(U32.add(U32.mul(g.dig(aa), 10), g.dig(bb)), 10), g.dig(cc)), 10),
        g.dig(dd))
    case _:
      0

# the word's leading DIGITs
def g.take_digits.pick(dg: Bool, hh: Char, after: List<&2, Char>) -> List<&2, Char>:
  match dg:
    case True{}:
      hh <> after
    case False{}:
      []

# the word's leading DIGITs
def g.take_digits(cs: List<&2, Char>) -> List<&2, Char>:
  match cs:
    case []:
      []
    case +hh <> tt:
      g.take_digits.pick(abnf.DIGIT(hh), hh, g.take_digits(tt))

# Z, or an offset of the sign minus when mm, else plus
def g.dt.zone.pick(mm: Bool, zz: Bool, +tt: List<&2, Char>) -> T.Zone:
  match zz:
    case True{}:
      T.Zulu{}
    case False{}:
      T.Shift{abnf.sign.pick(mm), g.two(tt), g.two(List.drop(&2, Char, tt, 3n))}

# the time-offset at the front of a word: Z or z, or a sign, two digits, a
# colon and two digits
def g.dt.zone(cs: List<&2, Char>) -> T.Zone:
  match cs:
    case +hh <> +tt:
      g.dt.zone.pick(abnf.cp(hh, 45), Bool.or(abnf.cp(hh, 90), abnf.cp(hh, 122)), tt)
    case []:
      T.Zulu{}

# the digits after a ".", or none
def g.dt.frac.pick(dot: Bool, tt: List<&2, Char>) -> String:
  match dot:
    case True{}:
      String.from_list(g.take_digits(tt))
    case False{}:
      ""

# the fraction's digits after a partial-time's seconds, "" when the word goes
# on with no ".", and the rest after them
def g.dt.frac(cs: List<&2, Char>) -> String:
  match cs:
    case +hh <> tt:
      g.dt.frac.pick(abnf.cp(hh, 46), tt)
    case []:
      ""

# the word after "." and its digits, or the word as it is
def g.dt.after_frac.pick(dot: Bool, hh: Char, tt: List<&2, Char>) -> List<&2, Char>:
  match dot:
    case True{}:
      abnf.drop_digits(tt)
    case False{}:
      hh <> tt

# what follows the fraction, if there is one
def g.dt.after_frac(cs: List<&2, Char>) -> List<&2, Char>:
  match cs:
    case +hh <> +tt:
      g.dt.after_frac.pick(abnf.cp(hh, 46), hh, tt)
    case []:
      []

# the partial-time at the front of a word: hour, minute, second, fraction
def g.dt.clock(+cs: List<&2, Char>) -> T.Clock:
  T.Clock{g.two(cs), g.two(List.drop(&2, Char, cs, 3n)), g.two(List.drop(&2, Char, cs, 6n)),
    g.dt.frac(List.drop(&2, Char, cs, 8n))}

# the full-date at the front of a word: year, month, day
def g.dt.date(+cs: List<&2, Char>) -> T.Date:
  T.Date{g.four(cs), g.two(List.drop(&2, Char, cs, 5n)), g.two(List.drop(&2, Char, cs, 8n))}

# a word's third character, or U+0000
def g.dt.third(cs: List<&2, Char>) -> Char:
  match cs:
    case _a <> _b <> cc <> _rest:
      cc
    case _:
      Chr{0}

# a local-date-time when nothing follows the partial-time, and an
# offset-date-time with the time-offset that does
def g.dt.zoned(date: T.Date, clock: T.Clock, +zz: List<&2, Char>) -> T.When:
  match zz:
    case []:
      T.WLocal{date, clock}
    case _h <> _t:
      T.WOff{date, clock, g.dt.zone(zz)}

# a local-time, a local-date, or a date with a time after it
def g.dt.when.pick(colon: Bool, +cs: List<&2, Char>, +tm: List<&2, Char>, dateonly: Bool) -> T.When:
  match colon dateonly:
    case True{} _d:
      T.WTime{g.dt.clock(cs)}
    case False{} True{}:
      T.WDate{g.dt.date(cs)}
    case False{} False{}:
      g.dt.zoned(g.dt.date(cs), g.dt.clock(tm), g.dt.after_frac(List.drop(&2, Char, tm, 8n)))

# the datetime a date-time word writes: a local-time when its third
# character is ":", and otherwise a full-date, then nothing (a local-date), or
# a time-delim, a partial-time and a time-offset or nothing
def g.dt.when(+cs: List<&2, Char>) -> T.When:
  g.dt.when.pick(abnf.cp(g.dt.third(cs), 58), cs, List.drop(&2, Char, cs, 11n),
    List.is_empty(&2, Char, List.drop(&2, Char, cs, 10n)))

# the month the test names when it holds, and the other otherwise
def prose.month.pick(hit: Bool, mm: Month, other: Month) -> Month:
  match hit:
    case True{}:
      mm
    case False{}:
      other

# the month a number from 1 to 12 names (January otherwise; the range check
# asks for 1 to 12 first)
def prose.month(+mo: U32) -> Month:
  prose.month.pick(U32.is_eq(mo, 2), Feb{}, prose.month.pick(U32.is_eq(mo, 3), Mar{},
    prose.month.pick(U32.is_eq(mo, 4), Apr{}, prose.month.pick(U32.is_eq(mo, 5), May{},
    prose.month.pick(U32.is_eq(mo, 6), Jun{}, prose.month.pick(U32.is_eq(mo, 7), Jul{},
    prose.month.pick(U32.is_eq(mo, 8), Aug{}, prose.month.pick(U32.is_eq(mo, 9), Sep{},
    prose.month.pick(U32.is_eq(mo, 10), Oct{}, prose.month.pick(U32.is_eq(mo, 11), Nov{},
    prose.month.pick(U32.is_eq(mo, 12), Dec{}, Jan{})))))))))))

# a full-date in range: month 1 to 12, day 1 to the days of its month in its
# year (RFC 3339, section 5.7, as days_in transcribes it)
def prose.date_ok(dd: T.Date) -> Bool:
  match dd:
    case T.Date{+yy, +mo, +dy}:
      Bool.and(abnf.range(mo, 1, 12), Bool.and(U32.is_ge(dy, 1), U32.is_le(dy, days_in(yy, prose.month(mo)))))

# a partial-time in range: hour 0 to 23, minute 0 to 59, second 0 to 60
def prose.clock_ok(cl: T.Clock) -> Bool:
  match cl:
    case T.Clock{hh, mi, ss, _frac}:
      Bool.and(U32.is_le(hh, 23), Bool.and(U32.is_le(mi, 59), U32.is_le(ss, 60)))

# a time-offset in range: hours 0 to 23 and minutes 0 to 59
def prose.zone_ok(zz: T.Zone) -> Bool:
  match zz:
    case T.Zulu{}:
      True{}
    case T.Shift{_sign, hh, mi}:
      Bool.and(U32.is_le(hh, 23), U32.is_le(mi, 59))

# every field of a datetime in range
def prose.when_ok(ww: T.When) -> Bool:
  match ww:
    case T.WOff{date, clock, zone}:
      Bool.and(prose.date_ok(date), Bool.and(prose.clock_ok(clock), prose.zone_ok(zone)))
    case T.WLocal{date, clock}:
      Bool.and(prose.date_ok(date), prose.clock_ok(clock))
    case T.WDate{date}:
      prose.date_ok(date)
    case T.WTime{clock}:
      prose.clock_ok(clock)

# toml.abnf gives RFC 3339's ranges only in comments (date-month ; 01-12,
# date-mday ; 01-28, 01-29, 01-30, 01-31 based on month/year, time-hour ;
# 00-23, time-minute ; 00-59, time-second ; 00-58, 00-59, 00-60 based on leap
# second rules), and TOML v1.0.0 asks for RFC 3339 datetimes. Over a
# date-time word: every field within its range (laws/DateTimeReadExactly.bend)
def prose.date_time_in_range(+cs: List<&2, Char>) -> Bool:
  prose.when_ok(g.dt.when(cs))

# TOML v1.0.0, String: "Any Unicode character may be escaped with the \uXXXX
# or \UXXXXXXXX forms. The escape codes must be valid Unicode scalar values."
# A \u or \U escape's digits name a scalar value (k3.scalar)
def prose.escape_scalar(pp: D5.KPiece) -> Bool:
  match pp:
    case D5.KpChar{_cc}:
      True{}
    case D5.KpEsc{_mm}:
      True{}
    case D5.KpU4{dd, cc, bb, aa}:
      D5.k3.scalar(D5.k3.hex4(dd, cc, bb, aa))
    case D5.KpU8{hh, gg, ff, ee, dd, cc, bb, aa}:
      D5.k3.scalar(D5.k3.hex8(hh, gg, ff, ee, dd, cc, bb, aa))

# every escape of a basic string's pieces names a scalar value
def prose.escapes_scalar(ps: List<&2, D5.KPiece>) -> Bool:
  match ps:
    case []:
      True{}
    case pp <> rest:
      Bool.and(prose.escape_scalar(pp), prose.escapes_scalar(rest))

# every escape of a multi-line basic body names a scalar value
def prose.mlb_escapes_scalar(ps: List<&2, D4.GMlb>) -> Bool:
  match ps:
    case []:
      True{}
    case D4.GmChar{kp} <> rest:
      Bool.and(prose.escape_scalar(kp), prose.mlb_escapes_scalar(rest))
    case _pp <> rest:
      prose.mlb_escapes_scalar(rest)

# TOML v1.0.0, Comment: "Control characters other than tab (U+0000 to
# U+0008, U+000A to U+001F, U+007F) are not permitted in comments."
# non-eol already leaves out every control but U+007F (%x7F is 127)
def prose.comment_char(cc: Char) -> Bool:
  Bool.not(abnf.cp(cc, 127))

# no character of a comment is U+007F
def prose.comment_chars(ss: String) -> Bool:
  match ss:
    case SNil{}:
      True{}
    case SCon{hh, tt}:
      Bool.and(prose.comment_char(hh), prose.comment_chars(tt))

# simple-key = quoted-key / unquoted-key
# quoted-key = basic-string / literal-string
# unquoted-key = 1*( ALPHA / DIGIT / %x2D / %x5F ) ; A-Z / a-z / 0-9 / - / _
# (abnf.unquoted_key, laws/BareKey.bend), with the escape restriction on a basic one
def g.ok.seg(sg: D5.KSeg) -> Bool:
  match sg:
    case D5.KsBare{name}:
      D2.abnf.unquoted_key(name)
    case D5.KsBasic{+pl}:
      Bool.and(abnf.basic_string(pl), prose.escapes_scalar(pl))
    case D5.KsLit{name}:
      abnf.literal_string(name)

# 1*( dot-sep simple-key )'s every part; at least one is the key's own test
def g.ok.dots(ds: List<&2, D4.GDotSep>) -> Bool:
  match ds:
    case []:
      True{}
    case D4.GDotSep{w1, w2, sk} <> rest:
      Bool.and(D1.abnf.ws(w1), Bool.and(D1.abnf.ws(w2), Bool.and(g.ok.seg(sk), g.ok.dots(rest))))

# key = simple-key / dotted-key: a dotted key has at least one dot-sep
def g.ok.key(kk: D4.GKey) -> Bool:
  match kk:
    case D4.GSimpleKey{sk}:
      g.ok.seg(sk)
    case D4.GDottedKey{sk, +more}:
      Bool.and(Bool.not(List.is_empty(&2, D4.GDotSep, more)), Bool.and(g.ok.seg(sk), g.ok.dots(more)))

# the names of a key's segments, in order
def g.dots.names(ds: List<&2, D4.GDotSep>) -> List<&2, String>:
  match ds:
    case []:
      []
    case D4.GDotSep{_w1, _w2, sk} <> rest:
      D5.k3.seg.name(sk) <> g.dots.names(rest)

# the names of a key's segments, in order: each its characters, a basic
# one's escapes decoded
def g.key.names(kk: D4.GKey) -> List<&2, String>:
  match kk:
    case D4.GSimpleKey{sk}:
      [D5.k3.seg.name(sk)]
    case D4.GDottedKey{sk, more}:
      D5.k3.seg.name(sk) <> g.dots.names(more)

# which of the mutually recursive rules a GVal node spells
type GRule is Data:
  RVal{}
  RArrayValues{}
  RInlineTableKeyvals{}
  RKeyval{}

# A leading byte-order mark.

# the rest after a byte-order mark, or the text as it is
def bom.drop.pick(bom: Bool, hh: Char, tt: String) -> String:
  match bom:
    case True{}:
      tt
    case False{}:
      SCon{hh, tt}

# the text with one leading U+FEFF taken off: the encoding's signature, not
# text (REVIEW-G1); toml-test's valid utf8-bom cases start with one
# (65279 is %xFEFF)
def bom.drop(ss: String) -> String:
  match ss:
    case SNil{}:
      SNil{}
    case SCon{+hh, tt}:
      bom.drop.pick(abnf.cp(hh, 65279), hh, tt)

# g.ok: every leaf matches its rule and keeps the prose's restrictions.

# [ comment ]: a comment's characters are non-eol, and none is U+007F
def g.ok.com(cm: D4.GCom) -> Bool:
  match cm:
    case D4.GcNone{}:
      True{}
    case D4.GcSome{+body}:
      Bool.and(abnf.comment(body), prose.comment_chars(body))

# ws-comment-newline = *( wschar / [ comment ] newline )
def g.ok.wcn(ws: List<&2, D4.GWcn>) -> Bool:
  match ws:
    case []:
      True{}
    case D4.GwWschar{cc} <> rest:
      Bool.and(D1.abnf.wschar(cc), g.ok.wcn(rest))
    case D4.GwNewline{com, nl} <> rest:
      Bool.and(g.ok.com(com), Bool.and(abnf.newline(nl), g.ok.wcn(rest)))

# a string of its form, with the escape restriction on a basic one's
def g.ok.str(st: D4.GString) -> Bool:
  match st:
    case D4.GsMlBasic{nl, +body}:
      Bool.and(abnf.opt_newline(nl), Bool.and(abnf.ml_basic_body(body, False{}), prose.mlb_escapes_scalar(body)))
    case D4.GsBasic{+pl}:
      Bool.and(abnf.basic_string(pl), prose.escapes_scalar(pl))
    case D4.GsMlLiteral{nl, body}:
      Bool.and(abnf.opt_newline(nl), abnf.ml_literal_body(body, False{}))
    case D4.GsLiteral{text}:
      abnf.literal_string(text)

# whether a GVal node spells the rule the mode names, every leaf in it
# matching its rule: a bare value's word matches its rule (an integer within
# signed 64 bits, a date-time within RFC 3339's ranges), and every part is
# of the rule its place asks for
def g.ok.val(vv: D4.GVal, md: GRule) -> Bool:
  match vv md:
    case D4.GvString{st} RVal{}:
      g.ok.str(st)
    case D4.GvBoolean{+cs} RVal{}:
      D2.abnf.boolean(cs)
    case D4.GvArrayEmpty{wn} RVal{}:
      g.ok.wcn(wn)
    case D4.GvArray{vals, wn} RVal{}:
      Bool.and(g.ok.val(vals, RArrayValues{}), g.ok.wcn(wn))
    case D4.GvInlineTableEmpty{w1, w2} RVal{}:
      Bool.and(D1.abnf.ws(w1), D1.abnf.ws(w2))
    case D4.GvInlineTable{w1, kvs, w2} RVal{}:
      Bool.and(D1.abnf.ws(w1), Bool.and(g.ok.val(kvs, RInlineTableKeyvals{}), D1.abnf.ws(w2)))
    case D4.GvDateTime{+cs} RVal{}:
      Bool.and(abnf.date_time(cs), prose.date_time_in_range(cs))
    case D4.GvFloat{+cs} RVal{}:
      abnf.float(cs)
    case D4.GvInteger{+cs} RVal{}:
      Bool.and(abnf.integer(cs), prose.int_in_range(cs))
    case D4.GArrayValues{wa, val, wb, rest} RArrayValues{}:
      Bool.and(g.ok.wcn(wa), Bool.and(g.ok.val(val, RVal{}), Bool.and(g.ok.wcn(wb),
        g.ok.val(rest, RArrayValues{}))))
    case D4.GArrayValuesLast{wa, val, wb, _sep} RArrayValues{}:
      Bool.and(g.ok.wcn(wa), Bool.and(g.ok.val(val, RVal{}), g.ok.wcn(wb)))
    case D4.GInlineTableKeyvals{kv, w1, w2, rest} RInlineTableKeyvals{}:
      Bool.and(g.ok.val(kv, RKeyval{}), Bool.and(D1.abnf.ws(w1), Bool.and(D1.abnf.ws(w2),
        g.ok.val(rest, RInlineTableKeyvals{}))))
    case D4.GInlineTableKeyvalsLast{kv} RInlineTableKeyvals{}:
      g.ok.val(kv, RKeyval{})
    case D4.GKeyval{key, w1, w2, val} RKeyval{}:
      Bool.and(g.ok.key(key), Bool.and(D1.abnf.ws(w1), Bool.and(D1.abnf.ws(w2), g.ok.val(val, RVal{}))))
    case _v _m:
      False{}

# a table header's key and ws
def g.ok.table(tb: D4.GTable) -> Bool:
  match tb:
    case D4.GStdTable{w1, key, w2}:
      Bool.and(D1.abnf.ws(w1), Bool.and(g.ok.key(key), D1.abnf.ws(w2)))
    case D4.GArrayTable{w1, key, w2}:
      Bool.and(D1.abnf.ws(w1), Bool.and(g.ok.key(key), D1.abnf.ws(w2)))

# an expression's parts
def g.ok.expr(ex: D4.GExpr) -> Bool:
  match ex:
    case D4.GxBlank{w1, com}:
      Bool.and(D1.abnf.ws(w1), g.ok.com(com))
    case D4.GxKeyval{w1, kv, w2, com}:
      Bool.and(D1.abnf.ws(w1), Bool.and(g.ok.val(kv, RKeyval{}), Bool.and(D1.abnf.ws(w2), g.ok.com(com))))
    case D4.GxTable{w1, tb, w2, com}:
      Bool.and(D1.abnf.ws(w1), Bool.and(g.ok.table(tb), Bool.and(D1.abnf.ws(w2), g.ok.com(com))))

# each newline and expression after the first
def g.ok.lines(ls: List<&2, D4.GLine>) -> Bool:
  match ls:
    case []:
      True{}
    case D4.GLine{nl, ex} <> rest:
      Bool.and(abnf.newline(nl), Bool.and(g.ok.expr(ex), g.ok.lines(rest)))

# whether every part of a derivation spells its rule
def g.ok(dd: D4.Gd) -> Bool:
  match dd:
    case D4.GToml{first, rest}:
      Bool.and(g.ok.expr(first), g.ok.lines(rest))

# g.val: what a value derivation denotes, as parse stores it.

# the characters a multi-line body starts with are trimmed: the first newline
# (right after the opening delimiter, TFirst), or all whitespace and newlines
# (after a line-ending backslash, TAll), or none
type GTrim is Data:
  TNone{}
  TFirst{}
  TAll{}

# a whitespace character dropped, or any other kept
def g.mlb.char.pick(drop: Bool, cc: Char, rest: String) -> String:
  match drop:
    case True{}:
      rest
    case False{}:
      SCon{cc, rest}

# a character written as itself: dropped while whitespace is trimmed
def g.mlb.char(tm: GTrim, +cc: Char, rest: String) -> String:
  match tm:
    case TAll{}:
      g.mlb.char.pick(D1.abnf.wschar(cc), cc, rest)
    case TFirst{}:
      SCon{cc, rest}
    case TNone{}:
      SCon{cc, rest}

# whitespace keeps the trim going, and anything else ends it
def g.mlb.char.trim.pick(ws: Bool) -> GTrim:
  match ws:
    case True{}:
      TAll{}
    case False{}:
      TNone{}

# the trim that goes on after a character written as itself: whitespace
# goes on being trimmed after a line-ending backslash, and nothing else does
def g.mlb.char.trim(tm: GTrim, +cc: Char) -> GTrim:
  match tm:
    case TAll{}:
      g.mlb.char.trim.pick(D1.abnf.wschar(cc))
    case TFirst{}:
      TNone{}
    case TNone{}:
      TNone{}

# a newline written as itself: dropped when trimmed, kept as written
# otherwise, LF or CRLF (REVIEW-G9)
def g.nl.char(tm: GTrim, nl: String, rest: String) -> String:
  match tm:
    case TAll{}:
      rest
    case TFirst{}:
      rest
    case TNone{}:
      String.append(nl, rest)

# the trim after a newline: whitespace after a backslash goes on being
# trimmed; the first newline is trimmed only once
def g.nl.trim(tm: GTrim) -> GTrim:
  match tm:
    case TAll{}:
      TAll{}
    case TFirst{}:
      TNone{}
    case TNone{}:
      TNone{}

# the characters a multi-line basic body stands for, with the specification's
# prose: "A newline immediately following the opening delimiter will be
# trimmed", whichever part of the derivation holds it, and "When the last
# non-whitespace character on a line is an unescaped \, it will be trimmed
# along with all whitespace (including newlines) up to the next
# non-whitespace character or closing delimiter". An escape stands for its
# character, a newline for itself as written (REVIEW-G9), and quotes for
# themselves
def g.mlb.chars(ps: List<&2, D4.GMlb>, +tm: GTrim) -> String:
  match ps:
    case []:
      ""
    case D4.GmChar{D5.KpChar{+cc}} <> rest:
      g.mlb.char(tm, cc, g.mlb.chars(rest, g.mlb.char.trim(tm, cc)))
    case D4.GmChar{kp} <> rest:
      SCon{D5.k3.pc.char(kp), g.mlb.chars(rest, TNone{})}
    case D4.GmNewline{nl} <> rest:
      g.nl.char(tm, nl, g.mlb.chars(rest, g.nl.trim(tm)))
    case D4.GmEscapedNl{_w1, _nl, _more} <> rest:
      g.mlb.chars(rest, TAll{})
    case D4.GmQuotes{two} <> rest:
      D4.g.quotes.text(two, '"', g.mlb.chars(rest, TNone{}))

# the characters a multi-line literal body stands for: itself, but a newline
# right after the opening delimiter
def g.mll.chars(ps: List<&2, D4.GMll>, +tm: GTrim) -> String:
  match ps:
    case []:
      ""
    case D4.GlChar{cc} <> rest:
      SCon{cc, g.mll.chars(rest, TNone{})}
    case D4.GlNewline{nl} <> rest:
      g.nl.char(tm, nl, g.mll.chars(rest, g.nl.trim(tm)))
    case D4.GlQuotes{two} <> rest:
      D4.g.quotes.text(two, '\'', g.mll.chars(rest, TNone{}))

# the trim a multi-line body starts with: none after a newline right after
# the delimiter, which is dropped, and the first newline otherwise
def g.first.trim(nl: String) -> GTrim:
  match nl:
    case SNil{}:
      TFirst{}
    case SCon{_h, _t}:
      TNone{}

# the characters a string stands for
def g.str.chars(st: D4.GString) -> String:
  match st:
    case D4.GsMlBasic{nl, body}:
      g.mlb.chars(body, g.first.trim(nl))
    case D4.GsBasic{pl}:
      D5.k3.pcs.name(pl)
    case D4.GsMlLiteral{nl, body}:
      g.mll.chars(body, g.first.trim(nl))
    case D4.GsLiteral{text}:
      text

# whether a value is a string, owned or a span, of the characters
def g.str.is(vv: T.Val, text: String) -> Bool:
  match vv:
    case T.VStr{tx}:
      String.eq(tx, text)
    case T.VSpan{src, nn}:
      String.eq(T.string(T.VSpan{src, nn}), text)
    case _:
      False{}

# a digit's value, an upper case letter's, or a lower case one's
def g.hexdig.val.pick(dg: Bool, up: Bool, +cp: U32) -> Nat:
  match dg up:
    case True{} _u:
      U32.to_nat(U32.sub(cp, 48))
    case False{} True{}:
      U32.to_nat(U32.sub(cp, 55))
    case False{} False{}:
      U32.to_nat(U32.sub(cp, 87))

# the value of a HEXDIG, which a DIGIT is: its digit, or a letter's 10 to 15
# in either case
def g.hexdig.val(cc: Char) -> Nat:
  match cc:
    case Chr{+cp}:
      g.hexdig.val.pick(D2.abnf.digit(cp), abnf.range(cp, 65, 70), cp)

# an underscore leaves the value as it is; a digit is one more place
def g.num.nat.step(us: Bool, hh: Char, +radix: Nat, acc: Nat) -> Nat:
  match us:
    case True{}:
      acc
    case False{}:
      Nat.add(Nat.mul(acc, radix), g.hexdig.val(hh))

# the value of a numeral's digits in a radix, the most significant first,
# its underscores skipped; acc is the value of the digits before
def g.num.nat(cs: List<&2, Char>, +radix: Nat, acc: Nat) -> Nat:
  match cs:
    case []:
      acc
    case +hh <> tt:
      g.num.nat(tt, radix, g.num.nat.step(abnf.underscore(hh), hh, radix, acc))

# whether every character of a string is a DIGIT
def g.dec.all(ss: String) -> Bool:
  match ss:
    case SNil{}:
      True{}
    case SCon{hh, tt}:
      Bool.and(abnf.DIGIT(hh), g.dec.all(tt))

# whether a string is decimal digits with no leading zero, or 0 alone
def g.dec.canon(ss: String) -> Bool:
  match ss:
    case SNil{}:
      False{}
    case SCon{+hh, +tt}:
      Bool.and(abnf.DIGIT(hh), Bool.or(Bool.and(abnf.cp(hh, 48), String.is_empty(tt)),
        Bool.and(abnf.digit1_9(hh), g.dec.all(tt))))

# the radix of the prefix that matched, or 10
def g.int.radix.pick(hx: Bool, oc: Bool, bi: Bool) -> Nat:
  match hx oc bi:
    case True{} _o _b:
      16n
    case False{} True{} _b:
      8n
    case False{} False{} True{}:
      2n
    case False{} False{} False{}:
      10n

# an integer word's radix: 16, 8 or 2 after its prefix, and 10 for a dec-int
def g.int.radix(+cs: List<&2, Char>) -> Nat:
  g.int.radix.pick(abnf.hex_int(cs), abnf.oct_int(cs), abnf.bin_int(cs))

# the digits after a two-character prefix, or after a dec-int's sign
def g.int.body.pick(pre: Bool, cs: List<&2, Char>) -> List<&2, Char>:
  match pre:
    case True{}:
      List.drop(&2, Char, cs, 2n)
    case False{}:
      String.to_list(abnf.dec_digits(cs))

# an integer word's digits: after the prefix, or after a dec-int's sign
def g.int.body(+cs: List<&2, Char>) -> List<&2, Char>:
  g.int.body.pick(Bool.or(abnf.hex_int(cs), Bool.or(abnf.oct_int(cs), abnf.bin_int(cs))), cs)

# an integer word denotes a sign, minus for a dec-int that starts with one
# and plus otherwise, and a value, written as decimal digits with no leading
# zero: those digits' value in base 10 is the numeral's in its radix, both
# as Nats. It is a relation, not computed, since a Nat is not evaluated
def g.int.is(vv: T.Val, +cs: List<&2, Char>) -> Bool:
  match vv:
    case T.VInt{sign, +digits}:
      Bool.and(D3.sign.eq(sign, abnf.dec_sign(cs)), Bool.and(g.dec.canon(digits),
        Nat.is_eq(g.num.nat(String.to_list(digits), 10n, 0n), g.num.nat(g.int.body(cs), g.int.radix(cs), 0n))))
    case _:
      False{}

# a float word denotes its sign, minus when it starts with one and plus
# otherwise, and its spelling with the sign and every underscore removed
# (abnf.dec_sign and abnf.dec_digits read any word that way)
def g.flo.is(vv: T.Val, +cs: List<&2, Char>) -> Bool:
  match vv:
    case T.VFlo{sign, text}:
      Bool.and(D3.sign.eq(sign, abnf.dec_sign(cs)), String.eq(text, abnf.dec_digits(cs)))
    case _:
      False{}

# a boolean word denotes its bit: true for true
def g.bool.is(vv: T.Val, cs: List<&2, Char>) -> Bool:
  match vv:
    case T.VBool{bit}:
      D3.bit.eq(bit, D2.abnf.true(cs))
    case _:
      False{}

# a date-time word denotes its form and fields
def g.when.is(vv: T.Val, cs: List<&2, Char>) -> Bool:
  match vv:
    case T.VWhen{when}:
      D3.when.eq(when, g.dt.when(cs))
    case _:
      False{}

# what g.val.go compares a node against: a value (GMVal), none (GMMiss, a
# lookup that found nothing, which no value derivation denotes), an array's
# items for its array-values (GMItems), or an inline table's rows for its
# keyvals (GMRows)
type GMode is Data:
  GMVal{val: T.Val}
  GMMiss{}
  GMItems{items: List<&2, T.Val>}
  GMRows{rows: List<&2, T.Val>}

# the mode for what a lookup found
def g.hit.mode(hh: T.Hit) -> GMode:
  match hh:
    case T.Found{vv}:
      GMVal{vv}
    case T.Miss{}:
      GMMiss{}

# the key paths of an inline table's keyvals
def g.kv.paths(vv: D4.GVal) -> List<&2, List<&2, String>>:
  match vv:
    case D4.GInlineTableKeyvals{D4.GKeyval{key, _w1, _w2, _v}, _a, _b, rest}:
      g.key.names(key) <> g.kv.paths(rest)
    case D4.GInlineTableKeyvalsLast{D4.GKeyval{key, _w1, _w2, _v}}:
      [g.key.names(key)]
    case _:
      []

# whether two key paths are one
def g.path.eq(aa: List<&2, String>, bb: List<&2, String>) -> Bool:
  match aa bb:
    case Nil{} Nil{}:
      True{}
    case +xx <> xt +yy <> yt:
      Bool.and(String.eq(xx, yy), g.path.eq(xt, yt))
    case _a _b:
      False{}

# whether a path is one of the paths
def g.path.in(+pp: List<&2, String>, ps: List<&2, List<&2, String>>) -> Bool:
  match ps:
    case []:
      False{}
    case qq <> rest:
      Bool.or(g.path.eq(pp, qq), g.path.in(pp, rest))

# whether a path lies strictly under another: it is longer and starts with it
def g.path.under(pp: List<&2, String>, at: List<&2, String>) -> Bool:
  match pp at:
    case Nil{} _a:
      False{}
    case _x <> _t Nil{}:
      True{}
    case xx <> xt yy <> yt:
      Bool.and(String.eq(xx, yy), g.path.under(xt, yt))

# whether some path lies strictly under the path
def g.path.above(+at: List<&2, String>, ps: List<&2, List<&2, String>>) -> Bool:
  match ps:
    case []:
      False{}
    case qq <> rest:
      Bool.or(g.path.under(qq, at), g.path.above(at, rest))

# a table's own paths when a keyval's path lies under it, and its path as one
# value otherwise
def g.leaf.pick(
  above: Bool,
  inner: List<&2, List<&2, String>>,
  at: List<&2, String>,
  rest: List<&2, List<&2, String>>
) -> List<&2, List<&2, String>>:
  match above:
    case True{}:
      List.append(&2, List<&2, String>, inner, rest)
    case False{}:
      at <> rest

# the paths from an inline table's rows to the values in it, entering a
# table (an inline table, as parse seals every table in one) exactly when the
# path of one of the keyvals ps lies under it: a table dotted keys made. A row
# that is no pair, which no inline table holds, counts as a value at the empty
# path, which no keyval has
def g.leaf.paths(
  rows: List<&2, T.Val>,
  +at: List<&2, String>,
  +ps: List<&2, List<&2, String>>
) -> List<&2, List<&2, String>>:
  match rows:
    case []:
      []
    case T.VPair{+nn, T.VInl{sub}} <> +tt:
      +pp = List.append(&2, String, at, [nn])
      g.leaf.pick(g.path.above(pp, ps), g.leaf.paths(sub, pp, ps), pp, g.leaf.paths(tt, at, ps))
    case T.VPair{+nn, _v} <> +tt:
      List.append(&2, String, at, [nn]) <> g.leaf.paths(tt, at, ps)
    case _v <> tt:
      Nil{} <> g.leaf.paths(tt, at, ps)

# whether every path of the first list is one of the second
def g.paths.within(ps: List<&2, List<&2, String>>, +qs: List<&2, List<&2, String>>) -> Bool:
  match ps:
    case []:
      True{}
    case pp <> rest:
      Bool.and(g.path.in(pp, qs), g.paths.within(rest, qs))

# whether an inline table's rows hold its keyvals' values and nothing else:
# as many values as keyvals, each at one of their paths, with only the tables
# dotted keys make on the way
def g.inl.only(+rows: List<&2, T.Val>, kvs: D4.GVal) -> Bool:
  +ps = g.kv.paths(kvs)
  +ls = g.leaf.paths(rows, [], ps)
  Bool.and(Nat.is_eq(List.length(&2, List<&2, String>, ls), List.length(&2, List<&2, String>, ps)),
    g.paths.within(ls, ps))

# whether a GVal node denotes what the mode holds: a string its characters
# (owned or a span), an integer, float, boolean or date-time word its value,
# an array its items in order, and an inline table the table its keyvals
# make: each keyval's value where `at` finds its key, and nothing else
def g.val.go(vv: D4.GVal, md: GMode) -> Bool:
  match vv md:
    case D4.GvString{st} GMVal{val}:
      g.str.is(val, g.str.chars(st))
    case D4.GvBoolean{cs} GMVal{val}:
      g.bool.is(val, cs)
    case D4.GvArrayEmpty{_wn} GMVal{T.VArr{items}}:
      List.is_empty(&2, T.Val, items)
    case D4.GvArray{vals, _wn} GMVal{T.VArr{items}}:
      g.val.go(vals, GMItems{items})
    case D4.GvInlineTableEmpty{_w1, _w2} GMVal{T.VInl{rows}}:
      List.is_empty(&2, T.Val, rows)
    case D4.GvInlineTable{_w1, +kvs, _w2} GMVal{T.VInl{+rows}}:
      Bool.and(g.val.go(kvs, GMRows{rows}), g.inl.only(rows, kvs))
    case D4.GvDateTime{cs} GMVal{val}:
      g.when.is(val, cs)
    case D4.GvFloat{cs} GMVal{val}:
      g.flo.is(val, cs)
    case D4.GvInteger{cs} GMVal{val}:
      g.int.is(val, cs)
    case D4.GArrayValues{_wa, val, _wb, rest} GMItems{it <> its}:
      Bool.and(g.val.go(val, GMVal{it}), g.val.go(rest, GMItems{its}))
    case D4.GArrayValuesLast{_wa, val, _wb, _sep} GMItems{it <> its}:
      Bool.and(g.val.go(val, GMVal{it}), List.is_empty(&2, T.Val, its))
    case D4.GInlineTableKeyvals{kv, _w1, _w2, rest} GMRows{+rows}:
      Bool.and(g.val.go(kv, GMRows{rows}), g.val.go(rest, GMRows{rows}))
    case D4.GInlineTableKeyvalsLast{kv} GMRows{rows}:
      g.val.go(kv, GMRows{rows})
    case D4.GKeyval{key, _w1, _w2, val} GMRows{rows}:
      g.val.go(val, g.hit.mode(T.at(rows, g.key.names(key))))
    case _v _m:
      False{}

# whether a value derivation denotes the value
def g.val(vv: D4.GVal, val: T.Val) -> Bool:
  g.val.go(vv, GMVal{val})

# defs: the definition rules of TOML v1.0.0's prose, which laws/DefinesEachTableOnce.bend
# states, over a derivation's expressions in order. A record says what each
# key path (the names of its segments, from the root) holds; each keyval and
# header reads it and adds to it, and the first rule broken fails the whole.

# what a key path holds, as the rules tell kinds apart: nothing yet; a key's
# value (a string, number, boolean, datetime, array or inline table); a table
# a [table] header named; a table a header only passed through on its way; a
# table dotted keys made, or entered after a header only passed through it;
# an array of tables
type DKind is Data:
  DAbsent{}
  DValue{}
  DHeader{}
  DPassed{}
  DDotted{}
  DArrayOfTables{}

# a path and what it holds
type DEnt is Data:
  DEnt{path: List<&2, String>, kind: DKind}

# the record so far, newest first, and the table the lines are in; or a rule
# broken
type DSt is Data:
  DOk{ents: List<&2, DEnt>, here: List<&2, String>}
  DFail{}

# what defines a path: a keyval's key, a [table] header, or an [[array]]
# header
type DJob is Data:
  DjKey{}
  DjStd{}
  DjAot{}

# what a key or header does with a table on its way to the path it defines:
# go on through it, record it as the kind and go on, or break a rule
type DStep is Data:
  DsGo{}
  DsMake{kind: DKind}
  DsBreak{}

# the newest entry's kind when it is for the path, and the older ones'
# otherwise
def defs.kind.pick(hit: Bool, kk: DKind, other: DKind) -> DKind:
  match hit:
    case True{}:
      kk
    case False{}:
      other

# what a path holds: its newest entry's kind, or DAbsent
def defs.kind(ents: List<&2, DEnt>, +pp: List<&2, String>) -> DKind:
  match ents:
    case []:
      DAbsent{}
    case DEnt{qq, kk} <> rest:
      defs.kind.pick(g.path.eq(qq, pp), kk, defs.kind(rest, pp))

# an entry kept when it is not under the path
def defs.drop.pick(under: Bool, en: DEnt, rest: List<&2, DEnt>) -> List<&2, DEnt>:
  match under:
    case True{}:
      rest
    case False{}:
      en <> rest

# the record with every path under at taken out
def defs.drop(ents: List<&2, DEnt>, +at: List<&2, String>) -> List<&2, DEnt>:
  match ents:
    case []:
      []
    case DEnt{+qq, kk} <> rest:
      defs.drop.pick(g.path.under(qq, at), DEnt{qq, kk}, defs.drop(rest, at))

# A table on the way to the path a key or header defines. TOML v1.0.0:
# "Dotted keys create and define a table for each key part before the last
# one, provided that such tables were not previously created." "If you
# don't [create a super-table], it will be created implicitly for you."
# "Since tables cannot be defined more than once, redefining such tables
# using a [table] header is not allowed. Likewise, using dotted keys to
# redefine tables already defined in [table] form is not allowed." "Inline
# tables are fully self-contained and define all keys and sub-tables within
# them. Keys and sub-tables cannot be added outside the braces." "Any
# reference to an array of tables points to the most recently defined table
# element of the array." A value is entered by nothing; a table a header
# named or an array of tables is entered by a header, never by a dotted key;
# a table a header passed through is entered by either, and dotted keys that
# enter it make it theirs (REVIEW-G2: open to dotted keys, and then no longer
# to a header naming it, as the code and tomllib do)
def defs.enter(look: DKind, job: DJob) -> DStep:
  match look job:
    case DAbsent{} DjKey{}:
      DsMake{DDotted{}}
    case DAbsent{} _j:
      DsMake{DPassed{}}
    case DValue{} _j:
      DsBreak{}
    case DHeader{} DjKey{}:
      DsBreak{}
    case DHeader{} _j:
      DsGo{}
    case DPassed{} DjKey{}:
      DsMake{DDotted{}}
    case DPassed{} _j:
      DsGo{}
    case DDotted{} _j:
      DsGo{}
    case DArrayOfTables{} DjKey{}:
      DsBreak{}
    case DArrayOfTables{} _j:
      DsGo{}

# The path a key or header defines. TOML v1.0.0: "Defining a key multiple
# times is invalid." "Just as keys, you cannot define a table more than
# once." "The [table] form can, however, be used to define sub-tables within
# tables defined via dotted keys", so a header may name a table it or another
# header only passed through. "Attempting to append to a statically defined
# array, even if that array is empty, must produce an error at parse time."
# "Attempting to define a normal table with the same name as an already
# established array must produce an error at parse time. Attempting to
# redefine a normal table as an array must likewise produce an error at
# parse time." A key's value needs the path free; a [table] header needs it
# free or only passed through, and its lines are in it after; an [[array]]
# header needs it free or an array of tables, and starts a new element,
# which is its own scope for these rules
def defs.last(look: DKind, job: DJob, ents: List<&2, DEnt>, +at: List<&2, String>, here: List<&2, String>) -> DSt:
  match look job:
    case DAbsent{} DjKey{}:
      DOk{DEnt{at, DValue{}} <> ents, here}
    case DAbsent{} DjStd{}:
      DOk{DEnt{at, DHeader{}} <> ents, at}
    case DPassed{} DjStd{}:
      DOk{DEnt{at, DHeader{}} <> ents, at}
    case DAbsent{} DjAot{}:
      DOk{DEnt{at, DArrayOfTables{}} <> ents, at}
    case DArrayOfTables{} DjAot{}:
      DOk{defs.drop(ents, at), at}
    case _l _j:
      DFail{}

# a key's or header's segments after the path at, whose kind is look and
# whose step on the way is st: each segment but the last enters a table,
# and the last is the path defined
def defs.walk(
  names: List<&2, String>,
  +ents: List<&2, DEnt>,
  +at: List<&2, String>,
  look: DKind,
  st: DStep,
  +job: DJob,
  here: List<&2, String>
) -> DSt:
  match names:
    case []:
      defs.last(look, job, ents, at, here)
    case nn <> rest:
      match st:
        case DsBreak{}:
          DFail{}
        case DsGo{}:
          +a2 = List.append(&2, String, at, [nn])
          +k2 = defs.kind(ents, a2)
          defs.walk(rest, ents, a2, k2, defs.enter(k2, job), job, here)
        case DsMake{kk}:
          +e2 = {DEnt{at, kk} <> ents : List<&2, DEnt>}
          +a2 = List.append(&2, String, at, [nn])
          +k2 = defs.kind(e2, a2)
          defs.walk(rest, e2, a2, k2, defs.enter(k2, job), job, here)

# the path a key starts from: the table the lines are in for a keyval's key,
# the root for a header's
def defs.base(job: DJob, here: List<&2, String>) -> List<&2, String>:
  match job:
    case DjKey{}:
      here
    case DjStd{}:
      []
    case DjAot{}:
      []

# a key or a header, of the names of its segments, defined from a record
def defs.key(st: DSt, names: List<&2, String>, +job: DJob) -> DSt:
  match st names:
    case DFail{} _n:
      DFail{}
    case DOk{_e, _h} Nil{}:
      DFail{}
    case DOk{+ents, +here} nn <> rest:
      +a0 = List.append(&2, String, defs.base(job, here), [nn])
      +k0 = defs.kind(ents, a0)
      defs.walk(rest, ents, a0, k0, defs.enter(k0, job), job, here)

# the record as it was when an inner record kept the rules, and a failure
# when it broke one
def defs.keep(inner: DSt, st: DSt) -> DSt:
  match inner:
    case DOk{_e, _h}:
      st
    case DFail{}:
      DFail{}

# a GVal node's definitions: a keyval defines its key in the record; the
# keyvals of an inline table are defined in a record of their own, from the
# empty one, since it is self-contained; and every value in an array or an
# inline table is checked the same way
def defs.go(vv: D4.GVal, st: DSt) -> DSt:
  match vv:
    case D4.GvArray{vals, _wn}:
      defs.go(vals, st)
    case D4.GvInlineTable{_w1, kvs, _w2}:
      defs.keep(defs.go(kvs, DOk{[], []}), st)
    case D4.GArrayValues{_wa, val, _wb, rest}:
      defs.go(rest, defs.go(val, st))
    case D4.GArrayValuesLast{_wa, val, _wb, _sep}:
      defs.go(val, st)
    case D4.GInlineTableKeyvals{kv, _w1, _w2, rest}:
      defs.go(rest, defs.go(kv, st))
    case D4.GInlineTableKeyvalsLast{kv}:
      defs.go(kv, st)
    case D4.GKeyval{key, _w1, _w2, val}:
      defs.keep(defs.go(val, DOk{[], []}), defs.key(st, g.key.names(key), DjKey{}))
    case _v:
      st

# an expression's definitions: a keyval's in the table the lines are in, a
# [table] header's, whose table the lines after it are in, and an [[array]]
# header's
def defs.expr(ex: D4.GExpr, st: DSt) -> DSt:
  match ex:
    case D4.GxBlank{_w1, _com}:
      st
    case D4.GxKeyval{_w1, kv, _w2, _com}:
      defs.go(kv, st)
    case D4.GxTable{_w1, D4.GStdTable{_a, key, _b}, _w2, _com}:
      defs.key(st, g.key.names(key), DjStd{})
    case D4.GxTable{_w1, D4.GArrayTable{_a, key, _b}, _w2, _com}:
      defs.key(st, g.key.names(key), DjAot{})

# the definitions of each expression after the first, in order
def defs.lines(ls: List<&2, D4.GLine>, st: DSt) -> DSt:
  match ls:
    case []:
      st
    case D4.GLine{_nl, ex} <> rest:
      defs.lines(rest, defs.expr(ex, st))

# whether no rule was broken
def defs.ok(st: DSt) -> Bool:
  match st:
    case DOk{_e, _h}:
      True{}
    case DFail{}:
      False{}

# whether a derivation's expressions, in order, break none of the definition
# rules
def defs(dd: D4.Gd) -> Bool:
  match dd:
    case D4.GToml{first, rest}:
      defs.ok(defs.lines(rest, defs.expr(first, DOk{[], []})))

# whether a bare word's reading is the boolean vv: vv's bit is the reading's
def n1.got.bool(gg: T.Got, vv: T.Val) -> Bool:
  match gg vv:
    case T.GotVal{T.VBool{b1}} T.VBool{b2}:
      D3.bit.eq(b2, b1)
    case _g _v:
      False{}

# the document of one pair: a key, " = ", a word and a newline
def bw.kv(kk: String, ww: String) -> String:
  String.append(kk, String.append(" = ", String.append(ww, "\n")))

# the document of one pair whose value is an array of one word
def bw.kva(kk: String, ww: String) -> String:
  String.append(kk, String.append(" = [", String.append(ww, "]\n")))

# the document of one pair whose value is an inline table of one pair, v
def bw.kvi(kk: String, ww: String) -> String:
  String.append(kk, String.append(" = {v = ", String.append(ww, "}\n")))
