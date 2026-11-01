# how a key segment is spelled and the name its characters give
import Base

# how a key segment is spelled: bare, as a basic string the way key writes
# one, or as a literal string
type Spell is Data:
  SpBare{}
  SpBasic{}
  SpLit{}

# a key segment: a name and how it is spelled
type Seg is Data:
  Seg{sp: Spell, name: String}

# a segment of a dotted key that a dot follows, with the blank space before
# the dot and after it (each blank a tab when true, a space when false)
type Dot is Data:
  Dot{seg: Seg, g1: List<&2, Bool>, g2: List<&2, Bool>}

# laws/KeyNameIsItsCharacters.bend: a key's name is its characters however it is written, read from
# every place a key may start. toml.abnf spells a basic string as quotation
# marks around basic-char pieces: basic-unescaped (any character but `"`,
# `\` and the controls other than tab) written as itself, or escaped: a
# backslash and one of `"`, `\`, b, f, n, r, t, or u and four HEXDIG, or U
# and eight. HEXDIG is a digit or a letter A to F, in either case, and the
# escape must name a Unicode scalar value. A basic key segment is a list of
# such pieces, named by the characters they stand for; a key segment is
# that, bare or literal, and a dotted key's segments are joined by dots with
# blank space around them, in a key and in a header alike.

# the letter of a two-character escape
type KMark is Data:
  KmQuote{}
  KmBack{}
  KmB{}
  KmF{}
  KmN{}
  KmR{}
  KmT{}

# the letter written after the backslash
def k3.mark.char(mm: KMark) -> Char:
  match mm:
    case KmQuote{}:
      '"'
    case KmBack{}:
      '\\'
    case KmB{}:
      'b'
    case KmF{}:
      'f'
    case KmN{}:
      'n'
    case KmR{}:
      'r'
    case KmT{}:
      't'

# the character it stands for: `"`, `\`, backspace, form feed, line feed,
# carriage return, tab
def k3.mark.dec(mm: KMark) -> Char:
  match mm:
    case KmQuote{}:
      '"'
    case KmBack{}:
      '\\'
    case KmB{}:
      Chr{8}
    case KmF{}:
      Chr{12}
    case KmN{}:
      '\n'
    case KmR{}:
      '\r'
    case KmT{}:
      '\t'

# a hexadecimal digit, a letter one in upper case when up
type KHex is Data:
  Kx0{}
  Kx1{}
  Kx2{}
  Kx3{}
  Kx4{}
  Kx5{}
  Kx6{}
  Kx7{}
  Kx8{}
  Kx9{}
  KxA{up: Bool}
  KxB{up: Bool}
  KxC{up: Bool}
  KxD{up: Bool}
  KxE{up: Bool}
  KxF{up: Bool}

# a letter digit's character: the upper case one, or the lower case one
def k3.hex.case(up: Bool, +upper: Char, +lower: Char) -> Char:
  match up:
    case True{}:
      upper
    case False{}:
      lower

# a hexadecimal digit's character
def k3.hex.char(hx: KHex) -> Char:
  match hx:
    case Kx0{}:
      '0'
    case Kx1{}:
      '1'
    case Kx2{}:
      '2'
    case Kx3{}:
      '3'
    case Kx4{}:
      '4'
    case Kx5{}:
      '5'
    case Kx6{}:
      '6'
    case Kx7{}:
      '7'
    case Kx8{}:
      '8'
    case Kx9{}:
      '9'
    case KxA{up}:
      k3.hex.case(up, 'A', 'a')
    case KxB{up}:
      k3.hex.case(up, 'B', 'b')
    case KxC{up}:
      k3.hex.case(up, 'C', 'c')
    case KxD{up}:
      k3.hex.case(up, 'D', 'd')
    case KxE{up}:
      k3.hex.case(up, 'E', 'e')
    case KxF{up}:
      k3.hex.case(up, 'F', 'f')

# a hexadecimal digit's value
def k3.hex.val(hx: KHex) -> U32:
  match hx:
    case Kx0{}:
      0
    case Kx1{}:
      1
    case Kx2{}:
      2
    case Kx3{}:
      3
    case Kx4{}:
      4
    case Kx5{}:
      5
    case Kx6{}:
      6
    case Kx7{}:
      7
    case Kx8{}:
      8
    case Kx9{}:
      9
    case KxA{_up}:
      10
    case KxB{_up}:
      11
    case KxC{_up}:
      12
    case KxD{_up}:
      13
    case KxE{_up}:
      14
    case KxF{_up}:
      15

# a number read so far, then one more digit
def k3.hex.acc(+acc: U32, hx: KHex) -> U32:
  U32.add(U32.mul(acc, 16), k3.hex.val(hx))

# the number four digits write, the most significant first
def k3.hex4(dd: KHex, cc: KHex, bb: KHex, aa: KHex) -> U32:
  k3.hex.acc(k3.hex.acc(k3.hex.acc(k3.hex.acc(0, dd), cc), bb), aa)

# a Unicode scalar value: at most U+10FFFF, and no surrogate (U+D800 to
# U+DFFF; 1114111 is %x10FFFF, 55296 %xD800 and 57343 %xDFFF)
def k3.scalar(+uu: U32) -> Bool:
  Bool.and(U32.is_le(uu, 1114111), Bool.not(Bool.and(U32.is_ge(uu, 55296), U32.is_le(uu, 57343))))

# one piece of a basic string: a character written as itself, a
# two-character escape, `\u` and four hexadecimal digits, or `\U` and eight
type KPiece is Data:
  KpChar{cc: Char}
  KpEsc{mm: KMark}
  KpU4{dd: KHex, cc: KHex, bb: KHex, aa: KHex}
  KpU8{hh: KHex, gg: KHex, ff: KHex, ee: KHex, dd: KHex, cc: KHex, bb: KHex, aa: KHex}

# four hexadecimal digits, then tail
def k3.hex4.text(dd: KHex, cc: KHex, bb: KHex, aa: KHex, tail: String) -> String:
  SCon{k3.hex.char(dd), SCon{k3.hex.char(cc), SCon{k3.hex.char(bb), SCon{k3.hex.char(aa), tail}}}}

# a piece's text, then tail
def k3.pc.text(pp: KPiece, tail: String) -> String:
  match pp:
    case KpChar{cc}:
      SCon{cc, tail}
    case KpEsc{mm}:
      SCon{'\\', SCon{k3.mark.char(mm), tail}}
    case KpU4{dd, cc, bb, aa}:
      SCon{'\\', SCon{'u', k3.hex4.text(dd, cc, bb, aa, tail)}}
    case KpU8{hh, gg, ff, ee, dd, cc, bb, aa}:
      SCon{'\\', SCon{'U', k3.hex4.text(hh, gg, ff, ee, k3.hex4.text(dd, cc, bb, aa, tail))}}

# the number eight digits write, the most significant first
def k3.hex8(
  hh: KHex,
  gg: KHex,
  ff: KHex,
  ee: KHex,
  dd: KHex,
  cc: KHex,
  bb: KHex,
  aa: KHex
) -> U32:
  k3.hex.acc(k3.hex.acc(k3.hex.acc(k3.hex.acc(k3.hex4(hh, gg, ff, ee), dd), cc), bb), aa)

# the character a piece stands for
def k3.pc.char(pp: KPiece) -> Char:
  match pp:
    case KpChar{cc}:
      cc
    case KpEsc{mm}:
      k3.mark.dec(mm)
    case KpU4{dd, cc, bb, aa}:
      Chr{k3.hex4(dd, cc, bb, aa)}
    case KpU8{hh, gg, ff, ee, dd, cc, bb, aa}:
      Chr{k3.hex8(hh, gg, ff, ee, dd, cc, bb, aa)}

# the pieces' text, then tail
def k3.pcs.text(ps: List<&2, KPiece>, tail: String) -> String:
  match ps:
    case []:
      tail
    case pp <> rest:
      k3.pc.text(pp, k3.pcs.text(rest, tail))

# the characters the pieces stand for
def k3.pcs.name(ps: List<&2, KPiece>) -> String:
  match ps:
    case []:
      ""
    case pp <> rest:
      SCon{k3.pc.char(pp), k3.pcs.name(rest)}

# a key segment: bare, a basic string of pieces, or a literal string
type KSeg is Data:
  KsBare{name: String}
  KsBasic{pl: List<&2, KPiece>}
  KsLit{name: String}

# a segment's text, then tail
def k3.seg.text(sg: KSeg, tail: String) -> String:
  match sg:
    case KsBare{name}:
      String.append(name, tail)
    case KsBasic{pl}:
      SCon{'"', k3.pcs.text(pl, SCon{'"', tail})}
    case KsLit{name}:
      SCon{'\'', String.append(name, SCon{'\'', tail})}

# a segment's name: its characters, a basic one's escapes decoded
def k3.seg.name(sg: KSeg) -> String:
  match sg:
    case KsBare{name}:
      name
    case KsBasic{pl}:
      k3.pcs.name(pl)
    case KsLit{name}:
      name
