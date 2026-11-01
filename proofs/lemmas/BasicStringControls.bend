# which characters basic-unescaped takes and when a character is a control
import Base
import ../../src/eq.bend as Eq
import ../../laws/defs/AbnfGrammar.bend as D1
import ./ControlEscapeText.bend as M1
import ./ValueTextReadback.bend as M2

# WP-S1: strings of every form read as the text they denote. A string's
# derivation (GString) is read from the state that waits for a value, one
# piece at a time: a one-line basic string through WP-S's span (sv.open,
# sv.eat) while its pieces are characters written as themselves, and in
# LStr once an escape copies the span; a literal string as a span alone; a
# multi-line string in LStr with the trims of LTrim and LFold and the quotes
# of LMq and LMqEnd. Escapes go through KEY-3's symbolic hex reader
# (k3.hx.dv, k3.hx.ok, k3.hx.scan), so every \u and \U costs the same few
# lemmas. Every field a string leaves alone is a parameter (bd the error, rw
# the rows, hs heads, he here, ps parts, sk the stack, ab arrtab), and the
# rest of the walk is a motive PP over the document, as in WP-S and WP-C.

# Characters. basic-unescaped and literal-char leave out every control but
# tab, so a character either takes is pushed by the string states, and is no
# quote it leaves out.

# a code point a class of characters takes is not one it leaves out
def s1.off(
  pp: Char -> Bool,
  +uu: U32,
  +kk: U32,
  yes: {pp(Chr{uu}) == True{} : Bool},
  no: {pp(Chr{kk}) == False{} : Bool}
) -> {U32.is_eq(uu, kk) == False{} : Bool}:
  M1.neq.off(uu, kk, ee => Eq.bit.clash(Equal.trans(Bool, False{}, pp(Chr{kk}), True{},
    Equal.sym(Bool, pp(Chr{kk}), False{}, no),
    Equal.trans(Bool, pp(Chr{kk}), pp(Chr{uu}), True{},
      Equal.cong(Char, Bool, pp, Chr{kk}, Chr{uu}, Equal.sym(Char, Chr{uu}, Chr{kk}, ee)), yes))))

# a control basic-unescaped takes is a tab
def s1.bu.tab(
  +uu: U32,
  h_c: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == True{} : Bool},
  hb: {D1.abnf.basic_unescaped(Chr{uu}) == True{} : Bool}
) -> {U32.is_eq(uu, 9) == True{} : Bool}:
  Eq.ctl.all(kk => {D1.abnf.basic_unescaped(Chr{kk}) == True{} : Bool} -> {U32.is_eq(kk, 9) == True{} : Bool},
    uu, h_c,
    h0 => Eq.bit.absurd(&2, {U32.is_eq(0, 9) == True{} : Bool}, h0),
    h1 => Eq.bit.absurd(&2, {U32.is_eq(1, 9) == True{} : Bool}, h1),
    h2 => Eq.bit.absurd(&2, {U32.is_eq(2, 9) == True{} : Bool}, h2),
    h3 => Eq.bit.absurd(&2, {U32.is_eq(3, 9) == True{} : Bool}, h3),
    h4 => Eq.bit.absurd(&2, {U32.is_eq(4, 9) == True{} : Bool}, h4),
    h5 => Eq.bit.absurd(&2, {U32.is_eq(5, 9) == True{} : Bool}, h5),
    h6 => Eq.bit.absurd(&2, {U32.is_eq(6, 9) == True{} : Bool}, h6),
    h7 => Eq.bit.absurd(&2, {U32.is_eq(7, 9) == True{} : Bool}, h7),
    h8 => Eq.bit.absurd(&2, {U32.is_eq(8, 9) == True{} : Bool}, h8),
    _h9 => {==},
    h10 => Eq.bit.absurd(&2, {U32.is_eq(10, 9) == True{} : Bool}, h10),
    h11 => Eq.bit.absurd(&2, {U32.is_eq(11, 9) == True{} : Bool}, h11),
    h12 => Eq.bit.absurd(&2, {U32.is_eq(12, 9) == True{} : Bool}, h12),
    h13 => Eq.bit.absurd(&2, {U32.is_eq(13, 9) == True{} : Bool}, h13),
    h14 => Eq.bit.absurd(&2, {U32.is_eq(14, 9) == True{} : Bool}, h14),
    h15 => Eq.bit.absurd(&2, {U32.is_eq(15, 9) == True{} : Bool}, h15),
    h16 => Eq.bit.absurd(&2, {U32.is_eq(16, 9) == True{} : Bool}, h16),
    h17 => Eq.bit.absurd(&2, {U32.is_eq(17, 9) == True{} : Bool}, h17),
    h18 => Eq.bit.absurd(&2, {U32.is_eq(18, 9) == True{} : Bool}, h18),
    h19 => Eq.bit.absurd(&2, {U32.is_eq(19, 9) == True{} : Bool}, h19),
    h20 => Eq.bit.absurd(&2, {U32.is_eq(20, 9) == True{} : Bool}, h20),
    h21 => Eq.bit.absurd(&2, {U32.is_eq(21, 9) == True{} : Bool}, h21),
    h22 => Eq.bit.absurd(&2, {U32.is_eq(22, 9) == True{} : Bool}, h22),
    h23 => Eq.bit.absurd(&2, {U32.is_eq(23, 9) == True{} : Bool}, h23),
    h24 => Eq.bit.absurd(&2, {U32.is_eq(24, 9) == True{} : Bool}, h24),
    h25 => Eq.bit.absurd(&2, {U32.is_eq(25, 9) == True{} : Bool}, h25),
    h26 => Eq.bit.absurd(&2, {U32.is_eq(26, 9) == True{} : Bool}, h26),
    h27 => Eq.bit.absurd(&2, {U32.is_eq(27, 9) == True{} : Bool}, h27),
    h28 => Eq.bit.absurd(&2, {U32.is_eq(28, 9) == True{} : Bool}, h28),
    h29 => Eq.bit.absurd(&2, {U32.is_eq(29, 9) == True{} : Bool}, h29),
    h30 => Eq.bit.absurd(&2, {U32.is_eq(30, 9) == True{} : Bool}, h30),
    h31 => Eq.bit.absurd(&2, {U32.is_eq(31, 9) == True{} : Bool}, h31),
    h127 => Eq.bit.absurd(&2, {U32.is_eq(127, 9) == True{} : Bool}, h127))(hb)

# and so does literal-char
def s1.lc.tab(
  +uu: U32,
  h_c: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == True{} : Bool},
  hl: {D1.abnf.literal_char(Chr{uu}) == True{} : Bool}
) -> {U32.is_eq(uu, 9) == True{} : Bool}:
  Eq.ctl.all(kk => {D1.abnf.literal_char(Chr{kk}) == True{} : Bool} -> {U32.is_eq(kk, 9) == True{} : Bool},
    uu, h_c,
    h0 => Eq.bit.absurd(&2, {U32.is_eq(0, 9) == True{} : Bool}, h0),
    h1 => Eq.bit.absurd(&2, {U32.is_eq(1, 9) == True{} : Bool}, h1),
    h2 => Eq.bit.absurd(&2, {U32.is_eq(2, 9) == True{} : Bool}, h2),
    h3 => Eq.bit.absurd(&2, {U32.is_eq(3, 9) == True{} : Bool}, h3),
    h4 => Eq.bit.absurd(&2, {U32.is_eq(4, 9) == True{} : Bool}, h4),
    h5 => Eq.bit.absurd(&2, {U32.is_eq(5, 9) == True{} : Bool}, h5),
    h6 => Eq.bit.absurd(&2, {U32.is_eq(6, 9) == True{} : Bool}, h6),
    h7 => Eq.bit.absurd(&2, {U32.is_eq(7, 9) == True{} : Bool}, h7),
    h8 => Eq.bit.absurd(&2, {U32.is_eq(8, 9) == True{} : Bool}, h8),
    _h9 => {==},
    h10 => Eq.bit.absurd(&2, {U32.is_eq(10, 9) == True{} : Bool}, h10),
    h11 => Eq.bit.absurd(&2, {U32.is_eq(11, 9) == True{} : Bool}, h11),
    h12 => Eq.bit.absurd(&2, {U32.is_eq(12, 9) == True{} : Bool}, h12),
    h13 => Eq.bit.absurd(&2, {U32.is_eq(13, 9) == True{} : Bool}, h13),
    h14 => Eq.bit.absurd(&2, {U32.is_eq(14, 9) == True{} : Bool}, h14),
    h15 => Eq.bit.absurd(&2, {U32.is_eq(15, 9) == True{} : Bool}, h15),
    h16 => Eq.bit.absurd(&2, {U32.is_eq(16, 9) == True{} : Bool}, h16),
    h17 => Eq.bit.absurd(&2, {U32.is_eq(17, 9) == True{} : Bool}, h17),
    h18 => Eq.bit.absurd(&2, {U32.is_eq(18, 9) == True{} : Bool}, h18),
    h19 => Eq.bit.absurd(&2, {U32.is_eq(19, 9) == True{} : Bool}, h19),
    h20 => Eq.bit.absurd(&2, {U32.is_eq(20, 9) == True{} : Bool}, h20),
    h21 => Eq.bit.absurd(&2, {U32.is_eq(21, 9) == True{} : Bool}, h21),
    h22 => Eq.bit.absurd(&2, {U32.is_eq(22, 9) == True{} : Bool}, h22),
    h23 => Eq.bit.absurd(&2, {U32.is_eq(23, 9) == True{} : Bool}, h23),
    h24 => Eq.bit.absurd(&2, {U32.is_eq(24, 9) == True{} : Bool}, h24),
    h25 => Eq.bit.absurd(&2, {U32.is_eq(25, 9) == True{} : Bool}, h25),
    h26 => Eq.bit.absurd(&2, {U32.is_eq(26, 9) == True{} : Bool}, h26),
    h27 => Eq.bit.absurd(&2, {U32.is_eq(27, 9) == True{} : Bool}, h27),
    h28 => Eq.bit.absurd(&2, {U32.is_eq(28, 9) == True{} : Bool}, h28),
    h29 => Eq.bit.absurd(&2, {U32.is_eq(29, 9) == True{} : Bool}, h29),
    h30 => Eq.bit.absurd(&2, {U32.is_eq(30, 9) == True{} : Bool}, h30),
    h31 => Eq.bit.absurd(&2, {U32.is_eq(31, 9) == True{} : Bool}, h31),
    h127 => Eq.bit.absurd(&2, {U32.is_eq(127, 9) == True{} : Bool}, h127))(hl)

# the code point is 9
def s1.is9(+uu: U32, e9: {U32.is_eq(uu, 9) == True{} : Bool}) -> {uu == 9 : U32}:
  Equal.cong(Char, U32, cc => Char.to_u32(cc), Chr{uu}, Chr{9}, Eq.u32_eq(uu, 9, e9))

# a character that is a control only when it is a tab, as the two classes
# take: ct says whether it is a control, and it is one exactly when a tab
def s1.C9(+uu: U32) -> Type:
  {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == U32.is_eq(uu, 9) : Bool}

# a code point that is a control exactly when it is 9, by the two answers
def s1.c9.go(
  ct: Bool,
  t9: Bool,
  +uu: U32,
  ec: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == ct : Bool},
  e9: {U32.is_eq(uu, 9) == t9 : Bool},
  tab: {ct == True{} : Bool} -> {t9 == True{} : Bool}
) -> s1.C9(uu):
  match ct t9:
    case True{} True{}:
      Equal.trans(Bool, Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), True{}, U32.is_eq(uu, 9), ec,
        Equal.sym(Bool, U32.is_eq(uu, 9), True{}, e9))
    case True{} False{}:
      Eq.bit.absurd(&1, s1.C9(uu), tab({==}))
    case False{} True{}:
      Eq.bit.absurd2(&1, s1.C9(uu), Equal.trans(Bool, True{}, Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), False{},
        Equal.cong(U32, Bool, nn => Bool.or(U32.is_lt(nn, 32), U32.is_eq(nn, 127)), 9, uu,
          Equal.sym(U32, uu, 9, s1.is9(uu, e9))), ec))
    case False{} False{}:
      Equal.trans(Bool, Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), False{}, U32.is_eq(uu, 9), ec,
        Equal.sym(Bool, U32.is_eq(uu, 9), False{}, e9))

# a character basic-unescaped takes is a control only when it is a tab
def s1.bu.c9(
  +uu: U32,
  +hb: {D1.abnf.basic_unescaped(Chr{uu}) == True{} : Bool}
) -> s1.C9(uu):
  s1.c9.go(Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), U32.is_eq(uu, 9), uu, {==}, {==},
    ec => s1.bu.tab(uu, ec, hb))

# and so is one literal-char takes
def s1.lc.c9(
  +uu: U32,
  +hl: {D1.abnf.literal_char(Chr{uu}) == True{} : Bool}
) -> s1.C9(uu):
  s1.c9.go(Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), U32.is_eq(uu, 9), uu, {==}, {==},
    ec => s1.lc.tab(uu, ec, hl))

# basic-unescaped takes no quotation mark
def s1.bu.q(
  +uu: U32,
  hb: {D1.abnf.basic_unescaped(Chr{uu}) == True{} : Bool}
) -> {U32.is_eq(uu, 34) == False{} : Bool}:
  s1.off(cc => D1.abnf.basic_unescaped(cc), uu, 34, hb, {==})

# and no backslash
def s1.bu.b(
  +uu: U32,
  hb: {D1.abnf.basic_unescaped(Chr{uu}) == True{} : Bool}
) -> {U32.is_eq(uu, 92) == False{} : Bool}:
  s1.off(cc => D1.abnf.basic_unescaped(cc), uu, 92, hb, {==})

# literal-char takes no apostrophe
def s1.lc.a(
  +uu: U32,
  hl: {D1.abnf.literal_char(Chr{uu}) == True{} : Bool}
) -> {U32.is_eq(uu, 39) == False{} : Bool}:
  s1.off(cc => D1.abnf.literal_char(cc), uu, 39, hl, {==})

# a carriage return and a line feed with nothing after them are CRLF
def s1.nl.end(
  t2: String,
  em: {String.is_empty(t2) == True{} : Bool},
  -QQ: String -> Type,
  crlf: QQ("\r\n")
) -> QQ(SCon{Chr{13}, SCon{Chr{10}, t2}}):
  match t2:
    case SNil{}:
      crlf
    case SCon{h3, t3}:
      Eq.bit.absurd(&1, QQ(SCon{Chr{13}, SCon{Chr{10}, SCon{h3, t3}}}), em)

# a newline is a line feed, or a carriage return and a line feed: a claim
# about both holds of every newline
def s1.nl.elim(
  -QQ: String -> Type,
  nl: String,
  +hn: {D1.abnf.newline(nl) == True{} : Bool},
  lf: QQ("\n"),
  crlf: QQ("\r\n")
) -> QQ(nl):
  match nl:
    case SNil{}:
      Eq.bit.absurd(&1, QQ(SNil{}), hn)
    case SCon{hh, tt}:
      match hh:
        case Chr{+uu}:
          match tt:
            case SNil{}:
              %Equal.sym(U32, uu, 10, M2.s1.isk(uu, 10, hn)) : QQ(SCon{Chr{_}, SNil{}})
              lf
            case SCon{h2, +t2}:
              match h2:
                case Chr{+u2}:
                  +e13 = {Eq.and.left(U32.is_eq(uu, 13), Bool.and(U32.is_eq(u2, 10), String.is_empty(t2)), hn)
                    : {U32.is_eq(uu, 13) == True{} : Bool}}
                  +e10 = {Eq.and.left(U32.is_eq(u2, 10), String.is_empty(t2), Eq.and.right(U32.is_eq(uu, 13),
                    Bool.and(U32.is_eq(u2, 10), String.is_empty(t2)), hn)) : {U32.is_eq(u2, 10) == True{} : Bool}}
                  +em = {Eq.and.right(U32.is_eq(u2, 10), String.is_empty(t2), Eq.and.right(U32.is_eq(uu, 13),
                    Bool.and(U32.is_eq(u2, 10), String.is_empty(t2)), hn)) : {String.is_empty(t2) == True{} : Bool}}
                  %Equal.sym(U32, uu, 13, M2.s1.isk(uu, 13, e13)) : QQ(SCon{Chr{_}, SCon{Chr{u2}, t2}})
                  %Equal.sym(U32, u2, 10, M2.s1.isk(u2, 10, e10)) : QQ(SCon{Chr{13}, SCon{Chr{_}, t2}})
                  s1.nl.end(t2, em, QQ, crlf)
