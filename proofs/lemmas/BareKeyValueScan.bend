# a bare key then ' = ' and a value, scanned from the document start
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/StringRenderEscapes.bend as L1
import ../../laws/defs/BareValueGrammar.bend as D1
import ./ControlEscapeText.bend as M1
import ./FreshNamesInRows.bend as M2
import ./HeldCharacterSteps.bend as M3
import ./ReorderedTableNames.bend as M4
import ./StringEqualsItself.bend as M5
import ./ValueTextReadback.bend as M6

# Multi-line strings. A body character a law calls plain is pushed onto the
# buffer, whichever kind the string is; the closing quotes are then read as
# plain text, since they are the same five or six characters for every body.

# the kind of a multi-line string: literal or basic
def mk(lit: Bool) -> T.QKind:
  match lit:
    case True{}:
      T.QMultiLit{}
    case False{}:
      T.QMulti{}

# Bare keys. A text of bare-key characters at the start of a document is
# pushed onto the buffer of a key; the first character comes through the
# byte-order-mark check and the top-level dispatch, every later one through
# the key's fast path.

# a scanner reading the first key of an empty document
def ky(buf: List<&2, Char>) -> T.St:
  T.St{"", [], [], [], [], buf, T.LKey{}, T.LTop{}, T.QBasic{}, [], T.HNone{}, 0, 0,
    False{}, False{}}

# the first character of the document: no byte-order mark, so a new key
def key.bom(
  bom: Bool,
  +xx: U32,
  ebom: {U32.is_eq(xx, 65279) == bom : Bool},
  +ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.read.once2(T.read.step.bom(bom, T.St{"", [], [], [], [], [], T.LTop{}, T.LTop{},
  T.QBasic{}, [], T.HNone{}, 0, 0, False{}, False{}}, Chr{xx})) == ky([Chr{xx}]) : T.St}:
  match bom:
    case True{}:
      Eq.bit.gone(&2, {T.read.once2(T.read.step.bom(True{}, T.St{"", [], [], [], [], [],
        T.LTop{}, T.LTop{}, T.QBasic{}, [], T.HNone{}, 0, 0, False{}, False{}}, Chr{xx}))
        == ky([Chr{xx}]) : T.St},
        Eq.refute_char(Chr{xx}, Chr{65279}, ch => T.bare.at(ch), ebom, ee, {==}))
    case False{}:
      Equal.cong(T.St, T.St, s => T.read.once2(s),
        T.lex.top.go(T.ch.sp(Chr{xx}), T.ch.nl(Chr{xx}), Char.is_eq(Chr{xx}, '#'),
          Char.is_eq(Chr{xx}, '['), Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''),
          T.bare.at(Chr{xx}), T.St{"", [], [], [], [], [], T.LTop{}, T.LTop{}, T.QBasic{},
          [], T.HNone{}, 0, 0, False{}, False{}}, Chr{xx}),
        T.st.push(T.St{"", [], [], [], [], [], T.LTop{}, T.LTop{}, T.QBasic{}, [],
          T.HNone{}, 0, 0, False{}, False{}}, Chr{xx}, T.LKey{}),
        M6.key.top(T.ch.sp(Chr{xx}), T.ch.nl(Chr{xx}), Char.is_eq(Chr{xx}, '#'),
          Char.is_eq(Chr{xx}, '['), Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''),
          T.bare.at(Chr{xx}), T.St{"", [], [], [], [], [], T.LTop{}, T.LTop{}, T.QBasic{},
          [], T.HNone{}, 0, 0, False{}, False{}}, xx, {==}, {==}, {==}, {==}, {==}, {==},
          {==}, ee))

# the first character of the document starts a key
def key.first(
  +xx: U32,
  +ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.doc.scan(T.st.start(), Chr{xx}) == T.MScan{ky([Chr{xx}])} : T.Mode}:
  Equal.trans(T.Mode,
    T.doc.scan(T.st.start(), Chr{xx}),
    T.MScan{T.read.fast(T.st.start(), Chr{xx})},
    T.MScan{ky([Chr{xx}])},
    M4.scan.other(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), U32.is_eq(xx, 13),
      T.st.start(), Chr{xx}, {==}, {==}, {==}, ch => T.bare.at(ch), ee, {==}, {==}, {==}),
    Equal.cong(T.St, T.Mode, s => T.MScan{s},
      T.read.fast(T.st.start(), Chr{xx}), ky([Chr{xx}]),
      key.bom(U32.is_eq(xx, 65279), xx, {==}, ee)))

# a later bare-key character stays on the key's fast path
def key.fast(
  ok: Bool,
  +buf: List<&2, Char>,
  +xx: U32,
  eok: {T.bare.at(Chr{xx}) == ok : Bool},
  ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.read.fast.key(ok, "", [], [], [], [], buf, T.LTop{}, T.QBasic{}, [], 0, 0, False{},
  Chr{xx}) == ky(Chr{xx} <> buf) : T.St}:
  match ok:
    case True{}:
      {==}
    case False{}:
      M5.clash(&2, {T.read.fast.key(False{}, "", [], [], [], [], buf, T.LTop{}, T.QBasic{}, [],
        0, 0, False{}, Chr{xx}) == ky(Chr{xx} <> buf) : T.St},
        Equal.trans(Bool, False{}, T.bare.at(Chr{xx}), True{},
          Equal.sym(Bool, T.bare.at(Chr{xx}), False{}, eok), ee))

# one later character of the key, from the scan mode
def key.step(
  +buf: List<&2, Char>,
  +xx: U32,
  +ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.doc.scan(ky(buf), Chr{xx}) == T.MScan{ky(Chr{xx} <> buf)} : T.Mode}:
  Equal.trans(T.Mode,
    T.doc.scan(ky(buf), Chr{xx}),
    T.MScan{T.read.fast(ky(buf), Chr{xx})},
    T.MScan{ky(Chr{xx} <> buf)},
    M4.scan.other(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), U32.is_eq(xx, 13),
      ky(buf), Chr{xx}, {==}, {==}, {==}, ch => T.bare.at(ch), ee, {==}, {==}, {==}),
    Equal.cong(T.St, T.Mode, s => T.MScan{s},
      T.read.fast(ky(buf), Chr{xx}), ky(Chr{xx} <> buf),
      key.fast(T.bare.at(Chr{xx}), buf, xx, {==}, ee)))

# a key of bare characters is pushed onto the buffer, whatever follows it
def key.body(
  ks: String,
  +rr: String,
  +buf: List<&2, Char>,
  +ee: {T.bare.all(String.to_list(ks)) == True{} : Bool}
) -> {T.doc.read(String.append(ks, rr), T.MScan{ky(buf)})
  == T.doc.read(rr, T.MScan{ky(M2.rev.onto(ks, buf))}) : T.Doc}:
  match ks:
    case SNil{}:
      {==}
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          Equal.trans(T.Doc,
            T.doc.read(String.append(tt, rr), T.doc.scan(ky(buf), Chr{xx})),
            T.doc.read(String.append(tt, rr), T.MScan{ky(Chr{xx} <> buf)}),
            T.doc.read(rr, T.MScan{ky(M2.rev.onto(tt, Chr{xx} <> buf))}),
            Equal.cong(T.Mode, T.Doc, m => T.doc.read(String.append(tt, rr), m),
              T.doc.scan(ky(buf), Chr{xx}), T.MScan{ky(Chr{xx} <> buf)},
              key.step(buf, xx, M6.ball.head(T.bare.at(Chr{xx}), String.to_list(tt), ee))),
            key.body(tt, rr, Chr{xx} <> buf,
              M6.ball.tail(T.bare.at(Chr{xx}), String.to_list(tt), ee)))

# an array item: in LArr the quote is held, read in LVal, and opens the
# string with back at LVal
def sv.arr(
  +ss: String,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +buf: List<&2, Char>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  es: {D1.short(ss) == True{} : Bool},
  hr: {M6.sv.free(rest) == True{} : Bool},
  ih: M6.sv.Then(ss, bd, rw, hs, he, ps, sk, ab, rest, PP)
) -> M6.sv.Read(ss, bd, rw, hs, he, ps, buf, T.LArr{}, bk, qk, sk, un, lf, ab, rest, PP):
  %Equal.sym(String, T.key.basic(ss), "\"" ++ L1.escs(ss) ++ "\"", L1.basic_escs(ss)) :
    PP(T.doc.read(String.append(_, rest), T.MScan{M3.fs.st(bd, rw, hs, he, ps, buf, T.LArr{}, bk, qk, sk, un, lf,
      ab)}))
  %Equal.sym(String, String.append(String.append(L1.escs(ss), "\""), rest),
    String.append(L1.escs(ss), String.append("\"", rest)), Eq.append_assoc(L1.escs(ss), "\"", rest)) :
    PP(T.doc.read(_, M6.sv.open(bd, rw, hs, he, ps, T.LVal{}, sk, un, lf, ab)))
  M6.sv.text(ss, rest, PP, M6.sv.open(bd, rw, hs, he, ps, T.LVal{}, sk, un, lf, ab),
    M6.sv.read(ss, bd, rw, hs, he, ps, T.LVal{}, sk, un, lf, ab, rest, PP, es, hr, ih))

# The laws. A bare key, then " = " and whatever opens the value, bring the
# scanner to the value position; the string is read there by sv.val or
# sv.arr; the text after it closes the document, which own reads as the
# document of s once the value is known to be a string.

# a space ends a nonempty bare key, and " = " leaves the scanner waiting for
# the value
def kv.eq2(
  +bb: List<&2, Char>,
  full: {List.is_empty(&2, Char, bb) == False{} : Bool},
  +vv: String
) -> {T.doc.read(SCon{' ', SCon{'=', SCon{' ', vv}}}, T.MScan{ky(bb)})
  == T.doc.read(vv, T.MScan{M3.fs.st("", [], [], [], [T.buf.str.go(bb, "")], [], T.LVal{}, T.LTop{}, T.QBasic{}, [], 0,
    0, False{})}) : T.Doc}:
  Equal.trans(T.Doc,
    T.doc.read(SCon{'=', SCon{' ', vv}}, T.MScan{T.read.once2(T.lex.key.end.go(
      List.is_empty(&2, Char, bb), ky(bb), T.LAfter{}))}),
    T.doc.read(SCon{'=', SCon{' ', vv}}, T.MScan{T.read.once2(T.lex.key.end.go(
      False{}, ky(bb), T.LAfter{}))}),
    T.doc.read(vv, T.MScan{M3.fs.st("", [], [], [], [T.buf.str.go(bb, "")], [], T.LVal{}, T.LTop{}, T.QBasic{}, [], 0,
      0, False{})}),
    Equal.cong(Bool, T.Doc,
      bt => T.doc.read(SCon{'=', SCon{' ', vv}}, T.MScan{T.read.once2(
        T.lex.key.end.go(bt, ky(bb), T.LAfter{}))}),
      List.is_empty(&2, Char, bb), False{}, full),
    {==})

# a bare key, then " = ": the scanner waits for the value, the key its name
def kv.key2(
  +xx: U32,
  +tt: String,
  +vv: String,
  +ee: {T.bare.all.step(T.bare.at(Chr{xx}), _u => T.bare.all(String.to_list(tt))) == True{} : Bool}
) -> {T.parse(String.append(SCon{Chr{xx}, tt}, SCon{' ', SCon{'=', SCon{' ', vv}}}))
  == T.doc.read(vv, T.MScan{M3.fs.st("", [], [], [], [SCon{Chr{xx}, tt}], [], T.LVal{}, T.LTop{}, T.QBasic{}, [], 0,
    0, False{})}) : T.Doc}:
  Equal.trans(T.Doc,
    T.doc.read(String.append(tt, SCon{' ', SCon{'=', SCon{' ', vv}}}), T.doc.scan(T.st.start(), Chr{xx})),
    T.doc.read(String.append(tt, SCon{' ', SCon{'=', SCon{' ', vv}}}), T.MScan{ky([Chr{xx}])}),
    T.doc.read(vv, T.MScan{M3.fs.st("", [], [], [], [SCon{Chr{xx}, tt}], [], T.LVal{}, T.LTop{}, T.QBasic{}, [], 0,
      0, False{})}),
    Equal.cong(T.Mode, T.Doc, md => T.doc.read(String.append(tt, SCon{' ', SCon{'=', SCon{' ', vv}}}), md),
      T.doc.scan(T.st.start(), Chr{xx}), T.MScan{ky([Chr{xx}])},
      key.first(xx, M6.ball.head(T.bare.at(Chr{xx}), String.to_list(tt), ee))),
    Equal.trans(T.Doc,
      T.doc.read(String.append(tt, SCon{' ', SCon{'=', SCon{' ', vv}}}), T.MScan{ky([Chr{xx}])}),
      T.doc.read(SCon{' ', SCon{'=', SCon{' ', vv}}}, T.MScan{ky(M2.rev.onto(tt, [Chr{xx}]))}),
      T.doc.read(vv, T.MScan{M3.fs.st("", [], [], [], [SCon{Chr{xx}, tt}], [], T.LVal{}, T.LTop{}, T.QBasic{}, [], 0,
        0, False{})}),
      key.body(tt, SCon{' ', SCon{'=', SCon{' ', vv}}}, [Chr{xx}],
        M6.ball.tail(T.bare.at(Chr{xx}), String.to_list(tt), ee)),
      Equal.trans(T.Doc,
        T.doc.read(SCon{' ', SCon{'=', SCon{' ', vv}}}, T.MScan{ky(M2.rev.onto(tt, [Chr{xx}]))}),
        T.doc.read(vv, T.MScan{M3.fs.st("", [], [], [], [T.buf.str.go(M2.rev.onto(tt, [Chr{xx}]), "")], [], T.LVal{},
          T.LTop{}, T.QBasic{}, [], 0, 0, False{})}),
        T.doc.read(vv, T.MScan{M3.fs.st("", [], [], [], [SCon{Chr{xx}, tt}], [], T.LVal{}, T.LTop{}, T.QBasic{}, [],
          0, 0, False{})}),
        kv.eq2(M2.rev.onto(tt, [Chr{xx}]), M6.rev.full(tt, Chr{xx}, []), vv),
        Equal.cong(String, T.Doc, nm => T.doc.read(vv, T.MScan{M3.fs.st("", [], [], [], [nm], [], T.LVal{},
          T.LTop{}, T.QBasic{}, [], 0, 0, False{})}),
          T.buf.str.go(M2.rev.onto(tt, [Chr{xx}]), ""), SCon{Chr{xx}, tt},
          Equal.trans(String, T.buf.str.go(M2.rev.onto(tt, [Chr{xx}]), ""),
            SCon{Chr{xx}, String.append(tt, "")}, SCon{Chr{xx}, tt},
            M6.ml.rev(tt, [Chr{xx}], ""),
            Equal.cong(String, String, ss => SCon{Chr{xx}, ss}, String.append(tt, ""), tt,
              Eq.append_nil(tt)))))))

# Headers after a value. A value before a header may have left uni and left
# anywhere a \u escape puts them, so a header's quoted segment is read by
# WP-C's qu family moved to the header's states: LHeadQ, with LHeadE and
# LHeadU for its escapes, and LHeadGap after the closing quote (qh).

# a scanner inside a quoted header segment, its characters so far reversed in buf, back
# wherever the last escape left it, and uni and left as they are
def qh(
  rw: List<&2, T.Val>,
  hs: List<&2, String>,
  he: List<&2, String>,
  ps: List<&2, String>,
  sk: List<&2, T.Ctx>,
  ab: Bool,
  bk: T.Lex,
  un: U32,
  lf: U32,
  buf: List<&2, Char>
) -> T.St:
  T.St{"", rw, hs, he, ps, buf, T.LHeadQ{}, bk, T.QBasic{}, sk, T.HNone{}, un, lf, ab, False{}}
