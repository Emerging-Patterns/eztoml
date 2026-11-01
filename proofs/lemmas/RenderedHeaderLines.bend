# header lines as render writes them, segment by segment, and the path counts
# behind them
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/AotHeaderExtendsArray.bend as L1
import ../../laws/AotHeaderStartsArray.bend as L2
import ../../laws/DefinesEachTableOnce.bend as L3
import ../../laws/GetFindsFirstPair.bend as L4
import ../../laws/HeaderDefinesNewTable.bend as L5
import ../../laws/KeyNameIsItsCharacters.bend as L6
import ../../laws/StringRenderEscapes.bend as L7
import ../../laws/TbOpenAfterSet.bend as L8
import ../../laws/TbRowsAfterSet.bend as L9
import ../../laws/defs/BareValueGrammar.bend as D1
import ../../laws/defs/DocumentSameness.bend as D2
import ../../laws/defs/KeySegmentSpelling.bend as D3
import ../../laws/defs/PartialDerivationRules.bend as D4
import ./BareKeyValueScan.bend as M1
import ./ControlEscapeText.bend as M2
import ./DecimalArithmetic.bend as M3
import ./FailedWalkNameCompare.bend as M4
import ./FreshNamesInRows.bend as M5
import ./HeaderDefinesTables.bend as M6
import ./HeaderSegmentWalk.bend as M7
import ./ReorderedTableNames.bend as M8
import ./ShortTextBounds.bend as M9
import ./StringEqualsItself.bend as M10
import ./TableLookupAfterSet.bend as M11
import ./ValuePassText.bend as M12
import ./ValueTextReadback.bend as M13

# where a segment starts: right after the bracket, or after a dot
def wh.lex0(dt: Bool) -> T.Lex:
  match dt:
    case False{}:
      T.LHead{}
    case True{}:
      T.LHeadDot{}

# the segments before it: none right after the bracket
def wh.ps(dt: Bool, parts: List<&2, String>) -> List<&2, String>:
  match dt:
    case False{}:
      []
    case True{}:
      parts

# what follows a segment: a dot, or the closing bracket
def wh.dl(cl: Bool) -> Char:
  match cl:
    case False{}:
      '.'
    case True{}:
      ']'

# a quoted segment's buffer reads back as its name
def wh.qname(+ss: String) -> {T.buf.str(M5.rev.onto(ss, [])) == ss : String}:
  Equal.trans(String, T.buf.str.go(M5.rev.onto(ss, []), ""), String.append(ss, ""), ss,
    M13.ml.rev(ss, [], ""), Eq.append_nil(ss))

# the segments after the first, each after a dot, as the rendered path
# writes them
def wh.more(segs: List<&2, String>) -> String:
  match segs:
    case []:
      ""
    case +seg <> rest:
      SCon{'.', String.append(T.key(seg), wh.more(rest))}

# the segments pushed onto parts, reversed, are the path in order
def wh.rev2(
  +t: List<&2, String>,
  +ss: String
) -> {List.reverse(&2, String, List.reverse.go(&2, String, t, [ss])) == ss <> t
  : List<&2, String>}:
  Equal.trans(List<&2, String>,
    List.reverse.go(&2, String, List.reverse.go(&2, String, t, [ss]), []),
    ss <> List.append(&2, String, t, []),
    ss <> t,
    M7.wh.rr(t, [ss], []),
    Equal.cong(List<&2, String>, List<&2, String>, zz => ss <> zz,
      List.append(&2, String, t, []), t, M7.wh.lnil(t)))

# and they are not empty
def wh.rne(
  t: List<&2, String>,
  +ss: String,
  +acc: List<&2, String>
) -> {List.is_empty(&2, String, List.reverse.go(&2, String, t, ss <> acc)) == False{} : Bool}:
  match t:
    case []:
      {==}
    case +xx <> xs:
      wh.rne(xs, xx, ss <> acc)

# a path joined onto a nonempty prefix is the prefix, a dot and the segment
def wh.pre(
  +pp: String,
  +xx: String,
  ep: {String.is_empty(pp) == False{} : Bool}
) -> {T.tree.pre(pp, xx) == String.append(pp, SCon{'.', T.key(xx)}) : String}:
  Equal.cong(Bool, String, bt => T.tree.pre.go(bt, pp, xx), String.is_empty(pp), False{}, ep)

# a nonempty prefix stays nonempty
def wh.ne(
  pp: String,
  +yy: String,
  ep: {String.is_empty(pp) == False{} : Bool}
) -> {String.is_empty(String.append(pp, yy)) == False{} : Bool}:
  match pp:
    case SNil{}:
      Eq.bit.absurd2(&2, {String.is_empty(String.append(SNil{}, yy)) == False{} : Bool}, ep)
    case SCon{_h, _t}:
      {==}

# the stored path of a header, from a nonempty prefix, is the prefix and the
# later segments, each after a dot
def wh.join(
  ss: List<&2, String>,
  +pp: String,
  +kk: String,
  +ep: {String.is_empty(pp) == False{} : Bool}
) -> {T.tree.pre(D1.tb.join(ss, pp), kk) == String.append(pp, wh.more(List.append(&2, String, ss,
  [kk]))) : String}:
  match ss:
    case []:
      Equal.trans(String, T.tree.pre(pp, kk), String.append(pp, SCon{'.', T.key(kk)}),
        String.append(pp, SCon{'.', String.append(T.key(kk), "")}),
        wh.pre(pp, kk, ep),
        Equal.cong(String, String, zz => String.append(pp, SCon{'.', zz}), T.key(kk),
          String.append(T.key(kk), ""), Equal.sym(String, String.append(T.key(kk), ""), T.key(kk),
          Eq.append_nil(T.key(kk)))))
    case +xx <> +xs:
      Equal.trans(String,
        T.tree.pre(D1.tb.join(xs, T.tree.pre(pp, xx)), kk),
        T.tree.pre(D1.tb.join(xs, String.append(pp, SCon{'.', T.key(xx)})), kk),
        String.append(pp, wh.more(xx <> List.append(&2, String, xs, [kk]))),
        Equal.cong(String, String, qq => T.tree.pre(D1.tb.join(xs, qq), kk), T.tree.pre(pp, xx),
          String.append(pp, SCon{'.', T.key(xx)}), wh.pre(pp, xx, ep)),
        Equal.trans(String,
          T.tree.pre(D1.tb.join(xs, String.append(pp, SCon{'.', T.key(xx)})), kk),
          String.append(String.append(pp, SCon{'.', T.key(xx)}), wh.more(List.append(&2, String, xs,
            [kk]))),
          String.append(pp, wh.more(xx <> List.append(&2, String, xs, [kk]))),
          wh.join(xs, String.append(pp, SCon{'.', T.key(xx)}), kk, wh.ne(pp, SCon{'.', T.key(xx)},
            ep)),
          Eq.append_assoc(pp, SCon{'.', T.key(xx)}, wh.more(List.append(&2, String, xs, [kk])))))

# a key is never empty: a bare one has a character, a quoted one its quotes
def wh.key.ne.go(
  bb: Bool,
  +ss: String,
  eb: {T.bare(ss) == bb : Bool}
) -> {String.is_empty(T.key.go(bb, ss)) == False{} : Bool}:
  match bb:
    case False{}:
      {==}
    case True{}:
      match ss:
        case SNil{}:
          Eq.bit.absurd(&2, {String.is_empty(T.key.go(True{}, SNil{})) == False{} : Bool}, eb)
        case SCon{_h, _t}:
          {==}

# a key is never empty
def wh.key.ne(+ss: String) -> {String.is_empty(T.key(ss)) == False{} : Bool}:
  wh.key.ne.go(T.bare(ss), ss, {==})

# the brackets that open a header: one, or two for an array of tables
def wh.open(arrtab: Bool, rest: String) -> String:
  match arrtab:
    case False{}:
      SCon{'[', rest}
    case True{}:
      SCon{'[', SCon{'[', rest}}

# WP-K3: a dotted key on a key/value line. Each segment starts at the start of
# the line (LTop, no parts yet) or after a dot (LKeyDot); a bare one is
# pushed in LKey and ended by blank space (to LAfter), a dot or `=`; a basic
# one is read by WP0's qs family and a literal one by ql, each ending in
# LAfter; blank space in LAfter and after a dot is skipped. The segment's
# name joins parts, newest first, and the last `=` leaves the scanner waiting
# for the value. The states are WP-H's wh.st, with the same fields.

# where a key segment starts: at the start of a line, or after a dot
def kl.lex0(dt: Bool) -> T.Lex:
  match dt:
    case False{}:
      T.LTop{}
    case True{}:
      T.LKeyDot{}

# at the start of a line, a character that is no blank and no newline takes
# the full step
def kl.ws(
  sp: Bool,
  nl: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +buf: List<&2, Char>,
  +lex: T.Lex,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +cc: Char,
  hs: {sp == False{} : Bool},
  hn: {nl == False{} : Bool}
) -> {T.read.fast.ws(sp, nl, True{}, "", rows, heads, here, parts, buf, lex, back, qkind, [], 0, 0, arrtab, cc)
  == T.read.fast.old("", rows, heads, here, parts, buf, lex, back, qkind, [], 0, 0, arrtab, cc) : T.St}:
  match sp:
    case True{}:
      Eq.bit.absurd2(&2, {T.read.fast.ws(True{}, nl, True{}, "", rows, heads, here, parts, buf, lex, back,
        qkind, [], 0, 0, arrtab, cc) == T.read.fast.old("", rows, heads, here, parts, buf, lex, back, qkind,
        [], 0, 0, arrtab, cc) : T.St}, hs)
    case False{}:
      match nl:
        case True{}:
          Eq.bit.absurd2(&2, {T.read.fast.ws(False{}, True{}, True{}, "", rows, heads, here, parts, buf, lex,
            back, qkind, [], 0, 0, arrtab, cc) == T.read.fast.old("", rows, heads, here, parts, buf, lex,
            back, qkind, [], 0, 0, arrtab, cc) : T.St}, hn)
        case False{}:
          {==}

# the first character of a bare segment starts its buffer
def kl.b1.fast(
  dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +xx: U32,
  +ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.read.fast(M7.wh.st(rows, heads, here, wh.ps(dt, parts), [], kl.lex0(dt), back, qkind, arrtab), Chr{xx})
  == M7.wh.st(rows, heads, here, wh.ps(dt, parts), [Chr{xx}], T.LKey{}, back, qkind, arrtab) : T.St}:
  match dt:
    case False{}:
      Equal.trans(T.St,
        T.read.fast(M7.wh.st(rows, heads, here, [], [], T.LTop{}, back, qkind, arrtab), Chr{xx}),
        T.read.fast.old("", rows, heads, here, [], [], T.LTop{}, back, qkind, [], 0, 0, arrtab, Chr{xx}),
        M7.wh.st(rows, heads, here, [], [Chr{xx}], T.LKey{}, back, qkind, arrtab),
        kl.ws(T.ch.sp(Chr{xx}), T.ch.nl(Chr{xx}), rows, heads, here, [], [], T.LTop{}, back, qkind, arrtab,
          Chr{xx}, M7.kl.no2(T.ch.sp(Chr{xx}), xx, 32, 9, {==}, ee, {==}, {==}),
          M7.kl.no2(T.ch.nl(Chr{xx}), xx, 10, 13, {==}, ee, {==}, {==})),
        Equal.cong(T.St, T.St, st => T.read.once2(st),
          T.lex.top.go(T.ch.sp(Chr{xx}), T.ch.nl(Chr{xx}), Char.is_eq(Chr{xx}, '#'),
            Char.is_eq(Chr{xx}, '['), Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''),
            T.bare.at(Chr{xx}), M7.wh.st(rows, heads, here, [], [], T.LTop{}, back, qkind, arrtab), Chr{xx}),
          T.st.push(M7.wh.st(rows, heads, here, [], [], T.LTop{}, back, qkind, arrtab), Chr{xx}, T.LKey{}),
          M13.key.top(T.ch.sp(Chr{xx}), T.ch.nl(Chr{xx}), Char.is_eq(Chr{xx}, '#'),
            Char.is_eq(Chr{xx}, '['), Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''),
            T.bare.at(Chr{xx}), M7.wh.st(rows, heads, here, [], [], T.LTop{}, back, qkind, arrtab), xx,
            {==}, {==}, {==}, {==}, {==}, {==}, {==}, ee)))
    case True{}:
      Equal.cong(T.St, T.St, st => T.read.once2(st),
        T.lex.kdot.go(T.ch.sp(Chr{xx}), Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''),
          Char.is_eq(Chr{xx}, '.'), T.ch.nl(Chr{xx}), M7.wh.st(rows, heads, here, parts, [], T.LKeyDot{}, back,
          qkind, arrtab), Chr{xx}),
        T.st.push(M7.wh.st(rows, heads, here, parts, [], T.LKeyDot{}, back, qkind, arrtab), Chr{xx}, T.LKey{}),
        M7.kd.bare(T.ch.sp(Chr{xx}), Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''),
          Char.is_eq(Chr{xx}, '.'), T.ch.nl(Chr{xx}), M7.wh.st(rows, heads, here, parts, [], T.LKeyDot{}, back,
          qkind, arrtab), xx, {==}, {==}, {==}, ee))

# and the scan mode sends it there
def kl.b1(
  +dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +xx: U32,
  +ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.doc.scan(M7.wh.st(rows, heads, here, wh.ps(dt, parts), [], kl.lex0(dt), back, qkind, arrtab), Chr{xx})
  == T.MScan{M7.wh.st(rows, heads, here, wh.ps(dt, parts), [Chr{xx}], T.LKey{}, back, qkind, arrtab)} : T.Mode}:
  Equal.trans(T.Mode,
    T.doc.scan(M7.wh.st(rows, heads, here, wh.ps(dt, parts), [], kl.lex0(dt), back, qkind, arrtab), Chr{xx}),
    T.MScan{T.read.fast(M7.wh.st(rows, heads, here, wh.ps(dt, parts), [], kl.lex0(dt), back, qkind, arrtab),
      Chr{xx})},
    T.MScan{M7.wh.st(rows, heads, here, wh.ps(dt, parts), [Chr{xx}], T.LKey{}, back, qkind, arrtab)},
    M8.scan.other(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), U32.is_eq(xx, 13),
      M7.wh.st(rows, heads, here, wh.ps(dt, parts), [], kl.lex0(dt), back, qkind, arrtab), Chr{xx}, {==}, {==},
      {==}, ch => T.bare.at(ch), ee, {==}, {==}, {==}),
    Equal.cong(T.St, T.Mode, st => T.MScan{st},
      T.read.fast(M7.wh.st(rows, heads, here, wh.ps(dt, parts), [], kl.lex0(dt), back, qkind, arrtab), Chr{xx}),
      M7.wh.st(rows, heads, here, wh.ps(dt, parts), [Chr{xx}], T.LKey{}, back, qkind, arrtab),
      kl.b1.fast(dt, rows, heads, here, parts, back, qkind, arrtab, xx, ee)))

# WP-K3: a document of one key/value line. Its first character goes through
# the byte-order-mark check; for a segment's first character that is the
# line-start step. The walk from the empty root misses every name, so each
# segment makes a new table, and at finds the value through them.

# a document's first segment starts as one at the start of a line does
def kl.start1(
  sg: D3.Seg,
  +xs: String,
  +eo: {L6.seg.ok(sg) == True{} : Bool}
) -> {T.doc.read(String.append(L6.seg.text(sg), xs), T.MScan{T.st.start()})
  == T.doc.read(String.append(L6.seg.text(sg), xs), T.MScan{L6.hb.line([], [], [], T.LTop{}, T.QBasic{},
    False{})}) : T.Doc}:
  match sg:
    case D3.Seg{sp, +name}:
      match sp:
        case D3.SpBare{}:
          match name:
            case SNil{}:
              Eq.bit.absurd(&2, {T.doc.read(String.append(SNil{}, xs), T.MScan{T.st.start()})
                == T.doc.read(String.append(SNil{}, xs), T.MScan{L6.hb.line([], [], [], T.LTop{}, T.QBasic{},
                False{})}) : T.Doc}, eo)
            case SCon{hh, +tt}:
              match hh:
                case Chr{+xx}:
                  Equal.trans(T.Doc,
                    T.doc.read(String.append(tt, xs), T.doc.scan(T.st.start(), Chr{xx})),
                    T.doc.read(String.append(tt, xs), T.MScan{M1.ky([Chr{xx}])}),
                    T.doc.read(String.append(tt, xs), T.doc.scan(L6.hb.line([], [], [], T.LTop{}, T.QBasic{},
                      False{}), Chr{xx})),
                    Equal.cong(T.Mode, T.Doc, md => T.doc.read(String.append(tt, xs), md),
                      T.doc.scan(T.st.start(), Chr{xx}), T.MScan{M1.ky([Chr{xx}])},
                      M1.key.first(xx, M13.ball.head(T.bare.at(Chr{xx}), String.to_list(tt), eo))),
                    Equal.sym(T.Doc,
                      T.doc.read(String.append(tt, xs), T.doc.scan(L6.hb.line([], [], [], T.LTop{}, T.QBasic{},
                        False{}), Chr{xx})),
                      T.doc.read(String.append(tt, xs), T.MScan{M1.ky([Chr{xx}])}),
                      Equal.cong(T.Mode, T.Doc, md => T.doc.read(String.append(tt, xs), md),
                        T.doc.scan(L6.hb.line([], [], [], T.LTop{}, T.QBasic{}, False{}), Chr{xx}),
                        T.MScan{M1.ky([Chr{xx}])},
                        kl.b1(False{}, [], [], [], [], T.LTop{}, T.QBasic{}, False{}, xx,
                          M13.ball.head(T.bare.at(Chr{xx}), String.to_list(tt), eo)))))
        case D3.SpBasic{}:
          {==}
        case D3.SpLit{}:
          {==}

# a path one segment longer names its table by that segment after the path
def wa.ja(
  aa: List<&2, String>,
  +pre: String,
  +nn: String
) -> {D1.tb.join(List.append(&2, String, aa, [nn]), pre) == T.tree.pre(D1.tb.join(aa, pre), nn) : String}:
  match aa:
    case []:
      {==}
    case +seg <> +rest:
      wa.ja(rest, T.tree.pre(pre, seg), nn)

# the rest of the walk from a quoted header segment with buf in its buffer, whatever
# back, uni and left are
def qh.Then(
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  @b2: T.Lex -> @u2: U32 -> @l2: U32 ->
    PP(T.doc.read(rest, T.MScan{M1.qh(rw, hs, he, ps, sk, ab, b2, u2, l2, buf)}))

# one character's escape read in a quoted header segment, then the rest of the text
def qh.Goal(
  +uu: U32,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  qh.Then(rw, hs, he, ps, sk, ab, Chr{uu} <> buf, rest, PP) ->
    PP(T.doc.read(String.append(L7.esc(Chr{uu}), rest), T.MScan{M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf, buf)}))

# the fast step of a character in a quoted header segment is the key's full step
def qh.fast(
  +uu: U32,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>
) -> {T.read.fast(M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu}) == T.read.once2(T.lex.kq.go(U32.is_eq(uu,
    34),
  U32.is_eq(uu, 92), True{}, Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)), M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf, buf),  # noqa: S002
  Chr{uu}, T.LHeadGap{}, T.LHeadQ{})) : T.St}:
  {==}

# a character that is no control is pushed: str.bad passes it
def qh.char(
  ctl: Bool,
  +uu: U32,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  hc: {ctl == False{} : Bool}
) -> {T.read.once2(T.lex.kq.char.go(T.str.bad.go(ctl, U32.is_eq(uu, 9), Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)),
  False{}), M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu}, T.LHeadQ{}))
  == M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf) : T.St}:
  match ctl:
    case False{}:
      {==}
    case True{}:
      Eq.bit.absurd2(&2, {T.read.once2(T.lex.kq.char.go(T.str.bad.go(True{}, U32.is_eq(uu, 9),
        Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)), False{}), M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf, buf),
            Chr{uu},
        T.LHeadQ{})) == M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf) : T.St}, hc)

# a character that is no quote, no backslash and no newline is no closer and
# no escape
def qh.go(
  quote: Bool,
  bs: Bool,
  nl: Bool,
  +uu: U32,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  hq: {quote == False{} : Bool},
  hb: {bs == False{} : Bool},
  hn: {nl == False{} : Bool},
  hc: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool}
) -> {T.read.once2(T.lex.kq.go(quote, bs, True{}, nl, M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu},
  T.LHeadGap{},
  T.LHeadQ{})) == M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf) : T.St}:
  match quote:
    case True{}:
      Eq.bit.absurd2(&2, {T.read.once2(T.lex.kq.go(True{}, bs, True{}, nl, M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf,
          buf),
        Chr{uu}, T.LHeadGap{}, T.LHeadQ{})) == M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf) : T.St}, hq)
    case False{}:
      match bs:
        case True{}:
          Eq.bit.absurd2(&2, {T.read.once2(T.lex.kq.go(False{}, True{}, True{}, nl, M1.qh(rw, hs, he, ps, sk, ab, bk,
              un,
            lf, buf), Chr{uu}, T.LHeadGap{}, T.LHeadQ{})) == M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf)
            : T.St}, hb)
        case False{}:
          match nl:
            case True{}:
              Eq.bit.absurd2(&2, {T.read.once2(T.lex.kq.go(False{}, False{}, True{}, True{}, M1.qh(rw, hs, he, ps, sk,
                ab, bk, un, lf, buf), Chr{uu}, T.LHeadGap{}, T.LHeadQ{})) == M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf,
                Chr{uu} <> buf) : T.St}, hn)
            case False{}:
              qh.char(Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), uu, rw, hs, he, ps, sk, ab, bk, un, lf, buf, hc)

# the fast step pushes a character
def qh.Fast(
  +uu: U32,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>
) -> Type:
  {T.read.fast(M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu})
    == M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf) : T.St}

# the doc.scan dispatch sends such a character to the fast step, and an
# apostrophe comes back from doc.wrap in the key's state
def qh.q(
  dq: Bool,
  sq: Bool,
  cr: Bool,
  +uu: U32,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  hq: {dq == False{} : Bool},
  hr: {cr == False{} : Bool},
  fast: qh.Fast(uu, rw, hs, he, ps, sk, ab, bk, un, lf, buf)
) -> {T.doc.scan.q(dq, sq, cr, M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu})
  == T.MScan{M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf)} : T.Mode}:
  match dq:
    case True{}:
      Eq.bit.absurd2(&2, {T.doc.scan.q(True{}, sq, cr, M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu})
        == T.MScan{M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf)} : T.Mode}, hq)
    case False{}:
      match sq:
        case True{}:
          Equal.cong(T.St, T.Mode, st => T.doc.wrap(st),
            T.read.fast(M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu}),
            M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf), fast)
        case False{}:
          match cr:
            case True{}:
              Eq.bit.absurd2(&2, {T.doc.scan.q(False{}, False{}, True{}, M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf, buf),
                Chr{uu}) == T.MScan{M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf)} : T.Mode}, hr)
            case False{}:
              Equal.cong(T.St, T.Mode, st => T.MScan{st},
                T.read.fast(M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu}),
                M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf), fast)

# a character written as itself is pushed, and back, uni and left stay
def qh.plain(
  +uu: U32,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  +e34: {U32.is_eq(uu, 34) == False{} : Bool},
  +e92: {U32.is_eq(uu, 92) == False{} : Bool},
  +ec: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool},
  ih: qh.Then(rw, hs, he, ps, sk, ab, Chr{uu} <> buf, rest, PP)
) -> PP(T.doc.read(String.append(L7.esc(Chr{uu}), rest), T.MScan{M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf, buf)})):
  +e10 = {M2.ctl.off(uu, 10, ec, {==}) : {U32.is_eq(uu, 10) == False{} : Bool}}
  +e13 = {M2.ctl.off(uu, 13, ec, {==}) : {U32.is_eq(uu, 13) == False{} : Bool}}
  %Equal.sym(String, L7.esc(Chr{uu}), SCon{Chr{uu}, SNil{}}, M13.esc.pl2(uu, e34, e92, ec)) :
    PP(T.doc.read(String.append(_, rest), T.MScan{M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf, buf)}))
  M13.pp.step(PP,
    T.doc.read(rest, T.doc.scan(M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu})),
    T.doc.read(rest, T.MScan{M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf)}),
    Equal.cong(T.Mode, T.Doc, md => T.doc.read(rest, md),
      T.doc.scan(M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu}),
      T.MScan{M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf)},
      qh.q(U32.is_eq(uu, 34), U32.is_eq(uu, 39), U32.is_eq(uu, 13), uu, rw, hs, he, ps, sk, ab, bk, un, lf, buf, e34,
        e13, Equal.trans(T.St, T.read.fast(M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu}),
          T.read.once2(T.lex.kq.go(U32.is_eq(uu, 34), U32.is_eq(uu, 92), True{},
            Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)), M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu},
            T.LHeadGap{}, T.LHeadQ{})),
          M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf),
          qh.fast(uu, rw, hs, he, ps, sk, ab, bk, un, lf, buf),
          qh.go(U32.is_eq(uu, 34), U32.is_eq(uu, 92), Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)), uu, rw, hs, he,
            ps, sk, ab, bk, un, lf, buf, e34, e92, M13.or.ff(U32.is_eq(uu, 10), U32.is_eq(uu, 13), e10, e13), ec)))),
    ih(bk, un, lf))

# a quotation mark: its escape reads back by computation, and leaves back at
# the key's state and uni and left as they were
def qh.q34(
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type
) -> qh.Goal(34, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP):
  ih => ih(T.LHeadQ{}, un, lf)

# and a backslash
def qh.q92(
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type
) -> qh.Goal(92, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP):
  ih => ih(T.LHeadQ{}, un, lf)

# CTL: qh.Goal with the escape's text as ss, for ctl.esc.all
def qh.GoalS(
  +uu: U32,
  ss: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  qh.Then(rw, hs, he, ps, sk, ab, Chr{uu} <> buf, rest, PP) ->
    PP(T.doc.read(String.append(ss, rest), T.MScan{M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf, buf)}))

# a control: each of the thirty-three escapes reads back by computation and
# leaves back at the key's state. The five with a letter (\b, \t, \n, \f,
# \r) leave uni and left as they were; a \u escape leaves both at 0
def qh.ctl(
  +uu: U32,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  h_c: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == True{} : Bool}
) -> qh.Goal(uu, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP):
  M2.ctl.esc.all(kk => ss => qh.GoalS(kk, ss, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP), uu, h_c,
    ih => ih(T.LHeadQ{}, 0, 0),
    ih => ih(T.LHeadQ{}, 0, 0),
    ih => ih(T.LHeadQ{}, 0, 0),
    ih => ih(T.LHeadQ{}, 0, 0),
    ih => ih(T.LHeadQ{}, 0, 0),
    ih => ih(T.LHeadQ{}, 0, 0),
    ih => ih(T.LHeadQ{}, 0, 0),
    ih => ih(T.LHeadQ{}, 0, 0),
    ih => ih(T.LHeadQ{}, un, lf),
    ih => ih(T.LHeadQ{}, un, lf),
    ih => ih(T.LHeadQ{}, un, lf),
    ih => ih(T.LHeadQ{}, 0, 0),
    ih => ih(T.LHeadQ{}, un, lf),
    ih => ih(T.LHeadQ{}, un, lf),
    ih => ih(T.LHeadQ{}, 0, 0),
    ih => ih(T.LHeadQ{}, 0, 0),
    ih => ih(T.LHeadQ{}, 0, 0),
    ih => ih(T.LHeadQ{}, 0, 0),
    ih => ih(T.LHeadQ{}, 0, 0),
    ih => ih(T.LHeadQ{}, 0, 0),
    ih => ih(T.LHeadQ{}, 0, 0),
    ih => ih(T.LHeadQ{}, 0, 0),
    ih => ih(T.LHeadQ{}, 0, 0),
    ih => ih(T.LHeadQ{}, 0, 0),
    ih => ih(T.LHeadQ{}, 0, 0),
    ih => ih(T.LHeadQ{}, 0, 0),
    ih => ih(T.LHeadQ{}, 0, 0),
    ih => ih(T.LHeadQ{}, 0, 0),
    ih => ih(T.LHeadQ{}, 0, 0),
    ih => ih(T.LHeadQ{}, 0, 0),
    ih => ih(T.LHeadQ{}, 0, 0),
    ih => ih(T.LHeadQ{}, 0, 0),
    ih => ih(T.LHeadQ{}, 0, 0))

# one code point k that the test found: its answer answers for the character
def qh.is(
  +uu: U32,
  +kk: U32,
  ee: {U32.is_eq(uu, kk) == True{} : Bool},
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  at: qh.Goal(kk, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP)
) -> qh.Goal(uu, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP):
  eu = Equal.cong(Char, U32, cc => Char.to_u32(cc), Chr{uu}, Chr{kk}, Eq.u32_eq(uu, kk, ee))
  %Equal.sym(U32, uu, kk, eu) : qh.Goal(_, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP)
  at

# every character: a quote, a backslash, a control, or one written as itself
def qh.split(
  +uu: U32,
  q34: Bool,
  b92: Bool,
  ctl: Bool,
  +e34: {U32.is_eq(uu, 34) == q34 : Bool},
  +e92: {U32.is_eq(uu, 92) == b92 : Bool},
  +ec: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == ctl : Bool},
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type
) -> qh.Goal(uu, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP):
  match q34:
    case True{}:
      qh.is(uu, 34, e34, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP,
        qh.q34(rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP))
    case False{}:
      match b92:
        case True{}:
          qh.is(uu, 92, e92, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP,
            qh.q92(rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP))
        case False{}:
          match ctl:
            case True{}:
              qh.ctl(uu, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP, ec)
            case False{}:
              ih => qh.plain(uu, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP, e34, e92, ec, ih)

# one character of a quoted header segment
def qh.one(
  +uu: U32,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type
) -> qh.Goal(uu, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP):
  qh.split(uu, U32.is_eq(uu, 34), U32.is_eq(uu, 92), Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), {==}, {==}, {==},
    rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, PP)

# every character of a name, as escs writes it, read in a quoted header segment: the
# rest is read with the characters pushed, from wherever the last escape
# left back, uni and left
def qh.escs(
  ss: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +rest: String,
  -PP: T.Doc -> Type,
  ih: qh.Then(rw, hs, he, ps, sk, ab, M5.rev.onto(ss, buf), rest, PP)
) -> PP(T.doc.read(String.append(L7.escs(ss), rest), T.MScan{M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf, buf)})):
  match ss:
    case SNil{}:
      ih(bk, un, lf)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+uu}:
          M13.pp.step(PP,
            T.doc.read(String.append(String.append(L7.esc(Chr{uu}), L7.escs(tt)), rest),
              T.MScan{M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf, buf)}),
            T.doc.read(String.append(L7.esc(Chr{uu}), String.append(L7.escs(tt), rest)),
              T.MScan{M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf, buf)}),
            Equal.cong(String, T.Doc, xs => T.doc.read(xs, T.MScan{M1.qh(rw, hs, he, ps, sk, ab, bk, un, lf, buf)}),
              String.append(String.append(L7.esc(Chr{uu}), L7.escs(tt)), rest),
              String.append(L7.esc(Chr{uu}), String.append(L7.escs(tt), rest)),
              Eq.append_assoc(L7.esc(Chr{uu}), L7.escs(tt), rest)),
            qh.one(uu, rw, hs, he, ps, sk, ab, bk, un, lf, buf, String.append(L7.escs(tt), rest), PP)(
              b2 => u2 => l2 => qh.escs(tt, rw, hs, he, ps, sk, ab, b2, u2, l2, Chr{uu} <> buf, rest, PP, ih)))

# A header after a value, read as WP-H reads one but with uni and left free,
# and the rest of the text taken as a motive over the document rather than an
# equation, as the key lines are (hm). The steps that do not depend on the
# state (wh.go.bare, wh.dot.bare, wh.bname, wh.join and the list lemmas) are
# WP-H's.

# a scanner inside a header, uni and left as a value before it left them
def hm.st(
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  parts: List<&2, String>,
  buf: List<&2, Char>,
  lex: T.Lex,
  back: T.Lex,
  qkind: T.QKind,
  un: U32,
  lf: U32,
  arrtab: Bool
) -> T.St:
  T.St{"", rows, heads, here, parts, buf, lex, back, qkind, [], T.HNone{}, un, lf, arrtab, False{}}

# the scanner after a segment and what follows it: waiting for the next
# segment after a dot, or closed after the bracket
def hm.aft(
  cl: Bool,
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  parts: List<&2, String>,
  back: T.Lex,
  qkind: T.QKind,
  un: U32,
  lf: U32,
  +arrtab: Bool
) -> T.St:
  match cl:
    case False{}:
      hm.st(rows, heads, here, parts, [], T.LHeadDot{}, back, qkind, un, lf, arrtab)
    case True{}:
      T.read.once2(T.lex.head.close2(arrtab, hm.st(rows, heads, here, parts, [], T.LHeadGap{}, back, qkind, un, lf,
        arrtab)))

# the rest of the text after a segment, from every back, qkind, uni and left
def hm.Then(
  cl: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +arrtab: Bool,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  @bk: T.Lex -> @qk: T.QKind -> @u2: U32 -> @l2: U32 ->
    PP(T.doc.read(rest, T.MScan{hm.aft(cl, rows, heads, here, parts, bk, qk, u2, l2, arrtab)}))

# the first character of a bare segment starts its buffer
def hm.b1.fast(
  dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +un: U32,
  +lf: U32,
  +arrtab: Bool,
  +xx: U32,
  +ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.read.fast(hm.st(rows, heads, here, wh.ps(dt, parts), [], wh.lex0(dt), back, qkind, un, lf, arrtab), Chr{xx})
  == hm.st(rows, heads, here, wh.ps(dt, parts), [Chr{xx}], T.LHead{}, back, qkind, un, lf, arrtab) : T.St}:
  match dt:
    case False{}:
      Equal.cong(T.St, T.St, st => T.read.once2(st),
        T.lex.head.go(Char.is_eq(Chr{xx}, '['), T.bare.at(Chr{xx}), T.ch.sp(Chr{xx}), Char.is_eq(Chr{xx}, '.'),
          Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), Char.is_eq(Chr{xx}, '#'),
          hm.st(rows, heads, here, [], [], T.LHead{}, back, qkind, un, lf, arrtab), Chr{xx}),
        T.lex.head.ch(hm.st(rows, heads, here, [], [], T.LHead{}, back, qkind, un, lf, arrtab), Chr{xx}),
        M7.wh.go.bare(Char.is_eq(Chr{xx}, '['), T.bare.at(Chr{xx}), T.ch.sp(Chr{xx}), Char.is_eq(Chr{xx}, '.'),
          Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), Char.is_eq(Chr{xx}, '#'),
          hm.st(rows, heads, here, [], [], T.LHead{}, back, qkind, un, lf, arrtab), xx, {==}, {==}, ee))
    case True{}:
      Equal.cong(T.St, T.St, st => T.read.once2(st),
        T.lex.hdot(T.ch.sp(Chr{xx}), T.bare.at(Chr{xx}), Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''),
          hm.st(rows, heads, here, parts, [], T.LHeadDot{}, back, qkind, un, lf, arrtab), Chr{xx}),
        T.st.push(hm.st(rows, heads, here, parts, [], T.LHeadDot{}, back, qkind, un, lf, arrtab), Chr{xx}, T.LHead{}),
        M7.wh.dot.bare(T.ch.sp(Chr{xx}), T.bare.at(Chr{xx}), Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''),
          hm.st(rows, heads, here, parts, [], T.LHeadDot{}, back, qkind, un, lf, arrtab), xx, {==}, {==}, ee))

# and the scan mode sends it there
def hm.b1(
  +dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +un: U32,
  +lf: U32,
  +arrtab: Bool,
  +xx: U32,
  +ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.doc.scan(hm.st(rows, heads, here, wh.ps(dt, parts), [], wh.lex0(dt), back, qkind, un, lf, arrtab), Chr{xx})
  == T.MScan{hm.st(rows, heads, here, wh.ps(dt, parts), [Chr{xx}], T.LHead{}, back, qkind, un, lf, arrtab)} : T.Mode}:
  +st = {hm.st(rows, heads, here, wh.ps(dt, parts), [], wh.lex0(dt), back, qkind, un, lf, arrtab) : T.St}
  Equal.trans(T.Mode, T.doc.scan(st, Chr{xx}), T.MScan{T.read.fast(st, Chr{xx})},
    T.MScan{hm.st(rows, heads, here, wh.ps(dt, parts), [Chr{xx}], T.LHead{}, back, qkind, un, lf, arrtab)},
    M8.scan.other(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), U32.is_eq(xx, 13), st, Chr{xx}, {==}, {==}, {==},
      ch => T.bare.at(ch), ee, {==}, {==}, {==}),
    Equal.cong(T.St, T.Mode, s2 => T.MScan{s2}, T.read.fast(st, Chr{xx}),
      hm.st(rows, heads, here, wh.ps(dt, parts), [Chr{xx}], T.LHead{}, back, qkind, un, lf, arrtab),
      hm.b1.fast(dt, rows, heads, here, parts, back, qkind, un, lf, arrtab, xx, ee)))

# with a segment open, the next bare character joins it, whatever came before
def hm.ch.later(
  parts: List<&2, String>,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +dd: Char,
  +bb: List<&2, Char>,
  +back: T.Lex,
  +qkind: T.QKind,
  +un: U32,
  +lf: U32,
  +arrtab: Bool,
  +cc: Char
) -> {T.read.once2(T.lex.head.ch(hm.st(rows, heads, here, parts, dd <> bb, T.LHead{}, back, qkind, un, lf, arrtab), cc))
  == hm.st(rows, heads, here, parts, cc <> dd <> bb, T.LHead{}, back, qkind, un, lf, arrtab) : T.St}:
  match parts:
    case []:
      {==}
    case _p <> _ps:
      {==}

# a later character of a bare segment, from the scan mode
def hm.b2(
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +dd: Char,
  +bb: List<&2, Char>,
  +back: T.Lex,
  +qkind: T.QKind,
  +un: U32,
  +lf: U32,
  +arrtab: Bool,
  +xx: U32,
  +ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.doc.scan(hm.st(rows, heads, here, parts, dd <> bb, T.LHead{}, back, qkind, un, lf, arrtab), Chr{xx})
  == T.MScan{hm.st(rows, heads, here, parts, Chr{xx} <> dd <> bb, T.LHead{}, back, qkind, un, lf, arrtab)} : T.Mode}:
  +st = {hm.st(rows, heads, here, parts, dd <> bb, T.LHead{}, back, qkind, un, lf, arrtab) : T.St}
  Equal.trans(T.Mode, T.doc.scan(st, Chr{xx}), T.MScan{T.read.fast(st, Chr{xx})},
    T.MScan{hm.st(rows, heads, here, parts, Chr{xx} <> dd <> bb, T.LHead{}, back, qkind, un, lf, arrtab)},
    M8.scan.other(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), U32.is_eq(xx, 13), st, Chr{xx}, {==}, {==}, {==},
      ch => T.bare.at(ch), ee, {==}, {==}, {==}),
    Equal.cong(T.St, T.Mode, s2 => T.MScan{s2}, T.read.fast(st, Chr{xx}),
      hm.st(rows, heads, here, parts, Chr{xx} <> dd <> bb, T.LHead{}, back, qkind, un, lf, arrtab),
      Equal.trans(T.St,
        T.read.once2(T.lex.head.go(Char.is_eq(Chr{xx}, '['), T.bare.at(Chr{xx}), T.ch.sp(Chr{xx}),
          Char.is_eq(Chr{xx}, '.'), Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''),
          Char.is_eq(Chr{xx}, '#'), st, Chr{xx})),
        T.read.once2(T.lex.head.ch(st, Chr{xx})),
        hm.st(rows, heads, here, parts, Chr{xx} <> dd <> bb, T.LHead{}, back, qkind, un, lf, arrtab),
        Equal.cong(T.St, T.St, s2 => T.read.once2(s2),
          T.lex.head.go(Char.is_eq(Chr{xx}, '['), T.bare.at(Chr{xx}), T.ch.sp(Chr{xx}), Char.is_eq(Chr{xx}, '.'),
            Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), Char.is_eq(Chr{xx}, '#'), st,
            Chr{xx}),
          T.lex.head.ch(st, Chr{xx}),
          M7.wh.go.bare(Char.is_eq(Chr{xx}, '['), T.bare.at(Chr{xx}), T.ch.sp(Chr{xx}), Char.is_eq(Chr{xx}, '.'),
            Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), Char.is_eq(Chr{xx}, '#'), st,
            xx, {==}, {==}, ee)),
        hm.ch.later(parts, rows, heads, here, dd, bb, back, qkind, un, lf, arrtab, Chr{xx}))))

# the rest of a bare segment is pushed onto its buffer, whatever follows it
def hm.bbody(
  ks: String,
  +rr: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +dd: Char,
  +bb: List<&2, Char>,
  +back: T.Lex,
  +qkind: T.QKind,
  +un: U32,
  +lf: U32,
  +arrtab: Bool,
  +ee: {T.bare.all(String.to_list(ks)) == True{} : Bool}
) -> {T.doc.read(String.append(ks, rr), T.MScan{hm.st(rows, heads, here, parts, dd <> bb, T.LHead{}, back, qkind, un,
  lf, arrtab)}) == T.doc.read(rr, T.MScan{hm.st(rows, heads, here, parts, M5.rev.onto(ks, dd <> bb), T.LHead{}, back,
    qkind,
  un, lf, arrtab)}) : T.Doc}:
  match ks:
    case SNil{}:
      {==}
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          Equal.trans(T.Doc,
            T.doc.read(String.append(tt, rr), T.doc.scan(hm.st(rows, heads, here, parts, dd <> bb, T.LHead{}, back,
              qkind, un, lf, arrtab), Chr{xx})),
            T.doc.read(String.append(tt, rr), T.MScan{hm.st(rows, heads, here, parts, Chr{xx} <> dd <> bb, T.LHead{},
              back, qkind, un, lf, arrtab)}),
            T.doc.read(rr, T.MScan{hm.st(rows, heads, here, parts, M5.rev.onto(tt, Chr{xx} <> dd <> bb), T.LHead{},
                back,
              qkind, un, lf, arrtab)}),
            Equal.cong(T.Mode, T.Doc, md => T.doc.read(String.append(tt, rr), md),
              T.doc.scan(hm.st(rows, heads, here, parts, dd <> bb, T.LHead{}, back, qkind, un, lf, arrtab), Chr{xx}),
              T.MScan{hm.st(rows, heads, here, parts, Chr{xx} <> dd <> bb, T.LHead{}, back, qkind, un, lf, arrtab)},
              hm.b2(rows, heads, here, parts, dd, bb, back, qkind, un, lf, arrtab, xx,
                M13.ball.head(T.bare.at(Chr{xx}), String.to_list(tt), ee))),
            hm.bbody(tt, rr, rows, heads, here, parts, Chr{xx}, dd <> bb, back, qkind, un, lf, arrtab,
              M13.ball.tail(T.bare.at(Chr{xx}), String.to_list(tt), ee)))

# the bracket closes the header the same way whatever state the last segment
# ended in
def hm.lexfree(
  arrtab: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +pp: String,
  +ps: List<&2, String>,
  +lx: T.Lex,
  +back: T.Lex,
  +qkind: T.QKind,
  +un: U32,
  +lf: U32
) -> {T.read.once2(T.lex.head.close2(arrtab, hm.st(rows, heads, here, pp <> ps, [], lx, back, qkind, un, lf, arrtab)))
  == T.read.once2(T.lex.head.close2(arrtab, hm.st(rows, heads, here, pp <> ps, [], T.LHeadGap{}, back, qkind, un, lf,
    arrtab))) : T.St}:
  match arrtab:
    case False{}:
      {==}
    case True{}:
      {==}

# a dot or the bracket ends an open bare segment and pushes it
def hm.bdl(
  cl: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +bf: List<&2, Char>,
  +back: T.Lex,
  +qkind: T.QKind,
  +un: U32,
  +lf: U32,
  +arrtab: Bool,
  +rest: String,
  full: {List.is_empty(&2, Char, bf) == False{} : Bool}
) -> {T.doc.read(SCon{wh.dl(cl), rest}, T.MScan{hm.st(rows, heads, here, parts, bf, T.LHead{}, back, qkind, un, lf,
  arrtab)}) == T.doc.read(rest, T.MScan{hm.aft(cl, rows, heads, here, T.buf.str(bf) <> parts, back, qkind, un, lf,
  arrtab)}) : T.Doc}:
  match cl:
    case False{}:
      Equal.cong(Bool, T.Doc,
        bt => T.doc.read(rest, T.MScan{T.read.once2(T.lex.head.dot3(bt, hm.st(rows, heads, here, parts, bf, T.LHead{},
          back, qkind, un, lf, arrtab)))}),
        List.is_empty(&2, Char, bf), False{}, full)
    case True{}:
      Equal.trans(T.Doc,
        T.doc.read(rest, T.MScan{T.read.once2(T.lex.head.close.go(List.is_empty(&2, Char, bf), arrtab, hm.st(rows,
          heads, here, parts, bf, T.LHead{}, back, qkind, un, lf, arrtab)))}),
        T.doc.read(rest, T.MScan{T.read.once2(T.lex.head.close.go(False{}, arrtab, hm.st(rows, heads, here, parts, bf,
          T.LHead{}, back, qkind, un, lf, arrtab)))}),
        T.doc.read(rest, T.MScan{hm.aft(True{}, rows, heads, here, T.buf.str(bf) <> parts, back, qkind, un, lf,
          arrtab)}),
        Equal.cong(Bool, T.Doc,
          bt => T.doc.read(rest, T.MScan{T.read.once2(T.lex.head.close.go(bt, arrtab, hm.st(rows, heads, here, parts,
            bf, T.LHead{}, back, qkind, un, lf, arrtab)))}),
          List.is_empty(&2, Char, bf), False{}, full),
        Equal.cong(T.St, T.Doc, st => T.doc.read(rest, T.MScan{st}),
          T.read.once2(T.lex.head.close2(arrtab, hm.st(rows, heads, here, T.buf.str(bf) <> parts, [], T.LHead{}, back,
            qkind, un, lf, arrtab))),
          T.read.once2(T.lex.head.close2(arrtab, hm.st(rows, heads, here, T.buf.str(bf) <> parts, [], T.LHeadGap{},
            back, qkind, un, lf, arrtab))),
          hm.lexfree(arrtab, rows, heads, here, T.buf.str(bf), parts, T.LHead{}, back, qkind, un, lf)))

# a bare segment and the dot or bracket after it: the rest is read with the
# segment pushed, and back, qkind, uni and left as they were
def hm.bseg(
  +xx: U32,
  +tt: String,
  +cl: Bool,
  +dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +un: U32,
  +lf: U32,
  +arrtab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  +ee: {T.bare.all.step(T.bare.at(Chr{xx}), _u => T.bare.all(String.to_list(tt))) == True{} : Bool},
  ih: hm.Then(cl, rows, heads, here, SCon{Chr{xx}, tt} <> wh.ps(dt, parts), arrtab, rest, PP)
) -> PP(T.doc.read(String.append(SCon{Chr{xx}, tt}, SCon{wh.dl(cl), rest}), T.MScan{hm.st(rows, heads, here,
  wh.ps(dt, parts), [], wh.lex0(dt), back, qkind, un, lf, arrtab)})):
  +ps = {wh.ps(dt, parts) : List<&2, String>}
  M13.pp.step(PP,
    T.doc.read(String.append(tt, SCon{wh.dl(cl), rest}), T.doc.scan(hm.st(rows, heads, here, ps, [], wh.lex0(dt), back,
      qkind, un, lf, arrtab), Chr{xx})),
    T.doc.read(rest, T.MScan{hm.aft(cl, rows, heads, here, SCon{Chr{xx}, tt} <> ps, back, qkind, un, lf, arrtab)}),
    Equal.trans(T.Doc,
      T.doc.read(String.append(tt, SCon{wh.dl(cl), rest}), T.doc.scan(hm.st(rows, heads, here, ps, [], wh.lex0(dt),
        back, qkind, un, lf, arrtab), Chr{xx})),
      T.doc.read(String.append(tt, SCon{wh.dl(cl), rest}), T.MScan{hm.st(rows, heads, here, ps, [Chr{xx}], T.LHead{},
        back, qkind, un, lf, arrtab)}),
      T.doc.read(rest, T.MScan{hm.aft(cl, rows, heads, here, SCon{Chr{xx}, tt} <> ps, back, qkind, un, lf, arrtab)}),
      Equal.cong(T.Mode, T.Doc, md => T.doc.read(String.append(tt, SCon{wh.dl(cl), rest}), md),
        T.doc.scan(hm.st(rows, heads, here, ps, [], wh.lex0(dt), back, qkind, un, lf, arrtab), Chr{xx}),
        T.MScan{hm.st(rows, heads, here, ps, [Chr{xx}], T.LHead{}, back, qkind, un, lf, arrtab)},
        hm.b1(dt, rows, heads, here, parts, back, qkind, un, lf, arrtab, xx,
          M13.ball.head(T.bare.at(Chr{xx}), String.to_list(tt), ee))),
      Equal.trans(T.Doc,
        T.doc.read(String.append(tt, SCon{wh.dl(cl), rest}), T.MScan{hm.st(rows, heads, here, ps, [Chr{xx}],
          T.LHead{}, back, qkind, un, lf, arrtab)}),
        T.doc.read(SCon{wh.dl(cl), rest}, T.MScan{hm.st(rows, heads, here, ps, M5.rev.onto(tt, [Chr{xx}]), T.LHead{},
          back, qkind, un, lf, arrtab)}),
        T.doc.read(rest, T.MScan{hm.aft(cl, rows, heads, here, SCon{Chr{xx}, tt} <> ps, back, qkind, un, lf, arrtab)}),
        hm.bbody(tt, SCon{wh.dl(cl), rest}, rows, heads, here, ps, Chr{xx}, [], back, qkind, un, lf, arrtab,
          M13.ball.tail(T.bare.at(Chr{xx}), String.to_list(tt), ee)),
        Equal.trans(T.Doc,
          T.doc.read(SCon{wh.dl(cl), rest}, T.MScan{hm.st(rows, heads, here, ps, M5.rev.onto(tt, [Chr{xx}]), T.LHead{},
            back, qkind, un, lf, arrtab)}),
          T.doc.read(rest, T.MScan{hm.aft(cl, rows, heads, here, T.buf.str(M5.rev.onto(tt, [Chr{xx}])) <> ps, back,
              qkind,
            un, lf, arrtab)}),
          T.doc.read(rest, T.MScan{hm.aft(cl, rows, heads, here, SCon{Chr{xx}, tt} <> ps, back, qkind, un, lf,
            arrtab)}),
          hm.bdl(cl, rows, heads, here, ps, M5.rev.onto(tt, [Chr{xx}]), back, qkind, un, lf, arrtab, rest,
            M13.rev.full(tt, Chr{xx}, [])),
          Equal.cong(String, T.Doc, nm => T.doc.read(rest, T.MScan{hm.aft(cl, rows, heads, here, nm <> ps, back, qkind,
            un, lf, arrtab)}), T.buf.str(M5.rev.onto(tt, [Chr{xx}])), SCon{Chr{xx}, tt}, M13.wh.bname(xx, tt))))),
    ih(back, qkind, un, lf))

# a segment as key writes it, when that is bare
def hm.seg.bare(
  +ss: String,
  +cl: Bool,
  +dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +un: U32,
  +lf: U32,
  +arrtab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  eb: {T.bare(ss) == True{} : Bool},
  ih: hm.Then(cl, rows, heads, here, ss <> wh.ps(dt, parts), arrtab, rest, PP)
) -> PP(T.doc.read(String.append(T.key.go(True{}, ss), SCon{wh.dl(cl), rest}), T.MScan{hm.st(rows, heads, here,
  wh.ps(dt, parts), [], wh.lex0(dt), back, qkind, un, lf, arrtab)})):
  match ss:
    case SNil{}:
      Eq.bit.absurd(&1, PP(T.doc.read(String.append(T.key.go(True{}, SNil{}), SCon{wh.dl(cl), rest}),
        T.MScan{hm.st(rows, heads, here, wh.ps(dt, parts), [], wh.lex0(dt), back, qkind, un, lf, arrtab)})), eb)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          hm.bseg(xx, tt, cl, dt, rows, heads, here, parts, back, qkind, un, lf, arrtab, rest, PP, eb, ih)

# the bracket runs the header's walk along the segments read, and the newline
# returns to the start of a line in the header's table
def hm.fin(
  arrtab: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +un: U32,
  +lf: U32,
  +path: List<&2, String>,
  +rows2: List<&2, T.Val>,
  +heads2: List<&2, String>,
  +rest: String,
  ne: {List.is_empty(&2, String, parts) == False{} : Bool},
  er: {List.reverse(&2, String, parts) == path : List<&2, String>},
  ew: M7.wh.Walk(arrtab, path, rows, heads, rows2, heads2)
) -> {T.doc.read(M7.wh.tail(arrtab, rest), T.MScan{hm.aft(True{}, rows, heads, here, parts, back, qkind, un, lf,
    arrtab)})
  == T.doc.read(rest, T.MScan{M3.dl(rows2, heads2, path, back, qkind, un, lf, False{})}) : T.Doc}:
  match arrtab:
    case False{}:
      Equal.trans(T.Doc,
        T.doc.read(SCon{'\n', rest}, T.MScan{T.read.once2(T.head.go(List.is_empty(&2, String, parts), hm.st(rows,
          heads, here, parts, [], T.LHeadGap{}, back, qkind, un, lf, False{}), List.reverse(&2, String, parts)))}),
        T.doc.read(SCon{'\n', rest}, T.MScan{T.read.once2(T.head.apply(T.tree.walk(List.reverse(&2, String, parts),
          T.Tw{rows, T.JDef{}, [], "", "", heads, False{}}, 0), List.reverse(&2, String, parts), back, qkind, un, lf,
          False{}))}),
        T.doc.read(rest, T.MScan{M3.dl(rows2, heads2, path, back, qkind, un, lf, False{})}),
        Equal.cong(Bool, T.Doc, bt => T.doc.read(SCon{'\n', rest}, T.MScan{T.read.once2(T.head.go(bt, hm.st(rows,
          heads, here, parts, [], T.LHeadGap{}, back, qkind, un, lf, False{}), List.reverse(&2, String, parts)))}),
          List.is_empty(&2, String, parts), False{}, ne),
        Equal.trans(T.Doc,
          T.doc.read(SCon{'\n', rest}, T.MScan{T.read.once2(T.head.apply(T.tree.walk(List.reverse(&2, String, parts),
            T.Tw{rows, T.JDef{}, [], "", "", heads, False{}}, 0), List.reverse(&2, String, parts), back, qkind, un, lf,
            False{}))}),
          T.doc.read(SCon{'\n', rest}, T.MScan{T.read.once2(T.head.apply(T.tree.walk(path, T.Tw{rows, T.JDef{}, [], "",
            "", heads, False{}}, 0), path, back, qkind, un, lf, False{}))}),
          T.doc.read(rest, T.MScan{M3.dl(rows2, heads2, path, back, qkind, un, lf, False{})}),
          Equal.cong(List<&2, String>, T.Doc, sg => T.doc.read(SCon{'\n', rest}, T.MScan{T.read.once2(T.head.apply(
            T.tree.walk(sg, T.Tw{rows, T.JDef{}, [], "", "", heads, False{}}, 0), sg, back, qkind, un, lf,
            False{}))}), List.reverse(&2, String, parts), path, er),
          Equal.cong(T.End, T.Doc, en => T.doc.read(SCon{'\n', rest}, T.MScan{T.read.once2(T.head.apply(en, path, back,
            qkind, un, lf, False{}))}),
            T.tree.walk(path, T.Tw{rows, T.JDef{}, [], "", "", heads, False{}}, 0), T.End{rows2, "", heads2}, ew)))
    case True{}:
      Equal.trans(T.Doc,
        T.doc.read(SCon{'\n', rest}, T.MScan{T.read.once2(T.head.go(List.is_empty(&2, String, parts), hm.st(rows,
          heads, here, parts, [], T.LHeadR{}, back, qkind, un, lf, True{}), List.reverse(&2, String, parts)))}),
        T.doc.read(SCon{'\n', rest}, T.MScan{T.read.once2(T.head.apply(T.tree.walk(List.reverse(&2, String, parts),
          T.Tw{rows, T.JAot{}, [], "", "", heads, False{}}, 0), List.reverse(&2, String, parts), back, qkind, un, lf,
          False{}))}),
        T.doc.read(rest, T.MScan{M3.dl(rows2, heads2, path, back, qkind, un, lf, False{})}),
        Equal.cong(Bool, T.Doc, bt => T.doc.read(SCon{'\n', rest}, T.MScan{T.read.once2(T.head.go(bt, hm.st(rows,
          heads, here, parts, [], T.LHeadR{}, back, qkind, un, lf, True{}), List.reverse(&2, String, parts)))}),
          List.is_empty(&2, String, parts), False{}, ne),
        Equal.trans(T.Doc,
          T.doc.read(SCon{'\n', rest}, T.MScan{T.read.once2(T.head.apply(T.tree.walk(List.reverse(&2, String, parts),
            T.Tw{rows, T.JAot{}, [], "", "", heads, False{}}, 0), List.reverse(&2, String, parts), back, qkind, un, lf,
            False{}))}),
          T.doc.read(SCon{'\n', rest}, T.MScan{T.read.once2(T.head.apply(T.tree.walk(path, T.Tw{rows, T.JAot{}, [], "",
            "", heads, False{}}, 0), path, back, qkind, un, lf, False{}))}),
          T.doc.read(rest, T.MScan{M3.dl(rows2, heads2, path, back, qkind, un, lf, False{})}),
          Equal.cong(List<&2, String>, T.Doc, sg => T.doc.read(SCon{'\n', rest}, T.MScan{T.read.once2(T.head.apply(
            T.tree.walk(sg, T.Tw{rows, T.JAot{}, [], "", "", heads, False{}}, 0), sg, back, qkind, un, lf,
            False{}))}), List.reverse(&2, String, parts), path, er),
          Equal.cong(T.End, T.Doc, en => T.doc.read(SCon{'\n', rest}, T.MScan{T.read.once2(T.head.apply(en, path, back,
            qkind, un, lf, False{}))}),
            T.tree.walk(path, T.Tw{rows, T.JAot{}, [], "", "", heads, False{}}, 0), T.End{rows2, "", heads2}, ew)))

# a quote where a segment starts opens a quoted segment with an empty buffer
def hm.qopen(
  dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +un: U32,
  +lf: U32,
  +arrtab: Bool
) -> {T.doc.scan(hm.st(rows, heads, here, wh.ps(dt, parts), [], wh.lex0(dt), back, qkind, un, lf, arrtab), '"')
  == T.MScan{M1.qh(rows, heads, here, wh.ps(dt, parts), [], arrtab, back, un, lf, [])} : T.Mode}:
  match dt:
    case False{}:
      {==}
    case True{}:
      {==}

# the closing quote pushes the segment, and the dot or bracket after it
# follows, whatever back, uni and left the last escape left
def hm.qend(
  cl: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +arrtab: Bool,
  +back: T.Lex,
  +un: U32,
  +lf: U32,
  +bf: List<&2, Char>,
  +rest: String
) -> {T.doc.read(SCon{'"', SCon{wh.dl(cl), rest}}, T.MScan{M1.qh(rows, heads, here, parts, [], arrtab, back, un, lf,
    bf)})
  == T.doc.read(rest, T.MScan{hm.aft(cl, rows, heads, here, T.buf.str(bf) <> parts, back, T.QBasic{}, un, lf,
    arrtab)}) : T.Doc}:
  match cl:
    case False{}:
      {==}
    case True{}:
      {==}

# a quoted segment as key writes it, then a dot or the bracket: the rest is
# read with the segment pushed under its name, from wherever the last escape
# left back, uni and left, and with qkind basic
def hm.qseg(
  +ss: String,
  +cl: Bool,
  +dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +un: U32,
  +lf: U32,
  +arrtab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  ih: hm.Then(cl, rows, heads, here, ss <> wh.ps(dt, parts), arrtab, rest, PP)
) -> PP(T.doc.read(String.append(T.key.go(False{}, ss), SCon{wh.dl(cl), rest}), T.MScan{hm.st(rows, heads, here,
  wh.ps(dt, parts), [], wh.lex0(dt), back, qkind, un, lf, arrtab)})):
  +ps = {wh.ps(dt, parts) : List<&2, String>}
  +st = {hm.st(rows, heads, here, ps, [], wh.lex0(dt), back, qkind, un, lf, arrtab) : T.St}
  +zz = {SCon{wh.dl(cl), rest} : String}
  %Equal.sym(String, T.key.basic(ss), "\"" ++ L7.escs(ss) ++ "\"", L7.basic_escs(ss)) :
    PP(T.doc.read(String.append(_, zz), T.MScan{st}))
  %Equal.sym(String, String.append(String.append(L7.escs(ss), "\""), zz), String.append(L7.escs(ss), SCon{'"',
    zz}), Eq.append_assoc(L7.escs(ss), "\"", zz)) :
    PP(T.doc.read(SCon{'"', _}, T.MScan{st}))
  M13.pp.step(PP, T.doc.read(String.append(L7.escs(ss), SCon{'"', zz}), T.doc.scan(st, '"')),
    T.doc.read(String.append(L7.escs(ss), SCon{'"', zz}), T.MScan{M1.qh(rows, heads, here, ps, [], arrtab, back, un, lf,
      [])}),
    Equal.cong(T.Mode, T.Doc, md => T.doc.read(String.append(L7.escs(ss), SCon{'"', zz}), md), T.doc.scan(st, '"'),
      T.MScan{M1.qh(rows, heads, here, ps, [], arrtab, back, un, lf, [])},
      hm.qopen(dt, rows, heads, here, parts, back, qkind, un, lf, arrtab)),
    qh.escs(ss, rows, heads, here, ps, [], arrtab, back, un, lf, [], SCon{'"', zz}, PP,
      +b2 => +u2 => +l2 => M13.pp.step(PP,
        T.doc.read(SCon{'"', zz}, T.MScan{M1.qh(rows, heads, here, ps, [], arrtab, b2, u2, l2, M5.rev.onto(ss, []))}),
        T.doc.read(rest, T.MScan{hm.aft(cl, rows, heads, here, ss <> ps, b2, T.QBasic{}, u2, l2, arrtab)}),
        Equal.trans(T.Doc,
          T.doc.read(SCon{'"', zz}, T.MScan{M1.qh(rows, heads, here, ps, [], arrtab, b2, u2, l2, M5.rev.onto(ss, []))}),
          T.doc.read(rest, T.MScan{hm.aft(cl, rows, heads, here, T.buf.str(M5.rev.onto(ss, [])) <> ps, b2, T.QBasic{},
              u2,
            l2, arrtab)}),
          T.doc.read(rest, T.MScan{hm.aft(cl, rows, heads, here, ss <> ps, b2, T.QBasic{}, u2, l2, arrtab)}),
          hm.qend(cl, rows, heads, here, ps, arrtab, b2, u2, l2, M5.rev.onto(ss, []), rest),
          Equal.cong(String, T.Doc, nm => T.doc.read(rest, T.MScan{hm.aft(cl, rows, heads, here, nm <> ps, b2,
            T.QBasic{}, u2, l2, arrtab)}), T.buf.str(M5.rev.onto(ss, [])), ss, wh.qname(ss))),
        ih(b2, T.QBasic{}, u2, l2))))

# a segment as key writes it, bare or quoted, then a dot or the bracket
def hm.seg.go(
  bb: Bool,
  +ss: String,
  +cl: Bool,
  +dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +un: U32,
  +lf: U32,
  +arrtab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  eb: {T.bare(ss) == bb : Bool},
  ih: hm.Then(cl, rows, heads, here, ss <> wh.ps(dt, parts), arrtab, rest, PP)
) -> PP(T.doc.read(String.append(T.key.go(bb, ss), SCon{wh.dl(cl), rest}), T.MScan{hm.st(rows, heads, here,
  wh.ps(dt, parts), [], wh.lex0(dt), back, qkind, un, lf, arrtab)})):
  match bb:
    case True{}:
      hm.seg.bare(ss, cl, dt, rows, heads, here, parts, back, qkind, un, lf, arrtab, rest, PP, eb, ih)
    case False{}:
      hm.qseg(ss, cl, dt, rows, heads, here, parts, back, qkind, un, lf, arrtab, rest, PP, ih)

# a segment as key writes it, then a dot or the bracket
def hm.seg(
  +ss: String,
  +cl: Bool,
  +dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +un: U32,
  +lf: U32,
  +arrtab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  ih: hm.Then(cl, rows, heads, here, ss <> wh.ps(dt, parts), arrtab, rest, PP)
) -> PP(T.doc.read(String.append(T.key(ss), SCon{wh.dl(cl), rest}), T.MScan{hm.st(rows, heads, here, wh.ps(dt, parts),
  [], wh.lex0(dt), back, qkind, un, lf, arrtab)})):
  hm.seg.go(T.bare(ss), ss, cl, dt, rows, heads, here, parts, back, qkind, un, lf, arrtab, rest, PP, {==}, ih)

# segments pushed one by one onto parts
def hm.Segs(
  t: List<&2, String>,
  +ss: String,
  +dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +un: U32,
  +lf: U32,
  +arrtab: Bool,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  hm.Then(True{}, rows, heads, here, List.reverse.go(&2, String, t, ss <> wh.ps(dt, parts)), arrtab, rest, PP) ->
    PP(T.doc.read(String.append(T.key(ss), String.append(wh.more(t), SCon{']', rest})), T.MScan{hm.st(rows, heads, here,
      wh.ps(dt, parts), [], wh.lex0(dt), back, qkind, un, lf, arrtab)}))

# a path's segments and the bracket after them: the rest is read with every
# segment pushed
def hm.segs(
  t: List<&2, String>,
  +ss: String,
  +dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +un: U32,
  +lf: U32,
  +arrtab: Bool,
  +rest: String,
  -PP: T.Doc -> Type
) -> hm.Segs(t, ss, dt, rows, heads, here, parts, back, qkind, un, lf, arrtab, rest, PP):
  match t:
    case []:
      ih => hm.seg(ss, True{}, dt, rows, heads, here, parts, back, qkind, un, lf, arrtab, rest, PP, ih)
    case +xx <> +xs:
      ih => hm.seg(ss, False{}, dt, rows, heads, here, parts, back, qkind, un, lf, arrtab,
        String.append(String.append(T.key(xx), wh.more(xs)), SCon{']', rest}), PP,
        +bk => +qk => +u2 => +l2 => M13.pp.step(PP,
          T.doc.read(String.append(String.append(T.key(xx), wh.more(xs)), SCon{']', rest}), T.MScan{hm.st(rows, heads,
            here, ss <> wh.ps(dt, parts), [], T.LHeadDot{}, bk, qk, u2, l2, arrtab)}),
          T.doc.read(String.append(T.key(xx), String.append(wh.more(xs), SCon{']', rest})), T.MScan{hm.st(rows, heads,
            here, ss <> wh.ps(dt, parts), [], T.LHeadDot{}, bk, qk, u2, l2, arrtab)}),
          Equal.cong(String, T.Doc, zz => T.doc.read(zz, T.MScan{hm.st(rows, heads, here, ss <> wh.ps(dt, parts), [],
            T.LHeadDot{}, bk, qk, u2, l2, arrtab)}),
            String.append(String.append(T.key(xx), wh.more(xs)), SCon{']', rest}),
            String.append(T.key(xx), String.append(wh.more(xs), SCon{']', rest})),
            Eq.append_assoc(T.key(xx), wh.more(xs), SCon{']', rest})),
          hm.segs(xs, xx, True{}, rows, heads, here, ss <> wh.ps(dt, parts), bk, qk, u2, l2, arrtab, rest, PP)(ih)))

# the rest of the text after the header, from the start of the next line
def hm.Line(
  +rows2: List<&2, T.Val>,
  +heads2: List<&2, String>,
  +path: List<&2, String>,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  @bk: T.Lex -> @qk: T.QKind -> @u2: U32 -> @l2: U32 ->
    PP(T.doc.read(rest, T.MScan{M3.dl(rows2, heads2, path, bk, qk, u2, l2, False{})}))

# a whole header line of the segments ss then t, from the start of a line
def hm.core(
  arrtab: Bool,
  +ss: String,
  +t: List<&2, String>,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +un: U32,
  +lf: U32,
  +a0: Bool,
  +rows2: List<&2, T.Val>,
  +heads2: List<&2, String>,
  +rest: String,
  -PP: T.Doc -> Type,
  ew: M7.wh.Walk(arrtab, ss <> t, rows, heads, rows2, heads2),
  ih: hm.Line(rows2, heads2, ss <> t, rest, PP)
) -> PP(T.doc.read(wh.open(arrtab, String.append(T.key(ss), String.append(wh.more(t), SCon{']', M7.wh.tail(arrtab,
  rest)}))), T.MScan{M3.dl(rows, heads, here, back, qkind, un, lf, a0)})):
  match arrtab:
    case False{}:
      hm.segs(t, ss, False{}, rows, heads, here, [], back, qkind, un, lf, False{}, M7.wh.tail(False{}, rest), PP)(
        +bk => +qk => +u2 => +l2 => M13.pp.step(PP,
          T.doc.read(SCon{'\n', rest}, T.MScan{hm.aft(True{}, rows, heads, here, List.reverse.go(&2, String, t, [ss]),
            bk,
            qk, u2, l2, False{})}),
          T.doc.read(rest, T.MScan{M3.dl(rows2, heads2, ss <> t, bk, qk, u2, l2, False{})}),
          hm.fin(False{}, rows, heads, here, List.reverse.go(&2, String, t, [ss]), bk, qk, u2, l2, ss <> t, rows2,
            heads2,
            rest, wh.rne(t, ss, []), wh.rev2(t, ss), ew),
          ih(bk, qk, u2, l2)))
    case True{}:
      hm.segs(t, ss, False{}, rows, heads, here, [], back, qkind, un, lf, True{}, M7.wh.tail(True{}, rest), PP)(
        +bk => +qk => +u2 => +l2 => M13.pp.step(PP,
          T.doc.read(SCon{']', SCon{'\n', rest}}, T.MScan{hm.aft(True{}, rows, heads, here, List.reverse.go(&2, String,
            t,
            [ss]), bk, qk, u2, l2, True{})}),
          T.doc.read(rest, T.MScan{M3.dl(rows2, heads2, ss <> t, bk, qk, u2, l2, False{})}),
          hm.fin(True{}, rows, heads, here, List.reverse.go(&2, String, t, [ss]), bk, qk, u2, l2, ss <> t, rows2,
            heads2,
            rest, wh.rne(t, ss, []), wh.rev2(t, ss), ew),
          ih(bk, qk, u2, l2)))

# a header line as render writes it, from the start of a line after any
# value: the stored path, which is the parent's path joined with the last
# segment
def hm.law(
  +arrtab: Bool,
  segs: List<&2, String>,
  +kk: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +un: U32,
  +lf: U32,
  +a0: Bool,
  +rows2: List<&2, T.Val>,
  +heads2: List<&2, String>,
  +rest: String,
  -PP: T.Doc -> Type,
  ew: M7.wh.Walk(arrtab, List.append(&2, String, segs, [kk]), rows, heads, rows2, heads2),
  ih: hm.Line(rows2, heads2, List.append(&2, String, segs, [kk]), rest, PP)
) -> PP(T.doc.read(wh.open(arrtab, String.append(T.tree.pre(D1.tb.join(segs, ""), kk), SCon{']', M7.wh.tail(arrtab,
  rest)})), T.MScan{M3.dl(rows, heads, here, back, qkind, un, lf, a0)})):
  match segs:
    case []:
      hm.core(arrtab, kk, [], rows, heads, here, back, qkind, un, lf, a0, rows2, heads2, rest, PP, ew, ih)
    case +s0 <> +ss:
      +st = {M3.dl(rows, heads, here, back, qkind, un, lf, a0) : T.St}
      M13.pp.step(PP,
        T.doc.read(wh.open(arrtab, String.append(T.tree.pre(D1.tb.join(ss, T.key(s0)), kk), SCon{']', M7.wh.tail(arrtab,
          rest)})), T.MScan{st}),
        T.doc.read(wh.open(arrtab, String.append(T.key(s0), String.append(wh.more(List.append(&2, String, ss, [kk])),
          SCon{']', M7.wh.tail(arrtab, rest)}))), T.MScan{st}),
        Equal.trans(T.Doc,
          T.doc.read(wh.open(arrtab, String.append(T.tree.pre(D1.tb.join(ss, T.key(s0)), kk), SCon{']',
            M7.wh.tail(arrtab, rest)})), T.MScan{st}),
          T.doc.read(wh.open(arrtab, String.append(String.append(T.key(s0), wh.more(List.append(&2, String, ss, [kk]))),
            SCon{']', M7.wh.tail(arrtab, rest)})), T.MScan{st}),
          T.doc.read(wh.open(arrtab, String.append(T.key(s0), String.append(wh.more(List.append(&2, String, ss, [kk])),
            SCon{']', M7.wh.tail(arrtab, rest)}))), T.MScan{st}),
          Equal.cong(String, T.Doc, pt => T.doc.read(wh.open(arrtab, String.append(pt, SCon{']', M7.wh.tail(arrtab,
            rest)})), T.MScan{st}),
            T.tree.pre(D1.tb.join(ss, T.key(s0)), kk),
            String.append(T.key(s0), wh.more(List.append(&2, String, ss, [kk]))),
            wh.join(ss, T.key(s0), kk, wh.key.ne(s0))),
          Equal.cong(String, T.Doc, pt => T.doc.read(wh.open(arrtab, pt), T.MScan{st}),
            String.append(String.append(T.key(s0), wh.more(List.append(&2, String, ss, [kk]))), SCon{']',
              M7.wh.tail(arrtab, rest)}),
            String.append(T.key(s0), String.append(wh.more(List.append(&2, String, ss, [kk])), SCon{']',
              M7.wh.tail(arrtab, rest)})),
            Eq.append_assoc(T.key(s0), wh.more(List.append(&2, String, ss, [kk])), SCon{']', M7.wh.tail(arrtab,
                rest)}))),
        hm.core(arrtab, s0, List.append(&2, String, ss, [kk]), rows, heads, here, back, qkind, un, lf, a0, rows2,
          heads2,
          rest, PP, ew, ih))

# The walk counts the current table's segments in a U32 (path.len) and counts
# them down again (counts.down), so a key's put needs a table nested fewer
# than 2^32 deep. A table's path, as its header writes it, has a character
# for each segment, so a short path is deep enough: counting its characters
# from zero never wraps, so neither does counting its segments.

# a list's length, counted up from k
def ln2(xs: List<&2, String>, kk: Nat) -> Nat:
  match xs:
    case []:
      kk
    case _h <> t:
      ln2(t, 1n+kk)

# counting from one more is one more
def ln2.s(xs: List<&2, String>, +kk: Nat) -> {ln2(xs, 1n+kk) == 1n+ln2(xs, kk) : Nat}:
  match xs:
    case []:
      {==}
    case _h <> t:
      ln2.s(t, 1n+kk)

# counting a list's elements up from m in a U32 never comes back to zero
def cd.lc(xs: List<&2, String>, +mm: U32) -> Bool:
  match xs:
    case []:
      True{}
    case _h <> t:
      Bool.and(Bool.not(U32.is_zero(U32.add(mm, 1))), cd.lc(t, U32.add(mm, 1)))

# then path.len counts them exactly
def cd.a1(
  xs: List<&2, String>,
  +mm: U32,
  +ee: {cd.lc(xs, mm) == True{} : Bool}
) -> {U32.to_nat(T.path.len(xs, mm)) == ln2(xs, U32.to_nat(mm)) : Nat}:
  match xs:
    case []:
      {==}
    case _h <> +t:
      +ez = {Eq.not.true(U32.is_zero(U32.add(mm, 1)), Eq.and.left(Bool.not(U32.is_zero(U32.add(mm, 1))),
        cd.lc(t, U32.add(mm, 1)), ee)) : {U32.is_zero(U32.add(mm, 1)) == False{} : Bool}}
      Equal.trans(Nat, U32.to_nat(T.path.len(t, U32.add(mm, 1))), ln2(t, U32.to_nat(U32.add(mm, 1))),
        ln2(t, 1n+U32.to_nat(mm)),
        cd.a1(t, U32.add(mm, 1), Eq.and.right(Bool.not(U32.is_zero(U32.add(mm, 1))), cd.lc(t, U32.add(mm, 1)), ee)),
        Equal.cong(Nat, Nat, k2 => ln2(t, k2), U32.to_nat(U32.add(mm, 1)), 1n+U32.to_nat(mm), Eq.inc.nat(mm, ez)))

# one step down from a count one more than the rest's length
def cd.a2s(
  bb: Bool,
  +t: List<&2, String>,
  +ss: U32,
  +eb: {U32.is_zero(ss) == bb : Bool},
  +ee: {U32.to_nat(ss) == 1n+ln2(t, 0n) : Nat},
  ih: @s2: U32 -> {U32.to_nat(s2) == ln2(t, 0n) : Nat} -> {D1.counts.down(t, s2) == True{} : Bool}
) -> {Bool.and(Bool.not(bb), D1.counts.down(t, T.path.dec.z(bb, ss))) == True{} : Bool}:
  match bb:
    case True{}:
      Eq.bit.gone(&2, {Bool.and(Bool.not(True{}), D1.counts.down(t, T.path.dec.z(True{}, ss))) == True{} : Bool},
        Eq.nat.clash(ln2(t, 0n), Equal.trans(Nat, 0n, U32.to_nat(ss), 1n+ln2(t, 0n),
          Equal.sym(Nat, U32.to_nat(ss), 0n, Eq.u32_zero_nat(ss, eb)), ee)))
    case False{}:
      ih(U32.sub(ss, 1), Eq.succ_inj(U32.to_nat(U32.sub(ss, 1)), ln2(t, 0n),
        Equal.trans(Nat, 1n+U32.to_nat(U32.sub(ss, 1)), U32.to_nat(ss), 1n+ln2(t, 0n),
          Equal.sym(Nat, U32.to_nat(ss), 1n+U32.to_nat(U32.sub(ss, 1)), Eq.u32_dec_nat(ss, eb)), ee)))

# a count that is exactly a list's length counts down past every element
def cd.a2(
  xs: List<&2, String>,
  +ss: U32,
  +ee: {U32.to_nat(ss) == ln2(xs, 0n) : Nat}
) -> {D1.counts.down(xs, ss) == True{} : Bool}:
  match xs:
    case []:
      {==}
    case _h <> +t:
      cd.a2s(U32.is_zero(ss), t, ss, {==}, Equal.trans(Nat, U32.to_nat(ss), ln2(t, 1n+0n), 1n+ln2(t, 0n), ee,
        ln2.s(t, 0n)), +s2 => e2 => cd.a2(t, s2, e2))

# the later segments of a short path, each after a dot, count up without
# wrapping
def cd.more(
  xs: List<&2, String>,
  +mm: U32,
  +ee: {D1.counts(wh.more(xs), mm) == True{} : Bool}
) -> {cd.lc(xs, mm) == True{} : Bool}:
  match xs:
    case []:
      {==}
    case +x <> +t:
      M9.cv.and2(Bool.not(U32.is_zero(U32.add(mm, 1))), cd.lc(t, U32.add(mm, 1)),
        Eq.and.left(Bool.not(U32.is_zero(U32.add(mm, 1))), D1.counts(String.append(T.key(x), wh.more(t)),
          U32.add(mm, 1)), ee),
        cd.more(t, U32.add(mm, 1), M9.cd.dp(T.key(x), wh.more(t), U32.add(mm, 1),
          Eq.and.right(Bool.not(U32.is_zero(U32.add(mm, 1))), D1.counts(String.append(T.key(x), wh.more(t)),
            U32.add(mm, 1)), ee))))

# after a first segment of at least one character, the rest of a short
# text is short from one
def cd.k(
  kk: String,
  +ww: String,
  ne: {String.is_empty(kk) == False{} : Bool},
  +ee: {D1.counts(String.append(kk, ww), 0) == True{} : Bool}
) -> {D1.counts(ww, 1) == True{} : Bool}:
  match kk:
    case SNil{}:
      Eq.bit.absurd2(&2, {D1.counts(ww, 1) == True{} : Bool}, ne)
    case SCon{_h, +t}:
      M9.cd.dp(t, ww, 1, Eq.and.right(Bool.not(U32.is_zero(U32.add(0, 1))), D1.counts(String.append(t, ww),
        U32.add(0, 1)), ee))

# a table whose header path is short is nested shallow enough for the walk's
# count: the count of its segments comes down past every one
def cd(
  he: List<&2, String>,
  +kk: String,
  +ee: {D1.short(T.tree.pre(D1.tb.join(he, ""), kk)) == True{} : Bool}
) -> {D1.counts.down(List.append(&2, String, he, [kk]), T.path.len(List.append(&2, String, he, [kk]), 0)) == True{}
  : Bool}:
  match he:
    case []:
      {==}
    case +s0 <> +ss:
      +xs = {List.append(&2, String, ss, [kk]) : List<&2, String>}
      +c0 = {Equal.trans(Bool, D1.counts(String.append(T.key(s0), wh.more(xs)), 0),
        D1.short(T.tree.pre(D1.tb.join(ss, T.key(s0)), kk)), True{},
        Equal.cong(String, Bool, x2 => D1.counts(x2, 0), String.append(T.key(s0), wh.more(xs)),
          T.tree.pre(D1.tb.join(ss, T.key(s0)), kk), Equal.sym(String, T.tree.pre(D1.tb.join(ss, T.key(s0)), kk),
          String.append(T.key(s0), wh.more(xs)), wh.join(ss, T.key(s0), kk, wh.key.ne(s0)))), ee)
        : {D1.counts(String.append(T.key(s0), wh.more(xs)), 0) == True{} : Bool}}
      cd.a2(s0 <> xs, T.path.len(s0 <> xs, 0), cd.a1(s0 <> xs, 0, M9.cv.and2(Bool.not(U32.is_zero(U32.add(0, 1))),
        cd.lc(xs, U32.add(0, 1)), {==}, cd.more(xs, 1, cd.k(T.key(s0), wh.more(xs), wh.key.ne(s0), c0)))))

# four texts appended left to right, then grouped to the right
def as4(
  +aa: String,
  +bb: String,
  +cc: String,
  +dd: String
) -> {String.append(String.append(String.append(aa, bb), cc),
  dd) == String.append(aa, String.append(bb, String.append(cc, dd))) : String}:
  Equal.trans(String, String.append(String.append(String.append(aa, bb), cc), dd),
    String.append(String.append(aa, bb), String.append(cc, dd)), String.append(aa, String.append(bb, String.append(cc,
    dd))), Eq.append_assoc(String.append(aa, bb), cc, dd), Eq.append_assoc(aa, bb, String.append(cc, dd)))

# the table pass's text for a table: its header, its rows as a table's, the
# later tables
def tt.head(
  +kk: String,
  +pp: String,
  +r: List<&2, T.Val>,
  +t: List<&2, T.Val>,
  +rest: String
) -> {String.append(T.render.pass(T.VPair{kk, T.VHead{pp, r}} <> t, "\n", True{}, True{}), rest) == SCon{'[',
  String.append(pp, SCon{']', SCon{'\n', String.append(T.render.pass(r, "\n", True{}, False{}),
  String.append(T.render.pass(r, "\n", True{}, True{}), String.append(T.render.pass(t, "\n", True{}, True{}),
  rest)))}})} : String}:
  +x1 = {T.render.pass(r, "\n", True{}, False{}) : String}
  +x2 = {T.render.pass(r, "\n", True{}, True{}) : String}
  +x3 = {T.render.pass(t, "\n", True{}, True{}) : String}
  Equal.cong(String, String, zz => SCon{'[', zz},
    String.append(String.append(pp, SCon{']', SCon{'\n', String.append(String.append(x1, x2), x3)}}), rest),
    String.append(pp, SCon{']', SCon{'\n', String.append(x1, String.append(x2, String.append(x3, rest)))}}),
    Equal.trans(String,
      String.append(String.append(pp, SCon{']', SCon{'\n', String.append(String.append(x1, x2), x3)}}), rest),
      String.append(pp, SCon{']', SCon{'\n', String.append(String.append(String.append(x1, x2), x3), rest)}}),
      String.append(pp, SCon{']', SCon{'\n', String.append(x1, String.append(x2, String.append(x3, rest)))}}),
      Eq.append_assoc(pp, SCon{']', SCon{'\n', String.append(String.append(x1, x2), x3)}}, rest),
      Equal.cong(String, String, zz => String.append(pp, SCon{']', SCon{'\n', zz}}),
        String.append(String.append(String.append(x1, x2), x3), rest),
        String.append(x1, String.append(x2, String.append(x3, rest))), as4(x1, x2, x3, rest))))

# and for an element of an array of tables
def tt.aot(
  +qq: String,
  +r: List<&2, T.Val>,
  +t: List<&2, T.Val>,
  +rest: String
) -> {String.append(T.render.pass(T.VAot{qq, r} <> t, "\n", True{}, True{}), rest) == SCon{'[', SCon{'[',
  String.append(qq, SCon{']', SCon{']', SCon{'\n', String.append(T.render.pass(r, "\n", True{}, False{}),
  String.append(T.render.pass(r, "\n", True{}, True{}), String.append(T.render.pass(t, "\n", True{}, True{}),
  rest)))}}})}} : String}:
  +x1 = {T.render.pass(r, "\n", True{}, False{}) : String}
  +x2 = {T.render.pass(r, "\n", True{}, True{}) : String}
  +x3 = {T.render.pass(t, "\n", True{}, True{}) : String}
  Equal.cong(String, String, zz => SCon{'[', SCon{'[', zz}},
    String.append(String.append(qq, SCon{']', SCon{']', SCon{'\n', String.append(String.append(x1, x2), x3)}}}), rest),
    String.append(qq, SCon{']', SCon{']', SCon{'\n', String.append(x1, String.append(x2, String.append(x3, rest)))}}}),
    Equal.trans(String,
      String.append(String.append(qq, SCon{']', SCon{']', SCon{'\n', String.append(String.append(x1, x2), x3)}}}),
        rest),
      String.append(qq, SCon{']', SCon{']', SCon{'\n', String.append(String.append(String.append(x1, x2), x3),
        rest)}}}),
      String.append(qq, SCon{']', SCon{']', SCon{'\n', String.append(x1, String.append(x2, String.append(x3,
        rest)))}}}),
      Eq.append_assoc(qq, SCon{']', SCon{']', SCon{'\n', String.append(String.append(x1, x2), x3)}}}, rest),
      Equal.cong(String, String, zz => String.append(qq, SCon{']', SCon{']', SCon{'\n', zz}}}),
        String.append(String.append(String.append(x1, x2), x3), rest),
        String.append(x1, String.append(x2, String.append(x3, rest))), as4(x1, x2, x3, rest))))

# the rest of the text after a header for kk: from the start of the next
# line, in the table the pair holds, its value vx put in front of cs
def hdr.Then(
  +vx: T.Val,
  +kk: String,
  +he: List<&2, String>,
  +r0: List<&2, T.Val>,
  +cs: List<&2, T.Val>,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  @hs2: List<&2, String> -> @b2: T.Lex -> @q2: T.QKind -> @u2: U32 -> @l2: U32 ->
    PP(T.doc.read(rest, T.MScan{M3.dl(D1.tb.set(he, "", r0, T.VPair{kk, vx} <> cs), hs2,
      List.append(&2, String, he, [kk]), b2, q2, u2, l2, False{})}))

# a [table] header for a name the current table's parent does not hold, read
# from the start of any line: the rest is read from the start of the next
# line in the new, empty table
def hdr.tab(
  +kk: String,
  +pp: String,
  +he: List<&2, String>,
  +r0: List<&2, T.Val>,
  +cs: List<&2, T.Val>,
  +hs: List<&2, String>,
  +cur: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  +eo: {D1.tb.open(he, r0) == True{} : Bool},
  +em: {L3.is_miss(T.get(cs, kk)) == True{} : Bool},
  +ep: {T.tree.pre(D1.tb.join(he, ""), kk) == pp : String},
  ih: hdr.Then(T.VHead{pp, []}, kk, he, r0, cs, rest, PP)
) -> PP(T.doc.read(SCon{'[', String.append(pp, SCon{']', SCon{'\n', rest}})}, T.MScan{M3.dl(D1.tb.set(he, "", r0, cs),
  hs,
  cur, bk, qk, un, lf, ab)})):
  +rr = {D1.tb.set(he, "", r0, cs) : List<&2, T.Val>}
  +p0 = {T.tree.pre(D1.tb.join(he, ""), kk) : String}
  +erw = {L9.tb_rows_after_set(he, "", r0, cs, eo) : {D1.tb.rows(he, rr) == cs : List<&2, T.Val>}}
  +r2 = {D1.tb.set(he, "", rr, T.VPair{kk, T.VHead{p0, []}} <> D1.tb.rows(he, rr)) : List<&2, T.Val>}
  +h2 = {T.heads.by.head(p0) <> hs : List<&2, String>}
  %ep : PP(T.doc.read(SCon{'[', String.append(_, SCon{']', SCon{'\n', rest}})}, T.MScan{M3.dl(rr, hs, cur, bk, qk, un,
      lf,
    ab)}))
  hm.law(False{}, he, kk, rr, hs, cur, bk, qk, un, lf, ab, r2, h2, rest, PP,
    L5.header_defines_new_table(he, kk, rr, hs, L8.tb_open_after_set(he, "", r0, cs, eo),
      Equal.trans(T.Hit, T.get(D1.tb.rows(he, rr), kk), T.get(cs, kk), T.Miss{},
        Equal.cong(List<&2, T.Val>, T.Hit, zs => T.get(zs, kk), D1.tb.rows(he, rr), cs, erw), M13.cv.miss(T.get(cs, kk),
          em))),
    +b2 => +q2 => +u2 => +l2 => M13.pp.step(PP,
      T.doc.read(rest, T.MScan{M3.dl(r2, h2, List.append(&2, String, he, [kk]), b2, q2, u2, l2, False{})}),
      T.doc.read(rest, T.MScan{M3.dl(D1.tb.set(he, "", r0, T.VPair{kk, T.VHead{pp, []}} <> cs), h2,
        List.append(&2, String, he, [kk]), b2, q2, u2, l2, False{})}),
      Equal.cong(List<&2, T.Val>, T.Doc, zs => T.doc.read(rest, T.MScan{M3.dl(zs, h2, List.append(&2, String, he, [kk]),
        b2, q2, u2,
        l2, False{})}), r2, D1.tb.set(he, "", r0, T.VPair{kk, T.VHead{pp, []}} <> cs),
        Equal.trans(List<&2, T.Val>, r2, D1.tb.set(he, "", rr, T.VPair{kk, T.VHead{p0, []}} <> cs),
          D1.tb.set(he, "", r0, T.VPair{kk, T.VHead{pp, []}} <> cs),
          Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => D1.tb.set(he, "", rr, T.VPair{kk, T.VHead{p0,
            []}} <> zs), D1.tb.rows(he, rr),
            cs, erw),
          Equal.trans(List<&2, T.Val>, D1.tb.set(he, "", rr, T.VPair{kk, T.VHead{p0, []}} <> cs),
            D1.tb.set(he, "", r0, T.VPair{kk, T.VHead{p0, []}} <> cs),
            D1.tb.set(he, "", r0, T.VPair{kk, T.VHead{pp, []}} <> cs),
            M13.wa.ss(he, "", r0, cs, T.VPair{kk, T.VHead{p0, []}} <> cs, eo),
            Equal.cong(String, List<&2, T.Val>, zz => D1.tb.set(he, "", r0, T.VPair{kk, T.VHead{zz, []}} <> cs), p0,
              pp, ep)))),
      ih(h2, b2, q2, u2, l2)))

# an [[array]] header for a name the current table's parent does not hold:
# the rest is read in the array's first, empty element
def hdr.aot0(
  +kk: String,
  +pp: String,
  +he: List<&2, String>,
  +r0: List<&2, T.Val>,
  +cs: List<&2, T.Val>,
  +hs: List<&2, String>,
  +cur: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  +eo: {D1.tb.open(he, r0) == True{} : Bool},
  +em: {L3.is_miss(T.get(cs, kk)) == True{} : Bool},
  +ep: {T.tree.pre(D1.tb.join(he, ""), kk) == pp : String},
  ih: hdr.Then(T.VAots{pp, [T.VAot{pp, []}]}, kk, he, r0, cs, rest, PP)
) -> PP(T.doc.read(SCon{'[', SCon{'[', String.append(pp, SCon{']', SCon{']', SCon{'\n', rest}}})}},
  T.MScan{M3.dl(D1.tb.set(he,
  "", r0, cs), hs, cur, bk, qk, un, lf, ab)})):
  +rr = {D1.tb.set(he, "", r0, cs) : List<&2, T.Val>}
  +p0 = {T.tree.pre(D1.tb.join(he, ""), kk) : String}
  +erw = {L9.tb_rows_after_set(he, "", r0, cs, eo) : {D1.tb.rows(he, rr) == cs : List<&2, T.Val>}}
  +r2 = {D1.tb.set(he, "", rr, T.VPair{kk, T.VAots{p0, [T.VAot{p0, []}]}} <> D1.tb.rows(he, rr)) : List<&2, T.Val>}
  %ep : PP(T.doc.read(SCon{'[', SCon{'[', String.append(_, SCon{']', SCon{']', SCon{'\n', rest}}})}}, T.MScan{M3.dl(rr,
      hs,
    cur, bk,
    qk, un, lf, ab)}))
  hm.law(True{}, he, kk, rr, hs, cur, bk, qk, un, lf, ab, r2, hs, rest, PP,
    L2.aot_header_starts_array(he, kk, rr, hs, L8.tb_open_after_set(he, "", r0, cs, eo),
      Equal.trans(T.Hit, T.get(D1.tb.rows(he, rr), kk), T.get(cs, kk), T.Miss{},
        Equal.cong(List<&2, T.Val>, T.Hit, zs => T.get(zs, kk), D1.tb.rows(he, rr), cs, erw), M13.cv.miss(T.get(cs, kk),
          em))),
    +b2 => +q2 => +u2 => +l2 => M13.pp.step(PP,
      T.doc.read(rest, T.MScan{M3.dl(r2, hs, List.append(&2, String, he, [kk]), b2, q2, u2, l2, False{})}),
      T.doc.read(rest, T.MScan{M3.dl(D1.tb.set(he, "", r0, T.VPair{kk, T.VAots{pp, [T.VAot{pp, []}]}} <> cs), hs,
        List.append(&2, String, he, [kk]), b2, q2, u2, l2, False{})}),
      Equal.cong(List<&2, T.Val>, T.Doc, zs => T.doc.read(rest, T.MScan{M3.dl(zs, hs, List.append(&2, String, he, [kk]),
        b2, q2, u2,
        l2, False{})}), r2, D1.tb.set(he, "", r0, T.VPair{kk, T.VAots{pp, [T.VAot{pp, []}]}} <> cs),
        Equal.trans(List<&2, T.Val>, r2, D1.tb.set(he, "", rr, T.VPair{kk, T.VAots{p0, [T.VAot{p0, []}]}} <> cs),
          D1.tb.set(he, "", r0, T.VPair{kk, T.VAots{pp, [T.VAot{pp, []}]}} <> cs),
          Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => D1.tb.set(he, "", rr, T.VPair{kk, T.VAots{p0, [T.VAot{p0,
            []}]}} <> zs),
            D1.tb.rows(he, rr), cs, erw),
          Equal.trans(List<&2, T.Val>, D1.tb.set(he, "", rr, T.VPair{kk, T.VAots{p0, [T.VAot{p0, []}]}} <> cs),
            D1.tb.set(he, "", r0, T.VPair{kk, T.VAots{p0, [T.VAot{p0, []}]}} <> cs),
            D1.tb.set(he, "", r0, T.VPair{kk, T.VAots{pp, [T.VAot{pp, []}]}} <> cs),
            M13.wa.ss(he, "", r0, cs, T.VPair{kk, T.VAots{p0, [T.VAot{p0, []}]}} <> cs, eo),
            Equal.cong(String, List<&2, T.Val>, zz => D1.tb.set(he, "", r0, T.VPair{kk, T.VAots{zz, [T.VAot{zz,
              []}]}} <> cs), p0,
              pp, ep)))),
      ih(hs, b2, q2, u2, l2)))

# an [[array]] header for the array of tables at the head of the current
# table's parent: the rest is read in a new, empty element in front
def hdr.aot1(
  +kk: String,
  +pp: String,
  +ee: List<&2, T.Val>,
  +he: List<&2, String>,
  +r0: List<&2, T.Val>,
  +cs: List<&2, T.Val>,
  +hs: List<&2, String>,
  +cur: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  +eo: {D1.tb.open(he, r0) == True{} : Bool},
  +em: {L3.is_miss(T.get(cs, kk)) == True{} : Bool},
  +ep: {T.tree.pre(D1.tb.join(he, ""), kk) == pp : String},
  ih: hdr.Then(T.VAots{pp, T.VAot{pp, []} <> ee}, kk, he, r0, cs, rest, PP)
) -> PP(T.doc.read(SCon{'[', SCon{'[', String.append(pp, SCon{']', SCon{']', SCon{'\n', rest}}})}},
  T.MScan{M3.dl(D1.tb.set(he,
  "", r0, T.VPair{kk, T.VAots{pp, ee}} <> cs), hs, cur, bk, qk, un, lf, ab)})):
  +c1 = {T.VPair{kk, T.VAots{pp, ee}} <> cs : List<&2, T.Val>}
  +rr = {D1.tb.set(he, "", r0, c1) : List<&2, T.Val>}
  +p0 = {T.tree.pre(D1.tb.join(he, ""), kk) : String}
  +erw = {L9.tb_rows_after_set(he, "", r0, c1, eo) : {D1.tb.rows(he, rr) == c1 : List<&2, T.Val>}}
  +r2 = {D1.tb.set(he, "", rr, T.rows.repl(D1.tb.rows(he, rr), kk, T.VAots{p0, T.VAot{p0,
    []} <> ee})) : List<&2, T.Val>}
  +h2 = {T.heads.drop(hs, String.append(p0, ".")) : List<&2, String>}
  %ep : PP(T.doc.read(SCon{'[', SCon{'[', String.append(_, SCon{']', SCon{']', SCon{'\n', rest}}})}}, T.MScan{M3.dl(rr,
      hs,
    cur, bk,
    qk, un, lf, ab)}))
  hm.law(True{}, he, kk, rr, hs, cur, bk, qk, un, lf, ab, r2, h2, rest, PP,
    L1.aot_header_extends_array(he, kk, rr, hs, pp, ee, L8.tb_open_after_set(he, "", r0, c1, eo),
      Equal.trans(T.Hit, T.get(D1.tb.rows(he, rr), kk), T.get(c1, kk), T.Found{T.VAots{pp, ee}},
        Equal.cong(List<&2, T.Val>, T.Hit, zs => T.get(zs, kk), D1.tb.rows(he, rr), c1, erw),
        L4.get_first(kk, T.VAots{pp, ee}, cs))),
    +b2 => +q2 => +u2 => +l2 => M13.pp.step(PP,
      T.doc.read(rest, T.MScan{M3.dl(r2, h2, List.append(&2, String, he, [kk]), b2, q2, u2, l2, False{})}),
      T.doc.read(rest, T.MScan{M3.dl(D1.tb.set(he, "", r0, T.VPair{kk, T.VAots{pp, T.VAot{pp, []} <> ee}} <> cs), h2,
        List.append(&2, String, he, [kk]), b2, q2, u2, l2, False{})}),
      Equal.cong(List<&2, T.Val>, T.Doc, zs => T.doc.read(rest, T.MScan{M3.dl(zs, h2, List.append(&2, String, he, [kk]),
        b2, q2, u2,
        l2, False{})}), r2, D1.tb.set(he, "", r0, T.VPair{kk, T.VAots{pp, T.VAot{pp, []} <> ee}} <> cs),
        Equal.trans(List<&2, T.Val>, r2, D1.tb.set(he, "", rr, T.VPair{kk, T.VAots{p0, T.VAot{p0, []} <> ee}} <> cs),
          D1.tb.set(he, "", r0, T.VPair{kk, T.VAots{pp, T.VAot{pp, []} <> ee}} <> cs),
          Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => D1.tb.set(he, "", rr, zs), T.rows.repl(D1.tb.rows(he,
            rr), kk, T.VAots{p0,
            T.VAot{p0, []} <> ee}), T.VPair{kk, T.VAots{p0, T.VAot{p0, []} <> ee}} <> cs,
            Equal.trans(List<&2, T.Val>, T.rows.repl(D1.tb.rows(he, rr), kk, T.VAots{p0, T.VAot{p0, []} <> ee}),
              T.rows.repl(c1, kk, T.VAots{p0, T.VAot{p0, []} <> ee}), T.VPair{kk, T.VAots{p0, T.VAot{p0,
                []} <> ee}} <> cs,
              Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => T.rows.repl(zs, kk, T.VAots{p0, T.VAot{p0, []} <> ee}),
                D1.tb.rows(he, rr), c1,
                erw),
              M13.wa.repl.hd(kk, T.VAots{pp, ee}, cs, T.VAots{p0, T.VAot{p0, []} <> ee}, em))),
          Equal.trans(List<&2, T.Val>, D1.tb.set(he, "", rr, T.VPair{kk, T.VAots{p0, T.VAot{p0, []} <> ee}} <> cs),
            D1.tb.set(he, "", r0, T.VPair{kk, T.VAots{p0, T.VAot{p0, []} <> ee}} <> cs),
            D1.tb.set(he, "", r0, T.VPair{kk, T.VAots{pp, T.VAot{pp, []} <> ee}} <> cs),
            M13.wa.ss(he, "", r0, c1, T.VPair{kk, T.VAots{p0, T.VAot{p0, []} <> ee}} <> cs, eo),
            Equal.cong(String, List<&2, T.Val>, zz => D1.tb.set(he, "", r0, T.VPair{kk, T.VAots{zz, T.VAot{zz,
              []} <> ee}} <> cs), p0,
              pp, ep)))),
      ih(h2, b2, q2, u2, l2)))

# and once it has read an array of tables' elements: the array, at the head
# of the current table's rows, holds what own reads, sealed, as mm
def tp.ThenE(
  +r0: List<&2, T.Val>,
  +he: List<&2, String>,
  +cs: List<&2, T.Val>,
  +nn: String,
  +pp: String,
  +mm: List<&2, T.Val>,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  @e2: List<&2, T.Val> -> @hs2: List<&2, String> -> @he2: List<&2, String> -> @b2: T.Lex -> @q2: T.QKind -> @u2: U32 ->
    @l2: U32 -> @a2: Bool ->
    {D1.own.rows(T.rows.seal(e2)) == D1.own.rows(mm) : List<&2, T.Val>} ->
    PP(T.doc.read(rest, T.MScan{M3.dl(D1.tb.set(he, "", r0, T.VPair{nn, T.VAots{pp, e2}} <> cs), hs2, he2, b2, q2, u2,
      l2, a2)}))

# what the table pass claims of a list: a table's rows (md false), read
# from the start of a line after its key pass, their tables put in order; or
# the later elements of an array of tables (md true), named nn in the table
# at he and stored under hp, holding ee so far
def tp.G(
  md: Bool,
  +ys: List<&2, T.Val>,
  +hp: String,
  +r0: List<&2, T.Val>,
  +he: List<&2, String>,
  +cs: List<&2, T.Val>,
  +mm: List<&2, T.Val>,
  +nn: String,
  +ee: List<&2, T.Val>,
  +hs: List<&2, String>,
  +cur: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type
) -> Type:
  match md:
    case False{}:
      {D1.tb.join(he, "") == hp : String} -> {T.wf.go(ys, T.WfRows{hp}) == True{} : Bool} ->
        {D4.short.rows(ys) == True{} : Bool} -> {M5.cv.fr(cs, D2.canon.tabs(ys)) == True{} : Bool} ->
        {M5.nd(D2.canon.tabs(ys)) == True{} : Bool} ->
          {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>} ->
        M13.tp.Then(r0, he, List.append(&2, T.Val, mm, D2.canon.tabs(ys)), rest, PP) ->
        PP(T.doc.read(String.append(T.render.pass(ys, "\n", True{}, True{}), rest), T.MScan{M3.dl(D1.tb.set(he, "", r0,
          cs), hs, cur, bk, qk, un, lf, ab)}))
    case True{}:
      {T.tree.pre(D1.tb.join(he, ""), nn) == hp : String} -> {L3.is_miss(T.get(cs, nn)) == True{} : Bool} ->
        {D1.short(hp) == True{} : Bool} -> {T.wf.go(ys, T.WfElems{hp}) == True{} : Bool} ->
        {D4.short.rows(ys) == True{} : Bool} ->
          {D1.own.rows(T.rows.seal(ee)) == D1.own.rows(mm) : List<&2, T.Val>} ->
        tp.ThenE(r0, he, cs, nn, hp, List.append(&2, T.Val, mm, D2.canon.go(ys, D2.CElems{hp})), rest, PP) ->
        PP(T.doc.read(String.append(T.render.pass(ys, "\n", True{}, True{}), rest), T.MScan{M3.dl(D1.tb.set(he, "", r0,
          T.VPair{nn, T.VAots{hp, ee}} <> cs), hs, cur, bk, qk, un, lf, ab)}))

# the table pass: each table's header, then its rows as a table's, and each
# array of tables' elements, each a header then its rows
def tp(
  ys: List<&2, T.Val>,
  md: Bool,
  +hp: String,
  +r0: List<&2, T.Val>,
  +he: List<&2, String>,
  +cs: List<&2, T.Val>,
  +mm: List<&2, T.Val>,
  +nn: String,
  +ee: List<&2, T.Val>,
  +hs: List<&2, String>,
  +cur: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  -PP: T.Doc -> Type,
  +eo: {D1.tb.open(he, r0) == True{} : Bool}
) -> tp.G(md, ys, hp, r0, he, cs, mm, nn, ee, hs, cur, bk, qk, un, lf, ab, rest, PP):
  match ys md:
    case [] False{}:
      _ej => _hw => _hl => _hf => _hn => ho => ih => ih(cs, hs, cur, bk, qk, un, lf, ab, Equal.trans(List<&2, T.Val>,
        D1.own.rows(T.rows.seal(cs)),
        D1.own.rows(mm), D1.own.rows(List.append(&2, T.Val, mm, [])), ho, Equal.cong(List<&2, T.Val>,
          List<&2, T.Val>, zs => D1.own.rows(zs), mm, List.append(&2, T.Val, mm, []),
        Equal.sym(List<&2, T.Val>, List.append(&2, T.Val, mm, []), mm, M13.va.nil(mm)))))
    case [] True{}:
      _ep => _em => _sh => _hw => _hl => ho => ih => ih(ee, hs, cur, bk, qk, un, lf, ab, Equal.trans(List<&2, T.Val>,
        D1.own.rows(T.rows.seal(ee)),
        D1.own.rows(mm), D1.own.rows(List.append(&2, T.Val, mm, [])), ho, Equal.cong(List<&2, T.Val>,
          List<&2, T.Val>, zs => D1.own.rows(zs), mm, List.append(&2, T.Val, mm, []),
        Equal.sym(List<&2, T.Val>, List.append(&2, T.Val, mm, []), mm, M13.va.nil(mm)))))
    case T.VPair{+kk, T.VHead{+p, +r}} <> +t False{}:
      +ej => +hw => +hl => +hf => +hn => +ho => ih =>
        +ha = {M9.wt.ok(Bool.and(T.wf.key(kk, t), T.str.eq(p, T.tree.pre(hp, kk))), _u => T.wf.then(T.wf.go(r,
          T.WfRows{p}), _v => T.wf.go(t, T.WfRows{hp})), hw) : {Bool.and(T.wf.key(kk, t), T.str.eq(p, T.tree.pre(hp,
          kk))) == True{} : Bool}}
        +hin = {M9.wt.more(Bool.and(T.wf.key(kk, t), T.str.eq(p, T.tree.pre(hp, kk))), _u => T.wf.then(T.wf.go(r,
          T.WfRows{p}), _v => T.wf.go(t, T.WfRows{hp})), hw) : {T.wf.then(T.wf.go(r, T.WfRows{p}), _v => T.wf.go(t,
          T.WfRows{hp})) == True{} : Bool}}
        +hwr = {M9.wt.ok(T.wf.go(r, T.WfRows{p}), _v => T.wf.go(t, T.WfRows{hp}), hin) : {T.wf.go(r, T.WfRows{p})
          == True{} : Bool}}
        +hwt = {M9.wt.more(T.wf.go(r, T.WfRows{p}), _v => T.wf.go(t, T.WfRows{hp}), hin) : {T.wf.go(t, T.WfRows{hp})
          == True{} : Bool}}
        +ep = {Equal.trans(String, T.tree.pre(D1.tb.join(he, ""), kk), T.tree.pre(hp, kk), p,
          Equal.cong(String, String, zz => T.tree.pre(zz, kk), D1.tb.join(he, ""), hp, ej),
          Equal.sym(String, p, T.tree.pre(hp, kk), M4.str.eq.true(p, T.tree.pre(hp, kk), Eq.and.right(T.wf.key(kk, t),
          T.str.eq(p, T.tree.pre(hp, kk)), ha)))) : {T.tree.pre(D1.tb.join(he, ""), kk) == p : String}}
        +shp = {Eq.and.left(D1.short(p), Bool.and(D4.short.rows(r), D4.short.rows(t)), hl) : {D1.short(p)
          == True{} : Bool}}
        +hl2 = {Eq.and.right(D1.short(p), Bool.and(D4.short.rows(r), D4.short.rows(t)), hl)
          : {Bool.and(D4.short.rows(r), D4.short.rows(t)) == True{} : Bool}}
        +em = {Eq.and.left(L3.is_miss(T.get(cs, kk)), M5.cv.fr(cs, D2.canon.tabs(t)), hf) : {L3.is_miss(T.get(cs,
          kk)) == True{} : Bool}}
        +x0 = {T.VPair{kk, T.VHead{p, D2.canon.rows(r)}} : T.Val}
        +zz = {String.append(T.render.pass(t, "\n", True{}, True{}), rest) : String}
        M13.pp.step(PP, T.doc.read(String.append(T.render.pass(T.VPair{kk, T.VHead{p, r}} <> t, "\n", True{}, True{}),
          rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un, lf, ab)}),
          T.doc.read(SCon{'[', String.append(p, SCon{']', SCon{'\n', String.append(T.render.pass(r, "\n", True{},
            False{}), String.append(T.render.pass(r, "\n", True{}, True{}), zz))}})},
            T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un, lf, ab)}),
          Equal.cong(String, T.Doc, ss => T.doc.read(ss, T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un,
            lf, ab)}),
            String.append(T.render.pass(T.VPair{kk, T.VHead{p, r}} <> t, "\n", True{}, True{}), rest), SCon{'[',
              String.append(p, SCon{']', SCon{'\n',
            String.append(T.render.pass(r, "\n", True{}, False{}), String.append(T.render.pass(r, "\n", True{}, True{}),
              zz))}})}, tt.head(kk, p, r, t, rest)),
          hdr.tab(kk, p, he, r0, cs, hs, cur, bk, qk, un, lf, ab, String.append(T.render.pass(r, "\n", True{}, False{}),
            String.append(T.render.pass(r, "\n", True{}, True{}), zz)), PP, eo, em, ep,
            +hs2 => +b2 => +q2 => +u2 => +l2 => M13.body(kk, T.VHead{p, []}, r, p, he, r0, cs, hs2, b2, q2, u2, l2,
                False{},
              zz,
              PP, eo, em, {==}, cd(he, kk, Equal.trans(Bool, D1.short(T.tree.pre(D1.tb.join(he, ""), kk)),
                D1.short(p),
              True{}, Equal.cong(String, Bool, s2 => D1.short(s2), T.tree.pre(D1.tb.join(he, ""), kk), p, ep),
                shp)),
              hwr, Eq.and.left(D4.short.rows(r), D4.short.rows(t), hl2),
              +c2 => +b3 => +q3 => +u3 => +l3 => f2 => n2 => o2 => i2 => tp(r, False{}, p, D1.tb.set(he, "", r0,
                T.VPair{kk, T.VHead{p, []}} <> cs), List.append(&2, String, he, [kk]), c2, D2.canon.keys(r), nn, ee,
                  hs2, List.append(&2, String, he, [kk]), b3, q3, u3, l3,
                False{}, zz, PP, M13.wa.eopen(he, r0, kk, T.VHead{p, []}, cs, eo, {==}))(Equal.trans(String,
                D1.tb.join(List.append(&2, String, he, [kk]), ""), T.tree.pre(D1.tb.join(he, ""), kk), p, wa.ja(he,
                  "", kk), ep), hwr,
                Eq.and.left(D4.short.rows(r), D4.short.rows(t), hl2), f2, n2, o2, i2),
              +c3 => +hs3 => +he3 => +b4 => +q4 => +u4 => +l4 => +a4 => o3 => tp(t, False{}, hp, r0, he,
                T.VPair{kk, T.VHead{p, c3}} <> cs, List.append(&2, T.Val, mm, [x0]), nn, ee, hs3, he3, b4, q4, u4, l4,
                  a4, rest,
                PP, eo)(ej, hwt, Eq.and.right(D4.short.rows(r), D4.short.rows(t), hl2),
                M13.cv.fr.step(D2.canon.tabs(t), kk, T.VHead{p, c3}, cs, Eq.and.right(L3.is_miss(T.get(cs, kk)),
                  M5.cv.fr(cs, D2.canon.tabs(t)), hf), Eq.and.left(T.wf.fresh(T.get(D2.canon.tabs(t), kk)),
                  M5.nd(D2.canon.tabs(t)), hn)),
                Eq.and.right(T.wf.fresh(T.get(D2.canon.tabs(t), kk)), M5.nd(D2.canon.tabs(t)), hn),
                M13.os.step(T.VPair{kk, T.VHead{p, c3}}, cs, mm, x0, ho, Equal.cong(List<&2, T.Val>, List<&2, T.Val>,
                  zs => [T.VPair{kk, T.VHead{p, zs}}], D1.own.rows(T.rows.seal(c3)),
                    D1.own.rows(D2.canon.rows(r)), o3)),
                +c5 => +hs5 => +he5 => +b5 => +q5 => +u5 => +l5 => +a5 => o5 => ih(c5, hs5, he5, b5, q5, u5, l5, a5,
                  Equal.trans(List<&2, T.Val>, D1.own.rows(T.rows.seal(c5)), D1.own.rows(List.append(&2, T.Val,
                    List.append(&2, T.Val, mm, [x0]), D2.canon.tabs(t))),
                    D1.own.rows(List.append(&2, T.Val, mm, x0 <> D2.canon.tabs(t))), o5,
                    Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => D1.own.rows(zs), List.append(&2, T.Val,
                      List.append(&2, T.Val, mm, [x0]), D2.canon.tabs(t)),
                      List.append(&2, T.Val, mm, x0 <> D2.canon.tabs(t)), M5.va.assoc(mm, [x0],
                        D2.canon.tabs(t)))))))))
    case T.VPair{+kk, T.VAots{+p, []}} <> +t False{}:
      _ej => hw => Eq.bit.absurd(&1, {D4.short.rows(T.VPair{kk, T.VAots{p, []}} <> t) == True{} : Bool} -> {M5.cv.fr(cs,
        D2.canon.tabs(T.VPair{kk, T.VAots{p, []}} <> t)) == True{} : Bool} -> {M5.nd(D2.canon.tabs(T.VPair{kk,
        T.VAots{p,
        []}} <> t)) == True{} : Bool} -> {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>} ->
        M13.tp.Then(r0, he, List.append(&2, T.Val, mm, D2.canon.tabs(T.VPair{kk, T.VAots{p, []}} <> t)), rest,
        PP) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{kk, T.VAots{p, []}} <> t, "\n", True{}, True{}), rest),
        T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un, lf, ab)})), hw)
    case T.VPair{+kk, T.VAots{+p, T.VStr{+a1} <> +et}} <> +t False{}:
      _ej => hw =>
        +hin = {M9.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VStr{a1} <> et)), Bool.and(T.wf.key(kk, t),
          T.str.eq(p,
          T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VStr{a1} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp})), hw)
          : {T.wf.then(T.wf.go(T.VStr{a1} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp})) == True{} : Bool}}
        Eq.bit.absurd(&1, {D4.short.rows(T.VPair{kk, T.VAots{p,
          T.VStr{a1} <> et}} <> t) == True{} : Bool} -> {M5.cv.fr(cs, D2.canon.tabs(T.VPair{kk, T.VAots{p,
          T.VStr{a1} <> et}} <> t)) == True{} : Bool} -> {M5.nd(D2.canon.tabs(T.VPair{kk, T.VAots{p,
          T.VStr{a1} <> et}} <> t)) == True{} : Bool} ->
          {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>} -> M13.tp.Then(r0, he, List.append(&2,
          T.Val, mm, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VStr{a1} <> et}} <> t)), rest,
          PP) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VStr{a1} <> et}} <> t, "\n", True{},
          True{}), rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un, lf, ab)})),
          M9.wt.ok(T.wf.go(T.VStr{a1} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VSpan{+a1, +a2} <> +et}} <> +t False{}:
      _ej => hw =>
        +hin = {M9.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VSpan{a1, a2} <> et)), Bool.and(T.wf.key(kk, t),
          T.str.eq(p,
          T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VSpan{a1, a2} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp})), hw)
          : {T.wf.then(T.wf.go(T.VSpan{a1, a2} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp})) == True{} : Bool}}
        Eq.bit.absurd(&1, {D4.short.rows(T.VPair{kk, T.VAots{p, T.VSpan{a1,
          a2} <> et}} <> t) == True{} : Bool} -> {M5.cv.fr(cs, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VSpan{a1,
          a2} <> et}} <> t)) == True{} : Bool} -> {M5.nd(D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VSpan{a1,
          a2} <> et}} <> t)) == True{} : Bool} ->
          {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>} -> M13.tp.Then(r0, he, List.append(&2,
          T.Val, mm, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VSpan{a1, a2} <> et}} <> t)), rest,
          PP) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VSpan{a1, a2} <> et}} <> t, "\n",
          True{}, True{}), rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un, lf, ab)})),
          M9.wt.ok(T.wf.go(T.VSpan{a1, a2} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VInt{+a1, +a2} <> +et}} <> +t False{}:
      _ej => hw =>
        +hin = {M9.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VInt{a1, a2} <> et)), Bool.and(T.wf.key(kk, t),
          T.str.eq(p,
          T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VInt{a1, a2} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp})), hw)
          : {T.wf.then(T.wf.go(T.VInt{a1, a2} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp})) == True{} : Bool}}
        Eq.bit.absurd(&1, {D4.short.rows(T.VPair{kk, T.VAots{p, T.VInt{a1,
          a2} <> et}} <> t) == True{} : Bool} -> {M5.cv.fr(cs, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VInt{a1,
          a2} <> et}} <> t)) == True{} : Bool} -> {M5.nd(D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VInt{a1,
          a2} <> et}} <> t)) == True{} : Bool} ->
          {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>} -> M13.tp.Then(r0, he, List.append(&2,
          T.Val, mm, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VInt{a1, a2} <> et}} <> t)), rest,
          PP) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VInt{a1, a2} <> et}} <> t, "\n",
          True{}, True{}), rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un, lf, ab)})),
          M9.wt.ok(T.wf.go(T.VInt{a1, a2} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VFlo{+a1, +a2} <> +et}} <> +t False{}:
      _ej => hw =>
        +hin = {M9.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VFlo{a1, a2} <> et)), Bool.and(T.wf.key(kk, t),
          T.str.eq(p,
          T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VFlo{a1, a2} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp})), hw)
          : {T.wf.then(T.wf.go(T.VFlo{a1, a2} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp})) == True{} : Bool}}
        Eq.bit.absurd(&1, {D4.short.rows(T.VPair{kk, T.VAots{p, T.VFlo{a1,
          a2} <> et}} <> t) == True{} : Bool} -> {M5.cv.fr(cs, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VFlo{a1,
          a2} <> et}} <> t)) == True{} : Bool} -> {M5.nd(D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VFlo{a1,
          a2} <> et}} <> t)) == True{} : Bool} ->
          {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>} -> M13.tp.Then(r0, he, List.append(&2,
          T.Val, mm, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VFlo{a1, a2} <> et}} <> t)), rest,
          PP) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VFlo{a1, a2} <> et}} <> t, "\n",
          True{}, True{}), rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un, lf, ab)})),
          M9.wt.ok(T.wf.go(T.VFlo{a1, a2} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VBool{+a1} <> +et}} <> +t False{}:
      _ej => hw =>
        +hin = {M9.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VBool{a1} <> et)), Bool.and(T.wf.key(kk, t),
          T.str.eq(p,
          T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VBool{a1} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp})), hw)
          : {T.wf.then(T.wf.go(T.VBool{a1} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp})) == True{} : Bool}}
        Eq.bit.absurd(&1, {D4.short.rows(T.VPair{kk, T.VAots{p,
          T.VBool{a1} <> et}} <> t) == True{} : Bool} -> {M5.cv.fr(cs, D2.canon.tabs(T.VPair{kk, T.VAots{p,
          T.VBool{a1} <> et}} <> t)) == True{} : Bool} -> {M5.nd(D2.canon.tabs(T.VPair{kk, T.VAots{p,
          T.VBool{a1} <> et}} <> t)) == True{} : Bool} ->
          {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>} -> M13.tp.Then(r0, he, List.append(&2,
          T.Val, mm, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VBool{a1} <> et}} <> t)), rest,
          PP) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VBool{a1} <> et}} <> t, "\n",
          True{}, True{}), rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un, lf, ab)})),
          M9.wt.ok(T.wf.go(T.VBool{a1} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VWhen{+a1} <> +et}} <> +t False{}:
      _ej => hw =>
        +hin = {M9.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VWhen{a1} <> et)), Bool.and(T.wf.key(kk, t),
          T.str.eq(p,
          T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VWhen{a1} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp})), hw)
          : {T.wf.then(T.wf.go(T.VWhen{a1} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp})) == True{} : Bool}}
        Eq.bit.absurd(&1, {D4.short.rows(T.VPair{kk, T.VAots{p,
          T.VWhen{a1} <> et}} <> t) == True{} : Bool} -> {M5.cv.fr(cs, D2.canon.tabs(T.VPair{kk, T.VAots{p,
          T.VWhen{a1} <> et}} <> t)) == True{} : Bool} -> {M5.nd(D2.canon.tabs(T.VPair{kk, T.VAots{p,
          T.VWhen{a1} <> et}} <> t)) == True{} : Bool} ->
          {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>} -> M13.tp.Then(r0, he, List.append(&2,
          T.Val, mm, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VWhen{a1} <> et}} <> t)), rest,
          PP) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VWhen{a1} <> et}} <> t, "\n",
          True{}, True{}), rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un, lf, ab)})),
          M9.wt.ok(T.wf.go(T.VWhen{a1} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VArr{+a1} <> +et}} <> +t False{}:
      _ej => hw =>
        +hin = {M9.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VArr{a1} <> et)), Bool.and(T.wf.key(kk, t),
          T.str.eq(p,
          T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VArr{a1} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp})), hw)
          : {T.wf.then(T.wf.go(T.VArr{a1} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp})) == True{} : Bool}}
        Eq.bit.absurd(&1, {D4.short.rows(T.VPair{kk, T.VAots{p,
          T.VArr{a1} <> et}} <> t) == True{} : Bool} -> {M5.cv.fr(cs, D2.canon.tabs(T.VPair{kk, T.VAots{p,
          T.VArr{a1} <> et}} <> t)) == True{} : Bool} -> {M5.nd(D2.canon.tabs(T.VPair{kk, T.VAots{p,
          T.VArr{a1} <> et}} <> t)) == True{} : Bool} ->
          {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>} -> M13.tp.Then(r0, he, List.append(&2,
          T.Val, mm, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VArr{a1} <> et}} <> t)), rest,
          PP) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VArr{a1} <> et}} <> t, "\n", True{},
          True{}), rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un, lf, ab)})),
          M9.wt.ok(T.wf.go(T.VArr{a1} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VInl{+a1} <> +et}} <> +t False{}:
      _ej => hw =>
        +hin = {M9.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VInl{a1} <> et)), Bool.and(T.wf.key(kk, t),
          T.str.eq(p,
          T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VInl{a1} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp})), hw)
          : {T.wf.then(T.wf.go(T.VInl{a1} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp})) == True{} : Bool}}
        Eq.bit.absurd(&1, {D4.short.rows(T.VPair{kk, T.VAots{p,
          T.VInl{a1} <> et}} <> t) == True{} : Bool} -> {M5.cv.fr(cs, D2.canon.tabs(T.VPair{kk, T.VAots{p,
          T.VInl{a1} <> et}} <> t)) == True{} : Bool} -> {M5.nd(D2.canon.tabs(T.VPair{kk, T.VAots{p,
          T.VInl{a1} <> et}} <> t)) == True{} : Bool} ->
          {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>} -> M13.tp.Then(r0, he, List.append(&2,
          T.Val, mm, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VInl{a1} <> et}} <> t)), rest,
          PP) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VInl{a1} <> et}} <> t, "\n", True{},
          True{}), rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un, lf, ab)})),
          M9.wt.ok(T.wf.go(T.VInl{a1} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VHead{+a1, +a2} <> +et}} <> +t False{}:
      _ej => hw =>
        +hin = {M9.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VHead{a1, a2} <> et)), Bool.and(T.wf.key(kk, t),
          T.str.eq(p,
          T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VHead{a1, a2} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp})), hw)
          : {T.wf.then(T.wf.go(T.VHead{a1, a2} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp})) == True{} : Bool}}
        Eq.bit.absurd(&1, {D4.short.rows(T.VPair{kk, T.VAots{p, T.VHead{a1,
          a2} <> et}} <> t) == True{} : Bool} -> {M5.cv.fr(cs, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VHead{a1,
          a2} <> et}} <> t)) == True{} : Bool} -> {M5.nd(D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VHead{a1,
          a2} <> et}} <> t)) == True{} : Bool} ->
          {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>} -> M13.tp.Then(r0, he, List.append(&2,
          T.Val, mm, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VHead{a1, a2} <> et}} <> t)), rest,
          PP) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VHead{a1, a2} <> et}} <> t, "\n",
          True{}, True{}), rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un, lf, ab)})),
          M9.wt.ok(T.wf.go(T.VHead{a1, a2} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VAots{+a1, +a2} <> +et}} <> +t False{}:
      _ej => hw =>
        +hin = {M9.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VAots{a1, a2} <> et)), Bool.and(T.wf.key(kk, t),
          T.str.eq(p,
          T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VAots{a1, a2} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp})), hw)
          : {T.wf.then(T.wf.go(T.VAots{a1, a2} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp})) == True{} : Bool}}
        Eq.bit.absurd(&1, {D4.short.rows(T.VPair{kk, T.VAots{p, T.VAots{a1,
          a2} <> et}} <> t) == True{} : Bool} -> {M5.cv.fr(cs, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VAots{a1,
          a2} <> et}} <> t)) == True{} : Bool} -> {M5.nd(D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VAots{a1,
          a2} <> et}} <> t)) == True{} : Bool} ->
          {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>} -> M13.tp.Then(r0, he, List.append(&2,
          T.Val, mm, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VAots{a1, a2} <> et}} <> t)), rest,
          PP) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VAots{a1, a2} <> et}} <> t, "\n",
          True{}, True{}), rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un, lf, ab)})),
          M9.wt.ok(T.wf.go(T.VAots{a1, a2} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VPair{+a1, T.VStr{+b1}} <> +et}} <> +t False{}:
      _ej => hw =>
        +hin = {M9.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VPair{a1, T.VStr{b1}} <> et)),
          Bool.and(T.wf.key(kk, t), T.str.eq(p,
          T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VPair{a1, T.VStr{b1}} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp})), hw)
          : {T.wf.then(T.wf.go(T.VPair{a1, T.VStr{b1}} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp})) == True{} : Bool}}
        Eq.bit.absurd(&1, {D4.short.rows(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VStr{b1}} <> et}} <> t) == True{} : Bool} -> {M5.cv.fr(cs, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VStr{b1}} <> et}} <> t)) == True{} : Bool} -> {M5.nd(D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VStr{b1}} <> et}} <> t)) == True{} : Bool} ->
          {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>} -> M13.tp.Then(r0, he, List.append(&2,
          T.Val, mm, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VStr{b1}} <> et}} <> t)), rest,
          PP) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VStr{b1}} <> et}} <> t,
          "\n", True{}, True{}), rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un, lf, ab)})),
          M9.wt.ok(T.wf.go(T.VPair{a1, T.VStr{b1}} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VPair{+a1, T.VSpan{+b1, +b2}} <> +et}} <> +t False{}:
      _ej => hw =>
        +hin = {M9.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VPair{a1, T.VSpan{b1, b2}} <> et)),
          Bool.and(T.wf.key(kk, t), T.str.eq(p,
          T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VPair{a1, T.VSpan{b1, b2}} <> et, T.WfElems{p}),
            _v => T.wf.go(t, T.WfRows{hp})), hw)
          : {T.wf.then(T.wf.go(T.VPair{a1, T.VSpan{b1, b2}} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp})) == True{} : Bool}}
        Eq.bit.absurd(&1, {D4.short.rows(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VSpan{b1,
          b2}} <> et}} <> t) == True{} : Bool} -> {M5.cv.fr(cs, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VSpan{b1, b2}} <> et}} <> t)) == True{} : Bool} -> {M5.nd(D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VSpan{b1,
          b2}} <> et}} <> t)) == True{} : Bool} ->
          {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>} -> M13.tp.Then(r0, he, List.append(&2,
          T.Val, mm, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VSpan{b1, b2}} <> et}} <> t)), rest,
          PP) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VSpan{b1,
          b2}} <> et}} <> t, "\n", True{}, True{}), rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un,
          lf, ab)})), M9.wt.ok(T.wf.go(T.VPair{a1, T.VSpan{b1, b2}} <> et, T.WfElems{p}), _v => T.wf.go(t,
              T.WfRows{hp}),
          hin))
    case T.VPair{+kk, T.VAots{+p, T.VPair{+a1, T.VInt{+b1, +b2}} <> +et}} <> +t False{}:
      _ej => hw =>
        +hin = {M9.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VPair{a1, T.VInt{b1, b2}} <> et)),
          Bool.and(T.wf.key(kk, t), T.str.eq(p,
          T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VPair{a1, T.VInt{b1, b2}} <> et, T.WfElems{p}),
            _v => T.wf.go(t, T.WfRows{hp})), hw)
          : {T.wf.then(T.wf.go(T.VPair{a1, T.VInt{b1, b2}} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp})) == True{} : Bool}}
        Eq.bit.absurd(&1, {D4.short.rows(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VInt{b1,
          b2}} <> et}} <> t) == True{} : Bool} -> {M5.cv.fr(cs, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VInt{b1, b2}} <> et}} <> t)) == True{} : Bool} -> {M5.nd(D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VInt{b1,
          b2}} <> et}} <> t)) == True{} : Bool} ->
          {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>} -> M13.tp.Then(r0, he, List.append(&2,
          T.Val, mm, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VInt{b1, b2}} <> et}} <> t)), rest,
          PP) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VInt{b1,
          b2}} <> et}} <> t, "\n", True{}, True{}), rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un,
          lf, ab)})), M9.wt.ok(T.wf.go(T.VPair{a1, T.VInt{b1, b2}} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}),
          hin))
    case T.VPair{+kk, T.VAots{+p, T.VPair{+a1, T.VFlo{+b1, +b2}} <> +et}} <> +t False{}:
      _ej => hw =>
        +hin = {M9.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VPair{a1, T.VFlo{b1, b2}} <> et)),
          Bool.and(T.wf.key(kk, t), T.str.eq(p,
          T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VPair{a1, T.VFlo{b1, b2}} <> et, T.WfElems{p}),
            _v => T.wf.go(t, T.WfRows{hp})), hw)
          : {T.wf.then(T.wf.go(T.VPair{a1, T.VFlo{b1, b2}} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp})) == True{} : Bool}}
        Eq.bit.absurd(&1, {D4.short.rows(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VFlo{b1,
          b2}} <> et}} <> t) == True{} : Bool} -> {M5.cv.fr(cs, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VFlo{b1, b2}} <> et}} <> t)) == True{} : Bool} -> {M5.nd(D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VFlo{b1,
          b2}} <> et}} <> t)) == True{} : Bool} ->
          {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>} -> M13.tp.Then(r0, he, List.append(&2,
          T.Val, mm, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VFlo{b1, b2}} <> et}} <> t)), rest,
          PP) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VFlo{b1,
          b2}} <> et}} <> t, "\n", True{}, True{}), rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un,
          lf, ab)})), M9.wt.ok(T.wf.go(T.VPair{a1, T.VFlo{b1, b2}} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}),
          hin))
    case T.VPair{+kk, T.VAots{+p, T.VPair{+a1, T.VBool{+b1}} <> +et}} <> +t False{}:
      _ej => hw =>
        +hin = {M9.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VPair{a1, T.VBool{b1}} <> et)),
          Bool.and(T.wf.key(kk, t), T.str.eq(p,
          T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VPair{a1, T.VBool{b1}} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp})), hw)
          : {T.wf.then(T.wf.go(T.VPair{a1, T.VBool{b1}} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp})) == True{} : Bool}}
        Eq.bit.absurd(&1, {D4.short.rows(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VBool{b1}} <> et}} <> t) == True{} : Bool} -> {M5.cv.fr(cs, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VBool{b1}} <> et}} <> t)) == True{} : Bool} -> {M5.nd(D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VBool{b1}} <> et}} <> t)) == True{} : Bool} ->
          {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>} -> M13.tp.Then(r0, he, List.append(&2,
          T.Val, mm, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VBool{b1}} <> et}} <> t)), rest,
          PP) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VBool{b1}} <> et}} <> t,
          "\n", True{}, True{}), rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un, lf, ab)})),
          M9.wt.ok(T.wf.go(T.VPair{a1, T.VBool{b1}} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VPair{+a1, T.VWhen{+b1}} <> +et}} <> +t False{}:
      _ej => hw =>
        +hin = {M9.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VPair{a1, T.VWhen{b1}} <> et)),
          Bool.and(T.wf.key(kk, t), T.str.eq(p,
          T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VPair{a1, T.VWhen{b1}} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp})), hw)
          : {T.wf.then(T.wf.go(T.VPair{a1, T.VWhen{b1}} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp})) == True{} : Bool}}
        Eq.bit.absurd(&1, {D4.short.rows(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VWhen{b1}} <> et}} <> t) == True{} : Bool} -> {M5.cv.fr(cs, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VWhen{b1}} <> et}} <> t)) == True{} : Bool} -> {M5.nd(D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VWhen{b1}} <> et}} <> t)) == True{} : Bool} ->
          {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>} -> M13.tp.Then(r0, he, List.append(&2,
          T.Val, mm, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VWhen{b1}} <> et}} <> t)), rest,
          PP) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VWhen{b1}} <> et}} <> t,
          "\n", True{}, True{}), rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un, lf, ab)})),
          M9.wt.ok(T.wf.go(T.VPair{a1, T.VWhen{b1}} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VPair{+a1, T.VArr{+b1}} <> +et}} <> +t False{}:
      _ej => hw =>
        +hin = {M9.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VPair{a1, T.VArr{b1}} <> et)),
          Bool.and(T.wf.key(kk, t), T.str.eq(p,
          T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VPair{a1, T.VArr{b1}} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp})), hw)
          : {T.wf.then(T.wf.go(T.VPair{a1, T.VArr{b1}} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp})) == True{} : Bool}}
        Eq.bit.absurd(&1, {D4.short.rows(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VArr{b1}} <> et}} <> t) == True{} : Bool} -> {M5.cv.fr(cs, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VArr{b1}} <> et}} <> t)) == True{} : Bool} -> {M5.nd(D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VArr{b1}} <> et}} <> t)) == True{} : Bool} ->
          {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>} -> M13.tp.Then(r0, he, List.append(&2,
          T.Val, mm, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VArr{b1}} <> et}} <> t)), rest,
          PP) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VArr{b1}} <> et}} <> t,
          "\n", True{}, True{}), rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un, lf, ab)})),
          M9.wt.ok(T.wf.go(T.VPair{a1, T.VArr{b1}} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VPair{+a1, T.VInl{+b1}} <> +et}} <> +t False{}:
      _ej => hw =>
        +hin = {M9.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VPair{a1, T.VInl{b1}} <> et)),
          Bool.and(T.wf.key(kk, t), T.str.eq(p,
          T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VPair{a1, T.VInl{b1}} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp})), hw)
          : {T.wf.then(T.wf.go(T.VPair{a1, T.VInl{b1}} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp})) == True{} : Bool}}
        Eq.bit.absurd(&1, {D4.short.rows(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VInl{b1}} <> et}} <> t) == True{} : Bool} -> {M5.cv.fr(cs, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VInl{b1}} <> et}} <> t)) == True{} : Bool} -> {M5.nd(D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VInl{b1}} <> et}} <> t)) == True{} : Bool} ->
          {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>} -> M13.tp.Then(r0, he, List.append(&2,
          T.Val, mm, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VInl{b1}} <> et}} <> t)), rest,
          PP) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VInl{b1}} <> et}} <> t,
          "\n", True{}, True{}), rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un, lf, ab)})),
          M9.wt.ok(T.wf.go(T.VPair{a1, T.VInl{b1}} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}), hin))
    case T.VPair{+kk, T.VAots{+p, T.VPair{+a1, T.VHead{+b1, +b2}} <> +et}} <> +t False{}:
      _ej => hw =>
        +hin = {M9.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VPair{a1, T.VHead{b1, b2}} <> et)),
          Bool.and(T.wf.key(kk, t), T.str.eq(p,
          T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VPair{a1, T.VHead{b1, b2}} <> et, T.WfElems{p}),
            _v => T.wf.go(t, T.WfRows{hp})), hw)
          : {T.wf.then(T.wf.go(T.VPair{a1, T.VHead{b1, b2}} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp})) == True{} : Bool}}
        Eq.bit.absurd(&1, {D4.short.rows(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VHead{b1,
          b2}} <> et}} <> t) == True{} : Bool} -> {M5.cv.fr(cs, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VHead{b1, b2}} <> et}} <> t)) == True{} : Bool} -> {M5.nd(D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VHead{b1,
          b2}} <> et}} <> t)) == True{} : Bool} ->
          {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>} -> M13.tp.Then(r0, he, List.append(&2,
          T.Val, mm, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VHead{b1, b2}} <> et}} <> t)), rest,
          PP) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VHead{b1,
          b2}} <> et}} <> t, "\n", True{}, True{}), rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un,
          lf, ab)})), M9.wt.ok(T.wf.go(T.VPair{a1, T.VHead{b1, b2}} <> et, T.WfElems{p}), _v => T.wf.go(t,
              T.WfRows{hp}),
          hin))
    case T.VPair{+kk, T.VAots{+p, T.VPair{+a1, T.VAot{+b1, +b2}} <> +et}} <> +t False{}:
      _ej => hw =>
        +hin = {M9.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VPair{a1, T.VAot{b1, b2}} <> et)),
          Bool.and(T.wf.key(kk, t), T.str.eq(p,
          T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VPair{a1, T.VAot{b1, b2}} <> et, T.WfElems{p}),
            _v => T.wf.go(t, T.WfRows{hp})), hw)
          : {T.wf.then(T.wf.go(T.VPair{a1, T.VAot{b1, b2}} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp})) == True{} : Bool}}
        Eq.bit.absurd(&1, {D4.short.rows(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VAot{b1,
          b2}} <> et}} <> t) == True{} : Bool} -> {M5.cv.fr(cs, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VAot{b1, b2}} <> et}} <> t)) == True{} : Bool} -> {M5.nd(D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VAot{b1,
          b2}} <> et}} <> t)) == True{} : Bool} ->
          {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>} -> M13.tp.Then(r0, he, List.append(&2,
          T.Val, mm, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VAot{b1, b2}} <> et}} <> t)), rest,
          PP) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VAot{b1,
          b2}} <> et}} <> t, "\n", True{}, True{}), rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un,
          lf, ab)})), M9.wt.ok(T.wf.go(T.VPair{a1, T.VAot{b1, b2}} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}),
          hin))
    case T.VPair{+kk, T.VAots{+p, T.VPair{+a1, T.VAots{+b1, +b2}} <> +et}} <> +t False{}:
      _ej => hw =>
        +hin = {M9.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VPair{a1, T.VAots{b1, b2}} <> et)),
          Bool.and(T.wf.key(kk, t), T.str.eq(p,
          T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VPair{a1, T.VAots{b1, b2}} <> et, T.WfElems{p}),
            _v => T.wf.go(t, T.WfRows{hp})), hw)
          : {T.wf.then(T.wf.go(T.VPair{a1, T.VAots{b1, b2}} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp})) == True{} : Bool}}
        Eq.bit.absurd(&1, {D4.short.rows(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VAots{b1,
          b2}} <> et}} <> t) == True{} : Bool} -> {M5.cv.fr(cs, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VAots{b1, b2}} <> et}} <> t)) == True{} : Bool} -> {M5.nd(D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VAots{b1,
          b2}} <> et}} <> t)) == True{} : Bool} ->
          {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>} -> M13.tp.Then(r0, he, List.append(&2,
          T.Val, mm, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VAots{b1, b2}} <> et}} <> t)), rest,
          PP) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VAots{b1,
          b2}} <> et}} <> t, "\n", True{}, True{}), rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un,
          lf, ab)})), M9.wt.ok(T.wf.go(T.VPair{a1, T.VAots{b1, b2}} <> et, T.WfElems{p}), _v => T.wf.go(t,
              T.WfRows{hp}),
          hin))
    case T.VPair{+kk, T.VAots{+p, T.VPair{+a1, T.VPair{+b1, +b2}} <> +et}} <> +t False{}:
      _ej => hw =>
        +hin = {M9.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VPair{a1, T.VPair{b1, b2}} <> et)),
          Bool.and(T.wf.key(kk, t), T.str.eq(p,
          T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VPair{a1, T.VPair{b1, b2}} <> et, T.WfElems{p}),
            _v => T.wf.go(t, T.WfRows{hp})), hw)
          : {T.wf.then(T.wf.go(T.VPair{a1, T.VPair{b1, b2}} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp})) == True{} : Bool}}
        Eq.bit.absurd(&1, {D4.short.rows(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VPair{b1,
          b2}} <> et}} <> t) == True{} : Bool} -> {M5.cv.fr(cs, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VPair{b1, b2}} <> et}} <> t)) == True{} : Bool} -> {M5.nd(D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VPair{a1,
          T.VPair{b1,
          b2}} <> et}} <> t)) == True{} : Bool} ->
          {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>} -> M13.tp.Then(r0, he, List.append(&2,
          T.Val, mm, D2.canon.tabs(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VPair{b1, b2}} <> et}} <> t)), rest,
          PP) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VPair{a1, T.VPair{b1,
          b2}} <> et}} <> t, "\n", True{}, True{}), rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un,
          lf, ab)})), M9.wt.ok(T.wf.go(T.VPair{a1, T.VPair{b1, b2}} <> et, T.WfElems{p}), _v => T.wf.go(t,
              T.WfRows{hp}),
          hin))
    case T.VPair{+kk, T.VAots{+p, T.VAot{+q, +r} <> +et}} <> +t False{}:
      +ej => +hw => +hl => +hf => +hn => +ho => ih =>
        +ha = {M9.wt.ok(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VAot{q, r} <> et)), Bool.and(T.wf.key(kk, t),
          T.str.eq(p,
          T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VAot{q, r} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp})), hw)
          : {Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VAot{q, r} <> et)), Bool.and(T.wf.key(kk, t), T.str.eq(p,
            T.tree.pre(hp, kk))))
          == True{} : Bool}}
        +hin = {M9.wt.more(Bool.and(Bool.not(List.is_empty(&2, T.Val, T.VAot{q, r} <> et)), Bool.and(T.wf.key(kk, t),
          T.str.eq(p,
          T.tree.pre(hp, kk)))), _u => T.wf.then(T.wf.go(T.VAot{q, r} <> et, T.WfElems{p}), _v => T.wf.go(t,
            T.WfRows{hp})), hw)
          : {T.wf.then(T.wf.go(T.VAot{q, r} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp})) == True{} : Bool}}
        +hwe = {M9.wt.ok(T.wf.go(T.VAot{q, r} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}),
          hin) : {T.wf.go(T.VAot{q, r} <> et, T.WfElems{p})
          == True{} : Bool}}
        +hwt = {M9.wt.more(T.wf.go(T.VAot{q, r} <> et, T.WfElems{p}), _v => T.wf.go(t, T.WfRows{hp}), hin) : {T.wf.go(t,
          T.WfRows{hp})
          == True{} : Bool}}
        +hb = {Eq.and.right(Bool.not(List.is_empty(&2, T.Val, T.VAot{q, r} <> et)), Bool.and(T.wf.key(kk, t),
          T.str.eq(p, T.tree.pre(hp,
          kk))), ha) : {Bool.and(T.wf.key(kk, t), T.str.eq(p, T.tree.pre(hp, kk))) == True{} : Bool}}
        +ep = {Equal.trans(String, T.tree.pre(D1.tb.join(he, ""), kk), T.tree.pre(hp, kk), p,
          Equal.cong(String, String, zz => T.tree.pre(zz, kk), D1.tb.join(he, ""), hp, ej),
          Equal.sym(String, p, T.tree.pre(hp, kk), M4.str.eq.true(p, T.tree.pre(hp, kk), Eq.and.right(T.wf.key(kk, t),
          T.str.eq(p, T.tree.pre(hp, kk)), hb)))) : {T.tree.pre(D1.tb.join(he, ""), kk) == p : String}}
        +shp = {Eq.and.left(D1.short(p), Bool.and(D4.short.rows(T.VAot{q, r} <> et), D4.short.rows(t)),
          hl) : {D1.short(p)
          == True{} : Bool}}
        +hl2 = {Eq.and.right(D1.short(p), Bool.and(D4.short.rows(T.VAot{q, r} <> et), D4.short.rows(t)), hl)
          : {Bool.and(D4.short.rows(T.VAot{q, r} <> et), D4.short.rows(t)) == True{} : Bool}}
        +em = {Eq.and.left(L3.is_miss(T.get(cs, kk)), M5.cv.fr(cs, D2.canon.tabs(t)), hf) : {L3.is_miss(T.get(cs,
          kk)) == True{} : Bool}}
        +zz = {String.append(T.render.pass(t, "\n", True{}, True{}), rest) : String}
        +h1 = {M9.wt.more(T.str.eq(q, p), _u => T.wf.then(T.wf.go(r, T.WfRows{q}), _v => T.wf.go(et, T.WfElems{p})),
          hwe) : {T.wf.then(T.wf.go(r, T.WfRows{q}), _v => T.wf.go(et, T.WfElems{p})) == True{} : Bool}}
        +eq = {M4.str.eq.true(q, p, M9.wt.ok(T.str.eq(q, p), _u => T.wf.then(T.wf.go(r, T.WfRows{q}), _v => T.wf.go(et,
          T.WfElems{p})), hwe)) : {q == p : String}}
        +hwr = {M9.wt.ok(T.wf.go(r, T.WfRows{q}), _v => T.wf.go(et, T.WfElems{p}), h1) : {T.wf.go(r, T.WfRows{q})
          == True{} : Bool}}
        +hwet = {M9.wt.more(T.wf.go(r, T.WfRows{q}), _v => T.wf.go(et, T.WfElems{p}), h1) : {T.wf.go(et,
          T.WfElems{p}) == True{} : Bool}}
        +hle = {Eq.and.left(D4.short.rows(T.VAot{q, r} <> et), D4.short.rows(t), hl2)
          : {Bool.and(D4.short.rows(r), D4.short.rows(et)) == True{} : Bool}}
        +ejq = {Equal.trans(String, D1.tb.join(List.append(&2, String, he, [kk]), ""), p, q, Equal.trans(String,
          D1.tb.join(List.append(&2, String, he, [kk]), ""),
          T.tree.pre(D1.tb.join(he, ""), kk), p, wa.ja(he, "", kk), ep), Equal.sym(String, q, p, eq))
          : {D1.tb.join(List.append(&2, String, he, [kk]), "") == q : String}}
        +bd = {String.append(T.render.pass(r, "\n", True{}, False{}), String.append(T.render.pass(r, "\n", True{},
          True{}), String.append(T.render.pass(et, "\n", True{}, True{}), zz))) : String}
        +x0 = {T.VPair{kk, T.VAots{p, D2.canon.go(T.VAot{q, r} <> et, D2.CElems{p})}} : T.Val}
        M13.pp.step(PP, T.doc.read(String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VAot{q, r} <> et}} <> t, "\n",
          True{}, True{}), rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un, lf, ab)}),
          T.doc.read(SCon{'[', SCon{'[', String.append(p, SCon{']', SCon{']', SCon{'\n', bd}}})}},
            T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un, lf, ab)}),
          Equal.cong(String, T.Doc, ss => T.doc.read(ss, T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un,
            lf, ab)}),
            String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VAot{q, r} <> et}} <> t, "\n", True{}, True{}), rest),
              SCon{'[', SCon{'[', String.append(p, SCon{']', SCon{']',
            SCon{'\n', bd}}})}},
            Equal.trans(String, String.append(T.render.pass(T.VPair{kk, T.VAots{p, T.VAot{q, r} <> et}} <> t, "\n",
              True{}, True{}), rest), String.append(T.render.pass(T.VAot{q, r} <> et, "\n", True{}, True{}), zz),
              SCon{'[', SCon{'[', String.append(p, SCon{']', SCon{']', SCon{'\n', bd}}})}},
              M12.tt.aots(kk, p, T.VAot{q, r} <> et, t, rest, M12.tt.pe(T.VAot{q, r} <> et, p, hwe)),
            Equal.trans(String, String.append(T.render.pass(T.VAot{q, r} <> et, "\n", True{}, True{}), zz), SCon{'[',
              SCon{'[', String.append(q, SCon{']',
              SCon{']', SCon{'\n', bd}}})}}, SCon{'[', SCon{'[', String.append(p, SCon{']', SCon{']', SCon{'\n',
              bd}}})}}, tt.aot(q, r, et, zz),
              Equal.cong(String, String, s2 => SCon{'[', SCon{'[', String.append(s2, SCon{']', SCon{']', SCon{'\n',
                bd}}})}}, q, p, eq)))),
          hdr.aot0(kk, p, he, r0, cs, hs, cur, bk, qk, un, lf, ab, bd, PP, eo, em, ep,
            +hs2 => +b2 => +q2 => +u2 => +l2 => M13.body(kk, T.VAots{p, [T.VAot{p, []}]}, r, q, he, r0, cs, hs2, b2, q2,
              u2, l2, False{}, String.append(T.render.pass(et, "\n", True{}, True{}), zz), PP, eo, em, {==},
              cd(he, kk, Equal.trans(Bool, D1.short(T.tree.pre(D1.tb.join(he, ""), kk)), D1.short(p), True{},
                Equal.cong(String, Bool, s2 => D1.short(s2), T.tree.pre(D1.tb.join(he, ""), kk), p, ep), shp)),
              hwr, Eq.and.left(D4.short.rows(r), D4.short.rows(et), hle),
              +c2 => +b3 => +q3 => +u3 => +l3 => f2 => n2 => o2 => i2 => tp(r, False{}, q, D1.tb.set(he, "", r0,
                T.VPair{kk, T.VAots{p, [T.VAot{p, []}]}} <> cs), List.append(&2, String, he, [kk]), c2,
                  D2.canon.keys(r), nn, ee, hs2, List.append(&2, String, he, [kk]), b3,
                q3, u3, l3, False{}, String.append(T.render.pass(et, "\n", True{}, True{}), zz), PP, M13.wa.eopen(he,
                    r0,
                  kk, T.VAots{p, [T.VAot{p, []}]}, cs, eo,
                {==}))(ejq, hwr, Eq.and.left(D4.short.rows(r), D4.short.rows(et), hle), f2, n2, o2, i2),
              +c3 => +hs3 => +he3 => +b4 => +q4 => +u4 => +l4 => +a4 => o3 => tp(et, True{}, p, r0, he, cs,
                [T.VAot{p, D2.canon.rows(r)}], kk, [T.VAot{p, c3}], hs3, he3, b4, q4, u4, l4, a4, zz, PP, eo)(ep, em,
                shp, hwet, Eq.and.right(D4.short.rows(r), D4.short.rows(et), hle),
                Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => [T.VAot{p, zs}], D1.own.rows(T.rows.seal(c3)),
                  D1.own.rows(D2.canon.rows(r)), o3),
                +e5 => +hs5 => +he5 => +b5 => +q5 => +u5 => +l5 => +a5 => o5 => tp(t, False{}, hp, r0, he,
                  T.VPair{kk, T.VAots{p, e5}} <> cs, List.append(&2, T.Val, mm, [x0]), nn, ee, hs5, he5, b5, q5, u5, l5,
                    a5, rest,
                  PP, eo)(ej, hwt, Eq.and.right(D4.short.rows(T.VAot{q, r} <> et), D4.short.rows(t), hl2),
                  M13.cv.fr.step(D2.canon.tabs(t), kk, T.VAots{p, e5}, cs, Eq.and.right(L3.is_miss(T.get(cs, kk)),
                    M5.cv.fr(cs, D2.canon.tabs(t)), hf), Eq.and.left(T.wf.fresh(T.get(D2.canon.tabs(t), kk)),
                    M5.nd(D2.canon.tabs(t)), hn)),
                  Eq.and.right(T.wf.fresh(T.get(D2.canon.tabs(t), kk)), M5.nd(D2.canon.tabs(t)), hn),
                  M13.os.step(T.VPair{kk, T.VAots{p, e5}}, cs, mm, x0, ho, Equal.cong(List<&2, T.Val>, List<&2, T.Val>,
                    zs => [T.VPair{kk, T.VAots{p, zs}}], D1.own.rows(T.rows.seal(e5)),
                    D1.own.rows(D2.canon.go(T.VAot{q, r} <> et, D2.CElems{p})), o5)),
                  +c6 => +hs6 => +he6 => +b6 => +q6 => +u6 => +l6 => +a6 => o6 => ih(c6, hs6, he6, b6, q6, u6, l6, a6,
                    Equal.trans(List<&2, T.Val>, D1.own.rows(T.rows.seal(c6)), D1.own.rows(List.append(&2, T.Val,
                      List.append(&2, T.Val, mm, [x0]), D2.canon.tabs(t))),
                      D1.own.rows(List.append(&2, T.Val, mm, x0 <> D2.canon.tabs(t))), o6,
                      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => D1.own.rows(zs), List.append(&2, T.Val,
                        List.append(&2, T.Val, mm, [x0]), D2.canon.tabs(t)),
                        List.append(&2, T.Val, mm, x0 <> D2.canon.tabs(t)), M5.va.assoc(mm, [x0],
                          D2.canon.tabs(t)))))))))
)
    case T.VPair{+kk, T.VStr{+a1}} <> +t False{}:
      ej => hw => hl => hf => hn => ho => ih => tp(t, False{}, hp, r0, he, cs, mm, nn, ee, hs, cur, bk, qk, un, lf, ab,
        rest,
        PP, eo)(ej, M9.wt.more(Bool.and(T.wf.atom(T.VStr{a1}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}), hw),
        Eq.and.right(D1.cv.short1(T.VStr{a1}), D4.short.rows(t), hl), hf, hn, ho, ih)
    case T.VPair{+kk, T.VSpan{+a1, +a2}} <> +t False{}:
      ej => hw => hl => hf => hn => ho => ih => tp(t, False{}, hp, r0, he, cs, mm, nn, ee, hs, cur, bk, qk, un, lf, ab,
        rest,
        PP, eo)(ej, M9.wt.more(Bool.and(T.wf.atom(T.VSpan{a1, a2}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}),
            hw),
        Eq.and.right(D1.cv.short1(T.VSpan{a1, a2}), D4.short.rows(t), hl), hf, hn, ho, ih)
    case T.VPair{+kk, T.VInt{+a1, +a2}} <> +t False{}:
      ej => hw => hl => hf => hn => ho => ih => tp(t, False{}, hp, r0, he, cs, mm, nn, ee, hs, cur, bk, qk, un, lf, ab,
        rest,
        PP, eo)(ej, M9.wt.more(Bool.and(T.wf.atom(T.VInt{a1, a2}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}),
            hw),
        Eq.and.right(D1.cv.short1(T.VInt{a1, a2}), D4.short.rows(t), hl), hf, hn, ho, ih)
    case T.VPair{+kk, T.VFlo{+a1, +a2}} <> +t False{}:
      ej => hw => hl => hf => hn => ho => ih => tp(t, False{}, hp, r0, he, cs, mm, nn, ee, hs, cur, bk, qk, un, lf, ab,
        rest,
        PP, eo)(ej, M9.wt.more(Bool.and(T.wf.atom(T.VFlo{a1, a2}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}),
            hw),
        Eq.and.right(D1.cv.short1(T.VFlo{a1, a2}), D4.short.rows(t), hl), hf, hn, ho, ih)
    case T.VPair{+kk, T.VBool{+a1}} <> +t False{}:
      ej => hw => hl => hf => hn => ho => ih => tp(t, False{}, hp, r0, he, cs, mm, nn, ee, hs, cur, bk, qk, un, lf, ab,
        rest,
        PP, eo)(ej, M9.wt.more(Bool.and(T.wf.atom(T.VBool{a1}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}), hw),
        Eq.and.right(D1.cv.short1(T.VBool{a1}), D4.short.rows(t), hl), hf, hn, ho, ih)
    case T.VPair{+kk, T.VWhen{+a1}} <> +t False{}:
      ej => hw => hl => hf => hn => ho => ih => tp(t, False{}, hp, r0, he, cs, mm, nn, ee, hs, cur, bk, qk, un, lf, ab,
        rest,
        PP, eo)(ej, M9.wt.more(Bool.and(T.wf.atom(T.VWhen{a1}), T.wf.key(kk, t)), _u => T.wf.go(t, T.WfRows{hp}), hw),
        Eq.and.right(D1.cv.short1(T.VWhen{a1}), D4.short.rows(t), hl), hf, hn, ho, ih)
    case T.VPair{+kk, T.VArr{+a1}} <> +t False{}:
      ej => hw => hl => hf => hn => ho => ih => tp(t, False{}, hp, r0, he, cs, mm, nn, ee, hs, cur, bk, qk, un, lf, ab,
        rest,
        PP, eo)(ej, M9.wt.more(T.wf.go(a1, T.WfItems{}), _v => T.wf.go(t, T.WfRows{hp}), M9.wt.more(T.wf.key(kk, t),
        _u => T.wf.then(T.wf.go(a1, T.WfItems{}), _v => T.wf.go(t, T.WfRows{hp})), hw)),
        Eq.and.right(D1.cv.short1(T.VArr{a1}), D4.short.rows(t), hl), hf, hn, ho, ih)
    case T.VPair{+kk, T.VInl{+a1}} <> +t False{}:
      ej => hw => hl => hf => hn => ho => ih => tp(t, False{}, hp, r0, he, cs, mm, nn, ee, hs, cur, bk, qk, un, lf, ab,
        rest,
        PP, eo)(ej, M9.wt.more(T.wf.go(a1, T.WfInl{}), _v => T.wf.go(t, T.WfRows{hp}), M9.wt.more(T.wf.key(kk, t),
        _u => T.wf.then(T.wf.go(a1, T.WfInl{}), _v => T.wf.go(t, T.WfRows{hp})), hw)),
        Eq.and.right(D1.cv.short1(T.VInl{a1}), D4.short.rows(t), hl), hf, hn, ho, ih)
    case T.VPair{+kk, T.VAot{+a1, +a2}} <> +t False{}:
      _ej => hw => Eq.bit.absurd(&1, {D4.short.rows(T.VPair{kk, T.VAot{a1, a2}} <> t) == True{} : Bool} -> {M5.cv.fr(cs,
        D2.canon.tabs(T.VPair{kk, T.VAot{a1, a2}} <> t))
        == True{} : Bool} -> {M5.nd(D2.canon.tabs(T.VPair{kk, T.VAot{a1,
          a2}} <> t)) == True{} : Bool} -> {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>} ->
        M13.tp.Then(r0, he, List.append(&2, T.Val, mm, D2.canon.tabs(T.VPair{kk, T.VAot{a1, a2}} <> t)), rest,
          PP) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{kk, T.VAot{a1, a2}} <> t, "\n", True{}, True{}),
          rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un, lf, ab)})), hw)
    case T.VPair{+kk, T.VPair{+a1, +a2}} <> +t False{}:
      _ej => hw => Eq.bit.absurd(&1, {D4.short.rows(T.VPair{kk, T.VPair{a1,
          a2}} <> t) == True{} : Bool} -> {M5.cv.fr(cs,
        D2.canon.tabs(T.VPair{kk, T.VPair{a1, a2}} <> t))
        == True{} : Bool} -> {M5.nd(D2.canon.tabs(T.VPair{kk, T.VPair{a1,
          a2}} <> t)) == True{} : Bool} -> {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>} ->
        M13.tp.Then(r0, he, List.append(&2, T.Val, mm, D2.canon.tabs(T.VPair{kk, T.VPair{a1, a2}} <> t)), rest,
          PP) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{kk, T.VPair{a1, a2}} <> t, "\n", True{}, True{}),
          rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un, lf, ab)})), hw)
    case T.VStr{+a1} <> +t False{}:
      _ej => hw => Eq.bit.absurd(&1, {D4.short.rows(T.VStr{a1} <> t) == True{} : Bool} -> {M5.cv.fr(cs,
        D2.canon.tabs(T.VStr{a1} <> t))
        == True{} : Bool} -> {M5.nd(D2.canon.tabs(T.VStr{a1} <> t)) == True{} : Bool} ->
          {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>} ->
        M13.tp.Then(r0, he, List.append(&2, T.Val, mm, D2.canon.tabs(T.VStr{a1} <> t)), rest,
          PP) -> PP(T.doc.read(String.append(T.render.pass(T.VStr{a1} <> t, "\n", True{}, True{}), rest),
          T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un, lf, ab)})), hw)
    case T.VSpan{+a1, +a2} <> +t False{}:
      _ej => hw => Eq.bit.absurd(&1, {D4.short.rows(T.VSpan{a1, a2} <> t) == True{} : Bool} -> {M5.cv.fr(cs,
        D2.canon.tabs(T.VSpan{a1, a2} <> t))
        == True{} : Bool} -> {M5.nd(D2.canon.tabs(T.VSpan{a1,
          a2} <> t)) == True{} : Bool} -> {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>} ->
        M13.tp.Then(r0, he, List.append(&2, T.Val, mm, D2.canon.tabs(T.VSpan{a1, a2} <> t)), rest,
          PP) -> PP(T.doc.read(String.append(T.render.pass(T.VSpan{a1, a2} <> t, "\n", True{}, True{}), rest),
          T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un, lf, ab)})), hw)
    case T.VInt{+a1, +a2} <> +t False{}:
      _ej => hw => Eq.bit.absurd(&1, {D4.short.rows(T.VInt{a1, a2} <> t) == True{} : Bool} -> {M5.cv.fr(cs,
        D2.canon.tabs(T.VInt{a1, a2} <> t))
        == True{} : Bool} -> {M5.nd(D2.canon.tabs(T.VInt{a1,
          a2} <> t)) == True{} : Bool} -> {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>} ->
        M13.tp.Then(r0, he, List.append(&2, T.Val, mm, D2.canon.tabs(T.VInt{a1, a2} <> t)), rest,
          PP) -> PP(T.doc.read(String.append(T.render.pass(T.VInt{a1, a2} <> t, "\n", True{}, True{}), rest),
          T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un, lf, ab)})), hw)
    case T.VFlo{+a1, +a2} <> +t False{}:
      _ej => hw => Eq.bit.absurd(&1, {D4.short.rows(T.VFlo{a1, a2} <> t) == True{} : Bool} -> {M5.cv.fr(cs,
        D2.canon.tabs(T.VFlo{a1, a2} <> t))
        == True{} : Bool} -> {M5.nd(D2.canon.tabs(T.VFlo{a1,
          a2} <> t)) == True{} : Bool} -> {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>} ->
        M13.tp.Then(r0, he, List.append(&2, T.Val, mm, D2.canon.tabs(T.VFlo{a1, a2} <> t)), rest,
          PP) -> PP(T.doc.read(String.append(T.render.pass(T.VFlo{a1, a2} <> t, "\n", True{}, True{}), rest),
          T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un, lf, ab)})), hw)
    case T.VBool{+a1} <> +t False{}:
      _ej => hw => Eq.bit.absurd(&1, {D4.short.rows(T.VBool{a1} <> t) == True{} : Bool} -> {M5.cv.fr(cs,
        D2.canon.tabs(T.VBool{a1} <> t))
        == True{} : Bool} -> {M5.nd(D2.canon.tabs(T.VBool{a1} <> t)) == True{} : Bool} ->
          {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>} ->
        M13.tp.Then(r0, he, List.append(&2, T.Val, mm, D2.canon.tabs(T.VBool{a1} <> t)), rest,
          PP) -> PP(T.doc.read(String.append(T.render.pass(T.VBool{a1} <> t, "\n", True{}, True{}), rest),
          T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un, lf, ab)})), hw)
    case T.VWhen{+a1} <> +t False{}:
      _ej => hw => Eq.bit.absurd(&1, {D4.short.rows(T.VWhen{a1} <> t) == True{} : Bool} -> {M5.cv.fr(cs,
        D2.canon.tabs(T.VWhen{a1} <> t))
        == True{} : Bool} -> {M5.nd(D2.canon.tabs(T.VWhen{a1} <> t)) == True{} : Bool} ->
          {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>} ->
        M13.tp.Then(r0, he, List.append(&2, T.Val, mm, D2.canon.tabs(T.VWhen{a1} <> t)), rest,
          PP) -> PP(T.doc.read(String.append(T.render.pass(T.VWhen{a1} <> t, "\n", True{}, True{}), rest),
          T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un, lf, ab)})), hw)
    case T.VArr{+a1} <> +t False{}:
      _ej => hw => Eq.bit.absurd(&1, {D4.short.rows(T.VArr{a1} <> t) == True{} : Bool} -> {M5.cv.fr(cs,
        D2.canon.tabs(T.VArr{a1} <> t))
        == True{} : Bool} -> {M5.nd(D2.canon.tabs(T.VArr{a1} <> t)) == True{} : Bool} ->
          {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>} ->
        M13.tp.Then(r0, he, List.append(&2, T.Val, mm, D2.canon.tabs(T.VArr{a1} <> t)), rest,
          PP) -> PP(T.doc.read(String.append(T.render.pass(T.VArr{a1} <> t, "\n", True{}, True{}), rest),
          T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un, lf, ab)})), hw)
    case T.VInl{+a1} <> +t False{}:
      _ej => hw => Eq.bit.absurd(&1, {D4.short.rows(T.VInl{a1} <> t) == True{} : Bool} -> {M5.cv.fr(cs,
        D2.canon.tabs(T.VInl{a1} <> t))
        == True{} : Bool} -> {M5.nd(D2.canon.tabs(T.VInl{a1} <> t)) == True{} : Bool} ->
          {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>} ->
        M13.tp.Then(r0, he, List.append(&2, T.Val, mm, D2.canon.tabs(T.VInl{a1} <> t)), rest,
          PP) -> PP(T.doc.read(String.append(T.render.pass(T.VInl{a1} <> t, "\n", True{}, True{}), rest),
          T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un, lf, ab)})), hw)
    case T.VHead{+a1, +a2} <> +t False{}:
      _ej => hw => Eq.bit.absurd(&1, {D4.short.rows(T.VHead{a1, a2} <> t) == True{} : Bool} -> {M5.cv.fr(cs,
        D2.canon.tabs(T.VHead{a1, a2} <> t))
        == True{} : Bool} -> {M5.nd(D2.canon.tabs(T.VHead{a1,
          a2} <> t)) == True{} : Bool} -> {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>} ->
        M13.tp.Then(r0, he, List.append(&2, T.Val, mm, D2.canon.tabs(T.VHead{a1, a2} <> t)), rest,
          PP) -> PP(T.doc.read(String.append(T.render.pass(T.VHead{a1, a2} <> t, "\n", True{}, True{}), rest),
          T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un, lf, ab)})), hw)
    case T.VAot{+a1, +a2} <> +t False{}:
      _ej => hw => Eq.bit.absurd(&1, {D4.short.rows(T.VAot{a1, a2} <> t) == True{} : Bool} -> {M5.cv.fr(cs,
        D2.canon.tabs(T.VAot{a1, a2} <> t))
        == True{} : Bool} -> {M5.nd(D2.canon.tabs(T.VAot{a1,
          a2} <> t)) == True{} : Bool} -> {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>} ->
        M13.tp.Then(r0, he, List.append(&2, T.Val, mm, D2.canon.tabs(T.VAot{a1, a2} <> t)), rest,
          PP) -> PP(T.doc.read(String.append(T.render.pass(T.VAot{a1, a2} <> t, "\n", True{}, True{}), rest),
          T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un, lf, ab)})), hw)
    case T.VAots{+a1, +a2} <> +t False{}:
      _ej => hw => Eq.bit.absurd(&1, {D4.short.rows(T.VAots{a1, a2} <> t) == True{} : Bool} -> {M5.cv.fr(cs,
        D2.canon.tabs(T.VAots{a1, a2} <> t))
        == True{} : Bool} -> {M5.nd(D2.canon.tabs(T.VAots{a1,
          a2} <> t)) == True{} : Bool} -> {D1.own.rows(T.rows.seal(cs)) == D1.own.rows(mm) : List<&2, T.Val>} ->
        M13.tp.Then(r0, he, List.append(&2, T.Val, mm, D2.canon.tabs(T.VAots{a1, a2} <> t)), rest,
          PP) -> PP(T.doc.read(String.append(T.render.pass(T.VAots{a1, a2} <> t, "\n", True{}, True{}), rest),
          T.MScan{M3.dl(D1.tb.set(he, "", r0, cs), hs, cur, bk, qk, un, lf, ab)})), hw)
    case T.VAot{+q, +r} <> +t True{}:
      +ep => +em => +shp => +hw => +hl => +ho => ih =>
        +h1 = {M9.wt.more(T.str.eq(q, hp), _u => T.wf.then(T.wf.go(r, T.WfRows{q}), _v => T.wf.go(t, T.WfElems{hp})),
            hw)
          : {T.wf.then(T.wf.go(r, T.WfRows{q}), _v => T.wf.go(t, T.WfElems{hp})) == True{} : Bool}}
        +eq = {M4.str.eq.true(q, hp, M9.wt.ok(T.str.eq(q, hp), _u => T.wf.then(T.wf.go(r, T.WfRows{q}), _v => T.wf.go(t,
          T.WfElems{hp})), hw)) : {q == hp : String}}
        +hwr = {M9.wt.ok(T.wf.go(r, T.WfRows{q}), _v => T.wf.go(t, T.WfElems{hp}), h1) : {T.wf.go(r,
            T.WfRows{q}) == True{}
          : Bool}}
        +hwt = {M9.wt.more(T.wf.go(r, T.WfRows{q}), _v => T.wf.go(t, T.WfElems{hp}), h1) : {T.wf.go(t, T.WfElems{hp})
          == True{} : Bool}}
        +ejq = {Equal.trans(String, D1.tb.join(List.append(&2, String, he, [nn]), ""), hp, q, Equal.trans(String,
          D1.tb.join(List.append(&2, String, he, [nn]), ""),
          T.tree.pre(D1.tb.join(he, ""), nn), hp, wa.ja(he, "", nn), ep), Equal.sym(String, q, hp, eq))
          : {D1.tb.join(List.append(&2, String, he, [nn]), "") == q : String}}
        +x0 = {T.VAot{hp, D2.canon.rows(r)} : T.Val}
        +bd = {String.append(T.render.pass(r, "\n", True{}, False{}), String.append(T.render.pass(r, "\n", True{},
          True{}), String.append(T.render.pass(t, "\n", True{}, True{}), rest))) : String}
        +st = {T.MScan{M3.dl(D1.tb.set(he, "", r0, T.VPair{nn, T.VAots{hp, ee}} <> cs), hs, cur, bk, qk, un, lf,
          ab)} : T.Mode}
        M13.pp.step(PP, T.doc.read(String.append(T.render.pass(T.VAot{q, r} <> t, "\n", True{}, True{}), rest), st),
          T.doc.read(SCon{'[', SCon{'[', String.append(hp, SCon{']', SCon{']', SCon{'\n', bd}}})}}, st),
          Equal.cong(String, T.Doc, ss => T.doc.read(ss, st),
            String.append(T.render.pass(T.VAot{q, r} <> t, "\n", True{}, True{}), rest), SCon{'[', SCon{'[',
              String.append(hp, SCon{']', SCon{']', SCon{'\n',
            bd}}})}},
            Equal.trans(String, String.append(T.render.pass(T.VAot{q, r} <> t, "\n", True{}, True{}), rest), SCon{'[',
              SCon{'[', String.append(q, SCon{']',
              SCon{']', SCon{'\n', bd}}})}}, SCon{'[', SCon{'[', String.append(hp, SCon{']', SCon{']', SCon{'\n',
              bd}}})}}, tt.aot(q, r, t, rest),
              Equal.cong(String, String, s2 => SCon{'[', SCon{'[', String.append(s2, SCon{']', SCon{']', SCon{'\n',
                bd}}})}}, q, hp, eq))),
          hdr.aot1(nn, hp, ee, he, r0, cs, hs, cur, bk, qk, un, lf, ab, bd, PP, eo, em, ep,
            +hs2 => +b2 => +q2 => +u2 => +l2 => M13.body(nn, T.VAots{hp, T.VAot{hp, []} <> ee}, r, q, he, r0, cs, hs2,
                b2,
              q2, u2, l2, False{}, String.append(T.render.pass(t, "\n", True{}, True{}), rest), PP, eo, em, {==},
              cd(he, nn, Equal.trans(Bool, D1.short(T.tree.pre(D1.tb.join(he, ""), nn)), D1.short(hp), True{},
                Equal.cong(String, Bool, s2 => D1.short(s2), T.tree.pre(D1.tb.join(he, ""), nn), hp, ep), shp)),
              hwr, Eq.and.left(D4.short.rows(r), D4.short.rows(t), hl),
              +c2 => +b3 => +q3 => +u3 => +l3 => f2 => n2 => o2 => i2 => tp(r, False{}, q, D1.tb.set(he, "", r0,
                T.VPair{nn, T.VAots{hp, T.VAot{hp, []} <> ee}} <> cs), List.append(&2, String, he, [nn]), c2,
                  D2.canon.keys(r), nn, ee, hs2, List.append(&2, String, he, [nn]),
                b3, q3, u3, l3, False{}, String.append(T.render.pass(t, "\n", True{}, True{}), rest), PP,
                    M13.wa.eopen(he,
                  r0, nn, T.VAots{hp, T.VAot{hp, []} <> ee},
                cs, eo, {==}))(ejq, hwr, Eq.and.left(D4.short.rows(r), D4.short.rows(t), hl), f2, n2, o2, i2),
              +c3 => +hs3 => +he3 => +b4 => +q4 => +u4 => +l4 => +a4 => o3 => tp(t, True{}, hp, r0, he, cs,
                List.append(&2, T.Val, mm, [x0]), nn, T.VAot{hp, c3} <> ee, hs3, he3, b4, q4, u4, l4, a4, rest, PP,
                  eo)(ep, em, shp,
                hwt, Eq.and.right(D4.short.rows(r), D4.short.rows(t), hl),
                M13.os.step(T.VAot{hp, c3}, ee, mm, x0, ho, Equal.cong(List<&2, T.Val>, List<&2, T.Val>,
                    zs => [T.VAot{hp,
                  zs}], D1.own.rows(T.rows.seal(c3)),
                  D1.own.rows(D2.canon.rows(r)), o3)),
                +e5 => +hs5 => +he5 => +b5 => +q5 => +u5 => +l5 => +a5 => o5 => ih(e5, hs5, he5, b5, q5, u5, l5, a5,
                  Equal.trans(List<&2, T.Val>, D1.own.rows(T.rows.seal(e5)), D1.own.rows(List.append(&2, T.Val,
                    List.append(&2, T.Val, mm, [x0]), D2.canon.go(t, D2.CElems{hp}))),
                    D1.own.rows(List.append(&2, T.Val, mm, x0 <> D2.canon.go(t, D2.CElems{hp}))), o5,
                    Equal.cong(List<&2, T.Val>, List<&2, T.Val>, zs => D1.own.rows(zs), List.append(&2, T.Val,
                      List.append(&2, T.Val, mm, [x0]), D2.canon.go(t, D2.CElems{hp})),
                      List.append(&2, T.Val, mm, x0 <> D2.canon.go(t, D2.CElems{hp})), M5.va.assoc(mm, [x0],
                        D2.canon.go(t,
                      D2.CElems{hp})))))))))
    case T.VStr{+a1} <> +t True{}:
      _ep => _em => _sh => hw => Eq.bit.absurd(&1, {D4.short.rows(T.VStr{a1} <> t) == True{} : Bool} ->
        {D1.own.rows(T.rows.seal(ee)) == D1.own.rows(mm) : List<&2, T.Val>} -> tp.ThenE(r0, he, cs, nn, hp,
          List.append(&2, T.Val, mm, D2.canon.go(T.VStr{a1} <> t, D2.CElems{hp})),
        rest, PP) -> PP(T.doc.read(String.append(T.render.pass(T.VStr{a1} <> t, "\n", True{}, True{}), rest),
          T.MScan{M3.dl(D1.tb.set(he, "", r0, T.VPair{nn, T.VAots{hp, ee}} <> cs), hs, cur, bk, qk, un, lf, ab)})), hw)
    case T.VSpan{+a1, +a2} <> +t True{}:
      _ep => _em => _sh => hw => Eq.bit.absurd(&1, {D4.short.rows(T.VSpan{a1, a2} <> t) == True{} : Bool} ->
        {D1.own.rows(T.rows.seal(ee)) == D1.own.rows(mm) : List<&2, T.Val>} -> tp.ThenE(r0, he, cs, nn, hp,
          List.append(&2, T.Val, mm, D2.canon.go(T.VSpan{a1, a2} <> t, D2.CElems{hp})),
        rest, PP) -> PP(T.doc.read(String.append(T.render.pass(T.VSpan{a1, a2} <> t, "\n", True{}, True{}), rest),
          T.MScan{M3.dl(D1.tb.set(he, "", r0, T.VPair{nn, T.VAots{hp, ee}} <> cs), hs, cur, bk, qk, un, lf, ab)})), hw)
    case T.VInt{+a1, +a2} <> +t True{}:
      _ep => _em => _sh => hw => Eq.bit.absurd(&1, {D4.short.rows(T.VInt{a1, a2} <> t) == True{} : Bool} ->
        {D1.own.rows(T.rows.seal(ee)) == D1.own.rows(mm) : List<&2, T.Val>} -> tp.ThenE(r0, he, cs, nn, hp,
          List.append(&2, T.Val, mm, D2.canon.go(T.VInt{a1, a2} <> t, D2.CElems{hp})),
        rest, PP) -> PP(T.doc.read(String.append(T.render.pass(T.VInt{a1, a2} <> t, "\n", True{}, True{}), rest),
          T.MScan{M3.dl(D1.tb.set(he, "", r0, T.VPair{nn, T.VAots{hp, ee}} <> cs), hs, cur, bk, qk, un, lf, ab)})), hw)
    case T.VFlo{+a1, +a2} <> +t True{}:
      _ep => _em => _sh => hw => Eq.bit.absurd(&1, {D4.short.rows(T.VFlo{a1, a2} <> t) == True{} : Bool} ->
        {D1.own.rows(T.rows.seal(ee)) == D1.own.rows(mm) : List<&2, T.Val>} -> tp.ThenE(r0, he, cs, nn, hp,
          List.append(&2, T.Val, mm, D2.canon.go(T.VFlo{a1, a2} <> t, D2.CElems{hp})),
        rest, PP) -> PP(T.doc.read(String.append(T.render.pass(T.VFlo{a1, a2} <> t, "\n", True{}, True{}), rest),
          T.MScan{M3.dl(D1.tb.set(he, "", r0, T.VPair{nn, T.VAots{hp, ee}} <> cs), hs, cur, bk, qk, un, lf, ab)})), hw)
    case T.VBool{+a1} <> +t True{}:
      _ep => _em => _sh => hw => Eq.bit.absurd(&1, {D4.short.rows(T.VBool{a1} <> t) == True{} : Bool} ->
        {D1.own.rows(T.rows.seal(ee)) == D1.own.rows(mm) : List<&2, T.Val>} -> tp.ThenE(r0, he, cs, nn, hp,
          List.append(&2, T.Val, mm, D2.canon.go(T.VBool{a1} <> t, D2.CElems{hp})),
        rest, PP) -> PP(T.doc.read(String.append(T.render.pass(T.VBool{a1} <> t, "\n", True{}, True{}), rest),
          T.MScan{M3.dl(D1.tb.set(he, "", r0, T.VPair{nn, T.VAots{hp, ee}} <> cs), hs, cur, bk, qk, un, lf, ab)})), hw)
    case T.VWhen{+a1} <> +t True{}:
      _ep => _em => _sh => hw => Eq.bit.absurd(&1, {D4.short.rows(T.VWhen{a1} <> t) == True{} : Bool} ->
        {D1.own.rows(T.rows.seal(ee)) == D1.own.rows(mm) : List<&2, T.Val>} -> tp.ThenE(r0, he, cs, nn, hp,
          List.append(&2, T.Val, mm, D2.canon.go(T.VWhen{a1} <> t, D2.CElems{hp})),
        rest, PP) -> PP(T.doc.read(String.append(T.render.pass(T.VWhen{a1} <> t, "\n", True{}, True{}), rest),
          T.MScan{M3.dl(D1.tb.set(he, "", r0, T.VPair{nn, T.VAots{hp, ee}} <> cs), hs, cur, bk, qk, un, lf, ab)})), hw)
    case T.VArr{+a1} <> +t True{}:
      _ep => _em => _sh => hw => Eq.bit.absurd(&1, {D4.short.rows(T.VArr{a1} <> t) == True{} : Bool} ->
        {D1.own.rows(T.rows.seal(ee)) == D1.own.rows(mm) : List<&2, T.Val>} -> tp.ThenE(r0, he, cs, nn, hp,
          List.append(&2, T.Val, mm, D2.canon.go(T.VArr{a1} <> t, D2.CElems{hp})),
        rest, PP) -> PP(T.doc.read(String.append(T.render.pass(T.VArr{a1} <> t, "\n", True{}, True{}), rest),
          T.MScan{M3.dl(D1.tb.set(he, "", r0, T.VPair{nn, T.VAots{hp, ee}} <> cs), hs, cur, bk, qk, un, lf, ab)})), hw)
    case T.VInl{+a1} <> +t True{}:
      _ep => _em => _sh => hw => Eq.bit.absurd(&1, {D4.short.rows(T.VInl{a1} <> t) == True{} : Bool} ->
        {D1.own.rows(T.rows.seal(ee)) == D1.own.rows(mm) : List<&2, T.Val>} -> tp.ThenE(r0, he, cs, nn, hp,
          List.append(&2, T.Val, mm, D2.canon.go(T.VInl{a1} <> t, D2.CElems{hp})),
        rest, PP) -> PP(T.doc.read(String.append(T.render.pass(T.VInl{a1} <> t, "\n", True{}, True{}), rest),
          T.MScan{M3.dl(D1.tb.set(he, "", r0, T.VPair{nn, T.VAots{hp, ee}} <> cs), hs, cur, bk, qk, un, lf, ab)})), hw)
    case T.VHead{+a1, +a2} <> +t True{}:
      _ep => _em => _sh => hw => Eq.bit.absurd(&1, {D4.short.rows(T.VHead{a1, a2} <> t) == True{} : Bool} ->
        {D1.own.rows(T.rows.seal(ee)) == D1.own.rows(mm) : List<&2, T.Val>} -> tp.ThenE(r0, he, cs, nn, hp,
          List.append(&2, T.Val, mm, D2.canon.go(T.VHead{a1, a2} <> t, D2.CElems{hp})),
        rest, PP) -> PP(T.doc.read(String.append(T.render.pass(T.VHead{a1, a2} <> t, "\n", True{}, True{}), rest),
          T.MScan{M3.dl(D1.tb.set(he, "", r0, T.VPair{nn, T.VAots{hp, ee}} <> cs), hs, cur, bk, qk, un, lf, ab)})), hw)
    case T.VAots{+a1, +a2} <> +t True{}:
      _ep => _em => _sh => hw => Eq.bit.absurd(&1, {D4.short.rows(T.VAots{a1, a2} <> t) == True{} : Bool} ->
        {D1.own.rows(T.rows.seal(ee)) == D1.own.rows(mm) : List<&2, T.Val>} -> tp.ThenE(r0, he, cs, nn, hp,
          List.append(&2, T.Val, mm, D2.canon.go(T.VAots{a1, a2} <> t, D2.CElems{hp})),
        rest, PP) -> PP(T.doc.read(String.append(T.render.pass(T.VAots{a1, a2} <> t, "\n", True{}, True{}), rest),
          T.MScan{M3.dl(D1.tb.set(he, "", r0, T.VPair{nn, T.VAots{hp, ee}} <> cs), hs, cur, bk, qk, un, lf, ab)})), hw)
    case T.VPair{+a1, T.VStr{+b1}} <> +t True{}:
      _ep => _em => _sh => hw => Eq.bit.absurd(&1, {D4.short.rows(T.VPair{a1, T.VStr{b1}} <> t) == True{} : Bool} ->
        {D1.own.rows(T.rows.seal(ee)) == D1.own.rows(mm) : List<&2, T.Val>} -> tp.ThenE(r0, he, cs, nn, hp,
          List.append(&2, T.Val, mm, D2.canon.go(T.VPair{a1, T.VStr{b1}} <> t, D2.CElems{hp})),
        rest, PP) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{a1, T.VStr{b1}} <> t, "\n", True{}, True{}),
          rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, T.VPair{nn, T.VAots{hp, ee}} <> cs), hs, cur, bk, qk, un, lf,
          ab)})), hw)
    case T.VPair{+a1, T.VSpan{+b1, +b2}} <> +t True{}:
      _ep => _em => _sh => hw => Eq.bit.absurd(&1, {D4.short.rows(T.VPair{a1, T.VSpan{b1,
        b2}} <> t) == True{} : Bool} ->
        {D1.own.rows(T.rows.seal(ee)) == D1.own.rows(mm) : List<&2, T.Val>} -> tp.ThenE(r0, he, cs, nn, hp,
          List.append(&2, T.Val, mm, D2.canon.go(T.VPair{a1, T.VSpan{b1, b2}} <> t, D2.CElems{hp})),
        rest, PP) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{a1, T.VSpan{b1, b2}} <> t, "\n", True{}, True{}),
          rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, T.VPair{nn, T.VAots{hp, ee}} <> cs), hs, cur, bk, qk, un, lf,
          ab)})), hw)
    case T.VPair{+a1, T.VInt{+b1, +b2}} <> +t True{}:
      _ep => _em => _sh => hw => Eq.bit.absurd(&1, {D4.short.rows(T.VPair{a1, T.VInt{b1,
        b2}} <> t) == True{} : Bool} ->
        {D1.own.rows(T.rows.seal(ee)) == D1.own.rows(mm) : List<&2, T.Val>} -> tp.ThenE(r0, he, cs, nn, hp,
          List.append(&2, T.Val, mm, D2.canon.go(T.VPair{a1, T.VInt{b1, b2}} <> t, D2.CElems{hp})),
        rest, PP) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{a1, T.VInt{b1, b2}} <> t, "\n", True{}, True{}),
          rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, T.VPair{nn, T.VAots{hp, ee}} <> cs), hs, cur, bk, qk, un, lf,
          ab)})), hw)
    case T.VPair{+a1, T.VFlo{+b1, +b2}} <> +t True{}:
      _ep => _em => _sh => hw => Eq.bit.absurd(&1, {D4.short.rows(T.VPair{a1, T.VFlo{b1,
        b2}} <> t) == True{} : Bool} ->
        {D1.own.rows(T.rows.seal(ee)) == D1.own.rows(mm) : List<&2, T.Val>} -> tp.ThenE(r0, he, cs, nn, hp,
          List.append(&2, T.Val, mm, D2.canon.go(T.VPair{a1, T.VFlo{b1, b2}} <> t, D2.CElems{hp})),
        rest, PP) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{a1, T.VFlo{b1, b2}} <> t, "\n", True{}, True{}),
          rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, T.VPair{nn, T.VAots{hp, ee}} <> cs), hs, cur, bk, qk, un, lf,
          ab)})), hw)
    case T.VPair{+a1, T.VBool{+b1}} <> +t True{}:
      _ep => _em => _sh => hw => Eq.bit.absurd(&1, {D4.short.rows(T.VPair{a1, T.VBool{b1}} <> t) == True{} : Bool} ->
        {D1.own.rows(T.rows.seal(ee)) == D1.own.rows(mm) : List<&2, T.Val>} -> tp.ThenE(r0, he, cs, nn, hp,
          List.append(&2, T.Val, mm, D2.canon.go(T.VPair{a1, T.VBool{b1}} <> t, D2.CElems{hp})),
        rest, PP) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{a1, T.VBool{b1}} <> t, "\n", True{}, True{}),
          rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, T.VPair{nn, T.VAots{hp, ee}} <> cs), hs, cur, bk, qk, un, lf,
          ab)})), hw)
    case T.VPair{+a1, T.VWhen{+b1}} <> +t True{}:
      _ep => _em => _sh => hw => Eq.bit.absurd(&1, {D4.short.rows(T.VPair{a1, T.VWhen{b1}} <> t) == True{} : Bool} ->
        {D1.own.rows(T.rows.seal(ee)) == D1.own.rows(mm) : List<&2, T.Val>} -> tp.ThenE(r0, he, cs, nn, hp,
          List.append(&2, T.Val, mm, D2.canon.go(T.VPair{a1, T.VWhen{b1}} <> t, D2.CElems{hp})),
        rest, PP) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{a1, T.VWhen{b1}} <> t, "\n", True{}, True{}),
          rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, T.VPair{nn, T.VAots{hp, ee}} <> cs), hs, cur, bk, qk, un, lf,
          ab)})), hw)
    case T.VPair{+a1, T.VArr{+b1}} <> +t True{}:
      _ep => _em => _sh => hw => Eq.bit.absurd(&1, {D4.short.rows(T.VPair{a1, T.VArr{b1}} <> t) == True{} : Bool} ->
        {D1.own.rows(T.rows.seal(ee)) == D1.own.rows(mm) : List<&2, T.Val>} -> tp.ThenE(r0, he, cs, nn, hp,
          List.append(&2, T.Val, mm, D2.canon.go(T.VPair{a1, T.VArr{b1}} <> t, D2.CElems{hp})),
        rest, PP) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{a1, T.VArr{b1}} <> t, "\n", True{}, True{}),
          rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, T.VPair{nn, T.VAots{hp, ee}} <> cs), hs, cur, bk, qk, un, lf,
          ab)})), hw)
    case T.VPair{+a1, T.VInl{+b1}} <> +t True{}:
      _ep => _em => _sh => hw => Eq.bit.absurd(&1, {D4.short.rows(T.VPair{a1, T.VInl{b1}} <> t) == True{} : Bool} ->
        {D1.own.rows(T.rows.seal(ee)) == D1.own.rows(mm) : List<&2, T.Val>} -> tp.ThenE(r0, he, cs, nn, hp,
          List.append(&2, T.Val, mm, D2.canon.go(T.VPair{a1, T.VInl{b1}} <> t, D2.CElems{hp})),
        rest, PP) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{a1, T.VInl{b1}} <> t, "\n", True{}, True{}),
          rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, T.VPair{nn, T.VAots{hp, ee}} <> cs), hs, cur, bk, qk, un, lf,
          ab)})), hw)
    case T.VPair{+a1, T.VHead{+b1, +b2}} <> +t True{}:
      _ep => _em => _sh => hw => Eq.bit.absurd(&1, {D4.short.rows(T.VPair{a1, T.VHead{b1,
        b2}} <> t) == True{} : Bool} ->
        {D1.own.rows(T.rows.seal(ee)) == D1.own.rows(mm) : List<&2, T.Val>} -> tp.ThenE(r0, he, cs, nn, hp,
          List.append(&2, T.Val, mm, D2.canon.go(T.VPair{a1, T.VHead{b1, b2}} <> t, D2.CElems{hp})),
        rest, PP) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{a1, T.VHead{b1, b2}} <> t, "\n", True{}, True{}),
          rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, T.VPair{nn, T.VAots{hp, ee}} <> cs), hs, cur, bk, qk, un, lf,
          ab)})), hw)
    case T.VPair{+a1, T.VAot{+b1, +b2}} <> +t True{}:
      _ep => _em => _sh => hw => Eq.bit.absurd(&1, {D4.short.rows(T.VPair{a1, T.VAot{b1,
        b2}} <> t) == True{} : Bool} ->
        {D1.own.rows(T.rows.seal(ee)) == D1.own.rows(mm) : List<&2, T.Val>} -> tp.ThenE(r0, he, cs, nn, hp,
          List.append(&2, T.Val, mm, D2.canon.go(T.VPair{a1, T.VAot{b1, b2}} <> t, D2.CElems{hp})),
        rest, PP) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{a1, T.VAot{b1, b2}} <> t, "\n", True{}, True{}),
          rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, T.VPair{nn, T.VAots{hp, ee}} <> cs), hs, cur, bk, qk, un, lf,
          ab)})), hw)
    case T.VPair{+a1, T.VAots{+b1, +b2}} <> +t True{}:
      _ep => _em => _sh => hw => Eq.bit.absurd(&1, {D4.short.rows(T.VPair{a1, T.VAots{b1,
        b2}} <> t) == True{} : Bool} ->
        {D1.own.rows(T.rows.seal(ee)) == D1.own.rows(mm) : List<&2, T.Val>} -> tp.ThenE(r0, he, cs, nn, hp,
          List.append(&2, T.Val, mm, D2.canon.go(T.VPair{a1, T.VAots{b1, b2}} <> t, D2.CElems{hp})),
        rest, PP) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{a1, T.VAots{b1, b2}} <> t, "\n", True{}, True{}),
          rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, T.VPair{nn, T.VAots{hp, ee}} <> cs), hs, cur, bk, qk, un, lf,
          ab)})), hw)
    case T.VPair{+a1, T.VPair{+b1, +b2}} <> +t True{}:
      _ep => _em => _sh => hw => Eq.bit.absurd(&1, {D4.short.rows(T.VPair{a1, T.VPair{b1,
        b2}} <> t) == True{} : Bool} ->
        {D1.own.rows(T.rows.seal(ee)) == D1.own.rows(mm) : List<&2, T.Val>} -> tp.ThenE(r0, he, cs, nn, hp,
          List.append(&2, T.Val, mm, D2.canon.go(T.VPair{a1, T.VPair{b1, b2}} <> t, D2.CElems{hp})),
        rest, PP) -> PP(T.doc.read(String.append(T.render.pass(T.VPair{a1, T.VPair{b1, b2}} <> t, "\n", True{}, True{}),
          rest), T.MScan{M3.dl(D1.tb.set(he, "", r0, T.VPair{nn, T.VAots{hp, ee}} <> cs), hs, cur, bk, qk, un, lf,
          ab)})), hw)
