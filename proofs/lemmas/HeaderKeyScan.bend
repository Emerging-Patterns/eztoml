# the scanner reading a header's segments, bare or quoted, up to its brackets
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/KeyNameIsItsCharacters.bend as L1
import ../../laws/defs/BareValueGrammar.bend as D1
import ../../laws/defs/BlankAndControlChars.bend as D2
import ../../laws/defs/KeySegmentSpelling.bend as D3
import ./ControlEscapeText.bend as M1
import ./FreshNamesInRows.bend as M2
import ./HeaderSegmentWalk.bend as M3
import ./PickAndDigitSteps.bend as M4
import ./QuotedKeySegments.bend as M5
import ./ReorderedTableNames.bend as M6
import ./ValueTextReadback.bend as M7

# the scanner after a segment and what follows it: waiting for the next
# segment after a dot, or closed after the bracket
def wh.aft(
  cl: Bool,
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  parts: List<&2, String>,
  back: T.Lex,
  qkind: T.QKind,
  +arrtab: Bool
) -> T.St:
  match cl:
    case False{}:
      M3.wh.st(rows, heads, here, parts, [], T.LHeadDot{}, back, qkind, arrtab)
    case True{}:
      T.read.once2(T.lex.head.close2(arrtab, M3.wh.st(rows, heads, here, parts, [],
        T.LHeadGap{}, back, qkind, arrtab)))

# the bracket runs the header's walk along the segments read, and the newline
# returns to the start of a line in the header's table
def wh.fin(
  arrtab: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +path: List<&2, String>,
  +rows2: List<&2, T.Val>,
  +heads2: List<&2, String>,
  +rest: String,
  ne: {List.is_empty(&2, String, parts) == False{} : Bool},
  er: {List.reverse(&2, String, parts) == path : List<&2, String>},
  ew: M3.wh.Walk(arrtab, path, rows, heads, rows2, heads2)
) -> {T.doc.read(M3.wh.tail(arrtab, rest), T.MScan{wh.aft(True{}, rows, heads, here, parts, back,
  qkind, arrtab)}) == T.doc.read(rest, T.MScan{L1.hb.line(rows2, heads2, path, back, qkind,
  False{})}) : T.Doc}:
  match arrtab:
    case False{}:
      Equal.trans(T.Doc,
        T.doc.read(SCon{'\n', rest}, T.MScan{T.read.once2(T.head.go(List.is_empty(&2, String,
          parts), M3.wh.st(rows, heads, here, parts, [], T.LHeadGap{}, back, qkind, False{}),
          List.reverse(&2, String, parts)))}),
        T.doc.read(SCon{'\n', rest}, T.MScan{T.read.once2(T.head.apply(T.tree.walk(
          List.reverse(&2, String, parts), T.Tw{rows, T.JDef{}, [], "", "", heads, False{}}, 0),
          List.reverse(&2, String, parts), back, qkind, 0, 0, False{}))}),
        T.doc.read(rest, T.MScan{L1.hb.line(rows2, heads2, path, back, qkind, False{})}),
        Equal.cong(Bool, T.Doc, bt => T.doc.read(SCon{'\n', rest},
          T.MScan{T.read.once2(T.head.go(bt, M3.wh.st(rows, heads, here, parts, [], T.LHeadGap{},
          back, qkind, False{}), List.reverse(&2, String, parts)))}),
          List.is_empty(&2, String, parts), False{}, ne),
        Equal.trans(T.Doc,
          T.doc.read(SCon{'\n', rest}, T.MScan{T.read.once2(T.head.apply(T.tree.walk(
            List.reverse(&2, String, parts), T.Tw{rows, T.JDef{}, [], "", "", heads, False{}}, 0),
            List.reverse(&2, String, parts), back, qkind, 0, 0, False{}))}),
          T.doc.read(SCon{'\n', rest}, T.MScan{T.read.once2(T.head.apply(T.tree.walk(path,
            T.Tw{rows, T.JDef{}, [], "", "", heads, False{}}, 0), path, back, qkind, 0, 0,
            False{}))}),
          T.doc.read(rest, T.MScan{L1.hb.line(rows2, heads2, path, back, qkind, False{})}),
          Equal.cong(List<&2, String>, T.Doc, sg => T.doc.read(SCon{'\n', rest},
            T.MScan{T.read.once2(T.head.apply(T.tree.walk(sg, T.Tw{rows, T.JDef{}, [], "", "",
            heads, False{}}, 0), sg, back, qkind, 0, 0, False{}))}),
            List.reverse(&2, String, parts), path, er),
          Equal.cong(T.End, T.Doc, en => T.doc.read(SCon{'\n', rest},
            T.MScan{T.read.once2(T.head.apply(en, path, back, qkind, 0, 0, False{}))}),
            T.tree.walk(path, T.Tw{rows, T.JDef{}, [], "", "", heads, False{}}, 0),
            T.End{rows2, "", heads2}, ew)))
    case True{}:
      Equal.trans(T.Doc,
        T.doc.read(SCon{'\n', rest}, T.MScan{T.read.once2(T.head.go(List.is_empty(&2, String,
          parts), M3.wh.st(rows, heads, here, parts, [], T.LHeadR{}, back, qkind, True{}),
          List.reverse(&2, String, parts)))}),
        T.doc.read(SCon{'\n', rest}, T.MScan{T.read.once2(T.head.apply(T.tree.walk(
          List.reverse(&2, String, parts), T.Tw{rows, T.JAot{}, [], "", "", heads, False{}}, 0),
          List.reverse(&2, String, parts), back, qkind, 0, 0, False{}))}),
        T.doc.read(rest, T.MScan{L1.hb.line(rows2, heads2, path, back, qkind, False{})}),
        Equal.cong(Bool, T.Doc, bt => T.doc.read(SCon{'\n', rest},
          T.MScan{T.read.once2(T.head.go(bt, M3.wh.st(rows, heads, here, parts, [], T.LHeadR{},
          back, qkind, True{}), List.reverse(&2, String, parts)))}),
          List.is_empty(&2, String, parts), False{}, ne),
        Equal.trans(T.Doc,
          T.doc.read(SCon{'\n', rest}, T.MScan{T.read.once2(T.head.apply(T.tree.walk(
            List.reverse(&2, String, parts), T.Tw{rows, T.JAot{}, [], "", "", heads, False{}}, 0),
            List.reverse(&2, String, parts), back, qkind, 0, 0, False{}))}),
          T.doc.read(SCon{'\n', rest}, T.MScan{T.read.once2(T.head.apply(T.tree.walk(path,
            T.Tw{rows, T.JAot{}, [], "", "", heads, False{}}, 0), path, back, qkind, 0, 0,
            False{}))}),
          T.doc.read(rest, T.MScan{L1.hb.line(rows2, heads2, path, back, qkind, False{})}),
          Equal.cong(List<&2, String>, T.Doc, sg => T.doc.read(SCon{'\n', rest},
            T.MScan{T.read.once2(T.head.apply(T.tree.walk(sg, T.Tw{rows, T.JAot{}, [], "", "",
            heads, False{}}, 0), sg, back, qkind, 0, 0, False{}))}),
            List.reverse(&2, String, parts), path, er),
          Equal.cong(T.End, T.Doc, en => T.doc.read(SCon{'\n', rest},
            T.MScan{T.read.once2(T.head.apply(en, path, back, qkind, 0, 0, False{}))}),
            T.tree.walk(path, T.Tw{rows, T.JAot{}, [], "", "", heads, False{}}, 0),
            T.End{rows2, "", heads2}, ew)))

# a literal character is no apostrophe
def lit.q(
  q39: Bool,
  ctl: Bool,
  t9: Bool,
  e: {Bool.not(Bool.or(q39, Bool.and(ctl, Bool.not(t9)))) == True{} : Bool}
) -> {q39 == False{} : Bool}:
  match q39:
    case True{}:
      Eq.bit.absurd(&2, {True{} == False{} : Bool}, e)
    case False{}:
      {==}

# and a literal character that is no tab is no control
def lit.c(
  q39: Bool,
  ctl: Bool,
  t9: Bool,
  e9: {t9 == False{} : Bool},
  e: {Bool.not(Bool.or(q39, Bool.and(ctl, Bool.not(t9)))) == True{} : Bool}
) -> {ctl == False{} : Bool}:
  match q39:
    case True{}:
      Eq.bit.absurd(&2, {ctl == False{} : Bool}, e)
    case False{}:
      match ctl:
        case False{}:
          {==}
        case True{}:
          match t9:
            case True{}:
              Eq.bit.absurd2(&2, {True{} == False{} : Bool}, e9)
            case False{}:
              Eq.bit.absurd(&2, {True{} == False{} : Bool}, e)

# WP-K3: the whole key/value line. After `=`, " 1" and a newline read the
# value, and the newline that ends it runs the put's walk along the current
# table and the key's parts; the laws take that walk as a premise or, with
# dotted_put_at_head, discharge it.

# a list reversed twice is itself
def kv.rr(
  +xs: List<&2, String>
) -> {List.reverse(&2, String, List.reverse(&2, String, xs)) == xs : List<&2, String>}:
  Equal.trans(List<&2, String>,
    List.reverse.go(&2, String, List.reverse.go(&2, String, xs, []), []),
    List.append(&2, String, xs, []),
    xs,
    M3.wh.rr(xs, [], []),
    M3.wh.lnil(xs))

# KEY-3: a basic key segment read piece by piece. Every lemma takes the
# segment's state by the bit hd (a key's LKeyQ, or a header's LHeadQ, as
# WP0's qs does) with the stack, uni and left as parameters, since a key may
# sit in an inline table and a string before it may leave uni and left
# anywhere; each piece pushes the character it stands for, and the rest is
# read from whatever back, uni and left the piece leaves.

# a scanner inside a basic quoted segment, its characters so far reversed in
# buf
def k3.q(
  hd: Bool,
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
  T.St{"", rw, hs, he, ps, buf, M4.qs.lex(hd), bk, T.QBasic{}, sk, T.HNone{}, un, lf, ab, False{}}

# the rest of the text read from the segment with buf in its buffer, whatever
# back, uni and left are
def k3.Then(
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +buf: List<&2, Char>,
  +rest: String,
  +goal: T.Doc
) -> Type:
  @b2: T.Lex -> @u2: U32 -> @l2: U32 ->
    {T.doc.read(rest, T.MScan{k3.q(hd, rw, hs, he, ps, sk, ab, b2, u2, l2, buf)}) == goal : T.Doc}

# a two-character escape pushes the character it stands for and leaves back
# at the segment's state
def k3.esc(
  mm: D3.KMark,
  +hd: Bool,
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
  +goal: T.Doc,
  ih: k3.Then(hd, rw, hs, he, ps, sk, ab, D3.k3.mark.dec(mm) <> buf, rest, goal)
) -> {T.doc.read(SCon{'\\', SCon{D3.k3.mark.char(mm), rest}}, T.MScan{k3.q(hd, rw, hs, he, ps, sk, ab, bk, un,
  lf, buf)}) == goal : T.Doc}:
  match mm hd:
    case D3.KmQuote{} False{}:
      ih(T.LKeyQ{}, un, lf)
    case D3.KmQuote{} True{}:
      ih(T.LHeadQ{}, un, lf)
    case D3.KmBack{} False{}:
      ih(T.LKeyQ{}, un, lf)
    case D3.KmBack{} True{}:
      ih(T.LHeadQ{}, un, lf)
    case D3.KmB{} False{}:
      ih(T.LKeyQ{}, un, lf)
    case D3.KmB{} True{}:
      ih(T.LHeadQ{}, un, lf)
    case D3.KmF{} False{}:
      ih(T.LKeyQ{}, un, lf)
    case D3.KmF{} True{}:
      ih(T.LHeadQ{}, un, lf)
    case D3.KmN{} False{}:
      ih(T.LKeyQ{}, un, lf)
    case D3.KmN{} True{}:
      ih(T.LHeadQ{}, un, lf)
    case D3.KmR{} False{}:
      ih(T.LKeyQ{}, un, lf)
    case D3.KmR{} True{}:
      ih(T.LHeadQ{}, un, lf)
    case D3.KmT{} False{}:
      ih(T.LKeyQ{}, un, lf)
    case D3.KmT{} True{}:
      ih(T.LHeadQ{}, un, lf)

# a raw tab is pushed as itself
def k3.tab(
  +hd: Bool,
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
  +goal: T.Doc,
  ih: k3.Then(hd, rw, hs, he, ps, sk, ab, Chr{9} <> buf, rest, goal)
) -> {T.doc.read(SCon{Chr{9}, rest}, T.MScan{k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)}) == goal
  : T.Doc}:
  match hd:
    case False{}:
      ih(bk, un, lf)
    case True{}:
      ih(bk, un, lf)

# the fast step of a character in the segment is the segment's full step
def k3.fast(
  +uu: U32,
  +hd: Bool,
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
) -> {T.read.fast(k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu}) == T.read.once2(T.lex.kq.go(
  U32.is_eq(uu, 34), U32.is_eq(uu, 92), True{}, Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)), k3.q(hd, rw, hs, he, ps,
  sk, ab, bk, un, lf, buf), Chr{uu}, M5.qs.close(hd), M4.qs.lex(hd))) : T.St}:
  match hd:
    case False{}:
      {==}
    case True{}:
      {==}

# the segment's state is no quote that opens a string
def k3.wrap(
  +hd: Bool,
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
) -> {T.MScan{k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)} == T.doc.wrap(k3.q(hd, rw, hs, he, ps, sk, ab, bk,
  un, lf, buf)) : T.Mode}:
  match hd:
    case False{}:
      {==}
    case True{}:
      {==}

# a character that is no control is pushed: str.bad passes it
def k3.char(
  ctl: Bool,
  +uu: U32,
  +hd: Bool,
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
  False{}), k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu}, M4.qs.lex(hd)))
  == k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf) : T.St}:
  match ctl:
    case False{}:
      match hd:
        case False{}:
          {==}
        case True{}:
          {==}
    case True{}:
      Eq.bit.absurd2(&2, {T.read.once2(T.lex.kq.char.go(T.str.bad.go(True{}, U32.is_eq(uu, 9),
        Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)), False{}), k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf),
        Chr{uu}, M4.qs.lex(hd))) == k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf) : T.St}, hc)

# a character that is no quote, no backslash and no newline is no closer and
# no escape
def k3.go(
  quote: Bool,
  bs: Bool,
  nl: Bool,
  +uu: U32,
  +hd: Bool,
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
) -> {T.read.once2(T.lex.kq.go(quote, bs, True{}, nl, k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu},
  M5.qs.close(hd), M4.qs.lex(hd))) == k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf) : T.St}:
  match quote bs nl:
    case False{} False{} False{}:
      k3.char(Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), uu, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, hc)
    case True{} bb nn:
      Eq.bit.absurd2(&2, {T.read.once2(T.lex.kq.go(True{}, bb, True{}, nn, k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf,
        buf), Chr{uu}, M5.qs.close(hd), M4.qs.lex(hd))) == k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf)
        : T.St}, hq)
    case False{} True{} nn:
      Eq.bit.absurd2(&2, {T.read.once2(T.lex.kq.go(False{}, True{}, True{}, nn, k3.q(hd, rw, hs, he, ps, sk, ab, bk, un,
        lf, buf), Chr{uu}, M5.qs.close(hd), M4.qs.lex(hd))) == k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf,
            Chr{uu} <> buf)
        : T.St}, hb)
    case False{} False{} True{}:
      Eq.bit.absurd2(&2, {T.read.once2(T.lex.kq.go(False{}, False{}, True{}, True{}, k3.q(hd, rw, hs, he, ps, sk, ab,
        bk,
        un, lf, buf), Chr{uu}, M5.qs.close(hd), M4.qs.lex(hd))) == k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf,
        Chr{uu} <> buf) : T.St}, hn)

# the fast step pushes a character
def k3.Fast(
  +uu: U32,
  +hd: Bool,
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
  {k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf)
    == T.read.fast(k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu}) : T.St}

# the scan mode sends such a character to the fast step, and an apostrophe
# comes back from doc.wrap in the segment's state
def k3.scq(
  dq: Bool,
  sq: Bool,
  cr: Bool,
  +uu: U32,
  +hd: Bool,
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
  fast: k3.Fast(uu, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)
) -> {T.MScan{k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf)}
  == T.doc.scan.q(dq, sq, cr, k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu}) : T.Mode}:
  match dq sq cr:
    case True{} s2 c2:
      Eq.bit.absurd2(&2, {T.MScan{k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf)}
        == T.doc.scan.q(True{}, s2, c2, k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu}) : T.Mode}, hq)
    case False{} True{} _c:
      %fast : {T.MScan{k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf)} == T.doc.wrap(_) : T.Mode}
      k3.wrap(hd, rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf)
    case False{} False{} True{}:
      Eq.bit.absurd2(&2, {T.MScan{k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf)}
        == T.doc.scan.q(False{}, False{}, True{}, k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu})
        : T.Mode}, hr)
    case False{} False{} False{}:
      %fast : {T.MScan{k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf)} == T.MScan{_} : T.Mode}
      {==}

# a character written as itself that is no quote, no backslash and no
# control is pushed, and back, uni and left stay
def k3.plain(
  +uu: U32,
  +hd: Bool,
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
  +goal: T.Doc,
  +e34: {U32.is_eq(uu, 34) == False{} : Bool},
  +e92: {U32.is_eq(uu, 92) == False{} : Bool},
  +ec: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool},
  ih: k3.Then(hd, rw, hs, he, ps, sk, ab, Chr{uu} <> buf, rest, goal)
) -> {T.doc.read(SCon{Chr{uu}, rest}, T.MScan{k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)}) == goal : T.Doc}:
  +e10 = {M1.ctl.off(uu, 10, ec, {==}) : {U32.is_eq(uu, 10) == False{} : Bool}}
  +e13 = {M1.ctl.off(uu, 13, ec, {==}) : {U32.is_eq(uu, 13) == False{} : Bool}}
  fast = {Equal.sym(T.St, T.read.fast(k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu}),
    k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf),
    Equal.trans(T.St, T.read.fast(k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu}),
    T.read.once2(T.lex.kq.go(U32.is_eq(uu, 34), U32.is_eq(uu, 92), True{}, Bool.or(U32.is_eq(uu, 10),
    U32.is_eq(uu, 13)), k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu}, M5.qs.close(hd), M4.qs.lex(hd))),
    k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf),
    k3.fast(uu, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf),
    k3.go(U32.is_eq(uu, 34), U32.is_eq(uu, 92), Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)), uu, hd, rw, hs, he,
      ps, sk, ab, bk, un, lf, buf, e34, e92, M7.or.ff(U32.is_eq(uu, 10), U32.is_eq(uu, 13), e10, e13), ec)))
    : k3.Fast(uu, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)}
  %k3.scq(U32.is_eq(uu, 34), U32.is_eq(uu, 39), U32.is_eq(uu, 13), uu, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf,
    e34, e13, fast) : {T.doc.read(rest, _) == goal : T.Doc}
  ih(bk, un, lf)

# KEY-3: a \u or \U escape's digits, read for every digit at once. dig.val
# is computed on a digit's character alone (k3.hx.dv, k3.hx.ok, one case per
# digit), and the number read so far and the digits left stay symbolic, so
# every code point goes through the same few lemmas.

# the state that reads an escape's hexadecimal digits: a key's LKeyU, or a
# header's LHeadU
def k3.ulex(hd: Bool) -> T.Lex:
  match hd:
    case False{}:
      T.LKeyU{}
    case True{}:
      T.LHeadU{}

# a scanner reading an escape's digits: the number read so far in uni, the
# digits still to read in left
def k3.u(
  hd: Bool,
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
  T.St{"", rw, hs, he, ps, buf, k3.ulex(hd), bk, T.QBasic{}, sk, T.HNone{}, un, lf, ab, False{}}

# a digit that is not the last one: it joins the number, and one digit fewer
# is left
def k3.hx.mid(
  +hx: D3.KHex,
  +hd: Bool,
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
  el: {U32.is_eq(lf, 1) == False{} : Bool}
) -> {k3.u(hd, rw, hs, he, ps, sk, ab, bk, D3.k3.hex.acc(un, hx), U32.sub(lf, 1), buf)
  == T.read.fast(k3.u(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf), D3.k3.hex.char(hx)) : T.St}:
  match hd:
    case False{}:
      %M7.k3.hx.ok(hx) : {k3.u(False{}, rw, hs, he, ps, sk, ab, bk, D3.k3.hex.acc(un, hx), U32.sub(lf, 1), buf)
        == T.read.once2(T.uni.go(_, k3.u(False{}, rw, hs, he, ps, sk, ab, bk, un, lf, buf), D3.k3.hex.char(hx),
        T.LKeyQ{}, un, lf)) : T.St}
      %M7.k3.hx.dv(hx) : {k3.u(False{}, rw, hs, he, ps, sk, ab, bk, D3.k3.hex.acc(un, hx), U32.sub(lf, 1), buf)
        == T.read.once2(T.uni.next(U32.is_eq(lf, 1), k3.u(False{}, rw, hs, he, ps, sk, ab, bk, un, lf, buf),
        U32.add(U32.mul(un, 16), _), T.LKeyQ{}, lf)) : T.St}
      %Equal.sym(Bool, U32.is_eq(lf, 1), False{}, el) : {k3.u(False{}, rw, hs, he, ps, sk, ab, bk,
        D3.k3.hex.acc(un, hx), U32.sub(lf, 1), buf) == T.read.once2(T.uni.next(_, k3.u(False{}, rw, hs, he, ps,
        sk, ab, bk, un, lf, buf), D3.k3.hex.acc(un, hx), T.LKeyQ{}, lf)) : T.St}
      {==}
    case True{}:
      %M7.k3.hx.ok(hx) : {k3.u(True{}, rw, hs, he, ps, sk, ab, bk, D3.k3.hex.acc(un, hx), U32.sub(lf, 1), buf)
        == T.read.once2(T.uni.go(_, k3.u(True{}, rw, hs, he, ps, sk, ab, bk, un, lf, buf), D3.k3.hex.char(hx),
        T.LHeadQ{}, un, lf)) : T.St}
      %M7.k3.hx.dv(hx) : {k3.u(True{}, rw, hs, he, ps, sk, ab, bk, D3.k3.hex.acc(un, hx), U32.sub(lf, 1), buf)
        == T.read.once2(T.uni.next(U32.is_eq(lf, 1), k3.u(True{}, rw, hs, he, ps, sk, ab, bk, un, lf, buf),
        U32.add(U32.mul(un, 16), _), T.LHeadQ{}, lf)) : T.St}
      %Equal.sym(Bool, U32.is_eq(lf, 1), False{}, el) : {k3.u(True{}, rw, hs, he, ps, sk, ab, bk,
        D3.k3.hex.acc(un, hx), U32.sub(lf, 1), buf) == T.read.once2(T.uni.next(_, k3.u(True{}, rw, hs, he, ps,
        sk, ab, bk, un, lf, buf), D3.k3.hex.acc(un, hx), T.LHeadQ{}, lf)) : T.St}
      {==}

# the last digit: the number is a Unicode scalar value, pushed as the
# character, and the segment's state is back with uni and left at 0
def k3.hx.last(
  +hx: D3.KHex,
  +hd: Bool,
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
  el: {U32.is_eq(lf, 1) == True{} : Bool},
  eo: {D3.k3.scalar(D3.k3.hex.acc(un, hx)) == True{} : Bool}
) -> {k3.q(hd, rw, hs, he, ps, sk, ab, bk, 0, 0, Chr{D3.k3.hex.acc(un, hx)} <> buf)
  == T.read.fast(k3.u(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf), D3.k3.hex.char(hx)) : T.St}:
  match hd:
    case False{}:
      %M7.k3.hx.ok(hx) : {k3.q(False{}, rw, hs, he, ps, sk, ab, bk, 0, 0, Chr{D3.k3.hex.acc(un, hx)} <> buf)
        == T.read.once2(T.uni.go(_, k3.u(False{}, rw, hs, he, ps, sk, ab, bk, un, lf, buf), D3.k3.hex.char(hx),
        T.LKeyQ{}, un, lf)) : T.St}
      %M7.k3.hx.dv(hx) : {k3.q(False{}, rw, hs, he, ps, sk, ab, bk, 0, 0, Chr{D3.k3.hex.acc(un, hx)} <> buf)
        == T.read.once2(T.uni.next(U32.is_eq(lf, 1), k3.u(False{}, rw, hs, he, ps, sk, ab, bk, un, lf, buf),
        U32.add(U32.mul(un, 16), _), T.LKeyQ{}, lf)) : T.St}
      %Equal.sym(Bool, U32.is_eq(lf, 1), True{}, el) : {k3.q(False{}, rw, hs, he, ps, sk, ab, bk, 0, 0,
        Chr{D3.k3.hex.acc(un, hx)} <> buf) == T.read.once2(T.uni.next(_, k3.u(False{}, rw, hs, he, ps, sk, ab, bk,
        un, lf, buf), D3.k3.hex.acc(un, hx), T.LKeyQ{}, lf)) : T.St}
      %Equal.sym(Bool, T.uni.ok(D3.k3.hex.acc(un, hx)), True{}, eo) : {k3.q(False{}, rw, hs, he, ps, sk, ab, bk,
        0, 0, Chr{D3.k3.hex.acc(un, hx)} <> buf) == T.read.once2(T.uni.finish(_, k3.u(False{}, rw, hs, he, ps, sk,
        ab, bk, un, lf, buf), D3.k3.hex.acc(un, hx), T.LKeyQ{})) : T.St}
      {==}
    case True{}:
      %M7.k3.hx.ok(hx) : {k3.q(True{}, rw, hs, he, ps, sk, ab, bk, 0, 0, Chr{D3.k3.hex.acc(un, hx)} <> buf)
        == T.read.once2(T.uni.go(_, k3.u(True{}, rw, hs, he, ps, sk, ab, bk, un, lf, buf), D3.k3.hex.char(hx),
        T.LHeadQ{}, un, lf)) : T.St}
      %M7.k3.hx.dv(hx) : {k3.q(True{}, rw, hs, he, ps, sk, ab, bk, 0, 0, Chr{D3.k3.hex.acc(un, hx)} <> buf)
        == T.read.once2(T.uni.next(U32.is_eq(lf, 1), k3.u(True{}, rw, hs, he, ps, sk, ab, bk, un, lf, buf),
        U32.add(U32.mul(un, 16), _), T.LHeadQ{}, lf)) : T.St}
      %Equal.sym(Bool, U32.is_eq(lf, 1), True{}, el) : {k3.q(True{}, rw, hs, he, ps, sk, ab, bk, 0, 0,
        Chr{D3.k3.hex.acc(un, hx)} <> buf) == T.read.once2(T.uni.next(_, k3.u(True{}, rw, hs, he, ps, sk, ab, bk,
        un, lf, buf), D3.k3.hex.acc(un, hx), T.LHeadQ{}, lf)) : T.St}
      %Equal.sym(Bool, T.uni.ok(D3.k3.hex.acc(un, hx)), True{}, eo) : {k3.q(True{}, rw, hs, he, ps, sk, ab, bk,
        0, 0, Chr{D3.k3.hex.acc(un, hx)} <> buf) == T.read.once2(T.uni.finish(_, k3.u(True{}, rw, hs, he, ps, sk,
        ab, bk, un, lf, buf), D3.k3.hex.acc(un, hx), T.LHeadQ{})) : T.St}
      {==}

# a digit that is not the last one, read from the text
def k3.hx.rmid(
  +hx: D3.KHex,
  +hd: Bool,
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
  el: {U32.is_eq(lf, 1) == False{} : Bool}
) -> {T.doc.read(rest, T.MScan{k3.u(hd, rw, hs, he, ps, sk, ab, bk, D3.k3.hex.acc(un, hx), U32.sub(lf, 1), buf)})
  == T.doc.read(SCon{D3.k3.hex.char(hx), rest}, T.MScan{k3.u(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)})
  : T.Doc}:
  %M7.k3.hx.scan(hx, k3.u(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)) : {T.doc.read(rest, T.MScan{k3.u(hd, rw, hs, he,
    ps, sk, ab, bk, D3.k3.hex.acc(un, hx), U32.sub(lf, 1), buf)}) == T.doc.read(rest, _) : T.Doc}
  %k3.hx.mid(hx, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, el) : {T.doc.read(rest, T.MScan{k3.u(hd, rw, hs, he,
    ps, sk, ab, bk, D3.k3.hex.acc(un, hx), U32.sub(lf, 1), buf)}) == T.doc.read(rest, T.MScan{_}) : T.Doc}
  {==}

# the last digit, read from the text
def k3.hx.rlast(
  +hx: D3.KHex,
  +hd: Bool,
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
  el: {U32.is_eq(lf, 1) == True{} : Bool},
  eo: {D3.k3.scalar(D3.k3.hex.acc(un, hx)) == True{} : Bool}
) -> {T.doc.read(rest, T.MScan{k3.q(hd, rw, hs, he, ps, sk, ab, bk, 0, 0, Chr{D3.k3.hex.acc(un, hx)} <> buf)})
  == T.doc.read(SCon{D3.k3.hex.char(hx), rest}, T.MScan{k3.u(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)})
  : T.Doc}:
  %M7.k3.hx.scan(hx, k3.u(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)) : {T.doc.read(rest, T.MScan{k3.q(hd, rw, hs, he,
    ps, sk, ab, bk, 0, 0, Chr{D3.k3.hex.acc(un, hx)} <> buf)}) == T.doc.read(rest, _) : T.Doc}
  %k3.hx.last(hx, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, el, eo) : {T.doc.read(rest, T.MScan{k3.q(hd, rw, hs,
    he, ps, sk, ab, bk, 0, 0, Chr{D3.k3.hex.acc(un, hx)} <> buf)}) == T.doc.read(rest, T.MScan{_}) : T.Doc}
  {==}

# a backslash and u (U when lg) start an escape of four digits (eight),
# with back at the segment's state
def k3.hx.open(
  +lg: Bool,
  +hd: Bool,
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
  +rest: String
) -> {T.doc.read(rest, T.MScan{k3.u(hd, rw, hs, he, ps, sk, ab, M4.qs.lex(hd), 0, M7.k3.hx.n(lg), buf)})
  == T.doc.read(SCon{'\\', SCon{M7.k3.hx.u(lg), rest}}, T.MScan{k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)})
  : T.Doc}:
  match lg:
    case False{}:
      match hd:
        case False{}:
          {==}
        case True{}:
          {==}
    case True{}:
      match hd:
        case False{}:
          {==}
        case True{}:
          {==}

# `\u` and four digits push the character they name, and leave back at the
# segment's state and uni and left at 0
def k3.u4(
  +dd: D3.KHex,
  +cc: D3.KHex,
  +bb: D3.KHex,
  +aa: D3.KHex,
  +hd: Bool,
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
  +goal: T.Doc,
  eo: {D3.k3.scalar(D3.k3.hex4(dd, cc, bb, aa)) == True{} : Bool},
  ih: k3.Then(hd, rw, hs, he, ps, sk, ab, Chr{D3.k3.hex4(dd, cc, bb, aa)} <> buf, rest, goal)
) -> {T.doc.read(D3.k3.pc.text(D3.KpU4{dd, cc, bb, aa}, rest), T.MScan{k3.q(hd, rw, hs, he, ps, sk, ab, bk, un,
  lf, buf)}) == goal : T.Doc}:
  %k3.hx.open(False{}, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, D3.k3.hex4.text(dd, cc, bb, aa, rest))
    : {_ == goal : T.Doc}
  %k3.hx.rmid(dd, hd, rw, hs, he, ps, sk, ab, M4.qs.lex(hd), 0, 4, buf, SCon{D3.k3.hex.char(cc),
    SCon{D3.k3.hex.char(bb), SCon{D3.k3.hex.char(aa), rest}}}, {==}) : {_ == goal : T.Doc}
  %k3.hx.rmid(cc, hd, rw, hs, he, ps, sk, ab, M4.qs.lex(hd), D3.k3.hex.acc(0, dd), 3, buf,
    SCon{D3.k3.hex.char(bb), SCon{D3.k3.hex.char(aa), rest}}, {==}) : {_ == goal : T.Doc}
  %k3.hx.rmid(bb, hd, rw, hs, he, ps, sk, ab, M4.qs.lex(hd), D3.k3.hex.acc(D3.k3.hex.acc(0, dd), cc), 2, buf,
    SCon{D3.k3.hex.char(aa), rest}, {==}) : {_ == goal : T.Doc}
  %k3.hx.rlast(aa, hd, rw, hs, he, ps, sk, ab, M4.qs.lex(hd), D3.k3.hex.acc(D3.k3.hex.acc(D3.k3.hex.acc(0, dd),
    cc), bb), 1, buf, rest, {==}, eo) : {_ == goal : T.Doc}
  ih(M4.qs.lex(hd), 0, 0)

# `\U` and eight digits push the character they name, and leave back at the
# segment's state and uni and left at 0
def k3.u8(
  +hh: D3.KHex,
  +gg: D3.KHex,
  +ff: D3.KHex,
  +ee: D3.KHex,
  +dd: D3.KHex,
  +cc: D3.KHex,
  +bb: D3.KHex,
  +aa: D3.KHex,
  +hd: Bool,
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
  +goal: T.Doc,
  eo: {D3.k3.scalar(D3.k3.hex8(hh, gg, ff, ee, dd, cc, bb, aa)) == True{} : Bool},
  ih: k3.Then(hd, rw, hs, he, ps, sk, ab, Chr{D3.k3.hex8(hh, gg, ff, ee, dd, cc, bb, aa)} <> buf, rest, goal)
) -> {T.doc.read(D3.k3.pc.text(D3.KpU8{hh, gg, ff, ee, dd, cc, bb, aa}, rest), T.MScan{k3.q(hd, rw, hs, he, ps,
  sk, ab, bk, un, lf, buf)}) == goal : T.Doc}:
  +t4 = D3.k3.hex4.text(dd, cc, bb, aa, rest)
  +a1 = D3.k3.hex.acc(0, hh)
  +a2 = D3.k3.hex.acc(a1, gg)
  +a3 = D3.k3.hex.acc(a2, ff)
  +a4 = D3.k3.hex.acc(a3, ee)
  +a5 = D3.k3.hex.acc(a4, dd)
  +a6 = D3.k3.hex.acc(a5, cc)
  +a7 = D3.k3.hex.acc(a6, bb)
  +sl = M4.qs.lex(hd)
  %k3.hx.open(True{}, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, D3.k3.hex4.text(hh, gg, ff, ee, t4))
    : {_ == goal : T.Doc}
  %k3.hx.rmid(hh, hd, rw, hs, he, ps, sk, ab, sl, 0, 8, buf, SCon{D3.k3.hex.char(gg), SCon{D3.k3.hex.char(ff),
    SCon{D3.k3.hex.char(ee), t4}}}, {==}) : {_ == goal : T.Doc}
  %k3.hx.rmid(gg, hd, rw, hs, he, ps, sk, ab, sl, a1, 7, buf, SCon{D3.k3.hex.char(ff), SCon{D3.k3.hex.char(ee),
    t4}}, {==}) : {_ == goal : T.Doc}
  %k3.hx.rmid(ff, hd, rw, hs, he, ps, sk, ab, sl, a2, 6, buf, SCon{D3.k3.hex.char(ee), t4}, {==})
    : {_ == goal : T.Doc}
  %k3.hx.rmid(ee, hd, rw, hs, he, ps, sk, ab, sl, a3, 5, buf, t4, {==}) : {_ == goal : T.Doc}
  %k3.hx.rmid(dd, hd, rw, hs, he, ps, sk, ab, sl, a4, 4, buf, SCon{D3.k3.hex.char(cc),
    SCon{D3.k3.hex.char(bb), SCon{D3.k3.hex.char(aa), rest}}}, {==}) : {_ == goal : T.Doc}
  %k3.hx.rmid(cc, hd, rw, hs, he, ps, sk, ab, sl, a5, 3, buf, SCon{D3.k3.hex.char(bb), SCon{D3.k3.hex.char(aa),
    rest}}, {==}) : {_ == goal : T.Doc}
  %k3.hx.rmid(bb, hd, rw, hs, he, ps, sk, ab, sl, a6, 2, buf, SCon{D3.k3.hex.char(aa), rest}, {==})
    : {_ == goal : T.Doc}
  %k3.hx.rlast(aa, hd, rw, hs, he, ps, sk, ab, sl, a7, 1, buf, rest, {==}, eo) : {_ == goal : T.Doc}
  ih(sl, 0, 0)

# a character written as itself read from the segment, then the rest
def k3.PcG(
  +cc: Char,
  +hd: Bool,
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
  +goal: T.Doc
) -> Type:
  k3.Then(hd, rw, hs, he, ps, sk, ab, cc <> buf, rest, goal) ->
    {T.doc.read(SCon{cc, rest}, T.MScan{k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)}) == goal : T.Doc}

# basic-unescaped is no quotation mark
def k3.bc.q(
  aa: Bool,
  bb: Bool,
  cc: Bool,
  dd: Bool,
  ee: {Bool.not(Bool.or(aa, Bool.or(bb, Bool.and(cc, Bool.not(dd))))) == True{} : Bool}
) -> {aa == False{} : Bool}:
  match aa:
    case True{}:
      Eq.bit.absurd(&2, {True{} == False{} : Bool}, ee)
    case False{}:
      {==}

# no backslash
def k3.bc.b(
  aa: Bool,
  bb: Bool,
  cc: Bool,
  dd: Bool,
  ee: {Bool.not(Bool.or(aa, Bool.or(bb, Bool.and(cc, Bool.not(dd))))) == True{} : Bool}
) -> {bb == False{} : Bool}:
  match aa bb:
    case True{} b2:
      Eq.bit.absurd(&2, {b2 == False{} : Bool}, ee)
    case False{} True{}:
      Eq.bit.absurd(&2, {True{} == False{} : Bool}, ee)
    case False{} False{}:
      {==}

# and, when it is no tab, no control
def k3.bc.c(
  aa: Bool,
  bb: Bool,
  cc: Bool,
  dd: Bool,
  e9: {dd == False{} : Bool},
  ee: {Bool.not(Bool.or(aa, Bool.or(bb, Bool.and(cc, Bool.not(dd))))) == True{} : Bool}
) -> {cc == False{} : Bool}:
  match aa bb cc dd:
    case True{} b2 c2 d2:
      Eq.bit.absurd(&2, {c2 == False{} : Bool}, ee)
    case False{} True{} c2 d2:
      Eq.bit.absurd(&2, {c2 == False{} : Bool}, ee)
    case False{} False{} False{} d2:
      {==}
    case False{} False{} True{} True{}:
      Eq.bit.absurd2(&2, {True{} == False{} : Bool}, e9)
    case False{} False{} True{} False{}:
      Eq.bit.absurd(&2, {True{} == False{} : Bool}, ee)

# a character written as itself: a tab, or one that is no quote, no
# backslash and no control
def k3.chr(
  t9: Bool,
  +uu: U32,
  +e9: {U32.is_eq(uu, 9) == t9 : Bool},
  +hd: Bool,
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
  +goal: T.Doc,
  +eb: {L1.k3.bchar(Chr{uu}) == True{} : Bool}
) -> k3.PcG(Chr{uu}, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, goal):
  match t9:
    case True{}:
      %Equal.sym(Char, Chr{uu}, Chr{9}, Eq.u32_eq(uu, 9, e9)) : k3.PcG(_, hd, rw, hs, he, ps, sk, ab, bk, un, lf,
        buf, rest, goal)
      ih => k3.tab(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, goal, ih)
    case False{}:
      +tq = U32.is_eq(uu, 34)
      +tb = U32.is_eq(uu, 92)
      +tc = Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127))
      +tt = U32.is_eq(uu, 9)
      ih => k3.plain(uu, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, goal, k3.bc.q(tq, tb, tc, tt, eb),
        k3.bc.b(tq, tb, tc, tt, eb), k3.bc.c(tq, tb, tc, tt, e9, eb), ih)

# one piece a basic string may hold pushes the character it stands for
def k3.pc(
  pp: D3.KPiece,
  +hd: Bool,
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
  +goal: T.Doc,
  eo: {L1.k3.pc.ok(pp) == True{} : Bool},
  ih: k3.Then(hd, rw, hs, he, ps, sk, ab, D3.k3.pc.char(pp) <> buf, rest, goal)
) -> {T.doc.read(D3.k3.pc.text(pp, rest), T.MScan{k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)}) == goal
  : T.Doc}:
  match pp:
    case D3.KpChar{cc}:
      match cc:
        case Chr{+uu}:
          k3.chr(U32.is_eq(uu, 9), uu, {==}, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, goal, eo)(ih)
    case D3.KpEsc{mm}:
      k3.esc(mm, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, goal, ih)
    case D3.KpU4{+dd, +cc, +bb, +aa}:
      k3.u4(dd, cc, bb, aa, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, goal, eo, ih)
    case D3.KpU8{+hh, +gg, +ff, +ee, +dd, +cc, +bb, +aa}:
      k3.u8(hh, gg, ff, ee, dd, cc, bb, aa, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, goal, eo, ih)

# every piece of a list a basic string may hold, in order: the rest is read
# with their characters pushed, from wherever the last piece left back, uni
# and left
def k3.pcs(
  pl: List<&2, D3.KPiece>,
  +hd: Bool,
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
  +goal: T.Doc,
  +eo: {L1.k3.pcs.ok(pl) == True{} : Bool},
  ih: k3.Then(hd, rw, hs, he, ps, sk, ab, M2.rev.onto(D3.k3.pcs.name(pl), buf), rest, goal)
) -> {T.doc.read(D3.k3.pcs.text(pl, rest), T.MScan{k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)}) == goal
  : T.Doc}:
  match pl:
    case []:
      ih(bk, un, lf)
    case +pp <> +pr:
      k3.pc(pp, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, D3.k3.pcs.text(pr, rest), goal,
        Eq.and.left(L1.k3.pc.ok(pp), L1.k3.pcs.ok(pr), eo),
        +b2 => +u2 => +l2 => k3.pcs(pr, hd, rw, hs, he, ps, sk, ab, b2, u2, l2, D3.k3.pc.char(pp) <> buf, rest,
          goal, Eq.and.right(L1.k3.pc.ok(pp), L1.k3.pcs.ok(pr), eo), ih))

# KEY-3: a literal segment, as WP-K3's ql reads it, with the stack, uni and
# left as parameters: every character but the apostrophe is pushed as it is,
# and back, uni and left never move.

# a scanner inside a literal quoted segment, its characters so far reversed
# in buf
def k3.l(
  hd: Bool,
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
  T.St{"", rw, hs, he, ps, buf, M4.qs.lex(hd), bk, T.QLit{}, sk, T.HNone{}, un, lf, ab, False{}}

# a character read from a literal segment is pushed
def k3.l.Step(
  +uu: U32,
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>
) -> Type:
  {T.doc.scan(k3.l(hd, rw, hs, he, ps, sk, ab, back, un, lf, buf), Chr{uu})
    == T.MScan{k3.l(hd, rw, hs, he, ps, sk, ab, back, un, lf, Chr{uu} <> buf)} : T.Mode}

# a quotation mark, a backslash and a tab: their steps compute
def k3.l.s34(
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>
) -> k3.l.Step(34, hd, rw, hs, he, ps, sk, ab, back, un, lf, buf):
  match hd:
    case False{}:
      {==}
    case True{}:
      {==}

# a backslash
def k3.l.s92(
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>
) -> k3.l.Step(92, hd, rw, hs, he, ps, sk, ab, back, un, lf, buf):
  match hd:
    case False{}:
      {==}
    case True{}:
      {==}

# a tab
def k3.l.s9(
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>
) -> k3.l.Step(9, hd, rw, hs, he, ps, sk, ab, back, un, lf, buf):
  match hd:
    case False{}:
      {==}
    case True{}:
      {==}

# the fast step of a character in a literal segment is the segment's full step
def k3.l.fast(
  +uu: U32,
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>
) -> {T.read.fast(k3.l(hd, rw, hs, he, ps, sk, ab, back, un, lf, buf), Chr{uu}) == T.read.once2(T.lex.kq.go(
  U32.is_eq(uu, 39), U32.is_eq(uu, 92), False{}, Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)),
  k3.l(hd, rw, hs, he, ps, sk, ab, back, un, lf, buf), Chr{uu}, M5.qs.close(hd), M4.qs.lex(hd))) : T.St}:
  match hd:
    case False{}:
      {==}
    case True{}:
      {==}

# a character that is no control is pushed: str.bad passes it
def k3.l.char(
  ctl: Bool,
  +uu: U32,
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  hc: {ctl == False{} : Bool}
) -> {T.read.once2(T.lex.kq.char.go(T.str.bad.go(ctl, U32.is_eq(uu, 9),
  Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)), False{}), k3.l(hd, rw, hs, he, ps, sk, ab, back, un, lf, buf),
  Chr{uu}, M4.qs.lex(hd))) == k3.l(hd, rw, hs, he, ps, sk, ab, back, un, lf, Chr{uu} <> buf) : T.St}:
  match ctl:
    case False{}:
      {==}
    case True{}:
      Eq.bit.absurd2(&2, {T.read.once2(T.lex.kq.char.go(T.str.bad.go(True{}, U32.is_eq(uu, 9),
        Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)), False{}), k3.l(hd, rw, hs, he, ps, sk, ab, back, un, lf,
        buf), Chr{uu}, M4.qs.lex(hd))) == k3.l(hd, rw, hs, he, ps, sk, ab, back, un, lf, Chr{uu} <> buf) : T.St}, hc)

# a character that is no apostrophe, no backslash and no newline is no closer
# and no backslash
def k3.l.go(
  quote: Bool,
  bs: Bool,
  nl: Bool,
  +uu: U32,
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  hq: {quote == False{} : Bool},
  hb: {bs == False{} : Bool},
  hn: {nl == False{} : Bool},
  hc: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool}
) -> {T.read.once2(T.lex.kq.go(quote, bs, False{}, nl, k3.l(hd, rw, hs, he, ps, sk, ab, back, un, lf, buf), Chr{uu},
  M5.qs.close(hd), M4.qs.lex(hd))) == k3.l(hd, rw, hs, he, ps, sk, ab, back, un, lf, Chr{uu} <> buf) : T.St}:
  match quote:
    case True{}:
      Eq.bit.absurd2(&2, {T.read.once2(T.lex.kq.go(True{}, bs, False{}, nl, k3.l(hd, rw, hs, he, ps, sk, ab,
        back, un, lf, buf), Chr{uu}, M5.qs.close(hd), M4.qs.lex(hd))) == k3.l(hd, rw, hs, he, ps, sk, ab, back, un, lf,
        Chr{uu} <> buf) : T.St}, hq)
    case False{}:
      match bs:
        case True{}:
          Eq.bit.absurd2(&2, {T.read.once2(T.lex.kq.go(False{}, True{}, False{}, nl, k3.l(hd, rw, hs, he,
            ps, sk, ab, back, un, lf, buf), Chr{uu}, M5.qs.close(hd), M4.qs.lex(hd))) == k3.l(hd, rw, hs, he, ps, sk,
                ab,
            back, un, lf, Chr{uu} <> buf) : T.St}, hb)
        case False{}:
          match nl:
            case True{}:
              Eq.bit.absurd2(&2, {T.read.once2(T.lex.kq.go(False{}, False{}, False{}, True{}, k3.l(hd,
                rw, hs, he, ps, sk, ab, back, un, lf, buf), Chr{uu}, M5.qs.close(hd), M4.qs.lex(hd))) == k3.l(hd, rw,
                    hs,
                he, ps, sk, ab, back, un, lf, Chr{uu} <> buf) : T.St}, hn)
            case False{}:
              k3.l.char(Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), uu, hd, rw, hs, he, ps, sk, ab,
                back, un, lf, buf, hc)

# the fast step pushes a character
def k3.l.Fast(
  +uu: U32,
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>
) -> Type:
  {T.read.fast(k3.l(hd, rw, hs, he, ps, sk, ab, back, un, lf, buf), Chr{uu})
    == k3.l(hd, rw, hs, he, ps, sk, ab, back, un, lf, Chr{uu} <> buf) : T.St}

# the scan mode sends such a character to the fast step
def k3.l.q(
  dq: Bool,
  sq: Bool,
  cr: Bool,
  +uu: U32,
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  hq: {dq == False{} : Bool},
  hs1: {sq == False{} : Bool},
  hr: {cr == False{} : Bool},
  fast: k3.l.Fast(uu, hd, rw, hs, he, ps, sk, ab, back, un, lf, buf)
) -> {T.doc.scan.q(dq, sq, cr, k3.l(hd, rw, hs, he, ps, sk, ab, back, un, lf, buf), Chr{uu})
  == T.MScan{k3.l(hd, rw, hs, he, ps, sk, ab, back, un, lf, Chr{uu} <> buf)} : T.Mode}:
  match dq:
    case True{}:
      Eq.bit.absurd2(&2, {T.doc.scan.q(True{}, sq, cr, k3.l(hd, rw, hs, he, ps, sk, ab, back, un, lf, buf), Chr{uu})
        == T.MScan{k3.l(hd, rw, hs, he, ps, sk, ab, back, un, lf, Chr{uu} <> buf)} : T.Mode}, hq)
    case False{}:
      match sq:
        case True{}:
          Eq.bit.absurd2(&2, {T.doc.scan.q(False{}, True{}, cr, k3.l(hd, rw, hs, he, ps, sk, ab, back, un, lf, buf),
            Chr{uu}) == T.MScan{k3.l(hd, rw, hs, he, ps, sk, ab, back, un, lf, Chr{uu} <> buf)} : T.Mode}, hs1)
        case False{}:
          match cr:
            case True{}:
              Eq.bit.absurd2(&2, {T.doc.scan.q(False{}, False{}, True{}, k3.l(hd, rw, hs, he, ps, sk, ab,
                back, un, lf, buf), Chr{uu}) == T.MScan{k3.l(hd, rw, hs, he, ps, sk, ab, back, un, lf, Chr{uu} <> buf)}
                : T.Mode}, hr)
            case False{}:
              Equal.cong(T.St, T.Mode, st => T.MScan{st},
                T.read.fast(k3.l(hd, rw, hs, he, ps, sk, ab, back, un, lf, buf), Chr{uu}),
                k3.l(hd, rw, hs, he, ps, sk, ab, back, un, lf, Chr{uu} <> buf), fast)

# any other literal character goes through the dispatch and is pushed
def k3.l.gen(
  +uu: U32,
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  e34: {U32.is_eq(uu, 34) == False{} : Bool},
  e92: {U32.is_eq(uu, 92) == False{} : Bool},
  +e9: {U32.is_eq(uu, 9) == False{} : Bool},
  +el: {L1.lit.char(Chr{uu}) == True{} : Bool}
) -> k3.l.Step(uu, hd, rw, hs, he, ps, sk, ab, back, un, lf, buf):
  +e39 = {lit.q(U32.is_eq(uu, 39), Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), U32.is_eq(uu, 9),
    el) : {U32.is_eq(uu, 39) == False{} : Bool}}
  +ec = {lit.c(U32.is_eq(uu, 39), Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), U32.is_eq(uu, 9),
    e9, el) : {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool}}
  +e10 = {M1.ctl.off(uu, 10, ec, {==}) : {U32.is_eq(uu, 10) == False{} : Bool}}
  +e13 = {M1.ctl.off(uu, 13, ec, {==}) : {U32.is_eq(uu, 13) == False{} : Bool}}
  k3.l.q(U32.is_eq(uu, 34), U32.is_eq(uu, 39), U32.is_eq(uu, 13), uu, hd, rw, hs, he, ps, sk, ab, back, un, lf, buf,
    e34, e39, e13,
    Equal.trans(T.St, T.read.fast(k3.l(hd, rw, hs, he, ps, sk, ab, back, un, lf, buf), Chr{uu}),
      T.read.once2(T.lex.kq.go(U32.is_eq(uu, 39), U32.is_eq(uu, 92), False{},
        Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)), k3.l(hd, rw, hs, he, ps, sk, ab, back, un, lf, buf), Chr{uu},
        M5.qs.close(hd), M4.qs.lex(hd))),
      k3.l(hd, rw, hs, he, ps, sk, ab, back, un, lf, Chr{uu} <> buf),
      k3.l.fast(uu, hd, rw, hs, he, ps, sk, ab, back, un, lf, buf),
      k3.l.go(U32.is_eq(uu, 39), U32.is_eq(uu, 92), Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)), uu, hd,
        rw, hs, he, ps, sk, ab, back, un, lf, buf, e39, e92, M7.or.ff(U32.is_eq(uu, 10), U32.is_eq(uu, 13), e10, e13),
        ec)))

# one code point k that the test found: its step is the character's
def k3.l.is(
  +uu: U32,
  +kk: U32,
  ee: {U32.is_eq(uu, kk) == True{} : Bool},
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  at: k3.l.Step(kk, hd, rw, hs, he, ps, sk, ab, back, un, lf, buf)
) -> k3.l.Step(uu, hd, rw, hs, he, ps, sk, ab, back, un, lf, buf):
  eu = Equal.cong(Char, U32, cc => Char.to_u32(cc), Chr{uu}, Chr{kk}, Eq.u32_eq(uu, kk, ee))
  %Equal.sym(U32, uu, kk, eu) : k3.l.Step(_, hd, rw, hs, he, ps, sk, ab, back, un, lf, buf)
  at

# every literal character: a quotation mark, a backslash, a tab, or another
def k3.l.split(
  +uu: U32,
  d34: Bool,
  b92: Bool,
  t9: Bool,
  e34: {U32.is_eq(uu, 34) == d34 : Bool},
  e92: {U32.is_eq(uu, 92) == b92 : Bool},
  e9: {U32.is_eq(uu, 9) == t9 : Bool},
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  el: {L1.lit.char(Chr{uu}) == True{} : Bool}
) -> k3.l.Step(uu, hd, rw, hs, he, ps, sk, ab, back, un, lf, buf):
  match d34:
    case True{}:
      k3.l.is(uu, 34, e34, hd, rw, hs, he, ps, sk, ab, back, un, lf, buf, k3.l.s34(hd, rw, hs, he, ps, sk, ab, back,
        un, lf, buf))
    case False{}:
      match b92:
        case True{}:
          k3.l.is(uu, 92, e92, hd, rw, hs, he, ps, sk, ab, back, un, lf, buf, k3.l.s92(hd, rw, hs, he, ps, sk, ab,
            back, un, lf, buf))
        case False{}:
          match t9:
            case True{}:
              k3.l.is(uu, 9, e9, hd, rw, hs, he, ps, sk, ab, back, un, lf, buf, k3.l.s9(hd, rw, hs, he, ps, sk, ab,
                back, un, lf,
                buf))
            case False{}:
              k3.l.gen(uu, hd, rw, hs, he, ps, sk, ab, back, un, lf, buf, e34, e92, e9, el)

# one character of a literal segment
def k3.l.one(
  +uu: U32,
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  el: {L1.lit.char(Chr{uu}) == True{} : Bool}
) -> k3.l.Step(uu, hd, rw, hs, he, ps, sk, ab, back, un, lf, buf):
  k3.l.split(uu, U32.is_eq(uu, 34), U32.is_eq(uu, 92), U32.is_eq(uu, 9), {==}, {==}, {==}, hd, rw, hs,
    he, ps, sk, ab, back, un, lf, buf, el)

# every character of a literal text is pushed, whatever follows it
def k3.l.body(
  ss: String,
  +rr: String,
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +un: U32,
  +lf: U32,
  +buf: List<&2, Char>,
  +ee: {L1.lit.text(ss) == True{} : Bool}
) -> {T.doc.read(String.append(ss, rr), T.MScan{k3.l(hd, rw, hs, he, ps, sk, ab, back, un, lf, buf)})
  == T.doc.read(rr, T.MScan{k3.l(hd, rw, hs, he, ps, sk, ab, back, un, lf, M2.rev.onto(ss, buf))}) : T.Doc}:
  match ss:
    case SNil{}:
      {==}
    case SCon{hh, +tt}:
      match hh:
        case Chr{+uu}:
          Equal.trans(T.Doc,
            T.doc.read(String.append(tt, rr), T.doc.scan(k3.l(hd, rw, hs, he, ps, sk, ab, back, un, lf, buf), Chr{uu})),
            T.doc.read(String.append(tt, rr), T.MScan{k3.l(hd, rw, hs, he, ps, sk, ab, back, un, lf, Chr{uu} <> buf)}),
            T.doc.read(rr, T.MScan{k3.l(hd, rw, hs, he, ps, sk, ab, back, un, lf, M2.rev.onto(tt, Chr{uu} <> buf))}),
            Equal.cong(T.Mode, T.Doc, md => T.doc.read(String.append(tt, rr), md),
              T.doc.scan(k3.l(hd, rw, hs, he, ps, sk, ab, back, un, lf, buf), Chr{uu}),
              T.MScan{k3.l(hd, rw, hs, he, ps, sk, ab, back, un, lf, Chr{uu} <> buf)},
              k3.l.one(uu, hd, rw, hs, he, ps, sk, ab, back, un, lf, buf,
                Eq.and.left(L1.lit.char(Chr{uu}), L1.lit.text(tt), ee))),
            k3.l.body(tt, rr, hd, rw, hs, he, ps, sk, ab, back, un, lf, Chr{uu} <> buf,
              Eq.and.right(L1.lit.char(Chr{uu}), L1.lit.text(tt), ee)))

# KEY-3: a dotted key read from every place a key may start: the start of a
# line (LTop), an inline table after `{` (LInl) or a comma (LInlK), and after
# a dot (LKeyDot), whatever the stack, uni and left hold. A bare segment is
# pushed in LKey and ended by blank space, a dot or `=`; a basic one is read
# piece by piece (k3.pcs) and a literal one character by character (k3.l),
# each ending in LAfter; blank space in LAfter and after a dot is skipped.
# The segment's name joins parts, newest first, as WP-K3's kl does with the
# stack and the escape fields fixed.

# a scanner reading a key, with its segments so far in ps and the open bare
# segment reversed in buf
def k3.w(
  rw: List<&2, T.Val>,
  hs: List<&2, String>,
  he: List<&2, String>,
  ps: List<&2, String>,
  buf: List<&2, Char>,
  lex: T.Lex,
  bk: T.Lex,
  qk: T.QKind,
  sk: List<&2, T.Ctx>,
  un: U32,
  lf: U32,
  ab: Bool
) -> T.St:
  T.St{"", rw, hs, he, ps, buf, lex, bk, qk, sk, T.HNone{}, un, lf, ab, False{}}

# the segments before it: none where a key starts
def k3.ps0(dt: Bool, ps: List<&2, String>) -> List<&2, String>:
  match dt:
    case False{}:
      []
    case True{}:
      ps

# a bare character is no quote and no carriage return, so the scan mode
# sends it to the fast step
def k3.so(
  +st: T.St,
  +xx: U32,
  +ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.MScan{T.read.fast(st, Chr{xx})} == T.doc.scan(st, Chr{xx}) : T.Mode}:
  Equal.sym(T.Mode, T.doc.scan(st, Chr{xx}), T.MScan{T.read.fast(st, Chr{xx})},
    M6.scan.other(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), U32.is_eq(xx, 13), st, Chr{xx}, {==}, {==}, {==},
      ch => T.bare.at(ch), ee, {==}, {==}, {==}))

# the key's segments pushed onto the parts before them, newest first
def k3.acc(ds: List<&2, L1.KDot>, last: D3.KSeg, dt: Bool, ps: List<&2, String>) -> List<&2, String>:
  List.reverse.go(&2, String, L1.k3.dk.names(ds, last), k3.ps0(dt, ps))

# KEY-3: a header read with every spelling of its segments, from any uni and
# left. After `[` (and a second `[` for an array of tables) the header waits
# in LHead; blank space there moves it to LHeadDot, as after a dot. A bare
# segment is pushed in LHead and ended by a blank (to LHeadGap), a dot or the
# bracket; a basic one is read by k3.pcs and a literal one by k3.l at hd =
# True, each closing into LHeadGap, where blank space stays until a dot or
# the bracket. The bracket runs the header's walk, as WP-H's wh.fin does.

# where a header segment starts: right after the bracket, or after blank
# space or a dot
def k3.hlex0(dt: Bool) -> T.Lex:
  match dt:
    case False{}:
      T.LHead{}
    case True{}:
      T.LHeadDot{}

# what ends a header segment: a dot, or the closing bracket
def k3.hdl(cl: Bool) -> Char:
  match cl:
    case False{}:
      '.'
    case True{}:
      ']'

# the scanner after a header segment and what follows it: waiting for the
# next segment after a dot, or closed after the bracket
def k3.haft(
  cl: Bool,
  rw: List<&2, T.Val>,
  hs: List<&2, String>,
  he: List<&2, String>,
  ps: List<&2, String>,
  bk: T.Lex,
  qk: T.QKind,
  un: U32,
  lf: U32,
  +ab: Bool
) -> T.St:
  match cl:
    case False{}:
      k3.w(rw, hs, he, ps, [], T.LHeadDot{}, bk, qk, [], un, lf, ab)
    case True{}:
      T.read.once2(T.lex.head.close2(ab, k3.w(rw, hs, he, ps, [], T.LHeadGap{}, bk, qk, [], un, lf, ab)))

# the rest of the text after a header segment, read from every back, qkind,
# uni and left
def k3.HT(
  +cl: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +ab: Bool,
  +rest: String,
  +goal: T.Doc
) -> Type:
  @b2: T.Lex -> @q2: T.QKind -> @u2: U32 -> @l2: U32 ->
    {T.doc.read(rest, T.MScan{k3.haft(cl, rw, hs, he, ps, b2, q2, u2, l2, ab)}) == goal : T.Doc}

# blank space after a dot, or right after the bracket once one blank is
# read, stays in LHeadDot
def k3.hdgap(
  gs: List<&2, Bool>,
  +rr: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool
) -> {T.doc.read(rr, T.MScan{k3.w(rw, hs, he, ps, [], T.LHeadDot{}, bk, qk, [], un, lf,
  ab)}) == T.doc.read(String.append(D2.gap(gs), rr), T.MScan{k3.w(rw, hs, he, ps, [], T.LHeadDot{}, bk, qk, [], un,
    lf, ab)}) : T.Doc}:
  match gs:
    case []:
      {==}
    case tab <> rest:
      match tab:
        case True{}:
          k3.hdgap(rest, rr, rw, hs, he, ps, bk, qk, un, lf, ab)
        case False{}:
          k3.hdgap(rest, rr, rw, hs, he, ps, bk, qk, un, lf, ab)

# and after a segment in LHeadGap
def k3.hgap(
  gs: List<&2, Bool>,
  +rr: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool
) -> {T.doc.read(rr, T.MScan{k3.w(rw, hs, he, ps, [], T.LHeadGap{}, bk, qk, [], un, lf,
  ab)}) == T.doc.read(String.append(D2.gap(gs), rr), T.MScan{k3.w(rw, hs, he, ps, [], T.LHeadGap{}, bk, qk, [], un,
    lf, ab)}) : T.Doc}:
  match gs:
    case []:
      {==}
    case tab <> rest:
      match tab:
        case True{}:
          k3.hgap(rest, rr, rw, hs, he, ps, bk, qk, un, lf, ab)
        case False{}:
          k3.hgap(rest, rr, rw, hs, he, ps, bk, qk, un, lf, ab)

# whether there is any blank space
def k3.nz(gs: List<&2, Bool>) -> Bool:
  match gs:
    case []:
      False{}
    case _t <> _r:
      True{}

# blank space right after the bracket waits for the first segment in
# LHeadDot
def k3.hlead(
  g0: List<&2, Bool>,
  +rr: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool
) -> {T.doc.read(rr, T.MScan{k3.w(rw, hs, he, k3.ps0(k3.nz(g0), []), [], k3.hlex0(k3.nz(g0)), bk, qk, [], un, lf,
  ab)}) == T.doc.read(String.append(D2.gap(g0), rr), T.MScan{k3.w(rw, hs, he, [], [], T.LHead{}, bk, qk, [], un, lf,
    ab)}) : T.Doc}:
  match g0:
    case []:
      {==}
    case tab <> rest:
      match tab:
        case True{}:
          k3.hdgap(rest, rr, rw, hs, he, [], bk, qk, un, lf, ab)
        case False{}:
          k3.hdgap(rest, rr, rw, hs, he, [], bk, qk, un, lf, ab)

# a dot or the bracket after a segment's blank space
def k3.hgdl(
  +cl: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String
) -> {T.doc.read(rest, T.MScan{k3.haft(cl, rw, hs, he, ps, bk, qk, un, lf, ab)}) == T.doc.read(SCon{k3.hdl(cl), rest},
  T.MScan{k3.w(rw, hs, he, ps, [], T.LHeadGap{}, bk, qk, [], un, lf, ab)}) : T.Doc}:
  match cl:
    case False{}:
      {==}
    case True{}:
      {==}

# a header segment's name pushed onto parts, then blank space and a dot or
# the bracket: the rest is read from there
def k3.hfin(
  +nm: String,
  +bf: List<&2, Char>,
  en: {nm == T.buf.str(bf) : String},
  +gs: List<&2, Bool>,
  +cl: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  +goal: T.Doc,
  ih: k3.HT(cl, rw, hs, he, nm <> ps, ab, rest, goal)
) -> {T.doc.read(String.append(D2.gap(gs), SCon{k3.hdl(cl), rest}), T.MScan{k3.w(rw, hs, he, T.buf.str(bf) <> ps,
  [], T.LHeadGap{}, bk, qk, [], un, lf, ab)}) == goal : T.Doc}:
  %k3.hgap(gs, SCon{k3.hdl(cl), rest}, rw, hs, he, T.buf.str(bf) <> ps, bk, qk, un, lf, ab) : {_ == goal : T.Doc}
  %k3.hgdl(cl, rw, hs, he, T.buf.str(bf) <> ps, bk, qk, un, lf, ab, rest) : {_ == goal : T.Doc}
  %en : {T.doc.read(rest, T.MScan{k3.haft(cl, rw, hs, he, _ <> ps, bk, qk, un, lf, ab)}) == goal : T.Doc}
  ih(bk, qk, un, lf)

# the first character of a bare header segment starts its buffer
def k3.hb1(
  +dt: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +xx: U32,
  +ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.MScan{k3.w(rw, hs, he, k3.ps0(dt, ps), [Chr{xx}], T.LHead{}, bk, qk, [], un, lf, ab)} == T.doc.scan(k3.w(rw,
  hs, he, k3.ps0(dt, ps), [], k3.hlex0(dt), bk, qk, [], un, lf, ab), Chr{xx}) : T.Mode}:
  match dt:
    case False{}:
      %k3.so(k3.w(rw, hs, he, k3.ps0(dt, ps), [], k3.hlex0(dt), bk, qk, [], un, lf, ab), xx, ee) : {T.MScan{k3.w(rw, hs,
        he, k3.ps0(dt, ps), [Chr{xx}], T.LHead{}, bk, qk, [], un, lf, ab)} == _ : T.Mode}
      Equal.cong(T.St, T.Mode, st => T.MScan{T.read.once2(st)}, T.lex.head.ch(k3.w(rw, hs, he, [], [], T.LHead{}, bk,
        qk, [], un, lf, ab), Chr{xx}), T.lex.head.go(Char.is_eq(Chr{xx}, '['), T.bare.at(Chr{xx}), T.ch.sp(Chr{xx}),
          Char.is_eq(Chr{xx}, '.'), Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''),
            Char.is_eq(Chr{xx}, '#'), k3.w(rw, hs, he, [], [], T.LHead{}, bk, qk, [], un, lf, ab), Chr{xx}),
        Equal.sym(T.St, T.lex.head.go(Char.is_eq(Chr{xx}, '['), T.bare.at(Chr{xx}), T.ch.sp(Chr{xx}),
          Char.is_eq(Chr{xx}, '.'), Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''),
            Char.is_eq(Chr{xx}, '#'), k3.w(rw, hs, he, [], [], T.LHead{}, bk, qk, [], un, lf, ab), Chr{xx}),
              T.lex.head.ch(k3.w(rw, hs, he, [], [], T.LHead{}, bk, qk, [], un, lf, ab), Chr{xx}),
                M3.wh.go.bare(Char.is_eq(Chr{xx}, '['), T.bare.at(Chr{xx}), T.ch.sp(Chr{xx}), Char.is_eq(Chr{xx}, '.'),
                  Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), Char.is_eq(Chr{xx},
                    '#'), k3.w(rw, hs, he, [], [], T.LHead{}, bk, qk, [], un, lf, ab), xx, {==}, {==}, ee)))
    case True{}:
      %k3.so(k3.w(rw, hs, he, k3.ps0(dt, ps), [], k3.hlex0(dt), bk, qk, [], un, lf, ab), xx, ee) : {T.MScan{k3.w(rw, hs,
        he, k3.ps0(dt, ps), [Chr{xx}], T.LHead{}, bk, qk, [], un, lf, ab)} == _ : T.Mode}
      Equal.cong(T.St, T.Mode, st => T.MScan{T.read.once2(st)}, T.st.push(k3.w(rw, hs, he, ps, [], T.LHeadDot{}, bk,
        qk, [], un, lf, ab), Chr{xx}, T.LHead{}), T.lex.hdot(T.ch.sp(Chr{xx}), T.bare.at(Chr{xx}), Char.is_eq(Chr{xx},
          '"'), Char.is_eq(Chr{xx}, '\''), k3.w(rw, hs, he, ps, [], T.LHeadDot{}, bk, qk, [], un, lf, ab), Chr{xx}),
        Equal.sym(T.St, T.lex.hdot(T.ch.sp(Chr{xx}), T.bare.at(Chr{xx}), Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx},
          '\''), k3.w(rw, hs, he, ps, [], T.LHeadDot{}, bk, qk, [], un, lf, ab), Chr{xx}), T.st.push(k3.w(rw, hs, he,
            ps, [], T.LHeadDot{}, bk, qk, [], un, lf, ab), Chr{xx}, T.LHead{}), M3.wh.dot.bare(T.ch.sp(Chr{xx}),
              T.bare.at(Chr{xx}), Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), k3.w(rw, hs, he, ps, [],
                T.LHeadDot{}, bk, qk, [], un, lf, ab), xx, {==}, {==}, ee)))

# with a segment open, the next bare character joins it, whatever came
# before
def k3.hlater(
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +dd: Char,
  +bb: List<&2, Char>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +cc: Char
) -> {k3.w(rw, hs, he, ps, cc <> dd <> bb, T.LHead{}, bk, qk, [], un, lf, ab) == T.read.once2(T.lex.head.ch(k3.w(rw,
  hs, he, ps, dd <> bb, T.LHead{}, bk, qk, [], un, lf, ab), cc)) : T.St}:
  match ps:
    case []:
      {==}
    case _p <> _ps:
      {==}

# a later character of a bare header segment
def k3.hb2(
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +dd: Char,
  +bb: List<&2, Char>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +xx: U32,
  +ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.MScan{k3.w(rw, hs, he, ps, Chr{xx} <> dd <> bb, T.LHead{}, bk, qk, [], un, lf, ab)} == T.doc.scan(k3.w(rw, hs,
  he, ps, dd <> bb, T.LHead{}, bk, qk, [], un, lf, ab), Chr{xx}) : T.Mode}:
  %k3.so(k3.w(rw, hs, he, ps, dd <> bb, T.LHead{}, bk, qk, [], un, lf, ab), xx, ee) : {T.MScan{k3.w(rw, hs, he, ps,
    Chr{xx} <> dd <> bb, T.LHead{}, bk, qk, [], un, lf, ab)} == _ : T.Mode}
  %Equal.sym(T.St, T.lex.head.go(Char.is_eq(Chr{xx}, '['), T.bare.at(Chr{xx}), T.ch.sp(Chr{xx}), Char.is_eq(Chr{xx},
    '.'), Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), Char.is_eq(Chr{xx}, '#'),
      k3.w(rw, hs, he, ps, dd <> bb, T.LHead{}, bk, qk, [], un, lf, ab), Chr{xx}), T.lex.head.ch(k3.w(rw, hs, he, ps,
        dd <> bb, T.LHead{}, bk, qk, [], un, lf, ab), Chr{xx}), M3.wh.go.bare(Char.is_eq(Chr{xx}, '['),
          T.bare.at(Chr{xx}), T.ch.sp(Chr{xx}), Char.is_eq(Chr{xx}, '.'), Char.is_eq(Chr{xx}, ']'),
            Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), Char.is_eq(Chr{xx}, '#'), k3.w(rw, hs, he, ps,
              dd <> bb, T.LHead{}, bk, qk, [], un, lf, ab), xx, {==}, {==}, ee)) : {T.MScan{k3.w(rw, hs, he, ps,
                Chr{xx} <> dd <> bb, T.LHead{}, bk, qk, [], un, lf, ab)} == T.MScan{T.read.once2(_)}
    : T.Mode}
  Equal.cong(T.St, T.Mode, st => T.MScan{st}, k3.w(rw, hs, he, ps, Chr{xx} <> dd <> bb, T.LHead{}, bk, qk, [], un, lf,
    ab), T.read.once2(T.lex.head.ch(k3.w(rw, hs, he, ps, dd <> bb, T.LHead{}, bk, qk, [], un, lf, ab), Chr{xx})),
    k3.hlater(rw, hs, he, ps, dd, bb, bk, qk, un, lf, ab, Chr{xx}))

# the rest of a bare header segment is pushed onto its buffer
def k3.hbbody(
  ks: String,
  +rr: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +dd: Char,
  +bb: List<&2, Char>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +ee: {T.bare.all(String.to_list(ks)) == True{} : Bool}
) -> {T.doc.read(rr, T.MScan{k3.w(rw, hs, he, ps, M2.rev.onto(ks, dd <> bb), T.LHead{}, bk, qk, [], un, lf,
  ab)}) == T.doc.read(String.append(ks, rr), T.MScan{k3.w(rw, hs, he, ps, dd <> bb, T.LHead{}, bk, qk, [], un, lf,
    ab)}) : T.Doc}:
  match ks:
    case SNil{}:
      {==}
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          %k3.hb2(rw, hs, he, ps, dd, bb, bk, qk, un, lf, ab, xx, M7.ball.head(T.bare.at(Chr{xx}), String.to_list(tt),
              ee))
            : {T.doc.read(rr, T.MScan{k3.w(rw, hs, he, ps, M2.rev.onto(ks, dd <> bb), T.LHead{}, bk, qk, [], un, lf,
              ab)}) == T.doc.read(String.append(tt, rr), _) : T.Doc}
          k3.hbbody(tt, rr, rw, hs, he, ps, Chr{xx}, dd <> bb, bk, qk, un, lf, ab, M7.ball.tail(T.bare.at(Chr{xx}),
            String.to_list(tt), ee))

# a blank ends an open bare header segment: it is pushed, and the header
# waits in LHeadGap
def k3.hbsp(
  +tab: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bf: List<&2, Char>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rr: String,
  full: {List.is_empty(&2, Char, bf) == False{} : Bool}
) -> {T.doc.read(rr, T.MScan{k3.w(rw, hs, he, T.buf.str(bf) <> ps, [], T.LHeadGap{}, bk, qk, [], un, lf,
  ab)}) == T.doc.read(SCon{D2.blank_char(tab), rr}, T.MScan{k3.w(rw, hs, he, ps, bf, T.LHead{}, bk, qk, [], un, lf,
    ab)}) : T.Doc}:
  match tab:
    case True{}:
      %Equal.sym(Bool, List.is_empty(&2, Char, bf), False{}, full) : {T.doc.read(rr, T.MScan{k3.w(rw, hs, he,
        T.buf.str(bf) <> ps, [], T.LHeadGap{}, bk, qk, [], un, lf, ab)})
        == T.doc.read(rr, T.MScan{T.read.once2(T.lex.head.gap.go(_, k3.w(rw, hs, he, ps, bf, T.LHead{}, bk, qk, [],
          un, lf, ab)))}) : T.Doc}
      {==}
    case False{}:
      %Equal.sym(Bool, List.is_empty(&2, Char, bf), False{}, full) : {T.doc.read(rr, T.MScan{k3.w(rw, hs, he,
        T.buf.str(bf) <> ps, [], T.LHeadGap{}, bk, qk, [], un, lf, ab)})
        == T.doc.read(rr, T.MScan{T.read.once2(T.lex.head.gap.go(_, k3.w(rw, hs, he, ps, bf, T.LHead{}, bk, qk, [],
          un, lf, ab)))}) : T.Doc}
      {==}

# the bracket closes the header the same way whatever state the last
# segment ended in
def k3.hlexfree(
  +ab: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +pp: String,
  +ps: List<&2, String>,
  +lx: T.Lex,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32
) -> {T.read.once2(T.lex.head.close2(ab, k3.w(rw, hs, he, pp <> ps, [], T.LHeadGap{}, bk, qk, [], un, lf,
  ab))) == T.read.once2(T.lex.head.close2(ab, k3.w(rw, hs, he, pp <> ps, [], lx, bk, qk, [], un, lf, ab))) : T.St}:
  match ab:
    case False{}:
      {==}
    case True{}:
      {==}

# a dot or the bracket ends an open bare header segment and pushes it
def k3.hbdl(
  +cl: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bf: List<&2, Char>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  full: {List.is_empty(&2, Char, bf) == False{} : Bool}
) -> {T.doc.read(rest, T.MScan{k3.haft(cl, rw, hs, he, T.buf.str(bf) <> ps, bk, qk, un, lf, ab)})
  == T.doc.read(SCon{k3.hdl(cl), rest}, T.MScan{k3.w(rw, hs, he, ps, bf, T.LHead{}, bk, qk, [], un, lf, ab)}) : T.Doc}:
  match cl:
    case False{}:
      %Equal.sym(Bool, List.is_empty(&2, Char, bf), False{}, full) : {T.doc.read(rest,
        T.MScan{k3.haft(False{}, rw, hs, he, T.buf.str(bf) <> ps, bk, qk, un, lf, ab)}) == T.doc.read(rest,
        T.MScan{T.read.once2(T.lex.head.dot3(_, k3.w(rw, hs, he, ps, bf, T.LHead{}, bk, qk, [], un, lf, ab)))}) : T.Doc}
      {==}
    case True{}:
      %Equal.sym(Bool, List.is_empty(&2, Char, bf), False{}, full) : {T.doc.read(rest,
        T.MScan{k3.haft(True{}, rw, hs, he, T.buf.str(bf) <> ps, bk, qk, un, lf, ab)}) == T.doc.read(rest,
        T.MScan{T.read.once2(T.lex.head.close.go(_, ab, k3.w(rw, hs, he, ps, bf, T.LHead{}, bk, qk, [], un, lf,
          ab)))}) : T.Doc}
      Equal.cong(T.St, T.Doc, st => T.doc.read(rest, T.MScan{st}), T.read.once2(T.lex.head.close2(ab, k3.w(rw, hs, he,
        T.buf.str(bf) <> ps, [], T.LHeadGap{}, bk, qk, [], un, lf, ab))),
        T.read.once2(T.lex.head.close2(ab, k3.w(rw, hs, he, T.buf.str(bf) <> ps, [], T.LHead{}, bk, qk, [], un, lf,
          ab))), k3.hlexfree(ab, rw, hs, he, T.buf.str(bf), ps, T.LHead{}, bk,
        qk, un, lf))

# blank space and a dot or the bracket after an open bare header segment
# push it
def k3.hbend(
  gs: List<&2, Bool>,
  +cl: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bf: List<&2, Char>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  full: {List.is_empty(&2, Char, bf) == False{} : Bool}
) -> {T.doc.read(rest, T.MScan{k3.haft(cl, rw, hs, he, T.buf.str(bf) <> ps, bk, qk, un, lf, ab)})
  == T.doc.read(String.append(D2.gap(gs), SCon{k3.hdl(cl), rest}), T.MScan{k3.w(rw, hs, he, ps, bf, T.LHead{}, bk,
    qk, [], un, lf, ab)}) : T.Doc}:
  match gs:
    case []:
      k3.hbdl(cl, rw, hs, he, ps, bf, bk, qk, un, lf, ab, rest, full)
    case +tab <> +gr:
      %k3.hbsp(tab, rw, hs, he, ps, bf, bk, qk, un, lf, ab, String.append(D2.gap(gr), SCon{k3.hdl(cl), rest}), full)
        : {T.doc.read(rest, T.MScan{k3.haft(cl, rw, hs, he, T.buf.str(bf) <> ps, bk, qk, un, lf, ab)}) == _ : T.Doc}
      %k3.hgap(gr, SCon{k3.hdl(cl), rest}, rw, hs, he, T.buf.str(bf) <> ps, bk, qk, un, lf, ab)
        : {T.doc.read(rest, T.MScan{k3.haft(cl, rw, hs, he, T.buf.str(bf) <> ps, bk, qk, un, lf, ab)}) == _ : T.Doc}
      k3.hgdl(cl, rw, hs, he, T.buf.str(bf) <> ps, bk, qk, un, lf, ab, rest)

# a bare header segment, its blank space and a dot or the bracket
def k3.hbseg(
  +xx: U32,
  +tt: String,
  +gs: List<&2, Bool>,
  +cl: Bool,
  +dt: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  +goal: T.Doc,
  +ee: {T.bare.all.step(T.bare.at(Chr{xx}), _u => T.bare.all(String.to_list(tt))) == True{} : Bool},
  ih: k3.HT(cl, rw, hs, he, SCon{Chr{xx}, tt} <> k3.ps0(dt, ps), ab, rest, goal)
) -> {T.doc.read(String.append(SCon{Chr{xx}, tt}, String.append(D2.gap(gs), SCon{k3.hdl(cl), rest})),
  T.MScan{k3.w(rw, hs, he, k3.ps0(dt, ps), [], k3.hlex0(dt), bk, qk, [], un, lf, ab)}) == goal : T.Doc}:
  %k3.hb1(dt, rw, hs, he, ps, bk, qk, un, lf, ab, xx, M7.ball.head(T.bare.at(Chr{xx}), String.to_list(tt), ee))
    : {T.doc.read(String.append(tt, String.append(D2.gap(gs), SCon{k3.hdl(cl), rest})), _) == goal : T.Doc}
  %k3.hbbody(tt, String.append(D2.gap(gs), SCon{k3.hdl(cl), rest}), rw, hs, he, k3.ps0(dt, ps), Chr{xx}, [], bk, qk,
    un, lf, ab, M7.ball.tail(T.bare.at(Chr{xx}),
    String.to_list(tt), ee)) : {_ == goal : T.Doc}
  %k3.hbend(gs, cl, rw, hs, he, k3.ps0(dt, ps), M2.rev.onto(tt, [Chr{xx}]), bk, qk, un, lf, ab, rest, M7.rev.full(tt,
    Chr{xx}, []))
    : {_ == goal : T.Doc}
  %Equal.sym(String, T.buf.str(M2.rev.onto(tt, [Chr{xx}])), SCon{Chr{xx}, tt}, M7.wh.bname(xx, tt)) : {T.doc.read(rest,
    T.MScan{k3.haft(cl, rw, hs, he, _ <> k3.ps0(dt, ps), bk, qk, un, lf, ab)}) == goal : T.Doc}
  ih(bk, qk, un, lf)

# a quotation mark where a header segment starts opens a basic segment
def k3.hqopen(
  +dt: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool
) -> {T.MScan{k3.q(True{}, rw, hs, he, k3.ps0(dt, ps), [], ab, bk, un, lf, [])} == T.doc.scan(k3.w(rw, hs, he,
  k3.ps0(dt, ps), [], k3.hlex0(dt), bk, qk, [], un, lf, ab), '"') : T.Mode}:
  match dt:
    case True{}:
      {==}
    case False{}:
      {==}

# and an apostrophe a literal one
def k3.hlopen(
  +dt: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool
) -> {T.MScan{k3.l(True{}, rw, hs, he, k3.ps0(dt, ps), [], ab, bk, un, lf, [])} == T.doc.scan(k3.w(rw, hs, he,
  k3.ps0(dt, ps), [], k3.hlex0(dt), bk, qk, [], un, lf, ab), '\'') : T.Mode}:
  match dt:
    case True{}:
      {==}
    case False{}:
      {==}

# a basic header segment of pieces, its blank space and a dot or the
# bracket
def k3.hqseg(
  +pl: List<&2, D3.KPiece>,
  +gs: List<&2, Bool>,
  +cl: Bool,
  +dt: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  +goal: T.Doc,
  eo: {L1.k3.pcs.ok(pl) == True{} : Bool},
  ih: k3.HT(cl, rw, hs, he, D3.k3.pcs.name(pl) <> k3.ps0(dt, ps), ab, rest, goal)
) -> {T.doc.read(SCon{'"', D3.k3.pcs.text(pl, SCon{'"', String.append(D2.gap(gs), SCon{k3.hdl(cl), rest})})},
  T.MScan{k3.w(rw, hs, he, k3.ps0(dt, ps), [], k3.hlex0(dt), bk, qk, [], un, lf, ab)}) == goal : T.Doc}:
  %k3.hqopen(dt, rw, hs, he, ps, bk, qk, un, lf, ab) : {T.doc.read(D3.k3.pcs.text(pl, SCon{'"',
    String.append(D2.gap(gs), SCon{k3.hdl(cl), rest})}), _)
    == goal : T.Doc}
  k3.pcs(pl, True{}, rw, hs, he, k3.ps0(dt, ps), [], ab, bk, un, lf, [], SCon{'"', String.append(D2.gap(gs),
    SCon{k3.hdl(cl), rest})}, goal, eo, +b2 => +u2 => +l2 =>
    k3.hfin(D3.k3.pcs.name(pl), M2.rev.onto(D3.k3.pcs.name(pl), []), M7.k3.nm(D3.k3.pcs.name(pl)), gs, cl, rw, hs,
      he, k3.ps0(dt, ps), b2, T.QBasic{}, u2, l2, ab, rest, goal, ih))

# a literal header segment, its blank space and a dot or the bracket
def k3.hlseg(
  +name: String,
  +gs: List<&2, Bool>,
  +cl: Bool,
  +dt: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  +goal: T.Doc,
  el: {L1.lit.text(name) == True{} : Bool},
  ih: k3.HT(cl, rw, hs, he, name <> k3.ps0(dt, ps), ab, rest, goal)
) -> {T.doc.read(SCon{'\'', String.append(name, SCon{'\'', String.append(D2.gap(gs), SCon{k3.hdl(cl), rest})})},
  T.MScan{k3.w(rw, hs, he, k3.ps0(dt, ps), [], k3.hlex0(dt), bk, qk, [], un, lf, ab)}) == goal : T.Doc}:
  %k3.hlopen(dt, rw, hs, he, ps, bk, qk, un, lf, ab) : {T.doc.read(String.append(name, SCon{'\'',
    String.append(D2.gap(gs), SCon{k3.hdl(cl), rest})}), _)
    == goal : T.Doc}
  Equal.trans(T.Doc, T.doc.read(String.append(name, SCon{'\'', String.append(D2.gap(gs), SCon{k3.hdl(cl), rest})}),
    T.MScan{k3.l(True{}, rw, hs, he, k3.ps0(dt, ps),
    [], ab, bk, un, lf, [])}), T.doc.read(SCon{'\'', String.append(D2.gap(gs), SCon{k3.hdl(cl), rest})},
      T.MScan{k3.l(True{}, rw, hs, he, k3.ps0(dt, ps), [], ab, bk,
    un, lf, M2.rev.onto(name, []))}), goal,
    k3.l.body(name, SCon{'\'', String.append(D2.gap(gs), SCon{k3.hdl(cl), rest})}, True{}, rw, hs, he, k3.ps0(dt,
      ps), [], ab, bk, un, lf, [], el),
    k3.hfin(name, M2.rev.onto(name, []), M7.k3.nm(name), gs, cl, rw, hs, he, k3.ps0(dt, ps), bk, T.QLit{}, un, lf, ab,
        rest,
      goal,
      ih))

# a header segment spelled any way toml.abnf allows, its blank space and a
# dot or the bracket
def k3.hseg(
  sg: D3.KSeg,
  +gs: List<&2, Bool>,
  +cl: Bool,
  +dt: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  +goal: T.Doc,
  eo: {L1.k3.seg.ok(sg) == True{} : Bool},
  ih: k3.HT(cl, rw, hs, he, D3.k3.seg.name(sg) <> k3.ps0(dt, ps), ab, rest, goal)
) -> {T.doc.read(D3.k3.seg.text(sg, String.append(D2.gap(gs), SCon{k3.hdl(cl), rest})), T.MScan{k3.w(rw, hs, he,
  k3.ps0(dt, ps), [], k3.hlex0(dt), bk, qk, [], un, lf, ab)}) == goal : T.Doc}:
  match sg:
    case D3.KsBare{name}:
      match name:
        case SNil{}:
          Eq.bit.absurd(&2, {T.doc.read(String.append(SNil{}, String.append(D2.gap(gs), SCon{k3.hdl(cl), rest})),
            T.MScan{k3.w(rw, hs, he, k3.ps0(dt, ps), [], k3.hlex0(dt), bk, qk, [], un, lf, ab)}) == goal : T.Doc}, eo)
        case SCon{hh, +tt}:
          match hh:
            case Chr{+xx}:
              k3.hbseg(xx, tt, gs, cl, dt, rw, hs, he, ps, bk, qk, un, lf, ab, rest, goal, eo, ih)
    case D3.KsBasic{+pl}:
      k3.hqseg(pl, gs, cl, dt, rw, hs, he, ps, bk, qk, un, lf, ab, rest, goal, eo, ih)
    case D3.KsLit{+name}:
      k3.hlseg(name, gs, cl, dt, rw, hs, he, ps, bk, qk, un, lf, ab, rest, goal, eo, ih)

# a header's segments, then blank space and the bracket: the rest is read
# with every segment pushed onto parts, newest first
def k3.hkeys(
  ds: List<&2, L1.KDot>,
  +last: D3.KSeg,
  +g9: List<&2, Bool>,
  +dt: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  +goal: T.Doc,
  +eo: {L1.k3.dk.ok(ds, last) == True{} : Bool},
  ih: k3.HT(True{}, rw, hs, he, k3.acc(ds, last, dt, ps), ab, rest, goal)
) -> {T.doc.read(L1.k3.dk.text(ds, last, String.append(D2.gap(g9), SCon{']', rest})), T.MScan{k3.w(rw, hs, he,
  k3.ps0(dt, ps), [], k3.hlex0(dt), bk, qk, [], un, lf, ab)}) == goal
  : T.Doc}:
  match ds:
    case []:
      k3.hseg(last, g9, True{}, dt, rw, hs, he, ps, bk, qk, un, lf, ab, rest, goal, eo, ih)
    case L1.KDot{+sg, g1, +g2} <> +dr:
      k3.hseg(sg, g1, False{}, dt, rw, hs, he, ps, bk, qk, un, lf, ab, String.append(D2.gap(g2),
        L1.k3.dk.text(dr, last, String.append(D2.gap(g9), SCon{']', rest}))), goal, Eq.and.left(L1.k3.seg.ok(sg),
        L1.k3.dk.ok(dr, last), eo), +b2 => +q2 => +u2 => +l2 =>
        %k3.hdgap(g2, L1.k3.dk.text(dr, last, String.append(D2.gap(g9), SCon{']', rest})), rw, hs, he,
          D3.k3.seg.name(sg) <> k3.ps0(dt, ps), b2, q2, u2, l2, ab) : {_ == goal : T.Doc}
        k3.hkeys(dr, last, g9, True{}, rw, hs, he, D3.k3.seg.name(sg) <> k3.ps0(dt, ps), b2, q2, u2, l2, ab, rest,
          goal,
          Eq.and.right(L1.k3.seg.ok(sg), L1.k3.dk.ok(dr, last), eo), ih))

# the names pushed are never none
def k3.ne(
  ds: List<&2, L1.KDot>,
  +last: D3.KSeg,
  +acc: List<&2, String>
) -> {List.is_empty(&2, String, List.reverse.go(&2, String, L1.k3.dk.names(ds, last), acc)) == False{} : Bool}:
  match ds:
    case []:
      {==}
    case L1.KDot{sg, _g1, _g2} <> rest:
      k3.ne(rest, last, D3.k3.seg.name(sg) <> acc)

# the names pushed from where a key or a header starts, reversed, are the
# key's names
def k3.path(
  +dt: Bool,
  +ds: List<&2, L1.KDot>,
  +last: D3.KSeg
) -> {List.reverse(&2, String, k3.acc(ds, last, dt, [])) == L1.k3.dk.names(ds, last) : List<&2, String>}:
  match dt:
    case False{}:
      kv.rr(L1.k3.dk.names(ds, last))
    case True{}:
      kv.rr(L1.k3.dk.names(ds, last))

# the walk a header runs along path, with what it returns
def k3.HWalk(
  +ab: Bool,
  +path: List<&2, String>,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +rows2: List<&2, T.Val>,
  +heads2: List<&2, String>
) -> Type:
  {T.tree.walk(path, T.Tw{rw, D1.header_job(ab), [], "", "", hs, False{}}, 0) == T.End{rows2, "", heads2} : T.End}

# the rest of the text read after a header, in the table path names, from
# every back, qkind, uni and left
def k3.HLine(
  +rows2: List<&2, T.Val>,
  +heads2: List<&2, String>,
  +path: List<&2, String>,
  +rest: String,
  +goal: T.Doc
) -> Type:
  @b2: T.Lex -> @q2: T.QKind -> @u2: U32 -> @l2: U32 ->
    {T.doc.read(rest, T.MScan{L1.k3.line(rows2, heads2, path, b2, q2, u2, l2)}) == goal : T.Doc}

# what follows the closing bracket: nothing more, or the second bracket of
# an array of tables
def k3.htail(ab: Bool, rest: String) -> String:
  match ab:
    case False{}:
      rest
    case True{}:
      SCon{']', rest}

# the bracket runs the header's walk along the segments read and leaves the
# scanner in the header's table
def k3.hend(
  +ab: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +parts: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +path: List<&2, String>,
  +rows2: List<&2, T.Val>,
  +heads2: List<&2, String>,
  +rest: String,
  ne: {List.is_empty(&2, String, parts) == False{} : Bool},
  er: {List.reverse(&2, String, parts) == path : List<&2, String>},
  ew: k3.HWalk(ab, path, rw, hs, rows2, heads2)
) -> {T.doc.read(rest, T.MScan{L1.k3.line(rows2, heads2, path, bk, qk, un, lf)}) == T.doc.read(k3.htail(ab, rest),
  T.MScan{k3.haft(True{}, rw, hs, he, parts, bk, qk, un, lf, ab)}) : T.Doc}:
  match ab:
    case False{}:
      %Equal.sym(Bool, List.is_empty(&2, String, parts), False{}, ne) : {T.doc.read(rest,
        T.MScan{L1.k3.line(rows2, heads2, path, bk, qk, un, lf)}) == T.doc.read(rest,
          T.MScan{T.read.once2(T.head.go(_,
        k3.w(rw, hs, he, parts, [], T.LHeadGap{}, bk, qk, [], un, lf, False{}), List.reverse(&2, String,
          parts)))}) : T.Doc}
      %Equal.sym(List<&2, String>, List.reverse(&2, String, parts), path, er) : {T.doc.read(rest,
        T.MScan{L1.k3.line(rows2, heads2, path, bk, qk, un, lf)}) == T.doc.read(rest,
        T.MScan{T.read.once2(T.head.apply(T.tree.walk(_, T.Tw{rw, T.JDef{}, [], "", "", hs, False{}}, 0), _, bk, qk,
        un, lf, False{}))}) : T.Doc}
      %Equal.sym(T.End, T.tree.walk(path, T.Tw{rw, T.JDef{}, [], "", "", hs, False{}}, 0), T.End{rows2, "", heads2},
        ew) : {T.doc.read(rest, T.MScan{L1.k3.line(rows2, heads2, path, bk, qk, un, lf)}) == T.doc.read(rest,
        T.MScan{T.read.once2(T.head.apply(_, path, bk, qk, un, lf, False{}))}) : T.Doc}
      {==}
    case True{}:
      %Equal.sym(Bool, List.is_empty(&2, String, parts), False{}, ne) : {T.doc.read(rest,
        T.MScan{L1.k3.line(rows2, heads2, path, bk, qk, un, lf)}) == T.doc.read(rest,
          T.MScan{T.read.once2(T.head.go(_,
        k3.w(rw, hs, he, parts, [], T.LHeadR{}, bk, qk, [], un, lf, True{}), List.reverse(&2, String,
          parts)))}) : T.Doc}
      %Equal.sym(List<&2, String>, List.reverse(&2, String, parts), path, er) : {T.doc.read(rest,
        T.MScan{L1.k3.line(rows2, heads2, path, bk, qk, un, lf)}) == T.doc.read(rest,
        T.MScan{T.read.once2(T.head.apply(T.tree.walk(_, T.Tw{rw, T.JAot{}, [], "", "", hs, False{}}, 0), _, bk, qk,
        un, lf, False{}))}) : T.Doc}
      %Equal.sym(T.End, T.tree.walk(path, T.Tw{rw, T.JAot{}, [], "", "", hs, False{}}, 0), T.End{rows2, "", heads2},
        ew) : {T.doc.read(rest, T.MScan{L1.k3.line(rows2, heads2, path, bk, qk, un, lf)}) == T.doc.read(rest,
        T.MScan{T.read.once2(T.head.apply(_, path, bk, qk, un, lf, False{}))}) : T.Doc}
      {==}

# a whole header, from the start of a line in any table
def k3.hcore(
  +arr: Bool,
  +g0: List<&2, Bool>,
  +ds: List<&2, L1.KDot>,
  +last: D3.KSeg,
  +g9: List<&2, Bool>,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +a0: Bool,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +rows2: List<&2, T.Val>,
  +heads2: List<&2, String>,
  +rest: String,
  +goal: T.Doc,
  +eo: {L1.k3.dk.ok(ds, last) == True{} : Bool},
  ew: k3.HWalk(arr, L1.k3.dk.names(ds, last), rw, hs, rows2, heads2),
  ih: k3.HLine(rows2, heads2, L1.k3.dk.names(ds, last), rest, goal)
) -> {T.doc.read(L1.k3.hd.text(arr, g0, ds, last, g9, rest), T.MScan{L1.k3.at(L1.AtLine{}, rw, hs, he, [], a0,
  bk, qk, un, lf)}) == goal : T.Doc}:
  match arr:
    case False{}:
      %k3.hlead(g0, L1.k3.dk.text(ds, last, String.append(D2.gap(g9), SCon{']', rest})), rw, hs, he, bk, qk, un, lf,
        False{}) : {_ == goal : T.Doc}
      k3.hkeys(ds, last, g9, k3.nz(g0), rw, hs, he, [], bk, qk, un, lf, False{}, rest, goal, eo, +b2 => +q2 => +u2 =>
        +l2 =>
        %k3.hend(False{}, rw, hs, he, k3.acc(ds, last, k3.nz(g0), []), b2, q2, u2, l2, L1.k3.dk.names(ds, last),
          rows2, heads2, rest, k3.ne(ds, last, k3.ps0(k3.nz(g0), [])), k3.path(k3.nz(g0), ds, last), ew)
          : {_ == goal : T.Doc}
        ih(b2, q2, u2, l2))
    case True{}:
      %k3.hlead(g0, L1.k3.dk.text(ds, last, String.append(D2.gap(g9), SCon{']', SCon{']', rest}})), rw, hs, he,
        bk, qk, un, lf, True{}) : {_ == goal : T.Doc}
      k3.hkeys(ds, last, g9, k3.nz(g0), rw, hs, he, [], bk, qk, un, lf, True{}, SCon{']', rest}, goal, eo,
        +b2 => +q2 => +u2 => +l2 =>
        %k3.hend(True{}, rw, hs, he, k3.acc(ds, last, k3.nz(g0), []), b2, q2, u2, l2, L1.k3.dk.names(ds, last),
          rows2, heads2, rest, k3.ne(ds, last, k3.ps0(k3.nz(g0), [])), k3.path(k3.nz(g0), ds, last), ew)
          : {_ == goal : T.Doc}
        ih(b2, q2, u2, l2))
