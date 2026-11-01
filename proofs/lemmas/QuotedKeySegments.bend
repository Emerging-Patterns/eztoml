# a quoted key segment reads as the name its characters and escapes give
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/StringRenderEscapes.bend as L1
import ./ControlEscapeText.bend as M1
import ./FreshNamesInRows.bend as M2
import ./PickAndDigitSteps.bend as M3
import ./ValueTextReadback.bend as M4

# the document of one pair named by a buffer, holding the integer 1
def kq.doc(buf: List<&2, Char>) -> T.Doc:
  T.Doc{"", [T.VPair{T.buf.str.go(buf, ""), T.VInt{T.Plus{}, "1"}}]}

# the state after the segment's closing quote
def qs.close(hd: Bool) -> T.Lex:
  match hd:
    case False{}:
      T.LAfter{}
    case True{}:
      T.LHeadGap{}

# one character's escape read from a quoted segment, then the rest of the
# text: the rest is read with the character pushed, from wherever the escape
# left back
def qs.Goal(
  +uu: U32,
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>,
  +rest: String,
  +goal: T.Doc
) -> Type:
  (@bk: T.Lex -> {T.doc.read(rest, T.MScan{M3.qs(hd, rw, hs, he, ps, sk, ab, bk, Chr{uu} <> buf)}) == goal
    : T.Doc}) ->
    {T.doc.read(String.append(L1.esc(Chr{uu}), rest), T.MScan{M3.qs(hd, rw, hs, he, ps, sk, ab, back, buf)})
      == goal : T.Doc}

# the fast step of a character in a quoted segment is the segment's full step
def qs.fast(
  +uu: U32,
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>
) -> {T.read.fast(M3.qs(hd, rw, hs, he, ps, sk, ab, back, buf), Chr{uu}) == T.read.once2(T.lex.kq.go(U32.is_eq(uu, 34),
  U32.is_eq(uu, 92), True{}, Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)),
  M3.qs(hd, rw, hs, he, ps, sk, ab, back, buf), Chr{uu}, qs.close(hd), M3.qs.lex(hd))) : T.St}:
  match hd:
    case False{}:
      {==}
    case True{}:
      {==}

# a quoted segment's state is no quote that opens a string
def qs.wrap(
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>
) -> {T.doc.wrap(M3.qs(hd, rw, hs, he, ps, sk, ab, back, buf)) == T.MScan{M3.qs(hd, rw, hs, he, ps, sk, ab, back, buf)}
  : T.Mode}:
  match hd:
    case False{}:
      {==}
    case True{}:
      {==}

# a character that is no control is pushed: str.bad passes it
def qs.char(
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
  +buf: List<&2, Char>,
  hc: {ctl == False{} : Bool}
) -> {T.read.once2(T.lex.kq.char.go(T.str.bad.go(ctl, U32.is_eq(uu, 9),
  Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)), False{}), M3.qs(hd, rw, hs, he, ps, sk, ab, back, buf), Chr{uu},
  M3.qs.lex(hd))) == M3.qs(hd, rw, hs, he, ps, sk, ab, back, Chr{uu} <> buf) : T.St}:
  match ctl:
    case False{}:
      {==}
    case True{}:
      Eq.bit.absurd2(&2, {T.read.once2(T.lex.kq.char.go(T.str.bad.go(True{},
        U32.is_eq(uu, 9), Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)), False{}),
        M3.qs(hd, rw, hs, he, ps, sk, ab, back, buf), Chr{uu}, M3.qs.lex(hd)))
        == M3.qs(hd, rw, hs, he, ps, sk, ab, back, Chr{uu} <> buf) : T.St}, hc)

# a character that is no quote, no backslash and no newline is no closer and
# no escape
def qs.go(
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
  +buf: List<&2, Char>,
  hq: {quote == False{} : Bool},
  hb: {bs == False{} : Bool},
  hn: {nl == False{} : Bool},
  hc: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool}
) -> {T.read.once2(T.lex.kq.go(quote, bs, True{}, nl, M3.qs(hd, rw, hs, he, ps, sk, ab, back, buf), Chr{uu},
  qs.close(hd), M3.qs.lex(hd))) == M3.qs(hd, rw, hs, he, ps, sk, ab, back, Chr{uu} <> buf) : T.St}:
  match quote:
    case True{}:
      Eq.bit.absurd2(&2, {T.read.once2(T.lex.kq.go(True{}, bs, True{}, nl,
        M3.qs(hd, rw, hs, he, ps, sk, ab, back, buf), Chr{uu}, qs.close(hd), M3.qs.lex(hd)))
        == M3.qs(hd, rw, hs, he, ps, sk, ab, back, Chr{uu} <> buf) : T.St}, hq)
    case False{}:
      match bs:
        case True{}:
          Eq.bit.absurd2(&2, {T.read.once2(T.lex.kq.go(False{}, True{}, True{}, nl,
            M3.qs(hd, rw, hs, he, ps, sk, ab, back, buf), Chr{uu}, qs.close(hd), M3.qs.lex(hd)))
            == M3.qs(hd, rw, hs, he, ps, sk, ab, back, Chr{uu} <> buf) : T.St}, hb)
        case False{}:
          match nl:
            case True{}:
              Eq.bit.absurd2(&2, {T.read.once2(T.lex.kq.go(False{}, False{}, True{}, True{},
                M3.qs(hd, rw, hs, he, ps, sk, ab, back, buf), Chr{uu}, qs.close(hd), M3.qs.lex(hd)))
                == M3.qs(hd, rw, hs, he, ps, sk, ab, back, Chr{uu} <> buf) : T.St}, hn)
            case False{}:
              qs.char(Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), uu, hd, rw, hs, he, ps, sk, ab, back, buf,
                hc)

# the fast step pushes a character
def qs.Fast(
  +uu: U32,
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>
) -> Type:
  {T.read.fast(M3.qs(hd, rw, hs, he, ps, sk, ab, back, buf), Chr{uu})
    == M3.qs(hd, rw, hs, he, ps, sk, ab, back, Chr{uu} <> buf) : T.St}

# the doc.scan dispatch sends such a character to the fast step, and an
# apostrophe comes back from doc.wrap in the segment's state
def qs.q(
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
  +buf: List<&2, Char>,
  hq: {dq == False{} : Bool},
  hr: {cr == False{} : Bool},
  fast: qs.Fast(uu, hd, rw, hs, he, ps, sk, ab, back, buf)
) -> {T.doc.scan.q(dq, sq, cr, M3.qs(hd, rw, hs, he, ps, sk, ab, back, buf), Chr{uu})
  == T.MScan{M3.qs(hd, rw, hs, he, ps, sk, ab, back, Chr{uu} <> buf)} : T.Mode}:
  match dq:
    case True{}:
      Eq.bit.absurd2(&2, {T.doc.scan.q(True{}, sq, cr, M3.qs(hd, rw, hs, he, ps, sk, ab, back, buf), Chr{uu})
        == T.MScan{M3.qs(hd, rw, hs, he, ps, sk, ab, back, Chr{uu} <> buf)} : T.Mode}, hq)
    case False{}:
      match sq:
        case True{}:
          Equal.trans(T.Mode, T.doc.wrap(T.read.fast(M3.qs(hd, rw, hs, he, ps, sk, ab, back, buf), Chr{uu})),
            T.doc.wrap(M3.qs(hd, rw, hs, he, ps, sk, ab, back, Chr{uu} <> buf)),
            T.MScan{M3.qs(hd, rw, hs, he, ps, sk, ab, back, Chr{uu} <> buf)},
            Equal.cong(T.St, T.Mode, st => T.doc.wrap(st),
              T.read.fast(M3.qs(hd, rw, hs, he, ps, sk, ab, back, buf), Chr{uu}),
              M3.qs(hd, rw, hs, he, ps, sk, ab, back, Chr{uu} <> buf), fast),
            qs.wrap(hd, rw, hs, he, ps, sk, ab, back, Chr{uu} <> buf))
        case False{}:
          match cr:
            case True{}:
              Eq.bit.absurd2(&2, {T.doc.scan.q(False{}, False{}, True{}, M3.qs(hd, rw, hs, he, ps, sk, ab, back, buf),
                Chr{uu}) == T.MScan{M3.qs(hd, rw, hs, he, ps, sk, ab, back, Chr{uu} <> buf)} : T.Mode}, hr)
            case False{}:
              Equal.cong(T.St, T.Mode, st => T.MScan{st},
                T.read.fast(M3.qs(hd, rw, hs, he, ps, sk, ab, back, buf), Chr{uu}),
                M3.qs(hd, rw, hs, he, ps, sk, ab, back, Chr{uu} <> buf), fast)

# a character written as itself is pushed, and back stays where it was
def qs.plain(
  +uu: U32,
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>,
  +rest: String,
  +goal: T.Doc,
  +e34: {U32.is_eq(uu, 34) == False{} : Bool},
  +e92: {U32.is_eq(uu, 92) == False{} : Bool},
  +ec: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool},
  ih: @bk: T.Lex -> {T.doc.read(rest, T.MScan{M3.qs(hd, rw, hs, he, ps, sk, ab, bk, Chr{uu} <> buf)}) == goal : T.Doc}
) -> {T.doc.read(String.append(L1.esc(Chr{uu}), rest), T.MScan{M3.qs(hd, rw, hs, he, ps, sk, ab, back, buf)})
  == goal : T.Doc}:
  +e10 = {M1.ctl.off(uu, 10, ec, {==}) : {U32.is_eq(uu, 10) == False{} : Bool}}
  +e13 = {M1.ctl.off(uu, 13, ec, {==}) : {U32.is_eq(uu, 13) == False{} : Bool}}
  ek = M1.cls.plain(uu, M1.ctl.off(uu, 8, ec, {==}), M1.ctl.off(uu, 9, ec, {==}), e10,
    M1.ctl.off(uu, 12, ec, {==}), e13, e34, e92, ec)
  %Equal.sym(T.BK, T.basic.cls(uu), T.BKCh{}, ek) : {T.doc.read(String.append(
    String.from_list(List.reverse(&2, Char, T.basic.disp(_, Chr{uu}, uu, []))), rest),
    T.MScan{M3.qs(hd, rw, hs, he, ps, sk, ab, back, buf)}) == goal : T.Doc}
  Equal.trans(T.Doc,
    T.doc.read(rest, T.doc.scan(M3.qs(hd, rw, hs, he, ps, sk, ab, back, buf), Chr{uu})),
    T.doc.read(rest, T.MScan{M3.qs(hd, rw, hs, he, ps, sk, ab, back, Chr{uu} <> buf)}),
    goal,
    Equal.cong(T.Mode, T.Doc, md => T.doc.read(rest, md),
      T.doc.scan(M3.qs(hd, rw, hs, he, ps, sk, ab, back, buf), Chr{uu}),
      T.MScan{M3.qs(hd, rw, hs, he, ps, sk, ab, back, Chr{uu} <> buf)},
      qs.q(U32.is_eq(uu, 34), U32.is_eq(uu, 39), U32.is_eq(uu, 13), uu, hd, rw, hs, he, ps, sk, ab, back, buf, e34,
        e13, Equal.trans(T.St, T.read.fast(M3.qs(hd, rw, hs, he, ps, sk, ab, back, buf), Chr{uu}),
          T.read.once2(T.lex.kq.go(U32.is_eq(uu, 34), U32.is_eq(uu, 92), True{},
            Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)), M3.qs(hd, rw, hs, he, ps, sk, ab, back, buf), Chr{uu},
            qs.close(hd), M3.qs.lex(hd))),
          M3.qs(hd, rw, hs, he, ps, sk, ab, back, Chr{uu} <> buf),
          qs.fast(uu, hd, rw, hs, he, ps, sk, ab, back, buf),
          qs.go(U32.is_eq(uu, 34), U32.is_eq(uu, 92), Bool.or(U32.is_eq(uu, 10),
            U32.is_eq(uu, 13)), uu, hd, rw, hs, he, ps, sk, ab, back, buf, e34, e92, M4.or.ff(U32.is_eq(uu, 10),
            U32.is_eq(uu, 13), e10, e13), ec)))),
    ih(back))

# a quotation mark: its escape reads back by computation, and leaves back at
# the segment's state
def qs.q34(
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>,
  +rest: String,
  +goal: T.Doc
) -> qs.Goal(34, hd, rw, hs, he, ps, sk, ab, back, buf, rest, goal):
  match hd:
    case False{}:
      ih => ih(T.LKeyQ{})
    case True{}:
      ih => ih(T.LHeadQ{})

# and a backslash
def qs.q92(
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>,
  +rest: String,
  +goal: T.Doc
) -> qs.Goal(92, hd, rw, hs, he, ps, sk, ab, back, buf, rest, goal):
  match hd:
    case False{}:
      ih => ih(T.LKeyQ{})
    case True{}:
      ih => ih(T.LHeadQ{})

# CTL: qs.Goal with the escape's text as ss, for ctl.esc.all
def qs.GoalS(
  +uu: U32,
  ss: String,
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>,
  +rest: String,
  +goal: T.Doc
) -> Type:
  (@bk: T.Lex -> {T.doc.read(rest, T.MScan{M3.qs(hd, rw, hs, he, ps, sk, ab, bk, Chr{uu} <> buf)}) == goal
    : T.Doc}) ->
    {T.doc.read(String.append(ss, rest), T.MScan{M3.qs(hd, rw, hs, he, ps, sk, ab, back, buf)}) == goal : T.Doc}

# a control: each of the thirty-three escapes reads back by computation, and
# leaves back at the segment's state
def qs.ctl(
  +uu: U32,
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>,
  +rest: String,
  +goal: T.Doc,
  h_c: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == True{} : Bool}
) -> qs.Goal(uu, hd, rw, hs, he, ps, sk, ab, back, buf, rest, goal):
  match hd:
    case False{}:
      M1.ctl.esc.all(kk => ss => qs.GoalS(kk, ss, False{}, rw, hs, he, ps, sk, ab, back, buf, rest, goal), uu,
        h_c,
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}),
        ih => ih(T.LKeyQ{}))
    case True{}:
      M1.ctl.esc.all(kk => ss => qs.GoalS(kk, ss, True{}, rw, hs, he, ps, sk, ab, back, buf, rest, goal), uu,
        h_c,
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}),
        ih => ih(T.LHeadQ{}))

# one code point k that the test found: its answer answers for the character
def qs.is(
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
  +buf: List<&2, Char>,
  +rest: String,
  +goal: T.Doc,
  at: qs.Goal(kk, hd, rw, hs, he, ps, sk, ab, back, buf, rest, goal)
) -> qs.Goal(uu, hd, rw, hs, he, ps, sk, ab, back, buf, rest, goal):
  eu = Equal.cong(Char, U32, cc => Char.to_u32(cc), Chr{uu}, Chr{kk}, Eq.u32_eq(uu, kk, ee))
  %Equal.sym(U32, uu, kk, eu) : qs.Goal(_, hd, rw, hs, he, ps, sk, ab, back, buf, rest, goal)
  at

# every character: a quote, a backslash, a control, or one written as itself
def qs.split(
  +uu: U32,
  q34: Bool,
  b92: Bool,
  ctl: Bool,
  +e34: {U32.is_eq(uu, 34) == q34 : Bool},
  +e92: {U32.is_eq(uu, 92) == b92 : Bool},
  +ec: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == ctl : Bool},
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>,
  +rest: String,
  +goal: T.Doc
) -> qs.Goal(uu, hd, rw, hs, he, ps, sk, ab, back, buf, rest, goal):
  match q34:
    case True{}:
      qs.is(uu, 34, e34, hd, rw, hs, he, ps, sk, ab, back, buf, rest, goal,
        qs.q34(hd, rw, hs, he, ps, sk, ab, back, buf, rest, goal))
    case False{}:
      match b92:
        case True{}:
          qs.is(uu, 92, e92, hd, rw, hs, he, ps, sk, ab, back, buf, rest, goal,
            qs.q92(hd, rw, hs, he, ps, sk, ab, back, buf, rest, goal))
        case False{}:
          match ctl:
            case True{}:
              qs.ctl(uu, hd, rw, hs, he, ps, sk, ab, back, buf, rest, goal, ec)
            case False{}:
              ih => qs.plain(uu, hd, rw, hs, he, ps, sk, ab, back, buf, rest, goal, e34, e92, ec, ih)

# one character of a quoted segment
def qs.one(
  +uu: U32,
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>,
  +rest: String,
  +goal: T.Doc
) -> qs.Goal(uu, hd, rw, hs, he, ps, sk, ab, back, buf, rest, goal):
  qs.split(uu, U32.is_eq(uu, 34), U32.is_eq(uu, 92), Bool.or(U32.is_lt(uu, 32),
    U32.is_eq(uu, 127)), {==}, {==}, {==}, hd, rw, hs, he, ps, sk, ab, back, buf, rest, goal)

# every character of a name, as escs writes it, read from a quoted segment:
# the rest is read with the name's characters pushed, from wherever the last
# escape left back
def qs.escs(
  ss: String,
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>,
  +rest: String,
  +goal: T.Doc,
  ih: @bk: T.Lex -> {T.doc.read(rest, T.MScan{M3.qs(hd, rw, hs, he, ps, sk, ab, bk, M2.rev.onto(ss, buf))}) == goal : T.Doc}  # noqa: S002
) -> {T.doc.read(String.append(L1.escs(ss), rest), T.MScan{M3.qs(hd, rw, hs, he, ps, sk, ab, back, buf)}) == goal
  : T.Doc}:
  match ss:
    case SNil{}:
      ih(back)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+uu}:
          Equal.trans(T.Doc,
            T.doc.read(String.append(String.append(L1.esc(Chr{uu}), L1.escs(tt)), rest),
              T.MScan{M3.qs(hd, rw, hs, he, ps, sk, ab, back, buf)}),
            T.doc.read(String.append(L1.esc(Chr{uu}), String.append(L1.escs(tt), rest)),
              T.MScan{M3.qs(hd, rw, hs, he, ps, sk, ab, back, buf)}),
            goal,
            Equal.cong(String, T.Doc, xs => T.doc.read(xs, T.MScan{M3.qs(hd, rw, hs, he, ps, sk, ab, back, buf)}),
              String.append(String.append(L1.esc(Chr{uu}), L1.escs(tt)), rest),
              String.append(L1.esc(Chr{uu}), String.append(L1.escs(tt), rest)),
              Eq.append_assoc(L1.esc(Chr{uu}), L1.escs(tt), rest)),
            qs.one(uu, hd, rw, hs, he, ps, sk, ab, back, buf, String.append(L1.escs(tt), rest), goal)(
              bk => qs.escs(tt, hd, rw, hs, he, ps, sk, ab, bk, Chr{uu} <> buf, rest, goal, ih)))

# a buffer of a name's characters names the pair by the name
def kq.name(
  +ss: String
) -> {kq.doc(M2.rev.onto(ss, [])) == T.Doc{"", [T.VPair{ss, T.VInt{T.Plus{}, "1"}}]} : T.Doc}:
  Equal.cong(String, T.Doc, nm => T.Doc{"", [T.VPair{nm, T.VInt{T.Plus{}, "1"}}]},
    T.buf.str.go(M2.rev.onto(ss, []), ""), ss,
    Equal.trans(String, T.buf.str.go(M2.rev.onto(ss, []), ""), String.append(ss, ""), ss,
      M4.ml.rev(ss, [], ""), Eq.append_nil(ss)))
