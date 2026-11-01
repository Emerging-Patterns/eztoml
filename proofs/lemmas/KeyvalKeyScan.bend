# the scanner reading a key's segments in a keyval or inline table
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/KeyNameIsItsCharacters.bend as L1
import ../../laws/defs/BlankAndControlChars.bend as D1
import ./FreshNamesInRows.bend as M1
import ./HeaderKeyScan.bend as M2
import ./HeaderSegmentWalk.bend as M3
import ./StringEqualsItself.bend as M4
import ./ValueTextReadback.bend as M5

# where a key segment starts: where a key may start, or after a dot
def k3.lex0(dt: Bool, at: L1.KPos) -> T.Lex:
  match dt:
    case False{}:
      L1.k3.pos.lex(at)
    case True{}:
      T.LKeyDot{}

# what ends a segment and its blank space: a dot, or `=` when cl
def k3.dl(cl: Bool) -> Char:
  match cl:
    case False{}:
      '.'
    case True{}:
      '='

# the state after it: waiting for the next segment, or for the value
def k3.aft(cl: Bool) -> T.Lex:
  match cl:
    case False{}:
      T.LKeyDot{}
    case True{}:
      T.LVal{}

# blank space after a segment stays in LAfter
def k3.agap(
  gs: List<&2, Bool>,
  +rr: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool
) -> {T.doc.read(rr, T.MScan{M2.k3.w(rw, hs, he, ps, [], T.LAfter{}, bk, qk, sk, un, lf, ab)})
  == T.doc.read(String.append(D1.gap(gs), rr), T.MScan{M2.k3.w(rw, hs, he, ps, [], T.LAfter{}, bk, qk, sk, un, lf,
  ab)}) : T.Doc}:
  match gs:
    case []:
      {==}
    case tab <> rest:
      match tab:
        case True{}:
          k3.agap(rest, rr, rw, hs, he, ps, bk, qk, sk, un, lf, ab)
        case False{}:
          k3.agap(rest, rr, rw, hs, he, ps, bk, qk, sk, un, lf, ab)

# and blank space after a dot stays in LKeyDot
def k3.dgap(
  gs: List<&2, Bool>,
  +rr: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool
) -> {T.doc.read(rr, T.MScan{M2.k3.w(rw, hs, he, ps, [], T.LKeyDot{}, bk, qk, sk, un, lf, ab)})
  == T.doc.read(String.append(D1.gap(gs), rr), T.MScan{M2.k3.w(rw, hs, he, ps, [], T.LKeyDot{}, bk, qk, sk, un, lf,
  ab)}) : T.Doc}:
  match gs:
    case []:
      {==}
    case tab <> rest:
      match tab:
        case True{}:
          k3.dgap(rest, rr, rw, hs, he, ps, bk, qk, sk, un, lf, ab)
        case False{}:
          k3.dgap(rest, rr, rw, hs, he, ps, bk, qk, sk, un, lf, ab)

# a dot or `=` after a segment's blank space
def k3.adl(
  +cl: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String
) -> {T.doc.read(rest, T.MScan{M2.k3.w(rw, hs, he, ps, [], k3.aft(cl), bk, qk, sk, un, lf, ab)})
  == T.doc.read(SCon{k3.dl(cl), rest}, T.MScan{M2.k3.w(rw, hs, he, ps, [], T.LAfter{}, bk, qk, sk, un, lf, ab)})
  : T.Doc}:
  match cl:
    case False{}:
      {==}
    case True{}:
      {==}

# a character that is no blank and no newline takes the full step
def k3.ws(
  sp: Bool,
  nl: Bool,
  keep: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +buf: List<&2, Char>,
  +lex: T.Lex,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +cc: Char,
  hs0: {sp == False{} : Bool},
  hn: {nl == False{} : Bool}
) -> {T.read.fast.old("", rw, hs, he, ps, buf, lex, bk, qk, sk, un, lf, ab, cc)
  == T.read.fast.ws(sp, nl, keep, "", rw, hs, he, ps, buf, lex, bk, qk, sk, un, lf, ab, cc) : T.St}:
  match sp nl:
    case False{} False{}:
      {==}
    case True{} n2:
      Eq.bit.absurd2(&2, {T.read.fast.old("", rw, hs, he, ps, buf, lex, bk, qk, sk, un, lf, ab, cc)
        == T.read.fast.ws(True{}, n2, keep, "", rw, hs, he, ps, buf, lex, bk, qk, sk, un, lf, ab, cc) : T.St}, hs0)
    case False{} True{}:
      Eq.bit.absurd2(&2, {T.read.fast.old("", rw, hs, he, ps, buf, lex, bk, qk, sk, un, lf, ab, cc)
        == T.read.fast.ws(False{}, True{}, keep, "", rw, hs, he, ps, buf, lex, bk, qk, sk, un, lf, ab, cc) : T.St}, hn)

# a bare character starts an inline table's key: the last of the tests
def k3.kbare(
  ok: Bool,
  st: T.St,
  +xx: U32,
  eok: {T.bare.at(Chr{xx}) == ok : Bool},
  ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.lex.key.bare(ok, st, Chr{xx}) == T.st.push(st, Chr{xx}, T.LKey{}) : T.St}:
  match ok:
    case True{}:
      {==}
    case False{}:
      M4.clash(&2, {T.lex.key.bare(False{}, st, Chr{xx}) == T.st.push(st, Chr{xx}, T.LKey{}) : T.St},
        Equal.trans(Bool, False{}, T.bare.at(Chr{xx}), True{}, Equal.sym(Bool, T.bare.at(Chr{xx}), False{}, eok), ee))

# no apostrophe
def k3.klit(
  lit: Bool,
  st: T.St,
  +xx: U32,
  elit: {Char.is_eq(Chr{xx}, '\'') == lit : Bool},
  +ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.lex.key.lit(lit, st, Chr{xx}) == T.st.push(st, Chr{xx}, T.LKey{}) : T.St}:
  match lit:
    case True{}:
      Eq.bit.gone(&2, {T.lex.key.lit(True{}, st, Chr{xx}) == T.st.push(st, Chr{xx}, T.LKey{}) : T.St},
        Eq.refute_char(Chr{xx}, '\'', ch => T.bare.at(ch), elit, ee, {==}))
    case False{}:
      k3.kbare(T.bare.at(Chr{xx}), st, xx, {==}, ee)

# no quotation mark
def k3.kq(
  qq: Bool,
  st: T.St,
  +xx: U32,
  eqq: {Char.is_eq(Chr{xx}, '"') == qq : Bool},
  +ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.lex.key.q(qq, st, Chr{xx}) == T.st.push(st, Chr{xx}, T.LKey{}) : T.St}:
  match qq:
    case True{}:
      Eq.bit.gone(&2, {T.lex.key.q(True{}, st, Chr{xx}) == T.st.push(st, Chr{xx}, T.LKey{}) : T.St},
        Eq.refute_char(Chr{xx}, '"', ch => T.bare.at(ch), eqq, ee, {==}))
    case False{}:
      k3.klit(Char.is_eq(Chr{xx}, '\''), st, xx, {==}, ee)

# in an inline table a bare character is no blank, no comment, no `}` and no
# newline, so it starts a key
def k3.inl.go(
  sp: Bool,
  hash: Bool,
  end: Bool,
  nl: Bool,
  st: T.St,
  +xx: U32,
  esp: {T.ch.sp(Chr{xx}) == sp : Bool},
  ehash: {Char.is_eq(Chr{xx}, '#') == hash : Bool},
  eend: {Char.is_eq(Chr{xx}, '}') == end : Bool},
  enl: {T.ch.nl(Chr{xx}) == nl : Bool},
  +ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.lex.inl.go(sp, hash, end, nl, st, Chr{xx}) == T.st.push(T.lex.key.clear(st), Chr{xx}, T.LKey{}) : T.St}:
  match sp:
    case True{}:
      Eq.bit.gone(&2, {T.lex.inl.go(True{}, hash, end, nl, st, Chr{xx}) == T.st.push(T.lex.key.clear(st), Chr{xx},
        T.LKey{}) : T.St}, M5.or2.no(xx, 32, 9, U32.is_eq(xx, 32), U32.is_eq(xx, 9), {==}, {==}, esp,
        ch => T.bare.at(ch), ee, {==}, {==}))
    case False{}:
      match hash:
        case True{}:
          Eq.bit.gone(&2, {T.lex.inl.go(False{}, True{}, end, nl, st, Chr{xx}) == T.st.push(T.lex.key.clear(st),
            Chr{xx}, T.LKey{}) : T.St}, Eq.refute_char(Chr{xx}, '#', ch => T.bare.at(ch), ehash, ee, {==}))
        case False{}:
          match end:
            case True{}:
              Eq.bit.gone(&2, {T.lex.inl.go(False{}, False{}, True{}, nl, st, Chr{xx})
                == T.st.push(T.lex.key.clear(st), Chr{xx}, T.LKey{}) : T.St},
                Eq.refute_char(Chr{xx}, '}', ch => T.bare.at(ch), eend, ee, {==}))
            case False{}:
              match nl:
                case True{}:
                  Eq.bit.gone(&2, {T.lex.inl.go(False{}, False{}, False{}, True{}, st, Chr{xx})
                    == T.st.push(T.lex.key.clear(st), Chr{xx}, T.LKey{}) : T.St},
                    M5.or2.no(xx, 10, 13, U32.is_eq(xx, 10), U32.is_eq(xx, 13), {==}, {==}, enl, ch => T.bare.at(ch),
                      ee, {==}, {==}))
                case False{}:
                  k3.kq(Char.is_eq(Chr{xx}, '"'), T.lex.key.clear(st), xx, {==}, ee)

# and after a comma in one: no blank, no comment and no newline
def k3.inlk.go(
  sp: Bool,
  hash: Bool,
  nl: Bool,
  st: T.St,
  +xx: U32,
  esp: {T.ch.sp(Chr{xx}) == sp : Bool},
  ehash: {Char.is_eq(Chr{xx}, '#') == hash : Bool},
  enl: {T.ch.nl(Chr{xx}) == nl : Bool},
  +ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.lex.inlk.go(sp, hash, nl, st, Chr{xx}) == T.st.push(T.lex.key.clear(st), Chr{xx}, T.LKey{}) : T.St}:
  match sp:
    case True{}:
      Eq.bit.gone(&2, {T.lex.inlk.go(True{}, hash, nl, st, Chr{xx}) == T.st.push(T.lex.key.clear(st), Chr{xx},
        T.LKey{}) : T.St}, M5.or2.no(xx, 32, 9, U32.is_eq(xx, 32), U32.is_eq(xx, 9), {==}, {==}, esp,
        ch => T.bare.at(ch), ee, {==}, {==}))
    case False{}:
      match hash:
        case True{}:
          Eq.bit.gone(&2, {T.lex.inlk.go(False{}, True{}, nl, st, Chr{xx}) == T.st.push(T.lex.key.clear(st),
            Chr{xx}, T.LKey{}) : T.St}, Eq.refute_char(Chr{xx}, '#', ch => T.bare.at(ch), ehash, ee, {==}))
        case False{}:
          match nl:
            case True{}:
              Eq.bit.gone(&2, {T.lex.inlk.go(False{}, False{}, True{}, st, Chr{xx})
                == T.st.push(T.lex.key.clear(st), Chr{xx}, T.LKey{}) : T.St},
                M5.or2.no(xx, 10, 13, U32.is_eq(xx, 10), U32.is_eq(xx, 13), {==}, {==}, enl, ch => T.bare.at(ch),
                  ee, {==}, {==}))
            case False{}:
              k3.kq(Char.is_eq(Chr{xx}, '"'), T.lex.key.clear(st), xx, {==}, ee)

# the first character of a bare segment after a dot starts its buffer
def k3.b1.dot(
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +xx: U32,
  +ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.MScan{M2.k3.w(rw, hs, he, ps, [Chr{xx}], T.LKey{}, bk, qk, sk, un, lf, ab)} == T.doc.scan(M2.k3.w(rw, hs, he,
    ps,
  [], T.LKeyDot{}, bk, qk, sk, un, lf, ab), Chr{xx}) : T.Mode}:
  %M2.k3.so(M2.k3.w(rw, hs, he, ps, [], T.LKeyDot{}, bk, qk, sk, un, lf, ab), xx, ee) : {T.MScan{M2.k3.w(rw, hs, he, ps,
    [Chr{xx}], T.LKey{}, bk, qk, sk, un, lf, ab)} == _ : T.Mode}
  Equal.cong(T.St, T.Mode, st => T.MScan{T.read.once2(st)}, T.st.push(M2.k3.w(rw, hs, he, ps, [], T.LKeyDot{}, bk, qk,
    sk, un, lf, ab), Chr{xx}, T.LKey{}),
    T.lex.kdot.go(T.ch.sp(Chr{xx}), Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), Char.is_eq(Chr{xx}, '.'),
      T.ch.nl(Chr{xx}), M2.k3.w(rw, hs, he, ps, [], T.LKeyDot{}, bk, qk, sk, un, lf, ab), Chr{xx}),
    Equal.sym(T.St, T.lex.kdot.go(T.ch.sp(Chr{xx}), Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''),
      Char.is_eq(Chr{xx}, '.'), T.ch.nl(Chr{xx}), M2.k3.w(rw, hs, he, ps, [], T.LKeyDot{}, bk, qk, sk, un, lf, ab),
        Chr{xx}), T.st.push(M2.k3.w(rw, hs, he, ps, [], T.LKeyDot{}, bk, qk, sk, un, lf, ab), Chr{xx}, T.LKey{}),
      M3.kd.bare(T.ch.sp(Chr{xx}), Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), Char.is_eq(Chr{xx}, '.'),
        T.ch.nl(Chr{xx}), M2.k3.w(rw, hs, he, ps, [], T.LKeyDot{}, bk, qk, sk, un, lf, ab), xx, {==}, {==}, {==}, ee)))

# at the start of a line, the first character of a bare key starts its
# buffer
def k3.b1.top(
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +xx: U32,
  +ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.MScan{M2.k3.w(rw, hs, he, [], [Chr{xx}], T.LKey{}, bk, qk, sk, un, lf, ab)} == T.doc.scan(M2.k3.w(rw, hs, he,
    [],
  [], T.LTop{}, bk, qk, sk, un, lf, ab), Chr{xx}) : T.Mode}:
  %M2.k3.so(M2.k3.w(rw, hs, he, [], [], T.LTop{}, bk, qk, sk, un, lf, ab), xx, ee) : {T.MScan{M2.k3.w(rw, hs, he, [],
    [Chr{xx}], T.LKey{}, bk, qk, sk, un, lf, ab)} == _ : T.Mode}
  %k3.ws(T.ch.sp(Chr{xx}), T.ch.nl(Chr{xx}), True{}, rw, hs, he, [], [], T.LTop{}, bk, qk, sk, un, lf, ab, Chr{xx},
    M3.kl.no2(T.ch.sp(Chr{xx}), xx, 32, 9, {==}, ee, {==}, {==}), M3.kl.no2(T.ch.nl(Chr{xx}), xx, 10, 13, {==}, ee,
        {==},
    {==})) : {T.MScan{M2.k3.w(rw, hs, he, [], [Chr{xx}], T.LKey{}, bk, qk, sk, un, lf, ab)} == T.MScan{_} : T.Mode}
  Equal.cong(T.St, T.Mode, st => T.MScan{T.read.once2(st)}, T.st.push(M2.k3.w(rw, hs, he, [], [], T.LTop{}, bk, qk, sk,
    un, lf, ab), Chr{xx}, T.LKey{}),
    T.lex.top.go(T.ch.sp(Chr{xx}), T.ch.nl(Chr{xx}), Char.is_eq(Chr{xx}, '#'), Char.is_eq(Chr{xx}, '['),
      Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), T.bare.at(Chr{xx}), M2.k3.w(rw, hs, he, [], [], T.LTop{}, bk,
        qk, sk, un, lf, ab), Chr{xx}),
    Equal.sym(T.St, T.lex.top.go(T.ch.sp(Chr{xx}), T.ch.nl(Chr{xx}), Char.is_eq(Chr{xx}, '#'),
      Char.is_eq(Chr{xx}, '['), Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), T.bare.at(Chr{xx}), M2.k3.w(rw, hs,
        he, [], [], T.LTop{}, bk, qk, sk, un, lf, ab),
      Chr{xx}), T.st.push(M2.k3.w(rw, hs, he, [], [], T.LTop{}, bk, qk, sk, un, lf, ab), Chr{xx}, T.LKey{}),
      M5.key.top(T.ch.sp(Chr{xx}), T.ch.nl(Chr{xx}), Char.is_eq(Chr{xx}, '#'), Char.is_eq(Chr{xx}, '['),
        Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), T.bare.at(Chr{xx}), M2.k3.w(rw, hs, he, [], [], T.LTop{},
          bk, qk, sk, un, lf, ab), xx, {==}, {==}, {==}, {==},
        {==}, {==}, {==}, ee)))

# after an inline table's `{`, the first character of a bare key starts its
# buffer
def k3.b1.inl(
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +xx: U32,
  +ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.MScan{M2.k3.w(rw, hs, he, [], [Chr{xx}], T.LKey{}, bk, qk, sk, un, lf, ab)} == T.doc.scan(M2.k3.w(rw, hs, he,
    [],
  [], T.LInl{}, bk, qk, sk, un, lf, ab), Chr{xx}) : T.Mode}:
  %M2.k3.so(M2.k3.w(rw, hs, he, [], [], T.LInl{}, bk, qk, sk, un, lf, ab), xx, ee) : {T.MScan{M2.k3.w(rw, hs, he, [],
    [Chr{xx}], T.LKey{}, bk, qk, sk, un, lf, ab)} == _ : T.Mode}
  %k3.ws(T.ch.sp(Chr{xx}), T.ch.nl(Chr{xx}), False{}, rw, hs, he, [], [], T.LInl{}, bk, qk, sk, un, lf, ab, Chr{xx},
    M3.kl.no2(T.ch.sp(Chr{xx}), xx, 32, 9, {==}, ee, {==}, {==}), M3.kl.no2(T.ch.nl(Chr{xx}), xx, 10, 13, {==}, ee,
        {==},
    {==})) : {T.MScan{M2.k3.w(rw, hs, he, [], [Chr{xx}], T.LKey{}, bk, qk, sk, un, lf, ab)} == T.MScan{_} : T.Mode}
  Equal.cong(T.St, T.Mode, st => T.MScan{T.read.once2(st)}, T.st.push(T.lex.key.clear(M2.k3.w(rw, hs, he, [], [],
    T.LInl{}, bk, qk, sk, un, lf, ab)), Chr{xx}, T.LKey{}),
    T.lex.inl.go(T.ch.sp(Chr{xx}), Char.is_eq(Chr{xx}, '#'), Char.is_eq(Chr{xx}, '}'), T.ch.nl(Chr{xx}), M2.k3.w(rw, hs,
      he, [], [], T.LInl{}, bk, qk, sk, un, lf, ab),
      Chr{xx}),
    Equal.sym(T.St, T.lex.inl.go(T.ch.sp(Chr{xx}), Char.is_eq(Chr{xx}, '#'), Char.is_eq(Chr{xx}, '}'),
      T.ch.nl(Chr{xx}), M2.k3.w(rw, hs, he, [], [], T.LInl{}, bk, qk, sk, un, lf, ab), Chr{xx}),
        T.st.push(T.lex.key.clear(M2.k3.w(rw, hs, he, [], [], T.LInl{}, bk, qk, sk, un, lf, ab)), Chr{xx}, T.LKey{}),
      k3.inl.go(T.ch.sp(Chr{xx}), Char.is_eq(Chr{xx}, '#'), Char.is_eq(Chr{xx}, '}'), T.ch.nl(Chr{xx}), M2.k3.w(rw, hs,
        he, [], [], T.LInl{}, bk, qk, sk, un, lf, ab), xx,
        {==}, {==}, {==}, {==}, ee)))

# and after a comma in one
def k3.b1.inlk(
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +xx: U32,
  +ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.MScan{M2.k3.w(rw, hs, he, [], [Chr{xx}], T.LKey{}, bk, qk, sk, un, lf, ab)} == T.doc.scan(M2.k3.w(rw, hs, he,
    [],
  [], T.LInlK{}, bk, qk, sk, un, lf, ab), Chr{xx}) : T.Mode}:
  %M2.k3.so(M2.k3.w(rw, hs, he, [], [], T.LInlK{}, bk, qk, sk, un, lf, ab), xx, ee) : {T.MScan{M2.k3.w(rw, hs, he, [],
    [Chr{xx}], T.LKey{}, bk, qk, sk, un, lf, ab)} == _ : T.Mode}
  %k3.ws(T.ch.sp(Chr{xx}), T.ch.nl(Chr{xx}), False{}, rw, hs, he, [], [], T.LInlK{}, bk, qk, sk, un, lf, ab, Chr{xx},
    M3.kl.no2(T.ch.sp(Chr{xx}), xx, 32, 9, {==}, ee, {==}, {==}), M3.kl.no2(T.ch.nl(Chr{xx}), xx, 10, 13, {==}, ee,
        {==},
    {==})) : {T.MScan{M2.k3.w(rw, hs, he, [], [Chr{xx}], T.LKey{}, bk, qk, sk, un, lf, ab)} == T.MScan{_} : T.Mode}
  Equal.cong(T.St, T.Mode, st => T.MScan{T.read.once2(st)}, T.st.push(T.lex.key.clear(M2.k3.w(rw, hs, he, [], [],
    T.LInlK{}, bk, qk, sk, un, lf, ab)), Chr{xx}, T.LKey{}),
    T.lex.inlk.go(T.ch.sp(Chr{xx}), Char.is_eq(Chr{xx}, '#'), T.ch.nl(Chr{xx}), M2.k3.w(rw, hs, he, [], [], T.LInlK{},
      bk, qk, sk, un, lf, ab), Chr{xx}),
    Equal.sym(T.St, T.lex.inlk.go(T.ch.sp(Chr{xx}), Char.is_eq(Chr{xx}, '#'), T.ch.nl(Chr{xx}), M2.k3.w(rw, hs, he, [],
      [], T.LInlK{}, bk, qk, sk, un, lf, ab), Chr{xx}),
      T.st.push(T.lex.key.clear(M2.k3.w(rw, hs, he, [], [], T.LInlK{}, bk, qk, sk, un, lf, ab)), Chr{xx}, T.LKey{}),
      k3.inlk.go(T.ch.sp(Chr{xx}), Char.is_eq(Chr{xx}, '#'), T.ch.nl(Chr{xx}), M2.k3.w(rw, hs, he, [], [], T.LInlK{},
          bk,
        qk, sk, un, lf, ab), xx, {==}, {==}, {==}, ee)))

# the first character of a bare segment starts its buffer, wherever the
# segment starts
def k3.b1(
  +dt: Bool,
  +at: L1.KPos,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +xx: U32,
  +ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.MScan{M2.k3.w(rw, hs, he, M2.k3.ps0(dt, ps), [Chr{xx}], T.LKey{}, bk, qk, sk, un, lf,
    ab)} == T.doc.scan(M2.k3.w(rw,
  hs, he, M2.k3.ps0(dt, ps), [], k3.lex0(dt, at), bk, qk, sk, un, lf, ab), Chr{xx}) : T.Mode}:
  match dt:
    case True{}:
      k3.b1.dot(rw, hs, he, ps, bk, qk, sk, un, lf, ab, xx, ee)
    case False{}:
      match at:
        case L1.AtLine{}:
          k3.b1.top(rw, hs, he, bk, qk, sk, un, lf, ab, xx, ee)
        case L1.AtInl{}:
          k3.b1.inl(rw, hs, he, bk, qk, sk, un, lf, ab, xx, ee)
        case L1.AtInlK{}:
          k3.b1.inlk(rw, hs, he, bk, qk, sk, un, lf, ab, xx, ee)

# a later bare character stays on the key's fast path
def k3.kfast(
  ok: Bool,
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
  +xx: U32,
  eok: {T.bare.at(Chr{xx}) == ok : Bool},
  ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {M2.k3.w(rw, hs, he, ps, Chr{xx} <> buf, T.LKey{}, bk, qk, sk, un, lf, ab) == T.read.fast.key(ok, "", rw, hs, he,
  ps, buf, bk, qk, sk, un, lf, ab, Chr{xx}) : T.St}:
  match ok:
    case True{}:
      {==}
    case False{}:
      M4.clash(&2, {M2.k3.w(rw, hs, he, ps, Chr{xx} <> buf, T.LKey{}, bk, qk, sk, un, lf,
          ab) == T.read.fast.key(False{},
        "", rw, hs, he, ps, buf, bk, qk, sk, un, lf, ab, Chr{xx}) : T.St},
        Equal.trans(Bool, False{}, T.bare.at(Chr{xx}), True{}, Equal.sym(Bool, T.bare.at(Chr{xx}), False{}, eok), ee))

# the rest of a bare segment is pushed onto its buffer, whatever follows it
def k3.bbody(
  ks: String,
  +rr: String,
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
  +ee: {T.bare.all(String.to_list(ks)) == True{} : Bool}
) -> {T.doc.read(rr, T.MScan{M2.k3.w(rw, hs, he, ps, M1.rev.onto(ks, buf), T.LKey{}, bk, qk, sk, un, lf,
  ab)}) == T.doc.read(String.append(ks, rr), T.MScan{M2.k3.w(rw, hs, he, ps, buf, T.LKey{}, bk, qk, sk, un, lf,
    ab)}) : T.Doc}:
  match ks:
    case SNil{}:
      {==}
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          %M2.k3.so(M2.k3.w(rw, hs, he, ps, buf, T.LKey{}, bk, qk, sk, un, lf, ab), xx, M5.ball.head(T.bare.at(Chr{xx}),
            String.to_list(tt), ee)) : {T.doc.read(rr, T.MScan{M2.k3.w(rw, hs, he, ps, M1.rev.onto(tt, Chr{xx} <> buf),
              T.LKey{}, bk, qk, sk, un, lf, ab)})
            == T.doc.read(String.append(tt, rr), _) : T.Doc}
          %k3.kfast(T.bare.at(Chr{xx}), rw, hs, he, ps, buf, bk, qk, sk, un, lf, ab, xx, {==},
            M5.ball.head(T.bare.at(Chr{xx}),
            String.to_list(tt), ee)) : {T.doc.read(rr, T.MScan{M2.k3.w(rw, hs, he, ps, M1.rev.onto(tt, Chr{xx} <> buf),
              T.LKey{}, bk, qk, sk, un, lf, ab)}) == T.doc.read(String.append(tt, rr), T.MScan{_})
            : T.Doc}
          k3.bbody(tt, rr, rw, hs, he, ps, Chr{xx} <> buf, bk, qk, sk, un, lf, ab, M5.ball.tail(T.bare.at(Chr{xx}),
            String.to_list(tt), ee))

# a blank ends an open bare segment: it is pushed, and the scanner waits in
# LAfter
def k3.bsp(
  +tab: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bf: List<&2, Char>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rr: String,
  full: {List.is_empty(&2, Char, bf) == False{} : Bool}
) -> {T.doc.read(rr, T.MScan{M2.k3.w(rw, hs, he, T.buf.str(bf) <> ps, [], T.LAfter{}, bk, qk, sk, un, lf,
  ab)}) == T.doc.read(SCon{D1.blank_char(tab), rr}, T.MScan{M2.k3.w(rw, hs, he, ps, bf, T.LKey{}, bk, qk, sk, un, lf,
    ab)}) : T.Doc}:
  match tab:
    case True{}:
      %Equal.sym(Bool, List.is_empty(&2, Char, bf), False{}, full) : {T.doc.read(rr, T.MScan{M2.k3.w(rw, hs, he,
        T.buf.str(bf) <> ps, [], T.LAfter{}, bk, qk, sk, un, lf,
        ab)}) == T.doc.read(rr, T.MScan{T.read.once2(T.lex.key.end.go(_, M2.k3.w(rw, hs, he, ps, bf, T.LKey{}, bk, qk,
          sk, un, lf, ab),
        T.LAfter{}))}) : T.Doc}
      {==}
    case False{}:
      %Equal.sym(Bool, List.is_empty(&2, Char, bf), False{}, full) : {T.doc.read(rr, T.MScan{M2.k3.w(rw, hs, he,
        T.buf.str(bf) <> ps, [], T.LAfter{}, bk, qk, sk, un, lf,
        ab)}) == T.doc.read(rr, T.MScan{T.read.once2(T.lex.key.end.go(_, M2.k3.w(rw, hs, he, ps, bf, T.LKey{}, bk, qk,
          sk, un, lf, ab),
        T.LAfter{}))}) : T.Doc}
      {==}

# a dot or `=` right after an open bare segment pushes it
def k3.bdl(
  +cl: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bf: List<&2, Char>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  full: {List.is_empty(&2, Char, bf) == False{} : Bool}
) -> {T.doc.read(rest, T.MScan{M2.k3.w(rw, hs, he, T.buf.str(bf) <> ps, [], k3.aft(cl), bk, qk, sk, un, lf,
  ab)}) == T.doc.read(SCon{k3.dl(cl), rest}, T.MScan{M2.k3.w(rw, hs, he, ps, bf, T.LKey{}, bk, qk, sk, un, lf,
    ab)}) : T.Doc}:
  match cl:
    case False{}:
      %Equal.sym(Bool, List.is_empty(&2, Char, bf), False{}, full) : {T.doc.read(rest, T.MScan{M2.k3.w(rw, hs, he,
        T.buf.str(bf) <> ps, [], T.LKeyDot{}, bk, qk, sk, un, lf,
        ab)}) == T.doc.read(rest, T.MScan{T.read.once2(T.lex.key.end.go(_, M2.k3.w(rw, hs, he, ps, bf, T.LKey{}, bk, qk,
          sk, un, lf, ab),
        T.LKeyDot{}))}) : T.Doc}
      {==}
    case True{}:
      %Equal.sym(Bool, List.is_empty(&2, Char, bf), False{}, full) : {T.doc.read(rest, T.MScan{M2.k3.w(rw, hs, he,
        T.buf.str(bf) <> ps, [], T.LVal{}, bk, qk, sk, un, lf,
        ab)}) == T.doc.read(rest, T.MScan{T.read.once2(T.lex.key.end.go(_, M2.k3.w(rw, hs, he, ps, bf, T.LKey{}, bk, qk,
          sk, un, lf, ab),
        T.LVal{}))}) : T.Doc}
      {==}

# blank space and a dot or `=` after an open bare segment push it
def k3.bend(
  gs: List<&2, Bool>,
  +cl: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bf: List<&2, Char>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  full: {List.is_empty(&2, Char, bf) == False{} : Bool}
) -> {T.doc.read(rest, T.MScan{M2.k3.w(rw, hs, he, T.buf.str(bf) <> ps, [], k3.aft(cl), bk, qk, sk, un, lf,
  ab)}) == T.doc.read(String.append(D1.gap(gs), SCon{k3.dl(cl), rest}), T.MScan{M2.k3.w(rw, hs, he, ps, bf, T.LKey{},
    bk, qk, sk, un, lf, ab)})
  : T.Doc}:
  match gs:
    case []:
      k3.bdl(cl, rw, hs, he, ps, bf, bk, qk, sk, un, lf, ab, rest, full)
    case +tab <> +gr:
      %k3.bsp(tab, rw, hs, he, ps, bf, bk, qk, sk, un, lf, ab, String.append(D1.gap(gr), SCon{k3.dl(cl), rest}),
        full) : {T.doc.read(rest, T.MScan{M2.k3.w(rw, hs, he, T.buf.str(bf) <> ps, [], k3.aft(cl), bk, qk, sk, un, lf,
          ab)}) == _ : T.Doc}
      %k3.agap(gr, SCon{k3.dl(cl), rest}, rw, hs, he, T.buf.str(bf) <> ps, bk, qk, sk, un, lf, ab)
        : {T.doc.read(rest, T.MScan{M2.k3.w(rw, hs, he, T.buf.str(bf) <> ps, [], k3.aft(cl), bk, qk, sk, un, lf,
          ab)}) == _ : T.Doc}
      k3.adl(cl, rw, hs, he, T.buf.str(bf) <> ps, bk, qk, sk, un, lf, ab, rest)

# a quotation mark where a segment starts opens a basic segment
def k3.qopen(
  +dt: Bool,
  +at: L1.KPos,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool
) -> {T.MScan{M2.k3.q(False{}, rw, hs, he, M2.k3.ps0(dt, ps), sk, ab, bk, un, lf, [])} == T.doc.scan(M2.k3.w(rw, hs, he,
  M2.k3.ps0(dt, ps), [], k3.lex0(dt, at), bk, qk, sk, un, lf, ab), '"') : T.Mode}:
  match dt:
    case True{}:
      {==}
    case False{}:
      match at:
        case L1.AtLine{}:
          {==}
        case L1.AtInl{}:
          {==}
        case L1.AtInlK{}:
          {==}

# and an apostrophe a literal one
def k3.lopen(
  +dt: Bool,
  +at: L1.KPos,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool
) -> {T.MScan{M2.k3.l(False{}, rw, hs, he, M2.k3.ps0(dt, ps), sk, ab, bk, un, lf, [])} == T.doc.scan(M2.k3.w(rw, hs, he,
  M2.k3.ps0(dt, ps), [], k3.lex0(dt, at), bk, qk, sk, un, lf, ab), '\'') : T.Mode}:
  match dt:
    case True{}:
      {==}
    case False{}:
      match at:
        case L1.AtLine{}:
          {==}
        case L1.AtInl{}:
          {==}
        case L1.AtInlK{}:
          {==}
