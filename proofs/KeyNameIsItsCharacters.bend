# proofs of laws/KeyNameIsItsCharacters.bend
import Base
import ../main.bend as T
import ../src/eq.bend as Eq
import ../laws/AotHeaderExtendsArray.bend as L1
import ../laws/AotHeaderStartsArray.bend as L2
import ../laws/DefinesEachTableOnce.bend as L3
import ../laws/GetFindsFirstPair.bend as L4
import ../laws/HeaderDefinesImplicitTable.bend as L5
import ../laws/HeaderDefinesNewTable.bend as L6
import ../laws/KeyNameIsItsCharacters.bend as Laws
import ../laws/StringRenderEscapes.bend as L7
import ../laws/defs/BareValueGrammar.bend as D1
import ../laws/defs/BlankAndControlChars.bend as D2
import ../laws/defs/KeySegmentSpelling.bend as D3
import ../laws/defs/SealedValues.bend as D4
import ./lemmas/ControlEscapeText.bend as M1
import ./lemmas/FailedWalkNameCompare.bend as M2
import ./lemmas/FreshNamesInRows.bend as M3
import ./lemmas/HeaderDefinesTables.bend as M4
import ./lemmas/HeaderKeyScan.bend as M5
import ./lemmas/HeaderSegmentWalk.bend as M6
import ./lemmas/KeyvalKeyScan.bend as M7
import ./lemmas/NavigationWalkFrames.bend as M8
import ./lemmas/PickAndDigitSteps.bend as M9
import ./lemmas/QuotedKeySegments.bend as M10
import ./lemmas/RefusalReasons.bend as M11
import ./lemmas/RenderedHeaderLines.bend as M12
import ./lemmas/ReorderedTableNames.bend as M13
import ./lemmas/ScanInvariantSteps.bend as M14
import ./lemmas/StringEqualsItself.bend as M15
import ./lemmas/ValueTextReadback.bend as M16
import ./lemmas/WellFormedTextWalk.bend as M17

# the rest of the text after a segment, read from every back and qkind
def wh.Then(
  cl: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +arrtab: Bool,
  +rest: String,
  +goal: T.Doc
) -> Type:
  @bk: T.Lex -> @qk: T.QKind ->
    {T.doc.read(rest, T.MScan{M5.wh.aft(cl, rows, heads, here, parts, bk, qk, arrtab)}) == goal
      : T.Doc}

# the first character of a bare segment starts its buffer
def wh.b1.fast(
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
) -> {T.read.fast(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind,
  arrtab), Chr{xx}) == M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [Chr{xx}], T.LHead{}, back,
  qkind, arrtab) : T.St}:
  match dt:
    case False{}:
      Equal.cong(T.St, T.St, st => T.read.once2(st),
        T.lex.head.go(Char.is_eq(Chr{xx}, '['), T.bare.at(Chr{xx}), T.ch.sp(Chr{xx}),
          Char.is_eq(Chr{xx}, '.'), Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '"'),
          Char.is_eq(Chr{xx}, '\''), Char.is_eq(Chr{xx}, '#'),
          M6.wh.st(rows, heads, here, [], [], T.LHead{}, back, qkind, arrtab), Chr{xx}),
        T.lex.head.ch(M6.wh.st(rows, heads, here, [], [], T.LHead{}, back, qkind, arrtab),
          Chr{xx}),
        M6.wh.go.bare(Char.is_eq(Chr{xx}, '['), T.bare.at(Chr{xx}), T.ch.sp(Chr{xx}),
          Char.is_eq(Chr{xx}, '.'), Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '"'),
          Char.is_eq(Chr{xx}, '\''), Char.is_eq(Chr{xx}, '#'),
          M6.wh.st(rows, heads, here, [], [], T.LHead{}, back, qkind, arrtab), xx, {==}, {==},
          ee))
    case True{}:
      Equal.cong(T.St, T.St, st => T.read.once2(st),
        T.lex.hdot(T.ch.sp(Chr{xx}), T.bare.at(Chr{xx}), Char.is_eq(Chr{xx}, '"'),
          Char.is_eq(Chr{xx}, '\''),
          M6.wh.st(rows, heads, here, parts, [], T.LHeadDot{}, back, qkind, arrtab), Chr{xx}),
        T.st.push(M6.wh.st(rows, heads, here, parts, [], T.LHeadDot{}, back, qkind, arrtab),
          Chr{xx}, T.LHead{}),
        M6.wh.dot.bare(T.ch.sp(Chr{xx}), T.bare.at(Chr{xx}), Char.is_eq(Chr{xx}, '"'),
          Char.is_eq(Chr{xx}, '\''),
          M6.wh.st(rows, heads, here, parts, [], T.LHeadDot{}, back, qkind, arrtab), xx, {==},
          {==}, ee))

# and the scan mode sends it there
def wh.b1(
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
) -> {T.doc.scan(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind,
  arrtab), Chr{xx}) == T.MScan{M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [Chr{xx}], T.LHead{},
  back, qkind, arrtab)} : T.Mode}:
  Equal.trans(T.Mode,
    T.doc.scan(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind,
      arrtab), Chr{xx}),
    T.MScan{T.read.fast(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back,
      qkind, arrtab), Chr{xx})},
    T.MScan{M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [Chr{xx}], T.LHead{}, back, qkind,
      arrtab)},
    M13.scan.other(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), U32.is_eq(xx, 13),
      M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind, arrtab),
      Chr{xx}, {==}, {==}, {==}, ch => T.bare.at(ch), ee, {==}, {==}, {==}),
    Equal.cong(T.St, T.Mode, st => T.MScan{st},
      T.read.fast(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind,
        arrtab), Chr{xx}),
      M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [Chr{xx}], T.LHead{}, back, qkind, arrtab),
      wh.b1.fast(dt, rows, heads, here, parts, back, qkind, arrtab, xx, ee)))

# with a segment open, the next bare character joins it, whatever came before
def wh.ch.later(
  parts: List<&2, String>,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +dd: Char,
  +bb: List<&2, Char>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +cc: Char
) -> {T.read.once2(T.lex.head.ch(M6.wh.st(rows, heads, here, parts, dd <> bb, T.LHead{}, back,
  qkind, arrtab), cc)) == M6.wh.st(rows, heads, here, parts, cc <> dd <> bb, T.LHead{}, back,
  qkind, arrtab) : T.St}:
  match parts:
    case []:
      {==}
    case _p <> _ps:
      {==}

# a later character of a bare segment, from the scan mode
def wh.b2(
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +dd: Char,
  +bb: List<&2, Char>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +xx: U32,
  +ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.doc.scan(M6.wh.st(rows, heads, here, parts, dd <> bb, T.LHead{}, back, qkind, arrtab),
  Chr{xx}) == T.MScan{M6.wh.st(rows, heads, here, parts, Chr{xx} <> dd <> bb, T.LHead{}, back,
  qkind, arrtab)} : T.Mode}:
  Equal.trans(T.Mode,
    T.doc.scan(M6.wh.st(rows, heads, here, parts, dd <> bb, T.LHead{}, back, qkind, arrtab),
      Chr{xx}),
    T.MScan{T.read.fast(M6.wh.st(rows, heads, here, parts, dd <> bb, T.LHead{}, back, qkind,
      arrtab), Chr{xx})},
    T.MScan{M6.wh.st(rows, heads, here, parts, Chr{xx} <> dd <> bb, T.LHead{}, back, qkind,
      arrtab)},
    M13.scan.other(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), U32.is_eq(xx, 13),
      M6.wh.st(rows, heads, here, parts, dd <> bb, T.LHead{}, back, qkind, arrtab),
      Chr{xx}, {==}, {==}, {==}, ch => T.bare.at(ch), ee, {==}, {==}, {==}),
    Equal.cong(T.St, T.Mode, st => T.MScan{st},
      T.read.fast(M6.wh.st(rows, heads, here, parts, dd <> bb, T.LHead{}, back, qkind, arrtab),
        Chr{xx}),
      M6.wh.st(rows, heads, here, parts, Chr{xx} <> dd <> bb, T.LHead{}, back, qkind, arrtab),
      Equal.trans(T.St,
        T.read.once2(T.lex.head.go(Char.is_eq(Chr{xx}, '['), T.bare.at(Chr{xx}),
          T.ch.sp(Chr{xx}), Char.is_eq(Chr{xx}, '.'), Char.is_eq(Chr{xx}, ']'),
          Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), Char.is_eq(Chr{xx}, '#'),
          M6.wh.st(rows, heads, here, parts, dd <> bb, T.LHead{}, back, qkind, arrtab), Chr{xx})),
        T.read.once2(T.lex.head.ch(M6.wh.st(rows, heads, here, parts, dd <> bb, T.LHead{}, back,
          qkind, arrtab), Chr{xx})),
        M6.wh.st(rows, heads, here, parts, Chr{xx} <> dd <> bb, T.LHead{}, back, qkind, arrtab),
        Equal.cong(T.St, T.St, st => T.read.once2(st),
          T.lex.head.go(Char.is_eq(Chr{xx}, '['), T.bare.at(Chr{xx}), T.ch.sp(Chr{xx}),
            Char.is_eq(Chr{xx}, '.'), Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '"'),
            Char.is_eq(Chr{xx}, '\''), Char.is_eq(Chr{xx}, '#'),
            M6.wh.st(rows, heads, here, parts, dd <> bb, T.LHead{}, back, qkind, arrtab),
            Chr{xx}),
          T.lex.head.ch(M6.wh.st(rows, heads, here, parts, dd <> bb, T.LHead{}, back, qkind,
            arrtab), Chr{xx}),
          M6.wh.go.bare(Char.is_eq(Chr{xx}, '['), T.bare.at(Chr{xx}), T.ch.sp(Chr{xx}),
            Char.is_eq(Chr{xx}, '.'), Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '"'),
            Char.is_eq(Chr{xx}, '\''), Char.is_eq(Chr{xx}, '#'),
            M6.wh.st(rows, heads, here, parts, dd <> bb, T.LHead{}, back, qkind, arrtab), xx,
            {==}, {==}, ee)),
        wh.ch.later(parts, rows, heads, here, dd, bb, back, qkind, arrtab, Chr{xx}))))

# the rest of a bare segment is pushed onto its buffer, whatever follows it
def wh.bbody(
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
  +arrtab: Bool,
  +ee: {T.bare.all(String.to_list(ks)) == True{} : Bool}
) -> {T.doc.read(String.append(ks, rr), T.MScan{M6.wh.st(rows, heads, here, parts, dd <> bb,
  T.LHead{}, back, qkind, arrtab)}) == T.doc.read(rr, T.MScan{M6.wh.st(rows, heads, here, parts,
  M3.rev.onto(ks, dd <> bb), T.LHead{}, back, qkind, arrtab)}) : T.Doc}:
  match ks:
    case SNil{}:
      {==}
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          Equal.trans(T.Doc,
            T.doc.read(String.append(tt, rr), T.doc.scan(M6.wh.st(rows, heads, here, parts,
              dd <> bb, T.LHead{}, back, qkind, arrtab), Chr{xx})),
            T.doc.read(String.append(tt, rr), T.MScan{M6.wh.st(rows, heads, here, parts,
              Chr{xx} <> dd <> bb, T.LHead{}, back, qkind, arrtab)}),
            T.doc.read(rr, T.MScan{M6.wh.st(rows, heads, here, parts,
              M3.rev.onto(tt, Chr{xx} <> dd <> bb), T.LHead{}, back, qkind, arrtab)}),
            Equal.cong(T.Mode, T.Doc, md => T.doc.read(String.append(tt, rr), md),
              T.doc.scan(M6.wh.st(rows, heads, here, parts, dd <> bb, T.LHead{}, back, qkind,
                arrtab), Chr{xx}),
              T.MScan{M6.wh.st(rows, heads, here, parts, Chr{xx} <> dd <> bb, T.LHead{}, back,
                qkind, arrtab)},
              wh.b2(rows, heads, here, parts, dd, bb, back, qkind, arrtab, xx,
                M16.ball.head(T.bare.at(Chr{xx}), String.to_list(tt), ee))),
            wh.bbody(tt, rr, rows, heads, here, parts, Chr{xx}, dd <> bb, back, qkind, arrtab,
              M16.ball.tail(T.bare.at(Chr{xx}), String.to_list(tt), ee)))

# the bracket closes the header the same way whatever state the last segment
# ended in
def wh.lexfree(
  arrtab: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +pp: String,
  +ps: List<&2, String>,
  +lx: T.Lex,
  +back: T.Lex,
  +qkind: T.QKind
) -> {T.read.once2(T.lex.head.close2(arrtab, M6.wh.st(rows, heads, here, pp <> ps, [], lx, back,
  qkind, arrtab))) == T.read.once2(T.lex.head.close2(arrtab, M6.wh.st(rows, heads, here, pp <> ps,
  [], T.LHeadGap{}, back, qkind, arrtab))) : T.St}:
  match arrtab:
    case False{}:
      {==}
    case True{}:
      {==}

# a dot or the bracket ends an open bare segment and pushes it
def wh.bdl(
  cl: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +bf: List<&2, Char>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +rest: String,
  full: {List.is_empty(&2, Char, bf) == False{} : Bool}
) -> {T.doc.read(SCon{M12.wh.dl(cl), rest}, T.MScan{M6.wh.st(rows, heads, here, parts, bf, T.LHead{},
  back, qkind, arrtab)}) == T.doc.read(rest, T.MScan{M5.wh.aft(cl, rows, heads, here,
  T.buf.str(bf) <> parts, back, qkind, arrtab)}) : T.Doc}:
  match cl:
    case False{}:
      Equal.cong(Bool, T.Doc,
        bt => T.doc.read(rest, T.MScan{T.read.once2(T.lex.head.dot3(bt, M6.wh.st(rows, heads,
          here, parts, bf, T.LHead{}, back, qkind, arrtab)))}),
        List.is_empty(&2, Char, bf), False{}, full)
    case True{}:
      Equal.trans(T.Doc,
        T.doc.read(rest, T.MScan{T.read.once2(T.lex.head.close.go(List.is_empty(&2, Char, bf),
          arrtab, M6.wh.st(rows, heads, here, parts, bf, T.LHead{}, back, qkind, arrtab)))}),
        T.doc.read(rest, T.MScan{T.read.once2(T.lex.head.close.go(False{}, arrtab,
          M6.wh.st(rows, heads, here, parts, bf, T.LHead{}, back, qkind, arrtab)))}),
        T.doc.read(rest, T.MScan{M5.wh.aft(True{}, rows, heads, here, T.buf.str(bf) <> parts, back,
          qkind, arrtab)}),
        Equal.cong(Bool, T.Doc,
          bt => T.doc.read(rest, T.MScan{T.read.once2(T.lex.head.close.go(bt, arrtab,
            M6.wh.st(rows, heads, here, parts, bf, T.LHead{}, back, qkind, arrtab)))}),
          List.is_empty(&2, Char, bf), False{}, full),
        Equal.cong(T.St, T.Doc, st => T.doc.read(rest, T.MScan{st}),
          T.read.once2(T.lex.head.close2(arrtab, M6.wh.st(rows, heads, here, T.buf.str(bf) <> parts,
            [], T.LHead{}, back, qkind, arrtab))),
          T.read.once2(T.lex.head.close2(arrtab, M6.wh.st(rows, heads, here, T.buf.str(bf) <> parts,
            [], T.LHeadGap{}, back, qkind, arrtab))),
          wh.lexfree(arrtab, rows, heads, here, T.buf.str(bf), parts, T.LHead{}, back, qkind)))

# a bare segment and the dot or bracket after it: the rest is read with the
# segment pushed, and back and qkind as they were
def wh.bseg(
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
  +arrtab: Bool,
  +rest: String,
  +goal: T.Doc,
  +ee: {T.bare.all.step(T.bare.at(Chr{xx}), _u => T.bare.all(String.to_list(tt))) == True{} : Bool},
  ih: wh.Then(cl, rows, heads, here, SCon{Chr{xx}, tt} <> M12.wh.ps(dt, parts), arrtab, rest, goal)
) -> {T.doc.read(String.append(SCon{Chr{xx}, tt}, SCon{M12.wh.dl(cl), rest}), T.MScan{M6.wh.st(rows,
  heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind, arrtab)}) == goal : T.Doc}:
  Equal.trans(T.Doc,
    T.doc.read(String.append(tt, SCon{M12.wh.dl(cl), rest}), T.doc.scan(M6.wh.st(rows, heads, here,
      M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind, arrtab), Chr{xx})),
    T.doc.read(String.append(tt, SCon{M12.wh.dl(cl), rest}), T.MScan{M6.wh.st(rows, heads, here,
      M12.wh.ps(dt, parts), [Chr{xx}], T.LHead{}, back, qkind, arrtab)}),
    goal,
    Equal.cong(T.Mode, T.Doc, md => T.doc.read(String.append(tt, SCon{M12.wh.dl(cl), rest}), md),
      T.doc.scan(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind,
        arrtab), Chr{xx}),
      T.MScan{M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [Chr{xx}], T.LHead{}, back, qkind,
        arrtab)},
      wh.b1(dt, rows, heads, here, parts, back, qkind, arrtab, xx,
        M16.ball.head(T.bare.at(Chr{xx}), String.to_list(tt), ee))),
    Equal.trans(T.Doc,
      T.doc.read(String.append(tt, SCon{M12.wh.dl(cl), rest}), T.MScan{M6.wh.st(rows, heads, here,
        M12.wh.ps(dt, parts), [Chr{xx}], T.LHead{}, back, qkind, arrtab)}),
      T.doc.read(SCon{M12.wh.dl(cl), rest}, T.MScan{M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts),
        M3.rev.onto(tt, [Chr{xx}]), T.LHead{}, back, qkind, arrtab)}),
      goal,
      wh.bbody(tt, SCon{M12.wh.dl(cl), rest}, rows, heads, here, M12.wh.ps(dt, parts), Chr{xx}, [],
        back, qkind, arrtab, M16.ball.tail(T.bare.at(Chr{xx}), String.to_list(tt), ee)),
      Equal.trans(T.Doc,
        T.doc.read(SCon{M12.wh.dl(cl), rest}, T.MScan{M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts),
          M3.rev.onto(tt, [Chr{xx}]), T.LHead{}, back, qkind, arrtab)}),
        T.doc.read(rest, T.MScan{M5.wh.aft(cl, rows, heads, here,
          T.buf.str(M3.rev.onto(tt, [Chr{xx}])) <> M12.wh.ps(dt, parts), back, qkind, arrtab)}),
        goal,
        wh.bdl(cl, rows, heads, here, M12.wh.ps(dt, parts), M3.rev.onto(tt, [Chr{xx}]), back, qkind,
          arrtab, rest, M16.rev.full(tt, Chr{xx}, [])),
        Equal.trans(T.Doc,
          T.doc.read(rest, T.MScan{M5.wh.aft(cl, rows, heads, here,
            T.buf.str(M3.rev.onto(tt, [Chr{xx}])) <> M12.wh.ps(dt, parts), back, qkind, arrtab)}),
          T.doc.read(rest, T.MScan{M5.wh.aft(cl, rows, heads, here,
            SCon{Chr{xx}, tt} <> M12.wh.ps(dt, parts), back, qkind, arrtab)}),
          goal,
          Equal.cong(String, T.Doc, nm => T.doc.read(rest, T.MScan{M5.wh.aft(cl, rows, heads,
            here, nm <> M12.wh.ps(dt, parts), back, qkind, arrtab)}),
            T.buf.str(M3.rev.onto(tt, [Chr{xx}])), SCon{Chr{xx}, tt}, M16.wh.bname(xx, tt)),
          ih(back, qkind)))))

# a segment as key writes it, when that is bare
def wh.seg.bare(
  +ss: String,
  +cl: Bool,
  +dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +rest: String,
  +goal: T.Doc,
  eb: {T.bare(ss) == True{} : Bool},
  ih: wh.Then(cl, rows, heads, here, ss <> M12.wh.ps(dt, parts), arrtab, rest, goal)
) -> {T.doc.read(String.append(T.key.go(True{}, ss), SCon{M12.wh.dl(cl), rest}), T.MScan{M6.wh.st(
  rows, heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind, arrtab)}) == goal
  : T.Doc}:
  match ss:
    case SNil{}:
      Eq.bit.absurd(&2, {T.doc.read(String.append(T.key.go(True{}, SNil{}), SCon{M12.wh.dl(cl),
        rest}), T.MScan{M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back,
        qkind, arrtab)}) == goal : T.Doc}, eb)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          wh.bseg(xx, tt, cl, dt, rows, heads, here, parts, back, qkind, arrtab, rest, goal,
            eb, ih)

# a quote where a segment starts opens a quoted segment with an empty buffer
def wh.qopen(
  dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool
) -> {T.doc.scan(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind,
  arrtab), '"') == T.MScan{M9.qs(True{}, rows, heads, here, M12.wh.ps(dt, parts), [], arrtab, back, [])}
  : T.Mode}:
  match dt:
    case False{}:
      {==}
    case True{}:
      {==}

# the closing quote pushes the segment, and the dot or bracket after it
# follows, whatever back the last escape left
def wh.qend(
  cl: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +arrtab: Bool,
  +back: T.Lex,
  +bf: List<&2, Char>,
  +rest: String
) -> {T.doc.read(SCon{'"', SCon{M12.wh.dl(cl), rest}}, T.MScan{M9.qs(True{}, rows, heads, here, parts, [],
  arrtab, back, bf)}) == T.doc.read(rest, T.MScan{M5.wh.aft(cl, rows, heads, here, T.buf.str(bf) <> parts,
  back, T.QBasic{}, arrtab)}) : T.Doc}:
  match cl:
    case False{}:
      {==}
    case True{}:
      {==}

# a quoted segment as key writes it, then a dot or the bracket: the rest is
# read with the segment pushed under its name, from wherever the last escape
# left back and with qkind basic
def wh.qseg(
  +ss: String,
  +cl: Bool,
  +dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +rest: String,
  +goal: T.Doc,
  ih: wh.Then(cl, rows, heads, here, ss <> M12.wh.ps(dt, parts), arrtab, rest, goal)
) -> {T.doc.read(String.append(T.key.go(False{}, ss), SCon{M12.wh.dl(cl), rest}), T.MScan{M6.wh.st(rows,
  heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind, arrtab)}) == goal : T.Doc}:
  Equal.trans(T.Doc,
    T.doc.read(String.append(T.key.basic(ss), SCon{M12.wh.dl(cl), rest}), T.MScan{M6.wh.st(rows, heads,
      here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind, arrtab)}),
    T.doc.read(String.append(String.append(L7.escs(ss), "\""), SCon{M12.wh.dl(cl), rest}),
      T.doc.scan(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind, arrtab),
      '"')),
    goal,
    Equal.cong(String, T.Doc, zz => T.doc.read(String.append(zz, SCon{M12.wh.dl(cl), rest}),
      T.MScan{M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind, arrtab)}),
      T.key.basic(ss), "\"" ++ L7.escs(ss) ++ "\"", L7.basic_escs(ss)),
    Equal.trans(T.Doc,
      T.doc.read(String.append(String.append(L7.escs(ss), "\""), SCon{M12.wh.dl(cl), rest}),
        T.doc.scan(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind,
        arrtab), '"')),
      T.doc.read(String.append(L7.escs(ss), SCon{'"', SCon{M12.wh.dl(cl), rest}}),
        T.MScan{M9.qs(True{}, rows, heads, here, M12.wh.ps(dt, parts), [], arrtab, back, [])}),
      goal,
      Equal.trans(T.Doc,
        T.doc.read(String.append(String.append(L7.escs(ss), "\""), SCon{M12.wh.dl(cl), rest}),
          T.doc.scan(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind,
          arrtab), '"')),
        T.doc.read(String.append(L7.escs(ss), SCon{'"', SCon{M12.wh.dl(cl), rest}}),
          T.doc.scan(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind,
          arrtab), '"')),
        T.doc.read(String.append(L7.escs(ss), SCon{'"', SCon{M12.wh.dl(cl), rest}}),
          T.MScan{M9.qs(True{}, rows, heads, here, M12.wh.ps(dt, parts), [], arrtab, back, [])}),
        Equal.cong(String, T.Doc, zz => T.doc.read(zz, T.doc.scan(M6.wh.st(rows, heads, here,
          M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind, arrtab), '"')),
          String.append(String.append(L7.escs(ss), "\""), SCon{M12.wh.dl(cl), rest}),
          String.append(L7.escs(ss), SCon{'"', SCon{M12.wh.dl(cl), rest}}),
          Eq.append_assoc(L7.escs(ss), "\"", SCon{M12.wh.dl(cl), rest})),
        Equal.cong(T.Mode, T.Doc, md => T.doc.read(String.append(L7.escs(ss), SCon{'"',
          SCon{M12.wh.dl(cl), rest}}), md),
          T.doc.scan(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind,
            arrtab), '"'),
          T.MScan{M9.qs(True{}, rows, heads, here, M12.wh.ps(dt, parts), [], arrtab, back, [])},
          wh.qopen(dt, rows, heads, here, parts, back, qkind, arrtab))),
      M10.qs.escs(ss, True{}, rows, heads, here, M12.wh.ps(dt, parts), [], arrtab, back, [],
        SCon{'"', SCon{M12.wh.dl(cl), rest}}, goal,
        +bk => Equal.trans(T.Doc,
          T.doc.read(SCon{'"', SCon{M12.wh.dl(cl), rest}}, T.MScan{M9.qs(True{}, rows, heads, here,
            M12.wh.ps(dt, parts), [], arrtab, bk, M3.rev.onto(ss, []))}),
          T.doc.read(rest, T.MScan{M5.wh.aft(cl, rows, heads, here, T.buf.str(M3.rev.onto(ss, [])) <>
            M12.wh.ps(dt, parts), bk, T.QBasic{}, arrtab)}),
          goal,
          wh.qend(cl, rows, heads, here, M12.wh.ps(dt, parts), arrtab, bk, M3.rev.onto(ss, []), rest),
          Equal.trans(T.Doc,
            T.doc.read(rest, T.MScan{M5.wh.aft(cl, rows, heads, here, T.buf.str(M3.rev.onto(ss, [])) <>
              M12.wh.ps(dt, parts), bk, T.QBasic{}, arrtab)}),
            T.doc.read(rest, T.MScan{M5.wh.aft(cl, rows, heads, here, ss <> M12.wh.ps(dt, parts), bk,
              T.QBasic{}, arrtab)}),
            goal,
            Equal.cong(String, T.Doc, nm => T.doc.read(rest, T.MScan{M5.wh.aft(cl, rows, heads, here,
              nm <> M12.wh.ps(dt, parts), bk, T.QBasic{}, arrtab)}),
              T.buf.str(M3.rev.onto(ss, [])), ss, M12.wh.qname(ss)),
            ih(bk, T.QBasic{}))))))

# a segment as key writes it, bare or quoted, then a dot or the bracket
def wh.seg.go(
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
  +arrtab: Bool,
  +rest: String,
  +goal: T.Doc,
  eb: {T.bare(ss) == bb : Bool},
  ih: wh.Then(cl, rows, heads, here, ss <> M12.wh.ps(dt, parts), arrtab, rest, goal)
) -> {T.doc.read(String.append(T.key.go(bb, ss), SCon{M12.wh.dl(cl), rest}), T.MScan{M6.wh.st(rows,
  heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind, arrtab)}) == goal : T.Doc}:
  match bb:
    case True{}:
      wh.seg.bare(ss, cl, dt, rows, heads, here, parts, back, qkind, arrtab, rest, goal, eb, ih)
    case False{}:
      wh.qseg(ss, cl, dt, rows, heads, here, parts, back, qkind, arrtab, rest, goal, ih)

# a segment as key writes it, then a dot or the bracket
def wh.seg(
  +ss: String,
  +cl: Bool,
  +dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +rest: String,
  +goal: T.Doc,
  ih: wh.Then(cl, rows, heads, here, ss <> M12.wh.ps(dt, parts), arrtab, rest, goal)
) -> {T.doc.read(String.append(T.key(ss), SCon{M12.wh.dl(cl), rest}), T.MScan{M6.wh.st(rows, heads,
  here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind, arrtab)}) == goal : T.Doc}:
  wh.seg.go(T.bare(ss), ss, cl, dt, rows, heads, here, parts, back, qkind, arrtab, rest, goal, {==},
    ih)

# segments pushed one by one onto parts
def wh.Segs(
  t: List<&2, String>,
  +ss: String,
  +dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +rest: String,
  +goal: T.Doc
) -> Type:
  wh.Then(True{}, rows, heads, here, List.reverse.go(&2, String, t, ss <> M12.wh.ps(dt, parts)),
    arrtab, rest, goal) ->
    {T.doc.read(String.append(T.key(ss), String.append(M12.wh.more(t), SCon{']', rest})),
      T.MScan{M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind, arrtab)})
      == goal : T.Doc}

# a path's segments and the bracket after them: the rest is read with every
# segment pushed
def wh.segs(
  t: List<&2, String>,
  +ss: String,
  +dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +rest: String,
  +goal: T.Doc
) -> wh.Segs(t, ss, dt, rows, heads, here, parts, back, qkind, arrtab, rest, goal):
  match t:
    case []:
      ih => wh.seg(ss, True{}, dt, rows, heads, here, parts, back, qkind, arrtab, rest, goal, ih)
    case +xx <> +xs:
      ih => wh.seg(ss, False{}, dt, rows, heads, here, parts, back, qkind, arrtab,
        String.append(String.append(T.key(xx), M12.wh.more(xs)), SCon{']', rest}), goal,
        +bk => +qk => Equal.trans(T.Doc,
          T.doc.read(String.append(String.append(T.key(xx), M12.wh.more(xs)), SCon{']', rest}),
            T.MScan{M6.wh.st(rows, heads, here, ss <> M12.wh.ps(dt, parts), [], T.LHeadDot{}, bk, qk,
            arrtab)}),
          T.doc.read(String.append(T.key(xx), String.append(M12.wh.more(xs), SCon{']', rest})),
            T.MScan{M6.wh.st(rows, heads, here, ss <> M12.wh.ps(dt, parts), [], T.LHeadDot{}, bk, qk,
            arrtab)}),
          goal,
          Equal.cong(String, T.Doc, zz => T.doc.read(zz, T.MScan{M6.wh.st(rows, heads, here,
            ss <> M12.wh.ps(dt, parts), [], T.LHeadDot{}, bk, qk, arrtab)}),
            String.append(String.append(T.key(xx), M12.wh.more(xs)), SCon{']', rest}),
            String.append(T.key(xx), String.append(M12.wh.more(xs), SCon{']', rest})),
            Eq.append_assoc(T.key(xx), M12.wh.more(xs), SCon{']', rest})),
          wh.segs(xs, xx, True{}, rows, heads, here, ss <> M12.wh.ps(dt, parts), bk, qk, arrtab,
            rest, goal)(ih)))

# the rest of the text after the header, from the start of the next line
def wh.Line(
  +rows2: List<&2, T.Val>,
  +heads2: List<&2, String>,
  +path: List<&2, String>,
  +rest: String,
  +goal: T.Doc
) -> Type:
  @bk: T.Lex -> @qk: T.QKind ->
    {T.doc.read(rest, T.MScan{Laws.hb.line(rows2, heads2, path, bk, qk, False{})}) == goal
      : T.Doc}

# a whole header line of the segments ss then t, from the start of a line
def wh.core(
  arrtab: Bool,
  +ss: String,
  +t: List<&2, String>,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +a0: Bool,
  +rows2: List<&2, T.Val>,
  +heads2: List<&2, String>,
  +rest: String,
  +goal: T.Doc,
  ew: M6.wh.Walk(arrtab, ss <> t, rows, heads, rows2, heads2),
  ih: wh.Line(rows2, heads2, ss <> t, rest, goal)
) -> {T.doc.read(M12.wh.open(arrtab, String.append(T.key(ss), String.append(M12.wh.more(t), SCon{']',
  M6.wh.tail(arrtab, rest)}))), T.MScan{Laws.hb.line(rows, heads, here, back, qkind, a0)}) == goal
  : T.Doc}:
  match arrtab:
    case False{}:
      wh.segs(t, ss, False{}, rows, heads, here, [], back, qkind, False{}, M6.wh.tail(False{}, rest),
        goal)(+bk => +qk => Equal.trans(T.Doc,
          T.doc.read(SCon{'\n', rest}, T.MScan{M5.wh.aft(True{}, rows, heads, here,
            List.reverse.go(&2, String, t, [ss]), bk, qk, False{})}),
          T.doc.read(rest, T.MScan{Laws.hb.line(rows2, heads2, ss <> t, bk, qk, False{})}),
          goal,
          M5.wh.fin(False{}, rows, heads, here, List.reverse.go(&2, String, t, [ss]), bk, qk, ss <> t,
            rows2, heads2, rest, M12.wh.rne(t, ss, []), M12.wh.rev2(t, ss), ew),
          ih(bk, qk)))
    case True{}:
      wh.segs(t, ss, False{}, rows, heads, here, [], back, qkind, True{}, M6.wh.tail(True{}, rest),
        goal)(+bk => +qk => Equal.trans(T.Doc,
          T.doc.read(SCon{']', SCon{'\n', rest}}, T.MScan{M5.wh.aft(True{}, rows, heads, here,
            List.reverse.go(&2, String, t, [ss]), bk, qk, True{})}),
          T.doc.read(rest, T.MScan{Laws.hb.line(rows2, heads2, ss <> t, bk, qk, False{})}),
          goal,
          M5.wh.fin(True{}, rows, heads, here, List.reverse.go(&2, String, t, [ss]), bk, qk, ss <> t,
            rows2, heads2, rest, M12.wh.rne(t, ss, []), M12.wh.rev2(t, ss), ew),
          ih(bk, qk)))

# a header line as render writes it: the stored path, which is the parent's
# path joined with the last segment
def wh.law(
  +arrtab: Bool,
  segs: List<&2, String>,
  +kk: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +a0: Bool,
  +rows2: List<&2, T.Val>,
  +heads2: List<&2, String>,
  +rest: String,
  +goal: T.Doc,
  ew: M6.wh.Walk(arrtab, List.append(&2, String, segs, [kk]), rows, heads, rows2, heads2),
  ih: wh.Line(rows2, heads2, List.append(&2, String, segs, [kk]), rest, goal)
) -> {T.doc.read(M12.wh.open(arrtab, String.append(T.tree.pre(D1.tb.join(segs, ""), kk), SCon{']',
  M6.wh.tail(arrtab, rest)})), T.MScan{Laws.hb.line(rows, heads, here, back, qkind, a0)}) == goal
  : T.Doc}:
  match segs:
    case []:
      wh.core(arrtab, kk, [], rows, heads, here, back, qkind, a0, rows2, heads2, rest, goal, ew, ih)
    case +s0 <> +ss:
      Equal.trans(T.Doc,
        T.doc.read(M12.wh.open(arrtab, String.append(T.tree.pre(D1.tb.join(ss, T.key(s0)), kk),
          SCon{']', M6.wh.tail(arrtab, rest)})), T.MScan{Laws.hb.line(rows, heads, here, back, qkind,
          a0)}),
        T.doc.read(M12.wh.open(arrtab, String.append(String.append(T.key(s0), M12.wh.more(List.append(&2,
          String, ss, [kk]))), SCon{']', M6.wh.tail(arrtab, rest)})), T.MScan{Laws.hb.line(rows,
          heads, here, back, qkind, a0)}),
        goal,
        Equal.cong(String, T.Doc, pt => T.doc.read(M12.wh.open(arrtab, String.append(pt, SCon{']',
          M6.wh.tail(arrtab, rest)})), T.MScan{Laws.hb.line(rows, heads, here, back, qkind, a0)}),
          T.tree.pre(D1.tb.join(ss, T.key(s0)), kk),
          String.append(T.key(s0), M12.wh.more(List.append(&2, String, ss, [kk]))),
          M12.wh.join(ss, T.key(s0), kk, M12.wh.key.ne(s0))),
        Equal.trans(T.Doc,
          T.doc.read(M12.wh.open(arrtab, String.append(String.append(T.key(s0), M12.wh.more(List.append(&2,
            String, ss, [kk]))), SCon{']', M6.wh.tail(arrtab, rest)})), T.MScan{Laws.hb.line(rows,
            heads, here, back, qkind, a0)}),
          T.doc.read(M12.wh.open(arrtab, String.append(T.key(s0), String.append(M12.wh.more(List.append(&2,
            String, ss, [kk])), SCon{']', M6.wh.tail(arrtab, rest)}))), T.MScan{Laws.hb.line(rows,
            heads, here, back, qkind, a0)}),
          goal,
          Equal.cong(String, T.Doc, pt => T.doc.read(M12.wh.open(arrtab, pt), T.MScan{Laws.hb.line(rows,
            heads, here, back, qkind, a0)}),
            String.append(String.append(T.key(s0), M12.wh.more(List.append(&2, String, ss, [kk]))),
              SCon{']', M6.wh.tail(arrtab, rest)}),
            String.append(T.key(s0), String.append(M12.wh.more(List.append(&2, String, ss, [kk])),
              SCon{']', M6.wh.tail(arrtab, rest)})),
            Eq.append_assoc(T.key(s0), M12.wh.more(List.append(&2, String, ss, [kk])), SCon{']',
              M6.wh.tail(arrtab, rest)})),
          wh.core(arrtab, s0, List.append(&2, String, ss, [kk]), rows, heads, here, back, qkind, a0,
            rows2, heads2, rest, goal, ew, ih)))

def Laws.header_reads_back(
  segs,
  k,
  rows,
  heads,
  here,
  back,
  qkind,
  arrtab,
  rows2,
  heads2,
  ew,
  rest,
  goal,
  ih
):
  wh.law(False{}, segs, k, rows, heads, here, back, qkind, arrtab, rows2, heads2, rest, goal, ew, ih)

def Laws.header_new_table_reads_back(
  segs,
  k,
  rows,
  heads,
  eo,
  em,
  here,
  back,
  qkind,
  arrtab,
  rest,
  goal,
  ih
):
  Laws.header_reads_back(segs, k, rows, heads, here, back, qkind, arrtab,
    D1.tb.set(segs, "", rows, T.VPair{k, T.VHead{T.tree.pre(D1.tb.join(segs, ""), k), []}}
      <> D1.tb.rows(segs, rows)),
    T.heads.by.head(T.tree.pre(D1.tb.join(segs, ""), k)) <> heads,
    L6.header_defines_new_table(segs, k, rows, heads, eo, em), rest, goal, ih)

def Laws.header_implicit_table_reads_back(
  segs,
  k,
  rows,
  heads,
  p,
  sub,
  eo,
  ef,
  eh,
  here,
  back,
  qkind,
  arrtab,
  rest,
  goal,
  ih
):
  Laws.header_reads_back(segs, k, rows, heads, here, back, qkind, arrtab,
    D1.tb.set(segs, "", rows, T.rows.repl(D1.tb.rows(segs, rows), k,
      T.VHead{T.tree.pre(D1.tb.join(segs, ""), k), sub})),
    T.heads.by.head(T.tree.pre(D1.tb.join(segs, ""), k)) <> heads,
    L5.header_defines_implicit_table(segs, k, rows, heads, p, sub, eo, ef, eh), rest, goal, ih)

def Laws.aot_header_reads_back(
  segs,
  k,
  rows,
  heads,
  here,
  back,
  qkind,
  arrtab,
  rows2,
  heads2,
  ew,
  rest,
  goal,
  ih
):
  wh.law(True{}, segs, k, rows, heads, here, back, qkind, arrtab, rows2, heads2, rest, goal, ew, ih)

def Laws.aot_header_new_array_reads_back(
  segs,
  k,
  rows,
  heads,
  eo,
  em,
  here,
  back,
  qkind,
  arrtab,
  rest,
  goal,
  ih
):
  Laws.aot_header_reads_back(segs, k, rows, heads, here, back, qkind, arrtab,
    D1.tb.set(segs, "", rows, T.VPair{k, T.VAots{T.tree.pre(D1.tb.join(segs, ""), k),
      [T.VAot{T.tree.pre(D1.tb.join(segs, ""), k), []}]}} <> D1.tb.rows(segs, rows)),
    heads, L2.aot_header_starts_array(segs, k, rows, heads, eo, em), rest, goal, ih)

def Laws.aot_header_extends_array_reads_back(
  segs,
  k,
  rows,
  heads,
  p,
  elems,
  eo,
  ef,
  here,
  back,
  qkind,
  arrtab,
  rest,
  goal,
  ih
):
  Laws.aot_header_reads_back(segs, k, rows, heads, here, back, qkind, arrtab,
    D1.tb.set(segs, "", rows, T.rows.repl(D1.tb.rows(segs, rows), k,
      T.VAots{T.tree.pre(D1.tb.join(segs, ""), k), T.VAot{T.tree.pre(D1.tb.join(segs, ""), k), []}
        <> elems})),
    T.heads.drop(heads, String.append(T.tree.pre(D1.tb.join(segs, ""), k), ".")),
    L1.aot_header_extends_array(segs, k, rows, heads, p, elems, eo, ef), rest, goal, ih)

# a character read from a literal segment is pushed
def ql.Step(
  +uu: U32,
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>
) -> Type:
  {T.doc.scan(M6.ql(hd, rw, hs, he, ps, ab, back, buf), Chr{uu})
    == T.MScan{M6.ql(hd, rw, hs, he, ps, ab, back, Chr{uu} <> buf)} : T.Mode}

# a quotation mark, a backslash and a tab: their steps compute
def ql.s34(
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>
) -> ql.Step(34, hd, rw, hs, he, ps, ab, back, buf):
  match hd:
    case False{}:
      {==}
    case True{}:
      {==}

# a backslash
def ql.s92(
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>
) -> ql.Step(92, hd, rw, hs, he, ps, ab, back, buf):
  match hd:
    case False{}:
      {==}
    case True{}:
      {==}

# a tab
def ql.s9(
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>
) -> ql.Step(9, hd, rw, hs, he, ps, ab, back, buf):
  match hd:
    case False{}:
      {==}
    case True{}:
      {==}

# the fast step of a character in a literal segment is the segment's full step
def ql.fast(
  +uu: U32,
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>
) -> {T.read.fast(M6.ql(hd, rw, hs, he, ps, ab, back, buf), Chr{uu}) == T.read.once2(T.lex.kq.go(
  U32.is_eq(uu, 39), U32.is_eq(uu, 92), False{}, Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)),
  M6.ql(hd, rw, hs, he, ps, ab, back, buf), Chr{uu}, M10.qs.close(hd), M9.qs.lex(hd))) : T.St}:
  match hd:
    case False{}:
      {==}
    case True{}:
      {==}

# a character that is no control is pushed: str.bad passes it
def ql.char(
  ctl: Bool,
  +uu: U32,
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>,
  hc: {ctl == False{} : Bool}
) -> {T.read.once2(T.lex.kq.char.go(T.str.bad.go(ctl, U32.is_eq(uu, 9),
  Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)), False{}), M6.ql(hd, rw, hs, he, ps, ab, back, buf),
  Chr{uu}, M9.qs.lex(hd))) == M6.ql(hd, rw, hs, he, ps, ab, back, Chr{uu} <> buf) : T.St}:
  match ctl:
    case False{}:
      {==}
    case True{}:
      Eq.bit.absurd2(&2, {T.read.once2(T.lex.kq.char.go(T.str.bad.go(True{}, U32.is_eq(uu, 9),
        Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)), False{}), M6.ql(hd, rw, hs, he, ps, ab, back,
        buf), Chr{uu}, M9.qs.lex(hd))) == M6.ql(hd, rw, hs, he, ps, ab, back, Chr{uu} <> buf) : T.St}, hc)

# a character that is no apostrophe, no backslash and no newline is no closer
# and no backslash
def ql.go(
  quote: Bool,
  bs: Bool,
  nl: Bool,
  +uu: U32,
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>,
  hq: {quote == False{} : Bool},
  hb: {bs == False{} : Bool},
  hn: {nl == False{} : Bool},
  hc: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool}
) -> {T.read.once2(T.lex.kq.go(quote, bs, False{}, nl, M6.ql(hd, rw, hs, he, ps, ab, back, buf), Chr{uu},
  M10.qs.close(hd), M9.qs.lex(hd))) == M6.ql(hd, rw, hs, he, ps, ab, back, Chr{uu} <> buf) : T.St}:
  match quote:
    case True{}:
      Eq.bit.absurd2(&2, {T.read.once2(T.lex.kq.go(True{}, bs, False{}, nl, M6.ql(hd, rw, hs, he, ps, ab,
        back, buf), Chr{uu}, M10.qs.close(hd), M9.qs.lex(hd))) == M6.ql(hd, rw, hs, he, ps, ab, back,
        Chr{uu} <> buf) : T.St}, hq)
    case False{}:
      match bs:
        case True{}:
          Eq.bit.absurd2(&2, {T.read.once2(T.lex.kq.go(False{}, True{}, False{}, nl, M6.ql(hd, rw, hs, he,
            ps, ab, back, buf), Chr{uu}, M10.qs.close(hd), M9.qs.lex(hd))) == M6.ql(hd, rw, hs, he, ps, ab,
            back, Chr{uu} <> buf) : T.St}, hb)
        case False{}:
          match nl:
            case True{}:
              Eq.bit.absurd2(&2, {T.read.once2(T.lex.kq.go(False{}, False{}, False{}, True{}, M6.ql(hd,
                rw, hs, he, ps, ab, back, buf), Chr{uu}, M10.qs.close(hd), M9.qs.lex(hd))) == M6.ql(hd, rw, hs,
                he, ps, ab, back, Chr{uu} <> buf) : T.St}, hn)
            case False{}:
              ql.char(Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), uu, hd, rw, hs, he, ps, ab,
                back, buf, hc)

# the fast step pushes a character
def ql.Fast(
  +uu: U32,
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>
) -> Type:
  {T.read.fast(M6.ql(hd, rw, hs, he, ps, ab, back, buf), Chr{uu})
    == M6.ql(hd, rw, hs, he, ps, ab, back, Chr{uu} <> buf) : T.St}

# the scan mode sends such a character to the fast step
def ql.q(
  dq: Bool,
  sq: Bool,
  cr: Bool,
  +uu: U32,
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>,
  hq: {dq == False{} : Bool},
  hs1: {sq == False{} : Bool},
  hr: {cr == False{} : Bool},
  fast: ql.Fast(uu, hd, rw, hs, he, ps, ab, back, buf)
) -> {T.doc.scan.q(dq, sq, cr, M6.ql(hd, rw, hs, he, ps, ab, back, buf), Chr{uu})
  == T.MScan{M6.ql(hd, rw, hs, he, ps, ab, back, Chr{uu} <> buf)} : T.Mode}:
  match dq:
    case True{}:
      Eq.bit.absurd2(&2, {T.doc.scan.q(True{}, sq, cr, M6.ql(hd, rw, hs, he, ps, ab, back, buf), Chr{uu})
        == T.MScan{M6.ql(hd, rw, hs, he, ps, ab, back, Chr{uu} <> buf)} : T.Mode}, hq)
    case False{}:
      match sq:
        case True{}:
          Eq.bit.absurd2(&2, {T.doc.scan.q(False{}, True{}, cr, M6.ql(hd, rw, hs, he, ps, ab, back, buf),
            Chr{uu}) == T.MScan{M6.ql(hd, rw, hs, he, ps, ab, back, Chr{uu} <> buf)} : T.Mode}, hs1)
        case False{}:
          match cr:
            case True{}:
              Eq.bit.absurd2(&2, {T.doc.scan.q(False{}, False{}, True{}, M6.ql(hd, rw, hs, he, ps, ab,
                back, buf), Chr{uu}) == T.MScan{M6.ql(hd, rw, hs, he, ps, ab, back, Chr{uu} <> buf)}
                : T.Mode}, hr)
            case False{}:
              Equal.cong(T.St, T.Mode, st => T.MScan{st},
                T.read.fast(M6.ql(hd, rw, hs, he, ps, ab, back, buf), Chr{uu}),
                M6.ql(hd, rw, hs, he, ps, ab, back, Chr{uu} <> buf), fast)

# any other literal character goes through the dispatch and is pushed
def ql.gen(
  +uu: U32,
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>,
  e34: {U32.is_eq(uu, 34) == False{} : Bool},
  e92: {U32.is_eq(uu, 92) == False{} : Bool},
  +e9: {U32.is_eq(uu, 9) == False{} : Bool},
  +el: {Laws.lit.char(Chr{uu}) == True{} : Bool}
) -> ql.Step(uu, hd, rw, hs, he, ps, ab, back, buf):
  +e39 = {M5.lit.q(U32.is_eq(uu, 39), Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), U32.is_eq(uu, 9),
    el) : {U32.is_eq(uu, 39) == False{} : Bool}}
  +ec = {M5.lit.c(U32.is_eq(uu, 39), Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)), U32.is_eq(uu, 9),
    e9, el) : {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool}}
  +e10 = {M1.ctl.off(uu, 10, ec, {==}) : {U32.is_eq(uu, 10) == False{} : Bool}}
  +e13 = {M1.ctl.off(uu, 13, ec, {==}) : {U32.is_eq(uu, 13) == False{} : Bool}}
  ql.q(U32.is_eq(uu, 34), U32.is_eq(uu, 39), U32.is_eq(uu, 13), uu, hd, rw, hs, he, ps, ab, back, buf,
    e34, e39, e13,
    Equal.trans(T.St, T.read.fast(M6.ql(hd, rw, hs, he, ps, ab, back, buf), Chr{uu}),
      T.read.once2(T.lex.kq.go(U32.is_eq(uu, 39), U32.is_eq(uu, 92), False{},
        Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)), M6.ql(hd, rw, hs, he, ps, ab, back, buf), Chr{uu},
        M10.qs.close(hd), M9.qs.lex(hd))),
      M6.ql(hd, rw, hs, he, ps, ab, back, Chr{uu} <> buf),
      ql.fast(uu, hd, rw, hs, he, ps, ab, back, buf),
      ql.go(U32.is_eq(uu, 39), U32.is_eq(uu, 92), Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)), uu, hd,
        rw, hs, he, ps, ab, back, buf, e39, e92, M16.or.ff(U32.is_eq(uu, 10), U32.is_eq(uu, 13), e10, e13),
        ec)))

# one code point k that the test found: its step is the character's
def ql.is(
  +uu: U32,
  +kk: U32,
  ee: {U32.is_eq(uu, kk) == True{} : Bool},
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>,
  at: ql.Step(kk, hd, rw, hs, he, ps, ab, back, buf)
) -> ql.Step(uu, hd, rw, hs, he, ps, ab, back, buf):
  eu = Equal.cong(Char, U32, cc => Char.to_u32(cc), Chr{uu}, Chr{kk}, Eq.u32_eq(uu, kk, ee))
  %Equal.sym(U32, uu, kk, eu) : ql.Step(_, hd, rw, hs, he, ps, ab, back, buf)
  at

# every literal character: a quotation mark, a backslash, a tab, or another
def ql.split(
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
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>,
  el: {Laws.lit.char(Chr{uu}) == True{} : Bool}
) -> ql.Step(uu, hd, rw, hs, he, ps, ab, back, buf):
  match d34:
    case True{}:
      ql.is(uu, 34, e34, hd, rw, hs, he, ps, ab, back, buf, ql.s34(hd, rw, hs, he, ps, ab, back, buf))
    case False{}:
      match b92:
        case True{}:
          ql.is(uu, 92, e92, hd, rw, hs, he, ps, ab, back, buf, ql.s92(hd, rw, hs, he, ps, ab, back, buf))
        case False{}:
          match t9:
            case True{}:
              ql.is(uu, 9, e9, hd, rw, hs, he, ps, ab, back, buf, ql.s9(hd, rw, hs, he, ps, ab, back,
                buf))
            case False{}:
              ql.gen(uu, hd, rw, hs, he, ps, ab, back, buf, e34, e92, e9, el)

# one character of a literal segment
def ql.one(
  +uu: U32,
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>,
  el: {Laws.lit.char(Chr{uu}) == True{} : Bool}
) -> ql.Step(uu, hd, rw, hs, he, ps, ab, back, buf):
  ql.split(uu, U32.is_eq(uu, 34), U32.is_eq(uu, 92), U32.is_eq(uu, 9), {==}, {==}, {==}, hd, rw, hs,
    he, ps, ab, back, buf, el)

# every character of a literal text is pushed, whatever follows it
def ql.body(
  ss: String,
  +rr: String,
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +ab: Bool,
  +back: T.Lex,
  +buf: List<&2, Char>,
  +ee: {Laws.lit.text(ss) == True{} : Bool}
) -> {T.doc.read(String.append(ss, rr), T.MScan{M6.ql(hd, rw, hs, he, ps, ab, back, buf)})
  == T.doc.read(rr, T.MScan{M6.ql(hd, rw, hs, he, ps, ab, back, M3.rev.onto(ss, buf))}) : T.Doc}:
  match ss:
    case SNil{}:
      {==}
    case SCon{hh, +tt}:
      match hh:
        case Chr{+uu}:
          Equal.trans(T.Doc,
            T.doc.read(String.append(tt, rr), T.doc.scan(M6.ql(hd, rw, hs, he, ps, ab, back, buf), Chr{uu})),
            T.doc.read(String.append(tt, rr), T.MScan{M6.ql(hd, rw, hs, he, ps, ab, back, Chr{uu} <> buf)}),
            T.doc.read(rr, T.MScan{M6.ql(hd, rw, hs, he, ps, ab, back, M3.rev.onto(tt, Chr{uu} <> buf))}),
            Equal.cong(T.Mode, T.Doc, md => T.doc.read(String.append(tt, rr), md),
              T.doc.scan(M6.ql(hd, rw, hs, he, ps, ab, back, buf), Chr{uu}),
              T.MScan{M6.ql(hd, rw, hs, he, ps, ab, back, Chr{uu} <> buf)},
              ql.one(uu, hd, rw, hs, he, ps, ab, back, buf,
                Eq.and.left(Laws.lit.char(Chr{uu}), Laws.lit.text(tt), ee))),
            ql.body(tt, rr, hd, rw, hs, he, ps, ab, back, Chr{uu} <> buf,
              Eq.and.right(Laws.lit.char(Chr{uu}), Laws.lit.text(tt), ee)))

def Laws.literal_key_reads_back(s, e):
  Equal.trans(T.Doc,
    T.doc.read(String.append(s, "' = 1"), T.MScan{M6.ql(False{}, [], [], [], [], False{}, T.LTop{}, [])}),
    T.doc.read("' = 1", T.MScan{M6.ql(False{}, [], [], [], [], False{}, T.LTop{}, M3.rev.onto(s, []))}),
    T.Doc{"", [T.VPair{s, T.VInt{T.Plus{}, "1"}}]},
    ql.body(s, "' = 1", False{}, [], [], [], [], False{}, T.LTop{}, [], e),
    Equal.trans(T.Doc,
      T.doc.read("' = 1", T.MScan{M6.ql(False{}, [], [], [], [], False{}, T.LTop{}, M3.rev.onto(s, []))}),
      M10.kq.doc(M3.rev.onto(s, [])),
      T.Doc{"", [T.VPair{s, T.VInt{T.Plus{}, "1"}}]},
      {==},
      M10.kq.name(s)))

# what ends a segment and its blank space: a dot, or `=` when cl
def kl.dl(cl: Bool) -> Char:
  match cl:
    case False{}:
      '.'
    case True{}:
      '='

# the state after it: waiting for the next segment, or for the value
def kl.aft(cl: Bool) -> T.Lex:
  match cl:
    case False{}:
      T.LKeyDot{}
    case True{}:
      T.LVal{}

# the rest of the text after a segment and what ends it, read from every
# back and qkind
def kl.Then(
  cl: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +arrtab: Bool,
  +rest: String,
  +goal: T.Doc
) -> Type:
  @bk: T.Lex -> @qk: T.QKind ->
    {T.doc.read(rest, T.MScan{M6.wh.st(rows, heads, here, parts, [], kl.aft(cl), bk, qk, arrtab)}) == goal
      : T.Doc}

# blank space after a segment stays in LAfter
def kl.agap(
  gs: List<&2, Bool>,
  +rr: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool
) -> {T.doc.read(String.append(D2.gap(gs), rr), T.MScan{M6.wh.st(rows, heads, here, parts, [], T.LAfter{},
  back, qkind, arrtab)}) == T.doc.read(rr, T.MScan{M6.wh.st(rows, heads, here, parts, [], T.LAfter{}, back,
  qkind, arrtab)}) : T.Doc}:
  match gs:
    case []:
      {==}
    case tab <> rest:
      match tab:
        case True{}:
          kl.agap(rest, rr, rows, heads, here, parts, back, qkind, arrtab)
        case False{}:
          kl.agap(rest, rr, rows, heads, here, parts, back, qkind, arrtab)

# and blank space after a dot stays in LKeyDot
def kl.dgap(
  gs: List<&2, Bool>,
  +rr: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool
) -> {T.doc.read(String.append(D2.gap(gs), rr), T.MScan{M6.wh.st(rows, heads, here, parts, [], T.LKeyDot{},
  back, qkind, arrtab)}) == T.doc.read(rr, T.MScan{M6.wh.st(rows, heads, here, parts, [], T.LKeyDot{}, back,
  qkind, arrtab)}) : T.Doc}:
  match gs:
    case []:
      {==}
    case tab <> rest:
      match tab:
        case True{}:
          kl.dgap(rest, rr, rows, heads, here, parts, back, qkind, arrtab)
        case False{}:
          kl.dgap(rest, rr, rows, heads, here, parts, back, qkind, arrtab)

# a dot or `=` after a segment's blank space
def kl.adl(
  cl: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +rest: String
) -> {T.doc.read(SCon{kl.dl(cl), rest}, T.MScan{M6.wh.st(rows, heads, here, parts, [], T.LAfter{}, back, qkind,
  arrtab)}) == T.doc.read(rest, T.MScan{M6.wh.st(rows, heads, here, parts, [], kl.aft(cl), back, qkind,
  arrtab)}) : T.Doc}:
  match cl:
    case False{}:
      {==}
    case True{}:
      {==}

# blank space, then a dot or `=`, after a segment pushed onto parts
def kl.atail(
  gs: List<&2, Bool>,
  +cl: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +rest: String
) -> {T.doc.read(String.append(D2.gap(gs), SCon{kl.dl(cl), rest}), T.MScan{M6.wh.st(rows, heads, here, parts,
  [], T.LAfter{}, back, qkind, arrtab)}) == T.doc.read(rest, T.MScan{M6.wh.st(rows, heads, here, parts, [],
  kl.aft(cl), back, qkind, arrtab)}) : T.Doc}:
  Equal.trans(T.Doc,
    T.doc.read(String.append(D2.gap(gs), SCon{kl.dl(cl), rest}), T.MScan{M6.wh.st(rows, heads, here, parts,
      [], T.LAfter{}, back, qkind, arrtab)}),
    T.doc.read(SCon{kl.dl(cl), rest}, T.MScan{M6.wh.st(rows, heads, here, parts, [], T.LAfter{}, back, qkind,
      arrtab)}),
    T.doc.read(rest, T.MScan{M6.wh.st(rows, heads, here, parts, [], kl.aft(cl), back, qkind, arrtab)}),
    kl.agap(gs, SCon{kl.dl(cl), rest}, rows, heads, here, parts, back, qkind, arrtab),
    kl.adl(cl, rows, heads, here, parts, back, qkind, arrtab, rest))

# the segment's buffer reads as its name, and the rest is read
def kl.nm(
  +nm: String,
  +bf: List<&2, Char>,
  en: {T.buf.str(bf) == nm : String},
  +cl: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +arrtab: Bool,
  +rest: String,
  +goal: T.Doc,
  ih: kl.Then(cl, rows, heads, here, nm <> parts, arrtab, rest, goal)
) -> {T.doc.read(rest, T.MScan{M6.wh.st(rows, heads, here, T.buf.str(bf) <> parts, [], kl.aft(cl), bk, qk,
  arrtab)}) == goal : T.Doc}:
  Equal.trans(T.Doc,
    T.doc.read(rest, T.MScan{M6.wh.st(rows, heads, here, T.buf.str(bf) <> parts, [], kl.aft(cl), bk, qk,
      arrtab)}),
    T.doc.read(rest, T.MScan{M6.wh.st(rows, heads, here, nm <> parts, [], kl.aft(cl), bk, qk, arrtab)}),
    goal,
    Equal.cong(String, T.Doc, xx => T.doc.read(rest, T.MScan{M6.wh.st(rows, heads, here, xx <> parts, [],
      kl.aft(cl), bk, qk, arrtab)}), T.buf.str(bf), nm, en),
    ih(bk, qk))

# after a quoted segment's closing quote: blank space, a dot or `=`, and the rest
def kl.fin(
  +nm: String,
  +bf: List<&2, Char>,
  en: {T.buf.str(bf) == nm : String},
  +gs: List<&2, Bool>,
  +cl: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +arrtab: Bool,
  +rest: String,
  +goal: T.Doc,
  ih: kl.Then(cl, rows, heads, here, nm <> parts, arrtab, rest, goal)
) -> {T.doc.read(String.append(D2.gap(gs), SCon{kl.dl(cl), rest}), T.MScan{M6.wh.st(rows, heads, here,
  T.buf.str(bf) <> parts, [], T.LAfter{}, bk, qk, arrtab)}) == goal : T.Doc}:
  Equal.trans(T.Doc,
    T.doc.read(String.append(D2.gap(gs), SCon{kl.dl(cl), rest}), T.MScan{M6.wh.st(rows, heads, here,
      T.buf.str(bf) <> parts, [], T.LAfter{}, bk, qk, arrtab)}),
    T.doc.read(rest, T.MScan{M6.wh.st(rows, heads, here, T.buf.str(bf) <> parts, [], kl.aft(cl), bk, qk,
      arrtab)}),
    goal,
    kl.atail(gs, cl, rows, heads, here, T.buf.str(bf) <> parts, bk, qk, arrtab, rest),
    kl.nm(nm, bf, en, cl, rows, heads, here, parts, bk, qk, arrtab, rest, goal, ih))

# a later bare character stays on the key's fast path
def kl.kfast(
  ok: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +buf: List<&2, Char>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +xx: U32,
  eok: {T.bare.at(Chr{xx}) == ok : Bool},
  ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.read.fast.key(ok, "", rows, heads, here, parts, buf, back, qkind, [], 0, 0, arrtab, Chr{xx})
  == M6.wh.st(rows, heads, here, parts, Chr{xx} <> buf, T.LKey{}, back, qkind, arrtab) : T.St}:
  match ok:
    case True{}:
      {==}
    case False{}:
      M15.clash(&2, {T.read.fast.key(False{}, "", rows, heads, here, parts, buf, back, qkind, [], 0, 0, arrtab,
        Chr{xx}) == M6.wh.st(rows, heads, here, parts, Chr{xx} <> buf, T.LKey{}, back, qkind, arrtab) : T.St},
        Equal.trans(Bool, False{}, T.bare.at(Chr{xx}), True{},
          Equal.sym(Bool, T.bare.at(Chr{xx}), False{}, eok), ee))

# a later character of a bare segment, from the scan mode
def kl.b2(
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +buf: List<&2, Char>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +xx: U32,
  +ee: {T.bare.at(Chr{xx}) == True{} : Bool}
) -> {T.doc.scan(M6.wh.st(rows, heads, here, parts, buf, T.LKey{}, back, qkind, arrtab), Chr{xx})
  == T.MScan{M6.wh.st(rows, heads, here, parts, Chr{xx} <> buf, T.LKey{}, back, qkind, arrtab)} : T.Mode}:
  Equal.trans(T.Mode,
    T.doc.scan(M6.wh.st(rows, heads, here, parts, buf, T.LKey{}, back, qkind, arrtab), Chr{xx}),
    T.MScan{T.read.fast(M6.wh.st(rows, heads, here, parts, buf, T.LKey{}, back, qkind, arrtab), Chr{xx})},
    T.MScan{M6.wh.st(rows, heads, here, parts, Chr{xx} <> buf, T.LKey{}, back, qkind, arrtab)},
    M13.scan.other(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), U32.is_eq(xx, 13),
      M6.wh.st(rows, heads, here, parts, buf, T.LKey{}, back, qkind, arrtab), Chr{xx}, {==}, {==}, {==},
      ch => T.bare.at(ch), ee, {==}, {==}, {==}),
    Equal.cong(T.St, T.Mode, st => T.MScan{st},
      T.read.fast(M6.wh.st(rows, heads, here, parts, buf, T.LKey{}, back, qkind, arrtab), Chr{xx}),
      M6.wh.st(rows, heads, here, parts, Chr{xx} <> buf, T.LKey{}, back, qkind, arrtab),
      kl.kfast(T.bare.at(Chr{xx}), rows, heads, here, parts, buf, back, qkind, arrtab, xx, {==}, ee)))

# the rest of a bare segment is pushed onto its buffer, whatever follows it
def kl.bbody(
  ks: String,
  +rr: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +buf: List<&2, Char>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +ee: {T.bare.all(String.to_list(ks)) == True{} : Bool}
) -> {T.doc.read(String.append(ks, rr), T.MScan{M6.wh.st(rows, heads, here, parts, buf, T.LKey{}, back, qkind,
  arrtab)}) == T.doc.read(rr, T.MScan{M6.wh.st(rows, heads, here, parts, M3.rev.onto(ks, buf), T.LKey{}, back,
  qkind, arrtab)}) : T.Doc}:
  match ks:
    case SNil{}:
      {==}
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          Equal.trans(T.Doc,
            T.doc.read(String.append(tt, rr), T.doc.scan(M6.wh.st(rows, heads, here, parts, buf, T.LKey{}, back,
              qkind, arrtab), Chr{xx})),
            T.doc.read(String.append(tt, rr), T.MScan{M6.wh.st(rows, heads, here, parts, Chr{xx} <> buf,
              T.LKey{}, back, qkind, arrtab)}),
            T.doc.read(rr, T.MScan{M6.wh.st(rows, heads, here, parts, M3.rev.onto(tt, Chr{xx} <> buf), T.LKey{},
              back, qkind, arrtab)}),
            Equal.cong(T.Mode, T.Doc, md => T.doc.read(String.append(tt, rr), md),
              T.doc.scan(M6.wh.st(rows, heads, here, parts, buf, T.LKey{}, back, qkind, arrtab), Chr{xx}),
              T.MScan{M6.wh.st(rows, heads, here, parts, Chr{xx} <> buf, T.LKey{}, back, qkind, arrtab)},
              kl.b2(rows, heads, here, parts, buf, back, qkind, arrtab, xx,
                M16.ball.head(T.bare.at(Chr{xx}), String.to_list(tt), ee))),
            kl.bbody(tt, rr, rows, heads, here, parts, Chr{xx} <> buf, back, qkind, arrtab,
              M16.ball.tail(T.bare.at(Chr{xx}), String.to_list(tt), ee)))

# a blank ends an open bare segment: it is pushed, and the scanner waits in
# LAfter
def kl.bsp(
  tab: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +bf: List<&2, Char>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +rr: String,
  full: {List.is_empty(&2, Char, bf) == False{} : Bool}
) -> {T.doc.read(SCon{D2.blank_char(tab), rr}, T.MScan{M6.wh.st(rows, heads, here, parts, bf, T.LKey{}, back,
  qkind, arrtab)}) == T.doc.read(rr, T.MScan{M6.wh.st(rows, heads, here, T.buf.str(bf) <> parts, [], T.LAfter{},
  back, qkind, arrtab)}) : T.Doc}:
  match tab:
    case True{}:
      Equal.cong(Bool, T.Doc, bt => T.doc.read(rr, T.MScan{T.read.once2(T.lex.key.end.go(bt, M6.wh.st(rows,
        heads, here, parts, bf, T.LKey{}, back, qkind, arrtab), T.LAfter{}))}),
        List.is_empty(&2, Char, bf), False{}, full)
    case False{}:
      Equal.cong(Bool, T.Doc, bt => T.doc.read(rr, T.MScan{T.read.once2(T.lex.key.end.go(bt, M6.wh.st(rows,
        heads, here, parts, bf, T.LKey{}, back, qkind, arrtab), T.LAfter{}))}),
        List.is_empty(&2, Char, bf), False{}, full)

# a dot or `=` right after an open bare segment pushes it
def kl.bdl(
  cl: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +bf: List<&2, Char>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +rest: String,
  full: {List.is_empty(&2, Char, bf) == False{} : Bool}
) -> {T.doc.read(SCon{kl.dl(cl), rest}, T.MScan{M6.wh.st(rows, heads, here, parts, bf, T.LKey{}, back, qkind,
  arrtab)}) == T.doc.read(rest, T.MScan{M6.wh.st(rows, heads, here, T.buf.str(bf) <> parts, [], kl.aft(cl), back,
  qkind, arrtab)}) : T.Doc}:
  match cl:
    case False{}:
      Equal.cong(Bool, T.Doc, bt => T.doc.read(rest, T.MScan{T.read.once2(T.lex.key.end.go(bt, M6.wh.st(rows,
        heads, here, parts, bf, T.LKey{}, back, qkind, arrtab), T.LKeyDot{}))}),
        List.is_empty(&2, Char, bf), False{}, full)
    case True{}:
      Equal.cong(Bool, T.Doc, bt => T.doc.read(rest, T.MScan{T.read.once2(T.lex.key.end.go(bt, M6.wh.st(rows,
        heads, here, parts, bf, T.LKey{}, back, qkind, arrtab), T.LVal{}))}),
        List.is_empty(&2, Char, bf), False{}, full)

# blank space and a dot or `=` after an open bare segment push it
def kl.bend(
  gs: List<&2, Bool>,
  +cl: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +bf: List<&2, Char>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +rest: String,
  full: {List.is_empty(&2, Char, bf) == False{} : Bool}
) -> {T.doc.read(String.append(D2.gap(gs), SCon{kl.dl(cl), rest}), T.MScan{M6.wh.st(rows, heads, here, parts,
  bf, T.LKey{}, back, qkind, arrtab)}) == T.doc.read(rest, T.MScan{M6.wh.st(rows, heads, here,
  T.buf.str(bf) <> parts, [], kl.aft(cl), back, qkind, arrtab)}) : T.Doc}:
  match gs:
    case []:
      kl.bdl(cl, rows, heads, here, parts, bf, back, qkind, arrtab, rest, full)
    case tab <> +gr:
      Equal.trans(T.Doc,
        T.doc.read(SCon{D2.blank_char(tab), String.append(D2.gap(gr), SCon{kl.dl(cl), rest})},
          T.MScan{M6.wh.st(rows, heads, here, parts, bf, T.LKey{}, back, qkind, arrtab)}),
        T.doc.read(String.append(D2.gap(gr), SCon{kl.dl(cl), rest}), T.MScan{M6.wh.st(rows, heads, here,
          T.buf.str(bf) <> parts, [], T.LAfter{}, back, qkind, arrtab)}),
        T.doc.read(rest, T.MScan{M6.wh.st(rows, heads, here, T.buf.str(bf) <> parts, [], kl.aft(cl), back,
          qkind, arrtab)}),
        kl.bsp(tab, rows, heads, here, parts, bf, back, qkind, arrtab, String.append(D2.gap(gr),
          SCon{kl.dl(cl), rest}), full),
        kl.atail(gr, cl, rows, heads, here, T.buf.str(bf) <> parts, back, qkind, arrtab, rest))

# a bare segment, its blank space and a dot or `=`: the rest is read with the
# segment pushed, and back and qkind as they were
def kl.bseg(
  +xx: U32,
  +tt: String,
  +gs: List<&2, Bool>,
  +cl: Bool,
  +dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +rest: String,
  +goal: T.Doc,
  +ee: {T.bare.all.step(T.bare.at(Chr{xx}), _u => T.bare.all(String.to_list(tt))) == True{} : Bool},
  ih: kl.Then(cl, rows, heads, here, SCon{Chr{xx}, tt} <> M12.wh.ps(dt, parts), arrtab, rest, goal)
) -> {T.doc.read(String.append(SCon{Chr{xx}, tt}, String.append(D2.gap(gs), SCon{kl.dl(cl), rest})),
  T.MScan{M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.kl.lex0(dt), back, qkind, arrtab)}) == goal
  : T.Doc}:
  Equal.trans(T.Doc,
    T.doc.read(String.append(tt, String.append(D2.gap(gs), SCon{kl.dl(cl), rest})), T.doc.scan(M6.wh.st(rows,
      heads, here, M12.wh.ps(dt, parts), [], M12.kl.lex0(dt), back, qkind, arrtab), Chr{xx})),
    T.doc.read(String.append(tt, String.append(D2.gap(gs), SCon{kl.dl(cl), rest})), T.MScan{M6.wh.st(rows,
      heads, here, M12.wh.ps(dt, parts), [Chr{xx}], T.LKey{}, back, qkind, arrtab)}),
    goal,
    Equal.cong(T.Mode, T.Doc, md => T.doc.read(String.append(tt, String.append(D2.gap(gs),
      SCon{kl.dl(cl), rest})), md),
      T.doc.scan(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.kl.lex0(dt), back, qkind, arrtab), Chr{xx}),
      T.MScan{M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [Chr{xx}], T.LKey{}, back, qkind, arrtab)},
      M12.kl.b1(dt, rows, heads, here, parts, back, qkind, arrtab, xx,
        M16.ball.head(T.bare.at(Chr{xx}), String.to_list(tt), ee))),
    Equal.trans(T.Doc,
      T.doc.read(String.append(tt, String.append(D2.gap(gs), SCon{kl.dl(cl), rest})), T.MScan{M6.wh.st(rows,
        heads, here, M12.wh.ps(dt, parts), [Chr{xx}], T.LKey{}, back, qkind, arrtab)}),
      T.doc.read(String.append(D2.gap(gs), SCon{kl.dl(cl), rest}), T.MScan{M6.wh.st(rows, heads, here,
        M12.wh.ps(dt, parts), M3.rev.onto(tt, [Chr{xx}]), T.LKey{}, back, qkind, arrtab)}),
      goal,
      kl.bbody(tt, String.append(D2.gap(gs), SCon{kl.dl(cl), rest}), rows, heads, here, M12.wh.ps(dt, parts),
        [Chr{xx}], back, qkind, arrtab, M16.ball.tail(T.bare.at(Chr{xx}), String.to_list(tt), ee)),
      Equal.trans(T.Doc,
        T.doc.read(String.append(D2.gap(gs), SCon{kl.dl(cl), rest}), T.MScan{M6.wh.st(rows, heads, here,
          M12.wh.ps(dt, parts), M3.rev.onto(tt, [Chr{xx}]), T.LKey{}, back, qkind, arrtab)}),
        T.doc.read(rest, T.MScan{M6.wh.st(rows, heads, here, T.buf.str(M3.rev.onto(tt, [Chr{xx}])) <>
          M12.wh.ps(dt, parts), [], kl.aft(cl), back, qkind, arrtab)}),
        goal,
        kl.bend(gs, cl, rows, heads, here, M12.wh.ps(dt, parts), M3.rev.onto(tt, [Chr{xx}]), back, qkind, arrtab,
          rest, M16.rev.full(tt, Chr{xx}, [])),
        kl.nm(SCon{Chr{xx}, tt}, M3.rev.onto(tt, [Chr{xx}]), M16.wh.bname(xx, tt), cl, rows, heads, here,
          M12.wh.ps(dt, parts), back, qkind, arrtab, rest, goal, ih))))

# a quotation mark where a segment starts opens a basic segment
def kl.qopen(
  dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool
) -> {T.doc.scan(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.kl.lex0(dt), back, qkind, arrtab), '"')
  == T.MScan{M9.qs(False{}, rows, heads, here, M12.wh.ps(dt, parts), [], arrtab, back, [])} : T.Mode}:
  match dt:
    case False{}:
      {==}
    case True{}:
      {==}

# and an apostrophe a literal one
def kl.lopen(
  dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool
) -> {T.doc.scan(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.kl.lex0(dt), back, qkind, arrtab), '\'')
  == T.MScan{M6.ql(False{}, rows, heads, here, M12.wh.ps(dt, parts), arrtab, back, [])} : T.Mode}:
  match dt:
    case False{}:
      {==}
    case True{}:
      {==}

# a basic segment, its blank space and a dot or `=`: the rest is read with the
# segment pushed under its name, from wherever the last escape left back
def kl.qseg(
  +ss: String,
  +gs: List<&2, Bool>,
  +cl: Bool,
  +dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +rest: String,
  +goal: T.Doc,
  ih: kl.Then(cl, rows, heads, here, ss <> M12.wh.ps(dt, parts), arrtab, rest, goal)
) -> {T.doc.read(String.append(T.key.basic(ss), String.append(D2.gap(gs), SCon{kl.dl(cl), rest})),
  T.MScan{M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.kl.lex0(dt), back, qkind, arrtab)}) == goal
  : T.Doc}:
  Equal.trans(T.Doc,
    T.doc.read(String.append(T.key.basic(ss), String.append(D2.gap(gs), SCon{kl.dl(cl), rest})),
      T.MScan{M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.kl.lex0(dt), back, qkind, arrtab)}),
    T.doc.read(String.append(String.append(L7.escs(ss), "\""), String.append(D2.gap(gs),
      SCon{kl.dl(cl), rest})), T.doc.scan(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.kl.lex0(dt), back,
      qkind, arrtab), '"')),
    goal,
    Equal.cong(String, T.Doc, zz => T.doc.read(String.append(zz, String.append(D2.gap(gs),
      SCon{kl.dl(cl), rest})), T.MScan{M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.kl.lex0(dt), back,
      qkind, arrtab)}),
      T.key.basic(ss), "\"" ++ L7.escs(ss) ++ "\"", L7.basic_escs(ss)),
    Equal.trans(T.Doc,
      T.doc.read(String.append(String.append(L7.escs(ss), "\""), String.append(D2.gap(gs),
        SCon{kl.dl(cl), rest})), T.doc.scan(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.kl.lex0(dt), back,
        qkind, arrtab), '"')),
      T.doc.read(String.append(L7.escs(ss), SCon{'"', String.append(D2.gap(gs), SCon{kl.dl(cl), rest})}),
        T.MScan{M9.qs(False{}, rows, heads, here, M12.wh.ps(dt, parts), [], arrtab, back, [])}),
      goal,
      Equal.trans(T.Doc,
        T.doc.read(String.append(String.append(L7.escs(ss), "\""), String.append(D2.gap(gs),
          SCon{kl.dl(cl), rest})), T.doc.scan(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.kl.lex0(dt),
          back, qkind, arrtab), '"')),
        T.doc.read(String.append(L7.escs(ss), SCon{'"', String.append(D2.gap(gs), SCon{kl.dl(cl),
          rest})}), T.doc.scan(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.kl.lex0(dt), back, qkind,
          arrtab), '"')),
        T.doc.read(String.append(L7.escs(ss), SCon{'"', String.append(D2.gap(gs), SCon{kl.dl(cl),
          rest})}), T.MScan{M9.qs(False{}, rows, heads, here, M12.wh.ps(dt, parts), [], arrtab, back, [])}),
        Equal.cong(String, T.Doc, zz => T.doc.read(zz, T.doc.scan(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts),
          [], M12.kl.lex0(dt), back, qkind, arrtab), '"')),
          String.append(String.append(L7.escs(ss), "\""), String.append(D2.gap(gs), SCon{kl.dl(cl),
            rest})),
          String.append(L7.escs(ss), SCon{'"', String.append(D2.gap(gs), SCon{kl.dl(cl), rest})}),
          Eq.append_assoc(L7.escs(ss), "\"", String.append(D2.gap(gs), SCon{kl.dl(cl), rest}))),
        Equal.cong(T.Mode, T.Doc, md => T.doc.read(String.append(L7.escs(ss), SCon{'"',
          String.append(D2.gap(gs), SCon{kl.dl(cl), rest})}), md),
          T.doc.scan(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.kl.lex0(dt), back, qkind, arrtab), '"'),
          T.MScan{M9.qs(False{}, rows, heads, here, M12.wh.ps(dt, parts), [], arrtab, back, [])},
          kl.qopen(dt, rows, heads, here, parts, back, qkind, arrtab))),
      M10.qs.escs(ss, False{}, rows, heads, here, M12.wh.ps(dt, parts), [], arrtab, back, [],
        SCon{'"', String.append(D2.gap(gs), SCon{kl.dl(cl), rest})}, goal,
        +bk => Equal.trans(T.Doc,
          T.doc.read(SCon{'"', String.append(D2.gap(gs), SCon{kl.dl(cl), rest})}, T.MScan{M9.qs(False{}, rows,
            heads, here, M12.wh.ps(dt, parts), [], arrtab, bk, M3.rev.onto(ss, []))}),
          T.doc.read(String.append(D2.gap(gs), SCon{kl.dl(cl), rest}), T.MScan{M6.wh.st(rows, heads, here,
            T.buf.str(M3.rev.onto(ss, [])) <> M12.wh.ps(dt, parts), [], T.LAfter{}, bk, T.QBasic{}, arrtab)}),
          goal,
          {==},
          kl.fin(ss, M3.rev.onto(ss, []), M12.wh.qname(ss), gs, cl, rows, heads, here, M12.wh.ps(dt, parts), bk,
            T.QBasic{}, arrtab, rest, goal, ih)))))

# a literal segment, its blank space and a dot or `=`: the rest is read with
# the segment pushed under its characters, and back as it was
def kl.lseg(
  +ss: String,
  +gs: List<&2, Bool>,
  +cl: Bool,
  +dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +rest: String,
  +goal: T.Doc,
  el: {Laws.lit.text(ss) == True{} : Bool},
  ih: kl.Then(cl, rows, heads, here, ss <> M12.wh.ps(dt, parts), arrtab, rest, goal)
) -> {T.doc.read(String.append(SCon{'\'', String.append(ss, "'")}, String.append(D2.gap(gs),
  SCon{kl.dl(cl), rest})), T.MScan{M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.kl.lex0(dt), back, qkind,
  arrtab)}) == goal : T.Doc}:
  Equal.trans(T.Doc,
    T.doc.read(String.append(String.append(ss, "'"), String.append(D2.gap(gs), SCon{kl.dl(cl), rest})),
      T.doc.scan(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.kl.lex0(dt), back, qkind, arrtab), '\'')),
    T.doc.read(String.append(ss, SCon{'\'', String.append(D2.gap(gs), SCon{kl.dl(cl), rest})}),
      T.MScan{M6.ql(False{}, rows, heads, here, M12.wh.ps(dt, parts), arrtab, back, [])}),
    goal,
    Equal.trans(T.Doc,
      T.doc.read(String.append(String.append(ss, "'"), String.append(D2.gap(gs), SCon{kl.dl(cl), rest})),
        T.doc.scan(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.kl.lex0(dt), back, qkind, arrtab), '\'')),
      T.doc.read(String.append(ss, SCon{'\'', String.append(D2.gap(gs), SCon{kl.dl(cl), rest})}),
        T.doc.scan(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.kl.lex0(dt), back, qkind, arrtab), '\'')),
      T.doc.read(String.append(ss, SCon{'\'', String.append(D2.gap(gs), SCon{kl.dl(cl), rest})}),
        T.MScan{M6.ql(False{}, rows, heads, here, M12.wh.ps(dt, parts), arrtab, back, [])}),
      Equal.cong(String, T.Doc, zz => T.doc.read(zz, T.doc.scan(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [],
        M12.kl.lex0(dt), back, qkind, arrtab), '\'')),
        String.append(String.append(ss, "'"), String.append(D2.gap(gs), SCon{kl.dl(cl), rest})),
        String.append(ss, SCon{'\'', String.append(D2.gap(gs), SCon{kl.dl(cl), rest})}),
        Eq.append_assoc(ss, "'", String.append(D2.gap(gs), SCon{kl.dl(cl), rest}))),
      Equal.cong(T.Mode, T.Doc, md => T.doc.read(String.append(ss, SCon{'\'', String.append(D2.gap(gs),
        SCon{kl.dl(cl), rest})}), md),
        T.doc.scan(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.kl.lex0(dt), back, qkind, arrtab), '\''),
        T.MScan{M6.ql(False{}, rows, heads, here, M12.wh.ps(dt, parts), arrtab, back, [])},
        kl.lopen(dt, rows, heads, here, parts, back, qkind, arrtab))),
    Equal.trans(T.Doc,
      T.doc.read(String.append(ss, SCon{'\'', String.append(D2.gap(gs), SCon{kl.dl(cl), rest})}),
        T.MScan{M6.ql(False{}, rows, heads, here, M12.wh.ps(dt, parts), arrtab, back, [])}),
      T.doc.read(SCon{'\'', String.append(D2.gap(gs), SCon{kl.dl(cl), rest})},
        T.MScan{M6.ql(False{}, rows, heads, here, M12.wh.ps(dt, parts), arrtab, back, M3.rev.onto(ss, []))}),
      goal,
      ql.body(ss, SCon{'\'', String.append(D2.gap(gs), SCon{kl.dl(cl), rest})}, False{}, rows, heads, here,
        M12.wh.ps(dt, parts), arrtab, back, [], el),
      Equal.trans(T.Doc,
        T.doc.read(SCon{'\'', String.append(D2.gap(gs), SCon{kl.dl(cl), rest})},
          T.MScan{M6.ql(False{}, rows, heads, here, M12.wh.ps(dt, parts), arrtab, back, M3.rev.onto(ss, []))}),
        T.doc.read(String.append(D2.gap(gs), SCon{kl.dl(cl), rest}), T.MScan{M6.wh.st(rows, heads, here,
          T.buf.str(M3.rev.onto(ss, [])) <> M12.wh.ps(dt, parts), [], T.LAfter{}, back, T.QLit{}, arrtab)}),
        goal,
        {==},
        kl.fin(ss, M3.rev.onto(ss, []), M12.wh.qname(ss), gs, cl, rows, heads, here, M12.wh.ps(dt, parts), back,
          T.QLit{}, arrtab, rest, goal, ih))))

# a segment spelled any way it can be, its blank space and a dot or `=`
def kl.seg(
  sg: D3.Seg,
  +gs: List<&2, Bool>,
  +cl: Bool,
  +dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +rest: String,
  +goal: T.Doc,
  eo: {Laws.seg.ok(sg) == True{} : Bool},
  ih: kl.Then(cl, rows, heads, here, Laws.seg.name(sg) <> M12.wh.ps(dt, parts), arrtab, rest, goal)
) -> {T.doc.read(String.append(Laws.seg.text(sg), String.append(D2.gap(gs), SCon{kl.dl(cl), rest})),
  T.MScan{M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.kl.lex0(dt), back, qkind, arrtab)}) == goal
  : T.Doc}:
  match sg:
    case D3.Seg{sp, +name}:
      match sp:
        case D3.SpBare{}:
          match name:
            case SNil{}:
              Eq.bit.absurd(&2, {T.doc.read(String.append(SNil{}, String.append(D2.gap(gs), SCon{kl.dl(cl),
                rest})), T.MScan{M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.kl.lex0(dt), back, qkind,
                arrtab)}) == goal : T.Doc}, eo)
            case SCon{hh, +tt}:
              match hh:
                case Chr{+xx}:
                  kl.bseg(xx, tt, gs, cl, dt, rows, heads, here, parts, back, qkind, arrtab, rest, goal, eo, ih)
        case D3.SpBasic{}:
          kl.qseg(name, gs, cl, dt, rows, heads, here, parts, back, qkind, arrtab, rest, goal, ih)
        case D3.SpLit{}:
          kl.lseg(name, gs, cl, dt, rows, heads, here, parts, back, qkind, arrtab, rest, goal, eo, ih)

# the key's segments pushed onto the parts before them, newest first
def kl.acc(ds: List<&2, D3.Dot>, last: D3.Seg, dt: Bool, parts: List<&2, String>) -> List<&2, String>:
  List.reverse.go(&2, String, Laws.dk.names(ds, last), M12.wh.ps(dt, parts))

# a dotted key's segments, then blank space and `=`: the rest is read with
# every segment pushed onto parts, newest first
def kl.keys(
  ds: List<&2, D3.Dot>,
  +last: D3.Seg,
  +g: List<&2, Bool>,
  +dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +rest: String,
  +goal: T.Doc,
  +eo: {Laws.dk.ok(ds, last) == True{} : Bool},
  ih: kl.Then(True{}, rows, heads, here, kl.acc(ds, last, dt, parts), arrtab, rest, goal)
) -> {T.doc.read(Laws.dk.text(ds, last, String.append(D2.gap(g), SCon{'=', rest})), T.MScan{M6.wh.st(rows,
  heads, here, M12.wh.ps(dt, parts), [], M12.kl.lex0(dt), back, qkind, arrtab)}) == goal : T.Doc}:
  match ds:
    case []:
      kl.seg(last, g, True{}, dt, rows, heads, here, parts, back, qkind, arrtab, rest, goal, eo, ih)
    case D3.Dot{+sg, g1, +g2} <> +dr:
      kl.seg(sg, g1, False{}, dt, rows, heads, here, parts, back, qkind, arrtab,
        String.append(D2.gap(g2), Laws.dk.text(dr, last, String.append(D2.gap(g), SCon{'=', rest}))), goal,
        Eq.and.left(Laws.seg.ok(sg), Laws.dk.ok(dr, last), eo),
        +bk => +qk => Equal.trans(T.Doc,
          T.doc.read(String.append(D2.gap(g2), Laws.dk.text(dr, last, String.append(D2.gap(g), SCon{'=',
            rest}))), T.MScan{M6.wh.st(rows, heads, here, Laws.seg.name(sg) <> M12.wh.ps(dt, parts), [], T.LKeyDot{},
            bk, qk, arrtab)}),
          T.doc.read(Laws.dk.text(dr, last, String.append(D2.gap(g), SCon{'=', rest})), T.MScan{M6.wh.st(rows,
            heads, here, Laws.seg.name(sg) <> M12.wh.ps(dt, parts), [], T.LKeyDot{}, bk, qk, arrtab)}),
          goal,
          kl.dgap(g2, Laws.dk.text(dr, last, String.append(D2.gap(g), SCon{'=', rest})), rows, heads, here,
            Laws.seg.name(sg) <> M12.wh.ps(dt, parts), bk, qk, arrtab),
          kl.keys(dr, last, g, True{}, rows, heads, here, Laws.seg.name(sg) <> M12.wh.ps(dt, parts), bk, qk, arrtab,
            rest, goal, Eq.and.right(Laws.seg.ok(sg), Laws.dk.ok(dr, last), eo), ih)))

def Laws.dotted_key_reads_back(ds, last, ok, g, rows, heads, here, back, qkind, arrtab, rest, goal, ih):
  kl.keys(ds, last, g, False{}, rows, heads, here, [], back, qkind, arrtab, rest, goal, ok, ih)

# WP-K3: a dotted key's value put by the walk. Each step is WP-W's
# navigation step (sub.step) while skip counts down, and once it reaches zero
# a dotted key's step: it enters a table no header defined, or makes an
# implicit one, and records the path behind `.`. The frames pushed are the
# same as navigation's (tb.fr), so WP-W's nav.rebuild puts every table back.

# where a put's step leaves the walk
def dsub.Goal(
  +look: T.Look,
  +seg: String,
  +vs: List<&2, T.Val>,
  +v: T.Val,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +mark: Bool
) -> Type:
  {T.tree.sub.look(look, seg, vs, T.JPut{v}, stack, pre, heads, inl, mark)
    == T.Tw{D1.tb.into(look), T.JPut{v}, M8.tb.fr(look, seg, vs, pre) <> stack, "", T.tree.pre(pre, seg),
      Laws.dk.mark(mark, T.tree.pre(pre, seg), heads), inl} : T.Tw}

# the code records a dotted key's table as the law says: behind `.`, once
def dk.mark.eq(
  seen: Bool,
  +path: String,
  +heads: List<&2, String>
) -> {T.heads.define.new(seen, path, heads) == Laws.dk.mark.new(seen, path, heads) : List<&2, String>}:
  match seen:
    case True{}:
      {==}
    case False{}:
      {==}

# a dotted key's step enters a table no header defined, or makes a new one
def dsub.dot(
  +look: T.Look,
  +seg: String,
  +vs: List<&2, T.Val>,
  +v: T.Val,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  ec: {Laws.dk.can.dot(look, heads, T.tree.pre(pre, seg)) == True{} : Bool}
) -> dsub.Goal(look, seg, vs, v, stack, pre, heads, inl, True{}):
  match look:
    case T.KMiss{}:
      Equal.cong(List<&2, String>, T.Tw, hh => T.Tw{[], T.JPut{v}, T.FrNew{seg, vs, T.tree.pre(pre, seg)} <> stack,
        "", T.tree.pre(pre, seg), hh, inl},
        T.heads.define.new(T.heads.has(heads, T.tree.pre(pre, seg)), T.tree.pre(pre, seg), heads),
        Laws.dk.mark.new(T.heads.has(heads, T.tree.pre(pre, seg)), T.tree.pre(pre, seg), heads),
        dk.mark.eq(T.heads.has(heads, T.tree.pre(pre, seg)), T.tree.pre(pre, seg), heads))
    case T.KHead{+p, +rr}:
      Equal.trans(T.Tw,
        T.tree.sub.head.go(T.heads.head(heads, T.tree.pre(pre, seg)), p, rr, seg, vs, T.JPut{v}, stack, pre, heads,
          inl, True{}),
        T.tree.sub.head.go(False{}, p, rr, seg, vs, T.JPut{v}, stack, pre, heads, inl, True{}),
        T.Tw{rr, T.JPut{v}, T.FrRep{seg, vs, p} <> stack, "", T.tree.pre(pre, seg),
          Laws.dk.mark(True{}, T.tree.pre(pre, seg), heads), inl},
        Equal.cong(Bool, T.Tw, bb => T.tree.sub.head.go(bb, p, rr, seg, vs, T.JPut{v}, stack, pre, heads, inl,
          True{}), T.heads.head(heads, T.tree.pre(pre, seg)), False{},
          Eq.not.true(T.heads.head(heads, T.tree.pre(pre, seg)), ec)),
        Equal.cong(List<&2, String>, T.Tw, hh => T.Tw{rr, T.JPut{v}, T.FrRep{seg, vs, p} <> stack, "",
          T.tree.pre(pre, seg), hh, inl},
          T.heads.define.new(T.heads.has(heads, T.tree.pre(pre, seg)), T.tree.pre(pre, seg), heads),
          Laws.dk.mark.new(T.heads.has(heads, T.tree.pre(pre, seg)), T.tree.pre(pre, seg), heads),
          dk.mark.eq(T.heads.has(heads, T.tree.pre(pre, seg)), T.tree.pre(pre, seg), heads)))
    case T.KInl{}:
      Eq.bit.absurd(&1, dsub.Goal(T.KInl{}, seg, vs, v, stack, pre, heads, inl, True{}), ec)
    case T.KAots{p, es}:
      Eq.bit.absurd(&1, dsub.Goal(T.KAots{p, es}, seg, vs, v, stack, pre, heads, inl, True{}), ec)
    case T.KNo{why}:
      Eq.bit.absurd(&1, dsub.Goal(T.KNo{why}, seg, vs, v, stack, pre, heads, inl, True{}), ec)

# a put's step: navigation, or a dotted key's segment
def dsub.step(
  mark: Bool,
  +look: T.Look,
  +seg: String,
  +vs: List<&2, T.Val>,
  +v: T.Val,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  ec: {Laws.dk.can(mark, look, heads, T.tree.pre(pre, seg)) == True{} : Bool}
) -> dsub.Goal(look, seg, vs, v, stack, pre, heads, inl, mark):
  match mark:
    case False{}:
      M8.sub.step(look, seg, vs, T.JPut{v}, stack, pre, heads, inl, False{}, ec, {==})
    case True{}:
      dsub.dot(look, seg, vs, v, stack, pre, heads, inl, ec)

# by induction on the path: each segment is one step of the put's walk
def dk.walk(
  path: List<&2, String>,
  +kk: String,
  +vs: List<&2, T.Val>,
  +v: T.Val,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +skip: U32,
  +eo: {Laws.dk.open(path, pre, vs, heads, skip) == True{} : Bool}
) -> {T.tree.walk(List.append(&2, String, path, [kk]), T.Tw{vs, T.JPut{v}, stack, "", pre, heads, inl}, skip)
  == T.tree.leaf(kk, T.Tw{D1.tb.rows(path, vs), T.JPut{v}, M8.nav.frs(path, pre, vs, stack), "",
    D1.tb.join(path, pre), Laws.dk.heads(path, pre, heads, skip), inl}) : T.End}:
  match path:
    case []:
      {==}
    case +seg <> +rest:
      Equal.trans(T.End,
        T.tree.walk(seg <> List.append(&2, String, rest, [kk]), T.Tw{vs, T.JPut{v}, stack, "", pre, heads, inl},
          skip),
        T.tree.walk(List.append(&2, String, rest, [kk]), T.Tw{D1.tb.into(T.rows.look(vs, seg)), T.JPut{v},
          M8.tb.fr(T.rows.look(vs, seg), seg, vs, pre) <> stack, "", T.tree.pre(pre, seg),
          Laws.dk.mark(U32.is_zero(skip), T.tree.pre(pre, seg), heads), inl}, T.path.dec(skip)),
        T.tree.leaf(kk, T.Tw{D1.tb.rows(rest, D1.tb.into(T.rows.look(vs, seg))), T.JPut{v},
          M8.nav.frs(rest, T.tree.pre(pre, seg), D1.tb.into(T.rows.look(vs, seg)),
            M8.tb.fr(T.rows.look(vs, seg), seg, vs, pre) <> stack), "",
          D1.tb.join(rest, T.tree.pre(pre, seg)), Laws.dk.heads(rest, T.tree.pre(pre, seg),
            Laws.dk.mark(U32.is_zero(skip), T.tree.pre(pre, seg), heads), T.path.dec(skip)), inl}),
        Equal.trans(T.End,
          T.tree.walk(seg <> List.append(&2, String, rest, [kk]), T.Tw{vs, T.JPut{v}, stack, "", pre, heads,
            inl}, skip),
          T.tree.walk(List.append(&2, String, rest, [kk]), T.tree.sub(seg, T.Tw{vs, T.JPut{v}, stack, "",
            pre, heads, inl}, U32.is_zero(skip)), T.path.dec(skip)),
          T.tree.walk(List.append(&2, String, rest, [kk]), T.Tw{D1.tb.into(T.rows.look(vs, seg)), T.JPut{v},
            M8.tb.fr(T.rows.look(vs, seg), seg, vs, pre) <> stack, "", T.tree.pre(pre, seg),
            Laws.dk.mark(U32.is_zero(skip), T.tree.pre(pre, seg), heads), inl}, T.path.dec(skip)),
          M8.walk.cons(seg, rest, kk, T.Tw{vs, T.JPut{v}, stack, "", pre, heads, inl}, skip),
          Equal.cong(T.Tw, T.End,
            tw => T.tree.walk(List.append(&2, String, rest, [kk]), tw, T.path.dec(skip)),
            T.tree.sub(seg, T.Tw{vs, T.JPut{v}, stack, "", pre, heads, inl}, U32.is_zero(skip)),
            T.Tw{D1.tb.into(T.rows.look(vs, seg)), T.JPut{v}, M8.tb.fr(T.rows.look(vs, seg), seg, vs, pre)
              <> stack, "", T.tree.pre(pre, seg), Laws.dk.mark(U32.is_zero(skip), T.tree.pre(pre, seg),
              heads), inl},
            dsub.step(U32.is_zero(skip), T.rows.look(vs, seg), seg, vs, v, stack, pre, heads, inl,
              Eq.and.left(Laws.dk.can(U32.is_zero(skip), T.rows.look(vs, seg), heads, T.tree.pre(pre, seg)),
                Laws.dk.open(rest, T.tree.pre(pre, seg), D1.tb.into(T.rows.look(vs, seg)),
                  Laws.dk.mark(U32.is_zero(skip), T.tree.pre(pre, seg), heads), T.path.dec(skip)), eo)))),
        dk.walk(rest, kk, D1.tb.into(T.rows.look(vs, seg)), v, M8.tb.fr(T.rows.look(vs, seg), seg, vs, pre)
          <> stack, T.tree.pre(pre, seg), Laws.dk.mark(U32.is_zero(skip), T.tree.pre(pre, seg), heads), inl,
          T.path.dec(skip),
          Eq.and.right(Laws.dk.can(U32.is_zero(skip), T.rows.look(vs, seg), heads, T.tree.pre(pre, seg)),
            Laws.dk.open(rest, T.tree.pre(pre, seg), D1.tb.into(T.rows.look(vs, seg)),
              Laws.dk.mark(U32.is_zero(skip), T.tree.pre(pre, seg), heads), T.path.dec(skip)), eo)))

# a step a put goes on through is one a walk can go on through
def dk.can.tb(
  zz: Bool,
  look: T.Look,
  heads: List<&2, String>,
  path: String,
  ee: {Laws.dk.can(zz, look, heads, path) == True{} : Bool}
) -> {D1.tb.can(look) == True{} : Bool}:
  match zz:
    case False{}:
      ee
    case True{}:
      match look:
        case T.KMiss{}:
          {==}
        case T.KHead{_p, _r}:
          {==}
        case T.KInl{}:
          Eq.bit.absurd(&2, {D1.tb.can(T.KInl{}) == True{} : Bool}, ee)
        case T.KAots{p, es}:
          Eq.bit.absurd(&2, {D1.tb.can(T.KAots{p, es}) == True{} : Bool}, ee)
        case T.KNo{why}:
          Eq.bit.absurd(&2, {D1.tb.can(T.KNo{why}) == True{} : Bool}, ee)

# both halves of an `and` answered True
def dk.and(
  aa: Bool,
  bb: Bool,
  ea: {aa == True{} : Bool},
  eb: {bb == True{} : Bool}
) -> {Bool.and(aa, bb) == True{} : Bool}:
  match aa:
    case True{}:
      eb
    case False{}:
      Eq.bit.absurd(&2, {Bool.and(False{}, bb) == True{} : Bool}, ea)

# a path a put goes on through is one a walk goes on through
def dk.tb(
  path: List<&2, String>,
  +pre: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +skip: U32,
  +eo: {Laws.dk.open(path, pre, rows, heads, skip) == True{} : Bool}
) -> {D1.tb.open(path, rows) == True{} : Bool}:
  match path:
    case []:
      {==}
    case +seg <> +rest:
      dk.and(D1.tb.can(T.rows.look(rows, seg)), D1.tb.open(rest, D1.tb.into(T.rows.look(rows, seg))),
        dk.can.tb(U32.is_zero(skip), T.rows.look(rows, seg), heads, T.tree.pre(pre, seg),
          Eq.and.left(Laws.dk.can(U32.is_zero(skip), T.rows.look(rows, seg), heads, T.tree.pre(pre, seg)),
            Laws.dk.open(rest, T.tree.pre(pre, seg), D1.tb.into(T.rows.look(rows, seg)),
              Laws.dk.mark(U32.is_zero(skip), T.tree.pre(pre, seg), heads), T.path.dec(skip)), eo)),
        dk.tb(rest, T.tree.pre(pre, seg), D1.tb.into(T.rows.look(rows, seg)),
          Laws.dk.mark(U32.is_zero(skip), T.tree.pre(pre, seg), heads), T.path.dec(skip),
          Eq.and.right(Laws.dk.can(U32.is_zero(skip), T.rows.look(rows, seg), heads, T.tree.pre(pre, seg)),
            Laws.dk.open(rest, T.tree.pre(pre, seg), D1.tb.into(T.rows.look(rows, seg)),
              Laws.dk.mark(U32.is_zero(skip), T.tree.pre(pre, seg), heads), T.path.dec(skip)), eo)))

def Laws.dotted_put_at_head(path, k, v, rows, heads, skip, inl, eo, em):
  Equal.trans(T.End,
    T.tree.walk(List.append(&2, String, path, [k]), T.Tw{rows, T.JPut{v}, [], "", "", heads, inl}, skip),
    T.tree.leaf(k, T.Tw{D1.tb.rows(path, rows), T.JPut{v}, M8.nav.frs(path, "", rows, []), "",
      D1.tb.join(path, ""), Laws.dk.heads(path, "", heads, skip), inl}),
    T.End{D1.tb.set(path, "", rows, T.VPair{k, v} <> D1.tb.rows(path, rows)), "",
      Laws.dk.heads(path, "", heads, skip)},
    dk.walk(path, k, rows, v, [], "", heads, inl, skip, eo),
    Equal.trans(T.End,
      T.tree.leaf(k, T.Tw{D1.tb.rows(path, rows), T.JPut{v}, M8.nav.frs(path, "", rows, []), "",
        D1.tb.join(path, ""), Laws.dk.heads(path, "", heads, skip), inl}),
      T.tree.rebuild(M8.nav.frs(path, "", rows, []), T.VPair{k, v} <> D1.tb.rows(path, rows), "",
        Laws.dk.heads(path, "", heads, skip)),
      T.End{D1.tb.set(path, "", rows, T.VPair{k, v} <> D1.tb.rows(path, rows)), "",
        Laws.dk.heads(path, "", heads, skip)},
      Equal.cong(T.Hit, T.End,
        hh => T.tree.leaf.put(hh, k, D1.tb.rows(path, rows), v, M8.nav.frs(path, "", rows, []), "",
          Laws.dk.heads(path, "", heads, skip)),
        T.get(D1.tb.rows(path, rows), k), T.Miss{}, em),
      M8.nav.rebuild(path, "", rows, [], T.VPair{k, v} <> D1.tb.rows(path, rows), "",
        Laws.dk.heads(path, "", heads, skip), dk.tb(path, "", rows, heads, skip, eo))))

# the put's walk of the value 1 along the path, from the table here, returns
# these rows and definitions
def kv.Walk(
  path: List<&2, String>,
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  rows2: List<&2, T.Val>,
  heads2: List<&2, String>
) -> Type:
  {T.tree.walk(path, T.Tw{rows, T.JPut{D1.one()}, [], "", "", heads, False{}}, T.path.len(here, 0))
    == T.End{rows2, "", heads2} : T.End}

# " 1" and a newline after `=`: the value is put by the walk, and the next line
# starts in the same table
def kv.line(
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +arrtab: Bool,
  +rows2: List<&2, T.Val>,
  +heads2: List<&2, String>,
  +rest: String,
  ew: kv.Walk(T.path.cat(here, parts), rows, heads, here, rows2, heads2)
) -> {T.doc.read(SCon{' ', SCon{'1', SCon{'\n', rest}}}, T.MScan{Laws.kb.val(rows, heads, here, parts, bk, qk,
  arrtab)}) == T.doc.read(rest, T.MScan{Laws.hb.line(rows2, heads2, here, bk, qk, arrtab)}) : T.Doc}:
  Equal.cong(T.End, T.Doc,
    en => T.doc.read(rest, T.MScan{T.read.once2(T.bare.line.go(T.take.root(en, here, bk, qk, 0, 0, arrtab,
      False{})))}),
    T.tree.walk(T.path.cat(here, parts), T.Tw{rows, T.JPut{D1.one()}, [], "", "", heads, False{}},
      T.path.len(here, 0)),
    T.End{rows2, "", heads2}, ew)

# the walk the line runs is along here and the key's names
def kv.walk(
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +names: List<&2, String>,
  +rows2: List<&2, T.Val>,
  +heads2: List<&2, String>,
  ew: kv.Walk(List.append(&2, String, here, names), rows, heads, here, rows2, heads2)
) -> kv.Walk(T.path.cat(here, List.reverse(&2, String, names)), rows, heads, here, rows2, heads2):
  Equal.trans(T.End,
    T.tree.walk(List.append(&2, String, here, List.reverse(&2, String, List.reverse(&2, String, names))),
      T.Tw{rows, T.JPut{D1.one()}, [], "", "", heads, False{}}, T.path.len(here, 0)),
    T.tree.walk(List.append(&2, String, here, names), T.Tw{rows, T.JPut{D1.one()}, [], "", "", heads,
      False{}}, T.path.len(here, 0)),
    T.End{rows2, "", heads2},
    Equal.cong(List<&2, String>, T.End, xs => T.tree.walk(List.append(&2, String, here, xs), T.Tw{rows,
      T.JPut{D1.one()}, [], "", "", heads, False{}}, T.path.len(here, 0)),
      List.reverse(&2, String, List.reverse(&2, String, names)), names, M5.kv.rr(names)),
    ew)

def Laws.dotted_key_pair_reads_back(
  ds,
  last,
  ok,
  g,
  rows,
  heads,
  here,
  back,
  qkind,
  arrtab,
  rows2,
  heads2,
  ew,
  rest,
  goal,
  ih
):
  Laws.dotted_key_reads_back(ds, last, ok, g, rows, heads, here, back, qkind, arrtab, String.append(" 1\n", rest),
    goal,
    +bk => +qk => Equal.trans(T.Doc,
      T.doc.read(String.append(" 1\n", rest), T.MScan{Laws.kb.val(rows, heads, here, List.reverse(&2, String,
        Laws.dk.names(ds, last)), bk, qk, arrtab)}),
      T.doc.read(rest, T.MScan{Laws.hb.line(rows2, heads2, here, bk, qk, arrtab)}),
      goal,
      kv.line(rows, heads, here, List.reverse(&2, String, Laws.dk.names(ds, last)), bk, qk, arrtab, rows2,
        heads2, rest, kv.walk(rows, heads, here, Laws.dk.names(ds, last), rows2, heads2, ew)),
      ih(bk, qk)))

# appending lists is associative
def la.assoc(
  xs: List<&2, String>,
  +ys: List<&2, String>,
  +zs: List<&2, String>
) -> {List.append(&2, String, List.append(&2, String, xs, ys), zs)
  == List.append(&2, String, xs, List.append(&2, String, ys, zs)) : List<&2, String>}:
  match xs:
    case []:
      {==}
    case +xx <> rest:
      Equal.cong(List<&2, String>, List<&2, String>, tt => xx <> tt,
        List.append(&2, String, List.append(&2, String, rest, ys), zs),
        List.append(&2, String, rest, List.append(&2, String, ys, zs)), la.assoc(rest, ys, zs))

# a dotted key's names are the names a dot follows, then the last
def dk.split(
  ds: List<&2, D3.Dot>,
  +last: D3.Seg
) -> {Laws.dk.names(ds, last) == List.append(&2, String, Laws.dk.init(ds), [Laws.seg.name(last)])
  : List<&2, String>}:
  match ds:
    case []:
      {==}
    case D3.Dot{+sg, _g1, _g2} <> rest:
      Equal.cong(List<&2, String>, List<&2, String>, tt => Laws.seg.name(sg) <> tt, Laws.dk.names(rest, last),
        List.append(&2, String, Laws.dk.init(rest), [Laws.seg.name(last)]), dk.split(rest, last))

# so the walk's path is here and the names a dot follows, then the last
def dk.path(
  +here: List<&2, String>,
  +ds: List<&2, D3.Dot>,
  +last: D3.Seg
) -> {List.append(&2, String, here, Laws.dk.names(ds, last)) == List.append(&2, String, List.append(&2,
  String, here, Laws.dk.init(ds)), [Laws.seg.name(last)]) : List<&2, String>}:
  Equal.trans(List<&2, String>,
    List.append(&2, String, here, Laws.dk.names(ds, last)),
    List.append(&2, String, here, List.append(&2, String, Laws.dk.init(ds), [Laws.seg.name(last)])),
    List.append(&2, String, List.append(&2, String, here, Laws.dk.init(ds)), [Laws.seg.name(last)]),
    Equal.cong(List<&2, String>, List<&2, String>, xs => List.append(&2, String, here, xs),
      Laws.dk.names(ds, last), List.append(&2, String, Laws.dk.init(ds), [Laws.seg.name(last)]),
      dk.split(ds, last)),
    Equal.sym(List<&2, String>,
      List.append(&2, String, List.append(&2, String, here, Laws.dk.init(ds)), [Laws.seg.name(last)]),
      List.append(&2, String, here, List.append(&2, String, Laws.dk.init(ds), [Laws.seg.name(last)])),
      la.assoc(here, Laws.dk.init(ds), [Laws.seg.name(last)])))

def Laws.dotted_key_pair_puts_value(ds, last, ok, g, rows, heads, here, eo, em, back, qkind, arrtab, rest, goal, ih):
  Laws.dotted_key_pair_reads_back(ds, last, ok, g, rows, heads, here, back, qkind, arrtab,
    D1.tb.set(List.append(&2, String, here, Laws.dk.init(ds)), "", rows, T.VPair{Laws.seg.name(last), D1.one()}
      <> D1.tb.rows(List.append(&2, String, here, Laws.dk.init(ds)), rows)),
    Laws.dk.heads(List.append(&2, String, here, Laws.dk.init(ds)), "", heads, T.path.len(here, 0)),
    Equal.trans(T.End,
      T.tree.walk(List.append(&2, String, here, Laws.dk.names(ds, last)), T.Tw{rows, T.JPut{D1.one()}, [], "",
        "", heads, False{}}, T.path.len(here, 0)),
      T.tree.walk(List.append(&2, String, List.append(&2, String, here, Laws.dk.init(ds)), [Laws.seg.name(last)]),
        T.Tw{rows, T.JPut{D1.one()}, [], "", "", heads, False{}}, T.path.len(here, 0)),
      T.End{D1.tb.set(List.append(&2, String, here, Laws.dk.init(ds)), "", rows, T.VPair{Laws.seg.name(last),
        D1.one()} <> D1.tb.rows(List.append(&2, String, here, Laws.dk.init(ds)), rows)), "",
        Laws.dk.heads(List.append(&2, String, here, Laws.dk.init(ds)), "", heads, T.path.len(here, 0))},
      Equal.cong(List<&2, String>, T.End, xs => T.tree.walk(xs, T.Tw{rows, T.JPut{D1.one()}, [], "", "", heads,
        False{}}, T.path.len(here, 0)),
        List.append(&2, String, here, Laws.dk.names(ds, last)),
        List.append(&2, String, List.append(&2, String, here, Laws.dk.init(ds)), [Laws.seg.name(last)]),
        dk.path(here, ds, last)),
      Laws.dotted_put_at_head(List.append(&2, String, here, Laws.dk.init(ds)), Laws.seg.name(last), D1.one(),
        rows, heads, T.path.len(here, 0), False{}, eo, em)),
    rest, goal, ih)

# and so does a dotted key's
def kl.start(
  ds: List<&2, D3.Dot>,
  +last: D3.Seg,
  +tail: String,
  eo: {Laws.dk.ok(ds, last) == True{} : Bool}
) -> {T.doc.read(Laws.dk.text(ds, last, tail), T.MScan{T.st.start()})
  == T.doc.read(Laws.dk.text(ds, last, tail), T.MScan{Laws.hb.line([], [], [], T.LTop{}, T.QBasic{}, False{})})
  : T.Doc}:
  match ds:
    case []:
      M12.kl.start1(last, tail, eo)
    case D3.Dot{+sg, +g1, +g2} <> +rest:
      M12.kl.start1(sg, String.append(D2.gap(g1), SCon{'.', String.append(D2.gap(g2), Laws.dk.text(rest, last,
        tail))}), Eq.and.left(Laws.seg.ok(sg), Laws.dk.ok(rest, last), eo))

# from the empty root every step makes a new table
def dk.open.nil(
  path: List<&2, String>,
  +pre: String,
  +heads: List<&2, String>
) -> {Laws.dk.open(path, pre, [], heads, 0) == True{} : Bool}:
  match path:
    case []:
      {==}
    case +seg <> rest:
      dk.open.nil(rest, T.tree.pre(pre, seg), Laws.dk.mark(True{}, T.tree.pre(pre, seg), heads))

# and the table at the end is empty
def tb.rows.nil(path: List<&2, String>) -> {D1.tb.rows(path, []) == [] : List<&2, T.Val>}:
  match path:
    case []:
      {==}
    case _seg <> rest:
      tb.rows.nil(rest)

# a longer path goes on in the rows of the table get found
def ka.hd(
  rest: List<&2, String>,
  +kk: String,
  +sub: List<&2, T.Val>,
  +pp: String
) -> {T.at.step(List.append(&2, String, rest, [kk]), T.Found{T.VHead{pp, sub}})
  == T.at(sub, List.append(&2, String, rest, [kk])) : T.Hit}:
  match rest:
    case []:
      {==}
    case _r <> _rr:
      {==}

# at finds the value through the tables made from the empty root, for a
# value sealing leaves alone
def ka.nest(
  path: List<&2, String>,
  +kk: String,
  +pre: String,
  +v: T.Val,
  es: {T.rows.seal([T.VPair{kk, v}]) == [T.VPair{kk, v}] : List<&2, T.Val>}
) -> {T.at(T.rows.seal(D1.tb.set(path, pre, [], [T.VPair{kk, v}])), List.append(&2, String, path, [kk]))
  == T.Found{v} : T.Hit}:
  match path:
    case []:
      Equal.trans(T.Hit, T.get(T.rows.seal([T.VPair{kk, v}]), kk), T.get([T.VPair{kk, v}], kk), T.Found{v},
        Equal.cong(List<&2, T.Val>, T.Hit, xs => T.get(xs, kk), T.rows.seal([T.VPair{kk, v}]), [T.VPair{kk, v}],
          es),
        L4.get_first(kk, v, []))
    case +seg <> +rest:
      Equal.trans(T.Hit,
        T.at.step(List.append(&2, String, rest, [kk]), T.get([T.VPair{seg, T.VHead{T.tree.pre(pre, seg),
          T.rows.seal(D1.tb.set(rest, T.tree.pre(pre, seg), [], [T.VPair{kk, v}]))}}], seg)),
        T.at.step(List.append(&2, String, rest, [kk]), T.Found{T.VHead{T.tree.pre(pre, seg),
          T.rows.seal(D1.tb.set(rest, T.tree.pre(pre, seg), [], [T.VPair{kk, v}]))}}),
        T.Found{v},
        Equal.cong(T.Hit, T.Hit, hh => T.at.step(List.append(&2, String, rest, [kk]), hh),
          T.get([T.VPair{seg, T.VHead{T.tree.pre(pre, seg), T.rows.seal(D1.tb.set(rest, T.tree.pre(pre, seg),
            [], [T.VPair{kk, v}]))}}], seg),
          T.Found{T.VHead{T.tree.pre(pre, seg), T.rows.seal(D1.tb.set(rest, T.tree.pre(pre, seg), [],
            [T.VPair{kk, v}]))}},
          L4.get_first(seg, T.VHead{T.tree.pre(pre, seg), T.rows.seal(D1.tb.set(rest, T.tree.pre(pre, seg),
            [], [T.VPair{kk, v}]))}, [])),
        Equal.trans(T.Hit,
          T.at.step(List.append(&2, String, rest, [kk]), T.Found{T.VHead{T.tree.pre(pre, seg),
            T.rows.seal(D1.tb.set(rest, T.tree.pre(pre, seg), [], [T.VPair{kk, v}]))}}),
          T.at(T.rows.seal(D1.tb.set(rest, T.tree.pre(pre, seg), [], [T.VPair{kk, v}])),
            List.append(&2, String, rest, [kk])),
          T.Found{v},
          ka.hd(rest, kk, T.rows.seal(D1.tb.set(rest, T.tree.pre(pre, seg), [], [T.VPair{kk, v}])),
            T.tree.pre(pre, seg)),
          ka.nest(rest, kk, T.tree.pre(pre, seg), v, es)))

def Laws.dotted_key_line_reads_back(ds, last, ok, g):
  Equal.trans(T.Doc,
    T.doc.read(Laws.dk.text(ds, last, String.append(D2.gap(g), "= 1\n")), T.MScan{T.st.start()}),
    T.doc.read(Laws.dk.text(ds, last, String.append(D2.gap(g), "= 1\n")), T.MScan{Laws.hb.line([], [], [],
      T.LTop{}, T.QBasic{}, False{})}),
    T.Doc{"", T.rows.seal(D1.tb.set(Laws.dk.init(ds), "", [], [T.VPair{Laws.seg.name(last), D1.one()}]))},
    kl.start(ds, last, String.append(D2.gap(g), "= 1\n"), ok),
    Laws.dotted_key_pair_puts_value(ds, last, ok, g, [], [], [], dk.open.nil(Laws.dk.init(ds), "", []),
      Equal.cong(List<&2, T.Val>, T.Hit, xs => T.get(xs, Laws.seg.name(last)), D1.tb.rows(Laws.dk.init(ds), []),
        [], tb.rows.nil(Laws.dk.init(ds))),
      T.LTop{}, T.QBasic{}, False{}, "",
      T.Doc{"", T.rows.seal(D1.tb.set(Laws.dk.init(ds), "", [], [T.VPair{Laws.seg.name(last), D1.one()}]))},
      +_bk => +_qk => Equal.cong(List<&2, T.Val>, T.Doc,
        xs => T.Doc{"", T.rows.seal(D1.tb.set(Laws.dk.init(ds), "", [], T.VPair{Laws.seg.name(last), D1.one()}
          <> xs))}, D1.tb.rows(Laws.dk.init(ds), []), [], tb.rows.nil(Laws.dk.init(ds)))))

def Laws.dotted_key_line_found_by_at(ds, last, ok, g):
  Equal.trans(T.Hit,
    T.at(T.root(T.parse(Laws.dk.text(ds, last, String.append(D2.gap(g), "= 1\n")))), Laws.dk.names(ds, last)),
    T.at(T.rows.seal(D1.tb.set(Laws.dk.init(ds), "", [], [T.VPair{Laws.seg.name(last), D1.one()}])),
      Laws.dk.names(ds, last)),
    T.Found{D1.one()},
    Equal.cong(T.Doc, T.Hit, dd => T.at(T.root(dd), Laws.dk.names(ds, last)),
      T.parse(Laws.dk.text(ds, last, String.append(D2.gap(g), "= 1\n"))),
      T.Doc{"", T.rows.seal(D1.tb.set(Laws.dk.init(ds), "", [], [T.VPair{Laws.seg.name(last), D1.one()}]))},
      Laws.dotted_key_line_reads_back(ds, last, ok, g)),
    Equal.trans(T.Hit,
      T.at(T.rows.seal(D1.tb.set(Laws.dk.init(ds), "", [], [T.VPair{Laws.seg.name(last), D1.one()}])),
        Laws.dk.names(ds, last)),
      T.at(T.rows.seal(D1.tb.set(Laws.dk.init(ds), "", [], [T.VPair{Laws.seg.name(last), D1.one()}])),
        List.append(&2, String, Laws.dk.init(ds), [Laws.seg.name(last)])),
      T.Found{D1.one()},
      Equal.cong(List<&2, String>, T.Hit, ns => T.at(T.rows.seal(D1.tb.set(Laws.dk.init(ds), "", [],
        [T.VPair{Laws.seg.name(last), D1.one()}])), ns), Laws.dk.names(ds, last),
        List.append(&2, String, Laws.dk.init(ds), [Laws.seg.name(last)]), dk.split(ds, last)),
      ka.nest(Laws.dk.init(ds), Laws.seg.name(last), "", D1.one(), {==})))

# WP-K3: header segments spelled any way, with blank space. Blank space after
# the bracket leaves the header waiting for a segment in LHeadDot, as after a
# dot; a bare segment is read by WP-H's wh.b1 and wh.bbody and ended by a
# blank (to LHeadGap), a dot or the bracket; a basic one by WP0's qs and a
# literal one by ql at hd = True, each closing into LHeadGap, where blank
# space stays until a dot or the bracket. The states are WP-H's wh.st.

# whether there is any blank space
def hg.nz(gs: List<&2, Bool>) -> Bool:
  match gs:
    case []:
      False{}
    case _t <> _r:
      True{}

# blank space after a dot stays in LHeadDot
def hg.dgap(
  gs: List<&2, Bool>,
  +rr: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool
) -> {T.doc.read(String.append(D2.gap(gs), rr), T.MScan{M6.wh.st(rows, heads, here, parts, [], T.LHeadDot{},
  back, qkind, arrtab)}) == T.doc.read(rr, T.MScan{M6.wh.st(rows, heads, here, parts, [], T.LHeadDot{}, back,
  qkind, arrtab)}) : T.Doc}:
  match gs:
    case []:
      {==}
    case tab <> rest:
      match tab:
        case True{}:
          hg.dgap(rest, rr, rows, heads, here, parts, back, qkind, arrtab)
        case False{}:
          hg.dgap(rest, rr, rows, heads, here, parts, back, qkind, arrtab)

# and after a segment in LHeadGap
def hg.hgap(
  gs: List<&2, Bool>,
  +rr: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool
) -> {T.doc.read(String.append(D2.gap(gs), rr), T.MScan{M6.wh.st(rows, heads, here, parts, [], T.LHeadGap{},
  back, qkind, arrtab)}) == T.doc.read(rr, T.MScan{M6.wh.st(rows, heads, here, parts, [], T.LHeadGap{}, back,
  qkind, arrtab)}) : T.Doc}:
  match gs:
    case []:
      {==}
    case tab <> rest:
      match tab:
        case True{}:
          hg.hgap(rest, rr, rows, heads, here, parts, back, qkind, arrtab)
        case False{}:
          hg.hgap(rest, rr, rows, heads, here, parts, back, qkind, arrtab)

# blank space right after the bracket waits for the first segment in LHeadDot
def hg.lead(
  g0: List<&2, Bool>,
  +xx: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool
) -> {T.doc.read(String.append(D2.gap(g0), xx), T.MScan{M6.wh.st(rows, heads, here, [], [], T.LHead{}, back, qkind,
  arrtab)}) == T.doc.read(xx, T.MScan{M6.wh.st(rows, heads, here, M12.wh.ps(hg.nz(g0), []), [], M12.wh.lex0(hg.nz(g0)), back,  # noqa: S002
  qkind, arrtab)}) : T.Doc}:
  match g0:
    case []:
      {==}
    case tab <> rest:
      match tab:
        case True{}:
          hg.dgap(rest, xx, rows, heads, here, [], back, qkind, arrtab)
        case False{}:
          hg.dgap(rest, xx, rows, heads, here, [], back, qkind, arrtab)

# a dot or the bracket after a segment's blank space
def hg.gdl(
  cl: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +rest: String
) -> {T.doc.read(SCon{M12.wh.dl(cl), rest}, T.MScan{M6.wh.st(rows, heads, here, parts, [], T.LHeadGap{}, back, qkind,
  arrtab)}) == T.doc.read(rest, T.MScan{M5.wh.aft(cl, rows, heads, here, parts, back, qkind, arrtab)}) : T.Doc}:
  match cl:
    case False{}:
      {==}
    case True{}:
      {==}

# blank space, then a dot or the bracket, after a segment pushed onto parts
def hg.gtail(
  gs: List<&2, Bool>,
  +cl: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +rest: String
) -> {T.doc.read(String.append(D2.gap(gs), SCon{M12.wh.dl(cl), rest}), T.MScan{M6.wh.st(rows, heads, here, parts, [],
  T.LHeadGap{}, back, qkind, arrtab)}) == T.doc.read(rest, T.MScan{M5.wh.aft(cl, rows, heads, here, parts, back,
  qkind, arrtab)}) : T.Doc}:
  Equal.trans(T.Doc,
    T.doc.read(String.append(D2.gap(gs), SCon{M12.wh.dl(cl), rest}), T.MScan{M6.wh.st(rows, heads, here, parts, [],
      T.LHeadGap{}, back, qkind, arrtab)}),
    T.doc.read(SCon{M12.wh.dl(cl), rest}, T.MScan{M6.wh.st(rows, heads, here, parts, [], T.LHeadGap{}, back, qkind,
      arrtab)}),
    T.doc.read(rest, T.MScan{M5.wh.aft(cl, rows, heads, here, parts, back, qkind, arrtab)}),
    hg.hgap(gs, SCon{M12.wh.dl(cl), rest}, rows, heads, here, parts, back, qkind, arrtab),
    hg.gdl(cl, rows, heads, here, parts, back, qkind, arrtab, rest))

# a blank ends an open bare segment: it is pushed, and the header waits in
# LHeadGap
def hg.bsp(
  tab: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +bf: List<&2, Char>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +rr: String,
  full: {List.is_empty(&2, Char, bf) == False{} : Bool}
) -> {T.doc.read(SCon{D2.blank_char(tab), rr}, T.MScan{M6.wh.st(rows, heads, here, parts, bf, T.LHead{}, back,
  qkind, arrtab)}) == T.doc.read(rr, T.MScan{M6.wh.st(rows, heads, here, T.buf.str(bf) <> parts, [], T.LHeadGap{},
  back, qkind, arrtab)}) : T.Doc}:
  match tab:
    case True{}:
      Equal.cong(Bool, T.Doc, bt => T.doc.read(rr, T.MScan{T.read.once2(T.lex.head.gap.go(bt, M6.wh.st(rows, heads,
        here, parts, bf, T.LHead{}, back, qkind, arrtab)))}), List.is_empty(&2, Char, bf), False{}, full)
    case False{}:
      Equal.cong(Bool, T.Doc, bt => T.doc.read(rr, T.MScan{T.read.once2(T.lex.head.gap.go(bt, M6.wh.st(rows, heads,
        here, parts, bf, T.LHead{}, back, qkind, arrtab)))}), List.is_empty(&2, Char, bf), False{}, full)

# blank space and a dot or the bracket after an open bare segment push it
def hg.bend(
  gs: List<&2, Bool>,
  +cl: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +bf: List<&2, Char>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +rest: String,
  full: {List.is_empty(&2, Char, bf) == False{} : Bool}
) -> {T.doc.read(String.append(D2.gap(gs), SCon{M12.wh.dl(cl), rest}), T.MScan{M6.wh.st(rows, heads, here, parts, bf,
  T.LHead{}, back, qkind, arrtab)}) == T.doc.read(rest, T.MScan{M5.wh.aft(cl, rows, heads, here,
  T.buf.str(bf) <> parts, back, qkind, arrtab)}) : T.Doc}:
  match gs:
    case []:
      wh.bdl(cl, rows, heads, here, parts, bf, back, qkind, arrtab, rest, full)
    case tab <> +gr:
      Equal.trans(T.Doc,
        T.doc.read(SCon{D2.blank_char(tab), String.append(D2.gap(gr), SCon{M12.wh.dl(cl), rest})},
          T.MScan{M6.wh.st(rows, heads, here, parts, bf, T.LHead{}, back, qkind, arrtab)}),
        T.doc.read(String.append(D2.gap(gr), SCon{M12.wh.dl(cl), rest}), T.MScan{M6.wh.st(rows, heads, here,
          T.buf.str(bf) <> parts, [], T.LHeadGap{}, back, qkind, arrtab)}),
        T.doc.read(rest, T.MScan{M5.wh.aft(cl, rows, heads, here, T.buf.str(bf) <> parts, back, qkind, arrtab)}),
        hg.bsp(tab, rows, heads, here, parts, bf, back, qkind, arrtab, String.append(D2.gap(gr),
          SCon{M12.wh.dl(cl), rest}), full),
        hg.gtail(gr, cl, rows, heads, here, T.buf.str(bf) <> parts, back, qkind, arrtab, rest))

# the segment's buffer reads as its name, and the rest is read
def hg.nm(
  +nm: String,
  +bf: List<&2, Char>,
  en: {T.buf.str(bf) == nm : String},
  +cl: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +arrtab: Bool,
  +rest: String,
  +goal: T.Doc,
  ih: wh.Then(cl, rows, heads, here, nm <> parts, arrtab, rest, goal)
) -> {T.doc.read(rest, T.MScan{M5.wh.aft(cl, rows, heads, here, T.buf.str(bf) <> parts, bk, qk, arrtab)}) == goal
  : T.Doc}:
  Equal.trans(T.Doc,
    T.doc.read(rest, T.MScan{M5.wh.aft(cl, rows, heads, here, T.buf.str(bf) <> parts, bk, qk, arrtab)}),
    T.doc.read(rest, T.MScan{M5.wh.aft(cl, rows, heads, here, nm <> parts, bk, qk, arrtab)}),
    goal,
    Equal.cong(String, T.Doc, xx => T.doc.read(rest, T.MScan{M5.wh.aft(cl, rows, heads, here, xx <> parts, bk, qk,
      arrtab)}), T.buf.str(bf), nm, en),
    ih(bk, qk))

# after a quoted segment's closing quote: blank space, a dot or the bracket,
# and the rest
def hg.fin(
  +nm: String,
  +bf: List<&2, Char>,
  en: {T.buf.str(bf) == nm : String},
  +gs: List<&2, Bool>,
  +cl: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +arrtab: Bool,
  +rest: String,
  +goal: T.Doc,
  ih: wh.Then(cl, rows, heads, here, nm <> parts, arrtab, rest, goal)
) -> {T.doc.read(String.append(D2.gap(gs), SCon{M12.wh.dl(cl), rest}), T.MScan{M6.wh.st(rows, heads, here,
  T.buf.str(bf) <> parts, [], T.LHeadGap{}, bk, qk, arrtab)}) == goal : T.Doc}:
  Equal.trans(T.Doc,
    T.doc.read(String.append(D2.gap(gs), SCon{M12.wh.dl(cl), rest}), T.MScan{M6.wh.st(rows, heads, here,
      T.buf.str(bf) <> parts, [], T.LHeadGap{}, bk, qk, arrtab)}),
    T.doc.read(rest, T.MScan{M5.wh.aft(cl, rows, heads, here, T.buf.str(bf) <> parts, bk, qk, arrtab)}),
    goal,
    hg.gtail(gs, cl, rows, heads, here, T.buf.str(bf) <> parts, bk, qk, arrtab, rest),
    hg.nm(nm, bf, en, cl, rows, heads, here, parts, bk, qk, arrtab, rest, goal, ih))

# a bare header segment, its blank space and a dot or the bracket
def hg.bseg(
  +xx: U32,
  +tt: String,
  +gs: List<&2, Bool>,
  +cl: Bool,
  +dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +rest: String,
  +goal: T.Doc,
  +ee: {T.bare.all.step(T.bare.at(Chr{xx}), _u => T.bare.all(String.to_list(tt))) == True{} : Bool},
  ih: wh.Then(cl, rows, heads, here, SCon{Chr{xx}, tt} <> M12.wh.ps(dt, parts), arrtab, rest, goal)
) -> {T.doc.read(String.append(SCon{Chr{xx}, tt}, String.append(D2.gap(gs), SCon{M12.wh.dl(cl), rest})),
  T.MScan{M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind, arrtab)}) == goal : T.Doc}:  # noqa: S002
  Equal.trans(T.Doc,
    T.doc.read(String.append(tt, String.append(D2.gap(gs), SCon{M12.wh.dl(cl), rest})), T.doc.scan(M6.wh.st(rows,
      heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind, arrtab), Chr{xx})),
    T.doc.read(String.append(tt, String.append(D2.gap(gs), SCon{M12.wh.dl(cl), rest})), T.MScan{M6.wh.st(rows,
      heads, here, M12.wh.ps(dt, parts), [Chr{xx}], T.LHead{}, back, qkind, arrtab)}),
    goal,
    Equal.cong(T.Mode, T.Doc, md => T.doc.read(String.append(tt, String.append(D2.gap(gs), SCon{M12.wh.dl(cl),
      rest})), md),
      T.doc.scan(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind, arrtab), Chr{xx}),
      T.MScan{M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [Chr{xx}], T.LHead{}, back, qkind, arrtab)},
      wh.b1(dt, rows, heads, here, parts, back, qkind, arrtab, xx,
        M16.ball.head(T.bare.at(Chr{xx}), String.to_list(tt), ee))),
    Equal.trans(T.Doc,
      T.doc.read(String.append(tt, String.append(D2.gap(gs), SCon{M12.wh.dl(cl), rest})), T.MScan{M6.wh.st(rows,
        heads, here, M12.wh.ps(dt, parts), [Chr{xx}], T.LHead{}, back, qkind, arrtab)}),
      T.doc.read(String.append(D2.gap(gs), SCon{M12.wh.dl(cl), rest}), T.MScan{M6.wh.st(rows, heads, here,
        M12.wh.ps(dt, parts), M3.rev.onto(tt, [Chr{xx}]), T.LHead{}, back, qkind, arrtab)}),
      goal,
      wh.bbody(tt, String.append(D2.gap(gs), SCon{M12.wh.dl(cl), rest}), rows, heads, here, M12.wh.ps(dt, parts),
        Chr{xx}, [], back, qkind, arrtab, M16.ball.tail(T.bare.at(Chr{xx}), String.to_list(tt), ee)),
      Equal.trans(T.Doc,
        T.doc.read(String.append(D2.gap(gs), SCon{M12.wh.dl(cl), rest}), T.MScan{M6.wh.st(rows, heads, here,
          M12.wh.ps(dt, parts), M3.rev.onto(tt, [Chr{xx}]), T.LHead{}, back, qkind, arrtab)}),
        T.doc.read(rest, T.MScan{M5.wh.aft(cl, rows, heads, here, T.buf.str(M3.rev.onto(tt, [Chr{xx}])) <>
          M12.wh.ps(dt, parts), back, qkind, arrtab)}),
        goal,
        hg.bend(gs, cl, rows, heads, here, M12.wh.ps(dt, parts), M3.rev.onto(tt, [Chr{xx}]), back, qkind, arrtab, rest,
          M16.rev.full(tt, Chr{xx}, [])),
        hg.nm(SCon{Chr{xx}, tt}, M3.rev.onto(tt, [Chr{xx}]), M16.wh.bname(xx, tt), cl, rows, heads, here,
          M12.wh.ps(dt, parts), back, qkind, arrtab, rest, goal, ih))))

# an apostrophe where a header segment starts opens a literal segment
def hs.lopen(
  dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool
) -> {T.doc.scan(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind, arrtab), '\'')
  == T.MScan{M6.ql(True{}, rows, heads, here, M12.wh.ps(dt, parts), arrtab, back, [])} : T.Mode}:
  match dt:
    case False{}:
      {==}
    case True{}:
      {==}

# a basic header segment, its blank space and a dot or the bracket
def hg.qseg(
  +ss: String,
  +gs: List<&2, Bool>,
  +cl: Bool,
  +dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +rest: String,
  +goal: T.Doc,
  ih: wh.Then(cl, rows, heads, here, ss <> M12.wh.ps(dt, parts), arrtab, rest, goal)
) -> {T.doc.read(String.append(T.key.basic(ss), String.append(D2.gap(gs), SCon{M12.wh.dl(cl), rest})),
  T.MScan{M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind, arrtab)}) == goal : T.Doc}:  # noqa: S002
  Equal.trans(T.Doc,
    T.doc.read(String.append(T.key.basic(ss), String.append(D2.gap(gs), SCon{M12.wh.dl(cl), rest})),
      T.MScan{M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind, arrtab)}),
    T.doc.read(String.append(String.append(L7.escs(ss), "\""), String.append(D2.gap(gs),
      SCon{M12.wh.dl(cl), rest})), T.doc.scan(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt),
          back,
      qkind, arrtab), '"')),
    goal,
    Equal.cong(String, T.Doc, zz => T.doc.read(String.append(zz, String.append(D2.gap(gs),
      SCon{M12.wh.dl(cl), rest})), T.MScan{M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back,
      qkind, arrtab)}),
      T.key.basic(ss), "\"" ++ L7.escs(ss) ++ "\"", L7.basic_escs(ss)),
    Equal.trans(T.Doc,
      T.doc.read(String.append(String.append(L7.escs(ss), "\""), String.append(D2.gap(gs),
        SCon{M12.wh.dl(cl), rest})), T.doc.scan(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt),
            back,
        qkind, arrtab), '"')),
      T.doc.read(String.append(L7.escs(ss), SCon{'"', String.append(D2.gap(gs), SCon{M12.wh.dl(cl), rest})}),
        T.MScan{M9.qs(True{}, rows, heads, here, M12.wh.ps(dt, parts), [], arrtab, back, [])}),
      goal,
      Equal.trans(T.Doc,
        T.doc.read(String.append(String.append(L7.escs(ss), "\""), String.append(D2.gap(gs),
          SCon{M12.wh.dl(cl), rest})), T.doc.scan(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt),
          back, qkind, arrtab), '"')),
        T.doc.read(String.append(L7.escs(ss), SCon{'"', String.append(D2.gap(gs), SCon{M12.wh.dl(cl),
          rest})}), T.doc.scan(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind,
          arrtab), '"')),
        T.doc.read(String.append(L7.escs(ss), SCon{'"', String.append(D2.gap(gs), SCon{M12.wh.dl(cl),
          rest})}), T.MScan{M9.qs(True{}, rows, heads, here, M12.wh.ps(dt, parts), [], arrtab, back, [])}),
        Equal.cong(String, T.Doc, zz => T.doc.read(zz, T.doc.scan(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts),
          [], M12.wh.lex0(dt), back, qkind, arrtab), '"')),
          String.append(String.append(L7.escs(ss), "\""), String.append(D2.gap(gs), SCon{M12.wh.dl(cl),
            rest})),
          String.append(L7.escs(ss), SCon{'"', String.append(D2.gap(gs), SCon{M12.wh.dl(cl), rest})}),
          Eq.append_assoc(L7.escs(ss), "\"", String.append(D2.gap(gs), SCon{M12.wh.dl(cl), rest}))),
        Equal.cong(T.Mode, T.Doc, md => T.doc.read(String.append(L7.escs(ss), SCon{'"',
          String.append(D2.gap(gs), SCon{M12.wh.dl(cl), rest})}), md),
          T.doc.scan(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind, arrtab), '"'),
          T.MScan{M9.qs(True{}, rows, heads, here, M12.wh.ps(dt, parts), [], arrtab, back, [])},
          wh.qopen(dt, rows, heads, here, parts, back, qkind, arrtab))),
      M10.qs.escs(ss, True{}, rows, heads, here, M12.wh.ps(dt, parts), [], arrtab, back, [],
        SCon{'"', String.append(D2.gap(gs), SCon{M12.wh.dl(cl), rest})}, goal,
        +bk => Equal.trans(T.Doc,
          T.doc.read(SCon{'"', String.append(D2.gap(gs), SCon{M12.wh.dl(cl), rest})}, T.MScan{M9.qs(True{}, rows,
            heads, here, M12.wh.ps(dt, parts), [], arrtab, bk, M3.rev.onto(ss, []))}),
          T.doc.read(String.append(D2.gap(gs), SCon{M12.wh.dl(cl), rest}), T.MScan{M6.wh.st(rows, heads, here,
            T.buf.str(M3.rev.onto(ss, [])) <> M12.wh.ps(dt, parts), [], T.LHeadGap{}, bk, T.QBasic{}, arrtab)}),
          goal,
          {==},
          hg.fin(ss, M3.rev.onto(ss, []), M12.wh.qname(ss), gs, cl, rows, heads, here, M12.wh.ps(dt, parts), bk,
            T.QBasic{}, arrtab, rest, goal, ih)))))

# a literal header segment, its blank space and a dot or the bracket
def hg.lseg(
  +ss: String,
  +gs: List<&2, Bool>,
  +cl: Bool,
  +dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +rest: String,
  +goal: T.Doc,
  el: {Laws.lit.text(ss) == True{} : Bool},
  ih: wh.Then(cl, rows, heads, here, ss <> M12.wh.ps(dt, parts), arrtab, rest, goal)
) -> {T.doc.read(String.append(SCon{'\'', String.append(ss, "'")}, String.append(D2.gap(gs),
  SCon{M12.wh.dl(cl), rest})), T.MScan{M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind,  # noqa: S002
  arrtab)}) == goal : T.Doc}:
  Equal.trans(T.Doc,
    T.doc.read(String.append(String.append(ss, "'"), String.append(D2.gap(gs), SCon{M12.wh.dl(cl), rest})),
      T.doc.scan(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind, arrtab), '\'')),
    T.doc.read(String.append(ss, SCon{'\'', String.append(D2.gap(gs), SCon{M12.wh.dl(cl), rest})}),
      T.MScan{M6.ql(True{}, rows, heads, here, M12.wh.ps(dt, parts), arrtab, back, [])}),
    goal,
    Equal.trans(T.Doc,
      T.doc.read(String.append(String.append(ss, "'"), String.append(D2.gap(gs), SCon{M12.wh.dl(cl), rest})),
        T.doc.scan(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind, arrtab), '\'')),
      T.doc.read(String.append(ss, SCon{'\'', String.append(D2.gap(gs), SCon{M12.wh.dl(cl), rest})}),
        T.doc.scan(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind, arrtab), '\'')),
      T.doc.read(String.append(ss, SCon{'\'', String.append(D2.gap(gs), SCon{M12.wh.dl(cl), rest})}),
        T.MScan{M6.ql(True{}, rows, heads, here, M12.wh.ps(dt, parts), arrtab, back, [])}),
      Equal.cong(String, T.Doc, zz => T.doc.read(zz, T.doc.scan(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [],
        M12.wh.lex0(dt), back, qkind, arrtab), '\'')),
        String.append(String.append(ss, "'"), String.append(D2.gap(gs), SCon{M12.wh.dl(cl), rest})),
        String.append(ss, SCon{'\'', String.append(D2.gap(gs), SCon{M12.wh.dl(cl), rest})}),
        Eq.append_assoc(ss, "'", String.append(D2.gap(gs), SCon{M12.wh.dl(cl), rest}))),
      Equal.cong(T.Mode, T.Doc, md => T.doc.read(String.append(ss, SCon{'\'', String.append(D2.gap(gs),
        SCon{M12.wh.dl(cl), rest})}), md),
        T.doc.scan(M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind, arrtab), '\''),
        T.MScan{M6.ql(True{}, rows, heads, here, M12.wh.ps(dt, parts), arrtab, back, [])},
        hs.lopen(dt, rows, heads, here, parts, back, qkind, arrtab))),
    Equal.trans(T.Doc,
      T.doc.read(String.append(ss, SCon{'\'', String.append(D2.gap(gs), SCon{M12.wh.dl(cl), rest})}),
        T.MScan{M6.ql(True{}, rows, heads, here, M12.wh.ps(dt, parts), arrtab, back, [])}),
      T.doc.read(SCon{'\'', String.append(D2.gap(gs), SCon{M12.wh.dl(cl), rest})},
        T.MScan{M6.ql(True{}, rows, heads, here, M12.wh.ps(dt, parts), arrtab, back, M3.rev.onto(ss, []))}),
      goal,
      ql.body(ss, SCon{'\'', String.append(D2.gap(gs), SCon{M12.wh.dl(cl), rest})}, True{}, rows, heads, here,
        M12.wh.ps(dt, parts), arrtab, back, [], el),
      Equal.trans(T.Doc,
        T.doc.read(SCon{'\'', String.append(D2.gap(gs), SCon{M12.wh.dl(cl), rest})},
          T.MScan{M6.ql(True{}, rows, heads, here, M12.wh.ps(dt, parts), arrtab, back, M3.rev.onto(ss, []))}),
        T.doc.read(String.append(D2.gap(gs), SCon{M12.wh.dl(cl), rest}), T.MScan{M6.wh.st(rows, heads, here,
          T.buf.str(M3.rev.onto(ss, [])) <> M12.wh.ps(dt, parts), [], T.LHeadGap{}, back, T.QLit{}, arrtab)}),
        goal,
        {==},
        hg.fin(ss, M3.rev.onto(ss, []), M12.wh.qname(ss), gs, cl, rows, heads, here, M12.wh.ps(dt, parts), back,
          T.QLit{}, arrtab, rest, goal, ih))))

# a header segment spelled any way it can be, its blank space and a dot or
# the bracket
def hg.seg(
  sg: D3.Seg,
  +gs: List<&2, Bool>,
  +cl: Bool,
  +dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +rest: String,
  +goal: T.Doc,
  eo: {Laws.seg.ok(sg) == True{} : Bool},
  ih: wh.Then(cl, rows, heads, here, Laws.seg.name(sg) <> M12.wh.ps(dt, parts), arrtab, rest, goal)
) -> {T.doc.read(String.append(Laws.seg.text(sg), String.append(D2.gap(gs), SCon{M12.wh.dl(cl), rest})),
  T.MScan{M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind, arrtab)}) == goal : T.Doc}:  # noqa: S002
  match sg:
    case D3.Seg{sp, +name}:
      match sp:
        case D3.SpBare{}:
          match name:
            case SNil{}:
              Eq.bit.absurd(&2, {T.doc.read(String.append(SNil{}, String.append(D2.gap(gs), SCon{M12.wh.dl(cl),
                rest})), T.MScan{M6.wh.st(rows, heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind,
                arrtab)}) == goal : T.Doc}, eo)
            case SCon{hh, +tt}:
              match hh:
                case Chr{+xx}:
                  hg.bseg(xx, tt, gs, cl, dt, rows, heads, here, parts, back, qkind, arrtab, rest, goal, eo, ih)
        case D3.SpBasic{}:
          hg.qseg(name, gs, cl, dt, rows, heads, here, parts, back, qkind, arrtab, rest, goal, ih)
        case D3.SpLit{}:
          hg.lseg(name, gs, cl, dt, rows, heads, here, parts, back, qkind, arrtab, rest, goal, eo, ih)

# a header's segments, then blank space and the bracket: the rest is read
# with every segment pushed onto parts, newest first
def hg.keys(
  ds: List<&2, D3.Dot>,
  +last: D3.Seg,
  +g9: List<&2, Bool>,
  +dt: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +arrtab: Bool,
  +rest: String,
  +goal: T.Doc,
  +eo: {Laws.dk.ok(ds, last) == True{} : Bool},
  ih: wh.Then(True{}, rows, heads, here, kl.acc(ds, last, dt, parts), arrtab, rest, goal)
) -> {T.doc.read(Laws.dk.text(ds, last, String.append(D2.gap(g9), SCon{']', rest})), T.MScan{M6.wh.st(rows,
  heads, here, M12.wh.ps(dt, parts), [], M12.wh.lex0(dt), back, qkind, arrtab)}) == goal : T.Doc}:
  match ds:
    case []:
      hg.seg(last, g9, True{}, dt, rows, heads, here, parts, back, qkind, arrtab, rest, goal, eo, ih)
    case D3.Dot{+sg, g1, +g2} <> +dr:
      hg.seg(sg, g1, False{}, dt, rows, heads, here, parts, back, qkind, arrtab,
        String.append(D2.gap(g2), Laws.dk.text(dr, last, String.append(D2.gap(g9), SCon{']', rest}))), goal,
        Eq.and.left(Laws.seg.ok(sg), Laws.dk.ok(dr, last), eo),
        +bk => +qk => Equal.trans(T.Doc,
          T.doc.read(String.append(D2.gap(g2), Laws.dk.text(dr, last, String.append(D2.gap(g9), SCon{']',
            rest}))), T.MScan{M6.wh.st(rows, heads, here, Laws.seg.name(sg) <> M12.wh.ps(dt, parts), [],
            T.LHeadDot{}, bk, qk, arrtab)}),
          T.doc.read(Laws.dk.text(dr, last, String.append(D2.gap(g9), SCon{']', rest})), T.MScan{M6.wh.st(rows,
            heads, here, Laws.seg.name(sg) <> M12.wh.ps(dt, parts), [], T.LHeadDot{}, bk, qk, arrtab)}),
          goal,
          hg.dgap(g2, Laws.dk.text(dr, last, String.append(D2.gap(g9), SCon{']', rest})), rows, heads, here,
            Laws.seg.name(sg) <> M12.wh.ps(dt, parts), bk, qk, arrtab),
          hg.keys(dr, last, g9, True{}, rows, heads, here, Laws.seg.name(sg) <> M12.wh.ps(dt, parts), bk, qk, arrtab,
            rest, goal, Eq.and.right(Laws.seg.ok(sg), Laws.dk.ok(dr, last), eo), ih)))

# the names pushed are never none
def hg.ne(
  ds: List<&2, D3.Dot>,
  +last: D3.Seg,
  +acc: List<&2, String>
) -> {List.is_empty(&2, String, List.reverse.go(&2, String, Laws.dk.names(ds, last), acc)) == False{} : Bool}:
  match ds:
    case []:
      {==}
    case D3.Dot{sg, _g1, _g2} <> rest:
      hg.ne(rest, last, Laws.seg.name(sg) <> acc)

# no segment before the first
def hg.ps0(dt: Bool) -> {M12.wh.ps(dt, []) == [] : List<&2, String>}:
  match dt:
    case False{}:
      {==}
    case True{}:
      {==}

# so the names pushed, reversed, are the header's path
def hg.path(
  +dt: Bool,
  +ds: List<&2, D3.Dot>,
  +last: D3.Seg
) -> {List.reverse(&2, String, List.reverse.go(&2, String, Laws.dk.names(ds, last), M12.wh.ps(dt, [])))
  == Laws.hd.path(ds, last) : List<&2, String>}:
  Equal.trans(List<&2, String>,
    List.reverse(&2, String, List.reverse.go(&2, String, Laws.dk.names(ds, last), M12.wh.ps(dt, []))),
    List.reverse(&2, String, List.reverse(&2, String, Laws.dk.names(ds, last))),
    Laws.hd.path(ds, last),
    Equal.cong(List<&2, String>, List<&2, String>, xs => List.reverse(&2, String, List.reverse.go(&2, String,
      Laws.dk.names(ds, last), xs)), M12.wh.ps(dt, []), [], hg.ps0(dt)),
    Equal.trans(List<&2, String>,
      List.reverse(&2, String, List.reverse(&2, String, Laws.dk.names(ds, last))),
      Laws.dk.names(ds, last),
      Laws.hd.path(ds, last),
      M5.kv.rr(Laws.dk.names(ds, last)),
      dk.split(ds, last)))

# after the path and the bracket: the header's walk, and the next line
def hg.end(
  arr: Bool,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +dt: Bool,
  +ds: List<&2, D3.Dot>,
  +last: D3.Seg,
  +bk: T.Lex,
  +qk: T.QKind,
  +rows2: List<&2, T.Val>,
  +heads2: List<&2, String>,
  +rest: String,
  +goal: T.Doc,
  ew: M6.wh.Walk(arr, Laws.hd.path(ds, last), rows, heads, rows2, heads2),
  ih: wh.Line(rows2, heads2, Laws.hd.path(ds, last), rest, goal)
) -> {T.doc.read(M6.wh.tail(arr, rest), T.MScan{M5.wh.aft(True{}, rows, heads, here, kl.acc(ds, last, dt, []), bk, qk,
  arr)}) == goal : T.Doc}:
  Equal.trans(T.Doc,
    T.doc.read(M6.wh.tail(arr, rest), T.MScan{M5.wh.aft(True{}, rows, heads, here, kl.acc(ds, last, dt, []), bk, qk,
      arr)}),
    T.doc.read(rest, T.MScan{Laws.hb.line(rows2, heads2, Laws.hd.path(ds, last), bk, qk, False{})}),
    goal,
    M5.wh.fin(arr, rows, heads, here, kl.acc(ds, last, dt, []), bk, qk, Laws.hd.path(ds, last), rows2, heads2, rest,
      hg.ne(ds, last, M12.wh.ps(dt, [])), hg.path(dt, ds, last), ew),
    ih(bk, qk))

# a whole header line, from the start of a line
def hg.core(
  arr: Bool,
  +g0: List<&2, Bool>,
  +ds: List<&2, D3.Dot>,
  +last: D3.Seg,
  +g9: List<&2, Bool>,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +a0: Bool,
  +rows2: List<&2, T.Val>,
  +heads2: List<&2, String>,
  +rest: String,
  +goal: T.Doc,
  +eo: {Laws.dk.ok(ds, last) == True{} : Bool},
  ew: M6.wh.Walk(arr, Laws.hd.path(ds, last), rows, heads, rows2, heads2),
  ih: wh.Line(rows2, heads2, Laws.hd.path(ds, last), rest, goal)
) -> {T.doc.read(Laws.hd.line(arr, g0, ds, last, g9, rest), T.MScan{Laws.hb.line(rows, heads, here, back, qkind,
  a0)}) == goal : T.Doc}:
  match arr:
    case False{}:
      Equal.trans(T.Doc,
        T.doc.read(String.append(D2.gap(g0), Laws.dk.text(ds, last, String.append(D2.gap(g9), SCon{']',
          M6.wh.tail(False{}, rest)}))), T.MScan{M6.wh.st(rows, heads, here, [], [], T.LHead{}, back, qkind, False{})}),
        T.doc.read(Laws.dk.text(ds, last, String.append(D2.gap(g9), SCon{']', M6.wh.tail(False{}, rest)})),
          T.MScan{M6.wh.st(rows, heads, here, M12.wh.ps(hg.nz(g0), []), [], M12.wh.lex0(hg.nz(g0)), back, qkind,
              False{})}),
        goal,
        hg.lead(g0, Laws.dk.text(ds, last, String.append(D2.gap(g9), SCon{']', M6.wh.tail(False{}, rest)})), rows,
          heads, here, back, qkind, False{}),
        hg.keys(ds, last, g9, hg.nz(g0), rows, heads, here, [], back, qkind, False{}, M6.wh.tail(False{}, rest), goal,
          eo, +bk => +qk => hg.end(False{}, rows, heads, here, hg.nz(g0), ds, last, bk, qk, rows2, heads2, rest,
            goal, ew, ih)))
    case True{}:
      Equal.trans(T.Doc,
        T.doc.read(String.append(D2.gap(g0), Laws.dk.text(ds, last, String.append(D2.gap(g9), SCon{']',
          M6.wh.tail(True{}, rest)}))), T.MScan{M6.wh.st(rows, heads, here, [], [], T.LHead{}, back, qkind, True{})}),
        T.doc.read(Laws.dk.text(ds, last, String.append(D2.gap(g9), SCon{']', M6.wh.tail(True{}, rest)})),
          T.MScan{M6.wh.st(rows, heads, here, M12.wh.ps(hg.nz(g0), []), [], M12.wh.lex0(hg.nz(g0)), back, qkind,
              True{})}),
        goal,
        hg.lead(g0, Laws.dk.text(ds, last, String.append(D2.gap(g9), SCon{']', M6.wh.tail(True{}, rest)})), rows,
          heads, here, back, qkind, True{}),
        hg.keys(ds, last, g9, hg.nz(g0), rows, heads, here, [], back, qkind, True{}, M6.wh.tail(True{}, rest), goal,
          eo, +bk => +qk => hg.end(True{}, rows, heads, here, hg.nz(g0), ds, last, bk, qk, rows2, heads2, rest,
            goal, ew, ih)))

def Laws.header_segments_read_back(
  arr,
  g0,
  ds,
  last,
  ok,
  g9,
  rows,
  heads,
  here,
  back,
  qkind,
  arrtab,
  rows2,
  heads2,
  ew,
  rest,
  goal,
  ih
):
  hg.core(arr, g0, ds, last, g9, rows, heads, here, back, qkind, arrtab, rows2, heads2, rest, goal, ok, ew, ih)

# from the empty root a walk goes on through every segment
def tb.open.nil(path: List<&2, String>) -> {D1.tb.open(path, []) == True{} : Bool}:
  match path:
    case []:
      {==}
    case _seg <> rest:
      tb.open.nil(rest)

# the table a one-line header defines
def hg.new(ds: List<&2, D3.Dot>, last: D3.Seg) -> T.Val:
  T.VHead{T.tree.pre(D1.tb.join(Laws.dk.init(ds), ""), Laws.seg.name(last)), []}

def Laws.header_line_reads_back(g0, ds, last, ok, g9):
  Laws.header_segments_read_back(False{}, g0, ds, last, ok, g9, [], [], [], T.LTop{}, T.QBasic{}, False{},
    D1.tb.set(Laws.dk.init(ds), "", [], T.VPair{Laws.seg.name(last), hg.new(ds, last)}
      <> D1.tb.rows(Laws.dk.init(ds), [])),
    T.heads.by.head(T.tree.pre(D1.tb.join(Laws.dk.init(ds), ""), Laws.seg.name(last))) <> [],
    L6.header_defines_new_table(Laws.dk.init(ds), Laws.seg.name(last), [], [], tb.open.nil(Laws.dk.init(ds)),
      Equal.cong(List<&2, T.Val>, T.Hit, xs => T.get(xs, Laws.seg.name(last)), D1.tb.rows(Laws.dk.init(ds), []),
        [], tb.rows.nil(Laws.dk.init(ds)))),
    "",
    T.Doc{"", T.rows.seal(D1.tb.set(Laws.dk.init(ds), "", [], [T.VPair{Laws.seg.name(last), hg.new(ds, last)}]))},
    +_bk => +_qk => Equal.cong(List<&2, T.Val>, T.Doc,
      xs => T.Doc{"", T.rows.seal(D1.tb.set(Laws.dk.init(ds), "", [], T.VPair{Laws.seg.name(last),
        hg.new(ds, last)} <> xs))}, D1.tb.rows(Laws.dk.init(ds), []), [], tb.rows.nil(Laws.dk.init(ds))))

def Laws.header_line_found_by_at(g0, ds, last, ok, g9):
  Equal.trans(T.Hit,
    T.at(T.root(T.parse(Laws.hd.line(False{}, g0, ds, last, g9, ""))), Laws.hd.path(ds, last)),
    T.at(T.rows.seal(D1.tb.set(Laws.dk.init(ds), "", [], [T.VPair{Laws.seg.name(last), hg.new(ds, last)}])),
      Laws.hd.path(ds, last)),
    T.Found{hg.new(ds, last)},
    Equal.cong(T.Doc, T.Hit, dd => T.at(T.root(dd), Laws.hd.path(ds, last)),
      T.parse(Laws.hd.line(False{}, g0, ds, last, g9, "")),
      T.Doc{"", T.rows.seal(D1.tb.set(Laws.dk.init(ds), "", [], [T.VPair{Laws.seg.name(last), hg.new(ds,
        last)}]))},
      Laws.header_line_reads_back(g0, ds, last, ok, g9)),
    ka.nest(Laws.dk.init(ds), Laws.seg.name(last), "", hg.new(ds, last), {==}))

def Laws.basic_key_reads_back(pl, ok):
  M5.k3.pcs(pl, False{}, [], [], [], [], [], False{}, T.LTop{}, 0, 0, [], "\" = 1", T.Doc{"", [T.VPair{
    D3.k3.pcs.name(pl), D1.one()}]}, ok, _b2 => _u2 => _l2 =>
    %M16.k3.nm(D3.k3.pcs.name(pl)) : {T.Doc{"", [T.VPair{_, D1.one()}]} == T.Doc{"", [T.VPair{D3.k3.pcs.name(pl),
      D1.one()}]} : T.Doc}
    {==})

# the rest of the text read after a segment and what ends it, from every
# back, qkind, uni and left
def k3.KT(
  +cl: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  +goal: T.Doc
) -> Type:
  @b2: T.Lex -> @q2: T.QKind -> @u2: U32 -> @l2: U32 ->
    {T.doc.read(rest, T.MScan{M5.k3.w(rw, hs, he, ps, [], M7.k3.aft(cl), b2, q2, sk, u2, l2, ab)}) == goal : T.Doc}

# and blank space where a key may start leaves the scanner there
def k3.g0(
  gs: List<&2, Bool>,
  +at: Laws.KPos,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +rr: String
) -> {T.doc.read(rr, T.MScan{Laws.k3.at(at, rw, hs, he, sk, ab, bk, qk, un, lf)})
  == T.doc.read(String.append(D2.gap(gs), rr), T.MScan{Laws.k3.at(at, rw, hs, he, sk, ab, bk, qk, un, lf)})
  : T.Doc}:
  match gs:
    case []:
      {==}
    case tab <> rest:
      match tab:
        case True{}:
          match at:
            case Laws.AtLine{}:
              k3.g0(rest, Laws.AtLine{}, rw, hs, he, sk, ab, bk, qk, un, lf, rr)
            case Laws.AtInl{}:
              k3.g0(rest, Laws.AtInl{}, rw, hs, he, sk, ab, bk, qk, un, lf, rr)
            case Laws.AtInlK{}:
              k3.g0(rest, Laws.AtInlK{}, rw, hs, he, sk, ab, bk, qk, un, lf, rr)
        case False{}:
          match at:
            case Laws.AtLine{}:
              k3.g0(rest, Laws.AtLine{}, rw, hs, he, sk, ab, bk, qk, un, lf, rr)
            case Laws.AtInl{}:
              k3.g0(rest, Laws.AtInl{}, rw, hs, he, sk, ab, bk, qk, un, lf, rr)
            case Laws.AtInlK{}:
              k3.g0(rest, Laws.AtInlK{}, rw, hs, he, sk, ab, bk, qk, un, lf, rr)

# a segment's name pushed onto parts, then blank space and a dot or `=`: the
# rest is read from there
def k3.fin(
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
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  +goal: T.Doc,
  ih: k3.KT(cl, rw, hs, he, nm <> ps, sk, ab, rest, goal)
) -> {T.doc.read(String.append(D2.gap(gs), SCon{M7.k3.dl(cl), rest}), T.MScan{M5.k3.w(rw, hs, he, T.buf.str(bf) <> ps,
  [], T.LAfter{}, bk, qk, sk, un, lf, ab)}) == goal : T.Doc}:
  %M7.k3.agap(gs, SCon{M7.k3.dl(cl), rest}, rw, hs, he, T.buf.str(bf) <> ps, bk, qk, sk, un, lf,
      ab) : {_ == goal : T.Doc}
  %M7.k3.adl(cl, rw, hs, he, T.buf.str(bf) <> ps, bk, qk, sk, un, lf, ab, rest) : {_ == goal : T.Doc}
  %en : {T.doc.read(rest, T.MScan{M5.k3.w(rw, hs, he, _ <> ps, [], M7.k3.aft(cl), bk, qk, sk, un, lf, ab)}) == goal
    : T.Doc}
  ih(bk, qk, un, lf)

# a bare segment, its blank space and a dot or `=`: the rest is read with the
# segment pushed, and back, qkind, uni and left as they were
def k3.bseg(
  +xx: U32,
  +tt: String,
  +gs: List<&2, Bool>,
  +cl: Bool,
  +dt: Bool,
  +at: Laws.KPos,
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
  +rest: String,
  +goal: T.Doc,
  +ee: {T.bare.all.step(T.bare.at(Chr{xx}), _u => T.bare.all(String.to_list(tt))) == True{} : Bool},
  ih: k3.KT(cl, rw, hs, he, SCon{Chr{xx}, tt} <> M5.k3.ps0(dt, ps), sk, ab, rest, goal)
) -> {T.doc.read(String.append(SCon{Chr{xx}, tt}, String.append(D2.gap(gs), SCon{M7.k3.dl(cl), rest})),
  T.MScan{M5.k3.w(rw, hs, he, M5.k3.ps0(dt, ps), [], M7.k3.lex0(dt, at), bk, qk, sk, un, lf, ab)}) == goal : T.Doc}:
  %M7.k3.b1(dt, at, rw, hs, he, ps, bk, qk, sk, un, lf, ab, xx, M16.ball.head(T.bare.at(Chr{xx}), String.to_list(tt),
      ee))
    : {T.doc.read(String.append(tt, String.append(D2.gap(gs), SCon{M7.k3.dl(cl), rest})), _) == goal : T.Doc}
  %M7.k3.bbody(tt, String.append(D2.gap(gs), SCon{M7.k3.dl(cl), rest}), rw, hs, he, M5.k3.ps0(dt, ps), [Chr{xx}], bk,
      qk, sk,
    un, lf, ab, M16.ball.tail(T.bare.at(Chr{xx}),
    String.to_list(tt), ee)) : {_ == goal : T.Doc}
  %M7.k3.bend(gs, cl, rw, hs, he, M5.k3.ps0(dt, ps), M3.rev.onto(tt, [Chr{xx}]), bk, qk, sk, un, lf, ab, rest,
      M16.rev.full(tt,
    Chr{xx},
    [])) : {_ == goal : T.Doc}
  %Equal.sym(String, T.buf.str(M3.rev.onto(tt, [Chr{xx}])), SCon{Chr{xx}, tt}, M16.wh.bname(xx, tt)) : {T.doc.read(rest,
    T.MScan{M5.k3.w(rw, hs, he, _ <> M5.k3.ps0(dt, ps), [], M7.k3.aft(cl), bk, qk, sk, un, lf, ab)}) == goal : T.Doc}
  ih(bk, qk, un, lf)

# a basic segment of pieces, its blank space and a dot or `=`: the rest is
# read with the segment pushed under the characters the pieces stand for,
# from wherever the last piece left back, uni and left
def k3.qseg(
  +pl: List<&2, D3.KPiece>,
  +gs: List<&2, Bool>,
  +cl: Bool,
  +dt: Bool,
  +at: Laws.KPos,
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
  +rest: String,
  +goal: T.Doc,
  eo: {Laws.k3.pcs.ok(pl) == True{} : Bool},
  ih: k3.KT(cl, rw, hs, he, D3.k3.pcs.name(pl) <> M5.k3.ps0(dt, ps), sk, ab, rest, goal)
) -> {T.doc.read(SCon{'"', D3.k3.pcs.text(pl, SCon{'"', String.append(D2.gap(gs), SCon{M7.k3.dl(cl), rest})})},
  T.MScan{M5.k3.w(rw, hs, he, M5.k3.ps0(dt, ps), [], M7.k3.lex0(dt, at), bk, qk, sk, un, lf, ab)}) == goal : T.Doc}:
  %M7.k3.qopen(dt, at, rw, hs, he, ps, bk, qk, sk, un, lf, ab) : {T.doc.read(D3.k3.pcs.text(pl, SCon{'"',
    String.append(D2.gap(gs), SCon{M7.k3.dl(cl), rest})}),
    _) == goal : T.Doc}
  M5.k3.pcs(pl, False{}, rw, hs, he, M5.k3.ps0(dt, ps), sk, ab, bk, un, lf, [], SCon{'"', String.append(D2.gap(gs),
    SCon{M7.k3.dl(cl), rest})}, goal, eo, +b2 => +u2 => +l2 =>
    k3.fin(D3.k3.pcs.name(pl), M3.rev.onto(D3.k3.pcs.name(pl), []), M16.k3.nm(D3.k3.pcs.name(pl)), gs, cl, rw, hs, he,
      M5.k3.ps0(dt, ps), b2, T.QBasic{}, sk, u2, l2, ab, rest, goal, ih))

# a literal segment, its blank space and a dot or `=`: the rest is read with
# the segment pushed under its characters, and back, uni and left as they
# were
def k3.lseg(
  +name: String,
  +gs: List<&2, Bool>,
  +cl: Bool,
  +dt: Bool,
  +at: Laws.KPos,
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
  +rest: String,
  +goal: T.Doc,
  el: {Laws.lit.text(name) == True{} : Bool},
  ih: k3.KT(cl, rw, hs, he, name <> M5.k3.ps0(dt, ps), sk, ab, rest, goal)
) -> {T.doc.read(SCon{'\'', String.append(name, SCon{'\'', String.append(D2.gap(gs), SCon{M7.k3.dl(cl), rest})})},
  T.MScan{M5.k3.w(rw, hs, he, M5.k3.ps0(dt, ps), [], M7.k3.lex0(dt, at), bk, qk, sk, un, lf, ab)}) == goal : T.Doc}:
  %M7.k3.lopen(dt, at, rw, hs, he, ps, bk, qk, sk, un, lf, ab) : {T.doc.read(String.append(name, SCon{'\'',
    String.append(D2.gap(gs), SCon{M7.k3.dl(cl), rest})}), _)
    == goal : T.Doc}
  Equal.trans(T.Doc, T.doc.read(String.append(name, SCon{'\'', String.append(D2.gap(gs), SCon{M7.k3.dl(cl), rest})}),
    T.MScan{M5.k3.l(False{}, rw, hs, he, M5.k3.ps0(dt, ps),
    sk, ab, bk, un, lf, [])}), T.doc.read(SCon{'\'', String.append(D2.gap(gs), SCon{M7.k3.dl(cl), rest})},
      T.MScan{M5.k3.l(False{}, rw, hs, he, M5.k3.ps0(dt, ps), sk, ab, bk,
    un, lf, M3.rev.onto(name, []))}), goal,
    M5.k3.l.body(name, SCon{'\'', String.append(D2.gap(gs), SCon{M7.k3.dl(cl), rest})}, False{}, rw, hs, he,
        M5.k3.ps0(dt,
      ps), sk, ab, bk, un, lf, [], el),
    k3.fin(name, M3.rev.onto(name, []), M16.k3.nm(name), gs, cl, rw, hs, he, M5.k3.ps0(dt, ps), bk, T.QLit{}, sk, un,
        lf, ab,
      rest, goal,
      ih))

# a segment spelled any way toml.abnf allows, its blank space and a dot or
# `=`
def k3.seg(
  sg: D3.KSeg,
  +gs: List<&2, Bool>,
  +cl: Bool,
  +dt: Bool,
  +at: Laws.KPos,
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
  +rest: String,
  +goal: T.Doc,
  eo: {Laws.k3.seg.ok(sg) == True{} : Bool},
  ih: k3.KT(cl, rw, hs, he, D3.k3.seg.name(sg) <> M5.k3.ps0(dt, ps), sk, ab, rest, goal)
) -> {T.doc.read(D3.k3.seg.text(sg, String.append(D2.gap(gs), SCon{M7.k3.dl(cl), rest})), T.MScan{M5.k3.w(rw, hs, he,
  M5.k3.ps0(dt, ps), [], M7.k3.lex0(dt, at), bk, qk, sk, un, lf, ab)}) == goal : T.Doc}:
  match sg:
    case D3.KsBare{name}:
      match name:
        case SNil{}:
          Eq.bit.absurd(&2, {T.doc.read(String.append(SNil{}, String.append(D2.gap(gs), SCon{M7.k3.dl(cl), rest})),
            T.MScan{M5.k3.w(rw, hs, he, M5.k3.ps0(dt, ps), [], M7.k3.lex0(dt, at), bk, qk, sk, un, lf,
                ab)}) == goal : T.Doc},
              eo)
        case SCon{hh, +tt}:
          match hh:
            case Chr{+xx}:
              k3.bseg(xx, tt, gs, cl, dt, at, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, goal, eo, ih)
    case D3.KsBasic{+pl}:
      k3.qseg(pl, gs, cl, dt, at, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, goal, eo, ih)
    case D3.KsLit{+name}:
      k3.lseg(name, gs, cl, dt, at, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, goal, eo, ih)

# a dotted key's segments, then blank space and `=`: the rest is read with
# every segment pushed onto parts, newest first
def k3.keys(
  ds: List<&2, Laws.KDot>,
  +last: D3.KSeg,
  +g: List<&2, Bool>,
  +dt: Bool,
  +at: Laws.KPos,
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
  +rest: String,
  +goal: T.Doc,
  +eo: {Laws.k3.dk.ok(ds, last) == True{} : Bool},
  ih: k3.KT(True{}, rw, hs, he, M5.k3.acc(ds, last, dt, ps), sk, ab, rest, goal)
) -> {T.doc.read(Laws.k3.dk.text(ds, last, String.append(D2.gap(g), SCon{'=', rest})), T.MScan{M5.k3.w(rw, hs, he,
  M5.k3.ps0(dt, ps), [], M7.k3.lex0(dt, at), bk, qk, sk, un, lf, ab)}) == goal
  : T.Doc}:
  match ds:
    case []:
      k3.seg(last, g, True{}, dt, at, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, goal, eo, ih)
    case Laws.KDot{+sg, g1, +g2} <> +dr:
      k3.seg(sg, g1, False{}, dt, at, rw, hs, he, ps, bk, qk, sk, un, lf, ab, String.append(D2.gap(g2),
        Laws.k3.dk.text(dr, last, String.append(D2.gap(g), SCon{'=', rest}))), goal, Eq.and.left(Laws.k3.seg.ok(sg),
        Laws.k3.dk.ok(dr, last), eo), +b2 => +q2 => +u2 => +l2 =>
        %M7.k3.dgap(g2, Laws.k3.dk.text(dr, last, String.append(D2.gap(g), SCon{'=', rest})), rw, hs, he,
          D3.k3.seg.name(sg) <> M5.k3.ps0(dt, ps), b2, q2, sk, u2, l2, ab) : {_ == goal : T.Doc}
        k3.keys(dr, last, g, True{}, at, rw, hs, he, D3.k3.seg.name(sg) <> M5.k3.ps0(dt, ps), b2, q2, sk, u2, l2, ab,
          rest, goal,
          Eq.and.right(Laws.k3.seg.ok(sg), Laws.k3.dk.ok(dr, last), eo), ih))

def Laws.key_reads_back_anywhere(
  at,
  g0,
  ds,
  last,
  ok,
  g,
  rows,
  heads,
  here,
  stack,
  arrtab,
  back,
  qkind,
  uni,
  left,
  rest,
  goal,
  ih
):
  %k3.g0(g0, at, rows, heads, here, stack, arrtab, back, qkind, uni, left, Laws.k3.dk.text(ds, last,
    String.append(D2.gap(g), SCon{'=', rest}))) : {_ == goal : T.Doc}
  k3.keys(ds, last, g, False{}, at, rows, heads, here, [], back, qkind, stack, uni, left, arrtab, rest, goal, ok, ih)

def Laws.header_reads_back_anywhere(
  arr,
  g0,
  ds,
  last,
  ok,
  g9,
  rows,
  heads,
  here,
  arrtab,
  back,
  qkind,
  uni,
  left,
  rows2,
  heads2,
  ew,
  rest,
  goal,
  ih
):
  M5.k3.hcore(arr, g0, ds, last, g9, rows, heads, here, arrtab, back, qkind, uni, left, rows2, heads2, rest, goal, ok,
      ew,
    ih)

# KEY-3: the lemmas of k3.has. A pair's value holds the rest of a path when
# it is a table or an inline table whose rows do, or an array of tables or
# an array one of whose elements does (kh.hv).

# a pair's value holds the rest of a path
def kh.hv(vv: T.Val, +path: List<&2, String>, +kk: String) -> Bool:
  match vv:
    case T.VHead{_q, rows}:
      Laws.k3.has(rows, path, kk)
    case T.VInl{rows}:
      Laws.k3.has(rows, path, kk)
    case T.VAots{_q, es}:
      Laws.k3.h(es, Laws.KhSome{path}, kk)
    case T.VArr{items}:
      Laws.k3.h(items, Laws.KhSome{path}, kk)
    case _v:
      False{}

# a Bool is itself or False
def kh.orf(bb: Bool) -> {Bool.not(bb) == Bool.or(Bool.not(bb), False{}) : Bool}:
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# one pair of the rows seen for a name: its value holds the path unless its
# name is another
def kh.cons(
  +mm: String,
  +vv: T.Val,
  +pp: List<&2, String>,
  +tt: List<&2, T.Val>,
  +nn: String,
  +kk: String
) -> {Laws.k3.h(T.VPair{mm, vv} <> tt, Laws.KhAll{nn, pp}, kk) == Bool.and(Bool.or(Bool.not(T.str.eq(mm, nn)),
  kh.hv(vv, pp, kk)), Laws.k3.h(tt, Laws.KhAll{nn, pp}, kk)) : Bool}:
  match vv:
    case T.VHead{_q, _r}:
      match pp:
        case []:
          {==}
        case _n <> _p:
          {==}
    case T.VInl{_r}:
      match pp:
        case []:
          {==}
        case _n <> _p:
          {==}
    case T.VAots{_q, _e}:
      {==}
    case T.VArr{_i}:
      {==}
    case T.VStr{_a}:
      %kh.orf(T.str.eq(mm, nn)) : {Bool.and(Bool.not(T.str.eq(mm, nn)), Laws.k3.h(tt, Laws.KhAll{nn, pp}, kk))
        == Bool.and(_, Laws.k3.h(tt, Laws.KhAll{nn, pp}, kk)) : Bool}
      {==}
    case T.VSpan{_a, _b}:
      %kh.orf(T.str.eq(mm, nn)) : {Bool.and(Bool.not(T.str.eq(mm, nn)), Laws.k3.h(tt, Laws.KhAll{nn, pp}, kk))
        == Bool.and(_, Laws.k3.h(tt, Laws.KhAll{nn, pp}, kk)) : Bool}
      {==}
    case T.VInt{_a, _b}:
      %kh.orf(T.str.eq(mm, nn)) : {Bool.and(Bool.not(T.str.eq(mm, nn)), Laws.k3.h(tt, Laws.KhAll{nn, pp}, kk))
        == Bool.and(_, Laws.k3.h(tt, Laws.KhAll{nn, pp}, kk)) : Bool}
      {==}
    case T.VFlo{_a, _b}:
      %kh.orf(T.str.eq(mm, nn)) : {Bool.and(Bool.not(T.str.eq(mm, nn)), Laws.k3.h(tt, Laws.KhAll{nn, pp}, kk))
        == Bool.and(_, Laws.k3.h(tt, Laws.KhAll{nn, pp}, kk)) : Bool}
      {==}
    case T.VBool{_a}:
      %kh.orf(T.str.eq(mm, nn)) : {Bool.and(Bool.not(T.str.eq(mm, nn)), Laws.k3.h(tt, Laws.KhAll{nn, pp}, kk))
        == Bool.and(_, Laws.k3.h(tt, Laws.KhAll{nn, pp}, kk)) : Bool}
      {==}
    case T.VWhen{_a}:
      %kh.orf(T.str.eq(mm, nn)) : {Bool.and(Bool.not(T.str.eq(mm, nn)), Laws.k3.h(tt, Laws.KhAll{nn, pp}, kk))
        == Bool.and(_, Laws.k3.h(tt, Laws.KhAll{nn, pp}, kk)) : Bool}
      {==}
    case T.VAot{_a, _b}:
      %kh.orf(T.str.eq(mm, nn)) : {Bool.and(Bool.not(T.str.eq(mm, nn)), Laws.k3.h(tt, Laws.KhAll{nn, pp}, kk))
        == Bool.and(_, Laws.k3.h(tt, Laws.KhAll{nn, pp}, kk)) : Bool}
      {==}
    case T.VPair{_a, _b}:
      %kh.orf(T.str.eq(mm, nn)) : {Bool.and(Bool.not(T.str.eq(mm, nn)), Laws.k3.h(tt, Laws.KhAll{nn, pp}, kk))
        == Bool.and(_, Laws.k3.h(tt, Laws.KhAll{nn, pp}, kk)) : Bool}
      {==}

# a pair of the rows seen for a name holds the rest of the path, as k3.h asks
# of it: its name is another, or its value holds the rest
def kh.eA(xx: T.Val, +nn: String, +pp: List<&2, String>, +kk: String) -> Bool:
  match xx:
    case T.VPair{mm, vv}:
      Bool.or(Bool.not(T.str.eq(mm, nn)), kh.hv(vv, pp, kk))
    case _x:
      True{}

# an element of an array of tables or an item of an array holds the rest of
# the path
def kh.eS(xx: T.Val, +pp: List<&2, String>, +kk: String) -> Bool:
  match xx:
    case T.VAot{_q, rows}:
      Laws.k3.has(rows, pp, kk)
    case T.VInl{rows}:
      Laws.k3.has(rows, pp, kk)
    case T.VArr{items}:
      Laws.k3.h(items, Laws.KhSome{pp}, kk)
    case _x:
      False{}

# a value is a pair of this name
def kh.eF(xx: T.Val, +nn: String) -> Bool:
  match xx:
    case T.VPair{mm, _v}:
      T.str.eq(mm, nn)
    case _x:
      False{}

# the rows seen for a name, one value at a time
def kh.uA(
  +xx: T.Val,
  +pp: List<&2, String>,
  +tt: List<&2, T.Val>,
  +nn: String,
  +kk: String
) -> {Laws.k3.h(xx <> tt, Laws.KhAll{nn, pp}, kk) == Bool.and(kh.eA(xx, nn, pp, kk), Laws.k3.h(tt, Laws.KhAll{nn,
  pp}, kk)) : Bool}:
  match xx:
    case T.VPair{+mm, +vv}:
      kh.cons(mm, vv, pp, tt, nn, kk)
    case T.VStr{_a}:
      {==}
    case T.VSpan{_a, _b}:
      {==}
    case T.VInt{_a, _b}:
      {==}
    case T.VFlo{_a, _b}:
      {==}
    case T.VBool{_a}:
      {==}
    case T.VWhen{_a}:
      {==}
    case T.VArr{_a}:
      {==}
    case T.VInl{_a}:
      {==}
    case T.VHead{_a, _b}:
      {==}
    case T.VAot{_a, _b}:
      {==}
    case T.VAots{_a, _b}:
      {==}

# the elements of an array of tables, or the items of an array, one at a time
def kh.uS(
  +xx: T.Val,
  +pp: List<&2, String>,
  +tt: List<&2, T.Val>,
  +kk: String
) -> {Laws.k3.h(xx <> tt, Laws.KhSome{pp}, kk) == Bool.or(kh.eS(xx, pp, kk), Laws.k3.h(tt, Laws.KhSome{pp}, kk))
  : Bool}:
  match xx:
    case T.VAot{_q, _r}:
      match pp:
        case []:
          {==}
        case _n <> _p:
          {==}
    case T.VInl{_r}:
      match pp:
        case []:
          {==}
        case _n <> _p:
          {==}
    case T.VArr{_i}:
      {==}
    case T.VPair{_a, bb}:
      match bb:
        case T.VStr{_c}:
          {==}
        case T.VSpan{_c, _d}:
          {==}
        case T.VInt{_c, _d}:
          {==}
        case T.VFlo{_c, _d}:
          {==}
        case T.VBool{_c}:
          {==}
        case T.VWhen{_c}:
          {==}
        case T.VArr{_c}:
          {==}
        case T.VInl{_c}:
          {==}
        case T.VHead{_c, _d}:
          {==}
        case T.VAot{_c, _d}:
          {==}
        case T.VAots{_c, _d}:
          {==}
        case T.VPair{_c, _d}:
          {==}
    case T.VStr{_a}:
      {==}
    case T.VSpan{_a, _b}:
      {==}
    case T.VInt{_a, _b}:
      {==}
    case T.VFlo{_a, _b}:
      {==}
    case T.VBool{_a}:
      {==}
    case T.VWhen{_a}:
      {==}
    case T.VHead{_a, _b}:
      {==}
    case T.VAots{_a, _b}:
      {==}

# the first pair found, as a Bool
def kh.fstep(
  bb: Bool,
  +vv: T.Val,
  +tt: List<&2, T.Val>,
  +nn: String
) -> {Laws.k3.found(T.find.step(bb, vv, _u => T.rows.find(tt, nn))) == Bool.or(bb, Laws.k3.found(T.get(tt, nn)))
  : Bool}:
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# a name found in rows, one value at a time
def kh.uF(
  +xx: T.Val,
  +tt: List<&2, T.Val>,
  +nn: String
) -> {Laws.k3.found(T.get(xx <> tt, nn)) == Bool.or(kh.eF(xx, nn), Laws.k3.found(T.get(tt, nn))) : Bool}:
  match xx:
    case T.VPair{+mm, +vv}:
      kh.fstep(T.str.eq(mm, nn), vv, tt, nn)
    case T.VStr{_a}:
      {==}
    case T.VSpan{_a, _b}:
      {==}
    case T.VInt{_a, _b}:
      {==}
    case T.VFlo{_a, _b}:
      {==}
    case T.VBool{_a}:
      {==}
    case T.VWhen{_a}:
      {==}
    case T.VArr{_a}:
      {==}
    case T.VInl{_a}:
      {==}
    case T.VHead{_a, _b}:
      {==}
    case T.VAot{_a, _b}:
      {==}
    case T.VAots{_a, _b}:
      {==}

# a name found in rows
def kh.F(xs: List<&2, T.Val>, +nn: String) -> Bool:
  Laws.k3.found(T.get(xs, nn))

# the rows seen for a name hold the rest of the path
def kh.A(xs: List<&2, T.Val>, +nn: String, +pp: List<&2, String>, +kk: String) -> Bool:
  Laws.k3.h(xs, Laws.KhAll{nn, pp}, kk)

# some element or item holds the rest of the path
def kh.S(xs: List<&2, T.Val>, +pp: List<&2, String>, +kk: String) -> Bool:
  Laws.k3.h(xs, Laws.KhSome{pp}, kk)

# or, with the first two swapped into a group
def bo.or.sw(aa: Bool, bb: Bool, cc: Bool) -> {Bool.or(bb, Bool.or(aa, cc)) == Bool.or(Bool.or(aa, bb), cc) : Bool}:
  match aa bb:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# and, with the first two swapped into a group
def bo.and.sw(
  aa: Bool,
  bb: Bool,
  cc: Bool
) -> {Bool.and(bb, Bool.and(aa, cc)) == Bool.and(Bool.and(aa, bb), cc) : Bool}:
  match aa bb:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# a name is found in a reversal onto a list when it is in either
def kh.revF(
  xs: List<&2, T.Val>,
  +acc: List<&2, T.Val>,
  +nn: String
) -> {kh.F(List.reverse.go(&2, T.Val, xs, acc), nn) == Bool.or(kh.F(xs, nn), kh.F(acc, nn)) : Bool}:
  match xs:
    case []:
      {==}
    case +xx <> +tt:
      Equal.trans(Bool, kh.F(List.reverse.go(&2, T.Val, tt, xx <> acc), nn), Bool.or(kh.F(tt, nn), kh.F(xx <> acc,
        nn)), Bool.or(kh.F(xx <> tt, nn), kh.F(acc, nn)), kh.revF(tt, xx <> acc, nn),
        Equal.trans(Bool, Bool.or(kh.F(tt, nn), kh.F(xx <> acc, nn)), Bool.or(kh.F(tt, nn), Bool.or(kh.eF(xx, nn),
          kh.F(acc, nn))), Bool.or(kh.F(xx <> tt, nn), kh.F(acc, nn)),
          Equal.cong(Bool, Bool, zz => Bool.or(kh.F(tt, nn), zz), kh.F(xx <> acc, nn), Bool.or(kh.eF(xx, nn),
            kh.F(acc, nn)), kh.uF(xx, acc, nn)),
          Equal.trans(Bool, Bool.or(kh.F(tt, nn), Bool.or(kh.eF(xx, nn), kh.F(acc, nn))),
            Bool.or(Bool.or(kh.eF(xx, nn), kh.F(tt, nn)), kh.F(acc, nn)), Bool.or(kh.F(xx <> tt, nn), kh.F(acc,
              nn)), bo.or.sw(kh.eF(xx, nn), kh.F(tt, nn), kh.F(acc, nn)),
            Equal.cong(Bool, Bool, zz => Bool.or(zz, kh.F(acc, nn)), Bool.or(kh.eF(xx, nn), kh.F(tt, nn)),
              kh.F(xx <> tt, nn), Equal.sym(Bool, kh.F(xx <> tt, nn), Bool.or(kh.eF(xx, nn), kh.F(tt, nn)),
                kh.uF(xx, tt, nn))))))

# the rows seen for a name hold a path in a reversal onto a list when they
# do in both
def kh.revA(
  xs: List<&2, T.Val>,
  +acc: List<&2, T.Val>,
  +nn: String,
  +pp: List<&2, String>,
  +kk: String
) -> {kh.A(List.reverse.go(&2, T.Val, xs, acc), nn, pp, kk) == Bool.and(kh.A(xs, nn, pp, kk), kh.A(acc, nn, pp,
  kk)) : Bool}:
  match xs:
    case []:
      {==}
    case +xx <> +tt:
      Equal.trans(Bool, kh.A(List.reverse.go(&2, T.Val, tt, xx <> acc), nn, pp, kk), Bool.and(kh.A(tt, nn, pp, kk),
        kh.A(xx <> acc, nn, pp, kk)), Bool.and(kh.A(xx <> tt, nn, pp, kk), kh.A(acc, nn, pp, kk)),
        kh.revA(tt, xx <> acc, nn, pp, kk),
        Equal.trans(Bool, Bool.and(kh.A(tt, nn, pp, kk), kh.A(xx <> acc, nn, pp, kk)), Bool.and(kh.A(tt, nn, pp,
          kk), Bool.and(kh.eA(xx, nn, pp, kk), kh.A(acc, nn, pp, kk))), Bool.and(kh.A(xx <> tt, nn, pp, kk),
          kh.A(acc, nn, pp, kk)),
          Equal.cong(Bool, Bool, zz => Bool.and(kh.A(tt, nn, pp, kk), zz), kh.A(xx <> acc, nn, pp, kk),
            Bool.and(kh.eA(xx, nn, pp, kk), kh.A(acc, nn, pp, kk)), kh.uA(xx, pp, acc, nn, kk)),
          Equal.trans(Bool, Bool.and(kh.A(tt, nn, pp, kk), Bool.and(kh.eA(xx, nn, pp, kk), kh.A(acc, nn, pp,
            kk))), Bool.and(Bool.and(kh.eA(xx, nn, pp, kk), kh.A(tt, nn, pp, kk)), kh.A(acc, nn, pp, kk)),
            Bool.and(kh.A(xx <> tt, nn, pp, kk), kh.A(acc, nn, pp, kk)), bo.and.sw(kh.eA(xx, nn, pp, kk), kh.A(tt,
              nn, pp, kk), kh.A(acc, nn, pp, kk)),
            Equal.cong(Bool, Bool, zz => Bool.and(zz, kh.A(acc, nn, pp, kk)), Bool.and(kh.eA(xx, nn, pp, kk),
              kh.A(tt, nn, pp, kk)), kh.A(xx <> tt, nn, pp, kk), Equal.sym(Bool, kh.A(xx <> tt, nn, pp, kk),
                Bool.and(kh.eA(xx, nn, pp, kk), kh.A(tt, nn, pp, kk)), kh.uA(xx, pp, tt, nn, kk))))))

# some element holds a path in a reversal onto a list when one of either
# does
def kh.revS(
  xs: List<&2, T.Val>,
  +acc: List<&2, T.Val>,
  +pp: List<&2, String>,
  +kk: String
) -> {kh.S(List.reverse.go(&2, T.Val, xs, acc), pp, kk) == Bool.or(kh.S(xs, pp, kk), kh.S(acc, pp, kk)) : Bool}:
  match xs:
    case []:
      {==}
    case +xx <> +tt:
      Equal.trans(Bool, kh.S(List.reverse.go(&2, T.Val, tt, xx <> acc), pp, kk), Bool.or(kh.S(tt, pp, kk),
        kh.S(xx <> acc, pp, kk)), Bool.or(kh.S(xx <> tt, pp, kk), kh.S(acc, pp, kk)), kh.revS(tt, xx <> acc, pp,
          kk),
        Equal.trans(Bool, Bool.or(kh.S(tt, pp, kk), kh.S(xx <> acc, pp, kk)), Bool.or(kh.S(tt, pp, kk),
          Bool.or(kh.eS(xx, pp, kk), kh.S(acc, pp, kk))), Bool.or(kh.S(xx <> tt, pp, kk), kh.S(acc, pp, kk)),
          Equal.cong(Bool, Bool, zz => Bool.or(kh.S(tt, pp, kk), zz), kh.S(xx <> acc, pp, kk),
            Bool.or(kh.eS(xx, pp, kk), kh.S(acc, pp, kk)), kh.uS(xx, pp, acc, kk)),
          Equal.trans(Bool, Bool.or(kh.S(tt, pp, kk), Bool.or(kh.eS(xx, pp, kk), kh.S(acc, pp, kk))),
            Bool.or(Bool.or(kh.eS(xx, pp, kk), kh.S(tt, pp, kk)), kh.S(acc, pp, kk)), Bool.or(kh.S(xx <> tt, pp,
              kk), kh.S(acc, pp, kk)), bo.or.sw(kh.eS(xx, pp, kk), kh.S(tt, pp, kk), kh.S(acc, pp, kk)),
            Equal.cong(Bool, Bool, zz => Bool.or(zz, kh.S(acc, pp, kk)), Bool.or(kh.eS(xx, pp, kk), kh.S(tt, pp,
              kk)), kh.S(xx <> tt, pp, kk), Equal.sym(Bool, kh.S(xx <> tt, pp, kk), Bool.or(kh.eS(xx, pp, kk),
                kh.S(tt, pp, kk)), kh.uS(xx, pp, tt, kk))))))

# which of k3.h's readings a lemma is about: a name found, the rows seen
# for a name, or some element or item
type KSel is Data:
  SlF{name: String}
  SlA{name: String, path: List<&2, String>}
  SlS{path: List<&2, String>}

# the reading a selector names
def kh.sl(sel: KSel, xs: List<&2, T.Val>, +kk: String) -> Bool:
  match sel:
    case SlF{nn}:
      kh.F(xs, nn)
    case SlA{nn, pp}:
      kh.A(xs, nn, pp, kk)
    case SlS{pp}:
      kh.S(xs, pp, kk)

# the reading of one value
def kh.el(sel: KSel, xx: T.Val, +kk: String) -> Bool:
  match sel:
    case SlF{nn}:
      kh.eF(xx, nn)
    case SlA{nn, pp}:
      kh.eA(xx, nn, pp, kk)
    case SlS{pp}:
      kh.eS(xx, pp, kk)

# how the readings of the values join: found or some is an or, all is an and
def kh.op(sel: KSel, aa: Bool, bb: Bool) -> Bool:
  match sel:
    case SlF{_n}:
      Bool.or(aa, bb)
    case SlA{_n, _p}:
      Bool.and(aa, bb)
    case SlS{_p}:
      Bool.or(aa, bb)

# a reading, one value at a time
def kh.slu(
  +sel: KSel,
  +xx: T.Val,
  +tt: List<&2, T.Val>,
  +kk: String
) -> {kh.sl(sel, xx <> tt, kk) == kh.op(sel, kh.el(sel, xx, kk), kh.sl(sel, tt, kk)) : Bool}:
  match sel:
    case SlF{+nn}:
      kh.uF(xx, tt, nn)
    case SlA{+nn, +pp}:
      kh.uA(xx, pp, tt, nn, kk)
    case SlS{+pp}:
      kh.uS(xx, pp, tt, kk)

# or False is the Bool
def bo.or.f(aa: Bool) -> {Bool.or(aa, False{}) == aa : Bool}:
  match aa:
    case True{}:
      {==}
    case False{}:
      {==}

# and True is the Bool
def bo.and.t(aa: Bool) -> {Bool.and(aa, True{}) == aa : Bool}:
  match aa:
    case True{}:
      {==}
    case False{}:
      {==}

# both sides of an and
def bo.and.cong(
  aa: Bool,
  bb: Bool,
  cc: Bool,
  dd: Bool,
  +e1: {aa == cc : Bool},
  +e2: {bb == dd : Bool}
) -> {Bool.and(aa, bb) == Bool.and(cc, dd) : Bool}:
  Equal.trans(Bool, Bool.and(aa, bb), Bool.and(cc, bb), Bool.and(cc, dd),
    Equal.cong(Bool, Bool, zz => Bool.and(zz, bb), aa, cc, e1),
    Equal.cong(Bool, Bool, zz => Bool.and(cc, zz), bb, dd, e2))

# both sides of an or
def bo.or.cong(
  aa: Bool,
  bb: Bool,
  cc: Bool,
  dd: Bool,
  +e1: {aa == cc : Bool},
  +e2: {bb == dd : Bool}
) -> {Bool.or(aa, bb) == Bool.or(cc, dd) : Bool}:
  Equal.trans(Bool, Bool.or(aa, bb), Bool.or(cc, bb), Bool.or(cc, dd),
    Equal.cong(Bool, Bool, zz => Bool.or(zz, bb), aa, cc, e1),
    Equal.cong(Bool, Bool, zz => Bool.or(cc, zz), bb, dd, e2))

# a reading does not see the order of the values
def kh.slrev(
  +sel: KSel,
  +ys: List<&2, T.Val>,
  +kk: String
) -> {kh.sl(sel, List.reverse(&2, T.Val, ys), kk) == kh.sl(sel, ys, kk) : Bool}:
  match sel:
    case SlF{+nn}:
      Equal.trans(Bool, kh.F(List.reverse(&2, T.Val, ys), nn), Bool.or(kh.F(ys, nn), False{}), kh.F(ys, nn),
        kh.revF(ys, [], nn), bo.or.f(kh.F(ys, nn)))
    case SlA{+nn, +pp}:
      Equal.trans(Bool, kh.A(List.reverse(&2, T.Val, ys), nn, pp, kk), Bool.and(kh.A(ys, nn, pp, kk), True{}),
        kh.A(ys, nn, pp, kk), kh.revA(ys, [], nn, pp, kk), bo.and.t(kh.A(ys, nn, pp, kk)))
    case SlS{+pp}:
      Equal.trans(Bool, kh.S(List.reverse(&2, T.Val, ys), pp, kk), Bool.or(kh.S(ys, pp, kk), False{}),
        kh.S(ys, pp, kk), kh.revS(ys, [], pp, kk), bo.or.f(kh.S(ys, pp, kk)))

# a reading of sealed rows, from the reading of the rows with every value
# sealed
def kh.slseal(
  +sel: KSel,
  +rr: List<&2, T.Val>,
  +kk: String,
  +ih: {kh.sl(sel, M16.cv.smap(rr), kk) == kh.sl(sel, rr, kk) : Bool}
) -> {kh.sl(sel, T.rows.seal(rr), kk) == kh.sl(sel, rr, kk) : Bool}:
  Equal.trans(Bool, kh.sl(sel, T.rows.seal(rr), kk), kh.sl(sel, List.reverse(&2, T.Val, M16.cv.smap(rr)), kk),
    kh.sl(sel, rr, kk),
    Equal.cong(List<&2, T.Val>, Bool, zs => kh.sl(sel, zs, kk), T.rows.seal(rr), List.reverse(&2, T.Val,
      M16.cv.smap(rr)), M16.cv.seal.rs(rr)),
    Equal.trans(Bool, kh.sl(sel, List.reverse(&2, T.Val, M16.cv.smap(rr)), kk), kh.sl(sel, M16.cv.smap(rr), kk),
      kh.sl(sel, rr, kk), kh.slrev(sel, M16.cv.smap(rr), kk), ih))

# both sides of the join
def kh.opcong(
  +sel: KSel,
  aa: Bool,
  bb: Bool,
  cc: Bool,
  dd: Bool,
  +e1: {aa == cc : Bool},
  +e2: {bb == dd : Bool}
) -> {kh.op(sel, aa, bb) == kh.op(sel, cc, dd) : Bool}:
  match sel:
    case SlF{_n}:
      bo.or.cong(aa, bb, cc, dd, e1, e2)
    case SlA{_n, _p}:
      bo.and.cong(aa, bb, cc, dd, e1, e2)
    case SlS{_p}:
      bo.or.cong(aa, bb, cc, dd, e1, e2)

# a reading of rows with every value sealed, one value at a time
def kh.smstep(
  +sel: KSel,
  +xx: T.Val,
  +tt: List<&2, T.Val>,
  +kk: String,
  +ee: {kh.el(sel, D4.sealed(xx), kk) == kh.el(sel, xx, kk) : Bool},
  +ih: {kh.sl(sel, M16.cv.smap(tt), kk) == kh.sl(sel, tt, kk) : Bool}
) -> {kh.sl(sel, D4.sealed(xx) <> M16.cv.smap(tt), kk) == kh.sl(sel, xx <> tt, kk) : Bool}:
  Equal.trans(Bool, kh.sl(sel, D4.sealed(xx) <> M16.cv.smap(tt), kk), kh.op(sel, kh.el(sel, D4.sealed(xx), kk),
    kh.sl(sel, M16.cv.smap(tt), kk)), kh.sl(sel, xx <> tt, kk), kh.slu(sel, D4.sealed(xx), M16.cv.smap(tt), kk),
    Equal.trans(Bool, kh.op(sel, kh.el(sel, D4.sealed(xx), kk), kh.sl(sel, M16.cv.smap(tt), kk)), kh.op(sel,
      kh.el(sel, xx, kk), kh.sl(sel, tt, kk)), kh.sl(sel, xx <> tt, kk), kh.opcong(sel, kh.el(sel,
        D4.sealed(xx), kk), kh.sl(sel, M16.cv.smap(tt), kk), kh.el(sel, xx, kk), kh.sl(sel, tt, kk), ee, ih),
      Equal.sym(Bool, kh.sl(sel, xx <> tt, kk), kh.op(sel, kh.el(sel, xx, kk), kh.sl(sel, tt, kk)), kh.slu(sel,
        xx, tt, kk))))

# sealed rows hold a path as the rows do, given that for their values
def kh.hs(
  pp: List<&2, String>,
  +rr: List<&2, T.Val>,
  +kk: String,
  fF: @nm: String -> {kh.F(M16.cv.smap(rr), nm) == kh.F(rr, nm) : Bool},
  fA: @nm: String -> @qq: List<&2, String> -> {kh.A(M16.cv.smap(rr), nm, qq, kk) == kh.A(rr, nm, qq, kk) : Bool}
) -> {Laws.k3.has(T.rows.seal(rr), pp, kk) == Laws.k3.has(rr, pp, kk) : Bool}:
  match pp:
    case []:
      kh.slseal(SlF{kk}, rr, kk, fF(kk))
    case +n2 <> +q2:
      bo.and.cong(kh.F(T.rows.seal(rr), n2), kh.A(T.rows.seal(rr), n2, q2, kk), kh.F(rr, n2), kh.A(rr, n2, q2,
        kk), kh.slseal(SlF{n2}, rr, kk, fF(n2)), kh.slseal(SlA{n2, q2}, rr, kk, fA(n2, q2)))

# a sealed array's items, in order again, hold a path as the items do
def kh.ha(
  +pp: List<&2, String>,
  +rr: List<&2, T.Val>,
  +kk: String,
  +iS: {kh.S(M16.cv.smap(rr), pp, kk) == kh.S(rr, pp, kk) : Bool}
) -> {kh.S(List.reverse(&2, T.Val, T.rows.seal(rr)), pp, kk) == kh.S(rr, pp, kk) : Bool}:
  Equal.trans(Bool, kh.S(List.reverse(&2, T.Val, T.rows.seal(rr)), pp, kk), kh.S(T.rows.seal(rr), pp, kk),
    kh.S(rr, pp, kk), kh.slrev(SlS{pp}, T.rows.seal(rr), kk), kh.slseal(SlS{pp}, rr, kk, iS))

# rows with every value sealed hold what the rows hold, read any way
def kh.smapeq(
  xs: List<&2, T.Val>,
  +sel: KSel,
  +kk: String
) -> {kh.sl(sel, M16.cv.smap(xs), kk) == kh.sl(sel, xs, kk) : Bool}:
  match xs:
    case []:
      {==}
    case T.VPair{+mm, T.VHead{+qq, +rr}} <> +tt:
      match sel:
        case SlF{+nn}:
          kh.smstep(sel, T.VPair{mm, T.VHead{qq, rr}}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlA{+nn, +pp}:
          kh.smstep(sel, T.VPair{mm, T.VHead{qq, rr}}, tt, kk, bo.or.cong(Bool.not(T.str.eq(mm, nn)),
            Laws.k3.has(T.rows.seal(rr), pp, kk), Bool.not(T.str.eq(mm, nn)), Laws.k3.has(rr, pp, kk), {==}, kh.hs(pp,
              rr, kk, nm => kh.smapeq(rr, SlF{nm}, kk), nm => qq => kh.smapeq(rr, SlA{nm, qq}, kk))), kh.smapeq(tt,
                sel, kk))
        case SlS{+pp}:
          kh.smstep(sel, T.VPair{mm, T.VHead{qq, rr}}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
    case T.VPair{+mm, T.VInl{+rr}} <> +tt:
      match sel:
        case SlF{+nn}:
          kh.smstep(sel, T.VPair{mm, T.VInl{rr}}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlA{+nn, +pp}:
          kh.smstep(sel, T.VPair{mm, T.VInl{rr}}, tt, kk, bo.or.cong(Bool.not(T.str.eq(mm, nn)),
            Laws.k3.has(T.rows.seal(rr), pp, kk), Bool.not(T.str.eq(mm, nn)), Laws.k3.has(rr, pp, kk), {==}, kh.hs(pp,
              rr, kk, nm => kh.smapeq(rr, SlF{nm}, kk), nm => qq => kh.smapeq(rr, SlA{nm, qq}, kk))), kh.smapeq(tt,
                sel, kk))
        case SlS{+pp}:
          kh.smstep(sel, T.VPair{mm, T.VInl{rr}}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
    case T.VPair{+mm, T.VAots{+qq, +rr}} <> +tt:
      match sel:
        case SlF{+nn}:
          kh.smstep(sel, T.VPair{mm, T.VAots{qq, rr}}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlA{+nn, +pp}:
          kh.smstep(sel, T.VPair{mm, T.VAots{qq, rr}}, tt, kk, bo.or.cong(Bool.not(T.str.eq(mm, nn)),
            kh.S(T.rows.seal(rr), pp, kk), Bool.not(T.str.eq(mm, nn)), kh.S(rr, pp, kk), {==}, kh.slseal(SlS{pp}, rr,
              kk, kh.smapeq(rr, SlS{pp}, kk))), kh.smapeq(tt, sel, kk))
        case SlS{+pp}:
          kh.smstep(sel, T.VPair{mm, T.VAots{qq, rr}}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
    case T.VPair{+mm, T.VArr{+rr}} <> +tt:
      match sel:
        case SlF{+nn}:
          kh.smstep(sel, T.VPair{mm, T.VArr{rr}}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlA{+nn, +pp}:
          kh.smstep(sel, T.VPair{mm, T.VArr{rr}}, tt, kk, bo.or.cong(Bool.not(T.str.eq(mm, nn)), kh.S(List.reverse(&2,
            T.Val, T.rows.seal(rr)), pp, kk), Bool.not(T.str.eq(mm, nn)), kh.S(rr, pp, kk), {==}, kh.ha(pp, rr, kk,
              kh.smapeq(rr, SlS{pp}, kk))), kh.smapeq(tt, sel, kk))
        case SlS{+pp}:
          kh.smstep(sel, T.VPair{mm, T.VArr{rr}}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
    case T.VPair{+mm, T.VStr{+a1}} <> +tt:
      match sel:
        case SlF{+nn}:
          kh.smstep(sel, T.VPair{mm, T.VStr{a1}}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlA{+nn, +pp}:
          kh.smstep(sel, T.VPair{mm, T.VStr{a1}}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlS{+pp}:
          kh.smstep(sel, T.VPair{mm, T.VStr{a1}}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
    case T.VPair{+mm, T.VSpan{+a1, +a2}} <> +tt:
      match sel:
        case SlF{+nn}:
          kh.smstep(sel, T.VPair{mm, T.VSpan{a1, a2}}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlA{+nn, +pp}:
          kh.smstep(sel, T.VPair{mm, T.VSpan{a1, a2}}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlS{+pp}:
          kh.smstep(sel, T.VPair{mm, T.VSpan{a1, a2}}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
    case T.VPair{+mm, T.VInt{+a1, +a2}} <> +tt:
      match sel:
        case SlF{+nn}:
          kh.smstep(sel, T.VPair{mm, T.VInt{a1, a2}}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlA{+nn, +pp}:
          kh.smstep(sel, T.VPair{mm, T.VInt{a1, a2}}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlS{+pp}:
          kh.smstep(sel, T.VPair{mm, T.VInt{a1, a2}}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
    case T.VPair{+mm, T.VFlo{+a1, +a2}} <> +tt:
      match sel:
        case SlF{+nn}:
          kh.smstep(sel, T.VPair{mm, T.VFlo{a1, a2}}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlA{+nn, +pp}:
          kh.smstep(sel, T.VPair{mm, T.VFlo{a1, a2}}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlS{+pp}:
          kh.smstep(sel, T.VPair{mm, T.VFlo{a1, a2}}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
    case T.VPair{+mm, T.VBool{+a1}} <> +tt:
      match sel:
        case SlF{+nn}:
          kh.smstep(sel, T.VPair{mm, T.VBool{a1}}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlA{+nn, +pp}:
          kh.smstep(sel, T.VPair{mm, T.VBool{a1}}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlS{+pp}:
          kh.smstep(sel, T.VPair{mm, T.VBool{a1}}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
    case T.VPair{+mm, T.VWhen{+a1}} <> +tt:
      match sel:
        case SlF{+nn}:
          kh.smstep(sel, T.VPair{mm, T.VWhen{a1}}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlA{+nn, +pp}:
          kh.smstep(sel, T.VPair{mm, T.VWhen{a1}}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlS{+pp}:
          kh.smstep(sel, T.VPair{mm, T.VWhen{a1}}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
    case T.VPair{+mm, T.VAot{+a1, +a2}} <> +tt:
      match sel:
        case SlF{+nn}:
          kh.smstep(sel, T.VPair{mm, T.VAot{a1, a2}}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlA{+nn, +pp}:
          kh.smstep(sel, T.VPair{mm, T.VAot{a1, a2}}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlS{+pp}:
          kh.smstep(sel, T.VPair{mm, T.VAot{a1, a2}}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
    case T.VPair{+mm, T.VPair{+a1, +a2}} <> +tt:
      match sel:
        case SlF{+nn}:
          kh.smstep(sel, T.VPair{mm, T.VPair{a1, a2}}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlA{+nn, +pp}:
          kh.smstep(sel, T.VPair{mm, T.VPair{a1, a2}}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlS{+pp}:
          kh.smstep(sel, T.VPair{mm, T.VPair{a1, a2}}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
    case T.VAot{+qq, +rr} <> +tt:
      match sel:
        case SlF{+nn}:
          kh.smstep(sel, T.VAot{qq, rr}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlA{+nn, +pp}:
          kh.smstep(sel, T.VAot{qq, rr}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlS{+pp}:
          kh.smstep(sel, T.VAot{qq, rr}, tt, kk, kh.hs(pp, rr, kk, nm => kh.smapeq(rr, SlF{nm}, kk),
            nm => qq => kh.smapeq(rr, SlA{nm, qq}, kk)), kh.smapeq(tt, sel, kk))
    case T.VInl{+rr} <> +tt:
      match sel:
        case SlF{+nn}:
          kh.smstep(sel, T.VInl{rr}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlA{+nn, +pp}:
          kh.smstep(sel, T.VInl{rr}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlS{+pp}:
          kh.smstep(sel, T.VInl{rr}, tt, kk, kh.hs(pp, rr, kk, nm => kh.smapeq(rr, SlF{nm}, kk),
            nm => qq => kh.smapeq(rr, SlA{nm, qq}, kk)), kh.smapeq(tt, sel, kk))
    case T.VArr{+rr} <> +tt:
      match sel:
        case SlF{+nn}:
          kh.smstep(sel, T.VArr{rr}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlA{+nn, +pp}:
          kh.smstep(sel, T.VArr{rr}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlS{+pp}:
          kh.smstep(sel, T.VArr{rr}, tt, kk, kh.ha(pp, rr, kk, kh.smapeq(rr, SlS{pp}, kk)), kh.smapeq(tt, sel, kk))
    case T.VStr{+a1} <> +tt:
      match sel:
        case SlF{+nn}:
          kh.smstep(sel, T.VStr{a1}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlA{+nn, +pp}:
          kh.smstep(sel, T.VStr{a1}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlS{+pp}:
          kh.smstep(sel, T.VStr{a1}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
    case T.VSpan{+a1, +a2} <> +tt:
      match sel:
        case SlF{+nn}:
          kh.smstep(sel, T.VSpan{a1, a2}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlA{+nn, +pp}:
          kh.smstep(sel, T.VSpan{a1, a2}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlS{+pp}:
          kh.smstep(sel, T.VSpan{a1, a2}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
    case T.VInt{+a1, +a2} <> +tt:
      match sel:
        case SlF{+nn}:
          kh.smstep(sel, T.VInt{a1, a2}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlA{+nn, +pp}:
          kh.smstep(sel, T.VInt{a1, a2}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlS{+pp}:
          kh.smstep(sel, T.VInt{a1, a2}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
    case T.VFlo{+a1, +a2} <> +tt:
      match sel:
        case SlF{+nn}:
          kh.smstep(sel, T.VFlo{a1, a2}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlA{+nn, +pp}:
          kh.smstep(sel, T.VFlo{a1, a2}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlS{+pp}:
          kh.smstep(sel, T.VFlo{a1, a2}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
    case T.VBool{+a1} <> +tt:
      match sel:
        case SlF{+nn}:
          kh.smstep(sel, T.VBool{a1}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlA{+nn, +pp}:
          kh.smstep(sel, T.VBool{a1}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlS{+pp}:
          kh.smstep(sel, T.VBool{a1}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
    case T.VWhen{+a1} <> +tt:
      match sel:
        case SlF{+nn}:
          kh.smstep(sel, T.VWhen{a1}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlA{+nn, +pp}:
          kh.smstep(sel, T.VWhen{a1}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlS{+pp}:
          kh.smstep(sel, T.VWhen{a1}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
    case T.VHead{+a1, +a2} <> +tt:
      match sel:
        case SlF{+nn}:
          kh.smstep(sel, T.VHead{a1, a2}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlA{+nn, +pp}:
          kh.smstep(sel, T.VHead{a1, a2}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlS{+pp}:
          kh.smstep(sel, T.VHead{a1, a2}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
    case T.VAots{+a1, +a2} <> +tt:
      match sel:
        case SlF{+nn}:
          kh.smstep(sel, T.VAots{a1, a2}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlA{+nn, +pp}:
          kh.smstep(sel, T.VAots{a1, a2}, tt, kk, {==}, kh.smapeq(tt, sel, kk))
        case SlS{+pp}:
          kh.smstep(sel, T.VAots{a1, a2}, tt, kk, {==}, kh.smapeq(tt, sel, kk))

# a reading of two lists, one value at a time: values read alike and rests
# read alike
def kh.mstep(
  +sel: KSel,
  +yy: T.Val,
  +xx: T.Val,
  +ys: List<&2, T.Val>,
  +xs: List<&2, T.Val>,
  +kk: String,
  +ee: {kh.el(sel, yy, kk) == kh.el(sel, xx, kk) : Bool},
  +ih: {kh.sl(sel, ys, kk) == kh.sl(sel, xs, kk) : Bool}
) -> {kh.sl(sel, yy <> ys, kk) == kh.sl(sel, xx <> xs, kk) : Bool}:
  Equal.trans(Bool, kh.sl(sel, yy <> ys, kk), kh.op(sel, kh.el(sel, yy, kk), kh.sl(sel, ys, kk)), kh.sl(sel, xx <>
    xs, kk), kh.slu(sel, yy, ys, kk),
    Equal.trans(Bool, kh.op(sel, kh.el(sel, yy, kk), kh.sl(sel, ys, kk)), kh.op(sel, kh.el(sel, xx, kk), kh.sl(sel,
      xs, kk)), kh.sl(sel, xx <> xs, kk), kh.opcong(sel, kh.el(sel, yy, kk), kh.sl(sel, ys, kk), kh.el(sel, xx,
        kk), kh.sl(sel, xs, kk), ee, ih),
      Equal.sym(Bool, kh.sl(sel, xx <> xs, kk), kh.op(sel, kh.el(sel, xx, kk), kh.sl(sel, xs, kk)), kh.slu(sel, xx,
        xs, kk))))

# rows an inline table closed hold a path as the rows do, given that for
# their values
def kh.hi(
  pp: List<&2, String>,
  +rr: List<&2, T.Val>,
  +kk: String,
  fF: @nm: String -> {kh.F(T.inl.seal(rr), nm) == kh.F(rr, nm) : Bool},
  fA: @nm: String -> @qq: List<&2, String> -> {kh.A(T.inl.seal(rr), nm, qq, kk) == kh.A(rr, nm, qq, kk) : Bool}
) -> {Laws.k3.has(T.inl.seal(rr), pp, kk) == Laws.k3.has(rr, pp, kk) : Bool}:
  match pp:
    case []:
      fF(kk)
    case +n2 <> +q2:
      bo.and.cong(kh.F(T.inl.seal(rr), n2), kh.A(T.inl.seal(rr), n2, q2, kk), kh.F(rr, n2), kh.A(rr, n2, q2,
        kk), fF(n2), fA(n2, q2))

# an inline table closed holds what its rows held, read any way
def kh.inleq(
  xs: List<&2, T.Val>,
  +sel: KSel,
  +kk: String
) -> {kh.sl(sel, T.inl.seal(xs), kk) == kh.sl(sel, xs, kk) : Bool}:
  match xs:
    case []:
      {==}
    case T.VPair{+mm, T.VHead{+qq, +rr}} <> +tt:
      match sel:
        case SlF{+nn}:
          kh.mstep(sel, T.VPair{mm, T.VInl{T.inl.seal(rr)}}, T.VPair{mm, T.VHead{qq, rr}}, T.inl.seal(tt), tt, kk,
            {==}, kh.inleq(tt, sel, kk))
        case SlA{+nn, +pp}:
          kh.mstep(sel, T.VPair{mm, T.VInl{T.inl.seal(rr)}}, T.VPair{mm, T.VHead{qq, rr}}, T.inl.seal(tt), tt, kk,
            bo.or.cong(Bool.not(T.str.eq(mm, nn)), Laws.k3.has(T.inl.seal(rr), pp, kk), Bool.not(T.str.eq(mm, nn)),
              Laws.k3.has(rr, pp, kk), {==}, kh.hi(pp, rr, kk, nm => kh.inleq(rr, SlF{nm}, kk),
                nm => qq2 => kh.inleq(rr, SlA{nm, qq2}, kk))), kh.inleq(tt, sel, kk))
        case SlS{+pp}:
          kh.mstep(sel, T.VPair{mm, T.VInl{T.inl.seal(rr)}}, T.VPair{mm, T.VHead{qq, rr}}, T.inl.seal(tt), tt, kk,
            {==}, kh.inleq(tt, sel, kk))
    case T.VPair{+mm, T.VStr{+a1}} <> +tt:
      kh.mstep(sel, T.VPair{mm, T.VStr{a1}}, T.VPair{mm, T.VStr{a1}}, T.inl.seal(tt), tt, kk, {==}, kh.inleq(tt, sel,
        kk))
    case T.VPair{+mm, T.VSpan{+a1, +a2}} <> +tt:
      kh.mstep(sel, T.VPair{mm, T.VSpan{a1, a2}}, T.VPair{mm, T.VSpan{a1, a2}}, T.inl.seal(tt), tt, kk, {==},
        kh.inleq(tt, sel, kk))
    case T.VPair{+mm, T.VInt{+a1, +a2}} <> +tt:
      kh.mstep(sel, T.VPair{mm, T.VInt{a1, a2}}, T.VPair{mm, T.VInt{a1, a2}}, T.inl.seal(tt), tt, kk, {==},
        kh.inleq(tt, sel, kk))
    case T.VPair{+mm, T.VFlo{+a1, +a2}} <> +tt:
      kh.mstep(sel, T.VPair{mm, T.VFlo{a1, a2}}, T.VPair{mm, T.VFlo{a1, a2}}, T.inl.seal(tt), tt, kk, {==},
        kh.inleq(tt, sel, kk))
    case T.VPair{+mm, T.VBool{+a1}} <> +tt:
      kh.mstep(sel, T.VPair{mm, T.VBool{a1}}, T.VPair{mm, T.VBool{a1}}, T.inl.seal(tt), tt, kk, {==}, kh.inleq(tt,
        sel, kk))
    case T.VPair{+mm, T.VWhen{+a1}} <> +tt:
      kh.mstep(sel, T.VPair{mm, T.VWhen{a1}}, T.VPair{mm, T.VWhen{a1}}, T.inl.seal(tt), tt, kk, {==}, kh.inleq(tt,
        sel, kk))
    case T.VPair{+mm, T.VArr{+a1}} <> +tt:
      kh.mstep(sel, T.VPair{mm, T.VArr{a1}}, T.VPair{mm, T.VArr{a1}}, T.inl.seal(tt), tt, kk, {==}, kh.inleq(tt, sel,
        kk))
    case T.VPair{+mm, T.VInl{+a1}} <> +tt:
      kh.mstep(sel, T.VPair{mm, T.VInl{a1}}, T.VPair{mm, T.VInl{a1}}, T.inl.seal(tt), tt, kk, {==}, kh.inleq(tt, sel,
        kk))
    case T.VPair{+mm, T.VAot{+a1, +a2}} <> +tt:
      kh.mstep(sel, T.VPair{mm, T.VAot{a1, a2}}, T.VPair{mm, T.VAot{a1, a2}}, T.inl.seal(tt), tt, kk, {==},
        kh.inleq(tt, sel, kk))
    case T.VPair{+mm, T.VAots{+a1, +a2}} <> +tt:
      kh.mstep(sel, T.VPair{mm, T.VAots{a1, a2}}, T.VPair{mm, T.VAots{a1, a2}}, T.inl.seal(tt), tt, kk, {==},
        kh.inleq(tt, sel, kk))
    case T.VPair{+mm, T.VPair{+a1, +a2}} <> +tt:
      kh.mstep(sel, T.VPair{mm, T.VPair{a1, a2}}, T.VPair{mm, T.VPair{a1, a2}}, T.inl.seal(tt), tt, kk, {==},
        kh.inleq(tt, sel, kk))
    case T.VStr{+a1} <> +tt:
      kh.mstep(sel, T.VStr{a1}, T.VStr{a1}, T.inl.seal(tt), tt, kk, {==}, kh.inleq(tt, sel, kk))
    case T.VSpan{+a1, +a2} <> +tt:
      kh.mstep(sel, T.VSpan{a1, a2}, T.VSpan{a1, a2}, T.inl.seal(tt), tt, kk, {==}, kh.inleq(tt, sel, kk))
    case T.VInt{+a1, +a2} <> +tt:
      kh.mstep(sel, T.VInt{a1, a2}, T.VInt{a1, a2}, T.inl.seal(tt), tt, kk, {==}, kh.inleq(tt, sel, kk))
    case T.VFlo{+a1, +a2} <> +tt:
      kh.mstep(sel, T.VFlo{a1, a2}, T.VFlo{a1, a2}, T.inl.seal(tt), tt, kk, {==}, kh.inleq(tt, sel, kk))
    case T.VBool{+a1} <> +tt:
      kh.mstep(sel, T.VBool{a1}, T.VBool{a1}, T.inl.seal(tt), tt, kk, {==}, kh.inleq(tt, sel, kk))
    case T.VWhen{+a1} <> +tt:
      kh.mstep(sel, T.VWhen{a1}, T.VWhen{a1}, T.inl.seal(tt), tt, kk, {==}, kh.inleq(tt, sel, kk))
    case T.VArr{+a1} <> +tt:
      kh.mstep(sel, T.VArr{a1}, T.VArr{a1}, T.inl.seal(tt), tt, kk, {==}, kh.inleq(tt, sel, kk))
    case T.VInl{+a1} <> +tt:
      kh.mstep(sel, T.VInl{a1}, T.VInl{a1}, T.inl.seal(tt), tt, kk, {==}, kh.inleq(tt, sel, kk))
    case T.VHead{+a1, +a2} <> +tt:
      kh.mstep(sel, T.VHead{a1, a2}, T.VHead{a1, a2}, T.inl.seal(tt), tt, kk, {==}, kh.inleq(tt, sel, kk))
    case T.VAot{+a1, +a2} <> +tt:
      kh.mstep(sel, T.VAot{a1, a2}, T.VAot{a1, a2}, T.inl.seal(tt), tt, kk, {==}, kh.inleq(tt, sel, kk))
    case T.VAots{+a1, +a2} <> +tt:
      kh.mstep(sel, T.VAots{a1, a2}, T.VAots{a1, a2}, T.inl.seal(tt), tt, kk, {==}, kh.inleq(tt, sel, kk))

# an or that answered False: its left half did
def bo.or.fl(aa: Bool, bb: Bool, +ee: {Bool.or(aa, bb) == False{} : Bool}) -> {aa == False{} : Bool}:
  match aa:
    case True{}:
      Eq.bit.absurd2(&2, {True{} == False{} : Bool}, ee)
    case False{}:
      {==}

# and its right half did
def bo.or.fr(aa: Bool, bb: Bool, +ee: {Bool.or(aa, bb) == False{} : Bool}) -> {bb == False{} : Bool}:
  match aa:
    case True{}:
      Eq.bit.absurd2(&2, {bb == False{} : Bool}, ee)
    case False{}:
      ee

# an or whose right half answered True
def bo.or.tr(aa: Bool, bb: Bool, +ee: {bb == True{} : Bool}) -> {Bool.or(aa, bb) == True{} : Bool}:
  match aa:
    case True{}:
      {==}
    case False{}:
      ee

# an or whose left half answered True
def bo.or.tl(aa: Bool, bb: Bool, +ee: {aa == True{} : Bool}) -> {Bool.or(aa, bb) == True{} : Bool}:
  match aa:
    case True{}:
      {==}
    case False{}:
      Eq.bit.absurd(&2, {Bool.or(False{}, bb) == True{} : Bool}, ee)

# a Bool that answered True, rewritten
def bo.t(aa: Bool, bb: Bool, +ee: {aa == bb : Bool}, +et: {bb == True{} : Bool}) -> {aa == True{} : Bool}:
  Equal.trans(Bool, aa, bb, True{}, ee, et)

# a value that is no pair of the name holds any path for it
def kh.eA.nf(
  +xx: T.Val,
  +nn: String,
  +pp: List<&2, String>,
  +kk: String,
  +ee: {kh.eF(xx, nn) == False{} : Bool}
) -> {kh.eA(xx, nn, pp, kk) == True{} : Bool}:
  match xx:
    case T.VPair{+mm, +vv}:
      %Equal.sym(Bool, T.str.eq(mm, nn), False{}, ee) : {Bool.or(Bool.not(_), kh.hv(vv, pp, kk)) == True{} : Bool}
      {==}
    case T.VStr{_a}:
      {==}
    case T.VSpan{_a, _b}:
      {==}
    case T.VInt{_a, _b}:
      {==}
    case T.VFlo{_a, _b}:
      {==}
    case T.VBool{_a}:
      {==}
    case T.VWhen{_a}:
      {==}
    case T.VArr{_a}:
      {==}
    case T.VInl{_a}:
      {==}
    case T.VHead{_a, _b}:
      {==}
    case T.VAot{_a, _b}:
      {==}
    case T.VAots{_a, _b}:
      {==}

# a name not found in rows, one value at a time
def kh.uF.f(
  +xx: T.Val,
  +tt: List<&2, T.Val>,
  +nn: String,
  +em: {kh.F(xx <> tt, nn) == False{} : Bool}
) -> {Bool.or(kh.eF(xx, nn), kh.F(tt, nn)) == False{} : Bool}:
  Equal.trans(Bool, Bool.or(kh.eF(xx, nn), kh.F(tt, nn)), kh.F(xx <> tt, nn), False{}, Equal.sym(Bool, kh.F(xx <>
    tt, nn), Bool.or(kh.eF(xx, nn), kh.F(tt, nn)), kh.uF(xx, tt, nn)), em)

# rows with no pair of a name hold any path through it for the pairs of it
def kh.A.miss(
  xs: List<&2, T.Val>,
  +nn: String,
  +pp: List<&2, String>,
  +kk: String,
  +em: {kh.F(xs, nn) == False{} : Bool}
) -> {kh.A(xs, nn, pp, kk) == True{} : Bool}:
  match xs:
    case []:
      {==}
    case +xx <> +tt:
      bo.t(kh.A(xx <> tt, nn, pp, kk), Bool.and(kh.eA(xx, nn, pp, kk), kh.A(tt, nn, pp, kk)), kh.uA(xx, pp, tt, nn,
        kk), M17.gd.tt(kh.eA(xx, nn, pp, kk), kh.A(tt, nn, pp, kk), kh.eA.nf(xx, nn, pp, kk, bo.or.fl(kh.eF(xx, nn),
          kh.F(tt, nn), kh.uF.f(xx, tt, nn, em))), kh.A.miss(tt, nn, pp, kk, bo.or.fr(kh.eF(xx, nn), kh.F(tt, nn),
            kh.uF.f(xx, tt, nn, em)))))

# every path the first rows hold, the second hold too
def kh.Ext(_xs: List<&2, T.Val>, _ys: List<&2, T.Val>, +_kk: String) -> Type:
  @pp: List<&2, String> -> {Laws.k3.has(_xs, pp, _kk) == True{} : Bool} -> {Laws.k3.has(_ys, pp, _kk) == True{} : Bool}

# a name found in rows is not one missing from them
def kh.neq(
  nn: String,
  mm: String,
  +vs: List<&2, T.Val>,
  bb: Bool,
  +ee: {T.str.eq(nn, mm) == bb : Bool},
  +em: {kh.F(vs, nn) == False{} : Bool},
  +ef: {kh.F(vs, mm) == True{} : Bool}
) -> {bb == False{} : Bool}:
  match bb:
    case True{}:
      Eq.bit.absurd(&2, {True{} == False{} : Bool}, Equal.trans(Bool, False{}, kh.F(vs, nn), True{}, Equal.sym(Bool,
        kh.F(vs, nn), False{}, em), Equal.trans(Bool, kh.F(vs, nn), kh.F(vs, mm), True{}, Equal.cong(String, Bool,
          zz => kh.F(vs, zz), nn, mm, M2.str.eq.true(nn, mm, ee)), ef)))
    case False{}:
      {==}

# a pair put in front of rows that had no pair of its name keeps every path
# they held
def kh.fresh.go(
  pp: List<&2, String>,
  +nn: String,
  +vv: T.Val,
  +vs: List<&2, T.Val>,
  +kk: String,
  +em: {kh.F(vs, nn) == False{} : Bool},
  +eh: {Laws.k3.has(vs, pp, kk) == True{} : Bool}
) -> {Laws.k3.has(T.VPair{nn, vv} <> vs, pp, kk) == True{} : Bool}:
  match pp:
    case []:
      bo.t(kh.F(T.VPair{nn, vv} <> vs, kk), Bool.or(kh.eF(T.VPair{nn, vv}, kk), kh.F(vs, kk)), kh.uF(T.VPair{nn, vv},
        vs, kk), bo.or.tr(kh.eF(T.VPair{nn, vv}, kk), kh.F(vs, kk), eh))
    case +mm <> +qq:
      M17.gd.tt(kh.F(T.VPair{nn, vv} <> vs, mm), kh.A(T.VPair{nn, vv} <> vs, mm, qq, kk),
        bo.t(kh.F(T.VPair{nn, vv} <> vs, mm), Bool.or(kh.eF(T.VPair{nn, vv}, mm), kh.F(vs, mm)), kh.uF(T.VPair{nn,
          vv}, vs, mm), bo.or.tr(kh.eF(T.VPair{nn, vv}, mm), kh.F(vs, mm), M17.gd.l(kh.F(vs, mm), kh.A(vs, mm, qq, kk),
            eh))),
        bo.t(kh.A(T.VPair{nn, vv} <> vs, mm, qq, kk), Bool.and(kh.eA(T.VPair{nn, vv}, mm, qq, kk), kh.A(vs, mm, qq,
          kk)), kh.uA(T.VPair{nn, vv}, qq, vs, mm, kk), M17.gd.tt(kh.eA(T.VPair{nn, vv}, mm, qq, kk), kh.A(vs, mm, qq,
            kk), kh.eA.nf(T.VPair{nn, vv}, mm, qq, kk, kh.neq(nn, mm, vs, T.str.eq(nn, mm), {==}, em, M17.gd.l(kh.F(vs,
              mm), kh.A(vs, mm, qq, kk), eh))), M17.gd.r(kh.F(vs, mm), kh.A(vs, mm, qq, kk), eh))))

# and so as a promise for every path
def kh.fresh(
  +nn: String,
  +vv: T.Val,
  +vs: List<&2, T.Val>,
  +kk: String,
  +em: {kh.F(vs, nn) == False{} : Bool}
) -> kh.Ext(vs, T.VPair{nn, vv} <> vs, kk):
  pp => eh => kh.fresh.go(pp, nn, vv, vs, kk, em, eh)

# a pair of the name, with a value that holds the path, holds it
def kh.eA.same(
  mm: String,
  +nn: String,
  +vv: T.Val,
  +pp: List<&2, String>,
  +kk: String,
  +ee: {T.str.eq(mm, nn) == True{} : Bool},
  +ev: {kh.hv(vv, pp, kk) == True{} : Bool}
) -> {kh.eA(T.VPair{mm, vv}, nn, pp, kk) == True{} : Bool}:
  %Equal.sym(Bool, T.str.eq(mm, nn), True{}, ee) : {Bool.or(Bool.not(_), kh.hv(vv, pp, kk)) == True{} : Bool}
  ev

# a pair put in front of rows that had no pair of its name is found there
def kh.mk0(+nn: String, +vv: T.Val, +vs: List<&2, T.Val>) -> {kh.F(T.VPair{nn, vv} <> vs, nn) == True{} : Bool}:
  bo.t(kh.F(T.VPair{nn, vv} <> vs, nn), Bool.or(T.str.eq(nn, nn), kh.F(vs, nn)), kh.uF(T.VPair{nn, vv}, vs, nn),
    bo.or.tl(T.str.eq(nn, nn), kh.F(vs, nn), M15.str.eq.self(nn)))

# and holds, through its name, every path its value holds
def kh.mk(
  +nn: String,
  +vv: T.Val,
  +vs: List<&2, T.Val>,
  +pp: List<&2, String>,
  +kk: String,
  +em: {kh.F(vs, nn) == False{} : Bool},
  +ev: {kh.hv(vv, pp, kk) == True{} : Bool}
) -> {Laws.k3.has(T.VPair{nn, vv} <> vs, nn <> pp, kk) == True{} : Bool}:
  M17.gd.tt(kh.F(T.VPair{nn, vv} <> vs, nn), kh.A(T.VPair{nn, vv} <> vs, nn, pp, kk), kh.mk0(nn, vv, vs),
    bo.t(kh.A(T.VPair{nn, vv} <> vs, nn, pp, kk), Bool.and(kh.eA(T.VPair{nn, vv}, nn, pp, kk), kh.A(vs, nn, pp,
      kk)), kh.uA(T.VPair{nn, vv}, pp, vs, nn, kk), M17.gd.tt(kh.eA(T.VPair{nn, vv}, nn, pp, kk), kh.A(vs, nn, pp, kk),
        kh.eA.same(nn, nn, vv, pp, kk, M15.str.eq.self(nn), ev), kh.A.miss(vs, nn, pp, kk, em))))

# the value of a pair to be replaced
def kh.hitv(hh: T.Hit) -> T.Val:
  match hh:
    case T.Found{vv}:
      vv
    case T.Miss{}:
      T.VBool{False{}}

# what rows.look finds is what get finds, as a Look
def kh.lk(hh: T.Hit) -> T.Look:
  match hh:
    case T.Found{vv}:
      T.look.of(vv)
    case T.Miss{}:
      T.KMiss{}

# one pair of the look
def kh.look.st(
  bb: Bool,
  +vv: T.Val,
  +tt: List<&2, T.Val>,
  +aa: String,
  +ih: {T.rows.look(tt, aa) == kh.lk(T.rows.find(tt, aa)) : T.Look}
) -> {T.look.step(bb, vv, _u => T.rows.look(tt, aa)) == kh.lk(T.find.step(bb, vv, _u => T.rows.find(tt, aa)))
  : T.Look}:
  match bb:
    case True{}:
      {==}
    case False{}:
      ih

# rows.look finds the pair get finds
def kh.look(xs: List<&2, T.Val>, +aa: String) -> {T.rows.look(xs, aa) == kh.lk(T.rows.find(xs, aa)) : T.Look}:
  match xs:
    case []:
      {==}
    case T.VPair{+mm, +vv} <> +tt:
      kh.look.st(T.str.eq(mm, aa), vv, tt, aa, kh.look(tt, aa))
    case T.VStr{+a1} <> +tt:
      kh.look(tt, aa)
    case T.VSpan{+a1, +a2} <> +tt:
      kh.look(tt, aa)
    case T.VInt{+a1, +a2} <> +tt:
      kh.look(tt, aa)
    case T.VFlo{+a1, +a2} <> +tt:
      kh.look(tt, aa)
    case T.VBool{+a1} <> +tt:
      kh.look(tt, aa)
    case T.VWhen{+a1} <> +tt:
      kh.look(tt, aa)
    case T.VArr{+a1} <> +tt:
      kh.look(tt, aa)
    case T.VInl{+a1} <> +tt:
      kh.look(tt, aa)
    case T.VHead{+a1, +a2} <> +tt:
      kh.look(tt, aa)
    case T.VAot{+a1, +a2} <> +tt:
      kh.look(tt, aa)
    case T.VAots{+a1, +a2} <> +tt:
      kh.look(tt, aa)

# one pair of a replacement: a name get finds is found after it
def kh.rF.st(
  bb: Bool,
  +mm: String,
  +old: T.Val,
  +vv: T.Val,
  +tt: List<&2, T.Val>,
  +aa: String,
  +nn: String,
  +ih: {kh.F(T.rows.repl(tt, aa, vv), nn) == kh.F(tt, nn) : Bool}
) -> {kh.F(T.rows.repl.step(bb, mm, old, vv, _u => T.rows.repl(tt, aa, vv)), nn) == kh.F(T.VPair{mm, old} <> tt,
  nn) : Bool}:
  match bb:
    case True{}:
      kh.mstep(SlF{nn}, T.VPair{mm, vv}, T.VPair{mm, old}, T.rows.repl(tt, aa, vv), tt, nn, {==}, ih)
    case False{}:
      kh.mstep(SlF{nn}, T.VPair{mm, old}, T.VPair{mm, old}, T.rows.repl(tt, aa, vv), tt, nn, {==}, ih)

# a replacement keeps every name found
def kh.rF(
  xs: List<&2, T.Val>,
  +aa: String,
  +vv: T.Val,
  +nn: String
) -> {kh.F(T.rows.repl(xs, aa, vv), nn) == kh.F(xs, nn) : Bool}:
  match xs:
    case []:
      {==}
    case T.VPair{+mm, +old} <> +tt:
      kh.rF.st(T.str.eq(mm, aa), mm, old, vv, tt, aa, nn, kh.rF(tt, aa, vv, nn))
    case T.VStr{+a1} <> +tt:
      kh.mstep(SlF{nn}, T.VStr{a1}, T.VStr{a1}, T.rows.repl(tt, aa, vv), tt, nn, {==}, kh.rF(tt, aa, vv, nn))
    case T.VSpan{+a1, +a2} <> +tt:
      kh.mstep(SlF{nn}, T.VSpan{a1, a2}, T.VSpan{a1, a2}, T.rows.repl(tt, aa, vv), tt, nn, {==}, kh.rF(tt, aa, vv, nn))
    case T.VInt{+a1, +a2} <> +tt:
      kh.mstep(SlF{nn}, T.VInt{a1, a2}, T.VInt{a1, a2}, T.rows.repl(tt, aa, vv), tt, nn, {==}, kh.rF(tt, aa, vv, nn))
    case T.VFlo{+a1, +a2} <> +tt:
      kh.mstep(SlF{nn}, T.VFlo{a1, a2}, T.VFlo{a1, a2}, T.rows.repl(tt, aa, vv), tt, nn, {==}, kh.rF(tt, aa, vv, nn))
    case T.VBool{+a1} <> +tt:
      kh.mstep(SlF{nn}, T.VBool{a1}, T.VBool{a1}, T.rows.repl(tt, aa, vv), tt, nn, {==}, kh.rF(tt, aa, vv, nn))
    case T.VWhen{+a1} <> +tt:
      kh.mstep(SlF{nn}, T.VWhen{a1}, T.VWhen{a1}, T.rows.repl(tt, aa, vv), tt, nn, {==}, kh.rF(tt, aa, vv, nn))
    case T.VArr{+a1} <> +tt:
      kh.mstep(SlF{nn}, T.VArr{a1}, T.VArr{a1}, T.rows.repl(tt, aa, vv), tt, nn, {==}, kh.rF(tt, aa, vv, nn))
    case T.VInl{+a1} <> +tt:
      kh.mstep(SlF{nn}, T.VInl{a1}, T.VInl{a1}, T.rows.repl(tt, aa, vv), tt, nn, {==}, kh.rF(tt, aa, vv, nn))
    case T.VHead{+a1, +a2} <> +tt:
      kh.mstep(SlF{nn}, T.VHead{a1, a2}, T.VHead{a1, a2}, T.rows.repl(tt, aa, vv), tt, nn, {==}, kh.rF(tt, aa, vv, nn))
    case T.VAot{+a1, +a2} <> +tt:
      kh.mstep(SlF{nn}, T.VAot{a1, a2}, T.VAot{a1, a2}, T.rows.repl(tt, aa, vv), tt, nn, {==}, kh.rF(tt, aa, vv, nn))
    case T.VAots{+a1, +a2} <> +tt:
      kh.mstep(SlF{nn}, T.VAots{a1, a2}, T.VAots{a1, a2}, T.rows.repl(tt, aa, vv), tt, nn, {==}, kh.rF(tt, aa, vv, nn))

# a pair of the replaced name is no pair of another name
def kh.ne.rep(
  mm: String,
  aa: String,
  nn: String,
  +em: {T.str.eq(mm, aa) == True{} : Bool},
  +ea: {T.str.eq(aa, nn) == False{} : Bool}
) -> {T.str.eq(mm, nn) == False{} : Bool}:
  %Equal.sym(String, mm, aa, M2.str.eq.true(mm, aa, em)) : {T.str.eq(_, nn) == False{} : Bool}
  ea

# one pair of a replacement, read for another name
def kh.rA.st(
  bb: Bool,
  +mm: String,
  +old: T.Val,
  +vv: T.Val,
  +tt: List<&2, T.Val>,
  +aa: String,
  +nn: String,
  +qq: List<&2, String>,
  +kk: String,
  +eb: {T.str.eq(mm, aa) == bb : Bool},
  +ea: {T.str.eq(aa, nn) == False{} : Bool},
  +ih: {kh.A(T.rows.repl(tt, aa, vv), nn, qq, kk) == kh.A(tt, nn, qq, kk) : Bool}
) -> {kh.A(T.rows.repl.step(bb, mm, old, vv, _u => T.rows.repl(tt, aa, vv)), nn, qq, kk) == kh.A(T.VPair{mm, old}
  <> tt, nn, qq, kk) : Bool}:
  match bb:
    case True{}:
      kh.mstep(SlA{nn, qq}, T.VPair{mm, vv}, T.VPair{mm, old}, T.rows.repl(tt, aa, vv), tt, kk,
        Equal.trans(Bool, kh.eA(T.VPair{mm, vv}, nn, qq, kk), True{}, kh.eA(T.VPair{mm, old}, nn, qq, kk),
          kh.eA.nf(T.VPair{mm, vv}, nn, qq, kk, kh.ne.rep(mm, aa, nn, eb, ea)), Equal.sym(Bool, kh.eA(T.VPair{mm,
            old}, nn, qq, kk), True{}, kh.eA.nf(T.VPair{mm, old}, nn, qq, kk, kh.ne.rep(mm, aa, nn, eb, ea)))), ih)
    case False{}:
      kh.mstep(SlA{nn, qq}, T.VPair{mm, old}, T.VPair{mm, old}, T.rows.repl(tt, aa, vv), tt, kk, {==}, ih)

# a replacement keeps what the rows seen for another name hold
def kh.rA.o(
  xs: List<&2, T.Val>,
  +aa: String,
  +vv: T.Val,
  +nn: String,
  +qq: List<&2, String>,
  +kk: String,
  +ea: {T.str.eq(aa, nn) == False{} : Bool}
) -> {kh.A(T.rows.repl(xs, aa, vv), nn, qq, kk) == kh.A(xs, nn, qq, kk) : Bool}:
  match xs:
    case []:
      {==}
    case T.VPair{+mm, +old} <> +tt:
      kh.rA.st(T.str.eq(mm, aa), mm, old, vv, tt, aa, nn, qq, kk, {==}, ea, kh.rA.o(tt, aa, vv, nn, qq, kk, ea))
    case T.VStr{+a1} <> +tt:
      kh.mstep(SlA{nn, qq}, T.VStr{a1}, T.VStr{a1}, T.rows.repl(tt, aa, vv), tt, kk, {==}, kh.rA.o(tt, aa, vv, nn, qq,
        kk, ea))
    case T.VSpan{+a1, +a2} <> +tt:
      kh.mstep(SlA{nn, qq}, T.VSpan{a1, a2}, T.VSpan{a1, a2}, T.rows.repl(tt, aa, vv), tt, kk, {==}, kh.rA.o(tt, aa,
        vv, nn, qq, kk, ea))
    case T.VInt{+a1, +a2} <> +tt:
      kh.mstep(SlA{nn, qq}, T.VInt{a1, a2}, T.VInt{a1, a2}, T.rows.repl(tt, aa, vv), tt, kk, {==}, kh.rA.o(tt, aa, vv,
        nn, qq, kk, ea))
    case T.VFlo{+a1, +a2} <> +tt:
      kh.mstep(SlA{nn, qq}, T.VFlo{a1, a2}, T.VFlo{a1, a2}, T.rows.repl(tt, aa, vv), tt, kk, {==}, kh.rA.o(tt, aa, vv,
        nn, qq, kk, ea))
    case T.VBool{+a1} <> +tt:
      kh.mstep(SlA{nn, qq}, T.VBool{a1}, T.VBool{a1}, T.rows.repl(tt, aa, vv), tt, kk, {==}, kh.rA.o(tt, aa, vv, nn,
        qq, kk, ea))
    case T.VWhen{+a1} <> +tt:
      kh.mstep(SlA{nn, qq}, T.VWhen{a1}, T.VWhen{a1}, T.rows.repl(tt, aa, vv), tt, kk, {==}, kh.rA.o(tt, aa, vv, nn,
        qq, kk, ea))
    case T.VArr{+a1} <> +tt:
      kh.mstep(SlA{nn, qq}, T.VArr{a1}, T.VArr{a1}, T.rows.repl(tt, aa, vv), tt, kk, {==}, kh.rA.o(tt, aa, vv, nn, qq,
        kk, ea))
    case T.VInl{+a1} <> +tt:
      kh.mstep(SlA{nn, qq}, T.VInl{a1}, T.VInl{a1}, T.rows.repl(tt, aa, vv), tt, kk, {==}, kh.rA.o(tt, aa, vv, nn, qq,
        kk, ea))
    case T.VHead{+a1, +a2} <> +tt:
      kh.mstep(SlA{nn, qq}, T.VHead{a1, a2}, T.VHead{a1, a2}, T.rows.repl(tt, aa, vv), tt, kk, {==}, kh.rA.o(tt, aa,
        vv, nn, qq, kk, ea))
    case T.VAot{+a1, +a2} <> +tt:
      kh.mstep(SlA{nn, qq}, T.VAot{a1, a2}, T.VAot{a1, a2}, T.rows.repl(tt, aa, vv), tt, kk, {==}, kh.rA.o(tt, aa, vv,
        nn, qq, kk, ea))
    case T.VAots{+a1, +a2} <> +tt:
      kh.mstep(SlA{nn, qq}, T.VAots{a1, a2}, T.VAots{a1, a2}, T.rows.repl(tt, aa, vv), tt, kk, {==}, kh.rA.o(tt, aa,
        vv, nn, qq, kk, ea))

# one pair of a replacement, read for its own name
def kh.rS.st(
  bb: Bool,
  +mm: String,
  +old: T.Val,
  +vv: T.Val,
  +tt: List<&2, T.Val>,
  +aa: String,
  +qq: List<&2, String>,
  +kk: String,
  +eb: {T.str.eq(mm, aa) == bb : Bool},
  +ev: {kh.hv(vv, qq, kk) == True{} : Bool},
  +ih: {kh.A(T.rows.repl(tt, aa, vv), aa, qq, kk) == True{} : Bool}
) -> {kh.A(T.rows.repl.step(bb, mm, old, vv, _u => T.rows.repl(tt, aa, vv)), aa, qq, kk) == True{} : Bool}:
  match bb:
    case True{}:
      bo.t(kh.A(T.VPair{mm, vv} <> T.rows.repl(tt, aa, vv), aa, qq, kk), Bool.and(kh.eA(T.VPair{mm, vv}, aa, qq,
        kk), kh.A(T.rows.repl(tt, aa, vv), aa, qq, kk)), kh.uA(T.VPair{mm, vv}, qq, T.rows.repl(tt, aa, vv), aa, kk),
        M17.gd.tt(kh.eA(T.VPair{mm, vv}, aa, qq, kk), kh.A(T.rows.repl(tt, aa, vv), aa, qq, kk), kh.eA.same(mm, aa, vv,
          qq, kk, eb, ev), ih))
    case False{}:
      bo.t(kh.A(T.VPair{mm, old} <> T.rows.repl(tt, aa, vv), aa, qq, kk), Bool.and(kh.eA(T.VPair{mm, old}, aa, qq,
        kk), kh.A(T.rows.repl(tt, aa, vv), aa, qq, kk)), kh.uA(T.VPair{mm, old}, qq, T.rows.repl(tt, aa, vv), aa,
          kk), M17.gd.tt(kh.eA(T.VPair{mm, old}, aa, qq, kk), kh.A(T.rows.repl(tt, aa, vv), aa, qq, kk),
            kh.eA.nf(T.VPair{mm,
            old}, aa, qq, kk, eb), ih))

# every pair of the replaced name holds what the new value holds
def kh.rA.s(
  xs: List<&2, T.Val>,
  +aa: String,
  +vv: T.Val,
  +qq: List<&2, String>,
  +kk: String,
  +ev: {kh.hv(vv, qq, kk) == True{} : Bool}
) -> {kh.A(T.rows.repl(xs, aa, vv), aa, qq, kk) == True{} : Bool}:
  match xs:
    case []:
      {==}
    case T.VPair{+mm, +old} <> +tt:
      kh.rS.st(T.str.eq(mm, aa), mm, old, vv, tt, aa, qq, kk, {==}, ev, kh.rA.s(tt, aa, vv, qq, kk, ev))
    case T.VStr{+a1} <> +tt:
      bo.t(kh.A(T.VStr{a1} <> T.rows.repl(tt, aa, vv), aa, qq, kk), Bool.and(True{}, kh.A(T.rows.repl(tt, aa, vv), aa,
        qq, kk)), kh.uA(T.VStr{a1}, qq, T.rows.repl(tt, aa, vv), aa, kk), kh.rA.s(tt, aa, vv, qq, kk, ev))
    case T.VSpan{+a1, +a2} <> +tt:
      bo.t(kh.A(T.VSpan{a1, a2} <> T.rows.repl(tt, aa, vv), aa, qq, kk), Bool.and(True{}, kh.A(T.rows.repl(tt, aa,
        vv), aa, qq, kk)), kh.uA(T.VSpan{a1, a2}, qq, T.rows.repl(tt, aa, vv), aa, kk), kh.rA.s(tt, aa, vv, qq, kk, ev))
    case T.VInt{+a1, +a2} <> +tt:
      bo.t(kh.A(T.VInt{a1, a2} <> T.rows.repl(tt, aa, vv), aa, qq, kk), Bool.and(True{}, kh.A(T.rows.repl(tt, aa, vv),
        aa, qq, kk)), kh.uA(T.VInt{a1, a2}, qq, T.rows.repl(tt, aa, vv), aa, kk), kh.rA.s(tt, aa, vv, qq, kk, ev))
    case T.VFlo{+a1, +a2} <> +tt:
      bo.t(kh.A(T.VFlo{a1, a2} <> T.rows.repl(tt, aa, vv), aa, qq, kk), Bool.and(True{}, kh.A(T.rows.repl(tt, aa, vv),
        aa, qq, kk)), kh.uA(T.VFlo{a1, a2}, qq, T.rows.repl(tt, aa, vv), aa, kk), kh.rA.s(tt, aa, vv, qq, kk, ev))
    case T.VBool{+a1} <> +tt:
      bo.t(kh.A(T.VBool{a1} <> T.rows.repl(tt, aa, vv), aa, qq, kk), Bool.and(True{}, kh.A(T.rows.repl(tt, aa, vv),
        aa, qq, kk)), kh.uA(T.VBool{a1}, qq, T.rows.repl(tt, aa, vv), aa, kk), kh.rA.s(tt, aa, vv, qq, kk, ev))
    case T.VWhen{+a1} <> +tt:
      bo.t(kh.A(T.VWhen{a1} <> T.rows.repl(tt, aa, vv), aa, qq, kk), Bool.and(True{}, kh.A(T.rows.repl(tt, aa, vv),
        aa, qq, kk)), kh.uA(T.VWhen{a1}, qq, T.rows.repl(tt, aa, vv), aa, kk), kh.rA.s(tt, aa, vv, qq, kk, ev))
    case T.VArr{+a1} <> +tt:
      bo.t(kh.A(T.VArr{a1} <> T.rows.repl(tt, aa, vv), aa, qq, kk), Bool.and(True{}, kh.A(T.rows.repl(tt, aa, vv), aa,
        qq, kk)), kh.uA(T.VArr{a1}, qq, T.rows.repl(tt, aa, vv), aa, kk), kh.rA.s(tt, aa, vv, qq, kk, ev))
    case T.VInl{+a1} <> +tt:
      bo.t(kh.A(T.VInl{a1} <> T.rows.repl(tt, aa, vv), aa, qq, kk), Bool.and(True{}, kh.A(T.rows.repl(tt, aa, vv), aa,
        qq, kk)), kh.uA(T.VInl{a1}, qq, T.rows.repl(tt, aa, vv), aa, kk), kh.rA.s(tt, aa, vv, qq, kk, ev))
    case T.VHead{+a1, +a2} <> +tt:
      bo.t(kh.A(T.VHead{a1, a2} <> T.rows.repl(tt, aa, vv), aa, qq, kk), Bool.and(True{}, kh.A(T.rows.repl(tt, aa,
        vv), aa, qq, kk)), kh.uA(T.VHead{a1, a2}, qq, T.rows.repl(tt, aa, vv), aa, kk), kh.rA.s(tt, aa, vv, qq, kk, ev))
    case T.VAot{+a1, +a2} <> +tt:
      bo.t(kh.A(T.VAot{a1, a2} <> T.rows.repl(tt, aa, vv), aa, qq, kk), Bool.and(True{}, kh.A(T.rows.repl(tt, aa, vv),
        aa, qq, kk)), kh.uA(T.VAot{a1, a2}, qq, T.rows.repl(tt, aa, vv), aa, kk), kh.rA.s(tt, aa, vv, qq, kk, ev))
    case T.VAots{+a1, +a2} <> +tt:
      bo.t(kh.A(T.VAots{a1, a2} <> T.rows.repl(tt, aa, vv), aa, qq, kk), Bool.and(True{}, kh.A(T.rows.repl(tt, aa,
        vv), aa, qq, kk)), kh.uA(T.VAots{a1, a2}, qq, T.rows.repl(tt, aa, vv), aa, kk), kh.rA.s(tt, aa, vv, qq, kk, ev))

# a pair of the name that holds a path: its value does
def kh.eA.get(
  mm: String,
  aa: String,
  +vv: T.Val,
  +qq: List<&2, String>,
  +kk: String,
  +eb: {T.str.eq(mm, aa) == True{} : Bool},
  +ee: {kh.eA(T.VPair{mm, vv}, aa, qq, kk) == True{} : Bool}
) -> {kh.hv(vv, qq, kk) == True{} : Bool}:
  Equal.trans(Bool, kh.hv(vv, qq, kk), kh.eA(T.VPair{mm, vv}, aa, qq, kk), True{}, Equal.sym(Bool,
    kh.eA(T.VPair{mm, vv}, aa, qq, kk), kh.hv(vv, qq, kk), Equal.cong(Bool, Bool, zz => Bool.or(Bool.not(zz),
      kh.hv(vv, qq, kk)), T.str.eq(mm, aa), True{}, eb)), ee)

# the first pair's search in the rest of the rows
def kh.FirstIH(
  _tt: List<&2, T.Val>,
  +_aa: String,
  _ww: T.Val,
  +_qq: List<&2, String>,
  +_kk: String
) -> Type:
  @e1: {T.rows.find(_tt, _aa) == T.Found{_ww} : T.Hit} -> @e2: {kh.A(_tt, _aa, _qq, _kk) == True{} : Bool} ->
    {kh.hv(_ww, _qq, _kk) == True{} : Bool}

# one pair of the first pair's search
def kh.first.st(
  bb: Bool,
  +mm: String,
  +old: T.Val,
  +tt: List<&2, T.Val>,
  +aa: String,
  +ww: T.Val,
  +qq: List<&2, String>,
  +kk: String,
  +eb: {T.str.eq(mm, aa) == bb : Bool},
  +ef: {T.find.step(bb, old, _u => T.rows.find(tt, aa)) == T.Found{ww} : T.Hit},
  +ea: {Bool.and(kh.eA(T.VPair{mm, old}, aa, qq, kk), kh.A(tt, aa, qq, kk)) == True{} : Bool},
  ih: kh.FirstIH(tt, aa, ww, qq, kk)
) -> {kh.hv(ww, qq, kk) == True{} : Bool}:
  match bb:
    case True{}:
      %Equal.cong(T.Hit, T.Val, hh => kh.hitv(hh), T.Found{old}, T.Found{ww}, ef) :
        {kh.hv(_, qq, kk) == True{} : Bool}
      kh.eA.get(mm, aa, old, qq, kk, eb, M17.gd.l(kh.eA(T.VPair{mm, old}, aa, qq, kk), kh.A(tt, aa, qq, kk), ea))
    case False{}:
      ih(ef, M17.gd.r(kh.eA(T.VPair{mm, old}, aa, qq, kk), kh.A(tt, aa, qq, kk), ea))

# whether a lookup found something, as False for a miss
def kh.isf(hh: T.Hit) -> Bool:
  match hh:
    case T.Found{_v}:
      True{}
    case T.Miss{}:
      False{}

# the first pair of a name, when every pair of it holds a path, holds it
def kh.first(
  xs: List<&2, T.Val>,
  +aa: String,
  +ww: T.Val,
  +qq: List<&2, String>,
  +kk: String,
  +ef: {T.rows.find(xs, aa) == T.Found{ww} : T.Hit},
  +ea: {kh.A(xs, aa, qq, kk) == True{} : Bool}
) -> {kh.hv(ww, qq, kk) == True{} : Bool}:
  match xs:
    case []:
      Eq.bit.absurd(&2, {kh.hv(ww, qq, kk) == True{} : Bool}, Equal.cong(T.Hit, Bool, hh => kh.isf(hh), T.Miss{},
        T.Found{ww}, ef))
    case T.VPair{+mm, +old} <> +tt:
      kh.first.st(T.str.eq(mm, aa), mm, old, tt, aa, ww, qq, kk, {==}, ef, bo.t(Bool.and(kh.eA(T.VPair{mm, old}, aa,
        qq, kk), kh.A(tt, aa, qq, kk)), kh.A(T.VPair{mm, old} <> tt, aa, qq, kk), Equal.sym(Bool, kh.A(T.VPair{mm,
          old} <> tt, aa, qq, kk), Bool.and(kh.eA(T.VPair{mm, old}, aa, qq, kk), kh.A(tt, aa, qq, kk)),
          kh.uA(T.VPair{mm, old}, qq, tt, aa, kk)), ea), e1 => e2 => kh.first(tt, aa, ww, qq, kk, e1, e2))
    case T.VStr{+a1} <> +tt:
      kh.first(tt, aa, ww, qq, kk, ef, ea)
    case T.VSpan{+a1, +a2} <> +tt:
      kh.first(tt, aa, ww, qq, kk, ef, ea)
    case T.VInt{+a1, +a2} <> +tt:
      kh.first(tt, aa, ww, qq, kk, ef, ea)
    case T.VFlo{+a1, +a2} <> +tt:
      kh.first(tt, aa, ww, qq, kk, ef, ea)
    case T.VBool{+a1} <> +tt:
      kh.first(tt, aa, ww, qq, kk, ef, ea)
    case T.VWhen{+a1} <> +tt:
      kh.first(tt, aa, ww, qq, kk, ef, ea)
    case T.VArr{+a1} <> +tt:
      kh.first(tt, aa, ww, qq, kk, ef, ea)
    case T.VInl{+a1} <> +tt:
      kh.first(tt, aa, ww, qq, kk, ef, ea)
    case T.VHead{+a1, +a2} <> +tt:
      kh.first(tt, aa, ww, qq, kk, ef, ea)
    case T.VAot{+a1, +a2} <> +tt:
      kh.first(tt, aa, ww, qq, kk, ef, ea)
    case T.VAots{+a1, +a2} <> +tt:
      kh.first(tt, aa, ww, qq, kk, ef, ea)

# the rows seen for one name after a replacement, by whether the name is the
# replaced one
def kh.xrep.a(
  bb: Bool,
  +parent: List<&2, T.Val>,
  +aa: String,
  +mm: String,
  +qq: List<&2, String>,
  +ww: T.Val,
  +vv: T.Val,
  +kk: String,
  +eb: {T.str.eq(aa, mm) == bb : Bool},
  +ef: {T.rows.find(parent, aa) == T.Found{ww} : T.Hit},
  ev: @q0: List<&2, String> -> {kh.hv(ww, q0, kk) == True{} : Bool} -> {kh.hv(vv, q0, kk) == True{} : Bool},
  +ea: {kh.A(parent, mm, qq, kk) == True{} : Bool}
) -> {kh.A(T.rows.repl(parent, aa, vv), mm, qq, kk) == True{} : Bool}:
  match bb:
    case True{}:
      %M2.str.eq.true(aa, mm, eb) : {kh.A(T.rows.repl(parent, aa, vv), _, qq, kk) == True{} : Bool}
      kh.rA.s(parent, aa, vv, qq, kk, ev(qq, kh.first(parent, aa, ww, qq, kk, ef, Equal.trans(Bool, kh.A(parent, aa,
        qq, kk), kh.A(parent, mm, qq, kk), True{}, Equal.cong(String, Bool, zz => kh.A(parent, zz, qq, kk), aa, mm,
          M2.str.eq.true(aa, mm, eb)), ea))))
    case False{}:
      bo.t(kh.A(T.rows.repl(parent, aa, vv), mm, qq, kk), kh.A(parent, mm, qq, kk), kh.rA.o(parent, aa, vv, mm, qq,
        kk, eb), ea)

# a replacement of every pair of a name found in rows, by a value that holds
# every path the first pair's value held, keeps every path the rows held
def kh.xrep.go(
  pp: List<&2, String>,
  +parent: List<&2, T.Val>,
  +aa: String,
  +ww: T.Val,
  +vv: T.Val,
  +kk: String,
  +ef: {T.rows.find(parent, aa) == T.Found{ww} : T.Hit},
  ev: @q0: List<&2, String> -> {kh.hv(ww, q0, kk) == True{} : Bool} -> {kh.hv(vv, q0, kk) == True{} : Bool},
  +eh: {Laws.k3.has(parent, pp, kk) == True{} : Bool}
) -> {Laws.k3.has(T.rows.repl(parent, aa, vv), pp, kk) == True{} : Bool}:
  match pp:
    case []:
      bo.t(kh.F(T.rows.repl(parent, aa, vv), kk), kh.F(parent, kk), kh.rF(parent, aa, vv, kk), eh)
    case +mm <> +qq:
      M17.gd.tt(kh.F(T.rows.repl(parent, aa, vv), mm), kh.A(T.rows.repl(parent, aa, vv), mm, qq, kk),
        bo.t(kh.F(T.rows.repl(parent, aa, vv), mm), kh.F(parent, mm), kh.rF(parent, aa, vv, mm), M17.gd.l(kh.F(parent,
          mm), kh.A(parent, mm, qq, kk), eh)),
        kh.xrep.a(T.str.eq(aa, mm), parent, aa, mm, qq, ww, vv, kk, {==}, ef, ev, M17.gd.r(kh.F(parent, mm),
            kh.A(parent,
          mm, qq, kk), eh)))

# and so as a promise for every path
def kh.xrep(
  +parent: List<&2, T.Val>,
  +aa: String,
  +ww: T.Val,
  +vv: T.Val,
  +kk: String,
  +ef: {T.rows.find(parent, aa) == T.Found{ww} : T.Hit},
  ev: @q0: List<&2, String> -> {kh.hv(ww, q0, kk) == True{} : Bool} -> {kh.hv(vv, q0, kk) == True{} : Bool}
) -> kh.Ext(parent, T.rows.repl(parent, aa, vv), kk):
  pp => eh => kh.xrep.go(pp, parent, aa, ww, vv, kk, ef, ev, eh)

# KEY-3: a walk keeps what the root held. A walk that ends with no error
# gives back rows that hold every path the rows it started from held: a pair
# is only put in front under a name the rows lack, a table's rows are only
# replaced by rows that hold what they held, and an array of tables only
# gains an element (kw.mono). kw.WI is the promise a walk carries down its
# frames: whatever the current table's rows become, if they keep what they
# held, putting the frames back keeps what the root held.

# the root's rows once the frames are put back
def kh.rb(stack: List<&2, T.Fr>, vs: List<&2, T.Val>) -> List<&2, T.Val>:
  match stack:
    case []:
      vs
    case fr <> tt:
      kh.rb(tt, T.tree.wrap(fr, vs))

# the rows a walk ends with
def kw.evs(ee: T.End) -> List<&2, T.Val>:
  match ee:
    case T.End{vs, _b, _h}:
      vs

# the error a walk ends with
def kw.ebad(ee: T.End) -> String:
  match ee:
    case T.End{_v, bad, _h}:
      bad

# a walk that ended with no error
def kw.OK(ee: T.End) -> Data:
  {String.is_empty(kw.ebad(ee)) == True{} : Bool}

# putting the frames back gives the root's rows
def kw.rbv(
  stack: List<&2, T.Fr>,
  vs: List<&2, T.Val>,
  bad: String,
  heads: List<&2, String>
) -> {kw.evs(T.tree.rebuild(stack, vs, bad, heads)) == kh.rb(stack, vs) : List<&2, T.Val>}:
  match stack:
    case []:
      {==}
    case fr <> tt:
      kw.rbv(tt, T.tree.wrap(fr, vs), bad, heads)

# and keeps the error
def kw.rbb(
  stack: List<&2, T.Fr>,
  vs: List<&2, T.Val>,
  bad: String,
  heads: List<&2, String>
) -> {kw.ebad(T.tree.rebuild(stack, vs, bad, heads)) == bad : String}:
  match stack:
    case []:
      {==}
    case fr <> tt:
      kw.rbb(tt, T.tree.wrap(fr, vs), bad, heads)

# a walk's promise: the current rows, kept, keep the root
def kw.WI(
  _stack: List<&2, T.Fr>,
  _vs: List<&2, T.Val>,
  _root: List<&2, T.Val>,
  +_kk: String
) -> Type:
  @v1: List<&2, T.Val> -> kh.Ext(_vs, v1, _kk) -> kh.Ext(_root, kh.rb(_stack, v1), _kk)

# the promise while the walk has not failed
def kw.T2(
  ok: Bool,
  stack: List<&2, T.Fr>,
  vs: List<&2, T.Val>,
  root: List<&2, T.Val>,
  +kk: String
) -> Type:
  match ok:
    case True{}:
      kw.WI(stack, vs, root, kk)
    case False{}:
      {True{} == True{} : Bool}

# the promise of a walk's state
def kw.T(tw: T.Tw, root: List<&2, T.Val>, +kk: String) -> Type:
  match tw:
    case T.Tw{vs, _j, stack, +bad, _p, _h, _i}:
      kw.T2(String.is_empty(bad), stack, vs, root, kk)

# the first error, by whether there was one
def kw.efg(
  bb: Bool,
  +bad: String,
  +why: String,
  +eo: {String.is_empty(bad) == bb : Bool},
  +ew: {String.is_empty(why) == False{} : Bool}
) -> {String.is_empty(T.err.first.go(bb, bad, why)) == False{} : Bool}:
  match bb:
    case True{}:
      ew
    case False{}:
      eo

# the first error is never empty when the new one is not
def kw.efne(
  +bad: String,
  +why: String,
  +ew: {String.is_empty(why) == False{} : Bool}
) -> {String.is_empty(T.err.first(bad, why)) == False{} : Bool}:
  kw.efg(String.is_empty(bad), bad, why, {==}, ew)

# a walk that ended well did not put the frames back with an error
def kw.okrb(
  +stack: List<&2, T.Fr>,
  +vs: List<&2, T.Val>,
  +bad: String,
  +heads: List<&2, String>,
  +eb: {String.is_empty(kw.ebad(T.tree.rebuild(stack, vs, bad, heads))) == True{} : Bool}
) -> {String.is_empty(bad) == True{} : Bool}:
  Equal.trans(Bool, String.is_empty(bad), String.is_empty(kw.ebad(T.tree.rebuild(stack, vs, bad, heads))), True{},
    Equal.cong(String, Bool, zz => String.is_empty(zz), bad, kw.ebad(T.tree.rebuild(stack, vs, bad, heads)),
      Equal.sym(String, kw.ebad(T.tree.rebuild(stack, vs, bad, heads)), bad, kw.rbb(stack, vs, bad, heads))), eb)

# nor with a new error
def kw.nox(
  +stack: List<&2, T.Fr>,
  +vs: List<&2, T.Val>,
  +bad: String,
  +why: String,
  +heads: List<&2, String>,
  +ew: {String.is_empty(why) == False{} : Bool},
  +eb: {String.is_empty(kw.ebad(T.tree.rebuild(stack, vs, T.err.first(bad, why), heads))) == True{} : Bool}
) -> {False{} == True{} : Bool}:
  Equal.trans(Bool, False{}, String.is_empty(T.err.first(bad, why)), True{}, Equal.sym(Bool,
    String.is_empty(T.err.first(bad, why)), False{}, kw.efne(bad, why, ew)), kw.okrb(stack, vs, T.err.first(bad,
      why), heads, eb))

# frames put back over rows that keep the current ones keep the root
def kw.okx(
  +stack: List<&2, T.Fr>,
  +vs: List<&2, T.Val>,
  +v1: List<&2, T.Val>,
  +bad: String,
  +heads: List<&2, String>,
  +root: List<&2, T.Val>,
  +kk: String,
  wi: kw.WI(stack, vs, root, kk),
  ex: kh.Ext(vs, v1, kk)
) -> kh.Ext(root, kw.evs(T.tree.rebuild(stack, v1, bad, heads)), kk):
  %Equal.sym(List<&2, T.Val>, kw.evs(T.tree.rebuild(stack, v1, bad, heads)), kh.rb(stack, v1), kw.rbv(stack, v1, bad,
    heads)) : kh.Ext(root, _, kk)
  wi(v1, ex)

# a name get misses is not found
def kw.miss(
  +vs: List<&2, T.Val>,
  +nn: String,
  +eh: {T.rows.find(vs, nn) == T.Miss{} : T.Hit}
) -> {kh.F(vs, nn) == False{} : Bool}:
  Equal.cong(T.Hit, Bool, hh => Laws.k3.found(hh), T.rows.find(vs, nn), T.Miss{}, eh)

# a name get finds is found
def kw.hit(
  +vs: List<&2, T.Val>,
  +nn: String,
  +ww: T.Val,
  +eh: {T.rows.find(vs, nn) == T.Found{ww} : T.Hit}
) -> {kh.F(vs, nn) == True{} : Bool}:
  Equal.cong(T.Hit, Bool, hh => Laws.k3.found(hh), T.rows.find(vs, nn), T.Found{ww}, eh)

# a put at the end of a walk
def kw.put(
  hit: T.Hit,
  +name: String,
  +vs: List<&2, T.Val>,
  +val: T.Val,
  +stack: List<&2, T.Fr>,
  +bad: String,
  +heads: List<&2, String>,
  +root: List<&2, T.Val>,
  +kk: String,
  +eh: {T.rows.find(vs, name) == hit : T.Hit},
  wi: kw.WI(stack, vs, root, kk),
  +eb: {String.is_empty(kw.ebad(T.tree.leaf.put(hit, name, vs, val, stack, bad, heads))) == True{} : Bool}
) -> kh.Ext(root, kw.evs(T.tree.leaf.put(hit, name, vs, val, stack, bad, heads)), kk):
  match hit:
    case T.Found{_v}:
      pp => _e => Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "duplicate key"),
        heads)), pp, kk) == True{} : Bool}, kw.nox(stack, vs, bad, "duplicate key", heads, {==}, eb))
    case T.Miss{}:
      kw.okx(stack, vs, T.VPair{name, val} <> vs, bad, heads, root, kk, wi, kh.fresh(name, val, vs, kk, kw.miss(vs,
        name, eh)))

# an explicit header for a table that already exists
def kw.dhead(
  seen: Bool,
  +name: String,
  +vs: List<&2, T.Val>,
  +p0: String,
  +rows: List<&2, T.Val>,
  +stack: List<&2, T.Fr>,
  +bad: String,
  +path: String,
  +heads: List<&2, String>,
  +root: List<&2, T.Val>,
  +kk: String,
  +eh: {T.rows.find(vs, name) == T.Found{T.VHead{p0, rows}} : T.Hit},
  wi: kw.WI(stack, vs, root, kk),
  +eb: kw.OK(T.tree.leaf.def.head(seen, name, vs, rows, stack, bad, path, heads))
) -> kh.Ext(root, kw.evs(T.tree.leaf.def.head(seen, name, vs, rows, stack, bad, path, heads)), kk):
  match seen:
    case True{}:
      pp => _e => Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "duplicate table"),
        heads)), pp, kk) == True{} : Bool}, kw.nox(stack, vs, bad, "duplicate table", heads, {==}, eb))
    case False{}:
      kw.okx(stack, vs, T.rows.repl(vs, name, T.VHead{path, rows}), bad, T.heads.by.head(path) <> heads, root, kk, wi,
        kh.xrep(vs, name, T.VHead{p0, rows}, T.VHead{path, rows}, kk, eh, _q => ee => ee))

# a table header at the end of a walk
def kw.dhit(
  hh: T.Hit,
  +name: String,
  +vs: List<&2, T.Val>,
  +stack: List<&2, T.Fr>,
  +bad: String,
  +path: String,
  +heads: List<&2, String>,
  +root: List<&2, T.Val>,
  +kk: String,
  +eh: {T.rows.find(vs, name) == hh : T.Hit},
  wi: kw.WI(stack, vs, root, kk),
  +eb: kw.OK(T.tree.leaf.def.hit(kh.lk(hh), name, vs, stack, bad, path, heads))
) -> kh.Ext(root, kw.evs(T.tree.leaf.def.hit(kh.lk(hh), name, vs, stack, bad, path, heads)), kk):
  match hh:
    case T.Miss{}:
      kw.okx(stack, vs, T.VPair{name, T.VHead{path, []}} <> vs, bad, T.heads.by.head(path) <> heads, root, kk, wi,
        kh.fresh(name, T.VHead{path, []}, vs, kk, kw.miss(vs, name, eh)))
    case T.Found{T.VHead{+p0, +rows}}:
      kw.dhead(T.heads.has(heads, path), name, vs, p0, rows, stack, bad, path, heads, root, kk, eh, wi, eb)
    case T.Found{T.VInl{_a}}:
      pp => _e => Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad,
        "inline table is closed"), heads)), pp, kk) == True{} : Bool}, kw.nox(stack, vs, bad,
          "inline table is closed", heads, {==}, eb))
    case T.Found{T.VAots{_a, _b}}:
      pp => _e => Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"),
        heads)), pp, kk) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads, {==}, eb))
    case T.Found{T.VStr{_a}}:
      pp => _e => Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"),
        heads)), pp, kk) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads, {==}, eb))
    case T.Found{T.VSpan{_a, _b}}:
      pp => _e => Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"),
        heads)), pp, kk) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads, {==}, eb))
    case T.Found{T.VInt{_a, _b}}:
      pp => _e => Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"),
        heads)), pp, kk) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads, {==}, eb))
    case T.Found{T.VFlo{_a, _b}}:
      pp => _e => Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"),
        heads)), pp, kk) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads, {==}, eb))
    case T.Found{T.VBool{_a}}:
      pp => _e => Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"),
        heads)), pp, kk) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads, {==}, eb))
    case T.Found{T.VWhen{_a}}:
      pp => _e => Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"),
        heads)), pp, kk) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads, {==}, eb))
    case T.Found{T.VArr{_a}}:
      pp => _e => Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"),
        heads)), pp, kk) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads, {==}, eb))
    case T.Found{T.VAot{_a, _b}}:
      pp => _e => Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"),
        heads)), pp, kk) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads, {==}, eb))
    case T.Found{T.VPair{_a, _b}}:
      pp => _e => Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"),
        heads)), pp, kk) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads, {==}, eb))

# an array of tables that gains an element keeps what its elements held
def kw.aotev(
  +path: String,
  +elems: List<&2, T.Val>,
  +q0: List<&2, String>,
  +kk: String,
  +ee: {kh.S(elems, q0, kk) == True{} : Bool}
) -> {kh.S(T.VAot{path, []} <> elems, q0, kk) == True{} : Bool}:
  bo.t(kh.S(T.VAot{path, []} <> elems, q0, kk), Bool.or(kh.eS(T.VAot{path, []}, q0, kk), kh.S(elems, q0, kk)),
    kh.uS(T.VAot{path, []}, q0, elems, kk), bo.or.tr(kh.eS(T.VAot{path, []}, q0, kk), kh.S(elems, q0, kk), ee))

# an array-of-tables header at the end of a walk
def kw.ahit(
  hh: T.Hit,
  +name: String,
  +vs: List<&2, T.Val>,
  +stack: List<&2, T.Fr>,
  +bad: String,
  +path: String,
  +heads: List<&2, String>,
  +root: List<&2, T.Val>,
  +kk: String,
  +eh: {T.rows.find(vs, name) == hh : T.Hit},
  wi: kw.WI(stack, vs, root, kk),
  +eb: kw.OK(T.tree.leaf.aot.hit(kh.lk(hh), name, vs, stack, bad, path, heads))
) -> kh.Ext(root, kw.evs(T.tree.leaf.aot.hit(kh.lk(hh), name, vs, stack, bad, path, heads)), kk):
  match hh:
    case T.Miss{}:
      kw.okx(stack, vs, T.VPair{name, T.VAots{path, [T.VAot{path, []}]}} <> vs, bad, heads, root, kk, wi,
        kh.fresh(name, T.VAots{path, [T.VAot{path, []}]}, vs, kk, kw.miss(vs, name, eh)))
    case T.Found{T.VAots{+p0, +elems}}:
      kw.okx(stack, vs, T.rows.repl(vs, name, T.VAots{path, T.VAot{path, []} <> elems}), bad, T.heads.drop(heads, path
        ++ "."), root, kk, wi, kh.xrep(vs, name, T.VAots{p0, elems}, T.VAots{path, T.VAot{path, []} <> elems}, kk, eh,
          q0 => ee => kw.aotev(path, elems, q0, kk, ee)))
    case T.Found{T.VHead{_a, _b}}:
      pp => _e => Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"),
        heads)), pp, kk) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads, {==}, eb))
    case T.Found{T.VInl{_a}}:
      pp => _e => Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad,
        "inline table is closed"), heads)), pp, kk) == True{} : Bool}, kw.nox(stack, vs, bad,
          "inline table is closed", heads, {==}, eb))
    case T.Found{T.VStr{_a}}:
      pp => _e => Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"),
        heads)), pp, kk) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads, {==}, eb))
    case T.Found{T.VSpan{_a, _b}}:
      pp => _e => Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"),
        heads)), pp, kk) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads, {==}, eb))
    case T.Found{T.VInt{_a, _b}}:
      pp => _e => Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"),
        heads)), pp, kk) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads, {==}, eb))
    case T.Found{T.VFlo{_a, _b}}:
      pp => _e => Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"),
        heads)), pp, kk) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads, {==}, eb))
    case T.Found{T.VBool{_a}}:
      pp => _e => Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"),
        heads)), pp, kk) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads, {==}, eb))
    case T.Found{T.VWhen{_a}}:
      pp => _e => Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"),
        heads)), pp, kk) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads, {==}, eb))
    case T.Found{T.VArr{_a}}:
      pp => _e => Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"),
        heads)), pp, kk) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads, {==}, eb))
    case T.Found{T.VAot{_a, _b}}:
      pp => _e => Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"),
        heads)), pp, kk) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads, {==}, eb))
    case T.Found{T.VPair{_a, _b}}:
      pp => _e => Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"),
        heads)), pp, kk) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads, {==}, eb))

# the job at the end of a walk
def kw.job(
  job: T.Job,
  +name: String,
  +vs: List<&2, T.Val>,
  +stack: List<&2, T.Fr>,
  +bad: String,
  +pre: String,
  +heads: List<&2, String>,
  +root: List<&2, T.Val>,
  +kk: String,
  wi: kw.WI(stack, vs, root, kk),
  +eb: {String.is_empty(kw.ebad(T.tree.leaf.job(job, name, vs, stack, bad, pre, heads))) == True{} : Bool}
) -> kh.Ext(root, kw.evs(T.tree.leaf.job(job, name, vs, stack, bad, pre, heads)), kk):
  match job:
    case T.JPut{+val}:
      kw.put(T.get(vs, name), name, vs, val, stack, bad, heads, root, kk, {==}, wi, eb)
    case T.JDef{}:
      %Equal.sym(T.Look, T.rows.look(vs, name), kh.lk(T.rows.find(vs, name)), kh.look(vs, name)) :
        kh.Ext(root, kw.evs(T.tree.leaf.def.hit(_, name, vs, stack, bad, T.tree.pre(pre, name), heads)), kk)
      kw.dhit(T.rows.find(vs, name), name, vs, stack, bad, T.tree.pre(pre, name), heads, root, kk, {==}, wi,
        Equal.trans(Bool, String.is_empty(kw.ebad(T.tree.leaf.def.hit(kh.lk(T.rows.find(vs, name)), name, vs, stack,
          bad, T.tree.pre(pre, name), heads))), String.is_empty(kw.ebad(T.tree.leaf.def.hit(T.rows.look(vs, name),
            name, vs, stack, bad, T.tree.pre(pre, name), heads))), True{}, Equal.cong(T.Look, Bool, zz =>
              String.is_empty(kw.ebad(T.tree.leaf.def.hit(zz, name, vs, stack, bad, T.tree.pre(pre, name), heads))),
              kh.lk(T.rows.find(vs, name)), T.rows.look(vs, name), Equal.sym(T.Look, T.rows.look(vs, name),
                kh.lk(T.rows.find(vs, name)), kh.look(vs, name))), eb))
    case T.JAot{}:
      %Equal.sym(T.Look, T.rows.look(vs, name), kh.lk(T.rows.find(vs, name)), kh.look(vs, name)) :
        kh.Ext(root, kw.evs(T.tree.leaf.aot.hit(_, name, vs, stack, bad, T.tree.pre(pre, name), heads)), kk)
      kw.ahit(T.rows.find(vs, name), name, vs, stack, bad, T.tree.pre(pre, name), heads, root, kk, {==}, wi,
        Equal.trans(Bool, String.is_empty(kw.ebad(T.tree.leaf.aot.hit(kh.lk(T.rows.find(vs, name)), name, vs, stack,
          bad, T.tree.pre(pre, name), heads))), String.is_empty(kw.ebad(T.tree.leaf.aot.hit(T.rows.look(vs, name),
            name, vs, stack, bad, T.tree.pre(pre, name), heads))), True{}, Equal.cong(T.Look, Bool, zz =>
              String.is_empty(kw.ebad(T.tree.leaf.aot.hit(zz, name, vs, stack, bad, T.tree.pre(pre, name), heads))),
              kh.lk(T.rows.find(vs, name)), T.rows.look(vs, name), Equal.sym(T.Look, T.rows.look(vs, name),
                kh.lk(T.rows.find(vs, name)), kh.look(vs, name))), eb))

# the key at the end of a walk, by whether the walk failed
def kw.leafok(
  ok: Bool,
  +name: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +bad: String,
  +pre: String,
  +heads: List<&2, String>,
  +root: List<&2, T.Val>,
  +kk: String,
  +eo: {String.is_empty(bad) == ok : Bool},
  wt: kw.T2(ok, stack, vs, root, kk),
  +eb: {String.is_empty(kw.ebad(T.tree.leaf.bad(ok, name, vs, job, stack, bad, pre, heads))) == True{} : Bool}
) -> kh.Ext(root, kw.evs(T.tree.leaf.bad(ok, name, vs, job, stack, bad, pre, heads)), kk):
  match ok:
    case False{}:
      pp => _e => Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, bad, heads)), pp, kk) == True{}
        : Bool}, Equal.trans(Bool, False{}, String.is_empty(bad), True{}, Equal.sym(Bool, String.is_empty(bad), False{},
          eo), kw.okrb(stack, vs, bad, heads, eb)))
    case True{}:
      kw.job(job, name, vs, stack, bad, pre, heads, root, kk, wt, eb)

# the key at the end of a walk
def kw.leaf(
  +name: String,
  tw: T.Tw,
  +root: List<&2, T.Val>,
  +kk: String,
  wt: kw.T(tw, root, kk),
  +eb: {String.is_empty(kw.ebad(T.tree.leaf(name, tw))) == True{} : Bool}
) -> kh.Ext(root, kw.evs(T.tree.leaf(name, tw)), kk):
  match tw:
    case T.Tw{+vs, +job, +stack, +bad, +pre, +heads, _i}:
      kw.leafok(String.is_empty(bad), name, vs, job, stack, bad, pre, heads, root, kk, {==}, wt, eb)

# a state a failed step leaves keeps the promise
def kw.tfail(
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +bad: String,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +root: List<&2, T.Val>,
  +kk: String,
  +eo: {String.is_empty(bad) == False{} : Bool}
) -> kw.T(T.Tw{vs, job, stack, bad, pre, heads, inl}, root, kk):
  %Equal.sym(Bool, String.is_empty(bad), False{}, eo) : kw.T2(_, stack, vs, root, kk)
  {==}

# an or keeps True when its left half is replaced by one True whenever it is
def bo.or.mono(
  aa: Bool,
  bb: Bool,
  cc: Bool,
  ff: @e1: {aa == True{} : Bool} -> {cc == True{} : Bool},
  +ee: {Bool.or(aa, bb) == True{} : Bool}
) -> {Bool.or(cc, bb) == True{} : Bool}:
  match aa:
    case True{}:
      bo.or.tl(cc, bb, ff({==}))
    case False{}:
      bo.or.tr(cc, bb, ee)

# a table entered or made by a walk
def kw.hgo(
  shut: Bool,
  +p0: String,
  +rows: List<&2, T.Val>,
  +name: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +mark: Bool,
  +root: List<&2, T.Val>,
  +kk: String,
  +eh: {T.rows.find(vs, name) == T.Found{T.VHead{p0, rows}} : T.Hit},
  wi: kw.WI(stack, vs, root, kk)
) -> kw.T(T.tree.sub.head.go(shut, p0, rows, name, vs, job, stack, pre, heads, inl, mark), root, kk):
  match shut:
    case True{}:
      {==}
    case False{}:
      +v1 => ex => wi(T.rows.repl(vs, name, T.VHead{p0, v1}), kh.xrep(vs, name, T.VHead{p0, rows}, T.VHead{p0, v1}, kk,
        eh, q0 => ee => ex(q0, ee)))

# a table entered by a walk, by whether a dotted key asks
def kw.hd(
  dot: Bool,
  +p0: String,
  +rows: List<&2, T.Val>,
  +name: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +mark: Bool,
  +root: List<&2, T.Val>,
  +kk: String,
  +eh: {T.rows.find(vs, name) == T.Found{T.VHead{p0, rows}} : T.Hit},
  wi: kw.WI(stack, vs, root, kk)
) -> kw.T(T.tree.sub.head(dot, p0, rows, name, vs, job, stack, pre, heads, inl, mark), root, kk):
  match dot:
    case True{}:
      kw.hgo(T.heads.head(heads, T.tree.pre(pre, name)), p0, rows, name, vs, job, stack, pre, heads, inl, mark, root,
        kk, eh, wi)
    case False{}:
      kw.hgo(False{}, p0, rows, name, vs, job, stack, pre, heads, inl, mark, root, kk, eh, wi)

# an element of an array of tables that holds a path, and the one that
# replaces it holding what it held
def kw.aotx(
  +p0: String,
  +p1: String,
  +rows: List<&2, T.Val>,
  +v1: List<&2, T.Val>,
  +tt: List<&2, T.Val>,
  +q0: List<&2, String>,
  +kk: String,
  ex: kh.Ext(rows, v1, kk),
  +ee: {kh.S(T.VAot{p1, rows} <> tt, q0, kk) == True{} : Bool}
) -> {kh.S(T.VAot{p0, v1} <> tt, q0, kk) == True{} : Bool}:
  bo.t(kh.S(T.VAot{p0, v1} <> tt, q0, kk), Bool.or(Laws.k3.has(v1, q0, kk), kh.S(tt, q0, kk)), kh.uS(T.VAot{p0, v1},
    q0, tt, kk), bo.or.mono(Laws.k3.has(rows, q0, kk), kh.S(tt, q0, kk), Laws.k3.has(v1, q0, kk), e1 => ex(q0, e1),
      Equal.trans(Bool, Bool.or(Laws.k3.has(rows, q0, kk), kh.S(tt, q0, kk)), kh.S(T.VAot{p1, rows} <> tt, q0, kk),
        True{}, Equal.sym(Bool, kh.S(T.VAot{p1, rows} <> tt, q0, kk), Bool.or(Laws.k3.has(rows, q0, kk), kh.S(tt, q0,
          kk)), kh.uS(T.VAot{p1, rows}, q0, tt, kk)), ee)))

# the newest element of an array of tables, entered by a walk
def kw.last(
  elems: List<&2, T.Val>,
  +p0: String,
  +name: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +root: List<&2, T.Val>,
  +kk: String,
  +eh: {T.rows.find(vs, name) == T.Found{T.VAots{p0, elems}} : T.Hit},
  wi: kw.WI(stack, vs, root, kk)
) -> kw.T(T.tree.sub.aots(T.look.last(elems, p0), name, vs, job, stack, pre, heads, inl, p0), root, kk):
  match elems:
    case []:
      {==}
    case T.VAot{+p1, +rows} <> +tt:
      +v1 => ex => wi(T.rows.repl(vs, name, T.VAots{p0, T.VAot{p0, v1} <> tt}), kh.xrep(vs, name, T.VAots{p0,
        T.VAot{p1, rows} <> tt}, T.VAots{p0, T.VAot{p0, v1} <> tt}, kk, eh, q0 => ee => kw.aotx(p0, p1, rows, v1, tt,
          q0, kk, ex, ee)))
    case T.VStr{_a} <> _t:
      {==}
    case T.VSpan{_a, _b} <> _t:
      {==}
    case T.VInt{_a, _b} <> _t:
      {==}
    case T.VFlo{_a, _b} <> _t:
      {==}
    case T.VBool{_a} <> _t:
      {==}
    case T.VWhen{_a} <> _t:
      {==}
    case T.VArr{_a} <> _t:
      {==}
    case T.VInl{_a} <> _t:
      {==}
    case T.VHead{_a, _b} <> _t:
      {==}
    case T.VAots{_a, _b} <> _t:
      {==}
    case T.VPair{_a, _b} <> _t:
      {==}

# an array of tables entered by a walk, by whether a dotted key asks
def kw.arr(
  dot: Bool,
  +p0: String,
  +elems: List<&2, T.Val>,
  +name: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +root: List<&2, T.Val>,
  +kk: String,
  +eh: {T.rows.find(vs, name) == T.Found{T.VAots{p0, elems}} : T.Hit},
  wi: kw.WI(stack, vs, root, kk)
) -> kw.T(T.tree.sub.arr(dot, p0, elems, name, vs, job, stack, pre, heads, inl), root, kk):
  match dot:
    case True{}:
      {==}
    case False{}:
      kw.last(elems, p0, name, vs, job, stack, pre, heads, inl, root, kk, eh, wi)

# one key a walk descends into
def kw.shit(
  hh: T.Hit,
  +name: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +mark: Bool,
  +root: List<&2, T.Val>,
  +kk: String,
  +eh: {T.rows.find(vs, name) == hh : T.Hit},
  wi: kw.WI(stack, vs, root, kk)
) -> kw.T(T.tree.sub.look(kh.lk(hh), name, vs, job, stack, pre, heads, inl, mark), root, kk):
  match hh:
    case T.Miss{}:
      +v1 => _ex => wi(T.VPair{name, T.VHead{T.tree.pre(pre, name), v1}} <> vs, kh.fresh(name, T.VHead{T.tree.pre(pre,
        name), v1}, vs, kk, kw.miss(vs, name, eh)))
    case T.Found{T.VHead{+p0, +rows}}:
      kw.hd(T.tree.sub.dot(T.tree.sub.job(mark, job)), p0, rows, name, vs, job, stack, pre, heads, inl, mark, root, kk,
        eh, wi)
    case T.Found{T.VAots{+p0, +elems}}:
      kw.arr(T.tree.sub.dot(T.tree.sub.job(mark, job)), p0, elems, name, vs, job, stack, pre, heads, inl, root, kk, eh,
        wi)
    case T.Found{T.VStr{_a}}:
      {==}
    case T.Found{T.VSpan{_a, _b}}:
      {==}
    case T.Found{T.VInt{_a, _b}}:
      {==}
    case T.Found{T.VFlo{_a, _b}}:
      {==}
    case T.Found{T.VBool{_a}}:
      {==}
    case T.Found{T.VWhen{_a}}:
      {==}
    case T.Found{T.VArr{_a}}:
      {==}
    case T.Found{T.VInl{_a}}:
      {==}
    case T.Found{T.VAot{_a, _b}}:
      {==}
    case T.Found{T.VPair{_a, _b}}:
      {==}

# one key a walk descends into, by whether the walk failed
def kw.subok(
  ok: Bool,
  +name: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +bad: String,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +mark: Bool,
  +root: List<&2, T.Val>,
  +kk: String,
  +eo: {String.is_empty(bad) == ok : Bool},
  wt: kw.T2(ok, stack, vs, root, kk)
) -> kw.T(T.tree.sub.bad(ok, name, vs, job, stack, bad, pre, heads, inl, mark), root, kk):
  match ok:
    case False{}:
      kw.tfail(vs, job, stack, bad, pre, heads, inl, root, kk, eo)
    case True{}:
      %Equal.sym(T.Look, T.rows.look(vs, name), kh.lk(T.rows.find(vs, name)), kh.look(vs, name)) :
        kw.T(T.tree.sub.look(_, name, vs, job, stack, pre, heads, inl, mark), root, kk)
      kw.shit(T.rows.find(vs, name), name, vs, job, stack, pre, heads, inl, mark, root, kk, {==}, wt)

# one key a walk descends into keeps the promise
def kw.sub(
  +name: String,
  tw: T.Tw,
  +mark: Bool,
  +root: List<&2, T.Val>,
  +kk: String,
  wt: kw.T(tw, root, kk)
) -> kw.T(T.tree.sub(name, tw, mark), root, kk):
  match tw:
    case T.Tw{+vs, +job, +stack, +bad, +pre, +heads, +inl}:
      kw.subok(String.is_empty(bad), name, vs, job, stack, bad, pre, heads, inl, mark, root, kk, {==}, wt)

# a walk with no key fails
def kw.none(
  tw: T.Tw,
  +root: List<&2, T.Val>,
  +kk: String,
  +eb: {String.is_empty(kw.ebad(T.tree.walk.none(tw))) == True{} : Bool}
) -> kh.Ext(root, kw.evs(T.tree.walk.none(tw)), kk):
  match tw:
    case T.Tw{+vs, _j, +stack, +bad, _p, +heads, _i}:
      pp => _e => Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "empty key"),
        heads)), pp, kk) == True{} : Bool}, kw.nox(stack, vs, bad, "empty key", heads, {==}, eb))

# a walk that ends with no error keeps every path the root held
def kw.walk(
  path: List<&2, String>,
  +tw: T.Tw,
  +skip: U32,
  +root: List<&2, T.Val>,
  +kk: String,
  wt: kw.T(tw, root, kk),
  +eb: {String.is_empty(kw.ebad(T.tree.walk(path, tw, skip))) == True{} : Bool}
) -> kh.Ext(root, kw.evs(T.tree.walk(path, tw, skip)), kk):
  match path:
    case []:
      kw.none(tw, root, kk, eb)
    case +nm <> rest:
      match rest:
        case []:
          kw.leaf(nm, tw, root, kk, wt, eb)
        case _h <> _t:
          kw.walk(rest, T.tree.sub(nm, tw, U32.is_zero(skip)), T.path.dec(skip), root, kk, kw.sub(nm, tw,
            U32.is_zero(skip), root, kk, wt), eb)

# the promise at the root
def kw.wi0(
  +bad: String,
  +rows: List<&2, T.Val>,
  +kk: String,
  +eo: {String.is_empty(bad) == True{} : Bool}
) -> kw.T2(String.is_empty(bad), [], rows, rows, kk):
  %Equal.sym(Bool, String.is_empty(bad), True{}, eo) : kw.T2(_, [], rows, rows, kk)
  _v1 => ex => ex

# LEMMA: a walk from the root that ends with no error keeps every path the
# root held
def kw.mono(
  path: List<&2, String>,
  +rows: List<&2, T.Val>,
  +job: T.Job,
  +bad: String,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +skip: U32,
  +kk: String,
  +eo: {String.is_empty(bad) == True{} : Bool},
  +eb: {String.is_empty(kw.ebad(T.tree.walk(path, T.Tw{rows, job, [], bad, pre, heads, inl}, skip))) == True{} : Bool}
) -> kh.Ext(rows, kw.evs(T.tree.walk(path, T.Tw{rows, job, [], bad, pre, heads, inl}, skip)), kk):
  kw.walk(path, T.Tw{rows, job, [], bad, pre, heads, inl}, skip, rows, kk, kw.wi0(bad, rows, kk, eo), eb)

# KEY-3: a walk makes what it puts. A walk that ends with no error gives back
# rows that hold, under the walk's names, the pair it put or the table it
# opened (kc.tab), and, when it put a value, every path the value holds
# below the pair (kc.put). kc.CI is the promise a walk carries down its
# frames: whatever the current table's rows hold, the root holds under the
# names walked so far, rp, reversed.

# a walk's promise: the current rows hold under the names walked so far
def kc.CI(_stack: List<&2, T.Fr>, _rp: List<&2, String>) -> Type:
  @k1: String -> @v1: List<&2, T.Val> -> @q0: List<&2, String> -> {Laws.k3.has(v1, q0, k1) == True{} : Bool} ->
    {Laws.k3.has(kh.rb(_stack, v1), List.reverse.go(&2, String, _rp, q0), k1) == True{} : Bool}

# the promise while the walk has not failed
def kc.T2(ok: Bool, stack: List<&2, T.Fr>, rp: List<&2, String>) -> Type:
  match ok:
    case True{}:
      kc.CI(stack, rp)
    case False{}:
      {True{} == True{} : Bool}

# the promise of a walk's state
def kc.T(tw: T.Tw, rp: List<&2, String>) -> Type:
  match tw:
    case T.Tw{_v, _j, stack, +bad, _p, _h, _i}:
      kc.T2(String.is_empty(bad), stack, rp)

# a replacement of every pair of a name found in rows, by a value that holds
# a path, holds the path through the name
def kh.mkr(
  +xs: List<&2, T.Val>,
  +aa: String,
  +vv: T.Val,
  +qq: List<&2, String>,
  +kk: String,
  +ef: {kh.F(xs, aa) == True{} : Bool},
  +ev: {kh.hv(vv, qq, kk) == True{} : Bool}
) -> {Laws.k3.has(T.rows.repl(xs, aa, vv), aa <> qq, kk) == True{} : Bool}:
  M17.gd.tt(kh.F(T.rows.repl(xs, aa, vv), aa), kh.A(T.rows.repl(xs, aa, vv), aa, qq, kk), bo.t(kh.F(T.rows.repl(xs, aa,
    vv), aa), kh.F(xs, aa), kh.rF(xs, aa, vv, aa), ef), kh.rA.s(xs, aa, vv, qq, kk, ev))

# a new newest element holds what its rows hold
def kc.aotin(
  +p0: String,
  +v1: List<&2, T.Val>,
  +tt: List<&2, T.Val>,
  +q0: List<&2, String>,
  +kk: String,
  +ee: {Laws.k3.has(v1, q0, kk) == True{} : Bool}
) -> {kh.S(T.VAot{p0, v1} <> tt, q0, kk) == True{} : Bool}:
  bo.t(kh.S(T.VAot{p0, v1} <> tt, q0, kk), Bool.or(Laws.k3.has(v1, q0, kk), kh.S(tt, q0, kk)), kh.uS(T.VAot{p0, v1},
    q0, tt, kk), bo.or.tl(Laws.k3.has(v1, q0, kk), kh.S(tt, q0, kk), ee))

# a state a failed step leaves keeps the promise
def kc.tfail(
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +bad: String,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +rp: List<&2, String>,
  +eo: {String.is_empty(bad) == False{} : Bool}
) -> kc.T(T.Tw{vs, job, stack, bad, pre, heads, inl}, rp):
  %Equal.sym(Bool, String.is_empty(bad), False{}, eo) : kc.T2(_, stack, rp)
  {==}

# a table entered or made by a walk
def kc.hgo(
  shut: Bool,
  +p0: String,
  +rows: List<&2, T.Val>,
  +name: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +mark: Bool,
  +rp: List<&2, String>,
  +eh: {T.rows.find(vs, name) == T.Found{T.VHead{p0, rows}} : T.Hit},
  wi: kc.CI(stack, rp)
) -> kc.T(T.tree.sub.head.go(shut, p0, rows, name, vs, job, stack, pre, heads, inl, mark), name <> rp):
  match shut:
    case True{}:
      {==}
    case False{}:
      +k1 => +v1 => +q0 => ee => wi(k1, T.rows.repl(vs, name, T.VHead{p0, v1}), name <> q0, kh.mkr(vs, name, T.VHead{p0,
        v1}, q0, k1, kw.hit(vs, name, T.VHead{p0, rows}, eh), ee))

# a table entered by a walk, by whether a dotted key asks
def kc.hd(
  dot: Bool,
  +p0: String,
  +rows: List<&2, T.Val>,
  +name: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +mark: Bool,
  +rp: List<&2, String>,
  +eh: {T.rows.find(vs, name) == T.Found{T.VHead{p0, rows}} : T.Hit},
  wi: kc.CI(stack, rp)
) -> kc.T(T.tree.sub.head(dot, p0, rows, name, vs, job, stack, pre, heads, inl, mark), name <> rp):
  match dot:
    case True{}:
      kc.hgo(T.heads.head(heads, T.tree.pre(pre, name)), p0, rows, name, vs, job, stack, pre, heads, inl, mark, rp,
        eh, wi)
    case False{}:
      kc.hgo(False{}, p0, rows, name, vs, job, stack, pre, heads, inl, mark, rp, eh, wi)

# the newest element of an array of tables, entered by a walk
def kc.last(
  elems: List<&2, T.Val>,
  +p0: String,
  +name: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +rp: List<&2, String>,
  +eh: {T.rows.find(vs, name) == T.Found{T.VAots{p0, elems}} : T.Hit},
  wi: kc.CI(stack, rp)
) -> kc.T(T.tree.sub.aots(T.look.last(elems, p0), name, vs, job, stack, pre, heads, inl, p0), name <> rp):
  match elems:
    case []:
      {==}
    case T.VAot{+p1, +rows} <> +tt:
      +k1 => +v1 => +q0 => ee => wi(k1, T.rows.repl(vs, name, T.VAots{p0, T.VAot{p0, v1} <> tt}), name <> q0,
        kh.mkr(vs, name, T.VAots{p0, T.VAot{p0, v1} <> tt}, q0, k1, kw.hit(vs, name, T.VAots{p0, T.VAot{p1, rows} <>
          tt}, eh), kc.aotin(p0, v1, tt, q0, k1, ee)))
    case T.VStr{_a} <> _t:
      {==}
    case T.VSpan{_a, _b} <> _t:
      {==}
    case T.VInt{_a, _b} <> _t:
      {==}
    case T.VFlo{_a, _b} <> _t:
      {==}
    case T.VBool{_a} <> _t:
      {==}
    case T.VWhen{_a} <> _t:
      {==}
    case T.VArr{_a} <> _t:
      {==}
    case T.VInl{_a} <> _t:
      {==}
    case T.VHead{_a, _b} <> _t:
      {==}
    case T.VAots{_a, _b} <> _t:
      {==}
    case T.VPair{_a, _b} <> _t:
      {==}

# an array of tables entered by a walk, by whether a dotted key asks
def kc.arr(
  dot: Bool,
  +p0: String,
  +elems: List<&2, T.Val>,
  +name: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +rp: List<&2, String>,
  +eh: {T.rows.find(vs, name) == T.Found{T.VAots{p0, elems}} : T.Hit},
  wi: kc.CI(stack, rp)
) -> kc.T(T.tree.sub.arr(dot, p0, elems, name, vs, job, stack, pre, heads, inl), name <> rp):
  match dot:
    case True{}:
      {==}
    case False{}:
      kc.last(elems, p0, name, vs, job, stack, pre, heads, inl, rp, eh, wi)

# one key a walk descends into
def kc.shit(
  hh: T.Hit,
  +name: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +mark: Bool,
  +rp: List<&2, String>,
  +eh: {T.rows.find(vs, name) == hh : T.Hit},
  wi: kc.CI(stack, rp)
) -> kc.T(T.tree.sub.look(kh.lk(hh), name, vs, job, stack, pre, heads, inl, mark), name <> rp):
  match hh:
    case T.Miss{}:
      +k1 => +v1 => +q0 => ee => wi(k1, T.VPair{name, T.VHead{T.tree.pre(pre, name), v1}} <> vs, name <> q0,
        kh.mk(name, T.VHead{T.tree.pre(pre, name), v1}, vs, q0, k1, kw.miss(vs, name, eh), ee))
    case T.Found{T.VHead{+p0, +rows}}:
      kc.hd(T.tree.sub.dot(T.tree.sub.job(mark, job)), p0, rows, name, vs, job, stack, pre, heads, inl, mark, rp,
        eh, wi)
    case T.Found{T.VAots{+p0, +elems}}:
      kc.arr(T.tree.sub.dot(T.tree.sub.job(mark, job)), p0, elems, name, vs, job, stack, pre, heads, inl, rp, eh,
        wi)
    case T.Found{T.VStr{_a}}:
      {==}
    case T.Found{T.VSpan{_a, _b}}:
      {==}
    case T.Found{T.VInt{_a, _b}}:
      {==}
    case T.Found{T.VFlo{_a, _b}}:
      {==}
    case T.Found{T.VBool{_a}}:
      {==}
    case T.Found{T.VWhen{_a}}:
      {==}
    case T.Found{T.VArr{_a}}:
      {==}
    case T.Found{T.VInl{_a}}:
      {==}
    case T.Found{T.VAot{_a, _b}}:
      {==}
    case T.Found{T.VPair{_a, _b}}:
      {==}

# one key a walk descends into, by whether the walk failed
def kc.subok(
  ok: Bool,
  +name: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +bad: String,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +mark: Bool,
  +rp: List<&2, String>,
  +eo: {String.is_empty(bad) == ok : Bool},
  wt: kc.T2(ok, stack, rp)
) -> kc.T(T.tree.sub.bad(ok, name, vs, job, stack, bad, pre, heads, inl, mark), name <> rp):
  match ok:
    case False{}:
      kc.tfail(vs, job, stack, bad, pre, heads, inl, name <> rp, eo)
    case True{}:
      %Equal.sym(T.Look, T.rows.look(vs, name), kh.lk(T.rows.find(vs, name)), kh.look(vs, name)) :
        kc.T(T.tree.sub.look(_, name, vs, job, stack, pre, heads, inl, mark), name <> rp)
      kc.shit(T.rows.find(vs, name), name, vs, job, stack, pre, heads, inl, mark, rp, {==}, wt)

# one key a walk descends into keeps the promise
def kc.sub(
  +name: String,
  tw: T.Tw,
  +mark: Bool,
  +rp: List<&2, String>,
  wt: kc.T(tw, rp)
) -> kc.T(T.tree.sub(name, tw, mark), name <> rp):
  match tw:
    case T.Tw{+vs, +job, +stack, +bad, +pre, +heads, +inl}:
      kc.subok(String.is_empty(bad), name, vs, job, stack, bad, pre, heads, inl, mark, rp, {==}, wt)

# a walk's job
def kw.tjob(tw: T.Tw) -> T.Job:
  match tw:
    case T.Tw{_v, job, _s, _b, _p, _h, _i}:
      job

# the job a walk goes down with, after the newest element of an array of
# tables is looked for
def kc.jlast(
  last: T.Last,
  +name: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +path: String
) -> {kw.tjob(T.tree.sub.aots(last, name, vs, job, stack, pre, heads, inl, path)) == job : T.Job}:
  match last:
    case T.LastSome{_p, _r, _w}:
      {==}
    case T.LastNo{_w}:
      {==}

# after an array of tables is entered
def kc.jarr(
  dot: Bool,
  +path: String,
  +elems: List<&2, T.Val>,
  +name: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool
) -> {kw.tjob(T.tree.sub.arr(dot, path, elems, name, vs, job, stack, pre, heads, inl)) == job : T.Job}:
  match dot:
    case True{}:
      {==}
    case False{}:
      kc.jlast(T.look.last(elems, path), name, vs, job, stack, pre, heads, inl, path)

# after a table is entered
def kc.jhgo(
  shut: Bool,
  +path: String,
  +rows: List<&2, T.Val>,
  +name: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +mark: Bool
) -> {kw.tjob(T.tree.sub.head.go(shut, path, rows, name, vs, job, stack, pre, heads, inl, mark)) == job : T.Job}:
  match shut:
    case True{}:
      {==}
    case False{}:
      {==}

# after a table is entered, by whether a dotted key asks
def kc.jhd(
  dot: Bool,
  +path: String,
  +rows: List<&2, T.Val>,
  +name: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +mark: Bool
) -> {kw.tjob(T.tree.sub.head(dot, path, rows, name, vs, job, stack, pre, heads, inl, mark)) == job : T.Job}:
  match dot:
    case True{}:
      kc.jhgo(T.heads.head(heads, T.tree.pre(pre, name)), path, rows, name, vs, job, stack, pre, heads, inl, mark)
    case False{}:
      kc.jhgo(False{}, path, rows, name, vs, job, stack, pre, heads, inl, mark)

# after one key is looked up
def kc.jlook(
  hit: T.Look,
  +name: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +mark: Bool
) -> {kw.tjob(T.tree.sub.look(hit, name, vs, job, stack, pre, heads, inl, mark)) == job : T.Job}:
  match hit:
    case T.KMiss{}:
      {==}
    case T.KHead{+path, +rows}:
      kc.jhd(T.tree.sub.dot(T.tree.sub.job(mark, job)), path, rows, name, vs, job, stack, pre, heads, inl, mark)
    case T.KInl{}:
      {==}
    case T.KAots{+path, +elems}:
      kc.jarr(T.tree.sub.dot(T.tree.sub.job(mark, job)), path, elems, name, vs, job, stack, pre, heads, inl)
    case T.KNo{_w}:
      {==}

# after one key, by whether the walk failed
def kc.jok(
  ok: Bool,
  +name: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +bad: String,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +mark: Bool
) -> {kw.tjob(T.tree.sub.bad(ok, name, vs, job, stack, bad, pre, heads, inl, mark)) == job : T.Job}:
  match ok:
    case False{}:
      {==}
    case True{}:
      kc.jlook(T.rows.look(vs, name), name, vs, job, stack, pre, heads, inl, mark)

# a walk goes down one key with its job
def kc.subjob(+name: String, tw: T.Tw, +mark: Bool) -> {kw.tjob(T.tree.sub(name, tw, mark)) == kw.tjob(tw) : T.Job}:
  match tw:
    case T.Tw{+vs, +job, +stack, +bad, +pre, +heads, +inl}:
      kc.jok(String.is_empty(bad), name, vs, job, stack, bad, pre, heads, inl, mark)

# the rows put back hold what the current rows did
def kc.okx(
  +stack: List<&2, T.Fr>,
  +v1: List<&2, T.Val>,
  +bad: String,
  +heads: List<&2, String>,
  +rp: List<&2, String>,
  +q0: List<&2, String>,
  +k1: String,
  wi: kc.CI(stack, rp),
  +ee: {Laws.k3.has(v1, q0, k1) == True{} : Bool}
) -> {Laws.k3.has(kw.evs(T.tree.rebuild(stack, v1, bad, heads)), List.reverse.go(&2, String, rp, q0), k1) == True{}
  : Bool}:
  %Equal.sym(List<&2, T.Val>, kw.evs(T.tree.rebuild(stack, v1, bad, heads)), kh.rb(stack, v1), kw.rbv(stack, v1, bad,
    heads)) : {Laws.k3.has(_, List.reverse.go(&2, String, rp, q0), k1) == True{} : Bool}
  wi(k1, v1, q0, ee)

# a put at the end of a walk puts the pair
def kc.tput(
  hit: T.Hit,
  +name: String,
  +vs: List<&2, T.Val>,
  +val: T.Val,
  +stack: List<&2, T.Fr>,
  +bad: String,
  +heads: List<&2, String>,
  +rp: List<&2, String>,
  +_eh: {T.rows.find(vs, name) == hit : T.Hit},
  wi: kc.CI(stack, rp),
  +eb: {String.is_empty(kw.ebad(T.tree.leaf.put(hit, name, vs, val, stack, bad, heads))) == True{} : Bool}
) -> {Laws.k3.has(kw.evs(T.tree.leaf.put(hit, name, vs, val, stack, bad, heads)), List.reverse.go(&2, String, rp, []),
  name) == True{} : Bool}:
  match hit:
    case T.Found{_v}:
      Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "duplicate key"), heads)),
        List.reverse.go(&2, String, rp, []), name) == True{} : Bool}, kw.nox(stack, vs, bad, "duplicate key", heads,
          {==}, eb))
    case T.Miss{}:
      kc.okx(stack, T.VPair{name, val} <> vs, bad, heads, rp, [], name, wi, kh.mk0(name, val, vs))

# an explicit header for a table that already exists
def kc.tdhead(
  seen: Bool,
  +name: String,
  +vs: List<&2, T.Val>,
  +p0: String,
  +rows: List<&2, T.Val>,
  +stack: List<&2, T.Fr>,
  +bad: String,
  +path: String,
  +heads: List<&2, String>,
  +rp: List<&2, String>,
  +eh: {T.rows.find(vs, name) == T.Found{T.VHead{p0, rows}} : T.Hit},
  wi: kc.CI(stack, rp),
  +eb: kw.OK(T.tree.leaf.def.head(seen, name, vs, rows, stack, bad, path, heads))
) -> {Laws.k3.has(kw.evs(T.tree.leaf.def.head(seen, name, vs, rows, stack, bad, path, heads)), List.reverse.go(&2,
  String, rp, []), name) == True{} : Bool}:
  match seen:
    case True{}:
      Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "duplicate table"), heads)),
        List.reverse.go(&2, String, rp, []), name) == True{} : Bool}, kw.nox(stack, vs, bad, "duplicate table", heads,
          {==}, eb))
    case False{}:
      kc.okx(stack, T.rows.repl(vs, name, T.VHead{path, rows}), bad, T.heads.by.head(path) <> heads, rp, [], name, wi,
        bo.t(kh.F(T.rows.repl(vs, name, T.VHead{path, rows}), name), kh.F(vs, name), kh.rF(vs, name, T.VHead{path,
          rows}, name), kw.hit(vs, name, T.VHead{p0, rows}, eh)))

# a table header at the end of a walk opens the table
def kc.tdhit(
  hh: T.Hit,
  +name: String,
  +vs: List<&2, T.Val>,
  +stack: List<&2, T.Fr>,
  +bad: String,
  +path: String,
  +heads: List<&2, String>,
  +rp: List<&2, String>,
  +eh: {T.rows.find(vs, name) == hh : T.Hit},
  wi: kc.CI(stack, rp),
  +eb: kw.OK(T.tree.leaf.def.hit(kh.lk(hh), name, vs, stack, bad, path, heads))
) -> {Laws.k3.has(kw.evs(T.tree.leaf.def.hit(kh.lk(hh), name, vs, stack, bad, path, heads)), List.reverse.go(&2,
  String, rp, []), name) == True{} : Bool}:
  match hh:
    case T.Miss{}:
      kc.okx(stack, T.VPair{name, T.VHead{path, []}} <> vs, bad, T.heads.by.head(path) <> heads, rp, [], name, wi,
        kh.mk0(name, T.VHead{path, []}, vs))
    case T.Found{T.VHead{+p0, +rows}}:
      kc.tdhead(T.heads.has(heads, path), name, vs, p0, rows, stack, bad, path, heads, rp, eh, wi, eb)
    case T.Found{T.VInl{_a}}:
      Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "inline table is closed"),
        heads)), List.reverse.go(&2, String, rp, []), name) == True{} : Bool}, kw.nox(stack, vs, bad,
          "inline table is closed", heads, {==}, eb))
    case T.Found{T.VStr{_a}}:
      Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"), heads)),
        List.reverse.go(&2, String, rp, []), name) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads,
          {==}, eb))
    case T.Found{T.VSpan{_a, _b}}:
      Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"), heads)),
        List.reverse.go(&2, String, rp, []), name) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads,
          {==}, eb))
    case T.Found{T.VInt{_a, _b}}:
      Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"), heads)),
        List.reverse.go(&2, String, rp, []), name) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads,
          {==}, eb))
    case T.Found{T.VFlo{_a, _b}}:
      Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"), heads)),
        List.reverse.go(&2, String, rp, []), name) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads,
          {==}, eb))
    case T.Found{T.VBool{_a}}:
      Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"), heads)),
        List.reverse.go(&2, String, rp, []), name) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads,
          {==}, eb))
    case T.Found{T.VWhen{_a}}:
      Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"), heads)),
        List.reverse.go(&2, String, rp, []), name) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads,
          {==}, eb))
    case T.Found{T.VArr{_a}}:
      Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"), heads)),
        List.reverse.go(&2, String, rp, []), name) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads,
          {==}, eb))
    case T.Found{T.VAot{_a, _b}}:
      Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"), heads)),
        List.reverse.go(&2, String, rp, []), name) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads,
          {==}, eb))
    case T.Found{T.VAots{_a, _b}}:
      Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"), heads)),
        List.reverse.go(&2, String, rp, []), name) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads,
          {==}, eb))
    case T.Found{T.VPair{_a, _b}}:
      Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"), heads)),
        List.reverse.go(&2, String, rp, []), name) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads,
          {==}, eb))

# an array-of-tables header at the end of a walk opens the array
def kc.tahit(
  hh: T.Hit,
  +name: String,
  +vs: List<&2, T.Val>,
  +stack: List<&2, T.Fr>,
  +bad: String,
  +path: String,
  +heads: List<&2, String>,
  +rp: List<&2, String>,
  +eh: {T.rows.find(vs, name) == hh : T.Hit},
  wi: kc.CI(stack, rp),
  +eb: kw.OK(T.tree.leaf.aot.hit(kh.lk(hh), name, vs, stack, bad, path, heads))
) -> {Laws.k3.has(kw.evs(T.tree.leaf.aot.hit(kh.lk(hh), name, vs, stack, bad, path, heads)), List.reverse.go(&2,
  String, rp, []), name) == True{} : Bool}:
  match hh:
    case T.Miss{}:
      kc.okx(stack, T.VPair{name, T.VAots{path, [T.VAot{path, []}]}} <> vs, bad, heads, rp, [], name, wi,
        kh.mk0(name, T.VAots{path, [T.VAot{path, []}]}, vs))
    case T.Found{T.VAots{+p0, +elems}}:
      kc.okx(stack, T.rows.repl(vs, name, T.VAots{path, T.VAot{path, []} <> elems}), bad, T.heads.drop(heads, path
        ++ "."), rp, [], name, wi, bo.t(kh.F(T.rows.repl(vs, name, T.VAots{path, T.VAot{path, []} <> elems}), name),
          kh.F(vs, name), kh.rF(vs, name, T.VAots{path, T.VAot{path, []} <> elems}, name), kw.hit(vs, name,
            T.VAots{p0, elems}, eh)))
    case T.Found{T.VInl{_a}}:
      Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "inline table is closed"),
        heads)), List.reverse.go(&2, String, rp, []), name) == True{} : Bool}, kw.nox(stack, vs, bad,
          "inline table is closed", heads, {==}, eb))
    case T.Found{T.VStr{_a}}:
      Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"), heads)),
        List.reverse.go(&2, String, rp, []), name) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads,
          {==}, eb))
    case T.Found{T.VSpan{_a, _b}}:
      Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"), heads)),
        List.reverse.go(&2, String, rp, []), name) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads,
          {==}, eb))
    case T.Found{T.VInt{_a, _b}}:
      Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"), heads)),
        List.reverse.go(&2, String, rp, []), name) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads,
          {==}, eb))
    case T.Found{T.VFlo{_a, _b}}:
      Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"), heads)),
        List.reverse.go(&2, String, rp, []), name) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads,
          {==}, eb))
    case T.Found{T.VBool{_a}}:
      Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"), heads)),
        List.reverse.go(&2, String, rp, []), name) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads,
          {==}, eb))
    case T.Found{T.VWhen{_a}}:
      Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"), heads)),
        List.reverse.go(&2, String, rp, []), name) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads,
          {==}, eb))
    case T.Found{T.VArr{_a}}:
      Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"), heads)),
        List.reverse.go(&2, String, rp, []), name) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads,
          {==}, eb))
    case T.Found{T.VHead{_a, _b}}:
      Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"), heads)),
        List.reverse.go(&2, String, rp, []), name) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads,
          {==}, eb))
    case T.Found{T.VAot{_a, _b}}:
      Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"), heads)),
        List.reverse.go(&2, String, rp, []), name) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads,
          {==}, eb))
    case T.Found{T.VPair{_a, _b}}:
      Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "not a table"), heads)),
        List.reverse.go(&2, String, rp, []), name) == True{} : Bool}, kw.nox(stack, vs, bad, "not a table", heads,
          {==}, eb))

# the job at the end of a walk makes what it names
def kc.tjob(
  job: T.Job,
  +name: String,
  +vs: List<&2, T.Val>,
  +stack: List<&2, T.Fr>,
  +bad: String,
  +pre: String,
  +heads: List<&2, String>,
  +rp: List<&2, String>,
  wi: kc.CI(stack, rp),
  +eb: {String.is_empty(kw.ebad(T.tree.leaf.job(job, name, vs, stack, bad, pre, heads))) == True{} : Bool}
) -> {Laws.k3.has(kw.evs(T.tree.leaf.job(job, name, vs, stack, bad, pre, heads)), List.reverse.go(&2, String, rp, []),
  name) == True{} : Bool}:
  match job:
    case T.JPut{+val}:
      kc.tput(T.get(vs, name), name, vs, val, stack, bad, heads, rp, {==}, wi, eb)
    case T.JDef{}:
      %Equal.sym(T.Look, T.rows.look(vs, name), kh.lk(T.rows.find(vs, name)), kh.look(vs, name)) :
        {Laws.k3.has(kw.evs(T.tree.leaf.def.hit(_, name, vs, stack, bad, T.tree.pre(pre, name), heads)),
          List.reverse.go(&2, String, rp, []), name) == True{} : Bool}
      kc.tdhit(T.rows.find(vs, name), name, vs, stack, bad, T.tree.pre(pre, name), heads, rp, {==}, wi,
        Equal.trans(Bool, String.is_empty(kw.ebad(T.tree.leaf.def.hit(kh.lk(T.rows.find(vs, name)), name, vs, stack,
          bad, T.tree.pre(pre, name), heads))), String.is_empty(kw.ebad(T.tree.leaf.def.hit(T.rows.look(vs, name),
            name, vs, stack, bad, T.tree.pre(pre, name), heads))), True{}, Equal.cong(T.Look, Bool, zz =>
              String.is_empty(kw.ebad(T.tree.leaf.def.hit(zz, name, vs, stack, bad, T.tree.pre(pre, name), heads))),
              kh.lk(T.rows.find(vs, name)), T.rows.look(vs, name), Equal.sym(T.Look, T.rows.look(vs, name),
                kh.lk(T.rows.find(vs, name)), kh.look(vs, name))), eb))
    case T.JAot{}:
      %Equal.sym(T.Look, T.rows.look(vs, name), kh.lk(T.rows.find(vs, name)), kh.look(vs, name)) :
        {Laws.k3.has(kw.evs(T.tree.leaf.aot.hit(_, name, vs, stack, bad, T.tree.pre(pre, name), heads)),
          List.reverse.go(&2, String, rp, []), name) == True{} : Bool}
      kc.tahit(T.rows.find(vs, name), name, vs, stack, bad, T.tree.pre(pre, name), heads, rp, {==}, wi,
        Equal.trans(Bool, String.is_empty(kw.ebad(T.tree.leaf.aot.hit(kh.lk(T.rows.find(vs, name)), name, vs, stack,
          bad, T.tree.pre(pre, name), heads))), String.is_empty(kw.ebad(T.tree.leaf.aot.hit(T.rows.look(vs, name),
            name, vs, stack, bad, T.tree.pre(pre, name), heads))), True{}, Equal.cong(T.Look, Bool, zz =>
              String.is_empty(kw.ebad(T.tree.leaf.aot.hit(zz, name, vs, stack, bad, T.tree.pre(pre, name), heads))),
              kh.lk(T.rows.find(vs, name)), T.rows.look(vs, name), Equal.sym(T.Look, T.rows.look(vs, name),
                kh.lk(T.rows.find(vs, name)), kh.look(vs, name))), eb))

# the key at the end of a walk, by whether the walk failed
def kc.tleafok(
  ok: Bool,
  +name: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +bad: String,
  +pre: String,
  +heads: List<&2, String>,
  +rp: List<&2, String>,
  +eo: {String.is_empty(bad) == ok : Bool},
  wt: kc.T2(ok, stack, rp),
  +eb: {String.is_empty(kw.ebad(T.tree.leaf.bad(ok, name, vs, job, stack, bad, pre, heads))) == True{} : Bool}
) -> {Laws.k3.has(kw.evs(T.tree.leaf.bad(ok, name, vs, job, stack, bad, pre, heads)), List.reverse.go(&2, String, rp,
  []), name) == True{} : Bool}:
  match ok:
    case False{}:
      Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, bad, heads)), List.reverse.go(&2, String, rp,
        []), name) == True{} : Bool}, Equal.trans(Bool, False{},
        String.is_empty(bad), True{}, Equal.sym(Bool, String.is_empty(bad), False{}, eo), kw.okrb(stack, vs, bad, heads,
          eb)))
    case True{}:
      kc.tjob(job, name, vs, stack, bad, pre, heads, rp, wt, eb)

# the key at the end of a walk
def kc.tleaf(
  +name: String,
  tw: T.Tw,
  +rp: List<&2, String>,
  wt: kc.T(tw, rp),
  +eb: {String.is_empty(kw.ebad(T.tree.leaf(name, tw))) == True{} : Bool}
) -> {Laws.k3.has(kw.evs(T.tree.leaf(name, tw)), List.reverse.go(&2, String, rp, []), name) == True{} : Bool}:
  match tw:
    case T.Tw{+vs, +job, +stack, +bad, +pre, +heads, _i}:
      kc.tleafok(String.is_empty(bad), name, vs, job, stack, bad, pre, heads, rp, {==}, wt, eb)

# whether a job is a put
def kc.isput(job: T.Job) -> Bool:
  match job:
    case T.JPut{_v}:
      True{}
    case _j:
      False{}

# the value a put puts
def kc.jval(job: T.Job) -> T.Val:
  match job:
    case T.JPut{vv}:
      vv
    case _j:
      T.VBool{False{}}

# a put at the end of a walk puts a value that holds what it held
def kc.pput(
  hit: T.Hit,
  +name: String,
  +vs: List<&2, T.Val>,
  +val: T.Val,
  +stack: List<&2, T.Fr>,
  +bad: String,
  +heads: List<&2, String>,
  +rp: List<&2, String>,
  +q0: List<&2, String>,
  +k1: String,
  +eh: {T.rows.find(vs, name) == hit : T.Hit},
  wi: kc.CI(stack, rp),
  +ev: {kh.hv(val, q0, k1) == True{} : Bool},
  +eb: {String.is_empty(kw.ebad(T.tree.leaf.put(hit, name, vs, val, stack, bad, heads))) == True{} : Bool}
) -> {Laws.k3.has(kw.evs(T.tree.leaf.put(hit, name, vs, val, stack, bad, heads)), List.reverse.go(&2, String, rp,
  name <> q0), k1) == True{} : Bool}:
  match hit:
    case T.Found{_v}:
      Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, T.err.first(bad, "duplicate key"), heads)),
        List.reverse.go(&2, String, rp, name <> q0), k1) == True{} : Bool},
        kw.nox(stack, vs, bad, "duplicate key", heads, {==}, eb))
    case T.Miss{}:
      kc.okx(stack, T.VPair{name, val} <> vs, bad, heads, rp, name <> q0, k1, wi, kh.mk(name, val, vs, q0, k1,
        kw.miss(vs, name, eh), ev))

# the put at the end of a walk, whatever the job was said to be
def kc.pjob(
  job: T.Job,
  +name: String,
  +vs: List<&2, T.Val>,
  +stack: List<&2, T.Fr>,
  +bad: String,
  +pre: String,
  +heads: List<&2, String>,
  +rp: List<&2, String>,
  +val: T.Val,
  +q0: List<&2, String>,
  +k1: String,
  wi: kc.CI(stack, rp),
  +ej: {job == T.JPut{val} : T.Job},
  +ev: {kh.hv(val, q0, k1) == True{} : Bool},
  +eb: {String.is_empty(kw.ebad(T.tree.leaf.job(job, name, vs, stack, bad, pre, heads))) == True{} : Bool}
) -> {Laws.k3.has(kw.evs(T.tree.leaf.job(job, name, vs, stack, bad, pre, heads)), List.reverse.go(&2, String, rp,
  name <> q0), k1) == True{} : Bool}:
  match job:
    case T.JPut{+v2}:
      kc.pput(T.get(vs, name), name, vs, v2, stack, bad, heads, rp, q0, k1, {==}, wi, Equal.trans(Bool, kh.hv(v2, q0,
        k1), kh.hv(val, q0, k1), True{}, Equal.cong(T.Val, Bool, zz => kh.hv(zz, q0, k1), v2, val, Equal.cong(T.Job,
          T.Val, jj => kc.jval(jj), T.JPut{v2}, T.JPut{val}, ej)), ev), eb)
    case T.JDef{}:
      Eq.bit.absurd2(&2, {Laws.k3.has(kw.evs(T.tree.leaf.job(T.JDef{}, name, vs, stack, bad, pre, heads)),
        List.reverse.go(&2, String, rp, name <> q0), k1) == True{} : Bool},
        Equal.cong(T.Job, Bool, jj => Bool.not(kc.isput(jj)), T.JDef{}, T.JPut{val}, ej))
    case T.JAot{}:
      Eq.bit.absurd2(&2, {Laws.k3.has(kw.evs(T.tree.leaf.job(T.JAot{}, name, vs, stack, bad, pre, heads)),
        List.reverse.go(&2, String, rp, name <> q0), k1) == True{} : Bool},
        Equal.cong(T.Job, Bool, jj => Bool.not(kc.isput(jj)), T.JAot{}, T.JPut{val}, ej))

# the put at the end of a walk, by whether the walk failed
def kc.pleafok(
  ok: Bool,
  +name: String,
  +vs: List<&2, T.Val>,
  +job: T.Job,
  +stack: List<&2, T.Fr>,
  +bad: String,
  +pre: String,
  +heads: List<&2, String>,
  +rp: List<&2, String>,
  +val: T.Val,
  +q0: List<&2, String>,
  +k1: String,
  +eo: {String.is_empty(bad) == ok : Bool},
  wt: kc.T2(ok, stack, rp),
  +ej: {job == T.JPut{val} : T.Job},
  +ev: {kh.hv(val, q0, k1) == True{} : Bool},
  +eb: {String.is_empty(kw.ebad(T.tree.leaf.bad(ok, name, vs, job, stack, bad, pre, heads))) == True{} : Bool}
) -> {Laws.k3.has(kw.evs(T.tree.leaf.bad(ok, name, vs, job, stack, bad, pre, heads)), List.reverse.go(&2, String, rp,
  name <> q0), k1) == True{} : Bool}:
  match ok:
    case False{}:
      Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.rebuild(stack, vs, bad, heads)), List.reverse.go(&2, String, rp,
        name <> q0), k1) == True{} : Bool}, Equal.trans(Bool, False{},
        String.is_empty(bad), True{}, Equal.sym(Bool, String.is_empty(bad), False{}, eo), kw.okrb(stack, vs, bad, heads,
          eb)))
    case True{}:
      kc.pjob(job, name, vs, stack, bad, pre, heads, rp, val, q0, k1, wt, ej, ev, eb)

# the put at the end of a walk
def kc.pleaf(
  +name: String,
  tw: T.Tw,
  +rp: List<&2, String>,
  +val: T.Val,
  +q0: List<&2, String>,
  +k1: String,
  wt: kc.T(tw, rp),
  +ej: {kw.tjob(tw) == T.JPut{val} : T.Job},
  +ev: {kh.hv(val, q0, k1) == True{} : Bool},
  +eb: {String.is_empty(kw.ebad(T.tree.leaf(name, tw))) == True{} : Bool}
) -> {Laws.k3.has(kw.evs(T.tree.leaf(name, tw)), List.reverse.go(&2, String, rp, name <> q0), k1) == True{} : Bool}:
  match tw:
    case T.Tw{+vs, +job, +stack, +bad, +pre, +heads, _i}:
      kc.pleafok(String.is_empty(bad), name, vs, job, stack, bad, pre, heads, rp, val, q0, k1, {==}, wt, ej, ev, eb)

# all but the last name of a path
def kc.initn(path: List<&2, String>) -> List<&2, String>:
  match path:
    case []:
      []
    case +nm <> rest:
      match rest:
        case []:
          []
        case _h <> _t:
          nm <> kc.initn(rest)

# the last name of a path
def kc.lastn(path: List<&2, String>) -> String:
  match path:
    case []:
      ""
    case +nm <> rest:
      match rest:
        case []:
          nm
        case _h <> _t:
          kc.lastn(rest)

# a walk with no key fails
def kc.none(
  tw: T.Tw,
  +goal: Bool,
  +eb: {String.is_empty(kw.ebad(T.tree.walk.none(tw))) == True{} : Bool}
) -> {goal == True{} : Bool}:
  match tw:
    case T.Tw{+vs, _j, +stack, +bad, _p, +heads, _i}:
      Eq.bit.absurd(&2, {goal == True{} : Bool}, kw.nox(stack, vs, bad, "empty key", heads, {==}, eb))

# LEMMA: a walk that ends with no error makes the pair or table it names,
# under its other names
def kc.wtab(
  path: List<&2, String>,
  +tw: T.Tw,
  +skip: U32,
  +rp: List<&2, String>,
  wt: kc.T(tw, rp),
  +eb: {String.is_empty(kw.ebad(T.tree.walk(path, tw, skip))) == True{} : Bool}
) -> {Laws.k3.has(kw.evs(T.tree.walk(path, tw, skip)), List.reverse.go(&2, String, rp, kc.initn(path)), kc.lastn(path))
  == True{} : Bool}:
  match path:
    case []:
      kc.none(tw, Laws.k3.has(kw.evs(T.tree.walk.none(tw)), List.reverse.go(&2, String, rp, []), ""), eb)
    case +nm <> rest:
      match rest:
        case []:
          kc.tleaf(nm, tw, rp, wt, eb)
        case _h <> _t:
          kc.wtab(rest, T.tree.sub(nm, tw, U32.is_zero(skip)), T.path.dec(skip), nm <> rp, kc.sub(nm, tw,
            U32.is_zero(skip), rp, wt), eb)

# LEMMA: a put's walk that ends with no error puts its value, and every path
# the value holds, under the walk's names
def kc.wput(
  path: List<&2, String>,
  +tw: T.Tw,
  +skip: U32,
  +rp: List<&2, String>,
  +val: T.Val,
  +q0: List<&2, String>,
  +k1: String,
  wt: kc.T(tw, rp),
  +ej: {kw.tjob(tw) == T.JPut{val} : T.Job},
  +ev: {kh.hv(val, q0, k1) == True{} : Bool},
  +eb: {String.is_empty(kw.ebad(T.tree.walk(path, tw, skip))) == True{} : Bool}
) -> {Laws.k3.has(kw.evs(T.tree.walk(path, tw, skip)), List.reverse.go(&2, String, rp, List.append(&2, String, path,
  q0)), k1) == True{} : Bool}:
  match path:
    case []:
      kc.none(tw, Laws.k3.has(kw.evs(T.tree.walk.none(tw)), List.reverse.go(&2, String, rp, q0), k1), eb)
    case +nm <> rest:
      match rest:
        case []:
          kc.pleaf(nm, tw, rp, val, q0, k1, wt, ej, ev, eb)
        case _h <> _t:
          kc.wput(rest, T.tree.sub(nm, tw, U32.is_zero(skip)), T.path.dec(skip), nm <> rp, val, q0, k1, kc.sub(nm, tw,
            U32.is_zero(skip), rp, wt), Equal.trans(T.Job, kw.tjob(T.tree.sub(nm, tw, U32.is_zero(skip))), kw.tjob(tw),
              T.JPut{val}, kc.subjob(nm, tw, U32.is_zero(skip)), ej), ev, eb)

# KEY-3: the invariant. gg names the key: the table path tp it is to be put
# in and its name. A state keeps the invariant when it has failed, or when a
# header could not throw away an open array or inline table (kk.S: a state
# that reads a header has none open), and the key is pending as the value
# being read (kk.pend), or as the key an open array or inline table will be
# put under (kk.PF), or is already held by the root or an open frame
# (kk.L). A lex state's class says which of these it may rely on: a value's
# (KcV), a header's or a line's (KcH), or another (KcO).

# the key a document is read for: the table's path and the key's name
type K3G is Data:
  K3G{tp: List<&2, String>, key: String}

# the key's table path
def kk.tp(gg: K3G) -> List<&2, String>:
  match gg:
    case K3G{tp, _k}:
      tp

# the key's name
def kk.key(gg: K3G) -> String:
  match gg:
    case K3G{_t, key}:
      key

# a lex state's class
type KC is Data:
  KcV{}
  KcH{}
  KcO{}

# the class of a lex state
def kk.cls0(lex: T.Lex) -> KC:
  match lex:
    case T.LTop{}:
      KcH{}
    case T.LLine{}:
      KcH{}
    case T.LKey{}:
      KcO{}
    case T.LKeyDot{}:
      KcO{}
    case T.LAfter{}:
      KcO{}
    case T.LKeyQ{}:
      KcO{}
    case T.LKeyE{}:
      KcO{}
    case T.LKeyU{}:
      KcO{}
    case T.LVal{}:
      KcV{}
    case T.LQ{}:
      KcV{}
    case T.LQ2{}:
      KcV{}
    case T.LStr{}:
      KcV{}
    case T.LEsc{}:
      KcV{}
    case T.LUni{}:
      KcV{}
    case T.LFold{}:
      KcV{}
    case T.LMq{}:
      KcV{}
    case T.LMqEnd{}:
      KcV{}
    case T.LTrim{}:
      KcV{}
    case T.LTrim2{}:
      KcV{}
    case T.LBare{}:
      KcV{}
    case T.LDate{}:
      KcV{}
    case T.LCom{}:
      KcO{}
    case T.LHead{}:
      KcH{}
    case T.LHeadGap{}:
      KcH{}
    case T.LHeadDot{}:
      KcH{}
    case T.LHeadQ{}:
      KcH{}
    case T.LHeadE{}:
      KcH{}
    case T.LHeadU{}:
      KcH{}
    case T.LHeadR{}:
      KcH{}
    case T.LArr{}:
      KcO{}
    case T.LArrC{}:
      KcO{}
    case T.LInl{}:
      KcO{}
    case T.LInlK{}:
      KcO{}
    case T.LInlC{}:
      KcO{}
    case T.LSink{}:
      KcO{}

# the class of a state's lex, a comment taking its return state's
def kk.cls(lex: T.Lex, back: T.Lex) -> KC:
  match lex:
    case T.LCom{}:
      kk.cls0(back)
    case other:
      kk.cls0(other)

# a value's class
def kk.isv(cc: KC) -> Bool:
  match cc:
    case KcV{}:
      True{}
    case _c:
      False{}

# a header's or a line's class
def kk.ish(cc: KC) -> Bool:
  match cc:
    case KcH{}:
      True{}
    case _c:
      False{}

# a step may go from one class to another without touching the fields:
# a value's stays a value's, and none goes to a header's but a header's
def kk.c1(cc: KC, dd: KC) -> Bool:
  match cc:
    case KcV{}:
      kk.isv(dd)
    case KcH{}:
      True{}
    case KcO{}:
      Bool.not(kk.ish(dd))

# and with the key's fields changed, when it was not a value's
def kk.c2(+cc: KC, dd: KC) -> Bool:
  Bool.and(Bool.not(kk.isv(cc)), kk.c1(cc, dd))

# the class of a state
def kk.cl(st: T.St) -> KC:
  match st:
    case T.St{_b, _r, _h, _e, _p, _f, lex, back, _q, _s, _o, _u, _l, _a, _d}:
      kk.cls(lex, back)

# two paths with the same names
def kk.leq(aa: List<&2, String>, bb: List<&2, String>) -> Bool:
  match aa bb:
    case [] Nil{}:
      True{}
    case +xx <> xs +yy <> ys:
      Bool.and(T.str.eq(xx, yy), kk.leq(xs, ys))
    case _a _b:
      False{}

# the key is the value to be taken next: its last part is the key's name
# and the others lead to the key's table, and it is no array's item
def kk.pend2(
  +gg: K3G,
  stack: List<&2, T.Ctx>,
  +here: List<&2, String>,
  parts: List<&2, String>
) -> Bool:
  match parts:
    case []:
      False{}
    case +nn <> ps:
      Bool.and(T.str.eq(nn, kk.key(gg)), kk.leq(Laws.k3.pl(stack, here, ps, []), kk.tp(gg)))

# and no array is open around it
def kk.pend(
  +gg: K3G,
  stack: List<&2, T.Ctx>,
  +here: List<&2, String>,
  parts: List<&2, String>
) -> Bool:
  match stack:
    case []:
      kk.pend2(gg, [], here, parts)
    case T.CArr{_i, _p, _h} <> _t:
      False{}
    case T.CInl{+rr, +sp, +sh} <> +rest:
      kk.pend2(gg, T.CInl{rr, sp, sh} <> rest, here, parts)

# what holds the key below a path: a table's rows, an array's items, or a
# value
type KHold is Data:
  HRows{rows: List<&2, T.Val>}
  HItems{items: List<&2, T.Val>}
  HVal{val: T.Val}

# a value taken holds a path when it is an inline table or an array that
# does
def kk.vh(vv: T.Val, +pp: List<&2, String>, +kk: String) -> Bool:
  match vv:
    case T.VInl{rows}:
      Laws.k3.has(rows, pp, kk)
    case T.VArr{items}:
      kh.S(items, pp, kk)
    case _v:
      False{}

# what holds a path
def kk.hold(hd: KHold, +pp: List<&2, String>, +kk: String) -> Bool:
  match hd:
    case HRows{rows}:
      Laws.k3.has(rows, pp, kk)
    case HItems{items}:
      kh.S(items, pp, kk)
    case HVal{vv}:
      kk.vh(vv, pp, kk)

# a path starts with the given names and the rest is held
def kk.sfx(aa: List<&2, String>, tt: List<&2, String>, hd: KHold, +kk: String) -> Bool:
  match aa tt:
    case [] +t0:
      kk.hold(hd, t0, kk)
    case +xx <> xs +yy <> ys:
      Bool.and(T.str.eq(xx, yy), kk.sfx(xs, ys, hd, kk))
    case _a _t:
      False{}

# an open frame holds the key
def kk.fh(+gg: K3G, fr: T.Ctx, rest: List<&2, T.Ctx>) -> Bool:
  match fr:
    case T.CArr{items, sp, sh}:
      kk.sfx(Laws.k3.pl(rest, sh, sp, []), kk.tp(gg), HItems{items}, kk.key(gg))
    case T.CInl{inl, sp, sh}:
      kk.sfx(Laws.k3.pl(rest, sh, sp, []), kk.tp(gg), HRows{inl}, kk.key(gg))

# the root or an open frame holds the key
def kk.L(+gg: K3G, stack: List<&2, T.Ctx>, rows: List<&2, T.Val>) -> Bool:
  match stack:
    case []:
      Laws.k3.has(rows, kk.tp(gg), kk.key(gg))
    case +fr <> +rest:
      Bool.or(kk.fh(gg, fr, rest), kk.L(gg, rest, rows))

# an open frame will be put under the key
def kk.PF(+gg: K3G, stack: List<&2, T.Ctx>) -> Bool:
  match stack:
    case []:
      False{}
    case T.CArr{_i, sp, sh} <> +rest:
      Bool.or(kk.pend(gg, rest, sh, sp), kk.PF(gg, rest))
    case T.CInl{_r, sp, sh} <> +rest:
      Bool.or(kk.pend(gg, rest, sh, sp), kk.PF(gg, rest))

# the invariant, from its parts: failed, or no frame open where a header
# may be read, and pending or held
def kk.Kb(+cc: KC, aa: Bool, ss: Bool, pp: Bool, xx: Bool) -> Bool:
  Bool.or(aa, Bool.and(Bool.or(Bool.not(kk.ish(cc)), ss), Bool.or(Bool.and(kk.isv(cc), pp), xx)))

# the invariant of a state's fields
def kk.Kc(
  +gg: K3G,
  cc: KC,
  +bad: String,
  +rows: List<&2, T.Val>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +stack: List<&2, T.Ctx>
) -> Bool:
  kk.Kb(cc, Bool.not(String.is_empty(bad)), List.is_empty(&2, T.Ctx, stack), kk.pend(gg, stack, here, parts),
    Bool.or(kk.PF(gg, stack), kk.L(gg, stack, rows)))

# KEY-3's invariant of a scanner state
def kk.K(+gg: K3G, st: T.St) -> Bool:
  match st:
    case T.St{bad, rows, _h, here, parts, _f, lex, back, _q, stack, _o, _u, _l, _a, _d}:
      kk.Kc(gg, kk.cls(lex, back), bad, rows, here, parts, stack)

# an or whose right half is replaced by one True whenever it is
def kk.bimp(
  aa: Bool,
  yy: Bool,
  zz: Bool,
  ff: @e1: {yy == True{} : Bool} -> {zz == True{} : Bool},
  +ee: {Bool.or(aa, yy) == True{} : Bool}
) -> {Bool.or(aa, zz) == True{} : Bool}:
  match aa:
    case True{}:
      {==}
    case False{}:
      ff(ee)

# a step between classes keeps the invariant's parts, when c1 allows it
def kk.b1(
  cc: KC,
  dd: KC,
  +aa: Bool,
  +ss: Bool,
  +pp: Bool,
  +xx: Bool,
  +e1: {kk.c1(cc, dd) == True{} : Bool},
  +ek: {kk.Kb(cc, aa, ss, pp, xx) == True{} : Bool}
) -> {kk.Kb(dd, aa, ss, pp, xx) == True{} : Bool}:
  match cc dd:
    case KcV{} KcV{}:
      ek
    case KcV{} KcH{}:
      Eq.bit.absurd(&2, {kk.Kb(KcH{}, aa, ss, pp, xx) == True{} : Bool}, e1)
    case KcV{} KcO{}:
      Eq.bit.absurd(&2, {kk.Kb(KcO{}, aa, ss, pp, xx) == True{} : Bool}, e1)
    case KcH{} KcV{}:
      kk.bimp(aa, Bool.and(ss, xx), Bool.or(pp, xx), e2 => bo.or.tr(pp, xx, M17.gd.r(ss, xx, e2)), ek)
    case KcH{} KcH{}:
      ek
    case KcH{} KcO{}:
      kk.bimp(aa, Bool.and(ss, xx), xx, e2 => M17.gd.r(ss, xx, e2), ek)
    case KcO{} KcV{}:
      kk.bimp(aa, xx, Bool.or(pp, xx), e2 => bo.or.tr(pp, xx, e2), ek)
    case KcO{} KcH{}:
      Eq.bit.absurd(&2, {kk.Kb(KcH{}, aa, ss, pp, xx) == True{} : Bool}, e1)
    case KcO{} KcO{}:
      ek

# and with the key's fields changed, when c2 allows it
def kk.b2(
  cc: KC,
  dd: KC,
  +aa: Bool,
  +ss: Bool,
  pp: Bool,
  +p2: Bool,
  +xx: Bool,
  +e2: {kk.c2(cc, dd) == True{} : Bool},
  +ek: {kk.Kb(cc, aa, ss, pp, xx) == True{} : Bool}
) -> {kk.Kb(dd, aa, ss, p2, xx) == True{} : Bool}:
  match cc dd:
    case KcV{} _d:
      Eq.bit.absurd(&2, {kk.Kb(_d, aa, ss, p2, xx) == True{} : Bool}, e2)
    case KcH{} KcV{}:
      kk.bimp(aa, Bool.and(ss, xx), Bool.or(p2, xx), e3 => bo.or.tr(p2, xx, M17.gd.r(ss, xx, e3)), ek)
    case KcH{} KcH{}:
      ek
    case KcH{} KcO{}:
      kk.bimp(aa, Bool.and(ss, xx), xx, e3 => M17.gd.r(ss, xx, e3), ek)
    case KcO{} KcV{}:
      kk.bimp(aa, xx, Bool.or(p2, xx), e3 => bo.or.tr(p2, xx, e3), ek)
    case KcO{} KcH{}:
      Eq.bit.absurd(&2, {kk.Kb(KcH{}, aa, ss, p2, xx) == True{} : Bool}, e2)
    case KcO{} KcO{}:
      ek

# a state's invariant at another class, with the same fields
def kk.lift1(
  +gg: K3G,
  cc: KC,
  dd: KC,
  +bad: String,
  +rows: List<&2, T.Val>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +stack: List<&2, T.Ctx>,
  +e1: {kk.c1(cc, dd) == True{} : Bool},
  +ek: {kk.Kc(gg, cc, bad, rows, here, parts, stack) == True{} : Bool}
) -> {kk.Kc(gg, dd, bad, rows, here, parts, stack) == True{} : Bool}:
  kk.b1(cc, dd, Bool.not(String.is_empty(bad)), List.is_empty(&2, T.Ctx, stack), kk.pend(gg, stack, here, parts),
    Bool.or(kk.PF(gg, stack), kk.L(gg, stack, rows)), e1, ek)

# and with the key's fields changed
def kk.lift2(
  +gg: K3G,
  cc: KC,
  dd: KC,
  +bad: String,
  +rows: List<&2, T.Val>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +h2: List<&2, String>,
  +p2: List<&2, String>,
  +stack: List<&2, T.Ctx>,
  +e2: {kk.c2(cc, dd) == True{} : Bool},
  +ek: {kk.Kc(gg, cc, bad, rows, here, parts, stack) == True{} : Bool}
) -> {kk.Kc(gg, dd, bad, rows, h2, p2, stack) == True{} : Bool}:
  kk.b2(cc, dd, Bool.not(String.is_empty(bad)), List.is_empty(&2, T.Ctx, stack), kk.pend(gg, stack, here, parts),
    kk.pend(gg, stack, h2, p2), Bool.or(kk.PF(gg, stack), kk.L(gg, stack, rows)), e2, ek)

# a state's return lex
def kk.bk(st: T.St) -> T.Lex:
  match st:
    case T.St{_b, _r, _h, _e, _p, _f, _x, back, _q, _s, _o, _u, _l, _a, _d}:
      back

# a comment's return state read as the lex state has its class
def kk.clsbb(bb: T.Lex) -> {kk.cls(bb, bb) == kk.cls0(bb) : KC}:
  match bb:
    case T.LTop{}:
      {==}
    case T.LLine{}:
      {==}
    case T.LKey{}:
      {==}
    case T.LKeyDot{}:
      {==}
    case T.LAfter{}:
      {==}
    case T.LKeyQ{}:
      {==}
    case T.LKeyE{}:
      {==}
    case T.LKeyU{}:
      {==}
    case T.LVal{}:
      {==}
    case T.LQ{}:
      {==}
    case T.LQ2{}:
      {==}
    case T.LStr{}:
      {==}
    case T.LEsc{}:
      {==}
    case T.LUni{}:
      {==}
    case T.LFold{}:
      {==}
    case T.LMq{}:
      {==}
    case T.LMqEnd{}:
      {==}
    case T.LTrim{}:
      {==}
    case T.LTrim2{}:
      {==}
    case T.LBare{}:
      {==}
    case T.LDate{}:
      {==}
    case T.LCom{}:
      {==}
    case T.LHead{}:
      {==}
    case T.LHeadGap{}:
      {==}
    case T.LHeadDot{}:
      {==}
    case T.LHeadQ{}:
      {==}
    case T.LHeadE{}:
      {==}
    case T.LHeadU{}:
      {==}
    case T.LHeadR{}:
      {==}
    case T.LArr{}:
      {==}
    case T.LArrC{}:
      {==}
    case T.LInl{}:
      {==}
    case T.LInlK{}:
      {==}
    case T.LInlC{}:
      {==}
    case T.LSink{}:
      {==}

# two paths leq calls equal are one path
def kk.leq.eq(
  aa: List<&2, String>,
  bb: List<&2, String>,
  +ee: {kk.leq(aa, bb) == True{} : Bool}
) -> {aa == bb : List<&2, String>}:
  match aa bb:
    case [] Nil{}:
      {==}
    case +xx <> +xs +yy <> +ys:
      Equal.trans(List<&2, String>, xx <> xs, yy <> xs, yy <> ys, Equal.cong(String, List<&2, String>, zz => zz <> xs,
        xx, yy, M2.str.eq.true(xx, yy, M17.gd.l(T.str.eq(xx, yy), kk.leq(xs, ys), ee))), Equal.cong(List<&2, String>,
          List<&2, String>, zs => yy <> zs, xs, ys, kk.leq.eq(xs, ys, M17.gd.r(T.str.eq(xx, yy), kk.leq(xs, ys), ee))))
    case [] _h <> _t:
      Eq.bit.absurd(&2, {[] == _h <> _t : List<&2, String>}, ee)
    case _h <> _t Nil{}:
      Eq.bit.absurd(&2, {_h <> _t == [] : List<&2, String>}, ee)

# the rest of a path after the given names
def kk.drop(aa: List<&2, String>, tt: List<&2, String>) -> List<&2, String>:
  match aa tt:
    case [] +t0:
      t0
    case _x <> xs _y <> ys:
      kk.drop(xs, ys)
    case _a _t:
      []

# a path that starts with the given names is them, then the rest
def kk.sfx.eq(
  aa: List<&2, String>,
  tt: List<&2, String>,
  +hd: KHold,
  +kk: String,
  +ee: {kk.sfx(aa, tt, hd, kk) == True{} : Bool}
) -> {tt == List.append(&2, String, aa, kk.drop(aa, tt)) : List<&2, String>}:
  match aa tt:
    case [] _t:
      {==}
    case +xx <> +xs +yy <> +ys:
      Equal.trans(List<&2, String>, yy <> ys, xx <> ys, xx <> List.append(&2, String, xs, kk.drop(xs, ys)),
        Equal.cong(String, List<&2, String>, zz => zz <> ys, yy, xx, Equal.sym(String, xx, yy, M2.str.eq.true(xx, yy,
          M17.gd.l(T.str.eq(xx, yy), kk.sfx(xs, ys, hd, kk), ee)))), Equal.cong(List<&2, String>, List<&2, String>,
              zs =>
            xx <> zs, ys, List.append(&2, String, xs, kk.drop(xs, ys)), kk.sfx.eq(xs, ys, hd, kk,
              M17.gd.r(T.str.eq(xx, yy), kk.sfx(xs, ys, hd, kk), ee))))
    case _h <> _t Nil{}:
      Eq.bit.absurd(&2, {[] == List.append(&2, String, _h <> _t, kk.drop(_h <> _t, [])) : List<&2, String>}, ee)

# and the rest is held
def kk.sfx.h(
  aa: List<&2, String>,
  tt: List<&2, String>,
  +hd: KHold,
  +kk: String,
  +ee: {kk.sfx(aa, tt, hd, kk) == True{} : Bool}
) -> {kk.hold(hd, kk.drop(aa, tt), kk) == True{} : Bool}:
  match aa tt:
    case [] _t:
      ee
    case +xx <> +xs +yy <> +ys:
      kk.sfx.h(xs, ys, hd, kk, M17.gd.r(T.str.eq(xx, yy), kk.sfx(xs, ys, hd, kk), ee))
    case _h <> _t Nil{}:
      Eq.bit.absurd(&2, {kk.hold(hd, kk.drop(_h <> _t, []), kk) == True{} : Bool}, ee)

# the given names, then a path held, start a path held
def kk.sfx.mk(
  aa: List<&2, String>,
  +dd: List<&2, String>,
  +hd: KHold,
  +kk: String,
  +ee: {kk.hold(hd, dd, kk) == True{} : Bool}
) -> {kk.sfx(aa, List.append(&2, String, aa, dd), hd, kk) == True{} : Bool}:
  match aa:
    case []:
      ee
    case +xx <> +xs:
      M17.gd.tt(T.str.eq(xx, xx), kk.sfx(xs, List.append(&2, String, xs, dd), hd, kk), M15.str.eq.self(xx),
          kk.sfx.mk(xs, dd,
        hd,
        kk, ee))

# a path held one way, and so held another
def kk.sfx.mono(
  aa: List<&2, String>,
  tt: List<&2, String>,
  +hd: KHold,
  +h2: KHold,
  +kk: String,
  ff: @q0: List<&2, String> -> {kk.hold(hd, q0, kk) == True{} : Bool} -> {kk.hold(h2, q0, kk) == True{} : Bool},
  +ee: {kk.sfx(aa, tt, hd, kk) == True{} : Bool}
) -> {kk.sfx(aa, tt, h2, kk) == True{} : Bool}:
  match aa tt:
    case [] +t0:
      ff(t0, ee)
    case +xx <> +xs +yy <> +ys:
      M17.gd.tt(T.str.eq(xx, yy), kk.sfx(xs, ys, h2, kk), M17.gd.l(T.str.eq(xx, yy), kk.sfx(xs, ys, hd, kk), ee),
        kk.sfx.mono(xs,
        ys, hd, h2, kk, ff, M17.gd.r(T.str.eq(xx, yy), kk.sfx(xs, ys, hd, kk), ee)))
    case _h <> _t Nil{}:
      ee

# the path of a value taken, then more names
def kk.pl.app(
  stack: List<&2, T.Ctx>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +aa: List<&2, String>,
  +pp: List<&2, String>
) -> {Laws.k3.pl(stack, here, parts, List.append(&2, String, aa, pp)) == List.append(&2, String, Laws.k3.pl(stack,
  here, parts,
  aa), pp) : List<&2, String>}:
  match stack:
    case []:
      Equal.sym(List<&2, String>, List.append(&2, String, List.append(&2, String, List.append(&2, String, here,
        List.reverse(&2, String, parts)), aa), pp), List.append(&2, String, List.append(&2, String, here,
          List.reverse(&2, String, parts)), List.append(&2, String, aa, pp)), la.assoc(List.append(&2, String, here,
            List.reverse(&2, String, parts)), aa, pp))
    case T.CArr{_i, +sp, +sh} <> rest:
      kk.pl.app(rest, sh, sp, aa, pp)
    case T.CInl{_r, +sp, +sh} <> rest:
      Equal.trans(List<&2, String>, Laws.k3.pl(rest, sh, sp, List.append(&2, String, List.reverse(&2, String, parts),
        List.append(&2, String, aa, pp))), Laws.k3.pl(rest, sh, sp, List.append(&2, String, List.append(&2, String,
          List.reverse(&2, String, parts), aa), pp)), List.append(&2, String, Laws.k3.pl(rest, sh, sp, List.append(&2,
            String, List.reverse(&2, String, parts), aa)), pp), Equal.cong(List<&2, String>, List<&2, String>, zs =>
              Laws.k3.pl(rest, sh, sp, zs), List.append(&2, String, List.reverse(&2, String, parts), List.append(&2,
                String,
                aa, pp)), List.append(&2, String, List.append(&2, String, List.reverse(&2, String, parts), aa), pp),
              Equal.sym(List<&2, String>, List.append(&2, String, List.append(&2, String, List.reverse(&2, String,
                parts), aa), pp), List.append(&2, String, List.reverse(&2, String, parts), List.append(&2, String, aa,
                  pp)), la.assoc(List.reverse(&2, String, parts), aa, pp))), kk.pl.app(rest, sh, sp, List.append(&2,
                    String, List.reverse(&2, String, parts), aa), pp))

# a reversal onto a list is the reversal, then the list
def kk.rga(
  zs: List<&2, String>,
  +bb: List<&2, String>,
  +acc: List<&2, String>
) -> {List.reverse.go(&2, String, zs, List.append(&2, String, bb, acc)) == List.append(&2, String,
  List.reverse.go(&2, String, zs, bb), acc) : List<&2, String>}:
  match zs:
    case []:
      {==}
    case +hh <> tt:
      kk.rga(tt, hh <> bb, acc)

# a key's parts reversed are its other parts reversed, then its last part
def kk.rev1(
  +nn: String,
  +ps: List<&2, String>
) -> {List.reverse(&2, String, nn <> ps) == List.append(&2, String, List.reverse(&2, String, ps), [nn]) : List<&2,
  String>}:
  kk.rga(ps, [], [nn])

# all but the last name of a path that ends with a name
def kk.initn(
  +aa: List<&2, String>,
  +nn: String
) -> {kc.initn(List.append(&2, String, aa, [nn])) == aa : List<&2, String>}:
  match aa:
    case []:
      {==}
    case +xx <> +xs:
      match xs:
        case []:
          {==}
        case _y <> _ys:
          Equal.cong(List<&2, String>, List<&2, String>, zs => xx <> zs, kc.initn(List.append(&2, String, xs, [nn])),
            xs,
            kk.initn(xs, nn))

# the last name of a path that ends with a name
def kk.lastn(+aa: List<&2, String>, +nn: String) -> {kc.lastn(List.append(&2, String, aa, [nn])) == nn : String}:
  match aa:
    case []:
      {==}
    case _x <> +xs:
      match xs:
        case []:
          {==}
        case _y <> _ys:
          kk.lastn(xs, nn)

# a value taken that holds a path holds it as a pair's value
def kk.vh.hv(
  +vv: T.Val,
  +pp: List<&2, String>,
  +kk: String,
  +ee: {kk.vh(vv, pp, kk) == True{} : Bool}
) -> {kh.hv(vv, pp, kk) == True{} : Bool}:
  match vv:
    case T.VInl{_r}:
      ee
    case T.VArr{_i}:
      ee
    case T.VStr{_a}:
      Eq.bit.absurd(&2, {kh.hv(T.VStr{_a}, pp, kk) == True{} : Bool}, ee)
    case T.VSpan{_a, _b}:
      Eq.bit.absurd(&2, {kh.hv(T.VSpan{_a, _b}, pp, kk) == True{} : Bool}, ee)
    case T.VInt{_a, _b}:
      Eq.bit.absurd(&2, {kh.hv(T.VInt{_a, _b}, pp, kk) == True{} : Bool}, ee)
    case T.VFlo{_a, _b}:
      Eq.bit.absurd(&2, {kh.hv(T.VFlo{_a, _b}, pp, kk) == True{} : Bool}, ee)
    case T.VBool{_a}:
      Eq.bit.absurd(&2, {kh.hv(T.VBool{_a}, pp, kk) == True{} : Bool}, ee)
    case T.VWhen{_a}:
      Eq.bit.absurd(&2, {kh.hv(T.VWhen{_a}, pp, kk) == True{} : Bool}, ee)
    case T.VHead{_a, _b}:
      Eq.bit.absurd(&2, {kh.hv(T.VHead{_a, _b}, pp, kk) == True{} : Bool}, ee)
    case T.VAot{_a, _b}:
      Eq.bit.absurd(&2, {kh.hv(T.VAot{_a, _b}, pp, kk) == True{} : Bool}, ee)
    case T.VAots{_a, _b}:
      Eq.bit.absurd(&2, {kh.hv(T.VAots{_a, _b}, pp, kk) == True{} : Bool}, ee)
    case T.VPair{_a, _b}:
      Eq.bit.absurd(&2, {kh.hv(T.VPair{_a, _b}, pp, kk) == True{} : Bool}, ee)

# and as an array's item
def kk.vh.es(
  +vv: T.Val,
  +pp: List<&2, String>,
  +kk: String,
  +ee: {kk.vh(vv, pp, kk) == True{} : Bool}
) -> {kh.eS(vv, pp, kk) == True{} : Bool}:
  match vv:
    case T.VInl{_r}:
      ee
    case T.VArr{_i}:
      ee
    case T.VStr{_a}:
      Eq.bit.absurd(&2, {kh.eS(T.VStr{_a}, pp, kk) == True{} : Bool}, ee)
    case T.VSpan{_a, _b}:
      Eq.bit.absurd(&2, {kh.eS(T.VSpan{_a, _b}, pp, kk) == True{} : Bool}, ee)
    case T.VInt{_a, _b}:
      Eq.bit.absurd(&2, {kh.eS(T.VInt{_a, _b}, pp, kk) == True{} : Bool}, ee)
    case T.VFlo{_a, _b}:
      Eq.bit.absurd(&2, {kh.eS(T.VFlo{_a, _b}, pp, kk) == True{} : Bool}, ee)
    case T.VBool{_a}:
      Eq.bit.absurd(&2, {kh.eS(T.VBool{_a}, pp, kk) == True{} : Bool}, ee)
    case T.VWhen{_a}:
      Eq.bit.absurd(&2, {kh.eS(T.VWhen{_a}, pp, kk) == True{} : Bool}, ee)
    case T.VHead{_a, _b}:
      Eq.bit.absurd(&2, {kh.eS(T.VHead{_a, _b}, pp, kk) == True{} : Bool}, ee)
    case T.VAot{_a, _b}:
      Eq.bit.absurd(&2, {kh.eS(T.VAot{_a, _b}, pp, kk) == True{} : Bool}, ee)
    case T.VAots{_a, _b}:
      Eq.bit.absurd(&2, {kh.eS(T.VAots{_a, _b}, pp, kk) == True{} : Bool}, ee)
    case T.VPair{_a, _b}:
      Eq.bit.absurd(&2, {kh.eS(T.VPair{_a, _b}, pp, kk) == True{} : Bool}, ee)

# the invariant of a value about to be taken: failed, or the key pending as
# the value or a frame, held, or held by the value
def kk.Kt(
  +gg: K3G,
  +bad: String,
  +rows: List<&2, T.Val>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +stack: List<&2, T.Ctx>,
  +vv: T.Val
) -> Bool:
  Bool.or(Bool.not(String.is_empty(bad)), Bool.or(kk.pend(gg, stack, here, parts), Bool.or(kk.PF(gg, stack),
    Bool.or(kk.L(gg, stack, rows), kk.sfx(Laws.k3.pl(stack, here, parts, []), kk.tp(gg), HVal{vv}, kk.key(gg))))))

# one of two held, and so one of three
def kk.fl(
  ff: Bool,
  +ll: Bool,
  +ww: Bool,
  +ee: {Bool.or(ff, ll) == True{} : Bool}
) -> {Bool.or(ff, Bool.or(ll, ww)) == True{} : Bool}:
  match ff:
    case True{}:
      {==}
    case False{}:
      bo.or.tl(ll, ww, ee)

# pending as a value's key, or held
def kk.ktb2(
  vv: Bool,
  +pp: Bool,
  +ff: Bool,
  +ll: Bool,
  +ww: Bool,
  +ee: {Bool.or(Bool.and(vv, pp), Bool.or(ff, ll)) == True{} : Bool}
) -> {Bool.or(pp, Bool.or(ff, Bool.or(ll, ww))) == True{} : Bool}:
  match vv:
    case True{}:
      match pp:
        case True{}:
          {==}
        case False{}:
          kk.fl(ff, ll, ww, ee)
    case False{}:
      bo.or.tr(pp, Bool.or(ff, Bool.or(ll, ww)), kk.fl(ff, ll, ww, ee))

# a state's invariant gives the invariant of any value it takes
def kk.tokt(
  +gg: K3G,
  +cc: KC,
  +bad: String,
  +rows: List<&2, T.Val>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +stack: List<&2, T.Ctx>,
  +vv: T.Val,
  +ek: {kk.Kc(gg, cc, bad, rows, here, parts, stack) == True{} : Bool}
) -> {kk.Kt(gg, bad, rows, here, parts, stack, vv) == True{} : Bool}:
  kk.bimp(Bool.not(String.is_empty(bad)), Bool.and(Bool.or(Bool.not(kk.ish(cc)), List.is_empty(&2, T.Ctx, stack)),
    Bool.or(Bool.and(kk.isv(cc), kk.pend(gg, stack, here, parts)), Bool.or(kk.PF(gg, stack), kk.L(gg, stack, rows)))),
    Bool.or(kk.pend(gg, stack, here, parts), Bool.or(kk.PF(gg, stack), Bool.or(kk.L(gg, stack, rows),
      kk.sfx(Laws.k3.pl(stack, here, parts, []), kk.tp(gg), HVal{vv}, kk.key(gg))))), e1 => kk.ktb2(kk.isv(cc),
        kk.pend(gg, stack, here, parts), kk.PF(gg, stack), kk.L(gg, stack, rows), kk.sfx(Laws.k3.pl(stack, here,
          parts, []),
          kk.tp(gg), HVal{vv}, kk.key(gg)), M17.gd.r(Bool.or(Bool.not(kk.ish(cc)), List.is_empty(&2, T.Ctx, stack)),
            Bool.or(Bool.and(kk.isv(cc), kk.pend(gg, stack, here, parts)), Bool.or(kk.PF(gg, stack), kk.L(gg, stack,
              rows))), e1)), ek)

# one of four, each giving the same
def kk.or4(
  pp: Bool,
  ff: Bool,
  ll: Bool,
  ww: Bool,
  +xx: Bool,
  +ee: {Bool.or(pp, Bool.or(ff, Bool.or(ll, ww))) == True{} : Bool},
  g1: @e1: {pp == True{} : Bool} -> {xx == True{} : Bool},
  g2: @e1: {ff == True{} : Bool} -> {xx == True{} : Bool},
  g3: @e1: {ll == True{} : Bool} -> {xx == True{} : Bool},
  g4: @e1: {ww == True{} : Bool} -> {xx == True{} : Bool}
) -> {xx == True{} : Bool}:
  match pp:
    case True{}:
      g1({==})
    case False{}:
      match ff:
        case True{}:
          g2({==})
        case False{}:
          match ll:
            case True{}:
              g3({==})
            case False{}:
              g4(ee)

# a path held rewritten
def kk.has2(
  +xs: List<&2, T.Val>,
  aa: List<&2, String>,
  bb: String,
  a2: List<&2, String>,
  b2: String,
  +ea: {aa == a2 : List<&2, String>},
  +eb: {bb == b2 : String},
  +ee: {Laws.k3.has(xs, a2, b2) == True{} : Bool}
) -> {Laws.k3.has(xs, aa, bb) == True{} : Bool}:
  %Equal.sym(List<&2, String>, aa, a2, ea) : {Laws.k3.has(xs, _, bb) == True{} : Bool}
  %Equal.sym(String, bb, b2, eb) : {Laws.k3.has(xs, a2, _) == True{} : Bool}
  ee

# a walk's end holds the key, or failed
def kk.KE(+gg: K3G, ee: T.End) -> Bool:
  match ee:
    case T.End{vs, +bad, _h}:
      Bool.or(Bool.not(String.is_empty(bad)), Laws.k3.has(vs, kk.tp(gg), kk.key(gg)))

# read off a walk's end
def kk.KE.u(
  +gg: K3G,
  ee: T.End
) -> {kk.KE(gg, ee) == Bool.or(Bool.not(String.is_empty(kw.ebad(ee))), Laws.k3.has(kw.evs(ee), kk.tp(gg),
  kk.key(gg))) : Bool}:
  match ee:
    case T.End{_v, _b, _h}:
      {==}

# by whether it failed
def kk.KE.mk2(
  bb: Bool,
  +hv: Bool,
  +_eb: {bb == bb : Bool},
  hh: @e1: {bb == True{} : Bool} -> {hv == True{} : Bool}
) -> {Bool.or(Bool.not(bb), hv) == True{} : Bool}:
  match bb:
    case True{}:
      hh({==})
    case False{}:
      {==}

# a walk's end holds the key when it did not fail
def kk.KEH(+_gg: K3G, +_ee: T.End) -> Type:
  @e1: {String.is_empty(kw.ebad(_ee)) == True{} : Bool} -> {Laws.k3.has(kw.evs(_ee), kk.tp(_gg), kk.key(_gg)) == True{}
    : Bool}

# a walk's end that holds the key, when it did not fail
def kk.KE.mk(
  +gg: K3G,
  +ee: T.End,
  hh: kk.KEH(gg, ee)
) -> {kk.KE(gg, ee) == True{} : Bool}:
  bo.t(kk.KE(gg, ee), Bool.or(Bool.not(String.is_empty(kw.ebad(ee))), Laws.k3.has(kw.evs(ee), kk.tp(gg), kk.key(gg))),
    kk.KE.u(gg, ee), kk.KE.mk2(String.is_empty(kw.ebad(ee)), Laws.k3.has(kw.evs(ee), kk.tp(gg), kk.key(gg)), {==}, hh))

# a take at the root
def kk.troot(
  +gg: K3G,
  end: T.End,
  +here: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +lead: Bool,
  +ee: {kk.KE(gg, end) == True{} : Bool}
) -> {kk.K(gg, T.take.root(end, here, back, qkind, uni, left, arrtab, lead)) == True{} : Bool}:
  match end:
    case T.End{+vs, +bad, +hs}:
      ee

# the promise a walk from the root starts with
def kk.ci0(
  +rows: List<&2, T.Val>,
  +job: T.Job,
  +bad: String,
  +pre: String,
  +heads: List<&2, String>,
  +inl: Bool,
  +eo: {String.is_empty(bad) == True{} : Bool}
) -> kc.T(T.Tw{rows, job, [], bad, pre, heads, inl}, []):
  %Equal.sym(Bool, String.is_empty(bad), True{}, eo) : kc.T2(_, [], [])
  _k1 => _v1 => _q0 => e1 => e1

# a walk from the root that puts a value
def kk.WR(
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +rows: List<&2, T.Val>,
  +vv: T.Val,
  +bad: String,
  +heads: List<&2, String>
) -> T.End:
  T.tree.walk(T.path.cat(here, parts), T.Tw{rows, T.JPut{vv}, [], bad, "", heads, False{}}, T.path.len(here, 0))

# a failed state's first error, over what it said
def kk.okor(
  +bad: String,
  +xx: Bool,
  +eo: {String.is_empty(bad) == True{} : Bool},
  +ee: {Bool.or(Bool.not(String.is_empty(bad)), xx) == True{} : Bool}
) -> {xx == True{} : Bool}:
  Equal.trans(Bool, xx, Bool.or(Bool.not(String.is_empty(bad)), xx), True{}, Equal.cong(Bool, Bool, zz =>
    Bool.or(Bool.not(zz), xx), True{}, String.is_empty(bad), Equal.sym(Bool, String.is_empty(bad), True{}, eo)), ee)

# the path of a key at the root: the current table, the other parts, the
# last
def kk.pc1(
  +here: List<&2, String>,
  +nn: String,
  +ps: List<&2, String>
) -> {T.path.cat(here, nn <> ps) == List.append(&2, String, List.append(&2, String, here, List.reverse(&2, String,
  ps)), [nn]) : List<&2, String>}:
  Equal.trans(List<&2, String>, List.append(&2, String, here, List.reverse(&2, String, nn <> ps)), List.append(&2,
    String, here, List.append(&2, String, List.reverse(&2, String, ps), [nn])), List.append(&2, String,
      List.append(&2, String, here, List.reverse(&2, String, ps)), [nn]), Equal.cong(List<&2, String>, List<&2,
        String>, zs => List.append(&2, String, here, zs), List.reverse(&2, String, nn <> ps), List.append(&2, String,
          List.reverse(&2, String, ps), [nn]), kk.rev1(nn, ps)), Equal.sym(List<&2, String>, List.append(&2, String,
            List.append(&2, String, here, List.reverse(&2, String, ps)), [nn]), List.append(&2, String, here,
              List.append(&2, String, List.reverse(&2, String, ps), [nn])), la.assoc(here, List.reverse(&2, String, ps),
                [nn])))

# a key pending at the root is put where it says
def kk.kroot.pend(
  +gg: K3G,
  parts: List<&2, String>,
  +here: List<&2, String>,
  +rows: List<&2, T.Val>,
  +vv: T.Val,
  +bad: String,
  +heads: List<&2, String>,
  +eo: {String.is_empty(bad) == True{} : Bool},
  +eb: kw.OK(kk.WR(here, parts, rows, vv, bad, heads)),
  +ep: {kk.pend2(gg, [], here, parts) == True{} : Bool}
) -> {Laws.k3.has(kw.evs(T.tree.walk(T.path.cat(here, parts), T.Tw{rows, T.JPut{vv}, [], bad, "", heads, False{}},
  T.path.len(here, 0))), kk.tp(gg), kk.key(gg)) == True{} : Bool}:
  match parts:
    case []:
      Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.walk(T.path.cat(here, []), T.Tw{rows, T.JPut{vv}, [], bad, "",
        heads, False{}}, T.path.len(here, 0))), kk.tp(gg), kk.key(gg)) == True{} : Bool}, ep)
    case +nn <> +ps:
      kk.has2(kw.evs(T.tree.walk(T.path.cat(here, nn <> ps), T.Tw{rows, T.JPut{vv}, [], bad, "", heads, False{}},
        T.path.len(here, 0))), kk.tp(gg), kk.key(gg), kc.initn(T.path.cat(here, nn <> ps)), kc.lastn(T.path.cat(here,
          nn <> ps)),
        Equal.trans(List<&2, String>, kk.tp(gg), List.append(&2, String, here, List.reverse(&2, String, ps)),
          kc.initn(T.path.cat(here, nn <> ps)),
          Equal.trans(List<&2, String>, kk.tp(gg), List.append(&2, String, List.append(&2, String, here,
            List.reverse(&2, String, ps)), []), List.append(&2, String, here, List.reverse(&2, String, ps)),
            Equal.sym(List<&2, String>, List.append(&2, String, List.append(&2, String, here, List.reverse(&2, String,
              ps)), []), kk.tp(gg), kk.leq.eq(List.append(&2,
              String, List.append(&2, String, here, List.reverse(&2, String, ps)), []), kk.tp(gg), M17.gd.r(T.str.eq(nn,
                kk.key(gg)), kk.leq(List.append(&2, String, List.append(&2, String, here, List.reverse(&2, String, ps)),
                []), kk.tp(gg)), ep))), M6.wh.lnil(List.append(&2, String, here, List.reverse(&2, String, ps)))),
          Equal.sym(List<&2, String>, kc.initn(T.path.cat(here, nn <> ps)), List.append(&2, String, here,
            List.reverse(&2, String, ps)), Equal.trans(List<&2, String>, kc.initn(T.path.cat(here, nn <> ps)),
            kc.initn(List.append(&2, String, List.append(&2, String, here, List.reverse(&2, String, ps)), [nn])),
              List.append(&2, String, here, List.reverse(&2, String, ps)), Equal.cong(List<&2, String>, List<&2,
                String>,
              zs => kc.initn(zs), T.path.cat(here, nn <> ps), List.append(&2, String, List.append(&2, String, here,
                List.reverse(&2, String, ps)), [nn]), kk.pc1(here, nn, ps)),
              kk.initn(List.append(&2, String, here, List.reverse(&2, String, ps)), nn)))),
        Equal.trans(String, kk.key(gg), nn, kc.lastn(T.path.cat(here, nn <> ps)), Equal.sym(String, nn, kk.key(gg),
          M2.str.eq.true(nn,
          kk.key(gg), M17.gd.l(T.str.eq(nn, kk.key(gg)), kk.leq(List.append(&2, String, List.append(&2, String, here,
            List.reverse(&2, String, ps)), []), kk.tp(gg)), ep))),
          Equal.sym(String, kc.lastn(T.path.cat(here, nn <> ps)), nn, Equal.trans(String, kc.lastn(T.path.cat(here,
            nn <> ps)), kc.lastn(List.append(&2,
            String, List.append(&2, String, here, List.reverse(&2, String, ps)), [nn])), nn, Equal.cong(List<&2,
              String>, String, zs => kc.lastn(zs), T.path.cat(here, nn <> ps),
              List.append(&2, String, List.append(&2, String, here, List.reverse(&2, String, ps)), [nn]), kk.pc1(here,
                nn, ps)), kk.lastn(List.append(&2, String, here, List.reverse(&2, String, ps)), nn)))),
        kc.wtab(T.path.cat(here, nn <> ps), T.Tw{rows, T.JPut{vv}, [], bad, "", heads, False{}}, T.path.len(here, 0),
          [], kk.ci0(rows,
          T.JPut{vv}, bad, "", heads, False{}, eo), eb))

# a value that holds the key, taken at the root, puts it where it says
def kk.kroot.vh(
  +gg: K3G,
  +parts: List<&2, String>,
  +here: List<&2, String>,
  +rows: List<&2, T.Val>,
  +vv: T.Val,
  +bad: String,
  +heads: List<&2, String>,
  +eo: {String.is_empty(bad) == True{} : Bool},
  +eb: kw.OK(kk.WR(here, parts, rows, vv, bad, heads)),
  +ev: {kk.sfx(Laws.k3.pl([], here, parts, []), kk.tp(gg), HVal{vv}, kk.key(gg)) == True{} : Bool}
) -> {Laws.k3.has(kw.evs(T.tree.walk(T.path.cat(here, parts), T.Tw{rows, T.JPut{vv}, [], bad, "", heads, False{}},
  T.path.len(here, 0))), kk.tp(gg), kk.key(gg)) == True{} : Bool}:
  kk.has2(kw.evs(T.tree.walk(T.path.cat(here, parts), T.Tw{rows, T.JPut{vv}, [], bad, "", heads, False{}},
    T.path.len(here, 0))), kk.tp(gg), kk.key(gg), List.append(&2, String, T.path.cat(here, parts),
    kk.drop(Laws.k3.pl([], here, parts, []), kk.tp(gg))), kk.key(gg), Equal.trans(List<&2, String>, kk.tp(gg),
      List.append(&2, String, Laws.k3.pl([], here, parts, []), kk.drop(Laws.k3.pl([], here, parts, []), kk.tp(gg))),
      List.append(&2, String, T.path.cat(here, parts), kk.drop(Laws.k3.pl([], here, parts, []), kk.tp(gg))),
      kk.sfx.eq(Laws.k3.pl([], here, parts, []), kk.tp(gg), HVal{vv}, kk.key(gg), ev), Equal.cong(List<&2, String>,
        List<&2, String>, zs => List.append(&2, String, zs, kk.drop(Laws.k3.pl([], here, parts, []), kk.tp(gg))),
        List.append(&2, String, T.path.cat(here, parts), []), T.path.cat(here, parts), M6.wh.lnil(T.path.cat(here,
          parts)))), {==}, kc.wput(T.path.cat(here, parts), T.Tw{rows, T.JPut{vv}, [], bad, "", heads, False{}},
            T.path.len(here, 0), [], vv, kk.drop(Laws.k3.pl([], here, parts, []), kk.tp(gg)), kk.key(gg), kk.ci0(rows,
              T.JPut{vv}, bad, "", heads, False{}, eo), {==}, kk.vh.hv(vv, kk.drop(Laws.k3.pl([], here, parts, []),
                kk.tp(gg)), kk.key(gg), kk.sfx.h(Laws.k3.pl([], here, parts, []), kk.tp(gg), HVal{vv}, kk.key(gg), ev)),
            eb))

# a walk at the root, by whether the state had failed
def kk.kroot.b(
  ok: Bool,
  +gg: K3G,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +vv: T.Val,
  +eo: {String.is_empty(bad) == ok : Bool},
  +et: {kk.Kt(gg, bad, rows, here, parts, [], vv) == True{} : Bool}
) -> {kk.KE(gg, T.tree.walk(T.path.cat(here, parts), T.Tw{rows, T.JPut{vv}, [], bad, "", heads, False{}},
  T.path.len(here, 0))) == True{} : Bool}:
  match ok:
    case False{}:
      %Equal.sym(T.End, T.tree.walk(T.path.cat(here, parts), T.Tw{rows, T.JPut{vv}, [], bad, "", heads, False{}},
        T.path.len(here, 0)), T.End{rows, bad, heads}, L3.failed_walk_changes_nothing(T.path.cat(here, parts),
        rows, T.JPut{vv}, bad, "", heads, False{}, T.path.len(here, 0), eo)) : {kk.KE(gg, _) == True{} : Bool}
      %Equal.sym(Bool, String.is_empty(bad), False{}, eo) : {Bool.or(Bool.not(_), Laws.k3.has(rows, kk.tp(gg),
        kk.key(gg))) == True{} : Bool}
      {==}
    case True{}:
      kk.KE.mk(gg, T.tree.walk(T.path.cat(here, parts), T.Tw{rows, T.JPut{vv}, [], bad, "", heads, False{}},
        T.path.len(here, 0)), +eb => kk.or4(kk.pend(gg, [], here, parts), kk.PF(gg, []), kk.L(gg, [], rows),
        kk.sfx(Laws.k3.pl([], here, parts, []), kk.tp(gg), HVal{vv}, kk.key(gg)),
          Laws.k3.has(kw.evs(T.tree.walk(T.path.cat(here, parts), T.Tw{rows, T.JPut{vv}, [], bad, "", heads, False{}},
            T.path.len(here, 0))), kk.tp(gg),
          kk.key(gg)), kk.okor(bad, Bool.or(kk.pend(gg, [], here, parts), Bool.or(kk.PF(gg, []), Bool.or(kk.L(gg, [],
            rows), kk.sfx(Laws.k3.pl([], here, parts, []), kk.tp(gg), HVal{vv}, kk.key(gg))))), eo, et),
          e1 => kk.kroot.pend(gg, parts, here, rows, vv, bad, heads, eo, eb, e1),
          e1 => Eq.bit.absurd(&2, {Laws.k3.has(kw.evs(T.tree.walk(T.path.cat(here, parts), T.Tw{rows, T.JPut{vv}, [],
            bad, "", heads, False{}}, T.path.len(here, 0))), kk.tp(gg), kk.key(gg)) == True{} : Bool}, e1),
          e1 => kw.mono(T.path.cat(here, parts), rows, T.JPut{vv}, bad, "", heads, False{}, T.path.len(here, 0),
            kk.key(gg), eo, eb)(kk.tp(gg), e1),
          e1 => kk.kroot.vh(gg, parts, here, rows, vv, bad, heads, eo, eb, e1)))

# an array's items with a value in front hold what the items held
def kk.itm(
  +vv: T.Val,
  +items: List<&2, T.Val>,
  +q0: List<&2, String>,
  +kk: String,
  +ee: {kh.S(items, q0, kk) == True{} : Bool}
) -> {kh.S(vv <> items, q0, kk) == True{} : Bool}:
  bo.t(kh.S(vv <> items, q0, kk), Bool.or(kh.eS(vv, q0, kk), kh.S(items, q0, kk)), kh.uS(vv, q0, items, kk),
    bo.or.tr(kh.eS(vv, q0, kk), kh.S(items, q0, kk), ee))

# and what the value held
def kk.itv(
  +vv: T.Val,
  +items: List<&2, T.Val>,
  +q0: List<&2, String>,
  +kk: String,
  +ee: {kk.vh(vv, q0, kk) == True{} : Bool}
) -> {kh.S(vv <> items, q0, kk) == True{} : Bool}:
  bo.t(kh.S(vv <> items, q0, kk), Bool.or(kh.eS(vv, q0, kk), kh.S(items, q0, kk)), kh.uS(vv, q0, items, kk),
    bo.or.tl(kh.eS(vv, q0, kk), kh.S(items, q0, kk), kk.vh.es(vv, q0, kk, ee)))

# a frame held, pending or put below, stays so when the frame gains
def kk.arrb(
  pf: Bool,
  fi: Bool,
  +lr: Bool,
  ww: Bool,
  +f2: Bool,
  g1: @e1: {fi == True{} : Bool} -> {f2 == True{} : Bool},
  g2: @e1: {ww == True{} : Bool} -> {f2 == True{} : Bool},
  +ee: {Bool.or(pf, Bool.or(Bool.or(fi, lr), ww)) == True{} : Bool}
) -> {Bool.or(pf, Bool.or(f2, lr)) == True{} : Bool}:
  match pf:
    case True{}:
      {==}
    case False{}:
      match fi:
        case True{}:
          bo.or.tl(f2, lr, g1({==}))
        case False{}:
          match lr:
            case True{}:
              bo.or.tr(f2, True{}, {==})
            case False{}:
              bo.or.tl(f2, False{}, g2(ee))

# a value taken into an open array
def kk.tarr(
  +gg: K3G,
  +items: List<&2, T.Val>,
  +saved: List<&2, String>,
  +at: List<&2, String>,
  +rest: List<&2, T.Ctx>,
  +vv: T.Val,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +lead: Bool,
  +et: {kk.Kt(gg, bad, rows, here, parts, T.CArr{items, saved, at} <> rest, vv) == True{} : Bool}
) -> {kk.K(gg, T.take.top(T.CArr{items, saved, at} <> rest, vv, bad, rows, heads, here, parts, back, qkind, uni,
  left, arrtab, lead)) == True{} : Bool}:
  kk.bimp(Bool.not(String.is_empty(bad)), Bool.or(kk.PF(gg, T.CArr{items, saved, at} <> rest), Bool.or(kk.L(gg,
    T.CArr{items, saved, at} <> rest, rows), kk.sfx(Laws.k3.pl(rest, at, saved, []), kk.tp(gg), HVal{vv}, kk.key(gg)))),
      Bool.or(kk.PF(gg,
      T.CArr{vv <> items, saved, at} <> rest), kk.L(gg, T.CArr{vv <> items, saved, at} <> rest, rows)), e1 =>
      kk.arrb(kk.PF(gg, T.CArr{items, saved, at} <> rest), kk.sfx(Laws.k3.pl(rest, at, saved, []), kk.tp(gg),
        HItems{items}, kk.key(gg)),
        kk.L(gg, rest, rows), kk.sfx(Laws.k3.pl(rest, at, saved, []), kk.tp(gg), HVal{vv}, kk.key(gg)),
          kk.sfx(Laws.k3.pl(rest,
          at, saved, []), kk.tp(gg), HItems{vv <>
          items}, kk.key(gg)), e2 => kk.sfx.mono(Laws.k3.pl(rest, at, saved, []), kk.tp(gg), HItems{items},
            HItems{vv <> items}, kk.key(gg),
            q0 => e3 => kk.itm(vv, items, q0, kk.key(gg), e3), e2), e2 => kk.sfx.mono(Laws.k3.pl(rest, at, saved, []),
              kk.tp(gg), HVal{vv},
              HItems{vv <> items}, kk.key(gg), q0 => e3 => kk.itv(vv, items, q0, kk.key(gg), e3), e2), e1), et)

# a walk's end in an inline table holds the key, or failed
def kk.KI(
  +gg: K3G,
  ee: T.End,
  +rows: List<&2, T.Val>,
  +at: List<&2, String>,
  +saved: List<&2, String>,
  +rest: List<&2, T.Ctx>
) -> Bool:
  match ee:
    case T.End{vs, +bad, _h}:
      Bool.or(Bool.not(String.is_empty(bad)), Bool.or(Bool.or(kk.pend(gg, rest, at, saved), kk.PF(gg, rest)),
        Bool.or(kk.sfx(Laws.k3.pl(rest, at, saved, []), kk.tp(gg), HRows{vs}, kk.key(gg)), kk.L(gg, rest, rows))))

# a value taken into an open inline table
def kk.tinl(
  +gg: K3G,
  end: T.End,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +at: List<&2, String>,
  +saved: List<&2, String>,
  +rest: List<&2, T.Ctx>,
  +back: T.Lex,
  +qkind: T.QKind,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +lead: Bool,
  +ee: {kk.KI(gg, end, rows, at, saved, rest) == True{} : Bool}
) -> {kk.K(gg, T.take.inl(end, rows, heads, at, saved, rest, back, qkind, uni, left, arrtab, lead)) == True{} : Bool}:
  match end:
    case T.End{+vs, +bad, _h}:
      ee

# read off a walk's end in an inline table
def kk.KI.u(
  +gg: K3G,
  ee: T.End,
  +rows: List<&2, T.Val>,
  +at: List<&2, String>,
  +saved: List<&2, String>,
  +rest: List<&2, T.Ctx>
) -> {kk.KI(gg, ee, rows, at, saved, rest) == Bool.or(Bool.not(String.is_empty(kw.ebad(ee))),
  Bool.or(Bool.or(kk.pend(gg, rest, at, saved), kk.PF(gg, rest)), Bool.or(kk.sfx(Laws.k3.pl(rest, at, saved, []),
    kk.tp(gg), HRows{kw.evs(ee)},
    kk.key(gg)), kk.L(gg, rest, rows)))) : Bool}:
  match ee:
    case T.End{_v, _b, _h}:
      {==}

# a key pending in an inline table is put where it says
def kk.kinl.pend(
  +gg: K3G,
  parts: List<&2, String>,
  +inl: List<&2, T.Val>,
  +saved: List<&2, String>,
  +at: List<&2, String>,
  +rest: List<&2, T.Ctx>,
  +here: List<&2, String>,
  +vv: T.Val,
  +bad: String,
  +eo: {String.is_empty(bad) == True{} : Bool},
  +eb: kw.OK(T.tree.walk(List.reverse(&2, String, parts), T.Tw{inl, T.JPut{vv}, [], bad, "", [], True{}}, 0)),
  +ep: {kk.pend2(gg, T.CInl{inl, saved, at} <> rest, here, parts) == True{} : Bool}
) -> {kk.sfx(Laws.k3.pl(rest, at, saved, []), kk.tp(gg), HRows{kw.evs(T.tree.walk(List.reverse(&2, String, parts),
  T.Tw{inl, T.JPut{vv}, [], bad, "", [], True{}}, 0))}, kk.key(gg)) == True{} : Bool}:
  match parts:
    case []:
      Eq.bit.absurd(&2, {kk.sfx(Laws.k3.pl(rest, at, saved, []), kk.tp(gg), HRows{kw.evs(T.tree.walk(List.reverse(&2,
        String, []), T.Tw{inl, T.JPut{vv}, [], bad, "", [], True{}}, 0))}, kk.key(gg)) == True{} : Bool}, ep)
    case +nn <> +ps:
      %Equal.sym(List<&2, String>, kk.tp(gg), List.append(&2, String, Laws.k3.pl(rest, at, saved, []), List.append(&2,
        String, List.reverse(&2, String, ps), [])),
        Equal.trans(List<&2, String>, kk.tp(gg), Laws.k3.pl(rest, at, saved, List.append(&2, String, List.reverse(&2,
          String, ps), [])),
          List.append(&2, String, Laws.k3.pl(rest, at, saved, []), List.append(&2, String, List.reverse(&2, String, ps),
            [])), Equal.sym(List<&2, String>,
            Laws.k3.pl(rest, at, saved, List.append(&2, String, List.reverse(&2, String, ps), [])), kk.tp(gg),
              kk.leq.eq(Laws.k3.pl(rest, at, saved,
              List.append(&2, String, List.reverse(&2, String, ps), [])), kk.tp(gg), M17.gd.r(T.str.eq(nn, kk.key(gg)),
                kk.leq(Laws.k3.pl(rest, at,
                saved, List.append(&2, String, List.reverse(&2, String, ps), [])), kk.tp(gg)), ep))), kk.pl.app(rest,
                  at, saved, [],
                  List.append(&2, String, List.reverse(&2, String, ps), [])))) : {kk.sfx(Laws.k3.pl(rest, at, saved,
                    []),
                    _, HRows{kw.evs(T.tree.walk(List.reverse(&2, String, nn <> ps), T.Tw{inl, T.JPut{vv}, [], bad, "",
                      [], True{}}, 0))}, kk.key(gg))
                    == True{} : Bool}
      kk.sfx.mk(Laws.k3.pl(rest, at, saved, []), List.append(&2, String, List.reverse(&2, String, ps), []),
        HRows{kw.evs(T.tree.walk(List.reverse(&2, String, nn <> ps), T.Tw{inl, T.JPut{vv}, [], bad, "", [], True{}},
          0))}, kk.key(gg),
        kk.has2(kw.evs(T.tree.walk(List.reverse(&2, String, nn <> ps), T.Tw{inl, T.JPut{vv}, [], bad, "", [], True{}},
          0)), List.append(&2, String, List.reverse(&2, String, ps), []), kk.key(gg), kc.initn(List.reverse(&2, String,
          nn <> ps)), kc.lastn(List.reverse(&2, String, nn <> ps)), Equal.trans(List<&2, String>, List.append(&2,
            String, List.reverse(&2, String, ps), []), List.reverse(&2, String, ps), kc.initn(List.reverse(&2, String,
              nn <> ps)), M6.wh.lnil(List.reverse(&2, String, ps)),
            Equal.sym(List<&2, String>, kc.initn(List.reverse(&2, String, nn <> ps)), List.reverse(&2, String, ps),
              Equal.trans(List<&2,
              String>, kc.initn(List.reverse(&2, String, nn <> ps)), kc.initn(List.append(&2, String, List.reverse(&2,
                String, ps), [nn])),
              List.reverse(&2, String, ps), Equal.cong(List<&2, String>, List<&2, String>, zs => kc.initn(zs),
                List.reverse(&2, String, nn <>
                ps), List.append(&2, String, List.reverse(&2, String, ps), [nn]), kk.rev1(nn, ps)),
                  kk.initn(List.reverse(&2, String, ps), nn)))),
          Equal.trans(String, kk.key(gg), nn, kc.lastn(List.reverse(&2, String, nn <> ps)), Equal.sym(String, nn,
            kk.key(gg), M2.str.eq.true(nn, kk.key(gg), M17.gd.l(T.str.eq(nn, kk.key(gg)), kk.leq(Laws.k3.pl(rest, at,
                saved,
              List.append(&2, String, List.reverse(&2, String, ps), [])), kk.tp(gg)), ep))), Equal.sym(String,
                kc.lastn(List.reverse(&2,
                String, nn <> ps)), nn, Equal.trans(String, kc.lastn(List.reverse(&2, String, nn <> ps)),
                kc.lastn(List.append(&2, String, List.reverse(&2, String, ps), [nn])), nn, Equal.cong(List<&2,
                  String>, String, zs =>
                  kc.lastn(zs), List.reverse(&2, String, nn <> ps), List.append(&2, String, List.reverse(&2, String,
                    ps), [nn]),
                  kk.rev1(nn, ps)), kk.lastn(List.reverse(&2, String, ps), nn)))),
          kc.wtab(List.reverse(&2, String, nn <> ps), T.Tw{inl, T.JPut{vv}, [], bad, "", [], True{}}, 0, [],
            kk.ci0(inl, T.JPut{vv}, bad, "", [], True{}, eo), eb)))

# a value taken into an inline table holds the key
def kk.VI(
  +gg: K3G,
  +rest: List<&2, T.Ctx>,
  +at: List<&2, String>,
  +saved: List<&2, String>,
  +parts: List<&2, String>,
  +vv: T.Val
) -> Bool:
  kk.sfx(Laws.k3.pl(rest, at, saved, List.append(&2, String, List.reverse(&2, String, parts), [])), kk.tp(gg), HVal{vv},
    kk.key(gg))

# the key's table path, when a value taken into an inline table holds it
def kk.kinl.tp(
  +gg: K3G,
  +rest: List<&2, T.Ctx>,
  +at: List<&2, String>,
  +saved: List<&2, String>,
  +parts: List<&2, String>,
  +vv: T.Val,
  +ev: {kk.VI(gg, rest, at, saved, parts, vv) == True{} : Bool}
) -> {kk.tp(gg) == List.append(&2, String, Laws.k3.pl(rest, at, saved, []), List.append(&2, String, List.reverse(&2,
  String, parts), kk.drop(Laws.k3.pl(rest, at, saved, List.append(&2, String, List.reverse(&2, String, parts), [])),
    kk.tp(gg)))) : List<&2, String>}:
  Equal.trans(List<&2, String>, kk.tp(gg), List.append(&2, String, Laws.k3.pl(rest, at, saved, List.append(&2, String,
    List.reverse(&2, String, parts), [])), kk.drop(Laws.k3.pl(rest, at, saved, List.append(&2, String, List.reverse(&2,
      String, parts), [])), kk.tp(gg))), List.append(&2, String, Laws.k3.pl(rest, at, saved, []), List.append(&2,
        String,
        List.reverse(&2, String, parts), kk.drop(Laws.k3.pl(rest, at, saved, List.append(&2, String, List.reverse(&2,
          String, parts), [])), kk.tp(gg)))),
    kk.sfx.eq(Laws.k3.pl(rest, at, saved, List.append(&2, String, List.reverse(&2, String, parts), [])), kk.tp(gg),
      HVal{vv}, kk.key(gg), ev),
    Equal.trans(List<&2, String>, List.append(&2, String, Laws.k3.pl(rest, at, saved, List.append(&2, String,
      List.reverse(&2, String, parts), [])),
      kk.drop(Laws.k3.pl(rest, at, saved, List.append(&2, String, List.reverse(&2, String, parts), [])), kk.tp(gg))),
        List.append(&2, String, List.append(&2, String, Laws.k3.pl(rest, at, saved, []), List.append(&2, String,
          List.reverse(&2, String, parts), [])), kk.drop(Laws.k3.pl(rest, at, saved, List.append(&2, String,
            List.reverse(&2, String, parts), [])), kk.tp(gg))),
      List.append(&2, String, Laws.k3.pl(rest, at, saved, []), List.append(&2, String, List.reverse(&2, String, parts),
        kk.drop(Laws.k3.pl(rest, at, saved, List.append(&2, String, List.reverse(&2, String, parts), [])), kk.tp(gg)))),
          Equal.cong(List<&2, String>, List<&2,
        String>, zs => List.append(&2, String, zs, kk.drop(Laws.k3.pl(rest, at, saved, List.append(&2, String,
          List.reverse(&2, String, parts), [])), kk.tp(gg))), Laws.k3.pl(rest, at, saved, List.append(&2, String,
            List.reverse(&2, String, parts), [])),
        List.append(&2, String, Laws.k3.pl(rest, at, saved, []), List.append(&2, String, List.reverse(&2, String,
          parts),
          [])), kk.pl.app(rest, at, saved, [],
          List.append(&2, String, List.reverse(&2, String, parts), []))), Equal.trans(List<&2, String>,
            List.append(&2, String, List.append(&2,
            String, Laws.k3.pl(rest, at, saved, []), List.append(&2, String, List.reverse(&2, String, parts), [])),
              kk.drop(Laws.k3.pl(rest, at, saved, List.append(&2, String, List.reverse(&2, String, parts), [])),
                kk.tp(gg))), List.append(&2, String, Laws.k3.pl(rest, at, saved, []), List.append(&2,
              String, List.append(&2, String, List.reverse(&2, String, parts), []), kk.drop(Laws.k3.pl(rest, at, saved,
                List.append(&2, String, List.reverse(&2, String, parts), [])), kk.tp(gg)))), List.append(&2, String,
                  Laws.k3.pl(rest, at, saved, []), List.append(&2,
                String, List.reverse(&2, String, parts), kk.drop(Laws.k3.pl(rest, at, saved, List.append(&2, String,
                  List.reverse(&2, String, parts), [])), kk.tp(gg)))), la.assoc(Laws.k3.pl(rest, at, saved, []),
                    List.append(&2, String, List.reverse(&2, String, parts), []), kk.drop(Laws.k3.pl(rest, at, saved,
                      List.append(&2, String, List.reverse(&2, String, parts), [])), kk.tp(gg))),
        Equal.cong(List<&2, String>, List<&2, String>, zs => List.append(&2, String, Laws.k3.pl(rest, at, saved, []),
          List.append(&2, String, zs,
          kk.drop(Laws.k3.pl(rest, at, saved, List.append(&2, String, List.reverse(&2, String, parts), [])),
            kk.tp(gg)))),
            List.append(&2, String, List.reverse(&2, String, parts), []), List.reverse(&2, String, parts),
              M6.wh.lnil(List.reverse(&2, String, parts))))))

# a value that holds the key, taken into an inline table, puts it where it
# says
def kk.kinl.vh(
  +gg: K3G,
  +parts: List<&2, String>,
  +inl: List<&2, T.Val>,
  +saved: List<&2, String>,
  +at: List<&2, String>,
  +rest: List<&2, T.Ctx>,
  +vv: T.Val,
  +bad: String,
  +eo: {String.is_empty(bad) == True{} : Bool},
  +eb: kw.OK(T.tree.walk(List.reverse(&2, String, parts), T.Tw{inl, T.JPut{vv}, [], bad, "", [], True{}}, 0)),
  +ev: {kk.VI(gg, rest, at, saved, parts, vv) == True{} : Bool}
) -> {kk.sfx(Laws.k3.pl(rest, at, saved, []), kk.tp(gg), HRows{kw.evs(T.tree.walk(List.reverse(&2, String, parts),
  T.Tw{inl, T.JPut{vv}, [], bad, "", [], True{}}, 0))}, kk.key(gg)) == True{} : Bool}:
  %Equal.sym(List<&2, String>, kk.tp(gg), List.append(&2, String, Laws.k3.pl(rest, at, saved, []), List.append(&2,
    String,
    List.reverse(&2, String, parts), kk.drop(Laws.k3.pl(rest, at, saved, List.append(&2, String, List.reverse(&2,
      String,
      parts), [])), kk.tp(gg)))),
    kk.kinl.tp(gg, rest, at, saved, parts, vv, ev)) : {kk.sfx(Laws.k3.pl(rest, at, saved, []), _,
      HRows{kw.evs(T.tree.walk(List.reverse(&2, String, parts), T.Tw{inl, T.JPut{vv}, [], bad, "", [], True{}}, 0))},
        kk.key(gg)) == True{}
      : Bool}
  kk.sfx.mk(Laws.k3.pl(rest, at, saved, []), List.append(&2, String, List.reverse(&2, String, parts),
    kk.drop(Laws.k3.pl(rest,
    at, saved, List.append(&2, String, List.reverse(&2, String, parts), [])), kk.tp(gg))),
      HRows{kw.evs(T.tree.walk(List.reverse(&2, String, parts), T.Tw{inl, T.JPut{vv}, [], bad, "", [], True{}}, 0))},
        kk.key(gg), kc.wput(List.reverse(&2, String, parts),
    T.Tw{inl, T.JPut{vv}, [], bad, "", [], True{}}, 0, [], vv, kk.drop(Laws.k3.pl(rest, at, saved, List.append(&2,
      String,
      List.reverse(&2, String, parts), [])), kk.tp(gg)), kk.key(gg), kk.ci0(inl, T.JPut{vv}, bad, "", [],
      True{}, eo), {==}, kk.vh.hv(vv, kk.drop(Laws.k3.pl(rest, at, saved, List.append(&2, String, List.reverse(&2,
        String,
        parts), [])), kk.tp(gg)), kk.key(gg), kk.sfx.h(Laws.k3.pl(rest, at, saved, List.append(&2, String,
        List.reverse(&2, String, parts), [])), kk.tp(gg), HVal{vv}, kk.key(gg), ev)), eb))

# an or with False first
def kk.or0(
  +xx: Bool,
  +ee: {Bool.or(False{}, xx) == True{} : Bool}
) -> {Bool.or(False{}, Bool.or(xx, False{})) == True{} : Bool}:
  bo.or.tl(xx, False{}, ee)

# a walk in an inline table, by whether the state had failed
def kk.kinl.b(
  ok: Bool,
  +gg: K3G,
  +inl: List<&2, T.Val>,
  +saved: List<&2, String>,
  +at: List<&2, String>,
  +rest: List<&2, T.Ctx>,
  +bad: String,
  +rows: List<&2, T.Val>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +vv: T.Val,
  +eo: {String.is_empty(bad) == ok : Bool},
  +et: {kk.Kt(gg, bad, rows, here, parts, T.CInl{inl, saved, at} <> rest, vv) == True{} : Bool}
) -> {kk.KI(gg, T.tree.walk(List.reverse(&2, String, parts), T.Tw{inl, T.JPut{vv}, [], bad, "", [], True{}}, 0), rows,
  at, saved, rest) == True{} : Bool}:
  match ok:
    case False{}:
      %Equal.sym(T.End, T.tree.walk(List.reverse(&2, String, parts), T.Tw{inl, T.JPut{vv}, [], bad, "", [], True{}},
        0), T.End{inl, bad, []}, L3.failed_walk_changes_nothing(List.reverse(&2, String, parts), inl, T.JPut{vv},
          bad, "",
        [], True{}, 0, eo)) : {kk.KI(gg, _, rows, at, saved, rest) == True{} : Bool}
      %Equal.sym(Bool, String.is_empty(bad), False{}, eo) : {Bool.or(Bool.not(_), Bool.or(Bool.or(kk.pend(gg, rest,
        at, saved), kk.PF(gg, rest)), Bool.or(kk.sfx(Laws.k3.pl(rest, at, saved, []), kk.tp(gg), HRows{inl},
          kk.key(gg)),
          kk.L(gg, rest, rows))))
          == True{} : Bool}
      {==}
    case True{}:
      bo.t(kk.KI(gg, T.tree.walk(List.reverse(&2, String, parts), T.Tw{inl, T.JPut{vv}, [], bad, "", [], True{}}, 0),
        rows, at, saved, rest), Bool.or(Bool.not(String.is_empty(kw.ebad(T.tree.walk(List.reverse(&2, String, parts),
          T.Tw{inl, T.JPut{vv}, [], bad, "", [], True{}}, 0)))),
        Bool.or(Bool.or(kk.pend(gg, rest, at, saved), kk.PF(gg, rest)), Bool.or(kk.sfx(Laws.k3.pl(rest, at, saved, []),
          kk.tp(gg),
          HRows{kw.evs(T.tree.walk(List.reverse(&2, String, parts), T.Tw{inl, T.JPut{vv}, [], bad, "", [], True{}},
            0))}, kk.key(gg)), kk.L(gg, rest, rows)))), kk.KI.u(gg, T.tree.walk(List.reverse(&2, String, parts),
              T.Tw{inl, T.JPut{vv}, [], bad, "", [], True{}}, 0), rows, at, saved, rest),
        kk.KE.mk2(String.is_empty(kw.ebad(T.tree.walk(List.reverse(&2, String, parts), T.Tw{inl, T.JPut{vv}, [], bad,
          "", [], True{}}, 0))), Bool.or(Bool.or(kk.pend(gg, rest, at, saved), kk.PF(gg, rest)),
          Bool.or(kk.sfx(Laws.k3.pl(rest, at, saved, []), kk.tp(gg), HRows{kw.evs(T.tree.walk(List.reverse(&2, String,
            parts), T.Tw{inl, T.JPut{vv}, [], bad, "", [], True{}}, 0))}, kk.key(gg)), kk.L(gg, rest, rows))), {==},
              +eb =>
            kk.or4(kk.pend(gg, T.CInl{inl, saved, at} <> rest, here, parts), kk.PF(gg, T.CInl{inl, saved,
              at} <> rest), kk.L(gg, T.CInl{inl, saved, at} <> rest, rows), kk.sfx(Laws.k3.pl(T.CInl{inl, saved,
                at} <> rest,
              here, parts, []), kk.tp(gg), HVal{vv}, kk.key(gg)), Bool.or(Bool.or(kk.pend(gg, rest, at, saved),
                kk.PF(gg, rest)), Bool.or(kk.sfx(Laws.k3.pl(rest, at, saved, []), kk.tp(gg),
                  HRows{kw.evs(T.tree.walk(List.reverse(&2, String, parts), T.Tw{inl, T.JPut{vv}, [], bad, "", [],
                    True{}}, 0))}, kk.key(gg)), kk.L(gg, rest,
                  rows))), kk.okor(bad, Bool.or(kk.pend(gg, T.CInl{inl, saved, at} <> rest, here, parts),
                    Bool.or(kk.PF(gg, T.CInl{inl, saved, at} <> rest),
                    Bool.or(kk.L(gg, T.CInl{inl, saved, at} <> rest, rows), kk.sfx(Laws.k3.pl(T.CInl{inl, saved,
                      at} <> rest, here, parts, []), kk.tp(gg), HVal{vv},
                      kk.key(gg))))), eo, et),
              e1 => bo.or.tr(Bool.or(kk.pend(gg, rest, at, saved), kk.PF(gg, rest)), Bool.or(kk.sfx(Laws.k3.pl(rest, at,
                saved, []), kk.tp(gg),
                HRows{kw.evs(T.tree.walk(List.reverse(&2, String, parts), T.Tw{inl, T.JPut{vv}, [], bad, "", [],
                  True{}}, 0))}, kk.key(gg)), kk.L(gg, rest, rows)), bo.or.tl(kk.sfx(Laws.k3.pl(rest, at, saved, []),
                    kk.tp(gg),
                  HRows{kw.evs(T.tree.walk(List.reverse(&2, String, parts), T.Tw{inl, T.JPut{vv}, [], bad, "", [],
                    True{}}, 0))}, kk.key(gg)), kk.L(gg, rest, rows), kk.kinl.pend(gg, parts, inl, saved, at,
                    rest, here, vv, bad, eo, eb, e1))),
              e1 => bo.or.tl(Bool.or(kk.pend(gg, rest, at, saved), kk.PF(gg, rest)), Bool.or(kk.sfx(Laws.k3.pl(rest, at,
                saved, []), kk.tp(gg),
                HRows{kw.evs(T.tree.walk(List.reverse(&2, String, parts), T.Tw{inl, T.JPut{vv}, [], bad, "", [],
                  True{}}, 0))}, kk.key(gg)), kk.L(gg, rest, rows)), e1),
              e1 => bo.or.tr(Bool.or(kk.pend(gg, rest, at, saved), kk.PF(gg, rest)), Bool.or(kk.sfx(Laws.k3.pl(rest, at,
                saved, []), kk.tp(gg),
                HRows{kw.evs(T.tree.walk(List.reverse(&2, String, parts), T.Tw{inl, T.JPut{vv}, [], bad, "", [],
                  True{}}, 0))}, kk.key(gg)), kk.L(gg, rest, rows)), kk.arrb(False{}, kk.sfx(Laws.k3.pl(rest, at, saved,
                    []), kk.tp(gg),
                  HRows{inl}, kk.key(gg)), kk.L(gg, rest, rows), False{}, kk.sfx(Laws.k3.pl(rest, at, saved, []),
                    kk.tp(gg),
                    HRows{kw.evs(T.tree.walk(List.reverse(&2, String, parts), T.Tw{inl, T.JPut{vv}, [], bad, "", [],
                      True{}}, 0))}, kk.key(gg)), e2 => kk.sfx.mono(Laws.k3.pl(rest, at, saved, []), kk.tp(gg),
                        HRows{inl},
                      HRows{kw.evs(T.tree.walk(List.reverse(&2, String, parts), T.Tw{inl, T.JPut{vv}, [], bad, "", [],
                        True{}}, 0))}, kk.key(gg), kw.mono(List.reverse(&2, String, parts), inl, T.JPut{vv}, bad, "",
                          [], True{}, 0,
                        kk.key(gg), eo, eb), e2), e2 => Eq.bit.absurd(&2, {kk.sfx(Laws.k3.pl(rest, at, saved, []),
                          kk.tp(gg),
                          HRows{kw.evs(T.tree.walk(List.reverse(&2, String, parts), T.Tw{inl, T.JPut{vv}, [], bad, "",
                            [], True{}}, 0))}, kk.key(gg)) == True{} : Bool}, e2),
                              kk.or0(Bool.or(kk.sfx(Laws.k3.pl(rest,
                              at, saved, []),
                            kk.tp(gg), HRows{inl}, kk.key(gg)), kk.L(gg, rest, rows)), e1))),
              e1 => bo.or.tr(Bool.or(kk.pend(gg, rest, at, saved), kk.PF(gg, rest)), Bool.or(kk.sfx(Laws.k3.pl(rest, at,
                saved, []), kk.tp(gg),
                HRows{kw.evs(T.tree.walk(List.reverse(&2, String, parts), T.Tw{inl, T.JPut{vv}, [], bad, "", [],
                  True{}}, 0))}, kk.key(gg)), kk.L(gg, rest, rows)), bo.or.tl(kk.sfx(Laws.k3.pl(rest, at, saved, []),
                    kk.tp(gg),
                  HRows{kw.evs(T.tree.walk(List.reverse(&2, String, parts), T.Tw{inl, T.JPut{vv}, [], bad, "", [],
                    True{}}, 0))}, kk.key(gg)), kk.L(gg, rest, rows), kk.kinl.vh(gg, parts, inl, saved, at, rest,
                    vv, bad, eo, eb, e1))))))

# a value taken where the state says
def kk.ttop(
  +gg: K3G,
  stack: List<&2, T.Ctx>,
  +vv: T.Val,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +lead: Bool,
  +et: {kk.Kt(gg, bad, rows, here, parts, stack, vv) == True{} : Bool}
) -> {kk.K(gg, T.take.top(stack, vv, bad, rows, heads, here, parts, back, qkind, uni, left, arrtab, lead)) == True{}
  : Bool}:
  match stack:
    case []:
      kk.troot(gg, T.tree.walk(T.path.cat(here, parts), T.Tw{rows, T.JPut{vv}, [], bad, "", heads, False{}},
        T.path.len(here, 0)), here, back, qkind, uni, left, arrtab, lead, kk.kroot.b(String.is_empty(bad), gg, bad,
          rows,
        heads, here, parts, vv, {==}, et))
    case T.CArr{+items, +saved, +at} <> +rest:
      kk.tarr(gg, items, saved, at, rest, vv, bad, rows, heads, here, parts, back, qkind, uni, left, arrtab, lead, et)
    case T.CInl{+inl, +saved, +at} <> +rest:
      kk.tinl(gg, T.tree.walk(List.reverse(&2, String, parts), T.Tw{inl, T.JPut{vv}, [], bad, "", [], True{}}, 0),
        rows, heads, at, saved, rest, back, qkind, uni, left, arrtab, lead,
        kk.kinl.b(String.is_empty(bad), gg, inl, saved, at, rest, bad, rows, here, parts, vv, {==}, et))

# LEMMA: a value taken keeps the invariant, from any state that keeps it
def kg.take(
  +gg: K3G,
  +st: T.St,
  +vv: T.Val,
  +eg: {kk.K(gg, st) == True{} : Bool}
) -> {kk.K(gg, T.val.take(st, vv)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, _f, +lex, +back, +qkind, +stack, _o, +uni, +left, +arrtab, +lead}:
      kk.ttop(gg, stack, vv, bad, rows, heads, here, parts, back, qkind, uni, left, arrtab, lead, kk.tokt(gg,
        kk.cls(lex, back), bad, rows, here, parts, stack, vv, eg))

# the fields the invariant reads, besides the lex state
type KF is Data:
  KF{bad: String, rows: List<&2, T.Val>, here: List<&2, String>, parts: List<&2, String>, stack: List<&2, T.Ctx>}

# the fields the invariant reads outside the key being read
type KF2 is Data:
  KF2{bad: String, rows: List<&2, T.Val>, stack: List<&2, T.Ctx>}

# a state's fields the invariant reads
def kk.flds(st: T.St) -> KF:
  match st:
    case T.St{bad, rows, _h, here, parts, _f, _x, _k, _q, stack, _o, _u, _l, _a, _d}:
      KF{bad, rows, here, parts, stack}

# the invariant over the fields
def kk.Kc2(+gg: K3G, cc: KC, ff: KF) -> Bool:
  match ff:
    case KF{bad, rows, here, parts, stack}:
      kk.Kc(gg, cc, bad, rows, here, parts, stack)

# the invariant, read off a state
def kk.K.u(+gg: K3G, st: T.St) -> {kk.K(gg, st) == kk.Kc2(gg, kk.cl(st), kk.flds(st)) : Bool}:
  match st:
    case T.St{_b, _r, _h, _e, _p, _f, _x, _k, _q, _s, _o, _u, _l, _a, _d}:
      {==}

# the invariant over the fields, at a class c1 allows
def kk.lf1(
  +gg: K3G,
  cc: KC,
  dd: KC,
  ff: KF,
  +e1: {kk.c1(cc, dd) == True{} : Bool},
  +ek: {kk.Kc2(gg, cc, ff) == True{} : Bool}
) -> {kk.Kc2(gg, dd, ff) == True{} : Bool}:
  match ff:
    case KF{+bad, +rows, +here, +parts, +stack}:
      kk.lift1(gg, cc, dd, bad, rows, here, parts, stack, e1, ek)

# a class that equals another
def kk.c1r(
  cc: KC,
  +d0: KC,
  +dd: KC,
  +ecl: {d0 == cc : KC},
  +ok: {kk.c1(cc, dd) == True{} : Bool}
) -> {kk.c1(d0, dd) == True{} : Bool}:
  %Equal.sym(KC, d0, cc, ecl) : {kk.c1(_, dd) == True{} : Bool}
  ok

# and for c2
def kk.c2r(
  cc: KC,
  +d0: KC,
  +dd: KC,
  +ecl: {d0 == cc : KC},
  +ok: {kk.c2(cc, dd) == True{} : Bool}
) -> {kk.c2(d0, dd) == True{} : Bool}:
  %Equal.sym(KC, d0, cc, ecl) : {kk.c2(_, dd) == True{} : Bool}
  ok

# LEMMA: a step that keeps the fields the invariant reads, between classes
# c1 allows, keeps it
def kk.l1(
  +gg: K3G,
  +st: T.St,
  +s2: T.St,
  +cc: KC,
  +ecl: {kk.cl(st) == cc : KC},
  +ok: {kk.c1(cc, kk.cl(s2)) == True{} : Bool},
  +ef: {kk.flds(s2) == kk.flds(st) : KF},
  +eg: {kk.K(gg, st) == True{} : Bool}
) -> {kk.K(gg, s2) == True{} : Bool}:
  bo.t(kk.K(gg, s2), kk.Kc2(gg, kk.cl(s2), kk.flds(s2)), kk.K.u(gg, s2), bo.t(kk.Kc2(gg, kk.cl(s2), kk.flds(s2)),
    kk.Kc2(gg, kk.cl(s2), kk.flds(st)), Equal.cong(KF, Bool, zz => kk.Kc2(gg, kk.cl(s2), zz), kk.flds(s2),
      kk.flds(st), ef),
    kk.lf1(gg, kk.cl(st), kk.cl(s2), kk.flds(st), kk.c1r(cc, kk.cl(st), kk.cl(s2), ecl, ok), Equal.trans(Bool,
      kk.Kc2(gg, kk.cl(st), kk.flds(st)), kk.K(gg, st), True{}, Equal.sym(Bool, kk.K(gg, st), kk.Kc2(gg, kk.cl(st),
        kk.flds(st)), kk.K.u(gg, st)), eg))))

# the fields outside the key
def kk.kf2(ff: KF) -> KF2:
  match ff:
    case KF{bad, rows, _h, _p, stack}:
      KF2{bad, rows, stack}

# the error of the fields outside the key
def kk.f2b(ff: KF2) -> String:
  match ff:
    case KF2{bad, _r, _s}:
      bad

# their rows
def kk.f2r(ff: KF2) -> List<&2, T.Val>:
  match ff:
    case KF2{_b, rows, _s}:
      rows

# their frames
def kk.f2s(ff: KF2) -> List<&2, T.Ctx>:
  match ff:
    case KF2{_b, _r, stack}:
      stack

# the invariant over the fields, with the key's fields changed, at a class
# c2 allows
def kk.lf2(
  +gg: K3G,
  cc: KC,
  dd: KC,
  ff: KF,
  f2: KF,
  +ef: {kk.kf2(f2) == kk.kf2(ff) : KF2},
  +e2: {kk.c2(cc, dd) == True{} : Bool},
  +ek: {kk.Kc2(gg, cc, ff) == True{} : Bool}
) -> {kk.Kc2(gg, dd, f2) == True{} : Bool}:
  match ff f2:
    case KF{+bad, +rows, +here, +parts, +stack} KF{+b2, +r2, +h2, +p2, +s2}:
      %Equal.sym(String, b2, bad, Equal.cong(KF2, String, zz => kk.f2b(zz), KF2{b2, r2, s2}, KF2{bad, rows, stack},
        ef)) : {kk.Kc(gg, dd, _, r2,
        h2, p2, s2) == True{} : Bool}
      %Equal.sym(List<&2, T.Val>, r2, rows, Equal.cong(KF2, List<&2, T.Val>, zz => kk.f2r(zz), KF2{b2, r2, s2},
        KF2{bad, rows, stack}, ef)) : {kk.Kc(gg, dd,
        bad, _, h2, p2, s2) == True{} : Bool}
      %Equal.sym(List<&2, T.Ctx>, s2, stack, Equal.cong(KF2, List<&2, T.Ctx>, zz => kk.f2s(zz), KF2{b2, r2, s2},
        KF2{bad, rows, stack}, ef)) : {kk.Kc(gg, dd,
        bad, rows, h2, p2, _) == True{} : Bool}
      kk.lift2(gg, cc, dd, bad, rows, here, parts, h2, p2, stack, e2, ek)

# LEMMA: a step that keeps the fields the invariant reads outside the key,
# between classes c2 allows, keeps it
def kk.l2(
  +gg: K3G,
  +st: T.St,
  +s2: T.St,
  +cc: KC,
  +ecl: {kk.cl(st) == cc : KC},
  +ok: {kk.c2(cc, kk.cl(s2)) == True{} : Bool},
  +ef: {kk.kf2(kk.flds(s2)) == kk.kf2(kk.flds(st)) : KF2},
  +eg: {kk.K(gg, st) == True{} : Bool}
) -> {kk.K(gg, s2) == True{} : Bool}:
  bo.t(kk.K(gg, s2), kk.Kc2(gg, kk.cl(s2), kk.flds(s2)), kk.K.u(gg, s2), kk.lf2(gg, kk.cl(st), kk.cl(s2),
    kk.flds(st), kk.flds(s2), ef, kk.c2r(cc, kk.cl(st), kk.cl(s2), ecl, ok), Equal.trans(Bool, kk.Kc2(gg, kk.cl(st),
      kk.flds(st)), kk.K(gg, st), True{}, Equal.sym(Bool, kk.K(gg, st), kk.Kc2(gg, kk.cl(st), kk.flds(st)),
        kk.K.u(gg, st)), eg)))

# a step that only moves the lex state
def kg.lex(
  +gg: K3G,
  +st: T.St,
  +lex2: T.Lex,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +cc: KC,
  +ecl: {kk.cl(st) == cc : KC},
  +ok: {kk.c1(cc, kk.cls(lex2, kk.bk(st))) == True{} : Bool}
) -> {kk.K(gg, T.st.lex(st, lex2)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      kk.l1(gg, T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead},
        T.st.lex(T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead},
          lex2), cc, ecl, ok, {==}, eg)

# a step that pushes a character
def kg.push(
  +gg: K3G,
  +st: T.St,
  +ch: Char,
  +lex2: T.Lex,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +cc: KC,
  +ecl: {kk.cl(st) == cc : KC},
  +ok: {kk.c1(cc, kk.cls(lex2, kk.bk(st))) == True{} : Bool}
) -> {kk.K(gg, T.st.push(st, ch, lex2)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      kk.l1(gg, T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead},
        T.st.push(T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead},
          ch, lex2), cc, ecl, ok, {==}, eg)

# a step that opens a quoted segment
def kg.qkey(
  +gg: K3G,
  +st: T.St,
  +kind: T.QKind,
  +lex2: T.Lex,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +cc: KC,
  +ecl: {kk.cl(st) == cc : KC},
  +ok: {kk.c1(cc, kk.cls(lex2, kk.bk(st))) == True{} : Bool}
) -> {kk.K(gg, T.lex.qkey(st, kind, lex2)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      kk.l1(gg, T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead},
        T.lex.qkey(T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead},
          kind, lex2), cc, ecl, ok, {==}, eg)

# a step that holds a character
def kg.hold(
  +gg: K3G,
  +st: T.St,
  +lex2: T.Lex,
  +ch: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +cc: KC,
  +ecl: {kk.cl(st) == cc : KC},
  +ok: {kk.c1(cc, kk.cls(lex2, lex2)) == True{} : Bool}
) -> {kk.K(gg, T.st.hold(st, lex2, ch)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      kk.l1(gg, T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead},
        T.st.hold(T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead},
          lex2, ch), cc, ecl, ok, {==}, eg)

# a comment starts
def kg.com(
  +gg: K3G,
  +st: T.St,
  +back2: T.Lex,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +cc: KC,
  +ecl: {kk.cl(st) == cc : KC},
  +ok: {kk.c1(cc, kk.cls0(back2)) == True{} : Bool}
) -> {kk.K(gg, T.com.enter(st, back2)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      kk.l1(gg, T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead},
        T.com.enter(T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead},
          back2), cc, ecl, ok, {==}, eg)

# a step that ends a segment
def kg.seg(
  +gg: K3G,
  +st: T.St,
  +lex2: T.Lex,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +cc: KC,
  +ecl: {kk.cl(st) == cc : KC},
  +ok: {kk.c2(cc, kk.cls(lex2, kk.bk(st))) == True{} : Bool}
) -> {kk.K(gg, T.seg.push(st, lex2)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      kk.l2(gg, T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead},
        T.seg.push(T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead},
          lex2), cc, ecl, ok, {==}, eg)

# a key starts clear
def kg.kclear(
  +gg: K3G,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +cc: KC,
  +ecl: {kk.cl(st) == cc : KC},
  +ok: {kk.c2(cc, kk.cls0(T.LKey{})) == True{} : Bool}
) -> {kk.K(gg, T.lex.key.clear(st)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      kk.l2(gg, T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead},
        T.lex.key.clear(T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab,
          lead}), cc, ecl, ok, {==}, eg)

# a header starts clear
def kg.bracket(
  +gg: K3G,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +cc: KC,
  +ecl: {kk.cl(st) == cc : KC},
  +ok: {kk.c2(cc, kk.cls0(T.LHead{})) == True{} : Bool}
) -> {kk.K(gg, T.lex.bracket(st)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      kk.l2(gg, T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead},
        T.lex.bracket(T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab,
          lead}), cc, ecl, ok, {==}, eg)

# a step that fails keeps the invariant
def kg.err(
  +gg: K3G,
  +st: T.St,
  +why: String,
  +ew: {String.is_empty(why) == False{} : Bool},
  +_eg: {kk.K(gg, st) == True{} : Bool}
) -> {kk.K(gg, T.st.err(st, why)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      bo.or.tl(Bool.not(String.is_empty(T.err.first(bad, why))), Bool.and(Bool.or(Bool.not(kk.ish(kk.cls0(T.LSink{}))),
        List.is_empty(&2, T.Ctx, stack)), Bool.or(Bool.and(kk.isv(kk.cls0(T.LSink{})), kk.pend(gg, stack, here,
          parts)), Bool.or(kk.PF(gg, stack), kk.L(gg, stack, rows)))), Equal.cong(Bool, Bool, zz => Bool.not(zz),
            String.is_empty(T.err.first(bad, why)), False{}, kw.efne(bad, why, ew)))

# a held character keeps the invariant
def kg.holdon(
  +gg: K3G,
  +st: T.St,
  +ch: Char,
  +eg: {kk.K(gg, st) == True{} : Bool}
) -> {kk.K(gg, T.bare.hold.on(st, ch)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      eg

# a state's lex state
def kk.lx(st: T.St) -> T.Lex:
  match st:
    case T.St{_b, _r, _h, _e, _p, _f, lex, _k, _q, _s, _o, _u, _l, _a, _d}:
      lex

# a newline read again in the state a comment returns to
def kg.comnl(
  +gg: K3G,
  +st: T.St,
  +ch: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +el: {kk.lx(st) == T.LCom{} : T.Lex}
) -> {kk.K(gg, T.lex.com.nl(st, ch)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      %Equal.sym(KC, kk.cls(back, back), kk.cls0(back), kk.clsbb(back)) : {kk.Kc(gg, _, bad, rows, here, parts, stack)
        == True{} : Bool}
      Equal.trans(Bool, kk.Kc(gg, kk.cls(T.LCom{}, back), bad, rows, here, parts, stack), kk.Kc(gg, kk.cls(lex, back),
        bad, rows, here, parts, stack), True{}, Equal.cong(T.Lex, Bool, zz => kk.Kc(gg, kk.cls(zz, back), bad, rows,
          here, parts, stack), T.LCom{}, lex, Equal.sym(T.Lex, lex, T.LCom{}, el)), eg)

# pending, pending below or held, and so pending in a new frame or held
def kk.pushb2(
  pp: Bool,
  ff: Bool,
  vv: Bool,
  ll: Bool,
  +fh: Bool,
  +ee: {Bool.or(Bool.and(vv, pp), Bool.or(ff, ll)) == True{} : Bool}
) -> {Bool.or(Bool.or(pp, ff), Bool.or(fh, ll)) == True{} : Bool}:
  match pp:
    case True{}:
      {==}
    case False{}:
      match ff:
        case True{}:
          {==}
        case False{}:
          match vv:
            case True{}:
              bo.or.tr(fh, ll, ee)
            case False{}:
              bo.or.tr(fh, ll, ee)

# an array opens a frame
def kg.array(
  +gg: K3G,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool}
) -> {kk.K(gg, T.lex.array(st)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      kk.bimp(Bool.not(String.is_empty(bad)), Bool.and(Bool.or(Bool.not(kk.ish(kk.cls(lex, back))), List.is_empty(&2,
        T.Ctx, stack)), Bool.or(Bool.and(kk.isv(kk.cls(lex, back)), kk.pend(gg, stack, here, parts)), Bool.or(kk.PF(gg,
          stack), kk.L(gg, stack, rows)))), Bool.or(Bool.or(kk.pend(gg, stack, here, parts), kk.PF(gg, stack)),
            Bool.or(kk.fh(gg, T.CArr{[], parts, here}, stack), kk.L(gg, stack, rows))),
              e1 => kk.pushb2(kk.pend(gg, stack, here, parts), kk.PF(gg,
              stack), kk.isv(kk.cls(lex, back)), kk.L(gg, stack, rows), kk.fh(gg, T.CArr{[],
                parts, here}, stack), M17.gd.r(Bool.or(Bool.not(kk.ish(kk.cls(lex, back))), List.is_empty(&2, T.Ctx,
                  stack)), Bool.or(Bool.and(kk.isv(kk.cls(lex, back)), kk.pend(gg, stack, here, parts)),
                    Bool.or(kk.PF(gg, stack), kk.L(gg, stack, rows))), e1)), eg)

# an inline table opens a frame
def kg.inline(
  +gg: K3G,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool}
) -> {kk.K(gg, T.lex.inline(st)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      kk.bimp(Bool.not(String.is_empty(bad)), Bool.and(Bool.or(Bool.not(kk.ish(kk.cls(lex, back))), List.is_empty(&2,
        T.Ctx, stack)), Bool.or(Bool.and(kk.isv(kk.cls(lex, back)), kk.pend(gg, stack, here, parts)), Bool.or(kk.PF(gg,
          stack), kk.L(gg, stack, rows)))), Bool.or(Bool.or(kk.pend(gg, stack, here, parts), kk.PF(gg, stack)),
            Bool.or(kk.fh(gg, T.CInl{[], parts, here}, stack), kk.L(gg, stack, rows))),
              e1 => kk.pushb2(kk.pend(gg, stack, here, parts), kk.PF(gg,
              stack), kk.isv(kk.cls(lex, back)), kk.L(gg, stack, rows), kk.fh(gg, T.CInl{[],
                parts, here}, stack), M17.gd.r(Bool.or(Bool.not(kk.ish(kk.cls(lex, back))), List.is_empty(&2, T.Ctx,
                  stack)), Bool.or(Bool.and(kk.isv(kk.cls(lex, back)), kk.pend(gg, stack, here, parts)),
                    Bool.or(kk.PF(gg, stack), kk.L(gg, stack, rows))), e1)), eg)

# a failed step's state keeps the invariant
def kk.kerr(
  +gg: K3G,
  +bad: String,
  +why: String,
  +rows: List<&2, T.Val>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  +stack: List<&2, T.Ctx>,
  +lx: T.Lex,
  +bk: T.Lex,
  +ew: {String.is_empty(why) == False{} : Bool}
) -> {kk.Kc(gg, kk.cls(lx, bk), T.err.first(bad, why), rows, here, parts, stack) == True{} : Bool}:
  bo.or.tl(Bool.not(String.is_empty(T.err.first(bad, why))), Bool.and(Bool.or(Bool.not(kk.ish(kk.cls(lx, bk))),
    List.is_empty(&2, T.Ctx, stack)), Bool.or(Bool.and(kk.isv(kk.cls(lx, bk)), kk.pend(gg, stack, here, parts)),
      Bool.or(kk.PF(gg, stack), kk.L(gg, stack, rows)))), Equal.cong(Bool, Bool, zz => Bool.not(zz),
        String.is_empty(T.err.first(bad, why)), False{}, kw.efne(bad, why, ew)))

# the same, the value's key read off
def kk.popb2(
  pp: Bool,
  ff: Bool,
  fi: Bool,
  +ll: Bool,
  +ww: Bool,
  gw: @e1: {fi == True{} : Bool} -> {ww == True{} : Bool},
  +ee: {Bool.or(Bool.or(pp, ff), Bool.or(fi, ll)) == True{} : Bool}
) -> {Bool.or(pp, Bool.or(ff, Bool.or(ll, ww))) == True{} : Bool}:
  match pp:
    case True{}:
      {==}
    case False{}:
      match ff:
        case True{}:
          {==}
        case False{}:
          match fi:
            case True{}:
              bo.or.tr(ll, ww, gw({==}))
            case False{}:
              bo.or.tl(ll, ww, ee)

# a frame closed: pending below it or held, or held by it and so by its value
def kk.popb(
  vp: Bool,
  pp: Bool,
  ff: Bool,
  fi: Bool,
  +ll: Bool,
  +ww: Bool,
  +evp: {vp == False{} : Bool},
  gw: @e1: {fi == True{} : Bool} -> {ww == True{} : Bool},
  +ee: {Bool.or(vp, Bool.or(Bool.or(pp, ff), Bool.or(fi, ll))) == True{} : Bool}
) -> {Bool.or(pp, Bool.or(ff, Bool.or(ll, ww))) == True{} : Bool}:
  kk.popb2(pp, ff, fi, ll, ww, gw, Equal.trans(Bool, Bool.or(Bool.or(pp, ff), Bool.or(fi, ll)), Bool.or(vp,
    Bool.or(Bool.or(pp, ff), Bool.or(fi, ll))), True{}, Equal.cong(Bool, Bool, zz => Bool.or(zz, Bool.or(Bool.or(pp,
      ff), Bool.or(fi, ll))), False{}, vp, Equal.sym(Bool, vp, False{}, evp)), ee))

# and with False
def kk.andf(bb: Bool) -> {Bool.and(bb, False{}) == False{} : Bool}:
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# not a value's class, and so no key pending as a value
def kk.andv(
  cc: KC,
  +xx: Bool,
  +ev: {kk.isv(cc) == False{} : Bool}
) -> {Bool.and(kk.isv(cc), xx) == False{} : Bool}:
  %Equal.sym(Bool, kk.isv(cc), False{}, ev) : {Bool.and(_, xx) == False{} : Bool}
  {==}

# an array closed
def kk.arrtop(
  +gg: K3G,
  stack: List<&2, T.Ctx>,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +lead: Bool,
  +cc: KC,
  +h0: List<&2, String>,
  +p0: List<&2, String>,
  +ek: {kk.Kc(gg, cc, bad, rows, h0, p0, stack) == True{} : Bool}
) -> {kk.K(gg, T.arr.top(stack, bad, rows, heads, back, qkind, uni, left, arrtab, lead)) == True{} : Bool}:
  match stack:
    case T.CArr{+xs, +parts, +here} <> +rest:
      kk.ttop(gg, rest, T.VArr{List.reverse(&2, T.Val, xs)}, bad, rows, heads, here, parts, back, qkind, uni, left,
        arrtab, lead,
        kk.bimp(Bool.not(String.is_empty(bad)), Bool.and(Bool.or(Bool.not(kk.ish(cc)), False{}),
          Bool.or(Bool.and(kk.isv(cc),
          False{}), Bool.or(Bool.or(kk.pend(gg, rest, here, parts), kk.PF(gg, rest)), Bool.or(kk.sfx(Laws.k3.pl(rest,
            here,
            parts, []), kk.tp(gg), HItems{xs}, kk.key(gg)), kk.L(gg, rest, rows))))), Bool.or(kk.pend(gg, rest, here,
              parts),
              Bool.or(kk.PF(gg, rest), Bool.or(kk.L(gg, rest, rows), kk.sfx(Laws.k3.pl(rest, here, parts, []),
                kk.tp(gg),
                HVal{T.VArr{List.reverse(&2, T.Val, xs)}}, kk.key(gg))))), e1 => kk.popb(Bool.and(kk.isv(cc),
                  False{}), kk.pend(gg, rest,
                  here, parts), kk.PF(gg, rest),
                  kk.sfx(Laws.k3.pl(rest, here, parts, []), kk.tp(gg), HItems{xs}, kk.key(gg)), kk.L(gg, rest, rows),
                    kk.sfx(Laws.k3.pl(rest, here, parts, []), kk.tp(gg), HVal{T.VArr{List.reverse(&2, T.Val, xs)}},
                      kk.key(gg)), kk.andf(kk.isv(cc)), e2 =>
                      kk.sfx.mono(Laws.k3.pl(rest, here, parts, []), kk.tp(gg), HItems{xs}, HVal{T.VArr{List.reverse(&2,
                        T.Val, xs)}}, kk.key(gg), +q0 => e3 =>
                        bo.t(kh.S(List.reverse(&2, T.Val, xs), q0, kk.key(gg)), kh.S(xs, q0, kk.key(gg)),
                          kh.slrev(SlS{q0}, xs, kk.key(gg)), e3), e2), M17.gd.r(Bool.or(Bool.not(kk.ish(cc)), False{}),
                            Bool.or(Bool.and(kk.isv(cc), False{}),
                          Bool.or(Bool.or(kk.pend(gg, rest, here, parts), kk.PF(gg, rest)),
                            Bool.or(kk.sfx(Laws.k3.pl(rest,
                            here, parts, []), kk.tp(gg), HItems{xs}, kk.key(gg)), kk.L(gg, rest, rows)))), e1)), ek))
    case T.CInl{_i, _p, _h} <> _t:
      kk.kerr(gg, bad, "unclosed", rows, [], [], [], T.LSink{}, back, {==})
    case []:
      kk.kerr(gg, bad, "unclosed", rows, [], [], [], T.LSink{}, back, {==})

# an inline table closed
def kk.inltop(
  +gg: K3G,
  stack: List<&2, T.Ctx>,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +uni: U32,
  +left: U32,
  +arrtab: Bool,
  +lead: Bool,
  +cc: KC,
  +h0: List<&2, String>,
  +p0: List<&2, String>,
  +env: {kk.isv(cc) == False{} : Bool},
  +ek: {kk.Kc(gg, cc, bad, rows, h0, p0, stack) == True{} : Bool}
) -> {kk.K(gg, T.inl.top(stack, bad, rows, heads, back, qkind, uni, left, arrtab, lead)) == True{} : Bool}:
  match stack:
    case T.CInl{+xs, +parts, +here} <> +rest:
      kk.ttop(gg, rest, T.VInl{T.inl.seal(xs)}, bad, rows, heads, here, parts, back, qkind, uni, left, arrtab, lead,
        kk.bimp(Bool.not(String.is_empty(bad)), Bool.and(Bool.or(Bool.not(kk.ish(cc)), False{}),
          Bool.or(Bool.and(kk.isv(cc), kk.pend2(gg, T.CInl{xs, parts, here} <> rest, h0, p0)),
            Bool.or(Bool.or(kk.pend(gg, rest, here, parts), kk.PF(gg, rest)), Bool.or(kk.sfx(Laws.k3.pl(rest, here,
            parts, []), kk.tp(gg), HRows{xs}, kk.key(gg)), kk.L(gg, rest, rows))))), Bool.or(kk.pend(gg, rest, here,
              parts),
              Bool.or(kk.PF(gg, rest), Bool.or(kk.L(gg, rest, rows), kk.sfx(Laws.k3.pl(rest, here, parts, []),
                kk.tp(gg),
                HVal{T.VInl{T.inl.seal(xs)}}, kk.key(gg))))), e1 => kk.popb(Bool.and(kk.isv(cc), kk.pend2(gg,
                  T.CInl{xs, parts, here} <> rest, h0, p0)), kk.pend(gg, rest, here,
                  parts), kk.PF(gg, rest),
                  kk.sfx(Laws.k3.pl(rest, here, parts, []), kk.tp(gg), HRows{xs}, kk.key(gg)), kk.L(gg, rest, rows),
                    kk.sfx(Laws.k3.pl(rest, here, parts, []), kk.tp(gg), HVal{T.VInl{T.inl.seal(xs)}}, kk.key(gg)),
                      kk.andv(cc, kk.pend2(gg, T.CInl{xs, parts, here} <> rest, h0, p0), env), e2 =>
                      kk.sfx.mono(Laws.k3.pl(rest, here, parts, []), kk.tp(gg), HRows{xs}, HVal{T.VInl{T.inl.seal(xs)}},
                        kk.key(gg), +q0 => e3 =>
                        bo.t(Laws.k3.has(T.inl.seal(xs), q0, kk.key(gg)), Laws.k3.has(xs, q0, kk.key(gg)), kh.hi(q0,
                          xs, kk.key(gg), nm => kh.inleq(xs, SlF{nm}, kk.key(gg)), nm => qq => kh.inleq(xs, SlA{nm,
                            qq}, kk.key(gg))), e3), e2), M17.gd.r(Bool.or(Bool.not(kk.ish(cc)), False{}),
                              Bool.or(Bool.and(kk.isv(cc), kk.pend2(gg, T.CInl{xs, parts, here} <> rest, h0, p0)),
                          Bool.or(Bool.or(kk.pend(gg, rest, here, parts), kk.PF(gg, rest)),
                            Bool.or(kk.sfx(Laws.k3.pl(rest,
                            here, parts, []), kk.tp(gg), HRows{xs}, kk.key(gg)), kk.L(gg, rest, rows)))), e1)), ek))
    case T.CArr{_i, _p, _h} <> _t:
      kk.kerr(gg, bad, "unclosed", rows, [], [], [], T.LSink{}, back, {==})
    case []:
      kk.kerr(gg, bad, "unclosed", rows, [], [], [], T.LSink{}, back, {==})

# a class equal to one not a value's is not
def kk.isvr(
  cc: KC,
  +d0: KC,
  +ecl: {d0 == cc : KC},
  +ev: {kk.isv(cc) == False{} : Bool}
) -> {kk.isv(d0) == False{} : Bool}:
  %Equal.sym(KC, d0, cc, ecl) : {kk.isv(_) == False{} : Bool}
  ev

# ] closes an array
def kg.arrclose(
  +gg: K3G,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool}
) -> {kk.K(gg, T.arr.close(st)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      kk.arrtop(gg, stack, bad, rows, heads, back, qkind, uni, left, arrtab, lead, kk.cls(lex, back), here, parts, eg)

# } closes an inline table
def kg.inlclose(
  +gg: K3G,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +cc: KC,
  +ecl: {kk.cl(st) == cc : KC},
  +env: {kk.isv(cc) == False{} : Bool}
) -> {kk.K(gg, T.inl.close(st)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      kk.inltop(gg, stack, bad, rows, heads, back, qkind, uni, left, arrtab, lead, kk.cls(lex, back), here, parts,
        kk.isvr(cc, kk.cls(lex, back), ecl, env), eg)

# a step that keeps the class and the fields the invariant reads keeps it
def kk.l0(
  +gg: K3G,
  +st: T.St,
  +s2: T.St,
  +ec: {kk.cl(s2) == kk.cl(st) : KC},
  +ef: {kk.flds(s2) == kk.flds(st) : KF},
  +eg: {kk.K(gg, st) == True{} : Bool}
) -> {kk.K(gg, s2) == True{} : Bool}:
  bo.t(kk.K(gg, s2), kk.Kc2(gg, kk.cl(s2), kk.flds(s2)), kk.K.u(gg, s2), bo.t(kk.Kc2(gg, kk.cl(s2), kk.flds(s2)),
    kk.Kc2(gg, kk.cl(st), kk.flds(st)), Equal.trans(Bool, kk.Kc2(gg, kk.cl(s2), kk.flds(s2)), kk.Kc2(gg, kk.cl(st),
      kk.flds(s2)), kk.Kc2(gg, kk.cl(st), kk.flds(st)), Equal.cong(KC, Bool, zz => kk.Kc2(gg, zz, kk.flds(s2)),
        kk.cl(s2), kk.cl(st), ec), Equal.cong(KF, Bool, zz => kk.Kc2(gg, kk.cl(st), zz), kk.flds(s2), kk.flds(st),
          ef)), Equal.trans(Bool, kk.Kc2(gg, kk.cl(st), kk.flds(st)), kk.K(gg, st), True{}, Equal.sym(Bool, kk.K(gg,
            st), kk.Kc2(gg, kk.cl(st), kk.flds(st)), kk.K.u(gg, st)), eg)))

# a multiline string starts
def kg.multi(
  +gg: K3G,
  +st: T.St,
  +kind: T.QKind,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.multi(st, kind)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      kk.l1(gg, T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead},
        T.lex.multi(T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead},
          kind), KcV{}, ecl, {==}, {==}, eg)

# closing quotes counted
def kg.mq(
  +gg: K3G,
  +st: T.St,
  +nn: U32,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.mq(st, nn)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      kk.l1(gg, T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead},
        T.lex.mq(T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead},
          nn), KcV{}, ecl, {==}, {==}, eg)

# a closing delimiter read
def kg.mqshut(
  +gg: K3G,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.mq.shut(st)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      kk.l1(gg, T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead},
        T.lex.mq.shut(T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab,
          lead}), KcV{}, ecl, {==}, {==}, eg)

# quotes that were no closer
def kg.mqback(
  +gg: K3G,
  +st: T.St,
  +cc: Char,
  +b2: List<&2, Char>,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.mq.back(st, cc, b2)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      kk.l1(gg, T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead},
        T.lex.mq.back(T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab,
          lead}, cc, b2), KcV{}, ecl, {==}, {==}, eg)

# a datetime's space and digit
def kg.datedig(
  +gg: K3G,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.date.digit(st, cc)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      kk.l1(gg, T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead},
        T.lex.date.digit(T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab,
          lead}, cc), KcV{}, ecl, {==}, {==}, eg)

# a folded newline seen
def kg.foldsaw(
  +gg: K3G,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool}
) -> {kk.K(gg, T.lex.fold.saw(st)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      kk.l0(gg, T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead},
        T.lex.fold.saw(T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab,
          lead}), {==}, {==}, eg)

# a quote after a closer
def kg.mqmore(
  +gg: K3G,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool}
) -> {kk.K(gg, T.lex.mq.more(st, cc)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      kk.l0(gg, T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead},
        T.lex.mq.more(T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab,
          lead}, cc), {==}, {==}, eg)

# a comment in a header, or a refusal
def kg.hash(
  +gg: K3G,
  hash: Bool,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.head.hash(hash, st)) == True{} : Bool}:
  match hash:
    case True{}:
      match st:
        case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
          +lead}:
          kk.l1(gg, T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead},
            T.lex.head.hash(True{}, T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left,
              arrtab, lead}), KcH{}, ecl, {==}, {==}, eg)
    case False{}:
      kg.err(gg, st, "invalid header", {==}, eg)

# [[ marks an array of tables once
def kg.br2(
  +gg: K3G,
  once: Bool,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.head.br2(once, st)) == True{} : Bool}:
  match once:
    case False{}:
      kg.err(gg, st, "invalid header", {==}, eg)
    case True{}:
      match st:
        case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
          +lead}:
          kk.l1(gg, T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead},
            T.lex.head.br2(True{}, T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left,
              arrtab, lead}), KcH{}, ecl, {==}, {==}, eg)

# a quoted segment's escape: a basic segment escapes, a literal one keeps the
# backslash
def kg.kqesc(
  +gg: K3G,
  basic: Bool,
  +st: T.St,
  +stay: T.Lex,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +cc: KC,
  +ecl: {kk.cl(st) == cc : KC},
  +os: {kk.c1(cc, kk.cls(stay, kk.bk(st))) == True{} : Bool},
  +oe: {kk.c1(cc, kk.cls(T.lex.esc.lex(stay), stay)) == True{} : Bool}
) -> {kk.K(gg, T.lex.kq.esc(basic, st, stay)) == True{} : Bool}:
  match basic:
    case True{}:
      match st:
        case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
          +lead}:
          kk.l1(gg, T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead},
            T.lex.kq.esc(True{}, T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left,
              arrtab, lead}, stay), cc, ecl, oe, {==}, eg)
    case False{}:
      kg.push(gg, st, '\\', stay, eg, cc, ecl, os)

# a quoted segment's character
def kg.kqch(
  +gg: K3G,
  bad: Bool,
  +st: T.St,
  +ch: Char,
  +stay: T.Lex,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +cc: KC,
  +ecl: {kk.cl(st) == cc : KC},
  +os: {kk.c1(cc, kk.cls(stay, kk.bk(st))) == True{} : Bool}
) -> {kk.K(gg, T.lex.kq.char.go(bad, st, ch, stay)) == True{} : Bool}:
  match bad:
    case True{}:
      kg.err(gg, st, "invalid control", {==}, eg)
    case False{}:
      kg.push(gg, st, ch, stay, eg, cc, ecl, os)

# a newline in a quoted segment
def kg.kqnl(
  +gg: K3G,
  nl: Bool,
  +st: T.St,
  +ch: Char,
  +stay: T.Lex,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +cc: KC,
  +ecl: {kk.cl(st) == cc : KC},
  +os: {kk.c1(cc, kk.cls(stay, kk.bk(st))) == True{} : Bool}
) -> {kk.K(gg, T.lex.kq.nl(nl, st, ch, stay)) == True{} : Bool}:
  match nl:
    case True{}:
      kg.err(gg, st, "newline in key", {==}, eg)
    case False{}:
      kg.kqch(gg, T.str.bad(Char.to_u32(ch), False{}), st, ch, stay, eg, cc, ecl, os)

# a backslash in a quoted segment
def kg.kqbs(
  +gg: K3G,
  bs: Bool,
  +basic: Bool,
  +nl: Bool,
  +st: T.St,
  +ch: Char,
  +stay: T.Lex,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +cc: KC,
  +ecl: {kk.cl(st) == cc : KC},
  +os: {kk.c1(cc, kk.cls(stay, kk.bk(st))) == True{} : Bool},
  +oe: {kk.c1(cc, kk.cls(T.lex.esc.lex(stay), stay)) == True{} : Bool}
) -> {kk.K(gg, T.lex.kq.bs(bs, basic, nl, st, ch, stay)) == True{} : Bool}:
  match bs:
    case True{}:
      kg.kqesc(gg, basic, st, stay, eg, cc, ecl, os, oe)
    case False{}:
      kg.kqnl(gg, nl, st, ch, stay, eg, cc, ecl, os)

# the closer, an escape, or a character
def kg.kqgo(
  +gg: K3G,
  quote: Bool,
  +bs: Bool,
  +basic: Bool,
  +nl: Bool,
  +st: T.St,
  +ch: Char,
  +done: T.Lex,
  +stay: T.Lex,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +cc: KC,
  +ecl: {kk.cl(st) == cc : KC},
  +od: {kk.c2(cc, kk.cls(done, kk.bk(st))) == True{} : Bool},
  +os: {kk.c1(cc, kk.cls(stay, kk.bk(st))) == True{} : Bool},
  +oe: {kk.c1(cc, kk.cls(T.lex.esc.lex(stay), stay)) == True{} : Bool}
) -> {kk.K(gg, T.lex.kq.go(quote, bs, basic, nl, st, ch, done, stay)) == True{} : Bool}:
  match quote:
    case True{}:
      kg.seg(gg, st, done, eg, cc, ecl, od)
    case False{}:
      kg.kqbs(gg, bs, basic, nl, st, ch, stay, eg, cc, ecl, os, oe)

# a quoted segment, a key's or a header's
def kg.kq(
  +gg: K3G,
  +st: T.St,
  +ch: Char,
  +done: T.Lex,
  +stay: T.Lex,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +cc: KC,
  +ecl: {kk.cl(st) == cc : KC},
  +od: {kk.c2(cc, kk.cls(done, kk.bk(st))) == True{} : Bool},
  +os: {kk.c1(cc, kk.cls(stay, kk.bk(st))) == True{} : Bool},
  +oe: {kk.c1(cc, kk.cls(T.lex.esc.lex(stay), stay)) == True{} : Bool}
) -> {kk.K(gg, T.lex.kq(st, ch, done, stay)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      kg.kqgo(gg, Char.is_eq(ch, T.q.char(qkind)), Char.is_eq(ch, '\\'), T.q.basic(qkind), T.ch.nl(ch), T.St{bad,
        rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead}, ch, done,
        stay, eg, cc, ecl, od, os, oe)

# a \u escape finished
def kg.ufin(
  +gg: K3G,
  ok: Bool,
  +st: T.St,
  +uu: U32,
  +back2: T.Lex,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +cc: KC,
  +ecl: {kk.cl(st) == cc : KC},
  +od: {kk.c1(cc, kk.cls(back2, kk.bk(st))) == True{} : Bool}
) -> {kk.K(gg, T.uni.finish(ok, st, uu, back2)) == True{} : Bool}:
  match ok:
    case True{}:
      match st:
        case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
          +lead}:
          kk.l1(gg, T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead},
            T.uni.finish.on(T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab,
              lead}, uu, back2), cc, ecl, od, {==}, eg)
    case False{}:
      kg.err(gg, st, "invalid escape", {==}, eg)

# a \u escape's digit, the last or not
def kg.unext(
  +gg: K3G,
  last: Bool,
  +st: T.St,
  +uu: U32,
  +back2: T.Lex,
  +left2: U32,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +cc: KC,
  +ecl: {kk.cl(st) == cc : KC},
  +od: {kk.c1(cc, kk.cls(back2, kk.bk(st))) == True{} : Bool}
) -> {kk.K(gg, T.uni.next(last, st, uu, back2, left2)) == True{} : Bool}:
  match last:
    case True{}:
      kg.ufin(gg, T.uni.ok(uu), st, uu, back2, eg, cc, ecl, od)
    case False{}:
      match st:
        case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
          +lead}:
          kk.l0(gg, T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead},
            T.uni.next.more(T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab,
              lead}, uu, left2), {==}, {==}, eg)

# a \u escape's digit
def kg.ugo(
  +gg: K3G,
  ok: Bool,
  +st: T.St,
  +ch: Char,
  +back2: T.Lex,
  +u0: U32,
  +left2: U32,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +cc: KC,
  +ecl: {kk.cl(st) == cc : KC},
  +od: {kk.c1(cc, kk.cls(back2, kk.bk(st))) == True{} : Bool}
) -> {kk.K(gg, T.uni.go(ok, st, ch, back2, u0, left2)) == True{} : Bool}:
  match ok:
    case False{}:
      kg.err(gg, st, "invalid escape", {==}, eg)
    case True{}:
      kg.unext(gg, U32.is_eq(left2, 1), st, U32.add(U32.mul(u0, 16), T.dig.val(ch)), back2, left2, eg, cc, ecl, od)

# a hex digit of a \u escape
def kg.uni(
  +gg: K3G,
  +st: T.St,
  +ch: Char,
  +back2: T.Lex,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +cc: KC,
  +ecl: {kk.cl(st) == cc : KC},
  +od: {kk.c1(cc, kk.cls(back2, kk.bk(st))) == True{} : Bool}
) -> {kk.K(gg, T.uni.step(st, ch, back2)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      kg.ugo(gg, T.dig.ok(T.dig.val(ch), 16), T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold,
        uni, left, arrtab, lead}, ch, back2, uni, left, eg, cc, ecl, od)

# a folded newline is a string's only
def kk.fok(+cc: KC, back2: T.Lex) -> Bool:
  match back2:
    case T.LStr{}:
      kk.c1(cc, KcV{})
    case _b:
      True{}

# a line-ending backslash belongs to a string only
def kg.fold(
  +gg: K3G,
  back2: T.Lex,
  +st: T.St,
  +saw: Bool,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +cc: KC,
  +ecl: {kk.cl(st) == cc : KC},
  +of: {kk.fok(cc, back2) == True{} : Bool}
) -> {kk.K(gg, T.esc.fold.use(back2, st, saw)) == True{} : Bool}:
  match back2:
    case T.LStr{}:
      match st:
        case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, qkind, +stack, +hold, +uni, +left, +arrtab,
          +lead}:
          match qkind:
            case T.QMulti{}:
              kk.l1(gg, T.St{bad, rows, heads, here, parts, buf, lex, back, T.QMulti{}, stack, hold, uni, left, arrtab,
                lead}, T.esc.fold.on(T.St{bad, rows, heads, here, parts, buf, lex, back, T.QMulti{}, stack, hold, uni,
                left, arrtab, lead}, saw), cc, ecl, of, {==}, eg)
            case T.QMultiLit{}:
              kk.l1(gg, T.St{bad, rows, heads, here, parts, buf, lex, back, T.QMultiLit{}, stack, hold, uni, left,
                arrtab, lead}, T.esc.fold.on(T.St{bad, rows, heads, here, parts, buf, lex, back, T.QMultiLit{}, stack,
                hold, uni, left, arrtab, lead}, saw), cc, ecl, of, {==}, eg)
            case T.QBasic{}:
              kg.err(gg, T.St{bad, rows, heads, here, parts, buf, lex, back, T.QBasic{}, stack, hold, uni, left,
                arrtab, lead}, "invalid escape", {==}, eg)
            case T.QLit{}:
              kg.err(gg, T.St{bad, rows, heads, here, parts, buf, lex, back, T.QLit{}, stack, hold, uni, left,
                arrtab, lead}, "invalid escape", {==}, eg)
    case T.LTop{}:
      kg.err(gg, st, "invalid escape", {==}, eg)
    case T.LLine{}:
      kg.err(gg, st, "invalid escape", {==}, eg)
    case T.LKey{}:
      kg.err(gg, st, "invalid escape", {==}, eg)
    case T.LKeyDot{}:
      kg.err(gg, st, "invalid escape", {==}, eg)
    case T.LAfter{}:
      kg.err(gg, st, "invalid escape", {==}, eg)
    case T.LKeyQ{}:
      kg.err(gg, st, "invalid escape", {==}, eg)
    case T.LKeyE{}:
      kg.err(gg, st, "invalid escape", {==}, eg)
    case T.LKeyU{}:
      kg.err(gg, st, "invalid escape", {==}, eg)
    case T.LVal{}:
      kg.err(gg, st, "invalid escape", {==}, eg)
    case T.LQ{}:
      kg.err(gg, st, "invalid escape", {==}, eg)
    case T.LQ2{}:
      kg.err(gg, st, "invalid escape", {==}, eg)
    case T.LEsc{}:
      kg.err(gg, st, "invalid escape", {==}, eg)
    case T.LUni{}:
      kg.err(gg, st, "invalid escape", {==}, eg)
    case T.LFold{}:
      kg.err(gg, st, "invalid escape", {==}, eg)
    case T.LMq{}:
      kg.err(gg, st, "invalid escape", {==}, eg)
    case T.LMqEnd{}:
      kg.err(gg, st, "invalid escape", {==}, eg)
    case T.LTrim{}:
      kg.err(gg, st, "invalid escape", {==}, eg)
    case T.LTrim2{}:
      kg.err(gg, st, "invalid escape", {==}, eg)
    case T.LBare{}:
      kg.err(gg, st, "invalid escape", {==}, eg)
    case T.LDate{}:
      kg.err(gg, st, "invalid escape", {==}, eg)
    case T.LCom{}:
      kg.err(gg, st, "invalid escape", {==}, eg)
    case T.LHead{}:
      kg.err(gg, st, "invalid escape", {==}, eg)
    case T.LHeadGap{}:
      kg.err(gg, st, "invalid escape", {==}, eg)
    case T.LHeadDot{}:
      kg.err(gg, st, "invalid escape", {==}, eg)
    case T.LHeadQ{}:
      kg.err(gg, st, "invalid escape", {==}, eg)
    case T.LHeadE{}:
      kg.err(gg, st, "invalid escape", {==}, eg)
    case T.LHeadU{}:
      kg.err(gg, st, "invalid escape", {==}, eg)
    case T.LHeadR{}:
      kg.err(gg, st, "invalid escape", {==}, eg)
    case T.LArr{}:
      kg.err(gg, st, "invalid escape", {==}, eg)
    case T.LArrC{}:
      kg.err(gg, st, "invalid escape", {==}, eg)
    case T.LInl{}:
      kg.err(gg, st, "invalid escape", {==}, eg)
    case T.LInlK{}:
      kg.err(gg, st, "invalid escape", {==}, eg)
    case T.LInlC{}:
      kg.err(gg, st, "invalid escape", {==}, eg)
    case T.LSink{}:
      kg.err(gg, st, "invalid escape", {==}, eg)

# an escape applied
def kg.esc(
  +gg: K3G,
  ee: T.Esc,
  +st: T.St,
  +back2: T.Lex,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +cc: KC,
  +ecl: {kk.cl(st) == cc : KC},
  +op: {kk.c1(cc, kk.cls(back2, kk.bk(st))) == True{} : Bool},
  +ou: {kk.c1(cc, kk.cls(T.esc.uni.lex(back2), kk.bk(st))) == True{} : Bool},
  +of: {kk.fok(cc, back2) == True{} : Bool}
) -> {kk.K(gg, T.esc.use(ee, st, back2)) == True{} : Bool}:
  match ee:
    case T.EChar{+c0}:
      kg.push(gg, st, c0, back2, eg, cc, ecl, op)
    case T.EUni{+n0}:
      match st:
        case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
          +lead}:
          kk.l1(gg, T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead},
            T.esc.uni(T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab,
              lead}, back2, n0), cc, ecl, ou, {==}, eg)
    case T.EFold{+saw}:
      kg.fold(gg, back2, st, saw, eg, cc, ecl, of)
    case T.EBad{}:
      kg.err(gg, st, "invalid escape", {==}, eg)

# a state's class, from its lex state
def kk.cllx(+st: T.St, +ll: T.Lex, +el: {kk.lx(st) == ll : T.Lex}) -> {kk.cl(st) == kk.cls(ll, kk.bk(st)) : KC}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      Equal.cong(T.Lex, KC, zz => kk.cls(zz, back), lex, ll, el)

# a newline that ended a root value moves the line on; any other state stays
def kg.blex(
  +gg: K3G,
  lex: T.Lex,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +el: {kk.lx(st) == lex : T.Lex}
) -> {kk.K(gg, T.bare.line.lex(lex, st)) == True{} : Bool}:
  match lex:
    case T.LTop{}:
      eg
    case T.LLine{}:
      kg.lex(gg, st, T.LTop{}, eg, kk.cls(T.LLine{}, kk.bk(st)), kk.cllx(st, T.LLine{}, el), {==})
    case T.LKey{}:
      eg
    case T.LKeyDot{}:
      eg
    case T.LAfter{}:
      eg
    case T.LKeyQ{}:
      eg
    case T.LKeyE{}:
      eg
    case T.LKeyU{}:
      eg
    case T.LVal{}:
      eg
    case T.LQ{}:
      eg
    case T.LQ2{}:
      eg
    case T.LStr{}:
      eg
    case T.LEsc{}:
      eg
    case T.LUni{}:
      eg
    case T.LFold{}:
      eg
    case T.LMq{}:
      eg
    case T.LMqEnd{}:
      eg
    case T.LTrim{}:
      eg
    case T.LTrim2{}:
      eg
    case T.LBare{}:
      eg
    case T.LDate{}:
      eg
    case T.LCom{}:
      eg
    case T.LHead{}:
      eg
    case T.LHeadGap{}:
      eg
    case T.LHeadDot{}:
      eg
    case T.LHeadQ{}:
      eg
    case T.LHeadE{}:
      eg
    case T.LHeadU{}:
      eg
    case T.LHeadR{}:
      eg
    case T.LArr{}:
      eg
    case T.LArrC{}:
      eg
    case T.LInl{}:
      eg
    case T.LInlK{}:
      eg
    case T.LInlC{}:
      eg
    case T.LSink{}:
      eg

# the newline, read off the state
def kg.blgo(
  +gg: K3G,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool}
) -> {kk.K(gg, T.bare.line.go(st)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      kg.blex(gg, lex, T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab,
        lead}, eg, {==})

# a newline, or another delimiter
def kg.bline(
  +gg: K3G,
  nl: Bool,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool}
) -> {kk.K(gg, T.bare.line(st, nl)) == True{} : Bool}:
  match nl:
    case True{}:
      kg.blgo(gg, st, eg)
    case False{}:
      eg

# the delimiter held, or not
def kg.bhold(
  +gg: K3G,
  +st: T.St,
  +ch: Char,
  hold: Bool,
  +eg: {kk.K(gg, st) == True{} : Bool}
) -> {kk.K(gg, T.bare.hold(st, ch, hold)) == True{} : Bool}:
  match hold:
    case False{}:
      kg.bline(gg, T.ch.nl(ch), st, eg)
    case True{}:
      kg.holdon(gg, st, ch, eg)

# a bare word classified: refused with a reason, or taken
def kg.bgot(
  +gg: K3G,
  g0: T.Got,
  +st: T.St,
  +ch: Char,
  +hold: Bool,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ew: {Laws.k3.why(g0) == True{} : Bool}
) -> {kk.K(gg, T.bare.got(g0, st, ch, hold)) == True{} : Bool}:
  match g0:
    case T.GotBad{+why}:
      kg.err(gg, st, why, Eq.not.true(String.is_empty(why), ew), eg)
    case T.GotVal{+val}:
      kg.bhold(gg, T.val.take(st, val), ch, hold, kg.take(gg, st, val, eg))

# a bare word finished
def kg.bfin(
  +gg: K3G,
  +st: T.St,
  +ch: Char,
  +hd: Bool,
  +eg: {kk.K(gg, st) == True{} : Bool}
) -> {kk.K(gg, T.bare.finish(st, ch, hd)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      kg.bgot(gg, T.word.val(List.reverse(&2, Char, buf)), T.St{bad, rows, heads, here, parts, [], lex, back, qkind,
        stack, hold, uni, left, arrtab, lead}, ch, hd, eg,
        Laws.bare_word_refusal_says_why(List.reverse(&2, Char, buf)))

# a string finished
def kg.strfin(
  +gg: K3G,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool}
) -> {kk.K(gg, T.str.fin(st)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      kg.take(gg, T.St{bad, rows, heads, here, parts, [], lex, back, qkind, stack, hold, uni, left, arrtab, lead},
        T.VStr{T.buf.str(buf)}, eg)

# a third quote starts a multiline string; two quotes are an empty string
def kg.q2go(
  +gg: K3G,
  same: Bool,
  +st: T.St,
  +ch: Char,
  +kind: T.QKind,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.q2.go(same, st, ch, kind)) == True{} : Bool}:
  match same:
    case True{}:
      kg.multi(gg, st, kind, eg, ecl)
    case False{}:
      kg.bhold(gg, T.val.take(st, T.VStr{""}), ch, True{}, kg.take(gg, st, T.VStr{""}, eg))

# two quotes have been seen
def kg.q2(
  +gg: K3G,
  +st: T.St,
  +ch: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.q2(st, ch)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      kg.q2go(gg, Char.is_eq(ch, T.q.char(qkind)), T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack,
        hold, uni, left, arrtab, lead}, ch, qkind, eg, ecl)

# the second quote waits; the third is a closing delimiter
def kg.mqone(
  +gg: K3G,
  one: Bool,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.mq.one(one, st)) == True{} : Bool}:
  match one:
    case True{}:
      kg.mq(gg, st, 2, eg, ecl)
    case False{}:
      kg.mqshut(gg, st, eg, ecl)

# a quote continues the closer; anything else is content
def kg.mqgo(
  +gg: K3G,
  quote: Bool,
  +one: Bool,
  +st: T.St,
  +ch: Char,
  +b2: List<&2, Char>,
  +kind: T.QKind,
  +l2: U32,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.mq.go(quote, one, st, ch, b2, kind, l2)) == True{} : Bool}:
  match quote:
    case True{}:
      kg.mqone(gg, one, st, eg, ecl)
    case False{}:
      kg.mqback(gg, st, ch, T.mq.put(one, T.q.char(kind), b2), eg, ecl)

# one character while closing a multiline string
def kg.mqstep(
  +gg: K3G,
  +st: T.St,
  +ch: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.mq.step(st, ch)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      kg.mqgo(gg, Char.is_eq(ch, T.q.char(qkind)), U32.is_eq(left, 1), T.St{bad, rows, heads, here, parts, buf, lex,
        back, qkind, stack, hold, uni, left, arrtab, lead}, ch, buf, qkind, left, eg, ecl)

# a comment's control: a tab is kept, anything else refused
def kg.ctab(
  +gg: K3G,
  tab: Bool,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool}
) -> {kk.K(gg, T.lex.com.tab(tab, st)) == True{} : Bool}:
  match tab:
    case True{}:
      eg
    case False{}:
      kg.err(gg, st, "invalid control in comment", {==}, eg)

# a comment's character
def kg.cctl(
  +gg: K3G,
  ctl: Bool,
  +tab: Bool,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool}
) -> {kk.K(gg, T.lex.com.ctl(ctl, tab, st)) == True{} : Bool}:
  match ctl:
    case False{}:
      eg
    case True{}:
      kg.ctab(gg, tab, st, eg)

# a comment: a newline ends it, a control is refused
def kg.cgo(
  +gg: K3G,
  nl: Bool,
  +ctl: Bool,
  +tab: Bool,
  +st: T.St,
  +ch: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +el: {kk.lx(st) == T.LCom{} : T.Lex}
) -> {kk.K(gg, T.lex.com.go(nl, ctl, tab, st, ch)) == True{} : Bool}:
  match nl:
    case False{}:
      kg.cctl(gg, ctl, tab, st, eg)
    case True{}:
      kg.comnl(gg, st, ch, eg, el)

# a header's walk done: the root it returned, and the header's table current
def kk.happly(
  +gg: K3G,
  end: T.End,
  +segs: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +uni: U32,
  +left: U32,
  +lead: Bool,
  +ee: {kk.KE(gg, end) == True{} : Bool}
) -> {kk.K(gg, T.head.apply(end, segs, back, qkind, uni, left, lead)) == True{} : Bool}:
  match end:
    case T.End{+vs, +bad, +hs}:
      ee

# a header's walk from a root that holds the key holds it, or fails
def kk.hke(
  ok: Bool,
  +gg: K3G,
  +segs: List<&2, String>,
  +rows: List<&2, T.Val>,
  +job: T.Job,
  +bad: String,
  +heads: List<&2, String>,
  +eo: {String.is_empty(bad) == ok : Bool},
  +ee: {Bool.or(Bool.not(String.is_empty(bad)), Laws.k3.has(rows, kk.tp(gg), kk.key(gg))) == True{} : Bool}
) -> {kk.KE(gg, T.tree.walk(segs, T.Tw{rows, job, [], bad, "", heads, False{}}, 0)) == True{} : Bool}:
  match ok:
    case False{}:
      %Equal.sym(T.End, T.tree.walk(segs, T.Tw{rows, job, [], bad, "", heads, False{}}, 0), T.End{rows, bad, heads},
        L3.failed_walk_changes_nothing(segs, rows, job, bad, "", heads, False{}, 0, eo)) : {kk.KE(gg, _) == True{}
          : Bool}
      ee
    case True{}:
      kk.KE.mk(gg, T.tree.walk(segs, T.Tw{rows, job, [], bad, "", heads, False{}}, 0), eb => kw.mono(segs, rows, job,
        bad, "", heads, False{}, 0, kk.key(gg), eo, eb)(kk.tp(gg), kk.okor(bad, Laws.k3.has(rows, kk.tp(gg),
          kk.key(gg)), eo, ee)))

# an array-of-tables header, or a table header
def kk.hjob(
  +gg: K3G,
  arr: Bool,
  +bad: String,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +segs: List<&2, String>,
  +back: T.Lex,
  +qkind: T.QKind,
  +uni: U32,
  +left: U32,
  +lead: Bool,
  +ee: {Bool.or(Bool.not(String.is_empty(bad)), Laws.k3.has(rows, kk.tp(gg), kk.key(gg))) == True{} : Bool}
) -> {kk.K(gg, T.head.job(arr, bad, rows, heads, segs, back, qkind, uni, left, lead)) == True{} : Bool}:
  match arr:
    case True{}:
      kk.happly(gg, T.tree.walk(segs, T.Tw{rows, T.JAot{}, [], bad, "", heads, False{}}, 0), segs, back, qkind, uni,
        left, lead, kk.hke(String.is_empty(bad), gg, segs, rows, T.JAot{}, bad,
        heads, {==}, ee))
    case False{}:
      kk.happly(gg, T.tree.walk(segs, T.Tw{rows, T.JDef{}, [], bad, "", heads, False{}}, 0), segs, back, qkind, uni,
        left, lead, kk.hke(String.is_empty(bad), gg, segs, rows, T.JDef{}, bad,
        heads, {==}, ee))

# a header's state's invariant: failed, or no frame open and pending below
# or held
def kk.HR(+gg: K3G, +stack: List<&2, T.Ctx>, +rows: List<&2, T.Val>, aa: Bool) -> Bool:
  Bool.or(aa, Bool.and(List.is_empty(&2, T.Ctx, stack), Bool.or(kk.PF(gg, stack), kk.L(gg, stack, rows))))

# a header's state: no frame is open, so the root holds the key
def kk.hroot(
  +gg: K3G,
  stack: List<&2, T.Ctx>,
  +rows: List<&2, T.Val>,
  +aa: Bool,
  +ee: {kk.HR(gg, stack, rows, aa) == True{} : Bool}
) -> {Bool.or(aa, Laws.k3.has(rows, kk.tp(gg), kk.key(gg))) == True{} : Bool}:
  match stack:
    case []:
      ee
    case _f <> _t:
      kk.bimp(aa, False{}, Laws.k3.has(rows, kk.tp(gg), kk.key(gg)), e1 => Eq.bit.absurd(&2, {Laws.k3.has(rows,
        kk.tp(gg), kk.key(gg)) == True{} : Bool}, e1), ee)

# open the table or the array of tables the header names
def kg.on(
  +gg: K3G,
  +st: T.St,
  +segs: List<&2, String>,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.head.on(st, segs)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      kk.hjob(gg, arrtab, bad, rows, heads, segs, back, qkind, uni, left, lead, kk.hroot(gg, stack, rows,
        Bool.not(String.is_empty(bad)), Equal.trans(Bool, kk.Kc(gg, KcH{}, bad, rows, here, parts, stack), kk.Kc(gg,
          kk.cls(lex, back), bad, rows, here, parts, stack), True{}, Equal.cong(KC, Bool, zz => kk.Kc(gg, zz, bad, rows,
            here, parts, stack), KcH{}, kk.cls(lex, back), Equal.sym(KC, kk.cls(lex, back), KcH{}, ecl)), eg)))

# the header's key is ready, or empty
def kg.go(
  +gg: K3G,
  empty: Bool,
  +st: T.St,
  +segs: List<&2, String>,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.head.go(empty, st, segs)) == True{} : Bool}:
  match empty:
    case True{}:
      kg.err(gg, st, "empty key", {==}, eg)
    case False{}:
      kg.on(gg, st, segs, eg, ecl)

# the segments pushed: the header's key
def kg.use(
  +gg: K3G,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.head.use(st)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      kg.go(gg, List.is_empty(&2, String, parts), T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack,
        hold, uni, left, arrtab, lead}, List.reverse(&2, String, parts), eg, ecl)

# a segment pushed at a header's end leaves a header's state
def kk.clseg(+st: T.St) -> {kk.cl(T.seg.push(st, T.LTop{})) == KcH{} : KC}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      {==}

# the buffer is the last segment when it holds one
def kg.finbuf(
  +gg: K3G,
  empty: Bool,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.head.fin.buf(empty, st)) == True{} : Bool}:
  match empty:
    case True{}:
      kg.use(gg, st, eg, ecl)
    case False{}:
      kg.use(gg, T.seg.push(st, T.LTop{}), kg.seg(gg, st, T.LTop{}, eg, KcH{}, ecl, {==}), kk.clseg(st))

# a header closed
def kg.fin(
  +gg: K3G,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.head.fin(st)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      kg.finbuf(gg, List.is_empty(&2, Char, buf), T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack,
        hold, uni, left, arrtab, lead}, eg, ecl)

# a segment pushed leaves the state's class the new lex state's
def kk.clsx(+st: T.St, +ll: T.Lex) -> {kk.cl(T.seg.push(st, ll)) == kk.cls(ll, kk.bk(st)) : KC}:
  match st:
    case T.St{_b, _r, _h, _e, _p, _f, _x, _k, _q, _s, _o, _u, _l, _a, _d}:
      {==}

# and a step that moves the lex state
def kk.clst(+st: T.St, +ll: T.Lex) -> {kk.cl(T.st.lex(st, ll)) == kk.cls(ll, kk.bk(st)) : KC}:
  match st:
    case T.St{_b, _r, _h, _e, _p, _f, _x, _k, _q, _s, _o, _u, _l, _a, _d}:
      {==}

# a key's segment ended before a comment: a key's class, or failed
def kk.clke2(empty: Bool, +st: T.St) -> {kk.cl(T.lex.key.end.go(empty, st, T.LAfter{})) == KcO{} : KC}:
  match empty:
    case True{}:
      match st:
        case T.St{_b, _r, _h, _e, _p, _f, _x, _k, _q, _s, _o, _u, _l, _a, _d}:
          {==}
    case False{}:
      match st:
        case T.St{_b, _r, _h, _e, _p, _f, _x, _k, _q, _s, _o, _u, _l, _a, _d}:
          {==}

# and read off the state
def kk.clke(+st: T.St) -> {kk.cl(T.lex.key.end(st, T.LAfter{})) == KcO{} : KC}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      kk.clke2(List.is_empty(&2, Char, buf), T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold,
        uni,
        left, arrtab, lead})

# a key cleared leaves a key's class
def kk.clkc(+st: T.St) -> {kk.cl(T.lex.key.clear(st)) == KcO{} : KC}:
  match st:
    case T.St{_b, _r, _h, _e, _p, _f, _x, _k, _q, _s, _o, _u, _l, _a, _d}:
      {==}

# ] with an array of tables waits for the second
def kg.close2(
  +gg: K3G,
  arr: Bool,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.head.close2(arr, st)) == True{} : Bool}:
  match arr:
    case True{}:
      kg.lex(gg, st, T.LHeadR{}, eg, KcH{}, ecl, {==})
    case False{}:
      kg.fin(gg, st, eg, ecl)

# ] pushes the open segment first
def kg.closego(
  +gg: K3G,
  empty: Bool,
  arr: Bool,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.head.close.go(empty, arr, st)) == True{} : Bool}:
  match empty:
    case True{}:
      kg.close2(gg, arr, st, eg, ecl)
    case False{}:
      kg.close2(gg, arr, T.seg.push(st, T.LHead{}), kg.seg(gg, st, T.LHead{}, eg, KcH{}, ecl, {==}), kk.clsx(st,
        T.LHead{}))

# ]
def kg.close(
  +gg: K3G,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.head.close(st)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      kg.closego(gg, List.is_empty(&2, Char, buf), arrtab, T.St{bad, rows, heads, here, parts, buf, lex, back, qkind,
        stack, hold, uni, left, arrtab, lead}, eg, ecl)

# a quote opens a segment only at the start
def kg.quotego(
  +gg: K3G,
  fresh: Bool,
  +st: T.St,
  +kind: T.QKind,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.head.quote.go(fresh, st, kind)) == True{} : Bool}:
  match fresh:
    case True{}:
      kg.qkey(gg, st, kind, T.LHeadQ{}, eg, KcH{}, ecl, {==})
    case False{}:
      kg.err(gg, st, "invalid header", {==}, eg)

# the step quote
def kg.quote(
  +gg: K3G,
  +st: T.St,
  +kind: T.QKind,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.head.quote(st, kind)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      kg.quotego(gg, Bool.and(List.is_empty(&2, Char, buf), List.is_empty(&2, String, parts)), T.St{bad, rows, heads,
        here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead}, kind, eg, ecl)

# the step brgo
def kg.brgo(
  +gg: K3G,
  fresh: Bool,
  once: Bool,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.head.br.go(fresh, once, st)) == True{} : Bool}:
  match fresh:
    case False{}:
      kg.err(gg, st, "invalid header", {==}, eg)
    case True{}:
      kg.br2(gg, once, st, eg, ecl)

# the step br
def kg.br(
  +gg: K3G,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.head.br(st)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      kg.brgo(gg, Bool.and(List.is_empty(&2, String, parts), List.is_empty(&2, Char, buf)), Bool.not(arrtab),
        T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead}, eg, ecl)

# a bare character: a segment goes on, or starts
def kg.chgo(
  +gg: K3G,
  gap: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.head.ch.go(gap, st, cc)) == True{} : Bool}:
  match gap:
    case True{}:
      kg.err(gg, st, "invalid header", {==}, eg)
    case False{}:
      kg.push(gg, st, cc, T.LHead{}, eg, KcH{}, ecl, {==})

# the step ch
def kg.ch(
  +gg: K3G,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.head.ch(st, cc)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      kg.chgo(gg, Bool.and(Bool.not(List.is_empty(&2, String, parts)), List.is_empty(&2, Char, buf)), T.St{bad, rows,
        heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead}, cc, eg, ecl)

# blank space ends an open segment
def kg.gapgo(
  +gg: K3G,
  empty: Bool,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.head.gap.go(empty, st)) == True{} : Bool}:
  match empty:
    case True{}:
      kg.lex(gg, st, T.LHeadDot{}, eg, KcH{}, ecl, {==})
    case False{}:
      kg.seg(gg, st, T.LHeadGap{}, eg, KcH{}, ecl, {==})

# the step gap
def kg.gap(
  +gg: K3G,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.head.gap(st)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      kg.gapgo(gg, List.is_empty(&2, Char, buf), T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack,
        hold, uni, left, arrtab, lead}, eg, ecl)

# a dot ends the open segment
def kg.dot3(
  +gg: K3G,
  empty: Bool,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.head.dot3(empty, st)) == True{} : Bool}:
  match empty:
    case True{}:
      kg.err(gg, st, "empty key", {==}, eg)
    case False{}:
      kg.seg(gg, st, T.LHeadDot{}, eg, KcH{}, ecl, {==})

# the step dot2
def kg.dot2(
  +gg: K3G,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.head.dot2(st)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      kg.dot3(gg, List.is_empty(&2, Char, buf), T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack,
        hold, uni, left, arrtab, lead}, eg, ecl)

# LHead's dispatch, one test at a time
def kg.hlit(
  +gg: K3G,
  lit: Bool,
  hash: Bool,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.head.lit(lit, hash, st)) == True{} : Bool}:
  match lit:
    case True{}:
      kg.quote(gg, st, T.QLit{}, eg, ecl)
    case False{}:
      kg.hash(gg, hash, st, eg, ecl)

# the step hq
def kg.hq(
  +gg: K3G,
  qq: Bool,
  lit: Bool,
  hash: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.head.q(qq, lit, hash, st, cc)) == True{} : Bool}:
  match qq:
    case True{}:
      kg.quote(gg, st, T.QBasic{}, eg, ecl)
    case False{}:
      kg.hlit(gg, lit, hash, st, eg, ecl)

# the step hend
def kg.hend(
  +gg: K3G,
  end: Bool,
  qq: Bool,
  lit: Bool,
  hash: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.head.end(end, qq, lit, hash, st, cc)) == True{} : Bool}:
  match end:
    case True{}:
      kg.close(gg, st, eg, ecl)
    case False{}:
      kg.hq(gg, qq, lit, hash, st, cc, eg, ecl)

# the step hdot
def kg.hdot(
  +gg: K3G,
  dot: Bool,
  end: Bool,
  qq: Bool,
  lit: Bool,
  hash: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.head.dot(dot, end, qq, lit, hash, st, cc)) == True{} : Bool}:
  match dot:
    case True{}:
      kg.dot2(gg, st, eg, ecl)
    case False{}:
      kg.hend(gg, end, qq, lit, hash, st, cc, eg, ecl)

# the step hsp
def kg.hsp(
  +gg: K3G,
  sp: Bool,
  dot: Bool,
  end: Bool,
  qq: Bool,
  lit: Bool,
  hash: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.head.sp(sp, dot, end, qq, lit, hash, st, cc)) == True{} : Bool}:
  match sp:
    case True{}:
      kg.gap(gg, st, eg, ecl)
    case False{}:
      kg.hdot(gg, dot, end, qq, lit, hash, st, cc, eg, ecl)

# the step hbare
def kg.hbare(
  +gg: K3G,
  bare: Bool,
  sp: Bool,
  dot: Bool,
  end: Bool,
  qq: Bool,
  lit: Bool,
  hash: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.head.bare(bare, sp, dot, end, qq, lit, hash, st, cc)) == True{} : Bool}:
  match bare:
    case True{}:
      kg.ch(gg, st, cc, eg, ecl)
    case False{}:
      kg.hsp(gg, sp, dot, end, qq, lit, hash, st, cc, eg, ecl)

# the step hgo
def kg.hgo(
  +gg: K3G,
  br: Bool,
  bare: Bool,
  sp: Bool,
  dot: Bool,
  end: Bool,
  qq: Bool,
  lit: Bool,
  hash: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.head.go(br, bare, sp, dot, end, qq, lit, hash, st, cc)) == True{} : Bool}:
  match br:
    case True{}:
      kg.br(gg, st, eg, ecl)
    case False{}:
      kg.hbare(gg, bare, sp, dot, end, qq, lit, hash, st, cc, eg, ecl)

# LHead
def kg.head(
  +gg: K3G,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.head(st, cc)) == True{} : Bool}:
  kg.hgo(gg, Char.is_eq(cc, '['), T.bare.at(cc), T.ch.sp(cc), Char.is_eq(cc, '.'), Char.is_eq(cc, ']'), Char.is_eq(cc,
    '"'), Char.is_eq(cc, '\''), Char.is_eq(cc, '#'), st, cc, eg, ecl)

# LHeadGap
def kg.hgend(
  +gg: K3G,
  end: Bool,
  hash: Bool,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.hgap.end(end, hash, st)) == True{} : Bool}:
  match end:
    case True{}:
      kg.close(gg, st, eg, ecl)
    case False{}:
      kg.hash(gg, hash, st, eg, ecl)

# the step hgdot
def kg.hgdot(
  +gg: K3G,
  dot: Bool,
  end: Bool,
  hash: Bool,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.hgap.dot(dot, end, hash, st)) == True{} : Bool}:
  match dot:
    case True{}:
      kg.lex(gg, st, T.LHeadDot{}, eg, KcH{}, ecl, {==})
    case False{}:
      kg.hgend(gg, end, hash, st, eg, ecl)

# the step hgap
def kg.hgap(
  +gg: K3G,
  sp: Bool,
  dot: Bool,
  end: Bool,
  hash: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.hgap(sp, dot, end, hash, st, cc)) == True{} : Bool}:
  match sp:
    case True{}:
      eg
    case False{}:
      kg.hgdot(gg, dot, end, hash, st, eg, ecl)

# LHeadDot
def kg.hdlit(
  +gg: K3G,
  lit: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.hdot.lit(lit, st, cc)) == True{} : Bool}:
  match lit:
    case True{}:
      kg.qkey(gg, st, T.QLit{}, T.LHeadQ{}, eg, KcH{}, ecl, {==})
    case False{}:
      kg.err(gg, st, "invalid header", {==}, eg)

# the step hdq
def kg.hdq(
  +gg: K3G,
  qq: Bool,
  lit: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.hdot.q(qq, lit, st, cc)) == True{} : Bool}:
  match qq:
    case True{}:
      kg.qkey(gg, st, T.QBasic{}, T.LHeadQ{}, eg, KcH{}, ecl, {==})
    case False{}:
      kg.hdlit(gg, lit, st, cc, eg, ecl)

# the step hdbare
def kg.hdbare(
  +gg: K3G,
  bare: Bool,
  qq: Bool,
  lit: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.hdot.bare(bare, qq, lit, st, cc)) == True{} : Bool}:
  match bare:
    case True{}:
      kg.push(gg, st, cc, T.LHead{}, eg, KcH{}, ecl, {==})
    case False{}:
      kg.hdq(gg, qq, lit, st, cc, eg, ecl)

# the step hdot2
def kg.hdot2(
  +gg: K3G,
  sp: Bool,
  bare: Bool,
  qq: Bool,
  lit: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.hdot(sp, bare, qq, lit, st, cc)) == True{} : Bool}:
  match sp:
    case True{}:
      eg
    case False{}:
      kg.hdbare(gg, bare, qq, lit, st, cc, eg, ecl)

# LHeadR
def kg.hr(
  +gg: K3G,
  end: Bool,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.head.r.go(end, st)) == True{} : Bool}:
  match end:
    case True{}:
      kg.fin(gg, st, eg, ecl)
    case False{}:
      kg.err(gg, st, "invalid header", {==}, eg)

# the step tbare
def kg.tbare(
  +gg: K3G,
  bare: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.top.bare(bare, st, cc)) == True{} : Bool}:
  match bare:
    case True{}:
      kg.push(gg, st, cc, T.LKey{}, eg, KcH{}, ecl, {==})
    case False{}:
      kg.err(gg, st, "invalid key", {==}, eg)

# the step tlit
def kg.tlit(
  +gg: K3G,
  lit: Bool,
  bare: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.top.lit(lit, bare, st, cc)) == True{} : Bool}:
  match lit:
    case True{}:
      kg.qkey(gg, st, T.QLit{}, T.LKeyQ{}, eg, KcH{}, ecl, {==})
    case False{}:
      kg.tbare(gg, bare, st, cc, eg, ecl)

# the step tq
def kg.tq(
  +gg: K3G,
  qq: Bool,
  lit: Bool,
  bare: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.top.q(qq, lit, bare, st, cc)) == True{} : Bool}:
  match qq:
    case True{}:
      kg.qkey(gg, st, T.QBasic{}, T.LKeyQ{}, eg, KcH{}, ecl, {==})
    case False{}:
      kg.tlit(gg, lit, bare, st, cc, eg, ecl)

# the step tbr
def kg.tbr(
  +gg: K3G,
  br: Bool,
  qq: Bool,
  lit: Bool,
  bare: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.top.br(br, qq, lit, bare, st, cc)) == True{} : Bool}:
  match br:
    case True{}:
      kg.bracket(gg, st, eg, KcH{}, ecl, {==})
    case False{}:
      kg.tq(gg, qq, lit, bare, st, cc, eg, ecl)

# the step thash
def kg.thash(
  +gg: K3G,
  hash: Bool,
  br: Bool,
  qq: Bool,
  lit: Bool,
  bare: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.top.hash(hash, br, qq, lit, bare, st, cc)) == True{} : Bool}:
  match hash:
    case True{}:
      kg.com(gg, st, T.LTop{}, eg, KcH{}, ecl, {==})
    case False{}:
      kg.tbr(gg, br, qq, lit, bare, st, cc, eg, ecl)

# the step tnl
def kg.tnl(
  +gg: K3G,
  nl: Bool,
  hash: Bool,
  br: Bool,
  qq: Bool,
  lit: Bool,
  bare: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.top.nl(nl, hash, br, qq, lit, bare, st, cc)) == True{} : Bool}:
  match nl:
    case True{}:
      eg
    case False{}:
      kg.thash(gg, hash, br, qq, lit, bare, st, cc, eg, ecl)

# the step tgo
def kg.tgo(
  +gg: K3G,
  sp: Bool,
  nl: Bool,
  hash: Bool,
  br: Bool,
  qq: Bool,
  lit: Bool,
  bare: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.top.go(sp, nl, hash, br, qq, lit, bare, st, cc)) == True{} : Bool}:
  match sp:
    case True{}:
      eg
    case False{}:
      kg.tnl(gg, nl, hash, br, qq, lit, bare, st, cc, eg, ecl)

# the step lnl
def kg.lnl(
  +gg: K3G,
  nl: Bool,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.line.nl(nl, st)) == True{} : Bool}:
  match nl:
    case True{}:
      kg.lex(gg, st, T.LTop{}, eg, KcH{}, ecl, {==})
    case False{}:
      kg.err(gg, st, "newline required", {==}, eg)

# the step lhash
def kg.lhash(
  +gg: K3G,
  hash: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.line.hash(hash, nl, st, cc)) == True{} : Bool}:
  match hash:
    case True{}:
      kg.com(gg, st, T.LLine{}, eg, KcH{}, ecl, {==})
    case False{}:
      kg.lnl(gg, nl, st, eg, ecl)

# the step lgo
def kg.lgo(
  +gg: K3G,
  sp: Bool,
  hash: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcH{} : KC}
) -> {kk.K(gg, T.lex.line.go(sp, hash, nl, st, cc)) == True{} : Bool}:
  match sp:
    case True{}:
      eg
    case False{}:
      kg.lhash(gg, hash, nl, st, cc, eg, ecl)

# the step kendgo
def kg.kendgo(
  +gg: K3G,
  empty: Bool,
  +st: T.St,
  +next: T.Lex,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC},
  +on: {kk.c2(KcO{}, kk.cls(next, kk.bk(st))) == True{} : Bool}
) -> {kk.K(gg, T.lex.key.end.go(empty, st, next)) == True{} : Bool}:
  match empty:
    case True{}:
      kg.err(gg, st, "empty key", {==}, eg)
    case False{}:
      kg.seg(gg, st, next, eg, KcO{}, ecl, on)

# the step kend
def kg.kend(
  +gg: K3G,
  +st: T.St,
  +next: T.Lex,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC},
  +on: {kk.c2(KcO{}, kk.cls(next, kk.bk(st))) == True{} : Bool}
) -> {kk.K(gg, T.lex.key.end(st, next)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      kg.kendgo(gg, List.is_empty(&2, Char, buf), T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack,
        hold, uni, left, arrtab, lead}, next, eg, ecl, on)

# the step knl
def kg.knl(
  +gg: K3G,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +_ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.key.nl(nl, st, cc)) == True{} : Bool}:
  match nl:
    case True{}:
      kg.err(gg, st, "newline in key", {==}, eg)
    case False{}:
      kg.err(gg, st, "invalid key", {==}, eg)

# the step khash
def kg.khash(
  +gg: K3G,
  hash: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.key.hash(hash, nl, st, cc)) == True{} : Bool}:
  match hash:
    case True{}:
      kg.com(gg, T.lex.key.end(st, T.LAfter{}), T.LAfter{}, kg.kend(gg, st, T.LAfter{}, eg, ecl, {==}), KcO{},
        kk.clke(st), {==})
    case False{}:
      kg.knl(gg, nl, st, cc, eg, ecl)

# the step keq
def kg.keq(
  +gg: K3G,
  eq: Bool,
  hash: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.key.eq(eq, hash, nl, st, cc)) == True{} : Bool}:
  match eq:
    case True{}:
      kg.kend(gg, st, T.LVal{}, eg, ecl, {==})
    case False{}:
      kg.khash(gg, hash, nl, st, cc, eg, ecl)

# the step kdot
def kg.kdot(
  +gg: K3G,
  dot: Bool,
  eq: Bool,
  hash: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.key.dot(dot, eq, hash, nl, st, cc)) == True{} : Bool}:
  match dot:
    case True{}:
      kg.kend(gg, st, T.LKeyDot{}, eg, ecl, {==})
    case False{}:
      kg.keq(gg, eq, hash, nl, st, cc, eg, ecl)

# the step ksp
def kg.ksp(
  +gg: K3G,
  sp: Bool,
  dot: Bool,
  eq: Bool,
  hash: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.key.sp(sp, dot, eq, hash, nl, st, cc)) == True{} : Bool}:
  match sp:
    case True{}:
      kg.kend(gg, st, T.LAfter{}, eg, ecl, {==})
    case False{}:
      kg.kdot(gg, dot, eq, hash, nl, st, cc, eg, ecl)

# the step kgo
def kg.kgo(
  +gg: K3G,
  bare: Bool,
  sp: Bool,
  dot: Bool,
  eq: Bool,
  hash: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.key.go(bare, sp, dot, eq, hash, nl, st, cc)) == True{} : Bool}:
  match bare:
    case True{}:
      kg.push(gg, st, cc, T.LKey{}, eg, KcO{}, ecl, {==})
    case False{}:
      kg.ksp(gg, sp, dot, eq, hash, nl, st, cc, eg, ecl)

# the step anl
def kg.anl(
  +gg: K3G,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +_ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.after.nl(nl, st, cc)) == True{} : Bool}:
  match nl:
    case True{}:
      kg.err(gg, st, "newline in key", {==}, eg)
    case False{}:
      kg.err(gg, st, "invalid key", {==}, eg)

# the step ahash
def kg.ahash(
  +gg: K3G,
  hash: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.after.hash(hash, nl, st, cc)) == True{} : Bool}:
  match hash:
    case True{}:
      kg.com(gg, st, T.LAfter{}, eg, KcO{}, ecl, {==})
    case False{}:
      kg.anl(gg, nl, st, cc, eg, ecl)

# the step aeq
def kg.aeq(
  +gg: K3G,
  eq: Bool,
  hash: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.after.eq(eq, hash, nl, st, cc)) == True{} : Bool}:
  match eq:
    case True{}:
      kg.lex(gg, st, T.LVal{}, eg, KcO{}, ecl, {==})
    case False{}:
      kg.ahash(gg, hash, nl, st, cc, eg, ecl)

# the step adot
def kg.adot(
  +gg: K3G,
  dot: Bool,
  eq: Bool,
  hash: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.after.dot(dot, eq, hash, nl, st, cc)) == True{} : Bool}:
  match dot:
    case True{}:
      kg.lex(gg, st, T.LKeyDot{}, eg, KcO{}, ecl, {==})
    case False{}:
      kg.aeq(gg, eq, hash, nl, st, cc, eg, ecl)

# the step ago
def kg.ago(
  +gg: K3G,
  sp: Bool,
  dot: Bool,
  eq: Bool,
  hash: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.after.go(sp, dot, eq, hash, nl, st, cc)) == True{} : Bool}:
  match sp:
    case True{}:
      eg
    case False{}:
      kg.adot(gg, dot, eq, hash, nl, st, cc, eg, ecl)

# the step dnl
def kg.dnl(
  +gg: K3G,
  nl: Bool,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +_ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.kdot.nl(nl, st)) == True{} : Bool}:
  match nl:
    case True{}:
      kg.err(gg, st, "newline in key", {==}, eg)
    case False{}:
      kg.err(gg, st, "invalid key", {==}, eg)

# the step ddot
def kg.ddot(
  +gg: K3G,
  dot: Bool,
  nl: Bool,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.kdot.dot(dot, nl, st)) == True{} : Bool}:
  match dot:
    case True{}:
      kg.err(gg, st, "empty key", {==}, eg)
    case False{}:
      kg.dnl(gg, nl, st, eg, ecl)

# the step dbare
def kg.dbare(
  +gg: K3G,
  bare: Bool,
  dot: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.kdot.bare(bare, dot, nl, st, cc)) == True{} : Bool}:
  match bare:
    case True{}:
      kg.push(gg, st, cc, T.LKey{}, eg, KcO{}, ecl, {==})
    case False{}:
      kg.ddot(gg, dot, nl, st, eg, ecl)

# the step dlit
def kg.dlit(
  +gg: K3G,
  lit: Bool,
  dot: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.kdot.lit(lit, dot, nl, st, cc)) == True{} : Bool}:
  match lit:
    case True{}:
      kg.qkey(gg, st, T.QLit{}, T.LKeyQ{}, eg, KcO{}, ecl, {==})
    case False{}:
      kg.dbare(gg, T.bare.at(cc), dot, nl, st, cc, eg, ecl)

# the step dq
def kg.dq(
  +gg: K3G,
  qq: Bool,
  lit: Bool,
  dot: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.kdot.q(qq, lit, dot, nl, st, cc)) == True{} : Bool}:
  match qq:
    case True{}:
      kg.qkey(gg, st, T.QBasic{}, T.LKeyQ{}, eg, KcO{}, ecl, {==})
    case False{}:
      kg.dlit(gg, lit, dot, nl, st, cc, eg, ecl)

# the step dgo
def kg.dgo(
  +gg: K3G,
  sp: Bool,
  qq: Bool,
  lit: Bool,
  dot: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.kdot.go(sp, qq, lit, dot, nl, st, cc)) == True{} : Bool}:
  match sp:
    case True{}:
      eg
    case False{}:
      kg.dq(gg, qq, lit, dot, nl, st, cc, eg, ecl)

# the step vnl3
def kg.vnl3(
  +gg: K3G,
  inside: Bool,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +_ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.val.nl3(inside, st)) == True{} : Bool}:
  match inside:
    case True{}:
      kg.err(gg, st, "newline in inline table", {==}, eg)
    case False{}:
      kg.err(gg, st, "newline before value", {==}, eg)

# the step vnl2
def kg.vnl2(
  +gg: K3G,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.val.nl2(st, cc)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      kg.vnl3(gg, T.inl.open(stack), T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left,
        arrtab, lead}, eg, ecl)

# the step vinl
def kg.vinl(
  +gg: K3G,
  inl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.val.inl(inl, st, cc)) == True{} : Bool}:
  match inl:
    case True{}:
      kg.inline(gg, st, eg)
    case False{}:
      kg.push(gg, st, cc, T.LBare{}, eg, KcV{}, ecl, {==})

# the step vbr
def kg.vbr(
  +gg: K3G,
  br: Bool,
  inl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.val.br(br, inl, st, cc)) == True{} : Bool}:
  match br:
    case True{}:
      kg.array(gg, st, eg)
    case False{}:
      kg.vinl(gg, inl, st, cc, eg, ecl)

# the step vlit
def kg.vlit(
  +gg: K3G,
  lit: Bool,
  br: Bool,
  inl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.val.lit(lit, br, inl, st, cc)) == True{} : Bool}:
  match lit:
    case True{}:
      kg.qkey(gg, st, T.QLit{}, T.LQ{}, eg, KcV{}, ecl, {==})
    case False{}:
      kg.vbr(gg, br, inl, st, cc, eg, ecl)

# the step vq
def kg.vq(
  +gg: K3G,
  qq: Bool,
  lit: Bool,
  br: Bool,
  inl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.val.q(qq, lit, br, inl, st, cc)) == True{} : Bool}:
  match qq:
    case True{}:
      kg.qkey(gg, st, T.QBasic{}, T.LQ{}, eg, KcV{}, ecl, {==})
    case False{}:
      kg.vlit(gg, lit, br, inl, st, cc, eg, ecl)

# the step vhash
def kg.vhash(
  +gg: K3G,
  hash: Bool,
  qq: Bool,
  lit: Bool,
  br: Bool,
  inl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.val.hash(hash, qq, lit, br, inl, st, cc)) == True{} : Bool}:
  match hash:
    case True{}:
      kg.com(gg, st, T.LVal{}, eg, KcV{}, ecl, {==})
    case False{}:
      kg.vq(gg, qq, lit, br, inl, st, cc, eg, ecl)

# the step vnl
def kg.vnl(
  +gg: K3G,
  nl: Bool,
  hash: Bool,
  qq: Bool,
  lit: Bool,
  br: Bool,
  inl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.val.nl(nl, hash, qq, lit, br, inl, st, cc)) == True{} : Bool}:
  match nl:
    case True{}:
      kg.vnl2(gg, st, cc, eg, ecl)
    case False{}:
      kg.vhash(gg, hash, qq, lit, br, inl, st, cc, eg, ecl)

# the step vgo
def kg.vgo(
  +gg: K3G,
  sp: Bool,
  nl: Bool,
  hash: Bool,
  qq: Bool,
  lit: Bool,
  br: Bool,
  inl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.val.go(sp, nl, hash, qq, lit, br, inl, st, cc)) == True{} : Bool}:
  match sp:
    case True{}:
      eg
    case False{}:
      kg.vnl(gg, nl, hash, qq, lit, br, inl, st, cc, eg, ecl)

# the step qgo
def kg.qgo(
  +gg: K3G,
  same: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.q.go(same, st, cc)) == True{} : Bool}:
  match same:
    case True{}:
      kg.lex(gg, st, T.LQ2{}, eg, KcV{}, ecl, {==})
    case False{}:
      kg.hold(gg, T.st.lex(st, T.LStr{}), T.LStr{}, cc, kg.lex(gg, st, T.LStr{}, eg, KcV{}, ecl, {==}), KcV{},
        kk.clst(st, T.LStr{}), {==})

# the step q
def kg.q(
  +gg: K3G,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.q(st, cc)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      kg.qgo(gg, Char.is_eq(cc, T.q.char(qkind)), T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack,
        hold,
        uni, left, arrtab, lead}, cc, eg, ecl)

# the step schgo
def kg.schgo(
  +gg: K3G,
  bad: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.str.char.go(bad, st, cc)) == True{} : Bool}:
  match bad:
    case True{}:
      kg.err(gg, st, "invalid control", {==}, eg)
    case False{}:
      kg.push(gg, st, cc, T.LStr{}, eg, KcV{}, ecl, {==})

# the step sch
def kg.sch(
  +gg: K3G,
  +multi: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.str.char(multi, st, cc)) == True{} : Bool}:
  kg.schgo(gg, T.str.bad(Char.to_u32(cc), multi), st, cc, eg, ecl)

# the step sbs
def kg.sbs(
  +gg: K3G,
  bs: Bool,
  +multi: Bool,
  +st: T.St,
  +cc: Char,
  +kind: T.QKind,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.str.bs(bs, multi, st, cc, kind)) == True{} : Bool}:
  match bs:
    case True{}:
      kg.lex(gg, st, T.LEsc{}, eg, KcV{}, ecl, {==})
    case False{}:
      kg.sch(gg, multi, st, cc, eg, ecl)

# the step sesc
def kg.sesc(
  +gg: K3G,
  basic: Bool,
  +multi: Bool,
  +st: T.St,
  +cc: Char,
  +kind: T.QKind,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.str.esc(basic, multi, st, cc, kind)) == True{} : Bool}:
  match basic:
    case True{}:
      kg.sbs(gg, Char.is_eq(cc, '\\'), multi, st, cc, kind, eg, ecl)
    case False{}:
      kg.sch(gg, multi, st, cc, eg, ecl)

# the step squote
def kg.squote(
  +gg: K3G,
  multi: Bool,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.str.quote(multi, st)) == True{} : Bool}:
  match multi:
    case False{}:
      kg.strfin(gg, st, eg)
    case True{}:
      kg.mq(gg, st, 1, eg, ecl)

# the step sgo
def kg.sgo(
  +gg: K3G,
  quote: Bool,
  +multi: Bool,
  +basic: Bool,
  +st: T.St,
  +cc: Char,
  +kind: T.QKind,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.str.go(quote, multi, basic, st, cc, kind)) == True{} : Bool}:
  match quote:
    case True{}:
      kg.squote(gg, multi, st, eg, ecl)
    case False{}:
      kg.sesc(gg, basic, multi, st, cc, kind, eg, ecl)

# the step str
def kg.str(
  +gg: K3G,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.str(st, cc)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      kg.sgo(gg, Char.is_eq(cc, T.q.char(qkind)), T.q.multi(qkind), T.q.basic(qkind), T.St{bad, rows, heads, here,
        parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead}, cc, qkind, eg, ecl)

# the step fendgo
def kg.fendgo(
  +gg: K3G,
  saw: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.fold.end.go(saw, st, cc)) == True{} : Bool}:
  match saw:
    case True{}:
      kg.hold(gg, T.st.lex(st, T.LStr{}), T.LStr{}, cc, kg.lex(gg, st, T.LStr{}, eg, KcV{}, ecl, {==}), KcV{},
        kk.clst(st, T.LStr{}), {==})
    case False{}:
      kg.err(gg, st, "invalid escape", {==}, eg)

# the step fend
def kg.fend(
  +gg: K3G,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.fold.end(st, cc)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      kg.fendgo(gg, U32.is_eq(left, 1), T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni,
        left, arrtab, lead}, cc, eg, ecl)

# the step fnl
def kg.fnl(
  +gg: K3G,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.fold.nl(nl, st, cc)) == True{} : Bool}:
  match nl:
    case True{}:
      kg.foldsaw(gg, st, eg)
    case False{}:
      kg.fend(gg, st, cc, eg, ecl)

# the step fgo
def kg.fgo(
  +gg: K3G,
  sp: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.fold.go(sp, nl, st, cc)) == True{} : Bool}:
  match sp:
    case True{}:
      eg
    case False{}:
      kg.fnl(gg, nl, st, cc, eg, ecl)

# the step mqfin
def kg.mqfin(
  +gg: K3G,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +_ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.mq.fin(st, cc)) == True{} : Bool}:
  kg.holdon(gg, T.str.fin(st), cc, kg.strfin(gg, st, eg))

# the step mqroom
def kg.mqroom(
  +gg: K3G,
  room: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.mq.room(room, st, cc)) == True{} : Bool}:
  match room:
    case True{}:
      kg.mqmore(gg, st, cc, eg)
    case False{}:
      kg.mqfin(gg, st, cc, eg, ecl)

# the step mqendgo
def kg.mqendgo(
  +gg: K3G,
  quote: Bool,
  +room: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.mq.end.go(quote, room, st, cc)) == True{} : Bool}:
  match quote:
    case True{}:
      kg.mqroom(gg, room, st, cc, eg, ecl)
    case False{}:
      kg.mqfin(gg, st, cc, eg, ecl)

# the step mqend
def kg.mqend(
  +gg: K3G,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.mq.end(st, cc)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      kg.mqendgo(gg, Char.is_eq(cc, T.q.char(qkind)), U32.is_lt(left, 2), T.St{bad, rows, heads, here, parts, buf, lex,
        back, qkind, stack, hold, uni, left, arrtab, lead}, cc, eg, ecl)

# the step tnl2
def kg.tnl2(
  +gg: K3G,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.trim.nl(nl, st, cc)) == True{} : Bool}:
  match nl:
    case True{}:
      kg.lex(gg, st, T.LStr{}, eg, KcV{}, ecl, {==})
    case False{}:
      kg.hold(gg, T.st.lex(st, T.LStr{}), T.LStr{}, cc, kg.lex(gg, st, T.LStr{}, eg, KcV{}, ecl, {==}), KcV{},
        kk.clst(st, T.LStr{}), {==})

# the step trimgo
def kg.trimgo(
  +gg: K3G,
  cr: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.trim.go(cr, nl, st, cc)) == True{} : Bool}:
  match cr:
    case True{}:
      kg.lex(gg, st, T.LTrim2{}, eg, KcV{}, ecl, {==})
    case False{}:
      kg.tnl2(gg, nl, st, cc, eg, ecl)

# the step trim2go
def kg.trim2go(
  +gg: K3G,
  lf: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.trim2.go(lf, st, cc)) == True{} : Bool}:
  match lf:
    case True{}:
      kg.lex(gg, st, T.LStr{}, eg, KcV{}, ecl, {==})
    case False{}:
      kg.hold(gg, T.st.lex(st, T.LStr{}), T.LStr{}, cc, kg.lex(gg, st, T.LStr{}, eg, KcV{}, ecl, {==}), KcV{},
        kk.clst(st, T.LStr{}), {==})

# the step aend
def kg.aend(
  +gg: K3G,
  end: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.arr.end(end, st, cc)) == True{} : Bool}:
  match end:
    case True{}:
      kg.arrclose(gg, st, eg)
    case False{}:
      kg.hold(gg, T.st.lex(st, T.LVal{}), T.LVal{}, cc, kg.lex(gg, st, T.LVal{}, eg, KcO{}, ecl, {==}), KcV{},
        kk.clst(st, T.LVal{}), {==})

# the step aahash
def kg.aahash(
  +gg: K3G,
  hash: Bool,
  end: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.arr.hash(hash, end, st, cc)) == True{} : Bool}:
  match hash:
    case True{}:
      kg.com(gg, st, T.LArr{}, eg, KcO{}, ecl, {==})
    case False{}:
      kg.aend(gg, end, st, cc, eg, ecl)

# the step aanl
def kg.aanl(
  +gg: K3G,
  nl: Bool,
  hash: Bool,
  end: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.arr.nl(nl, hash, end, st, cc)) == True{} : Bool}:
  match nl:
    case True{}:
      eg
    case False{}:
      kg.aahash(gg, hash, end, st, cc, eg, ecl)

# the step aago
def kg.aago(
  +gg: K3G,
  sp: Bool,
  nl: Bool,
  hash: Bool,
  end: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.arr.go(sp, nl, hash, end, st, cc)) == True{} : Bool}:
  match sp:
    case True{}:
      eg
    case False{}:
      kg.aanl(gg, nl, hash, end, st, cc, eg, ecl)

# the step acend
def kg.acend(
  +gg: K3G,
  end: Bool,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +_ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.arrc.end(end, st)) == True{} : Bool}:
  match end:
    case True{}:
      kg.arrclose(gg, st, eg)
    case False{}:
      kg.err(gg, st, "invalid array", {==}, eg)

# the step accomma
def kg.accomma(
  +gg: K3G,
  comma: Bool,
  end: Bool,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.arrc.comma(comma, end, st)) == True{} : Bool}:
  match comma:
    case True{}:
      kg.lex(gg, st, T.LArr{}, eg, KcO{}, ecl, {==})
    case False{}:
      kg.acend(gg, end, st, eg, ecl)

# the step achash
def kg.achash(
  +gg: K3G,
  hash: Bool,
  comma: Bool,
  end: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.arrc.hash(hash, comma, end, st, cc)) == True{} : Bool}:
  match hash:
    case True{}:
      kg.com(gg, st, T.LArrC{}, eg, KcO{}, ecl, {==})
    case False{}:
      kg.accomma(gg, comma, end, st, eg, ecl)

# the step acnl
def kg.acnl(
  +gg: K3G,
  nl: Bool,
  hash: Bool,
  comma: Bool,
  end: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.arrc.nl(nl, hash, comma, end, st, cc)) == True{} : Bool}:
  match nl:
    case True{}:
      eg
    case False{}:
      kg.achash(gg, hash, comma, end, st, cc, eg, ecl)

# the step acgo
def kg.acgo(
  +gg: K3G,
  sp: Bool,
  nl: Bool,
  hash: Bool,
  comma: Bool,
  end: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.arrc.go(sp, nl, hash, comma, end, st, cc)) == True{} : Bool}:
  match sp:
    case True{}:
      eg
    case False{}:
      kg.acnl(gg, nl, hash, comma, end, st, cc, eg, ecl)

# the step kbare
def kg.kbare(
  +gg: K3G,
  ok: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.key.bare(ok, st, cc)) == True{} : Bool}:
  match ok:
    case True{}:
      kg.push(gg, st, cc, T.LKey{}, eg, KcO{}, ecl, {==})
    case False{}:
      kg.err(gg, st, "invalid key", {==}, eg)

# the step klit
def kg.klit(
  +gg: K3G,
  lit: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.key.lit(lit, st, cc)) == True{} : Bool}:
  match lit:
    case True{}:
      kg.qkey(gg, st, T.QLit{}, T.LKeyQ{}, eg, KcO{}, ecl, {==})
    case False{}:
      kg.kbare(gg, T.bare.at(cc), st, cc, eg, ecl)

# the step kq0
def kg.kq0(
  +gg: K3G,
  qq: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.key.q(qq, st, cc)) == True{} : Bool}:
  match qq:
    case True{}:
      kg.qkey(gg, st, T.QBasic{}, T.LKeyQ{}, eg, KcO{}, ecl, {==})
    case False{}:
      kg.klit(gg, Char.is_eq(cc, '\''), st, cc, eg, ecl)

# the step kstart
def kg.kstart(
  +gg: K3G,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.key.start(st, cc)) == True{} : Bool}:
  kg.kq0(gg, Char.is_eq(cc, '"'), T.lex.key.clear(st), cc, kg.kclear(gg, st, eg, KcO{}, ecl, {==}), kk.clkc(st))

# the step inlnl
def kg.inlnl(
  +gg: K3G,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.inl.nl(nl, st, cc)) == True{} : Bool}:
  match nl:
    case True{}:
      kg.err(gg, st, "newline in inline table", {==}, eg)
    case False{}:
      kg.kstart(gg, st, cc, eg, ecl)

# the step inlend
def kg.inlend(
  +gg: K3G,
  end: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.inl.end(end, nl, st, cc)) == True{} : Bool}:
  match end:
    case True{}:
      kg.inlclose(gg, st, eg, KcO{}, ecl, {==})
    case False{}:
      kg.inlnl(gg, nl, st, cc, eg, ecl)

# the step inlhash
def kg.inlhash(
  +gg: K3G,
  hash: Bool,
  end: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.inl.hash(hash, end, nl, st, cc)) == True{} : Bool}:
  match hash:
    case True{}:
      kg.com(gg, st, T.LInl{}, eg, KcO{}, ecl, {==})
    case False{}:
      kg.inlend(gg, end, nl, st, cc, eg, ecl)

# the step inlgo
def kg.inlgo(
  +gg: K3G,
  sp: Bool,
  hash: Bool,
  end: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.inl.go(sp, hash, end, nl, st, cc)) == True{} : Bool}:
  match sp:
    case True{}:
      eg
    case False{}:
      kg.inlhash(gg, hash, end, nl, st, cc, eg, ecl)

# the step ikhash
def kg.ikhash(
  +gg: K3G,
  hash: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.inlk.hash(hash, nl, st, cc)) == True{} : Bool}:
  match hash:
    case True{}:
      kg.com(gg, st, T.LInlK{}, eg, KcO{}, ecl, {==})
    case False{}:
      kg.inlnl(gg, nl, st, cc, eg, ecl)

# the step ikgo
def kg.ikgo(
  +gg: K3G,
  sp: Bool,
  hash: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.inlk.go(sp, hash, nl, st, cc)) == True{} : Bool}:
  match sp:
    case True{}:
      eg
    case False{}:
      kg.ikhash(gg, hash, nl, st, cc, eg, ecl)

# the step icnl
def kg.icnl(
  +gg: K3G,
  nl: Bool,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +_ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.inlc.nl(nl, st)) == True{} : Bool}:
  match nl:
    case True{}:
      kg.err(gg, st, "newline in inline table", {==}, eg)
    case False{}:
      kg.err(gg, st, "invalid inline table", {==}, eg)

# the step icend
def kg.icend(
  +gg: K3G,
  end: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.inlc.end(end, nl, st, cc)) == True{} : Bool}:
  match end:
    case True{}:
      kg.inlclose(gg, st, eg, KcO{}, ecl, {==})
    case False{}:
      kg.icnl(gg, nl, st, eg, ecl)

# the step iccomma
def kg.iccomma(
  +gg: K3G,
  comma: Bool,
  end: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.inlc.comma(comma, end, nl, st, cc)) == True{} : Bool}:
  match comma:
    case True{}:
      kg.lex(gg, st, T.LInlK{}, eg, KcO{}, ecl, {==})
    case False{}:
      kg.icend(gg, end, nl, st, cc, eg, ecl)

# the step ichash
def kg.ichash(
  +gg: K3G,
  hash: Bool,
  comma: Bool,
  end: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.inlc.hash(hash, comma, end, nl, st, cc)) == True{} : Bool}:
  match hash:
    case True{}:
      kg.com(gg, st, T.LInlC{}, eg, KcO{}, ecl, {==})
    case False{}:
      kg.iccomma(gg, comma, end, nl, st, cc, eg, ecl)

# the step icgo
def kg.icgo(
  +gg: K3G,
  sp: Bool,
  hash: Bool,
  comma: Bool,
  end: Bool,
  nl: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcO{} : KC}
) -> {kk.K(gg, T.lex.inlc.go(sp, hash, comma, end, nl, st, cc)) == True{} : Bool}:
  match sp:
    case True{}:
      eg
    case False{}:
      kg.ichash(gg, hash, comma, end, nl, st, cc, eg, ecl)

# a step of a bare word: bdgo
def kg.bdgo(
  +gg: K3G,
  date: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.bare.date.go(date, st, cc)) == True{} : Bool}:
  match date:
    case True{}:
      kg.lex(gg, st, T.LDate{}, eg, KcV{}, ecl, {==})
    case False{}:
      kg.bfin(gg, st, cc, False{}, eg)

# a step of a bare word: bdate
def kg.bdate(
  +gg: K3G,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.bare.date(st, cc)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      kg.bdgo(gg, T.date.shaped(buf), T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left,
        arrtab, lead}, cc, eg, ecl)

# a step of a bare word: bend
def kg.bend(
  +gg: K3G,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +_ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.bare.end(st, cc)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left,
      +arrtab, +lead}:
      kg.bfin(gg, T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead},
        cc, T.lex.bare.hold(T.ch.skip(cc), T.ch.nl(cc), T.inl.open(stack)), eg)

# a step of a bare word: bsp
def kg.bsp(
  +gg: K3G,
  sp: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.bare.sp(sp, st, cc)) == True{} : Bool}:
  match sp:
    case True{}:
      kg.bdate(gg, st, cc, eg, ecl)
    case False{}:
      kg.bend(gg, st, cc, eg, ecl)

# a step of a bare word: bgo
def kg.bgo(
  +gg: K3G,
  delim: Bool,
  +sp: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.bare.go(delim, sp, st, cc)) == True{} : Bool}:
  match delim:
    case False{}:
      kg.push(gg, st, cc, T.LBare{}, eg, KcV{}, ecl, {==})
    case True{}:
      kg.bsp(gg, sp, st, cc, eg, ecl)

# a step of a bare word: datego
def kg.datego(
  +gg: K3G,
  digit: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ecl: {kk.cl(st) == KcV{} : KC}
) -> {kk.K(gg, T.lex.date.go(digit, st, cc)) == True{} : Bool}:
  match digit:
    case True{}:
      kg.datedig(gg, st, cc, eg, ecl)
    case False{}:
      kg.bfin(gg, st, cc, True{}, eg)

# one character in any state keeps KEY-3's invariant
def kk.on(
  +gg: K3G,
  lex: T.Lex,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +el: {kk.lx(st) == lex : T.Lex}
) -> {kk.K(gg, T.read.on(lex, st, cc)) == True{} : Bool}:
  match lex:
    case T.LTop{}:
      kg.tgo(gg, T.ch.sp(cc), T.ch.nl(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, '['), Char.is_eq(cc, '"'),
        Char.is_eq(cc, '\''), T.bare.at(cc), st, cc, eg, kk.cllx(st, T.LTop{}, el))
    case T.LLine{}:
      kg.lgo(gg, T.ch.sp(cc), Char.is_eq(cc, '#'), T.ch.nl(cc), st, cc, eg, kk.cllx(st, T.LLine{}, el))
    case T.LKey{}:
      kg.kgo(gg, T.bare.at(cc), T.ch.sp(cc), Char.is_eq(cc, '.'), Char.is_eq(cc, '='), Char.is_eq(cc, '#'),
        T.ch.nl(cc), st, cc, eg, kk.cllx(st, T.LKey{}, el))
    case T.LKeyDot{}:
      kg.dgo(gg, T.ch.sp(cc), Char.is_eq(cc, '"'), Char.is_eq(cc, '\''), Char.is_eq(cc, '.'), T.ch.nl(cc), st, cc, eg,
        kk.cllx(st, T.LKeyDot{}, el))
    case T.LAfter{}:
      kg.ago(gg, T.ch.sp(cc), Char.is_eq(cc, '.'), Char.is_eq(cc, '='), Char.is_eq(cc, '#'), T.ch.nl(cc), st, cc, eg,
        kk.cllx(st, T.LAfter{}, el))
    case T.LKeyQ{}:
      kg.kq(gg, st, cc, T.LAfter{}, T.LKeyQ{}, eg, KcO{}, kk.cllx(st, T.LKeyQ{}, el), {==}, {==}, {==})
    case T.LKeyE{}:
      kg.esc(gg, T.esc.of(cc), st, T.LKeyQ{}, eg, KcO{}, kk.cllx(st, T.LKeyE{}, el), {==}, {==}, {==})
    case T.LKeyU{}:
      kg.uni(gg, st, cc, T.LKeyQ{}, eg, KcO{}, kk.cllx(st, T.LKeyU{}, el), {==})
    case T.LVal{}:
      kg.vgo(gg, T.ch.sp(cc), T.ch.nl(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, '"'), Char.is_eq(cc, '\''),
        Char.is_eq(cc, '['), Char.is_eq(cc, '{'), st, cc, eg, kk.cllx(st, T.LVal{}, el))
    case T.LQ{}:
      kg.q(gg, st, cc, eg, kk.cllx(st, T.LQ{}, el))
    case T.LQ2{}:
      kg.q2(gg, st, cc, eg, kk.cllx(st, T.LQ2{}, el))
    case T.LStr{}:
      kg.str(gg, st, cc, eg, kk.cllx(st, T.LStr{}, el))
    case T.LEsc{}:
      kg.esc(gg, T.esc.of(cc), st, T.LStr{}, eg, KcV{}, kk.cllx(st, T.LEsc{}, el), {==}, {==}, {==})
    case T.LUni{}:
      kg.uni(gg, st, cc, T.LStr{}, eg, KcV{}, kk.cllx(st, T.LUni{}, el), {==})
    case T.LFold{}:
      kg.fgo(gg, T.ch.sp(cc), T.ch.nl(cc), st, cc, eg, kk.cllx(st, T.LFold{}, el))
    case T.LMq{}:
      kg.mqstep(gg, st, cc, eg, kk.cllx(st, T.LMq{}, el))
    case T.LMqEnd{}:
      kg.mqend(gg, st, cc, eg, kk.cllx(st, T.LMqEnd{}, el))
    case T.LTrim{}:
      kg.trimgo(gg, U32.is_eq(Char.to_u32(cc), 13), T.ch.nl(cc), st, cc, eg, kk.cllx(st, T.LTrim{}, el))
    case T.LTrim2{}:
      kg.trim2go(gg, U32.is_eq(Char.to_u32(cc), 10), st, cc, eg, kk.cllx(st, T.LTrim2{}, el))
    case T.LBare{}:
      kg.bgo(gg, T.ch.delim(cc), T.ch.space(cc), st, cc, eg, kk.cllx(st, T.LBare{}, el))
    case T.LDate{}:
      kg.datego(gg, Char.is_digit(cc), st, cc, eg, kk.cllx(st, T.LDate{}, el))
    case T.LCom{}:
      kg.cgo(gg, T.ch.nl(cc), T.ch.ctl(cc), U32.is_eq(Char.to_u32(cc), 9), st, cc, eg, el)
    case T.LHead{}:
      kg.head(gg, st, cc, eg, kk.cllx(st, T.LHead{}, el))
    case T.LHeadGap{}:
      kg.hgap(gg, T.ch.sp(cc), Char.is_eq(cc, '.'), Char.is_eq(cc, ']'), Char.is_eq(cc, '#'), st, cc, eg, kk.cllx(st,
        T.LHeadGap{}, el))
    case T.LHeadDot{}:
      kg.hdot2(gg, T.ch.sp(cc), T.bare.at(cc), Char.is_eq(cc, '"'), Char.is_eq(cc, '\''), st, cc, eg, kk.cllx(st,
        T.LHeadDot{}, el))
    case T.LHeadQ{}:
      kg.kq(gg, st, cc, T.LHeadGap{}, T.LHeadQ{}, eg, KcH{}, kk.cllx(st, T.LHeadQ{}, el), {==}, {==}, {==})
    case T.LHeadE{}:
      kg.esc(gg, T.esc.of(cc), st, T.LHeadQ{}, eg, KcH{}, kk.cllx(st, T.LHeadE{}, el), {==}, {==}, {==})
    case T.LHeadU{}:
      kg.uni(gg, st, cc, T.LHeadQ{}, eg, KcH{}, kk.cllx(st, T.LHeadU{}, el), {==})
    case T.LHeadR{}:
      kg.hr(gg, Char.is_eq(cc, ']'), st, eg, kk.cllx(st, T.LHeadR{}, el))
    case T.LArr{}:
      kg.aago(gg, T.ch.sp(cc), T.ch.nl(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, ']'), st, cc, eg, kk.cllx(st,
        T.LArr{}, el))
    case T.LArrC{}:
      kg.acgo(gg, T.ch.sp(cc), T.ch.nl(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, ','), Char.is_eq(cc, ']'), st, cc, eg,
        kk.cllx(st, T.LArrC{}, el))
    case T.LInl{}:
      kg.inlgo(gg, T.ch.sp(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, '}'), T.ch.nl(cc), st, cc, eg, kk.cllx(st,
        T.LInl{}, el))
    case T.LInlK{}:
      kg.ikgo(gg, T.ch.sp(cc), Char.is_eq(cc, '#'), T.ch.nl(cc), st, cc, eg, kk.cllx(st, T.LInlK{}, el))
    case T.LInlC{}:
      kg.icgo(gg, T.ch.sp(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, ','), Char.is_eq(cc, '}'), T.ch.nl(cc), st, cc, eg,
        kk.cllx(st, T.LInlC{}, el))
    case T.LSink{}:
      eg

# one character, the state read off
def kk.onst(
  +gg: K3G,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool}
) -> {kk.K(gg, T.read.on.st(st, cc)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      kk.on(gg, lex, T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab, lead},
        cc, eg, {==})

# a byte-order mark is dropped
def kk.sbom(
  +gg: K3G,
  bom: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool}
) -> {kk.K(gg, T.read.step.bom(bom, st, cc)) == True{} : Bool}:
  match bom:
    case True{}:
      eg
    case False{}:
      kk.onst(gg, st, cc, eg)

# the first character may be a byte-order mark
def kk.slead(
  +gg: K3G,
  lead: Bool,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool}
) -> {kk.K(gg, T.read.step.lead(lead, st, cc)) == True{} : Bool}:
  match lead:
    case False{}:
      kk.onst(gg, st, cc, eg)
    case True{}:
      kk.sbom(gg, U32.is_eq(Char.to_u32(cc), 65279), st, cc, eg)

# LEMMA: one character of the document by the full step keeps KEY-3's
# invariant
def kk.step(
  +gg: K3G,
  +st: T.St,
  +cc: Char,
  +eg: {kk.K(gg, st) == True{} : Bool}
) -> {kk.K(gg, T.read.step(st, cc)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      kk.slead(gg, lead, T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab,
        False{}}, cc, eg)

# a held character is read once
def kk.ohold(
  +gg: K3G,
  hold: T.Hold,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool}
) -> {kk.K(gg, T.read.once.hold(hold, st)) == True{} : Bool}:
  match hold:
    case T.HNone{}:
      eg
    case T.HChar{+c0}:
      kk.step(gg, st, c0, eg)

# and so does reading a held character
def kk.once2(
  +gg: K3G,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool}
) -> {kk.K(gg, T.read.once2(st)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      kk.ohold(gg, hold, T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, T.HNone{}, uni, left,
        arrtab, lead}, eg)

# what a parsed document says of the key: when it has no error, its root
# holds the key in its table
def kk.pd(+gg: K3G, +dd: T.Doc) -> Type:
  {String.is_empty(T.bad(dd)) == True{} : Bool} -> {Laws.k3.has(T.root(dd), kk.tp(gg), kk.key(gg)) == True{} : Bool}

# not a value's class, the root holds the key or failed
def kk.fdb(
  cc: KC,
  +aa: Bool,
  +pp: Bool,
  +xx: Bool,
  +ev: {kk.isv(cc) == False{} : Bool},
  +ee: {kk.Kb(cc, aa, True{}, pp, xx) == True{} : Bool}
) -> {Bool.or(aa, xx) == True{} : Bool}:
  match cc:
    case KcV{}:
      Eq.bit.absurd2(&2, {Bool.or(aa, xx) == True{} : Bool}, ev)
    case KcH{}:
      ee
    case KcO{}:
      ee

# a document of a state with no frame open holds the key, or has an error
def kk.fdoc(
  +gg: K3G,
  +cc: KC,
  +bad: String,
  +rows: List<&2, T.Val>,
  +here: List<&2, String>,
  +parts: List<&2, String>,
  stack: List<&2, T.Ctx>,
  +ev: {kk.isv(cc) == False{} : Bool},
  +ek: {kk.Kc(gg, cc, bad, rows, here, parts, stack) == True{} : Bool}
) -> kk.pd(gg, T.read.fin.stack(stack, bad, rows)):
  match stack:
    case []:
      eo => bo.t(Laws.k3.has(T.rows.seal(rows), kk.tp(gg), kk.key(gg)), Laws.k3.has(rows, kk.tp(gg), kk.key(gg)),
        kh.hs(kk.tp(gg), rows, kk.key(gg), nm => kh.smapeq(rows, SlF{nm}, kk.key(gg)), nm => qq => kh.smapeq(rows,
          SlA{nm, qq}, kk.key(gg))), kk.okor(bad, Laws.k3.has(rows, kk.tp(gg), kk.key(gg)), eo, kk.fdb(cc,
            Bool.not(String.is_empty(bad)), kk.pend(gg, [], here, parts), Laws.k3.has(rows, kk.tp(gg), kk.key(gg)), ev,
              ek)))
    case _f <> _t:
      eo => Eq.bit.absurd(&2, {Laws.k3.has(T.rows.seal(rows), kk.tp(gg), kk.key(gg)) == True{} : Bool},
        Equal.trans(Bool, False{}, String.is_empty(T.err.first(bad, "unclosed")), True{}, Equal.sym(Bool,
          String.is_empty(T.err.first(bad, "unclosed")), False{}, kw.efne(bad, "unclosed", {==})), eo))

# an unfinished document has an error
def kk.func(
  +gg: K3G,
  +st: T.St
) -> kk.pd(gg, T.read.fin.unclosed(st)):
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      eo => Eq.bit.absurd(&2, {Laws.k3.has(T.rows.seal(rows), kk.tp(gg), kk.key(gg)) == True{} : Bool},
        Equal.trans(Bool, False{}, String.is_empty(T.err.first(bad, "unclosed")), True{}, Equal.sym(Bool,
          String.is_empty(T.err.first(bad, "unclosed")), False{}, kw.efne(bad, "unclosed", {==})), eo))

# a finished document from a state
def kk.fdocst(
  +gg: K3G,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +ev: {kk.isv(kk.cl(st)) == False{} : Bool}
) -> kk.pd(gg, T.read.fin.doc(st)):
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      kk.fdoc(gg, kk.cls(lex, back), bad, rows, here, parts, stack, ev, eg)

# a comment's return state that may end a document is no value's
def kk.fendv(
  back: T.Lex,
  +ee: {T.read.fin.end(back) == True{} : Bool}
) -> {kk.isv(kk.cls0(back)) == False{} : Bool}:
  match back:
    case T.LTop{}:
      {==}
    case T.LLine{}:
      {==}
    case T.LKey{}:
      Eq.bit.absurd(&2, {kk.isv(kk.cls0(T.LKey{})) == False{} : Bool}, ee)
    case T.LKeyDot{}:
      Eq.bit.absurd(&2, {kk.isv(kk.cls0(T.LKeyDot{})) == False{} : Bool}, ee)
    case T.LAfter{}:
      Eq.bit.absurd(&2, {kk.isv(kk.cls0(T.LAfter{})) == False{} : Bool}, ee)
    case T.LKeyQ{}:
      Eq.bit.absurd(&2, {kk.isv(kk.cls0(T.LKeyQ{})) == False{} : Bool}, ee)
    case T.LKeyE{}:
      Eq.bit.absurd(&2, {kk.isv(kk.cls0(T.LKeyE{})) == False{} : Bool}, ee)
    case T.LKeyU{}:
      Eq.bit.absurd(&2, {kk.isv(kk.cls0(T.LKeyU{})) == False{} : Bool}, ee)
    case T.LVal{}:
      Eq.bit.absurd(&2, {kk.isv(kk.cls0(T.LVal{})) == False{} : Bool}, ee)
    case T.LQ{}:
      Eq.bit.absurd(&2, {kk.isv(kk.cls0(T.LQ{})) == False{} : Bool}, ee)
    case T.LQ2{}:
      Eq.bit.absurd(&2, {kk.isv(kk.cls0(T.LQ2{})) == False{} : Bool}, ee)
    case T.LStr{}:
      Eq.bit.absurd(&2, {kk.isv(kk.cls0(T.LStr{})) == False{} : Bool}, ee)
    case T.LEsc{}:
      Eq.bit.absurd(&2, {kk.isv(kk.cls0(T.LEsc{})) == False{} : Bool}, ee)
    case T.LUni{}:
      Eq.bit.absurd(&2, {kk.isv(kk.cls0(T.LUni{})) == False{} : Bool}, ee)
    case T.LFold{}:
      Eq.bit.absurd(&2, {kk.isv(kk.cls0(T.LFold{})) == False{} : Bool}, ee)
    case T.LMq{}:
      Eq.bit.absurd(&2, {kk.isv(kk.cls0(T.LMq{})) == False{} : Bool}, ee)
    case T.LMqEnd{}:
      Eq.bit.absurd(&2, {kk.isv(kk.cls0(T.LMqEnd{})) == False{} : Bool}, ee)
    case T.LTrim{}:
      Eq.bit.absurd(&2, {kk.isv(kk.cls0(T.LTrim{})) == False{} : Bool}, ee)
    case T.LTrim2{}:
      Eq.bit.absurd(&2, {kk.isv(kk.cls0(T.LTrim2{})) == False{} : Bool}, ee)
    case T.LBare{}:
      Eq.bit.absurd(&2, {kk.isv(kk.cls0(T.LBare{})) == False{} : Bool}, ee)
    case T.LDate{}:
      Eq.bit.absurd(&2, {kk.isv(kk.cls0(T.LDate{})) == False{} : Bool}, ee)
    case T.LCom{}:
      Eq.bit.absurd(&2, {kk.isv(kk.cls0(T.LCom{})) == False{} : Bool}, ee)
    case T.LHead{}:
      Eq.bit.absurd(&2, {kk.isv(kk.cls0(T.LHead{})) == False{} : Bool}, ee)
    case T.LHeadGap{}:
      Eq.bit.absurd(&2, {kk.isv(kk.cls0(T.LHeadGap{})) == False{} : Bool}, ee)
    case T.LHeadDot{}:
      Eq.bit.absurd(&2, {kk.isv(kk.cls0(T.LHeadDot{})) == False{} : Bool}, ee)
    case T.LHeadQ{}:
      Eq.bit.absurd(&2, {kk.isv(kk.cls0(T.LHeadQ{})) == False{} : Bool}, ee)
    case T.LHeadE{}:
      Eq.bit.absurd(&2, {kk.isv(kk.cls0(T.LHeadE{})) == False{} : Bool}, ee)
    case T.LHeadU{}:
      Eq.bit.absurd(&2, {kk.isv(kk.cls0(T.LHeadU{})) == False{} : Bool}, ee)
    case T.LHeadR{}:
      Eq.bit.absurd(&2, {kk.isv(kk.cls0(T.LHeadR{})) == False{} : Bool}, ee)
    case T.LArr{}:
      Eq.bit.absurd(&2, {kk.isv(kk.cls0(T.LArr{})) == False{} : Bool}, ee)
    case T.LArrC{}:
      Eq.bit.absurd(&2, {kk.isv(kk.cls0(T.LArrC{})) == False{} : Bool}, ee)
    case T.LInl{}:
      Eq.bit.absurd(&2, {kk.isv(kk.cls0(T.LInl{})) == False{} : Bool}, ee)
    case T.LInlK{}:
      Eq.bit.absurd(&2, {kk.isv(kk.cls0(T.LInlK{})) == False{} : Bool}, ee)
    case T.LInlC{}:
      Eq.bit.absurd(&2, {kk.isv(kk.cls0(T.LInlC{})) == False{} : Bool}, ee)
    case T.LSink{}:
      {==}

# a comment at the end, by whether it may end the document
def kk.fcom(
  +gg: K3G,
  ok: Bool,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool},
  ev: @e1: {ok == True{} : Bool} -> {kk.isv(kk.cl(st)) == False{} : Bool}
) -> kk.pd(gg, T.read.fin.com(ok, st)):
  match ok:
    case True{}:
      kk.fdocst(gg, st, eg, ev({==}))
    case False{}:
      kk.func(gg, st)

# a state's class not a value's, from its lex state
def kk.nv(
  +st: T.St,
  ll: T.Lex,
  +el: {kk.lx(st) == ll : T.Lex},
  +ev: {kk.isv(kk.cls(ll, kk.bk(st))) == False{} : Bool}
) -> {kk.isv(kk.cl(st)) == False{} : Bool}:
  Equal.trans(Bool, kk.isv(kk.cl(st)), kk.isv(kk.cls(ll, kk.bk(st))), False{}, Equal.cong(KC, Bool, zz => kk.isv(zz),
    kk.cl(st), kk.cls(ll, kk.bk(st)), kk.cllx(st, ll, el)), ev)

# the states that may end a document
def kk.fdone(
  +gg: K3G,
  lex: T.Lex,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool},
  +el: {kk.lx(st) == lex : T.Lex}
) -> kk.pd(gg, T.read.fin.ok(lex, st)):
  match lex:
    case T.LTop{}:
      kk.fdocst(gg, st, eg, kk.nv(st, T.LTop{}, el, {==}))
    case T.LLine{}:
      kk.fdocst(gg, st, eg, kk.nv(st, T.LLine{}, el, {==}))
    case T.LKey{}:
      kk.func(gg, st)
    case T.LKeyDot{}:
      kk.func(gg, st)
    case T.LAfter{}:
      kk.func(gg, st)
    case T.LKeyQ{}:
      kk.func(gg, st)
    case T.LKeyE{}:
      kk.func(gg, st)
    case T.LKeyU{}:
      kk.func(gg, st)
    case T.LVal{}:
      kk.func(gg, st)
    case T.LQ{}:
      kk.func(gg, st)
    case T.LQ2{}:
      kk.func(gg, st)
    case T.LStr{}:
      kk.func(gg, st)
    case T.LEsc{}:
      kk.func(gg, st)
    case T.LUni{}:
      kk.func(gg, st)
    case T.LFold{}:
      kk.func(gg, st)
    case T.LMq{}:
      kk.func(gg, st)
    case T.LMqEnd{}:
      kk.func(gg, st)
    case T.LTrim{}:
      kk.func(gg, st)
    case T.LTrim2{}:
      kk.func(gg, st)
    case T.LBare{}:
      kk.func(gg, st)
    case T.LDate{}:
      kk.func(gg, st)
    case T.LCom{}:
      match st:
        case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
          +lead}:
          kk.fcom(gg, T.read.fin.end(back), T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold,
            uni, left, arrtab, lead}, eg, e1 => kk.nv(T.St{bad, rows, heads, here, parts, buf, lex, back, qkind,
              stack, hold, uni, left, arrtab, lead}, T.LCom{}, el, kk.fendv(back, e1)))
    case T.LHead{}:
      kk.func(gg, st)
    case T.LHeadGap{}:
      kk.func(gg, st)
    case T.LHeadDot{}:
      kk.func(gg, st)
    case T.LHeadQ{}:
      kk.func(gg, st)
    case T.LHeadE{}:
      kk.func(gg, st)
    case T.LHeadU{}:
      kk.func(gg, st)
    case T.LHeadR{}:
      kk.func(gg, st)
    case T.LArr{}:
      kk.func(gg, st)
    case T.LArrC{}:
      kk.func(gg, st)
    case T.LInl{}:
      kk.func(gg, st)
    case T.LInlK{}:
      kk.func(gg, st)
    case T.LInlC{}:
      kk.func(gg, st)
    case T.LSink{}:
      kk.fdocst(gg, st, eg, kk.nv(st, T.LSink{}, el, {==}))

# the document once the last token has been closed
def kk.fin2(
  +gg: K3G,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool}
) -> kk.pd(gg, T.read.fin2(st)):
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      kk.fdone(gg, lex, T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab,
        lead}, eg, {==})

# a bare token, an empty string or a closed multiline string still open at
# the end is closed
def kk.flex(
  +gg: K3G,
  lex: T.Lex,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool}
) -> {kk.K(gg, T.read.fin.lex(lex, st)) == True{} : Bool}:
  match lex:
    case T.LTop{}:
      eg
    case T.LLine{}:
      eg
    case T.LKey{}:
      eg
    case T.LKeyDot{}:
      eg
    case T.LAfter{}:
      eg
    case T.LKeyQ{}:
      eg
    case T.LKeyE{}:
      eg
    case T.LKeyU{}:
      eg
    case T.LVal{}:
      eg
    case T.LQ{}:
      eg
    case T.LQ2{}:
      kg.take(gg, st, T.VStr{""}, eg)
    case T.LStr{}:
      eg
    case T.LEsc{}:
      eg
    case T.LUni{}:
      eg
    case T.LFold{}:
      eg
    case T.LMq{}:
      eg
    case T.LMqEnd{}:
      kg.strfin(gg, st, eg)
    case T.LTrim{}:
      eg
    case T.LTrim2{}:
      eg
    case T.LBare{}:
      kg.bfin(gg, st, ' ', False{}, eg)
    case T.LDate{}:
      kg.bfin(gg, st, ' ', False{}, eg)
    case T.LCom{}:
      eg
    case T.LHead{}:
      eg
    case T.LHeadGap{}:
      eg
    case T.LHeadDot{}:
      eg
    case T.LHeadQ{}:
      eg
    case T.LHeadE{}:
      eg
    case T.LHeadU{}:
      eg
    case T.LHeadR{}:
      eg
    case T.LArr{}:
      eg
    case T.LArrC{}:
      eg
    case T.LInl{}:
      eg
    case T.LInlK{}:
      eg
    case T.LInlC{}:
      eg
    case T.LSink{}:
      eg

# and read off the state
def kk.fclose(
  +gg: K3G,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool}
) -> {kk.K(gg, T.read.fin.close(st)) == True{} : Bool}:
  match st:
    case T.St{+bad, +rows, +heads, +here, +parts, +buf, +lex, +back, +qkind, +stack, +hold, +uni, +left, +arrtab,
      +lead}:
      kk.flex(gg, lex, T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, hold, uni, left, arrtab,
        lead}, eg)

# LEMMA: a state that keeps KEY-3's invariant at the end of the text gives
# a document that holds the key, or has an error
def kk.fin(
  +gg: K3G,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool}
) -> kk.pd(gg, T.read.fin(st)):
  kk.fin2(gg, T.read.fin.close(st), kk.fclose(gg, st, eg))

# KEY-3 as an instance of the scan induction: the invariant kk.K with the
# key as the context, no span check, any character and any text; each
# obligation is one of the lemmas above.

# LEMMA: from a state that keeps KEY-3's invariant, reading any text gives
# a document that holds the key, or has an error
def kk.read(
  +gg: K3G,
  +text: String,
  +st: T.St,
  +eg: {kk.K(gg, st) == True{} : Bool}
) -> kk.pd(gg, T.doc.read(text, T.MScan{st})):
  M14.sip.read(~K3G, ~(g => st0 => kk.K(g, st0)), ~(_g => _c => _n => _t => True{}), ~(_c => True{}), ~(_t => True{}),
    ~(g => dd => kk.pd(g, dd)), ~(g => st0 => e0 => cc => _e => kk.step(g, st0, cc, e0)), ~(g => st0 => e0 =>
      kk.once2(g, st0, e0)),
        ~(_g => _a => _b => _c => _d => _e => _f => _h => _i => _j => _k => _l => _m => _n => _c0 =>
        e0 => _e1 => e0), ~(g => st0 => why => ew => e0 => kg.err(g, st0, why, ew, e0)), ~(_g => _a => _b => _c => _d =>
          _e => _f => _h => _i => _j => _k => _l => e0 => e0), ~(_g => _h => _t => _e => _x => {==}), ~(_g => _c => _n
            => _h => _t => _e => _x => _y => {==}),
              ~(g => a => b => c => d => e => f => h => i => j => k => cut => nn =>
              _t => e0 => _e => kg.take(g, T.St{a, b, c, d, e, [], T.LStr{}, T.LStr{}, f, h, T.HNone{}, i, j, k,
                False{}}, T.VSpan{cut, nn}, e0)), ~(_g => _a => _b => _c => _d => _e => _f => _h => _i => _j => _k =>
                  _cut => _n => _t => e0 => _e => e0), ~(g => st0 => e0 => kk.fin(g, st0, e0)), ~(g => a => b => c =>
                    d => e => f => h => i => j => k => _e => kk.func(g, T.St{a, b, c, d, e, [], T.LStr{}, T.LStr{}, f,
                      h, T.HNone{}, i, j, k, False{}})), ~(_h => _t => _e => {==}), ~(_h => _t => _e => {==}), gg, text,
    T.MScan{st}, eg, {==})

# KEY-3: the keys and headers read with every spelling, as above (k3.keys,
# k3.hkeys), for what a document says of a key rather than for one document:
# the same steps, each rewriting the text read into the rest.

# a document said of from a contradiction
def kk.pdx(+gg: K3G, +dd: T.Doc, +ee: {False{} == True{} : Bool}) -> kk.pd(gg, dd):
  _e => Eq.bit.absurd(&2, {Laws.k3.has(T.root(dd), kk.tp(gg), kk.key(gg)) == True{} : Bool}, ee)

# the rest of the text read from the segment with buf in its buffer, whatever
# back, uni and left are
def k3p.Then(
  +hd: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +buf: List<&2, Char>,
  +rest: String,
  +gk: K3G
) -> Type:
  @b2: T.Lex -> @u2: U32 -> @l2: U32 ->
    kk.pd(gk, T.doc.read(rest, T.MScan{M5.k3.q(hd, rw, hs, he, ps, sk, ab, b2, u2, l2, buf)}))

# a two-character escape pushes the character it stands for and leaves back
# at the segment's state
def k3p.esc(
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
  +gk: K3G,
  ih: k3p.Then(hd, rw, hs, he, ps, sk, ab, D3.k3.mark.dec(mm) <> buf, rest, gk)
) -> kk.pd(gk, T.doc.read(SCon{'\\', SCon{D3.k3.mark.char(mm), rest}}, T.MScan{M5.k3.q(hd, rw, hs, he, ps, sk, ab, bk,
  un,
  lf, buf)})):
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
def k3p.tab(
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
  +gk: K3G,
  ih: k3p.Then(hd, rw, hs, he, ps, sk, ab, Chr{9} <> buf, rest, gk)
) -> kk.pd(gk, T.doc.read(SCon{Chr{9}, rest}, T.MScan{M5.k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)})):
  match hd:
    case False{}:
      ih(bk, un, lf)
    case True{}:
      ih(bk, un, lf)

# a character written as itself that is no quote, no backslash and no
# control is pushed, and back, uni and left stay
def k3p.plain(
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
  +gk: K3G,
  +e34: {U32.is_eq(uu, 34) == False{} : Bool},
  +e92: {U32.is_eq(uu, 92) == False{} : Bool},
  +ec: {Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127)) == False{} : Bool},
  ih: k3p.Then(hd, rw, hs, he, ps, sk, ab, Chr{uu} <> buf, rest, gk)
) -> kk.pd(gk, T.doc.read(SCon{Chr{uu}, rest}, T.MScan{M5.k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)})):
  +e10 = {M1.ctl.off(uu, 10, ec, {==}) : {U32.is_eq(uu, 10) == False{} : Bool}}
  +e13 = {M1.ctl.off(uu, 13, ec, {==}) : {U32.is_eq(uu, 13) == False{} : Bool}}
  fast = {Equal.sym(T.St, T.read.fast(M5.k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu}),
    M5.k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf),
    Equal.trans(T.St, T.read.fast(M5.k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu}),
    T.read.once2(T.lex.kq.go(U32.is_eq(uu, 34), U32.is_eq(uu, 92), True{}, Bool.or(U32.is_eq(uu, 10),
    U32.is_eq(uu, 13)), M5.k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf), Chr{uu}, M10.qs.close(hd),
        M9.qs.lex(hd))),
    M5.k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, Chr{uu} <> buf),
    M5.k3.fast(uu, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf),
    M5.k3.go(U32.is_eq(uu, 34), U32.is_eq(uu, 92), Bool.or(U32.is_eq(uu, 10), U32.is_eq(uu, 13)), uu, hd, rw, hs, he,
      ps, sk, ab, bk, un, lf, buf, e34, e92, M16.or.ff(U32.is_eq(uu, 10), U32.is_eq(uu, 13), e10, e13), ec)))
    : M5.k3.Fast(uu, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)}
  %M5.k3.scq(U32.is_eq(uu, 34), U32.is_eq(uu, 39), U32.is_eq(uu, 13), uu, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf,
    e34, e13, fast) : kk.pd(gk, T.doc.read(rest, _))
  ih(bk, un, lf)

# `\u` and four digits push the character they name, and leave back at the
# segment's state and uni and left at 0
def k3p.u4(
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
  +gk: K3G,
  eo: {D3.k3.scalar(D3.k3.hex4(dd, cc, bb, aa)) == True{} : Bool},
  ih: k3p.Then(hd, rw, hs, he, ps, sk, ab, Chr{D3.k3.hex4(dd, cc, bb, aa)} <> buf, rest, gk)
) -> kk.pd(gk, T.doc.read(D3.k3.pc.text(D3.KpU4{dd, cc, bb, aa}, rest), T.MScan{M5.k3.q(hd, rw, hs, he, ps, sk, ab,
  bk, un,
  lf, buf)})):
  %M5.k3.hx.open(False{}, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, D3.k3.hex4.text(dd, cc, bb, aa, rest))
    : kk.pd(gk, _)
  %M5.k3.hx.rmid(dd, hd, rw, hs, he, ps, sk, ab, M9.qs.lex(hd), 0, 4, buf, SCon{D3.k3.hex.char(cc),
    SCon{D3.k3.hex.char(bb), SCon{D3.k3.hex.char(aa), rest}}}, {==}) : kk.pd(gk, _)
  %M5.k3.hx.rmid(cc, hd, rw, hs, he, ps, sk, ab, M9.qs.lex(hd), D3.k3.hex.acc(0, dd), 3, buf,
    SCon{D3.k3.hex.char(bb), SCon{D3.k3.hex.char(aa), rest}}, {==}) : kk.pd(gk, _)
  %M5.k3.hx.rmid(bb, hd, rw, hs, he, ps, sk, ab, M9.qs.lex(hd), D3.k3.hex.acc(D3.k3.hex.acc(0, dd), cc), 2, buf,
    SCon{D3.k3.hex.char(aa), rest}, {==}) : kk.pd(gk, _)
  %M5.k3.hx.rlast(aa, hd, rw, hs, he, ps, sk, ab, M9.qs.lex(hd), D3.k3.hex.acc(D3.k3.hex.acc(D3.k3.hex.acc(0, dd),
    cc), bb), 1, buf, rest, {==}, eo) : kk.pd(gk, _)
  ih(M9.qs.lex(hd), 0, 0)

# `\U` and eight digits push the character they name, and leave back at the
# segment's state and uni and left at 0
def k3p.u8(
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
  +gk: K3G,
  eo: {D3.k3.scalar(D3.k3.hex8(hh, gg, ff, ee, dd, cc, bb, aa)) == True{} : Bool},
  ih: k3p.Then(hd, rw, hs, he, ps, sk, ab, Chr{D3.k3.hex8(hh, gg, ff, ee, dd, cc, bb, aa)} <> buf, rest, gk)
) -> kk.pd(gk, T.doc.read(D3.k3.pc.text(D3.KpU8{hh, gg, ff, ee, dd, cc, bb, aa}, rest), T.MScan{M5.k3.q(hd, rw, hs,
  he, ps,
  sk, ab, bk, un, lf, buf)})):
  +t4 = D3.k3.hex4.text(dd, cc, bb, aa, rest)
  +a1 = D3.k3.hex.acc(0, hh)
  +a2 = D3.k3.hex.acc(a1, gg)
  +a3 = D3.k3.hex.acc(a2, ff)
  +a4 = D3.k3.hex.acc(a3, ee)
  +a5 = D3.k3.hex.acc(a4, dd)
  +a6 = D3.k3.hex.acc(a5, cc)
  +a7 = D3.k3.hex.acc(a6, bb)
  +sl = M9.qs.lex(hd)
  %M5.k3.hx.open(True{}, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, D3.k3.hex4.text(hh, gg, ff, ee, t4))
    : kk.pd(gk, _)
  %M5.k3.hx.rmid(hh, hd, rw, hs, he, ps, sk, ab, sl, 0, 8, buf, SCon{D3.k3.hex.char(gg), SCon{D3.k3.hex.char(ff),
    SCon{D3.k3.hex.char(ee), t4}}}, {==}) : kk.pd(gk, _)
  %M5.k3.hx.rmid(gg, hd, rw, hs, he, ps, sk, ab, sl, a1, 7, buf, SCon{D3.k3.hex.char(ff), SCon{D3.k3.hex.char(ee),
    t4}}, {==}) : kk.pd(gk, _)
  %M5.k3.hx.rmid(ff, hd, rw, hs, he, ps, sk, ab, sl, a2, 6, buf, SCon{D3.k3.hex.char(ee), t4}, {==})
    : kk.pd(gk, _)
  %M5.k3.hx.rmid(ee, hd, rw, hs, he, ps, sk, ab, sl, a3, 5, buf, t4, {==}) : kk.pd(gk, _)
  %M5.k3.hx.rmid(dd, hd, rw, hs, he, ps, sk, ab, sl, a4, 4, buf, SCon{D3.k3.hex.char(cc),
    SCon{D3.k3.hex.char(bb), SCon{D3.k3.hex.char(aa), rest}}}, {==}) : kk.pd(gk, _)
  %M5.k3.hx.rmid(cc, hd, rw, hs, he, ps, sk, ab, sl, a5, 3, buf, SCon{D3.k3.hex.char(bb), SCon{D3.k3.hex.char(aa),
    rest}}, {==}) : kk.pd(gk, _)
  %M5.k3.hx.rmid(bb, hd, rw, hs, he, ps, sk, ab, sl, a6, 2, buf, SCon{D3.k3.hex.char(aa), rest}, {==})
    : kk.pd(gk, _)
  %M5.k3.hx.rlast(aa, hd, rw, hs, he, ps, sk, ab, sl, a7, 1, buf, rest, {==}, eo) : kk.pd(gk, _)
  ih(sl, 0, 0)

# a character written as itself read from the segment, then the rest
def k3p.PcG(
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
  +gk: K3G
) -> Type:
  k3p.Then(hd, rw, hs, he, ps, sk, ab, cc <> buf, rest, gk) ->
    kk.pd(gk, T.doc.read(SCon{cc, rest}, T.MScan{M5.k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)}))

# a character written as itself: a tab, or one that is no quote, no
# backslash and no control
def k3p.chr(
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
  +gk: K3G,
  +eb: {Laws.k3.bchar(Chr{uu}) == True{} : Bool}
) -> k3p.PcG(Chr{uu}, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, gk):
  match t9:
    case True{}:
      %Equal.sym(Char, Chr{uu}, Chr{9}, Eq.u32_eq(uu, 9, e9)) : k3p.PcG(_, hd, rw, hs, he, ps, sk, ab, bk, un, lf,
        buf, rest, gk)
      ih => k3p.tab(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, gk, ih)
    case False{}:
      +tq = U32.is_eq(uu, 34)
      +tb = U32.is_eq(uu, 92)
      +tc = Bool.or(U32.is_lt(uu, 32), U32.is_eq(uu, 127))
      +tt = U32.is_eq(uu, 9)
      ih => k3p.plain(uu, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, gk, M5.k3.bc.q(tq, tb, tc, tt, eb),
        M5.k3.bc.b(tq, tb, tc, tt, eb), M5.k3.bc.c(tq, tb, tc, tt, e9, eb), ih)

# one piece a basic string may hold pushes the character it stands for
def k3p.pc(
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
  +gk: K3G,
  eo: {Laws.k3.pc.ok(pp) == True{} : Bool},
  ih: k3p.Then(hd, rw, hs, he, ps, sk, ab, D3.k3.pc.char(pp) <> buf, rest, gk)
) -> kk.pd(gk, T.doc.read(D3.k3.pc.text(pp, rest), T.MScan{M5.k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)})):
  match pp:
    case D3.KpChar{cc}:
      match cc:
        case Chr{+uu}:
          k3p.chr(U32.is_eq(uu, 9), uu, {==}, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, gk, eo)(ih)
    case D3.KpEsc{mm}:
      k3p.esc(mm, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, gk, ih)
    case D3.KpU4{+dd, +cc, +bb, +aa}:
      k3p.u4(dd, cc, bb, aa, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, gk, eo, ih)
    case D3.KpU8{+hh, +gg, +ff, +ee, +dd, +cc, +bb, +aa}:
      k3p.u8(hh, gg, ff, ee, dd, cc, bb, aa, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, rest, gk, eo, ih)

# every piece of a list a basic string may hold, in order: the rest is read
# with their characters pushed, from wherever the last piece left back, uni
# and left
def k3p.pcs(
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
  +gk: K3G,
  +eo: {Laws.k3.pcs.ok(pl) == True{} : Bool},
  ih: k3p.Then(hd, rw, hs, he, ps, sk, ab, M3.rev.onto(D3.k3.pcs.name(pl), buf), rest, gk)
) -> kk.pd(gk, T.doc.read(D3.k3.pcs.text(pl, rest), T.MScan{M5.k3.q(hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf)})):
  match pl:
    case []:
      ih(bk, un, lf)
    case +pp <> +pr:
      k3p.pc(pp, hd, rw, hs, he, ps, sk, ab, bk, un, lf, buf, D3.k3.pcs.text(pr, rest), gk,
        Eq.and.left(Laws.k3.pc.ok(pp), Laws.k3.pcs.ok(pr), eo),
        +b2 => +u2 => +l2 => k3p.pcs(pr, hd, rw, hs, he, ps, sk, ab, b2, u2, l2, D3.k3.pc.char(pp) <> buf, rest,
          gk, Eq.and.right(Laws.k3.pc.ok(pp), Laws.k3.pcs.ok(pr), eo), ih))

# the rest of the text read after a segment and what ends it, from every
# back, qkind, uni and left
def k3p.KT(
  +cl: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +sk: List<&2, T.Ctx>,
  +ab: Bool,
  +rest: String,
  +gk: K3G
) -> Type:
  @b2: T.Lex -> @q2: T.QKind -> @u2: U32 -> @l2: U32 ->
    kk.pd(gk, T.doc.read(rest, T.MScan{M5.k3.w(rw, hs, he, ps, [], M7.k3.aft(cl), b2, q2, sk, u2, l2, ab)}))

# a segment's name pushed onto parts, then blank space and a dot or `=`: the
# rest is read from there
def k3p.fin(
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
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +rest: String,
  +gk: K3G,
  ih: k3p.KT(cl, rw, hs, he, nm <> ps, sk, ab, rest, gk)
) -> kk.pd(gk, T.doc.read(String.append(D2.gap(gs), SCon{M7.k3.dl(cl), rest}), T.MScan{M5.k3.w(rw, hs, he,
  T.buf.str(bf) <> ps,
  [], T.LAfter{}, bk, qk, sk, un, lf, ab)})):
  %M7.k3.agap(gs, SCon{M7.k3.dl(cl), rest}, rw, hs, he, T.buf.str(bf) <> ps, bk, qk, sk, un, lf, ab) : kk.pd(gk, _)
  %M7.k3.adl(cl, rw, hs, he, T.buf.str(bf) <> ps, bk, qk, sk, un, lf, ab, rest) : kk.pd(gk, _)
  %en : kk.pd(gk, T.doc.read(rest, T.MScan{M5.k3.w(rw, hs, he, _ <> ps, [], M7.k3.aft(cl), bk, qk, sk, un, lf, ab)}))
  ih(bk, qk, un, lf)

# a bare segment, its blank space and a dot or `=`: the rest is read with the
# segment pushed, and back, qkind, uni and left as they were
def k3p.bseg(
  +xx: U32,
  +tt: String,
  +gs: List<&2, Bool>,
  +cl: Bool,
  +dt: Bool,
  +at: Laws.KPos,
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
  +rest: String,
  +gk: K3G,
  +ee: {T.bare.all.step(T.bare.at(Chr{xx}), _u => T.bare.all(String.to_list(tt))) == True{} : Bool},
  ih: k3p.KT(cl, rw, hs, he, SCon{Chr{xx}, tt} <> M5.k3.ps0(dt, ps), sk, ab, rest, gk)
) -> kk.pd(gk, T.doc.read(String.append(SCon{Chr{xx}, tt}, String.append(D2.gap(gs), SCon{M7.k3.dl(cl), rest})),
  T.MScan{M5.k3.w(rw, hs, he, M5.k3.ps0(dt, ps), [], M7.k3.lex0(dt, at), bk, qk, sk, un, lf, ab)})):
  %M7.k3.b1(dt, at, rw, hs, he, ps, bk, qk, sk, un, lf, ab, xx, M16.ball.head(T.bare.at(Chr{xx}), String.to_list(tt),
      ee))
    : kk.pd(gk, T.doc.read(String.append(tt, String.append(D2.gap(gs), SCon{M7.k3.dl(cl), rest})), _))
  %M7.k3.bbody(tt, String.append(D2.gap(gs), SCon{M7.k3.dl(cl), rest}), rw, hs, he, M5.k3.ps0(dt, ps), [Chr{xx}], bk,
      qk, sk,
    un, lf, ab, M16.ball.tail(T.bare.at(Chr{xx}),
    String.to_list(tt), ee)) : kk.pd(gk, _)
  %M7.k3.bend(gs, cl, rw, hs, he, M5.k3.ps0(dt, ps), M3.rev.onto(tt, [Chr{xx}]), bk, qk, sk, un, lf, ab, rest,
      M16.rev.full(tt,
    Chr{xx},
    [])) : kk.pd(gk, _)
  %Equal.sym(String, T.buf.str(M3.rev.onto(tt, [Chr{xx}])), SCon{Chr{xx}, tt}, M16.wh.bname(xx, tt)) : kk.pd(gk,
    T.doc.read(rest,
    T.MScan{M5.k3.w(rw, hs, he, _ <> M5.k3.ps0(dt, ps), [], M7.k3.aft(cl), bk, qk, sk, un, lf, ab)}))
  ih(bk, qk, un, lf)

# a basic segment of pieces, its blank space and a dot or `=`: the rest is
# read with the segment pushed under the characters the pieces stand for,
# from wherever the last piece left back, uni and left
def k3p.qseg(
  +pl: List<&2, D3.KPiece>,
  +gs: List<&2, Bool>,
  +cl: Bool,
  +dt: Bool,
  +at: Laws.KPos,
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
  +rest: String,
  +gk: K3G,
  eo: {Laws.k3.pcs.ok(pl) == True{} : Bool},
  ih: k3p.KT(cl, rw, hs, he, D3.k3.pcs.name(pl) <> M5.k3.ps0(dt, ps), sk, ab, rest, gk)
) -> kk.pd(gk, T.doc.read(SCon{'"', D3.k3.pcs.text(pl, SCon{'"', String.append(D2.gap(gs), SCon{M7.k3.dl(cl),
  rest})})},
  T.MScan{M5.k3.w(rw, hs, he, M5.k3.ps0(dt, ps), [], M7.k3.lex0(dt, at), bk, qk, sk, un, lf, ab)})):
  %M7.k3.qopen(dt, at, rw, hs, he, ps, bk, qk, sk, un, lf, ab) : kk.pd(gk, T.doc.read(D3.k3.pcs.text(pl, SCon{'"',
    String.append(D2.gap(gs), SCon{M7.k3.dl(cl), rest})}),
    _))
  k3p.pcs(pl, False{}, rw, hs, he, M5.k3.ps0(dt, ps), sk, ab, bk, un, lf, [], SCon{'"', String.append(D2.gap(gs),
    SCon{M7.k3.dl(cl), rest})}, gk, eo, +b2 => +u2 => +l2 =>
    k3p.fin(D3.k3.pcs.name(pl), M3.rev.onto(D3.k3.pcs.name(pl), []), M16.k3.nm(D3.k3.pcs.name(pl)), gs, cl, rw, hs, he,
      M5.k3.ps0(dt, ps), b2, T.QBasic{}, sk, u2, l2, ab, rest, gk, ih))

# a literal segment, its blank space and a dot or `=`: the rest is read with
# the segment pushed under its characters, and back, uni and left as they
# were
def k3p.lseg(
  +name: String,
  +gs: List<&2, Bool>,
  +cl: Bool,
  +dt: Bool,
  +at: Laws.KPos,
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
  +rest: String,
  +gk: K3G,
  el: {Laws.lit.text(name) == True{} : Bool},
  ih: k3p.KT(cl, rw, hs, he, name <> M5.k3.ps0(dt, ps), sk, ab, rest, gk)
) -> kk.pd(gk, T.doc.read(SCon{'\'', String.append(name, SCon{'\'', String.append(D2.gap(gs), SCon{M7.k3.dl(cl),
  rest})})},
  T.MScan{M5.k3.w(rw, hs, he, M5.k3.ps0(dt, ps), [], M7.k3.lex0(dt, at), bk, qk, sk, un, lf, ab)})):
  %M7.k3.lopen(dt, at, rw, hs, he, ps, bk, qk, sk, un, lf, ab) : kk.pd(gk, T.doc.read(String.append(name, SCon{'\'',
    String.append(D2.gap(gs), SCon{M7.k3.dl(cl), rest})}), _))
  %Equal.sym(T.Doc, T.doc.read(String.append(name, SCon{'\'', String.append(D2.gap(gs), SCon{M7.k3.dl(cl), rest})}),
    T.MScan{M5.k3.l(False{}, rw, hs, he, M5.k3.ps0(dt, ps), sk, ab, bk, un, lf, [])}), T.doc.read(SCon{'\'',
      String.append(D2.gap(gs), SCon{M7.k3.dl(cl), rest})}, T.MScan{M5.k3.l(False{}, rw, hs, he, M5.k3.ps0(dt, ps), sk,
          ab,
        bk, un, lf, M3.rev.onto(name, []))}), M5.k3.l.body(name, SCon{'\'', String.append(D2.gap(gs), SCon{M7.k3.dl(cl),
          rest})}, False{}, rw, hs, he, M5.k3.ps0(dt, ps), sk, ab, bk, un, lf, [], el)) : kk.pd(gk, _)
  k3p.fin(name, M3.rev.onto(name, []), M16.k3.nm(name), gs, cl, rw, hs, he, M5.k3.ps0(dt, ps), bk, T.QLit{}, sk, un,
      lf, ab,
    rest, gk, ih)

# a segment spelled any way toml.abnf allows, its blank space and a dot or
# `=`
def k3p.seg(
  sg: D3.KSeg,
  +gs: List<&2, Bool>,
  +cl: Bool,
  +dt: Bool,
  +at: Laws.KPos,
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
  +rest: String,
  +gk: K3G,
  eo: {Laws.k3.seg.ok(sg) == True{} : Bool},
  ih: k3p.KT(cl, rw, hs, he, D3.k3.seg.name(sg) <> M5.k3.ps0(dt, ps), sk, ab, rest, gk)
) -> kk.pd(gk, T.doc.read(D3.k3.seg.text(sg, String.append(D2.gap(gs), SCon{M7.k3.dl(cl), rest})), T.MScan{M5.k3.w(rw,
  hs, he,
  M5.k3.ps0(dt, ps), [], M7.k3.lex0(dt, at), bk, qk, sk, un, lf, ab)})):
  match sg:
    case D3.KsBare{name}:
      match name:
        case SNil{}:
          kk.pdx(gk, T.doc.read(String.append(SNil{}, String.append(D2.gap(gs), SCon{M7.k3.dl(cl), rest})),
            T.MScan{M5.k3.w(rw, hs, he, M5.k3.ps0(dt, ps), [], M7.k3.lex0(dt, at), bk, qk, sk, un, lf, ab)}), eo)
        case SCon{hh, +tt}:
          match hh:
            case Chr{+xx}:
              k3p.bseg(xx, tt, gs, cl, dt, at, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, gk, eo, ih)
    case D3.KsBasic{+pl}:
      k3p.qseg(pl, gs, cl, dt, at, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, gk, eo, ih)
    case D3.KsLit{+name}:
      k3p.lseg(name, gs, cl, dt, at, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, gk, eo, ih)

# a dotted key's segments, then blank space and `=`: the rest is read with
# every segment pushed onto parts, newest first
def k3p.keys(
  ds: List<&2, Laws.KDot>,
  +last: D3.KSeg,
  +g: List<&2, Bool>,
  +dt: Bool,
  +at: Laws.KPos,
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
  +rest: String,
  +gk: K3G,
  +eo: {Laws.k3.dk.ok(ds, last) == True{} : Bool},
  ih: k3p.KT(True{}, rw, hs, he, M5.k3.acc(ds, last, dt, ps), sk, ab, rest, gk)
) -> kk.pd(gk, T.doc.read(Laws.k3.dk.text(ds, last, String.append(D2.gap(g), SCon{'=', rest})), T.MScan{M5.k3.w(rw, hs,
  he,
  M5.k3.ps0(dt, ps), [], M7.k3.lex0(dt, at), bk, qk, sk, un, lf, ab)})):
  match ds:
    case []:
      k3p.seg(last, g, True{}, dt, at, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, gk, eo, ih)
    case Laws.KDot{+sg, g1, +g2} <> +dr:
      k3p.seg(sg, g1, False{}, dt, at, rw, hs, he, ps, bk, qk, sk, un, lf, ab, String.append(D2.gap(g2),
        Laws.k3.dk.text(dr, last, String.append(D2.gap(g), SCon{'=', rest}))), gk, Eq.and.left(Laws.k3.seg.ok(sg),
        Laws.k3.dk.ok(dr, last), eo), +b2 => +q2 => +u2 => +l2 =>
        %M7.k3.dgap(g2, Laws.k3.dk.text(dr, last, String.append(D2.gap(g), SCon{'=', rest})), rw, hs, he,
          D3.k3.seg.name(sg) <> M5.k3.ps0(dt, ps), b2, q2, sk, u2, l2, ab) : kk.pd(gk, _)
        k3p.keys(dr, last, g, True{}, at, rw, hs, he, D3.k3.seg.name(sg) <> M5.k3.ps0(dt, ps), b2, q2, sk, u2, l2, ab,
          rest, gk,
          Eq.and.right(Laws.k3.seg.ok(sg), Laws.k3.dk.ok(dr, last), eo), ih))

# the rest of the text after a header segment, read from every back, qkind,
# uni and left
def k3p.HT(
  +cl: Bool,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +ab: Bool,
  +rest: String,
  +gk: K3G
) -> Type:
  @b2: T.Lex -> @q2: T.QKind -> @u2: U32 -> @l2: U32 ->
    kk.pd(gk, T.doc.read(rest, T.MScan{M5.k3.haft(cl, rw, hs, he, ps, b2, q2, u2, l2, ab)}))

# a header segment's name pushed onto parts, then blank space and a dot or
# the bracket: the rest is read from there
def k3p.hfin(
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
  +gk: K3G,
  ih: k3p.HT(cl, rw, hs, he, nm <> ps, ab, rest, gk)
) -> kk.pd(gk, T.doc.read(String.append(D2.gap(gs), SCon{M5.k3.hdl(cl), rest}), T.MScan{M5.k3.w(rw, hs, he,
  T.buf.str(bf) <> ps,
  [], T.LHeadGap{}, bk, qk, [], un, lf, ab)})):
  %M5.k3.hgap(gs, SCon{M5.k3.hdl(cl), rest}, rw, hs, he, T.buf.str(bf) <> ps, bk, qk, un, lf, ab) : kk.pd(gk, _)
  %M5.k3.hgdl(cl, rw, hs, he, T.buf.str(bf) <> ps, bk, qk, un, lf, ab, rest) : kk.pd(gk, _)
  %en : kk.pd(gk, T.doc.read(rest, T.MScan{M5.k3.haft(cl, rw, hs, he, _ <> ps, bk, qk, un, lf, ab)}))
  ih(bk, qk, un, lf)

# a bare header segment, its blank space and a dot or the bracket
def k3p.hbseg(
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
  +gk: K3G,
  +ee: {T.bare.all.step(T.bare.at(Chr{xx}), _u => T.bare.all(String.to_list(tt))) == True{} : Bool},
  ih: k3p.HT(cl, rw, hs, he, SCon{Chr{xx}, tt} <> M5.k3.ps0(dt, ps), ab, rest, gk)
) -> kk.pd(gk, T.doc.read(String.append(SCon{Chr{xx}, tt}, String.append(D2.gap(gs), SCon{M5.k3.hdl(cl), rest})),
  T.MScan{M5.k3.w(rw, hs, he, M5.k3.ps0(dt, ps), [], M5.k3.hlex0(dt), bk, qk, [], un, lf, ab)})):
  %M5.k3.hb1(dt, rw, hs, he, ps, bk, qk, un, lf, ab, xx, M16.ball.head(T.bare.at(Chr{xx}), String.to_list(tt), ee))
    : kk.pd(gk, T.doc.read(String.append(tt, String.append(D2.gap(gs), SCon{M5.k3.hdl(cl), rest})), _))
  %M5.k3.hbbody(tt, String.append(D2.gap(gs), SCon{M5.k3.hdl(cl), rest}), rw, hs, he, M5.k3.ps0(dt, ps), Chr{xx}, [],
      bk, qk,
    un, lf, ab, M16.ball.tail(T.bare.at(Chr{xx}),
    String.to_list(tt), ee)) : kk.pd(gk, _)
  %M5.k3.hbend(gs, cl, rw, hs, he, M5.k3.ps0(dt, ps), M3.rev.onto(tt, [Chr{xx}]), bk, qk, un, lf, ab, rest,
      M16.rev.full(tt,
    Chr{xx}, []))
    : kk.pd(gk, _)
  %Equal.sym(String, T.buf.str(M3.rev.onto(tt, [Chr{xx}])), SCon{Chr{xx}, tt}, M16.wh.bname(xx, tt)) : kk.pd(gk,
    T.doc.read(rest,
    T.MScan{M5.k3.haft(cl, rw, hs, he, _ <> M5.k3.ps0(dt, ps), bk, qk, un, lf, ab)}))
  ih(bk, qk, un, lf)

# a basic header segment of pieces, its blank space and a dot or the
# bracket
def k3p.hqseg(
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
  +gk: K3G,
  eo: {Laws.k3.pcs.ok(pl) == True{} : Bool},
  ih: k3p.HT(cl, rw, hs, he, D3.k3.pcs.name(pl) <> M5.k3.ps0(dt, ps), ab, rest, gk)
) -> kk.pd(gk, T.doc.read(SCon{'"', D3.k3.pcs.text(pl, SCon{'"', String.append(D2.gap(gs), SCon{M5.k3.hdl(cl),
  rest})})},
  T.MScan{M5.k3.w(rw, hs, he, M5.k3.ps0(dt, ps), [], M5.k3.hlex0(dt), bk, qk, [], un, lf, ab)})):
  %M5.k3.hqopen(dt, rw, hs, he, ps, bk, qk, un, lf, ab) : kk.pd(gk, T.doc.read(D3.k3.pcs.text(pl, SCon{'"',
    String.append(D2.gap(gs), SCon{M5.k3.hdl(cl), rest})}), _))
  k3p.pcs(pl, True{}, rw, hs, he, M5.k3.ps0(dt, ps), [], ab, bk, un, lf, [], SCon{'"', String.append(D2.gap(gs),
    SCon{M5.k3.hdl(cl), rest})}, gk, eo, +b2 => +u2 => +l2 =>
    k3p.hfin(D3.k3.pcs.name(pl), M3.rev.onto(D3.k3.pcs.name(pl), []), M16.k3.nm(D3.k3.pcs.name(pl)), gs, cl, rw, hs,
      he, M5.k3.ps0(dt, ps), b2, T.QBasic{}, u2, l2, ab, rest, gk, ih))

# a literal header segment, its blank space and a dot or the bracket
def k3p.hlseg(
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
  +gk: K3G,
  el: {Laws.lit.text(name) == True{} : Bool},
  ih: k3p.HT(cl, rw, hs, he, name <> M5.k3.ps0(dt, ps), ab, rest, gk)
) -> kk.pd(gk, T.doc.read(SCon{'\'', String.append(name, SCon{'\'', String.append(D2.gap(gs), SCon{M5.k3.hdl(cl),
  rest})})},
  T.MScan{M5.k3.w(rw, hs, he, M5.k3.ps0(dt, ps), [], M5.k3.hlex0(dt), bk, qk, [], un, lf, ab)})):
  %M5.k3.hlopen(dt, rw, hs, he, ps, bk, qk, un, lf, ab) : kk.pd(gk, T.doc.read(String.append(name, SCon{'\'',
    String.append(D2.gap(gs), SCon{M5.k3.hdl(cl), rest})}), _))
  %Equal.sym(T.Doc, T.doc.read(String.append(name, SCon{'\'', String.append(D2.gap(gs), SCon{M5.k3.hdl(cl), rest})}),
    T.MScan{M5.k3.l(True{}, rw, hs, he, M5.k3.ps0(dt, ps), [], ab, bk, un, lf, [])}), T.doc.read(SCon{'\'',
      String.append(D2.gap(gs), SCon{M5.k3.hdl(cl), rest})}, T.MScan{M5.k3.l(True{}, rw, hs, he, M5.k3.ps0(dt, ps), [],
          ab,
        bk, un, lf, M3.rev.onto(name, []))}), M5.k3.l.body(name, SCon{'\'', String.append(D2.gap(gs),
            SCon{M5.k3.hdl(cl),
          rest})}, True{}, rw, hs, he, M5.k3.ps0(dt, ps), [], ab, bk, un, lf, [], el)) : kk.pd(gk, _)
  k3p.hfin(name, M3.rev.onto(name, []), M16.k3.nm(name), gs, cl, rw, hs, he, M5.k3.ps0(dt, ps), bk, T.QLit{}, un, lf,
      ab, rest,
    gk, ih)

# a header segment spelled any way toml.abnf allows, its blank space and a
# dot or the bracket
def k3p.hseg(
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
  +gk: K3G,
  eo: {Laws.k3.seg.ok(sg) == True{} : Bool},
  ih: k3p.HT(cl, rw, hs, he, D3.k3.seg.name(sg) <> M5.k3.ps0(dt, ps), ab, rest, gk)
) -> kk.pd(gk, T.doc.read(D3.k3.seg.text(sg, String.append(D2.gap(gs), SCon{M5.k3.hdl(cl), rest})), T.MScan{M5.k3.w(rw,
  hs, he,
  M5.k3.ps0(dt, ps), [], M5.k3.hlex0(dt), bk, qk, [], un, lf, ab)})):
  match sg:
    case D3.KsBare{name}:
      match name:
        case SNil{}:
          kk.pdx(gk, T.doc.read(String.append(SNil{}, String.append(D2.gap(gs), SCon{M5.k3.hdl(cl), rest})),
            T.MScan{M5.k3.w(rw, hs, he, M5.k3.ps0(dt, ps), [], M5.k3.hlex0(dt), bk, qk, [], un, lf, ab)}), eo)
        case SCon{hh, +tt}:
          match hh:
            case Chr{+xx}:
              k3p.hbseg(xx, tt, gs, cl, dt, rw, hs, he, ps, bk, qk, un, lf, ab, rest, gk, eo, ih)
    case D3.KsBasic{+pl}:
      k3p.hqseg(pl, gs, cl, dt, rw, hs, he, ps, bk, qk, un, lf, ab, rest, gk, eo, ih)
    case D3.KsLit{+name}:
      k3p.hlseg(name, gs, cl, dt, rw, hs, he, ps, bk, qk, un, lf, ab, rest, gk, eo, ih)

# a header's segments, then blank space and the bracket: the rest is read
# with every segment pushed onto parts, newest first
def k3p.hkeys(
  ds: List<&2, Laws.KDot>,
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
  +gk: K3G,
  +eo: {Laws.k3.dk.ok(ds, last) == True{} : Bool},
  ih: k3p.HT(True{}, rw, hs, he, M5.k3.acc(ds, last, dt, ps), ab, rest, gk)
) -> kk.pd(gk, T.doc.read(Laws.k3.dk.text(ds, last, String.append(D2.gap(g9), SCon{']', rest})), T.MScan{M5.k3.w(rw,
  hs, he,
  M5.k3.ps0(dt, ps), [], M5.k3.hlex0(dt), bk, qk, [], un, lf, ab)})):
  match ds:
    case []:
      k3p.hseg(last, g9, True{}, dt, rw, hs, he, ps, bk, qk, un, lf, ab, rest, gk, eo, ih)
    case Laws.KDot{+sg, g1, +g2} <> +dr:
      k3p.hseg(sg, g1, False{}, dt, rw, hs, he, ps, bk, qk, un, lf, ab, String.append(D2.gap(g2),
        Laws.k3.dk.text(dr, last, String.append(D2.gap(g9), SCon{']', rest}))), gk, Eq.and.left(Laws.k3.seg.ok(sg),
        Laws.k3.dk.ok(dr, last), eo), +b2 => +q2 => +u2 => +l2 =>
        %M5.k3.hdgap(g2, Laws.k3.dk.text(dr, last, String.append(D2.gap(g9), SCon{']', rest})), rw, hs, he,
          D3.k3.seg.name(sg) <> M5.k3.ps0(dt, ps), b2, q2, u2, l2, ab) : kk.pd(gk, _)
        k3p.hkeys(dr, last, g9, True{}, rw, hs, he, D3.k3.seg.name(sg) <> M5.k3.ps0(dt, ps), b2, q2, u2, l2, ab, rest,
          gk,
          Eq.and.right(Laws.k3.seg.ok(sg), Laws.k3.dk.ok(dr, last), eo), ih))

# a path equals itself, read by leq
def kk.leq.self(aa: List<&2, String>) -> {kk.leq(aa, aa) == True{} : Bool}:
  match aa:
    case []:
      {==}
    case +xx <> +xs:
      M17.gd.tt(T.str.eq(xx, xx), kk.leq(xs, xs), M15.str.eq.self(xx), kk.leq.self(xs))

# a key whose parts are its name, then its other parts, is pending in the
# table they name, with no array open around it
def kk.pendv(
  stack: List<&2, T.Ctx>,
  +here: List<&2, String>,
  +kk: String,
  +ps: List<&2, String>,
  +es: {Laws.k3.noarr1(stack) == True{} : Bool}
) -> {kk.pend(K3G{Laws.k3.pl(stack, here, ps, []), kk}, stack, here, kk <> ps) == True{} : Bool}:
  match stack:
    case []:
      M17.gd.tt(T.str.eq(kk, kk), kk.leq(Laws.k3.pl([], here, ps, []), Laws.k3.pl([], here, ps, [])),
          M15.str.eq.self(kk),
        kk.leq.self(Laws.k3.pl([], here, ps, [])))
    case T.CArr{_i, _p, _h} <> _t:
      es
    case T.CInl{+rr, +sp, +sh} <> +rest:
      M17.gd.tt(T.str.eq(kk, kk), kk.leq(Laws.k3.pl(T.CInl{rr, sp, sh} <> rest, here, ps, []), Laws.k3.pl(T.CInl{rr, sp,
        sh} <> rest, here, ps, [])), M15.str.eq.self(kk), kk.leq.self(Laws.k3.pl(T.CInl{rr, sp, sh} <> rest, here, ps,
            [])))

def Laws.key_found_after_equals(rows, heads, here, k, ps, stack, arrtab, back, qkind, uni, left, rest, es, eo):
  kk.read(K3G{Laws.k3.pl(stack, here, ps, []), k}, rest, Laws.k3.val(rows, heads, here, k <> ps, stack, arrtab, back,
    qkind, uni, left), bo.or.tl(kk.pend(K3G{Laws.k3.pl(stack, here, ps, []), k}, stack, here, k <> ps),
      Bool.or(kk.PF(K3G{Laws.k3.pl(stack, here, ps, []), k}, stack), kk.L(K3G{Laws.k3.pl(stack, here, ps, []), k},
        stack, rows)), kk.pendv(stack, here, k, ps, es)))(eo)

# a reversal of a path with a last name puts the name first
def kk.rvsnoc(
  xs: List<&2, String>,
  +nn: String,
  +acc: List<&2, String>
) -> {List.reverse.go(&2, String, List.append(&2, String, xs, [nn]), acc) == nn <> List.reverse.go(&2, String, xs,
  acc) : List<&2, String>}:
  match xs:
    case []:
      {==}
    case +xx <> xr:
      kk.rvsnoc(xr, nn, xx <> acc)

# a dotted key's names are the names but the last, then the last
def kk.dksplit(
  ds: List<&2, Laws.KDot>,
  +last: D3.KSeg
) -> {Laws.k3.dk.names(ds, last) == List.append(&2, String, Laws.k3.dk.init(ds), [D3.k3.seg.name(last)])
  : List<&2, String>}:
  match ds:
    case []:
      {==}
    case Laws.KDot{+sg, _g1, _g2} <> rest:
      Equal.cong(List<&2, String>, List<&2, String>, zs => D3.k3.seg.name(sg) <> zs, Laws.k3.dk.names(rest, last),
        List.append(&2, String, Laws.k3.dk.init(rest), [D3.k3.seg.name(last)]), kk.dksplit(rest, last))

# a key's segments pushed onto parts are its last name, then the others
# reversed
def kk.accn(
  +ds: List<&2, Laws.KDot>,
  +last: D3.KSeg
) -> {M5.k3.acc(ds, last, False{}, []) == D3.k3.seg.name(last) <> List.reverse(&2, String, Laws.k3.dk.init(ds))
  : List<&2, String>}:
  Equal.trans(List<&2, String>, List.reverse.go(&2, String, Laws.k3.dk.names(ds, last), []), List.reverse.go(&2,
    String, List.append(&2, String, Laws.k3.dk.init(ds), [D3.k3.seg.name(last)]), []), D3.k3.seg.name(last) <>
      List.reverse(&2, String, Laws.k3.dk.init(ds)), Equal.cong(List<&2, String>, List<&2, String>, zs =>
        List.reverse.go(&2, String, zs, []), Laws.k3.dk.names(ds, last), List.append(&2, String, Laws.k3.dk.init(ds),
          [D3.k3.seg.name(last)]), kk.dksplit(ds, last)), kk.rvsnoc(Laws.k3.dk.init(ds), D3.k3.seg.name(last), []))

# a key read from where a key may start is pending in its table
def kk.pendk(
  +ds: List<&2, Laws.KDot>,
  +last: D3.KSeg,
  +stack: List<&2, T.Ctx>,
  +here: List<&2, String>,
  +es: {Laws.k3.noarr1(stack) == True{} : Bool}
) -> {kk.pend(K3G{Laws.k3.key.table(stack, here, ds), D3.k3.seg.name(last)}, stack, here, M5.k3.acc(ds, last, False{},
  [])) == True{} : Bool}:
  %Equal.sym(List<&2, String>, M5.k3.acc(ds, last, False{}, []), D3.k3.seg.name(last) <> List.reverse(&2, String,
    Laws.k3.dk.init(ds)), kk.accn(ds, last)) : {kk.pend(K3G{Laws.k3.key.table(stack, here, ds),
      D3.k3.seg.name(last)}, stack, here, _) == True{} : Bool}
  kk.pendv(stack, here, D3.k3.seg.name(last), List.reverse(&2, String, Laws.k3.dk.init(ds)), es)

# a key's text read from where a key may start, for what the document says
def k3p.keyread(
  +at: Laws.KPos,
  +g0: List<&2, Bool>,
  +ds: List<&2, Laws.KDot>,
  +last: D3.KSeg,
  +ok: {Laws.k3.dk.ok(ds, last) == True{} : Bool},
  +g: List<&2, Bool>,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>,
  +here: List<&2, String>,
  +stack: List<&2, T.Ctx>,
  +arrtab: Bool,
  +back: T.Lex,
  +qkind: T.QKind,
  +uni: U32,
  +left: U32,
  +rest: String,
  +gk: K3G,
  ih: k3p.KT(True{}, rows, heads, here, M5.k3.acc(ds, last, False{}, []), stack, arrtab, rest, gk)
) -> kk.pd(gk, Laws.k3.key.doc(at, g0, ds, last, g, rows, heads, here, stack, arrtab, back, qkind, uni, left, rest)):
  %k3.g0(g0, at, rows, heads, here, stack, arrtab, back, qkind, uni, left, Laws.k3.dk.text(ds, last,
    String.append(D2.gap(g), SCon{'=', rest}))) : kk.pd(gk, _)
  k3p.keys(ds, last, g, False{}, at, rows, heads, here, [], back, qkind, stack, uni, left, arrtab, rest, gk, ok, ih)

def Laws.key_found_anywhere(
  at,
  g0,
  ds,
  last,
  ok,
  g,
  rows,
  heads,
  here,
  stack,
  arrtab,
  back,
  qkind,
  uni,
  left,
  rest,
  es,
  eo
):
  k3p.keyread(at, g0, ds, last, ok, g, rows, heads, here, stack, arrtab, back, qkind, uni, left, rest,
    K3G{Laws.k3.key.table(stack, here, ds), D3.k3.seg.name(last)}, +b2 => +q2 => +u2 => +l2 =>
      kk.read(K3G{Laws.k3.key.table(stack, here, ds), D3.k3.seg.name(last)}, rest, M5.k3.w(rows, heads, here,
        M5.k3.acc(ds, last, False{}, []), [], T.LVal{}, b2, q2, stack, u2, l2, arrtab), bo.or.tl(kk.pend(K3G{
          Laws.k3.key.table(stack, here, ds), D3.k3.seg.name(last)}, stack, here, M5.k3.acc(ds, last, False{}, [])),
          Bool.or(kk.PF(K3G{Laws.k3.key.table(stack, here, ds), D3.k3.seg.name(last)}, stack), kk.L(K3G{
            Laws.k3.key.table(stack, here, ds), D3.k3.seg.name(last)}, stack, rows)), kk.pendk(ds, last, stack,
              here, es))))(eo)

# the rest of the text read after a header, from every back, qkind, uni and
# left, whatever its walk returned
def k3p.HRaw(
  +_arr: Bool,
  +_path: List<&2, String>,
  +_rw: List<&2, T.Val>,
  +_hs: List<&2, String>,
  +_rest: String,
  +_gk: K3G
) -> Type:
  @b2: T.Lex -> @q2: T.QKind -> @u2: U32 -> @l2: U32 -> kk.pd(_gk, T.doc.read(_rest,
    T.MScan{T.read.once2(T.head.apply(T.tree.walk(_path, T.Tw{_rw, D1.header_job(_arr), [], "", "", _hs, False{}}, 0),
      _path, b2, q2, u2, l2, False{}))}))

# the bracket runs the header's walk along the segments read, whatever it
# returns
def k3p.hend0(
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
  +rest: String,
  ne: {List.is_empty(&2, String, parts) == False{} : Bool},
  er: {List.reverse(&2, String, parts) == path : List<&2, String>}
) -> {T.doc.read(rest, T.MScan{T.read.once2(T.head.apply(T.tree.walk(path, T.Tw{rw, D1.header_job(ab), [], "", "",
  hs, False{}}, 0), path, bk, qk, un, lf, False{}))}) == T.doc.read(M5.k3.htail(ab, rest),
  T.MScan{M5.k3.haft(True{}, rw, hs, he, parts, bk, qk, un, lf, ab)}) : T.Doc}:
  match ab:
    case False{}:
      %Equal.sym(Bool, List.is_empty(&2, String, parts), False{}, ne) : {T.doc.read(rest,
        T.MScan{T.read.once2(T.head.apply(T.tree.walk(path, T.Tw{rw, T.JDef{}, [], "", "", hs, False{}}, 0), path, bk,
          qk, un, lf, False{}))}) == T.doc.read(rest,
          T.MScan{T.read.once2(T.head.go(_,
        M5.k3.w(rw, hs, he, parts, [], T.LHeadGap{}, bk, qk, [], un, lf, False{}), List.reverse(&2, String,
          parts)))}) : T.Doc}
      %Equal.sym(List<&2, String>, List.reverse(&2, String, parts), path, er) : {T.doc.read(rest,
        T.MScan{T.read.once2(T.head.apply(T.tree.walk(path, T.Tw{rw, T.JDef{}, [], "", "", hs, False{}}, 0), path, bk,
          qk, un, lf, False{}))}) == T.doc.read(rest,
        T.MScan{T.read.once2(T.head.apply(T.tree.walk(_, T.Tw{rw, T.JDef{}, [], "", "", hs, False{}}, 0), _, bk, qk,
        un, lf, False{}))}) : T.Doc}
      {==}
    case True{}:
      %Equal.sym(Bool, List.is_empty(&2, String, parts), False{}, ne) : {T.doc.read(rest,
        T.MScan{T.read.once2(T.head.apply(T.tree.walk(path, T.Tw{rw, T.JAot{}, [], "", "", hs, False{}}, 0), path, bk,
          qk, un, lf, False{}))}) == T.doc.read(rest,
          T.MScan{T.read.once2(T.head.go(_,
        M5.k3.w(rw, hs, he, parts, [], T.LHeadR{}, bk, qk, [], un, lf, True{}), List.reverse(&2, String,
          parts)))}) : T.Doc}
      %Equal.sym(List<&2, String>, List.reverse(&2, String, parts), path, er) : {T.doc.read(rest,
        T.MScan{T.read.once2(T.head.apply(T.tree.walk(path, T.Tw{rw, T.JAot{}, [], "", "", hs, False{}}, 0), path, bk,
          qk, un, lf, False{}))}) == T.doc.read(rest,
        T.MScan{T.read.once2(T.head.apply(T.tree.walk(_, T.Tw{rw, T.JAot{}, [], "", "", hs, False{}}, 0), _, bk, qk,
        un, lf, False{}))}) : T.Doc}
      {==}

# a whole header, from the start of a line in any table
def k3p.hcore(
  +arr: Bool,
  +g0: List<&2, Bool>,
  +ds: List<&2, Laws.KDot>,
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
  +rest: String,
  +gk: K3G,
  +eo: {Laws.k3.dk.ok(ds, last) == True{} : Bool},
  ih: k3p.HRaw(arr, Laws.k3.dk.names(ds, last), rw, hs, rest, gk)
) -> kk.pd(gk, T.doc.read(Laws.k3.hd.text(arr, g0, ds, last, g9, rest), T.MScan{Laws.k3.at(Laws.AtLine{}, rw, hs, he,
  [], a0,
  bk, qk, un, lf)})):
  match arr:
    case False{}:
      %M5.k3.hlead(g0, Laws.k3.dk.text(ds, last, String.append(D2.gap(g9), SCon{']', rest})), rw, hs, he, bk, qk, un,
          lf,
        False{}) : kk.pd(gk, _)
      k3p.hkeys(ds, last, g9, M5.k3.nz(g0), rw, hs, he, [], bk, qk, un, lf, False{}, rest, gk, eo, +b2 => +q2 => +u2 =>
        +l2 =>
        %k3p.hend0(False{}, rw, hs, he, M5.k3.acc(ds, last, M5.k3.nz(g0), []), b2, q2, u2, l2, Laws.k3.dk.names(ds,
            last),
          rest, M5.k3.ne(ds, last, M5.k3.ps0(M5.k3.nz(g0), [])), M5.k3.path(M5.k3.nz(g0), ds, last))
          : kk.pd(gk, _)
        ih(b2, q2, u2, l2))
    case True{}:
      %M5.k3.hlead(g0, Laws.k3.dk.text(ds, last, String.append(D2.gap(g9), SCon{']', SCon{']', rest}})), rw, hs, he,
        bk, qk, un, lf, True{}) : kk.pd(gk, _)
      k3p.hkeys(ds, last, g9, M5.k3.nz(g0), rw, hs, he, [], bk, qk, un, lf, True{}, SCon{']', rest}, gk, eo,
        +b2 => +q2 => +u2 => +l2 =>
        %k3p.hend0(True{}, rw, hs, he, M5.k3.acc(ds, last, M5.k3.nz(g0), []), b2, q2, u2, l2, Laws.k3.dk.names(ds,
            last),
          rest, M5.k3.ne(ds, last, M5.k3.ps0(M5.k3.nz(g0), [])), M5.k3.path(M5.k3.nz(g0), ds, last))
          : kk.pd(gk, _)
        ih(b2, q2, u2, l2))

# a header's walk holds the table it names, or fails
def kk.hwalk(
  +arr: Bool,
  +ds: List<&2, Laws.KDot>,
  +last: D3.KSeg,
  +rows: List<&2, T.Val>,
  +heads: List<&2, String>
) -> {kk.KE(K3G{Laws.k3.dk.init(ds), D3.k3.seg.name(last)}, T.tree.walk(Laws.k3.dk.names(ds, last), T.Tw{rows,
  D1.header_job(arr), [], "", "", heads, False{}}, 0)) == True{} : Bool}:
  kk.KE.mk(K3G{Laws.k3.dk.init(ds), D3.k3.seg.name(last)}, T.tree.walk(Laws.k3.dk.names(ds, last), T.Tw{rows,
    D1.header_job(arr), [], "", "", heads, False{}}, 0), eb => kk.has2(kw.evs(T.tree.walk(Laws.k3.dk.names(ds,
      last), T.Tw{rows, D1.header_job(arr), [], "", "", heads, False{}}, 0)), Laws.k3.dk.init(ds),
    D3.k3.seg.name(last), kc.initn(Laws.k3.dk.names(ds, last)), kc.lastn(Laws.k3.dk.names(ds, last)),
    Equal.sym(List<&2, String>, kc.initn(Laws.k3.dk.names(ds, last)), Laws.k3.dk.init(ds), Equal.trans(List<&2,
      String>, kc.initn(Laws.k3.dk.names(ds, last)), kc.initn(List.append(&2, String, Laws.k3.dk.init(ds),
        [D3.k3.seg.name(last)])), Laws.k3.dk.init(ds), Equal.cong(List<&2, String>, List<&2, String>, zs =>
          kc.initn(zs), Laws.k3.dk.names(ds, last), List.append(&2, String, Laws.k3.dk.init(ds),
            [D3.k3.seg.name(last)]), kk.dksplit(ds, last)), kk.initn(Laws.k3.dk.init(ds), D3.k3.seg.name(last)))),
    Equal.sym(String, kc.lastn(Laws.k3.dk.names(ds, last)), D3.k3.seg.name(last), Equal.trans(String,
      kc.lastn(Laws.k3.dk.names(ds, last)), kc.lastn(List.append(&2, String, Laws.k3.dk.init(ds),
        [D3.k3.seg.name(last)])), D3.k3.seg.name(last), Equal.cong(List<&2, String>, String, zs => kc.lastn(zs),
          Laws.k3.dk.names(ds, last), List.append(&2, String, Laws.k3.dk.init(ds), [D3.k3.seg.name(last)]),
            kk.dksplit(ds, last)), kk.lastn(Laws.k3.dk.init(ds), D3.k3.seg.name(last)))),
    kc.wtab(Laws.k3.dk.names(ds, last), T.Tw{rows, D1.header_job(arr), [], "", "", heads, False{}}, 0, [],
      kk.ci0(rows, D1.header_job(arr), "", "", heads, False{}, {==}), eb)))

def Laws.header_found_anywhere(arr, g0, ds, last, ok, g9, rows, heads, here, arrtab, back, qkind, uni, left, rest, eo):
  k3p.hcore(arr, g0, ds, last, g9, rows, heads, here, arrtab, back, qkind, uni, left, rest, K3G{Laws.k3.dk.init(ds),
    D3.k3.seg.name(last)}, ok, +b2 => +q2 => +u2 => +l2 => kk.read(K3G{Laws.k3.dk.init(ds), D3.k3.seg.name(last)},
      rest, T.read.once2(T.head.apply(T.tree.walk(Laws.k3.dk.names(ds, last), T.Tw{rows, D1.header_job(arr), [], "",
        "", heads, False{}}, 0), Laws.k3.dk.names(ds, last), b2, q2, u2, l2, False{})),
      kk.once2(K3G{Laws.k3.dk.init(ds), D3.k3.seg.name(last)}, T.head.apply(T.tree.walk(Laws.k3.dk.names(ds, last),
        T.Tw{rows, D1.header_job(arr), [], "", "", heads, False{}}, 0), Laws.k3.dk.names(ds, last), b2, q2,
        u2, l2, False{}), kk.happly(K3G{Laws.k3.dk.init(ds), D3.k3.seg.name(last)}, T.tree.walk(Laws.k3.dk.names(ds,
          last), T.Tw{rows, D1.header_job(arr), [], "", "", heads, False{}}, 0), Laws.k3.dk.names(ds,
          last), b2, q2, u2, l2, False{}, kk.hwalk(arr, ds, last, rows, heads)))))(eo)

# a hit that leads on through tables is a table or an inline table
def kk.tabh.is(
  pp: List<&2, String>,
  +hh: T.Hit,
  +ee: {Laws.k3.tabh(pp, hh) == True{} : Bool}
) -> {Laws.k3.istab(hh) == True{} : Bool}:
  match pp:
    case []:
      ee
    case +nn <> rest:
      M17.gd.l(Laws.k3.istab(hh), Laws.k3.tabh(rest, T.get(T.at.rows_of(hh), nn)), ee)

# the first pair of a name, when every pair of it holds a path and it is a
# table or an inline table, holds the path in its rows
def kk.hpmk(
  hh: T.Hit,
  +rows: List<&2, T.Val>,
  +nn: String,
  +pp: List<&2, String>,
  +kk: String,
  +eq: {T.rows.find(rows, nn) == hh : T.Hit},
  +ea: {kh.A(rows, nn, pp, kk) == True{} : Bool},
  +et: {Laws.k3.tabh(pp, hh) == True{} : Bool}
) -> {Laws.k3.has(T.at.rows_of(hh), pp, kk) == True{} : Bool}:
  match hh:
    case T.Found{T.VHead{+q, +r}}:
      kh.first(rows, nn, T.VHead{q, r}, pp, kk, eq, ea)
    case T.Found{T.VInl{+r}}:
      kh.first(rows, nn, T.VInl{r}, pp, kk, eq, ea)
    case T.Miss{}:
      Eq.bit.absurd(&2, {Laws.k3.has(T.at.rows_of(T.Miss{}), pp, kk) == True{} : Bool}, kk.tabh.is(pp, T.Miss{}, et))
    case T.Found{T.VStr{_a}}:
      Eq.bit.absurd(&2, {Laws.k3.has(T.at.rows_of(T.Found{T.VStr{_a}}), pp, kk) == True{} : Bool}, kk.tabh.is(pp,
        T.Found{T.VStr{_a}}, et))
    case T.Found{T.VSpan{_a, _b}}:
      Eq.bit.absurd(&2, {Laws.k3.has(T.at.rows_of(T.Found{T.VSpan{_a, _b}}), pp, kk) == True{} : Bool}, kk.tabh.is(pp,
        T.Found{T.VSpan{_a, _b}}, et))
    case T.Found{T.VInt{_a, _b}}:
      Eq.bit.absurd(&2, {Laws.k3.has(T.at.rows_of(T.Found{T.VInt{_a, _b}}), pp, kk) == True{} : Bool}, kk.tabh.is(pp,
        T.Found{T.VInt{_a, _b}}, et))
    case T.Found{T.VFlo{_a, _b}}:
      Eq.bit.absurd(&2, {Laws.k3.has(T.at.rows_of(T.Found{T.VFlo{_a, _b}}), pp, kk) == True{} : Bool}, kk.tabh.is(pp,
        T.Found{T.VFlo{_a, _b}}, et))
    case T.Found{T.VBool{_a}}:
      Eq.bit.absurd(&2, {Laws.k3.has(T.at.rows_of(T.Found{T.VBool{_a}}), pp, kk) == True{} : Bool}, kk.tabh.is(pp,
        T.Found{T.VBool{_a}}, et))
    case T.Found{T.VWhen{_a}}:
      Eq.bit.absurd(&2, {Laws.k3.has(T.at.rows_of(T.Found{T.VWhen{_a}}), pp, kk) == True{} : Bool}, kk.tabh.is(pp,
        T.Found{T.VWhen{_a}}, et))
    case T.Found{T.VArr{_a}}:
      Eq.bit.absurd(&2, {Laws.k3.has(T.at.rows_of(T.Found{T.VArr{_a}}), pp, kk) == True{} : Bool}, kk.tabh.is(pp,
        T.Found{T.VArr{_a}}, et))
    case T.Found{T.VAot{_a, _b}}:
      Eq.bit.absurd(&2, {Laws.k3.has(T.at.rows_of(T.Found{T.VAot{_a, _b}}), pp, kk) == True{} : Bool}, kk.tabh.is(pp,
        T.Found{T.VAot{_a, _b}}, et))
    case T.Found{T.VAots{_a, _b}}:
      Eq.bit.absurd(&2, {Laws.k3.has(T.at.rows_of(T.Found{T.VAots{_a, _b}}), pp, kk) == True{} : Bool}, kk.tabh.is(pp,
        T.Found{T.VAots{_a, _b}}, et))
    case T.Found{T.VPair{_a, _b}}:
      Eq.bit.absurd(&2, {Laws.k3.has(T.at.rows_of(T.Found{T.VPair{_a, _b}}), pp, kk) == True{} : Bool}, kk.tabh.is(pp,
        T.Found{T.VPair{_a, _b}}, et))

# at follows a path through tables from a hit whose rows hold it, to the key
def kk.ats(
  path: List<&2, String>,
  +hh: T.Hit,
  +kk: String,
  +eh: {Laws.k3.has(T.at.rows_of(hh), path, kk) == True{} : Bool},
  +et: {Laws.k3.tabh(path, hh) == True{} : Bool}
) -> {Laws.k3.found(T.at.step(List.append(&2, String, path, [kk]), hh)) == True{} : Bool}:
  match path:
    case []:
      eh
    case +mm <> +pp:
      kk.ats(pp, T.get(T.at.rows_of(hh), mm), kk, kk.hpmk(T.get(T.at.rows_of(hh), mm), T.at.rows_of(hh), mm, pp, kk,
        {==}, M17.gd.r(kh.F(T.at.rows_of(hh), mm), kh.A(T.at.rows_of(hh), mm, pp, kk), eh), M17.gd.r(Laws.k3.istab(hh),
          Laws.k3.tabh(pp, T.get(T.at.rows_of(hh), mm)), et)), M17.gd.r(Laws.k3.istab(hh), Laws.k3.tabh(pp,
            T.get(T.at.rows_of(hh), mm)), et))

# LEMMA: rows that hold a key in a table reached through tables only: at
# finds the key by the table's path and its name
def kk.atroot(
  +rows: List<&2, T.Val>,
  path: List<&2, String>,
  +kk: String,
  +eh: {Laws.k3.has(rows, path, kk) == True{} : Bool},
  +et: {Laws.k3.tabs(rows, path) == True{} : Bool}
) -> {Laws.k3.found(T.at(rows, List.append(&2, String, path, [kk]))) == True{} : Bool}:
  match path:
    case []:
      eh
    case +nn <> +pp:
      kk.ats(pp, T.get(rows, nn), kk, kk.hpmk(T.get(rows, nn), rows, nn, pp, kk, {==}, M17.gd.r(kh.F(rows, nn),
          kh.A(rows,
        nn, pp, kk), eh), et), et)

def Laws.key_found_by_at(
  at,
  g0,
  ds,
  last,
  ok,
  g,
  rows,
  heads,
  here,
  stack,
  arrtab,
  back,
  qkind,
  uni,
  left,
  rest,
  es,
  eo,
  et
):
  kk.atroot(T.root(Laws.k3.key.doc(at, g0, ds, last, g, rows, heads, here, stack, arrtab, back, qkind, uni, left,
    rest)), Laws.k3.key.table(stack, here, ds), D3.k3.seg.name(last), Laws.key_found_anywhere(at, g0, ds, last, ok,
      g, rows, heads, here,
    stack, arrtab, back, qkind, uni, left, rest, es, eo), et)

def Laws.header_found_by_at(
  arr,
  g0,
  ds,
  last,
  ok,
  g9,
  rows,
  heads,
  here,
  arrtab,
  back,
  qkind,
  uni,
  left,
  rest,
  eo,
  et
):
  kk.atroot(T.root(Laws.k3.hd.doc(arr, g0, ds, last, g9, rows, heads, here, arrtab, back, qkind, uni, left, rest)),
    Laws.k3.dk.init(ds), D3.k3.seg.name(last), Laws.header_found_anywhere(arr, g0, ds, last, ok,
    g9, rows, heads, here, arrtab, back, qkind, uni, left, rest, eo), et)

def Laws.key_found_in_document(
  pre,
  at,
  g0,
  ds,
  last,
  ok,
  g,
  rows,
  heads,
  here,
  stack,
  arrtab,
  back,
  qkind,
  uni,
  left,
  rest,
  es,
  ep,
  eo
):
  %Equal.sym(T.Doc, T.parse(String.append(pre, String.append(D2.gap(g0), Laws.k3.dk.text(ds, last,
    String.append(D2.gap(g), SCon{'=', rest}))))), Laws.k3.key.doc(at, g0, ds, last, g, rows, heads, here, stack,
      arrtab, back, qkind, uni, left, rest), ep) : {Laws.k3.has(T.root(_), Laws.k3.key.table(stack, here, ds),
        D3.k3.seg.name(last)) == True{} : Bool}
  Laws.key_found_anywhere(at, g0, ds, last, ok, g, rows, heads, here, stack, arrtab, back, qkind, uni, left, rest, es,
    Equal.trans(Bool, String.is_empty(T.bad(Laws.k3.key.doc(at, g0, ds, last, g, rows, heads, here, stack, arrtab,
      back, qkind, uni, left, rest))), String.is_empty(T.bad(T.parse(String.append(pre, String.append(D2.gap(g0),
        Laws.k3.dk.text(ds, last, String.append(D2.gap(g), SCon{'=', rest}))))))), True{}, Equal.cong(T.Doc, Bool,
      dd => String.is_empty(T.bad(dd)), Laws.k3.key.doc(at, g0, ds, last, g, rows, heads, here, stack, arrtab, back,
        qkind, uni, left, rest), T.parse(String.append(pre, String.append(D2.gap(g0), Laws.k3.dk.text(ds, last,
          String.append(D2.gap(g), SCon{'=', rest}))))), Equal.sym(T.Doc, T.parse(String.append(pre,
            String.append(D2.gap(g0), Laws.k3.dk.text(ds, last, String.append(D2.gap(g), SCon{'=', rest}))))),
              Laws.k3.key.doc(at, g0, ds, last, g, rows, heads, here, stack, arrtab, back, qkind, uni, left, rest),
                ep)), eo))
