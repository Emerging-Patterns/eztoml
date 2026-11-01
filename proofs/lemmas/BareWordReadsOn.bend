# a bare word is read on character by character until its delimiter
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/BareWordReadsOn.bend as L1
import ../../laws/defs/BareValueGrammar.bend as D1
import ../../laws/defs/ScalarReadbackScan.bend as D2
import ./BareValueScan.bend as M1
import ./FreshNamesInRows.bend as M2
import ./HeldCharacterSteps.bend as M3
import ./ReorderedTableNames.bend as M4

# WP-V: bare values stated over parse. From every value state, the scan
# pushes a bare word's characters (wd.first, wd.step), a space after a date
# through LDate with the digit after it (vl.sp, vl.dig), and at the text
# that ends the word classifies it and places the value (vl.fin), or fails.
# The value's state is named once (vl.vt) and each ending is one step of it.

# what holds of a character holds of one equal to it
def vl.chs(-P: Char -> Type, aa: Char, bb: Char, ee: {aa == bb : Char}, kk: P(bb)) -> P(aa):
  %Equal.sym(Char, aa, bb, ee) : P(_)
  kk

# the text's buffer is the proofs' rev.onto
def vl.rev(ss: String, acc: List<&2, Char>) -> {D1.bw.rev(ss, acc) == M2.rev.onto(ss, acc) : List<&2, Char>}:
  match ss:
    case SNil{}:
      {==}
    case SCon{hh, tt}:
      vl.rev(tt, hh <> acc)

# the scanner with a bare value placed, as a bare word leaves it
def vl.vt(+fx: D2.Vf, +vv: T.Val) -> T.St:
  T.val.take(D2.vst(fx, [], T.LBare{}), vv)

# a space after a date is kept: the scan waits in LDate
def vl.sp(
  +fx: D2.Vf,
  +buf: List<&2, Char>,
  hd: {T.date.shaped(buf) == True{} : Bool}
) -> {T.doc.scan(D2.vst(fx, buf, T.LBare{}), ' ') == T.MScan{D2.vst(fx, buf, T.LDate{})} : T.Mode}:
  match fx:
    case D2.Vf{bad, rows, heads, here, parts, back, qkind, stack, uni, left, arrtab}:
      Equal.cong(Bool, T.Mode, bb => T.MScan{T.read.once2(T.lex.bare.date.go(bb, T.St{bad, rows, heads, here, parts,
        buf, T.LBare{}, back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}}, ' '))}, T.date.shaped(buf), True{},
        hd)

# a digit after the space joins the word with the space before it
def vl.dig.f(
  +fx: D2.Vf,
  +buf: List<&2, Char>,
  +cc: Char,
  hd: {Char.is_digit(cc) == True{} : Bool}
) -> {T.MScan{T.read.fast(D2.vst(fx, buf, T.LDate{}), cc)} == T.MScan{D2.vst(fx, cc <> (' ' <> buf), T.LBare{})}
  : T.Mode}:
  match fx:
    case D2.Vf{bad, rows, heads, here, parts, back, qkind, stack, uni, left, arrtab}:
      Equal.cong(Bool, T.Mode, bb => T.MScan{T.read.once2(T.lex.date.go(bb, T.St{bad, rows, heads, here, parts, buf,
        T.LDate{}, back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}}, cc))}, Char.is_digit(cc), True{}, hd)

# and so in the scan mode, a digit being no quote and no carriage return
def vl.dig(
  +fx: D2.Vf,
  +buf: List<&2, Char>,
  +xx: U32,
  +hd: {Char.is_digit(Chr{xx}) == True{} : Bool}
) -> {T.doc.scan(D2.vst(fx, buf, T.LDate{}), Chr{xx}) == T.MScan{D2.vst(fx, Chr{xx} <> (' ' <> buf), T.LBare{})}
  : T.Mode}:
  Equal.trans(T.Mode, T.doc.scan(D2.vst(fx, buf, T.LDate{}), Chr{xx}),
    T.MScan{T.read.fast(D2.vst(fx, buf, T.LDate{}), Chr{xx})},
    T.MScan{D2.vst(fx, Chr{xx} <> (' ' <> buf), T.LBare{})},
    M4.scan.other(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), U32.is_eq(xx, 13), D2.vst(fx, buf, T.LDate{}),
      Chr{xx}, {==}, {==}, {==}, ch => Char.is_digit(ch), hd, {==}, {==}, {==}),
    vl.dig.f(fx, buf, Chr{xx}, hd))

# a digit is a character a bare value keeps
def vl.dch(cc: Char, hd: {Char.is_digit(cc) == True{} : Bool}) -> {D1.word.char(cc) == True{} : Bool}:
  M2.dg.elim(ch => {D1.word.char(ch) == True{} : Bool}, cc, hd, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==},
    {==})

# a date's space then a digit leave the scan where a space pushed as a
# character would, then the digit
def vl.spd(
  +fx: D2.Vf,
  +buf: List<&2, Char>,
  +xx: U32,
  +rr: String,
  hs: {T.date.shaped(buf) == True{} : Bool},
  +hd: {Char.is_digit(Chr{xx}) == True{} : Bool}
) -> {T.doc.read(SCon{' ', SCon{Chr{xx}, rr}}, T.MScan{D2.vst(fx, buf, T.LBare{})})
  == T.doc.read(SCon{Chr{xx}, rr}, T.MScan{D2.vst(fx, ' ' <> buf, T.LBare{})}) : T.Doc}:
  Equal.trans(T.Doc, T.doc.read(SCon{Chr{xx}, rr}, T.doc.scan(D2.vst(fx, buf, T.LBare{}), ' ')),
    T.doc.read(rr, T.MScan{D2.vst(fx, Chr{xx} <> (' ' <> buf), T.LBare{})}),
    T.doc.read(SCon{Chr{xx}, rr}, T.MScan{D2.vst(fx, ' ' <> buf, T.LBare{})}),
    Equal.trans(T.Doc, T.doc.read(SCon{Chr{xx}, rr}, T.doc.scan(D2.vst(fx, buf, T.LBare{}), ' ')),
      T.doc.read(rr, T.doc.scan(D2.vst(fx, buf, T.LDate{}), Chr{xx})),
      T.doc.read(rr, T.MScan{D2.vst(fx, Chr{xx} <> (' ' <> buf), T.LBare{})}),
      Equal.cong(T.Mode, T.Doc, md => T.doc.read(SCon{Chr{xx}, rr}, md), T.doc.scan(D2.vst(fx, buf, T.LBare{}), ' '),
        T.MScan{D2.vst(fx, buf, T.LDate{})}, vl.sp(fx, buf, hs)),
      Equal.cong(T.Mode, T.Doc, md => T.doc.read(rr, md), T.doc.scan(D2.vst(fx, buf, T.LDate{}), Chr{xx}),
        T.MScan{D2.vst(fx, Chr{xx} <> (' ' <> buf), T.LBare{})}, vl.dig(fx, buf, xx, hd))),
    Equal.sym(T.Doc, T.doc.read(rr, T.doc.scan(D2.vst(fx, ' ' <> buf, T.LBare{}), Chr{xx})),
      T.doc.read(rr, T.MScan{D2.vst(fx, Chr{xx} <> (' ' <> buf), T.LBare{})}),
      Equal.cong(T.Mode, T.Doc, md => T.doc.read(rr, md), T.doc.scan(D2.vst(fx, ' ' <> buf, T.LBare{}), Chr{xx}),
        T.MScan{D2.vst(fx, Chr{xx} <> (' ' <> buf), T.LBare{})},
        M1.wd.step(fx, ' ' <> buf, xx, vl.dch(Chr{xx}, hd)))))

# the claim of one step of the word: the character cc and the rest tt read
# from the buffer as the rest's characters pushed after cc's
def vl.Run(+fx: D2.Vf, +buf: List<&2, Char>, +cc: Char, +tt: String, +rr: String) -> Type:
  {T.doc.read(SCon{cc, String.append(tt, rr)}, T.MScan{D2.vst(fx, buf, T.LBare{})})
    == T.doc.read(rr, T.MScan{D2.vst(fx, M2.rev.onto(tt, cc <> buf), T.LBare{})}) : T.Doc}

# the rest read from the buffer with cc pushed, as the step's claim needs it
def vl.Ih(+fx: D2.Vf, +buf: List<&2, Char>, +cc: Char, +tt: String, +rr: String) -> Type:
  {T.doc.read(String.append(tt, rr), T.MScan{D2.vst(fx, cc <> buf, T.LBare{})})
    == T.doc.read(rr, T.MScan{D2.vst(fx, M2.rev.onto(tt, cc <> buf), T.LBare{})}) : T.Doc}

# a space the word keeps: a digit follows, and the space step is a push
def vl.run.sp(
  +fx: D2.Vf,
  +buf: List<&2, Char>,
  tt: String,
  +rr: String,
  hs: {T.date.shaped(buf) == True{} : Bool},
  hd: {D1.bw.digit1(tt) == True{} : Bool},
  ih: vl.Ih(fx, buf, ' ', tt, rr)
) -> vl.Run(fx, buf, ' ', tt, rr):
  match tt:
    case SNil{}:
      Eq.bit.absurd(&1, vl.Run(fx, buf, ' ', SNil{}, rr), hd)
    case SCon{dd, +t2}:
      match dd:
        case Chr{+yy}:
          Equal.trans(T.Doc, T.doc.read(SCon{' ', SCon{Chr{yy}, String.append(t2, rr)}}, T.MScan{D2.vst(fx, buf,
            T.LBare{})}), T.doc.read(SCon{Chr{yy}, String.append(t2, rr)}, T.MScan{D2.vst(fx, ' ' <> buf,
            T.LBare{})}), T.doc.read(rr, T.MScan{D2.vst(fx, M2.rev.onto(SCon{Chr{yy}, t2}, ' ' <> buf), T.LBare{})}),
            vl.spd(fx, buf, yy, String.append(t2, rr), hs, hd), ih)

# one character of the word: pushed when a bare value keeps it, and a
# datetime's space otherwise
def vl.run.at(
  wc: Bool,
  +xx: U32,
  +tt: String,
  +rr: String,
  +fx: D2.Vf,
  +buf: List<&2, Char>,
  ewc: {D1.word.char(Chr{xx}) == wc : Bool},
  +ho: {Bool.or(wc, D1.bw.dsp(Chr{xx}, buf, tt)) == True{} : Bool},
  ih: vl.Ih(fx, buf, Chr{xx}, tt, rr)
) -> vl.Run(fx, buf, Chr{xx}, tt, rr):
  match wc:
    case True{}:
      Equal.trans(T.Doc, T.doc.read(String.append(tt, rr), T.doc.scan(D2.vst(fx, buf, T.LBare{}), Chr{xx})),
        T.doc.read(String.append(tt, rr), T.MScan{D2.vst(fx, Chr{xx} <> buf, T.LBare{})}),
        T.doc.read(rr, T.MScan{D2.vst(fx, M2.rev.onto(tt, Chr{xx} <> buf), T.LBare{})}),
        Equal.cong(T.Mode, T.Doc, md => T.doc.read(String.append(tt, rr), md),
          T.doc.scan(D2.vst(fx, buf, T.LBare{}), Chr{xx}), T.MScan{D2.vst(fx, Chr{xx} <> buf, T.LBare{})},
          M1.wd.step(fx, buf, xx, ewc)), ih)
    case False{}:
      +eq = {Eq.char_eq_true(Chr{xx}, ' ', Eq.and.left(Char.is_eq(Chr{xx}, ' '), Bool.and(T.date.shaped(buf),
        D1.bw.digit1(tt)), ho)) : {Chr{xx} == ' ' : Char}}
      +h2 = {Eq.and.right(Char.is_eq(Chr{xx}, ' '), Bool.and(T.date.shaped(buf), D1.bw.digit1(tt)), ho)
        : {Bool.and(T.date.shaped(buf), D1.bw.digit1(tt)) == True{} : Bool}}
      vl.chs(ch => vl.Run(fx, buf, ch, tt, rr), Chr{xx}, ' ', eq,
        vl.run.sp(fx, buf, tt, rr, Eq.and.left(T.date.shaped(buf), D1.bw.digit1(tt), h2),
          Eq.and.right(T.date.shaped(buf), D1.bw.digit1(tt), h2),
          vl.chs(ch => vl.Ih(fx, buf, ch, tt, rr), ' ', Chr{xx}, Equal.sym(Char, Chr{xx}, ' ', eq), ih)))

# the characters the word keeps after its first are pushed one by one,
# whatever follows
def vl.run(
  ss: String,
  +rr: String,
  +fx: D2.Vf,
  +buf: List<&2, Char>,
  +ee: {D1.bw.more(ss, buf) == True{} : Bool}
) -> {T.doc.read(String.append(ss, rr), T.MScan{D2.vst(fx, buf, T.LBare{})}) == T.doc.read(rr, T.MScan{D2.vst(fx,
  M2.rev.onto(ss, buf), T.LBare{})}) : T.Doc}:
  match ss:
    case SNil{}:
      {==}
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          +hm = {Eq.and.right(Bool.or(D1.word.char(Chr{xx}), D1.bw.dsp(Chr{xx}, buf, tt)),
            D1.bw.more(tt, Chr{xx} <> buf), ee) : {D1.bw.more(tt, Chr{xx} <> buf) == True{} : Bool}}
          vl.run.at(D1.word.char(Chr{xx}), xx, tt, rr, fx, buf, {==},
            Eq.and.left(Bool.or(D1.word.char(Chr{xx}), D1.bw.dsp(Chr{xx}, buf, tt)),
              D1.bw.more(tt, Chr{xx} <> buf), ee), vl.run(tt, rr, fx, Chr{xx} <> buf, hm))

# The state with a bare value placed is one of three shapes, by where the
# value went: after a root pair's value (LLine), an array's item (LArrC) or an
# inline table's value (LInlC), with nothing held and nothing buffered.

# a claim of every state of one shape
def vl.Sh(-P: T.St -> Type, +lx: T.Lex) -> Type:
  @bd: String -> @rw: List<&2, T.Val> -> @hs: List<&2, String> -> @he: List<&2, String> -> @ps: List<&2, String> ->
    @bk: T.Lex -> @qk: T.QKind -> @sk: List<&2, T.Ctx> -> @un: U32 -> @lf: U32 -> @ab: Bool ->
    P(T.St{bd, rw, hs, he, ps, [], lx, bk, qk, sk, T.HNone{}, un, lf, ab, False{}})

# a root pair's value
def vl.vt.root(
  -P: T.St -> Type,
  end: T.End,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  pl: vl.Sh(P, T.LLine{})
) -> P(T.take.root(end, he, bk, qk, un, lf, ab, False{})):
  match end:
    case T.End{+vs, +bad, +heads}:
      pl(bad, vs, heads, he, [], bk, qk, [], un, lf, ab)

# an inline table's value
def vl.vt.inl(
  -P: T.St -> Type,
  end: T.End,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +rest: List<&2, T.Ctx>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  pi: vl.Sh(P, T.LInlC{})
) -> P(T.take.inl(end, rw, hs, he, ps, rest, bk, qk, un, lf, ab, False{})):
  match end:
    case T.End{+inl, +bad, _heads}:
      pi(bad, rw, hs, he, [], bk, qk, T.CInl{inl, ps, he} <> rest, un, lf, ab)

# a claim of each shape is a claim of the state with a bare value placed
def vl.vt.elim(
  -P: T.St -> Type,
  +fx: D2.Vf,
  +vv: T.Val,
  pl: vl.Sh(P, T.LLine{}),
  pa: vl.Sh(P, T.LArrC{}),
  pi: vl.Sh(P, T.LInlC{})
) -> P(vl.vt(fx, vv)):
  match fx:
    case D2.Vf{+bad, +rows, +heads, +here, +parts, +back, +qkind, stack, +uni, +left, +arrtab}:
      match stack:
        case []:
          vl.vt.root(P, T.tree.walk(T.path.cat(here, parts), T.Tw{rows, T.JPut{vv}, [], bad, "", heads, False{}},
            T.path.len(here, 0)), here, back, qkind, uni, left, arrtab, pl)
        case T.CArr{items, +saved, +at} <> +rest:
          pa(bad, rows, heads, at, saved, back, qkind, T.CArr{vv <> items, saved, at} <> rest, uni, left, arrtab)
        case T.CInl{inl, +saved, +at} <> +rest:
          vl.vt.inl(P, T.tree.walk(List.reverse(&2, String, parts), T.Tw{inl, T.JPut{vv}, [], bad, "", [], True{}}, 0),
            rows, heads, at, saved, rest, back, qkind, uni, left, arrtab, pi)

# the end of the text after a placed value finishes the document from it
def vl.close(
  +fx: D2.Vf,
  +vv: T.Val
) -> {T.read.fin(T.read.once2(vl.vt(fx, vv))) == T.read.fin2(vl.vt(fx, vv)) : T.Doc}:
  vl.vt.elim(st => {T.read.fin(T.read.once2(st)) == T.read.fin2(st) : T.Doc}, fx, vv,
    _bd => _rw => _hs => _he => _ps => _bk => _qk => _sk => _un => _lf => _ab => {==},
    _bd => _rw => _hs => _he => _ps => _bk => _qk => _sk => _un => _lf => _ab => {==},
    _bd => _rw => _hs => _he => _ps => _bk => _qk => _sk => _un => _lf => _ab => {==})

# nothing is held after a placed value
def vl.o2(+fx: D2.Vf, +vv: T.Val) -> {T.read.once2(vl.vt(fx, vv)) == vl.vt(fx, vv) : T.St}:
  vl.vt.elim(st => {T.read.once2(st) == st : T.St}, fx, vv,
    _bd => _rw => _hs => _he => _ps => _bk => _qk => _sk => _un => _lf => _ab => {==},
    _bd => _rw => _hs => _he => _ps => _bk => _qk => _sk => _un => _lf => _ab => {==},
    _bd => _rw => _hs => _he => _ps => _bk => _qk => _sk => _un => _lf => _ab => {==})

# a space or a tab in a state that skips it leaves the state as it is
def vl.ws(
  sp: Bool,
  nl: Bool,
  keep: Bool,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +buf: List<&2, Char>,
  +lx: T.Lex,
  +bk: T.Lex,
  +qk: T.QKind,
  +sk: List<&2, T.Ctx>,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +cc: Char,
  es: {sp == True{} : Bool}
) -> {T.read.fast.ws(sp, nl, keep, bd, rw, hs, he, ps, buf, lx, bk, qk, sk, un, lf, ab, cc) == M3.fs.st(bd, rw, hs, he,
    ps,
  buf, lx, bk, qk, sk, un, lf, ab) : T.St}:
  match sp:
    case True{}:
      {==}
    case False{}:
      Eq.bit.absurd(&2, {T.read.fast.ws(False{}, nl, keep, bd, rw, hs, he, ps, buf, lx, bk, qk, sk, un, lf, ab, cc)
        == M3.fs.st(bd, rw, hs, he, ps, buf, lx, bk, qk, sk, un, lf, ab) : T.St}, es)

# a space or a tab after a placed value is skipped
def vl.self(
  +fx: D2.Vf,
  +vv: T.Val,
  +cc: Char,
  +es: {T.ch.sp(cc) == True{} : Bool}
) -> {T.read.fast(vl.vt(fx, vv), cc) == vl.vt(fx, vv) : T.St}:
  vl.vt.elim(st => {T.read.fast(st, cc) == st : T.St}, fx, vv,
    bd => rw => hs => he => ps => bk => qk => sk => un => lf => ab => vl.ws(T.ch.sp(cc), T.ch.nl(cc), False{}, bd, rw,
      hs, he, ps, [], T.LLine{}, bk, qk, sk, un, lf, ab, cc, es),
    bd => rw => hs => he => ps => bk => qk => sk => un => lf => ab => vl.ws(T.ch.sp(cc), T.ch.nl(cc), True{}, bd, rw,
      hs, he, ps, [], T.LArrC{}, bk, qk, sk, un, lf, ab, cc, es),
    bd => rw => hs => he => ps => bk => qk => sk => un => lf => ab => vl.ws(T.ch.sp(cc), T.ch.nl(cc), False{}, bd, rw,
      hs, he, ps, [], T.LInlC{}, bk, qk, sk, un, lf, ab, cc, es))

# a space or a tab that ended a word is read as the fast step reads it after
# the value
def vl.eh.sp(
  +fx: D2.Vf,
  +vv: T.Val,
  +cc: Char,
  +es: {T.ch.sp(cc) == True{} : Bool}
) -> {T.read.once2(vl.vt(fx, vv)) == T.read.fast(vl.vt(fx, vv), cc) : T.St}:
  Equal.trans(T.St, T.read.once2(vl.vt(fx, vv)), vl.vt(fx, vv), T.read.fast(vl.vt(fx, vv), cc), vl.o2(fx, vv),
    Equal.sym(T.St, T.read.fast(vl.vt(fx, vv), cc), vl.vt(fx, vv), vl.self(fx, vv, cc, es)))

# a carriage return after a root value is consumed with it, as the fast step
# would
def vl.cr.root(
  end: T.End,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool
) -> {T.read.once2(T.bare.line.go(T.take.root(end, he, bk, qk, un, lf, ab, False{})))
  == T.read.fast(T.take.root(end, he, bk, qk, un, lf, ab, False{}), Chr{13}) : T.St}:
  match end:
    case T.End{_vs, _bad, _heads}:
      {==}

# a carriage return after a bare value, wherever the value went
def vl.eh.cr(+fx: D2.Vf, +vv: T.Val) -> M3.cw.Eh(fx, vv, Chr{13}, D2.vf.inl(fx)):
  match fx:
    case D2.Vf{+bad, +rows, +heads, +here, +parts, +back, +qkind, stack, +uni, +left, +arrtab}:
      match stack:
        case []:
          vl.cr.root(T.tree.walk(T.path.cat(here, parts), T.Tw{rows, T.JPut{vv}, [], bad, "", heads, False{}},
            T.path.len(here, 0)), here, back, qkind, uni, left, arrtab)
        case T.CArr{_items, _saved, _at} <> _rest:
          {==}
        case T.CInl{+inl, +saved, +at} <> +rest:
          M3.fs.held(T.CInl{inl, saved, at} <> rest, vv, Chr{13}, bad, rows, heads, here, parts, back, qkind, uni, left,
            arrtab)

# the character cc, which ends a bare word, finishes the word: word.val
# classifies the buffer and hold says whether cc is read again
def vl.Rf(+fx: D2.Vf, +bb: List<&2, Char>, +cc: Char, +hold: Bool) -> Type:
  {T.read.fast(D2.vst(fx, bb, T.LBare{}), cc) == T.read.once2(T.bare.got(T.word.val(List.reverse(&2, Char, bb)),
    D2.vst(fx, [], T.LBare{}), cc, hold)) : T.St}

# a tab
def vl.rf.tab(+fx: D2.Vf, +bb: List<&2, Char>) -> vl.Rf(fx, bb, Chr{9}, False{}):
  match fx:
    case D2.Vf{_bad, _rows, _heads, _here, _parts, _back, _qkind, _stack, _uni, _left, _arrtab}:
      {==}

# a line feed
def vl.rf.lf(+fx: D2.Vf, +bb: List<&2, Char>) -> vl.Rf(fx, bb, '\n', D2.vf.inl(fx)):
  match fx:
    case D2.Vf{_bad, _rows, _heads, _here, _parts, _back, _qkind, _stack, _uni, _left, _arrtab}:
      {==}

# a carriage return
def vl.rf.cr(+fx: D2.Vf, +bb: List<&2, Char>) -> vl.Rf(fx, bb, Chr{13}, D2.vf.inl(fx)):
  match fx:
    case D2.Vf{_bad, _rows, _heads, _here, _parts, _back, _qkind, _stack, _uni, _left, _arrtab}:
      {==}

# #, held
def vl.rf.hash(+fx: D2.Vf, +bb: List<&2, Char>) -> vl.Rf(fx, bb, '#', True{}):
  match fx:
    case D2.Vf{_bad, _rows, _heads, _here, _parts, _back, _qkind, _stack, _uni, _left, _arrtab}:
      {==}

# a comma, held
def vl.rf.comma(+fx: D2.Vf, +bb: List<&2, Char>) -> vl.Rf(fx, bb, ',', True{}):
  match fx:
    case D2.Vf{_bad, _rows, _heads, _here, _parts, _back, _qkind, _stack, _uni, _left, _arrtab}:
      {==}

# a bracket, held
def vl.rf.rb(+fx: D2.Vf, +bb: List<&2, Char>) -> vl.Rf(fx, bb, ']', True{}):
  match fx:
    case D2.Vf{_bad, _rows, _heads, _here, _parts, _back, _qkind, _stack, _uni, _left, _arrtab}:
      {==}

# a brace, held
def vl.rf.rc(+fx: D2.Vf, +bb: List<&2, Char>) -> vl.Rf(fx, bb, '}', True{}):
  match fx:
    case D2.Vf{_bad, _rows, _heads, _here, _parts, _back, _qkind, _stack, _uni, _left, _arrtab}:
      {==}

# a space the word does not keep: the buffer is no date
def vl.rf.sp(
  +fx: D2.Vf,
  +bb: List<&2, Char>,
  hs: {T.date.shaped(bb) == False{} : Bool}
) -> vl.Rf(fx, bb, ' ', False{}):
  match fx:
    case D2.Vf{bad, rows, heads, here, parts, back, qkind, stack, uni, left, arrtab}:
      Equal.cong(Bool, T.St, xx => T.read.once2(T.lex.bare.date.go(xx, T.St{bad, rows, heads, here, parts, bb,
        T.LBare{}, back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}}, ' ')), T.date.shaped(bb), False{}, hs)

# a character that ends a word, then the step after the value: the step from
# the buffer is the step from the state with the value placed
def vl.acc(
  +fx: D2.Vf,
  +bb: List<&2, Char>,
  +vv: T.Val,
  +cc: Char,
  +hold: Bool,
  hv: {T.word.val(List.reverse(&2, Char, bb)) == T.GotVal{vv} : T.Got},
  rf: vl.Rf(fx, bb, cc, hold),
  eh: M3.cw.Eh(fx, vv, cc, hold)
) -> {T.read.fast(D2.vst(fx, bb, T.LBare{}), cc) == T.read.fast(vl.vt(fx, vv), cc) : T.St}:
  Equal.trans(T.St, T.read.fast(D2.vst(fx, bb, T.LBare{}), cc), T.read.once2(T.bare.got(T.word.val(List.reverse(&2,
    Char, bb)), D2.vst(fx, [], T.LBare{}), cc, hold)), T.read.fast(vl.vt(fx, vv), cc), rf,
    Equal.trans(T.St, T.read.once2(T.bare.got(T.word.val(List.reverse(&2, Char, bb)), D2.vst(fx, [], T.LBare{}), cc,
      hold)), T.read.once2(T.bare.got(T.GotVal{vv}, D2.vst(fx, [], T.LBare{}), cc, hold)),
      T.read.fast(vl.vt(fx, vv), cc),
      Equal.cong(T.Got, T.St, gg => T.read.once2(T.bare.got(gg, D2.vst(fx, [], T.LBare{}), cc, hold)),
        T.word.val(List.reverse(&2, Char, bb)), T.GotVal{vv}, hv), eh))

# what the rest gives from the buffer, it gives from the placed value
def vl.Fin(+fx: D2.Vf, +bb: List<&2, Char>, +vv: T.Val, rest: String) -> Type:
  {T.doc.read(rest, T.MScan{D2.vst(fx, bb, T.LBare{})}) == T.doc.read(rest, T.MScan{vl.vt(fx, vv)}) : T.Doc}

# the step on a character the scan mode reads in scan mode
def vl.stp(
  +fx: D2.Vf,
  +bb: List<&2, Char>,
  +vv: T.Val,
  +cc: Char,
  +tt: String,
  ee: {T.read.fast(D2.vst(fx, bb, T.LBare{}), cc) == T.read.fast(vl.vt(fx, vv), cc) : T.St}
) -> {T.doc.read(tt, T.MScan{T.read.fast(D2.vst(fx, bb, T.LBare{}), cc)}) == T.doc.read(tt,
  T.MScan{T.read.fast(vl.vt(fx, vv), cc)}) : T.Doc}:
  Equal.cong(T.St, T.Doc, st => T.doc.read(tt, T.MScan{st}), T.read.fast(D2.vst(fx, bb, T.LBare{}), cc),
    T.read.fast(vl.vt(fx, vv), cc), ee)

# and after a carriage return
def vl.stp.cr(
  +fx: D2.Vf,
  +bb: List<&2, Char>,
  +vv: T.Val,
  +tt: String,
  ee: {T.read.fast(D2.vst(fx, bb, T.LBare{}), Chr{13}) == T.read.fast(vl.vt(fx, vv), Chr{13}) : T.St}
) -> vl.Fin(fx, bb, vv, SCon{Chr{13}, tt}):
  Equal.cong(T.St, T.Doc, st => T.doc.read(tt, T.MCr{st}), T.read.fast(D2.vst(fx, bb, T.LBare{}), Chr{13}),
    T.read.fast(vl.vt(fx, vv), Chr{13}), ee)

# the end of the text ends the word
def vl.nil.b(
  +fx: D2.Vf,
  +bb: List<&2, Char>,
  +vv: T.Val,
  hv: {T.word.val(List.reverse(&2, Char, bb)) == T.GotVal{vv} : T.Got}
) -> vl.Fin(fx, bb, vv, SNil{}):
  match fx:
    case D2.Vf{+bad, +rows, +heads, +here, +parts, +back, +qkind, +stack, +uni, +left, +arrtab}:
      Equal.trans(T.Doc, T.read.fin2(T.bare.got(T.word.val(List.reverse(&2, Char, bb)), T.St{bad, rows, heads, here,
        parts, [], T.LBare{}, back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}}, ' ', False{})),
        T.read.fin2(vl.vt(D2.Vf{bad, rows, heads, here, parts, back, qkind, stack, uni, left, arrtab}, vv)),
        T.read.fin(T.read.once2(vl.vt(D2.Vf{bad, rows, heads, here, parts, back, qkind, stack, uni, left, arrtab},
          vv))),
        Equal.cong(T.Got, T.Doc, gg => T.read.fin2(T.bare.got(gg, T.St{bad, rows, heads, here, parts, [], T.LBare{},
          back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}}, ' ', False{})),
          T.word.val(List.reverse(&2, Char, bb)), T.GotVal{vv}, hv),
        Equal.sym(T.Doc, T.read.fin(T.read.once2(vl.vt(D2.Vf{bad, rows, heads, here, parts, back, qkind, stack, uni,
          left, arrtab}, vv))), T.read.fin2(vl.vt(D2.Vf{bad, rows, heads, here, parts, back, qkind, stack, uni, left,
          arrtab}, vv)), vl.close(D2.Vf{bad, rows, heads, here, parts, back, qkind, stack, uni, left, arrtab}, vv)))

# and so it does after a date's space
def vl.nil.d(
  +fx: D2.Vf,
  +bb: List<&2, Char>,
  +vv: T.Val,
  hv: {T.word.val(List.reverse(&2, Char, bb)) == T.GotVal{vv} : T.Got}
) -> {T.doc.read(SNil{}, T.MScan{D2.vst(fx, bb, T.LDate{})}) == T.doc.read(SNil{}, T.MScan{vl.vt(fx, vv)}) : T.Doc}:
  match fx:
    case D2.Vf{+bad, +rows, +heads, +here, +parts, +back, +qkind, +stack, +uni, +left, +arrtab}:
      Equal.trans(T.Doc, T.read.fin2(T.bare.got(T.word.val(List.reverse(&2, Char, bb)), T.St{bad, rows, heads, here,
        parts, [], T.LDate{}, back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}}, ' ', False{})),
        T.read.fin2(vl.vt(D2.Vf{bad, rows, heads, here, parts, back, qkind, stack, uni, left, arrtab}, vv)),
        T.read.fin(T.read.once2(vl.vt(D2.Vf{bad, rows, heads, here, parts, back, qkind, stack, uni, left, arrtab},
          vv))),
        Equal.cong(T.Got, T.Doc, gg => T.read.fin2(T.bare.got(gg, T.St{bad, rows, heads, here, parts, [], T.LDate{},
          back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}}, ' ', False{})),
          T.word.val(List.reverse(&2, Char, bb)), T.GotVal{vv}, hv),
        Equal.sym(T.Doc, T.read.fin(T.read.once2(vl.vt(D2.Vf{bad, rows, heads, here, parts, back, qkind, stack, uni,
          left, arrtab}, vv))), T.read.fin2(vl.vt(D2.Vf{bad, rows, heads, here, parts, back, qkind, stack, uni, left,
          arrtab}, vv)), vl.close(D2.Vf{bad, rows, heads, here, parts, back, qkind, stack, uni, left, arrtab}, vv)))

# After a date's space, a character that is no digit ends the word: it is
# held and read again from the placed value, in whatever mode it opens.

# the step on a character, from two states the fast step takes to the same
# state, gives the same mode
def vl.q(
  dq: Bool,
  sq: Bool,
  cr: Bool,
  aa: T.St,
  bb: T.St,
  +cc: Char,
  ee: {T.read.fast(aa, cc) == T.read.fast(bb, cc) : T.St}
) -> {T.doc.scan.q(dq, sq, cr, aa, cc) == T.doc.scan.q(dq, sq, cr, bb, cc) : T.Mode}:
  match dq:
    case True{}:
      Equal.cong(T.St, T.Mode, st => T.doc.wrap(st), T.read.fast(aa, cc), T.read.fast(bb, cc), ee)
    case False{}:
      match sq:
        case True{}:
          Equal.cong(T.St, T.Mode, st => T.doc.wrap(st), T.read.fast(aa, cc), T.read.fast(bb, cc), ee)
        case False{}:
          match cr:
            case True{}:
              Equal.cong(T.St, T.Mode, st => T.MCr{st}, T.read.fast(aa, cc), T.read.fast(bb, cc), ee)
            case False{}:
              Equal.cong(T.St, T.Mode, st => T.MScan{st}, T.read.fast(aa, cc), T.read.fast(bb, cc), ee)

# a character after a date's space that is no digit: the word is classified
# and the character read again from the placed value
def vl.dacc(
  +fx: D2.Vf,
  +bb: List<&2, Char>,
  +vv: T.Val,
  +cc: Char,
  hv: {T.word.val(List.reverse(&2, Char, bb)) == T.GotVal{vv} : T.Got},
  hd: {Char.is_digit(cc) == False{} : Bool}
) -> {T.read.fast(D2.vst(fx, bb, T.LDate{}), cc) == T.read.fast(vl.vt(fx, vv), cc) : T.St}:
  match fx:
    case D2.Vf{+bad, +rows, +heads, +here, +parts, +back, +qkind, +stack, +uni, +left, +arrtab}:
      Equal.trans(T.St, T.read.once2(T.lex.date.go(Char.is_digit(cc), T.St{bad, rows, heads, here, parts, bb,
        T.LDate{}, back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}}, cc)),
        T.read.once2(T.bare.got(T.word.val(List.reverse(&2, Char, bb)), T.St{bad, rows, heads, here, parts, [],
          T.LDate{}, back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}}, cc, True{})),
        T.read.fast(vl.vt(D2.Vf{bad, rows, heads, here, parts, back, qkind, stack, uni, left, arrtab}, vv), cc),
        Equal.cong(Bool, T.St, xx => T.read.once2(T.lex.date.go(xx, T.St{bad, rows, heads, here, parts, bb, T.LDate{},
          back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}}, cc)), Char.is_digit(cc), False{}, hd),
        Equal.trans(T.St, T.read.once2(T.bare.got(T.word.val(List.reverse(&2, Char, bb)), T.St{bad, rows, heads, here,
          parts, [], T.LDate{}, back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}}, cc, True{})),
          T.read.once2(T.bare.got(T.GotVal{vv}, T.St{bad, rows, heads, here, parts, [], T.LDate{}, back, qkind, stack,
            T.HNone{}, uni, left, arrtab, False{}}, cc, True{})),
          T.read.fast(vl.vt(D2.Vf{bad, rows, heads, here, parts, back, qkind, stack, uni, left, arrtab}, vv), cc),
          Equal.cong(T.Got, T.St, gg => T.read.once2(T.bare.got(gg, T.St{bad, rows, heads, here, parts, [], T.LDate{},
            back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}}, cc, True{})),
            T.word.val(List.reverse(&2, Char, bb)), T.GotVal{vv}, hv),
          M3.fs.held(stack, vv, cc, bad, rows, heads, here, parts, back, qkind, uni, left, arrtab)))

# the rest after a date's space that starts with no digit reads as from the
# placed value
def vl.date.rest(
  +fx: D2.Vf,
  +bb: List<&2, Char>,
  +vv: T.Val,
  tt: String,
  +hv: {T.word.val(List.reverse(&2, Char, bb)) == T.GotVal{vv} : T.Got},
  hd: {D1.bw.digit1(tt) == False{} : Bool}
) -> {T.doc.read(tt, T.MScan{D2.vst(fx, bb, T.LDate{})}) == T.doc.read(tt, T.MScan{vl.vt(fx, vv)}) : T.Doc}:
  match tt:
    case SNil{}:
      vl.nil.d(fx, bb, vv, hv)
    case SCon{+c2, +t2}:
      Equal.cong(T.Mode, T.Doc, md => T.doc.read(t2, md), T.doc.scan(D2.vst(fx, bb, T.LDate{}), c2),
        T.doc.scan(vl.vt(fx, vv), c2),
        vl.q(Char.is_eq(c2, '"'), Char.is_eq(c2, '\''), U32.is_eq(Char.to_u32(c2), 13), D2.vst(fx, bb, T.LDate{}),
          vl.vt(fx, vv), c2, vl.dacc(fx, bb, vv, c2, hv, hd)))

# a space after a date with no digit after it ends the word, and is skipped
# after the value as a space is
def vl.fin.date(
  +fx: D2.Vf,
  +bb: List<&2, Char>,
  +vv: T.Val,
  +tt: String,
  hv: {T.word.val(List.reverse(&2, Char, bb)) == T.GotVal{vv} : T.Got},
  hs: {T.date.shaped(bb) == True{} : Bool},
  hd: {D1.bw.digit1(tt) == False{} : Bool}
) -> vl.Fin(fx, bb, vv, SCon{' ', tt}):
  Equal.trans(T.Doc, T.doc.read(tt, T.doc.scan(D2.vst(fx, bb, T.LBare{}), ' ')),
    T.doc.read(tt, T.MScan{D2.vst(fx, bb, T.LDate{})}), T.doc.read(tt, T.MScan{T.read.fast(vl.vt(fx, vv), ' ')}),
    Equal.cong(T.Mode, T.Doc, md => T.doc.read(tt, md), T.doc.scan(D2.vst(fx, bb, T.LBare{}), ' '),
      T.MScan{D2.vst(fx, bb, T.LDate{})}, vl.sp(fx, bb, hs)),
    Equal.trans(T.Doc, T.doc.read(tt, T.MScan{D2.vst(fx, bb, T.LDate{})}), T.doc.read(tt, T.MScan{vl.vt(fx, vv)}),
      T.doc.read(tt, T.MScan{T.read.fast(vl.vt(fx, vv), ' ')}), vl.date.rest(fx, bb, vv, tt, hv, hd),
      Equal.sym(T.Doc, T.doc.read(tt, T.MScan{T.read.fast(vl.vt(fx, vv), ' ')}), T.doc.read(tt, T.MScan{vl.vt(fx,
        vv)}), Equal.cong(T.St, T.Doc, st => T.doc.read(tt, T.MScan{st}), T.read.fast(vl.vt(fx, vv), ' '),
        vl.vt(fx, vv), vl.self(fx, vv, ' ', {==})))))

# an and whose left half holds, negated: its right half is false
def vl.nd(
  aa: Bool,
  bb: Bool,
  ea: {aa == True{} : Bool},
  hn: {Bool.not(Bool.and(aa, bb)) == True{} : Bool}
) -> {bb == False{} : Bool}:
  match aa:
    case True{}:
      Eq.not.true(bb, hn)
    case False{}:
      Eq.bit.absurd(&2, {bb == False{} : Bool}, ea)

# a space that ends the word: after a date the space is the date's, and
# otherwise it ends the word at once
def vl.fin.sp(
  ds: Bool,
  +fx: D2.Vf,
  +bb: List<&2, Char>,
  +vv: T.Val,
  +tt: String,
  +hv: {T.word.val(List.reverse(&2, Char, bb)) == T.GotVal{vv} : T.Got},
  +es: {T.date.shaped(bb) == ds : Bool},
  hn: {Bool.not(Bool.and(T.date.shaped(bb), D1.bw.digit1(tt))) == True{} : Bool}
) -> vl.Fin(fx, bb, vv, SCon{' ', tt}):
  match ds:
    case True{}:
      vl.fin.date(fx, bb, vv, tt, hv, es, vl.nd(T.date.shaped(bb), D1.bw.digit1(tt), es, hn))
    case False{}:
      vl.stp(fx, bb, vv, ' ', tt, vl.acc(fx, bb, vv, ' ', False{}, hv, vl.rf.sp(fx, bb, es), vl.eh.sp(fx, vv, ' ',
        {==})))

# a claim of each of the eight characters that end a bare value is a claim
# of every one: a space, a tab, a line feed, a carriage return, #, a comma, ]
# and }
def vl.delim.go(
  -P: Char -> Type,
  +xx: U32,
  b1: Bool,
  b2: Bool,
  b3: Bool,
  b4: Bool,
  b5: Bool,
  b6: Bool,
  b7: Bool,
  b8: Bool,
  e1: {U32.is_eq(xx, 32) == b1 : Bool},
  e2: {U32.is_eq(xx, 9) == b2 : Bool},
  e3: {U32.is_eq(xx, 10) == b3 : Bool},
  e4: {U32.is_eq(xx, 13) == b4 : Bool},
  e5: {U32.is_eq(xx, 35) == b5 : Bool},
  e6: {U32.is_eq(xx, 44) == b6 : Bool},
  e7: {U32.is_eq(xx, 93) == b7 : Bool},
  e8: {U32.is_eq(xx, 125) == b8 : Bool},
  hd: {Bool.or(Bool.or(b1, b2), Bool.or(Bool.or(b3, b4), Bool.or(b5, Bool.or(b6, Bool.or(b7, b8))))) == True{} : Bool},
  p1: P(' '),
  p2: P(Chr{9}),
  p3: P('\n'),
  p4: P(Chr{13}),
  p5: P('#'),
  p6: P(','),
  p7: P(']'),
  p8: P('}')
) -> P(Chr{xx}):
  match b1:
    case True{}:
      vl.chs(P, Chr{xx}, ' ', Eq.u32_eq(xx, 32, e1), p1)
    case False{}:
      match b2:
        case True{}:
          vl.chs(P, Chr{xx}, Chr{9}, Eq.u32_eq(xx, 9, e2), p2)
        case False{}:
          match b3:
            case True{}:
              vl.chs(P, Chr{xx}, '\n', Eq.u32_eq(xx, 10, e3), p3)
            case False{}:
              match b4:
                case True{}:
                  vl.chs(P, Chr{xx}, Chr{13}, Eq.u32_eq(xx, 13, e4), p4)
                case False{}:
                  match b5:
                    case True{}:
                      vl.chs(P, Chr{xx}, '#', Eq.u32_eq(xx, 35, e5), p5)
                    case False{}:
                      match b6:
                        case True{}:
                          vl.chs(P, Chr{xx}, ',', Eq.u32_eq(xx, 44, e6), p6)
                        case False{}:
                          match b7:
                            case True{}:
                              vl.chs(P, Chr{xx}, ']', Eq.u32_eq(xx, 93, e7), p7)
                            case False{}:
                              match b8:
                                case True{}:
                                  vl.chs(P, Chr{xx}, '}', Eq.u32_eq(xx, 125, e8), p8)
                                case False{}:
                                  Eq.bit.absurd(&1, P(Chr{xx}), hd)

# the same, from the scanner's test
def vl.delim(
  -P: Char -> Type,
  +xx: U32,
  hd: {T.ch.delim(Chr{xx}) == True{} : Bool},
  p1: P(' '),
  p2: P(Chr{9}),
  p3: P('\n'),
  p4: P(Chr{13}),
  p5: P('#'),
  p6: P(','),
  p7: P(']'),
  p8: P('}')
) -> P(Chr{xx}):
  vl.delim.go(P, xx, U32.is_eq(xx, 32), U32.is_eq(xx, 9), U32.is_eq(xx, 10), U32.is_eq(xx, 13), U32.is_eq(xx, 35),
    U32.is_eq(xx, 44), U32.is_eq(xx, 93), U32.is_eq(xx, 125), {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, hd,
    p1, p2, p3, p4, p5, p6, p7, p8)

# the claim for a word's buffer and one ending character, given that it is no
# date's space
def vl.Fp(+fx: D2.Vf, +bb: List<&2, Char>, +vv: T.Val, +tt: String, +cc: Char) -> Type:
  {Bool.not(D1.bw.dsp(cc, bb, tt)) == True{} : Bool} -> vl.Fin(fx, bb, vv, SCon{cc, tt})

# a text that ends the word reads as from the placed value
def vl.fin(
  +fx: D2.Vf,
  +bb: List<&2, Char>,
  +vv: T.Val,
  rest: String,
  +hv: {T.word.val(List.reverse(&2, Char, bb)) == T.GotVal{vv} : T.Got},
  +ee: {D1.bw.end(bb, rest) == True{} : Bool}
) -> vl.Fin(fx, bb, vv, rest):
  match rest:
    case SNil{}:
      vl.nil.b(fx, bb, vv, hv)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          vl.delim(ch => vl.Fp(fx, bb, vv, tt, ch), xx, Eq.and.left(T.ch.delim(Chr{xx}),
            Bool.not(D1.bw.dsp(Chr{xx}, bb, tt)), ee),
            hn => vl.fin.sp(T.date.shaped(bb), fx, bb, vv, tt, hv, {==}, hn),
            _hn => vl.stp(fx, bb, vv, Chr{9}, tt, vl.acc(fx, bb, vv, Chr{9}, False{}, hv, vl.rf.tab(fx, bb),
              vl.eh.sp(fx, vv, Chr{9}, {==}))),
            _hn => vl.stp(fx, bb, vv, '\n', tt, vl.acc(fx, bb, vv, '\n', D2.vf.inl(fx), hv, vl.rf.lf(fx, bb),
              M3.cw.nl(fx, vv))),
            _hn => vl.stp.cr(fx, bb, vv, tt, vl.acc(fx, bb, vv, Chr{13}, D2.vf.inl(fx), hv, vl.rf.cr(fx, bb),
              vl.eh.cr(fx, vv))),
            _hn => vl.stp(fx, bb, vv, '#', tt, vl.acc(fx, bb, vv, '#', True{}, hv, vl.rf.hash(fx, bb),
              M3.cw.held(fx, vv, '#'))),
            _hn => vl.stp(fx, bb, vv, ',', tt, vl.acc(fx, bb, vv, ',', True{}, hv, vl.rf.comma(fx, bb),
              M3.cw.held(fx, vv, ','))),
            _hn => vl.stp(fx, bb, vv, ']', tt, vl.acc(fx, bb, vv, ']', True{}, hv, vl.rf.rb(fx, bb),
              M3.cw.held(fx, vv, ']'))),
            _hn => vl.stp(fx, bb, vv, '}', tt, vl.acc(fx, bb, vv, '}', True{}, hv, vl.rf.rc(fx, bb),
              M3.cw.held(fx, vv, '}'))))(Eq.and.right(T.ch.delim(Chr{xx}), Bool.not(D1.bw.dsp(Chr{xx}, bb, tt)), ee))

# a bare word read from a value state, then a text that ends it: the rest is
# read from the state with the value placed
def vl.lift(
  ww: String,
  +hw: {D1.bw.word(ww) == True{} : Bool},
  +vv: T.Val,
  +hv: {T.word.val(String.to_list(ww)) == T.GotVal{vv} : T.Got},
  +fx: D2.Vf,
  +rest: String,
  ee: {D1.bw.end(D1.bw.rev(ww, []), rest) == True{} : Bool}
) -> {T.doc.read(String.append(ww, rest), T.MScan{D2.vst(fx, [], T.LVal{})}) == T.doc.read(rest,
  T.MScan{vl.vt(fx, vv)}) : T.Doc}:
  match ww:
    case SNil{}:
      Eq.bit.absurd(&2, {T.doc.read(String.append(SNil{}, rest), T.MScan{D2.vst(fx, [], T.LVal{})})
        == T.doc.read(rest, T.MScan{vl.vt(fx, vv)}) : T.Doc}, hw)
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          +bb = {M2.rev.onto(tt, [Chr{xx}]) : List<&2, Char>}
          +ho = {Equal.trans(T.Got, T.word.val(List.reverse(&2, Char, bb)), T.word.val(String.to_list(SCon{Chr{xx},
            tt})), T.GotVal{vv}, Equal.cong(List<&2, Char>, T.Got, cs => T.word.val(cs), List.reverse(&2, Char, bb),
            String.to_list(SCon{Chr{xx}, tt}), M2.wd.order(Chr{xx}, tt)), hv)
            : {T.word.val(List.reverse(&2, Char, bb)) == T.GotVal{vv} : T.Got}}
          +he = {Equal.trans(Bool, D1.bw.end(bb, rest), D1.bw.end(D1.bw.rev(tt, [Chr{xx}]), rest), True{},
            Equal.cong(List<&2, Char>, Bool, ys => D1.bw.end(ys, rest), bb, D1.bw.rev(tt, [Chr{xx}]),
            Equal.sym(List<&2, Char>, D1.bw.rev(tt, [Chr{xx}]), bb, vl.rev(tt, [Chr{xx}]))), ee)
            : {D1.bw.end(bb, rest) == True{} : Bool}}
          Equal.trans(T.Doc,
            T.doc.read(String.append(tt, rest), T.doc.scan(D2.vst(fx, [], T.LVal{}), Chr{xx})),
            T.doc.read(String.append(tt, rest), T.MScan{D2.vst(fx, [Chr{xx}], T.LBare{})}),
            T.doc.read(rest, T.MScan{vl.vt(fx, vv)}),
            Equal.cong(T.Mode, T.Doc, md => T.doc.read(String.append(tt, rest), md),
              T.doc.scan(D2.vst(fx, [], T.LVal{}), Chr{xx}), T.MScan{D2.vst(fx, [Chr{xx}], T.LBare{})},
              M1.wd.first(fx, xx, Eq.and.left(D1.word.first(Chr{xx}), D1.bw.more(tt, [Chr{xx}]), hw))),
            Equal.trans(T.Doc,
              T.doc.read(String.append(tt, rest), T.MScan{D2.vst(fx, [Chr{xx}], T.LBare{})}),
              T.doc.read(rest, T.MScan{D2.vst(fx, bb, T.LBare{})}),
              T.doc.read(rest, T.MScan{vl.vt(fx, vv)}),
              vl.run(tt, rest, fx, [Chr{xx}], Eq.and.right(D1.word.first(Chr{xx}), D1.bw.more(tt, [Chr{xx}]), hw)),
              vl.fin(fx, bb, vv, rest, ho, he)))

def L1.bare_word_reads_on(w, hw, v, hv, rw, hs, he, ps, bk, qk, sk, un, lf, ab, rest, ee):
  vl.lift(w, hw, v, hv, D2.Vf{"", rw, hs, he, ps, bk, qk, sk, un, lf, ab}, rest, ee)

# A bare word reads as a scalar or as nothing: word.val gives an integer, a
# float, a boolean or a datetime, or refuses. Each route is a case split on
# its result (as gd_word's gd.w.* are), with no scan invariant.

# whether a bare word's outcome is a scalar or a refusal
def vl.sc(gg: T.Got) -> Bool:
  match gg:
    case T.GotVal{T.VInt{_s, _d}}:
      True{}
    case T.GotVal{T.VFlo{_s, _t}}:
      True{}
    case T.GotVal{T.VBool{_b}}:
      True{}
    case T.GotVal{T.VWhen{_w}}:
      True{}
    case T.GotVal{_v}:
      False{}
    case T.GotBad{_why}:
      True{}

# nan, signed or not
def vl.sc.nan(aa: Bool, bb: Bool, cc: Bool) -> {vl.sc(T.word.spec.nan(aa, bb, cc)) == True{} : Bool}:
  match aa bb cc:
    case True{} _b _c:
      {==}
    case False{} True{} _c:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

# inf, or nan
def vl.sc.inf(aa: Bool, bb: Bool, cc: Bool, +ss: String) -> {vl.sc(T.word.spec.inf(aa, bb, cc, ss)) == True{} : Bool}:
  match aa bb cc:
    case True{} _b _c:
      {==}
    case False{} True{} _c:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      vl.sc.nan(T.str.eq(ss, "nan"), T.str.eq(ss, "+nan"), T.str.eq(ss, "-nan"))

# true, false, or the rest
def vl.sc.st(hit: Bool, other: Bool, +ss: String) -> {vl.sc(T.word.spec.t(hit, other, ss)) == True{} : Bool}:
  match hit other:
    case True{} _o:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      vl.sc.inf(T.str.eq(ss, "inf"), T.str.eq(ss, "+inf"), T.str.eq(ss, "-inf"), ss)

# a datetime's outcome
def vl.sc.when(ww: T.WhenOut) -> {vl.sc(T.word.from.when(ww)) == True{} : Bool}:
  match ww:
    case T.WSome{_w}:
      {==}
    case T.WFail{_why}:
      {==}
    case T.WSkip{}:
      {==}

# an integer's range test
def vl.sc.rng(ok: Bool, sg: T.Sign, ds: String) -> {vl.sc(T.num.fin.range(ok, sg, ds)) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

# an integer's digits
def vl.sc.int(saw: Bool, +sg: T.Sign, +ds: String) -> {vl.sc(T.num.fin.int(saw, sg, ds)) == True{} : Bool}:
  match saw:
    case True{}:
      vl.sc.rng(T.i64.fits(sg, ds), sg, ds)
    case False{}:
      {==}

# a prefixed integer
def vl.sc.base(
  signed: Bool,
  saw: Bool,
  +sg: T.Sign,
  +ds: List<&2, U32>
) -> {vl.sc(T.num.fin.base(signed, saw, sg, ds)) == True{} : Bool}:
  match signed:
    case True{}:
      {==}
    case False{}:
      vl.sc.int(saw, sg, T.dec.text(ds))

# a float's last run
def vl.sc.saw(saw: Bool, sg: T.Sign, tx: String) -> {vl.sc(T.num.fin.saw(saw, T.VFlo{sg, tx})) == True{} : Bool}:
  match saw:
    case True{}:
      {==}
    case False{}:
      {==}

# the kind the numeral scan finished in
def vl.sc.nk(
  nk: T.NK,
  +sg: T.Sign,
  +ds: List<&2, U32>,
  +saw: Bool,
  why: String,
  +cs: List<&2, Char>
) -> {vl.sc(T.num.fin.nk(nk, sg, ds, saw, why, cs)) == True{} : Bool}:
  match nk:
    case T.NBad{}:
      {==}
    case T.NLead{}:
      {==}
    case T.NSign{}:
      {==}
    case T.NZero{}:
      {==}
    case T.NDig{}:
      vl.sc.int(saw, sg, T.dec.text(ds))
    case T.NBase{}:
      vl.sc.base(T.num.signed(cs), saw, sg, ds)
    case T.NFrac{}:
      vl.sc.saw(saw, sg, T.word.body(cs))
    case T.NExp{}:
      {==}
    case T.NEDig{}:
      vl.sc.saw(saw, sg, T.word.body(cs))

# a finished numeral
def vl.sc.fin(st: T.Num, +cs: List<&2, Char>) -> {vl.sc(T.num.fin(st, cs)) == True{} : Bool}:
  match st:
    case T.Num{nk, +sign, _base, +ds, us, +saw, why}:
      match us:
        case True{}:
          {==}
        case False{}:
          vl.sc.nk(nk, sign, ds, saw, why, cs)

# a datetime or a numeral
def vl.sc.rdate(dt: Bool, +cs: List<&2, Char>) -> {vl.sc(T.word.route.date(dt, cs)) == True{} : Bool}:
  match dt:
    case True{}:
      vl.sc.when(T.when.read(cs))
    case False{}:
      vl.sc.fin(T.num.go(cs, T.num.start()), cs)

# a special's value, or a datetime or a numeral
def vl.sc.route(
  gg: T.Got,
  +dt: Bool,
  +cs: List<&2, Char>,
  eg: {vl.sc(gg) == True{} : Bool}
) -> {vl.sc(T.word.route(gg, dt, cs)) == True{} : Bool}:
  match gg:
    case T.GotVal{_v}:
      eg
    case T.GotBad{_why}:
      vl.sc.rdate(T.word.as_date(dt, T.word.ee(cs)), cs)

# a word that may be special, or not
def vl.sc.pick(special: Bool, +cs: List<&2, Char>) -> {vl.sc(T.word.val.pick(special, cs)) == True{} : Bool}:
  match special:
    case True{}:
      vl.sc.route(T.word.spec(String.from_list(cs)), T.word.or(T.word.colon(cs), T.word.dash(cs, True{})), cs,
        vl.sc.st(T.str.eq(String.from_list(cs), "true"), T.str.eq(String.from_list(cs), "false"),
        String.from_list(cs)))
    case False{}:
      vl.sc.route(T.GotBad{""}, T.word.or(T.word.colon(cs), T.word.dash(cs, True{})), cs, {==})

# every bare word reads as a scalar or as nothing
def vl.sc.word(+cs: List<&2, Char>) -> {vl.sc(T.word.val(cs)) == True{} : Bool}:
  vl.sc.pick(T.word.lead(cs), cs)

# the value state after a bare key and " = ", as vl.lift takes it
def vl.kf(+kk: String) -> D2.Vf:
  D2.Vf{"", [], [], [], [kk], T.LTop{}, T.QBasic{}, [], 0, 0, False{}}
