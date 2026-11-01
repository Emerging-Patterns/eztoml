# the scan of a bare value from its first character to its delimiter
import Base
import ../../main.bend as T
import ../../src/eq.bend as Eq
import ../../laws/WordReadsBack.bend as L1
import ../../laws/defs/BareValueGrammar.bend as D1
import ../../laws/defs/ScalarReadbackScan.bend as D2
import ./FreshNamesInRows.bend as M1
import ./ReorderedTableNames.bend as M2

# The scan of a bare value. It starts in the value state, stays on the fast
# path for each character it keeps, and a newline ends it.

# a character a bare value keeps is no delimiter
def wd.delim(+cc: Char, hw: {D1.word.char(cc) == True{} : Bool}) -> {T.ch.delim(cc) == False{} : Bool}:
  Eq.not.true(T.ch.delim(cc), Eq.and.left(Bool.not(T.ch.delim(cc)),
    Bool.not(Bool.or(Char.is_eq(cc, '"'), Char.is_eq(cc, '\''))), hw))

# a character that is no delimiter is pushed on the fast path
def wd.fast(
  +fx: D2.Vf,
  +buf: List<&2, Char>,
  +cc: Char,
  hd: {T.ch.delim(cc) == False{} : Bool}
) -> {T.MScan{T.read.fast(D2.vst(fx, buf, T.LBare{}), cc)} == T.MScan{D2.vst(fx, cc <> buf, T.LBare{})} : T.Mode}:
  match fx:
    case D2.Vf{bad, rows, heads, here, parts, back, qkind, stack, uni, left, arrtab}:
      Equal.cong(Bool, T.Mode, bb => T.MScan{T.read.fast.bare(bb, bad, rows, heads, here, parts, buf, back,
        qkind, stack, uni, left, arrtab, cc)}, T.ch.delim(cc), False{}, hd)

# a later character of a bare value is pushed and the value goes on
def wd.step(
  +fx: D2.Vf,
  +buf: List<&2, Char>,
  +xx: U32,
  +hw: {D1.word.char(Chr{xx}) == True{} : Bool}
) -> {T.doc.scan(D2.vst(fx, buf, T.LBare{}), Chr{xx}) == T.MScan{D2.vst(fx, Chr{xx} <> buf, T.LBare{})} : T.Mode}:
  Equal.trans(T.Mode,
    T.doc.scan(D2.vst(fx, buf, T.LBare{}), Chr{xx}),
    T.MScan{T.read.fast(D2.vst(fx, buf, T.LBare{}), Chr{xx})},
    T.MScan{D2.vst(fx, Chr{xx} <> buf, T.LBare{})},
    M2.scan.other(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), U32.is_eq(xx, 13),
      D2.vst(fx, buf, T.LBare{}), Chr{xx}, {==}, {==}, {==}, ch => D1.word.char(ch), hw, {==}, {==}, {==}),
    wd.fast(fx, buf, Chr{xx}, wd.delim(Chr{xx}, hw)))

# the characters a bare value keeps are pushed one by one, whatever follows
def wd.run(
  ks: String,
  +rr: String,
  +fx: D2.Vf,
  +buf: List<&2, Char>,
  +ee: {L1.word.rest(ks) == True{} : Bool}
) -> {T.doc.read(String.append(ks, rr), T.MScan{D2.vst(fx, buf, T.LBare{})}) == T.doc.read(rr, T.MScan{D2.vst(fx,
  M1.rev.onto(ks, buf), T.LBare{})}) : T.Doc}:
  match ks:
    case SNil{}:
      {==}
    case SCon{hh, +tt}:
      match hh:
        case Chr{+xx}:
          Equal.trans(T.Doc,
            T.doc.read(String.append(tt, rr), T.doc.scan(D2.vst(fx, buf, T.LBare{}), Chr{xx})),
            T.doc.read(String.append(tt, rr), T.MScan{D2.vst(fx, Chr{xx} <> buf, T.LBare{})}),
            T.doc.read(rr, T.MScan{D2.vst(fx, M1.rev.onto(tt, Chr{xx} <> buf), T.LBare{})}),
            Equal.cong(T.Mode, T.Doc, md => T.doc.read(String.append(tt, rr), md),
              T.doc.scan(D2.vst(fx, buf, T.LBare{}), Chr{xx}),
              T.MScan{D2.vst(fx, Chr{xx} <> buf, T.LBare{})},
              wd.step(fx, buf, xx, Eq.and.left(D1.word.char(Chr{xx}), L1.word.rest(tt), ee))),
            wd.run(tt, rr, fx, Chr{xx} <> buf, Eq.and.right(D1.word.char(Chr{xx}), L1.word.rest(tt), ee)))

# the value state's dispatch sends a character that starts a bare value to
# the bare state
def wd.go(
  sp: Bool,
  nl: Bool,
  hash: Bool,
  qq: Bool,
  lit: Bool,
  br: Bool,
  inl: Bool,
  +st: T.St,
  +cc: Char,
  hsp: {sp == False{} : Bool},
  hnl: {nl == False{} : Bool},
  hhs: {hash == False{} : Bool},
  hqq: {qq == False{} : Bool},
  hlt: {lit == False{} : Bool},
  hbr: {br == False{} : Bool},
  hin: {inl == False{} : Bool}
) -> {T.lex.val.go(sp, nl, hash, qq, lit, br, inl, st, cc) == T.st.push(st, cc, T.LBare{}) : T.St}:
  match sp:
    case True{}:
      Eq.bit.absurd2(&2, {T.lex.val.go(True{}, nl, hash, qq, lit, br, inl, st, cc)
        == T.st.push(st, cc, T.LBare{}) : T.St}, hsp)
    case False{}:
      match nl:
        case True{}:
          Eq.bit.absurd2(&2, {T.lex.val.go(False{}, True{}, hash, qq, lit, br, inl, st, cc)
            == T.st.push(st, cc, T.LBare{}) : T.St}, hnl)
        case False{}:
          match hash:
            case True{}:
              Eq.bit.absurd2(&2, {T.lex.val.go(False{}, False{}, True{}, qq, lit, br, inl, st, cc)
                == T.st.push(st, cc, T.LBare{}) : T.St}, hhs)
            case False{}:
              match qq:
                case True{}:
                  Eq.bit.absurd2(&2, {T.lex.val.go(False{}, False{}, False{}, True{}, lit, br, inl, st, cc)
                    == T.st.push(st, cc, T.LBare{}) : T.St}, hqq)
                case False{}:
                  match lit:
                    case True{}:
                      Eq.bit.absurd2(&2, {T.lex.val.go(False{}, False{}, False{}, False{}, True{}, br, inl, st,
                        cc) == T.st.push(st, cc, T.LBare{}) : T.St}, hlt)
                    case False{}:
                      match br:
                        case True{}:
                          Eq.bit.absurd2(&2, {T.lex.val.go(False{}, False{}, False{}, False{}, False{}, True{},
                            inl, st, cc) == T.st.push(st, cc, T.LBare{}) : T.St}, hbr)
                        case False{}:
                          match inl:
                            case True{}:
                              Eq.bit.absurd2(&2, {T.lex.val.go(False{}, False{}, False{}, False{}, False{},
                                False{}, True{}, st, cc) == T.st.push(st, cc, T.LBare{}) : T.St}, hin)
                            case False{}:
                              {==}

# the value state passes a character that is no space and no newline to its
# dispatch, which sends it to the bare state
def wd.ws(
  sp: Bool,
  nl: Bool,
  bad: String,
  rows: List<&2, T.Val>,
  heads: List<&2, String>,
  here: List<&2, String>,
  parts: List<&2, String>,
  back: T.Lex,
  qkind: T.QKind,
  stack: List<&2, T.Ctx>,
  uni: U32,
  left: U32,
  arrtab: Bool,
  +cc: Char,
  hsp: {sp == False{} : Bool},
  hnl: {nl == False{} : Bool},
  fsp: {T.ch.sp(cc) == False{} : Bool},
  fnl: {T.ch.nl(cc) == False{} : Bool},
  fhs: {Char.is_eq(cc, '#') == False{} : Bool},
  fqq: {Char.is_eq(cc, '"') == False{} : Bool},
  flt: {Char.is_eq(cc, '\'') == False{} : Bool},
  fbr: {Char.is_eq(cc, '[') == False{} : Bool},
  fin: {Char.is_eq(cc, '{') == False{} : Bool}
) -> {T.read.fast.ws(sp, nl, False{}, bad, rows, heads, here, parts, [], T.LVal{}, back, qkind, stack, uni, left,
  arrtab, cc) == T.St{bad, rows, heads, here, parts, [cc], T.LBare{}, back, qkind, stack, T.HNone{}, uni, left, arrtab,
  False{}} : T.St}:
  match sp:
    case True{}:
      Eq.bit.absurd2(&2, {T.read.fast.ws(True{}, nl, False{}, bad, rows, heads, here, parts, [], T.LVal{}, back,
        qkind, stack, uni, left, arrtab, cc) == T.St{bad, rows, heads, here, parts, [cc], T.LBare{}, back, qkind,
        stack, T.HNone{}, uni, left, arrtab, False{}} : T.St}, hsp)
    case False{}:
      match nl:
        case True{}:
          Eq.bit.absurd2(&2, {T.read.fast.ws(False{}, True{}, False{}, bad, rows, heads, here, parts, [],
            T.LVal{}, back, qkind, stack, uni, left, arrtab, cc) == T.St{bad, rows, heads, here, parts, [cc],
            T.LBare{}, back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}} : T.St}, hnl)
        case False{}:
          Equal.cong(T.St, T.St, ss => T.read.once2(ss),
            T.lex.val.go(T.ch.sp(cc), T.ch.nl(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, '"'),
              Char.is_eq(cc, '\''), Char.is_eq(cc, '['), Char.is_eq(cc, '{'), T.St{bad, rows, heads, here, parts,
              [], T.LVal{}, back, qkind, stack, T.HNone{}, uni, left, arrtab, False{}}, cc),
            T.st.push(T.St{bad, rows, heads, here, parts, [], T.LVal{}, back, qkind, stack, T.HNone{}, uni, left,
              arrtab, False{}}, cc, T.LBare{}),
            wd.go(T.ch.sp(cc), T.ch.nl(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, '"'), Char.is_eq(cc, '\''),
              Char.is_eq(cc, '['), Char.is_eq(cc, '{'), T.St{bad, rows, heads, here, parts, [], T.LVal{}, back,
              qkind, stack, T.HNone{}, uni, left, arrtab, False{}}, cc, fsp, fnl, fhs, fqq, flt, fbr, fin))

# the first character of a bare value, read from the value state, is pushed
def wd.lval(
  +fx: D2.Vf,
  +cc: Char,
  +fsp: {T.ch.sp(cc) == False{} : Bool},
  +fnl: {T.ch.nl(cc) == False{} : Bool},
  +fhs: {Char.is_eq(cc, '#') == False{} : Bool},
  +fqq: {Char.is_eq(cc, '"') == False{} : Bool},
  +flt: {Char.is_eq(cc, '\'') == False{} : Bool},
  +fbr: {Char.is_eq(cc, '[') == False{} : Bool},
  +fin: {Char.is_eq(cc, '{') == False{} : Bool}
) -> {T.MScan{T.read.fast(D2.vst(fx, [], T.LVal{}), cc)} == T.MScan{D2.vst(fx, [cc], T.LBare{})} : T.Mode}:
  match fx:
    case D2.Vf{bad, rows, heads, here, parts, back, qkind, stack, uni, left, arrtab}:
      Equal.cong(T.St, T.Mode, ss => T.MScan{ss},
        T.read.fast.ws(T.ch.sp(cc), T.ch.nl(cc), False{}, bad, rows, heads, here, parts, [], T.LVal{}, back,
          qkind, stack, uni, left, arrtab, cc),
        T.St{bad, rows, heads, here, parts, [cc], T.LBare{}, back, qkind, stack, T.HNone{}, uni, left, arrtab,
          False{}},
        wd.ws(T.ch.sp(cc), T.ch.nl(cc), bad, rows, heads, here, parts, back, qkind, stack, uni, left, arrtab, cc,
          fsp, fnl, fsp, fnl, fhs, fqq, flt, fbr, fin))

# the facts wd.lval takes, from a character that starts a bare value. The
# delimiters are a space, a newline, #, a comma and the closers, in that order
def wd.first(
  +fx: D2.Vf,
  +xx: U32,
  +h1: {D1.word.first(Chr{xx}) == True{} : Bool}
) -> {T.doc.scan(D2.vst(fx, [], T.LVal{}), Chr{xx}) == T.MScan{D2.vst(fx, [Chr{xx}], T.LBare{})} : T.Mode}:
  +hw = {Eq.and.left(D1.word.char(Chr{xx}), Bool.not(Bool.or(Char.is_eq(Chr{xx}, '['),
    Char.is_eq(Chr{xx}, '{'))), h1) : {D1.word.char(Chr{xx}) == True{} : Bool}}
  +hd = {wd.delim(Chr{xx}, hw) : {T.ch.delim(Chr{xx}) == False{} : Bool}}
  +hq = {Eq.not.true(Bool.or(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\'')),
    Eq.and.right(Bool.not(T.ch.delim(Chr{xx})), Bool.not(Bool.or(Char.is_eq(Chr{xx}, '"'),
    Char.is_eq(Chr{xx}, '\''))), hw))
    : {Bool.or(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\'')) == False{} : Bool}}
  +hb = {Eq.not.true(Bool.or(Char.is_eq(Chr{xx}, '['), Char.is_eq(Chr{xx}, '{')),
    Eq.and.right(D1.word.char(Chr{xx}), Bool.not(Bool.or(Char.is_eq(Chr{xx}, '['),
    Char.is_eq(Chr{xx}, '{'))), h1)) : {Bool.or(Char.is_eq(Chr{xx}, '['), Char.is_eq(Chr{xx}, '{')) == False{} : Bool}}
  +d1 = {Eq.or.right_false(T.ch.sp(Chr{xx}), Bool.or(T.ch.nl(Chr{xx}), Bool.or(Char.is_eq(Chr{xx}, '#'),
    Bool.or(Char.is_eq(Chr{xx}, ','), Bool.or(Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '}'))))), hd)
    : {Bool.or(T.ch.nl(Chr{xx}), Bool.or(Char.is_eq(Chr{xx}, '#'), Bool.or(Char.is_eq(Chr{xx}, ','),
    Bool.or(Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '}'))))) == False{} : Bool}}
  +d2 = {Eq.or.right_false(T.ch.nl(Chr{xx}), Bool.or(Char.is_eq(Chr{xx}, '#'), Bool.or(Char.is_eq(Chr{xx}, ','),
    Bool.or(Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '}')))), d1)
    : {Bool.or(Char.is_eq(Chr{xx}, '#'), Bool.or(Char.is_eq(Chr{xx}, ','), Bool.or(Char.is_eq(Chr{xx}, ']'),
    Char.is_eq(Chr{xx}, '}')))) == False{} : Bool}}
  Equal.trans(T.Mode,
    T.doc.scan(D2.vst(fx, [], T.LVal{}), Chr{xx}),
    T.MScan{T.read.fast(D2.vst(fx, [], T.LVal{}), Chr{xx})},
    T.MScan{D2.vst(fx, [Chr{xx}], T.LBare{})},
    M2.scan.other(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), U32.is_eq(xx, 13),
      D2.vst(fx, [], T.LVal{}), Chr{xx}, {==}, {==}, {==}, ch => D1.word.first(ch), h1, {==}, {==}, {==}),
    wd.lval(fx, Chr{xx},
      Eq.or.left_false(T.ch.sp(Chr{xx}), Bool.or(T.ch.nl(Chr{xx}), Bool.or(Char.is_eq(Chr{xx}, '#'),
        Bool.or(Char.is_eq(Chr{xx}, ','), Bool.or(Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '}'))))), hd),
      Eq.or.left_false(T.ch.nl(Chr{xx}), Bool.or(Char.is_eq(Chr{xx}, '#'), Bool.or(Char.is_eq(Chr{xx}, ','),
        Bool.or(Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '}')))), d1),
      Eq.or.left_false(Char.is_eq(Chr{xx}, '#'), Bool.or(Char.is_eq(Chr{xx}, ','),
        Bool.or(Char.is_eq(Chr{xx}, ']'), Char.is_eq(Chr{xx}, '}'))), d2),
      Eq.or.left_false(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), hq),
      Eq.or.right_false(Char.is_eq(Chr{xx}, '"'), Char.is_eq(Chr{xx}, '\''), hq),
      Eq.or.left_false(Char.is_eq(Chr{xx}, '['), Char.is_eq(Chr{xx}, '{'), hb),
      Eq.or.right_false(Char.is_eq(Chr{xx}, '['), Char.is_eq(Chr{xx}, '{'), hb)))

# a newline ends a bare value: word.val classifies the characters pushed, in
# the order they came, and a value is put where the state puts values
def wd.end(
  +fx: D2.Vf,
  +buf: List<&2, Char>
) -> {T.doc.scan(D2.vst(fx, buf, T.LBare{}), '\n') == T.MScan{T.read.once2(T.bare.got( T.word.val(List.reverse(&2,
  Char, buf)), D2.vst(fx, [], T.LBare{}), '\n', D2.vf.inl(fx)))} : T.Mode}:
  match fx:
    case D2.Vf{bad, rows, heads, here, parts, back, qkind, stack, uni, left, arrtab}:
      {==}
