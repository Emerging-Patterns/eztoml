# a held character is read again after a value, in arrays and at the root
import Base
import ../../main.bend as T
import ../../laws/defs/ScalarReadbackScan.bend as D1

# The empty string. `""` goes through LQ2, which waits for the character
# after the second quote to tell it from `"""`: that character is held and
# read again by the full step from the state with "" placed, where every
# other string's next character takes the fast step. The two agree in every
# state a value leaves (LLine, LArrC, LInlC), on every character, so ""
# followed by any rest that does not start with a quote reads as the others
# do.

# a scanner with no character held, past the first character of the text
def fs.st(
  bd: String,
  rw: List<&2, T.Val>,
  hs: List<&2, String>,
  he: List<&2, String>,
  ps: List<&2, String>,
  buf: List<&2, Char>,
  lx: T.Lex,
  bk: T.Lex,
  qk: T.QKind,
  sk: List<&2, T.Ctx>,
  un: U32,
  lf: U32,
  ab: Bool
) -> T.St:
  T.St{bd, rw, hs, he, ps, buf, lx, bk, qk, sk, T.HNone{}, un, lf, ab, False{}}

# A placed value holds no character, so read.once2 leaves it as it is.

# at the root
def tk.once.root(
  end: T.End,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +ld: Bool
) -> {T.take.root(end, he, bk, qk, un, lf, ab, ld) == T.read.once2(T.take.root(end, he, bk, qk, un, lf, ab, ld))
  : T.St}:
  match end:
    case T.End{_vs, _bad, _heads}:
      {==}

# in an inline table
def tk.once.inl(
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
  +ld: Bool
) -> {T.take.inl(end, rw, hs, he, ps, rest, bk, qk, un, lf, ab, ld)
  == T.read.once2(T.take.inl(end, rw, hs, he, ps, rest, bk, qk, un, lf, ab, ld)) : T.St}:
  match end:
    case T.End{_vs, _bad, _heads}:
      {==}

# wherever the value goes
def tk.once(
  sk: List<&2, T.Ctx>,
  +vv: T.Val,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +ld: Bool
) -> {T.take.top(sk, vv, bd, rw, hs, he, ps, bk, qk, un, lf, ab, ld)
  == T.read.once2(T.take.top(sk, vv, bd, rw, hs, he, ps, bk, qk, un, lf, ab, ld)) : T.St}:
  match sk:
    case []:
      tk.once.root(T.tree.walk(T.path.cat(he, ps), T.Tw{rw, T.JPut{vv}, [], bd, "", hs, False{}},
        T.path.len(he, 0)), he, bk, qk, un, lf, ab, ld)
    case T.CArr{_items, _saved, _at} <> _rest:
      {==}
    case T.CInl{inl, +saved, +at} <> +rest:
      tk.once.inl(T.tree.walk(List.reverse(&2, String, ps), T.Tw{inl, T.JPut{vv}, [], bd, "", [],
        True{}}, 0), rw, hs, at, saved, rest, bk, qk, un, lf, ab, ld)

# closing an array places it, so it holds no character either
def arr.once(
  sk: List<&2, T.Ctx>,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +ld: Bool
) -> {T.arr.top(sk, bd, rw, hs, bk, qk, un, lf, ab, ld)
  == T.read.once2(T.arr.top(sk, bd, rw, hs, bk, qk, un, lf, ab, ld)) : T.St}:
  match sk:
    case []:
      {==}
    case T.CArr{items, +parts, +here} <> rest:
      tk.once(rest, T.VArr{List.reverse(&2, T.Val, items)}, bd, rw, hs, here, parts, bk, qk, un, lf, ab, ld)
    case T.CInl{_rows, _parts, _here} <> _rest:
      {==}

# and so does closing an inline table
def inl.once(
  sk: List<&2, T.Ctx>,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +ld: Bool
) -> {T.inl.top(sk, bd, rw, hs, bk, qk, un, lf, ab, ld)
  == T.read.once2(T.inl.top(sk, bd, rw, hs, bk, qk, un, lf, ab, ld)) : T.St}:
  match sk:
    case []:
      {==}
    case T.CArr{_items, _parts, _here} <> _rest:
      {==}
    case T.CInl{inl, +parts, +here} <> rest:
      tk.once(rest, T.VInl{T.inl.seal(inl)}, bd, rw, hs, here, parts, bk, qk, un, lf, ab, ld)

# every step after a root pair's value holds no character
def once.line(
  sp: Bool,
  hash: Bool,
  nl: Bool,
  +cc: Char,
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
  +ab: Bool
) -> {T.lex.line.go(sp, hash, nl, fs.st(bd, rw, hs, he, ps, buf, T.LLine{}, bk, qk, sk, un, lf, ab), cc)
  == T.read.once2(T.lex.line.go(sp, hash, nl, fs.st(bd, rw, hs, he, ps, buf, T.LLine{}, bk, qk, sk, un, lf,
    ab), cc)) : T.St}:
  match sp:
    case True{}:
      {==}
    case False{}:
      match hash:
        case True{}:
          {==}
        case False{}:
          match nl:
            case True{}:
              {==}
            case False{}:
              {==}

# every step after an array item
def once.arrc(
  sp: Bool,
  nl: Bool,
  hash: Bool,
  comma: Bool,
  end: Bool,
  +cc: Char,
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
  +ab: Bool
) -> {T.lex.arrc.go(sp, nl, hash, comma, end, fs.st(bd, rw, hs, he, ps, buf, T.LArrC{}, bk, qk, sk, un, lf,
  ab), cc) == T.read.once2(T.lex.arrc.go(sp, nl, hash, comma, end, fs.st(bd, rw, hs, he, ps, buf, T.LArrC{},
  bk, qk, sk, un, lf, ab), cc)) : T.St}:
  match sp:
    case True{}:
      {==}
    case False{}:
      match nl:
        case True{}:
          {==}
        case False{}:
          match hash:
            case True{}:
              {==}
            case False{}:
              match comma:
                case True{}:
                  {==}
                case False{}:
                  match end:
                    case True{}:
                      arr.once(sk, bd, rw, hs, bk, qk, un, lf, ab, False{})
                    case False{}:
                      {==}

# every step after an inline table's value
def once.inlc(
  sp: Bool,
  hash: Bool,
  comma: Bool,
  end: Bool,
  nl: Bool,
  +cc: Char,
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
  +ab: Bool
) -> {T.lex.inlc.go(sp, hash, comma, end, nl, fs.st(bd, rw, hs, he, ps, buf, T.LInlC{}, bk, qk, sk, un, lf,
  ab), cc) == T.read.once2(T.lex.inlc.go(sp, hash, comma, end, nl, fs.st(bd, rw, hs, he, ps, buf, T.LInlC{},
  bk, qk, sk, un, lf, ab), cc)) : T.St}:
  match sp:
    case True{}:
      {==}
    case False{}:
      match hash:
        case True{}:
          {==}
        case False{}:
          match comma:
            case True{}:
              {==}
            case False{}:
              match end:
                case True{}:
                  inl.once(sk, bd, rw, hs, bk, qk, un, lf, ab, False{})
                case False{}:
                  match nl:
                    case True{}:
                      {==}
                    case False{}:
                      {==}

# after a root pair's value the full step is the fast step
def fs.line(
  sp: Bool,
  nl: Bool,
  +cc: Char,
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
  es: {T.ch.sp(cc) == sp : Bool}
) -> {T.lex.line(fs.st(bd, rw, hs, he, ps, buf, T.LLine{}, bk, qk, sk, un, lf, ab), cc)
  == T.read.fast.ws(sp, nl, False{}, bd, rw, hs, he, ps, buf, T.LLine{}, bk, qk, sk, un, lf, ab, cc) : T.St}:
  match sp:
    case True{}:
      %Equal.sym(Bool, T.ch.sp(cc), True{}, es) :
        {T.lex.line.go(_, Char.is_eq(cc, '#'), T.ch.nl(cc), fs.st(bd, rw, hs, he, ps, buf, T.LLine{}, bk, qk,
          sk, un, lf, ab), cc) == T.read.fast.ws(True{}, nl, False{}, bd, rw, hs, he, ps, buf, T.LLine{}, bk,
          qk, sk, un, lf, ab, cc) : T.St}
      {==}
    case False{}:
      match nl:
        case True{}:
          once.line(T.ch.sp(cc), Char.is_eq(cc, '#'), T.ch.nl(cc), cc, bd, rw, hs, he, ps, buf, bk, qk, sk, un,
            lf, ab)
        case False{}:
          once.line(T.ch.sp(cc), Char.is_eq(cc, '#'), T.ch.nl(cc), cc, bd, rw, hs, he, ps, buf, bk, qk, sk, un,
            lf, ab)

# after an array item
def fs.arrc(
  sp: Bool,
  nl: Bool,
  +cc: Char,
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
  es: {T.ch.sp(cc) == sp : Bool},
  en: {T.ch.nl(cc) == nl : Bool}
) -> {T.lex.arrc(fs.st(bd, rw, hs, he, ps, buf, T.LArrC{}, bk, qk, sk, un, lf, ab), cc)
  == T.read.fast.ws(sp, nl, True{}, bd, rw, hs, he, ps, buf, T.LArrC{}, bk, qk, sk, un, lf, ab, cc) : T.St}:
  match sp:
    case True{}:
      %Equal.sym(Bool, T.ch.sp(cc), True{}, es) :
        {T.lex.arrc.go(_, T.ch.nl(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, ','), Char.is_eq(cc, ']'),
          fs.st(bd, rw, hs, he, ps, buf, T.LArrC{}, bk, qk, sk, un, lf, ab), cc) == T.read.fast.ws(True{}, nl,
          True{}, bd, rw, hs, he, ps, buf, T.LArrC{}, bk, qk, sk, un, lf, ab, cc) : T.St}
      {==}
    case False{}:
      match nl:
        case True{}:
          %Equal.sym(Bool, T.ch.sp(cc), False{}, es) :
            {T.lex.arrc.go(_, T.ch.nl(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, ','), Char.is_eq(cc, ']'),
              fs.st(bd, rw, hs, he, ps, buf, T.LArrC{}, bk, qk, sk, un, lf, ab), cc) == T.read.fast.ws(False{},
              True{}, True{}, bd, rw, hs, he, ps, buf, T.LArrC{}, bk, qk, sk, un, lf, ab, cc) : T.St}
          %Equal.sym(Bool, T.ch.nl(cc), True{}, en) :
            {T.lex.arrc.go(False{}, _, Char.is_eq(cc, '#'), Char.is_eq(cc, ','), Char.is_eq(cc, ']'),
              fs.st(bd, rw, hs, he, ps, buf, T.LArrC{}, bk, qk, sk, un, lf, ab), cc) == T.read.fast.ws(False{},
              True{}, True{}, bd, rw, hs, he, ps, buf, T.LArrC{}, bk, qk, sk, un, lf, ab, cc) : T.St}
          {==}
        case False{}:
          once.arrc(T.ch.sp(cc), T.ch.nl(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, ','), Char.is_eq(cc, ']'), cc,
            bd, rw, hs, he, ps, buf, bk, qk, sk, un, lf, ab)

# after an inline table's value
def fs.inlc(
  sp: Bool,
  nl: Bool,
  +cc: Char,
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
  es: {T.ch.sp(cc) == sp : Bool}
) -> {T.lex.inlc(fs.st(bd, rw, hs, he, ps, buf, T.LInlC{}, bk, qk, sk, un, lf, ab), cc)
  == T.read.fast.ws(sp, nl, False{}, bd, rw, hs, he, ps, buf, T.LInlC{}, bk, qk, sk, un, lf, ab, cc) : T.St}:
  match sp:
    case True{}:
      %Equal.sym(Bool, T.ch.sp(cc), True{}, es) :
        {T.lex.inlc.go(_, Char.is_eq(cc, '#'), Char.is_eq(cc, ','), Char.is_eq(cc, '}'), T.ch.nl(cc),
          fs.st(bd, rw, hs, he, ps, buf, T.LInlC{}, bk, qk, sk, un, lf, ab), cc) == T.read.fast.ws(True{}, nl,
          False{}, bd, rw, hs, he, ps, buf, T.LInlC{}, bk, qk, sk, un, lf, ab, cc) : T.St}
      {==}
    case False{}:
      match nl:
        case True{}:
          once.inlc(T.ch.sp(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, ','), Char.is_eq(cc, '}'), T.ch.nl(cc), cc,
            bd, rw, hs, he, ps, buf, bk, qk, sk, un, lf, ab)
        case False{}:
          once.inlc(T.ch.sp(cc), Char.is_eq(cc, '#'), Char.is_eq(cc, ','), Char.is_eq(cc, '}'), T.ch.nl(cc), cc,
            bd, rw, hs, he, ps, buf, bk, qk, sk, un, lf, ab)

# a character held after a root pair's value is read as the fast step reads it
def fs.held.root(
  end: T.End,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool,
  +cc: Char
) -> {T.read.once2(T.bare.hold.on(T.take.root(end, he, bk, qk, un, lf, ab, False{}), cc))
  == T.read.fast(T.take.root(end, he, bk, qk, un, lf, ab, False{}), cc) : T.St}:
  match end:
    case T.End{+vs, +bad, +heads}:
      fs.line(T.ch.sp(cc), T.ch.nl(cc), cc, bad, vs, heads, he, [], [], bk, qk, [], un, lf, ab, {==})

# after an inline table's value
def fs.held.inl(
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
  +cc: Char
) -> {T.read.once2(T.bare.hold.on(T.take.inl(end, rw, hs, he, ps, rest, bk, qk, un, lf, ab, False{}), cc))
  == T.read.fast(T.take.inl(end, rw, hs, he, ps, rest, bk, qk, un, lf, ab, False{}), cc) : T.St}:
  match end:
    case T.End{+inl, +bad, _heads}:
      fs.inlc(T.ch.sp(cc), T.ch.nl(cc), cc, bad, rw, hs, he, [], [], bk, qk, T.CInl{inl, ps, he} <> rest, un,
        lf, ab, {==})

# wherever the value went
def fs.held(
  sk: List<&2, T.Ctx>,
  +vv: T.Val,
  +cc: Char,
  +bd: String,
  +rw: List<&2, T.Val>,
  +hs: List<&2, String>,
  +he: List<&2, String>,
  +ps: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool
) -> {T.read.once2(T.bare.hold.on(T.take.top(sk, vv, bd, rw, hs, he, ps, bk, qk, un, lf, ab, False{}), cc))
  == T.read.fast(T.take.top(sk, vv, bd, rw, hs, he, ps, bk, qk, un, lf, ab, False{}), cc) : T.St}:
  match sk:
    case []:
      fs.held.root(T.tree.walk(T.path.cat(he, ps), T.Tw{rw, T.JPut{vv}, [], bd, "", hs, False{}},
        T.path.len(he, 0)), he, bk, qk, un, lf, ab, cc)
    case T.CArr{items, +saved, +at} <> +rest:
      fs.arrc(T.ch.sp(cc), T.ch.nl(cc), cc, bd, rw, hs, at, saved, [], bk, qk,
        T.CArr{vv <> items, saved, at} <> rest, un, lf, ab, {==}, {==})
    case T.CInl{inl, +saved, +at} <> +rest:
      fs.held.inl(T.tree.walk(List.reverse(&2, String, ps), T.Tw{inl, T.JPut{vv}, [], bd, "", [],
        True{}}, 0), rw, hs, at, saved, rest, bk, qk, un, lf, ab, cc)

# a held character is read as the fast step reads it, wherever the value went
def cw.held(
  +fx: D1.Vf,
  +vv: T.Val,
  +cc: Char
) -> {T.read.once2(T.bare.hold.on(T.val.take(D1.vst(fx, [], T.LBare{}), vv), cc))
  == T.read.fast(T.val.take(D1.vst(fx, [], T.LBare{}), vv), cc) : T.St}:
  match fx:
    case D1.Vf{+bad, +rows, +heads, +here, +parts, +back, +qkind, +stack, +uni, +left, +arrtab}:
      fs.held(stack, vv, cc, bad, rows, heads, here, parts, back, qkind, uni, left, arrtab)

# a newline after a root value is consumed with it, as the fast step would
def cw.nl.root(
  end: T.End,
  +he: List<&2, String>,
  +bk: T.Lex,
  +qk: T.QKind,
  +un: U32,
  +lf: U32,
  +ab: Bool
) -> {T.read.once2(T.bare.line.go(T.take.root(end, he, bk, qk, un, lf, ab, False{})))
  == T.read.fast(T.take.root(end, he, bk, qk, un, lf, ab, False{}), '\n') : T.St}:
  match end:
    case T.End{_vs, _bad, _heads}:
      {==}

# a newline after a bare value, wherever the value went
def cw.nl(
  +fx: D1.Vf,
  +vv: T.Val
) -> {T.read.once2(T.bare.hold(T.val.take(D1.vst(fx, [], T.LBare{}), vv), '\n', D1.vf.inl(fx)))
  == T.read.fast(T.val.take(D1.vst(fx, [], T.LBare{}), vv), '\n') : T.St}:
  match fx:
    case D1.Vf{+bad, +rows, +heads, +here, +parts, +back, +qkind, stack, +uni, +left, +arrtab}:
      match stack:
        case []:
          cw.nl.root(T.tree.walk(T.path.cat(here, parts), T.Tw{rows, T.JPut{vv}, [], bad, "", heads, False{}},
            T.path.len(here, 0)), here, back, qkind, uni, left, arrtab)
        case T.CArr{_items, _saved, _at} <> _rest:
          {==}
        case T.CInl{+inl, +saved, +at} <> +rest:
          fs.held(T.CInl{inl, saved, at} <> rest, vv, '\n', bad, rows, heads, here, parts, back, qkind, uni, left,
            arrtab)

# the character read again after the value put, or consumed with it
def cw.Eh(+fx: D1.Vf, +vv: T.Val, +cc: Char, +hold: Bool) -> Type:
  {T.read.once2(T.bare.hold(T.val.take(D1.vst(fx, [], T.LBare{}), vv), cc, hold))
    == T.read.fast(T.val.take(D1.vst(fx, [], T.LBare{}), vv), cc) : T.St}
