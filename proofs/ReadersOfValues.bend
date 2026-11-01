# proofs of laws/ReadersOfValues.bend
import Base
import ../main.bend as T
import ../src/eq.bend as Eq
import ../laws/ReadersOfValues.bend as Laws

def Laws.string_of(_text):
  {==}

# laws/ReadersOfValues.bend.

# a span's walk counts its U32 down while Base's take counts a Nat, and the
# two counts agree at every step: zero is 0n, and anything else is one more
# than itself less one
def span.take(
  src: String,
  +nn: U32,
  zz: Bool,
  ez: {U32.is_zero(nn) == zz : Bool}
) -> {T.span.str(src, nn, zz) == String.take(src, U32.to_nat(nn)) : String}:
  match src zz:
    case SNil{} True{}:
      {==}
    case SNil{} False{}:
      {==}
    case SCon{+hh, +tt} True{}:
      Equal.cong(Nat, String, mm => String.take(SCon{hh, tt}, mm), 0n,
        U32.to_nat(nn),
        Equal.sym(Nat, U32.to_nat(nn), 0n, Eq.u32_zero_nat(nn, ez)))
    case SCon{+hh, +tt} False{}:
      Equal.trans(String,
        SCon{hh, T.span.str(tt, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)))},
        SCon{hh, String.take(tt, U32.to_nat(U32.sub(nn, 1)))},
        String.take(SCon{hh, tt}, U32.to_nat(nn)),
        Equal.cong(String, String, s2 => SCon{hh, s2},
          T.span.str(tt, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1))),
          String.take(tt, U32.to_nat(U32.sub(nn, 1))),
          span.take(tt, U32.sub(nn, 1), U32.is_zero(U32.sub(nn, 1)), {==})),
        Equal.cong(Nat, String, mm => String.take(SCon{hh, tt}, mm),
          1n+U32.to_nat(U32.sub(nn, 1)), U32.to_nat(nn),
          Equal.sym(Nat, U32.to_nat(nn), 1n+U32.to_nat(U32.sub(nn, 1)),
            Eq.u32_dec_nat(nn, ez))))

def Laws.string_of_span(src, n):
  span.take(src, n, U32.is_zero(n), {==})

def Laws.string_of_other(v, e):
  match v:
    case T.VStr{a}:
      Eq.bit.absurd2(&2, {T.string(T.VStr{a}) == "" : String}, e)
    case T.VSpan{a, b}:
      Eq.bit.absurd2(&2, {T.string(T.VSpan{a, b}) == "" : String}, e)
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
    case T.VPair{_a, _b}:
      {==}

def Laws.digits_of(_sign, _text):
  {==}

def Laws.digits_of_other(v, e):
  match v:
    case T.VInt{a, b}:
      Eq.bit.absurd2(&2, {T.digits(T.VInt{a, b}) == "" : String}, e)
    case T.VStr{_a}:
      {==}
    case T.VSpan{_a, _b}:
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
    case T.VPair{_a, _b}:
      {==}

def Laws.flag_of(_bit):
  {==}

def Laws.flag_of_other(v, e):
  match v:
    case T.VBool{a}:
      Eq.bit.absurd2(&2, {T.flag(T.VBool{a}) == False{} : Bool}, e)
    case T.VStr{_a}:
      {==}
    case T.VSpan{_a, _b}:
      {==}
    case T.VInt{_a, _b}:
      {==}
    case T.VFlo{_a, _b}:
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
    case T.VPair{_a, _b}:
      {==}
