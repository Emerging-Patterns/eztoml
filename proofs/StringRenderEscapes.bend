# proofs of laws/StringRenderEscapes.bend
import Base
import ../main.bend as T
import ../src/eq.bend as Eq
import ../laws/StringRenderEscapes.bend as Laws
import ./lemmas/ControlEscapeText.bend as M1

# laws/StringRenderEscapes.bend. esc reads back what basic.one writes for one character.

# the short escapes: the character is the one the law names
def Laws.esc_quote(c, h):
  ec = Equal.sym(Char, c, '"', h)
  %ec : {Laws.esc(_) == "\\\"" : String}
  {==}

# a backslash
def Laws.esc_backslash(c, h):
  ec = Equal.sym(Char, c, '\\', h)
  %ec : {Laws.esc(_) == "\\\\" : String}
  {==}

# a backspace
def Laws.esc_b(c, h):
  ec = Equal.sym(Char, c, '\u{8}', h)
  %ec : {Laws.esc(_) == "\\b" : String}
  {==}

# a tab
def Laws.esc_t(c, h):
  ec = Equal.sym(Char, c, '\t', h)
  %ec : {Laws.esc(_) == "\\t" : String}
  {==}

# a line feed
def Laws.esc_n(c, h):
  ec = Equal.sym(Char, c, '\n', h)
  %ec : {Laws.esc(_) == "\\n" : String}
  {==}

# a form feed
def Laws.esc_f(c, h):
  ec = Equal.sym(Char, c, '\u{c}', h)
  %ec : {Laws.esc(_) == "\\f" : String}
  {==}

# a carriage return
def Laws.esc_r(c, h):
  ec = Equal.sym(Char, c, '\r', h)
  %ec : {Laws.esc(_) == "\\r" : String}
  {==}

# WP0: the other controls, one at a time through ctl.esc.all: the five with
# short escapes are ruled out by their hypotheses, and the others compute
# from ctl.txt.

# what esc_ctl says of a code point, with its escape written as ss
def ctl.eqs(+uu: U32, ss: String) -> Type:
  {ss == "\\u00" ++ String.from_list([Laws.char_at(Laws.hex_lower(), U32.to_nat(U32.div(uu, 16))),
    Laws.char_at(Laws.hex_lower(), U32.to_nat(U32.mod(uu, 16)))]) : String}

# and with its other hypotheses first
def ctl.goals(+uu: U32, ss: String) -> Type:
  {Chr{uu} != '\u{8}' : Char} -> {Chr{uu} != '\t' : Char} -> {Chr{uu} != '\n' : Char} ->
    {Chr{uu} != '\u{c}' : Char} -> {Chr{uu} != '\r' : Char} -> ctl.eqs(uu, ss)

# every other control is \u00 and two lowercase hex digits
def Laws.esc_ctl(c, h_c, h_b, h_t, h_n, h_f, h_r):
  match c:
    case Chr{+uu}:
      M1.ctl.esc.all(kk => ss => ctl.goals(kk, ss), uu, h_c,
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        hb => _ht => _hn => _hf => _hr =>
          Eq.bit.gone(&1, ctl.eqs(8, M1.ctl.txt(8)), hb({==})),
        _hb => ht => _hn => _hf => _hr =>
          Eq.bit.gone(&1, ctl.eqs(9, M1.ctl.txt(9)), ht({==})),
        _hb => _ht => hn => _hf => _hr =>
          Eq.bit.gone(&1, ctl.eqs(10, M1.ctl.txt(10)), hn({==})),
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => hf => _hr =>
          Eq.bit.gone(&1, ctl.eqs(12, M1.ctl.txt(12)), hf({==})),
        _hb => _ht => _hn => _hf => hr =>
          Eq.bit.gone(&1, ctl.eqs(13, M1.ctl.txt(13)), hr({==})),
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==},
        _hb => _ht => _hn => _hf => _hr => {==})(h_b, h_t, h_n, h_f, h_r)

# no control, no quotation mark and no backslash: written as itself
def Laws.esc_plain(c, h_c, h_q, h_b):
  match c:
    case Chr{+uu}:
      ek = M1.cls.plain(uu, M1.ctl.off(uu, 8, h_c, {==}), M1.ctl.off(uu, 9, h_c, {==}), M1.ctl.off(uu, 10, h_c, {==}),
        M1.ctl.off(uu, 12, h_c, {==}), M1.ctl.off(uu, 13, h_c, {==}), M1.neq.off(uu, 34, h_q), M1.neq.off(uu, 92, h_b),
            h_c)
      %Equal.sym(T.BK, T.basic.cls(uu), T.BKCh{}, ek) :
        {String.from_list(List.reverse(&2, Char, T.basic.disp(_, Chr{uu}, uu,
          []))) == String.from_list([Chr{uu}]) : String}
      {==}

# the root table's first pair, then the rest: the appends regrouped
def render.regroup(
  +kk: String,
  +bb: String,
  +pf: String,
  +pt: String
) -> {String.append(String.append(String.append(kk, " = " ++ bb), "\n" ++ pf), pt)
  == kk ++ " = " ++ bb ++ "\n" ++ String.append(pf, pt) : String}:
  Equal.trans(String, String.append(String.append(String.append(kk, " = " ++ bb), "\n" ++ pf), pt),
    String.append(String.append(kk, " = " ++ bb), String.append("\n" ++ pf, pt)),
    kk ++ " = " ++ bb ++ "\n" ++ String.append(pf, pt),
    Eq.append_assoc(String.append(kk, " = " ++ bb), "\n" ++ pf, pt),
    Eq.append_assoc(kk, " = " ++ bb, String.append("\n" ++ pf, pt)))

# a string pair first in the root table
def Laws.render_string(e, name, v, rest, h):
  match v:
    case T.VStr{+a1}:
      render.regroup(T.key(name), T.key.basic(a1), T.render.pass(rest, "\n", True{}, False{}),
        T.render.pass(rest, "\n", True{}, True{}))
    case T.VSpan{+a1, +a2}:
      Equal.trans(String,
        String.append(String.append(String.append(T.key(name), " = " ++ T.span.quote(a1, a2)),
          "\n" ++ T.render.pass(rest, "\n", True{}, False{})), T.render.pass(rest, "\n", True{}, True{})),
        String.append(String.append(String.append(T.key(name), " = " ++ T.key.basic(T.span.str(a1, a2,
          U32.is_zero(a2)))),
          "\n" ++ T.render.pass(rest, "\n", True{}, False{})), T.render.pass(rest, "\n", True{}, True{})),
        T.key(name) ++ " = " ++ T.key.basic(T.span.str(a1, a2, U32.is_zero(a2))) ++ "\n" ++
          String.append(T.render.pass(rest, "\n", True{}, False{}), T.render.pass(rest, "\n", True{}, True{})),
        Equal.cong(String, String, zz => String.append(String.append(String.append(T.key(name), " = " ++ zz),
          "\n" ++ T.render.pass(rest, "\n", True{}, False{})), T.render.pass(rest, "\n", True{}, True{})),
          T.span.quote(a1, a2), T.key.basic(T.span.str(a1, a2, U32.is_zero(a2))), Laws.span_quote_basic(a1, a2)),
        render.regroup(T.key(name), T.key.basic(T.span.str(a1, a2, U32.is_zero(a2))),
          T.render.pass(rest, "\n", True{}, False{}), T.render.pass(rest, "\n", True{}, True{})))
    case T.VInt{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render(T.Doc{e, T.VPair{name, T.VInt{a1, a2}} <> rest})
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VInt{a1, a2})) ++ "\n" ++ T.render(T.Doc{e,
          rest}) : String}, h)
    case T.VFlo{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render(T.Doc{e, T.VPair{name, T.VFlo{a1, a2}} <> rest})
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VFlo{a1, a2})) ++ "\n" ++ T.render(T.Doc{e,
          rest}) : String}, h)
    case T.VBool{+a1}:
      Eq.bit.absurd(&2, {T.render(T.Doc{e, T.VPair{name, T.VBool{a1}} <> rest})
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VBool{a1})) ++ "\n" ++ T.render(T.Doc{e, rest}) : String}, h)
    case T.VWhen{+a1}:
      Eq.bit.absurd(&2, {T.render(T.Doc{e, T.VPair{name, T.VWhen{a1}} <> rest})
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VWhen{a1})) ++ "\n" ++ T.render(T.Doc{e, rest}) : String}, h)
    case T.VArr{+a1}:
      Eq.bit.absurd(&2, {T.render(T.Doc{e, T.VPair{name, T.VArr{a1}} <> rest})
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VArr{a1})) ++ "\n" ++ T.render(T.Doc{e, rest}) : String}, h)
    case T.VInl{+a1}:
      Eq.bit.absurd(&2, {T.render(T.Doc{e, T.VPair{name, T.VInl{a1}} <> rest})
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VInl{a1})) ++ "\n" ++ T.render(T.Doc{e, rest}) : String}, h)
    case T.VHead{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render(T.Doc{e, T.VPair{name, T.VHead{a1, a2}} <> rest})
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VHead{a1, a2})) ++ "\n" ++ T.render(T.Doc{e,
          rest}) : String}, h)
    case T.VAot{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render(T.Doc{e, T.VPair{name, T.VAot{a1, a2}} <> rest})
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VAot{a1, a2})) ++ "\n" ++ T.render(T.Doc{e,
          rest}) : String}, h)
    case T.VAots{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render(T.Doc{e, T.VPair{name, T.VAots{a1, a2}} <> rest})
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VAots{a1, a2})) ++ "\n" ++ T.render(T.Doc{e,
          rest}) : String}, h)
    case T.VPair{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render(T.Doc{e, T.VPair{name, T.VPair{a1, a2}} <> rest})
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VPair{a1, a2})) ++ "\n" ++ T.render(T.Doc{e,
          rest}) : String}, h)

# a string pair in the pass that writes keys
def Laws.pass_string(name, v, rest, gap, trail, h):
  match v:
    case T.VStr{_a1}:
      {==}
    case T.VSpan{+a1, +a2}:
      Equal.cong(String, String, zz => (T.key(name) ++ " = " ++ zz) ++
        T.render.suf(gap, trail, List.is_empty(&2, T.Val, rest)) ++ T.render.pass(rest, gap, trail, False{}),
        T.span.quote(a1, a2), T.key.basic(T.span.str(a1, a2, U32.is_zero(a2))), Laws.span_quote_basic(a1, a2))
    case T.VInt{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VInt{a1, a2}} <> rest, gap, trail, False{})
        == (T.key(name) ++ " = " ++ T.key.basic(T.string(T.VInt{a1, a2}))) ++ T.render.suf(gap, trail,
          List.is_empty(&2, T.Val, rest)) ++ T.render.pass(rest, gap, trail, False{}) : String}, h)
    case T.VFlo{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VFlo{a1, a2}} <> rest, gap, trail, False{})
        == (T.key(name) ++ " = " ++ T.key.basic(T.string(T.VFlo{a1, a2}))) ++ T.render.suf(gap, trail,
          List.is_empty(&2, T.Val, rest)) ++ T.render.pass(rest, gap, trail, False{}) : String}, h)
    case T.VBool{+a1}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VBool{a1}} <> rest, gap, trail, False{})
        == (T.key(name) ++ " = " ++ T.key.basic(T.string(T.VBool{a1}))) ++ T.render.suf(gap, trail, List.is_empty(&2,
          T.Val, rest)) ++ T.render.pass(rest, gap, trail, False{}) : String}, h)
    case T.VWhen{+a1}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VWhen{a1}} <> rest, gap, trail, False{})
        == (T.key(name) ++ " = " ++ T.key.basic(T.string(T.VWhen{a1}))) ++ T.render.suf(gap, trail, List.is_empty(&2,
          T.Val, rest)) ++ T.render.pass(rest, gap, trail, False{}) : String}, h)
    case T.VArr{+a1}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VArr{a1}} <> rest, gap, trail, False{})
        == (T.key(name) ++ " = " ++ T.key.basic(T.string(T.VArr{a1}))) ++ T.render.suf(gap, trail, List.is_empty(&2,
          T.Val, rest)) ++ T.render.pass(rest, gap, trail, False{}) : String}, h)
    case T.VInl{+a1}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VInl{a1}} <> rest, gap, trail, False{})
        == (T.key(name) ++ " = " ++ T.key.basic(T.string(T.VInl{a1}))) ++ T.render.suf(gap, trail, List.is_empty(&2,
          T.Val, rest)) ++ T.render.pass(rest, gap, trail, False{}) : String}, h)
    case T.VHead{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VHead{a1, a2}} <> rest, gap, trail, False{})
        == (T.key(name) ++ " = " ++ T.key.basic(T.string(T.VHead{a1, a2}))) ++ T.render.suf(gap, trail,
          List.is_empty(&2, T.Val, rest)) ++ T.render.pass(rest, gap, trail, False{}) : String}, h)
    case T.VAot{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VAot{a1, a2}} <> rest, gap, trail, False{})
        == (T.key(name) ++ " = " ++ T.key.basic(T.string(T.VAot{a1, a2}))) ++ T.render.suf(gap, trail,
          List.is_empty(&2, T.Val, rest)) ++ T.render.pass(rest, gap, trail, False{}) : String}, h)
    case T.VAots{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VAots{a1, a2}} <> rest, gap, trail, False{})
        == (T.key(name) ++ " = " ++ T.key.basic(T.string(T.VAots{a1, a2}))) ++ T.render.suf(gap, trail,
          List.is_empty(&2, T.Val, rest)) ++ T.render.pass(rest, gap, trail, False{}) : String}, h)
    case T.VPair{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VPair{a1, a2}} <> rest, gap, trail, False{})
        == (T.key(name) ++ " = " ++ T.key.basic(T.string(T.VPair{a1, a2}))) ++ T.render.suf(gap, trail,
          List.is_empty(&2, T.Val, rest)) ++ T.render.pass(rest, gap, trail, False{}) : String}, h)

# a string pair in the pass that writes tables
def Laws.pass_string_tables(name, v, rest, gap, trail, h):
  match v:
    case T.VStr{_a1}:
      {==}
    case T.VSpan{_a1, _a2}:
      {==}
    case T.VInt{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VInt{a1, a2}} <> rest, gap, trail, True{})
        == T.render.pass(rest, gap, trail, True{}) : String}, h)
    case T.VFlo{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VFlo{a1, a2}} <> rest, gap, trail, True{})
        == T.render.pass(rest, gap, trail, True{}) : String}, h)
    case T.VBool{+a1}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VBool{a1}} <> rest, gap, trail, True{})
        == T.render.pass(rest, gap, trail, True{}) : String}, h)
    case T.VWhen{+a1}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VWhen{a1}} <> rest, gap, trail, True{})
        == T.render.pass(rest, gap, trail, True{}) : String}, h)
    case T.VArr{+a1}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VArr{a1}} <> rest, gap, trail, True{})
        == T.render.pass(rest, gap, trail, True{}) : String}, h)
    case T.VInl{+a1}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VInl{a1}} <> rest, gap, trail, True{})
        == T.render.pass(rest, gap, trail, True{}) : String}, h)
    case T.VHead{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VHead{a1, a2}} <> rest, gap, trail, True{})
        == T.render.pass(rest, gap, trail, True{}) : String}, h)
    case T.VAot{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VAot{a1, a2}} <> rest, gap, trail, True{})
        == T.render.pass(rest, gap, trail, True{}) : String}, h)
    case T.VAots{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VAots{a1, a2}} <> rest, gap, trail, True{})
        == T.render.pass(rest, gap, trail, True{}) : String}, h)
    case T.VPair{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.pass(T.VPair{name, T.VPair{a1, a2}} <> rest, gap, trail, True{})
        == T.render.pass(rest, gap, trail, True{}) : String}, h)

# a string pair in an inline table
def Laws.inline_string(name, v, rest, gap, trail, h):
  match v:
    case T.VStr{_a1}:
      {==}
    case T.VSpan{+a1, +a2}:
      Equal.cong(String, String, zz => T.key(name) ++ " = " ++ zz ++
        T.render.suf(gap, trail, List.is_empty(&2, T.Val, rest)) ++ T.render.go(rest, gap, trail),
        T.span.quote(a1, a2), T.key.basic(T.span.str(a1, a2, U32.is_zero(a2))), Laws.span_quote_basic(a1, a2))
    case T.VInt{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.go(T.VPair{name, T.VInt{a1, a2}} <> rest, gap, trail)
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VInt{a1, a2})) ++ T.render.suf(gap, trail, List.is_empty(&2,
          T.Val, rest)) ++ T.render.go(rest, gap, trail) : String}, h)
    case T.VFlo{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.go(T.VPair{name, T.VFlo{a1, a2}} <> rest, gap, trail)
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VFlo{a1, a2})) ++ T.render.suf(gap, trail, List.is_empty(&2,
          T.Val, rest)) ++ T.render.go(rest, gap, trail) : String}, h)
    case T.VBool{+a1}:
      Eq.bit.absurd(&2, {T.render.go(T.VPair{name, T.VBool{a1}} <> rest, gap, trail)
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VBool{a1})) ++ T.render.suf(gap, trail, List.is_empty(&2,
          T.Val, rest)) ++ T.render.go(rest, gap, trail) : String}, h)
    case T.VWhen{+a1}:
      Eq.bit.absurd(&2, {T.render.go(T.VPair{name, T.VWhen{a1}} <> rest, gap, trail)
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VWhen{a1})) ++ T.render.suf(gap, trail, List.is_empty(&2,
          T.Val, rest)) ++ T.render.go(rest, gap, trail) : String}, h)
    case T.VArr{+a1}:
      Eq.bit.absurd(&2, {T.render.go(T.VPair{name, T.VArr{a1}} <> rest, gap, trail)
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VArr{a1})) ++ T.render.suf(gap, trail, List.is_empty(&2,
          T.Val, rest)) ++ T.render.go(rest, gap, trail) : String}, h)
    case T.VInl{+a1}:
      Eq.bit.absurd(&2, {T.render.go(T.VPair{name, T.VInl{a1}} <> rest, gap, trail)
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VInl{a1})) ++ T.render.suf(gap, trail, List.is_empty(&2,
          T.Val, rest)) ++ T.render.go(rest, gap, trail) : String}, h)
    case T.VHead{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.go(T.VPair{name, T.VHead{a1, a2}} <> rest, gap, trail)
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VHead{a1, a2})) ++ T.render.suf(gap, trail, List.is_empty(&2,
          T.Val, rest)) ++ T.render.go(rest, gap, trail) : String}, h)
    case T.VAot{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.go(T.VPair{name, T.VAot{a1, a2}} <> rest, gap, trail)
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VAot{a1, a2})) ++ T.render.suf(gap, trail, List.is_empty(&2,
          T.Val, rest)) ++ T.render.go(rest, gap, trail) : String}, h)
    case T.VAots{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.go(T.VPair{name, T.VAots{a1, a2}} <> rest, gap, trail)
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VAots{a1, a2})) ++ T.render.suf(gap, trail, List.is_empty(&2,
          T.Val, rest)) ++ T.render.go(rest, gap, trail) : String}, h)
    case T.VPair{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.go(T.VPair{name, T.VPair{a1, a2}} <> rest, gap, trail)
        == T.key(name) ++ " = " ++ T.key.basic(T.string(T.VPair{a1, a2})) ++ T.render.suf(gap, trail, List.is_empty(&2,
          T.Val, rest)) ++ T.render.go(rest, gap, trail) : String}, h)

# a string item in an array
def Laws.array_string(v, rest, gap, trail, h):
  match v:
    case T.VStr{_a1}:
      {==}
    case T.VSpan{+a1, +a2}:
      Equal.cong(String, String, zz => zz ++
        T.render.suf(gap, trail, List.is_empty(&2, T.Val, rest)) ++ T.render.go(rest, gap, trail),
        T.span.quote(a1, a2), T.key.basic(T.span.str(a1, a2, U32.is_zero(a2))), Laws.span_quote_basic(a1, a2))
    case T.VInt{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.go(T.VInt{a1, a2} <> rest, gap, trail)
        == T.key.basic(T.string(T.VInt{a1, a2})) ++ T.render.suf(gap, trail, List.is_empty(&2, T.Val,
          rest)) ++ T.render.go(rest, gap, trail) : String}, h)
    case T.VFlo{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.go(T.VFlo{a1, a2} <> rest, gap, trail)
        == T.key.basic(T.string(T.VFlo{a1, a2})) ++ T.render.suf(gap, trail, List.is_empty(&2, T.Val,
          rest)) ++ T.render.go(rest, gap, trail) : String}, h)
    case T.VBool{+a1}:
      Eq.bit.absurd(&2, {T.render.go(T.VBool{a1} <> rest, gap, trail)
        == T.key.basic(T.string(T.VBool{a1})) ++ T.render.suf(gap, trail, List.is_empty(&2, T.Val,
          rest)) ++ T.render.go(rest, gap, trail) : String}, h)
    case T.VWhen{+a1}:
      Eq.bit.absurd(&2, {T.render.go(T.VWhen{a1} <> rest, gap, trail)
        == T.key.basic(T.string(T.VWhen{a1})) ++ T.render.suf(gap, trail, List.is_empty(&2, T.Val,
          rest)) ++ T.render.go(rest, gap, trail) : String}, h)
    case T.VArr{+a1}:
      Eq.bit.absurd(&2, {T.render.go(T.VArr{a1} <> rest, gap, trail)
        == T.key.basic(T.string(T.VArr{a1})) ++ T.render.suf(gap, trail, List.is_empty(&2, T.Val,
          rest)) ++ T.render.go(rest, gap, trail) : String}, h)
    case T.VInl{+a1}:
      Eq.bit.absurd(&2, {T.render.go(T.VInl{a1} <> rest, gap, trail)
        == T.key.basic(T.string(T.VInl{a1})) ++ T.render.suf(gap, trail, List.is_empty(&2, T.Val,
          rest)) ++ T.render.go(rest, gap, trail) : String}, h)
    case T.VHead{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.go(T.VHead{a1, a2} <> rest, gap, trail)
        == T.key.basic(T.string(T.VHead{a1, a2})) ++ T.render.suf(gap, trail, List.is_empty(&2, T.Val,
          rest)) ++ T.render.go(rest, gap, trail) : String}, h)
    case T.VAot{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.go(T.VAot{a1, a2} <> rest, gap, trail)
        == T.key.basic(T.string(T.VAot{a1, a2})) ++ T.render.suf(gap, trail, List.is_empty(&2, T.Val,
          rest)) ++ T.render.go(rest, gap, trail) : String}, h)
    case T.VAots{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.go(T.VAots{a1, a2} <> rest, gap, trail)
        == T.key.basic(T.string(T.VAots{a1, a2})) ++ T.render.suf(gap, trail, List.is_empty(&2, T.Val,
          rest)) ++ T.render.go(rest, gap, trail) : String}, h)
    case T.VPair{+a1, +a2}:
      Eq.bit.absurd(&2, {T.render.go(T.VPair{a1, a2} <> rest, gap, trail)
        == T.key.basic(T.string(T.VPair{a1, a2})) ++ T.render.suf(gap, trail, List.is_empty(&2, T.Val,
          rest)) ++ T.render.go(rest, gap, trail) : String}, h)
