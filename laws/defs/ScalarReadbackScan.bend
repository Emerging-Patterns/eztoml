# the scanner fields that make a rendered scalar read back as itself
import Base
import ../../main.bend as T

# WP-N: a scalar reads back as itself. render writes an integer, a float, a
# boolean and a datetime as a bare word. The scanner reads a bare word from the
# state that waits for a value, up to the character that ends it, and word.val
# classifies it. The laws below state the classification of what render
# writes, kind by kind, and the scan in premise form: from every value state,
# whatever else it holds, as the round trip's document induction uses it.

# the fields of a scanner state that a bare value does not decide
type Vf is Data:
  Vf{bad: String, rows: List<&2, T.Val>, heads: List<&2, String>, here: List<&2, String>,
    parts: List<&2, String>, back: T.Lex, qkind: T.QKind, stack: List<&2, T.Ctx>,
    uni: U32, left: U32, arrtab: Bool}

# the scanner with those fields, a buffer and a lex state, holding no
# character and past the first character of the text
def vst(fx: Vf, buf: List<&2, Char>, lex: T.Lex) -> T.St:
  match fx:
    case Vf{bad, rows, heads, here, parts, back, qkind, stack, uni, left, arrtab}:
      T.St{bad, rows, heads, here, parts, buf, lex, back, qkind, stack, T.HNone{}, uni,
        left, arrtab, False{}}

# whether those fields are inside an inline table
def vf.inl(fx: Vf) -> Bool:
  match fx:
    case Vf{_bad, _rows, _heads, _here, _parts, _back, _qkind, stack, _uni, _left, _arrtab}:
      T.inl.open(stack)

# a text read from the state that waits for a value
def from_val(fx: Vf, text: String) -> T.Doc:
  T.doc.read(text, T.MScan{vst(fx, [], T.LVal{})})

# the text after a value's newline, read on from the state that put the value
# where the state puts values
def after_val(+fx: Vf, vv: T.Val, rest: String) -> T.Doc:
  T.doc.read(rest, T.MScan{T.read.once2(T.bare.hold(T.val.take(vst(fx, [], T.LBare{}), vv), '\n',
    vf.inl(fx)))})
