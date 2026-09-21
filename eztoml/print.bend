# eztoml/print: a value written back as TOML text.
import Base
import ./value.bend as V
import ./text.bend as Txt

# `true` or `false`
def render.bool(b: Bool) -> String:
  match b:
    case True{}:
      "true"
    case False{}:
      "false"

# one value. Arrays and tables are written inline. A chain of cells is the
# inside of an array; a chain of pairs is the inside of a table.
def render.val(v: V.Val) -> String:
  match v:
    case V.VStr{s}:
      Txt.quote(s)
    case V.VInt{raw}:
      raw
    case V.VFloat{raw}:
      raw
    case V.VBool{b}:
      render.bool(b)
    case V.VOff{raw}:
      raw
    case V.VLocal{raw}:
      raw
    case V.VDay{raw}:
      raw
    case V.VTime{raw}:
      raw
    case V.VArr{items, _aot}:
      "[" ++ render.val(items) ++ "]"
    case V.VTab{pairs, _explicit, _inline}:
      "{" ++ render.val(pairs) ++ "}"
    case V.VNil{}:
      ""
    case V.VCons{h, V.VNil{}}:
      render.val(h)
    case V.VCons{h, t}:
      render.val(h) ++ ", " ++ render.val(t)
    case V.VPair{k, val, V.VNil{}}:
      Txt.key(k) ++ " = " ++ render.val(val)
    case V.VPair{k, val, r}:
      Txt.key(k) ++ " = " ++ render.val(val) ++ ", " ++ render.val(r)
    case V.VMiss{}:
      ""

# key segments, innermost first, each written as a key
def render.segs(ks: List<&2, String>) -> List<&2, String>:
  match ks:
    case []:
      []
    case h <> t:
      Txt.key(h) <> render.segs(t)

# a dotted key, outermost first
def render.path(ks: List<&2, String>) -> String:
  String.join(List.reverse(&2, String, render.segs(ks)), ".")

# the pairs of a table. `aot` walks the cells of an array of tables.
def render.go(node: V.Val, +ks: List<&2, String>, aot: Bool) -> String:
  match node aot:
    case V.VNil{} _:
      ""
    case V.VCons{V.VTab{ps, _ex, _inl}, t} True{}:
      "\n[[" ++ render.path(ks) ++ "]]" ++ render.go(ps, ks, False{}) ++
        render.go(t, ks, True{})
    case V.VCons{_h, t} True{}:
      render.go(t, ks, True{})
    case V.VPair{+k, V.VTab{ps, ex, True{}}, r} False{}:
      "\n" ++ Txt.key(k) ++ " = " ++ render.val(V.VTab{ps, ex, True{}}) ++
        render.go(r, ks, False{})
    case V.VPair{+k, V.VTab{ps, _ex, False{}}, r} False{}:
      "\n[" ++ render.path(k <> ks) ++ "]" ++
        render.go(ps, k <> ks, False{}) ++ render.go(r, ks, False{})
    case V.VPair{+k, V.VArr{items, True{}}, r} False{}:
      render.go(items, k <> ks, True{}) ++ render.go(r, ks, False{})
    case V.VPair{+k, v, r} False{}:
      "\n" ++ Txt.key(k) ++ " = " ++ render.val(v) ++ render.go(r, ks, False{})
    case _ _:
      ""

# a value as TOML text
def render(v: V.Val) -> String:
  match v:
    case V.VTab{_pairs, _explicit, True{}}:
      render.val(v)
    case V.VTab{pairs, _explicit, False{}}:
      String.trim_start(render.go(pairs, [], False{}))
    case _:
      render.val(v)
