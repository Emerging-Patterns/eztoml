# document equality, canonical form and the kinds and boxes it compares
import Base
import ../../main.bend as T
import ./BareValueGrammar.bend as D1

# `same` and `own`: the specification's equality of documents (REVIEW-4).
# A parsed plain string is a span and a built one is owned; a table's pairs
# are in no particular order. `same` compares documents as TOML values: a
# table as the pairs it holds, matched by name whatever their order, an
# array and an array of tables in order, and a scalar by its fields, a
# string by its characters whether owned or a span. A table and an inline
# table are different kinds; a table's stored path and the error field are
# not compared. `own` reads every span out into an owned string.

# the value of a table's first pair of a name, and the rows without that pair
type Pick is Data:
  Picked{val: T.Val, rest: List<&2, T.Val>}
  NoPick{}

# a row kept in front of what a pick left
def pick.cons(hh: T.Val, pp: Pick) -> Pick:
  match pp:
    case Picked{vv, rest}:
      Picked{vv, hh <> rest}
    case NoPick{}:
      NoPick{}

# a pair of the name is picked; any other pair is kept
def pick.step(eq: Bool, nn: String, vv: T.Val, tt: List<&2, T.Val>, more: Unit -> Pick) -> Pick:
  match eq:
    case True{}:
      Picked{vv, tt}
    case False{}:
      pick.cons(T.VPair{nn, vv}, more(Unit{}))

# the first pair named k, taken out of the rows
def pick(rows: List<&2, T.Val>, +kk: String) -> Pick:
  match rows:
    case []:
      NoPick{}
    case T.VPair{+nn, vv} <> +tt:
      pick.step(String.eq(nn, kk), nn, vv, tt, _u => pick(tt, kk))
    case hh <> tt:
      pick.cons(hh, pick(tt, kk))

# the rest when this part holds, and False otherwise
def and_then(ok: Bool, more: Unit -> Bool) -> Bool:
  match ok:
    case True{}:
      more(Unit{})
    case False{}:
      False{}

# the kinds of value that hold a list: an array, an inline table, a table, an
# element of an array of tables, and an array of tables
type Kin is Data:
  KArr{}
  KInl{}
  KHead{}
  KAot{}
  KAots{}

# whether two kinds are one
def kin.eq(aa: Kin, bb: Kin) -> Bool:
  match aa bb:
    case KArr{} KArr{}:
      True{}
    case KInl{} KInl{}:
      True{}
    case KHead{} KHead{}:
      True{}
    case KAot{} KAot{}:
      True{}
    case KAots{} KAots{}:
      True{}
    case _a _b:
      False{}

# a value's kind and list, when it holds one
type Box is Data:
  Boxed{kin: Kin, list: List<&2, T.Val>}
  Unboxed{}

# the kind and the list a value holds
def kids(vv: T.Val) -> Box:
  match vv:
    case T.VArr{items}:
      Boxed{KArr{}, items}
    case T.VInl{rows}:
      Boxed{KInl{}, rows}
    case T.VHead{_path, rows}:
      Boxed{KHead{}, rows}
    case T.VAot{_path, rows}:
      Boxed{KAot{}, rows}
    case T.VAots{_path, elems}:
      Boxed{KAots{}, elems}
    case _:
      Unboxed{}

# a box of the kind whose list the comparison accepts
def same.boxed(kk: Kin, bx: Box, cmp: List<&2, T.Val> -> Bool) -> Bool:
  match bx:
    case Boxed{k2, list}:
      and_then(kin.eq(kk, k2), _u => cmp(list))
    case Unboxed{}:
      False{}

# a value of the kind whose list the comparison accepts
def same.box(kk: Kin, ww: T.Val, cmp: List<&2, T.Val> -> Bool) -> Bool:
  same.boxed(kk, kids(ww), cmp)

# a scalar's fields as parse stores them; a string's characters, owned or a
# span
type Sc is Data:
  ScStr{text: String}
  ScInt{sign: T.Sign, digits: String}
  ScFlo{sign: T.Sign, text: String}
  ScBool{bit: Bool}
  ScWhen{when: T.When}
  ScNo{}

# the fields of a scalar value, and ScNo for any other value
def scal(vv: T.Val) -> Sc:
  match vv:
    case T.VStr{text}:
      ScStr{text}
    case T.VSpan{src, +nn}:
      ScStr{T.span.str(src, nn, U32.is_zero(nn))}
    case T.VInt{sign, digits}:
      ScInt{sign, digits}
    case T.VFlo{sign, text}:
      ScFlo{sign, text}
    case T.VBool{bit}:
      ScBool{bit}
    case T.VWhen{when}:
      ScWhen{when}
    case _:
      ScNo{}

# whether two signs are one
def sign.eq(aa: T.Sign, bb: T.Sign) -> Bool:
  match aa bb:
    case T.Plus{} T.Plus{}:
      True{}
    case T.Minus{} T.Minus{}:
      True{}
    case _a _b:
      False{}

# whether two bits are one
def bit.eq(aa: Bool, bb: Bool) -> Bool:
  match aa bb:
    case True{} True{}:
      True{}
    case False{} False{}:
      True{}
    case _a _b:
      False{}

# whether two dates are one, field by field
def date.eq(aa: T.Date, bb: T.Date) -> Bool:
  match aa bb:
    case T.Date{y1, m1, d1} T.Date{y2, m2, d2}:
      Bool.and(U32.is_eq(y1, y2), Bool.and(U32.is_eq(m1, m2), U32.is_eq(d1, d2)))

# whether two clocks are one, field by field
def clock.eq(aa: T.Clock, bb: T.Clock) -> Bool:
  match aa bb:
    case T.Clock{h1, m1, s1, f1} T.Clock{h2, m2, s2, f2}:
      Bool.and(U32.is_eq(h1, h2), Bool.and(U32.is_eq(m1, m2),
        Bool.and(U32.is_eq(s1, s2), String.eq(f1, f2))))

# whether two zones are one, field by field
def zone.eq(aa: T.Zone, bb: T.Zone) -> Bool:
  match aa bb:
    case T.Zulu{} T.Zulu{}:
      True{}
    case T.Shift{s1, h1, m1} T.Shift{s2, h2, m2}:
      Bool.and(sign.eq(s1, s2), Bool.and(U32.is_eq(h1, h2), U32.is_eq(m1, m2)))
    case _a _b:
      False{}

# whether two datetimes are one: the same form, field by field
def when.eq(aa: T.When, bb: T.When) -> Bool:
  match aa bb:
    case T.WOff{d1, c1, z1} T.WOff{d2, c2, z2}:
      Bool.and(date.eq(d1, d2), Bool.and(clock.eq(c1, c2), zone.eq(z1, z2)))
    case T.WLocal{d1, c1} T.WLocal{d2, c2}:
      Bool.and(date.eq(d1, d2), clock.eq(c1, c2))
    case T.WDate{d1} T.WDate{d2}:
      date.eq(d1, d2)
    case T.WTime{c1} T.WTime{c2}:
      clock.eq(c1, c2)
    case _a _b:
      False{}

# whether two scalars are one: the same kind, field by field
def sc.eq(aa: Sc, bb: Sc) -> Bool:
  match aa bb:
    case ScStr{x1} ScStr{x2}:
      String.eq(x1, x2)
    case ScInt{s1, d1} ScInt{s2, d2}:
      Bool.and(sign.eq(s1, s2), String.eq(d1, d2))
    case ScFlo{s1, x1} ScFlo{s2, x2}:
      Bool.and(sign.eq(s1, s2), String.eq(x1, x2))
    case ScBool{b1} ScBool{b2}:
      bit.eq(b1, b2)
    case ScWhen{w1} ScWhen{w2}:
      when.eq(w1, w2)
    case _a _b:
      False{}

# whether two values are the same scalar
def same.atom(vv: T.Val, ww: T.Val) -> Bool:
  sc.eq(scal(vv), scal(ww))

# a pair's value against the value of the other rows' first pair of its name,
# then the rest against the other rows without that pair
def same.pair(pp: Pick, cmp: T.Val -> Bool, rest: List<&2, T.Val> -> Bool) -> Bool:
  match pp:
    case Picked{ww, left}:
      and_then(cmp(ww), _u => rest(left))
    case NoPick{}:
      False{}

# a value that is not a pair against the other rows' first value, then the
# rest against the others after it
def same.item(other: List<&2, T.Val>, cmp: T.Val -> Bool, rest: List<&2, T.Val> -> Bool) -> Bool:
  match other:
    case []:
      False{}
    case ww <> left:
      and_then(cmp(ww), _u => rest(left))

# whether every value of xs has its match in the other rows, with nothing of
# them left over: a pair matches the first pair of its name, wherever it is,
# and any other value matches the first value left, in order. A table's rows
# are pairs and an array's items are not, so a table is compared as a map
# and an array in order. A pair whose value is a pair, which no well-formed
# document holds, matches nothing
def same.go(xs: List<&2, T.Val>, other: List<&2, T.Val>) -> Bool:
  match xs:
    case []:
      List.is_empty(&2, T.Val, other)
    case T.VPair{nn, T.VArr{items}} <> tt:
      same.pair(pick(other, nn), ww => same.box(KArr{}, ww, ws => same.go(items, ws)), rr => same.go(tt, rr))
    case T.VPair{nn, T.VInl{rows}} <> tt:
      same.pair(pick(other, nn), ww => same.box(KInl{}, ww, ws => same.go(rows, ws)), rr => same.go(tt, rr))
    case T.VPair{nn, T.VHead{_path, rows}} <> tt:
      same.pair(pick(other, nn), ww => same.box(KHead{}, ww, ws => same.go(rows, ws)), rr => same.go(tt, rr))
    case T.VPair{nn, T.VAot{_path, rows}} <> tt:
      same.pair(pick(other, nn), ww => same.box(KAot{}, ww, ws => same.go(rows, ws)), rr => same.go(tt, rr))
    case T.VPair{nn, T.VAots{_path, elems}} <> tt:
      same.pair(pick(other, nn), ww => same.box(KAots{}, ww, ws => same.go(elems, ws)), rr => same.go(tt, rr))
    case T.VPair{nn, vv} <> tt:
      same.pair(pick(other, nn), ww => same.atom(vv, ww), rr => same.go(tt, rr))
    case T.VArr{items} <> tt:
      same.item(other, ww => same.box(KArr{}, ww, ws => same.go(items, ws)), rr => same.go(tt, rr))
    case T.VInl{rows} <> tt:
      same.item(other, ww => same.box(KInl{}, ww, ws => same.go(rows, ws)), rr => same.go(tt, rr))
    case T.VHead{_path, rows} <> tt:
      same.item(other, ww => same.box(KHead{}, ww, ws => same.go(rows, ws)), rr => same.go(tt, rr))
    case T.VAot{_path, rows} <> tt:
      same.item(other, ww => same.box(KAot{}, ww, ws => same.go(rows, ws)), rr => same.go(tt, rr))
    case T.VAots{_path, elems} <> tt:
      same.item(other, ww => same.box(KAots{}, ww, ws => same.go(elems, ws)), rr => same.go(tt, rr))
    case vv <> tt:
      same.item(other, ww => same.atom(vv, ww), rr => same.go(tt, rr))

# whether two documents are the same TOML document: each root table matches
# the other
def same(aa: T.Doc, bb: T.Doc) -> Bool:
  match aa bb:
    case T.Doc{_e1, +r1} T.Doc{_e2, +r2}:
      Bool.and(same.go(r1, r2), same.go(r2, r1))

# WP-D: the document render writes, read back. render writes a table's pairs
# that are no table first, in order, then its tables and arrays of tables, in
# order, each one's rows the same way; parse puts every pair in the order it
# reads it and reads a span out only when own asks. canon is the document so
# reordered, with every span read out and no error: an element of an array of
# tables under the array's path, as the walk stores it.

# a table's pairs that are no table and no array of tables, in order
def canon.keys(xs: List<&2, T.Val>) -> List<&2, T.Val>:
  match xs:
    case []:
      []
    case T.VPair{_n, T.VHead{_p, _r}} <> tt:
      canon.keys(tt)
    case T.VPair{_n, T.VAots{_p, _es}} <> tt:
      canon.keys(tt)
    case hh <> tt:
      hh <> canon.keys(tt)

# which list canon.go reorders: a table's rows, or the elements of an array
# of tables stored under path
type CMode is Data:
  CTabs{}
  CElems{path: String}

# a table's tables and arrays of tables, in order, each one's rows reordered;
# or an array's elements, each under the array's path with its rows reordered
def canon.go(xs: List<&2, T.Val>, md: CMode) -> List<&2, T.Val>:
  match xs md:
    case [] _m:
      []
    case T.VPair{nn, T.VHead{pp, +rr}} <> tt CTabs{}:
      T.VPair{nn, T.VHead{pp, List.append(&2, T.Val, canon.keys(rr), canon.go(rr, CTabs{}))}} <>
        canon.go(tt, CTabs{})
    case T.VPair{nn, T.VAots{+pp, es}} <> tt CTabs{}:
      T.VPair{nn, T.VAots{pp, canon.go(es, CElems{pp})}} <> canon.go(tt, CTabs{})
    case T.VAot{_q, +rr} <> tt CElems{+pp}:
      T.VAot{pp, List.append(&2, T.Val, canon.keys(rr), canon.go(rr, CTabs{}))} <> canon.go(tt, CElems{pp})
    case _hh <> tt m2:
      canon.go(tt, m2)

# a table's tables and arrays of tables, reordered
def canon.tabs(xs: List<&2, T.Val>) -> List<&2, T.Val>:
  canon.go(xs, CTabs{})

# a table's rows as render writes them: the pairs that are no table, then
# the tables
def canon.rows(+xs: List<&2, T.Val>) -> List<&2, T.Val>:
  List.append(&2, T.Val, canon.keys(xs), canon.tabs(xs))

# the document as parse reads back what render wrote for it
def canon(dd: T.Doc) -> T.Doc:
  match dd:
    case T.Doc{_bad, rows}:
      T.Doc{"", D1.own.rows(canon.rows(rows))}
