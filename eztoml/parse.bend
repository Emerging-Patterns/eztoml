# eztoml/parse: a TOML document. `parse` reads text into a table.
import Base
import ./value.bend as V
import ./lex.bend as L
import ./text.bend as Txt

# a dotted name, in order
type Nm is Data:
  NNil{}
  NCons{key: String, rest: Nm}

# one step down a value: a key, or an index in an array of tables
type Step is Data:
  SName{key: String}
  SIdx{n: Nat}

# a path from a table down to a value
type Path is Data:
  PNil{}
  PCons{step: Step, rest: Path}

# a document: the first error, or empty, and the root table
type Doc is Data:
  Doc{err: String, rt: V.Val}

# a write: the value, and the error or empty
type Wrote is Data:
  Wrote{node: V.Val, err: String}

# a header applied to a table: the table, the error, the path of the header
type Opened is Data:
  Opened{node: V.Val, err: String, cur: Path}

# where a value is being read
type Pm is Data:
  MTop{}
  MKey{}
  MSeg{}
  MBrack{}
  MHead{}
  MHeadDot{}
  MEnd{}
  MVal{}
  MPart{}
  MArr{}
  MArrSep{}
  MInl{}
  MInlKey{}
  MInlSeg{}
  MInlSep{}

# what an inline table is waiting for
type Want is Data:
  WKey{}
  WEq{}
  WVal{}
  WSep{}

# one unfinished value
type Fr is Data:
  FArr{items: V.Val}
  FInl{pairs: V.Val, names: Nm, want: Want}
  FHold{names: Nm, cur: Path}

# unfinished values, innermost first
type Sk is Data:
  KNil{}
  KCons{fr: Fr, rest: Sk}

# the reader
type St is Data:
  St{err: String, rt: V.Val, cur: Path, mode: Pm, names: Nm, part: String,
    stack: Sk, aot: Bool}

# a value read from a literal, or why it is not one
type Lit is Data:
  LOk{v: V.Val}
  LBad{why: String}

# a key found in a pair chain. `pre` is the pairs before it, reversed
type Work is Data:
  ZNone{}
  ZKey{miss: Bool, child: V.Val, pre: V.Val, post: V.Val, k: String,
    explicit: Bool, inline: Bool}
  ZIdx{pre: V.Val, n: Nat, aot: Bool}
  ZArr{ppre: V.Val, ppost: V.Val, k: String, explicit: Bool, inline: Bool,
    elpre: V.Val, idx: Nat, k2: String}

# the last element of an array of tables
type End is Data:
  ENone{}
  EGot{pre: V.Val, last: V.Val, i: Nat}

# a character class for a number
type Nc is Data:
  CPlus{}
  CMinus{}
  CZero{}
  C17{}
  C89{}
  CDot{}
  CE{}
  CX{}
  CO{}
  CB{}
  CHex{}
  CBad{}

# how far a number has been read
type Ns is Data:
  NsBad{}
  Ns0{}
  NsSign{}
  NsZ{}
  NsZS{}
  NsD{}
  NsDot{}
  NsF{}
  NsE{}
  NsEs{}
  NsEd{}
  NsX{}
  NsXd{}
  NsO{}
  NsOd{}
  NsB{}
  NsBd{}

# a date read so far
type Dr is Data:
  DNo{}
  DYes{v: V.Val}

# two digits, or not, and the chars left
type Take is Data:
  TNo{}
  TYes{n: U32, rest: List<&2, Char>}

# a keyword that names a value, or not one
type Hit is Data:
  HYes{v: V.Val}
  HNo{}

# which digits an underscore may sit between
type Uk is Data:
  UkDec{}
  UkHex{}
  UkOct{}
  UkBin{}

# an underscore walk
type Us is Data:
  UsNone{}
  UsDig{}
  UsUnder{}
  UsBad{}

# the first error, kept
def err.keep(old: String, why: String) -> String:
  match old:
    case SNil{}:
      why
    case SCon{_h, _t}:
      old

# the path `b` with `a` in front of it
def path.cat(a: Path, b: Path) -> Path:
  match a:
    case PNil{}:
      b
    case PCons{s, r}:
      PCons{s, path.cat(r, b)}

# a name as a path of keys
def nm.path(ns: Nm) -> Path:
  match ns:
    case NNil{}:
      PNil{}
    case NCons{k, r}:
      PCons{SName{k}, nm.path(r)}

# `k` after the segments already gathered
def nm.snoc(ns: Nm, +k: String) -> Nm:
  match ns:
    case NNil{}:
      NCons{k, NNil{}}
    case NCons{h, t}:
      NCons{h, nm.snoc(t, k)}

# a cell after the cells already gathered
def val.snoc(items: V.Val, v: V.Val) -> V.Val:
  match items:
    case V.VNil{}:
      V.VCons{v, V.VNil{}}
    case V.VCons{h, t}:
      V.VCons{h, val.snoc(t, v)}
    case _:
      V.VCons{v, V.VNil{}}

# how many cells an array holds
def arr.len(items: V.Val) -> Nat:
  match items:
    case V.VNil{}:
      0n
    case V.VCons{_h, t}:
      1n+arr.len(t)
    case _:
      0n

# `pre` reversed onto `acc`
def pair.cat.go(pre: V.Val, acc: V.Val) -> V.Val:
  match pre:
    case V.VNil{}:
      acc
    case V.VPair{n, v, r}:
      pair.cat.go(r, V.VPair{n, v, acc})
    case _:
      acc

# `pre` reversed, then `child`, then `post`
def pair.cat(pre: V.Val, +k: String, child: V.Val, post: V.Val) -> V.Val:
  pair.cat.go(pre, V.VPair{k, child, post})

# `pre` reversed, then `tail` in order
def join.rev(pre: V.Val, tail: V.Val) -> V.Val:
  match pre:
    case V.VNil{}:
      tail
    case V.VCons{h, r}:
      join.rev(r, V.VCons{h, tail})
    case _:
      tail

# `pre` reversed onto `acc`, for an array
def cons.cat.go(pre: V.Val, acc: V.Val) -> V.Val:
  match pre:
    case V.VNil{}:
      acc
    case V.VCons{h, r}:
      cons.cat.go(r, V.VCons{h, acc})
    case _:
      acc

# `pre` reversed, then `child`, then `post`, for an array
def cons.cat(pre: V.Val, child: V.Val, post: V.Val) -> V.Val:
  cons.cat.go(pre, V.VCons{child, post})

# the value a write keeps when the write failed
def wrote.node(e: String, n: V.Val, old: V.Val) -> V.Val:
  match e:
    case SNil{}:
      n
    case SCon{_h, _t}:
      old

# the key, once this pair has been compared with it
def spot.at(hit: Bool, found: Unit -> Work, missed: Unit -> Work) -> Work:
  match hit:
    case True{}:
      found(Unit{})
    case False{}:
      missed(Unit{})

# the key in a pair chain
def spot.go(pairs: V.Val, +k: String, +pre: V.Val, +explicit: Bool,
  +inline: Bool) -> Work:
  match pairs:
    case V.VNil{}:
      ZKey{True{}, V.VMiss{}, pre, V.VNil{}, k, explicit, inline}
    case V.VPair{+n, +v, +r}:
      spot.at(String.eq(n, k),
        _u => ZKey{False{}, v, pre, r, k, explicit, inline},
        _u => spot.go(r, k, V.VPair{n, v, pre}, explicit, inline))
    case _:
      ZKey{True{}, V.VMiss{}, pre, V.VNil{}, k, explicit, inline}

# the last cell, with the cells before it reversed
def arr.end(items: V.Val, pre: V.Val, i: Nat) -> End:
  match items:
    case V.VNil{}:
      ENone{}
    case V.VCons{+h, +t}:
      match t:
        case V.VNil{}:
          EGot{pre, h, i}
        case _:
          arr.end(t, V.VCons{h, pre}, 1n+i)
    case _:
      ENone{}

# the spliced table when the header had no error
def open.place.at(e: String, n: V.Val, cur: Path, pre: V.Val, post: V.Val,
  +k: String, explicit: Bool, inline: Bool, node: V.Val) -> Opened:
  match e:
    case SNil{}:
      Opened{V.VTab{pair.cat(pre, k, n, post), explicit, inline}, "",
        PCons{SName{k}, cur}}
    case SCon{_h, _t}:
      Opened{node, e, PNil{}}

# a header's value spliced back into the table it was found in
def open.place(o: Opened, pre: V.Val, post: V.Val, +k: String, explicit: Bool,
  inline: Bool, node: V.Val) -> Opened:
  match o:
    case Opened{n, e, cur}:
      open.place.at(e, n, cur, pre, post, k, explicit, inline, node)

# the array, once the last element's write is known
def open.arr.at(e: String, n: V.Val, cur: Path, elpre: V.Val, idx: Nat,
  ppre: V.Val, ppost: V.Val, +k: String, explicit: Bool, inline: Bool,
  node: V.Val) -> Opened:
  match e:
    case SNil{}:
      Opened{V.VTab{pair.cat(ppre, k,
        V.VArr{cons.cat(elpre, n, V.VNil{}), True{}}, ppost), explicit, inline},
        "", PCons{SName{k}, PCons{SIdx{idx}, cur}}}
    case SCon{_h, _t}:
      Opened{node, e, PNil{}}

# an updated array spliced into the table that holds it
def open.arr.place(o: Opened, elpre: V.Val, idx: Nat, ppre: V.Val, ppost: V.Val,
  +k: String, explicit: Bool, inline: Bool, node: V.Val) -> Opened:
  match o:
    case Opened{n, e, cur}:
      open.arr.at(e, n, cur, elpre, idx, ppre, ppost, k, explicit, inline, node)

# an implicit table promoted, or an explicit one left as it was
def open.fin.promote(ex: Bool, pairs: V.Val, pre: V.Val, post: V.Val, +k: String,
  explicit: Bool, node: V.Val) -> Opened:
  match ex:
    case True{}:
      Opened{node, "table already defined", PNil{}}
    case False{}:
      Opened{V.VTab{pair.cat(pre, k, V.VTab{pairs, True{}, False{}}, post),
        explicit, False{}}, "", PCons{SName{k}, PNil{}}}

# an existing table at the final segment
def open.fin.ex(ex: Bool, inl: Bool, pairs: V.Val, pre: V.Val, post: V.Val,
  +k: String, explicit: Bool, node: V.Val) -> Opened:
  match inl:
    case True{}:
      Opened{node, "inline table", PNil{}}
    case False{}:
      open.fin.promote(ex, pairs, pre, post, k, explicit, node)

# a final header on a value already known to be a table's child
def open.fin.have(child: V.Val, pre: V.Val, post: V.Val, +k: String,
  explicit: Bool, node: V.Val) -> Opened:
  match child:
    case V.VTab{pairs, ex, inline}:
      open.fin.ex(ex, inline, pairs, pre, post, k, explicit, node)
    case V.VArr{_items, _af}:
      Opened{node, "table already defined", PNil{}}
    case _:
      Opened{node, "not a table", PNil{}}

# a missing final table, or the value already written there
def open.fin.miss(gap: Bool, child: V.Val, pre: V.Val, post: V.Val, +k: String,
  explicit: Bool, node: V.Val) -> Opened:
  match gap:
    case True{}:
      Opened{V.VTab{pair.cat(pre, k, V.VTab{V.VNil{}, True{}, False{}}, post),
        explicit, False{}}, "", PCons{SName{k}, PNil{}}}
    case False{}:
      open.fin.have(child, pre, post, k, explicit, node)

# a final `[table]`
def open.fin.tab(focus: Work, explicit: Bool, +k: String, node: V.Val) -> Opened:
  match focus:
    case ZKey{miss, child, pre, post, _n, _ex, _il}:
      open.fin.miss(miss, child, pre, post, k, explicit, node)
    case _:
      Opened{node, "not a table", PNil{}}

# a final `[[table]]` on an existing array
def open.fin.append(+items: V.Val, af: Bool, pre: V.Val, post: V.Val, +k: String,
  explicit: Bool, node: V.Val) -> Opened:
  match af:
    case False{}:
      Opened{node, "array of tables", PNil{}}
    case True{}:
      Opened{V.VTab{pair.cat(pre, k, V.VArr{val.snoc(items,
        V.VTab{V.VNil{}, True{}, False{}}), True{}}, post), explicit, False{}},
        "", PCons{SName{k}, PCons{SIdx{arr.len(items)}, PNil{}}}}

# the value a final `[[table]]` found
def open.fin.arr(child: V.Val, pre: V.Val, post: V.Val, +k: String,
  explicit: Bool, node: V.Val) -> Opened:
  match child:
    case V.VArr{items, af}:
      open.fin.append(items, af, pre, post, k, explicit, node)
    case _:
      Opened{node, "array of tables", PNil{}}

# a new array of tables, or an append
def open.fin.anew(miss: Bool, child: V.Val, pre: V.Val, post: V.Val, +k: String,
  explicit: Bool, node: V.Val) -> Opened:
  match miss:
    case True{}:
      Opened{V.VTab{pair.cat(pre, k, V.VArr{V.VCons{V.VTab{V.VNil{}, True{},
        False{}}, V.VNil{}}, True{}}, post), explicit, False{}}, "",
        PCons{SName{k}, PCons{SIdx{0n}, PNil{}}}}
    case False{}:
      open.fin.arr(child, pre, post, k, explicit, node)

# a final `[[table]]`
def open.fin.aot(focus: Work, explicit: Bool, +k: String, node: V.Val) -> Opened:
  match focus:
    case ZKey{miss, child, pre, post, _n, _ex, _il}:
      open.fin.anew(miss, child, pre, post, k, explicit, node)
    case _:
      Opened{node, "not a table", PNil{}}

# a final header, table or array of tables
def open.fin.which(aot: Bool, focus: Work, explicit: Bool, +k: String,
  node: V.Val) -> Opened:
  match aot:
    case True{}:
      open.fin.aot(focus, explicit, k, node)
    case False{}:
      open.fin.tab(focus, explicit, k, node)

# a final header inside a table
def open.fin.in(inline: Bool, pairs: V.Val, +explicit: Bool, +k: String,
  aot: Bool, node: V.Val) -> Opened:
  match inline:
    case True{}:
      Opened{node, "inline table", PNil{}}
    case False{}:
      open.fin.which(aot, spot.go(pairs, k, V.VNil{}, explicit, False{}),
        explicit, k, node)

# a final header on a value
def open.final(+node: V.Val, +k: String, aot: Bool) -> Opened:
  match node:
    case V.VTab{+pairs, +explicit, +inline}:
      open.fin.in(inline, pairs, explicit, k, aot, node)
    case _:
      Opened{node, "not a table", PNil{}}

# the last element of an array of tables, opened as a final header
def open.last(e: End, +k: String, aot: Bool, ppre: V.Val, ppost: V.Val,
  pk: String, explicit: Bool, inline: Bool, node: V.Val) -> Opened:
  match e:
    case ENone{}:
      Opened{node, "array of tables", PNil{}}
    case EGot{pre, last, i}:
      open.arr.place(open.final(last, k, aot), pre, i, ppre, ppost, pk,
        explicit, inline, node)

# the table an array-of-tables walk started from
def open.back(elpre: V.Val, rest: V.Val, ppre: V.Val, ppost: V.Val, +k: String,
  explicit: Bool, inline: Bool) -> V.Val:
  V.VTab{pair.cat(ppre, k, V.VArr{join.rev(elpre, rest), True{}}, ppost),
    explicit, inline}

# a header. `focus` carries the table the previous key was found in
def open.go(+names: Nm, +node: V.Val, +aot: Bool, focus: Work) -> Opened:
  match names:
    case NNil{}:
      Opened{node, "key", PNil{}}
    case NCons{+k, +more}:
      match more:
        case NNil{}:
          match node:
            case V.VTab{_pairs, _explicit, _inl}:
              match focus:
                case ZNone{}:
                  open.final(node, k, aot)
                case ZKey{gap, held, pre, post, +pk, ex, il}:
                  match gap:
                    case True{}:
                      open.place(open.final(V.VTab{V.VNil{}, False{}, False{}},
                        k, aot), pre, post, pk, ex, il, node)
                    case False{}:
                      match held:
                        case V.VTab{_ps, _ex2, il2}:
                          match il2:
                            case True{}:
                              Opened{node, "inline table", PNil{}}
                            case False{}:
                              open.place(open.final(held, k, aot), pre, post,
                                pk, ex, il, node)
                        case V.VArr{items, af}:
                          match af:
                            case False{}:
                              Opened{node, "array of tables", PNil{}}
                            case True{}:
                              open.last(arr.end(items, V.VNil{}, 0n), k, aot,
                                pre, post, pk, ex, il, node)
                        case _:
                          Opened{node, "not a table", PNil{}}
                case ZArr{ppre, ppost, +pk, ex, il, elpre, idx, +k2}:
                  Opened{open.back(elpre, node, ppre, ppost, pk, ex, il),
                    "not a table", PNil{}}
                case ZIdx{_pre, _n, _af}:
                  Opened{node, "not a table", PNil{}}
            case V.VCons{+h, +t}:
              match h:
                case V.VTab{+ps, +ex2, il2}:
                  match il2:
                    case True{}:
                      match t:
                        case V.VNil{}:
                          match focus:
                            case ZArr{ppre, ppost, +pk, ex, il, elpre, idx,
                              _k2}:
                              Opened{open.back(elpre, node, ppre, ppost, pk, ex,
                                il), "inline table", PNil{}}
                            case _:
                              Opened{node, "not a table", PNil{}}
                        case _:
                          match focus:
                            case ZArr{ppre, ppost, +pk, ex, il, elpre, idx,
                              +k2}:
                              open.go(names, t, aot, ZArr{ppre, ppost, pk, ex,
                                il, V.VCons{h, elpre}, 1n+idx, k2})
                            case _:
                              Opened{node, "not a table", PNil{}}
                    case False{}:
                      match t:
                        case V.VNil{}:
                          match focus:
                            case ZArr{+ppre, +ppost, +pk, +ex, +il, +elpre,
                              idx, +k2}:
                              open.arr.place(open.go(names, h, aot, spot.go(ps,
                                k2, V.VNil{}, ex2, False{})), elpre, idx, ppre,
                                ppost, pk, ex, il, open.back(elpre, node, ppre,
                                ppost, pk, ex, il))
                            case _:
                              Opened{node, "not a table", PNil{}}
                        case _:
                          match focus:
                            case ZArr{ppre, ppost, +pk, ex, il, elpre, idx,
                              +k2}:
                              open.go(names, t, aot, ZArr{ppre, ppost, pk, ex,
                                il, V.VCons{h, elpre}, 1n+idx, k2})
                            case _:
                              Opened{node, "not a table", PNil{}}
                case _:
                  match t:
                    case V.VNil{}:
                      Opened{node, "not a table", PNil{}}
                    case _:
                      match focus:
                        case ZArr{ppre, ppost, +pk, ex, il, elpre, idx, +k2}:
                          open.go(names, t, aot, ZArr{ppre, ppost, pk, ex, il,
                            V.VCons{h, elpre}, 1n+idx, k2})
                        case _:
                          Opened{node, "not a table", PNil{}}
            case V.VNil{}:
              Opened{node, "array of tables", PNil{}}
            case _:
              Opened{node, "not a table", PNil{}}
        case _:
          match node:
            case V.VTab{pairs, explicit, inl}:
              match inl:
                case True{}:
                  Opened{node, "inline table", PNil{}}
                case False{}:
                  match focus:
                    case ZNone{}:
                      open.go(more, node, aot, spot.go(pairs, k, V.VNil{},
                        explicit, False{}))
                    case ZKey{gap, held, pre, post, +pk, ex, il}:
                      match gap:
                        case True{}:
                          open.place(open.go(more, V.VTab{V.VNil{}, False{},
                            False{}}, aot, spot.go(V.VNil{}, k, V.VNil{},
                            False{}, False{})), pre, post, pk, ex, il, node)
                        case False{}:
                          match held:
                            case V.VTab{+ps, +ex2, il2}:
                              match il2:
                                case True{}:
                                  Opened{node, "inline table", PNil{}}
                                case False{}:
                                  open.place(open.go(more, held, aot,
                                    spot.go(ps, k, V.VNil{}, ex2, False{})),
                                    pre, post, pk, ex, il, node)
                            case V.VArr{items, af}:
                              match af:
                                case False{}:
                                  Opened{node, "array of tables", PNil{}}
                                case True{}:
                                  open.go(more, items, aot, ZArr{pre, post, pk,
                                    ex, il, V.VNil{}, 0n, k})
                            case _:
                              Opened{node, "not a table", PNil{}}
                    case ZArr{_a, _b, _c, _d, _e, _f, _g, _h2}:
                      Opened{node, "not a table", PNil{}}
                    case ZIdx{_pre, _n, _af}:
                      Opened{node, "not a table", PNil{}}
            case V.VCons{+h, +t}:
              match h:
                case V.VTab{+ps, +ex2, il2}:
                  match il2:
                    case True{}:
                      match t:
                        case V.VNil{}:
                          match focus:
                            case ZArr{ppre, ppost, +pk, ex, il, elpre, idx,
                              _k2}:
                              Opened{open.back(elpre, node, ppre, ppost, pk, ex,
                                il), "inline table", PNil{}}
                            case _:
                              Opened{node, "not a table", PNil{}}
                        case _:
                          match focus:
                            case ZArr{ppre, ppost, +pk, ex, il, elpre, idx,
                              +k2}:
                              open.go(names, t, aot, ZArr{ppre, ppost, pk, ex,
                                il, V.VCons{h, elpre}, 1n+idx, k2})
                            case _:
                              Opened{node, "not a table", PNil{}}
                    case False{}:
                      match t:
                        case V.VNil{}:
                          match focus:
                            case ZArr{+ppre, +ppost, +pk, +ex, +il, +elpre,
                              idx, +k2}:
                              open.arr.place(open.go(names, h, aot, spot.go(ps,
                                k2, V.VNil{}, ex2, False{})), elpre, idx, ppre,
                                ppost, pk, ex, il, open.back(elpre, node, ppre,
                                ppost, pk, ex, il))
                            case _:
                              Opened{node, "not a table", PNil{}}
                        case _:
                          match focus:
                            case ZArr{ppre, ppost, +pk, ex, il, elpre, idx,
                              +k2}:
                              open.go(names, t, aot, ZArr{ppre, ppost, pk, ex,
                                il, V.VCons{h, elpre}, 1n+idx, k2})
                            case _:
                              Opened{node, "not a table", PNil{}}
                case _:
                  match t:
                    case V.VNil{}:
                      Opened{node, "not a table", PNil{}}
                    case _:
                      match focus:
                        case ZArr{ppre, ppost, +pk, ex, il, elpre, idx, +k2}:
                          open.go(names, t, aot, ZArr{ppre, ppost, pk, ex, il,
                            V.VCons{h, elpre}, 1n+idx, k2})
                        case _:
                          Opened{node, "not a table", PNil{}}
            case _:
              Opened{node, "not a table", PNil{}}

# a table rebuilt around a write, or the table it was
def put.tab(w: Wrote, pre: V.Val, post: V.Val, +k: String, explicit: Bool,
  inline: Bool, old: V.Val) -> Wrote:
  match w:
    case Wrote{n, +e}:
      Wrote{wrote.node(e, V.VTab{pair.cat(pre, k, n, post), explicit, inline},
        old), e}

# an array rebuilt around a write, or the array it was
def put.arr(w: Wrote, af: Bool, old: V.Val) -> Wrote:
  match w:
    case Wrote{n, +e}:
      Wrote{wrote.node(e, V.VArr{n, af}, old), e}

# the cell once the error is known
def put.cell.at(e: String, n: V.Val, pre: V.Val, tail: V.Val) -> Wrote:
  match e:
    case SNil{}:
      Wrote{cons.cat(pre, n, tail), ""}
    case SCon{_h, _t}:
      Wrote{V.VNil{}, e}

# the cell a write replaced, with the cells around it put back
def put.cell(w: Wrote, pre: V.Val, tail: V.Val) -> Wrote:
  match w:
    case Wrote{n, e}:
      put.cell.at(e, n, pre, tail)

# `val` written at `path` in `node`. `inl` is true while the write is inside
# an inline table. `focus` is the key already found in `node`.
def tree.put(+path: Path, +node: V.Val, +val: V.Val, +inl: Bool, focus: Work) ->
  Wrote:
  match path node inl focus:
    case PNil{} _ _ ZNone{}:
      Wrote{val, ""}
    case PCons{_step, _rest} V.VTab{_pairs, _explicit, True{}} False{} ZNone{}:
      Wrote{node, "inline table"}
    case PCons{SName{+k}, rest} V.VTab{+pairs, explicit, True{}} True{} ZNone{}:
      tree.put(rest, node, val, inl, spot.go(pairs, k, V.VNil{}, explicit, True{}))
    case PCons{SName{+k}, rest} V.VTab{+pairs, explicit, False{}} flag ZNone{}:
      tree.put(rest, node, val, flag, spot.go(pairs, k, V.VNil{}, explicit,
        False{}))
    case PCons{SIdx{n}, rest} V.VArr{items, af} flag ZNone{}:
      put.arr(tree.put(rest, items, val, flag, ZIdx{V.VNil{}, n, af}), af, node)
    case PCons{_step, _rest} _ _ ZNone{}:
      Wrote{node, "not a table"}
    case PNil{} _ _ ZKey{True{}, _held, pre, post, +pk, ex, il}:
      Wrote{V.VTab{pair.cat(pre, pk, val, post), ex, il}, ""}
    case PNil{} _ _ ZKey{False{}, _held, _pre, _post, _pk, _ex, _il}:
      Wrote{node, "duplicate key"}
    case PCons{SName{+k2}, rest} _ flag ZKey{True{}, _held, pre, post, +pk, ex,
      il}:
      put.tab(tree.put(rest, V.VTab{V.VNil{}, True{}, flag}, val, flag,
        spot.go(V.VNil{}, k2, V.VNil{}, True{}, flag)), pre, post, pk, ex, il,
        node)
    case PCons{SIdx{_n}, _rest} _ _ ZKey{True{}, _held, _pre, _post, _pk, _ex,
      _il}:
      Wrote{node, "not a table"}
    case PCons{_step, _rest} _ False{} ZKey{False{}, V.VTab{_ps, _ex2, True{}},
      _pre, _post, _pk, _ex, _il}:
      Wrote{node, "inline table"}
    case PCons{SName{+k2}, rest} _ True{} ZKey{False{},
      V.VTab{+ps, +ex2, True{}}, pre, post, +pk, ex, il}:
      put.tab(tree.put(rest, V.VTab{ps, ex2, True{}}, val, inl, spot.go(ps, k2,
        V.VNil{}, ex2, True{})), pre, post, pk, ex, il, node)
    case PCons{SIdx{_n}, _rest} _ True{} ZKey{False{}, V.VTab{_ps, _ex2,
      True{}}, _pre, _post, _pk, _ex, _il}:
      Wrote{node, "not a table"}
    case PCons{SName{+k2}, rest} _ flag ZKey{False{},
      V.VTab{+ps, +ex2, False{}}, pre, post, +pk, ex, il}:
      put.tab(tree.put(rest, V.VTab{ps, ex2, False{}}, val, flag, spot.go(ps, k2,
        V.VNil{}, ex2, False{})), pre, post, pk, ex, il, node)
    case PCons{SIdx{_n}, _rest} _ _ ZKey{False{}, V.VTab{_ps, _ex2, False{}},
      _pre, _post, _pk, _ex, _il}:
      Wrote{node, "not a table"}
    case PCons{SIdx{n}, rest} _ flag ZKey{False{}, V.VArr{+items, +af}, pre,
      post, +pk, ex, il}:
      put.tab(put.arr(tree.put(rest, items, val, flag, ZIdx{V.VNil{}, n, af}), af,
        V.VArr{items, af}), pre, post, pk, ex, il, node)
    case PCons{SName{_k2}, _rest} _ _ ZKey{False{}, V.VArr{_items, _af}, _pre,
      _post, _pk, _ex, _il}:
      Wrote{node, "not a table"}
    case PCons{_step, _rest} _ _ ZKey{False{}, _held, _pre, _post, _pk, _ex,
      _il}:
      Wrote{node, "not a table"}
    case here V.VNil{} _ ZIdx{_pre, _n, _af}:
      Wrote{node, "array of tables"}
    case here V.VCons{h, t} flag ZIdx{pre, 0n, _af}:
      put.cell(tree.put(here, h, val, flag, ZNone{}), pre, t)
    case here V.VCons{+h, +t} flag ZIdx{pre, 1n+i, af}:
      tree.put(here, t, val, flag, ZIdx{V.VCons{h, pre}, i, af})
    case _ _ _ ZIdx{_pre, _n, _af}:
      Wrote{V.VNil{}, "array of tables"}
    case _ _ _ ZArr{_a, _b, _c, _d, _e, _f, _g, _h2}:
      Wrote{node, "not a table"}
# a code point inside a closed range
def rng.u(+n: U32, +lo: U32, +hi: U32) -> Bool:
  Bool.and(U32.is_ge(n, lo), U32.is_le(n, hi))

# one digit, once the class is known
def take.dig.at(yes: Bool, +h: Char, t: List<&2, Char>) -> Take:
  match yes:
    case False{}:
      TNo{}
    case True{}:
      TYes{U32.sub(Char.to_u32(h), 48), t}

# one digit, or not
def take.dig(cs: List<&2, Char>) -> Take:
  match cs:
    case []:
      TNo{}
    case +h <> t:
      take.dig.at(Char.is_digit(h), h, t)

# the second digit of a pair
def take.two.b(t: Take, +n: U32) -> Take:
  match t:
    case TNo{}:
      TNo{}
    case TYes{m, rest}:
      TYes{U32.add(U32.mul(n, 10), m), rest}

# the first digit of a pair
def take.two.go(t: Take) -> Take:
  match t:
    case TNo{}:
      TNo{}
    case TYes{n, rest}:
      take.two.b(take.dig(rest), n)

# two digits
def take.two(cs: List<&2, Char>) -> Take:
  take.two.go(take.dig(cs))

# the low pair of four digits
def take.four.b(t: Take, +hi: U32) -> Take:
  match t:
    case TNo{}:
      TNo{}
    case TYes{lo, rest}:
      TYes{U32.add(U32.mul(hi, 100), lo), rest}

# the high pair of four digits
def take.four.go(t: Take) -> Take:
  match t:
    case TNo{}:
      TNo{}
    case TYes{hi, rest}:
      take.four.b(take.two(rest), hi)

# four digits
def take.four(cs: List<&2, Char>) -> Take:
  take.four.go(take.two(cs))

# a finished date or time
def date.done(dated: Bool, off: Bool, +raw: String) -> Dr:
  match dated off:
    case True{} True{}:
      DYes{V.VOff{raw}}
    case False{} True{}:
      DNo{}
    case True{} False{}:
      DYes{V.VLocal{raw}}
    case False{} False{}:
      DYes{V.VTime{raw}}

# `Z` only closes a date that already has a time
def date.z.ok(dated: Bool, +raw: String) -> Dr:
  match dated:
    case True{}:
      DYes{V.VOff{raw}}
    case False{}:
      DNo{}

# the chars after `Z`
def date.z(cs: List<&2, Char>, +raw: String, dated: Bool) -> Dr:
  match cs:
    case []:
      date.z.ok(dated, raw)
    case _h <> _t:
      DNo{}

# nothing after the offset minutes
def date.oend(cs: List<&2, Char>, +raw: String) -> Dr:
  match cs:
    case []:
      DYes{V.VOff{raw}}
    case _h <> _t:
      DNo{}

# the offset minutes, once they are in range
def date.om.ok(ok: Bool, rest: List<&2, Char>, +raw: String) -> Dr:
  match ok:
    case False{}:
      DNo{}
    case True{}:
      date.oend(rest, raw)

# the offset minutes
def date.om(t: Take, +raw: String) -> Dr:
  match t:
    case TNo{}:
      DNo{}
    case TYes{m, rest}:
      date.om.ok(rng.u(m, 0, 59), rest, raw)

# the colon before the offset minutes
def date.ocolon.at(yes: Bool, t: List<&2, Char>, +raw: String) -> Dr:
  match yes:
    case False{}:
      DNo{}
    case True{}:
      date.om(take.two(t), raw)

# the colon of an offset
def date.ocolon(cs: List<&2, Char>, +raw: String) -> Dr:
  match cs:
    case []:
      DNo{}
    case h <> t:
      date.ocolon.at(Char.is_eq(h, ':'), t, raw)

# the offset hour, once it is in range
def date.oh.ok(ok: Bool, rest: List<&2, Char>, +raw: String) -> Dr:
  match ok:
    case False{}:
      DNo{}
    case True{}:
      date.ocolon(rest, raw)

# the offset hour
def date.oh(t: Take, +raw: String) -> Dr:
  match t:
    case TNo{}:
      DNo{}
    case TYes{h, rest}:
      date.oh.ok(rng.u(h, 0, 23), rest, raw)

# the hour and minute after `+` or `-`
def date.osign(cs: List<&2, Char>, +raw: String, _dated: Bool) -> Dr:
  date.oh(take.two(cs), raw)

# digits of a fraction, then `Z` or an offset. `dig` means the previous
# char was a digit, so `cs` is what follows it.
def date.frac.more(cs: List<&2, Char>, dig: Bool, zee: Bool, sign: Bool,
  +raw: String, dated: Bool) -> Dr:
  match cs dig:
    case [] True{}:
      date.done(dated, False{}, raw)
    case +h <> t True{}:
      date.frac.more(t, Char.is_digit(h),
        Bool.or(Char.is_eq(h, 'Z'), Char.is_eq(h, 'z')),
        Bool.or(Char.is_eq(h, '+'), Char.is_eq(h, '-')), raw, dated)
    case [] False{}:
      match zee sign:
        case True{} _:
          date.z([], raw, dated)
        case False{} True{}:
          date.osign([], raw, dated)
        case False{} False{}:
          date.done(dated, False{}, raw)
    case h <> t False{}:
      match zee sign:
        case True{} _:
          date.z(h <> t, raw, dated)
        case False{} True{}:
          date.osign(h <> t, raw, dated)
        case False{} False{}:
          DNo{}

# a fraction needs one digit
def date.frac.go(t: Take, +raw: String, dated: Bool) -> Dr:
  match t:
    case TNo{}:
      DNo{}
    case TYes{_n, rest}:
      date.frac.more(rest, True{}, False{}, False{}, raw, dated)

# the fraction after `.`
def date.frac(cs: List<&2, Char>, +raw: String, dated: Bool) -> Dr:
  date.frac.go(take.dig(cs), raw, dated)

# `.`, `Z`, or an offset sign after the seconds
def date.tail.at(dot: Bool, zee: Bool, sign: Bool, t: List<&2, Char>,
  +raw: String, dated: Bool) -> Dr:
  match dot:
    case True{}:
      date.frac(t, raw, dated)
    case False{}:
      match zee:
        case True{}:
          date.z(t, raw, dated)
        case False{}:
          match sign:
            case True{}:
              date.osign(t, raw, dated)
            case False{}:
              DNo{}

# what follows the seconds
def date.tail(cs: List<&2, Char>, +raw: String, dated: Bool) -> Dr:
  match cs:
    case []:
      date.done(dated, False{}, raw)
    case +h <> t:
      date.tail.at(Char.is_eq(h, '.'),
        Bool.or(Char.is_eq(h, 'Z'), Char.is_eq(h, 'z')),
        Bool.or(Char.is_eq(h, '+'), Char.is_eq(h, '-')), t, raw, dated)

# the seconds, once they are in range
def date.sec.ok(ok: Bool, rest: List<&2, Char>, +raw: String, dated: Bool) ->
  Dr:
  match ok:
    case False{}:
      DNo{}
    case True{}:
      date.tail(rest, raw, dated)

# the seconds
def date.sec(t: Take, +raw: String, dated: Bool) -> Dr:
  match t:
    case TNo{}:
      DNo{}
    case TYes{n, rest}:
      date.sec.ok(rng.u(n, 0, 60), rest, raw, dated)

# the colon before the seconds
def date.scolon.at(yes: Bool, t: List<&2, Char>, +raw: String, dated: Bool) ->
  Dr:
  match yes:
    case False{}:
      DNo{}
    case True{}:
      date.sec(take.two(t), raw, dated)

# the colon of the seconds
def date.scolon(cs: List<&2, Char>, +raw: String, dated: Bool) -> Dr:
  match cs:
    case []:
      DNo{}
    case h <> t:
      date.scolon.at(Char.is_eq(h, ':'), t, raw, dated)

# the minutes, once they are in range
def date.min.ok(ok: Bool, rest: List<&2, Char>, +raw: String, dated: Bool) ->
  Dr:
  match ok:
    case False{}:
      DNo{}
    case True{}:
      date.scolon(rest, raw, dated)

# the minutes
def date.min(t: Take, +raw: String, dated: Bool) -> Dr:
  match t:
    case TNo{}:
      DNo{}
    case TYes{n, rest}:
      date.min.ok(rng.u(n, 0, 59), rest, raw, dated)

# the colon before the minutes
def date.mcolon.at(yes: Bool, t: List<&2, Char>, +raw: String, dated: Bool) ->
  Dr:
  match yes:
    case False{}:
      DNo{}
    case True{}:
      date.min(take.two(t), raw, dated)

# the colon of the minutes
def date.mcolon(cs: List<&2, Char>, +raw: String, dated: Bool) -> Dr:
  match cs:
    case []:
      DNo{}
    case h <> t:
      date.mcolon.at(Char.is_eq(h, ':'), t, raw, dated)

# the hour, once it is in range
def date.hour.ok(ok: Bool, rest: List<&2, Char>, +raw: String, dated: Bool) ->
  Dr:
  match ok:
    case False{}:
      DNo{}
    case True{}:
      date.mcolon(rest, raw, dated)

# the hour
def date.hour(t: Take, +raw: String, dated: Bool) -> Dr:
  match t:
    case TNo{}:
      DNo{}
    case TYes{n, rest}:
      date.hour.ok(rng.u(n, 0, 23), rest, raw, dated)

# a time, `dated` when a date was written in front of it
def date.time(cs: List<&2, Char>, +raw: String, dated: Bool) -> Dr:
  date.hour(take.two(cs), raw, dated)

# `T`, `t`, or a space between a date and a time
def date.sep.at(yes: Bool, t: List<&2, Char>, +raw: String) -> Dr:
  match yes:
    case False{}:
      DNo{}
    case True{}:
      date.time(t, raw, True{})

# the separator, or the end of a local date
def date.after(cs: List<&2, Char>, +raw: String) -> Dr:
  match cs:
    case []:
      DYes{V.VDay{raw}}
    case +h <> t:
      date.sep.at(Bool.or(Char.is_eq(h, 'T'),
        Bool.or(Char.is_eq(h, 't'), Char.is_eq(h, ' '))), t, raw)

# the day, once it is in range
def date.day.ok(ok: Bool, rest: List<&2, Char>, +raw: String) -> Dr:
  match ok:
    case False{}:
      DNo{}
    case True{}:
      date.after(rest, raw)

# the day
def date.day(t: Take, +raw: String) -> Dr:
  match t:
    case TNo{}:
      DNo{}
    case TYes{n, rest}:
      date.day.ok(rng.u(n, 1, 31), rest, raw)

# the dash before the day
def date.ddash.at(yes: Bool, t: List<&2, Char>, +raw: String) -> Dr:
  match yes:
    case False{}:
      DNo{}
    case True{}:
      date.day(take.two(t), raw)

# the dash of the day
def date.ddash(cs: List<&2, Char>, +raw: String) -> Dr:
  match cs:
    case []:
      DNo{}
    case h <> t:
      date.ddash.at(Char.is_eq(h, '-'), t, raw)

# the month, once it is in range
def date.month.ok(ok: Bool, rest: List<&2, Char>, +raw: String) -> Dr:
  match ok:
    case False{}:
      DNo{}
    case True{}:
      date.ddash(rest, raw)

# the month
def date.month(t: Take, +raw: String) -> Dr:
  match t:
    case TNo{}:
      DNo{}
    case TYes{n, rest}:
      date.month.ok(rng.u(n, 1, 12), rest, raw)

# the dash before the month
def date.mdash.at(yes: Bool, t: List<&2, Char>, +raw: String) -> Dr:
  match yes:
    case False{}:
      DNo{}
    case True{}:
      date.month(take.two(t), raw)

# the dash of the month
def date.mdash(cs: List<&2, Char>, +raw: String) -> Dr:
  match cs:
    case []:
      DNo{}
    case h <> t:
      date.mdash.at(Char.is_eq(h, '-'), t, raw)

# the year
def date.year(t: Take, +raw: String) -> Dr:
  match t:
    case TNo{}:
      DNo{}
    case TYes{_n, rest}:
      date.mdash(rest, raw)

# a local date, a local datetime, or an offset datetime
def date.full(cs: List<&2, Char>, +raw: String) -> Dr:
  date.year(take.four(cs), raw)

# a local time
def date.only(cs: List<&2, Char>, +raw: String) -> Dr:
  date.time(cs, raw, False{})

# the positive i64 limit, as digits
def rng.pos() -> String:
  "9223372036854775807"

# the negative i64 limit, as digits
def rng.neg() -> String:
  "9223372036854775808"

# one leading `+` dropped
def plus.drop.at(yes: Bool, h: Char, t: String) -> String:
  match yes:
    case True{}:
      t
    case False{}:
      SCon{h, t}

# the text with one leading `+` dropped
def plus.drop(s: String) -> String:
  match s:
    case SNil{}:
      s
    case SCon{+h, t}:
      plus.drop.at(Char.is_eq(h, '+'), h, t)

# one leading `+` or `-` skipped, for the base
def plus.skip.at(yes: Bool, h: Char, t: String) -> String:
  match yes:
    case True{}:
      t
    case False{}:
      SCon{h, t}

# the text after one leading sign
def plus.skip(s: String) -> String:
  match s:
    case SNil{}:
      s
    case SCon{+h, t}:
      plus.skip.at(Bool.or(Char.is_eq(h, '+'), Char.is_eq(h, '-')), h, t)

# the base mark after a leading zero
def us.base.p(+x: U32) -> Uk:
  Bool.pick(Uk, Bool.or(U32.is_eq(x, 120), U32.is_eq(x, 88)), UkHex{},
  Bool.pick(Uk, Bool.or(U32.is_eq(x, 111), U32.is_eq(x, 79)), UkOct{},
  Bool.pick(Uk, Bool.or(U32.is_eq(x, 98), U32.is_eq(x, 66)), UkBin{},
    UkDec{})))

# the base a leading zero announces
def us.base.z(z: Bool, t: String) -> Uk:
  match z:
    case False{}:
      UkDec{}
    case True{}:
      match t:
        case SNil{}:
          UkDec{}
        case SCon{h, _r}:
          us.base.p(Char.to_u32(h))

# the base of a number
def us.base.go(s: String) -> Uk:
  match s:
    case SNil{}:
      UkDec{}
    case SCon{h, t}:
      us.base.z(Char.is_eq(h, '0'), t)

# the base, after one optional sign
def us.base(s: String) -> Uk:
  us.base.go(plus.skip(s))

# a decimal digit
def us.dec(+x: U32) -> Bool:
  Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57))

# a hex digit
def us.hex(+x: U32) -> Bool:
  Bool.or(us.dec(x), Bool.or(Bool.and(U32.is_ge(x, 97), U32.is_le(x, 102)),
    Bool.and(U32.is_ge(x, 65), U32.is_le(x, 70))))

# an octal digit
def us.oct(+x: U32) -> Bool:
  Bool.and(U32.is_ge(x, 48), U32.is_le(x, 55))

# a binary digit
def us.bin(+x: U32) -> Bool:
  Bool.or(U32.is_eq(x, 48), U32.is_eq(x, 49))

# a digit of this base
def us.dig(uk: Uk, +x: U32) -> Bool:
  match uk:
    case UkDec{}:
      us.dec(x)
    case UkHex{}:
      us.hex(x)
    case UkOct{}:
      us.oct(x)
    case UkBin{}:
      us.bin(x)

# the walk after an underscore or another char
def us.step.c(st: Us, under: Bool, dig: Bool) -> Us:
  match st under:
    case UsDig{} True{}:
      UsUnder{}
    case _ True{}:
      UsBad{}
    case _ False{}:
      match dig:
        case True{}:
          UsDig{}
        case False{}:
          UsNone{}

# one char of an underscore walk
def us.step(st: Us, uk: Uk, +c: Char) -> Us:
  match st:
    case UsBad{}:
      UsBad{}
    case _:
      us.step.c(st, Char.is_eq(c, '_'), us.dig(uk, Char.to_u32(c)))

# the walk at the end of the text
def us.done(st: Us) -> Bool:
  match st:
    case UsBad{}:
      False{}
    case UsUnder{}:
      False{}
    case _:
      True{}

# whether every underscore sits between digits
def us.scan(cs: List<&2, Char>, +uk: Uk, st: Us) -> Bool:
  match cs:
    case []:
      us.done(st)
    case h <> t:
      us.scan(t, uk, us.step(st, uk, h))

# a char kept, or an underscore dropped
def us.drop.c(u: Bool, h: Char, acc: List<&2, Char>) -> List<&2, Char>:
  match u:
    case True{}:
      acc
    case False{}:
      h <> acc

# the chars with underscores dropped, reversed
def us.drop(cs: List<&2, Char>, acc: List<&2, Char>) -> List<&2, Char>:
  match cs:
    case []:
      acc
    case +h <> t:
      us.drop(t, us.drop.c(Char.is_eq(h, '_'), h, acc))

# the text with underscores dropped
def us.clean(s: String) -> String:
  String.from_list(List.reverse(&2, Char, us.drop(String.to_list(s), [])))

# the digits of a decimal, without its sign
def rng.dec.sign(neg: Bool, h: Char, t: String) -> String:
  match neg:
    case True{}:
      t
    case False{}:
      SCon{h, t}

# the digits a decimal compares
def rng.dec.body(s: String) -> String:
  match s:
    case SNil{}:
      s
    case SCon{+h, t}:
      rng.dec.sign(Char.is_eq(h, '-'), h, t)

# a 19-digit decimal against the signed limit
def rng.lim(digits: String, neg: Bool) -> Bool:
  match neg:
    case True{}:
      String.is_le(digits, rng.neg())
    case False{}:
      String.is_le(digits, rng.pos())

# a decimal whose length is known
def rng.dec.len(short: Bool, exact: Bool, digits: String, neg: Bool) -> Bool:
  match short:
    case True{}:
      True{}
    case False{}:
      match exact:
        case True{}:
          rng.lim(digits, neg)
        case False{}:
          False{}

# a non-empty run of digits
def rng.dec.digits(+digits: String, neg: Bool) -> Bool:
  rng.dec.len(Nat.is_le(String.length(digits), 18n),
    Nat.is_eq(String.length(digits), 19n), digits, neg)

# an empty digit run is not an integer
def rng.dec.at(empty: Bool, digits: String, neg: Bool) -> Bool:
  match empty:
    case True{}:
      False{}
    case False{}:
      rng.dec.digits(digits, neg)

# a decimal integer inside signed 64-bit range
def rng.dec(+s: String) -> Bool:
  +digits = rng.dec.body(s)
  rng.dec.at(String.is_empty(digits), digits, Bool.not(String.eq(digits, s)))

# the digits after leading zeros. `drop` keeps going while it is true.
def rng.zdrop(s: String, drop: Bool) -> String:
  match s drop:
    case SNil{} _:
      s
    case SCon{'0', t} True{}:
      rng.zdrop(t, True{})
    case SCon{_h, _t} _:
      s

# a hex body of sixteen digits starts at `7` or below
def rng.hex.first(b: String) -> Bool:
  match b:
    case SNil{}:
      False{}
    case SCon{h, _t}:
      U32.is_le(Char.to_u32(h), 55)

# a hex body whose length is known
def rng.hex.n(short: Bool, exact: Bool, b: String) -> Bool:
  match short:
    case True{}:
      True{}
    case False{}:
      match exact:
        case True{}:
          rng.hex.first(b)
        case False{}:
          False{}

# a hex body inside signed 64-bit range. Empty is zero.
def rng.hex.body(+b: String) -> Bool:
  match b:
    case SNil{}:
      True{}
    case SCon{_h, _t}:
      rng.hex.n(Nat.is_le(String.length(b), 15n),
        Nat.is_eq(String.length(b), 16n), b)

# a hex integer inside signed 64-bit range
def rng.hex(s: String) -> Bool:
  rng.hex.body(rng.zdrop(String.drop(s, 2n), True{}))

# an octal or binary body whose length fits
def rng.fit(b: String, +lim: Nat) -> Bool:
  match b:
    case SNil{}:
      True{}
    case SCon{_h, _t}:
      Nat.is_le(String.length(b), lim)

# an octal integer inside signed 64-bit range
def rng.oct(s: String) -> Bool:
  rng.fit(rng.zdrop(String.drop(s, 2n), True{}), 21n)

# a binary integer inside signed 64-bit range
def rng.bin(s: String) -> Bool:
  rng.fit(rng.zdrop(String.drop(s, 2n), True{}), 63n)

# `+` `-` `.` `e` `x` `o` `b` or a digit
def num.cls(+x: U32) -> Nc:
  Bool.pick(Nc, U32.is_eq(x, 43), CPlus{},
  Bool.pick(Nc, U32.is_eq(x, 45), CMinus{},
  Bool.pick(Nc, U32.is_eq(x, 48), CZero{},
  Bool.pick(Nc, Bool.and(U32.is_ge(x, 49), U32.is_le(x, 55)), C17{},
  Bool.pick(Nc, Bool.or(U32.is_eq(x, 56), U32.is_eq(x, 57)), C89{},
  Bool.pick(Nc, U32.is_eq(x, 46), CDot{},
  Bool.pick(Nc, Bool.or(U32.is_eq(x, 101), U32.is_eq(x, 69)), CE{},
  Bool.pick(Nc, Bool.or(U32.is_eq(x, 120), U32.is_eq(x, 88)), CX{},
  Bool.pick(Nc, Bool.or(U32.is_eq(x, 111), U32.is_eq(x, 79)), CO{},
  Bool.pick(Nc, Bool.or(U32.is_eq(x, 98), U32.is_eq(x, 66)), CB{},
  Bool.pick(Nc, Bool.or(Bool.and(U32.is_ge(x, 97), U32.is_le(x, 102)),
    Bool.and(U32.is_ge(x, 65), U32.is_le(x, 70))), CHex{},
    CBad{})))))))))))

# the first char of a number
def num.from0(cls: Nc) -> Ns:
  match cls:
    case CPlus{}:
      NsSign{}
    case CMinus{}:
      NsSign{}
    case CZero{}:
      NsZ{}
    case C17{}:
      NsD{}
    case C89{}:
      NsD{}
    case _:
      NsBad{}

# a digit after a sign
def num.from.sign(cls: Nc) -> Ns:
  match cls:
    case CZero{}:
      NsZS{}
    case C17{}:
      NsD{}
    case C89{}:
      NsD{}
    case _:
      NsBad{}

# a char after a bare zero
def num.from.z(cls: Nc) -> Ns:
  match cls:
    case CX{}:
      NsX{}
    case CO{}:
      NsO{}
    case CB{}:
      NsB{}
    case CDot{}:
      NsDot{}
    case CE{}:
      NsE{}
    case _:
      NsBad{}

# a char after a signed zero
def num.from.zs(cls: Nc) -> Ns:
  match cls:
    case CDot{}:
      NsDot{}
    case CE{}:
      NsE{}
    case _:
      NsBad{}

# a char after a decimal digit
def num.from.d(cls: Nc) -> Ns:
  match cls:
    case CZero{}:
      NsD{}
    case C17{}:
      NsD{}
    case C89{}:
      NsD{}
    case CDot{}:
      NsDot{}
    case CE{}:
      NsE{}
    case _:
      NsBad{}

# a digit after a dot
def num.from.dot(cls: Nc) -> Ns:
  match cls:
    case CZero{}:
      NsF{}
    case C17{}:
      NsF{}
    case C89{}:
      NsF{}
    case _:
      NsBad{}

# a char after a fraction digit
def num.from.f(cls: Nc) -> Ns:
  match cls:
    case CZero{}:
      NsF{}
    case C17{}:
      NsF{}
    case C89{}:
      NsF{}
    case CE{}:
      NsE{}
    case _:
      NsBad{}

# a char after `e`
def num.from.e(cls: Nc) -> Ns:
  match cls:
    case CPlus{}:
      NsEs{}
    case CMinus{}:
      NsEs{}
    case CZero{}:
      NsEd{}
    case C17{}:
      NsEd{}
    case C89{}:
      NsEd{}
    case _:
      NsBad{}

# a digit after an exponent sign
def num.from.es(cls: Nc) -> Ns:
  match cls:
    case CZero{}:
      NsEd{}
    case C17{}:
      NsEd{}
    case C89{}:
      NsEd{}
    case _:
      NsBad{}

# a digit after an exponent digit
def num.from.ed(cls: Nc) -> Ns:
  num.from.es(cls)

# a hex digit
def num.hexd(cls: Nc) -> Bool:
  match cls:
    case CZero{}:
      True{}
    case C17{}:
      True{}
    case C89{}:
      True{}
    case CE{}:
      True{}
    case CX{}:
      True{}
    case CO{}:
      True{}
    case CB{}:
      True{}
    case CHex{}:
      True{}
    case _:
      False{}

# a char of a hex integer
def num.from.hex(cls: Nc) -> Ns:
  match cls:
    case CZero{}:
      NsXd{}
    case C17{}:
      NsXd{}
    case C89{}:
      NsXd{}
    case CE{}:
      NsXd{}
    case CX{}:
      NsXd{}
    case CO{}:
      NsXd{}
    case CB{}:
      NsXd{}
    case CHex{}:
      NsXd{}
    case _:
      NsBad{}

# a char of an octal integer
def num.from.oct(cls: Nc) -> Ns:
  match cls:
    case CZero{}:
      NsOd{}
    case C17{}:
      NsOd{}
    case _:
      NsBad{}

# `0` or `1`
def num.from.bin.at(ok: Bool) -> Ns:
  match ok:
    case True{}:
      NsBd{}
    case False{}:
      NsBad{}

# a char of a binary integer
def num.from.bin(+x: U32) -> Ns:
  num.from.bin.at(Bool.or(U32.is_eq(x, 48), U32.is_eq(x, 49)))

# one char of a number
def num.step(st: Ns, cls: Nc, +x: U32) -> Ns:
  match st:
    case Ns0{}:
      num.from0(cls)
    case NsSign{}:
      num.from.sign(cls)
    case NsZ{}:
      num.from.z(cls)
    case NsZS{}:
      num.from.zs(cls)
    case NsD{}:
      num.from.d(cls)
    case NsDot{}:
      num.from.dot(cls)
    case NsF{}:
      num.from.f(cls)
    case NsE{}:
      num.from.e(cls)
    case NsEs{}:
      num.from.es(cls)
    case NsEd{}:
      num.from.ed(cls)
    case NsX{}:
      num.from.hex(cls)
    case NsXd{}:
      num.from.hex(cls)
    case NsO{}:
      num.from.oct(cls)
    case NsOd{}:
      num.from.oct(cls)
    case NsB{}:
      num.from.bin(x)
    case NsBd{}:
      num.from.bin(x)
    case NsBad{}:
      NsBad{}

# one char, classified
def num.feed(st: Ns, +c: Char) -> Ns:
  +x = Char.to_u32(c)
  num.step(st, num.cls(x), x)

# every char of a number
def num.run(cs: List<&2, Char>, st: Ns) -> Ns:
  match cs:
    case []:
      st
    case h <> t:
      num.run(t, num.feed(st, h))

# an integer the range accepted
def num.int.ok(ok: Bool, s: String) -> Lit:
  match ok:
    case True{}:
      LOk{V.VInt{s}}
    case False{}:
      LBad{"integer"}

# a decimal integer
def num.int(+s: String) -> Lit:
  num.int.ok(rng.dec(s), s)

# a hex integer
def num.hex(+s: String) -> Lit:
  num.int.ok(rng.hex(s), s)

# an octal integer
def num.oct(+s: String) -> Lit:
  num.int.ok(rng.oct(s), s)

# a binary integer
def num.bin(+s: String) -> Lit:
  num.int.ok(rng.bin(s), s)

# a number whose shape is known
def num.fin(st: Ns, +s: String) -> Lit:
  match st:
    case NsZ{}:
      num.int(plus.drop(s))
    case NsZS{}:
      num.int(plus.drop(s))
    case NsD{}:
      num.int(plus.drop(s))
    case NsF{}:
      LOk{V.VFloat{plus.drop(s)}}
    case NsEd{}:
      LOk{V.VFloat{plus.drop(s)}}
    case NsXd{}:
      num.hex(s)
    case NsOd{}:
      num.oct(s)
    case NsBd{}:
      num.bin(s)
    case _:
      LBad{"integer"}

# a number
def num.of(+s: String) -> Lit:
  num.fin(num.run(String.to_list(s), Ns0{}), s)

# `-nan`
def lit.word.nnan(yes: Bool, +s: String) -> Hit:
  match yes:
    case True{}:
      HYes{V.VFloat{s}}
    case False{}:
      HNo{}

# `+nan`
def lit.word.pnan(yes: Bool, +s: String) -> Hit:
  match yes:
    case True{}:
      HYes{V.VFloat{s}}
    case False{}:
      lit.word.nnan(String.eq(s, "-nan"), s)

# `nan`
def lit.word.nan(yes: Bool, +s: String) -> Hit:
  match yes:
    case True{}:
      HYes{V.VFloat{s}}
    case False{}:
      lit.word.pnan(String.eq(s, "+nan"), s)

# `-inf`
def lit.word.ninf(yes: Bool, +s: String) -> Hit:
  match yes:
    case True{}:
      HYes{V.VFloat{s}}
    case False{}:
      lit.word.nan(String.eq(s, "nan"), s)

# `+inf`
def lit.word.pinf(yes: Bool, +s: String) -> Hit:
  match yes:
    case True{}:
      HYes{V.VFloat{s}}
    case False{}:
      lit.word.ninf(String.eq(s, "-inf"), s)

# `inf`
def lit.word.inf(yes: Bool, +s: String) -> Hit:
  match yes:
    case True{}:
      HYes{V.VFloat{s}}
    case False{}:
      lit.word.pinf(String.eq(s, "+inf"), s)

# `false`
def lit.word.false(yes: Bool, +s: String) -> Hit:
  match yes:
    case True{}:
      HYes{V.VBool{False{}}}
    case False{}:
      lit.word.inf(String.eq(s, "inf"), s)

# `true`
def lit.word.true(yes: Bool, +s: String) -> Hit:
  match yes:
    case True{}:
      HYes{V.VBool{True{}}}
    case False{}:
      lit.word.false(String.eq(s, "false"), s)

# `true`, `false`, `inf`, or `nan`
def lit.word(+s: String) -> Hit:
  lit.word.true(String.eq(s, "true"), s)

# a date if one was read, otherwise a number. A colon is not a number.
def lit.of.when(full: Dr, only: Dr, colon: Bool, +clean: String) -> Lit:
  match full:
    case DYes{v}:
      LOk{v}
    case DNo{}:
      match only:
        case DYes{v}:
          LOk{v}
        case DNo{}:
          match colon:
            case True{}:
              LBad{"value"}
            case False{}:
              num.of(clean)

# a date or a time when the text holds `-` or `:`, otherwise a number
def lit.of.clean(+clean: String) -> Lit:
  lit.of.when(date.full(String.to_list(clean), clean),
    date.only(String.to_list(clean), clean), String.contains(clean, ":"),
    clean)

# the text once underscores are known to be placed
def lit.of.us(ok: Bool, +s: String) -> Lit:
  match ok:
    case False{}:
      LBad{"underscore"}
    case True{}:
      lit.of.clean(us.clean(s))

# a literal after keywords
def lit.of.word(h: Hit, +s: String) -> Lit:
  match h:
    case HYes{v}:
      LOk{v}
    case HNo{}:
      lit.of.us(us.scan(String.to_list(s), us.base(s), UsNone{}), s)

# a bare word read as a value
def lit.of(+s: String) -> Lit:
  lit.of.word(lit.word(s), s)
# the state with its error replaced by `why` when it had none
def step.bad(st: St, why: String) -> St:
  match st:
    case St{err, rt, cur, _mode, _names, _part, _stack, _aot}:
      St{err.keep(err, why), rt, cur, MTop{}, NNil{}, "", KNil{}, False{}}

# a key segment accepted
def step.kstr(err: String, rt: V.Val, cur: Path, names: Nm, stack: Sk,
  +s: String, mode: Pm) -> St:
  St{err, rt, cur, mode, nm.snoc(names, s), "", stack, False{}}

# a bare key segment, when it is one
def step.kbare(ok: Bool, err: String, rt: V.Val, cur: Path, names: Nm,
  stack: Sk, +s: String, mode: Pm) -> St:
  match ok:
    case True{}:
      step.kstr(err, rt, cur, names, stack, s, mode)
    case False{}:
      St{err.keep(err, "key"), rt, cur, MTop{}, NNil{}, "", KNil{}, False{}}

# a header whose error is known
def step.head.go(ok: Bool, n: V.Val, e: String, c: Path, err: String,
  rt: V.Val, cur: Path) -> St:
  match ok:
    case True{}:
      St{err, n, c, MTop{}, NNil{}, "", KNil{}, False{}}
    case False{}:
      St{err.keep(err, e), rt, cur, MTop{}, NNil{}, "", KNil{}, False{}}

# a header applied to the fields it was read in
def step.head.at(ok: Bool, n: V.Val, +e: String, c: Path, st: St) -> St:
  match st:
    case St{err, rt, cur, _mode, _names, _part, _stack, _aot}:
      step.head.go(ok, n, e, c, err, rt, cur)

# a header applied to the document
def step.head.use(o: Opened, st: St) -> St:
  match o:
    case Opened{n, +e, c}:
      step.head.at(String.is_empty(e), n, e, c, st)

# a header closed
def step.finish(st: St) -> St:
  match st:
    case St{_err, +rt, _cur, _mode, +names, _part, _stack, +aot}:
      step.head.use(open.go(names, rt, aot, ZNone{}), st)

# `]` of a header. The second `]` of `[[table]]` is still to come when `aot`.
def step.head.close(aot: Bool, st: St) -> St:
  match aot st:
    case True{} St{err, rt, cur, _mode, names, part, stack, _aot}:
      St{err, rt, cur, MEnd{}, names, part, stack, True{}}
    case False{} _:
      step.finish(st)

# a value written at the current key
def land.root.at(ok: Bool, n: V.Val, e: String, err: String, rt: V.Val,
  cur: Path) -> St:
  match ok:
    case True{}:
      St{err, n, cur, MTop{}, NNil{}, "", KNil{}, False{}}
    case False{}:
      St{err.keep(err, e), rt, cur, MTop{}, NNil{}, "", KNil{}, False{}}

# a value written into the root
def land.root(w: Wrote, err: String, rt: V.Val, cur: Path) -> St:
  match w:
    case Wrote{n, +e}:
      land.root.at(String.is_empty(e), n, e, err, rt, cur)

# an inline pair written
def land.inl.at(n: V.Val, e: String, rest: Sk, err: String, rt: V.Val,
  cur: Path) -> St:
  match n:
    case V.VTab{pairs, _explicit, _inline}:
      St{err.keep(err, e), rt, cur, MInlSep{}, NNil{}, "",
        KCons{FInl{pairs, NNil{}, WSep{}}, rest}, False{}}
    case _:
      St{err.keep(err, e), rt, cur, MTop{}, NNil{}, "", KNil{}, False{}}

# an inline pair, once the write is known
def land.inl.put(w: Wrote, rest: Sk, err: String, rt: V.Val, cur: Path) -> St:
  match w:
    case Wrote{n, e}:
      land.inl.at(n, e, rest, err, rt, cur)

# an inline table waiting for a value takes it
def land.inl(want: Want, pairs: V.Val, kn: Nm, rest: Sk, v: V.Val, err: String,
  rt: V.Val, cur: Path) -> St:
  match want:
    case WVal{}:
      land.inl.put(tree.put(nm.path(kn), V.VTab{pairs, True{}, True{}}, v, True{},
        ZNone{}), rest, err, rt, cur)
    case _:
      St{err.keep(err, "value"), rt, cur, MTop{}, NNil{}, "", KNil{}, False{}}

# a finished value. A key with no name is an error.
def step.land(stack: Sk, v: V.Val, err: String, +rt: V.Val, +cur: Path, names: Nm) ->
  St:
  match stack names:
    case KNil{} NNil{}:
      St{err.keep(err, "key"), rt, cur, MTop{}, NNil{}, "", KNil{}, False{}}
    case KNil{} _:
      land.root(tree.put(path.cat(cur, nm.path(names)), rt, v, False{}, ZNone{}),
        err, rt, cur)
    case KCons{FHold{hn, hc}, rest} _:
      step.land(rest, v, err, rt, hc, hn)
    case KCons{FArr{items}, rest} _:
      St{err, rt, cur, MArrSep{}, NNil{}, "",
        KCons{FArr{val.snoc(items, v)}, rest}, False{}}
    case KCons{FInl{pairs, kn, want}, rest} _:
      land.inl(want, pairs, kn, rest, v, err, rt, cur)

# the key a container was opened under, kept when the container is the value
def step.hold(stack: Sk, names: Nm, cur: Path) -> Sk:
  match stack:
    case KNil{}:
      KCons{FHold{names, cur}, KNil{}}
    case _:
      stack

# an array opened
def step.push.arr(stack: Sk, names: Nm, cur: Path) -> Sk:
  KCons{FArr{V.VNil{}}, step.hold(stack, names, cur)}

# an inline table opened
def step.push.inl(stack: Sk, names: Nm, cur: Path) -> Sk:
  KCons{FInl{V.VNil{}, NNil{}, WKey{}}, step.hold(stack, names, cur)}

# a newline inside an inline table
def step.nl.bad(stack: Sk) -> Bool:
  match stack:
    case KCons{FInl{_pairs, _names, _want}, _rest}:
      True{}
    case _:
      False{}

# a newline while a value is open
def step.read.nl.at(bad: Bool, err: String, rt: V.Val, cur: Path, mode: Pm,
  names: Nm, part: String, stack: Sk, aot: Bool) -> St:
  match bad:
    case True{}:
      St{err.keep(err, "newline"), rt, cur, MTop{}, NNil{}, "", KNil{},
        False{}}
    case False{}:
      St{err, rt, cur, mode, names, part, stack, aot}

# a newline, rejected inside an inline table
def step.read.nl(st: St) -> St:
  match st:
    case St{err, rt, cur, mode, names, part, +stack, aot}:
      step.read.nl.at(step.nl.bad(stack), err, rt, cur, mode, names, part,
        stack, aot)

# a literal landed, or its error kept
def step.land.lit(lit: Lit, err: String, rt: V.Val, cur: Path, names: Nm,
  stack: Sk) -> St:
  match lit:
    case LOk{v}:
      step.land(stack, v, err, rt, cur, names)
    case LBad{why}:
      St{err.keep(err, why), rt, cur, MTop{}, NNil{}, "", KNil{}, False{}}

# an array closed
def step.close.arr(st: St) -> St:
  match st:
    case St{err, rt, cur, _mode, _names, _part, stack, _aot}:
      match stack:
        case KCons{FArr{items}, rest}:
          step.land(rest, V.VArr{items, False{}}, err, rt, cur, NNil{})
        case _:
          St{err.keep(err, "value"), rt, cur, MTop{}, NNil{}, "", KNil{},
            False{}}

# an inline table closed
def step.close.inl(st: St) -> St:
  match st:
    case St{err, rt, cur, _mode, _names, _part, stack, _aot}:
      match stack:
        case KCons{FInl{pairs, _kn, _want}, rest}:
          step.land(rest, V.VTab{pairs, True{}, True{}}, err, rt, cur, NNil{})
        case _:
          St{err.keep(err, "value"), rt, cur, MTop{}, NNil{}, "", KNil{},
            False{}}

# `=` inside an inline table stores the key it follows
def step.inl.eq(st: St) -> St:
  match st:
    case St{err, rt, cur, _mode, names, _part, stack, _aot}:
      match stack:
        case KCons{FInl{pairs, _kn, _want}, rest}:
          St{err, rt, cur, MVal{}, NNil{}, "",
            KCons{FInl{pairs, names, WVal{}}, rest}, False{}}
        case _:
          St{err.keep(err, "value"), rt, cur, MTop{}, NNil{}, "", KNil{},
            False{}}

# a value token: a string, a bare word, an array, or an inline table
def step.read(st: St, tok: L.Tok) -> St:
  match st tok:
    case s L.TNl{}:
      step.read.nl(s)
    case St{err, rt, +cur, _m, names, _p, stack, _a} L.TStr{s}:
      step.land(stack, V.VStr{s}, err, rt, cur, names)
    case St{err, rt, cur, _m, names, _p, stack, _a} L.TBare{s}:
      St{err, rt, cur, MPart{}, names, s, stack, False{}}
    case St{err, rt, cur, _m, names, _p, stack, _a} L.TLBr{}:
      St{err, rt, cur, MArr{}, NNil{}, "", step.push.arr(stack, names, cur),
        False{}}
    case St{err, rt, cur, _m, names, _p, stack, _a} L.TLBc{}:
      St{err, rt, cur, MInl{}, NNil{}, "", step.push.inl(stack, names, cur),
        False{}}
    case St{err, rt, cur, _m, _n, _p, _s, _a} L.TBad{why}:
      St{err.keep(err, why), rt, cur, MTop{}, NNil{}, "", KNil{}, False{}}
    case St{err, rt, cur, _m, _n, _p, _s, _a} _:
      St{err.keep(err, "value"), rt, cur, MTop{}, NNil{}, "", KNil{}, False{}}

# a key segment at the top of a document
def step.top(st: St, tok: L.Tok) -> St:
  match st tok:
    case s L.TNl{}:
      s
    case St{err, rt, cur, _m, names, _p, stack, _a} L.TStr{s}:
      step.kstr(err, rt, cur, names, stack, s, MSeg{})
    case St{err, rt, cur, _m, names, _p, stack, _a} L.TBare{+s}:
      step.kbare(Txt.bare(s), err, rt, cur, names, stack, s, MSeg{})
    case St{err, rt, cur, _m, _n, _p, stack, _a} L.TLBr{}:
      St{err, rt, cur, MBrack{}, NNil{}, "", stack, False{}}
    case St{err, rt, cur, _m, _n, _p, _s, _a} L.TBad{why}:
      St{err.keep(err, why), rt, cur, MTop{}, NNil{}, "", KNil{}, False{}}
    case St{err, rt, cur, _m, _n, _p, _s, _a} _:
      St{err.keep(err, "key"), rt, cur, MTop{}, NNil{}, "", KNil{}, False{}}

# the segment after a dot
def step.key(st: St, tok: L.Tok) -> St:
  match st tok:
    case s L.TNl{}:
      s
    case St{err, rt, cur, _m, names, _p, stack, _a} L.TStr{s}:
      step.kstr(err, rt, cur, names, stack, s, MSeg{})
    case St{err, rt, cur, _m, names, _p, stack, _a} L.TBare{+s}:
      step.kbare(Txt.bare(s), err, rt, cur, names, stack, s, MSeg{})
    case St{err, rt, cur, _m, _n, _p, _s, _a} L.TBad{why}:
      St{err.keep(err, why), rt, cur, MTop{}, NNil{}, "", KNil{}, False{}}
    case St{err, rt, cur, _m, _n, _p, _s, _a} _:
      St{err.keep(err, "key"), rt, cur, MTop{}, NNil{}, "", KNil{}, False{}}

# a dot or `=` after a key
def step.seg(st: St, tok: L.Tok) -> St:
  match st tok:
    case s L.TNl{}:
      s
    case St{err, rt, cur, _m, names, _p, stack, _a} L.TDot{}:
      St{err, rt, cur, MKey{}, names, "", stack, False{}}
    case St{err, rt, cur, _m, names, _p, stack, _a} L.TEq{}:
      St{err, rt, cur, MVal{}, names, "", stack, False{}}
    case St{err, rt, cur, _m, _n, _p, _s, _a} L.TBad{why}:
      St{err.keep(err, why), rt, cur, MTop{}, NNil{}, "", KNil{}, False{}}
    case St{err, rt, cur, _m, _n, _p, _s, _a} _:
      St{err.keep(err, "key"), rt, cur, MTop{}, NNil{}, "", KNil{}, False{}}

# `[` of a header, or the key that follows one `[`
def step.brack(st: St, tok: L.Tok) -> St:
  match st tok:
    case s L.TNl{}:
      s
    case St{err, rt, cur, _m, _n, _p, stack, _a} L.TLBr{}:
      St{err, rt, cur, MHead{}, NNil{}, "", stack, True{}}
    case St{err, rt, cur, _m, names, _p, stack, _a} L.TStr{s}:
      step.kstr(err, rt, cur, names, stack, s, MHead{})
    case St{err, rt, cur, _m, names, _p, stack, _a} L.TBare{+s}:
      step.kbare(Txt.bare(s), err, rt, cur, names, stack, s, MHead{})
    case St{err, rt, cur, _m, _n, _p, _s, _a} L.TBad{why}:
      St{err.keep(err, why), rt, cur, MTop{}, NNil{}, "", KNil{}, False{}}
    case St{err, rt, cur, _m, _n, _p, _s, _a} _:
      St{err.keep(err, "key"), rt, cur, MTop{}, NNil{}, "", KNil{}, False{}}

# a bare header segment, keeping the array-of-tables bit
def step.hbare(ok: Bool, err: String, rt: V.Val, cur: Path, names: Nm,
  stack: Sk, +s: String, aot: Bool) -> St:
  match ok:
    case True{}:
      St{err, rt, cur, MHead{}, nm.snoc(names, s), "", stack, aot}
    case False{}:
      St{err.keep(err, "key"), rt, cur, MTop{}, NNil{}, "", KNil{}, False{}}

# `]` read out of a header state
def step.head.br(st: St) -> St:
  match st:
    case St{_err, _rt, _cur, _mode, _names, _part, _stack, +aot}:
      step.head.close(aot, st)

# that segment, once a quoted one is known to be legal
def step.head.first.ok(bare: Bool, err: String, rt: V.Val, cur: Path, stack: Sk,
  +s: String, aot: Bool) -> St:
  match bare:
    case True{}:
      step.hbare(True{}, err, rt, cur, NNil{}, stack, s, aot)
    case False{}:
      St{err.keep(err, "key"), rt, cur, MTop{}, NNil{}, "", KNil{}, False{}}

# the first segment of `[[table]]`, which arrives with no name yet
def step.head.first(names: Nm, err: String, rt: V.Val, cur: Path, stack: Sk,
  +s: String, aot: Bool, bare: Bool) -> St:
  match names:
    case NNil{}:
      step.head.first.ok(bare, err, rt, cur, stack, s, aot)
    case NCons{_h, _t}:
      St{err.keep(err, "key"), rt, cur, MTop{}, NNil{}, "", KNil{}, False{}}

# a header key, a dot, or `]`
def step.headm(st: St, tok: L.Tok) -> St:
  match st tok:
    case s L.TNl{}:
      s
    case St{err, rt, cur, _m, names, _p, stack, aot} L.TDot{}:
      St{err, rt, cur, MHeadDot{}, names, "", stack, aot}
    case s L.TRBr{}:
      step.head.br(s)
    case St{err, rt, cur, _m, names, _p, stack, aot} L.TStr{s}:
      step.head.first(names, err, rt, cur, stack, s, aot, True{})
    case St{err, rt, cur, _m, names, _p, stack, aot} L.TBare{+s}:
      step.head.first(names, err, rt, cur, stack, s, aot, Txt.bare(s))
    case St{err, rt, cur, _m, _n, _p, _s, _a} L.TBad{why}:
      St{err.keep(err, why), rt, cur, MTop{}, NNil{}, "", KNil{}, False{}}
    case St{err, rt, cur, _m, _n, _p, _s, _a} _:
      St{err.keep(err, "key"), rt, cur, MTop{}, NNil{}, "", KNil{}, False{}}

# the segment after a dot in a header
def step.hdot(st: St, tok: L.Tok) -> St:
  match st tok:
    case s L.TNl{}:
      s
    case St{err, rt, cur, _m, names, _p, stack, aot} L.TStr{s}:
      St{err, rt, cur, MHead{}, nm.snoc(names, s), "", stack, aot}
    case St{err, rt, cur, _m, names, _p, stack, aot} L.TBare{+s}:
      step.hbare(Txt.bare(s), err, rt, cur, names, stack, s, aot)
    case St{err, rt, cur, _m, _n, _p, _s, _a} L.TBad{why}:
      St{err.keep(err, why), rt, cur, MTop{}, NNil{}, "", KNil{}, False{}}
    case St{err, rt, cur, _m, _n, _p, _s, _a} _:
      St{err.keep(err, "key"), rt, cur, MTop{}, NNil{}, "", KNil{}, False{}}

# the second `]` of `[[table]]`
def step.end(st: St, tok: L.Tok) -> St:
  match st tok:
    case s L.TNl{}:
      s
    case s L.TRBr{}:
      step.finish(s)
    case St{err, rt, cur, _m, _n, _p, _s, _a} L.TBad{why}:
      St{err.keep(err, why), rt, cur, MTop{}, NNil{}, "", KNil{}, False{}}
    case St{err, rt, cur, _m, _n, _p, _s, _a} _:
      St{err.keep(err, "key"), rt, cur, MTop{}, NNil{}, "", KNil{}, False{}}

# the value after `=`
def step.val(st: St, tok: L.Tok) -> St:
  step.read(st, tok)

# a value or `]` in an array
def step.arr(st: St, tok: L.Tok) -> St:
  match st tok:
    case s L.TNl{}:
      s
    case s L.TRBr{}:
      step.close.arr(s)
    case s tok2:
      step.read(s, tok2)

# a comma or `]` after an array value
def step.arrsep(st: St, tok: L.Tok) -> St:
  match st tok:
    case s L.TNl{}:
      s
    case St{err, rt, cur, _m, _n, _p, stack, _a} L.TComma{}:
      St{err, rt, cur, MVal{}, NNil{}, "", stack, False{}}
    case s L.TRBr{}:
      step.close.arr(s)
    case St{err, rt, cur, _m, _n, _p, _s, _a} L.TBad{why}:
      St{err.keep(err, why), rt, cur, MTop{}, NNil{}, "", KNil{}, False{}}
    case St{err, rt, cur, _m, _n, _p, _s, _a} _:
      St{err.keep(err, "value"), rt, cur, MTop{}, NNil{}, "", KNil{}, False{}}

# a key or `}` in an inline table
def step.inl(st: St, tok: L.Tok) -> St:
  match st tok:
    case St{err, rt, cur, _m, _n, _p, _s, _a} L.TNl{}:
      St{err.keep(err, "newline"), rt, cur, MTop{}, NNil{}, "", KNil{},
        False{}}
    case s L.TRBc{}:
      step.close.inl(s)
    case St{err, rt, cur, _m, names, _p, stack, _a} L.TStr{s}:
      step.kstr(err, rt, cur, names, stack, s, MInlSeg{})
    case St{err, rt, cur, _m, names, _p, stack, _a} L.TBare{+s}:
      step.kbare(Txt.bare(s), err, rt, cur, names, stack, s, MInlSeg{})
    case St{err, rt, cur, _m, _n, _p, _s, _a} L.TBad{why}:
      St{err.keep(err, why), rt, cur, MTop{}, NNil{}, "", KNil{}, False{}}
    case St{err, rt, cur, _m, _n, _p, _s, _a} _:
      St{err.keep(err, "key"), rt, cur, MTop{}, NNil{}, "", KNil{}, False{}}

# a key after a dot, or after a comma, in an inline table
def step.inlkey(st: St, tok: L.Tok) -> St:
  step.inl(st, tok)

# a dot or `=` after an inline key
def step.inlseg(st: St, tok: L.Tok) -> St:
  match st tok:
    case St{err, rt, cur, _m, _n, _p, _s, _a} L.TNl{}:
      St{err.keep(err, "newline"), rt, cur, MTop{}, NNil{}, "", KNil{},
        False{}}
    case St{err, rt, cur, _m, names, _p, stack, _a} L.TDot{}:
      St{err, rt, cur, MInlKey{}, names, "", stack, False{}}
    case s L.TEq{}:
      step.inl.eq(s)
    case St{err, rt, cur, _m, _n, _p, _s, _a} L.TBad{why}:
      St{err.keep(err, why), rt, cur, MTop{}, NNil{}, "", KNil{}, False{}}
    case St{err, rt, cur, _m, _n, _p, _s, _a} _:
      St{err.keep(err, "key"), rt, cur, MTop{}, NNil{}, "", KNil{}, False{}}

# a comma or `}` after an inline value
def step.inlsep(st: St, tok: L.Tok) -> St:
  match st tok:
    case St{err, rt, cur, _m, _n, _p, _s, _a} L.TNl{}:
      St{err.keep(err, "newline"), rt, cur, MTop{}, NNil{}, "", KNil{},
        False{}}
    case St{err, rt, cur, _m, _n, _p, stack, _a} L.TComma{}:
      St{err, rt, cur, MInlKey{}, NNil{}, "", stack, False{}}
    case s L.TRBc{}:
      step.close.inl(s)
    case St{err, rt, cur, _m, _n, _p, _s, _a} L.TBad{why}:
      St{err.keep(err, why), rt, cur, MTop{}, NNil{}, "", KNil{}, False{}}
    case St{err, rt, cur, _m, _n, _p, _s, _a} _:
      St{err.keep(err, "value"), rt, cur, MTop{}, NNil{}, "", KNil{}, False{}}

# where the token that closed a bare value is read
def step.after.mode(mode: Pm, tok: L.Tok, st: St) -> St:
  match mode:
    case MTop{}:
      step.top(st, tok)
    case MArrSep{}:
      step.arrsep(st, tok)
    case MInlSep{}:
      step.inlsep(st, tok)
    case _:
      st

# the token that closed a bare value, in the mode the value left behind
def step.after(tok: L.Tok, st: St) -> St:
  match st:
    case St{_e, _r, _c, +mode, _n, _p, _s, _a}:
      step.after.mode(mode, tok, st)

# `part` joined to a time that follows a date
def step.join(+part: String, s: String) -> Bool:
  Bool.and(String.contains(part, "-"),
    Bool.and(Bool.not(String.contains(part, ":")),
      Bool.and(Bool.not(String.contains(part, ".")),
        String.contains(s, ":"))))

# a partial value closed by `tok`
def step.part.end(tok: L.Tok, err: String, rt: V.Val, cur: Path, names: Nm,
  part: String, stack: Sk) -> St:
  step.after(tok, step.land.lit(lit.of(part), err, rt, cur, names, stack))

# a bare word after a partial value
def step.part.bare(dot: Bool, join: Bool, +s: String, err: String, rt: V.Val,
  cur: Path, names: Nm, +part: String, stack: Sk) -> St:
  match dot:
    case True{}:
      St{err, rt, cur, MPart{}, names, part ++ s, stack, False{}}
    case False{}:
      match join:
        case True{}:
          St{err, rt, cur, MPart{}, names, part ++ " " ++ s, stack, False{}}
        case False{}:
          step.part.end(L.TBare{s}, err, rt, cur, names, part, stack)

# a dot, another word, or the end of a bare value
def step.part(st: St, tok: L.Tok) -> St:
  match st tok:
    case St{err, rt, cur, _m, names, part, stack, _a} L.TDot{}:
      St{err, rt, cur, MPart{}, names, part ++ ".", stack, False{}}
    case St{err, rt, cur, _m, names, +part, stack, _a} L.TBare{+s}:
      step.part.bare(String.ends_with(part, "."), step.join(part, s), s, err,
        rt, cur, names, part, stack)
    case St{err, rt, cur, _m, names, part, stack, _a} tok2:
      step.part.end(tok2, err, rt, cur, names, part, stack)

# one token in the mode the reader is in
def step.on(mode: Pm, st: St, tok: L.Tok) -> St:
  match mode:
    case MTop{}:
      step.top(st, tok)
    case MKey{}:
      step.key(st, tok)
    case MSeg{}:
      step.seg(st, tok)
    case MBrack{}:
      step.brack(st, tok)
    case MHead{}:
      step.headm(st, tok)
    case MHeadDot{}:
      step.hdot(st, tok)
    case MEnd{}:
      step.end(st, tok)
    case MVal{}:
      step.val(st, tok)
    case MPart{}:
      step.part(st, tok)
    case MArr{}:
      step.arr(st, tok)
    case MArrSep{}:
      step.arrsep(st, tok)
    case MInl{}:
      step.inl(st, tok)
    case MInlKey{}:
      step.inlkey(st, tok)
    case MInlSeg{}:
      step.inlseg(st, tok)
    case MInlSep{}:
      step.inlsep(st, tok)

# one token
def step.feed(st: St, tok: L.Tok) -> St:
  match st:
    case St{_err, _rt, _cur, +mode, _names, _part, _stack, _aot}:
      step.on(mode, st, tok)

# every token
def parse.run(ts: List<&2, L.Tok>, st: St) -> St:
  match ts:
    case []:
      st
    case h <> t:
      parse.run(t, step.feed(st, h))

# a document whose value is finished
def parse.fin.top(stack: Sk, err: String, rt: V.Val) -> Doc:
  match stack:
    case KNil{}:
      Doc{err, rt}
    case KCons{_fr, _rest}:
      Doc{err.keep(err, "unclosed"), rt}

# a document after a trailing bare value
def parse.fin.closed(mode: Pm, stack: Sk, err: String, rt: V.Val) -> Doc:
  match mode:
    case MTop{}:
      parse.fin.top(stack, err, rt)
    case _:
      Doc{err.keep(err, "unclosed"), rt}

# the state a trailing bare value leaves
def parse.fin.done(st: St) -> Doc:
  match st:
    case St{err, rt, _cur, mode, _names, _part, stack, _aot}:
      parse.fin.closed(mode, stack, err, rt)

# the document a reader left, including a bare value with nothing after it
def parse.fin.mode(mode: Pm, err: String, rt: V.Val, cur: Path, names: Nm,
  part: String, stack: Sk) -> Doc:
  match mode:
    case MPart{}:
      parse.fin.done(step.land.lit(lit.of(part), err, rt, cur, names, stack))
    case MTop{}:
      parse.fin.top(stack, err, rt)
    case _:
      Doc{err.keep(err, "unclosed"), rt}

# the document a reader left
def parse.fin(st: St) -> Doc:
  match st:
    case St{err, rt, cur, mode, names, part, stack, _aot}:
      parse.fin.mode(mode, err, rt, cur, names, part, stack)

# the table in `text`, and the first error if there was one
def parse(text: String) -> Doc:
  parse.fin(parse.run(L.tokens(text), St{"", V.empty(), PNil{}, MTop{}, NNil{},
    "", KNil{}, False{}}))
