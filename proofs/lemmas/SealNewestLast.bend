# rows.seal puts the newest row last, pass by pass
import Base
import ../../main.bend as T
import ../../laws/SealPutsNewestLast.bend as L1
import ../../laws/defs/SealedValues.bend as D1

# rows.seal. Its one pass conses each value, sealed, onto an accumulator and
# reverses a table's accumulator by not reversing it back.

# the value rows.seal.go conses for a value
def seal.y(+vv: T.Val) -> T.Val:
  match vv:
    case T.VPair{nn, T.VHead{pp, rows}}:
      T.VPair{nn, T.VHead{pp, T.rows.seal(rows)}}
    case T.VPair{nn, T.VAots{pp, elems}}:
      T.VPair{nn, T.VAots{pp, T.rows.seal(elems)}}
    case T.VPair{nn, T.VInl{rows}}:
      T.VPair{nn, T.VInl{T.rows.seal(rows)}}
    case T.VPair{nn, T.VArr{items}}:
      T.VPair{nn, T.VArr{T.rows.seal.go(items, False{}, [])}}
    case T.VAot{pp, rows}:
      T.VAot{pp, T.rows.seal(rows)}
    case T.VAots{pp, elems}:
      T.VAots{pp, T.rows.seal(elems)}
    case T.VInl{rows}:
      T.VInl{T.rows.seal(rows)}
    case T.VArr{items}:
      T.VArr{T.rows.seal.go(items, False{}, [])}
    case _:
      vv

# one step of the pass, for each value it can meet
def go.cons(
  xx: T.Val,
  tt: List<&2, T.Val>,
  rev: Bool,
  acc: List<&2, T.Val>
) -> {T.rows.seal.go(xx <> tt, rev, acc) == T.rows.seal.go(tt, rev, seal.y(xx) <> acc)
  : List<&2, T.Val>}:
  match xx:
    case T.VPair{_n, T.VStr{_a}}:
      {==}
    case T.VPair{_n, T.VSpan{_a, _b}}:
      {==}
    case T.VPair{_n, T.VInt{_a, _b}}:
      {==}
    case T.VPair{_n, T.VFlo{_a, _b}}:
      {==}
    case T.VPair{_n, T.VBool{_a}}:
      {==}
    case T.VPair{_n, T.VWhen{_a}}:
      {==}
    case T.VPair{_n, T.VArr{_a}}:
      {==}
    case T.VPair{_n, T.VInl{_a}}:
      {==}
    case T.VPair{_n, T.VHead{_a, _b}}:
      {==}
    case T.VPair{_n, T.VAot{_a, _b}}:
      {==}
    case T.VPair{_n, T.VAots{_a, _b}}:
      {==}
    case T.VPair{_n, T.VPair{_a, _b}}:
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

# appending one value and then a list is appending the list with it in front
def app.snoc(
  aa: List<&2, T.Val>,
  +yy: T.Val,
  +bb: List<&2, T.Val>
) -> {List.append(&2, T.Val, List.append(&2, T.Val, aa, [yy]), bb)
  == List.append(&2, T.Val, aa, yy <> bb) : List<&2, T.Val>}:
  match aa:
    case []:
      {==}
    case hh <> tt:
      Equal.cong(List<&2, T.Val>, List<&2, T.Val>, ll => hh <> ll,
        List.append(&2, T.Val, List.append(&2, T.Val, tt, [yy]), bb),
        List.append(&2, T.Val, tt, yy <> bb), app.snoc(tt, yy, bb))

# a table's pass onto an accumulator is the pass onto nothing, then the
# accumulator
def go.acc(
  vs: List<&2, T.Val>,
  +acc: List<&2, T.Val>
) -> {T.rows.seal.go(vs, True{}, acc)
  == List.append(&2, T.Val, T.rows.seal.go(vs, True{}, []), acc) : List<&2, T.Val>}:
  match vs:
    case []:
      {==}
    case +xx <> +tt:
      Equal.trans(List<&2, T.Val>,
        T.rows.seal.go(xx <> tt, True{}, acc),
        T.rows.seal.go(tt, True{}, seal.y(xx) <> acc),
        List.append(&2, T.Val, T.rows.seal.go(xx <> tt, True{}, []), acc),
        go.cons(xx, tt, True{}, acc),
        Equal.trans(List<&2, T.Val>,
          T.rows.seal.go(tt, True{}, seal.y(xx) <> acc),
          List.append(&2, T.Val, T.rows.seal.go(tt, True{}, []), seal.y(xx) <> acc),
          List.append(&2, T.Val, T.rows.seal.go(xx <> tt, True{}, []), acc),
          go.acc(tt, seal.y(xx) <> acc),
          Equal.sym(List<&2, T.Val>,
            List.append(&2, T.Val, T.rows.seal.go(xx <> tt, True{}, []), acc),
            List.append(&2, T.Val, T.rows.seal.go(tt, True{}, []), seal.y(xx) <> acc),
            Equal.trans(List<&2, T.Val>,
              List.append(&2, T.Val, T.rows.seal.go(xx <> tt, True{}, []), acc),
              List.append(&2, T.Val, T.rows.seal.go(tt, True{}, [seal.y(xx)]), acc),
              List.append(&2, T.Val, T.rows.seal.go(tt, True{}, []), seal.y(xx) <> acc),
              Equal.cong(List<&2, T.Val>, List<&2, T.Val>, ll => List.append(&2, T.Val, ll, acc),
                T.rows.seal.go(xx <> tt, True{}, []), T.rows.seal.go(tt, True{}, [seal.y(xx)]),
                go.cons(xx, tt, True{}, [])),
              Equal.trans(List<&2, T.Val>,
                List.append(&2, T.Val, T.rows.seal.go(tt, True{}, [seal.y(xx)]), acc),
                List.append(&2, T.Val, List.append(&2, T.Val, T.rows.seal.go(tt, True{}, []),
                  [seal.y(xx)]), acc),
                List.append(&2, T.Val, T.rows.seal.go(tt, True{}, []), seal.y(xx) <> acc),
                Equal.cong(List<&2, T.Val>, List<&2, T.Val>, ll => List.append(&2, T.Val, ll, acc),
                  T.rows.seal.go(tt, True{}, [seal.y(xx)]),
                  List.append(&2, T.Val, T.rows.seal.go(tt, True{}, []), [seal.y(xx)]),
                  go.acc(tt, [seal.y(xx)])),
                app.snoc(T.rows.seal.go(tt, True{}, []), seal.y(xx), acc))))))

# an array's pass keeps the order: it is a table's pass reversed back
def go.false(
  vs: List<&2, T.Val>,
  +acc: List<&2, T.Val>
) -> {T.rows.seal.go(vs, False{}, acc)
  == List.reverse(&2, T.Val, T.rows.seal.go(vs, True{}, acc)) : List<&2, T.Val>}:
  match vs:
    case []:
      {==}
    case +xx <> +tt:
      Equal.trans(List<&2, T.Val>,
        T.rows.seal.go(xx <> tt, False{}, acc),
        T.rows.seal.go(tt, False{}, seal.y(xx) <> acc),
        List.reverse(&2, T.Val, T.rows.seal.go(xx <> tt, True{}, acc)),
        go.cons(xx, tt, False{}, acc),
        Equal.trans(List<&2, T.Val>,
          T.rows.seal.go(tt, False{}, seal.y(xx) <> acc),
          List.reverse(&2, T.Val, T.rows.seal.go(tt, True{}, seal.y(xx) <> acc)),
          List.reverse(&2, T.Val, T.rows.seal.go(xx <> tt, True{}, acc)),
          go.false(tt, seal.y(xx) <> acc),
          Equal.cong(List<&2, T.Val>, List<&2, T.Val>, ll => List.reverse(&2, T.Val, ll),
            T.rows.seal.go(tt, True{}, seal.y(xx) <> acc), T.rows.seal.go(xx <> tt, True{}, acc),
            Equal.sym(List<&2, T.Val>, T.rows.seal.go(xx <> tt, True{}, acc),
              T.rows.seal.go(tt, True{}, seal.y(xx) <> acc), go.cons(xx, tt, True{}, acc)))))

# the value the pass conses is the value sealed
def y.sealed(xx: T.Val) -> {seal.y(xx) == D1.sealed(xx) : T.Val}:
  match xx:
    case T.VPair{_n, T.VStr{_a}}:
      {==}
    case T.VPair{_n, T.VSpan{_a, _b}}:
      {==}
    case T.VPair{_n, T.VInt{_a, _b}}:
      {==}
    case T.VPair{_n, T.VFlo{_a, _b}}:
      {==}
    case T.VPair{_n, T.VBool{_a}}:
      {==}
    case T.VPair{_n, T.VWhen{_a}}:
      {==}
    case T.VPair{+nn, T.VArr{+items}}:
      Equal.cong(List<&2, T.Val>, T.Val, ii => T.VPair{nn, T.VArr{ii}},
        T.rows.seal.go(items, False{}, []), List.reverse(&2, T.Val, T.rows.seal(items)),
        go.false(items, []))
    case T.VPair{_n, T.VInl{_a}}:
      {==}
    case T.VPair{_n, T.VHead{_a, _b}}:
      {==}
    case T.VPair{_n, T.VAot{_a, _b}}:
      {==}
    case T.VPair{_n, T.VAots{_a, _b}}:
      {==}
    case T.VPair{_n, T.VPair{_a, _b}}:
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
    case T.VArr{+items}:
      Equal.cong(List<&2, T.Val>, T.Val, ii => T.VArr{ii},
        T.rows.seal.go(items, False{}, []), List.reverse(&2, T.Val, T.rows.seal(items)),
        go.false(items, []))
    case T.VInl{_a}:
      {==}
    case T.VHead{_a, _b}:
      {==}
    case T.VAot{_a, _b}:
      {==}
    case T.VAots{_a, _b}:
      {==}

def L1.seal_puts_newest_last(x, rows):
  Equal.trans(List<&2, T.Val>,
    T.rows.seal.go(x <> rows, True{}, []),
    T.rows.seal.go(rows, True{}, [seal.y(x)]),
    List.append(&2, T.Val, T.rows.seal(rows), [D1.sealed(x)]),
    go.cons(x, rows, True{}, []),
    Equal.trans(List<&2, T.Val>,
      T.rows.seal.go(rows, True{}, [seal.y(x)]),
      List.append(&2, T.Val, T.rows.seal(rows), [seal.y(x)]),
      List.append(&2, T.Val, T.rows.seal(rows), [D1.sealed(x)]),
      go.acc(rows, [seal.y(x)]),
      Equal.cong(T.Val, List<&2, T.Val>, yy => List.append(&2, T.Val, T.rows.seal(rows), [yy]),
        seal.y(x), D1.sealed(x), y.sealed(x))))
