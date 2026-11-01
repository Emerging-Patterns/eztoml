# what a value looks like once rows.seal has sealed it
import Base
import ../../main.bend as T

# a value as rows.seal leaves it: the rows of a table, of an element of an
# array of tables and of an inline table, and the elements of an array of
# tables, each sealed in turn; an array's items sealed and kept in order
def sealed(+vv: T.Val) -> T.Val:
  match vv:
    case T.VPair{nn, T.VHead{pp, rows}}:
      T.VPair{nn, T.VHead{pp, T.rows.seal(rows)}}
    case T.VPair{nn, T.VAots{pp, elems}}:
      T.VPair{nn, T.VAots{pp, T.rows.seal(elems)}}
    case T.VPair{nn, T.VInl{rows}}:
      T.VPair{nn, T.VInl{T.rows.seal(rows)}}
    case T.VPair{nn, T.VArr{items}}:
      T.VPair{nn, T.VArr{List.reverse(&2, T.Val, T.rows.seal(items))}}
    case T.VAot{pp, rows}:
      T.VAot{pp, T.rows.seal(rows)}
    case T.VAots{pp, elems}:
      T.VAots{pp, T.rows.seal(elems)}
    case T.VInl{rows}:
      T.VInl{T.rows.seal(rows)}
    case T.VArr{items}:
      T.VArr{List.reverse(&2, T.Val, T.rows.seal(items))}
    case _:
      vv
