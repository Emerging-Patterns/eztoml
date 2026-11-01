import Base
import ../main.bend as T
import ./defs/DocumentSameness.bend as D1

# LAW: swapping two adjacent pairs of different names in a well-formed
# document's root table gives the same document
law same_swap:
  for +e: String
  for +pre: List<&2, T.Val>
  for +nx: String
  for +vx: T.Val
  for +ny: String
  for +vy: T.Val
  for +post: List<&2, T.Val>
  for w: {T.wf(T.Doc{e, List.append(&2, T.Val, pre, T.VPair{nx, vx} <> T.VPair{ny, vy} <> post)})
    == True{} : Bool}
  for ne: {String.eq(nx, ny) == False{} : Bool}
  {D1.same(T.Doc{e, List.append(&2, T.Val, pre, T.VPair{nx, vx} <> T.VPair{ny, vy} <> post)},
    T.Doc{e, List.append(&2, T.Val, pre, T.VPair{ny, vy} <> T.VPair{nx, vx} <> post)}) == True{} : Bool}
