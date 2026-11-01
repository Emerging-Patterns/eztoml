import Base
import ../main.bend as T
import ./defs/BareValueGrammar.bend as D1

# LAW: a value put along a path the walk goes on through, to a name the table
# at its end does not hold, goes at the head of that table's rows (newest
# first); the walk changes nothing else: every other table, the recorded
# definitions and the error are as they were. skip counts the segments that
# are navigation into the current table
law walk_put_at_head:
  for +here: List<&2, String>
  for +k: String
  for +v: T.Val
  for +rows: List<&2, T.Val>
  for +heads: List<&2, String>
  for +skip: U32
  for +inl: Bool
  for +eo: {D1.tb.open(here, rows) == True{} : Bool}
  for ec: {D1.counts.down(here, skip) == True{} : Bool}
  for em: {T.get(D1.tb.rows(here, rows), k) == T.Miss{} : T.Hit}
  {T.tree.walk(List.append(&2, String, here, [k]), T.Tw{rows, T.JPut{v}, [], "", "", heads, inl},
    skip) == T.End{D1.tb.set(here, "", rows, T.VPair{k, v} <> D1.tb.rows(here, rows)), "", heads} : T.End}
