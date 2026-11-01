import Base
import ../main.bend as T
import ./defs/SealedValues.bend as D1

# LAW: rows.seal puts the newest row last: sealing rows with x at their head
# is sealing the rest, then x sealed. Rows built newest first come out in the
# order they were written, and every table inside is sealed the same way
law seal_puts_newest_last:
  for +x: T.Val
  for +rows: List<&2, T.Val>
  {T.rows.seal(x <> rows) == List.append(&2, T.Val, T.rows.seal(rows), [D1.sealed(x)])
    : List<&2, T.Val>}
