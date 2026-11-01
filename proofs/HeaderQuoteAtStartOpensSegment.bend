# proofs of laws/HeaderQuoteAtStartOpensSegment.bend
import Base
import ../laws/HeaderQuoteAtStartOpensSegment.bend as Laws

def Laws.header_quote_at_start_opens_segment(
  _bad,
  _rows,
  _heads,
  _here,
  _back,
  _qkind,
  _stack,
  _uni,
  _left,
  _arrtab,
  lit
):
  match lit:
    case True{}:
      {==}
    case False{}:
      {==}
