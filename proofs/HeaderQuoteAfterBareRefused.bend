# proofs of laws/HeaderQuoteAfterBareRefused.bend
import Base
import ../main.bend as T
import ../laws/HeaderQuoteAfterBareRefused.bend as Laws
import ./lemmas/FailedScanStays.bend as M1

# laws/ParsesExactlyTheGrammar.bend and laws/KeyNameIsItsCharacters.bend: the header scanner. Each character computes to
# its step, and a refusal comes to the failed state through err.sinks.

def Laws.header_quote_after_bare_refused(
  bad,
  rows,
  heads,
  here,
  parts,
  c,
  cs,
  back,
  qkind,
  stack,
  uni,
  left,
  arrtab,
  lit,
  t
):
  match lit:
    case True{}:
      M1.err.sinks(T.St{bad, rows, heads, here, parts, c <> cs, T.LHead{}, back, qkind,
        stack, T.HNone{}, uni, left, arrtab, False{}}, 'i', "nvalid header", t)
    case False{}:
      M1.err.sinks(T.St{bad, rows, heads, here, parts, c <> cs, T.LHead{}, back, qkind,
        stack, T.HNone{}, uni, left, arrtab, False{}}, 'i', "nvalid header", t)
