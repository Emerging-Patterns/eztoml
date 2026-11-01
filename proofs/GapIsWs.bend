# proofs of laws/GapIsWs.bend
import Base
import ../laws/GapIsWs.bend as Laws

# GRAMMAR: the basic facts of the transcription (WP-G). The text lemmas say
# that each def of g.text writes its part before the tail it is given, so a
# derivation's text is its parts' texts one after another.

def Laws.gap_is_ws(gs):
  match gs:
    case []:
      {==}
    case tab <> rest:
      match tab:
        case True{}:
          Laws.gap_is_ws(rest)
        case False{}:
          Laws.gap_is_ws(rest)
