# the ABNF rules for whitespace characters
import Base

# Whitespace, newline and comment.

# wschar =  %x20  ; Space
# wschar =/ %x09  ; Horizontal tab
# (%x20 is 32, %x09 is 9)
def abnf.wschar(cc: Char) -> Bool:
  match cc:
    case Chr{+cp}:
      Bool.or(U32.is_eq(cp, 32), U32.is_eq(cp, 9))

# ws = *wschar
def abnf.ws(ss: String) -> Bool:
  match ss:
    case SNil{}:
      True{}
    case SCon{hh, tt}:
      Bool.and(abnf.wschar(hh), abnf.ws(tt))
