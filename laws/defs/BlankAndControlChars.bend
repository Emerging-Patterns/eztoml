# blank characters, gaps and control characters of the grammar
import Base

# a control character: U+0000 to U+001F, or U+007F
def is_ctl(+cc: Char) -> Bool:
  Bool.or(U32.is_lt(Char.to_u32(cc), 32), U32.is_eq(Char.to_u32(cc), 127))

# a space or a tab
def blank_char(tab: Bool) -> Char:
  match tab:
    case True{}:
      '\t'
    case False{}:
      ' '

# blank space: a tab for each true, a space for each false
def gap(gs: List<&2, Bool>) -> String:
  match gs:
    case []:
      ""
    case tab <> rest:
      SCon{blank_char(tab), gap(rest)}
