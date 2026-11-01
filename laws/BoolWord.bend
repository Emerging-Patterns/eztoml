import Base
import ../main.bend as T

# LAW: a boolean's text is classified as the boolean
law bool_word:
  for b: Bool
  {T.word.val(String.to_list(T.render.atom(T.VBool{b}))) == T.GotVal{T.VBool{b}} : T.Got}
