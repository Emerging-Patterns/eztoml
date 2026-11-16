# bolt.bend: how bolt lints this repo. Every rule is an error: the gate must
# see no findings. See bolt's src/config.bend for the groups and levels.
import Base

# what will fail or blow up
def correctness() -> String:
  "error"

# what is probably a slip
def suspicious() -> String:
  "error"

# comments and whitespace
def style() -> String:
  "error"

# the laws rules
def laws() -> String:
  "error"

# a law with no binder (opt-in)
def closed() -> String:
  "error"

# a def no quantified law reaches (L001, opt-in)
def coverage() -> String:
  "error"
