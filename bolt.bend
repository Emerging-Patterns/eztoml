# bolt.bend: how bolt lints this repo. Every rule is an error except `coverage`,
# which warns until SPEC.md's requirements are proved: the gate must see no
# errors. See bolt/config.bend for the groups and levels.
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

# a def no quantified law reaches: advice until SPEC.md's rows are proved
def laws() -> String:
  "warn"

# a closed equality is a computed document, which is what these laws are
def closed() -> String:
  "off"
