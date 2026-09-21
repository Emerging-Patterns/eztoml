# parse and render a TOML document
import Base
import ../../eztoml/main.bend as Toml

# the string at a hit
def shown.text(h: Toml.Hit) -> String:
  match h:
    case Toml.Found{v}:
      Toml.string(v)
    case Toml.Miss{}:
      ""

# a document with a root key, a table, an array, an inline table, and a datetime
def shown() -> String:
  +doc = Toml.parse("name = \"app\"\nver = 1\non = true\n" ++
    "items = [1, 2]\nmeta = { os = \"linux\" }\n" ++
    "when = 1979-05-27T07:32:00Z\n\n[pkg]\nname = \"eztoml\"\n\n" ++
    "[[fruit]]\nname = \"apple\"\n")
  "[" ++ Toml.bad(doc) ++ "]\n" ++ Toml.render(doc) ++
    shown.text(Toml.get(Toml.root(doc), "name"))

def main() -> IO(Unit):
  IO.print(shown())
