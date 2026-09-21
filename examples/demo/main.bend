# examples/demo: parse and render a string-valued TOML document
import Base
import ../../eztoml/main.bend as Toml

# the fixture document, parsed and shown
def shown() -> String:
  +text = "[package]\nname = " ++ Toml.quote("app") ++ "\n"
  +doc = Toml.parse(text)
  Toml.render(Toml.sects(doc)) ++
    String.join(Toml.segments("packages." ++ Toml.quote("0x0a") ++ ".files"),
      "|") ++ "\n" ++
    Toml.key("my-key") ++ "\n" ++
    Toml.quote("value")

def main() -> IO(Unit):
  IO.print(shown())
