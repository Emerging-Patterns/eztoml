# examples/demo: parse a TOML document and write it back
import Base
import ../../eztoml/main.bend as Toml

# the fixture document, parsed and shown
def shown() -> String:
  +text = "name = \"app\"\nversion = 1\ndebug = true\n" ++
    "ratio = 1.5\nwhen = 1979-05-27T07:32:00Z\n" ++
    "[package]\nauthors = [\"Ada\"]\n" ++
    "[deps]\nez = { version = \"1.0\" }\n" ++
    "[[bin]]\nname = \"demo\"\n"
  +doc = Toml.parse(text)
  Toml.err(doc) ++ "\n" ++ Toml.render(Toml.root(doc)) ++ "\n" ++
    String.join(Toml.segments("packages." ++ Toml.quote("0x0a") ++ ".files"),
      "|") ++ "\n" ++
    Toml.key("my-key") ++ "\n" ++
    Toml.quote("value")

def main() -> IO(Unit):
  IO.print(shown())
