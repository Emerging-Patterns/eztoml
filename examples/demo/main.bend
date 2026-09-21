# examples/demo: parse and render a string-valued TOML document
import Base
import ../../eztoml/main.bend as Toml

def main() -> IO(Unit):
  +text = "[package]\nname = \"app\"\n\n[deps.\"0x0a\"]\nhash = \"ab\"\n"
  +doc = Toml.parse(text)
  IO.print(Toml.render(Toml.sects(doc)))
  IO.print(String.join(Toml.segments("packages.\"0x0a\".files"), "|"))
  IO.print(Toml.key("my-key"))
  IO.print(Toml.quote("value"))
