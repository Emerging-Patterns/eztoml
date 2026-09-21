# eztoml

## Install

```
curl -fsSL https://bend-lang.com/install.sh | sh
```

```
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/main.bend as Toml
```

## Usage

eztoml is the TOML slice for string-valued sectioned docs: headers,
`key = "value"`, comments, and blanks. Headers may be quoted and dotted.
There are no arrays, inline tables, or numbers.

`parse` reads a document into sections and the first error if there was one.
`render` writes sections back. `value` looks up a key in a table. `sects`
is the sections a parse finished. `segments` cuts a header on unquoted dots.
`quote` wraps a string; `key` writes a name bare when it can.

```
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/main.bend as Toml

def main() -> IO(Unit):
  +doc = Toml.parse("[package]\nname = \"app\"\n")
  IO.print(Toml.render(Toml.sects(doc)))
```

```
git clone https://github.com/Emerging-Patterns/eztoml
cd eztoml
bend examples/demo/main.bend -o bin/demo.bin
bin/demo.bin
```

`nix build` builds the same fixture to `result/bin/demo`.
