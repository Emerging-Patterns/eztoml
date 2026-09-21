# eztoml

## Install

```
curl -fsSL https://bend-lang.com/install.sh | sh
```

```
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/main.bend as Toml
```

## Usage

eztoml reads and writes TOML. Values are strings, integers, floats, booleans,
datetimes, arrays, and inline tables. Tables and arrays of tables are headers.
Comments and blank lines are passed over.

`parse` reads text into a document. `render` writes a document back. `get`
finds a value by key and `at` finds one by a dotted path. A hit is `Found` or
`Miss`. `string`, `digits`, and `flag` read a string, an integer's digits, and
a boolean. `root` is the document's table and `bad` is the first error.
`str`, `integer`, `float`, `boolean`, `array`, `inline`, `table`, and `pair`
build values. `key` writes a name bare or as a basic string.

```
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/main.bend as Toml

def main() -> IO(Unit):
  +doc = Toml.parse("[pkg]\nname = \"app\"\nver = 1\non = true\n")
  IO.print(Toml.render(doc))
```

```
git clone https://github.com/Emerging-Patterns/eztoml
cd eztoml
bend examples/demo/main.bend -o bin/demo.bin
bin/demo.bin
```

`nix build` builds the same fixture to `result/bin/demo`.
