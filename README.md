# eztoml

## Install

```
curl -fsSL https://bend-lang.com/install.sh | sh
```

```
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/main.bend as Toml
```

## Usage

`parse` reads a TOML document into a table and keeps the first error.
`render` writes a value back as TOML. `root` is the table a parse built.
`err` is that error, or empty. `get` reads a key of a table. `at` reads a
cell of an array. `str`, `integer`, `float`, `boolean` and `datetime` read
a value of that kind.

`string`, `int`, `num`, `flag`, `offset`, `local`, `day`, `time`, `array`,
`table`, `pair`, `cons` and `nil` build values. `segments` cuts a dotted
name on unquoted dots. `quote` writes a basic string. `key` writes a name
bare when it can.

```
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/main.bend as Toml

def main() -> IO(Unit):
  +doc = Toml.parse("name = \"app\"\nversion = 1\n")
  IO.print(Toml.render(Toml.root(doc)))
```

```
git clone https://github.com/Emerging-Patterns/eztoml
cd eztoml
bend examples/demo/main.bend -o bin/demo.bin
bin/demo.bin
```

`nix build` builds the same fixture to `result/bin/demo`.
