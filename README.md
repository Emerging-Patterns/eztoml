# eztoml

TOML for [Bend 2](https://github.com/bendlang/bend).

## Install

Use with [Bend](https://github.com/bendlang/bend) or install easily with [ez](https://github.com/Emerging-Patterns/ez):

```
ez init
ez add Emerging-Patterns/eztoml
```

## Usage

`parse` reads text into a document. `render` writes a document back. `get`
finds a value by key and `at` finds one by a dotted path. A hit is `Found` or
`Miss`. `string`, `digits`, and `flag` read a string, an integer's digits, and
a boolean. `root` is the document's table and `bad` is the first error.
`str`, `integer`, `float`, `boolean`, `array`, `inline`, `table`, and `pair`
build values. `key` writes a name bare or as a basic string.

```
import 0x60bccc8edd34707613da7f8d2b8bfd47/main.bend as Toml

def main() -> IO(Unit):
  +doc = Toml.parse("[pkg]\nname = \"app\"\nver = 1\non = true\n")
  IO.print(Toml.render(doc))
```

```
git clone https://github.com/Emerging-Patterns/eztoml
cd eztoml
mkdir -p bin
bend examples/demo/main.bend -o bin/demo.bin
bin/demo.bin
```

`nix build` builds the same fixture to `result/bin/demo`.

## Compliance

`nix flake check` proves `eztoml/LAWS.bend` in `eztoml/PROOF.bend`. Those laws are closed parse and render equalities for these productions of [TOML v1.0.0](https://toml.io/en/v1.0.0) / [toml.abnf](https://github.com/toml-lang/toml/blob/1.0.0/toml.abnf):

- `comment`
- `boolean`
- `basic-string`, `literal-string`, `ml-basic-string`, `ml-literal-string`
- `dec-int`, `hex-int`, `oct-int`, `bin-int`
- `float`, `special-float`
- `std-table`, `dotted-key`, `quoted-key`
- `inline-table`, `array`, `array-table`

The datetime equalities follow [RFC 3339](https://www.rfc-editor.org/rfc/rfc3339): `offset-date-time`, `local-date-time`, `full-date`, `partial-time`.
