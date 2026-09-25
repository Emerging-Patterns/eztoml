# eztoml

TOML for [Bend 2](https://github.com/bendlang/bend).

## Install

With [Bend](https://github.com/bendlang/bend) alone there is nothing to
install: import eztoml by its hub name and `bend` fetches it from
[the hub](https://hub.bend-lang.com) into `~/.bend/lib` on the first run.
`0xd79254973edee82bcf56616220876efe` is eztoml v0.5.0.

```
import 0xd79254973edee82bcf56616220876efe/main.bend as Toml
```

Or with [ez](https://github.com/Emerging-Patterns/ez), which records the
package in `ez.toml` (`ez init` makes one):

```
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
import 0xd79254973edee82bcf56616220876efe/main.bend as Toml

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

## Guarantees

[SPEC.md](SPEC.md) lists every behavior eztoml guarantees, against [TOML v1.0.0](https://toml.io/en/v1.0.0) and [toml.abnf](https://github.com/toml-lang/toml/blob/1.0.0/toml.abnf), each either proved by a quantified law in `LAWS.bend` or named as a trusted assumption. A row marked pending is not guaranteed yet. `nix flake check` runs the proof gate (`bend PROOF.bend` must print exactly `All terms check.` first) and bolt, whose `trace` rule checks that SPEC.md and the laws agree. The headline is the round trip: a document `render` writes reads back as the same document (TOML-RT-1).
