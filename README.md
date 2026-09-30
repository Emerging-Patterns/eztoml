# eztoml

TOML for [Bend 2](https://github.com/bendlang/bend).

## Install

With [Bend](https://github.com/bendlang/bend) alone there is nothing to
install: import eztoml by its hub name and version, and `bend` fetches it
from [the hub](https://hub.bend-lang.com) into `~/.bend/lib` on the first
run; no install step. eztoml is built and checked on Bend 2.0.34.

```
import emerging-eztoml@0.8.0.0/main.bend as Toml
```

`emerging-eztoml@0.8.0.0` is eztoml v0.8.0 and resolves to
`0x8fb95168b7719a8faec16af7ee47b246`; to pin by content, import
`0x8fb95168b7719a8faec16af7ee47b246/main.bend` instead.

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
import emerging-eztoml@0.8.0.0/main.bend as Toml

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

`parse` takes text, not bytes. Bend's `File.read` replaces each invalid UTF-8
byte with U+FFFD rather than rejecting it, and U+FFFD is valid in a comment or
a string, so `parse` reads such a file as the valid text it has become. When
invalid bytes must be refused, check the file as UTF-8 before `parse`
(TOML-TRUST-3).

## Guarantees

[SPEC.md](SPEC.md) lists every behavior eztoml guarantees, against [TOML v1.0.0](https://toml.io/en/v1.0.0) and [toml.abnf](https://github.com/toml-lang/toml/blob/1.0.0/toml.abnf), each either proved by a quantified law in `LAWS.bend` or named as a trusted assumption. A row marked pending is not guaranteed yet. `nix flake check` runs the proof gate (`bend PROOF.bend` must print exactly `ALL PROOFS CHECK` first) and bolt, whose `trace` rule checks that SPEC.md and the laws agree. The headline is the round trip: a document `render` writes reads back as the same document (TOML-RT-1).
