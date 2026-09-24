# eztoml law inventory

Read at `d3c1356` on `main` ("Merge pull request #23", release 0.2.2), with bend 2.0.25 (the release `flake.lock` pins through `bendlang/bend` at `a495242`, checksum `91c0e264…` checked against the flake), bolt v0.4.0 (the pin, `24b497e`) and bolt v1.7.0 (the current release, for comparison).

This is the companion to [eztoml-spec.md](eztoml-spec.md). It records what eztoml's laws state today, maps each law to the requirement it points toward, and records what we found by reading the code and by running it. It follows the shape of ez's, bolt's and ezjson's inventories, and it takes the positions those projects reached: exactly two assurance levels, Proved and Trusted; pending is a status, not a level; a closed law has no standing; a test or fixture is never evidence for a requirement.

## How to read the tables

**Kind** is `Q` for a quantified law (at least one `for` or `exs` binder) and `C` for a closed law (no binder, one fixed input).

**Proof** is `{==}` when the whole proof in PROOF.bend is `{==}`: the two sides reduce to the same term with no case split, so for a quantified law the binders are never inspected and the law restates how a definition unfolds. `rewrite` means the proof rewrites by the premise and then closes with `{==}`. `struct` means the proof matches, recurses or uses a lemma.

**Claim** is what the law states, in one line. A closed claim is about one fixed input even when its name reads like a general statement. "Pins wording" means the expected value includes an error message, so rewording the message breaks the proof. "Pins layout" means it includes the renderer's exact spacing and ordering.

**Points toward** names the requirement in the RFC that the law illustrates (the IDs are listed below). `none` has a reason: `definitional` restates a definition, `wiring` restates how two defs compose, `wording` pins text nobody depends on, `helper` is a lemma the proofs use.

## Proposed requirement IDs

These are the IDs the RFC proposes, so the tables can point at them. Their wording and verdicts are in the RFC.

| ID | Short name |
| :---- | :---- |
| TOML-RT-1 | Headline. For every renderable document, `parse(render(d))` has no error and is `same` as `d`. |
| TOML-RT-2 | For every text that parses, `render` of it parses back `same`, and rendering again gives the same bytes. |
| TOML-RT-3 | Every document `parse` returns is renderable. |
| TOML-TEXT-1 | `parse(t)` has no error exactly when `t` is a TOML v1.0.0 document (toml.abnf plus the prose rules on keys and tables). |
| TOML-TEXT-2 | A document is read in one pass, and the first error is the one reported: `bad` is empty exactly when there is none. |
| TOML-KEY-1 | `bare(s)` holds exactly when `s` is nonempty and every character is `A-Za-z0-9_-`. |
| TOML-KEY-2 | `key(s)` is `s` when `bare(s)`, and otherwise a basic string that reads back as `s`. |
| TOML-STR-1 | Every string value reads back as its characters: basic, literal and both multi-line forms, with each escape decoded. |
| TOML-STR-2 | The renderer's basic string escapes exactly `"`, `\` and the controls, and reads back as the text. |
| TOML-NUM-1 | Integers: every form the grammar allows reads to its value, range checked to signed 64 bits. |
| TOML-NUM-2 | Floats keep their spelling, apart from the stated normalizations. |
| TOML-TIME-1 | Datetimes: the four forms read to their fields, with RFC 3339 range checks. |
| TOML-GET-1 | `get(rows, k)` is the value of the first pair named `k`, and `Miss` when there is none. |
| TOML-GET-2 | `at(rows, path)` walks tables, inline tables and the last array-of-tables element, key by key. |
| TOML-GET-3 | For every parsed document, a key reads the same whether it was written bare, quoted or dotted. |
| TOML-READ-1 | `string`, `digits` and `flag` read their kind, span or owned, and are `""` or `false` on every other kind. |
| TOML-BUILD-1 | Every value built only through the builders is renderable. |
| TOML-TRUST-1 | The Bend checker is sound. |
| TOML-TRUST-2 | The proof-gate runner accepts only an exact `All terms check.` first line. |

## The gate and the linter on eztoml itself

| Check | Result |
| :---- | :---- |
| `bend eztoml/PROOF.bend --check-only` | first line `All terms check.`, exit 0, 35 s |
| bolt v0.4.0 (the pin) over the tree | `clean`. v0.4.0 has no `trace` and its `closed` is off in `bolt.bend` ("a closed equality is a computed document, which is what these laws are"), so `clean` says nothing about laws |
| bolt v0.4.0 with `closed` at error | 16 findings, one per closed law |
| bolt v1.7.0 with the repo's `bolt.bend` | 703 errors: 578 S004 (one-letter parameter names), 109 S003 (wrapped def headers), 16 L001 (defs no quantified law reaches: 11 lemma proofs in `eq.bend`, 3 in `bench/`, 2 in `examples/`) |
| bolt v1.7.0 with `closed` and `trace` at error | the same plus 16 L002 (closed laws) and one L005 (`Cannot read SPEC.md`) |

`nix flake check` could not be run here (no nix in the audit environment); the three checks above are what it runs, run directly with the pinned binaries. The hub (`hub.bend-lang.com`) was not reachable from the audit environment, so nothing below says what the hub serves.

## Summary

| File | Laws | Quantified | Closed | Quantified proved by `{==}` or rewrite-then-`{==}` |
| :---- | ---: | ---: | ---: | ---: |
| `eztoml/LAWS.bend` | 37 | 21 | 16 | 19 |
| `eztoml/eq.bend` | 14 | 14 | 0 | 0 (all lemmas) |

**What eztoml proves today.** Two things about behavior: `get` finds a pair that is first in its table (`get_first`), and the empty string is not a bare key (`bare_needs_a_char`). Every other quantified law restates a definition: the eight builders are constructors, `root` and `bad` are field reads, `string`, `digits` and `flag` read the value a builder made (`string_of` covers `VStr`, not the `VSpan` that `parse` produces for every plain string), `at` of one key is `get`, and `key` picks between two defs by `bare`. `parse_empty` is quantified over a string its premise pins to `""`, so it is one input. The 16 closed laws are the only evidence for the README's "Compliance" section, which says `nix flake check` "proves" the listed toml.abnf productions; each checks a handful of fixed documents, pins the renderer's layout and the error wording, and would pass a parser that breaks on any other input. Nothing is proved about `parse` on any nonempty text, about `render` on any nonempty document, or about the two together, and the round trip is the guarantee ez is waiting for (ez's SPEC.md, EZ-DOC-1 and EZ-LED-4: "when ez moves to eztoml 0.2.x, the text layer rests on eztoml's own proved round trip").

## Inventory: `eztoml/LAWS.bend`

| Law | Kind | Proof | Claim | Points toward |
| :---- | :---- | :---- | :---- | :---- |
| `get_first` | Q | struct | `get(VPair{name, v} <> rest, name)` is `Found{v}`: a pair at the head of the rows is found | TOML-GET-1 (the head case only) |
| `bare_needs_a_char` | Q | rewrite | `bare(s)` is false when `s` is empty; the premise pins `s` to `""` | TOML-KEY-1 (one input) |
| `key_is_bare_when_it_can` | Q | rewrite | `key(s) == s` when `bare(s)` | none (wiring); TOML-KEY-2 needs the read-back half |
| `key_is_quoted_when_it_must` | Q | rewrite | `key(s) == key.basic(s)` when not `bare(s)` | none (wiring) |
| `parse_empty` | Q | struct | `parse("")` is `Doc{"", []}`; the premise pins `s` to `""` | TOML-TEXT-1 (one input) |
| `render_empty` | Q | `{==}` | `render(Doc{bad, []})` is `""` | none (definitional) |
| `string_of` | Q | `{==}` | `string(VStr{t}) == t` | TOML-READ-1 (owned only; `parse` makes `VSpan`) |
| `digits_of` | Q | `{==}` | `digits(VInt{s, t}) == t` | none (definitional) |
| `flag_of` | Q | `{==}` | `flag(VBool{b}) == b` | none (definitional) |
| `at_one` | Q | `{==}` | `at(rows, [k]) == get(rows, k)` | none (wiring) |
| `at_empty` | Q | `{==}` | `at(rows, [])` is `Miss` | none (definitional) |
| `root_rows` | Q | `{==}` | `root(Doc{b, rows}) == rows` | none (definitional) |
| `bad_text` | Q | `{==}` | `bad(Doc{t, rows}) == t` | none (definitional) |
| `str_builds` | Q | `{==}` | `str(t) == VStr{t}` | none (definitional) |
| `integer_builds` | Q | `{==}` | `integer(s, t) == VInt{s, t}` | none (definitional) |
| `float_builds` | Q | `{==}` | `float(s, t) == VFlo{s, t}` | none (definitional) |
| `boolean_builds` | Q | `{==}` | `boolean(b) == VBool{b}` | none (definitional) |
| `array_builds` | Q | `{==}` | `array(xs) == VArr{xs}` | none (definitional) |
| `inline_builds` | Q | `{==}` | `inline(rows) == VInl{rows}` | none (definitional) |
| `table_builds` | Q | `{==}` | `table(p, rows) == VHead{p, rows}` | none (definitional) |
| `pair_builds` | Q | `{==}` | `pair(k, v) == VPair{k, v}` | none (definitional) |
| `toml_comment` | C | `{==}` | three one-line documents with comments render as expected; one key reads `v` | TOML-TEXT-1 (`comment`); pins layout |
| `toml_bool` | C | `{==}` | `true`/`false` render and read; `True` is refused | TOML-TEXT-1 (`boolean`); pins wording |
| `toml_string` | C | `{==}` | eight fixed strings over the four string forms read or render as expected; `\q` is refused | TOML-STR-1, TOML-STR-2; pins layout and wording |
| `toml_integer` | C | `{==}` | fixed decimal, hex, octal, binary and underscore integers render in decimal; nine malformed ones are refused | TOML-NUM-1; pins wording |
| `toml_float` | C | `{==}` | fixed floats keep their spelling apart from a leading `+`; four malformed ones are refused | TOML-NUM-2; pins wording |
| `toml_table` | C | `{==}` | eleven fixed table and dotted-key documents render as expected | TOML-TEXT-1 (`std-table`, `dotted-key`), TOML-RT-2; pins layout |
| `toml_inline` | C | `{==}` | three inline tables render; three malformed ones are refused | TOML-TEXT-1 (`inline-table`); pins wording |
| `toml_array` | C | `{==}` | three arrays render | TOML-TEXT-1 (`array`); pins layout |
| `toml_aot` | C | `{==}` | two arrays of tables render; mixing `[[t]]` and `[t]` is refused | TOML-TEXT-1 (`array-table`); pins wording |
| `toml_datetime` | C | `{==}` | fixed datetimes of the four forms render; `07:32:00Z` is refused | TOML-TIME-1; pins wording |
| `toml_invalid` | C | `{==}` | eight fixed invalid documents give the expected message | TOML-TEXT-1; pins wording |
| `toml_miss` | C | `{==}` | `get` of an absent key in `a = 1` is `Miss` | TOML-GET-1 |
| `toml_keyval` | C | `{==}` | two pairs on a line, and a pair with no value, are refused | TOML-TEXT-1 (`keyval`); pins wording |
| `toml_dot` | C | `{==}` | six dotted and quoted keys render as expected | TOML-GET-3, TOML-KEY-2; pins layout |
| `toml_reopen` | C | `{==}` | a table defined by dotted keys is not reopened by a header | TOML-TEXT-1 (the prose rule); pins wording |
| `toml_range` | C | `{==}` | integers at and past the signed 64-bit limits | TOML-NUM-1; pins wording |

## Inventory: `eztoml/eq.bend`

All 14 are quantified and proved structurally in the same file, which PROOF.bend imports, so the gate checks them. They are the Base facts the proofs need: `bool_cmp_self`, `word_cmp_self`, `u32_cmp_self`, `char_cmp_self`, `string_cmp_self`, `string_eq_self`, `char_eq_self`, `and.left`, `and.right`, `not.true`, `starts_nil`, `starts_append`, `append_nil`, `append_assoc`. Points toward: none (helper). They stay as a lemma module, as ez's `check/str.bend` does. bolt v1.7.0's `coverage` reports 11 of their proof defs as reached by no quantified law, because the proofs are defs that nothing but the checker names; the rollout marks them as the lemma module they are rather than adding laws for them.

## Coverage by requirement

| Requirement | Quantified laws today | Closed laws today |
| :---- | :---- | :---- |
| TOML-RT-1, TOML-RT-2, TOML-RT-3 | none | `toml_table` (layout only) |
| TOML-TEXT-1 | `parse_empty` (one input) | 10 |
| TOML-TEXT-2 | none | none |
| TOML-KEY-1 | `bare_needs_a_char` (one input) | none |
| TOML-KEY-2 | `key_is_bare_when_it_can`, `key_is_quoted_when_it_must` (wiring, no read-back) | `toml_dot` |
| TOML-STR-1, TOML-STR-2 | none | `toml_string` |
| TOML-NUM-1, TOML-NUM-2 | none | `toml_integer`, `toml_float`, `toml_range` |
| TOML-TIME-1 | none | `toml_datetime` |
| TOML-GET-1 | `get_first` (head only) | `toml_miss` |
| TOML-GET-2 | `at_one`, `at_empty` (wiring) | none |
| TOML-GET-3 | none | `toml_dot` |
| TOML-READ-1 | `string_of`, `digits_of`, `flag_of` (owned values only) | none |
| TOML-BUILD-1 | the eight `*_builds` (definitional) | none |

## What each entry point reads

eztoml is a library with no IO in `eztoml/`. `parse` reads only its text argument, `render` only its document, and every reader only its arguments: there is no environment, file, clock or network read, and no fuel. The only IO in the repository is `examples/demo/main.bend` (prints one fixed document) and `bench/main.bend` (reads and writes files the bench names). Neither is part of the library, so neither gets a row; they are marked `# noqa: L001 IO` when `coverage` is turned on.

The one thing a caller reads that is not an argument is the package hash in the README's import line. See the findings below.

## Findings

Each finding is "Confirmed" (run against a binary built from this tree, with the command) or "by reading" (file and line). Findings are recorded here, not resolved; the RFC carries a REVIEW item for each one a requirement depends on.

### Bugs

- **The README's build fails on a fresh clone.** Confirmed: in a directory made by `git archive HEAD`, `bend examples/demo/main.bend -o bin/demo.bin` fails with `ld: cannot open output file …/bin/demo.bin: No such file or directory`, and bend exits 0. With `mkdir -p bin` first the demo builds and prints the expected document. The same bug ez had.
- **The README imports a different package.** Confirmed by hashing: the README's `import 0x04b9afdd6d6a56039c5ce6dfb1e55294/main.bend` is v0.1.0 (`ea1a73f`, the scaffold: `main.bend` plus `toml.bend`, a sectioned string-only document). That package has no `get`, `at`, `string` or `root`, and its `render` takes a list of sections, so the README's own example does not type-check against the hash it names. The tree at `d3c1356` hashes to `0x60bccc8edd34707613da7f8d2b8bfd47` by ez's rule (`"0x"` and the first 32 hex digits of the sha256 of the manifest), which was checked by reproducing v0.1.0's hash from the manifest in ez's lock. Whether the hub holds it could not be checked from here.

### Behavior the code guarantees that no requirement mentions

- `get` returns the first pair of a name (`main.bend:1850`); with duplicate keys refused by `parse`, this only matters for documents built by hand.
- `render` writes every table's direct keys before its sub-tables and arrays of tables (`render.both`, `main.bend:5039`), so a document written in any order comes back in one canonical order, and dotted keys come back as `[table]` headers (`a.b = 1` renders `[a]\nb = 1`). The closed laws record this but nothing states it.
- `render` normalizes numbers: hex, octal and binary integers and underscores come back in decimal, a leading `+` is dropped from integers, floats, `+inf` and `+nan`, and float spelling is otherwise kept (`toml_integer`, `toml_float`).

### Behavior that looks accidental

- `bare` is ASCII-only (`Char.is_alpha` is `A-Z` or `a-z` in Base), as TOML v1.0.0 requires. By reading.
- Table headers are written as `"[" ++ path ++ "]"` with the stored path, with no call to `key` (`render.go` and `render.head`, `main.bend:4908`, `4957`), while pair keys go through `key`. Whether a header whose name needed quotes reads back depends on what the parser stores in `path`.
- The builders accept any `Val`, including shapes `parse` never makes (a `VHead` outside a `VPair`, a `VAot` outside a `VAots`, a table inside an array, a `VPair` inside an array), and `render` writes something for each. `table(path, rows)` writes `path` verbatim as the header, so the caller must quote it.

### Requirements with no corresponding code

- None beyond the README's "proves" claim, which describes closed laws.
