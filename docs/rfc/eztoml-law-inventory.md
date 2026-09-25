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
| TOML-RT-1 | Headline. For every well-formed document `d`, `parse(render(d))` has no error and is `same` as `d`. |
| TOML-RT-2 | For every text that parses, `render` of the result parses back `same`, and rendering that gives the same bytes. |
| TOML-RT-3 | Every document `parse` returns with no error is well-formed. |
| TOML-TEXT-1 | `parse(t)` has no error exactly when `t` matches toml.abnf's `toml` rule and breaks none of the specification's rules on defining keys and tables. |
| TOML-TEXT-2 | The key and table rules, one by one: a key, table or array of tables is defined once, and dotted keys never extend a table a header defined, or the reverse. |
| TOML-KEY-1 | `bare(s)` holds exactly when `s` is nonempty and every character is `A-Za-z0-9_-`. |
| TOML-KEY-2 | `key(s)` is `s` when `bare(s)`, and otherwise a basic string that reads back as `s`. |
| TOML-KEY-3 | In a parsed document, a key reads the same however it was written: bare, basic, literal, or as a dotted segment or header. |
| TOML-STR-1 | Every string form reads back as its characters, each escape decoded. |
| TOML-STR-2 | `render` writes a string as a basic string escaping exactly `"`, `\` and the controls, which reads back as the text. |
| TOML-NUM-1 | Integers: every form the grammar allows reads to its sign and decimal digits, and only those, range checked to signed 64 bits. |
| TOML-NUM-2 | Floats keep their spelling, apart from the stated normalizations. |
| TOML-TIME-1 | Datetimes: the four forms read to their fields, with RFC 3339's range checks. |
| TOML-GET-1 | `get(rows, k)` is the value of the first pair named `k`, and `Miss` when there is none. |
| TOML-GET-2 | `at(rows, path)` walks tables and inline tables key by key, and misses at anything else. |
| TOML-READ-1 | `string`, `digits` and `flag` read their kind, span or owned, and give `""`, `""` and `false` for every other kind. |
| TOML-TRUST-1 | The Bend checker is sound. |
| TOML-TRUST-2 | The proof-gate runner accepts only an exact `All terms check.` first line. |
| TOML-TRUST-3 | A caller's bytes reach `parse` as the code points of their UTF-8 decoding. |

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
| `toml_dot` | C | `{==}` | six dotted and quoted keys render as expected | TOML-KEY-3, TOML-KEY-2; pins layout |
| `toml_reopen` | C | `{==}` | a table defined by dotted keys is not reopened by a header | TOML-TEXT-1 (the prose rule); pins wording |
| `toml_range` | C | `{==}` | integers at and past the signed 64-bit limits | TOML-NUM-1; pins wording |

## Inventory: `eztoml/eq.bend`

All 14 are quantified and proved structurally in the same file, which PROOF.bend imports, so the gate checks them. They are the Base facts the proofs need: `bool_cmp_self`, `word_cmp_self`, `u32_cmp_self`, `char_cmp_self`, `string_cmp_self`, `string_eq_self`, `char_eq_self`, `and.left`, `and.right`, `not.true`, `starts_nil`, `starts_append`, `append_nil`, `append_assoc`. Points toward: none (helper). They stay as a lemma module, as ez's `check/str.bend` does. bolt v1.7.0's `coverage` reports 11 of their proof defs as reached by no quantified law, because the proofs are defs that nothing but the checker names; the rollout marks them as the lemma module they are rather than adding laws for them.

## Coverage by requirement

| Requirement | Quantified laws today | Closed laws today |
| :---- | :---- | :---- |
| TOML-RT-1, TOML-RT-2, TOML-RT-3 | none | `toml_table` (layout only) |
| TOML-TEXT-1 | `parse_empty` (one input) | 10 |
| TOML-TEXT-2 | none | `toml_aot`, `toml_invalid`, `toml_reopen` |
| TOML-KEY-1 | `bare_needs_a_char` (one input) | none |
| TOML-KEY-2 | `key_is_bare_when_it_can`, `key_is_quoted_when_it_must` (wiring, no read-back) | `toml_dot` |
| TOML-STR-1, TOML-STR-2 | none | `toml_string` |
| TOML-NUM-1, TOML-NUM-2 | none | `toml_integer`, `toml_float`, `toml_range` |
| TOML-TIME-1 | none | `toml_datetime` |
| TOML-GET-1 | `get_first` (head only) | `toml_miss` |
| TOML-GET-2 | `at_one`, `at_empty` (wiring) | none |
| TOML-KEY-3 | none | `toml_dot` |
| TOML-READ-1 | `string_of`, `digits_of`, `flag_of` (owned values only) | none |

## What each entry point reads

eztoml is a library with no IO in `eztoml/`. `parse` reads only its text argument, `render` only its document, and every reader only its arguments: there is no environment, file, clock or network read, and no fuel. The only IO in the repository is `examples/demo/main.bend` (prints one fixed document) and `bench/main.bend` (reads and writes files the bench names). Neither is part of the library, so neither gets a row; they are marked `# noqa: L001 IO` when `coverage` is turned on.

The one thing a caller reads that is not an argument is the package hash in the README's import line. See the findings below.

## How the code was exercised

Besides the gate and the linter, the audit ran the real parser and renderer, compiled with the pinned bend, three ways. None of it is committed, and none of it is evidence for a requirement (RFC, Abandoned Ideas); it is how the verdicts below were checked.

- **toml-test.** Every case of [toml-test](https://github.com/toml-lang/toml-test)'s TOML 1.0.0 list: 208 valid documents, whose tagged JSON must match, and 501 invalid ones, which must be refused. A driver printed `bad`, the tagged JSON of the document and `render` of it, then the same three for `parse(render(parse t))`.
- **A differential fuzzer against Python's `tomllib`.** About 43,000 generated documents, 20,000 of them over a small key set to force table collisions: `parse` against `tomllib.loads`, `tomllib.loads` of `render`, and the round trip.
- **Targeted inputs** for keys, strings, numbers, datetimes, tables and the readers, below.

| Measure | Result |
| :---- | :---- |
| toml-test valid documents accepted with the expected values | 203 of 208; every accepted one had the expected values |
| toml-test invalid documents refused | 472 of 501 |
| round trip on the 203: `render` reparses with no error, the same values, and rendering again gives the same bytes | 203 of 203; `tomllib` reads the same values from `render`'s output for all 203 |
| round trip on fuzzed valid documents | no failure; every failure the fuzzer found was a valid document refused or an invalid one accepted |
| round trip after an invalid document was accepted | fails: `a = 0_0.5` renders `a = 00.5`, which does not reparse (R-I6 below) |

## Findings

Each finding is "Confirmed" (run against a binary built from this tree) or "by reading" (file and line). Findings are recorded here, not resolved; the RFC carries a REVIEW item for each one a requirement depends on. The IDs (V, I, R) are used by the RFC's decided behavior changes.

### Bugs

- **The README's build fails on a fresh clone.** Confirmed: in a directory made by `git archive HEAD`, `bend examples/demo/main.bend -o bin/demo.bin` fails with `ld: cannot open output file …/bin/demo.bin: No such file or directory`, and bend exits 0. With `mkdir -p bin` first the demo builds and prints the expected document. The same bug ez had.
- **The README imports a different package.** Confirmed by hashing: the README's `import 0x04b9afdd6d6a56039c5ce6dfb1e55294/main.bend` is v0.1.0 (`ea1a73f`, the scaffold: `main.bend` plus `toml.bend`, a sectioned string-only document). That package has no `get`, `at`, `string` or `root`, and its `render` takes a list of sections, so the README's own example does not type-check against the hash it names. The tree at `d3c1356` hashes to `0x60bccc8edd34707613da7f8d2b8bfd47` by ez's rule (`"0x"` and the first 32 hex digits of the sha256 of the manifest), which was checked by reproducing v0.1.0's hash from the manifest in ez's lock. Whether the hub holds it could not be checked from here.

Valid TOML that `parse` refuses. All confirmed:

| ID | Input | What happens | toml-test cases |
| :---- | :---- | :---- | :---- |
| V1 | `a = """x""""` and `a = '''x''''`: one or two quotes just before a multi-line string's closing delimiter | `newline required`: the string closes at the first `"""` | spec-1.0.0/string-4, string-7, string/multiline-quotes, string/raw-multiline |
| V2 | `t = {b.c = 1, b.d = 2}`: two dotted keys with a shared prefix in one inline table, also inside arrays and under a header | `inline table is closed` | inline-table/key-dotted-02, and about 50 fuzzer failures |
| R1 | `a=""` or `a=''` as the last line, with no newline after it | `unclosed`; `a="x"`, `a=1` and `a=[]` without a newline are fine | none (found by the fuzzer) |
| R2 | `[[a]]\n[a.b]\n[[a]]\n[a.b.c]\n[a.b]` | `duplicate table`: the headers a document has defined are one list of path strings, shared by every element of an array of tables | none |

Invalid TOML that `parse` accepts. All confirmed:

| ID | Input | What happens | toml-test cases |
| :---- | :---- | :---- | :---- |
| I1 | `[a.b]\nz=9\n[a]\nb.t=1`; `[[t.arr]]\n[t]\narr.v=1` | dotted keys add to a table or array of tables a header defined | array/extend-defined-aot, table/append-with-dotted-keys-01, -02, -03, -08 |
| I2 | `a = 1 # \x01`, and each other control but tab in a comment | accepted | control/comment-cr, -del, -ff, -lf, -null, -us |
| I3 | `a = "x"\rb = 1` | a lone CR ends a line | control/bare-cr |
| I4 | `d = 2100-02-29`, `d = 2000-02-30` | the day is checked against 31 only, not the month or leap years | datetime, local-date and local-datetime feb-29 and feb-30 (6) |
| I6 | `a = -+1` reads as **+1**; `a = ++99` as 99; `a = -+1.5` as `+1.5`; `0_0`, `0_1`, `-0_1`, `+0_1` read as numbers | a second sign is dropped, and a leading zero hidden by `_` is not caught. `-+1` silently changes the value | integer/double-sign-plus, leading-zero-03, leading-zero-sign-03 |
| R-I6 | `a = 0_0.5`, `a = 0_1e2` | read as float text `00.5`, `01e2`; `render` writes `a = 00.5`, which `parse` refuses: the one round-trip failure found | none |
| I7 | `key =\n1` | the value may start on the next line | key/newline-06 |
| I8 | `[ [t]]` | read as `[[t]]` | table/llbrace |
| R3 | `[a"b"]`, `[a.b"c"]`, `[[x'y']]` | a bare header segment followed by a quoted one is accepted and the bare part dropped: `[a"b"]` is table `b`. `a"b" = 1` is correctly refused | none |
| I5 | invalid UTF-8 in a string or comment | not a parser finding: Bend's `File.read` decodes the bytes and puts U+FFFD for each bad one before `parse` sees a `String` (the driver's code dump shows 65533). Six toml-test cases (encoding/bad-codepoint, bad-utf8-in-*) | encoding/* (6) |

### Behavior the code guarantees that no requirement mentions

- `get` returns the first pair of a name (`main.bend:1850`); with duplicate keys refused by `parse`, this only matters for documents built by hand. A key written quoted (`"a.b" = 1`) is found by `get(root, "a.b")` and is distinct from the dotted `a.b = 2`, which `at(root, ["a", "b"])` finds. Confirmed.
- How a table is stored: a table is `VPair{name, VHead{path, rows}}` in its parent's rows, where `path` is the full dotted path with each segment written by `key`; a table made by dotted keys is a `VHead` too, and inside an inline table a `VInl`. An array of tables is `VPair{name, VAots{path, elems}}` with each element a `VAot{path, rows}`. Rows are kept newest first while reading and put back in document order at the end (`rows.seal`). Confirmed with the driver.
- `render` writes every table's direct keys before its sub-tables and arrays of tables (`render.both`, `main.bend:5039`), so a document written in any order comes back in one canonical order. Dotted keys come back as `[table]` headers (`a.b = 1` renders `[a]\nb = 1`), and an implicit table gets its own header. Blank lines and comments are dropped. Confirmed.
- `render` normalizes numbers and datetimes: hex, octal and binary integers come back in decimal; underscores are dropped; a leading `+` is dropped from integers, floats, `+inf` and `+nan`; float spelling is otherwise kept (`1E+10`, `6.02e-023`); `-0`, `-0.0` and `-nan` are kept; a datetime's lowercase `t` and `z` and a space separator come back as `T` and `Z`, and fractions and `-00:00` are kept. Confirmed.
- `render` escapes a string or key's `"`, `\` and controls (the short escapes where TOML has one, `\u00XX` otherwise, DEL as `\u007f`) and writes every other character raw, astral ones included. Keys holding `=`, `"`, `\`, a newline, a control, `.`, nothing, `é` or an emoji render quoted and read back. Confirmed.
- A multi-line basic string keeps a CRLF inside it as `\r\n` in the value. Confirmed.

### Behavior that looks accidental

- `at` cannot descend into an array of tables: `at.rows` (`main.bend:5069`) reads `VHead`, `VInl` and `VAot` rows but not `VAots`, so `at(root, ["arr", "z"])` is `Miss` although `arr` holds tables. Confirmed. The README says only that `at` "finds one by a dotted path".
- `string`, `digits` and `flag` answer `""`, `""` and `false` for a value of another kind, which is also what they answer for an empty string, and `false`. By reading (`main.bend:5043` to `5066`).
- Table headers are written as `"[" ++ path ++ "]"` with the stored path (`main.bend:4908`, `4957`). For a parsed document the path is already written by `key`, so it reads back (confirmed for `["x\ny"]`, `[a."b.c"]`, `[[""]]`). For a hand-built one, `table(path, rows)` writes `path` verbatim, so the caller must quote it, and must keep it equal to the keys above it.
- The builders accept any `Val`, including shapes `parse` never makes (a `VHead` outside a `VPair`, a `VAot` outside a `VAots`, a table inside an array, a `VPair` inside an array, an integer whose digits are not digits), and `render` writes something for each, often not TOML. By reading `render.go`.
- Parse time grows with the square of the keys in one table and of the tables in a document: 2,000 keys in one table parse in 0.39 s and 8,000 in 5.4 s; 2,000 headers in 0.63 s and 8,000 in 10.2 s; a generated 2 MB mixed document in 65 s. Long strings, arrays and arrays of tables are linear. The duplicate checks scan lists (`rows.find`, `heads.has`). Confirmed with the compiled driver. Interpreted (`bend file.bend`), a 400-key document takes 47 s.

### Requirements with no corresponding code

- The README's "Compliance" says `nix flake check` proves the listed productions; what it runs are the closed laws above.

## Rollout progress

One row per step of the RFC's Rollout, kept current in every change.

| Step | State | What landed |
| :---- | :---- | :---- |
| Docs | done | README: `mkdir -p bin` before the build; the import line names v0.2.2's hash, `0x60bccc8e…` |
| Lint first | done | bolt v1.7.0 as a `[tools.bolt]` pin in ez.toml and ez.lock.toml, built by `ez.mkLint { src = self; }`; the ez flake input at `df6d616`; the bolt flake input removed; 578 S004 and 109 S003 fixed; bench and demo marked `noqa: L001`; `laws` at warn. Byte-identical parser output before and after on 6,784 documents |
| Layout | done | `main.bend` at the root, whole (Bend does not re-export an imported type); LAWS.bend and PROOF.bend beside it; the lemmas in `src/eq.bend`; ez.toml's entry is `main.bend` |
| One | done | SPEC.md; the 16 closed laws and 16 definitional laws deleted with their helpers; the five kept laws tagged (`get_first` TOML-GET-1, `bare_needs_a_char` TOML-KEY-1, `key_is_bare_when_it_can` and `key_is_quoted_when_it_must` TOML-KEY-2, `string_of` TOML-READ-1); `closed`, `unsafe` and `trace` at error; README's Compliance section replaced by a pointer to SPEC.md. The gate now takes 0.4 s instead of 35 s. TOML-KEY-1 (`bare_is_unquoted_key`, over a transcription of toml.abnf's `unquoted-key`), TOML-GET-1 (frame laws for skipping, `get_finds_first`, `get_misses`), TOML-GET-2 (seven laws; the row reworded to count a hand-built `VAot` as a table, which is what `at` does) and TOML-READ-1 (spans, the other kinds) proved; each new proof fails when replaced by `{==}` or a wrong term. 29 lemmas added to `src/eq.bend` (Base only), among them `str.eq` agreeing with `String.eq` |
| Fixes | done | I6 and R-I6 fixed (a second sign and `0_` refused; `-+1` no longer reads as 1): seven laws over the numeral scan and `word.val`, tagged TOML-NUM-1 and TOML-NUM-2; toml-test invalid 472 to 475. I4 fixed (the day bounded by the month and Gregorian leap years): `date_day_in_month` and `date_day_past_month` over RFC 3339 §5.7 transcribed, tagged TOML-TIME-1; invalid 475 to 481. Nine corpus documents change, all nine the toml-test cases the fixes target; the round trip still holds on 203 of 203. Each proof fails when replaced by `{==}`, and each planted original bug fails the gate on the new law. I2, I3 and I7 fixed (controls in comments, a lone CR, a value on the next line): `fail_stays` (a failed scanner keeps its first error to the end, in both read modes) and five step laws in premise form over every scanner state they name, tagged TOML-TEXT-1; invalid 481 to 489. V1 and R1 fixed (quotes before a multi-line closing delimiter; an empty string ending the text): six parse-level laws tagged TOML-STR-1; valid 203 to 207 of 208. 64 corpus documents change in all, each one a fix's target: the toml-test cases, two multi-line strings holding a lone CR, five already-refused documents whose message is now "newline before value", and 29 fuzzed documents ending in `= ""` or `= ''` (26 now parse; 3 now report the real error that "unclosed" hid). The round trip holds on 207 of 207. Timing unchanged (str2000 17 ms, flat2000 0.70 s). I1 fixed (a dotted key that reaches a table a header defined, or an array of tables, is refused; each entry of the scanner's `heads` now records whether a header or a dotted key defined its path): six laws tagged TOML-TEXT-2. R2 fixed (`[[a]]` forgets the tables defined under `a.` in the element before): two laws tagged TOML-TEXT-2. V2 fixed (a table a dotted key makes stays open while its inline table is read, and is closed with it): three laws tagged TOML-TEXT-1 and TOML-TEXT-2. R3 and I8 fixed (a quote after a bare header segment, and `[ [`, are refused): four laws tagged TOML-TEXT-1 and TOML-KEY-3. toml-test after all fixes: valid 208 of 208, invalid 495 of 501 (the six left are invalid UTF-8, TOML-TRUST-3), round trip 208 of 208. 130 corpus documents differ from `d3c1356`; the 66 the table fixes change all agree with Python's `tomllib` on accept or refuse. `wf(parse(t))` holds on all 3,813 documents that parse. One cost: 2,000 tables with two dotted keys each parse 11% slower (2.9 s to 3.2 s); the other timing files are unchanged |
| Two | in progress | `wf` public in `main.bend` (holds of all 3,774 corpus documents that parse; false on 37 hand-built counterexamples); `same` and `own` in LAWS.bend with `same_refl`, `same_sym`, `same_own`, `same_swap`; TOML-STR-2 proved by 16 laws (per-character escapes, the map law `basic_escs`, `span_quote_basic` tying the span fast path to `key.basic`, and the renderer's string laws), each proof failing when replaced by `{==}` and seven planted bugs each failing the gate. No output changed. TOML-KEY-2 proved (`key_reads_back`: `parse(key(s) ++ " = 1")` is exactly one pair named `s`, for every string). The design doc [eztoml-roundtrip-proofs.md](eztoml-roundtrip-proofs.md) plans TOML-RT-1, RT-3, RT-2 and KEY-3 as ten work packages (about 14,000 to 18,000 lines of proof); its spike also proved `render_parse_plain_pair` (a one-pair document with a plain string reads back, a partial law of TOML-RT-1) and found that a plain string of 2^32 characters or more does not read back (the span count is a U32), which the doc's REVIEW-R1 puts to the maintainer. The gate takes 6 s |
| Three | in progress | WP0 landed: the quoted-segment lemmas (`qs.*`) read key and header segments alike, `Eq.ctl.all` replaces the copied control enumerations, and seven U32 and word lemmas moved to `src/eq.bend`. The gate takes 7.4 s. WP-W landed: twelve contract laws for `tree.walk` (a put, a table header, an array-of-tables header, a failed walk, `rows.seal`, and reading back a table the walk set), four of them tagged TOML-TEXT-2; each fails the gate when its proof is replaced by `{==}`, and planted walk bugs (a put at the tail, `[[a]]` starting empty, an error cleared, a seal that does not recurse) each fail on a new law. The gate takes 7.5 s. WP-H landed: `[..]` and `[[..]]` headers with bare or basic-quoted segments read back from the line-start state, six laws tagged TOML-KEY-3 (1,190 lines of proof); each top-level proof fails when replaced by `{==}`, and eight planted header bugs (a segment dropped, a dot that pushes nothing, `]]` read as `]`, `[[` not marking an array of tables, the walk job swapped) each fail the gate. The gate takes 8.1 s. WP-S landed: every rendered string reads back as a root pair's value, an array item and an inline table's value (three laws tagged TOML-STR-1, 2,668 lines of proof); twenty proofs each fail when replaced by `{==}`, and six planted reader bugs each fail on a WP-S proof, one of them (a copied span dropping a character) caught by nothing before. The gate took 12.3 s; computing each control's escape once (`ctl.esc.lit`, `ctl.esc.all`) brought it back to about 7 s. WP-N landed: booleans, integers, floats and datetimes read back as themselves, by classifier laws tagged TOML-NUM-1, TOML-NUM-2 and TOML-TIME-1 and by `scalar_reads_back` in the scanner's premise form; `src/arith.bend` ports ezjson's U32 arithmetic for the year. Every new law fails when replaced by `{==}`, and nine planted renderer and reader bugs (`True`, a lost minus sign, a digit dropped, month and day swapped, a fraction's dot dropped) each fail the gate. The gate takes about 15 s. WP-K3 landed ten laws tagged TOML-KEY-3 (literal keys, dotted keys with blank space, the put a dotted key makes and `at` finding it, header segments spelled any way); the row stays pending for other basic-string spellings, inline-table keys, other values and whole documents. Each law fails when replaced by `{==}`, and six planted key bugs each fail on a new proof. The gate takes about 16 s. WP-C landed: every well-formed value `render` writes reads back in a value position, arrays and inline tables nested to any depth (`value_reads_back`, `pass_value`), and the partial law `render_parse_value_pair` tagged TOML-RT-1 (a one-pair document with any non-table value reads back `same` as itself). Each law fails when replaced by `{==}` or a wrong term, and four planted reader bugs (a space after `,` refused, array items reversed, a nested closer clearing the stack, an inline table not sealed) each fail on a WP-C proof. The gate takes about 17 s. WP-D (document induction, TOML-RT-1) next |
| Four | not started | |
