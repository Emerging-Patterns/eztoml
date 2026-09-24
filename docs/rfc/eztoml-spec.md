# eztoml: what it guarantees, and how we prove it

Read at `d3c1356` on main (release 0.2.2), bend 2.0.25, bolt v0.4.0 (the pin) and v1.7.0 (current).

## Draft Status

**State:** Accepted. Every REVIEW item was accepted as recommended by the maintainer in one reply.

We wrote this draft from the code at `d3c1356`, the evidence in [eztoml-law-inventory.md](eztoml-law-inventory.md), and the positions that ez, bolt and ezjson reached when they went through the same process ([ez-spec.md](https://github.com/Emerging-Patterns/ez/blob/master/docs/rfc/ez-spec.md), [bolt-spec.md](https://github.com/Emerging-Patterns/bolt/blob/main/docs/rfc/bolt-spec.md), [ezjson-spec.md](https://github.com/Emerging-Patterns/ezjson/blob/main/docs/rfc/ezjson-spec.md)). We checked every verdict against the code. Most were also confirmed by running a parser and renderer compiled from this tree against toml-test and a fuzzer (see the inventory, "How the code was exercised"). Each item below was put to the maintainer with its evidence and a recommendation, and each one also appears where its decision lives. REVIEW-1 and REVIEW-2 come first because the others depend on them.

**Items for review:**

- [x] <!-- REVIEW-1 (resolved): What is the public surface, and where does it live? Today everything is one 5,153-line `eztoml/main.bend`, so every internal def (`rows.find`, `render.pass`, the scanner states) can be imported, and nothing says which are promised. The header comment lists the interface: `parse`, `render`, `get`, `at`, `root`, `bad`, `string`, `digits`, `flag`, `str`, `integer`, `float`, `boolean`, `array`, `inline`, `table`, `pair`, `key`, with `bare` beside it. Recommend: the rows speak only about those defs, the new `wf` (REVIEW-3), and the types `Doc`, `Val`, `Hit`, `Sign`, `When`, `Date`, `Clock` and `Zone`; everything else is internal and carries no promise. Also recommend adopting the layout ezjson and shake use (current ez expects it): `main.bend` at the repository root as the whole interface, and the scanner, renderer and lemmas under `src/`. The move changes the entry a consumer's ledger records (`root = "eztoml"`, `entry = "eztoml/main.bend"` today). The only consumer we know of, ez, still pins v0.1.0 and will change its ledger anyway when it moves to 0.2.x, so now is the cheapest time. The move lands in its own PR at a minor release. Decided: accepted, then narrowed when we found that Bend does not re-export an imported type: with `Val`, `Hit` and `Doc` under `src/`, a consumer matching on them would have to import `src/` itself, and eztoml has no reader for a `Hit`, an array, a float, a datetime or a table, so every consumer matches. So the whole of `main.bend`, types and implementation, moved to the root unsplit; LAWS.bend and PROOF.bend sit beside it and the lemmas are `src/eq.bend`. Internal defs stay importable, and only SPEC.md's rows are promised. ezjson splits because its readers return `Maybe`, so its consumers need not match. -->
- [x] <!-- REVIEW-2 (resolved): The headline guarantee. Recommend TOML-RT-1: for every well-formed document `d`, `parse(render(d))` has no error and is `same` as `d`. It is what makes eztoml safe as a writer. It is the guarantee ez is waiting for: ez's EZ-DOC-1 and EZ-LED-4 say "when ez moves to eztoml 0.2.x, the text layer rests on eztoml's own proved round trip". And the code already keeps it on every input we tried (203 of 203 toml-test documents, and about 43,000 fuzzed ones). TOML-TEXT-1 (accepts exactly TOML v1.0.0) is the stronger conformance claim and by far the costliest proof. It stays pending, with partial laws from each conformance fix (REVIEW-6), until the grammar relation exists. Decided: accepted as recommended. -->
- [x] <!-- REVIEW-3 (resolved): What is a well-formed document? The builders are bare constructors, so they make shapes `parse` never produces, and `render` writes something that is not TOML for them: a `VHead` outside a `VPair`, a table inside an array, an integer whose digits are `abc`, a header path that disagrees with the keys above it (`table(path, rows)` writes `path` verbatim, so `table("a b", rows)` renders `[a b]`), a string holding a surrogate or a code point past U+10FFFF (written raw, which no UTF-8 file can hold), or two pairs of one name in a table. Recommend, as ezjson did: add a public `wf : Doc -> Bool` (and `wf.val`) that holds exactly for the shapes `parse` returns, and state TOML-RT-1 over it. `wf` checks that tables and arrays of tables appear only as a pair's value in a table's rows; that each `VHead` and `VAot` path is the parent's path, a `.`, and `key` of the pair's name; that keys in a table are distinct; that integer digits are decimal with no leading zero (apart from `0`) and within signed 64 bits; that float text matches the grammar with no sign and no `_`; that datetime fields are in range; and that every string and key holds only Unicode scalar values. The builders stay constructors, so nothing changes for existing callers. The alternatives are validating builders (ezjson's `num` returns `null` on a bad spelling), or a renderer that computes headers from the keys and ignores the stored path. Both are listed under Abandoned Ideas. New behavior (a new def), nothing breaks. Decided: accepted as recommended. -->
- [x] <!-- REVIEW-4 (resolved): Equality. A parsed plain string is a `VSpan` and a built one a `VStr`; `render` puts a table's keys before its sub-tables; and TOML says a table's pairs are in no particular order. So Bend's `==` on `Doc` is not TOML equality. Recommend, as ezjson did: define `same` in LAWS.bend as a specification helper, not a public def. It reads every span into a `VStr`, compares tables as maps from key to value (order ignored, keys distinct by `wf`), compares arrays and arrays of tables in order, and compares scalars by their fields as `parse` stores them (sign and decimal digits, sign and float text, datetime fields). A public `eq` is a Future Step. Not a behavior change. Decided: accepted as recommended. -->
- [x] <!-- REVIEW-5 (resolved): How far does the conformance claim go? The inventory measured 5 of 208 valid toml-test documents refused and 29 of 501 invalid ones accepted, plus four bugs toml-test does not cover (R1 to R3, R-I6). Recommend: TOML-TEXT-1 states the whole of TOML v1.0.0 (toml.abnf's `toml` rule, plus the specification's prose rules on defining keys and tables, which the ABNF cannot say), for texts of Unicode scalar values. TOML-TEXT-2 splits out the definition rules as their own row, because they are what the bugs are mostly about and they can be proved before the grammar relation exists. Invalid UTF-8 is out of scope: `parse` takes a `String`, and the reader decodes the bytes first (confirmed: Bend's `File.read` replaces bad bytes with U+FFFD). That boundary is TOML-TRUST-3, and the six `encoding/*` toml-test cases are not eztoml's. The grammar relation is TOML's ABNF transcribed one constructor per rule, as ezjson's `Derives` is for RFC 8259, and is planned in its own design doc. Decided: accepted as recommended. -->
- [x] <!-- REVIEW-6 (resolved): The conformance bugs. Recommend fixing every one (V1, V2, R1, R2, R3, I1 to I4, I6, R-I6, I7, I8 in the inventory), each as its own PR with master's binary against the branch's on the reproducer and the toml-test cases it names. None becomes a new row: TOML-TEXT-1 and TOML-TEXT-2 already state the behavior, and TOML-NUM-1, TOML-STR-1 and TOML-TIME-1 state the parts about values. Each fix lands with a quantified law tagged with the row it partly proves (for example "for every digit string `ds`, `a = -+` ++ `ds` is refused"), not a closed one. I6 goes first: `a = -+1` silently reads as `+1`, the only bug that changes a value instead of refusing or accepting a document. These are behavior changes, since documents that parsed stop parsing, but each one stops accepting only text TOML v1.0.0 says is invalid. Decided: accepted as recommended. -->
- [x] <!-- REVIEW-7 (resolved): `at` and arrays of tables. `at` does not descend into an array of tables: `at(root, ["fruit", "name"])` is `Miss` although `fruit` holds tables (`at.rows` ignores `VAots`). TOML's own header rule reads `[fruit.x]` after `[[fruit]]` as the last element, but a reader asking for `fruit.name` is ambiguous: toml++'s `at_path` needs an explicit index (`fruit[0].name`), and Rust's `toml` and `tomllib` have no path lookup at all. Recommend: keep `Miss`, state it in TOML-GET-2, and leave indexing into an array (a path segment that names an element) to Future Steps. Not a behavior change. Decided: accepted as recommended. Later, proving TOML-GET-2 found one more case: `at` goes on into a single element of an array of tables (`VAot`) when `get` finds one as a pair's value, which only a hand-built document has. The row was reworded to say so rather than change the code, since an element is a table; a whole array of tables (`VAots`) is still `Miss`. -->
- [x] <!-- REVIEW-8 (resolved): Readers of the wrong kind. `string`, `digits` and `flag` answer `""`, `""` and `false` for a value of another kind, which is also what they answer for an empty string, and `false`. serde's `as_str` returns `Option`; tomllib gives typed values. Recommend: keep them and state the defaults exactly (TOML-READ-1), since callers can match on `Val` (a public type) when they need to tell the cases apart. Not a behavior change. Decided: accepted as recommended. -->
- [x] <!-- REVIEW-9 (resolved): Error text. The closed laws pin the words of `bad` (`invalid number`, `unclosed`, `duplicate key`). Recommend: the rows speak of `bad` being empty or not, never of its words, so rewording touches no law, as ez and bolt decided. What the rows of a document with an error hold is unspecified. Not a behavior change. Decided: accepted as recommended. -->
- [x] <!-- REVIEW-10 (resolved): Retiring the laws. Recommend deleting all 16 closed laws, and their helpers (`again`, `why`, `read`, `str_at`, `dig_at`, `bit_at`, `path_at`), in the change that lands SPEC.md, as bolt and ezjson did, keeping the inventory's "points toward" column as the map. Of the 21 quantified laws, keep and tag the five that prove part of a row (`get_first` TOML-GET-1; `bare_needs_a_char` TOML-KEY-1; `key_is_bare_when_it_can` and `key_is_quoted_when_it_must` TOML-KEY-2; `string_of` TOML-READ-1) and delete the sixteen definitional ones (the eight builders, `root_rows`, `bad_text`, `render_empty`, `digits_of`, `flag_of`, `at_one`, `at_empty`, `parse_empty`), whose rows get real laws instead. eq.bend stays as the lemma module. The README's Compliance section is rewritten to point at SPEC.md. Decided: accepted as recommended. -->
- [x] <!-- REVIEW-11 (resolved): The bolt pin. The flake pins bolt v0.4.0 (`24b497e`), which has no `trace` or `coverage` and reports `clean` only because `closed` is off in bolt.bend. bolt v1.7.0 reports 703 errors: 578 S004 (one-letter parameter names), 109 S003 (wrapped headers), 16 L001 (11 lemma proofs in eq.bend, and the IO of `bench/` and `examples/`), then 16 L002 and one L005 once `closed` and `trace` are on. Recommend, as ezjson did: a lint-first PR that moves the pin to bolt v1.7.0 with `laws` at warn, fixes S003 and S004, and marks the IO defs `# noqa: L001 IO`. Then the SPEC.md PR turns `closed` and `trace` to error. Pure renames; no behavior change. Decided: accepted, with one change from the maintainer: bolt is not a flake input. It is a `[tools.bolt]` pin in ez.toml and ez.lock.toml, which `ez lock --upgrade --package bolt` fills, and `ez.mkLint { src = self; }` builds bolt from that pin. The ez flake input moves to a rev whose `mkLint` does so (`df6d616`). -->
- [x] <!-- REVIEW-12 (resolved): The README. Its build step fails on a fresh clone (no `bin/`), and its import line names `0x04b9afdd6d6a56039c5ce6dfb1e55294`, which is v0.1.0, a different API on which the README's own example does not type-check. `d3c1356` hashes to `0x60bccc8edd34707613da7f8d2b8bfd47`. Recommend: `mkdir -p bin` in the README, and the hash of the latest release checked with `ez` against the hub, in their own docs PR. We could not reach the hub from the audit environment. Decided: accepted as recommended. -->
- [x] <!-- REVIEW-13 (resolved): Parse time is quadratic in the keys of one table and in the number of tables (8,000 keys in one table: 5.4 s; a 2 MB document: 65 s). A law sees values, not time, so this is no row. Recommend: record it under Risks. A faster duplicate check, once TOML-TEXT-2 and TOML-RT-2 are proved, is a refactor mergeable on the gate alone. The files ez writes are tens of keys per table. Not a behavior change. Decided: accepted as recommended. -->

## Abstract

eztoml has 51 laws: 37 in `eztoml/LAWS.bend` and 14 lemmas in `eztoml/eq.bend`. Of the 37, 16 are closed, and 16 of the 21 quantified ones restate a definition. Passing the proof gate today tells us that the empty string is not a bare key, that `get` finds a pair at the head of a table, and that sixteen sets of fixed documents still render as they did. It tells us nothing about `parse` on any nonempty text or `render` on any nonempty document, although the README says `nix flake check` "proves" TOML v1.0.0 compliance. This RFC defines a specification for eztoml in the shape ez, bolt and ezjson use: every requirement is either **Proved** by a tagged quantified law or **Trusted** as a named assumption. It names the round trip as the headline, adds `wf`, deletes the closed laws, fixes the conformance bugs the audit found, and states conformance to TOML v1.0.0 as a row that is honest about being pending.

## Glossary

| Term | Meaning |
| :---- | :---- |
| document | a `Doc{bad, rows}`: the first error (`""` when there is none) and the root table's rows |
| value | a `Val`; a table is `VPair{name, VHead{path, rows}}` in its parent's rows, an array of tables `VPair{name, VAots{path, [VAot{path, rows}, ...]}}`, an inline table `VInl`, a plain string from the source a `VSpan` |
| well-formed | a document or value for which `wf` holds: the shapes `parse` returns (REVIEW-3). `wf` does not exist yet |
| `same` | the specification relation "the same TOML document", ignoring span against owned strings and the order of a table's pairs (REVIEW-4). It does not exist yet |
| closed law | a law with no `for` or `exs` binder; one fixed input, a unit test the checker runs |
| quantified law | a law with at least one binder |
| proof gate | the first line `bend eztoml/PROOF.bend` prints is exactly `All terms check.` (bend exits 0 when a proof leans on unsafe code, so the exit status is not the gate) |
| Proved, Trusted | the two levels. Pending is a status of a Proved row |
| toml-test | the TOML project's conformance corpus (github.com/toml-lang/toml-test), used here to audit, never as evidence |

## Background

### What eztoml is

eztoml reads and writes TOML v1.0.0 for Bend 2. `parse` turns text into a document, `render` writes one back, `get` and `at` look values up, `string`, `digits` and `flag` read scalars, and the builders make values by hand. It has no IO and no dependencies beyond Base. v0.1.0 was a sectioned, string-only reader that ez still pins; 0.2.x is a full parser, a 34-state character scanner with a two-pass renderer, tuned by the recent performance work (spans, one-state reads, consed rows).

### How eztoml proves things today

`nix flake check` runs the proof gate on `eztoml/PROOF.bend`, which passes (35 s), and bolt v0.4.0, which says `clean` with `closed` off. The 16 closed laws are the only evidence for the README's Compliance list: each checks a few fixed documents against the renderer's exact output and the error's exact words.

### How ez depends on eztoml

ez reads ez.toml and ez.lock.toml through eztoml v0.1.0. Its SPEC.md proves EZ-DOC-1 (a lock reads back as rendered) and EZ-LED-4 (a ledger reads back) against that reader, with restrictions that exist only because of v0.1.0: no `"`, `\` or newline in a value, no `=` in a file path (eztoml#24). Both rows say that when ez moves to 0.2.x, "the text layer rests on eztoml's own proved round trip instead". This RFC is that round trip.

### Why the current laws are the wrong evidence

A closed law is too weak to protect a behavior: a parser that broke on every other input would pass all 16. It is also too strong to let the behavior change: it pins layout and wording nobody depends on. The audit shows the gap directly. The gate is green while `a = -+1` reads as `+1`, while `a = """x""""` (valid) is refused, and while `[a"b"]` (invalid) is read as table `b`.

## Problem Statement

For every behavior of eztoml, a reader should be able to answer two questions from SPEC.md alone: is it guaranteed, and is the guarantee proved or assumed? Today neither can be answered.

Goals:

- One SPEC.md listing every guarantee, checked against the laws by bolt's `trace`.
- The round trip proved (TOML-RT-1), so ez can point a Trusted row at it.
- Every known conformance bug fixed, each with a law that would have caught it.
- No closed law in the tree.

Non-goals:

- TOML v1.1 (new escapes, optional seconds, newlines in inline tables). A later RFC.
- Preserving comments, blank lines or layout through a round trip. `render` is canonical, not lossless, and says so.
- Performance (REVIEW-13).

## Proposal

### Two levels, and the positions carried over from ez, bolt and ezjson

- Exactly two levels. A Proved row is backed by a quantified law tagged with its ID, passing the gate. A Trusted row names what the gate cannot check and says why. Pending is a status of a Proved row.
- A closed law has no standing.
- A test is never evidence for a row. The toml-test driver and the fuzzer that found the bugs are how we audited the code; they are not committed and no row cites them.
- Laws only reach values. eztoml has the easy case: every public def is pure, so there is no World and no planner to extract. The work is proofs, and the fixes that make them true.

### The proof gate

Unchanged: `bend eztoml/PROOF.bend` must print exactly `All terms check.` as its first line, which `ez.mkProofs` enforces in `nix flake check`.

### The interface, against mature TOML libraries

TOML specifies documents, not an API, so the interface rows are ours to choose. We checked each def against the libraries most readers know.

| eztoml | Rust `toml` | Python `tomllib` / `tomli-w` | Go `BurntSushi/toml` | C++ `toml++` |
| :---- | :---- | :---- | :---- | :---- |
| `parse` (error as a field) | `from_str::<Table>` (Result) | `loads` (raises) | `Decode` (error) | `parse` (throws or result) |
| `render` (canonical: keys first, dotted keys as headers) | `to_string` (same order) | `tomli_w.dumps` | `Encoder.Encode` | `operator<<` |
| `get` (first of a name) | `Table::get` | `dict[...]` | map index | `node_view[...]` |
| `at` (dotted path, no array index) | none built in | none | `MetaData.IsDefined` | `at_path` (indexes arrays) |
| `string`, `digits`, `flag` (default on the wrong kind) | `as_str`, `as_integer`, `as_bool` (Option) | typed values | typed values | `value_or` |
| integers as sign and decimal digits | `i64` | `int` | `int64` | `int64_t` |
| floats as their spelling | `f64` | `float` | `float64` | `double` |

Keeping a float's spelling and an integer's digits, rather than converting, is a departure that serves the round trip: nothing is rounded. The defaults on the wrong kind (REVIEW-8) and the missing array index in `at` (REVIEW-7) are departures we keep.

### Requirements: round trip (TOML-RT)

| ID | Requirement | Level | Status |
| :---- | :---- | :---- | :---- |
| TOML-RT-1 | For every document `d` with `wf(d)`: `bad(parse(render(d)))` is `""`, and `parse(render(d))` is `same` as `d` | Proved | pending |
| TOML-RT-2 | For every text `t` with `bad(parse(t)) == ""`: `parse(render(parse(t)))` is `same` as `parse(t)`, and `render` of it is `render(parse(t))` | Proved | pending |
| TOML-RT-3 | For every text `t` with `bad(parse(t)) == ""`, `wf(parse(t))` holds | Proved | pending |

Verdicts: TOML-RT-1 cannot be judged until `wf` exists. It holds for every parsed document we rendered (203 of 203, and about 43,000 fuzzed). TOML-RT-2 holds on every valid input we tried, and fails only after an invalid one was accepted: `a = 0_0.5` renders `a = 00.5`, which does not parse (R-I6). It holds once I6 is fixed. TOML-RT-3 holds on every input we tried, including headers that need quotes (`["x\ny"]`, `[a."b.c"]`, `[[""]]`).

TOML-RT-1 is the headline (REVIEW-2). Its law, with `wf` and `same` still to be written:

```
# LAW: render then parse is the same document
# TOML-RT-1
law render_parse:
  for +d: T.Doc
  for ok: {T.wf(d) == True{} : Bool}
  {same(T.parse(T.render(d)), d) == True{} : Bool}
```

It is a proof about the scanner run on text the renderer made, which is a smaller language than TOML: no comments, one canonical spacing, keys before tables. That is why it can come before the grammar relation. The proof plan goes in a design doc with a spike (Rollout).

### Requirements: TOML v1.0.0 texts (TOML-TEXT)

| ID | Requirement | Level | Status |
| :---- | :---- | :---- | :---- |
| TOML-TEXT-1 | For every text `t` of Unicode scalar values: `bad(parse(t))` is `""` exactly when `t` matches toml.abnf's `toml` rule (TOML v1.0.0) and breaks none of the rules of TOML-TEXT-2 | Proved | pending |
| TOML-TEXT-2 | For every text `t` that matches the `toml` rule, `bad(parse(t))` is `""` exactly when each key, table and array of tables is defined once; no `[table]` header names a table that dotted keys or an earlier header defined, or an array of tables; no dotted key adds to a table a header defined, or to an array of tables; no `[[array]]` header names a table or a static array; and inline tables and arrays are not extended after they are written. Each element of an array of tables is its own scope for these rules | Proved | pending |

Verdicts: TOML-TEXT-1 partly: 5 valid toml-test documents are refused (V1, V2) and 29 invalid ones accepted (I1 to I4, I6 to I8), besides R1 and R3. TOML-TEXT-2 partly: I1 (dotted keys extend a header's table) and R2 (the defined-headers list is shared across array elements, so `[[a]]\n[a.b]\n[[a]]\n[a.b.c]\n[a.b]` is refused).

TOML-TEXT-1 is proved through a law-side grammar relation, toml.abnf transcribed one constructor per rule with the rule quoted above each, as ezjson's `Derives` transcribes RFC 8259. It is the costliest row. Until it lands, each conformance fix adds a partial law tagged TOML-TEXT-1 or TOML-TEXT-2 (REVIEW-6).

### Requirements: keys (TOML-KEY)

| ID | Requirement | Level | Status |
| :---- | :---- | :---- | :---- |
| TOML-KEY-1 | `bare(s)` holds exactly when `s` is nonempty and every character of `s` is an ASCII letter, an ASCII digit, `_` or `-` (toml.abnf `unquoted-key`) | Proved | pending |
| TOML-KEY-2 | `key(s)` is `s` when `bare(s)`; otherwise it is a basic string, and for every `s` of Unicode scalar values, `parse(key(s) ++ " = 1")` has no error and one pair, named `s` | Proved | pending |
| TOML-KEY-3 | In a parsed document, a key's name is its characters however it was written: a bare key, a basic or literal string with its escapes decoded, or a segment of a dotted key or a header, so `get` and `at` find it by those characters | Proved | pending |

Verdicts: TOML-KEY-1 holds by reading (`bare.at` uses Base's ASCII `Char.is_alpha` and `Char.is_digit`). TOML-KEY-2 holds for every key we tried (`=`, `"`, `\`, newline, controls, `.`, the empty key, `é`, an emoji); `key_is_bare_when_it_can` and `key_is_quoted_when_it_must` prove the first half. TOML-KEY-3 holds on the targeted inputs (`"a.b" = 1` is found by `get(root, "a.b")` and is distinct from dotted `a.b`), except R3, where `[a"b"]` is read as `b`.

### Requirements: values (TOML-STR, TOML-NUM, TOML-TIME)

| ID | Requirement | Level | Status |
| :---- | :---- | :---- | :---- |
| TOML-STR-1 | For every string form of toml.abnf (basic, literal, multi-line basic, multi-line literal) and every text that form can hold, `string` of the value `parse` reads is the text it denotes: escapes decoded, a line-ending backslash and the whitespace after it dropped in a multi-line basic string, and a newline right after the opening delimiter dropped | Proved | pending |
| TOML-STR-2 | `render` writes a string value as a basic string that escapes exactly `"`, `\` and the controls U+0000 to U+001F and U+007F (with `\b`, `\t`, `\n`, `\f`, `\r` where TOML has them and `\u00XX` otherwise), and writes every other character as itself | Proved | pending |
| TOML-NUM-1 | An integer is read exactly when it matches toml.abnf's `integer` rule and lies within signed 64 bits, and reads to its sign and its value's decimal digits, with no leading zero unless the value is 0 | Proved | pending |
| TOML-NUM-2 | A float is read exactly when it matches toml.abnf's `float` rule, and reads to its sign and its spelling with the sign and every `_` removed; `render` writes the sign (`-` only) and that spelling | Proved | pending |
| TOML-TIME-1 | A datetime is read exactly when it matches one of toml.abnf's four date-time rules with RFC 3339's ranges (month 1 to 12, the day within the month in that year, hour 0 to 23, minute 0 to 59, second 0 to 60, offset hours 0 to 23 and minutes 0 to 59), and `render` writes it with `T` and `Z` in upper case, keeping the fraction's digits | Proved | pending |

Verdicts: TOML-STR-1 partly: V1 (quotes just before a closing delimiter) and R1 (an empty string at the end of a text with no newline). TOML-STR-2 holds on the targeted inputs. TOML-NUM-1 partly: I6 (`-+1` reads as 1; `0_1` reads). TOML-NUM-2 partly: I6 and R-I6 (`0_0.5`). TOML-TIME-1 partly: I4 (February 29 in 2100, February 30).

A note on wording: TOML-NUM-1 promises the value, not the spelling. Hex, octal, binary, underscores and a `+` are gone after a round trip, which is TOML's semantics and what every library in the comparison does.

### Requirements: readers (TOML-GET, TOML-READ)

| ID | Requirement | Level | Status |
| :---- | :---- | :---- | :---- |
| TOML-GET-1 | `get(rows, k)` is `Found{v}` for the value `v` of the first `VPair{k, v}` in `rows`, and `Miss` when no pair in `rows` is named `k` | Proved | pending |
| TOML-GET-2 | `at(rows, [])` is `Miss`; `at(rows, [k])` is `get(rows, k)`; and `at(rows, k <> ks)` with `ks` nonempty is `at` of the rows of the value `get(rows, k)` finds, when that value is a table, an inline table, or one element of an array of tables (a `VAot`, which only a hand-built document holds as a pair's value), and `Miss` otherwise, a whole array of tables included | Proved | pending |
| TOML-READ-1 | For every value `v`, `string(v)` is its characters when `v` is a string, owned or a span, and `""` otherwise; `digits(v)` is its digits when `v` is an integer, and `""` otherwise; `flag(v)` is its bit when `v` is a boolean, and `false` otherwise | Proved | pending |

Verdicts: TOML-GET-1 holds by reading (`rows.find`, `main.bend:1850`); `get_first` proves the head case. TOML-GET-2 holds by reading and was confirmed for an array of tables (REVIEW-7). TOML-READ-1 holds by reading; `string_of` proves the owned case.

The builders, `root` and `bad` get no row. They are constructors and field reads; the laws that restated them are deleted (REVIEW-10), and `wf` (REVIEW-3) is where a built document's validity lives.

### Retiring the closed laws

All 16 closed laws, and 16 definitional quantified ones, are deleted in the change that lands SPEC.md (REVIEW-10). The inventory's "points toward" column keeps the one useful thing they held: a map of which examples illustrate which row.

### Tagging and traceability

SPEC.md uses bolt's format, as ez, bolt and ezjson do: requirement tables headed `| ID | Requirement | Level | Status | Law |`, the Law cell as `<path> <law>` entries joined by `; `, a trust table headed `| ID | Assumption | Why it is trusted |`, and a "Left to prove" section for pending rows with partial laws. Each law carries its row's ID on its own comment line above `law`. With bolt v1.7.0, `trace` and `closed` run at error, and `coverage` at warn until the rows are proved.

### The refactoring contract

A tagged law's statement is owned by its row. It changes only when the row's wording changes, which is a behavior change and says so. Proofs may be rewritten freely, and so may untagged laws. The performance work of 0.2.x is the kind of change this is for: with TOML-RT and TOML-TEXT proved, a rewrite of the scanner is mergeable on the gate alone.

### The trust boundary

| ID | Assumption | Why it is trusted |
| :---- | :---- | :---- |
| TOML-TRUST-1 | The Bend checker is sound: a proof it accepts proves its law | The gate cannot check the checker. Same as EZ-TRUST-1. eztoml pins bend 2.0.25 through the flake |
| TOML-TRUST-2 | The proof-gate runner fails the build unless the first line of `bend eztoml/PROOF.bend` is `All terms check.` | It is ez's `mkProofs`, run by `nix flake check` in CI; this is EZ-TRUST-4 |
| TOML-TRUST-3 | A TOML file's bytes reach `parse` as the code points of their UTF-8 decoding, and invalid UTF-8 is the reader's to reject | `parse` takes a `String`. Bend's `File.read` decodes before eztoml sees the text, and replaces an invalid byte with U+FFFD (confirmed) |

### Decided behavior changes

Decided with the REVIEW items. Each lands as its own change, with master's results against the branch's:

| Change | Needed by | REVIEW |
| :---- | :---- | :---- |
| a second sign and an `_`-hidden leading zero are refused (I6, R-I6) | TOML-NUM-1, TOML-NUM-2, TOML-RT-2 | REVIEW-6 |
| quotes before a multi-line closing delimiter (V1); an empty string at the end of a text (R1) | TOML-STR-1 | REVIEW-6 |
| dotted keys with a shared prefix in an inline table (V2) | TOML-TEXT-1 | REVIEW-6 |
| the table-definition rules, per array element (I1, R2) | TOML-TEXT-2 | REVIEW-6 |
| a bare header segment next to a quoted one (R3); `[ [` (I8) | TOML-TEXT-1, TOML-KEY-3 | REVIEW-6 |
| controls in comments (I2), a lone CR (I3), a value on the next line (I7) | TOML-TEXT-1 | REVIEW-6 |
| the day checked against the month and leap years (I4) | TOML-TIME-1 | REVIEW-6 |
| add `wf` | TOML-RT-1, TOML-RT-3 | REVIEW-3 |
| move to `main.bend` at the root, lemmas to `src/` | none (layout) | REVIEW-1 |
| README build step and import hash | none (docs) | REVIEW-12 |

### How we will know it worked

- `trace` and `closed` at error under bolt v1.7.0 or later, with the gate green in `nix flake check`.
- No closed law in the tree.
- No pending row in TOML-RT, TOML-KEY, TOML-GET or TOML-READ. TOML-TEXT-1 may still be pending, with its partial laws tagged and "Left to prove" saying what is missing.
- ez's SPEC.md points its text layer at TOML-RT-1 through a Trusted row naming the eztoml pin, and drops its v0.1.0 restrictions.
- A rewrite of the scanner is mergeable on the gate alone.

## Abandoned Ideas

**Keep the closed laws as the Compliance section.** They read well and the README cites them by production. But each states a few fixed inputs, and a reader of "proves" takes them as a guarantee the audit shows does not hold. The inventory keeps the map; the rows keep the claims.

**Commit the toml-test driver as a test or a flake check.** It found most of the bugs and runs in under a second. But it is a closed law on a bigger input: it says nothing about the next document, and a green run would be read as evidence for TOML-TEXT-1. We used it to audit, and the inventory says so. The maintainer may still want it as a development tool outside the gate; it would have to be marked as such.

**Prove `parse` equal to a reference parser.** The reference would be a second parser with its own bugs, and the law would only say that two programs agree. The grammar relation is different: it is toml.abnf transcribed, short enough to check by reading.

**Validating builders.** `integer(sign, "abc")` could return an error value, as ezjson's `num` returns `null`. But eztoml's builders are used to write documents a caller already knows are valid (ez's ledger), a `Val` has no error case to return, and `wf` gives the same guarantee as a precondition without changing a released signature.

**A renderer that computes headers from the keys and ignores the stored path.** It would take the path condition out of `wf`, and `table(path, rows)` could not write a wrong header. But it makes the `path` field meaningless without removing it, and it is a behavior change to hand-built documents that render today. It stays open as a Future Step.

**Lossless round trips (comments, layout).** toml_edit does this for Rust. It needs a different document model (trivia on every node). Out of scope; `render` is canonical, and TOML-RT is stated over values.

## Rollout

| Phase | What lands | What it leaves true |
| :---- | :---- | :---- |
| Docs | README build step and import hash (REVIEW-12) | the README works on a fresh clone |
| Lint first | bolt v1.7.0 as a `[tools.bolt]` pin, the ez flake input at `df6d616`, `laws` at warn; S003 and S004 fixed; IO defs marked | lint clean except the law rules |
| Layout | `main.bend` at the root, whole; LAWS.bend and PROOF.bend beside it; the lemmas in `src/eq.bend` | the interface is one file, where ez expects it |
| One | SPEC.md from these tables; the closed and definitional laws deleted; `closed` and `trace` at error; README Compliance points at SPEC.md; the five kept laws tagged; TOML-KEY-1, TOML-GET-1, TOML-GET-2 and TOML-READ-1 proved | the gate is honest: SPEC.md says what is proved, and nothing claims more |
| Fixes | the conformance fixes of REVIEW-6, I6 first, each with its partial law | every known bug fixed, each with a law that would have caught it |
| Two | `wf` and `same`; TOML-KEY-2 and TOML-STR-2 (the renderer's side, structural inductions); a design doc for the scanner proofs with a spike that proves one production of TOML-RT-1 against the real checker | the renderer is proved, and the scanner proof has a plan |
| Three | TOML-RT-3, TOML-RT-1, TOML-RT-2, TOML-KEY-3 | the headline is proved; ez can rely on it |
| Four | the grammar relation; TOML-TEXT-2, then TOML-STR-1, TOML-NUM-1, TOML-NUM-2, TOML-TIME-1 and TOML-TEXT-1 | conformance is proved |

## Risks

- **Proof effort on the scanner.** `parse` is a 34-state machine over characters, with a stack of open arrays and inline tables and a list of defined headers, tuned for speed. TOML-RT-1 needs an invariant relating the scanner's state to the part of the rendered text read so far. If that proves too costly, moving a row to Trusted is a visible weakening the maintainer approves. The Two phase's spike is where we find out.
- **The grammar relation encodes a mistake.** It is checked against toml.abnf by reading only. Keeping it one constructor per ABNF rule, with the rule quoted above each, is the mitigation. The table-definition rules are prose in the TOML specification, not ABNF, so TOML-TEXT-2 is the riskier transcription.
- **The spec encodes accidents.** The defaults on the wrong kind, and `at` missing at an array of tables, become promises. REVIEW-7 and REVIEW-8 are where to stop that.
- **The fixes break documents that parsed.** Each fix refuses only text TOML v1.0.0 calls invalid (or accepts text it calls valid), and ez writes none of it. I6 changes a value today, so a caller who wrote `-+1` has been reading the wrong number.
- **Performance.** Parse time is quadratic in keys per table and in tables (REVIEW-13). A proof-driven change could make it worse; the refactoring contract lets a later rewrite fix it without touching a law.
- **Pressure to reintroduce examples.** A failing proof invites a closed law "for now". The contract is that a pending row is honest and a closed law is not.
- **Checker soundness.** TOML-TRUST-1, as everywhere.

## Future Steps

- A public `eq`, once `same` has been used enough to know which equality callers want (float by spelling or by value).
- Indexing into arrays and arrays of tables in `at`.
- Errors with a position: every library in the comparison says where a document went wrong.
- TOML v1.1.
- Headers computed from keys (see Abandoned Ideas).
- ez's EZ-DOC-1 and EZ-LED-4 resting on TOML-RT-1, and ez's `lockable`/`renderable` restrictions for v0.1.0 lifted.
