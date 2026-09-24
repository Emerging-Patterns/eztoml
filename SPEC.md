# eztoml specification

This is the list of every behavior eztoml guarantees, each under a stable requirement ID. There are two families: conformance to [TOML v1.0.0](https://toml.io/en/v1.0.0) and its [toml.abnf](https://github.com/toml-lang/toml/blob/1.0.0/toml.abnf) (TOML-TEXT, TOML-STR, TOML-NUM, TOML-TIME), and the public interface in `main.bend` (TOML-RT, TOML-KEY, TOML-GET, TOML-READ). The interface is the defs `parse`, `render`, `get`, `at`, `root`, `bad`, `string`, `digits`, `flag`, `str`, `integer`, `float`, `boolean`, `array`, `inline`, `table`, `pair`, `key`, `bare` and `wf`, and the types `Doc`, `Val`, `Hit`, `Sign`, `When`, `Date`, `Clock` and `Zone`. Every other def in `main.bend` is internal and carries no promise.

Every requirement has one of two levels. A **Proved** requirement holds for every input, and is backed by a quantified law (a `for` or `exs` binder) in `LAWS.bend` that passes the proof gate. A **Trusted** requirement is an assumption eztoml cannot check from inside its own gate, and it is listed in the trust boundary below. A Proved requirement whose laws have not all landed has status **pending**: we intend to prove it, and until then it is not guaranteed. The proof gate is this check: the first line `bend PROOF.bend` prints is exactly `All terms check.` Tests and fixtures are never evidence for a requirement.

A document is **well-formed** when `wf` holds of it: the shapes `parse` returns. `same` is the specification relation "the same TOML document", which ignores whether a string is owned or a span of the source and the order of a table's pairs. Neither exists yet; both land before the TOML-RT rows are proved.

The reasoning behind each requirement, the verdict of each against the code at `d3c1356`, and the decisions that shaped them are in [docs/rfc/eztoml-spec.md](docs/rfc/eztoml-spec.md). Every law as it stood then, what the audit found, and the progress of the rollout are in [docs/rfc/eztoml-law-inventory.md](docs/rfc/eztoml-law-inventory.md).

## Format

A requirement table is any table whose header row is exactly `| ID | Requirement | Level | Status | Law |`. An ID is uppercase segments joined by hyphens, at least two (`[A-Z][A-Z0-9]*(-[A-Z0-9]+)+`), unique within the requirement tables, and never reused once released. Level is `Proved` or `Trusted`. Status is `proved` or `pending` for a Proved row and empty for a Trusted row. A Law cell holds `<path> <law>` entries, paths relative to this file, separated by `; `. A proved row names one or more laws, and together they prove it. A pending row may name laws that each prove part of it; the row stays pending until its requirement is proved in full, and its entries are checked as a proved row's are. A Trusted row names none.

A law proves a requirement when a comment line `# <ID>`, alone on its line, sits in the unbroken comment block directly above its `law` line. A law may carry several tags, one per line:

```
# LAW: a pair at the head of a table's rows is what get finds for its name
# TOML-GET-1
law get_first:
```

A tag may name a proved or a pending requirement, never a Trusted one or an ID no requirement table lists. bolt's `trace` rule checks all of this over the whole tree, and its `closed` rule rejects a law with no binder; both are errors in `bolt.bend`.

## Requirements

### Round trip (TOML-RT)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| TOML-RT-1 | For every document `d` with `wf(d)`: `bad(parse(render(d)))` is `""`, and `parse(render(d))` is `same` as `d` | Proved | pending |  |
| TOML-RT-2 | For every text `t` with `bad(parse(t)) == ""`: `parse(render(parse(t)))` is `same` as `parse(t)`, and `render` of it is `render(parse(t))` | Proved | pending |  |
| TOML-RT-3 | For every text `t` with `bad(parse(t)) == ""`, `wf(parse(t))` holds | Proved | pending |  |

### TOML v1.0.0 texts (TOML-TEXT)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| TOML-TEXT-1 | For every text `t` of Unicode scalar values: `bad(parse(t))` is `""` exactly when `t` matches toml.abnf's `toml` rule (TOML v1.0.0) and breaks none of the rules of TOML-TEXT-2 | Proved | pending | LAWS.bend fail_stays; LAWS.bend comment_control_refused; LAWS.bend lone_cr_refused; LAWS.bend last_cr_refused; LAWS.bend value_on_key_line; LAWS.bend value_on_key_line_crlf |
| TOML-TEXT-2 | For every text `t` that matches the `toml` rule, `bad(parse(t))` is `""` exactly when each key, table and array of tables is defined once; no `[table]` header names a table that dotted keys or an earlier header defined, or an array of tables; no dotted key adds to a table a header defined, or to an array of tables; no `[[array]]` header names a table or a static array; and inline tables and arrays are not extended after they are written. Each element of an array of tables is its own scope for these rules | Proved | pending |  |

### Keys (TOML-KEY)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| TOML-KEY-1 | `bare(s)` holds exactly when `s` is nonempty and every character of `s` is an ASCII letter, an ASCII digit, `_` or `-` (toml.abnf `unquoted-key`) | Proved | proved | LAWS.bend bare_needs_a_char; LAWS.bend bare_is_unquoted_key |
| TOML-KEY-2 | `key(s)` is `s` when `bare(s)`; otherwise it is a basic string, and for every `s` of Unicode scalar values, `parse(key(s) ++ " = 1")` has no error and one pair, named `s` | Proved | pending | LAWS.bend key_is_bare_when_it_can; LAWS.bend key_is_quoted_when_it_must |
| TOML-KEY-3 | In a parsed document, a key's name is its characters however it was written: a bare key, a basic or literal string with its escapes decoded, or a segment of a dotted key or a header, so `get` and `at` find it by those characters | Proved | pending |  |

### Values (TOML-STR, TOML-NUM, TOML-TIME)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| TOML-STR-1 | For every string form of toml.abnf (basic, literal, multi-line basic, multi-line literal) and every text that form can hold, `string` of the value `parse` reads is the text it denotes: escapes decoded, a line-ending backslash and the whitespace after it dropped in a multi-line basic string, and a newline right after the opening delimiter dropped | Proved | pending | LAWS.bend ml_basic_one_quote; LAWS.bend ml_basic_two_quotes; LAWS.bend ml_literal_one_quote; LAWS.bend ml_literal_two_quotes; LAWS.bend empty_basic_at_end; LAWS.bend empty_literal_at_end |
| TOML-STR-2 | `render` writes a string value as a basic string that escapes exactly `"`, `\` and the controls U+0000 to U+001F and U+007F (with `\b`, `\t`, `\n`, `\f`, `\r` where TOML has them and `\u00XX` otherwise), and writes every other character as itself | Proved | pending |  |
| TOML-NUM-1 | An integer is read exactly when it matches toml.abnf's `integer` rule and lies within signed 64 bits, and reads to its sign and its value's decimal digits, with no leading zero unless the value is 0 | Proved | pending | LAWS.bend num_two_signs; LAWS.bend num_zero_underscore; LAWS.bend num_signed_zero_underscore; LAWS.bend num_one_sign; LAWS.bend word_two_signs; LAWS.bend word_zero_underscore; LAWS.bend word_signed_zero_underscore |
| TOML-NUM-2 | A float is read exactly when it matches toml.abnf's `float` rule, and reads to its sign and its spelling with the sign and every `_` removed; `render` writes the sign (`-` only) and that spelling | Proved | pending | LAWS.bend num_two_signs; LAWS.bend num_zero_underscore; LAWS.bend num_signed_zero_underscore; LAWS.bend num_one_sign; LAWS.bend word_two_signs; LAWS.bend word_zero_underscore; LAWS.bend word_signed_zero_underscore |
| TOML-TIME-1 | A datetime is read exactly when it matches one of toml.abnf's four date-time rules with RFC 3339's ranges (month 1 to 12, the day within the month in that year, hour 0 to 23, minute 0 to 59, second 0 to 60, offset hours 0 to 23 and minutes 0 to 59), and `render` writes it with `T` and `Z` in upper case, keeping the fraction's digits | Proved | pending | LAWS.bend date_day_in_month; LAWS.bend date_day_past_month |

### Readers (TOML-GET, TOML-READ)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| TOML-GET-1 | `get(rows, k)` is `Found{v}` for the value `v` of the first `VPair{k, v}` in `rows`, and `Miss` when no pair in `rows` is named `k` | Proved | proved | LAWS.bend get_first; LAWS.bend get_skips_other_name; LAWS.bend get_skips_non_pair; LAWS.bend get_finds_first; LAWS.bend get_misses |
| TOML-GET-2 | `at(rows, [])` is `Miss`; `at(rows, [k])` is `get(rows, k)`; and `at(rows, k <> ks)` with `ks` nonempty is `at` of the rows of the value `get(rows, k)` finds, when that value is a table, an inline table, or one element of an array of tables (a `VAot`, which only a hand-built document holds as a pair's value), and `Miss` otherwise, a whole array of tables included | Proved | proved | LAWS.bend at_empty; LAWS.bend at_one; LAWS.bend at_table; LAWS.bend at_inline; LAWS.bend at_aot; LAWS.bend at_miss; LAWS.bend at_leaf |
| TOML-READ-1 | For every value `v`, `string(v)` is its characters when `v` is a string, owned or a span, and `""` otherwise; `digits(v)` is its digits when `v` is an integer, and `""` otherwise; `flag(v)` is its bit when `v` is a boolean, and `false` otherwise | Proved | proved | LAWS.bend string_of; LAWS.bend string_of_span; LAWS.bend string_of_other; LAWS.bend digits_of; LAWS.bend digits_of_other; LAWS.bend flag_of; LAWS.bend flag_of_other |

### Trusted (TOML-TRUST)

| ID | Requirement | Level | Status | Law |
| :---- | :---- | :---- | :---- | :---- |
| TOML-TRUST-1 | The Bend checker is sound: a proof it accepts proves its law | Trusted |  |  |
| TOML-TRUST-2 | The proof-gate runner fails the build unless the first line of `bend PROOF.bend` is `All terms check.` | Trusted |  |  |
| TOML-TRUST-3 | A TOML file's bytes reach `parse` as the code points of their UTF-8 decoding, and invalid UTF-8 is the reader's to reject | Trusted |  |  |

## Left to prove

TOML-KEY-1, TOML-GET-1, TOML-GET-2 and TOML-READ-1 are proved; every other row is pending. For the pending rows that name laws already:

| Row | Proved so far | Missing |
| :---- | :---- | :---- |
| TOML-TEXT-1 | a failed scanner keeps its first error to the end of the text (`fail_stays`); from every scanner state inside a comment, a control other than tab is refused (`comment_control_refused`); from every scanner state, a carriage return followed by anything but a line feed, or ending the text, is refused (`lone_cr_refused`, `last_cr_refused`); from every scanner state waiting for a value after `=`, a newline is refused (`value_on_key_line`, `value_on_key_line_crlf`) | the grammar relation, and `bad(parse(t))` is `""` exactly when `t` matches it; errors outside the scanner (tree errors) staying set; a carriage return inside a one-line string is refused by the string's own control check, which no law states yet |
| TOML-STR-1 | for every text `x` of characters that are no control, quote, apostrophe or backslash, `a = """x""""` and `a = '''x''''` with a newline read `x` and one closing quote (`ml_basic_one_quote`, `ml_literal_one_quote`), and `a = """x"""""` and `a = '''x'''''` ending the text read `x` and two (`ml_basic_two_quotes`, `ml_literal_two_quotes`); for every bare key `k`, `k=""` and `k=''` ending the text read the empty string (`empty_basic_at_end`, `empty_literal_at_end`) | every other text each form can hold: escapes, line-ending backslashes, newlines and quotes inside the body, the newline after the opening delimiter, one-line strings (read as spans), and other keys and positions |
| TOML-KEY-2 | `key` picks `s` or `key.basic(s)` by `bare(s)` (`key_is_bare_when_it_can`, `key_is_quoted_when_it_must`) | that `key.basic(s)` reads back as `s` |
| TOML-NUM-1 | a bare word, and its numeral scan, that starts with two signs, or with `0_` after an optional sign, holds no value, whatever follows (`num_two_signs`, `num_zero_underscore`, `num_signed_zero_underscore`, `word_two_signs`, `word_zero_underscore`, `word_signed_zero_underscore`); after one sign, a character that is not a sign is read as the first character of an unsigned numeral, with the sign kept (`num_one_sign`) | the rest of the `integer` rule in both directions (digits, underscores, prefixes, the signed 64-bit range), the digits read, and the same stated over `parse` |
| TOML-NUM-2 | the same laws: a float's integer part is a `dec-int`, so two signs and `0_` are refused before any `.` or exponent (`0_0.5`, `0_1e2`, `-+1.5`) | the rest of the `float` rule in both directions, the spelling read, `render`, and the same stated over `parse` |
| TOML-TIME-1 | the date check accepts a date exactly when its day is from 1 to the days of its month in its year, by RFC 3339's table and leap-year rule, for every year, month and day (`date_day_in_month`, `date_day_past_month`) | the rest of the four date-time rules (digits, separators, the time and offset ranges, the fraction), the same stated over `parse`, and `render` |

The order of work is in the RFC's Rollout: the cheap readers first, then the conformance fixes each with its partial law, then `wf`, `same` and the renderer, then the round trip, then the grammar relation.

## Trust boundary

These assumptions sit outside the proofs. They are the complete list of Trusted requirements, and a passing proof gate says nothing about them.

| ID | Assumption | Why it is trusted |
| :---- | :---- | :---- |
| TOML-TRUST-1 | The Bend checker is sound: a proof it accepts proves its law. | It cannot be checked from inside Bend; this is EZ-TRUST-1. eztoml pins bend 2.0.25 through the flake. |
| TOML-TRUST-2 | The proof-gate runner fails the build unless the first line of `bend PROOF.bend` is `All terms check.` | It is ez's `mkProofs` (`ez prove`), run by `nix flake check` in CI; this is EZ-TRUST-4. |
| TOML-TRUST-3 | A TOML file's bytes reach `parse` as the code points of their UTF-8 decoding, and invalid UTF-8 is the reader's to reject. | `parse` takes a `String`. Bend's `File.read` decodes before eztoml sees the text, and replaces an invalid byte with U+FFFD (checked with a driver that dumps the code points it read). |
