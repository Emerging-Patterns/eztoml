# eztoml: proving the grammar

## Draft Status

**State:** Accepted. Every REVIEW item was accepted as recommended by the maintainer; REVIEW-G1 and REVIEW-G2 reworded SPEC.md's TOML-TEXT-1 and TOML-TEXT-2, and REVIEW-G8 reworded TOML-TRUST-3's reason and added a note to the README. It plans the last six pending rows of SPEC.md, the ones the RFC's Rollout puts in phase Four: TOML-TEXT-1, TOML-TEXT-2, TOML-STR-1, TOML-NUM-1, TOML-NUM-2 and TOML-TIME-1. The parent RFC is [eztoml-spec.md](eztoml-spec.md), and its decisions stand. The round-trip plan, [eztoml-roundtrip-proofs.md](eztoml-roundtrip-proofs.md), is the model for this one, and every piece it built is available here. We read the code at `65756da`, where TOML-RT-1, RT-2, RT-3 and KEY-3 are proved and the gate takes about 18 s. The spike below is on top of that commit.

The spike transcribed one rule of toml.abnf, `dec-int`, as a Bool recognizer, and proved its accept direction against `word.val` (`dec_int_word`, a partial law of TOML-NUM-1). Probing the real binary found that TOML-TEXT-1 and TOML-TEXT-2 are false as worded, in five places where toml.abnf and the TOML specification's prose disagree (REVIEW-G1, REVIEW-G2). No bug in `main.bend` was found. The code does what the specification's prose says; only the rows' wording has to change.

**Update (WP-G landed).** toml.abnf (TOML v1.0.0, tag 1.0.0) is transcribed in LAWS.bend's `# GRAMMAR` section, one def or constructor per rule with the rule quoted verbatim above it, and the basic facts are proved in PROOF.bend's `# GRAMMAR` section. The derivation is `Gd`. `val`, `array-values`, `inline-table-keyvals` and `keyval` are mutually recursive, so they are the constructors of one type, `GVal`, and `g.ok.val` takes a mode (`GRule`) naming the rule a node spells. The regular rules are Bool recognizers over a leaf's characters. The date-time rules read from the front of a word and give what is left (`ARest`), since every alternative and option there is told apart by its first character. The four prose restrictions are separate defs, named `prose.*` rather than the `abnf.*` names this plan used, so no reader takes them for ABNF: `prose.int_in_range` (TOML-NUM-1), `prose.date_time_in_range` (TOML-TIME-1), `prose.escape_scalar` and `prose.comment_char`. A matching text is `bom.drop(t) == g.text(d)` with `g.ok(d)`. `g.val(d, v)` relates a value derivation to a `T.Val`: a string by its characters, owned or a span; an integer by its sign and canonical decimal digits, whose value as a `Nat` is the numeral's in its radix; a float by its sign and its spelling with the sign and `_` removed; a boolean by its bit; a date-time by `when.eq`; an array item by item; and an inline table by `at` on each keyval's path, with nothing else in its rows. `defs(d)` is TOML-TEXT-2's rules over the expressions in order: a record of what each key path holds (a value, a table a header named, a table a header only passed through, a table dotted keys made, an array of tables), with a new `[[array]]` element dropping every path under it. Ten laws prove the basic facts: `gap_is_ws` (KEY-3's blank space is `ws`); `g_lines_text_append`, `g_val_text_tail` and `g_text_parts` (a derivation's text is its parts' texts in order); and the six pairwise disjointness laws of the word rules, `boolean_not_integer` to `float_not_date_time`. None is tagged, since none proves part of a row. Each fails the gate when its proof is replaced by `{==}`. Size: 2,236 lines of law (the section, the 10 laws included) and 1,068 of proof, inside the 1,500 to 2,000 and 800 to 1,200 planned. The gate is about 20.0 to 20.8 s, against 20.5 s at `21d474c` on the same machine. Lint: 0 errors. `main.bend` is unchanged. A scratch driver (not committed, not evidence) ran about 60 words through the recognizers, and a dozen hand-built derivations through `g.text`, `g.ok`, `g.val` and `defs`. Every verdict agreed with `parse`.

Three findings shaped the transcription, and none changes the code or a row:

- **REVIEW-G2's reading, completed.** After `[a.b.c]`, `[a]` and `b.d = 1`, `parse` refuses a later `[a.b]` ("duplicate table"), and so does `tomllib`, which marks the tables dotted keys enter as defined. So in `defs`, a dotted key that enters a table a header only passed through makes it a table dotted keys define (`defs.enter`). The table stays open to dotted keys and closes to a header naming it. This is how TOML-TEXT-2's "a table that dotted keys defined" is read.
- **Two ABNF ambiguities in multi-line strings.** In `mlb-escaped-nl`, the whitespace after the backslash's newline can be read as part of it or as body characters. The newline after the opening delimiter can be read as `[ newline ]` or as the body's first newline. The prose settles both ("trimmed along with all whitespace (including newlines) up to the next non-whitespace character"; "a newline immediately following the opening delimiter will be trimmed"), so `g.str.chars` gives the same characters for every derivation of a string (`GTrim`). Every other newline stands for itself as written (REVIEW-G9).
- **Inline tables are sealed.** `parse` stores the tables that dotted keys make inside an inline table as `VInl`, the same as a nested inline table, so `{b.c = 1}` and `{b = {c = 1}}` read to the same value. `g.val` therefore enters a table in an inline table's rows exactly when a keyval's path lies under it (`g.leaf.paths`).

| ABNF rule | Def or constructor in LAWS.bend |
| :---- | :---- |
| `toml` | `Gd` (`GToml`); newline-expression pairs are `GLine` |
| `expression` (three alternatives) | `GExpr`: `GxBlank`, `GxKeyval`, `GxTable` |
| `ws` / `wschar` | `abnf.ws` / `abnf.wschar` |
| `newline` | `abnf.newline`; `[ newline ]` is `abnf.opt_newline` |
| `comment-start-symbol`, `comment` | `abnf.comment` (the `#` is written by `g.com.text`); `[ comment ]` is `GCom` |
| `non-ascii` / `non-eol` | `abnf.non_ascii` / `abnf.non_eol` |
| `keyval` | `GKeyval` (a `GVal` constructor, mode `RKeyval`) |
| `key`, `dotted-key` | `GKey`: `GSimpleKey`, `GDottedKey`; checked by `g.ok.key` |
| `simple-key`, `quoted-key` | KEY-3's `KSeg`, checked by `g.ok.seg` |
| `unquoted-key` | `abnf.unquoted_key` (TOML-KEY-1) |
| `dot-sep` | `GDotSep` (a dot-sep and the simple-key after it) |
| `keyval-sep` | the `w1`, `w2` fields of `GKeyval`; `=` written by `g.val.text` |
| `val` | `GVal`: `GvString`, `GvBoolean`, `GvArrayEmpty`/`GvArray`, `GvInlineTableEmpty`/`GvInlineTable`, `GvDateTime`, `GvFloat`, `GvInteger` (mode `RVal`) |
| `string` | `GString`: `GsMlBasic`, `GsBasic`, `GsMlLiteral`, `GsLiteral` |
| `basic-string`, `quotation-mark` | `abnf.basic_string` over KEY-3's `KPiece` |
| `basic-char`, `escaped`, `escape`, `escape-seq-char` | `abnf.basic_char`; `KpEsc` (`KMark`), `KpU4`, `KpU8` |
| `basic-unescaped` | `abnf.basic_unescaped` |
| `ml-basic-string`, `ml-basic-string-delim` | `GsMlBasic{nl, body}` |
| `ml-basic-body` | `abnf.ml_basic_body` |
| `mlb-content`, `mlb-quotes` | `GMlb` (`GmChar`, `GmNewline`, `GmEscapedNl`, `GmQuotes`); `abnf.mlb_content` |
| `mlb-char` / `mlb-unescaped` | `abnf.mlb_char` / `abnf.mlb_unescaped` |
| `mlb-escaped-nl` | `abnf.mlb_escaped_nl`; its `*( wschar / newline )` is `abnf.ws_newlines` |
| `literal-string`, `apostrophe` | `abnf.literal_string` |
| `literal-char` | `abnf.literal_char` |
| `ml-literal-string`, `ml-literal-string-delim` | `GsMlLiteral{nl, body}` |
| `ml-literal-body` | `abnf.ml_literal_body` |
| `mll-content`, `mll-quotes` | `GMll` (`GlChar`, `GlNewline`, `GlQuotes`); `abnf.mll_content` |
| `mll-char` | `abnf.mll_char` |
| `integer` | `abnf.integer` |
| `minus`, `plus`, `underscore`, `digit1-9` | `abnf.minus`, `abnf.plus`, `abnf.underscore`, `abnf.digit1_9` (spike) |
| `digit0-7`, `digit0-1` | `abnf.digit0_7`, `abnf.digit0_1` |
| `hex-prefix`, `oct-prefix`, `bin-prefix` | the letter argument of `abnf.prefixed` (120, 111, 98) |
| `dec-int`, `unsigned-dec-int` | `abnf.dec_int`, `abnf.unsigned_dec_int`, with `abnf.dec_rep`/`abnf.dec_rep1` (spike) |
| `hex-int`, `oct-int`, `bin-int` | `abnf.hex_int`, `abnf.oct_int`, `abnf.bin_int` via `abnf.prefixed` and `abnf.radix_rep` (`ARadix`) |
| `float` (both alternatives) | `abnf.float`, `abnf.float_std` (cut at the first `.`/`e`/`E`, `ACut`) |
| `float-int-part` | `abnf.float_int_part` |
| `frac`, `decimal-point` | `abnf.frac`, `abnf.decimal_point`; `frac [ exp ]` is `abnf.frac_exp` |
| `zero-prefixable-int` | `abnf.zero_prefixable_int` |
| `exp`, `float-exp-part` | `abnf.exp` (with `abnf.e`, e or E), `abnf.float_exp_part`; `[ exp ]` is `abnf.opt_exp` |
| `special-float`, `inf`, `nan` | `abnf.special_float`, `abnf.inf`, `abnf.nan` |
| `boolean`, `true`, `false` | `abnf.boolean`, `abnf.true`, `abnf.false` (via `abnf.chars_are`) |
| `date-time` | `abnf.date_time` |
| `date-fullyear`, `date-month`, `date-mday` | `abnf.date_fullyear`, `abnf.date_month`, `abnf.date_mday` |
| `time-delim` | `abnf.time_delim` (T, t or space) |
| `time-hour`, `time-minute`, `time-second` | `abnf.time_hour`, `abnf.time_minute`, `abnf.time_second` |
| `time-secfrac` | `abnf.time_secfrac`; `[ time-secfrac ]` is `abnf.opt_secfrac` |
| `time-numoffset`, `time-offset` | `abnf.time_numoffset`, `abnf.time_offset` (Z or z) |
| `partial-time`, `full-date`, `full-time` | `abnf.partial_time`, `abnf.full_date`, `abnf.full_time` |
| `offset-date-time`, `local-date-time`, `local-date`, `local-time` | `abnf.offset_date_time`, `abnf.local_date_time`, `abnf.local_date`, `abnf.local_time` |
| `array`, `array-open`, `array-close` | `GvArrayEmpty` / `GvArray` |
| `array-values` (two alternatives) | `GArrayValues`, `GArrayValuesLast` (mode `RArrayValues`) |
| `array-sep` | the comma in `g.val.text`; `[ array-sep ]` is `GArrayValuesLast`'s `sep` |
| `ws-comment-newline` | a list of `GWcn` (`GwWschar`, `GwNewline`), checked by `g.ok.wcn` |
| `table` | `GTable` |
| `std-table`, `std-table-open`, `std-table-close` | `GStdTable` |
| `array-table`, `array-table-open`, `array-table-close` | `GArrayTable` |
| `inline-table`, `inline-table-open`, `inline-table-close` | `GvInlineTableEmpty` / `GvInlineTable` |
| `inline-table-sep` | the `w1`, `w2` fields of `GInlineTableKeyvals` |
| `inline-table-keyvals` | `GInlineTableKeyvals`, `GInlineTableKeyvalsLast` (mode `RInlineTableKeyvals`) |
| `ALPHA`, `DIGIT`, `HEXDIG` | `abnf.alpha` (KEY-1), `abnf.DIGIT` (spike), `abnf.HEXDIG` (a to f too); KEY-3's `KHex` |

**Update (WP-T1 landed).** The datetime words are exact in both directions, in LAWS.bend's and PROOF.bend's `# WP-T1` sections. `date_time_word` is the classifier, for every list of characters `cs` and every datetime `w`: `word.val(cs)` reads as `w` exactly when `cs` matches `abnf.date_time` (the four date-time rules) and `prose.date_time_in_range`, and `g.val` says `cs` denotes `w`. It covers a lowercase `t` or `z`, a space between the date and the time (at word level; how the scan keeps that space in a word, the `LDate` state, is WP-V's), a fraction of any length, `Z` and numeric offsets, every range refused past its bound, and every word outside the rules, whose outcome is no datetime at all. `date_time_word_read` is the accept direction as an equation, `word.val(cs) == GotVal{VWhen{g.dt.when(cs)}}`, the form WP-V's lift needs. `date_time_render` says the text `render` writes for every well-formed datetime matches the rules within the ranges and denotes it; it is `when_word` put through the classifier. All three are tagged TOML-TIME-1, and the row stays pending until WP-V.

How it is proved:

- **One walk, both directions.** `t1.read` shows that the datetime scan (`when.read`) and the grammar give the same option (`t1.spec`: the datetime a word denotes when it matches within the ranges, and none otherwise) for every list of characters. The two are walked together, one character test at a time. The grammar is read through its rules' `ARest` results, factored so that the test the scan makes at a character is the test the grammar makes there (`Char.is_digit` is `abnf.DIGIT`, and `Char.is_eq(c, ':')` is `abnf.cp(c, 58)`, once the character is `Chr{x}`). So the failing tests agree too, and no separate refusal proof is needed. The refuse direction is the straight case split the design asked for, done inside the same walk.
- **Symbolic digits.** Every two-digit field goes through one eliminator, `t1.tk2`, with the digits left symbolic. The only arithmetic fact needed is `U32.add(0, x) == x` (`t1.add0`, by induction over the word). The year's third digit goes through `dig.val`, which is a digit's code point less 48 (`t1.dv`). No field is enumerated. `dg.elim` (WP-N) is used only for four one-character facts: a digit is no colon, no dash, no exponent mark, and no special word's first character.
- **Ranges.** The scan checks the date before it reads the time, and the grammar checks every field at the end. `t1.dok` equates the two date checks. The code's days of a month equal `days_in` of `prose.month` for every number, a month's or not (`t1.days`, by testing each month's number, with TIME-1's `days.same` and `feb.same` for the months). A date out of range makes the grammar's answer none whatever follows it (`t1.dbad`). The clock and offset ranges are the scan's `bound.rng` from 0 (`t1.rng0`).
- **The shared tail.** A partial-time's minutes, seconds, fraction and zone are read the same way after a date and a delimiter as after a time alone. `t1.C` and `t1.F` are stated once, over what is observed of the scan (`t1.obs`: the datetime, or the local time the scan keeps of a time alone) and over what the grammar says follows the partial-time (a finisher: the end or a time-offset, `t1.fdt`; or the end only, `t1.ftm`). The fraction's digits, which the scan keeps reversed, are the word's leading digits (`t1.fl`, `t1.revrev`).
- **The route.** `t1.rs` shows that `word.val` sends a word that matches to the datetime scan: it starts with a digit, so with no special word's first character; it has a colon third, or a dash fifth; and it has no `e` or `E`. The last is an invariant over the rules' `ARest` results (`t1.e.*`): each rule takes only digits and `- : . + T t Z z` and the space, so a word with an exponent mark keeps one and no rule matches it whole. `t1.rn` shows that every other word reads as no datetime, since a special word and a numeral never give one (`t1.nw.*`).

Reuse: TIME-1's `days.same` and `feb.same` (the lemmas behind `date_day_in_month` and `date_day_past_month`), WP-N's `dg.elim` and `when_word` (for `date_time_render`), and `when.self` (a datetime equals itself). RT-3's datetime part of `gd_word` was not needed: the walk proves both directions at once, and its range facts follow from the classifier.

Findings: none. On every word the code and the grammar agree, with no case beyond REVIEW-G1's five (the datetime ranges are REVIEW-G1's case (2), and `prose.date_time_in_range` states them). `main.bend` is unchanged.

Size: 59 lines of law and 2,604 of proof (planned 1,800, expected 4,000 to 7,000). The gate is about 20.6 s, against about 19.9 s at `558eced` (three alternating runs each, on the same machine). Lint: 0 errors, and no new warnings. Break checks: replacing each of the three laws' proofs by `{==}` fails the gate. So does each of four bugs planted in a scratch copy of `main.bend`. The full gate stops at the first failing proof, an older one for each (`date_day_in_month`, `feb.same`, `gd.wd.after`, `zoff`). Checked with the WP-T1 section alone, month 13 accepted fails `t1.r10`, a lowercase `t` refused fails `t1.r13`, and a `+24:00` offset accepted fails `t1.z.mm`. 29 February accepted in 1900 fails `feb.same`, the TIME-1 lemma that `t1.days` rests on.

Left for TOML-TIME-1: the same stated over `parse` from every value state, with a space after a date through `LDate` (WP-V), and a lemma that `render` writes `T` and `Z` in upper case (WP-V's render half).

**Update (WP-R spike).** The spike ran the refusal direction of TOML-TEXT-1 ("a text `parse` accepts has a derivation") over the header and key states. It is in PROOF.bend's and LAWS.bend's `# WP-R` sections.

- **The engine.** `sipr` is the scan induction run backward. Its motive holds the mode and the text still to read. Each step gets that the successor's text has no error. `sr.ff` proves that the fast step is the full step for every `Lex`. That is 1,044 lines, paid once.
- **The grammar position.** `r1.gp(st)` is a list of frames, `R1Fr`: the rules still open at that state, innermost first. `r1.fill(frames, text)` says the text is made of a derivation piece for each frame, in order, so its recursion is structural. The header and key states map as follows:
  - `LHead`: `RfHOpen` then the line's end, or a bare segment then `RfKAfter` then `r1.hend`.
  - `LHeadGap`: `RfKAfter`.
  - `LHeadDot` and `LKeyDot`: `RfWs` then `RfKSeg`.
  - `LHeadR`: `RfRBr`, or `RfNone` when doomed.
  - The quoted, escape and digit states: `RfKBasic`/`RfKLit`, `RfKEsc` and `RfKUni{uni, left}`.
  - `LKey` and `LAfter`: a keyval's key, then `r1.vend(stack)`, which is `RfEq`, then `RfVal`, then `r1.after(stack)`.
  - A state with no step into it maps to `RfAny`, whose fill is `Unit`. This is sound: a predecessor has to prove its own fill from its successor's, so a reachable state mapped to `RfAny` would fail the gate.
  - The string and word states not yet done map to `RfLater`, which is also `Unit`. `LVal` already maps to its real frame, so the key states are proved against the real value frame.
  - This part is 457 lines of law.
- **The obligations.** The spike proves one law per state, `r1.ob.*`, for 13 states: `LHead`, `LHeadGap`, `LHeadDot`, `LHeadR`, `LHeadQ`, `LHeadE`, `LHeadU`, `LKey`, `LKeyDot`, `LAfter`, `LKeyQ`, `LKeyE` and `LKeyU`. Each is proved for every character, with no Nat literal. The U32 order kit (`r1.adj`: u ≤ k exactly when u < k+1, at the bit level) proves the character classes of `basic-unescaped` and `literal-char`, the inverse of `dig.val` on hexadecimal digits, and `\u`/`\U`'s scalar check. The obligations are 5,422 lines:

| Part | States | Lines | Per state |
| :---- | ----: | ----: | ----: |
| bare header and key states | 7 | 1,542 | 220 |
| quoted segments | 2 | 862 | 431 |
| escapes | 2 | 484 | 242 |
| `\u`/`\U` digits | 2 | 554 | 277 |
| frame kit | | 548 | |
| character-class and U32 order kit | | 813 | |
| hexadecimal inverse | | 619 | |

- **What the spike cost, and what is left.** The spike took 6,466 lines of proof and 457 of law, against 5,000 planned. The other 22 states and the other modes are left. The kits carry over, so the estimate uses the per-state costs:

| What is left | Estimate |
| :---- | ----: |
| `LTop`, `LLine`, `LCom` | 900 to 1,200 |
| the ten string states, one-line and multi-line, reusing the three kits | 3,500 to 6,000 |
| `LBare` and `LDate`, not counting WP-N1's and WP-T1's refusal halves | about 1,100 |
| `LVal`, the array and inline-table states, and `LSink` | 1,800 to 3,000 |
| the CR, lead, held, open, eat and end modes, and the instance that gives `text_derived` | 900 to 1,500 |
| **total left** | **8,200 to 12,800** |

  The value states' `gp` adds 400 to 800 lines of law. WP-R comes to about 15,000 to 19,000 lines of proof, in the lower half of the 15,000 to 25,000 estimate.
- **The checks.**
  - The gate is 20.0 to 20.7 s, against 19.9 s at `558eced`.
  - Lint: 0 errors.
  - Replacing any of 26 new top-level proofs with `{==}` fails the gate. The 26 are `sr.ff`, the five `sipr.*`, the 13 `r1.ob.*`, `r1.adj`, `r1.na`, `r1.bu`, `r1.lc`, `r1.uok`, `r1.dec1` and `r1.hx.of`.
  - Two bugs were planted in a scratch copy of `main.bend`. A header gap that skips a bare character, so `[a b]` is accepted, fails `r1.ob.gap`. A second dot in a key that stays in `LKeyDot`, so `a..b` is accepted, fails `r1.kd.go2`.
  - No text `parse` accepts was found without a derivation. `main.bend` is unchanged.
  - No law is tagged TOML-TEXT-1. The instance is complete only once every state is done.
- **Recommendation for REVIEW-G6:** keep TOML-TEXT-1 Proved, as decided in (a). The cost per state is steady, at 220 to 430 lines. The kits carry over to the strings. No state needed a new idea after the frame design.

**Items for review:**

- [x] <!-- REVIEW-G1 (resolved): TOML-TEXT-1 is false as worded, in five ways. It says `bad(parse(t))` is `""` exactly when `t` matches toml.abnf's `toml` rule and breaks none of TOML-TEXT-2's rules. But toml.abnf is looser than the specification. Its header says "certain invalid documents would need to be rejected as per the semantics described in the supporting text". Checked against the binary at `65756da`, `parse` refuses these texts, all of which match the rule and none of which defines anything twice: (1) `a = 9223372036854775808` ("out of range"; the ABNF has no range, and the prose asks for signed 64 bits); (2) `a = 1979-13-01`, `a = 1979-02-30`, `a = 24:00:00` and `+24:00` offsets (the ABNF gives RFC 3339's ranges only in comments); (3) `a = "\uD800"` and `"\U00110000"` ("invalid escape"; the ABNF allows any 4 or 8 HEXDIG, and the prose says an escape must be a Unicode scalar value); (4) `a = 1 # x<U+007F>y` ("invalid control in comment"; the ABNF's `non-eol` is `%x20-7F`, which includes U+007F, and the prose forbids it). It also accepts one text the rule does not match: (5) `<U+FEFF>a = 1`, a leading byte-order mark (the `lead` flag in `read.step`), which toml.abnf does not allow. Python's `tomllib` refuses the cases of (2) to (5) we tried and reads (1) as a big integer. Options: (a) reword the row. The grammar relation becomes toml.abnf together with the four prose restrictions, each named, with (1) and (2) pointing at TOML-NUM-1 and TOML-TIME-1. One leading U+FEFF is taken off before matching, since it is the encoding's signature rather than text. toml-test treats it that way: `bom-not-at-start` is invalid, and the newer valid cases `utf8-bom-01` and `utf8-bom-02` start with one. The row also gains the `short` bound every row that goes through the scan induction has; (b) as (a), but refuse the byte-order mark in the code, which is a behavior change for files saved by editors that write one; (c) change the code to follow the ABNF where it is looser, accepting (1) to (4), which the specification forbids. Recommend (a). No code changes, and each restriction is one the RFC's other rows already state. It is a rewording of the specification, and so a behavior change of the promise. Decided: (a), as recommended. -->
- [x] <!-- REVIEW-G2 (resolved): TOML-TEXT-2 is false as worded for the same reason. It speaks of "every text that matches the `toml` rule", so the four texts (1) to (4) of REVIEW-G1 are counterexamples: they break none of its rules and are refused. It is also unclear on one point, which the transcription must settle. "No dotted key adds to a table a header defined": after `[a.b.c]`, `[a]` and `b.d = 1`, the table `a.b` was made by a header but not named by one. `parse` accepts this, and so does `tomllib`. Options: (a) reword the row to "for every text shorter than 2^32 characters that matches the grammar of TOML-TEXT-1", and read "a table a header defined" as "the table a header names", so that the tables a header creates on its way stay open to dotted keys, as the code does; (b) as (a), but close those tables too, which changes the code, refuses a document `tomllib` accepts, and goes beyond what toml-test asks. Recommend (a). Decided: (a), as recommended. -->
- [x] <!-- REVIEW-G3 (resolved): How the grammar relation is represented. Options: (a) a derivation type for the context-free structure, with Bool recognizers at the leaves. The type has expressions, keys, arrays, inline tables, and strings as lists of pieces, reusing KEY-3's `KPiece`. The recognizers cover the regular rules: whitespace, newline, comment characters, `unquoted-key`, the integer, float, boolean and date-time rules. It comes with `g.text` (the text a derivation spells), `g.ok` (each leaf matches its rule) and `g.val` (what it denotes), as ezjson's `Gv` does for RFC 8259; (b) Bool recognizers throughout, one first-order def per rule over the list of remainders it can leave (list-of-successes), since alternation in toml.abnf is not deterministic; (c) a derivation type throughout, leaves included. Recommend (a). The structure is what the accept direction inducts on and what the refusal direction builds, so it has to be data. The leaves are where the ABNF is closest to a regular expression, and the spike showed a Bool leaf proves directly against the numeral scan. Option (b) reads most like the ABNF, but every refusal would be a statement over all parses. Option (c) makes each word-level refusal an existential. The transcription is checked by reading, one def or constructor per rule with the rule quoted above it, as TOML-KEY-1's `unquoted-key` and TOML-TIME-1's RFC 3339 table are. Two traps to name in the review: quoted strings in ABNF are case-insensitive (RFC 5234 §2.3), so `"T"`, `"Z"`, `"e"` and HEXDIG's `"A"` to `"F"` match either case, while `%x`-spelled rules such as `hex-prefix` and `true` do not; and Bend has no mutual recursion, so mutually recursive rules (`val`, `array-values`, `inline-table-keyvals`) become one def over a mode, as `canon` and `k3.has` are. Decided: (a), as recommended. -->
- [x] <!-- REVIEW-G4 (resolved): How TOML-TEXT-2 is proved. Options: (a) over the derivation. The accept-direction readers (WP-A) show that `parse` of a derivation's text is the replay of its expressions through `tree.walk`, with the error the first walk sets. TOML-TEXT-2 is then a statement with no scanner in it: the replay sets no error exactly when a law-side transcription of the prose rules (`defs`) accepts the expressions. It is proved by induction over the expressions, with an invariant that gives `heads` its meaning (each entry is a table a header named, or one dotted keys made, in the current element's scope); (b) as an invariant over `sip.read`, the scan induction, which its landing note built with TOML-TEXT-2 in mind. But the rules are about the text's expressions, and `sip.read`'s invariant sees only the scanner's state, so it would need a ghost record of the definitions made so far, which the state does not hold. Recommend (a). The row is stated for texts that match the grammar, so a derivation is in hand, and the induction steps once per expression rather than once per character. `sip.read` is still reused, by TOML-TEXT-1's refusal direction (REVIEW-G5). Decided: (a), as recommended. -->
- [x] <!-- REVIEW-G5 (resolved): How TOML-TEXT-1's refusal direction runs: a text `parse` accepts has a derivation. Options: (a) backward, over a generalized scan induction (`sipr`): for every scanner state `s` and every text `t`, if `doc.read(t, s)` has no error, then `t` completes the grammar position `gp(s)` that the state tracks. `gp` is a law-side function from the state (its lex state, `back`, `qkind`, stack frames, buffer, `uni` and `left`) to the open rules of a partial derivation. Each step's obligation is local: a character the scanner takes from `s` to `s'` extends a completion of `gp(s')` to one of `gp(s)`. `sipr` is `sip.read` with a motive that also sees the mode and the text still to read, a mechanical transformation like the one that made `sip.read` from TOML-RT-3's `gd_read`; (b) forward, with the text read so far as a ghost argument and a partial derivation of it carried as an existential through every step, as ezjson's `jl` does; (c) Trusted, a weakening. Recommend (a), with a spike over the header and key states first (as REVIEW-R5 did for TOML-RT-3), and decide then with its size in hand. Option (a) builds the existential once, from the end back, and each state's obligation needs nothing that came before it. Option (b) threads a Sigma through every one of the 35 states. Decided: (a), as recommended. -->
- [x] <!-- REVIEW-G6 (resolved): Should anything move to Trusted? The estimate below is 52,000 to 84,000 lines of proof for the six rows, of which TOML-TEXT-1's refusal direction (WP-R) is the largest and least certain part, 15,000 to 25,000. Options: (a) keep every row Proved. Decide WP-R's fate after its spike, as with REVIEW-R5; (b) move "a text `parse` accepts matches the grammar" to Trusted now, keeping the accept direction and TOML-TEXT-2 Proved; (c) move TOML-TEXT-1 to Trusted whole. Recommend (a). Nothing measured so far says the refusal direction is out of reach: KEY-3's "any text" half went through the same scan induction at 13,850 lines. Moving any part to Trusted is a weakening the maintainer approves. Decided: (a), as recommended. -->
- [x] <!-- REVIEW-G7 (resolved): The order of the packages. Options: (a) values first: WP-G, then WP-N1, WP-T1 and WP-S1 in parallel, then WP-V, which proves TOML-NUM-1, NUM-2, TIME-1 and STR-1, then WP-A and WP-D2 (TOML-TEXT-2), then WP-R (TOML-TEXT-1); (b) TOML-TEXT-2 first, with WP-A over a value contract whose proof comes later; (c) the refusal spike first, to size the largest risk before anything else. Recommend (a), with WP-A allowed to start against the value contract once WP-V states it, and WP-R's spike run as soon as WP-G lands. Four rows close early, each package ends with a row or a named piece, and the transcription is reviewed before any large proof rests on it. Decided: (a), as recommended. -->
- [x] <!-- REVIEW-G8 (resolved): Invalid UTF-8 and TOML-TRUST-3. toml-test after all fixes: valid 208 of 208, invalid 495 of 501. The six left are `invalid/encoding/bad-codepoint` and the five `bad-utf8-in-*` cases. Bend's `File.read` replaces each bad byte with U+FFFD, which is a valid character in a comment or string, so `parse` reads each file as the valid text it now is. TOML-TRUST-3 says "invalid UTF-8 is the reader's to reject", but the reader a Bend caller has does not reject it. Options: (a) keep TOML-TRUST-3, reword its reason to say that `File.read` substitutes U+FFFD rather than rejecting, and tell callers in the README that a file must be checked as UTF-8 before `parse` when invalid bytes must be refused; (b) add a byte-level entry point that decodes and refuses, as a Future Step with its own row; (c) leave it. Recommend (a) now and (b) as a Future Step. The grammar rows are stated over code points and are unaffected either way. Decided: (a), as recommended. -->
- [x] <!-- REVIEW-G9 (resolved): What a newline in a multi-line string denotes. `"""a<CR><LF>b"""` reads as `a`, CR, LF, `b`: the newline is kept as written. The specification lets a parser normalize newlines ("TOML parsers should feel free to normalize newline to whatever makes sense for their platform"), so TOML-STR-1's "the text it denotes" does not settle it. Options: (a) the denotation keeps each newline as written, which is what the code does; (b) normalize CRLF to LF, which changes the code, and `render` would then write a lone LF where the source had CRLF. Recommend (a), stated in WP-G's `g.val` and quoted in TOML-STR-1's Left-to-prove entry. No change. Decided: (a), as recommended. -->
- [x] <!-- REVIEW-G10 (resolved): The spike's law and the gate. `dec_int_word` is a partial law of TOML-NUM-1, and WP-N1's exact law subsumes it. Options: (a) delete it when TOML-NUM-1 is proved and keep its lemmas, as REVIEW-R6 did for the round trip's spike; (b) keep it as the `dec-int` case of the accept direction. Recommend (a). On the gate: PROOF.bend is 63,500 lines, and this plan roughly doubles it. We expect the gate to reach 30 to 45 s (see Gate time). Recommend recording the time in each PR, as before, and only if it passes 45 s moving lemma families into modules that `ez prove` can check in parallel, which is a change to the build and a decision of its own. Decided: (a), as recommended. -->

## Summary

Five of the six rows are about what `parse` does with a given kind of text. TOML-NUM-1, TOML-NUM-2 and TOML-TIME-1 are about bare words, TOML-STR-1 is about strings, and TOML-TEXT-2 is about the order in which keys and tables are defined. TOML-TEXT-1 is about every text. We plan them on one law-side object, toml.abnf transcribed as a derivation type with Bool recognizers at its leaves (REVIEW-G3). Three kinds of proof are built on it:

- **Word-level exactness** (WP-N1, WP-T1). For every list of characters, `word.val` gives an integer, a float, a boolean or a datetime exactly when the word matches that rule, with the value it denotes. A lift (WP-V) states each of these over `parse`, from every scanner state that waits for a value. This proves TOML-NUM-1, NUM-2 and TIME-1.
- **Readers of derivations** (WP-S1, WP-A). For every derivation, `parse` of its text is the replay of its expressions. WP-S1 covers strings of every form and every piece, which proves TOML-STR-1. WP-A covers everything else: comments, blank lines, CRLF, and whitespace wherever the ABNF allows it. With a transcription of the specification's definition rules (WP-D2), this proves TOML-TEXT-2 and the accept direction of TOML-TEXT-1.
- **A text `parse` accepts has a derivation** (WP-R). This is a generalized scan induction whose invariant is a grammar position the scanner's state tracks (REVIEW-G5). With the two above, it proves TOML-TEXT-1.

The estimate, calibrated against this project's record, is 52,000 to 84,000 lines of proof, and a gate of 30 to 45 s. TOML-TEXT-1 and TOML-TEXT-2 need rewording before they can be proved (REVIEW-G1, REVIEW-G2).

## Context

### What is proved, and what the rows need

Every row in this plan is pending. The Law cells list partial laws, all of which the plan keeps.

| Row | Proved now | Left: accept exactly the grammar | Left: refuse everything else |
| :---- | :---- | :---- | :---- |
| TOML-NUM-1 | two signs and `0_` refused (`num_two_signs`, `word_two_signs`, `num_zero_underscore`, `num_signed_zero_underscore`, their word forms); one sign keeps the scan going (`num_one_sign`); every well-formed integer as `render` writes it reads back (`int_word`, `int_reads_back`); the spike: every `dec-int` within signed 64 bits, `+` and `_` included (`dec_int_word`); `gd_word` (TOML-RT-3): every integer `word.val` returns has decimal digits with no leading zero, in range | `hex-int`, `oct-int`, `bin-int`, and their value's decimal digits; stated over `parse` | every word that `word.val` reads as an integer matches `integer` and is in range, and the digits are the value's; stated over `parse` |
| TOML-NUM-2 | the same refusals; every well-formed float as `render` writes it reads back (`flo_word`); `gd_word`: every float `word.val` returns is spelled as `wf.flo`'s grammar | every word matching `float`, a `+` sign, `_`, signed `inf` and `nan`, and `E` included; the render half (a definitional lemma over `render.atom`); stated over `parse` | every word read as a float matches `float`; stated over `parse` |
| TOML-TIME-1 | the day is checked against the month and leap years, for every date (`date_day_in_month`, `date_day_past_month`); every well-formed datetime as `render` writes it reads back (`when_word`); `gd_word`: every datetime `word.val` returns is in range | lowercase `t` and `z`, a space as the separator (the scanner's `LDate` state), fractions of any length, and the four forms with RFC 3339's ranges; the render half; stated over `parse` | every word read as a datetime matches one of the four rules within the ranges; stated over `parse` |
| TOML-STR-1 | quotes before a multi-line closing delimiter (`ml_basic_one_quote` and three more); `""` and `''` ending the text; a string as `render` writes it reads back in every value position (`basic_string_reads_back` and two more) | basic strings of any pieces (raw characters, tab, all seven escapes, `\u` and `\U` in either case); literal strings; multi-line basic strings with line-ending backslashes and the newline after the opening delimiter; multi-line literal strings; in keys (TOML-KEY-3 already covers basic and literal keys) | a string text outside its form: a control other than tab, U+007F, a bad escape, `\u` of a surrogate, a lone CR, a newline in a one-line string, an unclosed string |
| TOML-TEXT-2 | the per-step laws of the table fixes and WP-W (a dotted key refused into a header's table or an array of tables, a header's table recorded, a new element forgetting its tables, `walk_put_refused_exactly`, `header_refused_exactly`, `aot_header_refused_exactly`, `failed_walk_changes_nothing`) | that the steps compose to `parse` on every text the grammar derives, and that each rule of the prose is what the walks check | the same: "exactly when" in both directions over the composition |
| TOML-TEXT-1 | `fail_stays`, and step laws for comments, lone CRs, a value after the key's line, and header quotes and blanks | every text the grammar (with the prose restrictions, REVIEW-G1) derives, whose definitions TOML-TEXT-2's rules allow, is accepted | every text `parse` accepts has a derivation |

### What probing found

We built a driver against `main.bend` at `65756da` (the one earlier audits used: `bad`, the tagged JSON and `render` of each document) and ran about 260 small texts through it. Each was chosen to test one ABNF rule or one prose rule. Every result agreed with TOML v1.0.0's prose, and the only disagreements with the ABNF are REVIEW-G1's five. We also ran the REVIEW-G1 and REVIEW-G2 texts through Python's `tomllib`, which agrees with `parse` on all of them except the big integer, which it keeps, and the byte-order mark, which it refuses.

- **Agrees with the grammar:** comments right after a value (`a = 1#c`), after a header and inside arrays; trailing commas in arrays and none in inline tables; newlines inside arrays and none inside inline tables; `0x00`, `0o0_0` and hex in either case read as 0; `0X1`, `+0x1`, `0x_1`, `1__2`, `1_`, `_1`, `-00`, `01.5`, `.5`, `1.` and `1e_1` refused; `1E5`, `1e05` and `1e1_0` read; `NaN`, `Inf` and `True` refused; `t`, `z` and a space as the separator read; `1979-05-27T07:32Z` (no seconds), `07:32:00Z` (a zone on a local time) and `1979-05-27  07:32:00` (two spaces) refused; `2000-02-29` read and `2100-02-29` refused; `23:59:60` read.
- **Strings:** seven and eight quotes (`"""""""`, `""""""""`) read as one and two quotes, and nine are refused; a line-ending backslash with tabs, blank lines and CRLF after it drops them all; a backslash followed by a space and no newline is refused; the newline after the opening delimiter is dropped, as LF or CRLF; a CRLF inside the body is kept (REVIEW-G9); U+007F is refused in all four forms; a raw tab is kept; `"""a"""` as a key is refused.
- **Definitions:** `[a]` then `[[a]]`, `[[a]]` then `[a]`, `a = []` then `[[a]]`, `a = [{b = 1}]` then `[a.c]` or `[[a]]`, an inline table extended by a header or a dotted key, `a.b = 1` then `[a]`, `[a.b]` then `[a]` and `b.c = 1`, and duplicates in an inline table are all refused. `[[a]]` / `[a.b]` / `[[a]]` / `[a.b]` (a new element is its own scope), `a.b.c = 1` then `[a.b.d]`, and `[a.b.c]` then `[a.b]` are all read. `[a.b.c]` then `[a]` and `b.d = 1` is also read (REVIEW-G2).
- **Byte-order mark:** one leading U+FEFF is read; a second one, or one later in the text, is refused ("invalid key"); one inside a comment is kept.

The five texts of REVIEW-G1 are the complete list of disagreements we found. The probe driver and the case lists are not committed and are not evidence for any row (RFC, Abandoned Ideas).

## Design

### The grammar relation (WP-G)

In LAWS.bend, a section `# GRAMMAR` holds toml.abnf transcribed, one constructor or def per rule, with the rule quoted above it. Bounds are in decimal with their hex beside them, as `abnf.unquoted_key` already is.

| |
|:---:|
| <pre>leaves (Bool recognizers over characters or a word):<br>  abnf.ws, abnf.newline, abnf.non_eol, abnf.unquoted_key (exists),<br>  abnf.integer = dec_int / hex_int / oct_int / bin_int   (dec_int: the spike)<br>  abnf.float, abnf.boolean, abnf.date_time = offset / local-date-time / local-date / local-time<br><br>structure (a derivation type, with g.text, g.ok and g.val):<br>  Gd    = expressions separated by newlines, each: ws [comment] / ws keyval ws [comment] / ws table ws [comment]<br>  GKey  = segments (KSeg, from KEY-3: bare, basic of KPiece, literal) with the ws around each dot<br>  GVal  = GWord{w} (a bare value: integer, float, boolean or date-time, w its characters)<br>        &#124; GStr{form, pieces} (the four string forms; basic pieces are KPiece)<br>        &#124; GArr{cells with ws-comment-newline, trailing comma} &#124; GInl{keyvals with inline-table-sep}<br><br>the prose (REVIEW-G1, REVIEW-G2):<br>  g.ok also asks: integers within signed 64 bits, dates and times in RFC 3339's ranges,<br>  \u and \U escapes naming Unicode scalar values, no U+007F in a comment<br>  defs(expressions): TOML-TEXT-2's definition rules over the key paths and headers, in order</pre> |
| Caption: the grammar relation. A text matches when it is `g.text(d)` for a derivation with `g.ok(d)`, after one leading U+FEFF if REVIEW-G1 (a) is accepted. |

Three choices keep the transcription trustworthy:

- **Close to the ABNF, reviewed against it.** Each leaf def's body has the ABNF rule's shape: `Bool.or` for `/`, `Bool.and` for concatenation, a recursive def for `*` and `1*`. The spike's `abnf.dec_int`, `abnf.unsigned_dec_int` and `abnf.dec_rep` show this, and the review reads them against toml.abnf line by line. Where the shape has to differ, a comment says why. In the spike, a lone character left in `*( DIGIT / underscore DIGIT )` can only be a DIGIT, and Bend's lack of mutual recursion forces the two-level match. The derivation's constructors are named after the rules they spell.
- **Prose restrictions named, not buried.** Each restriction the ABNF leaves to prose is its own def with the sentence of the specification quoted above it: `abnf.int_in_range` over the decimal digits, reusing `i64.fits`'s constants as `wf.int` does; the date ranges through `days_in`, which TOML-TIME-1's laws already transcribe from RFC 3339; `abnf.escape_scalar`; `abnf.comment_char`. REVIEW-G1's rewording names the same four.
- **Denotation beside recognition.** `g.val(d, v)` says that `v` is the value `d` denotes, as the rows state it. It is a Bool relation rather than a function because of integers. For an integer, it is the sign and the decimal digits of the value. That is stated as a relation, not computed: the digits have no leading zero, and their value in base 10 is the numeral's value in its base, with both sides as symbolic `Nat`s (see Risks on large literals). For a float, the sign and the spelling with the sign and `_` removed. For a datetime, the fields. For a string, the characters the pieces stand for, with each newline as written (REVIEW-G9).

The derivation is data and the leaves are Bool, as REVIEW-G3 recommends. A text matches the grammar exactly when some derivation spells it (`g.text(d) == t`) and follows the rules (`g.ok(d)`). Laws that start from the grammar quantify over `d`, and laws that end in it are `exs d`, as ezjson's `text_derives` is.

### Relating it to the scanner, in both directions

| |
|:---:|
| <pre>accept (WP-A, WP-S1, WP-V):  for every derivation d with g.ok(d),<br>    own(parse(g.text(d))) == replay(d)        replay: each expression's walk, in order, from the root,<br>                                               with each leaf's value as its reader gives it<br>                                               (WP-N1, WP-T1, WP-S1 tie that to g.val); the first walk error is the doc's<br>refuse (WP-R):  for every scanner state s and text t,<br>    bad(doc.read(t, s)) == ""  ==&gt;  exs c. t == c.text and c completes gp(s)<br>    and at the start, gp(st.start()) is the whole document: exs d. t == g.text(d) and g.ok(d)<br>meaning (WP-D2):  replay(d) has no error  &lt;=&gt;  defs(d)</pre> |
| Caption: the three statements the rows are built from. TOML-TEXT-2 is the first and the third, and TOML-TEXT-1 is all three. |

**Accept direction: a simulation by the derivation.** The accept lemmas are the round trip's readers made general. They are stated in premise form, from every scanner state of a shape, over any rest of the text, with the rest of the walk as a motive over the fields the text does not decide, as `kq.Goal`, `qu`, `hm` and `vpos` are. Most of the hard pieces exist already. KEY-3's `key_reads_back_anywhere` and `header_reads_back_anywhere` read keys and headers spelled any way. WP-C's `value_reads_back` reads nested arrays and inline tables, but only as `render` spells them. WP-D's document induction runs the key pass and then the table pass. What is new: comments and blank lines between any two tokens the ABNF allows them between, CRLF everywhere, the whitespace forms of `array-values` and `inline-table-sep`, dotted keys in every position, values of every spelling (WP-V and WP-S1), and expressions in any order. The last is simpler than WP-D's, since the replay is in text order rather than `canon`'s.

**Refusal direction: a grammar position tracked by the state.** The scanner does not keep the text it has read, but it keeps enough to say which rules are open: its lex state, `back` (the state a comment returns to), `qkind`, the stack of open arrays and inline tables with their saved keys, and the word in `buf`. A law-side `gp(st)` maps each state to a grammar position: the open rules of a partial derivation, innermost first. Its completions are the derivations' tails that close those rules. The induction is `sipr`, a version of `sip.read` whose motive sees the mode and the text still to read (REVIEW-G5 (a)). The step obligation is backward, per state: if the step from `s` to `s'` on `c` did not fail, a completion of `gp(s')` by `t` gives one of `gp(s)` by `c` and then `t`. Every failing arm is free, because `fail_stays` leaves an error that makes the premise false. So only the accepting arms carry content. Words and strings finish in two places. `bare.finish` calls `word.val`, and the obligation there is WP-N1's and WP-T1's refusal halves: a word read as a value matches its rule. A closing quote needs WP-S1's refusal half: the pieces read so far are well-formed. The per-state dispatch is the shape KEY-3's `kg.*` has, which was TOML-RT-3's `gd.g.*` transformed mechanically. We expect the same transformation to give most of it.

This is the sense in which "the scanner's state tracks a grammar parse state" holds in both directions. Accepting runs the derivation through the states, and refusing reads a derivation back out of them.

### TOML-NUM-1, TOML-NUM-2 and TOML-TIME-1 (WP-N1, WP-T1, WP-V)

These are word-level, and the rows' "exactly when it matches the rule" halves are statements about `word.val`. One classifier law says it all:

```
# LAW: a bare word reads as a value exactly when toml.abnf's bare value rules
# give it one: an integer within signed 64 bits, a float, a boolean or a
# datetime within RFC 3339's ranges, and the value is the one it denotes
law word_is_grammar:
  for +cs: List<&2, Char>
  for +v: T.Val
  {got.is(T.word.val(cs), v) == g.word(cs, v) : Bool}
```

Here `got.is(g, v)` says `g` is `GotVal{v}`, and `g.word(cs, v)` says `cs` matches one of the four rules and `v` is what it denotes. The rules are disjoint, which the review checks. Since the law holds for every `v`, a word with no rule reads as no value at all. Each row takes its part: TOML-NUM-1 the integer case, TOML-NUM-2 the float case, TOML-TIME-1 the four datetime forms. The proof splits by how `word.val` routes the word: the specials `true`, `false`, `inf` and `nan` and their signed forms; a word with a colon, or a dash after its first character and no `e` or `E`, which goes to the datetime reader; and everything else, which goes to the numeral scan.

- **Accept direction.** The spike's form, one lemma per rule, reading the transcribed rule apart. `gs.rep.two` takes `*( DIGIT / underscore DIGIT )` apart into its two shapes. `gs.scan` shows that an underscore between digits leaves the numeral as it was. Then WP-N's `nw`, `dgo`, `dtext` and `int.fin` finish the job. `hex-int`, `oct-int` and `bin-int` need `dec.go` with radix 2, 8 and 16 related to the value: `val10(dec.go(ds, r, c)) == val10(ds) * r + c` as symbolic `Nat`s, then induction over the digits. Floats reuse `flo_word`'s scan with underscores and a `+` added, the way the spike added them to integers. Datetimes reuse `when_word`'s field readers, with the digits of each field symbolic (`take.n` over two digits, each from `dg.elim`, so 10 cases per digit rather than 100 per field) and `date_day_in_month` for the day.
- **Refusal direction.** A word `word.val` reads as an integer matches `integer`, within range, with those digits. `gd_word` (TOML-RT-3) already pairs the numeral scan's state with `wf.flo`'s automaton through every character. We extend that pairing to a state of the transcribed rules: each `NK` state with its sign, `us` and `saw` flags corresponds to a position in `dec-int`, `hex-int` and the float rules. At `num.fin`, `GotVal` is returned only in positions where the rule is complete. The datetime reader is a straight-line reader (`take.n` twice, then a separator), so its refusal half is a case split along it, not a simulation. `bare_word_refusal_says_why` shows that each refusal is a `GotBad`.
- **Stated over `parse` (WP-V).** A lift, in the premise form of `word_reads_back`. From every state that waits for a value, with the fields a bare value does not decide free (`Vf`), a word of word characters followed by any character that ends a word reads as follows. The ending characters are a space, a tab, a newline, CRLF, `#`, `,`, `]`, `}`, or the end of the text. If `word.val` classifies the word, the rest reads on with the value placed (`after_val`). Otherwise the document has an error (`fail_stays`). WP-C already has the `,`, `]` and `}` ends (`wd.end`). A datetime with a space needs `LDate`: a date-shaped buffer, the space, and a digit. The rows then follow as parse-level corollaries, for a bare key `k` and a word `w`: `parse(k ++ " = " ++ w)` is `Doc{"", [VPair{k, v}]}` when `g.word(w, v)`, and has an error when no value is related to `w`. The render halves of TOML-NUM-2 and TOML-TIME-1 are lemmas over `render.atom`: `sign.text` writes only `-`, and `when.text` writes `T` and `Z`.

### TOML-STR-1 (WP-S1)

The row covers every form and every text the form can hold, so the reader is stated over a derivation of the string: its form (basic, literal, multi-line basic, multi-line literal) and its pieces. For basic strings the pieces are KEY-3's `KPiece`: a character written as itself (a tab among them), one of seven escapes, or `\u` or `\U` with `KHex` digits in either case, naming a scalar value. Multi-line basic strings add a newline (LF or CRLF), a line-ending backslash with the whitespace and newlines after it (`mlb-escaped-nl`), and one or two quotes that are not the delimiter. Multi-line literal strings add newlines and one or two apostrophes.

- **Reuse.** KEY-3's symbolic hex reader (`k3.hx.dv`, `k3.hx.ok`, `k3.hx.scan`): `dig.val` is computed on a digit's character alone, and every code point goes through the same lemmas. So `\u` and `\U` of any scalar value cost nothing per code point. The `qu` family reads escapes in keys with `uni` and `left` free. WP-S reads a one-line basic string in a value position, span and copy included. `ctl.esc.all` and `Eq.ctl.all` handle the 33 controls in one enumeration each.
- **New.** The value-position states rendered text never visits: `LMq` and `LMqEnd` (the multi-line body and its closing quotes, generalizing V1's four laws from `x` to any body), `LFold`, `LTrim` and `LTrim2` (a line-ending backslash, blanks and newlines after it), the newline after the opening delimiter, literal strings through the span modes with `q` an apostrophe, and `MCr` inside a body for CRLF.
- **Refusal half.** A string text outside its form sets an error: a control other than tab (and a newline in a one-line form), U+007F, an escape that is not one of TOML's nine (seven letters, `\u` and `\U`), `\u` of a surrogate or `\U` past U+10FFFF (`uni.ok`), a lone CR (`lone_cr_refused` covers every state), and the end of the text inside a string (`read.fin`). WP-R needs this as its obligation at a closing quote, and TOML-STR-1 needs the accept half. The row as worded is only the accept half ("`string` of the value `parse` reads is the text it denotes"), so the refusal half is not on the row's critical path.
- **Stated over `parse`.** As WP-S did, from every value position (`sv.val`, `sv.arr`, and the inline table's), with the rest of the walk a motive over the document. A parse-level corollary follows for `k = <string>`.

### TOML-TEXT-2 (WP-A, WP-D2)

With a derivation in hand (the row is about texts that match the grammar), WP-A gives `parse(g.text(d))` as the replay of `d`'s expressions through `tree.walk`. TOML-TEXT-2 then has no scanner in it: the replay sets no error exactly when `defs` accepts the expressions (REVIEW-G4 (a)).

`defs` transcribes the specification's prose on tables. It is a law-side record of what each path is: a pair's value, a table a header named, a table a header only created on its way, a table dotted keys made, an array of tables, a static array, or an inline table. The record is updated per expression, with each rule a sentence quoted above its arm. The same sentences are in TOML-TEXT-2. The induction's invariant gives `heads` its meaning: while the replay has no error, every entry in `heads` behind `[` is a path `defs` records as named by a header in the current scope, and every entry behind `.` is one dotted keys made. The rows at each path hold what `defs` records. A new element of an array of tables drops the entries under it (`heads.drop`, and `new_element_forgets_tables_under_it` and `new_element_keeps_other_tables`, which are proved already). Each step is one of WP-W's exact contracts (`walk_put_refused_exactly`, `header_refused_exactly`, `aot_header_refused_exactly`) set beside the matching `defs` arm. What is new is the relation between the record and `(rows, heads)`, and inline tables, whose dotted keys build `VHead` tables that `inl.seal` closes (`closed_inline_table_holds_no_open_table` and `inline_table_refuses_keys` are the step laws).

`sip.read` is the right tool when the claim is about every text and the invariant is a function of the state. TOML-TEXT-2's claim is about the expressions of a derivation, so the derivation is the thing to induct on. The scan induction is reused by WP-R.

### TOML-TEXT-1 (WP-A, WP-D2, WP-R)

With REVIEW-G1's rewording, TOML-TEXT-1 is two laws:

```
# LAW: a text the grammar derives, whose definitions the prose allows, parses
# with no error
# TOML-TEXT-1
law text_accepted:
  for +d: Gd
  for +h_g: {g.ok(d) == True{} : Bool}
  for +h_d: {defs(d) == True{} : Bool}
  for h_s: {short(g.text(d)) == True{} : Bool}
  {String.is_empty(T.bad(T.parse(g.text(d)))) == True{} : Bool}

# LAW: a text that parses with no error is one the grammar derives, and its
# definitions are ones the prose allows
# TOML-TEXT-1
law text_derived:
  for +t: String
  for +h_u: {scalars(t) == True{} : Bool}
  for +h_s: {short(t) == True{} : Bool}
  for +h_p: {String.is_empty(T.bad(T.parse(t))) == True{} : Bool}
  exs d: Gd
  ({bom.drop(t) == g.text(d) : String} & {Bool.and(g.ok(d), defs(d)) == True{} : Bool})
```

`text_accepted` is WP-A then WP-D2. For `text_derived`, WP-R gives the derivation, and then WP-A and WP-D2 applied to that same derivation give `defs(d)`: its replay is `parse(t)`, which has no error. The rows are ambiguous-grammar safe. Two derivations of one text have the same `defs`, since both equal "`parse` of the text has no error".

## Plan

### The spike

`dec_int_word` (tagged TOML-NUM-1) is in LAWS.bend and PROOF.bend under `# GRAMMAR SPIKE`. For every list of characters that matches toml.abnf's `dec-int`, transcribed rule by rule (`abnf.minus`, `abnf.plus`, `abnf.underscore`, `abnf.digit1_9`, `abnf.DIGIT`, `abnf.dec_rep`, `abnf.dec_rep1`, `abnf.unsigned_dec_int`, `abnf.dec_int`), and whose digits fit in signed 64 bits, `word.val` reads the integer. Its sign is minus when the word starts with one and plus otherwise. Its digits are the ones after the sign, with the underscores removed (`abnf.dec_digits`).

- **It settled the leaf form.** A Bool recognizer shaped like the ABNF proves against the scanner directly. It needs no normal form: the proof takes the rule apart with one continuation-passing lemma per repetition (`gs.rep.two`), and each shape goes to WP-N's existing numeral lemmas. An alternative is taken apart by the test that tells its branches apart (a DIGIT or an underscore first), passed as a Bool with its equation, as the scanner's own dispatch is. The transcription needed one bit-level fact that WP-N did not have: a `digit1-9` is a digit and is not 0. It came from the lowest bit of the code point against 48 and 49 (`gs.ge01`, `gs.eq01`), with the upper 31 bits left symbolic. The same trick gives any ABNF `%xNN-MM` range whose bounds differ in their low bits.
- **It found a gap the gate had.** A planted bug, an underscore read as a 0 digit (`1_2` read as 102, by pushing a 0 in `num.us.go`), passes the gate at `65756da`, since no law reads a word with an underscore. With the spike it fails on `gs.us.step`.
- **Cost.** 143 lines of law and 792 of proof, over the 500 we aimed for. Each of the three sign forms routes differently through `word.val` (a minus and a plus are special-word candidates that must be shown not to be `-inf`, `+nan` and so on), so the multi-digit case is written three times. The gate went from about 17.0 s to about 18.0 s (three runs each, on this machine). All of that is the 30 lone-digit words evaluated concretely, and a symbolic lemma over `dg.elim` would remove it. The law fails the gate when its proof is replaced by `{==}`. Lint: 0 errors. One tooling note: bolt reports U001 (an unused parameter) for a parameter used only inside a dependent function type `@x: A -> {...}`, so the spike avoids that form.
- **Calibration.** The spike covers about a tenth of TOML-NUM-1's accept direction, and took about 800 lines. Its hex, octal and binary forms need the radix lemma, and the refusal direction is a simulation. So TOML-NUM-1 alone is about 3,000 to 4,500 lines, which is inside WP-N1's estimate below.

### Work packages

| |
|:---:|
| <pre>WP-G ──┬──▶ WP-N1 ──┐<br>       ├──▶ WP-T1 ──┼──▶ WP-V ──▶ TOML-NUM-1, TOML-NUM-2, TOML-TIME-1<br>       ├──▶ WP-S1 ──┼──────────▶ TOML-STR-1<br>       │           ▼<br>       ├──▶ WP-A (values through WP-V's and WP-S1's contract) ──▶ WP-D2 ──▶ TOML-TEXT-2<br>       └──▶ WP-R spike ──▶ WP-R (with WP-N1, WP-T1 and WP-S1's refusal halves) ──▶ with WP-A, WP-D2: TOML-TEXT-1</pre> |
| Caption: the work packages. WP-N1, WP-T1, WP-S1 and the WP-R spike can start as soon as WP-G is reviewed. WP-A can start once WP-V states its contract, before WP-V is proved. |

Estimates are lines of proof. The "planned" column is what the naive reading of each package gives, the way the round-trip plan sized its packages. The "expected" column multiplies that by this project's record, which ran 2 to 4 times over plan: WP-C 5,000 against 1,200, WP-D 8,200 against 2,000, RT-3 10,800 against 3,000 to 5,000, KEY-3 13,850 against 1,200 at first (and 15,000 once re-planned). Where a package reuses a lot of proved machinery, we use the low end of that ratio. Where it is new ground, we use the high end.

| WP | Scope | Needs | Planned | Expected |
| :---- | :---- | :---- | :---- | :---- |
| WP-G | toml.abnf transcribed: derivation type, leaf recognizers, `g.text`, `g.ok`, `g.val`, the four prose restrictions, `defs`; basic facts (disjointness of the word rules, `g.text` of a derivation's parts); reviewed against the ABNF and the prose | REVIEW-G1 to G3 | 400 of proof, 1,200 of law | 800 to 1,200 of proof, 1,500 to 2,000 of law |
| WP-N1 | integer, float and boolean words exact in both directions (`word_is_grammar`'s numeric cases): radix lemma for `dec.go`, `hex-int`, `oct-int`, `bin-int`, floats with `+` and `_`, the scan simulation extended from `gd_word` to the transcribed rules | WP-G | 2,500 | 6,000 to 9,000 |
| WP-T1 | datetime words exact in both directions: the four forms, `t`, `z`, a space, the ranges, symbolic field digits; the render half | WP-G | 1,800 | 4,000 to 7,000 |
| WP-V | the lift over `parse`: any bare word from every value state, every ending, `LDate`, refusal to an error; parse-level corollaries; proves TOML-NUM-1, NUM-2, TIME-1 | WP-N1, WP-T1 | 1,000 | 2,500 to 4,000 |
| WP-S1 | strings: four forms, all pieces, the multi-line states, the first newline, CRLF, in every value position; refusal half; proves TOML-STR-1 | WP-G | 3,000 | 8,000 to 12,000 |
| WP-A | `parse(g.text(d))` is `replay(d)`: comments, blank lines, CRLF, whitespace everywhere, dotted keys, arrays and inline tables of any spelling, expressions in any order | WP-G, WP-V's and WP-S1's statements | 5,000 | 12,000 to 18,000 |
| WP-D2 | `replay(d)` has no error exactly when `defs(d)`; `heads` given its meaning; proves TOML-TEXT-2 | WP-A | 1,500 | 4,000 to 7,000 |
| WP-R | a spike over the header and key states, then `sipr` (the scan induction with the text still to read in its motive), `gp` and its completions, every accepting arm; with WP-A and WP-D2 proves TOML-TEXT-1 | WP-G; WP-N1, WP-T1, WP-S1 refusal halves | 5,000 | 15,000 to 25,000 |
| | **total** | | 20,000 | 52,000 to 84,000 |

For scale: PROOF.bend is about 63,500 lines. The round trip and KEY-3 together were about 50,000 lines against a plan of 14,000 to 18,000.

### Gate time

The gate takes about 17 s on this machine at `65756da` (the round-trip notes give 18 to 22 s on theirs), and about 18 s with the spike. The record says what moves it. Symbolic proofs are cheap: TOML-RT-3's 5,400 lines in its second half added 0.7 s, and KEY-3's 13,850 lines left the gate within its noise. Concrete evaluation is what costs. WP-N's digit pairs and datetimes added about 8 s. The control escapes, before `ctl.esc.all`, added 5 s. The spike's 30 concrete words added 1 s. Projection:

- about 0.1 to 0.15 s per 1,000 symbolic lines: +5 to +12 s;
- the control enumeration in each new string state family (`LMq`, `LFold`, `LTrim`, literal and multi-line literal bodies), through `ctl.esc.all` and `Eq.ctl.all`: +3 to +6 s;
- digits through `dg.elim` (10 cases each) in the datetime and radix readers: +1 to +3 s;
- a few concrete words, as in the spike: +1 to +2 s.

Expected: 30 to 45 s. The mitigations are those of the round trip: symbolic lemmas before concrete enumeration where both work (the hex reader is the model), and the time recorded in each PR description. REVIEW-G10 sets the point at which splitting the file would be worth a decision.

## Risks

- **Rows false as worded.** REVIEW-G1 and REVIEW-G2 list what the probes found. There may be more, as there were in the round trip (the U32 wrap, `at` and arrays). The transcription review is where the next one will surface. Any text the grammar relation and `parse` disagree on is a finding with its own REVIEW item, never a quiet change to the relation.
- **The transcription encodes a mistake.** It is checked by reading only. The mitigations are one def per rule with the rule quoted, the prose restrictions named separately, RFC 5234's case-insensitive strings called out, and the probe cases above re-run by hand against the transcription during review. The review can evaluate the transcription on small texts with a scratch driver. That is a reading aid, not evidence.
- **The refusal direction's size.** WP-R is the largest and least measured package, as TOML-RT-3 was before its spike. REVIEW-G5 and REVIEW-G6 put a spike first. The measured record for "every text" proofs (RT-3 at 10,800 and KEY-3 at 13,850, both inside their re-estimates once spiked) is the reason to expect it to go through.
- **Invalid UTF-8 (TOML-TRUST-3).** The six toml-test cases left are invalid UTF-8, which Bend's `File.read` turns into U+FFFD. They are valid texts once decoded, so no grammar row can refuse them, and no row is false because of them. They are REVIEW-G8's concern, not this plan's. A raw surrogate in a text is outside every row's domain, since the rows are stated for texts of Unicode scalar values.
- **toml-test is no evidence, and it could not have caught this.** Valid 208 of 208 and invalid 495 of 501 agree with the prose: toml-test expects U+007F in a comment, out-of-range dates and surrogate escapes refused (`invalid/control/comment-del` and others), so passing it says nothing about rows worded against the ABNF alone. That is how REVIEW-G1's five went unnoticed. Every row here is proved over all texts, and the corpus stays an audit tool.
- **Large numbers.** The integer denotation relates the digits to the value as `Nat`s. Checking a large `Nat` literal overflows the checker's stack (WP-N's `U32.to_nat(10000)`). So the range stays stated on decimal strings (`i64.fits`'s constants), and every `Nat` in these proofs stays symbolic.
- **Mutual recursion and the linter.** Bend has no mutual recursion, so `val`, `array-values` and `inline-table-keyvals` become one def over a mode, which is harder to read against the ABNF. Each such def says so where it is. bolt misses parameter uses inside a dependent function type (the spike's U001), which constrains how continuations are written.
- **The walk moves again.** A faster duplicate check (REVIEW-13 in the RFC) would change `tree.walk`. WP-D2 is stated over WP-W's contracts, not the walk's frames, so such a change reproves WP-W and leaves WP-D2 alone.
- **Proof size and gate time.** See Gate time and REVIEW-G10.

## Future Steps

- A byte-level entry point that decodes UTF-8 and refuses invalid bytes, with its own row (REVIEW-G8 (b)). Until then, TOML-TRUST-3 stands: Bend's `File.read` replaces an invalid byte with U+FFFD, and the README tells callers to check a file as UTF-8 before `parse` when invalid bytes must be refused.

## Update (WP-S1 landed)

TOML-STR-1 is proved, in LAWS.bend's and PROOF.bend's `# WP-S1` sections. `string_reads_as_denoted` is the reading law in premise form: from every state that waits for a value (WP-C's `vpos`, with every field a string leaves alone a parameter), the text of every string derivation (`GString`, all four forms, any pieces its form can hold) that matches its rule (`g.ok.str`) and stands for fewer than 2^32 characters, then any rest that starts with neither quote (`s1.free`), reads on as the rest from the state with a string value holding `g.str.chars` of the derivation placed (`s1.holds`: owned or a span), whatever back, qkind, uni and left the string leaves. `string_reads_as_denoted_in_array` is the same from an array's item (`s1.apos`, LArr). `string_short_in_document` says a string stands for no more characters than its text holds, so in a document shorter than 2^32 characters it stands for fewer than 2^32. `string_parses_as_denoted`, `_in_array` and `_in_inline_table` are the document forms: `k = <string>`, `k = [<string>]` and `k = {v = <string>}` with a newline, the document shorter than 2^32 characters, parse with no error to the pair holding `g.str.chars`. All six are tagged TOML-STR-1.

How it is proved:

- **One-line basic strings** reuse WP-S's span (`sv.open`, `sv.eat`, `se.close`, `se.own`, `se.copy`, `se.rev`, `ls.own`, `sv.empty`): characters written as themselves grow the span (a raw tab included, since `str.bad` passes it), and the first escape copies it; from there every KEY-3 piece (`KPiece`) is read in LStr (`s1.pc`, `s1.pcs`). `\u` and `\U` of every scalar value go through KEY-3's symbolic hex reader (`k3.hx.dv`, `k3.hx.ok`, `k3.hx.scan`) with LUni's state generalized over the string's kind (`s1.hx.*`).
- **Literal strings** are always a span (`s1.lo`, `s1.le`, `s1.lg`); `''` goes through LQ2 as `""` does (`s1.lempty`).
- **Multi-line strings** are read piece by piece over the derivation's body (`s1.mb` for `GMlb`, `s1.lb` for `GMll`) under the trim `g.mlb.chars` and `g.mll.chars` give each piece, with the state the trim says (`s1.ms`: LStr, LTrim, or LFold with the newline seen). A character that ends a trim, or one after quotes that did not close, is held and read again in LStr; since no multi-line LStr step holds a character, that is LStr's fast step (`s1.once`, `s1.enter`, `s1.mq.exit`). A line-ending backslash reads its `ws newline *( wschar / newline )` into the fold (`s1.enl`, `s1.fws`, `s1.fnl`, `s1.fwn`), and every newline goes through `s1.nl.elim` (LF, or CR LF through `MCr`), kept as written (REVIEW-G9). The closing delimiter with up to two more quotes is `s1.m3`, `s1.m3x` and `s1.mend`. Each body's induction hypothesis is a function over the rest's flag, trim, back, uni, left and buffer (`s1.MbRec`, `s1.LbRec`), so each piece is its own lemma.
- **Characters.** `basic-unescaped` and `literal-char` leave out every control but tab: one `Eq.ctl.all` enumeration per class (`s1.bu.tab`, `s1.lc.tab`) gives `s1.C9` (a control exactly when a tab), from which every scanner test follows symbolically.
- **Lengths.** `s1.ln` (no longer than) and `s1.counts.le`; each piece stands for at most one character and is written with at least one (`s1.ln.str`).

Findings: none. Every form read as its derivation denotes, both ABNF ambiguities of WP-G read as `g.str.chars` settles them, and `main.bend` is unchanged.

Size: 180 lines of law and 4,956 of proof (planned 3,000, expected 8,000 to 12,000). The gate is about 21 to 24 s (against about 19 to 21 s at `faeca45` on the same machine, varying with load). Lint: 0 errors, and no new warnings (140, as at `faeca45`). Break checks: replacing each of the six laws' proofs by `{==}` fails the gate. Four bugs planted in a scratch copy of `main.bend` each fail the full gate first on an older proof (KEY-3's or TOML-RT-3's), and with those stubbed (`isolate_mutant.py`) each fails a WP-S1 proof: a line-ending backslash keeping the next line's indent fails `s1.fws1.go`; literal strings decoding escapes (`\n`) fails `s1.once`; the first newline of a multi-line string kept fails `s1.mb.lf`; `\U` reading seven digits fails `s1.hx.open`.

Left for TOML-STR-1: nothing. The refusal half (a text outside its form sets an error) is not on the row and is left to WP-R, which needs it at a closing quote. Quoted keys are TOML-KEY-3's.
