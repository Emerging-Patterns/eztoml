# eztoml: proving the round trip

## Draft Status

**State:** Accepted. Every REVIEW item was accepted as recommended by the maintainer; REVIEW-R1's bound is in SPEC.md's TOML-RT-1, TOML-RT-2, TOML-RT-3 and TOML-STR-1. It plans the rows that go through the scanner on text the renderer wrote: TOML-RT-1, TOML-RT-3, TOML-RT-2, and the read-back half of TOML-KEY-2, with how TOML-KEY-3 and TOML-TEXT-2 reuse the machinery. The parent RFC is [eztoml-spec.md](eztoml-spec.md); its decisions stand. We read the code at `6fd13cb`, after the tables-and-headers fixes (I1, R2, V2, R3, I8) landed, and the spike below is on top of that commit.

The spike proved TOML-KEY-2 in full (`key_reads_back`), so that row is now proved, and a partial law of TOML-RT-1 for a document of one string pair (`render_parse_plain_pair`). The second spike found that TOML-RT-1 does not hold as worded for a string of 2^32 characters or more (REVIEW-R1).

**Update (WP0 landed).** The quoted-segment family is one set of lemmas over a Bool `hd` (a key segment, `LKeyQ`/`LKeyE`/`LKeyU`, or a header segment, `LHeadQ`/`LHeadE`/`LHeadU`), generalized over every field a quoted segment leaves alone, so inline-table keys (WP-C) and headers (WP-H) call it as it is; `qs.escs` is the entry point. Only basic-quoted segments are covered; literal ones are WP-K3's. `Eq.ctl.all` takes one answer per control code point (a motive law), which removes the copied case split but not the per-control computation, so the gate is about 1 s slower (6.2 s to 7.4 s): the header segment's 33 controls are now proved too, which WP-H needs anyway. A symbolic lemma for `\u00XX` is still the way to cut that. Besides `inc.dec`, `sub.inc` and `inc.nat`, the word lemmas `zw`, `lt_fin_f`, `zw_nlt` and `lt_up` moved to `src/eq.bend`, reached as `Eq.x`.

**Update (WP-W landed).** The walk's contracts are exact equations over law-side helpers in LAWS.bend: `tb.open` (the walk goes on through every segment of a path), `tb.rows` (the rows at its end), `tb.set` (the root with that table replaced) and `tb.join`; the target-name premises are over the public `get`, so WP-D discharges them with `get_misses` and `get_finds_first`. Beyond the plan, `tb_rows_after_set` and `tb_open_after_set` let one put's conclusion discharge the next put's premises. What the code does that the plan did not say: entering an array of tables and rebuilding stores its newest element as `VAot{<the array's path>, ...}`, and a header that defines an implicit table, or extends an array of tables, re-stores it under the header's joined path, so `canon` must store paths the same way (they agree with the stored ones on well-formed documents); `rows.repl` writes into every pair of a name while `get` reads the first, so on rows that already hold a duplicate name a refused walk can still change the rows, and the refusal laws state only the error; the put contract needs `counts.down(here, path.len(here, 0))`, U32 arithmetic for a `here` shorter than 2^32 segments, which WP-D proves with `Eq.inc.*`; arrays are not reversed by `rows.seal` (the array reader already reversed them), while tables and array-of-tables element lists are. Dotted-key segments (skip reaching 0 under a put, `.` marks) are not covered here; `nav.quiet` marks where they begin, for WP-K3 and WP-R3.

**Items for review:**

- [x] <!-- REVIEW-R1 (resolved): TOML-RT-1 is false for very long strings. `parse` keeps a plain one-line string as a span of the text and counts its characters in a U32 (`MEat`'s `n`, `U32.add(nn, 1)` per character). A string of 2^32 characters that `render` writes with no escape reads back as the empty string, and one of 2^32 + 5 as its first five characters. The same holds for TOML-STR-1, and for TOML-RT-2 and TOML-RT-3 through the texts they parse. A second U32, `path.len` (the header segments a key walks through as navigation), wraps only at 2^32 nested tables, whose text is longer still. Options: (a) bound the rows on the text, as ezjson did for JSON-TEXT-1 and JSON-PULL-1: TOML-RT-1 for `d` whose rendered text is shorter than 2^32 characters, TOML-RT-2 and TOML-RT-3 for `t` (and, for TOML-RT-2, `render(parse(t))`) shorter than 2^32 characters, TOML-STR-1 for strings shorter than 2^32 characters; (b) make the span fall back to the copying path when its count would wrap, which adds a test to the tuned per-character loop and still leaves `path.len`; (c) move the long-text case to Trusted, a weakening. Recommend (a): no code change, the bound is on the text a caller hands in or gets out, and ezjson's `short` (at most 2^32 - 1 characters) is the model. The spike's partial law already carries it, as `short(s)`. Rewording rows is a behavior change of the specification, not of the code. Decided: accepted as recommended. -->
- [x] <!-- REVIEW-R2 (resolved): What the core lemma states. `same` is the row's relation, but it is a Bool built from `pick` and `and_then`, which is awkward to carry through an induction. Options: (a) prove an exact equation, `own(parse(render(d)))` equals `canon(d)`, where `canon` (in PROOF.bend) reads every span out, sets the error to `""`, and puts each table's pairs that are not tables before its tables and arrays of tables, keeping their order, as `render` writes them; then TOML-RT-1 is `same(canon(d), d)` plus the spike's `own.l` and `own.r` step, and TOML-RT-2's second half is `render(canon(d)) == render(d)`; (b) carry `same` through every step. Recommend (a): every lemma in the spike is an exact equation, equations compose with `Equal.trans` and `Equal.cong` and need no Bool bookkeeping, and the exact form is what makes TOML-RT-2 cheap. `same(canon(d), d)` is one lemma over `same_swap`'s `pick.same`, `pick.skip` and `pick.swap`. Not a behavior change. Decided: accepted as recommended. -->
- [x] <!-- REVIEW-R3 (resolved): How the induction runs. Options: (a) structural induction on the document, with the text after it as a context: a lemma per shape says that reading the text `render` writes for it, then any text `rest`, from a scanner state that the lemma names, is reading `rest` from the state after it; (b) an invariant over the scanner's state as it walks any text, shake-style, relating the state to how much rendered text it has read. Recommend (a) for TOML-RT-1, TOML-RT-2 and TOML-KEY-3, which are about text `render` wrote or a caller spelled from pieces, and (b) for TOML-RT-3, which is about every text. The spike used (a), with the rest of the walk passed as a function of the fields the text does not decide (see "The invariant"), and it went through on the first run. Not a behavior change. Decided: accepted as recommended. -->
- [x] <!-- REVIEW-R4 (resolved): Refactors. We looked for changes to `main.bend` that would make the proofs tractable. The scanner's dispatch is already in the form proofs want: each step names its tests as Bool parameters (`lex.top.go(sp, nl, hash, ...)`), so a proof matches the same Bools and passes the facts it has. The renderer's two passes with thunks (`render.head`, `render.pass`) went through TOML-STR-2 without trouble. The one structure that costs proof is that every pair is inserted by walking its whole path from the root (`take.top` calls `tree.walk(path.cat(here, parts), ...)`) and the root is rebuilt frame by frame, so each insertion's lemma is about the whole root. A zipper that keeps the current table open would make that local, but it rewrites the table code the fixes just changed, and the contract lemmas of WP-W isolate the walk anyway. Recommend: no refactor of `main.bend` for this plan. Any later one must keep the output byte-identical on the corpus, checked with the harness, as the rule for this rollout says. The proof side does get one generalization: the quoted-key lemmas take the states they return to as parameters, so that key segments (`LKeyQ`) and header segments (`LHeadQ`) share them. Decided: accepted as recommended. -->
- [x] <!-- REVIEW-R5 (resolved): Should any row move to Trusted? The spike measured the two kinds of lemma this plan is made of: the scanner reading rendered characters (about 500 lines per family of states, mechanical) and arithmetic facts about the scanner's counters (about 250 lines, ported from ezjson). Neither is expensive enough to trust. TOML-RT-3 is the one whose cost we have not measured: its invariant has to hold in every state for every text, not only on rendered text. Recommend: keep every row Proved; start TOML-RT-3 with a spike of its invariant over the header states and `tree.walk` (WP-R3's first step), and decide then, with its size in hand, as ezjson did for JSON-PULL-1. Moving a row to Trusted is a weakening the maintainer approves. Decided: accepted as recommended. -->
- [x] <!-- REVIEW-R6 (resolved): The spike's laws once the rows land. `render_parse_plain_pair` is a partial law of TOML-RT-1 and is subsumed when TOML-RT-1 is proved. Recommend: delete it in that change and keep its lemmas that the full proof reuses (the span count, `kv.*`, `op.*`, `ef.*`), as ez deleted its spike when the planner landed. `key_reads_back` stays: it is the row's own law. Decided: accepted as recommended. -->

## Summary

`render` writes a small part of TOML: no comments, one spacing, bare or basic-quoted keys, only basic one-line strings, decimal integers, keys before tables, and every table as a header. So the round trip is a proof about the scanner on that part only, and it can come before the grammar relation. We plan it as one exact lemma, proved by induction on the document with the rest of the text as a context, from which TOML-RT-1 and most of TOML-RT-2 follow. TOML-RT-3 is the other kind: a Bool invariant over the scanner's state, kept by every step on every text.

The spike proved the riskiest piece against the checker twice over. TOML-KEY-2's read-back holds for every string (not only strings of Unicode scalar values), which proves the row. And a one-pair document with a plain string reads back as itself, which needed the scanner's span and its U32 count, and found that the count wraps (REVIEW-R1). Both proofs checked with few failed runs, and together they are about 1,200 lines. The estimate is about 10,000 to 11,000 lines of proof for TOML-RT-1 (a third of it value lemmas shared with the TOML-NUM and TOML-TIME rows) and 14,000 to 18,000 for the whole plan, with TOML-RT-3 the least certain part.

## What render writes

| |
|:---:|
| <pre>document  = keys(root) tables(root)<br>keys(T)   = for each pair of T that is not a table or an array of tables:<br>              key(name) " = " value "\n"<br>tables(T) = for each table pair of T:        "[" path "]\n" keys(sub) tables(sub)<br>            for each array-of-tables pair:  for each element:<br>                                              "[[" path "]]\n" keys(el) tables(el)<br>value     = key.basic(s) &#124; sign digits &#124; sign spelling &#124; true &#124; false &#124; datetime<br>          &#124; "[" value ", " value ... "]" &#124; "{" key(name) " = " value ", " ... "}"<br>key(s)    = s when bare(s), else key.basic(s)</pre> |
| Caption: the text `render` writes for a well-formed document. `path` is the stored path, which `wf` makes the parent's path, `.`, and `key(name)`. |

What it never writes: comments, blank lines, tabs, carriage returns, literal and multi-line strings, dotted keys, a sign `+`, underscores, hex, octal or binary integers, a lowercase `t` or `z` in a datetime, or a space between a date and a time. So of the scanner's 35 `Lex` states, rendered text visits 26: `LTop`, `LKey`, `LAfter`, `LVal`, `LLine`, the quoted-key states `LKeyQ`, `LKeyE`, `LKeyU`, the string states (the span modes `MOpen` and `MEat`, then `LQ`, `LQ2` for `""`, `LStr`, `LEsc`, `LUni`), `LBare`, the header states `LHead`, `LHeadQ`, `LHeadE`, `LHeadU`, `LHeadGap`, `LHeadDot`, `LHeadR`, and the container states `LArr`, `LArrC`, `LInl`, `LInlK`, `LInlC`. It never visits `LCom`, `LFold`, `LMq`, `LMqEnd`, `LTrim`, `LTrim2`, `LDate`, `LKeyDot`, `LSink` or the `MCr` mode.

## What parse does, as far as this plan needs

| |
|:---:|
| <pre>text ──doc.read──▶ Mode ──(one character at a time)──▶ ... ──read.fin──▶ Doc<br><br>Mode = MScan{st}                       read.fast: fast paths, else read.on (the 35 states)<br>     &#124; MCr{st}                        after a carriage return<br>     &#124; MOpen{...}                     after the opening quote of a one-line string<br>     &#124; MEat{basic, q, cut, n, ...}     inside a span: cut is the text from the string's<br>                                      first character, n its U32 count<br><br>a finished value ──val.take──▶ take.top ──tree.walk(here ++ reverse(parts))──▶ rows</pre> |
| Caption: `parse` is `doc.read(text, MScan{st.start()})`. A finished value is put into the root through a walk of its whole path. |

- **The scanner state.** `St` has fifteen fields: the first error, the root's rows (newest first until `rows.seal` reverses each table at the end), `heads`, the current table's path `here`, the key's segments `parts`, the buffer `buf` (reversed), the state `lex` and the state to go back to `back`, the string kind `qkind`, the stack of open arrays and inline tables, a held character, the `\u` escape's value and digits left, the array-of-tables flag and the byte-order-mark flag. Rendered text leaves `back`, `qkind` and `arrtab` in values that depend on what came before, but on rendered text each is set again before it is next read (`qkind` at each opening quote, `arrtab` at each header's bracket) or never read (`back` is read only after a comment). The spike met this at once: an escape in a quoted key leaves `back` at `LKeyQ` where a plain character leaves it as it was.
- **Two paths.** `read.fast` handles a plain character in a key, a bare value, a comment, whitespace or a string without leaving the fast step; anything else goes through `read.on`, one def per state. A one-line string is a span (`MOpen`, `MEat`) until its first escape or control, which copies the span so far into the buffer (`eat.copy`) and goes on in `LStr`.
- **The tables, as they are at `6fd13cb`.** A key's value is placed by `take.top`, which walks the path `here ++ reverse(parts)` from the root with the job `JPut{val}`; a header walks its segments with `JDef{}` or `JAot{}`. `skip` counts the segments of `here`, which are navigation; the rest are a dotted key's, which define tables. `heads` records each defined table's path behind a mark, `[` for a header and `.` for dotted keys (`heads.by.head`, `heads.by.dot`); `heads.has` asks whether a table was defined at all and `heads.head` whether a header defined it. A dotted key may not add to a table a header defined, nor to an array of tables (`tree.sub.head`, `tree.sub.arr`); a new element of an array of tables forgets every table under it (`heads.drop`). Inside an inline table, dotted keys build `VHead` tables that become `VInl` when the inline table closes (`inl.seal`). Paths are built with `key` (`tree.pre`), which is why `wf` asks that a stored path be the parent's path, `.`, and `key(name)`.

Rendered text touches only part of this: no dotted keys, so no `.` marks and no `inl.seal` work (its input holds no `VHead`); every header defines a table once; `heads.drop` runs on each new element of an array of tables. We state the plan's walk lemmas as contracts of `tree.walk` (WP-W), so that later changes inside `tree.sub.*` touch those proofs and not their statements.

## The shape of the proof

### The invariant

Every lemma is stated in premise form: it holds from every scanner state of a given shape, whatever came before, and it never replays the text before. A shape is a law-side constructor of `St` or `Mode` with the fields that matter as parameters, as the spike's `kq(back, buf)` (a scanner inside a quoted key), `ky(buf)` (inside a bare key), `vo(name)` and `ve(cut, n, name)` (the span of a root key's string).

The fields a text does not decide are the difficulty. `kq` leaves `back` free, and after a character it is either what it was or `LKeyQ`, depending on the character. Naming that as a function of the character would tie each lemma to the dispatch. The spike instead takes the rest of the walk as a function of those fields:

```
def kq.Goal(uu, back, buf, rest, goal) -> Type:
  (@bk: T.Lex -> {T.doc.read(rest, T.MScan{kq(bk, Chr{uu} <> buf)}) == goal : T.Doc}) ->
    {T.doc.read(String.append(Laws.esc(Chr{uu}), rest), T.MScan{kq(back, buf)}) == goal : T.Doc}
```

A step that ends with `back` unchanged answers `ih => ih(back)`, one that ends at `LKeyQ` answers `ih => ih(T.LKeyQ{})`, and the induction over the string passes `bk => kq.body(tt, bk, Chr{uu} <> buf)` as the function. The checker accepted this form without complaint. For the document we plan the same with one record of the free fields (`back`, `qkind`, `arrtab`), so each lemma reads "from the line-start state of table `P` with rows `R` and heads `H`, and any free fields, the text of this pair then `rest` is `rest` from the line-start state with the pair put in, and some free fields".

The rows are the part with content. Since every insertion walks from the root, the line-start state of table `P` holds the whole root, newest first, and a pair's lemma says its rows after are `tree.walk` of its rows before. WP-W turns that into a statement about the document: on rows where the tables along `P` exist and hold no pair of the name, the walk puts the pair at the head of the table at `P`. The document induction then keeps `R` equal to a law-side `ins` of the pairs read so far, and at the end `rows.seal(ins(...))` is `canon(d)` (REVIEW-R2).

TOML-RT-3 is about every text, so it takes shake's form instead (REVIEW-R3): a Bool `good(st)` (the rows are well-formed newest first, every open frame's cells are well-formed, the key segments and the buffer hold scalar values, `heads` records the defined tables), one lemma per arm that each step keeps it, composed along the dispatch as the spike's helpers are, and read at the end through `rows.seal` and `read.fin`. A Bool invariant copies and splits with the `and` lemmas of `src/eq.bend`; a Pi-typed one does neither.

### How the arms are proved

The scanner names its tests as Bool parameters, so each lemma for an arm is a helper that takes the same Bools and a fact for each, matches them, and refutes the branches the facts rule out. The spike's `kq.q`, `kq.go`, `kq.char`, `op.q`, `op.bs`, `op.ok`, `ef.q`, `ef.bs` and `ef.ctl` are all this one pattern, five to twenty lines each. Where the characters are fixed the checker computes: the 33 controls, taken one at a time as `esc_ctl` takes them, each read back as a `\u` escape by `{==}`, and so do `" = 1"` and the closing quote and newline, with the buffer and the key's name left symbolic.

### How same and wf enter

`wf` enters TOML-RT-1 only as the premise that makes `render`'s text the language above: tables only as a pair's value, paths that are the key-join, distinct keys, canonical integers, floats and datetimes, scalar values in strings and keys, and no empty array of tables. Each lemma that needs one of these takes it as a Bool premise read off `wf.go` with the `and` lemmas. `same` enters only at the end (REVIEW-R2): `same(canon(d), d)` holds for well-formed `d`, by `same_refl`'s `refl.rows` and the `pick` lemmas of `same_swap` for the reordering, and `own.l` and `own.r` (a span and its characters compare alike) take `own` off the parsed side. The spike's `rp.same` is this step for one pair.

### What it reuses

| Existing law or lemma | Used for |
| :---- | :---- |
| `fail_stays`, `err.sinks`, the `sk.*` lemmas | nothing in TOML-RT-1 (rendered text never fails); the refusals of TOML-KEY-3 and TOML-TEXT-2, and the "stays failed" half of TOML-RT-3's end |
| `key.first`, `key.body`, `ball.head`, `ball.tail`, `rev.full`, `ml.rev` (from `empty_basic_at_end`) | every bare key; the spike's `kq.bare` and `kv.key` |
| `scan.other`, `or2.no`, `Eq.refute_char` | leaving a `doc.scan` branch a character cannot take |
| TOML-STR-2's `basic_escs`, `esc_plain`, `cls.plain`, `ctl.off`, `ctl.lt`, `ctl.at`, `ctl5`, `neq.off`, `render_string`, `pass_string`, `inline_string`, `array_string` | the text `render` writes for a string, and the facts about a character that decide how it is read back; reading back `key.basic(s)` as `s` is the core of TOML-KEY-2 and of every string in TOML-RT-1 |
| `span_quote_basic` | TOML-RT-2: a parsed span renders as its characters do |
| `same_refl`'s `refl.rows`, `pair.self.tt`, `own.l`, `own.r`, `pick.same`, `pick.skip`, `pick.swap` | `same(canon(d), d)` |
| `Eq.u32_eq`, `Eq.u32_dec_nat`, `Eq.append_assoc`, `Eq.append_nil`, the `and`, `or` and `not` lemmas | throughout |
| the table fixes' laws (`dotted_key_enters_other_table`, `header_enters_any_table`, `header_records_new_table`, `new_element_forgets_tables_under_it`, and the rest) | WP-W's walk contracts are the positive side of the same steps |

## Per requirement

### TOML-KEY-2 (proved by the spike)

```
# LAW: a key reads back as its name: for every string s, key(s) followed by
# " = 1" parses with no error to one pair, named s, holding the integer 1
# TOML-KEY-2
law key_reads_back:
  for +s: String
  {T.parse(String.append(T.key(s), " = 1"))
    == T.Doc{"", [T.VPair{s, T.VInt{T.Plus{}, "1"}}]} : T.Doc}
```

With `key_is_bare_when_it_can` and `key_is_quoted_when_it_must` it proves the row, which SPEC.md now marks proved. It holds for every string: a quoted key keeps any character that is no control, quote or backslash, and those three are escaped. Size: 512 lines of proof, 10 of law.

### TOML-RT-1

```
# LAW: render then parse is the same document
# TOML-RT-1
law render_parse:
  for +d: T.Doc
  for w: {T.wf(d) == True{} : Bool}
  for h_s: {short(T.render(d)) == True{} : Bool}
  {Bool.and(String.is_empty(T.bad(T.parse(T.render(d)))), same(T.parse(T.render(d)), d))
    == True{} : Bool}
```

The bound `h_s` is REVIEW-R1's recommendation; `short` is the spike's, a U32 counting the characters from 0 without wrapping. The proof is the exact lemma `own(parse(render(d))) == canon(d)` (REVIEW-R2) by induction on the document (REVIEW-R3), built from WP-S, WP-N, WP-C, WP-H and WP-W, then `same(canon(d), d)`. Reuse: everything in the table above. Effort: large. About 2,000 lines for the document induction and `canon` (WP-D), and about 10,000 to 11,000 lines with the packages it needs, of which WP-N's 3,000 to 4,000 are shared with TOML-NUM-1, TOML-NUM-2 and TOML-TIME-1.

### TOML-RT-3

```
# LAW: every document parse returns with no error is well-formed
# TOML-RT-3
law parse_wf:
  for +t: String
  for h_u: {scalars(t) == True{} : Bool}
  for h_s: {short(t) == True{} : Bool}
  for ok: {String.is_empty(T.bad(T.parse(t))) == True{} : Bool}
  {T.wf(T.parse(t)) == True{} : Bool}
```

`scalars` is a law-side check that every character is a Unicode scalar value. The proof is the Bool invariant `good(st)` of "The invariant", kept by every arm of `read.fast`, `read.on` and the span modes, plus value lemmas that each finished value is well-formed: `dec.text` of decimal digits has no leading zero and `i64.fits` agrees with `wf.int`'s range, a float's `word.body` matches `wf.flo`'s grammar, a datetime's fields are in `wf.when`'s ranges, and a `\u` escape gives a scalar value (`uni.ok`). The value lemmas are shared with TOML-NUM-1, TOML-NUM-2 and TOML-TIME-1. Effort: large, and the least certain: about 3,000 to 5,000 lines, since the invariant needs a lemma for every dispatch def, including all those rendered text never reaches (comments, multi-line strings, dotted keys, errors). REVIEW-R5 starts it with a spike.

### TOML-RT-2

```
# LAW: a parsed document renders, reparses and renders again unchanged
# TOML-RT-2
law parse_render_parse:
  for +t: String
  for h_u: {scalars(t) == True{} : Bool}
  for h_s: {short(t) == True{} : Bool}
  for h_r: {short(T.render(T.parse(t))) == True{} : Bool}
  for ok: {String.is_empty(T.bad(T.parse(t))) == True{} : Bool}
  {Bool.and(same(T.parse(T.render(T.parse(t))), T.parse(t)),
    String.eq(T.render(T.parse(T.render(T.parse(t)))), T.render(T.parse(t)))) == True{} : Bool}
```

Two bounds, because `render(parse(t))` can be much longer than `t`: a dotted key of n segments renders n headers, each with the path so far. The first half is TOML-RT-1 at `d = parse(t)`, with TOML-RT-3 for `wf`. The second is the exact lemma: `render(parse(render(d)))` is `render(canon(d))` because `render` reads a span as its characters (`span_quote_basic`), and `render(canon(d))` is `render(d)` because `render` already writes each table's non-table pairs first. Effort: small once TOML-RT-1 and TOML-RT-3 land, about 300 lines.

### TOML-KEY-3 and TOML-TEXT-2

TOML-KEY-3 generalizes the spike's quoted-key family from `esc(c)` to any spelling: a basic key is a list of pieces (a raw character, a two-character escape, a `\u` or `\U` escape), as ezjson's JSON-STR-4 spells a member name, and a literal key is its raw characters. Reading the pieces from `kq` pushes the characters they stand for; the same lemmas with `LHeadQ` read header segments, and with `LKeyDot` and `LAfter` dotted keys. `get` then finds the pair by TOML-GET-1's laws. Effort: medium, about 1,200 lines, after WP0 and WP-W.

TOML-TEXT-2 reuses WP-W's contracts as the positive direction of each definition rule, beside the refusals the fixes proved. Its hard part, that the walk's steps compose to `parse` on every text, is TOML-RT-3's invariant with `heads` given its meaning, so it follows WP-R3 rather than this plan.

## The spike

We proved two laws against the real checker, in LAWS.bend and PROOF.bend, inside the gate:

- **`key_reads_back`** (tagged TOML-KEY-2, now proving the row). The quoted case reads `key.basic(s)` one character of `escs(s)` at a time in `LKeyQ`: the per-character lemma splits on the quote, the backslash, the controls (below U+0020 bit by bit, as `esc_ctl` does, and U+007F) and the rest, and each case is either computed or goes through the fast-step helpers. The bare case reuses `empty_basic_at_end`'s lemmas. 512 lines of proof. About an hour of work; it checked on the first run.
- **`render_parse_plain_pair`** (tagged TOML-RT-1, partial). A document of one pair, a bare key and a string with no character `render` escapes and fewer than 2^32 characters, renders and reads back with no error and `same` as itself. The string opens a span on its first character (`op.*`), each later character adds one to the span's count (`ef.*`), and the closing quote and newline store `VSpan{cut, n}` by computation. The span reads as the string because `n` is its length: that took a word lemma (one taken from one more than a U32 is the U32, `inc.dec` and `sub.inc`), a count that does not wrap counting the characters (`cnt`), and `span.str` as a `take` (after ezjson's `span_take`). `same` then comes from `own.l`, `own.r` and `pair.self.tt`. 665 lines of proof, 43 of law. About ninety minutes; two failed runs, a missing parenthesis and a missing `+`.

Each proof fails when replaced by `{==}`. Planted wrong answers fail it too: a control's case answering the wrong `back`, a word lemma with one carry wrong, a tab escape decoded as a newline and a plain key character pushed as U+0000 in `main.bend` (both fail `key_reads_back`'s lemmas), and the span's count starting at 0 or growing by 2 in `main.bend` (both fail `render_parse_plain_pair`'s). No change to `main.bend` was needed or made.

The gate went from 3.5 s to 5.7 s. The 33 control cases, each running the scanner on six characters, are the likely cost of most of that; we did not profile it.

What this implies:

- **The scanner is provable as it is.** Its Bool-parameter dispatch turned every arm into a short helper, and runs of fixed characters closed by computation even with a symbolic buffer, name and rest. We expect about 400 to 600 lines per family of states read on rendered text, which is where most of the estimates below come from.
- **The continuation over free fields works.** It is the invariant we plan for the whole document.
- **Counters need arithmetic, and it ports.** The U32 lemmas were about 250 lines. ezjson has the rest of what integers need (U32 multiply and divide by ten, from JSON-TREE-6), so WP-N is porting, not research.
- **Wording can be wrong in ways only a proof finds.** The 2^32 wrap is REVIEW-R1. We expect the float and datetime read-backs to test `wf.flo` and `wf.when` against the scanner in the same way.
- **The gate will grow.** Concrete evaluation is cheap to write and costs checker time. A full TOML-RT-1 at this rate might add 30 to 60 seconds. REVIEW-R5's decision should look at that too; the fixes are fewer concrete cases (a symbolic hex lemma for `\u00XX`) and lemma modules that `ez prove` checks in parallel.

## Work packages

| |
|:---:|
| <pre>WP0 ──┬──▶ WP-S ──▶ WP-C ◀── WP-N<br>      ├──▶ WP-H<br>      └──▶ WP-K3 (TOML-KEY-3), also after WP-H and WP-W<br><br>WP-S, WP-N, WP-C, WP-H, WP-W ──▶ WP-D ──▶ TOML-RT-1 ──┐<br>WP-N, WP-W ──▶ WP-R3 ──▶ TOML-RT-3 ───────────────────┴──▶ WP-R2 ──▶ TOML-RT-2</pre> |
| Caption: the work packages. WP0, WP-N and WP-W can start at once, and WP-R3's spike as soon as WP-W has its statements. |

| WP | Scope | Needs | Effort |
| :---- | :---- | :---- | :---- |
| WP0 | the quoted-key family generalized over the states it returns to (`LKeyQ` and `LHeadQ`); the control enumeration over a motive instead of copied per goal; `inc.dec`, `sub.inc`, `inc.nat` moved to `src/eq.bend` | none | small, 300 lines |
| WP-S | a rendered string read back in any value position (a root pair, an array item, an inline table's pair): the span, the span copied at its first escape (`eat.copy`, `span.rev`), and a string that starts with an escape; the `LStr`, `LEsc`, `LUni` family with `back` at `LStr`; `""` through `LQ2` | WP0 | medium, 1,000 to 1,500 lines |
| WP-N | integers, floats, booleans and datetimes read back: `dec.text` over decimal digits (U32 multiply and divide by ten, ported from ezjson), `i64.fits` against `wf.int`, the numeral scan over `wf.flo`'s spellings, `when.read` over `when.text`; shared with TOML-NUM-1, TOML-NUM-2 and TOML-TIME-1 | none | large, 3,000 to 4,000 lines |
| WP-W | contracts of `tree.walk`: a `JPut` along existing tables to an absent name puts the pair at the head of that table; a `JDef` of a new path defines it and records it in `heads`; a `JAot` starts or extends an array of tables and forgets the tables under it; `rows.seal` reverses each table | the table fixes (landed) | medium, 1,200 lines |
| WP-C | arrays and inline tables: the frames `CArr` and `CInl`, `LArr`, `LArrC`, `LInl`, `LInlK`, `LInlC`, `", "` and the closers, by induction on the value and its shape together as ezjson's `pv` | WP-S, WP-N, WP-W | medium, 1,200 lines |
| WP-H | headers: `[path]` and `[[path]]` with bare and quoted segments, `LHead`, `LHeadGap`, `LHeadDot`, `LHeadR`, `head.fin`, `head.on` | WP0, WP-W | medium, 1,000 lines |
| WP-D | the document induction: the key pass then the table pass, the line-start state, `ins` and `canon`, the exact lemma, `same(canon(d), d)`; TOML-RT-1 | WP-S, WP-N, WP-C, WP-H, WP-W | large, 2,000 lines |
| WP-R3 | TOML-RT-3: a spike of `good(st)` over the header states and `tree.walk`, then every arm | WP-N, WP-W | large, 3,000 to 5,000 lines |
| WP-R2 | TOML-RT-2 from the exact lemma, `span_quote_basic` and TOML-RT-3 | WP-D, WP-R3 | small, 300 lines |
| WP-K3 | TOML-KEY-3: pieces, literal keys, dotted and header segments, `get` | WP0, WP-W, WP-H | medium, 1,200 lines |

## Risks

- **TOML-RT-3's cost.** It is the one row whose invariant runs over every state and every text, including all the states rendered text never visits. REVIEW-R5's spike measures it before WP-R3 commits.
- **The walk moves again.** The table code changed in the fixes that landed while this was written, and TOML-TEXT-2 will change it again. WP-W's statements are about `tree.walk`'s results, not its frames, so a change inside it reproves WP-W and leaves WP-D alone.
- **`wf` and the scanner disagree.** The spike found one disagreement between a row and the code (the U32 count). WP-N compares `wf.int`, `wf.flo` and `wf.when` with what the numeral and datetime scans accept and produce, and a disagreement there means a row, `wf`, or the code changes. Each would be a decision with its own REVIEW item.
- **Gate time.** 5.7 s now. The plan could take it past a minute (see the spike). Keep the time in each PR description, and prefer symbolic lemmas to concrete enumeration where both work.
- **Proof size.** 14,000 to 18,000 lines on top of PROOF.bend's 6,800. ezjson's PROOF.bend is 51,000 lines for a smaller language, so this is within what the toolchain handles, but it is a lot of text to keep in one file. Moving Base-only lemmas to `src/eq.bend` (WP0) is the start.
