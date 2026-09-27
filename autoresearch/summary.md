# eztoml other hot paths

Baseline is `9c6e64e` (parser identical to `db8dff3`), Bend 2.0.29, native
`bend bench/main.bend -o` with `CC=clang`. One kept change. The 28 kB mixed
document dropped from 10.31 ms/op to 9.36 ms/op.

## Metric

`sh autoresearch/verify.sh autoresearch/doc/mix28k.toml 128` archives `HEAD`
without `autoresearch/`, builds `bench/main.bend`, and prints
`MS <ms> SUM <u32> N <n> BYTES <n>`. The document is 27913 bytes.
The timed loop is `parse` plus `text.len(render(doc))`. Per-op time is
`MS / N`. `IO.now` resolves 1 ms; N=32 jittered by tens of milliseconds on
this host, so the recorded runs use N=128.

| build | N | MS | ms/op | SUM |
| :-- | --: | --: | --: | --: |
| baseline `9c6e64e` | 128 | 1320 | 10.31 | 3552640 |
| keep, key text is a thunk | 128 | 1198 | 9.36 | 3552640 |

`parse` on the same file: `OK SUM 2834622309 BYTES 27755`, before and after.
`bend PROOF.bend` prints `All terms check.`

Stages, same host, before the keep (in-place binary, N=128):

| stage | MS | ms/op |
| :-- | --: | --: |
| parse only (node walk, no render) | ~740 | ~5.8 |
| render only | 526 | 4.11 |
| parse + render | 1305 | 10.20 |

After the keep, render only was 393 ms (3.07 ms/op) and parse + render 1185 ms.
The official archive number is the table above.

Same-sized shapes, parse only, before the keep:

| doc | what it is | ms/op |
| :-- | :-- | --: |
| comments28k | comment lines | 1.2 |
| strings28k | plain strings in one small table | 1.0 |
| mix28k | the mixed document | 5.8 |
| tiny28k | thousands of sibling tables | 224 |
| ints28k | one flat table of integers | 305 |

Comment and string characters are cheap. The mixed document's extra parse
time is the table walk, not the string span. `tree.walk` returning the
table unchanged dropped parse-only from ~740 ms to 254 ms, so about 3.8
ms/op of parse is the walk. Flat and sibling-table documents are still
quadratic; that shape was measured on `autoresearch/eztoml-parse-perf` and
was not retried.

## Kept

`render.pass` walks every table twice, once for keys and once for tables.
The tables pass took each key's text (`key`, `render.atom`, `render.go` of
arrays and inline tables) as a strict argument and then dropped it. The
text is now a function, forced only when that pass writes keys.
`render.late` is that choice. `r2.sp.v` in `PROOF.bend` states it. No
tagged law statement changed, and `SPEC.md` did not change.

| | before | after |
| :-- | --: | --: |
| bench-parse, verify.sh, N=128 | 1320 ms, 10.31 ms/op | 1198 ms, 9.36 ms/op |
| render only, N=128 | 526 ms, 4.11 ms/op | 393 ms, 3.07 ms/op |

## Discarded

| try | what | result | why it is not a keep |
| :-- | :-- | :-- | :-- |
| 2 | One scan for `:`, `-`, and `e`/`E` before a bare word is routed | 9.14 ms/op vs 9.36. Checksum matched | About 0.2 ms/op. `word.num` itself, replaced by a constant, did not move the metric, so the pre-scan was the only piece and it is too small for the proofs that unfold `word.colon`. |
| 3 | `word.num` returns a constant integer | 9.31 ms/op, checksum changed | The numeral parser is not the time on this document. |
| 4 | `tree.walk` returns the table unchanged | parse-only 254 ms vs ~740 | The walk is the remaining parse time. Keeping a real speedup there means restating the table laws. Not done in this loop. |
| 5 | `heads.has` / `heads.head` stop at the first hit | 9.28 ms/op vs 9.36. Checksum matched | Inside noise. Newest paths sit at the front, but this document does not spend its time there. |

Rows are `iteration timestamp commit metric delta guard status description`
in `results.tsv`. Metric is ms/op on `mix28k.toml` from `verify.sh` when the
guard ran, and from an in-place `bench-parse` for discards.

## What still blocks the flat-table miss

A new key is a miss, and `rows.find` already stops on a hit. Skipping the
miss needs a complete index stored on the table. `walk_put_at_head`,
`header_defines_new_table`, and `aot_header_starts_array` say the list a
later key sees is `VPair <>` the old rows. `seal_puts_newest_last` says
`rows.seal` keeps that head. `St` is matched as written, so it cannot grow
a field either. That is the same block as `autoresearch/eztoml-parse-perf`.
On this document it is still about 3.8 ms/op of parse, and on a flat table
it is the whole quadratic.

A faster miss that is still `get` for every list has to live inside
`rows.find` / `get`. The closure-free loop tried on the other branch was
about 10% on a flat 38 kB file, invisible on this mixed document, and it
is `@unsafe`.

## Reproduce

```sh
export PATH="$HOME/.bend/bin:$PATH" BEND_NO_TELEMETRY=1 CC=clang
bend PROOF.bend          # first line: All terms check.
sh autoresearch/verify.sh autoresearch/doc/mix28k.toml 128
```
