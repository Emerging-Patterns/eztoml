# eztoml parse perf

Baseline is `db8dff3` (`feat(laws): WP-R chunk 1`), Bend 2.0.29, native
`bend bench/main.bend -o bench.bin` with `CC=clang`. No kept change.
The ~23k document did not get faster under a version that still agrees
with the laws.

## Metric

`bench.bin bench-parse autoresearch/doc/mix28k.toml N` prints
`MS <ms> SUM <u32> N <n> BYTES <n>`. The document is 27913 bytes
(app config, 80 `[[servers]]` with tls, dependency tables, jobs).
The timed loop is `parse` plus `text.len(render(doc))`. Per-op time is
`MS / N`. `IO.now` resolves 1 ms, so N is large enough that MS is not 0.

| build | N | MS | ms/op | SUM |
| :-- | --: | --: | --: | --: |
| tip | 16 | 147 | 9.19 | 444080 |

`parse` on the same file: `OK SUM 2834622309 BYTES 27755`.
`bend PROOF.bend` prints `All terms check.`

Shapes, same binary, to show where the time goes:

| doc | bytes | ms/op |
| :-- | --: | --: |
| flat400 / 800 / 1600 / 3200 (`kNNNN = "v"`) | 4800 … 38400 | 10.9 / 42 / 161 / 601 |
| nest200 / 400 / 800 (`[tNNNN]` plus two keys) | 4000 … 23780 | ~4 / ~16 / 112.5 |
| dot800 (`root.kNNNN.leaf = i`) | 17490 | 128.5 |
| mix28 render only | 27913 | 4.4 |
| nest800 render only | 23780 | 2.5 |

Flat and dotted documents are quadratic in the number of keys in one
table. `rows.find` / `rows.look` walk the whole table on a miss, and a
new key is a miss. Nested headers pay that scan plus `rows.repl`, which
rebuilds the parent around the one pair that changed.

## Kept

None.

## Discarded

| try | what | result | why it is not a keep |
| :-- | :-- | :-- | :-- |
| 1 | `VIx` map of pair names in front of the rows. A miss does not scan; a hit still calls `get`. `rows.seal` would drop the map. | flat1600 ~7 ms vs 157. nest800 ~76 vs 115. mix28 ~11 vs 9.2. Checksums matched. | `walk_put_at_head` says a new pair is `VPair <> rows`. A map consed in front is not that list. `seal_puts_newest_last` says `rows.seal(x <> rows)` keeps `x`. Dropping `VIx` makes that false; keeping it changes the rendered document. |
| 2 | `rows.repl` returns the original suffix when the rest of the walk changes nothing. | nest800 135 ms vs 112. mix28 unchanged. Checksums matched. | The walk still reads every row, and the extra dup costs more than the conses it saves. |
| 3 | `rows.repl` stops at the first hit and shares the tail. | nest800 48 ms vs 112. mix28 7.9. Checksums matched on these files. | Later pairs of the same name keep the old value. `rows.repl` today replaces every pair. The header laws describe the walk as that function. |
| 4 | Search the two halves of a long table in parallel. | flat3200 714 ms vs 601. mix28 10.9. | Slower. `@unsafe`, so the checker no longer opens with a bare `All terms check.` |
| 5 | `rows.find` calls the next row directly, no closure. | flat3200 539 ms vs 601. mix28 9.44 vs 9.13. Duplicates of an old key and of the newest key are still `BAD duplicate key`. | The ~23k document did not drop. The direct call is mutual recursion, which Bend only allows as `@unsafe`. That fails the proof gate. |
| 6 | Same direct call for `rows.look`, and `heads.or` runs the tail only on a miss. | dot800 160 ms vs 128. nest800 108 vs 112. | A miss still scans, and now also builds a thunk. Dotted keys miss. |
| 7 | Direct `rows.find` with a length fuel, so the checker accepts the recursion. | flat3200 297 ms vs 601. | Each row spent two units of fuel, then the rest returned `Miss`. A file of 200 keys plus a second `k0000` parsed `OK`. The tip parses it `BAD duplicate key`. |

Rows are `iteration timestamp commit metric delta guard status description`
in `results.tsv`. Metric is ms/op on `mix28k.toml`.

## What blocks more

The quadratic scan is the time, and the laws pin its result.

- A new key is a miss. An early exit helps only a hit. `rows.find` already
  stops on a hit, through the thunk in `find.step`.
- A sound index (hit means the scan would hit, miss still scans) does not
  speed inserts. The miss is the common case. Skipping the miss needs the
  index to be complete, so it has to be stored on the table.
- The table the next key sees is `End.vs` from `tree.walk`. `walk_put_at_head`,
  `header_defines_new_table` and `aot_header_starts_array` say that list is
  `VPair <>` the old rows, not a pair plus a map. `St` cannot grow a field
  either: the laws match `T.St{...}` as written.
- `rows.repl` is hot when a nested update rewrites a large parent
  (nest800 112 ms, and stopping after the first hit drops it to 48 ms).
  Sharing the tail only when every later pair was checked is slower than
  rebuilding (try 2). Sharing without that check is a different function
  (try 3).

A faster miss that is still `get` for every list has to live inside
`rows.find` / `get` and return the same `Hit`. The closure-free loop is
about 10% on a flat 38 kB file, invisible on the 28 kB mixed document,
and it is `@unsafe`. Bend's termination check rejects the safe spelling:
the call that continues after a failed compare is not, by itself, a
smaller piece of the list. A length fuel makes the check accept it and
is easy to get wrong (try 7).

## Reproduce

```sh
export PATH="$HOME/.bend/bin:$PATH" BEND_NO_TELEMETRY=1 CC=clang
bend PROOF.bend          # first line: All terms check.
sh autoresearch/verify.sh autoresearch/doc/mix28k.toml 32
```

`verify.sh` archives `HEAD` without `autoresearch/`, builds
`bench/main.bend` natively, and prints the `MS` line.
