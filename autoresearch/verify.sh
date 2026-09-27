#!/bin/sh
# Time one native parse of the tracked document. Build from a git archive
# with this directory left out, so the number is the library, not the log.
set -eu
cd "$(dirname "$0")/.."
doc="${1:-$(pwd)/autoresearch/doc/mix28k.toml}"
n="${2:-128}"
scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT
git archive HEAD -- . ':(exclude)autoresearch' | tar -x -C "$scratch"
export PATH="${HOME}/.bend/bin:${PATH}"
export BEND_NO_TELEMETRY=1
export CC="${CC:-clang}"
bend "$scratch/bench/main.bend" -o "$scratch/bench.bin"
"$scratch/bench.bin" bench-parse "$doc" "$n"
