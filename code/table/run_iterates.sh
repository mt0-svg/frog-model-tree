#!/usr/bin/env bash
# The iterates H14.txt and H15.txt from H13.txt: two steps of the iteration of the program (src/main.rs). Writes
# out/iterate.txt.1 and out/iterate.txt.2, then compares them with H14.txt and H15.txt. Output: out/iterates.out.
set -euo pipefail
cd "$(dirname "$0")"
cargo build --release -q
mkdir -p out
rm -f out/iterate.txt*
target/release/table iterate H13.txt 2 out/iterate.txt > out/iterates.out
{
  for p in "1 H14.txt" "2 H15.txt"; do
    set -- $p
    if cmp -s "out/iterate.txt.$1" "$2"; then echo "out/iterate.txt.$1 equals $2"; else echo "out/iterate.txt.$1 differs from $2"; fi
  done
} >> out/iterates.out
tail -n 2 out/iterates.out
