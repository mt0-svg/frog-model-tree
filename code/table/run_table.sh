#!/usr/bin/env bash
# The table from the iterates H14.txt and H15.txt of run_iterates.sh: the law H15 + 30 (H15 - H14), its rows rounded
# to multiples of 2^-28, written to out/table.v3 (and its atoms to out/table.v2); then out/table.v3 against
# ../certificate/table.cert. Output: out/table.out.
set -euo pipefail
cd "$(dirname "$0")"
cargo build --release -q
mkdir -p out
rm -f out/table.v3 out/table.v2
target/release/table write H15.txt H14.txt 30 out/table > out/table.out
{
  sha256sum out/table.v3 ../certificate/table.cert
  if cmp -s out/table.v3 ../certificate/table.cert; then echo "out/table.v3 equals ../certificate/table.cert"; else echo "out/table.v3 differs from ../certificate/table.cert"; fi
} >> out/table.out
cat out/table.out
