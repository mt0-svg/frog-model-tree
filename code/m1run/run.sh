#!/usr/bin/env bash
# The stored run of the lower model M1 (Section 15 of the paper; the release asset frog-model-tree-d3-m1run.txt.xz,
# unpacked) and the masses at height 100 (masses100.txt of the asset frog-model-tree-d3-certificate.tar.zst): m1run
# with (V, P) = (48, 96), W = 62, the heights 0 to 99 and the top rows at height 100 (q = 2 to 33), written to
# out/m1run_V48_P96_h100.txt and out/mass_V48_h100.txt (formats: src/bin/m1run.rs); then their sha256 against the two
# input lines of ../m1gen/modules.sha256, the files that code/m1gen reads. Output: out/run.out. Exit 0 when both equal.
set -euo pipefail
cd "$(dirname "$0")"
cargo build --release -q --locked
mkdir -p out
rm -f out/m1run_V48_P96_h100.txt out/mass_V48_h100.txt
trap 'cat out/run.out' EXIT
# Its output less the times it prints: out/run.out holds nothing that depends on the machine.
target/release/m1run 48 96 62 100 33 out/m1run_V48_P96_h100.txt out/mass_V48_h100.txt |
  sed -E 's/ t [0-9]+\.[0-9]+$//; /^# total [0-9.]+ s$/d' > out/run.out
{
  (cd out && sha256sum m1run_V48_P96_h100.txt mass_V48_h100.txt)
  if (cd out && grep -E '^[0-9a-f]{64}  (m1run_V48_P96_h100|mass_V48_h100)\.txt$' ../../m1gen/modules.sha256 | sha256sum -c --quiet) &&
    [ "$(grep -cE '^[0-9a-f]{64}  (m1run_V48_P96_h100|mass_V48_h100)\.txt$' ../m1gen/modules.sha256)" = 2 ]; then
    echo "the run and the masses equal the inputs of ../m1gen/modules.sha256"
  else
    echo "the run or the masses differ from the inputs of ../m1gen/modules.sha256"; st=1
  fi
} >> out/run.out 2>&1
exit "${st:-0}"
