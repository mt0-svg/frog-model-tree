#!/bin/bash
# Writes the Lean modules of the stored M1 run, FrogModel/D3/M1Data/ in the package (H0 to H9, the stored laws of the
# heights 0 to 99; Top, the top rows and the masses; Data, the list of the heights; C0 to C9 and CTop, their kernel
# checks; All), from the run and its mass file, and compares their sha256 with modules.sha256. The run is the release
# asset frog-model-tree-d3-m1run.txt.xz (ASSETS.md), compressed or not; the mass file is masses100.txt of the
# certificate asset frog-model-tree-d3-certificate.tar.zst, unpacked. Usage: code/m1gen/gen.sh RUN MASS [OUT]; OUT
# (default code/m1gen/out) receives the output of m1gen (gen.out) and the sha256 of the modules written (modules.out).
# Exit 0 when the inputs and the modules match modules.sha256.
set -eu
here=$(cd "$(dirname "$0")" && pwd); root=$(cd "$here/../.." && pwd)
run=${1:?usage: gen.sh RUN MASS [OUT]}; mass=${2:?usage: gen.sh RUN MASS [OUT]}
out=${3:-$here/out}; mkdir -p "$out"; out=$(cd "$out" && pwd)
w=$(mktemp -d); trap 'rm -rf "$w"' EXIT
case $run in *.xz) xz -dc "$run" > "$w/run.txt" ;; *) cp "$run" "$w/run.txt" ;; esac
want() { awk -v n="$1" '$2 == n { print $1 }' "$here/modules.sha256"; }
[ "$(sha256sum < "$w/run.txt" | cut -c1-64)" = "$(want m1run_V48_P96_h100.txt)" ] || { echo "the run is not the one of modules.sha256"; exit 1; }
[ "$(sha256sum < "$mass" | cut -c1-64)" = "$(want mass_V48_h100.txt)" ] || { echo "the mass file is not the one of modules.sha256"; exit 1; }
(cd "$here" && lake build m1gen)
rm -rf "$root/FrogModel/D3/M1Data"
"$here/.lake/build/bin/m1gen" "$w/run.txt" "$mass" "$root" > "$out/gen.out"
(cd "$root" && sha256sum FrogModel/D3/M1Data/*.lean | sort -k2 -V) > "$out/modules.out"
if grep -E '^[0-9a-f]{64}  FrogModel/D3/M1Data/' "$here/modules.sha256" | sort -k2 -V | diff - "$out/modules.out"; then
  echo "$(wc -l < "$out/modules.out") modules written, every sha256 equal to modules.sha256"
else
  echo "the modules written differ from modules.sha256"; exit 1
fi
