#!/bin/bash
# Writes the Lean modules of the data of the certificate, FrogModel/G3Q/Cand/ in the package (145 data modules,
# Data.lean, 61 theorem modules with 303 theorems, All.lean), from the table and the certificate, and compares their
# sha256 with modules.sha256. The certificate is the release asset frog-model-tree-certificate.v4.zst (ASSETS.md),
# uncompressed. Usage: code/g3k/gen.sh CERTIFICATE [OUT]; OUT (default code/g3k/out) receives the output of g3k
# (gen.out) and the sha256 of the modules written (modules.out). Exit 0 when they match modules.sha256.
set -eu
here=$(cd "$(dirname "$0")" && pwd); root=$(cd "$here/../.." && pwd)
cert=$(cd "$(dirname "${1:?usage: gen.sh CERTIFICATE [OUT]}")" && pwd)/$(basename "$1")
out=${2:-$here/out}; mkdir -p "$out"; out=$(cd "$out" && pwd)
table=$root/code/certificate/table.cert
grep -E '^[0-9a-f]{64}  ' "$here/modules.sha256" | awk '$2 == "certificate" { print $1 "  -" }' > "$out/cert.sha256"
grep -E '^[0-9a-f]{64}  ' "$here/modules.sha256" | awk '$2 == "table" { print $1 "  -" }' > "$out/table.sha256"
sha256sum - < "$cert" | diff - "$out/cert.sha256" > /dev/null || { echo "the certificate is not the one of modules.sha256"; exit 1; }
sha256sum - < "$table" | diff - "$out/table.sha256" > /dev/null || { echo "the table is not the one of modules.sha256"; exit 1; }
(cd "$here" && lake build g3k)
rm -rf "$root/FrogModel/G3Q/Cand"
"$here/.lake/build/bin/g3k" "$table" "$cert" "$root" Cand > "$out/gen.out"
(cd "$root" && sha256sum FrogModel/G3Q/Cand/*.lean | sort -k2 -V) > "$out/modules.out"
if grep -E '^[0-9a-f]{64}  FrogModel/G3Q/' "$here/modules.sha256" | diff - "$out/modules.out"; then
  echo "$(wc -l < "$out/modules.out") modules written, every sha256 equal to modules.sha256"
else
  echo "the modules written differ from modules.sha256"; exit 1
fi
