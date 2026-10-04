#!/bin/bash
# Writes the Lean modules of the certificate (Proposition 15.1 (2) of the paper), FrogModel/D3/CertData/ in the Lean package (../..; one module per stored
# state, one per line of the certificate with its kernel checks, the seed, the extension, the comparisons of the CHECK
# state, the segments of the chain and Main.lean), from the certificate, and compares their sha256 with modules.sha256.
# The certificate is the directory of the release asset (manifest.txt and the D3CERT files it names), unpacked.
# Usage: gen.sh CERTDIR [OUT]; OUT (default out/ next to this script) receives the output of d3chain
# (gen.out) and the sha256 of the inputs (inputs.out) and of the modules written (modules.out). Environment: JOBS (lines
# computed at once, default 4), CHECK=1 (d3chain -c: the compiled checkers on every part, the seed and the extension;
# needs masses100.txt in CERTDIR), WRAP (a command prefix for the build of d3chain and its run, e.g. a memory cap).
# INIT=1 writes modules.sha256 from the run instead of comparing. Exit 0 when the inputs and the modules match modules.sha256.
# The modules are written in a staging directory (under TMPDIR) and copied into the package only when they match, so
# the package never misses a module while d3chain runs.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
pkg=$(cd "$here/../.." && pwd)
cert=$(cd "${1:?usage: gen.sh CERTDIR [OUT]}" && pwd)
out=${2:-$here/out}; mkdir -p "$out"; out=$(cd "$out" && pwd)
read -r -a wrap <<< "${WRAP:-}"
list=$here/modules.sha256
files=$(cd "$cert" && { echo manifest.txt; awk '$1 !~ /^#/ && NF >= 3 { print $2; print $3 }' manifest.txt; } | sort -u)
(cd "$cert" && sha256sum $files | sed 's|  |  input/|' | sort -k2 -V) > "$out/inputs.out"
if [ -f "$list" ] && grep -E '^[0-9a-f]{64}  input/' "$list" | diff - "$out/inputs.out" > /dev/null; then :
else echo "the certificate is not the one of modules.sha256 (see $out/inputs.out)"; [ -n "${INIT:-}" ] || exit 1; fi
(cd "$here" && "${wrap[@]}" lake build d3chain)
dst=$pkg/FrogModel/D3/CertData
stage=$(mktemp -d "${TMPDIR:-/tmp}/d3chain.XXXXXX"); sdst=$stage/FrogModel/D3/CertData
opts=(-j "${JOBS:-4}"); [ "${CHECK:-0}" = 1 ] && opts+=(-c)
"${wrap[@]}" "$here/.lake/build/bin/d3chain" "$cert" "$stage" "${opts[@]}" > "$out/gen.out"
(cd "$stage" && find FrogModel/D3/CertData -name '*.lean' -print0 | xargs -0 sha256sum | sort -k2 -V) > "$out/modules.out"
if [ -n "${INIT:-}" ]; then
  { echo "# sha256 of the inputs (the manifest and the certificate files it names) and of the Lean modules that gen.sh writes from them"
    cat "$out/inputs.out" "$out/modules.out"; } > "$list"
  echo "modules.sha256 written: $(wc -l < "$out/inputs.out") inputs, $(wc -l < "$out/modules.out") modules"
elif grep -E '^[0-9a-f]{64}  FrogModel/' "$list" | diff - "$out/modules.out"; then
  echo "$(wc -l < "$out/modules.out") modules written, every sha256 equal to modules.sha256"
else
  echo "the modules written differ from modules.sha256; they are left in $stage, the package is unchanged"; exit 1
fi
# The package receives the modules only now, and only the files that changed (lake rebuilds by content).
printf '*\n!.gitignore\n' > "$sdst/.gitignore"
mkdir -p "$dst"; rsync -r --checksum --delete "$sdst/" "$dst/"
rm -rf "$stage"
