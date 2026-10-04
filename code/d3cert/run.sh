#!/usr/bin/env bash
# The certificate of Proposition 15.1 (2) of the paper (the release asset frog-model-tree-d3-certificate.tar.zst,
# unpacked: d3-certificate/), written into out/d3-certificate/ from the masses at height 100 (MASSES, default
# ../m1run/out/mass_V48_h100.txt, which ../m1run/run.sh writes): the seed at height 100 (E 32, GM 96); 500 plain
# steps to height 600 at (32, 96, 16, 12), S2 and S3 terms, no S4; the extension to (64, 224) and five plain steps at
# (64, 224, 32, 24) to height 605; d3-fhat's floating point search of the supersolution T on [605, 1778279] from the
# state at 600 (written to T605.txt; its own floating point test of T prints FAIL at these margins); the
# outward-rounded interval check of T, raised to the state at 605 and to nondecreasing rows, against the row mode1
# (check605.cert); the manifest of the chain and its verification by d3-cert verify. Then the sha256 of the 510 files
# of the manifest against the input lines of ../d3chain/modules.sha256, the files that code/d3chain reads, and of
# T605.txt against its value below. Output: out/run.out. Exit 0 when the verification passes on its 508 lines and every
# sha256 is equal. The times that the programs print are left out of out/run.out. About 2 minutes on 2 cores.
# Usage: run.sh [MASSES]
set -euo pipefail
cd "$(dirname "$0")"
T605=c2160832056fcd119e984b3531cc7d98c7190f073dcb3917df6b2ba501158eca
cargo build --release -q --locked
here=$(pwd); B=$here/target/release/d3-cert F=$here/target/release/d3-fhat
masses=$(cd "$(dirname "${1:-../m1run/out/mass_V48_h100.txt}")" && pwd)/$(basename "${1:-../m1run/out/mass_V48_h100.txt}")
W=out/d3-certificate O=$here/out/run.out
rm -rf "$W"; mkdir -p "$W"
trap 'cat "$O"' EXIT
cd "$W"
{
  cp "$masses" masses100.txt
  echo "# seed at 100 (E 32, GM 96)"
  "$B" seed masses100.txt 100 32 96 m100.cert
  echo "# 500 steps to 600 at (32, 96, 16, 12)"
  "$B" chain m100.cert chain 600 16 12 1 0 16 12 2 > chain.log
  awk '$1 % 50 == 0' chain.log | cut -d' ' -f1-7,14-17
  echo "# extension to (64, 224) at 600 and five steps at (64, 224, 32, 24)"
  "$B" ext chain/m600.cert e600.cert 64 224
  "$B" chain e600.cert chain64 605 32 24 1 0 16 12 2
  echo "# d3-fhat: floating point search of T on [605, 1778279] from the state at 600 (margins 1e-8, 12 iterations)"
  "$B" tostate chain/m600.cert m600.st
  FHAT_SPINE=1 FHAT_HROWS="0.4,0.0792397,62" FHAT_MARGIN=1e-8,1e-8 FHAT_BELL=1e-9 FHAT_NIT=12 FHAT_LOAD=m600.st \
    FHAT_SAVET=T605.txt "$F" 64 224 32 24 605 1 2 200 -1 0.12 605 1778279 0 1e-12 > fhat.log 2>&1
  grep 'SAVET' fhat.log
  echo "# outward-rounded interval check of T on [605, 1778279], row mode1"
  "$B" tcheck chain64/m605.cert T605.txt 1778279 32 24 1 2 check605.cert mode1
  echo "# manifest and verification of the chain"
  {
    echo "# (CertS_1) short route on the certified M1 masses: seed at 100, Phi^S steps to 600, extension, 5 steps, check on [605, 1778279], row mode1"
    echo "SEED masses100.txt m100.cert"
    prev=m100.cert
    for h in $(seq 101 600); do echo "STEP $prev chain/m$h.cert"; prev=chain/m$h.cert; done
    echo "EXT $prev e600.cert"
    prev=e600.cert
    for h in 601 602 603 604 605; do echo "STEP $prev chain64/m$h.cert"; prev=chain64/m$h.cert; done
    echo "CHECK $prev check605.cert mode1"
  } > manifest.txt
  "$B" verify manifest.txt > verify.log 2>&1 || true
  head -3 verify.log; echo "..."; tail -3 verify.log
  echo "# sha256 of the 510 files of the manifest against the inputs of ../d3chain/modules.sha256, and of T605.txt"
} 2>&1 | sed -E 's/;? [0-9]+\.[0-9]+ s$//' > "$O"
st=0
grep -q '^verify: 508 lines checked, 0 failed: PASS; .*(CertS) holds' "$O" || { echo "the verification does not pass on 508 lines" >> "$O"; st=1; }
n=$(grep -cE '^[0-9a-f]{64}  input/' ../../../d3chain/modules.sha256)
if [ "$n" = 510 ] && sed -n 's|^\([0-9a-f]\{64\}\)  input/|\1  |p' ../../../d3chain/modules.sha256 | sha256sum -c --quiet >> "$O" 2>&1 &&
  echo "$T605  T605.txt" | sha256sum -c --quiet >> "$O" 2>&1; then
  echo "the 510 files equal the inputs of ../d3chain/modules.sha256, and T605.txt has the sha256 of this script" >> "$O"
else
  echo "the files differ from the inputs of ../d3chain/modules.sha256 ($n lines) or T605.txt from the sha256 of this script" >> "$O"; st=1
fi
exit "$st"
