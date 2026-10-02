#!/bin/sh
# The certificate (Section 8.3 of the paper; the format is FORMAT.md): the states with the flag 1 on the pairs of
# out/occupations.txt (run_occupations.sh) at or above 1e-7, the values of the two linear systems and the plan, written
# to out/certificate.v4.zst; the output of the run to out/gen.out, ending with the sha256 of the data. Usage: code/certificate/run_gen.sh
set -e
cd "$(dirname "$0")"
cargo build --release -q -p certificate
rm -f out/certificate.v4.zst
target/release/gen --table table.cert --table-ref ../table.cert --occ out/occupations.txt --hmin 1e-7 \
  --out out/certificate.v4.zst --info out/info.out > out/gen.out
sha256sum out/certificate.v4.zst >> out/gen.out
stat -c "%s bytes %n" out/certificate.v4.zst >> out/gen.out
