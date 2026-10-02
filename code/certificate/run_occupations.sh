#!/bin/sh
# The occupations that choose the flags of the certificate (Section 8.3 of the paper): the expected number of visits
# of every (multiset of child states, number of waiting frogs) of each phase in the root chain without lumping, at
# threshold 1e-11, in floating point; the pairs at or above 1e-9 go to out/occupations.txt (17 MB, not committed).
# The program prints counts of the run, which the certificate does not use.
# Usage: code/certificate/run_occupations.sh
set -e
cd "$(dirname "$0")"
cargo build --release -q -p occupations
rm -f out/occupations.txt
XDP_HEAVY_OUT=out/occupations.txt XDP_HEAVY_TAU=1e-9 target/release/occupations table.cert 1e-11 > out/occupations.out
sha256sum out/occupations.txt >> out/occupations.out
