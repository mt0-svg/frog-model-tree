#!/usr/bin/env bash
# The table of Proposition 15.2 of the paper. dbranch_m1.gp proposes the branches of the 95 intervals in
# floating point (out/dcheck_m1_cert.gp, compared with dcheck_m1_cert.gp); dcheck_m1.gp checks them in exact rationals
# with outward rounding (out/dcheck_m1.out, compared with the recorded dcheck_m1.out, their times aside); gen_table.gp
# writes ../../FrogModel/D3/LaneE/Table.lean from dcheck_m1_cert.gp (compared with the file of the checkout, kept in
# out/Table.lean.checkout); gen_probe.gp prints the margins of the 95 entries that the paper prints (Section 15),
# from the inequalities checked in exact rationals, and writes them as Lean theorems under out/probe/ (not used by the
# proof). Output: out/run.out. Exit 0 when the three compare equal and no entry of gen_probe.gp fails.
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p out
O=out/run.out
trap 'cat "$O"' EXIT
notimes() { sed -E '/^# [0-9.]+ s user, /d; s/; [0-9]+\.[0-9]+ s$/; (time) s/' "$1"; }
st=0
{
  gp -q dbranch_m1.gp < /dev/null > out/dcheck_m1_cert.gp
  if cmp -s out/dcheck_m1_cert.gp dcheck_m1_cert.gp; then echo "out/dcheck_m1_cert.gp equals dcheck_m1_cert.gp"
  else echo "out/dcheck_m1_cert.gp differs from dcheck_m1_cert.gp"; st=1; fi
  gp -q -s 512M dcheck_m1_cert.gp dcheck_m1.gp < /dev/null > out/dcheck_m1.out 2>&1
  tail -n 2 out/dcheck_m1.out
  if cmp -s <(notimes out/dcheck_m1.out) <(notimes dcheck_m1.out); then echo "out/dcheck_m1.out equals dcheck_m1.out, times aside"
  else echo "out/dcheck_m1.out differs from dcheck_m1.out beyond times"; st=1; fi
  cp ../../FrogModel/D3/LaneE/Table.lean out/Table.lean.checkout
  gp -q dcheck_m1_cert.gp gen_table.gp < /dev/null
  if cmp -s ../../FrogModel/D3/LaneE/Table.lean out/Table.lean.checkout; then
    echo "../../FrogModel/D3/LaneE/Table.lean, written again, equals the file of the checkout"
  else echo "../../FrogModel/D3/LaneE/Table.lean, written again, differs from the file of the checkout (out/Table.lean.checkout)"; st=1; fi
  rm -rf out/probe
  gp -q dcheck_m1_cert.gp gen_probe.gp < /dev/null > out/probe.txt
  cat out/probe.txt
  grep -q '^rational form self-check: 0 failing of 95;' out/probe.txt || st=1
} > "$O" 2>&1
exit "$st"
