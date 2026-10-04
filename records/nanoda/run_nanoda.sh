#!/usr/bin/env bash
# nanoda on the closures of three theorems of the proof for d = 3, one export each: Proposition 15.2 of the paper
# (FrogModel.D3.LaneE.dcheck1_holds), Lemma 14.3 (FrogModel.D3.LaneE.dprime_tail_holds) and the declaration behind
# Theorem 14.1 (FrogModel.D3.LaneE.thmDprime1_of). lean4export writes the closure of each theorem from the built
# package; nanoda checks it on one thread with nanoda.json next to this script (the axioms propext, Classical.choice
# and Quot.sound, any other one an error).
# Usage: run_nanoda.sh TREE SCRATCH. TREE is a release tree with its data modules written and its package built;
# LEAN4EXPORT and NANODA name the two programs, built as the job comparator of .github/workflows/ci.yml builds them
# (lean4export at the commit that job checks, nanoda_bin of nanoda_lib at the commit it installs, given in NANODA_REV).
# SCRATCH receives each export, deleted after its check. Output: out/nanoda.txt next to this script: per theorem, the
# exit status, wall time and largest resident memory of the export and of the check (GNU time), the size of the export
# and the complete output of nanoda. Exit 0 when the six steps exit 0.
set -u
here=$(cd "$(dirname "$0")" && pwd)
tree=$(cd "${1:?usage: run_nanoda.sh TREE SCRATCH}" && pwd); S=${2:?usage: run_nanoda.sh TREE SCRATCH}
L4E=${LEAN4EXPORT:?set LEAN4EXPORT}; NAN=${NANODA:?set NANODA}
mkdir -p "$S" "$here/out"; S=$(cd "$S" && pwd)
O=$here/out/nanoda.txt
cg=/sys/fs/cgroup$(sed -n 's/^0:://p' /proc/self/cgroup)
cd "$tree" || exit 1
ok=1
{
  echo "# run_nanoda.sh on the release tree at $(git rev-parse --short HEAD) ($(git status --short --untracked-files=no | wc -l) changed files); $(date -u +%Y-%m-%dT%H:%MZ)"
  echo "# $(nproc) CPUs visible; memory limit of the control group: $(cat "$cg/memory.max" 2> /dev/null || echo unknown)"
  echo "# lean4export at $(git -C "$(dirname "$L4E")/../../.." rev-parse HEAD 2> /dev/null || echo 'an unknown commit'); nanoda_bin of nanoda_lib at ${NANODA_REV:-an unknown commit}"
  echo "# nanoda.json: $(tr -s ' \n' ' ' < "$here/nanoda.json")"
  for t in Table:dcheck1_holds Tail:dprime_tail_holds Induction:thmDprime1_of; do
    mod=FrogModel.D3.LaneE.${t%%:*} name=FrogModel.D3.LaneE.${t#*:} ex=$S/${t#*:}.export
    echo "== $name (module $mod)"
    /usr/bin/time -f '%e s wall, largest resident memory %M KB' -o "$S/time" lake env "$L4E" "$mod" -- "$name" > "$ex" 2> "$S/err"
    rc=$?; [ "$rc" = 0 ] || ok=0
    echo "export: exit $rc, $(tail -1 "$S/time"), $(stat -c %s "$ex") bytes"
    grep -v '^Command exited' "$S/err" | head -20
    RUST_MIN_STACK=4294967296 /usr/bin/time -f '%e s wall, %U s user, largest resident memory %M KB' -o "$S/time" \
      "$NAN" "$here/nanoda.json" < "$ex" > "$S/out" 2>&1
    rc=$?; [ "$rc" = 0 ] || ok=0
    echo "nanoda: exit $rc, $(tail -1 "$S/time"); its output:"
    cat "$S/out"
    rm -f "$ex"
  done
  if [ $ok = 1 ]; then echo "RESULT: PASS"; else echo "RESULT: FAIL"; fi
} 2>&1 | sed -u "s|$HOME|~|g; s|$S|SCRATCH|g; s/[[:space:]]*$//" > "$O"
tail -n 1 "$O"
[ "$(tail -n 1 "$O")" = "RESULT: PASS" ]
