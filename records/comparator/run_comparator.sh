#!/usr/bin/env bash
# Comparator with nanoda on a built release tree, as the job comparator of .github/workflows/ci.yml runs it: the build
# outputs of the challenge module dropped (Comparator compiles it again from its source, in its sandbox), then
# Comparator on the config in a systemd user service with no AF_UNIX socket, here also with a memory cap and no swap
# (MEM, default 10G), a CPU quota (CPUS, default 4) and a time limit (TIME, default 2h). The memory peak is that of the
# service's control group, page cache included; a peak at the cap bounds the run's memory, it does not measure it.
# Usage: run_comparator.sh TREE [CONFIG], CONFIG relative to TREE, default config-recurrent.json; COMPARATOR (the
# comparator program, built at the commit and with the patch of ci.yml), COMPARATOR_LANDRUN, COMPARATOR_LEAN4EXPORT and
# COMPARATOR_NANODA set as in ci.yml, NANODA_REV the commit of nanoda_lib. Output: out/comparator.txt next to this
# script: the files checked with their sha256, Comparator's complete output, the memory peak, and a last line
# COMPARATOR PASS or FAIL with the wall time. Exit: Comparator's status, or 1 without its success line.
set -u
here=$(cd "$(dirname "$0")" && pwd)
tree=$(cd "${1:?usage: run_comparator.sh TREE [CONFIG]}" && pwd); cfg=${2:-config-recurrent.json}
MEM=${MEM:-10G} CPUS=${CPUS:-4} TIME=${TIME:-2h}
: "${COMPARATOR:?}" "${COMPARATOR_LANDRUN:?}" "${COMPARATOR_LEAN4EXPORT:?}" "${COMPARATOR_NANODA:?}"
mkdir -p "$here/out"; O=$here/out/comparator.txt
cd "$tree" || exit 1
ch=$(jq -r .challenge_module "$cfg") so=$(jq -r .solution_module "$cfg")
c=${ch//.//} s=${so//.//}
{
  echo "# run_comparator.sh on the release tree at $(git rev-parse --short HEAD) ($(git status --short --untracked-files=no | wc -l) changed files); $(date -u +%Y-%m-%dT%H:%MZ)"
  echo "# limits of the service: MemoryMax=$MEM, MemorySwapMax=0, CPUQuota=$((CPUS * 100))%, RuntimeMaxSec=$TIME"
  echo "# Comparator at $(git -C "$(dirname "$COMPARATOR")/../../.." rev-parse HEAD 2> /dev/null || echo 'an unknown commit'), lean4export at $(git -C "$(dirname "$COMPARATOR_LEAN4EXPORT")/../../.." rev-parse HEAD 2> /dev/null || echo 'an unknown commit'), nanoda_lib at ${NANODA_REV:-an unknown commit}"
  echo "# $cfg: $(jq -c . "$cfg")"
  sha256sum "$c.lean" "$s.lean" "$cfg" | sed 's/^/# sha256 /'
  rm -rfv ".lake/build/lib/lean/$c" .lake/build/lib/lean/"$c".* ".lake/build/ir/$c" .lake/build/ir/"$c".* | wc -l |
    sed 's/^/# build outputs of the challenge module dropped: /'
} > "$O"
s0=$(date +%s)
systemd-run --user --pipe --wait --collect -q -p RestrictAddressFamilies=~AF_UNIX \
  -p MemoryMax="$MEM" -p MemorySwapMax=0 -p CPUQuota="$((CPUS * 100))%" -p RuntimeMaxSec="$TIME" \
  -E PATH="$PATH" -E HOME="$HOME" -E COMPARATOR_LANDRUN="$COMPARATOR_LANDRUN" \
  -E COMPARATOR_LEAN4EXPORT="$COMPARATOR_LEAN4EXPORT" -E COMPARATOR_NANODA="$COMPARATOR_NANODA" \
  --working-directory "$tree" -- bash -c '
    lake env "$0" "$1"; rc=$?
    echo "memory.peak $(cat "/sys/fs/cgroup$(sed -n "s/^0:://p" /proc/self/cgroup)/memory.peak") bytes"
    exit $rc' "$COMPARATOR" "$cfg" > "$here/out/comparator.log" 2>&1
rc=$?
w=$(($(date +%s) - s0))
peak=$(sed -n 's/^memory.peak \([0-9]*\) bytes$/\1/p' "$here/out/comparator.log")
cap=$(numfmt --from=iec "$MEM")
{
  sed "s|$HOME|~|g; s|$tree|TREE|g; s/[[:space:]]*$//" "$here/out/comparator.log"
  if [ -n "$peak" ]; then
    if [ "$peak" -ge "$cap" ]; then note="at the cap of $((cap / 1048576)) MiB: a bound, not a measurement"
    else note="under the cap of $((cap / 1048576)) MiB"; fi
    echo "# memory peak of the service: $((peak / 1048576)) MiB, $note"
  else echo "# memory peak of the service: not recorded"; fi
  if [ "$rc" = 0 ] && grep -q '^Your solution is okay!' "$here/out/comparator.log"; then
    echo "COMPARATOR PASS: $w s wall, exit $rc"
  else echo "COMPARATOR FAIL: $w s wall, exit $rc"; [ "$rc" != 0 ] || rc=1; fi
} >> "$O"
rm -f "$here/out/comparator.log"
tail -n 2 "$O"
exit "$rc"
