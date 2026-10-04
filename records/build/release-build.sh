#!/usr/bin/env bash
# The full build of the release tree with its data, as the jobs data, data3, build-N and lean of its ci.yml run it,
# timed part by part: code/g3k/gen.sh (FrogModel/G3Q from the d = 4 certificate), code/m1gen/gen.sh
# (FrogModel/D3/M1Data from the stored M1 run and the masses), code/d3chain/gen.sh (FrogModel/D3/CertData from the
# certificate of Proposition 15.1), then code/formal-proof/clean_build.sh with the knobs of ci.yml (HB=1 LB=2
# PEAK_HEAVY=9G PEAK_LIGHT=4G MEM_MARGIN=1G),
# then `lake build --no-build` of the default targets, main_axioms.lean, the negative controls of code/d3chain/neg and
# facts.lean. Mathlib comes with the tree (.lake/packages at the revisions of lake-manifest.json); only the package is
# compiled.
# Usage: release-build.sh TREE ASSETS (the log records the CPUs visible); ASSETS holds
# certificate.v4 (unpacked), frog-model-tree-d3-m1run.txt.xz and d3-certificate/ (unpacked). Outputs, in out/
# next to this script: release-build.out (the log: each part with its wall time, the generators' outputs, the
# result lines), and copies of clean_build.out and clean_build_modules.txt (the time of every module), as
# release-build-clean_build.out and release-build-modules.txt. LEAN_NUM_THREADS from the environment, 4 by default.
# RESUME=1 runs a second part on the tree of a first one stopped by its time limit: no data step, clean_build.sh
# with RESUME=1 on the build directory left, then the steps after it. POST=1 runs a second part with only the steps
# after clean_build.sh, on a tree that a first part built. A second part appends to release-build.out. The logs have
# the home directory written ~ and no trailing blanks.
set -u
here=$(cd "$(dirname "$0")" && pwd)
tree=$(cd "${1:?usage: release-build.sh TREE ASSETS}" && pwd); a=$(cd "${2:?usage: release-build.sh TREE ASSETS}" && pwd)
O=$here/out/release-build.out; mkdir -p "$here/out" "$here/out/release-build"
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-4}; RESUME=${RESUME:-0}; POST=${POST:-0}
TARGETS="Defs Main G3K Challenge Solution D3 ChallengeRecurrent SolutionRecurrent"
cd "$tree" || exit 1
t0=$(date +%s)
part() { # name, command...: runs it, logs its output, wall time and exit status
  local name=$1 s rc; shift; s=$(date +%s)
  echo "== $name: $*"
  "$@" 2>&1 | tail -n 40; rc=${PIPESTATUS[0]}
  echo "== $name: exit $rc, $(($(date +%s) - s)) s"
  return "$rc"
}
replay() { # lake build --no-build of every module of FrogModel/: each built module replays its messages; full output in
  # out/release-build-replay.txt, the home directory written ~
  local r; mapfile -t mods < <(find FrogModel -name '*.lean' | sed 's|\.lean$||; s|/|.|g' | LC_ALL=C sort)
  lake build --no-build "${mods[@]}" 2>&1 | sed "s|$HOME|~|g; s/[[:space:]]*$//" > "$here/out/release-build-replay.txt"; r=${PIPESTATUS[0]}
  echo "${#mods[@]} modules, exit $r"; tail -n 2 "$here/out/release-build-replay.txt"; return "$r"
}
msgs() { # the warnings and infos of the modules (the sorry of the two challenges aside): none allowed in the d = 3 modules
  # (FrogModel/D3, LemmaR, ZeroOne, ChallengeRecurrent.lean, SolutionRecurrent.lean); counted and reported in the d = 4
  # modules, which are those of v1 byte for byte
  local f=$here/out/release-build-replay.txt d3='FrogModel/((D3|LemmaR|ZeroOne)/|(ChallengeRecurrent|SolutionRecurrent)\.lean:)'
  local sorry="^warning: FrogModel/(Challenge|ChallengeRecurrent)\.lean:[0-9]+:[0-9]+: declaration uses [\`']sorry[\`']$"
  grep -E '^(warning|info): FrogModel/' "$f" | grep -vE "$sorry" > "$here/out/release-build-messages.txt"
  local w3 i3 w4 i4
  w3=$(grep -cE "^warning: $d3" "$here/out/release-build-messages.txt"); i3=$(grep -cE "^info: $d3" "$here/out/release-build-messages.txt")
  w4=$(grep -E '^warning: ' "$here/out/release-build-messages.txt" | grep -vcE "^warning: $d3")
  i4=$(grep -E '^info: ' "$here/out/release-build-messages.txt" | grep -vcE "^info: $d3")
  echo "d = 3 modules: warnings $w3, infos $i3 (none allowed); d = 4 modules (v1): warnings $w4, infos $i4; the sorry of FrogModel/Challenge.lean and FrogModel/ChallengeRecurrent.lean aside"
  sed -E 's/^(warning|info): ([^:]+):.*/\1 \2/' "$here/out/release-build-messages.txt" | sort | uniq -c | sort -rn | head -n 35
  [ "$w3" = 0 ] && [ "$i3" = 0 ]
}
negd3() { # the negative controls of the d = 3 data, as the lean job of ci.yml runs them: each must be rejected by the kernel
  local f rc log n=0 bad=0
  for f in code/d3chain/neg/Neg*.lean; do
    n=$((n + 1)) rc=0
    log=$(lake env lean "$f" 2>&1) || rc=$?
    if [ "$rc" -ne 0 ] && grep -qF '(kernel) application type mismatch' <<< "$log" && grep -q decide <<< "$log"; then
      echo "$f  rc $rc  fails as expected"
    else echo "$f  rc $rc  UNEXPECTED"; bad=1; fi
    printf '%s\n' "$log" | head -8
  done
  [ "$n" -ge 2 ] && [ "$bad" = 0 ]
}
{
  echo "# release-build.sh on the release tree at $(git rev-parse --short HEAD) ($(git status --short --untracked-files=no | wc -l) changed files); $(date -u +%Y-%m-%dT%H:%MZ)"
  echo "# $(nproc) CPUs visible, LEAN_NUM_THREADS=$LEAN_NUM_THREADS; $(lean --version 2> /dev/null || cat lean-toolchain)"
  ok=1
  if [ "$POST" = 1 ]; then echo "# POST=1: a second part, the steps after the build on the tree that the first part built"
  elif [ "$RESUME" = 1 ]; then echo "# RESUME=1: a second part, on the data modules and the build directory of the first; clean_build.sh continues"; else
  part "data: code/g3k/gen.sh" code/g3k/gen.sh "$a/certificate.v4" "$here/out/release-build/g3k" || ok=0
  part "data3: code/m1gen/gen.sh" code/m1gen/gen.sh "$a/frog-model-tree-d3-m1run.txt.xz" "$a/d3-certificate/masses100.txt" "$here/out/release-build/m1gen" || ok=0
  part "data3: code/d3chain/gen.sh" env JOBS=4 code/d3chain/gen.sh "$a/d3-certificate" "$here/out/release-build/d3chain" || ok=0; fi
  sed -i "s|$HOME|~|g" "$here"/out/release-build/*/*.out
  if [ "$POST" != 1 ]; then
  part "build: code/formal-proof/clean_build.sh" env RUN_WRAP= HB=1 LB=2 PEAK_HEAVY=9G PEAK_LIGHT=4G MEM_MARGIN=1G MIN_DISK_GB=3 RESUME="$RESUME" \
    code/formal-proof/clean_build.sh || ok=0
  cp code/formal-proof/clean_build.out "$here/out/release-build-clean_build.out" 2> /dev/null
  cp code/formal-proof/clean_build_modules.txt "$here/out/release-build-modules.txt" 2> /dev/null
  fi
  # shellcheck disable=SC2086
  part "lean: lake build --no-build" lake build --no-build $TARGETS || ok=0
  part "lean: replay of every module" replay || ok=0
  part "lean: warnings and infos of the modules" msgs || ok=0
  part "lean: main_axioms.lean" lake env lean code/formal-proof/main_axioms.lean || ok=0
  part "lean: negative controls of the d = 3 data" negd3 || ok=0
  part "lean: facts.lean" lake env lean code/formal-proof/facts.lean || ok=0
  echo "# total $(($(date +%s) - t0)) s"
  if [ $ok = 1 ]; then echo "RESULT: PASS"; else echo "RESULT: FAIL"; fi
} 2>&1 | sed -u "s|$HOME|~|g; s/[[:space:]]*$//" | if [ "$RESUME" = 1 ] || [ "$POST" = 1 ]; then cat >> "$O"; else cat > "$O"; fi
tail -n 1 "$O"
