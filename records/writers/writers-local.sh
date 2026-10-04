#!/usr/bin/env bash
# The job writers3 of the release ci.yml, run here on a release tree: code/m1run/run.sh, code/d3cert/run.sh (from the
# masses that m1run writes) and code/dcheck/run.sh, with the gp found in GPDIR (PARI/GP 2.15.4, the version of CI,
# built from source) and the Rust of the tree's rust-toolchain.toml (1.98.1).
# Usage: writers-local.sh TREE GPDIR (RAYON_NUM_THREADS=2 is set here; the output records the CPUs visible).
# Output: out/writers-local.out, then each run.sh's complete output (its out/run.out in the tree). RESULT: PASS when the
# three exit 0.
set -u
here=$(cd "$(dirname "$0")" && pwd)
tree=$(cd "${1:?usage: writers-local.sh TREE GPDIR}" && pwd)
export PATH="${2:?usage: writers-local.sh TREE GPDIR}:$PATH" RAYON_NUM_THREADS=2
O=$here/out/writers-local.out
mkdir -p "$here/out"
{
  echo "# writers-local.sh on the release tree at $(git -C "$tree" rev-parse --short HEAD) ($(git -C "$tree" status --short --untracked-files=no | wc -l) changed files); $(date -u +%Y-%m-%dT%H:%MZ)"
  echo "# $(nproc) CPUs visible, RAYON_NUM_THREADS=$RAYON_NUM_THREADS; PARI/GP $(echo 'print(version())' | gp -q); $(cd "$tree" && rustc --version); $(cd "$tree" && cargo --version)"
  ok=1
  for w in m1run d3cert dcheck; do
    s=$(date +%s)
    if (cd "$tree" && "code/$w/run.sh" > /dev/null 2>&1); then r=PASS; else r=FAIL; ok=0; fi
    echo "== code/$w/run.sh: $r, $(($(date +%s) - s)) s (build included); its out/run.out:"
    cat "$tree/code/$w/out/run.out"
  done
  if [ $ok = 1 ]; then echo "RESULT: PASS"; else echo "RESULT: FAIL"; fi
} > "$O" 2>&1
tail -n 1 "$O"
