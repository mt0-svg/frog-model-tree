#!/usr/bin/env bash
# The times of the full release build (release-build.sh), per part of the CI chain and per group of modules.
# Input, in out/ next to this script: release-build.out (each part of release-build.sh with its wall time) and
# release-build-modules.txt (lake's "Built M (t)" lines of clean_build.sh, the time of every module; the groups count
# the full build only, without the lines of a later part RESUME=1, which compiles again the modules changed since).
# Groups: G3Q (the d = 4 data modules), d = 4 (the rest of FrogModel outside D3, LemmaR, ZeroOne and the two d = 3
# targets), M1Data, CertData by directory (S the states, L the lines with their kernel checks, B the segments, the
# top files), Chain (FrogModel.D3.Chain), the other d = 3 modules (D3, LemmaR, ZeroOne), and the targets
# ChallengeRecurrent and SolutionRecurrent. For each: modules, sum of module times, the longest module.
# The sum of module times is CPU-ish time (lake runs several modules at once); the wall time of the build is the
# line of clean_build.sh in release-build.out. CI cuts the build into parts of at most 300 minutes (jobs of at most
# 360), so what must fit in one part is the longest module.
# Output: out/release-build-times.out.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
mods=$here/out/release-build-modules.txt log=$here/out/release-build.out out=$here/out/release-build-times.out
{
  echo "# parts of release-build.sh (wall time, from release-build.out), run by run"
  grep -E '^# release-build\.sh on |^# (POST|RESUME)=1|^== .*: exit [0-9]+, [0-9]+ s$|^# total |^RESULT' "$log" |
    awk -F', ' '/^== / { sub(/^== /, ""); s = $NF; sub(/ s$/, "", s); printf "  %-58s %8d s  %6.2f h\n", $1, s, s / 3600; next }
      /^# (POST|RESUME)=1/ { print "  " substr($0, 3, index($0, ":") - 3); next }
      /^# release-build/ { sub(/ \([0-9]+ changed files\)/, ""); print; next }
      { print "  " $0 }'
  echo
  echo "# modules of clean_build.sh by group (from release-build-modules.txt: the full build, the lines before a later part RESUME=1)"
  printf '%-34s %7s %12s %10s  %s\n' group modules "sum (s)" "max (s)" "longest module"
  sed -n '/^# RESUME=1$/q; p' "$mods" | sed -nE 's/.*Built ([A-Za-z0-9_.]+) \((.*)\)$/\1\t\2/p' |
    awk -F'\t' '
      function secs(t,   n, a, i, v) { v = 0; n = split(t, a, " ")
        for (i = 1; i <= n; i++) {
          if (a[i] ~ /ms$/) v += substr(a[i], 1, length(a[i]) - 2) / 1000
          else if (a[i] ~ /s$/) v += substr(a[i], 1, length(a[i]) - 1)
          else if (a[i] ~ /m$/) v += 60 * substr(a[i], 1, length(a[i]) - 1)
          else if (a[i] ~ /h$/) v += 3600 * substr(a[i], 1, length(a[i]) - 1) }
        return v }
      function group(m) {
        if (m ~ /^FrogModel\.G3Q\./) return "G3Q (d = 4 data)"
        if (m ~ /^FrogModel\.D3\.M1Data\./) return "M1Data (d = 3 run)"
        if (m ~ /^FrogModel\.D3\.CertData\.S\./) return "CertData.S (states)"
        if (m ~ /^FrogModel\.D3\.CertData\.L\./) return "CertData.L (lines, kernel checks)"
        if (m ~ /^FrogModel\.D3\.CertData\.B\./) return "CertData.B (segments)"
        if (m ~ /^FrogModel\.D3\.CertData\./) return "CertData (Seed, Ext, LeT, Main)"
        if (m ~ /^FrogModel\.D3\.Chain\./) return "Chain"
        if (m ~ /^FrogModel\.(ChallengeRecurrent|SolutionRecurrent)$/) return "ChallengeRecurrent, SolutionRecurrent"
        if (m ~ /^FrogModel\.(D3|LemmaR|ZeroOne)\./) return "d = 3 (D3, LemmaR, ZeroOne)"
        return "d = 4 (the rest)" }
      { g = group($1); v = secs($2); n[g]++; s[g] += v; if (v > mx[g]) { mx[g] = v; arg[g] = $1 }; tot += v; cnt++ }
      END {
        for (g in n) printf "%-34s %7d %12.1f %10.1f  %s\n", g, n[g], s[g], mx[g], arg[g] | "sort"
        close("sort")
        printf "%-34s %7d %12.1f\n", "all", cnt, tot }'
} > "$out"
cat "$out"
