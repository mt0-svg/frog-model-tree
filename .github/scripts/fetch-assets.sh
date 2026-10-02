#!/bin/bash
# The data tarballs of ASSETS.md from a release or a draft of this repository, checked against the sha256 sums of
# ASSETS.md and unpacked into DIR (the .tar.xz files; others stay as they are); writes release=<tag> to GITHUB_OUTPUT (none when no release has them, outside a
# run by hand). For a package whose computations read data tarballs listed in ASSETS.md (sha256 and name, one per
# line); delete it otherwise. Usage, in a job with GH_TOKEN and contents: write: .github/scripts/fetch-assets.sh DIR
set -eu
a=${1:?usage: fetch-assets.sh DIR}; mkdir -p "$a"
grep -E '^[0-9a-f]{64}  ' ASSETS.md > "$a/SHA256SUMS"
want=$(awk '{print $2}' "$a/SHA256SUMS" | jq -R . | jq -sc .)
# One line per release that has every tarball of ASSETS.md, newest first: tag, draft, then id:name of each.
gh api --paginate "repos/$GITHUB_REPOSITORY/releases?per_page=100" | jq -rs --argjson want "$want" '
  add // [] | .[] | . as $r
  | [$want[] as $n | $r.assets[] | select(.name == $n) | "\(.id):\(.name)"] as $ids
  | select(($ids | length) == ($want | length))
  | "\($r.tag_name) \($r.draft) \($ids | join(" "))"' > "$a/candidates.txt"
if [ ! -s "$a/candidates.txt" ]; then
  # A run started by hand certifies a release: it must check the data tarballs.
  if [ "$GITHUB_EVENT_NAME" = workflow_dispatch ]; then
    echo "No release or draft has the data tarballs of ASSETS.md: upload them to a draft of the tag (head of release.yml) or keep ASSETS.md as in the previous release, then run this workflow again."
    exit 1
  fi
  echo "No release has the data tarballs of ASSETS.md: the checks on them are not run."
  exit 0
fi
found=""
while read -r tag draft pairs <&3; do
  for p in $pairs; do
    gh api -H 'Accept: application/octet-stream' "repos/$GITHUB_REPOSITORY/releases/assets/${p%%:*}" > "$a/${p#*:}"
  done
  if (cd "$a" && sha256sum -c SHA256SUMS); then found=$tag; break; fi
  echo "release $tag (draft: $draft): the data tarballs differ from ASSETS.md"
done 3< "$a/candidates.txt"
[ -n "$found" ] || { echo "no release has the data tarballs of ASSETS.md with its sha256 sums"; exit 1; }
echo "Data tarballs of the release $found, checked against ASSETS.md."
(cd "$a" && for f in *.tar.xz; do [ ! -e "$f" ] || tar xJf "$f"; done)
echo "release=$found" >> "$GITHUB_OUTPUT"
