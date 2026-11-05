#!/usr/bin/env bash
# Commit what changed in _data/ (the `data` branch) and push it.
#
#   scripts/publish-data.sh "<message>" [squash-after]
#
# Writers (refresh, previews, their cleanup) touch separate folders, so a
# push that loses a race replays its one commit onto the new tip. With
# `squash-after`, a branch with more commits than that is squashed into one
# commit and force-pushed: the data branch keeps the current files, and
# GitHub drops the old ones. Only the refresh workflow squashes.
set -euo pipefail

message=$1
squash_after=${2:-0}
cd _data

git add -A
if git diff --cached --quiet; then
  echo "data: nothing changed"
  exit 0
fi
git commit --quiet -m "$message"

squash=false
if [ "$squash_after" -gt 0 ] && [ -n "${GITHUB_REPOSITORY:-}" ]; then
  # Commits on the remote branch, up to 100 (the clone is shallow).
  count=$(gh api "repos/$GITHUB_REPOSITORY/commits?sha=data&per_page=100" --jq length 2>/dev/null || echo 0)
  if [ "$count" -ge "$squash_after" ]; then
    squash=true
  fi
fi

for attempt in 1 2 3 4 5; do
  if $squash; then
    # One commit with the current files; the lease fails the push if another
    # writer pushed since the last fetch, and the loop replays onto theirs.
    root=$(git commit-tree 'HEAD^{tree}' -m "$message (data branch squashed)")
    if git push --quiet --force-with-lease="data:$(git rev-parse origin/data)" origin "$root:refs/heads/data"; then
      echo "data: squashed into one commit"
      exit 0
    fi
  elif git push --quiet origin HEAD:refs/heads/data; then
    echo "data: pushed"
    exit 0
  fi
  echo "data: push $attempt lost a race; replaying onto the new tip"
  sleep $((attempt * 3))
  git fetch --quiet --depth 1 origin data
  git rebase --quiet --onto origin/data HEAD~1
done
echo "data: could not push after 5 attempts" >&2
exit 1
