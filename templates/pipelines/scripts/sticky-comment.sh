#!/usr/bin/env bash
# Create or update the comment of a pull request (or issue) that carries
# `marker`, with the text of `file`.
#
#   scripts/sticky-comment.sh <number> <marker> <file>
set -euo pipefail
number=$1 marker=$2 file=$3
id=$(gh api "repos/$GITHUB_REPOSITORY/issues/$number/comments" --paginate \
  --jq ".[] | select(.body | contains(\"$marker\")) | .id" | tail -n 1)
if [ -n "$id" ]; then
  gh api --silent -X PATCH "repos/$GITHUB_REPOSITORY/issues/comments/$id" -F "body=@$file"
else
  gh api --silent -X POST "repos/$GITHUB_REPOSITORY/issues/$number/comments" -F "body=@$file"
fi
