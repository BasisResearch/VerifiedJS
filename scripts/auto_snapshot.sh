#!/bin/bash
cd /opt/verifiedjs
git add -A 2>/dev/null
# Only amend if there are changes
if ! git diff --cached --quiet 2>/dev/null; then
  git commit --amend --no-edit --date="$(date -R)" 2>/dev/null || \
  git commit -m "snapshot" 2>/dev/null
fi
