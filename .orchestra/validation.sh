#!/usr/bin/env bash
set -euo pipefail

# $HOME is read-only in this sandbox, so keep lake's cache dir inside the repo.
export XDG_CACHE_HOME="$PWD/.cache-home"

# Verify the worktree is clean
if ! [ -z "$(git status --porcelain)" ]; then
  echo "The working tree is not clean. Commit changes or discard if temporary."
  exit 1
fi

# Verify all .lean files are imported.
lake exe mk_all --lib Belyi --git --check || exit 1

# Fetch build cache
lake exe cache get

# Build everything, failing on any warning (including `sorry`): the project is
# sorry- and axiom-free, and Belyi's theorem `Belyi.belyi_iff` depends only on
# `propext`, `Classical.choice` and `Quot.sound`.
lake build --wfail

echo "Validation OK."
