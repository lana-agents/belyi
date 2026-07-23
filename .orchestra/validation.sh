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

# Build everything. Genuine elaboration errors fail here.
#
# We deliberately do NOT pass `--wfail`. Per taxis #201 the project's three
# research-grade inputs — B9 `rigidity_finiteness`, B10(ii) `belyi_spreadOut`,
# B11 `spreadOut_isotrivial_point` — are stated as `theorem … := sorry` rather
# than as `axiom`s, so the outstanding obligations are surfaced honestly (they
# appear as `sorryAx` in `#print axioms` and as `sorry` warnings at build) and
# tracked as concrete goals (issues #194, #199, #200). Those `sorry` warnings
# would make `--wfail` reject the build. Instead we enforce a stricter,
# sorry-aware policy below: the ONLY tolerated warnings are the sanctioned
# `sorry`s, and only in the three files that carry them.
set +e
BUILD_LOG="$(lake build 2>&1)"
BUILD_RC=$?
set -e
echo "$BUILD_LOG"
if [ "$BUILD_RC" -ne 0 ]; then
  echo "Validation failed: lake build returned $BUILD_RC."
  exit 1
fi

# (1) No warning or error other than a sanctioned `sorry` warning is allowed
#     (this preserves the `--wfail` guarantee for every real warning).
UNEXPECTED="$(printf '%s\n' "$BUILD_LOG" \
  | grep -E 'warning:|error:' \
  | grep -v 'declaration uses .sorry.' || true)"
if [ -n "$UNEXPECTED" ]; then
  echo "Validation failed: unexpected warnings/errors (only sanctioned \`sorry\` warnings are allowed):"
  printf '%s\n' "$UNEXPECTED"
  exit 1
fi

# (2) Every `sorry` warning must come from one of the sanctioned files (the
#     axiom-replacements of taxis #201). A `sorry` anywhere else fails the build.
ALLOWED_SORRY_FILES='Belyi/Rigidity.lean Belyi/SpreadOut.lean Belyi/Descent.lean'
SORRY_LOCS="$(printf '%s\n' "$BUILD_LOG" \
  | grep -oE '[^ ]+\.lean:[0-9]+:[0-9]+: declaration uses .sorry.' \
  | sort -u || true)"
BAD_SORRY=""
while IFS= read -r loc; do
  [ -z "$loc" ] && continue
  file="${loc%%:*}"
  case " $ALLOWED_SORRY_FILES " in
    *" $file "*) ;;
    *) BAD_SORRY="${BAD_SORRY}${loc}"$'\n' ;;
  esac
done <<< "$SORRY_LOCS"
if [ -n "$BAD_SORRY" ]; then
  echo "Validation failed: \`sorry\` found outside the sanctioned files ($ALLOWED_SORRY_FILES):"
  printf '%s\n' "$BAD_SORRY"
  exit 1
fi

echo "Validation OK (build green; only the sanctioned taxis-#201 \`sorry\`s present)."
