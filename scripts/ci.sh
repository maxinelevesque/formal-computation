#!/usr/bin/env bash
# Run on Modal by the CI runner (source root = repo root), from .forgejo/workflows/ci.yml.
# the CI runner has already run `lake exe cache get` in the project directory.
# Never run this on the dev machine: it builds Mathlib-importing modules.
#
# the CI runner returns only the last ~6000 characters of output to the Forgejo log,
# so this script ends with a compact summary.
set -uo pipefail
cd "$(dirname "$0")/.."
LOG=/tmp/lake-build.log
: > "$LOG"
BUDGET=${LAKE_BUILD_TIMEOUT:-2700}

before=$(sha256sum lake-manifest.json 2>/dev/null || echo none)
timeout "$BUDGET" lake build 2>&1 | tee -a "$LOG"
rc=${PIPESTATUS[0]}
after=$(sha256sum lake-manifest.json 2>/dev/null || echo none)

# Axiom audit: elaborate the audit file against the freshly built oleans.
AUDIT=/tmp/axioms.log
: > "$AUDIT"
if [ "$rc" -eq 0 ] && [ -f FormalComputation/Audit.lean ]; then
  lake env lean FormalComputation/Audit.lean > "$AUDIT" 2>&1
  rc_audit=$?
else
  rc_audit=0
fi

# Print the resolved manifest until one is committed (the CI runner's `cache get` creates it
# before this script runs, so a before/after comparison cannot detect that case).
if [ "$before" != "$after" ] || [ ! -f scripts/manifest-committed ]; then
  echo "LAKE_MANIFEST_BEGIN"; cat lake-manifest.json; echo "LAKE_MANIFEST_END"
fi

echo "==== AXIOMS ===="
# One line per declaration; long axiom lists are folded by Lean, so join continuation lines.
awk '/depends on axioms|does not depend on any axioms/{if (cur) print cur; cur=$0; next} /^ /{cur=cur $0; next} {if (cur) print cur; cur=""} END{if (cur) print cur}' "$AUDIT" \
  | sed -E 's/  +/ /g' | cut -c1-220 | head -80
grep -E "^error" "$AUDIT" | head -10 || true

echo "==== SUMMARY ===="
if [ "$rc" -eq 124 ]; then echo "lake build TIMED OUT after ${BUDGET}s"; fi
echo "sorry warnings: $(grep -cE "declaration uses .sorry." "$LOG" || true)"
grep -E -B1 "declaration uses .sorry." "$LOG" | grep -oE "FormalComputation/[A-Za-z/]+\.lean:[0-9]+" | sort | uniq | head -60 || true
echo "source lines with sorry (outside comments): $(grep -rnw --include='*.lean' sorry FormalComputation | grep -vE '^[^:]+:[0-9]+:\s*(--|/-)' | grep -vE '`sorry`|sorryAx' | wc -l)"
for tier in "tier1:Orth Presentation LocalSystems Translation Collapse" "tier2:Pentagon Dehn" "tier3:SKI/Syntax SKI/Weight SKI/PermEq" "essay:SKI/Types Predicates" "stretch:Stretch/Trace Stretch/Conjoint Stretch/PentQuotient Stretch/RedCat"; do
  name=${tier%%:*}; files=""
  for m in ${tier#*:}; do files="$files FormalComputation/$m.lean"; done
  n=$(cat $files 2>/dev/null | grep -vE '^\s*(--|/-)' | grep -wc sorry || true)
  echo "sorry in $name sources: $n"
done
echo "audit entries depending on sorryAx: $(grep -c "sorryAx" "$AUDIT" || true)"
echo "project modules built: $(grep -cE "Built FormalComputation" "$LOG" || true)"
echo "---- modules with errors ----"
grep -oE "^error: [^:]+\.lean" "$LOG" | sort | uniq -c | head -40 || true
if [ "$rc" -ne 0 ]; then
  echo "---- errors (first lines of each) ----"
  grep -E -A6 "^error:" "$LOG" | cut -c1-240 | head -c 4500 || true
  echo
fi
echo "lake build exit code: $rc; audit exit code: $rc_audit"
[ "$rc" -eq 0 ] && [ "$rc_audit" -eq 0 ]
