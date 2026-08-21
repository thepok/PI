#!/usr/bin/env bash
set -euo pipefail

expected="a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6"
actual="$(sha256sum "pi-positive-decimal-factor-entropy.txt" | cut -d ' ' -f 1)"
test "$actual" = "$expected"

note="T34_CYLINDER_AFFINITY_CRITERION.md"
for locator in \
  "Step 1: exact partition and refinement facts" \
  "Step 2: monotonicity under refinement" \
  "Step 6: Hellinger limit" \
  "Theorem 1 (all-depth cylinder affinity)" \
  "Step 8: exact uniform translation" \
  "Step 9: a sequence-independent sufficient weak-limit hypothesis" \
  "Counterexample 1" \
  "Counterexample 2" \
  "Conditional times-16 specialization" \
  "Criterion verdict:"
do
  grep -Fq "$locator" "$note"
done

python3 "check_counterexamples.py"
echo "Canonical SHA-256: $actual"
echo "T34 artifact verification: PASS"
