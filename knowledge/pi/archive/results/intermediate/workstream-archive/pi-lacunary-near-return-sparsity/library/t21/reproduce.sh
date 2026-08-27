#!/usr/bin/env bash
set -euo pipefail

here="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
record_dir="$(CDPATH= cd -- "$here/.." && pwd)"
workspace="$(CDPATH= cd -- "$here/../../../.." && pwd)"

cd "$here"
python3 verify_tradeoffs.py

checked_dependencies=0
missing_dependencies=0

check_if_present() {
  expected="$1"
  path="$2"
  label="$3"
  if [[ -f "$path" ]]; then
    actual="$(sha256sum "$path" | cut -d ' ' -f 1)"
    if [[ "$actual" != "$expected" ]]; then
      printf 'hash mismatch for %s: expected %s, got %s\n' \
        "$label" "$expected" "$actual" >&2
      exit 1
    fi
    printf '%s hash passed\n' "$label"
    checked_dependencies=$((checked_dependencies + 1))
  else
    printf '%s not present in this replay layout; expected SHA-256 %s\n' \
      "$label" "$expected"
    missing_dependencies=$((missing_dependencies + 1))
  fi
}

check_if_present \
  cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8 \
  "$workspace/problems/local/pi-lacunary-near-return-sparsity.txt" \
  canonical-statement
check_if_present \
  14ae452f34068dd78877054e231c58af02c2563cd755f0ee4edc0ff0ebeeda13 \
  "$record_dir/knowledge_library/t13/IteratedLagResonance.lean" \
  T13
check_if_present \
  3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5 \
  "$record_dir/knowledge_library/notes/t18/zeilberger-zudilin-2020.pdf" \
  irrationality-PDF
check_if_present \
  49ca4907538e4ccea23cee27f051f5b33832ed2cf3e3093b4aab58a13c814a68 \
  "$record_dir/knowledge_library/notes/t18/zeilberger-zudilin-2020.txt" \
  irrationality-extract

if [[ -f SHA256SUMS ]]; then
  sha256sum -c SHA256SUMS
fi

if [[ "$missing_dependencies" -eq 0 ]]; then
  printf 'T21 full replay passed with %d dependency hashes checked\n' \
    "$checked_dependencies"
else
  printf 'T21 self-contained checks passed; %d external dependencies were unavailable and were not checked\n' \
    "$missing_dependencies"
fi
