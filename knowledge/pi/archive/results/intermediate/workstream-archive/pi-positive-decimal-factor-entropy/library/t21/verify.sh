#!/usr/bin/env bash
set -euo pipefail

here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$here"

command -v sha256sum >/dev/null
command -v pdftotext >/dev/null
sha256sum -c ARTIFACT_HASHES.sha256
sha256sum -c SHA256SUMS

canonical=${CANONICAL_STATEMENT:-"$here/pi-positive-decimal-factor-entropy.txt"}
printf '%s  %s\n' \
  'a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6' \
  "$canonical" | sha256sum -c -

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

check_locator() {
  local file=$1
  local page=$2
  local needle=$3
  local out="$tmp/page.txt"

  pdftotext -f "$page" -l "$page" "$file" "$out"
  if ! grep -F -- "$needle" "$out" >/dev/null; then
    printf 'missing locator: %s page %s: %s\n' "$file" "$page" "$needle" >&2
    exit 1
  fi
}

check_locator sources/furstenberg-1967.pdf 48 'T H E O R E M IV. 1.'
check_locator sources/furstenberg-1967.pdf 48 'irrational'
check_locator sources/blmv-2009.pdf 3 'C OROLLARY 1.6.'
check_locator sources/blmv-2009.pdf 3 '(log N )'
check_locator sources/blmv-2009.pdf 3 'T HEOREM 1.8.'
check_locator sources/blmv-2009.pdf 3 'Diophantine-generic'
check_locator sources/badea-grivaux-2024-arxiv-v2.pdf 2 'Conjecture 1.2.'
check_locator sources/badea-grivaux-2024-arxiv-v2.pdf 3 'Conjecture 1.2 is largely open.'
check_locator sources/badea-grivaux-2024-arxiv-v2.pdf 5 'Theorem 1.5'
check_locator sources/badea-grivaux-2024-arxiv-v2.pdf 5 'large Fourier coefficients'
check_locator sources/hochman-shmerkin-2012.pdf 5 'Theorem 1.3.'
check_locator sources/hochman-shmerkin-2012.pdf 5 'invariant under Tm , Tn'
check_locator sources/hochman-shmerkin-2015-arxiv-v3.pdf 8 'Theorem 1.10.'
check_locator sources/hochman-shmerkin-2015-arxiv-v3.pdf 8 'positive entropy'
check_locator sources/wu-2019.pdf 5 'Theorem 1.4.'
check_locator sources/wu-2019.pdf 5 'dimB'

printf 'T21 source hashes and theorem locators verified.\n'
