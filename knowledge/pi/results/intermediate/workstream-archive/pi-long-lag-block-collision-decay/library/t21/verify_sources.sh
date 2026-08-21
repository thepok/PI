#!/bin/sh
set -eu

cd "$(dirname "$0")"
sha256sum -c SOURCE_SHA256SUMS

command -v pdftotext >/dev/null 2>&1 || {
  echo "pdftotext is required for locator replay" >&2
  exit 1
}

tmpdir=$(mktemp -d)
trap 'rm -rf "$tmpdir"' EXIT HUP INT TERM

pdftotext -f 3 -l 3 -layout demeter-silva-1311.4092v1.pdf "$tmpdir/ds-p3.txt"
pdftotext -f 15 -l 15 -layout demeter-silva-1311.4092v1.pdf "$tmpdir/ds-p15.txt"
pdftotext -f 17 -l 18 -layout aistleitner-berkes-seip-1210.0741v5.pdf "$tmpdir/abs-p17-18.txt"
pdftotext -f 2 -l 2 -layout chang-kerr-shparlinski-1706.04776v2.pdf "$tmpdir/cks-p2.txt"
pdftotext -f 4 -l 5 -layout chang-kerr-shparlinski-1706.04776v2.pdf "$tmpdir/cks-p4-5.txt"
pdftotext -f 6 -l 6 -layout chang-kerr-shparlinski-1706.04776v2.pdf "$tmpdir/cks-p6.txt"

grep -F "Carleson operator is defined" "$tmpdir/ds-p3.txt" >/dev/null
grep -F "Theorem 7.1" "$tmpdir/ds-p15.txt" >/dev/null
grep -F "Lemma 4." "$tmpdir/abs-p17-18.txt" >/dev/null
grep -F "Vλ" "$tmpdir/cks-p2.txt" >/dev/null
grep -F "Theorem 2.2." "$tmpdir/cks-p4-5.txt" >/dev/null
grep -F "Lemma 3.1." "$tmpdir/cks-p6.txt" >/dev/null

grep -F "def orderedLongPairDomain" T8_SPECTRAL_SOURCE.lean >/dev/null
grep -F "theorem mem_orderedLongPairDomain_iff" T8_SPECTRAL_SOURCE.lean >/dev/null
grep -F "def ScaleMatchedL1Bound" T12_SCALE_MATCHED_SOURCE.lean >/dev/null
grep -F "theorem scaleMatchedL1Bound_iff_quantifiers" T12_SCALE_MATCHED_SOURCE.lean >/dev/null

for duplicate in \
  APPLICABILITY_MATRIX.md \
  bailey-crandall-2001-random-character.pdf \
  philipp-1975-lacunary.pdf \
  fukuyama-2008-discrepancy.pdf \
  rudnick-zaharescu-1999-pair-correlation.pdf \
  chernov-kleinbock-1999-arxiv.pdf \
  rousseau-2021-longest-common-substring.pdf
do
  if [ -e "$duplicate" ]; then
    echo "unexpected duplicated T5 artifact: $duplicate" >&2
    exit 1
  fi
done

t5dir=../knowledge_library/t5
if [ -f "$t5dir/APPLICABILITY_MATRIX.md" ] && [ -f "$t5dir/SOURCE_MANIFEST.md" ]; then
  (
    cd "$t5dir"
    printf '%s  %s\n' \
      ab5bcb0ebd5eb590c849cc6620d4bdd764415ef9de88f2881d8ce48429715406 APPLICABILITY_MATRIX.md \
      ace2233019ea2a24e8b83fb49b03c968ca4f5a1f6d87e04327f12a784c70fc65 SOURCE_MANIFEST.md |
      sha256sum -c -
  )
else
  echo "external T5 library absent; retained T21 sources still verified"
fi

echo "source hashes and named locators verified"
