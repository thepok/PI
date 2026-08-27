#!/bin/sh
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$ROOT"

sha256sum -c SHA256SUMS

command -v pdftotext >/dev/null 2>&1 || {
  printf '%s\n' 'pdftotext is required for locator replay' >&2
  exit 1
}

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT HUP INT TERM

check_page() {
  file=$1
  page=$2
  pattern=$3
  out="$TMP/page-${page}.txt"
  pdftotext -f "$page" -l "$page" -layout "$file" "$out"
  test -s "$out"
  grep -Fq "$pattern" "$out"
}

check_page iyer-2312.01076.pdf 3 'Theorem 1.1. For any'
check_page iyer-2312.01076.pdf 4 'Some elementary observations'
check_page iyer-2312.01076.pdf 6 'Lemma 3.3. For all'
check_page iyer-2312.01076.pdf 6 'Lemma 3.4.'

check_page adamczewski-bugeaud-2007.pdf 7 'Theorem 5. Let'
check_page adamczewski-bugeaud-2007.pdf 10 'Lemma 1. For any integer n'

check_page pollington-velani-zafeiropoulos-zorin-1906.01151.pdf 3 'Theorem 1. Let'
check_page pollington-velani-zafeiropoulos-zorin-1906.01151.pdf 11 'Theorem 3. Let'
check_page pollington-velani-zafeiropoulos-zorin-1906.01151.pdf 11 'smooth numbers'

check_page blmv-2009.pdf 3 'Diophantine-generic: there exists k so that'
check_page blmv-2009.pdf 3 '(log log N )'

check_page corvaja-zannier-math0403522.pdf 2 'Main Theorem. Let'
check_page corvaja-zannier-math0403522.pdf 2 'finitely generated multiplicative group'

check_page hata-1993.pdf 2 'Theorem 1.1. For any'
check_page hata-1993.pdf 5 'Lemma 2.2. There exists'
check_page hata-1993.pdf 10 'qn = Dn vn'

pdftotext -f 3 -l 3 -layout bailey-borwein-plouffe-1997.pdf "$TMP/bbp-page-3.txt"
test -s "$TMP/bbp-page-3.txt"
grep -Eq 'Theorem[[:space:]]+1\.' "$TMP/bbp-page-3.txt"
grep -Fq '(1.2)' "$TMP/bbp-page-3.txt"

grep -nF 'theorem mem_sparse_short_sector_iff' T56LagSectorAudit.lean | grep -Eq '^69:'
grep -nF 'theorem sparseShortRepunitIncidenceBound_iff_quantifiers' T56LagSectorAudit.lean | grep -Eq '^126:'
grep -nF 'theorem mem_positiveFejerFrequencies_iff' T58TriangularFejerAudit.lean | grep -Eq '^48:'
grep -nF 'theorem mem_shortRectangle_iff' T58TriangularFejerAudit.lean | grep -Eq '^53:'
grep -nF 'Status: `proof sketch`' T60_VAALER_IRRATIONALITY_FRONTIER.md | grep -Eq '^3:'
grep -nF '(SI_pi)' T60_VAALER_IRRATIONALITY_FRONTIER.md | grep -Eq '^495:'
grep -nF 'theorem mem_residualShortRectangle_iff' T61VaalerAnalytic.lean | grep -Eq '^1760:'
grep -nF 'theorem vaalerAnalyticCertificate_proved' T61VaalerAnalytic.lean | grep -Eq '^1886:'
grep -nF 'def SignedStructuredDenominatorPremise' T61VaalerAnalytic.lean | grep -Eq '^2081:'
grep -nF 'theorem signedStructuredDenominatorPremise_iff_quantifiers' T61VaalerAnalytic.lean | grep -Eq '^2087:'

printf '%s\n' 'T79 hash and locator replay: PASS'
