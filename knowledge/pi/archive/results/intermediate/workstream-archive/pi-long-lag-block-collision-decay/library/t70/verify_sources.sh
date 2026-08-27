#!/bin/sh
set -eu

sha256sum -c SOURCE_SHA256SUMS

tmp_dir="$(mktemp -d)"
trap 'rm -rf "$tmp_dir"' EXIT HUP INT TERM

pdftotext -layout aistleitner-fukuyama-1403.1630v2.pdf "$tmp_dir/af.txt"
pdftotext -layout technau-zafeiropoulos-1812.06293v2.pdf "$tmp_dir/tz.txt"
pdftotext -layout garaev-1810.06341v1.pdf "$tmp_dir/garaev.txt"
pdftotext -layout kerr-1302.4170v1.pdf "$tmp_dir/kerr.txt"
pdftotext -layout baker-munsch-shparlinski-2103.12659v2.pdf "$tmp_dir/bms.txt"
pdftotext -layout bombieri-iwaniec-1986.pdf "$tmp_dir/bi.txt"

grep -F "Theorem 4. For any N" "$tmp_dir/af.txt" >/dev/null
grep -F "Theorem 1. Let" "$tmp_dir/tz.txt" >/dev/null
grep -F "Theorem 1. Let M" "$tmp_dir/garaev.txt" >/dev/null
grep -F "Theorem 2. For g" "$tmp_dir/kerr.txt" >/dev/null
grep -F "Theorem 1.1. With" "$tmp_dir/bms.txt" >/dev/null
grep -F "LEMMA 2.4" "$tmp_dir/bi.txt" >/dev/null
grep -F "integral values" "$tmp_dir/bi.txt" >/dev/null

grep -F "theorem aggregateEnergy_literal" T69_KERNEL_INTERFACE.lean >/dev/null
grep -F "theorem literal_combinedDiscrepancy_implies_aggregate" T69_KERNEL_INTERFACE.lean >/dev/null
grep -F "theorem literal_aggregate_failure_implies_halfArcExcessCertificate" T69_KERNEL_INTERFACE.lean >/dev/null
grep -F "theorem literal_T68_uniformDiscrepancy_implies_aggregate" T69_KERNEL_INTERFACE.lean >/dev/null

printf '%s\n' "All hashes and text-extractable locator markers verified."
printf '%s\n' "Manual scan check: Bombieri-Iwaniec physical PDF pages 5-7."
