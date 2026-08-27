#!/bin/sh
set -eu

sha256sum -c SOURCE_SHA256SUMS

tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT HUP INT TERM

pdftotext -layout banks-2018-beatty-zeta.pdf "$tmpdir/banks.txt"
pdftotext -layout aistleitner-hofer-larcher-2017.pdf "$tmpdir/ahl.txt"
pdftotext -layout zeilberger-zudilin-moscow-2020-9-407.pdf "$tmpdir/zz.txt"

grep -q 'Lemma 2.1' "$tmpdir/banks.txt"
grep -q 'Discrepancy and type' "$tmpdir/banks.txt"
grep -q 'Erdős–Turán inequality' "$tmpdir/ahl.txt"
grep -q 'H +1' "$tmpdir/ahl.txt"
grep -q 'World record' "$tmpdir/zz.txt"
grep -q 'irrationality measure' "$tmpdir/zz.txt"

echo 'source hashes and locator strings verified'
