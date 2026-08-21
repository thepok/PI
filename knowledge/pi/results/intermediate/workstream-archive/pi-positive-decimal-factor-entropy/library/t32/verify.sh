#!/usr/bin/env bash
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$ROOT"

sha256sum -c SHA256SUMS

tmp_dir=$(mktemp -d)
trap 'rm -rf "$tmp_dir"' EXIT HUP INT TERM

pdftotext -layout sources/rudolph-1990.pdf "$tmp_dir/rudolph.txt"
grep -Fq 'THEOREM 4.9.' "$tmp_dir/rudolph.txt"
grep -Eq 'COROLLARY +4\.11\.' "$tmp_dir/rudolph.txt"
grep -Fq 'LEMMA 2.2.' "$tmp_dir/rudolph.txt"
grep -Eq 'COROLLARY +3\.2\.' "$tmp_dir/rudolph.txt"
grep -Fq 'LEMMA 3.5.' "$tmp_dir/rudolph.txt"
grep -Eq 'COROLLARY +4\.10\.' "$tmp_dir/rudolph.txt"
grep -Fq 'inverse limit' "$tmp_dir/rudolph.txt"
grep -Fq 'GCD(u, v) = 1' "$tmp_dir/rudolph.txt"
grep -Fq 'u, v' "$tmp_dir/rudolph.txt"
grep -Fq 'm 2 - m 1 n 2' "$tmp_dir/rudolph.txt"

pdftotext -layout sources/furstenberg-1967.pdf "$tmp_dir/furstenberg.txt"
grep -Fq 'Definition IV.1.' "$tmp_dir/furstenberg.txt"
grep -Fq 'Otherwise, E is non-lacunary.' "$tmp_dir/furstenberg.txt"

grep -Fq 'id="Abs1"' sources/johnson-1992-publisher.html
grep -Fq 'nonlacunary subsemigroup of the natural numbers' sources/johnson-1992-publisher.html
grep -Fq 'if any element in' sources/johnson-1992-publisher.html
grep -Fq 'is Lebesgue' sources/johnson-1992-publisher.html

printf '%s\n' 'T32 source hashes and locators verified.'
