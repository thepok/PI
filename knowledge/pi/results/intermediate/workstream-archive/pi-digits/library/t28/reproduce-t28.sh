#!/usr/bin/env sh
set -eu

here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
mode=${1:-verify}

fetch_url() {
  curl -L --fail --silent --show-error \
    --retry 4 --retry-delay 3 --retry-all-errors \
    --user-agent "AllMath-T28-literature-audit/1.0" \
    "$1" -o "$2"
}

if [ "$mode" = verify ]; then
  cd "$here"
  sha256sum -c HASHES.sha256
  sha256sum -c DEPENDENCIES.sha256
elif [ "$mode" = fetch ]; then
  out=${2:?usage: ./reproduce-t28.sh fetch OUTPUT_DIRECTORY}
  if [ -e "$out" ]; then
    printf '%s\n' "output path already exists: $out" >&2
    exit 2
  fi
  mkdir "$out"

  fetch_url \
    "https://www.renyi.hu/~p_erdos/1955-06.pdf" \
    "$out/erdos-gal-1955-part1.pdf"
  fetch_url \
    "https://www.renyi.hu/~p_erdos/1955-07.pdf" \
    "$out/erdos-gal-1955-part2.pdf"
  fetch_url \
    "https://www.impan.pl/shop/publication/transaction/download/product/100600?download.pdf" \
    "$out/philipp-1975-lacunary.pdf"
  fetch_url \
    "https://da.lib.kobe-u.ac.jp/da/kernel/90003836/90003836.pdf" \
    "$out/fukuyama-2008-geometric-discrepancy.pdf"

  pdftotext -layout "$out/erdos-gal-1955-part1.pdf" \
    "$out/erdos-gal-1955-part1.txt"
  pdftotext -layout "$out/erdos-gal-1955-part2.pdf" \
    "$out/erdos-gal-1955-part2.txt"
  pdftotext -layout "$out/philipp-1975-lacunary.pdf" \
    "$out/philipp-1975-lacunary.txt"
  pdftotext -layout "$out/fukuyama-2008-geometric-discrepancy.pdf" \
    "$out/fukuyama-2008-geometric-discrepancy.txt"

  fetch_url \
    "https://api.crossref.org/works?query.bibliographic=lacunary%20exponential%20sums%20geometric%20progressions%20discrepancy&rows=20&select=DOI,title,author,published,URL" \
    "$out/search-crossref.json"
  fetch_url \
    "https://api.crossref.org/works?query.title=law%20of%20the%20iterated%20logarithm%20discrepancies%20theta%20n%20x&rows=20&select=DOI,title,author,published,URL" \
    "$out/search-crossref-title.json"
  fetch_url \
    "https://api.openalex.org/works?search=lacunary%20exponential%20sums%20geometric%20progressions%20discrepancy&per-page=25&select=id,doi,title,publication_year,primary_location,authorships" \
    "$out/search-openalex.json"

  cd "$out"
  sha256sum -c "$here/FETCH_STABLE_HASHES.sha256"
  sha256sum ./*
else
  printf '%s\n' "unknown mode: $mode" >&2
  exit 2
fi
