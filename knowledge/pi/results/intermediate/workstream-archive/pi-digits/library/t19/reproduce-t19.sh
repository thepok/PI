#!/usr/bin/env bash
set -euo pipefail

usage() {
  printf 'Usage: %s fetch OUTPUT_DIR | verify\n' "$0" >&2
  exit 2
}

if [[ ${1:-} == verify ]]; then
  cd "$(dirname "$0")"
  sha256sum -c HASHES.sha256
  exit
fi

[[ ${1:-} == fetch && -n ${2:-} ]] || usage
out=$2
mkdir -p "$out"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
agent='AllMath-T19-literature-audit/1.0'
bundle_started=$(date -u +%Y-%m-%dT%H:%M:%SZ)

download() {
  local name=$1
  local url=$2
  curl -fL --retry 3 -A "$agent" -o "$out/$name.pdf" "$url"
  pdftotext -layout "$out/$name.pdf" "$out/$name.txt"
}

download stoneham-1983-pi-approximations \
  'https://www.impan.pl/shop/publication/transaction/download/product/103744?download.pdf'
download barral-loiseau-2011-local-independence \
  'https://export.arxiv.org/pdf/1004.3713'
download almkvist-krattenthaler-petersson-2003-pi-formulas \
  'https://export.arxiv.org/pdf/math/0110238'
download aretxabaleta-et-al-2020-galperin-billiards \
  'https://export.arxiv.org/pdf/1712.06698v3'
download borwein-borwein-galway-2004-machin-exclusion \
  'https://www.cambridge.org/core/services/aop-cambridge-core/content/view/BB7919C8E1AE66878AE8D7BC7F0EBFA3/S0008414X0003385Xa.pdf/div-class-title-finding-and-excluding-span-class-italic-b-span-ary-machin-type-individual-digit-formulae-div.pdf'

crossref_urls=(
  'https://api.crossref.org/works?query.bibliographic=pi%20decimal%20digit%20occurrence&rows=20&select=DOI,title,author,published,URL,type'
  'https://api.crossref.org/works?query.bibliographic=pi%20decimal%20recurrence%20nonzero%20digits&rows=20&select=DOI,title,author,published,URL,type'
  'https://api.crossref.org/works?query.bibliographic=pi%20factor%20complexity%20decimal%20expansion&rows=20&select=DOI,title,author,published,URL,type'
  'https://api.crossref.org/works?query.bibliographic=pi%20nth%20decimal%20digit%20algorithm&rows=20&select=DOI,title,author,published,URL,type'
  'https://api.crossref.org/works?query.bibliographic=pi%20normality%20dynamical%20system&rows=20&select=DOI,title,author,published,URL,type'
)

openalex_urls=(
  'https://api.openalex.org/works?search=pi%20decimal%20digit%20occurrence&per-page=25&select=id,doi,title,publication_year,type,primary_location,open_access'
  'https://api.openalex.org/works?search=pi%20decimal%20recurrence%20nonzero%20digits&per-page=25&select=id,doi,title,publication_year,type,primary_location,open_access'
  'https://api.openalex.org/works?search=pi%20factor%20complexity%20decimal%20expansion&per-page=25&select=id,doi,title,publication_year,type,primary_location,open_access'
  'https://api.openalex.org/works?search=pi%20nth%20decimal%20digit%20algorithm&per-page=25&select=id,doi,title,publication_year,type,primary_location,open_access'
  'https://api.openalex.org/works?search=pi%20normality%20dynamical%20system&per-page=25&select=id,doi,title,publication_year,type,primary_location,open_access'
)

arxiv_urls=(
  'https://export.arxiv.org/api/query?search_query=all:%22digits%20of%20pi%22&start=0&max_results=50'
  'https://export.arxiv.org/api/query?search_query=all:%22normality%20of%20pi%22&start=0&max_results=50'
  'https://export.arxiv.org/api/query?search_query=all:%22factor%20complexity%22%20AND%20all:pi&start=0&max_results=50'
  'https://export.arxiv.org/api/query?search_query=all:%22non-zero%20digits%22%20AND%20all:pi&start=0&max_results=50'
  'https://export.arxiv.org/api/query?search_query=all:%22nth%20decimal%20digit%22%20AND%20all:pi&start=0&max_results=50'
)

bundle_json() {
  local db=$1
  local output=$2
  shift 2
  local i=0 url body item
  for url in "$@"; do
    body="$tmp/$db-body-$i"
    item="$tmp/$db-item-$i.json"
    curl -fsSL --retry 3 -A "$agent" "$url" > "$body"
    jq -n --arg url "$url" --slurpfile response "$body" \
      '{url: $url, response: $response[0]}' > "$item"
    i=$((i + 1))
  done
  jq -s --arg database "$db" --arg bundle_started_at "$bundle_started" \
    '{database: $database, bundle_started_at: $bundle_started_at,
      scope_note: "Each query is bounded by its rows/per-page parameter. Responses are mutable discovery records, not theorem evidence or proof of absence.",
      queries: .}' "$tmp/$db"-item-*.json > "$out/$output"
}

bundle_xml() {
  local db=$1
  local output=$2
  shift 2
  local i=0 url body item
  for url in "$@"; do
    body="$tmp/$db-body-$i"
    item="$tmp/$db-item-$i.json"
    curl -fsSL --retry 3 -A "$agent" "$url" > "$body"
    jq -n --arg url "$url" --rawfile response "$body" \
      '{url: $url, response_xml: $response}' > "$item"
    i=$((i + 1))
  done
  jq -s --arg database "$db" --arg bundle_started_at "$bundle_started" \
    '{database: $database, bundle_started_at: $bundle_started_at,
      scope_note: "Each query is bounded by max_results=50. Responses are mutable discovery records, not theorem evidence or proof of absence.",
      queries: .}' "$tmp/$db"-item-*.json > "$out/$output"
}

bundle_json crossref search-crossref.json "${crossref_urls[@]}"
bundle_json openalex search-openalex.json "${openalex_urls[@]}"
bundle_xml arxiv search-arxiv.json "${arxiv_urls[@]}"

sha256sum "$out"/*.pdf "$out"/*.txt "$out"/search-*.json
