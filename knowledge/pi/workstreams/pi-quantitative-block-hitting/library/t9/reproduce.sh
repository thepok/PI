#!/bin/sh
set -eu

HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
ROOT=$(CDPATH= cd -- "$HERE/../../../.." && pwd)
MANIFEST="$HERE/retrieval_manifest.json"

usage() {
  printf '%s\n' "usage: $0 verify | fetch NEW_OUTPUT_DIRECTORY"
  exit 2
}

verify_dependencies() {
  jq -r '(.canonical_target | [.sha256, .path_from_workspace] | @tsv),
         (.dependencies[] | [.sha256, .path_from_workspace] | @tsv)' "$MANIFEST" |
  while IFS="$(printf '\t')" read -r expected relative; do
    actual=$(sha256sum "$ROOT/$relative" | cut -d ' ' -f 1)
    test "$actual" = "$expected" || {
      printf '%s\n' "dependency hash mismatch: $relative" >&2
      exit 1
    }
    printf '%s\n' "dependency OK: $relative"
  done
}

verify_retained() {
  cd "$HERE"
  sha256sum -c HASHES.sha256
  verify_dependencies
}

fetch_all() {
  test "$#" -eq 1 || usage
  out=$1
  test ! -e "$out" || {
    printf '%s\n' "output path already exists: $out" >&2
    exit 1
  }
  mkdir -p "$out/sources" "$out/text" "$out/searches"

  jq -r '.sources[] | [.id, .url, .file, .sha256, .text_file, .pdftotext_sha256] | @tsv' "$MANIFEST" |
  while IFS="$(printf '\t')" read -r id url pdf_relative pdf_hash text_relative text_hash; do
    pdf_name=$(basename "$pdf_relative")
    text_name=$(basename "$text_relative")
    if test "$id" = "SAL2008"; then
      curl --fail --location --retry 4 --retry-delay 2 --user-agent "Mozilla/5.0" \
        --referer "https://www.mathnet.ru/eng/rm9175" "$url" -o "$out/sources/$pdf_name"
    else
      curl --fail --location --retry 4 --retry-delay 2 "$url" -o "$out/sources/$pdf_name"
    fi
    actual_pdf=$(sha256sum "$out/sources/$pdf_name" | cut -d ' ' -f 1)
    test "$actual_pdf" = "$pdf_hash" || {
      printf '%s\n' "$id PDF changed: expected $pdf_hash, got $actual_pdf" >&2
      exit 1
    }
    pdftotext -layout "$out/sources/$pdf_name" "$out/text/$text_name"
    actual_text=$(sha256sum "$out/text/$text_name" | cut -d ' ' -f 1)
    test "$actual_text" = "$text_hash" || {
      printf '%s\n' "$id extraction changed: expected $text_hash, got $actual_text" >&2
      exit 1
    }
    printf '%s\n' "$id source and extraction OK"
  done

  jq -r '.searches[] | [.retained_response, .url] | @tsv' "$MANIFEST" |
  while IFS="$(printf '\t')" read -r relative url; do
    name=$(basename "$relative")
    curl --fail --location --retry 4 --retry-delay 2 "$url" -o "$out/searches/$name"
  done
  sha256sum "$out"/searches/*.json > "$out/searches/FRESH_HASHES.sha256"
  printf '%s\n' "Fresh mutable search responses are in $out/searches"
}

case "${1-}" in
  verify)
    test "$#" -eq 1 || usage
    verify_retained
    ;;
  fetch)
    shift
    fetch_all "$@"
    ;;
  *) usage ;;
esac
