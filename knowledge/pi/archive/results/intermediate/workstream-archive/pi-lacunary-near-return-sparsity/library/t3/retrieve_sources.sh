#!/usr/bin/env bash
set -euo pipefail

destination="${1:-/tmp/t3-pi-lacunary-source-check}"
mkdir -p "$destination/sources" "$destination/texts"

fetch() {
  local url="$1"
  local output="$2"
  curl -L --fail --retry 2 "$url" -o "$destination/sources/$output"
}

fetch "https://www.impan.pl/shop/publication/transaction/download/product/110756?download.pdf" \
  "rudnick-zaharescu-1999.pdf"
fetch "https://arxiv.org/pdf/math/9912103v1" \
  "rudnick-zaharescu-2002-arxiv-v1.pdf"
fetch "https://msp.org/pjm/1967/20-1/pjm-v20-n1-p12-s.pdf" \
  "philipp-1967.pdf"
fetch "https://arxiv.org/pdf/2208.04702v1" \
  "yesha-2023-arxiv-v1.pdf"
fetch "https://arxiv.org/pdf/2208.06112v2" \
  "li-liao-velani-zorin-2023-arxiv-v2.pdf"
fetch "https://arxiv.org/pdf/2304.07532v3" \
  "yuan-wang-2024-arxiv-v3.pdf"

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cp "$script_dir/SOURCE_SHA256SUMS" "$destination/SOURCE_SHA256SUMS"
cp "$script_dir/DERIVED_TEXT_SHA256SUMS" "$destination/DERIVED_TEXT_SHA256SUMS"
(
  cd "$destination"
  sha256sum --check SOURCE_SHA256SUMS

  pdftotext -layout "sources/rudnick-zaharescu-1999.pdf" \
    "texts/rudnick-zaharescu-1999.txt"
  pdftotext -layout "sources/rudnick-zaharescu-2002-arxiv-v1.pdf" \
    "texts/rudnick-zaharescu-2002-arxiv-v1.txt"
  pdftotext -layout "sources/philipp-1967.pdf" \
    "texts/philipp-1967.txt"
  pdftotext -layout "sources/yesha-2023-arxiv-v1.pdf" \
    "texts/yesha-2023-arxiv-v1.txt"
  pdftotext -layout "sources/li-liao-velani-zorin-2023-arxiv-v2.pdf" \
    "texts/li-liao-velani-zorin-2023-arxiv-v2.txt"
  pdftotext -layout "sources/yuan-wang-2024-arxiv-v3.pdf" \
    "texts/yuan-wang-2024-arxiv-v3.txt"
  sha256sum --check DERIVED_TEXT_SHA256SUMS
)
