#!/bin/sh
set -eu

artifact_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$artifact_dir"

usage() {
  printf '%s\n' "usage: $0 verify | extract OUTPUT_DIR | retained-searches OUTPUT_DIR | search OUTPUT_DIR | fetch OUTPUT_DIR" >&2
  exit 2
}

require_new_dir() {
  if [ -e "$1" ]; then
    printf '%s\n' "output path already exists: $1" >&2
    exit 2
  fi
  mkdir -p "$1"
}

mode=${1:-}
case "$mode" in
  verify)
    [ "$#" -eq 1 ] || usage
    sha256sum -c HASHES.sha256
    tmp=$(mktemp -d)
    trap 'rm -rf "$tmp"' EXIT HUP INT TERM
    tar -xzf bounded-searches.tar.gz -C "$tmp"
    (cd "$tmp" && sha256sum -c SEARCH_HASHES.sha256)
    ;;
  extract)
    [ "$#" -eq 2 ] || usage
    out=$2
    require_new_dir "$out"
    pdftotext -layout furstenberg-1967-disjointness.pdf "$out/furstenberg-1967-disjointness.txt"
    pdftotext -layout rudolph-1990-times2-times3.pdf "$out/rudolph-1990-times2-times3.txt"
    pdftotext -layout hochman-2022-host-equidistribution-v2.pdf "$out/hochman-2022-host-equidistribution-v2.txt"
    pdftotext -layout algom-2020-simultaneous-host-v1.pdf "$out/algom-2020-simultaneous-host-v1.txt"
    (
      cd "$out"
      sha256sum -c - <<'EOF'
3e5a82a8c8861c51eca6931e2f39f22f6466427d597caac2d3e0583517ac5c4b  furstenberg-1967-disjointness.txt
0ad910b573346e14853030e0124f3c239eb7dd8532f542e9f7983b4928907de7  rudolph-1990-times2-times3.txt
013c44f31d7a2be36d09d060cf49ab2722c70dcf74989b885ba9d21bf1c080e5  hochman-2022-host-equidistribution-v2.txt
6f3e07aa72818c7a92cd04f424c6380d51a009cb7dd80c6ed8ea84853344b4a0  algom-2020-simultaneous-host-v1.txt
EOF
    )
    ;;
  retained-searches)
    [ "$#" -eq 2 ] || usage
    out=$2
    require_new_dir "$out"
    tar -xzf bounded-searches.tar.gz -C "$out"
    (cd "$out" && sha256sum -c SEARCH_HASHES.sha256)
    ;;
  search)
    [ "$#" -eq 2 ] || usage
    out=$2
    require_new_dir "$out"
    curl --retry 4 --retry-delay 2 -fL "https://api.openalex.org/works?search=Furstenberg%20times%20p%20times%20q%20closed%20invariant%20set&per-page=20&select=id,doi,title,publication_year,primary_location,open_access" -o "$out/openalex-closed-set.json"
    curl --retry 4 --retry-delay 2 -fL "https://api.openalex.org/works?search=times%20p%20times%20q%20invariant%20measure%20entropy%20Rudolph%20Johnson&per-page=20&select=id,doi,title,publication_year,primary_location,open_access" -o "$out/openalex-measure-rigidity.json"
    curl --retry 4 --retry-delay 2 -fL "https://api.openalex.org/works?search=simultaneous%20Host%20equidistribution%20theorem&per-page=20&select=id,doi,title,publication_year,primary_location,open_access" -o "$out/openalex-simultaneous-host.json"
    curl --retry 4 --retry-delay 2 -fL "https://api.crossref.org/works?query.bibliographic=Furstenberg%20times%20p%20times%20q%20closed%20invariant%20set&rows=20&select=DOI,title,author,published,URL,type" -o "$out/crossref-closed-set.json"
    curl --retry 4 --retry-delay 2 -fL "https://api.crossref.org/works?query.bibliographic=Rudolph%20Johnson%20invariant%20measure%20entropy%20times%20p%20times%20q&rows=20&select=DOI,title,author,published,URL,type" -o "$out/crossref-measure-rigidity.json"
    curl --retry 4 --retry-delay 2 -fL "https://api.crossref.org/works?query.bibliographic=simultaneous%20Host%20equidistribution%20theorem&rows=20&select=DOI,title,author,published,URL,type" -o "$out/crossref-simultaneous-host.json"
    sha256sum "$out"/*.json
    ;;
  fetch)
    [ "$#" -eq 2 ] || usage
    out=$2
    require_new_dir "$out"
    curl -k -fL "https://mathweb.ucsd.edu/~asalehig/F_Disjointness.pdf" -o "$out/furstenberg-1967-disjointness.pdf"
    curl -fL "https://www.cambridge.org/core/services/aop-cambridge-core/content/view/64243AD8323B37089540F911F8CC77EB/S0143385700005629a.pdf/2-and-3-invariant-measures-and-entropy.pdf" -o "$out/rudolph-1990-times2-times3.pdf"
    curl -fL "https://arxiv.org/pdf/2103.08938v2" -o "$out/hochman-2022-host-equidistribution-v2.pdf"
    curl -fL "https://arxiv.org/pdf/1904.12506v1" -o "$out/algom-2020-simultaneous-host-v1.pdf"
    curl -fL "https://link.springer.com/article/10.1007/BF02808018" -o "$out/johnson-1992-publisher.html"
    curl -fL "https://api.crossref.org/works/10.1007/BF02808018" -o "$out/johnson-1992-crossref.json"
    curl -fL "https://link.springer.com/article/10.1007/BF02761660" -o "$out/host-1995-publisher.html"
    curl -fL "https://api.crossref.org/works/10.1007/BF02761660" -o "$out/host-1995-crossref.json"
    sha256sum "$out"/*
    ;;
  *)
    usage
    ;;
esac
