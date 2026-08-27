#!/usr/bin/env sh
set -eu

here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
mode=${1:-verify}

fetch_url() {
  curl -L --fail --silent --show-error \
    --retry 4 --retry-delay 3 --retry-all-errors \
    --user-agent "AllMath-T35-literature-audit/1.0" \
    "$1" -o "$2"
}

new_directory() {
  out=$1
  if [ -e "$out" ]; then
    printf '%s\n' "output path already exists: $out" >&2
    exit 2
  fi
  mkdir "$out"
}

case "$mode" in
  verify)
    cd "$here"
    sha256sum -c HASHES.sha256
    actual=$(sha256sum pi-digits.txt | cut -d ' ' -f 1)
    expected=2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825
    test "$actual" = "$expected"
    tar -tzf bounded-searches-20260801.tar.gz
    ;;
  extract)
    out=${2:?usage: ./reproduce.sh extract OUTPUT_DIRECTORY}
    new_directory "$out"
    for pdf in "$here"/sources/*.pdf; do
      name=$(basename "$pdf" .pdf)
      pdftotext -layout "$pdf" "$out/$name.txt"
    done
    sha256sum "$out"/*
    ;;
  search)
    out=${2:?usage: ./reproduce.sh search OUTPUT_DIRECTORY}
    new_directory "$out"
    fetch_url "https://api.crossref.org/works?query.bibliographic=disjunctive%20sequence%20dense%20shift%20orbit%20base%20expansion&rows=20&select=DOI,title,author,published,URL" "$out/t20-crossref.json"
    fetch_url "https://api.openalex.org/works?search=disjunctive%20sequence%20dense%20shift%20orbit%20base%20expansion&per-page=20&select=id,doi,title,publication_year,primary_location,authorships" "$out/t20-openalex.json"
    fetch_url "https://api.crossref.org/works?query.bibliographic=Weyl%20criterion%20uniform%20distribution%20compact%20abelian%20group&rows=20&select=DOI,title,author,published,URL" "$out/t26-crossref.json"
    fetch_url "https://api.openalex.org/works?search=Weyl%20criterion%20uniform%20distribution%20compact%20abelian%20group&per-page=20&select=id,doi,title,publication_year,primary_location,authorships" "$out/t26-openalex.json"
    fetch_url "https://api.crossref.org/works?query.bibliographic=Erdos%20Turan%20inequality%20interval%20coverage%20exponential%20sum%20discrepancy&rows=20&select=DOI,title,author,published,URL" "$out/t27-t29-crossref.json"
    fetch_url "https://export.arxiv.org/api/query?search_query=all%3A%22Erdos-Turan%20inequality%22&start=0&max_results=20" "$out/t27-t29-arxiv.xml"
    fetch_url "https://api.openalex.org/works?search=empirical%20measure%20weak%20limit%20invariant%20continuous%20map%20compact&filter=is_oa:true&per-page=20&select=id,doi,title,publication_year,primary_location,authorships" "$out/t30-openalex.json"
    fetch_url "https://api.crossref.org/works?query.bibliographic=factor%20complexity%20omitted%20word%20entropy%20recurrent%20alphabet&rows=20&select=DOI,title,author,published,URL" "$out/t32-t33-crossref.json"
    fetch_url "https://api.openalex.org/works?search=factor%20complexity%20omitted%20word%20entropy%20recurrent%20alphabet&per-page=20&select=id,doi,title,publication_year,primary_location,authorships" "$out/t32-t33-openalex.json"
    sha256sum "$out"/*
    ;;
  fetch)
    out=${2:?usage: ./reproduce.sh fetch OUTPUT_DIRECTORY}
    new_directory "$out"
    fetch_url "https://zenodo.org/api/records/6995264/files/jucs_article_27272.pdf/content" "$out/hertling-1996-disjunctive.pdf"
    fetch_url "https://www.ams.org/journals/tran/1968-133-02/S0002-9947-1968-0227695-6/S0002-9947-1968-0227695-6.pdf?download=1" "$out/berg-rajagopalan-rubel-1968.pdf"
    fetch_url "https://arxiv.org/pdf/1305.2458v1" "$out/rosengarten-2013-erdos-turan.pdf"
    fetch_url "https://www.renyi.hu/~p_erdos/1955-06.pdf" "$out/erdos-gal-1955-part1.pdf"
    fetch_url "https://da.lib.kobe-u.ac.jp/da/kernel/90003836/90003836.pdf" "$out/fukuyama-2008-geometric-discrepancy.pdf"
    fetch_url "https://personalpages.manchester.ac.uk/staff/charles.walkden/ergodic-theory/ergodic_theory.pdf" "$out/walkden-ergodic-theory-notes.pdf"
    fetch_url "https://arxiv.org/pdf/1702.07698v2" "$out/mauduit-moreira-2018-complexity.pdf"
    fetch_url "http://www.scholarpedia.org/article/Symbolic_dynamics" "$out/marcus-williams-2008-symbolic-dynamics.html"
    sha256sum "$out"/*
    ;;
  *)
    printf '%s\n' "unknown mode: $mode" >&2
    exit 2
    ;;
esac
