#!/bin/sh
set -eu

sha256sum -c SOURCE_SHA256SUMS

test "$(pdfinfo bailey-crandall-2001-random-character.pdf | grep '^Pages:' | tr -s ' ' | cut -d' ' -f2)" = "25"
test "$(pdfinfo chernov-kleinbock-1999-arxiv.pdf | grep '^Pages:' | tr -s ' ' | cut -d' ' -f2)" = "23"
test "$(pdfinfo fukuyama-2008-discrepancy.pdf | grep '^Pages:' | tr -s ' ' | cut -d' ' -f2)" = "13"
test "$(pdfinfo philipp-1975-lacunary.pdf | grep '^Pages:' | tr -s ' ' | cut -d' ' -f2)" = "6"
test "$(pdfinfo rudnick-zaharescu-1999-pair-correlation.pdf | grep '^Pages:' | tr -s ' ' | cut -d' ' -f2)" = "11"
test "$(pdfinfo rousseau-2021-longest-common-substring.pdf | grep '^Pages:' | tr -s ' ' | cut -d' ' -f2)" = "20"

printf '%s\n' 'source hashes and page counts verified'
