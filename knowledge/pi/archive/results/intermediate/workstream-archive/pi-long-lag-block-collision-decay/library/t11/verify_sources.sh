#!/bin/sh
set -eu

sha256sum -c SOURCE_SHA256SUMS

canonical_hash=$(sha256sum CANONICAL_STATEMENT.txt | cut -d ' ' -f 1)
test "$canonical_hash" = "db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3"

printf '%s\n' "source verification passed"
