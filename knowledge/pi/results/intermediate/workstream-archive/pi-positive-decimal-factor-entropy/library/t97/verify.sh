#!/usr/bin/env sh
set -eu

HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$HERE"

printf '%s  %s\n' \
  'a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6' \
  'pi-positive-decimal-factor-entropy.txt' | sha256sum -c -

if [ ! -f SHA256SUMS ]; then
  printf '%s\n' 'required SHA256SUMS manifest is missing' >&2
  exit 1
fi
sha256sum -c SHA256SUMS

tmp_json=$(mktemp)
tmp_csv=$(mktemp)
trap 'rm -f "$tmp_json" "$tmp_csv"' EXIT HUP INT TERM

python3 -B ./t97_long_sector_census.py \
  --verify ./census_results.json \
  --output "$tmp_json" \
  --summary-output "$tmp_csv" \
  --quiet
