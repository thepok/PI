#!/bin/sh
set -eu

cd "$(dirname "$0")"
sha256sum -c SHA256SUMS

expected=a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6
actual=$(sha256sum pi-positive-decimal-factor-entropy.txt | cut -d ' ' -f 1)
test "$actual" = "$expected"

printf '%s\n' 'T54 artifact integrity checks passed.'
