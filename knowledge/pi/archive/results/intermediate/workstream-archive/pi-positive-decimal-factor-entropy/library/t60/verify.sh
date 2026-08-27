#!/bin/sh
set -eu

expected="a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6"
actual="$(sha256sum pi-positive-decimal-factor-entropy.txt | cut -d ' ' -f 1)"
test "$actual" = "$expected"
sha256sum -c SHA256SUMS
python3 t60_replay.py --write replay.json >/dev/null
cmp replay.json replay_expected.json
rm replay.json
printf '%s\n' "T60 hashes and replay verified"
