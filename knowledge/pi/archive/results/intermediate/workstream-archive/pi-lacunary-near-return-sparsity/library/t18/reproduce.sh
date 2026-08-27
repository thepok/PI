#!/usr/bin/env bash
set -euo pipefail

here="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
cd "$here"

printf '%s  %s\n' \
  '3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5' \
  'zeilberger-zudilin-2020.pdf' \
  '49ca4907538e4ccea23cee27f051f5b33832ed2cf3e3093b4aab58a13c814a68' \
  'zeilberger-zudilin-2020.txt' | sha256sum -c -

if [[ "$#" -eq 2 ]]; then
  printf '%s  %s\n' \
    'cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8' "$1" \
    '14ae452f34068dd78877054e231c58af02c2563cd755f0ee4edc0ff0ebeeda13' "$2" |
    sha256sum -c -
elif [[ "$#" -ne 0 ]]; then
  printf 'usage: %s [CANONICAL_STATEMENT T13_LEAN_FILE]\n' "$0" >&2
  exit 2
fi

python3 - <<'PY'
def density(D, d):
    for _ in range(d):
        D = 8 * D * D
    return D

def threshold(D, K, q, d):
    if d == 0:
        return K
    R = threshold(8 * D * D, K, q + 1, d - 1)
    return max(8 * D * D, 16 * (1 + q + R) * D * D)

for A in (1, 2, 5):
    for n in (1, 3):
        D0 = 2**17 * A*A * n*n
        for d in range(6):
            closed_D = 2**(20 * 2**d - 3) * (A*n)**(2**(d + 1))
            assert density(D0, d) == closed_D
            lambdas = [16 * density(D0, i)**2 for i in range(d)]
            C = 1
            E = 0
            prefix = 1
            for i, value in enumerate(lambdas):
                C *= value
                prefix *= value
                E += (i + 2) * prefix
            for K in (1, 2, 7):
                assert threshold(D0, K, 1, d) == C*K + E

print('closed-form recursion checks passed')
PY

printf '%s\n' 'T18 retained-source and arithmetic checks passed'
