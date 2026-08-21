#!/bin/sh
set -eu

sha256sum -c <<'EOF'
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3  CANONICAL_STATEMENT.txt
2f18966e04e00eb657d4a517d31281f9e8eafae4a6365bcf0985b94711e1e358  T29_KERNEL_INTERFACE.lean
88b17a0be03261d3b53fe64d09452491920ca3550194d4bd2efa22f0ca2519e4  T87_KERNEL_SPECIALIZATION.lean
0481de1cbdb9c8466efa6bff5ceb4ceb684536484ecdf6429f062ab2adc2ab90  T90_KERNEL_SPECIALIZATION.lean
68ed33e72b941db6c25664dcfdcf4d969d197ceee46e90120f898354df748b61  PRIOR_PINNED_CORPUS.tar
3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5  zeilberger-zudilin-2020.pdf
e395e4698837950b683362558441e1e75298ad28cb0cc8cf260a556c93093574  matveev-2000.pdf
3c809fcadaddbc08f57045e4f55562c8a379b5fa33d7e83046b63a9c14766e8f  evertse-schlickewei-schmidt-math0409604.pdf
60053bb3ce7ddc002e24367b00fa43fee3b554f7fce6287b75aa7a61e0459c1c  garaev-1810.06341v1.pdf
4c2990ec21a5962bfee2f7d603074d71b987e1dddaa1a885b3c55934f1749eea  aistleitner-fukuyama-1403.1630v2.pdf
b779dfb61606b3991a86fe6dc3a4d1c7d1c45a81c9b746c9d799178bb00195d7  chernov-kleinbock-math9912178v1.pdf
33a5d518ce974021dd672af2d5d5b8c1e830a1af4328a2f7148e509513cb955e  technau-zafeiropoulos-1812.06293v2.pdf
8c482ef709857877ea22e4bdf9ff3fa3673dd8c20ba9f9026e3a1bded1a6704d  bailey-crandall-2001.pdf
EOF

tmp_dir="$(mktemp -d)"
trap 'rm -rf "$tmp_dir"' EXIT HUP INT TERM

mkdir "$tmp_dir/prior"
tar -xf PRIOR_PINNED_CORPUS.tar -C "$tmp_dir/prior"
(
  cd "$tmp_dir/prior"
  sha256sum -c <<'EOF'
ab5bcb0ebd5eb590c849cc6620d4bdd764415ef9de88f2881d8ce48429715406  t5/APPLICABILITY_MATRIX.md
b468e509c4aa3b8bad7d833458578f94b4a5f0d95c53567a69a69e1598c525ae  t21/T21_APPLICABILITY_AUDIT.md
33521ed540153b2483b60d37edea6dd9b250dd304b56b4712d40e132e10ace8e  t63/T63ExactFiniteFourthMoment.lean
65936350dad95e2b29435633d6ceabd5a5fc79ce9ac7ca19737126dbd1a9e0e4  t68/T68HalfArcDiscrepancy.lean
6f7f2260af4904dcea7b75c22833513313faa6e1a3b02cefd5c116b14450af17  t70/T70_SOURCE_PINNED_APPLICABILITY_AUDIT.md
cd01d86a1b3e98791fd3e20a1fe69a612e0fc07e917d52e0f82e239d33dc2279  t79/T79HousekeepingBridges.lean
4d422c17fb22b2d24ba934ca667ab7e43508a4bcb8ae96158cf5c7ada024caa1  notes/t80/T80_POSITIVE_WEIGHTED_CAUCHY_BARRIER.md
6a85bb7cece8c58cc945fc850b0257a646211ce31215b8cbeda3cbd020337d76  t81/T81AdjacentIndexPairing.lean
1f7065745b8c35ea8c3a1b9cb44c1ec436bb49a84074715cfe56f779207ec878  notes/t82/T82_SHIFT_SUMMATION_BY_PARTS.md
421d1d304c7ed7da61e9a7fa34eb4d80c29e76c2affa2cbd2a46cf12d11447ff  t85/REPLAY.md
7c2298029c4f66b613d03405caefa60567e9b1a34632336e67e6cf3bfff12f1e  notes/t13/T13_MANY_ANCHOR_INCIDENCE.md
e92c9cfcfae6a00842fc661f4bdcf827ddf076fc4a655d3a7cc60a380f26bfb1  notes/t35/T35_SUBCRITICAL_CANCELLATION_SAVING.md
e3ef74182bcd0996f134e0a1c4ea7d8e1fbd762aa7e0f80cf940277d244eac41  notes/t47/T47_FIXED_PI_PRIMITIVE_OFFDIAGONAL.md
d5b6032a52f4bbe631eb89b8ba89c40cea0d34001d4c361085ea729c1ef82233  notes/t92/T92_VARIABLE_PHASE_CORRELATION.md
fbc6a0dd2c3b33be24dd539a61ec69cdf554751761398a78190b0ec93a1c1b9f  notes/t95/T95_EVENTUAL_VARIABLE_PHASE.md
37ca19e081316174b5e5ebdc829ae14ba1ae63f63b4cead1ffdb9a97cf89a3a2  notes/t97/T97_EXACT_VARIABLE_PHASE_BRIDGE.md
96818d8cbcf9c132ac4f666429ede133d997b6ae7d49a29f30e027ed9eded9e8  .research/orchestrator-escalations.json
EOF
)

extract_and_require() {
  pdf="$1"
  marker="$2"
  out="$tmp_dir/$(basename "$pdf").txt"
  pdftotext -layout "$pdf" "$out"
  grep -F "$marker" "$out" >/dev/null
}

grep -F 'def inclusiveFrequencies' T29_KERNEL_INTERFACE.lean >/dev/null
grep -F 'def translatedCanonicalBlocks' T29_KERNEL_INTERFACE.lean >/dev/null
grep -F 'def widthWeight' T29_KERNEL_INTERFACE.lean >/dev/null
grep -F 'def widthWeightedSquareFunction' T29_KERNEL_INTERFACE.lean >/dev/null
grep -F 'def WidthWeightedSquareFunctionAt' T29_KERNEL_INTERFACE.lean >/dev/null
grep -F 'def WidthWeightedSquareFunction' T29_KERNEL_INTERFACE.lean >/dev/null
grep -F 'theorem not_arithmeticExcluded_eight_one' T87_KERNEL_SPECIALIZATION.lean >/dev/null
grep -F 'theorem blockRecordDomain_eight_one_eq_orientations' T90_KERNEL_SPECIALIZATION.lean >/dev/null
grep -F 'theorem widthWeightedSquareFunction_eight_one_pi_eq_coreSum' T90_KERNEL_SPECIALIZATION.lean >/dev/null
grep -F 'def CORR_pi' T90_KERNEL_SPECIALIZATION.lean >/dev/null
grep -F 'def FixedPiDyadicFourthMomentBound' "$tmp_dir/prior/t63/T63ExactFiniteFourthMoment.lean" >/dev/null
grep -F 'def UniformShiftedHalfArcDiscrepancy' "$tmp_dir/prior/t68/T68HalfArcDiscrepancy.lean" >/dev/null
grep -F '## 7. Terminal mismatch' "$tmp_dir/prior/t70/T70_SOURCE_PINNED_APPLICABILITY_AUDIT.md" >/dev/null
grep -F 'todo:theory-pi-long-lag-block-collision-decay:t78' "$tmp_dir/prior/.research/orchestrator-escalations.json" >/dev/null
grep -F 'todo:theory-pi-positive-decimal-factor-entropy:t93' "$tmp_dir/prior/.research/orchestrator-escalations.json" >/dev/null

extract_and_require zeilberger-zudilin-2020.pdf 'World record.'
extract_and_require matveev-2000.pdf 'Theorem 2.1 (the main theorem).'
extract_and_require evertse-schlickewei-schmidt-math0409604.pdf 'Theorem 1.1.'
extract_and_require garaev-1810.06341v1.pdf 'Theorem 1. Let M'
extract_and_require aistleitner-fukuyama-1403.1630v2.pdf 'Theorem 4. For any N'
extract_and_require chernov-kleinbock-math9912178v1.pdf 'Theorem 2.1 Let'
extract_and_require technau-zafeiropoulos-1812.06293v2.pdf 'Theorem 1. Let'
extract_and_require bailey-crandall-2001.pdf 'Hypothesis A.'

printf '%s\n' 'T99 source and locator replay passed.'
