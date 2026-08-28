#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"

g++ -O2 -std=c++20 pi_cert.cpp -lgmpxx -lgmp -o pi_cert
./pi_cert 100050 7154 > pi_cert_output.txt

g++ -O3 -std=c++20 -fopenmp -fno-fast-math -ffp-contract=off \
  -frounding-math t189_interval_cert.cpp -o t189_interval_cert
./t189_interval_cert pi_digits_cert.txt rootall > rootall_interval_output.txt
for A in 334 1334 2334 3334 4334 8334 9334; do
  OMP_NUM_THREADS="${OMP_NUM_THREADS:-5}" \
    ./t189_interval_cert pi_digits_cert.txt node "$A" > "node_A${A}.txt"
done
python3 verify_bounds.py | tee checked_sign_summary.txt
diff -u expected_summary.txt checked_sign_summary.txt
