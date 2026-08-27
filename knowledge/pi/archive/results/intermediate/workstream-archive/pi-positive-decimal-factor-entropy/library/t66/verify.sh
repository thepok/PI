#!/bin/sh
set -eu
sha256sum -c SHA256SUMS
python3 ./t66_experiment.py replay --directory .
