#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 t38_experiment.py replay --directory .
