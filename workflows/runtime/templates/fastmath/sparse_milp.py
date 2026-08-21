#!/usr/bin/env python3
"""Sparse SciPy/HiGHS starting point with a known-answer self-test.

Use this when Python should describe the model but compiled HiGHS should do the
search. Replace build_model and verify_witness; never accept a solver vector
without the independent verifier.
"""

from __future__ import annotations

import argparse
import json

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_array


def build_model() -> tuple[np.ndarray, coo_array, np.ndarray, np.ndarray]:
    # Minimum binary cover: x0+x1>=1, x1+x2>=1, x0+x2>=1. Optimum is 2.
    objective = np.ones(3)
    matrix = coo_array(
        (
            np.ones(6),
            (
                np.asarray([0, 0, 1, 1, 2, 2], dtype=np.int32),
                np.asarray([0, 1, 1, 2, 0, 2], dtype=np.int32),
            ),
        ),
        shape=(3, 3),
    ).tocsr()
    return objective, matrix, np.ones(3), np.full(3, np.inf)


def verify_witness(vector: np.ndarray) -> bool:
    chosen = np.rint(vector).astype(int)
    return (
        np.all((chosen == 0) | (chosen == 1))
        and chosen[0] + chosen[1] >= 1
        and chosen[1] + chosen[2] >= 1
        and chosen[0] + chosen[2] >= 1
        and chosen.sum() == 2
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--time-limit", type=float, default=60.0)
    args = parser.parse_args()
    objective, matrix, lower, upper = build_model()
    result = milp(
        c=objective,
        integrality=np.ones(len(objective)),
        bounds=Bounds(np.zeros(len(objective)), np.ones(len(objective))),
        constraints=LinearConstraint(matrix, lower, upper),
        options={"time_limit": args.time_limit, "presolve": True},
    )
    valid = bool(result.x is not None and verify_witness(result.x))
    payload = {
        "claim_label": "experiment",
        "status": int(result.status),
        "message": str(result.message),
        "objective": float(result.fun) if result.fun is not None else None,
        "independent_witness_valid": valid,
    }
    print(json.dumps(payload, sort_keys=True))
    if args.self_test and not (
        bool(result.success) and float(result.fun) == 2.0 and valid
    ):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
