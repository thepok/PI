#!/usr/bin/env python3
"""Self-contained integrity and arithmetic replay for T112.

Finite checks are experiments. They do not prove source theorems or any claim
about pi, C1, C2, or canonical A1.
"""

from __future__ import annotations

import cmath
import hashlib
import math
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parent

HASHES = {
    "canonical_statement.txt": "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8",
    "spiegelhofer-wallner-2005.07167v3.pdf": "4e7ed13cab1b9cd23a8886db4fda3919ac8924873770695fb243f5c0b5116130",
    "spiegelhofer-wallner-2005.07167v3.txt": "4a8c93a160a492b463dd3f5d589d8db29392c330081a2296d0d03f44bec79b81",
    "hosten-janvresse-delarue-2111.05030v2.pdf": "cd910d2cb105c2887ff9ae6c25672973f0093c8ebd718349d829e0c79eccafa3",
    "hosten-janvresse-delarue-2111.05030v2.txt": "08f3a4f82e0719a748a37982dc1fb870b834a257ea51e77882ae81391bcbd0ec",
    "diaconis-fulman-0806.3583v1.pdf": "348abf1bc7b06a1527d285dc5274bd72b670b4cf2e19eec391118a659c44312e",
    "diaconis-fulman-0806.3583v1.txt": "ad61f1515402522501ccc47b0a5d41134f370090dcf6dc69d4738d1be91c0580",
    "balister-1909.08777v1.pdf": "53cb919f9e23c2edddd0141bb4d51a6c570f5ae4f5734bc1030d729878e42cc3",
    "balister-1909.08777v1.txt": "2ea1eb9f92b97ec3775b7f360053ecd16829fd7846292abaa1e5a9319afd8b4a",
    "heuberger-kropf-wagner-1404.3680v2.pdf": "20944e0a9cc1de10285ecfb0e664454cf6b3719dd23b27c805761bc9f993a1e9",
}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def check_hashes() -> None:
    for name, expected in HASHES.items():
        actual = sha256(ROOT / name)
        assert actual == expected, (name, actual, expected)


def check_source_anchors() -> None:
    anchors = {
        "spiegelhofer-wallner-2005.07167v3.txt": [
            "Theorem 1.2.", "δ(j, t)", "maximal blocks of 1s"
        ],
        "hosten-janvresse-delarue-2111.05030v2.txt": [
            "Theorem 1.2.", "Proposition 3.1.", "Lemma 4.3."
        ],
        "diaconis-fulman-0806.3583v1.txt": [
            "(H1) P (i, j)", "(H5)", "Theorem 4.3."
        ],
        "balister-1909.08777v1.txt": [
            "Theorem 1.", "Theorem 3.", "Proposition 4."
        ],
    }
    for name, terms in anchors.items():
        text = (ROOT / name).read_text(encoding="utf-8", errors="replace")
        for term in terms:
            assert term in text, (name, term)


def check_report_contract() -> None:
    report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
    required = [
        "PRIMARY_SOURCE_COUNT: 5",
        "PRIMARY_SOURCE_CAP: 12",
        "SEARCHED_LANE_COUNT: 4",
        "CANDIDATE_COUNT: 4",
        "CANDIDATE_CAP: 4",
        "TERMINAL_VERDICT_COUNT: 1",
        "SUCCESSOR_COUNT: 0",
        "H-G19-twisted-cocycle",
        "T_(L,P)(h)",
        "J_(L,P)^(K,v)(h)",
        "C_(L,P)^(K,v)(h)",
        "D*||C_(L,P)^(K,v)(h)||_(2->2)",
        "legal shift edges",
        "Lambda_ell(theta)",
        "4*pi*H_ell/epsilon_ell(theta)",
        "epsilon_ell(theta)*N(k)/(4D)",
        "R_reference",
        "R_centered",
        "R_entry(h)",
        "TERMINAL VERDICT (1/1): **HOLD AS MODEL.**",
    ]
    for term in required:
        assert term in report, term
    assert report.count("TERMINAL VERDICT (1/1)") == 1
    assert "Card disposition" not in report
    for prior in ["T64", "T82", "T91", "T103", "T104", "T105", "T109", "T110", "T111"]:
        assert f"| {prior} |" in report or f"| active {prior} |" in report, prior
    for exclusion in [
        "perturbative coupling", "broad ambient Fourier decay",
        "higher-order uniformity", "finite-state collision recurrence",
        "positive-entropy synchronization", "decimal-safe avoidance",
    ]:
        assert exclusion in report, exclusion
    for clause in ["(H1-boundary", "(H2-native spectral premise)", "(H3)"]:
        assert clause in report, clause
    assert "H-G19-carry-spectrum" not in report


def check_boundary_constants() -> None:
    for ell in range(1, 8):
        q = 10**ell
        child = Fraction(2 * 10 * q, 400 * q * q)
        parent = Fraction(2 * q, 4 * q * q)
        load = child + Fraction(1, 2) * parent
        budget = Fraction(1, 40 * q)
        assert child == Fraction(1, 20 * q)
        assert parent == Fraction(1, 2 * q)
        assert load == Fraction(3, 10 * q)
        assert load / budget == 12


def check_local_limit_thresholds() -> None:
    # Squared forms of the displayed half-budget inequalities.
    for ell in range(1, 8):
        q = 10**ell
        m_binary = (3200 / math.pi) * q * q
        rho_decimal = (1280 / math.pi) * q * q
        assert 1 / math.sqrt(2 * math.pi * m_binary) <= 1 / (80 * q) * (1 + 1e-14)
        assert 1 / math.sqrt(5 * math.pi * rho_decimal) <= 1 / (80 * q) * (1 + 1e-14)


def check_holte_matrix() -> None:
    matrix = (
        (Fraction(11, 20), Fraction(9, 20)),
        (Fraction(9, 20), Fraction(11, 20)),
    )
    assert all(sum(row) == 1 for row in matrix)
    stationary = (Fraction(1, 2), Fraction(1, 2))
    for j in range(2):
        value = sum(stationary[i] * matrix[i][j] for i in range(2))
        assert value == stationary[j]
    second_eigenvalue = matrix[0][0] - matrix[0][1]
    assert second_eigenvalue == Fraction(1, 10)
    assert Fraction(1, 2) > Fraction(1, 400)


def rudin_shapiro(n: int) -> int:
    bits = f"{n:b}"
    return -1 if sum(bits[i:i + 2] == "11" for i in range(len(bits) - 1)) % 2 else 1


def check_rudin_shapiro() -> None:
    values = [rudin_shapiro(n) for n in range(1024)]
    assert values[:3] == [1, 1, 1]
    for n in range(512):
        assert values[2 * n] == values[n]
        assert values[2 * n + 1] == ((-1) ** n) * values[n]
    for ell in range(1, 8):
        q = 10**ell
        theta = Fraction(1, 2)
        ac = 2 + math.log(800 * q * q + 1)
        ap = 2 + math.log(40 * q * q + 1)
        weight = ac * ac + 0.5 * ap * ap
        epsilon_sq = float(theta) / (160 * q * weight)
        threshold = 960 * q * weight / float(theta)
        assert 6 / threshold <= epsilon_sq * (1 + 1e-14)
    assert 81 != 0  # coefficient in the three-position irrationality test


def check_named_sequences() -> None:
    for m in range(1, 20):
        t = (4**m - 1) // 3
        assert f"{t:b}" == "10" * (m - 1) + "1"
        r = (10 ** (2 * m) - 1) // 99
        assert str(r) == "10" * (m - 1) + "1"


def check_native_transfer_thresholds() -> None:
    theta = 0.5
    for ell in range(1, 8):
        q = 10**ell
        ac = 2 + math.log(800 * q * q + 1)
        ap = 2 + math.log(40 * q * q + 1)
        weight = ac * ac + 0.5 * ap * ap
        epsilon = math.sqrt(theta / (160 * q * weight))
        frequency_cap = 8000 * q**3
        dimension_target = 4 * math.pi * frequency_cap / epsilon
        coding_length = 1
        dimension = 10
        while dimension < dimension_target:
            coding_length += 1
            dimension *= 10
        assert dimension >= dimension_target
        if coding_length > 1:
            assert dimension // 10 < dimension_target

        coding_error_per_term = 2 * math.pi * frequency_cap / dimension
        reference_scalar = epsilon / 4
        centered_target_per_term = epsilon / (4 * dimension)
        scalar_from_centered = dimension * centered_target_per_term
        assert coding_error_per_term <= epsilon / 2
        assert reference_scalar == epsilon / 4
        assert scalar_from_centered == epsilon / 4
        assert coding_error_per_term + reference_scalar + scalar_from_centered <= epsilon * (1 + 1e-14)

        # The report's pigeonhole obstruction to the discarded uncentered bound.
        raw_operator_lower_per_term = 1 / (10 * dimension)
        discarded_raw_target_per_term = epsilon / (2 * dimension)
        assert epsilon < 0.2
        assert raw_operator_lower_per_term > discarded_raw_target_per_term

        fourier_defect = 160 * q * weight * epsilon**2
        boundary_load_per_term = theta / (40 * q)
        boundary_defect = 40 * q * boundary_load_per_term
        assert math.isclose(fourier_defect, theta, rel_tol=1e-13)
        assert math.isclose(boundary_defect, theta, rel_tol=1e-13)
        for m in range(1, 20):
            row_sum = theta * (m - 1)
            t107_rhs = (m - 1) - ((1 - theta) * m - (1 - theta))
            assert math.isclose(row_sum, t107_rhs, abs_tol=1e-13)


def check_twisted_operator_identity() -> None:
    # Small transcription check for (10.1)--(10.5), not evidence about pi.
    digits = [3, 1, 4, 1, 5, 9, 2, 6]
    length = 2
    dimension = 10**length
    states = [10 * digits[j] + digits[j + 1] for j in range(len(digits) - 1)]
    for j in range(len(states) - 1):
        assert states[j + 1] == (10 * states[j] + digits[j + length]) % dimension

    h = 3
    transition_entries: dict[tuple[int, int], complex] = {}
    direct_sum = 0j
    for current, nxt in zip(states, states[1:]):
        weight = cmath.exp(2j * math.pi * h * current / dimension)
        transition_entries[(nxt, current)] = transition_entries.get((nxt, current), 0j) + weight
        direct_sum += weight
    all_ones_matrix_coefficient = sum(transition_entries.values(), 0j)
    assert abs(all_ones_matrix_coefficient - direct_sum) < 1e-12

    # Uniform legal-shift K and uniform v give a concrete check of J and C.
    reference_entries: dict[tuple[int, int], complex] = {}
    prefix_length = len(states) - 1
    for current in range(dimension):
        phase = cmath.exp(2j * math.pi * h * current / dimension)
        for digit in range(10):
            nxt = (10 * current + digit) % dimension
            reference_entries[(nxt, current)] = prefix_length * Fraction(1, 10) * Fraction(1, dimension) * phase
    for current in range(dimension):
        column_sum = sum(Fraction(1, 10) for _ in range(10))
        assert column_sum == 1
    for nxt in range(dimension):
        stationary_mass = sum(
            Fraction(1, dimension) * Fraction(1, 10)
            for current in range(dimension)
            if any((10 * current + digit) % dimension == nxt for digit in range(10))
        )
        assert stationary_mass == Fraction(1, dimension)

    reference_scalar = prefix_length * sum(
        cmath.exp(2j * math.pi * h * current / dimension) / dimension
        for current in range(dimension)
    )
    assert abs(sum(reference_entries.values(), 0j) - reference_scalar) < 1e-12
    centered_keys = transition_entries.keys() | reference_entries.keys()
    centered_entries = {
        key: transition_entries.get(key, 0j) - reference_entries.get(key, 0j)
        for key in centered_keys
    }
    assert abs(
        sum(centered_entries.values(), 0j)
        - (all_ones_matrix_coefficient - reference_scalar)
    ) < 1e-12


def main() -> None:
    check_hashes()
    check_source_anchors()
    check_report_contract()
    check_boundary_constants()
    check_local_limit_thresholds()
    check_holte_matrix()
    check_rudin_shapiro()
    check_named_sequences()
    check_native_transfer_thresholds()
    check_twisted_operator_identity()
    print("T112 replay: PASS")
    print("classification: experiment (integrity and finite arithmetic only)")
    print("primary sources: 5/12; candidates: 4/4; searched lanes: 4")
    print("uniform boundary defect: 12; literal good-row threshold: 1")
    print("native transfer: explicit sparse operator and dimension-aware half-budgets PASS")
    print("terminal verdict count: 1; successor count: 0")
    print("no fixed-pi, C1, C2, or canonical A1 claim")


if __name__ == "__main__":
    main()
