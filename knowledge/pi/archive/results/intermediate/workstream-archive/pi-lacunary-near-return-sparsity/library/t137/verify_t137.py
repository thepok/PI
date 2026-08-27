#!/usr/bin/env python3
"""Self-contained exact-integer replay for T137."""

from collections import Counter
from fractions import Fraction
from hashlib import sha256
from pathlib import Path


ROOT = Path(__file__).resolve().parent
CANONICAL_SHA256 = "cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8"
MASS_CAP = 24
SUPPORT_CAP = 12
TENSOR_COORDINATE_CAP = 100_000
EXPECTED_PAIR_COUNT = 2_693_413

if not __debug__:
    raise RuntimeError("verification requires assertions; do not use python -O")


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def partitions(n, largest=None, slots=SUPPORT_CAP):
    """Yield decreasing positive partitions of n having at most slots parts."""
    if n == 0:
        yield ()
        return
    if slots == 0:
        return
    largest = n if largest is None else min(largest, n)
    for first in range(largest, 0, -1):
        for rest in partitions(n - first, first, slots - 1):
            yield (first,) + rest


def pad(profile, width):
    return tuple(profile) + (0,) * (width - len(profile))


def energy(profile):
    return sum(x * x for x in profile)


def meet(left, right):
    """Majorization meet from the pointwise minimum of Lorenz sums."""
    width = max(len(left), len(right))
    left = pad(left, width)
    right = pad(right, width)
    left_sum = right_sum = previous = 0
    result = []
    for x, y in zip(left, right):
        left_sum += x
        right_sum += y
        current = min(left_sum, right_sum)
        result.append(current - previous)
        previous = current
    assert all(result[i] >= result[i + 1] for i in range(width - 1))
    assert sum(result) == sum(left) == sum(right)
    return tuple(result)


def tensor_power(profile, exponent):
    result = (1,)
    for _ in range(exponent):
        result = tuple(sorted((x * y for x in result for y in profile), reverse=True))
    return result


def majorized(left, right):
    """Return left prec right, including the equal-mass condition."""
    width = max(len(left), len(right))
    left = sorted(pad(left, width), reverse=True)
    right = sorted(pad(right, width), reverse=True)
    left_sum = right_sum = 0
    for x, y in zip(left, right):
        left_sum += x
        right_sum += y
        if left_sum > right_sum:
            return False
    return left_sum == right_sum


def next_power(base, lower_bound):
    value = base
    while value < lower_bound:
        value *= base
    return value


def crt_realization(left, right):
    """Realize two profiles by pairing unit labels and applying explicit CRT."""
    q = next_power(2, len(left))
    r = next_power(3, len(right))
    inverse = pow(q, -1, r)
    left_labels = [i for i, count in enumerate(left) for _ in range(count)]
    right_labels = [j for j, count in enumerate(right) for _ in range(count)]
    values = [
        i + q * (((j - i) * inverse) % r)
        for i, j in zip(left_labels, right_labels)
    ]
    got_left = Counter(value % q for value in values)
    got_right = Counter(value % r for value in values)
    assert tuple(sorted(got_left.values(), reverse=True)) == tuple(left)
    assert tuple(sorted(got_right.values(), reverse=True)) == tuple(right)
    return q, r, values


def ratio_data(left, right):
    common_meet = meet(left, right)
    numerator = min(energy(left), energy(right))
    denominator = energy(common_meet)
    return numerator, denominator, common_meet


def check_t132_witness():
    label_weights = (3, 1, 1, 3, 1, 1)
    exact = energy(label_weights)
    mod2 = tuple(sorted((sum(label_weights[0::2]), sum(label_weights[1::2])), reverse=True))
    mod3 = tuple(
        sorted((sum(label_weights[r::3]) for r in range(3)), reverse=True)
    )
    common_meet = meet(mod2, mod3)
    gain = energy(common_meet)
    projected_min = min(energy(mod2), energy(mod3))
    projected_average = Fraction(energy(mod2) + energy(mod3), 2)
    assert (mod2, mod3, common_meet) == ((5, 5), (6, 2, 2), (5, 3, 2))
    assert (exact, gain, projected_min, projected_average) == (22, 38, 44, 47)
    print("T132 witness: 22 < 38 < 44 < 47")


def exhaustive_sweep():
    total_pairs = 0
    global_best = (0, 1, None, None, None)
    print("exhaustive sweep by mass:")
    for mass in range(1, MASS_CAP + 1):
        profiles = list(partitions(mass))
        pair_count = len(profiles) * (len(profiles) + 1) // 2
        total_pairs += pair_count
        best = (0, 1, None, None, None)
        for i, left in enumerate(profiles):
            for right in profiles[i:]:
                q, r, values = crt_realization(left, right)
                assert len(values) == mass and q >= len(left) and r >= len(right)
                numerator, denominator, common_meet = ratio_data(left, right)
                if numerator * best[1] > best[0] * denominator:
                    best = (numerator, denominator, left, right, common_meet)
                if numerator * global_best[1] > global_best[0] * denominator:
                    global_best = (numerator, denominator, left, right, common_meet)
        print(
            f"  N={mass:2d} profiles={len(profiles):4d} pairs={pair_count:6d} "
            f"max={best[0]}/{best[1]} a={best[2]} b={best[3]} meet={best[4]}"
        )
    assert total_pairs == EXPECTED_PAIR_COUNT
    assert global_best[:2] == (180, 110)
    assert global_best[2:] == (
        (13, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1),
        (8, 8, 8),
        (8, 6, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1),
    )
    print(f"exhaustive total: {total_pairs} unordered pairs (self-pairs included)")
    print("bounded maximum: 180/110 = 18/11 at N=24")


def check_tensor_family(name, left, right, expected=None):
    width = max(len(left), len(right))
    left = pad(left, width)
    right = pad(right, width)
    base_meet = meet(left, right)
    print(f"{name} direct tensor powers (ambient coordinate cap {TENSOR_COORDINATE_CAP}):")
    exponent = 1
    observed = []
    while width**exponent <= TENSOR_COORDINATE_CAP:
        left_power = tensor_power(left, exponent)
        right_power = tensor_power(right, exponent)
        tensor_meet = meet(left_power, right_power)
        meet_power = tensor_power(base_meet, exponent)
        assert majorized(meet_power, tensor_meet)
        assert energy(meet_power) <= energy(tensor_meet)
        numerator = min(energy(left_power), energy(right_power))
        denominator = energy(tensor_meet)
        observed.append((numerator, denominator))
        print(
            f"  k={exponent:2d} coordinates={width**exponent:5d} "
            f"numerator={numerator} meet_energy={denominator} "
            f"ratio={numerator}/{denominator}"
        )
        exponent += 1
    assert width ** (exponent - 1) <= TENSOR_COORDINATE_CAP < width**exponent
    if expected is not None:
        assert observed == expected
    return observed


def check_unbounded_family():
    family = check_tensor_family("unbounded family", (4, 1, 1), (3, 3, 0))
    assert family[0] == (18, 14)
    assert family[1] == (324, 234)
    # The report's analytic lower bound has base 18/(10*sqrt(3)); its square is 27/25.
    assert 27 > 25


def check_t132_tensors():
    observed = check_tensor_family("T132 profiles", (5, 5, 0), (6, 2, 2))
    assert observed[0] == (44, 38)
    assert observed[1] == (1936, 1650)
    assert energy(tensor_power((5, 3, 2), 2)) == 1444 < 1650
    assert observed[2][0] * observed[1][1] > observed[1][0] * observed[2][1]
    assert observed[3][0] * observed[2][1] < observed[2][0] * observed[3][1]
    print("T132 tensor identity falsified: 1444 < 1650 at k=2")
    print("T132 tensor ratios increase from k=2 to k=3, then decrease at k=4")


def check_scope_markers():
    report = (ROOT / "REPORT.md").read_text(encoding="utf-8")
    required = [
        "VERDICT: PROVED UNBOUNDED FAMILY",
        "PI-MEET_STATUS: conjecture; unproved",
        "FIXED_PI_CLAIM: none",
        "C1_CLAIM: none",
        "C2_CLAIM: none",
        "MEET_MULTIPLICATIVITY_ASSUMED: no",
        "INDEPENDENCE_ASSUMED: no",
    ]
    for marker in required:
        assert marker in report, marker
    assert report.count("VERDICT:") == 1
    print("scope and unique-verdict markers: ok")


def main():
    print("T137 self-contained exact-integer replay")
    assert digest(ROOT / "canonical_statement.txt") == CANONICAL_SHA256
    print(f"canonical statement SHA-256: {CANONICAL_SHA256}")
    check_scope_markers()
    check_t132_witness()
    exhaustive_sweep()
    check_t132_tensors()
    check_unbounded_family()
    print("all T137 replay checks passed")


if __name__ == "__main__":
    main()
