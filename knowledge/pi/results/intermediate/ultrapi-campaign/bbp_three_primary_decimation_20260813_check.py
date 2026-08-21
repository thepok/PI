#!/usr/bin/env python3
"""Independent exact replay for the BBP three-primary decimation branch.

All arithmetic supporting identities is integer or Fraction arithmetic.  The
finite checks are experiments; they do not assert a full BBP-phase return or
the every-finite-decimal-word property for pi.
"""

from fractions import Fraction
from math import gcd


POLES = (
    (8, 1, Fraction(4)),
    (2, 1, Fraction(-1, 2)),
    (8, 5, Fraction(-1)),
    (4, 3, Fraction(-1, 2)),
)
OFFSETS = tuple(8 * b // a for a, b, _ in POLES)
LIFT_MULTIPLIERS = tuple(8 // a for a, _, _ in POLES)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def pole_term(index: int, k: int) -> Fraction:
    a, b, coefficient = POLES[index]
    return coefficient / ((a * k + b) * 16**k)


def coefficient(k: int) -> Fraction:
    return Fraction(
        120 * k * k + 151 * k + 47,
        (2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5),
    )


def v3_integer(value: int) -> int:
    value = abs(value)
    if value == 0:
        return 10**9
    result = 0
    while value % 3 == 0:
        value //= 3
        result += 1
    return result


def v3_fraction(value: Fraction) -> int:
    if value == 0:
        return 10**9
    return v3_integer(value.numerator) - v3_integer(value.denominator)


def split_power_three(value: int) -> tuple[int, int]:
    exponent = 0
    while value % 3 == 0 and value:
        value //= 3
        exponent += 1
    return exponent, value


def scaled_combined_term_mod(k: int, exponent: int) -> int:
    """Return 3^exponent * a(k)/16^k modulo 3^exponent.

    This is called only in a range where every summand has 3-adic valuation
    at least -exponent.
    """

    modulus = 3**exponent
    numerator = 120 * k * k + 151 * k + 47
    denominator = (2 * k + 1) * (4 * k + 3) * (8 * k + 1) * (8 * k + 5)
    common = gcd(numerator, denominator)
    numerator //= common
    denominator //= common
    numerator_exponent, numerator_unit = split_power_three(numerator)
    denominator_exponent, denominator_unit = split_power_three(denominator)
    shift = exponent + numerator_exponent - denominator_exponent
    require(shift >= 0, f"term height exceeds endpoint height at k={k}")
    if shift >= exponent:
        return 0
    dyadic_unit = pow(16, k, modulus)
    return (
        numerator_unit
        * 3**shift
        * pow(denominator_unit, -1, modulus)
        * pow(dyadic_unit, -1, modulus)
    ) % modulus


def endpoint_betas(e: int) -> tuple[int, int, int]:
    """Return pre-depth, pre beta mod 3^e, and post beta mod 3^(e-1)."""

    require(e >= 2 and e % 2 == 0, "e must be positive even and at least two")
    A = (3**e - 1) // 8
    pre_depth = 5 * A - 1
    modulus = 3**e
    scaled_sum = 0
    for k in range(pre_depth + 1):
        scaled_sum = (scaled_sum + scaled_combined_term_mod(k, e)) % modulus
    pre_beta = scaled_sum
    scaled_sum = (
        scaled_sum + scaled_combined_term_mod(pre_depth + 1, e)
    ) % modulus
    require(scaled_sum % 3 == 0, f"drop numerator did not cancel at e={e}")
    return pre_depth, pre_beta, scaled_sum // 3


def main() -> None:
    require(OFFSETS == (1, 4, 5, 6), f"wrong offsets: {OFFSETS}")
    require(LIFT_MULTIPLIERS == (1, 4, 1, 2), "wrong lift multipliers")

    partial_fraction_checks = 0
    for k in range(1025):
        require(
            coefficient(k) / 16**k
            == sum((pole_term(i, k) for i in range(4)), Fraction()),
            f"partial fraction failure at k={k}",
        )
        partial_fraction_checks += 1

    affine_decimation_checks = 0
    termwise_integrality_checks = 0
    for i, ((a, b, _), offset, multiplier) in enumerate(
        zip(POLES, OFFSETS, LIFT_MULTIPLIERS)
    ):
        require(a * offset + b == 9 * b, f"affine lift failure for pole {i}")
        for r in range(513):
            require(
                a * (9 * r + offset) + b == 9 * (a * r + b),
                f"affine decimation failure for pole {i}, r={r}",
            )
            require(8 * r + offset == multiplier * (a * r + b), "LTE exponent")
            affine_decimation_checks += 1
            lhs = 9 * pole_term(i, 9 * r + offset) - pole_term(i, r)
            rhs = pole_term(i, r) * (
                Fraction(1, 16 ** (8 * r + offset)) - 1
            )
            require(lhs == rhs, f"termwise identity failure for pole {i}, r={r}")
            require(v3_fraction(lhs) >= 0, f"nonintegral lift error at pole {i}, r={r}")
            termwise_integrality_checks += 1

    nonlift_integrality_checks = 0
    for i, (a, b, _) in enumerate(POLES):
        offset = OFFSETS[i]
        for k in range(4097):
            if k % 9 == offset:
                continue
            require(v3_integer(a * k + b) <= 1, f"unexpected height at pole {i}, k={k}")
            require(v3_fraction(9 * pole_term(i, k)) >= 0, "nonlift term not integral")
            nonlift_integrality_checks += 1

    # Directly replay the finite-sum decimation in Q_3 / Z_3.
    decimation_sum_checks = 0
    bbp_sum = Fraction()
    decimated_sums = [Fraction() for _ in POLES]
    next_r = [0 for _ in POLES]
    for M in range(513):
        bbp_sum += sum((pole_term(i, M) for i in range(4)), Fraction())
        for i, offset in enumerate(OFFSETS):
            if M >= offset and (M - offset) % 9 == 0:
                r = (M - offset) // 9
                require(r == next_r[i], f"decimated index gap for pole {i}")
                decimated_sums[i] += pole_term(i, r)
                next_r[i] += 1
        require(
            v3_fraction(9 * bbp_sum - sum(decimated_sums, Fraction())) >= 0,
            f"finite decimation congruence failure at M={M}",
        )
        decimation_sum_checks += 1

    symbolic_endpoint_checks = 0
    for e in range(4, 162, 2):
        old_A = (3 ** (e - 2) - 1) // 8
        old_pre = 5 * old_A - 1
        old_post = old_pre + 1
        A = (3**e - 1) // 8
        pre = 5 * A - 1
        post = pre + 1
        require(pre == 9 * old_pre + 13, f"pre scaling failure at e={e}")
        require(post == 9 * old_post + 5, f"post scaling failure at e={e}")
        pre_cutoffs = tuple((pre - c) // 9 for c in OFFSETS)
        post_cutoffs = tuple((post - c) // 9 for c in OFFSETS)
        require(pre_cutoffs == (old_pre + 1, old_pre + 1, old_pre, old_pre), "pre cutoffs")
        require(post_cutoffs == (old_post, old_post, old_post, old_post - 1), "post cutoffs")
        require((8 * old_post + 1) % 3 != 0, "pre extra pole zero not regular")
        require((2 * old_post + 1) % 3 != 0, "pre extra pole one not regular")
        require((4 * old_post + 3) % 3 != 0, "post missing pole not regular")
        symbolic_endpoint_checks += 1

    beta_rows = []
    previous_pre = None
    previous_post = None
    nested_pre_checks = 0
    nested_post_checks = 0
    for e in range(2, 14, 2):
        depth, pre_beta, post_beta = endpoint_betas(e)
        if previous_pre is not None:
            require(pre_beta % (3 ** (e - 2)) == previous_pre, f"pre nesting e={e}")
            require(post_beta % (3 ** (e - 3)) == previous_post, f"post nesting e={e}")
            nested_pre_checks += 1
            nested_post_checks += 1
        beta_rows.append((e, depth, pre_beta, post_beta))
        previous_pre = pre_beta
        previous_post = post_beta

    # Exact proportional-period margin used for the real shadow estimate.
    archimedean_margin_checks = 0
    geometric_ratio = Fraction(31250, 32768)
    require(geometric_ratio < 1, "geometric shadow ratio must contract")
    for e in range(4, 42, 2):
        A = (3**e - 1) // 8
        M = 5 * A - 1
        T = 3 ** (e - 2)
        require(M >= 5 * (T - 1), f"period margin failure at e={e}")
        # 10^(M+T)/16^M <= (8/5)^5 * rho^T follows from M >= 5(T-1).
        archimedean_margin_checks += 1

    print("claim_status=experiment")
    print(f"partial_fraction_checks={partial_fraction_checks}")
    print(f"affine_decimation_checks={affine_decimation_checks}")
    print(f"termwise_integrality_checks={termwise_integrality_checks}")
    print(f"nonlift_integrality_checks={nonlift_integrality_checks}")
    print(f"decimation_sum_checks={decimation_sum_checks}")
    print(f"symbolic_endpoint_checks={symbolic_endpoint_checks}")
    print(f"nested_pre_checks={nested_pre_checks}")
    print(f"nested_post_checks={nested_post_checks}")
    print(f"archimedean_margin_checks={archimedean_margin_checks}")
    print("beta_rows=" + ";".join(f"e{e}:M{M}:pre{pre}:post{post}" for e, M, pre, post in beta_rows))
    print("asserts_joint_crt_control=false")
    print("asserts_fixed_return=false")
    print("asserts_v1=false")
    print("status=PASS")


if __name__ == "__main__":
    main()
