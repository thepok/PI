#!/usr/bin/env python3
"""Generate deterministic T187/T188 reflected trigonometric shards.

The generated payload has three leaves per orbit point: the full boundary
angle, its half angle, and its q/2 angle.  All phase cylinders are derived
from the first 10,015 fractional digits retained by T173.  Horner rows and
leaf padding use exact integer/rational arithmetic matching T183 and T186.

This script imports the digit source and its SHA-256 guard from the T170
directed-interval replay.  It does not use Decimal approximations when
constructing Lean certificates.
"""

from __future__ import annotations

import argparse
import difflib
import sys
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from math import factorial
from pathlib import Path

from t170_signed_parent_334_interval import DIGITS


sys.set_int_max_str_digits(0)

CERTIFIED_PI_PLACES = 10_015
Q = 1_000
A = 334
CENTER_DIGITS = 80
HORNER_TERMS = 128
FIXED_SCALE_DIGITS = 100

PI_SCALE = 10**CERTIFIED_PI_PLACES
PI_PREFIX = int("3" + DIGITS[:CERTIFIED_PI_PLACES])
CENTER_SCALE = 10**CENTER_DIGITS
FIXED_SCALE = 10**FIXED_SCALE_DIGITS
PI_LOWER = Fraction(PI_PREFIX, PI_SCALE)
PI_UPPER = Fraction(PI_PREFIX + 1, PI_SCALE)


@dataclass(frozen=True)
class IntInterval:
    lower: int
    upper: int


@dataclass(frozen=True)
class ComplexIntInterval:
    re: IntInterval
    im: IntInterval


@dataclass(frozen=True)
class PhaseKind:
    name: str
    multiplier_numerator: int
    multiplier_denominator: int
    offset_numerator: int
    offset_denominator: int

    @property
    def multiplier(self) -> Fraction:
        return Fraction(self.multiplier_numerator, self.multiplier_denominator)

    @property
    def offset(self) -> Fraction:
        return Fraction(self.offset_numerator, self.offset_denominator)


PHASE_KINDS = (
    PhaseKind("full", 1, 1, -(2 * A + 1), 2 * Q),
    PhaseKind("half", 1, 2, -(2 * A + 1), 4 * Q),
    PhaseKind("qhalf", Q // 2, 1, -(2 * A + 1), 4),
)


@dataclass(frozen=True)
class LeafData:
    orbit_index: int
    kind: PhaseKind
    centered_turn: int
    center_numerator: int
    radius_numerator: int
    claimed: ComplexIntInterval
    cosine_leaf: IntInterval
    sine_leaf: IntInterval


def floor_fraction(x: Fraction) -> int:
    return x.numerator // x.denominator


def ceil_fraction(x: Fraction) -> int:
    return -floor_fraction(-x)


def nearest_integer(x: Fraction) -> int:
    """Round to nearest with upward tie-breaking (ties do not occur here)."""
    return floor_fraction(x + Fraction(1, 2))


@lru_cache(maxsize=None)
def orbit_cylinder(n: int) -> tuple[int, int, Fraction, Fraction]:
    if not 0 <= n <= CERTIFIED_PI_PLACES:
        raise ValueError(f"orbit index {n} exceeds the T173 horizon")
    denominator = 10 ** (CERTIFIED_PI_PLACES - n)
    lower_numerator = PI_PREFIX % denominator
    return (
        denominator,
        lower_numerator,
        Fraction(lower_numerator, denominator),
        Fraction(lower_numerator + 1, denominator),
    )


def phase_geometry(n: int, kind: PhaseKind) -> tuple[int, int, int]:
    _, _, orbit_lower, orbit_upper = orbit_cylinder(n)
    cycle_lower = kind.multiplier * orbit_lower + kind.offset
    cycle_upper = kind.multiplier * orbit_upper + kind.offset
    centered_turn = nearest_integer((cycle_lower + cycle_upper) / 2)
    cycle_lower -= centered_turn
    cycle_upper -= centered_turn
    if cycle_lower < Fraction(-1, 2) or cycle_upper > Fraction(1, 2):
        raise ValueError(f"centered phase crosses cut at n={n}, kind={kind.name}")

    # Both pi endpoints are positive.  Monotonicity selects the two extreme
    # corners directly and avoids sorting four 10,015-digit fractions.
    angle_lower = 2 * (PI_UPPER if cycle_lower < 0 else PI_LOWER) * cycle_lower
    angle_upper = 2 * (PI_LOWER if cycle_upper < 0 else PI_UPPER) * cycle_upper
    center_numerator = nearest_integer((angle_lower + angle_upper) / 2 * CENTER_SCALE)
    center = Fraction(center_numerator, CENTER_SCALE)
    radius_numerator = ceil_fraction(
        max(center - angle_lower, angle_upper - center) * CENTER_SCALE
    )
    return centered_turn, center_numerator, radius_numerator


def mul_rational_interval(p: int, d: int, row: IntInterval) -> IntInterval:
    if d <= 0:
        raise ValueError(f"nonpositive Horner denominator {d}")
    if p >= 0:
        return IntInterval(p * row.lower // d, p * row.upper // d + 1)
    return IntInterval(p * row.upper // d, p * row.lower // d + 1)


def horner_rows(center_numerator: int) -> ComplexIntInterval:
    """Exact Python replay of T183 `hornerRows ... 127 0`."""
    row = ComplexIntInterval(IntInterval(FIXED_SCALE, FIXED_SCALE), IntInterval(0, 0))
    for k in range(HORNER_TERMS - 1, 0, -1):
        xr = mul_rational_interval(center_numerator, CENTER_SCALE * k, row.re)
        xi = mul_rational_interval(center_numerator, CENTER_SCALE * k, row.im)
        row = ComplexIntInterval(
            IntInterval(FIXED_SCALE - xi.upper, FIXED_SCALE - xi.lower), xr
        )
    return row


def leaf_data(n: int, kind: PhaseKind) -> LeafData:
    turn, center_numerator, radius_numerator = phase_geometry(n, kind)
    claimed = horner_rows(center_numerator)
    error = Fraction(radius_numerator, CENTER_SCALE) + Fraction(
        2 * 4**HORNER_TERMS, factorial(HORNER_TERMS)
    )
    padding = ceil_fraction(error * FIXED_SCALE)
    return LeafData(
        orbit_index=n,
        kind=kind,
        centered_turn=turn,
        center_numerator=center_numerator,
        radius_numerator=radius_numerator,
        claimed=claimed,
        cosine_leaf=IntInterval(claimed.re.lower - padding, claimed.re.upper + padding),
        sine_leaf=IntInterval(claimed.im.lower - padding, claimed.im.upper + padding),
    )


def render_leaf(leaf: LeafData) -> str:
    n = leaf.orbit_index
    kind = leaf.kind
    return f"""def leaf_{n}_{kind.name} : TrigLeafCertificate where
  request := {{
    orbitIndex := {n}
    multiplierNumerator := {kind.multiplier_numerator}
    multiplierDenominator := {kind.multiplier_denominator}
    offsetNumerator := {kind.offset_numerator}
    offsetDenominator := {kind.offset_denominator}
    centeredTurn := {leaf.centered_turn}
    centerNumerator := {leaf.center_numerator}
    centerDenominator := 10 ^ {CENTER_DIGITS}
    radiusNumerator := {leaf.radius_numerator}
    radiusDenominator := 10 ^ {CENTER_DIGITS} }}
  horner := {{
    scale := 10 ^ {FIXED_SCALE_DIGITS}
    centerNumerator := {leaf.center_numerator}
    centerDenominator := 10 ^ {CENTER_DIGITS}
    terms := {HORNER_TERMS}
    claimed := ⟨⟨{leaf.claimed.re.lower}, {leaf.claimed.re.upper}⟩,
      ⟨{leaf.claimed.im.lower}, {leaf.claimed.im.upper}⟩⟩ }}
  cosineLeaf := ⟨{leaf.cosine_leaf.lower}, {leaf.cosine_leaf.upper}⟩
  sineLeaf := ⟨{leaf.sine_leaf.lower}, {leaf.sine_leaf.upper}⟩
"""


def render_group(n: int) -> str:
    denominator, lower_numerator, _, _ = orbit_cylinder(n)
    leaves = ", ".join(f"leaf_{n}_{kind.name}" for kind in PHASE_KINDS)
    return f"""def group_{n} : OrbitTrigGroupCertificate where
  cylinder := {{
    orbitIndex := {n}
    denominator := {denominator}
    lowerNumerator := {lower_numerator} }}
  scale := 10 ^ {FIXED_SCALE_DIGITS}
  leaves := [{leaves}]
"""


def render_header(shard_name: str, count: int) -> str:
    if shard_name == "T187ReflectedTrigShard9965" and count == 10:
        description = """# T187: first production-precision actual-pi trigonometric shard

One reflected batch certifies thirty trigonometric leaves for ten root-horizon
orbit points."""
    else:
        description = f"""# Generated production-precision actual-pi trigonometric shard

One reflected batch certifies {3 * count} trigonometric leaves for {count}
orbit points."""
    return f"""import TheoryLib.PiQuantitativeBlockHitting.T188T188SharedOrbitCylinderBatch

/-!
{description} Each point contributes the full boundary angle, its half angle
(the denominator sine in T185), and its q/2 angle for q = {Q}. The payload
uses {HORNER_TERMS} Horner terms, {CENTER_DIGITS}-decimal centres, and common scale 10^{FIXED_SCALE_DIGITS}.
-/

namespace Theory.PiDigits.{shard_name}

open Theory.PiDigits.T171CompactFixedPointCertificate
open Theory.PiDigits.T182ReflectedStackProgram
open Theory.PiDigits.T183ReflectedExpHorner
open Theory.PiDigits.T184CertifiedPiPhaseRequest
open Theory.PiDigits.T186ReflectedTrigLeaf
open Theory.PiDigits.T188SharedOrbitCylinderBatch

noncomputable section

"""


def render_footer(indices: list[int], shard_name: str) -> str:
    group_lines = ",\n".join(f"    group_{n}" for n in indices)
    group_defs = ", ".join(f"group_{n}" for n in indices)
    leaf_defs = ", ".join(
        f"leaf_{n}_{kind.name}" for n in indices for kind in PHASE_KINDS
    )
    denominator_rows = ", ".join(f"leaf_{n}_half.sineLeaf" for n in indices)
    count_word = "ten" if len(indices) == 10 else str(len(indices))
    value_count = "sixty" if len(indices) == 10 else str(6 * len(indices))
    return f"""def shard : OrbitTrigGroupBatchCertificate where
  scale := 10 ^ {FIXED_SCALE_DIGITS}
  groups := [
{group_lines}
  ]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 15000 in
theorem shard_checks : checkOrbitTrigGroupBatch shard = true := by
  norm_num (config := {{ maxSteps := 10000000 }})
    [checkOrbitTrigGroupBatch, shard, checkOrbitTrigGroup,
    checkOrbitCylinder, checkTrigLeafAtCylinder, checkPhaseAtCylinder,
    cycleLowerAt, cycleUpperAt, angleCornersAt, checkHorner,
    TrigLeafCertificate.error, rationalTrigRemainder,
    PhaseRequest.angleRadius, PhaseRequest.angleCenter,
    PhaseRequest.piLower, PhaseRequest.piUpper,
    PhaseRequest.multiplier, PhaseRequest.offset,
    OrbitCylinderCertificate.lower, OrbitCylinderCertificate.upper,
    hornerRows, hornerStep, mulRationalInterval,
    {group_defs},
    {leaf_defs}]

/-- All {value_count} actual sine/cosine values are enclosed by the generated rows.
The row order is cosine then sine within each three-leaf orbit group. -/
theorem shard_sound : StackRel shard.scale shard.rows shard.values :=
  checkedOrbitTrigGroupBatch_sound shard_checks

/-- The {count_word} half-angle sine rows used as T185 denominators avoid zero with
large explicit margins before any downstream division is attempted. -/
theorem denominator_sine_rows_avoid_zero :
    [{denominator_rows}].all
      (fun row => decide (row.upper < 0 ∨ 0 < row.lower)) = true := by rfl

end

end Theory.PiDigits.{shard_name}

#print axioms Theory.PiDigits.{shard_name}.shard_sound
#print axioms Theory.PiDigits.{shard_name}.denominator_sine_rows_avoid_zero
"""


def render_shard(start: int, stop: int, shard_name: str) -> str:
    if not 0 <= start < stop <= CERTIFIED_PI_PLACES:
        raise ValueError(
            f"expected 0 <= start < stop <= {CERTIFIED_PI_PLACES}, got {start}:{stop}"
        )
    indices = list(range(start, stop))
    pieces = [render_header(shard_name, len(indices))]
    pieces.extend(render_leaf(leaf_data(n, kind)) + "\n" for n in indices for kind in PHASE_KINDS)
    pieces.extend(render_group(n) + "\n" for n in indices)
    pieces.append(render_footer(indices, shard_name))
    return "".join(pieces)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--start", type=int, required=True, help="first orbit index")
    parser.add_argument("--stop", type=int, required=True, help="exclusive orbit index")
    parser.add_argument("--shard-name", required=True, help="Lean namespace suffix")
    parser.add_argument("--output", type=Path, help="write generated Lean source here")
    parser.add_argument(
        "--check-against",
        type=Path,
        help="compare generated bytes with an existing source and fail on differences",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.output is None and args.check_against is None:
        raise SystemExit("provide --output and/or --check-against")
    generated = render_shard(args.start, args.stop, args.shard_name)
    generated_bytes = generated.encode("utf-8")
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_bytes(generated_bytes)
        print(f"wrote {len(generated_bytes)} bytes to {args.output}")
    if args.check_against is not None:
        existing = args.check_against.read_bytes()
        if existing != generated_bytes:
            diff = difflib.unified_diff(
                existing.decode("utf-8").splitlines(),
                generated.splitlines(),
                fromfile=str(args.check_against),
                tofile="generated",
                n=3,
            )
            print("\n".join(list(diff)[:120]), file=sys.stderr)
            raise SystemExit("generated source differs from existing source")
        print(f"byte-for-byte match: {args.check_against}")


if __name__ == "__main__":
    main()
