"""Trusted pure-data oracle for the bounded T120 S0 controller gate.

Only canonical JSON, exact schemas, supplied-point integer statistics, hashes,
and controller-owned synthetic fixtures live here.  There is no BBP route,
production point generation, CAS write, receipt mint, or experiment launch.
"""

from __future__ import annotations

import json as _json
import re as _re


GATE_ID = "t120_s0_schema_v1"
EXPERIMENT_ID = "pi-q10-j10-lag-determinant-20260822-v1"
WINDOW_SCHEMA = "pi-q10-window-v1"
CAS_SCHEMA = "pi-q10-cas-record-v1"
RECEIPT_SCHEMA = "pi-q10-controller-receipt-v1"
FIXTURE_SCHEMA = "pi-t120-s0-controller-fixture-v3"
SPEC_BUNDLE_SHA256 = "fe180d8a5db818d3b4a9b3931779b3cc3d313a2437e9f4db808f3afecba51f98"

WINDOW_WIDTH = 256
FIRST_N = 512
WINDOW_COUNT = 14
TEST_WINDOW_INDEX = 13
TEST_START_N = 3840
TEST_END_EXCLUSIVE_N = 4096

CANDIDATE_SOURCE_MAX_BYTES = 262_144
REPORT_MAX_BYTES = 65_536
CANONICAL_RAW_MAX_BYTES = 268_435_456
JSON_MAX_NESTING_DEPTH = 32
JSON_MAX_ARRAY_ITEMS = 2_048
JSON_MAX_OBJECT_KEYS = 64
INTEGER_STRING_MAX_DIGITS = 2_000_000
ISOLATED_TIMEOUT_SECONDS = 120
ISOLATED_CPUS = 1
ISOLATED_MEMORY_BYTES = 2_147_483_648
ISOLATED_PIDS = 64
ISOLATED_TMPFS_BYTES = 1_073_741_824

_NONNEGATIVE_INTEGER_PATTERN = r"(?:0|[1-9][0-9]*)\Z"
_LOWER_HEX_64_PATTERN = r"[0-9a-f]{64}\Z"
_POINT_KEYS = ("cell", "n", "r", "w")
_LAG_KEYS = (
    "lag",
    "near_determinant_count",
    "same_cell_count",
    "zero_determinant_count",
)
_RATIO_KEYS = ("cell", "den", "lag", "num", "witness_m", "witness_n")
_DECISION_KEYS = (
    "a_sum",
    "c_sum",
    "has_zero_distinct_pair",
    "j_threshold_pass",
    "window13_action",
)
_WINDOW_KEYS = (
    "cell_counts",
    "decision",
    "end_exclusive_n",
    "experiment_id",
    "j",
    "j10_strict_pass",
    "lag_counts",
    "maximum_determinant_ratio",
    "points",
    "schema",
    "spec_bundle_sha256",
    "start_n",
    "window_index",
)
_CAS_KEYS = (
    "algorithm",
    "artifact_sha256",
    "end_exclusive_n",
    "experiment_id",
    "schema",
    "size_bytes",
    "spec_bundle_sha256",
    "start_n",
    "window_index",
)
_CAS_BINDING_KEYS = (
    "artifact_sha256",
    "end_exclusive_n",
    "experiment_id",
    "size_bytes",
    "spec_bundle_sha256",
    "start_n",
    "window_index",
)
_RECEIPT_KEYS = (
    "artifact_sha256",
    "controller_gate_id",
    "end_exclusive_n",
    "experiment_id",
    "generator_source_sha256",
    "schema",
    "spec_bundle_sha256",
    "start_n",
    "verifier_result",
    "verifier_source_sha256",
    "window_index",
)
_RECEIPT_BINDING_KEYS = (
    "artifact_sha256",
    "controller_gate_id",
    "end_exclusive_n",
    "experiment_id",
    "generator_source_sha256",
    "spec_bundle_sha256",
    "start_n",
    "verifier_result",
    "verifier_source_sha256",
    "window_index",
)


class _ValidationError(ValueError):
    pass


def _exact_equal(left: object, right: object) -> bool:
    if type(left) is not type(right):
        return False
    if type(left) is dict:
        if set(left) != set(right):
            return False
        return all(_exact_equal(left[key], right[key]) for key in left)
    if type(left) is list:
        return len(left) == len(right) and all(
            _exact_equal(a, b) for a, b in zip(left, right)
        )
    return left == right


def _validate_json_shape(value: object, depth: int = 0) -> None:
    if value is None or type(value) in (str, int, bool):
        return
    if type(value) is list:
        container_depth = depth + 1
        if container_depth > JSON_MAX_NESTING_DEPTH:
            raise _ValidationError("JSON nesting exceeds the frozen limit")
        if len(value) > JSON_MAX_ARRAY_ITEMS:
            raise _ValidationError("JSON array exceeds the frozen item limit")
        for item in value:
            _validate_json_shape(item, container_depth)
        return
    if type(value) is dict:
        container_depth = depth + 1
        if container_depth > JSON_MAX_NESTING_DEPTH:
            raise _ValidationError("JSON nesting exceeds the frozen limit")
        if len(value) > JSON_MAX_OBJECT_KEYS:
            raise _ValidationError("JSON object exceeds the frozen key limit")
        for key, item in value.items():
            if type(key) is not str:
                raise _ValidationError("JSON object keys must have exact type str")
            _validate_json_shape(item, container_depth)
        return
    raise _ValidationError("value has a forbidden non-JSON exact type")


def canonical_json_bytes(value: object) -> bytes:
    """Return compact sorted-key ensure-ASCII JSON plus exactly one LF."""
    _validate_json_shape(value)
    try:
        raw = _json.dumps(
            value,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
            allow_nan=False,
        ).encode("ascii") + b"\n"
    except (TypeError, ValueError, UnicodeError, OverflowError) as exc:
        raise _ValidationError("value cannot be encoded as frozen canonical JSON") from exc
    if type(raw) is not bytes:
        raise _ValidationError("canonical encoding did not produce built-in bytes")
    if len(raw) > CANONICAL_RAW_MAX_BYTES:
        raise _ValidationError("canonical JSON exceeds the frozen byte limit")
    return raw


def _reject_duplicate_pairs(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise _ValidationError("duplicate JSON object key")
        result[key] = value
    return result


def _reject_float(token: str) -> object:
    raise _ValidationError("floating-point JSON tokens are forbidden")


def _reject_constant(token: str) -> object:
    raise _ValidationError("non-finite JSON tokens are forbidden")


def _decimal_to_int(value: str) -> int:
    negative = value.startswith("-")
    digits = value[1:] if negative else value
    result = 0
    first = len(digits) % 9
    index = 0
    if first:
        result = int(digits[:first])
        index = first
    while index < len(digits):
        result = result * 1_000_000_000 + int(digits[index : index + 9])
        index += 9
    return -result if negative else result


def _parse_json_int(token: str) -> int:
    return _decimal_to_int(token)


def decode_canonical_json(raw: bytes) -> object:
    """Decode only exact built-in bytes in the frozen canonical representation."""
    if type(raw) is not bytes:
        raise _ValidationError("canonical input must have exact type bytes")
    if len(raw) > CANONICAL_RAW_MAX_BYTES:
        raise _ValidationError("canonical input exceeds the frozen byte limit")
    if raw.startswith(b"\xef\xbb\xbf"):
        raise _ValidationError("UTF-8 BOM is forbidden")
    if b"\r" in raw:
        raise _ValidationError("CR and CRLF are forbidden")
    if not raw.endswith(b"\n"):
        raise _ValidationError("exactly one final LF is required")
    if raw.endswith(b"\n\n") or b"\n" in raw[:-1]:
        raise _ValidationError("only one terminal LF is permitted")
    try:
        text = raw[:-1].decode("utf-8", errors="strict")
    except UnicodeError as exc:
        raise _ValidationError("invalid UTF-8") from exc
    try:
        value = _json.loads(
            text,
            object_pairs_hook=_reject_duplicate_pairs,
            parse_float=_reject_float,
            parse_constant=_reject_constant,
            parse_int=_parse_json_int,
        )
    except _ValidationError:
        raise
    except (
        TypeError,
        ValueError,
        UnicodeError,
        RecursionError,
        _json.JSONDecodeError,
    ) as exc:
        raise _ValidationError("invalid strict JSON") from exc
    _validate_json_shape(value)
    if canonical_json_bytes(value) != raw:
        raise _ValidationError("parsed-equivalent but noncanonical raw bytes")
    return value


def _require_exact_keys(value: object, keys: tuple[str, ...], label: str) -> dict[str, object]:
    if type(value) is not dict or set(value) != set(keys):
        raise _ValidationError(label + " has the wrong exact key set")
    return value


def _require_int(value: object, label: str, minimum: int | None = None) -> int:
    if type(value) is not int:
        raise _ValidationError(label + " must be a JSON integer, not boolean")
    if minimum is not None and value < minimum:
        raise _ValidationError(label + " is below its minimum")
    return value


def _require_bool(value: object, label: str) -> bool:
    if type(value) is not bool:
        raise _ValidationError(label + " must be a JSON boolean")
    return value


def _require_string(value: object, label: str, nonempty: bool = False) -> str:
    if type(value) is not str or (nonempty and not value):
        raise _ValidationError(label + " must be a JSON string")
    return value


def _require_digest(value: object, label: str) -> str:
    if type(value) is not str or _re.fullmatch(_LOWER_HEX_64_PATTERN, value) is None:
        raise _ValidationError(label + " must be lowercase SHA-256 hex")
    return value


def _require_nonnegative_integer_string(value: object, label: str) -> str:
    if type(value) is not str or _re.fullmatch(_NONNEGATIVE_INTEGER_PATTERN, value) is None:
        raise _ValidationError(label + " must be a canonical nonnegative integer string")
    if len(value) > INTEGER_STRING_MAX_DIGITS:
        raise _ValidationError(label + " exceeds the frozen digit limit")
    return value


def _compare_nonnegative_decimal(left: str, right: str) -> int:
    if len(left) != len(right):
        return -1 if len(left) < len(right) else 1
    if left == right:
        return 0
    return -1 if left < right else 1


def _multiply_decimal_small(value: str, factor: int) -> str:
    if factor == 0 or value == "0":
        return "0"
    carry = 0
    out: list[str] = []
    for char in reversed(value):
        total = (ord(char) - 48) * factor + carry
        out.append(chr(48 + total % 10))
        carry = total // 10
    while carry:
        out.append(chr(48 + carry % 10))
        carry //= 10
    out.reverse()
    return "".join(out)


def _point_cell(r: str, w: str) -> int:
    if r == "0":
        return 0
    scaled = _multiply_decimal_small(r, 10)
    for cell in range(9, -1, -1):
        if _compare_nonnegative_decimal(_multiply_decimal_small(w, cell), scaled) <= 0:
            return cell
    raise _ValidationError("cannot derive point cell")


def _point_parts(value: object, expected_n: object) -> tuple[int, str, str, int]:
    point = _require_exact_keys(value, _POINT_KEYS, "point")
    expected = _require_int(expected_n, "expected_n")
    n = _require_int(point["n"], "point.n")
    cell = _require_int(point["cell"], "point.cell")
    r = _require_nonnegative_integer_string(point["r"], "point.r")
    w = _require_nonnegative_integer_string(point["w"], "point.w")
    if n != expected:
        raise _ValidationError("point.n does not equal the controller-selected index")
    if w == "0":
        raise _ValidationError("point.w must be positive")
    if _compare_nonnegative_decimal(r, w) >= 0:
        raise _ValidationError("point.r must satisfy 0 <= r < w")
    if cell != _point_cell(r, w) or not 0 <= cell < 10:
        raise _ValidationError("point.cell is not exact integer division (10*r)//w")
    return n, r, w, cell


def validate_point(value: object, expected_n: object) -> None:
    """Validate one supplied point; S0 does not authenticate T118 provenance."""
    _point_parts(value, expected_n)
    return None


def _frozen_window(window_index: object, start_n: object, end_exclusive_n: object) -> tuple[int, int, int]:
    index = _require_int(window_index, "window_index", 0)
    start = _require_int(start_n, "start_n", 0)
    end = _require_int(end_exclusive_n, "end_exclusive_n", 0)
    if index >= WINDOW_COUNT:
        raise _ValidationError("window_index is outside the frozen census")
    expected_start = FIRST_N + WINDOW_WIDTH * index
    expected_end = expected_start + WINDOW_WIDTH
    if (start, end) != (expected_start, expected_end):
        raise _ValidationError("window range does not match a frozen row")
    return index, start, end


def _require_spec_bundle(value: object) -> str:
    if type(value) is not str or value != SPEC_BUNDLE_SHA256:
        raise _ValidationError("spec_bundle_sha256 is not the frozen parent binding")
    return value


def _decision(j: int, c_sum: int, a_sum: int, has_zero: bool) -> dict[str, object]:
    passed = 9 * j < 65536
    if not passed:
        action = "stop_local_conjecture"
    elif has_zero:
        action = "stop_audit_zero"
    elif a_sum <= 3512:
        action = "go_holdouts"
    else:
        action = "stop_determinant_route_pending_optional_refinement"
    return {
        "j_threshold_pass": passed,
        "c_sum": c_sum,
        "a_sum": a_sum,
        "has_zero_distinct_pair": has_zero,
        "window13_action": action,
    }


def recompute_window(
    points: object,
    window_index: object,
    start_n: object,
    end_exclusive_n: object,
    spec_bundle_sha256: object,
) -> dict[str, object]:
    """Return a newly allocated complete artifact recomputed from supplied points."""
    index, start, end = _frozen_window(window_index, start_n, end_exclusive_n)
    _require_spec_bundle(spec_bundle_sha256)
    if type(points) is not list or len(points) != WINDOW_WIDTH:
        raise _ValidationError("window must contain exactly 256 ordered points")

    checked: list[dict[str, object]] = []
    numeric: list[tuple[int, int, int, int]] = []
    counts = [0] * 10
    for offset, point in enumerate(points):
        n, r_text, w_text, cell = _point_parts(point, start + offset)
        checked.append({"n": n, "r": r_text, "w": w_text, "cell": cell})
        r = _decimal_to_int(r_text)
        w = _decimal_to_int(w_text)
        numeric.append((n, r, w, cell))
        counts[cell] += 1
    j = sum(count * count for count in counts)

    lag_counts: list[dict[str, int]] = []
    maximum: tuple[int, int, int, int, int, int] | None = None
    c_sum = 0
    a_sum = 0
    z_sum = 0
    for lag in range(1, WINDOW_WIDTH):
        same_count = 0
        near_count = 0
        zero_count = 0
        for offset in range(WINDOW_WIDTH - lag):
            left_n, left_r, left_w, left_cell = numeric[offset]
            right_n, right_r, right_w, right_cell = numeric[offset + lag]
            delta = left_r * right_w - right_r * left_w
            numerator = 10 * abs(delta)
            denominator = left_w * right_w
            same_cell = left_cell == right_cell
            near = numerator < denominator
            zero = delta == 0
            if same_cell:
                same_count += 1
                if not near:
                    raise _ValidationError("same-cell pair violates the exact near determinant law")
                candidate = (
                    left_n,
                    right_n,
                    numerator,
                    denominator,
                    lag,
                    left_cell,
                )
                if maximum is None:
                    maximum = candidate
                else:
                    comparison = numerator * maximum[3] - maximum[2] * denominator
                    if comparison > 0 or (
                        comparison == 0
                        and (left_n, right_n) < (maximum[0], maximum[1])
                    ):
                        maximum = candidate
            if near:
                near_count += 1
            if zero:
                zero_count += 1
        if not 0 <= same_count <= WINDOW_WIDTH - lag:
            raise _ValidationError("same-cell lag count is out of range")
        if not same_count <= near_count <= WINDOW_WIDTH - lag:
            raise _ValidationError("C_l <= A_l invariant failed")
        if not zero_count <= near_count <= WINDOW_WIDTH - lag:
            raise _ValidationError("Z_l <= A_l invariant failed")
        lag_counts.append(
            {
                "lag": lag,
                "same_cell_count": same_count,
                "near_determinant_count": near_count,
                "zero_determinant_count": zero_count,
            }
        )
        c_sum += same_count
        a_sum += near_count
        z_sum += zero_count

    if maximum is None:
        raise _ValidationError("maximum same-cell ratio domain is empty")
    if j != WINDOW_WIDTH + 2 * c_sum:
        raise _ValidationError("J != 256 + 2*sum(C_l)")

    witness_n, witness_m, numerator, denominator, lag, cell = maximum
    return {
        "schema": WINDOW_SCHEMA,
        "experiment_id": EXPERIMENT_ID,
        "spec_bundle_sha256": SPEC_BUNDLE_SHA256,
        "window_index": index,
        "start_n": start,
        "end_exclusive_n": end,
        "points": checked,
        "cell_counts": {f"n{cell_index}": counts[cell_index] for cell_index in range(10)},
        "j": j,
        "j10_strict_pass": 9 * j < 65536,
        "lag_counts": lag_counts,
        "maximum_determinant_ratio": {
            "num": str(numerator),
            "den": str(denominator),
            "witness_n": witness_n,
            "witness_m": witness_m,
            "lag": lag,
            "cell": cell,
        },
        "decision": _decision(j, c_sum, a_sum, z_sum > 0),
    }


def _validate_window_artifact(
    value: object,
    window_index: object,
    start_n: object,
    end_exclusive_n: object,
    spec_bundle_sha256: object,
) -> None:
    artifact = _require_exact_keys(value, _WINDOW_KEYS, "window artifact")
    recomputed = recompute_window(
        artifact["points"],
        window_index,
        start_n,
        end_exclusive_n,
        spec_bundle_sha256,
    )
    if not _exact_equal(artifact, recomputed):
        raise _ValidationError("window artifact differs from trusted recomputation")
    return None


def validate_window_bytes(
    raw: bytes,
    window_index: object,
    start_n: object,
    end_exclusive_n: object,
    spec_bundle_sha256: object,
) -> dict[str, object]:
    """Return the decoded artifact only after strict decode and recomputation."""
    value = decode_canonical_json(raw)
    _validate_window_artifact(
        value,
        window_index,
        start_n,
        end_exclusive_n,
        spec_bundle_sha256,
    )
    return value


def _validate_cas_binding_fields(value: dict[str, object], label: str) -> None:
    _require_digest(value["artifact_sha256"], label + ".artifact_sha256")
    _require_int(value["size_bytes"], label + ".size_bytes", 0)
    _require_string(value["experiment_id"], label + ".experiment_id")
    _require_digest(value["spec_bundle_sha256"], label + ".spec_bundle_sha256")
    _frozen_window(value["window_index"], value["start_n"], value["end_exclusive_n"])
    if value["experiment_id"] != EXPERIMENT_ID:
        raise _ValidationError(label + " experiment_id mismatch")
    _require_spec_bundle(value["spec_bundle_sha256"])


def validate_cas_record(value: object, expected_bindings: object) -> None:
    record = _require_exact_keys(value, _CAS_KEYS, "CAS record")
    expected = _require_exact_keys(expected_bindings, _CAS_BINDING_KEYS, "CAS expected bindings")
    if record["schema"] != CAS_SCHEMA or record["algorithm"] != "sha256":
        raise _ValidationError("CAS record constants mismatch")
    _validate_cas_binding_fields(record, "CAS record")
    _validate_cas_binding_fields(expected, "CAS expected bindings")
    for key in _CAS_BINDING_KEYS:
        if not _exact_equal(record[key], expected[key]):
            raise _ValidationError("CAS record does not equal controller-supplied bindings")
    return None


def _validate_receipt_binding_fields(value: dict[str, object], label: str) -> None:
    _require_string(value["experiment_id"], label + ".experiment_id")
    for key in (
        "spec_bundle_sha256",
        "artifact_sha256",
        "generator_source_sha256",
        "verifier_source_sha256",
    ):
        _require_digest(value[key], label + "." + key)
    _frozen_window(value["window_index"], value["start_n"], value["end_exclusive_n"])
    if value["experiment_id"] != EXPERIMENT_ID:
        raise _ValidationError(label + " experiment_id mismatch")
    _require_spec_bundle(value["spec_bundle_sha256"])
    if value["verifier_result"] != "accepted":
        raise _ValidationError(label + " verifier_result mismatch")
    gate_id = _require_string(value["controller_gate_id"], label + ".controller_gate_id", True)
    if gate_id == GATE_ID:
        raise _ValidationError("the S0 schema gate is not a production receipt authority")


def validate_receipt(value: object, expected_bindings: object) -> None:
    receipt = _require_exact_keys(value, _RECEIPT_KEYS, "receipt")
    expected = _require_exact_keys(
        expected_bindings, _RECEIPT_BINDING_KEYS, "receipt expected bindings"
    )
    if receipt["schema"] != RECEIPT_SCHEMA:
        raise _ValidationError("receipt schema mismatch")
    _validate_receipt_binding_fields(receipt, "receipt")
    _validate_receipt_binding_fields(expected, "receipt expected bindings")
    for key in _RECEIPT_BINDING_KEYS:
        if not _exact_equal(receipt[key], expected[key]):
            raise _ValidationError("receipt does not equal controller-supplied bindings")
    return None


# Everything below this line is trusted fixture construction.  Controller tests
# copy only the pure API above into their compliant candidate module.
def _round_robin_cells(counts: tuple[int, ...]) -> list[int]:
    if len(counts) != 10 or sum(counts) != WINDOW_WIDTH or any(count < 0 for count in counts):
        raise _ValidationError("synthetic count vector must have ten entries summing to 256")
    remaining = list(counts)
    result: list[int] = []
    while len(result) < WINDOW_WIDTH:
        for cell, count in enumerate(remaining):
            if count:
                result.append(cell)
                remaining[cell] -= 1
    return result


def _make_synthetic_points(
    counts: tuple[int, ...],
    *,
    start_n: int = TEST_START_N,
    near_adjacent_cells: bool,
    duplicate_same_cell_ratio: bool = False,
) -> list[dict[str, object]]:
    scale = 100_000
    denominator = 10 * scale
    ranks = [0] * 10
    points: list[dict[str, object]] = []
    for offset, cell in enumerate(_round_robin_cells(counts)):
        ranks[cell] += 1
        band_offset = ((9 - cell) if near_adjacent_cells else cell) * 1_000
        numerator = cell * scale + band_offset + ranks[cell]
        point: dict[str, object] = {
            "n": start_n + offset,
            "r": str(numerator),
            "w": str(denominator),
            "cell": cell,
        }
        validate_point(point, start_n + offset)
        points.append(point)
    if duplicate_same_cell_ratio:
        first_by_cell: dict[int, dict[str, object]] = {}
        for point in points:
            cell = int(point["cell"])
            prior = first_by_cell.get(cell)
            if prior is None:
                first_by_cell[cell] = point
                continue
            point["r"] = prior["r"]
            point["w"] = prior["w"]
            break
    return points


def _make_precision_cross_product_points() -> list[dict[str, object]]:
    points: list[dict[str, object]] = [
        {"n": TEST_START_N + offset, "r": "0", "w": "1", "cell": 0}
        for offset in range(WINDOW_WIDTH - 2)
    ]
    scale = 10**80
    points.extend(
        [
            {
                "n": TEST_END_EXCLUSIVE_N - 2,
                "r": str(scale - 1),
                "w": str(10 * scale),
                "cell": 0,
            },
            {
                "n": TEST_END_EXCLUSIVE_N - 1,
                "r": str(scale),
                "w": str(10 * (scale + 1)),
                "cell": 0,
            },
        ]
    )
    for offset, point in enumerate(points):
        validate_point(point, TEST_START_N + offset)
    return points


def _ratio_record(
    left: dict[str, object], right: dict[str, object], *, cell: int | None = None
) -> dict[str, object]:
    left_r = _decimal_to_int(str(left["r"]))
    left_w = _decimal_to_int(str(left["w"]))
    right_r = _decimal_to_int(str(right["r"]))
    right_w = _decimal_to_int(str(right["w"]))
    return {
        "num": str(10 * abs(left_r * right_w - right_r * left_w)),
        "den": str(left_w * right_w),
        "witness_n": left["n"],
        "witness_m": right["n"],
        "lag": int(right["n"]) - int(left["n"]),
        "cell": left["cell"] if cell is None else cell,
    }


def _ratio_mutation_vectors(
    go_points: list[dict[str, object]],
    go_artifact: dict[str, object],
    refinement_points: list[dict[str, object]],
) -> dict[str, dict[str, object]]:
    expected = go_artifact["maximum_determinant_ratio"]
    if type(expected) is not dict:
        raise _ValidationError("synthetic maximum ratio is malformed")
    expected_num = int(expected["num"])
    expected_den = int(expected["den"])
    nonmaximum = None
    equal_maximum = None
    for left_index in range(WINDOW_WIDTH):
        for right_index in range(left_index + 1, WINDOW_WIDTH):
            left = go_points[left_index]
            right = go_points[right_index]
            if left["cell"] != right["cell"]:
                continue
            record = _ratio_record(left, right)
            numerator = int(record["num"])
            denominator = int(record["den"])
            comparison = numerator * expected_den - expected_num * denominator
            if comparison < 0 and nonmaximum is None:
                nonmaximum = record
            if comparison == 0 and (
                record["witness_n"], record["witness_m"]
            ) != (expected["witness_n"], expected["witness_m"]):
                equal_maximum = record
            if nonmaximum is not None and equal_maximum is not None:
                break
        if nonmaximum is not None and equal_maximum is not None:
            break
    different_cell_near = None
    for left_index in range(WINDOW_WIDTH):
        for right_index in range(left_index + 1, WINDOW_WIDTH):
            left = refinement_points[left_index]
            right = refinement_points[right_index]
            if left["cell"] == right["cell"]:
                continue
            record = _ratio_record(left, right)
            if int(record["num"]) < int(record["den"]):
                different_cell_near = record
                break
        if different_cell_near is not None:
            break
    if nonmaximum is None or equal_maximum is None or different_cell_near is None:
        raise _ValidationError("controller ratio mutation fixture construction failed")
    first = go_points[0]
    diagonal = _ratio_record(first, first)
    a, b = expected_num, expected_den
    while b:
        a, b = b, a % b
    if a <= 1:
        raise _ValidationError("raw-ratio reduction mutation is unavailable")
    reduced = dict(expected)
    reduced["num"] = str(expected_num // a)
    reduced["den"] = str(expected_den // a)
    return {
        "diagonal": diagonal,
        "different_cell_near": different_cell_near,
        "nonmaximum": nonmaximum,
        "equal_maximum_nonlex": equal_maximum,
        "reduced_surrogate": reduced,
    }


def _seeded_words(seed: bytes, label: str):
    """Yield a replayable controller-private stream derived from one run seed."""
    import hashlib as _hashlib

    counter = 0
    label_bytes = label.encode("ascii")
    while True:
        block = _hashlib.sha256(
            b"pi-t120-s0-hidden-fixture-v1\0"
            + seed
            + len(label_bytes).to_bytes(2, "big")
            + label_bytes
            + counter.to_bytes(8, "big")
        ).digest()
        counter += 1
        for offset in range(0, len(block), 8):
            yield int.from_bytes(block[offset : offset + 8], "big")


def _make_seeded_points(
    counts: tuple[int, ...], *, start_n: int, seed: bytes, label: str
) -> list[dict[str, object]]:
    """Make varied exact point families unknown when candidate source is frozen."""
    cells = [cell for cell, count in enumerate(counts) for _ in range(count)]
    words = _seeded_words(seed, label)
    for index in range(len(cells) - 1, 0, -1):
        swap = next(words) % (index + 1)
        cells[index], cells[swap] = cells[swap], cells[index]

    points: list[dict[str, object]] = []
    for offset, cell in enumerate(cells):
        denominator = 1_000_003 + next(words) % 9_000_000
        lower = (cell * denominator + 9) // 10
        upper = ((cell + 1) * denominator + 9) // 10 - 1
        numerator = lower + next(words) % (upper - lower + 1)
        point: dict[str, object] = {
            "n": start_n + offset,
            "r": str(numerator),
            "w": str(denominator),
            "cell": cell,
        }
        validate_point(point, start_n + offset)
        points.append(point)
    return points


def build_controller_fixture(
    spec_bundle_sha256: str, fixture_seed_hex: str
) -> dict[str, object]:
    """Build deterministic non-BBP positives, mutations, and expected bindings."""
    import hashlib as _hashlib

    if spec_bundle_sha256 != SPEC_BUNDLE_SHA256:
        raise _ValidationError("controller fixture requested for the wrong spec bundle")
    if type(fixture_seed_hex) is not str or _re.fullmatch(
        _LOWER_HEX_64_PATTERN, fixture_seed_hex
    ) is None:
        raise _ValidationError("controller fixture seed must be lowercase 32-byte hex")
    fixture_seed = bytes.fromhex(fixture_seed_hex)
    case_inputs = {
        "balanced_go": ((26, 26, 26, 26, 26, 26, 25, 25, 25, 25), False, False),
        "balanced_refinement_stop": ((26, 26, 26, 26, 26, 26, 25, 25, 25, 25), True, False),
        "balanced_zero_stop": ((26, 26, 26, 26, 26, 26, 25, 25, 25, 25), False, True),
        "full_support_threshold_fail": ((100, 18, 18, 18, 17, 17, 17, 17, 17, 17), False, False),
        "missing_cell_threshold_fail": ((29, 29, 29, 29, 28, 28, 28, 28, 28, 0), False, False),
        "threshold_fail_with_zero_priority": ((100, 18, 18, 18, 17, 17, 17, 17, 17, 17), False, True),
    }
    cases: dict[str, dict[str, object]] = {}
    point_sets: dict[str, list[dict[str, object]]] = {}
    for name, (counts, near_adjacent, duplicate) in case_inputs.items():
        points = _make_synthetic_points(
            counts,
            near_adjacent_cells=near_adjacent,
            duplicate_same_cell_ratio=duplicate,
        )
        artifact = recompute_window(
            points,
            TEST_WINDOW_INDEX,
            TEST_START_N,
            TEST_END_EXCLUSIVE_N,
            spec_bundle_sha256,
        )
        raw = canonical_json_bytes(artifact)
        if not _exact_equal(
            validate_window_bytes(
                raw,
                TEST_WINDOW_INDEX,
                TEST_START_N,
                TEST_END_EXCLUSIVE_N,
                spec_bundle_sha256,
            ),
            artifact,
        ):
            raise _ValidationError("synthetic window round trip failed")
        cases[name] = {"points": points, "artifact": artifact, "raw_ascii": raw.decode("ascii")}
        point_sets[name] = points

    precision_points = _make_precision_cross_product_points()
    precision_artifact = recompute_window(
        precision_points,
        TEST_WINDOW_INDEX,
        TEST_START_N,
        TEST_END_EXCLUSIVE_N,
        spec_bundle_sha256,
    )
    precision_raw = canonical_json_bytes(precision_artifact)
    cases["precision_cross_product"] = {
        "points": precision_points,
        "artifact": precision_artifact,
        "raw_ascii": precision_raw.decode("ascii"),
    }
    precision_loser = _ratio_record(precision_points[0], precision_points[-2])
    precision_winner = precision_artifact["maximum_determinant_ratio"]
    if type(precision_winner) is not dict or not (
        int(precision_loser["num"]) * int(precision_winner["den"])
        < int(precision_winner["num"]) * int(precision_loser["den"])
    ):
        raise _ValidationError("precision cross-product fixture order failed")

    window_cases: list[dict[str, object]] = []
    counts = (26, 26, 26, 26, 26, 26, 25, 25, 25, 25)
    for index in range(WINDOW_COUNT):
        start = FIRST_N + WINDOW_WIDTH * index
        end = start + WINDOW_WIDTH
        points = _make_synthetic_points(counts, start_n=start, near_adjacent_cells=False)
        artifact = recompute_window(points, index, start, end, spec_bundle_sha256)
        window_cases.append(
            {
                "window_index": index,
                "start_n": start,
                "end_exclusive_n": end,
                "points": points,
                "artifact": artifact,
                "raw_ascii": canonical_json_bytes(artifact).decode("ascii"),
            }
        )

    hidden_cases: list[dict[str, object]] = []
    hidden_counts = (
        (26, 26, 26, 26, 26, 26, 25, 25, 25, 25),
        (28, 27, 27, 26, 26, 25, 25, 24, 24, 24),
        (30, 29, 28, 27, 26, 25, 24, 23, 22, 22),
        (27, 27, 26, 26, 26, 25, 25, 25, 25, 24),
    )
    for ordinal, (index, counts_row) in enumerate(zip((1, 4, 8, 12), hidden_counts)):
        start = FIRST_N + WINDOW_WIDTH * index
        end = start + WINDOW_WIDTH
        points = _make_seeded_points(
            counts_row,
            start_n=start,
            seed=fixture_seed,
            label=f"hidden-{ordinal}-window-{index}",
        )
        artifact = recompute_window(points, index, start, end, spec_bundle_sha256)
        hidden_cases.append(
            {
                "window_index": index,
                "start_n": start,
                "end_exclusive_n": end,
                "points": points,
                "artifact": artifact,
                "raw_ascii": canonical_json_bytes(artifact).decode("ascii"),
            }
        )

    go_raw = cases["balanced_go"]["raw_ascii"].encode("ascii")
    artifact_sha256 = _hashlib.sha256(go_raw).hexdigest()
    cas_bindings: dict[str, object] = {
        "artifact_sha256": artifact_sha256,
        "size_bytes": len(go_raw),
        "experiment_id": EXPERIMENT_ID,
        "spec_bundle_sha256": spec_bundle_sha256,
        "window_index": TEST_WINDOW_INDEX,
        "start_n": TEST_START_N,
        "end_exclusive_n": TEST_END_EXCLUSIVE_N,
    }
    cas_record = {"schema": CAS_SCHEMA, "algorithm": "sha256", **cas_bindings}
    receipt_bindings: dict[str, object] = {
        "experiment_id": EXPERIMENT_ID,
        "spec_bundle_sha256": spec_bundle_sha256,
        "window_index": TEST_WINDOW_INDEX,
        "start_n": TEST_START_N,
        "end_exclusive_n": TEST_END_EXCLUSIVE_N,
        "artifact_sha256": artifact_sha256,
        "generator_source_sha256": "1" * 64,
        "verifier_source_sha256": "2" * 64,
        "verifier_result": "accepted",
        "controller_gate_id": "synthetic-production-controller-v1",
    }
    receipt = {"schema": RECEIPT_SCHEMA, **receipt_bindings}
    validate_cas_record(cas_record, cas_bindings)
    validate_receipt(receipt, receipt_bindings)
    return {
        "schema": FIXTURE_SCHEMA,
        "fixture_seed_sha256": _hashlib.sha256(fixture_seed).hexdigest(),
        "spec_bundle_sha256": spec_bundle_sha256,
        "window_index": TEST_WINDOW_INDEX,
        "start_n": TEST_START_N,
        "end_exclusive_n": TEST_END_EXCLUSIVE_N,
        "limits": {
            "candidate_source_max_bytes": CANDIDATE_SOURCE_MAX_BYTES,
            "report_max_bytes": REPORT_MAX_BYTES,
            "canonical_raw_max_bytes": CANONICAL_RAW_MAX_BYTES,
            "json_max_nesting_depth": JSON_MAX_NESTING_DEPTH,
            "json_max_array_items": JSON_MAX_ARRAY_ITEMS,
            "json_max_object_keys": JSON_MAX_OBJECT_KEYS,
            "canonical_integer_string_max_digits": INTEGER_STRING_MAX_DIGITS,
        },
        "cases": cases,
        "window_cases": window_cases,
        "hidden_cases": hidden_cases,
        "ratio_mutation_vectors": _ratio_mutation_vectors(
            point_sets["balanced_go"],
            cases["balanced_go"]["artifact"],
            point_sets["balanced_refinement_stop"],
        ),
        "precision_ratio_loser": precision_loser,
        "cas_record": cas_record,
        "cas_expected_bindings": cas_bindings,
        "receipt": receipt,
        "receipt_expected_bindings": receipt_bindings,
    }
