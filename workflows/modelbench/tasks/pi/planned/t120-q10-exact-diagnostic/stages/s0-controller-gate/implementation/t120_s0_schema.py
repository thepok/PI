"""T120 S0 bounded pure validation library.

Strict canonical-byte JSON decoding, exact schema/binding validation, and
integer-only recomputation over supplied normalized point records for one
frozen q=10 window. This module implements no BBP terms, no T118 recurrence
arithmetic, no provenance authentication, no filesystem/CAS/receipt effects,
no subprocess/network/randomness/floats/reflection, and retains no state.

T118 r,w provenance is deferred to a later disjoint arithmetic verifier;
S0 authenticates only the exact consecutive n metadata of a frozen window.
"""

import json

_EXPERIMENT_ID = "pi-q10-j10-lag-determinant-20260822-v1"
_SCHEMA_WINDOW = "pi-q10-window-v1"
_SCHEMA_CAS = "pi-q10-cas-record-v1"
_SCHEMA_RECEIPT = "pi-q10-controller-receipt-v1"
_SPEC_BUNDLE_SHA256 = (
    "fe180d8a5db818d3b4a9b3931779b3cc3d313a2437e9f4db808f3afecba51f98"
)

_FROZEN_WINDOWS = (
    (0, 512, 768),
    (1, 768, 1024),
    (2, 1024, 1280),
    (3, 1280, 1536),
    (4, 1536, 1792),
    (5, 1792, 2048),
    (6, 2048, 2304),
    (7, 2304, 2560),
    (8, 2560, 2816),
    (9, 2816, 3072),
    (10, 3072, 3328),
    (11, 3328, 3584),
    (12, 3584, 3840),
    (13, 3840, 4096),
)

_MAX_RAW_BYTES = 268435456
_MAX_DEPTH = 32
_MAX_ARRAY_ITEMS = 2048
_MAX_OBJECT_KEYS = 64
_MAX_INT_DIGITS = 2000000

_WINDOW_POINT_COUNT = 256
_LAG_COUNT = 255
_J_THRESHOLD_NUM = 65536
_J_STRICT_MULT = 9
_A_SUM_GO_MAX = 3512

_ACTION_STOP_LOCAL_CONJECTURE = "stop_local_conjecture"
_ACTION_STOP_AUDIT_ZERO = "stop_audit_zero"
_ACTION_GO_HOLDOUTS = "go_holdouts"
_ACTION_STOP_DETERMINANT_ROUTE = (
    "stop_determinant_route_pending_optional_refinement"
)

_HEX_LOWER = "0123456789abcdef"
_DIGITS = "0123456789"
_LEADING = "123456789"

_POINT_KEYS = ("cell", "n", "r", "w")
_LAG_KEYS = (
    "lag",
    "near_determinant_count",
    "same_cell_count",
    "zero_determinant_count",
)
_CELL_COUNT_KEYS = (
    "n0", "n1", "n2", "n3", "n4", "n5", "n6", "n7", "n8", "n9",
)
_RATIO_KEYS = (
    "cell",
    "den",
    "lag",
    "num",
    "witness_m",
    "witness_n",
)
_DECISION_KEYS = (
    "a_sum",
    "c_sum",
    "has_zero_distinct_pair",
    "j_threshold_pass",
    "window13_action",
)
_ARTIFACT_KEYS = (
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


def _reject_noncanonical(msg):
    raise ValueError(msg)


def _reject_float(_token):
    raise ValueError("float tokens are not permitted")


def _reject_constant(_token):
    raise ValueError("NaN/Infinity tokens are not permitted")


def _require(cond, msg):
    if not cond:
        raise ValueError(msg)


def _is_plain_int(value):
    return type(value) is int


def _is_plain_bool(value):
    return type(value) is bool


def _is_plain_str(value):
    return type(value) is str


def _str_has_chars(text, allowed):
    for ch in text:
        if ch not in allowed:
            return False
    return True


def _keys_exact(container, expected):
    keys = sorted(container.keys())
    if len(keys) != len(expected):
        return False
    for index, key in enumerate(keys):
        if key != expected[index]:
            return False
    return True


def _check_hex64(value, label):
    _require(
        _is_plain_str(value)
        and len(value) == 64
        and _str_has_chars(value, _HEX_LOWER),
        "%s must be a lowercase 64-hex string" % label,
    )


def _check_uint_string(value, label):
    _require(_is_plain_str(value), "%s must be a string" % label)
    _require(len(value) <= _MAX_INT_DIGITS, "%s exceeds digit limit" % label)
    if value == "":
        _reject_noncanonical("%s is empty" % label)
    if value[0] == "0":
        _require(value == "0", "%s has a leading zero" % label)
    else:
        _require(
            value[0] in _LEADING and _str_has_chars(value, _DIGITS),
            "%s is not a canonical nonnegative integer string" % label,
        )


def _decimal_to_int(value):
    """Convert one canonical JSON/unsigned decimal in bounded chunks."""
    negative = value.startswith("-")
    digits = value[1:] if negative else value
    result = 0
    first = len(digits) % 9
    index = 0
    if first:
        result = int(digits[:first])
        index = first
    while index < len(digits):
        result = result * 1000000000 + int(digits[index:index + 9])
        index += 9
    if negative:
        return -result
    return result


def _check_json_value(value, depth):
    kind = type(value)
    if kind is list or kind is dict:
        _require(depth < _MAX_DEPTH, "nesting depth exceeds limit")
        if kind is list:
            _require(
                len(value) <= _MAX_ARRAY_ITEMS, "array item limit exceeded"
            )
            for item in value:
                _check_json_value(item, depth + 1)
        else:
            _require(
                len(value) <= _MAX_OBJECT_KEYS, "object key limit exceeded"
            )
            for key, item in value.items():
                _require(_is_plain_str(key), "object key must be a string")
                _check_json_value(item, depth + 1)
        return
    if kind is int:
        _require(
            len(str(abs(value))) <= _MAX_INT_DIGITS,
            "integer exceeds digit limit",
        )
        return
    if kind is str or kind is bool or value is None:
        return
    _reject_noncanonical("value is outside the supported JSON domain")


def _strict_pairs(pairs):
    result = {}
    for key, item in pairs:
        if key in result:
            _reject_noncanonical("duplicate object key %r" % key)
        result[key] = item
    return result


def _same_value(left, right):
    left_kind = type(left)
    if left_kind is not type(right):
        return False
    if left_kind is dict:
        if left.keys() != right.keys():
            return False
        return all(_same_value(left[key], right[key]) for key in left)
    if left_kind is list:
        if len(left) != len(right):
            return False
        return all(
            _same_value(a, b) for a, b in zip(left, right)
        )
    return left == right


def _bind_window_args(window_index, start_n, end_exclusive_n,
                      spec_bundle_sha256):
    _require(
        _is_plain_int(window_index)
        and _is_plain_int(start_n)
        and _is_plain_int(end_exclusive_n),
        "window arguments must be JSON integers",
    )
    _require(
        _is_plain_str(spec_bundle_sha256),
        "spec_bundle_sha256 must be a string",
    )
    _require(
        spec_bundle_sha256 == _SPEC_BUNDLE_SHA256,
        "spec_bundle_sha256 does not equal the frozen bundle digest",
    )
    for row_index, row_start, row_end in _FROZEN_WINDOWS:
        if (window_index == row_index
                and start_n == row_start
                and end_exclusive_n == row_end):
            return
    _reject_noncanonical(
        "(window_index, start_n, end_exclusive_n) is not a frozen window row"
    )


def canonical_json_bytes(value):
    """Return compact sorted-key ensure_ascii ASCII JSON bytes plus one LF."""
    _check_json_value(value, 0)
    text = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    )
    raw = text.encode("ascii") + b"\n"
    _require(len(raw) <= _MAX_RAW_BYTES, "encoded value exceeds raw byte limit")
    return raw


def _check_nesting_depth(text):
    depth = 0
    length = len(text)
    index = 0
    while index < length:
        ch = text[index]
        if ch == '"':
            index += 1
            while index < length:
                inner = text[index]
                if inner == "\\":
                    index += 2
                    continue
                if inner == '"':
                    break
                index += 1
        elif ch == "[" or ch == "{":
            depth += 1
            _require(
                depth <= _MAX_DEPTH, "nesting depth exceeds limit"
            )
        elif ch == "]" or ch == "}":
            depth -= 1
            if depth < 0:
                return
        index += 1


def decode_canonical_json(raw):
    """Decode strict canonical raw JSON bytes and return the parsed value."""
    _require(type(raw) is bytes, "input must be exact built-in bytes")
    _require(len(raw) <= _MAX_RAW_BYTES, "input exceeds the raw byte limit")
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError:
        _reject_noncanonical("input is not valid UTF-8")
    _require(not text.startswith("\ufeff"), "input begins with a UTF-8 BOM")
    _check_nesting_depth(text)
    try:
        value = json.loads(
            text,
            parse_float=_reject_float,
            parse_constant=_reject_constant,
            object_pairs_hook=_strict_pairs,
            parse_int=_decimal_to_int,
        )
    except RecursionError:
        _reject_noncanonical("parser recursion bomb")
    _check_json_value(value, 0)
    _require(
        raw == canonical_json_bytes(value),
        "raw bytes are not exactly canonical",
    )
    return value


def validate_point(value, expected_n):
    """Validate one normalized point record; return None on acceptance."""
    _require(
        _is_plain_int(expected_n), "expected_n must be a JSON integer"
    )
    _require(type(value) is dict, "point must be a JSON object")
    _require(_keys_exact(value, _POINT_KEYS), "point keys are wrong")
    n = value["n"]
    cell = value["cell"]
    _require(_is_plain_int(n), "point n must be a JSON integer")
    _require(
        not _is_plain_bool(n), "point n must not be a boolean"
    )
    _require(_is_plain_int(cell), "point cell must be a JSON integer")
    _require(
        not _is_plain_bool(cell), "point cell must not be a boolean"
    )
    _check_uint_string(value["r"], "point r")
    _check_uint_string(value["w"], "point w")
    r = _decimal_to_int(value["r"])
    w = _decimal_to_int(value["w"])
    _require(n == expected_n, "point n does not equal expected_n")
    _require(w > 0, "point w must be positive")
    _require(0 <= r < w, "point r must satisfy 0 <= r < w")
    _require(
        cell == (10 * r) // w, "point cell is not Int.ediv (10*r) w"
    )
    _require(0 <= cell < 10, "point cell must lie in 0..9")
    return None


def _recompute_statistics(points, start_n):
    r_values = []
    w_values = []
    cells = []
    counts = [0] * 10
    for point in points:
        r = _decimal_to_int(point["r"])
        w = _decimal_to_int(point["w"])
        r_values.append(r)
        w_values.append(w)
        cells.append(point["cell"])
        counts[point["cell"]] += 1
    j_value = 0
    for count in counts:
        j_value += count * count
    j_threshold_pass = (
        _J_STRICT_MULT * j_value < _J_THRESHOLD_NUM
    )

    lag_records = []
    c_sum = 0
    a_sum = 0
    has_zero_distinct_pair = False
    for lag in range(1, _LAG_COUNT + 1):
        same_cell = 0
        near = 0
        zero = 0
        for idx in range(_WINDOW_POINT_COUNT - lag):
            if cells[idx] == cells[idx + lag]:
                same_cell += 1
            delta = r_values[idx] * w_values[idx + lag]
            delta -= r_values[idx + lag] * w_values[idx]
            if delta < 0:
                delta = -delta
            if 10 * delta < w_values[idx] * w_values[idx + lag]:
                near += 1
            if r_values[idx] * w_values[idx + lag] \
                    == r_values[idx + lag] * w_values[idx]:
                zero += 1
        c_sum += same_cell
        a_sum += near
        if zero > 0:
            has_zero_distinct_pair = True
        lag_records.append(
            {
                "lag": lag,
                "same_cell_count": same_cell,
                "near_determinant_count": near,
                "zero_determinant_count": zero,
            }
        )

    best_num = None
    best_den = None
    best_pair = None
    for idx in range(_WINDOW_POINT_COUNT):
        for other in range(idx + 1, _WINDOW_POINT_COUNT):
            if cells[idx] != cells[other]:
                continue
            num = 10 * abs(
                r_values[idx] * w_values[other]
                - r_values[other] * w_values[idx]
            )
            den = w_values[idx] * w_values[other]
            if best_num is None or num * best_den > best_num * den:
                best_num = num
                best_den = den
                best_pair = (start_n + idx, start_n + other)
    _require(best_pair is not None, "no distinct same-cell pair exists")

    if not j_threshold_pass:
        action = _ACTION_STOP_LOCAL_CONJECTURE
    elif has_zero_distinct_pair:
        action = _ACTION_STOP_AUDIT_ZERO
    elif a_sum <= _A_SUM_GO_MAX:
        action = _ACTION_GO_HOLDOUTS
    else:
        action = _ACTION_STOP_DETERMINANT_ROUTE

    cell_counts = {}
    for cell in range(10):
        cell_counts[_CELL_COUNT_KEYS[cell]] = counts[cell]

    decision = {
        "j_threshold_pass": j_threshold_pass,
        "c_sum": c_sum,
        "a_sum": a_sum,
        "has_zero_distinct_pair": has_zero_distinct_pair,
        "window13_action": action,
    }
    maximum_ratio = {
        "num": str(best_num),
        "den": str(best_den),
        "witness_n": best_pair[0],
        "witness_m": best_pair[1],
        "lag": best_pair[1] - best_pair[0],
        "cell": cells[best_pair[0] - start_n],
    }
    return cell_counts, j_value, j_threshold_pass, lag_records, \
        maximum_ratio, decision


def _copy_point(point):
    return {
        "n": point["n"],
        "r": point["r"],
        "w": point["w"],
        "cell": point["cell"],
    }


def _build_artifact(points, window_index, start_n, end_exclusive_n,
                    spec_bundle_sha256):
    cell_counts, j_value, j_pass, lag_records, maximum_ratio, decision = (
        _recompute_statistics(points, start_n)
    )
    return {
        "schema": _SCHEMA_WINDOW,
        "experiment_id": _EXPERIMENT_ID,
        "spec_bundle_sha256": spec_bundle_sha256,
        "window_index": window_index,
        "start_n": start_n,
        "end_exclusive_n": end_exclusive_n,
        "points": [_copy_point(point) for point in points],
        "cell_counts": cell_counts,
        "j": j_value,
        "j10_strict_pass": j_pass,
        "lag_counts": lag_records,
        "maximum_determinant_ratio": maximum_ratio,
        "decision": decision,
    }


def _validate_points_argument(points, start_n):
    _require(type(points) is list, "points must be a JSON array")
    _require(
        len(points) == _WINDOW_POINT_COUNT,
        "points must contain exactly %d records" % _WINDOW_POINT_COUNT,
    )
    for offset, point in enumerate(points):
        validate_point(point, start_n + offset)


def recompute_window(points, window_index, start_n, end_exclusive_n,
                     spec_bundle_sha256):
    """Return a newly allocated complete recomputed window artifact."""
    _bind_window_args(
        window_index, start_n, end_exclusive_n, spec_bundle_sha256
    )
    _validate_points_argument(points, start_n)
    return _build_artifact(
        points, window_index, start_n, end_exclusive_n, spec_bundle_sha256
    )


def _check_struct_artifact(value, window_index, start_n, end_exclusive_n,
                           spec_bundle_sha256):
    _require(type(value) is dict, "artifact must be a JSON object")
    _require(
        _keys_exact(value, _ARTIFACT_KEYS),
        "artifact keys are not the exact required set",
    )
    _require(
        value["schema"] == _SCHEMA_WINDOW and _is_plain_str(value["schema"]),
        "artifact schema constant is wrong",
    )
    _require(
        value["experiment_id"] == _EXPERIMENT_ID
        and _is_plain_str(value["experiment_id"]),
        "artifact experiment_id constant is wrong",
    )
    _require(
        value["spec_bundle_sha256"] == spec_bundle_sha256
        and _is_plain_str(value["spec_bundle_sha256"]),
        "artifact spec_bundle_sha256 does not match the argument",
    )
    for field, expected in (
        ("window_index", window_index),
        ("start_n", start_n),
        ("end_exclusive_n", end_exclusive_n),
    ):
        stored = value[field]
        _require(
            _is_plain_int(stored) and not _is_plain_bool(stored),
            "artifact %s must be a JSON integer" % field,
        )
        _require(
            stored == expected,
            "artifact %s does not match the argument" % field,
        )
    _validate_points_argument(value["points"], start_n)

    cell_counts = value["cell_counts"]
    _require(
        type(cell_counts) is dict
        and tuple(sorted(cell_counts.keys())) == _CELL_COUNT_KEYS,
        "cell_counts keys are not exactly n0..n9",
    )
    total = 0
    for key in _CELL_COUNT_KEYS:
        count = cell_counts[key]
        _require(
            _is_plain_int(count) and not _is_plain_bool(count) and count >= 0,
            "cell count %s must be a nonnegative JSON integer" % key,
        )
        total += count
    _require(total == _WINDOW_POINT_COUNT, "cell counts do not sum to 256")

    j_stored = value["j"]
    _require(
        _is_plain_int(j_stored) and not _is_plain_bool(j_stored),
        "j must be a JSON integer",
    )
    _require(
        _is_plain_bool(value["j10_strict_pass"]),
        "j10_strict_pass must be a JSON boolean",
    )

    lag_counts = value["lag_counts"]
    _require(
        type(lag_counts) is list and len(lag_counts) == _LAG_COUNT,
        "lag_counts must contain exactly 255 records",
    )
    for offset, record in enumerate(lag_counts):
        lag_expected = offset + 1
        _require(
            type(record) is dict
            and _keys_exact(record, _LAG_KEYS),
            "lag record %d has wrong keys" % lag_expected,
        )
        bound = _WINDOW_POINT_COUNT - lag_expected
        fields = {}
        for field in (
            "lag", "same_cell_count", "near_determinant_count",
            "zero_determinant_count",
        ):
            item = record[field]
            _require(
                _is_plain_int(item) and not _is_plain_bool(item),
                "lag %d field %s must be a JSON integer" % (lag_expected,
                                                            field),
            )
            fields[field] = item
        _require(
            fields["lag"] == lag_expected,
            "lag records are not exactly ordered 1..255",
        )
        for name in ("same_cell_count", "near_determinant_count",
                     "zero_determinant_count"):
            _require(
                0 <= fields[name] <= bound,
                "lag %d %s is out of range" % (lag_expected, name),
            )
        _require(
            fields["same_cell_count"] <= fields["near_determinant_count"],
            "lag %d violates C_l <= A_l" % lag_expected,
        )
        _require(
            fields["zero_determinant_count"]
            <= fields["near_determinant_count"],
            "lag %d violates Z_l <= A_l" % lag_expected,
        )

    ratio = value["maximum_determinant_ratio"]
    _require(
        type(ratio) is dict and _keys_exact(ratio, _RATIO_KEYS),
        "maximum_determinant_ratio keys are wrong",
    )
    _check_uint_string(ratio["num"], "ratio num")
    _check_uint_string(ratio["den"], "ratio den")
    for field in ("witness_n", "witness_m", "lag", "cell"):
        item = ratio[field]
        _require(
            _is_plain_int(item) and not _is_plain_bool(item),
            "ratio %s must be a JSON integer" % field,
        )
    ratio_num = _decimal_to_int(ratio["num"])
    ratio_den = _decimal_to_int(ratio["den"])
    _require(ratio_den > 0, "ratio den must be positive")
    _require(
        ratio_num < ratio_den, "ratio must satisfy num < den"
    )
    _require(
        ratio["lag"] == ratio["witness_m"] - ratio["witness_n"],
        "ratio lag does not equal witness_m - witness_n",
    )
    _require(
        0 <= ratio["cell"] < 10, "ratio cell must lie in 0..9"
    )
    _require(
        start_n <= ratio["witness_n"] < ratio["witness_m"]
        < end_exclusive_n,
        "ratio witnesses are not inside the window in order",
    )

    decision = value["decision"]
    _require(
        type(decision) is dict
        and _keys_exact(decision, _DECISION_KEYS),
        "decision keys are wrong",
    )
    for field in ("j_threshold_pass", "has_zero_distinct_pair"):
        _require(
            _is_plain_bool(decision[field]),
            "decision %s must be a JSON boolean" % field,
        )
    for field in ("c_sum", "a_sum"):
        item = decision[field]
        _require(
            _is_plain_int(item) and not _is_plain_bool(item) and item >= 0,
            "decision %s must be a nonnegative JSON integer" % field,
        )
    _require(
        _is_plain_str(decision["window13_action"])
        and decision["window13_action"]
        in (
            _ACTION_STOP_LOCAL_CONJECTURE,
            _ACTION_STOP_AUDIT_ZERO,
            _ACTION_GO_HOLDOUTS,
            _ACTION_STOP_DETERMINANT_ROUTE,
        ),
        "decision window13_action is not an exact permitted action",
    )


def validate_window_bytes(raw, window_index, start_n, end_exclusive_n,
                          spec_bundle_sha256):
    """Strictly decode, recompute, and match a complete window artifact."""
    _bind_window_args(
        window_index, start_n, end_exclusive_n, spec_bundle_sha256
    )
    value = decode_canonical_json(raw)
    _check_struct_artifact(
        value, window_index, start_n, end_exclusive_n, spec_bundle_sha256
    )
    expected = _build_artifact(
        value["points"], window_index, start_n, end_exclusive_n,
        spec_bundle_sha256,
    )
    _require(
        _same_value(value, expected),
        "stored derived fields do not equal exact recomputation",
    )
    return value


def _check_nonneg_int_field(container, field, label):
    item = container[field]
    _require(
        _is_plain_int(item) and not _is_plain_bool(item) and item >= 0,
        "%s must be a nonnegative JSON integer" % label,
    )


def validate_cas_record(value, expected_bindings):
    """Validate the exact CAS record schema and expected bindings."""
    _require(type(value) is dict, "CAS record must be a JSON object")
    _require(
        type(expected_bindings) is dict,
        "expected bindings must be a JSON object",
    )
    _require(
        _keys_exact(value, _CAS_KEYS),
        "CAS record keys are not the exact required set",
    )
    _require(
        _is_plain_str(value["schema"]) and value["schema"] == _SCHEMA_CAS,
        "CAS record schema constant is wrong",
    )
    _require(
        _is_plain_str(value["algorithm"])
        and value["algorithm"] == "sha256",
        "CAS record algorithm constant is wrong",
    )
    _check_hex64(value["artifact_sha256"], "CAS artifact_sha256")
    _check_hex64(value["spec_bundle_sha256"], "CAS spec_bundle_sha256")
    _require(
        _is_plain_str(value["experiment_id"]),
        "CAS experiment_id must be a string",
    )
    for field in ("size_bytes", "window_index", "start_n",
                  "end_exclusive_n"):
        _check_nonneg_int_field(value, field, "CAS %s" % field)
    _require(
        value["experiment_id"] == _EXPERIMENT_ID,
        "CAS experiment_id is not the frozen experiment",
    )
    _bind_window_args(
        value["window_index"], value["start_n"],
        value["end_exclusive_n"], value["spec_bundle_sha256"],
    )
    _require(
        _keys_exact(expected_bindings, _CAS_BINDING_KEYS),
        "CAS expected bindings do not have the exact key set",
    )
    _check_hex64(
        expected_bindings["artifact_sha256"],
        "binding artifact_sha256",
    )
    _check_hex64(
        expected_bindings["spec_bundle_sha256"],
        "binding spec_bundle_sha256",
    )
    _require(
        _is_plain_str(expected_bindings["experiment_id"]),
        "binding experiment_id must be a string",
    )
    for field in ("size_bytes", "window_index", "start_n",
                  "end_exclusive_n"):
        _check_nonneg_int_field(
            expected_bindings, field, "binding %s" % field
        )
    _require(
        expected_bindings["experiment_id"] == _EXPERIMENT_ID,
        "CAS binding experiment_id is not the frozen experiment",
    )
    _bind_window_args(
        expected_bindings["window_index"], expected_bindings["start_n"],
        expected_bindings["end_exclusive_n"],
        expected_bindings["spec_bundle_sha256"],
    )
    for field in sorted(_CAS_BINDING_KEYS):
        _require(
            value[field] == expected_bindings[field],
            "CAS field %s does not equal the expected binding" % field,
        )
    return None


def validate_receipt(value, expected_bindings):
    """Validate the exact receipt schema and expected bindings."""
    _require(type(value) is dict, "receipt must be a JSON object")
    _require(
        type(expected_bindings) is dict,
        "expected bindings must be a JSON object",
    )
    _require(
        _keys_exact(value, _RECEIPT_KEYS),
        "receipt keys are not the exact required set",
    )
    _require(
        _is_plain_str(value["schema"])
        and value["schema"] == _SCHEMA_RECEIPT,
        "receipt schema constant is wrong",
    )
    _require(
        _is_plain_str(value["verifier_result"])
        and value["verifier_result"] == "accepted",
        "receipt verifier_result constant is wrong",
    )
    _require(
        _is_plain_str(value["experiment_id"]),
        "receipt experiment_id must be a string",
    )
    _require(
        _is_plain_str(value["controller_gate_id"]),
        "receipt controller_gate_id must be a string",
    )
    _require(
        value["experiment_id"] == _EXPERIMENT_ID,
        "receipt experiment_id is not the frozen experiment",
    )
    _require(
        value["controller_gate_id"] != ""
        and value["controller_gate_id"] != "t120_s0_schema_v1",
        "receipt controller_gate_id has no production authority",
    )
    for field in (
        "spec_bundle_sha256",
        "artifact_sha256",
        "generator_source_sha256",
        "verifier_source_sha256",
    ):
        _check_hex64(value[field], "receipt %s" % field)
    for field in ("window_index", "start_n", "end_exclusive_n"):
        _check_nonneg_int_field(value, field, "receipt %s" % field)
    _bind_window_args(
        value["window_index"], value["start_n"],
        value["end_exclusive_n"], value["spec_bundle_sha256"],
    )
    _require(
        _keys_exact(expected_bindings, _RECEIPT_BINDING_KEYS),
        "receipt expected bindings do not have the exact key set",
    )
    for field in (
        "spec_bundle_sha256",
        "artifact_sha256",
        "generator_source_sha256",
        "verifier_source_sha256",
    ):
        _check_hex64(expected_bindings[field], "binding %s" % field)
    _require(
        _is_plain_str(expected_bindings["experiment_id"]),
        "binding experiment_id must be a string",
    )
    _require(
        _is_plain_str(expected_bindings["controller_gate_id"]),
        "binding controller_gate_id must be a string",
    )
    _require(
        _is_plain_str(expected_bindings["verifier_result"]),
        "binding verifier_result must be a string",
    )
    _require(
        expected_bindings["experiment_id"] == _EXPERIMENT_ID,
        "receipt binding experiment_id is not the frozen experiment",
    )
    _require(
        expected_bindings["verifier_result"] == "accepted",
        "receipt binding verifier_result is not accepted",
    )
    _require(
        expected_bindings["controller_gate_id"] != ""
        and expected_bindings["controller_gate_id"] != "t120_s0_schema_v1",
        "receipt binding controller_gate_id has no production authority",
    )
    for field in ("window_index", "start_n", "end_exclusive_n"):
        _check_nonneg_int_field(
            expected_bindings, field, "binding %s" % field
        )
    _bind_window_args(
        expected_bindings["window_index"], expected_bindings["start_n"],
        expected_bindings["end_exclusive_n"],
        expected_bindings["spec_bundle_sha256"],
    )
    for field in sorted(_RECEIPT_BINDING_KEYS):
        _require(
            value[field] == expected_bindings[field],
            "receipt field %s does not equal the expected binding" % field,
        )
    return None
