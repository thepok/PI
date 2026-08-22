"""Isolated controller-owned mutation harness for the T120 S0 schema gate.

The candidate module is untrusted.  This harness owns every fixture, mutation,
comparison, and verdict.  It performs no BBP arithmetic, no filesystem write,
no CAS operation, and no receipt minting.
"""

from __future__ import annotations

import contextlib
import copy
import gc
import importlib.util
import io
import json
from pathlib import Path
import sys
from typing import Any, Callable


PASS_MARKER = "T120_S0_CONTROLLER_MUTATIONS_PASSED"
MINIMUM_REJECTION_CHECKS = 360
_rejection_checks = 0
REQUIRED_API = (
    "canonical_json_bytes",
    "decode_canonical_json",
    "validate_point",
    "recompute_window",
    "validate_window_bytes",
    "validate_cas_record",
    "validate_receipt",
)
WINDOW_KEYS = {
    "schema",
    "experiment_id",
    "spec_bundle_sha256",
    "window_index",
    "start_n",
    "end_exclusive_n",
    "points",
    "cell_counts",
    "j",
    "j10_strict_pass",
    "lag_counts",
    "maximum_determinant_ratio",
    "decision",
}
RATIO_KEYS = {"num", "den", "witness_n", "witness_m", "lag", "cell"}
DECISION_KEYS = {
    "j_threshold_pass",
    "c_sum",
    "a_sum",
    "has_zero_distinct_pair",
    "window13_action",
}


def _exact_equal(left: Any, right: Any) -> bool:
    if type(left) is not type(right):
        return False
    if type(left) is dict:
        return set(left) == set(right) and all(
            _exact_equal(left[key], right[key]) for key in left
        )
    if type(left) is list:
        return len(left) == len(right) and all(
            _exact_equal(a, b) for a, b in zip(left, right)
        )
    if type(left) is float and left != left and right != right:
        return True
    return left == right


def _snapshot(value: Any) -> Any:
    if type(value) is memoryview:
        return memoryview(value.tobytes())
    return copy.deepcopy(value)


def _assert_unchanged(before: Any, after: Any, label: str) -> None:
    if not _exact_equal(before, after):
        raise AssertionError(f"candidate mutated controller input: {label}")


def _accepts(
    function: Callable[..., Any],
    *arguments: Any,
    label: str,
    expected_result: Any = None,
    compare_result: bool = False,
) -> Any:
    snapshots = [_snapshot(argument) for argument in arguments]
    result = function(*arguments)
    for index, (before, after) in enumerate(zip(snapshots, arguments)):
        _assert_unchanged(before, after, f"{label} argument {index}")
    if compare_result and not _exact_equal(result, expected_result):
        raise AssertionError(f"candidate returned wrong result: {label}")
    return result


def _rejects(
    function: Callable[..., Any],
    *arguments: Any,
    label: str,
) -> None:
    global _rejection_checks
    _rejection_checks += 1
    snapshots = [_snapshot(argument) for argument in arguments]
    try:
        function(*arguments)
    except ValueError:
        for index, (before, after) in enumerate(zip(snapshots, arguments)):
            _assert_unchanged(before, after, f"{label} argument {index}")
        return
    except Exception as exc:
        raise AssertionError(
            f"candidate rejected with {type(exc).__name__}, not ValueError: {label}"
        ) from exc
    for index, (before, after) in enumerate(zip(snapshots, arguments)):
        _assert_unchanged(before, after, f"{label} argument {index}")
    raise AssertionError(f"mutation accepted: {label}")


def _change(value: Any, path: list[Any], replacement: Any) -> Any:
    changed = copy.deepcopy(value)
    target = changed
    for component in path[:-1]:
        target = target[component]
    target[path[-1]] = replacement
    if _exact_equal(changed, value):
        raise AssertionError(f"controller mutation was a no-op: {path!r}")
    return changed


def _delete(value: Any, path: list[Any]) -> Any:
    changed = copy.deepcopy(value)
    target = changed
    for component in path[:-1]:
        target = target[component]
    del target[path[-1]]
    return changed


def _load_candidate(path: Path) -> Any:
    spec = importlib.util.spec_from_file_location("candidate_t120_s0_schema", path)
    if spec is None or spec.loader is None:
        raise AssertionError("cannot create candidate module spec")
    module = importlib.util.module_from_spec(spec)
    stdout = io.StringIO()
    stderr = io.StringIO()
    with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
        spec.loader.exec_module(module)
    if stdout.getvalue() or stderr.getvalue():
        raise AssertionError("candidate performed import-time output")
    public_callables = {
        name for name, value in vars(module).items()
        if not name.startswith("_") and callable(value)
    }
    if public_callables != set(REQUIRED_API):
        raise AssertionError(
            "wrong exact non-underscore callable API: " + repr(sorted(public_callables))
        )
    return module


def _load_fixture(path: Path) -> dict[str, Any]:
    with path.open("r", encoding="ascii", newline="") as handle:
        fixture = json.load(handle)
    if type(fixture) is not dict or fixture.get("schema") != "pi-t120-s0-controller-fixture-v3":
        raise AssertionError("invalid trusted controller fixture")
    seed_digest = fixture.get("fixture_seed_sha256")
    if (
        type(seed_digest) is not str
        or len(seed_digest) != 64
        or any(char not in "0123456789abcdef" for char in seed_digest)
    ):
        raise AssertionError("invalid trusted hidden-fixture seed binding")
    if set(fixture.get("cases", {})) != {
        "balanced_go",
        "balanced_refinement_stop",
        "balanced_zero_stop",
        "full_support_threshold_fail",
        "missing_cell_threshold_fail",
        "threshold_fail_with_zero_priority",
        "precision_cross_product",
    }:
        raise AssertionError("trusted controller fixture has wrong case set")
    return fixture


def _window_arguments(fixture: dict[str, Any]) -> tuple[int, int, int, str]:
    return (
        fixture["window_index"],
        fixture["start_n"],
        fixture["end_exclusive_n"],
        fixture["spec_bundle_sha256"],
    )


def _canonical_mutation(
    module: Any,
    fixture: dict[str, Any],
    value: Any,
    label: str,
) -> None:
    raw = json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
        allow_nan=False,
    ).encode("ascii") + b"\n"
    _rejects(
        module.validate_window_bytes,
        raw,
        *_window_arguments(fixture),
        label=label,
    )


def _test_fixture_sanity(fixture: dict[str, Any]) -> None:
    cases = fixture["cases"]
    balanced = cases["balanced_go"]["artifact"]
    if balanced["j"] != 6556 or 9 * balanced["j"] != 59004:
        raise AssertionError("balanced exact J fixture drifted")
    if balanced["decision"]["window13_action"] != "go_holdouts":
        raise AssertionError("balanced go fixture has wrong decision")
    if (
        cases["balanced_refinement_stop"]["artifact"]["decision"]["window13_action"]
        != "stop_determinant_route_pending_optional_refinement"
    ):
        raise AssertionError("refinement decision fixture drifted")
    if (
        cases["balanced_zero_stop"]["artifact"]["decision"]["window13_action"]
        != "stop_audit_zero"
    ):
        raise AssertionError("zero decision fixture drifted")
    full = cases["full_support_threshold_fail"]["artifact"]
    if not all(full["cell_counts"][f"n{cell}"] > 0 for cell in range(10)):
        raise AssertionError("full-support threshold-failure fixture lost support")
    if full["j10_strict_pass"] is not False:
        raise AssertionError("full-support fixture must fail the J threshold")
    missing = cases["missing_cell_threshold_fail"]["artifact"]
    if missing["j"] != 7284 or missing["cell_counts"]["n9"] != 0:
        raise AssertionError("missing-cell threshold fixture drifted")
    priority = cases["threshold_fail_with_zero_priority"]["artifact"]["decision"]
    if priority != {
        "j_threshold_pass": False,
        "c_sum": priority["c_sum"],
        "a_sum": priority["a_sum"],
        "has_zero_distinct_pair": True,
        "window13_action": "stop_local_conjecture",
    }:
        raise AssertionError("threshold failure no longer has first priority")
    precision = cases["precision_cross_product"]["artifact"][
        "maximum_determinant_ratio"
    ]
    loser = fixture["precision_ratio_loser"]
    if not (
        int(loser["num"]) * int(precision["den"])
        < int(precision["num"]) * int(loser["den"])
    ):
        raise AssertionError("precision cross-product case lost strict exact order")


def _test_positive_api(module: Any, fixture: dict[str, Any]) -> None:
    sample = {"z": [True, None, 3], "a": "\u00e9"}
    expected_sample = b'{"a":"\\u00e9","z":[true,null,3]}\n'
    first_raw = _accepts(
        module.canonical_json_bytes,
        sample,
        label="canonical_json_bytes positive",
        expected_result=expected_sample,
        compare_result=True,
    )
    second_raw = _accepts(
        module.canonical_json_bytes,
        sample,
        label="canonical_json_bytes deterministic replay",
        expected_result=expected_sample,
        compare_result=True,
    )
    if type(first_raw) is not bytes or type(second_raw) is not bytes:
        raise AssertionError("canonical_json_bytes must return exact built-in bytes")
    decoded = _accepts(
        module.decode_canonical_json,
        expected_sample,
        label="decode_canonical_json positive",
        expected_result=sample,
        compare_result=True,
    )
    _accepts(
        module.decode_canonical_json,
        expected_sample,
        label="decode_canonical_json deterministic replay",
        expected_result=sample,
        compare_result=True,
    )
    if not _exact_equal(decoded, sample):
        raise AssertionError("strict decoder result mismatch")

    for case_name, case in fixture["cases"].items():
        points = copy.deepcopy(case["points"])
        artifact = copy.deepcopy(case["artifact"])
        raw = case["raw_ascii"].encode("ascii")
        if raw != json.dumps(
            artifact, sort_keys=True, separators=(",", ":"),
            ensure_ascii=True, allow_nan=False,
        ).encode("ascii") + b"\n":
            raise AssertionError(f"trusted fixture raw bytes drifted: {case_name}")
        _accepts(
            module.canonical_json_bytes, artifact,
            label=f"canonical window {case_name}",
            expected_result=raw, compare_result=True,
        )
        _accepts(
            module.decode_canonical_json, raw,
            label=f"decode window {case_name}",
            expected_result=artifact, compare_result=True,
        )
        for offset in (0, 1, 127, 255):
            _accepts(
                module.validate_point, copy.deepcopy(points[offset]),
                fixture["start_n"] + offset,
                label=f"point positive {case_name}/{offset}",
                expected_result=None, compare_result=True,
            )
        recomputed = _accepts(
            module.recompute_window, points, *_window_arguments(fixture),
            label=f"recompute {case_name}",
            expected_result=artifact, compare_result=True,
        )
        if recomputed is artifact or recomputed.get("points") is points:
            raise AssertionError("recompute_window did not allocate a new complete object")
        validated = _accepts(
            module.validate_window_bytes, raw, *_window_arguments(fixture),
            label=f"validate window bytes {case_name}",
            expected_result=artifact, compare_result=True,
        )
        if type(validated) is not dict:
            raise AssertionError("validate_window_bytes must return the decoded object")

    for case in fixture["window_cases"]:
        args = (
            case["window_index"], case["start_n"],
            case["end_exclusive_n"], fixture["spec_bundle_sha256"],
        )
        _accepts(
            module.recompute_window, copy.deepcopy(case["points"]), *args,
            label=f"frozen window {case['window_index']} recompute",
            expected_result=case["artifact"], compare_result=True,
        )
        _accepts(
            module.validate_window_bytes, case["raw_ascii"].encode("ascii"), *args,
            label=f"frozen window {case['window_index']} raw",
            expected_result=case["artifact"], compare_result=True,
        )

    if type(fixture.get("hidden_cases")) is not list or len(fixture["hidden_cases"]) < 4:
        raise AssertionError("controller-hidden point-family coverage is missing")
    for ordinal, case in enumerate(fixture["hidden_cases"]):
        args = (
            case["window_index"], case["start_n"],
            case["end_exclusive_n"], fixture["spec_bundle_sha256"],
        )
        points = copy.deepcopy(case["points"])
        artifact = copy.deepcopy(case["artifact"])
        raw = case["raw_ascii"].encode("ascii")
        _accepts(
            module.recompute_window, points, *args,
            label=f"controller-hidden recompute {ordinal}",
            expected_result=artifact, compare_result=True,
        )
        _accepts(
            module.validate_window_bytes, raw, *args,
            label=f"controller-hidden raw {ordinal}",
            expected_result=artifact, compare_result=True,
        )

    for replay in ("first", "replay"):
        _accepts(
            module.validate_cas_record, copy.deepcopy(fixture["cas_record"]),
            copy.deepcopy(fixture["cas_expected_bindings"]),
            label=f"CAS positive {replay}", expected_result=None, compare_result=True,
        )
        _accepts(
            module.validate_receipt, copy.deepcopy(fixture["receipt"]),
            copy.deepcopy(fixture["receipt_expected_bindings"]),
            label=f"receipt positive {replay}", expected_result=None, compare_result=True,
        )

def _test_encoder_rejections(module: Any) -> None:
    values = [
        (1.0, "encoder float"),
        (float("nan"), "encoder NaN"),
        (float("inf"), "encoder Infinity"),
        (b"bytes", "encoder bytes value"),
        ((1, 2), "encoder tuple"),
        ({1: "coerced key"}, "encoder non-string object key"),
        (bytearray(b"x"), "encoder bytearray"),
        (memoryview(b"x"), "encoder memoryview"),
        ({1, 2}, "encoder set"),
    ]
    for value, label in values:
        _rejects(module.canonical_json_bytes, value, label=label)


def _test_raw_byte_rejections(module: Any, fixture: dict[str, Any]) -> None:
    raw = fixture["cases"]["balanced_go"]["raw_ascii"].encode("ascii")
    artifact = fixture["cases"]["balanced_go"]["artifact"]
    reordered_value = {key: artifact[key] for key in reversed(list(artifact))}
    reordered = json.dumps(
        reordered_value,
        sort_keys=False,
        separators=(",", ":"),
        ensure_ascii=True,
    ).encode("ascii") + b"\n"
    if reordered == raw:
        raise AssertionError("controller key-order mutation is a no-op")
    first_point = artifact["points"][0]
    canonical_point = json.dumps(
        first_point, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("ascii")
    reordered_point_value = {
        key: first_point[key] for key in reversed(list(first_point))
    }
    reordered_point = json.dumps(
        reordered_point_value,
        sort_keys=False,
        separators=(",", ":"),
        ensure_ascii=True,
    ).encode("ascii")
    nested_reordered = raw.replace(canonical_point, reordered_point, 1)
    if nested_reordered == raw:
        raise AssertionError("controller nested key-order mutation is a no-op")
    pretty = json.dumps(artifact, sort_keys=True, indent=2, ensure_ascii=True).encode("ascii") + b"\n"
    raw_mutations: list[tuple[Any, str]] = [
        (b'{"a":1,"a":2}\n', "duplicate top-level key"),
        (b'{"a":{"x":1,"x":2}}\n', "duplicate nested key"),
        (b'{"a":1.0}\n', "float token"),
        (b'{"a":1e0}\n', "exponent float token"),
        (b'{"a":NaN}\n', "NaN token"),
        (b'{"a":Infinity}\n', "Infinity token"),
        (b'{"a":-Infinity}\n', "negative Infinity token"),
        (b"\xef\xbb\xbf" + raw, "UTF-8 BOM"),
        (b'{"a":"\xff"}\n', "invalid UTF-8"),
        (raw[:-1] + b"\r\n", "CRLF"),
        (raw[:-1] + b"\r", "lone CR"),
        (raw[:-1], "missing final LF"),
        (raw + b"\n", "multiple final LF"),
        (b" " + raw, "leading whitespace"),
        (raw[:-1] + b" \n", "trailing whitespace before LF"),
        (raw + b" ", "bytes after final LF"),
        (pretty, "pretty-printed JSON"),
        (reordered, "key-reordered parsed-equivalent JSON"),
        (nested_reordered, "nested key-reordered parsed-equivalent JSON"),
        ('{"a":"é"}\n'.encode("utf-8"), "non-ASCII parsed-equivalent UTF-8"),
        (b'{"a":"\\u00E9"}\n', "uppercase Unicode escape"),
        (b'{"a":"\\/"}\n', "escaped solidus"),
        (b'{"a":-0}\n', "negative zero integer grammar"),
        (b'{"a":+1}\n', "plus-sign integer grammar"),
        (b'{"a":01}\n', "leading-zero integer grammar"),
        (raw.decode("ascii"), "text instead of bytes"),
        (bytearray(raw), "bytearray instead of bytes"),
        (memoryview(raw), "memoryview instead of bytes"),
        (None, "null Python input instead of bytes"),
        (b"[" * 5000 + b"0" + b"]" * 5000 + b"\n", "parser recursion bomb"),
    ]
    for changed, label in raw_mutations:
        _rejects(module.decode_canonical_json, changed, label=label)
    for changed, label in raw_mutations:
        _rejects(
            module.validate_window_bytes,
            changed,
            *_window_arguments(fixture),
            label=f"window raw: {label}",
        )



def _test_limit_boundaries(module: Any, fixture: dict[str, Any]) -> None:
    limits = fixture["limits"]
    max_raw = limits["canonical_raw_max_bytes"]
    max_depth = limits["json_max_nesting_depth"]
    max_array = limits["json_max_array_items"]
    max_keys = limits["json_max_object_keys"]
    max_digits = limits["canonical_integer_string_max_digits"]

    nested: Any = 0
    for _ in range(max_depth):
        nested = [nested]
    boundary_nested = module.canonical_json_bytes(nested)
    _accepts(
        module.decode_canonical_json, boundary_nested,
        label="nesting exact boundary", expected_result=nested, compare_result=True,
    )
    over_nested = [nested]
    _rejects(module.canonical_json_bytes, over_nested, label="nesting one over encoder")
    over_nested_raw = b"[" * (max_depth + 1) + b"0" + b"]" * (max_depth + 1) + b"\n"
    _rejects(module.decode_canonical_json, over_nested_raw, label="nesting one over decoder")

    boundary_array = [0] * max_array
    _accepts(
        module.decode_canonical_json, module.canonical_json_bytes(boundary_array),
        label="array exact boundary", expected_result=boundary_array, compare_result=True,
    )
    _rejects(module.canonical_json_bytes, [0] * (max_array + 1), label="array one over")

    boundary_object = {str(index): 0 for index in range(max_keys)}
    _accepts(
        module.decode_canonical_json, module.canonical_json_bytes(boundary_object),
        label="object exact boundary", expected_result=boundary_object, compare_result=True,
    )
    over_object = {str(index): 0 for index in range(max_keys + 1)}
    _rejects(module.canonical_json_bytes, over_object, label="object one over")

    boundary_point = {
        "n": 0, "r": "0", "w": "1" + "0" * (max_digits - 1), "cell": 0,
    }
    _accepts(
        module.validate_point, boundary_point, 0,
        label="integer-string exact digit boundary",
        expected_result=None, compare_result=True,
    )
    over_point = {
        "n": 0, "r": "0", "w": "1" + "0" * max_digits, "cell": 0,
    }
    _rejects(module.validate_point, over_point, 0, label="integer-string one over")
    del boundary_point, over_point
    gc.collect()

    boundary_text = "x" * (max_raw - 3)
    boundary_raw = module.canonical_json_bytes(boundary_text)
    if type(boundary_raw) is not bytes or len(boundary_raw) != max_raw:
        raise AssertionError("canonical raw exact byte boundary was not accepted exactly")
    decoded = module.decode_canonical_json(boundary_raw)
    if type(decoded) is not str or len(decoded) != len(boundary_text):
        raise AssertionError("canonical raw exact boundary decoded incorrectly")
    del decoded, boundary_raw, boundary_text
    gc.collect()

    over_text = "x" * (max_raw - 2)
    _rejects(module.canonical_json_bytes, over_text, label="canonical raw one over encoder")
    del over_text
    gc.collect()
    over_raw = b'"' + b"x" * (max_raw - 2) + b'"\n'
    if len(over_raw) != max_raw + 1:
        raise AssertionError("controller one-over raw construction drifted")
    _rejects(module.decode_canonical_json, over_raw, label="canonical raw one over decoder")
    _rejects(
        module.validate_window_bytes, over_raw, *_window_arguments(fixture),
        label="window canonical raw one over",
    )
    del over_raw
    gc.collect()

def _test_expected_binding_rejections(module: Any, fixture: dict[str, Any]) -> None:
    case = fixture["cases"]["balanced_go"]
    raw = case["raw_ascii"].encode("ascii")
    points = case["points"]
    index, start, end, digest = _window_arguments(fixture)
    mutations = [
        (index - 1, start, end, digest, "wrong expected window index"),
        (True, start, end, digest, "boolean expected window index"),
        (index, start - 1, end, digest, "wrong expected start"),
        (index, True, end, digest, "boolean expected start"),
        (index, start, end + 1, digest, "wrong expected end"),
        (index, start, False, digest, "boolean expected end"),
        (index, start, end, "0" * 64, "wrong expected spec digest"),
        (index, start, end, 0, "non-string expected spec digest"),
    ]
    for wrong_index, wrong_start, wrong_end, wrong_digest, label in mutations:
        _rejects(
            module.recompute_window,
            copy.deepcopy(points),
            wrong_index,
            wrong_start,
            wrong_end,
            wrong_digest,
            label=f"recompute binding: {label}",
        )
        _rejects(
            module.validate_window_bytes,
            raw,
            wrong_index,
            wrong_start,
            wrong_end,
            wrong_digest,
            label=f"window binding: {label}",
        )


def _test_point_mutations(module: Any, fixture: dict[str, Any]) -> None:
    artifact = fixture["cases"]["balanced_go"]["artifact"]
    points = artifact["points"]
    first = points[0]
    wrong_mod_cell = int(first["r"]) % 10
    if wrong_mod_cell == first["cell"]:
        for point in points:
            candidate = int(point["r"]) % 10
            if candidate != point["cell"]:
                first = point
                wrong_mod_cell = candidate
                break
        else:
            raise AssertionError("controller %10 mutation fixture unavailable")
    first_offset = first["n"] - fixture["start_n"]
    point_mutations: list[tuple[Any, str]] = [
        (_change(first, ["n"], first["n"] + 1), "N versus N+1 substitution"),
        (_change(first, ["n"], True), "boolean point.n"),
        (_change(first, ["r"], "-1"), "negative r"),
        (_change(first, ["r"], first["w"]), "r equal to w"),
        (_change(first, ["r"], int(first["r"])), "numeric r instead of string"),
        (_change(first, ["r"], "0" + first["r"]), "leading-zero r"),
        (_change(first, ["r"], "+" + first["r"]), "plus-sign r"),
        (_change(first, ["w"], "0"), "zero w"),
        (_change(first, ["w"], "-1"), "negative w"),
        (_change(first, ["w"], int(first["w"])), "numeric w instead of string"),
        (_change(first, ["w"], "0" + first["w"]), "leading-zero w"),
        (_change(first, ["w"], "+" + first["w"]), "plus-sign w"),
        (_change(first, ["cell"], (first["cell"] + 1) % 10), "wrong cell"),
        (_change(first, ["cell"], wrong_mod_cell), "%10 cell substitution"),
        (_change(first, ["cell"], float(first["cell"])), "float cell"),
        (_change(first, ["cell"], True), "boolean cell"),
        (_delete(first, ["r"]), "missing point field"),
        ({**first, "extra": 1}, "extra point field"),
    ]
    for changed, label in point_mutations:
        _rejects(
            module.validate_point,
            changed,
            first["n"],
            label=f"validate_point: {label}",
        )
        mutated_artifact = copy.deepcopy(artifact)
        mutated_artifact["points"][first_offset] = copy.deepcopy(changed)
        _rejects(
            module.recompute_window,
            mutated_artifact["points"],
            *_window_arguments(fixture),
            label=f"recompute point: {label}",
        )
        _canonical_mutation(module, fixture, mutated_artifact, f"window point: {label}")

    valid_r_change = copy.deepcopy(first)
    valid_r_change["r"] = str(int(valid_r_change["r"]) + 1)
    if (10 * int(valid_r_change["r"])) // int(valid_r_change["w"]) != first["cell"]:
        raise AssertionError("controller valid-r mutation crossed a cell boundary")
    _accepts(
        module.validate_point,
        valid_r_change,
        first["n"],
        label="validate_point accepts valid changed r",
    )
    valid_r_artifact = copy.deepcopy(artifact)
    valid_r_artifact["points"][first_offset] = valid_r_change
    _canonical_mutation(
        module, fixture, valid_r_artifact, "valid point change with stale summaries"
    )

    scaled_point = copy.deepcopy(first)
    scaled_point["r"] = str(2 * int(scaled_point["r"]))
    scaled_point["w"] = str(2 * int(scaled_point["w"]))
    _accepts(
        module.validate_point,
        scaled_point,
        first["n"],
        label="validate_point accepts unreduced exact raw pair",
    )
    scaled_artifact = copy.deepcopy(artifact)
    scaled_artifact["points"][first_offset] = scaled_point
    _canonical_mutation(
        module, fixture, scaled_artifact, "raw r/w scale change with stale statistics"
    )

    collection_mutations: list[tuple[Any, str]] = []
    deleted = copy.deepcopy(points)
    del deleted[17]
    collection_mutations.append((deleted, "deleted point"))
    duplicated = copy.deepcopy(points)
    duplicated[17] = copy.deepcopy(duplicated[16])
    collection_mutations.append((duplicated, "duplicated point"))
    reordered = copy.deepcopy(points)
    reordered[0], reordered[1] = reordered[1], reordered[0]
    collection_mutations.append((reordered, "reordered points"))
    shifted = copy.deepcopy(points)
    for point in shifted:
        point["n"] += 1
    collection_mutations.append((shifted, "shifted point indices"))
    out_of_range = copy.deepcopy(points)
    out_of_range[-1]["n"] = fixture["end_exclusive_n"]
    collection_mutations.append((out_of_range, "out-of-range point"))
    collection_mutations.append((tuple(copy.deepcopy(points)), "tuple point collection"))
    for changed_points, label in collection_mutations:
        _rejects(
            module.recompute_window,
            changed_points,
            *_window_arguments(fixture),
            label=f"recompute collection: {label}",
        )
        if type(changed_points) is list:
            changed_artifact = copy.deepcopy(artifact)
            changed_artifact["points"] = changed_points
            _canonical_mutation(module, fixture, changed_artifact, f"window collection: {label}")


def _test_window_schema_and_summary_mutations(module: Any, fixture: dict[str, Any]) -> None:
    cases = fixture["cases"]
    artifact = cases["balanced_go"]["artifact"]
    if set(artifact) != WINDOW_KEYS:
        raise AssertionError("trusted window key set drifted")
    for key in sorted(WINDOW_KEYS):
        _canonical_mutation(module, fixture, _delete(artifact, [key]), f"missing top-level field {key}")
    for key in ("extra", "verified", "self_test_passed", "manifest", "receipt", "cas"):
        changed = copy.deepcopy(artifact)
        changed[key] = True
        _canonical_mutation(module, fixture, changed, f"candidate-authored claim field {key}")
    misspelled = _delete(artifact, ["j10_strict_pass"])
    misspelled["j10_strict"] = artifact["j10_strict_pass"]
    _canonical_mutation(module, fixture, misspelled, "misspelled j10 field")

    scalar_mutations = [
        (["schema"], "pi-q10-window-v2", "wrong window schema"),
        (["schema"], 1, "non-string window schema"),
        (["experiment_id"], "candidate-experiment", "wrong experiment"),
        (["spec_bundle_sha256"], "0" * 64, "wrong spec bundle"),
        (["window_index"], fixture["window_index"] - 1, "wrong artifact window index"),
        (["window_index"], True, "boolean artifact window index"),
        (["start_n"], fixture["start_n"] - 1, "wrong artifact start"),
        (["start_n"], True, "boolean artifact start"),
        (["end_exclusive_n"], fixture["end_exclusive_n"] + 1, "wrong artifact end"),
        (["end_exclusive_n"], False, "boolean artifact end"),
        (["points"], {}, "points wrong type"),
        (["cell_counts"], [], "cell_counts wrong type"),
        (["j"], artifact["j"] + 1, "altered J"),
        (["j"], True, "boolean J"),
        (["j"], str(artifact["j"]), "string J"),
        (["j10_strict_pass"], not artifact["j10_strict_pass"], "flipped J threshold flag"),
        (["j10_strict_pass"], 1, "integer J threshold flag"),
        (["lag_counts"], {}, "lag_counts wrong type"),
        (["maximum_determinant_ratio"], [], "maximum ratio wrong type"),
        (["decision"], [], "decision wrong type"),
    ]
    for path, replacement, label in scalar_mutations:
        _canonical_mutation(module, fixture, _change(artifact, path, replacement), label)

    counts = artifact["cell_counts"]
    for key in sorted(counts):
        _canonical_mutation(module, fixture, _delete(artifact, ["cell_counts", key]), f"missing count {key}")
    count_extra = copy.deepcopy(artifact)
    count_extra["cell_counts"]["n10"] = 0
    _canonical_mutation(module, fixture, count_extra, "extra cell count")
    count_mutations = [
        (["cell_counts", "n0"], counts["n0"] + 1, "altered cell count"),
        (["cell_counts", "n0"], -1, "negative cell count"),
        (["cell_counts", "n0"], True, "boolean cell count"),
        (["cell_counts", "n0"], str(counts["n0"]), "string cell count"),
    ]
    for path, replacement, label in count_mutations:
        _canonical_mutation(module, fixture, _change(artifact, path, replacement), label)
    balanced_swap = copy.deepcopy(artifact)
    if (balanced_swap["cell_counts"]["n0"], balanced_swap["cell_counts"]["n6"]) != (26, 25):
        raise AssertionError("balanced count-swap fixture drifted")
    balanced_swap["cell_counts"]["n0"] -= 1
    balanced_swap["cell_counts"]["n6"] += 1
    _canonical_mutation(
        module,
        fixture,
        balanced_swap,
        "point/count mismatch preserving count sum and J",
    )

    lags = artifact["lag_counts"]
    deleted_lag = copy.deepcopy(artifact)
    del deleted_lag["lag_counts"][17]
    _canonical_mutation(module, fixture, deleted_lag, "deleted lag record")
    duplicated_lag = copy.deepcopy(artifact)
    duplicated_lag["lag_counts"][17] = copy.deepcopy(duplicated_lag["lag_counts"][16])
    _canonical_mutation(module, fixture, duplicated_lag, "duplicated lag record")
    reordered_lag = copy.deepcopy(artifact)
    reordered_lag["lag_counts"][0], reordered_lag["lag_counts"][1] = (
        reordered_lag["lag_counts"][1],
        reordered_lag["lag_counts"][0],
    )
    _canonical_mutation(module, fixture, reordered_lag, "reordered lag records")
    lag_extra = copy.deepcopy(artifact)
    lag_extra["lag_counts"][0]["extra"] = 0
    _canonical_mutation(module, fixture, lag_extra, "extra lag field")
    lag_missing = _delete(artifact, ["lag_counts", 0, "zero_determinant_count"])
    _canonical_mutation(module, fixture, lag_missing, "missing lag field")
    lag_mutations = [
        (["lag_counts", 0, "lag"], 2, "wrong lag sequence"),
        (["lag_counts", 0, "lag"], True, "boolean lag"),
        (["lag_counts", 0, "same_cell_count"], lags[0]["same_cell_count"] + 1, "altered C_l"),
        (["lag_counts", 0, "near_determinant_count"], lags[0]["near_determinant_count"] + 1, "altered A_l"),
        (["lag_counts", 0, "zero_determinant_count"], 1, "altered Z_l"),
        (["lag_counts", 0, "same_cell_count"], -1, "negative C_l"),
        (["lag_counts", 0, "same_cell_count"], True, "boolean C_l"),
        (["lag_counts", 0, "same_cell_count"], 256, "C_l above lag bound"),
    ]
    for path, replacement, label in lag_mutations:
        _canonical_mutation(module, fixture, _change(artifact, path, replacement), label)
    c_le_a = copy.deepcopy(artifact)
    target = next(
        index
        for index, record in enumerate(c_le_a["lag_counts"])
        if record["same_cell_count"] > 0
    )
    c_le_a["lag_counts"][target]["near_determinant_count"] = (
        c_le_a["lag_counts"][target]["same_cell_count"] - 1
    )
    _canonical_mutation(module, fixture, c_le_a, "violation C_l <= A_l")
    z_le_a = copy.deepcopy(cases["balanced_zero_stop"]["artifact"])
    target = next(
        index
        for index, record in enumerate(z_le_a["lag_counts"])
        if record["zero_determinant_count"] > 0
    )
    z_le_a["lag_counts"][target]["near_determinant_count"] = 0
    _canonical_mutation(module, fixture, z_le_a, "violation Z_l <= A_l")

    balanced_lag_transfer = copy.deepcopy(artifact)
    source_index = next(
        index
        for index, record in enumerate(balanced_lag_transfer["lag_counts"])
        if record["same_cell_count"] > 0
    )
    target_index = next(
        index
        for index, record in enumerate(balanced_lag_transfer["lag_counts"])
        if index != source_index
        and record["near_determinant_count"] < 256 - record["lag"]
    )
    for key in ("same_cell_count", "near_determinant_count"):
        balanced_lag_transfer["lag_counts"][source_index][key] -= 1
        balanced_lag_transfer["lag_counts"][target_index][key] += 1
    _canonical_mutation(
        module,
        fixture,
        balanced_lag_transfer,
        "lag transfer preserving J identity, A_sum, and per-lag laws",
    )

    refinement_transfer = copy.deepcopy(cases["balanced_refinement_stop"]["artifact"])
    source_index = next(
        index
        for index, record in enumerate(refinement_transfer["lag_counts"])
        if record["near_determinant_count"] > record["same_cell_count"]
    )
    target_index = next(
        index
        for index, record in enumerate(refinement_transfer["lag_counts"])
        if index != source_index
        and record["near_determinant_count"] < 256 - record["lag"]
    )
    refinement_transfer["lag_counts"][source_index]["near_determinant_count"] -= 1
    refinement_transfer["lag_counts"][target_index]["near_determinant_count"] += 1
    _canonical_mutation(
        module,
        fixture,
        refinement_transfer,
        "A_l transfer preserving A_sum and all reported inequalities",
    )

    zero_transfer = copy.deepcopy(cases["balanced_zero_stop"]["artifact"])
    source_index = next(
        index
        for index, record in enumerate(zero_transfer["lag_counts"])
        if record["zero_determinant_count"] > 0
    )
    target_index = next(
        index
        for index, record in enumerate(zero_transfer["lag_counts"])
        if index != source_index
        and record["zero_determinant_count"] == 0
        and record["near_determinant_count"] > 0
    )
    zero_transfer["lag_counts"][source_index]["zero_determinant_count"] -= 1
    zero_transfer["lag_counts"][target_index]["zero_determinant_count"] += 1
    _canonical_mutation(
        module,
        fixture,
        zero_transfer,
        "Z_l transfer preserving zero flag, A_sum, and Z_l <= A_l",
    )

    decision = artifact["decision"]
    if set(decision) != DECISION_KEYS:
        raise AssertionError("trusted decision key set drifted")
    for key in sorted(DECISION_KEYS):
        _canonical_mutation(module, fixture, _delete(artifact, ["decision", key]), f"missing decision field {key}")
    decision_extra = copy.deepcopy(artifact)
    decision_extra["decision"]["pass"] = True
    _canonical_mutation(module, fixture, decision_extra, "candidate decision pass flag")
    decision_mutations = [
        (["decision", "j_threshold_pass"], False, "altered decision J flag"),
        (["decision", "j_threshold_pass"], 1, "integer decision J flag"),
        (["decision", "c_sum"], decision["c_sum"] + 1, "altered c_sum"),
        (["decision", "c_sum"], True, "boolean c_sum"),
        (["decision", "a_sum"], decision["a_sum"] + 1, "altered a_sum"),
        (["decision", "has_zero_distinct_pair"], True, "altered zero flag"),
        (["decision", "has_zero_distinct_pair"], 0, "integer zero flag"),
        (["decision", "window13_action"], "accepted", "wrong decision action"),
    ]
    for path, replacement, label in decision_mutations:
        _canonical_mutation(module, fixture, _change(artifact, path, replacement), label)
    zero_wrong = _change(
        cases["balanced_zero_stop"]["artifact"],
        ["decision", "window13_action"],
        "go_holdouts",
    )
    _canonical_mutation(module, fixture, zero_wrong, "zero witness priority mutation")
    fail_zero_wrong = _change(
        cases["threshold_fail_with_zero_priority"]["artifact"],
        ["decision", "window13_action"],
        "stop_audit_zero",
    )
    _canonical_mutation(module, fixture, fail_zero_wrong, "J-failure priority over zero mutation")
    refinement_wrong = _change(
        cases["balanced_refinement_stop"]["artifact"],
        ["decision", "window13_action"],
        "go_holdouts",
    )
    _canonical_mutation(module, fixture, refinement_wrong, "A_sum refinement branch mutation")


def _test_ratio_mutations(module: Any, fixture: dict[str, Any]) -> None:
    artifact = fixture["cases"]["balanced_go"]["artifact"]
    ratio = artifact["maximum_determinant_ratio"]
    if set(ratio) != RATIO_KEYS:
        raise AssertionError("trusted ratio key set drifted")
    for key in sorted(RATIO_KEYS):
        _canonical_mutation(
            module,
            fixture,
            _delete(artifact, ["maximum_determinant_ratio", key]),
            f"missing ratio field {key}",
        )
    ratio_extra = copy.deepcopy(artifact)
    ratio_extra["maximum_determinant_ratio"]["ratio"] = 0.5
    _canonical_mutation(module, fixture, ratio_extra, "serialized floating ratio")
    vectors = fixture["ratio_mutation_vectors"]
    for name, record in vectors.items():
        changed = copy.deepcopy(artifact)
        changed["maximum_determinant_ratio"] = copy.deepcopy(record)
        _canonical_mutation(module, fixture, changed, f"ratio vector {name}")
    precision_artifact = copy.deepcopy(
        fixture["cases"]["precision_cross_product"]["artifact"]
    )
    precision_artifact["maximum_determinant_ratio"] = copy.deepcopy(
        fixture["precision_ratio_loser"]
    )
    _canonical_mutation(
        module,
        fixture,
        precision_artifact,
        "float-collapsing exact cross-product loser",
    )
    ratio_mutations = [
        (["maximum_determinant_ratio", "num"], int(ratio["num"]), "numeric ratio numerator"),
        (["maximum_determinant_ratio", "num"], "-1", "negative ratio numerator"),
        (["maximum_determinant_ratio", "num"], "+1", "plus-sign ratio numerator"),
        (["maximum_determinant_ratio", "num"], "0" + ratio["num"], "leading-zero ratio numerator"),
        (["maximum_determinant_ratio", "den"], int(ratio["den"]), "numeric ratio denominator"),
        (["maximum_determinant_ratio", "den"], "0", "zero ratio denominator"),
        (["maximum_determinant_ratio", "den"], "-1", "negative ratio denominator"),
        (["maximum_determinant_ratio", "witness_n"], ratio["witness_n"] + 1, "wrong witness_n"),
        (["maximum_determinant_ratio", "witness_n"], True, "boolean witness_n"),
        (["maximum_determinant_ratio", "witness_m"], ratio["witness_m"] - 1, "wrong witness_m"),
        (["maximum_determinant_ratio", "lag"], ratio["lag"] + 1, "wrong ratio lag"),
        (["maximum_determinant_ratio", "cell"], (ratio["cell"] + 1) % 10, "wrong ratio cell"),
        (["maximum_determinant_ratio", "cell"], float(ratio["cell"]), "float ratio cell"),
    ]
    for path, replacement, label in ratio_mutations:
        _canonical_mutation(module, fixture, _change(artifact, path, replacement), label)
    num_ge_den = copy.deepcopy(artifact)
    num_ge_den["maximum_determinant_ratio"]["num"] = ratio["den"]
    _canonical_mutation(module, fixture, num_ge_den, "ratio num >= den")
    swapped = copy.deepcopy(artifact)
    swapped_ratio = swapped["maximum_determinant_ratio"]
    swapped_ratio["witness_n"], swapped_ratio["witness_m"] = (
        swapped_ratio["witness_m"],
        swapped_ratio["witness_n"],
    )
    swapped_ratio["lag"] = swapped_ratio["witness_m"] - swapped_ratio["witness_n"]
    _canonical_mutation(module, fixture, swapped, "reversed ratio witness order")


def _binding_mutations(
    module: Any,
    value: dict[str, Any],
    expected: dict[str, Any],
    validator: Callable[[Any, Any], Any],
    invalid_when_matched: list[tuple[list[Any], Any, str]],
    label: str,
) -> None:
    for key in sorted(value):
        _rejects(validator, _delete(value, [key]), copy.deepcopy(expected), label=f"{label} missing {key}")
    extra = copy.deepcopy(value)
    extra["candidate_pass"] = True
    _rejects(validator, extra, copy.deepcopy(expected), label=f"{label} candidate pass field")
    for path, replacement, description in invalid_when_matched:
        changed = _change(value, path, replacement)
        _rejects(
            validator,
            changed,
            copy.deepcopy(expected),
            label=f"{label} record mismatch: {description}",
        )
        if path[0] in expected:
            changed_expected = _change(expected, path, replacement)
            _rejects(
                validator,
                changed,
                changed_expected,
                label=f"{label} invalid even when expected: {description}",
            )
    _rejects(validator, copy.deepcopy(value), None, label=f"{label} null expected bindings")
    expected_extra = copy.deepcopy(expected)
    expected_extra["extra"] = 1
    _rejects(validator, copy.deepcopy(value), expected_extra, label=f"{label} extra expected binding")
    expected_missing = _delete(expected, [next(iter(expected))])
    _rejects(validator, copy.deepcopy(value), expected_missing, label=f"{label} missing expected binding")


def _test_cas_and_receipt_mutations(module: Any, fixture: dict[str, Any]) -> None:
    cas = fixture["cas_record"]
    cas_expected = fixture["cas_expected_bindings"]
    cas_invalid = [
        (["schema"], "pi-q10-cas-record-v2", "wrong schema"),
        (["algorithm"], "sha512", "wrong algorithm"),
        (["artifact_sha256"], "A" * 64, "uppercase artifact digest"),
        (["artifact_sha256"], "0" * 63, "short artifact digest"),
        (["size_bytes"], -1, "negative size"),
        (["size_bytes"], True, "boolean size"),
        (["experiment_id"], "candidate-experiment", "wrong experiment"),
        (["spec_bundle_sha256"], "0" * 64, "wrong spec digest"),
        (["window_index"], fixture["window_index"] - 1, "wrong window index"),
        (["window_index"], True, "boolean window index"),
        (["start_n"], fixture["start_n"] - 1, "wrong start"),
        (["start_n"], True, "boolean start"),
        (["end_exclusive_n"], fixture["end_exclusive_n"] + 1, "wrong end"),
    ]
    _binding_mutations(
        module,
        cas,
        cas_expected,
        module.validate_cas_record,
        cas_invalid,
        "CAS",
    )
    changed_digest = _change(cas, ["artifact_sha256"], "3" * 64)
    _rejects(
        module.validate_cas_record,
        changed_digest,
        copy.deepcopy(cas_expected),
        label="CAS valid-but-unexpected artifact digest",
    )
    changed_size = _change(cas, ["size_bytes"], cas["size_bytes"] + 1)
    _rejects(
        module.validate_cas_record,
        changed_size,
        copy.deepcopy(cas_expected),
        label="CAS valid-but-unexpected size",
    )

    receipt = fixture["receipt"]
    receipt_expected = fixture["receipt_expected_bindings"]
    receipt_invalid = [
        (["schema"], "pi-q10-controller-receipt-v2", "wrong schema"),
        (["experiment_id"], "candidate-experiment", "wrong experiment"),
        (["spec_bundle_sha256"], "0" * 64, "wrong spec digest"),
        (["window_index"], fixture["window_index"] - 1, "wrong window index"),
        (["window_index"], True, "boolean window index"),
        (["start_n"], fixture["start_n"] - 1, "wrong start"),
        (["end_exclusive_n"], fixture["end_exclusive_n"] + 1, "wrong end"),
        (["artifact_sha256"], "A" * 64, "uppercase artifact digest"),
        (["generator_source_sha256"], "0" * 63, "short generator digest"),
        (["verifier_source_sha256"], 0, "non-string verifier digest"),
        (["verifier_result"], "VERIFIED", "candidate verifier result"),
        (["controller_gate_id"], "", "empty controller gate ID"),
        (["controller_gate_id"], 0, "non-string controller gate ID"),
        (["controller_gate_id"], "t120_s0_schema_v1", "S0 gate used as receipt authority"),
    ]
    _binding_mutations(
        module,
        receipt,
        receipt_expected,
        module.validate_receipt,
        receipt_invalid,
        "receipt",
    )
    changed_gate = _change(
        receipt, ["controller_gate_id"], "other-controller-gate-v1"
    )
    _rejects(
        module.validate_receipt,
        changed_gate,
        copy.deepcopy(receipt_expected),
        label="receipt valid-but-unexpected controller_gate_id",
    )
    for key, replacement in (
        ("artifact_sha256", "3" * 64),
        ("generator_source_sha256", "4" * 64),
        ("verifier_source_sha256", "5" * 64),
    ):
        changed = _change(receipt, [key], replacement)
        _rejects(
            module.validate_receipt,
            changed,
            copy.deepcopy(receipt_expected),
            label=f"receipt valid-but-unexpected {key}",
        )


def run(candidate_path: Path, fixture_path: Path) -> None:
    global _rejection_checks
    _rejection_checks = 0
    fixture = _load_fixture(fixture_path)
    _test_fixture_sanity(fixture)
    module = _load_candidate(candidate_path)
    _test_positive_api(module, fixture)
    _test_encoder_rejections(module)
    _test_raw_byte_rejections(module, fixture)
    _test_limit_boundaries(module, fixture)
    _test_expected_binding_rejections(module, fixture)
    _test_point_mutations(module, fixture)
    _test_window_schema_and_summary_mutations(module, fixture)
    _test_ratio_mutations(module, fixture)
    _test_cas_and_receipt_mutations(module, fixture)
    if _rejection_checks < MINIMUM_REJECTION_CHECKS:
        raise AssertionError("controller mutation coverage count regressed")
    print(f"{PASS_MARKER}:{_rejection_checks}")


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: t120_s0_controller_harness.py CANDIDATE FIXTURE")
    run(Path(sys.argv[1]), Path(sys.argv[2]))


if __name__ == "__main__":
    main()
