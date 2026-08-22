"""Exact all-pairs replay for the canonical 256-point T120 window-13 array."""

import json
import sys

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(2_000_000)

N_MIN = 3840
N_MAX = 4096
COUNT = N_MAX - N_MIN
LAGS = COUNT - 1
KEYS = frozenset(("n", "r", "w", "cell"))


def die(msg):
    sys.stderr.write("replay_full_stats: fail-closed: %s\n" % msg)
    raise SystemExit(2)


def parse_decimal(idx, field, value):
    if not isinstance(value, str) or value == "":
        die("record %d: %s is not a nonempty decimal string" % (idx, field))
    if not value.isascii() or not value.isdigit():
        die("record %d: %s contains a non-digit character" % (idx, field))
    return int(value)


def load_records(path):
    try:
        with open(path, "rb") as stream:
            raw = stream.read()
    except OSError as exc:
        die("cannot read artifact: %s" % exc)
    try:
        doc = json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, ValueError) as exc:
        die("artifact is not valid UTF-8 JSON: %s" % exc)
    if not isinstance(doc, list):
        die("artifact root is not an array")
    if len(doc) != COUNT:
        die("artifact has %d records, expected %d" % (len(doc), COUNT))

    records = []
    for idx, rec in enumerate(doc):
        if not isinstance(rec, dict):
            die("record %d is not an object" % idx)
        if frozenset(rec.keys()) != KEYS:
            die("record %d does not have exactly the keys n,r,w,cell" % idx)
        n = rec["n"]
        cell = rec["cell"]
        if type(n) is not int or type(cell) is not int:
            die("record %d: n or cell is not a JSON integer" % idx)
        if n != N_MIN + idx:
            die("record %d: n violates the ordered range" % idx)
        if not 0 <= cell <= 9:
            die("record %d: cell outside 0..9" % idx)
        r = parse_decimal(idx, "r", rec["r"])
        w = parse_decimal(idx, "w", rec["w"])
        if w <= 0 or r >= w:
            die("record %d: invalid reduced-point range" % idx)
        if (10 * r) // w != cell:
            die("record %d: stored cell disagrees with (10*r)//w" % idx)
        records.append((n, r, w, cell))
    return records


def main():
    if len(sys.argv) != 2:
        die("usage: replay_full_stats.py POINT_ARRAY.json")
    records = load_records(sys.argv[1])

    ns = [rec[0] for rec in records]
    rs = [rec[1] for rec in records]
    ws = [rec[2] for rec in records]
    cells = [rec[3] for rec in records]
    cell_counts = [0] * 10
    for cell in cells:
        cell_counts[cell] += 1

    c_lag = [0] * LAGS
    a_lag = [0] * LAGS
    z_lag = [0] * LAGS
    best = None

    for i in range(COUNT):
        for j in range(i + 1, COUNT):
            lag_index = j - i - 1
            delta = rs[i] * ws[j] - rs[j] * ws[i]
            ten_abs_delta = 10 * abs(delta)
            denominator_product = ws[i] * ws[j]
            same_cell = cells[i] == cells[j]
            if same_cell:
                c_lag[lag_index] += 1
            if ten_abs_delta < denominator_product:
                a_lag[lag_index] += 1
                if delta == 0:
                    z_lag[lag_index] += 1
            if same_cell:
                candidate = (ten_abs_delta, denominator_product, ns[i], ns[j])
                if best is None:
                    best = candidate
                else:
                    num, den, ni, nj = candidate
                    best_num, best_den, best_ni, best_nj = best
                    cross_left = num * best_den
                    cross_right = best_num * den
                    if cross_left > cross_right or (
                        cross_left == cross_right and (ni, nj) < (best_ni, best_nj)
                    ):
                        best = candidate

    for lag_index in range(LAGS):
        if c_lag[lag_index] > a_lag[lag_index]:
            die("lag %d violates C_l <= A_l" % (lag_index + 1))
        if z_lag[lag_index] > a_lag[lag_index]:
            die("lag %d violates Z_l <= A_l" % (lag_index + 1))

    a_sum = sum(a_lag)
    z_sum = sum(z_lag)
    j_value = sum(count * count for count in cell_counts)
    if j_value != COUNT + 2 * sum(c_lag):
        die("J identity fails")

    if 9 * j_value >= 65536:
        branch = "9J_ge_65536"
    elif z_sum > 0:
        branch = "Z_sum_gt_0"
    elif a_sum <= 3512:
        branch = "A_sum_le_3512"
    else:
        branch = "A_sum_gt_3512"

    best_num, best_den, best_ni, best_nj = best
    output = {
        "A_sum": a_sum,
        "J": j_value,
        "Z_sum": z_sum,
        "branch": branch,
        "cell_counts": {str(digit): cell_counts[digit] for digit in range(10)},
        "lag_rows": [
            {"A": a_lag[i], "C": c_lag[i], "Z": z_lag[i], "l": i + 1}
            for i in range(LAGS)
        ],
        "max_same_cell_ratio": {
            "den": str(best_den),
            "n_i": best_ni,
            "n_j": best_nj,
            "num": str(best_num),
        },
    }
    sys.stdout.write(json.dumps(output, sort_keys=True, separators=(",", ":")) + "\n")


if __name__ == "__main__":
    main()
