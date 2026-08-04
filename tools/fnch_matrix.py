"""Evidence-only benchmark matrix for FNCH evaluation (programme issue #11).

Not a gate. The blocking complexity guard lives in
``tests/regressions/test_fnch_complexity.py`` and is expressed in deterministic
operation counts, because wall-clock thresholds are too noisy on shared runners.
This script produces the human-readable evidence that accompanies it.

Usage:
    python benchmarks/fnch_matrix.py [--max-width 3001] [--json out.json]
"""

from __future__ import annotations

import argparse
import json
import math
import sys
import time
from array import array

from exactcis import Design, exact_ci_conditional
from exactcis._numerics import fnch_probabilities, support_bounds

CASE_CONTROL = Design.CASE_CONTROL_FIXED_MARGIN


def _width(n1: int, n0: int, events: int) -> int:
    lower, upper = support_bounds(n1, n0, events)
    return upper - lower + 1


def evaluation_matrix(cases, repeats: int = 3):
    rows = []
    for n1, n0, events in cases:
        best = math.inf
        for _ in range(repeats):
            start = time.perf_counter()
            fnch_probabilities(n1, n0, events, 0.3)
            best = min(best, time.perf_counter() - start)
        width = _width(n1, n0, events)
        rows.append(
            {"width": width, "seconds": best, "us_per_point": best * 1e6 / width}
        )
    return rows


def interval_matrix(cases):
    rows = []
    for n1, n0, events in cases:
        # Build a concrete table with these margins.
        a = min(n1, events) // 2
        b = n1 - a
        c = events - a
        d = n0 - c
        if min(a, b, c, d) < 0:
            continue
        start = time.perf_counter()
        try:
            exact_ci_conditional(a, b, c, d, 0.05, design=CASE_CONTROL)
            status = "ok"
        except Exception as exc:  # noqa: BLE001 - benchmark records failures as data
            status = type(exc).__name__
        rows.append(
            {
                "table": (a, b, c, d),
                "width": _width(n1, n0, events),
                "seconds": time.perf_counter() - start,
                "status": status,
            }
        )
    return rows


def storage_matrix(size: int = 200_000):
    """List-of-floats versus ``array('d')`` for the coefficient store."""
    values = [float(i) * 1.000001 for i in range(size)]
    packed = array("d", values)

    def timed(seq):
        best = math.inf
        for _ in range(5):
            start = time.perf_counter()
            math.fsum(x * 0.3 for x in seq)
            best = min(best, time.perf_counter() - start)
        return best

    list_bytes = (
        sys.getsizeof(values)
        + sum(sys.getsizeof(x) for x in values[:1000]) / 1000 * size
    )
    return {
        "elements": size,
        "list_seconds": timed(values),
        "array_seconds": timed(packed),
        "list_bytes": int(list_bytes),
        "array_bytes": sys.getsizeof(packed),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-width", type=int, default=2001)
    parser.add_argument("--json", type=str, default=None)
    args = parser.parse_args()

    cases = [(n, n, n) for n in (100, 250, 500, 1000, 2000) if n + 1 <= args.max_width]

    report = {
        "evaluation": evaluation_matrix(cases),
        "interval": interval_matrix(cases),
        "storage": storage_matrix(),
    }

    print("FNCH single-evaluation cost")
    print(f"  {'width':>8} {'seconds':>10} {'us/point':>10}")
    for row in report["evaluation"]:
        print(
            f"  {row['width']:>8} {row['seconds']:>10.4f} {row['us_per_point']:>10.3f}"
        )

    print("\nFull conditional interval")
    print(f"  {'width':>8} {'seconds':>10}  status")
    for row in report["interval"]:
        print(f"  {row['width']:>8} {row['seconds']:>10.3f}  {row['status']}")

    storage = report["storage"]
    print(f"\nCoefficient storage ({storage['elements']:,} elements)")
    list_ms = storage["list_seconds"] * 1000
    array_ms = storage["array_seconds"] * 1000
    list_mb = storage["list_bytes"] / 1e6
    array_mb = storage["array_bytes"] / 1e6
    print(f"  list       {list_ms:7.2f} ms   {list_mb:6.2f} MB")
    print(f"  array('d') {array_ms:7.2f} ms   {array_mb:6.2f} MB")
    ratio = storage["list_bytes"] / storage["array_bytes"]
    slowdown = storage["array_seconds"] / storage["list_seconds"]
    print(
        f"  array uses {ratio:.1f}x less memory and is "
        f"{slowdown:.2f}x the list's iteration time"
    )

    if args.json:
        with open(args.json, "w", encoding="utf-8") as handle:
            json.dump(report, handle, indent=2)
        print(f"\nwrote {args.json}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
