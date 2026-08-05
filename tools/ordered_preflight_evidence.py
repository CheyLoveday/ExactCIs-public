#!/usr/bin/env python3
"""Record release-tier evidence for the ordered support-width preflight.

Run this script only from a clean environment containing an installed wheel.
It uses public ExactCIs APIs, exercises the real production cap-plus-one table,
and writes the measurement needed for release review.  It is deliberately not
an ordinary-CI test: the workflow archives one measurement from the immutable
release wheel instead.
"""

from __future__ import annotations

import argparse
import json
import os
import platform
import sys
import time
import tracemalloc
from pathlib import Path

try:
    import resource
except ImportError:  # pragma: no cover - the release job runs on Linux.
    resource = None  # type: ignore[assignment]

from exactcis import (
    Design,
    NumericalError,
    __version__,
    exact_ci_blaker,
    exact_ci_minlike,
)

_TABLE = (500_000, 500_000, 500_000, 500_000)
_EXPECTED_DIAGNOSTICS = {
    "support_size": 1_000_001,
    "limit": 1_000_000,
    "limit_kind": "ordered_hull_certification",
}
_SOLVERS = {
    "blaker": exact_ci_blaker,
    "minlike": exact_ci_minlike,
}


def _peak_rss_bytes() -> int | None:
    """Return process peak RSS in bytes when the platform exposes it."""
    if resource is None:
        return None
    peak = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    # macOS reports bytes; Linux and the release runner report KiB.
    return int(peak if sys.platform == "darwin" else peak * 1024)


def _measure(method: str) -> dict[str, object]:
    """Run one production-cap-plus-one public refusal with instrumentation."""
    solver = _SOLVERS[method]
    rss_before = _peak_rss_bytes()
    caught_error: NumericalError | None = None
    elapsed_seconds = 0.0
    tracemalloc_peak_bytes = 0
    tracemalloc.start()
    try:
        tracemalloc.reset_peak()
        started = time.perf_counter()
        try:
            solver(
                *_TABLE,
                0.05,
                design=Design.CASE_CONTROL_FIXED_MARGIN,
            )
        except NumericalError as error:
            caught_error = error
            elapsed_seconds = time.perf_counter() - started
        else:
            raise AssertionError("ordered cap-plus-one call unexpectedly succeeded")
        _, tracemalloc_peak_bytes = tracemalloc.get_traced_memory()
    finally:
        tracemalloc.stop()
    rss_after = _peak_rss_bytes()

    expected = {**_EXPECTED_DIAGNOSTICS, "method": method}
    if caught_error is None:
        raise AssertionError("ordered cap-plus-one call raised no NumericalError")
    if caught_error.method != method or caught_error.diagnostics != expected:
        raise AssertionError(
            "unexpected ordered preflight failure contract: "
            f"method={caught_error.method!r}, diagnostics={caught_error.diagnostics!r}"
        )
    return {
        "diagnostics": caught_error.diagnostics,
        "elapsed_seconds": elapsed_seconds,
        "peak_rss_bytes": rss_after,
        "peak_rss_delta_bytes": (
            None
            if rss_before is None or rss_after is None
            else max(0, rss_after - rss_before)
        ),
        "tracemalloc_peak_bytes": tracemalloc_peak_bytes,
    }


def main(argv: list[str] | None = None) -> int:
    """Write one release-evidence record and enforce its preflight limits."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path, required=True)
    parser.add_argument("--method", choices=tuple(_SOLVERS), default="minlike")
    parser.add_argument("--artifact-sha256", default=None)
    parser.add_argument("--max-seconds", type=float, default=0.01)
    parser.add_argument("--max-tracemalloc-bytes", type=int, default=5_000_000)
    args = parser.parse_args(argv)

    measurement = _measure(args.method)
    elapsed_seconds = float(measurement["elapsed_seconds"])
    tracemalloc_peak_bytes = int(measurement["tracemalloc_peak_bytes"])
    if elapsed_seconds >= args.max_seconds:
        raise AssertionError(
            f"ordered preflight took {elapsed_seconds:.9f}s, "
            f"not below {args.max_seconds:.9f}s"
        )
    if tracemalloc_peak_bytes >= args.max_tracemalloc_bytes:
        raise AssertionError(
            f"ordered preflight allocated {tracemalloc_peak_bytes} bytes, not below "
            f"{args.max_tracemalloc_bytes}"
        )

    report = {
        "artifact_sha256": args.artifact_sha256,
        "github_sha": os.environ.get("GITHUB_SHA"),
        "measurement": measurement,
        "measurement_method": (
            "public API from an installed wheel; time.perf_counter with "
            "tracemalloc enabled (its overhead is included); process maximum "
            "RSS from resource.getrusage"
        ),
        "method": args.method,
        "package_version": __version__,
        "platform": platform.platform(),
        "python_implementation": platform.python_implementation(),
        "python_version": platform.python_version(),
        "status": "refused_as_required",
        "table": _TABLE,
        "thresholds": {
            "max_seconds": args.max_seconds,
            "max_tracemalloc_bytes": args.max_tracemalloc_bytes,
        },
    }
    args.json.parent.mkdir(parents=True, exist_ok=True)
    args.json.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(report, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
