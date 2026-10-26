"""Measure every declared topology attempt, retaining refusals and timeouts.

This is a repository-only diagnostic, not a production cap or CI timing gate.
Scientific outputs and operation counts are exact; time/RSS are observations.
Each case has a fresh subprocess; its last complete stage survives a timeout.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import subprocess
import sys
import tempfile
from dataclasses import asdict
from fractions import Fraction as F
from pathlib import Path
from time import perf_counter_ns

from tests.unconditional import _cell_lanes as lanes
from tests.unconditional import _replay as base
from tests.unconditional import _topology as topology
from tests.unconditional._algebraic import Limits, Work
from tests.unconditional._polynomial import OracleLimitError
from tests.unconditional._topology_replay import SOURCES as TOPOLOGY_SOURCES

SOURCES = (
    *TOPOLOGY_SOURCES,
    "tests/unconditional/_tensor_reference.py",
    "tests/unconditional/_cell_lanes.py",
    "tools/unconditional_oracle/measure_capability.py",
)


def cases(max_total):
    if type(max_total) is not int or not 2 <= max_total <= 6:
        raise ValueError("declared total must be 2 through 6")
    return [
        (n1, total - n1, (x, y))
        for total in range(2, max_total + 1)
        for n1 in range(1, total)
        for x in range(n1 + 1)
        for y in range(total - n1 + 1)
    ] + [(4, 4, (0, 2))]


def _rss():
    # resource is unavailable on Windows. No simulated measurement replaces it.
    if sys.platform not in ("darwin", "linux"):
        return None
    import resource

    native = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return int(native * (1024 if sys.platform == "linux" else 1))


def checkpoint(path, row):
    pending = path.with_suffix(".partial")
    pending.write_bytes(base.canonical_bytes(row))
    pending.replace(path)


def worker(case, path):
    n1, n0, observed = case
    profile = (
        Limits(max_calls=500_000, max_degree=128) if (n1, n0) == (4, 4) else Limits()
    )
    work = Work(profile)
    row = {
        "inputs": {
            "n1": n1,
            "n0": n0,
            "observed": observed,
            "side_level": F(1, 40),
            "alpha": F(1, 20),
        },
        "profile": asdict(profile),
    }
    start = perf_counter_ns()
    try:
        result = topology.topology(n1, n0, tuple(observed), F(1, 40), work=work)
    except OracleLimitError as error:
        row.update(status="resource_refused", reason=str(error))
    else:
        # Retain exact event encodings, ownership, complete components and hull.
        # Full PRS objects are regenerated for their separate canonical digest.
        summary = {
            key: result[key]
            for key in ("events", "components", "ideal_hull", "empty", "full")
        }
        summary["leaves"] = [
            {
                key: leaf[key]
                for key in (
                    "kind",
                    "left_event",
                    "right_event",
                    "accepted",
                    "masks",
                    "pair",
                )
                if key in leaf
            }
            for leaf in result["leaves"]
        ]
        row.update(
            status="topology_complete",
            topology=summary,
            topology_sha256=base.digest("exactcis.topology.output.v4", result),
        )
    row.update(
        counts=work.counts,
        topology_elapsed_ns=perf_counter_ns() - start,
        peak_rss_bytes=_rss(),
    )
    checkpoint(path, row)
    if row["status"] != "topology_complete":
        return
    start = perf_counter_ns()
    row["cell_comparisons"] = lanes.compare_cells(
        n1, n0, tuple(observed), F(1, 40), result
    )
    row.update(
        status="complete",
        lanes_elapsed_ns=perf_counter_ns() - start,
        peak_rss_bytes=_rss(),
    )
    checkpoint(path, row)


def timeout_result(case, path):
    reason = "diagnostic wall timeout; child killed and waited for"
    if path.exists():
        row = json.loads(path.read_bytes())
        if row["status"] == "topology_complete":
            row.update(status="lane_timeout", reason=reason)
        elif row["status"] in ("resource_refused", "complete"):
            row.update(worker_exit_timeout=True, worker_exit_timeout_reason=reason)
        else:
            raise RuntimeError("unknown completed checkpoint stage")
        return row
    return {
        "inputs": {
            "n1": case[0],
            "n0": case[1],
            "observed": case[2],
            "side_level": base.encode(F(1, 40)),
            "alpha": base.encode(F(1, 20)),
        },
        "counts": None,
        "peak_rss_bytes": None,
        "status": "topology_timeout",
        "reason": reason,
    }


def run_case(case, timeout_seconds):
    start = perf_counter_ns()
    with tempfile.TemporaryDirectory(prefix="exactcis-capability-") as directory:
        path = Path(directory) / "stage.json"
        argv = [
            sys.executable,
            "-m",
            "tools.unconditional_oracle.measure_capability",
            "--worker",
            json.dumps(case),
            "--output",
            str(path),
        ]
        try:
            completed = subprocess.run(
                argv,
                cwd=base.ROOT,
                capture_output=True,
                timeout=timeout_seconds,
                check=False,
            )
        except subprocess.TimeoutExpired:
            row = timeout_result(case, path)
        else:
            if completed.returncode:
                raise RuntimeError(completed.stderr.decode("utf-8", errors="replace"))
            row = json.loads(path.read_bytes())
    row["attempt_elapsed_ns"] = perf_counter_ns() - start
    row["timeout_seconds"] = timeout_seconds
    row["input_sha256"] = base.digest("exactcis.capability.input.v1", row["inputs"])
    row["record_sha256"] = base.digest("exactcis.capability.record.v1", row)
    return row


def measure(max_total, timeout_seconds=10):
    rows = []
    for case in cases(max_total):
        row = run_case(
            case, max(60, timeout_seconds) if case[:2] == (4, 4) else timeout_seconds
        )
        rows.append(row)
        print(f"{case}: {row['status']}", flush=True)
    packet = {
        "schema_version": "exactcis.capability_measurement.v1",
        "procedure_version": "boschloo_three_lane_cell_measurement_v1",
        "domain": {"positive_groups_total_at_most": max_total, "extra": [4, 4, 0, 2]},
        "platform": {
            "system": platform.system(),
            "machine": platform.machine(),
            "python": platform.python_version(),
        },
        "units": {
            "time": "integer nanoseconds; elapsed wall time, includes scheduling",
            "peak_rss_bytes": (
                "fresh worker process lifetime peak, including "
                "Python; null if unavailable"
            ),
            "counts": "algebraic wrapper calls, not Fraction or bit operations",
            "cell_counts": (
                "named tensor nodes, witness evaluations, "
                "coefficient builds and rejection boxes"
            ),
        },
        "sources": {
            name: hashlib.sha256((base.ROOT / name).read_bytes()).hexdigest()
            for name in SOURCES
        },
        "results": rows,
        "scientific_claim_ceiling": (
            "finite declared attempts; inconclusions/"
            "refusals retained; no universal completeness "
            "or production cap"
        ),
    }
    packet["measurement_sha256"] = base.digest(
        "exactcis.capability.measurement.v1", packet
    )
    return packet


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-total", type=int, choices=range(2, 7), default=6)
    parser.add_argument("--timeout-seconds", type=int, choices=range(1, 61), default=10)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--worker", help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.worker:
        worker(json.loads(args.worker), args.output)
    else:
        args.output.write_bytes(
            base.canonical_bytes(measure(args.max_total, args.timeout_seconds))
        )


if __name__ == "__main__":
    main()
