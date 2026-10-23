"""Record every success/refusal in a declared finite topology corpus.

Counts are algebraic wrapper calls, not cumulative Fraction-operation counts.
This experiment is reference evidence; it proposes no production capability cap.
"""

from __future__ import annotations

import argparse
import hashlib
from dataclasses import asdict
from fractions import Fraction
from pathlib import Path

from tests.unconditional import _topology_replay as replay
from tests.unconditional._algebraic import Limits, Work
from tests.unconditional._polynomial import OracleLimitError


def measure(max_total: int, *, expanded: bool = False) -> dict:
    # A separately declared diagnostic profile, not a changed default or a
    # production capability proposal. Degree 128 permits the observed generic
    # PRS intermediates; 500k calls tests the measured 100k/250k work cliffs.
    limits = Limits(max_calls=500_000, max_degree=128) if expanded else Limits()
    cases = [
        (n1, total - n1, (x, y))
        for total in range(2, max_total + 1)
        for n1 in range(1, total)
        for x in range(n1 + 1)
        for y in range(total - n1 + 1)
    ]
    cases.append((4, 4, (0, 2)))
    results = []
    for n1, n0, observed in cases:
        work = Work(limits)
        row = {"n1": n1, "n0": n0, "observed": observed}
        try:
            result = replay.topology.topology(
                n1, n0, observed, Fraction(1, 40), work=work
            )
        except OracleLimitError as error:
            row.update(status="refused", reason=str(error))
        else:
            row.update(
                status="complete",
                output_sha256=replay.base.digest("exactcis.topology.output.v3", result),
                events=len(result["events"]),
                components=len(result["components"]),
            )
        row["counts"] = work.counts
        results.append(row)
        print(f"{n1},{n0},{observed}: {row['status']}", flush=True)
    return {
        "schema": "exactcis.topology_measurement.v3",
        "domain": {"positive_groups_total_at_most": max_total, "extra": [4, 4, 0, 2]},
        "side_level": Fraction(1, 40),
        "profile": asdict(limits),
        "profile_name": replay.EXPANDED_PROFILE if expanded else replay.PROFILE,
        "sources": {
            name: hashlib.sha256((replay.base.ROOT / name).read_bytes()).hexdigest()
            for name in replay.SOURCES
        },
        "measurement_source_sha256": hashlib.sha256(
            Path(__file__).read_bytes()
        ).hexdigest(),
        "specification_sha256": hashlib.sha256(
            (replay.base.ROOT / replay.base.SPEC_PATH).read_bytes()
        ).hexdigest(),
        "results": results,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-total", type=int, choices=(2, 3, 4), default=4)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--expanded", action="store_true")
    args = parser.parse_args()
    args.output.write_bytes(
        replay.base.canonical_bytes(measure(args.max_total, expanded=args.expanded))
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
