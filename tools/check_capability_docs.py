#!/usr/bin/env python3
"""Generate and verify capability and timing blocks in the methods document."""

from __future__ import annotations

import argparse
import datetime as dt
import json
import runpy
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
DOC = Path("docs_md/methods.md")
EVIDENCE = Path("tools/timing_evidence.json")
LIMITS_START = "<!-- exactcis-capability-table:start -->"
LIMITS_END = "<!-- exactcis-capability-table:end -->"
TIMINGS_START = "<!-- exactcis-timing-table:start -->"
TIMINGS_END = "<!-- exactcis-timing-table:end -->"


def _capability(root: Path) -> dict[str, Any]:
    """Load the dependency-free canonical capability module from ``root``."""
    return runpy.run_path(root / "src/exactcis/_capability.py")


def _value(capability: dict[str, Any], name: str, expected: type[Any]) -> Any:
    """Return one typed capability value or report a malformed canonical source."""
    value = capability.get(name)
    if isinstance(value, bool) or not isinstance(value, expected):
        raise ValueError(f"capability value {name} is missing or has the wrong type")
    return value


def render_limits(root: Path) -> str:
    """Render documented operational limits from ``exactcis._capability``."""
    capability = _capability(root)
    count = _value(capability, "_MAXIMUM_CELL_COUNT", int)
    alpha_margin = _value(capability, "_ALPHA_STABILITY_MARGIN", float)
    prepare_width = _value(capability, "_PREPARE_MAX_WIDTH", int)
    hull_width = _value(capability, "_HULL_MAX_WIDTH", int)
    budget = _value(capability, "_HULL_BOUND_BUDGET", int)
    depth = _value(capability, "_HULL_CERTIFY_DEPTH", int)
    alpha = f"{alpha_margin:.0e}"
    lines = [
        "| documented capability | value | applicability / failure contract |",
        "|---|---:|---|",
        (
            f"| Cell-count bound | `{count:,}` per cell | `ValidationError` before "
            "numerical work |"
        ),
        (
            f"| Certified alpha domain | `{alpha} < alpha < 1 - {alpha}` | "
            "`ValidationError` outside the open domain |"
        ),
        (
            f"| Preparation support-width cap | `{prepare_width:,}` | `conditional`, "
            "`midp`; `NumericalError` before support preparation |"
        ),
        (
            f"| Ordered-hull support-width cap | `{hull_width:,}` | `minlike`, "
            "`blaker`; `NumericalError` before ordered-hull preparation |"
        ),
        (
            f"| Ordered-hull evaluation budget | `{budget:,}` | certification can "
            "refuse below the width cap |"
        ),
        (
            f"| Ordered-hull recursion-depth cap | `{depth:,}` | one rejection "
            "certificate |"
        ),
    ]
    return "\n".join(lines)


def _read_evidence(root: Path) -> tuple[list[dict[str, Any]], str]:
    """Read and validate the version-stamped timing evidence schema."""
    payload = json.loads((root / EVIDENCE).read_text(encoding="utf-8"))
    if not isinstance(payload, dict) or payload.get("schema_version") != 1:
        raise ValueError("timing evidence must be a schema-version 1 JSON object")
    methodology = payload.get("measurement_method")
    rows = payload.get("rows")
    if not isinstance(methodology, str) or not methodology:
        raise ValueError("timing evidence must provide a measurement_method")
    if not isinstance(rows, list) or not rows:
        raise ValueError("timing evidence must provide one or more rows")

    required = (
        "table",
        "method",
        "seconds",
        "outcome",
        "package_version",
        "git_commit",
        "python_version",
        "platform",
        "date",
        "measurement_kind",
    )
    validated: list[dict[str, Any]] = []
    stamp: tuple[str, str, str, str, str] | None = None
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            raise ValueError(f"timing row {index} is not an object")
        missing = [key for key in required if key not in row]
        if missing:
            raise ValueError(f"timing row {index} is missing {', '.join(missing)}")
        if not all(
            isinstance(row[key], str) and row[key]
            for key in required
            if key != "seconds"
        ):
            raise ValueError(f"timing row {index} has an empty text field")
        seconds = row["seconds"]
        if seconds is not None and (
            isinstance(seconds, bool)
            or not isinstance(seconds, int | float)
            or seconds < 0
        ):
            raise ValueError(f"timing row {index} has an invalid seconds value")
        if not isinstance(row["git_commit"], str) or len(row["git_commit"]) != 40:
            raise ValueError(f"timing row {index} must carry a full git commit")
        try:
            dt.date.fromisoformat(row["date"])
        except ValueError as exc:
            raise ValueError(f"timing row {index} has an invalid date") from exc
        current_stamp = tuple(
            row[key]
            for key in (
                "package_version",
                "git_commit",
                "python_version",
                "platform",
                "date",
            )
        )
        if stamp is None:
            stamp = current_stamp
        elif current_stamp != stamp:
            raise ValueError("timing rows must share one package/environment stamp")
        validated.append(row)
    return validated, methodology


def _format_seconds(value: int | float | None) -> str:
    """Format a measured duration while preserving a recorded non-run row."""
    return "not rerun" if value is None else f"{value:.6g}"


def render_timings(root: Path) -> str:
    """Render the timing table from committed clean-wheel evidence."""
    rows, methodology = _read_evidence(root)
    first = rows[0]
    header = (
        f"Measured on `exactcis=={first['package_version']}` at "
        f"`{first['git_commit'][:7]}` with Python {first['python_version']} on "
        f"{first['platform']} ({first['date']}). {methodology}"
    )
    lines = [
        header,
        "",
        "| Table / support width | method | seconds | outcome |",
        "|---|---|---:|---|",
    ]
    for row in rows:
        lines.append(
            "| "
            f"`{row['table']}` | `{row['method']}` | "
            f"{_format_seconds(row['seconds'])} | {row['outcome']} |"
        )
    return "\n".join(lines)


def _replace_block(text: str, start: str, end: str, rendered: str) -> str:
    """Replace the marker-bounded generated block or fail closed."""
    before, separator, remainder = text.partition(start)
    if not separator:
        raise ValueError(f"missing marker {start}")
    _, separator, after = remainder.partition(end)
    if not separator:
        raise ValueError(f"missing marker {end}")
    return f"{before}{start}\n{rendered}\n{end}{after}"


def expected_document(root: Path) -> str:
    """Return the methods document with both generated blocks refreshed."""
    current = (root / DOC).read_text(encoding="utf-8")
    with_limits = _replace_block(current, LIMITS_START, LIMITS_END, render_limits(root))
    return _replace_block(with_limits, TIMINGS_START, TIMINGS_END, render_timings(root))


def main(root: Path, *, write: bool = False) -> int:
    """Check or write generated capability and timing blocks beneath ``root``."""
    root = root.resolve()
    try:
        current = (root / DOC).read_text(encoding="utf-8")
        expected = expected_document(root)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"ERROR: {exc}")
        return 1
    if write:
        (root / DOC).write_text(expected, encoding="utf-8")
        print(f"updated {DOC}")
        return 0
    if current != expected:
        print("ERROR: docs_md/methods.md differs from generated capability evidence")
        return 1
    print("OK: capability and timing documentation matches canonical evidence")
    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    arguments = parser.parse_args()
    raise SystemExit(main(ROOT, write=arguments.write))
