#!/usr/bin/env python3
"""Verify that the rendered method table exactly matches the registry."""

from __future__ import annotations

import argparse
from pathlib import Path

from exactcis.estimands import Design, Estimand, MethodSpec, method_registry

ROOT = Path(__file__).resolve().parents[1]
DOC = ROOT / "docs_md" / "methods.md"
START = "<!-- exactcis-method-table:start -->"
END = "<!-- exactcis-method-table:end -->"
DESIGN_ORDER = {design: index for index, design in enumerate(Design)}


def effect_measure(spec: MethodSpec) -> str:
    if spec.estimand is Estimand.RR:
        return (
            "prevalence ratio"
            if spec.design is Design.CROSS_SECTIONAL
            else "risk ratio"
        )
    if spec.design is Design.CROSS_SECTIONAL:
        return "prevalence odds ratio"
    if spec.design in {Design.STRATIFIED_CASE_CONTROL, Design.STRATIFIED_COHORT}:
        return "common odds ratio"
    return "odds ratio"


def render_table() -> str:
    """Render the canonical registry as the documented nine-column table."""
    lines = [
        (
            "| design | effect measure | method key | construction | status | "
            "point estimator | interval/test type | coverage/calibration statement | "
            "principal limitations |"
        ),
        "|---|---|---|---|---|---|---|---|---|",
    ]
    registry = method_registry()
    source_order = {id(item): index for index, item in enumerate(registry)}
    ordered = sorted(
        registry,
        key=lambda item: (
            DESIGN_ORDER[item.design],
            0 if item.estimand is Estimand.OR else 1,
            source_order[id(item)],
        ),
    )
    for item in ordered:
        cells = (
            item.design.value,
            effect_measure(item),
            f"`{item.method_key}`",
            item.construction,
            item.status,
            item.point_estimator,
            item.interval_type,
            item.calibration,
            item.limitations,
        )
        lines.append("| " + " | ".join(cells) + " |")
    return "\n".join(lines)


def replace_table(text: str, table: str) -> str:
    before, separator, remainder = text.partition(START)
    if not separator:
        raise ValueError(f"missing marker {START}")
    _, separator, after = remainder.partition(END)
    if not separator:
        raise ValueError(f"missing marker {END}")
    return f"{before}{START}\n{table}\n{END}{after}"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    current = DOC.read_text(encoding="utf-8")
    expected = replace_table(current, render_table())
    if args.write:
        DOC.write_text(expected, encoding="utf-8")
        print(f"updated {DOC.relative_to(ROOT)}")
        return 0
    if current != expected:
        print("ERROR: docs_md/methods.md differs from the canonical method registry")
        return 1
    print("OK: method documentation matches the registry")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
