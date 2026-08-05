#!/usr/bin/env python3
"""Capture the release differential corpus through ExactCIs public APIs only."""

from __future__ import annotations

import argparse
import json
from collections.abc import Callable
from dataclasses import fields, is_dataclass
from enum import Enum
from pathlib import Path

from exactcis import (
    Design,
    __version__,
    ci_score_rr,
    ci_wald,
    ci_wald_haldane,
    ci_wald_rr,
    compute_or_with_policy,
    compute_pooled_or,
    compute_rr_with_policy,
    exact_ci_blaker,
    exact_ci_conditional,
    exact_ci_midp,
    exact_ci_minlike,
)

_CASE_CONTROL = Design.CASE_CONTROL_FIXED_MARGIN
_COHORT = Design.COHORT_BINOMIAL


def _normalise(value: object) -> object:
    """Encode result bits and public result fields in stable JSON data."""
    if isinstance(value, float):
        return {"float_hex": value.hex()}
    if isinstance(value, Enum):
        return {"enum": f"{type(value).__name__}.{value.name}"}
    if is_dataclass(value):
        return {
            field.name: _normalise(getattr(value, field.name))
            for field in fields(value)
        }
    if isinstance(value, tuple | list):
        return [_normalise(item) for item in value]
    if isinstance(value, str | int | bool) or value is None:
        return value
    raise TypeError(f"unsupported public result value: {value!r}")


def _corpus() -> tuple[tuple[str, Callable[[], object]], ...]:
    """Return successful calls spanning every numerical public entry point."""
    return (
        (
            "exact_ci_conditional",
            lambda: exact_ci_conditional(12, 5, 8, 10, 0.05, design=_CASE_CONTROL),
        ),
        (
            "exact_ci_midp",
            lambda: exact_ci_midp(12, 5, 8, 10, 0.05, design=_CASE_CONTROL),
        ),
        (
            "exact_ci_minlike_anchor",
            lambda: exact_ci_minlike(4, 300, 150, 4, 0.01, design=_CASE_CONTROL),
        ),
        (
            "exact_ci_blaker_anchor",
            lambda: exact_ci_blaker(4, 300, 150, 4, 0.01, design=_CASE_CONTROL),
        ),
        (
            "ci_wald",
            lambda: ci_wald(12, 5, 8, 10, 0.05, design=_COHORT),
        ),
        (
            "ci_wald_haldane",
            lambda: ci_wald_haldane(12, 5, 8, 10, 0.05, design=_COHORT),
        ),
        (
            "ci_score_rr_large_anchor",
            lambda: ci_score_rr(
                600_000_000,
                400_000_000,
                400_000_000,
                600_000_000,
                0.05,
                design=_COHORT,
            ),
        ),
        (
            "ci_wald_rr",
            lambda: ci_wald_rr(12, 5, 8, 10, 0.05, design=_COHORT),
        ),
        (
            "compute_or_with_policy_fixed_margin",
            lambda: compute_or_with_policy(12, 5, 8, 10, design=_CASE_CONTROL),
        ),
        (
            "compute_or_with_policy_cohort",
            lambda: compute_or_with_policy(12, 5, 8, 10, design=_COHORT),
        ),
        (
            "compute_rr_with_policy_score",
            lambda: compute_rr_with_policy(12, 5, 8, 10, design=_COHORT),
        ),
        (
            "compute_rr_with_policy_wald",
            lambda: compute_rr_with_policy(
                12, 5, 8, 10, design=_COHORT, method="wald_rr"
            ),
        ),
        (
            "compute_pooled_or",
            lambda: compute_pooled_or(
                ((10, 20, 5, 25), (8, 22, 4, 26)),
                design=Design.STRATIFIED_CASE_CONTROL,
            ),
        ),
    )


def snapshot() -> dict[str, object]:
    """Return the bit-preserving public-result differential corpus."""
    return {
        "calls": [
            {"name": name, "result": _normalise(call())} for name, call in _corpus()
        ],
        "package_version": __version__,
    }


def main(argv: list[str] | None = None) -> int:
    """Write the corpus to JSON for comparison between clean wheel installs."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path, required=True)
    args = parser.parse_args(argv)
    args.json.parent.mkdir(parents=True, exist_ok=True)
    args.json.write_text(
        json.dumps(snapshot(), indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
