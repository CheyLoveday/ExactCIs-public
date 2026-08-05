#!/usr/bin/env python3
"""Exercise the documented design-aware contract from an installed package."""

from __future__ import annotations

import math
from importlib.metadata import version

import exactcis._numerics as numerics
from exactcis import (
    Design,
    InferenceResult,
    NumericalError,
    ValidationError,
    __version__,
    compute_or_with_policy,
    compute_pooled_or,
    exact_ci_blaker,
    exact_ci_minlike,
)


def _assert_ordered_preflight_contract() -> None:
    """Check the installed ordered failure contract with a bounded test cap.

    This is implementation certification, not a user-facing timing claim: it
    may inspect the shipped private seam to inject a small cap, while invoking
    only public ordered interval functions.  The bounded table avoids any
    support-sized production-cap allocation in wheel and sdist smoke jobs.
    """
    original_cap = numerics._HULL_MAX_WIDTH
    original_prepare = numerics.prepare_margins

    def unexpected_preparation(*args, **kwargs):
        raise AssertionError("ordered preflight entered support preparation")

    numerics._HULL_MAX_WIDTH = 10
    numerics.prepare_margins = unexpected_preparation
    try:
        for method, solver in (
            ("minlike", exact_ci_minlike),
            ("blaker", exact_ci_blaker),
        ):
            try:
                solver(5, 5, 5, 5, 0.05, design=Design.CASE_CONTROL_FIXED_MARGIN)
            except NumericalError as error:
                assert error.method == method
                assert error.diagnostics == {
                    "method": method,
                    "support_size": 11,
                    "limit": 10,
                    "limit_kind": "ordered_hull_certification",
                }
            else:
                raise AssertionError("ordered over-cap call unexpectedly succeeded")
    finally:
        numerics._HULL_MAX_WIDTH = original_cap
        numerics.prepare_margins = original_prepare


def main() -> int:
    result = compute_or_with_policy(
        10,
        2,
        5,
        20,
        design=Design.CASE_CONTROL_FIXED_MARGIN,
    )
    assert isinstance(result, InferenceResult)
    assert result.lower <= result.point <= result.upper
    assert result.design is Design.CASE_CONTROL_FIXED_MARGIN
    assert result.method == "conditional"
    assert __version__ == version("exactcis")

    for alpha in (1e-20, math.nextafter(1.0, 0.0)):
        try:
            compute_or_with_policy(
                10,
                2,
                5,
                20,
                design=Design.COHORT_BINOMIAL,
                method="wald",
                alpha=alpha,
            )
        except ValidationError as exc:
            assert "numerical stability" in str(exc)
        else:
            raise AssertionError("unsupported alpha escaped installed validation")

    strata = [(10, 20, 5, 25), (8, 22, 4, 26)]
    pooled = [
        compute_pooled_or(
            strata,
            design=Design.STRATIFIED_CASE_CONTROL,
            alpha=alpha,
        )
        for alpha in (0.05, 0.50, 0.90)
    ]
    point = pooled[0].point
    assert all(item.point == point for item in pooled)
    assert pooled[0].lower < pooled[1].lower < pooled[2].lower < point
    assert point < pooled[2].upper < pooled[1].upper < pooled[0].upper
    assert all(item.method == "mantel_haenszel" for item in pooled)
    assert all(item.lower != math.exp(-30.0) for item in pooled)
    assert all(item.upper != math.exp(30.0) for item in pooled)
    _assert_ordered_preflight_contract()
    print(f"OK: exactcis {__version__} installed-package smoke")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
