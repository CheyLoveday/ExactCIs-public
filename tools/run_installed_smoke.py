#!/usr/bin/env python3
"""Exercise the documented design-aware contract from an installed package."""

from __future__ import annotations

import math
from importlib.metadata import version

from exactcis import (
    Design,
    InferenceResult,
    ValidationError,
    __version__,
    compute_or_with_policy,
    compute_pooled_or,
)


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
    print(f"OK: exactcis {__version__} installed-package smoke")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
