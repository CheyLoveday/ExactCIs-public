"""Root-certification regressions (programme issue #13).

Two related gates, one already repaired and one still defective:

* ``solve_monotone_log_parameter`` scales its residual by ``max(1, abs(target))``.
  For the conditional MLE the target is the observed count, so the scale is
  genuine and the large balanced-table false refusals are gone. Locked below.
* The score inversion scales by ``max(1, abs(f_left), abs(f_right), abs(residual))``.
  All three are evaluations of the score function near its own root, so all three
  are small and the scale collapses to exactly ``1.0``. The gate is therefore
  still the original absolute ``1e-8`` test.
"""

from __future__ import annotations

import math

import pytest

from exactcis import (
    ci_score_rr,
    compute_or_with_policy,
    exact_ci_blaker,
    exact_ci_conditional,
)
from exactcis.exceptions import NumericalError

from ._evidence import CASE_CONTROL, COHORT

# Frozen reproducers. Provenance: adjudication pass, 4 August 2026, installed 1.0.0.
SCORE_LARGE_N = (600_000_000, 400_000_000, 400_000_000, 600_000_000)
SCORE_LARGE_N_EXPECTED_UPPER = 1.5001368544
CONDITIONAL_MLE_LOCK = (1400, 1400, 1120, 1680)


@pytest.mark.xfail(
    strict=True,
    reason=(
        "issue #13: score residual scale collapses to 1.0, so the gate stays absolute"
    ),
)
def test_score_inversion_survives_large_denominators() -> None:
    """A well-conditioned root is refused because the residual gate does not scale.

    Total N here is 2e9, comfortably inside the certified per-cell bound of 1e12.
    The root itself is accurate; only the acceptance criterion fails.
    """
    lower, upper = ci_score_rr(*SCORE_LARGE_N, 0.05, design=COHORT)
    assert 0.0 < lower < upper
    assert upper == pytest.approx(SCORE_LARGE_N_EXPECTED_UPPER, rel=1e-6)


@pytest.mark.parametrize(
    "table",
    [
        (600_000, 400_000, 400_000, 600_000),
        (6_000_000, 4_000_000, 4_000_000, 6_000_000),
        (60_000_000, 40_000_000, 40_000_000, 60_000_000),
    ],
)
def test_score_inversion_currently_succeeds_below_the_threshold(table) -> None:
    """Lock the sizes that do work, so a fix cannot narrow the working range."""
    lower, upper = ci_score_rr(*table, 0.05, design=COHORT)
    assert 0.0 < lower <= upper
    assert math.isfinite(lower) and math.isfinite(upper)


def test_residual_gate_scales_with_target_magnitude() -> None:
    """Fast proxy for the repaired conditional-MLE gate, with no FNCH cost.

    The bisection terminates on a relative log-parameter tolerance, so for a
    target of magnitude ``T`` the achievable residual is of order ``T * 2e-12``.
    An absolute ``2e-10`` gate is unsatisfiable once ``T`` exceeds roughly 100,
    regardless of how good the root is. This exercises the scaling directly.
    """
    from exactcis._numerics import solve_monotone_log_parameter

    target = 1.0e8

    def monotone(eta: float) -> float:
        return target + target * eta

    root = solve_monotone_log_parameter(
        monotone, target, increasing=True, method="scale_probe", side="point"
    )
    assert abs(root) <= 1e-11, f"root should be at eta=0, observed {root!r}"
    # The residual an absolute gate would have rejected.
    assert abs(monotone(root) - target) > 2e-10


@pytest.mark.slow
def test_conditional_mle_scale_regression_stays_fixed() -> None:
    """End-to-end lock for the repaired conditional-MLE residual scale.

    Before the ``max(1.0, abs(target))`` scaling this balanced table raised
    ``NumericalError`` from the point-estimate path while the interval route
    succeeded on the identical table. Marked slow because the present quadratic
    evaluator needs minutes at this support width; it becomes fast once the
    replacement kernel (issue #11) lands, at which point the marker should go.
    """
    a, b, c, d = CONDITIONAL_MLE_LOCK
    lower, upper = exact_ci_blaker(a, b, c, d, 0.05, design=CASE_CONTROL)
    assert 0.0 < lower < upper

    result = compute_or_with_policy(a, b, c, d, design=CASE_CONTROL)
    assert result.lower <= result.point <= result.upper

    interval = exact_ci_conditional(a, b, c, d, 0.05, design=CASE_CONTROL)
    assert interval[0] < interval[1]


def test_unbracketed_inversion_still_fails_closed() -> None:
    """Certification changes must not weaken fail-closed behaviour."""
    with pytest.raises(NumericalError):
        exact_ci_conditional(10**11, 1, 1, 10**11, 0.05, design=CASE_CONTROL)


def test_alpha_domain_still_enforced_before_inversion() -> None:
    from exactcis.exceptions import ValidationError

    for alpha in (0.0, 1.0, 1e-12, float("nan")):
        with pytest.raises(ValidationError):
            exact_ci_conditional(5, 2, 5, 8, alpha, design=CASE_CONTROL)
