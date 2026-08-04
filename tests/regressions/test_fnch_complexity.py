"""FNCH evaluation complexity (programme issue #11).

The blocking guard is a deterministic operation count, not wall-clock time.
Combinatorial work units are exactly reproducible across runs and machines;
wall clock varies by several percent even on an idle machine and far more on
shared CI runners, so timing belongs in the benchmark matrix as evidence rather
than in a gate.

Measured against installed 1.0.0: work per evaluation is exactly ``0.5 * W**2``
for balanced supports, because ``_log_choose`` performs ``O(min(k, n-k))`` work
per support point and is called twice per point.
"""

from __future__ import annotations

import pytest

from exactcis import exact_ci_conditional
from exactcis._numerics import fnch_probabilities

from ._evidence import CASE_CONTROL, count_work, support_width

WIDTH_CASES = [(250, 250, 250), (500, 500, 500), (1000, 1000, 1000), (2000, 2000, 2000)]

# Generous constant: the replacement kernel should use a handful of operations
# per support point per evaluation. Anything super-linear blows through this.
LINEAR_WORK_BUDGET_PER_POINT = 12


def _single_evaluation_work(n1: int, n0: int, events: int) -> tuple[int, int]:
    with count_work() as counter:
        fnch_probabilities(n1, n0, events, 0.3)
    return counter.total_work(), support_width(n1, n0, events)


def test_operation_counts_are_deterministic() -> None:
    """The guard is only meaningful if the measurement is exactly reproducible."""
    first = _single_evaluation_work(500, 500, 500)
    second = _single_evaluation_work(500, 500, 500)
    assert first == second


def test_current_kernel_work_is_exactly_quadratic() -> None:
    """Document the present behaviour: ``work / W**2`` is constant at 0.5.

    This test passes on 1.0.0 and must be deleted by the tranche that lands the
    replacement kernel, at which point the linear budget test below takes over.
    """
    ratios = []
    for n1, n0, events in WIDTH_CASES:
        work, width = _single_evaluation_work(n1, n0, events)
        ratios.append(work / (width * width))
    assert all(abs(r - 0.5) < 0.02 for r in ratios), ratios


@pytest.mark.xfail(
    strict=True,
    reason=(
        "issue #11: repeated _log_choose makes evaluation quadratic in support width"
    ),
)
@pytest.mark.parametrize(("n1", "n0", "events"), WIDTH_CASES)
def test_evaluation_work_is_linear_in_support_width(
    n1: int, n0: int, events: int
) -> None:
    work, width = _single_evaluation_work(n1, n0, events)
    assert work <= LINEAR_WORK_BUDGET_PER_POINT * width, (
        f"support width {width} consumed {work} work units "
        f"({work / width:.1f} per point, budget {LINEAR_WORK_BUDGET_PER_POINT})"
    )


@pytest.mark.xfail(
    strict=True,
    reason="issue #11: coefficients are rebuilt at every root evaluation",
)
def test_margins_are_prepared_once_per_inversion() -> None:
    """One interval must prepare the parameter-independent coefficients once.

    On 1.0.0 there is no preparation step at all, so the counter stays at zero
    while the distribution is rebuilt on every evaluation.
    """
    with count_work() as counter:
        exact_ci_conditional(200, 200, 160, 240, 0.05, design=CASE_CONTROL)
    assert counter.fnch_calls > 1, "expected multiple evaluations during inversion"
    assert counter.prepared == 1, (
        f"expected exactly one preparation per inversion, observed {counter.prepared} "
        f"across {counter.fnch_calls} distribution evaluations"
    )


def test_total_interval_work_scales_linearly_with_width() -> None:
    """Evidence-only companion to the gate above, recorded at small widths.

    Kept non-blocking because it measures the whole inversion rather than a
    single evaluation, and the evaluation count itself may legitimately change
    when safeguarded Newton lands.
    """
    observations = []
    for n1 in (100, 200, 400):
        with count_work() as counter:
            exact_ci_conditional(n1, n1, n1, n1, 0.05, design=CASE_CONTROL)
        observations.append((support_width(n1, n1, n1), counter.total_work()))

    growth = observations[-1][1] / observations[0][1]
    width_growth = observations[-1][0] / observations[0][0]
    assert growth > width_growth, (
        "current implementation is expected to grow faster than support width; "
        f"observed {observations}"
    )
