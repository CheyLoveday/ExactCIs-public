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


def test_legacy_kernel_work_was_exactly_quadratic() -> None:
    """The behaviour the replacement kernel removed: ``work / W**2`` constant at 0.5.

    Measured against the retained differential oracle rather than the production
    path, so the historical shape stays documented without keeping the quadratic
    evaluator reachable.
    """
    from exactcis._numerics import _legacy_fnch_probabilities

    ratios = []
    for n1, n0, events in WIDTH_CASES:
        with count_work() as counter:
            _legacy_fnch_probabilities(n1, n0, events, 0.3)
        width = support_width(n1, n0, events)
        ratios.append(counter.total_work() / (width * width))
    assert all(abs(r - 0.5) < 0.02 for r in ratios), ratios


@pytest.mark.parametrize(("n1", "n0", "events"), WIDTH_CASES)
def test_evaluation_work_is_linear_in_support_width(
    n1: int, n0: int, events: int
) -> None:
    work, width = _single_evaluation_work(n1, n0, events)
    assert work <= LINEAR_WORK_BUDGET_PER_POINT * width, (
        f"support width {width} consumed {work} work units "
        f"({work / width:.1f} per point, budget {LINEAR_WORK_BUDGET_PER_POINT})"
    )


def test_margins_are_prepared_once_per_inversion() -> None:
    """One interval prepares the parameter-independent ratios exactly once."""
    with count_work() as counter:
        exact_ci_conditional(200, 200, 160, 240, 0.05, design=CASE_CONTROL)
    assert counter.fnch_calls > 1, "expected multiple evaluations during inversion"
    assert counter.prepared == 1, (
        f"expected exactly one preparation per inversion, observed {counter.prepared} "
        f"across {counter.fnch_calls} distribution evaluations"
    )


def test_ordered_inversion_prepares_once_across_both_endpoints() -> None:
    """The ordered route shares one preparation across the MLE and both transitions."""
    from exactcis import exact_ci_blaker

    with count_work() as counter:
        exact_ci_blaker(30, 20, 15, 35, 0.05, design=CASE_CONTROL)
    assert counter.fnch_calls > 10
    assert counter.prepared == 1


def test_total_interval_work_scales_linearly_with_width() -> None:
    """Whole-inversion work must not grow faster than the support width.

    Allows generous headroom because the evaluation count itself varies a little
    with the table, and may legitimately change when safeguarded Newton lands.
    """
    observations = []
    for n1 in (100, 200, 400):
        with count_work() as counter:
            exact_ci_conditional(n1, n1, n1, n1, 0.05, design=CASE_CONTROL)
        observations.append((support_width(n1, n1, n1), counter.total_work()))

    work_growth = observations[-1][1] / observations[0][1]
    width_growth = observations[-1][0] / observations[0][0]
    assert work_growth <= 2.0 * width_growth, (
        f"work grew {work_growth:.1f}x while support width grew {width_growth:.1f}x; "
        f"observed {observations}"
    )
