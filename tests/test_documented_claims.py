"""Executable bindings for the numerical claims in the public documentation."""

from __future__ import annotations

import math
from pathlib import Path

import pytest

from exactcis import (
    Design,
    exact_ci_blaker,
    exact_ci_conditional,
    exact_ci_midp,
    exact_ci_minlike,
)
from exactcis._capability import (
    _ALPHA_STABILITY_MARGIN,
    _HULL_MAX_WIDTH,
    _MAXIMUM_CELL_COUNT,
    _MAXIMUM_CERTIFIED_ALPHA,
    _PREPARE_MAX_WIDTH,
    support_width,
)
from exactcis._numerics import prepare_margins
from exactcis._validation import validate_alpha, validate_table
from exactcis.exceptions import NumericalError, ValidationError

ROOT = Path(__file__).resolve().parents[1]
METHODS_DOC = ROOT / "docs_md" / "methods.md"
CASE_CONTROL = Design.CASE_CONTROL_FIXED_MARGIN


def test_active_support_claim_is_bit_identical_to_the_full_recurrence() -> None:
    """The documented active walk skips exact-underflow points only."""
    margins = prepare_margins(10_000, 10_000, 10_000)
    low, high = margins._active_range(0.0)  # noqa: SLF001 - certified private path

    assert high - low < margins.width * 0.30
    assert margins.probabilities(0.0) == margins._probabilities_full(0.0)  # noqa: SLF001


def test_documented_cap_values_match_the_capability_source() -> None:
    """The generated public limits table names the canonical cap values."""
    methods = METHODS_DOC.read_text(encoding="utf-8")

    assert (
        "| Preparation support-width cap | "
        f"`{_PREPARE_MAX_WIDTH:,}` | `conditional`, `midp`"
    ) in methods
    assert (
        "| Ordered-hull support-width cap | "
        f"`{_HULL_MAX_WIDTH:,}` | `minlike`, `blaker`"
    ) in methods


@pytest.mark.parametrize("solver", (exact_ci_conditional, exact_ci_midp))
def test_documented_prepare_cap_has_at_cap_and_cap_plus_one_behaviour(
    monkeypatch: pytest.MonkeyPatch, solver
) -> None:
    """The equal-tail methods keep their common preparation-cap contract."""
    import exactcis._numerics as numerics

    monkeypatch.setattr(numerics, "_PREPARE_MAX_WIDTH", 10)

    assert support_width(9, 10, 9) == 10
    lower, upper = solver(4, 5, 5, 5, 0.05, design=CASE_CONTROL)
    assert 0.0 <= lower <= upper

    assert support_width(10, 10, 10) == 11
    with pytest.raises(NumericalError) as excinfo:
        solver(5, 5, 5, 5, 0.05, design=CASE_CONTROL)
    assert excinfo.value.diagnostics == {"support_size": 11, "limit": 10}


@pytest.mark.parametrize("solver", (exact_ci_minlike, exact_ci_blaker))
def test_documented_ordered_cap_has_at_cap_and_cap_plus_one_behaviour(
    monkeypatch: pytest.MonkeyPatch, solver
) -> None:
    """Ordered inversion admits its injected boundary and refuses the next width."""
    import exactcis._numerics as numerics

    monkeypatch.setattr(numerics, "_HULL_MAX_WIDTH", 10)

    assert support_width(9, 10, 9) == 10
    lower, upper = solver(4, 5, 5, 5, 0.05, design=CASE_CONTROL)
    assert 0.0 <= lower <= upper

    assert support_width(10, 10, 10) == 11
    with pytest.raises(NumericalError) as excinfo:
        solver(5, 5, 5, 5, 0.05, design=CASE_CONTROL)
    assert excinfo.value.diagnostics == {
        "method": "minlike" if solver is exact_ci_minlike else "blaker",
        "support_size": 11,
        "limit": 10,
        "limit_kind": "ordered_hull_certification",
    }


def test_production_cap_boundaries_are_pure_width_calculations() -> None:
    """The public cap limits remain testable without large allocation."""
    assert support_width(9_999_999, 10_000_000, 9_999_999) == _PREPARE_MAX_WIDTH
    assert support_width(10_000_000, 10_000_000, 10_000_000) == (_PREPARE_MAX_WIDTH + 1)
    assert support_width(999_999, 1_000_000, 999_999) == _HULL_MAX_WIDTH
    assert support_width(1_000_000, 1_000_000, 1_000_000) == _HULL_MAX_WIDTH + 1


def test_documented_alpha_and_count_boundaries_match_validation() -> None:
    """The documented alpha domain and count ceiling execute as stated."""
    methods = METHODS_DOC.read_text(encoding="utf-8")
    assert "`1e-12 < alpha < 1 - 1e-12`" in methods
    assert f"`{_MAXIMUM_CELL_COUNT:,}` per cell" in methods

    with pytest.raises(ValidationError):
        validate_alpha(_ALPHA_STABILITY_MARGIN)
    with pytest.raises(ValidationError):
        validate_alpha(_MAXIMUM_CERTIFIED_ALPHA)
    assert validate_alpha(math.nextafter(_ALPHA_STABILITY_MARGIN, math.inf)) > (
        _ALPHA_STABILITY_MARGIN
    )
    assert validate_alpha(math.nextafter(_MAXIMUM_CERTIFIED_ALPHA, 0.0)) < (
        _MAXIMUM_CERTIFIED_ALPHA
    )

    assert validate_table(_MAXIMUM_CELL_COUNT, 0, 0, 0) == (
        _MAXIMUM_CELL_COUNT,
        0,
        0,
        0,
    )
    with pytest.raises(ValidationError):
        validate_table(_MAXIMUM_CELL_COUNT + 1, 0, 0, 0)
