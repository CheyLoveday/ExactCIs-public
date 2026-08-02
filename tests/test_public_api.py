"""Freeze the root API as actual module state, not only an __all__ list."""

from __future__ import annotations

import exactcis
from exactcis import Design

EXPECTED_ROOT = {
    "Design",
    "DesignError",
    "Estimand",
    "ExactCIsError",
    "InferenceResult",
    "NonIdentifiableError",
    "NumericalError",
    "PooledORResult",
    "UnsupportedMethodError",
    "ValidationError",
    "__version__",
    "ci_score_rr",
    "ci_wald",
    "ci_wald_haldane",
    "ci_wald_rr",
    "compute_or_with_policy",
    "compute_pooled_or",
    "compute_rr_with_policy",
    "exact_ci_blaker",
    "exact_ci_conditional",
    "exact_ci_midp",
    "exact_ci_minlike",
}


def test_root_all_is_exactly_the_approved_surface() -> None:
    assert set(exactcis.__all__) == EXPECTED_ROOT
    assert len(exactcis.__all__) == len(set(exactcis.__all__))


def test_plain_import_does_not_attach_excluded_module_families() -> None:
    forbidden = {
        "_internal",
        "analysis",
        "cli",
        "compat",
        "compute",
        "estimands",
        "estimation",
        "evidence",
        "exceptions",
        "inference",
        "plotting",
        "reporting",
        "results",
        "visualization",
    }
    assert forbidden.isdisjoint(vars(exactcis))


def test_removed_historical_root_names_are_absent() -> None:
    removed = {
        "compute_all_cis",
        "compute_all_rr_cis",
        "conditional_mle_or",
        "median_unbiased_or",
        "exact_ci_unconditional",
        "profile_likelihood_ci_or",
        "compute_ps4",
        "plot_forest",
    }
    assert all(not hasattr(exactcis, name) for name in removed)


def test_installed_smoke_contract_uses_design_aware_result() -> None:
    result = exactcis.compute_or_with_policy(
        10,
        2,
        5,
        20,
        design=Design.CASE_CONTROL_FIXED_MARGIN,
    )
    assert result.lower <= result.point <= result.upper
    assert result.method == "conditional"
