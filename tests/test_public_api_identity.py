"""Focused checks for the public API differential corpus definition."""

from __future__ import annotations

from pathlib import Path

import pytest

_ROOT = Path(__file__).parents[1]
if not (_ROOT / "tools").is_dir():
    pytest.skip("tools/ not shipped in the public sdist", allow_module_level=True)

from tools.public_api_identity import snapshot  # noqa: E402


def test_public_api_differential_corpus_has_all_expected_calls() -> None:
    """Keep the installed-artifact byte comparison broad and public-only."""
    corpus = snapshot()
    assert corpus["package_version"] == "1.1.2"
    assert [item["name"] for item in corpus["calls"]] == [
        "exact_ci_conditional",
        "exact_ci_midp",
        "exact_ci_minlike_anchor",
        "exact_ci_blaker_anchor",
        "ci_wald",
        "ci_wald_haldane",
        "ci_score_rr_large_anchor",
        "ci_wald_rr",
        "compute_or_with_policy_fixed_margin",
        "compute_or_with_policy_cohort",
        "compute_rr_with_policy_score",
        "compute_rr_with_policy_wald",
        "compute_pooled_or",
    ]
