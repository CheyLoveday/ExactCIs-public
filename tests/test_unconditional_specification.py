"""Freeze the U0 unconditional release decision while it remains unshipped."""

from __future__ import annotations

import json
from pathlib import Path

import exactcis
from exactcis import exceptions as exactcis_exceptions
from exactcis.estimands import method_registry

ROOT = Path(__file__).resolve().parents[1]
SPEC = ROOT / "docs_md" / "unconditional_exact_specification.md"
START = "<!-- exactcis-unconditional-release-manifest:start -->"
END = "<!-- exactcis-unconditional-release-manifest:end -->"

EXPECTED_MANIFEST: dict[str, object] = {
    "schema": "exactcis.unconditional.release_manifest.v1",
    "status": "specified-unshipped",
    "target_release": "1.2.0",
    "methods": [
        {
            "construction_id": "boschloo_or",
            "designs": ["cohort_binomial", "cross_sectional"],
            "estimand": "odds_ratio",
            "entrypoint": "exact_ci_boschloo",
            "method_key": "boschloo",
            "signature": (
                "exact_ci_boschloo(a: int, b: int, c: int, d: int, "
                "alpha: float, *, design: Design) -> tuple[float, float]"
            ),
        }
    ],
    "deferred_candidates": [
        {
            "construction_id": "barnard_efficient_score_or",
            "entrypoint": "exact_ci_barnard",
            "method_key": "barnard",
            "reason": (
                "candidate-specific exact algebraic comparator and endpoint "
                "ordering require separate approval"
            ),
            "signature": (
                "exact_ci_barnard(a: int, b: int, c: int, d: int, "
                "alpha: float, *, design: Design) -> tuple[float, float]"
            ),
        },
        {
            "construction_id": "exact_efficient_score_rr",
            "entrypoint": "exact_ci_score_rr",
            "method_key": "exact_score_rr",
            "reason": (
                "candidate-specific exact algebraic comparator and endpoint "
                "ordering require separate approval"
            ),
            "signature": (
                "exact_ci_score_rr(a: int, b: int, c: int, d: int, "
                "alpha: float, *, design: Design) -> tuple[float, float]"
            ),
        },
    ],
}


def _release_manifest() -> dict[str, object]:
    text = SPEC.read_text(encoding="utf-8")
    assert text.count(START) == 1, f"expected exactly one marker {START}"
    assert text.count(END) == 1, f"expected exactly one marker {END}"
    _, start, remainder = text.partition(START)
    assert start, f"missing marker {START}"
    payload, end, _ = remainder.partition(END)
    assert end, f"missing marker {END}"
    fenced = payload.strip()
    assert fenced.startswith("```json\n") and fenced.endswith("\n```")
    return json.loads(fenced.removeprefix("```json\n").removesuffix("\n```"))


def test_u0_release_manifest_is_explicit_and_boschloo_only() -> None:
    assert _release_manifest() == EXPECTED_MANIFEST


def test_deferred_score_candidates_are_named_but_not_manifest_methods() -> None:
    manifest = _release_manifest()
    deferred = manifest["deferred_candidates"]
    assert deferred == EXPECTED_MANIFEST["deferred_candidates"]


def test_banked_math_domains_partition_and_u2_anchors_are_explicit() -> None:
    text = SPEC.read_text(encoding="utf-8")
    normalized_text = " ".join(text.split())

    required_fragments = (
        "generic mathematical validity:  0 <= alpha <= 1",
        "ordinary confidence intervals:  0 < alpha < 1",
        "extended real interval `beta in [0,+infinity]`",
        "full compact real interval",
        "Rational `q` values are witnesses or subdivision endpoints only",
        "its supremum is attained",
        "complete certified partition",
        "BOUNDARY_ENCLOSURE` leaves are neither accepted nor rejected",
        "three isolated stationary cells",
        "alpha_side=108/3125",
        "supremum `108/3125` at `q=2/5`",
        "`23/9` accept, `47/17` reject, `3` accept, `25/7` reject",
        "3*psi^3 - 23*psi - 8 = 0",
        "not yet a standalone strict-fixture record",
    )
    assert all(
        " ".join(fragment.split()) in normalized_text for fragment in required_fragments
    )
    assert "finite positive rational effect\n`beta`" not in text


def test_u0_does_not_ship_the_specified_or_deferred_surfaces() -> None:
    proposed_entrypoints = {
        "exact_ci_barnard",
        "exact_ci_boschloo",
        "exact_ci_score_rr",
    }
    proposed_keys = {"barnard", "boschloo", "exact_score_rr"}

    assert proposed_entrypoints.isdisjoint(exactcis.__all__)
    assert all(not hasattr(exactcis, name) for name in proposed_entrypoints)
    assert proposed_keys.isdisjoint({item.method_key for item in method_registry()})
    assert "EmptyConfidenceSetError" not in exactcis.__all__
    assert not hasattr(exactcis, "EmptyConfidenceSetError")
    assert not hasattr(exactcis_exceptions, "EmptyConfidenceSetError")
