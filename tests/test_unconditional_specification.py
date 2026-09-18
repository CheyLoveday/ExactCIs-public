"""Freeze the U0 mathematics authority while it remains unshipped."""

from __future__ import annotations

import copy
import importlib.util
import json
import re
from collections.abc import Callable
from decimal import Decimal, localcontext
from fractions import Fraction
from math import comb
from pathlib import Path
from typing import Any

import pytest

import exactcis
from exactcis import exceptions as exactcis_exceptions
from exactcis.estimands import method_registry
from exactcis.inference import odds_ratio, relative_risk

ROOT = Path(__file__).resolve().parents[1]
SPEC = ROOT / "docs_md" / "unconditional_exact_specification.md"

EXPECTED_MANIFEST: dict[str, Any] = {
    "schema": "exactcis.unconditional.release_manifest.v2",
    "status": "specified-unshipped",
    "target_release": "1.2.0",
    "scope_lock": "owner-ratified-boschloo-only",
    "widenable_for_target_release": False,
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
    "deferred_nonblocking_research": [
        {
            "research_id": "barnard_efficient_score_or",
            "reason": (
                "formal research only; no 1.2.0 public surface or release blocker"
            ),
        },
        {
            "research_id": "exact_efficient_score_rr",
            "reason": (
                "formal research only; no 1.2.0 public surface or release blocker"
            ),
        },
    ],
}

EXPECTED_TERMINAL: dict[str, Any] = {
    "schema": "exactcis.unconditional.terminal_contract.v1",
    "states": {
        "CERTIFIED_EMPTY": {
            "evidence": "complete sound partition proves O is empty",
            "outcome": "raise EmptyConfidenceSetError",
        },
        "CERTIFIED_FULL": {
            "evidence": (
                "complete sound partition proves I equals the full compact effect "
                "domain and I is a subset of A"
            ),
            "outcome": "return exactly (0.0, inf)",
        },
        "HULL_CERTIFIED": {
            "evidence": "ratified T1-min contract",
            "outcome": "return the outward-converted certified hull",
        },
        "RESOURCE_EXHAUSTED": {
            "evidence": "active deterministic resource limit exhausted",
            "outcome": "raise NumericalError",
        },
        "UNRESOLVED": {
            "evidence": "classification or certificate obligation remains open",
            "outcome": "raise NumericalError",
        },
    },
}

EXPECTED_ASSURANCE: dict[str, Any] = {
    "schema": "exactcis.unconditional.assurance_contract.v1",
    "endpoint_tolerance_field": "hull_endpoint_excess_tolerance",
    "HULL_CERTIFIED": {
        "requires": [
            "accepted_subset_outer",
            "nonempty_inner_subset_accepted",
            "global_lower_beta_endpoint_excess_within_tolerance",
            "global_upper_beta_endpoint_excess_within_tolerance",
            "exact_structural_endpoints",
            "complete_sound_effect_partition",
            "no_invalid_or_unresolved_leaf_omitted_from_outer",
            "same_two_sided_accepted_set_contract",
        ],
        "does_not_require": [
            "component_matching",
            "component_count",
            "interior_gap_classification",
            "complete_accepted_set_topology",
        ],
    },
    "TOPOLOGY_CERTIFIED": {
        "requires": [
            "HULL_CERTIFIED",
            "complete_component_and_gap_classification_or_matching",
        ]
    },
}

EXPECTED_BREAKPOINT: dict[str, Any] = {
    "schema": "exactcis.unconditional.breakpoint_contract.v1",
    "group_sizes": [4, 4],
    "observed": [0, 2],
    "direction": "less",
    "candidate": [1, 3],
    "cross_product_orientation": "T13*den02 - T02*den13",
    "unreduced_numerator_factorization": "-2*psi*(3*psi^3-23*psi-8)",
    "ascending_coefficients": [0, 16, 46, 0, -6],
    "unique_positive_root_decimal": "2.9286857509700537",
    "isolating_bracket": [[29, 10], [59, 20]],
    "membership": {
        "29/10": "out",
        "unique_positive_root": "in_by_equality",
        "59/20": "in",
    },
}

EXPECTED_STRUCTURAL_OR_ENDPOINT: dict[str, Any] = {
    "schema": "exactcis.unconditional.structural_or_endpoint_contract.v1",
    "scope": {
        "construction_id": "boschloo_or",
        "estimand": "odds_ratio",
        "excludes": ["risk_ratio"],
    },
    "tuple_order": ["p_greater", "p_less"],
    "support": {
        "zero": {
            "predicate": "a == 0 or d == 0",
            "supported_pair": [1, 1],
            "unsupported_pair": [0, 1],
        },
        "positive_infinity": {
            "predicate": "c == 0 or b == 0",
            "supported_pair": [1, 1],
            "unsupported_pair": [1, 0],
        },
    },
    "classification": {
        "accepted_if": "p_greater >= alpha_side and p_less >= alpha_side",
        "rejected_if": "p_greater < alpha_side or p_less < alpha_side",
        "threshold_relation": "inclusive",
        "zero_alpha": "all endpoint pairs are accepted when alpha_side == 0",
        "positive_alpha": (
            "an unsupported endpoint pair is rejected when alpha_side > 0"
        ),
    },
    "symmetry": {
        "group_swap": "(a,b,c,d) -> (c,d,a,b)",
        "effect": "zero <-> positive_infinity",
        "directions": "greater <-> less",
    },
}

EXPECTED_MATHEMATICAL_REVIEW_PROVENANCE: dict[str, Any] = {
    "schema": "exactcis.unconditional.mathematical_review_provenance.v1",
    "packet_schema": "exactcis.mathematical_review.packet.v1",
    "packet_filename": "exactcis_1_2_0_math_packet.zip",
    "packet_sha256": (
        # pragma: allowlist nextline secret -- public checksum
        "b2b0a2ff80c1f744a8535a173316402ed235cbe8e25731d4564f6477de5fee43"
    ),
    "packet_hash_note": "public artifact checksum; # pragma: allowlist secret",
    "review_filename": "MATHEMATICAL_REVIEW_1_2_0.md",
    "review_file_sha256": (
        # pragma: allowlist nextline secret -- public checksum
        "6f282cbaadc3feb3b8e93733f0e4e894cbf7180b4c02f4a6db627eea5c30cae2"
    ),
    "review_hash_note": "public artifact checksum; # pragma: allowlist secret",
    # pragma: allowlist nextline secret -- public revision
    "reviewed_main_sha": "a308c7452ede2298f883db6926e12ca3891acb98",
    "main_revision_note": "public Git revision; # pragma: allowlist secret",
    # pragma: allowlist nextline secret -- public revision
    "reviewed_u0_sha": "42b3d4e2e16ff2bbe557e77fb52530ce724ae7e6",
    "u0_revision_note": "public Git revision; # pragma: allowlist secret",
    "status": "research_proofs_and_executed_checks_not_release_candidate",
    "scope": "boschloo_or_u0_only",
    "claim_ceiling": (
        "research proofs and finite regression evidence only; not Lean verification, "
        "runtime conformance, release approval, or a U1/U2 fixture source"
    ),
}

EXPECTED_MATHEMATICAL_TARGET_ROWS: dict[str, tuple[str, str]] = {
    "U-BOSCH-FISHER-ENVELOPE-001": (
        "ExactCIs.Unconditional.BoschlooOrdering.fisherDomination",
        "unshipped target: cheap rejection envelope and T1-min endpoint separation",
    ),
    "U-BOSCH-MASK-STRATUM-001": (
        "ExactCIs.Unconditional.BoschlooOrdering.effectMaskStratification",
        "unshipped target: exact mask cells and exceptional-point owner",
    ),
    "U-BOSCH-INTERIOR-ROOT-001": (
        "ExactCIs.Unconditional.ThresholdDecision.nontrivialBoschlooInteriorRoot",
        "unshipped target: exact fixed-null accept/reject classifier",
    ),
    "U-PARAMETRIC-ROOT-001": (
        "ExactCIs.Unconditional.GlobalInversion.parametricRootStratum",
        "unshipped target: exact whole-stratum classifier",
    ),
    "U-ALGEBRAIC-POINT-001": (
        "ExactCIs.Unconditional.GlobalInversion.exceptionalAlgebraicPoint",
        "unshipped target: exceptional-effect verifier and fail-closed scheduler",
    ),
}

EXPECTED_REVIEW_CORRESPONDENCE: dict[str, tuple[str, str, str]] = {
    "U-BOSCH-FISHER-ENVELOPE-001": (
        "unshipped exclusion scheduler: replay actual-mask Fisher domination "
        "at finite positive effect; observed-margin coefficients, positive "
        "rational side level, directional exponents and cutoff inequalities",
        "theorem target, observed margin, direction, `r`, `C0_fisher`, "
        "`Cinf_fisher`, `delta_fisher`, `M_fisher`, finite-region certificate",
        "no envelope-based rejection; continue another checked route or "
        "refuse; never return a Fisher interval",
    ),
    "U-BOSCH-MASK-STRATUM-001": (
        "unshipped mask partitioner: verify signed cross-products, positive "
        "denominators, permanent zero-polynomial ties, complete positive "
        "ordering-root isolation and inclusive point ownership",
        "theorem target, comparison polynomials, denominator proofs, "
        "identity-tie records, root isolators, chamber masks, "
        "exceptional-point owners",
        "mask unresolved; retain a checked enclosure or refuse; never "
        "substitute a neighbouring mask",
    ),
    "U-BOSCH-INTERIOR-ROOT-001": (
        "unshipped fixed-null classifier: check finite positive effect, "
        "positive exact side level, actual mask and observed tail below one; "
        "verify original endpoint signs, squarefree root-set identities and "
        "signed PRS/Sturm replay",
        "theorem target, effect, direction, `r`, mask digest, original `H`, "
        "squarefree representative, root-set identities, positive-scaling "
        "checks, endpoint variations, distinct-root count",
        "no root-based classification without checked evidence; use the "
        "generic/full-mask branch when applicable or refuse",
    ),
    "U-PARAMETRIC-ROOT-001": (
        "unshipped whole-stratum classifier: verify fixed-mask chamber, "
        "squarefree correspondence over `Q(psi)`, PRS identities, guarded "
        "specialisation and endpoint signs at every real effect; preserve "
        "`for every effect there exists a nuisance`",
        "theorem target, chamber, direction, rational coefficient data, "
        "squarefree identities, nonzero guard polynomials, checked zero-entry "
        "identities, root isolators, degree sequence, endpoint variations, "
        "constant root count",
        "retain a checked `BOUNDARY_ENCLOSURE` or refuse; no common-witness "
        "or sampled replacement",
    ),
    "U-ALGEBRAIC-POINT-001": (
        "unshipped exceptional-point verifier: verify the defining polynomial "
        "and rational isolator select one real embedding; recompute the "
        "actual inclusive mask and replay the specialised root/sign "
        "certificate over that embedding, including generic degenerate "
        "branches",
        "theorem target, defining polynomial, rational isolator, selected "
        "real embedding, exact comparison signs, actual mask digest, "
        "specialised objective and certificate, directional decisions",
        "retain a checked `BOUNDARY_ENCLOSURE` or refuse; no classification "
        "from neighbouring strata",
    ),
}

EXPECTED_CONTRACT_IDS = (
    "U-MANIFEST-001",
    "U-DESIGN-001",
    "U-XSEC-001",
    "U-XSEC-RETURN-001",
    "U-EFFECT-001",
    "U-HULL-TRANSPORT-001",
    "U-OR-CORNER-001",
    "U-OR-NULL-001",
    "U-OR-MASS-001",
    "U-OR-BERN-001",
    "U-OR-CONTROL-001",
    "U-NUISANCE-CONT-001",
    "U-ATTAIN-001",
    "U-BOSCH-ORDER-001",
    "U-BOSCH-REP-001",
    "U-BOSCH-FISHER-ENVELOPE-001",
    "U-BOSCH-MASK-STRATUM-001",
    "U-BOSCH-BREAKPOINT-001",
    "U-BOSCH-SWAP-001",
    "U-MASK-001",
    "U-THRESH-001",
    "U-BERN-CERT-001",
    "U-ROOT-CERT-001",
    "U-BOSCH-INTERIOR-ROOT-001",
    "U-EXACT-P-001",
    "U-COVER-001",
    "U-STRUCT-OR-001",
    "U-STRUCT-OR-VALID-001",
    "U-STRUCT-OR-MASK-001",
    "U-STRUCT-OR-LIMIT-001",
    "U-MOVING-USC-001",
    "U-ACCEPTED-CLOSED-001",
    "U-EFFECT-MASK-001",
    "U-EFFECT-QUANT-001",
    "U-PARAMETRIC-ROOT-001",
    "U-ALGEBRAIC-POINT-001",
    "U-INNER-OUTER-001",
    "U-COMPLETION-001",
    "U-HULL-001",
    "U-EMPTY-001",
    "U-FULL-001",
    "U-TOPOLOGY-001",
    "U-FLOAT-001",
)


def _text() -> str:
    return SPEC.read_text(encoding="utf-8")


def _unique_json_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON authority key: {key}")
        result[key] = value
    return result


def _json_block(text: str, name: str) -> dict[str, Any]:
    start = f"<!-- exactcis-unconditional-{name}:start -->"
    end = f"<!-- exactcis-unconditional-{name}:end -->"
    assert text.count(start) == 1, f"expected exactly one marker {start}"
    assert text.count(end) == 1, f"expected exactly one marker {end}"
    _, found_start, remainder = text.partition(start)
    assert found_start, f"missing marker {start}"
    payload, found_end, _ = remainder.partition(end)
    assert found_end, f"missing marker {end}"
    fenced = payload.strip()
    assert fenced.startswith("```json\n") and fenced.endswith("\n```")
    parsed = json.loads(
        fenced.removeprefix("```json\n").removesuffix("\n```"),
        object_pairs_hook=_unique_json_object,
    )
    assert isinstance(parsed, dict)
    return parsed


def _assert_manifest_authority(payload: dict[str, Any]) -> None:
    assert set(payload) == {
        "schema",
        "status",
        "target_release",
        "scope_lock",
        "widenable_for_target_release",
        "methods",
        "deferred_nonblocking_research",
    }
    assert payload["schema"] == "exactcis.unconditional.release_manifest.v2"
    assert payload["status"] == "specified-unshipped"
    assert payload["target_release"] == "1.2.0"
    assert payload["scope_lock"] == "owner-ratified-boschloo-only"
    assert payload["widenable_for_target_release"] is False
    methods = payload["methods"]
    assert isinstance(methods, list) and len(methods) == 1
    method = methods[0]
    assert method["construction_id"] == "boschloo_or"
    assert method["designs"] == ["cohort_binomial", "cross_sectional"]
    assert method["estimand"] == "odds_ratio"
    assert method["entrypoint"] == "exact_ci_boschloo"
    assert method["method_key"] == "boschloo"
    assert method["signature"] == EXPECTED_MANIFEST["methods"][0]["signature"]
    research_rows = payload["deferred_nonblocking_research"]
    assert [row["research_id"] for row in research_rows] == [
        "barnard_efficient_score_or",
        "exact_efficient_score_rr",
    ]
    for research in research_rows:
        assert set(research) == {"research_id", "reason"}
        assert "no 1.2.0 public surface or release blocker" in research["reason"]


def _assert_terminal_authority(payload: dict[str, Any]) -> None:
    assert payload["schema"] == "exactcis.unconditional.terminal_contract.v1"
    states = payload["states"]
    assert set(states) == {
        "CERTIFIED_EMPTY",
        "CERTIFIED_FULL",
        "HULL_CERTIFIED",
        "RESOURCE_EXHAUSTED",
        "UNRESOLVED",
    }
    assert states["CERTIFIED_EMPTY"]["evidence"] == (
        "complete sound partition proves O is empty"
    )
    assert states["CERTIFIED_EMPTY"]["outcome"] == ("raise EmptyConfidenceSetError")
    assert (
        "I equals the full compact effect domain"
        in states["CERTIFIED_FULL"]["evidence"]
    )
    assert states["CERTIFIED_FULL"]["outcome"] == "return exactly (0.0, inf)"
    assert states["HULL_CERTIFIED"]["evidence"] == "ratified T1-min contract"
    assert states["UNRESOLVED"]["outcome"] == "raise NumericalError"
    assert states["RESOURCE_EXHAUSTED"]["outcome"] == "raise NumericalError"


def _assert_assurance_authority(payload: dict[str, Any]) -> None:
    assert payload["schema"] == "exactcis.unconditional.assurance_contract.v1"
    assert payload["endpoint_tolerance_field"] == ("hull_endpoint_excess_tolerance")
    hull = payload["HULL_CERTIFIED"]
    assert set(hull["requires"]) == set(
        EXPECTED_ASSURANCE["HULL_CERTIFIED"]["requires"]
    )
    assert set(hull["does_not_require"]) == set(
        EXPECTED_ASSURANCE["HULL_CERTIFIED"]["does_not_require"]
    )
    assert "component_matching" not in hull["requires"]
    assert "component_matching" in hull["does_not_require"]
    assert payload["TOPOLOGY_CERTIFIED"]["requires"] == [
        "HULL_CERTIFIED",
        "complete_component_and_gap_classification_or_matching",
    ]


def _assert_structural_or_endpoint_authority(payload: dict[str, Any]) -> None:
    assert payload == EXPECTED_STRUCTURAL_OR_ENDPOINT
    assert payload["schema"] == (
        "exactcis.unconditional.structural_or_endpoint_contract.v1"
    )
    assert payload["tuple_order"] == ["p_greater", "p_less"]

    scope = payload["scope"]
    assert scope == {
        "construction_id": "boschloo_or",
        "estimand": "odds_ratio",
        "excludes": ["risk_ratio"],
    }

    zero = payload["support"]["zero"]
    infinity = payload["support"]["positive_infinity"]
    assert zero == {
        "predicate": "a == 0 or d == 0",
        "supported_pair": [1, 1],
        "unsupported_pair": [0, 1],
    }
    assert infinity == {
        "predicate": "c == 0 or b == 0",
        "supported_pair": [1, 1],
        "unsupported_pair": [1, 0],
    }

    classification = payload["classification"]
    assert classification["accepted_if"] == (
        "p_greater >= alpha_side and p_less >= alpha_side"
    )
    assert classification["rejected_if"] == (
        "p_greater < alpha_side or p_less < alpha_side"
    )
    assert classification["threshold_relation"] == "inclusive"
    assert classification["zero_alpha"] == (
        "all endpoint pairs are accepted when alpha_side == 0"
    )
    assert classification["positive_alpha"] == (
        "an unsupported endpoint pair is rejected when alpha_side > 0"
    )
    assert payload["symmetry"] == {
        "group_swap": "(a,b,c,d) -> (c,d,a,b)",
        "effect": "zero <-> positive_infinity",
        "directions": "greater <-> less",
    }


def _structural_or_endpoint_pair(
    a: int,
    b: int,
    c: int,
    d: int,
    endpoint: str,
) -> tuple[Fraction, Fraction]:
    """Independent exact fixture oracle for the ratified OR endpoint pairs."""
    if endpoint == "zero":
        return (
            (Fraction(1), Fraction(1))
            if a == 0 or d == 0
            else (
                Fraction(0),
                Fraction(1),
            )
        )
    if endpoint == "positive_infinity":
        return (
            (Fraction(1), Fraction(1))
            if c == 0 or b == 0
            else (
                Fraction(1),
                Fraction(0),
            )
        )
    raise AssertionError(f"unknown structural endpoint: {endpoint}")


def _structural_endpoint_accepts(
    pair: tuple[Fraction, Fraction], alpha_side: Fraction
) -> bool:
    return pair[0] >= alpha_side and pair[1] >= alpha_side


def _structural_or_supports(
    a: int,
    b: int,
    c: int,
    d: int,
    endpoint: str,
) -> bool:
    """Direct table support predicate for the endpoint contract."""
    if endpoint == "zero":
        return a == 0 or d == 0
    if endpoint == "positive_infinity":
        return c == 0 or b == 0
    raise AssertionError(f"unknown structural endpoint: {endpoint}")


def _product_binomial_table_mass(
    a: int,
    b: int,
    c: int,
    d: int,
    *,
    p1: Fraction,
    p0: Fraction,
) -> Fraction:
    """Exact mass of a 2x2 table under independent product binomials."""
    n1 = a + b
    n0 = c + d
    return (
        Fraction(comb(n1, a) * comb(n0, c))
        * p1**a
        * (1 - p1) ** b
        * p0**c
        * (1 - p0) ** d
    )


def _product_binomial_event_mass(
    n1: int,
    n0: int,
    *,
    p1: Fraction,
    p0: Fraction,
    event: Callable[[int, int, int, int], bool],
) -> Fraction:
    return sum(
        (
            _product_binomial_table_mass(
                a,
                n1 - a,
                c,
                n0 - c,
                p1=p1,
                p0=p0,
            )
            for a in range(n1 + 1)
            for c in range(n0 + 1)
            if event(a, n1 - a, c, n0 - c)
        ),
        start=Fraction(0),
    )


def _poly_multiply(left: list[int], right: list[int]) -> list[int]:
    result = [0] * (len(left) + len(right) - 1)
    for left_index, left_value in enumerate(left):
        for right_index, right_value in enumerate(right):
            result[left_index + right_index] += left_value * right_value
    return result


def _poly_subtract(left: list[int], right: list[int]) -> list[int]:
    width = max(len(left), len(right))
    return [
        (left[index] if index < len(left) else 0)
        - (right[index] if index < len(right) else 0)
        for index in range(width)
    ]


def _poly_evaluate(coefficients: list[int], value: Fraction) -> Fraction:
    result = Fraction(0)
    for coefficient in reversed(coefficients):
        result = result * value + coefficient
    return result


def _positive_root_decimal() -> str:
    with localcontext() as context:
        context.prec = 60
        lower = Decimal(29) / Decimal(10)
        upper = Decimal(59) / Decimal(20)
        for _ in range(220):
            midpoint = (lower + upper) / 2
            value = 3 * midpoint**3 - 23 * midpoint - 8
            if value < 0:
                lower = midpoint
            else:
                upper = midpoint
        return format((lower + upper) / 2, ".16f")


def _assert_breakpoint_authority(payload: dict[str, Any]) -> None:
    assert payload["schema"] == "exactcis.unconditional.breakpoint_contract.v1"
    assert payload["group_sizes"] == [4, 4]
    assert payload["observed"] == [0, 2]
    assert payload["direction"] == "less"
    assert payload["candidate"] == [1, 3]
    assert payload["cross_product_orientation"] == "T13*den02 - T02*den13"
    assert payload["unreduced_numerator_factorization"] == ("-2*psi*(3*psi^3-23*psi-8)")

    # T13*den02 - T02*den13, with coefficients in ascending order.
    reconstructed = _poly_subtract(
        _poly_multiply([1, 16], [6, 16, 6]),
        _poly_multiply([6], [1, 16, 36, 16, 1]),
    )
    factorized = _poly_multiply([0, -2], [-8, -23, 0, 3])
    assert reconstructed == factorized == payload["ascending_coefficients"]

    lower = Fraction(*payload["isolating_bracket"][0])
    upper = Fraction(*payload["isolating_bracket"][1])
    assert _poly_evaluate(reconstructed, lower) == Fraction(44457, 5000)
    assert _poly_evaluate(reconstructed, upper) == Fraction(-550883, 80000)
    assert payload["unique_positive_root_decimal"] == _positive_root_decimal()
    assert payload["membership"]["29/10"] == "out"
    assert payload["membership"]["unique_positive_root"] == "in_by_equality"
    assert payload["membership"]["59/20"] == "in"


def _assert_binding_text(text: str) -> None:
    normalized = " ".join(text.split())
    required = (
        (
            "Status: **specified but unshipped.** This document is U0 authority only "
            "when introduced to `main` by an explicitly owner-approved immutable-head "
            "merge. It does not authorize unconditional production implementation."
        ),
        (
            "It is the candidate U0-A/U0-B contract for programme issue #41 and "
            "records the #64-ratified structural OR endpoint lock."
        ),
        "p[m,greater,x](beta) >= alpha_side",
        "p[m,less,x](beta) >= alpha_side",
        "directional p-value is **strictly less** than `alpha_side`",
        "(p_greater, p_less).",
        "`a = 0 or d = 0`",
        "`c = 0 or b = 0`",
        "At `alpha_side = 0`, inclusive equality accepts every endpoint",
        "This contract is OR/Boschloo-only.",
        "STRUCTURAL_REJECTED` is impossible at `alpha_side = 0`",
        "min(x,n0-y) >= min(a,d)",
        "min(y,n1-x) >= min(c,b)",
        "constants independent of nuisance",
        "for every beta in C there exists a nuisance q",
        "Failures at unrelated effect points cannot be combined.",
        ("`D` vanishes exactly at the two corners `(s,q)=(0,1)` and `(s,q)=(1,0)`"),
        "No continuity argument may cross or fill either corner.",
        "A_s = c[A[m,x]]",
        "Membership of the tagged points `s=0` and `s=1` is decided by B.9",
        "empty != I subseteq A_s",
        "b_ext(lower_s(I)) - b_ext(lower_s(O)) <= epsilon_beta",
        "b_ext(upper_s(O)) - b_ext(upper_s(I)) <= epsilon_beta",
        "I and O derived from the same two-sided accepted-set contract",
        "inner_nonempty: I is nonempty;",
        "b_ext(lower_s(A)) - b_ext(lower_s(O)) <= epsilon",
        "b_ext(upper_s(O)) - b_ext(upper_s(A)) <= epsilon",
        "T1 inequalities are consumed to prove endpoint excess",
        "If `s=0` is rejected, a **positive** lower claim requires `lower_s(O)>0`",
        "If `s=1` is rejected, a finite upper claim requires `upper_s(O)<1`",
        "the returned upper endpoint is exactly `inf`",
        "hull_endpoint_excess_tolerance",
        "A large unmatched extreme sliver forces refinement or fail-closed refusal.",
        (
            "Component-to-component matching, component counts, interior-gap "
            "classification, and complete accepted-set topology are **not** "
            "premises of `HULL_CERTIFIED`."
        ),
        "The terminal branches are distinct.",
        "Empty, full, and hull are sibling terminal branches",
        "FIXED-NULL-BASE + FIXED-NULL-EVIDENCE -> fixed-null exact decisions",
        "fixed-positive-total ideal coverage + U-XSEC-001",
        "The complete-domain case split -> fixed-positive-total ideal coverage",
        "U-MOVING-USC-001 -> U-ACCEPTED-CLOSED-001",
        "ideal branch of U-COVER-001 + (U-HULL-001 OR U-FULL-001)",
        "U-HULL-001 + U-ACCEPTED-CLOSED-001",
        "U-XSEC-RETURN-001",
        "fixed-positive-total return bounds from (`U-HULL-001` or `U-FULL-001`)",
        "#check @RootSignCertificate.existsComplete :",
        "#check @Structural.orEndpoints :",
        "#check @Structural.orFibreSupportAlmostSure :",
        "#check @Structural.orFibreTwoSidedValidity :",
        "#check @BoschlooOrdering.eventualZeroGreaterMaskStratum :",
        "#check @BoschlooOrdering.eventualPositiveInfinityLessMaskStratum :",
        "#check @BoschlooOrdering.groupSwapFiniteMask :",
        "#check @Structural.orEndpointUniformLimits :",
        "#check @Structural.hullTransport :",
        "#check @GlobalInversion.movingPUpperSemicontinuous :",
        "#check @GlobalInversion.acceptedSetClosed :",
        "#check @GlobalInversion.adaptiveCompletion :",
        "effect split or degree elevation is followed only by nuisance refinement",
        "Berger--Boos nuisance adjustment is excluded",
        (
            '`compute_or_with_policy(a, b, c, d, design=design, method="boschloo", '
            "alpha=alpha)`"
        ),
        "Certificates and verifier types remain internal evidence in 1.2.0",
        "**Implementation status: blocked.**",
        (
            "Production unconditional Python remains blocked until #48, #51, "
            "#52, and #49 close"
        ),
    )
    assert all(" ".join(fragment.split()) in normalized for fragment in required)
    assert "exact-head approval pending" not in normalized
    assert "This exact-head candidate" not in normalized
    assert "does not add it, and it is not currently public" in normalized


def _assert_structural_repair_authority(text: str) -> None:
    """Guard the two mathematical repairs required before a U0 merge review."""
    normalized = " ".join(text.split())
    required = (
        (
            "This finite ordered-p lemma does **not** certify the separately "
            "tagged endpoints"
        ),
        "P[n1,n0,p1,p0](a = 0 or d = 0) = 1",
        "P[n1,n0,p1,p0](c = 0 or b = 0) = 1",
        "U-STRUCT-OR-VALID-001",
        "must join this structural branch (`U-STRUCT-OR-VALID-001`) with the finite",
        "all-failure corner `(p1,p0)=(0,0)`",
        "all-success corner `(p1,p0)=(1,1)`",
        "it does not invent a unique true OR",
        "BoschlooOrdering.finiteMask z dir psi",
        "finiteMaskMass(z,dir,psi,q)",
        "finiteP(z,dir,psi)",
        "#check @BoschlooOrdering.finiteMaskMass_eq :",
        "#check @BoschlooOrdering.finiteP_eq :",
        "#check @Structural.zeroUnsupportedFiniteMaskMassBound :",
        "#check @Structural.zeroUnsupportedFinitePBound :",
        "#check @Structural.positiveInfinityUnsupportedFiniteMaskMassBound :",
        "#check @Structural.positiveInfinityUnsupportedFinitePBound :",
        "one `delta`/`M` before all finite effects and candidates",
        "a tagged endpoint mask is -- not an admissible replacement premise",
        "reciprocal finite-mask transport for the infinity theorem",
    )
    assert all(" ".join(fragment.split()) in normalized for fragment in required)
    assert "BoschlooOrdering.structuralMask" not in text

    zero_start = text.index("#check @BoschlooOrdering.eventualZeroGreaterMaskStratum :")
    infinity_start = text.index(
        "#check @BoschlooOrdering.eventualPositiveInfinityLessMaskStratum :"
    )
    swap_start = text.index("#check @BoschlooOrdering.groupSwapFiniteMask :")
    zero = text[zero_start:infinity_start]
    infinity = text[infinity_start:swap_start]
    for theorem, expected_order in (
        (
            zero,
            (
                "observed : TableAt n1 n0",
                "∃ delta : Real, 0 < delta ∧ delta ≤ 1 ∧",
                "∀ (psi : Real), 0 < psi → psi ≤ delta →",
                "∀ candidate : TableAt n1 n0,",
                "candidate ∈ BoschlooOrdering.finiteMask observed .greater psi",
            ),
        ),
        (
            infinity,
            (
                "observed : TableAt n1 n0",
                "∃ M : Real, 1 < M ∧",
                "∀ (psi : Real), M ≤ psi →",
                "∀ candidate : TableAt n1 n0,",
                "candidate ∈ BoschlooOrdering.finiteMask observed .less psi",
            ),
        ),
    ):
        assert all(fragment in theorem for fragment in expected_order)
        positions = [theorem.index(fragment) for fragment in expected_order]
        assert positions == sorted(positions)
        assert " q" not in theorem

    mass_start = text.index("#check @BoschlooOrdering.finiteMaskMass_eq :")
    p_value_start = text.index("#check @BoschlooOrdering.finiteP_eq :")
    mass_bound_start = text.index(
        "#check @Structural.zeroUnsupportedFiniteMaskMassBound :"
    )
    limits_start = text.index("#check @Structural.orEndpointUniformLimits :")
    mass_definition = text[mass_start:p_value_start]
    p_value_definition = text[p_value_start:mass_bound_start]
    limits = text[mass_bound_start:limits_start]
    assert "ProductBinomial.mass n1 n0" in mass_definition
    assert "candidate ∈\n          BoschlooOrdering.finiteMask" in mass_definition
    assert "sSup (BoschlooOrdering.finiteMaskMass" in p_value_definition
    assert "Set.Icc (0 : Real) 1" in p_value_definition
    assert "BoschlooOrdering.finiteMaskMass observed .greater psi q" in limits
    assert "BoschlooOrdering.finiteMaskMass observed .less psi q" in limits
    assert "BoschlooOrdering.finiteP observed .greater psi" in limits
    assert "BoschlooOrdering.finiteP observed .less psi" in limits
    assert "BoschlooDirectionalTail" not in limits


def _assert_mathematical_review_provenance(payload: dict[str, Any]) -> None:
    assert (
        payload["schema"] == "exactcis.unconditional.mathematical_review_provenance.v1"
    )
    assert payload["packet_schema"] == "exactcis.mathematical_review.packet.v1"
    assert payload["packet_filename"] == "exactcis_1_2_0_math_packet.zip"
    assert (
        payload["packet_sha256"]
        == EXPECTED_MATHEMATICAL_REVIEW_PROVENANCE["packet_sha256"]
    )
    assert (
        payload["review_filename"]
        == EXPECTED_MATHEMATICAL_REVIEW_PROVENANCE["review_filename"]
    )
    assert (
        payload["review_file_sha256"]
        == EXPECTED_MATHEMATICAL_REVIEW_PROVENANCE["review_file_sha256"]
    )
    assert (
        payload["reviewed_main_sha"]
        == EXPECTED_MATHEMATICAL_REVIEW_PROVENANCE["reviewed_main_sha"]
    )
    assert (
        payload["reviewed_u0_sha"]
        == EXPECTED_MATHEMATICAL_REVIEW_PROVENANCE["reviewed_u0_sha"]
    )
    assert (
        payload["status"] == "research_proofs_and_executed_checks_not_release_candidate"
    )
    assert payload["scope"] == "boschloo_or_u0_only"
    for fragment in (
        "not Lean verification, runtime conformance, release approval",
        "or a U1/U2 fixture source",
    ):
        assert fragment in payload["claim_ceiling"]


def _assert_fisher_envelope_authority(text: str) -> None:
    section = text.split(
        "#### B.5.1 Fisher domination and finite endpoint envelope", 1
    )[1].split("#### B.5.2 Finite algebraic mask strata", 1)[0]
    normalized = " ".join(section.split())
    required = (
        "P[psi,q](R_dir(psi)) <= F_dir(a,c;psi),",
        "finiteP(observed,dir,psi) <= F_dir(a,c;psi).",
        "For the observed table `(a,b,c,d)` and its margin `m=a+c`,",
        "e0 = a-ell = min(a,d),",
        "C0_fisher = sum[k=a..h] c_k / c_ell,",
        "finiteP(observed,greater,psi) <= C0_fisher * psi^e0 for 0<psi<=1.",
        "einf = h-a = min(b,c),",
        "Cinf_fisher = sum[k=ell..a] c_k / c_h,",
        "finiteP(observed,less,psi) <= Cinf_fisher / psi^einf for psi>=1.",
        "delta_fisher = min(1/2, r/(2*C0_fisher)),",
        "M_fisher = max(2, 2*Cinf_fisher/r)",
        "Fisher domination is an exclusion theorem only:",
        "no implementation may return a Fisher interval under the Boschloo name.",
        "does **not** replace the actual-finite-mask route",
        "`U-STRUCT-OR-MASK-001` and `U-STRUCT-OR-LIMIT-001`",
        "`C0_mask` and `Cinf_mask`",
    )
    assert all(" ".join(fragment.split()) in normalized for fragment in required)

    structural_heading = "### B.9 Structural decisions and observed point estimates"
    structural = text.split(structural_heading, 1)[1].split(
        "For positive group totals", 1
    )[0]
    structural_normalized = " ".join(structural.split())
    assert (
        "B.5.1 Fisher envelope independently supplies a certified finite-effect "
        "separation." in structural_normalized
    )
    assert "does not assign either structural pair" in structural_normalized
    assert (
        "direct support-based authority at the tagged endpoints"
        in structural_normalized
    )


def _assert_fixed_null_reduction_authority(text: str) -> None:
    section = text.split("#### B.6.1 Nontrivial Boschloo interior-root reduction", 1)[
        1
    ].split("If ordering comparison yields certified masks", 1)[0]
    normalized = " ".join(section.split())
    required = (
        "call the directional case nontrivial when `F_d(a,c;psi)<1`.",
        "H_d,psi(0) = -r < 0,",
        "H_d,psi(1) = -r*psi^n1 < 0.",
        "finiteP(observed,d,psi) >= r\n"
        "    iff there exists q in (0,1) with H_d,psi(q) = 0.",
        "its mask is the full sample space and the directional p-value is exactly one",
        "deliberately outside this endpoint-negative specialisation.",
        "zero-level, zero-polynomial, constant, degree-drop, and "
        "endpoint-root branches",
        "checked squarefree reduction must preserve exactly the real root set",
        "Squarefree reduction need not preserve the sign of `H`;",
        "original `H` retains the endpoint signs and accepted-equality semantics.",
        "Positive scaling is a separate normalisation check",
        "does not assert that a squarefree representative is a positive "
        "multiple of `H`.",
        "A repeated or even-multiplicity interior root still accepts.",
        "Neither numerical maximisation, an argmax enclosure, "
        "stationary-point enumeration, nor a rational grid",
    )
    assert all(" ".join(fragment.split()) in normalized for fragment in required)


def _assert_global_root_strata_authority(text: str) -> None:
    mask_section = text.split("#### B.5.2 Finite algebraic mask strata", 1)[1].split(
        "### B.6 Exact fixed-null decision", 1
    )[0]
    section = text.split(
        "#### B.11.1 Exact fixed-mask strata and exceptional effects", 1
    )[1].split("Let the extended beta domain", 1)[0]
    normalized = " ".join(section.split())
    mask_required = (
        "`z in R_d(psi)` exactly when `G_z(psi)<=0`.",
        "zero polynomial is a permanent equality tie",
        "separately owned algebraic comparison points",
        "recompute the actual inclusive mask",
    )
    stratum_required = (
        "take a squarefree representative over `Q(psi)`",
        "content and squarefree-specialisation guards",
        "An identically zero endpoint entry is recorded as a checked zero identity,",
        "excluded from partition guards, and omitted when counting sign variations.",
        "Its denominator and squarefree-specialisation guards remain in force.",
        "Isolate roots only of nonzero guard polynomials;",
        "an isolated zero of a nonzero entry still owns an exceptional effect",
        "at **every real effect**.",
        "for every effect there exists a nuisance",
        "not assert one nuisance witness for the entire stratum.",
        "Squarefree reduction occurs before resultants or projection.",
        "raw resultant with its `q`-derivative vanishes identically",
        "actual inclusive mask, then specialises the root certificate",
        "must not evaluate a parameterised chain through a vanishing denominator",
        "use a neighbouring mask",
        "retains a `BOUNDARY_ENCLOSURE` or refuses",
    )
    assert "G_z(psi) = P_z(psi)*W_o(psi) - P_o(psi)*W_z(psi)" in mask_section
    assert all(
        " ".join(fragment.split()) in " ".join(mask_section.split())
        for fragment in mask_required
    )
    assert all(
        " ".join(fragment.split()) in normalized for fragment in stratum_required
    )


def _contract_ids(text: str) -> list[str]:
    table = text.split("### B.16 Formalisation target table", 1)[1].split(
        "#### B.16.1 Theorem dependency DAG", 1
    )[0]
    rows = [line for line in table.splitlines() if line.lstrip().startswith("|")]
    assert len(rows) >= 3
    assert all(row == row.lstrip() for row in rows), "indented B.16 table row"
    assert rows[0].startswith("| contract ID |")
    assert re.fullmatch(r"\|(?:---\|){5}---\|", rows[1])
    identifiers: list[str] = []
    for row in rows[2:]:
        cells = row.removeprefix("|").removesuffix("|").split("|")
        assert len(cells) == 6, f"malformed B.16 contract row: {row}"
        match = re.fullmatch(r"`(U-[A-Z0-9-]+)`", cells[0].strip())
        assert match is not None, f"malformed B.16 contract ID cell: {cells[0]}"
        identifiers.append(match.group(1))
    return identifiers


def _assert_contract_ids(text: str) -> None:
    identifiers = _contract_ids(text)
    assert len(identifiers) == len(set(identifiers))
    assert tuple(identifiers) == EXPECTED_CONTRACT_IDS


def _assert_unshipped_mathematical_target_rows(text: str) -> None:
    table = text.split("### B.16 Formalisation target table", 1)[1].split(
        "#### B.16.1 Theorem dependency DAG", 1
    )[0]
    rows = {
        row.split("|", 2)[1].strip().strip("`"): row
        for row in table.splitlines()
        if row.startswith("| `U-")
    }
    for contract_id, (target, consumer) in EXPECTED_MATHEMATICAL_TARGET_ROWS.items():
        row = rows[contract_id]
        cells = row.removeprefix("|").removesuffix("|").split("|")
        assert len(cells) == 6
        assert cells[2].strip() == f"`{target}`"
        assert cells[5].strip() == consumer
        assert cells[5].strip().startswith("unshipped target:")


def _assert_adversarial_review_boundary(text: str) -> None:
    adversarial_heading = "#### B.16.3 Named adversarial attacks and attacked premises"
    section = text.split(adversarial_heading, 1)[1].split(
        "#### B.16.4 Lean-ready signatures and coercion boundaries", 1
    )[0]
    normalized = " ".join(section.split())
    required = (
        "non-dyadic exact-equality tangency and even-multiplicity root",
        "persistent equality ridge and singleton algebraic acceptance",
        "inclusive ordering tie",
        "generic adversarial classes, not promoted fixture authority.",
        "remain in the ignored local review packet",
        "U0 neither publishes them nor treats them as U1/U2 fixture inputs.",
    )
    assert all(" ".join(fragment.split()) in normalized for fragment in required)


def _assert_review_correspondence(text: str) -> None:
    section = text.split("#### B.16.5 Theorem-to-runtime correspondence", 1)[1].split(
        "#### B.16.6 Claim ceiling and approval state", 1
    )[0]
    records: dict[str, tuple[str, ...]] = {}
    for row in section.splitlines():
        if not row.startswith("| `U-"):
            continue
        cells = tuple(
            " ".join(cell.split())
            for cell in row.removeprefix("|").removesuffix("|").split("|")
        )
        assert len(cells) == 4
        identifier = cells[0].strip("`")
        assert identifier not in records, "duplicate review correspondence"
        records[identifier] = cells[1:]
    assert records == EXPECTED_REVIEW_CORRESPONDENCE
    assert records.keys() == EXPECTED_MATHEMATICAL_TARGET_ROWS.keys()
    for target, _ in EXPECTED_MATHEMATICAL_TARGET_ROWS.values():
        declaration = target.removeprefix("ExactCIs.Unconditional.")
        assert f"#check @{declaration} :" in text


def _assert_review_dependency_edges(text: str) -> None:
    section = text.split("#### B.16.1 Theorem dependency DAG", 1)[1].split(
        "#### B.16.2 Hard-proof route and required infrastructure", 1
    )[0]
    normalized = " ".join(section.split())
    required = (
        "U-BOSCH-ORDER-001 + U-OR-MASS-001 -> U-BOSCH-FISHER-ENVELOPE-001",
        "|-> U-BOSCH-MASK-STRATUM-001",
        "U-ROOT-CERT-001 + U-BOSCH-ORDER-001 + U-THRESH-001 + U-ATTAIN-001 "
        "-> U-BOSCH-INTERIOR-ROOT-001",
        "U-BOSCH-MASK-STRATUM-001 + U-BOSCH-INTERIOR-ROOT-001 "
        "+ U-ROOT-CERT-001 -> U-PARAMETRIC-ROOT-001",
        "U-BOSCH-MASK-STRATUM-001 + U-ROOT-CERT-001 -> U-ALGEBRAIC-POINT-001",
        "U-PARAMETRIC-ROOT-001 + U-ALGEBRAIC-POINT-001 "
        "-> exact cell certificates for U-EFFECT-QUANT-001;",
        "absent exceptional-point evidence -> BOUNDARY_ENCLOSURE or refusal",
        "U-BOSCH-FISHER-ENVELOPE-001 "
        "-> certified finite exclusions and T1-min endpoint separation only",
        "U-STRUCT-OR-MASK-001 + U-OR-MASS-001 -> U-STRUCT-OR-LIMIT-001",
    )
    assert all(fragment in normalized for fragment in required)


def test_u0_authority_blocks_are_exact() -> None:
    text = _text()
    manifest = _json_block(text, "release-manifest")
    terminal = _json_block(text, "terminal-contract")
    assurance = _json_block(text, "assurance-contract")
    breakpoint = _json_block(text, "breakpoint-contract")
    structural_endpoint = _json_block(text, "structural-or-endpoint-contract")
    review_provenance = _json_block(text, "mathematical-review-provenance")
    assert manifest == EXPECTED_MANIFEST
    assert terminal == EXPECTED_TERMINAL
    assert assurance == EXPECTED_ASSURANCE
    assert breakpoint == EXPECTED_BREAKPOINT
    assert structural_endpoint == EXPECTED_STRUCTURAL_OR_ENDPOINT
    assert review_provenance == EXPECTED_MATHEMATICAL_REVIEW_PROVENANCE
    _assert_manifest_authority(manifest)
    _assert_terminal_authority(terminal)
    _assert_assurance_authority(assurance)
    _assert_breakpoint_authority(breakpoint)
    _assert_structural_or_endpoint_authority(structural_endpoint)
    _assert_mathematical_review_provenance(review_provenance)
    _assert_binding_text(text)
    _assert_structural_repair_authority(text)
    _assert_fisher_envelope_authority(text)
    _assert_fixed_null_reduction_authority(text)
    _assert_global_root_strata_authority(text)
    _assert_unshipped_mathematical_target_rows(text)
    _assert_adversarial_review_boundary(text)
    _assert_review_correspondence(text)
    _assert_review_dependency_edges(text)


def test_mathematical_review_provenance_mutations_fail() -> None:
    mutations = (
        lambda payload: payload.update(
            {"status": "formal_proof_and_release_candidate"}
        ),
        lambda payload: payload.update({"scope": "all_unconditional_methods"}),
        lambda payload: payload.update({"packet_sha256": "0" * 64}),
        lambda payload: payload.update({"review_file_sha256": "0" * 64}),
        lambda payload: payload.update(
            {"claim_ceiling": "release approval and production conformance"}
        ),
    )
    for mutate in mutations:
        payload = copy.deepcopy(EXPECTED_MATHEMATICAL_REVIEW_PROVENANCE)
        mutate(payload)
        with pytest.raises(AssertionError):
            _assert_mathematical_review_provenance(payload)


@pytest.mark.parametrize(
    ("old", "new"),
    (
        ("F_d(a,c;psi)<1", "F_d(a,c;psi)<=1"),
        ("H_d,psi(1) = -r*psi^n1 < 0.", "H_d,psi(1) = r*psi^n1 > 0."),
        ("H_d,psi(q) = 0.", "H_d,psi(q) > 0."),
        (
            "Squarefree\nreduction need not preserve the sign of `H`;",
            "Squarefree reduction preserves the sign of `H`;",
        ),
        (
            "the original `H` retains the\n"
            "endpoint signs and accepted-equality semantics.",
            "the reduced polynomial replaces the original endpoint signs.",
        ),
        (
            "If the observed tail is\n"
            "one, its mask is the full sample space and the directional "
            "p-value is exactly\n"
            "one; it is deliberately outside this endpoint-negative specialisation.",
            "The full-mask case uses the endpoint-negative interior-root "
            "specialisation.",
        ),
        (
            "A repeated\nor even-multiplicity interior root still accepts.",
            "A repeated interior root rejects.",
        ),
        (
            "Neither numerical\n"
            "maximisation, an argmax enclosure, stationary-point "
            "enumeration, nor a rational\n"
            "grid is a required decision path.",
            "A numerical maximisation is a required decision path.",
        ),
    ),
)
def test_fixed_null_reduction_mutations_fail(old: str, new: str) -> None:
    text = _text()
    assert old in text
    with pytest.raises(AssertionError):
        _assert_fixed_null_reduction_authority(text.replace(old, new, 1))


@pytest.mark.parametrize(
    ("old", "new"),
    (
        (
            "P[psi,q](R_dir(psi)) <= F_dir(a,c;psi),",
            "P[psi,q](R_dir(psi)) >= F_dir(a,c;psi),",
        ),
        (
            "e0 = a-ell = min(a,d),",
            "e0 = a-ell = min(b,c),",
        ),
        (
            "finiteP(observed,greater,psi) <= C0_fisher * psi^e0",
            "finiteP(observed,less,psi) <= C0_fisher * psi^e0",
        ),
        (
            "finiteP(observed,less,psi) <= Cinf_fisher / psi^einf",
            "finiteP(observed,less,psi) >= Cinf_fisher / psi^einf",
        ),
        (
            "finiteP(observed,greater,psi) <= C0_fisher * psi^e0",
            "finiteP(observed,greater,psi) <= C0_fisher * psi^einf",
        ),
        (
            "finiteP(observed,greater,psi) <= C0_fisher * psi^e0",
            "finiteP(observed,greater,psi) <= Cinf_fisher * psi^e0",
        ),
        (
            "einf = h-a = min(b,c),",
            "einf = h-a = min(a,d),",
        ),
        (
            "finiteP(observed,greater,psi) <= C0_fisher * psi^e0       for 0<psi<=1.",
            "finiteP(observed,greater,psi) <= C0_fisher * psi^e0       for psi>=1.",
        ),
        (
            "finiteP(observed,less,psi) <= Cinf_fisher / psi^einf      for psi>=1.",
            "finiteP(observed,less,psi) <= Cinf_fisher / psi^einf      for 0<psi<=1.",
        ),
        (
            "delta_fisher = min(1/2, r/(2*C0_fisher)),",
            "delta_fisher = max(1/2, r/(2*C0_fisher)),",
        ),
        (
            "M_fisher = max(2, 2*Cinf_fisher/r)",
            "M_fisher = min(2, 2*Cinf_fisher/r)",
        ),
        (
            "Fisher domination is an\nexclusion theorem only:",
            "Fisher domination authorizes a Fisher return:",
        ),
        (
            "does **not** replace the actual-finite-mask route",
            "replaces the actual-finite-mask route",
        ),
    ),
)
def test_fisher_envelope_mutations_fail(old: str, new: str) -> None:
    text = _text()
    assert old in text
    with pytest.raises(AssertionError):
        _assert_fisher_envelope_authority(text.replace(old, new, 1))


@pytest.mark.parametrize(
    ("old", "new"),
    (
        (
            "`z in R_d(psi)` exactly when `G_z(psi)<=0`.",
            "`z in R_d(psi)` exactly when `G_z(psi)<0`.",
        ),
        (
            "take a squarefree\nrepresentative over `Q(psi)`",
            "take an unreduced representative over `Q(psi)`",
        ),
        (
            "excluded from partition guards, and omitted when counting "
            "sign variations.",
            "included in partition guards and assigned a positive sign.",
        ),
        (
            "Its denominator and squarefree-specialisation guards remain in force.",
            "Its denominator and specialisation guards are discarded.",
        ),
        (
            "roots only of nonzero guard polynomials;",
            "roots of every guard polynomial including zero;",
        ),
        (
            "an isolated zero of a nonzero entry\nstill owns an exceptional effect",
            "an isolated zero of a nonzero entry is discarded as an identity",
        ),
        (
            "not assert one nuisance witness for the\nentire stratum.",
            "assert one nuisance witness for the entire stratum.",
        ),
        (
            "recomputes the actual\n"
            "inclusive mask, then specialises the root certificate",
            "uses a neighbouring mask and skips specialisation",
        ),
        (
            "retains a `BOUNDARY_ENCLOSURE` or refuses",
            "classifies every exceptional point from neighbouring strata",
        ),
    ),
)
def test_global_root_strata_mutations_fail(old: str, new: str) -> None:
    text = _text()
    assert old in text
    with pytest.raises(AssertionError):
        _assert_global_root_strata_authority(text.replace(old, new, 1))


@pytest.mark.parametrize("psi", (Fraction(1, 4), Fraction(1, 2), Fraction(3, 4)))
def test_generic_squarefree_sturm_zero_entry_contract(psi: Fraction) -> None:
    """Generic exact certificate check; no Boschloo or U1/U2 fixture authority."""

    def chain(q: Fraction) -> tuple[Fraction, Fraction, Fraction]:
        return q * q - psi, 2 * q, psi

    def variations(values: tuple[Fraction, ...]) -> int:
        nonzero = [value for value in values if value != 0]
        return sum(left * right < 0 for left, right in zip(nonzero, nonzero[1:]))

    for q in (Fraction(0), Fraction(1, 3), Fraction(2, 3), Fraction(1)):
        squarefree, derivative, remainder = chain(q)
        # S = (q/2) S' - psi is the checked negative-remainder identity.
        assert squarefree == q * derivative / 2 - remainder
        original = -((q * q - psi) ** 2)
        assert original == -squarefree * squarefree
        assert (original == 0) == (squarefree == 0)

    assert chain(Fraction(0)) == (-psi, Fraction(0), psi)
    assert chain(Fraction(1)) == (1 - psi, Fraction(2), psi)
    assert variations(chain(Fraction(0))) == 1
    assert variations(chain(Fraction(1))) == 0
    assert -(psi**2) < 0 and -((1 - psi) ** 2) < 0
    # The reduced polynomial is positive at one while the original is negative.
    assert chain(Fraction(1))[0] > 0


@pytest.mark.parametrize("identifier", tuple(EXPECTED_REVIEW_CORRESPONDENCE))
@pytest.mark.parametrize("column", (1, 2, 3))
def test_review_correspondence_field_mutations_fail(
    identifier: str, column: int
) -> None:
    text = _text()
    row = (
        "| `"
        + identifier
        + "` | "
        + " | ".join(EXPECTED_REVIEW_CORRESPONDENCE[identifier])
        + " |"
    )
    assert text.count(row) == 1
    cells = row.split("|")
    cells[column + 1] = " unchecked replacement "
    with pytest.raises(AssertionError):
        _assert_review_correspondence(text.replace(row, "|".join(cells), 1))


def test_review_correspondence_duplicate_fails() -> None:
    text = _text()
    identifier = "U-ALGEBRAIC-POINT-001"
    row = (
        "| `"
        + identifier
        + "` | "
        + " | ".join(EXPECTED_REVIEW_CORRESPONDENCE[identifier])
        + " |"
    )
    assert text.count(row) == 1
    with pytest.raises(AssertionError, match="duplicate review correspondence"):
        _assert_review_correspondence(text.replace(row, row + "\n" + row, 1))


@pytest.mark.parametrize(
    ("old", "new"),
    (
        (
            "U-THRESH-001 + U-ATTAIN-001\n    -> U-BOSCH-INTERIOR-ROOT-001",
            "U-THRESH-001 alone\n    -> U-BOSCH-INTERIOR-ROOT-001",
        ),
        (
            "U-BOSCH-MASK-STRATUM-001 + U-BOSCH-INTERIOR-ROOT-001\n"
            "    + U-ROOT-CERT-001 -> U-PARAMETRIC-ROOT-001",
            "U-BOSCH-MASK-STRATUM-001 alone -> U-PARAMETRIC-ROOT-001",
        ),
        (
            "U-BOSCH-MASK-STRATUM-001 + U-ROOT-CERT-001\n    -> U-ALGEBRAIC-POINT-001",
            "U-BOSCH-MASK-STRATUM-001 alone -> U-ALGEBRAIC-POINT-001",
        ),
        (
            "absent exceptional-point evidence -> BOUNDARY_ENCLOSURE or refusal",
            "absent exceptional-point evidence -> classify from adjacent cells",
        ),
        (
            "U-STRUCT-OR-MASK-001 + U-OR-MASS-001\n    -> U-STRUCT-OR-LIMIT-001",
            "U-BOSCH-FISHER-ENVELOPE-001 -> U-STRUCT-OR-LIMIT-001",
        ),
    ),
)
def test_review_dependency_mutations_fail(old: str, new: str) -> None:
    text = _text()
    assert old in text
    with pytest.raises(AssertionError):
        _assert_review_dependency_edges(text.replace(old, new, 1))


@pytest.mark.parametrize(
    ("old", "new"),
    (
        (
            "ExactCIs.Unconditional.GlobalInversion.parametricRootStratum",
            "ExactCIs.Unconditional.GlobalInversion.sampledRootStratum",
        ),
        (
            "unshipped target: exceptional-effect verifier and fail-closed scheduler",
            "shipped runtime: exceptional-effect verifier",
        ),
    ),
)
def test_unshipped_mathematical_target_row_mutations_fail(old: str, new: str) -> None:
    text = _text()
    assert old in text
    with pytest.raises(AssertionError):
        _assert_unshipped_mathematical_target_rows(text.replace(old, new, 1))


def test_adversarial_review_boundary_mutation_fails() -> None:
    text = _text()
    old = "U0 neither publishes them nor treats\nthem as U1/U2 fixture inputs."
    mutated = text.replace(old, "U0 promotes them as U1/U2 fixture inputs.", 1)
    assert mutated != text
    with pytest.raises(AssertionError):
        _assert_adversarial_review_boundary(mutated)


def test_contract_ids_are_stable_unique_and_boschloo_only() -> None:
    identifiers = _contract_ids(_text())
    _assert_contract_ids(_text())
    assert {"U-RR-THIN-001", "U-STRUCT-RR-001"}.isdisjoint(identifiers)
    assert {"U-SCORE-OR-001", "U-SCORE-RR-001"}.isdisjoint(identifiers)


def test_owner_packet_sections_and_claim_ceiling_are_present() -> None:
    text = _text()
    headings = (
        "#### B.16.1 Theorem dependency DAG",
        "#### B.16.2 Hard-proof route and required infrastructure",
        "#### B.16.3 Named adversarial attacks and attacked premises",
        "#### B.16.4 Lean-ready signatures and coercion boundaries",
        "#### B.16.5 Theorem-to-runtime correspondence",
        "#### B.16.6 Claim ceiling and approval state",
    )
    assert all(text.count(heading) == 1 for heading in headings)
    assert "**Implementation status: blocked.**" in text
    assert "does not prove the target theorems" in " ".join(text.split())


def test_manifest_scope_widening_mutations_fail() -> None:
    manifest = copy.deepcopy(EXPECTED_MANIFEST)
    manifest["methods"].append(
        {
            "construction_id": "barnard_or",
            "entrypoint": "exact_ci_barnard",
        }
    )
    with pytest.raises(AssertionError):
        _assert_manifest_authority(manifest)

    manifest = copy.deepcopy(EXPECTED_MANIFEST)
    manifest["widenable_for_target_release"] = True
    with pytest.raises(AssertionError):
        _assert_manifest_authority(manifest)


@pytest.mark.parametrize(
    ("table", "endpoint", "expected"),
    (
        ((0, 1, 1, 0), "zero", (Fraction(1), Fraction(1))),
        ((1, 0, 0, 1), "zero", (Fraction(0), Fraction(1))),
        ((1, 0, 0, 1), "positive_infinity", (Fraction(1), Fraction(1))),
        ((0, 1, 1, 0), "positive_infinity", (Fraction(1), Fraction(0))),
        ((1, 1, 1, 1), "zero", (Fraction(0), Fraction(1))),
        ((1, 1, 1, 1), "positive_infinity", (Fraction(1), Fraction(0))),
        ((0, 1, 0, 1), "zero", (Fraction(1), Fraction(1))),
        ((0, 1, 0, 1), "positive_infinity", (Fraction(1), Fraction(1))),
        ((1, 0, 1, 0), "zero", (Fraction(1), Fraction(1))),
        ((1, 0, 1, 0), "positive_infinity", (Fraction(1), Fraction(1))),
    ),
)
def test_structural_or_endpoint_support_pairs_are_exact(
    table: tuple[int, int, int, int],
    endpoint: str,
    expected: tuple[Fraction, Fraction],
) -> None:
    assert _structural_or_endpoint_pair(*table, endpoint) == expected


def test_structural_or_endpoint_alpha_zero_is_inclusive() -> None:
    zero_unsupported = (Fraction(0), Fraction(1))
    infinity_unsupported = (Fraction(1), Fraction(0))
    positive_alpha = Fraction(1, 13)

    assert _structural_endpoint_accepts(zero_unsupported, Fraction(0))
    assert _structural_endpoint_accepts(infinity_unsupported, Fraction(0))
    assert not _structural_endpoint_accepts(zero_unsupported, positive_alpha)
    assert not _structural_endpoint_accepts(infinity_unsupported, positive_alpha)
    assert zero_unsupported[0] < positive_alpha
    assert infinity_unsupported[1] < positive_alpha


@pytest.mark.parametrize(
    ("endpoint", "p1", "p0"),
    (
        ("zero", Fraction(0), Fraction(0)),
        ("zero", Fraction(0), Fraction(1, 2)),
        ("zero", Fraction(0), Fraction(1)),
        ("zero", Fraction(1, 2), Fraction(1)),
        ("zero", Fraction(1), Fraction(1)),
        ("positive_infinity", Fraction(0), Fraction(0)),
        ("positive_infinity", Fraction(1, 2), Fraction(0)),
        ("positive_infinity", Fraction(1), Fraction(0)),
        ("positive_infinity", Fraction(1), Fraction(1, 2)),
        ("positive_infinity", Fraction(1), Fraction(1)),
    ),
)
@pytest.mark.parametrize(("n1", "n0"), ((1, 1), (2, 3), (4, 2)))
def test_structural_or_fibre_support_and_two_sided_validity_are_exact(
    endpoint: str,
    p1: Fraction,
    p0: Fraction,
    n1: int,
    n0: int,
) -> None:
    """Finite exact evidence for the U-STRUCT-OR-VALID-001 theorem shape."""
    support_mass = _product_binomial_event_mass(
        n1,
        n0,
        p1=p1,
        p0=p0,
        event=lambda a, b, c, d: _structural_or_supports(a, b, c, d, endpoint),
    )
    assert support_mass == 1

    for alpha_side in (Fraction(0), Fraction(1, 7), Fraction(1)):
        rejection_mass = _product_binomial_event_mass(
            n1,
            n0,
            p1=p1,
            p0=p0,
            event=lambda a, b, c, d: (
                not _structural_endpoint_accepts(
                    _structural_or_endpoint_pair(a, b, c, d, endpoint), alpha_side
                )
            ),
        )
        assert rejection_mass == 0


@pytest.mark.parametrize(
    ("endpoint", "p1", "p0"),
    (
        ("zero", Fraction(0), Fraction(1, 2)),
        ("zero", Fraction(1, 2), Fraction(1)),
        ("positive_infinity", Fraction(1, 2), Fraction(0)),
        ("positive_infinity", Fraction(1), Fraction(1, 2)),
    ),
)
def test_structural_or_fibre_support_is_disjunctive_not_conjunctive(
    endpoint: str,
    p1: Fraction,
    p0: Fraction,
) -> None:
    def conjunctive_support(a: int, b: int, c: int, d: int) -> bool:
        if endpoint == "zero":
            return a == 0 and d == 0
        return c == 0 and b == 0

    union_mass = _product_binomial_event_mass(
        1,
        1,
        p1=p1,
        p0=p0,
        event=lambda a, b, c, d: _structural_or_supports(a, b, c, d, endpoint),
    )
    conjunction_mass = _product_binomial_event_mass(
        1,
        1,
        p1=p1,
        p0=p0,
        event=conjunctive_support,
    )
    assert union_mass == 1
    assert conjunction_mass == Fraction(1, 2)


def test_structural_or_endpoint_group_swap_reverses_endpoint_pairs() -> None:
    for a in range(3):
        for b in range(3):
            for c in range(3):
                for d in range(3):
                    if a + b == 0 or c + d == 0:
                        continue
                    table = (a, b, c, d)
                    swapped = (c, d, a, b)
                    assert _structural_or_endpoint_pair(*table, "zero") == tuple(
                        reversed(
                            _structural_or_endpoint_pair(*swapped, "positive_infinity")
                        )
                    )
                    assert _structural_or_endpoint_pair(
                        *table, "positive_infinity"
                    ) == tuple(reversed(_structural_or_endpoint_pair(*swapped, "zero")))


@pytest.mark.parametrize("t", (Fraction(1, 2), Fraction(2, 3), Fraction(5, 7)))
def test_n1_n0_one_rational_square_structural_anchor_and_swap(
    t: Fraction,
) -> None:
    """Exact U1/U2 counterexample anchor; it is not a runtime implementation."""
    psi = t * t
    q_star = Fraction(1, 1) / (Fraction(1, 1) + t)
    p0 = q_star
    p1 = psi * q_star / (Fraction(1, 1) + (psi - 1) * q_star)
    p_greater = p1 * (Fraction(1, 1) - p0)
    p_less = Fraction(1, 1)

    assert p1 == t / (Fraction(1, 1) + t)
    assert p_greater == t * t / (Fraction(1, 1) + t) ** 2
    assert p_less == Fraction(1, 1)

    # (a, c) = (1, 0), n1 = n0 = 1; swap maps zero to infinity and reverses
    # the pair/direction. The values remain exact rational evidence only.
    original = (1, 0, 0, 1)
    swapped = (0, 1, 1, 0)
    assert _structural_or_endpoint_pair(*original, "zero") == (
        Fraction(0),
        Fraction(1),
    )
    assert _structural_or_endpoint_pair(*swapped, "positive_infinity") == (
        Fraction(1),
        Fraction(0),
    )
    assert (p_less, p_greater) == (
        Fraction(1),
        t * t / (Fraction(1, 1) + t) ** 2,
    )


def test_structural_or_endpoint_authority_mutations_fail() -> None:
    mutations = (
        lambda payload: payload["support"]["zero"].update({"unsupported_pair": [0, 0]}),
        lambda payload: payload.update({"tuple_order": ["p_less", "p_greater"]}),
        lambda payload: payload["support"]["zero"].update(
            {"predicate": "a == 0 and d == 0"}
        ),
        lambda payload: payload["classification"].update(
            {"zero_alpha": "unsupported endpoint pairs are rejected"}
        ),
        lambda payload: payload["scope"].update({"excludes": []}),
        lambda payload: payload["symmetry"].update({"directions": "greater -> less"}),
    )
    for mutate in mutations:
        payload = copy.deepcopy(EXPECTED_STRUCTURAL_OR_ENDPOINT)
        mutate(payload)
        with pytest.raises(AssertionError):
            _assert_structural_or_endpoint_authority(payload)


@pytest.mark.parametrize(
    ("old", "new"),
    (
        (
            "P[n1,n0,p1,p0](a = 0 or d = 0) = 1",
            "P[n1,n0,p1,p0](a = 0 and d = 0) = 1",
        ),
        (
            "BoschlooOrdering.finiteMask observed .greater psi",
            "BoschlooOrdering.structuralMask observed .zero .greater",
        ),
        (
            "BoschlooOrdering.finiteMaskMass observed .greater psi q",
            "UnrelatedDirectionalQuantity observed .greater psi q",
        ),
        (
            "∀ (psi : Real), 0 < psi → psi ≤ delta →\n        ∀ candidate",
            "∀ candidate\n        ∀ (psi : Real), 0 < psi → psi ≤ delta →",
        ),
        (
            "U-STRUCT-OR-VALID-001`) with the finite",
            "U-EXACT-P-001`) with the finite",
        ),
    ),
)
def test_structural_coverage_and_eventual_mask_mutations_fail(
    old: str, new: str
) -> None:
    text = _text()
    assert old in text
    with pytest.raises(AssertionError):
        _assert_structural_repair_authority(text.replace(old, new, 1))


def test_u0_claim_ceiling_is_evergreen_not_self_ratifying() -> None:
    text = _text()
    _assert_binding_text(text)
    stale = text.replace(
        "Status: **specified but unshipped.**",
        "Status: **review candidate; exact-head approval pending.**",
        1,
    )
    assert stale != text
    with pytest.raises(AssertionError):
        _assert_binding_text(stale)


def test_duplicate_json_authority_key_fails_closed() -> None:
    text = _text()
    duplicate = text.replace(
        '  "schema": "exactcis.unconditional.release_manifest.v2",',
        (
            '  "schema": "contradictory.schema",\n'
            '  "schema": "exactcis.unconditional.release_manifest.v2",'
        ),
        1,
    )
    with pytest.raises(ValueError, match="duplicate JSON authority key: schema"):
        _json_block(duplicate, "release-manifest")


def test_tangency_and_structural_corner_text_mutations_fail() -> None:
    text = _text()
    reversed_tie = text.replace(
        "p[m,greater,x](beta) >= alpha_side",
        "p[m,greater,x](beta) > alpha_side",
        1,
    )
    with pytest.raises(AssertionError):
        _assert_binding_text(reversed_tie)

    missing_corner = text.replace("`(s,q)=(1,0)`", "`(s,q)=(1,1)`", 1)
    with pytest.raises(AssertionError):
        _assert_binding_text(missing_corner)


@pytest.mark.parametrize(
    ("old", "new"),
    (
        ("min(x,n0-y) >= min(a,d)", "zero mask stratum omitted"),
        ("min(y,n1-x) >= min(c,b)", "infinity mask stratum omitted"),
        ("constants independent of nuisance", "constants may depend on nuisance"),
        ("This contract is OR/Boschloo-only.", "This contract also applies to RR."),
        (
            "In particular, `STRUCTURAL_REJECTED` is impossible\nat `alpha_side = 0`.",
            "STRUCTURAL_REJECTED is allowed at alpha zero",
        ),
    ),
)
def test_structural_endpoint_handoff_text_mutations_fail(old: str, new: str) -> None:
    text = _text()
    assert old in text
    with pytest.raises(AssertionError):
        _assert_binding_text(text.replace(old, new))


@pytest.mark.parametrize(
    ("old", "new"),
    (
        (
            "empty != I subseteq A_s",
            "I subseteq A_s",
        ),
        (
            "b_ext(lower_s(I)) - b_ext(lower_s(O)) <= epsilon_beta",
            "b_ext(lower_s(O)) - b_ext(lower_s(I)) <= epsilon_beta",
        ),
        (
            "b_ext(upper_s(O)) - b_ext(upper_s(I)) <= epsilon_beta",
            "b_ext(upper_s(I)) - b_ext(upper_s(O)) <= epsilon_beta",
        ),
        (
            "I and O derived from the same two-sided accepted-set contract",
            "I and O may derive from separate directional fragments",
        ),
        (
            "A_s = c[A[m,x]]",
            "A_s is an unrelated compact search set",
        ),
        (
            "for every beta in C there exists a nuisance q",
            "there exists one nuisance q for every beta in C",
        ),
        (
            "b_ext(lower_s(A)) - b_ext(lower_s(O)) <= epsilon",
            "b_ext(lower_s(O)) - b_ext(lower_s(A)) <= epsilon",
        ),
        (
            "b_ext(upper_s(O)) - b_ext(upper_s(A)) <= epsilon",
            "b_ext(upper_s(A)) - b_ext(upper_s(O)) <= epsilon",
        ),
        (
            "The terminal branches are distinct.",
            "Empty and full descend from the nonempty T1 hull branch",
        ),
        (
            "FIXED-NULL-BASE + FIXED-NULL-EVIDENCE -> fixed-null exact decisions",
            "FIXED-NULL-BASE alone -> fixed-null exact decisions",
        ),
        (
            "fixed-positive-total ideal coverage + U-XSEC-001",
            "fixed-positive-total ideal coverage + U-XSEC-RETURN-001",
        ),
        (
            "U-MOVING-USC-001 -> U-ACCEPTED-CLOSED-001",
            "U-MOVING-USC-001 does not control accepted-set closure",
        ),
        (
            "ideal branch of U-COVER-001 + (U-HULL-001 OR U-FULL-001)",
            "U-HULL-001 alone -> fixed-positive-total returned-event bound",
        ),
        (
            "fixed-positive-total return bounds from (`U-HULL-001` or `U-FULL-001`)",
            "fixed-positive-total return bounds from `U-HULL-001`",
        ),
        (
            "U-HULL-001 + U-ACCEPTED-CLOSED-001",
            "U-HULL-001 alone",
        ),
        (
            "#check @RootSignCertificate.existsComplete :",
            "#check @RootSignCertificate.checkerSoundAgain :",
        ),
        (
            "#check @Structural.hullTransport :",
            "#check @Structural.effectOrderIsoAgain :",
        ),
        (
            "#check @GlobalInversion.adaptiveCompletion :",
            "#check @GlobalInversion.optimisticCompletion :",
        ),
        (
            "#check @GlobalInversion.acceptedSetClosed :",
            "#check @GlobalInversion.acceptedSetSampled :",
        ),
        (
            'method="boschloo"',
            'method="wald"',
        ),
        (
            "Berger--Boos nuisance adjustment is excluded",
            "Berger--Boos nuisance adjustment is permitted",
        ),
        (
            "Certificates and verifier types remain internal evidence in 1.2.0",
            "Certificate classes are public in 1.2.0",
        ),
    ),
)
def test_binding_contract_mutations_fail(old: str, new: str) -> None:
    text = _text()
    assert old in text
    mutated = text.replace(old, new, 1)
    with pytest.raises(AssertionError):
        _assert_binding_text(mutated)


def test_breakpoint_sign_and_root_mutations_fail() -> None:
    breakpoint = copy.deepcopy(EXPECTED_BREAKPOINT)
    breakpoint["unreduced_numerator_factorization"] = "2*psi*(3*psi^3-23*psi-8)"
    breakpoint["ascending_coefficients"] = [0, -16, -46, 0, 6]
    with pytest.raises(AssertionError):
        _assert_breakpoint_authority(breakpoint)

    breakpoint = copy.deepcopy(EXPECTED_BREAKPOINT)
    breakpoint["unique_positive_root_decimal"] = "2.9247"
    with pytest.raises(AssertionError):
        _assert_breakpoint_authority(breakpoint)


def test_matching_as_hull_premise_mutation_fails() -> None:
    assurance = copy.deepcopy(EXPECTED_ASSURANCE)
    hull = assurance["HULL_CERTIFIED"]
    hull["does_not_require"].remove("component_matching")
    hull["requires"].append("component_matching")
    with pytest.raises(AssertionError):
        _assert_assurance_authority(assurance)


def test_certified_empty_failure_conflation_mutation_fails() -> None:
    terminal = copy.deepcopy(EXPECTED_TERMINAL)
    terminal["states"]["CERTIFIED_EMPTY"]["outcome"] = "raise NumericalError"
    with pytest.raises(AssertionError):
        _assert_terminal_authority(terminal)


def test_malformed_or_extra_contract_rows_fail_closed() -> None:
    marker = "#### B.16.1 Theorem dependency DAG"
    text = _text()
    malformed = text.replace(
        marker,
        "| U-EXTRA-999 | malformed | row | that | must | fail |\n\n" + marker,
        1,
    )
    with pytest.raises(AssertionError, match="malformed B.16 contract ID cell"):
        _contract_ids(malformed)

    extra = text.replace(
        marker,
        "| `U-EXTRA-999` | extra | row | that | must | fail |\n\n" + marker,
        1,
    )
    with pytest.raises(AssertionError):
        _assert_contract_ids(extra)

    indented = text.replace(
        marker,
        " | `U-EXTRA-999` | extra | row | that | must | fail |\n\n" + marker,
        1,
    )
    with pytest.raises(AssertionError, match="indented B.16 table row"):
        _contract_ids(indented)


def test_u0_does_not_ship_specified_or_deferred_surfaces() -> None:
    proposed_entrypoints = {
        "exact_ci_barnard",
        "exact_ci_boschloo",
        "exact_ci_score_rr",
    }
    proposed_keys = {"barnard", "boschloo", "exact_score_rr"}

    assert proposed_entrypoints.isdisjoint(exactcis.__all__)
    assert all(not hasattr(exactcis, name) for name in proposed_entrypoints)
    assert proposed_entrypoints.isdisjoint(odds_ratio.__all__)
    assert proposed_entrypoints.isdisjoint(relative_risk.__all__)
    assert all(not hasattr(odds_ratio, name) for name in proposed_entrypoints)
    assert all(not hasattr(relative_risk, name) for name in proposed_entrypoints)
    assert proposed_keys.isdisjoint({item.method_key for item in method_registry()})
    assert "EmptyConfidenceSetError" not in exactcis.__all__
    assert not hasattr(exactcis, "EmptyConfidenceSetError")
    assert not hasattr(exactcis_exceptions, "EmptyConfidenceSetError")
    proposed_modules = (
        "exactcis.inference.odds_ratio.barnard",
        "exactcis.inference.odds_ratio.boschloo",
        "exactcis.inference.relative_risk.exact_score",
        "exactcis.inference.relative_risk.score_unconditional",
    )
    assert all(importlib.util.find_spec(module) is None for module in proposed_modules)
