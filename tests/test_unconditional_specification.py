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
    "U-BOSCH-BREAKPOINT-001",
    "U-BOSCH-SWAP-001",
    "U-MASK-001",
    "U-THRESH-001",
    "U-BERN-CERT-001",
    "U-ROOT-CERT-001",
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


def test_u0_authority_blocks_are_exact() -> None:
    text = _text()
    manifest = _json_block(text, "release-manifest")
    terminal = _json_block(text, "terminal-contract")
    assurance = _json_block(text, "assurance-contract")
    breakpoint = _json_block(text, "breakpoint-contract")
    structural_endpoint = _json_block(text, "structural-or-endpoint-contract")
    assert manifest == EXPECTED_MANIFEST
    assert terminal == EXPECTED_TERMINAL
    assert assurance == EXPECTED_ASSURANCE
    assert breakpoint == EXPECTED_BREAKPOINT
    assert structural_endpoint == EXPECTED_STRUCTURAL_OR_ENDPOINT
    _assert_manifest_authority(manifest)
    _assert_terminal_authority(terminal)
    _assert_assurance_authority(assurance)
    _assert_breakpoint_authority(breakpoint)
    _assert_structural_or_endpoint_authority(structural_endpoint)
    _assert_binding_text(text)
    _assert_structural_repair_authority(text)


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
