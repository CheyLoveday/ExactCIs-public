"""The method registry is the sole public scientific inventory."""

from __future__ import annotations

import pytest

from exactcis.estimands import (
    Design,
    Estimand,
    get_method_spec,
    method_registry,
    methods_for,
)
from exactcis.exceptions import DesignError, UnsupportedMethodError


def test_registry_is_unique_and_every_retained_method_is_classified() -> None:
    registry = method_registry()
    keys = {(item.design, item.estimand, item.method_key) for item in registry}
    assert len(registry) == len(keys) == 14
    assert {item.status for item in registry} == {"stable"}
    assert all(item.entrypoint.startswith("exactcis.") for item in registry)
    assert all(
        item.construction and item.calibration and item.limitations for item in registry
    )


def test_supported_lanes_are_explicit() -> None:
    assert methods_for(Design.CASE_CONTROL_FIXED_MARGIN, Estimand.OR) == (
        "blaker",
        "conditional",
        "midp",
        "minlike",
    )
    assert methods_for(Design.COHORT_BINOMIAL, Estimand.RR) == (
        "score_rr",
        "wald_rr",
    )
    assert methods_for(Design.STRATIFIED_CASE_CONTROL, Estimand.OR) == (
        "mantel_haenszel",
    )
    assert methods_for(Design.CASE_CONTROL_FIXED_MARGIN, Estimand.RR) == ()


def test_unknown_and_unidentified_routes_fail_explicitly() -> None:
    with pytest.raises(UnsupportedMethodError, match="available methods"):
        get_method_spec(Design.CASE_CONTROL_FIXED_MARGIN, Estimand.OR, "unconditional")
    with pytest.raises(DesignError, match="not shipped"):
        get_method_spec(Design.CASE_CONTROL_FIXED_MARGIN, Estimand.RR, "score_rr")
    with pytest.raises(DesignError, match="Design value"):
        methods_for("cohort_binomial", Estimand.RR)  # type: ignore[arg-type]


def test_registry_has_no_automatic_experimental_or_compatibility_method() -> None:
    assert not any(
        item.status in {"experimental", "compatibility-only"}
        for item in method_registry()
    )
