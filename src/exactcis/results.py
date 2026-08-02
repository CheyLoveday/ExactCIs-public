"""Typed result objects returned by the design-aware policy API."""

from __future__ import annotations

from dataclasses import dataclass

from exactcis.estimands import Design, Estimand


@dataclass(frozen=True, slots=True)
class InferenceResult:
    """One point estimate and two-sided confidence interval."""

    point: float
    lower: float
    upper: float
    confidence_level: float
    design: Design
    estimand: Estimand
    method: str
    construction: str
    status: str = "stable"


@dataclass(frozen=True, slots=True)
class PooledORResult:
    """Mantel-Haenszel common-odds-ratio result for independent strata."""

    point: float
    lower: float
    upper: float
    confidence_level: float
    design: Design
    method: str
    construction: str
    strata: int
    status: str = "stable"


__all__ = ["InferenceResult", "PooledORResult"]
