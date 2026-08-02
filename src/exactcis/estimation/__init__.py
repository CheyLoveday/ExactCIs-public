"""Design-aware policy entry points for the public package."""

from __future__ import annotations

import math
from collections.abc import Iterable

from exactcis._numerics import conditional_mle, normal_quantile
from exactcis._validation import (
    Table,
    validate_alpha,
    validate_independent_groups,
    validate_strata,
)
from exactcis.estimands import Design, Estimand, get_method_spec
from exactcis.exceptions import (
    DesignError,
    NonIdentifiableError,
    NumericalError,
    ValidationError,
)
from exactcis.inference.odds_ratio import (
    ci_wald,
    ci_wald_haldane,
    exact_ci_blaker,
    exact_ci_conditional,
    exact_ci_midp,
    exact_ci_minlike,
)
from exactcis.inference.relative_risk import ci_score_rr, ci_wald_rr
from exactcis.results import InferenceResult, PooledORResult


def _confidence_level(alpha: float) -> float:
    return 1.0 - alpha


def _product_or_point(a: int, b: int, c: int, d: int, *, always_correct: bool) -> float:
    table = validate_independent_groups(a, b, c, d)
    if table[0] + table[2] == 0 or table[1] + table[3] == 0:
        raise NonIdentifiableError(
            "the odds ratio is not estimable when an outcome column is empty"
        )
    correction = 0.5 if always_correct or 0 in table else 0.0
    a_f, b_f, c_f, d_f = (value + correction for value in table)
    return (a_f * d_f) / (b_f * c_f)


def _ratio_point(a: int, b: int, c: int, d: int) -> float:
    a, b, c, d = validate_independent_groups(a, b, c, d)
    if a == 0 and c == 0:
        raise NonIdentifiableError(
            "the risk/prevalence ratio is not estimable when both observed "
            "risks are zero"
        )
    if c == 0:
        return math.inf
    return (a / (a + b)) / (c / (c + d))


def compute_or_with_policy(
    a: int,
    b: int,
    c: int,
    d: int,
    *,
    design: Design,
    method: str | None = None,
    alpha: float = 0.05,
) -> InferenceResult:
    """Compute one design-authorized odds-ratio estimate and interval.

    Fixed-margin case-control tables default to the central conditional
    interval and report the conditional MLE. Independent-binomial cohort and
    cross-sectional tables default to the zero-triggered log-Wald interval.
    Stratified data must use :func:`compute_pooled_or`. Unknown, unsupported,
    or numerically failed methods raise explicitly and are never replaced.
    """
    alpha = validate_alpha(alpha)
    if design is Design.CASE_CONTROL_FIXED_MARGIN:
        selected = method or "conditional"
        spec = get_method_spec(design, Estimand.OR, selected)
        intervals = {
            "conditional": exact_ci_conditional,
            "midp": exact_ci_midp,
            "minlike": exact_ci_minlike,
            "blaker": exact_ci_blaker,
        }
        lower, upper = intervals[selected](a, b, c, d, alpha, design=design)
        point = conditional_mle(a, b, c, d)
        if math.isnan(point):
            raise NonIdentifiableError(
                "conditioning leaves singleton support, so the odds-ratio "
                "confidence set is full but no unique point estimate exists"
            )
    elif design in {Design.COHORT_BINOMIAL, Design.CROSS_SECTIONAL}:
        selected = method or "wald"
        spec = get_method_spec(design, Estimand.OR, selected)
        if selected == "wald":
            lower, upper = ci_wald(a, b, c, d, alpha, design=design)
            point = _product_or_point(a, b, c, d, always_correct=False)
        elif selected == "wald_haldane":
            lower, upper = ci_wald_haldane(a, b, c, d, alpha, design=design)
            point = _product_or_point(a, b, c, d, always_correct=True)
        else:  # The registry and dispatch table must stay synchronized.
            raise RuntimeError(f"unwired stable OR method {selected!r}")
    elif design in {Design.STRATIFIED_CASE_CONTROL, Design.STRATIFIED_COHORT}:
        raise DesignError("stratified data require compute_pooled_or(strata=...)")
    else:
        raise DesignError("design must be an exactcis.Design value")

    if lower > upper or not lower <= point <= upper:
        raise NumericalError(
            "the selected odds-ratio result failed interval containment",
            method=selected,
        )
    return InferenceResult(
        point=point,
        lower=lower,
        upper=upper,
        confidence_level=_confidence_level(alpha),
        design=design,
        estimand=Estimand.OR,
        method=selected,
        construction=spec.construction,
    )


def compute_rr_with_policy(
    a: int,
    b: int,
    c: int,
    d: int,
    *,
    design: Design,
    method: str | None = None,
    alpha: float = 0.05,
) -> InferenceResult:
    """Compute one independent-binomial risk or prevalence-ratio result.

    ``Design.COHORT_BINOMIAL`` denotes a risk ratio;
    ``Design.CROSS_SECTIONAL`` denotes a prevalence ratio. Retrospective
    fixed-margin case-control sampling does not identify either quantity and
    is refused. The default method is Koopman-Nam score inversion.
    """
    alpha = validate_alpha(alpha)
    if design not in {Design.COHORT_BINOMIAL, Design.CROSS_SECTIONAL}:
        if not isinstance(design, Design):
            raise DesignError("design must be an exactcis.Design value")
        raise DesignError(
            f"{Estimand.RR.value} is not shipped for design {design.value!r}"
        )
    selected = method or "score_rr"
    spec = get_method_spec(design, Estimand.RR, selected)
    point = _ratio_point(a, b, c, d)
    if selected == "score_rr":
        lower, upper = ci_score_rr(a, b, c, d, alpha, design=design)
    elif selected == "wald_rr":
        lower, upper = ci_wald_rr(a, b, c, d, alpha, design=design)
    else:
        raise RuntimeError(f"unwired stable ratio method {selected!r}")
    if lower > upper or not lower <= point <= upper:
        raise NumericalError(
            "the selected risk/prevalence-ratio result failed interval containment",
            method=selected,
        )
    return InferenceResult(
        point=point,
        lower=lower,
        upper=upper,
        confidence_level=_confidence_level(alpha),
        design=design,
        estimand=Estimand.RR,
        method=selected,
        construction=spec.construction,
    )


def compute_pooled_or(
    strata: Iterable[Table],
    *,
    design: Design,
    alpha: float = 0.05,
) -> PooledORResult:
    """Return a Mantel-Haenszel common OR for prespecified strata.

    Strata must be independent and fixed before inspecting outcomes. The
    interval uses the Robins-Breslow-Greenland large-sample variance. This
    function does not reconstruct participant-level unions from marginal
    summaries and does not silently discard uninformative strata. Zero pooled
    cross-products or a non-positive variance fail explicitly.
    """
    if design not in {Design.STRATIFIED_CASE_CONTROL, Design.STRATIFIED_COHORT}:
        raise DesignError(
            "compute_pooled_or requires Design.STRATIFIED_CASE_CONTROL or "
            "Design.STRATIFIED_COHORT"
        )
    alpha = validate_alpha(alpha)
    spec = get_method_spec(design, Estimand.OR, "mantel_haenszel")
    tables = validate_strata(strata)
    ad_terms: list[float] = []
    bc_terms: list[float] = []
    apd_terms: list[float] = []
    bpc_terms: list[float] = []
    for index, (a, b, c, d) in enumerate(tables):
        total = a + b + c + d
        if total == 0:
            raise ValidationError(f"stratum {index} has no observations")
        ad_terms.append(a * d / total)
        bc_terms.append(b * c / total)
        apd_terms.append((a + d) / total)
        bpc_terms.append((b + c) / total)
    sum_ad = math.fsum(ad_terms)
    sum_bc = math.fsum(bc_terms)
    if sum_ad <= 0.0 or sum_bc <= 0.0:
        raise NonIdentifiableError(
            "the Mantel-Haenszel OR requires positive pooled ad/n and bc/n "
            "cross-products"
        )
    point = sum_ad / sum_bc
    variance = 0.5 * (
        math.fsum(p * ad for p, ad in zip(apd_terms, ad_terms)) / sum_ad**2
        + math.fsum(
            p * bc + q * ad
            for p, q, ad, bc in zip(apd_terms, bpc_terms, ad_terms, bc_terms)
        )
        / (sum_ad * sum_bc)
        + math.fsum(q * bc for q, bc in zip(bpc_terms, bc_terms)) / sum_bc**2
    )
    if not math.isfinite(variance) or variance <= 0.0:
        raise NumericalError(
            "the stratified log-OR variance is not positive and finite",
            method="mantel_haenszel",
        )
    critical = normal_quantile(1.0 - alpha / 2.0)
    half_width = critical * math.sqrt(variance)
    lower = math.exp(math.log(point) - half_width)
    upper = math.exp(math.log(point) + half_width)
    return PooledORResult(
        point=point,
        lower=lower,
        upper=upper,
        confidence_level=_confidence_level(alpha),
        design=design,
        method="mantel_haenszel",
        construction=spec.construction,
        strata=len(tables),
    )


__all__ = ["compute_or_with_policy", "compute_pooled_or", "compute_rr_with_policy"]
