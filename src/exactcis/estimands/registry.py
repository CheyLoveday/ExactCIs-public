"""Canonical machine-readable registry for the public method boundary."""

from __future__ import annotations

from dataclasses import asdict, dataclass
from typing import Literal

from exactcis.estimands._enums import Design, Estimand
from exactcis.exceptions import DesignError, UnsupportedMethodError

MethodStatus = Literal[
    "stable",
    "experimental",
    "compatibility-only",
    "internal",
    "unsupported",
    "planned",
]


@dataclass(frozen=True, slots=True)
class MethodSpec:
    """One implementation and inferential contract in the public registry."""

    design: Design
    estimand: Estimand
    method_key: str
    construction: str
    status: MethodStatus
    point_estimator: str
    interval_type: str
    calibration: str
    limitations: str
    entrypoint: str

    def to_dict(self) -> dict[str, object]:
        """Return JSON-compatible method metadata."""
        return asdict(self)


def _spec(
    design: Design,
    estimand: Estimand,
    method_key: str,
    construction: str,
    point_estimator: str,
    interval_type: str,
    calibration: str,
    limitations: str,
    entrypoint: str,
) -> MethodSpec:
    return MethodSpec(
        design=design,
        estimand=estimand,
        method_key=method_key,
        construction=construction,
        status="stable",
        point_estimator=point_estimator,
        interval_type=interval_type,
        calibration=calibration,
        limitations=limitations,
        entrypoint=entrypoint,
    )


_FIXED_OR = (
    (
        "conditional",
        "Equal-tail inversion of the Fisher noncentral hypergeometric law",
        "conditional maximum-likelihood estimate",
        "conditional exact confidence interval",
        "Tail probabilities are computed under fixed margins; discreteness can make coverage conservative.",
        "Conditions on both margins and does not claim unconditional coverage.",
        "exactcis.exact_ci_conditional",
    ),
    (
        "midp",
        "Mid-P equal-tail inversion of the Fisher noncentral hypergeometric law",
        "conditional maximum-likelihood estimate",
        "conditional mid-P confidence interval",
        "Mid-P reduces discreteness but is not guaranteed to attain nominal coverage for every parameter value.",
        "Conditions on both margins; mid-P is not a fully exact coverage guarantee.",
        "exactcis.exact_ci_midp",
    ),
    (
        "minlike",
        "Fisher-Irwin minimum-likelihood ordering under the conditional law",
        "conditional maximum-likelihood estimate",
        "ordered conditional exact confidence set",
        "Inverts an inclusive probability-mass ordering at fixed margins.",
        "Discrete ordering can yield non-smooth endpoints and conservative coverage.",
        "exactcis.exact_ci_minlike",
    ),
    (
        "blaker",
        "Blaker acceptability ordering under the conditional law",
        "conditional maximum-likelihood estimate",
        "ordered conditional exact confidence set",
        "Inverts inclusive Blaker acceptability ordering at fixed margins.",
        "Discrete ordering can yield non-smooth endpoints and conservative coverage.",
        "exactcis.exact_ci_blaker",
    ),
)


_METHODS: tuple[MethodSpec, ...] = (
    tuple(
        _spec(Design.CASE_CONTROL_FIXED_MARGIN, Estimand.OR, *definition)
        for definition in _FIXED_OR
    )
    + tuple(
        _spec(
            design,
            Estimand.OR,
            method,
            construction,
            point,
            interval_type,
            calibration,
            limitations,
            entrypoint,
        )
        for design in (Design.COHORT_BINOMIAL, Design.CROSS_SECTIONAL)
        for method, construction, point, interval_type, calibration, limitations, entrypoint in (
            (
                "wald",
                "Log-Wald interval with a 0.5 correction only when any cell is zero",
                "sample odds ratio, corrected on zero-cell tables",
                "asymptotic confidence interval",
                "First-order normal approximation on the log-odds-ratio scale.",
                "Can be inaccurate for sparse data; the zero-cell correction changes the target estimator.",
                "exactcis.ci_wald",
            ),
            (
                "wald_haldane",
                "Log-Wald interval after adding 0.5 to every cell",
                "Haldane-Anscombe corrected odds ratio",
                "asymptotic confidence interval",
                "First-order normal approximation after a fixed continuity correction.",
                "The correction is applied even without zero cells and can matter in small samples.",
                "exactcis.ci_wald_haldane",
            ),
        )
    )
    + tuple(
        _spec(
            design,
            Estimand.RR,
            method,
            construction,
            point,
            interval_type,
            calibration,
            limitations,
            entrypoint,
        )
        for design in (Design.COHORT_BINOMIAL, Design.CROSS_SECTIONAL)
        for method, construction, point, interval_type, calibration, limitations, entrypoint in (
            (
                "score_rr",
                "Koopman-Nam inversion of the independent-binomial score statistic",
                "sample risk or prevalence ratio",
                "score confidence interval",
                "Score-test inversion for two independent binomial groups.",
                "Requires non-empty groups; discreteness is not modelled as an exact conditional law.",
                "exactcis.ci_score_rr",
            ),
            (
                "wald_rr",
                "Log-Wald interval for two independent binomial risks",
                "sample ratio with zero-triggered correction for finite-side calculation",
                "asymptotic confidence interval",
                "First-order normal approximation on the log-ratio scale.",
                "Can be inaccurate for sparse data; structural zero and infinity endpoints are retained.",
                "exactcis.ci_wald_rr",
            ),
        )
    )
    + tuple(
        _spec(
            design,
            Estimand.OR,
            "mantel_haenszel",
            "Mantel-Haenszel common odds ratio with Robins-Breslow-Greenland variance",
            "Mantel-Haenszel common odds ratio",
            "asymptotic stratified confidence interval",
            "Large-sample normal approximation for prespecified independent strata.",
            "Requires positive pooled cross-products and a defensible common-effect model.",
            "exactcis.compute_pooled_or",
        )
        for design in (Design.STRATIFIED_CASE_CONTROL, Design.STRATIFIED_COHORT)
    )
)

_INDEX = {(item.design, item.estimand, item.method_key): item for item in _METHODS}
if len(_INDEX) != len(_METHODS):
    raise RuntimeError("duplicate method contract in public registry")


def method_registry() -> tuple[MethodSpec, ...]:
    """Return the immutable canonical public method inventory."""
    return _METHODS


def methods_for(design: Design, estimand: Estimand) -> tuple[str, ...]:
    """Return stable method keys for one declared design and estimand."""
    _require_enums(design, estimand)
    return tuple(
        sorted(
            item.method_key
            for item in _METHODS
            if item.design is design
            and item.estimand is estimand
            and item.status == "stable"
        )
    )


def get_method_spec(design: Design, estimand: Estimand, method: str) -> MethodSpec:
    """Resolve one shipped method or fail explicitly without substitution."""
    _require_enums(design, estimand)
    if not isinstance(method, str) or not method:
        raise UnsupportedMethodError("method must be a non-empty public method key")
    try:
        return _INDEX[(design, estimand, method)]
    except KeyError as exc:
        available = methods_for(design, estimand)
        if not available:
            raise DesignError(
                f"{estimand.value} is not shipped for design {design.value!r}"
            ) from exc
        raise UnsupportedMethodError(
            f"method {method!r} is not shipped for {design.value}/{estimand.value}; "
            f"available methods: {', '.join(available)}"
        ) from exc


def _require_enums(design: Design, estimand: Estimand) -> None:
    if not isinstance(design, Design):
        raise DesignError("design must be an exactcis.Design value")
    if not isinstance(estimand, Estimand):
        raise DesignError("estimand must be an exactcis.Estimand value")


__all__ = [
    "MethodSpec",
    "MethodStatus",
    "get_method_spec",
    "method_registry",
    "methods_for",
]
