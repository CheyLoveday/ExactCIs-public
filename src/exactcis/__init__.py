"""Small, explicit public API for design-aware 2x2-table inference."""

from exactcis.__about__ import __version__
from exactcis.estimands import Design, Estimand
from exactcis.estimation import (
    compute_or_with_policy,
    compute_pooled_or,
    compute_rr_with_policy,
)
from exactcis.exceptions import (
    DesignError,
    ExactCIsError,
    NonIdentifiableError,
    NumericalError,
    UnsupportedMethodError,
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

__all__ = [
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
]

# Importing selected symbols necessarily loads explicit submodules. Remove the
# automatically attached module attributes so a plain ``import exactcis`` has
# only the frozen names above. Explicit ``import exactcis.estimands`` remains
# supported and restores that requested submodule attribute normally.
for _loaded_module in (
    "estimands",
    "estimation",
    "exceptions",
    "inference",
    "results",
):
    globals().pop(_loaded_module, None)
del _loaded_module
