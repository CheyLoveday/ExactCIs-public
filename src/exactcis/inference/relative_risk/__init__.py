"""Independent-binomial risk/prevalence-ratio intervals."""

from exactcis.inference.relative_risk.score import ci_score_rr
from exactcis.inference.relative_risk.wald import ci_wald_rr

__all__ = ["ci_score_rr", "ci_wald_rr"]
