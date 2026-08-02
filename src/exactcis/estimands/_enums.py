"""Study-design and effect-measure declarations."""

from enum import Enum


class Design(str, Enum):
    """Sampling-design contract for public inference operations."""

    CASE_CONTROL_FIXED_MARGIN = "case_control_fixed_margin"
    COHORT_BINOMIAL = "cohort_binomial"
    CROSS_SECTIONAL = "cross_sectional"
    STRATIFIED_CASE_CONTROL = "stratified_case_control"
    STRATIFIED_COHORT = "stratified_cohort"


class Estimand(str, Enum):
    """Effect measure requested from a 2x2 table."""

    OR = "odds_ratio"
    RR = "relative_risk"
