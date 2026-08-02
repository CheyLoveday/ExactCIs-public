"""Minimal design-aware ExactCIs example used by CI."""

from exactcis import Design, compute_or_with_policy

result = compute_or_with_policy(
    10,
    2,
    5,
    20,
    design=Design.CASE_CONTROL_FIXED_MARGIN,
)

assert result.lower <= result.point <= result.upper
