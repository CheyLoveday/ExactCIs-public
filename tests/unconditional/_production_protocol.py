"""Lazy tests-only access to the existing public policy entry point.

An UnsupportedMethodError is the current scientific capability failure for the
requested construction. Imports and infrastructure failures are never xfailed.
The protocol adds no placeholder implementation and no production registry key.
"""


def boschloo_hull(table, alpha):
    from exactcis import Design, compute_or_with_policy

    return compute_or_with_policy(
        *table, design=Design.COHORT_BINOMIAL, method="boschloo", alpha=alpha
    )
