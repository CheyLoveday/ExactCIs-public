"""Dependency-free numerical capability limits and support arithmetic.

This private module is the single source of truth for the numerical limits
shared by validation and the fixed-margin numerical kernels.  It deliberately
has no package imports so release tooling can consume it without importing a
numerical implementation.
"""

from __future__ import annotations

from typing import Final

_ROOT_TOL: Final = 2e-12
_UNDERFLOW_STOP: Final = -800.0
_BOUND_INFLATION: Final = 1e-9
_HULL_BOUND_BUDGET: Final = 50_000
_HULL_CERTIFY_DEPTH: Final = 64
_HULL_MAX_WIDTH: Final = 1_000_000
_PREPARE_MAX_WIDTH: Final = 10_000_000
_MAXIMUM_CELL_COUNT: Final = 10**12
_ALPHA_STABILITY_MARGIN: Final = 1e-12
_ALPHA_DOMAIN_MESSAGE: Final = (
    "alpha must satisfy 1e-12 < alpha < 1 - 1e-12 for numerical stability"
)


def support_width(n1: int, n0: int, events: int) -> int:
    """Return the fixed-margin support width without materialising support."""
    return min(n1, events) - max(0, events - n0) + 1
