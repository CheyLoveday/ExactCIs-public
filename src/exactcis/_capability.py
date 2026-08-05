"""Dependency-free numerical capability limits and support arithmetic.

This private module is the single source of truth for the numerical limits
shared by validation and the fixed-margin numerical kernels.  It deliberately
has no package imports so release tooling can consume it without importing a
numerical implementation.
"""

from __future__ import annotations

from typing import Final

# Keep cell counts inside a range where float/log-space arithmetic retains
# relative error comfortably below 1e-8 for the certified methods.
_MAXIMUM_CELL_COUNT: Final = 10**12
_ALPHA_STABILITY_MARGIN: Final = 1e-12
_MAXIMUM_CERTIFIED_ALPHA: Final = 1.0 - _ALPHA_STABILITY_MARGIN
_ALPHA_DOMAIN_MESSAGE: Final = (
    "alpha must satisfy 1e-12 < alpha < 1 - 1e-12 for numerical stability"
)

_ROOT_TOL: Final = 2e-12

# Active-support stop threshold for relative log masses. Strictly below the
# binary64 exponent floor: exp(x) == 0.0 for every x at or below this value on
# a conforming platform, verified once at import by _probe_underflow(). The
# stop rule never assumes monotonicity of exp: it stops on the VALUE of the
# accumulated relative log mass, whose outward non-increase is a rounding fact
# (adding a non-positive increment to a float cannot round above it), so every
# skipped term satisfies rel <= _UNDERFLOW_STOP and would itself evaluate to
# exactly 0.0.
_UNDERFLOW_STOP: Final = -800.0

# Explicit conservative roundoff inflation applied to every certified bound, per
# the hull specification (docs_md/ordered_hull_specification.md, E2). The margin
# dominates the measured kernel evaluation error (about 3e-14 at width 2e4) by
# more than four orders of magnitude, covers running-sum rounding for support
# widths up to about 1e6, and is validated against dense sampling in the test
# suite. Pure Python has no directed rounding, so explicit inflation is the
# reviewed zero-dependency enclosure mechanism.
_BOUND_INFLATION: Final = 1e-9
# Certified-bound evaluations allowed per endpoint before failing closed. Sized
# for graze bands: when p approaches alpha flatly from either side, certifying
# the band costs roughly (band width / certifiable cell width) evaluations, and
# the envelope's first-order slack makes the certifiable width proportional to
# |p - alpha|. Measured on the anchor case, table (23, 21, 23, 10) at
# alpha = 0.1 with a 1.3e-3-wide band sitting within 5e-7 of alpha, one
# endpoint spends 11764 evaluations, so the budget carries about 4x headroom.
# The cliff is structural: an alpha within about 1e-6 above the flat peak of a
# rejected island can exhaust any finite budget, and such calls fail closed
# with NumericalError rather than returning a loose interval. Worst-case
# runtime is budget * O(support width) element operations.
_HULL_BOUND_BUDGET: Final = 50_000
# Recursion depth cap for one rejection certificate.
_HULL_CERTIFY_DEPTH: Final = 64
_HULL_MAX_WIDTH: Final = 1_000_000

# Preparation materialises two sequences proportional to the support width, so
# the width must be rejected *before* allocation rather than by catching the
# allocator's failure. Catching MemoryError is not portable: Linux refuses an
# oversized request promptly, while macOS may accept it optimistically and let
# the kernel terminate the process, which is not fail-closed behaviour. This cap
# matches the >= 1e7 fail-closed band already documented in docs_md/methods.md.
_PREPARE_MAX_WIDTH: Final = 10_000_000


def support_width(n1: int, n0: int, events: int) -> int:
    """Return the fixed-margin support width without materialising support."""
    return min(n1, events) - max(0, events - n0) + 1
