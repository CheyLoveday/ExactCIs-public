"""Dependency-free numerical primitives used by the public methods."""

from __future__ import annotations

import math
from collections.abc import Callable
from statistics import NormalDist

from exactcis.exceptions import NumericalError

_LOG_LIMIT = 740.0
_ROOT_TOL = 2e-12

# Active-support stop threshold for relative log masses. Strictly below the
# binary64 exponent floor: exp(x) == 0.0 for every x at or below this value on
# a conforming platform, verified once at import by _probe_underflow(). The
# stop rule never assumes monotonicity of exp: it stops on the VALUE of the
# accumulated relative log mass, whose outward non-increase is a rounding fact
# (adding a non-positive increment to a float cannot round above it), so every
# skipped term satisfies rel <= _UNDERFLOW_STOP and would itself evaluate to
# exactly 0.0.
_UNDERFLOW_STOP = -800.0


def _probe_underflow() -> bool:
    """Certify the platform behaviour the active-support stop relies on.

    Checks that exp evaluates to exactly 0.0 at the stop threshold and at a
    spread of values below it. If any probe fails, active support is disabled
    and the complete-support recurrence is used, per the programme obligation
    that an uncertifiable floating condition falls back rather than truncating
    heuristically.
    """
    probes = (-800.0, -800.5, -1000.0, -5000.0, -1e6, -1e12, -math.inf)
    return all(math.exp(value) == 0.0 for value in probes)


_ACTIVE_SUPPORT_OK = _probe_underflow()


def normal_quantile(probability: float) -> float:
    """Return the standard-normal quantile using the Python standard library."""
    if not 0.0 < probability < 1.0 or not math.isfinite(probability):
        raise ValueError("normal probability must be finite and in (0, 1)")
    return NormalDist().inv_cdf(probability)


def support_bounds(n1: int, n0: int, events: int) -> tuple[int, int]:
    """Return the support of the first-row event count at fixed margins."""
    return max(0, events - n0), min(events, n1)


def _log_choose(n: int, k: int) -> float:
    """Return log(C(n, k)) without catastrophic cancellation.

    Small supports use exact ``math.comb``; large supports use an iterative
    product in log space. The previous three-term ``lgamma`` form can lose
    precision for large, unbalanced arguments.
    """
    if k < 0 or k > n:
        return -math.inf
    if k == 0 or k == n:
        return 0.0
    k = min(k, n - k)
    if n <= 10_000:
        return math.log(math.comb(n, k))
    result = 0.0
    for i in range(k):
        result += math.log(n - i) - math.log(i + 1)
    return result


def _legacy_fnch_probabilities(
    n1: int,
    n0: int,
    events: int,
    log_odds: float,
) -> tuple[tuple[int, ...], tuple[float, ...]]:
    """Absolute-coefficient FNCH evaluation, retained as a differential oracle.

    This is the pre-:class:`PreparedMargins` implementation. It recomputes both
    log binomial coefficients at every support point on every call, which makes
    a single evaluation quadratic in support width. It is kept only so the
    replacement kernel can be checked against it and is not reachable from any
    public entry point.
    """
    lower, upper = support_bounds(n1, n0, events)
    support = tuple(range(lower, upper + 1))
    if not support:
        raise NumericalError("conditional support is empty", method="FNCH")
    if lower == upper:
        return support, (1.0,)
    if log_odds == -math.inf:
        return support, tuple(1.0 if value == lower else 0.0 for value in support)
    if log_odds == math.inf:
        return support, tuple(1.0 if value == upper else 0.0 for value in support)
    if not math.isfinite(log_odds):
        raise NumericalError(
            "log odds must be finite or an extended endpoint", method="FNCH"
        )

    log_masses = tuple(
        _log_choose(n1, value) + _log_choose(n0, events - value) + value * log_odds
        for value in support
    )
    anchor = max(log_masses)
    if not math.isfinite(anchor):
        raise NumericalError("conditional mass anchor is not finite", method="FNCH")
    scaled = tuple(math.exp(value - anchor) for value in log_masses)
    total = math.fsum(scaled)
    if not math.isfinite(total) or total <= 0.0:
        raise NumericalError("conditional mass normalization failed", method="FNCH")
    probabilities = tuple(value / total for value in scaled)
    probability_sum = math.fsum(probabilities)
    if (
        any(value < 0.0 or not math.isfinite(value) for value in probabilities)
        or abs(probability_sum - 1.0) > 2e-13
    ):
        raise NumericalError(
            "conditional probabilities failed certification",
            method="FNCH",
            diagnostics={"sum": probability_sum, "support_size": len(support)},
        )
    return support, probabilities


class PreparedMargins:
    """Parameter-independent FNCH structure for one set of fixed margins.

    The unnormalised weights satisfy an exact ratio identity

        w(k + 1) / w(k) = ((n1 - k) / (k + 1)) * ((m - k) / (n0 - m + k + 1)) * theta

    whose first factor does not depend on the parameter. Preparing those adjacent
    log-ratios once costs ``O(W)`` and makes every subsequent evaluation ``O(W)``
    as well, where the absolute-coefficient form cost ``O(W)`` *per support point*
    and so ``O(W**2)`` per evaluation.

    Evaluation is anchored at the mode of the current parameter, not at any
    table-level reference point. Because ``r[k] + eta`` is strictly decreasing in
    ``k`` the mode is a single sign change, locatable by binary search, and
    reconstructing outward from it keeps every relative log mass small in
    magnitude. A table-level anchor would instead add a large stored coefficient
    to a large, oppositely signed ``k * eta`` term, reintroducing the very
    cancellation that ``_log_choose`` was rewritten to avoid.

    Note that no binomial coefficient is evaluated at all: the normalised
    probabilities are fully determined by the adjacent ratios.

    Instances are immutable and cheap to hold for the duration of one inversion.
    Callers create them explicitly; nothing here caches across calls, because an
    unbounded process-global cache is outside the programme scope.
    """

    __slots__ = ("_n1", "_n0", "_events", "_lower", "_upper", "_support", "_ratios")

    def __init__(self, n1: int, n0: int, events: int) -> None:
        lower, upper = support_bounds(n1, n0, events)
        if upper < lower:
            raise NumericalError("conditional support is empty", method="FNCH")
        self._n1 = n1
        self._n0 = n0
        self._events = events
        self._lower = lower
        self._upper = upper
        # Preparation allocates two sequences proportional to the support width,
        # so it can exhaust memory on a table that passes count validation. That
        # must surface as NumericalError like every other numerical failure, not
        # as a bare MemoryError: preparation now happens before the solver's own
        # guarded region, so it carries its own guard.
        try:
            self._support = tuple(range(lower, upper + 1))
            # r[i] is the log ratio from support[i] to support[i + 1] at theta = 1.
            # Each factor is strictly positive across the valid support: for
            # lower <= k < upper we have k + 1 >= 1, n1 - k >= 1, events - k >= 1
            # and n0 - events + k + 1 >= 1, so no term is degenerate.
            self._ratios = tuple(
                math.log(n1 - k)
                - math.log(k + 1)
                + math.log(events - k)
                - math.log(n0 - events + k + 1)
                for k in range(lower, upper)
            )
        except (MemoryError, OverflowError, ValueError) as exc:
            raise NumericalError(
                "conditional support could not be prepared",
                method="FNCH",
                diagnostics={"support_size": upper - lower + 1},
            ) from exc

    @property
    def support(self) -> tuple[int, ...]:
        return self._support

    @property
    def width(self) -> int:
        return len(self._support)

    def index_of(self, value: int) -> int:
        """Return the index of an observed count within the support."""
        if not self._lower <= value <= self._upper:
            raise NumericalError("observed count is outside conditional support")
        return value - self._lower

    def mode_index(self, log_odds: float) -> int:
        """Return the index of the modal support point at this parameter.

        ``r[i] + log_odds`` is strictly decreasing, so the mode is the first
        index at which it stops being positive. Binary search costs O(log W).
        """
        ratios = self._ratios
        low, high = 0, len(ratios) - 1
        while low <= high:
            middle = (low + high) // 2
            if ratios[middle] + log_odds > 0.0:
                low = middle + 1
            else:
                high = middle - 1
        return low

    def _relative_log_masses(
        self, log_odds: float, low: int | None = None, high: int | None = None
    ) -> list[float]:
        """Return log masses relative to the modal point, which is pinned at zero.

        With ``low``/``high`` set, accumulation covers only ``[low, high)`` and
        entries outside are left at ``0.0``; callers restricting the range must
        only read inside it. Accumulated values are identical to the full walk
        because the walk outward from the mode is a prefix of the same float
        additions in both cases.
        """
        ratios = self._ratios
        width = len(self._support)
        masses = [0.0] * width
        mode = self.mode_index(log_odds)
        stop_high = width - 1 if high is None else min(width - 1, high - 1)
        stop_low = 0 if low is None else low

        running = 0.0
        for index in range(mode, stop_high):
            running += ratios[index] + log_odds
            masses[index + 1] = running
        running = 0.0
        for index in range(mode - 1, stop_low - 1, -1):
            running -= ratios[index] + log_odds
            masses[index] = running
        return masses

    def _active_range(self, log_odds: float) -> tuple[int, int]:
        """Return the half-open index range whose masses are representable.

        Walks outward from the mode accumulating relative log masses and stops
        a direction at the first index whose value reaches ``_UNDERFLOW_STOP``.
        Outward from the mode each increment is non-positive, and adding a
        non-positive increment to a float cannot round above it, so every index
        beyond a stop satisfies the same threshold and its mass is exactly
        ``0.0`` under the probed platform behaviour. The skipped terms
        therefore contribute exactly nothing to any sum the full recurrence
        would have computed.
        """
        ratios = self._ratios
        width = len(self._support)
        mode = self.mode_index(log_odds)

        high = width
        running = 0.0
        for index in range(mode, width - 1):
            running += ratios[index] + log_odds
            if running <= _UNDERFLOW_STOP:
                high = index + 1
                break
        low = 0
        running = 0.0
        for index in range(mode - 1, -1, -1):
            running -= ratios[index] + log_odds
            if running <= _UNDERFLOW_STOP:
                low = index + 1
                break
        return low, high

    def probabilities(
        self, log_odds: float
    ) -> tuple[tuple[int, ...], tuple[float, ...]]:
        """Return the certified FNCH probability vector at one log odds ratio.

        Uses exact-underflow active support when the platform probe passed:
        terms whose relative log mass is at or below ``_UNDERFLOW_STOP`` are
        exactly ``0.0`` and are skipped without changing any computed value.
        """
        return self._evaluate(log_odds, _ACTIVE_SUPPORT_OK)

    def _probabilities_full(
        self, log_odds: float
    ) -> tuple[tuple[int, ...], tuple[float, ...]]:
        """Complete-support evaluation, retained as the differential oracle.

        The active path must agree with this bit for bit: skipped terms would
        evaluate to exactly ``0.0``, and appending exact zeros changes neither
        ``math.fsum`` nor any normalised probability.
        """
        return self._evaluate(log_odds, False)

    def _evaluate(
        self, log_odds: float, active: bool
    ) -> tuple[tuple[int, ...], tuple[float, ...]]:
        support = self._support
        if self._lower == self._upper:
            return support, (1.0,)
        if log_odds == -math.inf:
            return support, tuple(1.0 if v == self._lower else 0.0 for v in support)
        if log_odds == math.inf:
            return support, tuple(1.0 if v == self._upper else 0.0 for v in support)
        if not math.isfinite(log_odds):
            raise NumericalError(
                "log odds must be finite or an extended endpoint", method="FNCH"
            )

        if active:
            low, high = self._active_range(log_odds)
        else:
            low, high = 0, len(support)
        masses = self._relative_log_masses(log_odds, low, high)
        # Mode anchoring makes the maximum exactly zero by construction.
        # Verifying it is cheap and catches a mode-location fault directly.
        if max(masses[low:high]) != 0.0:
            raise NumericalError(
                "conditional mass anchor is not the modal point", method="FNCH"
            )
        scaled = tuple(
            math.exp(masses[i]) if low <= i < high else 0.0 for i in range(len(masses))
        )
        total = math.fsum(scaled[low:high])
        if not math.isfinite(total) or total <= 0.0:
            raise NumericalError("conditional mass normalization failed", method="FNCH")
        probabilities = tuple(value / total for value in scaled)
        probability_sum = math.fsum(probabilities)
        if (
            any(value < 0.0 or not math.isfinite(value) for value in probabilities)
            or abs(probability_sum - 1.0) > 2e-13
        ):
            raise NumericalError(
                "conditional probabilities failed certification",
                method="FNCH",
                diagnostics={"sum": probability_sum, "support_size": len(support)},
            )
        return support, probabilities

    def mean(self, log_odds: float) -> float:
        """Return the conditional mean of the first-row count."""
        support, probabilities = self.probabilities(log_odds)
        return math.fsum(v * p for v, p in zip(support, probabilities))

    def moments(self, log_odds: float) -> tuple[float, float]:
        """Return conditional mean and variance from a single traversal.

        ``d/d eta E_eta[X] == Var_eta(X)`` for this exponential family, so the
        variance returned here is the derivative a safeguarded Newton step needs
        and costs no additional distribution evaluation.
        """
        support, probabilities = self.probabilities(log_odds)
        mean = math.fsum(v * p for v, p in zip(support, probabilities))
        variance = math.fsum(
            (v - mean) * (v - mean) * p for v, p in zip(support, probabilities)
        )
        return mean, variance


def prepare_margins(n1: int, n0: int, events: int) -> PreparedMargins:
    """Build the parameter-independent structure for one set of fixed margins."""
    return PreparedMargins(n1, n0, events)


def fnch_probabilities(
    n1: int,
    n0: int,
    events: int,
    log_odds: float,
) -> tuple[tuple[int, ...], tuple[float, ...]]:
    """Evaluate a Fisher noncentral-hypergeometric probability vector.

    Convenience wrapper that prepares a single-use :class:`PreparedMargins`.
    Callers evaluating repeatedly at fixed margins, which is every inversion,
    should prepare once and reuse instead.
    """
    return prepare_margins(n1, n0, events).probabilities(log_odds)


def conditional_mean(n1: int, n0: int, events: int, log_odds: float) -> float:
    """Return the first-row conditional mean under one log odds ratio."""
    return prepare_margins(n1, n0, events).mean(log_odds)


def solve_monotone_log_parameter(
    function: Callable[[float], float],
    target: float,
    *,
    increasing: bool,
    method: str,
    side: str,
) -> float:
    """Solve a certified monotone equation on the extended log-OR domain."""
    left = -_LOG_LIMIT
    right = _LOG_LIMIT
    try:
        f_left = function(left)
        f_right = function(right)
    except NumericalError:
        raise
    except (OverflowError, ValueError, ZeroDivisionError, MemoryError) as exc:
        raise NumericalError(
            "endpoint evaluation failed during inversion",
            method=method,
            side=side,
        ) from exc
    values = (f_left, f_right, target)
    if any(not math.isfinite(value) for value in values):
        raise NumericalError(
            "non-finite value encountered during inversion",
            method=method,
            side=side,
        )
    bracketed = (
        f_left <= target <= f_right if increasing else f_right <= target <= f_left
    )
    if not bracketed:
        raise NumericalError(
            "monotone confidence-limit equation was not bracketed",
            method=method,
            side=side,
            diagnostics={"left": f_left, "right": f_right, "target": target},
        )

    for _ in range(220):
        middle = (left + right) / 2.0
        value = function(middle)
        if not math.isfinite(value):
            raise NumericalError(
                "non-finite value encountered during inversion",
                method=method,
                side=side,
            )
        if (value < target) == increasing:
            left = middle
        else:
            right = middle
        if right - left <= _ROOT_TOL * max(1.0, abs(middle)):
            break
    else:
        raise NumericalError(
            "confidence-limit inversion exceeded its iteration budget",
            method=method,
            side=side,
        )

    root = (left + right) / 2.0
    # Certify the bracket, not the function value. The loop maintains a
    # sign-changing bracket, which is a proof that a root lies inside it, so half
    # its width bounds the error in the returned log parameter. That is the
    # quantity the caller receives, and unlike a function residual it is
    # scale-invariant: the local derivative varies by orders of magnitude across
    # the inversion families sharing this solver (tail probabilities are O(1),
    # the conditional mean is O(n1)), so no single residual threshold fits all.
    # The residual is retained as a diagnostic only.
    log_error_bound = 0.5 * (right - left)
    residual = abs(function(root) - target)
    if not math.isfinite(root):
        raise NumericalError(
            "confidence-limit inversion produced a non-finite root",
            method=method,
            side=side,
            diagnostics={"log_error_bound": log_error_bound, "residual": residual},
        )
    if log_error_bound > _ROOT_TOL * max(1.0, abs(root)):
        raise NumericalError(
            "confidence-limit inversion failed its bracket-width criterion",
            method=method,
            side=side,
            diagnostics={"log_error_bound": log_error_bound, "residual": residual},
        )
    return root


def exp_parameter(log_value: float) -> float:
    """Map a finite/extended log parameter to the non-negative OR scale."""
    if log_value == -math.inf:
        return 0.0
    if log_value == math.inf or log_value > math.log(
        float.fromhex("0x1.fffffffffffffp+1023")
    ):
        return math.inf
    value = math.exp(log_value)
    return 0.0 if value < float.fromhex("0x0.0000000000001p-1022") else value


def _solve_mean_newton(
    margins: PreparedMargins,
    target: float,
    *,
    method: str,
) -> float:
    """Invert the conditional mean with bracket-safeguarded Newton steps.

    For the FNCH exponential family ``d/d eta E_eta[X] == Var_eta(X)``, so one
    ``moments`` traversal yields both the function value and its derivative.
    A Newton proposal is accepted only when it is finite and strictly inside
    the retained sign-changing bracket; otherwise the step is a bisection. The
    bracket is updated on every accepted evaluation and remains authoritative:
    termination and certification use exactly the bracket-width contract of
    ``solve_monotone_log_parameter``, so failure semantics are unchanged and
    the returned root carries the same parameter-error bound. Quadratic
    convergence near the root cuts distribution evaluations several-fold
    against pure bisection.
    """
    left = -_LOG_LIMIT
    right = _LOG_LIMIT
    try:
        f_left = margins.mean(left)
        f_right = margins.mean(right)
    except NumericalError:
        raise
    except (OverflowError, ValueError, ZeroDivisionError, MemoryError) as exc:
        raise NumericalError(
            "endpoint evaluation failed during inversion",
            method=method,
            side="point",
        ) from exc
    if any(not math.isfinite(v) for v in (f_left, f_right, target)):
        raise NumericalError(
            "non-finite value encountered during inversion",
            method=method,
            side="point",
        )
    if not f_left <= target <= f_right:
        raise NumericalError(
            "monotone confidence-limit equation was not bracketed",
            method=method,
            side="point",
            diagnostics={"left": f_left, "right": f_right, "target": target},
        )

    current = 0.5 * (left + right)
    for _ in range(220):
        mean, variance = margins.moments(current)
        if not math.isfinite(mean) or not math.isfinite(variance):
            raise NumericalError(
                "non-finite value encountered during inversion",
                method=method,
                side="point",
            )
        if mean < target:
            left = current
        else:
            right = current
        if right - left <= _ROOT_TOL * max(1.0, abs(0.5 * (left + right))):
            break
        proposal = math.inf
        if variance > 0.0:
            proposal = current - (mean - target) / variance
        if math.isfinite(proposal) and left < proposal < right:
            current = proposal
        else:
            current = 0.5 * (left + right)
    else:
        raise NumericalError(
            "confidence-limit inversion exceeded its iteration budget",
            method=method,
            side="point",
        )

    root = 0.5 * (left + right)
    log_error_bound = 0.5 * (right - left)
    if not math.isfinite(root):
        raise NumericalError(
            "confidence-limit inversion produced a non-finite root",
            method=method,
            side="point",
            diagnostics={"log_error_bound": log_error_bound},
        )
    if log_error_bound > _ROOT_TOL * max(1.0, abs(root)):
        raise NumericalError(
            "confidence-limit inversion failed its bracket-width criterion",
            method=method,
            side="point",
            diagnostics={"log_error_bound": log_error_bound},
        )
    return root


def conditional_mle(
    a: int,
    b: int,
    c: int,
    d: int,
    *,
    prepared: PreparedMargins | None = None,
) -> float:
    """Return the conditional MLE under the fixed-margin FNCH model.

    ``prepared`` lets a caller that already holds the margins structure reuse it
    rather than rebuilding it; the result is identical either way.
    """
    n1, n0, events = a + b, c + d, a + c
    lower, upper = support_bounds(n1, n0, events)
    if lower == upper:
        return math.nan
    if a == lower:
        return 0.0
    if a == upper:
        return math.inf
    margins = prepared if prepared is not None else prepare_margins(n1, n0, events)
    log_value = _solve_mean_newton(margins, float(a), method="conditional_mle")
    return exp_parameter(log_value)


def ordered_p_value(
    n1: int,
    n0: int,
    events: int,
    observed: int,
    log_odds: float,
    *,
    ordering: str,
    prepared: PreparedMargins | None = None,
) -> float:
    """Return an inclusive minimum-likelihood or Blaker ordered p-value.

    ``prepared`` lets an inversion reuse one margins structure across all of its
    evaluations instead of rebuilding it per call.
    """
    margins = prepared if prepared is not None else prepare_margins(n1, n0, events)
    support, probabilities = margins.probabilities(log_odds)
    try:
        index = support.index(observed)
    except ValueError as exc:
        raise NumericalError("observed count is outside conditional support") from exc
    if ordering == "minlike":
        order = probabilities
    elif ordering == "blaker":
        lower_tail: list[float] = []
        running = 0.0
        for probability in probabilities:
            running += probability
            lower_tail.append(running)
        upper_tail = [0.0] * len(probabilities)
        running = 0.0
        for position in range(len(probabilities) - 1, -1, -1):
            running += probabilities[position]
            upper_tail[position] = running
        order = tuple(min(low, high) for low, high in zip(lower_tail, upper_tail))
    else:
        raise ValueError(f"unknown conditional ordering {ordering!r}")

    threshold = math.nextafter(order[index] * (1.0 + 1e-10), math.inf)
    p_value = math.fsum(
        probability
        for probability, rank in zip(probabilities, order)
        if rank <= threshold
    )
    if not math.isfinite(p_value) or p_value < -1e-15 or p_value > 1.0 + 1e-12:
        raise NumericalError("ordered conditional p-value failed certification")
    return min(1.0, max(0.0, p_value))


# Explicit conservative roundoff inflation applied to every certified bound, per
# the hull specification (docs_md/ordered_hull_specification.md, E2). The margin
# dominates the measured kernel evaluation error (about 3e-14 at width 2e4) by
# more than four orders of magnitude, covers running-sum rounding for support
# widths up to about 1e6, and is validated against dense sampling in the test
# suite. Pure Python has no directed rounding, so explicit inflation is the
# reviewed zero-dependency enclosure mechanism.
_BOUND_INFLATION = 1e-9
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
_HULL_BOUND_BUDGET = 50000
# Recursion depth cap for one rejection certificate.
_HULL_CERTIFY_DEPTH = 64
# The inflation margin covers cumulative running-sum rounding only up to this
# support width; wider tables fail closed rather than weakening the certificate.
_HULL_MAX_WIDTH = 1_000_000


class _AcceptedPoint(Exception):
    """Control-flow signal: a rejection certificate found an accepted point."""

    def __init__(self, log_odds: float) -> None:
        super().__init__(log_odds)
        self.log_odds = log_odds


class _HullBudget:
    """Mutable evaluation budget shared across one endpoint search."""

    __slots__ = ("remaining",)

    def __init__(self, total: int) -> None:
        self.remaining = total

    def spend(self, ordering: str) -> None:
        self.remaining -= 1
        if self.remaining < 0:
            raise NumericalError(
                "ordered hull enclosure exceeded its evaluation budget",
                method=ordering,
            )


def _ordered_p_upper_bound(
    margins: PreparedMargins,
    observed: int,
    t_low: float,
    t_high: float,
    *,
    ordering: str,
) -> float:
    """Certified upper bound of the ordered p-value over ``[t_low, t_high]``.

    Sound without assuming fixed ordering membership across the region, which is
    what makes it valid for Blaker as well as minimum-likelihood ordering: a
    support point whose membership over the region is uncertain contributes its
    full upper mass bound. Per the specification only an upper bound is
    computed; acceptance is certified by direct evaluation, never by a lower
    bound.

    Construction: relative log masses are anchored at the mode of the midpoint
    parameter, so over the region each point's exponent lies between
    ``rel[i] - v * h`` and ``rel[i] + v * h`` with ``h`` the half-width. A
    common anchor shift cancels in every ratio and prevents overflow. Per-point
    probability bounds divide by the opposite-endpoint normalising sum, and
    every bound is widened by ``_BOUND_INFLATION`` in the conservative
    direction.
    """
    support = margins.support
    centre = 0.5 * (t_low + t_high)
    half = 0.5 * (t_high - t_low)
    rel = margins._relative_log_masses(centre)

    # Remove the common factor exp(v_mode * (t - centre)) before bounding. It
    # cancels exactly in every probability ratio, but a decoupled min/max bound
    # does not know that: with raw support values the normalising sums swing by
    # exp(v_mode * half), which underflows the denominator bound and makes the
    # envelope vacuous for any usefully wide region. Centred deviations keep the
    # exponent spread proportional to the distance from the mode, which is what
    # lets far regions certify at large widths.
    v_anchor = support[margins.mode_index(centre)]
    deviations = [abs(v - v_anchor) for v in support]
    hi_exp = [r + dv * half for r, dv in zip(rel, deviations)]
    lo_exp = [r - dv * half for r, dv in zip(rel, deviations)]
    anchor = max(hi_exp)
    inflate = 1.0 + _BOUND_INFLATION
    deflate = 1.0 - _BOUND_INFLATION
    mass_hi = [math.exp(x - anchor) * inflate for x in hi_exp]
    mass_lo = [math.exp(x - anchor) * deflate for x in lo_exp]

    total_hi = math.fsum(mass_hi) * inflate
    total_lo = math.fsum(mass_lo) * deflate
    if not math.isfinite(total_hi) or total_hi <= 0.0:
        raise NumericalError("hull bound normalisation failed", method=ordering)

    prob_hi = [min(1.0, m / total_lo) if total_lo > 0.0 else 1.0 for m in mass_hi]
    prob_lo = [max(0.0, m / total_hi) for m in mass_lo]

    if ordering == "minlike":
        rank_hi_observed = prob_hi[margins.index_of(observed)]
        rank_lo = prob_lo
    elif ordering == "blaker":
        width = len(support)
        forward_lo = [0.0] * width
        backward_lo = [0.0] * width
        running = 0.0
        for i in range(width):
            running += prob_lo[i]
            forward_lo[i] = running
        running = 0.0
        for i in range(width - 1, -1, -1):
            running += prob_lo[i]
            backward_lo[i] = running
        forward_hi_observed = 0.0
        observed_index = margins.index_of(observed)
        for i in range(observed_index + 1):
            forward_hi_observed += prob_hi[i]
        backward_hi_observed = 0.0
        for i in range(width - 1, observed_index - 1, -1):
            backward_hi_observed += prob_hi[i]
        # Running sums are not fsum, so widen once more for their rounding.
        rank_hi_observed = min(
            1.0, min(forward_hi_observed, backward_hi_observed) * inflate
        )
        rank_lo = [
            max(0.0, min(f, g) * deflate) for f, g in zip(forward_lo, backward_lo)
        ]
    else:  # pragma: no cover - guarded by callers
        raise ValueError(f"unknown conditional ordering {ordering!r}")

    # Sound upper bound on the frozen tie threshold. The true threshold is
    # nextafter(rank(a) * (1 + 1e-10), inf), monotone in rank(a), and rank(a)
    # over the region is at most rank_hi_observed.
    thr_high = math.nextafter(rank_hi_observed * (1.0 + 1e-10), math.inf)

    # A point is certainly not a member, for every parameter in the region, only
    # when even its lowest possible rank exceeds the highest possible threshold.
    # Everything else contributes its full upper mass bound.
    p_upper = math.fsum(p for p, r in zip(prob_hi, rank_lo) if r <= thr_high)
    p_upper = min(1.0, p_upper * inflate)
    if not math.isfinite(p_upper):
        raise NumericalError("hull bound evaluation failed", method=ordering)
    return p_upper


def ordered_interval(
    a: int,
    b: int,
    c: int,
    d: int,
    alpha: float,
    *,
    ordering: str,
) -> tuple[float, float]:
    """Return the certified interval hull of one inverted ordered p-value.

    The returned interval is a numerically certified enclosure of the smallest
    interval containing the complete accepted set ``{eta : p(eta) >= alpha}``,
    which may be disconnected. Contract in
    ``docs_md/ordered_hull_specification.md``: a region is excluded only by a
    certified upper bound of ``p`` below ``alpha``; acceptance by direct
    evaluation only ever extends the interval outward; finite endpoint excess is
    bounded by the shared ``_ROOT_TOL`` parameter-error contract beyond the
    closure of the near-accepted set; structural endpoints are exact; and
    failure to certify within budget raises rather than returning a best-effort
    interval.
    """
    n1, n0, events = a + b, c + d, a + c
    support_lower, support_upper = support_bounds(n1, n0, events)
    if support_lower == support_upper:
        return 0.0, math.inf

    # One preparation for the whole inversion: the MLE solve, every acceptance
    # probe and every certified bound share these parameter-independent ratios.
    margins = prepare_margins(n1, n0, events)
    if margins.width > _HULL_MAX_WIDTH:
        raise NumericalError(
            "ordered hull certification is not supported above support width"
            f" {_HULL_MAX_WIDTH}",
            method=ordering,
            diagnostics={"support_size": margins.width},
        )

    point = conditional_mle(a, b, c, d, prepared=margins)
    # For boundary observations the likelihood supremum sits at an extended
    # endpoint, and the acceptance probe below must be taken beyond every
    # ordering breakpoint, all of which lie within the range of the adjacent
    # log ratios. A fixed proxy of +/-36 is not sufficient for extreme margins
    # whose ratios exceed it, and previously produced a false "below alpha at
    # its likelihood maximum" refusal on valid tables.
    # Adjacent masses tie exactly at t = -r_k, so every mass-ordering change
    # lies in [-r_first, -r_last] and a probe beyond that span sees the frozen
    # limiting ordering.
    ratios = margins._ratios
    below_all = min(-36.0, -(ratios[0] if ratios else 0.0) - 5.0)
    above_all = max(36.0, -(ratios[-1] if ratios else 0.0) + 5.0)
    if point == 0.0:
        center = max(below_all, -_LOG_LIMIT + 1.0)
    elif math.isinf(point):
        center = min(above_all, _LOG_LIMIT - 1.0)
    else:
        center = math.log(point)

    def accepted(log_odds: float) -> bool:
        try:
            return (
                ordered_p_value(
                    n1,
                    n0,
                    events,
                    a,
                    log_odds,
                    ordering=ordering,
                    prepared=margins,
                )
                >= alpha
            )
        except (OverflowError, ValueError, ZeroDivisionError, MemoryError) as exc:
            raise NumericalError(
                "ordered conditional p-value evaluation failed",
                method=ordering,
            ) from exc

    try:
        center_ok = accepted(center)
    except NumericalError:
        raise
    except (OverflowError, ValueError, ZeroDivisionError, MemoryError) as exc:
        raise NumericalError(
            "ordered conditional p-value evaluation failed at the MLE",
            method=ordering,
        ) from exc
    if not center_ok:
        raise NumericalError(
            "ordered conditional p-value is below alpha at its likelihood maximum",
            method=ordering,
        )

    def reduce_frontier(
        inner: float, outer: float, direction: int, budget: _HullBudget, depth: int
    ) -> float:
        """Certify rejection outward-first and return the reduced frontier.

        For ``direction > 0`` the region is ``[inner, outer]`` with ``outer``
        the current frontier. Returns ``f`` such that everything strictly
        between ``f`` and ``outer`` on the outward side is certified rejected;
        ``f == inner`` means the whole region certified. Descends into the
        outermost failing half first, so the work per call is proportional to
        the recursion depth rather than to the number of resolvable cells, and
        certifying the region between the accepted set and the frontier costs a
        bounded number of evaluations per level.

        A direct evaluation that finds an accepted midpoint raises
        ``_AcceptedPoint`` instead, extending the hull. An unresolved cell at
        the resolution floor returns its own outer edge, which leaves the
        frontier at the top of the near-accepted zone: containment is
        unaffected and the excess is bounded by the width of
        ``{t : p(t) >= alpha - kappa}`` beyond the accepted set, where ``kappa``
        is the certification floor set by ``_BOUND_INFLATION``.
        """
        budget.spend(ordering)
        t_low, t_high = (inner, outer) if direction > 0 else (outer, inner)
        if _ordered_p_upper_bound(margins, a, t_low, t_high, ordering=ordering) < alpha:
            return inner
        middle = 0.5 * (inner + outer)
        if accepted(middle):
            raise _AcceptedPoint(middle)
        if depth <= 0 or abs(outer - inner) <= _ROOT_TOL * max(1.0, abs(middle)):
            return outer
        # Outermost half first: (middle, outer) lies outward of (inner, middle).
        frontier_outer = reduce_frontier(middle, outer, direction, budget, depth - 1)
        moved_fully = frontier_outer == middle
        if not moved_fully:
            return frontier_outer
        return reduce_frontier(inner, middle, direction, budget, depth - 1)

    def outer_endpoint(direction: int) -> float:
        """Certified outer endpoint of the hull in one direction.

        Invariant: every parameter strictly beyond ``frontier`` in this
        direction is certified rejected, and ``best`` is an accepted point (or
        the conservative inner edge of an unresolvable zone, which only widens
        the result). Terminates when the remaining gap meets the shared
        parameter-error contract, or conservatively at the frontier when the
        gap consists entirely of near-accepted parameters below the
        certification floor.

        Beyond the search limit no acceptance is possible once the limit itself
        is rejected: all ordering breakpoints lie within the range of the
        adjacent log ratios, whose magnitude is far below the limit for any
        validated table, and beyond the last breakpoint the p-value reduces to
        a fixed tail probability, monotone in the parameter by stochastic
        ordering.
        """
        limit = _LOG_LIMIT if direction > 0 else -_LOG_LIMIT
        # Structural extension per specification R4: if acceptance persists at
        # the domain limit the endpoint is the exact extended value, never the
        # finite sentinel.
        if accepted(limit):
            return math.inf if direction > 0 else -math.inf

        best = center
        frontier = limit
        budget = _HullBudget(_HULL_BOUND_BUDGET)
        for _ in range(200):
            gap = (frontier - best) if direction > 0 else (best - frontier)
            if gap <= _ROOT_TOL * max(1.0, abs(frontier)):
                return frontier
            candidate = 0.5 * (best + frontier)
            if accepted(candidate):
                best = candidate
                continue
            try:
                reduced = reduce_frontier(
                    candidate, frontier, direction, budget, _HULL_CERTIFY_DEPTH
                )
            except _AcceptedPoint as found:
                best = (
                    max(best, found.log_odds)
                    if direction > 0
                    else min(best, found.log_odds)
                )
                continue
            if reduced != frontier:
                frontier = reduced
                continue
            # No progress: the region abutting the frontier is a near-accepted
            # zone below the certification floor. Probe once just inside; if
            # even that is not accepted, return the frontier. Containment is
            # preserved and the excess is bounded by the width of the
            # near-accepted zone, per the specification.
            step = _ROOT_TOL * max(1.0, abs(frontier))
            inside = frontier - direction * step
            if accepted(inside):
                best = inside
                continue
            return frontier
        raise NumericalError(
            "ordered hull enclosure did not converge",
            method=ordering,
        )

    lower_log = -math.inf if a == support_lower else outer_endpoint(-1)
    upper_log = math.inf if a == support_upper else outer_endpoint(1)
    lower, upper = exp_parameter(lower_log), exp_parameter(upper_log)
    if lower < 0.0 or lower > upper:
        raise NumericalError(
            "ordered conditional inversion returned invalid bounds",
            method=ordering,
        )
    return lower, upper


__all__ = [
    "conditional_mean",
    "conditional_mle",
    "exp_parameter",
    "fnch_probabilities",
    "normal_quantile",
    "ordered_interval",
    "ordered_p_value",
    "solve_monotone_log_parameter",
    "support_bounds",
]
