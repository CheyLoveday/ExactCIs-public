"""Small-table exact references derived directly from the public U0 equations.

Only standard-library arithmetic is used. There are deliberately no production
imports, floating comparisons, optimisers, or research-packet dependencies.
Rational evaluation points are witnesses, never a nuisance-supremum grid.
This module neither classifies the real-continuum supremum nor returns a CI.
"""

from __future__ import annotations

from fractions import Fraction
from math import comb
from typing import Literal

Direction = Literal["greater", "less"]
Point = tuple[int, int]
Mask = tuple[Point, ...]
Polynomial = tuple[Fraction, ...]  # ascending power coefficients


def _groups(n1: int, n0: int) -> None:
    if any(type(n) is not int or n <= 0 for n in (n1, n0)):
        raise ValueError("group sizes must be positive integers")


def _point(n1: int, n0: int, point: Point) -> None:
    x, y = point
    if any(type(k) is not int or not 0 <= k <= n for k, n in zip(point, (n1, n0))):
        raise ValueError("success counts must be integers within their groups")


def _effect(psi: Fraction) -> None:
    if not isinstance(psi, Fraction) or psi <= 0:
        raise ValueError("effect must be an explicit positive Fraction")


def _unit(value: Fraction) -> None:
    if not isinstance(value, Fraction) or not 0 <= value <= 1:
        raise ValueError("probability or level must be an explicit Fraction in [0,1]")


def _direction(direction: Direction) -> None:
    if direction not in ("greater", "less"):
        raise ValueError("direction must be greater or less")


def sample_space(n1: int, n0: int) -> Mask:
    """Enumerate the full product-binomial sample space in canonical order."""
    _groups(n1, n0)
    return tuple((x, y) for x in range(n1 + 1) for y in range(n0 + 1))


def _check_mask(n1: int, n0: int, mask: Mask) -> None:
    _groups(n1, n0)
    for point in mask:
        _point(n1, n0, point)
    if len(set(mask)) != len(mask):
        raise ValueError("a mask cannot contain a candidate more than once")


def tail_weights(
    n1: int, n0: int, point: Point, psi: Fraction, direction: Direction
) -> tuple[Fraction, Fraction]:
    """Return the unnormalised inclusive tail and its positive normaliser."""
    _groups(n1, n0)
    _point(n1, n0, point)
    _effect(psi)
    _direction(direction)
    x, y = point
    margin = x + y
    numerator = denominator = Fraction(0)
    for k in range(max(0, margin - n0), min(n1, margin) + 1):
        weight = comb(n1, k) * comb(n0, margin - k) * psi**k
        denominator += weight
        if (k >= x) if direction == "greater" else (k <= x):
            numerator += weight
    return numerator, denominator


def fisher_tail(
    n1: int, n0: int, point: Point, psi: Fraction, direction: Direction
) -> Fraction:
    """Evaluate a conditional tail, not an unconditional p-value."""
    numerator, denominator = tail_weights(n1, n0, point, psi, direction)
    return numerator / denominator


def rejection_mask(
    n1: int, n0: int, observed: Point, psi: Fraction, direction: Direction
) -> Mask:
    """Compare exact unnormalised tails by inclusive cross multiplication."""
    observed_tail, observed_total = tail_weights(n1, n0, observed, psi, direction)
    selected = []
    for candidate in sample_space(n1, n0):
        tail, total = tail_weights(n1, n0, candidate, psi, direction)
        if tail * observed_total <= observed_tail * total:
            selected.append(candidate)
    return tuple(selected)


def product_mass(
    n1: int, n0: int, point: Point, psi: Fraction, q: Fraction
) -> Fraction:
    """Direct product of two binomial masses, including q=0 and q=1."""
    _groups(n1, n0)
    _point(n1, n0, point)
    _effect(psi)
    _unit(q)
    x, y = point
    p1 = psi * q / (1 - q + psi * q)
    return (
        comb(n1, x)
        * p1**x
        * (1 - p1) ** (n1 - x)
        * comb(n0, y)
        * q**y
        * (1 - q) ** (n0 - y)
    )


def mask_probability(
    n1: int, n0: int, mask: Mask, psi: Fraction, q: Fraction
) -> Fraction:
    """Enumerate the event mass independently of the polynomial construction."""
    _check_mask(n1, n0, mask)
    _effect(psi)
    _unit(q)
    return sum((product_mass(n1, n0, z, psi, q) for z in mask), Fraction(0))


def threshold_coefficients(
    n1: int, n0: int, mask: Mask, psi: Fraction, level: Fraction
) -> Polynomial:
    """Expand H=A-level*B exactly; retain all N+1 slots through degree drops."""
    _check_mask(n1, n0, mask)
    _effect(psi)
    _unit(level)
    size = n1 + n0
    coefficients = [Fraction(0)] * (size + 1)
    for x, y in mask:
        margin = x + y
        weight = comb(n1, x) * comb(n0, y) * psi**x
        for j in range(size - margin + 1):
            coefficients[margin + j] += weight * comb(size - margin, j) * (-1) ** j
    for j in range(n1 + 1):
        coefficients[j] -= level * comb(n1, j) * (psi - 1) ** j
    return tuple(coefficients)


def bernstein_coefficients(
    n1: int, n0: int, mask: Mask, psi: Fraction
) -> tuple[Polynomial, Polynomial]:
    """Return numerator and denominator control coefficients at common degree N."""
    _check_mask(n1, n0, mask)
    _effect(psi)
    size = n1 + n0
    selected = set(mask)
    numerator = [Fraction(0)] * (size + 1)
    denominator = [Fraction(0)] * (size + 1)
    for x, y in sample_space(n1, n0):
        margin = x + y
        control = comb(n1, x) * comb(n0, y) * psi**x / comb(size, margin)
        denominator[margin] += control
        if (x, y) in selected:
            numerator[margin] += control
    return tuple(numerator), tuple(denominator)


def evaluate(coefficients: Polynomial, value: Fraction) -> Fraction:
    """Evaluate an ascending-power rational polynomial by Horner's rule."""
    if not isinstance(value, Fraction):
        raise ValueError("evaluation point must be an explicit Fraction")
    result = Fraction(0)
    for coefficient in reversed(coefficients):
        result = result * value + coefficient
    return result


def _tail_polynomials(
    n1: int, n0: int, point: Point, direction: Direction
) -> tuple[Polynomial, Polynomial]:
    x, y = point
    numerator = [Fraction(0)] * (n1 + 1)
    denominator = [Fraction(0)] * (n1 + 1)
    for k in range(max(0, x + y - n0), min(n1, x + y) + 1):
        denominator[k] = Fraction(comb(n1, k) * comb(n0, x + y - k))
        if (k >= x) if direction == "greater" else (k <= x):
            numerator[k] = denominator[k]
    return tuple(numerator), tuple(denominator)


def comparison_polynomial(
    n1: int, n0: int, observed: Point, candidate: Point, direction: Direction
) -> Polynomial:
    """Unreduced G=P_candidate*W_observed-P_observed*W_candidate; in iff G<=0."""
    _groups(n1, n0)
    _point(n1, n0, observed)
    _point(n1, n0, candidate)
    _direction(direction)
    pn, pd = _tail_polynomials(n1, n0, candidate, direction)
    on, od = _tail_polynomials(n1, n0, observed, direction)
    coefficients = [Fraction(0)] * (2 * n1 + 1)
    for i in range(n1 + 1):
        for j in range(n1 + 1):
            coefficients[i + j] += pn[i] * od[j] - on[i] * pd[j]
    while len(coefficients) > 1 and coefficients[-1] == 0:
        coefficients.pop()
    return tuple(coefficients)


def structural_pair(
    n1: int, n0: int, observed: Point, endpoint: Literal["zero", "infinity"]
) -> tuple[Fraction, Fraction]:
    """Direct-support values in (greater, less) order, not acceptance labels."""
    _groups(n1, n0)
    _point(n1, n0, observed)
    a, c = observed
    if endpoint == "zero":
        return Fraction(int(a == 0 or c == n0)), Fraction(1)
    if endpoint == "infinity":
        return Fraction(1), Fraction(int(c == 0 or a == n1))
    raise ValueError("endpoint must be zero or infinity")


def subdivide_bernstein(
    coefficients: Polynomial, split: Fraction = Fraction(1, 2)
) -> tuple[Polynomial, Polynomial]:
    """Exact de Casteljau controls on [0,split] and [split,1].

    Each returned vector is parameterised by its own unit interval. This also
    handles split=0/1: the degenerate child is the constant endpoint value.
    """
    _unit(split)
    if not isinstance(coefficients, (tuple, list)) or not coefficients:
        raise ValueError("Bernstein coefficients must be a nonempty tuple or list")
    if any(
        type(value) is not int and not isinstance(value, Fraction)
        for value in coefficients
    ):
        raise ValueError("Bernstein coefficients must be exact integers or Fractions")
    row = tuple(Fraction(value) for value in coefficients)
    left = [row[0]]
    right = [row[-1]]
    while len(row) > 1:
        row = tuple((1 - split) * a + split * b for a, b in zip(row, row[1:]))
        left.append(row[0])
        right.append(row[-1])
    return tuple(left), tuple(reversed(right))


def cutoff_vector(
    n1: int, n0: int, observed: Point, psi: Fraction, direction: Direction
) -> tuple[int, ...]:
    """Independently reconstruct an inclusive Fisher cutoff at each total.

    This uses cumulative normalised conditional weights, not rejection_mask's
    candidate/observed cross products. For ``greater``, accepted x form a
    suffix, encoded by its first x (hi+1 for empty); for ``less``, they form a
    prefix, encoded by its last x (lo-1 for empty). Contiguity is checked rather
    than inferred from the recorded first or last selected value.
    """
    threshold = fisher_tail(n1, n0, observed, psi, direction)
    cutoffs = []
    for margin in range(n1 + n0 + 1):
        lo, hi = max(0, margin - n0), min(n1, margin)
        weights = tuple(
            comb(n1, x) * comb(n0, margin - x) * psi**x for x in range(lo, hi + 1)
        )
        normaliser = sum(weights, Fraction(0))
        cumulative = Fraction(0)
        accepted = []
        for x, weight in zip(range(lo, hi + 1), weights):
            cumulative += weight
            numerator = (
                cumulative if direction == "less" else normaliser - cumulative + weight
            )
            if numerator / normaliser <= threshold:
                accepted.append(x)
        if direction == "greater":
            cutoff = accepted[0] if accepted else hi + 1
            expected = list(range(cutoff, hi + 1))
        else:
            cutoff = accepted[-1] if accepted else lo - 1
            expected = list(range(lo, cutoff + 1))
        if accepted != expected:
            raise ArithmeticError("Fisher accepted margin is not a contiguous tail")
        cutoffs.append(cutoff)
    return tuple(cutoffs)


def expand_cutoffs(
    n1: int, n0: int, cutoffs: tuple[int, ...], direction: Direction
) -> Mask:
    """Expand checked per-margin cutoff integers in sample_space order."""
    _groups(n1, n0)
    _direction(direction)
    if not isinstance(cutoffs, (tuple, list)) or len(cutoffs) != n1 + n0 + 1:
        raise ValueError("one cutoff is required for every total from 0 through N")
    for margin, cutoff in enumerate(cutoffs):
        lo, hi = max(0, margin - n0), min(n1, margin)
        minimum, maximum = (lo, hi + 1) if direction == "greater" else (lo - 1, hi)
        if type(cutoff) is not int or not minimum <= cutoff <= maximum:
            raise ValueError("cutoff lies outside the margin's permitted tail bounds")
    return tuple(
        (x, y)
        for x, y in sample_space(n1, n0)
        if (x >= cutoffs[x + y] if direction == "greater" else x <= cutoffs[x + y])
    )
