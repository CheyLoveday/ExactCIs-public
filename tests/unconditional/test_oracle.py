"""Finite exact checks of U0 identities, independent of production arithmetic.

The rational nuisance points below exercise algebraic identities only. They do
not approximate a nuisance supremum or establish real-continuum coverage.
"""

from fractions import Fraction as F
from math import comb

import pytest

from ._oracle import (
    bernstein_coefficients,
    comparison_polynomial,
    cutoff_vector,
    evaluate,
    expand_cutoffs,
    fisher_tail,
    mask_probability,
    product_mass,
    rejection_mask,
    sample_space,
    structural_pair,
    subdivide_bernstein,
    tail_weights,
    threshold_coefficients,
)
from ._polynomial import threshold_decision


def _bernstein(controls: tuple[F, ...], q: F) -> F:
    """Direct basis sum, independently of the oracle's power expansion."""
    degree = len(controls) - 1
    return sum(
        (
            control * comb(degree, k) * q**k * (1 - q) ** (degree - k)
            for k, control in enumerate(controls)
        ),
        F(0),
    )


@pytest.mark.parametrize("n1", range(1, 5))
@pytest.mark.parametrize("n0", range(1, 5))
@pytest.mark.parametrize("psi", (F(1, 3), F(1), F(7, 3)))
def test_small_groups_exact_mass_and_control_identities(n1, n0, psi):
    """Every observation for 48 finite group/effect combinations is checked."""
    space = sample_space(n1, n0)
    nuisance_points = (F(0), F(2, 7), F(1))
    masses = {
        q: {point: product_mass(n1, n0, point, psi, q) for point in space}
        for q in nuisance_points
    }
    for q in nuisance_points:
        assert sum(masses[q].values()) == 1
        assert all(mass >= 0 for mass in masses[q].values())

    for observed in space:
        for direction in ("greater", "less"):
            mask = rejection_mask(n1, n0, observed, psi, direction)
            cutoffs = cutoff_vector(n1, n0, observed, psi, direction)
            assert expand_cutoffs(n1, n0, cutoffs, direction) == mask
            numerator, denominator = bernstein_coefficients(n1, n0, mask, psi)
            level = F(1, 40)
            coefficients = threshold_coefficients(n1, n0, mask, psi, level)
            assert len(coefficients) == n1 + n0 + 1
            assert len(numerator) == len(denominator) == len(coefficients)
            assert observed in mask
            assert all(0 <= a <= b and b > 0 for a, b in zip(numerator, denominator))

            observed_tail = fisher_tail(n1, n0, observed, psi, direction)
            for margin in range(n1 + n0 + 1):
                weights = {
                    (x, y): comb(n1, x) * comb(n0, y) * psi**x
                    for x, y in space
                    if x + y == margin
                }
                conditional_mass = sum(
                    (weight for point, weight in weights.items() if point in mask),
                    F(0),
                ) / sum(weights.values())
                assert numerator[margin] / denominator[margin] == conditional_mass
                # This is a finite conditional domination check at this effect.
                assert conditional_mass <= observed_tail

            for q in nuisance_points:
                b = (1 + (psi - 1) * q) ** n1
                direct = sum((masses[q][point] for point in mask), F(0))
                assert b > 0
                assert _bernstein(denominator, q) == b
                assert _bernstein(numerator, q) == direct * b
                assert evaluate(coefficients, q) == (direct - level) * b
                assert mask_probability(n1, n0, mask, psi, q) == direct


@pytest.mark.parametrize("n1,n0", ((1, 4), (2, 3), (4, 1), (4, 4)))
@pytest.mark.parametrize("psi", (F(1, 5), F(1), F(5, 2)))
def test_group_swap_and_outcome_complement_transport_nuisance(n1, n0, psi):
    space = sample_space(n1, n0)
    for q in (F(0), F(2, 7), F(1)):
        swapped_q = psi * q / (1 - q + psi * q)
        for x, y in space:
            mass = product_mass(n1, n0, (x, y), psi, q)
            assert mass == product_mass(n0, n1, (y, x), 1 / psi, swapped_q)
            assert mass == product_mass(n1, n0, (n1 - x, n0 - y), 1 / psi, 1 - q)

    for observed in space:
        x, y = observed
        for direction, reversed_direction in (("greater", "less"), ("less", "greater")):
            mask = rejection_mask(n1, n0, observed, psi, direction)
            swapped = rejection_mask(n0, n1, (y, x), 1 / psi, reversed_direction)
            complemented = rejection_mask(
                n1, n0, (n1 - x, n0 - y), 1 / psi, reversed_direction
            )
            assert {(v, u) for u, v in mask} == set(swapped)
            assert {(n1 - u, n0 - v) for u, v in mask} == set(complemented)
            assert fisher_tail(n1, n0, observed, psi, direction) == fisher_tail(
                n0, n1, (y, x), 1 / psi, reversed_direction
            )


def test_transformed_group_denominator_mutation_is_detectable():
    n1, n0, psi, q = 2, 4, F(1, 4), F(3, 7)
    space = sample_space(n1, n0)
    raw_mass = sum(
        (
            comb(n1, x)
            * comb(n0, y)
            * psi**x
            * q ** (x + y)
            * (1 - q) ** (n1 + n0 - x - y)
            for x, y in space
        ),
        F(0),
    )
    denominator = 1 + (psi - 1) * q
    assert raw_mass / denominator**n1 == 1
    assert raw_mass / denominator**n0 != 1
    mask = rejection_mask(n1, n0, (1, 0), psi, "greater")
    a, _ = bernstein_coefficients(n1, n0, mask, psi)
    assert _bernstein(a, q) / denominator**n0 != mask_probability(n1, n0, mask, psi, q)


@pytest.mark.parametrize("n1,n0", ((1, 1), (2, 3), (4, 4)))
def test_equality_null_controls_and_hypergeometric_tails(n1, n0):
    space = sample_space(n1, n0)
    _, denominator = bernstein_coefficients(n1, n0, space, F(1))
    assert denominator == (F(1),) * (n1 + n0 + 1)
    for x, y in space:
        margin = x + y
        normalizer = F(comb(n1 + n0, margin))
        for direction in ("greater", "less"):
            tail, total = tail_weights(n1, n0, (x, y), F(1), direction)
            assert total == normalizer
            assert fisher_tail(n1, n0, (x, y), F(1), direction) == tail / normalizer


@pytest.mark.parametrize("psi", (F(1, 5), F(1), F(5)))
def test_neutral_margins_and_inclusive_permanent_ties(psi):
    space = sample_space(2, 2)
    for neutral in ((0, 0), (2, 2)):
        for direction in ("greater", "less"):
            assert fisher_tail(2, 2, neutral, psi, direction) == 1
            assert rejection_mask(2, 2, neutral, psi, direction) == space
    for direction in ("greater", "less"):
        assert fisher_tail(2, 2, (1, 0), psi, direction) == fisher_tail(
            2, 2, (2, 1), psi, direction
        )
        assert (2, 1) in rejection_mask(2, 2, (1, 0), psi, direction)
        assert comparison_polynomial(2, 2, (1, 0), (2, 1), direction) == (F(0),)


@pytest.mark.parametrize("n1", range(1, 5))
@pytest.mark.parametrize("n0", range(1, 5))
def test_structural_pairs_and_inclusive_level_rule(n1, n0):
    for a, c in sample_space(n1, n0):
        zero = structural_pair(n1, n0, (a, c), "zero")
        infinity = structural_pair(n1, n0, (a, c), "infinity")
        assert zero == (F(a == 0 or c == n0), F(1))
        assert infinity == (F(1), F(c == 0 or a == n1))
        assert all(p >= 0 for pair in (zero, infinity) for p in pair)
        for level in (F(1, 40), F(1)):
            assert all(p >= level for p in zero) == (a == 0 or c == n0)
            assert all(p >= level for p in infinity) == (c == 0 or a == n1)
        assert zero == tuple(reversed(structural_pair(n0, n1, (c, a), "infinity")))


def test_public_float_alpha_uses_its_binary_rational_exactly():
    alpha = 0.05
    numerator, denominator = alpha.as_integer_ratio()
    level = F(numerator, 2 * denominator)
    assert level * 2 == F.from_float(alpha)
    assert level != F(1, 40)
    mask = rejection_mask(2, 3, (2, 0), F(1), "greater")
    coefficients = threshold_coefficients(2, 3, mask, F(1), level)
    assert coefficients[0] == -level
    assert evaluate(coefficients, F(0)) == -level
    assert coefficients != threshold_coefficients(2, 3, mask, F(1), F(1, 40))


@pytest.mark.parametrize("n1,n0", ((1, 1), (1, 2), (2, 1), (2, 2)))
@pytest.mark.parametrize("psi", (F(1, 3), F(1), F(3)))
@pytest.mark.parametrize("side_level", (F(0), F(1, 40), F(1, 4), F(1, 2)))
def test_finite_exact_directional_validity_and_two_sided_coverage(
    n1, n0, psi, side_level
):
    """Finite reference domain only; all real nuisances are used in each decision.

    Observation probabilities are checked at four rational nuisance values.
    This is a regression check, not the general coverage theorem.
    """
    space = sample_space(n1, n0)
    decisions = {}
    for observed in space:
        decisions[observed] = tuple(
            threshold_decision(
                threshold_coefficients(
                    n1,
                    n0,
                    rejection_mask(n1, n0, observed, psi, direction),
                    psi,
                    side_level,
                )
            )
            for direction in ("greater", "less")
        )
    for q in (F(0), F(1, 5), F(1, 2), F(1)):
        masses = {point: product_mass(n1, n0, point, psi, q) for point in space}
        for direction_index in (0, 1):
            rejected_mass = sum(
                (
                    mass
                    for point, mass in masses.items()
                    if not decisions[point][direction_index]
                ),
                F(0),
            )
            assert rejected_mass <= side_level
        accepted_mass = sum(
            (mass for point, mass in masses.items() if all(decisions[point])), F(0)
        )
        assert accepted_mass >= 1 - 2 * side_level


@pytest.mark.parametrize(
    "direction,observed,delta", (("greater", (2, 0), 1), ("less", (0, 2), -1))
)
def test_cutoff_off_by_one_mutation_excludes_the_observation(
    direction, observed, delta
):
    cutoffs = cutoff_vector(3, 2, observed, F(1), direction)
    mask = expand_cutoffs(3, 2, cutoffs, direction)
    assert observed in mask
    mutated = list(cutoffs)
    mutated[sum(observed)] += delta
    mutated_mask = expand_cutoffs(3, 2, tuple(mutated), direction)
    assert observed not in mutated_mask
    assert mutated_mask != mask


@pytest.mark.parametrize(
    "controls",
    ((F(3),), (F(-2), F(3)), (F(1, 7), F(-5, 3), F(2), F(-1, 9), F(4))),
)
@pytest.mark.parametrize("split", (F(0), F(2, 5), F(1)))
def test_de_casteljau_restrictions_equal_independent_basis_evaluation(controls, split):
    left, right = subdivide_bernstein(controls, split)
    assert len(left) == len(right) == len(controls)
    assert left[0] == controls[0]
    assert right[-1] == controls[-1]
    assert left[-1] == right[0] == _bernstein(controls, split)
    for point in (F(0), F(2, 7), F(1)):
        assert _bernstein(left, point) == _bernstein(controls, split * point)
        assert _bernstein(right, point) == _bernstein(
            controls, split + (1 - split) * point
        )
