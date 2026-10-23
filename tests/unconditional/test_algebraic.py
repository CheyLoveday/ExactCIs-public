"""Independent identities and failure cases for selected-root arithmetic."""

from fractions import Fraction as F

import pytest

from . import _parametric as q
from . import _polynomial as p
from ._algebraic import Element, Limits, Root, Work, between, compare, isolate, sign_at


def test_repeated_rational_roots_and_endpoint_ownership():
    w = Work()
    poly = p.multiply((0, -1, 1), p.multiply((-F(1, 2), 1), (-F(1, 2), 1)))
    roots = isolate(poly, F(0), F(1), w)
    assert [r.rational for r in roots] == [F(0), F(1, 2), F(1)]
    assert all(r.verify(w) for r in roots)


def test_irrational_sign_order_and_cross_polynomial_equality():
    w = Work()
    root = isolate((-2, 0, 1), F(1), F(2), w)[0]
    other = isolate(p.multiply((-2, 0, 1), (3, 1)), F(1), F(2), w)[0]
    assert compare(root, other, w) == 0
    assert sign_at((-2, 0, 1), root, w) == 0
    assert sign_at((-F(7, 5), 1), root, w) == 1
    assert sign_at((-F(3, 2), 1), root, w) == -1
    larger = isolate((-3, 0, 1), F(1), F(2), w)[0]
    assert compare(root, larger, w) == -1
    sample = between(root, larger, w)
    assert F(2) < sample**2 < F(3)


def test_reducible_definer_is_not_assumed_a_field():
    w = Work()
    # (s-1)(s-2): s-1 vanishes at the other embedding, but is invertible at 2.
    root = Root((2, -3, 1), F(3, 2), F(5, 2)).verify(w)
    inverse = Element(root, (1,), (-1, 1), w)
    assert not (inverse - 1)
    assert (inverse + 2).sign() == 1
    assert not ((inverse * 7) / 7 - 1)
    with pytest.raises(ValueError, match="zero denominator"):
        Element(root, (1,), (-2, 1), w)


def test_selected_embedding_preserves_negative_denominator_sign():
    w = Work()
    root = isolate((-2, 0, 1), F(1), F(2), w)[0]
    a = Element(root, (1,), (1, -1), w)
    assert a.sign() == -1
    assert not (a * Element(root, (1, -1), (1,), w) - 1)


def test_modular_inverse_requires_a_proved_unit():
    w = Work()
    root = isolate((-2, 0, 1), F(1), F(2), w)[0]
    inverse = Element(root, (1,), (1, 1), w)
    assert inverse.denominator == p.ONE
    assert inverse.numerator == (F(-1), F(1))
    # A denominator vanishing at the other component is not a unit modulo
    # the reducible definer, though it remains usable at the selected root.
    assert w.inverse_mod((-1, 1), (2, -3, 1)) is None


def test_cancelled_rational_functions_do_not_use_artificial_degree():
    w = Work(Limits(max_degree=2))
    a = Element(None, (1,), (1, 0, 1), w)
    b = Element(None, (1, 0, 1), (1,), w)
    assert not (a * b - 1)
    assert not (b / b - 1)
    assert not (a + a - 2 * a)
    with pytest.raises(ValueError, match="division by zero algebraic"):
        a / 0


@pytest.mark.parametrize(
    "root",
    [
        Root((1,), F(0), F(1)),
        Root((-2, 0, 2), F(0), F(2)),
        Root((-2, 0, 1), F(2), F(3)),
        Root((-2, 0, 1), F(-2), F(2)),
        Root((-2, 0, 1), F(2), F(1)),
        Root((-2, 0, 1), F(1), F(1)),
    ],
)
def test_invalid_root_claims_refuse(root):
    with pytest.raises(ValueError):
        root.verify(Work())


def test_budget_refuses_without_approximate_fallback():
    with pytest.raises(p.OracleLimitError, match="call budget"):
        isolate((-2, 0, 1), F(0), F(2), Work(Limits(max_calls=1)))
    with pytest.raises(ValueError):
        Limits(max_refinements=True)


@pytest.mark.parametrize(
    "coefficients,accepted",
    [
        ([(0,), (0,)], True),
        ([(-1,)], False),
        ([(1,)], True),
        ([(-F(1, 4),), (1,), (-1,)], True),
        ([(-F(1, 4) - F(1, 1000),), (1,), (-1,)], False),
        ([(0,), (-1,)], True),
    ],
)
def test_algebraic_field_sturm_matches_exact_rational_anchors(coefficients, accepted):
    w = Work()
    root = Root((-2, 0, 1), F(1), F(2)).verify(w)
    result = q.decide(q.specialize(coefficients, root, w))
    assert result["accepted"] is accepted


@pytest.mark.parametrize(
    "coefficients",
    [
        [(0, 0, -1), (0, 2), (-1,)],  # -(q-s)^2
        [(0, 0, -1), (0,), (0, 2), (0,), (-1,)],  # -(q^2-s)^2
        [(-1,), (0, 1)],  # leading-degree drop at s=0
        [(0,), (0, -1), (1,)],  # identically zero q=0 endpoint
    ],
)
def test_parametric_projection_retains_repeated_root_and_degree_guards(coefficients):
    w = Work()
    projection = q.projection(q.specialize(coefficients, None, w))
    assert not projection["zero"]
    assert projection["chain"]
    assert all(any(v for v in guard) for guard in projection["guards"])
    for s in (F(1, 4), F(3, 4)):
        root = Root((-s.numerator, s.denominator), s, s)
        actual = q.decide(q.specialize(coefficients, root, w))["accepted"]
        rational = tuple(p.evaluate(poly, s) for poly in coefficients)
        assert actual == p.threshold_decision(rational)


def test_two_quadratic_events_include_only_the_interior_tangency():
    w = Work()
    roots = isolate((1, -82, 1521), F(0), F(1), w)
    h = [(-F(1, 40),), (F(1, 40), F(39, 40)), (0, -1)]
    decisions = [q.decide(q.specialize(h, root, w)) for root in roots]
    assert [d["accepted"] for d in decisions] == [False, True]
    assert [d["root_count"] for d in decisions] == [0, 1]


def test_singleton_acceptance_at_an_irrational_effect():
    # H(s,q) = -(q-1/2)^2 -(s^2-1/2)^2. Its supremum is zero only
    # at s=sqrt(1/2), attained at q=1/2; all other effects are rejected.
    w = Work()
    h = [(-F(1, 2), 0, 1, 0, -1), (1,), (-1,)]
    projection = q.projection(q.specialize(h, None, w))
    event = isolate((-1, 0, 2), F(0), F(1), w)[0]
    assert any(sign_at(g, event, w) == 0 for g in projection["guards"])
    for s in (F(1, 4), F(3, 4)):
        point = Root((-s.numerator, s.denominator), s, s)
        assert q.decide(q.specialize(h, point, w))["accepted"] is False
    assert q.decide(q.specialize(h, event, w))["accepted"] is True


def test_zero_polynomial_and_wrong_field_are_distinct():
    w = Work()
    zero = q.specialize([(0,)], None, w)
    assert q.projection(zero)["zero"] is True
    with pytest.raises(ValueError, match="selected real effect"):
        q.decide(zero)
    with pytest.raises(ValueError, match="zero polynomial"):
        q.squarefree(zero)
    one = q.specialize([(1,)], None, w)
    with pytest.raises(ValueError, match="division by zero"):
        q.divide(one, zero)
    with pytest.raises(ArithmeticError, match="divide exactly"):
        q.exact_divide(one, q.specialize([(0,), (1,)], None, w))
    point = Root((0, 1), F(0), F(0))
    with pytest.raises(ValueError, match="projection requires"):
        q.projection(q.specialize([(1,)], point, w))


def test_field_context_and_resource_boundaries():
    w = Work()
    a = Element(None, (1,), (1,), w)
    for scalar in (True, 0.5, Element(None, (1,), (1,), Work())):
        with pytest.raises(ValueError):
            a + scalar
    with pytest.raises(ValueError, match="selected effect"):
        a.sign()
    with pytest.raises(ValueError, match="natural number"):
        a**-1
    assert not (a**3 - 1)
    with pytest.raises(ValueError, match="at least one"):
        q.trim([])
    limited = Work(Limits(max_degree=1))
    one = Element(None, (1,), (1,), limited)
    with pytest.raises(p.OracleLimitError, match="degree budget"):
        q.trim([one, one, one])
    with pytest.raises(p.OracleLimitError, match="degree budget"):
        q.mul((one, one), (one, one))
    assert q.iszero(q.mul(q.specialize([(0,)], None, w), (a,)))
    with pytest.raises(ValueError, match="increasing Fraction"):
        isolate((0, 1), F(1), F(0), w)
    assert isolate((1,), F(0), F(1), w) == ()
    point = Root((0, 1), F(0), F(0))
    with pytest.raises(ValueError, match="strictly ordered"):
        between(point, point, w)
    with pytest.raises(ValueError, match="exact Fractions"):
        Root((0, 1), 0, 1).verify(w)
    with pytest.raises(p.OracleLimitError, match="refinement budget"):
        narrow = Work(Limits(max_refinements=1))
        narrow.tick("refinement")
        narrow.tick("refinement")
