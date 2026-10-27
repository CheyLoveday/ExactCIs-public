"""Selected-embedding sign/order replay with the shared vector meter.

These are development components corresponding to SelectedRoot,
AlgebraicSignReplay.signCheck and RootComparison. No midpoint is substituted
for an algebraic value. Reducible/repeated definers are admitted when their
supplied isolator and identities replay. Parametric/global integration remains
separate; this module is not a complete global checker or a producer.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q

import metered_polynomial as p
import metered_root as r
import resource_model as v


@dataclass(frozen=True)
class Root:
    definer: p.P
    lower: Q
    upper: Q
    certificate: r.RootWitness


@dataclass(frozen=True)
class SignWitness:
    sign: int
    quotient: p.P
    remainder: p.P


@dataclass(frozen=True)
class Refinement:
    lower: Q
    upper: Q
    certificate: r.RootWitness


@dataclass(frozen=True)
class EqualWitness:
    common: Root
    left_quotient: p.P
    right_quotient: p.P


@dataclass(frozen=True)
class OrderWitness:
    left: Refinement
    right: Refinement
    sign: int  # -1: left root < right root, +1: left root > right root


def _event(m: r.Meter) -> None:
    m.resources.charge(
        v.Event.ALGEBRAIC_COMPARE,
        v.CostVector(algebraic_comparisons=1),
        phase="selected_embedding",
    )


def check_root(root: Root, m: r.Meter) -> None:
    if type(root) is not Root:
        raise r.InvalidWitness("a selected-root record is required")
    if type(root.lower) is not Q or type(root.upper) is not Q:
        raise r.InvalidWitness("exact rational isolator endpoints required")
    h = p.canonical(root.definer, m)
    if m.compare(root.lower, root.upper) >= 0:
        raise r.InvalidWitness("a strict open isolator is required")
    if not m.compare(p.value(h, root.lower, m), Q(0)) or not m.compare(
        p.value(h, root.upper, m), Q(0)
    ):
        raise r.InvalidWitness("isolator endpoints must not be roots")
    if r.count_with_meter(h, root.certificate, m, root.lower, root.upper) != 1:
        raise r.InvalidWitness("isolator must contain exactly one distinct root")


def bounds(poly: p.P, lower: Q, upper: Q, m: r.Meter) -> tuple[Q, Q]:
    """The exact nonnegative-chart Horner bounds used by RootCertificate."""
    if m.compare(lower, Q(0)) < 0 or m.compare(lower, upper) > 0:
        raise r.InvalidWitness("nonnegative ordered interval required")
    coefficients = m.poly(poly)
    lo = hi = Q(0)
    for coefficient in reversed(coefficients):
        m.structural()
        a, b = m.mul(lower, lo), m.mul(upper, lo)
        c, d = m.mul(lower, hi), m.mul(upper, hi)
        lo = m.add(coefficient, a if m.compare(a, b) <= 0 else b)
        hi = m.add(coefficient, c if m.compare(c, d) >= 0 else d)
    return lo, hi


def sign_at(root: Root, poly: p.P, witness: SignWitness, m: r.Meter) -> int:
    _event(m)
    check_root(root, m)
    if type(witness) is not SignWitness or type(witness.sign) is not int:
        raise r.InvalidWitness("an exact sign witness is required")
    if witness.sign not in (-1, 0, 1):
        raise r.InvalidWitness("invalid sign tag")
    original = p.canonical(poly, m)
    quotient, remainder = p.canonical(witness.quotient, m), p.canonical(
        witness.remainder, m
    )
    product = p.mul(root.definer, quotient, m)
    if witness.sign == 0:
        # The frozen zero branch does not inspect a remainder. It establishes
        # actual divisibility, rather than zero at an isolator midpoint.
        if not p.equal(original, product, m):
            raise r.InvalidWitness("selected zero identity failed")
    else:
        signed = original if witness.sign == 1 else p.scale(Q(-1), original, m)
        if not p.equal(signed, p.add(product, remainder, m), m):
            raise r.InvalidWitness("selected sign identity failed")
        if m.compare(bounds(remainder, root.lower, root.upper, m)[0], Q(0)) <= 0:
            raise r.InvalidWitness("strict remainder sign is not established")
    return witness.sign


def _refinement(root: Root, refinement: Refinement, m: r.Meter) -> Root:
    if type(refinement) is not Refinement:
        raise r.InvalidWitness("a refinement record is required")
    result = Root(
        root.definer, refinement.lower, refinement.upper, refinement.certificate
    )
    check_root(result, m)
    if (
        m.compare(root.lower, refinement.lower) >= 0
        or m.compare(refinement.upper, root.upper) >= 0
    ):
        raise r.InvalidWitness(
            "strict refinement inside the original isolator required"
        )
    return result


def compare(
    left: Root, right: Root, witness: EqualWitness | OrderWitness, m: r.Meter
) -> int:
    _event(m)
    check_root(left, m)
    check_root(right, m)
    if type(witness) is EqualWitness:
        common = witness.common
        check_root(common, m)
        for root, quotient in (
            (left, witness.left_quotient),
            (right, witness.right_quotient),
        ):
            m.structural()
            if (
                m.compare(root.lower, common.lower) >= 0
                or m.compare(common.upper, root.upper) >= 0
            ):
                raise r.InvalidWitness("common root must lie inside both isolators")
            if not p.equal(
                root.definer, p.mul(common.definer, p.canonical(quotient, m), m), m
            ):
                raise r.InvalidWitness("common-definer divisibility failed")
        return 0
    if type(witness) is not OrderWitness or type(witness.sign) is not int:
        raise r.InvalidWitness("a checked equality/order witness is required")
    if witness.sign not in (-1, 1):
        raise r.InvalidWitness("strict order tag required")
    a, b = _refinement(left, witness.left, m), _refinement(right, witness.right, m)
    if witness.sign == 1:
        a, b = b, a
    if m.compare(a.upper, b.lower) > 0:
        raise r.InvalidWitness("refined isolators do not establish strict order")
    return witness.sign
