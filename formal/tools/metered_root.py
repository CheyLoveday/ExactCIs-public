"""Deterministic rational root witnesses with work charged before arithmetic.

This is a formal-development reference, not the production fixed-null/global
engine. Root-check units count replay attempts; polynomial units count actual
Fraction +-*/ primitives. Total work adds cumulative reserved coefficient slots
to those two counters and is checked before each action.
No JSON parser, global certificate producer or Python execution proof is claimed.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q

import metered_polynomial as p
import resource_model as resource

P = p.P
ZERO: P = ()
ONE: P = (Q(1),)


class InvalidWitness(ValueError):
    """Data or a polynomial identity does not justify a decision."""


@dataclass(frozen=True)
class Limits:
    arithmetic: p.MeterLimits = p.MeterLimits()
    root_checks: int = 1000
    total_work: int = 2_000_000
    profile: resource.ResourceProfile = resource.DEVELOPMENT

    def __post_init__(self) -> None:
        if type(self.arithmetic) is not p.MeterLimits:
            raise ValueError("arithmetic limits must be a MeterLimits instance")
        if type(self.profile) is not resource.ResourceProfile:
            raise ValueError("a versioned resource profile is required")
        if any(
            type(v) is not int or v < 0 for v in (self.root_checks, self.total_work)
        ):
            raise ValueError("root and total budgets must be nonnegative integers")


@dataclass(frozen=True)
class State:
    arithmetic: p.MeterState
    root_checks: int
    total_work: int
    resources: resource.Snapshot


class BudgetRefusal(RuntimeError):
    def __init__(self, limit: str, operation: str, requested: int, state: State):
        super().__init__(
            f"{limit} refused before {operation}: requested {p.requested_text(requested)}"
        )
        self.limit = limit
        self.operation = operation
        self.requested = requested
        self.state = state


class Meter(p.Meter):
    def __init__(
        self, limits: Limits = Limits(), *, resources: resource.Meter | None = None
    ):
        if type(limits) is not Limits:
            raise ValueError("limits must be a Limits instance")
        if resources is not None and resources.profile != limits.profile:
            raise ValueError("root and shared-meter profiles must agree")
        super().__init__(
            limits.arithmetic,
            resources=(
                resource.Meter(limits.profile) if resources is None else resources
            ),
        )
        self.policy = limits
        self.root_checks = 0

    def root_state(self) -> State:
        return State(
            self.snapshot(),
            self.root_checks,
            self.operations + self.coefficients + self.root_checks,
            self.resources.snapshot(),
        )

    def charge_operation(self, operation: str) -> None:
        requested = self.root_state().total_work + 1
        if requested > self.policy.total_work:
            raise BudgetRefusal("totalWork", operation, requested, self.root_state())
        super().charge_operation(operation)

    def reserve(self, count: int, *, operation: str) -> None:
        if type(count) is not int or count < 0:
            raise ValueError("slot reservation must be a nonnegative integer")
        requested = self.root_state().total_work + count
        if requested > self.policy.total_work:
            raise BudgetRefusal("totalWork", operation, requested, self.root_state())
        super().reserve(count, operation=operation)

    def charge_root(self) -> None:
        requested = self.root_checks + 1
        if requested > self.policy.root_checks:
            raise BudgetRefusal(
                "rootChecks", "root replay", requested, self.root_state()
            )
        total = self.root_state().total_work + 1
        if total > self.policy.total_work:
            raise BudgetRefusal("totalWork", "root replay", total, self.root_state())
        self.root_step()
        self.root_checks = requested

    def root_step(self) -> None:
        self.resources.charge(
            resource.Event.ROOT_STEP,
            resource.CostVector(root_replay_steps=1),
            phase="root_replay",
        )


@dataclass(frozen=True)
class RootWitness:
    representative: P
    quotient: P
    power_quotient: P
    exponent: int
    bezout_left: P
    bezout_right: P
    tail: tuple[P, ...]
    quotients: tuple[P, ...]
    last: Q


@dataclass(frozen=True)
class Certificate:
    """The polynomial and interval are bound by the replay caller, never a flag."""

    root: RootWitness | None


@dataclass(frozen=True)
class Decision:
    accepted: bool
    roots_ioc: int | None
    state: State


def _wrap_resource(exc: p.ResourceLimit, m: Meter) -> BudgetRefusal:
    return BudgetRefusal(exc.limit, exc.operation, exc.requested, m.root_state())


def _inputs(coefficients: P, a: Q, b: Q, m: Meter) -> P:
    if type(a) is not Q or type(b) is not Q:
        raise InvalidWitness("ordered explicit Fraction endpoints are required")
    # Check even endpoints not reached by Horner evaluation (including zero).
    m.check(a)
    m.check(b)
    if m.sub(a, b).numerator > 0:
        raise InvalidWitness("ordered explicit Fraction endpoints are required")
    return m.poly(coefficients)


def _canonical(poly: P, m: Meter) -> P:
    if type(poly) is not tuple:
        raise InvalidWitness("a witness polynomial must be a tuple of Fractions")
    m.size(len(poly), operation="witness polynomial")
    if any(type(c) is not Q for c in poly):
        raise InvalidWitness("a witness polynomial must be a tuple of Fractions")
    checked = m.poly(poly)
    if len(checked) != len(poly):
        raise InvalidWitness("witness polynomial has trailing zero slots")
    return checked


def _validate(c: RootWitness, m: Meter) -> None:
    if type(c) is not RootWitness:
        raise InvalidWitness("a RootWitness record is required")
    if type(c.exponent) is not int or c.exponent <= 0:
        raise InvalidWitness("positive integer root transport exponent required")
    if c.exponent > m.limits.max_exponent:
        m.refuse("exponent", operation="root transport", requested=c.exponent)
    if type(c.last) is not Q:
        raise InvalidWitness("exact rational chain terminator required")
    for poly in (
        c.representative,
        c.quotient,
        c.power_quotient,
        c.bezout_left,
        c.bezout_right,
    ):
        _canonical(poly, m)
    for chain in (c.tail, c.quotients):
        if type(chain) is not tuple:
            raise InvalidWitness("immutable tuple chain required")
        if len(chain) > m.limits.max_degree + 1:
            m.refuse(
                "chainLength", operation="root witness validation", requested=len(chain)
            )
        for poly in chain:
            _canonical(poly, m)
    m.check(c.last)


def _generate_root(h: P, m: Meter) -> RootWitness:
    if not h:
        raise InvalidWitness("zero polynomial uses the endpoint branch")
    gcd, _, _ = p.xgcd(h, p.derivative(h, m), m)
    representative = p.exact_divide(h, gcd, m)
    representative = p.scale(m.div(Q(1), representative[-1]), representative, m)
    quotient = p.exact_divide(h, representative, m)
    current = ONE
    power_quotient = ZERO
    for exponent in range(1, min(max(1, len(h) - 1), m.limits.max_exponent) + 1):
        current = p.mul(current, representative, m)
        power_quotient, remainder = p.divide(current, h, m)
        if not remainder:
            break
    else:
        m.refuse("exponent", operation="root witness generation", requested=len(h) - 1)
        raise AssertionError("refusal must raise")
    derivative = p.derivative(representative, m)
    gcd, left, right = p.xgcd(representative, derivative, m)
    if not p.equal(gcd, ONE, m):
        raise InvalidWitness("generated representative is not squarefree")
    tail: list[P] = []
    quotients: list[P] = []
    previous = representative
    last = previous
    if derivative:
        tail.append(derivative)
        previous, last = representative, derivative
        while len(last) > 1:
            q, remainder = p.divide(previous, last, m)
            if not remainder:
                raise InvalidWitness(
                    "generated Sturm chain has nonconstant zero remainder"
                )
            next_poly = p.scale(Q(-1), remainder, m)
            quotients.append(q)
            tail.append(next_poly)
            previous, last = last, next_poly
    return RootWitness(
        representative,
        quotient,
        power_quotient,
        exponent,
        left,
        right,
        tuple(tail),
        tuple(quotients),
        last[0],
    )


def _variations(chain: tuple[P, ...], x: Q, m: Meter) -> int:
    previous = 0
    changes = 0
    for poly in chain:
        m.root_step()
        y = p.value(poly, x, m)
        sign = m.compare(y, Q(0))
        if sign:
            changes += int(previous != 0 and previous != sign)
            previous = sign
    return changes


def _check_root(h: P, c: RootWitness, a: Q, b: Q, m: Meter) -> int:
    # This is an actual replay attempt, charged before any identity arithmetic.
    m.charge_root()
    _validate(c, m)
    s = c.representative
    if not p.equal(p.mul(s, c.quotient, m), h, m):
        raise InvalidWitness("H=S*Q identity failed")
    if not p.equal(p.power(s, c.exponent, m), p.mul(h, c.power_quotient, m), m):
        raise InvalidWitness("S^m=H*T identity failed")
    derivative = p.derivative(s, m)
    if not p.equal(
        p.add(p.mul(c.bezout_left, s, m), p.mul(c.bezout_right, derivative, m), m),
        ONE,
        m,
    ):
        raise InvalidWitness("Bezout identity failed")
    chain = (s,) + c.tail
    if c.tail and not p.equal(c.tail[0], derivative, m):
        raise InvalidWitness("chain does not start with the actual derivative")
    if (
        m.compare(c.last, Q(0)) == 0
        or len(chain[-1]) != 1
        or m.compare(chain[-1][0], c.last)
    ):
        raise InvalidWitness("nonzero constant chain terminator required")
    if len(c.quotients) != max(0, len(chain) - 2):
        raise InvalidWitness("recurrence quotient count mismatch")
    for left, middle, right, quotient in zip(chain, chain[1:], chain[2:], c.quotients):
        m.root_step()
        if not p.equal(
            left, p.add(p.mul(middle, quotient, m), p.scale(Q(-1), right, m), m), m
        ):
            raise InvalidWitness("signed PRS recurrence failed")
    left_variation, right_variation = _variations(chain, a, m), _variations(chain, b, m)
    if left_variation < right_variation:
        raise InvalidWitness("negative root count")
    return left_variation - right_variation


def _replay(h: P, a: Q, b: Q, certificate: Certificate, m: Meter) -> Decision:
    if type(certificate) is not Certificate:
        raise InvalidWitness("a Certificate record is required")
    if m.compare(p.value(h, a, m), Q(0)) >= 0:
        if certificate.root is not None:
            raise InvalidWitness("unused root witness on the endpoint branch")
        return Decision(True, None, m.root_state())
    if certificate.root is None:
        raise InvalidWitness("negative endpoint requires a root witness")
    roots = _check_root(h, certificate.root, a, b, m)
    return Decision(roots > 0, roots, m.root_state())


def replay(
    coefficients: P,
    certificate: Certificate,
    a: Q = Q(0),
    b: Q = Q(1),
    *,
    limits: Limits = Limits(),
) -> Decision:
    """Check identities only: replay never invokes gcd, division or generation."""
    return replay_with_meter(coefficients, certificate, Meter(limits), a, b)


def count_with_meter(
    coefficients: P, witness: RootWitness, m: Meter, a: Q, b: Q
) -> int:
    """Replay a complete squarefree/PRS witness and count distinct roots in (a,b]."""
    try:
        return _check_root(_inputs(coefficients, a, b, m), witness, a, b, m)
    except p.ResourceLimit as exc:
        raise _wrap_resource(exc, m) from exc


def generate_witness_with_meter(coefficients: P, m: Meter) -> RootWitness:
    """Generate root-set/PRS data even when a decision's endpoint branch is trivial."""
    try:
        return _generate_root(p.canonical(coefficients, m), m)
    except p.ResourceLimit as exc:
        raise _wrap_resource(exc, m) from exc


def replay_with_meter(
    coefficients: P, certificate: Certificate, m: Meter, a: Q = Q(0), b: Q = Q(1)
) -> Decision:
    """Continue one cumulative meter, without resetting caller work."""
    if type(m) is not Meter:
        raise ValueError("an exact root Meter instance is required")
    try:
        return _replay(_inputs(coefficients, a, b, m), a, b, certificate, m)
    except p.ResourceLimit as exc:
        raise _wrap_resource(exc, m) from exc


def generate(
    coefficients: P, a: Q = Q(0), b: Q = Q(1), *, limits: Limits = Limits()
) -> tuple[Certificate, Decision]:
    """Generation and final identity replay share one cumulative work meter."""
    return generate_with_meter(coefficients, Meter(limits), a, b)


def generate_with_meter(
    coefficients: P, m: Meter, a: Q = Q(0), b: Q = Q(1)
) -> tuple[Certificate, Decision]:
    """Continue a coefficient/ordering pipeline's meter through final replay."""
    if type(m) is not Meter:
        raise ValueError("an exact root Meter instance is required")
    try:
        h = _inputs(coefficients, a, b, m)
        certificate = Certificate(
            None if m.compare(p.value(h, a, m), Q(0)) >= 0 else _generate_root(h, m)
        )
        return certificate, _replay(h, a, b, certificate, m)
    except p.ResourceLimit as exc:
        raise _wrap_resource(exc, m) from exc
