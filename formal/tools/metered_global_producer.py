"""Deterministic frozen-v1 global Boschloo certificate construction.

This development producer emits a candidate, never a statistical result.
The separate literal-byte checker must replay the complete candidate before
any result is exposed. All construction, failed refinements, identities,
root isolation and serialization use the supplied shared resource meter.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from typing import Any, cast

import metered_algebraic as a
import metered_boschloo_polynomials as b
import metered_global_geometry as g
import metered_isolate as isolation
import metered_parametric as f
import metered_polynomial as p
import metered_root as r
import metered_selected_refinement as local
import metered_specialized as specialized
import resource_model as v


def rational(q: Q, m: r.Meter) -> dict[str, str]:
    m.check(q)
    m.integer_step(max(q.numerator.bit_length(), q.denominator.bit_length()))
    m.structural(2)
    return {"numerator": str(q.numerator), "denominator": str(q.denominator)}


def polynomial(poly: p.P, m: r.Meter) -> list[dict[str, str]]:
    m.structural(len(poly))
    return [rational(coefficient, m) for coefficient in poly]


def bivariate(poly: f.B, m: r.Meter) -> list[list[dict[str, str]]]:
    m.structural(len(poly))
    return [polynomial(row, m) for row in poly]


def root_certificate(c: r.RootWitness, m: r.Meter) -> dict[str, Any]:
    m.structural(10 + len(c.tail) + len(c.quotients))
    return dict(
        representative=polynomial(c.representative, m),
        quotient=polynomial(c.quotient, m),
        powerQuotient=polynomial(c.power_quotient, m),
        exponent=str(c.exponent),
        bezoutLeft=polynomial(c.bezout_left, m),
        bezoutRight=polynomial(c.bezout_right, m),
        tail=[polynomial(poly, m) for poly in c.tail],
        quotients=[polynomial(poly, m) for poly in c.quotients],
        last=rational(c.last, m),
    )


def point_wire(point: g.Point, m: r.Meter) -> dict[str, Any]:
    m.structural(2)
    if type(point) is Q:
        return dict(kind="rational", value=rational(point, m))
    point = cast(a.Root, point)
    return dict(
        kind="algebraic",
        value=dict(
            definer=polynomial(point.definer, m),
            lower=rational(point.lower, m),
            upper=rational(point.upper, m),
            certificate=root_certificate(point.certificate, m),
        ),
    )


def sign_wire(witness: a.SignWitness | None, m: r.Meter) -> dict[str, Any]:
    m.structural()
    if witness is None:
        return {"kind": "rational"}
    return dict(
        kind="algebraic",
        witness=dict(
            sign=witness.sign,
            quotient=polynomial(witness.quotient, m),
            remainder=polynomial(witness.remainder, m),
        ),
    )


@dataclass(frozen=True)
class Cover:
    polynomial: p.P
    certificate: r.RootWitness


@dataclass
class PointData:
    point: g.Point
    polynomials: tuple[p.P, ...]
    signs: tuple[int, ...]
    witnesses: tuple[a.SignWitness | None, ...]
    leaf: dict[str, Any] | None = None

    def lookup(self, poly: p.P, m: r.Meter) -> tuple[int, dict[str, Any]]:
        poly = m.poly(poly)
        for i, candidate in enumerate(self.polynomials):
            m.structural()
            if p.equal(poly, candidate, m):
                return self.signs[i], sign_wire(self.witnesses[i], m)
        raise r.InvalidWitness(
            "a point sign query was absent from the finite query family"
        )


def _signs(point: g.Point, family: tuple[p.P, ...], m: r.Meter) -> PointData:
    if type(point) is Q:
        m.structural(len(family))
        signs = tuple(m.compare(p.value(poly, point, m), Q(0)) for poly in family)
        return PointData(point, family, signs, (None,) * len(family))
    result = local.localize(cast(a.Root, point), family, m)
    return PointData(result.point, family, result.signs, result.witnesses)


def _variations(signs: tuple[int, ...], m: r.Meter) -> int:
    previous = 0
    changes = 0
    for sign in signs:
        m.structural()
        if sign:
            if previous and sign != previous:
                m.integer_step()
                changes += 1
            previous = sign
    return changes


def _leaf(
    greater: tuple[bool, dict[str, Any]], less: tuple[bool, dict[str, Any]], m: r.Meter
) -> dict[str, Any]:
    m.resources.charge(
        v.Event.LEAF_TRANSITION,
        v.CostVector(leaf_or_cell_transitions=1),
        phase="classification",
    )
    if not greater[0]:
        return dict(state="REJECTED_GREATER", greater=greater[1], less=None)
    if not less[0]:
        return dict(state="REJECTED_LESS", greater=None, less=less[1])
    return dict(state="ACCEPTED", greater=greater[1], less=less[1])


def _specialized_wire(c: specialized.Certificate, m: r.Meter) -> dict[str, Any]:
    def modular_witness(poly: f.B) -> list[list[dict[str, str]]]:
        # The frozen wire grammar has canonical outer coefficient arrays.
        # The decoder restores omitted zero rows only for modular witnesses,
        # using each reconstructed identity's exact raw width. Typed witness
        # arrays themselves retain all rows required by zeroCheck.
        stop = len(poly)
        while stop:
            m.structural()
            if poly[stop - 1]:
                break
            stop -= 1
        m.reserve(stop, operation="canonical modular witness outer-row copy")
        m.structural(stop)
        return bivariate(poly[:stop], m)

    m.structural(16 + len(c.tail) + len(c.quotients) + len(c.witnesses))
    return dict(
        representative=bivariate(c.representative, m),
        quotient=bivariate(c.quotient, m),
        powerQuotient=bivariate(c.power_quotient, m),
        exponent=str(c.exponent),
        rootWitness=modular_witness(c.root_witness),
        powerWitness=modular_witness(c.power_witness),
        bezoutLeft=bivariate(c.bezout_left, m),
        bezoutRight=bivariate(c.bezout_right, m),
        bezoutWitness=modular_witness(c.bezout_witness),
        tail=[bivariate(x, m) for x in c.tail],
        quotients=[bivariate(x, m) for x in c.quotients],
        witnesses=[modular_witness(x) for x in c.witnesses],
        last=polynomial(c.last, m),
        lastInverse=polynomial(c.last_inverse, m),
        lastQuotient=polynomial(c.last_quotient, m),
        derivativeWitness=modular_witness(c.derivative_witness),
    )


def _point_data(
    point: g.Point,
    model: b.Model,
    comparisons: dict[str, tuple[p.P, ...]],
    base: tuple[p.P, ...],
    m: r.Meter,
) -> PointData:
    current = point
    while True:
        m.structural()
        data = _signs(current, base, m)
        current = data.point
        packets: dict[str, specialized.Certificate | r.RootWitness | None] = {}
        masks: dict[str, tuple[bool, ...]] = {}
        objectives: dict[str, f.B] = {}
        query_list = list(base)
        restart = False
        for direction in ("greater", "less"):
            m.structural()
            mask = tuple(
                data.lookup(poly, m)[0] <= 0 for poly in comparisons[direction]
            )
            masks[direction] = mask
            if all(mask) or model.level == 0:
                packets[direction] = None
                continue
            h = model.objective(mask)
            objectives[direction] = h
            if type(current) is Q:
                m.reserve(len(h), operation="rational singleton specialization")
                coefficients = m.poly(tuple(p.value(row, current, m) for row in h))
                packets[direction] = r.generate_witness_with_meter(coefficients, m)
            else:
                current = cast(a.Root, current)
                next_point, specialized_certificate = specialized.generate(
                    h, current, m
                )
                if not p.equal(next_point.definer, current.definer, m):
                    current = next_point
                    restart = True
                    break
                current = next_point
                packets[direction] = specialized_certificate
                for poly in (
                    h,
                    *[
                        specialized_certificate.representative,
                        *specialized_certificate.tail,
                    ],
                ):
                    m.structural(2)
                    query_list.extend(
                        (f.at_rational(poly, Q(0), m), f.at_rational(poly, Q(1), m))
                    )
        if restart:
            continue
        queries = f.signed_family(tuple(query_list), m)
        # Zero is queried explicitly too, because identity-zero guard polynomials
        # do not belong to the finite nonzero projection family.
        m.structural()
        queries = ((), *queries)
        final = _signs(current, queries, m)
        if type(current) is not Q and (
            type(final.point) is Q
            or not p.equal(
                cast(a.Root, final.point).definer, cast(a.Root, current).definer, m
            )
        ):
            current = final.point
            continue
        current = final.point
        decisions: list[tuple[bool, dict[str, Any]]] = []
        for direction in ("greater", "less"):
            m.structural()
            ordering = [final.lookup(poly, m)[1] for poly in comparisons[direction]]
            mask = masks[direction]
            if all(mask) or model.level == 0:
                decisions.append(
                    (
                        True,
                        dict(
                            kind="full_mask" if all(mask) else "zero_level",
                            direction=direction,
                            ordering=ordering,
                        ),
                    )
                )
                continue
            h = objectives[direction]
            certificate = packets[direction]
            if type(current) is Q:
                if not isinstance(certificate, r.RootWitness):
                    raise r.InvalidWitness(
                        "rational singleton lacked its root certificate"
                    )
                coefficients = m.poly(tuple(p.value(row, current, m) for row in h))
                if (
                    m.compare(p.value(coefficients, Q(0), m), Q(0)) >= 0
                    or m.compare(p.value(coefficients, Q(1), m), Q(0)) >= 0
                ):
                    raise r.InvalidWitness(
                        "proper Boschloo singleton lacked negative nuisance endpoints"
                    )
                count = r.count_with_meter(coefficients, certificate, m, Q(0), Q(1))
                decisions.append(
                    (
                        count > 0,
                        dict(
                            kind="rational_root",
                            direction=direction,
                            ordering=ordering,
                            root=root_certificate(certificate, m),
                        ),
                    )
                )
            else:
                if not isinstance(certificate, specialized.Certificate):
                    raise r.InvalidWitness(
                        "algebraic singleton lacked its root certificate"
                    )
                left = tuple(
                    final.lookup(f.at_rational(poly, Q(0), m), m)
                    for poly in (certificate.representative, *certificate.tail)
                )
                right = tuple(
                    final.lookup(f.at_rational(poly, Q(1), m), m)
                    for poly in (certificate.representative, *certificate.tail)
                )
                original = final.lookup(f.at_rational(h, Q(0), m), m)
                if original[0] != -1:
                    raise r.InvalidWitness(
                        "proper algebraic singleton lacked a negative left endpoint"
                    )
                count = _variations(tuple(x[0] for x in left), m) - _variations(
                    tuple(x[0] for x in right), m
                )
                decisions.append(
                    (
                        count > 0,
                        dict(
                            kind="algebraic_root",
                            direction=direction,
                            ordering=ordering,
                            original=original[1],
                            root=_specialized_wire(certificate, m),
                            left=[x[1] for x in left],
                            right=[x[1] for x in right],
                        ),
                    )
                )
        final.leaf = _leaf(decisions[0], decisions[1], m)
        return final


def _cover(poly: p.P, covers: tuple[Cover, ...], m: r.Meter) -> Cover:
    for cover in covers:
        m.structural()
        if p.equal(poly, cover.polynomial, m):
            return cover
    raise r.InvalidWitness(
        "an open-cell guard was absent from the closed projection family"
    )


def _family_roots(family: tuple[p.P, ...], m: r.Meter) -> tuple[g.Point, ...]:
    """Isolate one exact signed product in the frozen family order."""
    product = p.ONE
    for poly in family:
        m.structural()
        product = p.mul(product, poly, m)
    return isolation.isolate(product, m)


def _merged_family_roots(family: tuple[p.P, ...], m: r.Meter) -> tuple[g.Point, ...]:
    """Isolate each signed member, then merge equal selected real roots exactly.

    This executable reference route avoids multiplying the whole family into
    one high-degree polynomial. Result admission still requires full replay of
    every cover and the complete resulting partition by the independent checker.
    The product route remains the default for the general proof workstream.
    """
    roots: list[g.Point] = []
    for poly in family:
        m.structural()
        part = isolation.isolate(poly, m)
        m.reserve(len(roots) + len(part), operation="family root-list allocation")
        m.structural(len(part))
        roots.extend(part)
    m.structural(len(roots))
    return g.merge_sort(tuple(roots), m)


def _open_sign(
    poly: p.P,
    left: PointData,
    right: PointData,
    sample: Q,
    covers: tuple[Cover, ...],
    m: r.Meter,
) -> tuple[int, dict[str, Any]]:
    poly = m.poly(poly)
    if not poly:
        m.structural()
        return 0, {"kind": "identity_zero"}
    cover = _cover(poly, covers, m)
    sign = m.compare(p.value(poly, sample, m), Q(0))
    if not sign:
        raise r.InvalidWitness(
            "a nonzero guard vanished inside an allegedly root-free open cell"
        )
    chain = (cover.certificate.representative, *cover.certificate.tail)
    ls = tuple(left.lookup(coefficient, m) for coefficient in chain)
    rs = tuple(right.lookup(coefficient, m) for coefficient in chain)
    count = _variations(tuple(x[0] for x in ls), m) - _variations(
        tuple(x[0] for x in rs), m
    )
    m.integer_step()
    count -= int(rs[0][0] == 0)
    if count != 0:
        raise r.InvalidWitness("an open-cell sign guard still had an internal root")
    m.structural(6 + len(ls) + len(rs))
    return sign, dict(
        kind="root_free",
        sign=sign,
        certificate=root_certificate(cover.certificate, m),
        leftSigns=[x[1] for x in ls],
        rightSigns=[x[1] for x in rs],
        sample=rational(sample, m),
    )


def _open_decision(
    direction: str,
    model: b.Model,
    comparisons: tuple[p.P, ...],
    left: PointData,
    right: PointData,
    sample: Q,
    covers: tuple[Cover, ...],
    skeletons: list[tuple[str, tuple[bool, ...], f.B, f.Skeleton]],
    m: r.Meter,
) -> tuple[bool, dict[str, Any]]:
    ordering_signs = tuple(
        _open_sign(poly, left, right, sample, covers, m) for poly in comparisons
    )
    mask = tuple(value[0] <= 0 for value in ordering_signs)
    ordering = [value[1] for value in ordering_signs]
    if all(mask) or model.level == 0:
        return True, dict(
            kind="full_mask" if all(mask) else "zero_level",
            direction=direction,
            ordering=ordering,
        )
    selected = None
    for candidate_direction, candidate_mask, h, c in skeletons:
        m.structural(len(mask))
        if candidate_direction == direction and candidate_mask == mask:
            selected = h, c
            break
    if selected is None:
        raise r.InvalidWitness(
            "projection refinement introduced a previously unrealized comparison mask"
        )
    h, c = selected

    def sign(poly: p.P) -> tuple[int, dict[str, Any]]:
        return _open_sign(poly, left, right, sample, covers, m)

    original_left, original_right = sign(f.at_rational(h, Q(0), m)), sign(
        f.at_rational(h, Q(1), m)
    )
    if original_left[0] != -1 or original_right[0] != -1:
        raise r.InvalidWitness(
            "proper Boschloo open objective lacked negative nuisance endpoints"
        )
    chain = (c.representative, *c.tail)
    ls = tuple(sign(f.at_rational(poly, Q(0), m)) for poly in chain)
    rs = tuple(sign(f.at_rational(poly, Q(1), m)) for poly in chain)
    steps = []
    for step in c.steps:
        guard = sign(step.scale)
        if guard[0] != 1:
            raise r.InvalidWitness(
                "converted Sturm scale was not positive on its open cell"
            )
        m.structural(3)
        steps.append(
            dict(
                quotient=bivariate(step.quotient, m),
                scale=polynomial(step.scale, m),
                guard=guard[1],
            )
        )
    root = dict(
        representative=bivariate(c.representative, m),
        quotient=bivariate(c.quotient, m),
        powerQuotient=bivariate(c.power_quotient, m),
        exponent=str(c.exponent),
        bezoutLeft=bivariate(c.bezout_left, m),
        bezoutRight=bivariate(c.bezout_right, m),
        rootScale=polynomial(c.root_scale, m),
        powerScale=polynomial(c.power_scale, m),
        bezoutScale=polynomial(c.bezout_scale, m),
        last=polynomial(c.last, m),
        rootGuard=sign(c.root_scale)[1],
        powerGuard=sign(c.power_scale)[1],
        bezoutGuard=sign(c.bezout_scale)[1],
        lastGuard=sign(c.last)[1],
        tail=[bivariate(poly, m) for poly in c.tail],
        steps=steps,
    )
    count = _variations(tuple(x[0] for x in ls), m) - _variations(
        tuple(x[0] for x in rs), m
    )
    m.structural(8 + len(ls) + len(rs))
    return count > 0, dict(
        kind="interior_root",
        direction=direction,
        ordering=ordering,
        originalLeft=original_left[1],
        originalRight=original_right[1],
        root=root,
        left=[x[1] for x in ls],
        right=[x[1] for x in rs],
    )


def _prepare(
    points: tuple[g.Point, ...], tolerance: Q, m: r.Meter
) -> tuple[g.Point, ...]:
    m.structural(len(points) + 2)
    values: list[g.Point] = [Q(0), *points, Q(1)]
    for i in range(len(values) - 1):
        m.structural()
        _, values[i], values[i + 1] = g.sample(values[i], values[i + 1], m)
    if m.compare(tolerance, Q(0)) > 0:
        for i in range(1, len(values) - 1):
            point = values[i]
            depth = 0
            while type(point) is not Q:
                point = cast(a.Root, point)
                m.structural()
                if (
                    m.compare(point.lower, Q(0)) > 0
                    and m.compare(point.upper, Q(1)) < 0
                ):
                    beta_lo = m.div(point.lower, m.sub(Q(1), point.lower))
                    beta_hi = m.div(point.upper, m.sub(Q(1), point.upper))
                    if m.compare(m.sub(beta_hi, beta_lo), tolerance) <= 0:
                        break
                point = g.refine(point, m)
                depth += 1
                m.resources.shape(
                    "refinement_depth", depth, phase="hull_endpoint_excess"
                )
            values[i] = point
    m.structural(len(points))
    return tuple(values[1:-1])


def _terminal(
    model: b.Model,
    points: tuple[PointData, ...],
    opens: list[dict[str, Any]],
    tolerance: Q,
    m: r.Meter,
) -> dict[str, Any]:
    a_count, _, c_count, _ = model.table
    zero = model.level == 0 or a_count == 0 or c_count == model.n0
    one = model.level == 0 or c_count == 0 or a_count == model.n1
    accepted_points = [
        i
        for i, data in enumerate(points)
        if cast(dict[str, object], data.leaf)["state"] == "ACCEPTED"
    ]
    accepted_opens = [i for i, leaf in enumerate(opens) if leaf["state"] == "ACCEPTED"]
    m.structural(len(points) + len(opens) + 2)
    if (
        zero
        and one
        and len(accepted_points) == len(points)
        and len(accepted_opens) == len(opens)
    ):
        return {"kind": "FULL_CERTIFIED"}
    if not zero and not one and not accepted_points and not accepted_opens:
        return {"kind": "EMPTY_CERTIFIED"}

    def finite(index: int) -> tuple[Q, Q, dict[str, Any]]:
        point = points[index].point
        lo, hi = g.lower(point), g.upper(point)
        if m.compare(lo, Q(0)) <= 0 or m.compare(hi, Q(1)) >= 0:
            raise r.InvalidWitness(
                "finite hull anchor did not have an internal enclosure"
            )
        excess = m.sub(m.div(hi, m.sub(Q(1), hi)), m.div(lo, m.sub(Q(1), lo)))
        if m.compare(excess, tolerance) > 0:
            raise r.BudgetRefusal(
                "endpointExcess",
                "finite algebraic report refinement",
                1,
                m.root_state(),
            )
        return (
            lo,
            hi,
            dict(
                kind="finite",
                anchor=dict(kind="point", index=str(index)),
                enclosureLower=rational(lo, m),
                enclosureUpper=rational(hi, m),
            ),
        )

    if zero:
        lo, lower = Q(0), dict(kind="structural", endpoint="zero")
    elif accepted_points:
        lo, _, lower = finite(accepted_points[0])
    elif one and not accepted_opens:
        lo, lower = Q(1), dict(kind="structural", endpoint="one")
    else:
        raise r.InvalidWitness("closed acceptance set lacked its finite lower anchor")
    if one:
        hi, upper = Q(1), dict(kind="structural", endpoint="one")
    elif accepted_points:
        _, hi, upper = finite(accepted_points[-1])
    elif zero and not accepted_opens:
        hi, upper = Q(0), dict(kind="structural", endpoint="zero")
    else:
        raise r.InvalidWitness("closed acceptance set lacked its finite upper anchor")
    return dict(
        kind="HULL_CERTIFIED",
        outerLower=rational(lo, m),
        outerUpper=rational(hi, m),
        lower=lower,
        upper=upper,
    )


@dataclass(frozen=True)
class Candidate:
    input: dict[str, Any]
    payload: dict[str, Any]
    construction: r.State
    checkpoints: tuple[tuple[str, r.State], ...] = ()


@dataclass(frozen=True)
class SerializedCandidate:
    input_bytes: bytes
    payload_bytes: bytes
    construction_and_serialization: r.State


def _serialize(value: Any, m: r.Meter) -> bytes:
    output = bytearray()

    def emit(piece: str) -> None:
        count = len(piece)
        m.resources.shape(
            "emitted_bytes", len(output) + count, phase="canonical_serialization"
        )
        m.resources.charge(
            v.Event.EMIT_BYTES,
            v.CostVector(certificate_bytes=count),
            phase="canonical_serialization",
        )
        output.extend(piece.encode("ascii"))

    def string(text: str) -> None:
        m.resources.shape("string_length", len(text), phase="canonical_serialization")
        emit('"')
        for character in text:
            m.structural()
            code = ord(character)
            if character in ('"', "\\"):
                emit("\\" + character)
            elif 32 <= code <= 126:
                emit(character)
            elif code < 128:
                emit("\\u" + format(code, "04x"))
            else:
                raise r.InvalidWitness("producer emitted a non-ASCII protocol string")
        emit('"')

    def visit(item: Any, depth: int) -> None:
        m.structural()
        m.resources.shape("nesting", depth, phase="canonical_serialization")
        if item is None:
            emit("null")
        elif type(item) is str:
            string(item)
        elif type(item) is int:
            m.integer_step(item.bit_length())
            emit(str(item))
        elif type(item) is list:
            m.resources.shape("list_items", len(item), phase="canonical_serialization")
            emit("[")
            for index, child in enumerate(item):
                m.structural()
                if index:
                    emit(",")
                visit(child, depth + 1)
            emit("]")
        elif type(item) is dict:
            m.resources.shape(
                "object_items", len(item), phase="canonical_serialization"
            )
            emit("{")
            for index, (key, child) in enumerate(item.items()):
                m.structural()
                if index:
                    emit(",")
                string(key)
                emit(":")
                visit(child, depth + 1)
            emit("}")
        else:
            raise r.InvalidWitness("producer emitted an unsupported JSON value")

    visit(value, 0)
    # Charge the immutable output copy before allocating it as well.
    m.resources.charge(
        v.Event.EMIT_BYTES,
        v.CostVector(certificate_bytes=len(output)),
        phase="canonical_serialization_copy",
    )
    return bytes(output)


def serialize(candidate: Candidate, m: r.Meter) -> SerializedCandidate:
    input_bytes = _serialize(candidate.input, m)
    payload_bytes = _serialize(candidate.payload, m)
    return SerializedCandidate(input_bytes, payload_bytes, m.root_state())


def generate(
    table: tuple[int, int, int, int],
    alpha: Q,
    tolerance: Q,
    m: r.Meter,
    *,
    isolation_strategy: str = "product",
) -> Candidate:
    checkpoints: list[tuple[str, r.State]] = []

    def checkpoint(phase: str) -> None:
        m.structural()
        checkpoints.append((phase, m.root_state()))

    if (
        type(alpha) is not Q
        or type(tolerance) is not Q
        or m.compare(tolerance, Q(0)) < 0
    ):
        raise r.InvalidWitness(
            "alpha and nonnegative endpoint-excess tolerance must be exact rationals"
        )
    if m.compare(alpha, Q(0)) < 0 or m.compare(alpha, Q(1)) > 0:
        raise r.InvalidWitness("alpha must lie in [0,1]")
    if isolation_strategy not in ("product", "merge"):
        raise r.InvalidWitness("unknown family root-isolation strategy")
    family_roots = (
        _family_roots if isolation_strategy == "product" else _merged_family_roots
    )
    model = b.Model(table, m.div(alpha, Q(2)), m)
    checkpoint("P0_exact_input")
    comparisons = {
        direction: model.comparisons(cast(b.Direction, direction))
        for direction in ("greater", "less")
    }
    all_comparisons = tuple(
        poly
        for i in range(len(model.outcomes))
        for poly in (comparisons["greater"][i], comparisons["less"][i])
    )
    comparison_family = f.signed_family(all_comparisons, m)
    initial = _prepare(family_roots(comparison_family, m), Q(0), m)
    checkpoint("P1_P2_comparison_chambers")
    skeletons: list[tuple[str, tuple[bool, ...], f.B, f.Skeleton]] = []
    guards = list(all_comparisons)
    boundaries = (Q(0), *initial, Q(1))
    for left_bound, right_bound in zip(boundaries, boundaries[1:]):
        sample, _, _ = g.sample(left_bound, right_bound, m)
        for direction in ("greater", "less"):
            mask = tuple(
                m.compare(p.value(poly, sample, m), Q(0)) <= 0
                for poly in comparisons[direction]
            )
            if all(mask) or model.level == 0:
                continue
            if any(
                d == direction and previous == mask for d, previous, _, _ in skeletons
            ):
                continue
            h = model.objective(mask)
            skeleton = f.generate(h, m)
            m.structural(4)
            skeletons.append((direction, mask, h, skeleton))
            guards.extend(f.guards(h, skeleton, m))
    checkpoint("P3_fixed_generic_skeletons")
    family = f.signed_family(tuple(guards), m)
    covers: list[Cover] = []
    query_list = list(family)
    for poly in family:
        m.resources.charge(
            v.Event.PROJECTION_POLYNOMIAL,
            v.CostVector(projection_polynomials=1),
            phase="projection",
        )
        certificate = r.generate_witness_with_meter(poly, m)
        covers.append(Cover(poly, certificate))
        query_list.extend((certificate.representative, *certificate.tail))
    points = _prepare(family_roots(family, m), tolerance, m)
    checkpoint("P4_projection_and_endpoint_refinement")
    base = ((), *f.signed_family(tuple(query_list), m))
    data = tuple(_point_data(point, model, comparisons, base, m) for point in points)
    checkpoint("P5_inclusive_singletons")
    endpoints = (_signs(Q(0), base, m), *data, _signs(Q(1), base, m))
    cover_tuple = tuple(covers)
    opens = []
    for left, right in zip(endpoints, endpoints[1:]):
        sample, narrowed_left, narrowed_right = g.sample(left.point, right.point, m)
        if narrowed_left != left.point or narrowed_right != right.point:
            raise r.InvalidWitness(
                "point packet assembly invalidated a prepared chart sample"
            )
        greater = _open_decision(
            "greater",
            model,
            comparisons["greater"],
            left,
            right,
            sample,
            cover_tuple,
            skeletons,
            m,
        )
        less = _open_decision(
            "less",
            model,
            comparisons["less"],
            left,
            right,
            sample,
            cover_tuple,
            skeletons,
            m,
        )
        opens.append(_leaf(greater, less, m))
    checkpoint("P6_P7_whole_open_cells")
    cover_wire = []
    for cover in covers:
        members = []
        for index, point in enumerate(data):
            sign, witness = point.lookup(cover.polynomial, m)
            if not sign:
                m.structural(2)
                members.append(dict(point=str(index), zero=witness))
        if isolation.open_count(
            cover.polynomial, cover.certificate, Q(0), Q(1), m
        ) != len(members):
            raise r.InvalidWitness(
                "complete projection cover failed its distinct-root cardinality check"
            )
        cover_wire.append(
            dict(
                polynomial=polynomial(cover.polynomial, m),
                certificate=root_certificate(cover.certificate, m),
                members=members,
            )
        )
    terminal = _terminal(model, data, opens, tolerance, m)
    checkpoint("P8_complete_covers_and_global_T1")
    profile = m.resources.profile
    limits = dict(
        payloadBytes=str(profile.shapes.payload_bytes),
        integerDigits=str(profile.shapes.integer_digits),
        polynomialDegree=str(profile.limits.maximum_polynomial_degree),
        polynomialOps=str(profile.limits.rational_operations),
        rootChecks=str(profile.limits.root_replay_steps),
        algebraicComparisons=str(profile.limits.algebraic_comparisons),
        leaves=str(profile.limits.leaf_or_cell_transitions),
        totalWork=str(m.policy.total_work),
    )
    input_wire = dict(
        schema="exactcis.boschloo.global-checker.input.v1",
        method="boschloo",
        estimand="odds_ratio",
        design="independent_groups",
        a=str(table[0]),
        b=str(table[1]),
        c=str(table[2]),
        d=str(table[3]),
        alpha=rational(alpha, m),
        alphaSide=rational(model.level, m),
        hullEndpointExcessTolerance=rational(tolerance, m),
        limits=limits,
    )
    payload = dict(
        schema="exactcis.boschloo.global-checker.payload.v1",
        coordinate="s=psi/(1+psi)",
        points=[point_wire(point.point, m) for point in data],
        adjacentOrder=[
            dict(kind="rational_or_disjoint") for _ in range(max(0, len(data) - 1))
        ],
        rootCovers=cover_wire,
        openLeaves=opens,
        pointLeaves=[point.leaf for point in data],
        terminal=terminal,
    )
    checkpoint("P9_wire_records_before_serialization")
    return Candidate(input_wire, payload, m.root_state(), tuple(checkpoints))
