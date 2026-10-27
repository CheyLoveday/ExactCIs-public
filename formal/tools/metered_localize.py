"""Bounded constructive localization of a selected root for finitely many signs.

The selected real root can be represented by a reducible definer. A zero-sign
packet in v1 requires divisibility by that *whole* definer. Intersecting it with
each vanishing polynomial's gcd preserves the selected embedding while making
the required zero identities constructible. Nonzero remainders use dyadic
isolator refinement. This is a producer component, not global generation.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q

import metered_algebraic as a
import metered_polynomial as p
import metered_root as r
import resource_model as v


@dataclass(frozen=True)
class Localized:
    point: a.Root | Q
    signs: tuple[int, ...]
    witnesses: tuple[a.SignWitness | None, ...]


def _visit(m: r.Meter) -> None:
    m.resources.charge(
        v.Event.PROJECTION_ROOT,
        v.CostVector(projection_roots=1),
        phase="root_localization",
    )


def _rational(q: Q, family: tuple[p.P, ...], m: r.Meter) -> Localized:
    signs: list[int] = []
    witnesses: list[None] = []
    for poly in family:
        m.structural()
        signs.append(m.compare(p.value(poly, q, m), Q(0)))
        witnesses.append(None)
    m.structural(2 * len(family))
    return Localized(q, tuple(signs), tuple(witnesses))


def localize(selected: a.Root, family: tuple[p.P, ...], m: r.Meter) -> Localized:
    if type(family) is not tuple:
        raise r.InvalidWitness("an immutable ordered polynomial family is required")
    m.resources.shape("list_items", len(family), phase="root_localization")
    a.check_root(selected, m)
    if m.compare(selected.lower, Q(0)) < 0:
        raise r.InvalidWitness("v1 localization requires the nonnegative effect chart")
    current = selected
    for poly in family:
        m.structural()
        p.canonical(poly, m)
        common, _, _ = p.xgcd(current.definer, poly, m)
        _visit(m)
        certificate = r.generate_witness_with_meter(common, m)
        count = r.count_with_meter(common, certificate, m, current.lower, current.upper)
        if count == 1:
            current = a.Root(common, current.lower, current.upper, certificate)
        elif count != 0:
            raise r.InvalidWitness("gcd roots contradict the unique selected embedding")

    if len(current.definer) == 2:
        point = m.div(m.sub(Q(0), current.definer[0]), current.definer[1])
        if m.compare(current.lower, point) >= 0 or m.compare(point, current.upper) >= 0:
            raise r.InvalidWitness("linear definer contradicts its selected isolator")
        return _rational(point, family, m)

    # No new definer is introduced after this pass. Later narrowing preserves
    # every earlier remainder sign and every exact quotient identity.
    signs: list[int] = []
    witnesses: list[a.SignWitness | None] = []
    depth = 0
    for poly in family:
        quotient, remainder = p.divide(poly, current.definer, m)
        if not remainder:
            signs.append(0)
            witnesses.append(a.SignWitness(0, quotient, ()))
            continue
        while True:
            m.structural()
            lo, hi = a.bounds(remainder, current.lower, current.upper, m)
            if m.compare(lo, Q(0)) > 0:
                signs.append(1)
                witnesses.append(a.SignWitness(1, quotient, remainder))
                break
            if m.compare(hi, Q(0)) < 0:
                signs.append(-1)
                witnesses.append(
                    a.SignWitness(
                        -1, p.scale(Q(-1), quotient, m), p.scale(Q(-1), remainder, m)
                    )
                )
                break
            m.resources.shape("refinement_depth", depth + 1, phase="root_localization")
            midpoint = m.div(m.add(current.lower, current.upper), Q(2))
            _visit(m)
            if m.compare(p.value(current.definer, midpoint, m), Q(0)) == 0:
                return _rational(midpoint, family, m)
            left_count = r.count_with_meter(
                current.definer, current.certificate, m, current.lower, midpoint
            )
            if left_count == 1:
                current = a.Root(
                    current.definer, current.lower, midpoint, current.certificate
                )
            elif left_count == 0:
                current = a.Root(
                    current.definer, midpoint, current.upper, current.certificate
                )
            else:
                raise r.InvalidWitness("refinement contradicts the selected root count")
            depth += 1
    m.structural(2 * len(family))
    result = Localized(current, tuple(signs), tuple(witnesses))
    # Generation and actual sign replay share the same meter. No producer flag
    # attests that the emitted signs are justified.
    for poly, witness in zip(family, result.witnesses):
        if witness is None:
            raise r.InvalidWitness("algebraic point requires algebraic sign witnesses")
        a.sign_at(current, poly, witness, m)
    return result
