"""Common-round finite sign construction at one selected embedding.

After gcd localization fixes the zero identities, all nonzero remainders are
tested on the same interval in each round. One failed sign causes one checked
bisection. This schedule has a direct uniform-width termination proof.
"""

from __future__ import annotations

from fractions import Fraction as Q
from typing import cast

import metered_algebraic as a
import metered_global_geometry as g
import metered_polynomial as p
import metered_root as r
import resource_model as v
from metered_localize import Localized


def _rational(point: Q, family: tuple[p.P, ...], m: r.Meter) -> Localized:
    m.structural(2 * len(family))
    return Localized(
        point,
        tuple(m.compare(p.value(poly, point, m), Q(0)) for poly in family),
        (None,) * len(family),
    )


def localize(selected: a.Root, family: tuple[p.P, ...], m: r.Meter) -> Localized:
    a.check_root(selected, m)
    m.resources.shape("list_items", len(family), phase="selected_sign_family")
    current = selected
    for poly in family:
        m.structural()
        common, _, _ = p.xgcd(current.definer, poly, m)
        m.resources.charge(
            v.Event.PROJECTION_ROOT,
            v.CostVector(projection_roots=1),
            phase="selected_sign_family",
        )
        certificate = r.generate_witness_with_meter(common, m)
        count = r.count_with_meter(common, certificate, m, current.lower, current.upper)
        if count == 1:
            current = a.Root(common, current.lower, current.upper, certificate)
        elif count != 0:
            raise r.InvalidWitness(
                "finite-family localization lost the unique embedding"
            )
    if len(current.definer) == 2:
        point = m.div(m.sub(Q(0), current.definer[0]), current.definer[1])
        if m.compare(current.lower, point) >= 0 or m.compare(point, current.upper) >= 0:
            raise r.InvalidWitness(
                "localized linear definer escaped its selected interval"
            )
        return _rational(point, family, m)
    m.structural(len(family))
    divisions = tuple(p.divide(poly, current.definer, m) for poly in family)
    depth = 0
    while True:
        m.structural()
        signs: list[int] = []
        witnesses: list[a.SignWitness] = []
        complete = True
        for quotient, remainder in divisions:
            m.structural()
            if not remainder:
                signs.append(0)
                witnesses.append(a.SignWitness(0, quotient, ()))
                continue
            lo, hi = a.bounds(remainder, current.lower, current.upper, m)
            if m.compare(lo, Q(0)) > 0:
                signs.append(1)
                witnesses.append(a.SignWitness(1, quotient, remainder))
            elif m.compare(hi, Q(0)) < 0:
                signs.append(-1)
                witnesses.append(
                    a.SignWitness(
                        -1, p.scale(Q(-1), quotient, m), p.scale(Q(-1), remainder, m)
                    )
                )
            else:
                complete = False
                break
        if complete:
            m.structural(2 * len(family))
            for poly, witness in zip(family, witnesses):
                a.sign_at(current, poly, witness, m)
            return Localized(current, tuple(signs), tuple(witnesses))
        depth += 1
        m.resources.shape("refinement_depth", depth, phase="selected_sign_family")
        m.resources.charge(
            v.Event.PROJECTION_ROOT,
            v.CostVector(projection_roots=1),
            phase="selected_sign_family",
        )
        next_point = g.refine(current, m)
        if type(next_point) is Q:
            return _rational(next_point, family, m)
        current = cast(a.Root, next_point)
