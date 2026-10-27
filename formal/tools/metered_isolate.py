"""Deterministic adaptive isolation of every root in the open compact chart.

Only cells with a positive *open* distinct-root count are subdivided. Rational
midpoint roots become exact rational points. Structural roots at 0 and 1 are
excluded. This is a projection construction component, not global acceptance.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from typing import cast

import metered_algebraic as a
import metered_polynomial as p
import metered_root as r
import resource_model as v


@dataclass(frozen=True)
class Cell:
    lower: Q
    upper: Q
    count: int
    depth: int


def open_count(
    h: p.P, certificate: r.RootWitness, lower: Q, upper: Q, m: r.Meter
) -> int:
    count = r.count_with_meter(h, certificate, m, lower, upper)
    upper_zero = m.compare(p.value(h, upper, m), Q(0)) == 0
    m.integer_step()
    answer = count - int(upper_zero)
    if answer < 0:
        raise r.InvalidWitness("open root count became negative")
    return answer


def _visit(m: r.Meter) -> None:
    m.resources.charge(
        v.Event.PROJECTION_ROOT,
        v.CostVector(projection_roots=1),
        phase="root_isolation",
    )


def isolate(
    h: p.P, m: r.Meter, *, certificate: r.RootWitness | None = None
) -> tuple[Q | a.Root, ...]:
    h = p.canonical(h, m)
    if not h:
        raise r.InvalidWitness("zero projection polynomial has no finite root cover")
    certificate = (
        r.generate_witness_with_meter(h, m) if certificate is None else certificate
    )
    count = open_count(h, certificate, Q(0), Q(1), m)
    m.structural()
    pending: list[Cell | Q] = [Cell(Q(0), Q(1), count, 0)]
    found: list[Q | a.Root] = []
    while pending:
        _visit(m)
        cell = pending.pop()
        if type(cell) is Q:
            m.structural()
            found.append(cell)
            continue
        cell = cast(Cell, cell)
        if not cell.count:
            continue
        lower_zero = m.compare(p.value(h, cell.lower, m), Q(0)) == 0
        upper_zero = m.compare(p.value(h, cell.upper, m), Q(0)) == 0
        if cell.count == 1 and not lower_zero and not upper_zero:
            m.structural()
            root = a.Root(h, cell.lower, cell.upper, certificate)
            a.check_root(root, m)
            found.append(root)
            continue
        depth = cell.depth + 1
        m.resources.shape("refinement_depth", depth, phase="root_isolation")
        midpoint = m.div(m.add(cell.lower, cell.upper), Q(2))
        midpoint_zero = m.compare(p.value(h, midpoint, m), Q(0)) == 0
        left = open_count(h, certificate, cell.lower, midpoint, m)
        right = open_count(h, certificate, midpoint, cell.upper, m)
        m.integer_step()
        if left + int(midpoint_zero) + right != cell.count:
            raise r.InvalidWitness("open-root subdivision lost or duplicated a root")
        # A LIFO traversal schedules right, midpoint, left, so emitted roots
        # are already in mathematical left-to-right order. Empty cells are
        # never enqueued, and no cross-definer merge/sort is required.
        m.structural(3)
        if right:
            pending.append(Cell(midpoint, cell.upper, right, depth))
        if midpoint_zero:
            pending.append(midpoint)
        if left:
            pending.append(Cell(cell.lower, midpoint, left, depth))
    if len(found) != count:
        raise r.InvalidWitness("root isolation emitted an incomplete root list")
    m.structural(len(found))
    return tuple(found)
