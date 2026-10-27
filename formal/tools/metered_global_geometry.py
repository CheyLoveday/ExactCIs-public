"""Exact deterministic selected-root refinement, merging and chart samples."""

from __future__ import annotations

from fractions import Fraction as Q
from typing import cast

import metered_algebraic as a
import metered_polynomial as p
import metered_root as r

Point = Q | a.Root


def lower(point: Point) -> Q:
    return point if type(point) is Q else cast(a.Root, point).lower


def upper(point: Point) -> Q:
    return point if type(point) is Q else cast(a.Root, point).upper


def refine(point: a.Root, m: r.Meter) -> Point:
    midpoint = m.div(m.add(point.lower, point.upper), Q(2))
    if m.compare(p.value(point.definer, midpoint, m), Q(0)) == 0:
        return midpoint
    count = r.count_with_meter(
        point.definer, point.certificate, m, point.lower, midpoint
    )
    if count == 1:
        result = a.Root(point.definer, point.lower, midpoint, point.certificate)
    elif count == 0:
        result = a.Root(point.definer, midpoint, point.upper, point.certificate)
    else:
        raise r.InvalidWitness("refinement contradicted a singleton selected root")
    a.check_root(result, m)
    return result


def _poly_less(left: p.P, right: p.P, m: r.Meter) -> bool:
    m.structural()
    if len(left) != len(right):
        return len(left) < len(right)
    for a_value, b_value in zip(left, right):
        m.structural()
        order = m.compare(a_value, b_value)
        if order:
            return order < 0
    return False


def compare(left: Point, right: Point, m: r.Meter) -> tuple[int, Point, Point]:
    """Return exact order and narrowed representatives of the same values."""
    depth = 0
    common_checked = False
    while True:
        m.structural()
        if type(left) is Q and type(right) is Q:
            return m.compare(left, right), left, right
        if m.compare(upper(left), lower(right)) <= 0:
            return -1, left, right
        if m.compare(upper(right), lower(left)) <= 0:
            return 1, left, right
        if type(left) is Q:
            right = cast(a.Root, right)
            if m.compare(p.value(right.definer, left, m), Q(0)) == 0:
                return 0, left, left
            right = refine(right, m)
        elif type(right) is Q:
            left = cast(a.Root, left)
            if m.compare(p.value(left.definer, right, m), Q(0)) == 0:
                return 0, right, right
            left = refine(left, m)
        else:
            left, right = cast(a.Root, left), cast(a.Root, right)
            if not common_checked:
                common, _, _ = p.xgcd(left.definer, right.definer, m)
                if len(common) > 1:
                    lo = (
                        left.lower
                        if m.compare(left.lower, right.lower) >= 0
                        else right.lower
                    )
                    hi = (
                        left.upper
                        if m.compare(left.upper, right.upper) <= 0
                        else right.upper
                    )
                    certificate = r.generate_witness_with_meter(common, m)
                    count = r.count_with_meter(common, certificate, m, lo, hi)
                    if count == 1:
                        chosen = (
                            left
                            if _poly_less(left.definer, right.definer, m)
                            else right
                        )
                        point = a.Root(chosen.definer, lo, hi, chosen.certificate)
                        a.check_root(point, m)
                        return 0, point, point
                    if count != 0:
                        raise r.InvalidWitness(
                            "intersection contained multiple common selected roots"
                        )
                common_checked = True
            left_width = m.sub(left.upper, left.lower)
            right_width = m.sub(right.upper, right.lower)
            if m.compare(left_width, right_width) >= 0:
                left = refine(left, m)
            else:
                right = refine(right, m)
        depth += 1
        m.resources.shape("refinement_depth", depth, phase="root_ordering")


def merge_sort(points: tuple[Point, ...], m: r.Meter) -> tuple[Point, ...]:
    m.structural()
    if len(points) <= 1:
        return points
    middle = len(points) // 2
    m.structural(len(points))
    left = list(merge_sort(points[:middle], m))
    right = list(merge_sort(points[middle:], m))
    result: list[Point] = []
    i = j = 0
    while i < len(left) and j < len(right):
        m.structural()
        order, first, second = compare(left[i], right[j], m)
        if order < 0:
            result.append(first)
            right[j] = second
            i += 1
        elif order > 0:
            result.append(second)
            left[i] = first
            j += 1
        else:
            result.append(first)
            i += 1
            j += 1
    m.structural(len(left) - i + len(right) - j)
    result.extend(left[i:])
    result.extend(right[j:])
    m.resources.shape("unique_projection_members", len(result), phase="root_ordering")
    m.structural(len(result))
    return tuple(result)


def sample(left: Point, right: Point, m: r.Meter) -> tuple[Q, Point, Point]:
    depth = 0
    while True:
        m.structural()
        lo, hi = upper(left), lower(right)
        order = m.compare(lo, hi)
        if order < 0 or order == 0 and type(left) is not Q and type(right) is not Q:
            return m.div(m.add(lo, hi), Q(2)), left, right
        if type(left) is not Q:
            left = refine(cast(a.Root, left), m)
        if type(right) is not Q:
            right = refine(cast(a.Root, right), m)
        depth += 1
        m.resources.shape("refinement_depth", depth, phase="cell_sample")
