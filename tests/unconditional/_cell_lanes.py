"""Independent sufficient whole-cell tensor and cutoff-band certificates.

CAD-lite supplies event isolation and its independently checked cell decision.
The two fast lanes rebuild Fisher comparisons and cleared objectives from sums;
they never turn an unresolved box into a decision. All certificates refer to an
enclosing rational effect interval, not just a sample in the effect cell.
"""

from __future__ import annotations

from fractions import Fraction as F
from math import comb

from . import _tensor_reference as t


def comparisons(n1, n0, observed, direction):
    """Unreduced tail cross-products, cleared by (1-s)^(2*n1)."""

    def polynomials(point):
        x, y = point
        denominator = {
            (k, 0): F(comb(n1, k) * comb(n0, x + y - k))
            for k in range(max(0, x + y - n0), min(n1, x + y) + 1)
        }
        numerator = {
            key: value
            for key, value in denominator.items()
            if (key[0] >= x if direction == "greater" else key[0] <= x)
        }
        return numerator, denominator

    observed_n, observed_d = polynomials(observed)
    result = {}
    for x in range(n1 + 1):
        for y in range(n0 + 1):
            num, den = polynomials((x, y))
            cross = t._add(
                t._multiply(num, observed_d),
                t._scale(t._multiply(observed_n, den), F(-1)),
            )
            compact = {}
            for (k, _), value in cross.items():
                for j in range(2 * n1 - k + 1):
                    key = (k + j, 0)
                    compact[key] = (
                        compact.get(key, F(0)) + value * comb(2 * n1 - k, j) * (-1) ** j
                    )
            result[x, y] = {key: value for key, value in compact.items() if value}
    return result


def bands(n1, n0, family, interval, direction, *, cutoffs=False):
    """Sound Rminus/Rplus from whole-interval signs; optionally close cutoffs."""
    lower, upper = [], []
    a, b = interval
    for point, power in family.items():
        low, high = t.hull(t.controls(power, (2 * n1, 0), (a, b, F(0), F(1))))
        if high <= 0:
            lower.append(point)
        if low <= 0:
            upper.append(point)
    if cutoffs:
        included, excluded = set(lower), set(family) - set(upper)
        lower, upper = [], []
        for margin in range(n1 + n0 + 1):
            lo, hi = max(0, margin - n0), min(n1, margin)
            yes = [x for x in range(lo, hi + 1) if (x, margin - x) in included]
            no = [x for x in range(lo, hi + 1) if (x, margin - x) in excluded]
            if direction == "greater":
                lower_cut = min(yes, default=hi + 1)
                upper_cut = max(no, default=lo - 1) + 1
                lower.extend((x, margin - x) for x in range(lower_cut, hi + 1))
                upper.extend((x, margin - x) for x in range(upper_cut, hi + 1))
            else:
                lower_cut = max(yes, default=lo - 1)
                upper_cut = min(no, default=hi + 1) - 1
                lower.extend((x, margin - x) for x in range(lo, lower_cut + 1))
                upper.extend((x, margin - x) for x in range(lo, upper_cut + 1))
    return tuple(sorted(lower)), tuple(sorted(upper))


def decide(n1, n0, lower, upper, interval, level, *, effect_depth=1, nuisance_depth=3):
    """Sufficient universal-in-effect certificates with two-coordinate progress."""
    counts = {
        "effect_nodes": 0,
        "nuisance_nodes": 0,
        "witnesses": 0,
        "rejection_boxes": 0,
        "coefficient_builds": 2,
    }
    low_power, high_power = (
        t.objective(n1, n0, lower, level),
        t.objective(n1, n0, upper, level),
    )
    degree = n1, n1 + n0

    def one(a, b):
        low_tensor = t.controls(low_power, degree, (a, b, F(0), F(1)))
        for q in (F(0), F(1, 4), F(1, 2), F(3, 4), F(1)):
            counts["witnesses"] += 1
            if t.constant_witness(low_tensor, q):
                return True
        queue = [(F(0), F(1), 0)]
        unresolved = False
        while queue:
            c, d, depth = queue.pop()
            counts["nuisance_nodes"] += 1
            if t.hull(t.controls(high_power, degree, (a, b, c, d)))[1] < 0:
                counts["rejection_boxes"] += 1
                continue
            if depth == nuisance_depth:
                unresolved = True
            else:
                mid = (c + d) / 2
                queue.extend(((mid, d, depth + 1), (c, mid, depth + 1)))
        return None if unresolved else False

    def refine(a, b, depth):
        counts["effect_nodes"] += 1
        answer = one(a, b)
        if answer is not None or depth == effect_depth:
            return answer
        mid = (a + b) / 2
        left, right = refine(a, mid, depth + 1), refine(mid, b, depth + 1)
        return left if left is not None and left == right else None

    return refine(*interval, 0), counts


def compare_cells(n1, n0, observed, level, topology):
    families = {
        direction: comparisons(n1, n0, observed, direction)
        for direction in ("greater", "less")
    }
    records = []
    for index, leaf in enumerate(topology["leaves"]):
        if leaf["kind"] != "open":
            continue
        left = topology["events"][leaf["left_event"]]["isolator"][0]
        right = topology["events"][leaf["right_event"]]["isolator"][1]
        for i, direction in enumerate(("greater", "less")):
            expected = leaf["decisions"][i]["accepted"]
            actual = set(leaf["masks"][i])
            row = {
                "leaf": index,
                "direction": direction,
                "interval": (left, right),
                "projected_event": expected,
            }
            for name, cutoff in (("tensor", False), ("cutoff_cover", True)):
                lower, upper = bands(
                    n1,
                    n0,
                    families[direction],
                    (left, right),
                    direction,
                    cutoffs=cutoff,
                )
                if not set(lower) <= actual <= set(upper):
                    raise AssertionError("whole-cell mask-band disagreement")
                answer, counts = decide(n1, n0, lower, upper, (left, right), level)
                if answer is not None and answer != expected:
                    raise AssertionError("whole-cell scientific decision disagreement")
                row[name] = {
                    "decision": answer,
                    "lower_mask": lower,
                    "upper_mask": upper,
                    "counts": counts,
                }
            records.append(row)
    return records
