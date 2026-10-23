"""Independent bounded CAD-style Boschloo effect-topology reference.

It constructs the complete comparison partition, projects squarefree threshold
guards, and rebuilds every exceptional effect over its selected real embedding.
No rational sample alone certifies a cell. Successful output covers [0,1];
budget exhaustion raises rather than returning a partial topology.
"""

from __future__ import annotations

from fractions import Fraction as F
from math import comb

from . import _oracle as oracle
from . import _parametric as qpoly
from . import _polynomial as p
from ._algebraic import (
    Element,
    Root,
    Work,
    between,
    compare,
    isolate,
    merge_roots,
    refine,
    sign_at,
)

DIRECTIONS = ("greater", "less")


def ppow(a, n, work):
    result = p.ONE
    for _ in range(n):
        result = work.call("multiply", result, a)
    return result


def scale(a, k, work):
    return work.call("trim", tuple(F(k) * c for c in a))


def compact(a, work):
    """(1-s)^degree G(s/(1-s)), preserving sign on the interior."""
    a = work.call("trim", a)
    result = p.ZERO
    for j, c in enumerate(a):
        if c:
            term = work.call(
                "multiply",
                (F(0),) * j + (F(c),),
                ppow((F(1), F(-1)), len(a) - 1 - j, work),
            )
            result = work.call("add", result, term)
    return result


def threshold(n1, n0, mask, level, work):
    """Original H(s,q), ascending q coefficients which are polynomials in s."""
    work.tick("coefficient_build")
    size = n1 + n0
    result = [p.ZERO for _ in range(size + 1)]
    for x, y in mask:
        weight = work.call(
            "multiply",
            (F(0),) * x + (F(comb(n1, x) * comb(n0, y)),),
            ppow((F(1), F(-1)), n1 - x, work),
        )
        for j in range(size - x - y + 1):
            result[x + y + j] = work.call(
                "add",
                result[x + y + j],
                scale(weight, (-1) ** j * comb(size - x - y, j), work),
            )
    # L(s,q)=(1-s)+(2s-1)q; B=L^n1 is the actual cleared denominator.
    for j in range(n1 + 1):
        term = work.call(
            "multiply", ppow((F(1), F(-1)), n1 - j, work), ppow((F(-1), F(2)), j, work)
        )
        result[j] = work.call("add", result[j], scale(term, -level * comb(n1, j), work))
    while len(result) > 1 and result[-1] == p.ZERO:
        result.pop()
    return tuple(result)


def comparison_family(n1, n0, observed, work):
    family = {}
    for direction in DIRECTIONS:
        family[direction] = tuple(
            compact(
                oracle.comparison_polynomial(n1, n0, observed, candidate, direction),
                work,
            )
            for candidate in oracle.sample_space(n1, n0)
        )
    return family


def masks_at(n1, n0, comparisons, effect, work):
    sample = oracle.sample_space(n1, n0)
    work.tick("mask_classification")
    return tuple(
        tuple(
            candidate
            for candidate, poly in zip(sample, comparisons[direction])
            if sign_at(poly, effect, work) <= 0
        )
        for direction in DIRECTIONS
    )


def algebraic_cutoffs(n1, n0, observed, effect, direction, work):
    """Independent normalized Fisher sums at a selected algebraic effect."""
    s = Element(effect, (0, 1), (1,), work)
    psi = s / (1 - s)

    def tail(point):
        x, y = point
        weights = tuple(
            (k, comb(n1, k) * comb(n0, x + y - k) * psi**k)
            for k in range(max(0, x + y - n0), min(n1, x + y) + 1)
        )
        numerator = sum(
            v for k, v in weights if (k >= x if direction == "greater" else k <= x)
        )
        return numerator / sum(v for _, v in weights)

    observed_tail = tail(observed)
    cutoffs = []
    for m in range(n1 + n0 + 1):
        lo, hi = max(0, m - n0), min(n1, m)
        selected = [
            x
            for x in range(lo, hi + 1)
            if (tail((x, m - x)) - observed_tail).sign() <= 0
        ]
        if direction == "greater":
            cutoff = selected[0] if selected else hi + 1
            expected = list(range(cutoff, hi + 1))
        else:
            cutoff = selected[-1] if selected else lo - 1
            expected = list(range(lo, cutoff + 1))
        if selected != expected:
            raise ArithmeticError("Fisher tail ordering is not a contiguous cutoff")
        cutoffs.append(cutoff)
    return tuple(cutoffs)


def ordering_anchor(*, work=None):
    """Full inclusive masks at the specified cubic ordering transition."""
    work = Work() if work is None else work
    n1 = n0 = 4
    observed, candidate = (0, 2), (1, 3)
    comparisons = comparison_family(n1, n0, observed, work)
    polynomial = compact(
        oracle.comparison_polynomial(n1, n0, observed, candidate, "less"), work
    )
    roots = isolate(polynomial, F(29, 39), F(59, 79), work)
    if len(roots) != 1:
        raise ArithmeticError("ordering anchor no longer isolates one event")
    event = roots[0]
    masks = masks_at(n1, n0, comparisons, event, work)
    cutoffs = tuple(
        algebraic_cutoffs(n1, n0, observed, event, d, work) for d in DIRECTIONS
    )
    for direction, mask, cutoff in zip(DIRECTIONS, masks, cutoffs):
        if oracle.expand_cutoffs(n1, n0, cutoff, direction) != mask:
            raise ArithmeticError("algebraic cutoff and comparator masks disagree")
    if sign_at(polynomial, event, work) != 0 or candidate not in masks[1]:
        raise ArithmeticError("inclusive algebraic event tie was lost")
    record = root_record(event, work)
    return {
        "event": record,
        "masks": masks,
        "cutoffs": cutoffs,
        "candidate_tied_and_included": True,
        "counts": dict(work.counts),
    }


def separate(roots, work):
    roots = list(merge_roots(roots, work))
    for i in range(len(roots) - 1):
        while roots[i].right >= roots[i + 1].left:
            roots[i], roots[i + 1] = refine(roots[i], work), refine(roots[i + 1], work)
    return tuple(roots)


def rational_root(value):
    return Root((-value.numerator, value.denominator), value, value)


def root_record(root, work):
    root.verify(work)
    bound = F(1) + max(abs(F(c, root.polynomial[-1])) for c in root.polynomial[:-1])
    index = work.call("count_roots", root.polynomial, -bound, root.left)
    data = {
        "polynomial": tuple(str(c) for c in root.polynomial),
        "isolator": (root.left, root.right),
        "root_index": index,
    }
    if root.rational is not None:
        data["kind"] = "rational"
    else:
        variations, _ = work.root_variations(root.polynomial, root.left, root.right)
        data.update(kind="algebraic", variations=variations)
    return data


def components(leaves):
    """Group accepted consecutive owned leaves; retain open ends/singletons."""
    groups = []
    for i, leaf in enumerate(leaves):
        if leaf["accepted"]:
            if groups and groups[-1][-1] == i - 1:
                groups[-1].append(i)
            else:
                groups.append([i])
    result = []
    for group in groups:
        first, last = leaves[group[0]], leaves[group[-1]]
        result.append(
            {
                "leaves": tuple(group),
                "lower_event": first["left_event"],
                "upper_event": last["right_event"],
                "lower_closed": first["kind"] != "open",
                "upper_closed": last["kind"] != "open",
            }
        )
    hull = (
        None
        if not result
        else {
            "lower_event": result[0]["lower_event"],
            "upper_event": result[-1]["upper_event"],
            "lower_attained": result[0]["lower_closed"],
            "upper_attained": result[-1]["upper_closed"],
        }
    )
    return tuple(result), hull


def topology(n1, n0, observed, level, *, work=None):
    work = Work() if work is None else work
    oracle._groups(n1, n0)
    oracle._point(n1, n0, observed)
    oracle._unit(level)
    if max(n1, n0) > 12:
        raise p.OracleLimitError(
            "topology reference grammar supports groups through 12"
        )
    comparisons = comparison_family(n1, n0, observed, work)
    initial = [rational_root(F(0)), rational_root(F(1))]
    for polys in comparisons.values():
        for poly in polys:
            if len(poly) > 1:
                initial.extend(isolate(poly, F(0), F(1), work))
    ordering = separate(initial, work)
    events, projections, strata = list(ordering), [], []
    projection_cache, guard_cache = {}, {}
    for left, right in zip(ordering, ordering[1:]):
        sample = between(left, right, work)
        effect = rational_root(sample)
        masks = masks_at(n1, n0, comparisons, effect, work)
        ids = []
        for mask in masks:
            if mask in projection_cache:
                work.tick("projection_cache_hit")
                index = projection_cache[mask]
                projection = projections[index]["certificate"]
            else:
                h = threshold(n1, n0, mask, level, work)
                projection = qpoly.projection(qpoly.specialize(h, None, work))
                index = len(projections)
                projection_cache[mask] = index
                projections.append({"threshold": h, "certificate": projection})
            ids.append(index)
            for guard in projection["guards"]:
                if guard not in guard_cache:
                    guard_cache[guard] = isolate(guard, F(0), F(1), work)
                else:
                    work.tick("guard_cache_hit")
                for root in guard_cache[guard]:
                    if compare(left, root, work) < 0 and compare(root, right, work) < 0:
                        events.append(root)
        strata.append((left, right, masks, tuple(ids)))
    events = separate(events, work)
    leaves = []
    for i, event in enumerate(events):
        if i in (0, len(events) - 1):
            tag = "zero" if i == 0 else "infinity"
            pair = oracle.structural_pair(n1, n0, observed, tag)
            leaves.append(
                {
                    "kind": "structural",
                    "left_event": i,
                    "right_event": i,
                    "tag": tag,
                    "pair": pair,
                    "accepted": all(v >= level for v in pair),
                }
            )
        else:
            masks = masks_at(n1, n0, comparisons, event, work)
            decisions = tuple(
                qpoly.decide(
                    qpoly.specialize(threshold(n1, n0, mask, level, work), event, work)
                )
                for mask in masks
            )
            leaves.append(
                {
                    "kind": "point",
                    "left_event": i,
                    "right_event": i,
                    "masks": masks,
                    "decisions": decisions,
                    "accepted": all(d["accepted"] for d in decisions),
                }
            )
        if i + 1 == len(events):
            continue
        sample = between(event, events[i + 1], work)
        effect = rational_root(sample)
        owner = next(
            s
            for s in strata
            if compare(s[0], effect, work) < 0 and compare(effect, s[1], work) < 0
        )
        masks = masks_at(n1, n0, comparisons, effect, work)
        if masks != owner[2]:
            raise ArithmeticError("mask changed inside root-free ordering stratum")
        decisions = tuple(
            qpoly.decide(qpoly.specialize(projections[j]["threshold"], effect, work))
            for j in owner[3]
        )
        leaves.append(
            {
                "kind": "open",
                "left_event": i,
                "right_event": i + 1,
                "sample": sample,
                "masks": masks,
                "projection_ids": owner[3],
                "decisions": decisions,
                "accepted": all(d["accepted"] for d in decisions),
            }
        )
    component_list, hull = components(leaves)
    event_records = tuple(root_record(root, work) for root in events)
    return {
        "coordinate": "s=psi/(1+psi)",
        "comparison_polynomials": comparisons,
        "events": event_records,
        "projections": tuple(projections),
        "leaves": tuple(leaves),
        "components": component_list,
        "ideal_hull": hull,
        "empty": not component_list,
        "full": all(leaf["accepted"] for leaf in leaves),
        "counts": dict(work.counts),
    }
