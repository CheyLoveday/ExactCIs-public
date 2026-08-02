"""Print independently evaluated central and Mid-P FNCH endpoints.

This script is intentionally separate from the package implementation. It uses
arbitrary-precision binomial coefficients and a fixed 80-decimal bisection on
the log-odds scale. It prints values for human review and never overwrites the
reference fixture.
"""

from __future__ import annotations

import mpmath as mp

TABLES = (
    (12, 5, 8, 10),
    (3, 1, 1, 3),
    (7, 9, 8, 6),
    (1, 9, 11, 3),
    (0, 5, 5, 5),
    (10, 0, 0, 10),
    (99, 1, 50, 50),
    (50, 950, 25, 975),
    (20, 80, 40, 60),
)


def probabilities(
    table: tuple[int, int, int, int], log_odds: mp.mpf
) -> tuple[list[int], list[mp.mpf]]:
    """Return a normalized FNCH vector using direct high-precision sums."""
    a, b, c, d = table
    n1, n0, events = a + b, c + d, a + c
    support = list(range(max(0, events - n0), min(events, n1) + 1))
    masses = [
        mp.binomial(n1, value)
        * mp.binomial(n0, events - value)
        * mp.exp(log_odds * value)
        for value in support
    ]
    total = mp.fsum(masses)
    return support, [mass / total for mass in masses]


def endpoint(
    table: tuple[int, int, int, int], *, midp: bool, upper_tail: bool
) -> mp.mpf:
    """Solve one alpha/2 tail equation on the log-odds scale."""
    target = mp.mpf("0.025")
    left, right = mp.mpf(-1000), mp.mpf(1000)
    for _ in range(400):
        middle = (left + right) / 2
        support, masses = probabilities(table, middle)
        index = support.index(table[0])
        strict = mp.fsum(masses[index + 1 :] if upper_tail else masses[:index])
        value = strict + (mp.mpf("0.5") if midp else 1) * masses[index]
        if (value < target) == upper_tail:
            left = middle
        else:
            right = middle
    return mp.exp((left + right) / 2)


def main() -> None:
    mp.mp.dps = 80
    for table in TABLES:
        a, b, c, d = table
        n1, n0, events = a + b, c + d, a + c
        support_lower = max(0, events - n0)
        support_upper = min(events, n1)
        for name, midp in (("conditional", False), ("midp", True)):
            lower = (
                mp.mpf(0)
                if a == support_lower
                else endpoint(table, midp=midp, upper_tail=True)
            )
            upper = (
                mp.inf
                if a == support_upper
                else endpoint(table, midp=midp, upper_tail=False)
            )
            print(name, table, mp.nstr(lower, 30), mp.nstr(upper, 30))


if __name__ == "__main__":
    main()
