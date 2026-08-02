"""Shared validation for the public statistical core."""

from __future__ import annotations

import math
from numbers import Integral
from typing import Iterable

from exactcis.exceptions import ValidationError

Table = tuple[int, int, int, int]


def validate_alpha(alpha: float) -> float:
    """Return a finite significance level strictly between zero and one."""
    try:
        value = float(alpha)
    except (TypeError, ValueError, OverflowError) as exc:
        raise ValidationError("alpha must be a finite number in (0, 1)") from exc
    if not math.isfinite(value) or not 0.0 < value < 1.0:
        raise ValidationError(f"alpha must be a finite number in (0, 1), got {alpha!r}")
    return value


def validate_table(a: int, b: int, c: int, d: int) -> Table:
    """Return four finite, non-negative integer cell counts."""
    values = (a, b, c, d)
    if any(
        isinstance(value, bool) or not isinstance(value, Integral) for value in values
    ):
        raise ValidationError("table counts must be finite non-negative integers")
    counts = tuple(int(value) for value in values)
    if any(value < 0 for value in counts):
        raise ValidationError("table counts must be finite non-negative integers")
    try:
        if not math.isfinite(float(sum(counts))):
            raise ValidationError("table totals must be finite")
    except OverflowError as exc:
        raise ValidationError("table totals must be finite") from exc
    return counts  # type: ignore[return-value]


def validate_independent_groups(a: int, b: int, c: int, d: int) -> Table:
    """Validate a table and require at least one observation in each row."""
    table = validate_table(a, b, c, d)
    if table[0] + table[1] == 0 or table[2] + table[3] == 0:
        raise ValidationError(
            "independent-binomial inference requires at least one observation "
            "in each comparison group"
        )
    return table


def validate_strata(strata: Iterable[Table]) -> tuple[Table, ...]:
    """Validate a non-empty collection of prespecified independent strata."""
    try:
        materialized = tuple(strata)
    except TypeError as exc:
        raise ValidationError(
            "strata must be an iterable of four-count tables"
        ) from exc
    if not materialized:
        raise ValidationError("at least one stratum is required")
    validated: list[Table] = []
    for index, table in enumerate(materialized):
        if not isinstance(table, (tuple, list)) or len(table) != 4:
            raise ValidationError(f"stratum {index} must contain exactly four counts")
        validated.append(validate_table(*table))
    return tuple(validated)


__all__ = [
    "Table",
    "validate_alpha",
    "validate_independent_groups",
    "validate_strata",
    "validate_table",
]
