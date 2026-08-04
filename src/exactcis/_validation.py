"""Shared validation for the public statistical core."""

from __future__ import annotations

import math
from numbers import Integral
from typing import Iterable

from exactcis.exceptions import ValidationError

Table = tuple[int, int, int, int]
_ALPHA_STABILITY_MARGIN = 1e-12
_MAXIMUM_CERTIFIED_ALPHA = 1.0 - _ALPHA_STABILITY_MARGIN
# Keep cell counts inside a range where float/log-space arithmetic retains
# relative error comfortably below 1e-8 for the certified methods.
_MAXIMUM_CELL_COUNT = 10**12


def validate_alpha(alpha: float) -> float:
    """Return a significance level inside the certified numerical domain."""
    message = "alpha must satisfy 1e-12 < alpha < 1 - 1e-12 for numerical stability"
    try:
        value = float(alpha)
    except (TypeError, ValueError, OverflowError) as exc:
        raise ValidationError(message) from exc
    if (
        not math.isfinite(value)
        or not _ALPHA_STABILITY_MARGIN < value < _MAXIMUM_CERTIFIED_ALPHA
    ):
        raise ValidationError(f"{message}, got {alpha!r}")
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
    if any(value > _MAXIMUM_CELL_COUNT for value in counts):
        raise ValidationError(
            "table counts must not exceed "
            f"{_MAXIMUM_CELL_COUNT} (1e12); got {counts!r}"
        )
    try:
        total = sum(counts)
        if total > 4 * _MAXIMUM_CELL_COUNT or not math.isfinite(float(total)):
            raise ValidationError(
                "table totals must be finite and within certified bounds"
            )
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
