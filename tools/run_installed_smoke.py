#!/usr/bin/env python3
"""Exercise the documented design-aware contract from an installed package."""

from __future__ import annotations

from importlib.metadata import version

from exactcis import Design, InferenceResult, __version__, compute_or_with_policy


def main() -> int:
    result = compute_or_with_policy(
        10,
        2,
        5,
        20,
        design=Design.CASE_CONTROL_FIXED_MARGIN,
    )
    assert isinstance(result, InferenceResult)
    assert result.lower <= result.point <= result.upper
    assert result.design is Design.CASE_CONTROL_FIXED_MARGIN
    assert result.method == "conditional"
    assert __version__ == version("exactcis")
    print(f"OK: exactcis {__version__} installed-package smoke")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
