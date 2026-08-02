"""Every retained example executes against the source package."""

from __future__ import annotations

import runpy
from pathlib import Path

import pytest

EXAMPLE_ROOT = Path(__file__).parents[1] / "examples"


@pytest.mark.parametrize("name", ("quick_start.py", "api_examples.py"))
def test_example_executes(name: str) -> None:
    runpy.run_path(str(EXAMPLE_ROOT / name), run_name="__main__")
