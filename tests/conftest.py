"""Shared helpers for the public ExactCIs test suite."""

from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any

REFERENCE_ROOT = Path(__file__).parent / "references"


def load_reference(name: str) -> dict[str, Any]:
    """Load one reviewed independent-reference fixture."""
    return json.loads((REFERENCE_ROOT / name).read_text(encoding="utf-8"))


def endpoint(value: float | str) -> float:
    """Decode the JSON spelling of an extended positive endpoint."""
    return math.inf if value == "Infinity" else float(value)
