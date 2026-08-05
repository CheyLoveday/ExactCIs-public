#!/usr/bin/env python3
"""Reject stale current-release version references in public prose."""

from __future__ import annotations

import argparse
import ast
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ABOUT = Path("src/exactcis/__about__.py")
DOCUMENTS = (Path("README.md"), Path("AGENTS.md"), Path("CITATION.txt"))
VERSION = r"(?P<version>\d+\.\d+\.\d+(?:rc\d+)?)"
PATTERNS = (
    ("exactcis pin", re.compile(rf"\bexactcis=={VERSION}\b")),
    (
        "version statement",
        re.compile(
            rf"(?im)^\s*(?:[-*]\s*)?version\s*(?::|is)?\s*"
            rf"(?:[`*]+)?{VERSION}(?:[`*]+)?\b"
        ),
    ),
    (
        "release-tag statement",
        re.compile(
            rf"(?im)^\s*(?:[-*]\s*)?(?:public\s+)?(?:release\s+)?tag\s*:\s*"
            rf"v{VERSION}\b"
        ),
    ),
)
HISTORICAL_START = "<!-- exactcis-version-history:start -->"
HISTORICAL_END = "<!-- exactcis-version-history:end -->"
TIMING_START = "<!-- exactcis-timing-table:start -->"
TIMING_END = "<!-- exactcis-timing-table:end -->"


def package_version(root: Path) -> str:
    """Read the sole literal package version without importing the package."""
    path = root / ABOUT
    tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    assignments = [
        node.value.value
        for node in tree.body
        if isinstance(node, ast.Assign)
        and any(
            isinstance(target, ast.Name) and target.id == "__version__"
            for target in node.targets
        )
        and isinstance(node.value, ast.Constant)
        and isinstance(node.value.value, str)
    ]
    if len(assignments) != 1:
        raise ValueError("expected exactly one literal __version__ assignment")
    return assignments[0]


def _masked_block(text: str, start: str, end: str, path: Path) -> str:
    """Mask one explicitly exempt block while preserving original line numbers."""
    before, separator, remainder = text.partition(start)
    if not separator:
        return text
    body, separator, after = remainder.partition(end)
    if not separator:
        raise ValueError(f"{path}: missing closing marker {end}")
    masked = "\n" * (body.count("\n") + 1)
    return before + masked + after


def _scan_text(path: Path, expected: str) -> list[str]:
    """Return mismatched current-release references outside exempt blocks."""
    original = path.read_text(encoding="utf-8")
    scanned = _masked_block(original, HISTORICAL_START, HISTORICAL_END, path)
    scanned = _masked_block(scanned, TIMING_START, TIMING_END, path)
    errors: list[str] = []
    for label, pattern in PATTERNS:
        for match in pattern.finditer(scanned):
            actual = match.group("version")
            if actual != expected:
                line = scanned.count("\n", 0, match.start()) + 1
                errors.append(
                    f"{path}:{line}: {label} {actual!r} differs from package "
                    f"version {expected!r}"
                )
    return errors


def _documents(root: Path) -> tuple[Path, ...]:
    """List the version-controlled prose surfaces governed by this check."""
    docs = tuple(sorted((root / "docs_md").rglob("*.md")))
    return tuple(root / path for path in DOCUMENTS) + docs


def main(root: Path) -> int:
    """Check current-version prose under ``root`` and report every mismatch."""
    root = root.resolve()
    try:
        expected = package_version(root)
        errors = [
            error for path in _documents(root) for error in _scan_text(path, expected)
        ]
    except (OSError, ValueError, SyntaxError) as exc:
        print(f"ERROR: {exc}")
        return 1
    if errors:
        for error in errors:
            print(f"ERROR: {error}")
        return 1
    print(f"OK: public current-version references match exactcis=={expected}")
    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    arguments = parser.parse_args()
    raise SystemExit(main(arguments.root))
