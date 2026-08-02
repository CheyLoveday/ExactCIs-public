#!/usr/bin/env python3
"""Audit the zero-dependency runtime contract and every supported extra."""

from __future__ import annotations

import ast
import re
import subprocess
import sys
import tempfile
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "src" / "exactcis"
EXPECTED_EXTRAS = {"dev", "docs", "release", "security", "validation"}
REQUIREMENT = re.compile(r"^[A-Za-z0-9_.-]+==", re.MULTILINE)


def third_party_runtime_imports() -> set[str]:
    """Return import roots that are neither stdlib nor part of exactcis."""
    third_party: set[str] = set()
    for path in SOURCE.rglob("*.py"):
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        for node in ast.walk(tree):
            names: list[str] = []
            if isinstance(node, ast.Import):
                names.extend(alias.name for alias in node.names)
            elif isinstance(node, ast.ImportFrom) and node.module:
                names.append(node.module)
            for name in names:
                root = name.partition(".")[0]
                if root not in sys.stdlib_module_names and root != "exactcis":
                    third_party.add(root)
    return third_party


def main() -> int:
    metadata = tomllib.loads((ROOT / "pyproject.toml").read_text(encoding="utf-8"))
    dependencies = metadata["project"].get("dependencies", [])
    extras = set(metadata["project"].get("optional-dependencies", {}))
    errors: list[str] = []
    if dependencies:
        errors.append(f"core dependency list is not empty: {dependencies}")
    imports = third_party_runtime_imports()
    if imports:
        errors.append(f"undeclared third-party runtime imports: {sorted(imports)}")
    if extras != EXPECTED_EXTRAS:
        errors.append(
            f"supported extras changed without audit policy update: {sorted(extras)}"
        )
    if errors:
        for error in errors:
            print(f"ERROR: {error}")
        return 1
    print("OK: core dependency audit (zero dependencies; stdlib-only imports)")

    with tempfile.TemporaryDirectory(prefix="exactcis-audit-") as temporary:
        requirements = Path(temporary) / "all-extras.txt"
        subprocess.run(
            [
                "uv",
                "export",
                "--frozen",
                "--no-dev",
                "--no-emit-project",
                "--all-extras",
                "--output-file",
                str(requirements),
            ],
            cwd=ROOT,
            check=True,
            stdout=subprocess.DEVNULL,
        )
        text = requirements.read_text(encoding="utf-8")
        requirement_count = len(REQUIREMENT.findall(text))
        if requirement_count == 0:
            print("ERROR: all-extras audit set is unexpectedly empty")
            return 1
        subprocess.run(
            [
                sys.executable,
                "-m",
                "pip_audit",
                "--strict",
                "--no-deps",
                "--disable-pip",
                "--requirement",
                str(requirements),
            ],
            cwd=ROOT,
            check=True,
        )
    print(
        f"OK: pip-audit covered {requirement_count} pinned packages across "
        f"extras {sorted(extras)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
