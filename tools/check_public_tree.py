#!/usr/bin/env python3
"""Verify the clean public repository and retained import graph."""

from __future__ import annotations

import ast
import importlib
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_TOP_LEVEL = {
    ".github",
    ".gitignore",
    ".pre-commit-config.yaml",
    "CHANGELOG.md",
    "CITATION.cff",
    "CITATION.txt",
    "CONTRIBUTING.md",
    "LICENSE",
    "Makefile",
    "README.md",
    "docs_md",
    "examples",
    "mkdocs.yml",
    "pyproject.toml",
    "src",
    "tests",
    "tools",
    "uv.lock",
}
DENIED_PARTS = {
    ".agents",
    ".codex",
    ".devplans",
    ".grok",
    "_dev",
    "lean",
    "output",
    "replication",
    "research",
    "results",
    "site",
    "tmp",
    "__pycache__",
}
FORBIDDEN_IMPORTS = (
    "exactcis._internal",
    "exactcis.analysis",
    "exactcis.cli",
    "exactcis.compute",
    "exactcis.evidence",
    "exactcis.visualization",
    "exactcis.estimation.odds_ratio.pooled_cmle",
)
FORBIDDEN_SOURCE_PROFILE_PATHS = {
    "src/exactcis/estimation/odds_ratio/pooled_cmle.py",
}
TEXT_PATTERNS = {
    "macOS absolute path": re.compile("/" + r"Users/[^/\s]+/"),
    "Windows user path": re.compile(r"[A-Za-z]:\\" + r"Users\\[^\\\s]+\\"),
    "private key": re.compile(r"-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----"),
    "GitHub token": re.compile(r"(?:ghp|github_pat)_[A-Za-z0-9_]{20,}"),
    "OpenAI-style token": re.compile(r"\bsk-[A-Za-z0-9_-]{20,}"),
}


def tracked_paths() -> tuple[str, ...]:
    completed = subprocess.run(
        ["git", "ls-files"],
        cwd=ROOT,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    )
    return tuple(line for line in completed.stdout.splitlines() if line)


def _module_exists(module: str) -> bool:
    relative = Path("src") / Path(*module.split("."))
    return (ROOT / relative).with_suffix(".py").is_file() or (
        ROOT / relative / "__init__.py"
    ).is_file()


def _import_errors(paths: tuple[str, ...]) -> list[str]:
    errors: list[str] = []
    for path in paths:
        if not path.startswith("src/exactcis/") or not path.endswith(".py"):
            continue
        tree = ast.parse((ROOT / path).read_text(encoding="utf-8"), filename=path)
        for node in ast.walk(tree):
            modules: list[str] = []
            if isinstance(node, ast.Import):
                modules.extend(alias.name for alias in node.names)
            elif isinstance(node, ast.ImportFrom) and node.module:
                modules.append(node.module)
            for module in modules:
                if module.startswith(FORBIDDEN_IMPORTS):
                    errors.append(f"{path}: forbidden import {module}")
                if module.startswith("exactcis") and not _module_exists(module):
                    errors.append(f"{path}: unresolved retained import {module}")
    return errors


def check_tree() -> list[str]:
    """Return all tracked-boundary, content, import, and root-API errors."""
    paths = tracked_paths()
    errors: list[str] = []
    for path in paths:
        pure = Path(path)
        if path in FORBIDDEN_SOURCE_PROFILE_PATHS:
            errors.append(f"private pooled-profile implementation is retained: {path}")
        if pure.parts[0] not in ALLOWED_TOP_LEVEL:
            errors.append(f"disallowed top-level path: {path}")
        if set(pure.parts) & DENIED_PARTS:
            errors.append(f"denied tracked path: {path}")
        if pure.suffix.lower() in {".docx", ".pdf", ".pyc", ".whl", ".zip"}:
            errors.append(f"denied tracked file type: {path}")
        file_path = ROOT / path
        if file_path.is_symlink():
            errors.append(f"tracked symbolic link requires review: {path}")
        if file_path.is_file() and file_path.stat().st_size <= 2_000_000:
            try:
                text = file_path.read_text(encoding="utf-8")
            except UnicodeDecodeError:
                continue
            for label, pattern in TEXT_PATTERNS.items():
                if pattern.search(text):
                    errors.append(f"{label} in tracked file: {path}")
    docs_roots = [name for name in ("docs", "docs_md") if (ROOT / name).is_dir()]
    if docs_roots != ["docs_md"]:
        errors.append(
            f"expected exactly docs_md as documentation root; got {docs_roots}"
        )
    errors.extend(_import_errors(paths))

    sys.path.insert(0, str(ROOT / "src"))
    package = importlib.import_module("exactcis")
    actual = {name for name in vars(package) if not name.startswith("_")}
    expected = {name for name in package.__all__ if not name.startswith("_")}
    if actual != expected:
        errors.append(
            f"root namespace differs from __all__: extra={sorted(actual - expected)}, "
            f"missing={sorted(expected - actual)}"
        )
    forbidden_profile_exports = {
        "ci_conditional_profile_or",
        "cmle_common_beta",
        "pooled_conditional_or",
        "profile_likelihood_ci_or",
    }
    leaked_profile_exports = actual & forbidden_profile_exports
    if leaked_profile_exports:
        errors.append(
            "private pooled-profile symbols leaked at package root: "
            f"{sorted(leaked_profile_exports)}"
        )
    return errors


def main() -> int:
    errors = check_tree()
    if errors:
        for error in errors:
            print(f"ERROR: {error}")
        return 1
    print("OK: public tree and retained import graph")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
