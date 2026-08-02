#!/usr/bin/env python3
"""Enforce public-history, path, licence, generated-file, and notebook hygiene."""

from __future__ import annotations

import json
import re
import subprocess
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PUBLIC_EMAIL = "cheyloveday@users.noreply.github.com"
EMAIL = re.compile(r"[A-Z0-9._%+-]+@[A-Z0-9.-]+\.[A-Z]{2,}", re.IGNORECASE)
PRIVATE_DOC_TERM = re.compile(
    r"\b(?:PS4|Paper[ -]?M|JSS|Lean|ClinVar|VEP|CARF|ERDOS|hotstart)\b|manuscript",
    re.IGNORECASE,
)
DOC_PREFIXES = ("README.md", "CONTRIBUTING.md", "docs_md/", "examples/")
CONTENT_PATTERNS = {
    "macOS user path": re.compile("/" + r"Users/[^/\s]+/"),
    "Linux home path": re.compile("/" + r"home/[^/\s]+/"),
    "Windows user path": re.compile(r"[A-Za-z]:\\Users\\[^\\\s]+\\"),
    "private-network hostname": re.compile(
        r"\b(?:local"
        r"host|[A-Za-z0-9.-]+\.(?:loc"
        r"al|inter"
        r"nal|co"
        r"rp))\b",
        re.IGNORECASE,
    ),
    "private IPv4 address": re.compile(
        r"\b(?:10(?:\.\d{1,3}){3}|192\.168(?:\.\d{1,3}){2}|"
        r"172\.(?:1[6-9]|2\d|3[01])(?:\.\d{1,3}){2})\b"
    ),
    "private key": re.compile(r"-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----"),
    "GitHub token": re.compile(r"(?:gh[pousr]_|github_pat_)[A-Za-z0-9_]{20,}"),
    "OpenAI-style token": re.compile(r"\bsk-[A-Za-z0-9_-]{20,}"),
    "AWS access key": re.compile(r"\bAKIA[0-9A-Z]{16}\b"),
    "Slack token": re.compile(r"\bxox[baprs]-[A-Za-z0-9-]{10,}"),
    "private source repository": re.compile(
        r"github\.com/Chey"
        r"Loveday/ExactCIs|"
        r"\bChey"
        r"Loveday\b(?!@users\.noreply\.github\.com)",
        re.IGNORECASE,
    ),
}
DENIED_PARTS = {
    ".agents",
    ".codex",
    ".devplans",
    ".grok",
    ".mypy_cache",
    ".pytest_cache",
    ".ruff_cache",
    ".venv",
    "__pycache__",
    "_dev",
    "build",
    "dist",
    "htmlcov",
    "site",
}
DENIED_SUFFIXES = {".docx", ".pdf", ".pyc", ".whl", ".zip"}


def tracked_paths() -> tuple[str, ...]:
    completed = subprocess.run(
        ["git", "ls-files", "-z"],
        cwd=ROOT,
        check=True,
        stdout=subprocess.PIPE,
    )
    return tuple(item.decode("utf-8") for item in completed.stdout.split(b"\0") if item)


def check_hygiene() -> list[str]:
    paths = tracked_paths()
    errors: list[str] = []
    roots = subprocess.run(
        ["git", "rev-list", "--max-parents=0", "--all"],
        cwd=ROOT,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    ).stdout.splitlines()
    if len(roots) != 1:
        errors.append(f"expected one fresh-history root commit; got {len(roots)}")
    if ".secrets.baseline" in paths:
        errors.append("tracked .secrets.baseline is forbidden")

    for path in paths:
        pure = Path(path)
        if set(pure.parts) & DENIED_PARTS:
            errors.append(f"generated or private path is tracked: {path}")
        if pure.suffix.lower() in DENIED_SUFFIXES:
            errors.append(f"generated or disallowed file type is tracked: {path}")
        file_path = ROOT / path
        if file_path.is_symlink():
            errors.append(f"tracked symbolic link requires review: {path}")
        if not file_path.is_file() or file_path.stat().st_size > 2_000_000:
            continue
        try:
            text = file_path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            continue
        for label, pattern in CONTENT_PATTERNS.items():
            if pattern.search(text):
                errors.append(f"{label} in tracked file: {path}")
        emails = set(EMAIL.findall(text))
        unexpected_emails = emails - {PUBLIC_EMAIL}
        if unexpected_emails:
            errors.append(f"unreviewed email(s) in {path}: {sorted(unexpected_emails)}")
        if path.startswith(DOC_PREFIXES) and PRIVATE_DOC_TERM.search(text):
            errors.append(f"private or manuscript-only term in public prose: {path}")
        if pure.suffix == ".ipynb":
            try:
                notebook = json.loads(text)
            except json.JSONDecodeError as exc:
                errors.append(f"invalid notebook JSON in {path}: {exc}")
                continue
            if notebook.get("metadata", {}).get("widgets"):
                errors.append(f"embedded widget state in notebook: {path}")
            for index, cell in enumerate(notebook.get("cells", [])):
                if cell.get("outputs"):
                    errors.append(f"notebook output in {path}, cell {index}")
                if cell.get("attachments"):
                    errors.append(f"notebook attachment in {path}, cell {index}")

    pyproject = tomllib.loads((ROOT / "pyproject.toml").read_text(encoding="utf-8"))
    if pyproject["project"].get("license") != "MIT":
        errors.append("pyproject project.license must be MIT")
    if pyproject["project"].get("license-files") != ["LICENSE"]:
        errors.append("pyproject license-files must contain exactly LICENSE")
    licence = ROOT / "LICENSE"
    if not licence.is_file() or "MIT License" not in licence.read_text(
        encoding="utf-8"
    ):
        errors.append("MIT LICENSE file is missing or malformed")
    return errors


def main() -> int:
    errors = check_hygiene()
    if errors:
        for error in errors:
            print(f"ERROR: {error}")
        return 1
    notebooks = sum(path.endswith(".ipynb") for path in tracked_paths())
    print("OK: one-root fresh history, tracked-tree, content, and licence hygiene")
    print(f"OK: notebook inspection complete ({notebooks} tracked notebooks)")
    print(f"OK: only reviewed public email is {PUBLIC_EMAIL}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
