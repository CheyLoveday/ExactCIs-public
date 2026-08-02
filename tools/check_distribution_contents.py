#!/usr/bin/env python3
"""Fail when a wheel or sdist crosses the public release boundary."""

from __future__ import annotations

import argparse
import email.parser
import re
import tarfile
import zipfile
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Iterable

DENIED_PARTS = {
    ".agents",
    ".codex",
    ".devplans",
    ".grok",
    "_dev",
    "build",
    "htmlcov",
    "lean",
    "output",
    "replication",
    "research",
    "site",
    "tmp",
    "__pycache__",
}
DENIED_SUFFIXES = {".docx", ".pdf", ".pyc", ".zip"}
TEXT_SUFFIXES = {
    ".cff",
    ".json",
    ".lock",
    ".md",
    ".py",
    ".toml",
    ".txt",
    ".yaml",
    ".yml",
}
SECRET_PATTERNS = {
    "private key": re.compile(r"-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----"),
    "GitHub token": re.compile(r"(?:ghp|github_pat)_[A-Za-z0-9_]{20,}"),
    "OpenAI-style token": re.compile(r"\bsk-[A-Za-z0-9_-]{20,}"),
    "AWS access key": re.compile(r"\bAKIA[0-9A-Z]{16}\b"),
    "macOS absolute path": re.compile("/" + r"Users/[^/\s]+/"),
    "Windows user path": re.compile(r"[A-Za-z]:\\" + r"Users\\[^\\\s]+\\"),
}


@dataclass(frozen=True)
class Member:
    """One normalized archive member and optional bytes."""

    name: str
    data: bytes | None


def _members(path: Path) -> list[Member]:
    if path.suffix == ".whl":
        with zipfile.ZipFile(path) as archive:
            result = []
            for info in archive.infolist():
                data = None if info.is_dir() else archive.read(info)
                result.append(Member(info.filename, data))
            return result
    if path.name.endswith(".tar.gz"):
        with tarfile.open(path, "r:gz") as archive:
            result = []
            for info in archive.getmembers():
                extracted = archive.extractfile(info) if info.isfile() else None
                result.append(
                    Member(info.name, extracted.read() if extracted else None)
                )
            return result
    raise ValueError(f"unsupported distribution artefact: {path}")


def _relative_name(path: Path, name: str) -> str:
    pure = PurePosixPath(name)
    if pure.is_absolute() or ".." in pure.parts or "\\" in name:
        raise ValueError(f"unsafe archive member path in {path.name}: {name!r}")
    if path.name.endswith(".tar.gz") and len(pure.parts) > 1:
        return PurePosixPath(*pure.parts[1:]).as_posix()
    return pure.as_posix()


def inspect_distribution(path: Path) -> list[str]:
    """Return all public-boundary errors for one artefact."""
    errors: list[str] = []
    members = _members(path)
    relative: list[tuple[str, bytes | None]] = []
    for member in members:
        try:
            name = _relative_name(path, member.name)
        except ValueError as exc:
            errors.append(str(exc))
            continue
        parts = set(PurePosixPath(name).parts)
        if parts & DENIED_PARTS:
            errors.append(f"{path.name}: denied path {name}")
        if PurePosixPath(name).suffix.lower() in DENIED_SUFFIXES:
            errors.append(f"{path.name}: denied file type {name}")
        relative.append((name, member.data))

    names = {name for name, _ in relative}
    metadata_names: list[str]
    if path.suffix == ".whl":
        required = {
            "exactcis/__init__.py",
            "exactcis/__about__.py",
            "exactcis/py.typed",
        }
        missing = sorted(required - names)
        if missing:
            errors.append(f"{path.name}: missing wheel members {missing}")
        allowed_prefixes = ("exactcis/", "exactcis-")
        for name in names:
            if name and not name.startswith(allowed_prefixes):
                errors.append(f"{path.name}: non-package wheel member {name}")
        metadata_names = [
            name for name in names if name.endswith(".dist-info/METADATA")
        ]
        if not any(name.endswith(".dist-info/licenses/LICENSE") for name in names):
            errors.append(f"{path.name}: wheel does not contain the MIT licence file")
    else:
        required = {"LICENSE", "README.md", "pyproject.toml", "src/exactcis/py.typed"}
        missing = sorted(required - names)
        if missing:
            errors.append(f"{path.name}: missing sdist members {missing}")
        metadata_names = [name for name in names if name == "PKG-INFO"]

    if len(metadata_names) != 1:
        errors.append(
            f"{path.name}: expected exactly one core metadata file; "
            f"got {metadata_names}"
        )
    else:
        metadata_data = dict(relative)[metadata_names[0]]
        if metadata_data is None:
            errors.append(f"{path.name}: metadata member is not a regular file")
        else:
            message = email.parser.BytesParser().parsebytes(metadata_data)
            expected_fields = {
                "Name": "exactcis",
                "Version": "1.0.0rc1",
                "License-Expression": "MIT",
            }
            for field, expected in expected_fields.items():
                if message.get(field) != expected:
                    errors.append(
                        f"{path.name}: {field} is {message.get(field)!r}, "
                        f"expected {expected!r}"
                    )
            python_specifiers = {
                item.strip() for item in message.get("Requires-Python", "").split(",")
            }
            if python_specifiers != {">=3.11", "<3.14"}:
                errors.append(
                    f"{path.name}: Requires-Python is "
                    f"{message.get('Requires-Python')!r}, expected >=3.11,<3.14"
                )
            unconditional = [
                requirement
                for requirement in message.get_all("Requires-Dist", [])
                if "; extra ==" not in requirement
            ]
            if unconditional:
                errors.append(
                    f"{path.name}: core metadata contains runtime dependencies "
                    f"{unconditional}"
                )
            if "LICENSE" not in message.get_all("License-File", []):
                errors.append(f"{path.name}: core metadata omits License-File: LICENSE")

    for name, data in relative:
        if data is None or PurePosixPath(name).suffix.lower() not in TEXT_SUFFIXES:
            continue
        try:
            text = data.decode("utf-8")
        except UnicodeDecodeError:
            errors.append(f"{path.name}: non-UTF-8 text member {name}")
            continue
        for label, pattern in SECRET_PATTERNS.items():
            if pattern.search(text):
                errors.append(f"{path.name}: {label} pattern in {name}")
    return errors


def inspect_distributions(paths: Iterable[Path]) -> list[str]:
    """Inspect all supplied artefacts and enforce one wheel plus one sdist."""
    materialized = tuple(paths)
    errors: list[str] = []
    if sum(path.suffix == ".whl" for path in materialized) != 1:
        errors.append("expected exactly one wheel")
    if sum(path.name.endswith(".tar.gz") for path in materialized) != 1:
        errors.append("expected exactly one sdist")
    for path in materialized:
        if not path.is_file():
            errors.append(f"artefact does not exist: {path}")
            continue
        errors.extend(inspect_distribution(path))
    return errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("artefacts", nargs="+", type=Path)
    args = parser.parse_args()
    errors = inspect_distributions(args.artefacts)
    if errors:
        for error in errors:
            print(f"ERROR: {error}")
        return 1
    for path in args.artefacts:
        print(f"OK: {path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
