#!/usr/bin/env python3
"""Fail on detect-secrets findings anywhere in reachable public history."""

from __future__ import annotations

import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path, PurePosixPath

from detect_secrets.core.scan import scan_file
from detect_secrets.settings import default_settings

ROOT = Path(__file__).resolve().parents[1]
FROZEN_SOURCE_SHA = "".join(
    ("d4ce3a5b", "ce501eb6", "16ef6abf", "38107a6f", "917319c4")
)
SOURCE_REVISION = re.compile(r'^\s*"source_revision"\s*:\s*"[0-9a-f]{40}"\s*,?\s*$')


def _git(*args: str, text: bool = True) -> str | bytes:
    completed = subprocess.run(
        ["git", *args],
        cwd=ROOT,
        check=True,
        text=text,
        stdout=subprocess.PIPE,
    )
    return completed.stdout


def _allowed_reference_revision(path: str, line: str) -> bool:
    if path.startswith("tests/references/") and SOURCE_REVISION.match(line):
        return FROZEN_SOURCE_SHA in line
    allowed_citation_lines = {
        "CITATION.cff": f'commit: "{FROZEN_SOURCE_SHA}"',
        "CITATION.txt": f"Scientific source revision: {FROZEN_SOURCE_SHA}",
    }
    return line.strip() == allowed_citation_lines.get(path)


def _current_tree_errors() -> list[str]:
    completed = subprocess.run(
        [
            sys.executable,
            "-m",
            "detect_secrets",
            "scan",
            ".",
        ],
        cwd=ROOT,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    )
    result = json.loads(completed.stdout)["results"]
    errors: list[str] = []
    for path, findings in result.items():
        lines = (ROOT / path).read_text(encoding="utf-8").splitlines()
        for finding in findings:
            line_number = finding["line_number"]
            line = lines[line_number - 1] if 0 < line_number <= len(lines) else ""
            if _allowed_reference_revision(path, line):
                continue
            errors.append(f"current tree {path}:{line_number} {finding['type']}")
    return errors


def _history_errors() -> tuple[list[str], int, int]:
    revisions = tuple(str(_git("rev-list", "--all")).splitlines())
    scanned: set[tuple[str, str]] = set()
    errors: list[str] = []
    with tempfile.TemporaryDirectory(prefix="exactcis-history-") as temporary:
        temporary_root = Path(temporary)
        with default_settings():
            for revision in revisions:
                tree = bytes(
                    _git("ls-tree", "-r", "-z", "--full-tree", revision, text=False)
                )
                for entry in tree.split(b"\0"):
                    if not entry:
                        continue
                    metadata, raw_path = entry.split(b"\t", 1)
                    _mode, object_type, object_id = metadata.decode("ascii").split()
                    if object_type != "blob":
                        continue
                    path = raw_path.decode("utf-8")
                    pure = PurePosixPath(path)
                    if pure.is_absolute() or ".." in pure.parts:
                        errors.append(
                            f"{revision[:12]} unsafe historical path {path!r}"
                        )
                        continue
                    identity = (object_id, path)
                    if identity in scanned:
                        continue
                    scanned.add(identity)
                    data = bytes(_git("cat-file", "blob", object_id, text=False))
                    materialized = temporary_root.joinpath(*pure.parts)
                    materialized.parent.mkdir(parents=True, exist_ok=True)
                    materialized.write_bytes(data)
                    try:
                        lines = data.decode("utf-8").splitlines()
                    except UnicodeDecodeError:
                        lines = []
                    for finding in scan_file(str(materialized)):
                        line_number = finding.line_number
                        line = (
                            lines[line_number - 1]
                            if 0 < line_number <= len(lines)
                            else ""
                        )
                        if _allowed_reference_revision(path, line):
                            continue
                        errors.append(
                            f"{revision[:12]} {path}:{line_number} {finding.type}"
                        )
    return errors, len(revisions), len(scanned)


def main() -> int:
    errors = _current_tree_errors()
    history_errors, revisions, blobs = _history_errors()
    errors.extend(history_errors)
    if errors:
        for error in errors:
            print(f"ERROR: potential secret: {error}")
        return 1
    print(
        f"OK: detect-secrets scanned the current tree and {blobs} unique "
        f"path/blob pairs across {revisions} public commits"
    )
    print("OK: reviewed allowlist is limited to the frozen scientific source SHA")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
