#!/usr/bin/env python3
"""Require one coherent candidate version across code and release metadata."""

from __future__ import annotations

import argparse
import ast
import re
import subprocess
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ABOUT = ROOT / "src" / "exactcis" / "__about__.py"
SOURCE_REVISION = "".join(("ba671716", "7fe81d92", "9b02a958", "0d0fcc7b", "c86b830c"))


def package_version() -> str:
    """Read the sole package version assignment without importing the package."""
    tree = ast.parse(ABOUT.read_text(encoding="utf-8"), filename=str(ABOUT))
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
        raise ValueError(
            f"expected one literal __version__ assignment; got {assignments}"
        )
    return assignments[0]


def candidate_tag(version: str) -> str:
    """Convert one PEP 440 release candidate into the public tag convention."""
    match = re.fullmatch(r"(\d+)\.(\d+)\.(\d+)rc(\d+)", version)
    if not match:
        raise ValueError(f"version is not a release candidate: {version!r}")
    major, minor, patch, candidate = match.groups()
    return f"v{major}.{minor}.{patch}-rc.{candidate}"


def _scalar(text: str, key: str) -> str | None:
    matches = re.findall(
        rf"(?m)^{re.escape(key)}:\s*[\"']?([^\"'\n]+?)[\"']?\s*$", text
    )
    return matches[0].strip() if len(matches) == 1 else None


def check(release_tag: str | None = None) -> list[str]:
    version = package_version()
    tag = candidate_tag(version)
    errors: list[str] = []

    pyproject = tomllib.loads((ROOT / "pyproject.toml").read_text(encoding="utf-8"))
    if pyproject.get("tool", {}).get("hatch", {}).get("version", {}).get("path") != (
        "src/exactcis/__about__.py"
    ):
        errors.append("Hatch version path does not name src/exactcis/__about__.py")
    if pyproject["project"].get("dynamic") != ["version"]:
        errors.append(
            "project.version must be dynamic and sourced only from __about__.py"
        )

    sys.path.insert(0, str(ROOT / "src"))
    import exactcis  # noqa: PLC0415

    if exactcis.__version__ != version:
        errors.append(
            f"package root version {exactcis.__version__!r} differs from {version!r}"
        )

    changelog = (ROOT / "CHANGELOG.md").read_text(encoding="utf-8")
    expected_heading = f"## [{version}] - Unreleased"
    if changelog.count(expected_heading) != 1:
        errors.append(
            f"CHANGELOG must contain exactly one {expected_heading!r} heading"
        )
    if "no package-index publication or release tag is implied" not in changelog:
        errors.append("CHANGELOG does not state the candidate's unreleased status")

    cff = (ROOT / "CITATION.cff").read_text(encoding="utf-8")
    expected_cff = {
        "cff-version": "1.2.0",
        "title": "ExactCIs",
        "type": "software",
        "version": version,
        "commit": SOURCE_REVISION,
        "license": "MIT",
    }
    for key, expected in expected_cff.items():
        if _scalar(cff, key) != expected:
            errors.append(f"CITATION.cff {key} does not equal {expected!r}")
    forbidden_cff = ("doi:", "date-released:", "repository-code:")
    if any(re.search(rf"(?m)^\s*{re.escape(key)}", cff) for key in forbidden_cff):
        errors.append("CITATION.cff invents a DOI, release date, or public repository")

    citation_text = (ROOT / "CITATION.txt").read_text(encoding="utf-8")
    if f"Version: {version} (unreleased release candidate)" not in citation_text:
        errors.append("CITATION.txt version or release status differs")
    if f"Scientific source revision: {SOURCE_REVISION}" not in citation_text:
        errors.append("CITATION.txt source revision differs")

    workflow = (ROOT / ".github" / "workflows" / "release.yml").read_text(
        encoding="utf-8"
    )
    default_match = re.search(
        r"(?ms)^\s{6}candidate_tag:\n.*?^\s{8}default:\s*([^\s]+)\s*$",
        workflow,
    )
    workflow_tag = default_match.group(1) if default_match else None
    if workflow_tag != tag:
        errors.append(
            f"release workflow candidate input is {workflow_tag!r}, expected {tag!r}"
        )
    if f"release-{tag}-through-testpypi" not in workflow:
        errors.append(
            "release workflow authorization phrase differs from candidate tag"
        )

    if release_tag is not None:
        if release_tag != tag:
            errors.append(f"requested release tag {release_tag!r} differs from {tag!r}")
        tags = subprocess.run(
            ["git", "tag", "--points-at", "HEAD"],
            cwd=ROOT,
            check=True,
            text=True,
            stdout=subprocess.PIPE,
        ).stdout.splitlines()
        if release_tag not in tags:
            errors.append(f"release tag {release_tag!r} does not point at HEAD")
    return errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--release-tag")
    args = parser.parse_args()
    errors = check(args.release_tag)
    if errors:
        for error in errors:
            print(f"ERROR: {error}")
        return 1
    version = package_version()
    print(
        f"OK: version {version} and tag convention {candidate_tag(version)} agree "
        "across package, changelog, citations, and release workflow"
    )
    if args.release_tag is None:
        print("OK: local candidate check did not require or create a release tag")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
