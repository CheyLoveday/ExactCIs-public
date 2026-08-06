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

# Published 1.0.0 and 1.1.0 artefacts truthfully retain this scientific-source
# lineage.  Model B makes the public repository canonical from 1.1.1 onward;
# do not retroactively relabel the old files as public-release provenance.
HISTORICAL_SCIENTIFIC_SOURCE_SHA = "".join(
    ("ba671716", "7fe81d92", "9b02a958", "0d0fcc7b", "c86b830c")
)
GRANDFATHERED_VERSION_CORES = frozenset({(1, 0, 0), (1, 1, 0)})
MODEL_B_FIRST_VERSION = (1, 1, 1)
PUBLIC_REPOSITORY = "https://github.com/CheyLoveday/ExactCIs-public"

# Before a post-1.0.0 release tag exists, Model B requires this explicit CFF
# placeholder. At release time ``--release-tag`` resolves the tag with
# ``git rev-list -n 1``; the tag, not an in-tree SHA, is the published
# revision authority.
UNRELEASED_COMMIT_PLACEHOLDER = "UNRELEASED"


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
    """Convert a package version into the public git tag convention."""
    rc = re.fullmatch(r"(\d+)\.(\d+)\.(\d+)rc(\d+)", version)
    if rc:
        major, minor, patch, candidate = rc.groups()
        return f"v{major}.{minor}.{patch}-rc.{candidate}"
    final = re.fullmatch(r"(\d+)\.(\d+)\.(\d+)", version)
    if final:
        major, minor, patch = final.groups()
        return f"v{major}.{minor}.{patch}"
    raise ValueError(f"unsupported version for tagging: {version!r}")


def version_core(version: str) -> tuple[int, int, int]:
    """Return the comparable release tuple, accepting the package RC spelling."""
    match = re.fullmatch(r"(\d+)\.(\d+)\.(\d+)(?:rc\d+)?", version)
    if match is None:
        raise ValueError(f"unsupported package version: {version!r}")
    major, minor, patch = (int(part) for part in match.groups())
    return major, minor, patch


def is_grandfathered_version(version: str) -> bool:
    """Whether published historical citation semantics apply to ``version``."""
    return version_core(version) in GRANDFATHERED_VERSION_CORES


def uses_model_b(version: str) -> bool:
    """Whether public-release provenance is required for ``version``."""
    return version_core(version) >= MODEL_B_FIRST_VERSION


def _scalar(text: str, key: str) -> str | None:
    matches = re.findall(
        rf"(?m)^{re.escape(key)}:\s*[\"']?([^\"'\n]+?)[\"']?\s*$", text
    )
    return matches[0].strip() if len(matches) == 1 else None


def _has_key(text: str, key: str) -> bool:
    """Whether a top-level CFF key is present, including duplicate keys."""
    return re.search(rf"(?m)^\s*{re.escape(key)}:", text) is not None


def citation_cff_errors(
    cff: str,
    version: str,
    *,
    is_unreleased: bool,
    release_tag: str | None,
    tag_commit: str | None,
) -> list[str]:
    """Return CFF metadata/provenance failures for one package version.

    Model B is deliberately explicit: `commit: "UNRELEASED"` is valid only
    while the matching changelog heading is unreleased. A published release
    uses its tag as revision authority, so an in-tree ``commit:`` key would be
    self-referential or stale.
    """
    errors: list[str] = []
    expected_cff = {
        "cff-version": "1.2.0",
        "title": "ExactCIs",
        "type": "software",
        "version": version,
        "license": "MIT",
    }
    for key, expected in expected_cff.items():
        if _scalar(cff, key) != expected:
            errors.append(f"CITATION.cff {key} does not equal {expected!r}")
    if re.search(r"(?m)^\s*doi:", cff):
        errors.append("CITATION.cff invents a DOI")

    commit = _scalar(cff, "commit")
    if is_grandfathered_version(version):
        if commit != HISTORICAL_SCIENTIFIC_SOURCE_SHA:
            errors.append(
                "CITATION.cff historical scientific-source commit differs from "
                f"{HISTORICAL_SCIENTIFIC_SOURCE_SHA!r}"
            )
        return errors

    if not uses_model_b(version):
        errors.append(
            f"version {version!r} is neither a grandfathered release nor Model B"
        )
        return errors

    if is_unreleased:
        if release_tag is not None:
            errors.append("an unreleased Model B version must not name a release tag")
        if commit != UNRELEASED_COMMIT_PLACEHOLDER:
            errors.append(
                "CITATION.cff commit must equal the documented unreleased "
                f"placeholder {UNRELEASED_COMMIT_PLACEHOLDER!r}"
            )
        return errors

    if _has_key(cff, "commit"):
        errors.append(
            "CITATION.cff commit must be absent for published Model B "
            "(would be self-referential or stale)"
        )
    for key in ("date-released", "repository-code"):
        if _scalar(cff, key) is None:
            errors.append(f"CITATION.cff {key} is required for published Model B")
    if release_tag is not None and (
        tag_commit is None or not re.fullmatch(r"[0-9a-f]{40}", tag_commit)
    ):
        errors.append("release tag did not resolve to one 40-character commit")
    return errors


def citation_text_errors(
    citation_text: str,
    version: str,
    *,
    is_unreleased: bool,
    cff_commit: str | None,
) -> list[str]:
    """Return CITATION.txt failures for one package version and release state."""
    errors: list[str] = []
    tag = candidate_tag(version)
    unreleased_citation = f"Version: {version} (unreleased release candidate)"
    published_rc_citation = f"Version: {version} (release candidate)"
    final_citation = f"Version: {version}"
    pypi_ref = f"exactcis=={version}"
    has_tag = tag in citation_text or f"tagged {tag}" in citation_text
    has_pypi = pypi_ref in citation_text
    if unreleased_citation in citation_text:
        unreleased_note = (
            "No DOI, archive identifier, publication date, or release "
            "tag has been assigned."
        )
        if unreleased_note not in citation_text:
            errors.append("CITATION.txt unreleased disclaimer differs")
    elif published_rc_citation in citation_text:
        if not has_tag and not has_pypi:
            errors.append("CITATION.txt published status is incomplete")
    elif final_citation in citation_text and re.search(
        rf"(?m)^Version:\s*{re.escape(version)}\s*$", citation_text
    ):
        if not has_tag or not has_pypi:
            errors.append("CITATION.txt final release must name tag and PyPI version")
    else:
        errors.append("CITATION.txt version or release status differs")

    if is_grandfathered_version(version):
        if (
            f"Scientific source revision: {HISTORICAL_SCIENTIFIC_SOURCE_SHA}"
            not in citation_text
        ):
            errors.append("CITATION.txt historical scientific-source revision differs")
    elif uses_model_b(version):
        if is_unreleased:
            if f"Public repository revision: {cff_commit}" not in citation_text:
                errors.append(
                    "CITATION.txt public repository revision differs from CFF"
                )
        else:
            expected_lines = (
                f"Public repository: {PUBLIC_REPOSITORY}",
                f"Public tag: {tag}",
                f"PyPI: {pypi_ref}",
            )
            for line in expected_lines:
                if re.search(rf"(?m)^{re.escape(line)}$", citation_text) is None:
                    errors.append(f"CITATION.txt published Model B is missing {line!r}")
            if re.search(r"(?m)^[^\n]*\b[0-9a-f]{40}\b[^\n]*$", citation_text):
                errors.append(
                    "CITATION.txt published Model B must not name a revision SHA"
                )
    return errors


def _git_output(*arguments: str) -> str:
    """Run a deterministic git query rooted at this checkout."""
    completed = subprocess.run(
        ["git", *arguments],
        cwd=ROOT,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if completed.returncode != 0:
        detail = completed.stderr.strip() or completed.stdout.strip()
        raise ValueError(f"git {' '.join(arguments)} failed: {detail}")
    return completed.stdout.strip()


def release_tag_commit(release_tag: str) -> str:
    """Resolve exactly the commit a requested release tag names."""
    commit = _git_output("rev-list", "-n", "1", release_tag)
    if not re.fullmatch(r"[0-9a-f]{40}", commit):
        raise ValueError(f"release tag {release_tag!r} did not resolve to a commit")
    return commit


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
    unreleased_heading = f"## [{version}] - Unreleased"
    published_heading = re.search(
        rf"(?m)^## \[{re.escape(version)}\] - (\d{{4}}-\d{{2}}-\d{{2}})$",
        changelog,
    )
    if changelog.count(unreleased_heading) == 1:
        if "no package-index publication or release tag is implied" not in changelog:
            errors.append("CHANGELOG does not state the candidate's unreleased status")
    elif published_heading is not None:
        if changelog.count(published_heading.group(0)) != 1:
            errors.append(
                f"CHANGELOG must contain exactly one dated {version!r} heading"
            )
        if (
            f"`exactcis=={version}`" not in changelog
            and f"exactcis=={version}" not in changelog
        ):
            errors.append(
                "published CHANGELOG must name the PyPI project version "
                f"exactcis=={version}"
            )
        if tag not in changelog:
            errors.append(f"published CHANGELOG must name the release tag {tag!r}")
    else:
        errors.append(
            "CHANGELOG must contain exactly one "
            f"{unreleased_heading!r} heading or a dated "
            f"'## [{version}] - YYYY-MM-DD' published heading"
        )

    cff = (ROOT / "CITATION.cff").read_text(encoding="utf-8")
    is_unreleased = changelog.count(unreleased_heading) == 1
    tag_commit: str | None = None
    if uses_model_b(version) and release_tag is not None:
        try:
            tag_commit = release_tag_commit(release_tag)
        except ValueError as exc:
            errors.append(str(exc))
    errors.extend(
        citation_cff_errors(
            cff,
            version,
            is_unreleased=is_unreleased,
            release_tag=release_tag,
            tag_commit=tag_commit,
        )
    )

    citation_text = (ROOT / "CITATION.txt").read_text(encoding="utf-8")
    errors.extend(
        citation_text_errors(
            citation_text,
            version,
            is_unreleased=is_unreleased,
            cff_commit=_scalar(cff, "commit"),
        )
    )

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
        try:
            tags = _git_output("tag", "--points-at", "HEAD").splitlines()
        except ValueError as exc:
            errors.append(str(exc))
        else:
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
        print("OK: local version check did not require or create a release tag")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
