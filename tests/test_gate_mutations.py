"""Mutation evidence that the public-contract gates reject stale claims."""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).parents[1]

if not (ROOT / "tools").is_dir():
    pytest.skip("tools/ not shipped in the public sdist", allow_module_level=True)

from tools.check_capability_docs import main as check_capability_docs  # noqa: E402
from tools.check_doc_version_references import (  # noqa: E402
    main as check_doc_version_references,
)
from tools.check_method_docs import main as check_method_docs  # noqa: E402


def _copy_files(destination: Path, *relative_paths: str) -> None:
    """Copy the minimal ordinary files required by one isolated gate run."""
    for relative in relative_paths:
        source = ROOT / relative
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)


def _copy_capability_gate_tree(destination: Path) -> None:
    _copy_files(
        destination,
        "docs_md/methods.md",
        "src/exactcis/_capability.py",
        "tools/timing_evidence.json",
    )


def test_stale_version_pin_is_rejected_by_the_version_reference_gate(
    tmp_path: Path,
) -> None:
    _copy_files(
        tmp_path,
        "README.md",
        "AGENTS.md",
        "CITATION.txt",
        "src/exactcis/__about__.py",
    )
    readme = tmp_path / "README.md"
    original = readme.read_text(encoding="utf-8")
    assert "exactcis==1.1.1" in original
    readme.write_text(
        original.replace("exactcis==1.1.1", "exactcis==9.9.9", 1),
        encoding="utf-8",
    )

    assert check_doc_version_references(tmp_path) == 1


def test_altered_cap_value_is_rejected_by_the_capability_docs_gate(
    tmp_path: Path,
) -> None:
    _copy_capability_gate_tree(tmp_path)
    methods = tmp_path / "docs_md/methods.md"
    original = methods.read_text(encoding="utf-8")
    expected = "| Preparation support-width cap | `10,000,000` |"
    mutated = "| Preparation support-width cap | `10,000,001` |"
    assert expected in original
    methods.write_text(
        original.replace(expected, mutated, 1),
        encoding="utf-8",
    )

    assert check_capability_docs(tmp_path) == 1


def test_altered_timing_version_is_rejected_by_the_capability_docs_gate(
    tmp_path: Path,
) -> None:
    _copy_capability_gate_tree(tmp_path)
    evidence = tmp_path / "tools/timing_evidence.json"
    original = evidence.read_text(encoding="utf-8")
    expected = '"package_version": "1.1.0"'
    assert original.count(expected) > 1
    evidence.write_text(
        original.replace(expected, '"package_version": "9.9.9"', 1),
        encoding="utf-8",
    )

    assert check_capability_docs(tmp_path) == 1


def test_altered_method_sentence_is_rejected_by_the_method_docs_gate(
    tmp_path: Path,
) -> None:
    _copy_files(tmp_path, "docs_md/methods.md")
    methods = tmp_path / "docs_md/methods.md"
    original = methods.read_text(encoding="utf-8")
    expected = "conditional exact confidence interval"
    assert expected in original
    methods.write_text(
        original.replace(expected, "mutated confidence interval", 1),
        encoding="utf-8",
    )

    assert check_method_docs(tmp_path) == 1


def test_capability_formula_divergence_fails_the_r1_consistency_test(
    tmp_path: Path,
) -> None:
    """The R1 formula grid is executed in a fresh, intentionally bad source tree."""
    consistency_test = ROOT / "tests/test_capability.py"
    assert consistency_test.is_file()

    source = tmp_path / "src" / "exactcis"
    shutil.copytree(
        ROOT / "src" / "exactcis",
        source,
        ignore=shutil.ignore_patterns("__pycache__", "*.pyc"),
    )
    _copy_files(tmp_path, "tests/test_capability.py")
    capability = source / "_capability.py"
    original = capability.read_text(encoding="utf-8")
    expected = "return min(n1, events) - max(0, events - n0) + 1"
    assert expected in original
    capability.write_text(
        original.replace(expected, expected.replace("+ 1", "+ 2"), 1),
        encoding="utf-8",
    )

    environment = os.environ.copy()
    inherited = environment.get("PYTHONPATH")
    environment["PYTHONPATH"] = str(tmp_path / "src") + (
        os.pathsep + inherited if inherited else ""
    )
    completed = subprocess.run(
        [sys.executable, "-m", "pytest", "-q", "tests/test_capability.py"],
        cwd=tmp_path,
        check=False,
        env=environment,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )

    assert completed.returncode != 0, completed.stdout
    assert (
        "test_support_width_matches_support_bounds_on_margin_grid" in completed.stdout
    )
