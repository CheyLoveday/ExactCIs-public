"""Focused unit checks for public release-boundary tools."""

from __future__ import annotations

import subprocess
import sys
import zipfile
from pathlib import Path

from tools.check_distribution_contents import inspect_distribution
from tools.run_installed_smoke import main as run_installed_smoke
from tools.run_readme_examples import extract_examples

ROOT = Path(__file__).parents[1]


def test_readme_has_one_executable_marked_example() -> None:
    examples = extract_examples((ROOT / "README.md").read_text(encoding="utf-8"))
    assert len(examples) == 1
    compile(examples[0], "README.md", "exec")


def test_installed_smoke_contract_passes_against_source() -> None:
    assert run_installed_smoke() == 0


def test_method_documentation_matches_registry() -> None:
    completed = subprocess.run(
        [sys.executable, "tools/check_method_docs.py"],
        cwd=ROOT,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    assert completed.returncode == 0, completed.stdout


def test_public_tree_checker_passes_tracked_tree() -> None:
    completed = subprocess.run(
        [sys.executable, "tools/check_public_tree.py"],
        cwd=ROOT,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    assert completed.returncode == 0, completed.stdout


def test_release_version_metadata_is_consistent() -> None:
    completed = subprocess.run(
        [sys.executable, "tools/check_version_consistency.py"],
        cwd=ROOT,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    assert completed.returncode == 0, completed.stdout


def test_distribution_checker_rejects_private_paths(tmp_path: Path) -> None:
    wheel = tmp_path / "bad.whl"
    with zipfile.ZipFile(wheel, "w") as archive:
        archive.writestr("exactcis/__init__.py", "")
        archive.writestr("exactcis/__about__.py", "")
        archive.writestr("exactcis/py.typed", "")
        archive.writestr("_dev/private.py", "")
    errors = inspect_distribution(wheel)
    assert any("denied path" in error for error in errors)
