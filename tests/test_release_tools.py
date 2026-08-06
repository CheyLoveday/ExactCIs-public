"""Focused unit checks for public release-boundary tools.

These tests require the developer ``tools/`` tree (git checkout). They are
skipped when ``tools/`` is absent, as in the published sdist.
"""

from __future__ import annotations

import re
import subprocess
import sys
import zipfile
from pathlib import Path

import pytest

ROOT = Path(__file__).parents[1]
TOOLS = ROOT / "tools"

# Public sdist intentionally omits tools/; skip the whole module there.
if not TOOLS.is_dir():
    pytest.skip("tools/ not shipped in the public sdist", allow_module_level=True)

from tools.check_distribution_contents import inspect_distribution  # noqa: E402
from tools.run_installed_smoke import main as run_installed_smoke  # noqa: E402
from tools.run_readme_examples import extract_examples  # noqa: E402


def _workflow_jobs(path: Path) -> dict[str, tuple[str, ...]]:
    """Parse top-level job blocks without adding a YAML runtime dependency."""
    lines = path.read_text(encoding="utf-8").splitlines()
    jobs_index = lines.index("jobs:")
    jobs: dict[str, list[str]] = {}
    current: list[str] | None = None
    for line in lines[jobs_index + 1 :]:
        if line and not line.startswith(" "):
            break
        match = re.fullmatch(r"  (?P<name>[A-Za-z0-9_-]+):", line)
        if match is not None:
            current = []
            jobs[match.group("name")] = current
        elif current is not None:
            current.append(line)
    return {name: tuple(block) for name, block in jobs.items()}


def _workflow_steps(job: tuple[str, ...]) -> tuple[tuple[str, ...], ...]:
    """Return the step blocks from one parsed workflow job."""
    steps_line = next(line for line in job if line.strip() == "steps:")
    item_indent = len(steps_line) - len(steps_line.lstrip()) + 2
    steps: list[list[str]] = []
    current: list[str] | None = None
    for line in job[job.index(steps_line) + 1 :]:
        indent = len(line) - len(line.lstrip())
        if line.strip() and indent < item_indent:
            break
        if indent == item_indent and line.lstrip().startswith("- "):
            current = [line]
            steps.append(current)
        elif current is not None:
            current.append(line)
    return tuple(tuple(step) for step in steps)


def _has_full_history_checkout(job: tuple[str, ...]) -> bool:
    for step in _workflow_steps(job):
        if not any("uses: actions/checkout@" in line for line in step):
            continue
        if any(re.fullmatch(r"\s*fetch-depth:\s*0\s*(?:#.*)?", line) for line in step):
            return True
    return False


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
    if not (ROOT / ".git").exists():
        pytest.skip("public-tree checker requires a git checkout")
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
    if not (ROOT / ".git").exists():
        pytest.skip("version consistency checker expects a git worktree")
    if not (ROOT / ".github" / "workflows" / "release.yml").exists():
        pytest.skip("release workflow not present (sdist omits .github)")
    completed = subprocess.run(
        [sys.executable, "tools/check_version_consistency.py"],
        cwd=ROOT,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    assert completed.returncode == 0, completed.stdout


@pytest.mark.parametrize("workflow_name", ("ci.yml", "release.yml"))
def test_history_secret_steps_require_full_clone(workflow_name: str) -> None:
    workflow = ROOT / ".github" / "workflows" / workflow_name
    jobs = _workflow_jobs(workflow)
    invoking = {
        name: block
        for name, block in jobs.items()
        if any("check_history_secrets.py" in line for line in block)
    }
    assert invoking, f"{workflow_name} does not invoke the history-secrets gate"
    for name, block in invoking.items():
        assert _has_full_history_checkout(block), (
            f"{workflow_name} job {name!r} invokes check_history_secrets.py "
            "without actions/checkout fetch-depth: 0"
        )


def test_distribution_checker_rejects_private_paths(tmp_path: Path) -> None:
    wheel = tmp_path / "bad.whl"
    with zipfile.ZipFile(wheel, "w") as archive:
        archive.writestr("exactcis/__init__.py", "")
        archive.writestr("exactcis/__about__.py", "")
        archive.writestr("exactcis/py.typed", "")
        archive.writestr("_dev/private.py", "")
    errors = inspect_distribution(wheel)
    assert any("denied path" in error for error in errors)
