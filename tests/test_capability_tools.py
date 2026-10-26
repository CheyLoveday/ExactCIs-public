"""Real diagnostic child execution and preservation of the last complete stage."""

from pathlib import Path

import pytest

ROOT = Path(__file__).parents[1]
TOOLS_PRESENT = (ROOT / "tools").is_dir()
pytestmark = pytest.mark.skipif(
    not TOOLS_PRESENT, reason="capability measurement tools are repository-only"
)
if TOOLS_PRESENT:
    from tools.unconditional_oracle.measure_capability import (
        cases,
        checkpoint,
        run_case,
        timeout_result,
    )


def test_real_worker_finishes_a_small_scientific_case():
    row = run_case((1, 1, (1, 0)), 10)
    assert row["status"] == "complete"
    assert row["cell_comparisons"]
    assert row["topology"]["events"]
    assert row["counts"]


def test_real_bounded_large_attempt_preserves_status_and_refusal():
    row = run_case((4, 4, (0, 2)), 1)
    assert row["status"] in (
        "complete",
        "resource_refused",
        "topology_timeout",
        "lane_timeout",
    )
    if row["status"] != "complete":
        assert row["reason"]
    if row["status"] == "topology_timeout":
        assert row["counts"] is None
        assert row["peak_rss_bytes"] is None


def test_incomplete_checkpoint_cannot_destroy_a_completed_stage(tmp_path, monkeypatch):
    path = tmp_path / "stage.json"
    checkpoint(path, {"completed_stage": 1})
    previous = path.read_bytes()

    def fail_replace(*args):
        raise OSError("injected interruption before atomic replacement")

    monkeypatch.setattr(Path, "replace", fail_replace)
    with pytest.raises(OSError):
        checkpoint(path, {"completed_stage": 2})
    assert path.read_bytes() == previous


def test_declared_attempt_domain_is_complete_and_bounded():
    assert len(cases(6)) == 156
    for value in (True, 1, 7):
        with pytest.raises(ValueError):
            cases(value)


@pytest.mark.parametrize(
    "status", ["complete", "resource_refused", "topology_complete"]
)
def test_timeout_preserves_a_terminal_checkpoint_and_marks_only_unfinished_lanes(
    tmp_path, status
):
    path = tmp_path / "stage.json"
    row = {"status": status, "reason": "retained exact refusal", "counts": {"add": 3}}
    checkpoint(path, row)
    result = timeout_result((1, 1, (1, 0)), path)
    assert result["counts"] == {"add": 3}
    if status == "topology_complete":
        assert result["status"] == "lane_timeout"
        assert "worker_exit_timeout" not in result
    else:
        assert result["status"] == status
        assert result["reason"] == row["reason"]
        assert result["worker_exit_timeout"] is True
