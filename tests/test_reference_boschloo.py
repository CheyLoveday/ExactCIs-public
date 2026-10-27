"""Fast orchestration tests; mocked replies do not qualify the native checker."""

from __future__ import annotations

import json
import os
import sys
import time
from collections.abc import Callable
from fractions import Fraction as Q
from pathlib import Path
from typing import Any, cast

import pytest

REFERENCE_ROOT = Path(__file__).resolve().parents[1] / "formal"
pytestmark = pytest.mark.skipif(
    not REFERENCE_ROOT.is_dir(), reason="repository-only checked reference"
)
if REFERENCE_ROOT.is_dir():
    sys.path.insert(0, str(REFERENCE_ROOT / "tools"))
    import boschloo as method


def reply(
    result: dict[str, Any] | None = None,
    *,
    status: str = "accepted",
    counters: list[str] | None = None,
    reason: str = "resource cap",
) -> dict[str, Any]:
    out: dict[str, Any] = dict(
        protocol=method.PROTOCOL,
        profile=method.PROFILE_NAME,
        status=status,
        counters=counters if counters is not None else ["0"] * 15,
    )
    out["result" if status == "accepted" else "reason"] = (
        result if status == "accepted" else reason
    )
    return out


def wire(q: Q | int) -> dict[str, str]:
    q = Q(q)
    return dict(numerator=str(q.numerator), denominator=str(q.denominator))


def stub_checker(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    *,
    status: str = "accepted",
    code: int = 0,
    mutate: Callable[[dict[str, Any]], None] | None = None,
    timeout: bool = False,
) -> tuple[Path, list[tuple[str, list[str], float]]]:
    executable = tmp_path / "protocol test stub"
    executable.write_text("unit-test stub; not a native checker\n")
    commands: list[tuple[str, list[str], float]] = []

    def process(
        command: list[str], run_dir: Path, phase: str, seconds: float
    ) -> method._ProcessResult:
        commands.append((phase, command, seconds))
        (run_dir / f"{phase}.stdout").write_bytes(b"")
        (run_dir / f"{phase}.stderr").write_bytes(b"test transcript\n")
        if phase == "construction":
            return method._ProcessResult(
                method._construct_worker(Path(command[-2]), Path(command[-1])), False
            )
        assert len(command) == 18  # executable, two paths, the entire prior vector
        assert all(Path(p).is_file() for p in command[1:3])
        prior = command[3:]
        assert len(prior) == 15 and int(prior[3]) > 0
        terminal = json.loads(Path(command[2]).read_bytes())["terminal"]
        assert terminal == {"kind": "FULL_CERTIFIED"}
        answer = reply(terminal, status=status, counters=prior)
        if mutate:
            mutate(answer)
        (run_dir / "checker.stdout").write_bytes(json.dumps(answer).encode())
        return method._ProcessResult(code, timeout)

    monkeypatch.setattr(method, "_process", process)
    return executable, commands


def test_actual_full_production_is_only_returned_after_valid_checker_reply(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    executable, commands = stub_checker(tmp_path, monkeypatch)
    result = method.run_boschloo(
        (0, 1, 0, 1), "1/10", "0", output_dir=tmp_path, checker=executable
    )
    assert result.status is method.Status.ACCEPTED
    assert result.result == method.CheckedResult("FULL", Q(0), None)
    assert [phase for phase, _, _ in commands] == ["construction", "checker"]
    assert result.run_dir is not None
    receipt = json.loads((result.run_dir / "run.json").read_bytes())
    assert receipt["checker_command"][3:] == receipt["construction"]["counters"]
    assert receipt["input_sha256"] == method._digest(
        (result.run_dir / "input.json").read_bytes()
    )
    assert receipt["payload_sha256"] == method._digest(
        (result.run_dir / "payload.json").read_bytes()
    )
    assert receipt["result_sha256"] == method._digest(
        method._json_bytes(result.result.as_dict())
    )
    suffix = receipt["construction"]["source_snapshot_suffix"]
    for name, digest in receipt["construction"]["source_sha256"].items():
        assert (
            method._digest((result.run_dir / "sources" / (name + suffix)).read_bytes())
            == digest
        )
    assert receipt["construction"]["isolation_strategy"] == "merge"


@pytest.mark.parametrize(
    "status,code,expected",
    [
        ("refused", 2, "CHECKER_REFUSED"),
        ("rejected", 3, "CHECKER_REJECTED"),
        ("accepted", 7, "CHECKER_FAILED"),
    ],
)
def test_native_failure_never_exposes_a_candidate_terminal(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    status: str,
    code: int,
    expected: str,
) -> None:
    executable, _ = stub_checker(tmp_path, monkeypatch, status=status, code=code)
    result = method.run_boschloo(
        (0, 1, 0, 1), Q(1, 10), Q(0), output_dir=tmp_path, checker=executable
    )
    assert result.status is getattr(method.Status, expected) and result.result is None
    assert result.run_dir is not None
    assert (result.run_dir / "payload.json").is_file()
    assert (result.run_dir / "checker.stdout").is_file()
    assert json.loads((result.run_dir / "run.json").read_bytes())["result"] is None


def test_tampered_result_is_not_admitted(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    executable, _ = stub_checker(
        tmp_path,
        monkeypatch,
        mutate=lambda answer: answer.update(result={"kind": "EMPTY_CERTIFIED"}),
    )
    result = method.run_boschloo(
        (0, 1, 0, 1), "0.1", "0", output_dir=tmp_path, checker=executable
    )
    assert result.status is method.Status.CHECKER_PROTOCOL_ERROR
    assert result.reason is not None
    assert result.result is None and "disagrees" in result.reason


def test_exact_compact_hull_conversion_never_rounds_inward() -> None:
    terminal = dict(
        kind="HULL_CERTIFIED", outerLower=wire(Q(39, 512)), outerUpper=wire(1)
    )
    response = reply(
        dict(
            kind="HULL_CERTIFIED", compact_lower=wire(Q(39, 512)), compact_upper=wire(1)
        )
    )
    _, checked = method._reply(json.dumps(response).encode(), 0, (0,) * 15, terminal)
    assert checked is not None
    assert checked == method.CheckedResult("HULL", Q(39, 473), None)
    assert checked.as_dict()["lower"] == dict(
        kind="rational", numerator="39", denominator="473"
    )
    assert checked.as_dict()["upper"] == {"kind": "infinity"}


def test_empty_result_has_no_numeric_endpoints() -> None:
    response = reply({"kind": "EMPTY_CERTIFIED"})
    _, checked = method._reply(
        json.dumps(response).encode(), 0, (0,) * 15, {"kind": "EMPTY_CERTIFIED"}
    )
    assert checked is not None
    assert checked.as_dict() == dict(
        method="boschloo", estimand="odds_ratio", kind="EMPTY"
    )


@pytest.mark.parametrize(
    "mutate",
    [
        lambda answer: answer.update(profile="different-profile"),
        lambda answer: answer.update(counters=["0"] * 14),
        lambda answer: answer["counters"].__setitem__(0, "01"),
        lambda answer: answer["counters"].__setitem__(3, str(method.CAPS[3] + 1)),
        lambda answer: answer.update(extra="unexpected"),
        lambda answer: answer.update(
            result={"kind": "FULL_CERTIFIED", "upper": "infinity"}
        ),
    ],
)
def test_malformed_or_tampered_reply_is_rejected(
    mutate: Callable[[dict[str, Any]], None],
) -> None:
    answer = reply({"kind": "FULL_CERTIFIED"})
    mutate(answer)
    with pytest.raises(ValueError):
        method._reply(
            json.dumps(answer).encode(), 0, (0,) * 15, {"kind": "FULL_CERTIFIED"}
        )


def test_cumulative_counters_cannot_be_reset() -> None:
    prior = [0] * 15
    prior[3], prior[13] = 8, 63
    answer = reply({"kind": "FULL_CERTIFIED"})
    with pytest.raises(ValueError, match="reset"):
        method._reply(
            json.dumps(answer).encode(), 0, tuple(prior), {"kind": "FULL_CERTIFIED"}
        )


def test_duplicate_reply_keys_are_rejected() -> None:
    answer = json.dumps(reply({"kind": "FULL_CERTIFIED"})).encode()
    answer = b'{"status":"rejected",' + answer[1:]
    with pytest.raises(ValueError, match="duplicate"):
        method._reply(answer, 0, (0,) * 15, {"kind": "FULL_CERTIFIED"})


@pytest.mark.parametrize(
    "table,alpha,tolerance",
    [
        ((True, 1, 0, 1), "0.1", "0"),
        ((0, 0, 1, 1), "0.1", "0"),
        ((0, 1, 0, 1), 0.1, "0"),
        ((0, 1, 0, 1), "1.1", "0"),
        ((0, 1, 0, 1), "1/10", "-1/100"),
        ((0, 1, 0, 1), "1e100000000", "0"),
    ],
)
def test_invalid_input_has_no_statistical_result_or_process(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    table: tuple[int, int, int, int],
    alpha: Q | str | int | float,
    tolerance: Q | str | int,
) -> None:
    monkeypatch.setattr(
        method, "_process", lambda *args: pytest.fail("invalid input ran a process")
    )
    # This fixture deliberately sends a float through the runtime input guard.
    answer = method.run_boschloo(
        table, cast(Q | str | int, alpha), tolerance, output_dir=tmp_path
    )
    assert answer.status is method.Status.INVALID_INPUT and answer.result is None
    assert answer.run_dir is None and list(tmp_path.iterdir()) == []


def test_profile_shape_refusal_preserves_exact_input_and_diagnostic(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    executable, commands = stub_checker(tmp_path, monkeypatch)
    answer = method.run_boschloo(
        (129, 0, 1, 0), "1/10", "0", output_dir=tmp_path, checker=executable
    )
    assert answer.status is method.Status.CONSTRUCTION_REFUSED and answer.result is None
    assert [phase for phase, _, _ in commands] == ["construction"]
    assert answer.run_dir is not None
    assert (answer.run_dir / "input.json").is_file()
    assert not (answer.run_dir / "payload.json").exists()
    assert answer.reason is not None and "group_total" in answer.reason


def test_checker_timeout_retains_candidate(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    executable, _ = stub_checker(tmp_path, monkeypatch, timeout=True)
    answer = method.run_boschloo(
        (0, 1, 0, 1), "1/10", "0", output_dir=tmp_path, checker=executable
    )
    assert answer.status is method.Status.CHECKER_TIMEOUT and answer.result is None
    assert answer.run_dir is not None
    assert (answer.run_dir / "payload.json").is_file()


def test_missing_checker_fails_without_faking_success(tmp_path: Path) -> None:
    answer = method.run_boschloo(
        (0, 1, 0, 1), "1/10", "0", output_dir=tmp_path, checker=tmp_path / "missing"
    )
    assert answer.status is method.Status.CHECKER_UNAVAILABLE and answer.result is None
    assert answer.run_dir is not None
    assert (answer.run_dir / "request.json").is_file()


def test_receipt_io_failure_returns_resultless_io_error(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    executable, _ = stub_checker(tmp_path, monkeypatch)
    save = method._save_json

    def save_except_final(path: Path, value: Any) -> None:
        if path.name == "run.json":
            raise OSError("test disk failure")
        save(path, value)

    monkeypatch.setattr(method, "_save_json", save_except_final)
    answer = method.run_boschloo(
        (0, 1, 0, 1), "1/10", "0", output_dir=tmp_path, checker=executable
    )
    assert answer.status is method.Status.IO_ERROR and answer.result is None
    assert answer.reason is not None and "receipt" in answer.reason


@pytest.mark.skipif(
    os.name != "posix", reason="the native reference method targets POSIX"
)
def test_timeout_stops_child_group_before_late_output(tmp_path: Path) -> None:
    late = tmp_path / "late.txt"
    child = (
        "import pathlib,time; print('child-ready',flush=True); time.sleep(0.7); "
        "pathlib.Path(%r).write_text('ran')" % str(late)
    )
    parent = (
        "import subprocess,sys,time; "
        "subprocess.Popen([sys.executable,'-c',%r]); time.sleep(60)" % child
    )
    outcome = method._process(
        [sys.executable, "-c", parent], tmp_path, "timeout-probe", 0.3
    )
    assert outcome.timed_out and outcome.returncode != 0
    assert b"child-ready" in (tmp_path / "timeout-probe.stdout").read_bytes()
    time.sleep(0.8)
    assert not late.exists()
