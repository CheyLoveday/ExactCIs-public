"""Checked reference Boschloo odds-ratio hull API and command line.

Candidate production never admits a result. The native byte checker must accept
those exact files, continuing the same 15 construction counters. Python process,
request and evidence bookkeeping is outside those delegated-primitive counters.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import re
import signal
import subprocess
import sys
import tempfile
import time
from dataclasses import asdict, dataclass
from enum import Enum
from fractions import Fraction
from pathlib import Path
from typing import Any, Literal, Sequence

import metered_global_producer as producer
import metered_polynomial as polynomial
import metered_root as root
import resource_model as resource

FORMAL = Path(__file__).resolve().parents[1]
DEFAULT_CHECKER = FORMAL / "tools" / "boschloo_check"
PROTOCOL = "exactcis.boschloo.method.check.v1"
PROFILE_NAME = "BOSCHLOO_CHECKED_REFERENCE_V1"
GENERATOR_NAME = "EXACT_MERGED_FAMILY_REFERENCE_V1"
ISOLATION_STRATEGY = "merge"
CAPS = (
    4_000_000,
    64_000_000,
    100_000,
    8_000_000,
    2_000_000,
    20_000,
    20_000,
    20_000,
    20_000,
    20_000,
    2_000_000,
    8_000_000,
    4_000_000_000_000,
    4096,
    512,
)
TOTAL_WORK = 4_100_000_000_000
MAX_REPLY_BYTES = 65_536
NATURAL = re.compile(r"0|[1-9][0-9]*", re.ASCII)
EXACT_TEXT = re.compile(
    r"-?(?:[0-9]+/[1-9][0-9]*|[0-9]+(?:\.[0-9]*)?|\.[0-9]+)", re.ASCII
)
SOURCE_NAMES = (
    "boschloo.py",
    "metered_global_producer.py",
    "metered_global_geometry.py",
    "metered_boschloo_polynomials.py",
    "metered_parametric.py",
    "metered_specialized.py",
    "metered_isolate.py",
    "metered_localize.py",
    "metered_selected_refinement.py",
    "metered_algebraic.py",
    "metered_polynomial.py",
    "metered_root.py",
    "resource_model.py",
)


class Status(str, Enum):
    ACCEPTED = "accepted"
    INVALID_INPUT = "invalid_input"
    CONSTRUCTION_REFUSED = "construction_refused"
    CONSTRUCTION_FAILED = "construction_failed"
    CONSTRUCTION_TIMEOUT = "construction_timeout"
    CHECKER_UNAVAILABLE = "checker_unavailable"
    CHECKER_TIMEOUT = "checker_timeout"
    CHECKER_FAILED = "checker_failed"
    CHECKER_REFUSED = "checker_refused"
    CHECKER_REJECTED = "checker_rejected"
    CHECKER_PROTOCOL_ERROR = "checker_protocol_error"
    IO_ERROR = "io_error"
    INTERRUPTED = "interrupted"


@dataclass(frozen=True)
class CheckedResult:
    kind: Literal["FULL", "EMPTY", "HULL"]
    lower: Fraction | None = None  # None denotes infinity for nonempty results.
    upper: Fraction | None = None

    def as_dict(self) -> dict[str, Any]:
        def endpoint(q: Fraction | None) -> dict[str, str]:
            if q is None:
                return {"kind": "infinity"}
            if q == 0:
                return {"kind": "zero"}
            return {
                "kind": "rational",
                "numerator": str(q.numerator),
                "denominator": str(q.denominator),
            }

        out: dict[str, Any] = {
            "method": "boschloo",
            "estimand": "odds_ratio",
            "kind": self.kind,
        }
        if self.kind != "EMPTY":
            out.update(lower=endpoint(self.lower), upper=endpoint(self.upper))
        return out


@dataclass(frozen=True)
class RunResult:
    status: Status
    run_dir: Path | None
    result: CheckedResult | None = None
    reason: str | None = None

    def as_dict(self) -> dict[str, Any]:
        return {
            "status": self.status.value,
            "run_dir": str(self.run_dir) if self.run_dir else None,
            "result": self.result.as_dict() if self.result else None,
            "reason": self.reason,
        }


def common_profile() -> resource.ResourceProfile:
    return resource.ResourceProfile(resource.CostVector(*CAPS), name=PROFILE_NAME)


def _digest(data: bytes) -> str:
    value = hashlib.sha256(data).hexdigest()
    return "-".join(value[i : i + 8] for i in range(0, 64, 8))


def _json_bytes(value: Any) -> bytes:
    return json.dumps(value, separators=(",", ":"), ensure_ascii=True).encode("ascii")


def _receipt_value(value: Any) -> Any:
    """Group metadata hashes without changing any frozen checker input bytes."""
    if type(value) is dict:
        output: dict[str, Any] = {}
        for key, child in value.items():
            if (
                key.endswith("sha256")
                and type(child) is str
                and re.fullmatch("[0-9a-f]{64}", child)
            ):
                output[key] = "-".join(child[i : i + 8] for i in range(0, 64, 8))
            else:
                output[key] = _receipt_value(child)
        return output
    if type(value) is list:
        return [_receipt_value(child) for child in value]
    return value


def _save_json(path: Path, value: Any) -> None:
    path.write_bytes(
        json.dumps(_receipt_value(value), indent=2, ensure_ascii=True).encode("ascii")
        + b"\n"
    )


def _exact(value: Fraction | str | int, name: str) -> Fraction:
    if type(value) is Fraction:
        q = value
    elif type(value) is int:
        q = Fraction(value)
    elif (
        type(value) is str
        and len(value) <= 1024
        and EXACT_TEXT.fullmatch(value.strip())
    ):
        q = Fraction(value.strip())
    else:
        raise ValueError(
            f"{name} must be an exact Fraction, integer, decimal string or fraction string"
        )
    if max(q.numerator.bit_length(), q.denominator.bit_length()) > CAPS[13]:
        raise ValueError(f"{name} exceeds the {CAPS[13]}-bit exact input limit")
    return q


def _validate(
    table: Sequence[int],
    alpha: Fraction | str | int,
    tolerance: Fraction | str | int,
    timeout: float,
    checker_timeout: float,
) -> tuple[tuple[int, int, int, int], Fraction, Fraction]:
    if (
        type(table) not in (tuple, list)
        or len(table) != 4
        or any(type(c) is not int or c < 0 for c in table)
    ):
        raise ValueError(
            "table must contain four nonnegative Python integers (a,b,c,d)"
        )
    if any(c.bit_length() > 4096 for c in table):
        raise ValueError("a count exceeds the exact input size limit")
    counts = (table[0], table[1], table[2], table[3])
    if counts[0] + counts[1] == 0 or counts[2] + counts[3] == 0:
        raise ValueError("both independent-group totals must be positive")
    a, t = _exact(alpha, "alpha"), _exact(tolerance, "tolerance")
    if not 0 <= a <= 1 or t < 0:
        raise ValueError(
            "alpha must be in [0,1] and endpoint-excess tolerance must be nonnegative"
        )
    for name, seconds in (("timeout", timeout), ("checker_timeout", checker_timeout)):
        if (
            type(seconds) not in (int, float)
            or not math.isfinite(seconds)
            or seconds <= 0
        ):
            raise ValueError(f"{name} must be a positive finite number of seconds")
    return counts, a, t


def _wire_input(
    table: tuple[int, int, int, int], alpha: Fraction, tolerance: Fraction
) -> dict[str, Any]:
    def rational(q: Fraction) -> dict[str, str]:
        return {"numerator": str(q.numerator), "denominator": str(q.denominator)}

    return dict(
        schema="exactcis.boschloo.global-checker.input.v1",
        method="boschloo",
        estimand="odds_ratio",
        design="independent_groups",
        a=str(table[0]),
        b=str(table[1]),
        c=str(table[2]),
        d=str(table[3]),
        alpha=rational(alpha),
        alphaSide=rational(alpha / 2),
        hullEndpointExcessTolerance=rational(tolerance),
        limits=dict(
            payloadBytes="2000000",
            integerDigits="1024",
            polynomialDegree="512",
            polynomialOps="8000000",
            rootChecks="20000",
            algebraicComparisons="20000",
            leaves="20000",
            totalWork=str(TOTAL_WORK),
        ),
    )


def _construct_worker(request_path: Path, run_dir: Path) -> int:
    request = json.loads(request_path.read_bytes())
    table = tuple(request["table"])
    alpha, tolerance = Fraction(request["alpha"]), Fraction(request["tolerance"])
    expected_input = _json_bytes(_wire_input(table, alpha, tolerance))
    (run_dir / "input.json").write_bytes(expected_input)
    profile = common_profile()
    shared = resource.Meter(
        profile, input_sha256=hashlib.sha256(expected_input).hexdigest()
    )
    meter = root.Meter(
        root.Limits(
            arithmetic=polynomial.MeterLimits(
                max_degree=512, max_coefficients=2_000_000, max_operations=8_000_000
            ),
            root_checks=20_000,
            total_work=TOTAL_WORK,
            profile=profile,
        ),
        resources=shared,
    )
    started = time.monotonic()
    source_dir = run_dir / "sources"
    source_dir.mkdir()
    sources: dict[str, str] = {}
    for name in SOURCE_NAMES:
        exact_source = (Path(__file__).parent / name).read_bytes()
        (source_dir / (name + ".txt")).write_bytes(exact_source)
        sources[name] = _digest(exact_source)
    try:
        candidate = producer.generate(
            table, alpha, tolerance, meter, isolation_strategy=ISOLATION_STRATEGY
        )
        serialized = producer.serialize(candidate, meter)
        if serialized.input_bytes != expected_input:
            raise RuntimeError("producer changed the exact input identity")
        (run_dir / "payload.json").write_bytes(serialized.payload_bytes)
        status, reason, exit_code = "constructed", None, 0
    except Exception as error:
        status = (
            "refused"
            if isinstance(
                error,
                (
                    resource.ResourceRefusal,
                    resource.ShapeRefusal,
                    root.BudgetRefusal,
                    polynomial.ResourceLimit,
                ),
            )
            else "failed"
        )
        reason, exit_code = f"{type(error).__name__}: {str(error)[:4000]}", 2
    snapshot = meter.root_state()
    used = [getattr(snapshot.resources.used, name) for name in resource.DIMENSIONS]
    record = dict(
        status=status,
        reason=reason,
        generator=GENERATOR_NAME,
        isolation_strategy=ISOLATION_STRATEGY,
        profile=asdict(profile),
        counters=[str(n) for n in used],
        state=asdict(snapshot),
        elapsed_seconds=time.monotonic() - started,
        source_sha256=sources,
        source_snapshot_dir="sources",
        source_snapshot_suffix=".txt",
        input_sha256=_digest(expected_input),
        result_admitted=False,
    )
    payload_path = run_dir / "payload.json"
    if payload_path.exists():
        record["payload_sha256"] = _digest(payload_path.read_bytes())
    _save_json(run_dir / "construction.json", record)
    return exit_code


@dataclass(frozen=True)
class _ProcessResult:
    returncode: int
    timed_out: bool


def _process(
    command: list[str], run_dir: Path, phase: str, timeout: float
) -> _ProcessResult:
    """Keep binary transcripts; kill/reap the whole task group on POSIX timeout."""
    with (
        (run_dir / f"{phase}.stdout").open("wb") as stdout,
        (run_dir / f"{phase}.stderr").open("wb") as stderr,
    ):
        process = subprocess.Popen(
            command,
            stdin=subprocess.DEVNULL,
            stdout=stdout,
            stderr=stderr,
            shell=False,
            start_new_session=(os.name == "posix"),
        )

        def stop() -> None:
            try:
                if os.name == "posix":
                    os.killpg(process.pid, signal.SIGKILL)
                else:
                    process.kill()
            except ProcessLookupError:
                pass
            process.wait()

        try:
            process.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            stop()
            return _ProcessResult(process.returncode, True)
        except BaseException:
            stop()
            raise
    return _ProcessResult(process.returncode, False)


def _natural(value: Any) -> int:
    if type(value) is not str or len(value) > 19 or not NATURAL.fullmatch(value):
        raise ValueError(
            "checker counters must be canonical nonnegative decimal strings"
        )
    number = int(value)
    if number > resource.MAX_COUNTER:
        raise ValueError("checker counter exceeds the fixed integer limit")
    return number


def _counters(value: Any, prior: tuple[int, ...] | None = None) -> tuple[int, ...]:
    if type(value) is not list or len(value) != 15:
        raise ValueError("exactly 15 resource counters are required")
    counts = tuple(_natural(n) for n in value)
    if any(n > cap for n, cap in zip(counts, CAPS)):
        raise ValueError("checker counters exceed the common profile")
    if prior is not None and any(n < previous for n, previous in zip(counts, prior)):
        raise ValueError("checker reset a cumulative or high-water counter")
    if (
        sum(counts[resource.DIMENSIONS.index(name)] for name in resource.TOTAL_WORK)
        > TOTAL_WORK
    ):
        raise ValueError("checker counters exceed the wire total-work limit")
    return counts


def _rational(value: Any) -> Fraction:
    if type(value) is not dict or set(value) != {"numerator", "denominator"}:
        raise ValueError("exact rational endpoint fields are required")
    n, d = value["numerator"], value["denominator"]
    if (
        type(n) is not str
        or type(d) is not str
        or len(n) > 1024
        or len(d) > 1024
        or not NATURAL.fullmatch(n)
        or not NATURAL.fullmatch(d)
        or d == "0"
    ):
        raise ValueError("nonnegative canonical rational endpoints are required")
    q = Fraction(int(n), int(d))
    if str(q.numerator) != n or str(q.denominator) != d:
        raise ValueError("checker returned a noncanonical rational endpoint")
    return q


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate checker response key")
        result[key] = value
    return result


def _reply(
    data: bytes, returncode: int, prior: tuple[int, ...], terminal: dict[str, Any]
) -> tuple[dict[str, Any], CheckedResult | None]:
    if len(data) > MAX_REPLY_BYTES:
        raise ValueError("checker response exceeds the protocol size limit")
    reply = json.loads(
        data.decode("ascii"),
        object_pairs_hook=_unique_object,
        parse_constant=lambda _: (_ for _ in ()).throw(
            ValueError("nonfinite JSON number")
        ),
    )
    if (
        type(reply) is not dict
        or reply.get("protocol") != PROTOCOL
        or reply.get("profile") != PROFILE_NAME
    ):
        raise ValueError("unexpected native checker protocol or profile")
    status = reply.get("status")
    if type(status) is not str:
        raise ValueError("checker response status must be text")
    expected_code = {"accepted": 0, "refused": 2, "rejected": 3}.get(status)
    if expected_code is None or returncode != expected_code:
        raise ValueError("checker status and exit code disagree")
    expected_keys = {
        "protocol",
        "profile",
        "status",
        "counters",
        "result" if status == "accepted" else "reason",
    }
    if set(reply) != expected_keys:
        raise ValueError("unexpected checker response fields")
    _counters(reply["counters"], prior)
    if status != "accepted":
        if type(reply["reason"]) is not str or not 0 < len(reply["reason"]) <= 4096:
            raise ValueError("checker refusal/rejection requires a bounded reason")
        return reply, None
    result = reply["result"]
    if type(result) is not dict or result.get("kind") != terminal.get("kind"):
        raise ValueError("checker result disagrees with the submitted candidate")
    kind = result["kind"]
    if kind in ("FULL_CERTIFIED", "EMPTY_CERTIFIED"):
        if set(result) != {"kind"}:
            raise ValueError("unexpected structural-result endpoints")
        return reply, (
            CheckedResult("FULL", Fraction(0), None)
            if kind == "FULL_CERTIFIED"
            else CheckedResult("EMPTY")
        )
    if kind != "HULL_CERTIFIED" or set(result) != {
        "kind",
        "compact_lower",
        "compact_upper",
    }:
        raise ValueError("unknown checked result")
    lo, hi = _rational(result["compact_lower"]), _rational(result["compact_upper"])
    if (
        not 0 <= lo <= hi <= 1
        or lo != _rational(terminal["outerLower"])
        or hi != _rational(terminal["outerUpper"])
    ):
        raise ValueError(
            "checker hull endpoints disagree with the submitted compact bounds"
        )

    def odds(s: Fraction) -> Fraction | None:
        return None if s == 1 else s / (1 - s)

    return reply, CheckedResult("HULL", odds(lo), odds(hi))


def run_boschloo(
    table: Sequence[int],
    alpha: Fraction | str | int,
    tolerance: Fraction | str | int,
    *,
    output_dir: Path | str,
    checker: Path | str = DEFAULT_CHECKER,
    timeout: float = 1800,
    checker_timeout: float = 1800,
) -> RunResult:
    """Run the bounded reference method; only accepted native replies carry a result.

    ``timeout`` is the total construction/check deadline in seconds;
    ``checker_timeout`` also caps the checker phase. All artifacts are retained
    in a fresh child of ``output_dir``. Exact strings avoid float conversion.
    """
    started = time.monotonic()
    try:
        counts, alpha_q, tolerance_q = _validate(
            table, alpha, tolerance, timeout, checker_timeout
        )
    except (ValueError, TypeError, ZeroDivisionError) as error:
        return RunResult(Status.INVALID_INPUT, None, reason=str(error))
    try:
        destination = Path(output_dir).expanduser().resolve()
        destination.mkdir(parents=True, exist_ok=True)
        run_dir = Path(tempfile.mkdtemp(prefix="boschloo-", dir=destination))
        executable = Path(checker).expanduser().resolve()
        request = dict(
            table=list(counts),
            alpha=str(alpha_q),
            tolerance=str(tolerance_q),
            timeout_seconds=timeout,
            checker_timeout_seconds=checker_timeout,
            checker=str(executable),
            generator=GENERATOR_NAME,
            isolation_strategy=ISOLATION_STRATEGY,
        )
        request_path = run_dir / "request.json"
        _save_json(request_path, request)
    except OSError as error:
        return RunResult(Status.IO_ERROR, None, reason=str(error))
    evidence: dict[str, Any] = {
        "schema": "exactcis.boschloo.method.run.v1",
        "request": request,
        "request_sha256": _digest(request_path.read_bytes()),
        "profile": PROFILE_NAME,
        "accounting_scope": "producer construction/serialization plus cumulative native byte replay; request/process/artifact bookkeeping excluded",
    }

    def finish(
        status: Status, reason: str | None = None, result: CheckedResult | None = None
    ) -> RunResult:
        answer = RunResult(status, run_dir, result, reason)
        evidence.update(answer.as_dict(), elapsed_seconds=time.monotonic() - started)
        if result is not None:
            evidence["result_sha256"] = _digest(_json_bytes(result.as_dict()))
        try:
            _save_json(run_dir / "run.json", evidence)
        except OSError as error:
            return RunResult(
                Status.IO_ERROR,
                run_dir,
                reason=f"could not save final receipt: {error}",
            )
        return answer

    try:
        if not executable.is_file():
            return finish(
                Status.CHECKER_UNAVAILABLE,
                f"native checker executable is missing: {executable}",
            )
        evidence["checker_executable_sha256"] = _digest(executable.read_bytes())
        command = [
            sys.executable,
            str(Path(__file__).resolve()),
            "--_construct",
            str(request_path),
            str(run_dir),
        ]
        evidence["construction_command"] = command
        completed = _process(
            command,
            run_dir,
            "construction",
            max(0.001, timeout - (time.monotonic() - started)),
        )
        if completed.timed_out:
            return finish(
                Status.CONSTRUCTION_TIMEOUT,
                "construction exceeded the method deadline; partial artifacts retained",
            )
        record_path = run_dir / "construction.json"
        if not record_path.is_file():
            return finish(
                Status.CONSTRUCTION_FAILED,
                f"construction process exited {completed.returncode}; see transcript",
            )
        construction = json.loads(record_path.read_bytes())
        evidence["construction"] = construction
        if construction.get("status") != "constructed" or completed.returncode != 0:
            refused = construction.get("status") == "refused"
            return finish(
                Status.CONSTRUCTION_REFUSED if refused else Status.CONSTRUCTION_FAILED,
                construction.get("reason"),
            )
        prior = _counters(construction["counters"])
        input_path, payload_path = run_dir / "input.json", run_dir / "payload.json"
        input_bytes, payload_bytes = input_path.read_bytes(), payload_path.read_bytes()
        evidence.update(
            input_sha256=_digest(input_bytes), payload_sha256=_digest(payload_bytes)
        )
        if (
            evidence["input_sha256"] != construction["input_sha256"]
            or evidence["payload_sha256"] != construction["payload_sha256"]
        ):
            return finish(
                Status.CONSTRUCTION_FAILED, "serialized candidate digest mismatch"
            )
        terminal = json.loads(payload_bytes)["terminal"]
        remaining = timeout - (time.monotonic() - started)
        if remaining <= 0:
            return finish(
                Status.CHECKER_TIMEOUT, "method deadline elapsed before byte replay"
            )
        command = [
            str(executable),
            str(input_path),
            str(payload_path),
            *(str(n) for n in prior),
        ]
        evidence["checker_command"] = command
        checked = _process(command, run_dir, "checker", min(checker_timeout, remaining))
        evidence["checker_exit_code"] = checked.returncode
        if checked.timed_out:
            return finish(
                Status.CHECKER_TIMEOUT,
                "native checker exceeded its deadline; candidate and transcript retained",
            )
        if (
            input_path.read_bytes() != input_bytes
            or payload_path.read_bytes() != payload_bytes
        ):
            (run_dir / "input.original.json").write_bytes(input_bytes)
            (run_dir / "payload.original.json").write_bytes(payload_bytes)
            return finish(
                Status.CHECKER_PROTOCOL_ERROR,
                "checker modified its submitted input or payload",
            )
        with (run_dir / "checker.stdout").open("rb") as output:
            response = output.read(MAX_REPLY_BYTES + 1)
        evidence["checker_reply_sha256"] = _digest(response)
        try:
            reply, result = _reply(response, checked.returncode, prior, terminal)
        except (ValueError, TypeError, KeyError, UnicodeError) as error:
            return finish(
                (
                    Status.CHECKER_FAILED
                    if checked.returncode not in (0, 2, 3)
                    else Status.CHECKER_PROTOCOL_ERROR
                ),
                str(error),
            )
        evidence["checker_reply"] = reply
        if result is None:
            return finish(
                (
                    Status.CHECKER_REFUSED
                    if reply["status"] == "refused"
                    else Status.CHECKER_REJECTED
                ),
                reply["reason"],
            )
        evidence["checker_result_sha256"] = _digest(_json_bytes(reply["result"]))
        return finish(Status.ACCEPTED, result=result)
    except KeyboardInterrupt:
        return finish(
            Status.INTERRUPTED,
            "interrupted; child process group stopped and artifacts retained",
        )
    except (OSError, ValueError, TypeError, KeyError) as error:
        return finish(
            (
                Status.CHECKER_UNAVAILABLE
                if isinstance(error, (FileNotFoundError, PermissionError))
                else Status.IO_ERROR
            ),
            str(error),
        )


def main(argv: Sequence[str] | None = None) -> int:
    args = list(sys.argv[1:] if argv is None else argv)
    if args and args[0] == "--_construct":
        if len(args) != 3:
            return 2
        return _construct_worker(Path(args[1]), Path(args[2]))
    parser = argparse.ArgumentParser(
        description="Checked reference Boschloo odds-ratio confidence hull; exact decimal or fraction inputs."
    )
    for name in ("a", "b", "c", "d"):
        parser.add_argument(name, type=int)
    parser.add_argument(
        "--alpha", required=True, help="two-sided alpha, e.g. 1/20 or 0.05"
    )
    parser.add_argument(
        "--tolerance",
        required=True,
        help="nonnegative exact odds-ratio endpoint excess",
    )
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--checker", type=Path, default=DEFAULT_CHECKER)
    parser.add_argument(
        "--timeout",
        type=float,
        default=1800,
        help="total method deadline in seconds (default: 1800)",
    )
    parser.add_argument(
        "--checker-timeout",
        type=float,
        default=1800,
        help="additional native replay time cap in seconds",
    )
    parsed = parser.parse_args(args)
    result = run_boschloo(
        (parsed.a, parsed.b, parsed.c, parsed.d),
        parsed.alpha,
        parsed.tolerance,
        output_dir=parsed.output_dir,
        checker=parsed.checker,
        timeout=parsed.timeout,
        checker_timeout=parsed.checker_timeout,
    )
    print(json.dumps(result.as_dict(), separators=(",", ":")))
    return 0 if result.status is Status.ACCEPTED else 2


if __name__ == "__main__":
    raise SystemExit(main())
