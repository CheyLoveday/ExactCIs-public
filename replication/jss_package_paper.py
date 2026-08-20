#!/usr/bin/env python3
"""Reproduce the JSS package-paper examples for exactcis 1.1.2."""

from __future__ import annotations

import argparse
import dataclasses
import enum
import hashlib
import json
import platform
import sys
import time
from pathlib import Path
from typing import Any, Callable

import exactcis
from exactcis import Design

EXPECTED_VERSION = "1.1.2"
RELEASE_COMMIT = "f0cbf3c0ab37ea9a7f96e1b70367f40b6281f3c4"
RESULTS_SCHEMA = "exactcis.jss.results.v1"
ENV_SCHEMA = "exactcis.jss.environment.v1"
MANIFEST_SCHEMA = "exactcis.jss.manifest.v1"


def _json_value(value: Any) -> Any:
    if dataclasses.is_dataclass(value) and not isinstance(value, type):
        return {
            field.name: _json_value(getattr(value, field.name))
            for field in dataclasses.fields(value)
        }
    if isinstance(value, enum.Enum):
        return value.value
    if isinstance(value, tuple):
        return [_json_value(item) for item in value]
    if isinstance(value, list):
        return [_json_value(item) for item in value]
    if isinstance(value, dict):
        return {str(key): _json_value(item) for key, item in value.items()}
    if isinstance(value, (str, int, float, bool)) or value is None:
        return value
    raise TypeError(f"unsupported replication value: {type(value).__name__}")


def _canonical_bytes(payload: Any) -> bytes:
    text = json.dumps(
        _json_value(payload),
        allow_nan=False,
        ensure_ascii=False,
        indent=2,
        sort_keys=True,
    )
    return f"{text}\n".encode("utf-8")


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _capture_failure(function: Callable[[], Any]) -> dict[str, str]:
    try:
        function()
    except exactcis.ExactCIsError as exc:
        return {"exception": type(exc).__name__}
    raise AssertionError("expected an ExactCIsError refusal")


def build_results() -> dict[str, Any]:
    fixed = Design.CASE_CONTROL_FIXED_MARGIN
    cohort = Design.COHORT_BINOMIAL
    stratified = Design.STRATIFIED_CASE_CONTROL

    conditional_table = [12, 5, 8, 10]
    methods = (
        "exact_ci_conditional",
        "exact_ci_midp",
        "exact_ci_minlike",
        "exact_ci_blaker",
    )
    conditional_intervals = {
        name: getattr(exactcis, name)(*conditional_table, design=fixed)
        for name in methods
    }

    return {
        "schema_version": RESULTS_SCHEMA,
        "release": {
            "commit": RELEASE_COMMIT,
            "version": EXPECTED_VERSION,
        },
        "public_api": sorted(exactcis.__all__),
        "examples": {
            "conditional_methods": {
                "alpha": 0.05,
                "intervals": conditional_intervals,
                "table": conditional_table,
            },
            "fixed_margin_policy": {
                "result": exactcis.compute_or_with_policy(
                    10,
                    2,
                    5,
                    20,
                    design=fixed,
                ),
                "table": [10, 2, 5, 20],
            },
            "independent_group_rr_policy": {
                "result": exactcis.compute_rr_with_policy(
                    12,
                    5,
                    8,
                    10,
                    design=cohort,
                ),
                "table": conditional_table,
            },
            "ordered_hull": {
                "alpha": 0.01,
                "blaker": exactcis.exact_ci_blaker(
                    4,
                    300,
                    150,
                    4,
                    alpha=0.01,
                    design=fixed,
                ),
                "minlike": exactcis.exact_ci_minlike(
                    4,
                    300,
                    150,
                    4,
                    alpha=0.01,
                    design=fixed,
                ),
                "table": [4, 300, 150, 4],
            },
            "pooled_policy": {
                "result": exactcis.compute_pooled_or(
                    [(12, 5, 8, 10), (8, 2, 15, 20)],
                    design=stratified,
                ),
                "tables": [[12, 5, 8, 10], [8, 2, 15, 20]],
            },
        },
        "refusals": {
            "alpha_outside_certified_domain": _capture_failure(
                lambda: exactcis.exact_ci_conditional(
                    12,
                    5,
                    8,
                    10,
                    alpha=1e-13,
                    design=fixed,
                )
            ),
            "risk_ratio_under_fixed_margins": _capture_failure(
                lambda: exactcis.compute_rr_with_policy(
                    12,
                    5,
                    8,
                    10,
                    design=fixed,
                )
            ),
        },
    }


def build_environment(elapsed_seconds: float) -> dict[str, Any]:
    repository = Path(__file__).resolve().parents[1]
    package_file = Path(exactcis.__file__).resolve()
    return {
        "schema_version": ENV_SCHEMA,
        "elapsed_seconds": elapsed_seconds,
        "exactcis_file": str(package_file),
        "exactcis_version": exactcis.__version__,
        "executable": sys.executable,
        "implementation": platform.python_implementation(),
        "package_is_checkout": package_file.is_relative_to(repository),
        "platform": platform.platform(),
        "python_version": platform.python_version(),
        "random_seed": None,
    }


def write_replication(
    output_dir: Path,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    if exactcis.__version__ != EXPECTED_VERSION:
        raise RuntimeError(
            f"expected exactcis=={EXPECTED_VERSION}, found {exactcis.__version__} "
            f"at {exactcis.__file__}"
        )

    started = time.perf_counter()
    results = build_results()
    elapsed = time.perf_counter() - started
    environment = build_environment(elapsed)

    output_dir.mkdir(parents=True, exist_ok=True)
    results_bytes = _canonical_bytes(results)
    env_bytes = _canonical_bytes(environment)
    script_bytes = Path(__file__).read_bytes()
    manifest = {
        "schema_version": MANIFEST_SCHEMA,
        "claim_ceiling": (
            "Deterministic reproduction of the declared exactcis 1.1.2 public "
            "API examples; not clinical validation, formal verification, or a "
            "universal coverage claim."
        ),
        "command": [
            "python",
            "replication/jss_package_paper.py",
            "--mode",
            "minimal",
            "--show-env",
        ],
        "files": {
            "env.json": _sha256(env_bytes),
            "jss_package_paper.py": _sha256(script_bytes),
            "results.json": _sha256(results_bytes),
        },
        "release": {
            "commit": RELEASE_COMMIT,
            "version": EXPECTED_VERSION,
        },
        "skipped_phases": [
            {
                "phase": "figures",
                "reason": "the main manuscript contains no generated figures",
            }
        ],
    }
    manifest_bytes = _canonical_bytes(manifest)

    (output_dir / "results.json").write_bytes(results_bytes)
    (output_dir / "env.json").write_bytes(env_bytes)
    (output_dir / "manifest.json").write_bytes(manifest_bytes)
    return results, environment, manifest


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=("minimal",), default="minimal")
    parser.add_argument("--show-env", action="store_true")
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path(__file__).resolve().parent / "output" / "jss",
    )
    return parser.parse_args()


def main() -> int:
    args = _parse_args()
    _, environment, manifest = write_replication(args.output_dir.resolve())
    if args.show_env:
        print(_canonical_bytes(environment).decode("utf-8"), end="")
    print(f"output_dir={args.output_dir.resolve()}")
    print(f"results_sha256={manifest['files']['results.json']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
