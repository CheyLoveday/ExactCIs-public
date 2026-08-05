#!/usr/bin/env python3
"""Compare the public differential corpus in two isolated installations."""

from __future__ import annotations

import argparse
import json
import subprocess
from pathlib import Path
from tempfile import TemporaryDirectory

_CORPUS_SCRIPT = Path(__file__).with_name("public_api_identity.py")


def _capture(interpreter: Path, output: Path) -> dict[str, object]:
    """Run the public-only corpus under one installed package interpreter."""
    completed = subprocess.run(
        [str(interpreter), str(_CORPUS_SCRIPT), "--json", str(output)],
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    if completed.returncode:
        raise RuntimeError(
            f"public API corpus failed under {interpreter}:\n{completed.stdout}"
        )
    payload = json.loads(output.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise TypeError(f"public API corpus from {interpreter} was not a JSON object")
    return payload


def assert_byte_identical(
    candidate: dict[str, object], reference: dict[str, object]
) -> None:
    """Require exact public-result equality against the installed reference."""
    if reference.get("package_version") != "1.1.0":
        raise AssertionError(
            "reference interpreter did not report exactcis 1.1.0: "
            f"{reference.get('package_version')!r}"
        )
    if candidate.get("calls") != reference.get("calls"):
        candidate_calls = json.dumps(candidate.get("calls"), indent=2, sort_keys=True)
        reference_calls = json.dumps(reference.get("calls"), indent=2, sort_keys=True)
        raise AssertionError(
            "public API differential corpus differs from installed exactcis==1.1.0\n"
            f"candidate:\n{candidate_calls}\nreference:\n{reference_calls}"
        )


def main(argv: list[str] | None = None) -> int:
    """Compare a candidate package interpreter with an exactcis 1.1.0 one."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candidate-python", type=Path, required=True)
    parser.add_argument("--reference-python", type=Path, required=True)
    args = parser.parse_args(argv)

    with TemporaryDirectory(prefix="exactcis-public-api-identity-") as temporary:
        root = Path(temporary)
        candidate = _capture(args.candidate_python, root / "candidate.json")
        reference = _capture(args.reference_python, root / "reference.json")
    assert_byte_identical(candidate, reference)
    print("OK: public API corpus is byte-identical to installed exactcis==1.1.0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
