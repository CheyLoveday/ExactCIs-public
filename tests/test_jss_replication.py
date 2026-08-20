from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "replication" / "jss_package_paper.py"


def _run(output_dir: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--mode",
            "minimal",
            "--show-env",
            "--output-dir",
            str(output_dir),
        ],
        check=True,
        capture_output=True,
        cwd=output_dir.parent,
        text=True,
    )


def test_jss_minimal_replication_is_deterministic(tmp_path: Path) -> None:
    first = tmp_path / "first"
    second = tmp_path / "second"
    first_run = _run(first)
    _run(second)

    first_results = (first / "results.json").read_bytes()
    second_results = (second / "results.json").read_bytes()
    assert first_results == second_results
    assert "exactcis_version" in first_run.stdout

    results = json.loads(first_results)
    assert results["release"] == {
        "commit": "f0cbf3c0ab37ea9a7f96e1b70367f40b6281f3c4",
        "version": "1.1.2",
    }
    hull = results["examples"]["ordered_hull"]
    assert hull["minlike"] == [
        4.905125604468586e-05,
        0.0022975699605770773,
    ]
    assert hull["blaker"] == [
        4.905125604468586e-05,
        0.0021640717349887904,
    ]
    assert results["refusals"] == {
        "alpha_outside_certified_domain": {"exception": "ValidationError"},
        "risk_ratio_under_fixed_margins": {"exception": "DesignError"},
    }

    manifest = json.loads((first / "manifest.json").read_text())
    assert (
        manifest["files"]["results.json"] == hashlib.sha256(first_results).hexdigest()
    )
    assert "formal verification" in manifest["claim_ceiling"]
    assert manifest["skipped_phases"] == [
        {
            "phase": "figures",
            "reason": "the main manuscript contains no generated figures",
        }
    ]
