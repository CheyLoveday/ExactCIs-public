"""Bind actual Boschloo anchors and generic attacks without rewriting history."""

import hashlib
import json
from pathlib import Path

from tests.unconditional._replay import ROOT, canonical_bytes, digest

SOURCES = (
    "tests/unconditional/_capability_replay.py",
    "tests/unconditional/test_capability_replay.py",
    "tests/unconditional/_production_protocol.py",
    "tests/unconditional/test_adversaries.py",
    "tests/unconditional/test_resource_adversaries.py",
    "tests/unconditional/test_lane_comparison.py",
    "tests/unconditional/test_cell_lanes.py",
    "tests/unconditional/test_polynomial.py",
    "tests/unconditional/test_algebraic.py",
    "tests/unconditional/test_oracle.py",
    "tests/unconditional/test_topology.py",
)


def manifest():
    directory = ROOT / "tests/references/unconditional"
    fixed = json.loads((directory / "boschloo_fixed_null_v1.json").read_bytes())
    packet = {
        "schema_version": "exactcis.boschloo_adversarial_manifest.v1",
        "procedure_version": "boschloo_attack_bank_v1",
        "authority": (
            "Boschloo-only; T1-min global hull endpoint excess; topology optional"
        ),
        "fixed_null_anchors": {
            row["fixture_id"]: row["output_sha256"] for row in fixed["records"]
        },
        "actual_new_anchor": {
            "id": "asymmetric_12_10_moving_maximizer",
            "test": (
                "test_cell_lanes.py::test_actual_asymmetric_boschloo_maximizer_moves"
            ),
            "claim_ceiling": (
                "actual maximizing nuisance changes; no assertion that every "
                "constant acceptance cover fails"
            ),
        },
        "generic_attacks": [
            {
                "id": "two_witness_cover",
                "test": (
                    "test_cell_lanes.py::"
                    "test_two_witness_cover_succeeds_where_no_single_witness_covers"
                ),
            },
            {
                "id": "local_monotone_sign_mutation",
                "test": (
                    "test_cell_lanes.py::"
                    "test_local_derivative_control_certificate_rejects_sign_mutation"
                ),
            },
            {
                "id": "moving_ridge",
                "test": (
                    "test_lane_comparison.py::"
                    "test_constant_witness_does_not_claim_moving_ridge_complete"
                ),
            },
            {
                "id": "irrational_tangency",
                "test": (
                    "test_lane_comparison.py::"
                    "test_irrational_tangency_requires_exact_fallback"
                ),
            },
            {
                "id": "effect_only_stall",
                "test": (
                    "test_lane_comparison.py::"
                    "test_effect_only_subdivision_can_stall_on_a_negative_objective"
                ),
            },
            {
                "id": "direction_switch_cover",
                "test": (
                    "test_cell_lanes.py::"
                    "test_direction_switching_rejection_is_a_cover_not_one_global_direction"
                ),
            },
            {
                "id": "ghost_and_accumulated_fringe",
                "test": (
                    "test_cell_lanes.py::"
                    "test_t1_min_uses_global_hull_excess_and_retains_ghost_fringe"
                ),
            },
            {
                "id": "algebraic_singleton",
                "test": (
                    "test_algebraic.py::"
                    "test_singleton_acceptance_at_an_irrational_effect"
                ),
            },
        ],
        "strict_failures": [
            {
                "id": f"one_trial_inclusive_{endpoint}",
                "test": (
                    f"test_adversaries.py::"
                    f"test_production_one_trial_inclusive_{endpoint}"
                ),
                "repair_owner": "U3-B4/U4A-3",
                "current_failure_class": "UnsupportedMethodError",
                "strict": True,
                "primitive_table": table,
                "alpha": {"num": "1", "den": "2"},
                "expected_object": expected,
            }
            for endpoint, table, expected in (
                (
                    "lower",
                    [1, 0, 0, 1],
                    "hull owns equality psi=1, finite positive lower, infinite upper",
                ),
                (
                    "upper",
                    [0, 1, 1, 0],
                    "hull contains equality psi=1, zero lower, finite upper",
                ),
            )
        ],
        "sources": {
            name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
            for name in SOURCES
        },
        "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "claim_ceiling": (
            "finite scientific attack bank; no production implementation "
            "or general completeness"
        ),
    }
    packet["manifest_sha256"] = digest("exactcis.adversarial_manifest.v1", packet)
    return packet


if __name__ == "__main__":
    path = ROOT / "tests/references/unconditional/adversarial_manifest_v1.json"
    path.write_bytes(canonical_bytes(manifest()))
