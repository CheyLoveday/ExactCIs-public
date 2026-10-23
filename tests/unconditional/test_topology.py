"""Analytic topology anchors, independent fixed-null checks and replay attacks."""

from __future__ import annotations

import copy
import hashlib
import json
import os
import subprocess
import sys
from fractions import Fraction as F

import pytest

from . import _oracle as oracle
from . import _polynomial as polynomial
from . import _replay as base
from . import _topology as topology
from . import _topology_replay as replay
from ._algebraic import Root, Work, compare, sign_at


def decode(value):
    if isinstance(value, dict):
        if set(value) == {"num", "den"}:
            # Derived coefficients have the declared 16,384-bit work ceiling;
            # the independent 512-digit primitive-input limit stays unchanged.
            assert max(map(len, value.values())) <= 5000
            result = F(int(value["num"]), int(value["den"]))
            assert (
                max(result.numerator.bit_length(), result.denominator.bit_length())
                <= 16_384
            )
            assert base.encode(result) == value
            return result
        return {k: decode(v) for k, v in value.items()}
    if isinstance(value, list):
        return tuple(decode(v) for v in value)
    return value


@pytest.fixture(scope="module")
def packet_bytes():
    return (
        (base.FIXTURE_DIRECTORY / replay.PACKET).read_bytes(),
        (base.FIXTURE_DIRECTORY / replay.MANIFEST).read_bytes(),
    )


@pytest.fixture(scope="module")
def packet(packet_bytes):
    return json.loads(packet_bytes[0])


def get(packet, identity):
    return next(r for r in packet["records"] if r["fixture_id"] == identity)


def root(record):
    a, b = decode(record["isolator"])
    return Root(tuple(int(c) for c in record["polynomial"]), a, b)


def test_packet_reconstructs_all_scientific_outputs(packet_bytes):
    result = replay.verify(*packet_bytes)
    assert result["records_replayed"] == 18


@pytest.mark.parametrize(
    "identity",
    [
        f"one_trial_{label}_{x}{y}"
        for label in ("rational", "binary64")
        for x in (0, 1)
        for y in (0, 1)
    ],
)
def test_one_trial_topology_matches_independent_discriminant(packet, identity):
    record = get(packet, identity)
    data = decode(record["derived"])
    level = base._level(record["inputs"]["level"])
    w = Work()
    observed = tuple(record["inputs"]["observed"])
    assert not data["empty"]
    assert len(data["components"]) == 1
    if observed in ((0, 0), (1, 1)):
        assert data["full"]
        assert data["ideal_hull"]["lower_event"] == 0
        assert data["ideal_hull"]["upper_event"] == len(data["events"]) - 1
        return
    assert not data["full"]
    boundary_index = data["ideal_hull"][
        "lower_event" if observed == (1, 0) else "upper_event"
    ]
    boundary = root(record["derived"]["events"][boundary_index])
    # Discriminant after compactification: r²-(2r+4r²)s+(1+4r²)s².
    discriminant = (level**2, -2 * level - 4 * level**2, 1 + 4 * level**2)
    if observed == (0, 1):
        # Reverse groups: the compact effect is reflected, s -> 1-s.
        a, b, c = discriminant
        discriminant = (a + b + c, -b - 2 * c, c)
    assert sign_at(discriminant, boundary, w) == 0
    assert data["leaves"][2 * boundary_index]["accepted"]
    # For r=1/40, the upper original root is above 1/40 and is the interior tangency.
    if observed == (1, 0):
        assert sign_at((-F(1, 40), F(1)), boundary, w) > 0
        assert data["leaves"][2 * boundary_index - 1]["accepted"] is False
        assert data["leaves"][2 * boundary_index + 1]["accepted"] is True
    else:
        assert sign_at((-F(39, 40), F(1)), boundary, w) < 0


def test_decoded_alpha_has_its_actual_binary_rational_level(packet):
    exact = get(packet, "one_trial_rational_10")
    decoded = get(packet, "one_trial_binary64_10")
    assert base._level(exact["inputs"]["level"]) == F(1, 40)
    assert base._level(decoded["inputs"]["level"]) == F.from_float(0.05) / 2
    assert base._level(decoded["inputs"]["level"]) != F(1, 40)


def test_extraneous_projection_event_is_rejected(packet):
    data = get(packet, "one_trial_rational_10")["derived"]
    w = Work()
    events = [(i, root(r)) for i, r in enumerate(data["events"])]
    zeros = [(i, r) for i, r in events if sign_at((1, -84, 1604), r, w) == 0]
    assert len(zeros) == 2
    assert [data["leaves"][2 * i]["accepted"] for i, _ in zeros] == [False, True]
    rejected, accepted = [data["leaves"][2 * i]["decisions"][0] for i, _ in zeros]
    assert rejected["kind"] == "negative_controls"
    assert all(sign == -1 for sign in rejected["signs"])
    assert accepted["root_count"] == 1


def test_complete_ownership_and_independent_fixed_null_agreement(packet):
    for record in packet["records"]:
        if record["inputs"]["kind"] != "topology":
            continue
        inputs, data = record["inputs"], decode(record["derived"])
        n1, n0 = inputs["n1"], inputs["n0"]
        observed = tuple(inputs["observed"])
        level = base._level(inputs["level"])
        assert len(data["leaves"]) == 2 * len(data["events"]) - 1
        w = Work(replay.PROFILES[inputs["resource_profile"]])
        for i, leaf in enumerate(data["leaves"]):
            assert leaf["left_event"] == i // 2
            assert leaf["right_event"] == (i + 1) // 2
            if leaf["kind"] != "open":
                continue
            s = leaf["sample"]
            psi = s / (1 - s)
            assert (
                compare(
                    root(record["derived"]["events"][i // 2]),
                    topology.rational_root(s),
                    w,
                )
                < 0
            )
            assert (
                compare(
                    topology.rational_root(s),
                    root(record["derived"]["events"][(i + 1) // 2]),
                    w,
                )
                < 0
            )
            for direction, mask, decision in zip(
                topology.DIRECTIONS, leaf["masks"], leaf["decisions"]
            ):
                assert mask == oracle.rejection_mask(n1, n0, observed, psi, direction)
                controls = oracle.cutoff_vector(n1, n0, observed, psi, direction)
                assert oracle.expand_cutoffs(n1, n0, controls, direction) == mask
                coefficients = oracle.threshold_coefficients(n1, n0, mask, psi, level)
                assert (
                    polynomial.threshold_decision(coefficients) == decision["accepted"]
                )


def test_cubic_event_has_full_inclusive_mask_and_independent_cutoffs(packet):
    data = decode(get(packet, "cubic_ordering_event")["derived"])
    assert data["candidate_tied_and_included"] is True
    assert (1, 3) in data["masks"][1]
    assert tuple(map(len, data["masks"])) == (25, 6)
    for direction, mask, cutoffs in zip(
        topology.DIRECTIONS, data["masks"], data["cutoffs"]
    ):
        assert oracle.expand_cutoffs(4, 4, cutoffs, direction) == mask


@pytest.mark.parametrize(
    "mutation",
    [
        "delete_event",
        "delete_leaf",
        "flip_event",
        "false_full",
        "guard",
        "boolean_index",
        "hull",
        "cutoff",
    ],
)
def test_rehashed_scientific_mutations_are_rejected(packet, mutation):
    case = "cubic_ordering_event" if mutation == "cutoff" else "one_trial_rational_10"
    target = copy.deepcopy(get(packet, case))
    data = target["derived"]
    if mutation == "delete_event":
        data["events"].pop(1)
    elif mutation == "delete_leaf":
        data["leaves"].pop(1)
    elif mutation == "flip_event":
        data["leaves"][6]["accepted"] = False
    elif mutation == "false_full":
        data["full"] = True
    elif mutation == "guard":
        data["projections"][0]["certificate"]["guards"].pop()
    elif mutation == "boolean_index":
        data["leaves"][1]["right_event"] = True
    elif mutation == "hull":
        data["ideal_hull"]["lower_event"] = 0
    elif mutation == "cutoff":
        data["cutoffs"][1][4] += 1
    target["output_sha256"] = base.digest("exactcis.topology.output.v4", data)
    changed = copy.deepcopy(packet)
    changed["records"] = [target]
    manifest = {
        "schema_version": "exactcis.topology_manifest.v4",
        "packet_sha256": base.digest("exactcis.topology.packet.v4", changed),
        "fixture_ids": [case],
    }
    with pytest.raises(ValueError, match="scientific replay mismatch"):
        replay.verify(base.canonical_bytes(changed), base.canonical_bytes(manifest))


def test_empty_full_and_singleton_component_ownership():
    leaves = [
        {
            "kind": "point" if i % 2 == 0 else "open",
            "left_event": i // 2,
            "right_event": (i + 1) // 2,
            "accepted": i == 2,
        }
        for i in range(5)
    ]
    components, hull = topology.components(leaves)
    assert len(components) == 1 and components[0]["leaves"] == (2,)
    assert hull["lower_event"] == hull["upper_event"] == 1
    assert components[0]["lower_closed"] and components[0]["upper_closed"]
    for leaf in leaves:
        leaf["accepted"] = False
    assert topology.components(leaves) == ((), None)


def test_topology_generator_runs_and_is_byte_identical(packet_bytes, tmp_path):
    if not (base.ROOT / replay.GENERATOR).exists():
        pytest.skip("Repository-only topology generator is not shipped in sdist")
    env = {**os.environ, "PYTHONHASHSEED": "317"}
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "tools.unconditional_oracle.generate_topology",
            "--output",
            str(tmp_path),
        ],
        cwd=base.ROOT,
        env=env,
        capture_output=True,
        text=True,
        check=True,
        timeout=300,
    )
    assert "Generated 18" in result.stdout
    assert (tmp_path / replay.PACKET).read_bytes() == packet_bytes[0]
    assert (tmp_path / replay.MANIFEST).read_bytes() == packet_bytes[1]
    assert (
        hashlib.sha256((base.ROOT / replay.GENERATOR).read_bytes()).hexdigest()
        == json.loads(packet_bytes[0])["generator_sha256"]
    )


def rehash_packet(packet):
    manifest = {
        "schema_version": "exactcis.topology_manifest.v4",
        "packet_sha256": base.digest("exactcis.topology.packet.v4", packet),
        "fixture_ids": [r["fixture_id"] for r in packet["records"]],
    }
    return base.canonical_bytes(packet), base.canonical_bytes(manifest)


@pytest.mark.parametrize(
    "field,value",
    [
        ("schema_version", "unknown"),
        ("procedure_version", "unknown"),
        ("sources", {}),
        ("specification_sha256", "0" * 64),
        ("generator_sha256", "invalid"),
        ("profile", {}),
        ("records", []),
    ],
)
def test_packet_provenance_and_profile_fail_closed(packet, field, value):
    changed = copy.deepcopy(packet)
    changed[field] = value
    with pytest.raises(ValueError):
        replay.verify(*rehash_packet(changed))


@pytest.mark.parametrize(
    "field,value",
    [
        ("fixture_id", "NOT-CANONICAL"),
        ("schema_version", "unknown"),
        ("orientation", "rows reversed"),
        ("claim_ceiling", "production"),
        ("input_sha256", "0" * 64),
        ("output_sha256", "0" * 64),
        ("inputs", {"kind": []}),
    ],
)
def test_record_identity_and_hashes_fail_closed(packet, field, value):
    changed = copy.deepcopy(packet)
    changed["records"] = [copy.deepcopy(get(packet, "one_trial_rational_00"))]
    changed["records"][0][field] = value
    with pytest.raises(ValueError):
        replay.verify(*rehash_packet(changed))


def test_packet_byte_and_manifest_boundaries(packet_bytes, packet):
    with pytest.raises(polynomial.OracleLimitError, match="byte budget"):
        replay.verify(b" " * 8_000_001, packet_bytes[1])
    with pytest.raises(ValueError, match="noncanonical"):
        replay.verify(b" " + packet_bytes[0], packet_bytes[1])
    for field, value, error in (
        ("schema_version", "unknown", "unknown topology manifest"),
        ("packet_sha256", "0" * 64, "packet hash mismatch"),
        ("fixture_ids", [], "identity/order mismatch"),
    ):
        changed = copy.deepcopy(packet)
        changed["records"] = [copy.deepcopy(get(packet, "one_trial_rational_00"))]
        data, manifest_bytes = rehash_packet(changed)
        manifest = json.loads(manifest_bytes)
        manifest[field] = value
        with pytest.raises(ValueError, match=error):
            replay.verify(data, base.canonical_bytes(manifest))


def test_primitive_and_group_scope_validation(packet):
    original = get(packet, "one_trial_rational_00")["inputs"]
    rebuilt = replay.record("one_trial_rational_00", original)
    assert base.canonical_bytes(rebuilt) == base.canonical_bytes(
        get(packet, "one_trial_rational_00")
    )
    for field, value in (
        ("kind", "unknown"),
        ("resource_profile", "unknown"),
        ("kind", "ordering_anchor"),
    ):
        changed = copy.deepcopy(original)
        changed[field] = value
        with pytest.raises(ValueError):
            replay.derive(changed)
    with pytest.raises(polynomial.OracleLimitError, match="groups through 12"):
        topology.topology(13, 1, (0, 0), F(1, 40))


def test_compact_threshold_equals_independent_rational_coefficients():
    n1, n0, observed = 2, 3, (1, 0)
    for s in (F(1, 5), F(2, 3)):
        psi = s / (1 - s)
        for direction in topology.DIRECTIONS:
            mask = oracle.rejection_mask(n1, n0, observed, psi, direction)
            h = topology.threshold(n1, n0, mask, F(1, 40), Work())
            direct = oracle.threshold_coefficients(n1, n0, mask, psi, F(1, 40))
            assert polynomial.trim(tuple(polynomial.evaluate(c, s) for c in h)) == (
                polynomial.trim(tuple((1 - s) ** n1 * c for c in direct))
            )


def test_replay_cli(packet_bytes, tmp_path, monkeypatch, capsys):
    (tmp_path / replay.PACKET).write_bytes(packet_bytes[0])
    (tmp_path / replay.MANIFEST).write_bytes(packet_bytes[1])
    monkeypatch.setattr(sys, "argv", ["replay", "--directory", str(tmp_path)])
    assert replay.main() == 0
    assert json.loads(capsys.readouterr().out)["records_replayed"] == 18


def test_disconnected_target_retains_two_components_and_four_exact_witnesses(packet):
    record = get(packet, "disconnected_44_02")
    assert record["inputs"]["resource_profile"] == replay.EXPANDED_PROFILE
    data = decode(record["derived"])
    assert len(data["events"]) == 93
    assert len(data["components"]) == 2
    assert not data["empty"] and not data["full"]
    w = Work(replay.PROFILES[replay.EXPANDED_PROFILE])
    for psi, expected in (
        (F(23, 9), True),
        (F(47, 17), False),
        (F(3), True),
        (F(25, 7), False),
    ):
        point = topology.rational_root(psi / (1 + psi))
        membership = []
        for component in data["components"]:
            lower = root(record["derived"]["events"][component["lower_event"]])
            upper = root(record["derived"]["events"][component["upper_event"]])
            left, right = compare(lower, point, w), compare(point, upper, w)
            membership.append(
                (left < 0 or left == 0 and component["lower_closed"])
                and (right < 0 or right == 0 and component["upper_closed"])
            )
        assert any(membership) is expected
        assert (
            all(
                polynomial.threshold_decision(
                    oracle.threshold_coefficients(
                        4,
                        4,
                        oracle.rejection_mask(4, 4, (0, 2), psi, direction),
                        psi,
                        F(1, 40),
                    )
                )
                for direction in topology.DIRECTIONS
            )
            is expected
        )
    assert data["ideal_hull"]["lower_event"] == data["components"][0]["lower_event"]
    assert data["ideal_hull"]["upper_event"] == data["components"][-1]["upper_event"]


def test_expanded_profile_cannot_be_changed_or_silently_downgraded(packet):
    changed = copy.deepcopy(packet)
    changed["profile"][replay.EXPANDED_PROFILE]["max_bits"] += 1
    with pytest.raises(ValueError, match="profile differs"):
        replay.verify(*rehash_packet(changed))
    inputs = copy.deepcopy(get(packet, "disconnected_44_02")["inputs"])
    inputs["resource_profile"] = replay.PROFILE
    with pytest.raises(polynomial.OracleLimitError):
        replay.derive(inputs)
