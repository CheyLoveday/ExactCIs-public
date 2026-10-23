"""Replay the frozen finite packet and reject rehashed scientific mutations.

These tests exercise diagnostic records. They confer neither production
compatibility nor global-inversion, coverage-theorem, or Lean assurance status.
"""

import hashlib
import json
import os
import shutil
import subprocess
import sys
from fractions import Fraction as F

import pytest

from . import _replay as replay
from ._polynomial import OracleLimitError


@pytest.fixture
def packet_bytes():
    return (
        (replay.FIXTURE_DIRECTORY / replay.PACKET_NAME).read_bytes(),
        (replay.FIXTURE_DIRECTORY / replay.MANIFEST_NAME).read_bytes(),
    )


@pytest.fixture
def packet(packet_bytes):
    return json.loads(packet_bytes[0])


def _record(packet, fixture_id):
    return next(row for row in packet["records"] if row["fixture_id"] == fixture_id)


def _reseal(packet):
    """Recompute every scientific and custody digest after deliberate corruption."""
    for record in packet["records"]:
        record["primitive_sha256"] = replay.digest(
            "exactcis.oracle.inputs.v1", record["inputs"]
        )
        derived = record["derived"]
        if "mask" in derived:
            derived["mask_sha256"] = replay.digest(
                "exactcis.oracle.mask.v1", derived["mask"]
            )
        record["output_sha256"] = replay.digest("exactcis.oracle.output.v1", derived)
    manifest = {
        "schema_version": "exactcis.unconditional.oracle_manifest.v1",
        "packet_sha256": replay.digest("exactcis.oracle.packet.v1", packet),
        "fixture_ids": [record["fixture_id"] for record in packet["records"]],
    }
    return replay.canonical_bytes(packet), replay.canonical_bytes(manifest)


def _set_nested(value, path, replacement):
    for key in path[:-1]:
        value = value[key]
    value[path[-1]] = replacement


def _copy_replay_sources(root):
    for source in (*replay.SOURCE_PATHS, replay.SPEC_PATH):
        destination = root / source
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(replay.ROOT / source, destination)


def test_canonical_packet_replays_every_record(packet_bytes, packet):
    assert replay.canonical_bytes(packet) == packet_bytes[0]
    manifest = json.loads(packet_bytes[1])
    assert replay.canonical_bytes(manifest) == packet_bytes[1]
    result = replay.verify_packet(*packet_bytes)
    assert result == {
        "records_replayed": 21,
        "generator_source_checked": (replay.ROOT / replay.GENERATOR_PATH).exists(),
        "claim_ceiling": "finite_diagnostic",
    }
    for record in packet["records"]:
        replay.verify_record(record)
        assert record["orientation"] == "a b / c d; n1=a+b; n0=c+d; observed=(a,c)"
        assert record["seed"] is None


def test_frozen_anchor_results_match_the_u0_values(packet):
    equal = _record(packet, "tangency_equal")["derived"]
    assert equal["mask"] == [[2, 0]]
    assert list(map(replay.rational, equal["threshold_power"])) == [
        -F(108, 3125),
        F(0),
        F(1),
        F(-3),
        F(3),
        F(-1),
    ]
    assert equal["accepted"] is True
    assert equal["threshold_root_certificate"]["interior_roots"] == 1
    assert _record(packet, "tangency_below")["derived"]["accepted"] is True
    assert _record(packet, "tangency_above")["derived"]["accepted"] is False

    for i, (effect, roots, decision) in enumerate(
        (
            (F(23, 9), 4, True),
            (F(47, 17), 0, False),
            (F(3), 2, True),
            (F(25, 7), 0, False),
        )
    ):
        record = _record(packet, f"disconnected_{i}")
        assert replay.rational(record["inputs"]["effect"]["beta"]) == effect
        assert (
            record["derived"]["threshold_root_certificate"]["interior_roots"] == roots
        )
        assert record["derived"]["accepted"] is decision

    stationary = _record(packet, "multiple_maxima")["derived"][
        "stationary_root_certificate"
    ]
    assert stationary["interior_roots"] == 3
    assert stationary["endpoint_roots"] == [False, True]
    event = _record(packet, "ordering_breakpoint")["derived"]
    assert list(map(replay.rational, event["comparison_power_coefficients"])) == [
        0,
        16,
        46,
        0,
        -6,
    ]
    assert event["candidate_endpoint_membership"] == [False, True]
    assert event["candidate_at_event"] == "included_by_exact_equality"
    assert event["full_event_point_mask"] == "not_computed"


def test_decoded_alpha_and_structural_semantics_are_explicit(packet):
    decoded = _record(packet, "decoded_alpha_unequal_groups")
    alpha = float.fromhex(decoded["inputs"]["level"]["hex"])
    numerator, denominator = alpha.as_integer_ratio()
    assert replay.rational(decoded["derived"]["alpha_side"]) == F(
        numerator, 2 * denominator
    )
    assert replay.rational(decoded["derived"]["alpha_side"]) != F(1, 40)
    for record in packet["records"]:
        inputs, derived = record["inputs"], record["derived"]
        if inputs["kind"] == "fixed_null":
            effect = replay.rational(inputs["effect"]["beta"])
            assert replay.rational(inputs["effect"]["s"]) == effect / (1 + effect)
        elif inputs["kind"] == "structural":
            a, c = inputs["observed"]
            if inputs["effect"]["kind"] == "zero":
                expected = (F(a == 0 or c == inputs["n0"]), F(1))
            else:
                expected = (F(1), F(c == 0 or a == inputs["n1"]))
            assert tuple(map(replay.rational, derived["directional_pair"])) == expected
            level = replay.rational(derived["alpha_side"])
            assert derived["accepted"] is all(value >= level for value in expected)


@pytest.mark.parametrize(
    "fixture_id,path,replacement",
    (
        ("tangency_equal", ("mask",), []),
        ("tangency_equal", ("threshold_power", 2), replay.encode(F(-1))),
        ("tangency_equal", ("cutoffs", 2), 3),
        (
            "tangency_equal",
            ("threshold_root_certificate", "chain", -1, 0),
            replay.encode(F(1587, 1600)),
        ),
        ("multiple_maxima", ("stationary_root_certificate", "interior_roots"), 2),
        ("tangency_equal", ("accepted",), False),
        ("tangency_equal", ("accepted",), 1),
        ("tangency_equal", ("threshold_root_certificate", "interior_roots"), True),
        ("tangency_equal", ("threshold_root_certificate", "schema_version"), "unknown"),
        (
            "tangency_equal",
            ("threshold_root_certificate", "procedure_version"),
            "unknown",
        ),
        (
            "structural_zero_unsupported_positive",
            ("directional_pair",),
            replay.encode((F(1), F(1))),
        ),
        (
            "ordering_breakpoint",
            ("comparison_power_coefficients", 1),
            replay.encode(F(-16)),
        ),
        (
            "ordering_breakpoint",
            ("candidate_at_event",),
            "excluded_by_strict_comparison",
        ),
    ),
    ids=(
        "mask",
        "coefficient",
        "cutoff",
        "sturm_sign",
        "stationary_count",
        "strict_tangency",
        "integer_as_acceptance_bool",
        "bool_as_integer_root_count",
        "root_schema_version",
        "root_procedure_version",
        "structural_value",
        "comparison_orientation",
        "algebraic_tie",
    ),
)
def test_rehashed_scientific_mutations_are_rejected(
    packet, fixture_id, path, replacement
):
    record = _record(packet, fixture_id)
    _set_nested(record["derived"], path, replacement)
    data, manifest = _reseal(packet)
    # Hashes are internally consistent, so this must fail on actual derivation.
    assert json.loads(manifest)["packet_sha256"] == replay.digest(
        "exactcis.oracle.packet.v1", packet
    )
    with pytest.raises(ValueError, match="scientific replay mismatch"):
        replay.verify_packet(data, manifest)


@pytest.mark.parametrize(
    "field,value,message",
    (
        ("schema_version", "unknown", "unknown packet/procedure version"),
        ("procedure_version", "unknown", "unknown packet/procedure version"),
        ("scope", "production_certified", "unknown packet scope"),
        ("specification_sha256", "0" * 64, "specification source hash mismatch"),
        ("sources", {}, "oracle source hash mismatch"),
    ),
)
def test_rehashed_packet_identity_and_provenance_changes_refuse(
    packet, field, value, message
):
    packet[field] = value
    with pytest.raises(ValueError, match=message):
        replay.verify_packet(*_reseal(packet))


@pytest.mark.parametrize(
    "field,value,message",
    (
        ("schema_version", "unknown", "unknown record/procedure version"),
        ("procedure_version", "unknown", "unknown record/procedure version"),
        ("claim_ceiling", "global_coverage_certified", "claim ceiling mismatch"),
        ("claim_ceiling", "compatibility_only", "claim ceiling mismatch"),
        ("orientation", "a c / b d", "identity or claim ceiling mismatch"),
        ("seed", 17, "identity or claim ceiling mismatch"),
    ),
)
def test_rehashed_record_identity_changes_refuse(packet, field, value, message):
    _record(packet, "tangency_equal")[field] = value
    with pytest.raises(ValueError, match=message):
        replay.verify_packet(*_reseal(packet))


@pytest.mark.parametrize("coordinate", (F(0), F(1), F(1, 3)))
def test_effect_compact_coordinate_mismatch_refuses(packet, coordinate):
    _record(packet, "tangency_equal")["inputs"]["effect"]["s"] = replay.encode(
        coordinate
    )
    with pytest.raises(ValueError, match="finite effect/compact-coordinate mismatch"):
        replay.verify_packet(*_reseal(packet))


def test_structural_endpoint_cannot_be_replaced_by_finite_sentinel(packet):
    record = _record(packet, "structural_zero_unsupported_positive")
    record["inputs"]["effect"] = {
        "kind": "finite",
        "beta": replay.encode(F(1, 10**12)),
        "s": replay.encode(F(1, 10**12 + 1)),
    }
    with pytest.raises(ValueError, match="unexpected or missing schema fields"):
        replay.verify_packet(*_reseal(packet))


@pytest.mark.parametrize(
    "alpha",
    (
        "0x0.0p+0",
        "0x1.0000000000000p+0",
        "nan",
        "inf",
        "0.05",
        (1e-13).hex(),
        (1 - 1e-13).hex(),
    ),
)
def test_noncanonical_or_invalid_public_alpha_refuses(packet, alpha):
    record = _record(packet, "decoded_alpha_unequal_groups")
    record["inputs"]["level"]["hex"] = alpha
    with pytest.raises(ValueError, match="invalid public alpha encoding"):
        replay.verify_packet(*_reseal(packet))


@pytest.mark.parametrize(
    "value", (0.05, float("inf"), float("nan"), {"nested": [F(1, 3), 0.1]})
)
def test_canonical_serializer_rejects_scientific_floats(value):
    with pytest.raises(ValueError, match="scientific floats"):
        replay.canonical_bytes(value)


@pytest.mark.parametrize(
    "value",
    (
        {"num": "2", "den": "4"},
        {"num": "0", "den": "2"},
        {"num": "1", "den": "-2"},
        {"num": "-0", "den": "1"},
        {"num": "01", "den": "2"},
        {"num": "+1", "den": "2"},
        {"num": 1, "den": "2"},
        {"num": "1", "den": "0"},
    ),
)
def test_noncanonical_rationals_are_rejected(value):
    with pytest.raises(ValueError):
        replay.rational(value)


def test_canonical_rationals_and_digest_domains():
    for value in (F(0), F(-7, 3), F(21, 8)):
        assert replay.rational(replay.encode(value)) == value
    payload = {"x": F(1, 3)}
    assert replay.canonical_bytes(payload) == b'{"x":{"den":"3","num":"1"}}\n'
    assert replay.digest("domain_a", payload) != replay.digest("domain_b", payload)
    with pytest.raises(OracleLimitError, match="digit budget"):
        replay.rational({"num": "1" * 513, "den": "1"})


def test_noncanonical_bytes_and_manifest_tampering_refuse(packet_bytes):
    data, manifest_data = packet_bytes
    with pytest.raises(ValueError, match="noncanonical JSON bytes"):
        replay.verify_packet(data.rstrip(b"\n"), manifest_data)
    manifest = json.loads(manifest_data)
    manifest["schema_version"] = "unknown"
    with pytest.raises(ValueError, match="unknown manifest version"):
        replay.verify_packet(data, replay.canonical_bytes(manifest))
    manifest["schema_version"] = "exactcis.unconditional.oracle_manifest.v1"
    manifest["packet_sha256"] = "0" * 64
    with pytest.raises(ValueError, match="canonical packet hash mismatch"):
        replay.verify_packet(data, replay.canonical_bytes(manifest))


def test_source_distribution_replay_needs_no_generator(packet_bytes, tmp_path):
    _copy_replay_sources(tmp_path)
    assert not (tmp_path / replay.GENERATOR_PATH).exists()
    result = replay.verify_packet(*packet_bytes, root=tmp_path)
    assert result["records_replayed"] == 21
    assert result["generator_source_checked"] is False
    assert result["claim_ceiling"] == "finite_diagnostic"


@pytest.mark.parametrize("generator_hash", (None, 19, "not-a-sha256", "A" * 64))
def test_absent_generator_does_not_waive_hash_format(packet, tmp_path, generator_hash):
    _copy_replay_sources(tmp_path)
    packet["generator_sha256"] = generator_hash
    with pytest.raises(ValueError, match="invalid generator source hash"):
        replay.verify_packet(*_reseal(packet), root=tmp_path)


@pytest.mark.parametrize("malformed", (None, [], {}, {"fixture_id": 17}))
def test_malformed_records_fail_closed(packet_bytes, packet, malformed):
    packet["records"][0] = malformed
    manifest = json.loads(packet_bytes[1])
    manifest["packet_sha256"] = replay.digest("exactcis.oracle.packet.v1", packet)
    with pytest.raises(ValueError, match="malformed fixture record"):
        replay.verify_packet(
            replay.canonical_bytes(packet), replay.canonical_bytes(manifest)
        )


@pytest.mark.parametrize("source", (*replay.SOURCE_PATHS, replay.SPEC_PATH))
def test_source_content_mutation_is_rejected_without_generator(
    packet_bytes, tmp_path, source
):
    _copy_replay_sources(tmp_path)
    path = tmp_path / source
    path.write_bytes(path.read_bytes() + b"\n# modified source\n")
    message = (
        "specification source hash mismatch"
        if source == replay.SPEC_PATH
        else "oracle source hash mismatch"
    )
    with pytest.raises(ValueError, match=message):
        replay.verify_packet(*packet_bytes, root=tmp_path)


def test_fresh_generator_outputs_are_byte_identical(packet_bytes, tmp_path):
    if not (replay.ROOT / replay.GENERATOR_PATH).exists():
        pytest.skip(
            "Repository-only generator is excluded from the source distribution"
        )
    environment = os.environ.copy()
    environment["PYTHONHASHSEED"] = "103"
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "tools.unconditional_oracle.generate",
            "--output",
            str(tmp_path),
        ],
        cwd=replay.ROOT,
        env=environment,
        capture_output=True,
        text=True,
        check=True,
        timeout=60,
    )
    assert "Generated 21 exact diagnostic records" in result.stdout
    assert (tmp_path / replay.PACKET_NAME).read_bytes() == packet_bytes[0]
    assert (tmp_path / replay.MANIFEST_NAME).read_bytes() == packet_bytes[1]
    for source, expected in json.loads(packet_bytes[0])["sources"].items():
        assert (
            hashlib.sha256((replay.ROOT / source).read_bytes()).hexdigest() == expected
        )


@pytest.mark.parametrize("inputs", (None, [], {"kind": "unsupported"}))
def test_primitive_replay_requires_a_supported_input_object(inputs):
    with pytest.raises(ValueError, match="primitive inputs|unknown primitive kind"):
        replay.derive(inputs)


@pytest.mark.parametrize(
    "fixture_id,path,value,error,message",
    (
        ("tangency_equal", ("n1",), True, OracleLimitError, "positive groups"),
        ("tangency_equal", ("n1",), 13, OracleLimitError, "positive groups"),
        ("tangency_equal", ("n0",), 0, OracleLimitError, "positive groups"),
        ("tangency_equal", ("observed",), None, ValueError, "two success counts"),
        ("tangency_equal", ("observed",), [2], ValueError, "two success counts"),
        ("tangency_equal", ("observed",), [3, 0], ValueError, "within their groups"),
        ("tangency_equal", ("direction",), "two-sided", ValueError, "greater or less"),
        ("ordering_breakpoint", ("candidate",), None, ValueError, "two success counts"),
        ("ordering_breakpoint", ("candidate",), [1], ValueError, "two success counts"),
        (
            "ordering_breakpoint",
            ("isolator",),
            None,
            ValueError,
            "two rational endpoints",
        ),
        (
            "ordering_breakpoint",
            ("isolator",),
            [replay.encode(F(1))],
            ValueError,
            "two rational endpoints",
        ),
        (
            "ordering_breakpoint",
            ("isolator",),
            replay.encode((F(0), F(1))),
            ValueError,
            "finite and positive",
        ),
        (
            "ordering_breakpoint",
            ("isolator",),
            replay.encode((F(3), F(2))),
            ValueError,
            "finite and positive",
        ),
        (
            "ordering_breakpoint",
            ("isolator",),
            replay.encode((F(1), F(2))),
            ValueError,
            "isolate exactly one",
        ),
        (
            "decoded_alpha_unequal_groups",
            ("level", "hex"),
            None,
            ValueError,
            "hexadecimal float string",
        ),
        (
            "tangency_equal",
            ("level", "kind"),
            "rounded_decimal",
            ValueError,
            "unknown level kind",
        ),
        (
            "tangency_equal",
            ("level", "value"),
            replay.encode(F(-1, 20)),
            ValueError,
            r"in \[0,1\]",
        ),
        (
            "tangency_equal",
            ("level", "value"),
            replay.encode(F(21, 20)),
            ValueError,
            r"in \[0,1\]",
        ),
        (
            "structural_zero_unsupported_positive",
            ("effect", "kind"),
            "finite",
            ValueError,
            "endpoint tag",
        ),
        (
            "structural_zero_unsupported_positive",
            ("effect", "s"),
            replay.encode(F(1, 2)),
            ValueError,
            "structural compact-coordinate mismatch",
        ),
        (
            "tangency_equal",
            ("effect", "kind"),
            "zero",
            ValueError,
            "requires a finite effect",
        ),
        (
            "tangency_equal",
            ("effect", "beta"),
            replay.encode(F(0)),
            ValueError,
            "finite effect/compact-coordinate mismatch",
        ),
    ),
)
def test_malformed_primitive_fields_refuse_before_scientific_output(
    packet, fixture_id, path, value, error, message
):
    inputs = _record(packet, fixture_id)["inputs"]
    _set_nested(inputs, path, value)
    with pytest.raises(error, match=message):
        replay.derive(inputs)


@pytest.mark.parametrize(
    "value", (None, [], {}, {"num": "1"}, {"num": "1", "den": "2", "extra": "x"})
)
def test_rationals_require_exactly_the_two_named_fields(value):
    with pytest.raises(ValueError, match="requires exactly num and den"):
        replay.rational(value)


def test_canonical_json_rejects_non_string_keys():
    with pytest.raises(ValueError, match="object keys must be strings"):
        replay.canonical_bytes({1: "scientific coefficient"})


@pytest.mark.parametrize(
    "field,value,message",
    (
        ("fixture_id", "../external", "invalid fixture identity"),
        ("primitive_sha256", "0" * 64, "primitive-input hash mismatch"),
        ("output_sha256", "0" * 64, "derived-output hash mismatch"),
    ),
)
def test_record_identity_and_unresealed_hash_corruption_refuse(
    packet, field, value, message
):
    record = _record(packet, "tangency_equal")
    record[field] = value
    with pytest.raises(ValueError, match=message):
        replay.verify_record(record)


@pytest.mark.parametrize("records", ([], [None] * 257))
def test_record_count_is_bounded_before_replay(packet_bytes, packet, records):
    packet["records"] = records
    manifest = json.loads(packet_bytes[1])
    manifest["packet_sha256"] = replay.digest("exactcis.oracle.packet.v1", packet)
    with pytest.raises(ValueError, match="invalid fixture count"):
        replay.verify_packet(
            replay.canonical_bytes(packet), replay.canonical_bytes(manifest)
        )


@pytest.mark.parametrize("mutation", ("reverse", "duplicate"))
def test_rehashed_fixture_order_and_uniqueness_are_enforced(packet, mutation):
    if mutation == "reverse":
        packet["records"].reverse()
    else:
        packet["records"].append(packet["records"][-1])
    with pytest.raises(ValueError, match="fixture identity/order mismatch"):
        replay.verify_packet(*_reseal(packet))


def test_packet_byte_limit_precedes_json_parsing(packet_bytes):
    with pytest.raises(OracleLimitError, match="packet byte budget"):
        replay.verify_packet(b" " * 4_000_001, packet_bytes[1])


def test_present_generator_must_match_its_source_hash(packet_bytes, tmp_path):
    _copy_replay_sources(tmp_path)
    generator = tmp_path / replay.GENERATOR_PATH
    generator.parent.mkdir(parents=True)
    generator.write_text("# A replacement is not the recorded generator.\n")
    with pytest.raises(ValueError, match="generator source hash mismatch"):
        replay.verify_packet(*packet_bytes, root=tmp_path)


def test_replay_cli_reports_a_complete_packet(
    packet_bytes, tmp_path, monkeypatch, capsys
):
    for name, data in zip((replay.PACKET_NAME, replay.MANIFEST_NAME), packet_bytes):
        (tmp_path / name).write_bytes(data)
    monkeypatch.setattr(sys, "argv", ["oracle-replay", "--directory", str(tmp_path)])
    assert replay.main() == 0
    assert json.loads(capsys.readouterr().out) == {
        "records_replayed": 21,
        "generator_source_checked": (replay.ROOT / replay.GENERATOR_PATH).exists(),
        "claim_ceiling": "finite_diagnostic",
    }


def test_replay_cli_invalid_option_exits_without_success(monkeypatch, capsys):
    monkeypatch.setattr(sys, "argv", ["oracle-replay", "--unknown"])
    with pytest.raises(SystemExit) as error:
        replay.main()
    assert error.value.code == 2
    output = capsys.readouterr()
    assert not output.out
    assert "unrecognized arguments" in output.err
