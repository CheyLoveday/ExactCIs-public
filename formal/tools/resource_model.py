"""Version 1 delegated-primitive accounting, independent of certificate claims.

All counters are exact nonnegative integers. Thirteen dimensions accumulate;
the remaining two retain conservative high-water bounds. A proposal checks the
whole vector and the frozen-wire compatibility caps before changing any state.
The low-level ``perform`` helper only orders charging and a suspended body; it
does not certify what an arbitrary caller puts in that body.
"""

from __future__ import annotations

import hashlib
import json
from collections.abc import Callable
from dataclasses import asdict, dataclass, fields, replace
from enum import Enum
from typing import TypeVar

MAX_COUNTER = (1 << 63) - 1
SCHEMA = "exactcis.resource-profile.v1"
T = TypeVar("T")


@dataclass(frozen=True)
class CostVector:
    decoded_bytes: int = 0
    decoded_items: int = 0
    sample_states: int = 0
    rational_operations: int = 0
    coefficient_slots: int = 0
    root_replay_steps: int = 0
    algebraic_comparisons: int = 0
    projection_polynomials: int = 0
    projection_roots: int = 0
    leaf_or_cell_transitions: int = 0
    certificate_bytes: int = 0
    integer_operations: int = 0
    structural_steps: int = 0
    maximum_operand_bits: int = 0
    maximum_polynomial_degree: int = 0

    def __post_init__(self) -> None:
        for f in fields(self):
            value = getattr(self, f.name)
            if type(value) is not int or value < 0 or value > MAX_COUNTER:
                raise ValueError(f"{f.name} must be an integer in [0, 2**63-1]")


DIMENSIONS = tuple(f.name for f in fields(CostVector))
HIGH_WATER = ("maximum_operand_bits", "maximum_polynomial_degree")
TOTAL_WORK = tuple(
    name
    for name in DIMENSIONS
    if name not in (*HIGH_WATER, "decoded_bytes", "certificate_bytes")
)


class Event(str, Enum):
    ADMIT_BYTES = "admit_bytes"
    DECODE_ITEM = "decode_item"
    SAMPLE_STATE = "sample_state"
    RAT_ADD = "rat_add"
    RAT_SUB = "rat_sub"
    RAT_MUL = "rat_mul"
    RAT_DIV = "rat_div"
    COEFFICIENTS = "coefficients"
    ROOT_STEP = "root_step"
    ALGEBRAIC_COMPARE = "algebraic_compare"
    PROJECTION_POLYNOMIAL = "projection_polynomial"
    PROJECTION_ROOT = "projection_root"
    LEAF_TRANSITION = "leaf_transition"
    EMIT_BYTES = "emit_bytes"
    INTEGER = "integer"
    STRUCTURAL = "structural"
    OPERAND = "operand"
    DEGREE = "degree"


EVENT_DIMENSION = dict(
    zip(
        Event,
        (
            "decoded_bytes",
            "decoded_items",
            "sample_states",
            "rational_operations",
            "rational_operations",
            "rational_operations",
            "rational_operations",
            "coefficient_slots",
            "root_replay_steps",
            "algebraic_comparisons",
            "projection_polynomials",
            "projection_roots",
            "leaf_or_cell_transitions",
            "certificate_bytes",
            "integer_operations",
            "structural_steps",
            "maximum_operand_bits",
            "maximum_polynomial_degree",
        ),
    )
)


@dataclass(frozen=True)
class ShapeLimits:
    payload_bytes: int = 2_000_000
    integer_digits: int = 1024
    nesting: int = 64
    list_items: int = 20_000
    object_items: int = 32
    string_length: int = 2048
    sample_grid: int = 4096
    group_total: int = 128
    exponent: int = 128
    unique_projection_members: int = 4096
    refinement_depth: int = 128
    bernstein_nodes: int = 0  # disabled in v1's exact-only default
    emitted_bytes: int = 2_000_000
    trace_events: int = 20_000

    def __post_init__(self) -> None:
        for f in fields(self):
            value = getattr(self, f.name)
            if type(value) is not int or not 0 <= value <= MAX_COUNTER:
                raise ValueError(f"invalid shape cap: {f.name}")
        if self.nesting > 64:
            raise ValueError("v1 supports at most 64 nested JSON containers")


@dataclass(frozen=True)
class LegacyCaps:
    """Trusted frozen-wire limits, applied in addition to the vector profile."""

    polynomial_ops: int = MAX_COUNTER
    root_checks: int = MAX_COUNTER
    algebraic_comparisons: int = MAX_COUNTER
    leaves: int = MAX_COUNTER
    total_work: int = MAX_COUNTER

    def __post_init__(self) -> None:
        for f in fields(self):
            value = getattr(self, f.name)
            if type(value) is not int or not 0 <= value <= MAX_COUNTER:
                raise ValueError(f"invalid legacy cap: {f.name}")


@dataclass(frozen=True)
class ResourceProfile:
    limits: CostVector
    shapes: ShapeLimits = ShapeLimits()
    legacy: LegacyCaps = LegacyCaps()
    name: str = "VECTOR_DEVELOPMENT_V1"
    schema: str = SCHEMA

    def __post_init__(self) -> None:
        if (
            type(self.limits) is not CostVector
            or type(self.shapes) is not ShapeLimits
            or type(self.legacy) is not LegacyCaps
            or self.schema != SCHEMA
            or type(self.name) is not str
            or not self.name.isascii()
            or not 1 <= len(self.name) <= 128
        ):
            raise ValueError("a versioned exact resource profile is required")

    def canonical_bytes(self) -> bytes:
        return json.dumps(asdict(self), sort_keys=True, separators=(",", ":")).encode(
            "ascii"
        )

    @property
    def sha256(self) -> str:
        return hashlib.sha256(self.canonical_bytes()).hexdigest()


DEVELOPMENT = ResourceProfile(
    limits=CostVector(
        decoded_bytes=4_000_000,
        decoded_items=100_000,
        sample_states=100_000,
        rational_operations=2_000_000,
        coefficient_slots=2_000_000,
        root_replay_steps=20_000,
        algebraic_comparisons=20_000,
        projection_polynomials=20_000,
        projection_roots=20_000,
        leaf_or_cell_transitions=20_000,
        certificate_bytes=2_000_000,
        integer_operations=2_000_000,
        structural_steps=8_000_000,
        maximum_operand_bits=4096,
        maximum_polynomial_degree=128,
    )
)


WIRE_KEYS = (
    "payloadBytes",
    "integerDigits",
    "polynomialDegree",
    "polynomialOps",
    "rootChecks",
    "algebraicComparisons",
    "leaves",
    "totalWork",
)


def wire_profile(profile: ResourceProfile, limits: dict[str, int]) -> ResourceProfile:
    """Intersect trusted execution caps with exactly the frozen v1 work limits.

    The original wire format remains unchanged. Parser byte admission also
    checks the separate payloadBytes cap: decoded_bytes is cumulative over
    input and payload, so it cannot stand in for that per-payload limit.
    """
    if set(limits) != set(WIRE_KEYS) or any(
        type(v) is not int or not 0 <= v <= MAX_COUNTER for v in limits.values()
    ):
        raise ValueError("the eight exact v1 work limits are required")
    old = profile.legacy
    return replace(
        profile,
        limits=replace(
            profile.limits,
            maximum_polynomial_degree=min(
                profile.limits.maximum_polynomial_degree, limits["polynomialDegree"]
            ),
        ),
        shapes=replace(
            profile.shapes,
            payload_bytes=min(profile.shapes.payload_bytes, limits["payloadBytes"]),
            integer_digits=min(profile.shapes.integer_digits, limits["integerDigits"]),
        ),
        legacy=LegacyCaps(
            min(old.polynomial_ops, limits["polynomialOps"]),
            min(old.root_checks, limits["rootChecks"]),
            min(old.algebraic_comparisons, limits["algebraicComparisons"]),
            min(old.leaves, limits["leaves"]),
            min(old.total_work, limits["totalWork"]),
        ),
    )


@dataclass(frozen=True)
class Snapshot:
    used: CostVector
    profile_sha256: str
    input_sha256: str


class ResourceRefusal(RuntimeError):
    code = "RESOURCE_LIMIT"

    def __init__(
        self,
        dimension: str,
        phase: str,
        event: Event,
        previous: Snapshot,
        requested: CostVector,
    ) -> None:
        self.dimension = dimension
        self.phase = phase
        self.event = event
        self.previous = previous
        self.requested = requested
        super().__init__(f"RESOURCE_LIMIT:{phase}:{event.value}:{dimension}")


class ShapeRefusal(RuntimeError):
    code = "RESOURCE_LIMIT"

    def __init__(self, dimension: str, phase: str, previous: Snapshot) -> None:
        self.dimension = dimension
        self.phase = phase
        self.previous = previous
        super().__init__(f"RESOURCE_LIMIT:{phase}:shape:{dimension}")


@dataclass(frozen=True)
class Proposal:
    previous: Snapshot
    next: CostVector
    event: Event
    cost: CostVector
    phase: str


class Meter:
    """One request's state. No shared cache or process-global execution state."""

    def __init__(
        self,
        profile: ResourceProfile = DEVELOPMENT,
        *,
        input_sha256: str = "0" * 64,
        capture: bool = False,
    ) -> None:
        if type(profile) is not ResourceProfile:
            raise ValueError("a ResourceProfile is required")
        if (
            type(input_sha256) is not str
            or len(input_sha256) != 64
            or any(c not in "0123456789abcdef" for c in input_sha256)
        ):
            raise ValueError("input identity must be a lowercase SHA-256")
        if type(capture) is not bool:
            raise ValueError("capture must be a Boolean")
        self.profile = profile
        self._snapshot = Snapshot(CostVector(), profile.sha256, input_sha256)
        self.capture = capture
        self.trace: list[Proposal] = []

    def snapshot(self) -> Snapshot:
        return self._snapshot

    def shape(self, name: str, requested: int, *, phase: str) -> None:
        if name not in {f.name for f in fields(ShapeLimits)}:
            raise ValueError("unknown shape cap")
        if type(requested) is not int or requested < 0:
            raise ValueError("shape size must be an exact nonnegative integer")
        if requested > getattr(self.profile.shapes, name):
            raise ShapeRefusal(name, phase, self._snapshot)

    def propose(self, event: Event, cost: CostVector, *, phase: str) -> Proposal:
        if type(event) is not Event or type(cost) is not CostVector:
            raise ValueError("unknown primitive event or invalid cost descriptor")
        if type(phase) is not str or not phase.isascii() or not 1 <= len(phase) <= 128:
            raise ValueError("a bounded ASCII phase identifier is required")
        main = EVENT_DIMENSION[event]
        allowed = {main, *HIGH_WATER}
        if any(getattr(cost, d) for d in DIMENSIONS if d not in allowed):
            raise ValueError("cost dimensions do not match the primitive event")
        before = self._snapshot

        def refuse(dimension: str) -> None:
            raise ResourceRefusal(dimension, phase, event, before, cost)

        values: dict[str, int] = {}
        for d in DIMENSIONS:
            old, request, cap = (
                getattr(before.used, d),
                getattr(cost, d),
                getattr(self.profile.limits, d),
            )
            if d in HIGH_WATER:
                if request > cap:
                    refuse(d)
                values[d] = max(old, request)
            else:
                # Subtract before addition: descriptor calculation stays within
                # the same fixed metadata width as the selected profile.
                if request > cap - old:
                    refuse(d)
                values[d] = old + request
        for d, cap in (
            ("rational_operations", self.profile.legacy.polynomial_ops),
            ("root_replay_steps", self.profile.legacy.root_checks),
            ("algebraic_comparisons", self.profile.legacy.algebraic_comparisons),
            ("leaf_or_cell_transitions", self.profile.legacy.leaves),
        ):
            if values[d] > cap:
                refuse(f"legacy.{d}")
        remaining = self.profile.legacy.total_work
        for d in TOTAL_WORK:
            if values[d] > remaining:
                refuse("legacy.totalWork")
            remaining -= values[d]
        if self.capture and len(self.trace) >= self.profile.shapes.trace_events:
            refuse("trace_events")
        return Proposal(before, CostVector(**values), event, cost, phase)

    def commit(self, proposal: Proposal) -> None:
        # Revalidate, including profile/event/descriptor constraints. A stale or
        # caller-fabricated proposal cannot manufacture an admitted counter.
        if type(proposal) is not Proposal or proposal.previous != self._snapshot:
            raise ValueError("stale or invalid meter proposal")
        expected = self.propose(proposal.event, proposal.cost, phase=proposal.phase)
        if proposal != expected:
            raise ValueError("altered meter proposal")
        self._snapshot = Snapshot(
            proposal.next,
            self._snapshot.profile_sha256,
            self._snapshot.input_sha256,
        )
        if self.capture:
            self.trace.append(proposal)

    def charge(self, event: Event, cost: CostVector, *, phase: str) -> None:
        self.commit(self.propose(event, cost, phase=phase))

    def perform(
        self, event: Event, cost: CostVector, body: Callable[[], T], *, phase: str
    ) -> T:
        self.charge(event, cost, phase=phase)
        return body()
