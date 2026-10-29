# Formal checking results and assurance limits

Updated 29 October 2026. The full selected development project completed its
formal-code checker run on 28 October. Critical-profile assurance is **MET**
for the selected scope below following the protected comparison on 29 October.
Lean 4.35 is the canonical repository reference edition, with the tested
proof bodies and dependency pins. The installable package and the historical
Lean 4.33 edition retain their distinct contracts.

| Item | Recorded result |
| --- | --- |
| Full selected development project | **PASS:** all 225 selected Lean modules, without module exclusions, and their reachable declaration dependencies passed all six checkers |
| Evidence validation | **PASS:** strict inspection, the fresh remote evidence validator and offline inspection; cleanup confirmed. The 29 October follow-up rehashed 32 retained content-addressed objects and freshly downloaded and verified one full export |
| Protected specification comparison | **PASS:** all 42 selected theorem types and binder annotations, with 73 protected definitions, five protected datatypes and their required transitive meanings; no definition holes |
| Critical-profile assurance | **MET for the declared scope:** 42 semantically reviewed Boschloo targets and the 225-module mechanical checker selection in Lean 4.35 |
| Canonical public reference | Lean 4.35 with the tested proof bodies and exact dependency lock; the former 4.33 edition is preserved as history |
| Stable package activation | Separate integration and qualification work; the stable registry and published package remain unchanged |

The current 1.2.0 extension remains **Boschloo odds-ratio inversion with a
T1-min outward hull**. Complete topology, Barnard and exact unconditional RR
remain deferred and nonblocking. Matching tests, one-sided bounds and
likelihood-ratio extensions remain [later-release work](roadmap.md).

## Completed checker execution

The selected scope was `project_all` for 225 explicit module roots,
`DEPENDENCY_COMPLETE`, and `reachable_dependencies`. It is a whole-selection
result rather than an inference from an umbrella import or default build target.
It does not claim verification of all Mathlib declarations or the complete
Python implementation.

Each checker recorded return code zero, complete output streams, no errors,
zero out-of-memory events and confirmed process cleanup:

| Checker | Result |
| --- | --- |
| `leanchecker` | PASS |
| `leanchecker-paranoid` | PASS |
| `lean4lean` | PASS |
| `nanoda` | PASS |
| `con-leche` | PASS |
| `con-ron` | PASS |

The run reused verified dependency builds and the reference export, then
freshly compiled all 225 candidate modules and generated the candidate export.
The final candidate and reference exports each contain 286,318,170 bytes and
have the same SHA-256:

```text
07f6aec66fe68a312d5536b6426e1f0e68890fd1f8f92de01c368aeb8457a39e
```

The exact checked source archive has SHA-256:

```text
8b603b14432459c1441eaab0c8784d290e641eb605609c19ea123b22a6b0756c
```

The retained validation receipt has SHA-256:

```text
202fcef8175b60a8adff41c61e70cda4da19295ab35fd84f8a7cc457fee035d2
```

These identities distinguish the completed campaign artifacts. This public
summary does not distribute the larger private development archive or replace
its retained primary receipts.

## Historical and canonical environments

The historical reference used Lean **4.33.0**, source commit
`d8b18978322de05a8f3dba51ef03cf5461676c17`. The completed run and current
canonical reference use Lean **4.35.0**, source commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. The current package lock is bound by the
[checked reference manifest](https://github.com/CheyLoveday/ExactCIs-public/blob/main/formal/checked-reference-manifest.json).
The dependency revisions differ as follows:

| Package | Historical 4.33 revision | Canonical tested 4.35 revision |
| --- | --- | --- |
| Mathlib | `db584cd6d46c92f209a44c0f1c829460d327499d` | `56a005855ea17e0b0958f73ec801ae140b0a1679` |
| plausible | `b7eb3304aeae834b12dda98993a37f6a41f6f0bb` | `dfa4f38190d07c37e315953e08b90fe2d95b3c24` |
| LeanSearchClient | `5f4d51b81cbd3f6b32b156bfad9056621a040404` | `d6b4c7be5be75ec4917c873ac50c756dc1436372` |
| importGraph | `16f02aa7642864af59f1ff0e384a015994db9118` | `a41f0e9a4dea23188ea9cc1c41ac9f8bbafe0b93` |
| proofwidgets | `4be2e3d5087eeb272cf5a8853b8f9dd025ef5957` | `df72b022e558978a1c50264cfc4d7fec86fa8e04` |
| aesop | `3448c0bcc5ce01b2d1546e483ec3620e32df3d0e` | `4a174c490d8707121c4a9290800489f105d85e07` |
| Qq | `92c15be17b7caf78c2ad767ec40f89052d908d81` | `dce0ad79c486cb1fb504af04f953c3466b0c6db8` |
| batteries | `4488d40d070b9700d4d5a6aa342f0d40c31b2a2d` | `66e469188fe07963e5cf666c7d4433f45b8131c5` |
| Cli | `6130a47896ce867c6a4a55373441e59e565bad0f` | `c24fe6078c630e89b489bffe59b3e20ac30d12c8` |

All four typed global compiler options agree: `maxSynthPendingDepth = 3`,
`pp.unicode.fun = true`, `relaxedAutoImplicit = false`, and
`weak.linter.mathlibStandardSet = true`.

A comparison of the historical source against the tested edition accounts for
all 225 modules: **221 are byte-identical**, and four differ only in eleven theorem proof bodies. The
changes make unfolding, bind arguments and conditional branches explicit.
Statements, premises, imports and runtime definitions are unchanged in source.
That textual correspondence does not establish identical elaborated semantics
across dependency versions or supply a full six-checker result for Lean 4.33.

The current public reference contains 109 Lean files. Of these, 108 occur in
the full selection and now match its source bytes exactly, including the three
previous proof-body variants. The remaining file, `tools/lean/boschloo_check.lean`, is
the public CLI and is outside that 225-module selection. Its retained native
execution evidence is described in the
[reference guide](https://github.com/CheyLoveday/ExactCIs-public/blob/main/formal/README.md).
The full-project result does not add six-checker coverage to that CLI.

## Historical source custody

The [dated custody record](evidence/boschloo-reference-433-20261029.json) identifies
an exact [downloadable original-source archive](evidence/boschloo-reference-433-20261029.tar.gz).
It preserves the original 4.33 manifest, source files, dependency lock and guide
at their historical public revision. The earlier native hull receipt remains
bound to that archived manifest; it is not relabelled as 4.35 execution evidence.
Current source custody uses the new 4.35 manifest and rejects a 4.33 toolchain.

## Assurance follow-up on 29 October

The follow-up rehashed all 32 retained content-addressed objects in the selected
evidence set. One full 286,318,170-byte export was freshly downloaded and its
SHA-256 verified against the identity above. This does not claim a fresh download
or rehash of every remote bulk artifact. No new verification VM was needed.

Each of the 42 selected comparison targets now has an individually closed
transitive axiom audit, with zero unknown declaration references. Each actual
axiom set is a subset of `propext`, `Classical.choice` and `Quot.sound`; this does
not assert that every target uses all three. That selected audit is separate
from the six-checker coverage of the 225-module project.

An independently tasked AI reviewer froze the expected U0 mathematical contract
before inspecting the candidate. The subsequent review covered all 42 target
statement heads and 78 selected semantic roots without a blocking mathematical
finding. This records the review's actual independence and scope. The Lean
interface was transcribed from the candidate and then semantically reviewed
against that prior U0 derivation; it was not an independently authored Lean
formulation or human peer review. The subsequent mechanical comparison is
recorded separately below.

The original Lean 4.33 environment freshly built 19 target modules and exported
all 42 targets. Strict comparison against the checked 4.35 export was attempted
with the native 4.35 comparator. It **REFUSED** at `Nat.decLt`, reflecting a
version difference in the Lean primitive dependencies. This is not evidence of
a Boschloo mathematical failure, but it cannot count as a successful comparison
or qualify the original environment with the completed 4.35 campaign.

The completed protected comparison used a separately frozen types-only expected
challenge in the canonical 4.35 environment. The expected artifact contains the
reviewed exported statement expressions and protected meanings. The 42 candidate
solution proofs are excluded; expected target placeholders remain theorem-only.
It includes all 26 mandatory Lean primitive declarations required by the export.
Native-kernel reconstruction and the protected comparison both returned zero.

The expected export contains 67,899,397 bytes and has SHA-256:

```text
cb60454a2debc08f1a740012e32edfb65c04e2e3f87c3162f09dffe90c8b89c1
```

The comparison candidate is the unchanged 286,318,170-byte export identified
above. It checked all 42 exact theorem types and binder annotations and 73
protected definitions plus five datatypes, including the required transitive
protected meanings. The selected export contains 48,233 units. There are no
definition holes (`[]`). This closes the declared **A09** comparison gate.

Seven genuine controls were compiled, exported and checked by the native kernel.
The valid control passed comparison; all six adverse controls were rejected:
changed target, extra premise, changed binder, changed protected body, missing
target and hidden axiom. These controls exercise the actual comparator rather
than a mocked transport or an expected error string alone.

## Assurance decision and scope

Critical-profile assurance is **MET for this declared scope**: the 42 reviewed
Boschloo semantic targets and protected meanings, tied to the full 225-module
mechanical result and reachable dependencies in the recorded 4.35 environment.
This does not assert independent semantic review of every declaration in those
225 modules, all U0 programme obligations, all Mathlib or the Python package.
An independent critical-profile evidence review confirmed that limited decision.

The original completed campaign's reference used the same source as its
candidate. That historical comparison established consistency; the separately
frozen, reviewed expected challenge and successful comparison above supply the
additional protected mathematical comparison. The earlier cross-version
`Nat.decLt` refusal is retained as a diagnostic of the historical 4.33 edition;
it is not the current canonical comparison outcome.

The expected challenge adopts reviewed exported expressions after an independent
U0 derivation. It must not be described as independently authored Lean code.
The evidence review and mathematical review were separately tasked AI reviews;
no human peer-review acceptance is asserted. Multiple checkers still share
exporters, parsers, libraries or infrastructure, so their count is not a
probability of mathematical correctness.

The public CLI is outside the 225-module checker selection. Its fresh canonical
4.35 execution qualification is a separate result and is not claimed by this
profile decision. The stable package registry and published package are unchanged.

For the Boschloo construction, the claim remains conditional on independent
binomial groups, the frozen inclusive ordering and structural conventions, and
the enclosure premises. A returned hull must enclose ideal acceptance. The
operational coverage statement is `P(return and miss) <= alpha`; it does not
assert nominal coverage conditional on returning. Resource refusal remains
distinct from statistical rejection.

General producer termination/completeness, complete confidence-set topology,
universal Python/binary64 refinement, clinical validation, package publication
and production activation are not established by the six checker passes. Their
existing scope decisions are unchanged.
