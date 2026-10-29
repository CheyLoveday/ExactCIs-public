# Checked Boschloo development reference

Use the [callable method and CLI instructions](BOSCHLOO_METHOD.md) to construct
a candidate and replay its exact bytes with the Lean checker. This is a
repository tool. The installable package's API, method registry and default
methods are unchanged. The full 225-module development selection passed all
six formal-code checkers on 28 October 2026 in a separate Lean 4.35 compatibility
environment. This reference now uses that canonical Lean 4.35 edition and its
tested dependency pins. [Results and assurance limits](../docs_md/formal-verification.md)
record critical assurance MET for 42 reviewed Boschloo statement types and
protected meanings, with the 225-module mechanical scope. Production activation
retains its own gates. The former Lean 4.33 source edition is historical.

This directory contains exactly the checker dependency closure, thirteen
standard-library Python runtime modules, the checker launcher, its Lean CLI,
the frozen checker/resource schemas and pinned build inputs. It omits the
unfinished Lean producer programme and historical development evidence.
Accepted results depend on actual native byte replay; a candidate, protocol
mock or passing source-hash check is not an accepted statistical result.

The current Lean 4.35.0 and nine-package dependency lock match the tested
environment. The [historical 4.33 custody record](../docs_md/evidence/boschloo-reference-433-20261029.json)
identifies the preserved original source archive and manifest. The
public Lake configuration removes the unused legacy library and makes
`ExactCIs.Unconditional.MeteredGlobalChecker` the sole default target. No
umbrella module is needed. The exact file set and hashes are recorded in
[checked-reference-manifest.json](checked-reference-manifest.json).

From the repository root, check source custody with:

```sh
python tools/check_boschloo_reference.py
```

This guard checks the focused import closure, runtime dependencies, original
pins and schema bytes. It does not elaborate Lean or establish proof assurance.
The launcher performs the focused checker build before every call so that
changed sources cannot silently reuse stale objects.

The configuration follows the pinned Lake 4.35
[library configuration](https://github.com/leanprover/lean4/blob/v4.35.0/src/lake/README.md#lean-libraries)
and target-resolution implementation. Its shipped documentation/source was
inspected on 29 October 2026: submodules belong to their declared library roots,
and a module can be the default build target. Source identity, focused native
execution, the completed compatibility-copy checker run and full mathematical
assurance remain separate claims.

Schema-shape tests use the same `jsonschema==4.25.1` development-only dependency
as the private reference. Its [PyPI metadata](https://pypi.org/project/jsonschema/4.25.1/)
requires Python 3.9 or newer; its [versioned validator documentation](https://python-jsonschema.readthedocs.io/en/v4.25.1/validate/)
confirms Draft 2020-12 selection by `$schema`. These sources were checked on
27 October 2026. Python 3.14 is admitted by the package metadata but is not
listed as a release classifier; the existing public test matrix remains the
compatibility gate. No runtime dependency is added and schema-shape validation
is not semantic certificate acceptance.

The historical [native hull example](../tests/references/checked_boschloo_v1/replay.json)
records one Lean 4.33 checker acceptance for table `(1,0,0,1)`, `alpha=1/10`, and
`tolerance=1/100`: the exact odds-ratio hull is `[39/473, infinity]`. Its input
and payload bytes are retained alongside the path-free receipt, including the
construction counters supplied to replay. The receipt is bound to this source
manifest after byte comparison with the executed source. That original manifest
and every source file are preserved in the historical archive. The receipt is
not rebound to the current 4.35 manifest. It is finite local execution evidence;
the Python custody/protocol tests do not rerun Lean.

The [current Lean 4.35 native receipt](../tests/references/checked_boschloo_435_v1/replay.json)
records four actual frontend executions on 29 October 2026: the hull above and
full domain were accepted, a changed derivative witness was rejected, and an
exhausted byte allowance was refused. The current source manifest, exact inputs,
payloads, prior/final counters, return codes and emitted replies are bound in
that separate receipt. The hull input/payload bytes are reused unchanged from
the historical fixture, without relabelling its old receipt. This is finite
native functional qualification; the CLI remains outside the 225-module
six-checker selection. Custody/protocol tests do not rerun Lean.
