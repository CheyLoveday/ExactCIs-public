# Checked Boschloo development reference

Use the [callable method and CLI instructions](BOSCHLOO_METHOD.md) to construct
a candidate and replay its exact bytes with the Lean checker. This is a
repository tool. The installable package's API, method registry and default
methods are unchanged; production activation and comprehensive independent
formal-code verification remain deferred.

This directory contains exactly the checker dependency closure, thirteen
standard-library Python runtime modules, the checker launcher, its Lean CLI,
the frozen checker/resource schemas and pinned build inputs. It omits the
unfinished Lean producer programme and historical development evidence.
Accepted results depend on actual native byte replay; a candidate, protocol
mock or passing source-hash check is not an accepted statistical result.

The original Lean 4.33.0 and nine-package dependency lock are retained. The
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

The configuration follows the pinned Lake 4.33
[library configuration](https://github.com/leanprover/lean4/blob/v4.33.0/src/lake/README.md#lean-libraries)
and target-resolution implementation. Its shipped documentation/source was
inspected on 26 October 2026: submodules belong to their declared library roots,
and a module can be the default build target. Source identity, focused native
execution and future independent formal-code assurance remain separate.

Schema-shape tests use the same `jsonschema==4.25.1` development-only dependency
as the private reference. Its [PyPI metadata](https://pypi.org/project/jsonschema/4.25.1/)
requires Python 3.9 or newer; its [versioned validator documentation](https://python-jsonschema.readthedocs.io/en/v4.25.1/validate/)
confirms Draft 2020-12 selection by `$schema`. These sources were checked on
27 October 2026. Python 3.14 is admitted by the package metadata but is not
listed as a release classifier; the existing public test matrix remains the
compatibility gate. No runtime dependency is added and schema-shape validation
is not semantic certificate acceptance.

The retained [native hull example](../tests/references/checked_boschloo_v1/replay.json)
records one local checker acceptance for table `(1,0,0,1)`, `alpha=1/10`, and
`tolerance=1/100`: the exact odds-ratio hull is `[39/473, infinity]`. Its input
and payload bytes are retained alongside the path-free receipt, including the
construction counters supplied to replay. The receipt is bound to this source
manifest after byte comparison with the executed source. It is finite local
execution evidence; the Python custody/protocol tests do not rerun Lean.
