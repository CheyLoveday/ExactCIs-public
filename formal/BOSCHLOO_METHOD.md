# Callable checked Boschloo reference

This is a development reference for a two-sided Boschloo odds-ratio confidence
hull under independent binomial groups. It constructs a finite candidate and
returns a statistical result only after the actual Lean literal-byte checker
accepts that candidate. Critical-profile assurance covers the selected Boschloo
formal statements and their protected meanings; the [checking results](../docs_md/formal-verification.md)
record its exact scope and evidence. Production activation, general producer
completeness and universal Python implementation refinement are separate claims.

## Build and run

Use the repository's Python environment and pinned Lean 4.35.0/Mathlib lock.
Build the checker dependency closure once, from the repository root:

```sh
cd formal
lake exe cache get
lake build ExactCIs.Unconditional.MeteredGlobalChecker
cd ..
```

`lake exe cache get` obtains the pinned Mathlib build cache on a fresh checkout;
it can be skipped when that cache is already present. The default checker
launcher repeats the focused checker build before each replay, so
changed checker source cannot silently reuse stale objects. It does not build
the unfinished producer proof programme.

A small full-domain example is:

```sh
.venv/bin/python formal/tools/boschloo.py 0 1 0 1 \
  --alpha 1/20 --tolerance 0 --output-dir .reports/boschloo
```

A nontrivial hull example is:

```sh
.venv/bin/python formal/tools/boschloo.py 1 0 0 1 \
  --alpha 1/10 --tolerance 1/100 --output-dir .reports/boschloo \
  --timeout 1800 --checker-timeout 1800
```

The four counts are `(a,b,c,d)`, with group totals `a+b` and `c+d` both positive.
`alpha` is the two-sided error level; the method computes `alpha/2` internally.
Use exact fractions or decimal strings. The nonnegative tolerance is the
absolute odds-ratio endpoint-excess tolerance of the T1-min hull contract,
not a probability-grid spacing. Small tables can still be expensive or refuse.
A larger timeout does not increase the fixed resource caps.

The practical generator is explicitly
`EXACT_MERGED_FAMILY_REFERENCE_V1`: individual polynomial isolation followed by
exact merging. The older product-isolation route remains separately identified;
its timings do not describe this method. This reference makes no production
speed, table-size or capability promise.

## Python call and result

From the repository root:

```sh
PYTHONPATH=formal/tools .venv/bin/python - <<'PY'
from fractions import Fraction
from boschloo import Status, run_boschloo

run = run_boschloo(
    (0, 1, 0, 1), Fraction(1, 20), Fraction(0),
    output_dir=".reports/boschloo", timeout=1800, checker_timeout=1800,
)
if run.status is not Status.ACCEPTED:
    raise SystemExit(f"{run.status.value}: {run.reason}")
print(run.result.as_dict())
print(run.run_dir)
PY
```

`run_boschloo(table, alpha, tolerance, *, output_dir, checker=DEFAULT_CHECKER,
timeout=1800, checker_timeout=1800)` returns a `RunResult`. Integers, `Fraction`
values and exact strings are accepted for `alpha`/`tolerance`; binary floats
are rejected. The default checker is `formal/tools/boschloo_check`.
`--checker PATH` is an advanced trusted-checker override, not evidence that an
arbitrary executable is Lean.

Only `status == "accepted"` carries a `CheckedResult`:

| Kind | Meaning |
| --- | --- |
| `FULL` | Exact full odds-ratio domain: lower `Fraction(0)`, upper `None` (infinity). |
| `EMPTY` | Certified empty accepted set; there are no interval endpoints. |
| `HULL` | Checked outer hull; finite endpoints are exact `Fraction` values and `None` means infinity. |

The checker reports compact `s` bounds. The wrapper converts them exactly by
`OR = s/(1-s)`, with `s=0` becoming zero and `s=1` becoming infinity. For example,
compact lower `39/512` becomes odds-ratio lower `39/473`. It does not return
naively rounded floating-point endpoints. JSON endpoints use explicit
`zero`, `rational` and `infinity` tags. A hull result makes no component/topology
claim.

## Refusals and retained artifacts

The CLI prints one JSON response and exits `0` only for an accepted result;
other method outcomes exit `2`. A construction/resource refusal, deadline,
checker rejection, unavailable checker, malformed reply or IO failure carries
no statistical result. Candidate files alone are never accepted results.

Each attempt creates a fresh `boschloo-*` child of `--output-dir`. It retains
`request.json`, available `input.json`/`payload.json`, `construction.json`,
construction/checker stdout and stderr, Python source snapshots under `sources/`,
and `run.json` when writable. The final record contains status, identities,
profile/counter evidence and the accepted result, if any. A timeout may leave
only partial construction artifacts; they remain unaccepted.

The named `BOSCHLOO_CHECKED_REFERENCE_V1` profile continues all fifteen
construction/serialization counters into native byte replay. It does not reset
allowances between phases. Process startup, file IO and evidence bookkeeping
are outside those delegated-primitive counters. `--timeout` is the total method
deadline in seconds; `--checker-timeout` also limits replay, including its
focused build. On POSIX, timed-out child process groups are killed and reaped.
OS process creation can add uninterruptible startup time, so this is not a hard
real-time guarantee. The shell launcher and process-group boundary target
macOS/Linux; Windows execution is not qualified here.

The Python boundary was exercised with Python 3.12.3. Its process handling uses
Python's documented [subprocess](https://docs.python.org/3.12/library/subprocess.html)
and [process-group signaling](https://docs.python.org/3.12/library/os.html#os.killpg)
interfaces; exact textual inputs use [Fraction](https://docs.python.org/3.12/library/fractions.html).
These documentation references were checked on 26 October 2026.
