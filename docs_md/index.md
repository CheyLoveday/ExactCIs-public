# ExactCIs

ExactCIs provides design-aware inference for sparse 2 × 2 tables in Python.
Its public boundary is a small set of fixed-margin odds-ratio procedures,
independent-binomial odds/risk/prevalence-ratio procedures, and a prespecified
independent-strata common-odds-ratio operation.

```text
             outcome +   outcome -
exposed +        a           b
exposed -        c           d
```

Start with the [repository README](https://github.com/CheyLoveday/ExactCIs-public/blob/main/README.md)
for installation and an executable example.
Use [Supported methods](methods.md) to choose a construction and
[API contract](api.md) for endpoint and failure semantics.

## Release and development status

The published package is `exactcis==1.1.2`, supporting Python 3.11–3.13.
The development source admits Python 3.14 and retains the same stable method
registry. Conditional methods condition on both margins; no universal exactness
or unconditional coverage claim is made. Numerical failure raises explicitly
and never selects another method.

The agreed 1.2.0 extension is Boschloo OR with the T1-min outward hull contract.
A [callable checked reference](https://github.com/CheyLoveday/ExactCIs-public/blob/main/formal/BOSCHLOO_METHOD.md)
is available as a repository tool. It returns a statistical result only after
actual Lean byte-checker acceptance and can refuse bounded or unsupported work.
It does not activate a stable package method. The full 225-module selection
completed all six formal-code checkers on 28 October 2026 in a separate Lean
4.35 environment. The public reference now adopts that Lean 4.35 source edition
and its exact dependency pins; Lean 4.33 is historical.
[Formal checking results](formal-verification.md) record critical-profile
assurance MET for 42 reviewed Boschloo targets, protected comparison and the
225-module mechanical scope. Public runtime integration retains separate gates.

The planned Boschloo construction has separate
[bounded oracle evidence](evidence/u1-qualification.md) and an
[adversarial bank and capability proposal](evidence/u2-capability.md).
They document development evidence, with explicit refusals and pending
production tests.

Use the [release roadmap](roadmap.md) for the current boundary and proposed later
matching tests, one-sided bounds and likelihood-ratio methods with their
appropriate uncertainty measures.
