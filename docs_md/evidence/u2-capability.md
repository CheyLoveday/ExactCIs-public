# Boschloo adversarial bank and capability proposal

The bank binds all 21 historical exact Boschloo anchors: inclusive tangency and
both perturbations, three interior stationary points, disconnected acceptance,
the corrected signed cubic ordering break, permanent ties, empty/full/zero
thresholds and tagged structural endpoint cases. Existing exact tests retain
the cubic root near `2.9286857509700537`; signs come from the original
cross-product, rather than its unsigned squarefree representative.

The added actual asymmetric case has `n1=1,n0=2`, observation `(1,0)` and greater
mask `{(1,0)}`. At beta one the unique maximizing nuisance is `q=1/3`; at beta
one quarter the derivative there is positive and `q=2/5` gives a larger value.
This demonstrates a moving actual maximizer. It does not assert that every
constant acceptance cover fails.

Generic polynomial attacks separately cover the moving equality ridge,
irrational tangency, algebraic accepted singleton, direction-switching rejection
cover, a successful two-witness cover, a local derivative-sign mutation and
effect-only refinement stall. Nuisance subdivision resolves the
strict-negative stall example. T1-min attacks retain a narrow ghost fringe and
the accumulated width of adjacent leaves; local leaf widths alone do not bound
global hull endpoint excess. Generic attacks are not labelled Boschloo tables.

Two individually strict production xfails call the actual public policy API
through a lazy tests-only protocol. At exact alpha one half the one-trial
examples require inclusive ownership of beta one and the correct zero/infinite
endpoint. Their current failure class is `UnsupportedMethodError`, with repair
owner U3-B4/U4A-3. Import errors, placeholders and timing are not xfailed. New
production capability causes a strict XPASS that must be reviewed and retired.

## Measurement and refusal policy

`capability_measurement_v1.json` attempts all 155 observations through total six
and the larger disconnected anchor. Each case runs in a fresh child. Default
limits remain 100,000 algebraic wrapper calls, degree 64, 4,096 refinements,
16,384 coefficient bits and 2,000,000 polynomial operations per primitive.
Only the separately named larger-anchor diagnostic uses 500,000 wrapper calls
and degree 128. The diagnostic wall limit is ten seconds per small case and
sixty seconds for the larger anchor. Neither limit is a production promise.

The source-frozen local run retained **119 complete comparisons, 36 resource
refusals and one lane timeout** out of 156 attempts. The last case retains its
completed exact topology. Its 2,782 directional
whole-cell comparisons certified 2,069 acceptances and 342 rejections in each
fast lane, retaining 371 inconclusions; every certified answer agreed with
CAD-lite. Cumulative attempt wall time was 326,713,388,916 ns. The largest
recorded child lifetime peak RSS was 67,485,696 bytes. These are observations
of this run, with scheduling and interpreter overhead included.

The packet retains named algebraic counters, effect/nuisance node counts,
witness evaluations, coefficient builds, rejection boxes, exact event/component
counts and certificate identities. Wrapper calls are not Fraction operations
or bit-operation totals. These reference counters are separate from the
development checker's delegated-primitive vector meter. Time is integer elapsed
nanoseconds, including scheduling. Peak RSS is the fresh child process lifetime
peak, including Python; unavailable or killed-before-checkpoint measurements
remain null. No zero or estimated value replaces a missing observation.

A complete topology checkpoint is replaced atomically before the lane phase.
If the wall timeout fires, the child is killed and waited for; the last complete
stage survives. A completed topology plus an unfinished lane remains a named
`lane_timeout`. A terminal `resource_refused` or `complete` checkpoint retains
that scientific status if only worker exit times out; the interruption is
separately recorded as `worker_exit_timeout`. A timeout before topology has no
completed topology or lane outputs. Replay rejects such attached output even
after hashes are recomputed. Degree/work refusal, topology timeout and lane timeout all count
in the denominator. Unexpected errors or lane disagreements stop generation.
Time/RSS are observations, so reruns can move cases across the diagnostic wall
limit; scientific identities of successful stages are checked independently.

## Capability proposal

Retain these profiles as **diagnostic only**. Select production table-size,
operation, time, memory and endpoint-tolerance caps only after U3/U4 measure the
implemented phase vectors and adverse boundaries. The bounded corpus supplies
no completeness class or activation authority. Keep exact absolute/relative
cell-width tolerances separate from T1-min global hull endpoint excess.
Resource exhaustion must refuse rather than fall back to floating sampling or
another method. The [adversarial manifest](https://github.com/CheyLoveday/ExactCIs-public/blob/main/tests/references/unconditional/adversarial_manifest_v1.json)
records exact anchors, strict failures and repair ownership.

## Platform references checked on 26 October 2026

- [Python 3.11 subprocess](https://docs.python.org/3.11/library/subprocess.html#subprocess.run):
  timeout is seconds; `run` kills and waits for the child, and process creation
  itself may delay delivery. Argument vectors use `shell=False` and no credentials.
- [Python resource](https://docs.python.org/3.11/library/resource.html#resource.getrusage):
  availability is Unix. Other platforms retain null RSS.
- [Current Apple XNU manual](https://github.com/apple-oss-distributions/xnu/blob/main/bsd/man/man2/getrusage.2)
  documents Darwin `ru_maxrss` in bytes. The archived Apple web manual says
  kilobytes; the current source resolves that discrepancy for this Darwin run.
- [Linux getrusage manual](https://man7.org/linux/man-pages/man2/getrusage.2.html):
  Linux peak RSS is KiB and is multiplied by 1,024. `RUSAGE_SELF` is read inside
  the child, rather than treating an aggregate child maximum as a tree sum.
- [Python atomic replacement](https://docs.python.org/3.11/library/os.html#os.replace):
  the checkpoint uses same-directory replacement. No durability across host
  failure or power loss is claimed; the requirement is survival of child timeout.

The executed measurement establishes this local platform observation. The
platform-independent Fraction/JSON replay tests use the existing supported CI
matrix; an API document or local pass alone does not establish hosted platform
compatibility. [Issue #43](https://github.com/CheyLoveday/ExactCIs-public/issues/43)
retains its acceptance review and later production retirement gates.
