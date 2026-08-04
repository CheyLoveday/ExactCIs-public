# ExactCIs — Agent Instructions

This file provides guidance for LLM agents, coding assistants, and automated
tools that consume, generate, or reason about code that uses ExactCIs.

---

## What ExactCIs is

ExactCIs is a design-aware Python library for computing confidence intervals
for 2 × 2 contingency tables. It is **not** a general statistics toolkit. Every
call requires the sampling design to be declared explicitly. The library
provides fail-closed numerical behaviour: unsupported inputs raise exceptions;
no method silently substitutes another.

Supported Python: 3.11 – 3.13. Runtime dependencies: standard library only.

---

## Installation

```bash
pip install exactcis==1.0.0rc1
```

---

## Core concepts an agent must know

### Table orientation (fixed throughout the package)

```
             outcome +   outcome -
exposed +        a           b
exposed -        c           d
```

All four counts (`a`, `b`, `c`, `d`) must be finite, non-negative integers.
Swapping rows reciprocates the ratio; swapping columns also reciprocates it.
**Never relabel cell positions between calls.**

### Design declaration is mandatory

The `Design` enum must match the actual sampling scheme:

| Enum value | Sampling scheme |
|---|---|
| `Design.CASE_CONTROL_FIXED_MARGIN` | Retrospective; both margins fixed |
| `Design.COHORT_BINOMIAL` | Two independent prospective groups |
| `Design.CROSS_SECTIONAL` | Single sample, two exposure groups |

Risk and prevalence ratios are **not identified** from
`CASE_CONTROL_FIXED_MARGIN` data. Attempting this raises an exception.

### `alpha` convention

`alpha` is the **two-sided significance level**. `alpha=0.05` → 95 % CI.
Valid domain: `1e-12 < alpha < 1 - 1e-12`. Values outside this range raise
`ValidationError` before any computation occurs.

---

## Public API

### Odds ratio — fixed-margin case-control

```python
from exactcis import Design, compute_or_with_policy

result = compute_or_with_policy(
    a, b, c, d,
    design=Design.CASE_CONTROL_FIXED_MARGIN,
    method="conditional",   # default; omit to accept default
    alpha=0.05,             # default; omit to accept default
)
```

Stable `method` keys: `"conditional"`, `"midp"`, `"minlike"`, `"blaker"`.

### Odds ratio — independent binomial cohort or cross-sectional

```python
from exactcis import Design, compute_or_with_policy

result = compute_or_with_policy(
    a, b, c, d,
    design=Design.COHORT_BINOMIAL,  # or Design.CROSS_SECTIONAL
    method="wald",                  # or "wald_haldane"
)
```

### Risk ratio / prevalence ratio — independent binomial groups

```python
from exactcis import Design, compute_rr_with_policy

result = compute_rr_with_policy(
    a, b, c, d,
    design=Design.COHORT_BINOMIAL,  # or Design.CROSS_SECTIONAL
    method="score_rr",              # or "wald_rr"
)
```

### Stratified common odds ratio (Mantel-Haenszel)

```python
from exactcis import compute_pooled_or

result = compute_pooled_or(
    strata=[
        {"a": a1, "b": b1, "c": c1, "d": d1},
        {"a": a2, "b": b2, "c": c2, "d": d2},
    ],
    alpha=0.05,
)
```

This is the Mantel-Haenszel / Robins-Breslow-Greenland construction. It is
asymptotic. At least two strata are expected.

### Result object

All high-level calls return a typed result object with:

| Attribute | Meaning |
|---|---|
| `.lower` | Lower confidence limit |
| `.point` | Point estimate (may be `None` for degenerate tables) |
| `.upper` | Upper confidence limit |
| `.method` | String key identifying the construction used |
| `.estimand` | String label for the effect measure |
| `.alpha` | Significance level used |

An agent must not assume `.point` is always finite. It is `None` when the
design and table do not support a unique point estimate.

---

## Method registry inspection

To enumerate every stable method and its metadata at runtime:

```python
from exactcis.estimands import method_registry
print(method_registry())
```

This is the machine-readable source of truth. Agents should query it rather
than hardcode method key lists.

---

## What agents must NOT do

- **Do not guess a design** from the data shape alone. Always ask the user or
  infer from documented study type.
- **Do not catch `NumericalError` and retry with a different method.** The
  library's contract is fail-closed. Surface the error.
- **Do not use `alpha=0` or `alpha=1`.** These are invalid and will raise
  `ValidationError`.
- **Do not import private submodules** (names beginning with `_`). Their
  interfaces are unstable.
- **Do not treat conditional and asymptotic intervals as interchangeable.**
  They differ by construction and are not expected to agree.
- **Do not pool strata without declaring a prespecified stratified design.**
  Post-hoc stratification is not supported.

---

## Exception taxonomy

| Exception | Trigger |
|---|---|
| `ValidationError` | Invalid design, unsupported alpha, unidentified estimand |
| `NumericalError` | Bracketed inversion failed to converge |
| `MethodError` | Unknown or unsupported method key requested |

All three are importable from `exactcis`.

---

## Edge cases an agent should handle

- **Zero cell(s):** `wald` applies 0.5 continuity correction only when a zero
  is present; `wald_haldane` always applies it. The conditional methods handle
  zeros without correction.
- **All-zero row or column:** raises `ValidationError`.
- **Singleton conditional support:** returns `(0, +∞)` with `point=None`.
- **Very large margins:** exact conditional summation is complete but can be
  slow. Warn the user; do not switch to an asymptotic method silently.

---

## Generating code — checklist

Before emitting any ExactCIs code, confirm:

1. The sampling design is identified and mapped to the correct `Design` enum.
2. Cell labels match the `a b / c d` orientation above.
3. `alpha` is in `(0, 1)` and not at a floating-point extreme.
4. The estimand (OR, RR, PR) is identified from the design before choosing the
   call (`compute_or_with_policy` vs `compute_rr_with_policy` vs
   `compute_pooled_or`).
5. The `method` key, if specified, is one of the stable keys for that
   design/estimand combination (query `method_registry()` if unsure).

---

## Further reading

- [README.md](README.md) — installation, quick start, statistical conventions
- [docs_md/api.md](docs_md/api.md) — full return types, exceptions, per-method examples
- [docs_md/methods.md](docs_md/methods.md) — construction, calibration, limitations per method
- [CHANGELOG.md](CHANGELOG.md) — user-facing change history
- [CITATION.cff](CITATION.cff) — citation metadata
