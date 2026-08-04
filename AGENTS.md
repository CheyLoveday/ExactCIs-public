# ExactCIs — Agent Instructions

Guidance for LLM agents and coding tools that **call** ExactCIs. Prefer this
file over inventing APIs. When uncertain, open `docs_md/api.md` or query
`method_registry()`.

---

## Package identity

- Design-aware confidence intervals for **2×2 tables** (and prespecified
  independent strata for a common odds ratio).
- **Not** a general statistics toolkit. Sampling design is always explicit.
- **Fail-closed:** unsupported inputs and numerical failures raise; no method
  silently replaces another.
- Python **3.11–3.13**. Runtime: **standard library only**.
- Current release candidate: `exactcis==1.0.0rc2`.

```bash
pip install exactcis==1.0.0rc2
```

---

## Table orientation (fixed)

```text
             outcome +   outcome -
exposed +        a           b
exposed -        c           d
```

- Counts are finite non-negative integers no larger than `10**12` per cell.
- Swapping rows or columns reciprocates ratio estimands.
- **Never relabel cells between related calls.**

---

## Designs

Use `exactcis.Design` only:

| Enum | Meaning |
|------|---------|
| `CASE_CONTROL_FIXED_MARGIN` | Retrospective; both margins fixed |
| `COHORT_BINOMIAL` | Two independent prospective groups |
| `CROSS_SECTIONAL` | Single sample; two exposure groups |
| `STRATIFIED_CASE_CONTROL` | Prespecified independent case-control strata |
| `STRATIFIED_COHORT` | Prespecified independent cohort strata |

Risk / prevalence ratios are **not identified** from
`CASE_CONTROL_FIXED_MARGIN`. That combination raises `DesignError`.

Stratified single-table OR/RR policy calls are wrong: use `compute_pooled_or`
with a stratified design.

---

## Alpha

- `alpha` is the **two-sided** significance level (`0.05` → 95% CI).
- Certified domain: **`1e-12 < alpha < 1 - 1e-12`**.
- Outside that range → `ValidationError` **before** any numerical work.

---

## Prefer the policy API

Root exports include direct methods (`exact_ci_*`, `ci_wald*`, …), but agents
should default to the design-aware policy functions.

### Odds ratio

```python
from exactcis import Design, compute_or_with_policy

# Fixed-margin case-control (default method: "conditional")
result = compute_or_with_policy(
    12, 5, 8, 10,
    design=Design.CASE_CONTROL_FIXED_MARGIN,
    # method="conditional",  # or "midp", "minlike", "blaker"
    alpha=0.05,
)

# Independent binomial (default method: "wald")
result = compute_or_with_policy(
    12, 5, 8, 10,
    design=Design.COHORT_BINOMIAL,  # or CROSS_SECTIONAL
    # method="wald",  # or "wald_haldane"
    alpha=0.05,
)
```

### Risk ratio / prevalence ratio

```python
from exactcis import Design, compute_rr_with_policy

# COHORT_BINOMIAL → risk ratio; CROSS_SECTIONAL → prevalence ratio
# Default method: "score_rr" (also "wald_rr")
result = compute_rr_with_policy(
    12, 5, 8, 10,
    design=Design.COHORT_BINOMIAL,
    alpha=0.05,
)
```

### Stratified common odds ratio (Mantel–Haenszel / RBG)

```python
from exactcis import Design, compute_pooled_or

result = compute_pooled_or(
    [(12, 5, 8, 10), (8, 2, 15, 20)],  # iterable of (a, b, c, d) tuples
    design=Design.STRATIFIED_CASE_CONTROL,  # or STRATIFIED_COHORT
    alpha=0.05,
)
```

- Strata must be **prespecified independent** tables as **4-tuples**, not dicts.
- Method is fixed: Mantel–Haenszel with Robins–Breslow–Greenland variance.
- Empty strata inputs, zero pooled cross-products, or wrong design fail
  explicitly.

---

## Result objects

### `InferenceResult` (policy OR / RR)

Attributes: `point`, `lower`, `upper`, `confidence_level`, `design`,
`estimand`, `method`, `construction`, `status`.

- `estimand` is an `Estimand` enum (`OR` / `RR`), not a free string.
- Interval width uses `confidence_level` (= `1 - alpha`), not an `.alpha` field.
- `point` is a `float` on successful policy returns.

### `PooledORResult`

Attributes: `point`, `lower`, `upper`, `confidence_level`, `design`, `method`,
`construction`, `strata` (count), `status`.

### Policy vs direct methods (singleton support)

- **Policy** `compute_or_with_policy` on fixed-margin tables: if conditioning
  leaves **singleton support**, the call raises **`NonIdentifiableError`**
  (full set, no unique point). It does **not** return `point=None`.
- **Direct** `exact_ci_conditional` / `exact_ci_midp` / …: boundary and
  singleton cases use endpoints `0.0` and/or `math.inf` (see `docs_md/api.md`).

Do not conflate those contracts.

---

## Method registry

```python
from exactcis.estimands import method_registry, methods_for
from exactcis import Design, Estimand

method_registry()  # all stable MethodSpec records
methods_for(Design.CASE_CONTROL_FIXED_MARGIN, Estimand.OR)
```

Stable keys (do not invent others):

| Design family | Estimand | Keys |
|---------------|----------|------|
| Fixed-margin case-control | OR | `conditional`, `midp`, `minlike`, `blaker` |
| Cohort / cross-sectional | OR | `wald`, `wald_haldane` |
| Cohort / cross-sectional | RR | `score_rr`, `wald_rr` |
| Stratified | OR | `mantel_haenszel` (via `compute_pooled_or` only) |

---

## Exceptions (all importable from `exactcis`)

| Exception | Typical trigger |
|-----------|-----------------|
| `ExactCIsError` | Base class |
| `ValidationError` | Bad counts, alpha outside certified domain |
| `DesignError` | Design / estimand / route incoherent |
| `UnsupportedMethodError` | Unknown or unsupported method key |
| `NonIdentifiableError` | Point not identified (e.g. singleton MLE, MH) |
| `NumericalError` | Inversion/certification failed |

There is **no** `MethodError`.

**Do not** catch `NumericalError` (or any ExactCIs error) and retry with a
different method. Surface the failure.

---

## Zero cells and sparsity (short)

- OR `wald`: 0.5 continuity correction when a zero cell is present.
- OR `wald_haldane`: always adds 0.5 to all four cells.
- Exact conditional family: no Wald-style continuity correction.
- Empty comparison groups (independent-binomial) and all-zero structure fail
  validation where required.
- Exact conditional work is complete-support; very wide margins can be slow —
  **warn**, do not silently switch to Wald.

---

## Agent checklist (before emitting code)

1. Sampling design is known and mapped to the correct `Design` value.
2. Cells match `a b / c d` above.
3. `alpha` satisfies `1e-12 < alpha < 1 - 1e-12`.
4. Estimand matches design (no RR from fixed-margin case-control; stratified
   common OR only via `compute_pooled_or`).
5. Method key is stable for that design/estimand (`methods_for` / registry).
6. Pooled strata are 4-tuples with an explicit stratified `design=`.
7. Errors are surfaced; no silent method substitution.

---

## Further reading

- [README.md](README.md) — install and conventions
- [docs_md/api.md](docs_md/api.md) — authoritative API contract
- [docs_md/methods.md](docs_md/methods.md) — constructions and limits
- [CHANGELOG.md](CHANGELOG.md) — user-facing history
- [CITATION.cff](CITATION.cff) — citation metadata
