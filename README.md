# ExactCIs

ExactCIs provides design-aware inference for sparse 2 × 2 tables in Python,
with explicit sampling assumptions, documented interval constructions, and
fail-closed numerical behaviour.

This release does not claim universal exactness, unconditional coverage for
conditional procedures, clinical validation, or formal verification.

## Installation

ExactCIs supports Python 3.11 through 3.13 and has zero runtime dependencies.
(The lower bound is intentional: the public API and typing assume 3.11+.)

```bash
python -m pip install exactcis
```

For a reproducible pin to the current release:

```bash
python -m pip install exactcis==1.1.1
```

For development and documentation checks (from a source checkout):

```bash
uv sync --frozen --extra dev --extra docs
```

## Quick start

The package-wide table orientation is defined before this first calculation:

```text
             outcome +   outcome -
exposed +        a           b
exposed -        c           d
```

Declare the sampling design explicitly. A fixed-margin case-control table uses
the conditional odds-ratio lane:

<!-- exactcis-example:start -->
```python
from exactcis import Design, compute_or_with_policy

result = compute_or_with_policy(
    10,
    2,
    5,
    20,
    design=Design.CASE_CONTROL_FIXED_MARGIN,
)

assert result.lower <= result.point <= result.upper
print(
    f"{result.method} ({result.construction}): "
    f"point={result.point:.6g}  ({result.lower:.6g}, {result.upper:.6g})"
)
```
<!-- exactcis-example:end -->

The same four numbers must not be relabelled as a risk ratio under a
fixed-margin case-control design. For two independent cohort groups, declare
`Design.COHORT_BINOMIAL` and call `compute_rr_with_policy`.

## Table orientation

Throughout the package:

```text
             outcome +   outcome -
exposed +        a           b
exposed -        c           d
```

- The odds ratio is `a d / (b c)`, where defined.
- The cohort risk ratio is `[a / (a + b)] / [c / (c + d)]`, where identified.
- Cross-sectional use of the same row-proportion ratio is a prevalence ratio.

Counts must be finite, non-negative integers no larger than `10**12` per cell.
Rows identify the two comparison groups; columns identify outcome status.
Swapping either pair reciprocates the corresponding ratio and transforms finite
interval endpoints accordingly.

## Supported designs, estimands, and methods

The machine-readable source of truth is
`exactcis.estimands.method_registry()`. The complete generated table, including
construction, calibration statement, and limitations, is in
[Supported methods](https://github.com/CheyLoveday/ExactCIs-public/blob/main/docs_md/methods.md).

| Design | Effect measure | Stable method keys | Default policy method |
|---|---|---|---|
| Fixed-margin case-control | odds ratio | `conditional`, `midp`, `minlike`, `blaker` | `conditional` |
| Cohort, two independent binomials | odds ratio | `wald`, `wald_haldane` | `wald` |
| Cohort, two independent binomials | risk ratio | `score_rr`, `wald_rr` | `score_rr` |
| Cross-sectional groups | prevalence odds ratio | `wald`, `wald_haldane` | `wald` |
| Cross-sectional groups | prevalence ratio | `score_rr`, `wald_rr` | `score_rr` |
| Prespecified independent strata | common odds ratio | `mantel_haenszel` | explicit `compute_pooled_or` call |

Risk or prevalence ratios are not identified from fixed-margin retrospective
case-control sampling. Same-study marginal pooling without participant-level
union or dependence information is outside this release.
`compute_pooled_or` accepts one or more strata; a single stratum is valid
mathematically but is usually a modelling mistake when “pooled” was intended.

## Statistical conventions and assumptions

`alpha` is the two-sided significance level, so `alpha=0.05` requests a 95%
confidence set. The numerically certified domain is the open interval
`1e-12 < alpha < 1 - 1e-12`; unsupported extremes raise `ValidationError`
before quantile evaluation or inversion. Conditional methods use Fisher's
noncentral-hypergeometric law and condition on both margins. `conditional`
inverts inclusive equal tails;
`midp` uses half the observed mass in each tail; `minlike` uses inclusive
probability-mass ordering; and `blaker` uses the smaller inclusive tail as its
acceptability ordering.

The Wald methods and the Mantel-Haenszel/Robins-Breslow-Greenland construction
are asymptotic. `score_rr` inverts the Koopman-Nam score statistic for two
independent binomial groups. Conditional and unconditional/asymptotic methods
are not expected to agree by construction.

## Edge cases and numerical behaviour

- Conditional support endpoints map to odds-ratio endpoints `0` and `+∞`.
- Singleton conditional support yields the full confidence set `(0, +∞)`;
  the high-level policy refuses to invent a unique point estimate.
- Empty independent-binomial groups are invalid.
- A risk/prevalence ratio with zero events in both groups has confidence set
  `(0, +∞)` but no policy-level point estimate.
- `ci_wald` adds 0.5 to every cell only when a zero cell is present;
  `ci_wald_haldane` always applies that correction.
- Numerical inversion is bracketed and checked. Failure raises
  `NumericalError`; ExactCIs never returns another method as a fallback.
- A finite configured search-domain limit is never reported as an inferential
  endpoint. Unsupported significance levels fail validation instead.
- Conditional probability evaluation traverses outward from the mode and omits
  only terms that underflow exactly in binary64; returned values are
  bit-identical to the full recurrence. `conditional` and `midp` reject support
  widths above 10,000,000 before preparation; `minlike` and `blaker` reject
  widths above 1,000,000 before ordered-hull preparation. These limits always
  raise `NumericalError`. The ordered-hull evaluation budget can also refuse a
  narrower call, so its width cap is a certification ceiling, not a runtime
  promise. Prefer asymptotic methods when such scales are expected and exact
  conditioning is not required.
- Sparse independent-binomial Wald OR intervals can look successful while
  empirical coverage and failure rates deviate from the nominal 95%; see the
  coverage and timing tables in
  [Supported methods](https://github.com/CheyLoveday/ExactCIs-public/blob/main/docs_md/methods.md).

See [API contract](https://github.com/CheyLoveday/ExactCIs-public/blob/main/docs_md/api.md)
for return types, exceptions, and individual method examples.

## Experimental and compatibility methods

This release has no retained experimental or compatibility-only method.
Historical evidence-policy, unconditional, Bayesian-evidence, plotting,
reporting, batch, accelerator, and clinical-adjudication routes are not imported
or shipped.
Unknown method keys fail explicitly and do not participate in automatic
selection.

## API documentation

The stable root API is listed in
[API contract](https://github.com/CheyLoveday/ExactCIs-public/blob/main/docs_md/api.md).
Only the package root exports (see `exactcis.__all__`) and
`exactcis.estimands` are stable public surfaces. Other non-underscore
implementation packages under `exactcis.*` have no compatibility promise.
Lower-level registry inspection is available from `exactcis.estimands`;
helpers beginning with an underscore are internal.

## Validation and reproducibility

The release tests cover canonical interior and boundary tables, reciprocal
transformations, confidence-level nesting, endpoint domains, explicit solver
failure, and direct calls to every stable method. Independent fixtures record:

- 80-decimal mpmath finite-support calculations for central and Mid-P limits;
- R `exact2x2` 1.6.8 minimum-likelihood and Blaker results;
- R `PropCIs` 0.3-0 Koopman-Nam score limits; and
- statsmodels 0.14.5 Mantel-Haenszel/RBG results.

Every fixture records its function, options, orientation, definition,
tolerance, generator or derivation, version, and source revision. The release
workflow also executes this README example against source, wheel, and sdist.

## Contributing

See [CONTRIBUTING.md](https://github.com/CheyLoveday/ExactCIs-public/blob/main/CONTRIBUTING.md).
Statistical changes require a stated mathematical definition, an independent
oracle, focused boundary tests, and a separate explanation of any changed
outputs.

## Citation

See [CITATION.cff](https://github.com/CheyLoveday/ExactCIs-public/blob/main/CITATION.cff)
and [CITATION.txt](https://github.com/CheyLoveday/ExactCIs-public/blob/main/CITATION.txt).
Cite the exact version and Git revision analysed. No DOI is assigned yet.

## Licence

ExactCIs is distributed under the
[MIT License](https://github.com/CheyLoveday/ExactCIs-public/blob/main/LICENSE).
