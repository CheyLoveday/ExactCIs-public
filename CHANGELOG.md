# Changelog

This file records user-facing changes only.

## [Unreleased]

### Changed

- `exact_ci_minlike` and `exact_ci_blaker` now return a numerically certified
  interval hull of the complete inverted confidence set, which may be
  disconnected. The previous search stopped at the first transition around the
  conditional MLE and could omit accepted parameters; on `(4, 300, 150, 4)` at
  `alpha = 0.01` the upper endpoint moves from 0.0021641 to 0.0022976. A region
  is now excluded only by a conservative certified bound, direct evaluations
  only ever widen the interval, structural endpoints are exact, and an
  uncertifiable enclosure raises `NumericalError` rather than returning a
  best-effort interval. Contract in `docs_md/ordered_hull_specification.md`;
  registry wording updated accordingly. On connected accepted sets endpoints
  agree with 1.0.0 to better than 3e-8 on the log scale, always outward.
- Fisher noncentral hypergeometric evaluation uses a mode-centred
  adjacent-ratio kernel prepared once per inversion, restoring linear scaling
  in support width (support 3001: 95.1s to 0.29s per conditional interval).
- Root acceptance is certified by the retained sign-changing bracket width, the
  bound on the returned log parameter, instead of function residuals. The score
  gate previously collapsed to an absolute 1e-8 test and refused
  well-conditioned roots near total N of 2e9.
- The Koopman-Nam constrained-MLE discriminant uses cancellation-free
  sum-of-squares forms; the negative-result repair clamp is removed.

### Documentation

- Sparse cohort Wald coverage table and method-selection guidance.
- Conditional exact runtime table and soft threshold notes.
- Explicit Python ≥3.11 floor rationale in the API contract.

## [1.0.0] - 2026-08-04

First stable release (`exactcis==1.0.0`, tag `v1.0.0`).

### Added

- Production install path: `pip install exactcis`.
- Project URLs, absolute documentation links, and published-state README.
- Hardened public numerical and API surface carried forward from the 1.0.0rc2
  candidate (required `design`, cancellation-safe log-choose, scale-aware
  residuals, log-space Wald, 1e12 count bound, sdist without `tools/`).

### Changed

- Development Status classifier is Production/Stable.
- Pre-release install caveats removed from the primary Installation section.

## [1.0.0rc2] - 2026-08-04

Published packaging and numerical hardening release candidate (`exactcis==1.0.0rc2`,
tag `v1.0.0-rc.2`).

### Fixed

- Published README install path and project URLs for PyPI long description.
- Absolute documentation links; sdist no longer ships `tools/`.
- Cancellation-resistant log-binomial coefficients; scale-aware inversion residual gates.
- Log-space Wald OR point and non-finite endpoint rejection.
- Required `design` on raw interval routes; falsy `method` no longer selects defaults.
- Count bound `1e12`; tighter `NumericalError` wrapping; examples print results.

### Changed

- Release-tool tests skip when `tools/` or `.git` are absent (sdist-friendly).

## [1.0.0rc1] - 2026-08-04

Published to PyPI as `exactcis==1.0.0rc1` and tagged `v1.0.0-rc.1` on the
public repository. This remains a pre-release candidate for `1.0.0`.

### Added

- A design-aware public API for fixed-margin case-control, independent-binomial
  cohort and cross-sectional, and prespecified stratified designs.
- Stable conditional, Mid-P, minimum-likelihood, Blaker, Wald odds-ratio,
  Koopman-Nam score risk/prevalence-ratio, Wald risk/prevalence-ratio, and
  Mantel-Haenszel common-odds-ratio routes.
- Typed result objects, explicit method metadata, independent reference
  fixtures, installed-package smoke tests, and artefact-boundary checks.

### Changed

- Method names now identify their statistical construction; conditional,
  asymptotic, and stratified methods are not represented as interchangeable.
- Invalid designs, unidentified estimands, unsupported methods, and numerical
  nonconvergence now raise explicit exceptions. No method silently substitutes
  another construction after failure.
- Significance levels must satisfy the numerically certified open domain
  `1e-12 < alpha < 1 - 1e-12`; unsupported floating-point extremes fail
  validation before quantile evaluation or interval inversion.
- The public pooled route is explicitly the Mantel-Haenszel/RBG construction;
  the private conditional-profile implementation and its search domain are not
  shipped or reachable from the public package.
- The supported interpreter range is Python 3.11 through 3.13.
- The stable runtime is standard-library-only. Development, documentation,
  release, security, and validation dependencies are isolated in named extras.

### Compatibility

- The first public candidate intentionally provides no legacy root aliases.
- Historical policy, plotting, reporting, batching, accelerator, and clinical
  workflow surfaces are omitted rather than retained as compatibility shims.
- No experimental method is selected automatically or shipped as stable.

### Known limitations

- Exact odds-ratio methods condition on both margins and can be conservative;
  Mid-P does not guarantee nominal coverage at every parameter value.
- Wald and stratified intervals are asymptotic and can be inaccurate for sparse
  tables or poorly supported common-effect assumptions.
- Risk and prevalence ratios require independent-binomial group designs.
- Exact full-support summation can be slower for very wide conditional support.
