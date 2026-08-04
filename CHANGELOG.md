# Changelog

This file records user-facing changes only.

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
