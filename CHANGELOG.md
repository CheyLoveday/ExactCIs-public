# Changelog

This file records user-facing changes only. `1.0.0rc1` is an unreleased
candidate for `1.0.0`; no package-index publication or release tag is implied.

## [1.0.0rc1] - Unreleased

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
