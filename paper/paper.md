---
title: "exactcis: Design-aware confidence intervals for sparse 2x2 tables in Python"
tags:
  - Python
  - statistics
  - confidence intervals
  - contingency tables
  - exact inference
authors:
  - name: Chey Loveday
    affiliation: 1
affiliations:
  - name: "[AFFILIATION TO CONFIRM]"
    index: 1
date: 20 August 2026
bibliography: paper.bib
---

# Summary

`exactcis` is a Python package for design-aware effect estimates and confidence
intervals from sparse 2x2 tables. Version 1.1.2 requires callers to identify
the sampling design, routes each supported request through a machine-readable
method registry, and raises typed exceptions for unidentified or unsupported
combinations. Its stable public surface covers conditional odds-ratio
intervals for fixed-margin case-control sampling, asymptotic odds-ratio
intervals for independent groups, score and Wald intervals for risk or
prevalence ratios, and Mantel--Haenszel common-odds-ratio estimation for
prespecified independent strata. The base installation has no runtime
dependencies and supports Python 3.11--3.13.

The conditional implementation prepares the finite Fisher noncentral
hypergeometric distribution once, reconstructs probability mass from its mode
using adjacent ratios, and uses safeguarded inversion. Minimum-likelihood and
Blaker procedures return a certified interval hull containing the complete
inverted accepted set. This wording is deliberate: a discrete accepted set may
be disconnected, and the public endpoint pair does not claim that every
interior point is accepted. Numerical resource limits, structural endpoints,
and unsupported alpha values fail explicitly rather than silently switching
methods.

# Statement of need

A 2x2 table does not by itself determine an inferential model. Under fixed
margins in a retrospective case-control analysis, the conditional odds ratio
is identified through a noncentral hypergeometric law. Under independent row
sampling, risks and their ratio are identified; the same arithmetic is a
prevalence ratio in a cross-sectional design. Applying a familiar interval
without recording that distinction can produce a plausible number with the
wrong scientific label.

Python users can assemble many relevant calculations from general statistical
libraries, while R provides mature specialist tools such as `exact2x2`
[@Fay2010] and `PropCIs` [@PropCIs]. Those packages are important independent
comparators for `exactcis`. The narrower need addressed here is an installable
Python interface in which design is a required part of the call, public method
metadata is executable, and invalid compositions fail closed. The package is
intended for reproducible statistical analysis and method comparison; it is
not clinically validated and is not an automated clinical decision system.

# State of the field

General Python libraries provide contingency-table summaries and asymptotic
inference [@Seabold2010], and specialist R implementations provide several
exact and score constructions. Interoperability remains valuable, so
`exactcis` retains conventional numerical entry points and validates selected
outputs against high-precision finite-support calculations and external R and
Python references. Its distinctive contribution is not a claim to replace
those projects. It is the combination of explicit design routing, a compact
zero-dependency public surface, published resource ceilings, and regression
evidence for confidence-set inversion that cannot assume connectedness.

The release distinguishes four related but non-equivalent ideas: a method's
statistical calibration, numerical correctness within a stated envelope,
agreement with an external implementation under matched conventions, and
software release integrity. Tests for one do not establish the others. This
separation is reflected in the registry, capability documentation, independent
fixtures, mutation gates, and clean wheel/source-distribution checks.

# Software design

The public API exposes a `Design` enumeration, raw interval functions, policy
functions, result dataclasses, and a typed exception hierarchy. For example,

```python
from exactcis import Design, compute_or_with_policy

result = compute_or_with_policy(
    10, 2, 5, 20,
    design=Design.CASE_CONTROL_FIXED_MARGIN,
)
```

returns a conditional point estimate of `17.899832285205957` and a 95%
confidence interval of `(2.687648678643227, 219.2826281393888)`. A risk-ratio
request under that fixed-margin design raises `DesignError`, because the
independent row risks are not identified by the declared sampling model.

Raw fixed-margin methods include inclusive equal-tail conditional, Mid-P,
minimum-likelihood, and Blaker constructions. Independent-group routes include
log-Wald odds-ratio intervals, Koopman--Nam score ratio intervals [@Koopman1984;
@Nam1995], and log-Wald ratio intervals. Prespecified independent strata use
the Mantel--Haenszel estimator [@Mantel1959] with a
Robins--Breslow--Greenland large-sample variance. Every route validates finite
non-negative integer counts, alpha, design, estimand, and construction before
returning a result.

The repository includes deterministic examples, high-precision conditional
oracles, frozen external-reference fixtures, metamorphic checks, deliberate
contract mutations, strict generated-documentation gates, and distribution
smoke tests. The companion replication command installs the immutable release,
records the import path and environment, and emits canonical scientific JSON
with SHA-256 hashes:

```bash
python -m pip install exactcis==1.1.2
python replication/jss_package_paper.py --mode minimal --show-env
```

The release is archived as tag `v1.1.2` at commit `f0cbf3c` [@ExactCIs112].

# Research impact statement

`exactcis` packages design checks and conservative numerical boundaries that
would otherwise need to be reimplemented in each sparse-table analysis. Its
machine-readable registry also gives downstream tools one source for method
names, estimands, calibration language, and limitations. The public release
therefore provides reusable infrastructure for auditable comparisons of 2x2
interval procedures.

At the date of this draft, however, the public repository is new and there is
not yet sufficient evidence of independent research adoption or a public
development history exceeding six months. Availability on PyPI, a green test
suite, and package downloads are not treated as research impact by themselves.
This section must be updated with verifiable citations, downstream use, or
other research outcomes before submission.

# AI usage disclosure

OpenAI Codex using GPT-5-family models was used for scoped code generation,
refactoring, test scaffolding, repository review, validation orchestration, and
drafting; xAI Grok provided a publication-scope review. The exact historical
model version used for every earlier interaction was not retained in the
project records and must be reconciled before submission. The human author
defined the statistical and release contracts, selected and adjudicated the
evidence, reviewed and edited the assisted outputs, ran the validation gates,
made the core design decisions, and accepts responsibility for the software
and paper. AI-generated output is not treated as an independent statistical
oracle or authorship contribution.

# Acknowledgements

The project uses independent reference implementations and the open-source
Python [@Python] and R software ecosystems. Specific contributors and funding,
if any, must be confirmed by the author before submission.

# References
