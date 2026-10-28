# Release roadmap

Updated 28 October 2026. The current release keeps its agreed scope. Later
versions below are proposed sequencing labels, with no publication dates or
package-version changes implied.

## Current package and Boschloo work

The published package is `exactcis==1.1.2`. Its stable methods cover fixed-margin
conditional OR inference, independent-binomial OR/RR inference and prespecified
independent-strata common OR inference. See the [method registry](methods.md)
and [API contract](api.md) for constructions, assumptions and failure behavior.
Mid-P and asymptotic intervals retain their separate calibration claims.

Release 1.2.0 adds only Boschloo OR for the specified independent-binomial
designs, using the T1-min outward hull contract. The
[release manifest](unconditional_exact_specification.md#b1-release-boundary-and-manifest)
is authoritative. Barnard, exact unconditional RR and complete topology remain
deferred and nonblocking.

A [callable checked Boschloo reference](https://github.com/CheyLoveday/ExactCIs-public/blob/main/formal/BOSCHLOO_METHOD.md)
is available as a repository tool. Statistical output requires actual Lean
literal-byte acceptance; resource refusals and inconclusive work do not produce
a statistical result. This is separate from activation in the stable package
API and comprehensive independent formal-code verification, which retain their
existing completion gates. General producer termination and completeness remain
outside the current release's claims and are not new release blockers.

## Proposed later releases

| Release | Intended outcome | Required specification and evidence |
|---|---|---|
| **1.3.0** | Matching OR/RR hypothesis tests and one-sided confidence bounds | Match the interval's design, ordering, correction and nuisance treatment; define null values, alternatives, equality rules and result types; independently validate inversion and preserve two-sided defaults |
| **1.4.0** | Diagnostic LR+ and LR− with confidence intervals, sensitivity and specificity | Specify the diagnostic sampling model and table orientation; validate reuse of RR kernels, boundary behavior and marginal coverage; qualify binomial companions independently |
| **1.5.0** | Profile-likelihood inference and explicitly defined hypothesis-evidence ratios | Freeze likelihoods, hypotheses, priors and calibration; distinguish parameter confidence intervals, numerical error, prior sensitivity and any resampling uncertainty |

These additions do not become prerequisites for 1.2.0. A release starts with a
small fixed method/design matrix, then mathematical specification,
implementation, independent qualification and package integration. A later
release cannot delay an earlier release that satisfies its own acceptance gates.

## Matching tests and directional bounds

A test must use the same statistical construction as its associated interval.
Attaching a Fisher p-value to an unrelated Wald or score interval would not
provide that match. User-specified null ratios initially require finite positive
values; boundary-null tests need their own contract.

A greater alternative supplies a lower ratio bound, while a less alternative
supplies an upper bound. Directional inversion uses `alpha`, rather than the
`alpha/2` allocation of a central two-sided interval. Preserve accepted equality
where specified. A certified Boschloo decision at a level and a numerically
enclosed p-value need distinct reporting and unresolved-work semantics.

Minimum-likelihood and Blaker inversion can produce disconnected confidence
sets. The displayed hull can contain rejected parameter values, so matching a
test does not imply that every point inside the hull is accepted. Complete
component enumeration remains optional.

## Likelihood ratios and their uncertainty

| Quantity | Meaning | Appropriate uncertainty or calibration |
|---|---|---|
| Diagnostic LR+ and LR− | Ratios of test-result probabilities in reference-positive and reference-negative groups | Confidence intervals for population probability ratios under the stated sampling design |
| Profile-likelihood ratio | Relative likelihood as an OR or RR varies | Parameter confidence intervals and tests under an explicit calibration; an interior Wilks approximation is asymptotic |
| Integrated evidence ratio or Bayes factor | Relative support for specified hypotheses or models | Hypothesis definitions, proper priors where applicable, numerical diagnostics and sensitivity to chosen assumptions |

For diagnostic inference, the initial scope is one binary test against an
observed reference standard, with independent subjects and a prespecified test
rule. LR+ and LR− are ratios of binomial probabilities under that model. Score
and log-Wald intervals are approximate; exact unconditional LR intervals would
require a separately qualified exact RR construction. Sensitivity and specificity
need their own binomial interval methods and labels.

Initial diagnostic intervals are marginal: several 95% intervals are not a joint
95% confidence region. Dividing separate sensitivity/specificity interval
endpoints does not automatically yield a valid LR interval. Population predictive
values additionally need a population-prevalence contract; sample prevalence in
a case–control study cannot automatically supply it.

Evidence ratios require separate result types. Prior-sensitivity ranges and
numerical integration enclosures are not ordinary frequentist confidence
intervals. Any bootstrap band needs an explicit sampling model, statistic,
replicate budget, failure policy and interpretation. Posterior model odds also
require prior model odds; an evidence ratio alone is not a probability of
pathogenicity.

## Validation and later candidates

Each method requires a method card, independent numerical references, boundary
and failure tests, measured resource limits and explicit stop conditions.
Mathematical argument, kernel verification, Python correspondence and public
package qualification are separate evidence claims. Finite coverage grids
describe those parameter points; they do not establish a universal theorem.

Stop promotion when a mathematical contract remains unresolved, independent
results disagree without explanation, calibration is mislabelled, or resource
failure can silently alter the method or decision. Refusal remains distinct from
statistical rejection.

Later candidates include exact unconditional RR, risk difference, pooled RR,
paired designs, power/sample-size planning and confidence curves. Each requires
a new bounded scope decision. None changes the current release manifest.
