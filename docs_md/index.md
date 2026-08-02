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

Start with the repository README for installation and an executable example.
Use [Supported methods](methods.md) to choose a construction and
[API contract](api.md) for endpoint and failure semantics.

The `1.0.0rc1` tree is an unpublished candidate. Conditional methods condition
on both margins; no universal exactness or unconditional coverage claim is
made. Numerical failure raises explicitly and never selects another method.
