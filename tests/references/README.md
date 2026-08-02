# Independent statistical references

These files are not Python-generated golden snapshots. Each records the source
implementation, version, function, options, table orientation, method
definition, tolerance, generation route, and ExactCIs source revision.

- `conditional_mpmath.json`: independently summed 80-digit FNCH tails for the
  central and Mid-P intervals.
- `exact2x2.json`: R `exact2x2` 1.6.8 ordered-exact intervals and p-values.
- `propcis_rr.json`: R `PropCIs` 0.3-0 Koopman-Nam score limits.
- `statsmodels_pooled.json`: statsmodels 0.14.5 Mantel-Haenszel/RBG results.

Reference files are reviewed evidence. Do not refresh them because a package
result changes; first reconcile the estimand, sampling model, ordering, options,
and orientation.
