# Release workflow configuration

The release workflow is intentionally inert in a new repository. Before an
authorised maintainer can dispatch it, all of the following must be configured:

1. Keep the repository variable `EXACTCIS_RELEASE_WORKFLOW_ENABLED` absent or
   set to `false` until a release has been approved.
2. Configure `testpypi` and `pypi` GitHub environments for PyPI trusted
   publishing. Do not add long-lived package-index tokens.
3. Require at least one maintainer reviewer on the `pypi` environment. This is
   the manual production-promotion gate.
4. Protect the candidate tag namespace and require the public CI checks.
5. Create the candidate tag only after the version, changelog, citations, and
   release input have been reviewed together.

When those controls are in place, set the repository variable to `true`,
dispatch the workflow from the exact candidate tag, and type the authorization
phrase shown by the workflow input. The workflow builds only once, uploads the
same verified files to TestPyPI and PyPI, and creates the GitHub release only
after production publication succeeds.
