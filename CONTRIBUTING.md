# Contributing to ExactCIs

ExactCIs keeps a deliberately small public statistical boundary. Proposals
should identify the sampling design, estimand, construction, endpoint policy,
failure policy, and validation source before implementation begins.

The current 1.2.0 extension remains Boschloo OR with a T1-min outward hull.
See the [release roadmap](docs_md/roadmap.md) for later matching tests,
one-sided bounds and likelihood-ratio work. A future feature does not become a
prerequisite for this release.

## Development setup

Use a supported Python version (3.11 through 3.14) and `uv`:

```bash
uv sync --frozen --extra dev --extra docs
uv run pytest
```

## Required checks

```bash
uv run ruff check src tests
uv run ruff format --check src tests
uv run mypy src/exactcis
uv run pytest --cov=src/exactcis --cov-branch --cov-report=term-missing
uv run mkdocs build --strict
```

Build and inspect distributions before requesting release review:

```bash
uv run python -m build
uv run python -m twine check dist/*
python tools/check_distribution_contents.py dist/*
```

## Statistical changes

A numerical-method change must be isolated from documentation restructuring or
dependency upgrades. Its commit or pull-request description must state:

1. the mathematical definition and table orientation;
2. the previous defect or reason for change;
3. the implementation change;
4. the independent oracle and exact options;
5. focused interior, boundary, invariance, and failure tests; and
6. every changed output with a mathematical explanation.

Do not regenerate reference fixtures solely because output differs. First
reconcile estimand, conditioning, tail ordering, orientation, and tolerance.
Never weaken a tolerance or substitute another method to make CI pass.

## Public boundary

Keep clinical adjudication, private data, publication machinery, general research
outputs and accelerator orchestration outside this repository. The focused
`formal/` checker dependency closure is an explicit repository-only exception,
bounded by its [source manifest](formal/checked-reference-manifest.json).
Preserve its pinned inputs, schemas and retained receipts; do not import the
unfinished producer programme or treat repository-tool acceptance as stable
package activation or comprehensive formal assurance.

Add stable methods to the canonical registry only within the agreed release
scope, and regenerate the method documentation in the same focused change.
Preserve generated method, capability and timing blocks by using their existing
check/generation tools. Keep historical changelog entries and frozen evidence
byte-identical unless a separately reviewed correction requires otherwise.

Use conventional commit prefixes such as `feat:`, `fix:`, `test:`, `docs:`,
`build:`, `ci:`, and `security:`. Keep fixture changes separate from numerical
logic changes.
