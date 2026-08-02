.PHONY: sync lint typecheck test coverage docs build check audit clean

sync:
	uv sync --frozen --extra dev --extra docs --extra release --extra security

lint:
	uv run ruff check src tests examples tools
	uv run ruff format --check src tests examples tools

typecheck:
	uv run mypy src/exactcis

test:
	uv run pytest

coverage:
	uv run pytest --cov=src/exactcis --cov-branch --cov-report=term-missing

docs:
	uv run mkdocs build --strict
	uv run python tools/check_method_docs.py

build:
	uv run --extra release python -m build
	uv run --extra release python -m twine check dist/*
	uv run python tools/check_distribution_contents.py dist/*

check: lint typecheck test coverage docs build
	uv run python tools/check_public_tree.py
	uv run python tools/run_readme_examples.py --source README.md

audit:
	uv run --extra security python tools/audit_dependencies.py
	uv run --extra security python tools/check_history_secrets.py
	uv run python tools/check_repository_hygiene.py

clean:
	@echo "Remove generated build, coverage, and documentation outputs explicitly."
