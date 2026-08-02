"""Public exception hierarchy for ExactCIs."""

from __future__ import annotations

from typing import Any


class ExactCIsError(Exception):
    """Base class for package errors."""


class ValidationError(ExactCIsError, ValueError):
    """Input values do not satisfy the documented contract."""


class DesignError(ExactCIsError, ValueError):
    """A design, estimand, and method combination is incoherent."""


class UnsupportedMethodError(ExactCIsError, ValueError):
    """A requested method is not shipped for the declared design."""


class NonIdentifiableError(ExactCIsError, ValueError):
    """The requested point estimand is not identified by the observed data."""


class NumericalError(ExactCIsError, RuntimeError):
    """A numerical calculation failed its acceptance criterion.

    Numerical failures are never converted into a different interval method.
    The optional context fields are suitable for logging without containing
    private data or machine-local state.
    """

    def __init__(
        self,
        message: str,
        *,
        method: str | None = None,
        side: str | None = None,
        diagnostics: dict[str, Any] | None = None,
    ) -> None:
        super().__init__(message)
        self.method = method
        self.side = side
        self.diagnostics = diagnostics or {}


__all__ = [
    "DesignError",
    "ExactCIsError",
    "NonIdentifiableError",
    "NumericalError",
    "UnsupportedMethodError",
    "ValidationError",
]
