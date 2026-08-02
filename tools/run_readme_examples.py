#!/usr/bin/env python3
"""Extract and execute the designated README Python example blocks."""

from __future__ import annotations

import argparse
import re
from pathlib import Path

START = "<!-- exactcis-example:start -->"
END = "<!-- exactcis-example:end -->"
PYTHON_FENCE = re.compile(r"```python\n(?P<code>.*?)```", re.DOTALL)


def extract_examples(text: str) -> tuple[str, ...]:
    """Return Python snippets within explicit executable-example markers."""
    examples: list[str] = []
    remainder = text
    while START in remainder:
        _, _, marked = remainder.partition(START)
        region, separator, remainder = marked.partition(END)
        if not separator:
            raise ValueError(f"missing closing README example marker {END}")
        matches = tuple(match.group("code") for match in PYTHON_FENCE.finditer(region))
        if len(matches) != 1:
            raise ValueError("each README example marker must contain one Python fence")
        examples.extend(matches)
    if not examples:
        raise ValueError("README contains no marked executable Python example")
    return tuple(examples)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", required=True, type=Path)
    args = parser.parse_args()
    examples = extract_examples(args.source.read_text(encoding="utf-8"))
    for index, example in enumerate(examples, start=1):
        namespace = {"__name__": f"__exactcis_readme_example_{index}__"}
        exec(compile(example, f"{args.source}:example-{index}", "exec"), namespace)
        print(f"OK: README example {index}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
