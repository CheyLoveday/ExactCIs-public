"""Check the exact, checker-only development reference slice; not proof assurance."""

from __future__ import annotations

import ast
import hashlib
import json
import re
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = "checked-reference-manifest.json"
ENTRY = "ExactCIs.Unconditional.MeteredGlobalChecker"
LEAN_TOOLCHAIN = "leanprover/lean4:v4.35.0"
SCHEMA = "exactcis.checked_boschloo_reference.slice.v2"
SCOPE = "Development checked reference; proof assurance is recorded separately"
GENERATOR = "EXACT_MERGED_FAMILY_REFERENCE_V1"
PINS = {
    "lake-manifest.json": "".join(
        (
            "96435c50",
            "9708f258",
            "31936d6f",
            "9ea5bb44",
            "af609ee2",
            "e812bcdd",
            "c5cc98a9",
            "b8ecd9fd",
        )
    ),
    "global-checker-v1.schema.json": "".join(
        (
            "b1fe2d6a",
            "c6ca678d",
            "4e5e7619",
            "eb38aa30",
            "9da3b845",
            "96574d1c",
            "39fe50eb",
            "255223fd",
        )
    ),
    "resource-profile-v1.schema.json": "".join(
        (
            "d28c2296",
            "d5a04c13",
            "868d4c48",
            "1328176f",
            "9ee06455",
            "c08a9608",
            "c5577b5f",
            "ed0f208c",
        )
    ),
}
RUNTIME = {
    "boschloo",
    "metered_algebraic",
    "metered_boschloo_polynomials",
    "metered_global_geometry",
    "metered_global_producer",
    "metered_isolate",
    "metered_localize",
    "metered_parametric",
    "metered_polynomial",
    "metered_root",
    "metered_selected_refinement",
    "metered_specialized",
    "resource_model",
}
ROOT_FILES = {
    "README.md",
    MANIFEST,
    "BOSCHLOO_METHOD.md",
    "lean-toolchain",
    "lakefile.toml",
    *PINS,
}


def path_allowed(relative: str) -> bool:
    path = Path(relative)
    parts = path.parts
    if path.is_absolute() or ".." in parts or not parts:
        return False
    if relative in ROOT_FILES:
        return True
    if (
        relative == "tools/boschloo_check"
        or relative == "tools/lean/boschloo_check.lean"
    ):
        return True
    if len(parts) == 2 and parts[0] == "tools" and path.suffix == ".py":
        return path.stem in RUNTIME
    return (
        parts[0] in {"ExactCIs", "CarfSpine"}
        and path.suffix == ".lean"
        and not any(
            part.startswith("Producer") or part.startswith(".") for part in parts
        )
    )


def lean_code(text: str) -> str:
    """Read import commands after removing nested comments and quoted strings."""
    code, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            code.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            i += 1
            while i < len(text) and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            i += 1
        else:
            code.append(text[i])
            i += 1
    if depth:
        raise ValueError("unterminated Lean comment")
    return "".join(code)


def lean_imports(text: str) -> list[str]:
    return [
        name
        for line in re.findall(r"^(?:public )?import\s+([^\n]+)", lean_code(text), re.M)
        for name in line.split()
    ]


def check(root: Path = ROOT) -> list[str]:
    formal = root / "formal"
    raw = (formal / MANIFEST).read_bytes()
    manifest = json.loads(raw)
    canonical = (
        json.dumps(manifest, sort_keys=True, separators=(",", ":")) + "\n"
    ).encode()
    errors = []
    if raw != canonical or manifest["schema"] != SCHEMA:
        errors.append("noncanonical or unsupported reference manifest")
    if (
        manifest["entry_module"] != ENTRY
        or manifest["verification_scope"] != SCOPE
        or manifest["generator"] != GENERATOR
    ):
        errors.append("reference entry, strategy or assurance ceiling differs")
    expected = manifest["files"]
    actual = {
        path.relative_to(formal).as_posix()
        for path in formal.rglob("*")
        if path.is_file()
        and not ({".lake", "__pycache__"} & set(path.relative_to(formal).parts))
    }
    if actual != set(expected) | {"README.md", MANIFEST}:
        errors.append("reference source inventory differs")
    for relative, digest in expected.items():
        if not path_allowed(relative):
            errors.append(f"outside reference source boundary: {relative}")
            continue
        path = formal / relative
        if not path.is_file() or path.is_symlink():
            errors.append(f"missing or linked reference source: {relative}")
            continue
        data = path.read_bytes()
        if digest != {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}:
            errors.append(f"reference source bytes differ: {relative}")
    if (formal / "lean-toolchain").read_text(
        encoding="utf-8"
    ).strip() != LEAN_TOOLCHAIN or manifest.get("lean_toolchain") != LEAN_TOOLCHAIN:
        errors.append("current Lean 4.35 source pin differs")
    for relative, digest in PINS.items():
        if hashlib.sha256((formal / relative).read_bytes()).hexdigest() != digest:
            errors.append(f"frozen dependency/schema bytes differ: {relative}")
    config = tomllib.loads((formal / "lakefile.toml").read_text(encoding="utf-8"))
    if config["defaultTargets"] != [ENTRY] or {
        row["name"] for row in config["lean_lib"]
    } != {"ExactCIs", "CarfSpine"}:
        errors.append("Lake targets cross the focused checker boundary")
    modules = {
        path[:-5].replace("/", ".")
        for path in expected
        if path.endswith(".lean") and not path.startswith("tools/")
    }
    if sorted(modules) != manifest["lean_modules"] or len(modules) != 108:
        errors.append("checker module selection differs")
    reached = set()
    pending = [ENTRY]
    while pending:
        module = pending.pop()
        if module in reached:
            continue
        reached.add(module)
        path = formal.joinpath(*module.split(".")).with_suffix(".lean")
        if module not in modules or not path.is_file():
            errors.append(f"unselected checker import: {module}")
            continue
        code = lean_code(path.read_text(encoding="utf-8"))
        if re.search(r"\b(?:sorry|admit|axiom)\b", code):
            errors.append(f"project placeholder/axiom in checker source: {module}")
        for imported in lean_imports(path.read_text(encoding="utf-8")):
            if imported.startswith(("ExactCIs.", "CarfSpine.")):
                pending.append(imported)
            elif imported.split(".")[0] not in {
                "Mathlib",
                "Lean",
                "Std",
                "Init",
                "Batteries",
            }:
                errors.append(f"unreviewed external Lean import: {imported}")
    if reached != modules:
        errors.append("selected Lean files are not exactly the checker import closure")
    python = {path.stem for path in (formal / "tools").glob("*.py")}
    if python != RUNTIME or sorted(python) != manifest["python_modules"]:
        errors.append("reference Python module selection differs")
    for name in python & RUNTIME:
        for node in ast.walk(
            ast.parse((formal / "tools" / (name + ".py")).read_text(encoding="utf-8"))
        ):
            imports = (
                [alias.name for alias in node.names]
                if isinstance(node, ast.Import)
                else [node.module]
                if isinstance(node, ast.ImportFrom) and node.module
                else []
            )
            for imported in imports:
                if imported.split(".")[0] not in RUNTIME | sys.stdlib_module_names | {
                    "__future__"
                }:
                    errors.append(f"unreviewed reference Python dependency: {imported}")
    return errors


def main() -> int:
    errors = check(ROOT)
    for error in errors:
        print(f"ERROR: {error}")
    if not errors:
        print(
            "OK: checked-reference source custody; "
            "proof assurance is recorded separately"
        )
    return int(bool(errors))


if __name__ == "__main__":
    raise SystemExit(main())
