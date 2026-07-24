from __future__ import annotations

import argparse
import ast
import json
from pathlib import Path
from typing import Any, cast

ROOT = Path(__file__).resolve().parents[1]
AUTHORITY = ROOT / "tests" / "public-source-test-authority-v2.json"
OUT = ROOT / "LEMMA_CATALOGUE.md"


def _document(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise TypeError(f"{path} must contain a JSON object")
    return cast(dict[str, Any], value)


def _proof_rows(
    item: dict[str, Any],
) -> list[tuple[str, str, str, int]]:
    path = ROOT / cast(str, item["path"])
    tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    functions = {
        node.name: node
        for node in tree.body
        if isinstance(node, ast.FunctionDef) and node.name.startswith("prove_")
    }
    expected = cast(list[str], item["proof_functions"])
    if list(functions) != expected:
        raise RuntimeError(f"{path} differs from the V2 test authority")

    lazy_import_counts: dict[str, int] = {name: 0 for name in expected}
    for dependency in cast(list[dict[str, str]], item["external_dependency_imports"]):
        lazy_import_counts[dependency["proof_function"]] += 1

    rows: list[tuple[str, str, str, int]] = []
    for name in expected:
        function = functions[name]
        handles: list[str] = []
        for decorator in function.decorator_list:
            target = decorator.func if isinstance(decorator, ast.Call) else decorator
            if isinstance(target, ast.Attribute) and target.attr == "proof":
                handles.append(ast.unparse(target.value))
        if len(handles) != 1:
            raise RuntimeError(f"{path}:{function.lineno} must have one proof handle")
        rows.append(
            (
                handles[0],
                name,
                f"[`{path.relative_to(ROOT)}`]({path.relative_to(ROOT)}#L{function.lineno})",
                lazy_import_counts[name],
            )
        )
    return rows


def render_catalogue() -> str:
    authority = _document(AUTHORITY)
    if authority.get("schema") != "setmm-stage4-public-package-test-authority-v2":
        raise RuntimeError("unsupported public-source test authority")
    modules = cast(list[dict[str, Any]], authority["modules"])
    module_rows: list[tuple[str, str, int, int]] = []
    proof_sections: list[tuple[str, list[tuple[str, str, str, int]]]] = []

    for item in modules:
        rows = _proof_rows(item)
        module = cast(str, item["module"])
        path = cast(str, item["path"])
        dependency_count = len(
            cast(list[dict[str, str]], item["external_dependency_imports"])
        )
        module_rows.append((module, path, len(rows), dependency_count))
        proof_sections.append((module, rows))

    proof_count = sum(row[2] for row in module_rows)
    lazy_import_count = sum(row[3] for row in module_rows)
    lines = [
        "# Logic proof catalogue",
        "",
        "Generated from `tests/public-source-test-authority-v2.json` by "
        "`uv run --frozen python tools/generate_lemma_catalogue.py`; do not edit by hand.",
        "",
        "The public package is organized by ontology-owned modules. Each proof is a top-level "
        "function decorated by its proof handle; external proof dependencies are imported inside "
        "the function body and therefore elaborate lazily.",
        "",
        f"- Semantic modules: {len(module_rows)}",
        f"- Top-level proof functions: {proof_count}",
        f"- Function-local external dependency imports: {lazy_import_count}",
        "- Legacy `catalog_v1` modules: 0",
        "",
        "## Module inventory",
        "",
        "| Semantic module | Source | Proof functions | Lazy imports |",
        "|---|---|---:|---:|",
    ]
    lines.extend(
        f"| `{module}` | [`{path}`]({path}) | {proofs} | {imports} |"
        for module, path, proofs, imports in module_rows
    )
    for module, rows in proof_sections:
        lines.extend(
            [
                "",
                f"## `{module}`",
                "",
                "| Proof handle | Function | Source | Lazy imports |",
                "|---|---|---|---:|",
            ]
        )
        lines.extend(
            f"| `{handle}` | `{function}` | {source} | {imports} |"
            for handle, function, source, imports in rows
        )
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Generate the ontology-owned public proof catalogue"
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail instead of writing when LEMMA_CATALOGUE.md is stale",
    )
    args = parser.parse_args()

    rendered = render_catalogue()
    if args.check:
        current = OUT.read_text(encoding="utf-8") if OUT.exists() else ""
        if current != rendered:
            raise SystemExit(
                "LEMMA_CATALOGUE.md is stale; run "
                "`uv run --frozen python tools/generate_lemma_catalogue.py`"
            )
        return
    OUT.write_text(rendered, encoding="utf-8")


if __name__ == "__main__":
    main()
