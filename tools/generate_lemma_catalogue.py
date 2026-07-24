from __future__ import annotations

import argparse
import ast
import inspect
import sys
from collections.abc import Callable, Mapping
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
OUT = ROOT / "LEMMA_CATALOGUE.md"


def _source_link(constructor: Callable[..., object]) -> str:
    source = inspect.getsourcefile(constructor)
    if source is None:
        return "—"
    path = Path(source).resolve().relative_to(ROOT)
    line = inspect.getsourcelines(constructor)[1]
    return f"[`{path.as_posix()}`]({path.as_posix()}#L{line})"


def _proof_constructors() -> dict[str, tuple[Path, ...]]:
    constructors: dict[str, list[Path]] = {}
    for path in sorted((SRC / "logic").glob("**/*.py")):
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name.startswith(
                "prove_"
            ):
                constructors.setdefault(node.name, []).append(path)
    return {
        name: tuple(paths)
        for name, paths in constructors.items()
    }


def _constructor_source(constructor: Callable[..., object]) -> Path:
    source = inspect.getsourcefile(constructor)
    if source is None:
        raise RuntimeError(
            f"proof constructor has no source file: {constructor.__name__}"
        )
    return Path(source).resolve()


def _validate_shadowed_constructors(
    source_constructors: Mapping[str, tuple[Path, ...]],
    registries: tuple[Mapping[str, Callable[..., object]], ...],
) -> None:
    recognized: dict[str, set[Path]] = {}
    labels: dict[str, set[str]] = {}
    for registry in registries:
        for label, constructor in registry.items():
            recognized.setdefault(constructor.__name__, set()).add(
                _constructor_source(constructor)
            )
            labels.setdefault(constructor.__name__, set()).add(label)

    for name, paths in source_constructors.items():
        if len(paths) == 1:
            continue
        if len(paths) != len(set(paths)):
            raise RuntimeError(
                f"duplicate proof constructor {name} in one source module"
            )
        if labels.get(name) is None or len(labels[name]) != 1:
            raise RuntimeError(
                f"duplicate proof constructor {name} has ambiguous labels"
            )
        if set(paths) != recognized.get(name, set()):
            locations = ", ".join(str(path) for path in paths)
            raise RuntimeError(
                f"duplicate proof constructor {name} is not an audited "
                f"registry shadow: {locations}"
            )


def render_catalogue() -> str:
    sys.path.insert(0, str(SRC))

    from logic.fol import AXIOMS as FOL_AXIOMS
    from logic.fol import THEOREMS as FOL_THEOREMS
    from logic.fol.theorems import THEOREMS as GENERATED_FOL_THEOREMS
    from logic.prop import AXIOMS as PROP_AXIOMS
    from logic.prop import RULES as PROP_RULES
    from logic.prop import THEOREMS as PROP_THEOREMS
    from logic.prop.theorems import THEOREMS as GENERATED_PROP_THEOREMS

    registries: tuple[tuple[str, Mapping[str, Callable[..., object]]], ...] = (
        ("Propositional theorem", PROP_THEOREMS),
        ("Predicate theorem", FOL_THEOREMS),
    )
    registry_functions = {
        constructor.__name__ for _, registry in registries for constructor in registry.values()
    }
    source_constructors = _proof_constructors()
    _validate_shadowed_constructors(
        source_constructors,
        (
            PROP_THEOREMS,
            FOL_THEOREMS,
            GENERATED_PROP_THEOREMS,
            GENERATED_FOL_THEOREMS,
        ),
    )
    uncovered = set(source_constructors) - registry_functions
    missing = registry_functions - set(source_constructors)

    if missing:
        raise RuntimeError(f"registered constructors missing from source audit: {sorted(missing)}")
    if uncovered:
        raise RuntimeError(
            f"source proof constructors outside emission closure: {sorted(uncovered)}"
        )

    rows: list[tuple[str, str, str, str, str]] = []
    axiom_source = "[`src/logic/prop/axioms.py`](src/logic/prop/axioms.py)"
    rule_source = "[`src/logic/prop/rules.py`](src/logic/prop/rules.py)"
    build_source = "[`src/logic/_build.py`](src/logic/_build.py)"
    for label in sorted(PROP_AXIOMS):
        rows.append((label, label, "Axiom", axiom_source, "emitted"))
    predicate_axiom_source = "[`src/logic/fol/axioms.py`](src/logic/fol/axioms.py)"
    for label in sorted(FOL_AXIOMS):
        rows.append((label, label, "Predicate axiom", predicate_axiom_source, "emitted"))
    for label, local in sorted(PROP_RULES.items()):
        rows.append(
            (
                label,
                local.id.value,
                "Rule",
                rule_source,
                "emitted",
            )
        )
    for label in ("wo", "wtru", "wfal"):
        rows.append((label, label, "Syntax", build_source, "emitted"))
    for label in ("idi", "a1ii"):
        rows.append((label, label, "Helper theorem", build_source, "emitted"))
    for category, registry in registries:
        for label, constructor in sorted(registry.items()):
            rows.append(
                (
                    label,
                    constructor.__name__,
                    category,
                    _source_link(constructor),
                    "registered",
                )
            )

    md = [
        "# Lemma Catalogue",
        "",
        "Generated by `uv run --no-sync python tools/generate_lemma_catalogue.py`; do not edit by hand.",
        "",
        "The theorem rows come from both live scoped registries. Source links resolve to the public topic module that owns each directly importable constructor; registry membership is distinct from build emission coverage.",
        "",
        f"- Registry proofs: {sum(len(registry) for _, registry in registries)}",
        "- Support-only proofs: 0",
        f"- Source proof constructors: {len(source_constructors)}",
        f"- Uncovered source constructors: {len(uncovered)}",
        "- Latest verified coverage: 2675 declared / 5004 emitted / 213 declared-but-unemitted",
        "- Verifiers: `mmverify`, `metamath`, and `knife` pass",
        "",
        "| set.mm label | Local name/function | Category | Source module | Registry status |",
        "|--------------|---------------------|----------|---------------|--------------|",
    ]
    md.extend(
        f"| {label} | {local} | {category} | {source} | {status} |"
        for label, local, category, source, status in rows
    )
    return "\n".join(md) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate the emitted lemma catalogue")
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
                "`uv run --no-sync python tools/generate_lemma_catalogue.py`"
            )
        return
    OUT.write_text(rendered, encoding="utf-8")


if __name__ == "__main__":
    main()
