from __future__ import annotations

import re
import sys
from pathlib import Path
from typing import cast

ROOT = Path(__file__).resolve().parents[2]

setmm_path = ROOT / "set.mm" / "set.mm"
out_path = ROOT / "metamath-logic" / "LEMMA_CATALOGUE.md"

lines: list[str] = []
if setmm_path.exists():
    with setmm_path.open("r", encoding="utf-8", errors="ignore") as f:
        lines = f.readlines()


def find_label_line(label: str) -> int | None:
    pat = re.compile(rf"^\s*{re.escape(label)}\s+\$(?:a|p|f|e)\b")
    for i, ln in enumerate(lines, start=1):
        if pat.search(ln):
            return i
    return None


def setmm_link(label: str) -> str:
    ln = find_label_line(label)
    return f"file://{setmm_path}#L{ln}" if ln else f"file://{setmm_path}"


def refs(proof: object) -> set[str]:
    result: set[str] = set()
    for step in getattr(proof, "steps", ()):
        if getattr(step, "op", None) != "ref":
            continue
        ref = getattr(step, "ref", None)
        if isinstance(ref, str) and ref:
            result.add(ref)
    return result


def main() -> None:
    sys.path.insert(0, str(ROOT / "metamath-logic" / "src"))
    sys.path.insert(0, str(ROOT / "metamath-prelude" / "src"))
    sys.path.insert(0, str(ROOT / "proof-scaffold" / "src"))

    from prelude.formula import GLOBAL_PRELUDE_MODULE_ID, Builtins
    from skfd.core.symbols import SymbolId, SymbolInterner
    from skfd.names import NameResolver

    from logic.propositional.hilbert import (
        SETMM_TO_HILBERT_AXIOMS,
        SETMM_TO_HILBERT_RULES,
        System,
    )
    from logic.propositional.hilbert.theorems import SETMM_TO_HILBERT_LEMMAS

    interner = SymbolInterner()
    names = NameResolver()
    system = System.make(interner=interner, names=names)
    builtins = Builtins.ensure(interner)

    def foundation_var(name: str) -> SymbolId:
        return cast(
            SymbolId,
            interner.intern(
                origin_module_id=GLOBAL_PRELUDE_MODULE_ID,
                local_name=name,
                kind="Var",
                origin_ref=0,
            ),
        )

    # Keep this in sync with logic.build: this is the current lowered-proof
    # subset, not the long-term authoring registry.
    supported_tokens = {
        builtins.neg,
        builtins.imp,
        builtins.tru,
        builtins.fal,
        builtins.lp,
        builtins.rp,
    }
    floating_vars = {
        foundation_var("ph"),
        foundation_var("ps"),
        foundation_var("ch"),
        foundation_var("th"),
        foundation_var("ta"),
    }
    compiled_axioms = system.compile_axioms()
    reserved = {"wi", "wn", "wtru", "wfal"}

    def emittable(proof: object) -> bool:
        for step in getattr(proof, "steps", ()):
            wff = getattr(step, "wff", None)
            if wff is None:
                continue
            for token in wff.tokens:
                if token in supported_tokens or token in floating_vars:
                    continue
                return False
        return True

    constructed: dict[str, object] = {}
    excluded: dict[str, str] = {}
    for name, ctor in SETMM_TO_HILBERT_LEMMAS.items():
        try:
            proof = ctor(system)
        except Exception as exc:  # noqa: BLE001
            excluded[name] = f"construction failed: {exc}"
            continue
        if not emittable(proof):
            excluded[name] = "uses a connective outside the current lowering subset"
            continue
        constructed[name] = proof

    changed = True
    while changed:
        changed = False
        for name in list(constructed):
            for ref in refs(constructed[name]):
                if ref in SETMM_TO_HILBERT_LEMMAS and ref not in constructed:
                    excluded[name] = f"depends on non-emitted theorem {ref!r}"
                    del constructed[name]
                    changed = True
                    break

    for name in list(constructed):
        missing = sorted(
            ref
            for ref in refs(constructed[name])
            if ref not in compiled_axioms
            and ref not in reserved
            and ref not in constructed
            and ref not in SETMM_TO_HILBERT_AXIOMS
            and ref not in SETMM_TO_HILBERT_RULES
        )
        if missing:
            excluded[name] = f"has unresolved references: {', '.join(missing)}"
            del constructed[name]

    rows: list[tuple[str, str, str, str, str]] = []
    for label, local in sorted(SETMM_TO_HILBERT_AXIOMS.items()):
        rows.append((label, local, "Axiom", setmm_link(label), "exported"))
    for label, local in sorted(SETMM_TO_HILBERT_RULES.items()):
        rows.append((label, local, "Rule", setmm_link(label), "exported"))
    for label in ("wo", "wtru", "wfal"):
        rows.append((label, label, "Syntax", setmm_link(label), "exported"))
    for label in ("idi", "a1ii"):
        rows.append((label, label, "Helper theorem", setmm_link(label), "exported"))
    for label, ctor in sorted(SETMM_TO_HILBERT_LEMMAS.items()):
        status = (
            "lowered/exported" if label in constructed else f"registered only: {excluded[label]}"
        )
        rows.append(
            (
                label,
                getattr(ctor, "__name__", str(ctor)),
                "Lemma",
                setmm_link(label),
                status,
            )
        )

    md: list[str] = []
    md.append("# Lemma Catalogue")
    md.append("")
    md.append("Generated by `uv run python tools/generate_lemma_catalogue.py`.")
    md.append("")
    md.append(
        "This catalogue is derived from the Hilbert axiom/rule mappings, "
        "`SETMM_TO_HILBERT_LEMMAS`, and the current `logic.build` lowering subset."
    )
    md.append("")
    md.append(f"- Registry lemmas: {len(SETMM_TO_HILBERT_LEMMAS)}")
    md.append(f"- Lowered/exported registry lemmas: {len(constructed)}")
    md.append(f"- Registered-only lemmas: {len(excluded)}")
    md.append("")
    md.append("| set.mm label | Local name/function | Category | set.mm link | Build status |")
    md.append("|--------------|---------------------|----------|-------------|--------------|")
    for label, local, category, link, status in rows:
        md.append(f"| {label} | {local} | {category} | {link} | {status} |")
    content = "\n".join(md) + "\n"
    out_path.write_text(content, encoding="utf-8")


if __name__ == "__main__":
    main()
