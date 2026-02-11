from __future__ import annotations

from skfd.api_v2 import BuildContextV2
from skfd.authoring.emit import emit_axioms, emit_lowered_lemmas
from skfd.builder_v2 import MMBuilderV2
from skfd.core.symbols import SymbolId
from logic.propositional.hilbert import System
from logic.propositional.hilbert._structures import Imp, phi, psi
from logic.propositional.hilbert.lemmas import (
    Proof,
    prove_id,
)
from logic.propositional.hilbert.theorems import SETMM_TO_HILBERT_LEMMAS


def _emit_rule_skeleton(
    mm: MMBuilderV2, system: System, *, provable: SymbolId
) -> None:
    phi_wff = system.compile(phi, ctx="rule[mp.phi]")
    psi_wff = system.compile(psi, ctx="rule[mp.psi]")
    imp_wff = system.compile(Imp(phi, psi), ctx="rule[mp.imp]")

    with mm.block():
        mm.e(mm.sym.label("ax-mp.1"), tc=provable, expr=phi_wff.tokens)
        mm.e(mm.sym.label("ax-mp.2"), tc=provable, expr=imp_wff.tokens)
        mm.a(mm.sym.label("ax-mp"), tc=provable, expr=psi_wff.tokens)


def build(ctx: BuildContextV2) -> None:
    mm = ctx.mm
    prelude = ctx.deps["metamath-prelude"]

    system = System.make(interner=mm.interner, names=ctx.names)
    wff = prelude["wff"]
    provable = prelude["|-"]

    ax_1 = mm.sym.label("ax-1")
    ax_2 = mm.sym.label("ax-2")
    ax_3 = mm.sym.label("ax-3")
    ax_mp = mm.sym.label("ax-mp")

    emit_axioms(
        mm,
        system,
        typecode=provable,
        label_ids={"A1": ax_1, "A2": ax_2, "A3": ax_3},
    )
    _emit_rule_skeleton(mm, system, provable=provable)

    base_lemmas = [
        prove_id(system),
    ]

    compiled_axioms = system.compile_axioms()
    reserved = {"wi", "wn"}

    def _refs(p: Proof) -> set[str]:
        refs: set[str] = set()
        for st in getattr(p, "steps", ()):
            if getattr(st, "op", None) == "ref":
                r = getattr(st, "ref", None)
                if isinstance(r, str) and r:
                    refs.add(r)
        return refs

    queue: list[Proof] = list(base_lemmas)
    lemma_by_name: dict[str, Proof] = {}
    while queue:
        p = queue.pop()
        name = p.name
        if name in lemma_by_name:
            continue
        lemma_by_name[name] = p
        for ref in _refs(p):
            if ref in compiled_axioms or ref in reserved:
                continue
            if ref in lemma_by_name:
                continue
            ctor = SETMM_TO_HILBERT_LEMMAS.get(ref)
            if ctor is not None:
                queue.append(ctor(system))

    unresolved: set[str] = set()
    for p in lemma_by_name.values():
        for ref in _refs(p):
            if ref in compiled_axioms or ref in reserved or ref in lemma_by_name:
                continue
            unresolved.add(ref)
    if unresolved:
        raise ValueError(f"unresolved lemma references: {sorted(unresolved)}")

    lemmas = list(lemma_by_name.values())
    emit_lowered_lemmas(
        mm,
        system,
        lemmas,
        typecode=provable,
        wff_typecode=wff,
        label_ids={
            "wi": prelude["wi"],
            "wn": prelude["wn"],
            "mp": ax_mp,
            "A1": ax_1,
            "A2": ax_2,
            "A3": ax_3,
        },
        floating_by_var={
            prelude["ph"]: prelude["wph"],
            prelude["ps"]: prelude["wps"],
            prelude["ch"]: prelude["wch"],
        },
    )

    export_labels = [
        "ax-1",
        "ax-2",
        "ax-3",
        "ax-mp",
        *sorted(lemma_by_name.keys()),
    ]
    mm.export(*(mm.sym.label(n) for n in export_labels))
