from __future__ import annotations

from skfd.api_v2 import BuildContextV2
from skfd.authoring.emit import emit_axioms, emit_lowered_lemmas
from skfd.builder_v2 import MMBuilderV2
from skfd.core.symbols import SymbolId
from logic.propositional.hilbert import HilbertSystem
from logic.propositional.hilbert._structures import And, Imp, Not, phi, psi
from logic.propositional.hilbert.lemmas import (
    LemmaProof,
    prove_L1_id,
    prove_L2_or_intro_right,
    prove_L3_or_intro_left,
    prove_L4_demorgan,
    prove_L5_contrapositive,
    prove_L6_double_neg_intro,
    prove_L7_double_neg_elim,
    prove_L8_excluded_middle,
    prove_L9_peirce,
)
from logic.propositional.hilbert.theorems import SETMM_TO_HILBERT_LEMMAS


def _emit_rule_skeleton(
    mm: MMBuilderV2, system: HilbertSystem, *, wff: SymbolId
) -> None:
    wi_wff = system._compile(Imp(phi, psi), ctx="rule[wi]")
    wn_wff = system._compile(Not(phi), ctx="rule[wn]")
    wa_wff = system._compile(And(phi, psi), ctx="rule[wa]")
    phi_wff = system._compile(phi, ctx="rule[mp.phi]")
    psi_wff = system._compile(psi, ctx="rule[mp.psi]")
    imp_wff = system._compile(Imp(phi, psi), ctx="rule[mp.imp]")

    mm.a(mm.sym.label("wi"), tc=wff, expr=wi_wff.tokens)
    mm.a(mm.sym.label("wn"), tc=wff, expr=wn_wff.tokens)
    mm.a(mm.sym.label("wa"), tc=wff, expr=wa_wff.tokens)

    with mm.block():
        mm.e(mm.sym.label("mp.1"), tc=wff, expr=phi_wff.tokens)
        mm.e(mm.sym.label("mp.2"), tc=wff, expr=imp_wff.tokens)
        mm.a(mm.sym.label("mp"), tc=wff, expr=psi_wff.tokens)


def build(ctx: BuildContextV2) -> None:
    mm = ctx.mm
    prelude = ctx.deps.prelude

    system = HilbertSystem.make(interner=mm.interner, names=ctx.names)
    wff = prelude["wff"]

    emit_axioms(mm, system, typecode=wff)
    _emit_rule_skeleton(mm, system, wff=wff)

    base_lemmas = [
        prove_L1_id(system),
        prove_L2_or_intro_right(system),
    ]

    compiled_axioms = system.compile_axioms()
    reserved = {"wi", "wn", "wa", "mp"}

    def _refs(p: LemmaProof) -> set[str]:
        refs: set[str] = set()
        for st in getattr(p, "steps", ()):
            if getattr(st, "op", None) == "ref":
                r = getattr(st, "ref", None)
                if isinstance(r, str) and r:
                    refs.add(r)
        return refs

    queue: list[LemmaProof] = list(base_lemmas)
    lemma_by_name: dict[str, LemmaProof] = {}
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
    emit_lowered_lemmas(mm, system, lemmas, typecode=wff)

    export_labels = [
        "A1",
        "A2",
        "A3",
        "wi",
        "wn",
        "wa",
        "mp",
        *sorted(lemma_by_name.keys()),
    ]
    mm.export(*(mm.sym.label(n) for n in export_labels))
