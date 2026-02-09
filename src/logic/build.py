from __future__ import annotations

from skfd.api_v2 import BuildContextV2
from skfd.authoring.emit import emit_axioms, emit_lemmas
from skfd.builder_v2 import MMBuilderV2
from logic.propositional.hilbert import HilbertSystem
from logic.propositional.hilbert._structures import And, Imp, Not, phi, psi
from logic.propositional.hilbert.lemmas import (
    prove_L1_id,
    prove_L2_or_intro_right,
    prove_L4_demorgan,
    prove_L5_contrapositive,
    prove_L6_double_neg_intro,
    prove_L7_double_neg_elim,
    prove_L8_excluded_middle,
    prove_L9_peirce,
)


def manifest() -> dict[str, list[str]]:
    return {"deps": ["metamath-prelude"]}


def _emit_rule_skeleton(mm: MMBuilderV2, system: HilbertSystem, *, wff: int) -> None:
    wi_wff = system.compile(Imp(phi, psi), ctx="rule[wi]")
    wn_wff = system.compile(Not(phi), ctx="rule[wn]")
    wa_wff = system.compile(And(phi, psi), ctx="rule[wa]")
    phi_wff = system.compile(phi, ctx="rule[mp.phi]")
    psi_wff = system.compile(psi, ctx="rule[mp.psi]")
    imp_wff = system.compile(Imp(phi, psi), ctx="rule[mp.imp]")

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

    system = HilbertSystem.make(interner=mm.interner)
    wff = prelude["wff"]

    emit_axioms(mm, system, typecode=wff)
    _emit_rule_skeleton(mm, system, wff=wff)

    lemmas = [
        prove_L1_id(system),
        prove_L2_or_intro_right(system),
        prove_L4_demorgan(system),
        prove_L5_contrapositive(system),
        prove_L6_double_neg_intro(system),
        prove_L7_double_neg_elim(system),
        prove_L8_excluded_middle(system),
        prove_L9_peirce(system),
    ]
    emit_lemmas(mm, system, lemmas, typecode=wff)

    export_labels = [
        "A1",
        "A2",
        "A3",
        "wi",
        "wn",
        "wa",
        "mp",
        *[l.name for l in lemmas],
    ]
    mm.export(*(mm.sym.label(n) for n in export_labels))
