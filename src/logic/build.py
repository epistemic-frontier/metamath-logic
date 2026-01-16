from typing import Any

from skfd.authoring.emit import emit_axioms, emit_lemmas
from skfd.builder import MMBuilder
from logic.propositional.hilbert import HilbertSystem
from logic.propositional.hilbert._structures import And, Not, Imp, phi, psi
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


def manifest() -> dict[str, Any]:
    return {"deps": ["prelude"]}


def _emit_rule_skeleton(mm: MMBuilder, system: HilbertSystem) -> None:
    axioms = system.compile_axioms()
    symtab = system.interner.symbol_table()

    wi_wff = system.compile(Imp(phi, psi), ctx="rule[wi]")
    wn_wff = system.compile(Not(phi), ctx="rule[wn]")
    wa_wff = system.compile(And(phi, psi), ctx="rule[wa]")
    phi_wff = system.compile(phi, ctx="rule[mp.phi]")
    psi_wff = system.compile(psi, ctx="rule[mp.psi]")
    imp_wff = system.compile(Imp(phi, psi), ctx="rule[mp.imp]")

    const_ids: set[int] = set()
    var_ids: set[int] = set()

    all_wffs = list(axioms.values()) + [
        wi_wff,
        wn_wff,
        wa_wff,
        phi_wff,
        psi_wff,
        imp_wff,
    ]

    for wff in all_wffs:
        for sid in wff.tokens:
            s = symtab[sid]
            if s.kind == "Const":
                const_ids.add(s.id)
            elif s.kind == "Var":
                var_ids.add(s.id)

    token_map: dict[int, str] = {}

    const_names: list[str] = []
    for sid in sorted(const_ids):
        name = f"c{sid}"
        token_map[sid] = name
        const_names.append(name)

    for sid in sorted(var_ids):
        token_map[sid] = f"v{sid}"

    extra_consts = [name for name in const_names if name not in mm._constants]
    if extra_consts:
        mm.c(*extra_consts)

    for label, wff in {
        "wi": wi_wff,
        "wn": wn_wff,
        "wa": wa_wff,
    }.items():
        tokens = [token_map[sid] for sid in wff.tokens]
        expr = " ".join(tokens)
        mm.a(label, "wff", expr)

    def _render(wff) -> str:
        return " ".join(token_map[sid] for sid in wff.tokens)

    phi_expr = _render(phi_wff)
    imp_expr = _render(imp_wff)
    psi_expr = _render(psi_wff)

    with mm.block():
        mm.e("mp.1", "wff", phi_expr)
        mm.e("mp.2", "wff", imp_expr)
        mm.a("mp", "wff", psi_expr)


def build(mm: MMBuilder, **deps: Any) -> Any:
    prelude = deps.get("prelude")
    if not prelude:
        raise RuntimeError("Dependency 'prelude' not found or failed to load")

    mm.import_symbols(
        wff=prelude["wff"],
        ph=prelude["ph"],
        wph=prelude["wph"],
        ax_1=prelude["ax-1"],
    )

    system = HilbertSystem.make(interner=mm._interner)
    emit_axioms(mm, system)
    _emit_rule_skeleton(mm, system)

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
    emit_lemmas(mm, system, lemmas)

    return {}
