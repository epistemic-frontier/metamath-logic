# src/logic/build.py
from skfd import mm, deps
from skfd.authoring.emit import emit_axioms, emit_lemmas
from skfd.builder import MMBuilder
from logic.propositional.hilbert import HilbertSystem
from logic.predicate.hilbert.system import PredicateSystem
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

# 1. Import Dependencies
prelude = deps.metamath_prelude

# Explicitly import symbols we need from prelude
# Note: ax-1 is not in prelude, so we don't import it.
mm.import_symbols(
    wff=prelude["wff"],
    ph=prelude["ph"],
    wph=prelude["wph"],
)

# 2. Logic Construction
def _emit_rule_skeleton(mm: MMBuilder, system: HilbertSystem) -> None:
    # This function manually constructs syntax rules.
    # ideally we should reuse prelude's syntax, but for now we preserve existing behavior
    # to avoid breaking the logic system's internal assumptions.
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

# --- Predicate logic: emit AX5/AX6 via predicate system (unary forall scaffolding) ---
pred = PredicateSystem.make(interner=mm._interner)
emit_axioms(mm, pred)

# 3. Export API
mm.export("wi", "wn", "wa", "mp")

for label in system.axioms:
    mm.export(label)

for lemma in lemmas:
    mm.export(lemma.name)
    
for label in pred.axioms:
    mm.export(label)
