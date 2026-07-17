from __future__ import annotations

import importlib
import os
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))


def test_import_logic() -> None:
    m = importlib.import_module("logic")
    assert m.__name__ == "logic"


def test_scoped_public_registries() -> None:
    import logic.fol as fol
    import logic.prop as prop

    assert set(prop.__all__) == {
        "AXIOMS",
        "CALCULUS",
        "LANGUAGE",
        "RULES",
        "THEOREMS",
        "System",
        "make",
    }
    assert set(fol.__all__) == {
        "AXIOMS",
        "CALCULUS",
        "LANGUAGE",
        "RULES",
        "THEOREMS",
        "System",
        "make",
    }
    assert "ax-1" in prop.AXIOMS
    assert "ax-4" in fol.AXIOMS
    assert set(prop.RULES) == {"ax-mp"}
    assert set(fol.RULES) == {"ax-mp", "ax-gen"}
    assert fol.RULES["ax-mp"] is prop.RULES["ax-mp"]
    assert prop.RULES["ax-mp"] is prop.CALCULUS.rule(prop.RULES["ax-mp"].id)
    assert prop.THEOREMS and fol.THEOREMS


def test_fol_semantic_binder_and_generalization_canary() -> None:
    from skfd.authoring.ids import OwnerId
    from skfd.authoring.metamath_language import LiteralAtom, VariableAtom
    from skfd.authoring.term import App, VariableRef
    from skfd.authoring.term_ops import free_variables

    from logic._dv_contracts import ACTIVE_DV_PAIRS
    from logic.fol.axioms import AX5_SEMANTIC
    from logic.fol.calculus import CALCULUS, GENERALIZATION
    from logic.fol.language import LANGUAGE, SETVAR_VARIABLE, All, SetVar
    from logic.fol.metamath_binding import SETMM_FOL_BINDING, SETMM_FORALL_TOKEN
    from logic.fol.notation import FOL_UNICODE_NOTATION
    from logic.prop.calculus import PROVABLE
    from logic.prop.language import WFF_VARIABLE

    owner = OwnerId("test#fol-canary")
    x_ref = VariableRef("schema", owner, "x", SETVAR_VARIABLE)
    phi_ref = VariableRef("schema", owner, "phi", WFF_VARIABLE)
    x = SetVar(x_ref)
    phi = LANGUAGE.variable(phi_ref)
    quantified = All(x, phi)

    assert free_variables(quantified, LANGUAGE) == frozenset((phi_ref,))
    assert FOL_UNICODE_NOTATION.parse(
        "forall x phi",
        {"x": x_ref, "phi": phi_ref},
    ) == quantified
    assert FOL_UNICODE_NOTATION.render(quantified, {x_ref: "x", phi_ref: "φ"}) == "∀ x φ"
    assert SETMM_FOL_BINDING.lower(quantified) == (
        LiteralAtom(SETMM_FORALL_TOKEN),
        VariableAtom(x_ref),
        VariableAtom(phi_ref),
    )

    generalization = CALCULUS.rule(GENERALIZATION)
    assert len(generalization.premises) == 1
    assert generalization.premises[0].kind == PROVABLE
    assert generalization.conclusion == CALCULUS.judgment(PROVABLE, (generalization.conclusion.arguments[0],))
    assert isinstance(generalization.conclusion.arguments[0], App)
    assert generalization.conclusion.arguments[0].constructor == quantified.constructor

    ax5 = AX5_SEMANTIC.declaration
    assert ax5.conclusion.kind == PROVABLE
    assert len(ax5.mandatory_distinct) == 1
    distinct = ax5.mandatory_distinct[0]
    assert {distinct.left.local_key, distinct.right.local_key} == {"phi", "x"}
    assert {distinct.left.kind, distinct.right.kind} == {WFF_VARIABLE, SETVAR_VARIABLE}
    assert ACTIVE_DV_PAIRS["ax-5"] == (("ph", "x"),)


def test_prop_semantic_canary_is_independent_of_legacy_registries() -> None:
    from prelude.metamath_binding import SETMM_LPAREN_TOKEN, SETMM_RPAREN_TOKEN
    from skfd.authoring.formula import Wff
    from skfd.authoring.ids import OwnerId
    from skfd.authoring.metamath_language import LiteralAtom
    from skfd.authoring.term import VariableRef
    from skfd.core.symbols import SymbolInterner

    from logic.prop._builtins import PropositionalBuiltins, w3a, wa
    from logic.prop.calculus import CALCULUS, MODUS_PONENS, PROVABLE
    from logic.prop.language import AND2, AND3, IMP, LANGUAGE, WFF_VARIABLE, And2, And3
    from logic.prop.metamath_binding import SETMM_PROP_BINDING
    from logic.prop.notation import PROP_UNICODE_NOTATION

    refs = {
        name: VariableRef("schema", OwnerId("test"), name, WFF_VARIABLE)
        for name in ("phi", "psi", "chi")
    }
    phi, psi, chi = (LANGUAGE.variable(refs[name]) for name in refs)
    binary = And2(phi, psi)
    ternary = And3(phi, psi, chi)

    assert binary.constructor == AND2
    assert ternary.constructor == AND3
    assert binary != ternary
    assert PROP_UNICODE_NOTATION.parse("phi /\\ psi", refs) == binary
    assert PROP_UNICODE_NOTATION.parse("and3(phi, psi, chi)", refs) == ternary
    assert CALCULUS.judgment(PROVABLE, (binary,)).arguments == (binary,)
    mp = CALCULUS.rule(MODUS_PONENS)
    assert tuple(judgment.kind for judgment in mp.premises) == (PROVABLE, PROVABLE)
    assert mp.premises[1].arguments[0].constructor == IMP
    assert mp.conclusion.kind == PROVABLE

    binary_atoms = SETMM_PROP_BINDING.lower(binary)
    ternary_atoms = SETMM_PROP_BINDING.lower(ternary)
    assert [atom.token.local_name for atom in binary_atoms if isinstance(atom, LiteralAtom)] == [
        "(",
        "/\\",
        ")",
    ]
    assert [atom.token.local_name for atom in ternary_atoms if isinstance(atom, LiteralAtom)] == [
        "(",
        "/\\",
        "/\\",
        ")",
    ]
    assert SETMM_PROP_BINDING.formations[AND2].syntax_assertion != (
        SETMM_PROP_BINDING.formations[AND3].syntax_assertion
    )
    assert binary_atoms[0] == LiteralAtom(SETMM_LPAREN_TOKEN)
    assert binary_atoms[-1] == LiteralAtom(SETMM_RPAREN_TOKEN)

    interner = SymbolInterner()
    builtins = PropositionalBuiltins.ensure(interner)
    legacy_variables = tuple(
        Wff(
            "wff",
            (
                interner.intern(
                    origin_module_id="test",
                    local_name=name,
                    kind="Var",
                    origin_ref=None,
                ),
            ),
        )
        for name in refs
    )
    symbols = interner.symbol_table()
    assert [symbols[token].local_name for token in wa(builtins, *legacy_variables[:2]).tokens] == [
        atom.token.local_name if isinstance(atom, LiteralAtom) else atom.variable.local_key
        for atom in binary_atoms
    ]
    assert [symbols[token].local_name for token in w3a(builtins, *legacy_variables).tokens] == [
        atom.token.local_name if isinstance(atom, LiteralAtom) else atom.variable.local_key
        for atom in ternary_atoms
    ]


def test_semantic_language_digests_do_not_depend_on_import_order_or_hash_seed() -> None:
    scripts = (
        "import prelude.language as p; import logic.prop.language as l; "
        "print(p.LANGUAGE.semantic_digest, l.LANGUAGE.semantic_digest)",
        "import logic.prop.language as l; import prelude.language as p; "
        "print(p.LANGUAGE.semantic_digest, l.LANGUAGE.semantic_digest)",
    )
    outputs: list[str] = []
    for seed, script in enumerate(scripts):
        env = dict(os.environ)
        env["PYTHONHASHSEED"] = str(seed)
        outputs.append(
            subprocess.check_output(
                [sys.executable, "-c", script],
                text=True,
                env=env,
            ).strip()
        )
    assert outputs[0] == outputs[1]


def test_legacy_binary_and_ternary_conjunction_use_exact_constructor_builders() -> None:
    from skfd.core.symbols import SymbolInterner

    from logic.prop import make
    from logic.prop._structures import And, And3, chi, phi, psi

    interner = SymbolInterner()
    system = make(interner=interner)
    binary = system.compile(And(phi, psi))
    ternary = system.compile(And3(phi, psi, chi))
    symbols = interner.symbol_table()

    assert [symbols[token].local_name for token in binary.tokens] == ["(", "ph", "/\\", "ps", ")"]
    assert [symbols[token].local_name for token in ternary.tokens] == [
        "(",
        "ph",
        "/\\",
        "ps",
        "/\\",
        "ch",
        ")",
    ]


def test_prop_reexports_prelude_implication_and_negation_constructors() -> None:
    from prelude.structures import Imp as PreludeImp
    from prelude.structures import Not as PreludeNot

    from logic.prop._structures import Imp, Not

    assert Imp is PreludeImp
    assert Not is PreludeNot


def test_proof_constructors_remain_directly_importable() -> None:
    import logic.fol.foundation as foundation
    import logic.prop.alternative_axiomatizations as alternative_axiomatizations
    import logic.prop.core as core
    from logic.fol.foundation import prove_alcomw
    from logic.prop.alternative_axiomatizations import prove_meredith
    from logic.prop.conjunction import prove_mpan
    from logic.prop.core import prove_id
    from logic.prop.ternary import prove_syl3anc

    assert prove_id is core.prove_id
    assert prove_alcomw is foundation.prove_alcomw
    assert prove_meredith is alternative_axiomatizations.prove_meredith
    assert prove_mpan.__module__ == "logic.prop.conjunction"
    assert prove_syl3anc.__module__ == "logic.prop.ternary"
    assert "prove_id" in core.__all__
    assert "prove_alcomw" in foundation.__all__
    assert "_THEOREMS" not in core.__all__
    assert "_THEOREMS" not in foundation.__all__
