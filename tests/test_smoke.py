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
    from logic.fol.axioms import AX5_SEMANTIC, AX5_SIGNATURE, AX5_SOURCE_SNAPSHOT
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
    assert AX5_SOURCE_SNAPSHOT.declaration == AX5_SIGNATURE
    assert AX5_SOURCE_SNAPSHOT.declaration.mandatory_distinct == ax5.mandatory_distinct
    assert AX5_SOURCE_SNAPSHOT.active_distinct == ax5.mandatory_distinct
    assert ACTIVE_DV_PAIRS["ax-5"] == (("ph", "x"),)


def test_semantic_assertion_application_canaries() -> None:
    from prelude.metamath_binding import (
        SETMM_IMP_TOKEN,
        SETMM_LPAREN_TOKEN,
        SETMM_RPAREN_TOKEN,
    )
    from skfd.authoring.assertion import (
        AssertionSignature,
        apply_assertion,
        finalize_proof,
        start_draft,
    )
    from skfd.authoring.catalog import apply_assertion_by_id
    from skfd.authoring.ids import AssertionSemanticId, OwnerId, ProofId
    from skfd.authoring.judgment import DistinctPair, Judgment
    from skfd.authoring.legacy_replay import LegacyReplayBinding, lower_semantic_replay_plan
    from skfd.authoring.replay import build_semantic_replay_plan
    from skfd.authoring.term import VariableRef
    from skfd.core.disjoint import normalize_dv_pairs
    from skfd.core.symbols import SymbolInterner
    from skfd.proof import Proof, Step

    from logic.fol._system import System as FolSystem
    from logic.fol.axioms import AX5, AX5_SIGNATURE
    from logic.fol.calculus import CALCULUS
    from logic.fol.language import LANGUAGE, SETVAR, SETVAR_VARIABLE, All, SetVar
    from logic.fol.metamath_binding import (
        SETMM_AX5_REPLAY_BINDING,
        SETMM_FOL_BINDING,
        SETMM_FORALL_TOKEN,
    )
    from logic.fol.rules import (
        ASSERTION_CATALOG as FOL_ASSERTION_CATALOG,
    )
    from logic.fol.rules import FOL_CORE_PROFILE
    from logic.prop._system import make as make_prop_system
    from logic.prop.calculus import PROVABLE
    from logic.prop.core import prove_mp2b
    from logic.prop.language import WFF, WFF_VARIABLE, Imp
    from logic.prop.metamath_binding import SETMM_MP_REPLAY_BINDING, SETMM_PROP_BINDING
    from logic.prop.rules import ASSERTION_CATALOG, MP_ASSERTION, PROP_CORE_PROFILE

    owner = OwnerId("test#assertion-application")
    p_ref = VariableRef("local", owner, "p", WFF_VARIABLE)
    q_ref = VariableRef("local", owner, "q", WFF_VARIABLE)
    x_ref = VariableRef("local", owner, "x", SETVAR_VARIABLE)
    p, q = LANGUAGE.variable(p_ref), LANGUAGE.variable(q_ref)
    x = SetVar(x_ref)

    mp_draft = start_draft(
        ProofId("test#proof:mp-canary"),
        CALCULUS,
        (
            Judgment(PROVABLE, (p,)),
            Judgment(PROVABLE, (Imp(p, q),)),
        ),
    )
    mp = apply_assertion(
        mp_draft,
        CALCULUS,
        MP_ASSERTION,
        tuple(step.id for step in mp_draft.hypotheses),
    )
    assert mp.step.result == Judgment(PROVABLE, (q,))

    theorem_owner = OwnerId("metamath-logic/prop#assertion:mp2b")
    phi_ref = VariableRef("schema", theorem_owner, "phi", WFF_VARIABLE)
    psi_ref = VariableRef("schema", theorem_owner, "psi", WFF_VARIABLE)
    chi_ref = VariableRef("schema", theorem_owner, "chi", WFF_VARIABLE)
    phi = LANGUAGE.variable(phi_ref)
    psi = LANGUAGE.variable(psi_ref)
    chi = LANGUAGE.variable(chi_ref)
    mp2b_signature = AssertionSignature(
        id=AssertionSemanticId("metamath-logic/prop#assertion:mp2b"),
        canonical_label="mp2b",
        kind="theorem",
        schema_variables=(phi_ref, psi_ref, chi_ref),
        premises=(
            Judgment(PROVABLE, (phi,)),
            Judgment(PROVABLE, (Imp(phi, psi),)),
            Judgment(PROVABLE, (Imp(psi, chi),)),
        ),
        conclusion=Judgment(PROVABLE, (chi,)),
    )
    mp2b_draft = start_draft(
        ProofId("test#proof:mp2b-semantic"),
        CALCULUS,
        mp2b_signature.premises,
        signature=mp2b_signature,
    )
    first = apply_assertion_by_id(
        mp2b_draft,
        CALCULUS,
        ASSERTION_CATALOG,
        PROP_CORE_PROFILE,
        MP_ASSERTION.id,
        (mp2b_draft.hypotheses[0].id, mp2b_draft.hypotheses[1].id),
    )
    second = apply_assertion_by_id(
        first.draft,
        CALCULUS,
        ASSERTION_CATALOG,
        PROP_CORE_PROFILE,
        MP_ASSERTION.id,
        (first.step.id, mp2b_draft.hypotheses[2].id),
    )
    mp2b = finalize_proof(second.draft, CALCULUS, root=second.step.id)
    replay = build_semantic_replay_plan(
        mp2b,
        CALCULUS,
        ASSERTION_CATALOG,
        PROP_CORE_PROFILE,
    )
    assert tuple(step.canonical_label for step in replay.applications) == (
        "ax-mp",
        "ax-mp",
    )
    assert tuple(step.premise_positions for step in replay.applications) == (
        (0, 1),
        (3, 2),
    )
    assert tuple(step.result for step in replay.applications) == (
        Judgment(PROVABLE, (psi,)),
        Judgment(PROVABLE, (chi,)),
    )
    assert replay.root_position == 4
    assert tuple(item.assertion for item in replay.dependency_closure) == (
        MP_ASSERTION.id,
    )
    assert replay.replay_context.active_distinct == ()

    interner = SymbolInterner()
    prop_system = make_prop_system(interner=interner)
    expected_mp2b = prove_mp2b(prop_system)

    def variable_symbol(local_name: str, *, tokens: tuple[int, ...] | None = None) -> int:
        matches = [
            symbol.id
            for symbol in interner.symbol_table().values()
            if symbol.kind == "Var" and symbol.local_name == local_name
            and (tokens is None or symbol.id in tokens)
        ]
        assert len(matches) == 1
        return int(matches[0])

    lowered_mp2b = lower_semantic_replay_plan(
        replay,
        LegacyReplayBinding(
            language=SETMM_PROP_BINDING,
            provable_judgment=PROVABLE,
            assertions=(SETMM_MP_REPLAY_BINDING,),
            token_symbols={
                SETMM_LPAREN_TOKEN: prop_system.builtins.lp,
                SETMM_IMP_TOKEN: prop_system.builtins.imp,
                SETMM_RPAREN_TOKEN: prop_system.builtins.rp,
            },
            variable_symbols={
                phi_ref: variable_symbol("ph"),
                psi_ref: variable_symbol("ps"),
                chi_ref: variable_symbol("ch"),
            },
            legacy_sorts={WFF: "wff"},
            symbol_table=interner.symbol_table(),
        ),
        proof_name="mp2b",
    )
    assert lowered_mp2b == expected_mp2b

    ax5_variables = {
        variable.local_key: variable for variable in AX5_SIGNATURE.schema_variables
    }
    ax5_draft = start_draft(
        ProofId("test#proof:ax5-canary"),
        CALCULUS,
        (),
        active_distinct=(DistinctPair(p_ref, x_ref),),
    )
    ax5 = apply_assertion(
        ax5_draft,
        CALCULUS,
        AX5_SIGNATURE,
        (),
        subst={ax5_variables["phi"]: p, ax5_variables["x"]: x},
    )
    assert ax5.step.result == Judgment(PROVABLE, (Imp(p, All(x, p)),))
    assert ax5.step.satisfied_distinct == (DistinctPair(p_ref, x_ref),)

    ax5_owner = OwnerId("metamath-logic/fol#assertion:ax5-lowering-canary")
    ax5_phi_ref = VariableRef("schema", ax5_owner, "phi", WFF_VARIABLE)
    ax5_x_ref = VariableRef("schema", ax5_owner, "x", SETVAR_VARIABLE)
    proof_only_ref = VariableRef("local", ax5_owner, "proof-only", WFF_VARIABLE)
    ax5_phi = LANGUAGE.variable(ax5_phi_ref)
    ax5_x = SetVar(ax5_x_ref)
    ax5_theorem = AssertionSignature(
        id=AssertionSemanticId("metamath-logic/fol#theorem:ax5-lowering-canary"),
        canonical_label="ax5-lowering-canary",
        kind="theorem",
        schema_variables=(ax5_phi_ref, ax5_x_ref),
        premises=(),
        conclusion=Judgment(PROVABLE, (Imp(ax5_phi, All(ax5_x, ax5_phi)),)),
        mandatory_distinct=(DistinctPair(ax5_phi_ref, ax5_x_ref),),
    )
    ax5_theorem_draft = start_draft(
        ProofId("test#proof:ax5-lowering-canary"),
        CALCULUS,
        (),
        active_distinct=(
            DistinctPair(ax5_phi_ref, ax5_x_ref),
            DistinctPair(ax5_x_ref, proof_only_ref),
        ),
        signature=ax5_theorem,
    )
    ax5_application = apply_assertion_by_id(
        ax5_theorem_draft,
        CALCULUS,
        FOL_ASSERTION_CATALOG,
        FOL_CORE_PROFILE,
        AX5_SIGNATURE.id,
        (),
        subst={
            ax5_variables["phi"]: ax5_phi,
            ax5_variables["x"]: ax5_x,
        },
    )
    ax5_proof = finalize_proof(
        ax5_application.draft,
        CALCULUS,
        root=ax5_application.step.id,
    )
    ax5_replay = build_semantic_replay_plan(
        ax5_proof,
        CALCULUS,
        FOL_ASSERTION_CATALOG,
        FOL_CORE_PROFILE,
    )

    fol_system = FolSystem.make(
        interner=interner,
        names=prop_system.names,
    )
    expected_ax5_statement = fol_system.compile(AX5, ctx="ax5-lowering-canary")
    ph_symbol = variable_symbol("ph", tokens=expected_ax5_statement.tokens)
    x_symbol = variable_symbol("x", tokens=expected_ax5_statement.tokens)
    proof_only_symbol = variable_symbol("ps")
    expected_ax5_distinct = normalize_dv_pairs(
        ((ph_symbol, x_symbol), (x_symbol, proof_only_symbol)),
        symtab=interner.symbol_table(),
    )
    lowered_ax5 = lower_semantic_replay_plan(
        ax5_replay,
        LegacyReplayBinding(
            language=SETMM_FOL_BINDING,
            provable_judgment=PROVABLE,
            assertions=(SETMM_AX5_REPLAY_BINDING,),
            token_symbols={
                SETMM_LPAREN_TOKEN: fol_system.builtins.lp,
                SETMM_IMP_TOKEN: fol_system.builtins.imp,
                SETMM_RPAREN_TOKEN: fol_system.builtins.rp,
                SETMM_FORALL_TOKEN: fol_system.builtins.forall,
            },
            variable_symbols={
                ax5_phi_ref: ph_symbol,
                ax5_x_ref: x_symbol,
                proof_only_ref: proof_only_symbol,
            },
            legacy_sorts={WFF: "wff", SETVAR: "setvar"},
            symbol_table=interner.symbol_table(),
        ),
        proof_name="ax5-lowering-canary",
    )
    assert lowered_ax5 == Proof(
        "ax5-lowering-canary",
        expected_ax5_statement,
        (
            Step(
                "res",
                expected_ax5_statement,
                "ax-5",
                op="ref",
                ref="ax-5",
            ),
        ),
        expected_ax5_distinct,
    )


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
