from __future__ import annotations

from skfd.authoring import dsl
from skfd.authoring.dsl import App
from skfd.authoring.parsing import wff
from skfd.core.symbols import SymbolInterner
from skfd.names import NameResolver
from skfd.proof import ProofBuilder

from logic.fol import System as FirstOrderSystem
from logic.prop._structures import And, And3, chi, phi, psi


def test_predicate_system_owns_predicate_tokens() -> None:
    interner = SymbolInterner()

    system = FirstOrderSystem.make(interner=interner, names=NameResolver())
    compiled = system.compile_axioms()

    predicate_axioms = {f"ax-{number}" for number in range(4, 14)}
    assert predicate_axioms <= set(compiled)
    assert not {f"AX{number}" for number in range(4, 14)} & set(compiled)

    token_owners: dict[str, set[str]] = {}
    for d in interner.symbol_table().values():
        if d.local_name in {"A.", "E.", "=", "e."}:
            token_owners.setdefault(d.local_name, set()).add(d.origin_module_id)

    assert token_owners.keys() == {"A.", "E.", "=", "e."}
    assert all("logic.fol" in owners for owners in token_owners.values())


def test_predicate_parser_right_associates_quantifiers() -> None:
    interner = SymbolInterner()
    system = FirstOrderSystem.make(interner=interner, names=NameResolver())

    formula = ProofBuilder(system, "quantifiers").ref("result", "∀ y ∀ x φ", ref="unused")

    symbol_table = interner.symbol_table()
    assert [symbol_table[token].local_name for token in formula.tokens] == [
        "A.",
        "y",
        "A.",
        "x",
        "ph",
    ]


def test_predicate_parser_preserves_ternary_connective_with_quantified_operands() -> None:
    expr = wff("( ∀ x φ ∧ ∀ x ψ ∧ ∀ x χ )")

    assert isinstance(expr, App)
    assert expr.ctor.name == "∧"
    assert len(expr.args) == 3


def test_predicate_system_reuses_declared_conjunction_lowering() -> None:
    interner = SymbolInterner()
    system = FirstOrderSystem.make(interner=interner, names=NameResolver())

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


def test_predicate_parser_accepts_standard_substitution_notation() -> None:
    expr = wff("[ t / x ] φ")

    assert isinstance(expr, App)
    assert expr.ctor.name == "["
    assert expr.args == (dsl.Var("t"), dsl.Var("x"), dsl.Var("φ"))
