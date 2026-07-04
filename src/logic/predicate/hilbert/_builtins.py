from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from prelude.formula import Builtins as PropositionalBuiltins
from skfd.authoring.formula import Wff
from skfd.core.symbols import SymbolId, SymbolInterner

PREDICATE_BUILTINS_MODULE_ID = "logic.predicate"


@dataclass(frozen=True)
class PredicateBuiltins:
    """Predicate-owned token vocabulary layered over the foundation/propositional core."""

    lp: SymbolId
    rp: SymbolId
    imp: SymbolId
    neg: SymbolId
    and_: SymbolId
    forall: SymbolId  # "A."
    exist: SymbolId  # "E."
    eq: SymbolId  # "="
    elem: SymbolId  # "e."

    @staticmethod
    def ensure(
        interner: SymbolInterner,
        *,
        origin_module_id: str = PREDICATE_BUILTINS_MODULE_ID,
        origin_ref: Any = None,
    ) -> PredicateBuiltins:
        core = PropositionalBuiltins.ensure(interner, origin_ref=origin_ref)
        forall = interner.intern(
            origin_module_id=origin_module_id, local_name="A.", kind="Const", origin_ref=origin_ref
        )
        exist = interner.intern(
            origin_module_id=origin_module_id, local_name="E.", kind="Const", origin_ref=origin_ref
        )
        eq = interner.intern(
            origin_module_id=origin_module_id, local_name="=", kind="Const", origin_ref=origin_ref
        )
        elem = interner.intern(
            origin_module_id=origin_module_id, local_name="e.", kind="Const", origin_ref=origin_ref
        )
        return PredicateBuiltins(
            lp=core.lp,
            rp=core.rp,
            imp=core.imp,
            neg=core.neg,
            and_=core.and_,
            forall=forall,
            exist=exist,
            eq=eq,
            elem=elem,
        )


def forall2(b: PredicateBuiltins, x: Wff, phi: Wff) -> Wff:
    """Construct A. x phi."""
    return Wff("wff", (b.forall, *x.tokens, *phi.tokens))


def exist(b: PredicateBuiltins, x: Wff, phi: Wff) -> Wff:
    """Construct E. x phi."""
    return Wff("wff", (b.exist, *x.tokens, *phi.tokens))


def eq(b: PredicateBuiltins, x: Wff, y: Wff) -> Wff:
    return Wff("wff", (*x.tokens, b.eq, *y.tokens))


def elem(b: PredicateBuiltins, x: Wff, z: Wff) -> Wff:
    return Wff("wff", (*x.tokens, b.elem, *z.tokens))


__all__ = [
    "PREDICATE_BUILTINS_MODULE_ID",
    "PredicateBuiltins",
    "elem",
    "eq",
    "exist",
    "forall2",
]
