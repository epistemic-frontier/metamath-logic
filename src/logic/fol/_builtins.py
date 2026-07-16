from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from skfd.authoring.formula import Wff
from skfd.core.symbols import SymbolId, SymbolInterner

from logic.prop._builtins import PropositionalBuiltins

PREDICATE_BUILTINS_MODULE_ID = "logic.fol"


@dataclass(frozen=True)
class PredicateBuiltins:
    """Predicate-owned token vocabulary layered over the foundation/propositional core."""

    lp: SymbolId
    rp: SymbolId
    imp: SymbolId
    neg: SymbolId
    and_: SymbolId
    iff: SymbolId
    or_: SymbolId
    tru: SymbolId
    fal: SymbolId
    nand: SymbolId
    cadd: SymbolId
    xor: SymbolId
    had: SymbolId
    if_: SymbolId
    nor: SymbolId
    forall: SymbolId  # "∀"
    exist: SymbolId  # "∃"
    eu: SymbolId  # "E!"
    moeu: SymbolId  # "E*"
    nf: SymbolId  # "F/"
    eq: SymbolId  # "="
    elem: SymbolId  # "e."
    cv: SymbolId  # "cv"
    sb_lb: SymbolId  # "["
    sb_slash: SymbolId  # "/"
    sb_rb: SymbolId  # "]"

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
        eu = interner.intern(
            origin_module_id=origin_module_id, local_name="E!", kind="Const", origin_ref=origin_ref
        )
        moeu = interner.intern(
            origin_module_id=origin_module_id, local_name="E*", kind="Const", origin_ref=origin_ref
        )
        eq = interner.intern(
            origin_module_id=origin_module_id, local_name="=", kind="Const", origin_ref=origin_ref
        )
        elem = interner.intern(
            origin_module_id=origin_module_id, local_name="e.", kind="Const", origin_ref=origin_ref
        )
        cv = interner.intern(
            origin_module_id=origin_module_id,
            local_name="class-of",
            kind="Const",
            origin_ref=origin_ref,
        )
        nf = interner.intern(
            origin_module_id=origin_module_id, local_name="F/", kind="Const", origin_ref=origin_ref
        )
        sb_lb = interner.intern(
            origin_module_id=origin_module_id, local_name="[", kind="Const", origin_ref=origin_ref
        )
        sb_slash = interner.intern(
            origin_module_id=origin_module_id, local_name="/", kind="Const", origin_ref=origin_ref
        )
        sb_rb = interner.intern(
            origin_module_id=origin_module_id, local_name="]", kind="Const", origin_ref=origin_ref
        )
        return PredicateBuiltins(
            lp=core.lp,
            rp=core.rp,
            imp=core.imp,
            neg=core.neg,
            and_=core.and_,
            iff=core.iff,
            or_=core.or_,
            tru=core.tru,
            fal=core.fal,
            nand=core.nand,
            cadd=core.cadd,
            xor=core.xor,
            had=core.had,
            if_=core.if_,
            nor=core.nor,
            forall=forall,
            exist=exist,
            eu=eu,
            moeu=moeu,
            nf=nf,
            eq=eq,
            elem=elem,
            cv=cv,
            sb_lb=sb_lb,
            sb_slash=sb_slash,
            sb_rb=sb_rb,
        )


def forall2(b: PredicateBuiltins, x: Wff, phi: Wff) -> Wff:
    """Construct A. x φ."""
    return Wff("wff", (b.forall, *x.tokens, *phi.tokens))


def exist(b: PredicateBuiltins, x: Wff, phi: Wff) -> Wff:
    """Construct E. x φ."""
    return Wff("wff", (b.exist, *x.tokens, *phi.tokens))


def eu(b: PredicateBuiltins, x: Wff, phi: Wff) -> Wff:
    """Construct E! x φ."""
    return Wff("wff", (b.eu, *x.tokens, *phi.tokens))


def moeu(b: PredicateBuiltins, x: Wff, phi: Wff) -> Wff:
    """Construct E* x φ."""
    return Wff("wff", (b.moeu, *x.tokens, *phi.tokens))


def eq(b: PredicateBuiltins, x: Wff, y: Wff) -> Wff:
    return Wff("wff", (*x.tokens, b.eq, *y.tokens))


def elem(b: PredicateBuiltins, x: Wff, z: Wff) -> Wff:
    return Wff("wff", (*x.tokens, b.elem, *z.tokens))


def cv(b: PredicateBuiltins, x: Wff) -> Wff:
    """Construct class expression from setvar x."""
    return Wff("class", (b.cv, *x.tokens))


def nf(b: PredicateBuiltins, x: Wff, phi: Wff) -> Wff:
    """Construct F/ x φ."""
    return Wff("wff", (b.nf, *x.tokens, *phi.tokens))


def wsb(b: PredicateBuiltins, y: Wff, x: Wff, phi: Wff) -> Wff:
    """Construct [ y / x ] φ."""
    return Wff("wff", (b.sb_lb, *y.tokens, b.sb_slash, *x.tokens, b.sb_rb, *phi.tokens))


__all__ = [
    "PREDICATE_BUILTINS_MODULE_ID",
    "PredicateBuiltins",
    "cv",
    "elem",
    "eq",
    "eu",
    "exist",
    "moeu",
    "forall2",
    "nf",
    "wsb",
]
