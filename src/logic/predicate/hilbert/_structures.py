from __future__ import annotations

from collections.abc import Sequence

from skfd.authoring.dsl import Var, symbol
from skfd.authoring.formula import Wff
from skfd.authoring.typing import WFF
from logic.propositional.hilbert._structures import Imp, Not

from ._builtins import PredicateBuiltins
from ._builtins import elem as mk_elem
from ._builtins import eq as mk_eq
from ._builtins import exist as mk_exist
from ._builtins import forall2 as mk_forall2

# Formal variable placeholder (reuse wff sort discipline)
phi = Var(name="φ")
x = Var(name="x")
y = Var(name="y")
z = Var(name="z")
w = Var(name="w")


# Binary forall constructor (variable + body)
@symbol(
    "A.",
    2,
    (WFF, WFF),
    WFF,
    notes="binary forall over wff (var placeholder)",
    precedence=40,
    assoc="right",
    aliases=["∀"],
)
def All(b: PredicateBuiltins, xs: Sequence[Wff]) -> Wff:
    return mk_forall2(b, xs[0], xs[1])


@symbol(
    "E.",
    2,
    (WFF, WFF),
    WFF,
    notes="binary exists over wff (var placeholder)",
    precedence=40,
    assoc="right",
    aliases=["∃"],
)
def Exists(b: PredicateBuiltins, xs: Sequence[Wff]) -> Wff:
    return mk_exist(b, xs[0], xs[1])


@symbol("=", 2, (WFF, WFF), WFF, op="eq", notes="equality", precedence=30, assoc="none")
def Eq(b: PredicateBuiltins, xs: Sequence[Wff]) -> Wff:
    return mk_eq(b, xs[0], xs[1])


@symbol("e.", 2, (WFF, WFF), WFF, notes="membership", precedence=30, assoc="none")
def Elem(b: PredicateBuiltins, xs: Sequence[Wff]) -> Wff:
    return mk_elem(b, xs[0], xs[1])


__all__ = [
    "phi",
    "x",
    "All",
    "Exists",
    "Eq",
    "Elem",
    "Imp",
    "Not",
    "y",
    "z",
    "w",
]
