from __future__ import annotations

from collections.abc import Sequence

from skfd.authoring.dsl import Var, symbol
from skfd.authoring.formula import Wff
from skfd.authoring.typing import WFF

from logic.propositional.hilbert._structures import Imp, Not

from ._builtins import PredicateBuiltins
from ._builtins import cv as mk_cv
from ._builtins import elem as mk_elem
from ._builtins import eq as mk_eq
from ._builtins import eu as mk_eu
from ._builtins import exist as mk_exist
from ._builtins import forall2 as mk_forall2
from ._builtins import moeu as mk_moeu
from ._builtins import nf as mk_nf
from ._builtins import wsb as mk_wsb

# Formal variable placeholder (reuse wff sort discipline)
phi = Var(name="φ")
psi = Var(name="ψ")
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


@symbol(
    "E!",
    2,
    (WFF, WFF),
    WFF,
    notes="there exists a unique (E!)",
    precedence=40,
    assoc="right",
    aliases=["∃!"],
)
def Eu(b: PredicateBuiltins, xs: Sequence[Wff]) -> Wff:
    return mk_eu(b, xs[0], xs[1])


@symbol(
    "E*",
    2,
    (WFF, WFF),
    WFF,
    notes="there exists at most one (E*)",
    precedence=40,
    assoc="right",
    aliases=["∃*"],
)
def Mo(b: PredicateBuiltins, xs: Sequence[Wff]) -> Wff:
    return mk_moeu(b, xs[0], xs[1])


@symbol(
    "F/",
    2,
    (WFF, WFF),
    WFF,
    notes="not free (F/)",
    precedence=40,
    assoc="right",
)
def NF(b: PredicateBuiltins, xs: Sequence[Wff]) -> Wff:
    return mk_nf(b, xs[0], xs[1])


@symbol("[", 3, (WFF, WFF, WFF), WFF, notes="proper substitution [ y / x ] ph")
def Wsb(b: PredicateBuiltins, xs: Sequence[Wff]) -> Wff:
    return mk_wsb(b, xs[0], xs[1], xs[2])


@symbol("=", 2, (WFF, WFF), WFF, op="eq", notes="equality", precedence=30, assoc="none")
def Eq(b: PredicateBuiltins, xs: Sequence[Wff]) -> Wff:
    return mk_eq(b, xs[0], xs[1])


@symbol("e.", 2, (WFF, WFF), WFF, notes="membership", precedence=30, assoc="none")
def Elem(b: PredicateBuiltins, xs: Sequence[Wff]) -> Wff:
    return mk_elem(b, xs[0], xs[1])


@symbol("cv", 1, (WFF,), WFF, notes="class of setvar (cv)")
def Cv(b: PredicateBuiltins, xs: Sequence[Wff]) -> Wff:
    return mk_cv(b, xs[0])


__all__ = [
    "phi",
    "psi",
    "x",
    "All",
    "Cv",
    "Eu",
    "Exists",
    "Eq",
    "Elem",
    "Imp",
    "Mo",
    "NF",
    "Not",
    "Wsb",
    "y",
    "z",
    "w",
]
