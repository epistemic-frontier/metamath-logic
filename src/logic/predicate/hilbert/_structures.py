from __future__ import annotations

from skfd.authoring.dsl import Var, symbol
from skfd.authoring.typing import WFF
from logic.propositional.hilbert._structures import Imp, Not

from prelude.formula import forall2 as mk_forall2
from prelude.formula import eq as mk_eq
from prelude.formula import elem as mk_elem
from prelude.formula import exist as mk_exist

# Formal variable placeholder (reuse wff sort discipline)
phi = Var(name="φ")
x = Var(name="x")
y = Var(name="y")
z = Var(name="z")
w = Var(name="w")

# Binary forall constructor (variable + body)
@symbol("∀", 2, (WFF, WFF), WFF, notes="binary forall over wff (var placeholder)", precedence=40, assoc="right", aliases=["A."])
def All(b, xs):
    return mk_forall2(b, xs[0], xs[1])

@symbol("∃", 2, (WFF, WFF), WFF, notes="binary exists over wff (var placeholder)", precedence=40, assoc="right", aliases=["E."])
def Exists(b, xs):
    return mk_exist(b, xs[0], xs[1])

@symbol("=", 2, (WFF, WFF), WFF, op="eq", notes="equality", precedence=30, assoc="none")
def Eq(b, xs):
    return mk_eq(b, xs[0], xs[1])

@symbol("e.", 2, (WFF, WFF), WFF, notes="membership", precedence=30, assoc="none")
def Elem(b, xs):
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
