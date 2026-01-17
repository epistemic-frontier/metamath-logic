from __future__ import annotations

from collections.abc import Mapping
from skfd.authoring.dsl import Axiom, Expr, export_axioms
from skfd.authoring.parsing import wff

from logic.predicate.hilbert._structures import All, Elem, Eq, phi, x, y, z

# AX5: phi -> A. x phi
AX5: Axiom = wff("ph -> A. x ph")

# AX6: -. A. x -. x = y
AX6: Axiom = wff("-. A. x -. x = y")

# AX7: x = y -> ( x = z -> y = z )
AX7: Axiom = wff("x = y -> ( x = z -> y = z )")

# AX8: x = y -> ( x e. z -> y e. z )
AX8: Axiom = wff("x = y -> ( x e. z -> y e. z )")

# AX9: x = y -> ( z e. x -> z e. y )
AX9: Axiom = wff("x = y -> ( z e. x -> z e. y )")

# AX10: -. A. x phi -> A. x -. A. x phi
AX10: Axiom = wff("-. A. x ph -> A. x -. A. x ph")

# AX11: A. x A. y phi -> A. y A. x phi
AX11: Axiom = wff("A. x A. y ph -> A. y A. x ph")

# AX12: x = y -> ( A. y phi -> A. x ( x = y -> phi ) )
AX12: Axiom = wff("x = y -> ( A. y ph -> A. x ( x = y -> ph ) )")

# AX13 (ax-13): ( -. x = y -> ( y = z -> A. x y = z ) )
AX13: Axiom = wff("-. x = y -> ( y = z -> A. x y = z )")

def make_axioms() -> Mapping[str, Axiom]:
    return export_axioms(globals())

__all__ = ["AX5", "AX6", "AX7", "AX8", "AX9", "AX10", "AX11", "AX12", "AX13", "make_axioms"]
