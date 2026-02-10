from __future__ import annotations

from collections.abc import Mapping
from typing import cast

from skfd.authoring.dsl import Axiom, export_axioms
from skfd.authoring.parsing import wff

# AX5: phi -> A. x phi
AX5: Axiom = wff("φ → ∀ x φ")

# AX6: -. A. x -. x = y
AX6: Axiom = wff("¬ ∀ x ¬ x = y")

# AX7: x = y -> ( x = z -> y = z )
AX7: Axiom = wff("x = y → ( x = z → y = z )")

# AX8: x = y -> ( x e. z -> y e. z )
AX8: Axiom = wff("x = y → ( x e. z → y e. z )")

# AX9: x = y -> ( z e. x -> z e. y )
AX9: Axiom = wff("x = y → ( z e. x → z e. y )")

# AX10: -. A. x phi -> A. x -. A. x phi
AX10: Axiom = wff("¬ ∀ x φ → ∀ x ¬ ∀ x φ")

# AX11: A. x A. y phi -> A. y A. x phi
AX11: Axiom = wff("∀ x ∀ y φ → ∀ y ∀ x φ")

# AX12: x = y -> ( A. y phi -> A. x ( x = y -> phi ) )
AX12: Axiom = wff("x = y → ( ∀ y φ → ∀ x ( x = y → φ ) )")

# AX13 (ax-13): ( -. x = y -> ( y = z -> A. x y = z ) )
AX13: Axiom = wff("¬ x = y → ( y = z → ∀ x y = z )")

def make_axioms() -> Mapping[str, Axiom]:
    return cast(Mapping[str, Axiom], export_axioms(globals()))

__all__ = ["AX5", "AX6", "AX7", "AX8", "AX9", "AX10", "AX11", "AX12", "AX13", "make_axioms"]
