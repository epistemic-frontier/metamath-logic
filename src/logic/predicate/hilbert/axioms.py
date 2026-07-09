from __future__ import annotations

from collections.abc import Mapping
from typing import cast

from skfd.authoring.dsl import Axiom, export_axioms

from ._structures import All, Elem, Eq, Imp, Not, phi, psi, x, y, z

# AX4: ∀ x ( φ → ψ ) → ( ∀ x φ → ∀ x ψ )
AX4: Axiom = Imp(All(x, Imp(phi, psi)), Imp(All(x, phi), All(x, psi)))

# AX5: φ → ∀ x φ
AX5: Axiom = Imp(phi, All(x, phi))

# AX6: ¬ ∀ x ¬ x = y
AX6: Axiom = Not(All(x, Not(Eq(x, y))))

# AX7: x = y → ( x = z → y = z )
AX7: Axiom = Imp(Eq(x, y), Imp(Eq(x, z), Eq(y, z)))

# AX8: x = y → ( x e. z → y e. z )
AX8: Axiom = Imp(Eq(x, y), Imp(Elem(x, z), Elem(y, z)))

# AX9: x = y → ( z e. x → z e. y )
AX9: Axiom = Imp(Eq(x, y), Imp(Elem(z, x), Elem(z, y)))

# AX10: ¬ ∀ x φ → ∀ x ¬ ∀ x φ
AX10: Axiom = Imp(Not(All(x, phi)), All(x, Not(All(x, phi))))

# AX11: ∀ x ∀ y φ → ∀ y ∀ x φ
AX11: Axiom = Imp(All(x, All(y, phi)), All(y, All(x, phi)))

# AX12: x = y → ( ∀ y φ → ∀ x ( x = y → φ ) )
AX12: Axiom = Imp(Eq(x, y), Imp(All(y, phi), All(x, Imp(Eq(x, y), phi))))

# AX13 (ax-13): ( ¬ x = y → ( y = z → ∀ x y = z ) )
AX13: Axiom = Imp(Not(Eq(x, y)), Imp(Eq(y, z), All(x, Eq(y, z))))


def make_axioms() -> Mapping[str, Axiom]:
    return cast(Mapping[str, Axiom], export_axioms(globals()))


__all__ = ["AX4", "AX5", "AX6", "AX7", "AX8", "AX9", "AX10", "AX11", "AX12", "AX13", "make_axioms"]
