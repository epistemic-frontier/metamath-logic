"""First-order Hilbert axioms."""

from __future__ import annotations

from collections.abc import Mapping
from typing import cast

from skfd.authoring.assertion import signature_from_axiom
from skfd.authoring.dsl import Axiom, export_axioms
from skfd.authoring.ids import AssertionSemanticId, OwnerId
from skfd.authoring.judgment import AxiomDecl, DistinctPair, Judgment, resolve_axiom
from skfd.authoring.term import VariableRef

from logic.prop.calculus import PROVABLE
from logic.prop.language import WFF_VARIABLE
from logic.prop.language import Imp as SemanticImp

from ._structures import All, Elem, Eq, Imp, Not, phi, psi, x, y, z
from .calculus import CALCULUS
from .language import LANGUAGE, SETVAR_VARIABLE, SetVar
from .language import All as SemanticAll

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


_AX5_ID = AssertionSemanticId("metamath-logic/fol#axiom:ax-5")
_AX5_OWNER = OwnerId(str(_AX5_ID))
_AX5_PHI_REF = VariableRef("schema", _AX5_OWNER, "phi", WFF_VARIABLE)
_AX5_X_REF = VariableRef("schema", _AX5_OWNER, "x", SETVAR_VARIABLE)
_AX5_PHI = LANGUAGE.variable(_AX5_PHI_REF)
_AX5_X = SetVar(_AX5_X_REF)

# Typed semantic canary.  The legacy AX5 above remains the emission source until
# the assertion catalog migration, but both describe the same axiom.
AX5_SEMANTIC = resolve_axiom(
    AxiomDecl(
        id=_AX5_ID,
        schema_variables=(_AX5_PHI_REF, _AX5_X_REF),
        conclusion=Judgment(
            PROVABLE,
            (SemanticImp(_AX5_PHI, SemanticAll(_AX5_X, _AX5_PHI)),),
        ),
        mandatory_distinct=(DistinctPair(_AX5_PHI_REF, _AX5_X_REF),),
    ),
    CALCULUS,
)
AX5_SIGNATURE = signature_from_axiom(AX5_SEMANTIC, canonical_label="ax-5")


def make_axioms() -> Mapping[str, Axiom]:
    raw = cast(Mapping[str, Axiom], export_axioms(globals()))
    name_map = {f"AX{number}": f"ax-{number}" for number in range(4, 14)}
    return {name_map.get(name, name): axiom for name, axiom in raw.items()}


AXIOMS: Mapping[str, Axiom] = make_axioms()


__all__ = ["AX5_SEMANTIC", "AX5_SIGNATURE", "AXIOMS"]
