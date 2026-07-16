"""Author-facing Hilbert axiom schemas (Expr-level).

The axioms here are written as Expr trees over the core constructors from
_structures.py. They correspond to the usual Hilbert-style implicational
calculus:
- ax-1 (K): φ → (ψ → φ)
- ax-2 (S): (φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))
- ax-3: (¬φ → ¬ψ) → (ψ → φ)
- df-bi: biconditional definition
- df-3an: ternary conjunction definition

These are not token-level formulas; compilation to Wff is handled by the logic backend.
"""

from __future__ import annotations

from collections.abc import Mapping
from typing import cast

from skfd.authoring.dsl import Axiom, export_axioms

from ._structures import (
    And,
    And3,
    Cadd,
    Falsum,
    Hadd,
    If,
    Iff,
    Imp,
    Nand,
    Nor,
    Not,
    Or,
    Or3,
    Verum,
    Xor,
    chi,
    phi,
    psi,
)

# ax-1: φ → (ψ → φ)
A1: Axiom = Imp(phi, Imp(psi, phi))

# ax-2: (φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))
A2: Axiom = Imp(Imp(phi, Imp(psi, chi)), Imp(Imp(phi, psi), Imp(phi, chi)))

# ax-3: (¬φ → ¬ψ) → (ψ → φ)
A3: Axiom = Imp(Imp(Not(phi), Not(psi)), Imp(psi, phi))

# df-bi: ¬(((φ ↔ ψ) → ¬((φ → ψ) → ¬(ψ → φ))) → ¬(¬((φ → ψ) → ¬(ψ → φ)) → (φ ↔ ψ)))
# Let Y = (φ → ψ) → ¬(ψ → φ), let X = (φ ↔ ψ).
# Then df-bi = ¬((X → ¬Y) → ¬(¬Y → X))
_Y: Axiom = Imp(Imp(phi, psi), Not(Imp(psi, phi)))
_X: Axiom = Iff(phi, psi)
df_bi: Axiom = Not(Imp(Imp(_X, Not(_Y)), Not(Imp(Not(_Y), _X))))

# df-an: ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) )
df_an: Axiom = Iff(And(phi, psi), Not(Imp(phi, Not(psi))))

# df-nan: ( ( ph -/\ ps ) <-> -. ( ph /\ ps ) )
df_nan: Axiom = Iff(Nand(phi, psi), Not(And(phi, psi)))

# df-nor: ( ( ph -\/ ps ) <-> -. ( ph \/ ps ) )
df_nor: Axiom = Iff(Nor(phi, psi), Not(Or(phi, psi)))

# df-xor: ( ( ph \/_ ps ) <-> -. ( ph <-> ps ) )
df_xor: Axiom = Iff(Xor(phi, psi), Not(Iff(phi, psi)))

# df-3an: ( ( ph /\ ps /\ ch ) <-> ( ( ph /\ ps ) /\ ch ) )
df_3an: Axiom = Iff(And3(phi, psi, chi), And(And(phi, psi), chi))

# df-3or: ( ( φ ∨ ψ ∨ χ ) ↔ ( ( φ ∨ ψ ) ∨ χ ) )
df_3or: Axiom = Iff(Or3(phi, psi, chi), Or(Or(phi, psi), chi))

# df-or: ( ( ph \/ ps ) <-> ( -. ph -> ps ) )
df_or: Axiom = Iff(Or(phi, psi), Imp(Not(phi), psi))

# df-tru: ( T. <-> ( ph -> ph ) )
df_tru: Axiom = Iff(Verum(), Imp(phi, phi))

# df-fal: ( F. <-> -. T. )
df_fal: Axiom = Iff(Falsum(), Not(Verum()))

# df-cad: cadd ( ph , ps , ch ) <-> ( ( ph /\ ps ) \/ ( ch /\ ( ph \/_ ps ) ) )
df_cad: Axiom = Iff(Cadd(phi, psi, chi), Or(And(phi, psi), And(chi, Xor(phi, psi))))

# df-had: hadd( ph , ps , ch ) <-> ( ( ph \/_ ps ) \/_ ch )
df_had: Axiom = Iff(Hadd(phi, psi, chi), Xor(Xor(phi, psi), chi))

# df-ifp: if- ( ph , ps , ch ) <-> ( ( ph /\ ps ) \/ ( -. ph /\ ch ) )
df_ifp: Axiom = Iff(If(phi, psi, chi), Or(And(phi, psi), And(Not(phi), chi)))


def make_axioms() -> Mapping[str, Axiom]:
    raw = cast(Mapping[str, Axiom], export_axioms(globals()))
    # Map Python-safe names to set.mm labels
    name_map = {
        "A1": "ax-1",
        "A2": "ax-2",
        "A3": "ax-3",
        "df_bi": "df-bi",
        "df_an": "df-an",
        "df_3an": "df-3an",
        "df_3or": "df-3or",
        "df_or": "df-or",
        "df_tru": "df-tru",
        "df_fal": "df-fal",
        "df_cad": "df-cad",
        "df_had": "df-had",
        "df_nan": "df-nan",
        "df_nor": "df-nor",
        "df_xor": "df-xor",
        "df_ifp": "df-ifp",
    }
    return {name_map.get(k, k): v for k, v in raw.items()}


SETMM_TO_HILBERT_LABELS: Mapping[str, str] = {
    "ax-1": "ax-1",
    "ax-2": "ax-2",
    "ax-3": "ax-3",
    "df-bi": "df-bi",
    "df-an": "df-an",
    "df-3an": "df-3an",
    "df-3or": "df-3or",
    "df-or": "df-or",
    "df-tru": "df-tru",
    "df-fal": "df-fal",
    "df-cad": "df-cad",
    "df-had": "df-had",
    "df-nan": "df-nan",
    "df-nor": "df-nor",
    "df-xor": "df-xor",
    "df-ifp": "df-ifp",
}


__all__ = [
    "A1",
    "A2",
    "A3",
    "df_bi",
    "df_3an",
    "df_3or",
    "df_tru",
    "df_fal",
    "df_or",
    "df_cad",
    "df_had",
    "df_nan",
    "df_nor",
    "df_xor",
    "df_ifp",
    "make_axioms",
    "SETMM_TO_HILBERT_LABELS",
]
