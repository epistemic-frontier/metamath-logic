# logic/propositional/hilbert/axioms.py
"""Author-facing Hilbert axiom schemas (Expr-level).

The axioms here are written as Expr trees over the core constructors from
_structures.py. They correspond to the usual Hilbert-style implicational
calculus:
- A1 (K): φ → (ψ → φ)
- A2 (S): (φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))
- A3: (¬φ → ¬ψ) → (ψ → φ)

These are not token-level formulas; compilation to Wff is done via
HilbertSystem.compile(expr).
"""

from __future__ import annotations

from collections.abc import Mapping

from skfd.authoring.dsl import Expr

from ._structures import Imp, Not, chi, phi, psi

# A1: φ → (ψ → φ)
A1: Expr = Imp(phi, Imp(psi, phi))

# A2: (φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))
A2: Expr = Imp(
    Imp(phi, Imp(psi, chi)),
    Imp(Imp(phi, psi), Imp(phi, chi)),
)

# A3: (¬φ → ¬ψ) → (ψ → φ)
A3: Expr = Imp(
    Imp(Not(phi), Not(psi)),
    Imp(psi, phi),
)


def make_axioms() -> Mapping[str, Expr]:
    return  {
        "A1": A1,
        "A2": A2,
        "A3": A3,
    }


SETMM_TO_HILBERT_LABELS: Mapping[str, str] = {
    "ax-1": "A1",
    "ax-2": "A2",
    "ax-3": "A3",
}


__all__ = ["A1", "A2", "A3", "make_axioms", "SETMM_TO_HILBERT_LABELS"]
