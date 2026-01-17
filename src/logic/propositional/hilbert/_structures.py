# logic/propositional/hilbert/_structures.py
"""Author-facing language skeleton for the Hilbert propositional system.

This module declares:
- formal variables (φ, ψ, χ, ...)
- core constructors with arity (→, ¬, ∧)
- require(...) declarations for signatures (wff discipline)

No Builtins or SymbolInterner appear here; those are injected at system
construction time by logic.propositional.hilbert.HilbertSystem.
"""

from __future__ import annotations

from skfd.authoring.dsl import Var
from prelude.structures import (
    Imp, Not, And, Or, Iff,
    phi, psi, chi, th, ta
)

# Re-export for compatibility
__all__ = [
    "phi",
    "psi",
    "chi",
    "th",
    "ta",
    "Imp",
    "Not",
    "And",
    "Or",
    "Iff",
]
