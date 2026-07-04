"""Russell-Bernays axiomatization skeleton.

set.mm range:
    Derive the Lukasiewicz axioms from the Russell-Bernays axioms starts at
    set.mm line 14110.

Scope:
    Reserve this module for Russell-Bernays axiom schemes, the derived
    detachment rule, and the bridge proofs from Russell-Bernays to
    Lukasiewicz and the standard Hilbert basis.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping

from skfd.proof import Proof

from .. import System

LemmaCtor = Callable[[System], Proof]

THEOREMS: Mapping[str, LemmaCtor] = {}

__all__ = ["LemmaCtor", "THEOREMS"]
