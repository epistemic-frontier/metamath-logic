"""Tarski-Bernays-Wajsberg axiomatization skeleton.

set.mm range:
    Derive the Lukasiewicz axioms from the Tarski-Bernays-Wajsberg axioms
    starts at set.mm line 13673.

Scope:
    Reserve this module for TBW axiom schemes and derivations connecting them
    to the Lukasiewicz and standard Hilbert bases.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping

from skfd.proof import Proof

from .. import System

LemmaCtor = Callable[[System], Proof]

THEOREMS: Mapping[str, LemmaCtor] = {}

__all__ = ["LemmaCtor", "THEOREMS"]
