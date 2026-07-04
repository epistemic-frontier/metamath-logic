"""Minimal implicational calculus skeleton.

set.mm range:
    Starts at set.mm line 12843.

Scope:
    Reserve this module for ``minimp`` and the derivations showing how the
    minimal implicational single axiom can reconstruct the standard implication
    basis with modus ponens.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping

from skfd.proof import Proof

from .. import System

LemmaCtor = Callable[[System], Proof]

THEOREMS: Mapping[str, LemmaCtor] = {}

__all__ = ["LemmaCtor", "THEOREMS"]
