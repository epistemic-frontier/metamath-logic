"""Lukasiewicz axiomatization skeleton.

set.mm ranges:
    - Implicational calculus starts at set.mm line 12939.
    - Derive the standard axioms from the Lukasiewicz axioms starts at line
      13282.

Scope:
    Reserve this module for the Lukasiewicz axiom schemes, intermediate
    derivation steps, and theorems reconstructing the standard Hilbert axioms
    from the Lukasiewicz basis.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping

from skfd.proof import Proof

from .. import System

LemmaCtor = Callable[[System], Proof]

THEOREMS: Mapping[str, LemmaCtor] = {}

__all__ = ["LemmaCtor", "THEOREMS"]
