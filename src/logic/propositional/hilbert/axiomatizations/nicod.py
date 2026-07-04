"""Nicod axiomatization skeleton.

set.mm ranges:
    - Derive Nicod's axiom from the standard axioms starts at line 13365.
    - Derive the Lukasiewicz axioms from Nicod's axiom starts at line 13446.
    - Derive Nicod's axiom from Lukasiewicz's first Sheffer stroke axiom starts
      at line 13628.

Scope:
    Reserve this module for Nicod-style single-axiom material and the bridge
    proofs between Nicod, Lukasiewicz, and the standard Hilbert axioms.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping

from skfd.proof import Proof

from .. import System

LemmaCtor = Callable[[System], Proof]

THEOREMS: Mapping[str, LemmaCtor] = {}

__all__ = ["LemmaCtor", "THEOREMS"]
