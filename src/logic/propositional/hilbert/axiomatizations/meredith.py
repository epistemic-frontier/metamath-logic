"""Meredith axiomatization skeleton.

set.mm ranges:
    - Derive the Lukasiewicz axioms from Meredith's sole axiom starts at line
      13134.
    - Meredith CO axiom derivations also appear in the Tarski-Bernays-Wajsberg
      subsection starting at lines 13796 and 13991.

Scope:
    Reserve this module for Carew Meredith single-axiom derivations and their
    bridges to Lukasiewicz or Tarski-Bernays-Wajsberg style axioms.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping

from skfd.proof import Proof

from .. import System

LemmaCtor = Callable[[System], Proof]

THEOREMS: Mapping[str, LemmaCtor] = {}

__all__ = ["LemmaCtor", "THEOREMS"]
