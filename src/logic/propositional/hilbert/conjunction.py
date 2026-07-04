"""Conjunction calculus skeleton.

set.mm range:
    Main conjunction material starts at set.mm line 4044 with ``wa`` and
    ``df-an`` and continues until disjunction is introduced at line 7289.

Scope:
    This module is reserved for theorems around ``/\\`` and ``df-an``:

    - conjunction introduction and elimination
    - ``simpl*`` and ``simpr*`` projections
    - associativity, commutativity, idempotence, absorption
    - conjunction congruence and implication transport lemmas

Migration notes:
    This should become the main dependency base for truth constants, truth
    tables, natural-deduction context lemmas, and later adder proofs.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping

from skfd.proof import Proof

from . import System

LemmaCtor = Callable[[System], Proof]

THEOREMS: Mapping[str, LemmaCtor] = {}

__all__ = ["LemmaCtor", "THEOREMS"]
