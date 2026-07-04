"""Propositional full-adder skeleton.

set.mm range:
    ``Half adder and full adder in propositional calculus`` occupies set.mm
    lines 12588-12835.

Scope:
    This module is reserved for the propositional bit-adder connectives:

    - ``hadd`` / ``whad`` / ``df-had`` for full-adder sum
    - ``cadd`` / ``wcad`` / ``df-cad`` for full-adder carry
    - equality, associativity, commutativity, rotation, negation, and
      case-analysis theorems for both sum and carry

Boundary:
    The adder section depends on several late propositional connectives
    (exclusive disjunction, if-then-else, three-way conjunction/disjunction).
    Do not migrate these proofs until the relevant syntax constructors and
    lowering support exist.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping

from skfd.proof import Proof

from . import System

LemmaCtor = Callable[[System], Proof]

THEOREMS: Mapping[str, LemmaCtor] = {}

__all__ = ["LemmaCtor", "THEOREMS"]
