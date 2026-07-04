"""Truth-table theorem skeleton.

set.mm range:
    ``Truth tables`` occupies set.mm lines 12296-12587.

Scope:
    This module is reserved for the finite truth-value evaluation theorems for
    connectives already introduced in propositional calculus:

    - implication: ``truimtru``, ``truimfal``, ``falimtru``, ``falimfal``
    - negation: ``nottru``, ``notfal``
    - biconditional: ``trubitru``, ``falbitru``, ``trubifal``, ``falbifal``
    - conjunction and disjunction truth tables
    - alternative denial, exclusive disjunction, and joint denial truth tables

Boundary:
    Keep connective syntax/definitions in their own modules. This module
    should only contain theorems that evaluate those connectives on ``T.`` and
    ``F.``.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping

from skfd.proof import Proof

from . import System

LemmaCtor = Callable[[System], Proof]

THEOREMS: Mapping[str, LemmaCtor] = {}

__all__ = ["LemmaCtor", "THEOREMS"]
