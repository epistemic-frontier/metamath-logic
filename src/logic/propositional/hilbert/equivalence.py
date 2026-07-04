"""Biconditional calculus skeleton.

set.mm range:
    Main biconditional material starts at set.mm line 2390 and continues until
    conjunction is introduced at line 4044.

Scope:
    This module is reserved for theorems around ``<->`` and ``df-bi``:

    - definitional and justification material for biconditional reasoning
    - ``bi*`` inference helpers
    - ``bitr*`` transitivity helpers
    - ``imbi*`` and ``bibi*`` congruence/equality helpers

Migration notes:
    The current implementation still re-exports many early biconditional
    helpers through ``lemmas.py`` or depends on them indirectly. Move theorem
    constructors here when their dependency closure is ready and keep this
    module's ``THEOREMS`` map as the local registry fragment.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping

from skfd.proof import Proof

from . import System

LemmaCtor = Callable[[System], Proof]

THEOREMS: Mapping[str, LemmaCtor] = {}

__all__ = ["LemmaCtor", "THEOREMS"]
