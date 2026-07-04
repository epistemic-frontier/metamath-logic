"""Stoic logic derivation skeleton.

set.mm range:
    ``Stoic logic non-modal portion (Chrysippus of Soli)`` occupies set.mm
    lines 14280-14552.

Scope:
    This module is reserved for set.mm's derivations of non-modal Stoic logic
    inside the standard propositional Hilbert system:

    - indemonstrables: ``mptnan``, ``mptxor``, ``mtpor``, ``mtpxor``
    - themata: ``stoic1a``, ``stoic1b``, ``stoic2a``, ``stoic2b``,
      ``stoic3``, ``stoic4a``, ``stoic4b``

Boundary:
    These are not a separate proof kernel. They are theorem constructors in
    the existing Hilbert environment showing that the current propositional
    system proves the corresponding Stoic rules.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping

from skfd.proof import Proof

from . import System

LemmaCtor = Callable[[System], Proof]

THEOREMS: Mapping[str, LemmaCtor] = {}

__all__ = ["LemmaCtor", "THEOREMS"]
