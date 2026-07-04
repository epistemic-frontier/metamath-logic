"""Alternative propositional axiomatization skeletons.

set.mm range:
    ``Other axiomatizations related to classical propositional calculus``
    occupies set.mm lines 12836-14279.

These modules are kept under ``hilbert`` because set.mm proves the alternative
axiom systems inside the existing Hilbert-style propositional environment.
They are equivalence and derivability results, not independent proof kernels.
If we later need independently runnable systems, create sibling packages under
``logic.propositional`` and bridge them back to this package.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping

from skfd.proof import Proof

from .. import System
from .lukasiewicz import THEOREMS as LUKASIEWICZ
from .meredith import THEOREMS as MEREDITH
from .minimal_implicational import THEOREMS as MINIMAL_IMPLICATIONAL
from .nicod import THEOREMS as NICOD
from .russell_bernays import THEOREMS as RUSSELL_BERNAYS
from .tarski_bernays_wajsberg import THEOREMS as TARSKI_BERNAYS_WAJSBERG

LemmaCtor = Callable[[System], Proof]

THEOREMS: Mapping[str, LemmaCtor] = {
    **MINIMAL_IMPLICATIONAL,
    **LUKASIEWICZ,
    **MEREDITH,
    **NICOD,
    **TARSKI_BERNAYS_WAJSBERG,
    **RUSSELL_BERNAYS,
}

__all__ = [
    "LemmaCtor",
    "THEOREMS",
    "MINIMAL_IMPLICATIONAL",
    "LUKASIEWICZ",
    "MEREDITH",
    "NICOD",
    "TARSKI_BERNAYS_WAJSBERG",
    "RUSSELL_BERNAYS",
]
