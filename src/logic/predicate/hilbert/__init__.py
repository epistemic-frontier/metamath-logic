from __future__ import annotations

from collections.abc import Mapping
from typing import Any

from skfd.core.symbols import SymbolInterner

from .system import PredicateSystem, make as make_system
from .axioms import make_axioms

# Mapping from set.mm labels to local predicate system labels
SETMM_TO_PREDICATE_AXIOMS: Mapping[str, str] = {
    "ax-5": "AX5",
    "ax-6": "AX6",
    "ax-7": "AX7",
    "ax-8": "AX8",
    "ax-9": "AX9",
    "ax-10": "AX10",
    "ax-11": "AX11",
    "ax-12": "AX12",
    "ax-13": "AX13",
}

def make(*, interner: SymbolInterner, origin_ref: Any = None) -> PredicateSystem:
    return make_system(interner=interner, origin_ref=origin_ref)

__all__ = [
    "PredicateSystem",
    "make",
    "SETMM_TO_PREDICATE_AXIOMS",
    "make_axioms",
]
