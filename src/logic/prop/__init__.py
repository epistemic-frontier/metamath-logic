"""Public propositional-logic API."""

from collections.abc import Mapping

from logic.prop._semantic_proofs import prove_mp2b as _prove_mp2b_semantic
from logic.prop._system import System, make
from logic.prop.axioms import AXIOMS
from logic.prop.calculus import CALCULUS
from logic.prop.language import LANGUAGE
from logic.prop.rules import RULES
from logic.prop.theorems import THEOREMS as _GENERATED_THEOREMS
from logic.prop.theorems import LemmaCtor

THEOREMS: Mapping[str, LemmaCtor] = {
    **_GENERATED_THEOREMS,
    "mp2b": _prove_mp2b_semantic,
}

__all__ = ["AXIOMS", "CALCULUS", "LANGUAGE", "RULES", "THEOREMS", "System", "make"]
