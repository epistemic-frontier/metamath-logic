"""Public propositional-logic API."""

from logic.prop._system import System, make
from logic.prop.axioms import AXIOMS
from logic.prop.rules import RULES
from logic.prop.theorems import THEOREMS

__all__ = ["AXIOMS", "RULES", "THEOREMS", "System", "make"]
