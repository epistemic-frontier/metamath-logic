"""Public propositional-logic API."""

from logic.prop._system import System, make
from logic.prop.axioms import AXIOMS
from logic.prop.calculus import CALCULUS
from logic.prop.language import LANGUAGE
from logic.prop.rules import RULES
from logic.prop.theorems import THEOREMS

__all__ = ["AXIOMS", "CALCULUS", "LANGUAGE", "RULES", "THEOREMS", "System", "make"]
