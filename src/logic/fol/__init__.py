"""Public first-order-logic API."""

from logic.fol._system import System, make
from logic.fol.axioms import AXIOMS
from logic.fol.calculus import CALCULUS
from logic.fol.language import LANGUAGE
from logic.fol.rules import RULES
from logic.fol.theorems import THEOREMS

__all__ = ["AXIOMS", "CALCULUS", "LANGUAGE", "RULES", "THEOREMS", "System", "make"]
