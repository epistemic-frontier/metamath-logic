# logic/propositional/hilbert/_syntactic.py
from __future__ import annotations

from prelude.hilbert_rules import (
    DEBUG_CATALOG,
    DEBUG_RULES,
    Mp,
    Wa,
    Wi,
    Wn,
    make_rules,
)
from skfd.authoring.rules import RuleBundle

__all__ = ["RuleBundle", "make_rules", "DEBUG_CATALOG", "DEBUG_RULES", "Wi", "Mp", "Wn", "Wa"]
