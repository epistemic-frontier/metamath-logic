"""Public propositional inference-rule registry."""

from __future__ import annotations

from collections.abc import Mapping

from skfd.authoring.judgment import PrimitiveRuleDecl

from .calculus import MP

RULES: Mapping[str, PrimitiveRuleDecl] = {"ax-mp": MP}

__all__ = ["RULES"]
