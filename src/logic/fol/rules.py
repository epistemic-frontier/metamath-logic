"""Public first-order inference-rule registry."""

from __future__ import annotations

from collections.abc import Mapping

from skfd.authoring.judgment import PrimitiveRuleDecl

from logic.prop.calculus import MP

from .calculus import GEN

RULES: Mapping[str, PrimitiveRuleDecl] = {
    "ax-mp": MP,
    "ax-gen": GEN,
}

__all__ = ["RULES"]
