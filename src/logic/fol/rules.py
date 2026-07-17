"""Public first-order inference-rule registry."""

from __future__ import annotations

from collections.abc import Mapping

from skfd.authoring.judgment import PrimitiveRuleDecl

from logic.prop.rules import RULES as PROP_RULES

RULES: Mapping[str, PrimitiveRuleDecl] = PROP_RULES

__all__ = ["RULES"]
