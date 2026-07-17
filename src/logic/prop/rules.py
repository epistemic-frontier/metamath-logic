"""Public propositional inference-rule registry."""

from __future__ import annotations

from collections.abc import Mapping

from skfd.authoring.assertion import signature_from_primitive_rule
from skfd.authoring.ids import AssertionSemanticId
from skfd.authoring.judgment import PrimitiveRuleDecl

from .calculus import MP

MP_ASSERTION = signature_from_primitive_rule(
    MP,
    assertion_id=AssertionSemanticId("metamath-logic/prop#assertion:ax-mp"),
    canonical_label="ax-mp",
)

RULES: Mapping[str, PrimitiveRuleDecl] = {"ax-mp": MP}

__all__ = ["MP_ASSERTION", "RULES"]
