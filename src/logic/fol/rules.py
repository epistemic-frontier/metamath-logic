"""Public first-order inference-rule registry."""

from __future__ import annotations

from collections.abc import Mapping

from skfd.authoring.assertion import signature_from_primitive_rule
from skfd.authoring.ids import AssertionSemanticId
from skfd.authoring.judgment import PrimitiveRuleDecl

from logic.prop.calculus import MP

from .calculus import GEN

GEN_ASSERTION = signature_from_primitive_rule(
    GEN,
    assertion_id=AssertionSemanticId("metamath-logic/fol#assertion:ax-gen"),
    canonical_label="ax-gen",
)

RULES: Mapping[str, PrimitiveRuleDecl] = {
    "ax-mp": MP,
    "ax-gen": GEN,
}

__all__ = ["GEN_ASSERTION", "RULES"]
