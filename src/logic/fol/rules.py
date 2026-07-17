"""Public first-order inference-rule registry."""

from __future__ import annotations

from collections.abc import Mapping

from skfd.authoring.assertion import signature_from_primitive_rule
from skfd.authoring.catalog import (
    AssertionCatalogSpec,
    AssertionProfileSpec,
    resolve_assertion_catalog,
)
from skfd.authoring.ids import (
    AssertionCatalogId,
    AssertionProfileId,
    AssertionSemanticId,
)
from skfd.authoring.judgment import PrimitiveRuleDecl

from logic.prop.calculus import MP
from logic.prop.rules import MP_ASSERTION

from .axioms import AX5_SIGNATURE
from .calculus import GEN

GEN_ASSERTION = signature_from_primitive_rule(
    GEN,
    assertion_id=AssertionSemanticId("metamath-logic/fol#assertion:ax-gen"),
    canonical_label="ax-gen",
)

FOL_CORE_PROFILE = AssertionProfileId("metamath-logic/fol#profile:core")
ASSERTION_CATALOG = resolve_assertion_catalog(
    AssertionCatalogSpec(
        id=AssertionCatalogId("metamath-logic/fol#catalog:semantic"),
        assertions=(MP_ASSERTION, GEN_ASSERTION, AX5_SIGNATURE),
        profiles=(
            AssertionProfileSpec(
                id=FOL_CORE_PROFILE,
                allowed=(MP_ASSERTION.id, GEN_ASSERTION.id, AX5_SIGNATURE.id),
            ),
        ),
    )
)

RULES: Mapping[str, PrimitiveRuleDecl] = {
    "ax-mp": MP,
    "ax-gen": GEN,
}

__all__ = [
    "ASSERTION_CATALOG",
    "FOL_CORE_PROFILE",
    "GEN_ASSERTION",
    "RULES",
]
