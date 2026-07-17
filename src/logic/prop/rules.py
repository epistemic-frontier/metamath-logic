"""Public propositional inference-rule registry."""

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

from .calculus import MP

MP_ASSERTION = signature_from_primitive_rule(
    MP,
    assertion_id=AssertionSemanticId("metamath-logic/prop#assertion:ax-mp"),
    canonical_label="ax-mp",
)

PROP_CORE_PROFILE = AssertionProfileId("metamath-logic/prop#profile:core")
ASSERTION_CATALOG = resolve_assertion_catalog(
    AssertionCatalogSpec(
        id=AssertionCatalogId("metamath-logic/prop#catalog:semantic"),
        assertions=(MP_ASSERTION,),
        profiles=(
            AssertionProfileSpec(
                id=PROP_CORE_PROFILE,
                allowed=(MP_ASSERTION.id,),
            ),
        ),
    )
)

RULES: Mapping[str, PrimitiveRuleDecl] = {"ax-mp": MP}

__all__ = [
    "ASSERTION_CATALOG",
    "MP_ASSERTION",
    "PROP_CORE_PROFILE",
    "RULES",
]
