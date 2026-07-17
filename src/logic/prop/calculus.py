"""Judgment vocabulary for the propositional Hilbert calculus."""

from skfd.authoring.ids import CalculusId, JudgmentKindId
from skfd.authoring.judgment import CalculusSpec, JudgmentKindDecl, resolve_calculus
from skfd.authoring.language import LanguageRequirement

from .language import LANGUAGE, WFF

PROVABLE = JudgmentKindId("metamath-logic/prop#judgment:provable")
PROP_CALCULUS_ID = CalculusId("metamath-logic/prop#calculus:hilbert")

CALCULUS_SPEC = CalculusSpec(
    id=PROP_CALCULUS_ID,
    language=LanguageRequirement(
        id=LANGUAGE.id,
        semantic_digest=LANGUAGE.semantic_digest,
    ),
    judgments=(JudgmentKindDecl(id=PROVABLE, arguments=(WFF,)),),
)

CALCULUS = resolve_calculus(CALCULUS_SPEC, LANGUAGE)

__all__ = ["CALCULUS", "CALCULUS_SPEC", "PROP_CALCULUS_ID", "PROVABLE"]
