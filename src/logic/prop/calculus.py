"""Judgments and primitive rules for the propositional Hilbert calculus."""

from skfd.authoring.ids import CalculusId, JudgmentKindId, OwnerId, RuleId
from skfd.authoring.judgment import (
    CalculusSpec,
    Judgment,
    JudgmentKindDecl,
    PrimitiveRuleDecl,
    resolve_calculus,
)
from skfd.authoring.language import LanguageRequirement
from skfd.authoring.term import VariableRef

from .language import LANGUAGE, WFF, WFF_VARIABLE, Imp

PROVABLE = JudgmentKindId("metamath-logic/prop#judgment:provable")
MODUS_PONENS = RuleId("metamath-logic/prop#rule:modus-ponens")
PROP_CALCULUS_ID = CalculusId("metamath-logic/prop#calculus:hilbert")

_MP_OWNER = OwnerId(str(MODUS_PONENS))
_PHI_REF = VariableRef("schema", _MP_OWNER, "phi", WFF_VARIABLE)
_PSI_REF = VariableRef("schema", _MP_OWNER, "psi", WFF_VARIABLE)
_PHI = LANGUAGE.variable(_PHI_REF)
_PSI = LANGUAGE.variable(_PSI_REF)

MP = PrimitiveRuleDecl(
    id=MODUS_PONENS,
    schema_variables=(_PHI_REF, _PSI_REF),
    premises=(
        Judgment(PROVABLE, (_PHI,)),
        Judgment(PROVABLE, (Imp(_PHI, _PSI),)),
    ),
    conclusion=Judgment(PROVABLE, (_PSI,)),
)

CALCULUS_SPEC = CalculusSpec(
    id=PROP_CALCULUS_ID,
    language=LanguageRequirement(
        id=LANGUAGE.id,
        semantic_digest=LANGUAGE.semantic_digest,
    ),
    judgments=(JudgmentKindDecl(id=PROVABLE, arguments=(WFF,)),),
    rules=(MP,),
)

CALCULUS = resolve_calculus(CALCULUS_SPEC, LANGUAGE)

__all__ = [
    "CALCULUS",
    "CALCULUS_SPEC",
    "MODUS_PONENS",
    "MP",
    "PROP_CALCULUS_ID",
    "PROVABLE",
]
