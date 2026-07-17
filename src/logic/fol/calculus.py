"""First-order Hilbert calculus extending propositional modus ponens."""

from skfd.authoring.ids import CalculusId, OwnerId, RuleId
from skfd.authoring.judgment import (
    CalculusSpec,
    Judgment,
    JudgmentKindDecl,
    PrimitiveRuleDecl,
    resolve_calculus,
)
from skfd.authoring.language import LanguageRequirement
from skfd.authoring.term import VariableRef

from logic.prop.calculus import MP, PROVABLE
from logic.prop.language import WFF, WFF_VARIABLE

from .language import LANGUAGE, SETVAR_VARIABLE, All

GENERALIZATION = RuleId("metamath-logic/fol#rule:generalization")
FOL_CALCULUS_ID = CalculusId("metamath-logic/fol#calculus:hilbert")

_GEN_OWNER = OwnerId(str(GENERALIZATION))
_X_REF = VariableRef("schema", _GEN_OWNER, "x", SETVAR_VARIABLE)
_PHI_REF = VariableRef("schema", _GEN_OWNER, "phi", WFF_VARIABLE)
_X = LANGUAGE.variable(_X_REF)
_PHI = LANGUAGE.variable(_PHI_REF)

GEN = PrimitiveRuleDecl(
    id=GENERALIZATION,
    schema_variables=(_PHI_REF, _X_REF),
    premises=(Judgment(PROVABLE, (_PHI,)),),
    conclusion=Judgment(PROVABLE, (All(_X, _PHI),)),
)

CALCULUS_SPEC = CalculusSpec(
    id=FOL_CALCULUS_ID,
    language=LanguageRequirement(
        id=LANGUAGE.id,
        semantic_digest=LANGUAGE.semantic_digest,
    ),
    judgments=(JudgmentKindDecl(id=PROVABLE, arguments=(WFF,)),),
    rules=(MP, GEN),
)

CALCULUS = resolve_calculus(CALCULUS_SPEC, LANGUAGE)

__all__ = [
    "CALCULUS",
    "CALCULUS_SPEC",
    "FOL_CALCULUS_ID",
    "GEN",
    "GENERALIZATION",
]
