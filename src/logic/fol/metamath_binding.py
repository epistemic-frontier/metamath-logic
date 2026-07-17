"""set.mm-compatible realization of the semantic first-order canary."""

from skfd.authoring.ids import (
    AssertionSemanticId,
    BackendBindingId,
    BackendVocabularyId,
)
from skfd.authoring.language import LanguageRequirement
from skfd.authoring.metamath_language import (
    ArgumentPart,
    FormationBinding,
    LiteralPart,
    MetamathLanguageBinding,
    MetamathLanguageRequirement,
    SortTypecodeBinding,
    TokenRef,
    resolve_metamath_language,
)

from logic.prop.metamath_binding import SETMM_PROP_BINDING

from .language import ALL, LANGUAGE, SETVAR

FOL_VOCABULARY = BackendVocabularyId("metamath-logic/fol#vocabulary:setmm")
SETMM_FOL_BINDING_ID = BackendBindingId("metamath-logic/fol#binding:setmm")
SETMM_FORALL_TOKEN = TokenRef(FOL_VOCABULARY, "A.")
SETMM_SETVAR_TOKEN = TokenRef(FOL_VOCABULARY, "setvar")

SETMM_FOL_BINDING_SPEC = MetamathLanguageBinding(
    id=SETMM_FOL_BINDING_ID,
    language=LanguageRequirement(
        id=LANGUAGE.id,
        semantic_digest=LANGUAGE.semantic_digest,
    ),
    foundation=SETMM_PROP_BINDING.foundation,
    extends=(
        MetamathLanguageRequirement(
            id=SETMM_PROP_BINDING.id,
            digest=SETMM_PROP_BINDING.digest,
        ),
    ),
    formations=(
        FormationBinding(
            constructor=ALL,
            syntax_assertion=AssertionSemanticId("metamath-logic/fol#formation:wal"),
            syntax_assertion_label="wal",
            template=(
                LiteralPart(SETMM_FORALL_TOKEN),
                ArgumentPart(0),
                ArgumentPart(1),
            ),
        ),
    ),
    sort_typecodes=(
        SortTypecodeBinding(
            sort=SETVAR,
            typecode=SETMM_SETVAR_TOKEN,
        ),
    ),
)

SETMM_FOL_BINDING = resolve_metamath_language(
    SETMM_FOL_BINDING_SPEC,
    LANGUAGE,
    {SETMM_PROP_BINDING.id: SETMM_PROP_BINDING},
)

SETMM_WAL_LABEL = SETMM_FOL_BINDING.formations[ALL].syntax_assertion_label

__all__ = [
    "FOL_VOCABULARY",
    "SETMM_FOL_BINDING",
    "SETMM_FOL_BINDING_ID",
    "SETMM_FOL_BINDING_SPEC",
    "SETMM_FORALL_TOKEN",
    "SETMM_SETVAR_TOKEN",
    "SETMM_WAL_LABEL",
]
