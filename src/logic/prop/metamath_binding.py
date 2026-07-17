"""set.mm-compatible realization of the semantic propositional language."""

from prelude.metamath_binding import (
    SETMM_LPAREN_TOKEN,
    SETMM_PRELUDE_BINDING,
    SETMM_RPAREN_TOKEN,
)
from skfd.authoring.ids import (
    AssertionSemanticId,
    BackendBindingId,
    BackendVocabularyId,
)
from skfd.authoring.language import LanguageRequirement
from skfd.authoring.legacy_replay import LegacyAssertionReplayBinding
from skfd.authoring.metamath_language import (
    ArgumentPart,
    FormationBinding,
    LiteralPart,
    MetamathLanguageBinding,
    MetamathLanguageRequirement,
    TokenRef,
    resolve_metamath_language,
)

from .language import AND2, AND3, LANGUAGE
from .rules import MP_ASSERTION

PROP_VOCABULARY = BackendVocabularyId("metamath-logic/prop#vocabulary:setmm")
SETMM_PROP_BINDING_ID = BackendBindingId("metamath-logic/prop#binding:setmm")


def _token(local_name: str) -> TokenRef:
    return TokenRef(PROP_VOCABULARY, local_name)


SETMM_AND_TOKEN = _token("/\\")


SETMM_PROP_BINDING_SPEC = MetamathLanguageBinding(
    id=SETMM_PROP_BINDING_ID,
    language=LanguageRequirement(
        id=LANGUAGE.id,
        semantic_digest=LANGUAGE.semantic_digest,
    ),
    foundation=SETMM_PRELUDE_BINDING.foundation,
    extends=(
        MetamathLanguageRequirement(
            id=SETMM_PRELUDE_BINDING.id,
            digest=SETMM_PRELUDE_BINDING.digest,
        ),
    ),
    formations=(
        FormationBinding(
            constructor=AND2,
            syntax_assertion=AssertionSemanticId("metamath-logic/prop#formation:wa"),
            syntax_assertion_label="wa",
            template=(
                LiteralPart(SETMM_LPAREN_TOKEN),
                ArgumentPart(0),
                LiteralPart(SETMM_AND_TOKEN),
                ArgumentPart(1),
                LiteralPart(SETMM_RPAREN_TOKEN),
            ),
        ),
        FormationBinding(
            constructor=AND3,
            syntax_assertion=AssertionSemanticId("metamath-logic/prop#formation:w3a"),
            syntax_assertion_label="w3a",
            template=(
                LiteralPart(SETMM_LPAREN_TOKEN),
                ArgumentPart(0),
                LiteralPart(SETMM_AND_TOKEN),
                ArgumentPart(1),
                LiteralPart(SETMM_AND_TOKEN),
                ArgumentPart(2),
                LiteralPart(SETMM_RPAREN_TOKEN),
            ),
        ),
    ),
)

SETMM_PROP_BINDING = resolve_metamath_language(
    SETMM_PROP_BINDING_SPEC,
    LANGUAGE,
    {SETMM_PRELUDE_BINDING.id: SETMM_PRELUDE_BINDING},
)

SETMM_WA_LABEL = SETMM_PROP_BINDING.formations[AND2].syntax_assertion_label
SETMM_W3A_LABEL = SETMM_PROP_BINDING.formations[AND3].syntax_assertion_label
SETMM_MP_REPLAY_BINDING = LegacyAssertionReplayBinding(
    assertion=MP_ASSERTION.id,
    backend_label="ax-mp",
    operation="apply",
    legacy_rule="mp",
)

__all__ = [
    "PROP_VOCABULARY",
    "SETMM_AND_TOKEN",
    "SETMM_MP_REPLAY_BINDING",
    "SETMM_PROP_BINDING",
    "SETMM_PROP_BINDING_ID",
    "SETMM_PROP_BINDING_SPEC",
    "SETMM_W3A_LABEL",
    "SETMM_WA_LABEL",
]
