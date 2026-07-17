"""Unicode-first notation for the semantic first-order language."""

from skfd.authoring.ids import NotationId
from skfd.authoring.language import LanguageRequirement
from skfd.authoring.notation import (
    BinderForm,
    NotationDecl,
    NotationRequirement,
    NotationSpec,
    resolve_notation,
)

from logic.prop.notation import PROP_UNICODE_NOTATION

from .language import ALL, LANGUAGE

FOL_UNICODE_NOTATION_ID = NotationId("metamath-logic/fol#notation:unicode")

FOL_UNICODE_NOTATION_SPEC = NotationSpec(
    id=FOL_UNICODE_NOTATION_ID,
    language=LanguageRequirement(
        id=LANGUAGE.id,
        semantic_digest=LANGUAGE.semantic_digest,
    ),
    extends=(
        NotationRequirement(
            id=PROP_UNICODE_NOTATION.id,
            digest=PROP_UNICODE_NOTATION.digest,
        ),
    ),
    declarations=(
        NotationDecl(
            constructor=ALL,
            form=BinderForm(token="∀", precedence=0),
            aliases=("forall",),
        ),
    ),
)

FOL_UNICODE_NOTATION = resolve_notation(
    FOL_UNICODE_NOTATION_SPEC,
    LANGUAGE,
    {PROP_UNICODE_NOTATION.id: PROP_UNICODE_NOTATION},
)

__all__ = [
    "FOL_UNICODE_NOTATION",
    "FOL_UNICODE_NOTATION_ID",
    "FOL_UNICODE_NOTATION_SPEC",
]
