"""Unicode-first notation for the semantic propositional language."""

from prelude.notation import PRELUDE_UNICODE_NOTATION
from skfd.authoring.ids import NotationId
from skfd.authoring.language import LanguageRequirement
from skfd.authoring.notation import (
    CallForm,
    InfixForm,
    NotationDecl,
    NotationRequirement,
    NotationSpec,
    resolve_notation,
)

from .language import AND2, AND3, LANGUAGE

PROP_UNICODE_NOTATION_ID = NotationId("metamath-logic/prop#notation:unicode")

PROP_UNICODE_NOTATION_SPEC = NotationSpec(
    id=PROP_UNICODE_NOTATION_ID,
    language=LanguageRequirement(
        id=LANGUAGE.id,
        semantic_digest=LANGUAGE.semantic_digest,
    ),
    extends=(
        NotationRequirement(
            id=PRELUDE_UNICODE_NOTATION.id,
            digest=PRELUDE_UNICODE_NOTATION.digest,
        ),
    ),
    declarations=(
        NotationDecl(
            constructor=AND2,
            form=InfixForm(token="∧", precedence=25, associativity="left"),
            aliases=("/\\", "&"),
        ),
        NotationDecl(
            constructor=AND3,
            form=CallForm(token="and3"),
        ),
    ),
)

PROP_UNICODE_NOTATION = resolve_notation(
    PROP_UNICODE_NOTATION_SPEC,
    LANGUAGE,
    {PRELUDE_UNICODE_NOTATION.id: PRELUDE_UNICODE_NOTATION},
)

__all__ = [
    "PROP_UNICODE_NOTATION",
    "PROP_UNICODE_NOTATION_ID",
    "PROP_UNICODE_NOTATION_SPEC",
]
