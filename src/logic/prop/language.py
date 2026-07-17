"""Semantic propositional language, independent of legacy authoring registries."""

from __future__ import annotations

from prelude.language import IMP, NOT, WFF, WFF_VARIABLE, Imp, Not
from prelude.language import LANGUAGE as PRELUDE_LANGUAGE
from skfd.authoring.ids import ConstructorId, LanguageId
from skfd.authoring.language import (
    ConstructorDecl,
    LanguageRequirement,
    LanguageSpec,
    resolve_language,
)
from skfd.authoring.term import App, Term

PROP_LANGUAGE_ID = LanguageId("metamath-logic/prop#language:propositional")

AND2 = ConstructorId("metamath-logic/prop#constructor:and2")
AND3 = ConstructorId("metamath-logic/prop#constructor:and3")

LANGUAGE_SPEC = LanguageSpec(
    id=PROP_LANGUAGE_ID,
    extends=(
        LanguageRequirement(
            id=PRELUDE_LANGUAGE.id,
            semantic_digest=PRELUDE_LANGUAGE.semantic_digest,
        ),
    ),
    constructors=(
        ConstructorDecl(id=AND2, inputs=(WFF, WFF), output=WFF),
        ConstructorDecl(id=AND3, inputs=(WFF, WFF, WFF), output=WFF),
    ),
)

LANGUAGE = resolve_language(
    LANGUAGE_SPEC,
    {PRELUDE_LANGUAGE.id: PRELUDE_LANGUAGE},
)


def And2(left: Term, right: Term) -> App:
    """Construct binary semantic conjunction."""
    return LANGUAGE.apply(AND2, (left, right))


def And3(first: Term, second: Term, third: Term) -> App:
    """Construct ternary semantic conjunction with its own stable identity."""
    return LANGUAGE.apply(AND3, (first, second, third))


__all__ = [
    "AND2",
    "AND3",
    "IMP",
    "LANGUAGE",
    "LANGUAGE_SPEC",
    "NOT",
    "PROP_LANGUAGE_ID",
    "WFF",
    "WFF_VARIABLE",
    "And2",
    "And3",
    "Imp",
    "Not",
]
