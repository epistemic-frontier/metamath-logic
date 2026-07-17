"""Semantic first-order language canary with explicit set variables and binding."""

from __future__ import annotations

from skfd.authoring.errors import AuthoringSemanticError
from skfd.authoring.ids import ConstructorId, LanguageId, SortId, VariableKindId
from skfd.authoring.language import (
    BinderDecl,
    ConstructorDecl,
    LanguageRequirement,
    LanguageSpec,
    SortDecl,
    VariableKindDecl,
    resolve_language,
)
from skfd.authoring.term import App, Term, Var, VariableRef

from logic.prop.language import LANGUAGE as PROP_LANGUAGE
from logic.prop.language import WFF

FOL_LANGUAGE_ID = LanguageId("metamath-logic/fol#language:first-order")
SETVAR = SortId("metamath-logic/fol#sort:setvar")
SETVAR_VARIABLE = VariableKindId("metamath-logic/fol#variable-kind:setvar")
ALL = ConstructorId("metamath-logic/fol#constructor:all")

LANGUAGE_SPEC = LanguageSpec(
    id=FOL_LANGUAGE_ID,
    extends=(
        LanguageRequirement(
            id=PROP_LANGUAGE.id,
            semantic_digest=PROP_LANGUAGE.semantic_digest,
        ),
    ),
    sorts=(SortDecl(id=SETVAR),),
    variable_kinds=(VariableKindDecl(id=SETVAR_VARIABLE, sort=SETVAR),),
    constructors=(ConstructorDecl(id=ALL, inputs=(SETVAR, WFF), output=WFF),),
    binders=(
        BinderDecl(
            constructor=ALL,
            variable_argument=0,
            scoped_arguments=(1,),
        ),
    ),
)

LANGUAGE = resolve_language(
    LANGUAGE_SPEC,
    {PROP_LANGUAGE.id: PROP_LANGUAGE},
)


def SetVar(variable: VariableRef) -> Var:
    """Construct a checked semantic set variable."""
    if variable.kind != SETVAR_VARIABLE:
        raise AuthoringSemanticError(f"expected set-variable kind, got {variable.kind}")
    return LANGUAGE.variable(variable)


def All(variable: Term, body: Term) -> App:
    """Construct universal quantification with an explicit binder contract."""
    return LANGUAGE.apply(ALL, (variable, body))


__all__ = [
    "ALL",
    "FOL_LANGUAGE_ID",
    "LANGUAGE",
    "LANGUAGE_SPEC",
    "SETVAR",
    "SETVAR_VARIABLE",
    "All",
    "SetVar",
]
