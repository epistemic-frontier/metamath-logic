"""First-order Hilbert system kernel."""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from typing import Any

from skfd.authoring.dsl import DEFAULT_BUILDERS, CompileEnv, Expr, RequireRegistry
from skfd.authoring.formula import Wff
from skfd.authoring.typing import HypothesisAny
from skfd.core.symbols import SymbolInterner
from skfd.names import NameResolver

from ._builtins import PredicateBuiltins
from ._internal import _apply as _apply_impl
from ._internal import _compile as _compile_impl
from ._internal import _compile_axioms as _compile_axioms_impl
from .axioms import make_axioms


@dataclass(frozen=True)
class PredicateSystem:
    interner: SymbolInterner
    names: NameResolver
    builtins: PredicateBuiltins
    axioms: Mapping[str, Expr]

    @classmethod
    def make(
        cls,
        *,
        interner: SymbolInterner,
        names: NameResolver,
        origin_ref: Any = None,
    ) -> PredicateSystem:
        return cls(
            interner=interner,
            names=names,
            builtins=PredicateBuiltins.ensure(interner, origin_ref=origin_ref),
            axioms=make_axioms(),
        )

    def author_env(
        self,
        *,
        origin_module_id: str = "logic.fol",
        origin_ref: Any = None,
        registry: RequireRegistry | None = None,
    ) -> tuple[CompileEnv, RequireRegistry]:
        if registry is None:
            from skfd.authoring.dsl import DEFAULT_REQUIRE as registry_default

            registry = registry_default
        return (
            CompileEnv(
                interner=self.interner,
                names=self.names,
                builtins=self.builtins,
                ctor_builders=DEFAULT_BUILDERS.all(),
                origin_module_id=origin_module_id,
                origin_ref=origin_ref,
            ),
            registry,
        )

    def compile(self, expr: Expr, *, ctx: str = "compile") -> Wff:
        return _compile_impl(self, expr, ctx=ctx)

    def compile_axioms(self) -> Mapping[str, Wff]:
        return _compile_axioms_impl(self)

    def apply(self, rule: str, hyps: Sequence[HypothesisAny], *, ctx: str) -> Wff:
        return _apply_impl(self, rule, hyps, ctx=ctx)


# Predicate axiom labels are canonical set.mm labels throughout the system.
SETMM_TO_PREDICATE_AXIOMS: Mapping[str, str] = {
    f"ax-{number}": f"ax-{number}" for number in range(4, 14)
}


def make(*, interner: SymbolInterner, origin_ref: Any = None) -> PredicateSystem:
    return PredicateSystem.make(
        interner=interner,
        names=NameResolver(),
        origin_ref=origin_ref,
    )


__all__ = [
    "PredicateSystem",
    "make",
    "SETMM_TO_PREDICATE_AXIOMS",
    "make_axioms",
]
