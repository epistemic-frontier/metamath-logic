from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from typing import Any

from prelude.formula import Builtins
from skfd.authoring.dsl import CompileEnv, DEFAULT_BUILDERS, RequireRegistry, compile_wff
from skfd.authoring.typing import PreludeTypingError
from skfd.core.symbols import SymbolInterner
from skfd.names import NameResolver

from ._structures import All
from .axioms import make_axioms


# Deprecated: _predicate_builders
# Builders are now registered via @logic_symbol in _structures.py and logic.propositional.hilbert._structures


@dataclass(frozen=True)
class PredicateSystem:
    interner: SymbolInterner
    names: NameResolver
    builtins: Builtins
    axioms: Mapping[str, Any]

    @classmethod
    def make(
        cls,
        *,
        interner: SymbolInterner,
        names: NameResolver,
        origin_ref: Any = None,
    ) -> PredicateSystem:
        b = Builtins.ensure(interner, origin_ref=origin_ref)
        return cls(
            interner=interner,
            names=names,
            builtins=b,
            axioms=make_axioms(),
        )

    def author_env(
        self,
        *,
        origin_module_id: str = "predicate",
        origin_ref: Any = None,
        registry: RequireRegistry | None = None,
    ) -> tuple[CompileEnv, RequireRegistry]:
        if registry is None:
            from skfd.authoring.dsl import DEFAULT_REQUIRE as registry_default
            registry = registry_default
        env = CompileEnv(
            interner=self.interner,
            names=self.names,
            builtins=self.builtins,
            ctor_builders=DEFAULT_BUILDERS.all(),
            origin_module_id=origin_module_id,
            origin_ref=origin_ref,
        )
        return env, registry

    def compile(self, expr: Any, *, ctx: str = "compile") -> Any:
        env, registry = self.author_env()
        try:
            return compile_wff(expr, env=env, registry=registry)
        except Exception as e:
            raise PreludeTypingError(f"{ctx}: {e}") from e

    def compile_axioms(self) -> Mapping[str, Any]:
        return {k: self.compile(v, ctx=f"compile_axiom[{k}]") for k, v in self.axioms.items()}


def make(*, interner: SymbolInterner, origin_ref: Any = None) -> PredicateSystem:
    return PredicateSystem.make(interner=interner, names=NameResolver(), origin_ref=origin_ref)


__all__ = ["PredicateSystem", "make", "All"]
