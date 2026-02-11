# logic/propositional/hilbert/__init__.py
from __future__ import annotations

from collections.abc import Callable, Mapping, Sequence
from dataclasses import dataclass
from typing import Any, TypeAlias

from prelude.formula import Builtins
from skfd.authoring.dsl import CompileEnv, DEFAULT_BUILDERS, Expr, RequireRegistry
from skfd.authoring.formula import Wff
from skfd.authoring.typing import HypothesisAny, RuleApp
from skfd.core.symbols import SymbolInterner
from skfd.names import NameResolver
from skfd.proof import TacticRegistry

from skfd.authoring.rules import RuleBundle
from prelude.hilbert_rules import make_rules
from ._internal import _apply as _apply_impl
from ._internal import _compile as _compile_impl
from ._internal import _compile_axioms as _compile_axioms_impl
from .axioms import SETMM_TO_HILBERT_LABELS as SETMM_TO_HILBERT_AXIOMS

RuleFn: TypeAlias = Callable[..., Wff]


# -----------------------------------------------------------------------------
# Builders for authoring -> token lowering
# -----------------------------------------------------------------------------

# Deprecated: _hilbert_builders
# Builders are now registered via @logic_symbol in _structures.py


# -----------------------------------------------------------------------------
# System
# -----------------------------------------------------------------------------

@dataclass(frozen=True)
class System:
    """Hilbert propositional logic bundle.

    Authoring bridge:
      - author_env(): returns CompileEnv bound to this system
    """
    interner: SymbolInterner
    names: NameResolver
    builtins: Builtins
    rule_app: RuleApp
    rules: Mapping[str, RuleFn]
    axioms: Mapping[str, Expr]

    @classmethod
    def make(
        cls,
        *,
        interner: SymbolInterner,
        names: NameResolver,
        origin_ref: Any = None,
    ) -> System:
        b = Builtins.ensure(interner, origin_ref=origin_ref)

        bundle: RuleBundle = make_rules(b)
        rule_app = RuleApp(sigs=bundle.sigs)

        # You may keep the token-level schema view if you still want it.
        # If you are fully switching to authoring Expr axioms, you can drop this field.
        from .axioms import make_axioms  # authoring Expr axioms

        return cls(
            interner=interner,
            names=names,
            builtins=b,
            rule_app=rule_app,
            rules=bundle.rules,
            axioms=make_axioms(),
        )

    # -------------------------------------------------------------------------
    # Authoring bridge
    # -------------------------------------------------------------------------

    def author_env(
        self,
        *,
        origin_module_id: str = "hilbert",
        origin_ref: Any = None,
        registry: RequireRegistry | None = None,
    ) -> tuple[CompileEnv, RequireRegistry]:
        """Return a CompileEnv + RequireRegistry for authoring compilation.

        - origin_module_id controls where authoring Vars are interned.
        - registry defaults to skfd.authoring.dsl.DEFAULT_REQUIRE if not provided.
        """
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

    def _compile(self, expr: Expr, *, ctx: str = "compile") -> Wff:
        return _compile_impl(self, expr, ctx=ctx)

    def compile(self, expr: Expr, *, ctx: str = "compile") -> Wff:
        return _compile_impl(self, expr, ctx=ctx)

    def compile_axioms(self) -> Mapping[str, Wff]:
        """Compile the author-facing axioms (Expr) into token-level Wff."""
        return _compile_axioms_impl(self)

    # -------------------------------------------------------------------------
    # Typed rule application (optional convenience)
    # -------------------------------------------------------------------------

    def _apply(self, label: str, hyps: Sequence[HypothesisAny], *, ctx: str) -> Wff:
        return _apply_impl(self, label, hyps, ctx=ctx)

    def apply(self, rule: str, hyps: Sequence[HypothesisAny], *, ctx: str) -> Wff:
        return _apply_impl(self, rule, hyps, ctx=ctx)

    def tactics(self) -> TacticRegistry:
        return {}


def make(*, interner: SymbolInterner, origin_ref: Any = None) -> System:
    return System.make(interner=interner, names=NameResolver(), origin_ref=origin_ref)


SETMM_TO_HILBERT_RULES: Mapping[str, str] = {
    "ax-mp": "mp",
}

SETMM_TO_HILBERT: Mapping[str, str] = {
    **SETMM_TO_HILBERT_AXIOMS,
    **SETMM_TO_HILBERT_RULES,
}


__all__ = [
    "System",
    "make",
    "SETMM_TO_HILBERT_AXIOMS",
    "SETMM_TO_HILBERT_RULES",
    "SETMM_TO_HILBERT",
]
