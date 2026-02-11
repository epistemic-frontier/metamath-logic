from __future__ import annotations

from collections.abc import Mapping, Sequence
from typing import TYPE_CHECKING

from skfd.authoring.dsl import Expr, compile_wff
from skfd.authoring.formula import Wff
from skfd.authoring.typing import HypothesisAny, PreludeTypingError

if TYPE_CHECKING:
    from . import System


def _compile(system: System, expr: Expr, *, ctx: str = "compile") -> Wff:
    env, registry = system.author_env()
    try:
        return compile_wff(expr, env=env, registry=registry)
    except Exception as e:
        raise PreludeTypingError(f"{ctx}: {e}") from e


def _compile_axioms(system: System) -> Mapping[str, Wff]:
    return {k: _compile(system, v, ctx=f"compile_axiom[{k}]") for k, v in system.axioms.items()}


def _apply(system: System, label: str, hyps: Sequence[HypothesisAny], *, ctx: str) -> Wff:
    system.rule_app.check(label, hyps, ctx=ctx)
    fn = system.rules.get(label)
    if fn is None:
        raise PreludeTypingError(f"{ctx}: missing rule implementation for {label!r}")
    return fn(*hyps)
