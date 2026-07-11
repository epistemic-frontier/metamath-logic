from __future__ import annotations

from collections.abc import Mapping, Sequence
from typing import TYPE_CHECKING, cast

from skfd.authoring.dsl import Expr, compile_wff
from skfd.authoring.formula import Wff
from skfd.authoring.typing import HypothesisAny, PreludeShapeError, PreludeTypingError

from logic.propositional.hilbert._builtins import PropositionalBuiltins, try_parse_imp

if TYPE_CHECKING:
    from . import PredicateSystem


def _compile(system: PredicateSystem, expr: Expr, *, ctx: str = "compile") -> Wff:
    env, registry = system.author_env()
    try:
        return compile_wff(expr, env=env, registry=registry)
    except Exception as e:
        raise PreludeTypingError(f"{ctx}: {e}") from e


def _compile_axioms(system: PredicateSystem) -> Mapping[str, Wff]:
    return {
        key: _compile(system, expr, ctx=f"compile_axiom[{key}]")
        for key, expr in system.axioms.items()
    }


def _apply(
    system: PredicateSystem,
    rule: str,
    hyps: Sequence[HypothesisAny],
    *,
    ctx: str,
) -> Wff:
    if rule != "mp" or len(hyps) != 2:
        raise PreludeTypingError(f"{ctx}: unsupported predicate rule {rule!r}")
    antecedent, implication = hyps
    shape = try_parse_imp(cast(PropositionalBuiltins, system.builtins), implication.body.tokens)
    if shape is None:
        raise PreludeShapeError(f"{ctx}: expected token shape '( phi -> psi )'")
    if antecedent.body.tokens != shape.phi:
        raise PreludeShapeError(f"{ctx}: antecedent mismatch (token-level)")
    return Wff("wff", shape.psi)
