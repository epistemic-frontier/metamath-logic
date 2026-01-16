# logic/propositional/hilbert/definitions.py
"""Author-facing definitional macros for the Hilbert propositional system.

Definitions in this module are Expr-level macros:
- They introduce new names for patterns built from the core constructors.
- They must expand back into the underlying language (→, ¬, ∧).
- They do not add new axioms or inference rules.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping
from dataclasses import dataclass

from skfd.authoring.dsl import Expr
from skfd.authoring.typing import PreludeTypingError

from ._structures import Imp, Not


@dataclass(frozen=True)
class Definition:
    """A definitional macro over Expr terms.

    Attributes:
    - name: human-readable name (e.g. 'Or').
    - arity: number of arguments.
    - body: function mapping Expr arguments to an Expr.
    - doc: optional documentation string describing the macro.
    """

    name: str
    arity: int
    body: Callable[..., Expr]
    doc: str | None = None

    def apply(self, *args: Expr) -> Expr:
        if len(args) != self.arity:
            raise PreludeTypingError(
                f"definition {self.name!r}: expects {self.arity} args, got {len(args)}"
            )
        return self.body(*args)

    def expand(self, *args: Expr) -> Expr:
        """Expand the definition into core language Expr."""
        return self.apply(*args)


# Or(φ, ψ) := ¬φ → ψ
Or = Definition(
    name="Or",
    arity=2,
    body=lambda a, b: Imp(Not(a), b),
    doc=(
        "Disjunction: Or(φ, ψ) := ¬φ -> ψ.\n"
        "Formula: Or(φ, ψ) = (¬φ -> ψ)\n"
        "Reading: Either φ is false or ψ holds."
    ),
)


DEFINITIONS: Mapping[str, Definition] = {
    "Or": Or,
}

__all__ = ["Definition", "Or", "DEFINITIONS"]
