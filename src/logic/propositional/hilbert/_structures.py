# logic/propositional/hilbert/_structures.py
"""Author-facing language skeleton for the Hilbert propositional system.

This module declares:
- formal variables (φ, ψ, χ, ...)
- core constructors with arity (→, ¬, ∧)
- require(...) declarations for signatures (wff discipline)

No Builtins or SymbolInterner appear here; those are injected at system
construction time by logic.propositional.hilbert.System.
"""

from __future__ import annotations

from collections.abc import Sequence

from skfd.authoring.dsl import Var, symbol
from skfd.authoring.formula import Wff
from skfd.authoring.typing import WFF

from ._builtins import PropositionalBuiltins, imp, wa, wb, wfal, wn, wo, wtru

phi = Var("φ")
psi = Var("ψ")
chi = Var("χ")
th = Var("θ")
ta = Var("τ")


@symbol("->", 2, (WFF, WFF), WFF, op="rshift", precedence=20, assoc="right", aliases=["→", "⇒"])
def Imp(b: PropositionalBuiltins, args: Sequence[Wff]) -> Wff:
    return imp(b, args[0], args[1])


@symbol("-.", 1, (WFF,), WFF, op="invert", precedence=30, assoc="right", aliases=["¬", "~"])
def Not(b: PropositionalBuiltins, args: Sequence[Wff]) -> Wff:
    return wn(b, args[0])


@symbol("/\\", 2, (WFF, WFF), WFF, op="and", precedence=25, assoc="left", aliases=["∧", "&"])
def And(b: PropositionalBuiltins, args: Sequence[Wff]) -> Wff:
    return wa(b, args[0], args[1])


@symbol("\\/", 2, (WFF, WFF), WFF, op="or", precedence=24, assoc="left", aliases=["∨", "|"])
def Or(b: PropositionalBuiltins, args: Sequence[Wff]) -> Wff:
    return wo(b, args[0], args[1])


@symbol("<->", 2, (WFF, WFF), WFF, precedence=10, assoc="right", aliases=["↔"])
def Iff(b: PropositionalBuiltins, args: Sequence[Wff]) -> Wff:
    return wb(b, args[0], args[1])


@symbol("T.", 0, (), WFF, aliases=["⊤"])
def Verum(b: PropositionalBuiltins, args: Sequence[Wff]) -> Wff:
    return wtru(b)


@symbol("F.", 0, (), WFF, aliases=["⊥"])
def Falsum(b: PropositionalBuiltins, args: Sequence[Wff]) -> Wff:
    return wfal(b)


__all__ = [
    "phi",
    "psi",
    "chi",
    "th",
    "ta",
    "Imp",
    "Not",
    "And",
    "Or",
    "Iff",
    "Verum",
    "Falsum",
]
