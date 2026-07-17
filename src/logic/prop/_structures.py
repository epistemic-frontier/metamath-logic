"""Author-facing language skeleton for the Hilbert propositional system.

This module declares:
- formal variables (φ, ψ, χ, ...)
- core constructors with arity (→, ¬, ∧)
- require(...) declarations for signatures (wff discipline)

No Builtins or SymbolInterner appear here; those are injected at system
construction time by logic.prop.system.System.
"""

from __future__ import annotations

from collections.abc import Sequence

from skfd.authoring.dsl import Var, symbol
from skfd.authoring.formula import Wff
from skfd.authoring.legacy_metamath import legacy_symbol_spec
from skfd.authoring.typing import WFF

from ._builtins import (
    PropositionalBuiltins,
    imp,
    w3a,
    w3o,
    wa,
    wb,
    wcad,
    wfal,
    whad,
    wif,
    wn,
    wnan,
    wnor,
    wo,
    wtru,
    wxo,
)
from .language import AND2, AND3, LANGUAGE
from .language import WFF as SEMANTIC_WFF
from .metamath_binding import SETMM_PROP_BINDING
from .notation import PROP_UNICODE_NOTATION

phi = Var("φ")
psi = Var("ψ")
chi = Var("χ")
th = Var("θ")
ta = Var("τ")
et = Var("η")
ze = Var("ζ")

si = Var("σ")
rh = Var("ρ")
mu = Var("μ")
la = Var("λ")
ka = Var("κ")


@symbol("->", 2, (WFF, WFF), WFF, op="rshift", precedence=20, assoc="right", aliases=["→", "⇒"])
def Imp(b: PropositionalBuiltins, args: Sequence[Wff]) -> Wff:
    return imp(b, args[0], args[1])


@symbol("-.", 1, (WFF,), WFF, op="invert", precedence=30, assoc="right", aliases=["¬", "~"])
def Not(b: PropositionalBuiltins, args: Sequence[Wff]) -> Wff:
    return wn(b, args[0])


_AND2_LEGACY = legacy_symbol_spec(
    SETMM_PROP_BINDING,
    PROP_UNICODE_NOTATION,
    AND2,
    legacy_sorts={SEMANTIC_WFF: WFF},
)


@symbol(
    _AND2_LEGACY.name,
    _AND2_LEGACY.arity,
    _AND2_LEGACY.in_sorts,
    _AND2_LEGACY.out_sort,
    op="and",
    precedence=_AND2_LEGACY.precedence,
    assoc=_AND2_LEGACY.associativity,
    aliases=_AND2_LEGACY.aliases,
)
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


@symbol("-/\\", 2, (WFF, WFF), WFF, precedence=30, assoc="right", aliases=["⊼"])
def Nand(b: PropositionalBuiltins, args: Sequence[Wff]) -> Wff:
    return wnan(b, args[0], args[1])


@symbol("-\\/", 2, (WFF, WFF), WFF, precedence=30, assoc="right", aliases=["⊽"])
def Nor(b: PropositionalBuiltins, args: Sequence[Wff]) -> Wff:
    return wnor(b, args[0], args[1])


@symbol("cadd", 3, (WFF, WFF, WFF), WFF, precedence=30, aliases=[])
def Cadd(b: PropositionalBuiltins, args: Sequence[Wff]) -> Wff:
    return wcad(b, args[0], args[1], args[2])


@symbol("\\/_", 2, (WFF, WFF), WFF, precedence=24, assoc="left", aliases=["⊻"])
def Xor(b: PropositionalBuiltins, args: Sequence[Wff]) -> Wff:
    return wxo(b, args[0], args[1])


@symbol("hadd", 3, (WFF, WFF, WFF), WFF, precedence=30, aliases=[])
def Hadd(b: PropositionalBuiltins, args: Sequence[Wff]) -> Wff:
    return whad(b, args[0], args[1], args[2])


@symbol("if-", 3, (WFF, WFF, WFF), WFF, precedence=30, aliases=[])
def If(b: PropositionalBuiltins, args: Sequence[Wff]) -> Wff:
    return wif(b, args[0], args[1], args[2])


# ---------------------------------------------------------------------------
# Ternary conjunction (arity 3): ( φ /\ ψ /\ χ )
# ---------------------------------------------------------------------------
_AND3_DECL = LANGUAGE.constructors[AND3]


@symbol(
    _AND2_LEGACY.name,
    len(_AND3_DECL.inputs),
    tuple(WFF for _ in _AND3_DECL.inputs),
    WFF,
    precedence=_AND2_LEGACY.precedence,
    assoc=_AND2_LEGACY.associativity,
    aliases=_AND2_LEGACY.aliases,
)
def And3(b: PropositionalBuiltins, args: Sequence[Wff]) -> Wff:
    return w3a(b, args[0], args[1], args[2])


# ---------------------------------------------------------------------------
# Ternary disjunction (arity 3): ( φ \/ ψ \/ χ )
# ---------------------------------------------------------------------------
@symbol(r"\/", 3, (WFF, WFF, WFF), WFF, precedence=24, assoc="left", aliases=["∨", "|"])
def Or3(b: PropositionalBuiltins, args: Sequence[Wff]) -> Wff:
    return w3o(b, args[0], args[1], args[2])

__all__ = [
    "phi",
    "psi",
    "chi",
    "th",
    "ta",
    "et",
    "ze",
    "si",
    "rh",
    "mu",
    "la",
    "ka",
    "Imp",
    "Not",
    "And",
    "Or",
    "Iff",
    "Verum",
    "Falsum",
    "Nand",
    "Nor",
    "Cadd",
    "Xor",
    "Hadd",
    "If",
    "And3",
    "Or3",
]
