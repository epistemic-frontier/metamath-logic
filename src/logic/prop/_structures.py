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
# The /\\ token is already registered for arity 2 above.  The ternary form
# uses the same set.mm token, so we register the arity-3 constructor and a
# combined builder that dispatches on the number of arguments.

from skfd.authoring.dsl import DEFAULT_BUILDERS, DEFAULT_REQUIRE, Constructor, require  # noqa: E402

_ternary_and_ctor = Constructor("/\\", 3)

# Temporarily pop the binary entry from _by_name so that require() for the
# ternary form does not raise "duplicate constructor name".
_binary_and_spec = DEFAULT_REQUIRE._by_name.pop("/\\", None)

require(
    _ternary_and_ctor,
    in_sorts=(WFF, WFF, WFF),
    out_sort=WFF,
    registry=DEFAULT_REQUIRE,
    precedence=25,
    assoc="left",
)

# Restore the binary spec as the canonical _by_name entry.
if _binary_and_spec is not None:
    DEFAULT_REQUIRE._by_name["/\\"] = _binary_and_spec
else:
    DEFAULT_REQUIRE._by_name.pop("/\\", None)

# Replace the single-arity builder with a combined one that handles both
# binary (2 args) and ternary (3 args).
_binary_and_builder = DEFAULT_BUILDERS.get("/\\")


def _and_combined(
    b: PropositionalBuiltins,
    args: Sequence[Wff],
) -> Wff:
    r"""Combined builder for /\\ (binary arity 2 + ternary arity 3)."""
    if len(args) == 2:
        return _binary_and_builder(b, args)
    return w3a(b, args[0], args[1], args[2])


DEFAULT_BUILDERS.register("/\\", _and_combined)

for _alias in ("∧", "&"):
    _binary_alias_spec = DEFAULT_REQUIRE._by_name.pop(_alias, None)
    _ternary_alias_ctor = Constructor(_alias, 3)
    require(
        _ternary_alias_ctor,
        in_sorts=(WFF, WFF, WFF),
        out_sort=WFF,
        registry=DEFAULT_REQUIRE,
        precedence=25,
        assoc="left",
    )
    if _binary_alias_spec is not None:
        DEFAULT_REQUIRE._by_name[_alias] = _binary_alias_spec
    DEFAULT_BUILDERS.register(_alias, _and_combined)


And3 = _ternary_and_ctor


# ---------------------------------------------------------------------------
# Ternary disjunction (arity 3): ( φ \/ ψ \/ χ )
# ---------------------------------------------------------------------------
# Same pattern as ternary conjunction above: register an arity-3 constructor
# and a combined builder that dispatches on the number of arguments.

_ternary_or_ctor = Constructor(r"\/", 3)

# Temporarily pop the binary entry from _by_name so that require() for the
# ternary form does not raise "duplicate constructor name".
_binary_or_spec = DEFAULT_REQUIRE._by_name.pop(r"\/", None)

require(
    _ternary_or_ctor,
    in_sorts=(WFF, WFF, WFF),
    out_sort=WFF,
    registry=DEFAULT_REQUIRE,
    precedence=24,
    assoc="left",
)

# Restore the binary spec as the canonical _by_name entry.
if _binary_or_spec is not None:
    DEFAULT_REQUIRE._by_name[r"\/"] = _binary_or_spec
else:
    DEFAULT_REQUIRE._by_name.pop(r"\/", None)

# Replace the single-arity builder with a combined one that handles both
# binary (2 args) and ternary (3 args).
_binary_or_builder = DEFAULT_BUILDERS.get(r"\/")


def _or_combined(
    b: PropositionalBuiltins,
    args: Sequence[Wff],
) -> Wff:
    r"""Combined builder for \/ (binary arity 2 + ternary arity 3)."""
    if len(args) == 2:
        return _binary_or_builder(b, args)
    return w3o(b, args[0], args[1], args[2])


DEFAULT_BUILDERS.register(r"\/", _or_combined)

for _alias in ("∨", "|"):
    _binary_alias_spec = DEFAULT_REQUIRE._by_name.pop(_alias, None)
    _ternary_alias_ctor = Constructor(_alias, 3)
    require(
        _ternary_alias_ctor,
        in_sorts=(WFF, WFF, WFF),
        out_sort=WFF,
        registry=DEFAULT_REQUIRE,
        precedence=24,
        assoc="left",
    )
    if _binary_alias_spec is not None:
        DEFAULT_REQUIRE._by_name[_alias] = _binary_alias_spec
    DEFAULT_BUILDERS.register(_alias, _or_combined)


Or3 = _ternary_or_ctor

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
