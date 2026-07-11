"""Stoic logic derivation skeleton.

set.mm range:
    ``Stoic logic non-modal portion (Chrysippus of Soli)`` occupies set.mm
    lines 14280-14552.

Scope:
    This module is reserved for set.mm's derivations of non-modal Stoic logic
    inside the standard propositional Hilbert system:

    - indemonstrables: ``mptnan``, ``mptxor``, ``mtpor``, ``mtpxor``
    - themata: ``stoic1a``, ``stoic1b``, ``stoic2a``, ``stoic2b``,
      ``stoic3``, ``stoic4a``, ``stoic4b``

Boundary:
    These are not a separate proof kernel. They are theorem constructors in
    the existing Hilbert environment showing that the current propositional
    system proves the corresponding Stoic rules.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping

from skfd.proof import Proof, ProofBuilder

from . import System

LemmaCtor = Callable[[System], Proof]


def prove_mtpor(sys: System) -> Proof:
    r"""mtpor: ps.

    Modus tollendo ponens (disjunctive syllogism).
    Given -. ph and ( ph \/ ps ), conclude ps.
    (Contributed by FL, 30-Nov-2010.)
    (Proof shortened by Andrew Salmon, 11-Jul-2011.)
    """
    lb = ProofBuilder(sys, "mtpor")
    mtpor_min = lb.hyp("mtpor.min", "-. ph")
    mtpor_max = lb.hyp("mtpor.max", "( ph \\/ ps )")
    s1 = lb.ref("s1", "( -. ph -> ps )", mtpor_max, ref="ori", note="ori")
    res = lb.mp("res", mtpor_min, s1, "MP mtpor.min, ori(mtpor.max)")
    return lb.build(res)


def prove_stoic1a(sys: System) -> Proof:
    r"""stoic1a: ( ( ph /\ -. th ) -> -. ps ).

    Hyp: stoic1.1 |- ( ( ph /\ ps ) -> th ).

    If ph and not th, then not ps.
    (Contributed by NM, ...)
    """
    lb = ProofBuilder(sys, "stoic1a")
    h1 = lb.hyp("stoic1.1", r"( ( ph /\ ps ) -> th )")
    s1 = lb.ref("s1", "( ph -> ( ps -> th ) )", h1, ref="ex", note="ex")
    res = lb.ref("res", r"( ( ph /\ -. th ) -> -. ps )", s1, ref="con3dimp", note="con3dimp")
    return lb.build(res)


def prove_stoic1b(sys: System) -> Proof:
    """stoic1b: ( ψ ∧ ¬ θ ) → ¬ φ.

    If ψ and not θ, then not φ.
    Sibling of stoic1a obtained by commuting the hypothesis conjunction.
    """
    lb = ProofBuilder(sys, "stoic1b")
    h1 = lb.hyp("stoic1.1", "( ( φ ∧ ψ ) → θ )")
    s1 = lb.ref("s1", "( ( ψ ∧ φ ) → θ )", h1, ref="ancoms", note="ancoms")
    res = lb.ref("res", "( ( ψ ∧ ¬ θ ) → ¬ φ )", s1, ref="stoic1a", note="stoic1a")
    return lb.build(res)


def prove_stoic2a(sys: System) -> Proof:
    """stoic2a: ( φ ∧ ψ ) → θ.

    Syllogism deduction with common antecedent.
    If φ ∧ ψ implies χ, and φ ∧ χ implies θ, then φ ∧ ψ implies θ.
    """
    lb = ProofBuilder(sys, "stoic2a")
    h1 = lb.hyp("stoic2a.1", "( φ ∧ ψ ) → χ")
    h2 = lb.hyp("stoic2a.2", "( φ ∧ χ ) → θ")
    res = lb.ref("res", "( φ ∧ ψ ) → θ", h1, h2, ref="syldan", note="syldan")
    return lb.build(res)


def prove_stoic2b(sys: System) -> Proof:
    """stoic2b: ( φ ∧ ψ ) → θ.

    Syllogism deduction: If φ ∧ ψ implies χ, and φ ∧ ψ ∧ χ implies θ,
    then φ ∧ ψ implies θ.
    """
    lb = ProofBuilder(sys, "stoic2b")
    h1 = lb.hyp("stoic2b.1", "( φ ∧ ψ ) → χ")
    h2 = lb.hyp("stoic2b.2", "( φ ∧ ψ ∧ χ ) → θ")
    res = lb.ref("res", "( φ ∧ ψ ) → θ", h1, h2, ref="mpd3an3", note="mpd3an3")
    return lb.build(res)


THEOREMS: Mapping[str, LemmaCtor] = {
    "mtpor": prove_mtpor,
    "stoic1a": prove_stoic1a,
    "stoic1b": prove_stoic1b,
    "stoic2a": prove_stoic2a,
    "stoic2b": prove_stoic2b,
}

__all__ = [
    "LemmaCtor",
    "THEOREMS",
    "prove_mtpor",
    "prove_stoic1a",
    "prove_stoic1b",
    "prove_stoic2a",
    "prove_stoic2b",
]
