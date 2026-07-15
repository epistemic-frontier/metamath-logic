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


def prove_mtpxor(sys: System) -> Proof:
    """mtpxor: ψ.

    Modus tollendo ponens for exclusive disjunction.
    Given ¬ φ and ( φ ⊻ ψ ), conclude ψ.
    """
    lb = ProofBuilder(sys, "mtpxor")
    mtpxor_min = lb.hyp("mtpxor.min", "¬ φ")
    mtpxor_maj = lb.hyp("mtpxor.maj", "( φ ⊻ ψ )")
    xoror_step = lb.ref("xoror_step", "( φ ⊻ ψ ) → ( φ ∨ ψ )", ref="xoror", note="xoror")
    s1 = lb.mp("s1", mtpxor_maj, xoror_step, "xoror(mtpxor.maj)")
    res = lb.ref("res", "ψ", mtpxor_min, s1, ref="mtpor", note="mtpor")
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
    "prove_mtpxor",
]


def prove_stoic3(sys: System) -> Proof:
    """stoic3: ( φ ∧ ψ ∧ θ ) → τ.

    Syllogism with ternary conjunction: from ( φ ∧ ψ ) → χ and
    ( χ ∧ θ ) → τ, deduce ( φ ∧ ψ ∧ θ ) → τ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "stoic3")
    h1 = lb.hyp("stoic3.1", "( φ ∧ ψ ) → χ")
    h2 = lb.hyp("stoic3.2", "( χ ∧ θ ) → τ")
    s1 = lb.ref("s1", "( ( φ ∧ ψ ) ∧ θ ) → τ", h1, h2, ref="sylan", note="sylan")
    res = lb.ref("res", "( φ ∧ ψ ∧ θ ) → τ", s1, ref="3impa", note="3impa")
    return lb.build(res)


def prove_stoic4a(sys: System) -> Proof:
    """stoic4a: ( φ ∧ ψ ∧ θ ) → τ.

    Syllogism deduction with introduced third antecedent.
    From ( φ ∧ ψ ) → χ and ( χ ∧ φ ∧ θ ) → τ,
    deduce ( φ ∧ ψ ∧ θ ) → τ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "stoic4a")
    h1 = lb.hyp("stoic4a.1", "( φ ∧ ψ ) → χ")
    h2 = lb.hyp("stoic4a.2", "( χ ∧ φ ∧ θ ) → τ")
    s1 = lb.ref("s1", "( φ ∧ ψ ∧ θ ) → χ", h1, ref="3adant3", note="3adant3")
    s2 = lb.ref("s2", "( φ ∧ ψ ∧ θ ) → φ", ref="simp1", note="simp1")
    s3 = lb.ref("s3", "( φ ∧ ψ ∧ θ ) → θ", ref="simp3", note="simp3")
    res = lb.ref("res", "( φ ∧ ψ ∧ θ ) → τ", s1, s2, s3, h2, ref="syl3anc", note="syl3anc")
    return lb.build(res)


def prove_stoic4b(sys: System) -> Proof:
    """stoic4b: ( φ ∧ ψ ∧ θ ) → τ.

    Syllogism deduction with introduced second and third antecedents.
    From ( φ ∧ ψ ) → χ and ( ( χ ∧ φ ∧ ψ ) ∧ θ ) → τ,
    deduce ( φ ∧ ψ ∧ θ ) → τ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "stoic4b")
    h1 = lb.hyp("stoic4b.1", "( φ ∧ ψ ) → χ")
    h2 = lb.hyp("stoic4b.2", "( ( χ ∧ φ ∧ ψ ) ∧ θ ) → τ")
    s1 = lb.ref("s1", "( φ ∧ ψ ∧ θ ) → χ", h1, ref="3adant3", note="3adant3")
    s2 = lb.ref("s2", "( φ ∧ ψ ∧ θ ) → φ", ref="simp1", note="simp1")
    s3 = lb.ref("s3", "( φ ∧ ψ ∧ θ ) → ψ", ref="simp2", note="simp2")
    s4 = lb.ref("s4", "( φ ∧ ψ ∧ θ ) → θ", ref="simp3", note="simp3")
    res = lb.ref("res", "( φ ∧ ψ ∧ θ ) → τ", s1, s2, s3, s4, h2, ref="syl31anc", note="syl31anc")
    return lb.build(res)


MIGRATION_THEOREMS: Mapping[str, LemmaCtor] = {
    "stoic3": prove_stoic3,
    "stoic4a": prove_stoic4a,
    "stoic4b": prove_stoic4b,
    "mtpxor": prove_mtpxor,
}
