"""Disjunction calculus.

φ∨ψ = ¬φ→ψ (Hilbert encoding).
Includes Peirce's law, jarli/ja, basic properties.
"""

from __future__ import annotations
from skfd.proof import Proof, ProofBuilder
from . import System


def prove_jarli(sys: System) -> Proof:
    """
    jarli: ¬ φ → χ. Hyp: ( φ → ψ ) -> χ.

    Inference associated with jarl.
    """
    lb = ProofBuilder(sys, "jarli")
    h1 = lb.hyp("jarli.1", "( φ → ψ ) -> χ")

    s1 = lb.ref("s1", "¬ φ → ( φ → ψ )", ref="pm2.21", note="pm2.21")
    res = lb.ref("res", "¬ φ → χ", s1, h1, ref="syl", note="syl")
    return lb.build(res)

def prove_ja(sys: System) -> Proof:
    """
    ja: ( ( φ → ψ ) -> χ ). Hyp1: ¬ φ → χ, Hyp2: ψ → χ.

    Inference joining antecedents.
    """
    lb = ProofBuilder(sys, "ja")
    h1 = lb.hyp("ja.1", "¬ φ → χ")
    h2 = lb.hyp("ja.2", "ψ → χ")

    s1 = lb.ref("s1", "¬ ( φ → ψ ) -> φ", ref="simplim", note="simplim")
    s2 = lb.ref(
        "s2",
        "( ¬ ( φ → ψ ) -> φ ) -> ( ( ¬ φ → χ ) -> ( ¬ ( φ → ψ ) -> χ ) )",
        ref="syl",
        note="syl",
    )
    s3 = lb.mp("s3", s1, s2, "MP s1, s2")
    s4 = lb.mp("s4", h1, s3, "MP ja.1, s3")

    s5 = lb.ref(
        "s5",
        "( ψ → χ ) -> ( ( φ → ψ ) -> ( φ → χ ) )",
        ref="imim1",
        note="imim1",
    )
    s6 = lb.mp("s6", h2, s5, "MP ja.2, s5")

    s7 = lb.ref(
        "s7",
        "( ( ¬ ( φ → ψ ) -> χ ) -> ( ( ( φ → ψ ) -> ( φ → χ ) ) -> ( ( φ → ψ ) -> χ ) ) )",
        ref="pm2.61",
        note="pm2.61",
    )
    s8 = lb.mp("s8", s4, s7, "MP s4, s7")
    res = lb.mp("res", s6, s8, "MP s6, s8")
    return lb.build(res)

def prove_peirce(sys: System) -> Proof:
    """
    peirce: ( ( ( φ → ψ ) → φ ) → φ ).

    Peirce's axiom.
    """
    lb = ProofBuilder(sys, "peirce")
    s1 = lb.ref("s1", "¬ ( φ → ψ ) -> φ", ref="simplim", note="simplim")
    lb.ref("s2", "φ → φ", ref="id", note="id")
    lb.ref("s3", "( ( φ → ψ ) -> φ ) -> φ", ref="ja", note="ja")
    s4 = lb.ref(
        "s4",
        "( ¬ ( φ → ψ ) -> φ ) -> ( ( ( φ → ψ ) -> φ ) -> φ )",
        ref="syl",
        note="syl",
    )
    res = lb.mp("res", s1, s4, "MP s1, s4")
    return lb.build(res)

def prove_pm1_4(sys: System) -> Proof:
    lb = ProofBuilder(sys, "pm1.4")
    s1 = lb.ref("s1", "( ¬ φ → ψ ) → ( ¬ ψ → ¬ ¬ φ )", ref="con3", note="con3")
    s2 = lb.ref("s2", "¬ ¬ φ → φ", ref="notnotr", note="notnotr")
    res = lb.ref("res", "( ¬ φ → ψ ) → ( ¬ ψ → φ )", s1, s2, ref="syl6", note="syl6")
    return lb.build(res)

def prove_pm2_38(sys: System) -> Proof:
    lb = ProofBuilder(sys, "pm2.38")
    s1 = lb.ref("s1", "( ψ → χ ) → ( ¬ χ → ¬ ψ )", ref="con3", note="con3")
    s2 = lb.ref("s2", "( ¬ χ → ¬ ψ ) → ( ( ¬ ψ → φ ) → ( ¬ χ → φ ) )", ref="imim1", note="imim1")
    res = lb.ref("res", "( ψ → χ ) → ( ( ¬ ψ → φ ) → ( ¬ χ → φ ) )", s1, s2, ref="syl", note="syl")
    return lb.build(res)

def prove_pm2_36(sys: System) -> Proof:
    lb = ProofBuilder(sys, "pm2.36")
    s1 = lb.ref("s1", "( ¬ φ → ψ ) → ( ¬ ψ → φ )", ref="pm1.4", note="pm1.4")
    s2 = lb.ref("s2", "( ψ → χ ) → ( ( ¬ ψ → φ ) → ( ¬ χ → φ ) )", ref="pm2.38", note="pm2.38")
    res = lb.ref("res", "( ψ → χ ) → ( ( ¬ φ → ψ ) → ( ¬ χ → φ ) )", s1, s2, ref="syl5", note="syl5")
    return lb.build(res)

