"""Disjunction calculus.

φ∨ψ = ¬φ→ψ (Hilbert encoding).
Includes Peirce's law, jarli/ja, basic properties.
"""

from __future__ import annotations

from skfd.proof import Proof, ProofBuilder

from . import System


def prove_jarli(sys: System) -> Proof:
    """
    jarli: ¬ φ → χ. Hyp: ( φ → ψ ) → χ.

    Inference associated with jarl.
    """
    lb = ProofBuilder(sys, "jarli")
    h1 = lb.hyp("jarli.1", "( φ → ψ ) → χ")

    s1 = lb.ref("s1", "¬ φ → ( φ → ψ )", ref="pm2.21", note="pm2.21")
    res = lb.ref("res", "¬ φ → χ", s1, h1, ref="syl", note="syl")
    return lb.build(res)


def prove_ja(sys: System) -> Proof:
    """
    ja: ( ( φ → ψ ) → χ ). Hyp1: ¬ φ → χ, Hyp2: ψ → χ.

    Inference joining antecedents.
    set.mm proof: imim2i pm2.61d1.
    """
    lb = ProofBuilder(sys, "ja")
    h1 = lb.hyp("ja.1", "¬ φ → χ")
    h2 = lb.hyp("ja.2", "ψ → χ")

    s1 = lb.ref("s1", "( φ → ψ ) → ( φ → χ )", h2, ref="imim2i", note="imim2i")
    res = lb.ref("res", "( φ → ψ ) → χ", s1, h1, ref="pm2.61d1", note="pm2.61d1")
    return lb.build(res)


def prove_peirce(sys: System) -> Proof:
    """
    peirce: ( ( ( φ → ψ ) → φ ) → φ ).

    Peirce's axiom.
    """
    lb = ProofBuilder(sys, "peirce")
    s1 = lb.ref("s1", "¬ ( φ → ψ ) → φ", ref="simplim", note="simplim")
    lb.ref("s2", "φ → φ", ref="id", note="id")
    lb.ref("s3", "( ( φ → ψ ) → φ ) → φ", ref="ja", note="ja")
    s4 = lb.ref(
        "s4",
        "( ¬ ( φ → ψ ) → φ ) → ( ( ( φ → ψ ) → φ ) → φ )",
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
    res = lb.ref(
        "res", "( ψ → χ ) → ( ( ¬ φ → ψ ) → ( ¬ χ → φ ) )", s1, s2, ref="syl5", note="syl5"
    )
    return lb.build(res)


def prove_jaod(sys: System) -> Proof:
    """jaod: φ→((ψ∨θ)→χ).  Hyps: φ→(ψ→χ), φ→(θ→χ).
    set.mm proof: com12 + jaoi + com12."""
    lb = ProofBuilder(sys, "jaod")
    h1 = lb.hyp("jaod.1", "φ → ( ψ → χ )")
    h2 = lb.hyp("jaod.2", "φ → ( θ → χ )")
    s1 = lb.ref("s1", "ψ → ( φ → χ )", h1, ref="com12", note="com12(jaod.1)")
    s2 = lb.ref("s2", "θ → ( φ → χ )", h2, ref="com12", note="com12(jaod.2)")
    s3 = lb.ref("s3", "( ψ ∨ θ ) → ( φ → χ )", s1, s2, ref="jaoi", note="jaoi")
    res = lb.ref("res", "φ → ( ( ψ ∨ θ ) → χ )", s3, ref="com12", note="com12(s3)")
    return lb.build(res)


# ============================================================
# pm2.621 (under df-or = pm2.61)
# ============================================================


def prove_jaoi(sys: System) -> Proof:
    """jaoi: (φ ∨ χ) → ψ.  Hyps: φ→ψ, χ→ψ.
    Under df-or: (~φ→χ)→ψ.
    Proof: con3 on both hyps, compose via imim1+syl6+pm2.65+notnotr.
    """
    lb = ProofBuilder(sys, "jaoi")
    h1 = lb.hyp("jaoi.1", "φ → ψ")
    h2 = lb.hyp("jaoi.2", "χ → ψ")
    # Under df-or the goal is ( ¬ φ → χ ) → ψ, i.e. ja with φ:=¬φ, ψ:=χ.
    # ja's first hypothesis is ¬φ → χ = ¬ ¬ φ → ψ, obtained by lifting h1
    # through notnotr.
    s1 = lb.ref("s1", "-. -. φ → φ", ref="notnotr", note="notnotr")
    s2 = lb.ref("s2", "-. -. φ → ψ", s1, h1, ref="syl", note="syl(notnotr, jaoi.1)")
    res = lb.ref("res", "( -. φ → χ ) → ψ", s2, h2, ref="ja", note="ja(s2, jaoi.2)")
    return lb.build(res)


def prove_olc(sys: System) -> Proof:
    """olc: φ → (ψ ∨ φ).  From orc(pm2.24) + pm1.4 via syl."""
    lb = ProofBuilder(sys, "olc")
    s1 = lb.ref("s1", "φ → ( φ ∨ ψ )", ref="pm2.24", note="pm2.24 (orc)")
    s2 = lb.ref("s2", "( φ ∨ ψ ) → ( ψ ∨ φ )", ref="pm1.4", note="pm1.4")
    res = lb.ref("res", "φ → ( ψ ∨ φ )", s1, s2, ref="syl", note="syl(orc, pm1.4)")
    return lb.build(res)


# ============================================================
# pm2.53, pm2.54 (trivial under df-or)
# ============================================================


def prove_pm2_621(sys: System) -> Proof:
    """Theorem *2.621 of [WhiteheadRussell] p. 107.
    ( φ → ψ ) → ( ( φ ∨ ψ ) → ψ ).
    (Contributed by NM, 3-Jan-2005.)
    set.mm proof: id + idd + jaod.
    Under df-or: ( φ → ψ ) → ( ( -. φ → ψ ) → ψ ).
    This is exactly pm2.61."""
    lb = ProofBuilder(sys, "pm2.621")
    res = lb.ref("res", "( φ → ψ ) → ( ( -. φ → ψ ) → ψ )", ref="pm2.61", note="pm2.61")
    return lb.build(res)


def prove_pm2_67(sys: System) -> Proof:
    """Theorem *2.67 of [WhiteheadRussell] p. 107.
    ( ( ( φ ∨ ψ ) → ψ ) → ( φ → ψ ) )
    (Contributed by NM, 3-Jan-2005.)
    """
    lb = ProofBuilder(sys, "pm2.67")
    h1 = lb.hyp("pm2.67.1", "( ( ¬ φ → ψ ) → ψ )")
    s1 = lb.ref("s1", "¬ φ → ( φ → ψ )", ref="pm2.21", note="pm2.21")
    s2 = lb.ref("s2", "φ → ( ¬ φ → ψ )", s1, ref="com12", note="com12(s1)")
    res = lb.ref("res", "φ → ψ", s2, h1, ref="syl", note="syl(s2, h1)")
    return lb.build(res)


def prove_pm2_67_2(sys: System) -> Proof:
    """Theorem *2.67-2 of [WhiteheadRussell] p. 107.
    ( ( φ ∨ χ ) → ψ ) → ( φ → ψ ).
    (Contributed by NM, 3-Jan-2005.)
    set.mm proof: orc + imim1i.
    Under df-or: ( ( -. φ → χ ) → ψ ) → ( φ → ψ ).
    Proof: pm2.24 + imim1 via mp."""
    lb = ProofBuilder(sys, "pm2.67-2")
    s1 = lb.ref("s1", "φ → ( -. φ → χ )", ref="pm2.24", note="pm2.24")
    s2 = lb.ref(
        "s2",
        "( φ → ( -. φ → χ ) ) → ( ( ( -. φ → χ ) → ψ ) → ( φ → ψ ) )",
        ref="imim1",
        note="imim1",
    )
    res = lb.mp("res", s1, s2, note="MP pm2.24 imim1")
    return lb.build(res)


def prove_pm2_68(sys: System) -> Proof:
    """Theorem *2.68 of [WhiteheadRussell] p. 108.
    ( ( ( φ → ψ ) → ψ ) → ( φ ∨ ψ ) )
    (Contributed by NM, 3-Jan-2005.)
    Under df-or: ( ( ( φ → ψ ) → ψ ) → ( ¬ φ → ψ ) )
    Proof: jarli with hypothesis discharge.
    """
    lb = ProofBuilder(sys, "pm2.68")
    h1 = lb.hyp("pm2.68.1", "( φ → ψ ) → ψ")
    res = lb.ref("res", "¬ φ → ψ", h1, ref="jarli", note="jarli(h1)")
    return lb.build(res)


def prove_pm2_73(sys: System) -> Proof:
    """Theorem *2.73 of [WhiteheadRussell] p. 108.

    ( φ → ψ ) → ( ( ( φ ∨ ψ ) ∨ χ ) → ( ψ ∨ χ ) )

    (Contributed by NM, 3-Jan-2005.)
    Under df-or: ( φ → ψ ) → ( ( ¬ ( ¬ φ → ψ ) → χ ) → ( ¬ ψ → χ ) )
    Proof: pm2.61 + com12 gives pm2.621, then orim1d via con3 + imim1.
    """
    lb = ProofBuilder(sys, "pm2.73")
    # Step 1: pm2.621 = com12(com12(pm2.61))
    # pm2.61: (φ→ψ)→((¬φ→ψ)→ψ)
    s1 = lb.ref("s1", "( φ → ψ ) → ( ( ¬ φ → ψ ) → ψ )", ref="pm2.61", note="pm2.61")
    # pm2.62 = com12(s1): (¬φ→ψ)→((φ→ψ)→ψ)
    s2 = lb.ref("s2", "( ¬ φ → ψ ) → ( ( φ → ψ ) → ψ )", s1, ref="com12", note="com12(s1)")
    # pm2.621 = com12(s2): (φ→ψ)→((¬φ→ψ)→ψ)
    s3 = lb.ref("s3", "( φ → ψ ) → ( ( ¬ φ → ψ ) → ψ )", s2, ref="com12", note="com12(s2)")
    # Step 2: orim1d via con3 + imim1
    # con3: ((¬φ→ψ)→ψ) → (¬ψ→¬(¬φ→ψ))
    s4 = lb.ref("s4", "( ( ¬ φ → ψ ) → ψ ) → ( ¬ ψ → ¬ ( ¬ φ → ψ ) )", ref="con3", note="con3")
    # imim1: (¬ψ→¬(¬φ→ψ)) → ((¬(¬φ→ψ)→χ)→(¬ψ→χ))
    s5 = lb.ref(
        "s5",
        "( ¬ ψ → ¬ ( ¬ φ → ψ ) ) → ( ( ¬ ( ¬ φ → ψ ) → χ ) → ( ¬ ψ → χ ) )",
        ref="imim1",
        note="imim1",
    )
    # syl(s4, s5): ((¬φ→ψ)→ψ) → ((¬(¬φ→ψ)→χ)→(¬ψ→χ))
    s6 = lb.ref(
        "s6",
        "( ( ¬ φ → ψ ) → ψ ) → ( ( ¬ ( ¬ φ → ψ ) → χ ) → ( ¬ ψ → χ ) )",
        s4,
        s5,
        ref="syl",
        note="syl(s4, s5)",
    )
    # syl(s3, s6): (φ→ψ) → ((¬(¬φ→ψ)→χ)→(¬ψ→χ))
    res = lb.ref(
        "res",
        "( φ → ψ ) → ( ( ¬ ( ¬ φ → ψ ) → χ ) → ( ¬ ψ → χ ) )",
        s3,
        s6,
        ref="syl",
        note="syl(s3, s6)",
    )
    return lb.build(res)


def prove_pm2_74(sys: System) -> Proof:
    """
    pm2.74: ( ψ → φ ) → ( ( ¬ ( ¬ φ → ψ ) → χ ) → ( ¬ φ → χ ) ).

    Theorem *2.74 of [WhiteheadRussell] p. 108.
    (Contributed by NM, 3-Jan-2005.)
    (Proof shortened by Andrew Salmon, 7-May-2011.)

    In set.mm ∨-notation: ( ( ψ → φ ) →
      ( ( ( φ ∨ ψ ) ∨ χ ) → ( φ ∨ χ ) ) ).
    """
    lb = ProofBuilder(sys, "pm2.74")
    # pm2.61 with φ↦ψ, ψ↦φ: ( ψ → φ ) → ( ( ¬ ψ → φ ) → φ )
    s1 = lb.ref(
        "s1",
        "( ψ → φ ) → ( ( ¬ ψ → φ ) → φ )",
        ref="pm2.61",
        note="pm2.61",
    )
    # con3 on inner: ( ( ¬ ψ → φ ) → φ ) → ( ¬ φ → ¬ ( ¬ ψ → φ ) )
    s2 = lb.ref(
        "s2",
        "( ( ¬ ψ → φ ) → φ ) → ( ¬ φ → ¬ ( ¬ ψ → φ ) )",
        ref="con3",
        note="con3",
    )
    # syl s1, s2: ( ψ → φ ) → ( ¬ φ → ¬ ( ¬ ψ → φ ) )
    s3 = lb.ref(
        "s3",
        "( ψ → φ ) → ( ¬ φ → ¬ ( ¬ ψ → φ ) )",
        s1,
        s2,
        ref="syl",
        note="syl",
    )
    # pm1.4: ( ¬ φ → ψ ) → ( ¬ ψ → φ )
    s4 = lb.ref(
        "s4",
        "( ¬ φ → ψ ) → ( ¬ ψ → φ )",
        ref="pm1.4",
        note="pm1.4",
    )
    # con3 on s4: ( ( ¬ φ → ψ ) → ( ¬ ψ → φ ) ) → ( ¬ ( ¬ ψ → φ ) → ¬ ( ¬ φ → ψ ) )
    s5 = lb.ref(
        "s5",
        "( ( ¬ φ → ψ ) → ( ¬ ψ → φ ) ) → ( ¬ ( ¬ ψ → φ ) → ¬ ( ¬ φ → ψ ) )",
        ref="con3",
        note="con3",
    )
    # MP s4, s5: ¬ ( ¬ ψ → φ ) → ¬ ( ¬ φ → ψ )
    s6 = lb.mp("s6", s4, s5, "MP s4, s5")
    # syl6 s3, s6: ( ψ → φ ) → ( ¬ φ → ¬ ( ¬ φ → ψ ) )
    s7 = lb.ref(
        "s7",
        "( ψ → φ ) → ( ¬ φ → ¬ ( ¬ φ → ψ ) )",
        s3,
        s6,
        ref="syl6",
        note="syl6",
    )
    # imim1: ( ¬ φ → ¬ ( ¬ φ → ψ ) ) → ( ( ¬ ( ¬ φ → ψ ) → χ ) → ( ¬ φ → χ ) )
    s8 = lb.ref(
        "s8",
        "( ¬ φ → ¬ ( ¬ φ → ψ ) ) → ( ( ¬ ( ¬ φ → ψ ) → χ ) → ( ¬ φ → χ ) )",
        ref="imim1",
        note="imim1",
    )
    # syl s7, s8: ( ψ → φ ) → ( ( ¬ ( ¬ φ → ψ ) → χ ) → ( ¬ φ → χ ) )
    res = lb.ref(
        "res",
        "( ψ → φ ) → ( ( ¬ ( ¬ φ → ψ ) → χ ) → ( ¬ φ → χ ) )",
        s7,
        s8,
        ref="syl",
        note="syl",
    )
    return lb.build(res)


def prove_pm2_75(sys: System) -> Proof:
    """Theorem *2.75 of [WhiteheadRussell] p. 108.
    ( φ ∨ ψ ) → ( ( φ ∨ ( ψ → χ ) ) → ( φ ∨ χ ) )
    (Contributed by NM, 3-Jan-2005.)
    (Proof shortened by Wolf Lammen, 4-Jan-2013.)
    Under df-or: ( ¬ φ → ψ ) → ( ( ¬ φ → ( ψ → χ ) ) → ( ¬ φ → χ ) )
    Proof: A2 + com12.
    """
    lb = ProofBuilder(sys, "pm2.75")
    s1 = lb.ref(
        "s1",
        "( ¬ φ → ( ψ → χ ) ) → ( ( ¬ φ → ψ ) → ( ¬ φ → χ ) )",
        ref="A2",
        note="A2",
    )
    res = lb.ref(
        "res",
        "( ¬ φ → ψ ) → ( ( ¬ φ → ( ψ → χ ) ) → ( ¬ φ → χ ) )",
        s1,
        ref="com12",
        note="com12(s1)",
    )
    return lb.build(res)


def prove_pm2_76(sys: System) -> Proof:
    """
    pm2.76: ( ¬ φ → ( ψ → χ ) ) → ( ( ¬ φ → ψ ) → ( ¬ φ → χ ) ).

    Theorem *2.76 of [WhiteheadRussell] p. 108.
    (Contributed by NM, 3-Jan-2005.)

    In set.mm ∨-notation: ( ( φ ∨ ( ψ → χ ) ) →
      ( ( φ ∨ ψ ) → ( φ ∨ χ ) ) ).
    This is A2 (ax-2) with φ ↦ ¬ φ.
    """
    lb = ProofBuilder(sys, "pm2.76")
    # A2: ( ¬ φ → ( ψ → χ ) ) → ( ( ¬ φ → ψ ) → ( ¬ φ → χ ) )
    res = lb.ref(
        "res",
        "( ¬ φ → ( ψ → χ ) ) → ( ( ¬ φ → ψ ) → ( ¬ φ → χ ) )",
        ref="A2",
        note="A2",
    )
    return lb.build(res)


def prove_pm2_81(sys: System) -> Proof:
    """pm2.81: (ψ → (χ → θ)) → ((φ ∨ ψ) → ((φ ∨ χ) → (φ ∨ θ))).

    Theorem *2.81 of [WhiteheadRussell] p. 108.
    (Contributed by NM, 3-Jan-2005.)

    set.mm proof: orim2 pm2.76 syl6.
    Under df-or: (ψ→(χ→θ))→((¬φ→ψ)→((¬φ→χ)→(¬φ→θ))).
    imim2: (ψ→(χ→θ))→((¬φ→ψ)→(¬φ→(χ→θ))).
    A2: (¬φ→(χ→θ))→((¬φ→χ)→(¬φ→θ)).
    syl6 chains them.
    """
    lb = ProofBuilder(sys, "pm2.81")
    s_imim2 = lb.ref(
        "s_imim2",
        "( ( ψ → ( χ → θ ) ) → ( ( -. φ → ψ ) → ( -. φ → ( χ → θ ) ) ) )",
        ref="imim2",
        note="imim2",
    )
    s_A2 = lb.ref(
        "s_A2",
        "( ( -. φ → ( χ → θ ) ) → ( ( -. φ → χ ) → ( -. φ → θ ) ) )",
        ref="A2",
        note="A2",
    )
    res = lb.ref(
        "res",
        "( ( ψ → ( χ → θ ) ) → ( ( -. φ → ψ ) → ( ( -. φ → χ ) → ( -. φ → θ ) ) ) )",
        s_imim2,
        s_A2,
        ref="syl6",
        note="syl6(imim2, A2)",
    )
    return lb.build(res)


def prove_pm2_83(sys: System) -> Proof:
    """pm2.83: (φ → (ψ → χ)) → ((φ → (χ → θ)) → (φ → (ψ → θ))).

    Closed form of syld.  Theorem *2.83 of [WhiteheadRussell] p. 108.
    (Contributed by NM, 3-Jan-2005.)
    set.mm proof: imim1 imim3i.
    """
    lb = ProofBuilder(sys, "pm2.83")
    s1 = lb.ref("s1", "( ( ψ → χ ) → ( ( χ → θ ) → ( ψ → θ ) ) )", ref="imim1", note="imim1")
    res = lb.ref(
        "res",
        "( ( φ → ( ψ → χ ) ) → ( ( φ → ( χ → θ ) ) → ( φ → ( ψ → θ ) ) ) )",
        s1,
        ref="imim3i",
        note="imim3i",
    )
    return lb.build(res)


def prove_pm2_85(sys: System) -> Proof:
    """pm2.85: ((φ ∨ ψ) → (φ ∨ χ)) → (φ ∨ (ψ → χ)).
    Under df-or, this is pm2.86 with -.φ for φ.
    """
    lb = ProofBuilder(sys, "pm2.85")
    res = lb.ref(
        "res",
        "(( -. φ → ψ ) → ( -. φ → χ )) → ( -. φ → ( ψ → χ ))",
        ref="pm2.86",
        note="pm2.86 (df-or)",
    )
    return lb.build(res)


def prove_pm2_86(sys: System) -> Proof:
    """pm2.86: ((φ → ψ) → (φ → χ)) → (φ → (ψ → χ))."""
    lb = ProofBuilder(sys, "pm2.86")
    s1 = lb.ref(
        "s1",
        "( ( φ → ψ ) → ( φ → χ ) ) → ( ( φ → ψ ) → ( φ → χ ) )",
        ref="id",
        note="id",
    )
    res = lb.ref(
        "res",
        "( ( φ → ψ ) → ( φ → χ ) ) → ( φ → ( ψ → χ ) )",
        s1,
        ref="pm2.86d",
        note="pm2.86d",
    )
    return lb.build(res)


def prove_pm2_82(sys: System) -> Proof:
    """pm2.82: (((φ ∨ ψ) ∨ χ) → (((φ ∨ -. χ) ∨ θ) → ((φ ∨ ψ) ∨ θ))).

    Theorem *2.82 of [WhiteheadRussell] p. 108.
    Under df-or: A = (-. φ → ψ), B = (-. φ → -. χ).
    Goal: (-. A → χ) → ((-. B → θ) → (-. A → θ)).

    set.mm proof: pm2.24 orim2d jao1i orim1d.
    Direct transliteration using df-or expansion.
    """
    lb = ProofBuilder(sys, "pm2.82")

    # Under df-or: (φ ∨ ψ) = (¬ φ → ψ)
    # Let A = (¬ φ → ψ), B = (¬ φ → ¬ χ)
    # Goal in df-or:
    # (¬ (¬ φ → ψ) → χ) → ((¬ (¬ φ → ¬ χ) → θ) → (¬ (¬ φ → ψ) → θ))

    # Step 1: pm2.24: χ → (¬ χ → ψ)
    s1 = lb.ref("s1", "χ → ( -. χ → ψ )", ref="pm2.24", note="pm2.24")

    # Step 2: imim2: (¬ χ → ψ) → ((¬ φ → ¬ χ) → (¬ φ → ψ))
    s2 = lb.ref(
        "s2",
        "( -. χ → ψ ) → ( ( -. φ → -. χ ) → ( -. φ → ψ ) )",
        ref="imim2",
        note="imim2",
    )

    # Step 3: syl(s1, s2): χ → ((¬ φ → ¬ χ) → (¬ φ → ψ))
    s3 = lb.ref("s3", "χ → ( ( -. φ → -. χ ) → ( -. φ → ψ ) )", s1, s2, ref="syl", note="syl")

    # Step 4: con3: ((¬ φ → ¬ χ) → (¬ φ → ψ)) → (¬ (¬ φ → ψ) → ¬ (¬ φ → ¬ χ))
    s4 = lb.ref(
        "s4",
        "( ( -. φ → -. χ ) → ( -. φ → ψ ) ) → ( -. ( -. φ → ψ ) → -. ( -. φ → -. χ ) )",
        ref="con3",
        note="con3",
    )

    # Step 5: syl(s3, s4): χ → (¬ (¬ φ → ψ) → ¬ (¬ φ → ¬ χ))
    s5 = lb.ref("s5", "χ → ( -. ( -. φ → ψ ) → -. ( -. φ → -. χ ) )", s3, s4, ref="syl", note="syl")

    # Step 6: com12(s5): ¬ (¬ φ → ψ) → (χ → ¬ (¬ φ → ¬ χ))
    s6 = lb.ref("s6", "-. ( -. φ → ψ ) → ( χ → -. ( -. φ → -. χ ) )", s5, ref="com12", note="com12")

    # Step 7: imim1: (χ → ¬ (¬ φ → ¬ χ)) → ((¬ (¬ φ → ¬ χ) → θ) → (χ → θ))
    s7 = lb.ref(
        "s7",
        "( χ → -. ( -. φ → -. χ ) ) → ( ( -. ( -. φ → -. χ ) → θ ) → ( χ → θ ) )",
        ref="imim1",
        note="imim1",
    )

    # Step 8: syl(s6, s7)
    s8 = lb.ref(
        "s8",
        "-. ( -. φ → ψ ) → ( ( -. ( -. φ → -. χ ) → θ ) → ( χ → θ ) )",
        s6,
        s7,
        ref="syl",
        note="syl",
    )

    # Step 9: com12(s8)
    s9 = lb.ref(
        "s9",
        "( -. ( -. φ → -. χ ) → θ ) → ( -. ( -. φ → ψ ) → ( χ → θ ) )",
        s8,
        ref="com12",
        note="com12",
    )

    # Step 10: A2
    s10 = lb.ref(
        "s10",
        "( -. ( -. φ → ψ ) → ( χ → θ ) ) → ( ( -. ( -. φ → ψ ) → χ ) → ( -. ( -. φ → ψ ) → θ ) )",
        ref="A2",
        note="A2",
    )

    # Step 11: syl(s9, s10)
    s11 = lb.ref(
        "s11",
        "( -. ( -. φ → -. χ ) → θ ) → ( ( -. ( -. φ → ψ ) → χ ) → ( -. ( -. φ → ψ ) → θ ) )",
        s9,
        s10,
        ref="syl",
        note="syl",
    )

    # Step 12: com12(s11) — final
    res = lb.ref(
        "res",
        "( -. ( -. φ → ψ ) → χ ) → ( ( -. ( -. φ → -. χ ) → θ ) → ( -. ( -. φ → ψ ) → θ ) )",
        s11,
        ref="com12",
        note="com12",
    )

    return lb.build(res)
