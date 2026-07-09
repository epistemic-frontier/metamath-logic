"""Propositional logic — syllogism variants."""

from __future__ import annotations

from skfd.proof import Proof, ProofBuilder

from . import System


def prove_syl11(sys: System) -> Proof:
    """syl11: ψ → (θ → χ). Hyp: φ → (ψ → χ), θ → φ. (Contributed by BJ, 25-Oct-2021.)"""
    lb = ProofBuilder(sys, "syl11")
    h1 = lb.hyp("syl11.1", "φ → ( ψ → χ )")
    h2 = lb.hyp("syl11.2", "θ → φ")
    s1 = lb.ref("s1", "θ → ( ψ → χ )", h2, h1, ref="syl", note="syl")
    res = lb.ref("res", "ψ → ( θ → χ )", s1, ref="com12", note="com12")
    return lb.build(res)


def prove_syl2im(sys: System) -> Proof:
    """syl2im: φ → (χ → τ). Hyp: φ → ψ, χ → θ, ψ → (θ → τ). (Contributed by Wolf Lammen, 14-May-2013.)"""
    lb = ProofBuilder(sys, "syl2im")
    h1 = lb.hyp("syl2im.1", "φ → ψ")
    h2 = lb.hyp("syl2im.2", "χ → θ")
    h3 = lb.hyp("syl2im.3", "ψ → ( θ → τ )")
    s1 = lb.ref("s1", "ψ → ( χ → τ )", h2, h3, ref="syl5", note="syl5")
    res = lb.ref("res", "φ → ( χ → τ )", h1, s1, ref="syl", note="syl")
    return lb.build(res)


def prove_syl2imc(sys: System) -> Proof:
    """syl2imc: χ → (φ → τ). Hyp: φ → ψ, χ → θ, ψ → (θ → τ). (Contributed by BJ, 20-Oct-2021.)"""
    lb = ProofBuilder(sys, "syl2imc")
    h1 = lb.hyp("syl2imc.1", "φ → ψ")
    h2 = lb.hyp("syl2imc.2", "χ → θ")
    h3 = lb.hyp("syl2imc.3", "ψ → ( θ → τ )")
    s1 = lb.ref("s1", "φ → ( χ → τ )", h1, h2, h3, ref="syl2im", note="syl2im")
    res = lb.ref("res", "χ → ( φ → τ )", s1, ref="com12", note="com12")
    return lb.build(res)


def prove_syl56(sys: System) -> Proof:
    """syl56: χ → (φ → τ). Hyp: φ → ψ, χ → (ψ → θ), θ → τ. (Contributed by NM, 14-Nov-2013.)"""
    lb = ProofBuilder(sys, "syl56")
    h1 = lb.hyp("syl56.1", "φ → ψ")
    h2 = lb.hyp("syl56.2", "χ → ( ψ → θ )")
    h3 = lb.hyp("syl56.3", "θ → τ")
    s1 = lb.ref("s1", "χ → ( ψ → τ )", h2, h3, ref="syl6", note="syl6")
    res = lb.ref("res", "χ → ( φ → τ )", h1, s1, ref="syl5", note="syl5")
    return lb.build(res)


def prove_syl6com(sys: System) -> Proof:
    """syl6com: ψ → (φ → θ). Hyp: φ → (ψ → χ), χ → θ. (Contributed by NM, 25-May-2005.)"""
    lb = ProofBuilder(sys, "syl6com")
    h1 = lb.hyp("syl6com.1", "φ → ( ψ → χ )")
    h2 = lb.hyp("syl6com.2", "χ → θ")
    s1 = lb.ref("s1", "φ → ( ψ → θ )", h1, h2, ref="syl6", note="syl6")
    res = lb.ref("res", "ψ → ( φ → θ )", s1, ref="com12", note="com12")
    return lb.build(res)


def prove_syli(sys: System) -> Proof:
    """syli: ψ → (φ → θ). Hyp: ψ → (φ → χ), χ → (φ → θ). (Contributed by NM, 4-Nov-2004.)"""
    lb = ProofBuilder(sys, "syli")
    h1 = lb.hyp("syli.1", "ψ → ( φ → χ )")
    h2 = lb.hyp("syli.2", "χ → ( φ → θ )")
    s1 = lb.ref("s1", "φ → ( χ → θ )", h2, ref="com12", note="com12")
    res = lb.ref("res", "ψ → ( φ → θ )", h1, s1, ref="sylcom", note="sylcom")
    return lb.build(res)


def prove_pm2_01(sys: System) -> Proof:
    """pm2.01: (φ → ¬ φ) → ¬ φ. Weak Clavius law. Theorem *2.01 of [WhiteheadRussell] p. 100."""
    lb = ProofBuilder(sys, "pm2.01")
    s1 = lb.ref("s1", "¬ φ → ¬ φ", ref="id", note="id")
    s2 = lb.ref("s2", "¬ φ → ¬ φ", ref="id", note="id")
    res = lb.ref("res", "( φ → ¬ φ ) → ¬ φ", s1, s2, ref="ja", note="ja")
    return lb.build(res)


def prove_pm2_04(sys: System) -> Proof:
    """pm2.04: (φ → (ψ → χ)) → (ψ → (φ → χ)). Swap antecedents. Theorem *2.04 of [WhiteheadRussell] p. 100."""
    lb = ProofBuilder(sys, "pm2.04")
    h = lb.hyp("pm2.04.1", "φ → ( ψ → χ )")
    res = lb.ref("res", "ψ → ( φ → χ )", h, ref="com12", note="com12")
    return lb.build(res)


def prove_pm2_07(sys: System) -> Proof:
    """pm2.07: φ → ( φ \\/ φ ).

    Theorem *2.07 of [WhiteheadRussell] p. 101.
    (Contributed by NM, 3-Jan-2005.)
    set.mm proof: olc.  Here expanded via pm2.24 (df-or form).
    """
    lb = ProofBuilder(sys, "pm2.07")
    res = lb.ref("res", "( φ → ( φ \\/ φ ) )", ref="pm2.24", note="pm2.24 (df-or)")
    return lb.build(res)


def prove_pm2_27(sys: System) -> Proof:
    """pm2.27: φ → ((φ → ψ) → ψ). Theorem *2.27 of [WhiteheadRussell] p. 104."""
    lb = ProofBuilder(sys, "pm2.27")
    s1 = lb.ref("s1", "( φ → ψ ) → ( φ → ψ )", ref="id", note="id")
    res = lb.ref("res", "φ → ( ( φ → ψ ) → ψ )", s1, ref="com12", note="com12")
    return lb.build(res)


def prove_pm2_43(sys: System) -> Proof:
    """pm2.43: (φ → (φ → ψ)) → (φ → ψ). Theorem *2.43 of [WhiteheadRussell] p. 106."""
    lb = ProofBuilder(sys, "pm2.43")
    s1 = lb.ref("s1", "φ → ( ( φ → ψ ) → ψ )", ref="pm2.27", note="pm2.27")
    res = lb.ref("res", "( φ → ( φ → ψ ) ) → ( φ → ψ )", s1, ref="a2i", note="a2i")
    return lb.build(res)


def prove_pm2_6(sys: System) -> Proof:
    """pm2.6: (¬φ → ψ) → ((φ → ψ) → ψ).
    (Contributed by NM, 24-Jan-1993.)"""
    lb = ProofBuilder(sys, "pm2.6")
    s1 = lb.ref("s1", "( ¬ φ → ψ ) → ( ¬ φ → ψ )", ref="id", note="id")
    s2 = lb.ref("s2", "( ¬ φ → ψ ) → ( ψ → ψ )", ref="idd", note="idd")
    res = lb.ref("res", "( ¬ φ → ψ ) → ( ( φ → ψ ) → ψ )", s1, s2, ref="jad", note="jad")
    return lb.build(res)


def prove_pm2_13(sys: System) -> Proof:
    """pm2.13: φ \\/ -. -. -. φ.

    Theorem *2.13 of [WhiteheadRussell] p. 107.
    (Contributed by NM, 3-Jan-2005.)
    set.mm proof: notnot orri.

    Under df-or, φ \\/ -. -. -. φ is -. φ → -. -. -. φ,
    which is notnot with φ := -. φ. The framework handles
    df-or unification transparently, so orri is not needed.
    """
    lb = ProofBuilder(sys, "pm2.13")
    s1 = lb.ref("s1", "-. φ → -. -. -. φ", ref="notnot", note="notnot")
    return lb.build(s1)


def prove_pm2_26(sys: System) -> Proof:
    """pm2.26: -. φ \\/ ( ( φ → ψ ) → ψ ).

    Theorem *2.26 of [WhiteheadRussell] p. 107.
    (Contributed by NM, 3-Jan-2005.)
    set.mm proof: pm2.27 imori.

    Under df-or, -. φ \\/ X expands to φ → X.
    So -. φ \\/ ( ( φ → ψ ) → ψ ) = φ → ( ( φ → ψ ) → ψ ),
    which is exactly pm2.27.
    """
    lb = ProofBuilder(sys, "pm2.26")
    s1 = lb.ref("s1", "φ → ( ( φ → ψ ) → ψ )", ref="pm2.27", note="pm2.27")
    return lb.build(s1)


def prove_syl9(sys: System) -> Proof:
    """syl9: φ → ( θ → ( ψ → τ ) ).  Hyps: φ → (ψ → χ), θ → (χ → τ)."""
    lb = ProofBuilder(sys, "syl9")
    h1 = lb.hyp("syl9.1", "φ → ( ψ → χ )")
    h2 = lb.hyp("syl9.2", "θ → ( χ → τ )")
    s1 = lb.ref("s1", "χ → ( θ → τ )", h2, ref="com12", note="com12")
    s2 = lb.ref("s2", "φ → ( ψ → ( θ → τ ) )", h1, s1, ref="syl6", note="syl6")
    # Prove (ψ→(θ→τ)) → (θ→(ψ→τ)) via A2+A1+imim1+syl
    sw_a2 = lb.ref("sw_a2", "( ψ → ( θ → τ ) ) → ( ( ψ → θ ) → ( ψ → τ ) )", ref="A2", note="A2")
    sw_a1 = lb.ref("sw_a1", "θ → ( ψ → θ )", ref="A1", note="A1")
    sw_im = lb.ref(
        "sw_im",
        "( θ → ( ψ → θ ) ) → ( ( ( ψ → θ ) → ( ψ → τ ) ) → ( θ → ( ψ → τ ) ) )",
        ref="imim1",
        note="imim1",
    )
    sw_mp = lb.mp("sw_mp", sw_a1, sw_im, "mp A1, imim1")
    s3 = lb.ref(
        "s3",
        "( ψ → ( θ → τ ) ) → ( θ → ( ψ → τ ) )",
        sw_a2,
        sw_mp,
        ref="syl",
        note="syl",
    )
    res = lb.ref("res", "φ → ( θ → ( ψ → τ ) )", s2, s3, ref="syl", note="syl")
    return lb.build(res)


def prove_com23(sys: System) -> Proof:
    """com23: φ → ( χ → ( ψ → θ ) ).  Hyp: φ → (ψ → (χ → θ))."""
    lb = ProofBuilder(sys, "com23")
    h1 = lb.hyp("com23.1", "φ → ( ψ → ( χ → θ ) )")
    s1 = lb.ref("s1", "( ψ → ( χ → θ ) ) → ( ( ψ → χ ) → ( ψ → θ ) )", ref="A2", note="A2")
    s2 = lb.ref("s2", "φ → ( ( ψ → χ ) → ( ψ → θ ) )", h1, s1, ref="syl", note="syl")
    s3 = lb.ref("s3", "χ → ( ψ → χ )", ref="A1", note="A1")
    s4 = lb.ref(
        "s4",
        "( χ → ( ψ → χ ) ) → ( ( ( ψ → χ ) → ( ψ → θ ) ) → ( χ → ( ψ → θ ) ) )",
        ref="imim1",
        note="imim1",
    )
    s5 = lb.mp("s5", s3, s4, "mp A1, imim1")
    res = lb.ref("res", "φ → ( χ → ( ψ → θ ) )", s2, s5, ref="syl", note="syl")
    return lb.build(res)


def prove_pm2_25(sys: System) -> Proof:
    """pm2.25: φ ∨ ( ( φ ∨ ψ ) → ψ )."""
    lb = ProofBuilder(sys, "pm2.25")
    s1 = lb.ref("s1", "¬ φ → ( ( ¬ φ → ψ ) → ψ )", ref="pm2.27", note="pm2.27")
    return lb.build(s1)
