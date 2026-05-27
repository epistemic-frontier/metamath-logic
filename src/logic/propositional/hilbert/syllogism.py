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
    """pm2.07: ph -> ( ph \\/ ph ).

    Theorem *2.07 of [WhiteheadRussell] p. 101.
    (Contributed by NM, 3-Jan-2005.)
    set.mm proof: olc.  Here expanded via pm2.24 (df-or form).
    """
    lb = ProofBuilder(sys, "pm2.07")
    res = lb.ref("res", "( ph -> ( ph \\/ ph ) )", ref="pm2.24", note="pm2.24 (df-or)")
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


def prove_pm2_37(sys: System) -> Proof:
    """pm2.37: (ψ → χ) → ((ψ ∨ φ) → (φ ∨ χ)). Theorem *2.37. set.mm: pm2.38 pm1.4 syl6."""
    lb = ProofBuilder(sys, "pm2.37")
    s1 = lb.ref(
        "s1",
        "( ( ψ → χ ) → ( ( ¬ ψ → φ ) → ( ¬ χ → φ ) ) )",
        ref="pm2.38",
        note="pm2.38: (ψ→χ)→((ψ∨φ)→(χ∨φ))",
    )
    s2 = lb.ref("s2", "( ( ¬ χ → φ ) → ( ¬ φ → χ ) )", ref="pm1.4", note="pm1.4: (χ∨φ)→(φ∨χ)")
    res = lb.ref(
        "res",
        "( ( ψ → χ ) → ( ( ¬ ψ → φ ) → ( ¬ φ → χ ) ) )",
        s1,
        s2,
        ref="syl6",
        note="syl6(pm2.38, pm1.4)",
    )
    return lb.build(res)


def prove_pm2_41(sys: System) -> Proof:
    """pm2.41: (ψ ∨ (φ ∨ ψ)) → (φ ∨ ψ). Theorem *2.41.

    Under df-or: (¬ψ → (¬φ → ψ)) → (¬φ → ψ).
    Proof: com12 on hyp to get (¬φ → (¬ψ → ψ)), then syl with pm2.18.
    """
    lb = ProofBuilder(sys, "pm2.41")
    h = lb.hyp("pm2.41.1", "¬ ψ → ( ¬ φ → ψ )")
    s_swap = lb.ref("s_swap", "¬ φ → ( ¬ ψ → ψ )", h, ref="com12", note="com12(h)")
    s_pm18 = lb.ref("s_pm18", "( ¬ ψ → ψ ) → ψ", ref="pm2.18", note="pm2.18")
    res = lb.ref("res", "¬ φ → ψ", s_swap, s_pm18, ref="syl", note="syl(com12(h), pm2.18)")
    return lb.build(res)


def prove_pm2_13(sys: System) -> Proof:
    """pm2.13: ph \\/ -. -. -. ph.

    Theorem *2.13 of [WhiteheadRussell] p. 107.
    (Contributed by NM, 3-Jan-2005.)
    set.mm proof: notnot orri.

    Under df-or, ph \\/ -. -. -. ph is -. ph -> -. -. -. ph,
    which is notnot with ph := -. ph. The framework handles
    df-or unification transparently, so orri is not needed.
    """
    lb = ProofBuilder(sys, "pm2.13")
    s1 = lb.ref("s1", "-. ph -> -. -. -. ph", ref="notnot", note="notnot")
    return lb.build(s1)


def prove_pm2_26(sys: System) -> Proof:
    """pm2.26: -. ph \\/ ( ( ph -> ps ) -> ps ).

    Theorem *2.26 of [WhiteheadRussell] p. 107.
    (Contributed by NM, 3-Jan-2005.)
    set.mm proof: pm2.27 imori.

    Under df-or, -. ph \\/ X expands to ph -> X.
    So -. ph \\/ ( ( ph -> ps ) -> ps ) = ph -> ( ( ph -> ps ) -> ps ),
    which is exactly pm2.27.
    """
    lb = ProofBuilder(sys, "pm2.26")
    s1 = lb.ref("s1", "ph -> ( ( ph -> ps ) -> ps )", ref="pm2.27", note="pm2.27")
    return lb.build(s1)


def prove_syl9(sys: Any) -> Any:
    """syl9: ph -> ( th -> ( ps -> ta ) ).  Hyps: ph -> (ps -> ch), th -> (ch -> ta)."""
    from skfd.proof import ProofBuilder

    lb = ProofBuilder(sys, "syl9")
    h1 = lb.hyp("syl9.1", "ph -> ( ps -> ch )")
    h2 = lb.hyp("syl9.2", "th -> ( ch -> ta )")
    s1 = lb.ref("s1", "ch -> ( th -> ta )", h2, ref="com12", note="com12")
    s2 = lb.ref("s2", "ph -> ( ps -> ( th -> ta ) )", h1, s1, ref="syl6", note="syl6")
    # Prove (ps->(th->ta)) -> (th->(ps->ta)) via A2+A1+imim1+syl
    sw_a2 = lb.ref(
        "sw_a2", "( ps -> ( th -> ta ) ) -> ( ( ps -> th ) -> ( ps -> ta ) )", ref="A2", note="A2"
    )
    sw_a1 = lb.ref("sw_a1", "th -> ( ps -> th )", ref="A1", note="A1")
    sw_im = lb.ref(
        "sw_im",
        "( th -> ( ps -> th ) ) -> ( ( ( ps -> th ) -> ( ps -> ta ) ) -> ( th -> ( ps -> ta ) ) )",
        ref="imim1",
        note="imim1",
    )
    sw_mp = lb.mp("sw_mp", sw_a1, sw_im, "mp A1, imim1")
    s3 = lb.ref(
        "s3",
        "( ps -> ( th -> ta ) ) -> ( th -> ( ps -> ta ) )",
        sw_a2,
        sw_mp,
        ref="syl",
        note="syl",
    )
    res = lb.ref("res", "ph -> ( th -> ( ps -> ta ) )", s2, s3, ref="syl", note="syl")
    return lb.build(res)


def prove_com23(sys: Any) -> Any:
    """com23: ph -> ( ch -> ( ps -> th ) ).  Hyp: ph -> (ps -> (ch -> th))."""
    from skfd.proof import ProofBuilder

    lb = ProofBuilder(sys, "com23")
    h1 = lb.hyp("com23.1", "ph -> ( ps -> ( ch -> th ) )")
    s1 = lb.ref(
        "s1", "( ps -> ( ch -> th ) ) -> ( ( ps -> ch ) -> ( ps -> th ) )", ref="A2", note="A2"
    )
    s2 = lb.ref("s2", "ph -> ( ( ps -> ch ) -> ( ps -> th ) )", h1, s1, ref="syl", note="syl")
    s3 = lb.ref("s3", "ch -> ( ps -> ch )", ref="A1", note="A1")
    s4 = lb.ref(
        "s4",
        "( ch -> ( ps -> ch ) ) -> ( ( ( ps -> ch ) -> ( ps -> th ) ) -> ( ch -> ( ps -> th ) ) )",
        ref="imim1",
        note="imim1",
    )
    s5 = lb.mp("s5", s3, s4, "mp A1, imim1")
    res = lb.ref("res", "ph -> ( ch -> ( ps -> th ) )", s2, s5, ref="syl", note="syl")
    return lb.build(res)


def prove_pm2_86d(sys: Any) -> Any:
    """pm2.86d: ph -> ( ps -> ( ch -> th ) ).  Hyp: ph -> ((ps -> ch) -> (ps -> th))."""
    from skfd.proof import ProofBuilder

    lb = ProofBuilder(sys, "pm2.86d")
    h1 = lb.hyp("pm2.86d.1", "ph -> ( ( ps -> ch ) -> ( ps -> th ) )")
    s_a1 = lb.ref("s_a1", "ch -> ( ps -> ch )", ref="A1", note="A1")
    s_c12a = lb.ref(
        "s_c12a", "( ps -> ch ) -> ( ph -> ( ps -> th ) )", h1, ref="com12", note="com12"
    )
    s_syl = lb.ref("s_syl", "ch -> ( ph -> ( ps -> th ) )", s_a1, s_c12a, ref="syl", note="syl")
    s_c12b = lb.ref("s_c12b", "ph -> ( ch -> ( ps -> th ) )", s_syl, ref="com12", note="com12")
    res = lb.ref("res", "ph -> ( ps -> ( ch -> th ) )", s_c12b, ref="com23", note="com23")
    return lb.build(res)


def prove_pm2_86(sys: Any) -> Any:
    """pm2.86: ((ph -> ps) -> (ph -> ch)) -> (ph -> (ps -> ch))."""
    from skfd.proof import ProofBuilder

    lb = ProofBuilder(sys, "pm2.86")
    s1 = lb.ref(
        "s1",
        "( ( ph -> ps ) -> ( ph -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) )",
        ref="id",
        note="id",
    )
    res = lb.ref(
        "res",
        "( ( ph -> ps ) -> ( ph -> ch ) ) -> ( ph -> ( ps -> ch ) )",
        s1,
        ref="pm2.86d",
        note="pm2.86d",
    )
    return lb.build(res)


def prove_pm2_86i(sys: Any) -> Any:
    """pm2.86i: ph -> (ps -> ch).  Hyp: ((ph -> ps) -> (ph -> ch))."""
    from skfd.proof import ProofBuilder

    lb = ProofBuilder(sys, "pm2.86i")
    h1 = lb.hyp("pm2.86i.1", "( ph -> ps ) -> ( ph -> ch )")
    s1 = lb.ref("s1", "ps -> ( ph -> ch )", h1, ref="jarri", note="jarri")
    res = lb.ref("res", "ph -> ( ps -> ch )", s1, ref="com12", note="com12")
    return lb.build(res)


def prove_pm2_21fal(sys: Any) -> Any:
    """pm2.21fal: ph -> F. .  Hyps: ph -> ps, ph -> -. ps."""
    from skfd.proof import ProofBuilder

    lb = ProofBuilder(sys, "pm2.21fal")
    h1 = lb.hyp("pm2.21fal.1", "ph -> ps")
    h2 = lb.hyp("pm2.21fal.2", "ph -> -. ps")
    res = lb.ref("res", "ph -> F.", h1, h2, ref="pm2.21dd", note="pm2.21dd")
    return lb.build(res)


def prove_pm2_85(sys: Any) -> Any:
    """pm2.85: ((ph \/ ps) -> (ph \/ ch)) -> (ph \/ (ps -> ch)).
    Under df-or, this is pm2.86 with -.ph for ph.
    """
    from skfd.proof import ProofBuilder

    lb = ProofBuilder(sys, "pm2.85")
    res = lb.ref(
        "res",
        "(( -. ph -> ps ) -> ( -. ph -> ch )) -> ( -. ph -> ( ps -> ch ))",
        ref="pm2.86",
        note="pm2.86 (df-or)",
    )
    return lb.build(res)
