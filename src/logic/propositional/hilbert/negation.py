"""Negation and contraposition.

con1-con4 series, modus tollens family, explosion (pm2.21),
contradiction and reduction.
"""

from __future__ import annotations

from skfd.proof import Proof, ProofBuilder

from . import System


def prove_modus_tollens(sys: System) -> Proof:
    """Modus Tollens: φ → ψ, ¬ψ ⊢ ¬φ.

    Hyp 1: φ → ψ
    Hyp 2: ¬ψ
    Concl: ¬φ
    """
    lb = ProofBuilder(sys, "modus_tollens")

    h1 = lb.hyp("h1", "φ → ψ")
    h2 = lb.hyp("h2", "¬ ψ")

    s1 = lb.ref("s1", "( φ → ψ ) → ( ¬ ψ → ¬ φ )", ref="con3", note="con3")

    s2 = lb.mp("s2", h1, s1, "MP h1, s1")

    s3 = lb.mp("s3", h2, s2, "MP h2, s2")

    return lb.build(s3)


# -----------------------------------------------------------------------------
# Migration Expansion (set.mm compatibility)
# -----------------------------------------------------------------------------


def prove_con1(sys: System) -> Proof:
    """
    con1: ( ¬ φ → ψ ) → ( ¬ ψ → φ ).

    Contraposition.  Theorem *2.15 of [WhiteheadRussell] p. 102.  Its
         associated inference is ~ con1i .  (Contributed by NM, 29-Dec-1992.)
         (Proof shortened by Wolf Lammen, 12-Feb-2013.)

    """
    lb = ProofBuilder(sys, "con1")
    s1 = lb.ref("s1", "( ¬ φ → ψ ) → ( ¬ φ → ψ )", ref="id", note="id")
    res = lb.ref("res", "( ( ¬ φ → ψ ) → ( ¬ ψ → φ ) )", s1, ref="con1d", note="con1d")
    return lb.build(res)


def prove_con1d(sys: System) -> Proof:
    """
    con1d: φ → ( ¬ χ → ψ ). Hyp: φ → ( ¬ ψ → χ ).

    A contraposition deduction.
    """
    lb = ProofBuilder(sys, "con1d")
    h1 = lb.hyp("con1d.1", "φ → ( ¬ ψ → χ )")

    s1 = lb.ref("s1", "χ → ¬ ¬ χ", ref="notnot", note="notnot")
    s2 = lb.ref("s2", "φ → ( ¬ ψ → ¬ ¬ χ )", h1, s1, ref="syl6", note="syl6")
    res = lb.ref("res", "φ → ( ¬ χ → ψ )", s2, ref="con4d", note="con4d")
    return lb.build(res)


def prove_con2(sys: System) -> Proof:
    """
    con2: ( φ → ¬ ψ ) → ( ψ → ¬ φ ).

    Contraposition.  Theorem *2.03 of [WhiteheadRussell] p. 100.  (Contributed
         by NM, 29-Dec-1992.)  (Proof shortened by Wolf Lammen, 12-Feb-2013.)

    """
    lb = ProofBuilder(sys, "con2")
    s1 = lb.ref("s1", "( φ → ¬ ψ ) → ( φ → ¬ ψ )", ref="id", note="id")
    res = lb.ref("res", "( ( φ → ¬ ψ ) → ( ψ → ¬ φ ) )", s1, ref="con2d", note="con2d")
    return lb.build(res)


def prove_con2d(sys: System) -> Proof:
    """
    con2d: φ → ( χ → ¬ ψ ). Hyp: φ → ( ψ → ¬ χ ).

    A contraposition deduction.
    """
    lb = ProofBuilder(sys, "con2d")
    h1 = lb.hyp("con2d.1", "φ → ( ψ → ¬ χ )")

    s1 = lb.ref("s1", "¬ ¬ ψ → ψ", ref="notnotr", note="notnotr")
    s2 = lb.ref("s2", "φ → ( ¬ ¬ ψ → ¬ χ )", s1, h1, ref="syl5", note="syl5")
    res = lb.ref("res", "φ → ( χ → ¬ ψ )", s2, ref="con4d", note="con4d")
    return lb.build(res)


def prove_con3d(sys: System) -> Proof:
    """
    con3d: φ → ( ¬ χ → ¬ ψ ). Hyp: φ → ( ψ → χ ).
    """
    lb = ProofBuilder(sys, "con3d")
    h1 = lb.hyp("con3d.1", "φ → ( ψ → χ )")

    s1 = lb.ref("s1", "¬ ¬ ψ → ψ", ref="notnotr", note="notnotr")
    s2 = lb.ref("s2", "φ → ( ¬ ¬ ψ → χ )", s1, h1, ref="syl5", note="syl5")
    res = lb.ref("res", "φ → ( ¬ χ → ¬ ψ )", s2, ref="con1d", note="con1d")
    return lb.build(res)


def prove_con3(sys: System) -> Proof:
    """
    con3: ( φ → ψ ) → ( ¬ ψ → ¬ φ ).

    Contraposition.  Theorem *2.16 of [WhiteheadRussell] p. 103.  This was the
         fourth axiom of Frege, specifically Proposition 28 of [Frege1879] p. 43.
         Its associated inference is ~ con3i .  (Contributed by NM, 29-Dec-1992.)
         (Proof shortened by Wolf Lammen, 13-Feb-2013.)

    """
    lb = ProofBuilder(sys, "con3")
    s1 = lb.ref("s1", "( φ → ψ ) → ( φ → ψ )", ref="id", note="id")
    res = lb.ref("res", "( ( φ → ψ ) → ( ¬ ψ → ¬ φ ) )", s1, ref="con3d", note="con3d")
    return lb.build(res)


def prove_con4(sys: System) -> Proof:
    """
    con4: ( ¬ φ → ¬ ψ ) → ( ψ → φ ).

    Alias for ~ ax-3 to be used instead of it for labeling consistency.  Its
         associated inference is ~ con4i and its associated deduction is ~ con4d .
         (Contributed by BJ, 24-Dec-2020.)

    """
    lb = ProofBuilder(sys, "con4")
    stmt = lb.ref("res", "( ¬ φ → ¬ ψ ) → ( ψ → φ )", ref="A3", note="A3")
    return lb.build(stmt)


def prove_con4d(sys: System) -> Proof:
    """
    con4d: φ → ( χ → ψ ). Hyp: φ → ( ¬ ψ → ¬ χ ).

    Deduction associated with con4.
    """
    lb = ProofBuilder(sys, "con4d")
    h1 = lb.hyp("con4d.1", "φ → ( ¬ ψ → ¬ χ )")

    s1 = lb.ref(
        "s1",
        "( ¬ ψ → ¬ χ ) → ( χ → ψ )",
        ref="con4",
        note="con4",
    )
    s2 = lb.ref(
        "s2",
        "( ( ¬ ψ → ¬ χ ) → ( χ → ψ ) ) → ( φ → ( ( ¬ ψ → ¬ χ ) → ( χ → ψ ) ) )",
        ref="A1",
        note="A1",
    )
    s3 = lb.mp("s3", s1, s2, "MP s1, s2")
    s4 = lb.ref(
        "s4",
        "( φ → ( ( ¬ ψ → ¬ χ ) → ( χ → ψ ) ) ) → ( ( φ → ( ¬ ψ → ¬ χ ) ) → ( φ → ( χ → ψ ) ) )",
        ref="A2",
        note="A2",
    )
    s5 = lb.mp("s5", s3, s4, "MP s3, s4")
    res = lb.mp("res", h1, s5, "MP con4d.1, s5")
    return lb.build(res)


def prove_pm2_21(sys: System) -> Proof:
    """
    pm2.21: ¬ φ → ( φ → ψ ).

    From a wff and its negation, anything follows.  Theorem *2.21 of
         [WhiteheadRussell] p. 104.  Also called the Duns Scotus law.  Its commuted
         form is ~ pm2.24 and its associated inference is ~ pm2.21i .  (Contributed
         by NM, 29-Dec-1992.)  (Proof shortened by Wolf Lammen, 14-Sep-2012.)

    """
    lb = ProofBuilder(sys, "pm2.21")
    s1 = lb.ref("s1", "¬ φ → ¬ φ", ref="id", note="id")
    res = lb.ref("res", "¬ φ → ( φ → ψ )", s1, ref="pm2.21d", note="pm2.21d")
    return lb.build(res)


def prove_pm2_21d(sys: System) -> Proof:
    """
    pm2.21d: φ → ( ψ → χ ). Hyp: φ → ¬ ψ.

    Deduction associated with pm2.21.
    """
    lb = ProofBuilder(sys, "pm2.21d")
    h1 = lb.hyp("pm2.21d.1", "φ → ¬ ψ")
    s1 = lb.ref("s1", "φ → ( ¬ χ → ¬ ψ )", h1, ref="a1d", note="a1d")
    res = lb.ref("res", "φ → ( ψ → χ )", s1, ref="con4d", note="con4d")
    return lb.build(res)


def prove_pm2_24(sys: System) -> Proof:
    """
    pm2.24: φ → ( ¬ φ → ψ ).

    Theorem *2.24 of [WhiteheadRussell] p. 104.  Its associated inference is
         ~ pm2.24i .  Commuted form of ~ pm2.21 .  (Contributed by NM,
         3-Jan-2005.)

    """
    lb = ProofBuilder(sys, "pm2.24")
    s1 = lb.ref("s1", "¬ φ → ( φ → ψ )", ref="pm2.21", note="pm2.21")
    res = lb.ref("res", "φ → ( ¬ φ → ψ )", s1, ref="com12", note="com12")
    return lb.build(res)


def prove_conax1(sys: System) -> Proof:
    """
    conax1: ¬ ( φ → ψ ) → ¬ ψ.
    """
    lb = ProofBuilder(sys, "conax1")
    s1 = lb.ref("s1", "ψ → ( φ → ψ )", ref="A1", note="A1")
    s2 = lb.ref(
        "s2",
        "( ψ → ( φ → ψ ) ) → ( ¬ ( φ → ψ ) → ¬ ψ )",
        ref="con3",
        note="con3",
    )
    res = lb.mp("res", s1, s2, "MP s1, s2")
    return lb.build(res)


def prove_pm2_521g(sys: System) -> Proof:
    """
    pm2.521g: ¬ ( φ → ψ ) → ( ψ → χ ).
    """
    lb = ProofBuilder(sys, "pm2.521g")
    h1 = lb.ref("h1", "¬ ( φ → ψ ) → ¬ ψ", ref="conax1", note="conax1")
    res = lb.ref("res", "¬ ( φ → ψ ) → ( ψ → χ )", h1, ref="pm2.21d", note="pm2.21d")
    return lb.build(res)


def prove_pm2_521(sys: System) -> Proof:
    """
    pm2.521: ¬ ( φ → ψ ) → ( ψ → φ ).
    """
    lb = ProofBuilder(sys, "pm2.521")
    res = lb.ref("res", "¬ ( φ → ψ ) → ( ψ → φ )", ref="pm2.521g", note="pm2.521g")
    return lb.build(res)


def rove_con1i(sys: System) -> Proof:
    """
    con1i: ¬ ψ → φ. Hyp: ¬ φ → ψ.

    A contraposition inference.  Inference associated with ~ con1 .  Its
           associated inference is ~ mt3 .  (Contributed by NM, 3-Jan-1993.)
           (Proof shortened by Mel L. O'Cat, 28-Nov-2008.)  (Proof shortened by
           Wolf Lammen, 19-Jun-2013.)

    """
    lb = ProofBuilder(sys, "con1i")
    hyp = lb.hyp("prove_con1i.h", "¬ φ → ψ")
    s1 = lb.ref("s1", "( ¬ φ → ψ ) → ( ¬ ψ → φ )", ref="con1", note="con1")
    res = lb.mp("res", hyp, s1, "MP hyp, s1")
    return lb.build(res)


def prove_con2i(sys: System) -> Proof:
    """
    con2i: ψ → ¬ φ. Hyp: φ → ¬ ψ.

    A contraposition inference.  Its associated inference is ~ mt2 .
           (Contributed by NM, 10-Jan-1993.)  (Proof shortened by Mel L. O'Cat,
           28-Nov-2008.)  (Proof shortened by Wolf Lammen, 13-Jun-2013.)

    """
    lb = ProofBuilder(sys, "con2i")
    hyp = lb.hyp("prove_con2i.h", "φ → ¬ ψ")
    s1 = lb.ref("s1", "( φ → ¬ ψ ) → ( ψ → ¬ φ )", ref="con2", note="con2")
    res = lb.mp("res", hyp, s1, "MP hyp, s1")
    return lb.build(res)


def prove_con3i(sys: System) -> Proof:
    """
    con3i: ¬ ψ → ¬ φ. Hyp: φ → ψ.

    A contraposition inference.  Inference associated with ~ con3 .  Its
           associated inference is ~ mto .  (Contributed by NM, 3-Jan-1993.)
           (Proof shortened by Wolf Lammen, 20-Jun-2013.)

    """
    lb = ProofBuilder(sys, "con3i")
    hyp = lb.hyp("prove_con3i.h", "φ → ψ")
    s1 = lb.ref("s1", "( φ → ψ ) → ( ¬ ψ → ¬ φ )", ref="con3", note="con3")
    res = lb.mp("res", hyp, s1, "MP hyp, s1")
    return lb.build(res)


def prove_con4i(sys: System) -> Proof:
    """
    con4i: ψ → φ. Hyp: ¬ φ → ¬ ψ.

    Inference associated with ~ con4 .  Its associated inference is ~ mt4 .

           Remark: this can also be proved using ~ notnot followed by ~ nsyl2 ,
           giving a shorter proof but depending on more axioms (namely, ~ ax-1 and
           ~ ax-2 ).  (Contributed by NM, 29-Dec-1992.)

    """
    lb = ProofBuilder(sys, "con4i")
    hyp = lb.hyp("prove_con4i.h", "¬ φ → ¬ ψ")
    s1 = lb.ref("s1", "( ¬ φ → ¬ ψ ) → ( ψ → φ )", ref="con4", note="con4")
    res = lb.mp("res", hyp, s1, "MP hyp, s1")
    return lb.build(res)


def prove_mt4d(sys: System) -> Proof:
    """
    mt4d: φ → χ. Hyp1: φ → ψ, Hyp2: φ → ( ¬ χ → ¬ ψ ).

    Modus tollens deduction.  Deduction form of mt4.
    """
    lb = ProofBuilder(sys, "mt4d")
    h1 = lb.hyp("mt4d.1", "φ → ψ")
    h2 = lb.hyp("mt4d.2", "φ → ( ¬ χ → ¬ ψ )")
    s1 = lb.ref("s1", "φ → ( ψ → χ )", h2, ref="con4d", note="con4d")
    res = lb.ref("res", "φ → χ", h1, s1, ref="mpd", note="mpd")
    return lb.build(res)


# -----------------------------------------------------------------------------
# Optional: debug printer
# -----------------------------------------------------------------------------


# =============================================================================
# gen0_pod0: pm1.4, pm2.38, pm2.36
# =============================================================================


def prove_pm2_45(sys: System) -> Proof:
    """pm2.45: ¬(φ ∨ ψ) → ¬φ.

    Theorem *2.45 of [WhiteheadRussell] p. 106.
    (Contributed by NM, 3-Jan-2005.)
    Under df-or: pm2.24(φ,ψ) = φ→(¬φ→ψ) = orc.
    con3i applied to pm2.24 gives ¬(¬φ→ψ)→¬φ.
    """
    lb = ProofBuilder(sys, "pm2.45")
    s1 = lb.ref("s1", "( φ → ( -. φ → ψ ) )", ref="pm2.24", note="pm2.24 (orc)")
    res = lb.ref("res", "( -. ( -. φ → ψ ) → -. φ )", s1, ref="con3i", note="con3i(pm2.24)")
    return lb.build(res)


def prove_pm2_46(sys: System) -> Proof:
    """pm2.46: ¬(φ ∨ ψ) → ¬ψ.

    Theorem *2.46 of [WhiteheadRussell] p. 106.
    (Contributed by NM, 3-Jan-2005.)
    Under df-or: olc = ψ→(¬φ→ψ), an ax-1 instance.
    con3i applied gives ¬(¬φ→ψ)→¬ψ.
    """
    lb = ProofBuilder(sys, "pm2.46")
    s1 = lb.ref("s1", "( ψ → ( -. φ → ψ ) )", ref="A1", note="A1 (olc df-or)")
    res = lb.ref("res", "( -. ( -. φ → ψ ) → -. ψ )", s1, ref="con3i", note="con3i(olc)")
    return lb.build(res)


# ============================================================
# pm2.47, pm2.48, pm2.49 (negated disjunction with one branch)
# ============================================================


def prove_pm2_47(sys: System) -> Proof:
    """pm2.47: ¬(φ ∨ ψ) → (¬φ ∨ ψ).

    Theorem *2.47 of [WhiteheadRussell] p. 106.
    (Contributed by NM, 3-Jan-2005.)
    Under df-or: ¬(¬φ→ψ)→(¬¬φ→ψ).
    pm2.45 gives ¬(¬φ→ψ)→¬φ.
    A1(¬φ,ψ): ¬φ→(¬¬φ→ψ).
    syl: ¬(¬φ→ψ)→(¬¬φ→ψ).
    """
    lb = ProofBuilder(sys, "pm2.47")
    s1 = lb.ref("s1", "( -. ( -. φ → ψ ) → -. φ )", ref="pm2.45", note="pm2.45")
    s2 = lb.ref("s2", "( -. φ → ( -. -. φ → ψ ) )", ref="A1", note="A1 (-.φ,ψ)")
    res = lb.ref(
        "res",
        "( -. ( -. φ → ψ ) → ( -. -. φ → ψ ) )",
        s1,
        s2,
        ref="syl",
        note="syl(pm2.45, A1)",
    )
    return lb.build(res)


def prove_pm2_48(sys: System) -> Proof:
    """pm2.48: ¬(φ ∨ ψ) → (φ ∨ ¬ψ).

    Theorem *2.48 of [WhiteheadRussell] p. 106.
    (Contributed by NM, 3-Jan-2005.)
    Under df-or: ¬(¬φ→ψ)→(¬φ→¬ψ).
    pm2.46 gives ¬(¬φ→ψ)→¬ψ.
    A1(¬ψ,¬φ): ¬ψ→(¬φ→¬ψ).
    syl: ¬(¬φ→ψ)→(¬φ→¬ψ).
    """
    lb = ProofBuilder(sys, "pm2.48")
    s1 = lb.ref("s1", "( -. ( -. φ → ψ ) → -. ψ )", ref="pm2.46", note="pm2.46")
    s2 = lb.ref("s2", "( -. ψ → ( -. φ → -. ψ ) )", ref="A1", note="A1 (-.ψ,-.φ)")
    res = lb.ref(
        "res",
        "( -. ( -. φ → ψ ) → ( -. φ → -. ψ ) )",
        s1,
        s2,
        ref="syl",
        note="syl(pm2.46, A1)",
    )
    return lb.build(res)


def prove_pm2_49(sys: System) -> Proof:
    """pm2.49: ¬(φ ∨ ψ) → (¬φ ∨ ¬ψ).

    Theorem *2.49 of [WhiteheadRussell] p. 106.
    (Contributed by NM, 3-Jan-2005.)
    Under df-or: ¬(¬φ→ψ)→(¬¬φ→¬ψ).
    Same as pm2.48 with A1(¬ψ,¬¬φ).
    """
    lb = ProofBuilder(sys, "pm2.49")
    s1 = lb.ref("s1", "( -. ( -. φ → ψ ) → -. ψ )", ref="pm2.46", note="pm2.46")
    s2 = lb.ref("s2", "( -. ψ → ( -. -. φ → -. ψ ) )", ref="A1", note="A1 (-.ψ,-.-.φ)")
    res = lb.ref(
        "res",
        "( -. ( -. φ → ψ ) → ( -. -. φ → -. ψ ) )",
        s1,
        s2,
        ref="syl",
        note="syl(pm2.46, A1)",
    )
    return lb.build(res)


# ============================================================
# pm2.51, pm2.52 (negation of implication)
# ============================================================


def prove_pm2_51(sys: System) -> Proof:
    """pm2.51: ¬(φ → ψ) → (φ → ¬ψ).

    Theorem *2.51 of [WhiteheadRussell] p. 107.
    (Contributed by NM, 3-Jan-2005.)
    conax1(φ,ψ): ¬(φ→ψ)→¬ψ.
    A1(¬ψ,φ): ¬ψ→(φ→¬ψ).
    syl: ¬(φ→ψ)→(φ→¬ψ).
    """
    lb = ProofBuilder(sys, "pm2.51")
    s1 = lb.ref("s1", "( -. ( φ → ψ ) → -. ψ )", ref="conax1", note="conax1")
    s2 = lb.ref("s2", "( -. ψ → ( φ → -. ψ ) )", ref="A1", note="A1")
    res = lb.ref(
        "res", "( -. ( φ → ψ ) → ( φ → -. ψ ) )", s1, s2, ref="syl", note="syl(conax1, A1)"
    )
    return lb.build(res)


def prove_pm2_52(sys: System) -> Proof:
    """pm2.52: ¬(φ → ψ) → (¬φ → ¬ψ).

    Theorem *2.52 of [WhiteheadRussell] p. 107.
    (Contributed by NM, 3-Jan-2005.)
    (Proof shortened by Wolf Lammen, 8-Oct-2012.)
    conax1(φ,ψ): ¬(φ→ψ)→¬ψ.
    A1(¬ψ,¬φ): ¬ψ→(¬φ→¬ψ).
    syl: ¬(φ→ψ)→(¬φ→¬ψ).
    """
    lb = ProofBuilder(sys, "pm2.52")
    s1 = lb.ref("s1", "( -. ( φ → ψ ) → -. ψ )", ref="conax1", note="conax1")
    s2 = lb.ref("s2", "( -. ψ → ( -. φ → -. ψ ) )", ref="A1", note="A1")
    res = lb.ref(
        "res",
        "( -. ( φ → ψ ) → ( -. φ → -. ψ ) )",
        s1,
        s2,
        ref="syl",
        note="syl(conax1, A1)",
    )
    return lb.build(res)


# ============================================================
# pm2.37 (implication through disjunction)
# ============================================================


def prove_pm2_53(sys: System) -> Proof:
    """pm2.53: (φ ∨ ψ) → (¬φ → ψ).

    Theorem *2.53 of [WhiteheadRussell] p. 107.
    (Contributed by NM, 3-Jan-2005.)
    Under df-or: trivially id.
    """
    lb = ProofBuilder(sys, "pm2.53")
    res = lb.ref("res", "( -. φ → ψ ) → ( -. φ → ψ )", ref="id", note="id (trivial under df-or)")
    return lb.build(res)


def prove_pm2_54(sys: System) -> Proof:
    """pm2.54: (¬φ → ψ) → (φ ∨ ψ).

    Theorem *2.54 of [WhiteheadRussell] p. 107.
    (Contributed by NM, 3-Jan-2005.)
    Under df-or: trivially id.
    """
    lb = ProofBuilder(sys, "pm2.54")
    res = lb.ref("res", "( -. φ → ψ ) → ( -. φ → ψ )", ref="id", note="id (trivial under df-or)")
    return lb.build(res)


# ============================================================
# pm2.45, pm2.46 (negated disjunction elimination)
# ============================================================


def prove_pm2_62(sys: System) -> Proof:
    """pm2.62: (φ ∨ ψ) → ((φ → ψ) → ψ).

    Theorem *2.62 of [WhiteheadRussell] p. 107.
    (Contributed by NM, 3-Jan-2005.)
    pm2.61: (φ→ψ)→((¬φ→ψ)→ψ).
    com12 swaps antecedents.
    """
    lb = ProofBuilder(sys, "pm2.62")
    s1 = lb.ref("s1", "( ( φ → ψ ) → ( ( -. φ → ψ ) → ψ ) )", ref="pm2.61", note="pm2.61")
    res = lb.ref(
        "res",
        "( ( -. φ → ψ ) → ( ( φ → ψ ) → ψ ) )",
        s1,
        ref="com12",
        note="com12(pm2.61)",
    )
    return lb.build(res)


# ============================================================
# pm2.64 (disjunction with negated disjunct)
# ============================================================


def prove_pm2_63(sys: System) -> Proof:
    """Theorem *2.63 of [WhiteheadRussell] p. 107.
    ( φ ∨ ψ ) → ( ( -. φ ∨ ψ ) → ψ ).
    (Contributed by NM, 3-Jan-2005.)
    set.mm proof: pm2.53 idd jaod.
    Under df-or: ( -. φ → ψ ) → ( ( -. -. φ → ψ ) → ψ ).
    Derived: com12(syl(mp(notnot, imim1), pm2.61))."""
    lb = ProofBuilder(sys, "pm2.63")
    s_notnot = lb.ref("s_notnot", "φ → -. -. φ", ref="notnot", note="notnot")
    s_imim1 = lb.ref(
        "s_imim1",
        "( φ → -. -. φ ) → ( ( -. -. φ → ψ ) → ( φ → ψ ) )",
        ref="imim1",
        note="imim1(notnot)",
    )
    s_inner = lb.mp("s_inner", s_notnot, s_imim1, note="MP: (-.-.φ→ψ)→(φ→ψ)")
    s_pm61 = lb.ref("s_pm61", "( φ → ψ ) → ( ( -. φ → ψ ) → ψ )", ref="pm2.61", note="pm2.61")
    s_syl = lb.ref(
        "s_syl",
        "( -. -. φ → ψ ) → ( ( -. φ → ψ ) → ψ )",
        s_inner,
        s_pm61,
        ref="syl",
        note="syl(mp(notnot,imim1), pm2.61)",
    )
    res = lb.ref(
        "res",
        "( -. φ → ψ ) → ( ( -. -. φ → ψ ) → ψ )",
        s_syl,
        ref="com12",
        note="com12(syl(...))",
    )
    return lb.build(res)


def prove_pm2_64(sys: System) -> Proof:
    """pm2.64: (φ ∨ ψ) → ((φ ∨ ¬ψ) → φ).

    Theorem *2.64 of [WhiteheadRussell] p. 107.
    (Contributed by NM, 3-Jan-2005.)
    pm2.65: (¬φ→ψ)→((¬φ→¬ψ)→¬¬φ).
    notnotr: ¬¬φ→φ.
    syl6: chains them.
    """
    lb = ProofBuilder(sys, "pm2.64")
    s_pm65 = lb.ref(
        "s_pm65",
        "( ( -. φ → ψ ) → ( ( -. φ → -. ψ ) → -. -. φ ) )",
        ref="pm2.65",
        note="pm2.65",
    )
    s_nn = lb.ref("s_nn", "( -. -. φ → φ )", ref="notnotr", note="notnotr")
    res = lb.ref(
        "res",
        "( ( -. φ → ψ ) → ( ( -. φ → -. ψ ) → φ ) )",
        s_pm65,
        s_nn,
        ref="syl6",
        note="syl6(pm2.65, notnotr)",
    )
    return lb.build(res)


def prove_con1i(sys: System) -> Proof:
    """
    con1i: ¬ ψ → φ. Hyp: ¬ φ → ψ.

    A contraposition inference.  Inference associated with ~ con1 .  Its
           associated inference is ~ mt3 .  (Contributed by NM, 3-Jan-1993.)
           (Proof shortened by Mel L. O'Cat, 28-Nov-2008.)  (Proof shortened by
           Wolf Lammen, 19-Jun-2013.)

    """
    lb = ProofBuilder(sys, "con1i")
    hyp = lb.hyp("prove_con1i.h", "¬ φ → ψ")
    s1 = lb.ref("s1", "( ¬ φ → ψ ) → ( ¬ ψ → φ )", ref="con1", note="con1")
    res = lb.mp("res", hyp, s1, "MP hyp, s1")
    return lb.build(res)


def prove_mt2(sys: System) -> Proof:
    """mt2: ¬φ. Hyp: ψ, φ → ¬ψ. (Contributed by NM, 19-Aug-1993.)"""
    lb = ProofBuilder(sys, "mt2")
    h1 = lb.hyp("mt2.1", "ψ")
    h2 = lb.hyp("mt2.2", "φ → ¬ ψ")
    s1 = lb.ref("s1", "φ → ψ", h1, ref="a1i", note="a1i")
    res = lb.ref("res", "¬ φ", s1, h2, ref="pm2.65i", note="pm2.65i")
    return lb.build(res)


def prove_mt3(sys: System) -> Proof:
    """mt3: φ. Hyp: ¬ψ, ¬φ → ψ. (Contributed by NM, 18-May-1994.)"""
    lb = ProofBuilder(sys, "mt3")
    h1 = lb.hyp("mt3.1", "¬ ψ")
    h2 = lb.hyp("mt3.2", "¬ φ → ψ")
    s1 = lb.ref("s1", "¬ ¬ φ", h1, h2, ref="mto", note="mto")
    res = lb.ref("res", "φ", s1, ref="notnotri", note="notnotri")
    return lb.build(res)


def prove_nsyl(sys: System) -> Proof:
    """nsyl: φ → ¬χ. Hyp: φ → ¬ψ, χ → ψ. (Contributed by NM, 31-Dec-1993.)"""
    lb = ProofBuilder(sys, "nsyl")
    h1 = lb.hyp("nsyl.1", "φ → ¬ ψ")
    h2 = lb.hyp("nsyl.2", "χ → ψ")
    s1 = lb.ref("s1", "χ → ¬ φ", h1, h2, ref="nsyl3", note="nsyl3")
    res = lb.ref("res", "φ → ¬ χ", s1, ref="con2i", note="con2i")
    return lb.build(res)


def prove_nsyl2(sys: System) -> Proof:
    """nsyl2: φ → χ. Hyp: φ → ¬ψ, ¬χ → ψ. (Contributed by NM, 26-Jun-1994.)"""
    lb = ProofBuilder(sys, "nsyl2")
    h1 = lb.hyp("nsyl2.1", "φ → ¬ ψ")
    h2 = lb.hyp("nsyl2.2", "¬ χ → ψ")
    s1 = lb.ref("s1", "¬ χ → ¬ φ", h1, h2, ref="nsyl3", note="nsyl3")
    res = lb.ref("res", "φ → χ", s1, ref="con4i", note="con4i")
    return lb.build(res)


def prove_nsyl3(sys: System) -> Proof:
    """nsyl3: χ → ¬φ. Hyp: φ → ¬ψ, χ → ψ. (Contributed by NM, 1-Dec-1995.)"""
    lb = ProofBuilder(sys, "nsyl3")
    h1 = lb.hyp("nsyl3.1", "φ → ¬ ψ")
    h2 = lb.hyp("nsyl3.2", "χ → ψ")
    s1 = lb.ref("s1", "χ → ( φ → ¬ ψ )", h1, ref="a1i", note="a1i")
    res = lb.ref("res", "χ → ¬ φ", h2, s1, ref="mt2d", note="mt2d")
    return lb.build(res)


def prove_pm2_61(sys: System) -> Proof:
    """pm2.61: (φ → ψ) → ((¬φ → ψ) → ψ).
    (Contributed by NM, 5-Apr-1994.)"""
    lb = ProofBuilder(sys, "pm2.61")
    s1 = lb.ref("s1", "( ¬ φ → ψ ) → ( ( φ → ψ ) → ψ )", ref="pm2.6", note="pm2.6")
    res = lb.ref("res", "( φ → ψ ) → ( ( ¬ φ → ψ ) → ψ )", s1, ref="com12", note="com12")
    return lb.build(res)


def prove_pm2_65(sys: System) -> Proof:
    """pm2.65: (φ → ψ) → ((φ → ¬ψ) → ¬φ).

    Theorem *2.65 of [WhiteheadRussell] p. 107.
    Proof by contradiction ("reductio ad absurdum").
    (Contributed by NM, 4-Jan-1993.)
    (Proof shortened by Wolf Lammen, 5-Mar-2013.)
    set.mm proof: idd con3 jad.
    """
    lb = ProofBuilder(sys, "pm2.65")
    s1 = lb.ref("s1", "( ( φ → ψ ) → ( -. φ → -. φ ) )", ref="idd", note="idd")
    s2 = lb.ref("s2", "( ( φ → ψ ) → ( -. ψ → -. φ ) )", ref="con3", note="con3")
    res = lb.ref("res", "( ( φ → ψ ) → ( ( φ → -. ψ ) → -. φ ) )", s1, s2, ref="jad", note="jad")
    return lb.build(res)


def prove_pm2_65da(sys: System) -> Proof:
    """pm2.65da: ( φ → -. ψ ).

    Hypotheses: ( ( φ ∧ ψ ) → χ ), ( ( φ ∧ ψ ) → -. χ ).
    Deduction for proof by contradiction (conjunction form).
    (Contributed by NM, 12-Jun-2014.)

    Using df-an expansion: (φ ∧ ψ) is -. ( φ → -. ψ ).
    Proof: pm2.65i(h1, h2) → -.-.(φ → -.ψ) ; notnotri → (φ → -.ψ).
    pm2.65i needs explicit args (ψ not in conclusion).
    """
    lb = ProofBuilder(sys, "pm2.65da")
    h1 = lb.hyp("pm2.65da.1", "( -. ( φ → -. ψ ) → χ )")
    h2 = lb.hyp("pm2.65da.2", "( -. ( φ → -. ψ ) → -. χ )")
    s1 = lb.ref("s1", "-. -. ( φ → -. ψ )", h1, h2, ref="pm2.65i", note="pm2.65i h1 h2")
    res = lb.ref("res", "φ → -. ψ", s1, ref="notnotri", note="notnotri")
    return lb.build(res)


def prove_pm2_65ni(sys: System) -> Proof:
    """pm2.65ni: φ.

    Hypotheses: ( -. φ → ψ ), ( -. φ → -. ψ ).
    Inference rule for proof by contradiction.
    (Contributed by Glauco Siliprandi, 5-Apr-2020.)

    Proof: pm2.65i(h1, h2) → -. -. φ ; notnotri → φ.
    """
    lb = ProofBuilder(sys, "pm2.65ni")
    h1 = lb.hyp("pm2.65ni.1", "-. φ → ψ")
    h2 = lb.hyp("pm2.65ni.2", "-. φ → -. ψ")
    s1 = lb.ref("s1", "-. -. φ", h1, h2, ref="pm2.65i", note="pm2.65i")
    res = lb.ref("res", "φ", s1, ref="notnotri", note="notnotri")
    return lb.build(res)


def prove_pm2_61ii(sys: System) -> Proof:
    """pm2.61ii: χ.

    Hypotheses: ( -. φ → ( -. ψ → χ ) ), ( φ → χ ), ( ψ → χ ).
    Inference eliminating two antecedents.
    (Contributed by NM, 4-Jan-1993.) (Proof shortened by Josh Purinton, 29-Dec-2000.)

    Proof: a1i(h3) → (-.φ → (ψ → χ)) ; pm2.61d(that, h1) → (-.φ → χ) ; pm2.61i(h2, that) → χ.
    pm2.61d needs explicit args (ψ not in conclusion).
    """
    lb = ProofBuilder(sys, "pm2.61ii")
    h1 = lb.hyp("pm2.61ii.1", "-. φ → ( -. ψ → χ )")
    h2 = lb.hyp("pm2.61ii.2", "φ → χ")
    h3 = lb.hyp("pm2.61ii.3", "ψ → χ")
    s1 = lb.ref("s1", "-. φ → ( ψ → χ )", h3, ref="a1i", note="a1i h3")
    s2 = lb.ref("s2", "-. φ → χ", s1, h1, ref="pm2.61d", note="pm2.61d s1 h1")
    res = lb.ref("res", "χ", h2, s2, ref="pm2.61i", note="pm2.61i")
    return lb.build(res)


def prove_pm2_61iii(sys: System) -> Proof:
    """pm2.61iii: θ.

    Hypotheses: ( -. φ → ( -. ψ → ( -. χ → θ ) ) ), ( φ → θ ), ( ψ → θ ), ( χ → θ ).
    Inference eliminating three antecedents.
    (Contributed by NM, 2-Jan-2002.) (Proof shortened by Wolf Lammen, 22-Sep-2013.)

    Proof: a1d on hyp2/hyp3 gives (φ → (-.χ → θ)) and (ψ → (-.χ → θ)).
    Then pm2.61ii logic (inlined) gives (-.χ → θ).
    Finally pm2.61i with hyp4 gives θ.
    """
    lb = ProofBuilder(sys, "pm2.61iii")
    h1 = lb.hyp("pm2.61iii.1", "-. φ → ( -. ψ → ( -. χ → θ ) )")
    h2 = lb.hyp("pm2.61iii.2", "φ → θ")
    h3 = lb.hyp("pm2.61iii.3", "ψ → θ")
    h4 = lb.hyp("pm2.61iii.4", "χ → θ")
    # a1d on h2 and h3 to add ¬χ antecedent
    s_a1d2 = lb.ref("s_a1d2", "φ → ( -. χ → θ )", h2, ref="a1d", note="a1d h2")
    s_a1d3 = lb.ref("s_a1d3", "ψ → ( -. χ → θ )", h3, ref="a1d", note="a1d h3")
    # inlined pm2.61ii logic with X=φ, Y=ψ, Z=(¬χ → θ)
    s_ii_a1i = lb.ref("s_ii_a1i", "-. φ → ( ψ → ( -. χ → θ ) )", s_a1d3, ref="a1i", note="a1i")
    s_ii_pm2d = lb.ref(
        "s_ii_pm2d", "-. φ → ( -. χ → θ )", s_ii_a1i, h1, ref="pm2.61d", note="pm2.61d"
    )
    s_notch_th = lb.ref("s_notch_th", "-. χ → θ", s_a1d2, s_ii_pm2d, ref="pm2.61i", note="pm2.61i")
    # final pm2.61i
    res = lb.ref("res", "θ", h4, s_notch_th, ref="pm2.61i", note="pm2.61i")
    return lb.build(res)


def prove_pm2_61nii(sys: System) -> Proof:
    """pm2.61nii: χ.

    Hypotheses: ( φ → ( ψ → χ ) ), ( -. φ → χ ), ( -. ψ → χ ).
    Inference eliminating two antecedents.
    (Contributed by NM, 13-Jul-2005.) (Proof shortened by Andrew Salmon, 25-May-2011.)

    Proof: pm2.61d1(h1, h3) → (φ → χ) ; pm2.61i(that, h2) → χ.
    pm2.61d1 needs explicit args (ψ not in conclusion).
    """
    lb = ProofBuilder(sys, "pm2.61nii")
    h1 = lb.hyp("pm2.61nii.1", "φ → ( ψ → χ )")
    h2 = lb.hyp("pm2.61nii.2", "-. φ → χ")
    h3 = lb.hyp("pm2.61nii.3", "-. ψ → χ")
    s1 = lb.ref("s1", "φ → χ", h1, h3, ref="pm2.61d1", note="pm2.61d1 h1 h3")
    res = lb.ref("res", "χ", s1, h2, ref="pm2.61i", note="pm2.61i")
    return lb.build(res)


def prove_jad(sys: System) -> Proof:
    """jad: φ → ((ψ → χ) → θ). Hyp: φ → (¬ψ → θ), φ → (χ → θ). (Contributed by NM, 11-Jul-2004.)"""
    lb = ProofBuilder(sys, "jad")
    h1 = lb.hyp("jad.1", "φ → ( ¬ ψ → θ )")
    h2 = lb.hyp("jad.2", "φ → ( χ → θ )")
    s1 = lb.ref("s1", "¬ ψ → ( φ → θ )", h1, ref="com12", note="com12")
    s2 = lb.ref("s2", "χ → ( φ → θ )", h2, ref="com12", note="com12")
    s3 = lb.ref("s3", "( ψ → χ ) → ( φ → θ )", s1, s2, ref="ja", note="ja")
    res = lb.ref("res", "φ → ( ( ψ → χ ) → θ )", s3, ref="com12", note="com12")
    return lb.build(res)


def prove_jarl(sys: System) -> Proof:
    """jarl: ((φ → ψ) → χ) → (¬φ → χ).

    "Jar" with left antecedent negated (forward "ja" partial converse).
    (Contributed by NM, 25-Jun-1993.)
    set.mm proof: pm2.21 imim1i.

    Derivation: pm2.21 gives ¬φ → (φ → ψ). Then imim1 chains
    this to get ((φ → ψ) → χ) → (¬φ → χ).
    """
    lb = ProofBuilder(sys, "jarl")
    s1 = lb.ref("s1", "( -. φ → ( φ → ψ ) )", ref="pm2.21", note="pm2.21")
    s2 = lb.ref(
        "s2",
        "( ( -. φ → ( φ → ψ ) ) → ( ( ( φ → ψ ) → χ ) → ( -. φ → χ ) ) )",
        ref="imim1",
        note="imim1",
    )
    res = lb.mp("res", s1, s2, note="MP pm2.21, imim1")
    return lb.build(res)


def prove_mt2d(sys: System) -> Proof:
    """mt2d: φ → ¬ψ. Hyp: φ → χ, φ → (ψ → ¬χ). (Contributed by NM, 16-Apr-1995.)"""
    lb = ProofBuilder(sys, "mt2d")
    h1 = lb.hyp("mt2d.1", "φ → χ")
    h2 = lb.hyp("mt2d.2", "φ → ( ψ → ¬ χ )")
    s1 = lb.ref("s1", "φ → ( χ → ¬ ψ )", h2, ref="con2d", note="con2d")
    res = lb.ref("res", "φ → ¬ ψ", h1, s1, ref="mpd", note="mpd")
    return lb.build(res)


def prove_mt4(sys: System) -> Proof:
    """mt4: ψ.  Hyps: φ, -. ψ → -. φ.

    The rule of modus tollens.  Inference associated with con4i.
    (Contributed by Wolf Lammen, 12-May-2013.)
    set.mm proof: con4i ax-mp.
    """
    lb = ProofBuilder(sys, "mt4")
    h1 = lb.hyp("mt4.1", "φ")
    h2 = lb.hyp("mt4.2", "( -. ψ → -. φ )")
    s1 = lb.ref("s1", "( φ → ψ )", h2, ref="con4i", note="con4i")
    res = lb.mp("res", h1, s1, "MP hyp1, s1")
    return lb.build(res)


def prove_mto(sys: System) -> Proof:
    """mto: ¬φ. Hyp: ¬ψ, φ → ψ. (Contributed by NM, 2-Sep-1993.)"""
    lb = ProofBuilder(sys, "mto")
    h1 = lb.hyp("mto.1", "¬ ψ")
    h2 = lb.hyp("mto.2", "φ → ψ")
    s1 = lb.ref("s1", "φ → ¬ ψ", h1, ref="a1i", note="a1i")
    res = lb.ref("res", "¬ φ", h2, s1, ref="pm2.65i", note="pm2.65i")
    return lb.build(res)


def prove_notnotri(sys: System) -> Proof:
    """notnotri: φ. Hyp: ¬¬φ. (Contributed by NM, 15-Feb-1993.)"""
    lb = ProofBuilder(sys, "notnotri")
    h = lb.hyp("notnotri.1", "¬ ¬ φ")
    s1 = lb.ref("s1", "¬ ¬ φ → φ", ref="notnotr", note="notnotr")
    res = lb.mp("res", h, s1, note="MP notnotri.1, s1")
    return lb.build(res)


def prove_nsyl4(sys: System) -> Proof:
    """nsyl4: -. χ → ψ. Hyps: φ → ψ, -. φ → χ.

    (Contributed by Wolf Lammen, 20-May-2024.)
    set.mm proof: con1i syl.
    """
    lb = ProofBuilder(sys, "nsyl4")
    h1 = lb.hyp("nsyl4.1", "( φ → ψ )")
    h2 = lb.hyp("nsyl4.2", "( -. φ → χ )")
    s1 = lb.ref("s1", "( -. χ → φ )", h2, ref="con1i", note="con1i")
    res = lb.ref("res", "( -. χ → ψ )", s1, h1, ref="syl", note="syl")
    return lb.build(res)


def prove_pm2_01d(sys: System) -> Proof:
    """pm2.01d: φ → -. ψ.  Hyp: φ → (ψ → -. ψ).

    Deduction based on reductio ad absurdum.
    (Contributed by NM, 18-Aug-1993.)
    set.mm proof: id pm2.61d1.
    """
    lb = ProofBuilder(sys, "pm2.01d")
    h1 = lb.hyp("pm2.01d.1", "( φ → ( ψ → -. ψ ) )")
    # id : (¬ ψ → ¬ ψ)
    s_id = lb.ref("s_id", "( -. ψ → -. ψ )", ref="id", note="id")
    # pm2.61d1(h1, s_id): φ → ¬ ψ
    res = lb.ref("res", "( φ → -. ψ )", h1, s_id, ref="pm2.61d1", note="pm2.61d1")
    return lb.build(res)


def prove_pm2_18i(sys: System) -> Proof:
    """pm2.18i: φ.  Hyp: -. φ → φ.

    Inference associated with the Clavius law pm2.18.
    (Contributed by BJ, 30-Mar-2020.)
    set.mm proof: pm2.18 ax-mp.
    """
    lb = ProofBuilder(sys, "pm2.18i")
    h1 = lb.hyp("pm2.18i.1", "( -. φ → φ )")
    s1 = lb.ref("s1", "( ( -. φ → φ ) → φ )", ref="pm2.18", note="pm2.18")
    res = lb.mp("res", h1, s1, "MP hyp, pm2.18")
    return lb.build(res)


def prove_pm2_21dd(sys: System) -> Proof:
    """pm2.21dd: φ → χ.  Hyps: φ → ψ, φ → -. ψ.

    A contradiction implies anything.  Deduction from pm2.21.
    (Contributed by Mario Carneiro, 9-Feb-2017.)
    set.mm proof: pm2.65i pm2.21i.
    """
    lb = ProofBuilder(sys, "pm2.21dd")
    h1 = lb.hyp("pm2.21dd.1", "( φ → ψ )")
    h2 = lb.hyp("pm2.21dd.2", "( φ → -. ψ )")
    s1 = lb.ref("s1", "( -. φ )", h1, h2, ref="pm2.65i", note="pm2.65i")
    res = lb.ref("res", "( φ → χ )", s1, ref="pm2.21i", note="pm2.21i")
    return lb.build(res)


def prove_pm2_21ddALT(sys: System) -> Proof:
    """pm2.21ddALT: φ → χ.  Alternate proof of pm2.21dd.

    set.mm label: pm2.21ddALT
    Statement: φ → χ  (given φ → ψ and φ → -. ψ)
    Natural language: From a wff and its negation, anything follows (alternate proof).
    Contributed by Mario Carneiro, 9-Feb-2017.
    Proof sketch: Apply pm2.21d to get φ → (ψ → χ) from h2 (φ → -.ψ),
    then mpd with h1 (φ → ψ) yields φ → χ.

    Deduction variant: This is an alternate of pm2.21dd (already in lemmas.py).
    Cross-pod dependency: pm2.21d from pod0 knowledge module (negation.py).
    """
    lb = ProofBuilder(sys, "pm2.21ddALT")
    h1 = lb.hyp("pm2.21ddALT.1", "φ → ψ")
    h2 = lb.hyp("pm2.21ddALT.2", "φ → -. ψ")
    s1 = lb.ref("s1", "φ → ( ψ → χ )", h2, ref="pm2.21d", note="pm2.21d")
    res = lb.ref("res", "φ → χ", h1, s1, ref="mpd", note="mpd")
    return lb.build(res)


def prove_pm2_21i(sys: System) -> Proof:
    """pm2.21i: φ → ψ.  Hyp: -. φ.

    A contradiction implies anything.  Associated with pm2.21.
    (Contributed by NM, 16-Sep-1993.)
    set.mm proof: a1i con4i.
    """
    lb = ProofBuilder(sys, "pm2.21i")
    h1 = lb.hyp("pm2.21i.1", "( -. φ )")
    s1 = lb.ref("s1", "( -. ψ → -. φ )", h1, ref="a1i", note="a1i")
    res = lb.ref("res", "( φ → ψ )", s1, ref="con4i", note="con4i")
    return lb.build(res)


def prove_pm2_24d(sys: System) -> Proof:
    """pm2.24d: φ → (-. ψ → χ).  Hyp: φ → ψ.

    Deduction form of pm2.24.
    (Contributed by NM, 30-Jan-2006.)
    set.mm proof: a1d con1d.
    """
    lb = ProofBuilder(sys, "pm2.24d")
    h1 = lb.hyp("pm2.24d.1", "( φ → ψ )")
    s1 = lb.ref("s1", "( φ → ( -. χ → ψ ) )", h1, ref="a1d", note="a1d")
    res = lb.ref("res", "( φ → ( -. ψ → χ ) )", s1, ref="con1d", note="con1d")
    return lb.build(res)


def prove_pm2_24i(sys: System) -> Proof:
    """pm2.24i: -. φ → ψ.  Hyp: φ.

    Inference associated with pm2.24.
    (Contributed by NM, 20-Aug-2001.)
    set.mm proof: a1i con1i.
    """
    lb = ProofBuilder(sys, "pm2.24i")
    h1 = lb.hyp("pm2.24i.1", "φ")
    s1 = lb.ref("s1", "( -. ψ → φ )", h1, ref="a1i", note="a1i")
    res = lb.ref("res", "( -. φ → ψ )", s1, ref="con1i", note="con1i")
    return lb.build(res)


def prove_pm2_24ii(sys: System) -> Proof:
    """pm2.24ii: ψ.  Hyps: φ, -. φ.

    A contradiction implies anything.  Associated with pm2.21i and pm2.24i.
    (Contributed by NM, 27-Feb-2008.)
    set.mm proof: pm2.21i ax-mp.
    """
    lb = ProofBuilder(sys, "pm2.24ii")
    h1 = lb.hyp("pm2.24ii.1", "φ")
    h2 = lb.hyp("pm2.24ii.2", "( -. φ )")
    s1 = lb.ref("s1", "( φ → ψ )", h2, ref="pm2.21i", note="pm2.21i")
    res = lb.mp("res", h1, s1, "MP hyp1, s1")
    return lb.build(res)


def prove_pm2_521g2(sys: System) -> Proof:
    """pm2.521g2: -. ( φ → ψ ) → ( χ → φ ).

    A general instance of Theorem *2.521 of [WhiteheadRussell] p. 107.
    (Contributed by NM, 3-Jan-2005.)  (Proof shortened by Wolf Lammen,
    8-Oct-2012.)
    set.mm proof: simplim a1d.  Here we derive simplim as con1(pm2.21).
    """
    lb = ProofBuilder(sys, "pm2.521g2")
    s1 = lb.ref("s1", "( -. φ → ( φ → ψ ) )", ref="pm2.21", note="pm2.21")
    s2 = lb.ref("s2", "( ( -. φ → ( φ → ψ ) ) → ( -. ( φ → ψ ) → φ ) )", ref="con1", note="con1")
    s3 = lb.mp("s3", s1, s2, note="MP s1,s2: simplim")
    res = lb.ref("res", "( -. ( φ → ψ ) → ( χ → φ ) )", s3, ref="a1d", note="a1d")
    return lb.build(res)


def prove_pm2_5g(sys: System) -> Proof:
    """pm2.5g: -. ( φ → ψ ) → ( -. φ → χ ).

    General instance of Theorem *2.5 of [WhiteheadRussell] p. 107.
    (Contributed by NM, 3-Jan-2005.)
    (Proof shortened by Wolf Lammen, 9-Oct-2012.)
    set.mm proof: simplim pm2.24d.

    Proof sketch:
    1. pm2.21: -. φ → ( φ → ψ )
    2. con1 on step 1: ( -. φ → ( φ → ψ ) ) → ( -. ( φ → ψ ) → φ )
    3. MP steps 1,2: -. ( φ → ψ ) → φ  (inline simplim)
    4. pm2.21: -. φ → ( φ → χ )
    5. com12 on step 4: φ → ( -. φ → χ )
    6. syl(steps 3, 5): conclusion
    """
    lb = ProofBuilder(sys, "pm2.5g")
    # Inline simplim using con1 (no hypothesis) instead of con1i
    ss1 = lb.ref("ss1", "-. φ → ( φ → ψ )", ref="pm2.21", note="pm2.21")
    ss2 = lb.ref("ss2", "( -. φ → ( φ → ψ ) ) → ( -. ( φ → ψ ) → φ )", ref="con1", note="con1")
    s1 = lb.mp("s1", ss1, ss2, note="MP (inline simplim)")

    # pm2.21: ¬ φ → ( φ → χ )
    s2 = lb.ref("s2", "-. φ → ( φ → χ )", ref="pm2.21", note="pm2.21")
    # com12 on s2: φ → ( ¬ φ → χ )
    s3 = lb.ref("s3", "φ → ( -. φ → χ )", s2, ref="com12", note="com12")
    # syl: combine
    res = lb.ref("res", "-. ( φ → ψ ) → ( -. φ → χ )", s1, s3, ref="syl", note="syl")
    return lb.build(res)


def prove_pm2_61d(sys: System) -> Proof:
    """pm2.61d: φ → χ. Hyp: φ → (ψ → χ), φ → (¬ψ → χ). (Contributed by NM, 27-Apr-1994.)"""
    lb = ProofBuilder(sys, "pm2.61d")
    h1 = lb.hyp("pm2.61d.1", "φ → ( ψ → χ )")
    h2 = lb.hyp("pm2.61d.2", "φ → ( ¬ ψ → χ )")
    c3 = lb.ref("c3", "( ψ → χ ) → ( ¬ χ → ¬ ψ )", ref="con3", note="con3")
    s1 = lb.ref("s1", "φ → ( ¬ χ → ¬ ψ )", h1, c3, ref="syl", note="syl(h1,con3)")
    s2 = lb.ref("s2", "φ → ( ¬ χ → χ )", s1, h2, ref="syld", note="syld")
    res = lb.ref("res", "φ → χ", s2, ref="pm2.18d", note="pm2.18d")
    return lb.build(res)


def prove_pm2_61d1(sys: System) -> Proof:
    """pm2.61d1: φ → χ. Hyp: φ → (ψ → χ), ¬ψ → χ. (Contributed by NM, 15-Jul-2005.)"""
    lb = ProofBuilder(sys, "pm2.61d1")
    h1 = lb.hyp("pm2.61d1.1", "φ → ( ψ → χ )")
    h2 = lb.hyp("pm2.61d1.2", "¬ ψ → χ")
    s1 = lb.ref("s1", "φ → ( ¬ ψ → χ )", h2, ref="a1i", note="a1i")
    res = lb.ref("res", "φ → χ", h1, s1, ref="pm2.61d", note="pm2.61d")
    return lb.build(res)


def prove_pm2_61d2(sys: System) -> Proof:
    """pm2.61d2: φ → χ.  Hyps: φ → (-. ψ → χ), ψ → χ."""
    lb = ProofBuilder(sys, "pm2.61d2")
    h1 = lb.hyp("pm2.61d2.1", "φ → ( -. ψ → χ )")
    h2 = lb.hyp("pm2.61d2.2", "ψ → χ")
    s1 = lb.ref("s1", "φ → ( ψ → χ )", h2, ref="a1i", note="a1i")
    res = lb.ref("res", "φ → χ", s1, h1, ref="pm2.61d", note="pm2.61d")
    return lb.build(res)


def prove_pm2_61i(sys: System) -> Proof:
    """pm2.61i: ψ. Hyps: φ → ψ, -. φ → ψ.

    Inference eliminating an antecedent.
    (Contributed by NM, 5-Apr-1994.)
    set.mm proof: nsyl4 pm2.18i.
    """
    lb = ProofBuilder(sys, "pm2.61i")
    h1 = lb.hyp("pm2.61i.1", "( φ → ψ )")
    h2 = lb.hyp("pm2.61i.2", "( -. φ → ψ )")
    s1 = lb.ref("s1", "( -. ψ → ψ )", h1, h2, ref="nsyl4", note="nsyl4")
    res = lb.ref("res", "ψ", s1, ref="pm2.18i", note="pm2.18i")
    return lb.build(res)


def prove_pm2_65d(sys: System) -> Proof:
    """pm2.65d: ( φ → -. ψ ).

    Hypotheses: ( φ → ( ψ → χ ) ), ( φ → ( ψ → -. χ ) ).
    Deduction for proof by contradiction.
    (Contributed by NM, 26-Jun-1994.) (Proof shortened by Wolf Lammen, 26-May-2013.)

    Expanded proof: con3d(h1) → (φ → (-.χ → -.ψ)) ; syld(h2, s1) → (φ → (ψ → -.ψ)) ; pm2.01d → (φ → -.ψ).
    syld needs explicit args because χ does not appear in its conclusion.
    """
    lb = ProofBuilder(sys, "pm2.65d")
    h1 = lb.hyp("pm2.65d.1", "φ → ( ψ → χ )")
    h2 = lb.hyp("pm2.65d.2", "φ → ( ψ → -. χ )")
    s1 = lb.ref("s1", "φ → ( -. χ → -. ψ )", h1, ref="con3d", note="con3d h1")
    s2 = lb.ref("s2", "φ → ( ψ → -. ψ )", h2, s1, ref="syld", note="syld h2 s1")
    res = lb.ref("res", "φ → -. ψ", s2, ref="pm2.01d", note="pm2.01d")
    return lb.build(res)


def prove_pm2_65i(sys: System) -> Proof:
    """pm2.65i: -. φ.  Hyps: φ → ψ, φ → -. ψ.

    Inference for proof by contradiction.
    (Contributed by NM, 18-May-1994.)
    set.mm proof: con2i con3i pm2.61i.
    """
    lb = ProofBuilder(sys, "pm2.65i")
    h1 = lb.hyp("pm2.65i.1", "( φ → ψ )")
    h2 = lb.hyp("pm2.65i.2", "( φ → -. ψ )")
    s_con2i = lb.ref("s_con2i", "( ψ → -. φ )", h2, ref="con2i", note="con2i")
    s_con3i = lb.ref("s_con3i", "( -. ψ → -. φ )", h1, ref="con3i", note="con3i")
    res = lb.ref("res", "( -. φ )", s_con2i, s_con3i, ref="pm2.61i", note="pm2.61i")
    return lb.build(res)
