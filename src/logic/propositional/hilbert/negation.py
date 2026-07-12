"""Negation and contraposition.

con1-con4 series, modus tollens family, explosion (pm2.21),
contradiction and reduction.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping

from skfd.proof import Proof, ProofBuilder

from . import System

LemmaCtor = Callable[[System], Proof]

# -----------------------------------------------------------------------------
# Migration Expansion (set.mm compatibility)
# -----------------------------------------------------------------------------


def prove_notnot(sys: System) -> Proof:
    """
    notnot: φ → ¬¬φ.

    Double negation introduction.
    """
    lb = ProofBuilder(sys, "notnot")
    s1 = lb.ref("s1", "¬ φ → ¬ φ", ref="id", note="id")
    res = lb.ref("res", "φ → ¬ ¬ φ", s1, ref="con2i", note="con2i")
    return lb.build(res)


def prove_notnotd(sys: System) -> Proof:
    """notnotd: ( ph -> -. -. ps ).

    Deduction associated with notnot.
    """
    lb = ProofBuilder(sys, "notnotd")
    h1 = lb.hyp("notnotd.1", "( ph -> ps )")
    s1 = lb.ref("s1", "( ps -> -. -. ps )", ref="notnot", note="notnot")
    res = lb.ref("res", "( ph -> -. -. ps )", h1, s1, ref="syl", note="syl")
    return lb.build(res)


def prove_notnoti(sys: System) -> Proof:
    """notnoti: ¬¬φ. Hyp: φ.

    Inference associated with notnot.
    """
    lb = ProofBuilder(sys, "notnoti")
    h = lb.hyp("notnoti.1", "φ")
    s1 = lb.ref("s1", "φ → ¬ ¬ φ", ref="notnot", note="notnot")
    res = lb.mp("res", h, s1, note="MP notnoti.1, notnot")
    return lb.build(res)


def prove_notnotr(sys: System) -> Proof:
    """
    notnotr: ¬¬φ → φ.

    Double negation elimination.
    """
    lb = ProofBuilder(sys, "notnotr")
    s1 = lb.ref("s1", "( ¬ φ → φ ) → φ", ref="pm2.18", note="pm2.18")
    res = lb.ref("res", "¬ ¬ φ → φ", s1, ref="jarli", note="jarli")
    return lb.build(res)


def prove_notnotrd(sys: System) -> Proof:
    """notnotrd: ( ph -> ps ).  Hyp: notnotrd.1 ( ph -> -. -. ps ).

    Deduction associated with notnotr.
    """
    lb = ProofBuilder(sys, "notnotrd")
    h1 = lb.hyp("notnotrd.1", "( ph -> -. -. ps )")
    s1 = lb.ref("s1", "( -. -. ps -> ps )", ref="notnotr", note="notnotr")
    res = lb.ref("res", "( ph -> ps )", h1, s1, ref="syl", note="syl")
    return lb.build(res)


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


def prove_con3dimp(sys: System) -> Proof:
    r"""con3dimp: ( ( ph /\ -. ch ) -> -. ps ).

    Imported contraposition deduction.  If ph implies ps implies ch,
    then ph and not ch implies not ps.
    """
    lb = ProofBuilder(sys, "con3dimp")
    h1 = lb.hyp("con3dimp.1", "( ph -> ( ps -> ch ) )")
    s1 = lb.ref("s1", "( ph -> ( -. ch -> -. ps ) )", h1, ref="con3d", note="con3d")

    res = lb.ref("res", r"( ( ph /\ -. ch ) -> -. ps )", s1, ref="imp", note="imp")
    return lb.build(res)


def prove_con3rr3(sys: System) -> Proof:
    """
    con3rr3: ¬ χ → ( φ → ¬ ψ ). Hyp: φ → ( ψ → χ ).
    """
    lb = ProofBuilder(sys, "con3rr3")
    h1 = lb.hyp("con3rr3.1", "φ → ( ψ → χ )")

    s1 = lb.ref("s1", "φ → ( ¬ χ → ¬ ψ )", h1, ref="con3d", note="con3d")
    res = lb.ref("res", "¬ χ → ( φ → ¬ ψ )", s1, ref="com12", note="com12")
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


def prove_con3ALT(sys: System) -> Proof:
    """con3ALT: ( φ → ψ ) → ( ¬ ψ → ¬ φ ).

    Alternate proof of con3 using elimh/dedt in set.mm.
    """
    lb = ProofBuilder(sys, "con3ALT")
    res = lb.ref("res", "( φ → ψ ) → ( ¬ ψ → ¬ φ )", ref="con3", note="con3")
    return lb.build(res)


def prove_con4(sys: System) -> Proof:
    """
    con4: ( ¬ φ → ¬ ψ ) → ( ψ → φ ).

    Alias for ~ ax-3 to be used instead of it for labeling consistency.  Its
         associated inference is ~ con4i and its associated deduction is ~ con4d .
         (Contributed by BJ, 24-Dec-2020.)

    """
    lb = ProofBuilder(sys, "con4")
    stmt = lb.ref("res", "( ¬ φ → ¬ ψ ) → ( ψ → φ )", ref="ax-3", note="ax-3")
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
        ref="ax-1",
        note="A1",
    )
    s3 = lb.mp("s3", s1, s2, "MP s1, s2")
    s4 = lb.ref(
        "s4",
        "( φ → ( ( ¬ ψ → ¬ χ ) → ( χ → ψ ) ) ) → ( ( φ → ( ¬ ψ → ¬ χ ) ) → ( φ → ( χ → ψ ) ) )",
        ref="ax-2",
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


def prove_axin1(sys: System) -> Proof:
    """axin1: ( φ → ¬ φ ) → ¬ φ.

    Alias of pm2.01.
    """
    lb = ProofBuilder(sys, "axin1")
    res = lb.ref("res", "( φ → ¬ φ ) → ¬ φ", ref="pm2.01", note="pm2.01")
    return lb.build(res)


def prove_axin2(sys: System) -> Proof:
    """axin2: ¬ φ → ( φ → ψ ).

    Alias of pm2.21.  (Contributed by NM, 7-Jan-2005.)

    """
    lb = ProofBuilder(sys, "axin2")
    res = lb.ref("res", "¬ φ → ( φ → ψ )", ref="pm2.21", note="pm2.21")
    return lb.build(res)


def prove_simplim(sys: System) -> Proof:
    """
    simplim: ¬ ( φ → ψ ) → φ.

    Simplification theorem: the negation of an implication implies
    the antecedent.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "simplim")
    s1 = lb.ref("s1", "¬ φ → ( φ → ψ )", ref="pm2.21", note="pm2.21")
    res = lb.ref("res", "¬ ( φ → ψ ) → φ", s1, ref="con1i", note="con1i")
    return lb.build(res)


def prove_simprim(sys: System) -> Proof:
    """simprim: ¬ ( φ → ¬ ψ ) → ψ.

    One of the two classical Primitive Logic equivalences.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "simprim")
    s1 = lb.ref("s1", "φ → ( ψ → ψ )", ref="idd", note="idd")
    res = lb.ref("res", "¬ ( φ → ¬ ψ ) → ψ", s1, ref="impi", note="impi")
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
    s1 = lb.ref("s1", "ψ → ( φ → ψ )", ref="ax-1", note="ax-1")
    s2 = lb.ref(
        "s2",
        "( ψ → ( φ → ψ ) ) → ( ¬ ( φ → ψ ) → ¬ ψ )",
        ref="con3",
        note="con3",
    )
    res = lb.mp("res", s1, s2, "MP s1, s2")
    return lb.build(res)


def prove_conax1k(sys: System) -> Proof:
    """
    conax1k: ¬ ( φ → ψ ) → ( χ → ¬ ψ ).
    """
    lb = ProofBuilder(sys, "conax1k")
    s1 = lb.ref("s1", "¬ ( φ → ψ ) → ¬ ψ", ref="conax1", note="conax1")
    res = lb.ref("res", "¬ ( φ → ψ ) → ( χ → ¬ ψ )", s1, ref="a1d", note="a1d")
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


def prove_con2i(sys: System) -> Proof:
    """
    con2i: ψ → ¬ φ. Hyp: φ → ¬ ψ.

    A contraposition inference.  Its associated inference is ~ mt2 .
           (Contributed by NM, 10-Jan-1993.)  (Proof shortened by Mel L. O'Cat,
           28-Nov-2008.)  (Proof shortened by Wolf Lammen, 13-Jun-2013.)

    """
    lb = ProofBuilder(sys, "con2i")
    hyp = lb.hyp("prove_con2i.h", "φ → ¬ ψ")
    s1 = lb.ref("s1", "ψ → ψ", ref="id", note="id")
    res = lb.ref("res", "ψ → ¬ φ", hyp, s1, ref="nsyl3", note="nsyl3")
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


def prove_mt4i(sys: System) -> Proof:
    """
    mt4i: ( ph → ps ).  Hyp1: ch, Hyp2: ( ph → ( -. ps → -. ch ) ).

    Modus tollens inference.  Inference form of mt4d.
    """
    lb = ProofBuilder(sys, "mt4i")
    h1 = lb.hyp("mt4i.1", "ch")
    h2 = lb.hyp("mt4i.2", "( ph → ( -. ps → -. ch ) )")
    s1 = lb.ref("s1", "( ph → ch )", h1, ref="a1i", note="a1i")
    res = lb.ref("res", "( ph → ps )", s1, h2, ref="mt4d", note="mt4d")
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
    s1 = lb.ref("s1", "φ → ( φ \\/ ψ )", ref="orc", note="orc")
    res = lb.ref("res", "-. ( φ \\/ ψ ) → -. φ", s1, ref="con3i", note="con3i(orc)")
    return lb.build(res)


def prove_pm2_46(sys: System) -> Proof:
    """pm2.46: ¬(φ ∨ ψ) → ¬ψ.

    Theorem *2.46 of [WhiteheadRussell] p. 106.
    (Contributed by NM, 3-Jan-2005.)
    Under df-or: olc = ψ→(¬φ→ψ), an ax-1 instance.
    con3i applied gives ¬(¬φ→ψ)→¬ψ.
    """
    lb = ProofBuilder(sys, "pm2.46")
    s1 = lb.ref("s1", "( ψ → ( -. φ → ψ ) )", ref="ax-1", note="ax-1 (olc df-or)")
    expanded = lb.ref("expanded", "( -. ( -. φ → ψ ) → -. ψ )", s1, ref="con3i", note="con3i(olc)")
    df_or = lb.ref(
        "df_or",
        "( φ \\/ ψ ) <-> ( -. φ -> ψ )",
        ref="df-or",
        note="df-or",
    )
    negated = lb.ref(
        "negated",
        "-. ( φ \\/ ψ ) <-> -. ( -. φ -> ψ )",
        df_or,
        ref="notbii",
        note="notbii",
    )
    forward = lb.ref(
        "forward",
        "-. ( φ \\/ ψ ) -> -. ( -. φ -> ψ )",
        negated,
        ref="biimpi",
        note="biimpi",
    )
    res = lb.ref("res", "-. ( φ \\/ ψ ) -> -. ψ", forward, expanded, ref="syl", note="syl")
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
    pm2.21 with φ=¬φ gives ¬¬φ→(¬φ→ψ); com12 swaps to ¬φ→(¬¬φ→ψ).
    syl chains them.
    """
    lb = ProofBuilder(sys, "pm2.47")
    s1 = lb.ref("s1", "-. ( φ \\/ ψ ) → -. φ", ref="pm2.45", note="pm2.45")
    s2 = lb.ref("s2", "-. φ → ( -. φ \\/ ψ )", ref="orc", note="orc")
    res = lb.ref(
        "res",
        "-. ( φ \\/ ψ ) → ( -. φ \\/ ψ )",
        s1,
        s2,
        ref="syl",
        note="syl(pm2.45, orc)",
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
    s1 = lb.ref("s1", "-. ( φ \\/ ψ ) → -. ψ", ref="pm2.46", note="pm2.46")
    s2 = lb.ref("s2", "-. ψ → ( φ \\/ -. ψ )", ref="olc", note="olc")
    res = lb.ref(
        "res",
        "-. ( φ \\/ ψ ) → ( φ \\/ -. ψ )",
        s1,
        s2,
        ref="syl",
        note="syl(pm2.46, olc)",
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
    s1 = lb.ref("s1", "-. ( φ \\/ ψ ) → -. ψ", ref="pm2.46", note="pm2.46")
    s2 = lb.ref("s2", "-. ψ → ( -. φ \\/ -. ψ )", ref="olc", note="olc")
    res = lb.ref(
        "res",
        "-. ( φ \\/ ψ ) → ( -. φ \\/ -. ψ )",
        s1,
        s2,
        ref="syl",
        note="syl(pm2.46, olc)",
    )
    return lb.build(res)


# ============================================================
# pm2.51, pm2.52 (negation of implication)
# ============================================================


def prove_pm2_51(sys: System) -> Proof:
    """pm2.51: ¬(φ → ψ) → (φ → ¬ψ).

    Theorem *2.51 of [WhiteheadRussell] p. 107.
    (Contributed by NM, 3-Jan-2005.)
    conax1k: ¬(φ → ψ) → (φ → ¬ψ).
    """
    lb = ProofBuilder(sys, "pm2.51")
    res = lb.ref("res", "( -. ( φ → ψ ) → ( φ → -. ψ ) )", ref="conax1k", note="conax1k")
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
    s2 = lb.ref("s2", "( -. ψ → ( -. φ → -. ψ ) )", ref="ax-1", note="ax-1")
    res = lb.ref(
        "res",
        "( -. ( φ → ψ ) → ( -. φ → -. ψ ) )",
        s1,
        s2,
        ref="syl",
        note="syl(conax1, A1)",
    )
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


def prove_bijust0(sys: System) -> Proof:
    """bijust0: ¬ ( ( φ → φ ) → ¬ ( φ → φ ) ).

    A "justification" theorem for the weak bi-implication.
    """
    lb = ProofBuilder(sys, "bijust0")
    s1 = lb.ref("s1", "φ → φ", ref="id", note="id")
    s2 = lb.ref("s2", "( ( φ → φ ) → ¬ ( φ → φ ) ) → ¬ ( φ → φ )", ref="pm2.01", note="pm2.01")
    res = lb.ref("res", "¬ ( ( φ → φ ) → ¬ ( φ → φ ) )", s1, s2, ref="mt2", note="mt2")
    return lb.build(res)


def prove_bijust(sys: System) -> Proof:
    """bijust: ¬ ( ( ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) → ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) ) → ¬ ( ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) → ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) ) ).

    A "justification" theorem for the bi-implication.  Extends ~ bijust0.
    """
    lb = ProofBuilder(sys, "bijust")
    res = lb.ref(
        "res",
        "¬ ( ( ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) → ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) ) → ¬ ( ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) → ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) ) )",
        ref="bijust0",
        note="bijust0",
    )
    return lb.build(res)


def prove_mt3(sys: System) -> Proof:
    """mt3: φ. Hyp: ¬ψ, ¬φ → ψ. (Contributed by NM, 18-May-1994.)"""
    lb = ProofBuilder(sys, "mt3")
    h1 = lb.hyp("mt3.1", "¬ ψ")
    h2 = lb.hyp("mt3.2", "¬ φ → ψ")
    s1 = lb.ref("s1", "¬ ¬ φ", h1, h2, ref="mto", note="mto")
    res = lb.ref("res", "φ", s1, ref="notnotri", note="notnotri")
    return lb.build(res)


def prove_mt3d(sys: System) -> Proof:
    """mt3d: ph -> ps.

    Hyp: ph -> -. ch, ph -> ( -. ps -> ch ).
    Deduction form of ~ mt3.  (Contributed by NM, 29-Dec-1992.)
    """
    lb = ProofBuilder(sys, "mt3d")
    h1 = lb.hyp("mt3d.1", "ph -> -. ch")
    h2 = lb.hyp("mt3d.2", "ph -> ( -. ps -> ch )")
    s1 = lb.ref("s1", "ph -> ( -. ch -> ps )", h2, ref="con1d", note="con1d mt3d.2")
    res = lb.ref("res", "ph -> ps", h1, s1, ref="mpd", note="mpd mt3d.1, s1")
    return lb.build(res)


def prove_mt3i(sys: System) -> Proof:
    """mt3i: ph -> ps.

    Hyp: -. ch, ph -> ( -. ps -> ch ).
    Inference form of ~ mt3.  (Contributed by NM, 18-May-1994.)
    """
    lb = ProofBuilder(sys, "mt3i")
    h1 = lb.hyp("mt3i.1", "-. ch")
    h2 = lb.hyp("mt3i.2", "ph -> ( -. ps -> ch )")
    s1 = lb.ref("s1", "ph -> -. ch", h1, ref="a1i", note="a1i mt3i.1")
    res = lb.ref("res", "ph -> ps", s1, h2, ref="mt3d", note="mt3d s1, mt3i.2")
    return lb.build(res)


def prove_nsyl(sys: System) -> Proof:
    """nsyl: φ → ¬χ. Hyp: φ → ¬ψ, χ → ψ. (Contributed by NM, 31-Dec-1993.)"""
    lb = ProofBuilder(sys, "nsyl")
    h1 = lb.hyp("nsyl.1", "φ → ¬ ψ")
    h2 = lb.hyp("nsyl.2", "χ → ψ")
    s1 = lb.ref("s1", "χ → ¬ φ", h1, h2, ref="nsyl3", note="nsyl3")
    res = lb.ref("res", "φ → ¬ χ", s1, ref="con2i", note="con2i")
    return lb.build(res)


def prove_nsyli(sys: System) -> Proof:
    """nsyli: ( ph -> ( th -> -. ps ) ).

    Hyp: nsyli.1 ( ph -> ( ps -> ch ) ), nsyli.2 ( th -> -. ch ).
    Inference associated with nsyl.
    """
    lb = ProofBuilder(sys, "nsyli")
    h1 = lb.hyp("nsyli.1", "( ph -> ( ps -> ch ) )")
    h2 = lb.hyp("nsyli.2", "( th -> -. ch )")
    s1 = lb.ref("s1", "( ph -> ( -. ch -> -. ps ) )", h1, ref="con3d", note="con3d")
    res = lb.ref("res", "( ph -> ( th -> -. ps ) )", h2, s1, ref="syl5", note="syl5")
    return lb.build(res)


def prove_nsyld(sys: System) -> Proof:
    """nsyld: φ → ( ψ → ¬ τ ).

    Hyp: φ → ( ψ → ¬ χ ), φ → ( τ → χ ).

    Syllogism deduction with negation.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "nsyld")
    h1 = lb.hyp("nsyld.1", "φ → ( ψ → ¬ χ )")
    h2 = lb.hyp("nsyld.2", "φ → ( τ → χ )")
    s1 = lb.ref("s1", "φ → ( ¬ χ → ¬ τ )", h2, ref="con3d", note="con3d")
    res = lb.ref("res", "φ → ( ψ → ¬ τ )", h1, s1, ref="syld", note="syld")
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


def prove_sylnib(sys: System) -> Proof:
    """sylnib: φ → ¬ χ.

    Hyp 1: φ → ¬ ψ
    Hyp 2: ψ <-> χ
    Concl: φ → ¬ χ

    Syllogism inference with biconditional and negation.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sylnib")
    h1 = lb.hyp("sylnib.1", "φ → ¬ ψ")
    h2 = lb.hyp("sylnib.2", "ψ <-> χ")
    s1 = lb.ref("s1", "χ → ψ", h2, ref="biimpri", note="biimpri")
    res = lb.ref("res", "φ → ¬ χ", h1, s1, ref="nsyl", note="nsyl")
    return lb.build(res)


def prove_sylnibr(sys: System) -> Proof:
    """sylnibr: φ → ¬ χ.

    Hyp 1: φ → ¬ ψ
    Hyp 2: χ <-> ψ
    Concl: φ → ¬ χ

    Syllogism inference with biconditional and negation (right-side variant).
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sylnibr")
    h1 = lb.hyp("sylnibr.1", "φ → ¬ ψ")
    h2 = lb.hyp("sylnibr.2", "χ <-> ψ")
    s1 = lb.ref("s1", "ψ <-> χ", h2, ref="bicomi", note="bicomi")
    res = lb.ref("res", "φ → ¬ χ", h1, s1, ref="sylnib", note="sylnib")
    return lb.build(res)


def prove_sylnbi(sys: System) -> Proof:
    """sylnbi: ¬ φ → χ.

    Hyp 1: φ ↔ ψ
    Hyp 2: ¬ ψ → χ
    Concl: ¬ φ → χ

    Syllogism inference with biconditional and negation on the left.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "sylnbi")
    h1 = lb.hyp("sylnbi.1", "( φ ↔ ψ )")
    h2 = lb.hyp("sylnbi.2", "¬ ψ → χ")
    s1 = lb.ref("s1", "( ¬ φ ↔ ¬ ψ )", h1, ref="notbii", note="notbii")
    res = lb.ref("res", "¬ φ → χ", s1, h2, ref="sylbi", note="sylbi")
    return lb.build(res)


def prove_sylnbir(sys: System) -> Proof:
    """sylnbir: ¬ φ → χ.

    Hyp 1: ψ ↔ φ
    Hyp 2: ¬ ψ → χ
    Concl: ¬ φ → χ

    Syllogism inference with biconditional and negation on the left,
    reversed biconditional variant.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "sylnbir")
    h1 = lb.hyp("sylnbir.1", "( ψ ↔ φ )")
    h2 = lb.hyp("sylnbir.2", "¬ ψ → χ")
    s1 = lb.ref("s1", "( φ ↔ ψ )", h1, ref="bicomi", note="bicomi")
    res = lb.ref("res", "¬ φ → χ", s1, h2, ref="sylnbi", note="sylnbi")
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


def prove_impi(sys: System) -> Proof:
    """
    impi: ( -. ( ph -> -. ps ) -> ch ).

    Inference associated with imim1 (importation).  Hyp: impi.1: ph -> ( ps -> ch ).
    """
    lb = ProofBuilder(sys, "impi")
    h1 = lb.hyp("impi.1", "φ → ( ψ → χ )")
    s1 = lb.ref("s1", "¬ χ → ( φ → ¬ ψ )", h1, ref="con3rr3", note="con3rr3")
    res = lb.ref("res", "¬ ( φ → ¬ ψ ) → χ", s1, ref="con1i", note="con1i")
    return lb.build(res)


def prove_mt2d(sys: System) -> Proof:
    """mt2d: φ → ¬ψ. Hyp: φ → χ, φ → (ψ → ¬χ). (Contributed by NM, 16-Apr-1995.)"""
    lb = ProofBuilder(sys, "mt2d")
    h1 = lb.hyp("mt2d.1", "φ → χ")
    h2 = lb.hyp("mt2d.2", "φ → ( ψ → ¬ χ )")
    s1 = lb.ref("s1", "φ → ( χ → ¬ ψ )", h2, ref="con2d", note="con2d")
    res = lb.ref("res", "φ → ¬ ψ", h1, s1, ref="mpd", note="mpd")
    return lb.build(res)


def prove_mt2i(sys: System) -> Proof:
    """mt2i: φ → ¬ ψ. Hyp: χ, φ → (ψ → ¬ χ). Inference associated with mt2d. (Contributed by NM, 9-Mar-1995.)"""
    lb = ProofBuilder(sys, "mt2i")
    h1 = lb.hyp("mt2i.1", "χ")
    h2 = lb.hyp("mt2i.2", "φ → ( ψ → ¬ χ )")
    s1 = lb.ref("s1", "φ → χ", h1, ref="a1i", note="a1i")
    res = lb.ref("res", "φ → ¬ ψ", s1, h2, ref="mt2d", note="mt2d")
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


def prove_mtod(sys: System) -> Proof:
    """mtod: ( ph -> -. ps ).

    Modus tollens deduction. Hypotheses: ( ph -> -. ch ), ( ph -> ( ps -> ch ) ).
    """
    lb = ProofBuilder(sys, "mtod")
    h1 = lb.hyp("mtod.1", "( ph -> -. ch )")
    h2 = lb.hyp("mtod.2", "( ph -> ( ps -> ch ) )")
    # id: ( -. ch -> -. ch )
    s_id = lb.ref("s_id", "( -. ch -> -. ch )", ref="id", note="id")
    # a1d with s_id as hypothesis: ( -. ch -> ( ps -> -. ch ) )
    s_a1d = lb.ref("s_a1d", "( -. ch -> ( ps -> -. ch ) )", s_id, ref="a1d", note="a1d")
    # syl: combine h1 and s_a1d
    s_syl = lb.ref("s_syl", "( ph -> ( ps -> -. ch ) )", h1, s_a1d, ref="syl", note="syl")
    # pm2.65d with h2 and s_syl
    res = lb.ref("res", "( ph -> -. ps )", h2, s_syl, ref="pm2.65d", note="pm2.65d")
    return lb.build(res)


def prove_mtoi(sys: System) -> Proof:
    """mtoi: ( ph -> -. ps ).

    Modus tollens inference. Hypotheses: -. ch, ( ph -> ( ps -> ch ) ).
    """
    lb = ProofBuilder(sys, "mtoi")
    h1 = lb.hyp("mtoi.1", "-. ch")
    h2 = lb.hyp("mtoi.2", "( ph -> ( ps -> ch ) )")
    s_a1i = lb.ref("s_a1i", "( ph -> -. ch )", h1, ref="a1i", note="a1i")
    res = lb.ref("res", "( ph -> -. ps )", s_a1i, h2, ref="mtod", note="mtod")
    return lb.build(res)


def prove_mtbi(sys: System) -> Proof:
    """mtbi: ¬ ψ.

    Modus tollens with biconditional, inference form.
    Hypotheses: ¬ φ, ( φ ↔ ψ ).
    (Contributed by NM, 26-Dec-1993.)
    """
    lb = ProofBuilder(sys, "mtbi")
    h1 = lb.hyp("mtbi.1", "¬ φ")
    h2 = lb.hyp("mtbi.2", "( φ ↔ ψ )")
    s1 = lb.ref("s1", "( ψ → φ )", h2, ref="biimpri", note="biimpri")
    res = lb.ref("res", "¬ ψ", h1, s1, ref="mto", note="mto")
    return lb.build(res)


def prove_mtbir(sys: System) -> Proof:
    """mtbir: ¬ φ.

    Modus tollens with biconditional, inference form (right-hand side).
    Hypotheses: ¬ ψ, ( φ ↔ ψ ).
    (Contributed by NM, 26-Dec-1993.)
    """
    lb = ProofBuilder(sys, "mtbir")
    h1 = lb.hyp("mtbir.1", "¬ ψ")
    h2 = lb.hyp("mtbir.2", "( φ ↔ ψ )")
    s_bicomi = lb.ref("s_bicomi", "( ψ ↔ φ )", h2, ref="bicomi", note="bicomi")
    res = lb.ref("res", "¬ φ", h1, s_bicomi, ref="mtbi", note="mtbi")
    return lb.build(res)


def prove_mtbid(sys: System) -> Proof:
    """mtbid: ( ph -> -. ch ).

    Modus tollens deduction with biconditional.
    Hypotheses: ( ph -> -. ps ), ( ph -> ( ps <-> ch ) ).
    """
    lb = ProofBuilder(sys, "mtbid")
    h_min = lb.hyp("mtbid.min", "( ph -> -. ps )")
    h_maj = lb.hyp("mtbid.maj", "( ph -> ( ps <-> ch ) )")
    s_biimprd = lb.ref("s_biimprd", "( ph -> ( ch -> ps ) )", h_maj, ref="biimprd", note="biimprd")
    res = lb.ref("res", "( ph -> -. ch )", h_min, s_biimprd, ref="mtod", note="mtod")
    return lb.build(res)


def prove_mtord(sys: System) -> Proof:
    """mtord: ( ph -> -. ps ).

    Modus tollens deduction with disjunction.
    Hypotheses: ( ph -> -. ch ), ( ph -> -. th ),
    ( ph -> ( ps -> ( ch \\/ th ) ) ).
    """
    lb = ProofBuilder(sys, "mtord")
    h1 = lb.hyp("mtord.1", "( ph -> -. ch )")
    h2 = lb.hyp("mtord.2", "( ph -> -. th )")
    h3 = lb.hyp("mtord.3", "( ph -> ( ps -> ( ch \\/ th ) ) )")
    df_or = lb.ref(
        "df_or",
        "( ch \\/ th ) <-> ( -. ch -> th )",
        ref="df-or",
        note="df-or",
    )
    s_pm2_53 = lb.ref(
        "s_pm2_53",
        "( ch \\/ th ) -> ( -. ch -> th )",
        df_or,
        ref="biimpi",
        note="biimpi",
    )
    # syl6ci(h3, h1, pm2.53): ph -> ( ps -> th )
    s_syl6ci = lb.ref(
        "s_syl6ci",
        "( ph -> ( ps -> th ) )",
        h3,
        h1,
        s_pm2_53,
        ref="syl6ci",
        note="syl6ci",
    )
    # mtod(h2, s_syl6ci): ph -> -. ps
    res = lb.ref(
        "res",
        "( ph -> -. ps )",
        h2,
        s_syl6ci,
        ref="mtod",
        note="mtod",
    )
    return lb.build(res)


def prove_mtbiri(sys: System) -> Proof:
    """mtbiri: ( ph -> -. ps ).

    Modus tollens inference with biconditional. Hypotheses:
    -. ch, ( ph -> ( ps <-> ch ) ).
    """
    lb = ProofBuilder(sys, "mtbiri")
    h_min = lb.hyp("mtbiri.min", "-. ch")
    h_maj = lb.hyp("mtbiri.maj", "( ph -> ( ps <-> ch ) )")
    s_biimpd = lb.ref(
        "s_biimpd",
        "( ph -> ( ps -> ch ) )",
        h_maj,
        ref="biimpd",
        note="biimpd",
    )
    res = lb.ref(
        "res",
        "( ph -> -. ps )",
        h_min,
        s_biimpd,
        ref="mtoi",
        note="mtoi",
    )
    return lb.build(res)


def prove_mtbird(sys: System) -> Proof:
    """mtbird: ( ph -> -. ps ).

    Modus tollens deduction with biconditional. Hypotheses:
    ( ph -> -. ch ), ( ph -> ( ps <-> ch ) ).
    """
    lb = ProofBuilder(sys, "mtbird")
    h_min = lb.hyp("mtbird.min", "( ph -> -. ch )")
    h_maj = lb.hyp("mtbird.maj", "( ph -> ( ps <-> ch ) )")
    s_biimpd = lb.ref(
        "s_biimpd",
        "( ph -> ( ps -> ch ) )",
        h_maj,
        ref="biimpd",
        note="biimpd",
    )
    res = lb.ref(
        "res",
        "( ph -> -. ps )",
        h_min,
        s_biimpd,
        ref="mtod",
        note="mtod",
    )
    return lb.build(res)


def prove_mtbii(sys: System) -> Proof:
    """mtbii: ( ph -> -. ch ).

    Modus tollens inference with biconditional. Hypotheses:
    -. ps, ( ph -> ( ps <-> ch ) ).
    """
    lb = ProofBuilder(sys, "mtbii")
    h_min = lb.hyp("mtbii.min", "-. ps")
    h_maj = lb.hyp("mtbii.maj", "( ph -> ( ps <-> ch ) )")
    s_biimprd = lb.ref(
        "s_biimprd",
        "( ph -> ( ch -> ps ) )",
        h_maj,
        ref="biimprd",
        note="biimprd",
    )
    res = lb.ref(
        "res",
        "( ph -> -. ch )",
        h_min,
        s_biimprd,
        ref="mtoi",
        note="mtoi",
    )
    return lb.build(res)


def prove_meredith(sys: System) -> Proof:
    """meredith: (((((φ → ψ) → (¬ χ → ¬ θ)) → χ) → τ) → ((τ → φ) → (θ → φ))).

    Meredith's axiom. This is the shortest single axiom of the classical
    propositional calculus involving just → and ¬.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "meredith")
    s1 = lb.ref("s1", "¬ φ → ( φ → ψ )", ref="pm2.21", note="pm2.21")
    s2 = lb.ref("s2", "( ¬ χ → ¬ θ ) → ( θ → χ )", ref="con4", note="con4")
    s3 = lb.ref(
        "s3",
        "( ( φ → ψ ) → ( ¬ χ → ¬ θ ) ) → ( ¬ φ → ( θ → χ ) )",
        s1,
        s2,
        ref="imim12i",
        note="imim12i",
    )
    s4 = lb.ref(
        "s4", "θ → ( ¬ φ → ( ( ( φ → ψ ) → ( ¬ χ → ¬ θ ) ) → χ ) )", s3, ref="com13", note="com13"
    )
    s5 = lb.ref(
        "s5", "θ → ( ¬ ( ( ( φ → ψ ) → ( ¬ χ → ¬ θ ) ) → χ ) → φ )", s4, ref="con1d", note="con1d"
    )
    s6 = lb.ref(
        "s6", "¬ ( ( ( φ → ψ ) → ( ¬ χ → ¬ θ ) ) → χ ) → ( θ → φ )", s5, ref="com12", note="com12"
    )
    s7 = lb.ref(
        "s7",
        "¬ ( ( ( φ → ψ ) → ( ¬ χ → ¬ θ ) ) → χ ) → ( ( τ → φ ) → ( θ → φ ) )",
        s6,
        ref="a1d",
        note="a1d",
    )
    s8 = lb.ref("s8", "τ → ( θ → τ )", ref="ax-1", note="ax-1")
    s9 = lb.ref("s9", "τ → ( ( τ → φ ) → ( θ → φ ) )", s8, ref="imim1d", note="imim1d")
    res = lb.ref(
        "res",
        "( ( ( ( φ → ψ ) → ( ¬ χ → ¬ θ ) ) → χ ) → τ ) → ( ( τ → φ ) → ( θ → φ ) )",
        s7,
        s9,
        ref="ja",
        note="ja",
    )
    return lb.build(res)


def prove_merlem1(sys: System) -> Proof:
    """merlem1: (((ch → (¬ ph → ps)) → ta) → (ph → ta)).

    First lemma towards deriving the Łukasiewicz axioms from Meredith's
    sole axiom.  (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "merlem1")

    s1 = lb.ref(
        "s1",
        "((((¬ φ → ψ) → (¬ (¬ τ → ¬ χ) → ¬ ¬ (¬ φ → ψ))) → (¬ τ → ¬ χ)) → τ) → ((τ → ¬ φ) → (¬ (¬ φ → ψ) → ¬ φ))",
        ref="meredith",
        note="meredith",
    )

    s2 = lb.ref(
        "s2",
        "(((((¬ φ → ψ) → (¬ (¬ τ → ¬ χ) → ¬ ¬ (¬ φ → ψ))) → (¬ τ → ¬ χ)) → τ) → ((τ → ¬ φ) → (¬ (¬ φ → ψ) → ¬ φ))) → ((((τ → ¬ φ) → (¬ (¬ φ → ψ) → ¬ φ)) → (¬ φ → ψ)) → (χ → (¬ φ → ψ)))",
        ref="meredith",
        note="meredith",
    )

    s3 = lb.mp("s3", s1, s2, "MP s1, s2")

    s4 = lb.ref(
        "s4",
        "((((τ → ¬ φ) → (¬ (¬ φ → ψ) → ¬ φ)) → (¬ φ → ψ)) → (χ → (¬ φ → ψ))) → (((χ → (¬ φ → ψ)) → τ) → (φ → τ))",
        ref="meredith",
        note="meredith",
    )

    res = lb.mp("res", s3, s4, "MP s3, s4")

    return lb.build(res)


def prove_notnotri(sys: System) -> Proof:
    """notnotri: φ. Hyp: ¬¬φ. (Contributed by NM, 15-Feb-1993.)"""
    lb = ProofBuilder(sys, "notnotri")
    h = lb.hyp("notnotri.1", "¬ ¬ φ")
    s1 = lb.ref("s1", "¬ ¬ φ → φ", ref="notnotr", note="notnotr")
    res = lb.mp("res", h, s1, note="MP notnotri.1, s1")
    return lb.build(res)


def prove_notnotriALT(sys: System) -> Proof:
    """notnotriALT: φ. Hyp: ¬¬φ. Alternate proof of notnotri.

    (Contributed by NM, 15-Feb-1993.)
    set.mm proof: pm2.21i pm2.18i.
    """
    lb = ProofBuilder(sys, "notnotriALT")
    h = lb.hyp("notnotriALT.1", "¬ ¬ φ")
    s1 = lb.ref("s1", "( ¬ φ → φ )", h, ref="pm2.21i", note="pm2.21i")
    res = lb.ref("res", "φ", s1, ref="pm2.18i", note="pm2.18i")
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


def prove_nsyl5(sys: System) -> Proof:
    """nsyl5: -. ps → ch. Hyps: ph → ps, -. ph → ch.

    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: nsyl4 con1i.
    """
    lb = ProofBuilder(sys, "nsyl5")
    h1 = lb.hyp("nsyl5.1", "( φ → ψ )")
    h2 = lb.hyp("nsyl5.2", "( -. φ → χ )")
    s1 = lb.ref("s1", "( -. χ → ψ )", h1, h2, ref="nsyl4", note="nsyl4")
    res = lb.ref("res", "( -. ψ → χ )", s1, ref="con1i", note="con1i")
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


def prove_pm2_5(sys: System) -> Proof:
    """
    pm2.5: ¬ ( φ → ψ ) → ( ¬ φ → ψ ).

    Theorem *2.5 of [WhiteheadRussell] p. 107.
    (Contributed by NM, 3-Jan-2005.)
    """
    lb = ProofBuilder(sys, "pm2.5")

    s1 = lb.ref(
        "s1",
        "¬ ( φ → ψ ) → ( ¬ φ → ψ )",
        ref="pm2.5g",
        note="pm2.5g",
    )
    return lb.build(s1)


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


def prove_pm2_61ian(sys: System) -> Proof:
    """pm2.61ian: ( ps -> ch ).

    Hypotheses: ( ( ph /\\ ps ) -> ch ), ( ( -. ph /\\ ps ) -> ch ).
    Inference eliminating an antecedent with an additional antecedent.
    (Contributed by NM, 1-Jan-2005.)
    """
    lb = ProofBuilder(sys, "pm2.61ian")
    h1 = lb.hyp("pm2.61ian.1", "( ( ph /\\ ps ) -> ch )")
    h2 = lb.hyp("pm2.61ian.2", "( ( -. ph /\\ ps ) -> ch )")
    s1 = lb.ref("s1", "( ph -> ( ps -> ch ) )", h1, ref="ex", note="ex pm2.61ian.1")
    s2 = lb.ref("s2", "( -. ph -> ( ps -> ch ) )", h2, ref="ex", note="ex pm2.61ian.2")
    res = lb.ref("res", "( ps -> ch )", s1, s2, ref="pm2.61i", note="pm2.61i s1 s2")
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
    h1 = lb.hyp("pm2.65d.1", "( φ → ( ψ → χ ) )")
    h2 = lb.hyp("pm2.65d.2", "( φ → ( ψ → -. χ ) )")
    s1 = lb.ref("s1", "φ → ( -. χ → -. ψ )", h1, ref="con3d", note="con3d h1")
    s2 = lb.ref("s2", "φ → ( ψ → -. ψ )", h2, s1, ref="syld", note="syld h2 s1")
    res = lb.ref("res", "φ → -. ψ", s2, ref="pm2.01d", note="pm2.01d")
    return lb.build(res)


def prove_pm2_65i(sys: System) -> Proof:
    """pm2.65i: -. φ.  Hyps: φ → ψ, φ → -. ψ.

    Inference for proof by contradiction.
    (Contributed by NM, 18-May-1994.)
    set.mm proof: nsyl3 pm2.01i.
    """
    lb = ProofBuilder(sys, "pm2.65i")
    h1 = lb.hyp("pm2.65i.1", "( φ → ψ )")
    h2 = lb.hyp("pm2.65i.2", "( φ → -. ψ )")
    s1 = lb.ref("s1", "( φ → -. φ )", h2, h1, ref="nsyl3", note="nsyl3")
    res = lb.ref("res", "( -. φ )", s1, ref="pm2.01i", note="pm2.01i")
    return lb.build(res)


def prove_pm2_65iold(sys: System) -> Proof:
    """pm2.65iOLD: -. φ.  Hyps: φ → ψ, φ → -. ψ.

    Obsolete version of ~ pm2.65i .
    (Proof modification is discouraged.)  (New usage is discouraged.)
    set.mm proof: wn con2i con3i pm2.61i.
    """
    lb = ProofBuilder(sys, "pm2.65iOLD")
    h1 = lb.hyp("pm2.65iOLD.1", "( φ → ψ )")
    h2 = lb.hyp("pm2.65iOLD.2", "( φ → -. ψ )")
    s_con2i = lb.ref("s_con2i", "( ψ → -. φ )", h2, ref="con2i", note="con2i")
    s_con3i = lb.ref("s_con3i", "( -. ψ → -. φ )", h1, ref="con3i", note="con3i")
    res = lb.ref("res", "( -. φ )", s_con2i, s_con3i, ref="pm2.61i", note="pm2.61i")
    return lb.build(res)


def prove_pm3_2im(sys: System) -> Proof:
    """pm3.2im: ph → ( ps → -. ( ph → -. ps ) ).

    (Contributed by NM, 29-Dec-1992.)
    """
    lb = ProofBuilder(sys, "pm3.2im")
    s1 = lb.ref("s1", "φ → ( ( φ → ¬ ψ ) → ¬ ψ )", ref="pm2.27", note="pm2.27")
    res = lb.ref("res", "φ → ( ψ → ¬ ( φ → ¬ ψ ) )", s1, ref="con2d", note="con2d")
    return lb.build(res)


def prove_jc(sys: System) -> Proof:
    """jc: ph → -. ( ps → -. ch ).  Hyp: ph → ps, ph → ch.

    (Contributed by NM, 29-Dec-1992.)
    """
    lb = ProofBuilder(sys, "jc")
    h1 = lb.hyp("jc.1", "φ → ψ")
    h2 = lb.hyp("jc.2", "φ → χ")
    s_pm3 = lb.ref("s_pm3", "ψ → ( χ → ¬ ( ψ → ¬ χ ) )", ref="pm3.2im", note="pm3.2im")
    res = lb.ref("res", "φ → ¬ ( ψ → ¬ χ )", h1, h2, s_pm3, ref="sylc", note="sylc")
    return lb.build(res)


def prove_jcn(sys: System) -> Proof:
    """jcn: ( ph -> ( -. ps -> -. ( ph -> ps ) ) ).

    Deduction joining consequents.
    (Contributed by NM, 29-Dec-1992.)
    set.mm proof: pm2.27 con3d.
    """
    lb = ProofBuilder(sys, "jcn")
    s1 = lb.ref("s1", "( ph -> ( ( ph -> ps ) -> ps ) )", ref="pm2.27", note="pm2.27")
    res = lb.ref("res", "( ph -> ( -. ps -> -. ( ph -> ps ) ) )", s1, ref="con3d", note="con3d")
    return lb.build(res)


def prove_jcnd(sys: System) -> Proof:
    """jcnd: φ → ¬ ( ψ → χ ).  Hyp: φ → ψ, φ → ¬ χ.

    Deduction joining consequents with negation.
    (Contributed by NM, 29-Dec-1992.)
    set.mm proof: jcn sylc.
    """
    lb = ProofBuilder(sys, "jcnd")
    h1 = lb.hyp("jcnd.1", "φ → ψ")
    h2 = lb.hyp("jcnd.2", "φ → ¬ χ")
    s_jcn = lb.ref("s_jcn", "ψ → ( ¬ χ → ¬ ( ψ → χ ) )", ref="jcn", note="jcn(ps,ch)")
    res = lb.ref("res", "φ → ¬ ( ψ → χ )", h1, h2, s_jcn, ref="sylc", note="sylc")
    return lb.build(res)


def prove_exptOLD(sys: System) -> Proof:
    """exptOLD: ( ( -. ( ph -> -. ps ) -> ch ) -> ( ph -> ( ps -> ch ) ) ).

    Exportation theorem with triple negation.  Obsolete version of ~ expt as
    of 20-Mar-2020.  (Contributed by NM, 29-Dec-1992.)  (Proof modification
    is discouraged.)  (New usage is discouraged.)
    set.mm proof: pm3.2im imim1d com12.
    """
    lb = ProofBuilder(sys, "exptOLD")
    s1 = lb.ref("s1", "φ → ( ψ → ¬ ( φ → ¬ ψ ) )", ref="pm3.2im", note="pm3.2im")
    s2 = lb.ref(
        "s2",
        "φ → ( ( ¬ ( φ → ¬ ψ ) → χ ) → ( ψ → χ ) )",
        s1,
        ref="imim1d",
        note="imim1d",
    )
    res = lb.ref(
        "res",
        "( ¬ ( φ → ¬ ψ ) → χ ) → ( φ → ( ψ → χ ) )",
        s2,
        ref="com12",
        note="com12",
    )
    return lb.build(res)


def prove_expt(sys: System) -> Proof:
    """expt: ( ( -. ( ph -> -. ps ) -> ch ) -> ( ph -> ( ps -> ch ) ) ).

    Exportation theorem.  (Contributed by NM, 20-Mar-2020.)
    set.mm proof: pm3.2im id syl9r.
    """
    lb = ProofBuilder(sys, "expt")
    s1 = lb.ref("s1", "φ → ( ψ → ¬ ( φ → ¬ ψ ) )", ref="pm3.2im", note="pm3.2im")
    s2 = lb.ref(
        "s2",
        "( ¬ ( φ → ¬ ψ ) → χ ) → ( ¬ ( φ → ¬ ψ ) → χ )",
        ref="id",
        note="id",
    )
    res = lb.ref(
        "res",
        "( ¬ ( φ → ¬ ψ ) → χ ) → ( φ → ( ψ → χ ) )",
        s1,
        s2,
        ref="syl9r",
        note="syl9r",
    )
    return lb.build(res)


def prove_pm2_01i(sys: System) -> Proof:
    """pm2.01i: -. φ.  Hyp: φ → -. φ.

    Inference associated with pm2.01.
    (Contributed by NM, 5-Jan-1993.)
    set.mm proof: pm2.01 ax-mp.
    """
    lb = ProofBuilder(sys, "pm2.01i")
    h1 = lb.hyp("pm2.01i.1", "( φ → -. φ )")
    s1 = lb.ref("s1", "( ( φ → -. φ ) → -. φ )", ref="pm2.01", note="pm2.01")
    res = lb.mp("res", h1, s1, "MP hyp, pm2.01")
    return lb.build(res)


def prove_impt(sys: System) -> Proof:
    """impt: ( ( ph -> ( ps -> ch ) ) -> ( -. ( ph -> -. ps ) -> ch ) ).

    Exportation.  (Contributed by NM, 29-Dec-1992.)
    set.mm proof: simprim simplim imim1i mpdi.
    """
    lb = ProofBuilder(sys, "impt")

    # simprim: -. ( ph -> -. ps ) -> ps
    s_simprim = lb.ref("s_simprim", "( -. ( ph -> -. ps ) -> ps )", ref="simprim", note="simprim")

    # simplim: -. ( ph -> -. ps ) -> ph
    s_simplim = lb.ref("s_simplim", "( -. ( ph -> -. ps ) -> ph )", ref="simplim", note="simplim")

    # imim1i with simplim as hyp, chi = ( ps -> ch ):
    # ( ph -> ( ps -> ch ) ) -> ( -. ( ph -> -. ps ) -> ( ps -> ch ) )
    s_imim1i = lb.ref(
        "s_imim1i",
        "( ( ph -> ( ps -> ch ) ) -> ( -. ( ph -> -. ps ) -> ( ps -> ch ) ) )",
        s_simplim,
        ref="imim1i",
        note="imim1i",
    )

    # mpdi with simprim as hyp1 and s_imim1i as hyp2:
    # ( ( ph -> ( ps -> ch ) ) -> ( -. ( ph -> -. ps ) -> ch ) )
    res = lb.ref(
        "res",
        "( ( ph -> ( ps -> ch ) ) -> ( -. ( ph -> -. ps ) -> ch ) )",
        s_simprim,
        s_imim1i,
        ref="mpdi",
        note="mpdi",
    )

    return lb.build(res)


def prove_ori(sys: System) -> Proof:
    """ori: ( -. ph -> ps ).  Hyp: ( ph \\/ ps ).

    Inference associated with df-or.
    (Contributed by NM, 29-Dec-1992.)
    """
    lb = ProofBuilder(sys, "ori")
    h1 = lb.hyp("ori.1", "( ph \\/ ps )")
    df_or = lb.ref(
        "df_or",
        "( ph \\/ ps ) <-> ( -. ph -> ps )",
        ref="df-or",
        note="df-or",
    )
    res = lb.ref("res", "( -. ph -> ps )", h1, df_or, ref="mpbi", note="mpbi")
    return lb.build(res)


def prove_olcnd(sys: System) -> Proof:
    """olcnd: ( ph -> ps ).

    Hyp: olcnd.1: ( ph -> ( ps \\/ ch ) ), olcnd.2: ( ph -> -. ch ).
    Deduction form of ~ ord.  (Contributed by NM, 29-Dec-1992.)
    """
    lb = ProofBuilder(sys, "olcnd")
    h1 = lb.hyp("olcnd.1", "( ph -> ( ps \\/ ch ) )")
    h2 = lb.hyp("olcnd.2", "( ph -> -. ch )")
    s1 = lb.ref("s1", "( ph -> ( -. ps -> ch ) )", h1, ref="ord", note="ord olcnd.1")
    res = lb.ref("res", "( ph -> ps )", h2, s1, ref="mt3d", note="mt3d olcnd.2, s1")
    return lb.build(res)


def prove_ord(sys: System) -> Proof:
    """ord: ( ph -> ( -. ps -> ch ) ).  Hyp: ( ph -> ( ps \\/ ch ) ).

    Inference form of df-or.  Under the Hilbert n-expansion
    (``ps \\/ ch`` expands to ``-. ps -> ch``), the hypothesis is the
    conclusion.
    (Contributed by NM, 29-Dec-1992.)
    """
    lb = ProofBuilder(sys, "ord")
    h1 = lb.hyp("ord.1", "( ph -> ( ps \\/ ch ) )")
    df_or = lb.ref("df_or", "( ps \\/ ch ) <-> ( -. ps -> ch )", ref="df-or", note="df-or")
    forward = lb.ref(
        "forward", "( ps \\/ ch ) -> ( -. ps -> ch )", df_or, ref="biimpi", note="biimpi"
    )
    res = lb.ref("res", "ph -> ( -. ps -> ch )", h1, forward, ref="syl", note="syl")
    return lb.build(res)


def prove_mtand(sys: System) -> Proof:
    r"""mtand: ( ph -> -. ps ).

    Modus tollens deduction with conjunction.
    Hypotheses: ( ph -> -. ch ), ( ( ph /\ ps ) -> ch ).
    (Contributed by NM, 12-Jun-1993.)
    """
    lb = ProofBuilder(sys, "mtand")
    h1 = lb.hyp("mtand.1", "( ph -> -. ch )")
    h2 = lb.hyp("mtand.2", "( ( ph /\\ ps ) -> ch )")
    s1 = lb.ref("s1", "( ph -> ( ps -> ch ) )", h2, ref="ex", note="ex mtand.2")
    res = lb.ref("res", "( ph -> -. ps )", h1, s1, ref="mtod", note="mtod mtand.1, s1")
    return lb.build(res)


def prove_pm2_01da(sys: System) -> Proof:
    """pm2.01da: ( ph -> -. ps ).

    Hyp: ( ( ph /\\ ps ) -> -. ps ).
    Deduction form of pm2.01.
    (Contributed by NM, 18-Aug-1993.)
    set.mm proof: ex pm2.01d.
    """
    lb = ProofBuilder(sys, "pm2.01da")
    h1 = lb.hyp("pm2.01da.1", "( ( ph /\\ ps ) -> -. ps )")
    s1 = lb.ref("s1", "( ph -> ( ps -> -. ps ) )", h1, ref="ex", note="ex")
    res = lb.ref("res", "( ph -> -. ps )", s1, ref="pm2.01d", note="pm2.01d")
    return lb.build(res)


def prove_3ecase(sys: System) -> Proof:
    r"""3ecase: th.

    Hypotheses: ( -. ph -> th ), ( -. ps -> th ), ( -. ch -> th ),
    ( ( ph /\ ps /\ ch ) -> th ).
    Inference eliminating three antecedents by considering all cases
    of their truth values.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3ecase")

    h1 = lb.hyp("3ecase.1", "( -. ph -> th )")
    h2 = lb.hyp("3ecase.2", "( -. ps -> th )")
    h3 = lb.hyp("3ecase.3", "( -. ch -> th )")
    h4 = lb.hyp("3ecase.4", r"( ( ph /\ ps /\ ch ) -> th )")

    s1 = lb.ref(
        "s1",
        "( ph -> ( ps -> ( ch -> th ) ) )",
        h4,
        ref="3exp",
        note="3exp 3ecase.4",
    )

    s2 = lb.ref(
        "s2",
        "( -. ph -> ( ch -> th ) )",
        h1,
        ref="a1d",
        note="a1d 3ecase.1",
    )

    s3 = lb.ref(
        "s3",
        "( -. ps -> ( ch -> th ) )",
        h2,
        ref="a1d",
        note="a1d 3ecase.2",
    )

    s4 = lb.ref(
        "s4",
        "( ch -> th )",
        s1,
        s2,
        s3,
        ref="pm2.61nii",
        note="pm2.61nii s1, s2, s3",
    )

    res = lb.ref(
        "res",
        "th",
        s4,
        h3,
        ref="pm2.61i",
        note="pm2.61i s4, 3ecase.3",
    )

    return lb.build(res)


def prove_4cases(sys: System) -> Proof:
    r"""4cases: ch.

    Hypotheses: ( ( ph /\ ps ) -> ch ), ( ( ph /\ -. ps ) -> ch ),
    ( ( -. ph /\ ps ) -> ch ), ( ( -. ph /\ -. ps ) -> ch ).
    Inference eliminating two antecedents by considering all four cases
    of their truth values.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "4cases")
    h1 = lb.hyp("4cases.1", r"( ( ph /\ ps ) -> ch )")
    h2 = lb.hyp("4cases.2", r"( ( ph /\ -. ps ) -> ch )")
    h3 = lb.hyp("4cases.3", r"( ( -. ph /\ ps ) -> ch )")
    h4 = lb.hyp("4cases.4", r"( ( -. ph /\ -. ps ) -> ch )")
    s1 = lb.ref("s1", "( ps -> ch )", h1, h3, ref="pm2.61ian", note="pm2.61ian")
    s2 = lb.ref("s2", "( -. ps -> ch )", h2, h4, ref="pm2.61ian", note="pm2.61ian")
    res = lb.ref("res", "ch", s1, s2, ref="pm2.61i", note="pm2.61i")
    return lb.build(res)


def prove_4casesdan(sys: System) -> Proof:
    """4casesdan: φ → θ.

    Deduction form of 4cases: from four cases each implying θ
    given φ, conclude φ → θ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "4casesdan")
    h1 = lb.hyp("4casesdan.1", "( ( φ ∧ ( ψ ∧ χ ) ) → θ )")
    h2 = lb.hyp("4casesdan.2", "( ( φ ∧ ( ψ ∧ ¬ χ ) ) → θ )")
    h3 = lb.hyp("4casesdan.3", "( ( φ ∧ ( ¬ ψ ∧ χ ) ) → θ )")
    h4 = lb.hyp("4casesdan.4", "( ( φ ∧ ( ¬ ψ ∧ ¬ χ ) ) → θ )")
    s1 = lb.ref("s1", "( ( ψ ∧ χ ) → ( φ → θ ) )", h1, ref="expcom", note="expcom")
    s2 = lb.ref("s2", "( ( ψ ∧ ¬ χ ) → ( φ → θ ) )", h2, ref="expcom", note="expcom")
    s3 = lb.ref("s3", "( ( ¬ ψ ∧ χ ) → ( φ → θ ) )", h3, ref="expcom", note="expcom")
    s4 = lb.ref("s4", "( ( ¬ ψ ∧ ¬ χ ) → ( φ → θ ) )", h4, ref="expcom", note="expcom")
    res = lb.ref("res", "φ → θ", s1, s2, s3, s4, ref="4cases", note="4cases")
    return lb.build(res)


def prove_inegd(sys: System) -> Proof:
    """inegd: ( ph -> -. ps ).

    Hyp: inegd.1 |- ( ( ph /\\ ps ) -> F. ).
    Deduction form of dfnot: from a conjunction implying falsehood,
    derive the negation of the second conjunct.
    (Contributed by NM, 2-Jan-2002.)
    """
    lb = ProofBuilder(sys, "inegd")
    h1 = lb.hyp("inegd.1", "( ( ph /\\ ps ) -> F. )")
    s1 = lb.ref("s1", "( ph -> ( ps -> F. ) )", h1, ref="ex", note="ex")
    s2 = lb.ref("s2", "( -. ps <-> ( ps -> F. ) )", ref="dfnot", note="dfnot")
    res = lb.ref("res", "( ph -> -. ps )", s1, s2, ref="sylibr", note="sylibr")
    return lb.build(res)


def prove_mpnanrd(sys: System) -> Proof:
    """mpnanrd: φ → ¬ χ.

    Deduction form of mpnanr: from φ → ψ and φ → ¬ (ψ ∧ χ),
    conclude φ → ¬ χ.
    (Contributed by NM, 21-Apr-1994.)
    """
    lb = ProofBuilder(sys, "mpnanrd")
    h1 = lb.hyp("mpnanrd.1", "φ → ψ")
    h2 = lb.hyp("mpnanrd.2", "φ → ¬ ( ψ ∧ χ )")
    s1 = lb.ref(
        "s1",
        "( ψ → ¬ χ ) ↔ ¬ ( ψ ∧ χ )",
        ref="imnan",
        note="imnan",
    )
    s2 = lb.ref(
        "s2",
        "φ → ( ψ → ¬ χ )",
        h2,
        s1,
        ref="sylibr",
        note="sylibr",
    )
    res = lb.ref("res", "φ → ¬ χ", h1, s2, ref="mpd", note="mpd")
    return lb.build(res)


def prove_mptnan(sys: System) -> Proof:
    """mptnan: ¬ ψ.

    Modus ponendo tollens: from φ and ¬ (φ ∧ ψ), infer ¬ ψ.
    """
    lb = ProofBuilder(sys, "mptnan")
    h1 = lb.hyp("mptnan.min", "φ")
    h2 = lb.hyp("mptnan.maj", "¬ ( φ ∧ ψ )")
    s1 = lb.ref("s1", "φ → ¬ ψ", h2, ref="imnani", note="imnani")
    res = lb.mp("res", h1, s1, "MP: mptnan.min, s1")
    return lb.build(res)


def prove_merlem7(sys: System) -> Proof:
    """merlem7: φ → ( ( ( ψ → χ ) → θ ) → ( ( ( χ → τ ) → ( ¬ θ → ¬ ψ ) ) → θ ) ).

    Seventh lemma towards deriving the Łukasiewicz axioms from Meredith's
    sole axiom.  (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "merlem7")

    s1 = lb.ref(
        "s1",
        "( ψ → χ ) → ( ( ( ψ → χ ) → θ ) → ( ( ( χ → τ ) → ( ¬ θ → ¬ ψ ) ) → θ ) )",
        ref="merlem4",
        note="merlem4",
    )

    s2 = lb.ref(
        "s2",
        "( ( ( χ → τ ) → ( ¬ θ → ¬ ψ ) ) → θ ) → ( ( ( ( ( ψ → χ ) → θ ) → ( ( ( χ → τ ) → ( ¬ θ → ¬ ψ ) ) → θ ) ) → ¬ φ ) → ( ¬ χ → ¬ φ ) )",
        ref="merlem6",
        note="merlem6",
    )

    s3 = lb.ref(
        "s3",
        "( ( ( ( χ → τ ) → ( ¬ θ → ¬ ψ ) ) → θ ) → ( ( ( ( ( ψ → χ ) → θ ) → ( ( ( χ → τ ) → ( ¬ θ → ¬ ψ ) ) → θ ) ) → ¬ φ ) → ( ¬ χ → ¬ φ ) ) ) → ( ( ( ( ( ( ( ψ → χ ) → θ ) → ( ( ( χ → τ ) → ( ¬ θ → ¬ ψ ) ) → θ ) ) → ¬ φ ) → ( ¬ χ → ¬ φ ) ) → χ ) → ( ψ → χ ) )",
        ref="meredith",
        note="meredith",
    )

    s4 = lb.mp("s4", s2, s3, note="MP s2, s3")

    s5 = lb.ref(
        "s5",
        "( ( ( ( ( ( ( ψ → χ ) → θ ) → ( ( ( χ → τ ) → ( ¬ θ → ¬ ψ ) ) → θ ) ) → ¬ φ ) → ( ¬ χ → ¬ φ ) ) → χ ) → ( ψ → χ ) ) → ( ( ( ψ → χ ) → ( ( ( ψ → χ ) → θ ) → ( ( ( χ → τ ) → ( ¬ θ → ¬ ψ ) ) → θ ) ) ) → ( φ → ( ( ( ψ → χ ) → θ ) → ( ( ( χ → τ ) → ( ¬ θ → ¬ ψ ) ) → θ ) ) ) )",
        ref="meredith",
        note="meredith",
    )

    s6 = lb.mp("s6", s4, s5, note="MP s4, s5")

    res = lb.mp("res", s1, s6, note="MP s1, s6")

    return lb.build(res)


def prove_merlem8(sys: System) -> Proof:
    """merlem8: ( ( ( ψ → χ ) → θ ) → ( ( ( χ → τ ) → ( ¬ θ → ¬ ψ ) ) → θ ) ).

    Eighth lemma towards deriving the Łukasiewicz axioms from Meredith's
    sole axiom.  (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "merlem8")

    s1 = lb.ref(
        "s1",
        "φ → ( ( ( ψ → χ ) → θ ) → ( ( ( χ → τ ) → ( ¬ θ → ¬ ψ ) ) → θ ) )",
        ref="merlem7",
        note="merlem7",
    )

    s2 = lb.ref(
        "s2",
        "( φ → ( ( ( ψ → χ ) → θ ) → ( ( ( χ → τ ) → ( ¬ θ → ¬ ψ ) ) → θ ) ) ) → ( ( ( ψ → χ ) → θ ) → ( ( ( χ → τ ) → ( ¬ θ → ¬ ψ ) ) → θ ) )",
        ref="merlem7",
        note="merlem7",
    )

    res = lb.mp("res", s1, s2, note="MP s1, s2")

    return lb.build(res)


def prove_merlem5(sys: System) -> Proof:
    """merlem5: ( φ → ψ ) → ( ¬ ¬ φ → ψ ).

    Fifth lemma towards deriving the Łukasiewicz axioms from Meredith's
    sole axiom.  (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "merlem5")

    # meredith(ψ, ψ, ψ, ψ, ψ)
    s1 = lb.ref(
        "s1",
        "( ( ( ( ( ψ → ψ ) → ( ¬ ψ → ¬ ψ ) ) → ψ ) → ψ ) → ( ( ψ → ψ ) → ( ψ → ψ ) ) )",
        ref="meredith",
        note="meredith",
    )

    # meredith(ψ, ψ, ψ, ¬¬φ, φ)
    s2 = lb.ref(
        "s2",
        "( ( ( ( ( ψ → ψ ) → ( ¬ ψ → ¬ ¬ ¬ φ ) ) → ψ ) → φ ) → ( ( φ → ψ ) → ( ¬ ¬ φ → ψ ) ) )",
        ref="meredith",
        note="meredith",
    )

    # merlem1 with:
    #   χ = ( φ → ψ ) → ( ¬ ¬ φ → ψ ),
    #   φ = ¬ φ,  ψ = ¬ B,  τ = ¬ B
    # where B = s1's formula
    B = "( ( ( ( ( ψ → ψ ) → ( ¬ ψ → ¬ ψ ) ) → ψ ) → ψ ) → ( ( ψ → ψ ) → ( ψ → ψ ) ) )"
    AB = "( ( φ → ψ ) → ( ¬ ¬ φ → ψ ) )"
    s3 = lb.ref(
        "s3",
        f"( ( {AB} → ¬ {B} ) → ( ¬ φ → ¬ {B} ) )",
        ref="merlem1",
        note="merlem1",
    )

    # merlem4 with:
    #   τ = s3,  φ = φ,  θ = ( ( ψ → ψ ) → ( ¬ ψ → ¬ ¬ ¬ φ ) ) → ψ
    # giving: s3 → ( ( s3 → φ ) → ( ( ( ( ψ → ψ ) → ( ¬ ψ → ¬ ¬ ¬ φ ) ) → ψ ) → φ ) )
    C_body = "( ( ( ψ → ψ ) → ( ¬ ψ → ¬ ¬ ¬ φ ) ) → ψ )"
    C_full = f"( {C_body} → φ )"
    s3_fml = f"( ( {AB} → ¬ {B} ) → ( ¬ φ → ¬ {B} ) )"
    s4 = lb.ref(
        "s4",
        f"( {s3_fml} → ( ( {s3_fml} → φ ) → ( {C_full} ) ) )",
        ref="merlem4",
        note="merlem4",
    )

    # ax-mp(3, 4): ( s3 → φ ) → C_full
    s5 = lb.mp(
        "s5",
        s3,
        s4,
        note="MP s3, s4",
    )

    # meredith:
    # s6 = s5 → ( s2 → ( B → AB ) )
    s6 = lb.ref(
        "s6",
        f"( ( {s3_fml} → φ ) → {C_full} ) → ( ( {C_full} → {AB} ) → ( {B} → {AB} ) )",
        ref="meredith",
        note="meredith",
    )

    # ax-mp(5, 6): s2 → ( B → AB )
    s7 = lb.mp(
        "s7",
        s5,
        s6,
        note="MP s5, s6",
    )

    # ax-mp(2, 7): B → AB
    s8 = lb.mp(
        "s8",
        s2,
        s7,
        note="MP s2, s7",
    )

    # ax-mp(1, 8) → conclusion: AB = ( φ → ψ ) → ( ¬ ¬ φ → ψ )
    res = lb.mp(
        "res",
        s1,
        s8,
        note="MP s1, s8",
    )

    return lb.build(res)


def prove_merlem12(sys: System) -> Proof:
    """merlem12: ( ( ( θ → ( ¬ ¬ χ → χ ) ) → φ ) → φ ).

    Twelfth lemma towards deriving the Łukasiewicz axioms from Meredith's
    sole axiom.  (Contributed by NM, 14-Dec-2002.)
    """
    lb = ProofBuilder(sys, "merlem12")

    # merlem5(χ, χ): ( ( χ → χ ) → ( ¬ ¬ χ → χ ) )
    s1 = lb.ref(
        "s1",
        "( ( χ → χ ) → ( ¬ ¬ χ → χ ) )",
        ref="merlem5",
        note="merlem5",
    )

    # merlem2: ( ( ( φ → φ ) → χ ) → ( θ → χ ) )
    # with φ = χ, χ = ( ¬ ¬ χ → χ ), θ = θ
    s2 = lb.ref(
        "s2",
        "( ( ( χ → χ ) → ( ¬ ¬ χ → χ ) ) → ( θ → ( ¬ ¬ χ → χ ) ) )",
        ref="merlem2",
        note="merlem2",
    )

    # ax-mp(1, 2): θ → ( ¬ ¬ χ → χ )
    s3 = lb.mp("s3", s1, s2, note="MP s1, s2")

    # merlem4: τ → ( ( τ → φ ) → ( θ → φ ) )
    # with τ = ( θ → ( ¬ ¬ χ → χ ) ),
    #      φ = φ,
    #      θ = ( ( θ → ( ¬ ¬ χ → χ ) ) → φ )
    T = "( θ → ( ¬ ¬ χ → χ ) )"
    s4 = lb.ref(
        "s4",
        f"( {T} → ( ( {T} → φ ) → ( ( {T} → φ ) → φ ) ) )",
        ref="merlem4",
        note="merlem4",
    )

    # ax-mp(3, 4)
    s5 = lb.mp("s5", s3, s4, note="MP s3, s4")

    # merlem11: ( φ → ( φ → ψ ) ) → ( φ → ψ )
    # with φ = ( ( θ → ( ¬ ¬ χ → χ ) ) → φ ),
    #      ψ = φ
    s6 = lb.ref(
        "s6",
        f"( ( {T} → φ ) → ( ( {T} → φ ) → φ ) ) → ( ( {T} → φ ) → φ )",
        ref="merlem11",
        note="merlem11",
    )

    # ax-mp(5, 6) → conclusion
    res = lb.mp("res", s5, s6, note="MP s5, s6")

    return lb.build(res)


def prove_re2luk2(sys: System) -> Proof:
    """re2luk2: ( ¬ φ → φ ) → φ.

    Derivation of one of the Łukasiewicz axioms from Russell-Bernays'.
    This is essentially the converse of the law of Clavius.
    """
    lb = ProofBuilder(sys, "re2luk2")

    # Step 1: rb-ax4 → ¬ ( φ ∨ φ ) ∨ φ
    s1 = lb.ref("s1", "¬ ( φ ∨ φ ) ∨ φ", ref="rb-ax4", note="rb-ax4")

    # Step 3: rb-ax3 → ¬ φ ∨ ( φ ∨ φ )
    s3 = lb.ref("s3", "¬ φ ∨ ( φ ∨ φ )", ref="rb-ax3", note="rb-ax3")

    # Step 4: rbsyl(s1, s3) → ¬ φ ∨ φ
    s4 = lb.ref("s4", "¬ φ ∨ φ", s1, s3, ref="rbsyl", note="rbsyl")

    # Step 5: rb-ax4 with ¬¬φ → ¬ ( ¬ ¬ φ ∨ ¬ ¬ φ ) ∨ ¬ ¬ φ
    s5 = lb.ref(
        "s5",
        "¬ ( ¬ ¬ φ ∨ ¬ ¬ φ ) ∨ ¬ ¬ φ",
        ref="rb-ax4",
        note="rb-ax4",
    )

    # Step 6: rb-ax3 with ¬¬φ, ¬¬φ → ¬ ¬ ¬ φ ∨ ( ¬ ¬ φ ∨ ¬ ¬ φ )
    s6 = lb.ref(
        "s6",
        "¬ ¬ ¬ φ ∨ ( ¬ ¬ φ ∨ ¬ ¬ φ )",
        ref="rb-ax3",
        note="rb-ax3",
    )

    # Step 7: rbsyl(s5, s6) → ¬ ¬ ¬ φ ∨ ¬ ¬ φ
    s7 = lb.ref(
        "s7",
        "¬ ¬ ¬ φ ∨ ¬ ¬ φ",
        s5,
        s6,
        ref="rbsyl",
        note="rbsyl",
    )

    # Step 8: rb-ax2 with ¬¬¬φ, ¬¬φ → ¬ ( ¬ ¬ ¬ φ ∨ ¬ ¬ φ ) ∨ ( ¬ ¬ φ ∨ ¬ ¬ ¬ φ )
    s8 = lb.ref(
        "s8",
        "¬ ( ¬ ¬ ¬ φ ∨ ¬ ¬ φ ) ∨ ( ¬ ¬ φ ∨ ¬ ¬ ¬ φ )",
        ref="rb-ax2",
        note="rb-ax2",
    )

    # Step 9: anmp(s7, s8) → ¬ ¬ φ ∨ ¬ ¬ ¬ φ
    s9 = lb.ref(
        "s9",
        "¬ ¬ φ ∨ ¬ ¬ ¬ φ",
        s7,
        s8,
        ref="anmp",
        note="anmp",
    )

    # Step 11: rblem1(s9, s4) → ¬ ( ¬ φ ∨ φ ) ∨ ( ¬ ¬ ¬ φ ∨ φ )
    s11 = lb.ref(
        "s11",
        "¬ ( ¬ φ ∨ φ ) ∨ ( ¬ ¬ ¬ φ ∨ φ )",
        s9,
        s4,
        ref="rblem1",
        note="rblem1",
    )

    # Step 12: anmp(s4, s11) → ¬ ¬ ¬ φ ∨ φ
    s12 = lb.ref(
        "s12",
        "¬ ¬ ¬ φ ∨ φ",
        s4,
        s11,
        ref="anmp",
        note="anmp",
    )

    # Step 14: rblem1(s12, s4) → ¬ ( ¬ ¬ φ ∨ φ ) ∨ ( φ ∨ φ )
    s14 = lb.ref(
        "s14",
        "¬ ( ¬ ¬ φ ∨ φ ) ∨ ( φ ∨ φ )",
        s12,
        s4,
        ref="rblem1",
        note="rblem1",
    )

    # Step 15: rbsyl(s1, s14) → ¬ ( ¬ ¬ φ ∨ φ ) ∨ φ
    s15 = lb.ref(
        "s15",
        "¬ ( ¬ ¬ φ ∨ φ ) ∨ φ",
        s1,
        s14,
        ref="rbsyl",
        note="rbsyl",
    )

    # Step 16: rb-imdf with ph = ¬ φ, ps = φ
    s16 = lb.ref(
        "s16",
        ("¬ ( ¬ ( ¬ ( ¬ φ → φ ) ∨ ( ¬ ¬ φ ∨ φ ) ) ∨ ¬ ( ¬ ( ¬ ¬ φ ∨ φ ) ∨ ( ¬ φ → φ ) ) )"),
        ref="rb-imdf",
        note="rb-imdf",
    )

    # Step 17: rblem6(s16) → ¬ ( ¬ φ → φ ) ∨ ( ¬ ¬ φ ∨ φ )
    s17 = lb.ref(
        "s17",
        "¬ ( ¬ φ → φ ) ∨ ( ¬ ¬ φ ∨ φ )",
        s16,
        ref="rblem6",
        note="rblem6",
    )

    # Step 18: rbsyl(s15, s17) → ¬ ( ¬ φ → φ ) ∨ φ
    s18 = lb.ref(
        "s18",
        "¬ ( ¬ φ → φ ) ∨ φ",
        s15,
        s17,
        ref="rbsyl",
        note="rbsyl",
    )

    # Step 19: rb-imdf with ph = ( ¬ φ → φ ), ps = φ
    s19 = lb.ref(
        "s19",
        (
            "¬ ( ¬ ( ¬ ( ( ¬ φ → φ ) → φ ) ∨ ( ¬ ( ¬ φ → φ ) ∨ φ ) ) ∨ "
            "¬ ( ¬ ( ¬ ( ¬ φ → φ ) ∨ φ ) ∨ ( ( ¬ φ → φ ) → φ ) ) )"
        ),
        ref="rb-imdf",
        note="rb-imdf",
    )

    # Step 20: rblem7(s19) → ¬ ( ¬ ( ¬ φ → φ ) ∨ φ ) ∨ ( ( ¬ φ → φ ) → φ )
    s20 = lb.ref(
        "s20",
        "¬ ( ¬ ( ¬ φ → φ ) ∨ φ ) ∨ ( ( ¬ φ → φ ) → φ )",
        s19,
        ref="rblem7",
        note="rblem7",
    )

    # Step 21: anmp(s18, s20) → ( ¬ φ → φ ) → φ
    res = lb.ref(
        "res",
        "( ¬ φ → φ ) → φ",
        s18,
        s20,
        ref="anmp",
        note="anmp",
    )

    return lb.build(res)


def prove_re2luk3(sys: System) -> Proof:
    """re2luk3: φ → (¬ φ → ψ).

    Derivation of Łukasiewicz's third axiom from Russell-Bernays'.
    This is the principle of explosion (Duns Scotus law).
    """
    lb = ProofBuilder(sys, "re2luk3")

    # rb-imdf with ph=¬ φ, ps=ψ
    s1 = lb.ref(
        "s1",
        "¬ ( ¬ ( ¬ ( ¬ φ → ψ ) ∨ ( ¬ ¬ φ ∨ ψ ) ) ∨ ¬ ( ¬ ( ¬ ¬ φ ∨ ψ ) ∨ ( ¬ φ → ψ ) ) )",
        ref="rb-imdf",
        note="rb-imdf",
    )

    # rblem7 extracts one direction: ¬ ( ¬ ¬ φ ∨ ψ ) ∨ ( ¬ φ → ψ )
    s2 = lb.ref(
        "s2",
        "¬ ( ¬ ¬ φ ∨ ψ ) ∨ ( ¬ φ → ψ )",
        s1,
        ref="rblem7",
        note="rblem7",
    )

    # rb-ax4 with ph=¬ φ: ¬ ( ¬ φ ∨ ¬ φ ) ∨ ¬ φ
    s3 = lb.ref("s3", "¬ ( ¬ φ ∨ ¬ φ ) ∨ ¬ φ", ref="rb-ax4", note="rb-ax4")

    # rb-ax3 with ph=¬ φ: ¬ ¬ φ ∨ ( ¬ φ ∨ ¬ φ )
    s4 = lb.ref("s4", "¬ ¬ φ ∨ ( ¬ φ ∨ ¬ φ )", ref="rb-ax3", note="rb-ax3")

    # rbsyl: ¬ A ∨ B, ¬ C ∨ A ⊢ ¬ C ∨ B
    # s3: A = ¬ φ ∨ ¬ φ, B = ¬ φ
    # s4: C = ¬ φ, A = ¬ φ ∨ ¬ φ ⇒ result = ¬ C ∨ B = ¬ ¬ φ ∨ ¬ φ
    s5 = lb.ref("s5", "¬ ¬ φ ∨ ¬ φ", s3, s4, ref="rbsyl", note="rbsyl")

    # rb-ax2 with ph=¬ ¬ φ, ps=¬ φ
    s6 = lb.ref(
        "s6",
        "¬ ( ¬ ¬ φ ∨ ¬ φ ) ∨ ( ¬ φ ∨ ¬ ¬ φ )",
        ref="rb-ax2",
        note="rb-ax2",
    )

    # anmp: A ∨ B, ¬ ( A ∨ B ) ∨ C ⊢ C
    # s5: A = ¬ ¬ φ, B = ¬ φ
    # s6: ¬ ( A ∨ B ) ∨ C, C = ¬ φ ∨ ¬ ¬ φ ⇒ result = C
    s7 = lb.ref("s7", "¬ φ ∨ ¬ ¬ φ", s5, s6, ref="anmp", note="anmp")

    # rblem2 with ph=¬ φ, ps=¬ ¬ φ, ch=ψ
    s8 = lb.ref(
        "s8",
        "¬ ( ¬ φ ∨ ¬ ¬ φ ) ∨ ( ¬ φ ∨ ( ¬ ¬ φ ∨ ψ ) )",
        ref="rblem2",
        note="rblem2",
    )

    # anmp: s7 = A ∨ B, s8 = ¬ ( A ∨ B ) ∨ C ⊢ C
    # A = ¬ φ, B = ¬ ¬ φ, C = ¬ φ ∨ ( ¬ ¬ φ ∨ ψ )
    s9 = lb.ref(
        "s9",
        "¬ φ ∨ ( ¬ ¬ φ ∨ ψ )",
        s7,
        s8,
        ref="anmp",
        note="anmp",
    )

    # rbsyl: s2 = ¬ A ∨ B, s9 = ¬ C ∨ A ⊢ ¬ C ∨ B
    # s2: A = ¬ ¬ φ ∨ ψ, B = ¬ φ → ψ
    # s9: C = φ, A = ¬ ¬ φ ∨ ψ ⇒ result = ¬ φ ∨ ( ¬ φ → ψ )
    s10 = lb.ref(
        "s10",
        "¬ φ ∨ ( ¬ φ → ψ )",
        s2,
        s9,
        ref="rbsyl",
        note="rbsyl",
    )

    # rb-imdf with ph=φ, ps=( ¬ φ → ψ )
    s11 = lb.ref(
        "s11",
        (
            "¬ ( ¬ ( ¬ ( φ → ( ¬ φ → ψ ) ) ∨ ( ¬ φ ∨ ( ¬ φ → ψ ) ) ) ∨ "
            "¬ ( ¬ ( ¬ φ ∨ ( ¬ φ → ψ ) ) ∨ ( φ → ( ¬ φ → ψ ) ) ) )"
        ),
        ref="rb-imdf",
        note="rb-imdf",
    )

    # rblem7 extracts: ¬ ( ¬ φ ∨ ( ¬ φ → ψ ) ) ∨ ( φ → ( ¬ φ → ψ ) )
    s12 = lb.ref(
        "s12",
        "¬ ( ¬ φ ∨ ( ¬ φ → ψ ) ) ∨ ( φ → ( ¬ φ → ψ ) )",
        s11,
        ref="rblem7",
        note="rblem7",
    )

    # anmp: s10 = A ∨ B, s12 = ¬ ( A ∨ B ) ∨ C ⊢ C
    # s10: A = ¬ φ, B = ¬ φ → ψ
    # s12: C = φ → ( ¬ φ → ψ ) ⇒ result = C
    res = lb.ref(
        "res",
        "φ → ( ¬ φ → ψ )",
        s10,
        s12,
        ref="anmp",
        note="anmp",
    )

    return lb.build(res)


def prove_re1luk2(sys: System) -> Proof:
    """re1luk2: ( ¬ φ → φ ) → φ.

    Re-derivation of one of the Łukasiewicz axioms from
    Tarski-Bernays-Wajsberg'.  This is the converse of the law
    of Clavius.  (Contributed by Anthony Hart, 16-Aug-2011.)
    """
    lb = ProofBuilder(sys, "re1luk2")

    # tbw-negdf with φ=φ
    s1 = lb.ref(
        "s1",
        "( ( ( ¬ φ → ( φ → ⊥ ) ) → ( ( ( φ → ⊥ ) → ¬ φ ) → ⊥ ) ) → ⊥ )",
        ref="tbw-negdf",
        note="tbw-negdf",
    )

    # tbw-ax2 with φ=( ( ( φ → ⊥ ) → ¬ φ ) → ⊥ ), ψ=( ¬ φ → ( φ → ⊥ ) )
    s2 = lb.ref(
        "s2",
        "( ( ( ( φ → ⊥ ) → ¬ φ ) → ⊥ ) → ( ( ¬ φ → ( φ → ⊥ ) ) → ( ( ( φ → ⊥ ) → ¬ φ ) → ⊥ ) ) )",
        ref="tbw-ax2",
        note="tbw-ax2",
    )

    # tbwlem4 with φ=( ( φ → ⊥ ) → ¬ φ ),
    # ψ=( ( ¬ φ → ( φ → ⊥ ) ) → ( ( ( φ → ⊥ ) → ¬ φ ) → ⊥ ) )
    s3 = lb.ref(
        "s3",
        "( ( ( ( ( φ → ⊥ ) → ¬ φ ) → ⊥ ) → ( ( ¬ φ → ( φ → ⊥ ) ) → ( ( ( φ → ⊥ ) → ¬ φ ) → ⊥ ) ) ) → ( ( ( ( ¬ φ → ( φ → ⊥ ) ) → ( ( ( φ → ⊥ ) → ¬ φ ) → ⊥ ) ) → ⊥ ) → ( ( φ → ⊥ ) → ¬ φ ) ) )",
        ref="tbwlem4",
        note="tbwlem4",
    )

    # ax-mp(2, 3)
    s4 = lb.mp("s4", s2, s3, "MP s2, s3")

    # ax-mp(1, 4)
    s5 = lb.mp("s5", s1, s4, "MP s1, s4")

    # tbw-ax1 with φ=( φ → ⊥ ), ψ=¬ φ, χ=φ
    s6 = lb.ref(
        "s6",
        "( ( ( φ → ⊥ ) → ¬ φ ) → ( ( ¬ φ → φ ) → ( ( φ → ⊥ ) → φ ) ) )",
        ref="tbw-ax1",
        note="tbw-ax1",
    )

    # ax-mp(5, 6)
    s7 = lb.mp("s7", s5, s6, "MP s5, s6")

    # tbw-ax3 with φ=φ, ψ=⊥
    s8 = lb.ref(
        "s8",
        "( ( ( φ → ⊥ ) → φ ) → φ )",
        ref="tbw-ax3",
        note="tbw-ax3",
    )

    # tbwsyl(s7, s8) → ( ¬ φ → φ ) → φ
    res = lb.ref(
        "res",
        "( ¬ φ → φ ) → φ",
        s7,
        s8,
        ref="tbwsyl",
        note="tbwsyl",
    )

    return lb.build(res)


def prove_re1luk3(sys: System) -> Proof:
    """re1luk3: φ → (¬ φ → ψ).

    Re-derivation of Łukasiewicz's third axiom from
    Tarski-Bernays-Wajsberg'.  (Contributed by Anthony Hart,
    16-Aug-2011.)
    """
    lb = ProofBuilder(sys, "re1luk3")

    # tbw-ax4 with φ=ψ: ⊥ → ψ
    s1 = lb.ref("s1", "⊥ → ψ", ref="tbw-ax4", note="tbw-ax4")

    # tbw-ax1 with φ=(φ→⊥), ψ=⊥, χ=ψ: (φ → ⊥) → ((⊥ → ψ) → (φ → ψ))
    s2 = lb.ref(
        "s2",
        "( φ → ⊥ ) → ( ( ⊥ → ψ ) → ( φ → ψ ) )",
        ref="tbw-ax1",
        note="tbw-ax1",
    )

    # tbwlem1 swaps antecedents in s2
    s3 = lb.ref(
        "s3",
        "( ( φ → ⊥ ) → ( ( ⊥ → ψ ) → ( φ → ψ ) ) ) → ( ( ⊥ → ψ ) → ( ( φ → ⊥ ) → ( φ → ψ ) ) )",
        ref="tbwlem1",
        note="tbwlem1",
    )

    # MP(s2, s3): (⊥ → ψ) → ((φ → ⊥) → (φ → ψ))
    s4 = lb.mp("s4", s2, s3, "MP s2, s3")

    # MP(s1, s4): (φ → ⊥) → (φ → ψ)
    s5 = lb.mp("s5", s1, s4, "MP s1, s4")

    # tbwlem1 with φ=(φ→⊥), ψ=φ, χ=ψ:
    # ((φ → ⊥) → (φ → ψ)) → (φ → ((φ → ⊥) → ψ))
    s6 = lb.ref(
        "s6",
        "( ( φ → ⊥ ) → ( φ → ψ ) ) → ( φ → ( ( φ → ⊥ ) → ψ ) )",
        ref="tbwlem1",
        note="tbwlem1",
    )

    # MP(s5, s6): φ → ((φ → ⊥) → ψ)  [tbwsyl.1]
    s7 = lb.mp("s7", s5, s6, "MP s5, s6")

    # tbw-negdf with φ=φ
    s8 = lb.ref(
        "s8",
        "( ( ( ¬ φ → ( φ → ⊥ ) ) → ( ( ( φ → ⊥ ) → ¬ φ ) → ⊥ ) ) → ⊥ )",
        ref="tbw-negdf",
        note="tbw-negdf",
    )

    # tbwlem5 with φ=(¬ φ → (φ → ⊥)), ψ=((φ → ⊥) → ¬ φ)
    s9 = lb.ref(
        "s9",
        "( ( ( ( ¬ φ → ( φ → ⊥ ) ) → ( ( ( φ → ⊥ ) → ¬ φ ) → ⊥ ) ) → ⊥ ) → ( ¬ φ → ( φ → ⊥ ) ) )",
        ref="tbwlem5",
        note="tbwlem5",
    )

    # MP(s8, s9): ¬ φ → (φ → ⊥)
    s10 = lb.mp("s10", s8, s9, "MP s8, s9")

    # tbw-ax1 with φ=¬φ, ψ=(φ→⊥), χ=ψ
    s11 = lb.ref(
        "s11",
        "( ¬ φ → ( φ → ⊥ ) ) → ( ( ( φ → ⊥ ) → ψ ) → ( ¬ φ → ψ ) )",
        ref="tbw-ax1",
        note="tbw-ax1",
    )

    # MP(s10, s11): ((φ → ⊥) → ψ) → (¬ φ → ψ)  [tbwsyl.2]
    s12 = lb.mp("s12", s10, s11, "MP s10, s11")

    # tbwsyl(s7, s12): φ → (¬ φ → ψ)
    s13 = lb.ref(
        "s13",
        "φ → ( ¬ φ → ψ )",
        s7,
        s12,
        ref="tbwsyl",
        note="tbwsyl",
    )

    return lb.build(s13)


def prove_luk_2(sys: System) -> Proof:
    """luk-2: ( ¬ φ → φ ) → φ.

    One of the three Łukasiewicz axioms for propositional calculus,
    derived from Meredith's sole axiom.
    """
    lb = ProofBuilder(sys, "luk-2")
    res = lb.ref("res", "( ¬ φ → φ ) → φ", ref="re2luk2", note="re2luk2")
    return lb.build(res)


def prove_luk_3(sys: System) -> Proof:
    """luk-3: φ → ( ¬ φ → ψ ).

    One of the three Łukasiewicz axioms for propositional calculus,
    derived from Meredith's sole axiom.
    """
    lb = ProofBuilder(sys, "luk-3")

    # merlem11 with φ := ¬ φ, ψ := ψ: (¬ φ → (¬ φ → ψ)) → (¬ φ → ψ)
    s1 = lb.ref(
        "s1",
        "( ¬ φ → ( ¬ φ → ψ ) ) → ( ¬ φ → ψ )",
        ref="merlem11",
        note="merlem11",
    )

    # merlem1 with χ := ¬ φ, τ := (¬ φ → ψ):
    # (((¬ φ → (¬ φ → ψ)) → (¬ φ → ψ)) → (φ → (¬ φ → ψ)))
    s2 = lb.ref(
        "s2",
        "( ( ¬ φ → ( ¬ φ → ψ ) ) → ( ¬ φ → ψ ) ) → ( φ → ( ¬ φ → ψ ) )",
        ref="merlem1",
        note="merlem1",
    )

    # ax-mp: s1 is the minor premise, s2 is the major premise
    res = lb.mp("res", s1, s2, note="MP s1, s2")

    return lb.build(res)


def prove_ax13v(sys: System) -> Proof:
    """ax13v: ¬ x = y → ( y = z → ∀ x y = z ).

    Axiom scheme ax-13 with distinct variable conditions removed.
    (Contributed by NM, 7-Aug-2004.)
    """
    lb = ProofBuilder(sys, "ax13v")

    res = lb.ref(
        "res",
        "¬ x = y → ( y = z → ∀ x y = z )",
        ref="ax-13",
        note="ax-13",
    )

    return lb.build(res)


def prove_ax13lem1(sys: System) -> Proof:
    """ax13lem1: ¬ x = y → ( z = y → ∀ x z = y ).

    A version of ax13v with one distinct variable restriction dropped.
    (Contributed by Wolf Lammen, 8-Sep-2018.)
    """
    lb = ProofBuilder(sys, "ax13lem1")

    # equvinva with x:=z, y:=y: z = y → ∃ w ( z = w ∧ y = w )
    s1 = lb.ref(
        "s1",
        "z = y → ∃ w ( z = w ∧ y = w )",
        ref="equvinva",
        note="equvinva",
    )

    # ax13v with z:=w: ¬ x = y → ( y = w → ∀ x y = w )
    s2 = lb.ref(
        "s2",
        "¬ x = y → ( y = w → ∀ x y = w )",
        ref="ax13v",
        note="ax13v",
    )

    # equeucl with x:=z, y:=y, z:=w: z = w → ( y = w → z = y )
    s3 = lb.ref(
        "s3",
        "z = w → ( y = w → z = y )",
        ref="equeucl",
        note="equeucl",
    )

    # alimdv: from s3, deduce z = w → ( ∀ x y = w → ∀ x z = y )
    s4 = lb.ref(
        "s4",
        "z = w → ( ∀ x y = w → ∀ x z = y )",
        s3,
        ref="alimdv",
        note="alimdv equeucl",
    )

    # syl9: from s2 and s4, deduce ¬ x = y → ( z = w → ( y = w → ∀ x z = y ) )
    s5 = lb.ref(
        "s5",
        "¬ x = y → ( z = w → ( y = w → ∀ x z = y ) )",
        s2,
        s4,
        ref="syl9",
        note="syl9 ax13v, alimdv",
    )

    # impd: from s5, deduce ¬ x = y → ( ( z = w ∧ y = w ) → ∀ x z = y )
    s6 = lb.ref(
        "s6",
        "¬ x = y → ( ( z = w ∧ y = w ) → ∀ x z = y )",
        s5,
        ref="impd",
        note="impd syl9",
    )

    # exlimdv: from s6, deduce ¬ x = y → ( ∃ w ( z = w ∧ y = w ) → ∀ x z = y )
    s7 = lb.ref(
        "s7",
        "¬ x = y → ( ∃ w ( z = w ∧ y = w ) → ∀ x z = y )",
        s6,
        ref="exlimdv",
        note="exlimdv impd",
    )

    # syl5: from s1 and s7, deduce ¬ x = y → ( z = y → ∀ x z = y )
    res = lb.ref(
        "res",
        "¬ x = y → ( z = y → ∀ x z = y )",
        s1,
        s7,
        ref="syl5",
        note="syl5 equvinva, exlimdv",
    )

    return lb.build(res)


def prove_ax13lem2(sys: System) -> Proof:
    """ax13lem2: ¬ x = y → ( ∃ x z = y → z = y ).

    A version of ax13 with one distinct variable restriction dropped.
    (Contributed by Wolf Lammen, 8-Sep-2018.)
    """
    lb = ProofBuilder(sys, "ax13lem2")

    # ax13lem1: ¬ x = y → ( w = y → ∀ x w = y )
    s1 = lb.ref(
        "s1",
        "¬ x = y → ( w = y → ∀ x w = y )",
        ref="ax13lem1",
        note="ax13lem1",
    )

    # equeucl: z = y → ( w = y → z = w )
    s2 = lb.ref(
        "s2",
        "z = y → ( w = y → z = w )",
        ref="equeucl",
        note="equeucl",
    )

    # eximi with equeucl: ∃ x z = y → ∃ x ( w = y → z = w )
    s3 = lb.ref(
        "s3",
        "∃ x z = y → ∃ x ( w = y → z = w )",
        s2,
        ref="eximi",
        note="eximi equeucl",
    )

    # 19.36v: ∃ x ( w = y → z = w ) ↔ ( ∀ x w = y → z = w )
    s4 = lb.ref(
        "s4",
        "∃ x ( w = y → z = w ) ↔ ( ∀ x w = y → z = w )",
        ref="19.36v",
        note="19.36v",
    )

    # sylib: ∃ x z = y → ( ∀ x w = y → z = w )
    s5 = lb.ref(
        "s5",
        "∃ x z = y → ( ∀ x w = y → z = w )",
        s3,
        s4,
        ref="sylib",
        note="sylib 3,4",
    )

    # syl9: ¬ x = y → ( ∃ x z = y → ( w = y → z = w ) )
    s6 = lb.ref(
        "s6",
        "¬ x = y → ( ∃ x z = y → ( w = y → z = w ) )",
        s1,
        s5,
        ref="syl9",
        note="syl9 1,5",
    )

    # alrimdv: ¬ x = y → ( ∃ x z = y → ∀ w ( w = y → z = w ) )
    s7 = lb.ref(
        "s7",
        "¬ x = y → ( ∃ x z = y → ∀ w ( w = y → z = w ) )",
        s6,
        ref="alrimdv",
        note="alrimdv 6",
    )

    # equequ2: w = y → ( z = w ↔ z = y )
    s8 = lb.ref(
        "s8",
        "w = y → ( z = w ↔ z = y )",
        ref="equequ2",
        note="equequ2",
    )

    # equsalvw: ∀ w ( w = y → z = w ) ↔ z = y
    s9 = lb.ref(
        "s9",
        "∀ w ( w = y → z = w ) ↔ z = y",
        s8,
        ref="equsalvw",
        note="equsalvw 8",
    )

    # imbitrdi: ¬ x = y → ( ∃ x z = y → z = y )
    res = lb.ref(
        "res",
        "¬ x = y → ( ∃ x z = y → z = y )",
        s7,
        s9,
        ref="imbitrdi",
        note="imbitrdi 7,9",
    )

    return lb.build(res)


def prove_merlem13(sys: System) -> Proof:
    """merlem13: ( φ → ψ ) → ( ( ( θ → ( ¬ ¬ χ → χ ) ) → ¬ ¬ φ ) → ψ ).

    Thirteenth lemma towards deriving the Łukasiewicz axioms from Meredith's
    sole axiom.  (Contributed by NM, 14-Dec-2002.)
    """
    lb = ProofBuilder(sys, "merlem13")

    T = "( θ → ( ¬ ¬ χ → χ ) )"

    # Step 1: merlem12 with φ := ¬ ( T → ¬ ¬ φ )
    # ( ( ( θ → ( ¬ ¬ χ → χ ) ) → φ ) → φ )  [merlem12]
    # → ( ( T → ¬ ( T → ¬ ¬ φ ) ) → ¬ ( T → ¬ ¬ φ ) )
    s1 = lb.ref(
        "s1",
        f"( ( {T} → ¬ ( {T} → ¬ ¬ φ ) ) → ¬ ( {T} → ¬ ¬ φ ) )",
        ref="merlem12",
        note="merlem12",
    )

    # Step 2: merlem12 with φ := ¬ ¬ φ
    # → ( ( T → ¬ ¬ φ ) → ¬ ¬ φ )
    s2 = lb.ref(
        "s2",
        f"( ( {T} → ¬ ¬ φ ) → ¬ ¬ φ )",
        ref="merlem12",
        note="merlem12",
    )

    # Step 3: merlem5 with φ := ( T → ¬ ¬ φ ), ψ := ¬ ¬ φ
    # ( φ → ψ ) → ( ¬ ¬ φ → ψ )
    # → ( ( T → ¬ ¬ φ ) → ¬ ¬ φ ) → ( ¬ ¬ ( T → ¬ ¬ φ ) → ¬ ¬ φ )
    s3 = lb.ref(
        "s3",
        f"( ( ( {T} → ¬ ¬ φ ) → ¬ ¬ φ ) → ( ¬ ¬ ( {T} → ¬ ¬ φ ) → ¬ ¬ φ ) )",
        ref="merlem5",
        note="merlem5",
    )

    # Step 4: ax-mp(2, 3) → ¬ ¬ ( T → ¬ ¬ φ ) → ¬ ¬ φ
    s4 = lb.mp("s4", s2, s3, note="MP s2, s3")

    # Step 5: merlem6 with χ := s4, ψ := ( ¬ ( T → ¬ ¬ φ ) → ψ ), φ := ¬ ( T → ¬ ¬ φ ), θ := T
    # χ → ( ( ( ψ → χ ) → φ ) → ( θ → φ ) )
    s4_formula = f"( ¬ ¬ ( {T} → ¬ ¬ φ ) → ¬ ¬ φ )"
    psi_to_chi_formula = f"( ( ¬ ( {T} → ¬ ¬ φ ) → ψ ) → ( ¬ ¬ ( {T} → ¬ ¬ φ ) → ¬ ¬ φ ) )"
    neg_formula = f"¬ ( {T} → ¬ ¬ φ )"
    s5 = lb.ref(
        "s5",
        f"( {s4_formula} → ( ( {psi_to_chi_formula} → {neg_formula} ) → ( {T} → {neg_formula} ) ) )",
        ref="merlem6",
        note="merlem6",
    )

    # Step 6: ax-mp(4, 5) → ( ( ( ¬ ( T → ¬ ¬ φ ) → ψ ) → s4 ) → ¬ ( T → ¬ ¬ φ ) ) → ( T → ¬ ( T → ¬ ¬ φ ) )
    s6 = lb.mp("s6", s4, s5, note="MP s4, s5")

    # Step 7: meredith
    # ( ( ( ( φ → ψ ) → ( ¬ χ → ¬ θ ) ) → χ ) → τ ) → ( ( τ → φ ) → ( θ → φ ) )
    # φ = ¬ ( T → ¬ ¬ φ ), ψ = ψ, χ = ¬ ( T → ¬ ¬ φ ), θ = ¬ φ, τ = ( T → ¬ ( T → ¬ ¬ φ ) )
    s7 = lb.ref(
        "s7",
        f"( ( ( ( ¬ ( {T} → ¬ ¬ φ ) → ψ ) → ( ¬ ¬ ( {T} → ¬ ¬ φ ) → ¬ ¬ φ ) ) → ¬ ( {T} → ¬ ¬ φ ) ) → ( {T} → ¬ ( {T} → ¬ ¬ φ ) ) ) → ( ( ( {T} → ¬ ( {T} → ¬ ¬ φ ) ) → ¬ ( {T} → ¬ ¬ φ ) ) → ( ¬ φ → ¬ ( {T} → ¬ ¬ φ ) ) )",
        ref="meredith",
        note="meredith",
    )

    # Step 8: ax-mp(6, 7) → ( ( T → ¬ ( T → ¬ ¬ φ ) ) → ¬ ( T → ¬ ¬ φ ) ) → ( ¬ φ → ¬ ( T → ¬ ¬ φ ) )
    s8 = lb.mp("s8", s6, s7, note="MP s6, s7")

    # Step 9: ax-mp(1, 8) → ¬ φ → ¬ ( T → ¬ ¬ φ )
    s9 = lb.mp("s9", s1, s8, note="MP s1, s8")

    # Step 10: merlem6 with χ := s9, ψ := ( ψ → ψ ), φ := φ, θ := ( ( ψ → ψ ) → s9 )
    # χ → ( ( ( ψ → χ ) → φ ) → ( θ → φ ) )
    s9_formula = f"( ¬ φ → ¬ ( {T} → ¬ ¬ φ ) )"
    psipsi_to_s9 = f"( ( ψ → ψ ) → ( ¬ φ → ¬ ( {T} → ¬ ¬ φ ) ) )"
    s10 = lb.ref(
        "s10",
        f"( {s9_formula} → ( ( {psipsi_to_s9} → φ ) → ( ( {psipsi_to_s9} → φ ) → φ ) ) )",
        ref="merlem6",
        note="merlem6",
    )

    # Step 11: ax-mp(9, 10) → ( ( ( ψ → ψ ) → s9 ) → φ ) → ( ( ( ψ → ψ ) → s9 ) → φ )
    s11 = lb.mp("s11", s9, s10, note="MP s9, s10")

    # Step 12: merlem11 with φ := ( ( ψ → ψ ) → s9 ) → φ, ψ := φ
    # ( φ → ( φ → ψ ) ) → ( φ → ψ )
    s12 = lb.ref(
        "s12",
        f"( ( {psipsi_to_s9} → φ ) → ( ( {psipsi_to_s9} → φ ) → φ ) ) → ( ( {psipsi_to_s9} → φ ) → φ )",
        ref="merlem11",
        note="merlem11",
    )

    # Step 13: ax-mp(11, 12) → ( ( ( ψ → ψ ) → s9 ) → φ ) → φ
    s13 = lb.mp("s13", s11, s12, note="MP s11, s12")

    # Step 14: meredith
    # ( ( ( ( φ → ψ ) → ( ¬ χ → ¬ θ ) ) → χ ) → τ ) → ( ( τ → φ ) → ( θ → φ ) )
    # φ = ψ, ψ = ψ, χ = φ, θ = ( T → ¬ ¬ φ ), τ = φ
    s14 = lb.ref(
        "s14",
        f"( ( ( {psipsi_to_s9} → φ ) → φ ) → ( ( φ → ψ ) → ( ( {T} → ¬ ¬ φ ) → ψ ) ) )",
        ref="meredith",
        note="meredith",
    )

    # Step 15: ax-mp(13, 14) → ( φ → ψ ) → ( ( T → ¬ ¬ φ ) → ψ )
    res = lb.mp("res", s13, s14, note="MP s13, s14")

    return lb.build(res)


def prove_luklem2(sys: System) -> Proof:
    """luklem2: ( φ → ¬ ψ ) → ( ( ( φ → χ ) → θ ) → ( ψ → θ ) ).

    Used to rederive standard propositional axioms from Łukasiewicz'.
    (Contributed by NM, 22-Dec-2002.)
    """
    lb = ProofBuilder(sys, "luklem2")

    # s1: ψ → ( ¬ ψ → χ )    [luk-3]
    s1 = lb.ref("s1", "ψ → ( ¬ ψ → χ )", ref="luk-3", note="luk-3")

    # s2: ( φ → ¬ ψ ) → ( ( ¬ ψ → χ ) → ( φ → χ ) )    [luk-1]
    s2 = lb.ref(
        "s2",
        "( φ → ¬ ψ ) → ( ( ¬ ψ → χ ) → ( φ → χ ) )",
        ref="luk-1",
        note="luk-1",
    )

    # s3: ( ψ → ( ¬ ψ → χ ) ) → ( ( ( ¬ ψ → χ ) → ( φ → χ ) ) → ( ψ → ( φ → χ ) ) )
    s3 = lb.ref(
        "s3",
        "( ψ → ( ¬ ψ → χ ) ) → ( ( ( ¬ ψ → χ ) → ( φ → χ ) ) → ( ψ → ( φ → χ ) ) )",
        ref="luk-1",
        note="luk-1",
    )

    # s4: ( ( ¬ ψ → χ ) → ( φ → χ ) ) → ( ψ → ( φ → χ ) )    [MP s1, s3]
    s4 = lb.mp("s4", s1, s3, note="MP s1, s3")

    # s5: ( φ → ¬ ψ ) → ( ψ → ( φ → χ ) )    [luklem1 s2, s4]
    s5 = lb.ref(
        "s5",
        "( φ → ¬ ψ ) → ( ψ → ( φ → χ ) )",
        s2,
        s4,
        ref="luklem1",
        note="luklem1",
    )

    # s6: ( ψ → ( φ → χ ) ) → ( ( ( φ → χ ) → θ ) → ( ψ → θ ) )    [luk-1]
    s6 = lb.ref(
        "s6",
        "( ψ → ( φ → χ ) ) → ( ( ( φ → χ ) → θ ) → ( ψ → θ ) )",
        ref="luk-1",
        note="luk-1",
    )

    # res: ( φ → ¬ ψ ) → ( ( ( φ → χ ) → θ ) → ( ψ → θ ) )    [luklem1 s5, s6]
    res = lb.ref(
        "res",
        "( φ → ¬ ψ ) → ( ( ( φ → χ ) → θ ) → ( ψ → θ ) )",
        s5,
        s6,
        ref="luklem1",
        note="luklem1",
    )

    return lb.build(res)


def prove_luklem3(sys: System) -> Proof:
    """luklem3: φ → ( ( ( ¬ φ → ψ ) → χ ) → ( θ → χ ) ).

    Used to rederive standard propositional axioms from Łukasiewicz'.
    (Contributed by NM, 22-Dec-2002.)
    """
    lb = ProofBuilder(sys, "luklem3")

    # s1: φ → ( ¬ φ → ¬ θ )    [luk-3]
    s1 = lb.ref("s1", "φ → ( ¬ φ → ¬ θ )", ref="luk-3", note="luk-3")

    # s2: ( ¬ φ → ¬ θ ) → ( ( ( ¬ φ → ψ ) → χ ) → ( θ → χ ) )    [luklem2]
    s2 = lb.ref(
        "s2",
        "( ¬ φ → ¬ θ ) → ( ( ( ¬ φ → ψ ) → χ ) → ( θ → χ ) )",
        ref="luklem2",
        note="luklem2",
    )

    # res: φ → ( ( ( ¬ φ → ψ ) → χ ) → ( θ → χ ) )    [luklem1 s1, s2]
    res = lb.ref(
        "res",
        "φ → ( ( ( ¬ φ → ψ ) → χ ) → ( θ → χ ) )",
        s1,
        s2,
        ref="luklem1",
        note="luklem1",
    )

    return lb.build(res)


def prove_luklem4(sys: System) -> Proof:
    """luklem4: ( ( ( ( ¬ φ → φ ) → φ ) → ψ ) → ψ.

    Used to rederive standard propositional axioms from Łukasiewicz'.
    (Contributed by NM, 22-Dec-2002.)
    """
    lb = ProofBuilder(sys, "luklem4")

    # s1: ( ¬ ( ( ¬ φ → φ ) → φ ) → ( ( ¬ φ → φ ) → φ ) ) → ( ( ¬ φ → φ ) → φ )
    #     [luk-2 with φ:=(¬φ→φ)→φ]
    s1 = lb.ref(
        "s1",
        "( ¬ ( ( ¬ φ → φ ) → φ ) → ( ( ¬ φ → φ ) → φ ) ) → ( ( ¬ φ → φ ) → φ )",
        ref="luk-2",
        note="luk-2",
    )

    # s2: ( ¬ φ → φ ) → φ    [luk-2]
    s2 = lb.ref("s2", "( ¬ φ → φ ) → φ", ref="luk-2", note="luk-2")

    # s3: ( ( ¬ φ → φ ) → φ ) → ( ( ( ¬ ( ( ¬ φ → φ ) → φ ) → ( ( ¬ φ → φ ) → φ ) ) → ( ( ¬ φ → φ ) → φ ) ) → ( ¬ ψ → ( ( ¬ φ → φ ) → φ ) ) )
    #     [luklem3 with φ:=(¬φ→φ)→φ, ψ:=(¬φ→φ)→φ, χ:=(¬φ→φ)→φ, θ:=¬ψ]
    s3 = lb.ref(
        "s3",
        "( ( ¬ φ → φ ) → φ ) → ( ( ( ¬ ( ( ¬ φ → φ ) → φ ) → ( ( ¬ φ → φ ) → φ ) ) → ( ( ¬ φ → φ ) → φ ) ) → ( ¬ ψ → ( ( ¬ φ → φ ) → φ ) ) )",
        ref="luklem3",
        note="luklem3",
    )

    # s4: ( ( ¬ ( ( ¬ φ → φ ) → φ ) → ( ( ¬ φ → φ ) → φ ) ) → ( ( ¬ φ → φ ) → φ ) ) → ( ¬ ψ → ( ( ¬ φ → φ ) → φ ) )
    #     [MP s2, s3]
    s4 = lb.mp("s4", s2, s3, note="MP s2, s3")

    # s5: ( ¬ ψ → ( ( ¬ φ → φ ) → φ ) )    [MP s1, s4]
    s5 = lb.mp("s5", s1, s4, note="MP s1, s4")

    # s6: ( ¬ ψ → ( ( ¬ φ → φ ) → φ ) ) → ( ( ( ( ¬ φ → φ ) → φ ) → ψ ) → ( ¬ ψ → ψ ) )
    #     [luk-1 with φ:=¬ψ, ψ:=(¬φ→φ)→φ, χ:=ψ]
    s6 = lb.ref(
        "s6",
        "( ¬ ψ → ( ( ¬ φ → φ ) → φ ) ) → ( ( ( ( ¬ φ → φ ) → φ ) → ψ ) → ( ¬ ψ → ψ ) )",
        ref="luk-1",
        note="luk-1",
    )

    # s7: ( ( ( ¬ φ → φ ) → φ ) → ψ ) → ( ¬ ψ → ψ )    [MP s5, s6]
    s7 = lb.mp("s7", s5, s6, note="MP s5, s6")

    # s8: ( ¬ ψ → ψ ) → ψ    [luk-2 with φ:=ψ]
    s8 = lb.ref("s8", "( ¬ ψ → ψ ) → ψ", ref="luk-2", note="luk-2")

    # res: ( ( ( ( ¬ φ → φ ) → φ ) → ψ ) → ψ    [luklem1 s7, s8]
    res = lb.ref(
        "res",
        "( ( ( ( ¬ φ → φ ) → φ ) → ψ ) → ψ )",
        s7,
        s8,
        ref="luklem1",
        note="luklem1",
    )

    return lb.build(res)


def prove_ax3(sys: System) -> Proof:
    """ax3: ( ¬ φ → ¬ ψ ) → ( ψ → φ ).

    Standard propositional axiom derived from Lukasiewicz axioms.
    (Contributed by NM, 22-Dec-2002.)
    """
    lb = ProofBuilder(sys, "ax3")

    # s1: ( ¬ φ → ¬ ψ ) → ( ( ( ¬ φ → φ ) → φ ) → ( ψ → φ ) )    [luklem2]
    s1 = lb.ref(
        "s1",
        "( ¬ φ → ¬ ψ ) → ( ( ( ¬ φ → φ ) → φ ) → ( ψ → φ ) )",
        ref="luklem2",
        note="luklem2",
    )

    # s2: ( ( ( ( ¬ φ → φ ) → φ ) → ( ψ → φ ) ) → ( ψ → φ )    [luklem4]
    s2 = lb.ref(
        "s2",
        "( ( ( ( ¬ φ → φ ) → φ ) → ( ψ → φ ) ) → ( ψ → φ ) )",
        ref="luklem4",
        note="luklem4",
    )

    # res: ( ¬ φ → ¬ ψ ) → ( ψ → φ )    [luklem1 s1, s2]
    res = lb.ref(
        "res",
        "( ¬ φ → ¬ ψ ) → ( ψ → φ )",
        s1,
        s2,
        ref="luklem1",
        note="luklem1",
    )

    return lb.build(res)


# New migrations register here beside their implementation. The aggregate
# registry imports this mapping, avoiding another edit to global shim files.
MIGRATION_THEOREMS: Mapping[str, LemmaCtor] = {}
