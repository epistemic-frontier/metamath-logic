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

    s1 = lb.ref("s1", "( φ → ψ ) -> ( ¬ ψ → ¬ φ )", ref="con3", note="con3")

    s2 = lb.mp("s2", h1, s1, "MP h1, s1")

    s3 = lb.mp("s3", h2, s2, "MP h2, s2")

    return lb.build(s3)


# -----------------------------------------------------------------------------
# Migration Expansion (set.mm compatibility)
# -----------------------------------------------------------------------------

def prove_con1(sys: System) -> Proof:
    """
    con1: ( ¬ φ → ψ ) -> ( ¬ ψ → φ ).

    Contraposition.  Theorem *2.15 of [WhiteheadRussell] p. 102.  Its
         associated inference is ~ con1i .  (Contributed by NM, 29-Dec-1992.)
         (Proof shortened by Wolf Lammen, 12-Feb-2013.)

    """
    lb = ProofBuilder(sys, "con1")
    s1 = lb.ref("s1", "( ¬ φ → ψ ) -> ( ¬ φ → ψ )", ref="id", note="id")
    res = lb.ref("res", "( ( ¬ φ → ψ ) -> ( ¬ ψ → φ ) )", s1, ref="con1d", note="con1d")
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
    con2: ( φ → ¬ ψ ) -> ( ψ → ¬ φ ).

    Contraposition.  Theorem *2.03 of [WhiteheadRussell] p. 100.  (Contributed
         by NM, 29-Dec-1992.)  (Proof shortened by Wolf Lammen, 12-Feb-2013.)

    """
    lb = ProofBuilder(sys, "con2")
    s1 = lb.ref("s1", "( φ → ¬ ψ ) -> ( φ → ¬ ψ )", ref="id", note="id")
    res = lb.ref("res", "( ( φ → ¬ ψ ) -> ( ψ → ¬ φ ) )", s1, ref="con2d", note="con2d")
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
    con3: ( φ → ψ ) -> ( ¬ ψ → ¬ φ ).

    Contraposition.  Theorem *2.16 of [WhiteheadRussell] p. 103.  This was the
         fourth axiom of Frege, specifically Proposition 28 of [Frege1879] p. 43.
         Its associated inference is ~ con3i .  (Contributed by NM, 29-Dec-1992.)
         (Proof shortened by Wolf Lammen, 13-Feb-2013.)

    """
    lb = ProofBuilder(sys, "con3")
    s1 = lb.ref("s1", "( φ → ψ ) -> ( φ → ψ )", ref="id", note="id")
    res = lb.ref("res", "( ( φ → ψ ) -> ( ¬ ψ → ¬ φ ) )", s1, ref="con3d", note="con3d")
    return lb.build(res)

def prove_con4(sys: System) -> Proof:
    """
    con4: ( ¬ φ → ¬ ψ ) -> ( ψ → φ ).

    Alias for ~ ax-3 to be used instead of it for labeling consistency.  Its
         associated inference is ~ con4i and its associated deduction is ~ con4d .
         (Contributed by BJ, 24-Dec-2020.)

    """
    lb = ProofBuilder(sys, "con4")
    stmt = lb.ref("res", "( ¬ φ → ¬ ψ ) -> ( ψ → φ )", ref="A3", note="A3")
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
        "( ¬ ψ → ¬ χ ) -> ( χ → ψ )",
        ref="con4",
        note="con4",
    )
    s2 = lb.ref(
        "s2",
        "( ( ¬ ψ → ¬ χ ) -> ( χ → ψ ) ) -> ( φ -> ( ( ¬ ψ → ¬ χ ) -> ( χ → ψ ) ) )",
        ref="A1",
        note="A1",
    )
    s3 = lb.mp("s3", s1, s2, "MP s1, s2")
    s4 = lb.ref(
        "s4",
        "( φ -> ( ( ¬ ψ → ¬ χ ) -> ( χ → ψ ) ) ) -> ( ( φ -> ( ¬ ψ → ¬ χ ) ) -> ( φ -> ( χ → ψ ) ) )",
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
    s2 = lb.ref("s2", "( ¬ φ → ( φ → ψ ) ) -> ( φ → ( ¬ φ → ψ ) )", ref="com12", note="com12")
    res = lb.mp("res", s1, s2, "MP s1, s2")
    return lb.build(res)

def prove_conax1(sys: System) -> Proof:
    """
    conax1: ¬ ( φ → ψ ) → ¬ ψ.
    """
    lb = ProofBuilder(sys, "conax1")
    s1 = lb.ref("s1", "ψ → ( φ → ψ )", ref="A1", note="A1")
    s2 = lb.ref(
        "s2",
        "( ψ → ( φ → ψ ) ) -> ( ¬ ( φ → ψ ) -> ¬ ψ )",
        ref="con3",
        note="con3",
    )
    res = lb.mp("res", s1, s2, "MP s1, s2")
    return lb.build(res)

def prove_pm2_521g(sys: System) -> Proof:
    """
    pm2.521g: ¬ ( φ → ψ ) -> ( ψ → χ ).
    """
    lb = ProofBuilder(sys, "pm2.521g")
    h1 = lb.ref("h1", "¬ ( φ → ψ ) -> ¬ ψ", ref="conax1", note="conax1")
    res = lb.ref("res", "¬ ( φ → ψ ) -> ( ψ → χ )", h1, ref="pm2.21d", note="pm2.21d")
    return lb.build(res)

def prove_pm2_521(sys: System) -> Proof:
    """
    pm2.521: ¬ ( φ → ψ ) -> ( ψ → φ ).
    """
    lb = ProofBuilder(sys, "pm2.521")
    res = lb.ref("res", "¬ ( φ → ψ ) -> ( ψ → φ )", ref="pm2.521g", note="pm2.521g")
    return lb.build(res)

def prove_mt2(sys: System) -> Proof:
    """
    mt2: ¬ φ. Hyp1: ψ, Hyp2: φ → ¬ ψ.

    A rule similar to modus tollens.  Inference associated with ~ con2i .
           (Contributed by NM, 19-Aug-1993.)  (Proof shortened by Wolf Lammen,
           10-Sep-2013.)

    """
    lb = ProofBuilder(sys, "mt2")
    lb.hyp("hyp1", "ψ")
    lb.hyp("hyp2", "φ → ¬ ψ")
    stmt = lb.raw("res", "¬ φ", note="Imported")
    return lb.build(stmt)

def prove_mt3(sys: System) -> Proof:
    """
    mt3: φ. Hyp1: ¬ ψ, Hyp2: ¬ φ → ψ.

    A rule similar to modus tollens.  Inference associated with ~ con1i .
           (Contributed by NM, 18-May-1994.)  (Proof shortened by Wolf Lammen,
           11-Sep-2013.)

    """
    lb = ProofBuilder(sys, "mt3")
    lb.hyp("hyp1", "¬ ψ")
    lb.hyp("hyp2", "¬ φ → ψ")
    stmt = lb.raw("res", "φ", note="Imported")
    return lb.build(stmt)

def prove_nsyl(sys: System) -> Proof:
    """
    nsyl: φ → ¬ χ. Hyp1: φ → ¬ ψ, Hyp2: χ → ψ.

    A negated syllogism inference.  (Contributed by NM, 31-Dec-1993.)
           (Proof shortened by Wolf Lammen, 2-Mar-2013.)

    """
    lb = ProofBuilder(sys, "nsyl")
    lb.hyp("hyp1", "φ → ¬ ψ")
    lb.hyp("hyp2", "χ → ψ")
    stmt = lb.raw("res", "φ → ¬ χ", note="Imported")
    return lb.build(stmt)

def prove_nsyl2(sys: System) -> Proof:
    """
    nsyl2: φ → χ. Hyp1: φ → ¬ ψ, Hyp2: ¬ χ → ψ.

    A negated syllogism inference.  (Contributed by NM, 26-Jun-1994.)
           (Proof shortened by Wolf Lammen, 14-Nov-2023.)

    """
    lb = ProofBuilder(sys, "nsyl2")
    lb.hyp("hyp1", "φ → ¬ ψ")
    lb.hyp("hyp2", "¬ χ → ψ")
    stmt = lb.raw("res", "φ → χ", note="Imported")
    return lb.build(stmt)

def prove_nsyl3(sys: System) -> Proof:
    """
    nsyl3: χ → ¬ φ. Hyp1: φ → ¬ ψ, Hyp2: χ → ψ.

    A negated syllogism inference.  (Contributed by NM, 1-Dec-1995.)

    """
    lb = ProofBuilder(sys, "nsyl3")
    lb.hyp("hyp1", "φ → ¬ ψ")
    lb.hyp("hyp2", "χ → ψ")
    stmt = lb.raw("res", "χ → ¬ φ", note="Imported")
    return lb.build(stmt)

def prove_pm2_61(sys: System) -> Proof:
    """
    pm2.61: ( φ → ψ ) -> ( ( ¬ φ → ψ ) -> ψ ).

    Theorem *2.61 of [WhiteheadRussell] p. 107.  Useful for eliminating an
         antecedent.  (Contributed by NM, 4-Jan-1993.)  (Proof shortened by Wolf
         Lammen, 22-Sep-2013.)

    """
    lb = ProofBuilder(sys, "pm2.61")
    stmt = lb.raw("res", "( φ → ψ ) -> ( ( ¬ φ → ψ ) -> ψ )", note="Imported")
    return lb.build(stmt)

def prove_pm2_65(sys: System) -> Proof:
    """
    pm2.65: ( φ → ψ ) -> ( ( φ → ¬ ψ ) -> ¬ φ ).

    Theorem *2.65 of [WhiteheadRussell] p. 107.  Proof by contradiction.
         (Contributed by NM, 21-Jun-1993.)  (Proof shortened by Wolf Lammen,
         8-Mar-2013.)

    """
    lb = ProofBuilder(sys, "pm2.65")
    stmt = lb.raw("res", "( φ → ψ ) -> ( ( φ → ¬ ψ ) -> ¬ φ )", note="Imported")
    return lb.build(stmt)

def prove_con1i(sys: System) -> Proof:
    """
    con1i: ¬ ψ → φ. Hyp: ¬ φ → ψ.

    A contraposition inference.  Inference associated with ~ con1 .  Its
           associated inference is ~ mt3 .  (Contributed by NM, 3-Jan-1993.)
           (Proof shortened by Mel L. O'Cat, 28-Nov-2008.)  (Proof shortened by
           Wolf Lammen, 19-Jun-2013.)

    """
    lb = ProofBuilder(sys, "con1i")
    hyp = lb.hyp("hyp", "¬ φ → ψ")
    s1 = lb.ref("s1", "( ¬ φ → ψ ) -> ( ¬ ψ → φ )", ref="con1", note="con1")
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
    hyp = lb.hyp("hyp", "φ → ¬ ψ")
    s1 = lb.ref("s1", "( φ → ¬ ψ ) -> ( ψ → ¬ φ )", ref="con2", note="con2")
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
    hyp = lb.hyp("hyp", "φ → ψ")
    s1 = lb.ref("s1", "( φ → ψ ) -> ( ¬ ψ → ¬ φ )", ref="con3", note="con3")
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
    hyp = lb.hyp("hyp", "¬ φ → ¬ ψ")
    s1 = lb.ref("s1", "( ¬ φ → ¬ ψ ) -> ( ψ → φ )", ref="con4", note="con4")
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

