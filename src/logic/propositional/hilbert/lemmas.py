# logic/propositional/hilbert/lemmas.py
"""Classic propositional lemmas for a Hilbert-style system.

This module collects derived lemmas over implication, negation and the
derived disjunction `Or`. Each `prove_*` function constructs a `Proof`
value that records the statement and a debug-friendly sequence of steps.

Families covered here include identity, disjunction introduction, contraposition,
double negation, and related classical equivalences.
"""

from __future__ import annotations

from skfd.authoring.formula import render
from skfd.proof import Proof, ProofBuilder, Step

from . import System


# -----------------------------------------------------------------------------
# Lemma proofs
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


def prove_notnotr(sys: System) -> Proof:
    """
    notnotr: ¬¬φ → φ.

    Double negation elimination.
    """
    lb = ProofBuilder(sys, "notnotr")
    s1 = lb.ref("s1", "( ¬ φ → φ ) -> φ", ref="pm2.18", note="pm2.18")
    res = lb.ref("res", "¬ ¬ φ → φ", s1, ref="jarli", note="jarli")
    return lb.build(res)


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


def prove_simplim(sys: System) -> Proof:
    """
    simplim: ¬ ( φ → ψ ) -> φ.

    Simplification theorem.
    """
    lb = ProofBuilder(sys, "simplim")
    s1 = lb.ref("s1", "¬ φ → ( φ → ψ )", ref="pm2.21", note="pm2.21")
    s2 = lb.ref("s2", "( ¬ φ → ( φ → ψ ) ) -> ( ¬ ( φ → ψ ) -> φ )", ref="con1i", note="con1i")
    res = lb.mp("res", s1, s2, "MP s1, s2")
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


def prove_a1i(sys: System) -> Proof:
    """
    a1i: φ → (ψ → φ).

    Hyp: φ
    Concl: ψ → φ

    Inference introducing an antecedent.  Inference associated with ~ ax-1 .
           Its associated inference is ~ a1ii .  See ~ conventions for a definition
           of "associated inference".  (Contributed by NM, 29-Dec-1992.)

    """
    lb = ProofBuilder(sys, "a1i")
    hyp = lb.hyp("a1i.1", "φ")
    a1 = lb.ref("s1", "φ → ( ψ → φ )", ref="A1", note="A1")
    res = lb.mp("s2", hyp, a1, "MP a1i.1, s1")
    return lb.build(res)


def prove_a2i(sys: System) -> Proof:
    """
    a2i: (φ → ψ) -> (φ → χ).

    Hyp: φ → (ψ → χ)
    Concl: (φ → ψ) -> (φ → χ)

    Inference distributing an antecedent.  Inference associated with
           ~ ax-2 .  Its associated inference is ~ mpd .  (Contributed by NM,
           29-Dec-1992.)

    """
    lb = ProofBuilder(sys, "a2i")
    hyp = lb.hyp("a2i.1", "φ → ( ψ → χ )")
    a2 = lb.ref("s1", "( φ → ( ψ → χ ) ) -> ( ( φ → ψ ) -> ( φ → χ ) )", ref="A2", note="A2")
    res = lb.mp("s2", hyp, a2, "MP a2i.1, s1")
    return lb.build(res)


def prove_mpd(sys: System) -> Proof:
    """
    mpd: φ → χ.

    Hyp 1: φ → ψ
    Hyp 2: φ → (ψ → χ)
    Concl: φ → χ

    A modus ponens deduction.  A translation of natural deduction rule
           ` → ` E ( ` → ` elimination), see ~ natded .  Deduction form of
           ~ ax-mp .  Inference associated with ~ a2i .  Commuted form of ~ mpcom .
           (Contributed by NM, 29-Dec-1992.)

    """
    lb = ProofBuilder(sys, "mpd")
    h1 = lb.hyp("mpd.1", "φ → ψ")
    h2 = lb.hyp("mpd.2", "φ → ( ψ → χ )")
    a2 = lb.ref("s1", "( φ → ( ψ → χ ) ) -> ( ( φ → ψ ) -> ( φ → χ ) )", ref="A2", note="A2")
    s2 = lb.mp("s2", h2, a2, "MP mpd.2, s1")
    s3 = lb.mp("s3", h1, s2, "MP mpd.1, s2")
    return lb.build(s3)


def prove_syl(sys: System) -> Proof:
    """
    syl: φ → χ.

    Hyp 1: φ → ψ
    Hyp 2: ψ → χ
    Concl: φ → χ

    An inference version of the transitive laws for implication ~ imim2 and
           ~ imim1 (and ~ imim1i and ~ imim2i ), which Russell and Whitehead call
           "the principle of the syllogism ... because ... the syllogism in Barbara
           is derived from [[ ~ syl ]" (quote after Theorem *2.06 of
           [WhiteheadRussell] p. 101).  Some authors call this law a "hypothetical
           syllogism".  Its associated inference is ~ mp2b .

           (A bit of trivia: this is the most commonly referenced assertion in our
           database (13449 times as of 22-Jul-2021).  In second place is ~ eqid
           (9597 times), followed by ~ adantr (8861 times), ~ syl2anc (7421 times),
           ~ adantl (6403 times), and ~ simpr (5829 times).  The Metamath program
           command 'show usage' shows the number of references.)

           (Contributed by NM, 30-Sep-1992.)  (Proof shortened by Mel L. O'Cat,
           20-Oct-2011.)  (Proof shortened by Wolf Lammen, 26-Jul-2012.)

    """
    lb = ProofBuilder(sys, "syl")
    h1 = lb.hyp("syl.1", "φ → ψ")
    h2 = lb.hyp("syl.2", "ψ → χ")
    a1 = lb.ref("s1", "( ψ → χ ) -> ( φ → ( ψ → χ ) )", ref="A1", note="A1")
    s2 = lb.mp("s2", h2, a1, "MP syl.2, s1")
    a2 = lb.ref("s3", "( φ → ( ψ → χ ) ) -> ( ( φ → ψ ) -> ( φ → χ ) )", ref="A2", note="A2")
    s4 = lb.mp("s4", s2, a2, "MP s2, s3")
    s5 = lb.mp("s5", h1, s4, "MP syl.1, s4")
    return lb.build(s5)


def prove_sylcom(sys: System) -> Proof:
    """
    sylcom: φ → (ψ → θ).

    Hyp 1: φ → (ψ → χ)
    Hyp 2: ψ → (χ → θ)
    Concl: φ → (ψ → θ)

    Syllogism inference with commutation of antecedents.  (Contributed by
           NM, 29-Aug-2004.)  (Proof shortened by Mel L. O'Cat, 2-Feb-2006.)
           (Proof shortened by Stefan Allan, 23-Feb-2006.)

    """
    lb = ProofBuilder(sys, "sylcom")

    hyp1_wff = lb.hyp("sylcom.1", "φ → ( ψ → χ )")
    hyp2_wff = lb.hyp("sylcom.2", "ψ → ( χ → θ )")

    s1 = lb.ref(
        "s1",
        "( ψ → ( χ → θ ) ) -> ( ( ψ → χ ) -> ( ψ → θ ) )",
        ref="A2",
        note="A2(ψ,χ,θ)",
    )
    s2 = lb.mp("s2", hyp2_wff, s1, "(ψ→χ)→(ψ→θ)")

    s3 = lb.ref(
        "s3",
        "( ( ψ → χ ) -> ( ψ → θ ) ) -> ( φ → ( ( ψ → χ ) -> ( ψ → θ ) ) )",
        ref="A1",
        note="A1 lift",
    )
    s4 = lb.mp("s4", s2, s3, "φ→((ψ→χ)→(ψ→θ))")

    s5 = lb.ref(
        "s5",
        "( φ → ( ( ψ → χ ) -> ( ψ → θ ) ) ) -> ( ( φ → ( ψ → χ ) ) -> ( φ → ( ψ → θ ) ) )",
        ref="A2",
        note="A2 special",
    )
    s6 = lb.mp("s6", s4, s5, "(φ→(ψ→χ))→(φ→(ψ→θ))")

    s7 = lb.mp("s7", hyp1_wff, s6, "φ→(ψ→θ)")

    return lb.build(s7)


def prove_com12(sys: System) -> Proof:
    """
    com12: ψ → (φ → χ).

    Hyp: φ → (ψ → χ)
    Concl: ψ → (φ → χ)

    Inference that swaps (commutes) antecedents in an implication.
           Inference associated with ~ pm2.04 .  Its associated inference is
           ~ mpi .  (Contributed by NM, 29-Dec-1992.)  (Proof shortened by Wolf
           Lammen, 4-Aug-2012.)

    """
    lb = ProofBuilder(sys, "com12")

    hyp_wff = lb.hyp("com12.1", "φ → ( ψ → χ )")

    s1 = lb.ref("s1", "ψ → ( φ → ψ )", ref="A1", note="A1 ψ→(φ→ψ)")
    s2 = lb.ref(
        "s2",
        "( φ → ( ψ → χ ) ) -> ( ( φ → ψ ) -> ( φ → χ ) )",
        ref="A2",
        note="A2 (φ,(ψ→χ))",
    )

    s3 = lb.mp("s3", hyp_wff, s2, "(φ→ψ)→(φ→χ)")

    s4 = lb.ref(
        "s4",
        "( ( φ → ψ ) -> ( φ → χ ) ) -> ( ψ → ( ( φ → ψ ) -> ( φ → χ ) ) )",
        ref="A1",
        note="A1 lift",
    )
    s5 = lb.mp("s5", s3, s4, "ψ→((φ→ψ)→(φ→χ))")

    s6 = lb.ref(
        "s6",
        "( ψ → ( ( φ → ψ ) -> ( φ → χ ) ) ) -> ( ( ψ → ( φ → ψ ) ) -> ( ψ → ( φ → χ ) ) )",
        ref="A2",
        note="A2(ψ,...)",
    )
    s7 = lb.mp("s7", s5, s6, "(ψ→(φ→ψ))→(ψ→(φ→χ))")

    s8 = lb.mp("s8", s1, s7, "ψ→(φ→χ)")

    return lb.build(s8)


def prove_syl5(sys: System) -> Proof:
    """
    syl5: χ → (φ → θ).

    A syllogism rule of inference.  The first premise is used to replace the
           second antecedent of the second premise.  (Contributed by NM,
           27-Dec-1992.)  (Proof shortened by Wolf Lammen, 25-May-2013.)

    """
    lb = ProofBuilder(sys, "syl5")
    h1 = lb.hyp("syl5.1", "φ → ψ")
    h2 = lb.hyp("syl5.2", "χ → ( ψ → θ )")

    s1 = lb.ref(
        "s1",
        "( χ → ( ψ → θ ) ) -> ( φ → ( χ → ( ψ → θ ) ) )",
        ref="A1",
        note="A1",
    )
    s2 = lb.mp("s2", h2, s1, "MP syl5.2, s1")
    s3 = lb.ref("s3", "χ → ( φ → ( ψ → θ ) )", s2, ref="com12", note="com12")

    s5 = lb.ref(
        "s5",
        "( φ → ( ψ → θ ) ) -> ( ( φ → ψ ) -> ( φ → θ ) )",
        ref="A2",
        note="A2",
    )
    s6 = lb.ref(
        "s6",
        "( ( φ → ( ψ → θ ) ) -> ( ( φ → ψ ) -> ( φ → θ ) ) ) -> ( χ -> ( ( φ → ( ψ → θ ) ) -> ( ( φ → ψ ) -> ( φ → θ ) ) ) )",
        ref="A1",
        note="A1",
    )
    s7 = lb.mp("s7", s5, s6, "MP s5, s6")
    s8 = lb.ref(
        "s8",
        "( χ -> ( ( φ → ( ψ → θ ) ) -> ( ( φ → ψ ) -> ( φ → θ ) ) ) ) -> ( ( χ -> ( φ → ( ψ → θ ) ) ) -> ( χ -> ( ( φ → ψ ) -> ( φ → θ ) ) ) )",
        ref="A2",
        note="A2",
    )
    s9 = lb.mp("s9", s7, s8, "MP s7, s8")
    s10 = lb.mp("s10", s3, s9, "MP s3, s9")

    s11 = lb.ref(
        "s11",
        "( φ → ψ ) -> ( χ -> ( φ → ψ ) )",
        ref="A1",
        note="A1",
    )
    s12 = lb.mp("s12", h1, s11, "MP syl5.1, s11")
    s13 = lb.ref(
        "s13",
        "( χ -> ( ( φ → ψ ) -> ( φ → θ ) ) ) -> ( ( χ -> ( φ → ψ ) ) -> ( χ -> ( φ → θ ) ) )",
        ref="A2",
        note="A2",
    )
    s14 = lb.mp("s14", s10, s13, "MP s10, s13")
    res = lb.mp("res", s12, s14, "MP s12, s14")
    return lb.build(res)


def prove_syl6(sys: System) -> Proof:
    """
    syl6: φ → (ψ → θ).

    Hyp 1: φ → (ψ → χ)
    Hyp 2: χ → θ
    Concl: φ → (ψ → θ)

    A syllogism rule of inference.  The second premise is used to replace
           the consequent of the first premise.  (Contributed by NM, 5-Jan-1993.)
           (Proof shortened by Wolf Lammen, 30-Jul-2012.)

    """
    lb = ProofBuilder(sys, "syl6")

    h1 = lb.hyp("syl6.1", "φ → ( ψ → χ )")
    h2 = lb.hyp("syl6.2", "χ → θ")

    lb.ref(
        "s1",
        "ψ → ( χ → ψ )",
        ref="A1",
        note="A1",
    )
    s2 = lb.ref(
        "s2",
        "( χ → θ ) -> ( ψ → ( χ → θ ) )",
        ref="A1",
        note="A1",
    )
    s3 = lb.ref(
        "s3",
        "( ψ → ( χ → θ ) ) -> ( ( ψ → χ ) -> ( ψ → θ ) )",
        ref="A2",
        note="A2",
    )
    s4 = lb.mp("s4", h2, s2, "MP syl6.2, s2")
    s5 = lb.mp("s5", s4, s3, "MP s4, s3")

    s6 = lb.ref(
        "s6",
        "( ( ψ → χ ) -> ( ψ → θ ) ) -> ( φ → ( ( ψ → χ ) -> ( ψ → θ ) ) )",
        ref="A1",
        note="A1",
    )
    s7 = lb.mp("s7", s5, s6, "MP s5, s6")
    s8 = lb.ref(
        "s8",
        "( φ → ( ( ψ → χ ) -> ( ψ → θ ) ) ) -> ( ( φ → ( ψ → χ ) ) -> ( φ → ( ψ → θ ) ) )",
        ref="A2",
        note="A2",
    )
    s9 = lb.mp("s9", s7, s8, "MP s7, s8")
    res = lb.mp("res", h1, s9, "MP syl6.1, s9")

    return lb.build(res)


def prove_a1d(sys: System) -> Proof:
    """
    a1d: φ → (χ → ψ).

    Hyp: φ → ψ
    Concl: φ → (χ → ψ)

    Deduction introducing an embedded antecedent.  Deduction form of ~ ax-1
           and ~ a1i .  (Contributed by NM, 5-Jan-1993.)  (Proof shortened by
           Stefan Allan, 20-Mar-2006.)

    """
    lb = ProofBuilder(sys, "a1d")

    hyp_wff = lb.hyp("a1d.1", "φ → ψ")

    s1 = lb.ref("s1", "ψ → ( χ → ψ )", ref="A1", note="A1")

    s2 = lb.ref(
        "s2",
        "( ψ → ( χ → ψ ) ) -> ( φ → ( ψ → ( χ → ψ ) ) )",
        ref="A1",
        note="A1 (syl)",
    )
    s3 = lb.mp("s3", s1, s2, "MP s1, s2")

    s4 = lb.ref(
        "s4",
        "( φ → ( ψ → ( χ → ψ ) ) ) -> ( ( φ → ψ ) -> ( φ → ( χ → ψ ) ) )",
        ref="A2",
        note="A2 (syl)",
    )
    s5 = lb.mp("s5", s3, s4, "MP s3, s4")

    s6 = lb.mp("s6", hyp_wff, s5, "MP hyp, s5")

    return lb.build(s6)


# -----------------------------------------------------------------------------
# Expanded lemmas
# -----------------------------------------------------------------------------


def prove_idd(sys: System) -> Proof:
    """
    idd: φ → (ψ → ψ).

    Principle of identity ~ id with antecedent.  (Contributed by NM,
         26-Nov-1995.)

    """
    lb = ProofBuilder(sys, "idd")
    stmt = lb.raw("res", "φ → ( ψ → ψ )", note="Imported")
    return lb.build(stmt)


def prove_a1i13(sys: System) -> Proof:
    """
    a1i13: φ → (ψ → (χ → θ)). Hyp: ψ → θ.

    Add two antecedents to a wff.  (Contributed by Jeff Hankins,
           4-Aug-2009.)

    """
    lb = ProofBuilder(sys, "a1i13")
    lb.hyp("hyp", "ψ → θ")
    stmt = lb.raw("res", "φ → ( ψ → ( χ → θ ) )", note="Imported")
    return lb.build(stmt)


def prove_2a1d(sys: System) -> Proof:
    """
    2a1d: φ → (χ → (θ → ψ)). Hyp: φ → ψ.

    Deduction introducing two antecedents.  Two applications of ~ a1d .
           Deduction associated with ~ 2a1 and ~ 2a1i .  (Contributed by BJ,
           10-Aug-2020.)

    """
    lb = ProofBuilder(sys, "2a1d")
    lb.hyp("hyp", "φ → ψ")
    stmt = lb.raw("res", "φ → ( χ → ( θ → ψ ) )", note="Imported")
    return lb.build(stmt)


def prove_2a1(sys: System) -> Proof:
    """
    2a1: φ → (ψ → (χ → φ)).

    A double form of ~ ax-1 .  Its associated inference is ~ 2a1i .  Its
         associated deduction is ~ 2a1d .  (Contributed by BJ, 10-Aug-2020.)
         (Proof shortened by Wolf Lammen, 1-Sep-2020.)

    """
    lb = ProofBuilder(sys, "2a1")
    stmt = lb.raw("res", "φ → ( ψ → ( χ → φ ) )", note="Imported")
    return lb.build(stmt)


def prove_a2d(sys: System) -> Proof:
    """
    a2d: φ → ((ψ → χ) -> (ψ → θ)). Hyp: φ → (ψ → (χ → θ)).

    Deduction distributing an embedded antecedent.  Deduction form of
           ~ ax-2 .  (Contributed by NM, 23-Jun-1994.)

    """
    lb = ProofBuilder(sys, "a2d")
    h1 = lb.hyp("hyp", "φ → ( ψ → ( χ → θ ) )")

    s1 = lb.ref(
        "s1",
        "( ψ → ( χ → θ ) ) -> ( ( ψ → χ ) -> ( ψ → θ ) )",
        ref="A2",
        note="A2",
    )
    s2 = lb.ref(
        "s2",
        "( ( ψ → ( χ → θ ) ) -> ( ( ψ → χ ) -> ( ψ → θ ) ) ) -> ( φ → ( ( ψ → ( χ → θ ) ) -> ( ( ψ → χ ) -> ( ψ → θ ) ) ) )",
        ref="A1",
        note="A1",
    )
    s3 = lb.mp("s3", s1, s2, "MP s1, s2")
    s4 = lb.ref(
        "s4",
        "( φ → ( ( ψ → ( χ → θ ) ) -> ( ( ψ → χ ) -> ( ψ → θ ) ) ) ) -> ( ( φ → ( ψ → ( χ → θ ) ) ) -> ( φ → ( ( ψ → χ ) -> ( ψ → θ ) ) ) )",
        ref="A2",
        note="A2",
    )
    s5 = lb.mp("s5", s3, s4, "MP s3, s4")
    res = lb.mp("res", h1, s5, "MP hyp, s5")
    return lb.build(res)


def prove_syl5com(sys: System) -> Proof:
    """
    syl5com: φ → (χ → θ). Hyp1: φ → ψ, Hyp2: χ → (ψ → θ).

    Syllogism inference with commuted antecedents.  (Contributed by NM,
           24-May-2005.)

    """
    lb = ProofBuilder(sys, "syl5com")
    h1 = lb.hyp("hyp1", "φ → ψ")
    h2 = lb.hyp("hyp2", "χ → ( ψ → θ )")

    s1 = lb.ref(
        "s1",
        "( ψ → θ ) -> ( φ → ( ψ → θ ) )",
        ref="A1",
        note="A1",
    )
    s2 = lb.mp("s2", h2, s1, "MP hyp2, s1")
    s3 = lb.ref(
        "s3",
        "( φ → ( ψ → θ ) ) -> ( ( φ → ψ ) -> ( φ → θ ) )",
        ref="A2",
        note="A2",
    )
    s4 = lb.mp("s4", s2, s3, "MP s2, s3")
    res = lb.mp("res", h1, s4, "MP hyp1, s4")
    return lb.build(res)


def prove_syl11(sys: System) -> Proof:
    """
    syl11: ψ → (θ → χ). Hyp1: φ → (ψ → χ), Hyp2: θ → φ.

    A syllogism inference.  Commuted form of an instance of ~ syl .
           (Contributed by BJ, 25-Oct-2021.)

    """
    lb = ProofBuilder(sys, "syl11")
    lb.hyp("hyp1", "φ → ( ψ → χ )")
    lb.hyp("hyp2", "θ → φ")
    stmt = lb.raw("res", "ψ → ( θ → χ )", note="Imported")
    return lb.build(stmt)


def prove_syl56(sys: System) -> Proof:
    """
    syl56: χ → (φ → ta). Hyp1: φ → ψ, Hyp2: χ → (ψ → θ), Hyp3: θ → ta.

    Combine ~ syl5 and ~ syl6 .  (Contributed by NM, 14-Nov-2013.)

    """
    lb = ProofBuilder(sys, "syl56")
    lb.hyp("hyp1", "φ → ψ")
    lb.hyp("hyp2", "χ → ( ψ → θ )")
    lb.hyp("hyp3", "θ → τ")
    stmt = lb.raw("res", "χ → ( φ → τ )", note="Imported")
    return lb.build(stmt)


def prove_syl6com(sys: System) -> Proof:
    """
    syl6com: ψ → (φ → θ). Hyp1: φ → (ψ → χ), Hyp2: χ → θ.

    Syllogism inference with commuted antecedents.  (Contributed by NM,
           25-May-2005.)

    """
    lb = ProofBuilder(sys, "syl6com")
    lb.hyp("hyp1", "φ → ( ψ → χ )")
    lb.hyp("hyp2", "χ → θ")
    stmt = lb.raw("res", "ψ → ( φ → θ )", note="Imported")
    return lb.build(stmt)


def prove_mpcom(sys: System) -> Proof:
    """
    mpcom: ψ → χ. Hyp1: ψ → φ, Hyp2: φ → (ψ → χ).

    Modus ponens inference with commutation of antecedents.  Commuted form
           of ~ mpd .  (Contributed by NM, 17-Mar-1996.)

    """
    lb = ProofBuilder(sys, "mpcom")
    lb.hyp("hyp1", "ψ → φ")
    lb.hyp("hyp2", "φ → ( ψ → χ )")
    stmt = lb.raw("res", "ψ → χ", note="Imported")
    return lb.build(stmt)


def prove_syli(sys: System) -> Proof:
    """
    syli: ψ → (φ → θ). Hyp1: ψ → (φ → χ), Hyp2: χ → (φ → θ).

    Syllogism inference with common nested antecedent.  (Contributed by NM,
           4-Nov-2004.)

    """
    lb = ProofBuilder(sys, "syli")
    lb.hyp("hyp1", "ψ → ( φ → χ )")
    lb.hyp("hyp2", "χ → ( φ → θ )")
    stmt = lb.raw("res", "ψ → ( φ → θ )", note="Imported")
    return lb.build(stmt)


def prove_syl2im(sys: System) -> Proof:
    """
    syl2im: φ → (χ → τ). Hyp1: φ → ψ, Hyp2: χ → θ, Hyp3: ψ → (θ → τ).

    Replace two antecedents.  Implication-only version of ~ syl2an .
           (Contributed by Wolf Lammen, 14-May-2013.)

    """
    lb = ProofBuilder(sys, "syl2im")
    lb.hyp("hyp1", "φ → ψ")
    lb.hyp("hyp2", "χ → θ")
    lb.hyp("hyp3", "ψ → ( θ → τ )")
    stmt = lb.raw("res", "φ → ( χ → τ )", note="Imported")
    return lb.build(stmt)


def prove_syl2imc(sys: System) -> Proof:
    """
    syl2imc: χ → (φ → ta). Hyp1: φ → ψ, Hyp2: χ → θ, Hyp3: ψ → (θ → τ).

    A commuted version of ~ syl2im .  Implication-only version of
           ~ syl2anr .  (Contributed by BJ, 20-Oct-2021.)

    """
    lb = ProofBuilder(sys, "syl2imc")
    lb.hyp("hyp1", "φ → ψ")
    lb.hyp("hyp2", "χ → θ")
    lb.hyp("hyp3", "ψ → ( θ → τ )")
    stmt = lb.raw("res", "χ → ( φ → τ )", note="Imported")
    return lb.build(stmt)


def prove_pm2_27(sys: System) -> Proof:
    """
    pm2.27: φ → ((φ → ψ) -> ψ).

    This theorem, sometimes called "Assertion" or "Pon" (for "ponens"), can be
         thought of as a closed form of modus ponens ~ ax-mp .  Theorem *2.27 of
         [WhiteheadRussell] p. 104.  (Contributed by NM, 15-Jul-1993.)

    """
    lb = ProofBuilder(sys, "pm2.27")
    stmt = lb.raw("res", "φ → ( ( φ → ψ ) -> ψ )", note="Imported")
    return lb.build(stmt)


def prove_mpdd(sys: System) -> Proof:
    """
    mpdd: φ → (ψ → θ). Hyp1: φ → (ψ → χ), Hyp2: φ → (ψ → (χ → θ)).

    A nested modus ponens deduction.  Double deduction associated with
           ~ ax-mp .  Deduction associated with ~ mpd .  (Contributed by NM,
           12-Dec-2004.)

    """
    lb = ProofBuilder(sys, "mpdd")
    lb.hyp("hyp1", "φ → ( ψ → χ )")
    lb.hyp("hyp2", "φ → ( ψ → ( χ → θ ) )")
    stmt = lb.raw("res", "φ → ( ψ → θ )", note="Imported")
    return lb.build(stmt)


def prove_mpid(sys: System) -> Proof:
    """
    mpid: φ → (ψ → θ). Hyp1: φ → χ, Hyp2: φ → (ψ → (χ → θ)).

    A nested modus ponens deduction.  Deduction associated with ~ mpi .
           (Contributed by NM, 14-Dec-2004.)

    """
    lb = ProofBuilder(sys, "mpid")
    lb.hyp("hyp1", "φ → χ")
    lb.hyp("hyp2", "φ → ( ψ → ( χ → θ ) )")
    stmt = lb.raw("res", "φ → ( ψ → θ )", note="Imported")
    return lb.build(stmt)


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


def prove_id(sys: System) -> Proof:
    lb = ProofBuilder(sys, "id")

    s1 = lb.ref("s1", "φ → ( φ → φ )", ref="A1", note="A1")
    s2 = lb.ref(
        "s2",
        "( φ → ( ( φ → φ ) -> φ ) ) -> ( ( φ → ( φ → φ ) ) -> ( φ → φ ) )",
        ref="A2",
        note="A2",
    )
    s3 = lb.ref("s3", "φ → ( ( φ → φ ) -> φ )", ref="A1", note="A1")
    s4 = lb.mp("s4", s3, s2, "MP s3, s2")
    res = lb.mp("res", s1, s4, "MP s1, s4")
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


def prove_pm2_43(sys: System) -> Proof:
    """
    pm2.43: ( φ → ( φ → ψ ) ) -> ( φ → ψ ).

    Absorption of redundant antecedent.  Also called the "Contraction" or
         "Hilbert" axiom.  Theorem *2.43 of [WhiteheadRussell] p. 106.
         (Contributed by NM, 10-Jan-1993.)  (Proof shortened by Mel L. O'Cat,
         15-Aug-2004.)

    """
    lb = ProofBuilder(sys, "pm2.43")
    stmt = lb.raw("res", "( φ → ( φ → ψ ) ) -> ( φ → ψ )", note="Imported")
    return lb.build(stmt)


def prove_pm2_18(sys: System) -> Proof:
    """
    pm2.18: ( ¬ φ → φ ) → φ.

    Clavius law, or "consequentia mirabilis" ("admirable consequence").  If a
         formula is implied by its negation, then it is true.  Can be used in
         proofs by contradiction.  Theorem *2.18 of [WhiteheadRussell] p. 103.  See
         also the weak Clavius law ~ pm2.01 .  (Contributed by NM, 29-Dec-1992.)
         (Proof shortened by Wolf Lammen, 17-Nov-2023.)

    """
    lb = ProofBuilder(sys, "pm2.18")
    s1 = lb.ref("s1", "( ¬ φ → φ ) -> ( ¬ φ → φ )", ref="id", note="id")
    res = lb.ref("res", "( ( ¬ φ → φ ) -> φ )", s1, ref="pm2.18d", note="pm2.18d")
    return lb.build(res)


def prove_pm2_18d(sys: System) -> Proof:
    """
    pm2.18d: φ → ψ. Hyp: φ → ( ¬ ψ → ψ ).
    """
    lb = ProofBuilder(sys, "pm2.18d")
    h1 = lb.hyp("pm2.18d.1", "φ → ( ¬ ψ → ψ )")

    s1 = lb.ref("s1", "¬ ψ → ( ψ → ¬ ( ¬ ψ → ψ ) )", ref="pm2.21", note="pm2.21")
    s2 = lb.ref(
        "s2",
        "φ → ( ¬ ψ → ¬ ( ¬ ψ → ψ ) )",
        h1,
        s1,
        ref="sylcom",
        note="sylcom",
    )
    res = lb.ref("res", "φ → ψ", h1, s2, ref="mt4d", note="mt4d")
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


def prove_imim1(sys: System) -> Proof:
    """
    imim1: ( φ → ψ ) -> ( ( ψ → χ ) -> ( φ → χ ) ).

    A closed form of syllogism (see ~ syl ).  Theorem *2.06 of
         [WhiteheadRussell] p. 100.  Its associated inference is ~ imim1i .
         (Contributed by NM, 29-Dec-1992.)  (Proof shortened by Wolf Lammen,
         25-May-2013.)

    """
    lb = ProofBuilder(sys, "imim1")
    stmt = lb.raw("res", "( φ → ψ ) -> ( ( ψ → χ ) -> ( φ → χ ) )", note="Imported")
    return lb.build(stmt)


def prove_imim2(sys: System) -> Proof:
    """
    imim2: ( φ → ψ ) -> ( ( χ → φ ) -> ( χ → ψ ) ).

    A closed form of syllogism (see ~ syl ).  Theorem *2.05 of
         [WhiteheadRussell] p. 100.  Its associated inference is ~ imim2i .  Its
         associated deduction is ~ imim2d .  An alternate proof from more basic
         results is given by ~ ax-1 followed by ~ a2d .  (Contributed by NM,
         29-Dec-1992.)  (Proof shortened by Wolf Lammen, 6-Sep-2012.)

    """
    lb = ProofBuilder(sys, "imim2")
    stmt = lb.raw("res", "( φ → ψ ) -> ( ( χ → φ ) -> ( χ → ψ ) )", note="Imported")
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


def debug_dump(proof: Proof, *, sys: System) -> str:
    """Render a lemma proof using the symbol table for debugging."""
    symtab = sys.interner.symbol_table()
    lines = [f"== {proof.name} =="]
    lines.append("statement: " + render(proof.statement.tokens, symtab=symtab))
    for st in proof.steps:
        lines.append(f"{st.label}: {render(st.wff.tokens, symtab=symtab)}    # {st.note}")
    return "\n".join(lines)


__all__ = [
    "Step",
    "Proof",
    "ProofBuilder",
    "prove_modus_tollens",
    "prove_a1i",
    "prove_a2i",
    "prove_mpd",
    "prove_syl",
    "prove_sylcom",
    "prove_com12",
    "prove_syl5",
    "prove_syl6",
    "prove_a1d",
    "prove_idd",
    "prove_a1i13",
    "prove_2a1d",
    "prove_2a1",
    "prove_a2d",
    "prove_syl5com",
    "prove_syl11",
    "prove_syl56",
    "prove_syl6com",
    "prove_mpcom",
    "prove_syli",
    "prove_syl2im",
    "prove_syl2imc",
    "prove_pm2_27",
    "prove_mpdd",
    "prove_mpid",
    "prove_con1",
    "prove_con2",
    "prove_con3",
    "prove_con4",
    "prove_pm2_21",
    "prove_pm2_24",
    "prove_pm2_43",
    "prove_pm2_18",
    "prove_mt2",
    "prove_mt3",
    "prove_nsyl",
    "prove_nsyl2",
    "prove_nsyl3",
    "prove_pm2_61",
    "prove_pm2_65",
    "prove_imim1",
    "prove_imim2",
    "prove_con1i",
    "prove_con2i",
    "prove_con3i",
    "prove_con4i",
    "debug_dump",
]
