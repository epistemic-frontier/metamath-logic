"""Hilbert-style implication calculus.

Axioms: ax-1, ax-2, ax-3, ax-mp.
Operators: → and ¬ (∨ derived: φ∨ψ = ¬φ→ψ).
"""

from __future__ import annotations
from skfd.proof import Proof, ProofBuilder
from . import System


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


def prove_simplim(sys: System) -> Proof:
    """
    simplim: ¬ ( φ → ψ ) -> φ.

    Simplification theorem.
    """
    lb = ProofBuilder(sys, "simplim")
    s1 = lb.ref("s1", "¬ φ → ( φ → ψ )", ref="pm2.21", note="pm2.21")
    res = lb.ref("res", "¬ ( φ → ψ ) -> φ", s1, ref="con1i", note="con1i")
    return lb.build(res)


def prove_a1i(sys: System) -> Proof:
    """
    a1i: ψ → φ.

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
    """a1d: φ → (χ → ψ).

    Hyp: φ → ψ, Concl: φ → (χ → ψ).

    Deduction introducing an embedded antecedent.  Deduction form of ~ ax-1
    and ~ a1i .  (Contributed by NM, 5-Jan-1993.)  (Proof shortened by
    Stefan Allan, 20-Mar-2006.)
    """
    lb = ProofBuilder(sys, "a1d")

    hyp_wff = lb.hyp("a1d.1", "φ → ψ")

    s1 = lb.ref("s1", "ψ → (χ → ψ)", ref="A1", note="A1")
    res = lb.ref("res", "φ → (χ → ψ)", hyp_wff, s1, ref="syl", note="syl")

    return lb.build(res)


def prove_a2d(sys: System) -> Proof:
    """
    a2d: φ → ((ψ → χ) -> (ψ → θ)). Hyp: φ → (ψ → (χ → θ)).

    Deduction distributing an embedded antecedent.  Deduction form of
           ~ ax-2 .  (Contributed by NM, 23-Jun-1994.)

    """
    lb = ProofBuilder(sys, "a2d")
    h1 = lb.hyp("prove_a2d.h", "φ → ( ψ → ( χ → θ ) )")

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

    # Commute the antecedents of hyp2: χ → ( ψ → θ )  ⇒  ψ → ( χ → θ ).
    s1 = lb.ref("s1", "ψ → ( χ → θ )", h2, ref="com12", note="com12(hyp2)")
    # Syllogism with hyp1: φ → ψ , ψ → ( χ → θ )  ⇒  φ → ( χ → θ ).
    res = lb.ref("res", "φ → ( χ → θ )", h1, s1, ref="syl", note="syl(hyp1, s1)")
    return lb.build(res)


def e_id(sys: System) -> Proof:
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


def prove_imim1(sys: System) -> Proof:
    """imim1: (φ → ψ) → ((ψ → χ) → (φ → χ)).

    Derived from safe axioms: A1, A2, syl, com12.
    This replaces the blocked lb.raw() version in lemmas.py.
    """
    lb = ProofBuilder(sys, "imim1")
    s_a1 = lb.ref("s_a1", "( ( ps -> ch ) -> ( ph -> ( ps -> ch ) ) )", ref="A1", note="A1")
    s_a2 = lb.ref(
        "s_a2",
        "( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) )",
        ref="A2",
        note="A2",
    )
    s_syl = lb.ref(
        "s_syl",
        "( ( ps -> ch ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) )",
        s_a1,
        s_a2,
        ref="syl",
        note="syl(A1, A2)",
    )
    res = lb.ref(
        "res",
        "( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) )",
        s_syl,
        ref="com12",
        note="com12(syl)",
    )
    return lb.build(res)


def prove_imim2(sys: System) -> Proof:
    """imim2: (φ → ψ) → ((χ → φ) → (χ → ψ)).

    Derived from safe axioms: A1, A2, syl.
    This replaces the blocked lb.raw() version in lemmas.py.
    """
    lb = ProofBuilder(sys, "imim2")
    s_a1 = lb.ref("s_a1", "( ( ph -> ps ) -> ( ch -> ( ph -> ps ) ) )", ref="A1", note="A1")
    s_a2 = lb.ref(
        "s_a2",
        "( ( ch -> ( ph -> ps ) ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) )",
        ref="A2",
        note="A2",
    )
    res = lb.ref(
        "res",
        "( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) )",
        s_a1,
        s_a2,
        ref="syl",
        note="syl(A1, A2)",
    )
    return lb.build(res)


def prove_pm2_37(sys: System) -> Proof:
    """pm2.37: (ψ → χ) → ((ψ ∨ φ) → (φ ∨ χ)).

    Theorem *2.37 of [WhiteheadRussell] p. 105.
    (Contributed by NM, 6-Mar-2008.)
    pm2.38: (ps→ch)→((¬ps→ph)→(¬ch→ph)).
    pm1.4: (¬ch→ph)→(¬ph→ch).
    syl6: chains pm2.38 with pm1.4.
    """
    lb = ProofBuilder(sys, "pm2.37")
    s1 = lb.ref(
        "s1",
        "( ( ps -> ch ) -> ( ( -. ps -> ph ) -> ( -. ch -> ph ) ) )",
        ref="pm2.38",
        note="pm2.38",
    )
    s2 = lb.ref("s2", "( ( -. ch -> ph ) -> ( -. ph -> ch ) )", ref="pm1.4", note="pm1.4")
    res = lb.ref(
        "res",
        "( ( ps -> ch ) -> ( ( -. ps -> ph ) -> ( -. ph -> ch ) ) )",
        s1,
        s2,
        ref="syl6",
        note="syl6(pm2.38, pm1.4)",
    )
    return lb.build(res)


def prove_pm2_4(sys: System) -> Proof:
    """
    pm2.4: ( ¬ φ → ( ¬ φ → ψ ) ) → ( ¬ φ → ψ ).

    Theorem *2.4 of [WhiteheadRussell] p. 106.
    (Contributed by NM, 3-Jan-2005.)

    Under df-or: ( φ ∨ ( φ ∨ ψ ) ) → ( φ ∨ ψ ).
    This is exactly pm2.43(¬φ, ψ).
    """
    lb = ProofBuilder(sys, "pm2.4")
    res = lb.ref(
        "res",
        "( ¬ φ → ( ¬ φ → ψ ) ) → ( ¬ φ → ψ )",
        ref="pm2.43",
        note="pm2.43",
    )
    return lb.build(res)


def prove_pm2_41(sys: System) -> Proof:
    """Theorem *2.41 of [WhiteheadRussell] p. 106.
    ( ps \\/ ( ph \\/ ps ) ) -> ( ph \\/ ps ).
    (Contributed by NM, 3-Jan-2005.)
    set.mm proof: olc + id + jaoi.
    Under df-or: ( -. ps -> ( -. ph -> ps ) ) -> ( -. ph -> ps ).
    Proof: pm2.61(A1) = pm2.61 with phi:=ps, psi:=( -. ph -> ps )."""
    lb = ProofBuilder(sys, "pm2.41")
    s1 = lb.ref("s1", "ps -> ( -. ph -> ps )", ref="A1", note="A1")
    s2 = lb.ref(
        "s2",
        "( ps -> ( -. ph -> ps ) ) -> ( ( -. ps -> ( -. ph -> ps ) ) -> ( -. ph -> ps ) )",
        ref="pm2.61",
        note="pm2.61",
    )
    res = lb.mp("res", s1, s2, note="MP A1 pm2.61")
    return lb.build(res)


def prove_pm2_42(sys: System) -> Proof:
    """Theorem *2.42 of [WhiteheadRussell] p. 106.
    ( -. ph \\/ ( ph -> ps ) ) -> ( ph -> ps ).
    (Contributed by NM, 3-Jan-2005.)
    set.mm proof: pm2.21 + pm2.4 + jaoi.
    Under df-or: ( -. -. ph -> ( ph -> ps ) ) -> ( ph -> ps ).
    Proof: imim1(notnot) + pm2.43 via mp + syl."""
    lb = ProofBuilder(sys, "pm2.42")
    s_notnot = lb.ref("s_notnot", "ph -> -. -. ph", ref="notnot", note="notnot")
    s_imim1 = lb.ref(
        "s_imim1",
        "( ph -> -. -. ph ) -> ( ( -. -. ph -> ( ph -> ps ) ) -> ( ph -> ( ph -> ps ) ) )",
        ref="imim1",
        note="imim1",
    )
    s_inner = lb.mp("s_inner", s_notnot, s_imim1, note="MP notnot imim1")
    s_pm43 = lb.ref("s_pm43", "( ph -> ( ph -> ps ) ) -> ( ph -> ps )", ref="pm2.43", note="pm2.43")
    res = lb.ref(
        "res",
        "( -. -. ph -> ( ph -> ps ) ) -> ( ph -> ps )",
        s_inner,
        s_pm43,
        ref="syl",
        note="syl(mp(notnot,imim1), pm2.43)",
    )
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


def prove_pm2_8(sys: System) -> Proof:
    """pm2.8: (φ ∨ ψ) → ((¬ψ ∨ χ) → (φ ∨ χ)).

    Theorem *2.8 of [WhiteheadRussell] p. 108.
    (Contributed by NM, 3-Jan-2005.)
    (Proof shortened by Wolf Lammen, 5-Jan-2013.)

    set.mm proof: pm2.53 con1d orim1d.
    Under df-or: (¬φ→ψ)→((¬¬ψ→χ)→(¬φ→χ)).
    Proof: notnot: ψ→¬¬ψ.
           imim2 + mp: (¬φ→ψ)→(¬φ→¬¬ψ).
           imim1: (¬φ→¬¬ψ)→((¬¬ψ→χ)→(¬φ→χ)).
           syl chains them.
    """
    lb = ProofBuilder(sys, "pm2.8")
    s_notnot = lb.ref("s_notnot", "( ps -> -. -. ps )", ref="notnot", note="notnot")
    s_imim2 = lb.ref(
        "s_imim2",
        "( ( ps -> -. -. ps ) -> ( ( -. ph -> ps ) -> ( -. ph -> -. -. ps ) ) )",
        ref="imim2",
        note="imim2",
    )
    s1 = lb.mp("s1", s_notnot, s_imim2, note="MP notnot imim2")
    s_imim1 = lb.ref(
        "s_imim1",
        "( ( -. ph -> -. -. ps ) -> ( ( -. -. ps -> ch ) -> ( -. ph -> ch ) ) )",
        ref="imim1",
        note="imim1",
    )
    res = lb.ref(
        "res",
        "( ( -. ph -> ps ) -> ( ( -. -. ps -> ch ) -> ( -. ph -> ch ) ) )",
        s1,
        s_imim1,
        ref="syl",
        note="syl(s1, imim1)",
    )
    return lb.build(res)


def prove_id(sys: System) -> Proof:
    """id: φ → φ.

    Principle of identity.  Theorem *2.08 of [WhiteheadRussell] p. 101.
    For a shorter proof using ~ ax-2 see ~ idALT .
    (Contributed by NM, 30-Sep-1992.)
    """
    lb = ProofBuilder(sys, "id")
    s1 = lb.ref("s1", "φ → ( φ → φ )", ref="A1", note="ax-1")
    s2 = lb.ref("s2", "φ → ( ( φ → φ ) → φ )", ref="A1", note="ax-1")
    res = lb.ref("res", "φ → φ", s1, s2, ref="mpd", note="mpd")
    return lb.build(res)


def prove_idALT(sys: System) -> Proof:
    """idALT: φ → φ. Alternate proof of id directly from the axioms.

    (Contributed by NM, 30-Sep-1992.)  (Proof modification is discouraged.)
    (New usage is discouraged.)
    """
    lb = ProofBuilder(sys, "idALT")

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


def prove_2a1(sys: System) -> Proof:
    """2a1: φ → (ψ → (χ → φ)). Double form of ax-1. (Contributed by BJ, 10-Aug-2020.)"""
    lb = ProofBuilder(sys, "2a1")
    s1 = lb.ref("s1", "φ → φ", ref="id", note="id")
    res = lb.ref("res", "φ → ( ψ → ( χ → φ ) )", s1, ref="2a1d", note="2a1d")
    return lb.build(res)


def prove_2a1d(sys: System) -> Proof:
    """2a1d: ph → (ch → (th → ps)). Hyp: ph → ps."""
    lb = ProofBuilder(sys, "2a1d")
    hyp = lb.hyp("2a1d.1", "ph → ps")
    s1 = lb.ref("s1", "ph → ( th → ps )", hyp, ref="a1d", note="a1d")
    res = lb.ref("res", "ph → ( ch → ( th → ps ) )", s1, ref="a1d", note="a1d")
    return lb.build(res)

def prove_2a1i(sys: System) -> Proof:
    """2a1i: ps → (ch → ph).

    Hyp: ph
    Concl: ps → (ch → ph)

    Inference introducing two nested antecedents.  Inference associated
    with ~ 2a1 .  (Contributed by NM, 5-Jan-1993.)

    """
    lb = ProofBuilder(sys, "2a1i")
    hyp = lb.hyp("2a1i.1", "ph")
    s1 = lb.ref("s1", "ch → ph", hyp, ref="a1i", note="a1i")
    res = lb.ref("res", "ps → ( ch → ph )", s1, ref="a1i", note="a1i")
    return lb.build(res)

def prove_a1i13(sys: System) -> Proof:
    """a1i13: ph → (ps → (ch → th)). Hyp: ps → th."""
    lb = ProofBuilder(sys, "a1i13")
    hyp = lb.hyp("a1i13.1", "ps → th")
    s1 = lb.ref("s1", "ps → ( ch → th )", hyp, ref="a1d", note="a1d")
    res = lb.ref("res", "ph → ( ps → ( ch → th ) )", s1, ref="a1i", note="a1i")
    return lb.build(res)


def prove_idd(sys: System) -> Proof:
    """idd: φ → (ψ → ψ). No hypotheses."""
    lb = ProofBuilder(sys, "idd")
    s1 = lb.ref("s1", "ψ → ( φ → ψ )", ref="A1", note="A1")
    res = lb.ref("res", "φ → ( ψ → ψ )", s1, ref="com12", note="com12")
    return lb.build(res)


def prove_mpcom(sys: System) -> Proof:
    """mpcom: ψ → χ. Hyp: ψ → φ, φ → (ψ → χ). (Contributed by NM, 17-Mar-1996.)"""
    lb = ProofBuilder(sys, "mpcom")
    h1 = lb.hyp("mpcom.1", "ψ → φ")
    h2 = lb.hyp("mpcom.2", "φ → ( ψ → χ )")
    s1 = lb.ref("s1", "ψ → ( φ → χ )", h2, ref="com12", note="com12")
    res = lb.ref("res", "ψ → χ", h1, s1, ref="mpd", note="mpd")
    return lb.build(res)


def prove_mpdd(sys: System) -> Proof:
    """mpdd: ph → (ps → th). Hyp1: ph → (ps → ch), Hyp2: ph → (ps → (ch → th)).

    Nested modus ponens deduction.
    (Contributed by NM, 26-Mar-1995.)
    set.mm proof: a2d mpd.
    """
    lb = ProofBuilder(sys, "mpdd")
    h1 = lb.hyp("mpdd.1", "( ph → ( ps → ch ) )")
    h2 = lb.hyp("mpdd.2", "( ph → ( ps → ( ch → th ) ) )")
    s1 = lb.ref("s1", "( ph → ( ( ps → ch ) → ( ps → th ) ) )", h2, ref="a2d", note="a2d")
    res = lb.ref("res", "( ph → ( ps → th ) )", h1, s1, ref="mpd", note="mpd")
    return lb.build(res)
def prove_mpid(sys: System) -> Proof:
    """mpid: φ → (ψ → θ). Hyp: φ → χ, φ → (ψ → (χ → θ)). (Contributed by NM, 14-Dec-2004.)"""
    lb = ProofBuilder(sys, "mpid")
    h1 = lb.hyp("mpid.1", "φ → χ")
    h2 = lb.hyp("mpid.2", "φ → ( ψ → ( χ → θ ) )")
    s1 = lb.ref("s1", "φ → ( ψ → χ )", h1, ref="a1d", note="a1d")
    res = lb.ref("res", "φ → ( ψ → θ )", s1, h2, ref="mpdd", note="mpdd")
    return lb.build(res)


def prove_pm2_86d(sys: System) -> Proof:
    """pm2.86d: ph -> ( ps -> ( ch -> th ) ).  Hyp: ph -> ((ps -> ch) -> (ps -> th))."""
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


def prove_pm2_86i(sys: System) -> Proof:
    """pm2.86i: ph -> (ps -> ch).  Hyp: ((ph -> ps) -> (ph -> ch))."""
    lb = ProofBuilder(sys, "pm2.86i")
    h1 = lb.hyp("pm2.86i.1", "( ph -> ps ) -> ( ph -> ch )")
    s1 = lb.ref("s1", "ps -> ( ph -> ch )", h1, ref="jarri", note="jarri")
    res = lb.ref("res", "ph -> ( ps -> ch )", s1, ref="com12", note="com12")
    return lb.build(res)


def prove_imim2i(sys: System) -> Proof:
    """imim2i: (ψ → χ) → ((φ → ψ) → (φ → χ)). Hyp: ψ → χ. (Contributed by NM, 28-Dec-1992.)"""
    lb = ProofBuilder(sys, "imim2i")
    h = lb.hyp("imim2i.1", "ψ → χ")
    s1 = lb.ref("s1", "( ψ → χ ) → ( φ → ( ψ → χ ) )", ref="A1", note="A1")
    s2 = lb.mp("s2", h, s1, note="MP h, A1")
    s3 = lb.ref("s3", "( φ → ( ψ → χ ) ) → ( ( φ → ψ ) → ( φ → χ ) )", ref="A2", note="A2")
    s4 = lb.mp("s4", s2, s3, note="MP s2, A2")
    return lb.build(s4)


def prove_imim3i(sys: System) -> Proof:
    """imim3i: (th -> ph) -> ((th -> ps) -> (th -> ch)).  Hyp: ph -> (ps -> ch).

    Inference adding three nested antecedents.
    (Contributed by NM, 19-Dec-2006.)
    set.mm proof: imim2i a2d.
    """
    lb = ProofBuilder(sys, "imim3i")
    h1 = lb.hyp("imim3i.1", "( ph -> ( ps -> ch ) )")
    s1 = lb.ref("s1", "( ( th -> ph ) -> ( th -> ( ps -> ch ) ) )", h1, ref="imim2i", note="imim2i")
    res = lb.ref(
        "res", "( ( th -> ph ) -> ( ( th -> ps ) -> ( th -> ch ) ) )", s1, ref="a2d", note="a2d"
    )
    return lb.build(res)


def prove_jarr(sys: System) -> Proof:
    """jarr: ((ph → ps) → ch) → (ps → ch).

    "Jar" — weakening of the consequent (backwards "ja").
    (Contributed by NM, 21-Jun-1993.)
    set.mm proof: ax-1 imim1i.

    Derivation: ax-1 gives ps → (ph → ps). Then imim1 chains this
    with the target to get ((ph → ps) → ch) → (ps → ch).
    """
    lb = ProofBuilder(sys, "jarr")
    s1 = lb.ref("s1", "( ps → ( ph → ps ) )", ref="A1", note="A1")
    s2 = lb.ref(
        "s2",
        "( ( ps → ( ph → ps ) ) → ( ( ( ph → ps ) → ch ) → ( ps → ch ) ) )",
        ref="imim1",
        note="imim1",
    )
    res = lb.mp("res", s1, s2, note="MP A1, imim1")
    return lb.build(res)


def prove_jarri(sys: System) -> Proof:
    """jarri: ps -> ch.  Hyp: ((ph -> ps) -> ch)."""
    lb = ProofBuilder(sys, "jarri")
    h1 = lb.hyp("jarri.1", "( ph -> ps ) -> ch")
    s1 = lb.ref("s1", "ps -> ( ph -> ps )", ref="A1", note="A1")
    res = lb.ref("res", "ps -> ch", s1, h1, ref="syl", note="syl")
    return lb.build(res)


def prove_loolin(sys: System) -> Proof:
    """loolin: ((ph → ps) → (ps → ph)) → (ps → ph).

    An alternate for the Linearity Axiom of the infinite-valued sentential
    logic (L-infinity) of Lukasiewicz.
    (Contributed by Mel L. O'Cat, 12-Aug-2004.)
    set.mm proof: jarr pm2.43d.
    """
    lb = ProofBuilder(sys, "loolin")
    s1 = lb.ref(
        "s1", "( ( ( ph → ps ) → ( ps → ph ) ) → ( ps → ( ps → ph ) ) )", ref="jarr", note="jarr"
    )
    res = lb.ref(
        "res", "( ( ( ph → ps ) → ( ps → ph ) ) → ( ps → ph ) )", s1, ref="pm2.43d", note="pm2.43d"
    )
    return lb.build(res)


def prove_mpdi(sys: System) -> Proof:
    """mpdi: ph → (ps → th). Hyp1: ps → ch, Hyp2: ph → (ps → (ch → th)).

    A nested modus ponens deduction.
    (Contributed by NM, 16-Apr-2005.)
    (Proof shortened by Mel L. O'Cat, 15-Jan-2008.)
    set.mm proof: a1i mpdd.
    """
    lb = ProofBuilder(sys, "mpdi")
    h1 = lb.hyp("mpdi.1", "( ps → ch )")
    h2 = lb.hyp("mpdi.2", "( ph → ( ps → ( ch → th ) ) )")
    s1 = lb.ref("s1", "( ph → ( ps → ch ) )", h1, ref="a1i", note="a1i")
    res = lb.ref("res", "( ph → ( ps → th ) )", s1, h2, ref="mpdd", note="mpdd")
    return lb.build(res)


def prove_pm2_43d(sys: System) -> Proof:
    """pm2.43d: ph → (ps → ch). Hyp: ph → (ps → (ps → ch)).

    Deduction absorbing redundant antecedent.
    (Contributed by NM, 18-Aug-1993.)
    set.mm proof: id mpdi.
    """
    lb = ProofBuilder(sys, "pm2.43d")
    h1 = lb.hyp("pm2.43d.1", "( ph → ( ps → ( ps → ch ) ) )")
    s_id = lb.ref("s_id", "( ps → ps )", ref="id", note="id")
    res = lb.ref("res", "( ph → ( ps → ch ) )", s_id, h1, ref="mpdi", note="mpdi")
    return lb.build(res)


def prove_pm2_43i(sys: System) -> Proof:
    """pm2.43i: ph -> ps.  Hyp: ph -> (ph -> ps).

    Inference absorbing redundant antecedent.  Associated with pm2.43.
    (Contributed by NM, 10-Jan-1993.)
    set.mm proof: id mpd.
    """
    lb = ProofBuilder(sys, "pm2.43i")
    h1 = lb.hyp("pm2.43i.1", "( ph -> ( ph -> ps ) )")
    s1 = lb.ref("s1", "( ph -> ph )", ref="id", note="id")
    res = lb.ref("res", "( ph -> ps )", s1, h1, ref="mpd", note="mpd")
    return lb.build(res)


def prove_syld(sys: System) -> Proof:
    """syld: φ → (ψ → θ). Hyp: φ → (ψ → χ), φ → (χ → θ). (Contributed by NM, 5-Aug-1993.)"""
    lb = ProofBuilder(sys, "syld")
    h1 = lb.hyp("syld.1", "φ → ( ψ → χ )")
    h2 = lb.hyp("syld.2", "φ → ( χ → θ )")
    s1 = lb.ref("s1", "φ → ( ψ → ( χ → θ ) )", h2, ref="a1d", note="a1d")
    res = lb.ref("res", "φ → ( ψ → θ )", h1, s1, ref="mpdd", note="mpdd")
    return lb.build(res)


def prove_mp2(sys: System) -> Proof:
    """mp2: χ.

    Hyp 1: φ
    Hyp 2: ψ
    Hyp 3: φ → (ψ → χ)
    Concl: χ

    A double modus ponens inference.
    (Contributed by NM, 5-Apr-1994.)
    """
    lb = ProofBuilder(sys, "mp2")
    h1 = lb.hyp("mp2.1", "φ")
    h2 = lb.hyp("mp2.2", "ψ")
    h3 = lb.hyp("mp2.3", "φ → ( ψ → χ )")
    s1 = lb.mp("s1", h1, h3, "MP mp2.1, mp2.3")
    res = lb.mp("res", h2, s1, "MP mp2.2, s1")
    return lb.build(res)


def prove_mp2b(sys: System) -> Proof:
    """mp2b: χ.

    Hyp 1: φ
    Hyp 2: φ → ψ
    Hyp 3: ψ → χ
    Concl: χ

    A chained modus ponens inference.
    (Contributed by NM, 5-Apr-1994.)
    """
    lb = ProofBuilder(sys, "mp2b")
    h1 = lb.hyp("mp2b.1", "φ")
    h2 = lb.hyp("mp2b.2", "φ → ψ")
    h3 = lb.hyp("mp2b.3", "ψ → χ")
    s1 = lb.mp("s1", h1, h2, "MP mp2b.1, mp2b.2")
    res = lb.mp("res", s1, h3, "MP s1, mp2b.3")
    return lb.build(res)


def prove_mp1i(sys: System) -> Proof:
    """mp1i: χ → ψ.

    Hyp 1: φ
    Hyp 2: φ → ψ
    Concl: χ → ψ

    Inference adding an antecedent to a modus ponens.
    (Contributed by NM, 5-Apr-1994.)
    """
    lb = ProofBuilder(sys, "mp1i")
    h1 = lb.hyp("mp1i.1", "φ")
    h2 = lb.hyp("mp1i.2", "φ → ψ")
    s1 = lb.mp("s1", h1, h2, "MP mp1i.1, mp1i.2")
    res = lb.ref("res", "χ → ψ", s1, ref="a1i", note="a1i")
    return lb.build(res)


def prove_tbw_ax2(sys: System) -> Proof:
    """tbw-ax2: ( ph -> ( ps -> ph ) ).

    Restatement of ax-1.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "tbw-ax2")
    res = lb.ref("res", "ph → ( ps → ph )", ref="A1", note="A1")
    return lb.build(res)


def prove_3syl(sys: System) -> Proof:
    """3syl: φ → θ.

    Hyp 1: φ → ψ
    Hyp 2: ψ → χ
    Hyp 3: χ → θ
    Concl: φ → θ

    Nested syllogism inference.
    (Contributed by NM, 31-Dec-1993.)
    """
    lb = ProofBuilder(sys, "3syl")
    h1 = lb.hyp("3syl.1", "φ → ψ")
    h2 = lb.hyp("3syl.2", "ψ → χ")
    h3 = lb.hyp("3syl.3", "χ → θ")
    s1 = lb.ref("s1", "ψ → θ", h2, h3, ref="syl", note="syl 3syl.2, 3syl.3")
    res = lb.ref("res", "φ → θ", h1, s1, ref="syl", note="syl 3syl.1, s1")
    return lb.build(res)


def prove_4syl(sys: System) -> Proof:
    """4syl: φ → τ.

    Hyp 1: φ → ψ
    Hyp 2: ψ → χ
    Hyp 3: χ → θ
    Hyp 4: θ → τ
    Concl: φ → τ

    Nested syllogism inference.
    (Contributed by NM, 12-May-1993.)
    """
    lb = ProofBuilder(sys, "4syl")
    h1 = lb.hyp("4syl.1", "φ → ψ")
    h2 = lb.hyp("4syl.2", "ψ → χ")
    h3 = lb.hyp("4syl.3", "χ → θ")
    h4 = lb.hyp("4syl.4", "θ → τ")
    s1 = lb.ref("s1", "φ → θ", h1, h2, h3, ref="3syl", note="3syl 4syl.1, 4syl.2, 4syl.3")
    res = lb.ref("res", "φ → τ", s1, h4, ref="syl", note="syl s1, 4syl.4")
    return lb.build(res)


def prove_mpi(sys: System) -> Proof:
    """mpi: φ → χ.

    Hyp 1: ψ
    Hyp 2: φ → (ψ → χ)
    Concl: φ → χ

    An inference form of modus ponens.
    (Contributed by NM, 5-Jul-1994.)
    set.mm proof: a1i mpd.
    """
    lb = ProofBuilder(sys, "mpi")
    h1 = lb.hyp("mpi.1", "ψ")
    h2 = lb.hyp("mpi.2", "φ → ( ψ → χ )")
    s1 = lb.ref("s1", "φ → ψ", h1, ref="a1i", note="a1i mpi.1")
    res = lb.ref("res", "φ → χ", s1, h2, ref="mpd", note="mpd s1, mpi.2")
    return lb.build(res)
