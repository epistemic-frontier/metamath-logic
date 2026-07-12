"""Hilbert-style implication calculus.

Axioms: ax-1, ax-2, ax-3, ax-mp.
Operators: → and ¬ (∨ derived: φ∨ψ = ¬φ→ψ).
"""

from __future__ import annotations

from collections.abc import Callable, Mapping

from skfd.proof import Proof, ProofBuilder

from . import System

LemmaCtor = Callable[[System], Proof]


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
    a1 = lb.ref("s1", "φ → ( ψ → φ )", ref="ax-1", note="A1")
    res = lb.mp("s2", hyp, a1, "MP a1i.1, s1")
    return lb.build(res)


def prove_ax1w(sys: System) -> Proof:
    """ax1w: φ → ( ψ → ( χ → ψ ) ).

    Weak version of ax-1, introducing an additional antecedent.
    (Contributed by NM, 29-Dec-1992.)
    """
    lb = ProofBuilder(sys, "ax1w")
    s1 = lb.ref("s1", "ψ → ( χ → ψ )", ref="ax-1", note="A1")
    res = lb.ref("res", "φ → ( ψ → ( χ → ψ ) )", s1, ref="a1i", note="a1i")
    return lb.build(res)


def prove_ax1(sys: System) -> Proof:
    """ax1: φ → (ψ → φ).

    One of the three Hilbert axioms; equivalent to luklem5.
    """
    lb = ProofBuilder(sys, "ax1")
    res = lb.ref("res", "φ → ( ψ → φ )", ref="luklem5", note="luklem5")
    return lb.build(res)


def prove_a2i(sys: System) -> Proof:
    """
    a2i: (φ → ψ) → (φ → χ).

    Hyp: φ → (ψ → χ)
    Concl: (φ → ψ) → (φ → χ)

    Inference distributing an antecedent.  Inference associated with
           ~ ax-2 .  Its associated inference is ~ mpd .  (Contributed by NM,
           29-Dec-1992.)

    """
    lb = ProofBuilder(sys, "a2i")
    hyp = lb.hyp("a2i.1", "φ → ( ψ → χ )")
    a2 = lb.ref("s1", "( φ → ( ψ → χ ) ) → ( ( φ → ψ ) → ( φ → χ ) )", ref="ax-2", note="A2")
    res = lb.mp("s2", hyp, a2, "MP a2i.1, s1")
    return lb.build(res)


def prove_anidms(sys: System) -> Proof:
    r"""anidms: ph -> ps.

    Hyp: anidms.1 |- ( ( ph /\ ph ) -> ps ).
    Concl: |- ( ph -> ps ).

    Inference eliminating a redundant conjunct from an antecedent.
    (Contributed by NM, 15-Jul-1993.)
    """
    lb = ProofBuilder(sys, "anidms")
    h1 = lb.hyp("anidms.1", "( ( ph /\\ ph ) -> ps )")
    s1 = lb.ref("s1", "( ph -> ( ph -> ps ) )", h1, ref="ex", note="ex")
    res = lb.ref("res", "( ph -> ps )", s1, ref="pm2.43i", note="pm2.43i")
    return lb.build(res)


def prove_animpimp2impd(sys: System) -> Proof:
    """animpimp2impd: φ → ((ψ → χ) → (ψ → (θ → τ))).

    Hyp: animpimp2impd.1 |- ((ψ ∧ φ) → (χ → (θ → η)))
         animpimp2impd.2 |- ((ψ ∧ (φ ∧ θ)) → (η → τ))
    Concl: |- (φ → ((ψ → χ) → (ψ → (θ → τ))))

    Deduction deriving nested implications from conjunctions.
    (Contributed by AV, 21-Aug-2022.)
    """
    lb = ProofBuilder(sys, "animpimp2impd")
    h1 = lb.hyp("animpimp2impd.1", "( ψ ∧ φ ) → ( χ → ( θ → η ) )")
    h2 = lb.hyp("animpimp2impd.2", "( ψ ∧ ( φ ∧ θ ) ) → ( η → τ )")
    s1 = lb.ref("s1", "( ψ ∧ φ ) → ( θ → ( η → τ ) )", h2, ref="expr", note="expr animpimp2impd.2")
    s2 = lb.ref("s2", "( ψ ∧ φ ) → ( ( θ → η ) → ( θ → τ ) )", s1, ref="a2d", note="a2d s1")
    s3 = lb.ref(
        "s3", "( ψ ∧ φ ) → ( χ → ( θ → τ ) )", h1, s2, ref="syld", note="syld animpimp2impd.1, s2"
    )
    s4 = lb.ref("s4", "φ → ( ψ → ( χ → ( θ → τ ) ) )", s3, ref="expcom", note="expcom s3")
    res = lb.ref("res", "φ → ( ( ψ → χ ) → ( ψ → ( θ → τ ) ) )", s4, ref="a2d", note="a2d s4")
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
    a2 = lb.ref("s1", "( φ → ( ψ → χ ) ) → ( ( φ → ψ ) → ( φ → χ ) )", ref="ax-2", note="A2")
    s2 = lb.mp("s2", h2, a2, "MP mpd.2, s1")
    s3 = lb.mp("s3", h1, s2, "MP mpd.1, s2")
    return lb.build(s3)


def prove_mpbi(sys: System) -> Proof:
    """mpbi: ps.

    Hyp 1: ph
    Hyp 2: ( ph <-> ps )
    Concl: ps

    An inference from a biconditional.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "mpbi")
    h1 = lb.hyp("mpbi.min", "ph")
    h2 = lb.hyp("mpbi.maj", "( ph <-> ps )")
    s1 = lb.ref("s1", "ph -> ps", h2, ref="biimpi", note="biimpi mpbi.maj")
    res = lb.mp("res", h1, s1, "MP mpbi.min, s1")
    return lb.build(res)


def prove_mpbir(sys: System) -> Proof:
    """mpbir: ph.

    Hyp 1: ps
    Hyp 2: ( ph <-> ps )
    Concl: ph

    An inference from a biconditional, related to modus ponens.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "mpbir")
    h1 = lb.hyp("mpbir.min", "ps")
    h2 = lb.hyp("mpbir.maj", "( ph <-> ps )")
    s1 = lb.ref("s1", "ps -> ph", h2, ref="biimpri", note="biimpri mpbir.maj")
    res = lb.mp("res", h1, s1, "MP mpbir.min, s1")
    return lb.build(res)


def prove_mpbid(sys: System) -> Proof:
    """mpbid: ph → ch.

    Hyp 1: ph → ps
    Hyp 2: ph → ( ps <-> ch )
    Concl: ph → ch

    A modus ponens deduction from a biconditional.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "mpbid")
    h1 = lb.hyp("mpbid.1", "ph → ps")
    h2 = lb.hyp("mpbid.2", "ph → ( ps <-> ch )")
    s1 = lb.ref("s1", "ph → ( ps → ch )", h2, ref="biimpd", note="biimpd")
    res = lb.ref("res", "ph → ch", h1, s1, ref="mpd", note="mpd")
    return lb.build(res)


def prove_mpbird(sys: System) -> Proof:
    """mpbird: ph → ps.

    Hyp 1: ph → ch
    Hyp 2: ph → ( ps <-> ch )
    Concl: ph → ps

    A modus ponens deduction from a biconditional (reverse direction).
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "mpbird")
    h1 = lb.hyp("mpbird.min", "ph → ch")
    h2 = lb.hyp("mpbird.maj", "ph → ( ps <-> ch )")
    s1 = lb.ref("s1", "ph → ( ch → ps )", h2, ref="biimprd", note="biimprd")
    res = lb.ref("res", "ph → ps", h1, s1, ref="mpd", note="mpd")
    return lb.build(res)


def prove_mpbii(sys: System) -> Proof:
    """mpbii: ph → ch.

    Hyp 1: ps
    Hyp 2: ph → ( ps <-> ch )
    Concl: ph → ch

    A modus ponens inference from a biconditional.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "mpbii")
    h1 = lb.hyp("mpbii.min", "ps")
    h2 = lb.hyp("mpbii.maj", "ph → ( ps <-> ch )")
    s1 = lb.ref("s1", "ph → ps", h1, ref="a1i", note="a1i mpbii.min")
    res = lb.ref("res", "ph → ch", s1, h2, ref="mpbid", note="mpbid s1, mpbii.maj")
    return lb.build(res)


def prove_mpbiri(sys: System) -> Proof:
    """mpbiri: ph → ps.

    Hyp 1: ch
    Hyp 2: ph → ( ps <-> ch )
    Concl: ph → ps

    An inference from a biconditional, reverse of mpbii.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "mpbiri")
    h1 = lb.hyp("mpbiri.min", "ch")
    h2 = lb.hyp("mpbiri.maj", "ph → ( ps <-> ch )")
    s1 = lb.ref("s1", "ph → ch", h1, ref="a1i", note="a1i mpbiri.min")
    res = lb.ref("res", "ph → ps", s1, h2, ref="mpbird", note="mpbird s1, mpbiri.maj")
    return lb.build(res)


def prove_mpbidi(sys: System) -> Proof:
    """mpbidi: ( th → ( ph → ch ) ).

    Inference form of mpbid.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "mpbidi")
    h1 = lb.hyp("mpbidi.min", "th → ( ph → ps )")
    h2 = lb.hyp("mpbidi.maj", "ph → ( ps <-> ch )")
    s1 = lb.ref("s1", "ph → ( ps → ch )", h2, ref="biimpd", note="biimpd mpbidi.maj")
    res = lb.ref("res", "th → ( ph → ch )", h1, s1, ref="sylcom", note="sylcom mpbidi.min, s1")
    return lb.build(res)


def prove_mpbi2and(sys: System) -> Proof:
    r"""mpbi2and: ph -> th.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> ( ( ps /\ ch ) <-> th )
    Concl: ph -> th

    A deduction from a biconditional with two antecedents joined by conjunction.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "mpbi2and")
    h1 = lb.hyp("mpbi2and.1", "( ph -> ps )")
    h2 = lb.hyp("mpbi2and.2", "( ph -> ch )")
    h3 = lb.hyp("mpbi2and.3", r"( ph -> ( ( ps /\ ch ) <-> th ) )")
    s1 = lb.ref(
        "s1",
        r"( ph -> ( ps /\ ch ) )",
        h1,
        h2,
        ref="jca",
        note="jca mpbi2and.1, mpbi2and.2",
    )
    res = lb.ref(
        "res",
        "( ph -> th )",
        s1,
        h3,
        ref="mpbid",
        note="mpbid s1, mpbi2and.3",
    )
    return lb.build(res)


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
    a1 = lb.ref("s1", "( ψ → χ ) → ( φ → ( ψ → χ ) )", ref="ax-1", note="A1")
    s2 = lb.mp("s2", h2, a1, "MP syl.2, s1")
    a2 = lb.ref("s3", "( φ → ( ψ → χ ) ) → ( ( φ → ψ ) → ( φ → χ ) )", ref="ax-2", note="A2")
    s4 = lb.mp("s4", s2, a2, "MP s2, s3")
    s5 = lb.mp("s5", h1, s4, "MP syl.1, s4")
    return lb.build(s5)


def prove_sylib(sys: System) -> Proof:
    """sylib: φ → χ.

    Hyp 1: φ → ψ
    Hyp 2: ψ <-> χ
    Concl: φ → χ

    Syllogism inference with biconditional in the second hypothesis.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sylib")
    h1 = lb.hyp("sylib.1", "φ → ψ")
    h2 = lb.hyp("sylib.2", "ψ <-> χ")
    s1 = lb.ref("s1", "ψ → χ", h2, ref="biimpi", note="biimpi")
    res = lb.ref("res", "φ → χ", h1, s1, ref="syl", note="syl")
    return lb.build(res)


def prove_sylibr(sys: System) -> Proof:
    """sylibr: φ → χ.

    Hyp 1: φ → ψ
    Hyp 2: χ ↔ ψ
    Concl: φ → χ

    Syllogism inference with biconditional in the second hypothesis (reverse).
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sylibr")
    h1 = lb.hyp("sylibr.1", "φ → ψ")
    h2 = lb.hyp("sylibr.2", "χ ↔ ψ")
    s1 = lb.ref("s1", "ψ → χ", h2, ref="biimpri", note="biimpri")
    res = lb.ref("res", "φ → χ", h1, s1, ref="syl", note="syl")
    return lb.build(res)


def prove_sylibd(sys: System) -> Proof:
    """sylibd: ( ph -> ( ps -> th ) ).

    Hyp 1: ( ph -> ( ps -> ch ) )
    Hyp 2: ( ph -> ( ch <-> th ) )
    Concl: ( ph -> ( ps -> th ) )

    Syllogism deduction combined with a biconditional in the second
    hypothesis.  Deduction form of sylib.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sylibd")
    h1 = lb.hyp("sylibd.1", "( ph -> ( ps -> ch ) )")
    h2 = lb.hyp("sylibd.2", "( ph -> ( ch <-> th ) )")
    s1 = lb.ref("s1", "( ph -> ( ch -> th ) )", h2, ref="biimpd", note="biimpd")
    res = lb.ref("res", "( ph -> ( ps -> th ) )", h1, s1, ref="syld", note="syld")
    return lb.build(res)


def prove_sylibrd(sys: System) -> Proof:
    """sylibrd: ( ph -> ( ps -> th ) ).

    Hyp 1: ( ph -> ( ps -> ch ) )
    Hyp 2: ( ph -> ( th <-> ch ) )
    Concl: ( ph -> ( ps -> th ) )

    Syllogism deduction combined with a biconditional in the second
    hypothesis (reverse).  Deduction form of sylibr.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sylibrd")
    h1 = lb.hyp("sylibrd.1", "( ph -> ( ps -> ch ) )")
    h2 = lb.hyp("sylibrd.2", "( ph -> ( th <-> ch ) )")
    s1 = lb.ref("s1", "( ph -> ( ch -> th ) )", h2, ref="biimprd", note="biimprd")
    res = lb.ref("res", "( ph -> ( ps -> th ) )", h1, s1, ref="syld", note="syld")
    return lb.build(res)


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
        "( ψ → ( χ → θ ) ) → ( ( ψ → χ ) → ( ψ → θ ) )",
        ref="ax-2",
        note="A2(ψ,χ,θ)",
    )
    s2 = lb.mp("s2", hyp2_wff, s1, "(ψ→χ)→(ψ→θ)")

    s3 = lb.ref(
        "s3",
        "( ( ψ → χ ) → ( ψ → θ ) ) → ( φ → ( ( ψ → χ ) → ( ψ → θ ) ) )",
        ref="ax-1",
        note="A1 lift",
    )
    s4 = lb.mp("s4", s2, s3, "φ→((ψ→χ)→(ψ→θ))")

    s5 = lb.ref(
        "s5",
        "( φ → ( ( ψ → χ ) → ( ψ → θ ) ) ) → ( ( φ → ( ψ → χ ) ) → ( φ → ( ψ → θ ) ) )",
        ref="ax-2",
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

    s1 = lb.ref("s1", "ψ → ( φ → ψ )", ref="ax-1", note="A1 ψ→(φ→ψ)")
    s2 = lb.ref(
        "s2",
        "( φ → ( ψ → χ ) ) → ( ( φ → ψ ) → ( φ → χ ) )",
        ref="ax-2",
        note="A2 (φ,(ψ→χ))",
    )

    s3 = lb.mp("s3", hyp_wff, s2, "(φ→ψ)→(φ→χ)")

    s4 = lb.ref(
        "s4",
        "( ( φ → ψ ) → ( φ → χ ) ) → ( ψ → ( ( φ → ψ ) → ( φ → χ ) ) )",
        ref="ax-1",
        note="A1 lift",
    )
    s5 = lb.mp("s5", s3, s4, "ψ→((φ→ψ)→(φ→χ))")

    s6 = lb.ref(
        "s6",
        "( ψ → ( ( φ → ψ ) → ( φ → χ ) ) ) → ( ( ψ → ( φ → ψ ) ) → ( ψ → ( φ → χ ) ) )",
        ref="ax-2",
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
        "( χ → ( ψ → θ ) ) → ( φ → ( χ → ( ψ → θ ) ) )",
        ref="ax-1",
        note="A1",
    )
    s2 = lb.mp("s2", h2, s1, "MP syl5.2, s1")
    s3 = lb.ref("s3", "χ → ( φ → ( ψ → θ ) )", s2, ref="com12", note="com12")

    s5 = lb.ref(
        "s5",
        "( φ → ( ψ → θ ) ) → ( ( φ → ψ ) → ( φ → θ ) )",
        ref="ax-2",
        note="A2",
    )
    s6 = lb.ref(
        "s6",
        "( ( φ → ( ψ → θ ) ) → ( ( φ → ψ ) → ( φ → θ ) ) ) → ( χ → ( ( φ → ( ψ → θ ) ) → ( ( φ → ψ ) → ( φ → θ ) ) ) )",
        ref="ax-1",
        note="A1",
    )
    s7 = lb.mp("s7", s5, s6, "MP s5, s6")
    s8 = lb.ref(
        "s8",
        "( χ → ( ( φ → ( ψ → θ ) ) → ( ( φ → ψ ) → ( φ → θ ) ) ) ) → ( ( χ → ( φ → ( ψ → θ ) ) ) → ( χ → ( ( φ → ψ ) → ( φ → θ ) ) ) )",
        ref="ax-2",
        note="A2",
    )
    s9 = lb.mp("s9", s7, s8, "MP s7, s8")
    s10 = lb.mp("s10", s3, s9, "MP s3, s9")

    s11 = lb.ref(
        "s11",
        "( φ → ψ ) → ( χ → ( φ → ψ ) )",
        ref="ax-1",
        note="A1",
    )
    s12 = lb.mp("s12", h1, s11, "MP syl5.1, s11")
    s13 = lb.ref(
        "s13",
        "( χ → ( ( φ → ψ ) → ( φ → θ ) ) ) → ( ( χ → ( φ → ψ ) ) → ( χ → ( φ → θ ) ) )",
        ref="ax-2",
        note="A2",
    )
    s14 = lb.mp("s14", s10, s13, "MP s10, s13")
    res = lb.mp("res", s12, s14, "MP s12, s14")
    return lb.build(res)


def prove_syl5d(sys: System) -> Proof:
    """syl5d: φ → (θ → (ψ → τ)). Hyp: φ → (ψ → χ), φ → (θ → (χ → τ)).

    A syllogism deduction.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "syl5d")
    h1 = lb.hyp("syl5d.1", "φ → (ψ → χ)")
    h2 = lb.hyp("syl5d.2", "φ → (θ → (χ → τ))")
    s1 = lb.ref("s1", "φ → (θ → (ψ → χ))", h1, ref="a1d", note="a1d")
    res = lb.ref("res", "φ → (θ → (ψ → τ))", s1, h2, ref="syldd", note="syldd")
    return lb.build(res)


def prove_imbitrid(sys: System) -> Proof:
    """imbitrid: ( ch -> ( ph -> th ) ).

    A mixed syllogism inference from an implication and a biconditional.
    (Contributed by NM, 25-May-2013.)
    """
    lb = ProofBuilder(sys, "imbitrid")
    h1 = lb.hyp("imbitrid.1", "( ph -> ps )")
    h2 = lb.hyp("imbitrid.2", "( ch -> ( ps <-> th ) )")
    s1 = lb.ref("s1", "( ch -> ( ps -> th ) )", h2, ref="biimpd", note="biimpd")
    res = lb.ref("res", "( ch -> ( ph -> th ) )", h1, s1, ref="syl5", note="syl5")
    return lb.build(res)


def prove_imbitrrid(sys: System) -> Proof:
    """imbitrrid: ( ch -> ( ph -> ps ) ).

    A mixed syllogism inference from an implication and a biconditional.
    (Contributed by NM, 25-May-2013.)
    """
    lb = ProofBuilder(sys, "imbitrrid")
    h1 = lb.hyp("imbitrrid.1", "( ph -> th )")
    h2 = lb.hyp("imbitrrid.2", "( ch -> ( ps <-> th ) )")
    s1 = lb.ref("s1", "( ch -> ( th <-> ps ) )", h2, ref="bicomd", note="bicomd")
    res = lb.ref("res", "( ch -> ( ph -> ps ) )", h1, s1, ref="imbitrid", note="imbitrid")
    return lb.build(res)


def prove_imbitrdi(sys: System) -> Proof:
    """imbitrdi: ( ph -> ( ps -> th ) ).

    A mixed syllogism inference from an implication and a biconditional.
    (Contributed by NM, 25-Jun-2013.)
    """
    lb = ProofBuilder(sys, "imbitrdi")
    h1 = lb.hyp("imbitrdi.1", "( ph -> ( ps -> ch ) )")
    h2 = lb.hyp("imbitrdi.2", "( ch <-> th )")
    s1 = lb.ref("s1", "( ch -> th )", h2, ref="biimpi", note="biimpi imbitrdi.2")
    res = lb.ref("res", "( ph -> ( ps -> th ) )", h1, s1, ref="syl6", note="syl6")
    return lb.build(res)


def prove_imbitrrdi(sys: System) -> Proof:
    """imbitrrdi: ( ph -> ( ps -> th ) ).

    A mixed syllogism inference from an implication and a biconditional.
    (Contributed by NM, 25-Jun-2013.)
    """
    lb = ProofBuilder(sys, "imbitrrdi")
    h1 = lb.hyp("imbitrrdi.1", "( ph -> ( ps -> ch ) )")
    h2 = lb.hyp("imbitrrdi.2", "( th <-> ch )")
    s1 = lb.ref("s1", "( ch -> th )", h2, ref="biimpri", note="biimpri imbitrrdi.2")
    res = lb.ref("res", "( ph -> ( ps -> th ) )", h1, s1, ref="syl6", note="syl6")
    return lb.build(res)


def prove_syl5ibcom(sys: System) -> Proof:
    """syl5ibcom: ( ph -> ( ch -> th ) ).

    Hyp 1: ( ph -> ps )
    Hyp 2: ( ch -> ( ps <-> th ) )
    Concl: ( ph -> ( ch -> th ) )

    A mixed syllogism inference from an implication and a biconditional,
    with commuted antecedents.
    (Contributed by NM, 25-May-2013.)
    """
    lb = ProofBuilder(sys, "syl5ibcom")
    h1 = lb.hyp("syl5ibcom.1", "( ph -> ps )")
    h2 = lb.hyp("syl5ibcom.2", "( ch -> ( ps <-> th ) )")
    s1 = lb.ref("s1", "( ch -> ( ph -> th ) )", h1, h2, ref="imbitrid", note="imbitrid")
    res = lb.ref("res", "( ph -> ( ch -> th ) )", s1, ref="com12", note="com12")
    return lb.build(res)


def prove_syl5ibrcom(sys: System) -> Proof:
    """syl5ibrcom: ( ph -> ( ch -> ps ) ).

    Hyp 1: ( ph -> th )
    Hyp 2: ( ch -> ( ps <-> th ) )
    Concl: ( ph -> ( ch -> ps ) )

    A mixed syllogism inference from an implication and a biconditional,
    with commuted antecedents.
    (Contributed by NM, 25-May-2013.)
    """
    lb = ProofBuilder(sys, "syl5ibrcom")
    h1 = lb.hyp("syl5ibrcom.1", "( ph -> th )")
    h2 = lb.hyp("syl5ibrcom.2", "( ch -> ( ps <-> th ) )")
    s1 = lb.ref("s1", "( ch -> ( ph -> ps ) )", h1, h2, ref="imbitrrid", note="imbitrrid")
    res = lb.ref("res", "( ph -> ( ch -> ps ) )", s1, ref="com12", note="com12")
    return lb.build(res)


def prove_pm2_86d(sys: System) -> Proof:
    """pm2.86d: ( ph -> ( ps -> ( ch -> th ) ) ).  Hyp: ( ph -> ( ( ps -> ch ) -> ( ps -> th ) ) ).

    Deduction associated with ~ pm2.86 .
    (Contributed by NM, 29-Jun-1995.)  (Proof shortened by Wolf Lammen, 3-Apr-2013.)
    """
    lb = ProofBuilder(sys, "pm2.86d")
    h1 = lb.hyp("pm2.86d.1", "( ph -> ( ( ps -> ch ) -> ( ps -> th ) ) )")

    # ax-1: ch -> (ps -> ch)
    s1 = lb.ref("s1", "( ch -> ( ps -> ch ) )", ref="ax-1", note="ax-1")

    # syl5: from s1 (ch -> (ps -> ch)) and h1 (ph -> ((ps -> ch) -> (ps -> th)))
    # syl5.1: φ → ψ   with φ=ch, ψ=(ps -> ch)
    # syl5.2: χ → (ψ → θ) with χ=ph, ψ=(ps -> ch), θ=(ps -> th)
    # conclusion: χ → (φ → θ) = ph -> (ch -> (ps -> th))
    s2 = lb.ref("s2", "( ph -> ( ch -> ( ps -> th ) ) )", s1, h1, ref="syl5", note="syl5")

    # com23: swap second and third antecedents
    # com23.1: ph -> (ch -> (ps -> th)) = φ → (ψ → (χ → θ)) with φ=ph, ψ=ch, χ=ps, θ=th
    # com23: ph -> (ps -> (ch -> th))
    res = lb.ref("res", "( ph -> ( ps -> ( ch -> th ) ) )", s2, ref="com23", note="com23")

    return lb.build(res)


def prove_pm2_86(sys: System) -> Proof:
    """pm2.86: ( ( ph -> ps ) -> ( ph -> ch ) ) -> ( ph -> ( ps -> ch ) ).

    Converse of Axiom ~ ax-2 .  Theorem *2.86 of [WhiteheadRussell] p. 108.
    (Contributed by NM, 25-Apr-1994.)  (Proof shortened by Wolf Lammen,
    3-Apr-2013.)
    """
    lb = ProofBuilder(sys, "pm2.86")

    # id: X -> X
    s1 = lb.ref(
        "s1",
        "( ( ( ph -> ps ) -> ( ph -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) )",
        ref="id",
        note="id",
    )

    # pm2.86d with ph = ((ph -> ps) -> (ph -> ch)), ps=ph, ch=ps, th=ch
    res = lb.ref(
        "res",
        "( ( ( ph -> ps ) -> ( ph -> ch ) ) -> ( ph -> ( ps -> ch ) ) )",
        s1,
        ref="pm2.86d",
        note="pm2.86d",
    )

    return lb.build(res)


def prove_pm2_86i(sys: System) -> Proof:
    """pm2.86i: ( ph -> ( ps -> ch ) ).  Hyp: ( ( ph -> ps ) -> ( ph -> ch ) ).

    Inference associated with ~ pm2.86 .
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm2.86i")
    h1 = lb.hyp("pm2.86i.1", "( ( ph -> ps ) -> ( ph -> ch ) )")

    # pm2.86: ((ph -> ps) -> (ph -> ch)) -> (ph -> (ps -> ch))
    s1 = lb.ref(
        "s1",
        "( ( ( ph -> ps ) -> ( ph -> ch ) ) -> ( ph -> ( ps -> ch ) ) )",
        ref="pm2.86",
        note="pm2.86",
    )

    # MP: h1 and s1
    res = lb.mp("res", h1, s1, "MP pm2.86i.1, pm2.86")

    return lb.build(res)


def prove_biimpcd(sys: System) -> Proof:
    """biimpcd: ( ps -> ( ph -> ch ) ).

    Hyp: ( ph -> ( ps <-> ch ) )
    Concl: ( ps -> ( ph -> ch ) )

    Deduction form of biimpc.
    (Contributed by NM, 30-Sep-1992.)
    """
    lb = ProofBuilder(sys, "biimpcd")
    h = lb.hyp("biimpcd.1", "( ph -> ( ps <-> ch ) )")
    s_id = lb.ref("s_id", "( ps -> ps )", ref="id", note="id")
    res = lb.ref("res", "( ps -> ( ph -> ch ) )", s_id, h, ref="syl5ibcom", note="syl5ibcom")
    return lb.build(res)


def prove_biimprcd(sys: System) -> Proof:
    """biimprcd: ( ch -> ( ph -> ps ) ).

    Hyp: ( ph -> ( ps <-> ch ) )
    Concl: ( ch -> ( ph -> ps ) )

    Deduction form of biimprc.
    (Contributed by NM, 30-Sep-1992.)
    """
    lb = ProofBuilder(sys, "biimprcd")
    h = lb.hyp("biimpcd.1", "( ph -> ( ps <-> ch ) )")
    s_id = lb.ref("s_id", "( ch -> ch )", ref="id", note="id")
    res = lb.ref("res", "( ch -> ( ph -> ps ) )", s_id, h, ref="syl5ibrcom", note="syl5ibrcom")
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

    s1 = lb.ref("s1", "ψ → ( χ → θ )", h2, ref="a1i", note="a1i syl6.2")
    res = lb.ref("res", "φ → ( ψ → θ )", h1, s1, ref="sylcom", note="sylcom syl6.1, s1")

    return lb.build(res)


def prove_syl6c(sys: System) -> Proof:
    """syl6c: φ → (ψ → τ).

    Hyp 1: φ → (ψ → χ)
    Hyp 2: φ → (ψ → θ)
    Hyp 3: χ → (θ → τ)
    Concl: φ → (ψ → τ)

    A nested modus ponens syllogism.  (Contributed by NM, 26-Mar-1995.)
    """
    lb = ProofBuilder(sys, "syl6c")

    h1 = lb.hyp("syl6c.1", "φ → ( ψ → χ )")
    h2 = lb.hyp("syl6c.2", "φ → ( ψ → θ )")
    h3 = lb.hyp("syl6c.3", "χ → ( θ → τ )")

    s1 = lb.ref("s1", "φ → ( ψ → ( θ → τ ) )", h1, h3, ref="syl6", note="syl6")
    res = lb.ref("res", "φ → ( ψ → τ )", h2, s1, ref="mpdd", note="mpdd")

    return lb.build(res)


def prove_syl6d(sys: System) -> Proof:
    """syl6d: φ → (ψ → (χ → τ)).

    Hyp 1: φ → (ψ → (χ → θ))
    Hyp 2: φ → (θ → τ)
    Concl: φ → (ψ → (χ → τ))

    Deduction combining a1d with syldd.  (Contributed by NM, 5-Jan-1993.)
    """
    lb = ProofBuilder(sys, "syl6d")

    h1 = lb.hyp("syl6d.1", "φ → ( ψ → ( χ → θ ) )")
    h2 = lb.hyp("syl6d.2", "φ → ( θ → τ )")

    s1 = lb.ref("s1", "φ → ( ψ → ( θ → τ ) )", h2, ref="a1d", note="a1d syl6d.2")
    res = lb.ref("res", "φ → ( ψ → ( χ → τ ) )", h1, s1, ref="syldd", note="syldd syl6d.1, s1")

    return lb.build(res)


def prove_syl6an(sys: System) -> Proof:
    r"""syl6an: ph -> ( ch -> ta ).

    Hyp 1: ph -> ps
    Hyp 2: ph -> ( ch -> th )
    Hyp 3: ( ps /\ th ) -> ta
    Concl: ph -> ( ch -> ta )

    Syllogism deduction combined with an antecendent and a consequent.
    (Contributed by NM, 12-Dec-1993.)
    """
    lb = ProofBuilder(sys, "syl6an")
    h1 = lb.hyp("syl6an.1", "ph -> ps")
    h2 = lb.hyp("syl6an.2", "ph -> ( ch -> th )")
    h3 = lb.hyp("syl6an.3", r"( ps /\ th ) -> ta")
    s1 = lb.ref("s1", "ps -> ( th -> ta )", h3, ref="ex", note="ex syl6an.3")
    res = lb.ref(
        "res",
        "ph -> ( ch -> ta )",
        h1,
        h2,
        s1,
        ref="sylsyld",
        note="sylsyld syl6an.1, syl6an.2, s1",
    )
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

    s1 = lb.ref("s1", "ψ → (χ → ψ)", ref="ax-1", note="A1")
    res = lb.ref("res", "φ → (χ → ψ)", hyp_wff, s1, ref="syl", note="syl")

    return lb.build(res)


def prove_syl6ci(sys: System) -> Proof:
    """syl6ci: φ → (ψ → τ).

    Hyp 1: φ → (ψ → χ)
    Hyp 2: φ → θ
    Hyp 3: χ → (θ → τ)
    Concl: φ → (ψ → τ)

    Inference form of ~ syl6c .  (Contributed by NM, 22-Jun-1994.)
    """
    lb = ProofBuilder(sys, "syl6ci")

    h1 = lb.hyp("syl6ci.1", "φ → ( ψ → χ )")
    h2 = lb.hyp("syl6ci.2", "φ → θ")
    h3 = lb.hyp("syl6ci.3", "χ → ( θ → τ )")

    s1 = lb.ref("s1", "φ → ( ψ → θ )", h2, ref="a1d", note="a1d syl6ci.2")
    res = lb.ref("res", "φ → ( ψ → τ )", h1, s1, h3, ref="syl6c", note="syl6c syl6ci.1 s1 syl6ci.3")

    return lb.build(res)


def prove_a1dd(sys: System) -> Proof:
    """a1dd: φ → (ψ → (θ → χ)).

    Hyp: φ → (ψ → χ), Concl: φ → (ψ → (θ → χ)).

    Deduction introducing a nested antecedent.  Deduction form of
    ~ a1d .  (Contributed by NM, 5-Jan-1993.)
    """
    lb = ProofBuilder(sys, "a1dd")

    hyp_wff = lb.hyp("a1dd.1", "φ → ( ψ → χ )")

    s1 = lb.ref("s1", "χ → ( θ → χ )", ref="ax-1", note="A1")
    res = lb.ref("res", "φ → ( ψ → ( θ → χ ) )", hyp_wff, s1, ref="syl6", note="syl6")

    return lb.build(res)


def prove_a2d(sys: System) -> Proof:
    """
    a2d: φ → ((ψ → χ) → (ψ → θ)). Hyp: φ → (ψ → (χ → θ)).

    Deduction distributing an embedded antecedent.  Deduction form of
           ~ ax-2 .  (Contributed by NM, 23-Jun-1994.)

    """
    lb = ProofBuilder(sys, "a2d")
    h1 = lb.hyp("prove_a2d.h", "φ → ( ψ → ( χ → θ ) )")

    s1 = lb.ref(
        "s1",
        "( ψ → ( χ → θ ) ) → ( ( ψ → χ ) → ( ψ → θ ) )",
        ref="ax-2",
        note="A2",
    )
    s2 = lb.ref(
        "s2",
        "( ( ψ → ( χ → θ ) ) → ( ( ψ → χ ) → ( ψ → θ ) ) ) → ( φ → ( ( ψ → ( χ → θ ) ) → ( ( ψ → χ ) → ( ψ → θ ) ) ) )",
        ref="ax-1",
        note="A1",
    )
    s3 = lb.mp("s3", s1, s2, "MP s1, s2")
    s4 = lb.ref(
        "s4",
        "( φ → ( ( ψ → ( χ → θ ) ) → ( ( ψ → χ ) → ( ψ → θ ) ) ) ) → ( ( φ → ( ψ → ( χ → θ ) ) ) → ( φ → ( ( ψ → χ ) → ( ψ → θ ) ) ) )",
        ref="ax-2",
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
    h1 = lb.hyp("syl5com.1", "φ → ψ")
    h2 = lb.hyp("syl5com.2", "χ → ( ψ → θ )")

    # a1d(h1): φ → ψ  ⇒  φ → (χ → ψ).
    s1 = lb.ref("s1", "φ → ( χ → ψ )", h1, ref="a1d", note="a1d(h1)")
    # sylcom(s1, h2): φ → (χ → ψ) , χ → (ψ → θ)  ⇒  φ → (χ → θ).
    res = lb.ref("res", "φ → ( χ → θ )", s1, h2, ref="sylcom", note="sylcom(s1, h2)")
    return lb.build(res)


def e_id(sys: System) -> Proof:
    lb = ProofBuilder(sys, "id")

    s1 = lb.ref("s1", "φ → ( φ → φ )", ref="ax-1", note="A1")
    s2 = lb.ref(
        "s2",
        "( φ → ( ( φ → φ ) → φ ) ) → ( ( φ → ( φ → φ ) ) → ( φ → φ ) )",
        ref="ax-2",
        note="A2",
    )
    s3 = lb.ref("s3", "φ → ( ( φ → φ ) → φ )", ref="ax-1", note="A1")
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
    s1 = lb.ref("s1", "( ¬ φ → φ ) → ( ¬ φ → φ )", ref="id", note="id")
    res = lb.ref("res", "( ( ¬ φ → φ ) → φ )", s1, ref="pm2.18d", note="pm2.18d")
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


def prove_pm2_18da(sys: System) -> Proof:
    r"""pm2.18da: ( ph -> ps ).

    Hyp: pm2.18da.1 |- ( ( ph /\ -. ps ) -> ps ).
    Concl: |- ( ph -> ps ).

    Deduction form of pm2.18d.  (Contributed by NM, 29-Dec-1992.)
    """
    lb = ProofBuilder(sys, "pm2.18da")
    h1 = lb.hyp("pm2.18da.1", "( ( ph /\\ ¬ ps ) -> ps )")
    s1 = lb.ref("s1", "( ph -> ( ¬ ps -> ps ) )", h1, ref="ex", note="ex")
    res = lb.ref("res", "( ph -> ps )", s1, ref="pm2.18d", note="pm2.18d")
    return lb.build(res)


def prove_imim1(sys: System) -> Proof:
    """imim1: (φ → ψ) → ((ψ → χ) → (φ → χ)).

    set.mm proof: id, imim1d.
    """
    lb = ProofBuilder(sys, "imim1")
    h = lb.ref("h", "( φ → ψ ) → ( φ → ψ )", ref="id", note="id")
    res = lb.ref("res", "( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) )", h, ref="imim1d", note="imim1d")
    return lb.build(res)


def prove_imim12(sys: System) -> Proof:
    """imim12: ( ( ph -> ps ) -> ( ( ch -> th ) -> ( ( ps -> ch ) -> ( ph -> th ) ) ) ).

    set.mm proof: imim2, imim1, syl9r.
    """
    lb = ProofBuilder(sys, "imim12")
    s1 = lb.ref("s1", "( ch -> th ) -> ( ( ps -> ch ) -> ( ps -> th ) )", ref="imim2", note="imim2")
    s2 = lb.ref("s2", "( ph -> ps ) -> ( ( ps -> th ) -> ( ph -> th ) )", ref="imim1", note="imim1")
    res = lb.ref(
        "res",
        "( ph -> ps ) -> ( ( ch -> th ) -> ( ( ps -> ch ) -> ( ph -> th ) ) )",
        s1,
        s2,
        ref="syl9r",
        note="syl9r",
    )
    return lb.build(res)


def prove_imim2(sys: System) -> Proof:
    """imim2: (φ → ψ) → ((χ → φ) → (χ → ψ)).

    Derived from safe axioms: A1, A2, syl.
    This replaces the blocked lb.raw() version in lemmas.py.
    """
    lb = ProofBuilder(sys, "imim2")
    s_a1 = lb.ref("s_a1", "( ( φ → ψ ) → ( χ → ( φ → ψ ) ) )", ref="ax-1", note="A1")
    s_a2 = lb.ref(
        "s_a2",
        "( ( χ → ( φ → ψ ) ) → ( ( χ → φ ) → ( χ → ψ ) ) )",
        ref="ax-2",
        note="A2",
    )
    res = lb.ref(
        "res",
        "( ( φ → ψ ) → ( ( χ → φ ) → ( χ → ψ ) ) )",
        s_a1,
        s_a2,
        ref="syl",
        note="syl(A1, A2)",
    )
    return lb.build(res)


def prove_impsingle(sys: System) -> Proof:
    """impsingle: ( ( ( φ → ψ ) → χ ) → ( ( χ → φ ) → ( θ → φ ) ) ).

    set.mm proof: imim1, peirce, a1d, syl6.
    """
    lb = ProofBuilder(sys, "impsingle")

    s_imim1 = lb.ref(
        "s_imim1",
        "( ( φ → ψ ) → χ ) → ( ( χ → φ ) → ( ( φ → ψ ) → φ ) )",
        ref="imim1",
        note="imim1",
    )
    s_peirce = lb.ref(
        "s_peirce",
        "( ( φ → ψ ) → φ ) → φ",
        ref="peirce",
        note="peirce",
    )
    s_a1d = lb.ref(
        "s_a1d",
        "( ( φ → ψ ) → φ ) → ( θ → φ )",
        s_peirce,
        ref="a1d",
        note="a1d",
    )
    res = lb.ref(
        "res",
        "( ( φ → ψ ) → χ ) → ( ( χ → φ ) → ( θ → φ ) )",
        s_imim1,
        s_a1d,
        ref="syl6",
        note="syl6",
    )
    return lb.build(res)


def prove_impsingle_step8(sys: System) -> Proof:
    """impsingle-step8: ( ( ( φ → ψ ) → χ ) → ( ψ → χ ) ).

    Derived from impsingle with ax-mp. Step 8 in the impsingle-step series.
    """
    lb = ProofBuilder(sys, "impsingle-step8")

    # impsingle(τ, η, φ, ψ)
    # (1) — reuse for step 27
    s27 = lb.ref(
        "s27",
        "( ( ( τ → η ) → φ ) → ( ( φ → τ ) → ( ψ → τ ) ) )",
        ref="impsingle",
    )

    # (3) impsingle(χ, θ, (φ→ψ), ψ)
    s42 = lb.ref(
        "s42",
        "( ( ( χ → θ ) → ( φ → ψ ) ) → ( ( ( φ → ψ ) → χ ) → ( ψ → χ ) ) )",
        ref="impsingle",
    )

    # (4) same as (1) — step 65
    s65 = lb.ref(
        "s65",
        "( ( ( τ → η ) → φ ) → ( ( φ → τ ) → ( ψ → τ ) ) )",
        ref="impsingle",
    )

    # (5) impsingle(ψ, θ, (ψ→χ), φ)
    s80 = lb.ref(
        "s80",
        "( ( ( ψ → θ ) → ( ψ → χ ) ) → ( ( ( ψ → χ ) → ψ ) → ( φ → ψ ) ) )",
        ref="impsingle",
    )

    # (6) impsingle(ψ, χ, (ψ→χ), φ)
    s99 = lb.ref(
        "s99",
        "( ( ( ψ → χ ) → ( ψ → χ ) ) → ( ( ( ψ → χ ) → ψ ) → ( φ → ψ ) ) )",
        ref="impsingle",
    )

    # (7) impsingle((ψ→χ), (ψ→χ), ((ψ→χ)→ψ)→(φ→ψ), (ψ→θ))
    s104 = lb.ref(
        "s104",
        "( ( ( ( ψ → χ ) → ( ψ → χ ) ) → ( ( ( ψ → χ ) → ψ ) → ( φ → ψ ) ) ) → ( ( ( ( ( ψ → χ ) → ψ ) → ( φ → ψ ) ) → ( ψ → χ ) ) → ( ( ψ → θ ) → ( ψ → χ ) ) ) )",
        ref="impsingle",
    )

    # (8) MP(99, 104)
    s105 = lb.mp("s105", s99, s104)

    # (9) impsingle(((ψ→χ)→ψ)→(φ→ψ), (ψ→χ), (ψ→θ)→(ψ→χ), ((τ→η)→φ)→((φ→τ)→(ψ→τ)))
    s110 = lb.ref(
        "s110",
        "( ( ( ( ( ( ψ → χ ) → ψ ) → ( φ → ψ ) ) → ( ψ → χ ) ) → ( ( ψ → θ ) → ( ψ → χ ) ) ) → ( ( ( ( ψ → θ ) → ( ψ → χ ) ) → ( ( ( ψ → χ ) → ψ ) → ( φ → ψ ) ) ) → ( ( ( ( τ → η ) → φ ) → ( ( φ → τ ) → ( ψ → τ ) ) ) → ( ( ( ψ → χ ) → ψ ) → ( φ → ψ ) ) ) ) )",
        ref="impsingle",
    )

    # (10) MP(105, 110)
    s111 = lb.mp("s111", s105, s110)

    # (11) MP(80, 111)
    s112 = lb.mp("s112", s80, s111)

    # (12) MP(65, 112)
    s113 = lb.mp("s113", s65, s112)

    # (13) impsingle((ψ→χ), ψ, (φ→ψ), ((φ→ψ)→χ))
    s118 = lb.ref(
        "s118",
        "( ( ( ( ψ → χ ) → ψ ) → ( φ → ψ ) ) → ( ( ( φ → ψ ) → ( ψ → χ ) ) → ( ( ( φ → ψ ) → χ ) → ( ψ → χ ) ) ) )",
        ref="impsingle",
    )

    # (14) MP(113, 118)
    s119 = lb.mp("s119", s113, s118)

    # (15) impsingle((φ→ψ), (ψ→χ), ((φ→ψ)→χ)→(ψ→χ), (χ→θ))
    s124 = lb.ref(
        "s124",
        "( ( ( ( φ → ψ ) → ( ψ → χ ) ) → ( ( ( φ → ψ ) → χ ) → ( ψ → χ ) ) ) → ( ( ( ( ( φ → ψ ) → χ ) → ( ψ → χ ) ) → ( φ → ψ ) ) → ( ( χ → θ ) → ( φ → ψ ) ) ) )",
        ref="impsingle",
    )

    # (16) MP(119, 124)
    s125 = lb.mp("s125", s119, s124)

    # (17) impsingle((((φ→ψ)→χ)→(ψ→χ))→(φ→ψ), (χ→θ)→(φ→ψ), ((φ→ψ)→χ)→(ψ→χ), ((τ→η)→φ)→((φ→τ)→(ψ→τ)))
    s130 = lb.ref(
        "s130",
        "( ( ( ( ( ( φ → ψ ) → χ ) → ( ψ → χ ) ) → ( φ → ψ ) ) → ( ( χ → θ ) → ( φ → ψ ) ) ) → ( ( ( ( χ → θ ) → ( φ → ψ ) ) → ( ( ( φ → ψ ) → χ ) → ( ψ → χ ) ) ) → ( ( ( ( τ → η ) → φ ) → ( ( φ → τ ) → ( ψ → τ ) ) ) → ( ( ( φ → ψ ) → χ ) → ( ψ → χ ) ) ) ) )",
        ref="impsingle",
    )

    # (18) MP(125, 130)
    s131 = lb.mp("s131", s125, s130)

    # (19) MP(42, 131)
    s132 = lb.mp("s132", s42, s131)

    # (20) MP(27, 132) — final step
    res = lb.mp("res", s27, s132)

    return lb.build(res)


def prove_impsingle_step4(sys: System) -> Proof:
    """impsingle-step4: ( ( ( ph → ps ) → ph ) → ( ch → ph ) ).

    Derived from impsingle with ax-mp. Step 4 in the impsingle-step series.
    """
    lb = ProofBuilder(sys, "impsingle-step4")

    # (27) impsingle(ta, et, ze, si) — here ze→φ, si→ψ reuse variables
    s27 = lb.ref(
        "s27",
        "( ( ( τ → η ) → φ ) → ( ( φ → τ ) → ( ψ → τ ) ) )",
        ref="impsingle",
    )

    # (42) impsingle(ph, th, (ph→ps), ch)
    s42 = lb.ref(
        "s42",
        "( ( ( φ → θ ) → ( φ → ψ ) ) → ( ( ( φ → ψ ) → φ ) → ( χ → φ ) ) )",
        ref="impsingle",
    )

    # (61) impsingle(ph, ps, (ph→ps), ch)
    s61 = lb.ref(
        "s61",
        "( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( φ → ψ ) → φ ) → ( χ → φ ) ) )",
        ref="impsingle",
    )

    # (66) impsingle((ph→ps), (ph→ps), ((ph→ps)→ph)→(ch→ph), (ph→th))
    s66 = lb.ref(
        "s66",
        "( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( φ → ψ ) → φ ) → ( χ → φ ) ) ) → ( ( ( ( ( φ → ψ ) → φ ) → ( χ → φ ) ) → ( φ → ψ ) ) → ( ( φ → θ ) → ( φ → ψ ) ) ) )",
        ref="impsingle",
    )

    # (67) ax-mp(61, 66)
    s67 = lb.mp("s67", s61, s66)

    # (72) impsingle((((φ→ψ)→φ)→(χ→φ)), (φ→ψ), ((φ→θ)→(φ→ψ)), s27)
    s72 = lb.ref(
        "s72",
        "( ( ( ( ( φ → ψ ) → φ ) → ( χ → φ ) ) → ( φ → ψ ) ) → ( ( φ → θ ) → ( φ → ψ ) ) ) → ( ( ( ( φ → θ ) → ( φ → ψ ) ) → ( ( ( φ → ψ ) → φ ) → ( χ → φ ) ) ) → ( ( ( ( τ → η ) → φ ) → ( ( φ → τ ) → ( ψ → τ ) ) ) → ( ( ( φ → ψ ) → φ ) → ( χ → φ ) ) ) )",
        ref="impsingle",
    )

    # (73) ax-mp(67, 72)
    s73 = lb.mp("s73", s67, s72)

    # (74) ax-mp(42, 73)
    s74 = lb.mp("s74", s42, s73)

    # (75) ax-mp(27, 74) — final step
    res = lb.mp("res", s27, s74)

    return lb.build(res)


def prove_impsingle_step22(sys: System) -> Proof:
    """impsingle-step22: ( ph -> ph ).

    Derived from impsingle-step4 and impsingle with ax-mp.
    Step 22 in the impsingle-step series.
    """
    lb = ProofBuilder(sys, "impsingle-step22")

    # (10) impsingle-step4(th, ta, et)
    s10 = lb.ref(
        "s10",
        "( ( ( θ → τ ) → θ ) → ( η → θ ) )",
        ref="impsingle-step4",
    )

    # (16) impsingle-step4(ph, ps, ph)
    s16 = lb.ref(
        "s16",
        "( ( ( φ → ψ ) → φ ) → ( φ → φ ) )",
        ref="impsingle-step4",
    )

    # (20) impsingle-step4(ph, ph, (ph → ps))
    s20 = lb.ref(
        "s20",
        "( ( ( φ → φ ) → φ ) → ( ( φ → ψ ) → φ ) )",
        ref="impsingle-step4",
    )

    # (21) impsingle((ph → ph), ph, ((ph → ps) → ph), step-10-formula)
    s21 = lb.ref(
        "s21",
        "( ( ( ( φ → φ ) → φ ) → ( ( φ → ψ ) → φ ) ) → ( ( ( ( φ → ψ ) → φ ) → ( φ → φ ) ) → ( ( ( ( θ → τ ) → θ ) → ( η → θ ) ) → ( φ → φ ) ) ) )",
        ref="impsingle",
    )

    # (22) ax-mp(20, 21)
    s22 = lb.mp("s22", s20, s21)

    # (23) ax-mp(16, 22)
    s23 = lb.mp("s23", s16, s22)

    # (24) ax-mp(10, 23)
    res = lb.mp("res", s10, s23)

    return lb.build(res)


def prove_impsingle_step15(sys: System) -> Proof:
    """impsingle-step15: ( ( ( φ → ψ ) → ( χ → θ ) ) → ( ( φ → θ ) → ( χ → θ ) ).

    Derived from impsingle and impsingle-step8 with ax-mp.
    Step 15 in the impsingle-step series.
    """
    lb = ProofBuilder(sys, "impsingle-step15")

    # (1) impsingle(θ, λ, φ, χ)
    s1 = lb.ref(
        "s1",
        "( ( ( θ → λ ) → φ ) → ( ( φ → θ ) → ( χ → θ ) ) )",
        ref="impsingle",
    )

    # (2) impsingle(τ, σ, ρ, μ)
    s2 = lb.ref(
        "s2",
        "( ( ( τ → σ ) → ρ ) → ( ( ρ → τ ) → ( μ → τ ) ) )",
        ref="impsingle",
    )

    # (3) impsingle(((φ→θ)→(χ→θ)), η, ((θ→λ)→φ), ((φ→ψ)→(χ→θ)))
    s3 = lb.ref(
        "s3",
        "( ( ( ( ( φ → θ ) → ( χ → θ ) ) → η ) → ( ( θ → λ ) → φ ) ) → ( ( ( ( θ → λ ) → φ ) → ( ( φ → θ ) → ( χ → θ ) ) ) → ( ( ( φ → ψ ) → ( χ → θ ) ) → ( ( φ → θ ) → ( χ → θ ) ) ) ) )",
        ref="impsingle",
    )

    # (4) impsingle((χ→θ), ζ, (φ→ψ), (φ→θ))
    s4 = lb.ref(
        "s4",
        "( ( ( ( χ → θ ) → ζ ) → ( φ → ψ ) ) → ( ( ( φ → ψ ) → ( χ → θ ) ) → ( ( φ → θ ) → ( χ → θ ) ) ) )",
        ref="impsingle",
    )

    # (5) impsingle-step8(((χ→θ)→ζ), (φ→ψ), (((φ→ψ)→(χ→θ))→((φ→θ)→(χ→θ))))
    s5 = lb.ref(
        "s5",
        "( ( ( ( ( χ → θ ) → ζ ) → ( φ → ψ ) ) → ( ( ( φ → ψ ) → ( χ → θ ) ) → ( ( φ → θ ) → ( χ → θ ) ) ) ) → ( ( φ → ψ ) → ( ( ( φ → ψ ) → ( χ → θ ) ) → ( ( φ → θ ) → ( χ → θ ) ) ) ) )",
        ref="impsingle-step8",
    )

    # (6) ax-mp(4, 5)
    s6 = lb.mp("s6", s4, s5)

    # (7) impsingle(φ, ψ, (((φ→ψ)→(χ→θ))→((φ→θ)→(χ→θ))), (θ→λ))
    s7 = lb.ref(
        "s7",
        "( ( ( φ → ψ ) → ( ( ( φ → ψ ) → ( χ → θ ) ) → ( ( φ → θ ) → ( χ → θ ) ) ) ) → ( ( ( ( ( φ → ψ ) → ( χ → θ ) ) → ( ( φ → θ ) → ( χ → θ ) ) ) → φ ) → ( ( θ → λ ) → φ ) ) )",
        ref="impsingle",
    )

    # (8) ax-mp(6, 7)
    s8 = lb.mp("s8", s6, s7)

    # (9) impsingle((((φ→ψ)→(χ→θ))→((φ→θ)→(χ→θ))), φ, ((θ→λ)→φ), ((θ→λ)→φ)→((φ→θ)→(χ→θ)))
    s9 = lb.ref(
        "s9",
        "( ( ( ( ( ( φ → ψ ) → ( χ → θ ) ) → ( ( φ → θ ) → ( χ → θ ) ) ) → φ ) → ( ( θ → λ ) → φ ) ) → ( ( ( ( θ → λ ) → φ ) → ( ( ( φ → ψ ) → ( χ → θ ) ) → ( ( φ → θ ) → ( χ → θ ) ) ) ) → ( ( ( ( θ → λ ) → φ ) → ( ( φ → θ ) → ( χ → θ ) ) ) → ( ( ( φ → ψ ) → ( χ → θ ) ) → ( ( φ → θ ) → ( χ → θ ) ) ) ) ) )",
        ref="impsingle",
    )

    # (10) ax-mp(8, 9)
    s10 = lb.mp("s10", s8, s9)

    # (11) impsingle(((θ→λ)→φ), (((φ→ψ)→(χ→θ))→((φ→θ)→(χ→θ))), (((θ→λ)→φ)→((φ→θ)→(χ→θ))), (((φ→θ)→(χ→θ))→η))
    s11 = lb.ref(
        "s11",
        "( ( ( ( ( θ → λ ) → φ ) → ( ( ( φ → ψ ) → ( χ → θ ) ) → ( ( φ → θ ) → ( χ → θ ) ) ) ) → ( ( ( ( θ → λ ) → φ ) → ( ( φ → θ ) → ( χ → θ ) ) ) → ( ( ( φ → ψ ) → ( χ → θ ) ) → ( ( φ → θ ) → ( χ → θ ) ) ) ) ) → ( ( ( ( ( ( θ → λ ) → φ ) → ( ( φ → θ ) → ( χ → θ ) ) ) → ( ( ( φ → ψ ) → ( χ → θ ) ) → ( ( φ → θ ) → ( χ → θ ) ) ) ) → ( ( θ → λ ) → φ ) ) → ( ( ( ( φ → θ ) → ( χ → θ ) ) → η ) → ( ( θ → λ ) → φ ) ) ) )",
        ref="impsingle",
    )

    # (12) ax-mp(10, 11)
    s12 = lb.mp("s12", s10, s11)

    # (13) impsingle((((θ→λ)→φ)→((φ→θ)→(χ→θ)))→(((φ→ψ)→(χ→θ))→((φ→θ)→(χ→θ))), (θ→λ)→φ, ((φ→θ)→(χ→θ))→η, ((τ→σ)→ρ)→((ρ→τ)→(μ→τ)))
    s13 = lb.ref(
        "s13",
        "( ( ( ( ( ( ( θ → λ ) → φ ) → ( ( φ → θ ) → ( χ → θ ) ) ) → ( ( ( φ → ψ ) → ( χ → θ ) ) → ( ( φ → θ ) → ( χ → θ ) ) ) ) → ( ( θ → λ ) → φ ) ) → ( ( ( ( φ → θ ) → ( χ → θ ) ) → η ) → ( ( θ → λ ) → φ ) ) ) → ( ( ( ( ( ( φ → θ ) → ( χ → θ ) ) → η ) → ( ( θ → λ ) → φ ) ) → ( ( ( ( θ → λ ) → φ ) → ( ( φ → θ ) → ( χ → θ ) ) ) → ( ( ( φ → ψ ) → ( χ → θ ) ) → ( ( φ → θ ) → ( χ → θ ) ) ) ) ) → ( ( ( ( τ → σ ) → ρ ) → ( ( ρ → τ ) → ( μ → τ ) ) ) → ( ( ( ( θ → λ ) → φ ) → ( ( φ → θ ) → ( χ → θ ) ) ) → ( ( ( φ → ψ ) → ( χ → θ ) ) → ( ( φ → θ ) → ( χ → θ ) ) ) ) ) ) )",
        ref="impsingle",
    )

    # (14) ax-mp(12, 13)
    s14 = lb.mp("s14", s12, s13)

    # (15) ax-mp(3, 14)
    s15 = lb.mp("s15", s3, s14)

    # (16) ax-mp(2, 15)
    s16 = lb.mp("s16", s2, s15)

    # (17) ax-mp(1, 16) — final
    res = lb.mp("res", s1, s16)

    return lb.build(res)


def prove_impsingle_ax1(sys: System) -> Proof:
    """impsingle-ax1: ( ph -> ( ps -> ph ) ).

    Derived from impsingle-step8 with ax-mp.  (Contributed by NM, 29-Dec-1992.)
    """
    lb = ProofBuilder(sys, "impsingle-ax1")

    # impsingle-step8(χ, ψ, φ): ((χ → ψ) → φ) → (ψ → φ)
    s1 = lb.ref(
        "s1",
        "( ( ( χ → ψ ) → φ ) → ( ψ → φ ) )",
        ref="impsingle-step8",
    )

    # impsingle-step8((χ→ψ), φ, (ψ→φ)):
    #   (((χ → ψ) → φ) → (ψ → φ)) → (φ → (ψ → φ))
    s2 = lb.ref(
        "s2",
        "( ( ( ( χ → ψ ) → φ ) → ( ψ → φ ) ) → ( φ → ( ψ → φ ) ) )",
        ref="impsingle-step8",
    )

    # ax-mp: s1, s2 → (φ → (ψ → φ))
    res = lb.mp("res", s1, s2)

    return lb.build(res)


def prove_imim1d(sys: System) -> Proof:
    """imim1d: φ → ((χ → θ) → (ψ → θ)).  Hyp: φ → (ψ → χ).

    Deduction form of imim1.
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: idd imim12d.
    """
    lb = ProofBuilder(sys, "imim1d")
    h1 = lb.hyp("imim1d.1", "φ → (ψ → χ)")
    s_idd = lb.ref("s_idd", "φ → (θ → θ)", ref="idd", note="idd")
    res = lb.ref("res", "φ → ((χ → θ) → (ψ → θ))", h1, s_idd, ref="imim12d", note="imim12d")
    return lb.build(res)


def prove_pm2_37(sys: System) -> Proof:
    """pm2.37: (ψ → χ) → ((ψ ∨ φ) → (φ ∨ χ)).

    Theorem *2.37 of [WhiteheadRussell] p. 105.
    (Contributed by NM, 6-Mar-2008.)
    pm2.38: (ψ→χ)→((¬ψ→φ)→(¬χ→φ)).
    pm1.4: (¬χ→φ)→(¬φ→χ).
    syl6: chains pm2.38 with pm1.4.
    """
    lb = ProofBuilder(sys, "pm2.37")
    s1 = lb.ref(
        "s1",
        "( ψ → χ ) → ( ( ψ ∨ φ ) → ( χ ∨ φ ) )",
        ref="pm2.38",
        note="pm2.38",
    )
    s2 = lb.ref("s2", "( χ ∨ φ ) → ( φ ∨ χ )", ref="pm1.4", note="pm1.4")
    res = lb.ref(
        "res",
        "( ψ → χ ) → ( ( ψ ∨ φ ) → ( φ ∨ χ ) )",
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


def prove_pm2_42(sys: System) -> Proof:
    """Theorem *2.42 of [WhiteheadRussell] p. 106.
    ( -. φ \\/ ( φ → ψ ) ) → ( φ → ψ ).
    (Contributed by NM, 3-Jan-2005.)
    set.mm proof: pm2.21 + pm2.4 + jaoi.
    Under df-or: ( -. -. φ → ( φ → ψ ) ) → ( φ → ψ ).
    Proof: imim1(notnot) + pm2.43 via mp + syl."""
    lb = ProofBuilder(sys, "pm2.42")
    s_notnot = lb.ref("s_notnot", "φ → -. -. φ", ref="notnot", note="notnot")
    s_imim1 = lb.ref(
        "s_imim1",
        "( φ → -. -. φ ) → ( ( -. -. φ → ( φ → ψ ) ) → ( φ → ( φ → ψ ) ) )",
        ref="imim1",
        note="imim1",
    )
    s_inner = lb.mp("s_inner", s_notnot, s_imim1, note="MP notnot imim1")
    s_pm43 = lb.ref("s_pm43", "( φ → ( φ → ψ ) ) → ( φ → ψ )", ref="pm2.43", note="pm2.43")
    res = lb.ref(
        "res",
        "( -. -. φ → ( φ → ψ ) ) → ( φ → ψ )",
        s_inner,
        s_pm43,
        ref="syl",
        note="syl(mp(notnot,imim1), pm2.43)",
    )
    return lb.build(res)


def prove_id(sys: System) -> Proof:
    """id: φ → φ.

    Principle of identity.  Theorem *2.08 of [WhiteheadRussell] p. 101.
    For a shorter proof using ~ ax-2 see ~ idALT .
    (Contributed by NM, 30-Sep-1992.)
    """
    lb = ProofBuilder(sys, "id")
    s1 = lb.ref("s1", "φ → ( φ → φ )", ref="ax-1", note="ax-1")
    s2 = lb.ref("s2", "φ → ( ( φ → φ ) → φ )", ref="ax-1", note="ax-1")
    res = lb.ref("res", "φ → φ", s1, s2, ref="mpd", note="mpd")
    return lb.build(res)


def prove_idALT(sys: System) -> Proof:
    """idALT: φ → φ. Alternate proof of id directly from the axioms.

    (Contributed by NM, 30-Sep-1992.)  (Proof modification is discouraged.)
    (New usage is discouraged.)
    """
    lb = ProofBuilder(sys, "idALT")

    s1 = lb.ref("s1", "φ → ( φ → φ )", ref="ax-1", note="A1")
    s2 = lb.ref(
        "s2",
        "( φ → ( ( φ → φ ) → φ ) ) → ( ( φ → ( φ → φ ) ) → ( φ → φ ) )",
        ref="ax-2",
        note="A2",
    )
    s3 = lb.ref("s3", "φ → ( ( φ → φ ) → φ )", ref="ax-1", note="A1")
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
    """2a1d: φ → (χ → (θ → ψ)). Hyp: φ → ψ."""
    lb = ProofBuilder(sys, "2a1d")
    hyp = lb.hyp("2a1d.1", "φ → ψ")
    s1 = lb.ref("s1", "φ → ( θ → ψ )", hyp, ref="a1d", note="a1d")
    res = lb.ref("res", "φ → ( χ → ( θ → ψ ) )", s1, ref="a1d", note="a1d")
    return lb.build(res)


def prove_2a1i(sys: System) -> Proof:
    """2a1i: ψ → (χ → φ).

    Hyp: φ
    Concl: ψ → (χ → φ)

    Inference introducing two nested antecedents.  Inference associated
    with ~ 2a1 .  (Contributed by NM, 5-Jan-1993.)

    """
    lb = ProofBuilder(sys, "2a1i")
    hyp = lb.hyp("2a1i.1", "φ")
    s1 = lb.ref("s1", "χ → φ", hyp, ref="a1i", note="a1i")
    res = lb.ref("res", "ψ → ( χ → φ )", s1, ref="a1i", note="a1i")
    return lb.build(res)


def prove_a1i13(sys: System) -> Proof:
    """a1i13: φ → (ψ → (χ → θ)). Hyp: ψ → θ."""
    lb = ProofBuilder(sys, "a1i13")
    hyp = lb.hyp("a1i13.1", "ψ → θ")
    s1 = lb.ref("s1", "ψ → ( χ → θ )", hyp, ref="a1d", note="a1d")
    res = lb.ref("res", "φ → ( ψ → ( χ → θ ) )", s1, ref="a1i", note="a1i")
    return lb.build(res)


def prove_idd(sys: System) -> Proof:
    """idd: φ → (ψ → ψ). No hypotheses."""
    lb = ProofBuilder(sys, "idd")
    s1 = lb.ref("s1", "ψ → ( φ → ψ )", ref="ax-1", note="A1")
    res = lb.ref("res", "φ → ( ψ → ψ )", s1, ref="com12", note="com12")
    return lb.build(res)


def prove_ibi(sys: System) -> Proof:
    """ibi: ph → ps.  Hyp: ph → ( ph <-> ps ).

    Inference from a biconditional.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "ibi")
    h = lb.hyp("ibi.1", "ph → ( ph <-> ps )")
    s1 = lb.ref("s1", "ph → ph", ref="id", note="id")
    res = lb.ref("res", "ph → ps", s1, h, ref="mpbid", note="mpbid")
    return lb.build(res)


def prove_ibir(sys: System) -> Proof:
    """ibir: ph → ps.  Hyp: ph → ( ps <-> ph ).

    Inference from a biconditional, with the biconditional commuted.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "ibir")
    h = lb.hyp("ibir.1", "ph → ( ps <-> ph )")
    s1 = lb.ref("s1", "ph → ( ph <-> ps )", h, ref="bicomd", note="bicomd")
    res = lb.ref("res", "ph → ps", s1, ref="ibi", note="ibi")
    return lb.build(res)


def prove_ibd(sys: System) -> Proof:
    """ibd: ph → ( ps → ch ).  Hyp: ph → ( ps → ( ps <-> ch ) ).

    Deduction from a biconditional.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "ibd")
    h = lb.hyp("ibd.1", "ph → ( ps → ( ps <-> ch ) )")
    s1 = lb.ref("s1", "( ps <-> ch ) → ( ps → ch )", ref="biimp", note="biimp")
    res = lb.ref("res", "ph → ( ps → ch )", h, s1, ref="syli", note="syli")
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
    """mpdd: φ → (ψ → θ). Hyp1: φ → (ψ → χ), Hyp2: φ → (ψ → (χ → θ)).

    Nested modus ponens deduction.
    (Contributed by NM, 26-Mar-1995.)
    set.mm proof: a2d mpd.
    """
    lb = ProofBuilder(sys, "mpdd")
    h1 = lb.hyp("mpdd.1", "( φ → ( ψ → χ ) )")
    h2 = lb.hyp("mpdd.2", "( φ → ( ψ → ( χ → θ ) ) )")
    s1 = lb.ref("s1", "( φ → ( ( ψ → χ ) → ( ψ → θ ) ) )", h2, ref="a2d", note="a2d")
    res = lb.ref("res", "( φ → ( ψ → θ ) )", h1, s1, ref="mpd", note="mpd")
    return lb.build(res)


def prove_mpid(sys: System) -> Proof:
    """mpid: φ → (ψ → θ). Hyp: φ → χ, φ → (ψ → (χ → θ)). (Contributed by NM, 14-Dec-2004.)"""
    lb = ProofBuilder(sys, "mpid")
    h1 = lb.hyp("mpid.1", "φ → χ")
    h2 = lb.hyp("mpid.2", "φ → ( ψ → ( χ → θ ) )")
    s1 = lb.ref("s1", "φ → ( ψ → χ )", h1, ref="a1d", note="a1d")
    res = lb.ref("res", "φ → ( ψ → θ )", s1, h2, ref="mpdd", note="mpdd")
    return lb.build(res)


def prove_imim2i(sys: System) -> Proof:
    """imim2i: (ψ → χ) → ((φ → ψ) → (φ → χ)). Hyp: ψ → χ. (Contributed by NM, 28-Dec-1992.)"""
    lb = ProofBuilder(sys, "imim2i")
    h = lb.hyp("imim2i.1", "ψ → χ")
    s1 = lb.ref("s1", "( ψ → χ ) → ( φ → ( ψ → χ ) )", ref="ax-1", note="A1")
    s2 = lb.mp("s2", h, s1, note="MP h, A1")
    s3 = lb.ref("s3", "( φ → ( ψ → χ ) ) → ( ( φ → ψ ) → ( φ → χ ) )", ref="ax-2", note="A2")
    s4 = lb.mp("s4", s2, s3, note="MP s2, A2")
    return lb.build(s4)


def prove_imim3i(sys: System) -> Proof:
    """imim3i: (θ → φ) → ((θ → ψ) → (θ → χ)).  Hyp: φ → (ψ → χ).

    Inference adding three nested antecedents.
    (Contributed by NM, 19-Dec-2006.)
    set.mm proof: imim2i a2d.
    """
    lb = ProofBuilder(sys, "imim3i")
    h1 = lb.hyp("imim3i.1", "( φ → ( ψ → χ ) )")
    s1 = lb.ref("s1", "( ( θ → φ ) → ( θ → ( ψ → χ ) ) )", h1, ref="imim2i", note="imim2i")
    res = lb.ref("res", "( ( θ → φ ) → ( ( θ → ψ ) → ( θ → χ ) ) )", s1, ref="a2d", note="a2d")
    return lb.build(res)


def prove_imim2d(sys: System) -> Proof:
    """imim2d: φ → ((θ → ψ) → (θ → χ)).  Hyp: φ → (ψ → χ).

    Deduction form of imim2 and imim3i.
    (Contributed by NM, 23-Jun-1994.)
    set.mm proof: a1d a2d.
    """
    lb = ProofBuilder(sys, "imim2d")
    hyp = lb.hyp("imim2d.1", "( φ → ( ψ → χ ) )")

    s1 = lb.ref("s1", "( φ → ( θ → ( ψ → χ ) ) )", hyp, ref="a1d", note="a1d")
    res = lb.ref("res", "( φ → ( ( θ → ψ ) → ( θ → χ ) ) )", s1, ref="a2d", note="a2d")

    return lb.build(res)


def prove_imim12d(sys: System) -> Proof:
    """imim12d: φ → ((χ → θ) → (ψ → τ)).  Hyp: φ → (ψ → χ), φ → (θ → τ).

    Deduction form of imim12.
    (Contributed by NM, 23-Jun-1994.)
    set.mm proof: imim2d syl5d.
    """
    lb = ProofBuilder(sys, "imim12d")
    h1 = lb.hyp("imim12d.1", "φ → (ψ → χ)")
    h2 = lb.hyp("imim12d.2", "φ → (θ → τ)")

    s1 = lb.ref("s1", "φ → ((χ → θ) → (χ → τ))", h2, ref="imim2d", note="imim2d")
    res = lb.ref("res", "φ → ((χ → θ) → (ψ → τ))", h1, s1, ref="syl5d", note="syl5d")

    return lb.build(res)


def prove_jarr(sys: System) -> Proof:
    """jarr: ((φ → ψ) → χ) → (ψ → χ).

    "Jar" — weakening of the consequent (backwards "ja").
    (Contributed by NM, 21-Jun-1993.)
    set.mm proof: ax-1 imim1i.

    Derivation: ax-1 gives ψ → (φ → ψ). Then imim1 chains this
    with the target to get ((φ → ψ) → χ) → (ψ → χ).
    """
    lb = ProofBuilder(sys, "jarr")
    s1 = lb.ref("s1", "( ψ → ( φ → ψ ) )", ref="ax-1", note="A1")
    s2 = lb.ref(
        "s2",
        "( ( ψ → ( φ → ψ ) ) → ( ( ( φ → ψ ) → χ ) → ( ψ → χ ) ) )",
        ref="imim1",
        note="imim1",
    )
    res = lb.mp("res", s1, s2, note="MP A1, imim1")
    return lb.build(res)


def prove_jarri(sys: System) -> Proof:
    """jarri: ψ → χ.  Hyp: ((φ → ψ) → χ)."""
    lb = ProofBuilder(sys, "jarri")
    h1 = lb.hyp("jarri.1", "( φ → ψ ) → χ")
    s1 = lb.ref("s1", "ψ → ( φ → ψ )", ref="ax-1", note="A1")
    res = lb.ref("res", "ψ → χ", s1, h1, ref="syl", note="syl")
    return lb.build(res)


def prove_loolin(sys: System) -> Proof:
    """loolin: ((φ → ψ) → (ψ → φ)) → (ψ → φ).

    An alternate for the Linearity Axiom of the infinite-valued sentential
    logic (L-infinity) of Lukasiewicz.
    (Contributed by Mel L. O'Cat, 12-Aug-2004.)
    set.mm proof: jarr pm2.43d.
    """
    lb = ProofBuilder(sys, "loolin")
    s1 = lb.ref("s1", "( ( ( φ → ψ ) → ( ψ → φ ) ) → ( ψ → ( ψ → φ ) ) )", ref="jarr", note="jarr")
    res = lb.ref(
        "res", "( ( ( φ → ψ ) → ( ψ → φ ) ) → ( ψ → φ ) )", s1, ref="pm2.43d", note="pm2.43d"
    )
    return lb.build(res)


def prove_loowoz(sys: System) -> Proof:
    """loowoz: (((φ → ψ) → (φ → χ)) → ((ψ → φ) → (ψ → χ))).

    An alternate for the Linearity Axiom of the infinite-valued sentential
    logic (L-infinity) of Lukasiewicz.  (Contributed by NM, 12-Aug-2004.)
    set.mm proof: wi jarr a2d.
    """
    lb = ProofBuilder(sys, "loowoz")
    s1 = lb.ref(
        "s1",
        "( ( ( φ → ψ ) → ( φ → χ ) ) → ( ψ → ( φ → χ ) ) )",
        ref="jarr",
        note="jarr",
    )
    res = lb.ref(
        "res",
        "( ( ( φ → ψ ) → ( φ → χ ) ) → ( ( ψ → φ ) → ( ψ → χ ) ) )",
        s1,
        ref="a2d",
        note="a2d",
    )
    return lb.build(res)


def prove_looinv(sys: System) -> Proof:
    """looinv: ((φ → ψ) → ψ) → ((ψ → φ) → φ).

    An alternate for the Linearity Axiom of the infinite-valued sentential
    logic (L-infinity) of Lukasiewicz.
    (Contributed by NM, 12-Aug-2004.)
    set.mm proof: imim1 peirce syl6.
    """
    lb = ProofBuilder(sys, "looinv")
    s1 = lb.ref(
        "s1",
        "( ( ( φ → ψ ) → ψ ) → ( ( ψ → φ ) → ( ( φ → ψ ) → φ ) ) )",
        ref="imim1",
        note="imim1",
    )
    s2 = lb.ref(
        "s2",
        "( ( φ → ψ ) → φ ) → φ",
        ref="peirce",
        note="peirce",
    )
    res = lb.ref(
        "res",
        "( ( ( φ → ψ ) → ψ ) → ( ( ψ → φ ) → φ ) )",
        s1,
        s2,
        ref="syl6",
        note="syl6",
    )
    return lb.build(res)


def prove_luk_1(sys: System) -> Proof:
    """luk-1: ( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) ).

    One of the three Łukasiewicz axioms for propositional calculus,
    derived from Meredith's sole axiom.
    (Contributed by NM, 14-Dec-2002.)
    """
    lb = ProofBuilder(sys, "luk-1")

    # ( ( ( χ → χ ) → ( ¬ ¬ ¬ φ → ¬ φ ) ) → ¬ ¬ φ ) → ψ
    B = "( ( ( χ → χ ) → ( ¬ ¬ ¬ φ → ¬ φ ) ) → ¬ ¬ φ ) → ψ"
    # ( ( ψ → χ ) → ( φ → χ ) ) → φ
    C = "( ( ( ψ → χ ) → ( φ → χ ) ) → φ )"
    # ¬ ¬ ¬ ( φ → ψ ) → ¬ ( φ → ψ )
    D = "( ¬ ¬ ¬ ( φ → ψ ) → ¬ ( φ → ψ ) )"
    # ¬ ¬ ( φ → ψ )
    E = "¬ ¬ ( φ → ψ )"

    # Step 1: meredith with φ=χ, ψ=χ, χ=¬¬φ, θ=φ, τ=ψ
    s1 = lb.ref(
        "s1",
        f"( ( {B} ) → ( ( ψ → χ ) → ( φ → χ ) ) )",
        ref="meredith",
        note="meredith",
    )

    # Step 2: merlem13 with φ=φ, ψ=ψ, θ=(χ→χ), χ=¬φ
    s2 = lb.ref(
        "s2",
        f"( ( φ → ψ ) → ( {B} ) )",
        ref="merlem13",
        note="merlem13",
    )

    # Step 3: merlem13 with φ=(φ→ψ), ψ=B, θ=C, χ=¬(φ→ψ)
    s3 = lb.ref(
        "s3",
        f"( ( ( φ → ψ ) → ( {B} ) ) → ( ( ( ( {C} ) → ( {D} ) ) → ( {E} ) ) → ( {B} ) ) )",
        ref="merlem13",
        note="merlem13",
    )

    # Step 4: ax-mp(2, 3)
    s4 = lb.mp(
        "s4",
        s2,
        s3,
        note="MP s2, s3",
    )

    # Step 5: meredith with φ=((ψ→χ)→(φ→χ)), ψ=φ, χ=E, θ=(φ→ψ), τ=B
    s5 = lb.ref(
        "s5",
        f"( ( ( ( ( {C} ) → ( {D} ) ) → ( {E} ) ) → ( {B} ) ) → ( ( ( {B} ) → ( ( ψ → χ ) → ( φ → χ ) ) ) → ( ( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) ) ) ) )",
        ref="meredith",
        note="meredith",
    )

    # Step 6: ax-mp(4, 5)
    s6 = lb.mp(
        "s6",
        s4,
        s5,
        note="MP s4, s5",
    )

    # Step 7: ax-mp(1, 6)
    res = lb.mp(
        "res",
        s1,
        s6,
        note="MP s1, s6",
    )

    return lb.build(res)


def prove_luklem1(sys: System) -> Proof:
    """luklem1: φ → χ.

    Hyp 1: φ → ψ
    Hyp 2: ψ → χ
    Concl: φ → χ

    Lemma used in the derivation of the Łukasiewicz axioms from Meredith's
    sole axiom.
    (Contributed by NM, 14-Dec-2002.)
    """
    lb = ProofBuilder(sys, "luklem1")
    h1 = lb.hyp("luklem1.1", "φ → ψ")
    h2 = lb.hyp("luklem1.2", "ψ → χ")
    s1 = lb.ref(
        "s1",
        "( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) )",
        ref="luk-1",
        note="luk-1",
    )
    s2 = lb.mp("s2", h1, s1, "MP luklem1.1, s1")
    res = lb.mp("res", h2, s2, "MP luklem1.2, s2")
    return lb.build(res)


def prove_luklem5(sys: System) -> Proof:
    """luklem5: φ → (ψ → φ).

    Used to rederive standard propositional axioms from Łukasiewicz'.
    (Contributed by NM, 22-Dec-2002.)
    """
    lb = ProofBuilder(sys, "luklem5")

    # s1: φ → (((¬φ → φ) → φ) → (ψ → φ))    [luklem3]
    s1 = lb.ref(
        "s1",
        "φ → ( ( ( ¬ φ → φ ) → φ ) → ( ψ → φ ) )",
        ref="luklem3",
        note="luklem3",
    )

    # s2: ((((¬φ → φ) → φ) → (ψ → φ)) → (ψ → φ))    [luklem4]
    s2 = lb.ref(
        "s2",
        "( ( ( ( ¬ φ → φ ) → φ ) → ( ψ → φ ) ) → ( ψ → φ ) )",
        ref="luklem4",
        note="luklem4",
    )

    # res: φ → (ψ → φ)    [luklem1 s1, s2]
    res = lb.ref(
        "res",
        "φ → ( ψ → φ )",
        s1,
        s2,
        ref="luklem1",
        note="luklem1",
    )

    return lb.build(res)


def prove_mpdi(sys: System) -> Proof:
    """mpdi: φ → (ψ → θ). Hyp1: ψ → χ, Hyp2: φ → (ψ → (χ → θ)).

    A nested modus ponens deduction.
    (Contributed by NM, 16-Apr-2005.)
    (Proof shortened by Mel L. O'Cat, 15-Jan-2008.)
    set.mm proof: a1i mpdd.
    """
    lb = ProofBuilder(sys, "mpdi")
    h1 = lb.hyp("mpdi.1", "( ψ → χ )")
    h2 = lb.hyp("mpdi.2", "( φ → ( ψ → ( χ → θ ) ) )")
    s1 = lb.ref("s1", "( φ → ( ψ → χ ) )", h1, ref="a1i", note="a1i")
    res = lb.ref("res", "( φ → ( ψ → θ ) )", s1, h2, ref="mpdd", note="mpdd")
    return lb.build(res)


def prove_pm2_43d(sys: System) -> Proof:
    """pm2.43d: φ → (ψ → χ). Hyp: φ → (ψ → (ψ → χ)).

    Deduction absorbing redundant antecedent.
    (Contributed by NM, 18-Aug-1993.)
    set.mm proof: id mpdi.
    """
    lb = ProofBuilder(sys, "pm2.43d")
    h1 = lb.hyp("pm2.43d.1", "( φ → ( ψ → ( ψ → χ ) ) )")
    s_id = lb.ref("s_id", "( ψ → ψ )", ref="id", note="id")
    res = lb.ref("res", "( φ → ( ψ → χ ) )", s_id, h1, ref="mpdi", note="mpdi")
    return lb.build(res)


def prove_pm2_43i(sys: System) -> Proof:
    """pm2.43i: φ → ψ.  Hyp: φ → (φ → ψ).

    Inference absorbing redundant antecedent.  Associated with pm2.43.
    (Contributed by NM, 10-Jan-1993.)
    set.mm proof: id mpd.
    """
    lb = ProofBuilder(sys, "pm2.43i")
    h1 = lb.hyp("pm2.43i.1", "( φ → ( φ → ψ ) )")
    s1 = lb.ref("s1", "( φ → φ )", ref="id", note="id")
    res = lb.ref("res", "( φ → ψ )", s1, h1, ref="mpd", note="mpd")
    return lb.build(res)


def prove_pm2_43a(sys: System) -> Proof:
    """pm2.43a: ψ → (φ → χ). Hyp: ψ → (φ → (ψ → χ)).

    Associated with pm2.43.  (Contributed by NM, 30-Sep-1992.)
    set.mm proof: id mpid.
    """
    lb = ProofBuilder(sys, "pm2.43a")
    h1 = lb.hyp("pm2.43a.1", "( ψ → ( φ → ( ψ → χ ) ) )")
    s1 = lb.ref("s1", "( ψ → ψ )", ref="id", note="id")
    res = lb.ref("res", "( ψ → ( φ → χ ) )", s1, h1, ref="mpid", note="mpid")
    return lb.build(res)


def prove_pm2_43b(sys: System) -> Proof:
    """pm2.43b: ( φ → ( ψ → χ ) ). Hyp: ( ψ → ( φ → ( ψ → χ ) ) ).

    Inference associated with pm2.43a.  Swap antecedents of its conclusion
    via com12.  (Contributed by NM, 30-Sep-1992.)
    set.mm proof: pm2.43a com12.
    """
    lb = ProofBuilder(sys, "pm2.43b")
    h1 = lb.hyp("pm2.43b.1", "( ψ → ( φ → ( ψ → χ ) ) )")
    s1 = lb.ref("s1", "( ψ → ( φ → χ ) )", h1, ref="pm2.43a", note="pm2.43a")
    res = lb.ref("res", "( φ → ( ψ → χ ) )", s1, ref="com12", note="com12")
    return lb.build(res)


def prove_syld(sys: System) -> Proof:
    """syld: φ → (ψ → θ). Hyp: φ → (ψ → χ), φ → (χ → θ). (Contributed by NM, 5-Aug-1993.)"""
    lb = ProofBuilder(sys, "syld")
    h1 = lb.hyp("syld.1", "φ → ( ψ → χ )")
    h2 = lb.hyp("syld.2", "φ → ( χ → θ )")
    s1 = lb.ref("s1", "φ → ( ψ → ( χ → θ ) )", h2, ref="a1d", note="a1d")
    res = lb.ref("res", "φ → ( ψ → θ )", h1, s1, ref="mpdd", note="mpdd")
    return lb.build(res)


def prove_syldc(sys: System) -> Proof:
    """syldc: ψ → (φ → θ). Hyp: φ → (ψ → χ), φ → (χ → θ).

    Inference commuting the antecedents of a syllogism deduction.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "syldc")
    h1 = lb.hyp("syldc.1", "φ → ( ψ → χ )")
    h2 = lb.hyp("syldc.2", "φ → ( χ → θ )")
    s1 = lb.ref("s1", "φ → ( ψ → θ )", h1, h2, ref="syld", note="syld")
    res = lb.ref("res", "ψ → ( φ → θ )", s1, ref="com12", note="com12")
    return lb.build(res)


def prove_syldd(sys: System) -> Proof:
    """syldd: φ → ( ψ → ( χ → τ ) ). Hyp: φ → ( ψ → ( χ → θ ) ), φ → ( ψ → ( θ → τ ) ).

    Nested syllogism deduction.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "syldd")
    h1 = lb.hyp("syldd.1", "φ → ( ψ → ( χ → θ ) )")
    h2 = lb.hyp("syldd.2", "φ → ( ψ → ( θ → τ ) )")
    s1 = lb.ref("s1", "( θ → τ ) → ( ( χ → θ ) → ( χ → τ ) )", ref="imim2", note="imim2")
    res = lb.ref("res", "φ → ( ψ → ( χ → τ ) )", h2, h1, s1, ref="syl6c", note="syl6c")
    return lb.build(res)


def prove_3syld(sys: System) -> Proof:
    """3syld: φ → ( ψ → τ ).

    Hyp 1: φ → ( ψ → χ )
    Hyp 2: φ → ( χ → θ )
    Hyp 3: φ → ( θ → τ )
    Concl: φ → ( ψ → τ )

    Nested syllogism deduction.
    (Contributed by NM, 20-Aug-2001.)
    """
    lb = ProofBuilder(sys, "3syld")
    h1 = lb.hyp("3syld.1", "φ → ( ψ → χ )")
    h2 = lb.hyp("3syld.2", "φ → ( χ → θ )")
    h3 = lb.hyp("3syld.3", "φ → ( θ → τ )")
    s1 = lb.ref("s1", "φ → ( ψ → θ )", h1, h2, ref="syld", note="syld 3syld.1, 3syld.2")
    res = lb.ref("res", "φ → ( ψ → τ )", s1, h3, ref="syld", note="syld s1, 3syld.3")
    return lb.build(res)


def prove_sylsyld(sys: System) -> Proof:
    """sylsyld: φ → (χ → τ).

    Hyp 1: φ → ψ
    Hyp 2: φ → (χ → θ)
    Hyp 3: ψ → (θ → τ)
    Concl: φ → (χ → τ)

    Nested syllogism deduction.
    (Contributed by NM, 26-Mar-1995.)
    """
    lb = ProofBuilder(sys, "sylsyld")
    h1 = lb.hyp("sylsyld.1", "φ → ψ")
    h2 = lb.hyp("sylsyld.2", "φ → ( χ → θ )")
    h3 = lb.hyp("sylsyld.3", "ψ → ( θ → τ )")
    s1 = lb.ref("s1", "φ → ( θ → τ )", h1, h3, ref="syl", note="syl sylsyld.1, sylsyld.3")
    res = lb.ref("res", "φ → ( χ → τ )", h2, s1, ref="syld", note="syld sylsyld.2, s1")
    return lb.build(res)


def prove_sylc(sys: System) -> Proof:
    """sylc: φ → θ.  Hyp: φ → ψ, φ → χ, ψ → (χ → θ).

    Inference combining syl2im with pm2.43i.
    (Contributed by NM, 12-Dec-1993.)
    set.mm proof: syl2im pm2.43i.
    """
    lb = ProofBuilder(sys, "sylc")
    h1 = lb.hyp("sylc.1", "φ → ψ")
    h2 = lb.hyp("sylc.2", "φ → χ")
    h3 = lb.hyp("sylc.3", "ψ → ( χ → θ )")
    s1 = lb.ref("s1", "φ → ( φ → θ )", h1, h2, h3, ref="syl2im", note="syl2im")
    res = lb.ref("res", "φ → θ", s1, ref="pm2.43i", note="pm2.43i")
    return lb.build(res)


def prove_syl3c(sys: System) -> Proof:
    """syl3c: φ → τ.  Hyp: φ → ψ, φ → χ, φ → θ, ψ → (χ → (θ → τ)).

    Syllogism inference combined with contraction.
    (Contributed by NM, 25-Mar-2015.)
    set.mm proof: sylc mpd.
    """
    lb = ProofBuilder(sys, "syl3c")
    h1 = lb.hyp("syl3c.1", "φ → ψ")
    h2 = lb.hyp("syl3c.2", "φ → χ")
    h3 = lb.hyp("syl3c.3", "φ → θ")
    h4 = lb.hyp("syl3c.4", "ψ → ( χ → ( θ → τ ) )")
    s1 = lb.ref("s1", "φ → ( θ → τ )", h1, h2, h4, ref="sylc", note="sylc")
    res = lb.ref("res", "φ → τ", h3, s1, ref="mpd", note="mpd")
    return lb.build(res)


def prove_syl2anc(sys: System) -> Proof:
    r"""syl2anc: ph -> th.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ( ps /\ ch ) -> th
    Concl: ph -> th

    Syllogism inference combined with two antecedents.
    (Contributed by NM, 1-Jan-2013.)
    set.mm proof: ex sylc.
    """
    lb = ProofBuilder(sys, "syl2anc")
    h1 = lb.hyp("syl2anc.1", "ph -> ps")
    h2 = lb.hyp("syl2anc.2", "ph -> ch")
    h3 = lb.hyp("syl2anc.3", r"( ps /\ ch ) -> th")
    s1 = lb.ref("s1", "ps -> ( ch -> th )", h3, ref="ex", note="ex")
    res = lb.ref("res", "ph -> th", h1, h2, s1, ref="sylc", note="sylc")
    return lb.build(res)


def prove_syl2anc2(sys: System) -> Proof:
    r"""syl2anc2: ph -> th.

    Hyp 1: ph -> ps
    Hyp 2: ps -> ch
    Hyp 3: ( ps /\ ch ) -> th
    Concl: ph -> th

    Syllogism inference combined with two antecedents (chained form).
    (Contributed by NM, 1-Jan-2013.)
    set.mm proof: syl syl2anc.
    """
    lb = ProofBuilder(sys, "syl2anc2")
    h1 = lb.hyp("syl2anc2.1", "ph -> ps")
    h2 = lb.hyp("syl2anc2.2", "ps -> ch")
    h3 = lb.hyp("syl2anc2.3", r"( ps /\ ch ) -> th")
    s1 = lb.ref("s1", "ph -> ch", h1, h2, ref="syl", note="syl syl2anc2.1, syl2anc2.2")
    res = lb.ref(
        "res", "ph -> th", h1, s1, h3, ref="syl2anc", note="syl2anc syl2anc2.1, s1, syl2anc2.3"
    )
    return lb.build(res)


def prove_syl12anc(sys: System) -> Proof:
    r"""syl12anc: ph -> ta.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ( ps /\ ( ch /\ th ) ) -> ta
    Concl: ph -> ta

    Syllogism inference combined with two antecedents and a conjunctive
    antecedent.  (Contributed by NM, 1-Jan-2013.)
    set.mm proof: wa jca syl2anc.
    """
    lb = ProofBuilder(sys, "syl12anc")
    h1 = lb.hyp("syl12anc.1", "ph -> ps")
    h2 = lb.hyp("syl12anc.2", "ph -> ch")
    h3 = lb.hyp("syl12anc.3", "ph -> th")
    h4 = lb.hyp("syl12anc.4", r"( ps /\ ( ch /\ th ) ) -> ta")
    s1 = lb.ref(
        "s1",
        r"( ph -> ( ch /\ th ) )",
        h2,
        h3,
        ref="jca",
        note="jca syl12anc.2, syl12anc.3",
    )
    res = lb.ref(
        "res",
        "ph -> ta",
        h1,
        s1,
        h4,
        ref="syl2anc",
        note="syl2anc syl12anc.1, s1, syl12anc.4",
    )
    return lb.build(res)


def prove_syl21anc(sys: System) -> Proof:
    r"""syl21anc: ph -> ta.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ( ( ps /\ ch ) /\ th ) -> ta
    Concl: ph -> ta

    Syllogism combined with two antecedents and a conjunctive
    antecedent.  (Contributed by NM, 1-Jan-2013.)
    set.mm proof: wa jca syl2anc.
    """
    lb = ProofBuilder(sys, "syl21anc")
    h1 = lb.hyp("syl21anc.1", "ph -> ps")
    h2 = lb.hyp("syl21anc.2", "ph -> ch")
    h3 = lb.hyp("syl21anc.3", "ph -> th")
    h4 = lb.hyp("syl21anc.4", r"( ( ps /\ ch ) /\ th ) -> ta")
    s1 = lb.ref(
        "s1",
        r"( ph -> ( ps /\ ch ) )",
        h1,
        h2,
        ref="jca",
        note="jca syl21anc.1, syl21anc.2",
    )
    res = lb.ref(
        "res",
        "ph -> ta",
        s1,
        h3,
        h4,
        ref="syl2anc",
        note="syl2anc s1, syl21anc.3, syl21anc.4",
    )
    return lb.build(res)


def prove_syl211anc(sys: System) -> Proof:
    r"""syl211anc: ph -> et.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ph -> ta
    Hyp 5: ( ( ps /\ ch ) /\ th /\ ta ) -> et
    Concl: ph -> et

    Syllogism combined with two conjunctive antecedents, one antecedent,
    and one antecedent.  (Contributed by NM, 1-Jan-2013.)
    set.mm proof: wa jca syl3anc.
    """
    lb = ProofBuilder(sys, "syl211anc")
    h1 = lb.hyp("syl3anc.1", "ph -> ps")
    h2 = lb.hyp("syl3anc.2", "ph -> ch")
    h3 = lb.hyp("syl3anc.3", "ph -> th")
    h4 = lb.hyp("syl3Xanc.4", "ph -> ta")
    h5 = lb.hyp("syl211anc.5", r"( ( ps /\ ch ) /\ th /\ ta ) -> et")
    s1 = lb.ref(
        "s1",
        r"ph -> ( ps /\ ch )",
        h1,
        h2,
        ref="jca",
        note="jca syl3anc.1, syl3anc.2",
    )
    res = lb.ref(
        "res",
        "ph -> et",
        s1,
        h3,
        h4,
        h5,
        ref="syl3anc",
        note="syl3anc s1, syl3anc.3, syl3Xanc.4, syl211anc.5",
    )
    return lb.build(res)


def prove_syl212anc(sys: System) -> Proof:
    r"""syl212anc: ph -> ze.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ph -> ta
    Hyp 5: ph -> et
    Hyp 6: ( ( ps /\ ch ) /\ th /\ ( ta /\ et ) ) -> ze
    Concl: ph -> ze

    Syllogism combined with two conjunctive antecedents, one antecedent,
    and two conjunctive antecedents.  (Contributed by NM, 3-Apr-2013.)
    set.mm proof: wa jca syl211anc.
    """
    lb = ProofBuilder(sys, "syl212anc")
    h1 = lb.hyp("syl3anc.1", "ph -> ps")
    h2 = lb.hyp("syl3anc.2", "ph -> ch")
    h3 = lb.hyp("syl3anc.3", "ph -> th")
    h4 = lb.hyp("syl3Xanc.4", "ph -> ta")
    h5 = lb.hyp("syl23anc.5", "ph -> et")
    h6 = lb.hyp("syl212anc.6", r"( ( ps /\ ch ) /\ th /\ ( ta /\ et ) ) -> ze")
    s1 = lb.ref(
        "s1",
        r"ph -> ( ta /\ et )",
        h4,
        h5,
        ref="jca",
        note="jca syl3Xanc.4, syl23anc.5",
    )
    res = lb.ref(
        "res",
        "ph -> ze",
        h1,
        h2,
        h3,
        s1,
        h6,
        ref="syl211anc",
        note="syl211anc syl3anc.1, syl3anc.2, syl3anc.3, s1, syl212anc.6",
    )
    return lb.build(res)


def prove_syl213anc(sys: System) -> Proof:
    r"""syl213anc: ph -> si.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ph -> ta
    Hyp 5: ph -> et
    Hyp 6: ph -> ze
    Hyp 7: ( ( ps /\ ch ) /\ th /\ ( ta /\ et /\ ze ) ) -> si
    Concl: ph -> si

    Syllogism combined with two conjunctive antecedents, one antecedent,
    and three conjunctive antecedents.  (Contributed by NM, 1-Jan-2013.)
    set.mm proof: wa jca syl113anc.
    """
    lb = ProofBuilder(sys, "syl213anc")
    h1 = lb.hyp("syl3anc.1", "ph -> ps")
    h2 = lb.hyp("syl3anc.2", "ph -> ch")
    h3 = lb.hyp("syl3anc.3", "ph -> th")
    h4 = lb.hyp("syl3Xanc.4", "ph -> ta")
    h5 = lb.hyp("syl23anc.5", "ph -> et")
    h6 = lb.hyp("syl33anc.6", "ph -> ze")
    h7 = lb.hyp("syl213anc.7", r"( ( ps /\ ch ) /\ th /\ ( ta /\ et /\ ze ) ) -> si")
    s1 = lb.ref(
        "s1",
        r"ph -> ( ps /\ ch )",
        h1,
        h2,
        ref="jca",
        note="jca syl3anc.1, syl3anc.2",
    )
    res = lb.ref(
        "res",
        "ph -> si",
        s1,
        h3,
        h4,
        h5,
        h6,
        h7,
        ref="syl113anc",
        note="syl113anc s1, syl3anc.3, syl3Xanc.4, syl23anc.5, syl33anc.6, syl213anc.7",
    )
    return lb.build(res)


def prove_syl22anc(sys: System) -> Proof:
    r"""syl22anc: ph -> et.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ph -> ta
    Hyp 5: ( ( ps /\ ch ) /\ ( th /\ ta ) ) -> et
    Concl: ph -> et

    Syllogism combined with contraction.
    (Contributed by NM, 11-Mar-2012.)
    set.mm proof: wa jca syl12anc.
    """
    lb = ProofBuilder(sys, "syl22anc")
    h1 = lb.hyp("syl12anc.1", "ph -> ps")
    h2 = lb.hyp("syl12anc.2", "ph -> ch")
    h3 = lb.hyp("syl12anc.3", "ph -> th")
    h4 = lb.hyp("syl22anc.4", "ph -> ta")
    h5 = lb.hyp("syl22anc.5", r"( ( ps /\ ch ) /\ ( th /\ ta ) ) -> et")
    s1 = lb.ref(
        "s1",
        r"( ph -> ( ps /\ ch ) )",
        h1,
        h2,
        ref="jca",
        note="jca syl12anc.1, syl12anc.2",
    )
    res = lb.ref(
        "res",
        "ph -> et",
        s1,
        h3,
        h4,
        h5,
        ref="syl12anc",
        note="syl12anc s1, syl12anc.3, syl22anc.4, syl22anc.5",
    )
    return lb.build(res)


def prove_syl13anc(sys: System) -> Proof:
    r"""syl13anc: ph -> et.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ph -> ta
    Hyp 5: ( ps /\ ( ch /\ th /\ ta ) ) -> et
    Concl: ph -> et

    Syllogism inference combined with three antecedents in conjunctive form.
    (Contributed by NM, 1-Jan-2013.)
    set.mm proof: w3a 3jca syl2anc.
    """
    lb = ProofBuilder(sys, "syl13anc")
    h1 = lb.hyp("syl13anc.1", "ph -> ps")
    h2 = lb.hyp("syl13anc.2", "ph -> ch")
    h3 = lb.hyp("syl13anc.3", "ph -> th")
    h4 = lb.hyp("syl13anc.4", "ph -> ta")
    h5 = lb.hyp("syl13anc.5", r"( ps /\ ( ch /\ th /\ ta ) ) -> et")
    s1 = lb.ref(
        "s1",
        r"( ph -> ( ch /\ th /\ ta ) )",
        h2,
        h3,
        h4,
        ref="3jca",
        note="3jca syl13anc.2, syl13anc.3, syl13anc.4",
    )
    res = lb.ref(
        "res",
        "ph -> et",
        h1,
        s1,
        h5,
        ref="syl2anc",
        note="syl2anc syl13anc.1, s1, syl13anc.5",
    )
    return lb.build(res)


def prove_syl131anc(sys: System) -> Proof:
    r"""syl131anc: ph -> ze.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ph -> ta
    Hyp 5: ph -> et
    Hyp 6: ( ps /\ ( ch /\ th /\ ta ) /\ et ) -> ze
    Concl: ph -> ze

    Syllogism inference combined with one, three, and one antecedents in
    conjunctive form.  (Contributed by NM, 1-Jan-2013.)
    set.mm proof: w3a 3jca syl3anc.
    """
    lb = ProofBuilder(sys, "syl131anc")
    h1 = lb.hyp("syl3anc.1", "ph -> ps")
    h2 = lb.hyp("syl3anc.2", "ph -> ch")
    h3 = lb.hyp("syl3anc.3", "ph -> th")
    h4 = lb.hyp("syl3Xanc.4", "ph -> ta")
    h5 = lb.hyp("syl23anc.5", "ph -> et")
    h6 = lb.hyp("syl131anc.6", r"( ps /\ ( ch /\ th /\ ta ) /\ et ) -> ze")
    s1 = lb.ref(
        "s1",
        r"ph -> ( ch /\ th /\ ta )",
        h2,
        h3,
        h4,
        ref="3jca",
        note="3jca syl3anc.2, syl3anc.3, syl3Xanc.4",
    )
    res = lb.ref(
        "res",
        "ph -> ze",
        h1,
        s1,
        h5,
        h6,
        ref="syl3anc",
        note="syl3anc syl3anc.1, s1, syl23anc.5, syl131anc.6",
    )
    return lb.build(res)


def prove_syl132anc(sys: System) -> Proof:
    r"""syl132anc: ph -> si.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ph -> ta
    Hyp 5: ph -> et
    Hyp 6: ph -> ze
    Hyp 7: ( ps /\ ( ch /\ th /\ ta ) /\ ( et /\ ze ) ) -> si
    Concl: ph -> si

    Syllogism inference combined with one, three, and two antecedents in
    conjunctive form.  (Contributed by NM, 1-Jan-2013.)
    set.mm proof: wa jca syl131anc.
    """
    lb = ProofBuilder(sys, "syl132anc")
    h1 = lb.hyp("syl3anc.1", "ph -> ps")
    h2 = lb.hyp("syl3anc.2", "ph -> ch")
    h3 = lb.hyp("syl3anc.3", "ph -> th")
    h4 = lb.hyp("syl3Xanc.4", "ph -> ta")
    h5 = lb.hyp("syl23anc.5", "ph -> et")
    h6 = lb.hyp("syl33anc.6", "ph -> ze")
    h7 = lb.hyp("syl132anc.7", r"( ps /\ ( ch /\ th /\ ta ) /\ ( et /\ ze ) ) -> si")
    s1 = lb.ref(
        "s1",
        r"ph -> ( et /\ ze )",
        h5,
        h6,
        ref="jca",
        note="jca syl23anc.5, syl33anc.6",
    )
    res = lb.ref(
        "res",
        "ph -> si",
        h1,
        h2,
        h3,
        h4,
        s1,
        h7,
        ref="syl131anc",
        note="syl131anc syl3anc.1, syl3anc.2, syl3anc.3, syl3Xanc.4, s1, syl132anc.7",
    )
    return lb.build(res)


def prove_syl133anc(sys: System) -> Proof:
    r"""syl133anc: ph -> rh.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ph -> ta
    Hyp 5: ph -> et
    Hyp 6: ph -> ze
    Hyp 7: ph -> si
    Hyp 8: ( ps /\ ( ch /\ th /\ ta ) /\ ( et /\ ze /\ si ) ) -> rh
    Concl: ph -> rh

    Syllogism inference combined with one, three, and three antecedents in
    conjunctive form.  (Contributed by NM, 1-Jan-2013.)
    set.mm proof: w3a 3jca syl131anc.
    """
    lb = ProofBuilder(sys, "syl133anc")
    h1 = lb.hyp("syl3anc.1", "ph -> ps")
    h2 = lb.hyp("syl3anc.2", "ph -> ch")
    h3 = lb.hyp("syl3anc.3", "ph -> th")
    h4 = lb.hyp("syl3Xanc.4", "ph -> ta")
    h5 = lb.hyp("syl23anc.5", "ph -> et")
    h6 = lb.hyp("syl33anc.6", "ph -> ze")
    h7 = lb.hyp("syl133anc.7", "ph -> si")
    h8 = lb.hyp("syl133anc.8", r"( ps /\ ( ch /\ th /\ ta ) /\ ( et /\ ze /\ si ) ) -> rh")
    s1 = lb.ref(
        "s1",
        r"ph -> ( et /\ ze /\ si )",
        h5,
        h6,
        h7,
        ref="3jca",
        note="3jca syl23anc.5, syl33anc.6, syl133anc.7",
    )
    res = lb.ref(
        "res",
        "ph -> rh",
        h1,
        h2,
        h3,
        h4,
        s1,
        h8,
        ref="syl131anc",
        note="syl131anc syl3anc.1, syl3anc.2, syl3anc.3, syl3Xanc.4, s1, syl133anc.8",
    )
    return lb.build(res)


def prove_sylancr(sys: System) -> Proof:
    r"""sylancr: ph -> th.

    Hyp 1: ps
    Hyp 2: ph -> ch
    Hyp 3: ( ps /\ ch ) -> th
    Concl: ph -> th

    Syllogism inference combined with a constant antecedent.
    (Contributed by NM, 1-Jan-2013.)
    set.mm proof: a1i syl2anc.
    """
    lb = ProofBuilder(sys, "sylancr")
    h1 = lb.hyp("sylancr.1", "ps")
    h2 = lb.hyp("sylancr.2", "ph -> ch")
    h3 = lb.hyp("sylancr.3", r"( ps /\ ch ) -> th")
    s1 = lb.ref("s1", "ph -> ps", h1, ref="a1i", note="a1i sylancr.1")
    res = lb.ref(
        "res", "ph -> th", s1, h2, h3, ref="syl2anc", note="syl2anc s1, sylancr.2, sylancr.3"
    )
    return lb.build(res)


def prove_sylancl(sys: System) -> Proof:
    r"""sylancl: ph -> th.

    Hyp 1: ph -> ps
    Hyp 2: ch
    Hyp 3: ( ps /\ ch ) -> th
    Concl: ph -> th

    Syllogism inference combined with a constant consequent.
    (Contributed by NM, 1-Jan-2013.)
    set.mm proof: a1i syl2anc.
    """
    lb = ProofBuilder(sys, "sylancl")
    h1 = lb.hyp("sylancl.1", "ph -> ps")
    h2 = lb.hyp("sylancl.2", "ch")
    h3 = lb.hyp("sylancl.3", r"( ps /\ ch ) -> th")
    s1 = lb.ref("s1", "ph -> ch", h2, ref="a1i", note="a1i sylancl.2")
    res = lb.ref(
        "res", "ph -> th", h1, s1, h3, ref="syl2anc", note="syl2anc sylancl.1, s1, sylancl.3"
    )
    return lb.build(res)


def prove_sylanblc(sys: System) -> Proof:
    r"""sylanblc: ph -> th.

    Hyp 1: ph -> ps
    Hyp 2: ch
    Hyp 3: ( ( ps /\ ch ) <-> th )
    Concl: ph -> th

    Syllogism inference combined with a constant consequent and a
    biconditional rather than an implication.
    (Contributed by NM, 1-Jan-1993.)
    set.mm proof: wa biimpi sylancl.
    """
    lb = ProofBuilder(sys, "sylanblc")
    h1 = lb.hyp("sylanblc.1", "ph -> ps")
    h2 = lb.hyp("sylanblc.2", "ch")
    h3 = lb.hyp("sylanblc.3", r"( ( ps /\ ch ) <-> th )")
    s1 = lb.ref(
        "s1",
        r"( ps /\ ch ) -> th",
        h3,
        ref="biimpi",
        note="biimpi sylanblc.3",
    )
    res = lb.ref(
        "res",
        "ph -> th",
        h1,
        h2,
        s1,
        ref="sylancl",
        note="sylancl sylanblc.1, sylanblc.2, s1",
    )
    return lb.build(res)


def prove_mpdan(sys: System) -> Proof:
    r"""mpdan: ph -> ch.

    Hyp 1: ph -> ps
    Hyp 2: ( ph /\ ps ) -> ch
    Concl: ph -> ch

    A modus ponens deduction with an antecedent expressed as a conjunction.
    (Contributed by NM, 30-Sep-1992.)
    set.mm proof: id syl2anc.
    """
    lb = ProofBuilder(sys, "mpdan")
    h1 = lb.hyp("mpdan.1", "ph -> ps")
    h2 = lb.hyp("mpdan.2", r"( ph /\ ps ) -> ch")
    s1 = lb.ref("s1", "ph -> ph", ref="id", note="id")
    res = lb.ref("res", "ph -> ch", s1, h1, h2, ref="syl2anc", note="syl2anc")
    return lb.build(res)


def prove_mpidan(sys: System) -> Proof:
    r"""mpidan: ( ( φ ∧ ψ ) → θ ).

    Hyp 1: φ → χ
    Hyp 2: ( ( φ ∧ ψ ) ∧ χ ) → θ
    Concl: ( φ ∧ ψ ) → θ

    A modus ponens deduction with a nested conjunction antecedent.
    (Contributed by NM, 30-Sep-1992.)
    set.mm proof: wa adantr mpdan.
    """
    lb = ProofBuilder(sys, "mpidan")
    h1 = lb.hyp("mpidan.1", "φ → χ")
    h2 = lb.hyp("mpidan.2", "( ( φ ∧ ψ ) ∧ χ ) → θ")
    s1 = lb.ref("s1", "( φ ∧ ψ ) → χ", h1, ref="adantr", note="adantr mpidan.1")
    res = lb.ref("res", "( φ ∧ ψ ) → θ", s1, h2, ref="mpdan", note="mpdan s1, mpidan.2")
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


def prove_mp2d(sys: System) -> Proof:
    """mp2d: φ → θ.

    Hyp 1: φ → ψ
    Hyp 2: φ → χ
    Hyp 3: φ → ( ψ → ( χ → θ ) )
    Concl: φ → θ

    A double modus ponens deduction.
    (Contributed by NM, 23-May-2013.)
    """
    lb = ProofBuilder(sys, "mp2d")
    h1 = lb.hyp("mp2d.1", "φ → ψ")
    h2 = lb.hyp("mp2d.2", "φ → χ")
    h3 = lb.hyp("mp2d.3", "φ → ( ψ → ( χ → θ ) )")
    s1 = lb.ref("s1", "φ → ( ψ → θ )", h2, h3, ref="mpid", note="mpid")
    res = lb.ref("res", "φ → θ", h1, s1, ref="mpd", note="mpd")
    return lb.build(res)


def prove_mp2and(sys: System) -> Proof:
    """mp2and: φ → θ.

    Hyp 1: φ → ψ
    Hyp 2: φ → χ
    Hyp 3: φ → ( ( ψ ∧ χ ) → θ )
    Concl: φ → θ

    A double modus ponens with an antecedent as a conjunction.
    (Contributed by NM, 13-Apr-1996.)
    """
    lb = ProofBuilder(sys, "mp2and")
    h1 = lb.hyp("mp2and.1", "φ → ψ")
    h2 = lb.hyp("mp2and.2", "φ → χ")
    h3 = lb.hyp("mp2and.3", "φ → ( ( ψ ∧ χ ) → θ )")
    s1 = lb.ref("s1", "φ → ( χ → θ )", h1, h3, ref="mpand", note="mpand mp2and.1, mp2and.3")
    res = lb.ref("res", "φ → θ", h2, s1, ref="mpd", note="mpd mp2and.2, s1")

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


def prove_mpancom(sys: System) -> Proof:
    r"""mpancom: ps -> ch.

    Hyp 1: ps -> ph
    Hyp 2: ( ph /\ ps ) -> ch
    Concl: ps -> ch

    Inference eliminating a conjunct from an antecedent when the other conjunct
    implies it.  (Contributed by NM, 30-Sep-1992.)
    set.mm proof: id syl2anc.
    """
    lb = ProofBuilder(sys, "mpancom")
    h1 = lb.hyp("mpancom.1", "ps -> ph")
    h2 = lb.hyp("mpancom.2", r"( ph /\ ps ) -> ch")
    s1 = lb.ref("s1", "ps -> ps", ref="id", note="id")
    res = lb.ref("res", "ps -> ch", h1, s1, h2, ref="syl2anc", note="syl2anc")

    return lb.build(res)


def prove_mpan(sys: System) -> Proof:
    r"""mpan: ps -> ch.

    Hyp 1: ph
    Hyp 2: ( ph /\ ps ) -> ch
    Concl: ps -> ch

    Modus ponens with an antecedent.  (Contributed by NM, 29-Dec-1992.)
    set.mm proof: a1i mpancom.
    """
    lb = ProofBuilder(sys, "mpan")
    h1 = lb.hyp("mpan.1", "ph")
    h2 = lb.hyp("mpan.2", r"( ph /\ ps ) -> ch")
    s1 = lb.ref("s1", "ps -> ph", h1, ref="a1i", note="a1i mpan.1")
    res = lb.ref("res", "ps -> ch", s1, h2, ref="mpancom", note="mpancom s1, mpan.2")
    return lb.build(res)


def prove_mpand(sys: System) -> Proof:
    r"""mpand: ph -> ( ch -> th ).

    Hyp 1: ph -> ps
    Hyp 2: ph -> ( ( ps /\ ch ) -> th )
    Concl: ph -> ( ch -> th )

    Deduction form of mpan.  (Contributed by NM, 10-Aug-2015.)
    set.mm proof: ancomsd mpan2d.
    """
    lb = ProofBuilder(sys, "mpand")
    h1 = lb.hyp("mpand.1", "ph -> ps")
    h2 = lb.hyp("mpand.2", r"ph -> ( ( ps /\ ch ) -> th )")
    s1 = lb.ref(
        "s1",
        r"ph -> ( ( ch /\ ps ) -> th )",
        h2,
        ref="ancomsd",
        note="ancomsd mpand.2",
    )
    res = lb.ref(
        "res",
        "ph -> ( ch -> th )",
        h1,
        s1,
        ref="mpan2d",
        note="mpan2d mpand.1, s1",
    )

    return lb.build(res)


def prove_mpani(sys: System) -> Proof:
    """mpani: φ → (χ → θ).

    Hyp 1: ψ
    Hyp 2: φ → ((ψ ∧ χ) → θ)
    Concl: φ → (χ → θ)

    Inference form of mpand.  (Contributed by NM, 10-Aug-2015.)
    set.mm proof: a1i mpand.
    """
    lb = ProofBuilder(sys, "mpani")
    h1 = lb.hyp("mpani.1", "ψ")
    h2 = lb.hyp("mpani.2", "φ → ((ψ ∧ χ) → θ)")
    s1 = lb.ref("s1", "φ → ψ", h1, ref="a1i", note="a1i mpani.1")
    res = lb.ref("res", "φ → (χ → θ)", s1, h2, ref="mpand", note="mpand s1, mpani.2")
    return lb.build(res)


def prove_mpan2(sys: System) -> Proof:
    r"""mpan2: ph -> ch.

    Hyp 1: ps
    Hyp 2: ( ph /\ ps ) -> ch
    Concl: ph -> ch

    Modus ponens with an antecedent as the second conjunct.
    (Contributed by NM, 29-Dec-1992.)
    set.mm proof: a1i mpdan.
    """
    lb = ProofBuilder(sys, "mpan2")
    h1 = lb.hyp("mpan2.1", "ps")
    h2 = lb.hyp("mpan2.2", r"( ph /\ ps ) -> ch")
    s1 = lb.ref("s1", "ph -> ps", h1, ref="a1i", note="a1i mpan2.1")
    res = lb.ref("res", "ph -> ch", s1, h2, ref="mpdan", note="mpdan s1, mpan2.2")
    return lb.build(res)


def prove_mpan2d(sys: System) -> Proof:
    r"""mpan2d: ph -> ( ps -> th ).

    Hyp 1: ph -> ch
    Hyp 2: ph -> ( ( ps /\ ch ) -> th )
    Concl: ph -> ( ps -> th )

    Deduction form of mpan2.  (Contributed by NM, 14-Dec-2004.)
    set.mm proof: expd mpid.
    """
    lb = ProofBuilder(sys, "mpan2d")
    h1 = lb.hyp("mpan2d.1", "ph -> ch")
    h2 = lb.hyp("mpan2d.2", r"ph -> ( ( ps /\ ch ) -> th )")
    s1 = lb.ref(
        "s1",
        "ph -> ( ps -> ( ch -> th ) )",
        h2,
        ref="expd",
        note="expd mpan2d.2",
    )
    res = lb.ref(
        "res",
        "ph -> ( ps -> th )",
        h1,
        s1,
        ref="mpid",
        note="mpid mpan2d.1, s1",
    )
    return lb.build(res)


def prove_mpan2i(sys: System) -> Proof:
    r"""mpan2i: ph -> ( ps -> th ).

    Hyp 1: ch
    Hyp 2: ph -> ( ( ps /\ ch ) -> th )
    Concl: ph -> ( ps -> th )

    Inference form of mpan2d.  (Contributed by NM, 10-Aug-2015.)
    set.mm proof: a1i mpan2d.
    """
    lb = ProofBuilder(sys, "mpan2i")
    h1 = lb.hyp("mpan2i.1", "ch")
    h2 = lb.hyp("mpan2i.2", r"ph -> ( ( ps /\ ch ) -> th )")
    s1 = lb.ref("s1", "ph -> ch", h1, ref="a1i", note="a1i mpan2i.1")
    res = lb.ref(
        "res",
        "ph -> ( ps -> th )",
        s1,
        h2,
        ref="mpan2d",
        note="mpan2d s1, mpan2i.2",
    )
    return lb.build(res)


def prove_mp2an(sys: System) -> Proof:
    r"""mp2an: ch.

    Hyp 1: ph
    Hyp 2: ps
    Hyp 3: ( ph /\ ps ) -> ch
    Concl: ch

    Double modus ponens with an antecedent.  (Contributed by NM, 29-Dec-1992.)
    set.mm proof: mpan ax-mp.
    """
    lb = ProofBuilder(sys, "mp2an")
    h1 = lb.hyp("mp2an.1", "ph")
    h2 = lb.hyp("mp2an.2", "ps")
    h3 = lb.hyp("mp2an.3", r"( ph /\ ps ) -> ch")
    s1 = lb.ref("s1", "ps -> ch", h1, h3, ref="mpan", note="mpan mp2an.1, mp2an.3")
    res = lb.mp("res", h2, s1, note="ax-mp mp2an.2, s1")
    return lb.build(res)


def prove_mp2ani(sys: System) -> Proof:
    """mp2ani: φ → θ.

    Hyp 1: ψ
    Hyp 2: χ
    Hyp 3: φ → ((ψ ∧ χ) → θ)
    Concl: φ → θ

    Inference form of mp2and.
    """
    lb = ProofBuilder(sys, "mp2ani")
    h1 = lb.hyp("mp2ani.1", "ψ")
    h2 = lb.hyp("mp2ani.2", "χ")
    h3 = lb.hyp("mp2ani.3", "φ → ((ψ ∧ χ) → θ)")
    s1 = lb.ref("s1", "φ → (χ → θ)", h1, h3, ref="mpani", note="mpani mp2ani.1, mp2ani.3")
    res = lb.ref("res", "φ → θ", h2, s1, ref="mpi", note="mpi mp2ani.2, s1")
    return lb.build(res)


def prove_mp4an(sys: System) -> Proof:
    r"""mp4an: ta.

    Hyp 1: ph
    Hyp 2: ps
    Hyp 3: ch
    Hyp 4: th
    Hyp 5: ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta
    Concl: ta

    Quadruple modus ponens with an antecedent.
    (Contributed by NM, 5-Jan-1993.)
    set.mm proof: wa pm3.2i mp2an.
    """
    lb = ProofBuilder(sys, "mp4an")
    h1 = lb.hyp("mp4an.1", "ph")
    h2 = lb.hyp("mp4an.2", "ps")
    h3 = lb.hyp("mp4an.3", "ch")
    h4 = lb.hyp("mp4an.4", "th")
    h5 = lb.hyp("mp4an.5", r"( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta")
    s1 = lb.ref("s1", r"( ph /\ ps )", h1, h2, ref="pm3.2i", note="pm3.2i mp4an.1, mp4an.2")
    s2 = lb.ref("s2", r"( ch /\ th )", h3, h4, ref="pm3.2i", note="pm3.2i mp4an.3, mp4an.4")
    res = lb.ref("res", "ta", s1, s2, h5, ref="mp2an", note="mp2an s1, s2, mp4an.5")
    return lb.build(res)


def prove_mp3an(sys: System) -> Proof:
    r"""mp3an: th.

    Hyp 1: ph
    Hyp 2: ps
    Hyp 3: ch
    Hyp 4: ( ph /\ ps /\ ch ) -> th
    Concl: th

    Triple modus ponens with an antecedent.
    (Contributed by NM, 14-May-1993.)
    set.mm proof: mp3an1 mp2an.
    """
    lb = ProofBuilder(sys, "mp3an")
    h1 = lb.hyp("mp3an.1", "ph")
    h2 = lb.hyp("mp3an.2", "ps")
    h3 = lb.hyp("mp3an.3", "ch")
    h4 = lb.hyp("mp3an.4", r"( ph /\ ps /\ ch ) -> th")
    s1 = lb.ref(
        "s1",
        r"( ps /\ ch ) -> th",
        h1,
        h4,
        ref="mp3an1",
        note="mp3an1 mp3an.1, mp3an.4",
    )
    res = lb.ref(
        "res",
        "th",
        h2,
        h3,
        s1,
        ref="mp2an",
        note="mp2an mp3an.2, mp3an.3, s1",
    )
    return lb.build(res)


def prove_mp3an12(sys: System) -> Proof:
    r"""mp3an12: χ → θ.

    Hyp 1: φ
    Hyp 2: ψ
    Hyp 3: ( φ ∧ ψ ∧ χ ) → θ
    Concl: χ → θ

    Triple modus ponens with the first two antecedents fixed.
    (Contributed by NM, 14-May-1993.)
    set.mm proof: mp3an1 mpan.
    """
    lb = ProofBuilder(sys, "mp3an12")
    h1 = lb.hyp("mp3an12.1", "φ")
    h2 = lb.hyp("mp3an12.2", "ψ")
    h3 = lb.hyp("mp3an12.3", "( φ ∧ ψ ∧ χ ) → θ")
    s1 = lb.ref(
        "s1",
        "( ψ ∧ χ ) → θ",
        h1,
        h3,
        ref="mp3an1",
        note="mp3an1 mp3an12.1, mp3an12.3",
    )
    res = lb.ref(
        "res",
        "χ → θ",
        h2,
        s1,
        ref="mpan",
        note="mpan mp3an12.2, s1",
    )
    return lb.build(res)


def prove_mp3an12i(sys: System) -> Proof:
    """mp3an12i: χ → τ.

    Hyp 1: φ
    Hyp 2: ψ
    Hyp 3: χ → θ
    Hyp 4: ( φ ∧ ψ ∧ θ ) → τ
    Concl: χ → τ

    Triple modus ponens with the first two antecedents fixed plus additional
    antecedent.
    (Contributed by NM, 14-May-1993.)
    """
    lb = ProofBuilder(sys, "mp3an12i")
    h1 = lb.hyp("mp3an12i.1", "φ")
    h2 = lb.hyp("mp3an12i.2", "ψ")
    h3 = lb.hyp("mp3an12i.3", "χ → θ")
    h4 = lb.hyp("mp3an12i.4", "( φ ∧ ψ ∧ θ ) → τ")
    s1 = lb.ref(
        "s1",
        "θ → τ",
        h1,
        h2,
        h4,
        ref="mp3an12",
        note="mp3an12 mp3an12i.1, mp3an12i.2, mp3an12i.4",
    )
    res = lb.ref(
        "res",
        "χ → τ",
        h3,
        s1,
        ref="syl",
        note="syl mp3an12i.3, s1",
    )
    return lb.build(res)


def prove_tbw_ax2(sys: System) -> Proof:
    """tbw-ax2: ( φ → ( ψ → φ ) ).

    Restatement of ax-1.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "tbw-ax2")
    res = lb.ref("res", "φ → ( ψ → φ )", ref="ax-1", note="A1")
    return lb.build(res)


def prove_tbw_ax1(sys: System) -> Proof:
    """tbw-ax1: ( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) ).

    Restatement of imim1.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "tbw-ax1")
    res = lb.ref("res", "( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) )", ref="imim1", note="imim1")
    return lb.build(res)


def prove_re1luk1(sys: System) -> Proof:
    """re1luk1: ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ).

    Restatement of tbw-ax1.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "re1luk1")
    res = lb.ref("res", "( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) )", ref="tbw-ax1", note="tbw-ax1")
    return lb.build(res)


def prove_tbw_ax3(sys: System) -> Proof:
    """tbw-ax3: ( ( ( φ → ψ ) → φ ) → φ ).

    Peirce's axiom restated in the Tarski-Bernays axiom system.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "tbw-ax3")
    res = lb.ref("res", "( ( ( φ → ψ ) → φ ) → φ )", ref="peirce", note="peirce")
    return lb.build(res)


def prove_tbwsyl(sys: System) -> Proof:
    """tbwsyl: φ → χ.

    Hyp 1: φ → ψ
    Hyp 2: ψ → χ
    Concl: φ → χ

    Syllogism inference from the Tarski-Bernays axiom system.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "tbwsyl")
    h1 = lb.hyp("tbwsyl.1", "φ → ψ")
    h2 = lb.hyp("tbwsyl.2", "ψ → χ")
    a1 = lb.ref("a1", "( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) )", ref="tbw-ax1", note="tbw-ax1")
    s1 = lb.mp("s1", h1, a1, "MP tbwsyl.1, a1")
    s2 = lb.mp("s2", h2, s1, "MP tbwsyl.2, s1")
    return lb.build(s2)


def prove_tbwlem1(sys: System) -> Proof:
    """tbwlem1: ( φ → ( ψ → χ ) ) → ( ψ → ( φ → χ ) ).

    Swap antecedents.  Tarski-Bernays proof.
    (Contributed by Anthony Hart, 16-Aug-2011.)
    """
    lb = ProofBuilder(sys, "tbwlem1")

    # tbw-ax1 with φ=φ, ψ=(ψ→χ), χ=χ
    s19 = lb.ref(
        "s19",
        "( φ → ( ψ → χ ) ) → ( ( ( ψ → χ ) → χ ) → ( φ → χ ) )",
        ref="tbw-ax1",
        note="tbw-ax1",
    )

    # tbw-ax2 with φ=ψ, ψ=(ψ→χ)
    s38 = lb.ref("s38", "ψ → ( ( ψ → χ ) → ψ )", ref="tbw-ax2", note="tbw-ax2")

    # tbw-ax1 with φ=(ψ→χ), ψ=ψ, χ=χ
    s42 = lb.ref(
        "s42",
        "( ( ψ → χ ) → ψ ) → ( ( ψ → χ ) → ( ( ψ → χ ) → χ ) )",
        ref="tbw-ax1",
        note="tbw-ax1",
    )

    # tbwsyl with s38, s42
    s43 = lb.ref(
        "s43", "ψ → ( ( ψ → χ ) → ( ( ψ → χ ) → χ ) )", s38, s42, ref="tbwsyl", note="tbwsyl"
    )

    # tbw-ax1 with φ=(ψ→χ), ψ=((ψ→χ)→χ), χ=χ
    s54 = lb.ref(
        "s54",
        "( ( ψ → χ ) → ( ( ψ → χ ) → χ ) ) → ( ( ( ( ψ → χ ) → χ ) → χ ) → ( ( ψ → χ ) → χ ) )",
        ref="tbw-ax1",
        note="tbw-ax1",
    )

    # tbw-ax3 with φ=((ψ→χ)→χ), ψ=χ
    s57 = lb.ref(
        "s57",
        "( ( ( ( ( ψ → χ ) → χ ) → χ ) → ( ( ψ → χ ) → χ ) ) → ( ( ψ → χ ) → χ ) )",
        ref="tbw-ax3",
        note="tbw-ax3",
    )

    # tbwsyl with s54, s57
    s58 = lb.ref(
        "s58",
        "( ( ψ → χ ) → ( ( ψ → χ ) → χ ) ) → ( ( ψ → χ ) → χ )",
        s54,
        s57,
        ref="tbwsyl",
        note="tbwsyl",
    )

    # tbwsyl with s43, s58
    s59 = lb.ref("s59", "ψ → ( ( ψ → χ ) → χ )", s43, s58, ref="tbwsyl", note="tbwsyl")

    # tbw-ax1 with φ=ψ, ψ=((ψ→χ)→χ), χ=(φ→χ)
    s63 = lb.ref(
        "s63",
        "( ψ → ( ( ψ → χ ) → χ ) ) → ( ( ( ( ψ → χ ) → χ ) → ( φ → χ ) ) → ( ψ → ( φ → χ ) ) )",
        ref="tbw-ax1",
        note="tbw-ax1",
    )

    # ax-mp with s63, s59
    s64 = lb.mp("s64", s59, s63, "MP s59, s63")

    # tbwsyl with s19, s64 (final step)
    res = lb.ref(
        "res", "( φ → ( ψ → χ ) ) → ( ψ → ( φ → χ ) )", s19, s64, ref="tbwsyl", note="tbwsyl"
    )

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


def prove_3imtr4i(sys: System) -> Proof:
    """3imtr4i: χ → θ.

    Hyp 1: φ → ψ
    Hyp 2: χ <-> φ
    Hyp 3: θ <-> ψ
    Concl: χ → θ

    Inference combining two biconditionals with an implication.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3imtr4i")
    h1 = lb.hyp("3imtr4i.1", "φ → ψ")
    h2 = lb.hyp("3imtr4i.2", "χ <-> φ")
    h3 = lb.hyp("3imtr4i.3", "θ <-> ψ")
    s1 = lb.ref("s1", "φ → θ", h1, h3, ref="sylibr", note="sylibr 3imtr4i.1, 3imtr4i.3")
    res = lb.ref("res", "χ → θ", h2, s1, ref="sylbi", note="sylbi 3imtr4i.2, s1")
    return lb.build(res)


def prove_3imtr3i(sys: System) -> Proof:
    """3imtr3i: χ → θ.

    Hyp 1: φ → ψ
    Hyp 2: φ <-> χ
    Hyp 3: ψ <-> θ
    Concl: χ → θ

    Inference combining two biconditionals with an implication.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3imtr3i")
    h1 = lb.hyp("3imtr3i.1", "φ → ψ")
    h2 = lb.hyp("3imtr3i.2", "φ <-> χ")
    h3 = lb.hyp("3imtr3i.3", "ψ <-> θ")
    s1 = lb.ref("s1", "φ → θ", h1, h3, ref="sylib", note="sylib 3imtr3i.1, 3imtr3i.3")
    res = lb.ref("res", "χ → θ", h2, s1, ref="sylbir", note="sylbir 3imtr3i.2, s1")
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


def prove_mpii(sys: System) -> Proof:
    """mpii: φ → (ψ → θ). Hyp1: χ, Hyp2: φ → (ψ → (χ → θ)).

    A nested modus ponens inference.
    (Contributed by NM, 5-Jul-1994.)
    set.mm proof: a1i mpdi.
    """
    lb = ProofBuilder(sys, "mpii")
    h1 = lb.hyp("mpii.1", "χ")
    h2 = lb.hyp("mpii.2", "( φ → ( ψ → ( χ → θ ) ) )")
    s1 = lb.ref("s1", "( ψ → χ )", h1, ref="a1i", note="a1i mpii.1")
    res = lb.ref("res", "( φ → ( ψ → θ ) )", s1, h2, ref="mpdi", note="mpdi s1, mpii.2")
    return lb.build(res)


def prove_mpisyl(sys: System) -> Proof:
    """mpisyl: φ → θ.

    Hyp 1: φ → ψ
    Hyp 2: χ
    Hyp 3: ψ → ( χ → θ )
    Concl: φ → θ

    A syllogism combined with a modus ponens inference.
    (Contributed by NM, 28-Dec-1992.)
    set.mm proof: mpi syl.
    """
    lb = ProofBuilder(sys, "mpisyl")
    h1 = lb.hyp("mpisyl.1", "φ → ψ")
    h2 = lb.hyp("mpisyl.2", "χ")
    h3 = lb.hyp("mpisyl.3", "ψ → ( χ → θ )")
    s1 = lb.ref("s1", "ψ → θ", h2, h3, ref="mpi", note="mpi mpisyl.2, mpisyl.3")
    res = lb.ref("res", "φ → θ", h1, s1, ref="syl", note="syl mpisyl.1, s1")
    return lb.build(res)


def prove_syl6mpi(sys: System) -> Proof:
    """syl6mpi: φ → ( ψ → τ ).

    Hyp 1: φ → ( ψ → χ )
    Hyp 2: θ
    Hyp 3: χ → ( θ → τ )
    Concl: φ → ( ψ → τ )

    A syllogism combined with a modus ponens inference.
    (Contributed by NM, 20-Aug-2001.)
    set.mm proof: mpi syl6.
    """
    lb = ProofBuilder(sys, "syl6mpi")
    h1 = lb.hyp("syl6mpi.1", "φ → ( ψ → χ )")
    h2 = lb.hyp("syl6mpi.2", "θ")
    h3 = lb.hyp("syl6mpi.3", "χ → ( θ → τ )")
    s1 = lb.ref("s1", "χ → τ", h2, h3, ref="mpi", note="mpi syl6mpi.2, syl6mpi.3")
    res = lb.ref("res", "φ → ( ψ → τ )", h1, s1, ref="syl6", note="syl6 syl6mpi.1, s1")
    return lb.build(res)


def prove_imim12i(sys: System) -> Proof:
    """imim12i: (ψ → χ) → (φ → θ).

    Hyp 1: φ → ψ
    Hyp 2: χ → θ
    Concl: (ψ → χ) → (φ → θ)

    Inference combining imim2i and syl5.
    (Contributed by NM, 28-Dec-1992.)
    """
    lb = ProofBuilder(sys, "imim12i")
    h1 = lb.hyp("imim12i.1", "φ → ψ")
    h2 = lb.hyp("imim12i.2", "χ → θ")
    s1 = lb.ref("s1", "(ψ → χ) → (ψ → θ)", h2, ref="imim2i", note="imim2i")
    res = lb.ref("res", "(ψ → χ) → (φ → θ)", h1, s1, ref="syl5", note="syl5")
    return lb.build(res)


def prove_imim1i(sys: System) -> Proof:
    """imim1i: (ψ → χ) → (φ → χ).

    Hyp: φ → ψ
    Concl: (ψ → χ) → (φ → χ)

    Inference form of imim1.
    (Contributed by NM, 28-Dec-1992.)
    """
    lb = ProofBuilder(sys, "imim1i")
    h1 = lb.hyp("imim1i.1", "φ → ψ")
    s_id = lb.ref("s_id", "χ → χ", ref="id", note="id")
    res = lb.ref("res", "(ψ → χ) → (φ → χ)", h1, s_id, ref="imim12i", note="imim12i")
    return lb.build(res)


def prove_2a1dd(sys: System) -> Proof:
    """2a1dd: φ → (ψ → (θ → (τ → χ))).

    Hyp: φ → (ψ → χ), Concl: φ → (ψ → (θ → (τ → χ))).

    Deduction introducing two nested antecedents.  Deduction form of
    ~ 2a1d .  (Contributed by NM, 5-Jan-1993.)
    """
    lb = ProofBuilder(sys, "2a1dd")

    hyp_wff = lb.hyp("2a1dd.1", "φ → ( ψ → χ )")

    s1 = lb.ref("s1", "φ → ( ψ → ( τ → χ ) )", hyp_wff, ref="a1dd", note="a1dd")
    res = lb.ref("res", "φ → ( ψ → ( θ → ( τ → χ ) ) )", s1, ref="a1dd", note="a1dd")

    return lb.build(res)


def prove_embantd(sys: System) -> Proof:
    """embantd: φ → ((ψ → χ) → θ).

    Hyp: φ → ψ, φ → (χ → θ).
    Deduction embedding an antecedent.
    (Contributed by NM, 14-Dec-2004.)
    """
    lb = ProofBuilder(sys, "embantd")
    h1 = lb.hyp("embantd.1", "φ → ψ")
    h2 = lb.hyp("embantd.2", "φ → ( χ → θ )")
    s1 = lb.ref("s1", "φ → ( ( ψ → χ ) → ( ψ → θ ) )", h2, ref="imim2d", note="imim2d")
    res = lb.ref("res", "φ → ( ( ψ → χ ) → θ )", h1, s1, ref="mpid", note="mpid")
    return lb.build(res)


def prove_ecase(sys: System) -> Proof:
    """ecase: χ.  Hyps: -. φ → χ, -. ψ → χ, ( φ ∧ ψ ) → χ.

    Inference for elimination by cases.
    (Contributed by NM, 13-Jul-2005.)
    """
    lb = ProofBuilder(sys, "ecase")
    h1 = lb.hyp("ecase.1", "-. φ → χ")
    h2 = lb.hyp("ecase.2", "-. ψ → χ")
    h3 = lb.hyp("ecase.3", "( φ ∧ ψ ) → χ")
    s1 = lb.ref("s1", "φ → ( ψ → χ )", h3, ref="ex", note="ex")
    res = lb.ref("res", "χ", s1, h1, h2, ref="pm2.61nii", note="pm2.61nii")
    return lb.build(res)


def prove_ecase3(sys: System) -> Proof:
    """ecase3: χ.  Hyps: φ → χ, ψ → χ, ¬ ( φ ∨ ψ ) → χ.

    Inference for elimination by cases.
    (Contributed by NM, 29-Dec-1992.)
    """
    lb = ProofBuilder(sys, "ecase3")
    h1 = lb.hyp("ecase3.1", "φ → χ")
    h2 = lb.hyp("ecase3.2", "ψ → χ")
    h3 = lb.hyp("ecase3.3", "¬ ( φ ∨ ψ ) → χ")
    s1 = lb.ref("s1", "( φ ∨ ψ ) → χ", h1, h2, ref="jaoi", note="jaoi")
    res = lb.ref("res", "χ", s1, h3, ref="pm2.61i", note="pm2.61i")
    return lb.build(res)


def prove_ecase3d(sys: System) -> Proof:
    """ecase3d: φ → θ.  Hyps: φ → (ψ → θ), φ → (χ → θ), φ → (¬ (ψ ∨ χ) → θ).

    Deduction for elimination by cases.
    (Contributed by NM, 29-Dec-1992.)
    """
    lb = ProofBuilder(sys, "ecase3d")
    h1 = lb.hyp("ecase3d.1", "φ → ( ψ → θ )")
    h2 = lb.hyp("ecase3d.2", "φ → ( χ → θ )")
    h3 = lb.hyp("ecase3d.3", "φ → ( ¬ ( ψ ∨ χ ) → θ )")
    s1 = lb.ref("s1", "φ → ( ( ψ ∨ χ ) → θ )", h1, h2, ref="jaod", note="jaod")
    res = lb.ref("res", "φ → θ", s1, h3, ref="pm2.61d", note="pm2.61d")
    return lb.build(res)


def prove_ecase2d(sys: System) -> Proof:
    """ecase2d: φ → τ.

    Hyps: φ → ψ, φ → ¬(ψ ∧ χ), φ → ¬(ψ ∧ θ), φ → (τ ∨ (χ ∨ θ)).

    Deduction for elimination by cases with two alternatives.
    (Contributed by NM, 21-Apr-1994.)
    """
    lb = ProofBuilder(sys, "ecase2d")
    h1 = lb.hyp("ecase2d.1", "φ → ψ")
    h2 = lb.hyp("ecase2d.2", "φ → ¬ ( ψ ∧ χ )")
    h3 = lb.hyp("ecase2d.3", "φ → ¬ ( ψ ∧ θ )")
    h4 = lb.hyp("ecase2d.4", "φ → ( τ ∨ ( χ ∨ θ ) )")
    s1 = lb.ref("s1", "φ → ¬ χ", h1, h2, ref="mpnanrd", note="mpnanrd h1,h2")
    s2 = lb.ref("s2", "φ → ¬ θ", h1, h3, ref="mpnanrd", note="mpnanrd h1,h3")
    s3 = lb.ref(
        "s3",
        "φ → ( ¬ τ → ( χ ∨ θ ) )",
        h4,
        ref="ord",
        note="ord h4",
    )
    s4 = lb.ref(
        "s4",
        "φ → ¬ ¬ τ",
        s1,
        s2,
        s3,
        ref="mtord",
        note="mtord s1,s2,s3",
    )
    res = lb.ref("res", "φ → τ", s4, ref="notnotrd", note="notnotrd s4")
    return lb.build(res)


def prove_ecase23d(sys: System) -> Proof:
    """ecase23d: φ → ψ.

    Hyps: φ → ¬ χ, φ → ¬ θ, φ → ( ψ ∨ χ ∨ θ ).

    Deduction for elimination by cases with three alternatives, where the
    first two are eliminated by their negations.
    (Contributed by NM, 29-Dec-1992.)
    """
    lb = ProofBuilder(sys, "ecase23d")
    h1 = lb.hyp("ecase23d.1", "φ → ¬ χ")
    h2 = lb.hyp("ecase23d.2", "φ → ¬ θ")
    h3 = lb.hyp("ecase23d.3", "φ → ( ψ ∨ χ ∨ θ )")
    s1 = lb.ref(
        "s1",
        "( ψ ∨ χ ∨ θ ) ↔ ( ψ ∨ ( χ ∨ θ ) )",
        ref="3orass",
        note="3orass",
    )
    s2 = lb.ref(
        "s2",
        "φ → ( ψ ∨ ( χ ∨ θ ) )",
        h3,
        s1,
        ref="sylib",
        note="sylib h3, s1",
    )
    s3 = lb.ref(
        "s3",
        "¬ ( χ ∨ θ ) ↔ ( ¬ χ ∧ ¬ θ )",
        ref="ioran",
        note="ioran",
    )
    s4 = lb.ref(
        "s4",
        "φ → ¬ ( χ ∨ θ )",
        h1,
        h2,
        s3,
        ref="sylanbrc",
        note="sylanbrc h1, h2, s3",
    )
    res = lb.ref(
        "res",
        "φ → ψ",
        s2,
        s4,
        ref="olcnd",
        note="olcnd s2, s4",
    )
    return lb.build(res)


def prove_ecased(sys: System) -> Proof:
    """ecased: φ → θ.  Hyps: φ → (¬ ψ → θ), φ → (¬ χ → θ), φ → ((ψ ∧ χ) → θ).

    Deduction for elimination by cases.
    (Contributed by NM, 26-Oct-2006.)
    """
    lb = ProofBuilder(sys, "ecased")
    h1 = lb.hyp("ecased.1", "φ → ( ¬ ψ → θ )")
    h2 = lb.hyp("ecased.2", "φ → ( ¬ χ → θ )")
    h3 = lb.hyp("ecased.3", "φ → ( ( ψ ∧ χ ) → θ )")
    s1 = lb.ref(
        "s1",
        "¬ ( ¬ ψ ∨ ¬ χ ) → ( ψ ∧ χ )",
        ref="pm3.11",
        note="pm3.11",
    )
    s2 = lb.ref(
        "s2",
        "φ → ( ¬ ( ¬ ψ ∨ ¬ χ ) → θ )",
        s1,
        h3,
        ref="syl5",
        note="syl5",
    )
    res = lb.ref(
        "res",
        "φ → θ",
        h1,
        h2,
        s2,
        ref="ecase3d",
        note="ecase3d",
    )
    return lb.build(res)


def prove_efald(sys: System) -> Proof:
    r"""efald: ( ph -> ps ).  Hyp: efald.1 |- ( ( ph /\ -. ps ) -> ⊥ ).

    Deduction form of efal: from a conjunction with a negated consequent
    implying falsehood, derive the consequent.
    (Contributed by NM, 2-Jan-2002.)
    """
    lb = ProofBuilder(sys, "efald")
    h1 = lb.hyp("efald.1", "( ( ph /\\ -. ps ) -> ⊥ )")
    s1 = lb.ref("s1", "( ph -> -. -. ps )", h1, ref="inegd", note="inegd")
    res = lb.ref("res", "( ph -> ps )", s1, ref="notnotrd", note="notnotrd")
    return lb.build(res)


def prove_equcoms(sys: System) -> Proof:
    """equcoms: y = x → φ.

    Inference commuting equality in an antecedent.
    set.mm proof: weq equcomi syl.
    """
    lb = ProofBuilder(sys, "equcoms")
    h1 = lb.hyp("equcoms.1", "x = y → φ")
    s1 = lb.ref("s1", "y = x → x = y", ref="equcomi", note="equcomi")
    res = lb.ref("res", "y = x → φ", s1, h1, ref="syl", note="syl equcomi, equcoms.1")
    return lb.build(res)


def prove_equeuclr(sys: System) -> Proof:
    """equeuclr: x = z → ( y = z → y = x ).

    Equality Euclidean property: from two equalities with a common term z,
    conclude the remaining equality.
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: weq equtrr equcoms.
    """
    lb = ProofBuilder(sys, "equeuclr")
    # equtrr with x:=z, y:=x, z:=y: z = x → ( y = z → y = x )
    s1 = lb.ref(
        "s1",
        "z = x → ( y = z → y = x )",
        ref="equtrr",
        note="equtrr with x:=z, y:=x, z:=y",
    )
    # equcoms: from z = x → φ derive x = z → φ
    res = lb.ref(
        "res",
        "x = z → ( y = z → y = x )",
        s1,
        ref="equcoms",
        note="equcoms",
    )
    return lb.build(res)


def prove_equeucl(sys: System) -> Proof:
    """equeucl: x = z → ( y = z → x = y ).

    Equality Euclidean property: from two equalities with a common term z,
    conclude the remaining equality, with x and y swapped in the inner
    antecedent compared to ~ equeuclr .
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: weq equeuclr com12.
    """
    lb = ProofBuilder(sys, "equeucl")
    # equeuclr with x:=y, y:=x: y = z → ( x = z → x = y )
    s1 = lb.ref(
        "s1",
        "y = z → ( x = z → x = y )",
        ref="equeuclr",
        note="equeuclr with x:=y, y:=x",
    )
    # com12: from y = z → ( x = z → x = y ) derive x = z → ( y = z → x = y )
    res = lb.ref(
        "res",
        "x = z → ( y = z → x = y )",
        s1,
        ref="com12",
        note="com12",
    )
    return lb.build(res)


def prove_expi(sys: System) -> Proof:
    """expi: ph → ( ps → ch ).

    Hyp: expi.1 |- ( ¬ ( φ → ¬ ψ ) → χ ).
    Concl: |- ( ph → ( ps → ch ) ).

    Exportation inference.  (Contributed by NM, 29-Dec-1992.)
    """
    lb = ProofBuilder(sys, "expi")
    h1 = lb.hyp("expi.1", "( ¬ ( φ → ¬ ψ ) → χ )")
    s1 = lb.ref("s1", "φ → ( ψ → ¬ ( φ → ¬ ψ ) )", ref="pm3.2im", note="pm3.2im")
    res = lb.ref("res", "φ → ( ψ → χ )", s1, h1, ref="syl6", note="syl6")
    return lb.build(res)


def prove_mpsyl(sys: System) -> Proof:
    """mpsyl: ψ → θ.

    Hyp 1: φ
    Hyp 2: ψ → χ
    Hyp 3: φ → (χ → θ)
    Concl: ψ → θ

    Inference combining a1i and sylc.
    (Contributed by NM, 12-Dec-1993.)
    """
    lb = ProofBuilder(sys, "mpsyl")
    h1 = lb.hyp("mpsyl.1", "φ")
    h2 = lb.hyp("mpsyl.2", "ψ → χ")
    h3 = lb.hyp("mpsyl.3", "φ → ( χ → θ )")
    s1 = lb.ref("s1", "ψ → φ", h1, ref="a1i", note="a1i")
    res = lb.ref("res", "ψ → θ", s1, h2, h3, ref="sylc", note="sylc")
    return lb.build(res)


def prove_mpsylsyld(sys: System) -> Proof:
    """mpsylsyld: ψ → (χ → τ).

    Hyp 1: φ
    Hyp 2: ψ → (χ → θ)
    Hyp 3: φ → (θ → τ)
    Concl: ψ → (χ → τ)

    Modus ponens with nested syllogism deduction.
    (Contributed by NM, 26-Mar-1995.)
    """
    lb = ProofBuilder(sys, "mpsylsyld")
    h1 = lb.hyp("mpsylsyld.1", "φ")
    h2 = lb.hyp("mpsylsyld.2", "ψ → ( χ → θ )")
    h3 = lb.hyp("mpsylsyld.3", "φ → ( θ → τ )")
    s1 = lb.ref("s1", "ψ → φ", h1, ref="a1i", note="a1i")
    res = lb.ref("res", "ψ → ( χ → τ )", s1, h2, h3, ref="sylsyld", note="sylsyld")
    return lb.build(res)


def prove_syl7(sys: System) -> Proof:
    """syl7: χ → (θ → (φ → τ)). Hyps: φ → ψ, χ → (θ → (ψ → τ)).

    A syllogism inference.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "syl7")
    h1 = lb.hyp("syl7.1", "φ → ψ")
    h2 = lb.hyp("syl7.2", "χ → (θ → (ψ → τ))")
    s1 = lb.ref("s1", "χ → (φ → ψ)", h1, ref="a1i", note="a1i")
    res = lb.ref("res", "χ → (θ → (φ → τ))", s1, h2, ref="syl5d", note="syl5d")
    return lb.build(res)


def prove_syl7bi(sys: System) -> Proof:
    """syl7bi: χ → (θ → (φ → τ)). Hyps: φ ↔ ψ, χ → (θ → (ψ → τ)).

    A syllogism inference with a biconditional antecedent.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "syl7bi")
    h1 = lb.hyp("syl7bi.1", "φ <-> ψ")
    h2 = lb.hyp("syl7bi.2", "χ → (θ → (ψ → τ))")
    s1 = lb.ref("s1", "φ → ψ", h1, ref="biimpi", note="biimpi syl7bi.1")
    res = lb.ref("res", "χ → (θ → (φ → τ))", s1, h2, ref="syl7", note="syl7 s1, syl7bi.2")
    return lb.build(res)


def prove_syl8(sys: System) -> Proof:
    """syl8: φ → (ψ → (χ → τ)).  Hyps: φ → (ψ → (χ → θ)), θ → τ.

    A syllogism inference.  (Contributed by NM, 25-Dec-1992.)
    """
    lb = ProofBuilder(sys, "syl8")
    h1 = lb.hyp("syl8.1", "φ → ( ψ → ( χ → θ ) )")
    h2 = lb.hyp("syl8.2", "θ → τ")
    s1 = lb.ref("s1", "φ → ( θ → τ )", h2, ref="a1i", note="a1i syl8.2")
    res = lb.ref("res", "φ → ( ψ → ( χ → τ ) )", h1, s1, ref="syl6d", note="syl6d syl8.1, s1")
    return lb.build(res)


def prove_syl8ib(sys: System) -> Proof:
    """syl8ib: φ → (ψ → (χ → τ)).  Hyps: φ → (ψ → (χ → θ)), θ ↔ τ.

    A syllogism inference with a biconditional.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "syl8ib")
    h1 = lb.hyp("syl8ib.1", "φ → ( ψ → ( χ → θ ) )")
    h2 = lb.hyp("syl8ib.2", "θ <-> τ")
    s1 = lb.ref("s1", "θ → τ", h2, ref="biimpi", note="biimpi syl8ib.2")
    res = lb.ref("res", "φ → ( ψ → ( χ → τ ) )", h1, s1, ref="syl8", note="syl8 syl8ib.1, s1")
    return lb.build(res)


def prove_syl9(sys: System) -> Proof:
    """syl9: φ → (θ → (ψ → τ)). Hyps: φ → (ψ → χ), θ → (χ → τ).

    A syllogism inference. (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "syl9")
    h1 = lb.hyp("syl9.1", "φ → (ψ → χ)")
    h2 = lb.hyp("syl9.2", "θ → (χ → τ)")
    s1 = lb.ref("s1", "φ → (θ → (χ → τ))", h2, ref="a1i", note="a1i")
    res = lb.ref("res", "φ → (θ → (ψ → τ))", h1, s1, ref="syl5d", note="syl5d")
    return lb.build(res)


def prove_syl9r(sys: System) -> Proof:
    """syl9r: θ → (φ → (ψ → τ)). Hyps: φ → (ψ → χ), θ → (χ → τ).

    A syllogism inference. (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "syl9r")
    h1 = lb.hyp("syl9r.1", "φ → (ψ → χ)")
    h2 = lb.hyp("syl9r.2", "θ → (χ → τ)")
    s1 = lb.ref("s1", "φ → (θ → (ψ → τ))", h1, h2, ref="syl9", note="syl9")
    res = lb.ref("res", "θ → (φ → (ψ → τ))", s1, ref="com12", note="com12")
    return lb.build(res)


def prove_syl10(sys: System) -> Proof:
    """syl10: φ → ( ψ → ( θ → η ) ).

    Hyp 1: φ → ( ψ → χ )
    Hyp 2: φ → ( ψ → ( θ → τ ) )
    Hyp 3: χ → ( τ → η )
    Concl: φ → ( ψ → ( θ → η ) )

    A syllogism inference.  (Contributed by NM, 31-May-1993.)
    """
    lb = ProofBuilder(sys, "syl10")
    h1 = lb.hyp("syl10.1", "φ → ( ψ → χ )")
    h2 = lb.hyp("syl10.2", "φ → ( ψ → ( θ → τ ) )")
    h3 = lb.hyp("syl10.3", "χ → ( τ → η )")
    s1 = lb.ref("s1", "φ → ( ψ → ( τ → η ) )", h1, h3, ref="syl6", note="syl6 syl10.1, syl10.3")
    res = lb.ref("res", "φ → ( ψ → ( θ → η ) )", h2, s1, ref="syldd", note="syldd syl10.2, s1")
    return lb.build(res)


def prove_com3r(sys: System) -> Proof:
    """com3r: χ → (φ → (ψ → θ)).  Hyp: φ → (ψ → (χ → θ)).

    Commutation of antecedents.  Rotate right.
    (Contributed by NM, 27-Dec-1992.)
    """
    lb = ProofBuilder(sys, "com3r")
    h1 = lb.hyp("com3.1", "φ → ( ψ → ( χ → θ ) )")
    s1 = lb.ref("s1", "φ → ( χ → ( ψ → θ ) )", h1, ref="com23", note="com23")
    res = lb.ref("res", "χ → ( φ → ( ψ → θ ) )", s1, ref="com12", note="com12")
    return lb.build(res)


def prove_com13(sys: System) -> Proof:
    """com13: χ → (ψ → (φ → θ)).  Hyp: φ → (ψ → (χ → θ)).

    Commutation of antecedents.  Swap 1st and 3rd.
    (Contributed by NM, 27-Dec-1992.)
    """
    lb = ProofBuilder(sys, "com13")
    h1 = lb.hyp("com13.1", "φ → ( ψ → ( χ → θ ) )")
    s1 = lb.ref("s1", "χ → ( φ → ( ψ → θ ) )", h1, ref="com3r", note="com3r")
    res = lb.ref("res", "χ → ( ψ → ( φ → θ ) )", s1, ref="com23", note="com23")
    return lb.build(res)


def prove_com3l(sys: System) -> Proof:
    """com3l: ψ → (χ → (φ → θ)).  Hyp: φ → (ψ → (χ → θ)).

    Commutation of antecedents.  Rotate left.
    (Contributed by NM, 27-Dec-1992.)
    """
    lb = ProofBuilder(sys, "com3l")
    h1 = lb.hyp("com3l.1", "φ → ( ψ → ( χ → θ ) )")
    s1 = lb.ref("s1", "χ → ( φ → ( ψ → θ ) )", h1, ref="com3r", note="com3r")
    s2 = lb.ref("s2", "χ → ( ψ → ( φ → θ ) )", s1, ref="com23", note="com23")
    res = lb.ref("res", "ψ → ( χ → ( φ → θ ) )", s2, ref="com12", note="com12")
    return lb.build(res)


def prove_com34(sys: System) -> Proof:
    """com34: ph → (ps → (th → (ch → ta))).  Hyp: ph → (ps → (ch → (th → ta))).

    Commutation of antecedents.  Swap 3rd and 4th.  Deduction associated
    with ~ com23 .  Double deduction associated with ~ com12 .
    (Contributed by NM, 25-Apr-1994.)
    """
    lb = ProofBuilder(sys, "com34")

    h = lb.hyp("com4.1", "ph → ( ps → ( ch → ( th → ta ) ) )")

    s1 = lb.ref(
        "s1",
        "( ch → ( th → ta ) ) → ( th → ( ch → ta ) )",
        ref="pm2.04",
        note="pm2.04",
    )
    res = lb.ref(
        "res",
        "ph → ( ps → ( th → ( ch → ta ) ) )",
        h,
        s1,
        ref="syl6",
        note="syl6",
    )
    return lb.build(res)


def prove_com45(sys: System) -> Proof:
    """com45: ph → (ps → (ch → (ta → (th → et)))).  Hyp: ph → (ps → (ch → (th → (ta → et)))).

    Commutation of antecedents.  Swap 4th and 5th.
    (Contributed by NM, 25-Apr-1994.)
    """
    lb = ProofBuilder(sys, "com45")

    h = lb.hyp("com5.1", "ph → ( ps → ( ch → ( th → ( ta → et ) ) ) )")

    s1 = lb.ref(
        "s1",
        "( th → ( ta → et ) ) → ( ta → ( th → et ) )",
        ref="pm2.04",
        note="pm2.04",
    )
    res = lb.ref(
        "res",
        "ph → ( ps → ( ch → ( ta → ( th → et ) ) ) )",
        h,
        s1,
        ref="syl8",
        note="syl8 com5.1, s1",
    )
    return lb.build(res)


def prove_com35(sys: System) -> Proof:
    """com35: ph → (ps → (ta → (th → (ch → et)))).  Hyp: ph → (ps → (ch → (th → (ta → et)))).

    Commutation of antecedents.  Swap 3rd and 5th.
    (Contributed by NM, 25-Apr-1994.)
    """
    lb = ProofBuilder(sys, "com35")

    h = lb.hyp("com35.1", "ph → ( ps → ( ch → ( th → ( ta → et ) ) ) )")

    s1 = lb.ref(
        "s1",
        "ph → ( ps → ( th → ( ch → ( ta → et ) ) ) )",
        h,
        ref="com34",
        note="com34 com35.1",
    )
    s2 = lb.ref(
        "s2",
        "ph → ( ps → ( th → ( ta → ( ch → et ) ) ) )",
        s1,
        ref="com45",
        note="com45 s1",
    )
    res = lb.ref(
        "res",
        "ph → ( ps → ( ta → ( th → ( ch → et ) ) ) )",
        s2,
        ref="com34",
        note="com34 s2",
    )
    return lb.build(res)


def prove_com4l(sys: System) -> Proof:
    """com4l: ps → (ch → (th → (ph → ta))).  Hyp: ph → (ps → (ch → (th → ta))).

    Commutation of antecedents.  Rotate left.
    (Contributed by NM, 27-Dec-1992.)
    """
    lb = ProofBuilder(sys, "com4l")
    h = lb.hyp("com4l.1", "ph → ( ps → ( ch → ( th → ta ) ) )")
    s1 = lb.ref("s1", "ps → ( ch → ( ph → ( th → ta ) ) )", h, ref="com3l", note="com3l")
    res = lb.ref("res", "ps → ( ch → ( th → ( ph → ta ) ) )", s1, ref="com34", note="com34")
    return lb.build(res)


def prove_com4t(sys: System) -> Proof:
    """com4t: ch → (th → (ph → (ps → ta))).  Hyp: ph → (ps → (ch → (th → ta))).

    Commutation of antecedents.  Rotate right.
    (Contributed by NM, 27-Dec-1992.)
    """
    lb = ProofBuilder(sys, "com4t")
    h = lb.hyp("com4t.1", "ph → ( ps → ( ch → ( th → ta ) ) )")
    s1 = lb.ref("s1", "ps → ( ch → ( th → ( ph → ta ) ) )", h, ref="com4l", note="com4l")
    res = lb.ref("res", "ch → ( th → ( ph → ( ps → ta ) ) )", s1, ref="com4l", note="com4l")
    return lb.build(res)


def prove_com4r(sys: System) -> Proof:
    """com4r: th → (ph → (ps → (ch → ta))).  Hyp: ph → (ps → (ch → (th → ta))).

    Commutation of antecedents.  Rotate right.
    (Contributed by NM, 25-Apr-1994.)
    """
    lb = ProofBuilder(sys, "com4r")
    h = lb.hyp("com4r.1", "ph → ( ps → ( ch → ( th → ta ) ) )")
    s1 = lb.ref("s1", "ch → ( th → ( ph → ( ps → ta ) ) )", h, ref="com4t", note="com4t")
    res = lb.ref("res", "th → ( ph → ( ps → ( ch → ta ) ) )", s1, ref="com4l", note="com4l")
    return lb.build(res)


def prove_com14(sys: System) -> Proof:
    """com14: th → ( ps → ( ch → ( ph → ta ) ) ).  Hyp: ph → ( ps → ( ch → ( th → ta ) ) ).

    Commutation of antecedents.  Swap 1st and 4th.
    (Contributed by NM, 27-Dec-1992.)
    """
    lb = ProofBuilder(sys, "com14")
    h = lb.hyp("com14.1", "ph → ( ps → ( ch → ( th → ta ) ) )")
    s1 = lb.ref("s1", "ps → ( ch → ( th → ( ph → ta ) ) )", h, ref="com4l", note="com4l")
    res = lb.ref("res", "th → ( ps → ( ch → ( ph → ta ) ) )", s1, ref="com3r", note="com3r")
    return lb.build(res)


def prove_com24(sys: System) -> Proof:
    """com24: ph → (th → (ch → (ps → ta))).  Hyp: ph → (ps → (ch → (th → ta))).

    Commutation of antecedents.  Swap 2nd and 4th.
    (Contributed by NM, 27-Dec-1992.)
    """
    lb = ProofBuilder(sys, "com24")
    h = lb.hyp("com24.1", "ph → ( ps → ( ch → ( th → ta ) ) )")
    s1 = lb.ref("s1", "ch → ( th → ( ph → ( ps → ta ) ) )", h, ref="com4t", note="com4t")
    res = lb.ref("res", "ph → ( th → ( ch → ( ps → ta ) ) )", s1, ref="com13", note="com13")
    return lb.build(res)


def prove_com25(sys: System) -> Proof:
    """com25: ph → (ta → (ch → (th → (ps → et)))).  Hyp: ph → (ps → (ch → (th → (ta → et)))).

    Commutation of antecedents.  Swap 2nd and 5th.
    (Contributed by NM, 25-Apr-1994.)
    """
    lb = ProofBuilder(sys, "com25")

    h = lb.hyp("com25.1", "ph → ( ps → ( ch → ( th → ( ta → et ) ) ) )")

    s1 = lb.ref(
        "s1",
        "ph → ( th → ( ch → ( ps → ( ta → et ) ) ) )",
        h,
        ref="com24",
        note="com24 com25.1",
    )
    s2 = lb.ref(
        "s2",
        "ph → ( th → ( ch → ( ta → ( ps → et ) ) ) )",
        s1,
        ref="com45",
        note="com45 s1",
    )
    res = lb.ref(
        "res",
        "ph → ( ta → ( ch → ( th → ( ps → et ) ) ) )",
        s2,
        ref="com24",
        note="com24 s2",
    )
    return lb.build(res)


def prove_a1ddd(sys: System) -> Proof:
    """a1ddd: φ → (ψ → (χ → (θ → τ))).  Hyp: φ → (ψ → (χ → τ)).

    Deduction introducing a nested antecedent.  Deduction form of ~ ax-1 .
    (Contributed by NM, 7-Feb-1993.)
    """
    lb = ProofBuilder(sys, "a1ddd")
    hyp = lb.hyp("a1ddd.1", "φ → ( ψ → ( χ → τ ) )")
    s1 = lb.ref("s1", "τ → ( θ → τ )", ref="ax-1", note="A1")
    res = lb.ref("res", "φ → ( ψ → ( χ → ( θ → τ ) ) )", hyp, s1, ref="syl8", note="syl8")
    return lb.build(res)


def prove_tarski_bernays_ax2(sys: System) -> Proof:
    """tarski-bernays-ax2: (φ → (ψ → χ)) → ((φ → ψ) → (φ → χ)).

    Tarski-Bernays axiom 2.  Equivalent to ax-2.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "tarski-bernays-ax2")
    res = lb.ref(
        "res",
        "( φ → ( ψ → χ ) ) → ( ( φ → ψ ) → ( φ → χ ) )",
        ref="ax-2",
        note="A2",
    )
    return lb.build(res)


def prove_biimtrdi(sys: System) -> Proof:
    """biimtrdi: φ → ( ψ → θ ).

    Hyp 1: φ → ( ψ <-> χ )
    Hyp 2: χ → θ
    Concl: φ → ( ψ → θ )

    Deduction form of biimtr: from a hypothesis that implies a
    biconditional and a second hypothesis, deduce the consequent
    of the forward implication.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "biimtrdi")
    h1 = lb.hyp("biimtrdi.1", "φ → ( ψ <-> χ )")
    h2 = lb.hyp("biimtrdi.2", "χ → θ")
    s1 = lb.ref("s1", "φ → ( ψ → χ )", h1, ref="biimpd", note="biimpd biimtrdi.1")
    res = lb.ref("res", "φ → ( ψ → θ )", s1, h2, ref="syl6", note="syl6 s1, biimtrdi.2")
    return lb.build(res)


def prove_biimtrrdi(sys: System) -> Proof:
    """biimtrrdi: φ → ( ψ → θ ).

    Hyp 1: φ → ( χ <-> ψ )
    Hyp 2: χ → θ
    Concl: φ → ( ψ → θ )

    Deduction form of biimtrr: from a hypothesis that implies a
    biconditional and a second hypothesis, deduce the consequent
    of the reverse implication.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "biimtrrdi")
    h1 = lb.hyp("biimtrrdi.1", "φ → ( χ <-> ψ )")
    h2 = lb.hyp("biimtrrdi.2", "χ → θ")
    s1 = lb.ref("s1", "φ → ( ψ → χ )", h1, ref="biimprd", note="biimprd biimtrrdi.1")
    res = lb.ref("res", "φ → ( ψ → θ )", s1, h2, ref="syl6", note="syl6 s1, biimtrrdi.2")
    return lb.build(res)


def prove_biimtrid(sys: System) -> Proof:
    """biimtrid: χ → ( φ → θ ).

    Hyp 1: φ <-> ψ
    Hyp 2: χ → ( ψ → θ )
    Concl: χ → ( φ → θ )

    Deduction form of inference: from a biconditional and a second hypothesis,
    deduce the forward implication substituted into the first antecedent of the
    second hypothesis.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "biimtrid")
    h1 = lb.hyp("biimtrid.1", "( φ <-> ψ )")
    h2 = lb.hyp("biimtrid.2", "χ → ( ψ → θ )")
    s1 = lb.ref("s1", "( φ <-> ψ ) → ( φ → ψ )", ref="biimp", note="biimp")
    s2 = lb.mp("s2", h1, s1, "MP biimtrid.1, biimp")
    res = lb.ref("res", "χ → ( φ → θ )", s2, h2, ref="syl5", note="syl5")
    return lb.build(res)


def prove_biimtrrid(sys: System) -> Proof:
    """biimtrrid: ( ch -> ( ph -> th ) ).

    Hyp 1: ( ps <-> ph )
    Hyp 2: ( ch -> ( ps -> th ) )
    Concl: ( ch -> ( ph -> th ) )

    Inference from a biconditional and an implication, with the biconditional's
    right-hand side substituted into the first antecedent of the implication.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "biimtrrid")
    h1 = lb.hyp("biimtrrid.1", "( ps <-> ph )")
    h2 = lb.hyp("biimtrrid.2", "( ch -> ( ps -> th ) )")
    s1 = lb.ref("s1", "( ph -> ps )", h1, ref="biimpri", note="biimpri")
    res = lb.ref("res", "( ch -> ( ph -> th ) )", s1, h2, ref="syl5", note="syl5")
    return lb.build(res)


def prove_sylbi(sys: System) -> Proof:
    """sylbi: ( φ → χ ).

    Hyp 1: φ <-> ψ
    Hyp 2: ψ → χ

    A mixed syllogism inference from a biconditional and an implication.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "sylbi")
    h1 = lb.hyp("sylbi.1", "( φ <-> ψ )")
    h2 = lb.hyp("sylbi.2", "ψ → χ")
    s1 = lb.ref("s1", "( φ <-> ψ ) → ( φ → ψ )", ref="biimp", note="biimp")
    s2 = lb.mp("s2", h1, s1, "MP sylbi.1, biimp")
    # syl: ( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) )
    res = lb.ref("res", "φ → χ", s2, h2, ref="syl", note="syl")
    return lb.build(res)


def prove_sylbir(sys: System) -> Proof:
    """sylbir: ( φ → χ ).

    Hyp 1: ( ps <-> ph )
    Hyp 2: ps → χ

    A mixed syllogism inference from a biconditional and an implication,
    with the biconditional reversed.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sylbir")
    h1 = lb.hyp("sylbir.1", "( ps <-> ph )")
    h2 = lb.hyp("sylbir.2", "ps → χ")
    s1 = lb.ref("s1", "( ps <-> ph ) → ( ph → ps )", ref="biimpr", note="biimpr")
    s2 = lb.mp("s2", h1, s1, "MP sylbir.1, biimpr")
    res = lb.ref("res", "φ → χ", s2, h2, ref="syl", note="syl")
    return lb.build(res)


def prove_sylbb(sys: System) -> Proof:
    """sylbb: ( φ → χ ).

    Hyp 1: φ <-> ψ
    Hyp 2: ψ <-> χ

    A syllogism inference from two biconditionals.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sylbb")
    h1 = lb.hyp("sylbb.1", "( φ <-> ψ )")
    h2 = lb.hyp("sylbb.2", "( ψ <-> χ )")
    s1 = lb.ref("s1", "( ψ <-> χ ) → ( ψ → χ )", ref="biimp", note="biimp")
    s2 = lb.mp("s2", h2, s1, "MP sylbb.2, biimp")
    res = lb.ref("res", "φ → χ", h1, s2, ref="sylbi", note="sylbi")
    return lb.build(res)


def prove_sylbb2(sys: System) -> Proof:
    """sylbb2: ( φ → χ ).

    Hyp 1: φ <-> ψ
    Hyp 2: χ <-> ψ

    A syllogism inference from two biconditionals.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sylbb2")
    h1 = lb.hyp("sylbb2.1", "( φ <-> ψ )")
    h2 = lb.hyp("sylbb2.2", "( χ <-> ψ )")
    s1 = lb.ref("s1", "( χ <-> ψ ) → ( ψ → χ )", ref="biimpr", note="biimpr")
    s2 = lb.mp("s2", h2, s1, "MP sylbb2.2, biimpr")
    res = lb.ref("res", "φ → χ", h1, s2, ref="sylbi", note="sylbi")
    return lb.build(res)


def prove_sylbb1(sys: System) -> Proof:
    """sylbb1: ( ps -> ch ).

    Hyp 1: ( ph <-> ps )
    Hyp 2: ( ph <-> ch )

    A syllogism inference from two biconditionals.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sylbb1")
    h1 = lb.hyp("sylbb1.1", "( ph <-> ps )")
    h2 = lb.hyp("sylbb1.2", "( ph <-> ch )")
    s1 = lb.ref("s1", "( ph <-> ps ) → ( ps → ph )", ref="biimpr", note="biimpr")
    s2 = lb.mp("s2", h1, s1, "MP sylbb1.1, biimpr")
    res = lb.ref("res", "( ps → ch )", s2, h2, ref="sylib", note="sylib")
    return lb.build(res)


def prove_sylbbr(sys: System) -> Proof:
    """sylbbr: ( ch -> ph ).

    Hyp 1: ( ph <-> ps )
    Hyp 2: ( ps <-> ch )
    Concl: ( ch -> ph )

    A syllogism inference from two biconditionals (reverse).
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sylbbr")
    h1 = lb.hyp("sylbbr.1", "( ph <-> ps )")
    h2 = lb.hyp("sylbbr.2", "( ps <-> ch )")
    s1 = lb.ref("s1", "( ch -> ps )", h2, ref="biimpri", note="biimpri")
    res = lb.ref("res", "( ch -> ph )", s1, h1, ref="sylibr", note="sylibr")
    return lb.build(res)


def prove_sylbid(sys: System) -> Proof:
    """sylbid: φ → (ψ → θ).

    Hyp 1: φ → (ψ <-> χ)
    Hyp 2: φ → (χ → θ)

    A mixed syllogism inference from a biconditional and an implication.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sylbid")
    h1 = lb.hyp("sylbid.1", "φ → ( ψ <-> χ )")
    h2 = lb.hyp("sylbid.2", "φ → ( χ → θ )")
    s1 = lb.ref("s1", "φ → ( ψ → χ )", h1, ref="biimpd", note="biimpd sylbid.1")
    res = lb.ref("res", "φ → ( ψ → θ )", s1, h2, ref="syld", note="syld")
    return lb.build(res)


def prove_sylbird(sys: System) -> Proof:
    """sylbird: φ → ( ψ → θ ).

    Hyp 1: φ → ( χ <-> ψ )
    Hyp 2: φ → ( χ → θ )

    A mixed syllogism inference from a biconditional and an implication.
    This is the reverse of sylbid, using biimprd instead of biimpd.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sylbird")
    h1 = lb.hyp("sylbird.1", "φ → ( χ <-> ψ )")
    h2 = lb.hyp("sylbird.2", "φ → ( χ → θ )")
    s1 = lb.ref("s1", "φ → ( ψ → χ )", h1, ref="biimprd", note="biimprd sylbird.1")
    res = lb.ref("res", "φ → ( ψ → θ )", s1, h2, ref="syld", note="syld")
    return lb.build(res)


def prove_sylbida(sys: System) -> Proof:
    """sylbida: ( φ ∧ ψ ) → θ.

    Hyp 1: φ → ( ψ ↔ χ )
    Hyp 2: ( φ ∧ χ ) → θ

    A mixed syllogism inference from a biconditional and an implication,
    with a common antecedent.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sylbida")
    h1 = lb.hyp("sylbida.1", "φ → ( ψ ↔ χ )")
    h2 = lb.hyp("sylbida.2", "( φ ∧ χ ) → θ")
    s1 = lb.ref("s1", "( φ ∧ ψ ) → χ", h1, ref="biimpa", note="biimpa sylbida.1")
    res = lb.ref("res", "( φ ∧ ψ ) → θ", s1, h2, ref="syldan", note="syldan")
    return lb.build(res)


def prove_peirceroll(sys: System) -> Proof:
    """peirceroll: ( ( ( ( ph -> ps ) -> ph ) -> ph ) -> ( ( ( ph -> ps ) -> ch ) -> ( ( ch -> ph ) -> ph ) ) ).

    A theorem related to Peirce's law.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "peirceroll")
    s1 = lb.ref(
        "s1",
        "( ( ph -> ps ) -> ch ) -> ( ( ch -> ph ) -> ( ( ph -> ps ) -> ph ) )",
        ref="imim1",
        note="imim1",
    )
    s2 = lb.ref(
        "s2",
        "( ( ( ph -> ps ) -> ph ) -> ph ) -> ( ( ( ph -> ps ) -> ph ) -> ph )",
        ref="id",
        note="id",
    )
    res = lb.ref(
        "res",
        "( ( ( ph -> ps ) -> ph ) -> ph ) -> ( ( ( ph -> ps ) -> ch ) -> ( ( ch -> ph ) -> ph ) )",
        s1,
        s2,
        ref="syl9r",
        note="syl9r",
    )
    return lb.build(res)


def prove_com5l(sys: System) -> Proof:
    """com5l: ps → (ch → (th → (ta → (ph → et)))).

    Hyp: ph → (ps → (ch → (th → (ta → et))))
    Concl: ps → (ch → (th → (ta → (ph → et))))

    Commutation of antecedents.  Rotate left.
    (Contributed by NM, 27-Dec-1992.)
    """
    lb = ProofBuilder(sys, "com5l")
    h = lb.hyp("com5l.1", "ph → ( ps → ( ch → ( th → ( ta → et ) ) ) )")
    s1 = lb.ref(
        "s1",
        "ps → ( ch → ( th → ( ph → ( ta → et ) ) ) )",
        h,
        ref="com4l",
        note="com4l",
    )
    res = lb.ref(
        "res",
        "ps → ( ch → ( th → ( ta → ( ph → et ) ) ) )",
        s1,
        ref="com45",
        note="com45",
    )
    return lb.build(res)


def prove_com15(sys: System) -> Proof:
    """com15: ta → (ps → (ch → (th → (ph → et)))).

    Hyp: ph → (ps → (ch → (th → (ta → et))))
    Concl: ta → (ps → (ch → (th → (ph → et))))

    Commutation of antecedents.  Swap 1st and 5th.
    (Contributed by Jeff Hankins, 28-Jun-2009.)
    (Proof shortened by Wolf Lammen, 29-Jul-2012.)
    """
    lb = ProofBuilder(sys, "com15")
    h = lb.hyp("com15.1", "ph → ( ps → ( ch → ( th → ( ta → et ) ) ) )")
    s1 = lb.ref(
        "s1",
        "ps → ( ch → ( th → ( ta → ( ph → et ) ) ) )",
        h,
        ref="com5l",
        note="com5l",
    )
    res = lb.ref(
        "res",
        "ta → ( ps → ( ch → ( th → ( ph → et ) ) ) )",
        s1,
        ref="com4r",
        note="com4r",
    )
    return lb.build(res)


def prove_com52l(sys: System) -> Proof:
    """com52l: ch → (th → (ta → (ph → (ps → et)))).

    Hyp: ph → (ps → (ch → (th → (ta → et))))
    Concl: ch → (th → (ta → (ph → (ps → et))))

    Commutation of antecedents.  Rotate right.
    (Contributed by NM, 25-Apr-1994.)
    """
    lb = ProofBuilder(sys, "com52l")
    h = lb.hyp("com52l.1", "ph → ( ps → ( ch → ( th → ( ta → et ) ) ) )")
    s1 = lb.ref(
        "s1",
        "ps → ( ch → ( th → ( ta → ( ph → et ) ) ) )",
        h,
        ref="com5l",
        note="com5l com52l.1",
    )
    res = lb.ref(
        "res",
        "ch → ( th → ( ta → ( ph → ( ps → et ) ) ) )",
        s1,
        ref="com5l",
        note="com5l s1",
    )
    return lb.build(res)


def prove_com52r(sys: System) -> Proof:
    """com52r: th → (ta → (ph → (ps → (ch → et))).

    Hyp: ph → (ps → (ch → (th → (ta → et))))
    Concl: th → (ta → (ph → (ps → (ch → et))))

    Commutation of antecedents.  Rotate right.
    (Contributed by NM, 25-Apr-1994.)
    """
    lb = ProofBuilder(sys, "com52r")
    h = lb.hyp("com52r.1", "ph → ( ps → ( ch → ( th → ( ta → et ) ) ) )")
    s1 = lb.ref(
        "s1",
        "ch → ( th → ( ta → ( ph → ( ps → et ) ) ) )",
        h,
        ref="com52l",
        note="com52l",
    )
    res = lb.ref(
        "res",
        "th → ( ta → ( ph → ( ps → ( ch → et ) ) ) )",
        s1,
        ref="com5l",
        note="com5l",
    )
    return lb.build(res)


def prove_com5r(sys: System) -> Proof:
    """com5r: ta → (ph → (ps → (ch → (th → et)))).

    Hyp: ph → (ps → (ch → (th → (ta → et))))
    Concl: ta → (ph → (ps → (ch → (th → et))))

    Commutation of antecedents.  Rotate right.
    (Contributed by NM, 25-Apr-1994.)
    """
    lb = ProofBuilder(sys, "com5r")
    h = lb.hyp("com5r.1", "ph → ( ps → ( ch → ( th → ( ta → et ) ) ) )")
    s1 = lb.ref(
        "s1",
        "ch → ( th → ( ta → ( ph → ( ps → et ) ) ) )",
        h,
        ref="com52l",
        note="com52l",
    )
    res = lb.ref(
        "res",
        "ta → ( ph → ( ps → ( ch → ( th → et ) ) ) )",
        s1,
        ref="com52l",
        note="com52l",
    )
    return lb.build(res)


def prove_minimp(sys: System) -> Proof:
    """minimp: φ → ((ψ → χ) → (((θ → ψ) → (χ → τ)) → (ψ → τ))).

    Derivation of the minimal implicational calculus from {ax-1, ax-2}.
    This section proves that the implicational fragment avoids ax-3.
    (Contributed by NM, 4-Apr-2021.)

    set.mm proof: wi jarr a2d com12 a1i.
    """
    lb = ProofBuilder(sys, "minimp")
    s1 = lb.ref(
        "s1",
        "( ( θ → ψ ) → ( χ → τ ) ) → ( ψ → ( χ → τ ) )",
        ref="jarr",
        note="jarr",
    )
    s2 = lb.ref(
        "s2",
        "( ( θ → ψ ) → ( χ → τ ) ) → ( ( ψ → χ ) → ( ψ → τ ) )",
        s1,
        ref="a2d",
        note="a2d",
    )
    s3 = lb.ref(
        "s3",
        "( ψ → χ ) → ( ( ( θ → ψ ) → ( χ → τ ) ) → ( ψ → τ ) )",
        s2,
        ref="com12",
        note="com12",
    )
    res = lb.ref(
        "res",
        "φ → ( ( ψ → χ ) → ( ( ( θ → ψ ) → ( χ → τ ) ) → ( ψ → τ ) ) )",
        s3,
        ref="a1i",
        note="a1i",
    )
    return lb.build(res)


def prove_minimp_syllsimp(sys: System) -> Proof:
    """minimp-syllsimp: ( ( ( ph → ps ) → ch ) → ( ps → ch ) ).

    Derivation of syll-simp from minimp and ax-mp.
    (Contributed by BJ, 4-Apr-2021.)
    """
    lb = ProofBuilder(sys, "minimp-syllsimp")

    s1 = lb.ref(
        "s1",
        "( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( ( φ → ψ ) → χ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) )",
        ref="minimp",
        note="minimp",
    )

    s2 = lb.ref(
        "s2",
        "( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( ( φ → ψ ) → χ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( ( φ → ψ ) → χ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( ( φ → ψ ) → χ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) ) → ( ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( ( φ → ψ ) → χ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( ( φ → ψ ) → χ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( ( φ → ψ ) → χ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( ( φ → ψ ) → χ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( ( φ → ψ ) → χ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( ( φ → ψ ) → χ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) ) ) ) )",
        ref="minimp",
        note="minimp",
    )

    s3 = lb.ref(
        "s3",
        "( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( ( φ → ψ ) → χ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( ( φ → ψ ) → χ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( ( φ → ψ ) → χ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) ) → ( ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( ( φ → ψ ) → χ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( ( φ → ψ ) → χ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( ( φ → ψ ) → χ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( ( φ → ψ ) → χ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( ( φ → ψ ) → χ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( ( φ → ψ ) → χ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) ) ) ) ) → ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( ( φ → ψ ) → χ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) ) → ( ( ( ( φ → ψ ) → ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( ( φ → ψ ) → χ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( ( φ → ψ ) → χ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) ) ) )",
        ref="minimp",
        note="minimp",
    )

    s4 = lb.mp("s4", s2, s3, "ax-mp")

    s5 = lb.ref(
        "s5",
        "( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) ) → ( ( ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) ) → ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) ) ) → ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) ) ) ) )",
        ref="minimp",
        note="minimp",
    )

    s6 = lb.ref(
        "s6",
        "( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( ( φ → ψ ) → χ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) )",
        ref="minimp",
        note="minimp",
    )

    s7 = lb.ref(
        "s7",
        "( ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) ) → ( ( ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) ) → ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) ) ) → ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) ) ) ) ) → ( ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( ( φ → ψ ) → χ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) ) → ( ( ( ( ( φ → ψ ) → ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( ( φ → ψ ) → χ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( ( φ → ψ ) → χ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) ) → ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( φ → ψ ) → χ ) ) ) ) )",
        ref="minimp",
        note="minimp",
    )

    s8 = lb.ref(
        "s8",
        "( ( ( ( ( φ → ψ ) → ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( ( φ → ψ ) → χ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( ( φ → ψ ) → χ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) ) → ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( φ → ψ ) → χ ) ) )",
        s5,
        s6,
        s7,
        ref="mp2",
        note="mp2",
    )

    s9 = lb.ref(
        "s9",
        "( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( φ → ψ ) → χ ) )",
        s1,
        s4,
        s8,
        ref="mp2b",
        note="mp2b",
    )

    s10 = lb.ref(
        "s10",
        "( ( φ → ψ ) → ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) )",
        ref="minimp",
        note="minimp",
    )

    s11 = lb.ref(
        "s11",
        "( ( ( φ → ψ ) → ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) ) → ( ( ( φ → ψ ) → ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( φ → ψ ) → χ ) ) ) → ( ( ( ( ( φ → ψ ) → χ ) → ( φ → ψ ) ) → ( ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( φ → ψ ) → χ ) ) → ( ( ( φ → ψ ) → χ ) → χ ) ) ) → ( ( φ → ψ ) → ( ( ( φ → ψ ) → χ ) → χ ) ) ) ) )",
        ref="minimp",
        note="minimp",
    )

    s12 = lb.ref(
        "s12",
        "( ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( φ → ψ ) → χ ) ) → ( ( ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( φ → ψ ) → χ ) ) → ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( φ → ψ ) → χ ) ) ) → ( ( ( ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( φ → ψ ) → χ ) ) → ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( φ → ψ ) → χ ) ) ) → ( ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( φ → ψ ) → χ ) ) → ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( φ → ψ ) → χ ) ) ) ) → ( ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( φ → ψ ) → χ ) ) → ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( φ → ψ ) → χ ) ) ) ) ) )",
        ref="minimp",
        note="minimp",
    )

    s13 = lb.ref(
        "s13",
        "( ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( φ → ψ ) → χ ) ) → ( ( ( ( φ → ψ ) → χ ) → ( φ → ψ ) ) → ( ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( φ → ψ ) → χ ) ) → ( ( ( φ → ψ ) → χ ) → χ ) ) ) )",
        ref="minimp",
        note="minimp",
    )

    s14 = lb.ref(
        "s14",
        "( ( ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( φ → ψ ) → χ ) ) → ( ( ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( φ → ψ ) → χ ) ) → ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( φ → ψ ) → χ ) ) ) → ( ( ( ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( φ → ψ ) → χ ) ) → ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( φ → ψ ) → χ ) ) ) → ( ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( φ → ψ ) → χ ) ) → ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( φ → ψ ) → χ ) ) ) ) → ( ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( φ → ψ ) → χ ) ) → ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( φ → ψ ) → χ ) ) ) ) ) ) → ( ( ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( φ → ψ ) → χ ) ) → ( ( ( ( φ → ψ ) → χ ) → ( φ → ψ ) ) → ( ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( φ → ψ ) → χ ) ) → ( ( ( φ → ψ ) → χ ) → χ ) ) ) ) → ( ( ( ( φ → ψ ) → ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( φ → ψ ) → χ ) ) ) → ( ( ( ( ( φ → ψ ) → χ ) → ( φ → ψ ) ) → ( ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( φ → ψ ) → χ ) ) → ( ( ( φ → ψ ) → χ ) → χ ) ) ) → ( ( φ → ψ ) → ( ( ( φ → ψ ) → χ ) → χ ) ) ) ) → ( ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( φ → ψ ) → χ ) ) → ( ( φ → ψ ) → ( ( ( φ → ψ ) → χ ) → χ ) ) ) ) ) )",
        ref="minimp",
        note="minimp",
    )

    s15 = lb.ref(
        "s15",
        "( ( ( ( φ → ψ ) → ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( φ → ψ ) → χ ) ) ) → ( ( ( ( ( φ → ψ ) → χ ) → ( φ → ψ ) ) → ( ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( φ → ψ ) → χ ) ) → ( ( ( φ → ψ ) → χ ) → χ ) ) ) → ( ( φ → ψ ) → ( ( ( φ → ψ ) → χ ) → χ ) ) ) ) → ( ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( φ → ψ ) → χ ) ) → ( ( φ → ψ ) → ( ( ( φ → ψ ) → χ ) → χ ) ) ) )",
        s12,
        s13,
        s14,
        ref="mp2",
        note="mp2",
    )

    s16 = lb.ref(
        "s16",
        "( ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) → ( ( φ → ψ ) → χ ) ) → ( ( φ → ψ ) → χ ) ) → ( ( φ → ψ ) → ( ( ( φ → ψ ) → χ ) → χ ) ) )",
        s10,
        s11,
        s15,
        ref="mp2b",
        note="mp2b",
    )

    s17 = lb.ref(
        "s17",
        "( ( ( φ → ψ ) → χ ) → ( ( ( ( φ → ψ ) → χ ) → ( ( φ → ψ ) → χ ) ) → ( ( ( ( ( φ → ψ ) → χ ) → ( ( φ → ψ ) → χ ) ) → ( ( ( φ → ψ ) → χ ) → ( ( φ → ψ ) → χ ) ) ) → ( ( ( φ → ψ ) → χ ) → ( ( φ → ψ ) → χ ) ) ) ) )",
        ref="minimp",
        note="minimp",
    )

    s18 = lb.ref(
        "s18",
        "( ( ( ( φ → ψ ) → χ ) → ( ( ( ( φ → ψ ) → χ ) → ( ( φ → ψ ) → χ ) ) → ( ( ( ( ( φ → ψ ) → χ ) → ( ( φ → ψ ) → χ ) ) → ( ( ( φ → ψ ) → χ ) → ( ( φ → ψ ) → χ ) ) ) → ( ( ( φ → ψ ) → χ ) → ( ( φ → ψ ) → χ ) ) ) ) ) → ( ( ( ( φ → ψ ) → χ ) → ( ( φ → ψ ) → ( ( ( φ → ψ ) → χ ) → χ ) ) ) → ( ( ( ψ → ( ( φ → ψ ) → χ ) ) → ( ( ( φ → ψ ) → ( ( ( φ → ψ ) → χ ) → χ ) ) → ( ψ → χ ) ) ) → ( ( ( φ → ψ ) → χ ) → ( ψ → χ ) ) ) ) )",
        ref="minimp",
        note="minimp",
    )

    s19 = lb.ref(
        "s19",
        "( ( ( φ → ψ ) → ( ( ( φ → ψ ) → χ ) → χ ) ) → ( ( ( ( φ → ψ ) → ( ( ( φ → ψ ) → χ ) → χ ) ) → ( ( φ → ψ ) → ( ( ( φ → ψ ) → χ ) → χ ) ) ) → ( ( ( ( ( φ → ψ ) → ( ( ( φ → ψ ) → χ ) → χ ) ) → ( ( φ → ψ ) → ( ( ( φ → ψ ) → χ ) → χ ) ) ) → ( ( ( φ → ψ ) → ( ( ( φ → ψ ) → χ ) → χ ) ) → ( ( φ → ψ ) → ( ( ( φ → ψ ) → χ ) → χ ) ) ) ) → ( ( ( φ → ψ ) → ( ( ( φ → ψ ) → χ ) → χ ) ) → ( ( φ → ψ ) → ( ( ( φ → ψ ) → χ ) → χ ) ) ) ) ) )",
        ref="minimp",
        note="minimp",
    )

    s20 = lb.ref(
        "s20",
        "( ( ( φ → ψ ) → ( ( ( φ → ψ ) → χ ) → χ ) ) → ( ( ψ → ( ( φ → ψ ) → χ ) ) → ( ( ( φ → ψ ) → ( ( ( φ → ψ ) → χ ) → χ ) ) → ( ψ → χ ) ) ) )",
        ref="minimp",
        note="minimp",
    )

    s21 = lb.ref(
        "s21",
        "( ( ( ( φ → ψ ) → ( ( ( φ → ψ ) → χ ) → χ ) ) → ( ( ( ( φ → ψ ) → ( ( ( φ → ψ ) → χ ) → χ ) ) → ( ( φ → ψ ) → ( ( ( φ → ψ ) → χ ) → χ ) ) ) → ( ( ( ( ( φ → ψ ) → ( ( ( φ → ψ ) → χ ) → χ ) ) → ( ( φ → ψ ) → ( ( ( φ → ψ ) → χ ) → χ ) ) ) → ( ( ( φ → ψ ) → ( ( ( φ → ψ ) → χ ) → χ ) ) → ( ( φ → ψ ) → ( ( ( φ → ψ ) → χ ) → χ ) ) ) ) → ( ( ( φ → ψ ) → ( ( ( φ → ψ ) → χ ) → χ ) ) → ( ( φ → ψ ) → ( ( ( φ → ψ ) → χ ) → χ ) ) ) ) ) ) → ( ( ( ( φ → ψ ) → ( ( ( φ → ψ ) → χ ) → χ ) ) → ( ( ψ → ( ( φ → ψ ) → χ ) ) → ( ( ( φ → ψ ) → ( ( ( φ → ψ ) → χ ) → χ ) ) → ( ψ → χ ) ) ) ) → ( ( ( ( ( φ → ψ ) → χ ) → ( ( φ → ψ ) → ( ( ( φ → ψ ) → χ ) → χ ) ) ) → ( ( ( ψ → ( ( φ → ψ ) → χ ) ) → ( ( ( φ → ψ ) → ( ( ( φ → ψ ) → χ ) → χ ) ) → ( ψ → χ ) ) ) → ( ( ( φ → ψ ) → χ ) → ( ψ → χ ) ) ) ) → ( ( ( φ → ψ ) → ( ( ( φ → ψ ) → χ ) → χ ) ) → ( ( ( φ → ψ ) → χ ) → ( ψ → χ ) ) ) ) ) )",
        ref="minimp",
        note="minimp",
    )

    s22 = lb.ref(
        "s22",
        "( ( ( ( ( φ → ψ ) → χ ) → ( ( φ → ψ ) → ( ( ( φ → ψ ) → χ ) → χ ) ) ) → ( ( ( ψ → ( ( φ → ψ ) → χ ) ) → ( ( ( φ → ψ ) → ( ( ( φ → ψ ) → χ ) → χ ) ) → ( ψ → χ ) ) ) → ( ( ( φ → ψ ) → χ ) → ( ψ → χ ) ) ) ) → ( ( ( φ → ψ ) → ( ( ( φ → ψ ) → χ ) → χ ) ) → ( ( ( φ → ψ ) → χ ) → ( ψ → χ ) ) ) )",
        s19,
        s20,
        s21,
        ref="mp2",
        note="mp2",
    )

    s23 = lb.ref(
        "s23",
        "( ( ( φ → ψ ) → ( ( ( φ → ψ ) → χ ) → χ ) ) → ( ( ( φ → ψ ) → χ ) → ( ψ → χ ) ) )",
        s17,
        s18,
        s22,
        ref="mp2b",
        note="mp2b",
    )

    s24 = lb.ref(
        "s24",
        "( ( ( φ → ψ ) → χ ) → ( ψ → χ ) )",
        s9,
        s16,
        s23,
        ref="mp2b",
        note="mp2b",
    )
    return lb.build(s24)


def prove_minimp_ax2c(sys: System) -> Proof:
    """minimp-ax2c: ( ( φ → ψ ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ).

    Derivation of ~ ax-2 from ~ minimp and ~ minimp-syllsimp .
    (Contributed by BJ, 4-Apr-2021.)
    """
    lb = ProofBuilder(sys, "minimp-ax2c")

    s0 = lb.ref(
        "s0",
        "( φ → ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) )",
        ref="minimp",
        note="minimp",
    )
    s1 = lb.ref(
        "s1",
        "( ( φ → ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) ) → ( ( φ → ψ ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) ) )",
        ref="minimp",
        note="minimp",
    )
    s2 = lb.mp("s2", s0, s1, "ax-mp")
    s3 = lb.ref(
        "s3",
        "( ( φ → ( ψ → χ ) ) → ( ( ( φ → ( ψ → χ ) ) → ( φ → ( ψ → χ ) ) ) → ( ( ( ( φ → ( ψ → χ ) ) → ( φ → ( ψ → χ ) ) ) → ( ( φ → ( ψ → χ ) ) → ( φ → ( ψ → χ ) ) ) ) → ( ( φ → ( ψ → χ ) ) → ( φ → ( ψ → χ ) ) ) ) ) )",
        ref="minimp",
        note="minimp",
    )
    s4 = lb.ref(
        "s4",
        "( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) ) → ( ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) ) → ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) ) ) → ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) ) ) ) )",
        ref="minimp",
        note="minimp",
    )
    s5 = lb.ref(
        "s5",
        "( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) )",
        ref="minimp",
        note="minimp",
    )
    s6 = lb.ref(
        "s6",
        "( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) ) → ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) ) ) → ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) ) ) ) )",
        ref="minimp",
        note="minimp",
    )
    s7 = lb.ref(
        "s7",
        "( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) )",
        ref="minimp",
        note="minimp",
    )
    s8 = lb.ref(
        "s8",
        "( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) ) → ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) ) ) → ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) ) ) ) ) → ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) ) → ( ( ( φ → ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) ) → ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) ) → ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) ) ) )",
        ref="minimp",
        note="minimp",
    )
    s9 = lb.ref(
        "s9",
        "( ( ( φ → ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) ) → ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) ) → ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) )",
        s6,
        s7,
        s8,
        ref="mp2",
        note="mp2",
    )
    s10 = lb.ref(
        "s10",
        "( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) ) → ( ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) ) → ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) ) ) → ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) ) ) ) )",
        ref="minimp",
        note="minimp",
    )
    s11 = lb.ref(
        "s11",
        "( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) ) → ( ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) ) → ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) ) ) → ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) ) ) ) ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) ) → ( ( ( ( φ → ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) ) → ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) ) → ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) ) → ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → φ ) ) ) )",
        ref="minimp",
        note="minimp",
    )
    s12 = lb.mp("s12", s10, s11, "ax-mp")
    s13 = lb.ref(
        "s13",
        "( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → φ )",
        s5,
        s9,
        s12,
        ref="mp2",
        note="mp2",
    )
    s14 = lb.ref(
        "s14",
        "( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) ) → ( ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) ) → ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) ) ) → ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) ) ) ) ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → φ ) → ( ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) ) → ( φ → ( ψ → χ ) ) ) → ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) ) ) )",
        ref="minimp",
        note="minimp",
    )
    s15 = lb.ref(
        "s15",
        "( ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) ) → ( φ → ( ψ → χ ) ) ) → ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) )",
        s4,
        s13,
        s14,
        ref="mp2",
        note="mp2",
    )
    s16 = lb.ref(
        "s16",
        "( ( ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) ) → ( φ → ( ψ → χ ) ) ) → ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) ) → ( ( φ → ( ψ → χ ) ) → ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) ) )",
        ref="minimp-syllsimp",
        note="minimp-syllsimp",
    )
    s17 = lb.mp("s17", s15, s16, "ax-mp")
    s18 = lb.ref(
        "s18",
        "( ( ( φ → ( ψ → χ ) ) → ( ( ( φ → ( ψ → χ ) ) → ( φ → ( ψ → χ ) ) ) → ( ( ( ( φ → ( ψ → χ ) ) → ( φ → ( ψ → χ ) ) ) → ( ( φ → ( ψ → χ ) ) → ( φ → ( ψ → χ ) ) ) ) → ( ( φ → ( ψ → χ ) ) → ( φ → ( ψ → χ ) ) ) ) ) ) → ( ( ( φ → ( ψ → χ ) ) → ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) ) → ( ( ( ( φ → ( ψ → χ ) ) → ( φ → ( ψ → χ ) ) ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) ) )",
        ref="minimp",
        note="minimp",
    )
    s19 = lb.ref(
        "s19",
        "( ( ( ( φ → ( ψ → χ ) ) → ( φ → ( ψ → χ ) ) ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) )",
        s3,
        s17,
        s18,
        ref="mp2",
        note="mp2",
    )
    s20 = lb.ref(
        "s20",
        "( ( ( ( ( φ → ( ψ → χ ) ) → ( φ → ( ψ → χ ) ) ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) )",
        ref="minimp-syllsimp",
        note="minimp-syllsimp",
    )
    s21 = lb.mp("s21", s19, s20, "ax-mp")
    s22 = lb.ref(
        "s22",
        "( ( ( φ → ψ ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( ( ( φ → ψ ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( φ → ψ ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) ) ) → ( ( ( ( ( φ → ψ ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( φ → ψ ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) ) ) → ( ( ( φ → ψ ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( φ → ψ ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) ) ) ) → ( ( ( φ → ψ ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( φ → ψ ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) ) ) ) ) )",
        ref="minimp",
        note="minimp",
    )
    s23 = lb.ref(
        "s23",
        "( ( φ → ψ ) → ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) )",
        ref="minimp",
        note="minimp",
    )
    s24 = lb.ref(
        "s24",
        "( ( ( φ → ψ ) → ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ψ ) ) ) ) ) → ( ( ( φ → ψ ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) ) → ( ( φ → ψ ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) ) ) )",
        ref="minimp",
        note="minimp",
    )
    s25 = lb.mp("s25", s23, s24, "ax-mp")
    s26 = lb.ref(
        "s26",
        "( ( ( ( φ → ψ ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( ( ( φ → ψ ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( φ → ψ ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) ) ) → ( ( ( ( ( φ → ψ ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( φ → ψ ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) ) ) → ( ( ( φ → ψ ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( φ → ψ ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) ) ) ) → ( ( ( φ → ψ ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( φ → ψ ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) ) ) ) ) ) → ( ( ( ( φ → ψ ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) ) → ( ( φ → ψ ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) ) ) → ( ( ( ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) → ( ( φ → ψ ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) ) ) → ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) ) → ( ( φ → ψ ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) ) → ( ( ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( φ → ψ ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) ) ) ) → ( ( ( φ → ψ ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( φ → ψ ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) ) ) ) ) )",
        ref="minimp",
        note="minimp",
    )
    s27 = lb.ref(
        "s27",
        "( ( ( ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) → ( ( φ → ψ ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) ) ) → ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) ) → ( ( φ → ψ ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) ) → ( ( ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( φ → ψ ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) ) ) ) → ( ( ( φ → ψ ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( φ → ψ ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) ) ) )",
        s22,
        s25,
        s26,
        ref="mp2",
        note="mp2",
    )
    s28 = lb.ref(
        "s28",
        "( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) ) → ( ( φ → ψ ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) ) → ( ( ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( φ → ψ ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) ) )",
        ref="minimp-syllsimp",
        note="minimp-syllsimp",
    )
    s29 = lb.ref(
        "s29",
        "( ( ( ( ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) → ( ( φ → ψ ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) ) ) → ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) ) → ( ( φ → ψ ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) ) → ( ( ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( φ → ψ ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) ) ) ) → ( ( ( φ → ψ ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( φ → ψ ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) ) ) ) → ( ( ( ( ( ( φ → ψ ) → ( φ → ψ ) ) → ( ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) ) → ( ( φ → ψ ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) ) → ( ( ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( φ → ψ ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) ) ) → ( ( ( φ → ψ ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( φ → ψ ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) ) ) ) )",
        ref="minimp-syllsimp",
        note="minimp-syllsimp",
    )
    s30 = lb.ref(
        "s30",
        "( ( ( φ → ψ ) → ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( ( ( ( ( ( φ → φ ) → ( ( ( φ → φ ) → ( φ → φ ) ) → ( φ → φ ) ) ) → φ ) → ( ψ → χ ) ) → ( φ → χ ) ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( φ → ψ ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) ) )",
        s27,
        s28,
        s29,
        ref="mp2",
        note="mp2",
    )
    s31 = lb.ref(
        "s31",
        "( ( φ → ψ ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) )",
        s2,
        s21,
        s30,
        ref="mp2",
        note="mp2",
    )

    return lb.build(s31)


def prove_minimp_ax2(sys: System) -> Proof:
    """minimp-ax2: ( φ → ( ψ → χ ) ) → ( ( φ → ψ ) → ( φ → χ ) ).

    Derivation of ax-2 from minimp-ax2c, minimp-syllsimp, and ax-mp.
    (Contributed by BJ, 4-Apr-2021.)  (Proof shortened by BJ,
    11-Apr-2021.)
    """
    lb = ProofBuilder(sys, "minimp-ax2")
    s1 = lb.ref(
        "s1",
        "( φ → ψ ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) )",
        ref="minimp-ax2c",
        note="minimp-ax2c",
    )
    s2 = lb.ref(
        "s2",
        "( ( φ → ψ ) → ( φ → ( ψ → χ ) ) ) → ( ( ( φ → ψ ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( φ → ψ ) → ( φ → χ ) ) )",
        ref="minimp-ax2c",
        note="minimp-ax2c",
    )
    s3 = lb.ref(
        "s3",
        "( ( ( ( φ → ψ ) → ( φ → ( ψ → χ ) ) ) → ( ( ( φ → ψ ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( φ → ψ ) → ( φ → χ ) ) ) ) → ( ( φ → ( ψ → χ ) ) → ( ( ( φ → ψ ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( φ → ψ ) → ( φ → χ ) ) ) ) )",
        ref="minimp-syllsimp",
        note="minimp-syllsimp",
    )
    s4 = lb.mp("s4", s2, s3, "ax-mp")
    s5 = lb.ref(
        "s5",
        "( ( φ → ( ψ → χ ) ) → ( ( φ → ψ ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) ) → ( ( ( φ → ( ψ → χ ) ) → ( ( ( φ → ψ ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( φ → ψ ) → ( φ → χ ) ) ) ) → ( ( φ → ( ψ → χ ) ) → ( ( φ → ψ ) → ( φ → χ ) ) ) )",
        ref="minimp-ax2c",
        note="minimp-ax2c",
    )
    s6 = lb.ref(
        "s6",
        "( ( ( φ → ( ψ → χ ) ) → ( ( φ → ψ ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) ) → ( ( ( φ → ( ψ → χ ) ) → ( ( ( φ → ψ ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( φ → ψ ) → ( φ → χ ) ) ) ) → ( ( φ → ( ψ → χ ) ) → ( ( φ → ψ ) → ( φ → χ ) ) ) ) ) → ( ( ( φ → ψ ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( ( φ → ( ψ → χ ) ) → ( ( ( φ → ψ ) → ( ( φ → ( ψ → χ ) ) → ( φ → χ ) ) ) → ( ( φ → ψ ) → ( φ → χ ) ) ) ) → ( ( φ → ( ψ → χ ) ) → ( ( φ → ψ ) → ( φ → χ ) ) ) ) )",
        ref="minimp-syllsimp",
        note="minimp-syllsimp",
    )
    s7 = lb.mp("s7", s5, s6, "ax-mp")
    res = lb.ref(
        "res",
        "( φ → ( ψ → χ ) ) → ( ( φ → ψ ) → ( φ → χ ) )",
        s1,
        s4,
        s7,
        ref="mp2",
        note="mp2",
    )
    return lb.build(res)


def prove_minimp_ax1(sys: System) -> Proof:
    """minimp-ax1: φ → (ψ → φ).

    Derivation of ax-1 from minimp and ax-mp.
    (Contributed by BJ, 4-Apr-2021.)
    """
    lb = ProofBuilder(sys, "minimp-ax1")

    s1 = lb.ref(
        "s1",
        "( ( ( φ → ψ ) → φ ) → ( ψ → φ ) )",
        ref="minimp-syllsimp",
        note="minimp-syllsimp",
    )

    s2 = lb.ref(
        "s2",
        "( ( ( ( φ → ψ ) → φ ) → ( ψ → φ ) ) → ( φ → ( ψ → φ ) ) )",
        ref="minimp-syllsimp",
        note="minimp-syllsimp",
    )

    s3 = lb.mp("s3", s1, s2, "MP s1, s2")

    return lb.build(s3)


def prove_minimp_pm2_43(sys: System) -> Proof:
    """minimp-pm2.43: ( φ → ( φ → ψ ) ) → ( φ → ψ ).

    Derivation of pm2.43 from minimp-ax2, minimp-ax1, ax-mp, and mp2.
    (Contributed by BJ, 4-Apr-2021.)
    """
    lb = ProofBuilder(sys, "minimp-pm2.43")

    s1 = lb.ref(
        "s1",
        "( φ → ( φ → ψ ) ) → ( ( φ → φ ) → ( φ → ψ ) )",
        ref="minimp-ax2",
        note="minimp-ax2",
    )

    s2 = lb.ref(
        "s2",
        "φ → ( ( φ → ψ ) → φ )",
        ref="minimp-ax1",
        note="minimp-ax1",
    )

    s3 = lb.ref(
        "s3",
        "( φ → ( ( φ → ψ ) → φ ) ) → ( ( φ → ( φ → ψ ) ) → ( φ → φ ) )",
        ref="minimp-ax2",
        note="minimp-ax2",
    )

    s4 = lb.mp("s4", s2, s3, "MP s2, s3")

    s5 = lb.ref(
        "s5",
        "( ( φ → ( φ → ψ ) ) → ( ( φ → φ ) → ( φ → ψ ) ) ) → ( ( ( φ → ( φ → ψ ) ) → ( φ → φ ) ) → ( ( φ → ( φ → ψ ) ) → ( φ → ψ ) ) )",
        ref="minimp-ax2",
        note="minimp-ax2",
    )

    res = lb.ref(
        "res",
        "( φ → ( φ → ψ ) ) → ( φ → ψ )",
        s1,
        s4,
        s5,
        ref="mp2",
        note="mp2",
    )

    return lb.build(res)


def prove_merlem2(sys: System) -> Proof:
    """merlem2: ( ( ( φ → φ ) → χ ) → ( θ → χ ) ).

    Second lemma towards deriving the Łukasiewicz axioms from Meredith's
    sole axiom.  (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "merlem2")

    s1 = lb.ref(
        "s1",
        "( ( ( ( χ → χ ) → ( ¬ φ → ¬ θ ) ) → φ ) → ( φ → φ ) )",
        ref="merlem1",
        note="merlem1",
    )

    s2 = lb.ref(
        "s2",
        "( ( ( ( ( χ → χ ) → ( ¬ φ → ¬ θ ) ) → φ ) → ( φ → φ ) ) → ( ( ( φ → φ ) → χ ) → ( θ → χ ) ) )",
        ref="meredith",
        note="meredith",
    )

    res = lb.mp("res", s1, s2, note="ax-mp")
    return lb.build(res)


def prove_merlem3(sys: System) -> Proof:
    """merlem3: ( ( ( ψ → χ ) → φ ) → ( χ → φ ) ).

    Third lemma towards deriving the Łukasiewicz axioms from Meredith's
    sole axiom.  (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "merlem3")

    s1 = lb.ref(
        "s1",
        "( ( ( ¬ χ → ¬ χ ) → ( ¬ χ → ¬ χ ) ) → ( ( φ → φ ) → ( ¬ χ → ¬ χ ) ) )",
        ref="merlem2",
        note="merlem2",
    )

    s2 = lb.ref(
        "s2",
        "( ( ( ( ¬ χ → ¬ χ ) → ( ¬ χ → ¬ χ ) ) → ( ( φ → φ ) → ( ¬ χ → ¬ χ ) ) ) → ( ( ( ( χ → φ ) → ( ¬ ψ → ¬ ψ ) ) → ψ ) → ( ( φ → φ ) → ( ¬ χ → ¬ χ ) ) ) )",
        ref="merlem2",
        note="merlem2",
    )

    s3 = lb.mp("s3", s1, s2, note="ax-mp")

    s4 = lb.ref(
        "s4",
        "( ( ( ( ( χ → φ ) → ( ¬ ψ → ¬ ψ ) ) → ψ ) → ( ( φ → φ ) → ( ¬ χ → ¬ χ ) ) ) → ( ( ( ( φ → φ ) → ( ¬ χ → ¬ χ ) ) → χ ) → ( ψ → χ ) ) )",
        ref="meredith",
        note="meredith",
    )

    s5 = lb.mp("s5", s3, s4, note="ax-mp")

    s6 = lb.ref(
        "s6",
        "( ( ( ( ( φ → φ ) → ( ¬ χ → ¬ χ ) ) → χ ) → ( ψ → χ ) ) → ( ( ( ψ → χ ) → φ ) → ( χ → φ ) ) )",
        ref="meredith",
        note="meredith",
    )

    res = lb.mp("res", s5, s6, note="ax-mp")
    return lb.build(res)


def prove_merlem4(sys: System) -> Proof:
    """merlem4: ( τ → ( ( τ → φ ) → ( θ → φ ) ) ).

    Fourth lemma towards deriving the Łukasiewicz axioms from Meredith's
    sole axiom.  (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "merlem4")

    s1 = lb.ref(
        "s1",
        "( ( ( ( φ → φ ) → ( ¬ θ → ¬ θ ) ) → θ ) → τ ) → ( ( τ → φ ) → ( θ → φ ) )",
        ref="meredith",
        note="meredith",
    )

    s2 = lb.ref(
        "s2",
        "( ( ( ( ( ( φ → φ ) → ( ¬ θ → ¬ θ ) ) → θ ) → τ ) → ( ( τ → φ ) → ( θ → φ ) ) ) → ( τ → ( ( τ → φ ) → ( θ → φ ) ) ) )",
        ref="merlem3",
        note="merlem3",
    )

    res = lb.mp("res", s1, s2, note="ax-mp")
    return lb.build(res)


def prove_merlem6(sys: System) -> Proof:
    """merlem6: ( χ → ( ( ( ψ → χ ) → φ ) → ( θ → φ ) ) ).

    Sixth lemma towards deriving the Łukasiewicz axioms from Meredith's
    sole axiom.  (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "merlem6")

    s1 = lb.ref(
        "s1",
        "( ψ → χ ) → ( ( ( ψ → χ ) → φ ) → ( θ → φ ) )",
        ref="merlem4",
        note="merlem4",
    )

    s2 = lb.ref(
        "s2",
        "( ( ψ → χ ) → ( ( ( ψ → χ ) → φ ) → ( θ → φ ) ) ) → ( χ → ( ( ( ψ → χ ) → φ ) → ( θ → φ ) ) )",
        ref="merlem3",
        note="merlem3",
    )

    res = lb.mp("res", s1, s2, note="ax-mp")
    return lb.build(res)


def prove_merlem9(sys: System) -> Proof:
    """merlem9: ( ( ( φ → ψ ) → ( χ → ( θ → ( ψ → τ ) ) ) ) → ( η → ( χ → ( θ → ( ψ → τ ) ) ) ) ).

    Ninth lemma towards deriving the Łukasiewicz axioms from Meredith's
    sole axiom.  (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "merlem9")

    X = "( χ → ( θ → ( ψ → τ ) ) )"
    A = f"( ( {X} → ¬ η ) → ( ¬ ψ → ¬ η ) )"
    B = f"( ¬ {A} → ¬ θ )"

    s1_f = f"( θ → ( ψ → τ ) ) → {A}"
    s3_f = f"( ( ( ψ → τ ) → ( ¬ {B} → ¬ φ ) ) → {B} ) → {A}"
    s5_f = f"( {A} → ψ ) → ( φ → ψ )"
    target = f"( ( φ → ψ ) → {X} ) → ( η → {X} )"

    # merlem6
    s1 = lb.ref("s1", s1_f, ref="merlem6", note="merlem6")

    # merlem8: s1_f → s3_f
    s2 = lb.ref("s2", f"( ( {s1_f} ) → {s3_f} )", ref="merlem8", note="merlem8")

    # ax-mp
    s3 = lb.mp("s3", s1, s2, note="ax-mp")

    # meredith: s3_f → s5_f
    s4 = lb.ref("s4", f"( ( {s3_f} ) → {s5_f} )", ref="meredith", note="meredith")

    # ax-mp
    s5 = lb.mp("s5", s3, s4, note="ax-mp")

    # meredith: s5_f → target
    s6 = lb.ref("s6", f"( ( {s5_f} ) → {target} )", ref="meredith", note="meredith")

    # ax-mp
    res = lb.mp("res", s5, s6, note="ax-mp")
    return lb.build(res)


def prove_merlem10(sys: System) -> Proof:
    """merlem10: ( φ → ( φ → ψ ) ) → ( θ → ( φ → ψ ) ).

    Tenth lemma towards deriving the Łukasiewicz axioms from Meredith's
    sole axiom.  (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "merlem10")

    # meredith(φ, φ, φ, φ, φ)
    s16 = lb.ref(
        "s16",
        "( ( ( ( ( φ → φ ) → ( ¬ φ → ¬ φ ) ) → φ ) → φ ) → ( ( φ → φ ) → ( φ → φ ) ) )",
        ref="meredith",
        note="meredith",
    )

    # meredith((φ → ψ), φ, φ, θ, φ)
    s25 = lb.ref(
        "s25",
        "( ( ( ( ( ( φ → ψ ) → φ ) → ( ¬ φ → ¬ θ ) ) → φ ) → φ ) → ( ( φ → ( φ → ψ ) ) → ( θ → ( φ → ψ ) ) ) )",
        ref="meredith",
        note="meredith",
    )

    # merlem9 connecting s25 and s16
    s26 = lb.ref(
        "s26",
        "( ( ( ( ( ( ( φ → ψ ) → φ ) → ( ¬ φ → ¬ θ ) ) → φ ) → φ ) → ( ( φ → ( φ → ψ ) ) → ( θ → ( φ → ψ ) ) ) ) → ( ( ( ( ( ( φ → φ ) → ( ¬ φ → ¬ φ ) ) → φ ) → φ ) → ( ( φ → φ ) → ( φ → φ ) ) ) → ( ( φ → ( φ → ψ ) ) → ( θ → ( φ → ψ ) ) ) ) )",
        ref="merlem9",
        note="merlem9",
    )

    # ax-mp(25, 26)
    s27 = lb.mp("s27", s25, s26, note="ax-mp")

    # ax-mp(16, 27)
    res = lb.mp("res", s16, s27, note="ax-mp")
    return lb.build(res)


def prove_merlem11(sys: System) -> Proof:
    """merlem11: ( φ → ( φ → ψ ) ) → ( φ → ψ ).

    Step 20 of Meredith's proof of Łukasiewicz axioms from his sole axiom.
    (Contributed by NM, 14-Dec-2002.)
    """
    lb = ProofBuilder(sys, "merlem11")

    # meredith(φ, φ, φ, φ, φ)
    s1 = lb.ref(
        "s1",
        "( ( ( ( ( φ → φ ) → ( ¬ φ → ¬ φ ) ) → φ ) → φ ) → ( ( φ → φ ) → ( φ → φ ) ) )",
        ref="meredith",
        note="meredith",
    )

    # merlem10 with θ = ( φ → ( φ → ψ ) )
    s2 = lb.ref(
        "s2",
        "( φ → ( φ → ψ ) ) → ( ( φ → ( φ → ψ ) ) → ( φ → ψ ) )",
        ref="merlem10",
        note="merlem10",
    )

    # merlem10 connecting s2 and s1
    s3 = lb.ref(
        "s3",
        "( ( φ → ( φ → ψ ) ) → ( ( φ → ( φ → ψ ) ) → ( φ → ψ ) ) ) → ( ( ( ( ( ( φ → φ ) → ( ¬ φ → ¬ φ ) ) → φ ) → φ ) → ( ( φ → φ ) → ( φ → φ ) ) ) → ( ( φ → ( φ → ψ ) ) → ( φ → ψ ) ) )",
        ref="merlem10",
        note="merlem10",
    )

    # ax-mp(2, 3)
    s4 = lb.mp("s4", s2, s3, note="ax-mp")

    # ax-mp(1, 4)
    res = lb.mp("res", s1, s4, note="ax-mp")
    return lb.build(res)


def prove_3imtr3g(sys: System) -> Proof:
    """3imtr3g: ( ph -> ( th -> ta ) ).

    Hyp 1: ( ph -> ( ps -> ch ) )
    Hyp 2: ( ps <-> th )
    Hyp 3: ( ch <-> ta )
    Concl: ( ph -> ( th -> ta ) )

    Inference from two biconditionals and an implication, applying biconditional
    substitution to the consequent and then the antecedent.
    (Contributed by NM, 28-Mar-1995.)
    """
    lb = ProofBuilder(sys, "3imtr3g")
    h1 = lb.hyp("3imtr3g.1", "( ph -> ( ps -> ch ) )")
    h2 = lb.hyp("3imtr3g.2", "( ps <-> th )")
    h3 = lb.hyp("3imtr3g.3", "( ch <-> ta )")
    s1 = lb.ref("s1", "( ph -> ( ps -> ta ) )", h1, h3, ref="imbitrdi", note="imbitrdi")
    res = lb.ref("res", "( ph -> ( th -> ta ) )", h2, s1, ref="biimtrrid", note="biimtrrid")
    return lb.build(res)


def prove_3imtr3d(sys: System) -> Proof:
    """3imtr3d: ( ph -> ( th -> ta ) ).

    Hyp 1: ( ph -> ( ps -> ch ) )
    Hyp 2: ( ph -> ( ps <-> th ) )
    Hyp 3: ( ph -> ( ch <-> ta ) )
    Concl: ( ph -> ( th -> ta ) )

    Deduction form of ~ 3imtr3i .  Syllogism deduction combined with two
    biconditionals, applying substitution to the consequent and then the
    antecedent.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "3imtr3d")
    h1 = lb.hyp("3imtr3d.1", "( ph -> ( ps -> ch ) )")
    h2 = lb.hyp("3imtr3d.2", "( ph -> ( ps <-> th ) )")
    h3 = lb.hyp("3imtr3d.3", "( ph -> ( ch <-> ta ) )")
    s1 = lb.ref(
        "s1", "( ph -> ( ps -> ta ) )", h1, h3, ref="sylibd", note="sylibd 3imtr3d.1, 3imtr3d.3"
    )
    res = lb.ref(
        "res", "( ph -> ( th -> ta ) )", h2, s1, ref="sylbird", note="sylbird 3imtr3d.2, s1"
    )
    return lb.build(res)


def prove_3imtr4g(sys: System) -> Proof:
    """3imtr4g: ( ph -> ( th -> ta ) ).

    Hyp 1: ( ph -> ( ps -> ch ) )
    Hyp 2: ( th <-> ps )
    Hyp 3: ( ta <-> ch )
    Concl: ( ph -> ( th -> ta ) )

    More general version of ~ 3imtr4i .  Useful for converting definitions
    to inferences.
    (Contributed by NM, 28-Mar-1995.)
    """
    lb = ProofBuilder(sys, "3imtr4g")
    h1 = lb.hyp("3imtr4g.1", "( ph -> ( ps -> ch ) )")
    h2 = lb.hyp("3imtr4g.2", "( th <-> ps )")
    h3 = lb.hyp("3imtr4g.3", "( ta <-> ch )")
    s1 = lb.ref("s1", "( ph -> ( th -> ch ) )", h2, h1, ref="biimtrid", note="biimtrid")
    res = lb.ref("res", "( ph -> ( th -> ta ) )", s1, h3, ref="imbitrrdi", note="imbitrrdi")
    return lb.build(res)


def prove_3imtr4d(sys: System) -> Proof:
    """3imtr4d: ( ph -> ( th -> ta ) ).

    Hyp 1: ( ph -> ( ps -> ch ) )
    Hyp 2: ( ph -> ( th <-> ps ) )
    Hyp 3: ( ph -> ( ta <-> ch ) )
    Concl: ( ph -> ( th -> ta ) )

    Deduction form of ~ 3imtr4i .
    (Contributed by NM, 28-Mar-1995.)
    """
    lb = ProofBuilder(sys, "3imtr4d")
    h1 = lb.hyp("3imtr4d.1", "( ph -> ( ps -> ch ) )")
    h2 = lb.hyp("3imtr4d.2", "( ph -> ( th <-> ps ) )")
    h3 = lb.hyp("3imtr4d.3", "( ph -> ( ta <-> ch ) )")
    s1 = lb.ref(
        "s1", "( ph -> ( ps -> ta ) )", h1, h3, ref="sylibrd", note="sylibrd 3imtr4d.1, 3imtr4d.3"
    )
    res = lb.ref("res", "( ph -> ( th -> ta ) )", h2, s1, ref="sylbid", note="sylbid 3imtr4d.2, s1")
    return lb.build(res)


def prove_ex(sys: System) -> Proof:
    r"""ex: ph -> ( ps -> ch ).

    Hyp: ex.1 |- ( ( ph /\ ps ) -> ch ).
    Concl: |- ( ph -> ( ps -> ch ) ).

    Exportation.  (Contributed by NM, 23-Jun-2002.)
    """
    lb = ProofBuilder(sys, "ex")
    h1 = lb.hyp("ex.1", "( ( ph /\\ ps ) -> ch )")
    dfan = lb.ref(
        "df-an",
        "( ( ph /\\ ps ) <-> -. ( ph -> -. ps ) )",
        ref="df-an",
        note="df-an",
    )
    s1 = lb.ref(
        "s1",
        "( -. ( ph -> -. ps ) -> ch )",
        dfan,
        h1,
        ref="sylbir",
        note="sylbir",
    )
    res = lb.ref(
        "res",
        "ph -> ( ps -> ch )",
        s1,
        ref="expi",
        note="expi",
    )
    return lb.build(res)


def prove_exp31(sys: System) -> Proof:
    r"""exp31: ph -> ( ps -> ( ch -> th ) ).

    Hyp: exp31.1 |- ( ( ( ph /\ ps ) /\ ch ) -> th ).
    Concl: |- ( ph -> ( ps -> ( ch -> th ) ) ).

    An exportation inference.  (Contributed by NM, 26-Apr-1994.)
    """
    lb = ProofBuilder(sys, "exp31")
    h1 = lb.hyp("exp31.1", "( ( ( ph /\\ ps ) /\\ ch ) -> th )")
    s1 = lb.ref(
        "s1",
        "( ( ph /\\ ps ) -> ( ch -> th ) )",
        h1,
        ref="ex",
        note="ex exp31.1",
    )
    res = lb.ref(
        "res",
        "( ph -> ( ps -> ( ch -> th ) ) )",
        s1,
        ref="ex",
        note="ex s1",
    )
    return lb.build(res)


def prove_exbiri(sys: System) -> Proof:
    r"""exbiri: ph -> ( ps -> ( th -> ch ) ).

    Hyp: exbiri.1 |- ( ( ph /\ ps ) -> ( ch <-> th ) ).
    Concl: |- ( ph -> ( ps -> ( th -> ch ) ) ).

    Inference form of exbir.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "exbiri")
    h1 = lb.hyp("exbiri.1", r"( ( ph /\ ps ) -> ( ch <-> th ) )")
    s1 = lb.ref(
        "s1",
        r"( ( ( ph /\ ps ) /\ th ) -> ch )",
        h1,
        ref="biimpar",
        note="biimpar exbiri.1",
    )
    res = lb.ref(
        "res",
        "( ph -> ( ps -> ( th -> ch ) ) )",
        s1,
        ref="exp31",
        note="exp31 s1",
    )
    return lb.build(res)


def prove_exp41(sys: System) -> Proof:
    r"""exp41: ph -> ( ps -> ( ch -> ( th -> ta ) ) ).

    Hyp: exp41.1 |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta ).
    Concl: |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ).

    An exportation inference.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "exp41")
    h1 = lb.hyp("exp41.1", "( ( ( ( ph /\\ ps ) /\\ ch ) /\\ th ) -> ta )")
    s1 = lb.ref(
        "s1",
        "( ( ( ph /\\ ps ) /\\ ch ) -> ( th -> ta ) )",
        h1,
        ref="ex",
        note="ex exp41.1",
    )
    res = lb.ref(
        "res",
        "( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )",
        s1,
        ref="exp31",
        note="exp31 s1",
    )
    return lb.build(res)


def prove_exp42(sys: System) -> Proof:
    r"""exp42: ph -> ( ps -> ( ch -> ( th -> ta ) ) ).

    Hyp: exp42.1 |- ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ta ).
    Concl: |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ).

    An exportation inference.  (Contributed by NM, 26-Apr-1994.)
    """
    lb = ProofBuilder(sys, "exp42")
    h1 = lb.hyp("exp42.1", "( ( ( ph /\\ ( ps /\\ ch ) ) /\\ th ) -> ta )")
    s1 = lb.ref(
        "s1",
        "( ph -> ( ( ps /\\ ch ) -> ( th -> ta ) ) )",
        h1,
        ref="exp31",
        note="exp31 exp42.1",
    )
    res = lb.ref(
        "res",
        "( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )",
        s1,
        ref="expd",
        note="expd s1",
    )
    return lb.build(res)


def prove_exp43(sys: System) -> Proof:
    r"""exp43: ph -> ( ps -> ( ch -> ( th -> ta ) ) ).

    Hyp: exp43.1 |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ).
    Concl: |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ).

    An exportation inference.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "exp43")
    h1 = lb.hyp("exp43.1", "( ( ( ph /\\ ps ) /\\ ( ch /\\ th ) ) -> ta )")
    s1 = lb.ref(
        "s1",
        "( ( ph /\\ ps ) -> ( ( ch /\\ th ) -> ta ) )",
        h1,
        ref="ex",
        note="ex exp43.1",
    )
    res = lb.ref(
        "res",
        "ph -> ( ps -> ( ch -> ( th -> ta ) ) )",
        s1,
        ref="exp4b",
        note="exp4b s1",
    )
    return lb.build(res)


def prove_exp44(sys: System) -> Proof:
    r"""exp44: ph -> ( ps -> ( ch -> ( th -> ta ) ) ).

    Hyp: exp44.1 |- ( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ta ).
    Concl: |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ).

    An exportation inference.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "exp44")
    h1 = lb.hyp("exp44.1", r"( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ta )")
    s1 = lb.ref(
        "s1",
        r"ph -> ( ( ps /\ ch ) -> ( th -> ta ) )",
        h1,
        ref="exp32",
        note="exp32 exp44.1",
    )
    res = lb.ref(
        "res",
        "ph -> ( ps -> ( ch -> ( th -> ta ) ) )",
        s1,
        ref="expd",
        note="expd s1",
    )
    return lb.build(res)


def prove_exp45(sys: System) -> Proof:
    r"""exp45: ph -> ( ps -> ( ch -> ( th -> ta ) ) ).

    Hyp: exp45.1 |- ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) -> ta ).
    Concl: |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ).

    An exportation inference.  (Contributed by NM, 26-Apr-1994.)
    """
    lb = ProofBuilder(sys, "exp45")
    h1 = lb.hyp("exp45.1", "( ( ph /\\ ( ps /\\ ( ch /\\ th ) ) ) -> ta )")
    s1 = lb.ref(
        "s1",
        "( ph -> ( ps -> ( ( ch /\\ th ) -> ta ) ) )",
        h1,
        ref="exp32",
        note="exp32 exp45.1",
    )
    res = lb.ref(
        "res",
        "ph -> ( ps -> ( ch -> ( th -> ta ) ) )",
        s1,
        ref="exp4a",
        note="exp4a s1",
    )
    return lb.build(res)


def prove_exp53(sys: System) -> Proof:
    r"""exp53: ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ).

    Hyp: exp53.1 |- ( ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) /\ ta ) -> et ).
    Concl: |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ).

    An exportation inference.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "exp53")
    h1 = lb.hyp("exp53.1", "( ( ( ( ph /\\ ps ) /\\ ( ch /\\ th ) ) /\\ ta ) -> et )")
    s1 = lb.ref(
        "s1",
        "( ( ( ph /\\ ps ) /\\ ( ch /\\ th ) ) -> ( ta -> et ) )",
        h1,
        ref="ex",
        note="ex exp53.1",
    )
    res = lb.ref(
        "res",
        "ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) )",
        s1,
        ref="exp43",
        note="exp43 s1",
    )
    return lb.build(res)


def prove_3exp(sys: System) -> Proof:
    """3exp: ( ph -> ( ps -> ( ch -> th ) ) ).

    Hyp: ( ( ph /\\ ps /\\ ch ) -> th ).
    Concl: ( ph -> ( ps -> ( ch -> th ) ) ).

    An exportation inference.  (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3exp")
    h1 = lb.hyp("3exp.1", "( ph /\\ ps /\\ ch ) -> th")
    s1 = lb.ref(
        "s1",
        "( ( ph /\\ ps ) /\\ ch ) -> th",
        h1,
        ref="3expa",
        note="3expa 3exp.1",
    )
    res = lb.ref(
        "res",
        "( ph -> ( ps -> ( ch -> th ) ) )",
        s1,
        ref="exp31",
        note="exp31 s1",
    )
    return lb.build(res)


def prove_3expib(sys: System) -> Proof:
    r"""3expib: ( ph -> ( ( ps /\ ch ) -> th ) ).

    Hyp: ( ( ph /\ ps /\ ch ) -> th ).
    Concl: ( ph -> ( ( ps /\ ch ) -> th ) ).

    An exportation inference.  (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3expib")
    h1 = lb.hyp("3exp.1", "( ph /\\ ps /\\ ch ) -> th")
    s1 = lb.ref(
        "s1",
        "( ph -> ( ps -> ( ch -> th ) ) )",
        h1,
        ref="3exp",
        note="3exp 3exp.1",
    )
    res = lb.ref(
        "res",
        "( ph -> ( ( ps /\\ ch ) -> th ) )",
        s1,
        ref="impd",
        note="impd s1",
    )
    return lb.build(res)


def prove_3expd(sys: System) -> Proof:
    r"""3expd: ph -> (ps -> (ch -> (th -> ta))).

    Hyp: 3expd.1 |- ph -> ((ps /\ ch /\ th) -> ta).
    Concl: |- ph -> (ps -> (ch -> (th -> ta))).

    Deduction form of ~ 3exp .  (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3expd")
    h1 = lb.hyp("3expd.1", "ph -> ( ( ps /\\ ch /\\ th ) -> ta )")
    s1 = lb.ref(
        "s1",
        "( ps /\\ ch /\\ th ) -> ( ph -> ta )",
        h1,
        ref="com12",
        note="com12 3expd.1",
    )
    s2 = lb.ref(
        "s2",
        "ps -> ( ch -> ( th -> ( ph -> ta ) ) )",
        s1,
        ref="3exp",
        note="3exp s1",
    )
    res = lb.ref(
        "res",
        "ph -> ( ps -> ( ch -> ( th -> ta ) ) )",
        s2,
        ref="com4r",
        note="com4r s2",
    )
    return lb.build(res)


def prove_3exp1(sys: System) -> Proof:
    r"""3exp1: ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ).

    Hyp: ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ).
    Concl: ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ).

    An exportation inference.  (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3exp1")
    h1 = lb.hyp("3exp1.1", "( ( ( ph /\\ ps /\\ ch ) /\\ th ) -> ta )")
    s1 = lb.ref(
        "s1",
        "( ( ph /\\ ps /\\ ch ) -> ( th -> ta ) )",
        h1,
        ref="ex",
        note="ex 3exp1.1",
    )
    res = lb.ref(
        "res",
        "( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )",
        s1,
        ref="3exp",
        note="3exp s1",
    )
    return lb.build(res)


def prove_3exp2(sys: System) -> Proof:
    r"""3exp2: ph -> ( ps -> ( ch -> ( th -> ta ) ) ).

    Hyp: 3exp2.1 |- ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ).
    Concl: |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ).

    An exportation inference.  (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3exp2")
    h1 = lb.hyp("3exp2.1", r"( ( ph /\ ( ps /\ ch /\ th ) ) -> ta )")
    s1 = lb.ref(
        "s1",
        r"( ph -> ( ( ps /\ ch /\ th ) -> ta ) )",
        h1,
        ref="ex",
        note="ex 3exp2.1",
    )
    res = lb.ref(
        "res",
        "( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )",
        s1,
        ref="3expd",
        note="3expd s1",
    )
    return lb.build(res)


def prove_expdcom(sys: System) -> Proof:
    r"""expdcom: ψ → (χ → (φ → θ)).

    Hyp: expd.1 |- φ → ((ψ ∧ χ) → θ)
    Concl: |- ψ → (χ → (φ → θ))

    Commuted form of ~ expd .  (Contributed by NM, 26-Apr-1994.)
    """
    lb = ProofBuilder(sys, "expdcom")
    h1 = lb.hyp("expd.1", "φ → ( ( ψ ∧ χ ) → θ )")
    s1 = lb.ref("s1", "( ψ ∧ χ ) → ( φ → θ )", h1, ref="com12", note="com12")
    res = lb.ref("res", "ψ → ( χ → ( φ → θ ) )", s1, ref="ex", note="ex")
    return lb.build(res)


def prove_expd(sys: System) -> Proof:
    r"""expd: φ → (ψ → (χ → θ)).

    Hyp: expd.1 |- φ → ((ψ ∧ χ) → θ)
    Concl: |- φ → (ψ → (χ → θ))

    Deduction form of ~ ex .  (Contributed by NM, 26-Apr-1994.)
    """
    lb = ProofBuilder(sys, "expd")
    h1 = lb.hyp("expd.1", "φ → ( ( ψ ∧ χ ) → θ )")
    s1 = lb.ref("s1", "ψ → ( χ → ( φ → θ ) )", h1, ref="expdcom", note="expdcom")
    res = lb.ref("res", "φ → ( ψ → ( χ → θ ) )", s1, ref="com3r", note="com3r")
    return lb.build(res)


def prove_expcom(sys: System) -> Proof:
    """expcom: ψ → (φ → χ).

    Hyp: expcom.1 |- ( ( φ ∧ ψ ) → χ ).
    Concl: |- ψ → (φ → χ).

    Exportation with commuted antecedents.  (Contributed by NM, 29-Dec-1992.)
    """
    lb = ProofBuilder(sys, "expcom")
    h1 = lb.hyp("expcom.1", "( ( φ ∧ ψ ) → χ )")
    s1 = lb.ref("s1", "φ → ( ψ → χ )", h1, ref="ex", note="ex expcom.1")
    res = lb.ref("res", "ψ → ( φ → χ )", s1, ref="com12", note="com12 s1")
    return lb.build(res)


def prove_expcomd(sys: System) -> Proof:
    r"""expcomd: φ → (χ → (ψ → θ)).

    Hyp: expcomd.1 |- φ → ((ψ ∧ χ) → θ)
    Concl: |- φ → (χ → (ψ → θ))

    A commuted form of ~ expd .  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "expcomd")
    h1 = lb.hyp("expcomd.1", "φ → ( ( ψ ∧ χ ) → θ )")
    s1 = lb.ref("s1", "φ → ( ψ → ( χ → θ ) )", h1, ref="expd", note="expd expcomd.1")
    res = lb.ref("res", "φ → ( χ → ( ψ → θ ) )", s1, ref="com23", note="com23 s1")
    return lb.build(res)


def prove_exp4a(sys: System) -> Proof:
    r"""exp4a: ph -> ( ps -> ( ch -> ( th -> ta ) ) ).

    Hyp: exp4a.1 |- ( ph -> ( ps -> ( ( ch /\ th ) -> ta ) ) ).
    Concl: |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ).

    An exportation inference.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "exp4a")
    h1 = lb.hyp("exp4a.1", "ph -> ( ps -> ( ( ch /\\ th ) -> ta ) )")
    s1 = lb.ref(
        "s1",
        "( ( ph /\\ ps ) -> ( ( ch /\\ th ) -> ta ) )",
        h1,
        ref="imp",
        note="imp exp4a.1",
    )
    res = lb.ref(
        "res",
        "ph -> ( ps -> ( ch -> ( th -> ta ) ) )",
        s1,
        ref="exp4b",
        note="exp4b s1",
    )
    return lb.build(res)


def prove_exp4b(sys: System) -> Proof:
    r"""exp4b: ph -> ( ps -> ( ch -> ( th -> ta ) ) ).

    Hyp: exp4b.1 |- ( ( ph /\ ps ) -> ( ( ch /\ th ) -> ta ) ).
    Concl: |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ).

    An exportation inference.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "exp4b")
    h1 = lb.hyp("exp4b.1", "( ( ph /\\ ps ) -> ( ( ch /\\ th ) -> ta ) )")
    s1 = lb.ref(
        "s1",
        "( ph /\\ ps ) -> ( ch -> ( th -> ta ) )",
        h1,
        ref="expd",
        note="expd exp4b.1",
    )
    res = lb.ref(
        "res",
        "ph -> ( ps -> ( ch -> ( th -> ta ) ) )",
        s1,
        ref="ex",
        note="ex s1",
    )
    return lb.build(res)


def prove_exp4c(sys: System) -> Proof:
    r"""exp4c: ph -> ( ps -> ( ch -> ( th -> ta ) ) ).

    Hyp: exp4c.1 |- ( ph -> ( ( ( ps /\ ch ) /\ th ) -> ta ) ).
    Concl: |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ).

    An exportation inference.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "exp4c")
    h1 = lb.hyp("exp4c.1", "ph -> ( ( ( ps /\\ ch ) /\\ th ) -> ta )")
    s1 = lb.ref(
        "s1",
        "ph -> ( ( ps /\\ ch ) -> ( th -> ta ) )",
        h1,
        ref="expd",
        note="expd exp4c.1",
    )
    res = lb.ref(
        "res",
        "ph -> ( ps -> ( ch -> ( th -> ta ) ) )",
        s1,
        ref="expd",
        note="expd s1",
    )
    return lb.build(res)


def prove_exp4d(sys: System) -> Proof:
    r"""exp4d: ph -> ( ps -> ( ch -> ( th -> ta ) ) ).

    Hyp: exp4d.1 |- ( ph -> ( ( ps /\ ( ch /\ th ) ) -> ta ) ).
    Concl: |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ).

    An exportation inference.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "exp4d")
    h1 = lb.hyp("exp4d.1", r"ph -> ( ( ps /\ ( ch /\ th ) ) -> ta )")
    s1 = lb.ref(
        "s1",
        r"ph -> ( ps -> ( ( ch /\ th ) -> ta ) )",
        h1,
        ref="expd",
        note="expd exp4d.1",
    )
    res = lb.ref(
        "res",
        "ph -> ( ps -> ( ch -> ( th -> ta ) ) )",
        s1,
        ref="exp4a",
        note="exp4a s1",
    )
    return lb.build(res)


def prove_exp5c(sys: System) -> Proof:
    r"""exp5c: ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ).

    Hyp: exp5c.1 |- ( ph -> ( ( ps /\ ch ) -> ( ( th /\ ta ) -> et ) ) ).
    Concl: |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ).

    An exportation inference.  (Contributed by NM, 26-Apr-1994.)
    """
    lb = ProofBuilder(sys, "exp5c")
    h1 = lb.hyp("exp5c.1", "ph -> ( ( ps /\\ ch ) -> ( ( th /\\ ta ) -> et ) )")
    s1 = lb.ref(
        "s1",
        "ph -> ( ( ps /\\ ch ) -> ( th -> ( ta -> et ) ) )",
        h1,
        ref="exp4a",
        note="exp4a exp5c.1",
    )
    res = lb.ref(
        "res",
        "ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) )",
        s1,
        ref="expd",
        note="expd s1",
    )
    return lb.build(res)


def prove_exp5j(sys: System) -> Proof:
    r"""exp5j: ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ).

    Hyp: exp5j.1 |- ( ph -> ( ( ( ( ps /\ ch ) /\ th ) /\ ta ) -> et ) ).
    Concl: |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ).

    An exportation inference.  (Contributed by NM, 21-Apr-2006.)
    """
    lb = ProofBuilder(sys, "exp5j")
    h1 = lb.hyp("exp5j.1", "ph -> ( ( ( ( ps /\\ ch ) /\\ th ) /\\ ta ) -> et )")
    s1 = lb.ref(
        "s1",
        "ph -> ( ( ( ps /\\ ch ) /\\ th ) -> ( ta -> et ) )",
        h1,
        ref="expd",
        note="expd exp5j.1",
    )
    res = lb.ref(
        "res",
        "ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) )",
        s1,
        ref="exp4c",
        note="exp4c s1",
    )
    return lb.build(res)


def prove_exp5l(sys: System) -> Proof:
    r"""exp5l: ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ).

    Hyp: exp5l.1 |- ( ph -> ( ( ( ps /\ ch ) /\ ( th /\ ta ) ) -> et ) ).
    Concl: |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ).

    An exportation inference.  (Contributed by NM, 26-Apr-1994.)
    """
    lb = ProofBuilder(sys, "exp5l")
    h1 = lb.hyp("exp5l.1", "ph -> ( ( ( ps /\\ ch ) /\\ ( th /\\ ta ) ) -> et )")
    s1 = lb.ref(
        "s1",
        "ph -> ( ( ps /\\ ch ) -> ( ( th /\\ ta ) -> et ) )",
        h1,
        ref="expd",
        note="expd exp5l.1",
    )
    res = lb.ref(
        "res",
        "ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) )",
        s1,
        ref="exp5c",
        note="exp5c s1",
    )
    return lb.build(res)


def prove_exp5o(sys: System) -> Proof:
    r"""exp5o: ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ).

    Hyp: exp5o.1 |- ( ( ph /\ ps /\ ch ) -> ( ( th /\ ta ) -> et ) ).
    Concl: |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ).

    An exportation inference.  (Contributed by NM, 26-Apr-1994.)
    """
    lb = ProofBuilder(sys, "exp5o")
    h1 = lb.hyp("exp5o.1", "( ph /\\ ps /\\ ch ) -> ( ( th /\\ ta ) -> et )")
    s1 = lb.ref(
        "s1",
        "( ph /\\ ps /\\ ch ) -> ( th -> ( ta -> et ) )",
        h1,
        ref="expd",
        note="expd exp5o.1",
    )
    res = lb.ref(
        "res",
        "ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) )",
        s1,
        ref="3exp",
        note="3exp s1",
    )
    return lb.build(res)


def prove_exp516(sys: System) -> Proof:
    r"""exp516: ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ).

    Hyp: exp516.1 |- ( ( ( ph /\ ( ps /\ ch /\ th ) ) /\ ta ) -> et ).
    Concl: |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ).

    An exportation inference.  (Contributed by NM, 26-Apr-1994.)
    """
    lb = ProofBuilder(sys, "exp516")
    h1 = lb.hyp("exp516.1", "( ( ( ph /\\ ( ps /\\ ch /\\ th ) ) /\\ ta ) -> et )")
    s1 = lb.ref(
        "s1",
        "( ph -> ( ( ps /\\ ch /\\ th ) -> ( ta -> et ) ) )",
        h1,
        ref="exp31",
        note="exp31 exp516.1",
    )
    res = lb.ref(
        "res",
        "ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) )",
        s1,
        ref="3expd",
        note="3expd s1",
    )
    return lb.build(res)


def prove_exp520(sys: System) -> Proof:
    r"""exp520: ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ).

    Hyp: exp520.1 |- ( ( ( ph /\ ps /\ ch ) /\ ( th /\ ta ) ) -> et ).
    Concl: |- ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ).

    An exportation inference.  (Contributed by NM, 26-Apr-1994.)
    """
    lb = ProofBuilder(sys, "exp520")
    h1 = lb.hyp("exp520.1", "( ( ( ph /\\ ps /\\ ch ) /\\ ( th /\\ ta ) ) -> et )")
    s1 = lb.ref(
        "s1",
        "( ph /\\ ps /\\ ch ) -> ( ( th /\\ ta ) -> et )",
        h1,
        ref="ex",
        note="ex exp520.1",
    )
    res = lb.ref(
        "res",
        "ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) )",
        s1,
        ref="exp5o",
        note="exp5o s1",
    )
    return lb.build(res)


def prove_exp32(sys: System) -> Proof:
    r"""exp32: ph -> ( ps -> ( ch -> th ) ).

    Hyp: exp32.1 |- ( ( ph /\ ( ps /\ ch ) ) -> th ).
    Concl: |- ( ph -> ( ps -> ( ch -> th ) ) ).

    An exportation inference.  (Contributed by NM, 26-Apr-1994.)
    """
    lb = ProofBuilder(sys, "exp32")
    h1 = lb.hyp("exp32.1", "( ( ph /\\ ( ps /\\ ch ) ) -> th )")
    s1 = lb.ref(
        "s1",
        "( ph -> ( ( ps /\\ ch ) -> th ) )",
        h1,
        ref="ex",
        note="ex exp32.1",
    )
    res = lb.ref(
        "res",
        "( ph -> ( ps -> ( ch -> th ) ) )",
        s1,
        ref="expd",
        note="expd s1",
    )
    return lb.build(res)


def prove_condan(sys: System) -> Proof:
    r"""condan: ( ph -> ps ).

    Hypotheses: condan.1 |- ( ( ph /\ -. ps ) -> ch ),
                condan.2 |- ( ( ph /\ -. ps ) -> -. ch ).
    Concl: |- ( ph -> ps ).

    Deduction form of proof by contradiction (conjunction form).
    From condan.1 and condan.2, pm2.65da gives ( ph -> -. -. ps ),
    then notnotrd yields ( ph -> ps ).
    (Contributed by NM, 13-Jun-1994.)
    """
    lb = ProofBuilder(sys, "condan")
    h1 = lb.hyp("condan.1", "( -. ( ph -> -. -. ps ) -> ch )")
    h2 = lb.hyp("condan.2", "( -. ( ph -> -. -. ps ) -> -. ch )")
    s1 = lb.ref(
        "s1",
        "( ph -> -. -. ps )",
        h1,
        h2,
        ref="pm2.65da",
        note="pm2.65da condan.1 condan.2",
    )
    res = lb.ref(
        "res",
        "( ph -> ps )",
        s1,
        ref="notnotrd",
        note="notnotrd s1",
    )
    return lb.build(res)


def prove_dedt(sys: System) -> Proof:
    """dedt: χ → θ.

    Deduction form involving the conditional operator if-.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "dedt")
    h1 = lb.hyp("dedt.1", "( ( if- χ φ ψ ↔ φ ) → ( τ ↔ θ ) )")
    h2 = lb.hyp("dedt.2", "τ")

    # ifptru: χ → ( if- χ φ ψ ↔ φ )
    s1 = lb.ref(
        "s1",
        "χ → ( if- χ φ ψ ↔ φ )",
        ref="ifptru",
        note="ifptru",
    )

    # mpbii: ( if- χ φ ψ ↔ φ ) → θ
    s2 = lb.ref(
        "s2",
        "( if- χ φ ψ ↔ φ ) → θ",
        h2,
        h1,
        ref="mpbii",
        note="mpbii dedt.2, dedt.1",
    )

    # syl: χ → θ
    res = lb.ref(
        "res",
        "χ → θ",
        s1,
        s2,
        ref="syl",
        note="syl",
    )

    return lb.build(res)


def prove_mp3an23(sys: System) -> Proof:
    r"""mp3an23: ph -> th.

    Hyp 1: ps
    Hyp 2: ch
    Hyp 3: ( ph /\ ps /\ ch ) -> th
    Concl: ph -> th

    An inference form of modus ponens with a triple conjunction antecedent
    where two antecedents are provided.
    (Contributed by NM, 28-Aug-1994.)
    set.mm proof: mp3an3 mpan2.
    """
    lb = ProofBuilder(sys, "mp3an23")
    h1 = lb.hyp("mp3an23.1", r"ps")
    h2 = lb.hyp("mp3an23.2", r"ch")
    h3 = lb.hyp("mp3an23.3", r"( ph /\ ps /\ ch ) -> th")
    s1 = lb.ref(
        "s1",
        r"( ( ph /\ ps ) -> th )",
        h2,
        h3,
        ref="mp3an3",
        note="mp3an3 mp3an23.2, mp3an23.3",
    )
    res = lb.ref(
        "res",
        r"ph -> th",
        h1,
        s1,
        ref="mpan2",
        note="mpan2 mp3an23.1, s1",
    )
    return lb.build(res)


def prove_mpd3an23(sys: System) -> Proof:
    r"""mpd3an23: ph -> th.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ( ph /\ ps /\ ch ) -> th
    Concl: ph -> th

    A modus ponens deduction with a triple conjunction antecedent where
    two antecedents are deductions.
    (Contributed by NM, 28-Aug-1994.)
    set.mm proof: id syl3anc.
    """
    lb = ProofBuilder(sys, "mpd3an23")
    h1 = lb.hyp("mpd3an23.1", "ph -> ps")
    h2 = lb.hyp("mpd3an23.2", "ph -> ch")
    h3 = lb.hyp("mpd3an23.3", r"( ph /\ ps /\ ch ) -> th")
    s1 = lb.ref("s1", "ph -> ph", ref="id", note="id")
    res = lb.ref("res", "ph -> th", s1, h1, h2, h3, ref="syl3anc", note="syl3anc")
    return lb.build(res)


def prove_mp3an13(sys: System) -> Proof:
    r"""mp3an13: ps -> th.

    Hyp 1: ph
    Hyp 2: ch
    Hyp 3: ( ph /\ ps /\ ch ) -> th
    Concl: ps -> th

    An inference form of modus ponens with a triple conjunction antecedent
    where the first and third antecedents are provided.
    (Contributed by NM, 14-May-1993.)
    set.mm proof: mp3an3 mpan.
    """
    lb = ProofBuilder(sys, "mp3an13")
    h1 = lb.hyp("mp3an13.1", r"ph")
    h2 = lb.hyp("mp3an13.2", r"ch")
    h3 = lb.hyp("mp3an13.3", r"( ph /\ ps /\ ch ) -> th")
    s1 = lb.ref(
        "s1",
        r"( ( ph /\ ps ) -> th )",
        h2,
        h3,
        ref="mp3an3",
        note="mp3an3 mp3an13.2, mp3an13.3",
    )
    res = lb.ref(
        "res",
        r"ps -> th",
        h1,
        s1,
        ref="mpan",
        note="mpan mp3an13.1, s1",
    )
    return lb.build(res)


def prove_mp3an2i(sys: System) -> Proof:
    r"""mp3an2i: ps -> ta.

    Hyp 1: ph
    Hyp 2: ps -> ch
    Hyp 3: ps -> th
    Hyp 4: ( ph /\ ch /\ th ) -> ta
    Concl: ps -> ta

    An inference form of modus ponens with a triple conjunction antecedent
    where the second and third antecedents are conditional.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: mp3an1 syl2anc.
    """
    lb = ProofBuilder(sys, "mp3an2i")
    h1 = lb.hyp("mp3an2i.1", r"ph")
    h2 = lb.hyp("mp3an2i.2", r"ps -> ch")
    h3 = lb.hyp("mp3an2i.3", r"ps -> th")
    h4 = lb.hyp("mp3an2i.4", r"( ph /\ ch /\ th ) -> ta")
    s1 = lb.ref(
        "s1",
        r"( ch /\ th ) -> ta",
        h1,
        h4,
        ref="mp3an1",
        note="mp3an1 mp3an2i.1, mp3an2i.4",
    )
    res = lb.ref(
        "res",
        r"ps -> ta",
        h2,
        h3,
        s1,
        ref="syl2anc",
        note="syl2anc mp3an2i.2, mp3an2i.3, s1",
    )
    return lb.build(res)


def prove_simplbi(sys: System) -> Proof:
    """simplbi: φ → ψ.

    Hyp: simplbi.1 |- ( φ ↔ ( ψ ∧ χ ) )
    Concl: |- ( φ → ψ )

    Inference from a biconditional via biimpi and simpld.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "simplbi")
    h1 = lb.hyp("simplbi.1", "( φ ↔ ( ψ ∧ χ ) )")
    s1 = lb.ref(
        "s1",
        "φ → ( ψ ∧ χ )",
        h1,
        ref="biimpi",
        note="biimpi simplbi.1",
    )
    res = lb.ref(
        "res",
        "φ → ψ",
        s1,
        ref="simpld",
        note="simpld s1",
    )
    return lb.build(res)


def prove_just1_df(sys: System) -> Proof:
    """just1-df: φ → ψ.

    Hyp: just1-df.1 |- ( φ ↔ ( ψ ∧ χ ) )
    Concl: |- ( φ → ψ )

    Inference from a biconditional.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "just1-df")
    h1 = lb.hyp("just1-df.1", "( φ ↔ ( ψ ∧ χ ) )")
    res = lb.ref(
        "res",
        "φ → ψ",
        h1,
        ref="simplbi",
        note="simplbi just1-df.1",
    )
    return lb.build(res)


def prove_simplbi2(sys: System) -> Proof:
    r"""simplbi2: ps -> ( ch -> ph ).

    Hyp: simplbi2.1 |- ( ph <-> ( ps /\ ch ) ).
    Concl: |- ( ps -> ( ch -> ph ) ).

    Inference from a biconditional via biimpri and ex.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "simplbi2")
    h1 = lb.hyp("simplbi2.1", r"( ph <-> ( ps /\ ch ) )")
    s1 = lb.ref(
        "s1",
        r"( ( ps /\ ch ) -> ph )",
        h1,
        ref="biimpri",
        note="biimpri simplbi2.1",
    )
    res = lb.ref(
        "res",
        r"( ps -> ( ch -> ph ) )",
        s1,
        ref="ex",
        note="ex s1",
    )
    return lb.build(res)


def prove_simplbi2com(sys: System) -> Proof:
    r"""simplbi2com: ch -> ( ps -> ph ).

    Hyp: simplbi2com.1 |- ( ph <-> ( ps /\ ch ) ).
    Concl: |- ( ch -> ( ps -> ph ) ).

    Commuted form of ~ simplbi2 .
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "simplbi2com")
    h1 = lb.hyp("simplbi2com.1", r"( ph <-> ( ps /\ ch ) )")
    s1 = lb.ref(
        "s1",
        r"( ps -> ( ch -> ph ) )",
        h1,
        ref="simplbi2",
        note="simplbi2 simplbi2com.1",
    )
    res = lb.ref(
        "res",
        r"( ch -> ( ps -> ph ) )",
        s1,
        ref="com12",
        note="com12 s1",
    )
    return lb.build(res)


def prove_simprbi(sys: System) -> Proof:
    """simprbi: φ → χ.

    Hyp: simprbi.1 |- ( φ ↔ ( ψ ∧ χ ) )
    Concl: |- ( φ → χ )

    Inference from a biconditional via biimpi and simprd.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "simprbi")
    h1 = lb.hyp("simprbi.1", "( φ ↔ ( ψ ∧ χ ) )")
    s1 = lb.ref(
        "s1",
        "φ → ( ψ ∧ χ )",
        h1,
        ref="biimpi",
        note="biimpi simprbi.1",
    )
    res = lb.ref(
        "res",
        "φ → χ",
        s1,
        ref="simprd",
        note="simprd s1",
    )
    return lb.build(res)


def prove_sylanbrc(sys: System) -> Proof:
    """sylanbrc: φ → θ.

    Hyp 1: φ → ψ
    Hyp 2: φ → χ
    Hyp 3: θ ↔ ( ψ ∧ χ )
    Concl: φ → θ

    Inference joining two implications and a biconditional with conjunction.
    (Contributed by NM, 28-Dec-1992.)
    """
    lb = ProofBuilder(sys, "sylanbrc")
    h1 = lb.hyp("sylanbrc.1", "φ → ψ")
    h2 = lb.hyp("sylanbrc.2", "φ → χ")
    h3 = lb.hyp("sylanbrc.3", "θ ↔ ( ψ ∧ χ )")
    s1 = lb.ref(
        "s1",
        "φ → ( ψ ∧ χ )",
        h1,
        h2,
        ref="jca",
        note="jca",
    )
    res = lb.ref(
        "res",
        "φ → θ",
        s1,
        h3,
        ref="sylibr",
        note="sylibr",
    )
    return lb.build(res)


def prove_sylanblrc(sys: System) -> Proof:
    """sylanblrc: φ → θ.

    Hyp 1: φ → ψ
    Hyp 2: χ
    Hyp 3: θ ↔ ( ψ ∧ χ )
    Concl: φ → θ

    Inference joining an implication, a premise, and a biconditional with conjunction.
    (Contributed by NM, 28-Dec-1992.)
    """
    lb = ProofBuilder(sys, "sylanblrc")
    h1 = lb.hyp("sylanblrc.1", "φ → ψ")
    h2 = lb.hyp("sylanblrc.2", "χ")
    h3 = lb.hyp("sylanblrc.3", "θ ↔ ( ψ ∧ χ )")
    s1 = lb.ref(
        "s1",
        "φ → χ",
        h2,
        ref="a1i",
        note="a1i sylanblrc.2",
    )
    res = lb.ref(
        "res",
        "φ → θ",
        h1,
        s1,
        h3,
        ref="sylanbrc",
        note="sylanbrc",
    )

    return lb.build(res)


def prove_syl21anbrc(sys: System) -> Proof:
    r"""syl21anbrc: ph -> ta.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ta <-> ( ( ps /\ ch ) /\ th )
    Concl: ph -> ta

    Syllogism combined with two antecedents and a conjunctive antecedent,
    with a biconditional in the consequent.  (Contributed by NM, 1-Jan-2013.)
    """
    lb = ProofBuilder(sys, "syl21anbrc")
    h1 = lb.hyp("syl21anbrc.1", "ph -> ps")
    h2 = lb.hyp("syl21anbrc.2", "ph -> ch")
    h3 = lb.hyp("syl21anbrc.3", "ph -> th")
    h4 = lb.hyp("syl21anbrc.4", r"ta <-> ( ( ps /\ ch ) /\ th )")
    s1 = lb.ref(
        "s1",
        r"ph -> ( ( ps /\ ch ) /\ th )",
        h1,
        h2,
        h3,
        ref="jca31",
        note="jca31",
    )
    res = lb.ref(
        "res",
        "ph -> ta",
        s1,
        h4,
        ref="sylibr",
        note="sylibr",
    )
    return lb.build(res)


def prove_mpbir2an(sys: System) -> Proof:
    """mpbir2an: φ.

    Hyp 1: ψ
    Hyp 2: χ
    Hyp 3 (maj): ( φ ↔ ( ψ ∧ χ ) )
    Concl: φ

    An inference from a biconditional and two conjuncts.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "mpbir2an")
    h1 = lb.hyp("mpbir2an.1", "ψ")
    h2 = lb.hyp("mpbir2an.2", "χ")
    h3 = lb.hyp("mpbir2an.maj", "( φ ↔ ( ψ ∧ χ ) )")
    s1 = lb.ref("s1", "φ ↔ χ", h1, h3, ref="mpbiran", note="mpbiran")
    res = lb.ref("res", "φ", h2, s1, ref="mpbir", note="mpbir")
    return lb.build(res)


def prove_mpbir3an(sys: System) -> Proof:
    """mpbir3an: φ.

    Hyp 1: ψ
    Hyp 2: χ
    Hyp 3: θ
    Hyp 4 (maj): ( φ ↔ ( ψ ∧ χ ∧ θ ) )
    Concl: φ

    An inference from a biconditional and three conjuncts.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "mpbir3an")
    h1 = lb.hyp("mpbir3an.1", "ψ")
    h2 = lb.hyp("mpbir3an.2", "χ")
    h3 = lb.hyp("mpbir3an.3", "θ")
    h4 = lb.hyp("mpbir3an.4", "( φ ↔ ( ψ ∧ χ ∧ θ ) )")
    s1 = lb.ref("s1", "( ψ ∧ χ ∧ θ )", h1, h2, h3, ref="3pm3.2i", note="3pm3.2i")
    res = lb.ref("res", "φ", s1, h4, ref="mpbir", note="mpbir")
    return lb.build(res)


def prove_mpbir2and(sys: System) -> Proof:
    r"""mpbir2and: ph -> ps.

    Hyp 1: ph -> ch
    Hyp 2: ph -> th
    Hyp 3: ph -> ( ps <-> ( ch /\ th ) )
    Concl: ph -> ps

    A deduction joining two implications to form a conjunction of their
    consequents, then using mpbird with a biconditional.
    (Contributed by NM, 28-Dec-1992.)
    """
    lb = ProofBuilder(sys, "mpbir2and")
    h1 = lb.hyp("mpbir2and.1", "ph -> ch")
    h2 = lb.hyp("mpbir2and.2", "ph -> th")
    h3 = lb.hyp("mpbir2and.3", "ph -> ( ps <-> ( ch /\\ th ) )")
    s1 = lb.ref(
        "s1",
        "ph -> ( ch /\\ th )",
        h1,
        h2,
        ref="jca",
        note="jca mpbir2and.1, mpbir2and.2",
    )
    res = lb.ref(
        "res",
        "ph -> ps",
        s1,
        h3,
        ref="mpbird",
        note="mpbird s1, mpbir2and.3",
    )
    return lb.build(res)


def prove_mpbir3and(sys: System) -> Proof:
    r"""mpbir3and: ph -> ps.

    Hyp 1: ph -> ch
    Hyp 2: ph -> th
    Hyp 3: ph -> ta
    Hyp 4: ph -> ( ps <-> ( ch /\\ th /\\ ta ) )
    Concl: ph -> ps

    A deduction joining three implications to form a conjunction of their
    consequents, then using mpbird with a biconditional.
    (Contributed by NM, 29-Dec-1992.)
    """
    lb = ProofBuilder(sys, "mpbir3and")
    h1 = lb.hyp("mpbir3and.1", "ph -> ch")
    h2 = lb.hyp("mpbir3and.2", "ph -> th")
    h3 = lb.hyp("mpbir3and.3", "ph -> ta")
    h4 = lb.hyp("mpbir3and.4", "ph -> ( ps <-> ( ch /\\ th /\\ ta ) )")
    s1 = lb.ref(
        "s1",
        "ph -> ( ch /\\ th /\\ ta )",
        h1,
        h2,
        h3,
        ref="3jca",
        note="3jca mpbir3and.1, mpbir3and.2, mpbir3and.3",
    )
    res = lb.ref(
        "res",
        "ph -> ps",
        s1,
        h4,
        ref="mpbird",
        note="mpbird s1, mpbir3and.4",
    )
    return lb.build(res)


def prove_mp3and(sys: System) -> Proof:
    r"""mp3and: ph -> ta.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ph -> ( ( ps /\ ch /\ th ) -> ta )
    Concl: ph -> ta

    A modus ponens deduction with a triple conjunction antecedent.
    (Contributed by NM, 10-May-1993.)
    """
    lb = ProofBuilder(sys, "mp3and")
    h1 = lb.hyp("mp3and.1", "ph -> ps")
    h2 = lb.hyp("mp3and.2", "ph -> ch")
    h3 = lb.hyp("mp3and.3", "ph -> th")
    h4 = lb.hyp("mp3and.4", r"ph -> ( ( ps /\ ch /\ th ) -> ta )")
    s1 = lb.ref(
        "s1",
        r"ph -> ( ps /\ ch /\ th )",
        h1,
        h2,
        h3,
        ref="3jca",
        note="3jca mp3and.1, mp3and.2, mp3and.3",
    )
    res = lb.ref(
        "res",
        "ph -> ta",
        s1,
        h4,
        ref="mpd",
        note="mpd s1, mp3and.4",
    )
    return lb.build(res)


def prove_syl3anbrc(sys: System) -> Proof:
    """syl3anbrc: φ → τ.

    Hyp 1: φ → ψ
    Hyp 2: φ → χ
    Hyp 3: φ → θ
    Hyp 4: τ ↔ ( ψ ∧ χ ∧ θ )
    Concl: φ → τ

    Inference joining three implications and a biconditional with triple
    conjunction.
    (Contributed by NM, 5-Jan-1993.)
    """
    lb = ProofBuilder(sys, "syl3anbrc")
    h1 = lb.hyp("syl3anbrc.1", "φ → ψ")
    h2 = lb.hyp("syl3anbrc.2", "φ → χ")
    h3 = lb.hyp("syl3anbrc.3", "φ → θ")
    h4 = lb.hyp("syl3anbrc.4", "τ ↔ ( ψ ∧ χ ∧ θ )")
    s1 = lb.ref(
        "s1",
        "φ → ( ψ ∧ χ ∧ θ )",
        h1,
        h2,
        h3,
        ref="3jca",
        note="3jca",
    )
    res = lb.ref(
        "res",
        "φ → τ",
        s1,
        h4,
        ref="sylibr",
        note="sylibr",
    )
    return lb.build(res)


def prove_syl3anc(sys: System) -> Proof:
    r"""syl3anc: ph -> ta.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ( ps /\ ch /\ th ) -> ta
    Concl: ph -> ta

    Syllogism inference combined with three antecedents.
    (Contributed by NM, 5-Jan-1993.)
    set.mm proof: ( w3a 3jca syl ).
    """
    lb = ProofBuilder(sys, "syl3anc")
    h1 = lb.hyp("syl3anc.1", "ph -> ps")
    h2 = lb.hyp("syl3anc.2", "ph -> ch")
    h3 = lb.hyp("syl3anc.3", "ph -> th")
    h4 = lb.hyp("syl3anc.4", r"( ps /\ ch /\ th ) -> ta")
    s1 = lb.ref(
        "s1",
        r"ph -> ( ps /\ ch /\ th )",
        h1,
        h2,
        h3,
        ref="3jca",
        note="3jca syl3anc.1, syl3anc.2, syl3anc.3",
    )
    res = lb.ref(
        "res",
        "ph -> ta",
        s1,
        h4,
        ref="syl",
        note="syl s1, syl3anc.4",
    )
    return lb.build(res)


def prove_syl311anc(sys: System) -> Proof:
    r"""syl311anc: ph -> ze.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ph -> ta
    Hyp 5: ph -> et
    Hyp 6: ( ( ps /\ ch /\ th ) /\ ta /\ et ) -> ze
    Concl: ph -> ze

    Syllogism inference combined with three antecedents and two single
    antecedents.  (Contributed by NM, 5-Jan-1993.)
    set.mm proof: w3a 3jca syl3anc.
    """
    lb = ProofBuilder(sys, "syl311anc")
    h1 = lb.hyp("syl311anc.1", "ph -> ps")
    h2 = lb.hyp("syl311anc.2", "ph -> ch")
    h3 = lb.hyp("syl311anc.3", "ph -> th")
    h4 = lb.hyp("syl311anc.4", "ph -> ta")
    h5 = lb.hyp("syl311anc.5", "ph -> et")
    h6 = lb.hyp("syl311anc.6", r"( ( ps /\ ch /\ th ) /\ ta /\ et ) -> ze")
    s1 = lb.ref(
        "s1",
        r"ph -> ( ps /\ ch /\ th )",
        h1,
        h2,
        h3,
        ref="3jca",
        note="3jca syl311anc.1, syl311anc.2, syl311anc.3",
    )
    res = lb.ref(
        "res",
        "ph -> ze",
        s1,
        h4,
        h5,
        h6,
        ref="syl3anc",
        note="syl3anc s1, syl311anc.4, syl311anc.5, syl311anc.6",
    )
    return lb.build(res)


def prove_syl312anc(sys: System) -> Proof:
    r"""syl312anc: ph -> si.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ph -> ta
    Hyp 5: ph -> et
    Hyp 6: ph -> ze
    Hyp 7: ( ( ( ps /\ ch /\ th ) /\ ta /\ ( et /\ ze ) ) -> si
    Concl: ph -> si

    Syllogism inference combined with three antecedents, one antecedent, and
    two conjunctive antecedents.  (Contributed by NM, 5-Jan-1993.)
    set.mm proof: wa jca syl311anc.
    """
    lb = ProofBuilder(sys, "syl312anc")
    h1 = lb.hyp("syl312anc.1", "ph -> ps")
    h2 = lb.hyp("syl312anc.2", "ph -> ch")
    h3 = lb.hyp("syl312anc.3", "ph -> th")
    h4 = lb.hyp("syl312anc.4", "ph -> ta")
    h5 = lb.hyp("syl312anc.5", "ph -> et")
    h6 = lb.hyp("syl312anc.6", "ph -> ze")
    h7 = lb.hyp(
        "syl312anc.7",
        r"( ( ( ps /\ ch /\ th ) /\ ta /\ ( et /\ ze ) ) -> si )",
    )
    s1 = lb.ref(
        "s1",
        r"ph -> ( et /\ ze )",
        h5,
        h6,
        ref="jca",
        note="jca syl312anc.5, syl312anc.6",
    )
    res = lb.ref(
        "res",
        "ph -> si",
        h1,
        h2,
        h3,
        h4,
        s1,
        h7,
        ref="syl311anc",
        note="syl311anc syl312anc.1, syl312anc.2, syl312anc.3, syl312anc.4, s1, syl312anc.7",
    )
    return lb.build(res)


def prove_syl313anc(sys: System) -> Proof:
    r"""syl313anc: ph -> rh.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ph -> ta
    Hyp 5: ph -> et
    Hyp 6: ph -> ze
    Hyp 7: ph -> si
    Hyp 8: ( ( ( ps /\ ch /\ th ) /\ ta /\ ( et /\ ze /\ si ) ) -> rh )
    Concl: ph -> rh

    Syllogism inference combined with three antecedents, one antecedent, and
    three conjunctive antecedents.  (Contributed by NM, 5-Jan-1993.)
    set.mm proof: w3a 3jca syl311anc.
    """
    lb = ProofBuilder(sys, "syl313anc")
    h1 = lb.hyp("syl313anc.1", "ph -> ps")
    h2 = lb.hyp("syl313anc.2", "ph -> ch")
    h3 = lb.hyp("syl313anc.3", "ph -> th")
    h4 = lb.hyp("syl313anc.4", "ph -> ta")
    h5 = lb.hyp("syl313anc.5", "ph -> et")
    h6 = lb.hyp("syl313anc.6", "ph -> ze")
    h7 = lb.hyp("syl313anc.7", "ph -> si")
    h8 = lb.hyp(
        "syl313anc.8",
        r"( ( ( ps /\ ch /\ th ) /\ ta /\ ( et /\ ze /\ si ) ) -> rh )",
    )
    s1 = lb.ref(
        "s1",
        r"ph -> ( et /\ ze /\ si )",
        h5,
        h6,
        h7,
        ref="3jca",
        note="3jca syl313anc.5, syl313anc.6, syl313anc.7",
    )
    res = lb.ref(
        "res",
        "ph -> rh",
        h1,
        h2,
        h3,
        h4,
        s1,
        h8,
        ref="syl311anc",
        note="syl311anc syl313anc.1, syl313anc.2, syl313anc.3, syl313anc.4, s1, syl313anc.8",
    )
    return lb.build(res)


def prove_syl323anc(sys: System) -> Proof:
    r"""syl323anc: ph -> mu.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ph -> ta
    Hyp 5: ph -> et
    Hyp 6: ph -> ze
    Hyp 7: ph -> si
    Hyp 8: ph -> rh
    Hyp 9: ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et ) /\ ( ze /\ si /\ rh ) ) -> mu )
    Concl: ph -> mu

    Syllogism inference combined with three antecedents, two conjunctive
    antecedents, and three conjunctive antecedents.  (Contributed by NM,
    5-Jan-1993.)
    set.mm proof: wa jca syl313anc.
    """
    lb = ProofBuilder(sys, "syl323anc")
    h1 = lb.hyp("syl323anc.1", "ph -> ps")
    h2 = lb.hyp("syl323anc.2", "ph -> ch")
    h3 = lb.hyp("syl323anc.3", "ph -> th")
    h4 = lb.hyp("syl323anc.4", "ph -> ta")
    h5 = lb.hyp("syl323anc.5", "ph -> et")
    h6 = lb.hyp("syl323anc.6", "ph -> ze")
    h7 = lb.hyp("syl323anc.7", "ph -> si")
    h8 = lb.hyp("syl323anc.8", "ph -> rh")
    h9 = lb.hyp(
        "syl323anc.9",
        r"( ( ( ps /\ ch /\ th ) /\ ( ta /\ et ) /\ ( ze /\ si /\ rh ) ) -> mu )",
    )
    s1 = lb.ref(
        "s1",
        r"ph -> ( ta /\ et )",
        h4,
        h5,
        ref="jca",
        note="jca syl323anc.4, syl323anc.5",
    )
    res = lb.ref(
        "res",
        "ph -> mu",
        h1,
        h2,
        h3,
        s1,
        h6,
        h7,
        h8,
        h9,
        ref="syl313anc",
        note="syl313anc syl323anc.1, syl323anc.2, syl323anc.3, s1, "
        "syl323anc.6, syl323anc.7, syl323anc.8, syl323anc.9",
    )
    return lb.build(res)


def prove_syl31anc(sys: System) -> Proof:
    r"""syl31anc: ph -> et.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ph -> ta
    Hyp 5: ( ( ps /\ ch /\ th ) /\ ta ) -> et
    Concl: ph -> et

    Syllogism inference combined with three antecedents and a conjunctive
    antecedent.  (Contributed by NM, 5-Jan-1993.)
    set.mm proof: w3a 3jca syl2anc.
    """
    lb = ProofBuilder(sys, "syl31anc")
    h1 = lb.hyp("syl31anc.1", "ph -> ps")
    h2 = lb.hyp("syl31anc.2", "ph -> ch")
    h3 = lb.hyp("syl31anc.3", "ph -> th")
    h4 = lb.hyp("syl31anc.4", "ph -> ta")
    h5 = lb.hyp("syl31anc.5", r"( ( ps /\ ch /\ th ) /\ ta ) -> et")
    s1 = lb.ref(
        "s1",
        r"ph -> ( ps /\ ch /\ th )",
        h1,
        h2,
        h3,
        ref="3jca",
        note="3jca syl31anc.1, syl31anc.2, syl31anc.3",
    )
    res = lb.ref(
        "res",
        "ph -> et",
        s1,
        h4,
        h5,
        ref="syl2anc",
        note="syl2anc s1, syl31anc.4, syl31anc.5",
    )
    return lb.build(res)


def prove_syl32anc(sys: System) -> Proof:
    r"""syl32anc: ph -> ze.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ph -> ta
    Hyp 5: ph -> et
    Hyp 6: ( ( ps /\ ch /\ th ) /\ ( ta /\ et ) ) -> ze
    Concl: ph -> ze

    Syllogism inference combined with three and two antecedents in conjunctive
    form.  (Contributed by NM, 1-Jan-2013.)
    set.mm proof: wa jca syl31anc.
    """
    lb = ProofBuilder(sys, "syl32anc")
    h1 = lb.hyp("syl3anc.1", "ph -> ps")
    h2 = lb.hyp("syl3anc.2", "ph -> ch")
    h3 = lb.hyp("syl3anc.3", "ph -> th")
    h4 = lb.hyp("syl3Xanc.4", "ph -> ta")
    h5 = lb.hyp("syl23anc.5", "ph -> et")
    h6 = lb.hyp("syl32anc.6", r"( ( ps /\ ch /\ th ) /\ ( ta /\ et ) ) -> ze")
    s1 = lb.ref(
        "s1",
        r"ph -> ( ta /\ et )",
        h4,
        h5,
        ref="jca",
        note="jca syl3Xanc.4, syl23anc.5",
    )
    res = lb.ref(
        "res",
        "ph -> ze",
        h1,
        h2,
        h3,
        s1,
        h6,
        ref="syl31anc",
        note="syl31anc syl3anc.1, syl3anc.2, syl3anc.3, s1, syl32anc.6",
    )
    return lb.build(res)


def prove_syl321anc(sys: System) -> Proof:
    r"""syl321anc: ph -> si.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ph -> ta
    Hyp 5: ph -> et
    Hyp 6: ph -> ze
    Hyp 7: ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et ) /\ ze ) -> si )
    Concl: ph -> si

    Syllogism inference combined with three, two, and one antecedents in
    conjunctive form.  (Contributed by NM, 1-Jan-2013.)
    set.mm proof: wa jca syl311anc.
    """
    lb = ProofBuilder(sys, "syl321anc")
    h1 = lb.hyp("syl3anc.1", "ph -> ps")
    h2 = lb.hyp("syl3anc.2", "ph -> ch")
    h3 = lb.hyp("syl3anc.3", "ph -> th")
    h4 = lb.hyp("syl3Xanc.4", "ph -> ta")
    h5 = lb.hyp("syl23anc.5", "ph -> et")
    h6 = lb.hyp("syl33anc.6", "ph -> ze")
    h7 = lb.hyp(
        "syl321anc.7",
        r"( ( ( ps /\ ch /\ th ) /\ ( ta /\ et ) /\ ze ) -> si )",
    )
    s1 = lb.ref(
        "s1",
        r"ph -> ( ta /\ et )",
        h4,
        h5,
        ref="jca",
        note="jca syl3Xanc.4, syl23anc.5",
    )
    res = lb.ref(
        "res",
        "ph -> si",
        h1,
        h2,
        h3,
        s1,
        h6,
        h7,
        ref="syl311anc",
        note="syl311anc syl3anc.1, syl3anc.2, syl3anc.3, s1, syl33anc.6, syl321anc.7",
    )
    return lb.build(res)


def prove_syl322anc(sys: System) -> Proof:
    r"""syl322anc: ph -> rh.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ph -> ta
    Hyp 5: ph -> et
    Hyp 6: ph -> ze
    Hyp 7: ph -> si
    Hyp 8: ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et ) /\ ( ze /\ si ) ) -> rh )
    Concl: ph -> rh

    Syllogism inference combined with three, two, and two antecedents in
    conjunctive form.  (Contributed by NM, 1-Jan-2013.)
    set.mm proof: wa jca syl321anc.
    """
    lb = ProofBuilder(sys, "syl322anc")
    h1 = lb.hyp("syl3anc.1", "ph -> ps")
    h2 = lb.hyp("syl3anc.2", "ph -> ch")
    h3 = lb.hyp("syl3anc.3", "ph -> th")
    h4 = lb.hyp("syl3Xanc.4", "ph -> ta")
    h5 = lb.hyp("syl23anc.5", "ph -> et")
    h6 = lb.hyp("syl33anc.6", "ph -> ze")
    h7 = lb.hyp("syl133anc.7", "ph -> si")
    h8 = lb.hyp(
        "syl322anc.8",
        r"( ( ( ps /\ ch /\ th ) /\ ( ta /\ et ) /\ ( ze /\ si ) ) -> rh )",
    )
    s1 = lb.ref(
        "s1",
        r"ph -> ( ze /\ si )",
        h6,
        h7,
        ref="jca",
        note="jca syl33anc.6, syl133anc.7",
    )
    res = lb.ref(
        "res",
        "ph -> rh",
        h1,
        h2,
        h3,
        h4,
        h5,
        s1,
        h8,
        ref="syl321anc",
        note="syl321anc syl3anc.1, syl3anc.2, syl3anc.3, syl3Xanc.4, syl23anc.5, s1, syl322anc.8",
    )
    return lb.build(res)


def prove_syl33anc(sys: System) -> Proof:
    r"""syl33anc: ph -> si.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ph -> ta
    Hyp 5: ph -> et
    Hyp 6: ph -> ze
    Hyp 7: ( ( ps /\ ch /\ th ) /\ ( ta /\ et /\ ze ) ) -> si
    Concl: ph -> si

    Syllogism inference combined with two groups of three antecedents in
    conjunctive form.  (Contributed by NM, 1-Jan-2013.)
    set.mm proof: w3a 3jca syl13anc.
    """
    lb = ProofBuilder(sys, "syl33anc")
    h1 = lb.hyp("syl3anc.1", "ph -> ps")
    h2 = lb.hyp("syl3anc.2", "ph -> ch")
    h3 = lb.hyp("syl3anc.3", "ph -> th")
    h4 = lb.hyp("syl3Xanc.4", "ph -> ta")
    h5 = lb.hyp("syl23anc.5", "ph -> et")
    h6 = lb.hyp("syl33anc.6", "ph -> ze")
    h7 = lb.hyp("syl33anc.7", r"( ( ps /\ ch /\ th ) /\ ( ta /\ et /\ ze ) ) -> si")
    s1 = lb.ref(
        "s1",
        r"ph -> ( ps /\ ch /\ th )",
        h1,
        h2,
        h3,
        ref="3jca",
        note="3jca syl3anc.1, syl3anc.2, syl3anc.3",
    )
    res = lb.ref(
        "res",
        "ph -> si",
        s1,
        h4,
        h5,
        h6,
        h7,
        ref="syl13anc",
        note="syl13anc s1, syl3Xanc.4, syl23anc.5, syl33anc.6, syl33anc.7",
    )
    return lb.build(res)


def prove_syl331anc(sys: System) -> Proof:
    r"""syl331anc: ph -> rh.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ph -> ta
    Hyp 5: ph -> et
    Hyp 6: ph -> ze
    Hyp 7: ph -> si
    Hyp 8: ( ( ps /\ ch /\ th ) /\ ( ta /\ et /\ ze ) /\ si ) -> rh
    Concl: ph -> rh

    Syllogism inference combined with three, three, and one antecedents in
    conjunctive form.  (Contributed by NM, 1-Jan-2013.)
    set.mm proof: w3a 3jca syl311anc.
    """
    lb = ProofBuilder(sys, "syl331anc")
    h1 = lb.hyp("syl3anc.1", "ph -> ps")
    h2 = lb.hyp("syl3anc.2", "ph -> ch")
    h3 = lb.hyp("syl3anc.3", "ph -> th")
    h4 = lb.hyp("syl3Xanc.4", "ph -> ta")
    h5 = lb.hyp("syl23anc.5", "ph -> et")
    h6 = lb.hyp("syl33anc.6", "ph -> ze")
    h7 = lb.hyp("syl331anc.7", "ph -> si")
    h8 = lb.hyp("syl331anc.8", r"( ( ps /\ ch /\ th ) /\ ( ta /\ et /\ ze ) /\ si ) -> rh")
    s1 = lb.ref(
        "s1",
        r"ph -> ( ta /\ et /\ ze )",
        h4,
        h5,
        h6,
        ref="3jca",
        note="3jca syl3Xanc.4, syl23anc.5, syl33anc.6",
    )
    res = lb.ref(
        "res",
        "ph -> rh",
        h1,
        h2,
        h3,
        s1,
        h7,
        h8,
        ref="syl311anc",
        note="syl311anc syl3anc.1, syl3anc.2, syl3anc.3, s1, syl331anc.7, syl331anc.8",
    )
    return lb.build(res)


def prove_syl332anc(sys: System) -> Proof:
    r"""syl332anc: ph -> mu.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ph -> ta
    Hyp 5: ph -> et
    Hyp 6: ph -> ze
    Hyp 7: ph -> si
    Hyp 8: ph -> rh
    Hyp 9: ( ( ps /\ ch /\ th ) /\ ( ta /\ et /\ ze ) /\ ( si /\ rh ) ) -> mu
    Concl: ph -> mu

    Syllogism inference combined with three, three, and two antecedents in
    conjunctive form.  (Contributed by NM, 1-Jan-2013.)
    set.mm proof: wa jca syl331anc.
    """
    lb = ProofBuilder(sys, "syl332anc")
    h1 = lb.hyp("syl3anc.1", "ph -> ps")
    h2 = lb.hyp("syl3anc.2", "ph -> ch")
    h3 = lb.hyp("syl3anc.3", "ph -> th")
    h4 = lb.hyp("syl3Xanc.4", "ph -> ta")
    h5 = lb.hyp("syl23anc.5", "ph -> et")
    h6 = lb.hyp("syl33anc.6", "ph -> ze")
    h7 = lb.hyp("syl133anc.7", "ph -> si")
    h8 = lb.hyp("syl233anc.8", "ph -> rh")
    h9 = lb.hyp(
        "syl332anc.9", r"( ( ps /\ ch /\ th ) /\ ( ta /\ et /\ ze ) /\ ( si /\ rh ) ) -> mu"
    )
    s1 = lb.ref(
        "s1",
        r"ph -> ( si /\ rh )",
        h7,
        h8,
        ref="jca",
        note="jca syl133anc.7, syl233anc.8",
    )
    res = lb.ref(
        "res",
        "ph -> mu",
        h1,
        h2,
        h3,
        h4,
        h5,
        h6,
        s1,
        h9,
        ref="syl331anc",
        note="syl331anc syl3anc.1, syl3anc.2, syl3anc.3, syl3Xanc.4, syl23anc.5, syl33anc.6, s1, syl332anc.9",
    )
    return lb.build(res)


def prove_syl333anc(sys: System) -> Proof:
    r"""syl333anc: ph -> la.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ph -> ta
    Hyp 5: ph -> et
    Hyp 6: ph -> ze
    Hyp 7: ph -> si
    Hyp 8: ph -> rh
    Hyp 9: ph -> mu
    Hyp 10: ( ( ps /\ ch /\ th ) /\ ( ta /\ et /\ ze ) /\ ( si /\ rh /\ mu ) ) -> la
    Concl: ph -> la

    Syllogism inference combined with three groups of three antecedents in
    conjunctive form.  (Contributed by NM, 1-Jan-2013.)
    set.mm proof: w3a 3jca syl331anc.
    """
    lb = ProofBuilder(sys, "syl333anc")
    h1 = lb.hyp("syl3anc.1", "ph -> ps")
    h2 = lb.hyp("syl3anc.2", "ph -> ch")
    h3 = lb.hyp("syl3anc.3", "ph -> th")
    h4 = lb.hyp("syl3Xanc.4", "ph -> ta")
    h5 = lb.hyp("syl23anc.5", "ph -> et")
    h6 = lb.hyp("syl33anc.6", "ph -> ze")
    h7 = lb.hyp("syl133anc.7", "ph -> si")
    h8 = lb.hyp("syl233anc.8", "ph -> rh")
    h9 = lb.hyp("syl333anc.9", "ph -> mu")
    h10 = lb.hyp(
        "syl333anc.10", r"( ( ps /\ ch /\ th ) /\ ( ta /\ et /\ ze ) /\ ( si /\ rh /\ mu ) ) -> la"
    )
    s1 = lb.ref(
        "s1",
        r"ph -> ( si /\ rh /\ mu )",
        h7,
        h8,
        h9,
        ref="3jca",
        note="3jca syl133anc.7, syl233anc.8, syl333anc.9",
    )
    res = lb.ref(
        "res",
        "ph -> la",
        h1,
        h2,
        h3,
        h4,
        h5,
        h6,
        s1,
        h10,
        ref="syl331anc",
        note="syl331anc syl3anc.1, syl3anc.2, syl3anc.3, syl3Xanc.4, syl23anc.5, syl33anc.6, s1, syl333anc.10",
    )
    return lb.build(res)


def prove_syl113anc(sys: System) -> Proof:
    r"""syl113anc: ph -> ze.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ph -> ta
    Hyp 5: ph -> et
    Hyp 6: ( ps /\ ch /\ ( th /\ ta /\ et ) ) -> ze
    Concl: ph -> ze

    Syllogism inference combined with one, one, and three antecedents in
    conjunctive form.  (Contributed by NM, 1-Jan-2013.)
    set.mm proof: w3a 3jca syl3anc.
    """
    lb = ProofBuilder(sys, "syl113anc")
    h1 = lb.hyp("syl3anc.1", "ph -> ps")
    h2 = lb.hyp("syl3anc.2", "ph -> ch")
    h3 = lb.hyp("syl3anc.3", "ph -> th")
    h4 = lb.hyp("syl3Xanc.4", "ph -> ta")
    h5 = lb.hyp("syl23anc.5", "ph -> et")
    h6 = lb.hyp("syl113anc.6", r"( ps /\ ch /\ ( th /\ ta /\ et ) ) -> ze")
    s1 = lb.ref(
        "s1",
        r"ph -> ( th /\ ta /\ et )",
        h3,
        h4,
        h5,
        ref="3jca",
        note="3jca syl3anc.3, syl3Xanc.4, syl23anc.5",
    )
    res = lb.ref(
        "res",
        "ph -> ze",
        h1,
        h2,
        s1,
        h6,
        ref="syl3anc",
        note="syl3anc syl3anc.1, syl3anc.2, s1, syl113anc.6",
    )
    return lb.build(res)


def prove_syl123anc(sys: System) -> Proof:
    r"""syl123anc: ph -> si.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ph -> ta
    Hyp 5: ph -> et
    Hyp 6: ph -> ze
    Hyp 7: ( ps /\ ( ch /\ th ) /\ ( ta /\ et /\ ze ) ) -> si
    Concl: ph -> si

    Syllogism inference combined with one, two, and three antecedents in
    conjunctive form.  (Contributed by NM, 1-Jan-2013.)
    set.mm proof: wa jca syl113anc.
    """
    lb = ProofBuilder(sys, "syl123anc")
    h1 = lb.hyp("syl3anc.1", "ph -> ps")
    h2 = lb.hyp("syl3anc.2", "ph -> ch")
    h3 = lb.hyp("syl3anc.3", "ph -> th")
    h4 = lb.hyp("syl3Xanc.4", "ph -> ta")
    h5 = lb.hyp("syl23anc.5", "ph -> et")
    h6 = lb.hyp("syl33anc.6", "ph -> ze")
    h7 = lb.hyp("syl123anc.7", r"( ps /\ ( ch /\ th ) /\ ( ta /\ et /\ ze ) ) -> si")
    s1 = lb.ref(
        "s1",
        r"ph -> ( ch /\ th )",
        h2,
        h3,
        ref="jca",
        note="jca syl3anc.2, syl3anc.3",
    )
    res = lb.ref(
        "res",
        "ph -> si",
        h1,
        s1,
        h4,
        h5,
        h6,
        h7,
        ref="syl113anc",
        note="syl113anc syl3anc.1, s1, syl3Xanc.4, syl23anc.5, syl33anc.6, syl123anc.7",
    )
    return lb.build(res)


def prove_syl23anc(sys: System) -> Proof:
    r"""syl23anc: ph -> ze.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ph -> ta
    Hyp 5: ph -> et
    Hyp 6: ( ( ps /\ ch ) /\ ( th /\ ta /\ et ) ) -> ze
    Concl: ph -> ze

    Syllogism inference combined with two and three antecedents in conjunctive
    form.  (Contributed by NM, 1-Jan-2013.)
    set.mm proof: wa jca syl13anc.
    """
    lb = ProofBuilder(sys, "syl23anc")
    h1 = lb.hyp("syl3anc.1", "ph -> ps")
    h2 = lb.hyp("syl3anc.2", "ph -> ch")
    h3 = lb.hyp("syl3anc.3", "ph -> th")
    h4 = lb.hyp("syl3Xanc.4", "ph -> ta")
    h5 = lb.hyp("syl23anc.5", "ph -> et")
    h6 = lb.hyp("syl23anc.6", r"( ( ps /\ ch ) /\ ( th /\ ta /\ et ) ) -> ze")
    s1 = lb.ref(
        "s1",
        r"ph -> ( ps /\ ch )",
        h1,
        h2,
        ref="jca",
        note="jca syl3anc.1, syl3anc.2",
    )
    res = lb.ref(
        "res",
        "ph -> ze",
        s1,
        h3,
        h4,
        h5,
        h6,
        ref="syl13anc",
        note="syl13anc s1, syl3anc.3, syl3Xanc.4, syl23anc.5, syl23anc.6",
    )
    return lb.build(res)


def prove_syl231anc(sys: System) -> Proof:
    r"""syl231anc: ph -> si.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ph -> ta
    Hyp 5: ph -> et
    Hyp 6: ph -> ze
    Hyp 7: ( ( ( ps /\ ch ) /\ ( th /\ ta /\ et ) /\ ze ) -> si )
    Concl: ph -> si

    Syllogism inference combined with two, three, and one antecedents in
    conjunctive form.  (Contributed by NM, 1-Jan-2013.)
    set.mm proof: wa jca syl131anc.
    """
    lb = ProofBuilder(sys, "syl231anc")
    h1 = lb.hyp("syl3anc.1", "ph -> ps")
    h2 = lb.hyp("syl3anc.2", "ph -> ch")
    h3 = lb.hyp("syl3anc.3", "ph -> th")
    h4 = lb.hyp("syl3Xanc.4", "ph -> ta")
    h5 = lb.hyp("syl23anc.5", "ph -> et")
    h6 = lb.hyp("syl33anc.6", "ph -> ze")
    h7 = lb.hyp("syl231anc.7", r"( ( ( ps /\ ch ) /\ ( th /\ ta /\ et ) /\ ze ) -> si )")
    s1 = lb.ref(
        "s1",
        r"ph -> ( ps /\ ch )",
        h1,
        h2,
        ref="jca",
        note="jca syl3anc.1, syl3anc.2",
    )
    res = lb.ref(
        "res",
        "ph -> si",
        s1,
        h3,
        h4,
        h5,
        h6,
        h7,
        ref="syl131anc",
        note="syl131anc s1, syl3anc.3, syl3Xanc.4, syl23anc.5, syl33anc.6, syl231anc.7",
    )
    return lb.build(res)


def prove_syl232anc(sys: System) -> Proof:
    r"""syl232anc: ph -> rh.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ph -> ta
    Hyp 5: ph -> et
    Hyp 6: ph -> ze
    Hyp 7: ph -> si
    Hyp 8: ( ( ( ps /\ ch ) /\ ( th /\ ta /\ et ) /\ ( ze /\ si ) ) -> rh )
    Concl: ph -> rh

    Syllogism inference combined with two, three, and two antecedents in
    conjunctive form.  (Contributed by NM, 1-Jan-2013.)
    set.mm proof: wa jca syl231anc.
    """
    lb = ProofBuilder(sys, "syl232anc")
    h1 = lb.hyp("syl3anc.1", "ph -> ps")
    h2 = lb.hyp("syl3anc.2", "ph -> ch")
    h3 = lb.hyp("syl3anc.3", "ph -> th")
    h4 = lb.hyp("syl3Xanc.4", "ph -> ta")
    h5 = lb.hyp("syl23anc.5", "ph -> et")
    h6 = lb.hyp("syl33anc.6", "ph -> ze")
    h7 = lb.hyp("syl133anc.7", "ph -> si")
    h8 = lb.hyp("syl232anc.8", r"( ( ( ps /\ ch ) /\ ( th /\ ta /\ et ) /\ ( ze /\ si ) ) -> rh )")
    s1 = lb.ref(
        "s1",
        r"ph -> ( ze /\ si )",
        h6,
        h7,
        ref="jca",
        note="jca syl33anc.6, syl133anc.7",
    )
    res = lb.ref(
        "res",
        "ph -> rh",
        h1,
        h2,
        h3,
        h4,
        h5,
        s1,
        h8,
        ref="syl231anc",
        note="syl231anc syl3anc.1, syl3anc.2, syl3anc.3, syl3Xanc.4, syl23anc.5, s1, syl232anc.8",
    )
    return lb.build(res)


def prove_syl233anc(sys: System) -> Proof:
    r"""syl233anc: ph -> mu.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ph -> ta
    Hyp 5: ph -> et
    Hyp 6: ph -> ze
    Hyp 7: ph -> si
    Hyp 8: ph -> rh
    Hyp 9: ( ( ps /\ ch ) /\ ( th /\ ta /\ et ) /\ ( ze /\ si /\ rh ) ) -> mu
    Concl: ph -> mu

    Syllogism inference combined with two, three, and three antecedents in
    conjunctive form.  (Contributed by NM, 1-Jan-2013.)
    set.mm proof: wa jca syl133anc.
    """
    lb = ProofBuilder(sys, "syl233anc")
    h1 = lb.hyp("syl3anc.1", "ph -> ps")
    h2 = lb.hyp("syl3anc.2", "ph -> ch")
    h3 = lb.hyp("syl3anc.3", "ph -> th")
    h4 = lb.hyp("syl3Xanc.4", "ph -> ta")
    h5 = lb.hyp("syl23anc.5", "ph -> et")
    h6 = lb.hyp("syl33anc.6", "ph -> ze")
    h7 = lb.hyp("syl133anc.7", "ph -> si")
    h8 = lb.hyp("syl233anc.8", "ph -> rh")
    h9 = lb.hyp(
        "syl233anc.9",
        r"( ( ps /\ ch ) /\ ( th /\ ta /\ et ) /\ ( ze /\ si /\ rh ) ) -> mu",
    )
    s1 = lb.ref(
        "s1",
        r"ph -> ( ps /\ ch )",
        h1,
        h2,
        ref="jca",
        note="jca syl3anc.1, syl3anc.2",
    )
    res = lb.ref(
        "res",
        "ph -> mu",
        s1,
        h3,
        h4,
        h5,
        h6,
        h7,
        h8,
        h9,
        ref="syl133anc",
        note="syl133anc s1, syl3anc.3, syl3Xanc.4, syl23anc.5, syl33anc.6, syl133anc.7, syl233anc.8, syl233anc.9",
    )
    return lb.build(res)


def prove_syl112anc(sys: System) -> Proof:
    r"""syl112anc: ph -> et.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ph -> ta
    Hyp 5: ( ps /\ ch /\ ( th /\ ta ) ) -> et
    Concl: ph -> et

    Syllogism inference combined with one, one, and two antecedents in
    conjunctive form.  (Contributed by NM, 1-Jan-2013.)
    set.mm proof: wa jca syl3anc.
    """
    lb = ProofBuilder(sys, "syl112anc")
    h1 = lb.hyp("syl3anc.1", "ph -> ps")
    h2 = lb.hyp("syl3anc.2", "ph -> ch")
    h3 = lb.hyp("syl3anc.3", "ph -> th")
    h4 = lb.hyp("syl3Xanc.4", "ph -> ta")
    h5 = lb.hyp("syl112anc.5", r"( ps /\ ch /\ ( th /\ ta ) ) -> et")
    s1 = lb.ref(
        "s1",
        r"ph -> ( th /\ ta )",
        h3,
        h4,
        ref="jca",
        note="jca syl3anc.3, syl3Xanc.4",
    )
    res = lb.ref(
        "res",
        "ph -> et",
        h1,
        h2,
        s1,
        h5,
        ref="syl3anc",
        note="syl3anc syl3anc.1, syl3anc.2, s1, syl112anc.5",
    )
    return lb.build(res)


def prove_syl121anc(sys: System) -> Proof:
    r"""syl121anc: ph -> et.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ph -> ta
    Hyp 5: ( ps /\ ( ch /\ th ) /\ ta ) -> et
    Concl: ph -> et

    Syllogism inference combined with one, two, and one antecedents in
    conjunctive form.  (Contributed by NM, 1-Jan-2013.)
    set.mm proof: wa jca syl3anc.
    """
    lb = ProofBuilder(sys, "syl121anc")
    h1 = lb.hyp("syl3anc.1", "ph -> ps")
    h2 = lb.hyp("syl3anc.2", "ph -> ch")
    h3 = lb.hyp("syl3anc.3", "ph -> th")
    h4 = lb.hyp("syl3Xanc.4", "ph -> ta")
    h5 = lb.hyp("syl121anc.5", r"( ps /\ ( ch /\ th ) /\ ta ) -> et")
    s1 = lb.ref(
        "s1",
        r"ph -> ( ch /\ th )",
        h2,
        h3,
        ref="jca",
        note="jca syl3anc.2, syl3anc.3",
    )
    res = lb.ref(
        "res",
        "ph -> et",
        h1,
        s1,
        h4,
        h5,
        ref="syl3anc",
        note="syl3anc syl3anc.1, s1, syl3Xanc.4, syl121anc.5",
    )
    return lb.build(res)


def prove_syl122anc(sys: System) -> Proof:
    r"""syl122anc: ph -> ze.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ph -> ta
    Hyp 5: ph -> et
    Hyp 6: ( ps /\ ( ch /\ th ) /\ ( ta /\ et ) ) -> ze
    Concl: ph -> ze

    Syllogism inference combined with one, two, and two antecedents in
    conjunctive form.  (Contributed by NM, 1-Jan-2013.)
    set.mm proof: wa jca syl121anc.
    """
    lb = ProofBuilder(sys, "syl122anc")
    h1 = lb.hyp("syl3anc.1", "ph -> ps")
    h2 = lb.hyp("syl3anc.2", "ph -> ch")
    h3 = lb.hyp("syl3anc.3", "ph -> th")
    h4 = lb.hyp("syl3Xanc.4", "ph -> ta")
    h5 = lb.hyp("syl23anc.5", "ph -> et")
    h6 = lb.hyp("syl122anc.6", r"( ps /\ ( ch /\ th ) /\ ( ta /\ et ) ) -> ze")
    s1 = lb.ref(
        "s1",
        r"ph -> ( ta /\ et )",
        h4,
        h5,
        ref="jca",
        note="jca syl3Xanc.4, syl23anc.5",
    )
    res = lb.ref(
        "res",
        "ph -> ze",
        h1,
        h2,
        h3,
        s1,
        h6,
        ref="syl121anc",
        note="syl121anc syl3anc.1, syl3anc.2, syl3anc.3, s1, syl122anc.6",
    )
    return lb.build(res)


def prove_syl221anc(sys: System) -> Proof:
    r"""syl221anc: ph -> ze.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ph -> ta
    Hyp 5: ph -> et
    Hyp 6: ( ( ps /\ ch ) /\ ( th /\ ta ) /\ et ) -> ze
    Concl: ph -> ze

    Syllogism combined with two conjunctive antecedents, two conjunctive
    antecedents, and one antecedent.  (Contributed by NM, 1-Jan-2013.)
    set.mm proof: wa jca syl211anc.
    """
    lb = ProofBuilder(sys, "syl221anc")
    h1 = lb.hyp("syl3anc.1", "ph -> ps")
    h2 = lb.hyp("syl3anc.2", "ph -> ch")
    h3 = lb.hyp("syl3anc.3", "ph -> th")
    h4 = lb.hyp("syl3Xanc.4", "ph -> ta")
    h5 = lb.hyp("syl23anc.5", "ph -> et")
    h6 = lb.hyp("syl221anc.6", r"( ( ps /\ ch ) /\ ( th /\ ta ) /\ et ) -> ze")
    s1 = lb.ref(
        "s1",
        r"ph -> ( th /\ ta )",
        h3,
        h4,
        ref="jca",
        note="jca syl3anc.3, syl3Xanc.4",
    )
    res = lb.ref(
        "res",
        "ph -> ze",
        h1,
        h2,
        s1,
        h5,
        h6,
        ref="syl211anc",
        note="syl211anc syl3anc.1, syl3anc.2, s1, syl23anc.5, syl221anc.6",
    )
    return lb.build(res)


def prove_syl222anc(sys: System) -> Proof:
    r"""syl222anc: ph -> si.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ph -> ta
    Hyp 5: ph -> et
    Hyp 6: ph -> ze
    Hyp 7: ( ( ps /\ ch ) /\ ( th /\ ta ) /\ ( et /\ ze ) ) -> si
    Concl: ph -> si

    Syllogism combined with two conjunctive antecedents, two conjunctive
    antecedents, and two conjunctive antecedents.  (Contributed by NM,
    1-Jan-2013.)  set.mm proof: wa jca syl221anc.
    """
    lb = ProofBuilder(sys, "syl222anc")
    h1 = lb.hyp("syl3anc.1", "ph -> ps")
    h2 = lb.hyp("syl3anc.2", "ph -> ch")
    h3 = lb.hyp("syl3anc.3", "ph -> th")
    h4 = lb.hyp("syl3Xanc.4", "ph -> ta")
    h5 = lb.hyp("syl23anc.5", "ph -> et")
    h6 = lb.hyp("syl33anc.6", "ph -> ze")
    h7 = lb.hyp("syl222anc.7", r"( ( ps /\ ch ) /\ ( th /\ ta ) /\ ( et /\ ze ) ) -> si")
    s1 = lb.ref(
        "s1",
        r"ph -> ( et /\ ze )",
        h5,
        h6,
        ref="jca",
        note="jca syl23anc.5, syl33anc.6",
    )
    res = lb.ref(
        "res",
        "ph -> si",
        h1,
        h2,
        h3,
        h4,
        s1,
        h7,
        ref="syl221anc",
        note="syl221anc syl3anc.1, syl3anc.2, syl3anc.3, syl3Xanc.4, s1, syl222anc.7",
    )
    return lb.build(res)


def prove_syl223anc(sys: System) -> Proof:
    r"""syl223anc: ph -> rh.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ph -> ta
    Hyp 5: ph -> et
    Hyp 6: ph -> ze
    Hyp 7: ph -> si
    Hyp 8: ( ( ps /\ ch ) /\ ( th /\ ta ) /\ ( et /\ ze /\ si ) ) -> rh
    Concl: ph -> rh

    Syllogism combined with two conjunctive antecedents, two conjunctive
    antecedents, and three conjunctive antecedents.  (Contributed by NM,
    1-Jan-2013.)  set.mm proof: wa jca syl213anc.
    """
    lb = ProofBuilder(sys, "syl223anc")
    h1 = lb.hyp("syl3anc.1", "ph -> ps")
    h2 = lb.hyp("syl3anc.2", "ph -> ch")
    h3 = lb.hyp("syl3anc.3", "ph -> th")
    h4 = lb.hyp("syl3Xanc.4", "ph -> ta")
    h5 = lb.hyp("syl23anc.5", "ph -> et")
    h6 = lb.hyp("syl33anc.6", "ph -> ze")
    h7 = lb.hyp("syl133anc.7", "ph -> si")
    h8 = lb.hyp(
        "syl223anc.8",
        r"( ( ps /\ ch ) /\ ( th /\ ta ) /\ ( et /\ ze /\ si ) ) -> rh",
    )
    s1 = lb.ref(
        "s1",
        r"ph -> ( th /\ ta )",
        h3,
        h4,
        ref="jca",
        note="jca syl3anc.3, syl3Xanc.4",
    )
    res = lb.ref(
        "res",
        "ph -> rh",
        h1,
        h2,
        s1,
        h5,
        h6,
        h7,
        h8,
        ref="syl213anc",
        note="syl213anc syl3anc.1, syl3anc.2, s1, syl23anc.5, syl33anc.6, syl133anc.7, syl223anc.8",
    )
    return lb.build(res)


def prove_syl1111anc(sys: System) -> Proof:
    r"""syl1111anc: ph -> et.

    Hyp 1: ph -> ps
    Hyp 2: ph -> ch
    Hyp 3: ph -> th
    Hyp 4: ph -> ta
    Hyp 5: ( ( ( ( ps /\ ch ) /\ th ) /\ ta ) -> et
    Concl: ph -> et

    Syllogism combined with four nested conjunctive antecedents.
    (Contributed by NM, 1-Jan-2013.)
    set.mm proof: wa jca syl21anc.
    """
    lb = ProofBuilder(sys, "syl1111anc")
    h1 = lb.hyp("syl1111anc.1", "ph -> ps")
    h2 = lb.hyp("syl1111anc.2", "ph -> ch")
    h3 = lb.hyp("syl1111anc.3", "ph -> th")
    h4 = lb.hyp("syl1111anc.4", "ph -> ta")
    h5 = lb.hyp("syl1111anc.5", r"( ( ( ( ps /\ ch ) /\ th ) /\ ta ) -> et )")
    s1 = lb.ref(
        "s1",
        r"ph -> ( ps /\ ch )",
        h1,
        h2,
        ref="jca",
        note="jca syl1111anc.1, syl1111anc.2",
    )
    res = lb.ref(
        "res",
        "ph -> et",
        s1,
        h3,
        h4,
        h5,
        ref="syl21anc",
        note="syl21anc s1, syl1111anc.3, syl1111anc.4, syl1111anc.5",
    )
    return lb.build(res)


def prove_mpsyl4anc(sys: System) -> Proof:
    r"""mpsyl4anc: th -> et.

    Hyp 1: ph
    Hyp 2: ps
    Hyp 3: ch
    Hyp 4: th -> ta
    Hyp 5: ( ( ( ( ph /\ ps ) /\ ch ) /\ ta ) -> et )
    Concl: th -> et

    Syllogism combined with four conjunctive antecedents (inference form of
    ~ syl1111anc ).  (Contributed by NM, 1-Jan-2013.)
    set.mm proof: a1i syl1111anc.
    """
    lb = ProofBuilder(sys, "mpsyl4anc")
    h1 = lb.hyp("mpsyl4anc.1", "ph")
    h2 = lb.hyp("mpsyl4anc.2", "ps")
    h3 = lb.hyp("mpsyl4anc.3", "ch")
    h4 = lb.hyp("mpsyl4anc.4", "th -> ta")
    h5 = lb.hyp("mpsyl4anc.5", r"( ( ( ( ph /\ ps ) /\ ch ) /\ ta ) -> et )")
    s1 = lb.ref("s1", "th -> ph", h1, ref="a1i", note="a1i mpsyl4anc.1")
    s2 = lb.ref("s2", "th -> ps", h2, ref="a1i", note="a1i mpsyl4anc.2")
    s3 = lb.ref("s3", "th -> ch", h3, ref="a1i", note="a1i mpsyl4anc.3")
    res = lb.ref(
        "res",
        "th -> et",
        s1,
        s2,
        s3,
        h4,
        h5,
        ref="syl1111anc",
        note="syl1111anc s1, s2, s3, mpsyl4anc.4, mpsyl4anc.5",
    )
    return lb.build(res)


def prove_olcs(sys: System) -> Proof:
    """olcs: ( ps -> ch ).  Hyp: ( ( ph ∨ ps ) -> ch ).

    Inference eliminating a disjunct.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: orcoms orcs.
    """
    lb = ProofBuilder(sys, "olcs")
    h1 = lb.hyp("olcs.1", "( ( ph ∨ ps ) -> ch )")
    s1 = lb.ref("s1", "( ( ps ∨ ph ) -> ch )", h1, ref="orcoms", note="orcoms")
    res = lb.ref("res", "( ps -> ch )", s1, ref="orcs", note="orcs")
    return lb.build(res)


def prove_orcnd(sys: System) -> Proof:
    """orcnd: ( ph -> ch ).

    Hyp: orcnd.1: ( ph -> ( ps \\/ ch ) ), orcnd.2: ( ph -> -. ps ).
    Deduction form of ~ orel.  (Contributed by NM, 29-Dec-1992.)
    set.mm proof: orcomd olcnd.
    """
    lb = ProofBuilder(sys, "orcnd")
    h1 = lb.hyp("orcnd.1", "( ph -> ( ps \\/ ch ) )")
    h2 = lb.hyp("orcnd.2", "( ph -> -. ps )")
    s1 = lb.ref("s1", "( ph -> ( ch \\/ ps ) )", h1, ref="orcomd", note="orcomd orcnd.1")
    res = lb.ref("res", "( ph -> ch )", s1, h2, ref="olcnd", note="olcnd s1, orcnd.2")
    return lb.build(res)


def prove_mercolem1(sys: System) -> Proof:
    """mercolem1: (((φ → ψ) → χ) → (ψ → (θ → χ))).

    Used to rederive the Tarski-Bernays-Wajsberg axioms from merco2.
    (Contributed by Anthony Hart, 16-Aug-2011.)
    """
    lb = ProofBuilder(sys, "mercolem1")

    # Step 33 (A): merco2 with φ=φ, ψ=φ, χ=φ, θ=φ, τ=φ, η=φ
    s33 = lb.ref(
        "s33",
        "( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) )",
        ref="merco2",
        note="merco2",
    )

    # Step 38: same as s33
    s38 = lb.ref(
        "s38",
        "( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) )",
        ref="merco2",
        note="merco2",
    )

    # Step 57 (B): merco2 with φ=χ, ψ=φ, χ=φ, θ=(φ→ψ), τ=ψ, η=θ
    s57 = lb.ref(
        "s57",
        "( ( ( χ → φ ) → ( ( ⊥ → φ ) → ( φ → ψ ) ) ) → ( ( ( φ → ψ ) → χ ) → ( ψ → ( θ → χ ) ) ) )",
        ref="merco2",
        note="merco2",
    )

    # Step 94 (C): merco2 with φ=ψ, ψ=(θ→χ), χ=φ, θ=⊥, τ=(⊥→φ), η=φ
    s94 = lb.ref(
        "s94",
        "( ( ( ψ → ( θ → χ ) ) → ( ( ⊥ → φ ) → ⊥ ) ) → ( ( ⊥ → ψ ) → ( ( ⊥ → φ ) → ( φ → ψ ) ) ) )",
        ref="merco2",
        note="merco2",
    )

    # Step 101: merco2 with φ=(ψ→(θ→χ)), ψ=((⊥→φ)→⊥), χ=ψ, θ=((⊥→φ)→(φ→ψ)),
    #           τ=(⊥→φ), η=((φ→ψ)→χ)
    s101 = lb.ref(
        "s101",
        "( ( ( ( ψ → ( θ → χ ) ) → ( ( ⊥ → φ ) → ⊥ ) ) → ( ( ⊥ → ψ ) → ( ( ⊥ → φ ) → ( φ → ψ ) ) ) ) → ( ( ( ( ⊥ → φ ) → ( φ → ψ ) ) → ( ψ → ( θ → χ ) ) ) → ( ( ⊥ → φ ) → ( ( ( φ → ψ ) → χ ) → ( ψ → ( θ → χ ) ) ) ) ) )",
        ref="merco2",
        note="merco2",
    )

    # Step 102: ax-mp(94, 101)
    s102 = lb.mp(
        "s102",
        s94,
        s101,
        "MP s94, s101",
    )

    # Step 109: merco2 with φ=((⊥→φ)→(φ→ψ)), ψ=(ψ→(θ→χ)), χ=φ,
    #           θ=(((φ→ψ)→χ)→(ψ→(θ→χ))), τ=(⊥→φ), η=(χ→φ)
    s109 = lb.ref(
        "s109",
        "( ( ( ( ( ⊥ → φ ) → ( φ → ψ ) ) → ( ψ → ( θ → χ ) ) ) → ( ( ⊥ → φ ) → ( ( ( φ → ψ ) → χ ) → ( ψ → ( θ → χ ) ) ) ) ) → ( ( ( ( ( φ → ψ ) → χ ) → ( ψ → ( θ → χ ) ) ) → ( ( ⊥ → φ ) → ( φ → ψ ) ) ) → ( ( ⊥ → φ ) → ( ( χ → φ ) → ( ( ⊥ → φ ) → ( φ → ψ ) ) ) ) ) )",
        ref="merco2",
        note="merco2",
    )

    # Step 110: ax-mp(102, 109)
    s110 = lb.mp(
        "s110",
        s102,
        s109,
        "MP s102, s109",
    )

    # Step 117: merco2 with complex substitution
    s117 = lb.ref(
        "s117",
        "( ( ( ( ( ( φ → ψ ) → χ ) → ( ψ → ( θ → χ ) ) ) → ( ( ⊥ → φ ) → ( φ → ψ ) ) ) → ( ( ⊥ → φ ) → ( ( χ → φ ) → ( ( ⊥ → φ ) → ( φ → ψ ) ) ) ) ) → ( ( ( ( χ → φ ) → ( ( ⊥ → φ ) → ( φ → ψ ) ) ) → ( ( ( φ → ψ ) → χ ) → ( ψ → ( θ → χ ) ) ) ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( ( φ → ψ ) → χ ) → ( ψ → ( θ → χ ) ) ) ) ) ) )",
        ref="merco2",
        note="merco2",
    )

    # Step 118: ax-mp(110, 117)
    s118 = lb.mp(
        "s118",
        s110,
        s117,
        "MP s110, s117",
    )

    # Step 119: ax-mp(57, 118)
    s119 = lb.mp(
        "s119",
        s57,
        s118,
        "MP s57, s118",
    )

    # Step 120: ax-mp(38, 119)
    s120 = lb.mp(
        "s120",
        s38,
        s119,
        "MP s38, s119",
    )

    # Step 121: ax-mp(33, 120)
    res = lb.mp(
        "s121",
        s33,
        s120,
        "MP s33, s120",
    )

    return lb.build(res)


def prove_mercolem2(sys: System) -> Proof:
    """mercolem2: ( ( ( ph -> ps ) -> ph ) -> ( ch -> ( th -> ph ) ) ).

    Used to rederive the Tarski-Bernays-Wajsberg axioms from merco2.
    (Contributed by Anthony Hart, 17-Sep-2011.)
    """
    lb = ProofBuilder(sys, "mercolem2")

    # ( ( ph -> ps ) -> ( ( ⊥ -> ch ) -> ( ph -> ps ) ) )  [ax-1]
    s1 = lb.ref(
        "s1",
        "( ( ph -> ps ) -> ( ( ⊥ -> ch ) -> ( ph -> ps ) ) )",
        ref="ax-1",
        note="ax-1",
    )

    # merco2 with phi=ph, psi=ps, chi=ch, th=(ph->ps), ta=ch, et=th
    s2 = lb.ref(
        "s2",
        "( ( ( ph -> ps ) -> ( ( ⊥ -> ch ) -> ( ph -> ps ) ) ) -> ( ( ( ph -> ps ) -> ph ) -> ( ch -> ( th -> ph ) ) ) )",
        ref="merco2",
        note="merco2",
    )

    res = lb.mp("res", s1, s2, "MP s1, s2")
    return lb.build(res)


def prove_mercolem5(sys: System) -> Proof:
    """mercolem5: ( th -> ( ( th -> ph ) -> ( ta -> ( ch -> ph ) ) ) ).

    Used to rederive the Tarski-Bernays-Wajsberg axioms from merco2.
    (Contributed by Anthony Hart, 14-Aug-2011.)
    """
    lb = ProofBuilder(sys, "mercolem5")

    # Step 1: merco2 with phi=ph, psi=ph, chi=ph, th=ph, ta=ph, et=ph
    s1 = lb.ref(
        "s1",
        "( ( ( ph -> ph ) -> ( ( ⊥ -> ph ) -> ph ) ) -> ( ( ph -> ph ) -> ( ph -> ( ph -> ph ) ) ) )",
        ref="merco2",
        note="merco2",
    )

    # Step 3: merco2 with phi=ph, psi=ph, chi=ph, th=th, ta=ta, et=ch
    s3 = lb.ref(
        "s3",
        "( ( ( ph -> ph ) -> ( ( ⊥ -> ph ) -> th ) ) -> ( ( th -> ph ) -> ( ta -> ( ch -> ph ) ) ) )",
        ref="merco2",
        note="merco2",
    )

    # Step 4: mercolem1 with phi=(ph->ph), psi=((⊥->ph)->th),
    #         chi=((th->ph)->(ta->(ch->ph))), th=th
    s4 = lb.ref(
        "s4",
        "( ( ( ( ph -> ph ) -> ( ( ⊥ -> ph ) -> th ) ) -> ( ( th -> ph ) -> ( ta -> ( ch -> ph ) ) ) ) -> ( ( ( ⊥ -> ph ) -> th ) -> ( th -> ( ( th -> ph ) -> ( ta -> ( ch -> ph ) ) ) ) ) )",
        ref="mercolem1",
        note="mercolem1",
    )

    # Step 5: ax-mp(3, 4)
    s5 = lb.mp(
        "s5",
        s3,
        s4,
        "MP s3, s4",
    )

    # Step 6: mercolem2 with phi=th, psi=((th->ph)->(ta->(ch->ph))),
    #         chi=(⊥->ph), th=(⊥->ph)
    s6 = lb.ref(
        "s6",
        "( ( ( th -> ( ( th -> ph ) -> ( ta -> ( ch -> ph ) ) ) ) -> th ) -> ( ( ⊥ -> ph ) -> ( ( ⊥ -> ph ) -> th ) ) )",
        ref="mercolem2",
        note="mercolem2",
    )

    # Step 7: merco2 with phi=th, psi=((th->ph)->(ta->(ch->ph))), chi=ph,
    #         th=((⊥->ph)->th), ta=S, et=S
    #   where S = ((ph->ph)->((⊥->ph)->ph)) -> ((ph->ph)->(ph->(ph->ph)))
    s7 = lb.ref(
        "s7",
        "( ( ( ( th -> ( ( th -> ph ) -> ( ta -> ( ch -> ph ) ) ) ) -> th ) -> ( ( ⊥ -> ph ) -> ( ( ⊥ -> ph ) -> th ) ) ) -> ( ( ( ( ⊥ -> ph ) -> th ) -> ( th -> ( ( th -> ph ) -> ( ta -> ( ch -> ph ) ) ) ) ) -> ( ( ( ( ph -> ph ) -> ( ( ⊥ -> ph ) -> ph ) ) -> ( ( ph -> ph ) -> ( ph -> ( ph -> ph ) ) ) ) -> ( ( ( ( ph -> ph ) -> ( ( ⊥ -> ph ) -> ph ) ) -> ( ( ph -> ph ) -> ( ph -> ( ph -> ph ) ) ) ) -> ( th -> ( ( th -> ph ) -> ( ta -> ( ch -> ph ) ) ) ) ) ) ) )",
        ref="merco2",
        note="merco2",
    )

    # Step 8: ax-mp(6, 7)
    s8 = lb.mp(
        "s8",
        s6,
        s7,
        "MP s6, s7",
    )

    # Step 9: ax-mp(5, 8)
    s9 = lb.mp(
        "s9",
        s5,
        s8,
        "MP s5, s8",
    )

    # Step 10: ax-mp(1, 9)
    s10 = lb.mp(
        "s10",
        s1,
        s9,
        "MP s1, s9",
    )

    # Step 11: ax-mp(1, 10)
    res = lb.mp(
        "s11",
        s1,
        s10,
        "MP s1, s10",
    )

    return lb.build(res)


def prove_mercolem3(sys: System) -> Proof:
    """mercolem3: ( ψ → χ ) → ( ψ → ( φ → χ ) ).

    Used to rederive the Tarski-Bernays-Wajsberg axioms from merco2.
    (Contributed by Anthony Hart, 16-Aug-2011.)
    """
    lb = ProofBuilder(sys, "mercolem3")

    # merco2 with all-φ substitution
    s1 = lb.ref(
        "s1",
        "( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) )",
        ref="merco2",
        note="merco2",
    )

    # Same merco2 with all-φ substitution
    s2 = lb.ref(
        "s2",
        "( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) )",
        ref="merco2",
        note="merco2",
    )

    # merco2 with φ=χ, ψ=φ, χ=φ, θ=ψ, τ=ψ, η=φ
    s3 = lb.ref(
        "s3",
        "( ( ( χ → φ ) → ( ( ⊥ → φ ) → ψ ) ) → ( ( ψ → χ ) → ( ψ → ( φ → χ ) ) ) )",
        ref="merco2",
        note="merco2",
    )

    # mercolem2 with φ=ψ, ψ=(φ→χ), χ=(⊥→φ), θ=(⊥→φ)
    s4 = lb.ref(
        "s4",
        "( ( ( ψ → ( φ → χ ) ) → ψ ) → ( ( ⊥ → φ ) → ( ( ⊥ → φ ) → ψ ) ) )",
        ref="mercolem2",
        note="mercolem2",
    )

    # merco2 with φ=(ψ→(φ→χ)), ψ=ψ, χ=φ, θ=((⊥→φ)→ψ), τ=(⊥→φ), η=(ψ→χ)
    s5 = lb.ref(
        "s5",
        "( ( ( ( ψ → ( φ → χ ) ) → ψ ) → ( ( ⊥ → φ ) → ( ( ⊥ → φ ) → ψ ) ) ) → ( ( ( ( ⊥ → φ ) → ψ ) → ( ψ → ( φ → χ ) ) ) → ( ( ⊥ → φ ) → ( ( ψ → χ ) → ( ψ → ( φ → χ ) ) ) ) ) )",
        ref="merco2",
        note="merco2",
    )

    s6 = lb.mp("s6", s4, s5, "MP s4, s5")

    # merco2 with φ=((⊥→φ)→ψ), ψ=(ψ→(φ→χ)), χ=φ, θ=((ψ→χ)→(ψ→(φ→χ))), τ=(⊥→φ), η=(χ→φ)
    s7 = lb.ref(
        "s7",
        "( ( ( ( ( ⊥ → φ ) → ψ ) → ( ψ → ( φ → χ ) ) ) → ( ( ⊥ → φ ) → ( ( ψ → χ ) → ( ψ → ( φ → χ ) ) ) ) ) → ( ( ( ( ψ → χ ) → ( ψ → ( φ → χ ) ) ) → ( ( ⊥ → φ ) → ψ ) ) → ( ( ⊥ → φ ) → ( ( χ → φ ) → ( ( ⊥ → φ ) → ψ ) ) ) ) )",
        ref="merco2",
        note="merco2",
    )

    s8 = lb.mp("s8", s6, s7, "MP s6, s7")

    # merco2 with φ=((ψ→χ)→(ψ→(φ→χ))), ψ=((⊥→φ)→ψ), χ=φ, θ=((χ→φ)→((⊥→φ)→ψ)), τ=X, η=X
    s9 = lb.ref(
        "s9",
        "( ( ( ( ( ψ → χ ) → ( ψ → ( φ → χ ) ) ) → ( ( ⊥ → φ ) → ψ ) ) → ( ( ⊥ → φ ) → ( ( χ → φ ) → ( ( ⊥ → φ ) → ψ ) ) ) ) → ( ( ( ( χ → φ ) → ( ( ⊥ → φ ) → ψ ) ) → ( ( ψ → χ ) → ( ψ → ( φ → χ ) ) ) ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( ψ → χ ) → ( ψ → ( φ → χ ) ) ) ) ) ) )",
        ref="merco2",
        note="merco2",
    )

    s10 = lb.mp("s10", s8, s9, "MP s8, s9")

    s11 = lb.mp("s11", s3, s10, "MP s3, s10")

    s12 = lb.mp("s12", s1, s11, "MP s1, s11")

    res = lb.mp("res", s2, s12, "MP s2, s12")

    return lb.build(res)


def prove_mercolem4(sys: System) -> Proof:
    """mercolem4: (θ → (η → φ)) → (((θ → χ) → φ) → (τ → (η → φ))).

    Used to rederive the Tarski-Bernays-Wajsberg axioms from merco2.
    (Contributed by Anthony Hart, 16-Aug-2011.)
    """
    lb = ProofBuilder(sys, "mercolem4")

    # Step 1 (37): merco2 with all-φ substitution
    s1 = lb.ref(
        "s1",
        "( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) )",
        ref="merco2",
        note="merco2",
    )

    # Step 2 (42): same as s1
    s2 = lb.ref(
        "s2",
        "( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) )",
        ref="merco2",
        note="merco2",
    )

    # Step 3 (61): merco2 with φ=(η→φ), ψ=φ, χ=φ, θ=θ, τ=((θ→χ)→φ), η=τ
    s3 = lb.ref(
        "s3",
        "( ( ( ( η → φ ) → φ ) → ( ( ⊥ → φ ) → θ ) ) → ( ( θ → ( η → φ ) ) → ( ( ( θ → χ ) → φ ) → ( τ → ( η → φ ) ) ) ) )",
        ref="merco2",
        note="merco2",
    )

    # Step 4 (100): merco2 with φ=φ, ψ=φ, χ=φ, θ=(θ→χ), τ=((θ→χ)→φ), η=τ
    s4 = lb.ref(
        "s4",
        "( ( ( φ → φ ) → ( ( ⊥ → φ ) → ( θ → χ ) ) ) → ( ( ( θ → χ ) → φ ) → ( τ → ( η → φ ) ) ) )",
        ref="merco2",
        note="merco2",
    )

    # Step 5 (105): mercolem1 with φ=(φ→φ), ψ=((⊥→φ)→(θ→χ)),
    #                χ=(((θ→χ)→φ)→(τ→(η→φ))), θ=(θ→(η→φ))
    s5 = lb.ref(
        "s5",
        "( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → ( θ → χ ) ) ) → ( ( ( θ → χ ) → φ ) → ( τ → ( η → φ ) ) ) ) → ( ( ( ⊥ → φ ) → ( θ → χ ) ) → ( ( θ → ( η → φ ) ) → ( ( ( θ → χ ) → φ ) → ( τ → ( η → φ ) ) ) ) ) )",
        ref="mercolem1",
        note="mercolem1",
    )

    # Step 6 (106): ax-mp(4, 5)
    s6 = lb.mp(
        "s6",
        s4,
        s5,
        "MP s4, s5",
    )

    # Step 7 (111): mercolem1 with φ=((⊥→φ)→(θ→χ)), ψ=(θ→χ),
    #                χ=((θ→(η→φ))→(((θ→χ)→φ)→(τ→(η→φ)))), θ=(⊥→φ)
    s7 = lb.ref(
        "s7",
        "( ( ( ( ⊥ → φ ) → ( θ → χ ) ) → ( ( θ → ( η → φ ) ) → ( ( ( θ → χ ) → φ ) → ( τ → ( η → φ ) ) ) ) ) → ( ( θ → χ ) → ( ( ⊥ → φ ) → ( ( θ → ( η → φ ) ) → ( ( ( θ → χ ) → φ ) → ( τ → ( η → φ ) ) ) ) ) ) )",
        ref="mercolem1",
        note="mercolem1",
    )

    # Step 8 (112): ax-mp(6, 7)
    s8 = lb.mp(
        "s8",
        s6,
        s7,
        "MP s6, s7",
    )

    # Step 9 (119): merco2 with φ=(θ→χ),
    #                ψ=((θ→(η→φ))→(((θ→χ)→φ)→(τ→(η→φ)))), χ=φ, θ=θ,
    #                τ=((η→φ)→φ), η=(⊥→φ)
    s9 = lb.ref(
        "s9",
        "( ( ( θ → χ ) → ( ( ⊥ → φ ) → ( ( θ → ( η → φ ) ) → ( ( ( θ → χ ) → φ ) → ( τ → ( η → φ ) ) ) ) ) ) → ( ( ( ( θ → ( η → φ ) ) → ( ( ( θ → χ ) → φ ) → ( τ → ( η → φ ) ) ) ) → θ ) → ( ( ( η → φ ) → φ ) → ( ( ⊥ → φ ) → θ ) ) ) )",
        ref="merco2",
        note="merco2",
    )

    # Step 10 (120): ax-mp(8, 9)
    s10 = lb.mp(
        "s10",
        s8,
        s9,
        "MP s8, s9",
    )

    # Step 11 (124): mercolem3 with ψ=(((θ→(η→φ))→(((θ→χ)→φ)→(τ→(η→φ))))→θ),
    #                 χ=(((η→φ)→φ)→((⊥→φ)→θ)), φ=(⊥→φ)
    s11 = lb.ref(
        "s11",
        "( ( ( ( ( θ → ( η → φ ) ) → ( ( ( θ → χ ) → φ ) → ( τ → ( η → φ ) ) ) ) → θ ) → ( ( ( η → φ ) → φ ) → ( ( ⊥ → φ ) → θ ) ) ) → ( ( ( ( θ → ( η → φ ) ) → ( ( ( θ → χ ) → φ ) → ( τ → ( η → φ ) ) ) ) → θ ) → ( ( ⊥ → φ ) → ( ( ( η → φ ) → φ ) → ( ( ⊥ → φ ) → θ ) ) ) ) )",
        ref="mercolem3",
        note="mercolem3",
    )

    # Step 12 (125): ax-mp(10, 11)
    s12 = lb.mp(
        "s12",
        s10,
        s11,
        "MP s10, s11",
    )

    # Step 13 (132): merco2 with φ=(((θ→(η→φ))→(((θ→χ)→φ)→(τ→(η→φ))))→θ),
    #                 ψ=((⊥→φ)→(((η→φ)→φ)→((⊥→φ)→θ))), χ=φ,
    #                 θ=(((η→φ)→φ)→((⊥→φ)→θ)),
    #                 τ=((θ→(η→φ))→(((θ→χ)→φ)→(τ→(η→φ)))),
    #                 η=(((φ→φ)→((⊥→φ)→φ))→((φ→φ)→(φ→(φ→φ))))
    s13 = lb.ref(
        "s13",
        "( ( ( ( ( θ → ( η → φ ) ) → ( ( ( θ → χ ) → φ ) → ( τ → ( η → φ ) ) ) ) → θ ) → ( ( ⊥ → φ ) → ( ( ( η → φ ) → φ ) → ( ( ⊥ → φ ) → θ ) ) ) ) → ( ( ( ( ( η → φ ) → φ ) → ( ( ⊥ → φ ) → θ ) ) → ( ( θ → ( η → φ ) ) → ( ( ( θ → χ ) → φ ) → ( τ → ( η → φ ) ) ) ) ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( θ → ( η → φ ) ) → ( ( ( θ → χ ) → φ ) → ( τ → ( η → φ ) ) ) ) ) ) ) )",
        ref="merco2",
        note="merco2",
    )

    # Step 14 (133): ax-mp(12, 13)
    s14 = lb.mp(
        "s14",
        s12,
        s13,
        "MP s12, s13",
    )

    # Step 15 (134): ax-mp(3, 14)
    s15 = lb.mp(
        "s15",
        s3,
        s14,
        "MP s3, s14",
    )

    # Step 16 (135): ax-mp(2, 15)
    s16 = lb.mp(
        "s16",
        s2,
        s15,
        "MP s2, s15",
    )

    # Step 17 (136): ax-mp(1, 16)
    res = lb.mp(
        "res",
        s1,
        s16,
        "MP s1, s16",
    )

    return lb.build(res)


def prove_mercolem6(sys: System) -> Proof:
    """mercolem6: (φ → (ψ → (φ → χ))) → (ψ → (φ → χ)).

    Used to rederive the Tarski-Bernays-Wajsberg axioms from merco2.
    (Contributed by Anthony Hart, 16-Aug-2011.)
    """
    lb = ProofBuilder(sys, "mercolem6")

    # Step 1: merco2 with phi=ph, psi=ph, chi=ph, th=ph, ta=ph, et=ph
    s1 = lb.ref(
        "s1",
        "( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) )",
        ref="merco2",
        note="merco2",
    )

    # Step 2: same as s1
    s2 = lb.ref(
        "s2",
        "( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) )",
        ref="merco2",
        note="merco2",
    )

    # Step 3: same as s1
    s3 = lb.ref(
        "s3",
        "( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) )",
        ref="merco2",
        note="merco2",
    )

    # Step 4: same as s1
    s4 = lb.ref(
        "s4",
        "( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) )",
        ref="merco2",
        note="merco2",
    )

    # Step 5: mercolem1 with phi=phi, psi=(phi->(psi->(phi->chi))), chi=(phi->chi), th=psi
    s5 = lb.ref(
        "s5",
        "( ( ( φ → ( φ → ( ψ → ( φ → χ ) ) ) ) → ( φ → χ ) ) → ( ( φ → ( ψ → ( φ → χ ) ) ) → ( ψ → ( φ → χ ) ) ) )",
        ref="mercolem1",
        note="mercolem1",
    )

    # Step 6: mercolem1 with phi=((phi->(phi->(psi->(phi->chi))))->(phi->chi)),
    #          psi=((phi->(psi->(phi->chi)))->(psi->(phi->chi))),
    #          chi=((phi->chi)->((((phi->phi)->((⊥->phi)->phi))->((phi->phi)->(phi->(phi->phi))))->((phi->(psi->(phi->chi)))->(psi->(phi->chi))))),
    #          th=(((phi->phi)->((⊥->phi)->phi))->((phi->phi)->(phi->(phi->phi))))
    s6 = lb.ref(
        "s6",
        "( ( ( ( φ → ( φ → ( ψ → ( φ → χ ) ) ) ) → ( φ → χ ) ) → ( ( φ → ( ψ → ( φ → χ ) ) ) → ( ψ → ( φ → χ ) ) ) ) → ( ( φ → χ ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( φ → ( ψ → ( φ → χ ) ) ) → ( ψ → ( φ → χ ) ) ) ) ) )",
        ref="mercolem1",
        note="mercolem1",
    )

    # Step 7: ax-mp(5, 6)
    s7 = lb.mp(
        "s7",
        s5,
        s6,
        "MP s5, s6",
    )

    # Step 8: mercolem5 with th=phi, ph=(psi->(phi->chi)),
    #          ta=(((phi->phi)->((⊥->phi)->phi))->((phi->phi)->(phi->(phi->phi)))),
    #          ch=(((phi->phi)->((⊥->phi)->phi))->((phi->phi)->(phi->(phi->phi))))
    s8 = lb.ref(
        "s8",
        "( φ → ( ( φ → ( ψ → ( φ → χ ) ) ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( φ → ( ψ → ( φ → χ ) ) ) → ( ψ → ( φ → χ ) ) ) ) ) )",
        ref="mercolem5",
        note="mercolem5",
    )

    # Step 9: mercolem4 with th=phi, et=(phi->(psi->(phi->chi))),
    #          ph=((((phi->phi)->((⊥->phi)->phi))->((phi->phi)->(phi->(phi->phi))))->((phi->(psi->(phi->chi)))->(psi->(phi->chi)))),
    #          ch=(phi->chi),
    #          ta=(((phi->phi)->((⊥->phi)->phi))->((phi->phi)->(phi->(phi->phi))))
    s9 = lb.ref(
        "s9",
        "( ( φ → ( ( φ → ( ψ → ( φ → χ ) ) ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( φ → ( ψ → ( φ → χ ) ) ) → ( ψ → ( φ → χ ) ) ) ) ) ) → ( ( ( φ → χ ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( φ → ( ψ → ( φ → χ ) ) ) → ( ψ → ( φ → χ ) ) ) ) ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( φ → ( ψ → ( φ → χ ) ) ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( φ → ( ψ → ( φ → χ ) ) ) → ( ψ → ( φ → χ ) ) ) ) ) ) ) )",
        ref="mercolem4",
        note="mercolem4",
    )

    # Step 10: ax-mp(8, 9)
    s10 = lb.mp(
        "s10",
        s8,
        s9,
        "MP s8, s9",
    )

    # Step 11: ax-mp(7, 10)
    s11 = lb.mp(
        "s11",
        s7,
        s10,
        "MP s7, s10",
    )

    # Step 12: ax-mp(4, 11)
    s12 = lb.mp(
        "s12",
        s4,
        s11,
        "MP s4, s11",
    )

    # Step 13: same as s1
    s13 = lb.ref(
        "s13",
        "( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) )",
        ref="merco2",
        note="merco2",
    )

    # Step 14: mercolem1 with phi=phi, psi=(((phi->phi)->((⊥->phi)->phi))->((phi->phi)->(phi->(phi->phi)))),
    #           chi=((phi->(psi->(phi->chi)))->(psi->(phi->chi))),
    #           th=(((phi->phi)->((⊥->phi)->phi))->((phi->phi)->(phi->(phi->phi))))
    s14 = lb.ref(
        "s14",
        "( ( ( φ → ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) ) → ( ( φ → ( ψ → ( φ → χ ) ) ) → ( ψ → ( φ → χ ) ) ) ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( φ → ( ψ → ( φ → χ ) ) ) → ( ψ → ( φ → χ ) ) ) ) ) )",
        ref="mercolem1",
        note="mercolem1",
    )

    # Step 15: mercolem1 with phi=((phi->(((phi->phi)->((⊥->phi)->phi))->((phi->phi)->(phi->(phi->phi)))))->((phi->(psi->(phi->chi)))->(psi->(phi->chi)))),
    #           psi=((((phi->phi)->((⊥->phi)->phi))->((phi->phi)->(phi->(phi->phi))))->((((phi->phi)->((⊥->phi)->phi))->((phi->phi)->(phi->(phi->phi))))->((phi->(psi->(phi->chi)))->(psi->(phi->chi))))),
    #           chi=(((phi->(psi->(phi->chi)))->(psi->(phi->chi)))->((((phi->phi)->((⊥->phi)->phi))->((phi->phi)->(phi->(phi->phi))))->((((phi->phi)->((⊥->phi)->phi))->((phi->phi)->(phi->(phi->phi))))->((((phi->phi)->((⊥->phi)->phi))->((phi->phi)->(phi->(phi->phi))))->((phi->(psi->(phi->chi)))->(psi->(phi->chi)))))),
    #           th=(((phi->phi)->((⊥->phi)->phi))->((phi->phi)->(phi->(phi->phi))))
    s15 = lb.ref(
        "s15",
        "( ( ( ( φ → ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) ) → ( ( φ → ( ψ → ( φ → χ ) ) ) → ( ψ → ( φ → χ ) ) ) ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( φ → ( ψ → ( φ → χ ) ) ) → ( ψ → ( φ → χ ) ) ) ) ) ) → ( ( ( φ → ( ψ → ( φ → χ ) ) ) → ( ψ → ( φ → χ ) ) ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( φ → ( ψ → ( φ → χ ) ) ) → ( ψ → ( φ → χ ) ) ) ) ) ) ) )",
        ref="mercolem1",
        note="mercolem1",
    )

    # Step 16: ax-mp(14, 15)
    s16 = lb.mp(
        "s16",
        s14,
        s15,
        "MP s14, s15",
    )

    # Step 17: mercolem5 with th=(phi->(psi->(phi->chi))),
    #           ph=((((phi->phi)->((⊥->phi)->phi))->((phi->phi)->(phi->(phi->phi))))->((phi->(psi->(phi->chi)))->(psi->(phi->chi)))),
    #           ta=(((phi->phi)->((⊥->phi)->phi))->((phi->phi)->(phi->(phi->phi)))),
    #           ch=(((phi->phi)->((⊥->phi)->phi))->((phi->phi)->(phi->(phi->phi))))
    s17 = lb.ref(
        "s17",
        "( ( φ → ( ψ → ( φ → χ ) ) ) → ( ( ( φ → ( ψ → ( φ → χ ) ) ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( φ → ( ψ → ( φ → χ ) ) ) → ( ψ → ( φ → χ ) ) ) ) ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( φ → ( ψ → ( φ → χ ) ) ) → ( ψ → ( φ → χ ) ) ) ) ) ) ) )",
        ref="mercolem5",
        note="mercolem5",
    )

    # Step 18: mercolem4 with th=(phi->(psi->(phi->chi))), et=((phi->(psi->(phi->chi)))->((((phi->phi)->((⊥->phi)->phi))->((phi->phi)->(phi->(phi->phi))))->((phi->(psi->(phi->chi)))->(psi->(phi->chi))))),
    #           ph=((((phi->phi)->((⊥->phi)->phi))->((phi->phi)->(phi->(phi->phi))))->((((phi->phi)->((⊥->phi)->phi))->((phi->phi)->(phi->(phi->phi))))->((((phi->phi)->((⊥->phi)->phi))->((phi->phi)->(phi->(phi->phi))))->((phi->(psi->(phi->chi)))->(psi->(phi->chi)))))),
    #           ch=((phi->(psi->(phi->chi)))->(psi->(phi->chi))),
    #           ta=(((phi->phi)->((⊥->phi)->phi))->((phi->phi)->(phi->(phi->phi))))
    s18 = lb.ref(
        "s18",
        "( ( ( φ → ( ψ → ( φ → χ ) ) ) → ( ( ( φ → ( ψ → ( φ → χ ) ) ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( φ → ( ψ → ( φ → χ ) ) ) → ( ψ → ( φ → χ ) ) ) ) ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( φ → ( ψ → ( φ → χ ) ) ) → ( ψ → ( φ → χ ) ) ) ) ) ) ) ) → ( ( ( ( φ → ( ψ → ( φ → χ ) ) ) → ( ψ → ( φ → χ ) ) ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( φ → ( ψ → ( φ → χ ) ) ) → ( ψ → ( φ → χ ) ) ) ) ) ) ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( ( φ → ( ψ → ( φ → χ ) ) ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( φ → ( ψ → ( φ → χ ) ) ) → ( ψ → ( φ → χ ) ) ) ) ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( φ → ( ψ → ( φ → χ ) ) ) → ( ψ → ( φ → χ ) ) ) ) ) ) ) ) ) )",
        ref="mercolem4",
        note="mercolem4",
    )

    # Step 19: ax-mp(17, 18)
    s19 = lb.mp(
        "s19",
        s17,
        s18,
        "MP s17, s18",
    )

    # Step 20: ax-mp(16, 19)
    s20 = lb.mp(
        "s20",
        s16,
        s19,
        "MP s16, s19",
    )

    # Step 21: ax-mp(13, 20)
    s21 = lb.mp(
        "s21",
        s13,
        s20,
        "MP s13, s20",
    )

    # Step 22: ax-mp(12, 21)
    s22 = lb.mp(
        "s22",
        s12,
        s21,
        "MP s12, s21",
    )

    # Step 23: ax-mp(3, 22)
    s23 = lb.mp(
        "s23",
        s3,
        s22,
        "MP s3, s22",
    )

    # Step 24: ax-mp(2, 23)
    s24 = lb.mp(
        "s24",
        s2,
        s23,
        "MP s2, s23",
    )

    # Step 25: ax-mp(1, 24)
    res = lb.mp(
        "res",
        s1,
        s24,
        "MP s1, s24",
    )

    return lb.build(res)


def prove_mercolem7(sys: System) -> Proof:
    """mercolem7: ( ( φ → ψ ) → ( ( ( φ → χ ) → ( θ → ψ ) ) → ( θ → ψ ) ) ).

    Used to rederive the Tarski-Bernays-Wajsberg axioms from merco2.
    (Contributed by Anthony Hart, 16-Aug-2011.)
    """
    lb = ProofBuilder(sys, "mercolem7")

    # Step 1: merco2 with all-φ substitution
    s1 = lb.ref(
        "s1",
        "( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) )",
        ref="merco2",
        note="merco2",
    )

    # Step 2: mercolem3 with ψ:=(φ→χ), χ:=(θ→ψ), φ:=((φ→χ)→(θ→ψ))
    s2 = lb.ref(
        "s2",
        "( ( ( φ → χ ) → ( θ → ψ ) ) → ( ( φ → χ ) → ( ( ( φ → χ ) → ( θ → ψ ) ) → ( θ → ψ ) ) ) )",
        ref="mercolem3",
        note="mercolem3",
    )

    # Step 3: mercolem6 with φ:=((φ→χ)→(θ→ψ)), ψ:=(φ→χ), χ:=(θ→ψ)
    s3 = lb.ref(
        "s3",
        "( ( ( ( φ → χ ) → ( θ → ψ ) ) → ( ( φ → χ ) → ( ( ( φ → χ ) → ( θ → ψ ) ) → ( θ → ψ ) ) ) ) → ( ( φ → χ ) → ( ( ( φ → χ ) → ( θ → ψ ) ) → ( θ → ψ ) ) ) )",
        ref="mercolem6",
        note="mercolem6",
    )

    # Step 4: ax-mp(2, 3)
    s4 = lb.mp(
        "s4",
        s2,
        s3,
        "MP s2, s3",
    )

    # Step 5: mercolem5 with th:=φ, ph:=ψ, ta:=((φ→χ)→(θ→ψ)), ch:=θ
    s5 = lb.ref(
        "s5",
        "( φ → ( ( φ → ψ ) → ( ( ( φ → χ ) → ( θ → ψ ) ) → ( θ → ψ ) ) ) )",
        ref="mercolem5",
        note="mercolem5",
    )

    # Step 6: mercolem4 with θ:=φ, η:=(φ→ψ), φ:=(((φ→χ)→(θ→ψ))→(θ→ψ)),
    #          χ:=χ, τ:=( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) )
    s6 = lb.ref(
        "s6",
        "( ( φ → ( ( φ → ψ ) → ( ( ( φ → χ ) → ( θ → ψ ) ) → ( θ → ψ ) ) ) ) → ( ( ( φ → χ ) → ( ( ( φ → χ ) → ( θ → ψ ) ) → ( θ → ψ ) ) ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( φ → ψ ) → ( ( ( φ → χ ) → ( θ → ψ ) ) → ( θ → ψ ) ) ) ) ) )",
        ref="mercolem4",
        note="mercolem4",
    )

    # Step 7: ax-mp(5, 6)
    s7 = lb.mp(
        "s7",
        s5,
        s6,
        "MP s5, s6",
    )

    # Step 8: ax-mp(4, 7)
    s8 = lb.mp(
        "s8",
        s4,
        s7,
        "MP s4, s7",
    )

    # Step 9: ax-mp(1, 8) → conclusion
    res = lb.mp(
        "s9",
        s1,
        s8,
        "MP s1, s8",
    )

    return lb.build(res)


def prove_merco1lem4(sys: System) -> Proof:
    """merco1lem4: ((φ → ψ) → χ) → (ψ → χ).

    Used to rederive the Tarski-Bernays-Wajsberg axioms from merco1.
    (Contributed by Anthony Hart, 17-Sep-2011.)
    """
    lb = ProofBuilder(sys, "merco1lem4")

    s36 = lb.ref(
        "s36",
        "( ( ( ( ψ → ⊥ ) → ( φ → ⊥ ) ) → ( ( χ → φ ) → ⊥ ) ) → ( ( χ → φ ) → ( ψ → ⊥ ) ) )",
        ref="merco1lem3",
        note="merco1lem3",
    )

    s42 = lb.ref(
        "s42",
        "( ( ( ( ( ψ → ⊥ ) → ( φ → ⊥ ) ) → ( ( χ → φ ) → ⊥ ) ) → ( ( χ → φ ) → ( ψ → ⊥ ) ) ) → ( ( ( ( χ → φ ) → ( ψ → ⊥ ) ) → ψ ) → ( φ → ψ ) ) )",
        ref="merco1",
        note="merco1",
    )

    s43 = lb.mp("s43", s36, s42, "ax-mp 36,42")

    s49 = lb.ref(
        "s49",
        "( ( ( ( ( χ → φ ) → ( ψ → ⊥ ) ) → ψ ) → ( φ → ψ ) ) → ( ( ( φ → ψ ) → χ ) → ( ψ → χ ) ) )",
        ref="merco1",
        note="merco1",
    )

    res = lb.mp("res", s43, s49, "ax-mp 43,49")

    return lb.build(res)


def prove_merco1lem10(sys: System) -> Proof:
    """merco1lem10: ( ( ( ( ( φ → ψ ) → χ ) → ( τ → χ ) ) → φ ) → ( θ → φ ).

    Used to rederive the Tarski-Bernays-Wajsberg axioms from merco1.
    (Contributed by Anthony Hart, 17-Sep-2011.)
    """
    lb = ProofBuilder(sys, "merco1lem10")

    # merco1 with φ:=χ, ψ:=φ, χ:=τ, θ:=φ, τ:=(φ→ψ)
    s1 = lb.ref(
        "s1",
        "( ( ( ( ( χ → φ ) → ( τ → ⊥ ) ) → φ ) → ( φ → ψ ) ) → ( ( ( φ → ψ ) → χ ) → ( τ → χ ) ) )",
        ref="merco1",
        note="merco1",
    )

    # merco1lem2 with φ:=(((χ→φ)→(τ→⊥))→φ), ψ:=(φ→ψ),
    #                χ:=(((φ→ψ)→χ)→(τ→χ)), τ:=(θ→⊥)
    s2 = lb.ref(
        "s2",
        "( ( ( ( ( ( χ → φ ) → ( τ → ⊥ ) ) → φ ) → ( φ → ψ ) ) → ( ( ( φ → ψ ) → χ ) → ( τ → χ ) ) ) → ( ( ( ( φ → ψ ) → ( θ → ⊥ ) ) → ( ( ( ( χ → φ ) → ( τ → ⊥ ) ) → φ ) → ⊥ ) ) → ( ( ( φ → ψ ) → χ ) → ( τ → χ ) ) ) )",
        ref="merco1lem2",
        note="merco1lem2",
    )

    # ax-mp from s1 and s2
    s3 = lb.mp("s3", s1, s2, "ax-mp 1,2")

    # merco1 with φ:=φ, ψ:=ψ, χ:=θ,
    #           θ:=((((χ→φ)→(τ→⊥))→φ)→⊥), τ:=(((φ→ψ)→χ)→(τ→χ))
    s4 = lb.ref(
        "s4",
        "( ( ( ( ( φ → ψ ) → ( θ → ⊥ ) ) → ( ( ( ( χ → φ ) → ( τ → ⊥ ) ) → φ ) → ⊥ ) ) → ( ( ( φ → ψ ) → χ ) → ( τ → χ ) ) ) → ( ( ( ( ( φ → ψ ) → χ ) → ( τ → χ ) ) → φ ) → ( θ → φ ) ) )",
        ref="merco1",
        note="merco1",
    )

    # ax-mp from s3 and s4
    res = lb.mp("res", s3, s4, "ax-mp 3,4")

    return lb.build(res)


def prove_merco1lem6(sys: System) -> Proof:
    """merco1lem6: ((φ → (φ → ψ)) → (χ → (φ → ψ))).

    Used to rederive the Tarski-Bernays-Wajsberg axioms from merco1.
    (Contributed by Anthony Hart, 17-Sep-2011.)
    """
    lb = ProofBuilder(sys, "merco1lem6")

    s1 = lb.ref(
        "s1",
        "((((((φ → ψ) → ⊥) → (χ → ⊥)) → ⊥) → ⊥) → ⊥) → ((((φ → ψ) → ⊥) → (χ → ⊥)) → ⊥)",
        ref="merco1lem5",
        note="merco1lem5",
    )

    s2 = lb.ref(
        "s2",
        "(((((((φ → ψ) → ⊥) → (χ → ⊥)) → ⊥) → ⊥) → ⊥) → ((((φ → ψ) → ⊥) → (χ → ⊥)) → ⊥)) → ((((φ → ψ) → ⊥) → (χ → ⊥)) → (((((φ → ψ) → ⊥) → (χ → ⊥)) → ⊥) → ⊥))",
        ref="merco1lem3",
        note="merco1lem3",
    )

    s3 = lb.mp("s3", s1, s2, "ax-mp 1,2")

    s4 = lb.ref(
        "s4",
        "(((((φ → ψ) → ⊥) → (χ → ⊥)) → (((((φ → ψ) → ⊥) → (χ → ⊥)) → ⊥) → ⊥)) → ((φ → ψ) → (((((φ → ψ) → ⊥) → (χ → ⊥)) → ⊥) → ⊥)))",
        ref="merco1lem5",
        note="merco1lem5",
    )

    s5 = lb.mp("s5", s3, s4, "ax-mp 3,4")

    s6 = lb.ref(
        "s6",
        "(((φ → ψ) → (((((φ → ψ) → ⊥) → (χ → ⊥)) → ⊥) → ⊥)) → (((((φ → ψ) → ⊥) → (χ → ⊥)) → ⊥) → φ))",
        ref="merco1lem3",
        note="merco1lem3",
    )

    s7 = lb.mp("s7", s5, s6, "ax-mp 5,6")

    s8 = lb.ref(
        "s8",
        "((((((φ → ψ) → ⊥) → (χ → ⊥)) → ⊥) → φ) → ((φ → (φ → ψ)) → (χ → (φ → ψ))))",
        ref="merco1",
        note="merco1",
    )

    res = lb.mp("res", s7, s8, "ax-mp 7,8")

    return lb.build(res)


def prove_merco1lem7(sys: System) -> Proof:
    """merco1lem7: φ → (((ψ → χ) → ψ) → ψ).

    Used to rederive the Tarski-Bernays-Wajsberg axioms from merco1.
    (Contributed by Anthony Hart, 17-Sep-2011.)
    """
    lb = ProofBuilder(sys, "merco1lem7")

    s1 = lb.ref(
        "s1",
        "((((ψ → ⊥) → (((ψ → χ) → ψ) → ⊥)) → χ) → (ψ → χ))",
        ref="merco1lem5",
        note="merco1lem5",
    )

    s2 = lb.ref(
        "s2",
        "(((((ψ → ⊥) → (((ψ → χ) → ψ) → ⊥)) → χ) → (ψ → χ)) → (((ψ → χ) → ψ) → (((ψ → χ) → ψ) → ψ)))",
        ref="merco1",
        note="merco1",
    )

    s3 = lb.mp("s3", s1, s2, "ax-mp 1,2")

    s4 = lb.ref(
        "s4",
        "((((ψ → χ) → ψ) → (((ψ → χ) → ψ) → ψ)) → (φ → (((ψ → χ) → ψ) → ψ)))",
        ref="merco1lem6",
        note="merco1lem6",
    )

    res = lb.mp("res", s3, s4, "ax-mp 3,4")

    return lb.build(res)


def prove_retbwax2(sys: System) -> Proof:
    """retbwax2: φ → (ψ → φ).

    Re-derive ax-1 from the merco1 axiom system.
    (Contributed by Anthony Hart, 17-Sep-2011.)
    """
    lb = ProofBuilder(sys, "retbwax2")

    s1 = lb.ref(
        "s1",
        "( ( ( ( ( φ → φ ) → φ ) → ( φ → ⊥ ) ) → φ ) → ( ⊥ → φ ) )",
        ref="merco1lem1",
        note="merco1lem1",
    )

    s2 = lb.ref(
        "s2",
        "( ( ( ( ( ( φ → φ ) → φ ) → ( φ → ⊥ ) ) → φ ) → ( ⊥ → φ ) ) → ( ( ( ⊥ → φ ) → ( φ → φ ) ) → ( φ → ( φ → φ ) ) ) )",
        ref="merco1",
        note="merco1",
    )

    s3 = lb.mp("s3", s1, s2, "ax-mp 1,2")

    s4 = lb.ref(
        "s4",
        "( ( ( ( ( φ → ( φ → φ ) ) → ( φ → ⊥ ) ) → ( φ → ⊥ ) ) → ⊥ ) → ( ( ⊥ → φ ) → ( φ → φ ) ) )",
        ref="merco1",
        note="merco1",
    )

    s5 = lb.ref(
        "s5",
        "( ( ( ( ( ( φ → ( φ → φ ) ) → ( φ → ⊥ ) ) → ( φ → ⊥ ) ) → ⊥ ) → ( ( ⊥ → φ ) → ( φ → φ ) ) ) → ( ( ( ( ⊥ → φ ) → ( φ → φ ) ) → ( φ → ( φ → φ ) ) ) → ( φ → ( φ → ( φ → φ ) ) ) ) )",
        ref="merco1",
        note="merco1",
    )

    s6 = lb.mp("s6", s4, s5, "ax-mp 4,5")

    s7 = lb.mp("s7", s3, s6, "ax-mp 3,6")

    s8 = lb.ref(
        "s8",
        "( ( ( ( ( ψ → φ ) → φ ) → ( φ → ⊥ ) ) → φ ) → ( ⊥ → φ ) )",
        ref="merco1lem1",
        note="merco1lem1",
    )

    s9 = lb.ref(
        "s9",
        "( ( ( ( ( ( ψ → φ ) → φ ) → ( φ → ⊥ ) ) → φ ) → ( ⊥ → φ ) ) → ( ( ( ⊥ → φ ) → ( ψ → φ ) ) → ( φ → ( ψ → φ ) ) ) )",
        ref="merco1",
        note="merco1",
    )

    s10 = lb.mp("s10", s8, s9, "ax-mp 8,9")

    s11 = lb.ref(
        "s11",
        "( ( ( ( ( φ → ( ψ → φ ) ) → ( ψ → ⊥ ) ) → ( ( φ → ( φ → ( φ → φ ) ) ) → ⊥ ) ) → ⊥ ) → ( ( ⊥ → φ ) → ( ψ → φ ) ) )",
        ref="merco1",
        note="merco1",
    )

    s12 = lb.ref(
        "s12",
        "( ( ( ( ( ( φ → ( ψ → φ ) ) → ( ψ → ⊥ ) ) → ( ( φ → ( φ → ( φ → φ ) ) ) → ⊥ ) ) → ⊥ ) → ( ( ⊥ → φ ) → ( ψ → φ ) ) ) → ( ( ( ( ⊥ → φ ) → ( ψ → φ ) ) → ( φ → ( ψ → φ ) ) ) → ( ( φ → ( φ → ( φ → φ ) ) ) → ( φ → ( ψ → φ ) ) ) ) )",
        ref="merco1",
        note="merco1",
    )

    s13 = lb.mp("s13", s11, s12, "ax-mp 11,12")

    s14 = lb.mp("s14", s10, s13, "ax-mp 10,13")

    res = lb.mp("res", s7, s14, "ax-mp 7,14")

    return lb.build(res)


def prove_retbwax3(sys: System) -> Proof:
    """retbwax3: ((φ → ψ) → φ) → φ.

    Pierce's law derived from the merco1 axiom system.
    (Contributed by Anthony Hart, 17-Sep-2011.)
    """
    lb = ProofBuilder(sys, "retbwax3")

    s1 = lb.ref(
        "s1",
        "( φ → ( φ → φ ) )",
        ref="retbwax2",
        note="retbwax2",
    )

    s2 = lb.ref(
        "s2",
        "( ( φ → ( φ → φ ) ) → ( ( ( φ → ψ ) → φ ) → φ ) )",
        ref="merco1lem7",
        note="merco1lem7",
    )

    res = lb.mp("res", s1, s2, "ax-mp 1,2")

    return lb.build(res)


def prove_simplbiim(sys: System) -> Proof:
    """simplbiim: φ → θ.

    Hyp 1: φ ↔ (ψ ∧ χ)
    Hyp 2: χ → θ
    Concl: φ → θ

    Syllogism inference from a biconditional with a conjunction.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "simplbiim")
    h1 = lb.hyp("simplbiim.1", "( φ ↔ ( ψ ∧ χ ) )")
    h2 = lb.hyp("simplbiim.2", "χ → θ")
    s1 = lb.ref("s1", "φ → χ", h1, ref="simprbi", note="simprbi")
    res = lb.ref("res", "φ → θ", s1, h2, ref="syl", note="syl")
    return lb.build(res)


def prove_simpl2im(sys: System) -> Proof:
    """simpl2im: φ → θ.

    Hyp 1: φ → (ψ ∧ χ)
    Hyp 2: χ → θ
    Concl: φ → θ

    Syllogism inference with a conjunction antecedent.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "simpl2im")
    h1 = lb.hyp("simpl2im.1", "φ → ( ψ ∧ χ )")
    h2 = lb.hyp("simpl2im.2", "χ → θ")
    s1 = lb.ref("s1", "φ → χ", h1, ref="simprd", note="simprd simpl2im.1")
    res = lb.ref("res", "φ → θ", s1, h2, ref="syl", note="syl s1, simpl2im.2")
    return lb.build(res)


def prove_oplem1(sys: System) -> Proof:
    """oplem1: φ → ψ.

    A specialized lemma for set theory (ordered pair theorem).
    Hypotheses: φ → (¬ ψ → χ), φ → (¬ θ → τ), ψ ↔ θ, χ → (θ ↔ τ).
    (Contributed by NM, 18-Oct-1995.)
    (Proof shortened by Wolf Lammen, 8-Dec-2012.)
    """
    lb = ProofBuilder(sys, "oplem1")
    h3 = lb.hyp("oplem1.3", "( ψ ↔ θ )")
    h1 = lb.hyp("oplem1.1", "( φ → ( ψ ∨ χ ) )")
    h2 = lb.hyp("oplem1.2", "( φ → ( θ ∨ τ ) )")
    h4 = lb.hyp("oplem1.4", "( χ → ( θ ↔ τ ) )")

    s2 = lb.ref("s2", "( ¬ ψ ↔ ¬ θ )", h3, ref="notbii", note="notbii oplem1.3")
    s4 = lb.ref("s4", "( φ → ( ¬ ψ → χ ) )", h1, ref="ord", note="ord oplem1.1")
    s5 = lb.ref("s5", "( φ → ( ¬ θ → χ ) )", s2, s4, ref="biimtrrid", note="biimtrrid s2, s4")
    s7 = lb.ref("s7", "( φ → ( ¬ θ → τ ) )", h2, ref="ord", note="ord oplem1.2")
    s8 = lb.ref("s8", "( φ → ( ¬ θ → ( χ ∧ τ ) ) )", s5, s7, ref="jcad", note="jcad s5, s7")
    s10 = lb.ref("s10", "( ( χ ∧ τ ) → θ )", h4, ref="biimpar", note="biimpar oplem1.4")
    s11 = lb.ref("s11", "( φ → ( ¬ θ → θ ) )", s8, s10, ref="syl6", note="syl6 s8, s10")
    s12 = lb.ref("s12", "( φ → θ )", s11, ref="pm2.18d", note="pm2.18d s11")
    res = lb.ref("res", "( φ → ψ )", s12, h3, ref="sylibr", note="sylibr s12, oplem1.3")
    return lb.build(res)


def prove_1fpid3(sys: System) -> Proof:
    """1fpid3: if- φ ψ χ → χ.

    Hyp: ( φ ∧ ψ ) → χ

    The conditional implies its third argument.
    (Contributed by BJ, 25-Aug-2023.)
    """
    lb = ProofBuilder(sys, "1fpid3")
    h1 = lb.hyp("1fpid3.1", "( φ ∧ ψ ) → χ")
    s1 = lb.ref("s1", "( ( ¬ φ ∧ χ ) → χ )", ref="simpr", note="simpr")
    s2 = lb.ref("s2", "( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) ) → χ", h1, s1, ref="jaoi", note="jaoi")
    s3 = lb.ref("s3", "( if- φ ψ χ ↔ ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) ) )", ref="df-ifp", note="df-ifp")
    res = lb.ref("res", "if- φ ψ χ → χ", s3, s2, ref="sylbi", note="sylbi")
    return lb.build(res)


def prove_ifpimpda(sys: System) -> Proof:
    """ifpimpda: φ → if-(ψ, χ, θ).

    Hyp 1: ( φ ∧ ψ ) → χ
    Hyp 2: ( φ ∧ ¬ ψ ) → θ
    Concl: φ → if-(ψ, χ, θ)

    Deduction form of the implication variant of the conditional operator.
    (Contributed by BJ, 13-Oct-2023.)
    """
    lb = ProofBuilder(sys, "ifpimpda")
    h1 = lb.hyp("ifpimpda.1", "( φ ∧ ψ ) → χ")
    h2 = lb.hyp("ifpimpda.2", "( φ ∧ ¬ ψ ) → θ")

    # ex on h1: φ → (ψ → χ)
    s1 = lb.ref("s1", "φ → ( ψ → χ )", h1, ref="ex", note="ex")

    # ex on h2: φ → (¬ψ → θ)
    s2 = lb.ref("s2", "φ → ( ¬ ψ → θ )", h2, ref="ex", note="ex")

    # dfifp2: if-(ψ, χ, θ) ↔ ((ψ → χ) ∧ (¬ψ → θ))
    s3 = lb.ref(
        "s3",
        "( if- ψ χ θ ↔ ( ( ψ → χ ) ∧ ( ¬ ψ → θ ) ) )",
        ref="dfifp2",
        note="dfifp2",
    )

    # sylanbrc: combine the three into the conclusion
    res = lb.ref(
        "res",
        "φ → if- ψ χ θ",
        s1,
        s2,
        s3,
        ref="sylanbrc",
        note="sylanbrc",
    )

    return lb.build(res)


def prove_impsingle_step18(sys: System) -> Proof:
    """impsingle-step18: (( (φ→ψ) → (χ→ψ) ) → ( ( (ψ→θ) → φ ) → τ )) → (η → ( ( (ψ→θ) → φ ) → τ )).

    Step 18 in the impsingle-step series.
    Derived from impsingle, impsingle-step8, and impsingle-step15 with ax-mp.
    """
    lb = ProofBuilder(sys, "impsingle-step18")

    # Let P = (φ→ψ)→(χ→ψ), Q = ((ψ→θ)→φ)→τ, A = (ψ→θ)→φ

    # (1) impsingle(ψ, θ, φ, χ): A → P
    s1 = lb.ref(
        "s1",
        "((ψ → θ) → φ) → ((φ → ψ) → (χ → ψ))",
        ref="impsingle",
    )

    # (2) impsingle((χ→ψ), ρ, Q, (φ→ψ)):
    #     (((χ→ψ)→ρ)→Q) → ((Q→(χ→ψ))→P)
    s2 = lb.ref(
        "s2",
        "((((χ → ψ) → ρ) → (((ψ → θ) → φ) → τ)) → (((((ψ → θ) → φ) → τ) → (χ → ψ)) → ((φ → ψ) → (χ → ψ))))",
        ref="impsingle",
    )

    # (3) impsingle-step8((χ→ψ)→ρ, Q, ((Q→(χ→ψ))→P)):
    #     s2 → (Q → ((Q→(χ→ψ))→P))
    s3 = lb.ref(
        "s3",
        "(((((χ → ψ) → ρ) → (((ψ → θ) → φ) → τ)) → (((((ψ → θ) → φ) → τ) → (χ → ψ)) → ((φ → ψ) → (χ → ψ)))) → ((((ψ → θ) → φ) → τ) → (((((ψ → θ) → φ) → τ) → (χ → ψ)) → ((φ → ψ) → (χ → ψ)))))",
        ref="impsingle-step8",
    )

    # (4) ax-mp(s2, s3): Q → ((Q→(χ→ψ))→P)
    s4 = lb.mp("s4", s2, s3)

    # (5) impsingle-step15(A, τ, (Q→(χ→ψ)), P):
    #     (Q → ((Q→(χ→ψ))→P)) → ((A→P) → ((Q→(χ→ψ))→P))
    s5 = lb.ref(
        "s5",
        "(((((ψ → θ) → φ) → τ) → (((((ψ → θ) → φ) → τ) → (χ → ψ)) → ((φ → ψ) → (χ → ψ)))) → ((((ψ → θ) → φ) → ((φ → ψ) → (χ → ψ))) → (((((ψ → θ) → φ) → τ) → (χ → ψ)) → ((φ → ψ) → (χ → ψ)))))",
        ref="impsingle-step15",
    )

    # (6) ax-mp(s4, s5): (A→P) → ((Q→(χ→ψ))→P)
    s6 = lb.mp("s6", s4, s5)

    # (7) ax-mp(s1, s6): (Q→(χ→ψ))→P
    s7 = lb.mp("s7", s1, s6)

    # (8) impsingle(Q, (χ→ψ), P, η):
    #     ((Q→(χ→ψ))→P) → ((P→Q)→(η→Q))  =  ((Q→(χ→ψ))→P) → target
    s8 = lb.ref(
        "s8",
        "((((((ψ → θ) → φ) → τ) → (χ → ψ)) → ((φ → ψ) → (χ → ψ))) → ((((φ → ψ) → (χ → ψ)) → (((ψ → θ) → φ) → τ)) → (η → (((ψ → θ) → φ) → τ))))",
        ref="impsingle",
    )

    # (9) ax-mp(s7, s8): target
    res = lb.mp("res", s7, s8)

    return lb.build(res)


def prove_impsingle_step19(sys: System) -> Proof:
    """impsingle-step19: ((((φ → ψ) → χ) → (θ → ψ)) → (((ψ → χ) → θ) → (φ → ψ))).

    Step 19 in the impsingle-step series.
    Derived from impsingle-step18 with ax-mp.
    """
    lb = ProofBuilder(sys, "impsingle-step19")

    # (1) impsingle-step18(φ, ψ, χ, θ, τ, η):
    #     (((φ→ψ)→(χ→ψ)) → (((ψ→θ)→φ)→τ)) → (η → (((ψ→θ)→φ)→τ))
    s43 = lb.ref(
        "s43",
        "((((φ → ψ) → (χ → ψ)) → (((ψ → θ) → φ) → τ)) → (η → (((ψ → θ) → φ) → τ)))",
        ref="impsingle-step18",
    )

    # (2) impsingle-step18(θ, ψ, φ, χ, (φ→ψ), ((φ→ψ)→χ)→(θ→ψ)):
    #     ((((θ→ψ)→(φ→ψ))→(((ψ→χ)→θ)→(φ→ψ))) → ((((φ→ψ)→χ)→(θ→ψ))→(((ψ→χ)→θ)→(φ→ψ))))
    #     Note: the consequent is exactly the target.
    s60 = lb.ref(
        "s60",
        "((((θ → ψ) → (φ → ψ)) → (((ψ → χ) → θ) → (φ → ψ))) → ((((φ → ψ) → χ) → (θ → ψ)) → (((ψ → χ) → θ) → (φ → ψ))))",
        ref="impsingle-step18",
    )

    # (3) impsingle-step18 with η = s43:
    #     (s60_antecedent → target) → (s43 → target)
    s67 = lb.ref(
        "s67",
        "(((((θ → ψ) → (φ → ψ)) → (((ψ → χ) → θ) → (φ → ψ))) → ((((φ → ψ) → χ) → (θ → ψ)) → (((ψ → χ) → θ) → (φ → ψ)))) → (((((φ → ψ) → (χ → ψ)) → (((ψ → θ) → φ) → τ)) → (η → (((ψ → θ) → φ) → τ))) → ((((φ → ψ) → χ) → (θ → ψ)) → (((ψ → χ) → θ) → (φ → ψ)))))",
        ref="impsingle-step18",
    )

    # (4) ax-mp(s60, s67): s43 → target
    s68 = lb.mp("s68", s60, s67)

    # (5) ax-mp(s43, s68): target
    res = lb.mp("res", s43, s68)

    return lb.build(res)


def prove_impsingle_step20(sys: System) -> Proof:
    """impsingle-step20: ((((φ → ψ) → ψ) → (χ → ψ)) → (((ψ → θ) → φ) → (χ → ψ))).

    Step 20 in the impsingle-step series.
    Derived from impsingle-step19, impsingle, and impsingle-step8 with ax-mp.
    """
    lb = ProofBuilder(sys, "impsingle-step20")

    # (1) impsingle-step19(χ, ψ, θ, φ, ψ):
    #     ((((χ → ψ) → θ) → (φ → ψ)) → (((ψ → θ) → φ) → (χ → ψ)))
    s1 = lb.ref(
        "s1",
        "((((χ → ψ) → θ) → (φ → ψ)) → (((ψ → θ) → φ) → (χ → ψ)))",
        ref="impsingle-step19",
    )

    # (2) impsingle(τ, ζ, σ, ρ):
    #     (((τ → ζ) → σ) → ((σ → τ) → (ρ → τ)))
    s2 = lb.ref(
        "s2",
        "(((τ → ζ) → σ) → ((σ → τ) → (ρ → τ)))",
        ref="impsingle",
    )

    # (3) impsingle(((ψ → θ) → φ) → (χ → ψ), η, ((χ → ψ) → θ) → (φ → ψ), ((φ → ψ) → ψ) → (χ → ψ)):
    s3 = lb.ref(
        "s3",
        "((((((ψ → θ) → φ) → (χ → ψ)) → η) → (((χ → ψ) → θ) → (φ → ψ))) → (((((χ → ψ) → θ) → (φ → ψ)) → (((ψ → θ) → φ) → (χ → ψ))) → ((((φ → ψ) → ψ) → (χ → ψ)) → (((ψ → θ) → φ) → (χ → ψ)))))",
        ref="impsingle",
    )

    # (4) impsingle((χ → ψ) → τ, (φ → ψ) → ψ, ((φ → ψ) → ψ) → (χ → ψ), ((ψ → θ) → φ) → (χ → ψ)):
    s4 = lb.ref(
        "s4",
        "((((χ → ψ) → τ) → ((φ → ψ) → ψ)) → ((((φ → ψ) → ψ) → (χ → ψ)) → (((ψ → θ) → φ) → (χ → ψ))))",
        ref="impsingle",
    )

    # (5) impsingle-step8 with antecedent = s4 formula:
    s5 = lb.ref(
        "s5",
        "(((((χ → ψ) → τ) → ((φ → ψ) → ψ)) → ((((φ → ψ) → ψ) → (χ → ψ)) → (((ψ → θ) → φ) → (χ → ψ)))) → (((φ → ψ) → ψ) → ((((φ → ψ) → ψ) → (χ → ψ)) → (((ψ → θ) → φ) → (χ → ψ)))))",
        ref="impsingle-step8",
    )

    # (6) ax-mp(s4, s5):
    s6 = lb.mp("s6", s4, s5)

    # (7) impsingle((φ → ψ) → ψ, ((φ → ψ) → ψ) → (χ → ψ) → (((ψ → θ) → φ) → (χ → ψ)), (((φ → ψ) → ψ) → (χ → ψ)) → (((ψ → θ) → φ) → (χ → ψ))) → (φ → ψ), ((χ → ψ) → θ) → (φ → ψ)):
    s7 = lb.ref(
        "s7",
        "((((φ → ψ) → ψ) → ((((φ → ψ) → ψ) → (χ → ψ)) → (((ψ → θ) → φ) → (χ → ψ)))) → ((((((φ → ψ) → ψ) → (χ → ψ)) → (((ψ → θ) → φ) → (χ → ψ))) → (φ → ψ)) → (((χ → ψ) → θ) → (φ → ψ))))",
        ref="impsingle",
    )

    # (8) ax-mp(s6, s7):
    s8 = lb.mp("s8", s6, s7)

    # (9) impsingle(((((φ → ψ) → ψ) → (χ → ψ)) → (((ψ → θ) → φ) → (χ → ψ))) → (φ → ψ), ((χ → ψ) → θ) → (φ → ψ), ((χ → ψ) → θ) → (φ → ψ)) → ((((φ → ψ) → ψ) → (χ → ψ)) → (((ψ → θ) → φ) → (χ → ψ))), ((χ → ψ) → θ) → (φ → ψ)) → (((ψ → θ) → φ) → (χ → ψ))) → ((((φ → ψ) → ψ) → (χ → ψ)) → (((ψ → θ) → φ) → (χ → ψ)))):
    s9 = lb.ref(
        "s9",
        "(((((((φ → ψ) → ψ) → (χ → ψ)) → (((ψ → θ) → φ) → (χ → ψ))) → (φ → ψ)) → (((χ → ψ) → θ) → (φ → ψ))) → (((((χ → ψ) → θ) → (φ → ψ)) → ((((φ → ψ) → ψ) → (χ → ψ)) → (((ψ → θ) → φ) → (χ → ψ)))) → (((((χ → ψ) → θ) → (φ → ψ)) → (((ψ → θ) → φ) → (χ → ψ))) → ((((φ → ψ) → ψ) → (χ → ψ)) → (((ψ → θ) → φ) → (χ → ψ))))))",
        ref="impsingle",
    )

    # (10) ax-mp(s8, s9):
    s10 = lb.mp("s10", s8, s9)

    # (11) impsingle with appropriate substitutions:
    s11 = lb.ref(
        "s11",
        "((((((χ → ψ) → θ) → (φ → ψ)) → ((((φ → ψ) → ψ) → (χ → ψ)) → (((ψ → θ) → φ) → (χ → ψ)))) → (((((χ → ψ) → θ) → (φ → ψ)) → (((ψ → θ) → φ) → (χ → ψ))) → ((((φ → ψ) → ψ) → (χ → ψ)) → (((ψ → θ) → φ) → (χ → ψ))))) → (((((((χ → ψ) → θ) → (φ → ψ)) → (((ψ → θ) → φ) → (χ → ψ))) → ((((φ → ψ) → ψ) → (χ → ψ)) → (((ψ → θ) → φ) → (χ → ψ)))) → (((χ → ψ) → θ) → (φ → ψ))) → (((((ψ → θ) → φ) → (χ → ψ)) → η) → (((χ → ψ) → θ) → (φ → ψ)))))",
        ref="impsingle",
    )

    # (12) ax-mp(s10, s11):
    s12 = lb.mp("s12", s10, s11)

    # (13) impsingle with appropriate substitutions:
    s13 = lb.ref(
        "s13",
        "((((((((χ → ψ) → θ) → (φ → ψ)) → (((ψ → θ) → φ) → (χ → ψ))) → ((((φ → ψ) → ψ) → (χ → ψ)) → (((ψ → θ) → φ) → (χ → ψ)))) → (((χ → ψ) → θ) → (φ → ψ))) → (((((ψ → θ) → φ) → (χ → ψ)) → η) → (((χ → ψ) → θ) → (φ → ψ)))) → (((((((ψ → θ) → φ) → (χ → ψ)) → η) → (((χ → ψ) → θ) → (φ → ψ))) → (((((χ → ψ) → θ) → (φ → ψ)) → (((ψ → θ) → φ) → (χ → ψ))) → ((((φ → ψ) → ψ) → (χ → ψ)) → (((ψ → θ) → φ) → (χ → ψ))))) → ((((τ → ζ) → σ) → ((σ → τ) → (ρ → τ))) → (((((χ → ψ) → θ) → (φ → ψ)) → (((ψ → θ) → φ) → (χ → ψ))) → ((((φ → ψ) → ψ) → (χ → ψ)) → (((ψ → θ) → φ) → (χ → ψ)))))))",
        ref="impsingle",
    )

    # (14) ax-mp(s12, s13):
    s14 = lb.mp("s14", s12, s13)

    # (15) ax-mp(s3, s14):
    s15 = lb.mp("s15", s3, s14)

    # (16) ax-mp(s2, s15):
    s16 = lb.mp("s16", s2, s15)

    # (qed) ax-mp(s1, s16):
    res = lb.mp("res", s1, s16)

    return lb.build(res)


def prove_impsingle_step21(sys: System) -> Proof:
    """impsingle-step21: ((((φ → ψ) → χ) → χ) → ((χ → ψ) → (φ → ψ))).

    Step 21 in the impsingle-step series.
    Derived from impsingle-step15 and impsingle-step20 with ax-mp.
    """
    lb = ProofBuilder(sys, "impsingle-step21")

    # (1) impsingle-step15(χ, (φ → ψ), φ, ψ):
    #     (((χ → (φ → ψ)) → (φ → ψ)) → ((χ → ψ) → (φ → ψ)))
    s1 = lb.ref(
        "s1",
        "(((χ → (φ → ψ)) → (φ → ψ)) → ((χ → ψ) → (φ → ψ)))",
        ref="impsingle-step15",
    )

    # (2) impsingle-step20(χ, (φ → ψ), (χ → ψ), χ):
    #     ((((χ → (φ → ψ)) → (φ → ψ)) → ((χ → ψ) → (φ → ψ))) →
    #      ((((φ → ψ) → χ) → χ) → ((χ → ψ) → (φ → ψ))))
    s2 = lb.ref(
        "s2",
        "((((χ → (φ → ψ)) → (φ → ψ)) → ((χ → ψ) → (φ → ψ))) → ((((φ → ψ) → χ) → χ) → ((χ → ψ) → (φ → ψ))))",
        ref="impsingle-step20",
    )

    # (qed) ax-mp(s1, s2):
    res = lb.mp("res", s1, s2)

    return lb.build(res)


def prove_impsingle_step25(sys: System) -> Proof:
    """impsingle-step25: ( φ → ψ ) → ( ( ( φ → χ ) → ψ ) → ψ ).

    Step 25 in the impsingle-step series.
    Derived from impsingle-step22, impsingle-step20, impsingle-step8,
    and impsingle-step15 with ax-mp.
    """
    lb = ProofBuilder(sys, "impsingle-step25")

    # (1) impsingle-step22 with ph := (((φ → χ) → ψ) → ψ)
    s1 = lb.ref(
        "s1",
        "((((φ → χ) → ψ) → ψ) → (((φ → χ) → ψ) → ψ))",
        ref="impsingle-step22",
    )

    # (2) impsingle-step20 with φ := (φ → χ), ψ := ψ, χ := ((φ → χ) → ψ), θ := θ
    s2 = lb.ref(
        "s2",
        "(((((φ → χ) → ψ) → ψ) → (((φ → χ) → ψ) → ψ)) → (((ψ → θ) → (φ → χ)) → (((φ → χ) → ψ) → ψ)))",
        ref="impsingle-step20",
    )

    # (3) ax-mp(1, 2)
    s3 = lb.mp("s3", s1, s2)

    # (4) impsingle-step8 with φ := (ψ → θ), ψ := (φ → χ), χ := (((φ → χ) → ψ) → ψ)
    s4 = lb.ref(
        "s4",
        "((((ψ → θ) → (φ → χ)) → (((φ → χ) → ψ) → ψ)) → ((φ → χ) → (((φ → χ) → ψ) → ψ)))",
        ref="impsingle-step8",
    )

    # (5) ax-mp(3, 4)
    s5 = lb.mp("s5", s3, s4)

    # (6) impsingle-step15 with φ := φ, ψ := χ, χ := ((φ → χ) → ψ), θ := ψ
    s6 = lb.ref(
        "s6",
        "(((φ → χ) → (((φ → χ) → ψ) → ψ)) → ((φ → ψ) → (((φ → χ) → ψ) → ψ)))",
        ref="impsingle-step15",
    )

    # (7) ax-mp(5, 6)
    res = lb.mp("res", s5, s6)

    return lb.build(res)


def prove_impsingle_peirce(sys: System) -> Proof:
    """impsingle-peirce: ( ( ( φ → ψ ) → φ ) → φ ).

    Peirce's law derived from impsingle-step22 and impsingle-step25.
    """
    lb = ProofBuilder(sys, "impsingle-peirce")

    # (1) impsingle-step22: φ → φ
    s1 = lb.ref(
        "s1",
        "φ → φ",
        ref="impsingle-step22",
    )

    # (2) impsingle-step25 with ψ:=φ, χ:=ψ: (φ → φ) → (((φ → ψ) → φ) → φ)
    s2 = lb.ref(
        "s2",
        "( φ → φ ) → ( ( ( φ → ψ ) → φ ) → φ )",
        ref="impsingle-step25",
    )

    # (3) ax-mp(1, 2)
    res = lb.mp("res", s1, s2)

    return lb.build(res)


def prove_merco1lem8(sys: System) -> Proof:
    """merco1lem8: φ → ((ψ → (ψ → χ)) → (ψ → χ)).

    Used to rederive the Tarski-Bernays-Wajsberg axioms from merco1.
    (Contributed by Anthony Hart, 17-Sep-2011.)
    """
    lb = ProofBuilder(sys, "merco1lem8")

    s16 = lb.ref(
        "s16",
        "(ψ → (ψ → χ)) → ((ψ → (ψ → χ)) → (ψ → χ))",
        ref="merco1lem6",
        note="merco1lem6",
    )

    s20 = lb.ref(
        "s20",
        "((ψ → (ψ → χ)) → ((ψ → (ψ → χ)) → (ψ → χ))) → (φ → ((ψ → (ψ → χ)) → (ψ → χ)))",
        ref="merco1lem6",
        note="merco1lem6",
    )

    res = lb.mp("res", s16, s20, "ax-mp 16,20")

    return lb.build(res)


def prove_merco1lem9(sys: System) -> Proof:
    """merco1lem9: ((φ → (φ → ψ)) → (φ → ψ)).

    Used to rederive the Tarski-Bernays-Wajsberg axioms from merco1.
    (Contributed by Anthony Hart, 18-Sep-2011.)
    """
    lb = ProofBuilder(sys, "merco1lem9")

    s16 = lb.ref(
        "s16",
        "(⊥ → φ) → ((φ → (φ → ψ)) → (φ → ψ))",
        ref="merco1lem8",
        note="merco1lem8",
    )

    s20 = lb.ref(
        "s20",
        "((⊥ → φ) → ((φ → (φ → ψ)) → (φ → ψ))) → ((φ → (φ → ψ)) → (φ → ψ))",
        ref="merco1lem8",
        note="merco1lem8",
    )

    res = lb.mp("res", s16, s20, "ax-mp 16,20")

    return lb.build(res)


def prove_merco1lem12(sys: System) -> Proof:
    """merco1lem12: (φ → ψ) → (((χ → (φ → τ)) → φ) → ψ).

    Used to rederive the Tarski-Bernays-Wajsberg axioms from merco1.
    (Contributed by Anthony Hart, 18-Sep-2011.)
    """
    lb = ProofBuilder(sys, "merco1lem12")

    # Step 1: merco1lem3 with φ := (φ → τ), ψ := (((χ → (φ → τ)) → φ) → ⊥), χ := χ
    s1 = lb.ref(
        "s1",
        "(((φ → τ) → (((χ → (φ → τ)) → φ) → ⊥)) → (χ → ⊥)) → (χ → (φ → τ))",
        ref="merco1lem3",
        note="merco1lem3",
    )

    # Step 2: merco1 with φ := φ, ψ := τ, χ := ((χ → (φ → τ)) → φ), θ := (χ → ⊥), τ := (χ → (φ → τ))
    s2 = lb.ref(
        "s2",
        "((((φ → τ) → (((χ → (φ → τ)) → φ) → ⊥)) → (χ → ⊥)) → (χ → (φ → τ))) → (((χ → (φ → τ)) → φ) → (((χ → (φ → τ)) → φ) → φ))",
        ref="merco1",
        note="merco1",
    )

    # Step 3: ax-mp(s1, s2)
    s3 = lb.mp("s3", s1, s2, "ax-mp 1,2")

    # Step 4: merco1lem9 with φ := ((χ → (φ → τ)) → φ), ψ := φ
    s4 = lb.ref(
        "s4",
        "((((χ → (φ → τ)) → φ) → (((χ → (φ → τ)) → φ) → φ)) → (((χ → (φ → τ)) → φ) → φ))",
        ref="merco1lem9",
        note="merco1lem9",
    )

    # Step 5: ax-mp(s3, s4)
    s5 = lb.mp("s5", s3, s4, "ax-mp 3,4")

    # Step 6: merco1lem11 with φ := ((χ → (φ → τ)) → φ), ψ := φ, χ := (ψ → φ), τ := ⊥
    s6 = lb.ref(
        "s6",
        "((((χ → (φ → τ)) → φ) → φ) → ((((ψ → φ) → (((χ → (φ → τ)) → φ) → ⊥)) → ⊥) → φ))",
        ref="merco1lem11",
        note="merco1lem11",
    )

    # Step 7: ax-mp(s5, s6)
    s7 = lb.mp("s7", s5, s6, "ax-mp 5,6")

    # Step 8: merco1 with φ := ψ, ψ := φ, χ := ((χ → (φ → τ)) → φ), θ := ⊥, τ := φ
    s8 = lb.ref(
        "s8",
        "((((ψ → φ) → (((χ → (φ → τ)) → φ) → ⊥)) → ⊥) → φ) → ((φ → ψ) → (((χ → (φ → τ)) → φ) → ψ))",
        ref="merco1",
        note="merco1",
    )

    # Step 9: ax-mp(s7, s8)
    res = lb.mp("res", s7, s8, "ax-mp 7,8")

    return lb.build(res)


def prove_merco1lem13(sys: System) -> Proof:
    """merco1lem13: ((((φ → ψ) → (χ → ψ)) → τ) → (φ → τ).

    Used to rederive the Tarski-Bernays-Wajsberg axioms from merco1.
    (Contributed by Anthony Hart, 18-Sep-2011.)
    """
    lb = ProofBuilder(sys, "merco1lem13")

    # Step 1: merco1 with φ := ψ, ψ := φ, χ := χ, θ := φ, τ := φ
    s1 = lb.ref(
        "s1",
        "(((((ψ → φ) → (χ → ⊥)) → φ) → φ) → ((φ → ψ) → (χ → ψ)))",
        ref="merco1",
        note="merco1",
    )

    # Step 2: merco1lem4 on s1
    s2 = lb.ref(
        "s2",
        "((((((ψ → φ) → (χ → ⊥)) → φ) → φ) → ((φ → ψ) → (χ → ψ))) → (φ → ((φ → ψ) → (χ → ψ))))",
        ref="merco1lem4",
        note="merco1lem4",
    )

    # Step 3: ax-mp(s1, s2)
    s3 = lb.mp("s3", s1, s2, "ax-mp 1,2")

    # Step 4: merco1lem12 with φ := φ, ψ := ((φ → ψ) → (χ → ψ)), χ := (τ → φ), τ := ⊥
    s4 = lb.ref(
        "s4",
        "((φ → ((φ → ψ) → (χ → ψ))) → ((((τ → φ) → (φ → ⊥)) → φ) → ((φ → ψ) → (χ → ψ))))",
        ref="merco1lem12",
        note="merco1lem12",
    )

    # Step 5: ax-mp(s3, s4)
    s5 = lb.mp("s5", s3, s4, "ax-mp 3,4")

    # Step 6: merco1 with φ := τ, ψ := φ, χ := φ, θ := φ, τ := ((φ → ψ) → (χ → ψ))
    s6 = lb.ref(
        "s6",
        "(((((τ → φ) → (φ → ⊥)) → φ) → ((φ → ψ) → (χ → ψ))) → ((((φ → ψ) → (χ → ψ)) → τ) → (φ → τ)))",
        ref="merco1",
        note="merco1",
    )

    # Step 7: ax-mp(s5, s6)
    res = lb.mp("res", s5, s6, "ax-mp 5,6")

    return lb.build(res)


def prove_re1tbw3(sys: System) -> Proof:
    """re1tbw3: ( ( ( φ → ψ ) → φ ) → φ ).

    Peirce's law derived from the Tarski-Bernays-Wajsberg axioms.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "re1tbw3")

    # Step 1: mercolem2 with ψ=φ, χ=φ, θ=φ
    s1 = lb.ref(
        "s1",
        "( ( ( φ → φ ) → φ ) → ( φ → ( φ → φ ) ) )",
        ref="mercolem2",
        note="mercolem2",
    )

    # Step 2: mercolem2 with χ=( ( ( φ → φ ) → φ ) → ( φ → ( φ → φ ) ) ),
    #         θ=( ( φ → ψ ) → φ )
    s2 = lb.ref(
        "s2",
        "( ( ( φ → ψ ) → φ ) → ( ( ( ( φ → φ ) → φ ) → ( φ → ( φ → φ ) ) ) → ( ( ( φ → ψ ) → φ ) → φ ) ) )",
        ref="mercolem2",
        note="mercolem2",
    )

    # Step 3: mercolem6 with φ=( ( φ → ψ ) → φ ),
    #         ψ=( ( ( φ → φ ) → φ ) → ( φ → ( φ → φ ) ) ),
    #         χ=φ
    s3 = lb.ref(
        "s3",
        "( ( ( φ → ψ ) → φ ) → ( ( ( ( φ → φ ) → φ ) → ( φ → ( φ → φ ) ) ) → ( ( ( φ → ψ ) → φ ) → φ ) ) ) → ( ( ( ( φ → φ ) → φ ) → ( φ → ( φ → φ ) ) ) → ( ( ( φ → ψ ) → φ ) → φ ) )",
        ref="mercolem6",
        note="mercolem6",
    )

    # Step 4: ax-mp(s2, s3)
    s4 = lb.mp("s4", s2, s3, "MP s2, s3")

    # Step 5: ax-mp(s1, s4)
    res = lb.mp("res", s1, s4, "MP s1, s4")

    return lb.build(res)


def prove_re1tbw2(sys: System) -> Proof:
    """re1tbw2: φ → (ψ → φ).

    The principle of simplification (ax-1) derived from the
    Tarski-Bernays-Wajsberg axioms.  (Contributed by Anthony Hart,
    16-Aug-2011.)
    """
    lb = ProofBuilder(sys, "re1tbw2")

    # Step 1: mercolem1 with φ=φ, ψ=φ, χ=φ, θ=ψ
    s1 = lb.ref(
        "s1",
        "( ( ( φ → φ ) → φ ) → ( φ → ( ψ → φ ) ) )",
        ref="mercolem1",
        note="mercolem1",
    )

    # Step 2: mercolem1 with φ=(φ→φ), ψ=φ, χ=(φ→(ψ→φ)), θ=ψ
    s2 = lb.ref(
        "s2",
        "( ( ( ( φ → φ ) → φ ) → ( φ → ( ψ → φ ) ) ) → ( φ → ( ψ → ( φ → ( ψ → φ ) ) ) ) )",
        ref="mercolem1",
        note="mercolem1",
    )

    # Step 3: ax-mp(s1, s2)
    s3 = lb.mp("s3", s1, s2, "MP s1, s2")

    # Step 4: mercolem6 with φ=φ, ψ=ψ, χ=(ψ→φ)
    s4 = lb.ref(
        "s4",
        "( ( φ → ( ψ → ( φ → ( ψ → φ ) ) ) ) → ( ψ → ( φ → ( ψ → φ ) ) ) )",
        ref="mercolem6",
        note="mercolem6",
    )

    # Step 5: ax-mp(s3, s4)
    s5 = lb.mp("s5", s3, s4, "MP s3, s4")

    # Step 6: mercolem6 with φ=ψ, ψ=φ, χ=φ
    s6 = lb.ref(
        "s6",
        "( ( ψ → ( φ → ( ψ → φ ) ) ) → ( φ → ( ψ → φ ) ) )",
        ref="mercolem6",
        note="mercolem6",
    )

    # Step 7: ax-mp(s5, s6)
    res = lb.mp("res", s5, s6, "MP s5, s6")

    return lb.build(res)


def prove_re1tbw1(sys: System) -> Proof:
    """re1tbw1: (φ → ψ) → ((ψ → χ) → (φ → χ)).

    Transitivity of implication (syllogism) derived from the
    Tarski-Bernays-Wajsberg axioms.  (Contributed by Anthony Hart,
    16-Aug-2011.)
    """
    lb = ProofBuilder(sys, "re1tbw1")

    # Step 1: mercolem3
    s1 = lb.ref(
        "s1",
        "( ψ → χ ) → ( ψ → ( φ → χ ) )",
        ref="mercolem3",
        note="mercolem3",
    )

    # Step 2: mercolem8 with τ=(φ→ψ), θ=(ψ→χ)
    s2 = lb.ref(
        "s2",
        "( φ → ψ ) → ( ( ψ → ( φ → χ ) ) → ( ( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) ) ) )",
        ref="mercolem8",
        note="mercolem8",
    )

    # Step 3: mercolem6 with φ=(φ→ψ), ψ=(ψ→(φ→χ)), χ=((ψ→χ)→(φ→χ))
    s3 = lb.ref(
        "s3",
        "( ( φ → ψ ) → ( ( ψ → ( φ → χ ) ) → ( ( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) ) ) ) ) → ( ( ψ → ( φ → χ ) ) → ( ( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) ) ) )",
        ref="mercolem6",
        note="mercolem6",
    )

    # Step 4: MP(s2, s3)
    s4 = lb.mp("s4", s2, s3, "MP s2, s3")

    # Step 5: mercolem3 with ψ=(ψ→(φ→χ)), χ=((φ→ψ)→((ψ→χ)→(φ→χ))), φ=(ψ→χ)
    s5 = lb.ref(
        "s5",
        "( ( ψ → ( φ → χ ) ) → ( ( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) ) ) ) → ( ( ψ → ( φ → χ ) ) → ( ( ψ → χ ) → ( ( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) ) ) ) )",
        ref="mercolem3",
        note="mercolem3",
    )

    # Step 6: MP(s4, s5)
    s6 = lb.mp("s6", s4, s5, "MP s4, s5")

    # Step 7: mercolem8 with φ=(ψ→χ), ψ=(ψ→(φ→χ)), χ=((φ→ψ)→((ψ→χ)→(φ→χ))),
    #         τ=((ψ→χ)→(ψ→(φ→χ))), θ=(φ→ψ)
    s7 = lb.ref(
        "s7",
        "( ( ψ → χ ) → ( ψ → ( φ → χ ) ) ) → ( ( ( ψ → ( φ → χ ) ) → ( ( ψ → χ ) → ( ( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) ) ) ) ) → ( ( ( ψ → χ ) → ( ψ → ( φ → χ ) ) ) → ( ( φ → ψ ) → ( ( ψ → χ ) → ( ( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) ) ) ) ) ) )",
        ref="mercolem8",
        note="mercolem8",
    )

    # Step 8: mercolem6 with φ=((ψ→χ)→(ψ→(φ→χ))), ψ=((ψ→(φ→χ))→...), χ=((φ→ψ)→...)
    s8 = lb.ref(
        "s8",
        "( ( ( ψ → χ ) → ( ψ → ( φ → χ ) ) ) → ( ( ( ψ → ( φ → χ ) ) → ( ( ψ → χ ) → ( ( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) ) ) ) ) → ( ( ( ψ → χ ) → ( ψ → ( φ → χ ) ) ) → ( ( φ → ψ ) → ( ( ψ → χ ) → ( ( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) ) ) ) ) ) ) ) → ( ( ( ψ → ( φ → χ ) ) → ( ( ψ → χ ) → ( ( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) ) ) ) ) → ( ( ( ψ → χ ) → ( ψ → ( φ → χ ) ) ) → ( ( φ → ψ ) → ( ( ψ → χ ) → ( ( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) ) ) ) ) ) )",
        ref="mercolem6",
        note="mercolem6",
    )

    # Step 9: MP(s7, s8)
    s9 = lb.mp("s9", s7, s8, "MP s7, s8")

    # Step 10: MP(s6, s9)
    s10 = lb.mp("s10", s6, s9, "MP s6, s9")

    # Step 11: MP(s1, s10)
    s11 = lb.mp("s11", s1, s10, "MP s1, s10")

    # Step 12: mercolem6 with φ=(φ→ψ), ψ=(ψ→χ), χ=((ψ→χ)→(φ→χ))
    s12 = lb.ref(
        "s12",
        "( ( φ → ψ ) → ( ( ψ → χ ) → ( ( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) ) ) ) ) → ( ( ψ → χ ) → ( ( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) ) ) )",
        ref="mercolem6",
        note="mercolem6",
    )

    # Step 13: MP(s11, s12)
    s13 = lb.mp("s13", s11, s12, "MP s11, s12")

    # Step 14: mercolem6 with φ=(ψ→χ), ψ=(φ→ψ), χ=(φ→χ)
    s14 = lb.ref(
        "s14",
        "( ( ψ → χ ) → ( ( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) ) ) ) → ( ( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) ) )",
        ref="mercolem6",
        note="mercolem6",
    )

    # Step 15: MP(s13, s14)
    res = lb.mp("res", s13, s14, "MP s13, s14")

    return lb.build(res)


def prove_mercolem8(sys: System) -> Proof:
    """mercolem8: (φ → ψ) → ((ψ → (φ → χ)) → (τ → (θ → (φ → χ)))).

    Used to rederive the Tarski-Bernays-Wajsberg axioms from merco2.
    (Contributed by Anthony Hart, 17-Aug-2011.)
    """
    lb = ProofBuilder(sys, "mercolem8")

    # Step 1: merco2 with all-φ substitution
    s1 = lb.ref(
        "s1",
        "( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) )",
        ref="merco2",
        note="merco2",
    )

    # Step 2: same as s1
    s2 = lb.ref(
        "s2",
        "( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) )",
        ref="merco2",
        note="merco2",
    )

    # Step 3: merco2 with φ:=(φ→χ), ψ:=((⊥→φ)→ψ), χ:=φ, θ:=ψ, τ:=τ, η:=θ
    s3 = lb.ref(
        "s3",
        "( ( ( ( φ → χ ) → ( ( ⊥ → φ ) → ψ ) ) → ( ( ⊥ → φ ) → ψ ) ) → ( ( ψ → ( φ → χ ) ) → ( τ → ( θ → ( φ → χ ) ) ) ) )",
        ref="merco2",
        note="merco2",
    )

    # Step 4: mercolem3 with ψ:=S, χ:=Q, φ:=(φ→ψ) where
    #   S = (((φ→χ)→((⊥→φ)→ψ))→((⊥→φ)→ψ))
    #   Q = ((ψ→(φ→χ))→(τ→(θ→(φ→χ))))
    s4 = lb.ref(
        "s4",
        "( ( ( ( ( φ → χ ) → ( ( ⊥ → φ ) → ψ ) ) → ( ( ⊥ → φ ) → ψ ) ) → ( ( ψ → ( φ → χ ) ) → ( τ → ( θ → ( φ → χ ) ) ) ) ) → ( ( ( ( φ → χ ) → ( ( ⊥ → φ ) → ψ ) ) → ( ( ⊥ → φ ) → ψ ) ) → ( ( φ → ψ ) → ( ( ψ → ( φ → χ ) ) → ( τ → ( θ → ( φ → χ ) ) ) ) ) ) )",
        ref="mercolem3",
        note="mercolem3",
    )

    # Step 5: MP(s3, s4)
    s5 = lb.mp("s5", s3, s4, "MP s3, s4")

    # Step 6: mercolem7 with φ:=φ, ψ:=ψ, χ:=χ, θ:=(⊥→φ)
    s6 = lb.ref(
        "s6",
        "( ( φ → ψ ) → ( ( ( φ → χ ) → ( ( ⊥ → φ ) → ψ ) ) → ( ( ⊥ → φ ) → ψ ) ) )",
        ref="mercolem7",
        note="mercolem7",
    )

    # Step 7: mercolem7 with φ:=(φ→ψ), ψ:=S, χ:=Q, θ:=(⊥→φ)
    s7 = lb.ref(
        "s7",
        "( ( ( φ → ψ ) → ( ( ( φ → χ ) → ( ( ⊥ → φ ) → ψ ) ) → ( ( ⊥ → φ ) → ψ ) ) ) → ( ( ( ( φ → ψ ) → ( ( ψ → ( φ → χ ) ) → ( τ → ( θ → ( φ → χ ) ) ) ) ) → ( ( ⊥ → φ ) → ( ( ( φ → χ ) → ( ( ⊥ → φ ) → ψ ) ) → ( ( ⊥ → φ ) → ψ ) ) ) ) → ( ( ⊥ → φ ) → ( ( ( φ → χ ) → ( ( ⊥ → φ ) → ψ ) ) → ( ( ⊥ → φ ) → ψ ) ) ) ) )",
        ref="mercolem7",
        note="mercolem7",
    )

    # Step 8: MP(s6, s7)
    s8 = lb.mp("s8", s6, s7, "MP s6, s7")

    # Step 9: merco2 with φ:=T, ψ:=((⊥→φ)→S), χ:=φ, θ:=S, τ:=A, η:=A where
    #   T = ((φ→ψ)→((ψ→(φ→χ))→(τ→(θ→(φ→χ)))))
    #   S = (((φ→χ)→((⊥→φ)→ψ))→((⊥→φ)→ψ))
    #   A = (((φ→φ)→((⊥→φ)→φ))→((φ→φ)→(φ→(φ→φ))))
    s9 = lb.ref(
        "s9",
        "( ( ( ( ( φ → ψ ) → ( ( ψ → ( φ → χ ) ) → ( τ → ( θ → ( φ → χ ) ) ) ) ) → ( ( ⊥ → φ ) → ( ( ( φ → χ ) → ( ( ⊥ → φ ) → ψ ) ) → ( ( ⊥ → φ ) → ψ ) ) ) ) → ( ( ⊥ → φ ) → ( ( ( φ → χ ) → ( ( ⊥ → φ ) → ψ ) ) → ( ( ⊥ → φ ) → ψ ) ) ) ) → ( ( ( ( ( φ → χ ) → ( ( ⊥ → φ ) → ψ ) ) → ( ( ⊥ → φ ) → ψ ) ) → ( ( φ → ψ ) → ( ( ψ → ( φ → χ ) ) → ( τ → ( θ → ( φ → χ ) ) ) ) ) ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( ( ( φ → φ ) → ( ( ⊥ → φ ) → φ ) ) → ( ( φ → φ ) → ( φ → ( φ → φ ) ) ) ) → ( ( φ → ψ ) → ( ( ψ → ( φ → χ ) ) → ( τ → ( θ → ( φ → χ ) ) ) ) ) ) ) ) )",
        ref="merco2",
        note="merco2",
    )

    # Step 10: MP(s8, s9)
    s10 = lb.mp("s10", s8, s9, "MP s8, s9")

    # Step 11: MP(s5, s10)
    s11 = lb.mp("s11", s5, s10, "MP s5, s10")

    # Step 12: MP(s2, s11)
    s12 = lb.mp("s12", s2, s11, "MP s2, s11")

    # Step 13: MP(s1, s12) → conclusion
    res = lb.mp("res", s1, s12, "MP s1, s12")

    return lb.build(res)


def prove_re2luk1(sys: System) -> Proof:
    """re2luk1: ( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) ).

    Derivation of the Łukasiewicz syllogism axiom from Russell-Bernays axioms.
    """
    lb = ProofBuilder(sys, "re2luk1")

    # 1: rb-imdf with (ψ→χ) and (φ→χ)
    s1 = lb.ref(
        "s1",
        "¬ ( ¬ ( ¬ ( ( ψ → χ ) → ( φ → χ ) ) ∨ ( ¬ ( ψ → χ ) ∨ ( φ → χ ) ) ) ∨ ¬ ( ¬ ( ¬ ( ψ → χ ) ∨ ( φ → χ ) ) ∨ ( ( ψ → χ ) → ( φ → χ ) ) ) )",
        ref="rb-imdf",
        note="rb-imdf",
    )

    # 2: rblem7 from s1
    s2 = lb.ref(
        "s2",
        "( ¬ ( ¬ ( ψ → χ ) ∨ ( φ → χ ) ) ∨ ( ( ψ → χ ) → ( φ → χ ) ) )",
        s1,
        ref="rblem7",
        note="rblem7",
    )

    # 3: rb-imdf with ψ and χ
    s3 = lb.ref(
        "s3",
        "¬ ( ¬ ( ¬ ( ψ → χ ) ∨ ( ¬ ψ ∨ χ ) ) ∨ ¬ ( ¬ ( ¬ ψ ∨ χ ) ∨ ( ψ → χ ) ) )",
        ref="rb-imdf",
        note="rb-imdf",
    )

    # 4: rblem6 from s3
    s4 = lb.ref(
        "s4",
        "( ¬ ( ψ → χ ) ∨ ( ¬ ψ ∨ χ ) )",
        s3,
        ref="rblem6",
        note="rblem6",
    )

    # 5: rb-ax2 with ¬(ψ→χ), ¬¬(¬ψ∨χ)
    s5 = lb.ref(
        "s5",
        "( ¬ ( ¬ ( ψ → χ ) ∨ ¬ ¬ ( ¬ ψ ∨ χ ) ) ∨ ( ¬ ¬ ( ¬ ψ ∨ χ ) ∨ ¬ ( ψ → χ ) ) )",
        ref="rb-ax2",
        note="rb-ax2",
    )

    # 6: rb-ax4 with ¬(ψ→χ)
    s6 = lb.ref(
        "s6",
        "( ¬ ( ¬ ( ψ → χ ) ∨ ¬ ( ψ → χ ) ) ∨ ¬ ( ψ → χ ) )",
        ref="rb-ax4",
        note="rb-ax4",
    )

    # 7: rb-ax3 with ¬(ψ→χ), ¬(ψ→χ)
    s7 = lb.ref(
        "s7",
        "( ¬ ¬ ( ψ → χ ) ∨ ( ¬ ( ψ → χ ) ∨ ¬ ( ψ → χ ) ) )",
        ref="rb-ax3",
        note="rb-ax3",
    )

    # 8: rbsyl from s6, s7
    s8 = lb.ref(
        "s8",
        "( ¬ ¬ ( ψ → χ ) ∨ ¬ ( ψ → χ ) )",
        s6,
        s7,
        ref="rbsyl",
        note="rbsyl",
    )

    # 9: rb-ax4 with (¬ψ∨χ)
    s9 = lb.ref(
        "s9",
        "( ¬ ( ¬ ( ¬ ψ ∨ χ ) ∨ ¬ ( ¬ ψ ∨ χ ) ) ∨ ¬ ( ¬ ψ ∨ χ ) )",
        ref="rb-ax4",
        note="rb-ax4",
    )

    # 10: rb-ax3 with (¬ψ∨χ), (¬ψ∨χ)
    s10 = lb.ref(
        "s10",
        "( ¬ ¬ ( ¬ ψ ∨ χ ) ∨ ( ¬ ( ¬ ψ ∨ χ ) ∨ ¬ ( ¬ ψ ∨ χ ) ) )",
        ref="rb-ax3",
        note="rb-ax3",
    )

    # 11: rbsyl from s9, s10
    s11 = lb.ref(
        "s11",
        "( ¬ ¬ ( ¬ ψ ∨ χ ) ∨ ¬ ( ¬ ψ ∨ χ ) )",
        s9,
        s10,
        ref="rbsyl",
        note="rbsyl",
    )

    # 12: rb-ax2 with ¬¬(¬ψ∨χ), ¬(¬ψ∨χ)
    s12 = lb.ref(
        "s12",
        "( ¬ ( ¬ ¬ ( ¬ ψ ∨ χ ) ∨ ¬ ( ¬ ψ ∨ χ ) ) ∨ ( ¬ ( ¬ ψ ∨ χ ) ∨ ¬ ¬ ( ¬ ψ ∨ χ ) ) )",
        ref="rb-ax2",
        note="rb-ax2",
    )

    # 13: anmp from s11, s12
    s13 = lb.ref(
        "s13",
        "( ¬ ( ¬ ψ ∨ χ ) ∨ ¬ ¬ ( ¬ ψ ∨ χ ) )",
        s11,
        s12,
        ref="anmp",
        note="anmp",
    )

    # 14: rblem1 from s8, s13
    s14 = lb.ref(
        "s14",
        "( ¬ ( ¬ ( ψ → χ ) ∨ ( ¬ ψ ∨ χ ) ) ∨ ( ¬ ( ψ → χ ) ∨ ¬ ¬ ( ¬ ψ ∨ χ ) ) )",
        s8,
        s13,
        ref="rblem1",
        note="rblem1",
    )

    # 15: rbsyl from s5, s14
    s15 = lb.ref(
        "s15",
        "( ¬ ( ¬ ( ψ → χ ) ∨ ( ¬ ψ ∨ χ ) ) ∨ ( ¬ ¬ ( ¬ ψ ∨ χ ) ∨ ¬ ( ψ → χ ) ) )",
        s5,
        s14,
        ref="rbsyl",
        note="rbsyl",
    )

    # 16: anmp from s4, s15
    s16 = lb.ref(
        "s16",
        "( ¬ ¬ ( ¬ ψ ∨ χ ) ∨ ¬ ( ψ → χ ) )",
        s4,
        s15,
        ref="anmp",
        note="anmp",
    )

    # 17: rb-imdf with φ and χ
    s17 = lb.ref(
        "s17",
        "¬ ( ¬ ( ¬ ( φ → χ ) ∨ ( ¬ φ ∨ χ ) ) ∨ ¬ ( ¬ ( ¬ φ ∨ χ ) ∨ ( φ → χ ) ) )",
        ref="rb-imdf",
        note="rb-imdf",
    )

    # 18: rblem7 from s17
    s18 = lb.ref(
        "s18",
        "( ¬ ( ¬ φ ∨ χ ) ∨ ( φ → χ ) )",
        s17,
        ref="rblem7",
        note="rblem7",
    )

    # 19: rblem1 from s16, s18
    s19 = lb.ref(
        "s19",
        "( ¬ ( ¬ ( ¬ ψ ∨ χ ) ∨ ( ¬ φ ∨ χ ) ) ∨ ( ¬ ( ψ → χ ) ∨ ( φ → χ ) ) )",
        s16,
        s18,
        ref="rblem1",
        note="rblem1",
    )

    # 20: rb-ax1
    s20 = lb.ref(
        "s20",
        "( ¬ ( ¬ ψ ∨ χ ) ∨ ( ¬ ( ¬ φ ∨ ψ ) ∨ ( ¬ φ ∨ χ ) ) )",
        ref="rb-ax1",
        note="rb-ax1",
    )

    # 21: rb-ax2
    s21 = lb.ref(
        "s21",
        "( ¬ ( ( ¬ ( ¬ ψ ∨ χ ) ∨ ( ¬ φ ∨ χ ) ) ∨ ¬ ( ¬ φ ∨ ψ ) ) ∨ ( ¬ ( ¬ φ ∨ ψ ) ∨ ( ¬ ( ¬ ψ ∨ χ ) ∨ ( ¬ φ ∨ χ ) ) ) )",
        ref="rb-ax2",
        note="rb-ax2",
    )

    # 22: rb-ax4 with (¬φ∨ψ)
    s22 = lb.ref(
        "s22",
        "( ¬ ( ¬ ( ¬ φ ∨ ψ ) ∨ ¬ ( ¬ φ ∨ ψ ) ) ∨ ¬ ( ¬ φ ∨ ψ ) )",
        ref="rb-ax4",
        note="rb-ax4",
    )

    # 23: rb-ax3 with (¬φ∨ψ), (¬φ∨ψ)
    s23 = lb.ref(
        "s23",
        "( ¬ ¬ ( ¬ φ ∨ ψ ) ∨ ( ¬ ( ¬ φ ∨ ψ ) ∨ ¬ ( ¬ φ ∨ ψ ) ) )",
        ref="rb-ax3",
        note="rb-ax3",
    )

    # 24: rbsyl from s22, s23
    s24 = lb.ref(
        "s24",
        "( ¬ ¬ ( ¬ φ ∨ ψ ) ∨ ¬ ( ¬ φ ∨ ψ ) )",
        s22,
        s23,
        ref="rbsyl",
        note="rbsyl",
    )

    # 25: rb-ax4 with (¬φ∨χ)
    s25 = lb.ref(
        "s25",
        "( ¬ ( ( ¬ φ ∨ χ ) ∨ ( ¬ φ ∨ χ ) ) ∨ ( ¬ φ ∨ χ ) )",
        ref="rb-ax4",
        note="rb-ax4",
    )

    # 26: rb-ax3 with (¬φ∨χ), (¬φ∨χ)
    s26 = lb.ref(
        "s26",
        "( ¬ ( ¬ φ ∨ χ ) ∨ ( ( ¬ φ ∨ χ ) ∨ ( ¬ φ ∨ χ ) ) )",
        ref="rb-ax3",
        note="rb-ax3",
    )

    # 27: rbsyl from s25, s26
    s27 = lb.ref(
        "s27",
        "( ¬ ( ¬ φ ∨ χ ) ∨ ( ¬ φ ∨ χ ) )",
        s25,
        s26,
        ref="rbsyl",
        note="rbsyl",
    )

    # 28: same as s11 (direct reference to step 11 in set.mm)
    # In ProofScaffold we use s11 directly in step 29

    # 29: rblem4 from s24, s27, s11
    s29 = lb.ref(
        "s29",
        "( ¬ ( ( ¬ ( ¬ φ ∨ ψ ) ∨ ( ¬ φ ∨ χ ) ) ∨ ¬ ( ¬ ψ ∨ χ ) ) ∨ ( ( ¬ ( ¬ ψ ∨ χ ) ∨ ( ¬ φ ∨ χ ) ) ∨ ¬ ( ¬ φ ∨ ψ ) ) )",
        s24,
        s27,
        s11,
        ref="rblem4",
        note="rblem4",
    )

    # 30: rb-ax2
    s30 = lb.ref(
        "s30",
        "( ¬ ( ¬ ( ¬ ψ ∨ χ ) ∨ ( ¬ ( ¬ φ ∨ ψ ) ∨ ( ¬ φ ∨ χ ) ) ) ∨ ( ( ¬ ( ¬ φ ∨ ψ ) ∨ ( ¬ φ ∨ χ ) ) ∨ ¬ ( ¬ ψ ∨ χ ) ) )",
        ref="rb-ax2",
        note="rb-ax2",
    )

    # 31: rbsyl from s29, s30
    s31 = lb.ref(
        "s31",
        "( ¬ ( ¬ ( ¬ ψ ∨ χ ) ∨ ( ¬ ( ¬ φ ∨ ψ ) ∨ ( ¬ φ ∨ χ ) ) ) ∨ ( ( ¬ ( ¬ ψ ∨ χ ) ∨ ( ¬ φ ∨ χ ) ) ∨ ¬ ( ¬ φ ∨ ψ ) ) )",
        s29,
        s30,
        ref="rbsyl",
        note="rbsyl",
    )

    # 32: rbsyl from s21, s31
    s32 = lb.ref(
        "s32",
        "( ¬ ( ¬ ( ¬ ψ ∨ χ ) ∨ ( ¬ ( ¬ φ ∨ ψ ) ∨ ( ¬ φ ∨ χ ) ) ) ∨ ( ¬ ( ¬ φ ∨ ψ ) ∨ ( ¬ ( ¬ ψ ∨ χ ) ∨ ( ¬ φ ∨ χ ) ) ) )",
        s21,
        s31,
        ref="rbsyl",
        note="rbsyl",
    )

    # 33: anmp from s20, s32
    s33 = lb.ref(
        "s33",
        "( ¬ ( ¬ φ ∨ ψ ) ∨ ( ¬ ( ¬ ψ ∨ χ ) ∨ ( ¬ φ ∨ χ ) ) )",
        s20,
        s32,
        ref="anmp",
        note="anmp",
    )

    # 34: rbsyl from s19, s33
    s34 = lb.ref(
        "s34",
        "( ¬ ( ¬ φ ∨ ψ ) ∨ ( ¬ ( ψ → χ ) ∨ ( φ → χ ) ) )",
        s19,
        s33,
        ref="rbsyl",
        note="rbsyl",
    )

    # 35: rb-imdf with φ and ψ
    s35 = lb.ref(
        "s35",
        "¬ ( ¬ ( ¬ ( φ → ψ ) ∨ ( ¬ φ ∨ ψ ) ) ∨ ¬ ( ¬ ( ¬ φ ∨ ψ ) ∨ ( φ → ψ ) ) )",
        ref="rb-imdf",
        note="rb-imdf",
    )

    # 36: rblem6 from s35
    s36 = lb.ref(
        "s36",
        "( ¬ ( φ → ψ ) ∨ ( ¬ φ ∨ ψ ) )",
        s35,
        ref="rblem6",
        note="rblem6",
    )

    # 37: rbsyl from s34, s36
    s37 = lb.ref(
        "s37",
        "( ¬ ( φ → ψ ) ∨ ( ¬ ( ψ → χ ) ∨ ( φ → χ ) ) )",
        s34,
        s36,
        ref="rbsyl",
        note="rbsyl",
    )

    # 38: rbsyl from s2, s37
    s38 = lb.ref(
        "s38",
        "( ¬ ( φ → ψ ) ∨ ( ( ψ → χ ) → ( φ → χ ) ) )",
        s2,
        s37,
        ref="rbsyl",
        note="rbsyl",
    )

    # 39: rb-imdf with (φ→ψ) and ((ψ→χ)→(φ→χ))
    s39 = lb.ref(
        "s39",
        "¬ ( ¬ ( ¬ ( ( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) ) ) ∨ ( ¬ ( φ → ψ ) ∨ ( ( ψ → χ ) → ( φ → χ ) ) ) ) ∨ ¬ ( ¬ ( ¬ ( φ → ψ ) ∨ ( ( ψ → χ ) → ( φ → χ ) ) ) ∨ ( ( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) ) ) ) )",
        ref="rb-imdf",
        note="rb-imdf",
    )

    # 40: rblem7 from s39
    s40 = lb.ref(
        "s40",
        "( ¬ ( ¬ ( φ → ψ ) ∨ ( ( ψ → χ ) → ( φ → χ ) ) ) ∨ ( ( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) ) ) )",
        s39,
        ref="rblem7",
        note="rblem7",
    )

    # 41: anmp from s38, s40
    res = lb.ref(
        "res",
        "( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) )",
        s38,
        s40,
        ref="anmp",
        note="anmp",
    )

    return lb.build(res)


def prove_impsingle_imim1(sys: System) -> Proof:
    """impsingle-imim1: ( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ).

    Transitivity of implication (syllogism) derived from impsingle-step21
    and impsingle-step25.  Step 29 in Lukasiewicz.
    """
    lb = ProofBuilder(sys, "impsingle-imim1")

    # (1) impsingle-step21(ph:=φ, ps:=χ, ch:=ψ):
    #     ( ( ( φ → χ ) → ψ ) → ψ ) → ( ( ψ → χ ) → ( φ → χ ) )
    s1 = lb.ref(
        "s1",
        "( ( ( φ → χ ) → ψ ) → ψ ) → ( ( ψ → χ ) → ( φ → χ ) )",
        ref="impsingle-step21",
        note="impsingle-step21(ph:=φ, ps:=χ, ch:=ψ)",
    )

    # (2) impsingle-step25(ph:=φ, ps:=ψ, ch:=χ):
    #     ( φ → ψ ) → ( ( ( φ → χ ) → ψ ) → ψ )
    s2 = lb.ref(
        "s2",
        "( φ → ψ ) → ( ( ( φ → χ ) → ψ ) → ψ )",
        ref="impsingle-step25",
        note="impsingle-step25(ph:=φ, ps:=ψ, ch:=χ)",
    )

    # (3) impsingle-step25(ph:=(φ→ψ), ps:=(((φ→χ)→ψ)→ψ), ch:=((ψ→χ)→(φ→χ))):
    #     ((φ→ψ)→(((φ→χ)→ψ)→ψ)) →
    #     ((((φ→ψ)→((ψ→χ)→(φ→χ)))→(((φ→χ)→ψ)→ψ))→(((φ→χ)→ψ)→ψ))
    s3 = lb.ref(
        "s3",
        "( ( φ → ψ ) → ( ( ( φ → χ ) → ψ ) → ψ ) ) →"
        " ( ( ( ( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) ) ) → ( ( ( φ → χ ) → ψ ) → ψ ) ) →"
        " ( ( ( φ → χ ) → ψ ) → ψ ) )",
        ref="impsingle-step25",
        note="impsingle-step25(ph:=(φ→ψ), ps:=(((φ→χ)→ψ)→ψ), ch:=((ψ→χ)→(φ→χ)))",
    )

    # (4) ax-mp(2, 3):
    #     ( ( ( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) ) ) → ( ( ( φ → χ ) → ψ ) → ψ ) ) →
    #     ( ( ( φ → χ ) → ψ ) → ψ )
    s4 = lb.mp("s4", s2, s3, "ax-mp 2,3")

    # (5) impsingle-step21(ph:=(φ→ψ), ps:=((ψ→χ)→(φ→χ)), ch:=(((φ→χ)→ψ)→ψ)):
    #     ( ( ( ( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) ) ) → ( ( ( φ → χ ) → ψ ) → ψ ) ) →
    #       ( ( ( φ → χ ) → ψ ) → ψ ) ) →
    #     ( ( ( ( ( φ → χ ) → ψ ) → ψ ) → ( ( ψ → χ ) → ( φ → χ ) ) ) →
    #       ( ( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) ) ) )
    s5 = lb.ref(
        "s5",
        "( ( ( ( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) ) ) → ( ( ( φ → χ ) → ψ ) → ψ ) ) →"
        " ( ( ( φ → χ ) → ψ ) → ψ ) ) →"
        " ( ( ( ( ( φ → χ ) → ψ ) → ψ ) → ( ( ψ → χ ) → ( φ → χ ) ) ) →"
        " ( ( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) ) ) )",
        ref="impsingle-step21",
        note="impsingle-step21(ph:=(φ→ψ), ps:=((ψ→χ)→(φ→χ)), ch:=(((φ→χ)→ψ)→ψ))",
    )

    # (6) ax-mp(4, 5):
    #     ( ( ( ( φ → χ ) → ψ ) → ψ ) → ( ( ψ → χ ) → ( φ → χ ) ) ) →
    #     ( ( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) ) )
    s6 = lb.mp("s6", s4, s5, "ax-mp 4,5")

    # (7) ax-mp(1, 6):
    #     ( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) )
    res = lb.mp("res", s1, s6, "ax-mp 1,6")

    return lb.build(res)


def prove_merco1lem14(sys: System) -> Proof:
    """merco1lem14: ((((φ → ψ) → ψ) → χ) → (φ → χ)).

    Used to rederive the Tarski-Bernays-Wajsberg axioms from merco1.
    (Contributed by Anthony Hart, 18-Sep-2011.)
    """
    lb = ProofBuilder(sys, "merco1lem14")

    # (1) merco1lem13 with φ := φ, ψ := ψ, χ := (φ → ψ), τ := ((φ → ψ) → ψ):
    #     (((φ → ψ) → ((φ → ψ) → ψ)) → ((φ → ψ) → ψ)) → (φ → ((φ → ψ) → ψ))
    s1 = lb.ref(
        "s1",
        "((((φ → ψ) → ((φ → ψ) → ψ)) → ((φ → ψ) → ψ)) → (φ → ((φ → ψ) → ψ)))",
        ref="merco1lem13",
        note="merco1lem13",
    )

    # (2) merco1lem8 with φ := (((φ → ((φ → ψ) → ψ)) → φ) → (((((φ → ψ) → ((φ → ψ) → ψ)) → ((φ → ψ) → ψ)) → (φ → ((φ → ψ) → ψ))) → ⊥)) → φ, ψ := (φ → ψ), χ := ψ:
    #     ((((φ → ((φ → ψ) → ψ)) → φ) → (((((φ → ψ) → ((φ → ψ) → ψ)) → ((φ → ψ) → ψ)) → (φ → ((φ → ψ) → ψ))) → ⊥)) → φ) → (((φ → ψ) → ((φ → ψ) → ψ)) → ((φ → ψ) → ψ))
    s2 = lb.ref(
        "s2",
        "((((φ → ((φ → ψ) → ψ)) → φ) → (((((φ → ψ) → ((φ → ψ) → ψ)) → ((φ → ψ) → ψ)) → (φ → ((φ → ψ) → ψ))) → ⊥)) → φ) → (((φ → ψ) → ((φ → ψ) → ψ)) → ((φ → ψ) → ψ))",
        ref="merco1lem8",
        note="merco1lem8",
    )

    # (3) merco1 with φ := (φ → ((φ → ψ) → ψ)), ψ := φ, χ := ((((φ → ψ) → ((φ → ψ) → ψ)) → ((φ → ψ) → ψ)) → (φ → ((φ → ψ) → ψ))), θ := φ, τ := (((φ → ψ) → ((φ → ψ) → ψ)) → ((φ → ψ) → ψ)):
    #     (((((φ → ((φ → ψ) → ψ)) → φ) → (((((φ → ψ) → ((φ → ψ) → ψ)) → ((φ → ψ) → ψ)) → (φ → ((φ → ψ) → ψ))) → ⊥)) → φ) → (((φ → ψ) → ((φ → ψ) → ψ)) → ((φ → ψ) → ψ))) → (((((φ → ψ) → ((φ → ψ) → ψ)) → ((φ → ψ) → ψ)) → (φ → ((φ → ψ) → ψ))) → (((((φ → ψ) → ((φ → ψ) → ψ)) → ((φ → ψ) → ψ)) → (φ → ((φ → ψ) → ψ))) → (φ → ((φ → ψ) → ψ))))
    s3 = lb.ref(
        "s3",
        "(((((φ → ((φ → ψ) → ψ)) → φ) → (((((φ → ψ) → ((φ → ψ) → ψ)) → ((φ → ψ) → ψ)) → (φ → ((φ → ψ) → ψ))) → ⊥)) → φ) → (((φ → ψ) → ((φ → ψ) → ψ)) → ((φ → ψ) → ψ))) → (((((φ → ψ) → ((φ → ψ) → ψ)) → ((φ → ψ) → ψ)) → (φ → ((φ → ψ) → ψ))) → (((((φ → ψ) → ((φ → ψ) → ψ)) → ((φ → ψ) → ψ)) → (φ → ((φ → ψ) → ψ))) → (φ → ((φ → ψ) → ψ))))",
        ref="merco1",
        note="merco1",
    )

    # (4) ax-mp(2, 3):
    #     ((((φ → ψ) → ((φ → ψ) → ψ)) → ((φ → ψ) → ψ)) → (φ → ((φ → ψ) → ψ))) → (((((φ → ψ) → ((φ → ψ) → ψ)) → ((φ → ψ) → ψ)) → (φ → ((φ → ψ) → ψ))) → (φ → ((φ → ψ) → ψ)))
    s4 = lb.mp("s4", s2, s3, "ax-mp 2,3")

    # (5) merco1lem9 with φ := ((((φ → ψ) → ((φ → ψ) → ψ)) → ((φ → ψ) → ψ)) → (φ → ((φ → ψ) → ψ))), ψ := (φ → ((φ → ψ) → ψ)):
    #     ((((((φ → ψ) → ((φ → ψ) → ψ)) → ((φ → ψ) → ψ)) → (φ → ((φ → ψ) → ψ))) → (((((φ → ψ) → ((φ → ψ) → ψ)) → ((φ → ψ) → ψ)) → (φ → ((φ → ψ) → ψ))) → (φ → ((φ → ψ) → ψ)))) → (((((φ → ψ) → ((φ → ψ) → ψ)) → ((φ → ψ) → ψ)) → (φ → ((φ → ψ) → ψ))) → (φ → ((φ → ψ) → ψ))))
    s5 = lb.ref(
        "s5",
        "((((((φ → ψ) → ((φ → ψ) → ψ)) → ((φ → ψ) → ψ)) → (φ → ((φ → ψ) → ψ))) → (((((φ → ψ) → ((φ → ψ) → ψ)) → ((φ → ψ) → ψ)) → (φ → ((φ → ψ) → ψ))) → (φ → ((φ → ψ) → ψ)))) → (((((φ → ψ) → ((φ → ψ) → ψ)) → ((φ → ψ) → ψ)) → (φ → ((φ → ψ) → ψ))) → (φ → ((φ → ψ) → ψ))))",
        ref="merco1lem9",
        note="merco1lem9",
    )

    # (6) ax-mp(4, 5):
    #     ((((φ → ψ) → ((φ → ψ) → ψ)) → ((φ → ψ) → ψ)) → (φ → ((φ → ψ) → ψ))) → (φ → ((φ → ψ) → ψ))
    s6 = lb.mp("s6", s4, s5, "ax-mp 4,5")

    # (7) ax-mp(1, 6):
    #     (φ → ((φ → ψ) → ψ))
    s7 = lb.mp("s7", s1, s6, "ax-mp 1,6")

    # (8) merco1lem12 with φ := φ, ψ := ((φ → ψ) → ψ), χ := (χ → φ), τ := ⊥:
    #     (φ → ((φ → ψ) → ψ)) → ((((χ → φ) → (φ → ⊥)) → φ) → ((φ → ψ) → ψ))
    s8 = lb.ref(
        "s8",
        "((φ → ((φ → ψ) → ψ)) → ((((χ → φ) → (φ → ⊥)) → φ) → ((φ → ψ) → ψ)))",
        ref="merco1lem12",
        note="merco1lem12",
    )

    # (9) ax-mp(7, 8):
    #     ((((χ → φ) → (φ → ⊥)) → φ) → ((φ → ψ) → ψ))
    s9 = lb.mp("s9", s7, s8, "ax-mp 7,8")

    # (10) merco1 with φ := χ, ψ := φ, χ := φ, θ := φ, τ := ((φ → ψ) → ψ):
    #      ((((χ → φ) → (φ → ⊥)) → φ) → ((φ → ψ) → ψ)) → ((((φ → ψ) → ψ) → χ) → (φ → χ))
    s10 = lb.ref(
        "s10",
        "((((χ → φ) → (φ → ⊥)) → φ) → ((φ → ψ) → ψ)) → ((((φ → ψ) → ψ) → χ) → (φ → χ))",
        ref="merco1",
        note="merco1",
    )

    # (11) ax-mp(9, 10):
    #      ((((φ → ψ) → ψ) → χ) → (φ → χ))
    res = lb.mp("res", s9, s10, "ax-mp 9,10")

    return lb.build(res)


def prove_merco1lem15(sys: System) -> Proof:
    """merco1lem15: (φ → ψ) → (φ → (χ → ψ)).

    Used to rederive the Tarski-Bernays-Wajsberg axioms from merco1.
    (Contributed by Anthony Hart, 18-Sep-2011.)
    """
    lb = ProofBuilder(sys, "merco1lem15")

    # (1) merco1lem14 with χ := χ → ψ:
    #     ((((φ → ψ) → ψ) → (χ → ψ)) → (φ → (χ → ψ)))
    s1 = lb.ref(
        "s1",
        "((((φ → ψ) → ψ) → (χ → ψ)) → (φ → (χ → ψ)))",
        ref="merco1lem14",
        note="merco1lem14",
    )

    # (2) merco1lem13 with φ := (((φ → ψ) → ψ) → (χ → ψ)) → (φ → (χ → ψ)),
    #     τ := (φ → ψ) → (φ → (χ → ψ)):
    #     (((((φ → ψ) → ψ) → (χ → ψ)) → (φ → (χ → ψ))) → ((φ → ψ) → (φ → (χ → ψ))))
    s2 = lb.ref(
        "s2",
        "(((((φ → ψ) → ψ) → (χ → ψ)) → (φ → (χ → ψ))) → ((φ → ψ) → (φ → (χ → ψ))))",
        ref="merco1lem13",
        note="merco1lem13",
    )

    # (3) ax-mp(1, 2):
    #     (φ → ψ) → (φ → (χ → ψ))
    res = lb.mp("res", s1, s2, "ax-mp 1,2")

    return lb.build(res)


def prove_merco1lem16(sys: System) -> Proof:
    """merco1lem16: ((φ → (ψ → χ)) → τ) → ((φ → χ) → τ).

    Used to rederive the Tarski-Bernays-Wajsberg axioms from merco1.
    (Contributed by Anthony Hart, 18-Sep-2011.)
    """
    lb = ProofBuilder(sys, "merco1lem16")

    # (1) merco1lem15 with φ := φ, ψ := χ, χ := ψ:
    #     (φ → χ) → (φ → (ψ → χ))
    s1 = lb.ref(
        "s1",
        "((φ → χ) → (φ → (ψ → χ)))",
        ref="merco1lem15",
        note="merco1lem15",
    )

    # (2) merco1lem11 with φ := (φ → χ), ψ := (φ → (ψ → χ)), χ := (τ → φ), τ := ⊥:
    #     ((φ → χ) → (φ → (ψ → χ))) → ((((τ → φ) → ((φ → χ) → ⊥)) → ⊥) → (φ → (ψ → χ)))
    s2 = lb.ref(
        "s2",
        "(((φ → χ) → (φ → (ψ → χ))) → ((((τ → φ) → ((φ → χ) → ⊥)) → ⊥) → (φ → (ψ → χ))))",
        ref="merco1lem11",
        note="merco1lem11",
    )

    # (3) ax-mp(1, 2):
    #     (((τ → φ) → ((φ → χ) → ⊥)) → ⊥) → (φ → (ψ → χ))
    s3 = lb.mp("s3", s1, s2, "ax-mp 1,2")

    # (4) merco1 with φ := τ, ψ := φ, χ := (φ → χ), θ := ⊥, τ := (φ → (ψ → χ)):
    #     ((((τ → φ) → ((φ → χ) → ⊥)) → ⊥) → (φ → (ψ → χ))) → (((φ → (ψ → χ)) → τ) → ((φ → χ) → τ))
    s4 = lb.ref(
        "s4",
        "(((((τ → φ) → ((φ → χ) → ⊥)) → ⊥) → (φ → (ψ → χ))) → (((φ → (ψ → χ)) → τ) → ((φ → χ) → τ)))",
        ref="merco1",
        note="merco1",
    )

    # (5) ax-mp(3, 4):
    #     ((φ → (ψ → χ)) → τ) → ((φ → χ) → τ)
    res = lb.mp("res", s3, s4, "ax-mp 3,4")

    return lb.build(res)


def prove_merco1lem17(sys: System) -> Proof:
    """merco1lem17: ((((φ → ψ) → φ) → χ) → τ) → ((φ → χ) → τ).

    Used to rederive the Tarski-Bernays-Wajsberg axioms from merco1.
    (Contributed by Anthony Hart, 18-Sep-2011.)
    """
    lb = ProofBuilder(sys, "merco1lem17")

    s1 = lb.ref(
        "s1",
        "( ( ( ( φ → ψ ) → φ ) → φ ) → ( ( ( ( χ → φ ) → ( ( ( φ → ψ ) → φ ) → ⊥ ) ) → ⊥ ) → φ ) )",
        ref="merco1lem11",
        note="merco1lem11",
    )

    s2 = lb.ref(
        "s2",
        "( ( ( ( ( ( ( ( χ → φ ) → ( ( ( φ → ψ ) → φ ) → ⊥ ) ) → ⊥ ) → φ ) → φ ) → ( ( ( ( ( φ → ψ ) → φ ) → φ ) → ( ( ( ( χ → φ ) → ( ( ( φ → ψ ) → φ ) → ⊥ ) ) → ⊥ ) → φ ) ) → ⊥ ) ) → φ ) → ( ( ( φ → ψ ) → φ ) → φ ) )",
        ref="merco1lem7",
        note="merco1lem7",
    )

    s3 = lb.ref(
        "s3",
        "( ( ( ( ( ( ( ( ( χ → φ ) → ( ( ( φ → ψ ) → φ ) → ⊥ ) ) → ⊥ ) → φ ) → φ ) → ( ( ( ( ( φ → ψ ) → φ ) → φ ) → ( ( ( ( χ → φ ) → ( ( ( φ → ψ ) → φ ) → ⊥ ) ) → ⊥ ) → φ ) ) → ⊥ ) ) → φ ) → ( ( ( φ → ψ ) → φ ) → φ ) ) → ( ( ( ( ( φ → ψ ) → φ ) → φ ) → ( ( ( ( χ → φ ) → ( ( ( φ → ψ ) → φ ) → ⊥ ) ) → ⊥ ) → φ ) ) → ( ( ( ( ( φ → ψ ) → φ ) → φ ) → ( ( ( ( χ → φ ) → ( ( ( φ → ψ ) → φ ) → ⊥ ) ) → ⊥ ) → φ ) ) → ( ( ( ( χ → φ ) → ( ( ( φ → ψ ) → φ ) → ⊥ ) ) → ⊥ ) → φ ) ) ) )",
        ref="merco1",
        note="merco1",
    )

    s5 = lb.ref(
        "s5",
        "( ( ( ( ( ( φ → ψ ) → φ ) → φ ) → ( ( ( ( χ → φ ) → ( ( ( φ → ψ ) → φ ) → ⊥ ) ) → ⊥ ) → φ ) ) → ( ( ( ( ( φ → ψ ) → φ ) → φ ) → ( ( ( ( χ → φ ) → ( ( ( φ → ψ ) → φ ) → ⊥ ) ) → ⊥ ) → φ ) ) → ( ( ( ( χ → φ ) → ( ( ( φ → ψ ) → φ ) → ⊥ ) ) → ⊥ ) → φ ) ) ) → ( ( ( ( ( φ → ψ ) → φ ) → φ ) → ( ( ( ( χ → φ ) → ( ( ( φ → ψ ) → φ ) → ⊥ ) ) → ⊥ ) → φ ) ) → ( ( ( ( χ → φ ) → ( ( ( φ → ψ ) → φ ) → ⊥ ) ) → ⊥ ) → φ ) ) )",
        ref="merco1lem9",
        note="merco1lem9",
    )

    s8 = lb.ref(
        "s8",
        "( ( ( ( ( χ → φ ) → ( ( ( φ → ψ ) → φ ) → ⊥ ) ) → ⊥ ) → φ ) → ( ( φ → χ ) → ( ( ( φ → ψ ) → φ ) → χ ) ) )",
        ref="merco1",
        note="merco1",
    )

    s10 = lb.ref(
        "s10",
        "( ( ( ( ( φ → χ ) → ⊥ ) → ( φ → χ ) ) → ( φ → χ ) ) → ( ( ( ( ( ( ( φ → ψ ) → φ ) → χ ) → φ ) → ( ( ( ( φ → χ ) → ⊥ ) → ( φ → χ ) ) → ⊥ ) ) → ⊥ ) → ( φ → χ ) ) )",
        ref="merco1lem11",
        note="merco1lem11",
    )

    s11 = lb.ref(
        "s11",
        "( ( ( ( ( ( ( ( ( ( ( φ → ψ ) → φ ) → χ ) → φ ) → ( ( ( ( φ → χ ) → ⊥ ) → ( φ → χ ) ) → ⊥ ) ) → ⊥ ) → ( φ → χ ) ) → φ ) → ( ( ( ( ( ( φ → χ ) → ⊥ ) → ( φ → χ ) ) → ( φ → χ ) ) → ( ( ( ( ( ( ( φ → ψ ) → φ ) → χ ) → φ ) → ( ( ( ( φ → χ ) → ⊥ ) → ( φ → χ ) ) → ⊥ ) ) → ⊥ ) → ( φ → χ ) ) ) → ⊥ ) ) → φ ) → ( ( ( ( φ → χ ) → ⊥ ) → ( φ → χ ) ) → ( φ → χ ) ) )",
        ref="merco1lem7",
        note="merco1lem7",
    )

    s12 = lb.ref(
        "s12",
        "( ( ( ( ( ( ( ( ( ( ( ( φ → ψ ) → φ ) → χ ) → φ ) → ( ( ( ( φ → χ ) → ⊥ ) → ( φ → χ ) ) → ⊥ ) ) → ⊥ ) → ( φ → χ ) ) → φ ) → ( ( ( ( ( ( φ → χ ) → ⊥ ) → ( φ → χ ) ) → ( φ → χ ) ) → ( ( ( ( ( ( ( φ → ψ ) → φ ) → χ ) → φ ) → ( ( ( ( φ → χ ) → ⊥ ) → ( φ → χ ) ) → ⊥ ) ) → ⊥ ) → ( φ → χ ) ) ) → ⊥ ) ) → φ ) → ( ( ( ( φ → χ ) → ⊥ ) → ( φ → χ ) ) → ( φ → χ ) ) ) → ( ( ( ( ( ( φ → χ ) → ⊥ ) → ( φ → χ ) ) → ( φ → χ ) ) → ( ( ( ( ( ( ( φ → ψ ) → φ ) → χ ) → φ ) → ( ( ( ( φ → χ ) → ⊥ ) → ( φ → χ ) ) → ⊥ ) ) → ⊥ ) → ( φ → χ ) ) ) → ( ( ( ( ( ( φ → χ ) → ⊥ ) → ( φ → χ ) ) → ( φ → χ ) ) → ( ( ( ( ( ( ( φ → ψ ) → φ ) → χ ) → φ ) → ( ( ( ( φ → χ ) → ⊥ ) → ( φ → χ ) ) → ⊥ ) ) → ⊥ ) → ( φ → χ ) ) ) → ( ( ( ( ( ( ( φ → ψ ) → φ ) → χ ) → φ ) → ( ( ( ( φ → χ ) → ⊥ ) → ( φ → χ ) ) → ⊥ ) ) → ⊥ ) → ( φ → χ ) ) ) ) )",
        ref="merco1",
        note="merco1",
    )

    s14 = lb.ref(
        "s14",
        "( ( ( ( ( ( ( φ → χ ) → ⊥ ) → ( φ → χ ) ) → ( φ → χ ) ) → ( ( ( ( ( ( ( φ → ψ ) → φ ) → χ ) → φ ) → ( ( ( ( φ → χ ) → ⊥ ) → ( φ → χ ) ) → ⊥ ) ) → ⊥ ) → ( φ → χ ) ) ) → ( ( ( ( ( ( φ → χ ) → ⊥ ) → ( φ → χ ) ) → ( φ → χ ) ) → ( ( ( ( ( ( ( φ → ψ ) → φ ) → χ ) → φ ) → ( ( ( ( φ → χ ) → ⊥ ) → ( φ → χ ) ) → ⊥ ) ) → ⊥ ) → ( φ → χ ) ) ) → ( ( ( ( ( ( ( φ → ψ ) → φ ) → χ ) → φ ) → ( ( ( ( φ → χ ) → ⊥ ) → ( φ → χ ) ) → ⊥ ) ) → ⊥ ) → ( φ → χ ) ) ) ) → ( ( ( ( ( ( φ → χ ) → ⊥ ) → ( φ → χ ) ) → ( φ → χ ) ) → ( ( ( ( ( ( ( φ → ψ ) → φ ) → χ ) → φ ) → ( ( ( ( φ → χ ) → ⊥ ) → ( φ → χ ) ) → ⊥ ) ) → ⊥ ) → ( φ → χ ) ) ) → ( ( ( ( ( ( ( φ → ψ ) → φ ) → χ ) → φ ) → ( ( ( ( φ → χ ) → ⊥ ) → ( φ → χ ) ) → ⊥ ) ) → ⊥ ) → ( φ → χ ) ) ) )",
        ref="merco1lem9",
        note="merco1lem9",
    )

    s17 = lb.ref(
        "s17",
        "( ( ( ( ( ( ( ( φ → ψ ) → φ ) → χ ) → φ ) → ( ( ( ( φ → χ ) → ⊥ ) → ( φ → χ ) ) → ⊥ ) ) → ⊥ ) → ( φ → χ ) ) → ( ( ( φ → χ ) → ( ( ( φ → ψ ) → φ ) → χ ) ) → ( ( ( ( φ → χ ) → ⊥ ) → ( φ → χ ) ) → ( ( ( φ → ψ ) → φ ) → χ ) ) ) )",
        ref="merco1",
        note="merco1",
    )

    s20 = lb.ref(
        "s20",
        "( ( ( ( ( φ → χ ) → ⊥ ) → ( φ → χ ) ) → ( ( ( φ → ψ ) → φ ) → χ ) ) → ( ( ( ( φ → χ ) → ⊥ ) → χ ) → ( ( ( φ → ψ ) → φ ) → χ ) ) )",
        ref="merco1lem16",
        note="merco1lem16",
    )

    s22 = lb.ref(
        "s22",
        "( ( ( ( τ → φ ) → ( ( φ → χ ) → ⊥ ) ) → χ ) → ( ( ( φ → χ ) → ⊥ ) → χ ) )",
        ref="merco1lem4",
        note="merco1lem4",
    )

    s23 = lb.ref(
        "s23",
        "( ( ( ( ( τ → φ ) → ( ( φ → χ ) → ⊥ ) ) → χ ) → ( ( ( φ → χ ) → ⊥ ) → χ ) ) → ( ( ( ( ( ( ( φ → ψ ) → φ ) → χ ) → φ ) → ( ( ( ( τ → φ ) → ( ( φ → χ ) → ⊥ ) ) → χ ) → ⊥ ) ) → ⊥ ) → ( ( ( φ → χ ) → ⊥ ) → χ ) ) )",
        ref="merco1lem11",
        note="merco1lem11",
    )

    s25 = lb.ref(
        "s25",
        "( ( ( ( ( ( ( ( φ → ψ ) → φ ) → χ ) → φ ) → ( ( ( ( τ → φ ) → ( ( φ → χ ) → ⊥ ) ) → χ ) → ⊥ ) ) → ⊥ ) → ( ( ( φ → χ ) → ⊥ ) → χ ) ) → ( ( ( ( ( φ → χ ) → ⊥ ) → χ ) → ( ( ( φ → ψ ) → φ ) → χ ) ) → ( ( ( ( τ → φ ) → ( ( φ → χ ) → ⊥ ) ) → χ ) → ( ( ( φ → ψ ) → φ ) → χ ) ) ) )",
        ref="merco1",
        note="merco1",
    )

    s28 = lb.ref(
        "s28",
        "( ( ( ( ( τ → φ ) → ( ( φ → χ ) → ⊥ ) ) → χ ) → ( ( ( φ → ψ ) → φ ) → χ ) ) → ( ( ( ( ( φ → ψ ) → φ ) → χ ) → τ ) → ( ( φ → χ ) → τ ) ) )",
        ref="merco1",
        note="merco1",
    )

    s4 = lb.mp("s4", s2, s3, "ax-mp 2,3")

    s6 = lb.mp("s6", s4, s5, "ax-mp 4,5")

    s7 = lb.mp("s7", s1, s6, "ax-mp 1,6")

    s9 = lb.mp("s9", s7, s8, "ax-mp 7,8")

    s13 = lb.mp("s13", s11, s12, "ax-mp 11,12")

    s15 = lb.mp("s15", s13, s14, "ax-mp 13,14")

    s16 = lb.mp("s16", s10, s15, "ax-mp 10,15")

    s18 = lb.mp("s18", s16, s17, "ax-mp 16,17")

    s19 = lb.mp("s19", s9, s18, "ax-mp 9,18")

    s21 = lb.mp("s21", s19, s20, "ax-mp 19,20")

    s24 = lb.mp("s24", s22, s23, "ax-mp 22,23")

    s26 = lb.mp("s26", s24, s25, "ax-mp 24,25")

    s27 = lb.mp("s27", s21, s26, "ax-mp 21,26")

    s29 = lb.mp("s29", s27, s28, "ax-mp 27,28")

    return lb.build(s29)


def prove_luklem6(sys: System) -> Proof:
    """luklem6: (φ → (φ → ψ)) → (φ → ψ).

    Used to rederive standard propositional axioms from Łukasiewicz'.
    (Contributed by NM, 22-Dec-2002.)
    """
    lb = ProofBuilder(sys, "luklem6")

    # s1: (φ → (φ → ψ)) → (((φ → ψ) → ψ) → (φ → ψ))    [luk-1]
    s1 = lb.ref(
        "s1",
        "( φ → ( φ → ψ ) ) → ( ( ( φ → ψ ) → ψ ) → ( φ → ψ ) )",
        ref="luk-1",
        note="luk-1",
    )

    # s2: ¬(φ → ψ) → (¬ψ → ¬(φ → ψ))    [luklem5]
    s2 = lb.ref(
        "s2",
        "¬ ( φ → ψ ) → ( ¬ ψ → ¬ ( φ → ψ ) )",
        ref="luklem5",
        note="luklem5",
    )

    # s3: (¬ψ → ¬(φ → ψ)) → (((¬ψ → ψ) → ψ) → ((φ → ψ) → ψ))    [luklem2]
    s3 = lb.ref(
        "s3",
        "( ¬ ψ → ¬ ( φ → ψ ) ) → ( ( ( ¬ ψ → ψ ) → ψ ) → ( ( φ → ψ ) → ψ ) )",
        ref="luklem2",
        note="luklem2",
    )

    # s4: ((((¬ψ → ψ) → ψ) → ((φ → ψ) → ψ)) → ((φ → ψ) → ψ))    [luklem4]
    s4 = lb.ref(
        "s4",
        "( ( ( ( ¬ ψ → ψ ) → ψ ) → ( ( φ → ψ ) → ψ ) ) → ( ( φ → ψ ) → ψ ) )",
        ref="luklem4",
        note="luklem4",
    )

    # s5: (¬ψ → ¬(φ → ψ)) → ((φ → ψ) → ψ)    [luklem1 s3, s4]
    s5 = lb.ref(
        "s5",
        "( ¬ ψ → ¬ ( φ → ψ ) ) → ( ( φ → ψ ) → ψ )",
        s3,
        s4,
        ref="luklem1",
        note="luklem1",
    )

    # s6: ¬(φ → ψ) → ((φ → ψ) → ψ)    [luklem1 s2, s5]
    s6 = lb.ref(
        "s6",
        "¬ ( φ → ψ ) → ( ( φ → ψ ) → ψ )",
        s2,
        s5,
        ref="luklem1",
        note="luklem1",
    )

    # s7: (¬(φ → ψ) → ((φ → ψ) → ψ)) → ((((φ → ψ) → ψ) → (φ → ψ)) → (¬(φ → ψ) → (φ → ψ)))    [luk-1]
    s7 = lb.ref(
        "s7",
        "( ¬ ( φ → ψ ) → ( ( φ → ψ ) → ψ ) ) → ( ( ( ( φ → ψ ) → ψ ) → ( φ → ψ ) ) → ( ¬ ( φ → ψ ) → ( φ → ψ ) ) )",
        ref="luk-1",
        note="luk-1",
    )

    # s8: (((φ → ψ) → ψ) → (φ → ψ)) → (¬(φ → ψ) → (φ → ψ))    [MP s6, s7]
    s8 = lb.mp("s8", s6, s7, "MP s6, s7")

    # s9: ((((φ → ψ) → ψ) → (φ → ψ)) → (¬(φ → ψ) → (φ → ψ))) → (((¬(φ → ψ) → (φ → ψ)) → (φ → ψ)) → ((((φ → ψ) → ψ) → (φ → ψ)) → (φ → ψ)))    [luk-1]
    s9 = lb.ref(
        "s9",
        "( ( ( ( φ → ψ ) → ψ ) → ( φ → ψ ) ) → ( ¬ ( φ → ψ ) → ( φ → ψ ) ) ) → ( ( ( ¬ ( φ → ψ ) → ( φ → ψ ) ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ψ ) → ( φ → ψ ) ) → ( φ → ψ ) ) )",
        ref="luk-1",
        note="luk-1",
    )

    # s10: ((¬(φ → ψ) → (φ → ψ)) → (φ → ψ)) → ((((φ → ψ) → ψ) → (φ → ψ)) → (φ → ψ))    [MP s8, s9]
    s10 = lb.mp("s10", s8, s9, "MP s8, s9")

    # s11: (((¬(φ → ψ) → (φ → ψ)) → (φ → ψ)) → ((((φ → ψ) → ψ) → (φ → ψ)) → (φ → ψ))) → ((((φ → ψ) → ψ) → (φ → ψ)) → (φ → ψ))    [luklem4]
    s11 = lb.ref(
        "s11",
        "( ( ( ¬ ( φ → ψ ) → ( φ → ψ ) ) → ( φ → ψ ) ) → ( ( ( ( φ → ψ ) → ψ ) → ( φ → ψ ) ) → ( φ → ψ ) ) ) → ( ( ( ( φ → ψ ) → ψ ) → ( φ → ψ ) ) → ( φ → ψ ) )",
        ref="luklem4",
        note="luklem4",
    )

    # s12: (((φ → ψ) → ψ) → (φ → ψ)) → (φ → ψ)    [MP s10, s11]
    s12 = lb.mp("s12", s10, s11, "MP s10, s11")

    # res: (φ → (φ → ψ)) → (φ → ψ)    [luklem1 s1, s12]
    res = lb.ref(
        "res",
        "( φ → ( φ → ψ ) ) → ( φ → ψ )",
        s1,
        s12,
        ref="luklem1",
        note="luklem1",
    )

    return lb.build(res)


def prove_luklem7(sys: System) -> Proof:
    """luklem7: ( φ → ( ψ → χ ) ) → ( ψ → ( φ → χ ) ).

    Commutation of antecedents.  Used to rederive standard propositional
    axioms from Łukasiewicz'.
    (Contributed by NM, 22-Dec-2002.)
    """
    lb = ProofBuilder(sys, "luklem7")

    # s1: ( φ → ( ψ → χ ) ) → ( ( ( ψ → χ ) → χ ) → ( φ → χ ) )    [luk-1]
    s1 = lb.ref(
        "s1",
        "( φ → ( ψ → χ ) ) → ( ( ( ψ → χ ) → χ ) → ( φ → χ ) )",
        ref="luk-1",
        note="luk-1",
    )

    # s2: ψ → ( ( ψ → χ ) → ψ )    [luklem5]
    s2 = lb.ref(
        "s2",
        "ψ → ( ( ψ → χ ) → ψ )",
        ref="luklem5",
        note="luklem5",
    )

    # s3: ( ( ψ → χ ) → ψ ) → ( ( ψ → χ ) → ( ( ψ → χ ) → χ ) )    [luk-1]
    s3 = lb.ref(
        "s3",
        "( ( ψ → χ ) → ψ ) → ( ( ψ → χ ) → ( ( ψ → χ ) → χ ) )",
        ref="luk-1",
        note="luk-1",
    )

    # s4: ψ → ( ( ψ → χ ) → ( ( ψ → χ ) → χ ) )    [luklem1 s2, s3]
    s4 = lb.ref(
        "s4",
        "ψ → ( ( ψ → χ ) → ( ( ψ → χ ) → χ ) )",
        s2,
        s3,
        ref="luklem1",
        note="luklem1",
    )

    # s5: ( ( ψ → χ ) → ( ( ψ → χ ) → χ ) ) → ( ( ψ → χ ) → χ )    [luklem6]
    s5 = lb.ref(
        "s5",
        "( ( ψ → χ ) → ( ( ψ → χ ) → χ ) ) → ( ( ψ → χ ) → χ )",
        ref="luklem6",
        note="luklem6",
    )

    # s6: ψ → ( ( ψ → χ ) → χ )    [luklem1 s4, s5]
    s6 = lb.ref(
        "s6",
        "ψ → ( ( ψ → χ ) → χ )",
        s4,
        s5,
        ref="luklem1",
        note="luklem1",
    )

    # s7: ( ψ → ( ( ψ → χ ) → χ ) ) → ( ( ( ( ψ → χ ) → χ ) → ( φ → χ ) ) → ( ψ → ( φ → χ ) ) )    [luk-1]
    s7 = lb.ref(
        "s7",
        "( ψ → ( ( ψ → χ ) → χ ) ) → ( ( ( ( ψ → χ ) → χ ) → ( φ → χ ) ) → ( ψ → ( φ → χ ) ) )",
        ref="luk-1",
        note="luk-1",
    )

    # s8: ( ( ( ψ → χ ) → χ ) → ( φ → χ ) ) → ( ψ → ( φ → χ ) )    [MP s6, s7]
    s8 = lb.mp("s8", s6, s7, "MP s6, s7")

    # res: ( φ → ( ψ → χ ) ) → ( ψ → ( φ → χ ) )    [luklem1 s1, s8]
    res = lb.ref(
        "res",
        "( φ → ( ψ → χ ) ) → ( ψ → ( φ → χ ) )",
        s1,
        s8,
        ref="luklem1",
        note="luklem1",
    )

    return lb.build(res)


def prove_ax2(sys: System) -> Proof:
    """ax2: ( φ → ( ψ → χ ) ) → ( ( φ → ψ ) → ( φ → χ ) ).

    Standard propositional axiom derived from Łukasiewicz axioms.
    (Contributed by NM, 22-Dec-2002.)
    """
    lb = ProofBuilder(sys, "ax2")

    # s1: ( φ → ( ψ → χ ) ) → ( ψ → ( φ → χ ) )    [luklem7]
    s1 = lb.ref(
        "s1",
        "( φ → ( ψ → χ ) ) → ( ψ → ( φ → χ ) )",
        ref="luklem7",
        note="luklem7",
    )

    # s2: ( ψ → ( φ → χ ) ) → ( ( φ → ψ ) → ( φ → ( φ → χ ) ) )    [luklem8]
    s2 = lb.ref(
        "s2",
        "( ψ → ( φ → χ ) ) → ( ( φ → ψ ) → ( φ → ( φ → χ ) ) )",
        ref="luklem8",
        note="luklem8",
    )

    # s3: ( φ → ( φ → χ ) ) → ( φ → χ )    [luklem6]
    s3 = lb.ref(
        "s3",
        "( φ → ( φ → χ ) ) → ( φ → χ )",
        ref="luklem6",
        note="luklem6",
    )

    # s4: ( ( φ → ( φ → χ ) ) → ( φ → χ ) ) → ( ( ( φ → ψ ) → ( φ → ( φ → χ ) ) ) → ( ( φ → ψ ) → ( φ → χ ) ) )    [luklem8]
    s4 = lb.ref(
        "s4",
        "( ( φ → ( φ → χ ) ) → ( φ → χ ) ) → ( ( ( φ → ψ ) → ( φ → ( φ → χ ) ) ) → ( ( φ → ψ ) → ( φ → χ ) ) )",
        ref="luklem8",
        note="luklem8",
    )

    # s5: ( ( φ → ψ ) → ( φ → ( φ → χ ) ) ) → ( ( φ → ψ ) → ( φ → χ ) )    [MP s3, s4]
    s5 = lb.mp("s5", s3, s4, "MP s3, s4")

    # s6: ( ψ → ( φ → χ ) ) → ( ( φ → ψ ) → ( φ → χ ) )    [luklem1 s2, s5]
    s6 = lb.ref(
        "s6",
        "( ψ → ( φ → χ ) ) → ( ( φ → ψ ) → ( φ → χ ) )",
        s2,
        s5,
        ref="luklem1",
        note="luklem1",
    )

    # res: ( φ → ( ψ → χ ) ) → ( ( φ → ψ ) → ( φ → χ ) )    [luklem1 s1, s6]
    res = lb.ref(
        "res",
        "( φ → ( ψ → χ ) ) → ( ( φ → ψ ) → ( φ → χ ) )",
        s1,
        s6,
        ref="luklem1",
        note="luklem1",
    )

    return lb.build(res)


def prove_sylancb(sys: System) -> Proof:
    r"""sylancb: φ → θ.

    Hyp 1: φ ↔ ψ
    Hyp 2: φ ↔ χ
    Hyp 3: ( ψ ∧ χ ) → θ
    Concl: φ → θ

    Inference joining two biconditionals with a conjunction;
    sylanc with biconditional replacements for the hypotheses.
    (Contributed by NM, 1-May-1995.)
    set.mm proof: syl2anb anidms.
    """
    lb = ProofBuilder(sys, "sylancb")
    h1 = lb.hyp("sylancb.1", "( φ ↔ ψ )")
    h2 = lb.hyp("sylancb.2", "( φ ↔ χ )")
    h3 = lb.hyp("sylancb.3", "( ψ ∧ χ ) → θ")
    s1 = lb.ref(
        "s1",
        "( φ ∧ φ ) → θ",
        h1,
        h2,
        h3,
        ref="syl2anb",
        note="syl2anb sylancb.1, sylancb.2, sylancb.3",
    )
    res = lb.ref("res", "φ → θ", s1, ref="anidms", note="anidms s1")
    return lb.build(res)


def prove_mpanl12(sys: System) -> Proof:
    """mpanl12: χ → θ.

    Inference joining two conjuncts to the left of an antecedent:
    given φ, ψ, and ( ( φ ∧ ψ ) ∧ χ ) → θ, conclude χ → θ.
    (Contributed by NM, 12-Apr-1994.)
    """
    lb = ProofBuilder(sys, "mpanl12")
    h1 = lb.hyp("mpanl12.1", "φ")
    h2 = lb.hyp("mpanl12.2", "ψ")
    h3 = lb.hyp("mpanl12.3", "( ( φ ∧ ψ ) ∧ χ ) → θ")

    s1 = lb.ref(
        "s1",
        "( ψ ∧ χ ) → θ",
        h1,
        h3,
        ref="mpanl1",
        note="mpanl1 mpanl12.1, mpanl12.3",
    )

    res = lb.ref(
        "res",
        "χ → θ",
        h2,
        s1,
        ref="mpan",
        note="mpan mpanl12.2, s1",
    )

    return lb.build(res)


def prove_mpanr12(sys: System) -> Proof:
    """mpanr12: φ → θ.

    Inference joining a right conjunct with an antecedent to form
    a single consequent: given ψ, χ, and ( φ ∧ ( ψ ∧ χ ) ) → θ,
    conclude φ → θ.  (Contributed by NM, 3-May-1994.)
    """
    lb = ProofBuilder(sys, "mpanr12")
    h1 = lb.hyp("mpanr12.1", "ψ")
    h2 = lb.hyp("mpanr12.2", "χ")
    h3 = lb.hyp("mpanr12.3", "( φ ∧ ( ψ ∧ χ ) ) → θ")
    s1 = lb.ref(
        "s1",
        "( φ ∧ χ ) → θ",
        h1,
        h3,
        ref="mpanr1",
        note="mpanr1 mpanr12.1, mpanr12.3",
    )
    res = lb.ref(
        "res",
        "φ → θ",
        h2,
        s1,
        ref="mpan2",
        note="mpan2 mpanr12.2, s1",
    )
    return lb.build(res)


def prove_mp3an2(sys: System) -> Proof:
    r"""mp3an2: ( φ ∧ χ ) → θ.

    Hyp 1: ψ
    Hyp 2: ( φ ∧ ψ ∧ χ ) → θ
    Concl: ( φ ∧ χ ) → θ

    Triple modus ponens with the second antecedent fixed.
    (Contributed by NM, 5-May-1996.)
    set.mm proof: 3expa mpanl2.
    """
    lb = ProofBuilder(sys, "mp3an2")
    h1 = lb.hyp("mp3an2.1", "ψ")
    h2 = lb.hyp("mp3an2.2", "( φ ∧ ψ ∧ χ ) → θ")
    s1 = lb.ref(
        "s1",
        "( ( φ ∧ ψ ) ∧ χ ) → θ",
        h2,
        ref="3expa",
        note="3expa mp3an2.2",
    )
    res = lb.ref(
        "res",
        "( φ ∧ χ ) → θ",
        h1,
        s1,
        ref="mpanl2",
        note="mpanl2 mp3an2.1, s1",
    )
    return lb.build(res)


def prove_ecase3ad(sys: System) -> Proof:
    """ecase3ad: φ → θ.  Hyps: φ → (ψ → θ), φ → (χ → θ), φ → ((¬ ψ ∧ ¬ χ) → θ).

    Deduction for elimination by cases with three alternatives.
    (Contributed by NM, 29-Dec-1992.)
    """
    lb = ProofBuilder(sys, "ecase3ad")
    h1 = lb.hyp("ecase3ad.1", "φ → ( ψ → θ )")
    h2 = lb.hyp("ecase3ad.2", "φ → ( χ → θ )")
    h3 = lb.hyp("ecase3ad.3", "φ → ( ( ¬ ψ ∧ ¬ χ ) → θ )")
    s1 = lb.ref("s1", "( φ ∧ ψ ) → θ", h1, ref="imp", note="imp")
    s2 = lb.ref("s2", "( φ ∧ χ ) → θ", h2, ref="imp", note="imp")
    s3 = lb.ref("s3", "( φ ∧ ( ¬ ψ ∧ ¬ χ ) ) → θ", h3, ref="imp", note="imp")
    res = lb.ref("res", "φ → θ", s1, s2, s3, ref="pm2.61ddan", note="pm2.61ddan")
    return lb.build(res)


def prove_ecase13d(sys: System) -> Proof:
    """ecase13d: φ → ψ.

    Hyps: φ → ¬ χ, φ → ¬ θ, φ → ( χ ∨ ψ ∨ θ ).

    Deduction for elimination by cases with three alternatives, where the
    first and third are eliminated by their negations.
    (Contributed by Jeff Hankins, 18-Aug-2009.)
    """
    lb = ProofBuilder(sys, "ecase13d")
    h1 = lb.hyp("ecase13d.1", "φ → ¬ χ")
    h2 = lb.hyp("ecase13d.2", "φ → ¬ θ")
    h3 = lb.hyp("ecase13d.3", "φ → ( χ ∨ ψ ∨ θ )")
    s1 = lb.ref(
        "s1",
        "( χ ∨ ψ ∨ θ ) ↔ ( χ ∨ ( ψ ∨ θ ) )",
        ref="3orass",
        note="3orass",
    )
    s2 = lb.ref(
        "s2",
        "( χ ∨ ( ψ ∨ θ ) ) ↔ ( ¬ χ → ( ψ ∨ θ ) )",
        ref="df-or",
        note="df-or",
    )
    s3 = lb.ref(
        "s3",
        "( χ ∨ ψ ∨ θ ) ↔ ( ¬ χ → ( ψ ∨ θ ) )",
        s1,
        s2,
        ref="bitri",
        note="bitri",
    )
    s4 = lb.ref(
        "s4",
        "φ → ( ¬ χ → ( ψ ∨ θ ) )",
        h3,
        s3,
        ref="sylib",
        note="sylib h3, s3",
    )
    s5 = lb.ref(
        "s5",
        "φ → ( ψ ∨ θ )",
        h1,
        s4,
        ref="mpd",
        note="mpd h1, s4",
    )
    res = lb.ref(
        "res",
        "φ → ψ",
        s5,
        h2,
        ref="olcnd",
        note="olcnd s5, h2",
    )
    return lb.build(res)


def prove_luklem8(sys: System) -> Proof:
    """luklem8: ( φ → ψ ) → ( ( χ → φ ) → ( χ → ψ ) ).

    Commutation of antecedents; used to rederive standard propositional
    axioms from Łukasiewicz'.
    (Contributed by NM, 22-Dec-2002.)
    """
    lb = ProofBuilder(sys, "luklem8")

    # s1: ( χ → φ ) → ( ( φ → ψ ) → ( χ → ψ ) )    [luk-1]
    s1 = lb.ref(
        "s1",
        "( χ → φ ) → ( ( φ → ψ ) → ( χ → ψ ) )",
        ref="luk-1",
        note="luk-1",
    )

    # s2: ( ( χ → φ ) → ( ( φ → ψ ) → ( χ → ψ ) ) ) → ( ( φ → ψ ) → ( ( χ → φ ) → ( χ → ψ ) ) )    [luklem7]
    s2 = lb.ref(
        "s2",
        "( ( χ → φ ) → ( ( φ → ψ ) → ( χ → ψ ) ) ) → ( ( φ → ψ ) → ( ( χ → φ ) → ( χ → ψ ) ) )",
        ref="luklem7",
        note="luklem7",
    )

    # res: ( φ → ψ ) → ( ( χ → φ ) → ( χ → ψ ) )    [MP s1, s2]
    res = lb.mp("res", s1, s2, "MP s1, s2")

    return lb.build(res)


def prove_merco1lem18(sys: System) -> Proof:
    """merco1lem18: ( φ → ( ψ → χ ) ) → ( ( ψ → φ ) → ( ψ → χ ) ).

    Used to rederive the Tarski-Bernays-Wajsberg axioms from merco1.
    (Contributed by Anthony Hart, 18-Sep-2011.)
    """
    lb = ProofBuilder(sys, "merco1lem18")

    # Define subformula abbreviations for readability
    A = "( ψ → χ )"
    B = "( ψ → φ )"
    Z = f"( ( φ → {A} ) → ( {B} → {A} ) )"  # conclusion
    I1 = f"( {B} → {Z} )"
    D = f"( ( {Z} → ⊥ ) → ( {I1} → ⊥ ) )"

    # Step 1: merco1
    s1 = lb.ref(
        "s1",
        f"( ( ( ( ( {A} → ψ ) → ( {B} → ⊥ ) ) → ( {A} → ψ ) ) → φ ) → {Z} )",
        ref="merco1",
        note="merco1",
    )

    # Step 2: merco1lem17
    s2 = lb.ref(
        "s2",
        f"( ( ( ( ( ( {A} → ψ ) → ( {B} → ⊥ ) ) → ( {A} → ψ ) ) → φ ) → {Z} ) → ( ( ( {A} → ψ ) → φ ) → {Z} ) )",
        ref="merco1lem17",
        note="merco1lem17",
    )

    # Step 3: ax-mp from s1, s2
    s3 = lb.mp("s3", s1, s2, "ax-mp 1,2")

    # Step 4: merco1lem17
    s4 = lb.ref(
        "s4",
        f"( ( ( ( {A} → ψ ) → φ ) → {Z} ) → ( {B} → ( ( φ → {A} ) → ( {B} → {A} ) ) ) )",
        ref="merco1lem17",
        note="merco1lem17",
    )

    # Step 5: ax-mp from s3, s4
    s5 = lb.mp("s5", s3, s4, "ax-mp 3,4")

    # Step 6: merco1lem5
    s6 = lb.ref(
        "s6",
        f"( ( ( ( {D} → ⊥ ) → ⊥ ) → ⊥ ) → ( {D} → ⊥ ) )",
        ref="merco1lem5",
        note="merco1lem5",
    )

    # Step 7: merco1lem3
    s7 = lb.ref(
        "s7",
        f"( ( ( ( ( {D} → ⊥ ) → ⊥ ) → ⊥ ) → ( {D} → ⊥ ) ) → ( {D} → ( ( {D} → ⊥ ) → ⊥ ) ) )",
        ref="merco1lem3",
        note="merco1lem3",
    )

    # Step 8: ax-mp from s6, s7
    s8 = lb.mp("s8", s6, s7, "ax-mp 6,7")

    # Step 9: merco1lem5
    s9 = lb.ref(
        "s9",
        f"( ( {D} → ( ( {D} → ⊥ ) → ⊥ ) ) → ( {Z} → ( ( {D} → ⊥ ) → ⊥ ) ) )",
        ref="merco1lem5",
        note="merco1lem5",
    )

    # Step 10: ax-mp from s8, s9
    s10 = lb.mp("s10", s8, s9, "ax-mp 8,9")

    # Step 11: merco1lem4
    s11 = lb.ref(
        "s11",
        f"( ( {Z} → ( ( {D} → ⊥ ) → ⊥ ) ) → ( ( {B} → {A} ) → ( ( {D} → ⊥ ) → ⊥ ) ) )",
        ref="merco1lem4",
        note="merco1lem4",
    )

    # Step 12: ax-mp from s10, s11
    s12 = lb.mp("s12", s10, s11, "ax-mp 10,11")

    # Step 13: merco1
    s13 = lb.ref(
        "s13",
        f"( ( ( {D} → ⊥ ) → {B} ) → ( {I1} → ( {I1} → {Z} ) ) )",
        ref="merco1",
        note="merco1",
    )

    # Step 14: merco1lem2
    s14 = lb.ref(
        "s14",
        f"( ( ( ( {D} → ⊥ ) → {B} ) → ( {I1} → ( {I1} → {Z} ) ) ) → ( ( ( {B} → {A} ) → ( ( {D} → ⊥ ) → ⊥ ) ) → ( {I1} → ( {I1} → {Z} ) ) ) )",
        ref="merco1lem2",
        note="merco1lem2",
    )

    # Step 15: ax-mp from s13, s14
    s15 = lb.mp("s15", s13, s14, "ax-mp 13,14")

    # Step 16: ax-mp from s12, s15
    s16 = lb.mp("s16", s12, s15, "ax-mp 12,15")

    # Step 17: merco1lem9
    s17 = lb.ref(
        "s17",
        f"( ( {I1} → ( {I1} → {Z} ) ) → ( {I1} → {Z} ) )",
        ref="merco1lem9",
        note="merco1lem9",
    )

    # Step 18: ax-mp from s16, s17
    s18 = lb.mp("s18", s16, s17, "ax-mp 16,17")

    # Step 19: ax-mp from s5, s18
    res = lb.mp("res", s5, s18, "ax-mp 5,18")

    return lb.build(res)


# New migrations register here beside their implementation.
# The aggregate registry imports this mapping, avoiding another edit to global shim files.
MIGRATION_THEOREMS: Mapping[str, LemmaCtor] = {
    "ax2": prove_ax2,
    "ecase13d": prove_ecase13d,
    "ecase3ad": prove_ecase3ad,
    "luklem8": prove_luklem8,
    "merco1lem18": prove_merco1lem18,
    "mp3an2": prove_mp3an2,
    "mpanl12": prove_mpanl12,
    "mpanr12": prove_mpanr12,
    "sylancb": prove_sylancb,
}
