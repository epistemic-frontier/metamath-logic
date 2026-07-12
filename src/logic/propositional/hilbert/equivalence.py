"""Biconditional calculus skeleton.

set.mm range:
    Main biconditional material starts at set.mm line 2390 and continues until
    conjunction is introduced at line 4044.

Scope:
    This module is reserved for theorems around ``<->`` and ``df-bi``:

    - definitional and justification material for biconditional reasoning
    - ``bi*`` inference helpers
    - ``bitr*`` transitivity helpers
    - ``imbi*`` and ``bibi*`` congruence/equality helpers

Migration notes:
    The current implementation still re-exports many early biconditional
    helpers through ``lemmas.py`` or depends on them indirectly. Move theorem
    constructors here when their dependency closure is ready and keep this
    module's ``THEOREMS`` map as the local registry fragment.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping

from skfd.proof import Proof, ProofBuilder

from . import System

LemmaCtor = Callable[[System], Proof]


def prove_biimp(sys: System) -> Proof:
    """biimp: ( φ <-> ψ ) → ( φ → ψ ).

    One direction of the biconditional: from a biconditional one can
    deduce the forward implication.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "biimp")

    # Step 1: df-bi axiom
    # ¬(((φ↔ψ)→¬((φ→ψ)→¬(ψ→φ)))→¬(¬((φ→ψ)→¬(ψ→φ))→(φ↔ψ)))
    dfbi = lb.ref(
        "dfbi",
        "¬ ( ( ( φ <-> ψ ) → ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) ) → "
        "¬ ( ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) → ( φ <-> ψ ) ) )",
        ref="df-bi",
        note="df-bi",
    )

    # Step 2: simplim applied to df-bi's formula
    # simplim: ¬(A→B)→A
    # With A = (φ↔ψ)→¬((φ→ψ)→¬(ψ→φ)), B = ¬(¬((φ→ψ)→¬(ψ→φ))→(φ↔ψ))
    s2 = lb.ref(
        "s2",
        "( ¬ ( ( ( φ <-> ψ ) → ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) ) → "
        "¬ ( ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) → ( φ <-> ψ ) ) ) ) → "
        "( ( φ <-> ψ ) → ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) )",
        ref="simplim",
        note="simplim",
    )

    # Step 3: MP with df-bi and simplim
    # → (φ<->ψ)→¬((φ→ψ)→¬(ψ→φ))
    s3 = lb.mp("s3", dfbi, s2, note="MP df-bi, simplim")

    # Step 4: simplim with a different substitution
    # simplim: ¬(A→B)→A
    # With A = (φ→ψ), B = ¬(ψ→φ)
    # → ¬((φ→ψ)→¬(ψ→φ))→(φ→ψ)
    s4 = lb.ref(
        "s4",
        "¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) → ( φ → ψ )",
        ref="simplim",
        note="simplim",
    )

    # Step 5: syl combines the two implications
    # syl: (A→B), (B→C) ⊢ (A→C)
    # With A = (φ↔ψ), B = ¬((φ→ψ)→¬(ψ→φ)), C = (φ→ψ)
    res = lb.ref(
        "res",
        "( φ <-> ψ ) → ( φ → ψ )",
        s3,
        s4,
        ref="syl",
        note="syl",
    )

    return lb.build(res)


def prove_biimpr(sys: System) -> Proof:
    """biimpr: ( φ <-> ψ ) → ( ψ → φ ).

    The other direction of the biconditional: from a biconditional one can
    deduce the reverse implication.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "biimpr")

    # Step 1: simprim, substitute φ→(φ→ψ), ψ→(ψ→φ)
    # simprim: ¬(φ→¬ψ)→ψ
    # → ¬((φ→ψ)→¬(ψ→φ)) → (ψ→φ)
    s1 = lb.ref(
        "s1",
        "¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) → ( ψ → φ )",
        ref="simprim",
        note="simprim",
    )

    # Step 2: dfbi1
    # dfbi1: (φ↔ψ) ↔ ¬((φ→ψ)→¬(ψ→φ))
    s2 = lb.ref(
        "s2",
        "( φ ↔ ψ ) ↔ ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) )",
        ref="dfbi1",
        note="dfbi1",
    )

    # Step 3: sylbi with s2 and s1
    # sylbi.1: (φ↔ψ) ↔ ¬((φ→ψ)→¬(ψ→φ))
    # sylbi.2: ¬((φ→ψ)→¬(ψ→φ)) → (ψ→φ)
    # conclusion: (φ↔ψ) → (ψ→φ)
    res = lb.ref(
        "res",
        "( φ ↔ ψ ) → ( ψ → φ )",
        s2,
        s1,
        ref="sylbi",
        note="sylbi",
    )

    return lb.build(res)


def prove_biimpi(sys: System) -> Proof:
    """biimpi: ( φ → ψ ).

    One direction of a biconditional, inference form.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "biimpi")
    h1 = lb.hyp("biimpi.1", "( φ <-> ψ )")
    s1 = lb.ref(
        "s1",
        "( φ <-> ψ ) → ( φ → ψ )",
        ref="biimp",
        note="biimp",
    )
    res = lb.mp("res", h1, s1, "MP hyp1, biimp")
    return lb.build(res)


def prove_biimpri(sys: System) -> Proof:
    """biimpri: ( ps -> ph ).

    One direction of a biconditional, inference form (reverse).
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "biimpri")
    h1 = lb.hyp("biimpri.1", "( ph <-> ps )")
    s1 = lb.ref("s1", "( ps <-> ph )", h1, ref="bicomi", note="bicomi")
    res = lb.ref("res", "( ps -> ph )", s1, ref="biimpi", note="biimpi")
    return lb.build(res)


def prove_biimpd(sys: System) -> Proof:
    """biimpd: ( ph → ( ps → ch ) ).

    Deduction form of biimp: from a hypothesis that implies a
    biconditional, deduce the forward implication.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "biimpd")
    h1 = lb.hyp("biimpd.1", "( ph → ( ps <-> ch ) )")
    s1 = lb.ref(
        "s1",
        "( ps <-> ch ) → ( ps → ch )",
        ref="biimp",
        note="biimp",
    )
    res = lb.ref(
        "res",
        "( ph → ( ps → ch ) )",
        h1,
        s1,
        ref="syl",
        note="syl",
    )
    return lb.build(res)


def prove_biimprd(sys: System) -> Proof:
    """biimprd: ( ph -> ( ch -> ps ) ).

    Deduction form of biimpr: from a hypothesis that implies a
    biconditional, deduce the reverse implication.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "biimprd")
    h1 = lb.hyp("biimprd.1", "( ph -> ( ps <-> ch ) )")
    s1 = lb.ref("s1", "( ch -> ch )", ref="id", note="id")
    res = lb.ref("res", "( ph -> ( ch -> ps ) )", s1, h1, ref="imbitrrid", note="imbitrrid")
    return lb.build(res)


def prove_biimpa(sys: System) -> Proof:
    r"""biimpa: ( ( ph /\ ps ) -> ch ).

    Deduction form of biimp with an antecedent: if ph implies
    (ps <-> ch), then (ph /\ ps) implies ch.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "biimpa")
    h1 = lb.hyp("biimpa.1", "( ph -> ( ps <-> ch ) )")

    # biimpd: ( ph -> ( ps <-> ch ) ) -> ( ph -> ( ps -> ch ) )
    s1 = lb.ref(
        "s1",
        "( ph -> ( ps -> ch ) )",
        h1,
        ref="biimpd",
        note="biimpd",
    )

    # imp: ( ph -> ( ps -> ch ) ) -> ( ( ph /\ ps ) -> ch )
    res = lb.ref(
        "res",
        r"( ( ph /\ ps ) -> ch )",
        s1,
        ref="imp",
        note="imp",
    )

    return lb.build(res)


def prove_biimpar(sys: System) -> Proof:
    r"""biimpar: ( ( ph /\ ch ) -> ps ).

    Deduction form of biimpr with an antecedent: if ph implies
    (ps <-> ch), then (ph /\ ch) implies ps.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "biimpar")
    h1 = lb.hyp("biimpar.1", "( ph -> ( ps <-> ch ) )")

    # biimprd: ( ph -> ( ps <-> ch ) ) -> ( ph -> ( ch -> ps ) )
    s1 = lb.ref(
        "s1",
        "( ph -> ( ch -> ps ) )",
        h1,
        ref="biimprd",
        note="biimprd",
    )

    # imp: ( ph -> ( ch -> ps ) ) -> ( ( ph /\ ch ) -> ps )
    res = lb.ref(
        "res",
        r"( ( ph /\ ch ) -> ps )",
        s1,
        ref="imp",
        note="imp",
    )

    return lb.build(res)


def prove_biimpac(sys: System) -> Proof:
    r"""biimpac: ( ( ps /\ ph ) -> ch ).

    Commuted form of biimpa: if ph implies (ps <-> ch), then
    (ps /\ ph) implies ch.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "biimpac")
    h1 = lb.hyp("biimpac.1", "( ph -> ( ps <-> ch ) )")

    # biimpcd: ( ph -> ( ps <-> ch ) ) -> ( ps -> ( ph -> ch ) )
    s1 = lb.ref(
        "s1",
        "( ps -> ( ph -> ch ) )",
        h1,
        ref="biimpcd",
        note="biimpcd",
    )

    # imp: ( ps -> ( ph -> ch ) ) -> ( ( ps /\ ph ) -> ch )
    res = lb.ref(
        "res",
        r"( ( ps /\ ph ) -> ch )",
        s1,
        ref="imp",
        note="imp",
    )

    return lb.build(res)


def prove_biimparc(sys: System) -> Proof:
    r"""biimparc: ( ( ch /\ ph ) -> ps ).

    If ph implies (ps <-> ch), then (ch /\ ph) implies ps.
    (Contributed by NM, 30-Sep-1992.)
    """
    lb = ProofBuilder(sys, "biimparc")
    h1 = lb.hyp("biimparc.1", "( ph -> ( ps <-> ch ) )")

    # biimprcd: ( ph -> ( ps <-> ch ) ) -> ( ch -> ( ph -> ps ) )
    s1 = lb.ref(
        "s1",
        "( ch -> ( ph -> ps ) )",
        h1,
        ref="biimprcd",
        note="biimprcd",
    )

    # imp: ( ch -> ( ph -> ps ) ) -> ( ( ch /\ ph ) -> ps )
    res = lb.ref(
        "res",
        r"( ( ch /\ ph ) -> ps )",
        s1,
        ref="imp",
        note="imp",
    )

    return lb.build(res)


def prove_impbi(sys: System) -> Proof:
    """impbi: ( φ → ψ ) → ( ( ψ → φ ) → ( φ ↔ ψ ) ).

    Deduce a biconditional from both directions of an implication.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "impbi")

    # Step 1: df-bi axiom
    # ¬(((φ↔ψ)→¬((φ→ψ)→¬(ψ→φ)))→¬(¬((φ→ψ)→¬(ψ→φ))→(φ↔ψ)))
    dfbi = lb.ref(
        "dfbi",
        "¬ ( ( ( φ ↔ ψ ) → ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) ) → "
        "¬ ( ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) → ( φ ↔ ψ ) ) )",
        ref="df-bi",
        note="df-bi",
    )

    # Step 2: simprim with substitution
    # simprim: ¬(φ→¬ψ)→ψ
    # Substitute φ = (φ↔ψ)→¬((φ→ψ)→¬(ψ→φ)),
    #            ψ = ¬((φ→ψ)→¬(ψ→φ))→(φ↔ψ)
    # → ¬(((φ↔ψ)→¬((φ→ψ)→¬(ψ→φ)))→¬(¬((φ→ψ)→¬(ψ→φ))→(φ↔ψ)))
    #   → (¬((φ→ψ)→¬(ψ→φ))→(φ↔ψ))
    s2 = lb.ref(
        "s2",
        "¬ ( ( ( φ ↔ ψ ) → ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) ) → "
        "¬ ( ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) → ( φ ↔ ψ ) ) ) → "
        "( ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) → ( φ ↔ ψ ) )",
        ref="simprim",
        note="simprim",
    )

    # Step 3: MP with df-bi and simprim instance
    # → ¬((φ→ψ)→¬(ψ→φ)) → (φ↔ψ)
    s3 = lb.mp("s3", dfbi, s2, note="MP df-bi, simprim")

    # Step 4: expi with hypothesis s3
    # expi.1: (¬(φ→¬ψ)→χ) with φ=(φ→ψ), ψ=(ψ→φ), χ=(φ↔ψ)
    # → (φ→ψ)→((ψ→φ)→(φ↔ψ))
    res = lb.ref(
        "res",
        "( φ → ψ ) → ( ( ψ → φ ) → ( φ ↔ ψ ) )",
        s3,
        ref="expi",
        note="expi",
    )

    return lb.build(res)


def prove_impbii(sys: System) -> Proof:
    """impbii: ( ph <-> ps ).

    Deduce a biconditional from both directions of an implication,
    inference form of impbi.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "impbii")
    h1 = lb.hyp("impbii.1", "( ph -> ps )")
    h2 = lb.hyp("impbii.2", "( ps -> ph )")

    # impbi: ( φ -> ψ ) -> ( ( ψ -> φ ) -> ( φ <-> ψ ) )
    impbi_ref = lb.ref(
        "impbi_ref",
        "( ph -> ps ) -> ( ( ps -> ph ) -> ( ph <-> ps ) )",
        ref="impbi",
        note="impbi",
    )

    # mp2 with mp2.1=(ph->ps), mp2.2=(ps->ph), mp2.3=impbi_ref
    res = lb.ref(
        "res",
        "( ph <-> ps )",
        h1,
        h2,
        impbi_ref,
        ref="mp2",
        note="mp2",
    )
    return lb.build(res)


def prove_impbidd(sys: System) -> Proof:
    """impbidd: ( ph -> ( ps -> ( ch <-> th ) ) ).

    Deduction form of impbi: from two implications, deduce a
    biconditional with nested antecedents.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "impbidd")

    h1 = lb.hyp("impbidd.1", "( ph -> ( ps -> ( ch -> th ) ) )")
    h2 = lb.hyp("impbidd.2", "( ph -> ( ps -> ( th -> ch ) ) )")

    impbi_ref = lb.ref(
        "impbi_ref",
        "( ( ch -> th ) -> ( ( th -> ch ) -> ( ch <-> th ) ) )",
        ref="impbi",
        note="impbi",
    )

    res = lb.ref(
        "res",
        "( ph -> ( ps -> ( ch <-> th ) ) )",
        h1,
        h2,
        impbi_ref,
        ref="syl6c",
        note="syl6c",
    )

    return lb.build(res)


def prove_impbid21d(sys: System) -> Proof:
    """impbid21d: ( ph -> ( ps -> ( ch <-> th ) ) ).

    Variant of impbidd: deduce a biconditional from two implications
    with swapped antecedents.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "impbid21d")

    h1 = lb.hyp("impbid21d.1", "( ps -> ( ch -> th ) )")
    h2 = lb.hyp("impbid21d.2", "( ph -> ( th -> ch ) )")

    impbi_ref = lb.ref(
        "impbi_ref",
        "( ( ch -> th ) -> ( ( th -> ch ) -> ( ch <-> th ) ) )",
        ref="impbi",
        note="impbi",
    )

    res = lb.ref(
        "res",
        "( ph -> ( ps -> ( ch <-> th ) ) )",
        h1,
        h2,
        impbi_ref,
        ref="syl2imc",
        note="syl2imc",
    )

    return lb.build(res)


def prove_2th(sys: System) -> Proof:
    """2th: ( ph <-> ps ).

    Two true statements are equivalent.
    (Contributed by NM, 30-Sep-1992.)
    """
    lb = ProofBuilder(sys, "2th")
    h1 = lb.hyp("2th.1", "ph")
    h2 = lb.hyp("2th.2", "ps")

    # a1i: from |- ps, get |- ( ph -> ps )
    s1 = lb.ref("s1", "( ph -> ps )", h2, ref="a1i", note="a1i 2th.2")

    # a1i: from |- ph, get |- ( ps -> ph )
    s2 = lb.ref("s2", "( ps -> ph )", h1, ref="a1i", note="a1i 2th.1")

    # impbii: from (ph -> ps) and (ps -> ph), get (ph <-> ps)
    res = lb.ref(
        "res",
        "( ph <-> ps )",
        s1,
        s2,
        ref="impbii",
        note="impbii",
    )

    return lb.build(res)
    return lb.build(res)


def prove_2thd(sys: System) -> Proof:
    """2thd: ( ph -> ( ps <-> ch ) ).

    Two true statements are equivalent (deduction form).
    (Contributed by NM, 30-Sep-1992.)
    """
    lb = ProofBuilder(sys, "2thd")
    h1 = lb.hyp("2thd.1", "( ph -> ps )")
    h2 = lb.hyp("2thd.2", "( ph -> ch )")

    # pm5.1im: ( ps -> ( ch -> ( ps <-> ch ) ) )
    s1 = lb.ref("s1", "( ps -> ( ch -> ( ps <-> ch ) ) )", ref="pm5.1im", note="pm5.1im")

    # sylc: from 2thd.1, 2thd.2, and s1, get ( ph -> ( ps <-> ch ) )
    res = lb.ref("res", "( ph -> ( ps <-> ch ) )", h1, h2, s1, ref="sylc", note="sylc")

    return lb.build(res)


def prove_2false(sys: System) -> Proof:
    """2false: ( φ ↔ ψ ).

    Two false statements are equivalent.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "2false")
    h1 = lb.hyp("2false.1", "¬ φ")
    h2 = lb.hyp("2false.2", "¬ ψ")

    # 2th: from ¬ φ and ¬ ψ, get ( ¬ φ ↔ ¬ ψ )
    s1 = lb.ref(
        "s1",
        "( ¬ φ ↔ ¬ ψ )",
        h1,
        h2,
        ref="2th",
        note="2th",
    )

    # con4bii: from ( ¬ φ ↔ ¬ ψ ), get ( φ ↔ ψ )
    res = lb.ref(
        "res",
        "( φ ↔ ψ )",
        s1,
        ref="con4bii",
        note="con4bii",
    )

    return lb.build(res)


def prove_2falsed(sys: System) -> Proof:
    """2falsed: ( ph -> ( ps <-> ch ) ).

    Deduce a biconditional from two negated antecedents.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "2falsed")
    h1 = lb.hyp("2falsed.1", "( ph -> -. ps )")
    h2 = lb.hyp("2falsed.2", "( ph -> -. ch )")

    # 2thd: from two negated antecedents, get a biconditional of negations
    s1 = lb.ref(
        "s1",
        "( ph -> ( -. ps <-> -. ch ) )",
        h1,
        h2,
        ref="2thd",
        note="2thd",
    )

    # con4bid: from a biconditional of negations, deduce the biconditional
    res = lb.ref(
        "res",
        "( ph -> ( ps <-> ch ) )",
        s1,
        ref="con4bid",
        note="con4bid",
    )

    return lb.build(res)


def prove_pm5_21ni(sys: System) -> Proof:
    """pm5.21ni: ( -. ps -> ( ph <-> ch ) ).

    Two propositions implying a false one are equivalent.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm5.21ni")
    h1 = lb.hyp("pm5.21ni.1", "( ph -> ps )")
    h2 = lb.hyp("pm5.21ni.2", "( ch -> ps )")

    # con3i: from ( ph -> ps ) get ( -. ps -> -. ph )
    s1 = lb.ref("s1", "( -. ps -> -. ph )", h1, ref="con3i", note="con3i pm5.21ni.1")

    # con3i: from ( ch -> ps ) get ( -. ps -> -. ch )
    s2 = lb.ref("s2", "( -. ps -> -. ch )", h2, ref="con3i", note="con3i pm5.21ni.2")

    # 2falsed: from ( -. ps -> -. ph ) and ( -. ps -> -. ch ) get ( -. ps -> ( ph <-> ch ) )
    res = lb.ref("res", "( -. ps -> ( ph <-> ch ) )", s1, s2, ref="2falsed", note="2falsed")

    return lb.build(res)


def prove_pm5_21nii(sys: System) -> Proof:
    """pm5.21nii: ( ph <-> ch ).

    Hypotheses: ( ph -> ps ), ( ch -> ps ), ( ps -> ( ph <-> ch ) ).
    Elimination of two antecedents with a biconditional consequent.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm5.21nii")
    h1 = lb.hyp("pm5.21nii.1", "( ph -> ps )")
    h2 = lb.hyp("pm5.21nii.2", "( ch -> ps )")
    h3 = lb.hyp("pm5.21nii.3", "( ps -> ( ph <-> ch ) )")

    # pm5.21ni: from h1, h2 get ( -. ps -> ( ph <-> ch ) )
    s1 = lb.ref("s1", "( -. ps -> ( ph <-> ch ) )", h1, h2, ref="pm5.21ni", note="pm5.21ni")

    # pm2.61i: from h3 (ps -> ...) and s1 (-.ps -> ...) get ( ph <-> ch )
    res = lb.ref("res", "( ph <-> ch )", h3, s1, ref="pm2.61i", note="pm2.61i")

    return lb.build(res)


def prove_bicom1(sys: System) -> Proof:
    """bicom1: ( ( ph <-> ps ) -> ( ps <-> ph ) ).

    Commutation of biconditional.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "bicom1")

    # biimpr: ( ph <-> ps ) -> ( ps -> ph )
    bimpr = lb.ref(
        "bimpr",
        "( ph <-> ps ) -> ( ps -> ph )",
        ref="biimpr",
        note="biimpr",
    )

    # biimp: ( ph <-> ps ) -> ( ph -> ps )
    bimp = lb.ref(
        "bimp",
        "( ph <-> ps ) -> ( ph -> ps )",
        ref="biimp",
        note="biimp",
    )

    # impbid: combine to get the swapped biconditional
    res = lb.ref(
        "res",
        "( ph <-> ps ) -> ( ps <-> ph )",
        bimpr,
        bimp,
        ref="impbid",
        note="impbid",
    )

    return lb.build(res)


def prove_bicom(sys: System) -> Proof:
    """bicom: |- ( ( ph <-> ps ) <-> ( ps <-> ph ) ).

    Commutation of biconditional: a biconditional is symmetric.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "bicom")

    # bicom1: ( ( ph <-> ps ) -> ( ps <-> ph ) )
    s1 = lb.ref(
        "s1",
        "( ( ph <-> ps ) -> ( ps <-> ph ) )",
        ref="bicom1",
        note="bicom1",
    )

    # bicom1 with swapped variables: ( ( ps <-> ph ) -> ( ph <-> ps ) )
    s2 = lb.ref(
        "s2",
        "( ( ps <-> ph ) -> ( ph <-> ps ) )",
        ref="bicom1",
        note="bicom1 swapped",
    )

    # impbii: from the two implications, deduce the biconditional
    res = lb.ref(
        "res",
        "( ( ph <-> ps ) <-> ( ps <-> ph ) )",
        s1,
        s2,
        ref="impbii",
        note="impbii",
    )

    return lb.build(res)

    return lb.build(res)


def prove_bicomd(sys: System) -> Proof:
    """bicomd: |- ( ph -> ( ch <-> ps ) ).

    Deduction form of bicom: from a biconditional, deduce the commuted
    version with the same antecedent.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "bicomd")

    h1 = lb.hyp("bicomd.1", "( ph -> ( ps <-> ch ) )")

    s1 = lb.ref(
        "s1",
        "( ( ps <-> ch ) <-> ( ch <-> ps ) )",
        ref="bicom",
        note="bicom",
    )

    res = lb.ref(
        "res",
        "( ph -> ( ch <-> ps ) )",
        h1,
        s1,
        ref="sylib",
        note="sylib",
    )

    return lb.build(res)


def prove_bicomi(sys: System) -> Proof:
    """bicomi: ( ps <-> ph ).

    Inference form of bicom1: from a biconditional, deduce the commuted
    version.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "bicomi")

    # Hypothesis: ( ph <-> ps )
    h1 = lb.hyp("bicomi.1", "( ph <-> ps )")

    # bicom1: ( ( ph <-> ps ) -> ( ps <-> ph ) )
    s1 = lb.ref(
        "s1",
        "( ( ph <-> ps ) -> ( ps <-> ph ) )",
        ref="bicom1",
        note="bicom1",
    )

    # MP: from ( ph <-> ps ) and (( ph <-> ps ) -> ( ps <-> ph )) get ( ps <-> ph )
    res = lb.mp("res", h1, s1, "MP hyp1, bicom1")

    return lb.build(res)


def prove_con34b(sys: System) -> Proof:
    """con34b: ( ( ph -> ps ) <-> ( -. ps -> -. ph ) ).

    Commutation of antecedents, commuted form (contraposition).
    (Contributed by NM, 13-Sep-2011.)
    """
    lb = ProofBuilder(sys, "con34b")

    # con3: ( ph -> ps ) -> ( -. ps -> -. ph )
    s1 = lb.ref(
        "s1",
        "( ph -> ps ) -> ( -. ps -> -. ph )",
        ref="con3",
        note="con3",
    )

    # con4: ( -. ps -> -. ph ) -> ( ph -> ps )
    s2 = lb.ref(
        "s2",
        "( -. ps -> -. ph ) -> ( ph -> ps )",
        ref="con4",
        note="con4",
    )

    # impbii: combine both directions
    res = lb.ref(
        "res",
        "( ( ph -> ps ) <-> ( -. ps -> -. ph ) )",
        s1,
        s2,
        ref="impbii",
        note="impbii",
    )

    return lb.build(res)
    return lb.build(res)


def prove_imdi(sys: System) -> Proof:
    """imdi: ( ( ph -> ( ps -> ch ) ) <-> ( ( ph -> ps ) -> ( ph -> ch ) ) ).

    Distribution of implication over implication, biconditional form.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "imdi")

    # ax-2: ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) )
    s1 = lb.ref(
        "s1",
        "( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) )",
        ref="ax-2",
        note="ax-2",
    )

    # pm2.86: ( ( ph -> ps ) -> ( ph -> ch ) ) -> ( ph -> ( ps -> ch ) )
    s2 = lb.ref(
        "s2",
        "( ( ph -> ps ) -> ( ph -> ch ) ) -> ( ph -> ( ps -> ch ) )",
        ref="pm2.86",
        note="pm2.86",
    )

    # impbii: combine the two implications into a biconditional
    res = lb.ref(
        "res",
        "( ( ph -> ( ps -> ch ) ) <-> ( ( ph -> ps ) -> ( ph -> ch ) ) )",
        s1,
        s2,
        ref="impbii",
        note="impbii",
    )

    return lb.build(res)
    return lb.build(res)


def prove_bi2_04(sys: System) -> Proof:
    """bi2.04: ( ( ph -> ( ps -> ch ) ) <-> ( ps -> ( ph -> ch ) ) ).

    Commutation of antecedents, biconditional form.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "bi2.04")

    # pm2.04: ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) )
    s1 = lb.ref(
        "s1",
        "( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) )",
        ref="pm2.04",
        note="pm2.04",
    )

    # pm2.04 with ph/ps swapped: ( ps -> ( ph -> ch ) ) -> ( ph -> ( ps -> ch ) )
    s2 = lb.ref(
        "s2",
        "( ps -> ( ph -> ch ) ) -> ( ph -> ( ps -> ch ) )",
        ref="pm2.04",
        note="pm2.04",
    )

    # impbii: combine the two implications into a biconditional
    res = lb.ref(
        "res",
        "( ( ph -> ( ps -> ch ) ) <-> ( ps -> ( ph -> ch ) ) )",
        s1,
        s2,
        ref="impbii",
        note="impbii",
    )

    return lb.build(res)
    return lb.build(res)


def prove_biid(sys: System) -> Proof:
    """biid: ( ph <-> ph ).

    Identity law for the biconditional: a proposition is equivalent to
    itself.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "biid")

    # id: ( ph -> ph )
    s1 = lb.ref("s1", "( ph -> ph )", ref="id", note="id")

    # impbii: from ( ph -> ph ) and ( ph -> ph ), get ( ph <-> ph )
    res = lb.ref("res", "( ph <-> ph )", s1, s1, ref="impbii", note="impbii")

    return lb.build(res)


def prove_biidd(sys: System) -> Proof:
    """biidd: ( ph -> ( ps <-> ps ) ).

    Deduction form of biid: given any proposition ph, the biconditional
    identity ( ps <-> ps ) still holds.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "biidd")

    # biid: ( ps <-> ps )
    s1 = lb.ref("s1", "( ps <-> ps )", ref="biid", note="biid")

    # a1i: from ( ps <-> ps ), get ( ph -> ( ps <-> ps ) )
    res = lb.ref("res", "( ph -> ( ps <-> ps ) )", s1, ref="a1i", note="a1i")

    return lb.build(res)


def prove_con2b(sys: System) -> Proof:
    """con2b: ( ( ph -> -. ps ) <-> ( ps -> -. ph ) ).

    Contraposition, biconditional form.
    (Contributed by NM, 29-Dec-1992.)
    """
    lb = ProofBuilder(sys, "con2b")

    # con2: ( ph -> -. ps ) -> ( ps -> -. ph )
    s1 = lb.ref(
        "s1",
        "( ph -> -. ps ) -> ( ps -> -. ph )",
        ref="con2",
        note="con2",
    )

    # con2 with ph/ps swapped: ( ps -> -. ph ) -> ( ph -> -. ps )
    s2 = lb.ref(
        "s2",
        "( ps -> -. ph ) -> ( ph -> -. ps )",
        ref="con2",
        note="con2",
    )

    # impbii combines both directions
    res = lb.ref(
        "res",
        "( ( ph -> -. ps ) <-> ( ps -> -. ph ) )",
        s1,
        s2,
        ref="impbii",
        note="impbii",
    )

    return lb.build(res)
    return lb.build(res)


def prove_con2bi(sys: System) -> Proof:
    """con2bi: ( φ ↔ ¬ ψ ) ↔ ( ψ ↔ ¬ φ ).

    Contraposition of biconditional, exchanging negated sides.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "con2bi")

    # bicom: ( ( φ ↔ ¬ ψ ) ↔ ( ¬ ψ ↔ φ ) )
    h1 = lb.ref(
        "h1",
        "( ( φ ↔ ¬ ψ ) ↔ ( ¬ ψ ↔ φ ) )",
        ref="bicom",
        note="bicom",
    )

    # notbi: ( ( ¬ ψ ↔ φ ) ↔ ( ¬ ¬ ψ ↔ ¬ φ ) )
    s_a = lb.ref(
        "s_a",
        "( ( ¬ ψ ↔ φ ) ↔ ( ¬ ¬ ψ ↔ ¬ φ ) )",
        ref="notbi",
        note="notbi",
    )

    # bicom: ( ( ¬ ¬ ψ ↔ ¬ φ ) ↔ ( ¬ φ ↔ ¬ ¬ ψ ) )
    s_b = lb.ref(
        "s_b",
        "( ( ¬ ¬ ψ ↔ ¬ φ ) ↔ ( ¬ φ ↔ ¬ ¬ ψ ) )",
        ref="bicom",
        note="bicom",
    )

    # bitri: ( ( ¬ ψ ↔ φ ) ↔ ( ¬ φ ↔ ¬ ¬ ψ ) )
    s_c = lb.ref(
        "s_c",
        "( ( ¬ ψ ↔ φ ) ↔ ( ¬ φ ↔ ¬ ¬ ψ ) )",
        s_a,
        s_b,
        ref="bitri",
        note="bitri",
    )

    # bicomi: ( ( ¬ φ ↔ ¬ ¬ ψ ) ↔ ( ¬ ψ ↔ φ ) )
    h2 = lb.ref(
        "h2",
        "( ( ¬ φ ↔ ¬ ¬ ψ ) ↔ ( ¬ ψ ↔ φ ) )",
        s_c,
        ref="bicomi",
        note="bicomi",
    )

    # notnotb: ( ψ ↔ ¬ ¬ ψ )
    s_d = lb.ref(
        "s_d",
        "( ψ ↔ ¬ ¬ ψ )",
        ref="notnotb",
        note="notnotb",
    )

    # bibi2i: ( ( ¬ φ ↔ ψ ) ↔ ( ¬ φ ↔ ¬ ¬ ψ ) )
    s_e = lb.ref(
        "s_e",
        "( ( ¬ φ ↔ ψ ) ↔ ( ¬ φ ↔ ¬ ¬ ψ ) )",
        s_d,
        ref="bibi2i",
        note="bibi2i",
    )

    # bicom: ( ( ψ ↔ ¬ φ ) ↔ ( ¬ φ ↔ ψ ) )
    s_f = lb.ref(
        "s_f",
        "( ( ψ ↔ ¬ φ ) ↔ ( ¬ φ ↔ ψ ) )",
        ref="bicom",
        note="bicom",
    )

    # bitri: ( ( ψ ↔ ¬ φ ) ↔ ( ¬ φ ↔ ¬ ¬ ψ ) )
    s_g = lb.ref(
        "s_g",
        "( ( ψ ↔ ¬ φ ) ↔ ( ¬ φ ↔ ¬ ¬ ψ ) )",
        s_f,
        s_e,
        ref="bitri",
        note="bitri",
    )

    # bicomi: ( ( ¬ φ ↔ ¬ ¬ ψ ) ↔ ( ψ ↔ ¬ φ ) )
    h3 = lb.ref(
        "h3",
        "( ( ¬ φ ↔ ¬ ¬ ψ ) ↔ ( ψ ↔ ¬ φ ) )",
        s_g,
        ref="bicomi",
        note="bicomi",
    )

    # 3bitr2i combines the three biconditionals
    res = lb.ref(
        "res",
        "( ( φ ↔ ¬ ψ ) ↔ ( ψ ↔ ¬ φ ) )",
        h1,
        h2,
        h3,
        ref="3bitr2i",
        note="3bitr2i",
    )

    return lb.build(res)


def prove_con2bid(sys: System) -> Proof:
    """con2bid: φ → ( χ ↔ ¬ ψ ).

    Hyp 1: φ → ( ψ ↔ ¬ χ )
    Concl: φ → ( χ ↔ ¬ ψ )

    Deduction form of con2bi.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "con2bid")
    h1 = lb.hyp("con2bid.1", "( φ → ( ψ ↔ ¬ χ ) )")
    # con2bi with φ := χ, ψ := ψ: ( ( χ ↔ ¬ ψ ) ↔ ( ψ ↔ ¬ χ ) )
    s1 = lb.ref(
        "s1",
        "( ( χ ↔ ¬ ψ ) ↔ ( ψ ↔ ¬ χ ) )",
        ref="con2bi",
        note="con2bi",
    )
    res = lb.ref("res", "( φ → ( χ ↔ ¬ ψ ) )", h1, s1, ref="sylibr", note="sylibr")
    return lb.build(res)


def prove_con2bii(sys: System) -> Proof:
    """con2bii: ( ψ ↔ ¬ φ ).

    Inference form of con2b: from ( φ ↔ ¬ ψ ), deduce ( ψ ↔ ¬ φ ).
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "con2bii")

    h1 = lb.hyp("con2bii.1", "( φ ↔ ¬ ψ )")

    # notnotb: ( ψ ↔ ¬ ¬ ψ )
    s1 = lb.ref(
        "s1",
        "( ψ ↔ ¬ ¬ ψ )",
        ref="notnotb",
        note="notnotb",
    )

    # xchbinxr with s1 and h1: ( ψ ↔ ¬ φ )
    res = lb.ref(
        "res",
        "( ψ ↔ ¬ φ )",
        s1,
        h1,
        ref="xchbinxr",
        note="xchbinxr",
    )

    return lb.build(res)


def prove_con1bid(sys: System) -> Proof:
    """con1bid: φ → ( ¬ χ ↔ ψ ).

    Deduction form of con1b: swap the negated side of a biconditional
    with the help of an antecedent.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "con1bid")
    h1 = lb.hyp("con1bid.1", "( φ → ( ¬ ψ ↔ χ ) )")
    s1 = lb.ref(
        "s1",
        "( φ → ( χ ↔ ¬ ψ ) )",
        h1,
        ref="bicomd",
        note="bicomd",
    )
    s2 = lb.ref(
        "s2",
        "( φ → ( ψ ↔ ¬ χ ) )",
        s1,
        ref="con2bid",
        note="con2bid",
    )
    res = lb.ref(
        "res",
        "( φ → ( ¬ χ ↔ ψ ) )",
        s2,
        ref="bicomd",
        note="bicomd",
    )
    return lb.build(res)


def prove_con1b(sys: System) -> Proof:
    """con1b: ( ( -. ph -> ps ) <-> ( -. ps -> ph ) ).

    Contraposition, biconditional form.
    (Contributed by NM, 29-Dec-1992.)
    """
    lb = ProofBuilder(sys, "con1b")

    # con1: ( -. ph -> ps ) -> ( -. ps -> ph )
    s1 = lb.ref(
        "s1",
        "( -. ph -> ps ) -> ( -. ps -> ph )",
        ref="con1",
        note="con1",
    )

    # con1 with ph/ps swapped: ( -. ps -> ph ) -> ( -. ph -> ps )
    s2 = lb.ref(
        "s2",
        "( -. ps -> ph ) -> ( -. ph -> ps )",
        ref="con1",
        note="con1",
    )

    # impbii combines both directions
    res = lb.ref(
        "res",
        "( ( -. ph -> ps ) <-> ( -. ps -> ph ) )",
        s1,
        s2,
        ref="impbii",
        note="impbii",
    )

    return lb.build(res)
    return lb.build(res)


def prove_con1bii(sys: System) -> Proof:
    """con1bii: ( ¬ ψ ↔ φ ).

    Inference form of con1b: from ( ¬ φ ↔ ψ ), deduce ( ¬ ψ ↔ φ ).
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "con1bii")

    h1 = lb.hyp("con1bii.1", "( ¬ φ ↔ ψ )")

    # notnotb: ( φ ↔ ¬ ¬ φ )
    s1 = lb.ref(
        "s1",
        "( φ ↔ ¬ ¬ φ )",
        ref="notnotb",
        note="notnotb",
    )

    # xchbinx with s1 and h1: ( φ ↔ ¬ ψ )
    s2 = lb.ref(
        "s2",
        "( φ ↔ ¬ ψ )",
        s1,
        h1,
        ref="xchbinx",
        note="xchbinx",
    )

    # bicomi: ( ¬ ψ ↔ φ )
    res = lb.ref(
        "res",
        "( ¬ ψ ↔ φ )",
        s2,
        ref="bicomi",
        note="bicomi",
    )

    return lb.build(res)


def prove_notbid(sys: System) -> Proof:
    """notbid: φ → ( ¬ ψ ↔ ¬ χ ).

    Negate both sides of a biconditional.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "notbid")

    h1 = lb.hyp("notbid.1", "( φ → ( ψ ↔ χ ) )")

    # notnotb: ( ψ ↔ ¬ ¬ ψ )
    s1 = lb.ref("s1", "( ψ ↔ ¬ ¬ ψ )", ref="notnotb", note="notnotb")

    # notnotb: ( χ ↔ ¬ ¬ χ )
    s2 = lb.ref("s2", "( χ ↔ ¬ ¬ χ )", ref="notnotb", note="notnotb")

    # 3bitr3g: from h1: ( φ → ( ψ ↔ χ ) ), s1, s2
    # deduce ( φ → ( ¬ ¬ ψ ↔ ¬ ¬ χ ) )
    s3 = lb.ref(
        "s3",
        "( φ → ( ¬ ¬ ψ ↔ ¬ ¬ χ ) )",
        h1,
        s1,
        s2,
        ref="3bitr3g",
        note="3bitr3g",
    )

    # con4bid: ( φ → ( ¬ ¬ ψ ↔ ¬ ¬ χ ) ) ⊢ ( φ → ( ¬ ψ ↔ ¬ χ ) )
    res = lb.ref(
        "res",
        "( φ → ( ¬ ψ ↔ ¬ χ ) )",
        s3,
        ref="con4bid",
        note="con4bid",
    )

    return lb.build(res)


def prove_notbi(sys: System) -> Proof:
    """notbi: ( φ ↔ ψ ) ↔ ( ¬ φ ↔ ¬ ψ ).

    Negation of both sides of a biconditional.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "notbi")

    # id: ( ( φ ↔ ψ ) → ( φ ↔ ψ ) )
    s1 = lb.ref("s1", "( ( φ ↔ ψ ) → ( φ ↔ ψ ) )", ref="id", note="id")

    # notbid: from s1, ( ( φ ↔ ψ ) → ( ¬ φ ↔ ¬ ψ ) )
    s2 = lb.ref("s2", "( ( φ ↔ ψ ) → ( ¬ φ ↔ ¬ ψ ) )", s1, ref="notbid", note="notbid")

    # id: ( ( ¬ φ ↔ ¬ ψ ) → ( ¬ φ ↔ ¬ ψ ) )
    s3 = lb.ref("s3", "( ( ¬ φ ↔ ¬ ψ ) → ( ¬ φ ↔ ¬ ψ ) )", ref="id", note="id")

    # con4bid: from s3, ( ( ¬ φ ↔ ¬ ψ ) → ( φ ↔ ψ ) )
    s4 = lb.ref("s4", "( ( ¬ φ ↔ ¬ ψ ) → ( φ ↔ ψ ) )", s3, ref="con4bid", note="con4bid")

    # impbii: combine s2 and s4
    res = lb.ref(
        "res",
        "( ( φ ↔ ψ ) ↔ ( ¬ φ ↔ ¬ ψ ) )",
        s2,
        s4,
        ref="impbii",
        note="impbii",
    )

    return lb.build(res)


def prove_notbii(sys: System) -> Proof:
    """notbii: ( ¬ φ ↔ ¬ ψ ).

    Inference form of notbi.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "notbii")
    h1 = lb.hyp("notbii.1", "( φ ↔ ψ )")

    # notbi: ( ( φ ↔ ψ ) ↔ ( ¬ φ ↔ ¬ ψ ) )
    notbi_th = lb.ref(
        "notbi_th",
        "( ( φ ↔ ψ ) ↔ ( ¬ φ ↔ ¬ ψ ) )",
        ref="notbi",
        note="notbi",
    )

    # mpbi: from the hypothesis and notbi, deduce the conclusion
    res = lb.ref(
        "res",
        "( ¬ φ ↔ ¬ ψ )",
        h1,
        notbi_th,
        ref="mpbi",
        note="mpbi",
    )

    return lb.build(res)


def prove_pm4_81(sys: System) -> Proof:
    """pm4.81: ( ( -. ph -> ph ) <-> ph ).

    Negation of a conditional implies the negation of the consequent, with the
    antecedent negated.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm4.81")

    # pm2.18: ( -. ph -> ph ) -> ph
    s1 = lb.ref(
        "s1",
        "( -. ph -> ph ) -> ph",
        ref="pm2.18",
        note="pm2.18",
    )

    # pm2.24: ph -> ( -. ph -> ph )
    s2 = lb.ref(
        "s2",
        "ph -> ( -. ph -> ph )",
        ref="pm2.24",
        note="pm2.24",
    )

    # impbii combines both directions
    res = lb.ref(
        "res",
        "( ( -. ph -> ph ) <-> ph )",
        s1,
        s2,
        ref="impbii",
        note="impbii",
    )

    return lb.build(res)
    return lb.build(res)


def prove_notnotb(sys: System) -> Proof:
    """notnotb: ( ph <-> -. -. ph ).

    Double negation equivalence.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "notnotb")
    s1 = lb.ref("s1", "( ph -> -. -. ph )", ref="notnot", note="notnot")
    s2 = lb.ref("s2", "( -. -. ph -> ph )", ref="notnotr", note="notnotr")
    res = lb.ref("res", "( ph <-> -. -. ph )", s1, s2, ref="impbii", note="impbii")
    return lb.build(res)


def prove_pm4_8(sys: System) -> Proof:
    """pm4.8: ( ( ph -> -. ph ) <-> -. ph ).

    Weak Clavius law, biconditional form.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm4.8")
    s1 = lb.ref("s1", "( ( ph -> -. ph ) -> -. ph )", ref="pm2.01", note="pm2.01")
    s2 = lb.ref("s2", "( -. ph -> ( ph -> -. ph ) )", ref="ax-1", note="ax-1")
    res = lb.ref("res", "( ( ph -> -. ph ) <-> -. ph )", s1, s2, ref="impbii", note="impbii")
    return lb.build(res)


def prove_pm5_1im(sys: System) -> Proof:
    """pm5.1im: ( ph -> ( ps -> ( ph <-> ps ) ) ).

    Variant of pm5.1 expressed with implications instead of conjunction:
    from two true statements, deduce their equivalence.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm5.1im")

    # ax-1: ( ps -> ( ph -> ps ) ) — impbid21d.1 with ch=ph, th=ps
    h1 = lb.ref("h1", "( ps -> ( ph -> ps ) )", ref="ax-1", note="ax-1")

    # ax-1: ( ph -> ( ps -> ph ) ) — impbid21d.2 with ch=ph, th=ps
    h2 = lb.ref("h2", "( ph -> ( ps -> ph ) )", ref="ax-1", note="ax-1")

    # impbid21d: from both hypotheses deduce the biconditional
    res = lb.ref(
        "res",
        "( ph -> ( ps -> ( ph <-> ps ) ) )",
        h1,
        h2,
        ref="impbid21d",
        note="impbid21d",
    )

    return lb.build(res)


def prove_pm5_501(sys: System) -> Proof:
    r"""pm5.501: ( ph -> ( ps <-> ( ph <-> ps ) ) ).

    From ph and ps, deduce that ps is equivalent to the
    biconditional ph <-> ps.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm5.501")

    # pm5.1im: ( ph -> ( ps -> ( ph <-> ps ) ) )
    s1 = lb.ref(
        "s1",
        "( ph -> ( ps -> ( ph <-> ps ) ) )",
        ref="pm5.1im",
        note="pm5.1im",
    )

    # biimp: ( ( ph <-> ps ) -> ( ph -> ps ) )
    s2 = lb.ref(
        "s2",
        "( ( ph <-> ps ) -> ( ph -> ps ) )",
        ref="biimp",
        note="biimp",
    )

    # com12: ( ( ph <-> ps ) -> ( ph -> ps ) ) -> ( ph -> ( ( ph <-> ps ) -> ps ) )
    s3 = lb.ref(
        "s3",
        "( ph -> ( ( ph <-> ps ) -> ps ) )",
        s2,
        ref="com12",
        note="com12",
    )

    # impbid: from s1 and s3, deduce the biconditional
    res = lb.ref(
        "res",
        "( ph -> ( ps <-> ( ph <-> ps ) ) )",
        s1,
        s3,
        ref="impbid",
        note="impbid",
    )

    return lb.build(res)


def prove_pm5_5(sys: System) -> Proof:
    """pm5.5: ( ph -> ( ( ph -> ps ) <-> ps ) ).

    From `biimt` and `bicomd`.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm5.5")

    # biimt: ( ph -> ( ps <-> ( ph -> ps ) ) )
    h1 = lb.ref(
        "h1",
        "( ph -> ( ps <-> ( ph -> ps ) ) )",
        ref="biimt",
        note="biimt",
    )

    # bicomd: from biimt, commute the biconditional
    res = lb.ref(
        "res",
        "( ph -> ( ( ph -> ps ) <-> ps ) )",
        h1,
        ref="bicomd",
        note="bicomd",
    )

    return lb.build(res)


def prove_pm5_4(sys: System) -> Proof:
    """pm5.4: ( ( ph -> ( ph -> ps ) ) <-> ( ph -> ps ) ).

    From pm5.5 and pm5.74i.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm5.4")

    # pm5.5: ( ph -> ( ( ph -> ps ) <-> ps ) )
    h1 = lb.ref(
        "h1",
        "( ph -> ( ( ph -> ps ) <-> ps ) )",
        ref="pm5.5",
        note="pm5.5",
    )

    # pm5.74i: from h1, deduce ( ( ph -> ( ph -> ps ) ) <-> ( ph -> ps ) )
    res = lb.ref(
        "res",
        "( ( ph -> ( ph -> ps ) ) <-> ( ph -> ps ) )",
        h1,
        ref="pm5.74i",
        note="pm5.74i",
    )

    return lb.build(res)


def prove_pm5_41(sys: System) -> Proof:
    """pm5.41: ( ( ( ph -> ps ) -> ( ph -> ch ) ) <-> ( ph -> ( ps -> ch ) ) ).

    Commuted form of imdi.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm5.41")

    # imdi: ( ( ph -> ( ps -> ch ) ) <-> ( ( ph -> ps ) -> ( ph -> ch ) ) )
    s1 = lb.ref(
        "s1",
        "( ( ph -> ( ps -> ch ) ) <-> ( ( ph -> ps ) -> ( ph -> ch ) ) )",
        ref="imdi",
        note="imdi",
    )

    # bicomi: commute the biconditional
    res = lb.ref(
        "res",
        "( ( ( ph -> ps ) -> ( ph -> ch ) ) <-> ( ph -> ( ps -> ch ) ) )",
        s1,
        ref="bicomi",
        note="bicomi",
    )

    return lb.build(res)


def prove_impbid(sys: System) -> Proof:
    """impbid: ( ph -> ( ps <-> ch ) ).

    Deduce a biconditional from both directions of an implication
    with a common antecedent.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "impbid")

    h1 = lb.hyp("impbid.1", "( ph -> ( ps -> ch ) )")
    h2 = lb.hyp("impbid.2", "( ph -> ( ch -> ps ) )")

    # impbid21d with ps→ph, th→ch gives: ( ph -> ( ph -> ( ps <-> ch ) ) )
    s1 = lb.ref(
        "s1",
        "( ph -> ( ph -> ( ps <-> ch ) ) )",
        h1,
        h2,
        ref="impbid21d",
        note="impbid21d",
    )

    # pm2.43i collapses the duplicate antecedent
    res = lb.ref(
        "res",
        "( ph -> ( ps <-> ch ) )",
        s1,
        ref="pm2.43i",
        note="pm2.43i",
    )

    return lb.build(res)


def prove_bibiad(sys: System) -> Proof:
    """bibiad: φ → (ψ ↔ χ).

    Eliminate a hypothesis θ in a biconditional.
    (Contributed by Thierry Arnoux, 4-May-2025.)
    """
    lb = ProofBuilder(sys, "bibiad")

    h1 = lb.hyp("bibiad.1", "( ( φ ∧ ψ ) → θ )")
    h2 = lb.hyp("bibiad.2", "( ( φ ∧ χ ) → θ )")
    h3 = lb.hyp("bibiad.3", "( ( φ ∧ θ ) → ( ψ ↔ χ ) )")

    # biimpa with bibiad.3 → ( ( ( φ ∧ θ ) ∧ ψ ) → χ )
    s_biimpa = lb.ref(
        "s_biimpa",
        "( ( ( φ ∧ θ ) ∧ ψ ) → χ )",
        h3,
        ref="biimpa",
        note="biimpa",
    )

    # simpl → ( ( φ ∧ ψ ) → φ )
    s_simpl_ps = lb.ref(
        "s_simpl_ps",
        "( ( φ ∧ ψ ) → φ )",
        ref="simpl",
        note="simpl",
    )

    # simpr → ( ( φ ∧ ψ ) → ψ )
    s_simpr_ps = lb.ref(
        "s_simpr_ps",
        "( ( φ ∧ ψ ) → ψ )",
        ref="simpr",
        note="simpr",
    )

    # syl21anc simpl, bibiad.1, simpr, s_biimpa → ( ( φ ∧ ψ ) → χ )
    s_left = lb.ref(
        "s_left",
        "( ( φ ∧ ψ ) → χ )",
        s_simpl_ps,
        h1,
        s_simpr_ps,
        s_biimpa,
        ref="syl21anc",
        note="syl21anc",
    )

    # simpl → ( ( φ ∧ χ ) → φ )
    s_simpl_ch = lb.ref(
        "s_simpl_ch",
        "( ( φ ∧ χ ) → φ )",
        ref="simpl",
        note="simpl",
    )

    # simpr → ( ( φ ∧ χ ) → χ )
    s_simpr_ch = lb.ref(
        "s_simpr_ch",
        "( ( φ ∧ χ ) → χ )",
        ref="simpr",
        note="simpr",
    )

    # biimpar with bibiad.3 → ( ( ( φ ∧ θ ) ∧ χ ) → ψ )
    s_biimpar = lb.ref(
        "s_biimpar",
        "( ( ( φ ∧ θ ) ∧ χ ) → ψ )",
        h3,
        ref="biimpar",
        note="biimpar",
    )

    # syl21anc simpl, bibiad.2, simpr, s_biimpar → ( ( φ ∧ χ ) → ψ )
    s_right = lb.ref(
        "s_right",
        "( ( φ ∧ χ ) → ψ )",
        s_simpl_ch,
        h2,
        s_simpr_ch,
        s_biimpar,
        ref="syl21anc",
        note="syl21anc",
    )

    # impbida s_left, s_right → ( φ → ( ψ ↔ χ ) )
    res = lb.ref(
        "res",
        "( φ → ( ψ ↔ χ ) )",
        s_left,
        s_right,
        ref="impbida",
        note="impbida",
    )

    return lb.build(res)


def prove_impbida(sys: System) -> Proof:
    """impbida: ( ph -> ( ps <-> ch ) ).

    Deduction form of impbid: from two conjunctions with a common
    antecedent implying each side of a biconditional, deduce the
    biconditional.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "impbida")

    h1 = lb.hyp("impbida.1", "( ( ph /\\ ps ) -> ch )")
    h2 = lb.hyp("impbida.2", "( ( ph /\\ ch ) -> ps )")

    # ex: ( ( ph /\ ps ) -> ch )  =>  ( ph -> ( ps -> ch ) )
    s1 = lb.ref(
        "s1",
        "( ph -> ( ps -> ch ) )",
        h1,
        ref="ex",
        note="ex",
    )

    # ex: ( ( ph /\ ch ) -> ps )  =>  ( ph -> ( ch -> ps ) )
    s2 = lb.ref(
        "s2",
        "( ph -> ( ch -> ps ) )",
        h2,
        ref="ex",
        note="ex",
    )

    # impbid combines both directions
    res = lb.ref(
        "res",
        "( ph -> ( ps <-> ch ) )",
        s1,
        s2,
        ref="impbid",
        note="impbid",
    )

    return lb.build(res)


def prove_impbid1(sys: System) -> Proof:
    """impbid1: ( ph -> ( ps <-> ch ) ).

    Deduce a biconditional from an implication with a common antecedent
    and its converse.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "impbid1")

    h1 = lb.hyp("impbid1.1", "( ph -> ( ps -> ch ) )")
    h2 = lb.hyp("impbid1.2", "( ch -> ps )")

    s1 = lb.ref(
        "s1",
        "( ph -> ( ch -> ps ) )",
        h2,
        ref="a1i",
        note="a1i on impbid1.2",
    )

    res = lb.ref(
        "res",
        "( ph -> ( ps <-> ch ) )",
        h1,
        s1,
        ref="impbid",
        note="impbid",
    )

    return lb.build(res)


def prove_impbid2(sys: System) -> Proof:
    """impbid2: ( ph -> ( ps <-> ch ) ).

    Deduce a biconditional from an implication and a reversed
    implication with a common antecedent.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "impbid2")

    h1 = lb.hyp("impbid2.1", "( ps -> ch )")
    h2 = lb.hyp("impbid2.2", "( ph -> ( ch -> ps ) )")

    # impbid1 with swapped variables: ( ph -> ( ch <-> ps ) )
    s1 = lb.ref(
        "s1",
        "( ph -> ( ch <-> ps ) )",
        h2,
        h1,
        ref="impbid1",
        note="impbid1",
    )

    # bicomd: ( ph -> ( ps <-> ch ) )
    res = lb.ref(
        "res",
        "( ph -> ( ps <-> ch ) )",
        s1,
        ref="bicomd",
        note="bicomd",
    )

    return lb.build(res)


def prove_impcon4bid(sys: System) -> Proof:
    """impcon4bid: ( ph -> ( ps <-> ch ) ).

    Deduce a biconditional from an implication and its contrapositive.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "impcon4bid")

    h1 = lb.hyp("impcon4bid.1", "( ph -> ( ps -> ch ) )")
    h2 = lb.hyp("impcon4bid.2", "( ph -> ( -. ps -> -. ch ) )")

    # con4d: ( ph -> ( -. ps -> -. ch ) ) -> ( ph -> ( ch -> ps ) )
    s1 = lb.ref(
        "s1",
        "( ph -> ( ch -> ps ) )",
        h2,
        ref="con4d",
        note="con4d",
    )

    # impbid: from ( ph -> ( ps -> ch ) ) and ( ph -> ( ch -> ps ) )
    # deduce ( ph -> ( ps <-> ch ) )
    res = lb.ref(
        "res",
        "( ph -> ( ps <-> ch ) )",
        h1,
        s1,
        ref="impbid",
        note="impbid",
    )

    return lb.build(res)


def prove_con4bid(sys: System) -> Proof:
    """con4bid: ( ph -> ( ps <-> ch ) ).

    Deduce a biconditional from a biconditional of negations.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "con4bid")

    h1 = lb.hyp("con4bid.1", "( ph -> ( -. ps <-> -. ch ) )")

    # biimpd: from the biconditional of negations, deduce the forward
    # implication of negations
    s1 = lb.ref(
        "s1",
        "( ph -> ( -. ps -> -. ch ) )",
        h1,
        ref="biimpd",
        note="biimpd",
    )

    # biimprd: from the biconditional of negations, deduce the reverse
    # implication of negations
    s2 = lb.ref(
        "s2",
        "( ph -> ( -. ch -> -. ps ) )",
        h1,
        ref="biimprd",
        note="biimprd",
    )

    # con4d: contraposition on the reverse direction gives ( ps -> ch )
    s3 = lb.ref(
        "s3",
        "( ph -> ( ps -> ch ) )",
        s2,
        ref="con4d",
        note="con4d",
    )

    # impcon4bid: combine the two implications into a biconditional
    res = lb.ref(
        "res",
        "( ph -> ( ps <-> ch ) )",
        s3,
        s1,
        ref="impcon4bid",
        note="impcon4bid",
    )

    return lb.build(res)


def prove_con4bii(sys: System) -> Proof:
    """con4bii: ( φ ↔ ψ ).

    Infer a biconditional from a biconditional of negations.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "con4bii")
    h1 = lb.hyp("con4bii.1", "( ¬ φ ↔ ¬ ψ )")

    # notbi: ( ( φ ↔ ψ ) ↔ ( ¬ φ ↔ ¬ ψ ) )
    s1 = lb.ref("s1", "( ( φ ↔ ψ ) ↔ ( ¬ φ ↔ ¬ ψ ) )", ref="notbi", note="notbi")

    # mpbir: from the biconditional and the RHS, deduce the LHS
    res = lb.ref("res", "( φ ↔ ψ )", h1, s1, ref="mpbir", note="mpbir")

    return lb.build(res)


def prove_pm5_74(sys: System) -> Proof:
    """pm5.74: ( ph -> ( ps <-> ch ) ) <-> ( ( ph -> ps ) <-> ( ph -> ch ) ).

    Distribution of implication over biconditional.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm5.74")

    # biimp and biimpr as base theorems
    biimp_th = lb.ref(
        "biimp_th",
        "( ( ps <-> ch ) -> ( ps -> ch ) )",
        ref="biimp",
        note="biimp",
    )
    biimpr_th = lb.ref(
        "biimpr_th",
        "( ( ps <-> ch ) -> ( ch -> ps ) )",
        ref="biimpr",
        note="biimpr",
    )

    # imim3i from biimp: (ph -> (ps <-> ch)) -> ((ph -> ps) -> (ph -> ch))
    fwd1 = lb.ref(
        "fwd1",
        "( ( ph -> ( ps <-> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) )",
        biimp_th,
        ref="imim3i",
        note="imim3i",
    )

    # imim3i from biimpr: (ph -> (ps <-> ch)) -> ((ph -> ch) -> (ph -> ps))
    fwd2 = lb.ref(
        "fwd2",
        "( ( ph -> ( ps <-> ch ) ) -> ( ( ph -> ch ) -> ( ph -> ps ) ) )",
        biimpr_th,
        ref="imim3i",
        note="imim3i",
    )

    # impbid: (ph -> (ps <-> ch)) -> ((ph -> ps) <-> (ph -> ch))
    forward = lb.ref(
        "forward",
        "( ( ph -> ( ps <-> ch ) ) -> ( ( ph -> ps ) <-> ( ph -> ch ) ) )",
        fwd1,
        fwd2,
        ref="impbid",
        note="impbid",
    )

    # biimp of outer biconditional
    biimp_outer = lb.ref(
        "biimp_outer",
        "( ( ( ph -> ps ) <-> ( ph -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) )",
        ref="biimp",
        note="biimp",
    )

    # biimpr of outer biconditional
    biimpr_outer = lb.ref(
        "biimpr_outer",
        "( ( ( ph -> ps ) <-> ( ph -> ch ) ) -> ( ( ph -> ch ) -> ( ph -> ps ) ) )",
        ref="biimpr",
        note="biimpr",
    )

    # pm2.86d on biimp_outer
    bwd1 = lb.ref(
        "bwd1",
        "( ( ( ph -> ps ) <-> ( ph -> ch ) ) -> ( ph -> ( ps -> ch ) ) )",
        biimp_outer,
        ref="pm2.86d",
        note="pm2.86d",
    )

    # pm2.86d on biimpr_outer
    bwd2 = lb.ref(
        "bwd2",
        "( ( ( ph -> ps ) <-> ( ph -> ch ) ) -> ( ph -> ( ch -> ps ) ) )",
        biimpr_outer,
        ref="pm2.86d",
        note="pm2.86d",
    )

    # impbidd: ((ph -> ps) <-> (ph -> ch)) -> (ph -> (ps <-> ch))
    backward = lb.ref(
        "backward",
        "( ( ( ph -> ps ) <-> ( ph -> ch ) ) -> ( ph -> ( ps <-> ch ) ) )",
        bwd1,
        bwd2,
        ref="impbidd",
        note="impbidd",
    )

    # impbii: combine forward and backward
    res = lb.ref(
        "res",
        "( ( ph -> ( ps <-> ch ) ) <-> ( ( ph -> ps ) <-> ( ph -> ch ) ) )",
        forward,
        backward,
        ref="impbii",
        note="impbii",
    )

    return lb.build(res)

    return lb.build(res)


def prove_pm5_74d(sys: System) -> Proof:
    """pm5.74d: ( ph -> ( ( ps -> ch ) <-> ( ps -> th ) ) ).

    Deduction form of pm5.74.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm5.74d")
    h1 = lb.hyp("pm5.74d.1", "( ph -> ( ps -> ( ch <-> th ) ) )")

    # pm5.74: ( ps -> ( ch <-> th ) ) <-> ( ( ps -> ch ) <-> ( ps -> th ) )
    pm5_74_th = lb.ref(
        "pm5_74_th",
        "( ( ps -> ( ch <-> th ) ) <-> ( ( ps -> ch ) <-> ( ps -> th ) ) )",
        ref="pm5.74",
        note="pm5.74",
    )

    # sylib combines the hypothesis with pm5.74
    res = lb.ref(
        "res",
        "( ph -> ( ( ps -> ch ) <-> ( ps -> th ) ) )",
        h1,
        pm5_74_th,
        ref="sylib",
        note="sylib",
    )

    return lb.build(res)


def prove_pm5_74da(sys: System) -> Proof:
    """pm5.74da: ( ph -> ( ( ps -> ch ) <-> ( ps -> th ) ) ).

    Deduction form of pm5.74 with a conjunction antecedent.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm5.74da")
    h1 = lb.hyp("pm5.74da.1", "( ( ph /\\ ps ) -> ( ch <-> th ) )")

    # ex: ( ( ph /\ ps ) -> ( ch <-> th ) ) -> ( ph -> ( ps -> ( ch <-> th ) ) )
    h1_ex = lb.ref(
        "h1_ex",
        "( ph -> ( ps -> ( ch <-> th ) ) )",
        h1,
        ref="ex",
        note="ex",
    )

    # pm5.74d: ( ph -> ( ps -> ( ch <-> th ) ) ) ->
    #          ( ph -> ( ( ps -> ch ) <-> ( ps -> th ) ) )
    res = lb.ref(
        "res",
        "( ph -> ( ( ps -> ch ) <-> ( ps -> th ) ) )",
        h1_ex,
        ref="pm5.74d",
        note="pm5.74d",
    )

    return lb.build(res)


def prove_pm5_74rd(sys: System) -> Proof:
    """pm5.74rd: ( ph -> ( ps -> ( ch <-> th ) ) ).

    Reverse deduction form of pm5.74.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm5.74rd")
    h1 = lb.hyp(
        "pm5.74rd.1",
        "( ph -> ( ( ps -> ch ) <-> ( ps -> th ) ) )",
    )

    # pm5.74: ( ps -> ( ch <-> th ) ) <-> ( ( ps -> ch ) <-> ( ps -> th ) )
    pm5_74_th = lb.ref(
        "pm5_74_th",
        "( ( ps -> ( ch <-> th ) ) <-> ( ( ps -> ch ) <-> ( ps -> th ) ) )",
        ref="pm5.74",
        note="pm5.74",
    )

    # sylibr combines the hypothesis with pm5.74
    res = lb.ref(
        "res",
        "( ph -> ( ps -> ( ch <-> th ) ) )",
        h1,
        pm5_74_th,
        ref="sylibr",
        note="sylibr",
    )

    return lb.build(res)


def prove_pm5_74i(sys: System) -> Proof:
    """pm5.74i: ( ( ph -> ps ) <-> ( ph -> ch ) ).

    Inference form of pm5.74.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm5.74i")
    h1 = lb.hyp("pm5.74i.1", "( ph -> ( ps <-> ch ) )")

    # pm5.74: ( ( ph -> ( ps <-> ch ) ) <-> ( ( ph -> ps ) <-> ( ph -> ch ) ) )
    pm5_74_th = lb.ref(
        "pm5_74_th",
        "( ( ph -> ( ps <-> ch ) ) <-> ( ( ph -> ps ) <-> ( ph -> ch ) ) )",
        ref="pm5.74",
        note="pm5.74",
    )

    # mpbi: from the LHS of the biconditional, deduce the RHS
    res = lb.ref(
        "res",
        "( ( ph -> ps ) <-> ( ph -> ch ) )",
        h1,
        pm5_74_th,
        ref="mpbi",
        note="mpbi",
    )

    return lb.build(res)


def prove_pm5_74ri(sys: System) -> Proof:
    """pm5.74ri: ( ph -> ( ps <-> ch ) ).

    Inference form of pm5.74.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm5.74ri")
    h1 = lb.hyp("pm5.74ri.1", "( ( ph -> ps ) <-> ( ph -> ch ) )")

    # pm5.74: ( ( ph -> ( ps <-> ch ) ) <-> ( ( ph -> ps ) <-> ( ph -> ch ) ) )
    pm5_74_th = lb.ref(
        "pm5_74_th",
        "( ( ph -> ( ps <-> ch ) ) <-> ( ( ph -> ps ) <-> ( ph -> ch ) ) )",
        ref="pm5.74",
        note="pm5.74",
    )

    # mpbir: from the biconditional and the RHS, deduce the LHS
    res = lb.ref(
        "res",
        "( ph -> ( ps <-> ch ) )",
        h1,
        pm5_74_th,
        ref="mpbir",
        note="mpbir",
    )

    return lb.build(res)


def prove_imbi2d(sys: System) -> Proof:
    """imbi2d: ( ph -> ( ( th -> ps ) <-> ( th -> ch ) ) ).

    Deduction form of imbi2.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "imbi2d")
    h1 = lb.hyp("imbi2d.1", "( ph -> ( ps <-> ch ) )")

    # a1d: ( ph -> ( ps <-> ch ) ) -> ( ph -> ( th -> ( ps <-> ch ) ) )
    s1 = lb.ref(
        "s1",
        "( ph -> ( th -> ( ps <-> ch ) ) )",
        h1,
        ref="a1d",
        note="a1d",
    )

    # pm5.74d transforms ( ph -> ( ps -> ( ch <-> th ) ) ) into
    # ( ph -> ( ( ps -> ch ) <-> ( ps -> th ) ) ).
    # With ps:=th, ch:=ps, th:=ch, this gives the desired conclusion.
    res = lb.ref(
        "res",
        "( ph -> ( ( th -> ps ) <-> ( th -> ch ) ) )",
        s1,
        ref="pm5.74d",
        note="pm5.74d",
    )

    return lb.build(res)


def prove_imbi1d(sys: System) -> Proof:
    """imbi1d: ( ph -> ( ( ps -> th ) <-> ( ch -> th ) ) ).

    Deduction form of imbi1: from a hypothesis that implies a
    biconditional, deduce that both sides imply the same consequent.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "imbi1d")
    h1 = lb.hyp("imbi1d.1", "( ph -> ( ps <-> ch ) )")

    # biimpd: ( ph -> ( ps <-> ch ) ) -> ( ph -> ( ps -> ch ) )
    s_biimpd = lb.ref(
        "s_biimpd",
        "( ph -> ( ps -> ch ) )",
        h1,
        ref="biimpd",
        note="biimpd",
    )

    # imim1d: ( ph -> ( ps -> ch ) ) -> ( ph -> ( ( ch -> th ) -> ( ps -> th ) ) )
    s_fwd = lb.ref(
        "s_fwd",
        "( ph -> ( ( ch -> th ) -> ( ps -> th ) ) )",
        s_biimpd,
        ref="imim1d",
        note="imim1d",
    )

    # biimprd: ( ph -> ( ps <-> ch ) ) -> ( ph -> ( ch -> ps ) )
    s_biimprd = lb.ref(
        "s_biimprd",
        "( ph -> ( ch -> ps ) )",
        h1,
        ref="biimprd",
        note="biimprd",
    )

    # imim1d: ( ph -> ( ch -> ps ) ) -> ( ph -> ( ( ps -> th ) -> ( ch -> th ) ) )
    s_rev = lb.ref(
        "s_rev",
        "( ph -> ( ( ps -> th ) -> ( ch -> th ) ) )",
        s_biimprd,
        ref="imim1d",
        note="imim1d",
    )

    # impbid: combine both directions into a biconditional
    res = lb.ref(
        "res",
        "( ph -> ( ( ps -> th ) <-> ( ch -> th ) ) )",
        s_rev,
        s_fwd,
        ref="impbid",
        note="impbid",
    )

    return lb.build(res)


def prove_imbi12d(sys: System) -> Proof:
    """imbi12d: ( ph -> ( ( ps -> th ) <-> ( ch -> ta ) ) ).

    Deduction form of imbi12: from two biconditional hypotheses, deduce
    that both antecedents and consequents can be correspondingly changed.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "imbi12d")
    h1 = lb.hyp("imbi12d.1", "( ph -> ( ps <-> ch ) )")
    h2 = lb.hyp("imbi12d.2", "( ph -> ( th <-> ta ) )")

    # imbi1d: ( ph -> ( ps <-> ch ) ) -> ( ph -> ( ( ps -> th ) <-> ( ch -> th ) ) )
    s1 = lb.ref(
        "s1",
        "( ph -> ( ( ps -> th ) <-> ( ch -> th ) ) )",
        h1,
        ref="imbi1d",
        note="imbi1d",
    )

    # imbi2d: ( ph -> ( th <-> ta ) ) -> ( ph -> ( ( ch -> th ) <-> ( ch -> ta ) ) )
    s2 = lb.ref(
        "s2",
        "( ph -> ( ( ch -> th ) <-> ( ch -> ta ) ) )",
        h2,
        ref="imbi2d",
        note="imbi2d",
    )

    # bitrd: combine both transformations
    res = lb.ref(
        "res",
        "( ph -> ( ( ps -> th ) <-> ( ch -> ta ) ) )",
        s1,
        s2,
        ref="bitrd",
        note="bitrd",
    )

    return lb.build(res)


def prove_imbi12(sys: System) -> Proof:
    """imbi12: ( ( ph <-> ps ) -> ( ( ch <-> th ) -> ( ( ph -> ch ) <-> ( ps -> th ) ) ) ).

    The biconditional implies equivalence of implications with both
    antecedents and consequents changed correspondingly.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "imbi12")

    # simplim: ¬ ( φ → ψ ) → φ
    # With φ = ( ph <-> ps ), ψ = ¬ ( ch <-> th )
    s1 = lb.ref(
        "s1",
        "¬ ( ( ph <-> ps ) -> ¬ ( ch <-> th ) ) -> ( ph <-> ps )",
        ref="simplim",
        note="simplim",
    )

    # simprim: ¬ ( φ → ¬ ψ ) → ψ
    # With φ = ( ph <-> ps ), ψ = ( ch <-> th )
    s2 = lb.ref(
        "s2",
        "¬ ( ( ph <-> ps ) -> ¬ ( ch <-> th ) ) -> ( ch <-> th )",
        ref="simprim",
        note="simprim",
    )

    # imbi12d with s1 and s2 as hypotheses
    s3 = lb.ref(
        "s3",
        "¬ ( ( ph <-> ps ) -> ¬ ( ch <-> th ) ) -> ( ( ph -> ch ) <-> ( ps -> th ) )",
        s1,
        s2,
        ref="imbi12d",
        note="imbi12d",
    )

    # expi: ( ¬ ( φ → ¬ ψ ) → χ ) → ( φ → ( ψ → χ ) )
    # With φ = ( ph <-> ps ), ψ = ( ch <-> th ),
    #      χ = ( ( ph -> ch ) <-> ( ps -> th ) )
    res = lb.ref(
        "res",
        "( ( ph <-> ps ) -> ( ( ch <-> th ) -> ( ( ph -> ch ) <-> ( ps -> th ) ) ) )",
        s3,
        ref="expi",
        note="expi",
    )

    return lb.build(res)


def prove_imbi12i(sys: System) -> Proof:
    """imbi12i: ( ( ph -> ch ) <-> ( ps -> th ) ).

    The biconditional implies equivalence of implications — inference form.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "imbi12i")
    h1 = lb.hyp("imbi12i.1", "( ph <-> ps )")
    h2 = lb.hyp("imbi12i.2", "( ch <-> th )")

    # imbi12: ( ( ph <-> ps ) -> ( ( ch <-> th ) -> ( ( ph -> ch ) <-> ( ps -> th ) ) ) )
    imbi12_ref = lb.ref(
        "imbi12_ref",
        "( ( ph <-> ps ) -> ( ( ch <-> th ) -> ( ( ph -> ch ) <-> ( ps -> th ) ) ) )",
        ref="imbi12",
        note="imbi12",
    )

    # mp2 with mp2.1=h1, mp2.2=h2, mp2.3=imbi12_ref
    res = lb.ref(
        "res",
        "( ( ph -> ch ) <-> ( ps -> th ) )",
        h1,
        h2,
        imbi12_ref,
        ref="mp2",
        note="mp2",
    )
    return lb.build(res)


def prove_imbi2(sys: System) -> Proof:
    """imbi2: ( ( ph <-> ps ) -> ( ( ch -> ph ) <-> ( ch -> ps ) ) ).

    The biconditional implies the same implication transformation.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "imbi2")
    s1 = lb.ref(
        "s1",
        "( ( ph <-> ps ) -> ( ph <-> ps ) )",
        ref="id",
        note="id",
    )
    res = lb.ref(
        "res",
        "( ( ph <-> ps ) -> ( ( ch -> ph ) <-> ( ch -> ps ) ) )",
        s1,
        ref="imbi2d",
        note="imbi2d",
    )
    return lb.build(res)


def prove_imbi2i(sys: System) -> Proof:
    """imbi2i: ( ( ch -> ph ) <-> ( ch -> ps ) ).

    Inference form of imbi2.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "imbi2i")
    h1 = lb.hyp("imbi2i.1", "( ph <-> ps )")

    # a1i: ( ch -> ( ph <-> ps ) )
    s1 = lb.ref("s1", "( ch -> ( ph <-> ps ) )", h1, ref="a1i", note="a1i")

    # pm5.74i: ( ( ch -> ph ) <-> ( ch -> ps ) )
    res = lb.ref(
        "res",
        "( ( ch -> ph ) <-> ( ch -> ps ) )",
        s1,
        ref="pm5.74i",
        note="pm5.74i",
    )

    return lb.build(res)


def prove_imbi1(sys: System) -> Proof:
    """imbi1: ( ( ph <-> ps ) -> ( ( ph -> ch ) <-> ( ps -> ch ) ) ).

    The biconditional implies the same consequent transformation.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "imbi1")
    s1 = lb.ref(
        "s1",
        "( ( ph <-> ps ) -> ( ph <-> ps ) )",
        ref="id",
        note="id",
    )
    res = lb.ref(
        "res",
        "( ( ph <-> ps ) -> ( ( ph -> ch ) <-> ( ps -> ch ) ) )",
        s1,
        ref="imbi1d",
        note="imbi1d",
    )
    return lb.build(res)


def prove_imbi1i(sys: System) -> Proof:
    """imbi1i: ( ( ph -> ch ) <-> ( ps -> ch ) ).

    Inference form of imbi1.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "imbi1i")
    h1 = lb.hyp("imbi1i.1", "( ph <-> ps )")
    s1 = lb.ref(
        "s1",
        "( ( ph <-> ps ) -> ( ( ph -> ch ) <-> ( ps -> ch ) ) )",
        ref="imbi1",
        note="imbi1",
    )
    res = lb.mp("res", h1, s1, "MP hyp1, imbi1")
    return lb.build(res)


def prove_dfbi1(sys: System) -> Proof:
    """dfbi1: ( φ <-> ψ ) <-> -. ( ( φ -> ψ ) -> -. ( ψ -> φ ) ).

    Relate the biconditional connective to primitive connectives.
    (Contributed by NM, 29-Dec-1992.)
    """
    lb = ProofBuilder(sys, "dfbi1")

    # Let A = ( φ <-> ψ )
    # Let notB = -. ( ( φ -> ψ ) -> -. ( ψ -> φ ) )
    # Then  C = ( A <-> notB ) is the goal
    #
    # impbi gives: ( A -> notB ) -> ( ( notB -> A ) -> ( A <-> notB ) )
    impbi_out = lb.ref(
        "impbi_out",
        "( ( φ ↔ ψ ) → ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) ) → "
        "( ( ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) → ( φ ↔ ψ ) ) → "
        "( ( φ ↔ ψ ) ↔ ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) ) )",
        ref="impbi",
        note="impbi",
    )

    # con3rr3 applied to impbi:
    # ¬ C → ( ( A → notB ) → ¬ ( notB → A ) )
    con3rr3_out = lb.ref(
        "con3rr3_out",
        "¬ ( ( φ ↔ ψ ) ↔ ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) ) → "
        "( ( ( φ ↔ ψ ) → ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) ) → "
        "¬ ( ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) → ( φ ↔ ψ ) ) )",
        impbi_out,
        ref="con3rr3",
        note="con3rr3",
    )

    # df-bi: ¬ ( ( A → notB ) → ¬ ( notB → A ) )
    dfbi = lb.ref(
        "dfbi",
        "¬ ( ( ( φ ↔ ψ ) → ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) ) → "
        "¬ ( ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) → ( φ ↔ ψ ) ) )",
        ref="df-bi",
        note="df-bi",
    )

    # mt3:
    #   mt3.1 = dfbi        = ¬ ( ( A → notB ) → ¬ ( notB → A ) )
    #   mt3.2 = con3rr3_out = ¬ C → ( ( A → notB ) → ¬ ( notB → A ) )
    #   conclusion = C
    res = lb.ref(
        "res",
        "( φ ↔ ψ ) ↔ ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) )",
        dfbi,
        con3rr3_out,
        ref="mt3",
        note="mt3",
    )

    return lb.build(res)


def prove_dfbi1ALT(sys: System) -> Proof:
    """dfbi1ALT: ( φ <-> ψ ) <-> -. ( ( φ -> ψ ) -> -. ( ψ -> φ ) ).

    Alternative definition of the biconditional: the biconditional is
    equivalent to the negation of one direction implying the negation
    of the other.  (Contributed by NM, 5-Aug-1993.)
    (Proof modification is discouraged.)  (New usage is discouraged.)
    """
    lb = ProofBuilder(sys, "dfbi1ALT")

    # Step 1: df-bi axiom
    # -.(((φ<->ψ)->-.((φ->ψ)->-.(ψ->φ)))->-.(-.((φ->ψ)->-.(ψ->φ))->(φ<->ψ)))
    dfbi = lb.ref(
        "dfbi",
        "¬ ( ( ( φ ↔ ψ ) → ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) ) → "
        "¬ ( ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) → ( φ ↔ ψ ) ) )",
        ref="df-bi",
        note="df-bi",
    )

    # Step 2: simplim applied to df-bi
    # simplim: ¬(A→B)→A
    # With A = ((φ↔ψ)→¬((φ→ψ)→¬(ψ→φ))), B = ¬(¬((φ→ψ)→¬(ψ→φ))→(φ↔ψ))
    s2 = lb.ref(
        "s2",
        "( ¬ ( ( ( φ ↔ ψ ) → ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) ) → "
        "¬ ( ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) → ( φ ↔ ψ ) ) ) ) → "
        "( ( φ ↔ ψ ) → ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) )",
        ref="simplim",
        note="simplim",
    )

    # Step 3: MP df-bi, simplim → (φ↔ψ) → ¬((φ→ψ)→¬(ψ→φ))  [dir1]
    s3 = lb.mp("s3", dfbi, s2, note="MP df-bi, simplim")

    # Step 4: simplim: ¬((φ→ψ)→¬(ψ→φ)) → (φ→ψ)
    s4 = lb.ref(
        "s4",
        "¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) → ( φ → ψ )",
        ref="simplim",
        note="simplim",
    )

    # Step 5: simprim: ¬((φ→ψ)→¬(ψ→φ)) → (ψ→φ)
    s5 = lb.ref(
        "s5",
        "¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) → ( ψ → φ )",
        ref="simprim",
        note="simprim",
    )

    # Step 6: impbi: (φ→ψ) → ((ψ→φ) → (φ↔ψ))
    s6 = lb.ref(
        "s6",
        "( φ → ψ ) → ( ( ψ → φ ) → ( φ ↔ ψ ) )",
        ref="impbi",
        note="impbi",
    )

    # Step 7: sylc with s4, s5, s6 → ¬((φ→ψ)→¬(ψ→φ)) → (φ↔ψ)  [dir2]
    s7 = lb.ref(
        "s7",
        "¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) → ( φ ↔ ψ )",
        s4,
        s5,
        s6,
        ref="sylc",
        note="sylc",
    )

    # Step 8: impbi with biconditional: (A→B)→((B→A)→(A↔B))
    # where A = (φ↔ψ), B = ¬((φ→ψ)→¬(ψ→φ))
    s8 = lb.ref(
        "s8",
        "( ( φ ↔ ψ ) → ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) ) → "
        "( ( ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) → ( φ ↔ ψ ) ) → "
        "( ( φ ↔ ψ ) ↔ ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) ) )",
        ref="impbi",
        note="impbi",
    )

    # Step 9: mp2 with s3, s7, s8 → (φ↔ψ) ↔ ¬((φ→ψ)→¬(ψ→φ))
    res = lb.ref(
        "res",
        "( φ ↔ ψ ) ↔ ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) )",
        s3,
        s7,
        s8,
        ref="mp2",
        note="mp2",
    )

    return lb.build(res)


def prove_bitri(sys: System) -> Proof:
    """bitri: ( ph <-> ch ).

    Transitivity of biconditional: from two biconditionals, deduce a new
    biconditional linking the two outer propositions.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "bitri")

    h1 = lb.hyp("bitri.1", "( ph <-> ps )")
    h2 = lb.hyp("bitri.2", "( ps <-> ch )")

    # sylbb: ( ph <-> ps ) , ( ps <-> ch ) |- ( ph -> ch )
    s1 = lb.ref("s1", "( ph -> ch )", h1, h2, ref="sylbb", note="sylbb")

    # sylbbr: ( ph <-> ps ) , ( ps <-> ch ) |- ( ch -> ph )
    s2 = lb.ref("s2", "( ch -> ph )", h1, h2, ref="sylbbr", note="sylbbr")

    # impbii: ( ph -> ch ) , ( ch -> ph ) |- ( ph <-> ch )
    res = lb.ref("res", "( ph <-> ch )", s1, s2, ref="impbii", note="impbii")

    return lb.build(res)


def prove_bitr2i(sys: System) -> Proof:
    """bitr2i: ( ch <-> ph ).

    An inference from transitive law for equivalence.  ( ph <-> ps ) and
    ( ps <-> ch ) imply ( ch <-> ph ).
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "bitr2i")

    h1 = lb.hyp("bitr2i.1", "( ph <-> ps )")
    h2 = lb.hyp("bitr2i.2", "( ps <-> ch )")

    # bitri: ( ph <-> ps ), ( ps <-> ch ) |- ( ph <-> ch )
    s1 = lb.ref("s1", "( ph <-> ch )", h1, h2, ref="bitri", note="bitri")

    # bicomi: ( ph <-> ch ) |- ( ch <-> ph )
    res = lb.ref("res", "( ch <-> ph )", s1, ref="bicomi", note="bicomi")

    return lb.build(res)


def prove_bitr3i(sys: System) -> Proof:
    """bitr3i: ( ph <-> ch ).

    An inference from transitive law for equivalence.  ( ps <-> ph ) and
    ( ps <-> ch ) imply ( ph <-> ch ).
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "bitr3i")

    h1 = lb.hyp("bitr3i.1", "( ps <-> ph )")
    h2 = lb.hyp("bitr3i.2", "( ps <-> ch )")

    # bicomi: ( ps <-> ph ) |- ( ph <-> ps )
    s1 = lb.ref("s1", "( ph <-> ps )", h1, ref="bicomi", note="bicomi")

    # bitri: ( ph <-> ps ), ( ps <-> ch ) |- ( ph <-> ch )
    res = lb.ref("res", "( ph <-> ch )", s1, h2, ref="bitri", note="bitri")

    return lb.build(res)


def prove_bitr4i(sys: System) -> Proof:
    """bitr4i: ( ph <-> ch ).

    An inference from transitive law for equivalence: ( ph <-> ps ) and
    ( ch <-> ps ) imply ( ph <-> ch ).
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "bitr4i")

    h1 = lb.hyp("bitr4i.1", "( ph <-> ps )")
    h2 = lb.hyp("bitr4i.2", "( ch <-> ps )")

    # bicomi: ( ch <-> ps ) -> ( ps <-> ch )
    s1 = lb.ref("s1", "( ps <-> ch )", h2, ref="bicomi", note="bicomi")

    # bitri: ( ph <-> ps ), ( ps <-> ch ) -> ( ph <-> ch )
    res = lb.ref("res", "( ph <-> ch )", h1, s1, ref="bitri", note="bitri")

    return lb.build(res)


def prove_bitrd(sys: System) -> Proof:
    """bitrd: ( ph -> ( ps <-> th ) ).

    Deduction form of bitri.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "bitrd")

    h1 = lb.hyp("bitrd.1", "( ph -> ( ps <-> ch ) )")
    h2 = lb.hyp("bitrd.2", "( ph -> ( ch <-> th ) )")

    # pm5.74i: ( ph -> ( ps <-> ch ) ) |- ( ( ph -> ps ) <-> ( ph -> ch ) )
    s1 = lb.ref("s1", "( ( ph -> ps ) <-> ( ph -> ch ) )", h1, ref="pm5.74i", note="pm5.74i")

    # pm5.74i: ( ph -> ( ch <-> th ) ) |- ( ( ph -> ch ) <-> ( ph -> th ) )
    s2 = lb.ref("s2", "( ( ph -> ch ) <-> ( ph -> th ) )", h2, ref="pm5.74i", note="pm5.74i")

    # bitri: ( ( ph -> ps ) <-> ( ph -> ch ) ) , ( ( ph -> ch ) <-> ( ph -> th ) )
    # |- ( ( ph -> ps ) <-> ( ph -> th ) )
    s3 = lb.ref(
        "s3",
        "( ( ph -> ps ) <-> ( ph -> th ) )",
        s1,
        s2,
        ref="bitri",
        note="bitri",
    )

    # pm5.74ri: ( ( ph -> ps ) <-> ( ph -> th ) ) |- ( ph -> ( ps <-> th ) )
    res = lb.ref(
        "res",
        "( ph -> ( ps <-> th ) )",
        s3,
        ref="pm5.74ri",
        note="pm5.74ri",
    )

    return lb.build(res)


def prove_bitrdi(sys: System) -> Proof:
    """bitrdi: ( ph -> ( ps <-> th ) ).

    Inference form of bitrd.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "bitrdi")

    h1 = lb.hyp("bitrdi.1", "( ph -> ( ps <-> ch ) )")
    h2 = lb.hyp("bitrdi.2", "( ch <-> th )")

    # a1i: ( ch <-> th ) |- ( ph -> ( ch <-> th ) )
    s1 = lb.ref("s1", "( ph -> ( ch <-> th ) )", h2, ref="a1i", note="a1i bitrdi.2")

    # bitrd: ( ph -> ( ps <-> ch ) ), ( ph -> ( ch <-> th ) )
    # |- ( ph -> ( ps <-> th ) )
    res = lb.ref(
        "res",
        "( ph -> ( ps <-> th ) )",
        h1,
        s1,
        ref="bitrd",
        note="bitrd",
    )

    return lb.build(res)


def prove_bitrid(sys: System) -> Proof:
    """bitrid: ( ch -> ( ph <-> th ) ).

    Deduction form of bitr.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "bitrid")

    h1 = lb.hyp("bitrid.1", "( ph <-> ps )")
    h2 = lb.hyp("bitrid.2", "( ch -> ( ps <-> th ) )")

    # a1i: ( ph <-> ps ) |- ( ch -> ( ph <-> ps ) )
    s1 = lb.ref("s1", "( ch -> ( ph <-> ps ) )", h1, ref="a1i", note="a1i")

    # bitrd: ( ch -> ( ph <-> ps ) ), ( ch -> ( ps <-> th ) )
    # |- ( ch -> ( ph <-> th ) )
    res = lb.ref(
        "res",
        "( ch -> ( ph <-> th ) )",
        s1,
        h2,
        ref="bitrd",
        note="bitrd",
    )

    return lb.build(res)


def prove_bitr2id(sys: System) -> Proof:
    """bitr2id: ( ch -> ( th <-> ph ) ).

    Deduction form of bitr2.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "bitr2id")

    h1 = lb.hyp("bitr2id.1", "( ph <-> ps )")
    h2 = lb.hyp("bitr2id.2", "( ch -> ( ps <-> th ) )")

    # bitrid: ( ph <-> ps ), ( ch -> ( ps <-> th ) ) |- ( ch -> ( ph <-> th ) )
    s1 = lb.ref(
        "s1",
        "( ch -> ( ph <-> th ) )",
        h1,
        h2,
        ref="bitrid",
        note="bitrid",
    )

    # bicomd: ( ch -> ( ph <-> th ) ) |- ( ch -> ( th <-> ph ) )
    res = lb.ref(
        "res",
        "( ch -> ( th <-> ph ) )",
        s1,
        ref="bicomd",
        note="bicomd",
    )

    return lb.build(res)


def prove_bitr3id(sys: System) -> Proof:
    """bitr3id: ( χ → ( φ ↔ θ ) ).

    Deduction form of bitr3.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "bitr3id")

    h1 = lb.hyp("bitr3id.1", "( ψ ↔ φ )")
    h2 = lb.hyp("bitr3id.2", "( χ → ( ψ ↔ θ ) )")

    # bicomi: ( ψ ↔ φ ) |- ( φ ↔ ψ )
    s1 = lb.ref("s1", "( φ ↔ ψ )", h1, ref="bicomi", note="bicomi")

    # bitrid: ( φ ↔ ψ ), ( χ → ( ψ ↔ θ ) ) |- ( χ → ( φ ↔ θ ) )
    res = lb.ref("res", "( χ → ( φ ↔ θ ) )", s1, h2, ref="bitrid", note="bitrid")

    return lb.build(res)


def prove_bitr2di(sys: System) -> Proof:
    """bitr2di: ( ph -> ( th <-> ps ) ).

    Inference form of bitr2d.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "bitr2di")

    h1 = lb.hyp("bitr2di.1", "( ph -> ( ps <-> ch ) )")
    h2 = lb.hyp("bitr2di.2", "( ch <-> th )")

    # bitrdi: ( ph -> ( ps <-> ch ) ), ( ch <-> th ) |- ( ph -> ( ps <-> th ) )
    s1 = lb.ref(
        "s1",
        "( ph -> ( ps <-> th ) )",
        h1,
        h2,
        ref="bitrdi",
        note="bitrdi",
    )

    # bicomd: ( ph -> ( ps <-> th ) ) |- ( ph -> ( th <-> ps ) )
    res = lb.ref(
        "res",
        "( ph -> ( th <-> ps ) )",
        s1,
        ref="bicomd",
        note="bicomd",
    )

    return lb.build(res)


def prove_bitr3di(sys: System) -> Proof:
    """bitr3di: ( ph -> ( ch <-> th ) ).

    Inference form of bitr3d.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "bitr3di")

    h1 = lb.hyp("bitr3di.1", "( ph -> ( ps <-> ch ) )")
    h2 = lb.hyp("bitr3di.2", "( ps <-> th )")

    # bicomi: ( ps <-> th ) |- ( th <-> ps )
    s1 = lb.ref(
        "s1",
        "( th <-> ps )",
        h2,
        ref="bicomi",
        note="bicomi",
    )

    # bitr2id: ( th <-> ps ), ( ph -> ( ps <-> ch ) )
    # |- ( ph -> ( ch <-> th ) )
    res = lb.ref(
        "res",
        "( ph -> ( ch <-> th ) )",
        s1,
        h1,
        ref="bitr2id",
        note="bitr2id",
    )

    return lb.build(res)


def prove_bitr4di(sys: System) -> Proof:
    """bitr4di: ( ph -> ( ps <-> th ) ).

    Inference form of bitr4d.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "bitr4di")

    h1 = lb.hyp("bitr4di.1", "( ph -> ( ps <-> ch ) )")
    h2 = lb.hyp("bitr4di.2", "( th <-> ch )")

    # bicomi: ( th <-> ch ) |- ( ch <-> th )
    s1 = lb.ref(
        "s1",
        "( ch <-> th )",
        h2,
        ref="bicomi",
        note="bicomi",
    )

    # bitrdi: ( ph -> ( ps <-> ch ) ), ( ch <-> th )
    # |- ( ph -> ( ps <-> th ) )
    res = lb.ref(
        "res",
        "( ph -> ( ps <-> th ) )",
        h1,
        s1,
        ref="bitrdi",
        note="bitrdi",
    )

    return lb.build(res)


def prove_bibi2i(sys: System) -> Proof:
    """bibi2i: ( ( ch <-> ph ) <-> ( ch <-> ps ) ).

    Inference form: from ( ph <-> ps ), deduce the biconditional is
    preserved under a common conjunct.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "bibi2i")
    h1 = lb.hyp("bibi2i.1", "( ph <-> ps )")

    # id: ( ( ch <-> ph ) -> ( ch <-> ph ) )
    s1 = lb.ref(
        "s1",
        "( ( ch <-> ph ) -> ( ch <-> ph ) )",
        ref="id",
        note="id",
    )

    # bitrdi: ( ( ch <-> ph ) -> ( ch <-> ph ) ), ( ph <-> ps )
    # |- ( ( ch <-> ph ) -> ( ch <-> ps ) )
    s2 = lb.ref(
        "s2",
        "( ( ch <-> ph ) -> ( ch <-> ps ) )",
        s1,
        h1,
        ref="bitrdi",
        note="bitrdi",
    )

    # id: ( ( ch <-> ps ) -> ( ch <-> ps ) )
    s3 = lb.ref(
        "s3",
        "( ( ch <-> ps ) -> ( ch <-> ps ) )",
        ref="id",
        note="id",
    )

    # bitr4di: ( ( ch <-> ps ) -> ( ch <-> ps ) ), ( ph <-> ps )
    # |- ( ( ch <-> ps ) -> ( ch <-> ph ) )
    s4 = lb.ref(
        "s4",
        "( ( ch <-> ps ) -> ( ch <-> ph ) )",
        s3,
        h1,
        ref="bitr4di",
        note="bitr4di",
    )

    # impbii: ( ( ch <-> ph ) -> ( ch <-> ps ) ), ( ( ch <-> ps ) -> ( ch <-> ph ) )
    # |- ( ( ch <-> ph ) <-> ( ch <-> ps ) )
    res = lb.ref(
        "res",
        "( ( ch <-> ph ) <-> ( ch <-> ps ) )",
        s2,
        s4,
        ref="impbii",
        note="impbii",
    )

    return lb.build(res)

    return lb.build(res)


def prove_bibi2d(sys: System) -> Proof:
    """bibi2d: ( ph -> ( ( th <-> ps ) <-> ( th <-> ch ) ) ).

    Deduction form of bibi2i: adding a biconditional to the right
    in an equivalence.
    (Contributed by NM, 11-May-1993.)
    """
    lb = ProofBuilder(sys, "bibi2d")
    h1 = lb.hyp("bibi2d.1", "( ph -> ( ps <-> ch ) )")

    # pm5.74i: ( ph -> ( ps <-> ch ) ) -> ( ( ph -> ps ) <-> ( ph -> ch ) )
    s1 = lb.ref(
        "s1",
        "( ( ph -> ps ) <-> ( ph -> ch ) )",
        h1,
        ref="pm5.74i",
        note="pm5.74i",
    )

    # bibi2i: ( ( ph -> ps ) <-> ( ph -> ch ) ) ->
    #         ( ( ( ph -> th ) <-> ( ph -> ps ) ) <-> ( ( ph -> th ) <-> ( ph -> ch ) ) )
    s2 = lb.ref(
        "s2",
        "( ( ( ph -> th ) <-> ( ph -> ps ) ) <-> ( ( ph -> th ) <-> ( ph -> ch ) ) )",
        s1,
        ref="bibi2i",
        note="bibi2i",
    )

    # pm5.74: ( ph -> ( th <-> ps ) ) <-> ( ( ph -> th ) <-> ( ph -> ps ) )
    s3 = lb.ref(
        "s3",
        "( ( ph -> ( th <-> ps ) ) <-> ( ( ph -> th ) <-> ( ph -> ps ) ) )",
        ref="pm5.74",
        note="pm5.74",
    )

    # pm5.74: ( ph -> ( th <-> ch ) ) <-> ( ( ph -> th ) <-> ( ph -> ch ) )
    s4 = lb.ref(
        "s4",
        "( ( ph -> ( th <-> ch ) ) <-> ( ( ph -> th ) <-> ( ph -> ch ) ) )",
        ref="pm5.74",
        note="pm5.74",
    )

    # 3bitr4i: combine s2, s3, s4 into the desired biconditional
    s5 = lb.ref(
        "s5",
        "( ( ph -> ( th <-> ps ) ) <-> ( ph -> ( th <-> ch ) ) )",
        s2,
        s3,
        s4,
        ref="3bitr4i",
        note="3bitr4i",
    )

    # pm5.74ri: convert biconditional of implications to implication of biconditional
    res = lb.ref(
        "res",
        "( ph -> ( ( th <-> ps ) <-> ( th <-> ch ) ) )",
        s5,
        ref="pm5.74ri",
        note="pm5.74ri",
    )

    return lb.build(res)


def prove_bibi1d(sys: System) -> Proof:
    """bibi1d: φ → ((ψ ↔ θ) ↔ (χ ↔ θ)).

    Deduction form of bibi1: adding a biconditional to the left
    in an equivalence.  (Contributed by NM, 11-May-1993.)
    """
    lb = ProofBuilder(sys, "bibi1d")
    h1 = lb.hyp("bibi1d.1", "( φ → ( ψ ↔ χ ) )")

    # bibi2d: ( φ → ( ψ ↔ χ ) ) |- ( φ → ( ( θ ↔ ψ ) ↔ ( θ ↔ χ ) ) )
    s1 = lb.ref(
        "s1",
        "( φ → ( ( θ ↔ ψ ) ↔ ( θ ↔ χ ) ) )",
        h1,
        ref="bibi2d",
        note="bibi2d",
    )

    # bicom: ( ( ψ ↔ θ ) ↔ ( θ ↔ ψ ) )
    s2 = lb.ref(
        "s2",
        "( ( ψ ↔ θ ) ↔ ( θ ↔ ψ ) )",
        ref="bicom",
        note="bicom",
    )

    # bicom: ( ( χ ↔ θ ) ↔ ( θ ↔ χ ) )
    s3 = lb.ref(
        "s3",
        "( ( χ ↔ θ ) ↔ ( θ ↔ χ ) )",
        ref="bicom",
        note="bicom",
    )

    # 3bitr4g: combine s1, s2, s3
    res = lb.ref(
        "res",
        "( φ → ( ( ψ ↔ θ ) ↔ ( χ ↔ θ ) ) )",
        s1,
        s2,
        s3,
        ref="3bitr4g",
        note="3bitr4g",
    )

    return lb.build(res)


def prove_bibi1(sys: System) -> Proof:
    """bibi1: ( φ ↔ ψ ) → ( ( φ ↔ χ ) ↔ ( ψ ↔ χ ) ).

    Adding a biconditional to the left in an equivalence.
    (Contributed by NM, 26-May-1993.)
    """
    lb = ProofBuilder(sys, "bibi1")

    # id: ( ( φ ↔ ψ ) → ( φ ↔ ψ ) )
    s1 = lb.ref(
        "s1",
        "( ( φ ↔ ψ ) → ( φ ↔ ψ ) )",
        ref="id",
        note="id",
    )

    # bibi1d: ( ( φ ↔ ψ ) → ( φ ↔ ψ ) ) → ( ( φ ↔ ψ ) → ( ( φ ↔ χ ) ↔ ( ψ ↔ χ ) ) )
    res = lb.ref(
        "res",
        "( ( φ ↔ ψ ) → ( ( φ ↔ χ ) ↔ ( ψ ↔ χ ) ) )",
        s1,
        ref="bibi1d",
        note="bibi1d",
    )

    return lb.build(res)


def prove_bibi12d(sys: System) -> Proof:
    """bibi12d: φ → ((ψ ↔ θ) ↔ (χ ↔ τ)).

    Deduction form of bibi12i: adding biconditionals to both sides
    of an equivalence.  (Contributed by NM, 11-May-1993.)
    """
    lb = ProofBuilder(sys, "bibi12d")
    h1 = lb.hyp("bibi12d.1", "( φ → ( ψ ↔ χ ) )")
    h2 = lb.hyp("bibi12d.2", "( φ → ( θ ↔ τ ) )")

    # bibi1d: ( φ → ( ψ ↔ χ ) ) |- ( φ → ( ( ψ ↔ θ ) ↔ ( χ ↔ θ ) ) )
    s1 = lb.ref(
        "s1",
        "( φ → ( ( ψ ↔ θ ) ↔ ( χ ↔ θ ) ) )",
        h1,
        ref="bibi1d",
        note="bibi1d",
    )

    # bibi2d: ( φ → ( θ ↔ τ ) ) |- ( φ → ( ( χ ↔ θ ) ↔ ( χ ↔ τ ) ) )
    s2 = lb.ref(
        "s2",
        "( φ → ( ( χ ↔ θ ) ↔ ( χ ↔ τ ) ) )",
        h2,
        ref="bibi2d",
        note="bibi2d",
    )

    # bitrd: combine s1 and s2
    res = lb.ref(
        "res",
        "( φ → ( ( ψ ↔ θ ) ↔ ( χ ↔ τ ) ) )",
        s1,
        s2,
        ref="bitrd",
        note="bitrd",
    )

    return lb.build(res)


def prove_bitr4id(sys: System) -> Proof:
    """bitr4id: ( ph -> ( ps <-> th ) ).
    Inference/deduction form of bitr4.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "bitr4id")

    h1 = lb.hyp("bitr4id.1", "( ph -> ( th <-> ch ) )")
    h2 = lb.hyp("bitr4id.2", "( ps <-> ch )")

    # bicomi: ( ps <-> ch ) |- ( ch <-> ps )
    s1 = lb.ref(
        "s1",
        "( ch <-> ps )",
        h2,
        ref="bicomi",
        note="bicomi",
    )

    # bitr2di: ( ph -> ( th <-> ch ) ), ( ch <-> ps )
    # |- ( ph -> ( ps <-> th ) )
    res = lb.ref(
        "res",
        "( ph -> ( ps <-> th ) )",
        h1,
        s1,
        ref="bitr2di",
        note="bitr2di",
    )

    return lb.build(res)


def prove_bitr2d(sys: System) -> Proof:
    """bitr2d: ( ph -> ( th <-> ps ) ).

    Deduction form of bitr2.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "bitr2d")

    h1 = lb.hyp("bitr2d.1", "( ph -> ( ps <-> ch ) )")
    h2 = lb.hyp("bitr2d.2", "( ph -> ( ch <-> th ) )")

    # bitrd: ( ph -> ( ps <-> ch ) ), ( ph -> ( ch <-> th ) )
    # |- ( ph -> ( ps <-> th ) )
    s1 = lb.ref(
        "s1",
        "( ph -> ( ps <-> th ) )",
        h1,
        h2,
        ref="bitrd",
        note="bitrd",
    )

    # bicomd: ( ph -> ( ps <-> th ) ) |- ( ph -> ( th <-> ps ) )
    res = lb.ref(
        "res",
        "( ph -> ( th <-> ps ) )",
        s1,
        ref="bicomd",
        note="bicomd",
    )

    return lb.build(res)


def prove_bitr3d(sys: System) -> Proof:
    """bitr3d: ( ph -> ( ch <-> th ) ).

    Deduction form of bitr3.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "bitr3d")

    h1 = lb.hyp("bitr3d.1", "( ph -> ( ps <-> ch ) )")
    h2 = lb.hyp("bitr3d.2", "( ph -> ( ps <-> th ) )")

    # bicomd: ( ph -> ( ps <-> ch ) ) |- ( ph -> ( ch <-> ps ) )
    s1 = lb.ref(
        "s1",
        "( ph -> ( ch <-> ps ) )",
        h1,
        ref="bicomd",
        note="bicomd",
    )

    # bitrd: ( ph -> ( ch <-> ps ) ), ( ph -> ( ps <-> th ) )
    # |- ( ph -> ( ch <-> th ) )
    res = lb.ref(
        "res",
        "( ph -> ( ch <-> th ) )",
        s1,
        h2,
        ref="bitrd",
        note="bitrd",
    )

    return lb.build(res)


def prove_bitr4d(sys: System) -> Proof:
    """bitr4d: ( ph -> ( ps <-> th ) ).

    Deduction form of bitr4.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "bitr4d")

    h1 = lb.hyp("bitr4d.1", "( ph -> ( ps <-> ch ) )")
    h2 = lb.hyp("bitr4d.2", "( ph -> ( th <-> ch ) )")

    # bicomd: ( ph -> ( th <-> ch ) ) |- ( ph -> ( ch <-> th ) )
    s1 = lb.ref(
        "s1",
        "( ph -> ( ch <-> th ) )",
        h2,
        ref="bicomd",
        note="bicomd",
    )

    # bitrd: ( ph -> ( ps <-> ch ) ), ( ph -> ( ch <-> th ) )
    # |- ( ph -> ( ps <-> th ) )
    res = lb.ref(
        "res",
        "( ph -> ( ps <-> th ) )",
        h1,
        s1,
        ref="bitrd",
        note="bitrd",
    )

    return lb.build(res)


def prove_3bitrd(sys: System) -> Proof:
    """3bitrd: ( ph -> ( ps <-> ta ) ).

    Deduction form of 3bitri.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "3bitrd")

    h1 = lb.hyp("3bitrd.1", "( ph -> ( ps <-> ch ) )")
    h2 = lb.hyp("3bitrd.2", "( ph -> ( ch <-> th ) )")
    h3 = lb.hyp("3bitrd.3", "( ph -> ( th <-> ta ) )")

    # bitrd: ( ph -> ( ps <-> ch ) ), ( ph -> ( ch <-> th ) )
    # |- ( ph -> ( ps <-> th ) )
    s1 = lb.ref(
        "s1",
        "( ph -> ( ps <-> th ) )",
        h1,
        h2,
        ref="bitrd",
        note="bitrd(3bitrd.1, 3bitrd.2)",
    )

    # bitrd: ( ph -> ( ps <-> th ) ), ( ph -> ( th <-> ta ) )
    # |- ( ph -> ( ps <-> ta ) )
    res = lb.ref(
        "res",
        "( ph -> ( ps <-> ta ) )",
        s1,
        h3,
        ref="bitrd",
        note="bitrd",
    )

    return lb.build(res)


def prove_3bitrrd(sys: System) -> Proof:
    """3bitrrd: ( ph -> ( ta <-> ps ) ).

    Deduction form of 3bitrr.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "3bitrrd")

    h1 = lb.hyp("3bitrrd.1", "( ph -> ( ps <-> ch ) )")
    h2 = lb.hyp("3bitrrd.2", "( ph -> ( ch <-> th ) )")
    h3 = lb.hyp("3bitrrd.3", "( ph -> ( th <-> ta ) )")

    # bitr2d: ( ph -> ( ps <-> ch ) ), ( ph -> ( ch <-> th ) )
    # |- ( ph -> ( th <-> ps ) )
    s1 = lb.ref(
        "s1",
        "( ph -> ( th <-> ps ) )",
        h1,
        h2,
        ref="bitr2d",
        note="bitr2d",
    )

    # bitr3d: ( ph -> ( th <-> ta ) ), ( ph -> ( th <-> ps ) )
    # |- ( ph -> ( ta <-> ps ) )
    res = lb.ref(
        "res",
        "( ph -> ( ta <-> ps ) )",
        h3,
        s1,
        ref="bitr3d",
        note="bitr3d",
    )

    return lb.build(res)


def prove_3bitr2d(sys: System) -> Proof:
    """3bitr2d: ( ph -> ( ps <-> ta ) ).

    Deduction form of 3bitr2i.
    (Contributed by NM, 4-Aug-2006.)
    """
    lb = ProofBuilder(sys, "3bitr2d")

    h1 = lb.hyp("3bitr2d.1", "( ph -> ( ps <-> ch ) )")
    h2 = lb.hyp("3bitr2d.2", "( ph -> ( th <-> ch ) )")
    h3 = lb.hyp("3bitr2d.3", "( ph -> ( th <-> ta ) )")

    # bitr4d: ( ph -> ( ps <-> ch ) ), ( ph -> ( th <-> ch ) )
    # |- ( ph -> ( ps <-> th ) )
    s1 = lb.ref(
        "s1",
        "( ph -> ( ps <-> th ) )",
        h1,
        h2,
        ref="bitr4d",
        note="bitr4d",
    )

    # bitrd: ( ph -> ( ps <-> th ) ), ( ph -> ( th <-> ta ) )
    # |- ( ph -> ( ps <-> ta ) )
    res = lb.ref(
        "res",
        "( ph -> ( ps <-> ta ) )",
        s1,
        h3,
        ref="bitrd",
        note="bitrd",
    )

    return lb.build(res)


def prove_3bitr2rd(sys: System) -> Proof:
    """3bitr2rd: ( ph -> ( ta <-> ps ) ).

    Deduction form of 3bitr2r.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "3bitr2rd")

    h1 = lb.hyp("3bitr2rd.1", "( ph -> ( ps <-> ch ) )")
    h2 = lb.hyp("3bitr2rd.2", "( ph -> ( th <-> ch ) )")
    h3 = lb.hyp("3bitr2rd.3", "( ph -> ( th <-> ta ) )")

    # bitr4d: ( ph -> ( ps <-> ch ) ), ( ph -> ( th <-> ch ) )
    # |- ( ph -> ( ps <-> th ) )
    s1 = lb.ref(
        "s1",
        "( ph -> ( ps <-> th ) )",
        h1,
        h2,
        ref="bitr4d",
        note="bitr4d",
    )

    # bitr2d: ( ph -> ( ps <-> th ) ), ( ph -> ( th <-> ta ) )
    # |- ( ph -> ( ta <-> ps ) )
    res = lb.ref(
        "res",
        "( ph -> ( ta <-> ps ) )",
        s1,
        h3,
        ref="bitr2d",
        note="bitr2d",
    )

    return lb.build(res)


def prove_3bitr3d(sys: System) -> Proof:
    """3bitr3d: ( ph -> ( th <-> ta ) ).

    Deduction form of 3bitr3.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "3bitr3d")

    h1 = lb.hyp("3bitr3d.1", "( ph -> ( ps <-> ch ) )")
    h2 = lb.hyp("3bitr3d.2", "( ph -> ( ps <-> th ) )")
    h3 = lb.hyp("3bitr3d.3", "( ph -> ( ch <-> ta ) )")

    # bitr3d: ( ph -> ( ps <-> ch ) ), ( ph -> ( ps <-> th ) )
    # |- ( ph -> ( ch <-> th ) )
    s1 = lb.ref(
        "s1",
        "( ph -> ( ch <-> th ) )",
        h1,
        h2,
        ref="bitr3d",
        note="bitr3d",
    )

    # bitr3d: ( ph -> ( ch <-> th ) ), ( ph -> ( ch <-> ta ) )
    # |- ( ph -> ( th <-> ta ) )
    res = lb.ref(
        "res",
        "( ph -> ( th <-> ta ) )",
        s1,
        h3,
        ref="bitr3d",
        note="bitr3d",
    )

    return lb.build(res)


def prove_3bitr3rd(sys: System) -> Proof:
    """3bitr3rd: ( ph -> ( ta <-> th ) ).

    Deduction form of 3bitr3r.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "3bitr3rd")

    h1 = lb.hyp("3bitr3rd.1", "( ph -> ( ps <-> ch ) )")
    h2 = lb.hyp("3bitr3rd.2", "( ph -> ( ps <-> th ) )")
    h3 = lb.hyp("3bitr3rd.3", "( ph -> ( ch <-> ta ) )")

    # bitr3d: ( ph -> ( ps <-> ch ) ), ( ph -> ( ps <-> th ) )
    # |- ( ph -> ( ch <-> th ) )
    s1 = lb.ref(
        "s1",
        "( ph -> ( ch <-> th ) )",
        h1,
        h2,
        ref="bitr3d",
        note="bitr3d",
    )

    # bitr3d: ( ph -> ( ch <-> ta ) ), ( ph -> ( ch <-> th ) )
    # |- ( ph -> ( ta <-> th ) )
    res = lb.ref(
        "res",
        "( ph -> ( ta <-> th ) )",
        h3,
        s1,
        ref="bitr3d",
        note="bitr3d",
    )

    return lb.build(res)


def prove_3bitr4rd(sys: System) -> Proof:
    """3bitr4rd: ( ph -> ( ta <-> th ) ).

    Deduction form of 3bitr4r.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "3bitr4rd")

    h1 = lb.hyp("3bitr4rd.1", "( ph -> ( ps <-> ch ) )")
    h2 = lb.hyp("3bitr4rd.2", "( ph -> ( th <-> ps ) )")
    h3 = lb.hyp("3bitr4rd.3", "( ph -> ( ta <-> ch ) )")

    # bitrd: ( ph -> ( th <-> ps ) ), ( ph -> ( ps <-> ch ) )
    # |- ( ph -> ( th <-> ch ) )
    s1 = lb.ref(
        "s1",
        "( ph -> ( th <-> ch ) )",
        h2,
        h1,
        ref="bitrd",
        note="bitrd",
    )

    # bitr4d: ( ph -> ( ta <-> ch ) ), ( ph -> ( th <-> ch ) )
    # |- ( ph -> ( ta <-> th ) )
    res = lb.ref(
        "res",
        "( ph -> ( ta <-> th ) )",
        h3,
        s1,
        ref="bitr4d",
        note="bitr4d",
    )

    return lb.build(res)


def prove_3bitr4d(sys: System) -> Proof:
    """3bitr4d: ( ph -> ( th <-> ta ) ).

    Deduction form of 3bitr4i.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "3bitr4d")

    h1 = lb.hyp("3bitr4d.1", "( ph -> ( ps <-> ch ) )")
    h2 = lb.hyp("3bitr4d.2", "( ph -> ( th <-> ps ) )")
    h3 = lb.hyp("3bitr4d.3", "( ph -> ( ta <-> ch ) )")

    # bitrd: ( ph -> ( th <-> ps ) ), ( ph -> ( ps <-> ch ) )
    # |- ( ph -> ( th <-> ch ) )
    s1 = lb.ref(
        "s1",
        "( ph -> ( th <-> ch ) )",
        h2,
        h1,
        ref="bitrd",
        note="bitrd",
    )

    # bitr4d: ( ph -> ( th <-> ch ) ), ( ph -> ( ta <-> ch ) )
    # |- ( ph -> ( th <-> ta ) )
    res = lb.ref(
        "res",
        "( ph -> ( th <-> ta ) )",
        s1,
        h3,
        ref="bitr4d",
        note="bitr4d",
    )

    return lb.build(res)


def prove_3bitr4g(sys: System) -> Proof:
    """3bitr4g: ( ph -> ( th <-> ta ) ).

    "G" variant of 3bitr4d: the latter two hypotheses are biconditionals
    instead of deductions.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "3bitr4g")

    h1 = lb.hyp("3bitr4g.1", "( ph -> ( ps <-> ch ) )")
    h2 = lb.hyp("3bitr4g.2", "( th <-> ps )")
    h3 = lb.hyp("3bitr4g.3", "( ta <-> ch )")

    # bitr4di: ( ph -> ( ps <-> ch ) ), ( ta <-> ch )
    # |- ( ph -> ( ps <-> ta ) )
    s1 = lb.ref(
        "s1",
        "( ph -> ( ps <-> ta ) )",
        h1,
        h3,
        ref="bitr4di",
        note="bitr4di",
    )

    # bitrid: ( th <-> ps ), ( ph -> ( ps <-> ta ) )
    # |- ( ph -> ( th <-> ta ) )
    res = lb.ref(
        "res",
        "( ph -> ( th <-> ta ) )",
        h2,
        s1,
        ref="bitrid",
        note="bitrid",
    )

    return lb.build(res)


def prove_3bitr2i(sys: System) -> Proof:
    """3bitr2i: ( ph <-> th ).

    An inference from transitive law for equivalence: from three
    biconditionals, deduce a biconditional linking the two outer
    propositions.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "3bitr2i")

    h1 = lb.hyp("3bitr2i.1", "( ph <-> ps )")
    h2 = lb.hyp("3bitr2i.2", "( ch <-> ps )")
    h3 = lb.hyp("3bitr2i.3", "( ch <-> th )")

    # bitr4i: ( ph <-> ps ), ( ch <-> ps ) -> ( ph <-> ch )
    s1 = lb.ref("s1", "( ph <-> ch )", h1, h2, ref="bitr4i", note="bitr4i")

    # bitri: ( ph <-> ch ), ( ch <-> th ) -> ( ph <-> th )
    res = lb.ref("res", "( ph <-> th )", s1, h3, ref="bitri", note="bitri")

    return lb.build(res)


def prove_3bitr2ri(sys: System) -> Proof:
    """3bitr2ri: ( th <-> ph ).

    A chained inference from transitive law for logical equivalence.
    (Contributed by NM, 4-Aug-2006.)
    """
    lb = ProofBuilder(sys, "3bitr2ri")

    h1 = lb.hyp("3bitr2ri.1", "( ph <-> ps )")
    h2 = lb.hyp("3bitr2ri.2", "( ch <-> ps )")
    h3 = lb.hyp("3bitr2ri.3", "( ch <-> th )")

    # bitr4i: ( ph <-> ps ), ( ch <-> ps ) -> ( ph <-> ch )
    s1 = lb.ref("s1", "( ph <-> ch )", h1, h2, ref="bitr4i", note="bitr4i")

    # bitr2i: ( ph <-> ch ), ( ch <-> th ) -> ( th <-> ph )
    res = lb.ref("res", "( th <-> ph )", s1, h3, ref="bitr2i", note="bitr2i")

    return lb.build(res)


def prove_3bitr3i(sys: System) -> Proof:
    """3bitr3i: ( ch ↔ th ).

    A chained inference from transitive law for logical equivalence.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "3bitr3i")

    h1 = lb.hyp("3bitr3i.1", "( ph ↔ ps )")
    h2 = lb.hyp("3bitr3i.2", "( ph ↔ ch )")
    h3 = lb.hyp("3bitr3i.3", "( ps ↔ th )")

    # bitr3i: ( ph ↔ ch ), ( ph ↔ ps ) → ( ch ↔ ps )
    s1 = lb.ref("s1", "( ch ↔ ps )", h2, h1, ref="bitr3i", note="bitr3i")

    # bitri: ( ch ↔ ps ), ( ps ↔ th ) → ( ch ↔ th )
    res = lb.ref("res", "( ch ↔ th )", s1, h3, ref="bitri", note="bitri")

    return lb.build(res)


def prove_3bitr3ri(sys: System) -> Proof:
    """3bitr3ri: ( th <-> ch ).

    A chained inference from transitive law for logical equivalence: reverse
    of 3bitr3i.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "3bitr3ri")

    h1 = lb.hyp("3bitr3ri.1", "( ph <-> ps )")
    h2 = lb.hyp("3bitr3ri.2", "( ph <-> ch )")
    h3 = lb.hyp("3bitr3ri.3", "( ps <-> th )")

    # bitr3i: ( ph <-> ps ), ( ph <-> ch ) -> ( ps <-> ch )
    s1 = lb.ref("s1", "( ps <-> ch )", h1, h2, ref="bitr3i", note="bitr3i")

    # bitr3i: ( ps <-> th ), ( ps <-> ch ) -> ( th <-> ch )
    res = lb.ref("res", "( th <-> ch )", h3, s1, ref="bitr3i", note="bitr3i")

    return lb.build(res)


def prove_3bitr3g(sys: System) -> Proof:
    """3bitr3g: φ → ( θ ↔ τ ).

    "G" variant of 3bitr3d: the latter two hypotheses are biconditionals
    instead of deductions.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "3bitr3g")

    h1 = lb.hyp("3bitr3g.1", "( φ → ( ψ ↔ χ ) )")
    h2 = lb.hyp("3bitr3g.2", "( ψ ↔ θ )")
    h3 = lb.hyp("3bitr3g.3", "( χ ↔ τ )")

    # bitrdi: ( φ → ( ψ ↔ χ ) ), ( χ ↔ τ )
    # |- ( φ → ( ψ ↔ τ ) )
    s1 = lb.ref(
        "s1",
        "( φ → ( ψ ↔ τ ) )",
        h1,
        h3,
        ref="bitrdi",
        note="bitrdi",
    )

    # bitr3id: ( ψ ↔ θ ), ( φ → ( ψ ↔ τ ) )
    # |- ( φ → ( θ ↔ τ ) )
    res = lb.ref(
        "res",
        "( φ → ( θ ↔ τ ) )",
        h2,
        s1,
        ref="bitr3id",
        note="bitr3id",
    )

    return lb.build(res)


def prove_3bitr4i(sys: System) -> Proof:
    """3bitr4i: ( ch <-> th ).

    An inference from transitive law for equivalence: combine three
    biconditionals into one.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "3bitr4i")

    h1 = lb.hyp("3bitr4i.1", "( ph <-> ps )")
    h2 = lb.hyp("3bitr4i.2", "( ch <-> ph )")
    h3 = lb.hyp("3bitr4i.3", "( th <-> ps )")

    # bitri: ( ch <-> ph ), ( ph <-> ps ) -> ( ch <-> ps )
    s1 = lb.ref("s1", "( ch <-> ps )", h2, h1, ref="bitri", note="bitri")

    # bitr4i: ( ch <-> ps ), ( th <-> ps ) -> ( ch <-> th )
    res = lb.ref("res", "( ch <-> th )", s1, h3, ref="bitr4i", note="bitr4i")

    return lb.build(res)


def prove_3bitr4ri(sys: System) -> Proof:
    """3bitr4ri: ( th <-> ch ).

    An inference from transitive law for equivalence: combine three
    biconditionals into one, with the final biconditional reversed.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "3bitr4ri")

    h1 = lb.hyp("3bitr4ri.1", "( ph <-> ps )")
    h2 = lb.hyp("3bitr4ri.2", "( ch <-> ph )")
    h3 = lb.hyp("3bitr4ri.3", "( th <-> ps )")

    # bitr4i: ( ph <-> ps ), ( th <-> ps ) -> ( ph <-> th )
    s1 = lb.ref("s1", "( ph <-> th )", h1, h3, ref="bitr4i", note="bitr4i")

    # bitr2i: ( ch <-> ph ), ( ph <-> th ) -> ( th <-> ch )
    res = lb.ref("res", "( th <-> ch )", h2, s1, ref="bitr2i", note="bitr2i")

    return lb.build(res)


def prove_3bitri(sys: System) -> Proof:
    """3bitri: ( ph <-> th ).

    An inference from transitive law for equivalence: from three
    biconditionals, deduce a biconditional linking the two outer
    propositions.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "3bitri")

    h1 = lb.hyp("3bitri.1", "( ph <-> ps )")
    h2 = lb.hyp("3bitri.2", "( ps <-> ch )")
    h3 = lb.hyp("3bitri.3", "( ch <-> th )")

    # bitri: ( ph <-> ps ), ( ps <-> ch ) -> ( ph <-> ch )
    s1 = lb.ref("s1", "( ph <-> ch )", h1, h2, ref="bitri", note="bitri")

    # bitri: ( ph <-> ch ), ( ch <-> th ) -> ( ph <-> th )
    res = lb.ref("res", "( ph <-> th )", s1, h3, ref="bitri", note="bitri")

    return lb.build(res)


def prove_3bitrri(sys: System) -> Proof:
    """3bitrri: ( th <-> ph ).

    A chained inference from transitive law for logical equivalence,
    linking the final proposition back to the first.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "3bitrri")

    h1 = lb.hyp("3bitrri.1", "( ph <-> ps )")
    h2 = lb.hyp("3bitrri.2", "( ps <-> ch )")
    h3 = lb.hyp("3bitrri.3", "( ch <-> th )")

    # bitr2i: ( ph <-> ps ), ( ps <-> ch ) -> ( ch <-> ph )
    s1 = lb.ref("s1", "( ch <-> ph )", h1, h2, ref="bitr2i", note="bitr2i")

    # bitr3i: ( ch <-> th ), ( ch <-> ph ) -> ( th <-> ph )
    res = lb.ref("res", "( th <-> ph )", h3, s1, ref="bitr3i", note="bitr3i")

    return lb.build(res)


def prove_bibi1i(sys: System) -> Proof:
    """bibi1i: ( ( ph <-> ch ) <-> ( ps <-> ch ) ).

    Inference adding a biconditional to the right in an equivalence.
    (Contributed by NM, 26-May-1993.)
    """
    lb = ProofBuilder(sys, "bibi1i")
    h1 = lb.hyp("bibi1i.1", "( ph <-> ps )")

    # bicom: |- ( ( ph <-> ch ) <-> ( ch <-> ph ) )
    s1 = lb.ref(
        "s1",
        "( ( ph <-> ch ) <-> ( ch <-> ph ) )",
        ref="bicom",
        note="bicom",
    )

    # bibi2i: from hypothesis (ph <-> ps), get |- ( ( ch <-> ph ) <-> ( ch <-> ps ) )
    s2 = lb.ref(
        "s2",
        "( ( ch <-> ph ) <-> ( ch <-> ps ) )",
        h1,
        ref="bibi2i",
        note="bibi2i",
    )

    # bicom: |- ( ( ch <-> ps ) <-> ( ps <-> ch ) )
    s3 = lb.ref(
        "s3",
        "( ( ch <-> ps ) <-> ( ps <-> ch ) )",
        ref="bicom",
        note="bicom",
    )

    # 3bitri with the three biconditionals
    res = lb.ref(
        "res",
        "( ( ph <-> ch ) <-> ( ps <-> ch ) )",
        s1,
        s2,
        s3,
        ref="3bitri",
        note="3bitri",
    )

    return lb.build(res)


def prove_bibi12i(sys: System) -> Proof:
    """bibi12i: ( ( ph <-> ch ) <-> ( ps <-> th ) ).

    Inference form: from ( ph <-> ps ) and ( ch <-> th ),
    deduce the biconditional of biconditionals.
    (Contributed by NM, 1-Nov-1993.)
    """
    lb = ProofBuilder(sys, "bibi12i")
    h1 = lb.hyp("bibi12i.1", "( ph <-> ps )")
    h2 = lb.hyp("bibi12i.2", "( ch <-> th )")

    # bibi1i: from ( ph <-> ps ), get |- ( ( ph <-> ch ) <-> ( ps <-> ch ) )
    s1 = lb.ref(
        "s1",
        "( ( ph <-> ch ) <-> ( ps <-> ch ) )",
        h1,
        ref="bibi1i",
        note="bibi1i",
    )

    # bibi2i: from ( ch <-> th ), get |- ( ( ps <-> ch ) <-> ( ps <-> th ) )
    s2 = lb.ref(
        "s2",
        "( ( ps <-> ch ) <-> ( ps <-> th ) )",
        h2,
        ref="bibi2i",
        note="bibi2i",
    )

    # bitri: ( ( ph <-> ch ) <-> ( ps <-> ch ) ), ( ( ps <-> ch ) <-> ( ps <-> th ) )
    # |- ( ( ph <-> ch ) <-> ( ps <-> th ) )
    res = lb.ref(
        "res",
        "( ( ph <-> ch ) <-> ( ps <-> th ) )",
        s1,
        s2,
        ref="bitri",
        note="bitri",
    )

    return lb.build(res)


def prove_bija(sys: System) -> Proof:
    """bija: ( ( ph <-> ps ) -> ch ).

    Combine biimpr + syli and biimp + con3d + syli, then apply pm2.61d.
    (Contributed by NM, 27-Apr-1994.)
    """
    lb = ProofBuilder(sys, "bija")
    h1 = lb.hyp("bija.1", "ph -> ( ps -> ch )")
    h2 = lb.hyp("bija.2", "¬ ph -> ( ¬ ps -> ch )")

    # (1) ( ph <-> ps ) -> ( ps -> ch )  via  syli(biimpr, bija.1)
    s1 = lb.ref(
        "s1",
        "( ph <-> ps ) -> ( ps -> ph )",
        ref="biimpr",
        note="biimpr",
    )
    s2 = lb.ref(
        "s2",
        "( ph <-> ps ) -> ( ps -> ch )",
        s1,
        h1,
        ref="syli",
        note="syli(biimpr,bija.1)",
    )

    # (2) ( ph <-> ps ) -> ( ¬ ps -> ch )  via  syli(con3d(biimp), bija.2)
    s3 = lb.ref(
        "s3",
        "( ph <-> ps ) -> ( ph -> ps )",
        ref="biimp",
        note="biimp",
    )
    s4 = lb.ref(
        "s4",
        "( ph <-> ps ) -> ( ¬ ps -> ¬ ph )",
        s3,
        ref="con3d",
        note="con3d(biimp)",
    )
    s5 = lb.ref(
        "s5",
        "( ph <-> ps ) -> ( ¬ ps -> ch )",
        s4,
        h2,
        ref="syli",
        note="syli(con3d(biimp),bija.2)",
    )

    # (3) pm2.61d(s2, s5)  →  ( ph <-> ps ) -> ch
    res = lb.ref(
        "res",
        "( ph <-> ps ) -> ch",
        s2,
        s5,
        ref="pm2.61d",
        note="pm2.61d",
    )

    return lb.build(res)


def prove_iba(sys: System) -> Proof:
    """iba: φ → ( ψ ↔ ( ψ ∧ φ ) ).

    Introduce biconditional absorption.  From φ, deduce that ψ is
    equivalent to ψ ∧ φ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "iba")

    s_pm3_21 = lb.ref(
        "s_pm3_21",
        "φ → ( ψ → ( ψ ∧ φ ) )",
        ref="pm3.21",
        note="pm3.21",
    )

    s_simpl = lb.ref(
        "s_simpl",
        "( ψ ∧ φ ) → ψ",
        ref="simpl",
        note="simpl",
    )

    res = lb.ref(
        "res",
        "φ → ( ψ ↔ ( ψ ∧ φ ) )",
        s_pm3_21,
        s_simpl,
        ref="impbid1",
        note="impbid1",
    )

    return lb.build(res)


def prove_ibar(sys: System) -> Proof:
    """ibar: φ → ( ψ ↔ ( φ ∧ ψ ) ).

    Introduce biconditional absorption.  From φ, deduce that ψ is
    equivalent to φ ∧ ψ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "ibar")

    s_iba = lb.ref(
        "s_iba",
        "φ → ( ψ ↔ ( ψ ∧ φ ) )",
        ref="iba",
        note="iba",
    )

    res = lb.ref(
        "res",
        "φ → ( ψ ↔ ( φ ∧ ψ ) )",
        s_iba,
        ref="biancomd",
        note="biancomd",
    )

    return lb.build(res)


def prove_ibib(sys: System) -> Proof:
    """ibib: ( ( ph -> ps ) <-> ( ph -> ( ph <-> ps ) ) ).

    Equivalence of an implication and the same implication with a
    biconditional embedded in the consequent.  (Contributed by NM,
    5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "ibib")

    # pm5.501: ( ph -> ( ps <-> ( ph <-> ps ) ) )
    pm5_501 = lb.ref(
        "pm5_501",
        "( ph -> ( ps <-> ( ph <-> ps ) ) )",
        ref="pm5.501",
        note="pm5.501",
    )

    # pm5.74i: from pm5.501, deduce ( ( ph -> ps ) <-> ( ph -> ( ph <-> ps ) ) )
    res = lb.ref(
        "res",
        "( ( ph -> ps ) <-> ( ph -> ( ph <-> ps ) ) )",
        pm5_501,
        ref="pm5.74i",
        note="pm5.74i",
    )

    return lb.build(res)


def prove_ibibr(sys: System) -> Proof:
    """ibibr: ( ( ph -> ps ) <-> ( ph -> ( ps <-> ph ) ) ).

    Variant of ibib with the biconditional commuted in the consequent.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "ibibr")

    # pm5.501: ( ph -> ( ps <-> ( ph <-> ps ) ) )
    pm5_501 = lb.ref(
        "pm5_501",
        "( ph -> ( ps <-> ( ph <-> ps ) ) )",
        ref="pm5.501",
        note="pm5.501",
    )

    # bicom: ( ( ph <-> ps ) <-> ( ps <-> ph ) )
    bicom_ref = lb.ref(
        "bicom_ref",
        "( ( ph <-> ps ) <-> ( ps <-> ph ) )",
        ref="bicom",
        note="bicom",
    )

    # bitrdi: ( ph -> ( ps <-> ( ps <-> ph ) ) )
    bitrdi_res = lb.ref(
        "bitrdi_res",
        "( ph -> ( ps <-> ( ps <-> ph ) ) )",
        pm5_501,
        bicom_ref,
        ref="bitrdi",
        note="bitrdi",
    )

    # pm5.74i: from the above, deduce the target
    res = lb.ref(
        "res",
        "( ( ph -> ps ) <-> ( ph -> ( ps <-> ph ) ) )",
        bitrdi_res,
        ref="pm5.74i",
        note="pm5.74i",
    )

    return lb.build(res)


def prove_tbt(sys: System) -> Proof:
    """tbt: ( ps <-> ( ps <-> ph ) ).

    Inference from ibibr and a true antecedent: if ph holds, then
    ps is equivalent to "ps is equivalent to ph".
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "tbt")
    h1 = lb.hyp("tbt.1", "ph")

    # ibibr: ( ( ph -> ps ) <-> ( ph -> ( ps <-> ph ) ) )
    ibibr_ref = lb.ref(
        "ibibr_ref",
        "( ( ph -> ps ) <-> ( ph -> ( ps <-> ph ) ) )",
        ref="ibibr",
        note="ibibr",
    )

    # pm5.74ri: ( ph -> ( ps <-> ( ps <-> ph ) ) )
    pm5_74ri_res = lb.ref(
        "pm5_74ri_res",
        "( ph -> ( ps <-> ( ps <-> ph ) ) )",
        ibibr_ref,
        ref="pm5.74ri",
        note="pm5.74ri",
    )

    # ax-mp: ph, ph -> ( ps <-> ( ps <-> ph ) ) |- ( ps <-> ( ps <-> ph ) )
    res = lb.mp("res", h1, pm5_74ri_res, "MP hyp, pm5.74ri")

    return lb.build(res)


def prove_biimt(sys: System) -> Proof:
    """biimt: ( ph -> ( ps <-> ( ph -> ps ) ) ).

    From a true antecedent, a consequent is equivalent to the
    implication of the antecedent and consequent.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "biimt")

    # ax-1 with variables swapped: ( ps -> ( ph -> ps ) )
    h1 = lb.ref("h1", "( ps -> ( ph -> ps ) )", ref="ax-1", note="ax-1")

    # pm2.27: ( ph -> ( ( ph -> ps ) -> ps ) )
    h2 = lb.ref("h2", "( ph -> ( ( ph -> ps ) -> ps ) )", ref="pm2.27", note="pm2.27")

    # impbid2 from h1 and h2 gives ( ph -> ( ps <-> ( ph -> ps ) ) )
    res = lb.ref(
        "res",
        "( ph -> ( ps <-> ( ph -> ps ) ) )",
        h1,
        h2,
        ref="impbid2",
        note="impbid2",
    )

    return lb.build(res)


def prove_a1bi(sys: System) -> Proof:
    """a1bi: ( ps <-> ( ph -> ps ) ).

    Inference form of biimt: from a true antecedent, the consequent is
    equivalent to the implication with that antecedent.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "a1bi")
    h1 = lb.hyp("a1bi.1", "ph")
    s1 = lb.ref(
        "s1",
        "( ph -> ( ps <-> ( ph -> ps ) ) )",
        ref="biimt",
        note="biimt",
    )
    res = lb.mp("res", h1, s1, "MP hyp1, biimt")
    return lb.build(res)


def prove_baib(sys: System) -> Proof:
    """baib: ψ → ( φ ↔ χ ).

    From an equivalence of φ and ψ ∧ χ, deduce that ψ implies the
    equivalence of φ and χ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "baib")

    h1 = lb.hyp("baib.1", "( φ ↔ ( ψ ∧ χ ) )")

    # ibar: ψ → ( χ ↔ ( ψ ∧ χ ) )
    s_ibar = lb.ref(
        "s_ibar",
        "ψ → ( χ ↔ ( ψ ∧ χ ) )",
        ref="ibar",
        note="ibar",
    )

    # bitr4id: from ibar and baib.1, prove ψ → ( φ ↔ χ )
    res = lb.ref(
        "res",
        "ψ → ( φ ↔ χ )",
        s_ibar,
        h1,
        ref="bitr4id",
        note="bitr4id",
    )

    return lb.build(res)


def prove_baibd(sys: System) -> Proof:
    """baibd: ( φ ∧ χ ) → ( ψ ↔ θ ).

    Deduction form of baib: from φ → ( ψ ↔ ( χ ∧ θ ) ), deduce that
    φ and χ together imply ψ ↔ θ .
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "baibd")

    h1 = lb.hyp("baibd.1", "φ → ( ψ ↔ ( χ ∧ θ ) )")

    # ibar: χ → ( θ ↔ ( χ ∧ θ ) )
    s_ibar = lb.ref(
        "s_ibar",
        "χ → ( θ ↔ ( χ ∧ θ ) )",
        ref="ibar",
        note="ibar",
    )

    # bicomd: χ → ( ( χ ∧ θ ) ↔ θ )
    s_bicomd = lb.ref(
        "s_bicomd",
        "χ → ( ( χ ∧ θ ) ↔ θ )",
        s_ibar,
        ref="bicomd",
        note="bicomd",
    )

    # sylan9bb: ( φ ∧ χ ) → ( ψ ↔ θ )
    res = lb.ref(
        "res",
        "( φ ∧ χ ) → ( ψ ↔ θ )",
        h1,
        s_bicomd,
        ref="sylan9bb",
        note="sylan9bb",
    )

    return lb.build(res)


def prove_rbaibd(sys: System) -> Proof:
    """rbaibd: ( φ ∧ θ ) → ( ψ ↔ χ ).

    Deduction form of rbaib: from φ → ( ψ ↔ ( χ ∧ θ ) ), deduce that
    φ and θ together imply ψ ↔ χ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "rbaibd")

    h1 = lb.hyp("baibd.1", "φ → ( ψ ↔ ( χ ∧ θ ) )")

    # biancomd: φ → ( ψ ↔ ( θ ∧ χ ) )
    s_biancomd = lb.ref(
        "s_biancomd",
        "φ → ( ψ ↔ ( θ ∧ χ ) )",
        h1,
        ref="biancomd",
        note="biancomd",
    )

    # baibd: ( φ ∧ θ ) → ( ψ ↔ χ )
    res = lb.ref(
        "res",
        "( φ ∧ θ ) → ( ψ ↔ χ )",
        s_biancomd,
        ref="baibd",
        note="baibd",
    )

    return lb.build(res)


def prove_baibr(sys: System) -> Proof:
    """baibr: ψ → ( χ ↔ φ ).

    Inference form of baib: from φ ↔ ( ψ ∧ χ ), deduce that ψ implies
    χ ↔ φ .  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "baibr")

    h1 = lb.hyp("baibr.1", "( φ ↔ ( ψ ∧ χ ) )")

    # baib: from hypothesis, get ψ → ( φ ↔ χ )
    s1 = lb.ref(
        "s1",
        "ψ → ( φ ↔ χ )",
        h1,
        ref="baib",
        note="baib",
    )

    # bicomd: from ψ → ( φ ↔ χ ), get ψ → ( χ ↔ φ )
    res = lb.ref(
        "res",
        "ψ → ( χ ↔ φ )",
        s1,
        ref="bicomd",
        note="bicomd",
    )

    return lb.build(res)


def prove_rbaibr(sys: System) -> Proof:
    """rbaibr: χ → ( ψ ↔ φ ).

    Inference form: from φ ↔ ( ψ ∧ χ ), deduce that χ implies ψ ↔ φ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "rbaibr")

    h1 = lb.hyp("rbaibr.1", "( φ ↔ ( ψ ∧ χ ) )")

    s1 = lb.ref(
        "s1",
        "( φ ↔ ( χ ∧ ψ ) )",
        h1,
        ref="biancomi",
        note="biancomi",
    )

    res = lb.ref(
        "res",
        "χ → ( ψ ↔ φ )",
        s1,
        ref="baibr",
        note="baibr",
    )

    return lb.build(res)


def prove_rbaib(sys: System) -> Proof:
    """rbaib: χ → ( φ ↔ ψ ).

    Inference form: from φ ↔ ( ψ ∧ χ ), deduce that χ implies φ ↔ ψ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "rbaib")

    h1 = lb.hyp("rbaib.1", "( φ ↔ ( ψ ∧ χ ) )")

    s1 = lb.ref(
        "s1",
        "χ → ( ψ ↔ φ )",
        h1,
        ref="rbaibr",
        note="rbaibr",
    )

    res = lb.ref(
        "res",
        "χ → ( φ ↔ ψ )",
        s1,
        ref="bicomd",
        note="bicomd",
    )

    return lb.build(res)


def prove_mt2bi(sys: System) -> Proof:
    """mt2bi: ( -. ps <-> ( ps -> -. ph ) ).

    Given ph, the negation of ps is equivalent to ps implying the negation
    of ph.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "mt2bi")
    h1 = lb.hyp("mt2bi.1", "ph")

    # a1bi: ( -. ps <-> ( ph -> -. ps ) )
    s1 = lb.ref(
        "s1",
        "( -. ps <-> ( ph -> -. ps ) )",
        h1,
        ref="a1bi",
        note="a1bi",
    )

    # con2b: ( ( ph -> -. ps ) <-> ( ps -> -. ph ) )
    s2 = lb.ref(
        "s2",
        "( ( ph -> -. ps ) <-> ( ps -> -. ph ) )",
        ref="con2b",
        note="con2b",
    )

    # bitri: ( -. ps <-> ( ps -> -. ph ) )
    res = lb.ref(
        "res",
        "( -. ps <-> ( ps -> -. ph ) )",
        s1,
        s2,
        ref="bitri",
        note="bitri",
    )
    return lb.build(res)


def prove_imnot(sys: System) -> Proof:
    """imnot: |- ( -. ps -> ( ( ph -> ps ) <-> -. ph ) ).

    Negated antecedent: consequent's negation is equivalent to the
    consequent implying the negated antecedent.  (Contributed by NM,
    13-Sep-2011.)
    """
    lb = ProofBuilder(sys, "imnot")

    # mtt with ph := ps, ps := ph: ( -. ps -> ( -. ph <-> ( ph -> ps ) ) )
    s1 = lb.ref(
        "s1",
        "( -. ps -> ( -. ph <-> ( ph -> ps ) ) )",
        ref="mtt",
        note="mtt",
    )

    # bicomd: from mtt, commute the biconditional
    res = lb.ref(
        "res",
        "( -. ps -> ( ( ph -> ps ) <-> -. ph ) )",
        s1,
        ref="bicomd",
        note="bicomd",
    )

    return lb.build(res)


def prove_mtt(sys: System) -> Proof:
    """mtt: ( -. ph -> ( -. ps <-> ( ps -> ph ) ) ).

    A negated antecedent: the consequent's negation is equivalent to
    the consequent implying the negated antecedent.
    (Contributed by NM, 13-Sep-2011.)
    """
    lb = ProofBuilder(sys, "mtt")

    # biimt: ( -. ph -> ( -. ps <-> ( -. ph -> -. ps ) ) )
    s1 = lb.ref(
        "s1",
        "( -. ph -> ( -. ps <-> ( -. ph -> -. ps ) ) )",
        ref="biimt",
        note="biimt",
    )

    # con34b with ph and ps swapped: ( ( ps -> ph ) <-> ( -. ph -> -. ps ) )
    s2 = lb.ref(
        "s2",
        "( ( ps -> ph ) <-> ( -. ph -> -. ps ) )",
        ref="con34b",
        note="con34b",
    )

    # bitr4di: ( -. ph -> ( -. ps <-> ( ps -> ph ) ) )
    res = lb.ref(
        "res",
        "( -. ph -> ( -. ps <-> ( ps -> ph ) ) )",
        s1,
        s2,
        ref="bitr4di",
        note="bitr4di",
    )

    return lb.build(res)


def prove_monothetic(sys: System) -> Proof:
    """monothetic: ( ( ph -> ph ) <-> ( ps -> ps ) ).

    Two instances of the law of identity are equivalent.
    (Contributed by NM, 1-Aug-1992.)
    """
    lb = ProofBuilder(sys, "monothetic")

    # id: ( ph -> ph )
    s1 = lb.ref("s1", "( ph -> ph )", ref="id", note="id")

    # id: ( ps -> ps )
    s2 = lb.ref("s2", "( ps -> ps )", ref="id", note="id")

    # 2th: from |- ( ph -> ph ) and |- ( ps -> ps ), get ( ( ph -> ph ) <-> ( ps -> ps ) )
    res = lb.ref("res", "( ( ph -> ph ) <-> ( ps -> ps ) )", s1, s2, ref="2th", note="2th")

    return lb.build(res)


def prove_imim21b(sys: System) -> Proof:
    """imim21b: (ψ → φ) → (((φ → χ) → (ψ → θ)) ↔ (ψ → (χ → θ))).

    An antecedent fixes itself to the consequent of an implication when the
    consequent is an equivalence; commuted variant of imim21b.
    (Contributed by Paul Chapman, 22-Jun-2011.)
    """
    lb = ProofBuilder(sys, "imim21b")

    # Step 1: bi2.04 — (φ → (ψ → χ)) ↔ (ψ → (φ → χ))
    # With φ↦(φ→χ), ψ↦ψ, χ↦θ:
    s1 = lb.ref(
        "s1",
        "( ( φ → χ ) → ( ψ → θ ) ) ↔ ( ψ → ( ( φ → χ ) → θ ) )",
        ref="bi2.04",
        note="bi2.04",
    )

    # Step 2: pm5.5 — φ → ((φ → ψ) ↔ ψ)
    # With φ↦φ, ψ↦χ:
    s2 = lb.ref(
        "s2",
        "φ → ( ( φ → χ ) ↔ χ )",
        ref="pm5.5",
        note="pm5.5",
    )

    # Step 3: imbi1d — (φ → (ψ ↔ χ)) → (φ → ((ψ → θ) ↔ (χ → θ)))
    # With ph↦φ, ps↦(φ→χ), ch↦χ, th↦θ, using s2 as hypothesis:
    s3 = lb.ref(
        "s3",
        "φ → ( ( ( φ → χ ) → θ ) ↔ ( χ → θ ) )",
        s2,
        ref="imbi1d",
        note="imbi1d",
    )

    # Step 4: imim2i — (ψ → χ) → ((φ → ψ) → (φ → χ))
    # With ψ↦φ, χ↦(((φ→χ)→θ)↔(χ→θ)), φ↦ψ, using s3 as hypothesis:
    s4 = lb.ref(
        "s4",
        "( ψ → φ ) → ( ψ → ( ( ( φ → χ ) → θ ) ↔ ( χ → θ ) ) )",
        s3,
        ref="imim2i",
        note="imim2i",
    )

    # Step 5: pm5.74d — (φ → (ψ → (χ ↔ θ))) → (φ → ((ψ → χ) ↔ (ψ → θ)))
    # With φ↦(ψ→φ), ψ↦ψ, χ↦((φ→χ)→θ), θ↦(χ→θ), using s4 as hypothesis:
    s5 = lb.ref(
        "s5",
        "( ψ → φ ) → ( ( ψ → ( ( φ → χ ) → θ ) ) ↔ ( ψ → ( χ → θ ) ) )",
        s4,
        ref="pm5.74d",
        note="pm5.74d",
    )

    # Step 6: bitrid — (φ ↔ ψ) and (χ → (ψ ↔ θ)) → (χ → (φ ↔ θ))
    # With φ↦((φ→χ)→(ψ→θ)), ψ↦(ψ→((φ→χ)→θ)), χ↦(ψ→φ), θ↦(ψ→(χ→θ)):
    res = lb.ref(
        "res",
        "( ψ → φ ) → ( ( ( φ → χ ) → ( ψ → θ ) ) ↔ ( ψ → ( χ → θ ) ) )",
        s1,
        s5,
        ref="bitrid",
        note="bitrid",
    )

    return lb.build(res)


def prove_bitr3(sys: System) -> Proof:
    """bitr3: ( φ ↔ ψ ) → ( ( φ ↔ χ ) → ( ψ ↔ χ ) ).

    Variant of bitr with the left biconditional moved to the front
    as a common antecedent.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "bitr3")

    # bibi1: ( ( φ ↔ ψ ) → ( ( φ ↔ χ ) ↔ ( ψ ↔ χ ) ) )
    s1 = lb.ref(
        "s1",
        "( ( φ ↔ ψ ) → ( ( φ ↔ χ ) ↔ ( ψ ↔ χ ) ) )",
        ref="bibi1",
        note="bibi1",
    )

    # biimpd applied to s1: ( ( φ ↔ ψ ) → ( ( φ ↔ χ ) → ( ψ ↔ χ ) ) )
    res = lb.ref(
        "res",
        "( ( φ ↔ ψ ) → ( ( φ ↔ χ ) → ( ψ ↔ χ ) ) )",
        s1,
        ref="biimpd",
        note="biimpd",
    )

    return lb.build(res)


def prove_imbibi(sys: System) -> Proof:
    """imbibi: ((φ → ψ) ↔ χ) → (φ → (ψ ↔ χ)).

    An implication inside a biconditional with ch can be turned into a
    biconditional inside an implication with ch.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "imbibi")

    # bitr3: (φ ↔ ψ) → ((φ ↔ χ) → (ψ ↔ χ))
    # With φ ↦ (φ → ψ), ψ ↦ ψ, χ ↦ χ:
    s1 = lb.ref(
        "s1",
        "( ( φ → ψ ) ↔ ψ ) → ( ( ( φ → ψ ) ↔ χ ) → ( ψ ↔ χ ) )",
        ref="bitr3",
        note="bitr3",
    )

    # pm5.5: φ → ((φ → ψ) ↔ ψ)
    s2 = lb.ref(
        "s2",
        "φ → ( ( φ → ψ ) ↔ ψ )",
        ref="pm5.5",
        note="pm5.5",
    )

    # syl11: ψ → (θ → χ). Hyp: φ → (ψ → χ), θ → φ.
    # With hyp1 = s1: ((φ→ψ)↔ψ) → (((φ→ψ)↔χ) → (ψ↔χ))
    #      hyp2 = s2: φ → ((φ→ψ)↔ψ)
    #      conclusion: ((φ→ψ)↔χ) → (φ → (ψ↔χ))
    res = lb.ref(
        "res",
        "( ( φ → ψ ) ↔ χ ) → ( φ → ( ψ ↔ χ ) )",
        s1,
        s2,
        ref="syl11",
        note="syl11",
    )

    return lb.build(res)


def prove_imbibiOLD(sys: System) -> Proof:
    """imbibiOLD: ( ( ( φ → ψ ) ↔ χ ) → ( φ → ( ψ ↔ χ ) ).

    The biconditional version of imbiOLD.
    (Contributed by NM, 29-May-1999.)  (New usage is discouraged.)
    """
    lb = ProofBuilder(sys, "imbibiOLD")

    # pm5.4: ( ( φ → ( φ → ψ ) ) ↔ ( φ → ψ ) )
    s1 = lb.ref(
        "s1",
        "( ( φ → ( φ → ψ ) ) ↔ ( φ → ψ ) )",
        ref="pm5.4",
        note="pm5.4",
    )

    # imbi2: ( ( ( φ → ψ ) ↔ χ ) → ( ( φ → ( φ → ψ ) ) ↔ ( φ → χ ) ) )
    s2 = lb.ref(
        "s2",
        "( ( ( φ → ψ ) ↔ χ ) → ( ( φ → ( φ → ψ ) ) ↔ ( φ → χ ) ) )",
        ref="imbi2",
        note="imbi2",
    )

    # bitr3id: ( ( ( φ → ψ ) ↔ χ ) → ( ( φ → ψ ) ↔ ( φ → χ ) ) )
    s3 = lb.ref(
        "s3",
        "( ( ( φ → ψ ) ↔ χ ) → ( ( φ → ψ ) ↔ ( φ → χ ) ) )",
        s1,
        s2,
        ref="bitr3id",
        note="bitr3id",
    )

    # pm5.74rd: ( ( ( φ → ψ ) ↔ χ ) → ( φ → ( ψ ↔ χ ) ) )
    res = lb.ref(
        "res",
        "( ( ( φ → ψ ) ↔ χ ) → ( φ → ( ψ ↔ χ ) ) )",
        s3,
        ref="pm5.74rd",
        note="pm5.74rd",
    )

    return lb.build(res)


def prove_impimprbi(sys: System) -> Proof:
    """impimprbi: ( ( φ ↔ ψ ) ↔ ( ( φ → ψ ) ↔ ( ψ → φ ) ) ).

    A biconditional is equivalent to the bidirectional implication of its
    components.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "impimprbi")

    # Forward direction: ( φ ↔ ψ ) → ( ( φ → ψ ) ↔ ( ψ → φ ) )
    s1 = lb.ref(
        "s1",
        "( φ ↔ ψ ) ↔ ( ( φ → ψ ) ∧ ( ψ → φ ) )",
        ref="dfbi2",
        note="dfbi2",
    )
    s2 = lb.ref(
        "s2",
        "( ( φ → ψ ) ∧ ( ψ → φ ) ) → ( ( φ → ψ ) ↔ ( ψ → φ ) )",
        ref="pm5.1",
        note="pm5.1",
    )
    forward = lb.ref(
        "forward",
        "( φ ↔ ψ ) → ( ( φ → ψ ) ↔ ( ψ → φ ) )",
        s1,
        s2,
        ref="sylbi",
        note="sylbi",
    )

    # Reverse direction: ( ( φ → ψ ) ↔ ( ψ → φ ) ) → ( φ ↔ ψ )
    s3 = lb.ref(
        "s3",
        "( φ → ψ ) → ( ( ψ → φ ) → ( φ ↔ ψ ) )",
        ref="impbi",
        note="impbi",
    )
    s4 = lb.ref(
        "s4",
        "¬ ( φ → ψ ) → ( ψ → φ )",
        ref="pm2.521",
        note="pm2.521",
    )
    s5 = lb.ref(
        "s5",
        "¬ ( φ → ψ ) → ( ¬ ( ψ → φ ) → ( φ ↔ ψ ) )",
        s4,
        ref="pm2.24d",
        note="pm2.24d",
    )
    reverse = lb.ref(
        "reverse",
        "( ( φ → ψ ) ↔ ( ψ → φ ) ) → ( φ ↔ ψ )",
        s3,
        s5,
        ref="bija",
        note="bija",
    )

    # Combine forward and reverse via impbii
    res = lb.ref(
        "res",
        "( φ ↔ ψ ) ↔ ( ( φ → ψ ) ↔ ( ψ → φ ) )",
        forward,
        reverse,
        ref="impbii",
        note="impbii",
    )

    return lb.build(res)


def prove_bianabs(sys: System) -> Proof:
    """bianabs: φ → ( ψ ↔ χ ).

    Absorb a biconditional embedded with a conjunct in the consequent.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "bianabs")

    h1 = lb.hyp("bianabs.1", "φ → ( ψ ↔ ( φ ∧ χ ) )")

    # ibar: φ → ( χ ↔ ( φ ∧ χ ) )
    s_ibar = lb.ref(
        "s_ibar",
        "φ → ( χ ↔ ( φ ∧ χ ) )",
        ref="ibar",
        note="ibar",
    )

    # bitr4d: ( φ → ( ψ ↔ ( φ ∧ χ ) ) ), ( φ → ( χ ↔ ( φ ∧ χ ) ) )
    # |- ( φ → ( ψ ↔ χ ) )
    res = lb.ref(
        "res",
        "φ → ( ψ ↔ χ )",
        h1,
        s_ibar,
        ref="bitr4d",
        note="bitr4d",
    )

    return lb.build(res)


def prove_nbn2(sys: System) -> Proof:
    """nbn2: ¬ φ → ( ¬ ψ ↔ ( φ ↔ ψ ) ).

    From ¬ φ, deduce that ¬ ψ is equivalent to φ ↔ ψ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "nbn2")

    # pm5.501: ( φ → ( ψ ↔ ( φ ↔ ψ ) ) )
    # With ¬ φ for φ and ¬ ψ for ψ:
    # ( ¬ φ → ( ¬ ψ ↔ ( ¬ φ ↔ ¬ ψ ) ) )
    s1 = lb.ref(
        "s1",
        "( ¬ φ → ( ¬ ψ ↔ ( ¬ φ ↔ ¬ ψ ) ) )",
        ref="pm5.501",
        note="pm5.501",
    )

    # notbi: ( ( φ ↔ ψ ) ↔ ( ¬ φ ↔ ¬ ψ ) )
    s2 = lb.ref(
        "s2",
        "( ( φ ↔ ψ ) ↔ ( ¬ φ ↔ ¬ ψ ) )",
        ref="notbi",
        note="notbi",
    )

    # bitr4di: ( ph → ( ps ↔ ch ) ), ( th ↔ ch ) → ( ph → ( ps ↔ th ) )
    # With ph = ¬ φ, ps = ¬ ψ, ch = ( ¬ φ ↔ ¬ ψ ), th = ( φ ↔ ψ )
    res = lb.ref(
        "res",
        "( ¬ φ → ( ¬ ψ ↔ ( φ ↔ ψ ) ) )",
        s1,
        s2,
        ref="bitr4di",
        note="bitr4di",
    )

    return lb.build(res)


def prove_nbn(sys: System) -> Proof:
    """nbn: ( ¬ ψ ↔ ( ψ ↔ φ ) ).

    Conclude that ¬ ψ is equivalent to ψ ↔ φ, given ¬ φ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "nbn")

    # Hypothesis: ¬ φ
    h1 = lb.hyp("nbn.1", "¬ φ")

    # bibif: ( ¬ φ → ( ( ψ ↔ φ ) ↔ ¬ ψ ) )
    s1 = lb.ref(
        "s1",
        "( ¬ φ → ( ( ψ ↔ φ ) ↔ ¬ ψ ) )",
        ref="bibif",
        note="bibif",
    )

    # ax-mp: from ¬ φ and ( ¬ φ → ( ( ψ ↔ φ ) ↔ ¬ ψ ) ), get ( ( ψ ↔ φ ) ↔ ¬ ψ )
    s2 = lb.mp(
        "s2",
        h1,
        s1,
        "MP hyp1, bibif",
    )

    # bicomi: commute ( ( ψ ↔ φ ) ↔ ¬ ψ ) to ( ¬ ψ ↔ ( ψ ↔ φ ) )
    res = lb.ref(
        "res",
        "( ¬ ψ ↔ ( ψ ↔ φ ) )",
        s2,
        ref="bicomi",
        note="bicomi",
    )

    return lb.build(res)


def prove_nbn3(sys: System) -> Proof:
    """nbn3: ( ¬ ψ ↔ ( ψ ↔ ¬ φ ) ).

    From φ, conclude that ¬ ψ is equivalent to ψ ↔ ¬ φ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "nbn3")

    # Hypothesis: φ
    h1 = lb.hyp("nbn3.1", "φ")

    # notnoti: from φ, get ¬ ¬ φ
    s1 = lb.ref("s1", "¬ ¬ φ", h1, ref="notnoti", note="notnoti")

    # nbn: ( ¬ ψ ↔ ( ψ ↔ φ ) ), with ¬ φ as hypothesis
    # Substituting φ := ¬ φ matches s1 and gives the target conclusion
    res = lb.ref(
        "res",
        "( ¬ ψ ↔ ( ψ ↔ ¬ φ ) )",
        s1,
        ref="nbn",
        note="nbn",
    )

    return lb.build(res)


def prove_pm5_21im(sys: System) -> Proof:
    """pm5.21im: ¬ φ → ( ¬ ψ → ( φ ↔ ψ ) ).

    The identity of a proposition with a false proposition follows from
    the negation of the false proposition.  In particular, from
    ¬ φ, deduce that ¬ ψ implies φ ↔ ψ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm5.21im")

    # nbn2: ¬ φ → ( ¬ ψ ↔ ( φ ↔ ψ ) )
    s1 = lb.ref(
        "s1",
        "( ¬ φ → ( ¬ ψ ↔ ( φ ↔ ψ ) ) )",
        ref="nbn2",
        note="nbn2",
    )

    # biimpd: ( φ → ( ψ ↔ χ ) ) ⊢ ( φ → ( ψ → χ ) ), with
    # φ := ¬ φ, ψ := ¬ ψ, χ := ( φ ↔ ψ )
    res = lb.ref(
        "res",
        "( ¬ φ → ( ¬ ψ → ( φ ↔ ψ ) ) )",
        s1,
        ref="biimpd",
        note="biimpd",
    )
    return lb.build(res)


def prove_pm5_21ndd(sys: System) -> Proof:
    """pm5.21ndd: φ → (χ ↔ θ).

    Deduction form of pm5.21im, using con3d for contraposition,
    syl6c for nested modus ponens, and pm2.61d to eliminate ¬ ψ.
    (Contributed by NM, 27-Apr-1994.)
    """
    lb = ProofBuilder(sys, "pm5.21ndd")

    h1 = lb.hyp("pm5.21ndd.1", "φ → ( χ → ψ )")
    h2 = lb.hyp("pm5.21ndd.2", "φ → ( θ → ψ )")
    h3 = lb.hyp("pm5.21ndd.3", "φ → ( ψ → ( χ ↔ θ ) )")

    # con3d: φ → ( χ → ψ ) ⊢ φ → ( ¬ ψ → ¬ χ )
    s1 = lb.ref(
        "s1",
        "φ → ( ¬ ψ → ¬ χ )",
        h1,
        ref="con3d",
        note="con3d",
    )

    # con3d: φ → ( θ → ψ ) ⊢ φ → ( ¬ ψ → ¬ θ )
    s2 = lb.ref(
        "s2",
        "φ → ( ¬ ψ → ¬ θ )",
        h2,
        ref="con3d",
        note="con3d",
    )

    # pm5.21im: ¬ χ → ( ¬ θ → ( χ ↔ θ ) )
    s3 = lb.ref(
        "s3",
        "¬ χ → ( ¬ θ → ( χ ↔ θ ) )",
        ref="pm5.21im",
        note="pm5.21im",
    )

    # syl6c with s1, s2, s3: φ → ( ¬ ψ → ( χ ↔ θ ) )
    s4 = lb.ref(
        "s4",
        "φ → ( ¬ ψ → ( χ ↔ θ ) )",
        s1,
        s2,
        s3,
        ref="syl6c",
        note="syl6c",
    )

    # pm2.61d with h3, s4: φ → ( χ ↔ θ )
    res = lb.ref(
        "res",
        "φ → ( χ ↔ θ )",
        h3,
        s4,
        ref="pm2.61d",
        note="pm2.61d",
    )

    return lb.build(res)


def prove_pm5_21nd(sys: System) -> Proof:
    """pm5.21nd: φ → (ψ ↔ χ).

    Deduction form of pm5.21ndd, using exportation to convert the
    conjunctive hypotheses into implicational form.
    (Contributed by NM, 8-Oct-1992.)
    """
    lb = ProofBuilder(sys, "pm5.21nd")

    h1 = lb.hyp("pm5.21nd.1", "( φ ∧ ψ ) → θ")
    h2 = lb.hyp("pm5.21nd.2", "( φ ∧ χ ) → θ")
    h3 = lb.hyp("pm5.21nd.3", "θ → ( ψ ↔ χ )")

    # ex: ( φ ∧ ψ ) → θ ⊢ φ → ( ψ → θ )
    s1 = lb.ref("s1", "φ → ( ψ → θ )", h1, ref="ex", note="ex")

    # ex: ( φ ∧ χ ) → θ ⊢ φ → ( χ → θ )
    s2 = lb.ref("s2", "φ → ( χ → θ )", h2, ref="ex", note="ex")

    # a1i: θ → ( ψ ↔ χ ) ⊢ φ → ( θ → ( ψ ↔ χ ) )
    s3 = lb.ref("s3", "φ → ( θ → ( ψ ↔ χ ) )", h3, ref="a1i", note="a1i")

    # pm5.21ndd with s1, s2, s3: φ → ( ψ ↔ χ )
    res = lb.ref("res", "φ → ( ψ ↔ χ )", s1, s2, s3, ref="pm5.21ndd", note="pm5.21ndd")

    return lb.build(res)


def prove_bibif(sys: System) -> Proof:
    """bibif: ( ¬ ψ → ( ( φ ↔ ψ ) ↔ ¬ φ ) ).

    The negation of an antecedent: the biconditional of the consequent
    with the negated antecedent is equivalent to the negated antecedent.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "bibif")

    # nbn2: ¬ φ → ( ¬ ψ ↔ ( φ ↔ ψ ) )
    # Substitute φ ↦ ψ, ψ ↦ φ: ¬ ψ → ( ¬ φ ↔ ( ψ ↔ φ ) )
    s1 = lb.ref(
        "s1",
        "( ¬ ψ → ( ¬ φ ↔ ( ψ ↔ φ ) ) )",
        ref="nbn2",
        note="nbn2",
    )

    # bicom: ( ( ψ ↔ φ ) ↔ ( φ ↔ ψ ) )
    s2 = lb.ref(
        "s2",
        "( ( ψ ↔ φ ) ↔ ( φ ↔ ψ ) )",
        ref="bicom",
        note="bicom",
    )

    # bitr2di: ( ¬ ψ → ( ( φ ↔ ψ ) ↔ ¬ φ ) )
    res = lb.ref(
        "res",
        "( ¬ ψ → ( ( φ ↔ ψ ) ↔ ¬ φ ) )",
        s1,
        s2,
        ref="bitr2di",
        note="bitr2di",
    )

    return lb.build(res)


def prove_xchnxbi(sys: System) -> Proof:
    """xchnxbi: ( ¬ χ ↔ ψ ).

    Swap a biconditional and negate the swapped-out variable using two
    given equivalences.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "xchnxbi")

    h1 = lb.hyp("xchnxbi.1", "( ¬ φ ↔ ψ )")
    h2 = lb.hyp("xchnxbi.2", "( φ ↔ χ )")

    # notbii applied to h2: ( ¬ φ ↔ ¬ χ )
    s1 = lb.ref(
        "s1",
        "( ¬ φ ↔ ¬ χ )",
        h2,
        ref="notbii",
        note="notbii",
    )

    # bitr3i with h1 and s1: ( ψ ↔ ¬ χ )
    s2 = lb.ref(
        "s2",
        "( ψ ↔ ¬ χ )",
        h1,
        s1,
        ref="bitr3i",
        note="bitr3i",
    )

    # bicomi to swap: ( ¬ χ ↔ ψ )
    res = lb.ref(
        "res",
        "( ¬ χ ↔ ψ )",
        s2,
        ref="bicomi",
        note="bicomi",
    )

    return lb.build(res)


def prove_xchnxbir(sys: System) -> Proof:
    """xchnxbir: ( ¬ χ ↔ ψ ).

    Swap a biconditional and negate the swapped-out variable using two
    given equivalences, commuted biconditional form.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "xchnxbir")

    h1 = lb.hyp("xchnxbir.1", "( ¬ φ ↔ ψ )")
    h2 = lb.hyp("xchnxbir.2", "( χ ↔ φ )")

    # bicomi applied to h2: ( φ ↔ χ )
    s1 = lb.ref(
        "s1",
        "( φ ↔ χ )",
        h2,
        ref="bicomi",
        note="bicomi",
    )

    # xchnxbi with h1 and s1: ( ¬ χ ↔ ψ )
    res = lb.ref(
        "res",
        "( ¬ χ ↔ ψ )",
        h1,
        s1,
        ref="xchnxbi",
        note="xchnxbi",
    )

    return lb.build(res)


def prove_xchbinx(sys: System) -> Proof:
    """xchbinx: ( φ ↔ ¬ χ ).

    Swap a biconditional and negate the swapped-in variable using two
    given equivalences.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "xchbinx")

    h1 = lb.hyp("xchbinx.1", "( φ ↔ ¬ ψ )")
    h2 = lb.hyp("xchbinx.2", "( ψ ↔ χ )")

    # notbii applied to h2: ( ¬ ψ ↔ ¬ χ )
    s1 = lb.ref(
        "s1",
        "( ¬ ψ ↔ ¬ χ )",
        h2,
        ref="notbii",
        note="notbii",
    )

    # bitri with h1 and s1: ( φ ↔ ¬ χ )
    res = lb.ref(
        "res",
        "( φ ↔ ¬ χ )",
        h1,
        s1,
        ref="bitri",
        note="bitri",
    )

    return lb.build(res)


def prove_xchbinxr(sys: System) -> Proof:
    """xchbinxr: ( φ ↔ ¬ χ ).

    Swap a biconditional and negate the swapped-in variable using two
    given equivalences, commuted form.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "xchbinxr")

    h1 = lb.hyp("xchbinxr.1", "( φ ↔ ¬ ψ )")
    h2 = lb.hyp("xchbinxr.2", "( χ ↔ ψ )")

    # bicomi applied to h2: ( ψ ↔ χ )
    s1 = lb.ref(
        "s1",
        "( ψ ↔ χ )",
        h2,
        ref="bicomi",
        note="bicomi",
    )

    # xchbinx with h1 and s1: ( φ ↔ ¬ χ )
    res = lb.ref(
        "res",
        "( φ ↔ ¬ χ )",
        h1,
        s1,
        ref="xchbinx",
        note="xchbinx",
    )

    return lb.build(res)


def prove_mpbiran(sys: System) -> Proof:
    """mpbiran: φ ↔ χ.

    An inference from a biconditional and a conjunction: given ψ and
    φ ↔ (ψ ∧ χ), conclude φ ↔ χ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "mpbiran")

    h1 = lb.hyp("mpbiran.1", "ψ")
    h2 = lb.hyp("mpbiran.2", "φ ↔ ( ψ ∧ χ )")

    # biantrur: with hyp ψ, gives χ ↔ ( ψ ∧ χ )
    s1 = lb.ref("s1", "χ ↔ ( ψ ∧ χ )", h1, ref="biantrur", note="biantrur")

    # bitr4i: φ ↔ ( ψ ∧ χ ), χ ↔ ( ψ ∧ χ )  →  φ ↔ χ
    res = lb.ref("res", "φ ↔ χ", h2, s1, ref="bitr4i", note="bitr4i")

    return lb.build(res)


def prove_mpbiran2(sys: System) -> Proof:
    """mpbiran2: φ ↔ ψ.

    An inference from a biconditional and a conjunction: given χ and
    φ ↔ (ψ ∧ χ), conclude φ ↔ ψ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "mpbiran2")

    h1 = lb.hyp("mpbiran2.1", "χ")
    h2 = lb.hyp("mpbiran2.2", "φ ↔ ( ψ ∧ χ )")

    # biancomi: φ ↔ ( ψ ∧ χ ) → φ ↔ ( χ ∧ ψ )
    s1 = lb.ref("s1", "φ ↔ ( χ ∧ ψ )", h2, ref="biancomi", note="biancomi")

    # mpbiran: χ, φ ↔ ( χ ∧ ψ ) → φ ↔ ψ
    res = lb.ref("res", "φ ↔ ψ", h1, s1, ref="mpbiran", note="mpbiran")

    return lb.build(res)


def prove_xorcom(sys: System) -> Proof:
    """xorcom: ( φ ⊻ ψ ) ↔ ( ψ ⊻ φ ).

    Commutation of exclusive or: XOR is commutative.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "xorcom")

    # df-xor: ( φ ⊻ ψ ) ↔ ¬( φ ↔ ψ )
    s1 = lb.ref(
        "s1",
        "( φ ⊻ ψ ) ↔ ¬ ( φ ↔ ψ )",
        ref="df-xor",
        note="df-xor",
    )

    # bicom: ( φ ↔ ψ ) ↔ ( ψ ↔ φ )
    s2 = lb.ref(
        "s2",
        "( φ ↔ ψ ) ↔ ( ψ ↔ φ )",
        ref="bicom",
        note="bicom",
    )

    # df-xor (swapped): ( ψ ⊻ φ ) ↔ ¬( ψ ↔ φ )
    s3 = lb.ref(
        "s3",
        "( ψ ⊻ φ ) ↔ ¬ ( ψ ↔ φ )",
        ref="df-xor",
        note="df-xor",
    )

    # xchbinx with s1 and s2: ( φ ⊻ ψ ) ↔ ¬( ψ ↔ φ )
    s4 = lb.ref(
        "s4",
        "( φ ⊻ ψ ) ↔ ¬ ( ψ ↔ φ )",
        s1,
        s2,
        ref="xchbinx",
        note="xchbinx",
    )

    # bitr4i with s4 and s3: ( φ ⊻ ψ ) ↔ ( ψ ⊻ φ )
    res = lb.ref(
        "res",
        "( φ ⊻ ψ ) ↔ ( ψ ⊻ φ )",
        s4,
        s3,
        ref="bitr4i",
        note="bitr4i",
    )

    return lb.build(res)


def prove_xnor(sys: System) -> Proof:
    """xnor: ( φ ↔ ψ ) ↔ ¬ ( φ ⊻ ψ ).

    Express XNOR (↔) in terms of XOR (⊻) via negation.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "xnor")

    # df-xor: ( φ ⊻ ψ ) ↔ ¬ ( φ ↔ ψ )
    dfxor = lb.ref(
        "dfxor",
        "( φ ⊻ ψ ) ↔ ¬ ( φ ↔ ψ )",
        ref="df-xor",
        note="df-xor",
    )

    # con2bii: ( A ↔ ¬ B ) ⊢ ( B ↔ ¬ A )
    # with A = ( φ ⊻ ψ ), B = ( φ ↔ ψ )
    res = lb.ref(
        "res",
        "( φ ↔ ψ ) ↔ ¬ ( φ ⊻ ψ )",
        dfxor,
        ref="con2bii",
        note="con2bii",
    )

    return lb.build(res)


def prove_xorbi12i(sys: System) -> Proof:
    """xorbi12i: ( φ ⊻ χ ) ↔ ( ψ ⊻ θ ).

    Inference form: from ( φ ↔ ψ ) and ( χ ↔ θ ),
    deduce the biconditional of XORs.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "xorbi12i")
    h1 = lb.hyp("xorbi12.1", "( φ ↔ ψ )")
    h2 = lb.hyp("xorbi12.2", "( χ ↔ θ )")

    # df-xor: ( φ ⊻ χ ) ↔ ¬ ( φ ↔ χ )
    s1 = lb.ref(
        "s1",
        "( φ ⊻ χ ) ↔ ¬ ( φ ↔ χ )",
        ref="df-xor",
        note="df-xor",
    )

    # df-xor: ( ψ ⊻ θ ) ↔ ¬ ( ψ ↔ θ )
    s2 = lb.ref(
        "s2",
        "( ψ ⊻ θ ) ↔ ¬ ( ψ ↔ θ )",
        ref="df-xor",
        note="df-xor",
    )

    # bibi12i: ( ( φ ↔ χ ) ↔ ( ψ ↔ θ ) )
    s3 = lb.ref(
        "s3",
        "( ( φ ↔ χ ) ↔ ( ψ ↔ θ ) )",
        h1,
        h2,
        ref="bibi12i",
        note="bibi12i",
    )

    # xchbinx: ( φ ⊻ χ ) ↔ ¬ ( ψ ↔ θ )
    s4 = lb.ref(
        "s4",
        "( φ ⊻ χ ) ↔ ¬ ( ψ ↔ θ )",
        s1,
        s3,
        ref="xchbinx",
        note="xchbinx",
    )

    # bitr4i: ( φ ⊻ χ ) ↔ ( ψ ⊻ θ )
    res = lb.ref(
        "res",
        "( φ ⊻ χ ) ↔ ( ψ ⊻ θ )",
        s4,
        s2,
        ref="bitr4i",
        note="bitr4i",
    )

    return lb.build(res)


def prove_xorbi12d(sys: System) -> Proof:
    """xorbi12d: φ → ((ψ ⊻ θ) ↔ (χ ⊻ τ)).

    Deduction form of xorbi12i: deduce the biconditional of XORs
    from two biconditional deductions.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "xorbi12d")
    h1 = lb.hyp("xor12d.1", "( φ → ( ψ ↔ χ ) )")
    h2 = lb.hyp("xor12d.2", "( φ → ( θ ↔ τ ) )")

    # bibi12d: ( φ → ( ( ψ ↔ θ ) ↔ ( χ ↔ τ ) ) )
    s1 = lb.ref(
        "s1",
        "( φ → ( ( ψ ↔ θ ) ↔ ( χ ↔ τ ) ) )",
        h1,
        h2,
        ref="bibi12d",
        note="bibi12d",
    )

    # notbid: ( φ → ( ¬ ( ψ ↔ θ ) ↔ ¬ ( χ ↔ τ ) ) )
    s2 = lb.ref(
        "s2",
        "( φ → ( ¬ ( ψ ↔ θ ) ↔ ¬ ( χ ↔ τ ) ) )",
        s1,
        ref="notbid",
        note="notbid",
    )

    # df-xor: ( ψ ⊻ θ ) ↔ ¬ ( ψ ↔ θ )
    s3 = lb.ref(
        "s3",
        "( ψ ⊻ θ ) ↔ ¬ ( ψ ↔ θ )",
        ref="df-xor",
        note="df-xor",
    )

    # df-xor: ( χ ⊻ τ ) ↔ ¬ ( χ ↔ τ )
    s4 = lb.ref(
        "s4",
        "( χ ⊻ τ ) ↔ ¬ ( χ ↔ τ )",
        ref="df-xor",
        note="df-xor",
    )

    # 3bitr4g: combine s2, s3, s4
    res = lb.ref(
        "res",
        "( φ → ( ( ψ ⊻ θ ) ↔ ( χ ⊻ τ ) ) )",
        s2,
        s3,
        s4,
        ref="3bitr4g",
        note="3bitr4g",
    )

    return lb.build(res)


def prove_nan(sys: System) -> Proof:
    """nan: (φ → ¬ (ψ ∧ χ)) ↔ ((φ ∧ ψ) → ¬ χ).

    Express implication of negated conjunction as negated consequent
    of conjoined antecedents.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "nan")

    # impexp: (((φ ∧ ψ) → χ) ↔ (φ → (ψ → χ))) with χ := ¬ χ
    s1 = lb.ref(
        "s1",
        "((φ ∧ ψ) → ¬ χ) ↔ (φ → (ψ → ¬ χ))",
        ref="impexp",
        note="impexp",
    )

    # imnan: (φ → ¬ ψ) ↔ ¬ (φ ∧ ψ) with φ := ψ, ψ := χ
    s2 = lb.ref(
        "s2",
        "(ψ → ¬ χ) ↔ ¬ (ψ ∧ χ)",
        ref="imnan",
        note="imnan",
    )

    # imbi2i: from s2, (φ → (ψ → ¬ χ)) ↔ (φ → ¬ (ψ ∧ χ))
    s3 = lb.ref(
        "s3",
        "(φ → (ψ → ¬ χ)) ↔ (φ → ¬ (ψ ∧ χ))",
        s2,
        ref="imbi2i",
        note="imbi2i",
    )

    # bitr2i: from s1 and s3, (φ → ¬ (ψ ∧ χ)) ↔ ((φ ∧ ψ) → ¬ χ)
    res = lb.ref(
        "res",
        "(φ → ¬ (ψ ∧ χ)) ↔ ((φ ∧ ψ) → ¬ χ)",
        s1,
        s3,
        ref="bitr2i",
        note="bitr2i",
    )

    return lb.build(res)


def prove_dfnan2(sys: System) -> Proof:
    """dfnan2: ( φ ⊼ ψ ) ↔ ( φ → ¬ ψ ).

    Express NAND (negated conjunction) as implication of a negated consequent.
    """
    lb = ProofBuilder(sys, "dfnan2")

    # df-nan: ( φ ⊼ ψ ) ↔ ¬ ( φ ∧ ψ )
    s1 = lb.ref(
        "s1",
        "( φ ⊼ ψ ) ↔ ¬ ( φ ∧ ψ )",
        ref="df-nan",
        note="df-nan",
    )

    # imnan: ( φ → ¬ ψ ) ↔ ¬ ( φ ∧ ψ )
    s2 = lb.ref(
        "s2",
        "( φ → ¬ ψ ) ↔ ¬ ( φ ∧ ψ )",
        ref="imnan",
        note="imnan",
    )

    # bitr4i: from s1 (A ↔ B) and s2 (C ↔ B), conclude A ↔ C
    res = lb.ref(
        "res",
        "( φ ⊼ ψ ) ↔ ( φ → ¬ ψ )",
        s1,
        s2,
        ref="bitr4i",
        note="bitr4i",
    )

    return lb.build(res)


def prove_nanbi1(sys: System) -> Proof:
    """nanbi1: ( φ ↔ ψ ) → ( ( φ ⊼ χ ) ↔ ( ψ ⊼ χ ) ).

    The NAND connective respects biconditional equivalence in the first
    argument.
    """
    lb = ProofBuilder(sys, "nanbi1")

    # imbi1: ( φ ↔ ψ ) → ( ( φ → ¬ χ ) ↔ ( ψ → ¬ χ ) )
    s1 = lb.ref(
        "s1",
        "( ( φ ↔ ψ ) → ( ( φ → ¬ χ ) ↔ ( ψ → ¬ χ ) ) )",
        ref="imbi1",
        note="imbi1",
    )

    # dfnan2: ( φ ⊼ χ ) ↔ ( φ → ¬ χ )
    s2 = lb.ref(
        "s2",
        "( φ ⊼ χ ) ↔ ( φ → ¬ χ )",
        ref="dfnan2",
        note="dfnan2",
    )

    # dfnan2: ( ψ ⊼ χ ) ↔ ( ψ → ¬ χ )
    s3 = lb.ref(
        "s3",
        "( ψ ⊼ χ ) ↔ ( ψ → ¬ χ )",
        ref="dfnan2",
        note="dfnan2",
    )

    # 3bitr4g: combine s1, s2, s3
    res = lb.ref(
        "res",
        "( φ ↔ ψ ) → ( ( φ ⊼ χ ) ↔ ( ψ ⊼ χ ) )",
        s1,
        s2,
        s3,
        ref="3bitr4g",
        note="3bitr4g",
    )

    return lb.build(res)


def prove_nanbi1i(sys: System) -> Proof:
    """nanbi1i: ( φ ⊼ χ ) ↔ ( ψ ⊼ χ ).

    Inference form of nanbi1.
    """
    lb = ProofBuilder(sys, "nanbi1i")
    h1 = lb.hyp("nanbi1i.1", "( φ ↔ ψ )")
    s1 = lb.ref(
        "s1",
        "( ( φ ↔ ψ ) → ( ( φ ⊼ χ ) ↔ ( ψ ⊼ χ ) ) )",
        ref="nanbi1",
        note="nanbi1",
    )
    res = lb.mp("res", h1, s1, "MP hyp1, nanbi1")
    return lb.build(res)


def prove_nanbi1d(sys: System) -> Proof:
    """nanbi1d: φ → ( ( ψ ⊼ θ ) ↔ ( χ ⊼ θ ) ).

    Deduction form of nanbi1.
    """
    lb = ProofBuilder(sys, "nanbi1d")

    # nanbid.1: φ → ( ψ ↔ χ )
    h1 = lb.hyp("nanbid.1", "( φ → ( ψ ↔ χ ) )")

    # nanbi1: ( ψ ↔ χ ) → ( ( ψ ⊼ θ ) ↔ ( χ ⊼ θ ) )
    s1 = lb.ref(
        "s1",
        "( ( ψ ↔ χ ) → ( ( ψ ⊼ θ ) ↔ ( χ ⊼ θ ) ) )",
        ref="nanbi1",
        note="nanbi1",
    )

    # syl: φ → ( ψ ↔ χ ) , ( ψ ↔ χ ) → ( ( ψ ⊼ θ ) ↔ ( χ ⊼ θ ) )
    #    ⇒ φ → ( ( ψ ⊼ θ ) ↔ ( χ ⊼ θ ) )
    res = lb.ref(
        "res",
        "( φ → ( ( ψ ⊼ θ ) ↔ ( χ ⊼ θ ) ) )",
        h1,
        s1,
        ref="syl",
        note="syl hyp, nanbi1",
    )
    return lb.build(res)


def prove_nancom(sys: System) -> Proof:
    """nancom: ( φ ⊼ ψ ) ↔ ( ψ ⊼ φ ).

    NAND is commutative.
    """
    lb = ProofBuilder(sys, "nancom")

    # con2b: ( ( φ → ¬ ψ ) ↔ ( ψ → ¬ φ ) )
    s1 = lb.ref(
        "s1",
        "( ( φ → ¬ ψ ) ↔ ( ψ → ¬ φ ) )",
        ref="con2b",
        note="con2b",
    )

    # dfnan2: ( φ ⊼ ψ ) ↔ ( φ → ¬ ψ )
    s2 = lb.ref(
        "s2",
        "( φ ⊼ ψ ) ↔ ( φ → ¬ ψ )",
        ref="dfnan2",
        note="dfnan2",
    )

    # dfnan2 with φ, ψ swapped: ( ψ ⊼ φ ) ↔ ( ψ → ¬ φ )
    s3 = lb.ref(
        "s3",
        "( ψ ⊼ φ ) ↔ ( ψ → ¬ φ )",
        ref="dfnan2",
        note="dfnan2",
    )

    # 3bitr4i: from s1 (bridge), s2 (left ↔ left), s3 (right ↔ right)
    res = lb.ref(
        "res",
        "( φ ⊼ ψ ) ↔ ( ψ ⊼ φ )",
        s1,
        s2,
        s3,
        ref="3bitr4i",
        note="3bitr4i",
    )

    return lb.build(res)


def prove_nanbi2(sys: System) -> Proof:
    """nanbi2: ( φ ↔ ψ ) → ( ( χ ⊼ φ ) ↔ ( χ ⊼ ψ ) ).

    The NAND connective respects biconditional equivalence in the second
    argument.
    """
    lb = ProofBuilder(sys, "nanbi2")

    # nanbi1: ( φ ↔ ψ ) → ( ( φ ⊼ χ ) ↔ ( ψ ⊼ χ ) )
    s1 = lb.ref(
        "s1",
        "( φ ↔ ψ ) → ( ( φ ⊼ χ ) ↔ ( ψ ⊼ χ ) )",
        ref="nanbi1",
        note="nanbi1",
    )

    # nancom: ( χ ⊼ φ ) ↔ ( φ ⊼ χ )
    s2 = lb.ref(
        "s2",
        "( χ ⊼ φ ) ↔ ( φ ⊼ χ )",
        ref="nancom",
        note="nancom",
    )

    # nancom: ( χ ⊼ ψ ) ↔ ( ψ ⊼ χ )
    s3 = lb.ref(
        "s3",
        "( χ ⊼ ψ ) ↔ ( ψ ⊼ χ )",
        ref="nancom",
        note="nancom",
    )

    # 3bitr4g: combine s1, s2, s3
    res = lb.ref(
        "res",
        "( φ ↔ ψ ) → ( ( χ ⊼ φ ) ↔ ( χ ⊼ ψ ) )",
        s1,
        s2,
        s3,
        ref="3bitr4g",
        note="3bitr4g",
    )

    return lb.build(res)


def prove_nanbi2i(sys: System) -> Proof:
    """nanbi2i: ( χ ⊼ φ ) ↔ ( χ ⊼ ψ ).

    Inference form of nanbi2.
    """
    lb = ProofBuilder(sys, "nanbi2i")
    h1 = lb.hyp("nanbii.1", "( φ ↔ ψ )")
    s1 = lb.ref(
        "s1",
        "( ( φ ↔ ψ ) → ( ( χ ⊼ φ ) ↔ ( χ ⊼ ψ ) ) )",
        ref="nanbi2",
        note="nanbi2",
    )
    res = lb.mp("res", h1, s1, "MP hyp1, nanbi2")
    return lb.build(res)


def prove_nanbi2d(sys: System) -> Proof:
    """nanbi2d: φ → ( ( θ ⊼ ψ ) ↔ ( θ ⊼ χ ) ).

    Deduction form of nanbi2.
    """
    lb = ProofBuilder(sys, "nanbi2d")

    # nanbid.1: φ → ( ψ ↔ χ )
    h1 = lb.hyp("nanbid.1", "( φ → ( ψ ↔ χ ) )")

    # nanbi2: ( ψ ↔ χ ) → ( ( θ ⊼ ψ ) ↔ ( θ ⊼ χ ) )
    s1 = lb.ref(
        "s1",
        "( ( ψ ↔ χ ) → ( ( θ ⊼ ψ ) ↔ ( θ ⊼ χ ) ) )",
        ref="nanbi2",
        note="nanbi2",
    )

    # syl: φ → ( ψ ↔ χ ) , ( ψ ↔ χ ) → ( ( θ ⊼ ψ ) ↔ ( θ ⊼ χ ) )
    #    ⇒ φ → ( ( θ ⊼ ψ ) ↔ ( θ ⊼ χ ) )
    res = lb.ref(
        "res",
        "( φ → ( ( θ ⊼ ψ ) ↔ ( θ ⊼ χ ) ) )",
        h1,
        s1,
        ref="syl",
        note="syl",
    )

    return lb.build(res)


def prove_ifpdfbi(sys: System) -> Proof:
    """ifpdfbi: ( φ ↔ ψ ) ↔ if- ( φ , ψ , ¬ ψ ).

    Equivalence of biconditional and conditional operator.
    """
    lb = ProofBuilder(sys, "ifpdfbi")

    # dfbi3: ( φ ↔ ψ ) ↔ ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ ¬ ψ ) )
    s1 = lb.ref(
        "s1",
        "( ( φ ↔ ψ ) ↔ ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ ¬ ψ ) ) )",
        ref="dfbi3",
        note="dfbi3",
    )

    # df-ifp with χ := ¬ ψ: if- φ ψ ( ¬ ψ ) ↔ ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ ¬ ψ ) )
    s2 = lb.ref(
        "s2",
        "( if- φ ψ ( ¬ ψ ) ↔ ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ ¬ ψ ) ) )",
        ref="df-ifp",
        note="df-ifp",
    )

    # bitr4i: combine them
    res = lb.ref(
        "res",
        "( ( φ ↔ ψ ) ↔ if- φ ψ ( ¬ ψ ) )",
        s1,
        s2,
        ref="bitr4i",
        note="bitr4i",
    )

    return lb.build(res)


def prove_ifpdfbiOLD(sys: System) -> Proof:
    """ifpdfbiOLD: ( φ ↔ ψ ) ↔ if- φ ψ ( ¬ ψ ).

    Equivalence of biconditional and conditional operator.
    (Proof modification is discouraged.)  (New usage is discouraged.)
    """
    lb = ProofBuilder(sys, "ifpdfbiOLD")

    # con34b: ( ( ψ → φ ) ↔ ( ¬ φ → ¬ ψ ) )
    s1 = lb.ref(
        "s1",
        "( ( ψ → φ ) ↔ ( ¬ φ → ¬ ψ ) )",
        ref="con34b",
        note="con34b",
    )

    # anbi2i with χ := ( φ → ψ )
    s2 = lb.ref(
        "s2",
        "( ( ( φ → ψ ) ∧ ( ψ → φ ) ) ↔ ( ( φ → ψ ) ∧ ( ¬ φ → ¬ ψ ) ) )",
        s1,
        ref="anbi2i",
        note="anbi2i(con34b)",
    )

    # dfbi2: ( ( φ ↔ ψ ) ↔ ( ( φ → ψ ) ∧ ( ψ → φ ) ) )
    s3 = lb.ref(
        "s3",
        "( ( φ ↔ ψ ) ↔ ( ( φ → ψ ) ∧ ( ψ → φ ) ) )",
        ref="dfbi2",
        note="dfbi2",
    )

    # dfifp2 with χ := ¬ ψ
    s4 = lb.ref(
        "s4",
        "( if- φ ψ ( ¬ ψ ) ↔ ( ( φ → ψ ) ∧ ( ¬ φ → ¬ ψ ) ) )",
        ref="dfifp2",
        note="dfifp2",
    )

    # 3bitr4i: combine s2, s3, s4
    res = lb.ref(
        "res",
        "( ( φ ↔ ψ ) ↔ if- φ ψ ( ¬ ψ ) )",
        s2,
        s3,
        s4,
        ref="3bitr4i",
        note="3bitr4i",
    )

    return lb.build(res)


def prove_ifptru(sys: System) -> Proof:
    """ifptru: φ → ( if- ( φ , ψ , χ ) ↔ ψ ).

    If the first argument of the conditional operator is true, then
    the conditional reduces to the second argument.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "ifptru")

    # biimt: φ → ( ψ ↔ ( φ → ψ ) )
    s1 = lb.ref(
        "s1",
        "φ → ( ψ ↔ ( φ → ψ ) )",
        ref="biimt",
        note="biimt",
    )

    # orc: φ → ( φ ∨ χ )
    s2 = lb.ref(
        "s2",
        "φ → ( φ ∨ χ )",
        ref="orc",
        note="orc",
    )

    # biantrud: φ → ( ( φ → ψ ) ↔ ( ( φ → ψ ) ∧ ( φ ∨ χ ) ) )
    s3 = lb.ref(
        "s3",
        "φ → ( ( φ → ψ ) ↔ ( ( φ → ψ ) ∧ ( φ ∨ χ ) ) )",
        s2,
        ref="biantrud",
        note="biantrud",
    )

    # dfifp3: ( if- φ ψ χ ↔ ( ( φ → ψ ) ∧ ( φ ∨ χ ) ) )
    s4 = lb.ref(
        "s4",
        "( if- φ ψ χ ↔ ( ( φ → ψ ) ∧ ( φ ∨ χ ) ) )",
        ref="dfifp3",
        note="dfifp3",
    )

    # bitr4di: φ → ( ( φ → ψ ) ↔ if- φ ψ χ )
    s5 = lb.ref(
        "s5",
        "φ → ( ( φ → ψ ) ↔ if- φ ψ χ )",
        s3,
        s4,
        ref="bitr4di",
        note="bitr4di",
    )

    # bitr2d: φ → ( if- φ ψ χ ↔ ψ )
    res = lb.ref(
        "res",
        "φ → ( if- φ ψ χ ↔ ψ )",
        s1,
        s5,
        ref="bitr2d",
        note="bitr2d",
    )

    return lb.build(res)


def prove_ifpn(sys: System) -> Proof:
    """ifpn: ( if- φ ψ χ ↔ if- ( ¬ φ ) χ ψ ).

    The conditional operator is invariant under swapping its second and
    third arguments together with negation of the first.
    (Contributed by NM, 30-Sep-2014.)
    """
    lb = ProofBuilder(sys, "ifpn")

    # dfifp5: ( if- φ ψ χ ↔ ( ( ¬ φ ∨ ψ ) ∧ ( ¬ φ → χ ) ) )
    s1 = lb.ref(
        "s1",
        "( if- φ ψ χ ↔ ( ( ¬ φ ∨ ψ ) ∧ ( ¬ φ → χ ) ) )",
        ref="dfifp5",
        note="dfifp5",
    )

    # ancom: ( ( ( ¬ φ ∨ ψ ) ∧ ( ¬ φ → χ ) ) ↔ ( ( ¬ φ → χ ) ∧ ( ¬ φ ∨ ψ ) ) )
    s2 = lb.ref(
        "s2",
        "( ( ( ¬ φ ∨ ψ ) ∧ ( ¬ φ → χ ) ) ↔ ( ( ¬ φ → χ ) ∧ ( ¬ φ ∨ ψ ) ) )",
        ref="ancom",
        note="ancom",
    )

    # dfifp3: ( if- ( ¬ φ ) χ ψ ↔ ( ( ¬ φ → χ ) ∧ ( ¬ φ ∨ ψ ) ) )
    s3 = lb.ref(
        "s3",
        "( if- ( ¬ φ ) χ ψ ↔ ( ( ¬ φ → χ ) ∧ ( ¬ φ ∨ ψ ) ) )",
        ref="dfifp3",
        note="dfifp3",
    )

    # 3bitr4i: combine s2 (bridge), s1 (left), s3 (right)
    res = lb.ref(
        "res",
        "( if- φ ψ χ ↔ if- ( ¬ φ ) χ ψ )",
        s2,
        s1,
        s3,
        ref="3bitr4i",
        note="3bitr4i",
    )

    return lb.build(res)


def prove_ifpfal(sys: System) -> Proof:
    """ifpfal: ¬ φ → ( if- ( φ , ψ , χ ) ↔ χ ).

    If the first argument of the conditional operator is false, then
    the conditional reduces to the third argument.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "ifpfal")

    # ifpn: ( if- φ ψ χ ↔ if- ( ¬ φ ) χ ψ )
    s1 = lb.ref(
        "s1",
        "( if- φ ψ χ ↔ if- ( ¬ φ ) χ ψ )",
        ref="ifpn",
        note="ifpn",
    )

    # ifptru: ( ¬ φ → ( if- ( ¬ φ ) χ ψ ↔ χ ) )
    s2 = lb.ref(
        "s2",
        "( ¬ φ → ( if- ( ¬ φ ) χ ψ ↔ χ ) )",
        ref="ifptru",
        note="ifptru",
    )

    # bitrid: ( if- φ ψ χ ↔ if- ( ¬ φ ) χ ψ ),
    # ( ¬ φ → ( if- ( ¬ φ ) χ ψ ↔ χ ) )
    # |- ( ¬ φ → ( if- φ ψ χ ↔ χ ) )
    res = lb.ref(
        "res",
        "( ¬ φ → ( if- φ ψ χ ↔ χ ) )",
        s1,
        s2,
        ref="bitrid",
        note="bitrid",
    )

    return lb.build(res)


def prove_ifpid(sys: System) -> Proof:
    """ifpid: ( if- φ ψ ψ ↔ ψ ).

    The conditional operator reduces to its second argument when the
    second and third arguments are the same.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "ifpid")

    # ifptru with χ := ψ: φ → ( if- φ ψ ψ ↔ ψ )
    s1 = lb.ref(
        "s1",
        "φ → ( if- φ ψ ψ ↔ ψ )",
        ref="ifptru",
        note="ifptru",
    )

    # ifpfal with χ := ψ: ¬ φ → ( if- φ ψ ψ ↔ ψ )
    s2 = lb.ref(
        "s2",
        "¬ φ → ( if- φ ψ ψ ↔ ψ )",
        ref="ifpfal",
        note="ifpfal",
    )

    # pm2.61i: ( if- φ ψ ψ ↔ ψ )
    res = lb.ref(
        "res",
        "( if- φ ψ ψ ↔ ψ )",
        s1,
        s2,
        ref="pm2.61i",
        note="pm2.61i",
    )

    return lb.build(res)


def prove_nanim(sys: System) -> Proof:
    """nanim: ( φ → ψ ) ↔ ( φ ⊼ ( ψ ⊼ ψ ) ).

    Implication expressed as NAND.
    """
    lb = ProofBuilder(sys, "nanim")

    # nannan (ψ/φ, ψ/ψ, χ/ψ): ( φ ⊼ ( ψ ⊼ ψ ) ) ↔ ( φ → ( ψ ∧ ψ ) )
    s1 = lb.ref(
        "s1",
        "( φ ⊼ ( ψ ⊼ ψ ) ) ↔ ( φ → ( ψ ∧ ψ ) )",
        ref="nannan",
        note="nannan",
    )

    # anidmdbi: ( φ → ( ψ ∧ ψ ) ) ↔ ( φ → ψ )
    s2 = lb.ref(
        "s2",
        "( φ → ( ψ ∧ ψ ) ) ↔ ( φ → ψ )",
        ref="anidmdbi",
        note="anidmdbi",
    )

    # bitr2i: from s1, s2: ( φ → ψ ) ↔ ( φ ⊼ ( ψ ⊼ ψ ) )
    res = lb.ref(
        "res",
        "( φ → ψ ) ↔ ( φ ⊼ ( ψ ⊼ ψ ) )",
        s1,
        s2,
        ref="bitr2i",
        note="bitr2i",
    )

    return lb.build(res)


def prove_2exanali(sys: System) -> Proof:
    """2exanali: ¬ ∃ x ∃ y ( φ ∧ ¬ ψ ) ↔ ∀ x ∀ y ( φ → ψ ).

    Equivalence of doubly negated existential conjunction with
    doubly universal implication.
    """
    lb = ProofBuilder(sys, "2exanali")
    # annim: ( φ ∧ ¬ ψ ) ↔ ¬ ( φ → ψ )
    s1 = lb.ref(
        "s1",
        "( φ ∧ ¬ ψ ) ↔ ¬ ( φ → ψ )",
        ref="annim",
        note="annim",
    )
    # 2exbii with annim: ∃ x ∃ y ( φ ∧ ¬ ψ ) ↔ ∃ x ∃ y ¬ ( φ → ψ )
    s2 = lb.ref(
        "s2",
        "∃ x ∃ y ( φ ∧ ¬ ψ ) ↔ ∃ x ∃ y ¬ ( φ → ψ )",
        s1,
        ref="2exbii",
        note="2exbii annim",
    )
    # 2nalexn with φ := ( φ → ψ ): ¬ ∀ x ∀ y ( φ → ψ ) ↔ ∃ x ∃ y ¬ ( φ → ψ )
    s3 = lb.ref(
        "s3",
        "¬ ∀ x ∀ y ( φ → ψ ) ↔ ∃ x ∃ y ¬ ( φ → ψ )",
        ref="2nalexn",
        note="2nalexn",
    )
    # bicomi of s3: ∃ x ∃ y ¬ ( φ → ψ ) ↔ ¬ ∀ x ∀ y ( φ → ψ )
    s4 = lb.ref(
        "s4",
        "∃ x ∃ y ¬ ( φ → ψ ) ↔ ¬ ∀ x ∀ y ( φ → ψ )",
        s3,
        ref="bicomi",
        note="bicomi 2nalexn",
    )
    # bitri s2, s4: ∃ x ∃ y ( φ ∧ ¬ ψ ) ↔ ¬ ∀ x ∀ y ( φ → ψ )
    s5 = lb.ref(
        "s5",
        "∃ x ∃ y ( φ ∧ ¬ ψ ) ↔ ¬ ∀ x ∀ y ( φ → ψ )",
        s2,
        s4,
        ref="bitri",
        note="bitri 2exbii, bicomi",
    )
    # bicomi of s5: ¬ ∀ x ∀ y ( φ → ψ ) ↔ ∃ x ∃ y ( φ ∧ ¬ ψ )
    s6 = lb.ref(
        "s6",
        "¬ ∀ x ∀ y ( φ → ψ ) ↔ ∃ x ∃ y ( φ ∧ ¬ ψ )",
        s5,
        ref="bicomi",
        note="bicomi bitri",
    )
    # con1bii with s6: ¬ ∃ x ∃ y ( φ ∧ ¬ ψ ) ↔ ∀ x ∀ y ( φ → ψ )
    res = lb.ref(
        "res",
        "¬ ∃ x ∃ y ( φ ∧ ¬ ψ ) ↔ ∀ x ∀ y ( φ → ψ )",
        s6,
        ref="con1bii",
        note="con1bii bicomi",
    )
    return lb.build(res)


def prove_equvelv(sys: System) -> Proof:
    """equvelv: ( ∀ z ( z = x → z = y ) ↔ x = y ).

    The variable z is universally quantified over the implication
    (z = x → z = y), and this is equivalent to x = y. The proof uses
    equequ1 to obtain the substitution instance, pm5.74i to transform
    the implication pattern, albii to lift the quantifier, equsv to
    simplify the result, and bitri to chain the equivalences.
    """
    lb = ProofBuilder(sys, "equvelv")

    # equequ1: z = x → ( z = y ↔ x = y )
    s1 = lb.ref(
        "s1",
        "z = x → ( z = y ↔ x = y )",
        ref="equequ1",
        note="equequ1",
    )

    # pm5.74i: ( z = x → z = y ) ↔ ( z = x → x = y )
    s2 = lb.ref(
        "s2",
        "( z = x → z = y ) ↔ ( z = x → x = y )",
        s1,
        ref="pm5.74i",
        note="pm5.74i",
    )

    # albii: ( ∀ z ( z = x → z = y ) ↔ ∀ z ( z = x → x = y ) )
    s3 = lb.ref(
        "s3",
        "( ∀ z ( z = x → z = y ) ↔ ∀ z ( z = x → x = y ) )",
        s2,
        ref="albii",
        note="albii",
    )

    # equsv: ( ∀ z ( z = x → x = y ) ↔ x = y )
    s4 = lb.ref(
        "s4",
        "( ∀ z ( z = x → x = y ) ↔ x = y )",
        ref="equsv",
        note="equsv",
    )

    # bitri: ( ∀ z ( z = x → z = y ) ↔ x = y )
    res = lb.ref(
        "res",
        "( ∀ z ( z = x → z = y ) ↔ x = y )",
        s3,
        s4,
        ref="bitri",
        note="bitri",
    )

    return lb.build(res)


THEOREMS: Mapping[str, LemmaCtor] = {
    "baib": prove_baib,
    "baibd": prove_baibd,
    "baibr": prove_baibr,
    "rbaibr": prove_rbaibr,
    "mt2bi": prove_mt2bi,
    "mpbiran": prove_mpbiran,
    "mpbiran2": prove_mpbiran2,
    "mtt": prove_mtt,
    "monothetic": prove_monothetic,
    "imnot": prove_imnot,
    "bitri": prove_bitri,
    "bitr4i": prove_bitr4i,
    "bitrd": prove_bitrd,
    "bitrdi": prove_bitrdi,
    "bitr4id": prove_bitr4id,
    "bibi2i": prove_bibi2i,
    "bibi1i": prove_bibi1i,
    "bibi1": prove_bibi1,
    "bibi2d": prove_bibi2d,
    "bitr2d": prove_bitr2d,
    "bitr3d": prove_bitr3d,
    "bitr4d": prove_bitr4d,
    "3bitri": prove_3bitri,
    "3bitrri": prove_3bitrri,
    "3bitr4i": prove_3bitr4i,
    "biimp": prove_biimp,
    "biimpr": prove_biimpr,
    "dfbi1": prove_dfbi1,
    "dfbi1ALT": prove_dfbi1ALT,
    "biimpi": prove_biimpi,
    "biimpd": prove_biimpd,
    "biimpa": prove_biimpa,
    "impbi": prove_impbi,
    "impbid": prove_impbid,
    "impbida": prove_impbida,
    "impbid1": prove_impbid1,
    "impbid2": prove_impbid2,
    "impbii": prove_impbii,
    "impbidd": prove_impbidd,
    "impbid21d": prove_impbid21d,
    "pm5.1im": prove_pm5_1im,
    "pm5.501": prove_pm5_501,
    "pm5.5": prove_pm5_5,
    "biid": prove_biid,
    "biidd": prove_biidd,
    "2th": prove_2th,
    "2thd": prove_2thd,
    "2exanali": prove_2exanali,
    "2false": prove_2false,
    "2falsed": prove_2falsed,
    "pm5.21ni": prove_pm5_21ni,
    "pm5.21nii": prove_pm5_21nii,
    "pm5.21im": prove_pm5_21im,
    "pm5.21ndd": prove_pm5_21ndd,
    "pm5.21nd": prove_pm5_21nd,
    "con34b": prove_con34b,
    "con2b": prove_con2b,
    "con2bi": prove_con2bi,
    "con2bid": prove_con2bid,
    "con2bii": prove_con2bii,
    "con1b": prove_con1b,
    "con1bii": prove_con1bii,
    "notbid": prove_notbid,
    "notbi": prove_notbi,
    "notnotb": prove_notnotb,
    "pm4.8": prove_pm4_8,
    "pm4.81": prove_pm4_81,
    "bi2.04": prove_bi2_04,
    "bianabs": prove_bianabs,
    "bibiad": prove_bibiad,
    "bibif": prove_bibif,
    "bicom1": prove_bicom1,
    "bicom": prove_bicom,
    "bicomd": prove_bicomd,
    "bicomi": prove_bicomi,
    "biimpac": prove_biimpac,
    "biimt": prove_biimt,
    "iba": prove_iba,
    "ibar": prove_ibar,
    "ibib": prove_ibib,
    "ibibr": prove_ibibr,
    "ifpdfbi": prove_ifpdfbi,
    "ifpdfbiOLD": prove_ifpdfbiOLD,
    "ifpfal": prove_ifpfal,
    "ifpid": prove_ifpid,
    "ifpn": prove_ifpn,
    "ifptru": prove_ifptru,
    "tbt": prove_tbt,
    "bija": prove_bija,
    "bitr3": prove_bitr3,
    "nbn2": prove_nbn2,
    "nbn": prove_nbn,
    "dfnan2": prove_dfnan2,
    "nan": prove_nan,
    "nanbi1": prove_nanbi1,
    "nanbi1i": prove_nanbi1i,
    "nanbi2i": prove_nanbi2i,
    "nancom": prove_nancom,
    "nanim": prove_nanim,
    "nbn3": prove_nbn3,
    "imdi": prove_imdi,
    "pm5.41": prove_pm5_41,
    "pm5.74": prove_pm5_74,
    "pm5.74d": prove_pm5_74d,
    "pm5.74da": prove_pm5_74da,
    "pm5.74ri": prove_pm5_74ri,
    "imbi2d": prove_imbi2d,
    "imbi12d": prove_imbi12d,
    "imbi12": prove_imbi12,
    "imbi1d": prove_imbi1d,
    "imbi1": prove_imbi1,
    "imbi2": prove_imbi2,
    "imbi2i": prove_imbi2i,
    "imbibi": prove_imbibi,
    "imbibiOLD": prove_imbibiOLD,
    "imim21b": prove_imim21b,
    "impcon4bid": prove_impcon4bid,
    "impimprbi": prove_impimprbi,
    "xchnxbi": prove_xchnxbi,
    "xchnxbir": prove_xchnxbir,
    "xchbinx": prove_xchbinx,
    "xchbinxr": prove_xchbinxr,
    "xorcom": prove_xorcom,
    "xnor": prove_xnor,
    "xorbi12i": prove_xorbi12i,
    "con4bid": prove_con4bid,
    "con4bii": prove_con4bii,
    "equvelv": prove_equvelv,
}

__all__ = [
    "LemmaCtor",
    "THEOREMS",
    "prove_dfbi1",
    "prove_dfbi1ALT",
    "prove_bitri",
    "prove_bitr4i",
    "prove_bitrd",
    "prove_bitr2d",
    "prove_bitr3d",
    "prove_bibi1i",
    "prove_bibiad",
    "prove_bibi1",
    "prove_bitr4id",
    "prove_bibi2i",
    "prove_bibi2d",
    "prove_bitrdi",
    "prove_bitr4d",
    "prove_3bitri",
    "prove_3bitrri",
    "prove_3bitr4i",
    "prove_biimp",
    "prove_biimpi",
    "prove_biimpd",
    "prove_biimpa",
    "prove_impbi",
    "prove_impbid",
    "prove_impbida",
    "prove_impbid1",
    "prove_impbid2",
    "prove_impbii",
    "prove_imdi",
    "prove_pm5_41",
    "prove_pm5_1im",
    "prove_pm5_501",
    "prove_impbidd",
    "prove_impbid21d",
    "prove_notbid",
    "prove_notbi",
    "prove_notnotb",
    "prove_biid",
    "prove_biidd",
    "prove_2th",
    "prove_2thd",
    "prove_2exanali",
    "prove_2false",
    "prove_2falsed",
    "prove_pm5_21ni",
    "prove_pm5_21nii",
    "prove_pm5_21im",
    "prove_pm5_21ndd",
    "prove_pm5_21nd",
    "prove_con34b",
    "prove_con2b",
    "prove_con2bi",
    "prove_con2bid",
    "prove_con2bii",
    "prove_con1b",
    "prove_con1bii",
    "prove_con4bii",
    "prove_equvelv",
    "prove_mt2bi",
    "prove_imnot",
    "prove_bicom1",
    "prove_bicom",
    "prove_bicomd",
    "prove_bicomi",
    "prove_bi2_04",
    "prove_bianabs",
    "prove_iba",
    "prove_ibar",
    "prove_ibib",
    "prove_ibibr",
    "prove_ifpdfbi",
    "prove_ifpdfbiOLD",
    "prove_ifpfal",
    "prove_ifpid",
    "prove_ifpn",
    "prove_ifptru",
    "prove_tbt",
    "prove_bija",
    "prove_nbn2",
    "prove_nbn",
    "prove_nbn3",
    "prove_dfnan2",
    "prove_nan",
    "prove_nanim",
    "prove_bitr3",
    "prove_pm4_8",
    "prove_pm4_81",
    "prove_pm5_74d",
    "prove_pm5_74da",
    "prove_imbi1",
    "prove_imbi1d",
    "prove_imbi12d",
    "prove_imbibi",
    "prove_imbibiOLD",
    "prove_imbi12",
    "prove_imim21b",
    "prove_pm5_74ri",
    "prove_impimprbi",
    "prove_xchnxbi",
    "prove_xchnxbir",
    "prove_xchbinxr",
    "prove_xchbinx",
    "prove_xorcom",
    "prove_xnor",
    "prove_xorbi12i",
    "prove_nornot",
]


def prove_nornot(sys: System) -> Proof:
    """nornot: ¬ φ ↔ (φ ⊽ φ).

    Negation expressed in terms of NOR: ¬φ is equivalent to φ NOR φ.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: df-nor oridm xchbinx bicomi.
    """
    lb = ProofBuilder(sys, "nornot")

    # df-nor: ( φ ⊽ φ ) ↔ ¬ ( φ ∨ φ )
    s1 = lb.ref(
        "s1",
        "( φ ⊽ φ ) ↔ ¬ ( φ ∨ φ )",
        ref="df-nor",
        note="df-nor",
    )

    # oridm: ( φ ∨ φ ) ↔ φ
    s2 = lb.ref(
        "s2",
        "( φ ∨ φ ) ↔ φ",
        ref="oridm",
        note="oridm",
    )

    # xchbinx(s1, s2): ( φ ⊽ φ ) ↔ ¬ φ
    s3 = lb.ref(
        "s3",
        "( φ ⊽ φ ) ↔ ¬ φ",
        s1,
        s2,
        ref="xchbinx",
        note="xchbinx",
    )

    # bicomi(s3): ¬ φ ↔ ( φ ⊽ φ )
    res = lb.ref(
        "res",
        "¬ φ ↔ ( φ ⊽ φ )",
        s3,
        ref="bicomi",
        note="bicomi",
    )

    return lb.build(res)


def prove_ifpbi123d(sys: System) -> Proof:
    """ifpbi123d: φ → ( if- ψ χ θ ↔ if- τ η ζ ).

    Deduction: from three biconditional hypotheses, deduce equivalence of
    the corresponding conditional operators.
    (Contributed by BJ, 25-Aug-2023.)
    """
    lb = ProofBuilder(sys, "ifpbi123d")
    h1 = lb.hyp("ifpbi123d.1", "φ → ( ψ ↔ τ )")
    h2 = lb.hyp("ifpbi123d.2", "φ → ( χ ↔ η )")
    h3 = lb.hyp("ifpbi123d.3", "φ → ( θ ↔ ζ )")

    # imbi12d: from h1 and h2
    s1 = lb.ref(
        "s1",
        "φ → ( ( ψ → χ ) ↔ ( τ → η ) )",
        h1,
        h2,
        ref="imbi12d",
        note="imbi12d",
    )

    # orbi12d: from h1 and h3
    s2 = lb.ref(
        "s2",
        "φ → ( ( ψ ∨ θ ) ↔ ( τ ∨ ζ ) )",
        h1,
        h3,
        ref="orbi12d",
        note="orbi12d",
    )

    # anbi12d: combine s1 and s2
    s3 = lb.ref(
        "s3",
        "φ → ( ( ( ψ → χ ) ∧ ( ψ ∨ θ ) ) ↔ ( ( τ → η ) ∧ ( τ ∨ ζ ) ) )",
        s1,
        s2,
        ref="anbi12d",
        note="anbi12d",
    )

    # dfifp3: if- ψ χ θ ↔ ( ( ψ → χ ) ∧ ( ψ ∨ θ ) )
    s4 = lb.ref(
        "s4",
        "( if- ψ χ θ ↔ ( ( ψ → χ ) ∧ ( ψ ∨ θ ) ) )",
        ref="dfifp3",
        note="dfifp3",
    )

    # dfifp3: if- τ η ζ ↔ ( ( τ → η ) ∧ ( τ ∨ ζ ) )
    s5 = lb.ref(
        "s5",
        "( if- τ η ζ ↔ ( ( τ → η ) ∧ ( τ ∨ ζ ) ) )",
        ref="dfifp3",
        note="dfifp3",
    )

    # 3bitr4g: combine s3, s4, s5
    res = lb.ref(
        "res",
        "φ → ( if- ψ χ θ ↔ if- τ η ζ )",
        s3,
        s4,
        s5,
        ref="3bitr4g",
        note="3bitr4g",
    )

    return lb.build(res)


def prove_ifpbi23d(sys: System) -> Proof:
    """ifpbi23d: φ → ( if- ψ χ θ ↔ if- ψ η ζ ).

    Deduction: equivalence of two conditionals where only the second and
    third operands differ.  (Contributed by BJ, 25-Aug-2023.)
    """
    lb = ProofBuilder(sys, "ifpbi23d")
    h1 = lb.hyp("ifpbi23d.1", "φ → ( χ ↔ η )")
    h2 = lb.hyp("ifpbi23d.2", "φ → ( θ ↔ ζ )")

    # biidd: φ → ( ψ ↔ ψ )
    s1 = lb.ref("s1", "φ → ( ψ ↔ ψ )", ref="biidd", note="biidd")

    # ifpbi123d: combine the three biconditional hypotheses
    res = lb.ref(
        "res",
        "φ → ( if- ψ χ θ ↔ if- ψ η ζ )",
        s1,
        h1,
        h2,
        ref="ifpbi123d",
        note="ifpbi123d",
    )

    return lb.build(res)


def prove_nanass(sys: System) -> Proof:
    """nanass: ( φ ↔ χ ) ↔ ( ( ( φ ⊼ ψ ) ⊼ χ ) ↔ ( φ ⊼ ( ψ ⊼ χ ) ) ).

    A characterization of when an expression involving alternative denials
    associates.  Remark: alternative denial is commutative, see nancom.
    (Contributed by Richard Penner, 29-Feb-2020.)
    (Proof shortened by Wolf Lammen, 23-Oct-2022.)
    """
    lb = ProofBuilder(sys, "nanass")

    # (1) bicom1: ( φ ↔ χ ) → ( χ ↔ φ )
    s1 = lb.ref(
        "s1",
        "( φ ↔ χ ) → ( χ ↔ φ )",
        ref="bicom1",
        note="bicom1",
    )

    # (2) nanbi2: ( φ ↔ χ ) → ( ( ψ ⊼ φ ) ↔ ( ψ ⊼ χ ) )
    s2 = lb.ref(
        "s2",
        "( φ ↔ χ ) → ( ( ψ ⊼ φ ) ↔ ( ψ ⊼ χ ) )",
        ref="nanbi2",
        note="nanbi2",
    )

    # (3) nanbi12d with 1,2: ( φ ↔ χ ) → ( ( χ ⊼ ( ψ ⊼ φ ) ) ↔ ( φ ⊼ ( ψ ⊼ χ ) ) )
    s3 = lb.ref(
        "s3",
        "( φ ↔ χ ) → ( ( χ ⊼ ( ψ ⊼ φ ) ) ↔ ( φ ⊼ ( ψ ⊼ χ ) ) )",
        s1,
        s2,
        ref="nanbi12d",
        note="nanbi12d bicom1, nanbi2",
    )

    # (4) nannan: ( φ ⊼ ( ψ ⊼ χ ) ) ↔ ( φ → ( ψ ∧ χ ) )
    s4 = lb.ref(
        "s4",
        "( φ ⊼ ( ψ ⊼ χ ) ) ↔ ( φ → ( ψ ∧ χ ) )",
        ref="nannan",
        note="nannan",
    )

    # (5) simpr: ( ψ ∧ χ ) → χ
    s5 = lb.ref(
        "s5",
        "( ψ ∧ χ ) → χ",
        ref="simpr",
        note="simpr",
    )

    # (6) imim2i with 5: ( φ → ( ψ ∧ χ ) ) → ( φ → χ )
    s6 = lb.ref(
        "s6",
        "( φ → ( ψ ∧ χ ) ) → ( φ → χ )",
        s5,
        ref="imim2i",
        note="imim2i simpr",
    )

    # (7) sylbi with 4,6: ( φ ⊼ ( ψ ⊼ χ ) ) → ( φ → χ )
    s7 = lb.ref(
        "s7",
        "( φ ⊼ ( ψ ⊼ χ ) ) → ( φ → χ )",
        s4,
        s6,
        ref="sylbi",
        note="sylbi nannan, imim2i",
    )

    # (8) nannan: ( χ ⊼ ( ψ ⊼ φ ) ) ↔ ( χ → ( ψ ∧ φ ) )
    s8 = lb.ref(
        "s8",
        "( χ ⊼ ( ψ ⊼ φ ) ) ↔ ( χ → ( ψ ∧ φ ) )",
        ref="nannan",
        note="nannan",
    )

    # (9) simpr: ( ψ ∧ φ ) → φ
    s9 = lb.ref(
        "s9",
        "( ψ ∧ φ ) → φ",
        ref="simpr",
        note="simpr",
    )

    # (10) imim2i with 9: ( χ → ( ψ ∧ φ ) ) → ( χ → φ )
    s10 = lb.ref(
        "s10",
        "( χ → ( ψ ∧ φ ) ) → ( χ → φ )",
        s9,
        ref="imim2i",
        note="imim2i simpr",
    )

    # (11) sylbi with 8,10: ( χ ⊼ ( ψ ⊼ φ ) ) → ( χ → φ )
    s11 = lb.ref(
        "s11",
        "( χ ⊼ ( ψ ⊼ φ ) ) → ( χ → φ )",
        s8,
        s10,
        ref="sylbi",
        note="sylbi nannan, imim2i",
    )

    # (12) impbid21d with 7,11: ( χ ⊼ ( ψ ⊼ φ ) ) → ( ( φ ⊼ ( ψ ⊼ χ ) ) → ( φ ↔ χ ) )
    s12 = lb.ref(
        "s12",
        "( χ ⊼ ( ψ ⊼ φ ) ) → ( ( φ ⊼ ( ψ ⊼ χ ) ) → ( φ ↔ χ ) )",
        s7,
        s11,
        ref="impbid21d",
        note="impbid21d",
    )

    # (13) nanan: ( φ ∧ ( ψ ⊼ χ ) ) ↔ ¬ ( φ ⊼ ( ψ ⊼ χ ) )
    s13 = lb.ref(
        "s13",
        "( φ ∧ ( ψ ⊼ χ ) ) ↔ ¬ ( φ ⊼ ( ψ ⊼ χ ) )",
        ref="nanan",
        note="nanan",
    )

    # (14) simpl: ( φ ∧ ( ψ ⊼ χ ) ) → φ
    s14 = lb.ref(
        "s14",
        "( φ ∧ ( ψ ⊼ χ ) ) → φ",
        ref="simpl",
        note="simpl",
    )

    # (15) sylbir with 13,14: ¬ ( φ ⊼ ( ψ ⊼ χ ) ) → φ
    s15 = lb.ref(
        "s15",
        "¬ ( φ ⊼ ( ψ ⊼ χ ) ) → φ",
        s13,
        s14,
        ref="sylbir",
        note="sylbir nanan, simpl",
    )

    # (16) nanan: ( χ ∧ ( ψ ⊼ φ ) ) ↔ ¬ ( χ ⊼ ( ψ ⊼ φ ) )
    s16 = lb.ref(
        "s16",
        "( χ ∧ ( ψ ⊼ φ ) ) ↔ ¬ ( χ ⊼ ( ψ ⊼ φ ) )",
        ref="nanan",
        note="nanan",
    )

    # (17) simpl: ( χ ∧ ( ψ ⊼ φ ) ) → χ
    s17 = lb.ref(
        "s17",
        "( χ ∧ ( ψ ⊼ φ ) ) → χ",
        ref="simpl",
        note="simpl",
    )

    # (18) sylbir with 16,17: ¬ ( χ ⊼ ( ψ ⊼ φ ) ) → χ
    s18 = lb.ref(
        "s18",
        "¬ ( χ ⊼ ( ψ ⊼ φ ) ) → χ",
        s16,
        s17,
        ref="sylbir",
        note="sylbir nanan, simpl",
    )

    # (19) pm5.1im: φ → ( χ → ( φ ↔ χ ) )
    s19 = lb.ref(
        "s19",
        "φ → ( χ → ( φ ↔ χ ) )",
        ref="pm5.1im",
        note="pm5.1im",
    )

    # (20) syl2imc with 15,18,19: ¬ ( χ ⊼ ( ψ ⊼ φ ) ) → ( ¬ ( φ ⊼ ( ψ ⊼ χ ) ) → ( φ ↔ χ ) )
    s20 = lb.ref(
        "s20",
        "¬ ( χ ⊼ ( ψ ⊼ φ ) ) → ( ¬ ( φ ⊼ ( ψ ⊼ χ ) ) → ( φ ↔ χ ) )",
        s15,
        s18,
        s19,
        ref="syl2imc",
        note="syl2imc",
    )

    # (21) bija with 12,20: ( ( χ ⊼ ( ψ ⊼ φ ) ) ↔ ( φ ⊼ ( ψ ⊼ χ ) ) ) → ( φ ↔ χ )
    s21 = lb.ref(
        "s21",
        "( ( χ ⊼ ( ψ ⊼ φ ) ) ↔ ( φ ⊼ ( ψ ⊼ χ ) ) ) → ( φ ↔ χ )",
        s12,
        s20,
        ref="bija",
        note="bija",
    )

    # (22) impbii with 3,21: ( φ ↔ χ ) ↔ ( ( χ ⊼ ( ψ ⊼ φ ) ) ↔ ( φ ⊼ ( ψ ⊼ χ ) ) )
    s22 = lb.ref(
        "s22",
        "( φ ↔ χ ) ↔ ( ( χ ⊼ ( ψ ⊼ φ ) ) ↔ ( φ ⊼ ( ψ ⊼ χ ) ) )",
        s3,
        s21,
        ref="impbii",
        note="impbii",
    )

    # (23) nancom: ( ψ ⊼ φ ) ↔ ( φ ⊼ ψ )
    s23 = lb.ref(
        "s23",
        "( ψ ⊼ φ ) ↔ ( φ ⊼ ψ )",
        ref="nancom",
        note="nancom",
    )

    # (24) nanbi2i with 23: ( χ ⊼ ( ψ ⊼ φ ) ) ↔ ( χ ⊼ ( φ ⊼ ψ ) )
    s24 = lb.ref(
        "s24",
        "( χ ⊼ ( ψ ⊼ φ ) ) ↔ ( χ ⊼ ( φ ⊼ ψ ) )",
        s23,
        ref="nanbi2i",
        note="nanbi2i nancom",
    )

    # (25) nancom: ( χ ⊼ ( φ ⊼ ψ ) ) ↔ ( ( φ ⊼ ψ ) ⊼ χ )
    s25 = lb.ref(
        "s25",
        "( χ ⊼ ( φ ⊼ ψ ) ) ↔ ( ( φ ⊼ ψ ) ⊼ χ )",
        ref="nancom",
        note="nancom",
    )

    # (26) bitri with 24,25: ( χ ⊼ ( ψ ⊼ φ ) ) ↔ ( ( φ ⊼ ψ ) ⊼ χ )
    s26 = lb.ref(
        "s26",
        "( χ ⊼ ( ψ ⊼ φ ) ) ↔ ( ( φ ⊼ ψ ) ⊼ χ )",
        s24,
        s25,
        ref="bitri",
        note="bitri nanbi2i, nancom",
    )

    # (27) bibi1i with 26: ( ( χ ⊼ ( ψ ⊼ φ ) ) ↔ ( φ ⊼ ( ψ ⊼ χ ) ) ) ↔ ( ( ( φ ⊼ ψ ) ⊼ χ ) ↔ ( φ ⊼ ( ψ ⊼ χ ) ) )
    s27 = lb.ref(
        "s27",
        "( ( χ ⊼ ( ψ ⊼ φ ) ) ↔ ( φ ⊼ ( ψ ⊼ χ ) ) ) ↔ ( ( ( φ ⊼ ψ ) ⊼ χ ) ↔ ( φ ⊼ ( ψ ⊼ χ ) ) )",
        s26,
        ref="bibi1i",
        note="bibi1i bitri",
    )

    # (28) bitri with 22,27: ( φ ↔ χ ) ↔ ( ( ( φ ⊼ ψ ) ⊼ χ ) ↔ ( φ ⊼ ( ψ ⊼ χ ) ) )
    res = lb.ref(
        "res",
        "( φ ↔ χ ) ↔ ( ( ( φ ⊼ ψ ) ⊼ χ ) ↔ ( φ ⊼ ( ψ ⊼ χ ) ) )",
        s22,
        s27,
        ref="bitri",
        note="bitri",
    )

    return lb.build(res)


def prove_ax13b(sys: System) -> Proof:
    """ax13b: ( ¬ x = y → ( y = z → φ ) ) ↔ ( ¬ x = y → ( ¬ x = z → ( y = z → φ ) ) ).

    Equivalence of two implication forms with a common antecedent involving
    negated equalities.  (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "ax13b")

    # (1) equeuclr with x:=y, y:=x: y = z → ( x = z → x = y )
    s1 = lb.ref(
        "s1",
        "y = z → ( x = z → x = y )",
        ref="equeuclr",
        note="equeuclr with x:=y, y:=x",
    )

    # (2) con3rr3: ¬ x = y → ( y = z → ¬ x = z )
    s2 = lb.ref(
        "s2",
        "¬ x = y → ( y = z → ¬ x = z )",
        s1,
        ref="con3rr3",
        note="con3rr3",
    )

    # (3) imim1d: ¬ x = y → ( ( ¬ x = z → ( y = z → φ ) ) → ( y = z → ( y = z → φ ) ) )
    s3 = lb.ref(
        "s3",
        "¬ x = y → ( ( ¬ x = z → ( y = z → φ ) ) → ( y = z → ( y = z → φ ) ) )",
        s2,
        ref="imim1d",
        note="imim1d",
    )

    # (4) pm2.43: ( y = z → ( y = z → φ ) ) → ( y = z → φ )
    s4 = lb.ref(
        "s4",
        "( y = z → ( y = z → φ ) ) → ( y = z → φ )",
        ref="pm2.43",
        note="pm2.43",
    )

    # (5) syl6: ¬ x = y → ( ( ¬ x = z → ( y = z → φ ) ) → ( y = z → φ ) )
    s5 = lb.ref(
        "s5",
        "¬ x = y → ( ( ¬ x = z → ( y = z → φ ) ) → ( y = z → φ ) )",
        s3,
        s4,
        ref="syl6",
        note="syl6",
    )

    # (6) ax-1: ( y = z → φ ) → ( ¬ x = z → ( y = z → φ ) )
    s6 = lb.ref(
        "s6",
        "( y = z → φ ) → ( ¬ x = z → ( y = z → φ ) )",
        ref="ax-1",
        note="A1",
    )

    # (7) impbid2: ¬ x = y → ( ( y = z → φ ) ↔ ( ¬ x = z → ( y = z → φ ) ) )
    s7 = lb.ref(
        "s7",
        "¬ x = y → ( ( y = z → φ ) ↔ ( ¬ x = z → ( y = z → φ ) ) )",
        s6,
        s5,
        ref="impbid2",
        note="impbid2",
    )

    # (8) pm5.74i: ( ¬ x = y → ( y = z → φ ) ) ↔ ( ¬ x = y → ( ¬ x = z → ( y = z → φ ) ) )
    res = lb.ref(
        "res",
        "( ¬ x = y → ( y = z → φ ) ) ↔ ( ¬ x = y → ( ¬ x = z → ( y = z → φ ) ) )",
        s7,
        ref="pm5.74i",
        note="pm5.74i",
    )

    return lb.build(res)


# New migrations register here beside their implementation. The aggregate
# registry imports this mapping, avoiding another edit to global shim files.
MIGRATION_THEOREMS: Mapping[str, LemmaCtor] = {}
