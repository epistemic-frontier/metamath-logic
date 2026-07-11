"""Conjunction calculus skeleton.



set.mm range:


    Main conjunction material starts at set.mm line 4044 with ``wa`` and
    ``df-an`` and continues until disjunction is introduced at line 7289.

Scope:
    This module is reserved for theorems around ``/\\`` and ``df-an``:

    - conjunction introduction and elimination
    - ``simpl*`` and ``simpr*`` projections
    - associativity, commutativity, idempotence, absorption
    - conjunction congruence and implication transport lemmas

Migration notes:
    This should become the main dependency base for truth constants, truth
    tables, natural-deduction context lemmas, and later adder proofs.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping

from skfd.proof import Proof, ProofBuilder

from . import System

LemmaCtor = Callable[[System], Proof]


def prove_3impa(sys: System) -> Proof:
    r"""3impa: ( ( ph /\ ps /\ ch ) -> th ).

    Inference form of df-3an: from a hypothesis using binary conjunction
    derive the same with ternary conjunction.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3impa")
    h1 = lb.hyp("3impa.1", "( ( ph /\\ ps ) /\\ ch ) -> th")
    df3an = lb.ref(
        "df3an",
        "( ph /\\ ps /\\ ch ) <-> ( ( ph /\\ ps ) /\\ ch )",
        ref="df-3an",
        note="df-3an",
    )
    res = lb.ref(
        "res",
        "( ph /\\ ps /\\ ch ) -> th",
        df3an,
        h1,
        ref="sylbi",
        note="sylbi",
    )
    return lb.build(res)


def prove_3simpa(sys: System) -> Proof:
    """3simpa: ( φ ∧ ψ ∧ χ ) → ( φ ∧ ψ ).

    Simplify a triple conjunction to the first two conjuncts.
    """
    lb = ProofBuilder(sys, "3simpa")
    s_id = lb.ref(
        "s_id",
        "( φ ∧ ψ ) → ( φ ∧ ψ )",
        ref="id",
        note="id",
    )
    res = lb.ref(
        "res",
        "( φ ∧ ψ ∧ χ ) → ( φ ∧ ψ )",
        s_id,
        ref="3adant3",
        note="3adant3",
    )
    return lb.build(res)


def prove_3expa(sys: System) -> Proof:
    r"""3expa: ( ( ( ph /\ ps ) /\ ch ) -> th ).

    Exportation from triple conjunction.  Given a hypothesis of the form
    ( ( ph /\ ps /\ ch ) -> th ), derive ( ( ( ph /\ ps ) /\ ch ) -> th ).
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3expa")
    h1 = lb.hyp("3expa.1", "( ph /\\ ps /\\ ch ) -> th")
    df3an = lb.ref(
        "df3an",
        "( ph /\\ ps /\\ ch ) <-> ( ( ph /\\ ps ) /\\ ch )",
        ref="df-3an",
        note="df-3an",
    )
    res = lb.ref(
        "res",
        "( ( ph /\\ ps ) /\\ ch ) -> th",
        df3an,
        h1,
        ref="sylbir",
        note="sylbir",
    )
    return lb.build(res)


def prove_3expb(sys: System) -> Proof:
    r"""3expb: ( ( ph /\ ( ps /\ ch ) ) -> th ).

    An exportation/importation inference.  (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3expb")
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
        "( ( ph /\\ ( ps /\\ ch ) ) -> th )",
        s1,
        ref="imp32",
        note="imp32 s1",
    )
    return lb.build(res)


def prove_3expia(sys: System) -> Proof:
    r"""3expia: ( ( ph /\ ps ) -> ( ch -> th ) ).

    Exportation from triple conjunction.  Given
    ( ( ph /\ ps /\ ch ) -> th ), derive
    ( ( ph /\ ps ) -> ( ch -> th ) ).
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3expia")
    h1 = lb.hyp("3exp.1", r"( ph /\ ps /\ ch ) -> th")
    s1 = lb.ref(
        "s1",
        r"( ( ph /\ ( ps /\ ch ) ) -> th )",
        h1,
        ref="3expb",
        note="3expb 3exp.1",
    )
    res = lb.ref(
        "res",
        r"( ( ph /\ ps ) -> ( ch -> th ) )",
        s1,
        ref="expr",
        note="expr s1",
    )
    return lb.build(res)


def prove_ex3(sys: System) -> Proof:
    r"""ex3: ( ( ph /\ ps /\ ch ) -> ( th -> ta ) ).

    Hyp: ex3.1 |- ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta ).
    Concl: |- ( ( ph /\ ps /\ ch ) -> ( th -> ta ) ).

    Exportation with a ternary antecedent.  (Contributed by NM, 23-Jun-2002.)
    """
    lb = ProofBuilder(sys, "ex3")
    h1 = lb.hyp("ex3.1", "( ( ( ( ph /\\ ps ) /\\ ch ) /\\ th ) -> ta )")
    s1 = lb.ref(
        "s1",
        "( ( ph /\\ ps ) /\\ ch ) -> ( th -> ta )",
        h1,
        ref="ex",
        note="ex",
    )
    res = lb.ref(
        "res",
        "( ph /\\ ps /\\ ch ) -> ( th -> ta )",
        s1,
        ref="3impa",
        note="3impa",
    )
    return lb.build(res)


def prove_impac(sys: System) -> Proof:
    r"""impac: ( ( ph /\ ps ) -> ( ch /\ ps ) ).

    Hyp: impac.1 |- ( ph -> ( ps -> ch ) )

    Importation with conjunction of consequent and antecedent.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "impac")
    h1 = lb.hyp("impac.1", "( ph -> ( ps -> ch ) )")
    s1 = lb.ref(
        "s1",
        r"( ph -> ( ps -> ( ch /\ ps ) ) )",
        h1,
        ref="ancrd",
        note="ancrd impac.1",
    )
    res = lb.ref(
        "res",
        r"( ( ph /\ ps ) -> ( ch /\ ps ) )",
        s1,
        ref="imp",
        note="imp s1",
    )
    return lb.build(res)


def prove_imdistanri(sys: System) -> Proof:
    r"""imdistanri: ( ( ps /\ ph ) -> ( ch /\ ph ) ).

    Hyp: imdistanri.1 |- ( ph -> ( ps -> ch ) )

    Inference distributing an implication into a conjunction with a
    commuted antecedent.  (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "imdistanri")
    h1 = lb.hyp("imdistanri.1", "( ph -> ( ps -> ch ) )")
    s1 = lb.ref(
        "s1",
        "( ps -> ( ph -> ch ) )",
        h1,
        ref="com12",
        note="com12 imdistanri.1",
    )
    res = lb.ref(
        "res",
        r"( ( ps /\ ph ) -> ( ch /\ ph ) )",
        s1,
        ref="impac",
        note="impac s1",
    )
    return lb.build(res)


def prove_imp(sys: System) -> Proof:
    r"""imp: ( ( ph /\ ps ) -> ch ).

    Importation.  If ph implies ps implies ch, then ph and ps implies ch.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "imp")
    h1 = lb.hyp("imp.1", "( ph -> ( ps -> ch ) )")
    dfan = lb.ref(
        "df-an",
        r"( ( ph /\ ps ) <-> -. ( ph -> -. ps ) )",
        ref="df-an",
        note="df-an",
    )
    impi_step = lb.ref(
        "impi",
        "( -. ( ph -> -. ps ) -> ch )",
        h1,
        ref="impi",
        note="impi",
    )
    res = lb.ref(
        "res",
        r"( ph /\ ps ) -> ch",
        dfan,
        impi_step,
        ref="sylbi",
        note="sylbi",
    )
    return lb.build(res)


def prove_abai(sys: System) -> Proof:
    """abai: ( φ ∧ ψ ) ↔ ( φ ∧ ( φ → ψ ) ).

    Derive the equivalence between a conjunction and the same
    conjunction with the antecedent replaced by implication.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "abai")

    # biimt: ( φ → ( ψ ↔ ( φ → ψ ) ) )
    s1 = lb.ref(
        "s1",
        "( φ → ( ψ ↔ ( φ → ψ ) ) )",
        ref="biimt",
        note="biimt",
    )

    # pm5.32i with hypothesis s1: ( φ ∧ ψ ) ↔ ( φ ∧ ( φ → ψ ) )
    res = lb.ref(
        "res",
        "( φ ∧ ψ ) ↔ ( φ ∧ ( φ → ψ ) )",
        s1,
        ref="pm5.32i",
        note="pm5.32i",
    )

    return lb.build(res)


def prove_adantl(sys: System) -> Proof:
    """adantl: ( ( χ ∧ φ ) → ψ ).

    Add a conjunct to the left of an antecedent.  If φ → ψ, then
    ( χ ∧ φ ) → ψ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "adantl")
    h1 = lb.hyp("adantl.1", "φ → ψ")
    s1 = lb.ref(
        "s1",
        "( φ ∧ χ ) → ψ",
        h1,
        ref="adantr",
        note="adantr",
    )
    res = lb.ref(
        "res",
        "( χ ∧ φ ) → ψ",
        s1,
        ref="ancoms",
        note="ancoms",
    )
    return lb.build(res)


def prove_adantr(sys: System) -> Proof:
    r"""adantr: ( ( φ ∧ χ ) → ψ ).

    Add a conjunct to the right of an antecedent.  If φ → ψ, then
    ( φ ∧ χ ) → ψ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "adantr")
    h1 = lb.hyp("adantr.1", "φ → ψ")
    s1 = lb.ref(
        "s1",
        "φ → ( χ → ψ )",
        h1,
        ref="a1d",
        note="a1d adantr.1",
    )
    res = lb.ref(
        "res",
        "( φ ∧ χ ) → ψ",
        s1,
        ref="imp",
        note="imp s1",
    )
    return lb.build(res)


def prove_adantrd(sys: System) -> Proof:
    """adantrd: φ → ( ( ψ ∧ θ ) → χ ).

    Deduction adding a conjunct to the right of an antecedent.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "adantrd")
    h1 = lb.hyp("adantrd.1", "φ → ( ψ → χ )")
    s1 = lb.ref(
        "s1",
        "( ψ ∧ θ ) → ψ",
        ref="simpl",
        note="simpl",
    )
    res = lb.ref(
        "res",
        "φ → ( ( ψ ∧ θ ) → χ )",
        s1,
        h1,
        ref="syl5",
        note="syl5",
    )
    return lb.build(res)


def prove_adantld(sys: System) -> Proof:
    """adantld: φ → ( ( θ ∧ ψ ) → χ ).

    Deduction adding a conjunct to the left of an antecedent.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "adantld")
    h1 = lb.hyp("adantld.1", "φ → ( ψ → χ )")
    s1 = lb.ref(
        "s1",
        "( θ ∧ ψ ) → ψ",
        ref="simpr",
        note="simpr",
    )
    res = lb.ref(
        "res",
        "φ → ( ( θ ∧ ψ ) → χ )",
        s1,
        h1,
        ref="syl5",
        note="syl5",
    )
    return lb.build(res)


def prove_adantrr(sys: System) -> Proof:
    """adantrr: ( φ ∧ ( ψ ∧ θ ) ) → χ.

    Syllogism inference with a nested conjunction antecedent.  From
    ( φ ∧ ψ ) → χ and simpl, derive ( φ ∧ ( ψ ∧ θ ) ) → χ via sylan2.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "adantrr")
    h1 = lb.hyp("adant2.1", "( φ ∧ ψ ) → χ")

    s1 = lb.ref(
        "s1",
        "( ψ ∧ θ ) → ψ",
        ref="simpl",
        note="simpl",
    )

    res = lb.ref(
        "res",
        "( φ ∧ ( ψ ∧ θ ) ) → χ",
        s1,
        h1,
        ref="sylan2",
        note="sylan2",
    )

    return lb.build(res)


def prove_adantrl(sys: System) -> Proof:
    """adantrl: ( φ ∧ ( θ ∧ ψ ) ) → χ.

    Add a conjunct to the right conjunct in the antecedent of a deduction.
    (Contributed by NM, 25-Feb-1996.)
    """
    lb = ProofBuilder(sys, "adantrl")
    h1 = lb.hyp("adant2.1", "( φ ∧ ψ ) → χ")

    s1 = lb.ref(
        "s1",
        "( θ ∧ ψ ) → ψ",
        ref="simpr",
        note="simpr",
    )

    res = lb.ref(
        "res",
        "( φ ∧ ( θ ∧ ψ ) ) → χ",
        s1,
        h1,
        ref="sylan2",
        note="sylan2",
    )

    return lb.build(res)


def prove_3adant3(sys: System) -> Proof:
    """3adant3: ( φ ∧ ψ ∧ θ ) → χ.

    Deduction adding a conjunct to the antecedent.  From ( φ ∧ ψ ) → χ,
    derive ( φ ∧ ψ ∧ θ ) → χ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3adant3")
    h1 = lb.hyp("3adant.1", "( φ ∧ ψ ) → χ")

    s1 = lb.ref(
        "s1",
        "( φ ∧ ( ψ ∧ θ ) ) → χ",
        h1,
        ref="adantrr",
        note="adantrr",
    )

    res = lb.ref(
        "res",
        "( φ ∧ ψ ∧ θ ) → χ",
        s1,
        ref="3impb",
        note="3impb",
    )

    return lb.build(res)


def prove_3adant3r3(sys: System) -> Proof:
    """3adant3r3: ( φ ∧ ( ψ ∧ χ ∧ τ ) ) → θ.

    Deduction adding a conjunct to a nested antecedent.  From
    ( φ ∧ ψ ∧ χ ) → θ, derive ( φ ∧ ( ψ ∧ χ ∧ τ ) ) → θ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3adant3r3")
    h1 = lb.hyp("ad4ant3.1", "( φ ∧ ψ ∧ χ ) → θ")

    s1 = lb.ref(
        "s1",
        "( φ ∧ ( ψ ∧ χ ) ) → θ",
        h1,
        ref="3expb",
        note="3expb ad4ant3.1",
    )

    res = lb.ref(
        "res",
        "( φ ∧ ( ψ ∧ χ ∧ τ ) ) → θ",
        s1,
        ref="3adantr3",
        note="3adantr3 s1",
    )

    return lb.build(res)


def prove_3adantr3(sys: System) -> Proof:
    """3adantr3: ( φ ∧ ( ψ ∧ χ ∧ τ ) ) → θ.

    Deduction adding a conjunct to the right side of a nested antecedent.
    From ( φ ∧ ( ψ ∧ χ ) ) → θ, derive ( φ ∧ ( ψ ∧ χ ∧ τ ) ) → θ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3adantr3")
    h1 = lb.hyp("3adantr.1", "( φ ∧ ( ψ ∧ χ ) ) → θ")

    s1 = lb.ref(
        "s1",
        "( ψ ∧ χ ∧ τ ) → ( ψ ∧ χ )",
        ref="3simpa",
        note="3simpa",
    )

    res = lb.ref(
        "res",
        "( φ ∧ ( ψ ∧ χ ∧ τ ) ) → θ",
        s1,
        h1,
        ref="sylan2",
        note="sylan2",
    )

    return lb.build(res)


def prove_3ad2antr1(sys: System) -> Proof:
    """3ad2antr1: ( φ ∧ ( χ ∧ ψ ∧ τ ) ) → θ.

    Deduction adding conjuncts to the right side of a nested antecedent.
    From ( φ ∧ χ ) → θ, derive ( φ ∧ ( χ ∧ ψ ∧ τ ) ) → θ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3ad2antr1")
    h1 = lb.hyp("3ad2antl.1", "( φ ∧ χ ) → θ")

    s1 = lb.ref(
        "s1",
        "( φ ∧ ( χ ∧ ψ ) ) → θ",
        h1,
        ref="adantrr",
        note="adantrr",
    )

    res = lb.ref(
        "res",
        "( φ ∧ ( χ ∧ ψ ∧ τ ) ) → θ",
        s1,
        ref="3adantr3",
        note="3adantr3",
    )

    return lb.build(res)


def prove_3ad2antr2(sys: System) -> Proof:
    """3ad2antr2: ( φ ∧ ( ψ ∧ χ ∧ τ ) ) → θ.

    Deduction adding conjuncts to the right side of a nested antecedent.
    From ( φ ∧ χ ) → θ, derive ( φ ∧ ( ψ ∧ χ ∧ τ ) ) → θ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3ad2antr2")
    h1 = lb.hyp("3ad2antl.1", "( φ ∧ χ ) → θ")

    s1 = lb.ref(
        "s1",
        "( φ ∧ ( ψ ∧ χ ) ) → θ",
        h1,
        ref="adantrl",
        note="adantrl",
    )

    res = lb.ref(
        "res",
        "( φ ∧ ( ψ ∧ χ ∧ τ ) ) → θ",
        s1,
        ref="3adantr3",
        note="3adantr3",
    )

    return lb.build(res)


def prove_ad4ant123(sys: System) -> Proof:
    r"""ad4ant123: ( ( ( ( φ ∧ ψ ) ∧ χ ) ∧ τ ) → θ.

    Deduction adding an antecedent. Given ( φ ∧ ψ ∧ χ ) → θ,
    derive ( ( ( ( φ ∧ ψ ) ∧ χ ) ∧ τ ) → θ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "ad4ant123")
    h1 = lb.hyp("ad4ant3.1", "( φ ∧ ψ ∧ χ ) → θ")
    s1 = lb.ref(
        "s1",
        "( ( ( φ ∧ ψ ) ∧ χ ) → θ )",
        h1,
        ref="3expa",
        note="3expa ad4ant3.1",
    )
    res = lb.ref(
        "res",
        "( ( ( ( φ ∧ ψ ) ∧ χ ) ∧ τ ) → θ )",
        s1,
        ref="adantr",
        note="adantr s1",
    )
    return lb.build(res)


def prove_ad2antll(sys: System) -> Proof:
    """ad2antll: ( ( χ ∧ ( θ ∧ φ ) ) → ψ ).

    Add two conjuncts to the left of an antecedent.  If φ → ψ, then
    ( χ ∧ ( θ ∧ φ ) ) → ψ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "ad2antll")
    h1 = lb.hyp("ad2ant.1", "φ → ψ")
    s1 = lb.ref(
        "s1",
        "( θ ∧ φ ) → ψ",
        h1,
        ref="adantl",
        note="adantl",
    )
    res = lb.ref(
        "res",
        "( χ ∧ ( θ ∧ φ ) ) → ψ",
        s1,
        ref="adantl",
        note="adantl",
    )
    return lb.build(res)


def prove_ad2antrl(sys: System) -> Proof:
    """ad2antrl: ( ( χ ∧ ( φ ∧ θ ) ) → ψ ).

    Syllogism inference with a nested conjunction antecedent.  If φ → ψ,
    then ( χ ∧ ( φ ∧ θ ) ) → ψ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "ad2antrl")
    h1 = lb.hyp("ad2ant.1", "φ → ψ")
    s1 = lb.ref(
        "s1",
        "( χ ∧ φ ) → ψ",
        h1,
        ref="adantl",
        note="adantl",
    )
    res = lb.ref(
        "res",
        "( χ ∧ ( φ ∧ θ ) ) → ψ",
        s1,
        ref="adantrr",
        note="adantrr",
    )
    return lb.build(res)


def prove_simpl(sys: System) -> Proof:
    """simpl: ( φ ∧ ψ ) → φ.

    Simplify a conjunction to the left conjunct.
    (Contributed by NM, 5-Jan-1993.)
    """
    lb = ProofBuilder(sys, "simpl")
    s_id = lb.ref(
        "s_id",
        "φ → φ",
        ref="id",
        note="id",
    )
    res = lb.ref(
        "res",
        "( φ ∧ ψ ) → φ",
        s_id,
        ref="adantr",
        note="adantr",
    )
    return lb.build(res)


def prove_simpli(sys: System) -> Proof:
    """simpli: φ.

    Inference form of simpl.  From a conjunction, deduce the left conjunct.
    (Contributed by NM, 5-Jan-1993.)
    """
    lb = ProofBuilder(sys, "simpli")
    h1 = lb.hyp("simpli.1", "φ ∧ ψ")
    s1 = lb.ref("s1", "( φ ∧ ψ ) → φ", ref="simpl", note="simpl")
    res = lb.mp("res", h1, s1, "MP simpli.1, simpl")
    return lb.build(res)


def prove_simpld(sys: System) -> Proof:
    """simpld: φ → ψ.

    Deduction form of simpl: from φ → ( ψ ∧ χ ) deduce φ → ψ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "simpld")
    h1 = lb.hyp("simpld.1", "φ → ( ψ ∧ χ )")
    s1 = lb.ref(
        "s1",
        "( ψ ∧ χ ) → ψ",
        ref="simpl",
        note="simpl",
    )
    res = lb.ref(
        "res",
        "φ → ψ",
        h1,
        s1,
        ref="syl",
        note="syl simpld.1, simpl",
    )
    return lb.build(res)


def prove_simplld(sys: System) -> Proof:
    """simplld: φ → ψ.

    Deduction form of simpl: from φ → ( ( ψ ∧ χ ) ∧ θ ) deduce φ → ψ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "simplld")
    h1 = lb.hyp("simplld.1", "φ → ( ( ψ ∧ χ ) ∧ θ )")
    s1 = lb.ref(
        "s1",
        "φ → ( ψ ∧ χ )",
        h1,
        ref="simpld",
        note="simpld",
    )
    res = lb.ref(
        "res",
        "φ → ψ",
        s1,
        ref="simpld",
        note="simpld",
    )
    return lb.build(res)


def prove_simpr(sys: System) -> Proof:
    """simpr: ( φ ∧ ψ ) → ψ.

    Simplify a conjunction to the right conjunct.
    (Contributed by NM, 5-Jan-1993.)
    """
    lb = ProofBuilder(sys, "simpr")
    s_id = lb.ref(
        "s_id",
        "ψ → ψ",
        ref="id",
        note="id",
    )
    res = lb.ref(
        "res",
        "( φ ∧ ψ ) → ψ",
        s_id,
        ref="adantl",
        note="adantl",
    )
    return lb.build(res)


def prove_simpri(sys: System) -> Proof:
    """simpri: ψ.

    Inference form of simpr.  From a conjunction, deduce the right conjunct.
    (Contributed by NM, 5-Jan-1993.)
    """
    lb = ProofBuilder(sys, "simpri")
    h1 = lb.hyp("simpri.1", "φ ∧ ψ")
    s1 = lb.ref("s1", "( φ ∧ ψ ) → ψ", ref="simpr", note="simpr")
    res = lb.mp("res", h1, s1, "MP simpri.1, simpr")
    return lb.build(res)


def prove_simprbda(sys: System) -> Proof:
    """simprbda: ( φ ∧ ψ ) → χ.

    Deduction form: if φ implies ψ ↔ ( χ ∧ θ ), then ( φ ∧ ψ ) → χ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "simprbda")
    h1 = lb.hyp("simplbda.1", "φ → ( ψ ↔ ( χ ∧ θ ) )")
    s1 = lb.ref(
        "s1",
        "( φ ∧ ψ ) → ( χ ∧ θ )",
        h1,
        ref="biimpa",
        note="biimpa simplbda.1",
    )
    res = lb.ref(
        "res",
        "( φ ∧ ψ ) → χ",
        s1,
        ref="simpld",
        note="simpld",
    )
    return lb.build(res)


def prove_simprd(sys: System) -> Proof:
    """simprd: φ → χ.

    Deduction form of simpr: from φ → ( ψ ∧ χ ) deduce φ → χ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "simprd")
    h1 = lb.hyp("simprd.1", "φ → ( ψ ∧ χ )")
    s1 = lb.ref("s1", "φ → ( χ ∧ ψ )", h1, ref="ancomd", note="ancomd simprd.1")
    res = lb.ref("res", "φ → χ", s1, ref="simpld", note="simpld s1")
    return lb.build(res)


def prove_simprld(sys: System) -> Proof:
    """simprld: φ → χ.

    Deduction form: from φ → ( ψ ∧ ( χ ∧ θ ) ) deduce φ → χ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "simprld")
    h1 = lb.hyp("simprld.1", "φ → ( ψ ∧ ( χ ∧ θ ) )")
    s1 = lb.ref(
        "s1",
        "φ → ( χ ∧ θ )",
        h1,
        ref="simprd",
        note="simprd",
    )
    res = lb.ref(
        "res",
        "φ → χ",
        s1,
        ref="simpld",
        note="simpld",
    )
    return lb.build(res)


def prove_simprl(sys: System) -> Proof:
    """simprl: ( φ ∧ ( ψ ∧ χ ) ) → ψ.

    Simplify a nested conjunction: from φ and (ψ ∧ χ) deduce ψ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "simprl")
    s_id = lb.ref(
        "s_id",
        "ψ → ψ",
        ref="id",
        note="id",
    )
    res = lb.ref(
        "res",
        "( φ ∧ ( ψ ∧ χ ) ) → ψ",
        s_id,
        ref="ad2antrl",
        note="ad2antrl",
    )
    return lb.build(res)


def prove_simprr(sys: System) -> Proof:
    """simprr: ( φ ∧ ( ψ ∧ χ ) ) → χ.

    Simplify a nested conjunction: from φ and ( ψ ∧ χ ) deduce χ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "simprr")
    s_id = lb.ref(
        "s_id",
        "χ → χ",
        ref="id",
        note="id",
    )
    res = lb.ref(
        "res",
        "( φ ∧ ( ψ ∧ χ ) ) → χ",
        s_id,
        ref="ad2antll",
        note="ad2antll",
    )
    return lb.build(res)


def prove_simpr1(sys: System) -> Proof:
    """simpr1: ( φ ∧ ( ψ ∧ χ ∧ θ ) ) → ψ.

    Simplify a ternary conjunction: from φ and a triple conjunction,
    deduce the first conjunct of the triple.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "simpr1")
    s1 = lb.ref(
        "s1",
        "( φ ∧ ψ ) → ψ",
        ref="simpr",
        note="simpr",
    )
    res = lb.ref(
        "res",
        "( φ ∧ ( ψ ∧ χ ∧ θ ) ) → ψ",
        s1,
        ref="3ad2antr1",
        note="3ad2antr1",
    )
    return lb.build(res)


def prove_simpr1l(sys: System) -> Proof:
    """simpr1l: ( τ ∧ ( ( φ ∧ ψ ) ∧ χ ∧ θ ) ) → φ.

    Simplify a ternary conjunction: from τ and a nested conjunction
    ( ( φ ∧ ψ ) ∧ χ ∧ θ ), derive φ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "simpr1l")
    s1 = lb.ref(
        "s1",
        "( τ ∧ ( φ ∧ ψ ) ) → φ",
        ref="simprl",
        note="simprl",
    )
    res = lb.ref(
        "res",
        "( τ ∧ ( ( φ ∧ ψ ) ∧ χ ∧ θ ) ) → φ",
        s1,
        ref="3ad2antr1",
        note="3ad2antr1",
    )
    return lb.build(res)


def prove_simpr1r(sys: System) -> Proof:
    """simpr1r: ( τ ∧ ( ( φ ∧ ψ ) ∧ χ ∧ θ ) ) → ψ.

    Simplify a ternary conjunction: from τ and a nested conjunction
    ( ( φ ∧ ψ ) ∧ χ ∧ θ ), derive ψ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "simpr1r")
    s1 = lb.ref(
        "s1",
        "( τ ∧ ( φ ∧ ψ ) ) → ψ",
        ref="simprr",
        note="simprr",
    )
    res = lb.ref(
        "res",
        "( τ ∧ ( ( φ ∧ ψ ) ∧ χ ∧ θ ) ) → ψ",
        s1,
        ref="3ad2antr1",
        note="3ad2antr1",
    )
    return lb.build(res)


def prove_simpr2(sys: System) -> Proof:
    """simpr2: ( φ ∧ ( ψ ∧ χ ∧ θ ) ) → χ.

    Simplify a nested ternary conjunction to the middle conjunct.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "simpr2")
    s1 = lb.ref(
        "s1",
        "( φ ∧ χ ) → χ",
        ref="simpr",
        note="simpr",
    )
    res = lb.ref(
        "res",
        "( φ ∧ ( ψ ∧ χ ∧ θ ) ) → χ",
        s1,
        ref="3ad2antr2",
        note="3ad2antr2",
    )

    return lb.build(res)


def prove_simpr2l(sys: System) -> Proof:
    """simpr2l: ( τ ∧ ( χ ∧ ( φ ∧ ψ ) ∧ θ ) ) → φ.

    Simplify a nested conjunction: from τ and (χ ∧ (φ ∧ ψ) ∧ θ) deduce φ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "simpr2l")
    s1 = lb.ref(
        "s1",
        "( τ ∧ ( φ ∧ ψ ) ) → φ",
        ref="simprl",
        note="simprl",
    )
    res = lb.ref(
        "res",
        "( τ ∧ ( χ ∧ ( φ ∧ ψ ) ∧ θ ) ) → φ",
        s1,
        ref="3ad2antr2",
        note="3ad2antr2",
    )
    return lb.build(res)


def prove_simpr2r(sys: System) -> Proof:
    """simpr2r: ( τ ∧ ( χ ∧ ( φ ∧ ψ ) ∧ θ ) ) → ψ.

    Simplify a nested conjunction: from τ and (χ ∧ (φ ∧ ψ) ∧ θ) deduce ψ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "simpr2r")
    s1 = lb.ref(
        "s1",
        "( τ ∧ ( φ ∧ ψ ) ) → ψ",
        ref="simprr",
        note="simprr",
    )
    res = lb.ref(
        "res",
        "( τ ∧ ( χ ∧ ( φ ∧ ψ ) ∧ θ ) ) → ψ",
        s1,
        ref="3ad2antr2",
        note="3ad2antr2",
    )
    return lb.build(res)


def prove_simpr11(sys: System) -> Proof:
    """simpr11: ( η ∧ ( ( φ ∧ ψ ∧ χ ) ∧ θ ∧ τ ) ) → φ.

    Simplify a nested triple conjunction: from η and ((φ ∧ ψ ∧ χ) ∧ θ ∧ τ)
    deduce the first conjunct φ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "simpr11")
    s1 = lb.ref(
        "s1",
        "( η ∧ ( φ ∧ ψ ∧ χ ) ) → φ",
        ref="simpr1",
        note="simpr1",
    )
    res = lb.ref(
        "res",
        "( η ∧ ( ( φ ∧ ψ ∧ χ ) ∧ θ ∧ τ ) ) → φ",
        s1,
        ref="3ad2antr1",
        note="3ad2antr1",
    )
    return lb.build(res)


def prove_simpr12(sys: System) -> Proof:
    """simpr12: ( η ∧ ( ( φ ∧ ψ ∧ χ ) ∧ θ ∧ τ ) ) → ψ.

    Simplify a nested triple conjunction: from η and ((φ ∧ ψ ∧ χ) ∧ θ ∧ τ)
    deduce the second conjunct ψ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "simpr12")
    s1 = lb.ref(
        "s1",
        "( η ∧ ( φ ∧ ψ ∧ χ ) ) → ψ",
        ref="simpr2",
        note="simpr2",
    )
    res = lb.ref(
        "res",
        "( η ∧ ( ( φ ∧ ψ ∧ χ ) ∧ θ ∧ τ ) ) → ψ",
        s1,
        ref="3ad2antr1",
        note="3ad2antr1",
    )
    return lb.build(res)


def prove_simpr21(sys: System) -> Proof:
    """simpr21: ( η ∧ ( θ ∧ ( φ ∧ ψ ∧ χ ) ∧ τ ) ) → φ.

    Simplify a nested triple conjunction: from η and (θ ∧ (φ ∧ ψ ∧ χ) ∧ τ)
    deduce the first conjunct φ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "simpr21")
    s1 = lb.ref(
        "s1",
        "( η ∧ ( φ ∧ ψ ∧ χ ) ) → φ",
        ref="simpr1",
        note="simpr1",
    )
    res = lb.ref(
        "res",
        "( η ∧ ( θ ∧ ( φ ∧ ψ ∧ χ ) ∧ τ ) ) → φ",
        s1,
        ref="3ad2antr2",
        note="3ad2antr2",
    )
    return lb.build(res)


def prove_simpr22(sys: System) -> Proof:
    """simpr22: ( η ∧ ( θ ∧ ( φ ∧ ψ ∧ χ ) ∧ τ ) ) → ψ.

    Simplify a nested triple conjunction: from η and (θ ∧ (φ ∧ ψ ∧ χ) ∧ τ)
    deduce the second conjunct ψ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "simpr22")
    s1 = lb.ref(
        "s1",
        "( η ∧ ( φ ∧ ψ ∧ χ ) ) → ψ",
        ref="simpr2",
        note="simpr2",
    )
    res = lb.ref(
        "res",
        "( η ∧ ( θ ∧ ( φ ∧ ψ ∧ χ ) ∧ τ ) ) → ψ",
        s1,
        ref="3ad2antr2",
        note="3ad2antr2",
    )
    return lb.build(res)


def prove_simprrd(sys: System) -> Proof:
    """simprrd: φ → θ.

    Deduction form: from φ → ( ψ ∧ ( χ ∧ θ ) ) deduce φ → θ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "simprrd")
    h1 = lb.hyp("simprrd.1", "φ → ( ψ ∧ ( χ ∧ θ ) )")
    s1 = lb.ref(
        "s1",
        "φ → ( χ ∧ θ )",
        h1,
        ref="simprd",
        note="simprd",
    )
    res = lb.ref(
        "res",
        "φ → θ",
        s1,
        ref="simprd",
        note="simprd",
    )
    return lb.build(res)


def prove_simplrd(sys: System) -> Proof:
    """simplrd: φ → χ.

    Deduction form: from φ → ( ( ψ ∧ χ ) ∧ θ ) deduce φ → χ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "simplrd")
    h1 = lb.hyp("simplrd.1", "φ → ( ( ψ ∧ χ ) ∧ θ )")
    s1 = lb.ref(
        "s1",
        "φ → ( ψ ∧ χ )",
        h1,
        ref="simpld",
        note="simpld",
    )
    res = lb.ref(
        "res",
        "φ → χ",
        s1,
        ref="simprd",
        note="simprd",
    )
    return lb.build(res)


def prove_birani(sys: System) -> Proof:
    """birani: ( φ ∧ χ ) → ψ.

    From a biconditional φ ↔ ψ, deduce ( φ ∧ χ ) → ψ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "birani")
    h1 = lb.hyp("birani.1", "φ ↔ ψ")
    s1 = lb.ref(
        "s1",
        "φ → ψ",
        h1,
        ref="biimpi",
        note="biimpi birani.1",
    )
    res = lb.ref(
        "res",
        "( φ ∧ χ ) → ψ",
        s1,
        ref="adantr",
        note="adantr s1",
    )
    return lb.build(res)


def prove_bilani(sys: System) -> Proof:
    """bilani: ( χ ∧ φ ) → ψ.

    From a biconditional φ ↔ ψ, deduce ( χ ∧ φ ) → ψ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "bilani")
    h1 = lb.hyp("bilani.1", "φ ↔ ψ")
    s1 = lb.ref(
        "s1",
        "φ → ψ",
        h1,
        ref="biimpi",
        note="biimpi bilani.1",
    )
    res = lb.ref(
        "res",
        "( χ ∧ φ ) → ψ",
        s1,
        ref="adantl",
        note="adantl s1",
    )
    return lb.build(res)


def prove_biranri(sys: System) -> Proof:
    """biranri: ( ψ ∧ χ ) → φ.

    From a biconditional φ ↔ ψ, deduce ( ψ ∧ χ ) → φ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "biranri")
    h1 = lb.hyp("biranri.1", "φ ↔ ψ")
    s1 = lb.ref(
        "s1",
        "ψ → φ",
        h1,
        ref="biimpri",
        note="biimpri biranri.1",
    )
    res = lb.ref(
        "res",
        "( ψ ∧ χ ) → φ",
        s1,
        ref="adantr",
        note="adantr s1",
    )
    return lb.build(res)


def prove_bilanri(sys: System) -> Proof:
    """bilanri: ( χ ∧ ψ ) → φ.

    From a biconditional φ ↔ ψ, deduce ( χ ∧ ψ ) → φ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "bilanri")
    h1 = lb.hyp("birani.1", "φ ↔ ψ")
    s1 = lb.ref(
        "s1",
        "ψ → φ",
        h1,
        ref="biimpri",
        note="biimpri birani.1",
    )
    res = lb.ref(
        "res",
        "( χ ∧ ψ ) → φ",
        s1,
        ref="adantl",
        note="adantl s1",
    )
    return lb.build(res)


def prove_pm3_33(sys: System) -> Proof:
    r"""pm3.33: ( ( ( ph -> ps ) /\ ( ps -> ch ) ) -> ( ph -> ch ) ).

    Implicational syllogism with importation.  If ph implies ps and ps
    implies ch, then the conjunction of those implications yields
    ph implies ch.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "pm3.33")
    s_imim1 = lb.ref(
        "s_imim1",
        "( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) )",
        ref="imim1",
        note="imim1",
    )
    res = lb.ref(
        "res",
        r"( ( ( ph -> ps ) /\ ( ps -> ch ) ) -> ( ph -> ch ) )",
        s_imim1,
        ref="imp",
        note="imp",
    )
    return lb.build(res)


def prove_impel(sys: System) -> Proof:
    r"""impel: ( ( ph /\ th ) -> ch ).

    An inference adding a conjunct to the left of an implication.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "impel")
    h1 = lb.hyp("impel.1", "( ph -> ( ps -> ch ) )")
    h2 = lb.hyp("impel.2", "( th -> ps )")

    s1 = lb.ref(
        "s1",
        "( ph -> ( th -> ch ) )",
        h2,
        h1,
        ref="syl5",
        note="syl5",
    )
    res = lb.ref(
        "res",
        r"( ( ph /\ th ) -> ch )",
        s1,
        ref="imp",
        note="imp",
    )
    return lb.build(res)


def prove_impcom(sys: System) -> Proof:
    r"""impcom: ( ( ps /\ ph ) -> ch ).

    Commuted importation.  If ph implies ps implies ch, then ps and ph
    implies ch.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "impcom")
    h1 = lb.hyp("imp.1", "( ph -> ( ps -> ch ) )")
    s_com12 = lb.ref(
        "s_com12",
        "( ps -> ( ph -> ch ) )",
        h1,
        ref="com12",
        note="com12",
    )
    res = lb.ref(
        "res",
        r"( ( ps /\ ph ) -> ch )",
        s_com12,
        ref="imp",
        note="imp",
    )
    return lb.build(res)


def prove_pm3_34(sys: System) -> Proof:
    r"""pm3.34: ( ( ψ → χ ) ∧ ( φ → ψ ) ) → ( φ → χ ).

    Implicational syllogism.  If ψ implies χ and φ implies ψ, then φ and
    the conjunction of those implications yields χ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "pm3.34")
    s_imim2 = lb.ref(
        "s_imim2",
        "( ( ψ → χ ) → ( ( φ → ψ ) → ( φ → χ ) ) )",
        ref="imim2",
        note="imim2",
    )
    res = lb.ref(
        "res",
        "( ( ( ψ → χ ) ∧ ( φ → ψ ) ) → ( φ → χ ) )",
        s_imim2,
        ref="imp",
        note="imp",
    )
    return lb.build(res)


def prove_pm3_35(sys: System) -> Proof:
    r"""pm3.35: ( ( ph /\ ( ph -> ps ) ) -> ps ).

    Modus ponens with conjunction (imported from pm2.27).
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "pm3.35")
    pm2_27 = lb.ref(
        "pm2.27",
        "( ph -> ( ( ph -> ps ) -> ps ) )",
        ref="pm2.27",
        note="pm2.27",
    )
    res = lb.ref(
        "res",
        r"( ( ph /\ ( ph -> ps ) ) -> ps )",
        pm2_27,
        ref="imp",
        note="imp",
    )
    return lb.build(res)


def prove_pm3_4(sys: System) -> Proof:
    """pm3.4: ( ( φ ∧ ψ ) → ( φ → ψ ) ).

    From a conjunction, deduce the first conjunct implies the second.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "pm3.4")
    s_simpr = lb.ref(
        "s_simpr",
        "( φ ∧ ψ ) → ψ",
        ref="simpr",
        note="simpr",
    )
    s_id = lb.ref(
        "s_id",
        "ψ → ψ",
        ref="id",
        note="id",
    )
    s_a1d = lb.ref(
        "s_a1d",
        "ψ → ( φ → ψ )",
        s_id,
        ref="a1d",
        note="a1d",
    )
    res = lb.ref(
        "res",
        "( φ ∧ ψ ) → ( φ → ψ )",
        s_simpr,
        s_a1d,
        ref="syl",
        note="syl",
    )
    return lb.build(res)


def prove_pm3_41(sys: System) -> Proof:
    """pm3.41: ( φ → χ ) → ( ( φ ∧ ψ ) → χ ).

    From φ → χ deduce that φ ∧ ψ also implies χ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "pm3.41")
    s_simpl = lb.ref("s_simpl", "( φ ∧ ψ ) → φ", ref="simpl", note="simpl")
    res = lb.ref("res", "( φ → χ ) → ( ( φ ∧ ψ ) → χ )", s_simpl, ref="imim1i", note="imim1i")
    return lb.build(res)


def prove_pm3_42(sys: System) -> Proof:
    """pm3.42: ( ψ → χ ) → ( ( φ ∧ ψ ) → χ ).

    From ψ → χ deduce that φ ∧ ψ also implies χ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "pm3.42")
    s_simpr = lb.ref("s_simpr", "( φ ∧ ψ ) → ψ", ref="simpr", note="simpr")
    res = lb.ref("res", "( ψ → χ ) → ( ( φ ∧ ψ ) → χ )", s_simpr, ref="imim1i", note="imim1i")
    return lb.build(res)


def prove_pm3_31(sys: System) -> Proof:
    r"""pm3.31: ( ( ph -> ( ps -> ch ) ) -> ( ( ph /\ ps ) -> ch ) ).

    Import-export theorem.  If ph implies that ps implies ch, then
    ph and ps together imply ch.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "pm3.31")
    s_id = lb.ref(
        "s_id",
        "( ( ph -> ( ps -> ch ) ) -> ( ph -> ( ps -> ch ) ) )",
        ref="id",
        note="id",
    )
    res = lb.ref(
        "res",
        r"( ( ph -> ( ps -> ch ) ) -> ( ( ph /\ ps ) -> ch ) )",
        s_id,
        ref="impd",
        note="impd",
    )
    return lb.build(res)


def prove_biimp3a(sys: System) -> Proof:
    r"""biimp3a: ( ( ph /\ ps /\ ch ) -> th ).

    Inference from a biconditional to a ternary conjunction.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "biimp3a")
    h1 = lb.hyp("biimp3a.1", r"( ( ph /\ ps ) -> ( ch <-> th ) )")

    # biimpa: ( ( ph /\ ps ) -> ( ch <-> th ) ) -> ( ( ( ph /\ ps ) /\ ch ) -> th )
    s1 = lb.ref(
        "s1",
        r"( ( ( ph /\ ps ) /\ ch ) -> th )",
        h1,
        ref="biimpa",
        note="biimpa",
    )

    # 3impa: ( ( ( ph /\ ps ) /\ ch ) -> th ) -> ( ( ph /\ ps /\ ch ) -> th )
    res = lb.ref(
        "res",
        r"( ph /\ ps /\ ch ) -> th",
        s1,
        ref="3impa",
        note="3impa",
    )

    return lb.build(res)


def prove_biimp3ar(sys: System) -> Proof:
    r"""biimp3ar: ( ( ph /\ ps /\ th ) -> ch ).

    Inference from a biconditional to a ternary conjunction.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "biimp3ar")
    h1 = lb.hyp("biimp3a.1", r"( ( ph /\ ps ) -> ( ch <-> th ) )")

    # exbiri: ( ( ph /\ ps ) -> ( ch <-> th ) ) -> ( ph -> ( ps -> ( th -> ch ) ) )
    s1 = lb.ref(
        "s1",
        r"( ph -> ( ps -> ( th -> ch ) ) )",
        h1,
        ref="exbiri",
        note="exbiri",
    )

    # 3imp: ( ph -> ( ps -> ( th -> ch ) ) ) -> ( ( ph /\ ps /\ th ) -> ch )
    res = lb.ref(
        "res",
        r"( ph /\ ps /\ th ) -> ch",
        s1,
        ref="3imp",
        note="3imp",
    )

    return lb.build(res)


def prove_bimsc1(sys: System) -> Proof:
    """bimsc1: ( ( φ → ψ ) ∧ ( χ ↔ ( ψ ∧ φ ) ) ) → ( χ ↔ φ ).

    If χ is equivalent to ψ ∧ φ and φ implies ψ, then χ is equivalent to φ.
    """
    lb = ProofBuilder(sys, "bimsc1")

    # simpr: ( ψ ∧ φ ) → φ
    s_simpr = lb.ref(
        "s_simpr",
        "( ψ ∧ φ ) → φ",
        ref="simpr",
        note="simpr",
    )

    # ancr: ( φ → ψ ) → ( φ → ( ψ ∧ φ ) )
    s_ancr = lb.ref(
        "s_ancr",
        "( φ → ψ ) → ( φ → ( ψ ∧ φ ) )",
        ref="ancr",
        note="ancr",
    )

    # impbid2: ( φ → ψ ) → ( ( ψ ∧ φ ) ↔ φ )
    # impbid2.1: ( ψ ∧ φ ) → φ  from s_simpr
    # impbid2.2: ( φ → ψ ) → ( φ → ( ψ ∧ φ ) )  from s_ancr
    s_impbid2 = lb.ref(
        "s_impbid2",
        "( φ → ψ ) → ( ( ψ ∧ φ ) ↔ φ )",
        s_simpr,
        s_ancr,
        ref="impbid2",
        note="impbid2",
    )

    # id: ( χ ↔ ( ψ ∧ φ ) ) → ( χ ↔ ( ψ ∧ φ ) )
    s_id = lb.ref(
        "s_id",
        "( χ ↔ ( ψ ∧ φ ) ) → ( χ ↔ ( ψ ∧ φ ) )",
        ref="id",
        note="id",
    )

    # sylan9bbr: ( ( φ → ψ ) ∧ ( χ ↔ ( ψ ∧ φ ) ) ) → ( χ ↔ φ )
    # sylan9bbr.1: ( χ ↔ ( ψ ∧ φ ) ) → ( χ ↔ ( ψ ∧ φ ) )  from s_id
    # sylan9bbr.2: ( φ → ψ ) → ( ( ψ ∧ φ ) ↔ φ )  from s_impbid2
    res = lb.ref(
        "res",
        "( ( φ → ψ ) ∧ ( χ ↔ ( ψ ∧ φ ) ) ) → ( χ ↔ φ )",
        s_id,
        s_impbid2,
        ref="sylan9bbr",
        note="sylan9bbr",
    )

    return lb.build(res)


def prove_impd(sys: System) -> Proof:
    r"""impd: ( ph -> ( ( ps /\ ch ) -> th ) ).

    Deduction form of imp.  If ph implies that ps implies ch implies th,
    then ph implies that ps and ch together imply th.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "impd")
    h1 = lb.hyp("impd.1", "( ph -> ( ps -> ( ch -> th ) ) )")

    # com3l: ps -> (ch -> (ph -> th))
    s1 = lb.ref(
        "s1",
        "( ps -> ( ch -> ( ph -> th ) ) )",
        h1,
        ref="com3l",
        note="com3l",
    )

    # imp: (ps /\ ch) -> (ph -> th)
    s2 = lb.ref(
        "s2",
        "( ( ps /\\ ch ) -> ( ph -> th ) )",
        s1,
        ref="imp",
        note="imp",
    )

    # com12: ph -> ((ps /\ ch) -> th)
    res = lb.ref(
        "res",
        "( ph -> ( ( ps /\\ ch ) -> th ) )",
        s2,
        ref="com12",
        note="com12",
    )

    return lb.build(res)


def prove_impcomd(sys: System) -> Proof:
    r"""impcomd: ( ph -> ( ( ch /\ ps ) -> th ) ).

    Deduction form of impcom with antecedents commuted.
    If ph implies ps implies ch implies th, then ph implies
    that ch and ps together imply th.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "impcomd")
    h1 = lb.hyp("impd.1", "( ph -> ( ps -> ( ch -> th ) ) )")

    # com23: swap 2nd and 3rd antecedents
    s1 = lb.ref(
        "s1",
        "( ph -> ( ch -> ( ps -> th ) ) )",
        h1,
        ref="com23",
        note="com23",
    )

    # impd: import the two antecedents into a conjunction
    res = lb.ref(
        "res",
        r"( ph -> ( ( ch /\ ps ) -> th ) )",
        s1,
        ref="impd",
        note="impd",
    )

    return lb.build(res)


def prove_ancoms(sys: System) -> Proof:
    """ancoms: ( ( ψ ∧ φ ) → χ ).

    Inference form of expcom: from ( φ ∧ ψ ) → χ derive ( ψ ∧ φ ) → χ.
    (Contributed by NM, 29-Dec-1992.)
    """
    lb = ProofBuilder(sys, "ancoms")
    h1 = lb.hyp("ancoms.1", "( ( φ ∧ ψ ) → χ )")
    s1 = lb.ref("s1", "ψ → ( φ → χ )", h1, ref="expcom", note="expcom")
    res = lb.ref("res", "( ( ψ ∧ φ ) → χ )", s1, ref="imp", note="imp")
    return lb.build(res)


def prove_ancomsd(sys: System) -> Proof:
    r"""ancomsd: ( ph -> ( ( ch /\ ps ) -> th ) ).

    Deduction form of ancoms.  If ph implies that ps and ch jointly imply th,
    then ph implies that ch and ps jointly imply th.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "ancomsd")
    h1 = lb.hyp("ancomsd.1", r"( ph -> ( ( ps /\ ch ) -> th ) )")

    # expcomd: export and commute the antecedents
    s1 = lb.ref(
        "s1",
        "( ph -> ( ch -> ( ps -> th ) ) )",
        h1,
        ref="expcomd",
        note="expcomd",
    )

    # impd: import the two antecedents into a conjunction
    res = lb.ref(
        "res",
        r"( ph -> ( ( ch /\ ps ) -> th ) )",
        s1,
        ref="impd",
        note="impd",
    )

    return lb.build(res)


def prove_expl(sys: System) -> Proof:
    r"""expl: ( ph -> ( ( ps /\ ch ) -> th ) ).

    Hyp: expl.1 |- ( ( ( ph /\ ps ) /\ ch ) -> th ).
    Concl: |- ( ph -> ( ( ps /\ ch ) -> th ) ).

    An exportation inference.  (Contributed by NM, 26-Apr-1994.)
    """
    lb = ProofBuilder(sys, "expl")
    h1 = lb.hyp("expl.1", "( ( ( ph /\\ ps ) /\\ ch ) -> th )")
    s1 = lb.ref(
        "s1",
        "( ph -> ( ps -> ( ch -> th ) ) )",
        h1,
        ref="exp31",
        note="exp31 expl.1",
    )
    res = lb.ref(
        "res",
        "( ph -> ( ( ps /\\ ch ) -> th ) )",
        s1,
        ref="impd",
        note="impd s1",
    )
    return lb.build(res)


def prove_impl(sys: System) -> Proof:
    r"""impl: ( ( ( ph /\ ps ) /\ ch ) -> th ).

    Hyp: impl.1 |- ( ph -> ( ( ps /\ ch ) -> th ) ).
    Concl: |- ( ( ( ph /\ ps ) /\ ch ) -> th ).

    An importation inference.  (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "impl")
    h1 = lb.hyp("impl.1", "( ph -> ( ( ps /\\ ch ) -> th ) )")
    s1 = lb.ref(
        "s1",
        "( ph -> ( ps -> ( ch -> th ) ) )",
        h1,
        ref="expd",
        note="expd impl.1",
    )
    res = lb.ref(
        "res",
        "( ( ( ph /\\ ps ) /\\ ch ) -> th )",
        s1,
        ref="imp31",
        note="imp31 s1",
    )
    return lb.build(res)


def prove_imp31(sys: System) -> Proof:
    r"""imp31: ( ( ( ph /\ ps ) /\ ch ) -> th ).

    Importation of a triple conjunction.  If ph implies ps implies ch
    implies th, then ph and ps and ch together imply th.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "imp31")
    h1 = lb.hyp("imp31.1", "( ph -> ( ps -> ( ch -> th ) ) )")

    # imp: (ph -> (ps -> (ch -> th))) -> ((ph /\ ps) -> (ch -> th))
    s1 = lb.ref(
        "s1",
        r"( ( ph /\ ps ) -> ( ch -> th ) )",
        h1,
        ref="imp",
        note="imp",
    )

    # imp: ((ph /\ ps) -> (ch -> th)) -> (((ph /\ ps) /\ ch) -> th)
    res = lb.ref(
        "res",
        r"( ( ( ph /\ ps ) /\ ch ) -> th )",
        s1,
        ref="imp",
        note="imp",
    )

    return lb.build(res)


def prove_an31(sys: System) -> Proof:
    """an31: ( ( φ ∧ ψ ) ∧ χ ) ↔ ( ( χ ∧ ψ ) ∧ φ ).

    Swap the first and third conjuncts in a nested conjunction.
    """
    lb = ProofBuilder(sys, "an31")

    # an13: ( φ ∧ ( ψ ∧ χ ) ) ↔ ( χ ∧ ( ψ ∧ φ ) )
    s1 = lb.ref(
        "s1",
        "( φ ∧ ( ψ ∧ χ ) ) ↔ ( χ ∧ ( ψ ∧ φ ) )",
        ref="an13",
        note="an13",
    )

    # anass: ( ( φ ∧ ψ ) ∧ χ ) ↔ ( φ ∧ ( ψ ∧ χ ) )
    s2 = lb.ref(
        "s2",
        "( ( φ ∧ ψ ) ∧ χ ) ↔ ( φ ∧ ( ψ ∧ χ ) )",
        ref="anass",
        note="anass",
    )

    # anass: ( ( χ ∧ ψ ) ∧ φ ) ↔ ( χ ∧ ( ψ ∧ φ ) )
    s3 = lb.ref(
        "s3",
        "( ( χ ∧ ψ ) ∧ φ ) ↔ ( χ ∧ ( ψ ∧ φ ) )",
        ref="anass",
        note="anass",
    )

    # 3bitr4i: ( ( φ ∧ ψ ) ∧ χ ) ↔ ( ( χ ∧ ψ ) ∧ φ )
    res = lb.ref(
        "res",
        "( ( φ ∧ ψ ) ∧ χ ) ↔ ( ( χ ∧ ψ ) ∧ φ )",
        s1,
        s2,
        s3,
        ref="3bitr4i",
        note="3bitr4i",
    )

    return lb.build(res)


def prove_an31s(sys: System) -> Proof:
    r"""an31s: ( ( ( ch /\ ps ) /\ ph ) -> th ).

    Hyp: an31s.1 |- ( ( ( ph /\ ps ) /\ ch ) -> th ).
    Concl: |- ( ( ( ch /\ ps ) /\ ph ) -> th ).

    Inference associated with ~ an31 .  (Contributed by NM, 26-Apr-1994.)
    """
    lb = ProofBuilder(sys, "an31s")
    h1 = lb.hyp("an31s.1", r"( ( ( ph /\ ps ) /\ ch ) -> th )")

    # exp31: (((ph /\ ps) /\ ch) -> th) -> (ph -> (ps -> (ch -> th)))
    s1 = lb.ref(
        "s1",
        "( ph -> ( ps -> ( ch -> th ) ) )",
        h1,
        ref="exp31",
        note="exp31 an31s.1",
    )

    # com13: (ph -> (ps -> (ch -> th))) -> (ch -> (ps -> (ph -> th)))
    s2 = lb.ref(
        "s2",
        "( ch -> ( ps -> ( ph -> th ) ) )",
        s1,
        ref="com13",
        note="com13 s1",
    )

    # imp31: (ch -> (ps -> (ph -> th))) -> (((ch /\ ps) /\ ph) -> th)
    res = lb.ref(
        "res",
        r"( ( ( ch /\ ps ) /\ ph ) -> th )",
        s2,
        ref="imp31",
        note="imp31 s2",
    )

    return lb.build(res)


def prove_an13s(sys: System) -> Proof:
    r"""an13s: ( ( ch /\ ( ps /\ ph ) ) -> th ).

    Hyp: an12s.1 |- ( ( ph /\ ( ps /\ ch ) ) -> th ).
    Concl: |- ( ( ch /\ ( ps /\ ph ) ) -> th ).

    Inference associated with ~ an13 .  (Contributed by NM, 26-Apr-1994.)
    """
    lb = ProofBuilder(sys, "an13s")
    h1 = lb.hyp("an12s.1", r"( ( ph /\ ( ps /\ ch ) ) -> th )")

    # exp32: ((ph /\ (ps /\ ch)) -> th) -> (ph -> (ps -> (ch -> th)))
    s1 = lb.ref(
        "s1",
        "( ph -> ( ps -> ( ch -> th ) ) )",
        h1,
        ref="exp32",
        note="exp32 an12s.1",
    )

    # com13: (ph -> (ps -> (ch -> th))) -> (ch -> (ps -> (ph -> th)))
    s2 = lb.ref(
        "s2",
        "( ch -> ( ps -> ( ph -> th ) ) )",
        s1,
        ref="com13",
        note="com13 s1",
    )

    # imp32: (ch -> (ps -> (ph -> th))) -> ((ch /\ (ps /\ ph)) -> th)
    res = lb.ref(
        "res",
        r"( ( ch /\ ( ps /\ ph ) ) -> th )",
        s2,
        ref="imp32",
        note="imp32 s2",
    )

    return lb.build(res)


def prove_ancom2s(sys: System) -> Proof:
    """ancom2s: ( φ ∧ ( χ ∧ ψ ) ) → θ.

    Inference swapping the conjuncts in the second position.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "ancom2s")
    h1 = lb.hyp("an12s.1", "( ( φ ∧ ( ψ ∧ χ ) ) → θ )")

    s1 = lb.ref(
        "s1",
        "( ( χ ∧ ψ ) → ( ψ ∧ χ ) )",
        ref="pm3.22",
        note="pm3.22",
    )

    res = lb.ref(
        "res",
        "( ( φ ∧ ( χ ∧ ψ ) ) → θ )",
        s1,
        h1,
        ref="sylan2",
        note="sylan2",
    )

    return lb.build(res)


def prove_anassrs(sys: System) -> Proof:
    r"""anassrs: ( ( ( ph /\ ps ) /\ ch ) -> th ).

    Associative rearrangement of an antecedent with a conjunction.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "anassrs")
    h1 = lb.hyp("anassrs.1", r"( ( ph /\ ( ps /\ ch ) ) -> th )")

    # exp32: ((ph /\ (ps /\ ch)) -> th) -> (ph -> (ps -> (ch -> th)))
    s1 = lb.ref(
        "s1",
        "( ph -> ( ps -> ( ch -> th ) ) )",
        h1,
        ref="exp32",
        note="exp32",
    )

    # imp31: (ph -> (ps -> (ch -> th))) -> (((ph /\ ps) /\ ch) -> th)
    res = lb.ref(
        "res",
        r"( ( ( ph /\ ps ) /\ ch ) -> th )",
        s1,
        ref="imp31",
        note="imp31",
    )

    return lb.build(res)


def prove_anass1rs(sys: System) -> Proof:
    """anass1rs: ( ( φ ∧ χ ) ∧ ψ ) → θ.

    Inference associated with anassrs. Swap the second and third conjuncts in
    the antecedent, using anassrs on the hypothesis then an32s on that result.
    """
    lb = ProofBuilder(sys, "anass1rs")
    h1 = lb.hyp("anass1rs.1", "( ( φ ∧ ( ψ ∧ χ ) ) → θ )")

    # anassrs: from ( φ ∧ ( ψ ∧ χ ) ) → θ, derive ( ( ( φ ∧ ψ ) ∧ χ ) → θ )
    s1 = lb.ref(
        "s1",
        "( ( ( φ ∧ ψ ) ∧ χ ) → θ )",
        h1,
        ref="anassrs",
        note="anassrs",
    )

    # an32s: from ( ( ( φ ∧ ψ ) ∧ χ ) → θ, derive ( ( ( φ ∧ χ ) ∧ ψ ) → θ )
    res = lb.ref(
        "res",
        "( ( ( φ ∧ χ ) ∧ ψ ) → θ )",
        s1,
        ref="an32s",
        note="an32s",
    )

    return lb.build(res)


def prove_3anassrs(sys: System) -> Proof:
    r"""3anassrs: ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta ).

    Hypothesis: ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ).

    An inference from triple conjunction to quadruple conjunction.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3anassrs")
    h1 = lb.hyp("3anassrs.1", r"( ( ph /\ ( ps /\ ch /\ th ) ) -> ta )")

    # 3exp2: ((ph /\ (ps /\ ch /\ th)) -> ta) -> (ph -> (ps -> (ch -> (th -> ta))))
    s1 = lb.ref(
        "s1",
        "( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )",
        h1,
        ref="3exp2",
        note="3exp2",
    )

    # imp41: (ph -> (ps -> (ch -> (th -> ta)))) -> ((((ph /\ ps) /\ ch) /\ th) -> ta)
    res = lb.ref(
        "res",
        r"( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta )",
        s1,
        ref="imp41",
        note="imp41",
    )

    return lb.build(res)


def prove_3an1rs(sys: System) -> Proof:
    r"""3an1rs: ( ( ( ph /\ ps /\ th ) /\ ch ) -> ta ).

    Hypothesis: ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ).

    Swap the third and fourth antecedents in an inference with 3+1 conjuncts.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3an1rs")
    h1 = lb.hyp("3an1rs.1", r"( ( ( ph /\ ps /\ ch ) /\ th ) -> ta )")

    # 3exp1: (((ph /\ ps /\ ch) /\ th) -> ta) -> (ph -> (ps -> (ch -> (th -> ta))))
    s1 = lb.ref(
        "s1",
        r"( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )",
        h1,
        ref="3exp1",
        note="3exp1",
    )

    # com34: (ph -> (ps -> (ch -> (th -> ta)))) -> (ph -> (ps -> (th -> (ch -> ta))))
    s2 = lb.ref(
        "s2",
        r"( ph -> ( ps -> ( th -> ( ch -> ta ) ) ) )",
        s1,
        ref="com34",
        note="com34",
    )

    # 3imp1: (ph -> (ps -> (th -> (ch -> ta)))) -> (((ph /\ ps /\ th) /\ ch) -> ta)
    res = lb.ref(
        "res",
        r"( ( ( ph /\ ps /\ th ) /\ ch ) -> ta )",
        s2,
        ref="3imp1",
        note="3imp1",
    )

    return lb.build(res)


def prove_imp41(sys: System) -> Proof:
    r"""imp41: ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta ).

    Importation of a quadruple conjunction.  If ph implies ps implies ch
    implies th implies ta, then ph and ps and ch and th together imply ta.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "imp41")
    h1 = lb.hyp("imp4.1", "( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )")

    # imp31: (ph -> (ps -> (ch -> (th -> ta)))) -> (((ph /\ ps) /\ ch) -> (th -> ta))
    s1 = lb.ref(
        "s1",
        r"( ( ( ph /\ ps ) /\ ch ) -> ( th -> ta ) )",
        h1,
        ref="imp31",
        note="imp31",
    )

    # imp: (((ph /\ ps) /\ ch) -> (th -> ta)) -> ((((ph /\ ps) /\ ch) /\ th) -> ta)
    res = lb.ref(
        "res",
        r"( ( ( ( ph /\ ps ) /\ ch ) /\ th ) -> ta )",
        s1,
        ref="imp",
        note="imp",
    )

    return lb.build(res)


def prove_imp42(sys: System) -> Proof:
    r"""imp42: ( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ta ).

    Importation with a nested conjunct in the first two antecedents.
    If ph implies ps implies ch implies th implies ta, then ph and the
    conjunction of ps and ch together with th imply ta.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "imp42")
    h1 = lb.hyp("imp4.1", "( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )")
    s1 = lb.ref(
        "s1",
        r"( ( ph /\ ( ps /\ ch ) ) -> ( th -> ta ) )",
        h1,
        ref="imp32",
        note="imp32",
    )
    res = lb.ref(
        "res",
        r"( ( ( ph /\ ( ps /\ ch ) ) /\ th ) -> ta )",
        s1,
        ref="imp",
        note="imp",
    )
    return lb.build(res)


def prove_imp43(sys: System) -> Proof:
    r"""imp43: ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ).

    An importation inference.  If ph implies ps implies ch implies
    th implies ta, then ph and ps together with ch and th imply ta.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "imp43")
    h1 = lb.hyp("imp4.1", "( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )")

    # imp4b: (ph -> (ps -> (ch -> (th -> ta)))) -> ((ph /\ ps) -> ((ch /\ th) -> ta))
    s1 = lb.ref(
        "s1",
        r"( ( ph /\ ps ) -> ( ( ch /\ th ) -> ta ) )",
        h1,
        ref="imp4b",
        note="imp4b",
    )

    # imp: ((ph /\ ps) -> ((ch /\ th) -> ta)) -> (((ph /\ ps) /\ (ch /\ th)) -> ta)
    res = lb.ref(
        "res",
        r"( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta )",
        s1,
        ref="imp",
        note="imp",
    )

    return lb.build(res)


def prove_imp44(sys: System) -> Proof:
    r"""imp44: ( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ta ).

    An importation inference.  If ph implies ps implies ch implies
    th implies ta, then ph and ps and ch together with th imply ta.
    (Contributed by NM, 28-Mar-1995.)
    """
    lb = ProofBuilder(sys, "imp44")
    h1 = lb.hyp("imp4.1", "( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )")

    # imp4c: h1 -> (ph -> (((ps /\ ch) /\ th) -> ta))
    s1 = lb.ref(
        "s1",
        r"( ph -> ( ( ( ps /\ ch ) /\ th ) -> ta ) )",
        h1,
        ref="imp4c",
        note="imp4c",
    )

    # imp: (ph -> (((ps /\ ch) /\ th) -> ta)) -> ((ph /\ ((ps /\ ch) /\ th)) -> ta)
    res = lb.ref(
        "res",
        r"( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ta )",
        s1,
        ref="imp",
        note="imp",
    )

    return lb.build(res)


def prove_imp45(sys: System) -> Proof:
    r"""imp45: ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) -> ta ).

    An importation inference.  If ph implies ps implies ch implies
    th implies ta, then ph and the conjunction of ps, ch, th and ta
    together imply ta.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "imp45")
    h1 = lb.hyp("imp4.1", "( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )")

    # imp4d: h1 -> (ph -> ((ps /\ (ch /\ th)) -> ta))
    s1 = lb.ref(
        "s1",
        r"( ph -> ( ( ps /\ ( ch /\ th ) ) -> ta ) )",
        h1,
        ref="imp4d",
        note="imp4d",
    )

    # imp: (ph -> ((ps /\ (ch /\ th)) -> ta)) -> ((ph /\ (ps /\ (ch /\ th))) -> ta)
    res = lb.ref(
        "res",
        r"( ( ph /\ ( ps /\ ( ch /\ th ) ) ) -> ta )",
        s1,
        ref="imp",
        note="imp",
    )

    return lb.build(res)


def prove_imp4b(sys: System) -> Proof:
    r"""imp4b: ( ( ph /\ ps ) -> ( ( ch /\ th ) -> ta ) ).

    An importation inference.  If ph implies ps implies ch implies th
    implies ta, then ph and ps together imply that ch and th together
    imply ta.
    (Contributed by NM, 26-Apr-1994.)
    """
    lb = ProofBuilder(sys, "imp4b")
    h1 = lb.hyp("imp4.1", "( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )")

    # imp: (ph -> (ps -> (ch -> (th -> ta)))) -> ((ph /\ ps) -> (ch -> (th -> ta)))
    s1 = lb.ref(
        "s1",
        r"( ( ph /\ ps ) -> ( ch -> ( th -> ta ) ) )",
        h1,
        ref="imp",
        note="imp",
    )

    # impd: ((ph /\ ps) -> (ch -> (th -> ta))) -> ((ph /\ ps) -> ((ch /\ th) -> ta))
    res = lb.ref(
        "res",
        r"( ( ph /\ ps ) -> ( ( ch /\ th ) -> ta ) )",
        s1,
        ref="impd",
        note="impd",
    )

    return lb.build(res)


def prove_imp4a(sys: System) -> Proof:
    r"""imp4a: ( ph -> ( ps -> ( ( ch /\ th ) -> ta ) ) ).

    An importation inference.  If ph implies ps implies ch implies th
    implies ta, then ph implies ps implies that ch and th together imply
    ta.
    (Contributed by NM, 26-Apr-1994.)
    """
    lb = ProofBuilder(sys, "imp4a")
    h1 = lb.hyp("imp4.1", "( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )")

    # imp4b: imp4.1 -> ((ph /\ ps) -> ((ch /\ th) -> ta))
    s1 = lb.ref(
        "s1",
        r"( ( ph /\ ps ) -> ( ( ch /\ th ) -> ta ) )",
        h1,
        ref="imp4b",
        note="imp4b",
    )

    # ex: ((ph /\ ps) -> ((ch /\ th) -> ta)) -> (ph -> (ps -> ((ch /\ th) -> ta)))
    res = lb.ref(
        "res",
        r"( ph -> ( ps -> ( ( ch /\ th ) -> ta ) ) )",
        s1,
        ref="ex",
        note="ex",
    )

    return lb.build(res)


def prove_imp4d(sys: System) -> Proof:
    r"""imp4d: ( ph -> ( ( ps /\ ( ch /\ th ) ) -> ta ) ).

    Deduction form of imp4.  If ph implies ps implies ch implies th
    implies ta, then ph implies that ps and ch and th together imply ta.
    (Contributed by NM, 26-Apr-1994.)
    """
    lb = ProofBuilder(sys, "imp4d")
    h1 = lb.hyp("imp4.1", "( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )")

    # imp4a: imp4.1 -> (ph -> (ps -> ((ch /\ th) -> ta)))
    s1 = lb.ref(
        "s1",
        r"( ph -> ( ps -> ( ( ch /\ th ) -> ta ) ) )",
        h1,
        ref="imp4a",
        note="imp4a",
    )

    # impd: (ph -> (ps -> ((ch /\ th) -> ta))) -> (ph -> ((ps /\ (ch /\ th)) -> ta))
    res = lb.ref(
        "res",
        r"( ph -> ( ( ps /\ ( ch /\ th ) ) -> ta ) )",
        s1,
        ref="impd",
        note="impd",
    )

    return lb.build(res)


def prove_imp4c(sys: System) -> Proof:
    r"""imp4c: ( ph -> ( ( ( ps /\ ch ) /\ th ) -> ta ) ).

    If ph implies ps implies ch implies th implies ta, then ph implies
    that ps and ch together with th imply ta.
    (Contributed by NM, 26-Apr-1994.)
    """
    lb = ProofBuilder(sys, "imp4c")
    h1 = lb.hyp("imp4.1", "( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )")

    # impd: imp4.1 -> (ph -> ((ps /\ ch) -> (th -> ta)))
    s1 = lb.ref(
        "s1",
        r"( ph -> ( ( ps /\ ch ) -> ( th -> ta ) ) )",
        h1,
        ref="impd",
        note="impd",
    )

    # impd: (ph -> ((ps /\ ch) -> (th -> ta))) -> (ph -> (((ps /\ ch) /\ th) -> ta))
    res = lb.ref(
        "res",
        r"( ph -> ( ( ( ps /\ ch ) /\ th ) -> ta ) )",
        s1,
        ref="impd",
        note="impd",
    )

    return lb.build(res)


def prove_imp5d(sys: System) -> Proof:
    r"""imp5d: ( ( ( ph /\ ps ) /\ ch ) -> ( ( th /\ ta ) -> et ) ).

    Deduction form of imp5.  If ph implies ps implies ch implies
    th implies ta implies et, then ph and ps and ch together imply
    that th and ta together imply et.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "imp5d")
    h1 = lb.hyp("imp5.1", "( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) )")

    # imp31: imp5.1 -> (((ph /\ ps) /\ ch) -> (th -> (ta -> et)))
    s1 = lb.ref(
        "s1",
        r"( ( ( ph /\ ps ) /\ ch ) -> ( th -> ( ta -> et ) ) )",
        h1,
        ref="imp31",
        note="imp31",
    )

    # impd: (((ph /\ ps) /\ ch) -> (th -> (ta -> et))) ->
    #       (((ph /\ ps) /\ ch) -> ((th /\ ta) -> et))
    res = lb.ref(
        "res",
        r"( ( ( ph /\ ps ) /\ ch ) -> ( ( th /\ ta ) -> et ) )",
        s1,
        ref="impd",
        note="impd",
    )

    return lb.build(res)


def prove_imp5a(sys: System) -> Proof:
    r"""imp5a: ( ph -> ( ps -> ( ch -> ( ( th /\ ta ) -> et ) ) ) ).

    An importation inference.  If ph implies ps implies ch implies
    th implies ta implies et, then ph implies ps implies ch implies
    that th and ta together imply et.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "imp5a")
    h1 = lb.hyp("imp5.1", "( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) )")

    # imp5d: imp5.1 -> (((ph /\ ps) /\ ch) -> ((th /\ ta) -> et))
    s1 = lb.ref(
        "s1",
        r"( ( ( ph /\ ps ) /\ ch ) -> ( ( th /\ ta ) -> et ) )",
        h1,
        ref="imp5d",
        note="imp5d",
    )

    # exp31: (((ph /\ ps) /\ ch) -> ((th /\ ta) -> et)) ->
    #        (ph -> (ps -> (ch -> ((th /\ ta) -> et))))
    res = lb.ref(
        "res",
        r"( ph -> ( ps -> ( ch -> ( ( th /\ ta ) -> et ) ) ) )",
        s1,
        ref="exp31",
        note="exp31",
    )

    return lb.build(res)


def prove_imp5g(sys: System) -> Proof:
    r"""imp5g: ( ( ph /\ ps ) -> ( ( ( ch /\ th ) /\ ta ) -> et ) ).

    An importation inference.  If ph implies ps implies ch implies
    th implies ta implies et, then ph and ps together imply that
    ch, th, and ta together imply et.
    (Contributed by NM, 26-Apr-1994.)
    """
    lb = ProofBuilder(sys, "imp5g")
    h1 = lb.hyp("imp5.1", "( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) )")

    # imp4b: imp5.1 -> ((ph /\ ps) -> ((ch /\ th) -> (ta -> et)))
    s1 = lb.ref(
        "s1",
        r"( ( ph /\ ps ) -> ( ( ch /\ th ) -> ( ta -> et ) ) )",
        h1,
        ref="imp4b",
        note="imp4b",
    )

    # impd: ((ph /\ ps) -> ((ch /\ th) -> (ta -> et))) ->
    #       ((ph /\ ps) -> (((ch /\ th) /\ ta) -> et))
    res = lb.ref(
        "res",
        r"( ( ph /\ ps ) -> ( ( ( ch /\ th ) /\ ta ) -> et ) )",
        s1,
        ref="impd",
        note="impd",
    )

    return lb.build(res)


def prove_imp55(sys: System) -> Proof:
    r"""imp55: ( ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) /\ ta ) -> et ).

    An importation inference.  If ph implies ps implies ch implies
    th implies ta implies et, then ph and the conjunction of ps with
    the conjunction of ch and th, together with ta, imply et.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "imp55")
    h1 = lb.hyp("imp5.1", "( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) )")

    # imp4a: imp5.1 -> (ph -> (ps -> ((ch /\ th) -> (ta -> et))))
    s1 = lb.ref(
        "s1",
        r"( ph -> ( ps -> ( ( ch /\ th ) -> ( ta -> et ) ) ) )",
        h1,
        ref="imp4a",
        note="imp4a",
    )

    # imp42: s1 -> (((ph /\ (ps /\ (ch /\ th))) /\ ta) -> et)
    res = lb.ref(
        "res",
        r"( ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) /\ ta ) -> et )",
        s1,
        ref="imp42",
        note="imp42",
    )

    return lb.build(res)


def prove_imp511(sys: System) -> Proof:
    r"""imp511: ( ( ph /\ ( ( ps /\ ( ch /\ th ) ) /\ ta ) ) -> et ).

    An importation inference.  If ph implies ps implies ch implies
    th implies ta implies et, then ph and the conjunction of ps with
    the conjunction of ch and th, together with ta, imply et.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "imp511")
    h1 = lb.hyp("imp5.1", "( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) )")

    # imp4a: imp5.1 -> (ph -> (ps -> ((ch /\ th) -> (ta -> et))))
    s1 = lb.ref(
        "s1",
        r"( ph -> ( ps -> ( ( ch /\ th ) -> ( ta -> et ) ) ) )",
        h1,
        ref="imp4a",
        note="imp4a",
    )

    # imp44: s1 -> ((ph /\ ((ps /\ (ch /\ th)) /\ ta)) -> et)
    res = lb.ref(
        "res",
        r"( ( ph /\ ( ( ps /\ ( ch /\ th ) ) /\ ta ) ) -> et )",
        s1,
        ref="imp44",
        note="imp44",
    )

    return lb.build(res)


def prove_3imp(sys: System) -> Proof:
    r"""3imp: ( ( ph /\ ps /\ ch ) -> th ).

    Importation of a triple conjunction using imp31 and 3impa.
    If ph implies ps implies ch implies th, then the ternary
    conjunction of ph, ps, and ch implies th.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3imp")
    h1 = lb.hyp("3imp.1", "( ph -> ( ps -> ( ch -> th ) ) )")
    s1 = lb.ref(
        "s1",
        r"( ( ( ph /\ ps ) /\ ch ) -> th )",
        h1,
        ref="imp31",
        note="imp31",
    )
    res = lb.ref(
        "res",
        r"( ph /\ ps /\ ch ) -> th",
        s1,
        ref="3impa",
        note="3impa",
    )
    return lb.build(res)


def prove_3impb(sys: System) -> Proof:
    r"""3impb: ( ( ph /\ ps /\ ch ) -> th ).

    Importation from a triple conjunction.  The hypothesis
    3impb.1 is ``( ( ph /\ ( ps /\ ch ) ) -> th )``.
    (Contributed by NM, 26-Apr-1994.)
    """
    lb = ProofBuilder(sys, "3impb")
    h1 = lb.hyp("3impb.1", r"( ( ph /\ ( ps /\ ch ) ) -> th )")
    s1 = lb.ref(
        "s1",
        "( ph -> ( ps -> ( ch -> th ) ) )",
        h1,
        ref="exp32",
        note="exp32",
    )
    res = lb.ref(
        "res",
        r"( ph /\ ps /\ ch ) -> th",
        s1,
        ref="3imp",
        note="3imp",
    )
    return lb.build(res)


def prove_3impia(sys: System) -> Proof:
    r"""3impia: ( ( ph /\ ps /\ ch ) -> th ).

    Importation inference from a hypothesis using binary conjunction
    to derive the same with ternary conjunction.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3impia")
    h1 = lb.hyp("3impia.1", "( ( ph /\\ ps ) -> ( ch -> th ) )")
    s1 = lb.ref(
        "s1",
        "( ph -> ( ( ps /\\ ch ) -> th ) )",
        h1,
        ref="expimpd",
        note="expimpd 3impia.1",
    )
    res = lb.ref(
        "res",
        "( ph /\\ ps /\\ ch ) -> th",
        s1,
        ref="3impib",
        note="3impib s1",
    )
    return lb.build(res)


def prove_3impib(sys: System) -> Proof:
    r"""3impib: ( ( ph /\ ps /\ ch ) -> th ).

    Importation inference.  The hypothesis 3impib.1 is
    ``( ph -> ( ( ps /\ ch ) -> th ) )``.
    (Contributed by NM, 26-Apr-1994.)
    """
    lb = ProofBuilder(sys, "3impib")
    h1 = lb.hyp("3impib.1", r"( ph -> ( ( ps /\ ch ) -> th ) )")
    s1 = lb.ref(
        "s1",
        "( ph -> ( ps -> ( ch -> th ) ) )",
        h1,
        ref="expd",
        note="expd",
    )
    res = lb.ref(
        "res",
        r"( ph /\ ps /\ ch ) -> th",
        s1,
        ref="3imp",
        note="3imp",
    )
    return lb.build(res)


def prove_3imp231(sys: System) -> Proof:
    r"""3imp231: ( ( ps /\ ch /\ ph ) -> th ).

    Importation inference with premises permuted to the order
    ps, ch, ph instead of ph, ps, ch.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3imp231")
    h1 = lb.hyp("3imp.1", "( ph -> ( ps -> ( ch -> th ) ) )")
    s1 = lb.ref(
        "s1",
        "( ps -> ( ch -> ( ph -> th ) ) )",
        h1,
        ref="com3l",
        note="com3l",
    )
    res = lb.ref(
        "res",
        r"( ps /\ ch /\ ph ) -> th",
        s1,
        ref="3imp",
        note="3imp",
    )
    return lb.build(res)


def prove_3imp21(sys: System) -> Proof:
    r"""3imp21: ( ( ps /\ ph /\ ch ) -> th ).

    Importation inference with premises permuted to a different
    ternary conjunction order — ps, ph, ch instead of ph, ps, ch.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3imp21")
    h1 = lb.hyp("3imp.1", "( ph -> ( ps -> ( ch -> th ) ) )")
    s1 = lb.ref(
        "s1",
        "( ch -> ( ps -> ( ph -> th ) ) )",
        h1,
        ref="com13",
        note="com13",
    )
    res = lb.ref(
        "res",
        r"( ps /\ ph /\ ch ) -> th",
        s1,
        ref="3imp231",
        note="3imp231",
    )
    return lb.build(res)


def prove_3imp31(sys: System) -> Proof:
    r"""3imp31: ( ( ch /\ ps /\ ph ) -> th ).

    Importation inference with premises permuted to a different
    ternary conjunction order — ch, ps, ph instead of ph, ps, ch.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3imp31")
    h1 = lb.hyp("3imp.1", "( ph -> ( ps -> ( ch -> th ) ) )")
    s1 = lb.ref(
        "s1",
        "( ch -> ( ps -> ( ph -> th ) ) )",
        h1,
        ref="com13",
        note="com13",
    )
    res = lb.ref(
        "res",
        r"( ch /\ ps /\ ph ) -> th",
        s1,
        ref="3imp",
        note="3imp",
    )
    return lb.build(res)


def prove_3com12(sys: System) -> Proof:
    r"""3com12: ( ( ps /\ ph /\ ch ) -> th ).

    Commutation of antecedents — swap the first two conjuncts in a
    ternary conjunction.  Uses `3exp` to export then `3imp21` to
    re-import in the permuted order.  (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3com12")
    h1 = lb.hyp("3exp.1", r"( ph /\ ps /\ ch ) -> th")
    s1 = lb.ref(
        "s1",
        "( ph -> ( ps -> ( ch -> th ) ) )",
        h1,
        ref="3exp",
        note="3exp 3exp.1",
    )
    res = lb.ref(
        "res",
        r"( ps /\ ph /\ ch ) -> th",
        s1,
        ref="3imp21",
        note="3imp21",
    )
    return lb.build(res)


def prove_3com13(sys: System) -> Proof:
    r"""3com13: ( ( ch /\ ps /\ ph ) -> th ).

    Commutation of antecedents — swap the first and third conjuncts in a
    ternary conjunction.  Uses `3exp` to export then `3imp31` to
    re-import in the permuted order.  (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3com13")
    h1 = lb.hyp("3exp.1", r"( ph /\ ps /\ ch ) -> th")
    s1 = lb.ref(
        "s1",
        "( ph -> ( ps -> ( ch -> th ) ) )",
        h1,
        ref="3exp",
        note="3exp 3exp.1",
    )
    res = lb.ref(
        "res",
        r"( ch /\ ps /\ ph ) -> th",
        s1,
        ref="3imp31",
        note="3imp31",
    )
    return lb.build(res)


def prove_3comr(sys: System) -> Proof:
    r"""3comr: ( ( ch /\ ph /\ ps ) -> th ).

    Commutation of antecedents — rotate the three conjuncts so that
    the first moves to the end: ph, ps, ch → ch, ph, ps.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3comr")
    h1 = lb.hyp("3exp.1", r"( ph /\ ps /\ ch ) -> th")
    s1 = lb.ref(
        "s1",
        r"( ps /\ ph /\ ch ) -> th",
        h1,
        ref="3com12",
        note="3com12 3exp.1",
    )
    res = lb.ref(
        "res",
        r"( ch /\ ph /\ ps ) -> th",
        s1,
        ref="3com13",
        note="3com13",
    )
    return lb.build(res)


def prove_3com23(sys: System) -> Proof:
    r"""3com23: ( ( ph /\ ch /\ ps ) -> th ).

    Commutation of antecedents — swap the second and third conjuncts in a
    ternary conjunction.  Uses `3comr` to rotate then `3com12` to swap the
    first two.  (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3com23")
    h1 = lb.hyp("3exp.1", r"( ph /\ ps /\ ch ) -> th")
    s1 = lb.ref(
        "s1",
        r"( ch /\ ph /\ ps ) -> th",
        h1,
        ref="3comr",
        note="3comr 3exp.1",
    )
    res = lb.ref(
        "res",
        r"( ph /\ ch /\ ps ) -> th",
        s1,
        ref="3com12",
        note="3com12",
    )
    return lb.build(res)


def prove_3coml(sys: System) -> Proof:
    r"""3coml: ( ( ps /\ ch /\ ph ) -> th ).

    Commutation of antecedents — rotate the three conjuncts so that
    the first moves to the second position, the second to the first,
    and the third remains in place: ph, ps, ch -> ps, ch, ph.
    Uses 3com23 to swap the second and third, then 3com13 to swap
    the first and third.  (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3coml")
    h1 = lb.hyp("3exp.1", r"( ph /\ ps /\ ch ) -> th")
    s1 = lb.ref(
        "s1",
        r"( ph /\ ch /\ ps ) -> th",
        h1,
        ref="3com23",
        note="3com23 3exp.1",
    )
    res = lb.ref(
        "res",
        r"( ps /\ ch /\ ph ) -> th",
        s1,
        ref="3com13",
        note="3com13",
    )

    return lb.build(res)


def prove_3impd(sys: System) -> Proof:
    r"""3impd: ( ph -> ( ( ps /\ ch /\ th ) -> ta ) ).

    Importation inference with three antecedents.
    If ph implies ps implies ch implies th implies ta, then ph implies
    the triple conjunction of ps, ch, and th implies ta.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3impd")
    h1 = lb.hyp("3impd.1", "( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )")
    s1 = lb.ref(
        "s1",
        "( ps -> ( ch -> ( th -> ( ph -> ta ) ) ) )",
        h1,
        ref="com4l",
        note="com4l",
    )
    s2 = lb.ref(
        "s2",
        r"( ps /\ ch /\ th ) -> ( ph -> ta )",
        s1,
        ref="3imp",
        note="3imp",
    )
    res = lb.ref(
        "res",
        r"( ph -> ( ( ps /\ ch /\ th ) -> ta ) )",
        s2,
        ref="com12",
        note="com12",
    )
    return lb.build(res)


def prove_3impexp(sys: System) -> Proof:
    r"""3impexp: ( ( ( ph /\ ps /\ ch ) -> th ) <-> ( ph -> ( ps -> ( ch -> th ) ) ) ).

    Import-export theorem for ternary conjunction.  The conjunction
    of ph, ps, and ch implies th iff ph implies ps implies ch implies th.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3impexp")
    s1 = lb.ref(
        "s1",
        r"( ( ( ph /\ ps /\ ch ) -> th ) -> ( ( ph /\ ps /\ ch ) -> th ) )",
        ref="id",
        note="id",
    )
    s2 = lb.ref(
        "s2",
        r"( ( ( ph /\ ps /\ ch ) -> th ) -> ( ph -> ( ps -> ( ch -> th ) ) ) )",
        s1,
        ref="3expd",
        note="3expd",
    )
    s3 = lb.ref(
        "s3",
        r"( ( ph -> ( ps -> ( ch -> th ) ) ) -> ( ph -> ( ps -> ( ch -> th ) ) ) )",
        ref="id",
        note="id",
    )
    s4 = lb.ref(
        "s4",
        r"( ( ph -> ( ps -> ( ch -> th ) ) ) -> ( ( ph /\ ps /\ ch ) -> th ) )",
        s3,
        ref="3impd",
        note="3impd",
    )
    res = lb.ref(
        "res",
        r"( ( ( ph /\ ps /\ ch ) -> th ) <-> ( ph -> ( ps -> ( ch -> th ) ) ) )",
        s2,
        s4,
        ref="impbii",
        note="impbii",
    )
    return lb.build(res)


def prove_bi23imp13(sys: System) -> Proof:
    r"""bi23imp13: ( ( ph /\ ps /\ ch ) -> th ).

    Import a biconditional into a ternary conjunction.  If ph implies
    that ps is equivalent to (ch implies th), then the ternary
    conjunction of ph, ps, and ch implies th.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "bi23imp13")
    h1 = lb.hyp("bi23imp13.1", "( ph -> ( ps <-> ( ch -> th ) ) )")
    s1 = lb.ref(
        "s1",
        "( ph -> ( ps -> ( ch -> th ) ) )",
        h1,
        ref="biimpd",
        note="biimpd",
    )
    res = lb.ref(
        "res",
        r"( ph /\ ps /\ ch ) -> th",
        s1,
        ref="3imp",
        note="3imp",
    )
    return lb.build(res)


def prove_3imp1(sys: System) -> Proof:
    r"""3imp1: ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta ).

    Importation of a quadruple conjunction with ternary conjunction
    for the first three antecedents.  If ph implies ps implies ch
    implies th implies ta, then the ternary conjunction of ph, ps, ch
    together with th implies ta.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3imp1")
    h1 = lb.hyp("3imp1.1", "( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )")
    s1 = lb.ref(
        "s1",
        r"( ph /\ ps /\ ch ) -> ( th -> ta )",
        h1,
        ref="3imp",
        note="3imp",
    )
    res = lb.ref(
        "res",
        r"( ( ( ph /\ ps /\ ch ) /\ th ) -> ta )",
        s1,
        ref="imp",
        note="imp",
    )
    return lb.build(res)


def prove_3imp2(sys: System) -> Proof:
    r"""3imp2: ( ( ph /\ ( ps /\ ch /\ th ) ) -> ta ).

    Importation with a ternary conjunction as the second conjunct.
    If ph implies ps implies ch implies th implies ta, then ph and
    the ternary conjunction of ps, ch, th imply ta.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3imp2")
    h1 = lb.hyp("3imp1.1", "( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )")
    s1 = lb.ref(
        "s1",
        r"( ph -> ( ( ps /\ ch /\ th ) -> ta ) )",
        h1,
        ref="3impd",
        note="3impd",
    )
    res = lb.ref(
        "res",
        r"( ( ph /\ ( ps /\ ch /\ th ) ) -> ta )",
        s1,
        ref="imp",
        note="imp",
    )
    return lb.build(res)


def prove_imp32(sys: System) -> Proof:
    r"""imp32: ( ( ph /\ ( ps /\ ch ) ) -> th ).

    Importation with a nested conjunct.  If ph implies ps implies ch
    implies th, then ph and the conjunction of ps and ch together imply th.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "imp32")
    h1 = lb.hyp("imp31.1", "( ph -> ( ps -> ( ch -> th ) ) )")
    s1 = lb.ref(
        "s1",
        "( ph -> ( ( ps /\\ ch ) -> th ) )",
        h1,
        ref="impd",
        note="impd",
    )
    res = lb.ref(
        "res",
        "( ( ph /\\ ( ps /\\ ch ) ) -> th )",
        s1,
        ref="imp",
        note="imp",
    )
    return lb.build(res)


def prove_impr(sys: System) -> Proof:
    r"""impr: ( ( ph /\ ( ps /\ ch ) ) -> th ).

    Importation with a nested conjunct.  If ph and ps implies ch implies
    th, then ph and the conjunction of ps and ch together imply th.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "impr")
    h1 = lb.hyp("impr.1", "( ( ph /\\ ps ) -> ( ch -> th ) )")
    s1 = lb.ref(
        "s1",
        "( ph -> ( ps -> ( ch -> th ) ) )",
        h1,
        ref="ex",
        note="ex impr.1",
    )
    res = lb.ref(
        "res",
        "( ( ph /\\ ( ps /\\ ch ) ) -> th )",
        s1,
        ref="imp32",
        note="imp32",
    )
    return lb.build(res)


def prove_pm4_14(sys: System) -> Proof:
    r"""pm4.14: ( ( ( ph /\ ps ) -> ch ) <-> ( ( ph /\ -. ch ) -> -. ps ) ).

    Theorem *4.14 of [WhiteheadRussell] p. 117.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "pm4.14")

    # con34b: ( ( ps -> ch ) <-> ( -. ch -> -. ps ) )
    s1 = lb.ref(
        "s1",
        r"( ( ps -> ch ) <-> ( -. ch -> -. ps ) )",
        ref="con34b",
        note="con34b",
    )

    # imbi2i: ( ph -> ( ps -> ch ) ) <-> ( ph -> ( -. ch -> -. ps ) )
    s2 = lb.ref(
        "s2",
        r"( ph -> ( ps -> ch ) ) <-> ( ph -> ( -. ch -> -. ps ) )",
        s1,
        ref="imbi2i",
        note="imbi2i",
    )

    # impexp: ( ( ( ph /\ ps ) -> ch ) <-> ( ph -> ( ps -> ch ) ) )
    s3 = lb.ref(
        "s3",
        r"( ( ( ph /\ ps ) -> ch ) <-> ( ph -> ( ps -> ch ) ) )",
        ref="impexp",
        note="impexp",
    )

    # impexp with -. ch for ps and -. ps for ch:
    # ( ( ( ph /\ -. ch ) -> -. ps ) <-> ( ph -> ( -. ch -> -. ps ) ) )
    s4 = lb.ref(
        "s4",
        r"( ( ( ph /\ -. ch ) -> -. ps ) <-> ( ph -> ( -. ch -> -. ps ) ) )",
        ref="impexp",
        note="impexp",
    )

    # 3bitr4i: chain s2, s3, s4
    res = lb.ref(
        "res",
        r"( ( ( ph /\ ps ) -> ch ) <-> ( ( ph /\ -. ch ) -> -. ps ) )",
        s2,
        s3,
        s4,
        ref="3bitr4i",
        note="3bitr4i",
    )
    return lb.build(res)


def prove_pm3_37(sys: System) -> Proof:
    """pm3.37: ( ( φ ∧ ψ ) → χ ) → ( ( φ ∧ ¬ χ ) → ¬ ψ ).

    Consequent manipulation of antecedents (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "pm3.37")

    # pm4.14: ( ( ( φ ∧ ψ ) → χ ) ↔ ( ( φ ∧ ¬ χ ) → ¬ ψ ) )
    s1 = lb.ref(
        "s1",
        "( ( ( φ ∧ ψ ) → χ ) ↔ ( ( φ ∧ ¬ χ ) → ¬ ψ ) )",
        ref="pm4.14",
        note="pm4.14",
    )

    # biimpi: ( ( ( φ ∧ ψ ) → χ ) → ( ( φ ∧ ¬ χ ) → ¬ ψ ) )
    res = lb.ref(
        "res",
        "( ( ( φ ∧ ψ ) → χ ) → ( ( φ ∧ ¬ χ ) → ¬ ψ ) )",
        s1,
        ref="biimpi",
        note="biimpi",
    )
    return lb.build(res)


def prove_pm3_21(sys: System) -> Proof:
    """pm3.21: φ → (ψ → (ψ ∧ φ)).

    Commuted conjunction introduction.  If φ and ψ hold individually, then
    their conjunction holds in reverse order.
    (Contributed by NM, 5-Jan-1993.)
    """
    lb = ProofBuilder(sys, "pm3.21")
    s_id = lb.ref(
        "s_id",
        "( ψ ∧ φ ) → ( ψ ∧ φ )",
        ref="id",
        note="id",
    )
    res = lb.ref(
        "res",
        "φ → ( ψ → ( ψ ∧ φ ) )",
        s_id,
        ref="expcom",
        note="expcom",
    )
    return lb.build(res)


def prove_pm3_22(sys: System) -> Proof:
    """pm3.22: ( φ ∧ ψ ) → ( ψ ∧ φ ).

    Commutative law for conjunction.  (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "pm3.22")
    s_id = lb.ref(
        "s_id",
        "( ( ψ ∧ φ ) → ( ψ ∧ φ ) )",
        ref="id",
        note="id",
    )
    res = lb.ref(
        "res",
        "( ( φ ∧ ψ ) → ( ψ ∧ φ ) )",
        s_id,
        ref="ancoms",
        note="ancoms",
    )
    return lb.build(res)


def prove_ancom(sys: System) -> Proof:
    """ancom: ( ( φ ∧ ψ ) ↔ ( ψ ∧ φ ) ).

    Commutative law for conjunction — biconditional form.  If φ and ψ
    hold together, then ψ and φ hold together, and vice versa.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "ancom")
    s1 = lb.ref("s1", "( φ ∧ ψ ) → ( ψ ∧ φ )", ref="pm3.22", note="pm3.22")
    s2 = lb.ref("s2", "( ψ ∧ φ ) → ( φ ∧ ψ )", ref="pm3.22", note="pm3.22")
    res = lb.ref("res", "( ( φ ∧ ψ ) ↔ ( ψ ∧ φ ) )", s1, s2, ref="impbii", note="impbii")
    return lb.build(res)


def prove_ancomd(sys: System) -> Proof:
    """ancomd: φ → ( χ ∧ ψ ).

    Hyp 1: φ → ( ψ ∧ χ )
    Concl: φ → ( χ ∧ ψ )

    Deduction form of ancom — swap the conjuncts under an implication.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "ancomd")
    h1 = lb.hyp("ancomd.1", "φ → ( ψ ∧ χ )")
    s1 = lb.ref("s1", "( ψ ∧ χ ) ↔ ( χ ∧ ψ )", ref="ancom", note="ancom")
    res = lb.ref("res", "φ → ( χ ∧ ψ )", h1, s1, ref="sylib", note="sylib")
    return lb.build(res)


def prove_an12(sys: System) -> Proof:
    """an12: ( ( φ ∧ ( ψ ∧ χ ) ) ↔ ( ψ ∧ ( φ ∧ χ ) ) ).

    Swap the first two conjuncts in a nested conjunction — biconditional
    form.  (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "an12")

    # ancom: ( ψ ∧ χ ) ↔ ( χ ∧ ψ )
    s1 = lb.ref(
        "s1",
        "( ψ ∧ χ ) ↔ ( χ ∧ ψ )",
        ref="ancom",
        note="ancom",
    )

    # bianass: ( φ ∧ ( ψ ∧ χ ) ) ↔ ( ( φ ∧ χ ) ∧ ψ )
    s2 = lb.ref(
        "s2",
        "( φ ∧ ( ψ ∧ χ ) ) ↔ ( ( φ ∧ χ ) ∧ ψ )",
        s1,
        ref="bianass",
        note="bianass",
    )

    # biancomi: ( φ ∧ ( ψ ∧ χ ) ) ↔ ( ψ ∧ ( φ ∧ χ ) )
    res = lb.ref(
        "res",
        "( ( φ ∧ ( ψ ∧ χ ) ) ↔ ( ψ ∧ ( φ ∧ χ ) ) )",
        s2,
        ref="biancomi",
        note="biancomi",
    )

    return lb.build(res)


def prove_an13(sys: System) -> Proof:
    """an13: ( ( φ ∧ ( ψ ∧ χ ) ) ↔ ( χ ∧ ( ψ ∧ φ ) ) ).

    Swap the first and third conjuncts in a nested conjunction.
    """
    lb = ProofBuilder(sys, "an13")

    # ancom: ( ( ψ ∧ χ ) ∧ φ ) ↔ ( φ ∧ ( ψ ∧ χ ) )
    s1 = lb.ref(
        "s1",
        "( ( ψ ∧ χ ) ∧ φ ) ↔ ( φ ∧ ( ψ ∧ χ ) )",
        ref="ancom",
        note="ancom",
    )

    # an21: ( ( ψ ∧ χ ) ∧ φ ) ↔ ( χ ∧ ( ψ ∧ φ ) )
    s2 = lb.ref(
        "s2",
        "( ( ψ ∧ χ ) ∧ φ ) ↔ ( χ ∧ ( ψ ∧ φ ) )",
        ref="an21",
        note="an21",
    )

    # bitr3i: ( ( φ ∧ ( ψ ∧ χ ) ) ↔ ( χ ∧ ( ψ ∧ φ ) ) )
    res = lb.ref(
        "res",
        "( ( φ ∧ ( ψ ∧ χ ) ) ↔ ( χ ∧ ( ψ ∧ φ ) ) )",
        s1,
        s2,
        ref="bitr3i",
        note="bitr3i",
    )

    return lb.build(res)


def prove_an12s(sys: System) -> Proof:
    """an12s: ( ( ψ ∧ ( φ ∧ χ ) ) → θ ).

    Hyp: an12s.1 |- ( ( φ ∧ ( ψ ∧ χ ) ) → θ ).
    Concl: |- ( ( ψ ∧ ( φ ∧ χ ) ) → θ ).

    Inference associated with ~ an12 .  (Contributed by NM, 26-Apr-1994.)
    """
    lb = ProofBuilder(sys, "an12s")
    h1 = lb.hyp("an12s.1", "( ( φ ∧ ( ψ ∧ χ ) ) → θ )")

    # an12: ( ( φ ∧ ( ψ ∧ χ ) ) ↔ ( ψ ∧ ( φ ∧ χ ) ) )
    s1 = lb.ref(
        "s1",
        "( ( φ ∧ ( ψ ∧ χ ) ) ↔ ( ψ ∧ ( φ ∧ χ ) ) )",
        ref="an12",
        note="an12",
    )

    # sylbir: from ( ψ ↔ φ ) and ( ψ → χ ), derive ( φ → χ )
    res = lb.ref(
        "res",
        "( ( ψ ∧ ( φ ∧ χ ) ) → θ )",
        s1,
        h1,
        ref="sylbir",
        note="sylbir",
    )

    return lb.build(res)


def prove_pm4_63(sys: System) -> Proof:
    r"""pm4.63: ( -. ( ph -> -. ps ) <-> ( ph /\ ps ) ).

    Theorem *4.63 of [WhiteheadRussell] p. 120.
    """
    lb = ProofBuilder(sys, "pm4.63")
    dfan = lb.ref(
        "dfan",
        r"( ( ph /\ ps ) <-> -. ( ph -> -. ps ) )",
        ref="df-an",
        note="df-an",
    )
    res = lb.ref(
        "res",
        r"( -. ( ph -> -. ps ) <-> ( ph /\ ps ) )",
        dfan,
        ref="bicomi",
        note="bicomi",
    )
    return lb.build(res)


def prove_pm4_67(sys: System) -> Proof:
    r"""pm4.67: ( -. ( -. ph -> -. ps ) <-> ( -. ph /\ ps ) ).

    Theorem *4.67 of [WhiteheadRussell] p. 120.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "pm4.67")
    res = lb.ref(
        "res",
        r"( -. ( -. ph -> -. ps ) <-> ( -. ph /\ ps ) )",
        ref="pm4.63",
        note="pm4.63",
    )
    return lb.build(res)


def prove_pm4_82(sys: System) -> Proof:
    r"""pm4.82: ( ( ( ph -> ps ) /\ ( ph -> -. ps ) ) <-> -. ph ).

    Theorem *4.82 of [WhiteheadRussell] p. 122.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "pm4.82")
    s1 = lb.ref(
        "s1",
        r"( ( ph -> ps ) -> ( ( ph -> -. ps ) -> -. ph ) )",
        ref="pm2.65",
        note="pm2.65",
    )
    s2 = lb.ref(
        "s2",
        r"( ( ( ph -> ps ) /\ ( ph -> -. ps ) ) -> -. ph )",
        s1,
        ref="imp",
        note="imp",
    )
    s3 = lb.ref(
        "s3",
        r"( -. ph -> ( ph -> ps ) )",
        ref="pm2.21",
        note="pm2.21",
    )
    s4 = lb.ref(
        "s4",
        r"( -. ph -> ( ph -> -. ps ) )",
        ref="pm2.21",
        note="pm2.21",
    )
    s5 = lb.ref(
        "s5",
        r"( -. ph -> ( ( ph -> ps ) /\ ( ph -> -. ps ) ) )",
        s3,
        s4,
        ref="jca",
        note="jca",
    )
    res = lb.ref(
        "res",
        r"( ( ( ph -> ps ) /\ ( ph -> -. ps ) ) <-> -. ph )",
        s2,
        s5,
        ref="impbii",
        note="impbii",
    )
    return lb.build(res)


def prove_pm4_87(sys: System) -> Proof:
    """pm4.87: ( ( ( ( ( φ ∧ ψ ) → χ ) ↔ ( φ → ( ψ → χ ) ) ) ∧ ( ( φ → ( ψ → χ ) ) ↔ ( ψ → ( φ → χ ) ) ) ) ∧ ( ( ψ → ( φ → χ ) ) ↔ ( ( ψ ∧ φ ) → χ ) ) ).

    Theorem combining impexp, bi2.04, and pm3.2i into a single conjunctive form.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "pm4.87")

    # impexp: ( ( φ ∧ ψ ) → χ ) ↔ ( φ → ( ψ → χ ) )
    s1 = lb.ref(
        "s1",
        "( ( ( φ ∧ ψ ) → χ ) ↔ ( φ → ( ψ → χ ) ) )",
        ref="impexp",
        note="impexp",
    )

    # bi2.04: ( φ → ( ψ → χ ) ) ↔ ( ψ → ( φ → χ ) )
    s2 = lb.ref(
        "s2",
        "( ( φ → ( ψ → χ ) ) ↔ ( ψ → ( φ → χ ) ) )",
        ref="bi2.04",
        note="bi2.04",
    )

    # pm3.2i: conjoin s1 and s2
    s3 = lb.ref(
        "s3",
        "( ( ( ( φ ∧ ψ ) → χ ) ↔ ( φ → ( ψ → χ ) ) ) ∧ ( ( φ → ( ψ → χ ) ) ↔ ( ψ → ( φ → χ ) ) ) )",
        s1,
        s2,
        ref="pm3.2i",
        note="pm3.2i",
    )

    # impexp with ψ and φ swapped: ( ( ψ ∧ φ ) → χ ) ↔ ( ψ → ( φ → χ ) )
    s4 = lb.ref(
        "s4",
        "( ( ( ψ ∧ φ ) → χ ) ↔ ( ψ → ( φ → χ ) ) )",
        ref="impexp",
        note="impexp",
    )

    # bicomi: swap sides of s4
    s5 = lb.ref(
        "s5",
        "( ( ψ → ( φ → χ ) ) ↔ ( ( ψ ∧ φ ) → χ ) )",
        s4,
        ref="bicomi",
        note="bicomi",
    )

    # pm3.2i: conjoin s3 and s5 for the final result
    res = lb.ref(
        "res",
        "( ( ( ( ( φ ∧ ψ ) → χ ) ↔ ( φ → ( ψ → χ ) ) ) ∧ ( ( φ → ( ψ → χ ) ) ↔ ( ψ → ( φ → χ ) ) ) ) ∧ ( ( ψ → ( φ → χ ) ) ↔ ( ( ψ ∧ φ ) → χ ) ) )",
        s3,
        s5,
        ref="pm3.2i",
        note="pm3.2i",
    )

    return lb.build(res)


def prove_dfbi2(sys: System) -> Proof:
    r"""dfbi2: ( ( ph <-> ps ) <-> ( ( ph -> ps ) /\ ( ps -> ph ) ) ).

    Relate the biconditional connective to conjunction of implications.
    (Contributed by NM, 29-Dec-1992.)
    """
    lb = ProofBuilder(sys, "dfbi2")

    # dfbi1: ( ( ph <-> ps ) <-> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) )
    dfbi1_step = lb.ref(
        "dfbi1",
        r"( ( ph <-> ps ) <-> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) )",
        ref="dfbi1",
        note="dfbi1",
    )

    # df-an: ( ( ( ph -> ps ) /\ ( ps -> ph ) ) <-> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) )
    dfan_step = lb.ref(
        "df-an",
        r"( ( ( ph -> ps ) /\ ( ps -> ph ) ) <-> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) )",
        ref="df-an",
        note="df-an",
    )

    # bitr4i: ( ph <-> ch ) given ( ph <-> ps ) and ( ch <-> ps )
    res = lb.ref(
        "res",
        r"( ( ph <-> ps ) <-> ( ( ph -> ps ) /\ ( ps -> ph ) ) )",
        dfbi1_step,
        dfan_step,
        ref="bitr4i",
        note="bitr4i",
    )

    return lb.build(res)


def prove_dfbi(sys: System) -> Proof:
    r"""dfbi: ( ( ( ph <-> ps ) -> ( ( ph -> ps ) /\ ( ps -> ph ) ) )
    /\ ( ( ( ph -> ps ) /\ ( ps -> ph ) ) -> ( ph <-> ps ) ) ).

        Definition ~ df-bi rewritten in an abbreviated form to help intuitive
        understanding of that definition.  Note that it is a conjunction of two
        implications; one which asserts properties that follow from the
        biconditional and one which asserts properties that imply the
        biconditional.
        (Contributed by NM, 15-Aug-2008.)
    """
    lb = ProofBuilder(sys, "dfbi")

    # dfbi2: ( ( ph <-> ps ) <-> ( ( ph -> ps ) /\ ( ps -> ph ) ) )
    dfbi2_step = lb.ref(
        "dfbi2",
        r"( ( ph <-> ps ) <-> ( ( ph -> ps ) /\ ( ps -> ph ) ) )",
        ref="dfbi2",
        note="dfbi2",
    )

    # Apply dfbi2 again with substitution:
    #   ph' = ( ph <-> ps ),  ps' = ( ( ph -> ps ) /\ ( ps -> ph ) )
    # giving the major premise for mpbi.
    dfbi2_subst = lb.ref(
        "dfbi2_subst",
        r"( ( ( ph <-> ps ) <-> ( ( ph -> ps ) /\ ( ps -> ph ) ) ) <-> "
        r"( ( ( ph <-> ps ) -> ( ( ph -> ps ) /\ ( ps -> ph ) ) ) /\ "
        r"( ( ( ph -> ps ) /\ ( ps -> ph ) ) -> ( ph <-> ps ) ) ) )",
        ref="dfbi2",
        note="dfbi2 (subst)",
    )

    # mpbi: mpbi.min = dfbi2_step, mpbi.maj = dfbi2_subst
    res = lb.ref(
        "res",
        r"( ( ( ph <-> ps ) -> ( ( ph -> ps ) /\ ( ps -> ph ) ) ) /\ "
        r"( ( ( ph -> ps ) /\ ( ps -> ph ) ) -> ( ph <-> ps ) ) )",
        dfbi2_step,
        dfbi2_subst,
        ref="mpbi",
        note="mpbi",
    )

    return lb.build(res)


def prove_impancom(sys: System) -> Proof:
    r"""impancom: ( ( ph /\ ch ) -> ( ps -> th ) ).

    Hyp: impancom.1 |- ( ( ph /\ ps ) -> ( ch -> th ) ).
    Concl: |- ( ( ph /\ ch ) -> ( ps -> th ) ).

    Swap and-combined antecedents in an implication.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "impancom")
    h1 = lb.hyp("impancom.1", "( ( ph /\\ ps ) -> ( ch -> th ) )")
    # ex: shift ( ph /\ ps ) from antecedent to ( ph -> ( ps -> ... ) )
    s1 = lb.ref(
        "s1",
        "( ph -> ( ps -> ( ch -> th ) ) )",
        h1,
        ref="ex",
        note="ex impancom.1",
    )
    # com23: swap ps and ch in the consequent chain
    s2 = lb.ref(
        "s2",
        "( ph -> ( ch -> ( ps -> th ) ) )",
        s1,
        ref="com23",
        note="com23 s1",
    )
    # imp: import ph /\ ch back into the antecedent
    res = lb.ref(
        "res",
        "( ( ph /\\ ch ) -> ( ps -> th ) )",
        s2,
        ref="imp",
        note="imp s2",
    )
    return lb.build(res)


def prove_anasss(sys: System) -> Proof:
    r"""anasss: ( ( ph /\ ( ps /\ ch ) ) -> th ).

    Hyp: anasss.1 |- ( ( ( ph /\ ps ) /\ ch ) -> th ).
    Concl: |- ( ( ph /\ ( ps /\ ch ) ) -> th ).

    An inference that converts an exportation to an importation with
    a nested conjunction in the antecedent.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "anasss")
    h1 = lb.hyp("anasss.1", "( ( ( ph /\\ ps ) /\\ ch ) -> th )")
    s1 = lb.ref(
        "s1",
        "( ph -> ( ps -> ( ch -> th ) ) )",
        h1,
        ref="exp31",
        note="exp31",
    )
    res = lb.ref(
        "res",
        "( ( ph /\\ ( ps /\\ ch ) ) -> th )",
        s1,
        ref="imp32",
        note="imp32",
    )
    return lb.build(res)


def prove_anass(sys: System) -> Proof:
    r"""anass: ( ( ( ph /\ ps ) /\ ch ) <-> ( ph /\ ( ps /\ ch ) ) ).

    Associative law for conjunction.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "anass")

    # id: ( ( ( ph /\ ps ) /\ ch ) -> ( ( ph /\ ps ) /\ ch ) )
    id1 = lb.ref(
        "id1",
        r"( ( ( ph /\ ps ) /\ ch ) -> ( ( ph /\ ps ) /\ ch ) )",
        ref="id",
        note="id",
    )

    # anasss with id1: ( ( ph /\ ( ps /\ ch ) ) -> ( ( ph /\ ps ) /\ ch ) )
    rev = lb.ref(
        "rev",
        r"( ( ph /\ ( ps /\ ch ) ) -> ( ( ph /\ ps ) /\ ch ) )",
        id1,
        ref="anasss",
        note="anasss",
    )

    # id: ( ( ph /\ ( ps /\ ch ) ) -> ( ph /\ ( ps /\ ch ) ) )
    id2 = lb.ref(
        "id2",
        r"( ( ph /\ ( ps /\ ch ) ) -> ( ph /\ ( ps /\ ch ) ) )",
        ref="id",
        note="id",
    )

    # anassrs with id2: ( ( ( ph /\ ps ) /\ ch ) -> ( ph /\ ( ps /\ ch ) ) )
    fwd = lb.ref(
        "fwd",
        r"( ( ( ph /\ ps ) /\ ch ) -> ( ph /\ ( ps /\ ch ) ) )",
        id2,
        ref="anassrs",
        note="anassrs",
    )

    # impbii: ( ( ( ph /\ ps ) /\ ch ) <-> ( ph /\ ( ps /\ ch ) ) )
    res = lb.ref(
        "res",
        r"( ( ( ph /\ ps ) /\ ch ) <-> ( ph /\ ( ps /\ ch ) ) )",
        fwd,
        rev,
        ref="impbii",
        note="impbii",
    )

    return lb.build(res)


def prove_anbi12i(sys: System) -> Proof:
    """anbi12i: ( φ ∧ χ ) ↔ ( ψ ∧ θ ).

    Inference conjoining two biconditionals: from φ ↔ ψ and χ ↔ θ,
    deduce ( φ ∧ χ ) ↔ ( ψ ∧ θ ).
    (Contributed by NM, 25-Dec-1993.)
    """
    lb = ProofBuilder(sys, "anbi12i")
    h1 = lb.hyp("anbi12.1", "φ ↔ ψ")
    h2 = lb.hyp("anbi12.2", "χ ↔ θ")
    s1 = lb.ref("s1", "( φ ∧ χ ) ↔ ( φ ∧ θ )", h2, ref="anbi2i", note="anbi2i")
    res = lb.ref("res", "( φ ∧ χ ) ↔ ( ψ ∧ θ )", s1, h1, ref="bianbi", note="bianbi")
    return lb.build(res)


def prove_3anbi123i(sys: System) -> Proof:
    """3anbi123i: ( φ ∧ χ ∧ τ ) ↔ ( ψ ∧ θ ∧ η ).

    Inference joining three biconditionals into a triple conjunction:
    from φ ↔ ψ, χ ↔ θ, and τ ↔ η,
    deduce ( φ ∧ χ ∧ τ ) ↔ ( ψ ∧ θ ∧ η ).
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3anbi123i")
    h1 = lb.hyp("bi3.1", "φ ↔ ψ")
    h2 = lb.hyp("bi3.2", "χ ↔ θ")
    h3 = lb.hyp("bi3.3", "τ ↔ η")
    # anbi12i: ( φ ∧ χ ) ↔ ( ψ ∧ θ )
    s1 = lb.ref("s1", "( φ ∧ χ ) ↔ ( ψ ∧ θ )", h1, h2, ref="anbi12i", note="anbi12i")
    # anbi12i: ( ( φ ∧ χ ) ∧ τ ) ↔ ( ( ψ ∧ θ ) ∧ η )
    s2 = lb.ref(
        "s2", "( ( φ ∧ χ ) ∧ τ ) ↔ ( ( ψ ∧ θ ) ∧ η )", s1, h3, ref="anbi12i", note="anbi12i"
    )
    # df-3an: ( φ ∧ χ ∧ τ ) ↔ ( ( φ ∧ χ ) ∧ τ )
    s3 = lb.ref("s3", "( φ ∧ χ ∧ τ ) ↔ ( ( φ ∧ χ ) ∧ τ )", ref="df-3an", note="df-3an")
    # df-3an: ( ψ ∧ θ ∧ η ) ↔ ( ( ψ ∧ θ ) ∧ η )
    s4 = lb.ref("s4", "( ψ ∧ θ ∧ η ) ↔ ( ( ψ ∧ θ ) ∧ η )", ref="df-3an", note="df-3an")
    # 3bitr4i: chain s2, s3, s4 → ( φ ∧ χ ∧ τ ) ↔ ( ψ ∧ θ ∧ η )
    res = lb.ref("res", "( φ ∧ χ ∧ τ ) ↔ ( ψ ∧ θ ∧ η )", s2, s3, s4, ref="3bitr4i", note="3bitr4i")
    return lb.build(res)


def prove_3anbi1i(sys: System) -> Proof:
    """3anbi1i: ( φ ∧ χ ∧ θ ) ↔ ( ψ ∧ χ ∧ θ ).

    Inference adding two conjuncts to a biconditional.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "3anbi1i")
    h1 = lb.hyp("3anbi1i.1", "φ ↔ ψ")
    s1 = lb.ref("s1", "χ ↔ χ", ref="biid", note="biid")
    s2 = lb.ref("s2", "θ ↔ θ", ref="biid", note="biid")
    res = lb.ref(
        "res", "( φ ∧ χ ∧ θ ) ↔ ( ψ ∧ χ ∧ θ )", h1, s1, s2, ref="3anbi123i", note="3anbi123i"
    )
    return lb.build(res)


def prove_3anbi2i(sys: System) -> Proof:
    """3anbi2i: ( χ ∧ φ ∧ θ ) ↔ ( χ ∧ ψ ∧ θ ).

    Inference adding two conjuncts to a biconditional.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "3anbi2i")
    h1 = lb.hyp("3anbi2i.1", "φ ↔ ψ")
    s1 = lb.ref("s1", "χ ↔ χ", ref="biid", note="biid")
    s2 = lb.ref("s2", "θ ↔ θ", ref="biid", note="biid")
    res = lb.ref(
        "res",
        "( χ ∧ φ ∧ θ ) ↔ ( χ ∧ ψ ∧ θ )",
        s1,
        h1,
        s2,
        ref="3anbi123i",
        note="3anbi123i",
    )
    return lb.build(res)


def prove_3anbi3i(sys: System) -> Proof:
    """3anbi3i: ( χ ∧ θ ∧ φ ) ↔ ( χ ∧ θ ∧ ψ ).

    Inference adding two conjuncts to a biconditional.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "3anbi3i")
    h1 = lb.hyp("3anbi3i.1", "φ ↔ ψ")
    s1 = lb.ref("s1", "χ ↔ χ", ref="biid", note="biid")
    s2 = lb.ref("s2", "θ ↔ θ", ref="biid", note="biid")
    res = lb.ref(
        "res",
        "( χ ∧ θ ∧ φ ) ↔ ( χ ∧ θ ∧ ψ )",
        s1,
        s2,
        h1,
        ref="3anbi123i",
        note="3anbi123i",
    )
    return lb.build(res)


def prove_3anbi123d(sys: System) -> Proof:
    """3anbi123d: φ → ( ( ψ ∧ θ ∧ η ) ↔ ( χ ∧ τ ∧ ζ ) ).

    Deduction joining three biconditionals into a triple-conjunction
    equivalence.  (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3anbi123d")
    h1 = lb.hyp("bi3d.1", "φ → ( ψ ↔ χ )")
    h2 = lb.hyp("bi3d.2", "φ → ( θ ↔ τ )")
    h3 = lb.hyp("bi3d.3", "φ → ( η ↔ ζ )")

    # anbi12d: φ → ( ( ψ ∧ θ ) ↔ ( χ ∧ τ ) )
    s1 = lb.ref(
        "s1",
        "φ → ( ( ψ ∧ θ ) ↔ ( χ ∧ τ ) )",
        h1,
        h2,
        ref="anbi12d",
        note="anbi12d",
    )

    # anbi12d: φ → ( ( ( ψ ∧ θ ) ∧ η ) ↔ ( ( χ ∧ τ ) ∧ ζ ) )
    s2 = lb.ref(
        "s2",
        "φ → ( ( ( ψ ∧ θ ) ∧ η ) ↔ ( ( χ ∧ τ ) ∧ ζ ) )",
        s1,
        h3,
        ref="anbi12d",
        note="anbi12d",
    )

    # df-3an: ( ψ ∧ θ ∧ η ) ↔ ( ( ψ ∧ θ ) ∧ η )
    s3 = lb.ref(
        "s3",
        "( ψ ∧ θ ∧ η ) ↔ ( ( ψ ∧ θ ) ∧ η )",
        ref="df-3an",
        note="df-3an",
    )

    # df-3an: ( χ ∧ τ ∧ ζ ) ↔ ( ( χ ∧ τ ) ∧ ζ )
    s4 = lb.ref(
        "s4",
        "( χ ∧ τ ∧ ζ ) ↔ ( ( χ ∧ τ ) ∧ ζ )",
        ref="df-3an",
        note="df-3an",
    )

    # 3bitr4g chains s2, s3, s4
    res = lb.ref(
        "res",
        "φ → ( ( ψ ∧ θ ∧ η ) ↔ ( χ ∧ τ ∧ ζ ) )",
        s2,
        s3,
        s4,
        ref="3bitr4g",
        note="3bitr4g",
    )

    return lb.build(res)


def prove_3anbi23d(sys: System) -> Proof:
    """3anbi23d: φ → ( ( η ∧ ψ ∧ θ ) ↔ ( η ∧ χ ∧ τ ) ).

    Deduction joining two biconditionals into a triple-conjunction
    equivalence, with the first conjunct unchanged.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3anbi23d")
    h1 = lb.hyp("h1", "φ → ( ψ ↔ χ )")
    h2 = lb.hyp("h2", "φ → ( θ ↔ τ )")

    # biidd: φ → ( η ↔ η )
    s1 = lb.ref("s1", "φ → ( η ↔ η )", ref="biidd", note="biidd")

    # 3anbi123d: φ → ( ( η ∧ ψ ∧ θ ) ↔ ( η ∧ χ ∧ τ ) )
    res = lb.ref(
        "res",
        "φ → ( ( η ∧ ψ ∧ θ ) ↔ ( η ∧ χ ∧ τ ) )",
        s1,
        h1,
        h2,
        ref="3anbi123d",
        note="3anbi123d",
    )
    return lb.build(res)


def prove_3anbi12d(sys: System) -> Proof:
    """3anbi12d: φ → ( ( ψ ∧ θ ∧ η ) ↔ ( χ ∧ τ ∧ η ) ).

    Deduction joining two biconditionals into a triple-conjunction
    equivalence, with the third conjunct unchanged.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3anbi12d")
    h1 = lb.hyp("h1", "φ → ( ψ ↔ χ )")
    h2 = lb.hyp("h2", "φ → ( θ ↔ τ )")

    # biidd: φ → ( η ↔ η )
    s1 = lb.ref("s1", "φ → ( η ↔ η )", ref="biidd", note="biidd")

    # 3anbi123d: φ → ( ( ψ ∧ θ ∧ η ) ↔ ( χ ∧ τ ∧ η ) )
    res = lb.ref(
        "res",
        "φ → ( ( ψ ∧ θ ∧ η ) ↔ ( χ ∧ τ ∧ η ) )",
        h1,
        h2,
        s1,
        ref="3anbi123d",
        note="3anbi123d",
    )

    return lb.build(res)


def prove_3anbi13d(sys: System) -> Proof:
    """3anbi13d: φ → ( ( ψ ∧ η ∧ θ ) ↔ ( χ ∧ η ∧ τ ) ).

    Deduction joining two biconditionals into a triple-conjunction
    equivalence, with the second conjunct unchanged.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3anbi13d")
    h1 = lb.hyp("h1", "φ → ( ψ ↔ χ )")
    h2 = lb.hyp("h2", "φ → ( θ ↔ τ )")

    # biidd: φ → ( η ↔ η )
    s1 = lb.ref("s1", "φ → ( η ↔ η )", ref="biidd", note="biidd")

    # 3anbi123d: φ → ( ( ψ ∧ η ∧ θ ) ↔ ( χ ∧ η ∧ τ ) )
    res = lb.ref(
        "res",
        "φ → ( ( ψ ∧ η ∧ θ ) ↔ ( χ ∧ η ∧ τ ) )",
        h1,
        s1,
        h2,
        ref="3anbi123d",
        note="3anbi123d",
    )

    return lb.build(res)


def prove_3anbi1d(sys: System) -> Proof:
    """3anbi1d: φ → ( ( ψ ∧ θ ∧ τ ) ↔ ( χ ∧ θ ∧ τ ) ).

    Deduction joining a biconditional into a triple-conjunction
    equivalence, with the second and third conjuncts unchanged.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3anbi1d")
    h1 = lb.hyp("h1", "φ → ( ψ ↔ χ )")

    # biidd: φ → ( θ ↔ θ )
    s1 = lb.ref("s1", "φ → ( θ ↔ θ )", ref="biidd", note="biidd")

    # 3anbi12d: φ → ( ( ψ ∧ θ ∧ τ ) ↔ ( χ ∧ θ ∧ τ ) )
    res = lb.ref(
        "res",
        "φ → ( ( ψ ∧ θ ∧ τ ) ↔ ( χ ∧ θ ∧ τ ) )",
        h1,
        s1,
        ref="3anbi12d",
        note="3anbi12d",
    )

    return lb.build(res)


def prove_3anbi2d(sys: System) -> Proof:
    """3anbi2d: φ → ( ( θ ∧ ψ ∧ τ ) ↔ ( θ ∧ χ ∧ τ ) ).

    Deduction joining a biconditional into a triple-conjunction
    equivalence, with the first and third conjuncts unchanged.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3anbi2d")
    h1 = lb.hyp("h1", "φ → ( ψ ↔ χ )")

    # biidd: φ → ( θ ↔ θ )
    s1 = lb.ref("s1", "φ → ( θ ↔ θ )", ref="biidd", note="biidd")

    # 3anbi12d: φ → ( ( θ ∧ ψ ∧ τ ) ↔ ( θ ∧ χ ∧ τ ) )
    res = lb.ref(
        "res",
        "φ → ( ( θ ∧ ψ ∧ τ ) ↔ ( θ ∧ χ ∧ τ ) )",
        s1,
        h1,
        ref="3anbi12d",
        note="3anbi12d",
    )

    return lb.build(res)


def prove_3anbi3d(sys: System) -> Proof:
    """3anbi3d: φ → ( ( θ ∧ τ ∧ ψ ) ↔ ( θ ∧ τ ∧ χ ) ).

    Deduction adding two conjuncts to a biconditional on the third conjunct.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3anbi3d")
    h1 = lb.hyp("h1", "φ → ( ψ ↔ χ )")

    # biidd: φ → ( θ ↔ θ )
    s1 = lb.ref("s1", "φ → ( θ ↔ θ )", ref="biidd", note="biidd")

    # 3anbi13d: φ → ( ( θ ∧ τ ∧ ψ ) ↔ ( θ ∧ τ ∧ χ ) )
    res = lb.ref(
        "res",
        "φ → ( ( θ ∧ τ ∧ ψ ) ↔ ( θ ∧ τ ∧ χ ) )",
        s1,
        h1,
        ref="3anbi13d",
        note="3anbi13d",
    )

    return lb.build(res)


def prove_syl3anb(sys: System) -> Proof:
    """syl3anb: ( φ ∧ χ ∧ τ ) → ζ.

    Syllogism inference with biconditional replacement of three antecedents:
    from φ ↔ ψ, χ ↔ θ, τ ↔ η, and ( ψ ∧ θ ∧ η ) → ζ,
    derive ( φ ∧ χ ∧ τ ) → ζ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "syl3anb")
    h1 = lb.hyp("syl3anb.1", "φ ↔ ψ")
    h2 = lb.hyp("syl3anb.2", "χ ↔ θ")
    h3 = lb.hyp("syl3anb.3", "τ ↔ η")
    h4 = lb.hyp("syl3anb.4", "( ψ ∧ θ ∧ η ) → ζ")
    s1 = lb.ref(
        "s1",
        "( φ ∧ χ ∧ τ ) ↔ ( ψ ∧ θ ∧ η )",
        h1,
        h2,
        h3,
        ref="3anbi123i",
        note="3anbi123i",
    )
    res = lb.ref("res", "( φ ∧ χ ∧ τ ) → ζ", s1, h4, ref="sylbi", note="sylbi")
    return lb.build(res)


def prove_syl3anbr(sys: System) -> Proof:
    """syl3anbr: ( φ ∧ χ ∧ τ ) → ζ.

    Syllogism inference with biconditional replacement of three antecedents
    (reversed biconditional form): from ψ ↔ φ, θ ↔ χ, η ↔ τ, and
    ( ψ ∧ θ ∧ η ) → ζ, derive ( φ ∧ χ ∧ τ ) → ζ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "syl3anbr")
    h1 = lb.hyp("syl3anbr.1", "ψ ↔ φ")
    h2 = lb.hyp("syl3anbr.2", "θ ↔ χ")
    h3 = lb.hyp("syl3anbr.3", "η ↔ τ")
    h4 = lb.hyp("syl3anbr.4", "( ψ ∧ θ ∧ η ) → ζ")
    s1 = lb.ref("s1", "φ ↔ ψ", h1, ref="bicomi", note="bicomi")
    s2 = lb.ref("s2", "χ ↔ θ", h2, ref="bicomi", note="bicomi")
    s3 = lb.ref("s3", "τ ↔ η", h3, ref="bicomi", note="bicomi")
    res = lb.ref(
        "res",
        "( φ ∧ χ ∧ τ ) → ζ",
        s1,
        s2,
        s3,
        h4,
        ref="syl3anb",
        note="syl3anb",
    )
    return lb.build(res)


def prove_anbi1i(sys: System) -> Proof:
    """anbi1i: ( φ ∧ χ ) ↔ ( ψ ∧ χ ).

    Inference adding a conjunct to the right of a biconditional.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "anbi1i")
    h1 = lb.hyp("anbi1i.1", "φ ↔ ψ")
    s1 = lb.ref("s1", "χ → ( φ ↔ ψ )", h1, ref="a1i", note="a1i")
    res = lb.ref("res", "( φ ∧ χ ) ↔ ( ψ ∧ χ )", s1, ref="pm5.32ri", note="pm5.32ri")
    return lb.build(res)


def prove_anbi1d(sys: System) -> Proof:
    """anbi1d: φ → ( ( ψ ∧ θ ) ↔ ( χ ∧ θ ) ).

    Deduction adding a conjunct to the right of a biconditional.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "anbi1d")
    h1 = lb.hyp("anbi1d.1", "φ → ( ψ ↔ χ )")

    # a1d: φ → ( ψ ↔ χ )  ⇒  φ → ( θ → ( ψ ↔ χ ) )
    s1 = lb.ref(
        "s1",
        "φ → ( θ → ( ψ ↔ χ ) )",
        h1,
        ref="a1d",
        note="a1d",
    )

    # pm5.32rd: distribute the conjunct over the biconditional
    res = lb.ref(
        "res",
        "φ → ( ( ψ ∧ θ ) ↔ ( χ ∧ θ ) )",
        s1,
        ref="pm5.32rd",
        note="pm5.32rd",
    )

    return lb.build(res)


def prove_anbi1(sys: System) -> Proof:
    """anbi1: ( φ ↔ ψ ) → ( ( φ ∧ χ ) ↔ ( ψ ∧ χ ) ).

    Deduction adding a right conjunct to both sides of a biconditional,
    in closed form.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "anbi1")
    s_id = lb.ref(
        "s_id",
        "( φ ↔ ψ ) → ( φ ↔ ψ )",
        ref="id",
        note="id",
    )
    res = lb.ref(
        "res",
        "( φ ↔ ψ ) → ( ( φ ∧ χ ) ↔ ( ψ ∧ χ ) )",
        s_id,
        ref="anbi1d",
        note="anbi1d",
    )
    return lb.build(res)


def prove_anbi2i(sys: System) -> Proof:
    """anbi2i: ( χ ∧ φ ) ↔ ( χ ∧ ψ ).

    Inference adding a conjunct to the left of a biconditional.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "anbi2i")
    h1 = lb.hyp("anbi2i.1", "φ ↔ ψ")
    s1 = lb.ref("s1", "χ → ( φ ↔ ψ )", h1, ref="a1i", note="a1i")
    res = lb.ref("res", "( χ ∧ φ ) ↔ ( χ ∧ ψ )", s1, ref="pm5.32i", note="pm5.32i")
    return lb.build(res)


def prove_anbi1ci(sys: System) -> Proof:
    """anbi1ci: ( χ ∧ φ ) ↔ ( ψ ∧ χ ).

    Inference adding a conjunct to the left and commuting conjuncts
    in a biconditional.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "anbi1ci")
    h1 = lb.hyp("anbi1ci.1", "φ ↔ ψ")
    s1 = lb.ref("s1", "( χ ∧ φ ) ↔ ( χ ∧ ψ )", h1, ref="anbi2i", note="anbi2i")
    res = lb.ref("res", "( χ ∧ φ ) ↔ ( ψ ∧ χ )", s1, ref="biancomi", note="biancomi")
    return lb.build(res)


def prove_anbiim(sys: System) -> Proof:
    r"""anbiim: ( ( ph /\ ps ) -> ( ch <-> th ) ).

    Adding biconditional when antecedents are conjuncted.

    (Contributed by metakunt, 16-Apr-2024.)
    (Proof shortened by Wolf Lammen, 7-May-2025.)
    (Proof shortened by Garrett Katz, 15-Jun-2026.)
    """
    lb = ProofBuilder(sys, "anbiim")

    h1 = lb.hyp("anbiim.1", "( ph -> ( ch -> th ) )")
    h2 = lb.hyp("anbiim.2", "( ps -> ( th -> ch ) )")

    s_impbid21d = lb.ref(
        "s_impbid21d",
        "( ps -> ( ph -> ( ch <-> th ) ) )",
        h1,
        h2,
        ref="impbid21d",
        note="impbid21d",
    )

    res = lb.ref(
        "res",
        "( ( ph /\\ ps ) -> ( ch <-> th ) )",
        s_impbid21d,
        ref="impcom",
        note="impcom",
    )

    return lb.build(res)


def prove_anbiimOLD(sys: System) -> Proof:
    """anbiimOLD: ( ( φ ∧ ψ ) → ( χ ↔ θ ) ).

    Adding biconditional when antecedents are conjuncted.
    (Contributed by NM, 5-Aug-1993.)
    (Proof modification is discouraged.)  (New usage is discouraged.)
    """
    lb = ProofBuilder(sys, "anbiimOLD")

    h1 = lb.hyp("anbiim.1", "( φ → ( χ → θ ) )")
    h2 = lb.hyp("anbiim.2", "( ψ → ( θ → χ ) )")

    s1 = lb.ref(
        "s1",
        "( ( φ ∧ ψ ) → ( χ → θ ) )",
        h1,
        ref="adantr",
        note="adantr anbiim.1",
    )

    s2 = lb.ref(
        "s2",
        "( ( φ ∧ ψ ) → ( θ → χ ) )",
        h2,
        ref="adantl",
        note="adantl anbiim.2",
    )

    res = lb.ref(
        "res",
        "( ( φ ∧ ψ ) → ( χ ↔ θ ) )",
        s1,
        s2,
        ref="impbid",
        note="impbid",
    )
    return lb.build(res)


def prove_3anass(sys: System) -> Proof:
    r"""3anass: ( ( ph /\ ps /\ ch ) <-> ( ph /\ ( ps /\ ch ) ) ).

    Association of three conjunctions.  ( ph /\ ps /\ ch ) is equivalent to
    ( ph /\ ( ps /\ ch ) ).
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3anass")

    # df-3an: ( ph /\ ps /\ ch ) <-> ( ( ph /\ ps ) /\ ch )
    df3an = lb.ref(
        "df3an",
        "( ph /\\ ps /\\ ch ) <-> ( ( ph /\\ ps ) /\\ ch )",
        ref="df-3an",
        note="df-3an",
    )

    # anass: ( ( ph /\ ps ) /\ ch ) <-> ( ph /\ ( ps /\ ch ) )
    anass_step = lb.ref(
        "anass_step",
        "( ( ph /\\ ps ) /\\ ch ) <-> ( ph /\\ ( ps /\\ ch ) )",
        ref="anass",
        note="anass",
    )

    # bitri: chain df-3an and anass
    res = lb.ref(
        "res",
        "( ph /\\ ps /\\ ch ) <-> ( ph /\\ ( ps /\\ ch ) )",
        df3an,
        anass_step,
        ref="bitri",
        note="bitri",
    )

    return lb.build(res)


def prove_3anan12(sys: System) -> Proof:
    """3anan12: ( φ ∧ ψ ∧ χ ) ↔ ( ψ ∧ ( φ ∧ χ ) ).

    Swap the first two conjuncts in a triple conjunction.
    """
    lb = ProofBuilder(sys, "3anan12")

    # 3anass: ( φ ∧ ψ ∧ χ ) ↔ ( φ ∧ ( ψ ∧ χ ) )
    s_3anass = lb.ref(
        "s_3anass",
        "( φ ∧ ψ ∧ χ ) ↔ ( φ ∧ ( ψ ∧ χ ) )",
        ref="3anass",
        note="3anass",
    )

    # an12: ( φ ∧ ( ψ ∧ χ ) ) ↔ ( ψ ∧ ( φ ∧ χ ) )
    s_an12 = lb.ref(
        "s_an12",
        "( φ ∧ ( ψ ∧ χ ) ) ↔ ( ψ ∧ ( φ ∧ χ ) )",
        ref="an12",
        note="an12",
    )

    # bitri: chain s_3anass and s_an12
    res = lb.ref(
        "res",
        "( φ ∧ ψ ∧ χ ) ↔ ( ψ ∧ ( φ ∧ χ ) )",
        s_3anass,
        s_an12,
        ref="bitri",
        note="bitri",
    )

    return lb.build(res)


def prove_3anan32(sys: System) -> Proof:
    """3anan32: ( φ ∧ ψ ∧ χ ) ↔ ( ( φ ∧ χ ) ∧ ψ ).

    Swap the last two conjuncts in a triple conjunction.
    """
    lb = ProofBuilder(sys, "3anan32")

    # 3anan12: ( φ ∧ ψ ∧ χ ) ↔ ( ψ ∧ ( φ ∧ χ ) )
    s_3anan12 = lb.ref(
        "s_3anan12",
        "( φ ∧ ψ ∧ χ ) ↔ ( ψ ∧ ( φ ∧ χ ) )",
        ref="3anan12",
        note="3anan12",
    )

    # biancomi: from ( φ ∧ ψ ∧ χ ) ↔ ( ψ ∧ ( φ ∧ χ ) )
    #           to   ( φ ∧ ψ ∧ χ ) ↔ ( ( φ ∧ χ ) ∧ ψ )
    res = lb.ref(
        "res",
        "( φ ∧ ψ ∧ χ ) ↔ ( ( φ ∧ χ ) ∧ ψ )",
        s_3anan12,
        ref="biancomi",
        note="biancomi",
    )

    return lb.build(res)


def prove_3anan32OLD(sys: System) -> Proof:
    """3anan32OLD: ( φ ∧ ψ ∧ χ ) ↔ ( ( φ ∧ χ ) ∧ ψ ).

    Swap the last two conjuncts in a triple conjunction.
    (Contributed by NM, 3-Jan-1993.) (Proof modification is discouraged.)
    (New usage is discouraged.)
    """
    lb = ProofBuilder(sys, "3anan32OLD")

    # df-3an: ( φ ∧ ψ ∧ χ ) ↔ ( ( φ ∧ ψ ) ∧ χ )
    s1 = lb.ref(
        "s1",
        "( φ ∧ ψ ∧ χ ) ↔ ( ( φ ∧ ψ ) ∧ χ )",
        ref="df-3an",
        note="df-3an",
    )

    # an32: ( ( φ ∧ ψ ) ∧ χ ) ↔ ( ( φ ∧ χ ) ∧ ψ )
    s2 = lb.ref(
        "s2",
        "( ( φ ∧ ψ ) ∧ χ ) ↔ ( ( φ ∧ χ ) ∧ ψ )",
        ref="an32",
        note="an32",
    )

    # bitri: chain df-3an and an32
    res = lb.ref(
        "res",
        "( φ ∧ ψ ∧ χ ) ↔ ( ( φ ∧ χ ) ∧ ψ )",
        s1,
        s2,
        ref="bitri",
        note="bitri",
    )

    return lb.build(res)


def prove_3ancomb(sys: System) -> Proof:
    """3ancomb: ( φ ∧ ψ ∧ χ ) ↔ ( φ ∧ χ ∧ ψ ).

    Swap the last two conjuncts in a triple conjunction.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "3ancomb")

    # 3anan32: ( φ ∧ ψ ∧ χ ) ↔ ( ( φ ∧ χ ) ∧ ψ )
    s1 = lb.ref(
        "s1",
        "( φ ∧ ψ ∧ χ ) ↔ ( ( φ ∧ χ ) ∧ ψ )",
        ref="3anan32",
        note="3anan32",
    )

    # df-3an: ( φ ∧ χ ∧ ψ ) ↔ ( ( φ ∧ χ ) ∧ ψ )
    s2 = lb.ref(
        "s2",
        "( φ ∧ χ ∧ ψ ) ↔ ( ( φ ∧ χ ) ∧ ψ )",
        ref="df-3an",
        note="df-3an",
    )

    # bitr4i: ( φ ∧ ψ ∧ χ ) ↔ ( φ ∧ χ ∧ ψ )
    res = lb.ref(
        "res",
        "( φ ∧ ψ ∧ χ ) ↔ ( φ ∧ χ ∧ ψ )",
        s1,
        s2,
        ref="bitr4i",
        note="bitr4i",
    )

    return lb.build(res)


def prove_3ancoma(sys: System) -> Proof:
    """3ancoma: ( φ ∧ ψ ∧ χ ) ↔ ( ψ ∧ φ ∧ χ ).

    Swap the first two conjuncts in a triple conjunction.
    """
    lb = ProofBuilder(sys, "3ancoma")

    # 3anan12: ( φ ∧ ψ ∧ χ ) ↔ ( ψ ∧ ( φ ∧ χ ) )
    s1 = lb.ref(
        "s1",
        "( φ ∧ ψ ∧ χ ) ↔ ( ψ ∧ ( φ ∧ χ ) )",
        ref="3anan12",
        note="3anan12",
    )

    # 3anass: ( ψ ∧ φ ∧ χ ) ↔ ( ψ ∧ ( φ ∧ χ ) )
    s2 = lb.ref(
        "s2",
        "( ψ ∧ φ ∧ χ ) ↔ ( ψ ∧ ( φ ∧ χ ) )",
        ref="3anass",
        note="3anass",
    )

    # bitr4i: ( φ ∧ ψ ∧ χ ) ↔ ( ψ ∧ φ ∧ χ )
    res = lb.ref(
        "res",
        "( φ ∧ ψ ∧ χ ) ↔ ( ψ ∧ φ ∧ χ )",
        s1,
        s2,
        ref="bitr4i",
        note="bitr4i",
    )

    return lb.build(res)


def prove_3an4anass(sys: System) -> Proof:
    """3an4anass: ( ( φ ∧ ψ ∧ χ ) ∧ θ ) ↔ ( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ).

    Associativity of four conjuncts — a ternary conjunction with a fourth
    conjunct is equivalent to the pairwise conjunction of its components.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3an4anass")

    # df-3an: ( φ ∧ ψ ∧ χ ) ↔ ( ( φ ∧ ψ ) ∧ χ )
    df3an = lb.ref(
        "df3an",
        "( φ ∧ ψ ∧ χ ) ↔ ( ( φ ∧ ψ ) ∧ χ )",
        ref="df-3an",
        note="df-3an",
    )

    # anbi1i: ( ( φ ∧ ψ ∧ χ ) ∧ θ ) ↔ ( ( ( φ ∧ ψ ) ∧ χ ) ∧ θ )
    s1 = lb.ref(
        "s1",
        "( ( φ ∧ ψ ∧ χ ) ∧ θ ) ↔ ( ( ( φ ∧ ψ ) ∧ χ ) ∧ θ )",
        df3an,
        ref="anbi1i",
        note="anbi1i",
    )

    # anass: ( ( ( φ ∧ ψ ) ∧ χ ) ∧ θ ) ↔ ( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) )
    s2 = lb.ref(
        "s2",
        "( ( ( φ ∧ ψ ) ∧ χ ) ∧ θ ) ↔ ( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) )",
        ref="anass",
        note="anass",
    )

    # bitri: chain s1 and s2
    res = lb.ref(
        "res",
        "( ( φ ∧ ψ ∧ χ ) ∧ θ ) ↔ ( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) )",
        s1,
        s2,
        ref="bitri",
        note="bitri",
    )

    return lb.build(res)


def prove_expr(sys: System) -> Proof:
    r"""expr: ( ( ph /\ ps ) -> ( ch -> th ) ).

    Exportation.  Given ( ( ph /\ ( ps /\ ch ) ) -> th ), derive
    ( ( ph /\ ps ) -> ( ch -> th ) ).
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "expr")
    h1 = lb.hyp("expr.1", r"( ( ph /\ ( ps /\ ch ) ) -> th )")
    s1 = lb.ref(
        "s1",
        "( ph -> ( ps -> ( ch -> th ) ) )",
        h1,
        ref="exp32",
        note="exp32 expr.1",
    )
    res = lb.ref(
        "res",
        r"( ( ph /\ ps ) -> ( ch -> th ) )",
        s1,
        ref="imp",
        note="imp s1",
    )
    return lb.build(res)


def prove_pm3_2(sys: System) -> Proof:
    r"""pm3.2: ( ph -> ( ps -> ( ph /\ ps ) ) ).

    Conjunction introduction.  If ph and ps hold individually, then
    their conjunction holds.
    (Contributed by NM, 5-Jan-1993.)
    """
    lb = ProofBuilder(sys, "pm3.2")
    s_id = lb.ref(
        "s_id",
        r"( ( ph /\ ps ) -> ( ph /\ ps ) )",
        ref="id",
        note="id",
    )
    res = lb.ref(
        "res",
        r"( ph -> ( ps -> ( ph /\ ps ) ) )",
        s_id,
        ref="ex",
        note="ex",
    )
    return lb.build(res)


def prove_pm3_2i(sys: System) -> Proof:
    r"""pm3.2i: ( ph /\ ps ).

    Hyp 1: ph
    Hyp 2: ps
    Concl: ( ph /\ ps )

    Inference form of pm3.2.
    (Contributed by NM, 5-Jan-1993.)
    set.mm proof: wa pm3.2 mp2.
    """
    lb = ProofBuilder(sys, "pm3.2i")
    h1 = lb.hyp("pm3.2i.1", "ph")
    h2 = lb.hyp("pm3.2i.2", "ps")
    pm3_2_ref = lb.ref(
        "pm3_2_ref",
        r"( ph -> ( ps -> ( ph /\ ps ) ) )",
        ref="pm3.2",
        note="pm3.2",
    )
    res = lb.ref(
        "res",
        r"( ph /\ ps )",
        h1,
        h2,
        pm3_2_ref,
        ref="mp2",
        note="mp2",
    )
    return lb.build(res)


def prove_3pm3_2i(sys: System) -> Proof:
    """3pm3.2i: ( φ ∧ ψ ∧ χ ).

    Inference form: from φ, ψ, and χ, derive their triple conjunction.
    (Contributed by NM, 5-Jan-1993.)
    set.mm proof: w3a wa pm3.2i df-3an mpbir2an.
    """
    lb = ProofBuilder(sys, "3pm3.2i")
    h1 = lb.hyp("3pm3.2i.1", "ph")
    h2 = lb.hyp("3pm3.2i.2", "ps")
    h3 = lb.hyp("3pm3.2i.3", "ch")
    # pm3.2i: ( φ ∧ ψ )
    s_pm32 = lb.ref("s_pm32", "( φ ∧ ψ )", h1, h2, ref="pm3.2i", note="pm3.2i")
    # df-3an: ( φ ∧ ψ ∧ χ ) ↔ ( ( φ ∧ ψ ) ∧ χ )
    df3an = lb.ref(
        "df3an",
        "( φ ∧ ψ ∧ χ ) ↔ ( ( φ ∧ ψ ) ∧ χ )",
        ref="df-3an",
        note="df-3an",
    )
    # mpbir2an
    res = lb.ref(
        "res",
        "( φ ∧ ψ ∧ χ )",
        s_pm32,
        h3,
        df3an,
        ref="mpbir2an",
        note="mpbir2an",
    )
    return lb.build(res)


def prove_pm3_2an3(sys: System) -> Proof:
    r"""pm3.2an3: ( ph -> ( ps -> ( ch -> ( ph /\ ps /\ ch ) ) ) ).


    Ternary conjunction introduction.
    (Contributed by NM, 5-Jan-1993.)
    """
    lb = ProofBuilder(sys, "pm3.2an3")
    s_id = lb.ref(
        "s_id",
        "( ph /\\ ps /\\ ch ) -> ( ph /\\ ps /\\ ch )",
        ref="id",
        note="id",
    )
    res = lb.ref(
        "res",
        "( ph -> ( ps -> ( ch -> ( ph /\\ ps /\\ ch ) ) ) )",
        s_id,
        ref="3exp",
        note="3exp",
    )
    return lb.build(res)


def prove_pm3_43i(sys: System) -> Proof:
    r"""pm3.43i: ( ( ph -> ps ) -> ( ( ph -> ch ) -> ( ph -> ( ps /\ ch ) ) ) ).

    Inference form of pm3.43.  If ph implies ps and ph implies ch, then
    ph implies their conjunction.
    (Contributed by NM, 5-Jan-1993.)
    set.mm proof: wa pm3.2 imim3i.
    """
    lb = ProofBuilder(sys, "pm3.43i")
    # pm3.2 with ph:=ps, ps:=ch: ( ps -> ( ch -> ( ps /\ ch ) ) )
    s1 = lb.ref(
        "s1",
        r"( ps -> ( ch -> ( ps /\ ch ) ) )",
        ref="pm3.2",
        note="pm3.2",
    )
    # imim3i with θ:=ph, φ:=ps, ψ:=ch, χ:=(ps∧ch)
    res = lb.ref(
        "res",
        r"( ( ph -> ps ) -> ( ( ph -> ch ) -> ( ph -> ( ps /\ ch ) ) ) )",
        s1,
        ref="imim3i",
        note="imim3i",
    )
    return lb.build(res)


def prove_pm3_43(sys: System) -> Proof:
    r"""pm3.43: ( ( ( ph -> ps ) /\ ( ph -> ch ) ) -> ( ph -> ( ps /\ ch ) ) ).

    If ph implies ps and ph implies ch, then ph implies their conjunction.
    (Contributed by NM, 5-Jan-1993.)
    set.mm proof: pm3.43i imp.
    """
    lb = ProofBuilder(sys, "pm3.43")
    s1 = lb.ref(
        "s1",
        r"( ( ph -> ps ) -> ( ( ph -> ch ) -> ( ph -> ( ps /\ ch ) ) ) )",
        ref="pm3.43i",
        note="pm3.43i",
    )
    res = lb.ref(
        "res",
        r"( ( ( ph -> ps ) /\ ( ph -> ch ) ) -> ( ph -> ( ps /\ ch ) ) )",
        s1,
        ref="imp",
        note="imp",
    )
    return lb.build(res)


def prove_pm3_45(sys: System) -> Proof:
    """pm3.45: ( φ → ψ ) → ( ( φ ∧ χ ) → ( ψ ∧ χ ) ).

    Conjoin a common consequent to both sides of a conditional.
    """
    lb = ProofBuilder(sys, "pm3.45")
    s_id = lb.ref(
        "s_id",
        "( φ → ψ ) → ( φ → ψ )",
        ref="id",
        note="id",
    )
    res = lb.ref(
        "res",
        "( φ → ψ ) → ( ( φ ∧ χ ) → ( ψ ∧ χ ) )",
        s_id,
        ref="anim1d",
        note="anim1d",
    )
    return lb.build(res)


def prove_mpd3an3(sys: System) -> Proof:
    r"""mpd3an3: ( ( ph /\ ps ) -> th ).

    Hyp 1: ( ph /\ ps ) -> ch
    Hyp 2: ( ph /\ ps /\ ch ) -> th
    Concl: ( ph /\ ps ) -> th

    A modus ponens deduction with a triple conjunction antecedent.
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: wa 3expa mpdan.
    """
    lb = ProofBuilder(sys, "mpd3an3")
    h2 = lb.hyp("mpd3an3.2", r"( ph /\ ps ) -> ch")
    h3 = lb.hyp("mpd3an3.3", r"( ph /\ ps /\ ch ) -> th")
    s1 = lb.ref("s1", r"( ( ph /\ ps ) /\ ch ) -> th", h3, ref="3expa", note="3expa")
    res = lb.ref("res", r"( ph /\ ps ) -> th", h2, s1, ref="mpdan", note="mpdan")
    return lb.build(res)


def prove_mp3an1(sys: System) -> Proof:
    r"""mp3an1: ( ps /\ ch ) -> th.

    Hyp 1: ph
    Hyp 2: ( ph /\ ps /\ ch ) -> th
    Concl: ( ps /\ ch ) -> th

    An inference form of modus ponens with a triple conjunction antecedent
    where the first antecedent is provided.
    (Contributed by NM, 14-May-1993.)
    set.mm proof: 3expb mpan.
    """
    lb = ProofBuilder(sys, "mp3an1")
    h1 = lb.hyp("mp3an1.1", r"ph")
    h2 = lb.hyp("mp3an1.2", r"( ph /\ ps /\ ch ) -> th")
    s1 = lb.ref(
        "s1",
        r"( ph /\ ( ps /\ ch ) ) -> th",
        h2,
        ref="3expb",
        note="3expb mp3an1.2",
    )
    res = lb.ref(
        "res",
        r"( ps /\ ch ) -> th",
        h1,
        s1,
        ref="mpan",
        note="mpan mp3an1.1, s1",
    )
    return lb.build(res)


def prove_mp3an3(sys: System) -> Proof:
    r"""mp3an3: ( ( ph /\ ps ) -> th ).

    Hyp 1: ch
    Hyp 2: ( ph /\ ps /\ ch ) -> th
    Concl: ( ph /\ ps ) -> th

    An inference form of modus ponens with a triple conjunction antecedent.
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: 3expia mpi.
    """
    lb = ProofBuilder(sys, "mp3an3")
    h1 = lb.hyp("mp3an3.1", r"ch")
    h2 = lb.hyp("mp3an3.2", r"( ph /\ ps /\ ch ) -> th")
    s1 = lb.ref(
        "s1",
        r"( ( ph /\ ps ) -> ( ch -> th ) )",
        h2,
        ref="3expia",
        note="3expia mp3an3.2",
    )
    res = lb.ref(
        "res",
        r"( ( ph /\ ps ) -> th )",
        h1,
        s1,
        ref="mpi",
        note="mpi mp3an3.1, s1",
    )
    return lb.build(res)


def prove_mpanr2(sys: System) -> Proof:
    """mpanr2: (φ ∧ ψ) → θ.

    Inference form of mpanr: given the second antecedent ch and a proof
    that ( φ ∧ ( ψ ∧ χ ) ) → θ, conclude ( φ ∧ ψ ) → θ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "mpanr2")
    h1 = lb.hyp("mpanr2.1", "χ")
    h2 = lb.hyp("mpanr2.2", "( φ ∧ ( ψ ∧ χ ) ) → θ")

    s1 = lb.ref(
        "s1",
        "ψ → ( ψ ∧ χ )",
        h1,
        ref="jctr",
        note="jctr mpanr2.1",
    )

    res = lb.ref(
        "res",
        "( φ ∧ ψ ) → θ",
        s1,
        h2,
        ref="sylan2",
        note="sylan2 s1, mpanr2.2",
    )

    return lb.build(res)


def prove_mp3anl3(sys: System) -> Proof:
    r"""mp3anl3: ( ( ( ph /\ ps ) /\ th ) -> ta ).

    Hyp 1: ch
    Hyp 2: ( ( ( ph /\ ps /\ ch ) /\ th ) -> ta )
    Concl: ( ( ( ph /\ ps ) /\ th ) -> ta )

    An inference form of modus ponens with a triple conjunction antecedent,
    left-hand conjunct eliminated.  (Contributed by NM, 3-Jan-1993.)
    set.mm proof: ex mp3an3 imp.
    """
    lb = ProofBuilder(sys, "mp3anl3")
    h1 = lb.hyp("mp3anl3.1", r"ch")
    h2 = lb.hyp("mp3anl3.2", r"( ( ( ph /\ ps /\ ch ) /\ th ) -> ta )")
    s1 = lb.ref(
        "s1",
        r"( ( ph /\ ps /\ ch ) -> ( th -> ta ) )",
        h2,
        ref="ex",
        note="ex mp3anl3.2",
    )
    s2 = lb.ref(
        "s2",
        r"( ( ph /\ ps ) -> ( th -> ta ) )",
        h1,
        s1,
        ref="mp3an3",
        note="mp3an3 mp3anl3.1, s1",
    )
    res = lb.ref(
        "res",
        r"( ( ( ph /\ ps ) /\ th ) -> ta )",
        s2,
        ref="imp",
        note="imp s2",
    )
    return lb.build(res)


def prove_mp3anl1(sys: System) -> Proof:
    r"""mp3anl1: ( ( ( ψ ∧ χ ) ∧ θ ) → τ ).

    Hyp 1: φ
    Hyp 2: ( ( ( φ ∧ ψ ∧ χ ) ∧ θ ) → τ )
    Concl: ( ( ( ψ ∧ χ ) ∧ θ ) → τ )

    An inference form of modus ponens with a triple conjunction antecedent,
    first conjunct eliminated.  (Contributed by NM, 14-May-1993.)
    set.mm proof: ex mp3an1 imp.
    """
    lb = ProofBuilder(sys, "mp3anl1")
    h1 = lb.hyp("mp3anl1.1", "φ")
    h2 = lb.hyp("mp3anl1.2", r"( ( ( φ ∧ ψ ∧ χ ) ∧ θ ) → τ )")
    s1 = lb.ref(
        "s1",
        r"( φ ∧ ψ ∧ χ ) → ( θ → τ )",
        h2,
        ref="ex",
        note="ex mp3anl1.2",
    )
    s2 = lb.ref(
        "s2",
        r"( ψ ∧ χ ) → ( θ → τ )",
        h1,
        s1,
        ref="mp3an1",
        note="mp3an1 mp3anl1.1, s1",
    )
    res = lb.ref(
        "res",
        r"( ( ( ψ ∧ χ ) ∧ θ ) → τ )",
        s2,
        ref="imp",
        note="imp s2",
    )
    return lb.build(res)


def prove_mp3anr3(sys: System) -> Proof:
    r"""mp3anr3: ( ( φ ∧ ( ψ ∧ χ ) ) → τ ).

    Hyp 1: θ
    Hyp 2: ( ( φ ∧ ( ψ ∧ χ ∧ θ ) ) → τ )
    Concl: ( ( φ ∧ ( ψ ∧ χ ) ) → τ )

    An inference form of modus ponens with a triple conjunction antecedent,
    right-hand conjunct eliminated.  (Contributed by NM, 14-May-1993.)
    set.mm proof: ancoms mp3anl3.
    """
    lb = ProofBuilder(sys, "mp3anr3")
    h1 = lb.hyp("mp3anr3.1", r"θ")
    h2 = lb.hyp("mp3anr3.2", r"( ( φ ∧ ( ψ ∧ χ ∧ θ ) ) → τ )")
    s1 = lb.ref(
        "s1",
        r"( ( ( ψ ∧ χ ∧ θ ) ∧ φ ) → τ )",
        h2,
        ref="ancoms",
        note="ancoms mp3anr3.2",
    )
    s2 = lb.ref(
        "s2",
        r"( ( ( ψ ∧ χ ) ∧ φ ) → τ )",
        h1,
        s1,
        ref="mp3anl3",
        note="mp3anl3 mp3anr3.1, s1",
    )
    res = lb.ref(
        "res",
        r"( ( φ ∧ ( ψ ∧ χ ) ) → τ )",
        s2,
        ref="ancoms",
        note="ancoms s2",
    )
    return lb.build(res)


def prove_mp3anr1(sys: System) -> Proof:
    r"""mp3anr1: ( ( φ ∧ ( χ ∧ θ ) ) → τ ).

    Hyp 1: ψ
    Hyp 2: ( ( φ ∧ ( ψ ∧ χ ∧ θ ) ) → τ )
    Concl: ( ( φ ∧ ( χ ∧ θ ) ) → τ )

    An inference form of modus ponens with a triple conjunction antecedent,
    right-hand first conjunct eliminated.  (Contributed by NM, 14-May-1993.)
    set.mm proof: ancoms mp3anl1.
    """
    lb = ProofBuilder(sys, "mp3anr1")
    h1 = lb.hyp("mp3anr1.1", "ψ")
    h2 = lb.hyp("mp3anr1.2", r"( ( φ ∧ ( ψ ∧ χ ∧ θ ) ) → τ )")
    s1 = lb.ref(
        "s1",
        r"( ( ( ψ ∧ χ ∧ θ ) ∧ φ ) → τ )",
        h2,
        ref="ancoms",
        note="ancoms mp3anr1.2",
    )
    s2 = lb.ref(
        "s2",
        r"( ( ( χ ∧ θ ) ∧ φ ) → τ )",
        h1,
        s1,
        ref="mp3anl1",
        note="mp3anl1 mp3anr1.1, s1",
    )
    res = lb.ref(
        "res",
        r"( ( φ ∧ ( χ ∧ θ ) ) → τ )",
        s2,
        ref="ancoms",
        note="ancoms s2",
    )
    return lb.build(res)


def prove_ancli(sys: System) -> Proof:
    r"""ancli: ( ph -> ( ph /\ ps ) ).



    Hyp 1: ( ph -> ps )
    Concl: ( ph -> ( ph /\ ps ) )

    Conjoin antecedent with consequent.  (Contributed by NM, 5-Jan-1993.)
    set.mm proof: id jca.
    """
    lb = ProofBuilder(sys, "ancli")
    h1 = lb.hyp("ancli.1", "( ph -> ps )")
    s1 = lb.ref(
        "s1",
        "( ph -> ph )",
        ref="id",
        note="id",
    )
    res = lb.ref(
        "res",
        "( ph -> ( ph /\\ ps ) )",
        s1,
        h1,
        ref="jca",
        note="jca s1, ancli.1",
    )
    return lb.build(res)


def prove_anc2l(sys: System) -> Proof:
    """anc2l: ( φ → ( ψ → χ ) ) → ( φ → ( ψ → ( φ ∧ χ ) ) ).

    Conjoin antecedent with left consequent, closed form.
    (Contributed by NM, 5-Jan-1993.)
    """
    lb = ProofBuilder(sys, "anc2l")

    # pm5.42: ( φ → ( ψ → χ ) ) ↔ ( φ → ( ψ → ( φ ∧ χ ) ) )
    s1 = lb.ref(
        "s1",
        "( φ → ( ψ → χ ) ) ↔ ( φ → ( ψ → ( φ ∧ χ ) ) )",
        ref="pm5.42",
        note="pm5.42",
    )

    # biimpi: convert biconditional to forward implication
    res = lb.ref(
        "res",
        "( φ → ( ψ → χ ) ) → ( φ → ( ψ → ( φ ∧ χ ) ) )",
        s1,
        ref="biimpi",
        note="biimpi",
    )

    return lb.build(res)


def prove_anc2li(sys: System) -> Proof:
    r"""anc2li: ( ph -> ( ps -> ( ph /\ ch ) ) ).

    Hyp 1: ( ph -> ( ps -> ch ) )
    Concl: ( ph -> ( ps -> ( ph /\ ch ) ) )

    Conjoin antecedent with left consequent.  (Contributed by NM, 5-Jan-1993.)
    set.mm proof: id jctild.
    """
    lb = ProofBuilder(sys, "anc2li")
    h1 = lb.hyp("anc2li.1", "( ph -> ( ps -> ch ) )")
    s1 = lb.ref(
        "s1",
        "( ph -> ph )",
        ref="id",
        note="id",
    )
    res = lb.ref(
        "res",
        "( ph -> ( ps -> ( ph /\\ ch ) ) )",
        h1,
        s1,
        ref="jctild",
        note="jctild anc2li.1, s1",
    )
    return lb.build(res)


def prove_ancri(sys: System) -> Proof:
    r"""ancri: ( ph -> ( ps /\ ph ) ).

    Hyp 1: ( ph -> ps )
    Concl: ( ph -> ( ps /\ ph ) )

    Conjoin consequent to right.  (Contributed by NM, 5-Jan-1993.)
    set.mm proof: id jca.
    """
    lb = ProofBuilder(sys, "ancri")
    h1 = lb.hyp("ancri.1", "( ph -> ps )")
    s1 = lb.ref(
        "s1",
        "( ph -> ph )",
        ref="id",
        note="id",
    )
    res = lb.ref(
        "res",
        "( ph -> ( ps /\\ ph ) )",
        h1,
        s1,
        ref="jca",
        note="jca ancri.1, s1",
    )

    return lb.build(res)


def prove_jca(sys: System) -> Proof:
    r"""jca: ( ph -> ( ps /\ ch ) ).

    Hyp 1: ( ph -> ps )
    Hyp 2: ( ph -> ch )
    Concl: ( ph -> ( ps /\ ch ) )

    Join consequents with `and`.  (Contributed by NM, 5-Jan-1993.)
    set.mm proof: wa pm3.2 sylc.
    """
    lb = ProofBuilder(sys, "jca")
    h1 = lb.hyp("jca.1", "( ph -> ps )")
    h2 = lb.hyp("jca.2", "( ph -> ch )")
    pm32 = lb.ref(
        "pm32",
        "( ps -> ( ch -> ( ps /\\ ch ) ) )",
        ref="pm3.2",
        note="pm3.2",
    )
    res = lb.ref(
        "res",
        "( ph -> ( ps /\\ ch ) )",
        h1,
        h2,
        pm32,
        ref="sylc",
        note="sylc",
    )
    return lb.build(res)


def prove_jcai(sys: System) -> Proof:
    r"""jcai: ( ph -> ( ps /\ ch ) ).

    Hyp 1: ( ph -> ps )
    Hyp 2: ( ph -> ( ps -> ch ) )
    Concl: ( ph -> ( ps /\ ch ) )

    Join consequents with `and` via deduction.
    (Contributed by NM, 5-Jan-1993.)
    set.mm proof: mpd jca.
    """
    lb = ProofBuilder(sys, "jcai")
    h1 = lb.hyp("jcai.1", "( ph -> ps )")
    h2 = lb.hyp("jcai.2", "( ph -> ( ps -> ch ) )")
    s1 = lb.ref(
        "s1",
        "( ph -> ch )",
        h1,
        h2,
        ref="mpd",
        note="mpd jcai.1, jcai.2",
    )
    res = lb.ref(
        "res",
        "( ph -> ( ps /\\ ch ) )",
        h1,
        s1,
        ref="jca",
        note="jca jcai.1, s1",
    )
    return lb.build(res)


def prove_jcab(sys: System) -> Proof:
    """jcab: ( φ → ( ψ ∧ χ ) ) ↔ ( ( φ → ψ ) ∧ ( φ → χ ) ).

    Distribute an implication over a conjunction — biconditional form.
    (Contributed by NM, 5-Jan-1993.)
    """
    lb = ProofBuilder(sys, "jcab")

    # ( ψ ∧ χ ) → ψ
    s1 = lb.ref("s1", "( ψ ∧ χ ) → ψ", ref="simpl", note="simpl")

    # ( φ → ( ψ ∧ χ ) ) → ( φ → ψ )
    s2 = lb.ref("s2", "( φ → ( ψ ∧ χ ) ) → ( φ → ψ )", s1, ref="imim2i", note="imim2i")

    # ( ψ ∧ χ ) → χ
    s3 = lb.ref("s3", "( ψ ∧ χ ) → χ", ref="simpr", note="simpr")

    # ( φ → ( ψ ∧ χ ) ) → ( φ → χ )
    s4 = lb.ref("s4", "( φ → ( ψ ∧ χ ) ) → ( φ → χ )", s3, ref="imim2i", note="imim2i")

    # ( φ → ( ψ ∧ χ ) ) → ( ( φ → ψ ) ∧ ( φ → χ ) )
    s5 = lb.ref(
        "s5",
        "( φ → ( ψ ∧ χ ) ) → ( ( φ → ψ ) ∧ ( φ → χ ) )",
        s2,
        s4,
        ref="jca",
        note="jca",
    )

    # ( ( φ → ψ ) ∧ ( φ → χ ) ) → ( φ → ( ψ ∧ χ ) )
    s6 = lb.ref(
        "s6",
        "( ( φ → ψ ) ∧ ( φ → χ ) ) → ( φ → ( ψ ∧ χ ) )",
        ref="pm3.43",
        note="pm3.43",
    )

    # ( φ → ( ψ ∧ χ ) ) ↔ ( ( φ → ψ ) ∧ ( φ → χ ) )
    res = lb.ref(
        "res", "( φ → ( ψ ∧ χ ) ) ↔ ( ( φ → ψ ) ∧ ( φ → χ ) )", s5, s6, ref="impbii", note="impbii"
    )

    return lb.build(res)


def prove_pm4_76(sys: System) -> Proof:
    """pm4.76: ( ( φ → ψ ) ∧ ( φ → χ ) ) ↔ ( φ → ( ψ ∧ χ ) ).

    Commuted form of jcab.  (Contributed by NM, 5-Jan-1993.)
    """
    lb = ProofBuilder(sys, "pm4.76")

    s_jcab = lb.ref(
        "s_jcab",
        "( φ → ( ψ ∧ χ ) ) ↔ ( ( φ → ψ ) ∧ ( φ → χ ) )",
        ref="jcab",
        note="jcab",
    )
    res = lb.ref(
        "res",
        "( ( φ → ψ ) ∧ ( φ → χ ) ) ↔ ( φ → ( ψ ∧ χ ) )",
        s_jcab,
        ref="bicomi",
        note="bicomi",
    )

    return lb.build(res)


def prove_jccir(sys: System) -> Proof:
    r"""jccir: ( ph -> ( ps /\ ch ) ).

    Hyp 1: ( ph -> ps )
    Hyp 2: ( ps -> ch )
    Concl: ( ph -> ( ps /\ ch ) )

    Inference form of jca where the second hypothesis is an implication
    instead of a direct conjunct.  (Contributed by NM, 5-Jan-1993.)
    set.mm proof: syl jca.
    """
    lb = ProofBuilder(sys, "jccir")
    h1 = lb.hyp("jccir.1", "( ph -> ps )")
    h2 = lb.hyp("jccir.2", "( ps -> ch )")
    s1 = lb.ref(
        "s1",
        "( ph -> ch )",
        h1,
        h2,
        ref="syl",
        note="syl jccir.1, jccir.2",
    )
    res = lb.ref(
        "res",
        "( ph -> ( ps /\\ ch ) )",
        h1,
        s1,
        ref="jca",
        note="jca jccir.1, s1",
    )
    return lb.build(res)


def prove_jccil(sys: System) -> Proof:
    """jccil: φ → ( χ ∧ ψ ).

    Hyp 1: φ → ψ
    Hyp 2: ψ → χ
    Concl: φ → ( χ ∧ ψ )

    Inference form of jccir with swapped conjuncts in the conclusion.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "jccil")
    h1 = lb.hyp("jccil.1", "φ → ψ")
    h2 = lb.hyp("jccil.2", "ψ → χ")
    s1 = lb.ref(
        "s1",
        "φ → ( ψ ∧ χ )",
        h1,
        h2,
        ref="jccir",
        note="jccir jccil.1, jccil.2",
    )
    res = lb.ref(
        "res",
        "φ → ( χ ∧ ψ )",
        s1,
        ref="ancomd",
        note="ancomd s1",
    )
    return lb.build(res)


def prove_jctir(sys: System) -> Proof:
    r"""jctir: ( ph -> ( ps /\ ch ) ).

    Hyp 1: ( ph -> ps )
    Hyp 2: ch
    Concl: ( ph -> ( ps /\ ch ) )

    Inference form of jca where the second conjunct is unconditionally
    true.  (Contributed by NM, 5-Jan-1993.)
    set.mm proof: a1i jca.
    """
    lb = ProofBuilder(sys, "jctir")
    h1 = lb.hyp("jctir.1", "( ph -> ps )")
    h2 = lb.hyp("jctir.2", "ch")
    s1 = lb.ref(
        "s1",
        "( ph -> ch )",
        h2,
        ref="a1i",
        note="a1i jctir.2",
    )
    res = lb.ref(
        "res",
        "( ph -> ( ps /\\ ch ) )",
        h1,
        s1,
        ref="jca",
        note="jca jctir.1, s1",
    )
    return lb.build(res)


def prove_jctil(sys: System) -> Proof:
    r"""jctil: ( ph -> ( ch /\ ps ) ).

    Hyp 1: ( ph -> ps )
    Hyp 2: ch
    Concl: ( ph -> ( ch /\ ps ) )

    Inference form of jca where the first conjunct is unconditionally
    true.  Like jctir but with swapped order in the conclusion.
    (Contributed by NM, 5-Jan-1993.)
    set.mm proof: a1i jca.
    """
    lb = ProofBuilder(sys, "jctil")
    h1 = lb.hyp("jctil.1", "( ph -> ps )")
    h2 = lb.hyp("jctil.2", "ch")
    s1 = lb.ref(
        "s1",
        "( ph -> ch )",
        h2,
        ref="a1i",
        note="a1i jctil.2",
    )
    res = lb.ref(
        "res",
        "( ph -> ( ch /\\ ps ) )",
        s1,
        h1,
        ref="jca",
        note="jca s1, jctil.1",
    )
    return lb.build(res)


def prove_jctl(sys: System) -> Proof:
    r"""jctl: ( ph -> ( ps /\ ph ) ).

    Hyp 1: ps
    Concl: ( ph -> ( ps /\ ph ) )

    Inference joining a conjunct to the left of a consequent.
    (Contributed by NM, 5-Jan-1993.)
    set.mm proof: id jctil.
    """
    lb = ProofBuilder(sys, "jctl")
    h1 = lb.hyp("jctl.1", "ps")
    s1 = lb.ref(
        "s1",
        "( ph -> ph )",
        ref="id",
        note="id",
    )
    res = lb.ref(
        "res",
        "( ph -> ( ps /\\ ph ) )",
        s1,
        h1,
        ref="jctil",
        note="jctil s1, jctl.1",
    )
    return lb.build(res)


def prove_jctr(sys: System) -> Proof:
    r"""jctr: ( ph -> ( ph /\ ps ) ).

    Hyp 1: ps
    Concl: ( ph -> ( ph /\ ps ) )

    Inference conjoining a theorem to the right of a consequent.
    (Contributed by NM, 18-Aug-1993.)  (Proof shortened by Wolf Lammen,
    24-Oct-2012.)
    set.mm proof: id jctir.
    """
    lb = ProofBuilder(sys, "jctr")
    h1 = lb.hyp("jctr.1", "ps")
    s1 = lb.ref(
        "s1",
        "( ph -> ph )",
        ref="id",
        note="id",
    )
    res = lb.ref(
        "res",
        "( ph -> ( ph /\\ ps ) )",
        s1,
        h1,
        ref="jctir",
        note="jctir s1, jctr.1",
    )
    return lb.build(res)


def prove_jcad(sys: System) -> Proof:
    r"""jcad: ( ph -> ( ps -> ( ch /\ th ) ) ).

    Hyp 1: ( ph -> ( ps -> ch ) )
    Hyp 2: ( ph -> ( ps -> th ) )
    Concl: ( ph -> ( ps -> ( ch /\ th ) ) )

    Deduction form of jca (join consequents with and).
    (Contributed by NM, 5-Jan-1993.)
    """
    lb = ProofBuilder(sys, "jcad")

    h1 = lb.hyp("jcad.1", "( ph -> ( ps -> ch ) )")
    h2 = lb.hyp("jcad.2", "( ph -> ( ps -> th ) )")

    pm32 = lb.ref(
        "pm32",
        "( ch -> ( th -> ( ch /\\ th ) ) )",
        ref="pm3.2",
        note="pm3.2",
    )

    res = lb.ref(
        "res",
        "( ph -> ( ps -> ( ch /\\ th ) ) )",
        h1,
        h2,
        pm32,
        ref="syl6c",
        note="syl6c",
    )

    return lb.build(res)


def prove_jctild(sys: System) -> Proof:
    r"""jctild: ( ph -> ( ps -> ( th /\ ch ) ) ).

    Hyp 1: ( ph -> ( ps -> ch ) )
    Hyp 2: ( ph -> th )
    Concl: ( ph -> ( ps -> ( th /\ ch ) ) )

    Deduction form of jctil where the first antecedent in the
    antecedent of the conclusion is `th` while the second consequent
    of the first hypothesis is `ch`.
    (Contributed by NM, 5-Jan-1993.)
    set.mm proof: a1d jcad.
    """
    lb = ProofBuilder(sys, "jctild")

    h1 = lb.hyp("jctild.1", "( ph -> ( ps -> ch ) )")
    h2 = lb.hyp("jctild.2", "( ph -> th )")

    s1 = lb.ref(
        "s1",
        "( ph -> ( ps -> th ) )",
        h2,
        ref="a1d",
        note="a1d jctild.2",
    )

    res = lb.ref(
        "res",
        "( ph -> ( ps -> ( th /\\ ch ) ) )",
        s1,
        h1,
        ref="jcad",
        note="jcad s1, jctild.1",
    )

    return lb.build(res)


def prove_jca2(sys: System) -> Proof:
    r"""jca2: ( ph -> ( ps -> ( ch /\ th ) ) ).

    Hyp 1: ( ph -> ( ps -> ch ) )
    Hyp 2: ( ps -> th )
    Concl: ( ph -> ( ps -> ( ch /\ th ) ) )

    Join consequents with `and` where the second consequent is not
    dependent on `ph`.
    (Contributed by NM, 5-Jan-1993.)
    """
    lb = ProofBuilder(sys, "jca2")

    h1 = lb.hyp("jca2.1", "( ph -> ( ps -> ch ) )")
    h2 = lb.hyp("jca2.2", "( ps -> th )")

    s1 = lb.ref(
        "s1",
        "( ph -> ( ps -> th ) )",
        h2,
        ref="a1i",
        note="a1i jca2.2",
    )

    res = lb.ref(
        "res",
        "( ph -> ( ps -> ( ch /\\ th ) ) )",
        h1,
        s1,
        ref="jcad",
        note="jcad",
    )

    return lb.build(res)


def prove_jca32(sys: System) -> Proof:
    r"""jca32: ( ph -> ( ps /\\ ( ch /\\ th ) ) ).

    Hyp 1: ( ph -> ps )
    Hyp 2: ( ph -> ch )
    Hyp 3: ( ph -> th )
    Concl: ( ph -> ( ps /\ ( ch /\ th ) ) )

    Join consequents with `and`.  (Contributed by NM, 5-Jan-1993.)
    """
    lb = ProofBuilder(sys, "jca32")
    h1 = lb.hyp("jca32.1", "( ph -> ps )")
    h2 = lb.hyp("jca32.2", "( ph -> ch )")
    h3 = lb.hyp("jca32.3", "( ph -> th )")

    s1 = lb.ref(
        "s1",
        "( ph -> ( ch /\\ th ) )",
        h2,
        h3,
        ref="jca",
        note="jca jca32.2, jca32.3",
    )

    res = lb.ref(
        "res",
        "( ph -> ( ps /\\ ( ch /\\ th ) ) )",
        h1,
        s1,
        ref="jca",
        note="jca jca32.1, s1",
    )

    return lb.build(res)


def prove_jca31(sys: System) -> Proof:
    r"""jca31: ( ph -> ( ( ps /\ ch ) /\ th ) ).

    Hyp 1: ( ph -> ps )
    Hyp 2: ( ph -> ch )
    Hyp 3: ( ph -> th )
    Concl: ( ph -> ( ( ps /\ ch ) /\ th ) )

    Join consequents with `and`, grouping the first two together.
    (Contributed by NM, 5-Jan-1993.)
    """
    lb = ProofBuilder(sys, "jca31")
    h1 = lb.hyp("jca31.1", "( ph -> ps )")
    h2 = lb.hyp("jca31.2", "( ph -> ch )")
    h3 = lb.hyp("jca31.3", "( ph -> th )")

    s1 = lb.ref(
        "s1",
        "( ph -> ( ps /\\ ch ) )",
        h1,
        h2,
        ref="jca",
        note="jca jca31.1, jca31.2",
    )

    res = lb.ref(
        "res",
        "( ph -> ( ( ps /\\ ch ) /\\ th ) )",
        s1,
        h3,
        ref="jca",
        note="jca s1, jca31.3",
    )

    return lb.build(res)


def prove_3jca(sys: System) -> Proof:
    r"""3jca: ( ph -> ( ps /\ ch /\ th ) ).

    Hyp 1: ( ph -> ps )
    Hyp 2: ( ph -> ch )
    Hyp 3: ( ph -> th )
    Concl: ( ph -> ( ps /\ ch /\ th ) )

    Join consequents with triple-`and`.
    (Contributed by NM, 5-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3jca")
    h1 = lb.hyp("3jca.1", "( ph -> ps )")
    h2 = lb.hyp("3jca.2", "( ph -> ch )")
    h3 = lb.hyp("3jca.3", "( ph -> th )")

    s1 = lb.ref(
        "s1",
        "( ph -> ( ( ps /\\ ch ) /\\ th ) )",
        h1,
        h2,
        h3,
        ref="jca31",
        note="jca31 3jca.1, 3jca.2, 3jca.3",
    )

    df3an = lb.ref(
        "df3an",
        "( ( ps /\\ ch /\\ th ) <-> ( ( ps /\\ ch ) /\\ th ) )",
        ref="df-3an",
        note="df-3an",
    )

    res = lb.ref(
        "res",
        "( ph -> ( ps /\\ ch /\\ th ) )",
        s1,
        df3an,
        ref="sylibr",
        note="sylibr s1, df3an",
    )

    return lb.build(res)


def prove_3jcad(sys: System) -> Proof:
    r"""3jcad: ( ph -> ( ps -> ( ch /\ th /\ ta ) ) ).

    Hyp 1: ( ph -> ( ps -> ch ) )
    Hyp 2: ( ph -> ( ps -> th ) )
    Hyp 3: ( ph -> ( ps -> ta ) )
    Concl: ( ph -> ( ps -> ( ch /\ th /\ ta ) ) )

    Deduction form of 3jca.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3jcad")

    h1 = lb.hyp("3jcad.1", "( ph -> ( ps -> ch ) )")
    h2 = lb.hyp("3jcad.2", "( ph -> ( ps -> th ) )")
    h3 = lb.hyp("3jcad.3", "( ph -> ( ps -> ta ) )")

    s1 = lb.ref(
        "s1",
        "( ( ph /\\ ps ) -> ch )",
        h1,
        ref="imp",
        note="imp 3jcad.1",
    )
    s2 = lb.ref(
        "s2",
        "( ( ph /\\ ps ) -> th )",
        h2,
        ref="imp",
        note="imp 3jcad.2",
    )
    s3 = lb.ref(
        "s3",
        "( ( ph /\\ ps ) -> ta )",
        h3,
        ref="imp",
        note="imp 3jcad.3",
    )

    s4 = lb.ref(
        "s4",
        "( ( ph /\\ ps ) -> ( ch /\\ th /\\ ta ) )",
        s1,
        s2,
        s3,
        ref="3jca",
        note="3jca s1, s2, s3",
    )

    res = lb.ref(
        "res",
        "( ph -> ( ps -> ( ch /\\ th /\\ ta ) ) )",
        s4,
        ref="ex",
        note="ex s4",
    )

    return lb.build(res)


def prove_jctird(sys: System) -> Proof:
    r"""jctird: ( ph -> ( ps -> ( ch /\ th ) ) ).

    Hyp 1: ( ph -> ( ps -> ch ) )
    Hyp 2: ( ph -> th )
    Concl: ( ph -> ( ps -> ( ch /\ th ) ) )

    Deduction form of jctir.  Join consequents with `and`, where the
    second consequent is added as an antecedent in the deduction chain.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "jctird")

    h1 = lb.hyp("jctird.1", "( ph -> ( ps -> ch ) )")
    h2 = lb.hyp("jctird.2", "( ph -> th )")

    s1 = lb.ref(
        "s1",
        "( ph -> ( ps -> th ) )",
        h2,
        ref="a1d",
        note="a1d jctird.2",
    )

    res = lb.ref(
        "res",
        "( ph -> ( ps -> ( ch /\\ th ) ) )",
        h1,
        s1,
        ref="jcad",
        note="jcad",
    )

    return lb.build(res)


def prove_expdimp(sys: System) -> Proof:
    r"""expdimp: ( ( ph /\ ps ) -> ( ch -> th ) ).

    Hyp: expdimp.1 |- ph -> ( ( ps /\ ch ) -> th )
    Concl: |- ( ( ph /\ ps ) -> ( ch -> th ) )

    A combined exportation and importation inference.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "expdimp")
    h1 = lb.hyp("expdimp.1", "ph -> ( ( ps /\\ ch ) -> th )")
    s1 = lb.ref("s1", "ph -> ( ps -> ( ch -> th ) )", h1, ref="expd", note="expd expdimp.1")
    res = lb.ref("res", "( ph /\\ ps ) -> ( ch -> th )", s1, ref="imp", note="imp s1")
    return lb.build(res)


def prove_ancrd(sys: System) -> Proof:
    r"""ancrd: ( ph -> ( ps -> ( ch /\ ps ) ) ).

    Hyp: ancrd.1 |- ( ph -> ( ps -> ch ) )
    Concl: |- ( ph -> ( ps -> ( ch /\ ps ) ) )

    Deduction form of ancr: conjoin an antecedent with the consequent
    on the right.  (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "ancrd")
    h1 = lb.hyp("ancrd.1", "( ph -> ( ps -> ch ) )")
    s1 = lb.ref(
        "s1",
        "( ph -> ( ps -> ps ) )",
        ref="idd",
        note="idd",
    )
    res = lb.ref(
        "res",
        r"( ph -> ( ps -> ( ch /\ ps ) ) )",
        h1,
        s1,
        ref="jcad",
        note="jcad ancrd.1, s1",
    )
    return lb.build(res)


# Insert prove_ancld function after prove_ancrd (after line 2987)
def prove_ancld(sys: System) -> Proof:
    r"""ancld: ( ph -> ( ps -> ( ps /\ ch ) ) ).

    Hyp: ancld.1 |- ( ph -> ( ps -> ch ) )
    Concl: |- ( ph -> ( ps -> ( ps /\ ch ) ) )

    Deduction form of ancl: conjoin the consequent with an antecedent
    on the left.  (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "ancld")
    h1 = lb.hyp("ancld.1", "( ph -> ( ps -> ch ) )")
    s1 = lb.ref(
        "s1",
        "( ph -> ( ps -> ps ) )",
        ref="idd",
        note="idd",
    )
    res = lb.ref(
        "res",
        r"( ph -> ( ps -> ( ps /\ ch ) ) )",
        s1,
        h1,
        ref="jcad",
        note="jcad s1, ancld.1",
    )
    return lb.build(res)


def prove_anc2r(sys: System) -> Proof:
    """anc2r: (φ → (ψ → χ)) → (φ → (ψ → (χ ∧ φ))).

    Conjoin antecedent to right of consequent.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "anc2r")
    s1 = lb.ref(
        "s1",
        "φ → ( χ → ( χ ∧ φ ) )",
        ref="pm3.21",
        note="pm3.21",
    )
    s2 = lb.ref(
        "s2",
        "φ → ( ( ψ → χ ) → ( ψ → ( χ ∧ φ ) ) )",
        s1,
        ref="imim2d",
        note="imim2d",
    )
    res = lb.ref(
        "res",
        "( φ → ( ψ → χ ) ) → ( φ → ( ψ → ( χ ∧ φ ) ) )",
        s2,
        ref="a2i",
        note="a2i",
    )
    return lb.build(res)


def prove_anc2ri(sys: System) -> Proof:
    r"""anc2ri: ( ph -> ( ps -> ( ch /\ ph ) ) ).

    Hyp: anc2ri.1 |- ( ph -> ( ps -> ch ) )
    Concl: |- ( ph -> ( ps -> ( ch /\ ph ) ) )

    Inference form of anc2r.  Join antecedent and consequent of
    `anc2ri.1` with `and`, where the first antecedent is conjoined
    on the right.  (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "anc2ri")
    h1 = lb.hyp("anc2ri.1", "( ph -> ( ps -> ch ) )")
    s1 = lb.ref(
        "s1",
        "( ph -> ph )",
        ref="id",
        note="id",
    )
    res = lb.ref(
        "res",
        "( ph -> ( ps -> ( ch /\\ ph ) ) )",
        h1,
        s1,
        ref="jctird",
        note="jctird anc2ri.1, s1",
    )
    return lb.build(res)


def prove_imdistani(sys: System) -> Proof:
    r"""imdistani: ( ( ph /\ ps ) -> ( ph /\ ch ) ).

    Hyp: imdistani.1 |- ( ph -> ( ps -> ch ) )
    Concl: |- ( ( ph /\ ps ) -> ( ph /\ ch ) )

    An inference distributing an implication into a conjunction.
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: wa anc2li imp.
    """
    lb = ProofBuilder(sys, "imdistani")
    h1 = lb.hyp("imdistani.1", "( ph -> ( ps -> ch ) )")
    s1 = lb.ref(
        "s1",
        "( ph -> ( ps -> ( ph /\\ ch ) ) )",
        h1,
        ref="anc2li",
        note="anc2li imdistani.1",
    )
    res = lb.ref(
        "res",
        "( ( ph /\\ ps ) -> ( ph /\\ ch ) )",
        s1,
        ref="imp",
        note="imp s1",
    )
    return lb.build(res)


def prove_ancl(sys: System) -> Proof:
    r"""ancl: ( ( ph -> ps ) -> ( ph -> ( ph /\ ps ) ) ).

    Conjoin antecedent with consequent.  (Contributed by NM, 5-Jan-1993.)
    """
    lb = ProofBuilder(sys, "ancl")
    s1 = lb.ref(
        "s1",
        r"( ph -> ( ps -> ( ph /\ ps ) ) )",
        ref="pm3.2",
        note="pm3.2",
    )
    res = lb.ref(
        "res",
        r"( ( ph -> ps ) -> ( ph -> ( ph /\ ps ) ) )",
        s1,
        ref="a2i",
        note="a2i s1",
    )
    return lb.build(res)


def prove_ancr(sys: System) -> Proof:
    """ancr: ( ( φ → ψ ) → ( φ → ( ψ ∧ φ ) ) ).

    Conjoin consequent to right.  (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "ancr")
    s1 = lb.ref(
        "s1",
        "φ → ( ψ → ( ψ ∧ φ ) )",
        ref="pm3.21",
        note="pm3.21",
    )
    res = lb.ref(
        "res",
        "( φ → ψ ) → ( φ → ( ψ ∧ φ ) )",
        s1,
        ref="a2i",
        note="a2i s1",
    )
    return lb.build(res)


def prove_ancrb(sys: System) -> Proof:
    """ancrb: ( ( φ → ψ ) ↔ ( φ → ( ψ ∧ φ ) ) ).

    Conjoin consequent to right with a biconditional.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "ancrb")
    s_iba = lb.ref(
        "s_iba",
        "φ → ( ψ ↔ ( ψ ∧ φ ) )",
        ref="iba",
        note="iba",
    )
    res = lb.ref(
        "res",
        "( ( φ → ψ ) ↔ ( φ → ( ψ ∧ φ ) ) )",
        s_iba,
        ref="pm5.74i",
        note="pm5.74i",
    )
    return lb.build(res)


def prove_anclb(sys: System) -> Proof:
    """anclb: ( ( φ → ψ ) ↔ ( φ → ( φ ∧ ψ ) ) ).

    Conjoin antecedent with consequent with a biconditional.
    (Contributed by NM, 5-Jan-1993.)
    """
    lb = ProofBuilder(sys, "anclb")
    s_ibar = lb.ref(
        "s_ibar",
        "φ → ( ψ ↔ ( φ ∧ ψ ) )",
        ref="ibar",
        note="ibar",
    )
    res = lb.ref(
        "res",
        "( ( φ → ψ ) ↔ ( φ → ( φ ∧ ψ ) ) )",
        s_ibar,
        ref="pm5.74i",
        note="pm5.74i",
    )
    return lb.build(res)


def prove_sylan9(sys: System) -> Proof:
    r"""sylan9: (φ ∧ θ) → (ψ → τ).

    Syllogism inference with importation.  If φ implies ψ implies χ,
    and θ implies χ implies τ, then φ and θ together imply
    ψ implies τ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sylan9")
    h1 = lb.hyp("sylan9.1", "φ → (ψ → χ)")
    h2 = lb.hyp("sylan9.2", "θ → (χ → τ)")
    s1 = lb.ref(
        "s1",
        "φ → (θ → (ψ → τ))",
        h1,
        h2,
        ref="syl9",
        note="syl9",
    )
    res = lb.ref(
        "res",
        "(φ ∧ θ) → (ψ → τ)",
        s1,
        ref="imp",
        note="imp",
    )
    return lb.build(res)


def prove_sylan9r(sys: System) -> Proof:
    r"""sylan9r: ( ( th /\ ph ) -> ( ps -> ta ) ).

    Syllogism inference with commuted antecedents. If ph implies ps implies ch,
    and th implies ch implies ta, then th and ph together imply ps implies ta.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sylan9r")
    h1 = lb.hyp("sylan9r.1", "ph -> ( ps -> ch )")
    h2 = lb.hyp("sylan9r.2", "th -> ( ch -> ta )")
    s1 = lb.ref(
        "s1",
        "th -> ( ph -> ( ps -> ta ) )",
        h1,
        h2,
        ref="syl9r",
        note="syl9r",
    )
    res = lb.ref(
        "res",
        "( th /\\ ph ) -> ( ps -> ta )",
        s1,
        ref="imp",
        note="imp",
    )
    return lb.build(res)


def prove_sylan9bb(sys: System) -> Proof:
    """sylan9bb: ( φ ∧ θ ) → ( ψ ↔ τ ).

    Syllogism inference with biconditional.  If φ → ( ψ ↔ χ ) and
    θ → ( χ ↔ τ ), then φ and θ together imply ψ ↔ τ .
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sylan9bb")
    h1 = lb.hyp("sylan9bb.1", "φ → ( ψ ↔ χ )")
    h2 = lb.hyp("sylan9bb.2", "θ → ( χ ↔ τ )")
    s1 = lb.ref(
        "s1",
        "( φ ∧ θ ) → ( ψ ↔ χ )",
        h1,
        ref="adantr",
        note="adantr",
    )
    s2 = lb.ref(
        "s2",
        "( φ ∧ θ ) → ( χ ↔ τ )",
        h2,
        ref="adantl",
        note="adantl",
    )
    res = lb.ref(
        "res",
        "( φ ∧ θ ) → ( ψ ↔ τ )",
        s1,
        s2,
        ref="bitrd",
        note="bitrd",
    )
    return lb.build(res)


def prove_sylan9bbr(sys: System) -> Proof:
    """sylan9bbr: ( θ ∧ φ ) → ( ψ ↔ τ ).

    Syllogism inference with biconditional, commuting the antecedent
    conjunction.  If φ → ( ψ ↔ χ ) and θ → ( χ ↔ τ ), then θ and φ
    together imply ψ ↔ τ .
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sylan9bbr")
    h1 = lb.hyp("sylan9bbr.1", "φ → ( ψ ↔ χ )")
    h2 = lb.hyp("sylan9bbr.2", "θ → ( χ ↔ τ )")
    s1 = lb.ref(
        "s1",
        "( φ ∧ θ ) → ( ψ ↔ τ )",
        h1,
        h2,
        ref="sylan9bb",
        note="sylan9bb",
    )
    res = lb.ref(
        "res",
        "( θ ∧ φ ) → ( ψ ↔ τ )",
        s1,
        ref="ancoms",
        note="ancoms",
    )
    return lb.build(res)


def prove_syl3an9b(sys: System) -> Proof:
    """syl3an9b: ( φ ∧ θ ∧ η ) → ( ψ ↔ ζ ).

    Syllogism inference with biconditional on three antecedents.
    If φ → ( ψ ↔ χ ), θ → ( χ ↔ τ ), and η → ( τ ↔ ζ ),
    then φ, θ, η together imply ψ ↔ ζ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "syl3an9b")
    h1 = lb.hyp("syl3an9b.1", "φ → ( ψ ↔ χ )")
    h2 = lb.hyp("syl3an9b.2", "θ → ( χ ↔ τ )")
    h3 = lb.hyp("syl3an9b.3", "η → ( τ ↔ ζ )")
    s1 = lb.ref(
        "s1",
        "( φ ∧ θ ) → ( ψ ↔ τ )",
        h1,
        h2,
        ref="sylan9bb",
        note="sylan9bb",
    )
    s2 = lb.ref(
        "s2",
        "( ( φ ∧ θ ) ∧ η ) → ( ψ ↔ ζ )",
        s1,
        h3,
        ref="sylan9bb",
        note="sylan9bb",
    )
    res = lb.ref(
        "res",
        "( φ ∧ θ ∧ η ) → ( ψ ↔ ζ )",
        s2,
        ref="3impa",
        note="3impa",
    )
    return lb.build(res)


def prove_syland(sys: System) -> Proof:
    r"""syland: ( ph -> ( ( ps /\ th ) -> ta ) ).

    Syllogism deduction with conjunction.  If ph implies ps implies ch,
    and ph implies ch and th together imply ta, then ph implies ps and th
    together imply ta.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "syland")
    h1 = lb.hyp("syland.1", "φ → ( ψ → χ )")
    h2 = lb.hyp("syland.2", "φ → ( ( χ ∧ θ ) → τ )")

    # expd: φ → (χ → (θ → τ))
    s1 = lb.ref(
        "s1",
        "φ → ( χ → ( θ → τ ) )",
        h2,
        ref="expd",
        note="expd syland.2",
    )

    # syld: φ → (ψ → (θ → τ))
    s2 = lb.ref(
        "s2",
        "φ → ( ψ → ( θ → τ ) )",
        h1,
        s1,
        ref="syld",
        note="syld",
    )

    # impd: φ → ((ψ ∧ θ) → τ)
    res = lb.ref(
        "res",
        "φ → ( ( ψ ∧ θ ) → τ )",
        s2,
        ref="impd",
        note="impd",
    )

    return lb.build(res)


def prove_syldan(sys: System) -> Proof:
    r"""syldan: ( φ ∧ ψ ) → θ.

    Syllogism deduction with common antecedent.  If φ ∧ ψ implies χ,
    and φ ∧ χ implies θ, then φ ∧ ψ implies θ.
    (Contributed by NM, 5-Jan-1993.)
    """
    lb = ProofBuilder(sys, "syldan")
    h1 = lb.hyp("syldan.1", "( φ ∧ ψ ) → χ")
    h2 = lb.hyp("syldan.2", "( φ ∧ χ ) → θ")

    s_simpl = lb.ref(
        "s_simpl",
        "( φ ∧ ψ ) → φ",
        ref="simpl",
        note="simpl",
    )

    res = lb.ref(
        "res",
        "( φ ∧ ψ ) → θ",
        s_simpl,
        h1,
        h2,
        ref="syl2anc",
        note="syl2anc",
    )

    return lb.build(res)


def prove_sylancom(sys: System) -> Proof:
    """sylancom: ( φ ∧ ψ ) → θ.

    Syllogism inference with commutation of conjunction.  If ( φ ∧ ψ ) → χ
    and ( χ ∧ ψ ) → θ, then ( φ ∧ ψ ) → θ.
    (Contributed by NM, 2-Jan-1993.)
    """
    lb = ProofBuilder(sys, "sylancom")
    h1 = lb.hyp("sylancom.1", "( φ ∧ ψ ) → χ")
    h2 = lb.hyp("sylancom.2", "( χ ∧ ψ ) → θ")

    s_simpr = lb.ref(
        "s_simpr",
        "( φ ∧ ψ ) → ψ",
        ref="simpr",
        note="simpr",
    )

    res = lb.ref(
        "res",
        "( φ ∧ ψ ) → θ",
        h1,
        s_simpr,
        h2,
        ref="syl2anc",
        note="syl2anc",
    )

    return lb.build(res)


def prove_sylan2(sys: System) -> Proof:
    """sylan2: (ψ ∧ φ) → θ.

    Syllogism inference with different antecedents.  If φ → χ and
    (ψ ∧ χ) → θ, then (ψ ∧ φ) → θ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sylan2")
    h1 = lb.hyp("sylan2.1", "φ → χ")
    h2 = lb.hyp("sylan2.2", "( ψ ∧ χ ) → θ")

    s1 = lb.ref(
        "s1",
        "( ψ ∧ φ ) → χ",
        h1,
        ref="adantl",
        note="adantl",
    )

    res = lb.ref(
        "res",
        "( ψ ∧ φ ) → θ",
        s1,
        h2,
        ref="syldan",
        note="syldan",
    )

    return lb.build(res)


def prove_sylan2d(sys: System) -> Proof:
    """sylan2d: φ → ((θ ∧ ψ) → τ).

    Deduction form of sylan2.  If φ implies ψ → χ and φ implies
    (θ ∧ χ) → τ, then φ implies (θ ∧ ψ) → τ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sylan2d")
    h1 = lb.hyp("sylan2d.1", "φ → ( ψ → χ )")
    h2 = lb.hyp("sylan2d.2", "φ → ( ( θ ∧ χ ) → τ )")

    s1 = lb.ref(
        "s1",
        "φ → ( ( χ ∧ θ ) → τ )",
        h2,
        ref="ancomsd",
        note="ancomsd",
    )

    s2 = lb.ref(
        "s2",
        "φ → ( ( ψ ∧ θ ) → τ )",
        h1,
        s1,
        ref="syland",
        note="syland",
    )

    res = lb.ref(
        "res",
        "φ → ( ( θ ∧ ψ ) → τ )",
        s2,
        ref="ancomsd",
        note="ancomsd",
    )

    return lb.build(res)


def prove_sylan2i(sys: System) -> Proof:
    """sylan2i: ψ → ((χ ∧ φ) → τ).

    Inference form of sylan2d.  If φ → θ and ψ → ((χ ∧ θ) → τ),
    then ψ → ((χ ∧ φ) → τ).
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sylan2i")
    h1 = lb.hyp("sylan2i.1", "φ → θ")
    h2 = lb.hyp("sylan2i.2", "ψ → ( ( χ ∧ θ ) → τ )")

    s1 = lb.ref(
        "s1",
        "ψ → ( φ → θ )",
        h1,
        ref="a1i",
        note="a1i sylan2i.1",
    )

    res = lb.ref(
        "res",
        "ψ → ( ( χ ∧ φ ) → τ )",
        s1,
        h2,
        ref="sylan2d",
        note="sylan2d",
    )

    return lb.build(res)


def prove_sylan2br(sys: System) -> Proof:
    """sylan2br: (ψ ∧ φ) → θ.

    Inference joining a biconditional with sylan2.  If χ ↔ φ and
    (ψ ∧ χ) → θ, then (ψ ∧ φ) → θ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sylan2br")
    h1 = lb.hyp("sylan2br.1", "( χ ↔ φ )")
    h2 = lb.hyp("sylan2br.2", "( ψ ∧ χ ) → θ")

    s1 = lb.ref(
        "s1",
        "φ → χ",
        h1,
        ref="biimpri",
        note="biimpri sylan2br.1",
    )

    res = lb.ref(
        "res",
        "( ψ ∧ φ ) → θ",
        s1,
        h2,
        ref="sylan2",
        note="sylan2",
    )

    return lb.build(res)


def prove_sylan2b(sys: System) -> Proof:
    """sylan2b: (ψ ∧ φ) → θ.

    Inference joining a biconditional with sylan2.  If φ ↔ χ and
    (ψ ∧ χ) → θ, then (ψ ∧ φ) → θ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sylan2b")
    h1 = lb.hyp("sylan2b.1", "( φ ↔ χ )")
    h2 = lb.hyp("sylan2b.2", "( ψ ∧ χ ) → θ")

    s1 = lb.ref(
        "s1",
        "φ → χ",
        h1,
        ref="biimpi",
        note="biimpi sylan2b.1",
    )

    res = lb.ref(
        "res",
        "( ψ ∧ φ ) → θ",
        s1,
        h2,
        ref="sylan2",
        note="sylan2",
    )

    return lb.build(res)


def prove_sylani(sys: System) -> Proof:
    r"""sylani: ( ps -> ( ( ph /\ th ) -> ta ) ).

    Inference associated with syland.  If ph implies ch and ps implies
    ch and th together imply ta, then ps implies ph and th together
    imply ta.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sylani")
    h1 = lb.hyp("sylani.1", "φ → χ")
    h2 = lb.hyp("sylani.2", "ψ → ( ( χ ∧ θ ) → τ )")

    # a1i: ψ → (φ → χ)
    s1 = lb.ref(
        "s1",
        "ψ → ( φ → χ )",
        h1,
        ref="a1i",
        note="a1i sylani.1",
    )

    # syland: ψ → ((φ ∧ θ) → τ)
    res = lb.ref(
        "res",
        "ψ → ( ( φ ∧ θ ) → τ )",
        s1,
        h2,
        ref="syland",
        note="syland",
    )

    return lb.build(res)


def prove_syl2ani(sys: System) -> Proof:
    """syl2ani: ψ → ((φ ∧ η) → τ).

    Inference associated with syl2an.  If φ → χ and η → θ and
    ψ → ((χ ∧ θ) → τ), then ψ → ((φ ∧ η) → τ).
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "syl2ani")
    h1 = lb.hyp("syl2ani.1", "φ → χ")
    h2 = lb.hyp("syl2ani.2", "η → θ")
    h3 = lb.hyp("syl2ani.3", "ψ → ( ( χ ∧ θ ) → τ )")

    # sylan2i: ψ → ((χ ∧ η) → τ)
    s1 = lb.ref(
        "s1",
        "ψ → ( ( χ ∧ η ) → τ )",
        h2,
        h3,
        ref="sylan2i",
        note="sylan2i",
    )

    # sylani: ψ → ((φ ∧ η) → τ)
    res = lb.ref(
        "res",
        "ψ → ( ( φ ∧ η ) → τ )",
        h1,
        s1,
        ref="sylani",
        note="sylani",
    )

    return lb.build(res)


def prove_bianbi(sys: System) -> Proof:
    """bianbi: φ ↔ ( θ ∧ χ ).

    Inference from a biconditional conjoined with a biconditional:
    from φ ↔ ( ψ ∧ χ ) and ψ ↔ θ, deduce φ ↔ ( θ ∧ χ ).
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "bianbi")
    h1 = lb.hyp("bianbi.1", "φ ↔ ( ψ ∧ χ )")
    h2 = lb.hyp("bianbi.2", "ψ ↔ θ")
    s1 = lb.ref("s1", "( ψ ∧ χ ) ↔ ( θ ∧ χ )", h2, ref="anbi1i", note="anbi1i")
    res = lb.ref("res", "φ ↔ ( θ ∧ χ )", h1, s1, ref="bitri", note="bitri")
    return lb.build(res)


def prove_biancomi(sys: System) -> Proof:
    """biancomi: φ ↔ ( ψ ∧ χ ).

    Inference from biconditional transitivity and conjunction
    commutativity: ( φ ↔ ( χ ∧ ψ ) ) implies ( φ ↔ ( ψ ∧ χ ) ).
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "biancomi")

    h1 = lb.hyp("biancomi.1", "( φ ↔ ( χ ∧ ψ ) )")

    s1 = lb.ref(
        "s1",
        "( ( χ ∧ ψ ) ↔ ( ψ ∧ χ ) )",
        ref="ancom",
        note="ancom",
    )

    s2 = lb.ref(
        "s2",
        "( ( ψ ∧ χ ) ↔ ( χ ∧ ψ ) )",
        s1,
        ref="bicomi",
        note="bicomi",
    )

    res = lb.ref(
        "res",
        "( φ ↔ ( ψ ∧ χ ) )",
        h1,
        s2,
        ref="bitr4i",
        note="bitr4i",
    )

    return lb.build(res)


def prove_anbi2ci(sys: System) -> Proof:
    """anbi2ci: ( φ ∧ χ ) ↔ ( χ ∧ ψ ).

    Commuted form of anbi1i — given φ ↔ ψ, conclude ( φ ∧ χ ) ↔ ( χ ∧ ψ ).
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "anbi2ci")
    h1 = lb.hyp("anbi.1", "φ ↔ ψ")
    s1 = lb.ref("s1", "( φ ∧ χ ) ↔ ( ψ ∧ χ )", h1, ref="anbi1i", note="anbi1i")
    res = lb.ref("res", "( φ ∧ χ ) ↔ ( χ ∧ ψ )", s1, ref="biancomi", note="biancomi")
    return lb.build(res)


def prove_anbi12ci(sys: System) -> Proof:
    """anbi12ci: ( φ ∧ χ ) ↔ ( θ ∧ ψ ).

    Commuted form of anbi12i — given φ ↔ ψ and χ ↔ θ,
    conclude ( φ ∧ χ ) ↔ ( θ ∧ ψ ).
    """
    lb = ProofBuilder(sys, "anbi12ci")
    h1 = lb.hyp("anbi12.1", "φ ↔ ψ")
    h2 = lb.hyp("anbi12.2", "χ ↔ θ")
    s1 = lb.ref("s1", "( φ ∧ χ ) ↔ ( ψ ∧ θ )", h1, h2, ref="anbi12i", note="anbi12i")
    res = lb.ref("res", "( φ ∧ χ ) ↔ ( θ ∧ ψ )", s1, ref="biancomi", note="biancomi")
    return lb.build(res)


def prove_anbi12d(sys: System) -> Proof:
    """anbi12d: φ → ( ( ψ ∧ θ ) ↔ ( χ ∧ τ ) ).

    Deduction joining two equivalences to form an equivalence of conjunctions.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "anbi12d")
    h1 = lb.hyp("anbi12d.1", "φ → ( ψ ↔ χ )")
    h2 = lb.hyp("anbi12d.2", "φ → ( θ ↔ τ )")

    s1 = lb.ref(
        "s1",
        "φ → ( ( ψ ∧ θ ) ↔ ( χ ∧ θ ) )",
        h1,
        ref="anbi1d",
        note="anbi1d",
    )

    s2 = lb.ref(
        "s2",
        "φ → ( ( χ ∧ θ ) ↔ ( χ ∧ τ ) )",
        h2,
        ref="anbi2d",
        note="anbi2d",
    )

    res = lb.ref(
        "res",
        "φ → ( ( ψ ∧ θ ) ↔ ( χ ∧ τ ) )",
        s1,
        s2,
        ref="bitrd",
        note="bitrd",
    )

    return lb.build(res)


def prove_anbi2d(sys: System) -> Proof:
    """anbi2d: φ → ( ( θ ∧ ψ ) ↔ ( θ ∧ χ ) ).

    Hyp: φ → ( ψ ↔ χ )
    Concl: φ → ( ( θ ∧ ψ ) ↔ ( θ ∧ χ ) )

    Deduction conjoining an antecedent to both sides of a biconditional.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "anbi2d")
    h1 = lb.hyp("anbid.1", "φ → ( ψ ↔ χ )")
    s1 = lb.ref(
        "s1",
        "φ → ( θ → ( ψ ↔ χ ) )",
        h1,
        ref="a1d",
        note="a1d anbid.1",
    )
    res = lb.ref(
        "res",
        "φ → ( ( θ ∧ ψ ) ↔ ( θ ∧ χ ) )",
        s1,
        ref="pm5.32d",
        note="pm5.32d",
    )
    return lb.build(res)


def prove_anbi2(sys: System) -> Proof:
    """anbi2: ( φ ↔ ψ ) → ( ( χ ∧ φ ) ↔ ( χ ∧ ψ ) ).

    Conjoin an antecedent to both sides of a biconditional, in closed form.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "anbi2")
    s_id = lb.ref(
        "s_id",
        "( φ ↔ ψ ) → ( φ ↔ ψ )",
        ref="id",
        note="id",
    )
    res = lb.ref(
        "res",
        "( φ ↔ ψ ) → ( ( χ ∧ φ ) ↔ ( χ ∧ ψ ) )",
        s_id,
        ref="anbi2d",
        note="anbi2d",
    )
    return lb.build(res)


def prove_biancomd(sys: System) -> Proof:
    """biancomd: φ → ( ψ ↔ ( χ ∧ θ ) ).

    Deduction form of biancomi — swap conjuncts in a biconditional
    under an implication.  Given φ → ( ψ ↔ ( θ ∧ χ ) ), conclude
    φ → ( ψ ↔ ( χ ∧ θ ) ).
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "biancomd")

    h1 = lb.hyp("biancomd.1", "φ → ( ψ ↔ ( θ ∧ χ ) )")

    s1 = lb.ref(
        "s1",
        "( θ ∧ χ ) ↔ ( χ ∧ θ )",
        ref="ancom",
        note="ancom",
    )

    res = lb.ref(
        "res",
        "φ → ( ψ ↔ ( χ ∧ θ ) )",
        h1,
        s1,
        ref="bitrdi",
        note="bitrdi",
    )

    return lb.build(res)


def prove_bian1d(sys: System) -> Proof:
    """bian1d: φ → ( ( χ ∧ ψ ) ↔ ( χ ∧ θ ) ).

    Deduction form: from φ → ( ψ ↔ ( χ ∧ θ ) ), derive that φ implies
    ( χ ∧ ψ ) is equivalent to ( χ ∧ θ ).
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "bian1d")
    h1 = lb.hyp("bian1d.1", "φ → ( ψ ↔ ( χ ∧ θ ) )")
    s_baibd = lb.ref(
        "s_baibd",
        "( φ ∧ χ ) → ( ψ ↔ θ )",
        h1,
        ref="baibd",
        note="baibd",
    )
    res = lb.ref(
        "res",
        "φ → ( ( χ ∧ ψ ) ↔ ( χ ∧ θ ) )",
        s_baibd,
        ref="pm5.32da",
        note="pm5.32da",
    )
    return lb.build(res)


def prove_bianfd(sys: System) -> Proof:
    """bianfd: φ → ( ψ ↔ ( ψ ∧ χ ) ).

    Deduction form: from a negated antecedent, derive a biconditional
    with the conjunction of that antecedent and an arbitrary consequent.
    (Contributed by NM, 5-Jan-1993.)
    """
    lb = ProofBuilder(sys, "bianfd")
    h1 = lb.hyp("bianfd.1", "φ → ¬ ψ")
    s1 = lb.ref("s1", "φ → ¬ ( ψ ∧ χ )", h1, ref="intnanrd", note="intnanrd")
    res = lb.ref("res", "φ → ( ψ ↔ ( ψ ∧ χ ) )", h1, s1, ref="2falsed", note="2falsed")
    return lb.build(res)


def prove_bianfi(sys: System) -> Proof:
    """bianfi: φ ↔ ( ψ ∧ φ ).

    Inference form of bianfd: from a negated antecedent, derive a
    biconditional with the conjunction of that antecedent and an
    arbitrary consequent.
    (Contributed by NM, 5-Jan-1993.)
    """
    lb = ProofBuilder(sys, "bianfi")
    h1 = lb.hyp("bianfi.1", "¬ φ")
    s1 = lb.ref("s1", "¬ ( ψ ∧ φ )", h1, ref="intnan", note="intnan")
    res = lb.ref("res", "φ ↔ ( ψ ∧ φ )", h1, s1, ref="2false", note="2false")
    return lb.build(res)


def prove_bianim(sys: System) -> Proof:
    """bianim: φ ↔ ( θ ∧ χ ).

    Inference form of biancomd: derive an equivalent biconditional
    with a permuted conjunction from two hypotheses.
    (Contributed by NM, 5-Jan-1993.)
    """
    lb = ProofBuilder(sys, "bianim")
    h1 = lb.hyp("bianim.1", "φ ↔ ( ψ ∧ χ )")
    h2 = lb.hyp("bianim.2", "χ → ( ψ ↔ θ )")

    # pm5.32ri: ( χ → ( ψ ↔ θ ) ) → ( ( ψ ∧ χ ) ↔ ( θ ∧ χ ) )
    s1 = lb.ref(
        "s1",
        "( ψ ∧ χ ) ↔ ( θ ∧ χ )",
        h2,
        ref="pm5.32ri",
        note="pm5.32ri",
    )

    # bitri: ( φ ↔ ( ψ ∧ χ ) ) , ( ( ψ ∧ χ ) ↔ ( θ ∧ χ ) ) → ( φ ↔ ( θ ∧ χ ) )
    res = lb.ref(
        "res",
        "φ ↔ ( θ ∧ χ )",
        h1,
        s1,
        ref="bitri",
        note="bitri",
    )

    return lb.build(res)


def prove_biantr(sys: System) -> Proof:
    r"""biantr: ( ( ( ph <-> ps ) /\ ( ch <-> ps ) ) -> ( ph <-> ch ) ).

    If two propositions are each equivalent to a third, then they are
    equivalent to each other.  (Contributed by NM, 18-Aug-1993.)
    """
    lb = ProofBuilder(sys, "biantr")

    # id: ( ( ch <-> ps ) -> ( ch <-> ps ) )
    s_id = lb.ref(
        "s_id",
        "( ( ch <-> ps ) -> ( ch <-> ps ) )",
        ref="id",
        note="id",
    )

    # bibi2d: ( ( ch <-> ps ) -> ( ( ph <-> ch ) <-> ( ph <-> ps ) ) )
    s_bibi2d = lb.ref(
        "s_bibi2d",
        "( ( ch <-> ps ) -> ( ( ph <-> ch ) <-> ( ph <-> ps ) ) )",
        s_id,
        ref="bibi2d",
        note="bibi2d",
    )

    # biimparc: ( ( ( ph <-> ps ) /\ ( ch <-> ps ) ) -> ( ph <-> ch ) )
    res = lb.ref(
        "res",
        r"( ( ( ph <-> ps ) /\ ( ch <-> ps ) ) -> ( ph <-> ch ) )",
        s_bibi2d,
        ref="biimparc",
        note="biimparc",
    )

    return lb.build(res)


def prove_biantru(sys: System) -> Proof:
    """biantru: ψ ↔ ( ψ ∧ φ ).  Hyp: φ.

    Introduce biconditional from an antecedent.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "biantru")
    h = lb.hyp("biantru.1", "φ")
    s_iba = lb.ref("s_iba", "φ → ( ψ ↔ ( ψ ∧ φ ) )", ref="iba", note="iba")
    res = lb.mp("res", h, s_iba, "ax-mp")
    return lb.build(res)


def prove_biantrur(sys: System) -> Proof:
    """biantrur: ψ ↔ ( φ ∧ ψ ).  Hyp: φ.

    Introduce biconditional from an antecedent (right conjunct).
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "biantrur")
    h = lb.hyp("biantrur.1", "φ")
    s_biantru = lb.ref("s_biantru", "( ψ ↔ ( ψ ∧ φ ) )", h, ref="biantru", note="biantru")
    res = lb.ref("res", "( ψ ↔ ( φ ∧ ψ ) )", s_biantru, ref="biancomi", note="biancomi")
    return lb.build(res)


def prove_biantrud(sys: System) -> Proof:
    """biantrud: φ → ( χ ↔ ( χ ∧ ψ ) ).  Hyp: φ → ψ.

    Biconditional and transitive implication deduction.
    (Contributed by NM, 21-Jun-1993.)
    """
    lb = ProofBuilder(sys, "biantrud")
    h = lb.hyp("biantrud.1", "φ → ψ")
    s_iba = lb.ref("s_iba", "ψ → ( χ ↔ ( χ ∧ ψ ) )", ref="iba", note="iba")
    res = lb.ref("res", "φ → ( χ ↔ ( χ ∧ ψ ) )", h, s_iba, ref="syl", note="syl")
    return lb.build(res)


def prove_biantrurd(sys: System) -> Proof:
    """biantrurd: φ → ( χ ↔ ( ψ ∧ χ ) ).  Hyp: φ → ψ.

    Biconditional and transitive implication deduction (right-hand side).
    (Contributed by NM, 21-Jun-1993.)
    """
    lb = ProofBuilder(sys, "biantrurd")
    h = lb.hyp("biantrud.1", "φ → ψ")
    s_ibar = lb.ref("s_ibar", "ψ → ( χ ↔ ( ψ ∧ χ ) )", ref="ibar", note="ibar")
    res = lb.ref("res", "φ → ( χ ↔ ( ψ ∧ χ ) )", h, s_ibar, ref="syl", note="syl")
    return lb.build(res)


def prove_3biant1d(sys: System) -> Proof:
    """3biant1d: φ → ( ( χ ∧ ψ ) ↔ ( θ ∧ χ ∧ ψ ) ).

    Biconditional and transitive implication deduction: from φ → θ, wrap
    a conjunction ( χ ∧ ψ ) with θ on the right, forming a triple
    conjunction.
    (Contributed by NM, 21-Jun-1993.)
    """
    lb = ProofBuilder(sys, "3biant1d")
    h = lb.hyp("3biantd.1", "φ → θ")

    # biantrurd: φ → ( ( χ ∧ ψ ) ↔ ( θ ∧ ( χ ∧ ψ ) ) )
    s_biantrurd = lb.ref(
        "s_biantrurd",
        "φ → ( ( χ ∧ ψ ) ↔ ( θ ∧ ( χ ∧ ψ ) ) )",
        h,
        ref="biantrurd",
        note="biantrurd",
    )

    # 3anass: ( θ ∧ χ ∧ ψ ) ↔ ( θ ∧ ( χ ∧ ψ ) )
    s_3anass = lb.ref(
        "s_3anass",
        "( θ /\\ χ /\\ ψ ) ↔ ( θ ∧ ( χ ∧ ψ ) )",
        ref="3anass",
        note="3anass",
    )

    # bitr4di: chain the two
    res = lb.ref(
        "res",
        "φ → ( ( χ ∧ ψ ) ↔ ( θ /\\ χ /\\ ψ ) )",
        s_biantrurd,
        s_3anass,
        ref="bitr4di",
        note="bitr4di",
    )

    return lb.build(res)


def prove_bi2bian9(sys: System) -> Proof:
    """bi2bian9: ( φ ∧ θ ) → ( ( ψ ↔ τ ) ↔ ( χ ↔ η ) ).

    From two biconditional hypotheses, deduce a biconditional equivalence
    under a common conjunction antecedent.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "bi2bian9")
    h1 = lb.hyp("bi2an9.1", "φ → ( ψ ↔ χ )")
    h2 = lb.hyp("bi2an9.2", "θ → ( τ ↔ η )")

    s1 = lb.ref(
        "s1",
        "( φ ∧ θ ) → ( ψ ↔ χ )",
        h1,
        ref="adantr",
        note="adantr",
    )

    s2 = lb.ref(
        "s2",
        "( φ ∧ θ ) → ( τ ↔ η )",
        h2,
        ref="adantl",
        note="adantl",
    )

    res = lb.ref(
        "res",
        "( φ ∧ θ ) → ( ( ψ ↔ τ ) ↔ ( χ ↔ η ) )",
        s1,
        s2,
        ref="bibi12d",
        note="bibi12d",
    )

    return lb.build(res)


def prove_bianir(sys: System) -> Proof:
    r"""bianir: ( ( ph /\ ( ps <-> ph ) ) -> ps ).

    A nested biconditional inside an antecedent: from ph and (ps <-> ph),
    deduce ps.  (Contributed by NM, 30-Sep-1992.)
    """
    lb = ProofBuilder(sys, "bianir")

    # biimpr: ( ( ps <-> ph ) -> ( ph -> ps ) )
    s_biimpr = lb.ref(
        "s_biimpr",
        "( ( ps <-> ph ) -> ( ph -> ps ) )",
        ref="biimpr",
        note="biimpr",
    )

    # impcom: ( ( ph /\ ( ps <-> ph ) ) -> ps )
    res = lb.ref(
        "res",
        r"( ( ph /\ ( ps <-> ph ) ) -> ps )",
        s_biimpr,
        ref="impcom",
        note="impcom",
    )
    return lb.build(res)


def prove_bianass(sys: System) -> Proof:
    """bianass: ( ( η ∧ φ ) ↔ ( ( η ∧ ψ ) ∧ χ ) ).

    Inference adding a left conjunct to a biconditional, with
    rearrangement.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "bianass")
    h1 = lb.hyp("bianass.1", "φ ↔ ( ψ ∧ χ )")
    s1 = lb.ref(
        "s1",
        "( η ∧ φ ) ↔ ( η ∧ ( ψ ∧ χ ) )",
        h1,
        ref="anbi2i",
        note="anbi2i",
    )
    s2 = lb.ref(
        "s2",
        "( ( η ∧ ψ ) ∧ χ ) ↔ ( η ∧ ( ψ ∧ χ ) )",
        ref="anass",
        note="anass",
    )
    res = lb.ref(
        "res",
        "( ( η ∧ φ ) ↔ ( ( η ∧ ψ ) ∧ χ ) )",
        s1,
        s2,
        ref="bitr4i",
        note="bitr4i",
    )
    return lb.build(res)


def prove_bianassc(sys: System) -> Proof:
    r"""bianassc: ( η ∧ φ ) ↔ ( ( ψ ∧ η ) ∧ χ ).

    Commuted form of bianass — swap the conjuncts in the second
    antecedent of the biconditional.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "bianassc")
    h1 = lb.hyp("bianass.1", "φ ↔ ( ψ ∧ χ )")
    s1 = lb.ref(
        "s1",
        "( η ∧ φ ) ↔ ( ( η ∧ ψ ) ∧ χ )",
        h1,
        ref="bianass",
        note="bianass",
    )
    s2 = lb.ref(
        "s2",
        "( η ∧ ψ ) ↔ ( ψ ∧ η )",
        ref="ancom",
        note="ancom",
    )
    res = lb.ref(
        "res",
        "( η ∧ φ ) ↔ ( ( ψ ∧ η ) ∧ χ )",
        s1,
        s2,
        ref="bianbi",
        note="bianbi",
    )
    return lb.build(res)


def prove_orcanai(sys: System) -> Proof:
    r"""orcanai: ( ( ph /\ -. ps ) -> ch ).

    From ph -> (ps \/ ch) infer (ph /\ -. ps) -> ch.
    (Contributed by NM, 29-Dec-1992.)
    """
    lb = ProofBuilder(sys, "orcanai")
    h1 = lb.hyp("orcanai.1", "( ph -> ( ps \\/ ch ) )")
    s1 = lb.ref("s1", "( ph -> ( -. ps -> ch ) )", h1, ref="ord", note="ord orcanai.1")
    res = lb.ref("res", "( ( ph /\\ -. ps ) -> ch )", s1, ref="imp", note="imp s1")
    return lb.build(res)


def prove_pm3_3(sys: System) -> Proof:
    r"""pm3.3: ( ( ( ph /\ ps ) -> ch ) -> ( ph -> ( ps -> ch ) ) ).

    Exportation.  (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "pm3.3")
    s1 = lb.ref(
        "s1",
        r"( ( ph /\ ps ) -> ch ) -> ( ( ph /\ ps ) -> ch )",
        ref="id",
        note="id",
    )
    res = lb.ref(
        "res",
        r"( ( ph /\ ps ) -> ch ) -> ( ph -> ( ps -> ch ) )",
        s1,
        ref="expd",
        note="expd",
    )
    return lb.build(res)


def prove_impexp(sys: System) -> Proof:
    r"""impexp: ( ( ( ph /\ ps ) -> ch ) <-> ( ph -> ( ps -> ch ) ) ).

    Import-export theorem.  If ph and ps together imply ch, then ph implies
    that ps implies ch, and vice versa.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "impexp")
    pm33 = lb.ref(
        "pm33",
        r"( ( ( ph /\ ps ) -> ch ) -> ( ph -> ( ps -> ch ) ) )",
        ref="pm3.3",
        note="pm3.3",
    )
    pm331 = lb.ref(
        "pm331",
        r"( ( ph -> ( ps -> ch ) ) -> ( ( ph /\ ps ) -> ch ) )",
        ref="pm3.31",
        note="pm3.31",
    )
    res = lb.ref(
        "res",
        r"( ( ( ph /\ ps ) -> ch ) <-> ( ph -> ( ps -> ch ) ) )",
        pm33,
        pm331,
        ref="impbii",
        note="impbii",
    )
    return lb.build(res)


def prove_ad5ant125OLD(sys: System) -> Proof:
    r"""ad5ant125OLD: ( ( ( ( ( ph /\ ps ) /\ ta ) /\ et ) /\ ch ) -> th ).

    Deduction adding two conjuncts to the antecedent.
    Given ( ( ph /\ ps /\ ch ) -> th ), derive
    ( ( ( ( ( ph /\ ps ) /\ ta ) /\ et ) /\ ch ) -> th ).
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "ad5ant125OLD")
    h1 = lb.hyp("ad5ant.1", r"( ph /\ ps /\ ch ) -> th")

    # 3expia: ( ( ph /\ ps /\ ch ) -> th ) → ( ( ph /\ ps ) -> ( ch -> th ) )
    s1 = lb.ref(
        "s1",
        r"( ( ph /\ ps ) -> ( ch -> th ) )",
        h1,
        ref="3expia",
        note="3expia ad5ant.1",
    )

    # 2a1d: ( ( ph /\ ps ) -> ( ch -> th ) ) → ( ( ph /\ ps ) -> ( ta -> ( et -> ( ch -> th ) ) ) )
    s2 = lb.ref(
        "s2",
        r"( ( ph /\ ps ) -> ( ta -> ( et -> ( ch -> th ) ) ) )",
        s1,
        ref="2a1d",
        note="2a1d s1",
    )

    # imp41: ( ( ph /\ ps ) -> ( ta -> ( et -> ( ch -> th ) ) ) )
    #     → ( ( ( ( ( ph /\ ps ) /\ ta ) /\ et ) /\ ch ) -> th )
    res = lb.ref(
        "res",
        r"( ( ( ( ( ph /\ ps ) /\ ta ) /\ et ) /\ ch ) -> th )",
        s2,
        ref="imp41",
        note="imp41 s2",
    )

    return lb.build(res)


def prove_expimpd(sys: System) -> Proof:
    r"""expimpd: ( ph -> ( ( ps /\ ch ) -> th ) ).

    Hyp: expimpd.1 |- ( ( ph /\ ps ) -> ( ch -> th ) )
    Concl: |- ( ph -> ( ( ps /\ ch ) -> th ) )

    Exportation followed by importation.  (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "expimpd")
    h1 = lb.hyp("expimpd.1", "( ( ph /\\ ps ) -> ( ch -> th ) )")
    s1 = lb.ref("s1", "ph -> ( ps -> ( ch -> th ) )", h1, ref="ex", note="ex expimpd.1")
    res = lb.ref("res", "( ph -> ( ( ps /\\ ch ) -> th ) )", s1, ref="impd", note="impd s1")
    return lb.build(res)


def prove_pm5_1(sys: System) -> Proof:
    r"""pm5.1: ( ( ph /\ ps ) -> ( ph <-> ps ) ).

    From two true statements, deduce their equivalence.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm5.1")

    # pm5.501: ( ph -> ( ps <-> ( ph <-> ps ) ) )
    pm5_501 = lb.ref(
        "pm5_501",
        "( ph -> ( ps <-> ( ph <-> ps ) ) )",
        ref="pm5.501",
        note="pm5.501",
    )

    # biimpa: from pm5.501, deduce ( ( ph /\ ps ) -> ( ph <-> ps ) )
    res = lb.ref(
        "res",
        "( ( ph /\\ ps ) -> ( ph <-> ps ) )",
        pm5_501,
        ref="biimpa",
        note="biimpa",
    )

    return lb.build(res)


def prove_pm5_3(sys: System) -> Proof:
    """pm5.3: ( ( φ ∧ ψ ) → χ ) ↔ ( ( φ ∧ ψ ) → ( φ ∧ χ ) ).

    Conjoin an implication's antecedent with one of its consequent conjuncts.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm5.3")

    # simpl: ( φ ∧ ψ ) → φ
    s_simpl = lb.ref(
        "s_simpl",
        "( φ ∧ ψ ) → φ",
        ref="simpl",
        note="simpl",
    )

    # biantrurd: ( ( φ ∧ ψ ) → ( χ ↔ ( φ ∧ χ ) ) )
    s_biantrurd = lb.ref(
        "s_biantrurd",
        "( ( φ ∧ ψ ) → ( χ ↔ ( φ ∧ χ ) ) )",
        s_simpl,
        ref="biantrurd",
        note="biantrurd",
    )

    # pm5.74i: ( ( φ ∧ ψ ) → χ ) ↔ ( ( φ ∧ ψ ) → ( φ ∧ χ ) )
    res = lb.ref(
        "res",
        "( ( ( φ ∧ ψ ) → χ ) ↔ ( ( φ ∧ ψ ) → ( φ ∧ χ ) ) )",
        s_biantrurd,
        ref="pm5.74i",
        note="pm5.74i",
    )

    return lb.build(res)


def prove_pm5_35(sys: System) -> Proof:
    """pm5.35: ( ( φ → ψ ) ∧ ( φ → χ ) ) → ( φ → ( ψ ↔ χ ) ).

    Two implications with the same antecedent imply the equivalence
    of their consequents under that antecedent.
    (Contributed by BJ, 19-Jul-2023.)  (Proof shortened by BJ, 1-Sep-2024.)
    """
    lb = ProofBuilder(sys, "pm5.35")

    # pm5.1: ( ( ( φ → ψ ) ∧ ( φ → χ ) ) → ( ( φ → ψ ) ↔ ( φ → χ ) ) )
    s1 = lb.ref(
        "s1",
        "( ( ( φ → ψ ) ∧ ( φ → χ ) ) → ( ( φ → ψ ) ↔ ( φ → χ ) ) )",
        ref="pm5.1",
        note="pm5.1",
    )

    # pm5.74rd: from s1, deduce ( ( ( φ → ψ ) ∧ ( φ → χ ) ) → ( φ → ( ψ ↔ χ ) ) )
    res = lb.ref(
        "res",
        "( ( ( φ → ψ ) ∧ ( φ → χ ) ) → ( φ → ( ψ ↔ χ ) ) )",
        s1,
        ref="pm5.74rd",
        note="pm5.74rd",
    )

    return lb.build(res)


def prove_intnanr(sys: System) -> Proof:
    """intnanr: ¬ ( φ ∧ ψ ).

    Inference introducing a negated right conjunct from a negated left conjunct.
    (Contributed by NM, 5-Jan-1993.)
    """
    lb = ProofBuilder(sys, "intnanr")
    h1 = lb.hyp("intnan.1", "¬ φ")
    s1 = lb.ref("s1", "( φ ∧ ψ ) → φ", ref="simpl", note="simpl")
    res = lb.ref("res", "¬ ( φ ∧ ψ )", h1, s1, ref="mto", note="mto")
    return lb.build(res)


def prove_intnan(sys: System) -> Proof:
    """intnan: ¬ ( ψ ∧ φ ).

    Inference introducing a negated conjunction from a negated right conjunct.
    (Contributed by NM, 5-Jan-1993.)
    """
    lb = ProofBuilder(sys, "intnan")
    h1 = lb.hyp("intnan.1", "¬ φ")
    s1 = lb.ref("s1", "( ψ ∧ φ ) → φ", ref="simpr", note="simpr")
    res = lb.ref("res", "¬ ( ψ ∧ φ )", h1, s1, ref="mto", note="mto")
    return lb.build(res)


def prove_intnanrd(sys: System) -> Proof:
    """intnanrd: φ → ¬ ( ψ ∧ χ ).

    Deduction form of intnanr: introduce a negated conjunction from a
    negated left conjunct.
    (Contributed by NM, 5-Jan-1993.)
    """
    lb = ProofBuilder(sys, "intnanrd")
    h1 = lb.hyp("intnand.1", "φ → ¬ ψ")
    s1 = lb.ref("s1", "( ψ ∧ χ ) → ψ", ref="simpl", note="simpl")
    res = lb.ref("res", "φ → ¬ ( ψ ∧ χ )", h1, s1, ref="nsyl", note="nsyl")
    return lb.build(res)


def prove_intnand(sys: System) -> Proof:
    """intnand: φ → ¬ ( χ ∧ ψ ).

    Introduce a negated conjunction from a negated right conjunct.
    (Contributed by NM, 5-Jan-1993.)
    """
    lb = ProofBuilder(sys, "intnand")
    h1 = lb.hyp("intnand.1", "φ → ¬ ψ")
    s1 = lb.ref("s1", "( χ ∧ ψ ) → ψ", ref="simpr", note="simpr")
    res = lb.ref("res", "φ → ¬ ( χ ∧ ψ )", h1, s1, ref="nsyl", note="nsyl")
    return lb.build(res)


def prove_simprrr(sys: System) -> Proof:
    """simprrr: ( φ ∧ ( ψ ∧ ( χ ∧ θ ) ) ) → θ.

    Simplify a nested conjunction to the inner right conjunct.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "simprrr")
    s1 = lb.ref("s1", "( χ ∧ θ ) → θ", ref="simpr", note="simpr")
    res = lb.ref("res", "( φ ∧ ( ψ ∧ ( χ ∧ θ ) ) ) → θ", s1, ref="ad2antll", note="ad2antll")
    return lb.build(res)


def prove_simprrl(sys: System) -> Proof:
    """simprrl: ( φ ∧ ( ψ ∧ ( χ ∧ θ ) ) ) → χ.

    Simplify a nested conjunction to the inner left conjunct.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "simprrl")
    s1 = lb.ref("s1", "( χ ∧ θ ) → χ", ref="simpl", note="simpl")
    res = lb.ref("res", "( φ ∧ ( ψ ∧ ( χ ∧ θ ) ) ) → χ", s1, ref="ad2antll", note="ad2antll")
    return lb.build(res)


def prove_simprll(sys: System) -> Proof:
    """simprll: ( φ ∧ ( ( ψ ∧ χ ) ∧ θ ) ) → ψ.

    Simplify a nested conjunction to the inner left conjunct.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "simprll")
    s1 = lb.ref("s1", "( ψ ∧ χ ) → ψ", ref="simpl", note="simpl")
    res = lb.ref("res", "( φ ∧ ( ( ψ ∧ χ ) ∧ θ ) ) → ψ", s1, ref="ad2antrl", note="ad2antrl")
    return lb.build(res)


def prove_simprlr(sys: System) -> Proof:
    """simprlr: ( φ ∧ ( ( ψ ∧ χ ) ∧ θ ) ) → χ.

    Simplify a nested conjunction to the inner right conjunct.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "simprlr")
    s1 = lb.ref("s1", "( ψ ∧ χ ) → χ", ref="simpr", note="simpr")
    res = lb.ref("res", "( φ ∧ ( ( ψ ∧ χ ) ∧ θ ) ) → χ", s1, ref="ad2antrl", note="ad2antrl")
    return lb.build(res)


def prove_ancomst(sys: System) -> Proof:
    """ancomst: ( ( φ ∧ ψ ) → χ ) ↔ ( ( ψ ∧ φ ) → χ ).

    Swap the two conjuncts in an implication antecedent.
    (Contributed by NM, 29-Dec-1992.)
    """
    lb = ProofBuilder(sys, "ancomst")
    s1 = lb.ref("s1", "( φ ∧ ψ ) ↔ ( ψ ∧ φ )", ref="ancom", note="ancom")
    res = lb.ref("res", "( ( φ ∧ ψ ) → χ ) ↔ ( ( ψ ∧ φ ) → χ )", s1, ref="imbi1i", note="imbi1i")
    return lb.build(res)


def prove_syl2an2(sys: System) -> Proof:
    """syl2an2: ( χ ∧ φ ) → τ.

    Syllogism inference with two different antecedents.
    (Contributed by NM, 25-May-1999.)
    """
    lb = ProofBuilder(sys, "syl2an2")
    h1 = lb.hyp("syl2an2.1", "φ → ψ")
    h2 = lb.hyp("syl2an2.2", "( χ ∧ φ ) → θ")
    h3 = lb.hyp("syl2an2.3", "( ψ ∧ θ ) → τ")
    s1 = lb.ref("s1", "( χ ∧ φ ) → ψ", h1, ref="adantl", note="adantl")
    res = lb.ref("res", "( χ ∧ φ ) → τ", s1, h2, h3, ref="syl2anc", note="syl2anc")
    return lb.build(res)


def prove_pm5_31(sys: System) -> Proof:
    r"""pm5.31: ( χ ∧ ( φ → ψ ) ) → ( φ → ( ψ ∧ χ ) ).

    From a conjunction of χ and φ → ψ, derive φ → ( ψ ∧ χ ).
    (Contributed by NM, 5-Jan-1993.)
    """
    lb = ProofBuilder(sys, "pm5.31")
    s1 = lb.ref("s1", "( χ ∧ ( φ → ψ ) ) → ( φ → ψ )", ref="simpr", note="simpr")
    s2 = lb.ref("s2", "( χ ∧ ( φ → ψ ) ) → χ", ref="simpl", note="simpl")
    res = lb.ref(
        "res",
        "( χ ∧ ( φ → ψ ) ) → ( φ → ( ψ ∧ χ ) )",
        s1,
        s2,
        ref="jctird",
        note="jctird",
    )
    return lb.build(res)


def prove_pm5_32(sys: System) -> Proof:
    """pm5.32: ( φ → ( ψ ↔ χ ) ) ↔ ( ( φ ∧ ψ ) ↔ ( φ ∧ χ ) ).

    Distribution of implication over biconditional with conjunction.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm5.32")

    # notbi: ( ψ ↔ χ ) ↔ ( ¬ ψ ↔ ¬ χ )
    s_notbi = lb.ref(
        "s_notbi",
        "( ψ ↔ χ ) ↔ ( ¬ ψ ↔ ¬ χ )",
        ref="notbi",
        note="notbi",
    )

    # imbi2i: ( φ → ( ψ ↔ χ ) ) ↔ ( φ → ( ¬ ψ ↔ ¬ χ ) )
    s_imbi2i = lb.ref(
        "s_imbi2i",
        "( φ → ( ψ ↔ χ ) ) ↔ ( φ → ( ¬ ψ ↔ ¬ χ ) )",
        s_notbi,
        ref="imbi2i",
        note="imbi2i",
    )

    # pm5.74: ( φ → ( ¬ ψ ↔ ¬ χ ) ) ↔ ( ( φ → ¬ ψ ) ↔ ( φ → ¬ χ ) )
    s_pm574 = lb.ref(
        "s_pm574",
        "( φ → ( ¬ ψ ↔ ¬ χ ) ) ↔ ( ( φ → ¬ ψ ) ↔ ( φ → ¬ χ ) )",
        ref="pm5.74",
        note="pm5.74",
    )

    # notbi: ( ( φ → ¬ ψ ) ↔ ( φ → ¬ χ ) ) ↔ ( ¬ ( φ → ¬ ψ ) ↔ ¬ ( φ → ¬ χ ) )
    s_notbi2 = lb.ref(
        "s_notbi2",
        "( ( φ → ¬ ψ ) ↔ ( φ → ¬ χ ) ) ↔ ( ¬ ( φ → ¬ ψ ) ↔ ¬ ( φ → ¬ χ ) )",
        ref="notbi",
        note="notbi",
    )

    # 3bitri: chain s_imbi2i, s_pm574, s_notbi2
    # → ( φ → ( ψ ↔ χ ) ) ↔ ( ¬ ( φ → ¬ ψ ) ↔ ¬ ( φ → ¬ χ ) )
    s_3bitri = lb.ref(
        "s_3bitri",
        "( φ → ( ψ ↔ χ ) ) ↔ ( ¬ ( φ → ¬ ψ ) ↔ ¬ ( φ → ¬ χ ) )",
        s_imbi2i,
        s_pm574,
        s_notbi2,
        ref="3bitri",
        note="3bitri",
    )

    # df-an: ( φ ∧ ψ ) ↔ ¬ ( φ → ¬ ψ )
    s_dfan_ps = lb.ref(
        "s_dfan_ps",
        "( φ ∧ ψ ) ↔ ¬ ( φ → ¬ ψ )",
        ref="df-an",
        note="df-an",
    )

    # df-an: ( φ ∧ χ ) ↔ ¬ ( φ → ¬ χ )
    s_dfan_ch = lb.ref(
        "s_dfan_ch",
        "( φ ∧ χ ) ↔ ¬ ( φ → ¬ χ )",
        ref="df-an",
        note="df-an",
    )

    # bibi12i: ( ( φ ∧ ψ ) ↔ ( φ ∧ χ ) ) ↔ ( ¬ ( φ → ¬ ψ ) ↔ ¬ ( φ → ¬ χ ) )
    s_bibi12i = lb.ref(
        "s_bibi12i",
        "( ( φ ∧ ψ ) ↔ ( φ ∧ χ ) ) ↔ ( ¬ ( φ → ¬ ψ ) ↔ ¬ ( φ → ¬ χ ) )",
        s_dfan_ps,
        s_dfan_ch,
        ref="bibi12i",
        note="bibi12i",
    )

    # bitr4i: ( φ → ( ψ ↔ χ ) ) ↔ ( ( φ ∧ ψ ) ↔ ( φ ∧ χ ) )
    res = lb.ref(
        "res",
        "( φ → ( ψ ↔ χ ) ) ↔ ( ( φ ∧ ψ ) ↔ ( φ ∧ χ ) )",
        s_3bitri,
        s_bibi12i,
        ref="bitr4i",
        note="bitr4i",
    )

    return lb.build(res)


def prove_pm5_32d(sys: System) -> Proof:
    """pm5.32d: φ → ( ( ψ ∧ χ ) ↔ ( ψ ∧ θ ) ).

    Hyp 1: φ → ( ψ → ( χ ↔ θ ) )
    Concl: φ → ( ( ψ ∧ χ ) ↔ ( ψ ∧ θ ) )

    Deduction form of pm5.32.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm5.32d")
    h1 = lb.hyp("pm5.32d.1", "φ → ( ψ → ( χ ↔ θ ) )")
    s1 = lb.ref(
        "s1",
        "( ψ → ( χ ↔ θ ) ) ↔ ( ( ψ ∧ χ ) ↔ ( ψ ∧ θ ) )",
        ref="pm5.32",
        note="pm5.32",
    )
    res = lb.ref(
        "res",
        "φ → ( ( ψ ∧ χ ) ↔ ( ψ ∧ θ ) )",
        h1,
        s1,
        ref="sylib",
        note="sylib",
    )
    return lb.build(res)


def prove_pm5_32da(sys: System) -> Proof:
    """pm5.32da: φ → ( ( ψ ∧ χ ) ↔ ( ψ ∧ θ ) ).

    Hyp: ( ( φ ∧ ψ ) → ( χ ↔ θ ) ).
    Deduction form of pm5.32 with differently ordered antecedents.
    (Contributed by NM, 29-Mar-1997.)

    Proof: apply ex to the hypothesis to get φ → ( ψ → ( χ ↔ θ ) ),
    then pm5.32d to get the conclusion.
    """
    lb = ProofBuilder(sys, "pm5.32da")
    h1 = lb.hyp("pm5.32da.1", "( ( φ ∧ ψ ) → ( χ ↔ θ ) )")
    s1 = lb.ref("s1", "φ → ( ψ → ( χ ↔ θ ) )", h1, ref="ex", note="ex")
    res = lb.ref("res", "φ → ( ( ψ ∧ χ ) ↔ ( ψ ∧ θ ) )", s1, ref="pm5.32d", note="pm5.32d")
    return lb.build(res)


def prove_pm5_32i(sys: System) -> Proof:
    """pm5.32i: ( φ ∧ ψ ) ↔ ( φ ∧ χ ).

    Inference form of pm5.32.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm5.32i")
    h1 = lb.hyp("pm5.32i.1", "φ → ( ψ ↔ χ )")
    s1 = lb.ref(
        "s1",
        "( φ → ( ψ ↔ χ ) ) ↔ ( ( φ ∧ ψ ) ↔ ( φ ∧ χ ) )",
        ref="pm5.32",
        note="pm5.32",
    )
    res = lb.ref(
        "res",
        "( φ ∧ ψ ) ↔ ( φ ∧ χ )",
        h1,
        s1,
        ref="mpbi",
        note="mpbi",
    )
    return lb.build(res)


def prove_pm5_33(sys: System) -> Proof:
    """pm5.33: ( φ ∧ ( ψ → χ ) ) ↔ ( φ ∧ ( ( φ ∧ ψ ) → χ ) ).

    Equivalence of two forms involving conjunction and implication.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm5.33")

    # ibar: φ → ( ψ ↔ ( φ ∧ ψ ) )
    s1 = lb.ref(
        "s1",
        "( φ → ( ψ ↔ ( φ ∧ ψ ) ) )",
        ref="ibar",
        note="ibar",
    )

    # imbi1d: φ → ( ( ψ → χ ) ↔ ( ( φ ∧ ψ ) → χ ) )
    s2 = lb.ref(
        "s2",
        "( φ → ( ( ψ → χ ) ↔ ( ( φ ∧ ψ ) → χ ) ) )",
        s1,
        ref="imbi1d",
        note="imbi1d",
    )

    # pm5.32i: ( φ ∧ ( ψ → χ ) ) ↔ ( φ ∧ ( ( φ ∧ ψ ) → χ ) )
    res = lb.ref(
        "res",
        "( φ ∧ ( ψ → χ ) ) ↔ ( φ ∧ ( ( φ ∧ ψ ) → χ ) )",
        s2,
        ref="pm5.32i",
        note="pm5.32i",
    )

    return lb.build(res)


def prove_pm5_32ri(sys: System) -> Proof:
    """pm5.32ri: ( ψ ∧ φ ) ↔ ( χ ∧ φ ).

    Inference form of pm5.32r.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm5.32ri")
    h1 = lb.hyp("pm5.32ri.1", "φ → ( ψ ↔ χ )")

    # pm5.32i: ( φ ∧ ψ ) ↔ ( φ ∧ χ )
    s1 = lb.ref(
        "s1",
        "( φ ∧ ψ ) ↔ ( φ ∧ χ )",
        h1,
        ref="pm5.32i",
        note="pm5.32i",
    )

    # ancom: ( ψ ∧ φ ) ↔ ( φ ∧ ψ )
    s2 = lb.ref(
        "s2",
        "( ψ ∧ φ ) ↔ ( φ ∧ ψ )",
        ref="ancom",
        note="ancom",
    )

    # ancom: ( χ ∧ φ ) ↔ ( φ ∧ χ )
    s3 = lb.ref(
        "s3",
        "( χ ∧ φ ) ↔ ( φ ∧ χ )",
        ref="ancom",
        note="ancom",
    )

    # 3bitr4i: combine s1, s2, s3
    res = lb.ref(
        "res",
        "( ψ ∧ φ ) ↔ ( χ ∧ φ )",
        s1,
        s2,
        s3,
        ref="3bitr4i",
        note="3bitr4i",
    )

    return lb.build(res)


def prove_pm5_32rd(sys: System) -> Proof:
    """pm5.32rd: φ → ( ( χ ∧ ψ ) ↔ ( θ ∧ ψ ) ).

    Deduction form of pm5.32r: distribute a conjunct over a
    biconditional in an antecedent.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm5.32rd")
    h1 = lb.hyp("pm5.32rd.1", "φ → ( ψ → ( χ ↔ θ ) )")

    # pm5.32d: φ → ( ( ψ ∧ χ ) ↔ ( ψ ∧ θ ) )
    s1 = lb.ref(
        "s1",
        "φ → ( ( ψ ∧ χ ) ↔ ( ψ ∧ θ ) )",
        h1,
        ref="pm5.32d",
        note="pm5.32d",
    )

    # ancom: ( χ ∧ ψ ) ↔ ( ψ ∧ χ )
    s2 = lb.ref(
        "s2",
        "( χ ∧ ψ ) ↔ ( ψ ∧ χ )",
        ref="ancom",
        note="ancom",
    )

    # ancom: ( θ ∧ ψ ) ↔ ( ψ ∧ θ )
    s3 = lb.ref(
        "s3",
        "( θ ∧ ψ ) ↔ ( ψ ∧ θ )",
        ref="ancom",
        note="ancom",
    )

    # 3bitr4g: combine s1, s2, s3
    res = lb.ref(
        "res",
        "φ → ( ( χ ∧ ψ ) ↔ ( θ ∧ ψ ) )",
        s1,
        s2,
        s3,
        ref="3bitr4g",
        note="3bitr4g",
    )

    return lb.build(res)


def prove_biadaniALT(sys: System) -> Proof:
    """biadaniALT: ( ψ → ( φ ↔ χ ) ) ↔ ( φ ↔ ( ψ ∧ χ ) ).

    Alternate proof of biadani — equivalence between implication of a
    biconditional and a biconditional with a conjunction.
    (Contributed by NM, 5-Aug-1993.)
    (Proof modification is discouraged.)  (New usage is discouraged.)
    """
    lb = ProofBuilder(sys, "biadaniALT")
    h1 = lb.hyp("biadani.1", "φ → ψ")

    # pm5.32: ( φ → ( ψ ↔ χ ) ) ↔ ( ( φ ∧ ψ ) ↔ ( φ ∧ χ ) )
    # [ψ/φ, φ/ψ, χ/χ]: ( ψ → ( φ ↔ χ ) ) ↔ ( ( ψ ∧ φ ) ↔ ( ψ ∧ χ ) )
    s1 = lb.ref(
        "s1",
        "( ψ → ( φ ↔ χ ) ) ↔ ( ( ψ ∧ φ ) ↔ ( ψ ∧ χ ) )",
        ref="pm5.32",
        note="pm5.32",
    )

    # pm4.71ri: φ ↔ ( ψ ∧ φ )  (using hypothesis φ → ψ)
    s2 = lb.ref(
        "s2",
        "φ ↔ ( ψ ∧ φ )",
        h1,
        ref="pm4.71ri",
        note="pm4.71ri biadani.1",
    )

    # bicomi: ( ψ ∧ φ ) ↔ φ
    s3 = lb.ref(
        "s3",
        "( ψ ∧ φ ) ↔ φ",
        s2,
        ref="bicomi",
        note="bicomi",
    )

    # bibi1i: ( ( ψ ∧ φ ) ↔ ( ψ ∧ χ ) ) ↔ ( φ ↔ ( ψ ∧ χ ) )
    #   using hypothesis ( ψ ∧ φ ) ↔ φ
    s4 = lb.ref(
        "s4",
        "( ( ψ ∧ φ ) ↔ ( ψ ∧ χ ) ) ↔ ( φ ↔ ( ψ ∧ χ ) )",
        s3,
        ref="bibi1i",
        note="bibi1i",
    )

    # bicomi: ( φ ↔ ( ψ ∧ χ ) ) ↔ ( ( ψ ∧ φ ) ↔ ( ψ ∧ χ ) )
    s5 = lb.ref(
        "s5",
        "( φ ↔ ( ψ ∧ χ ) ) ↔ ( ( ψ ∧ φ ) ↔ ( ψ ∧ χ ) )",
        s4,
        ref="bicomi",
        note="bicomi",
    )

    # bitr4i: ( ψ → ( φ ↔ χ ) ) ↔ ( φ ↔ ( ψ ∧ χ ) )
    res = lb.ref(
        "res",
        "( ψ → ( φ ↔ χ ) ) ↔ ( φ ↔ ( ψ ∧ χ ) )",
        s1,
        s5,
        ref="bitr4i",
        note="bitr4i",
    )

    return lb.build(res)


def prove_pm5_36(sys: System) -> Proof:
    """pm5.36: ( φ ∧ ( φ ↔ ψ ) ) ↔ ( ψ ∧ ( φ ↔ ψ ) ).

    Biconditional with conjunction: two equivalent branches.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm5.36")

    # id: ( φ ↔ ψ ) → ( φ ↔ ψ )
    s_id = lb.ref(
        "s_id",
        "( φ ↔ ψ ) → ( φ ↔ ψ )",
        ref="id",
        note="id",
    )

    # pm5.32ri with hypothesis s_id
    res = lb.ref(
        "res",
        "( φ ∧ ( φ ↔ ψ ) ) ↔ ( ψ ∧ ( φ ↔ ψ ) )",
        s_id,
        ref="pm5.32ri",
        note="pm5.32ri",
    )

    return lb.build(res)


def prove_pm5_21(sys: System) -> Proof:
    """pm5.21: ( ¬ φ ∧ ¬ ψ ) → ( φ ↔ ψ ).

    If both φ and ψ are false, they are equivalent.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm5.21")
    s1 = lb.ref(
        "s1",
        "( ¬ φ → ( ¬ ψ → ( φ ↔ ψ ) ) )",
        ref="pm5.21im",
        note="pm5.21im",
    )
    res = lb.ref(
        "res",
        "( ( ¬ φ ∧ ¬ ψ ) → ( φ ↔ ψ ) )",
        s1,
        ref="imp",
        note="imp pm5.21im",
    )
    return lb.build(res)


def prove_pm5_42(sys: System) -> Proof:
    """pm5.42: ( φ → ( ψ → χ ) ) ↔ ( φ → ( ψ → ( φ ∧ χ ) ) ).

    From the equivalence φ → ( χ ↔ ( φ ∧ χ ) ) given by ibar,
    deduce the biconditional linking two nested implications.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm5.42")

    # ibar: φ → ( χ ↔ ( φ ∧ χ ) )
    s_ibar = lb.ref(
        "s_ibar",
        "φ → ( χ ↔ ( φ ∧ χ ) )",
        ref="ibar",
        note="ibar",
    )

    # imbi2d s_ibar: φ → ( ( ψ → χ ) ↔ ( ψ → ( φ ∧ χ ) ) )
    s_imbi2d = lb.ref(
        "s_imbi2d",
        "φ → ( ( ψ → χ ) ↔ ( ψ → ( φ ∧ χ ) ) )",
        s_ibar,
        ref="imbi2d",
        note="imbi2d",
    )

    # pm5.74i s_imbi2d: ( ( φ → ( ψ → χ ) ) ↔ ( φ → ( ψ → ( φ ∧ χ ) ) ) )
    res = lb.ref(
        "res",
        "( φ → ( ψ → χ ) ) ↔ ( φ → ( ψ → ( φ ∧ χ ) ) )",
        s_imbi2d,
        ref="pm5.74i",
        note="pm5.74i",
    )

    return lb.build(res)


def prove_pm5_44(sys: System) -> Proof:
    """pm5.44: ( φ → ψ ) → ( ( φ → χ ) ↔ ( φ → ( ψ ∧ χ ) ) ).

    Transform an implication into a biconditional by distributing over a conjunction.
    """
    lb = ProofBuilder(sys, "pm5.44")

    # jcab: ( φ → ( ψ ∧ χ ) ) ↔ ( ( φ → ψ ) ∧ ( φ → χ ) )
    s1 = lb.ref(
        "s1",
        "( φ → ( ψ ∧ χ ) ) ↔ ( ( φ → ψ ) ∧ ( φ → χ ) )",
        ref="jcab",
        note="jcab",
    )

    # baibr with s1 as hypothesis
    res = lb.ref(
        "res",
        "( φ → ψ ) → ( ( φ → χ ) ↔ ( φ → ( ψ ∧ χ ) ) )",
        s1,
        ref="baibr",
        note="baibr",
    )

    return lb.build(res)


def prove_imdistan(sys: System) -> Proof:
    """imdistan: ( φ → ( ψ → χ ) ) ↔ ( ( φ ∧ ψ ) → ( φ ∧ χ ) ).

    Distribution of implication over conjunction.
    """
    lb = ProofBuilder(sys, "imdistan")

    # pm5.42: ( φ → ( ψ → χ ) ) ↔ ( φ → ( ψ → ( φ ∧ χ ) ) )
    s1 = lb.ref(
        "s1",
        "( φ → ( ψ → χ ) ) ↔ ( φ → ( ψ → ( φ ∧ χ ) ) )",
        ref="pm5.42",
        note="pm5.42",
    )

    # impexp with χ := ( φ ∧ χ ):
    # ( ( φ ∧ ψ ) → ( φ ∧ χ ) ) ↔ ( φ → ( ψ → ( φ ∧ χ ) ) )
    s2 = lb.ref(
        "s2",
        "( ( φ ∧ ψ ) → ( φ ∧ χ ) ) ↔ ( φ → ( ψ → ( φ ∧ χ ) ) )",
        ref="impexp",
        note="impexp",
    )

    # bitr4i: from A ↔ B and C ↔ B, derive A ↔ C
    res = lb.ref(
        "res",
        "( φ → ( ψ → χ ) ) ↔ ( ( φ ∧ ψ ) → ( φ ∧ χ ) )",
        s1,
        s2,
        ref="bitr4i",
        note="bitr4i",
    )

    return lb.build(res)


def prove_pm4_83(sys: System) -> Proof:
    """pm4.83: ( ( φ → ψ ) ∧ ( ¬ φ → ψ ) ) ↔ ψ.

    Proof by cases: both φ and ¬ φ imply ψ iff ψ holds.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm4.83")

    # exmid: φ ∨ ¬ φ
    s_exmid = lb.ref(
        "s_exmid",
        "( φ ∨ ¬ φ )",
        ref="exmid",
        note="exmid",
    )

    # a1bi with exmid: ψ ↔ ((φ ∨ ¬ φ) → ψ)
    s_a1bi = lb.ref(
        "s_a1bi",
        "( ψ ↔ ( ( φ ∨ ¬ φ ) → ψ ) )",
        s_exmid,
        ref="a1bi",
        note="a1bi",
    )

    # jaob (with χ := ¬ φ): ((φ ∨ ¬ φ) → ψ) ↔ ((φ → ψ) ∧ (¬ φ → ψ))
    s_jaob = lb.ref(
        "s_jaob",
        "( ( ( φ ∨ ¬ φ ) → ψ ) ↔ ( ( φ → ψ ) ∧ ( ¬ φ → ψ ) ) )",
        ref="jaob",
        note="jaob",
    )

    # bitr2i: chain s_a1bi and s_jaob
    res = lb.ref(
        "res",
        "( ( ( φ → ψ ) ∧ ( ¬ φ → ψ ) ) ↔ ψ )",
        s_a1bi,
        s_jaob,
        ref="bitr2i",
        note="bitr2i",
    )

    return lb.build(res)


def prove_3anim123d(sys: System) -> Proof:
    """3anim123d: φ → ( ( ψ ∧ θ ∧ η ) → ( χ ∧ τ ∧ ζ ) ).

    Deduction form of 3anim123.  From φ → ( ψ → χ ), φ → ( θ → τ ),
    and φ → ( η → ζ ), deduce φ → ( ( ψ ∧ θ ∧ η ) → ( χ ∧ τ ∧ ζ ) ).
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "3anim123d")
    h1 = lb.hyp("3anim123d.1", "φ → ( ψ → χ )")
    h2 = lb.hyp("3anim123d.2", "φ → ( θ → τ )")
    h3 = lb.hyp("3anim123d.3", "φ → ( η → ζ )")

    # anim12d h1 h2: φ → ( ( ψ ∧ θ ) → ( χ ∧ τ ) )
    s1 = lb.ref(
        "s1",
        "φ → ( ( ψ ∧ θ ) → ( χ ∧ τ ) )",
        h1,
        h2,
        ref="anim12d",
        note="anim12d",
    )

    # anim12d s1 h3: φ → ( ( ( ψ ∧ θ ) ∧ η ) → ( ( χ ∧ τ ) ∧ ζ ) )
    s2 = lb.ref(
        "s2",
        "φ → ( ( ( ψ ∧ θ ) ∧ η ) → ( ( χ ∧ τ ) ∧ ζ ) )",
        s1,
        h3,
        ref="anim12d",
        note="anim12d",
    )

    # df-3an: ( ψ ∧ θ ∧ η ) ↔ ( ( ψ ∧ θ ) ∧ η )
    df3an1 = lb.ref(
        "df3an1",
        "( ψ ∧ θ ∧ η ) ↔ ( ( ψ ∧ θ ) ∧ η )",
        ref="df-3an",
        note="df-3an",
    )

    # df-3an: ( χ ∧ τ ∧ ζ ) ↔ ( ( χ ∧ τ ) ∧ ζ )
    df3an2 = lb.ref(
        "df3an2",
        "( χ ∧ τ ∧ ζ ) ↔ ( ( χ ∧ τ ) ∧ ζ )",
        ref="df-3an",
        note="df-3an",
    )

    # 3imtr4g: φ → ( ( ψ ∧ θ ∧ η ) → ( χ ∧ τ ∧ ζ ) )
    res = lb.ref(
        "res",
        "φ → ( ( ψ ∧ θ ∧ η ) → ( χ ∧ τ ∧ ζ ) )",
        s2,
        df3an1,
        df3an2,
        ref="3imtr4g",
        note="3imtr4g",
    )

    return lb.build(res)


def prove_annotanannot(sys: System) -> Proof:
    """annotanannot: ( φ ∧ ¬ ( φ ∧ ψ ) ) ↔ ( φ ∧ ¬ ψ ).

    If φ holds, then the negation of ( φ ∧ ψ ) is equivalent
    to the negation of ψ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "annotanannot")

    # ibar: φ → ( ψ ↔ ( φ ∧ ψ ) )
    s1 = lb.ref(
        "s1",
        "φ → ( ψ ↔ ( φ ∧ ψ ) )",
        ref="ibar",
        note="ibar",
    )

    # bicomd s1: φ → ( ( φ ∧ ψ ) ↔ ψ )
    s2 = lb.ref(
        "s2",
        "φ → ( ( φ ∧ ψ ) ↔ ψ )",
        s1,
        ref="bicomd",
        note="bicomd",
    )

    # notbid s2: φ → ( ¬ ( φ ∧ ψ ) ↔ ¬ ψ )
    s3 = lb.ref(
        "s3",
        "φ → ( ¬ ( φ ∧ ψ ) ↔ ¬ ψ )",
        s2,
        ref="notbid",
        note="notbid",
    )

    # pm5.32i s3: ( φ ∧ ¬ ( φ ∧ ψ ) ) ↔ ( φ ∧ ¬ ψ )
    res = lb.ref(
        "res",
        "( φ ∧ ¬ ( φ ∧ ψ ) ) ↔ ( φ ∧ ¬ ψ )",
        s3,
        ref="pm5.32i",
        note="pm5.32i",
    )

    return lb.build(res)


def prove_pm4_71(sys: System) -> Proof:
    """pm4.71: ( ( φ → ψ ) ↔ ( φ ↔ ( φ ∧ ψ ) ) ).

    An alternative definition of the biconditional relating implication
    and conjunction.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm4.71")

    # simpl: ( φ ∧ ψ ) → φ
    s_simpl = lb.ref("simpl", "( φ ∧ ψ ) → φ", ref="simpl", note="simpl")

    # biantru with hypothesis simpl
    s_biantru = lb.ref(
        "s_biantru",
        "( ( φ → ( φ ∧ ψ ) ) ↔ ( ( φ → ( φ ∧ ψ ) ) ∧ ( ( φ ∧ ψ ) → φ ) ) )",
        s_simpl,
        ref="biantru",
        note="biantru",
    )

    # anclb: ( ( φ → ψ ) ↔ ( φ → ( φ ∧ ψ ) ) )
    s_anclb = lb.ref(
        "anclb",
        "( ( φ → ψ ) ↔ ( φ → ( φ ∧ ψ ) ) )",
        ref="anclb",
        note="anclb",
    )

    # dfbi2: ( ( φ ↔ ( φ ∧ ψ ) ) ↔ ( ( φ → ( φ ∧ ψ ) ) ∧ ( ( φ ∧ ψ ) → φ ) ) )
    s_dfbi2 = lb.ref(
        "dfbi2",
        "( ( φ ↔ ( φ ∧ ψ ) ) ↔ ( ( φ → ( φ ∧ ψ ) ) ∧ ( ( φ ∧ ψ ) → φ ) ) )",
        ref="dfbi2",
        note="dfbi2",
    )

    # 3bitr4i: chain equivalences
    res = lb.ref(
        "res",
        "( ( φ → ψ ) ↔ ( φ ↔ ( φ ∧ ψ ) ) )",
        s_biantru,
        s_anclb,
        s_dfbi2,
        ref="3bitr4i",
        note="3bitr4i",
    )

    return lb.build(res)


def prove_pm4_71i(sys: System) -> Proof:
    """pm4.71i: φ ↔ ( φ ∧ ψ ).

    Inference adding a conjunct to the right of an implication.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm4.71i")
    h1 = lb.hyp("pm4.71i.1", "φ → ψ")
    s1 = lb.ref(
        "s1",
        "( φ → ψ ) ↔ ( φ ↔ ( φ ∧ ψ ) )",
        ref="pm4.71",
        note="pm4.71",
    )
    res = lb.ref(
        "res",
        "φ ↔ ( φ ∧ ψ )",
        h1,
        s1,
        ref="mpbi",
        note="mpbi",
    )
    return lb.build(res)


def prove_pm4_45im(sys: System) -> Proof:
    """pm4.45im: φ ↔ ( φ ∧ ( ψ → φ ) ).

    Principle of identity expressed as an equivalence, with the antecedent
    of the implied antecedent as a conjunct.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm4.45im")
    s1 = lb.ref("s1", "φ → ( ψ → φ )", ref="ax-1", note="ax-1")
    res = lb.ref(
        "res",
        "φ ↔ ( φ ∧ ( ψ → φ ) )",
        s1,
        ref="pm4.71i",
        note="pm4.71i",
    )
    return lb.build(res)


def prove_pm4_71ri(sys: System) -> Proof:
    """pm4.71ri: φ ↔ ( ψ ∧ φ ).

    Inference adding a conjunct to the left of an implication.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm4.71ri")
    h1 = lb.hyp("pm4.71ri.1", "φ → ψ")
    s1 = lb.ref(
        "s1",
        "φ ↔ ( φ ∧ ψ )",
        h1,
        ref="pm4.71i",
        note="pm4.71i",
    )
    res = lb.ref(
        "res",
        "φ ↔ ( ψ ∧ φ )",
        s1,
        ref="biancomi",
        note="biancomi",
    )
    return lb.build(res)


def prove_pm4_71d(sys: System) -> Proof:
    """pm4.71d: φ → ( ψ ↔ ( ψ ∧ χ ) ).

    Deduction form of pm4.71 — given that φ implies ψ → χ,
    φ implies ψ is equivalent to ψ ∧ χ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm4.71d")
    h1 = lb.hyp("pm4.71d.1", "φ → ( ψ → χ )")
    s1 = lb.ref(
        "s1",
        "( ( ψ → χ ) ↔ ( ψ ↔ ( ψ ∧ χ ) ) )",
        ref="pm4.71",
        note="pm4.71",
    )
    res = lb.ref(
        "res",
        "φ → ( ψ ↔ ( ψ ∧ χ ) )",
        h1,
        s1,
        ref="sylib",
        note="sylib",
    )
    return lb.build(res)


def prove_pm4_71da(sys: System) -> Proof:
    """pm4.71da: φ → ( ψ ↔ ( ψ ∧ χ ) ).

    Deduction form of pm4.71 — given that φ implies ψ ↔ χ,
    φ implies ψ is equivalent to ψ ∧ χ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm4.71da")
    h1 = lb.hyp("pm4.71da.1", "φ → ( ψ ↔ χ )")
    s1 = lb.ref(
        "s1",
        "φ → ( ψ → χ )",
        h1,
        ref="biimpd",
        note="biimpd",
    )
    res = lb.ref(
        "res",
        "φ → ( ψ ↔ ( ψ ∧ χ ) )",
        s1,
        ref="pm4.71d",
        note="pm4.71d",
    )
    return lb.build(res)


def prove_pm4_71rd(sys: System) -> Proof:
    """pm4.71rd: φ → ( ψ ↔ ( χ ∧ ψ ) ).

    Deduction form of pm4.71r — given that φ implies ψ → χ,
    φ implies ψ is equivalent to χ ∧ ψ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm4.71rd")
    h1 = lb.hyp("pm4.71rd.1", "φ → ( ψ → χ )")
    s1 = lb.ref(
        "s1",
        "φ → ( ψ ↔ ( ψ ∧ χ ) )",
        h1,
        ref="pm4.71d",
        note="pm4.71d",
    )
    res = lb.ref(
        "res",
        "φ → ( ψ ↔ ( χ ∧ ψ ) )",
        s1,
        ref="biancomd",
        note="biancomd",
    )
    return lb.build(res)


def prove_pm4_24(sys: System) -> Proof:
    """pm4.24: φ ↔ ( φ ∧ φ ).

    Idempotence of conjunction — a proposition is equivalent to
    its conjunction with itself.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm4.24")
    s_id = lb.ref("s_id", "φ → φ", ref="id", note="id")
    res = lb.ref("res", "φ ↔ ( φ ∧ φ )", s_id, ref="pm4.71i", note="pm4.71i")
    return lb.build(res)


def prove_pm4_38(sys: System) -> Proof:
    """pm4.38: ( ( φ ↔ χ ) ∧ ( ψ ↔ θ ) ) → ( ( φ ∧ ψ ) ↔ ( χ ∧ θ ) ).

    Equivalence of conjunctions.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm4.38")
    s1 = lb.ref("s1", "( ( φ ↔ χ ) ∧ ( ψ ↔ θ ) ) → ( φ ↔ χ )", ref="simpl", note="simpl")
    s2 = lb.ref("s2", "( ( φ ↔ χ ) ∧ ( ψ ↔ θ ) ) → ( ψ ↔ θ )", ref="simpr", note="simpr")
    res = lb.ref(
        "res",
        "( ( φ ↔ χ ) ∧ ( ψ ↔ θ ) ) → ( ( φ ∧ ψ ) ↔ ( χ ∧ θ ) )",
        s1,
        s2,
        ref="anbi12d",
        note="anbi12d",
    )
    return lb.build(res)


def prove_anidm(sys: System) -> Proof:
    """anidm: ( ( φ ∧ φ ) ↔ φ ).

    Idempotence of conjunction — the conjunction of a proposition with
    itself is equivalent to the proposition (biconditional form).
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "anidm")
    s24 = lb.ref("s24", "φ ↔ ( φ ∧ φ )", ref="pm4.24", note="pm4.24")
    res = lb.ref("res", "( ( φ ∧ φ ) ↔ φ )", s24, ref="bicomi", note="bicomi")
    return lb.build(res)


def prove_anidmdbi(sys: System) -> Proof:
    """anidmdbi: ( ( φ → ( ψ ∧ ψ ) ) ↔ ( φ → ψ ) ).

    Biconditional form of anidm with implication context — the
    implication form of idempotency of conjunction.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "anidmdbi")
    s1 = lb.ref("s1", "( ( ψ ∧ ψ ) ↔ ψ )", ref="anidm", note="anidm")
    res = lb.ref(
        "res",
        "( ( φ → ( ψ ∧ ψ ) ) ↔ ( φ → ψ ) )",
        s1,
        ref="imbi2i",
        note="imbi2i",
    )
    return lb.build(res)


def prove_pm4_15(sys: System) -> Proof:
    """pm4.15: ( ( φ ∧ ψ ) → ¬ χ ) ↔ ( ( ψ ∧ χ ) → ¬ φ ).

    Negated consequent of conjunction commutes via contraposition
    and the NAND relation.
    """
    lb = ProofBuilder(sys, "pm4.15")

    # con2b: ( ( ψ ∧ χ ) → ¬ φ ) ↔ ( φ → ¬ ( ψ ∧ χ ) )
    s1 = lb.ref(
        "s1",
        "( ( ψ ∧ χ ) → ¬ φ ) ↔ ( φ → ¬ ( ψ ∧ χ ) )",
        ref="con2b",
        note="con2b",
    )

    # nan: ( φ → ¬ ( ψ ∧ χ ) ) ↔ ( ( φ ∧ ψ ) → ¬ χ )
    s2 = lb.ref(
        "s2",
        "( φ → ¬ ( ψ ∧ χ ) ) ↔ ( ( φ ∧ ψ ) → ¬ χ )",
        ref="nan",
        note="nan",
    )

    # bitr2i: from s1 and s2
    res = lb.ref(
        "res",
        "( ( φ ∧ ψ ) → ¬ χ ) ↔ ( ( ψ ∧ χ ) → ¬ φ )",
        s1,
        s2,
        ref="bitr2i",
        note="bitr2i",
    )

    return lb.build(res)


def prove_an3andi(sys: System) -> Proof:
    """an3andi: ( φ ∧ ( ψ ∧ χ ∧ θ ) ) ↔ ( ( φ ∧ ψ ) ∧ ( φ ∧ χ ) ∧ ( φ ∧ θ ) ).

    Distribution of conjunction over a ternary conjunction:
    distributing φ over the three conjuncts produces a ternary
    conjunction of three binary pairs.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "an3andi")

    # df-3an [ψ, χ, θ]: ( ψ ∧ χ ∧ θ ) ↔ ( ( ψ ∧ χ ) ∧ θ )
    s1 = lb.ref(
        "s1",
        "( ψ ∧ χ ∧ θ ) ↔ ( ( ψ ∧ χ ) ∧ θ )",
        ref="df-3an",
        note="df-3an",
    )

    # anbi2i with φ conjoined to the left:
    # ( φ ∧ ( ψ ∧ χ ∧ θ ) ) ↔ ( φ ∧ ( ( ψ ∧ χ ) ∧ θ ) )
    s2 = lb.ref(
        "s2",
        "( φ ∧ ( ψ ∧ χ ∧ θ ) ) ↔ ( φ ∧ ( ( ψ ∧ χ ) ∧ θ ) )",
        s1,
        ref="anbi2i",
        note="anbi2i",
    )

    # anandi [φ, (ψ∧χ), θ]:
    # ( φ ∧ ( ( ψ ∧ χ ) ∧ θ ) ) ↔ ( ( φ ∧ ( ψ ∧ χ ) ) ∧ ( φ ∧ θ ) )
    s3 = lb.ref(
        "s3",
        "( φ ∧ ( ( ψ ∧ χ ) ∧ θ ) ) ↔ ( ( φ ∧ ( ψ ∧ χ ) ) ∧ ( φ ∧ θ ) )",
        ref="anandi",
        note="anandi",
    )

    # df-3an [(φ∧ψ), (φ∧χ), (φ∧θ)]:
    # ( ( φ ∧ ψ ) ∧ ( φ ∧ χ ) ∧ ( φ ∧ θ ) ) ↔ ( ( ( φ ∧ ψ ) ∧ ( φ ∧ χ ) ) ∧ ( φ ∧ θ ) )
    s4 = lb.ref(
        "s4",
        "( ( φ ∧ ψ ) ∧ ( φ ∧ χ ) ∧ ( φ ∧ θ ) ) ↔ ( ( ( φ ∧ ψ ) ∧ ( φ ∧ χ ) ) ∧ ( φ ∧ θ ) )",
        ref="df-3an",
        note="df-3an",
    )

    # anandi [φ, ψ, χ]:
    # ( φ ∧ ( ψ ∧ χ ) ) ↔ ( ( φ ∧ ψ ) ∧ ( φ ∧ χ ) )
    s5 = lb.ref(
        "s5",
        "( φ ∧ ( ψ ∧ χ ) ) ↔ ( ( φ ∧ ψ ) ∧ ( φ ∧ χ ) )",
        ref="anandi",
        note="anandi",
    )
    s5r = lb.ref(
        "s5r",
        "( ( φ ∧ ψ ) ∧ ( φ ∧ χ ) ) ↔ ( φ ∧ ( ψ ∧ χ ) )",
        s5,
        ref="bicomi",
        note="bicomi",
    )

    # bianbi s4, s5: substitute s5 into the right conjunct of s4
    # s4 is D ↔ ( Y ∧ Z ) with Y = ((φ∧ψ)∧(φ∧χ)), Z = (φ∧θ)
    # s5 is W ↔ Y  with W = (φ∧(ψ∧χ))
    # bianbi gives: D ↔ ( W ∧ Z )
    # i.e. ( ( φ ∧ ψ ) ∧ ( φ ∧ χ ) ∧ ( φ ∧ θ ) ) ↔ ( ( φ ∧ ( ψ ∧ χ ) ) ∧ ( φ ∧ θ ) )
    s6 = lb.ref(
        "s6",
        "( ( φ ∧ ψ ) ∧ ( φ ∧ χ ) ∧ ( φ ∧ θ ) ) ↔ ( ( φ ∧ ( ψ ∧ χ ) ) ∧ ( φ ∧ θ ) )",
        s4,
        s5r,
        ref="bianbi",
        note="bianbi",
    )

    # 3bitr4i: chain s3 (A↔B), s2 (C↔A), s6 (D↔B) → C↔D
    # C = ( φ ∧ ( ψ ∧ χ ∧ θ ) ), D = ( ( φ ∧ ψ ) ∧ ( φ ∧ χ ) ∧ ( φ ∧ θ ) )
    res = lb.ref(
        "res",
        "( φ ∧ ( ψ ∧ χ ∧ θ ) ) ↔ ( ( φ ∧ ψ ) ∧ ( φ ∧ χ ) ∧ ( φ ∧ θ ) )",
        s3,
        s2,
        s6,
        ref="3bitr4i",
        note="3bitr4i",
    )

    return lb.build(res)


def prove_nanan(sys: System) -> Proof:
    """nanan: ( φ ∧ ψ ) ↔ ¬ ( φ ⊼ ψ ).

    Alternative definition of conjunction in terms of NAND — the converse
    of df-nan via con2bii.
    """
    lb = ProofBuilder(sys, "nanan")
    dfnan = lb.ref(
        "df-nan",
        "( φ ⊼ ψ ) ↔ ¬ ( φ ∧ ψ )",
        ref="df-nan",
        note="df-nan",
    )
    res = lb.ref(
        "res",
        "( φ ∧ ψ ) ↔ ¬ ( φ ⊼ ψ )",
        dfnan,
        ref="con2bii",
        note="con2bii",
    )
    return lb.build(res)


def prove_nannan(sys: System) -> Proof:
    """nannan: ( φ ⊼ ( ψ ⊼ χ ) ) ↔ ( φ → ( ψ ∧ χ ) ).

    NAND-in-NAND expressed as implication of a conjunction.
    """
    lb = ProofBuilder(sys, "nannan")

    # dfnan2: ( φ ⊼ ( ψ ⊼ χ ) ) ↔ ( φ → ¬ ( ψ ⊼ χ ) )
    s1 = lb.ref(
        "s1",
        "( φ ⊼ ( ψ ⊼ χ ) ) ↔ ( φ → ¬ ( ψ ⊼ χ ) )",
        ref="dfnan2",
        note="dfnan2",
    )

    # nanan (ψ/φ, χ/ψ): ( ψ ∧ χ ) ↔ ¬ ( ψ ⊼ χ )
    s2 = lb.ref(
        "s2",
        "( ψ ∧ χ ) ↔ ¬ ( ψ ⊼ χ )",
        ref="nanan",
        note="nanan",
    )

    # imbi2i on s2: ( φ → ( ψ ∧ χ ) ) ↔ ( φ → ¬ ( ψ ⊼ χ ) )
    s3 = lb.ref(
        "s3",
        "( φ → ( ψ ∧ χ ) ) ↔ ( φ → ¬ ( ψ ⊼ χ ) )",
        s2,
        ref="imbi2i",
        note="imbi2i",
    )

    # bitr4i on s1 and s3
    res = lb.ref(
        "res",
        "( φ ⊼ ( ψ ⊼ χ ) ) ↔ ( φ → ( ψ ∧ χ ) )",
        s1,
        s3,
        ref="bitr4i",
        note="bitr4i",
    )

    return lb.build(res)


def prove_nic_mp(sys: System) -> Proof:
    """nic-mp: ψ.

    Nicod's modus ponens: from φ and φ ⊼ (χ ⊼ ψ), derive ψ.
    """
    lb = ProofBuilder(sys, "nic-mp")
    h_min = lb.hyp("nic-mp.nic-jmin", "φ")
    h_maj = lb.hyp("nic-mp.nic-jmaj", "φ ⊼ ( χ ⊼ ψ )")

    # nannan: ( φ ⊼ ( χ ⊼ ψ ) ) ↔ ( φ → ( χ ∧ ψ ) )
    s1 = lb.ref(
        "s1",
        "( φ ⊼ ( χ ⊼ ψ ) ) ↔ ( φ → ( χ ∧ ψ ) )",
        ref="nannan",
        note="nannan",
    )

    # mpbi: φ → ( χ ∧ ψ )
    s2 = lb.ref(
        "s2",
        "φ → ( χ ∧ ψ )",
        h_maj,
        s1,
        ref="mpbi",
        note="mpbi",
    )

    # simprd: φ → ψ
    s3 = lb.ref(
        "s3",
        "φ → ψ",
        s2,
        ref="simprd",
        note="simprd",
    )

    # ax-mp: ψ
    res = lb.mp("res", h_min, s3, "MP nic-jmin, s3")

    return lb.build(res)


def prove_nic_mp_alt(sys: System) -> Proof:
    """nic-mpALT: ψ.

    Alternate proof of Nicod's modus ponens: from φ and φ ⊼ (χ ⊼ ψ), derive ψ.
    Uses df-nan, anbi2i, xchbinx, mpbi, iman, mpbir, simprd, and ax-mp.
    """
    lb = ProofBuilder(sys, "nic-mpALT")
    h_min = lb.hyp("nic-mpALT.nic-jmin", "φ")
    h_maj = lb.hyp("nic-mpALT.nic-jmaj", "φ ⊼ ( χ ⊼ ψ )")

    # df-nan: ( φ ⊼ ( χ ⊼ ψ ) ) ↔ ¬ ( φ ∧ ( χ ⊼ ψ ) )
    s1 = lb.ref(
        "s1",
        "( φ ⊼ ( χ ⊼ ψ ) ) ↔ ¬ ( φ ∧ ( χ ⊼ ψ ) )",
        ref="df-nan",
        note="df-nan",
    )

    # mpbi: ¬ ( φ ∧ ( χ ⊼ ψ ) )
    s2 = lb.ref(
        "s2",
        "¬ ( φ ∧ ( χ ⊼ ψ ) )",
        h_maj,
        s1,
        ref="mpbi",
        note="mpbi",
    )

    # df-nan: ( χ ⊼ ψ ) ↔ ¬ ( χ ∧ ψ )
    s3 = lb.ref(
        "s3",
        "( χ ⊼ ψ ) ↔ ¬ ( χ ∧ ψ )",
        ref="df-nan",
        note="df-nan",
    )

    # anbi2i: ( φ ∧ ( χ ⊼ ψ ) ) ↔ ( φ ∧ ¬ ( χ ∧ ψ ) )
    s4 = lb.ref(
        "s4",
        "( φ ∧ ( χ ⊼ ψ ) ) ↔ ( φ ∧ ¬ ( χ ∧ ψ ) )",
        s3,
        ref="anbi2i",
        note="anbi2i",
    )

    # xchbinx: ¬ ( φ ∧ ( χ ⊼ ψ ) ) ↔ ¬ ( φ ∧ ¬ ( χ ∧ ψ ) )
    s5 = lb.ref(
        "s5",
        "¬ ( φ ∧ ( χ ⊼ ψ ) ) ↔ ¬ ( φ ∧ ¬ ( χ ∧ ψ ) )",
        s4,
        ref="notbii",
        note="notbii",
    )

    # mpbi: ¬ ( φ ∧ ¬ ( χ ∧ ψ ) )
    s6 = lb.ref(
        "s6",
        "¬ ( φ ∧ ¬ ( χ ∧ ψ ) )",
        s2,
        s5,
        ref="mpbi",
        note="mpbi",
    )

    # iman: ( φ → ( χ ∧ ψ ) ) ↔ ¬ ( φ ∧ ¬ ( χ ∧ ψ ) )
    s7 = lb.ref(
        "s7",
        "( φ → ( χ ∧ ψ ) ) ↔ ¬ ( φ ∧ ¬ ( χ ∧ ψ ) )",
        ref="iman",
        note="iman",
    )

    # mpbir: φ → ( χ ∧ ψ )
    s8 = lb.ref(
        "s8",
        "φ → ( χ ∧ ψ )",
        s6,
        s7,
        ref="mpbir",
        note="mpbir",
    )

    # simprd: φ → ψ
    s9 = lb.ref(
        "s9",
        "φ → ψ",
        s8,
        ref="simprd",
        note="simprd",
    )

    # ax-mp: ψ
    res = lb.mp("res", h_min, s9, "MP nic-jmin, s9")

    return lb.build(res)


def prove_nic_ax(sys: System) -> Proof:
    """nic-ax: ( φ ⊼ ( χ ⊼ ψ ) ) ⊼ ( ( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) ).

    Nicod's axiom — the single axiom of the Nicod system, expressed in
    NAND.  This is derivable as a theorem in the Hilbert system.
    """
    lb = ProofBuilder(sys, "nic-ax")

    # 1. nannan: ( φ ⊼ ( χ ⊼ ψ ) ) ↔ ( φ → ( χ ∧ ψ ) )
    s1 = lb.ref(
        "s1",
        "( φ ⊼ ( χ ⊼ ψ ) ) ↔ ( φ → ( χ ∧ ψ ) )",
        ref="nannan",
        note="nannan",
    )

    # 2. biimpi: ( φ ⊼ ( χ ⊼ ψ ) ) → ( φ → ( χ ∧ ψ ) )
    s2 = lb.ref(
        "s2",
        "( φ ⊼ ( χ ⊼ ψ ) ) → ( φ → ( χ ∧ ψ ) )",
        s1,
        ref="biimpi",
        note="biimpi",
    )

    # 3. simpl: ( χ ∧ ψ ) → χ
    s3 = lb.ref(
        "s3",
        "( χ ∧ ψ ) → χ",
        ref="simpl",
        note="simpl",
    )

    # 4. imim2i: ( φ → ( χ ∧ ψ ) ) → ( φ → χ )
    s4 = lb.ref(
        "s4",
        "( φ → ( χ ∧ ψ ) ) → ( φ → χ )",
        s3,
        ref="imim2i",
        note="imim2i",
    )

    # 5. imnan: ( θ → ¬ χ ) ↔ ¬ ( θ ∧ χ )
    s5 = lb.ref(
        "s5",
        "( θ → ¬ χ ) ↔ ¬ ( θ ∧ χ )",
        ref="imnan",
        note="imnan",
    )

    # 6. df-nan: ( θ ⊼ χ ) ↔ ¬ ( θ ∧ χ )
    s6 = lb.ref(
        "s6",
        "( θ ⊼ χ ) ↔ ¬ ( θ ∧ χ )",
        ref="df-nan",
        note="df-nan",
    )

    # 7. bitr4i: ( θ → ¬ χ ) ↔ ( θ ⊼ χ )
    s7 = lb.ref(
        "s7",
        "( θ → ¬ χ ) ↔ ( θ ⊼ χ )",
        s5,
        s6,
        ref="bitr4i",
        note="bitr4i",
    )

    # 8. con3: ( φ → χ ) → ( ¬ χ → ¬ φ )
    s8 = lb.ref(
        "s8",
        "( φ → χ ) → ( ¬ χ → ¬ φ )",
        ref="con3",
        note="con3",
    )

    # 9. imim2d: ( φ → χ ) → ( ( θ → ¬ χ ) → ( θ → ¬ φ ) )
    s9 = lb.ref(
        "s9",
        "( φ → χ ) → ( ( θ → ¬ χ ) → ( θ → ¬ φ ) )",
        s8,
        ref="imim2d",
        note="imim2d",
    )

    # 10. imnan: ( φ → ¬ θ ) ↔ ¬ ( φ ∧ θ )
    s10 = lb.ref(
        "s10",
        "( φ → ¬ θ ) ↔ ¬ ( φ ∧ θ )",
        ref="imnan",
        note="imnan",
    )

    # 11. con2b: ( θ → ¬ φ ) ↔ ( φ → ¬ θ )
    s11 = lb.ref(
        "s11",
        "( θ → ¬ φ ) ↔ ( φ → ¬ θ )",
        ref="con2b",
        note="con2b",
    )

    # 12. df-nan: ( φ ⊼ θ ) ↔ ¬ ( φ ∧ θ )
    s12 = lb.ref(
        "s12",
        "( φ ⊼ θ ) ↔ ¬ ( φ ∧ θ )",
        ref="df-nan",
        note="df-nan",
    )

    # 13. 3bitr4ri: ( φ ⊼ θ ) ↔ ( θ → ¬ φ )
    s13 = lb.ref(
        "s13",
        "( φ ⊼ θ ) ↔ ( θ → ¬ φ )",
        s10,
        s11,
        s12,
        ref="3bitr4ri",
        note="3bitr4ri",
    )

    # 14. imbitrrdi: ( φ → χ ) → ( ( θ → ¬ χ ) → ( φ ⊼ θ ) )
    s14 = lb.ref(
        "s14",
        "( φ → χ ) → ( ( θ → ¬ χ ) → ( φ ⊼ θ ) )",
        s9,
        s13,
        ref="imbitrrdi",
        note="imbitrrdi",
    )

    # 15. biimtrrid: ( φ → χ ) → ( ( θ ⊼ χ ) → ( φ ⊼ θ ) )
    s15 = lb.ref(
        "s15",
        "( φ → χ ) → ( ( θ ⊼ χ ) → ( φ ⊼ θ ) )",
        s7,
        s14,
        ref="biimtrrid",
        note="biimtrrid",
    )

    # 16. nanim: ( ( θ ⊼ χ ) → ( φ ⊼ θ ) ) ↔ ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) )
    s16 = lb.ref(
        "s16",
        "( ( θ ⊼ χ ) → ( φ ⊼ θ ) ) ↔ ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) )",
        ref="nanim",
        note="nanim",
    )

    # 17. sylib: ( φ → χ ) → ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) )
    s17 = lb.ref(
        "s17",
        "( φ → χ ) → ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) )",
        s15,
        s16,
        ref="sylib",
        note="sylib",
    )

    # 18. 3syl: ( φ ⊼ ( χ ⊼ ψ ) ) → ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) )
    s18 = lb.ref(
        "s18",
        "( φ ⊼ ( χ ⊼ ψ ) ) → ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) )",
        s2,
        s4,
        s17,
        ref="3syl",
        note="3syl",
    )

    # 19. pm4.24: τ ↔ ( τ ∧ τ )
    s19 = lb.ref(
        "s19",
        "τ ↔ ( τ ∧ τ )",
        ref="pm4.24",
        note="pm4.24",
    )

    # 20. biimpi: τ → ( τ ∧ τ )
    s20 = lb.ref(
        "s20",
        "τ → ( τ ∧ τ )",
        s19,
        ref="biimpi",
        note="biimpi",
    )

    # 21. nannan: ( τ ⊼ ( τ ⊼ τ ) ) ↔ ( τ → ( τ ∧ τ ) )
    s21 = lb.ref(
        "s21",
        "( τ ⊼ ( τ ⊼ τ ) ) ↔ ( τ → ( τ ∧ τ ) )",
        ref="nannan",
        note="nannan",
    )

    # 22. mpbir: τ ⊼ ( τ ⊼ τ )
    s22 = lb.ref(
        "s22",
        "τ ⊼ ( τ ⊼ τ )",
        s20,
        s21,
        ref="mpbir",
        note="mpbir",
    )

    # 23. jctil: ( φ ⊼ ( χ ⊼ ψ ) ) → ( ( τ ⊼ ( τ ⊼ τ ) ) ∧ ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) )
    s23 = lb.ref(
        "s23",
        "( φ ⊼ ( χ ⊼ ψ ) ) → ( ( τ ⊼ ( τ ⊼ τ ) ) ∧ ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) )",
        s18,
        s22,
        ref="jctil",
        note="jctil",
    )

    # 24. nannan: ( ( φ ⊼ ( χ ⊼ ψ ) ) ⊼ ( ( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) ) ) ↔ ( ( φ ⊼ ( χ ⊼ ψ ) ) → ( ( τ ⊼ ( τ ⊼ τ ) ) ∧ ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) ) )
    s24 = lb.ref(
        "s24",
        "( ( φ ⊼ ( χ ⊼ ψ ) ) ⊼ ( ( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) ) ) ↔ ( ( φ ⊼ ( χ ⊼ ψ ) ) → ( ( τ ⊼ ( τ ⊼ τ ) ) ∧ ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) ) )",
        ref="nannan",
        note="nannan",
    )

    # 25. mpbir: final conclusion
    res = lb.ref(
        "res",
        "( φ ⊼ ( χ ⊼ ψ ) ) ⊼ ( ( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) )",
        s23,
        s24,
        ref="mpbir",
        note="mpbir",
    )

    return lb.build(res)


def prove_nic_axALT(sys: System) -> Proof:
    """nic-axALT: ( φ ⊼ ( χ ⊼ ψ ) ) ⊼ ( ( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) ).

    Alternate direct proof of nic-ax.
    """
    lb = ProofBuilder(sys, "nic-axALT")
    res = lb.ref(
        "res",
        "( φ ⊼ ( χ ⊼ ψ ) ) ⊼ ( ( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) )",
        ref="nic-ax",
        note="nic-ax",
    )
    return lb.build(res)


def prove_nic_imp(sys: System) -> Proof:
    """nic-imp: ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ).

    Inference for nic-mp using nic-ax as major premise.
    """
    lb = ProofBuilder(sys, "nic-imp")
    h_nic_imp = lb.hyp("nic-imp.nic-imp.1", "φ ⊼ ( χ ⊼ ψ )")

    # nic-ax: ( φ ⊼ ( χ ⊼ ψ ) ) ⊼ ( ( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) )
    s1 = lb.ref(
        "s1",
        "( φ ⊼ ( χ ⊼ ψ ) ) ⊼ ( ( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) )",
        ref="nic-ax",
        note="nic-ax",
    )

    # nic-mp: from φ ⊼ ( χ ⊼ ψ ) and nic-ax, derive ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) )
    res = lb.ref(
        "res",
        "( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) )",
        h_nic_imp,
        s1,
        ref="nic-mp",
        note="nic-mp",
    )

    return lb.build(res)


def prove_nic_idlem1(sys: System) -> Proof:
    """nic-idlem1: ( θ ⊼ ( τ ⊼ ( τ ⊼ τ ) ) ) ⊼ ( ( ( φ ⊼ ( χ ⊼ ψ ) ) ⊼ θ ) ⊼ ( ( φ ⊼ ( χ ⊼ ψ ) ) ⊼ θ ) ).

    Lemma for nic-id.  Instance of nic-imp with nic-ax providing the hypothesis.
    (Contributed by Jeff Hoffman, 17-Nov-2007.)
    """
    lb = ProofBuilder(sys, "nic-idlem1")

    # nic-ax: ( φ ⊼ ( χ ⊼ ψ ) ) ⊼ ( ( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) )
    s1 = lb.ref(
        "s1",
        "( φ ⊼ ( χ ⊼ ψ ) ) ⊼ ( ( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) )",
        ref="nic-ax",
        note="nic-ax",
    )

    # nic-imp using s1 as hypothesis
    res = lb.ref(
        "res",
        "( θ ⊼ ( τ ⊼ ( τ ⊼ τ ) ) ) ⊼ ( ( ( φ ⊼ ( χ ⊼ ψ ) ) ⊼ θ ) ⊼ ( ( φ ⊼ ( χ ⊼ ψ ) ) ⊼ θ ) )",
        s1,
        ref="nic-imp",
        note="nic-imp",
    )

    return lb.build(res)


def prove_nic_idlem2(sys: System) -> Proof:
    """nic-idlem2: ( θ ⊼ ( τ ⊼ ( τ ⊼ τ ) ) ) ⊼ η.

    Lemma for nic-id.  Instance of nic-mp with nic-idlem1 providing the
    major premise via nic-imp.
    (Contributed by Jeff Hoffman, 17-Nov-2007.)
    """
    lb = ProofBuilder(sys, "nic-idlem2")
    h = lb.hyp("nic-idlem2.1", "η ⊼ ( ( φ ⊼ ( χ ⊼ ψ ) ) ⊼ θ )")

    # nic-ax
    s1 = lb.ref(
        "s1",
        "( φ ⊼ ( χ ⊼ ψ ) ) ⊼ ( ( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) )",
        ref="nic-ax",
        note="nic-ax",
    )

    # nic-imp on nic-ax → nic-idlem1
    s2 = lb.ref(
        "s2",
        "( θ ⊼ ( τ ⊼ ( τ ⊼ τ ) ) ) ⊼ ( ( ( φ ⊼ ( χ ⊼ ψ ) ) ⊼ θ ) ⊼ ( ( φ ⊼ ( χ ⊼ ψ ) ) ⊼ θ ) )",
        s1,
        ref="nic-imp",
        note="nic-imp",
    )

    # nic-imp on nic-idlem1 → major for nic-mp
    s3 = lb.ref(
        "s3",
        "( η ⊼ ( ( φ ⊼ ( χ ⊼ ψ ) ) ⊼ θ ) ) ⊼ ( ( ( θ ⊼ ( τ ⊼ ( τ ⊼ τ ) ) ) ⊼ η ) ⊼ ( ( θ ⊼ ( τ ⊼ ( τ ⊼ τ ) ) ) ⊼ η ) )",
        s2,
        ref="nic-imp",
        note="nic-imp",
    )

    # nic-mp: from hypothesis (minor) and s3 (major), derive conclusion
    res = lb.ref(
        "res",
        "( θ ⊼ ( τ ⊼ ( τ ⊼ τ ) ) ) ⊼ η",
        h,
        s3,
        ref="nic-mp",
        note="nic-mp",
    )

    return lb.build(res)


def prove_lukshef_ax1(sys: System) -> Proof:
    """lukshef-ax1: ( φ ⊼ ( χ ⊼ ψ ) ) ⊼ ( ( θ ⊼ ( θ ⊼ θ ) ) ⊼ ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) ).

    Instance of Nicod's axiom used by Lukasiewicz.
    """
    lb = ProofBuilder(sys, "lukshef-ax1")
    res = lb.ref(
        "res",
        "( φ ⊼ ( χ ⊼ ψ ) ) ⊼ ( ( θ ⊼ ( θ ⊼ θ ) ) ⊼ ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) )",
        ref="nic-ax",
        note="nic-ax",
    )
    return lb.build(res)


def prove_lukshefth1(sys: System) -> Proof:
    """lukshefth1: ( ( ( τ ⊼ ψ ) ⊼ ( ( φ ⊼ τ ) ⊼ ( φ ⊼ τ ) ) ) ⊼ ( θ ⊼ ( θ ⊼ θ ) ) ) ⊼ ( φ ⊼ ( ψ ⊼ χ ) ).

    Lemma for renicax. Nicod's/Lukasiewicz's shortest thesis.
    """
    lb = ProofBuilder(sys, "lukshefth1")

    # Step 1 (lukshef-ax1): ( φ ⊼ ( ψ ⊼ χ ) ) ⊼ ( ( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( τ ⊼ ψ ) ⊼ ( ( φ ⊼ τ ) ⊼ ( φ ⊼ τ ) ) ) )
    s1 = lb.ref(
        "s1",
        "( φ ⊼ ( ψ ⊼ χ ) ) ⊼ ( ( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( τ ⊼ ψ ) ⊼ ( ( φ ⊼ τ ) ⊼ ( φ ⊼ τ ) ) ) )",
        ref="lukshef-ax1",
        note="lukshef-ax1",
    )

    # Step 2 (lukshef-ax1): ( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( θ ⊼ ( θ ⊼ θ ) ) ⊼ ( ( θ ⊼ τ ) ⊼ ( ( τ ⊼ θ ) ⊼ ( τ ⊼ θ ) ) ) )
    s2 = lb.ref(
        "s2",
        "( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( θ ⊼ ( θ ⊼ θ ) ) ⊼ ( ( θ ⊼ τ ) ⊼ ( ( τ ⊼ θ ) ⊼ ( τ ⊼ θ ) ) ) )",
        ref="lukshef-ax1",
        note="lukshef-ax1",
    )

    # Step 3 (lukshef-ax1): step 2 applied to itself (complex substitution)
    s3 = lb.ref(
        "s3",
        "( ( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( θ ⊼ ( θ ⊼ θ ) ) ⊼ ( ( θ ⊼ τ ) ⊼ ( ( τ ⊼ θ ) ⊼ ( τ ⊼ θ ) ) ) ) ) ⊼ ( ( ( ( τ ⊼ ψ ) ⊼ ( ( φ ⊼ τ ) ⊼ ( φ ⊼ τ ) ) ) ⊼ ( ( ( τ ⊼ ψ ) ⊼ ( ( φ ⊼ τ ) ⊼ ( φ ⊼ τ ) ) ) ⊼ ( ( τ ⊼ ψ ) ⊼ ( ( φ ⊼ τ ) ⊼ ( φ ⊼ τ ) ) ) ) ) ⊼ ( ( ( ( τ ⊼ ψ ) ⊼ ( ( φ ⊼ τ ) ⊼ ( φ ⊼ τ ) ) ) ⊼ ( θ ⊼ ( θ ⊼ θ ) ) ) ⊼ ( ( ( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( τ ⊼ ψ ) ⊼ ( ( φ ⊼ τ ) ⊼ ( φ ⊼ τ ) ) ) ) ⊼ ( ( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( τ ⊼ ψ ) ⊼ ( ( φ ⊼ τ ) ⊼ ( φ ⊼ τ ) ) ) ) ) ) )",
        ref="lukshef-ax1",
        note="lukshef-ax1",
    )

    # Step 4 (nic-mp): from s2 and s3
    s4 = lb.ref(
        "s4",
        "( ( ( τ ⊼ ψ ) ⊼ ( ( φ ⊼ τ ) ⊼ ( φ ⊼ τ ) ) ) ⊼ ( θ ⊼ ( θ ⊼ θ ) ) ) ⊼ ( ( ( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( τ ⊼ ψ ) ⊼ ( ( φ ⊼ τ ) ⊼ ( φ ⊼ τ ) ) ) ) ⊼ ( ( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( τ ⊼ ψ ) ⊼ ( ( φ ⊼ τ ) ⊼ ( φ ⊼ τ ) ) ) ) )",
        s2,
        s3,
        ref="nic-mp",
        note="nic-mp s2, s3",
    )

    # Step 5 (lukshef-ax1): applied to step 4
    s5 = lb.ref(
        "s5",
        "( ( ( ( τ ⊼ ψ ) ⊼ ( ( φ ⊼ τ ) ⊼ ( φ ⊼ τ ) ) ) ⊼ ( θ ⊼ ( θ ⊼ θ ) ) ) ⊼ ( ( ( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( τ ⊼ ψ ) ⊼ ( ( φ ⊼ τ ) ⊼ ( φ ⊼ τ ) ) ) ) ⊼ ( ( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( τ ⊼ ψ ) ⊼ ( ( φ ⊼ τ ) ⊼ ( φ ⊼ τ ) ) ) ) ) ) ⊼ ( ( ( φ ⊼ ( ψ ⊼ χ ) ) ⊼ ( ( φ ⊼ ( ψ ⊼ χ ) ) ⊼ ( φ ⊼ ( ψ ⊼ χ ) ) ) ) ⊼ ( ( ( φ ⊼ ( ψ ⊼ χ ) ) ⊼ ( ( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( τ ⊼ ψ ) ⊼ ( ( φ ⊼ τ ) ⊼ ( φ ⊼ τ ) ) ) ) ) ⊼ ( ( ( ( ( τ ⊼ ψ ) ⊼ ( ( φ ⊼ τ ) ⊼ ( φ ⊼ τ ) ) ) ⊼ ( θ ⊼ ( θ ⊼ θ ) ) ) ⊼ ( φ ⊼ ( ψ ⊼ χ ) ) ) ⊼ ( ( ( ( τ ⊼ ψ ) ⊼ ( ( φ ⊼ τ ) ⊼ ( φ ⊼ τ ) ) ) ⊼ ( θ ⊼ ( θ ⊼ θ ) ) ) ⊼ ( φ ⊼ ( ψ ⊼ χ ) ) ) ) ) )",
        ref="lukshef-ax1",
        note="lukshef-ax1",
    )

    # Step 6 (nic-mp): from s4 and s5
    s6 = lb.ref(
        "s6",
        "( ( φ ⊼ ( ψ ⊼ χ ) ) ⊼ ( ( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( τ ⊼ ψ ) ⊼ ( ( φ ⊼ τ ) ⊼ ( φ ⊼ τ ) ) ) ) ) ⊼ ( ( ( ( ( τ ⊼ ψ ) ⊼ ( ( φ ⊼ τ ) ⊼ ( φ ⊼ τ ) ) ) ⊼ ( θ ⊼ ( θ ⊼ θ ) ) ) ⊼ ( φ ⊼ ( ψ ⊼ χ ) ) ) ⊼ ( ( ( ( τ ⊼ ψ ) ⊼ ( ( φ ⊼ τ ) ⊼ ( φ ⊼ τ ) ) ) ⊼ ( θ ⊼ ( θ ⊼ θ ) ) ) ⊼ ( φ ⊼ ( ψ ⊼ χ ) ) ) )",
        s4,
        s5,
        ref="nic-mp",
        note="nic-mp s4, s5",
    )

    # Step 7 (nic-mp): from s1 and s6 → conclusion
    res = lb.ref(
        "res",
        "( ( ( τ ⊼ ψ ) ⊼ ( ( φ ⊼ τ ) ⊼ ( φ ⊼ τ ) ) ) ⊼ ( θ ⊼ ( θ ⊼ θ ) ) ) ⊼ ( φ ⊼ ( ψ ⊼ χ ) )",
        s1,
        s6,
        ref="nic-mp",
        note="nic-mp s1, s6",
    )

    return lb.build(res)


def prove_lukshefth2(sys: System) -> Proof:
    """lukshefth2: ( τ ⊼ θ ) ⊼ ( ( θ ⊼ τ ) ⊼ ( θ ⊼ τ ) ).

    Lemma for renicax, from lukshef-ax1 and lukshefth1 via nic-mp.
    """
    lb = ProofBuilder(sys, "lukshefth2")

    # Step 1 (lukshef-ax1)
    s1 = lb.ref(
        "s1",
        "( ψ ⊼ ( χ ⊼ φ ) ) ⊼ ( ( θ ⊼ ( θ ⊼ θ ) ) ⊼ ( ( θ ⊼ χ ) ⊼ ( ( ψ ⊼ θ ) ⊼ ( ψ ⊼ θ ) ) ) )",
        ref="lukshef-ax1",
        note="lukshef-ax1",
    )

    # Step 2 (lukshef-ax1)
    s2 = lb.ref(
        "s2",
        "( ( ψ ⊼ ( χ ⊼ φ ) ) ⊼ ( ( θ ⊼ ( θ ⊼ θ ) ) ⊼ ( ( θ ⊼ χ ) ⊼ ( ( ψ ⊼ θ ) ⊼ ( ψ ⊼ θ ) ) ) ) ) ⊼ ( ( θ ⊼ ( θ ⊼ θ ) ) ⊼ ( ( θ ⊼ ( θ ⊼ ( θ ⊼ θ ) ) ) ⊼ ( ( ( ψ ⊼ ( χ ⊼ φ ) ) ⊼ θ ) ⊼ ( ( ψ ⊼ ( χ ⊼ φ ) ) ⊼ θ ) ) ) )",
        ref="lukshef-ax1",
        note="lukshef-ax1",
    )

    # Step 3 (nic-mp): from s1 and s2
    s3 = lb.ref(
        "s3",
        "( θ ⊼ ( θ ⊼ ( θ ⊼ θ ) ) ) ⊼ ( ( ( ψ ⊼ ( χ ⊼ φ ) ) ⊼ θ ) ⊼ ( ( ψ ⊼ ( χ ⊼ φ ) ) ⊼ θ ) )",
        s1,
        s2,
        ref="nic-mp",
        note="nic-mp s1, s2",
    )

    # Step 4 (lukshefth1)
    s4 = lb.ref(
        "s4",
        "( ( ( τ ⊼ φ ) ⊼ ( ( φ ⊼ τ ) ⊼ ( φ ⊼ τ ) ) ) ⊼ ( θ ⊼ ( θ ⊼ θ ) ) ) ⊼ ( φ ⊼ ( φ ⊼ φ ) )",
        ref="lukshefth1",
        note="lukshefth1",
    )

    # Step 5 (lukshef-ax1)
    s5 = lb.ref(
        "s5",
        "( ( θ ⊼ ( θ ⊼ ( θ ⊼ θ ) ) ) ⊼ ( ( ( ψ ⊼ ( χ ⊼ φ ) ) ⊼ θ ) ⊼ ( ( ψ ⊼ ( χ ⊼ φ ) ) ⊼ θ ) ) ) ⊼ ( ( φ ⊼ ( φ ⊼ φ ) ) ⊼ ( ( φ ⊼ ( ( ψ ⊼ ( χ ⊼ φ ) ) ⊼ θ ) ) ⊼ ( ( ( θ ⊼ ( θ ⊼ ( θ ⊼ θ ) ) ) ⊼ φ ) ⊼ ( ( θ ⊼ ( θ ⊼ ( θ ⊼ θ ) ) ) ⊼ φ ) ) ) )",
        ref="lukshef-ax1",
        note="lukshef-ax1",
    )

    # Step 6 (lukshef-ax1)
    s6 = lb.ref(
        "s6",
        "( ( ( θ ⊼ ( θ ⊼ ( θ ⊼ θ ) ) ) ⊼ ( ( ( ψ ⊼ ( χ ⊼ φ ) ) ⊼ θ ) ⊼ ( ( ψ ⊼ ( χ ⊼ φ ) ) ⊼ θ ) ) ) ⊼ ( ( φ ⊼ ( φ ⊼ φ ) ) ⊼ ( ( φ ⊼ ( ( ψ ⊼ ( χ ⊼ φ ) ) ⊼ θ ) ) ⊼ ( ( ( θ ⊼ ( θ ⊼ ( θ ⊼ θ ) ) ) ⊼ φ ) ⊼ ( ( θ ⊼ ( θ ⊼ ( θ ⊼ θ ) ) ) ⊼ φ ) ) ) ) ) ⊼ ( ( ( ( ( τ ⊼ φ ) ⊼ ( ( φ ⊼ τ ) ⊼ ( φ ⊼ τ ) ) ) ⊼ ( θ ⊼ ( θ ⊼ θ ) ) ) ⊼ ( ( ( ( τ ⊼ φ ) ⊼ ( ( φ ⊼ τ ) ⊼ ( φ ⊼ τ ) ) ) ⊼ ( θ ⊼ ( θ ⊼ θ ) ) ) ⊼ ( ( ( τ ⊼ φ ) ⊼ ( ( φ ⊼ τ ) ⊼ ( φ ⊼ τ ) ) ) ⊼ ( θ ⊼ ( θ ⊼ θ ) ) ) ) ) ⊼ ( ( ( ( ( τ ⊼ φ ) ⊼ ( ( φ ⊼ τ ) ⊼ ( φ ⊼ τ ) ) ) ⊼ ( θ ⊼ ( θ ⊼ θ ) ) ) ⊼ ( φ ⊼ ( φ ⊼ φ ) ) ) ⊼ ( ( ( ( θ ⊼ ( θ ⊼ ( θ ⊼ θ ) ) ) ⊼ ( ( ( ψ ⊼ ( χ ⊼ φ ) ) ⊼ θ ) ⊼ ( ( ψ ⊼ ( χ ⊼ φ ) ) ⊼ θ ) ) ) ⊼ ( ( ( τ ⊼ φ ) ⊼ ( ( φ ⊼ τ ) ⊼ ( φ ⊼ τ ) ) ) ⊼ ( θ ⊼ ( θ ⊼ θ ) ) ) ) ⊼ ( ( ( θ ⊼ ( θ ⊼ ( θ ⊼ θ ) ) ) ⊼ ( ( ( ψ ⊼ ( χ ⊼ φ ) ) ⊼ θ ) ⊼ ( ( ψ ⊼ ( χ ⊼ φ ) ) ⊼ θ ) ) ) ⊼ ( ( ( τ ⊼ φ ) ⊼ ( ( φ ⊼ τ ) ⊼ ( φ ⊼ τ ) ) ) ⊼ ( θ ⊼ ( θ ⊼ θ ) ) ) ) ) ) )",
        ref="lukshef-ax1",
        note="lukshef-ax1",
    )

    # Step 7 (nic-mp): from s5 and s6
    s7 = lb.ref(
        "s7",
        "( ( ( ( τ ⊼ φ ) ⊼ ( ( φ ⊼ τ ) ⊼ ( φ ⊼ τ ) ) ) ⊼ ( θ ⊼ ( θ ⊼ θ ) ) ) ⊼ ( φ ⊼ ( φ ⊼ φ ) ) ) ⊼ ( ( ( ( θ ⊼ ( θ ⊼ ( θ ⊼ θ ) ) ) ⊼ ( ( ( ψ ⊼ ( χ ⊼ φ ) ) ⊼ θ ) ⊼ ( ( ψ ⊼ ( χ ⊼ φ ) ) ⊼ θ ) ) ) ⊼ ( ( ( τ ⊼ φ ) ⊼ ( ( φ ⊼ τ ) ⊼ ( φ ⊼ τ ) ) ) ⊼ ( θ ⊼ ( θ ⊼ θ ) ) ) ) ⊼ ( ( ( θ ⊼ ( θ ⊼ ( θ ⊼ θ ) ) ) ⊼ ( ( ( ψ ⊼ ( χ ⊼ φ ) ) ⊼ θ ) ⊼ ( ( ψ ⊼ ( χ ⊼ φ ) ) ⊼ θ ) ) ) ⊼ ( ( ( τ ⊼ φ ) ⊼ ( ( φ ⊼ τ ) ⊼ ( φ ⊼ τ ) ) ) ⊼ ( θ ⊼ ( θ ⊼ θ ) ) ) ) )",
        s5,
        s6,
        ref="nic-mp",
        note="nic-mp s5, s6",
    )

    # Step 8 (nic-mp): from s4 and s7
    s8 = lb.ref(
        "s8",
        "( ( θ ⊼ ( θ ⊼ ( θ ⊼ θ ) ) ) ⊼ ( ( ( ψ ⊼ ( χ ⊼ φ ) ) ⊼ θ ) ⊼ ( ( ψ ⊼ ( χ ⊼ φ ) ) ⊼ θ ) ) ) ⊼ ( ( ( τ ⊼ φ ) ⊼ ( ( φ ⊼ τ ) ⊼ ( φ ⊼ τ ) ) ) ⊼ ( θ ⊼ ( θ ⊼ θ ) ) )",
        s4,
        s7,
        ref="nic-mp",
        note="nic-mp s4, s7",
    )

    # Step 9 (nic-mp): from s3 and s8
    s9 = lb.ref(
        "s9",
        "θ ⊼ ( θ ⊼ θ )",
        s3,
        s8,
        ref="nic-mp",
        note="nic-mp s3, s8",
    )

    # Step 10 (lukshef-ax1)
    s10 = lb.ref(
        "s10",
        "( θ ⊼ ( θ ⊼ θ ) ) ⊼ ( ( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( τ ⊼ θ ) ⊼ ( ( θ ⊼ τ ) ⊼ ( θ ⊼ τ ) ) ) )",
        ref="lukshef-ax1",
        note="lukshef-ax1",
    )

    # Step 11 (nic-mp): from s9 and s10 → conclusion
    res = lb.ref(
        "res",
        "( τ ⊼ θ ) ⊼ ( ( θ ⊼ τ ) ⊼ ( θ ⊼ τ ) )",
        s9,
        s10,
        ref="nic-mp",
        note="nic-mp s9, s10",
    )

    return lb.build(res)


def prove_renicax(sys: System) -> Proof:
    """renicax: ( φ ⊼ ( χ ⊼ ψ ) ) ⊼ ( ( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) ).

    A rederivation of nic-ax from lukshef-ax1, proving that lukshef-ax1
    with nic-mp can be used as a complete axiomatization of propositional
    calculus.  (Contributed by Anthony Hart, 31-Jul-2011.)
    """
    lb = ProofBuilder(sys, "renicax")

    # Step 1 (lukshefth1): ((θ⊼χ)⊼((φ⊼θ)⊼(φ⊼θ)))⊼(τ⊼(τ⊼τ)))⊼(φ⊼(χ⊼ψ))
    s1 = lb.ref(
        "s1",
        "( ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) ⊼ ( τ ⊼ ( τ ⊼ τ ) ) ) ⊼ ( φ ⊼ ( χ ⊼ ψ ) )",
        ref="lukshefth1",
        note="lukshefth1",
    )

    # Step 2 (lukshefth2): s1 ⊼ (((φ⊼(χ⊼ψ))⊼(((θ⊼χ)⊼((φ⊼θ)⊼(φ⊼θ)))⊼(τ⊼(τ⊼τ))))⊼((φ⊼(χ⊼ψ))⊼(((θ⊼χ)⊼((φ⊼θ)⊼(φ⊼θ)))⊼(τ⊼(τ⊼τ)))))
    s2 = lb.ref(
        "s2",
        "( ( ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) ⊼ ( τ ⊼ ( τ ⊼ τ ) ) ) ⊼ ( φ ⊼ ( χ ⊼ ψ ) ) ) ⊼ ( ( ( φ ⊼ ( χ ⊼ ψ ) ) ⊼ ( ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) ⊼ ( τ ⊼ ( τ ⊼ τ ) ) ) ) ⊼ ( ( φ ⊼ ( χ ⊼ ψ ) ) ⊼ ( ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) ⊼ ( τ ⊼ ( τ ⊼ τ ) ) ) ) )",
        ref="lukshefth2",
        note="lukshefth2",
    )

    # Step 3 (nic-mp s1,s2): (φ⊼(χ⊼ψ))⊼(((θ⊼χ)⊼((φ⊼θ)⊼(φ⊼θ)))⊼(τ⊼(τ⊼τ)))
    s3 = lb.ref(
        "s3",
        "( φ ⊼ ( χ ⊼ ψ ) ) ⊼ ( ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) ⊼ ( τ ⊼ ( τ ⊼ τ ) ) )",
        s1,
        s2,
        ref="nic-mp",
        note="nic-mp s1, s2",
    )

    # Step 4 (lukshefth2): (τ⊼(τ⊼τ))⊼((θ⊼χ)⊼((φ⊼θ)⊼(φ⊼θ))))⊼((((θ⊼χ)⊼((φ⊼θ)⊼(φ⊼θ)))⊼(τ⊼(τ⊼τ)))⊼(((θ⊼χ)⊼((φ⊼θ)⊼(φ⊼θ)))⊼(τ⊼(τ⊼τ))))
    s4 = lb.ref(
        "s4",
        "( ( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) ) ⊼ ( ( ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) ⊼ ( τ ⊼ ( τ ⊼ τ ) ) ) ⊼ ( ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) ⊼ ( τ ⊼ ( τ ⊼ τ ) ) ) )",
        ref="lukshefth2",
        note="lukshefth2",
    )

    # Step 5 (lukshef-ax1): s4 ⊼ ((φ⊼(χ⊼ψ))⊼((φ⊼(χ⊼ψ))⊼(φ⊼(χ⊼ψ))))⊼(((φ⊼(χ⊼ψ))⊼(((θ⊼χ)⊼((φ⊼θ)⊼(φ⊼θ)))⊼(τ⊼(τ⊼τ))))⊼((((τ⊼(τ⊼τ))⊼((θ⊼χ)⊼((φ⊼θ)⊼(φ⊼θ))))⊼(φ⊼(χ⊼ψ)))⊼(((τ⊼(τ⊼τ))⊼((θ⊼χ)⊼((φ⊼θ)⊼(φ⊼θ))))⊼(φ⊼(χ⊼ψ))))))
    s5 = lb.ref(
        "s5",
        "( ( ( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) ) ⊼ ( ( ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) ⊼ ( τ ⊼ ( τ ⊼ τ ) ) ) ⊼ ( ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) ⊼ ( τ ⊼ ( τ ⊼ τ ) ) ) ) ) ⊼ ( ( ( φ ⊼ ( χ ⊼ ψ ) ) ⊼ ( ( φ ⊼ ( χ ⊼ ψ ) ) ⊼ ( φ ⊼ ( χ ⊼ ψ ) ) ) ) ⊼ ( ( ( φ ⊼ ( χ ⊼ ψ ) ) ⊼ ( ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) ⊼ ( τ ⊼ ( τ ⊼ τ ) ) ) ) ⊼ ( ( ( ( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) ) ⊼ ( φ ⊼ ( χ ⊼ ψ ) ) ) ⊼ ( ( ( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) ) ⊼ ( φ ⊼ ( χ ⊼ ψ ) ) ) ) ) )",
        ref="lukshef-ax1",
        note="lukshef-ax1",
    )

    # Step 6 (nic-mp s4,s5): (φ⊼(χ⊼ψ))⊼(((θ⊼χ)⊼((φ⊼θ)⊼(φ⊼θ)))⊼(τ⊼(τ⊼τ))))⊼((((τ⊼(τ⊼τ))⊼((θ⊼χ)⊼((φ⊼θ)⊼(φ⊼θ))))⊼(φ⊼(χ⊼ψ)))⊼(((τ⊼(τ⊼τ))⊼((θ⊼χ)⊼((φ⊼θ)⊼(φ⊼θ))))⊼(φ⊼(χ⊼ψ))))
    s6 = lb.ref(
        "s6",
        "( ( φ ⊼ ( χ ⊼ ψ ) ) ⊼ ( ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) ⊼ ( τ ⊼ ( τ ⊼ τ ) ) ) ) ⊼ ( ( ( ( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) ) ⊼ ( φ ⊼ ( χ ⊼ ψ ) ) ) ⊼ ( ( ( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) ) ⊼ ( φ ⊼ ( χ ⊼ ψ ) ) ) )",
        s4,
        s5,
        ref="nic-mp",
        note="nic-mp s4, s5",
    )

    # Step 7 (nic-mp s3,s6): ((τ⊼(τ⊼τ))⊼((θ⊼χ)⊼((φ⊼θ)⊼(φ⊼θ))))⊼(φ⊼(χ⊼ψ))
    s7 = lb.ref(
        "s7",
        "( ( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) ) ⊼ ( φ ⊼ ( χ ⊼ ψ ) )",
        s3,
        s6,
        ref="nic-mp",
        note="nic-mp s3, s6",
    )

    # Step 8 (lukshefth2): s7 ⊼ (((φ⊼(χ⊼ψ))⊼((τ⊼(τ⊼τ))⊼((θ⊼χ)⊼((φ⊼θ)⊼(φ⊼θ)))))⊼((φ⊼(χ⊼ψ))⊼((τ⊼(τ⊼τ))⊼((θ⊼χ)⊼((φ⊼θ)⊼(φ⊼θ))))))
    s8 = lb.ref(
        "s8",
        "( ( ( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) ) ⊼ ( φ ⊼ ( χ ⊼ ψ ) ) ) ⊼ ( ( ( φ ⊼ ( χ ⊼ ψ ) ) ⊼ ( ( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) ) ) ⊼ ( ( φ ⊼ ( χ ⊼ ψ ) ) ⊼ ( ( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) ) ) )",
        ref="lukshefth2",
        note="lukshefth2",
    )

    # Step 9 (nic-mp s7,s8): (φ⊼(χ⊼ψ))⊼((τ⊼(τ⊼τ))⊼((θ⊼χ)⊼((φ⊼θ)⊼(φ⊼θ))))
    res = lb.ref(
        "res",
        "( φ ⊼ ( χ ⊼ ψ ) ) ⊼ ( ( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) )",
        s7,
        s8,
        ref="nic-mp",
        note="nic-mp s7, s8",
    )

    return lb.build(res)


def prove_nic_id(sys: System) -> Proof:
    """nic-id: τ ⊼ ( τ ⊼ τ ).

    Nicod's identity: the NAND of τ with itself yields τ.
    Uses nic-ax, nic-idlem1, nic-idlem2, and nic-mp.
    (Contributed by Jeff Hoffman, 17-Nov-2007.)
    """
    lb = ProofBuilder(sys, "nic-id")

    # nic-ax: ( ψ ⊼ ( ψ ⊼ ψ ) ) ⊼ ( ( θ ⊼ ( θ ⊼ θ ) ) ⊼ ( ( φ ⊼ ψ ) ⊼ ( ( ψ ⊼ φ ) ⊼ ( ψ ⊼ φ ) ) ) )
    s1 = lb.ref(
        "s1",
        "( ψ ⊼ ( ψ ⊼ ψ ) ) ⊼ ( ( θ ⊼ ( θ ⊼ θ ) ) ⊼ ( ( φ ⊼ ψ ) ⊼ ( ( ψ ⊼ φ ) ⊼ ( ψ ⊼ φ ) ) ) )",
        ref="nic-ax",
        note="nic-ax",
    )

    # nic-idlem2 with s1 as hypothesis → minor premise
    s2 = lb.ref(
        "s2",
        "( ( ( φ ⊼ ψ ) ⊼ ( ( ψ ⊼ φ ) ⊼ ( ψ ⊼ φ ) ) ) ⊼ ( χ ⊼ ( χ ⊼ χ ) ) ) ⊼ ( ψ ⊼ ( ψ ⊼ ψ ) )",
        s1,
        ref="nic-idlem2",
        note="nic-idlem2",
    )

    # nic-idlem1 → hypothesis for second nic-idlem2
    s3 = lb.ref(
        "s3",
        "( ( χ ⊼ ( χ ⊼ χ ) ) ⊼ ( τ ⊼ ( τ ⊼ τ ) ) ) ⊼ ( ( ( ( φ ⊼ ψ ) ⊼ ( ( ψ ⊼ φ ) ⊼ ( ψ ⊼ φ ) ) ) ⊼ ( χ ⊼ ( χ ⊼ χ ) ) ) ⊼ ( ( ( φ ⊼ ψ ) ⊼ ( ( ψ ⊼ φ ) ⊼ ( ψ ⊼ φ ) ) ) ⊼ ( χ ⊼ ( χ ⊼ χ ) ) ) )",
        ref="nic-idlem1",
        note="nic-idlem1",
    )

    # nic-idlem2 with s3 as hypothesis → major premise
    s4 = lb.ref(
        "s4",
        "( ( ( ( φ ⊼ ψ ) ⊼ ( ( ψ ⊼ φ ) ⊼ ( ψ ⊼ φ ) ) ) ⊼ ( χ ⊼ ( χ ⊼ χ ) ) ) ⊼ ( ψ ⊼ ( ψ ⊼ ψ ) ) ) ⊼ ( ( χ ⊼ ( χ ⊼ χ ) ) ⊼ ( τ ⊼ ( τ ⊼ τ ) ) )",
        s3,
        ref="nic-idlem2",
        note="nic-idlem2",
    )

    # nic-mp with s2 (minor) and s4 (major) → conclusion
    res = lb.ref(
        "res",
        "( τ ⊼ ( τ ⊼ τ ) )",
        s2,
        s4,
        ref="nic-mp",
        note="nic-mp",
    )

    return lb.build(res)


def prove_nic_swap(sys: System) -> Proof:
    """nic-swap: ( θ ⊼ φ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ).

    The connector ⊼ is symmetric.
    """
    lb = ProofBuilder(sys, "nic-swap")

    # nic-id with τ := φ
    s1 = lb.ref("s1", "( φ ⊼ ( φ ⊼ φ ) )", ref="nic-id", note="nic-id")

    # nic-ax with φ:=φ, χ:=φ, ψ:=φ, θ:=θ, τ:=τ
    s2 = lb.ref(
        "s2",
        "( φ ⊼ ( φ ⊼ φ ) ) ⊼ ( ( τ ⊼ ( τ ⊼ τ ) ) ⊼ ( ( θ ⊼ φ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) ) ) )",
        ref="nic-ax",
        note="nic-ax",
    )

    # nic-mp: from s1 (minor) and s2 (major) derive conclusion
    res = lb.ref(
        "res",
        "( θ ⊼ φ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) )",
        s1,
        s2,
        ref="nic-mp",
        note="nic-mp",
    )

    return lb.build(res)


def prove_nic_bijust(sys: System) -> Proof:
    """nic-bijust: ( τ ⊼ τ ) ⊼ ( ( τ ⊼ τ ) ⊼ ( τ ⊼ τ ) ).

    Direct instance of nic-swap with both variables instantiated to τ.
    """
    lb = ProofBuilder(sys, "nic-bijust")

    res = lb.ref(
        "res",
        "( τ ⊼ τ ) ⊼ ( ( τ ⊼ τ ) ⊼ ( τ ⊼ τ ) )",
        ref="nic-swap",
        note="nic-swap",
    )

    return lb.build(res)


def prove_nic_isw1(sys: System) -> Proof:
    """nic-isw1: φ ⊼ θ.

    Swap the two arguments of NAND.  From the hypothesis ``θ ⊼ φ`` we derive
    ``φ ⊼ θ`` using nic-swap and nic-mp.
    """
    lb = ProofBuilder(sys, "nic-isw1")

    h = lb.hyp("nic-isw1.1", "θ ⊼ φ")

    # nic-swap: ( θ ⊼ φ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) )
    s1 = lb.ref(
        "s1",
        "( θ ⊼ φ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) )",
        ref="nic-swap",
        note="nic-swap",
    )

    # nic-mp: from h (minor) and s1 (major) → φ ⊼ θ
    res = lb.ref(
        "res",
        "φ ⊼ θ",
        h,
        s1,
        ref="nic-mp",
        note="nic-mp",
    )

    return lb.build(res)


def prove_nic_isw2(sys: System) -> Proof:
    """nic-isw2: ψ ⊼ ( φ ⊼ θ ).

    Swap nested NAND terms.  From ``ψ ⊼ ( θ ⊼ φ )`` we derive
    ``ψ ⊼ ( φ ⊼ θ )`` using nic-swap, nic-imp, nic-mp, and nic-isw1.
    (Contributed by Jeff Hoffman, 17-Nov-2007.)
    """
    lb = ProofBuilder(sys, "nic-isw2")

    h = lb.hyp("nic-isw2.1", "ψ ⊼ ( θ ⊼ φ )")

    # nic-swap: ( φ ⊼ θ ) ⊼ ( ( θ ⊼ φ ) ⊼ ( θ ⊼ φ ) )
    s1 = lb.ref(
        "s1",
        "( φ ⊼ θ ) ⊼ ( ( θ ⊼ φ ) ⊼ ( θ ⊼ φ ) )",
        ref="nic-swap",
        note="nic-swap",
    )

    # nic-imp: from s1,
    #   derive ( ψ ⊼ ( θ ⊼ φ ) ) ⊼ ( ( ( φ ⊼ θ ) ⊼ ψ ) ⊼ ( ( φ ⊼ θ ) ⊼ ψ ) )
    s2 = lb.ref(
        "s2",
        "( ψ ⊼ ( θ ⊼ φ ) ) ⊼ ( ( ( φ ⊼ θ ) ⊼ ψ ) ⊼ ( ( φ ⊼ θ ) ⊼ ψ ) )",
        s1,
        ref="nic-imp",
        note="nic-imp",
    )

    # nic-mp: from h (minor) and s2 (major) → ( φ ⊼ θ ) ⊼ ψ
    s3 = lb.ref(
        "s3",
        "( φ ⊼ θ ) ⊼ ψ",
        h,
        s2,
        ref="nic-mp",
        note="nic-mp",
    )

    # nic-isw1: from ( φ ⊼ θ ) ⊼ ψ → ψ ⊼ ( φ ⊼ θ )
    res = lb.ref(
        "res",
        "ψ ⊼ ( φ ⊼ θ )",
        s3,
        ref="nic-isw1",
        note="nic-isw1",
    )

    return lb.build(res)


def prove_nic_iimp1(sys: System) -> Proof:
    """nic-iimp1: θ ⊼ φ.

    Inference form of nic-imp using nic-mp and nic-isw1.
    (Contributed by Jeff Hoffman, 17-Nov-2007.)
    """
    lb = ProofBuilder(sys, "nic-iimp1")

    h1 = lb.hyp("nic-iimp1.1", "φ ⊼ ( χ ⊼ ψ )")
    h2 = lb.hyp("nic-iimp1.2", "θ ⊼ χ")

    # nic-imp: from h1, derive ( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) )
    s1 = lb.ref(
        "s1",
        "( θ ⊼ χ ) ⊼ ( ( φ ⊼ θ ) ⊼ ( φ ⊼ θ ) )",
        h1,
        ref="nic-imp",
        note="nic-imp",
    )

    # nic-mp: from h2 (minor) and s1 (major) → φ ⊼ θ
    s2 = lb.ref(
        "s2",
        "φ ⊼ θ",
        h2,
        s1,
        ref="nic-mp",
        note="nic-mp",
    )

    # nic-isw1: from s2 (φ ⊼ θ) → θ ⊼ φ
    res = lb.ref(
        "res",
        "θ ⊼ φ",
        s2,
        ref="nic-isw1",
        note="nic-isw1",
    )

    return lb.build(res)


def prove_nic_iimp2(sys: System) -> Proof:
    """nic-iimp2: θ ⊼ ( χ ⊼ χ ).

    Inference form of nic-imp using nic-isw1 and nic-iimp1.
    (Contributed by Jeff Hoffman, 17-Nov-2007.)
    """
    lb = ProofBuilder(sys, "nic-iimp2")

    h1 = lb.hyp("nic-iimp2.1", "( φ ⊼ ψ ) ⊼ ( χ ⊼ χ )")
    h2 = lb.hyp("nic-iimp2.2", "θ ⊼ φ")

    # nic-isw1: from ( φ ⊼ ψ ) ⊼ ( χ ⊼ χ ) → ( χ ⊼ χ ) ⊼ ( φ ⊼ ψ )
    s1 = lb.ref(
        "s1",
        "( χ ⊼ χ ) ⊼ ( φ ⊼ ψ )",
        h1,
        ref="nic-isw1",
        note="nic-isw1",
    )

    # nic-iimp1: from s1 and h2 → θ ⊼ ( χ ⊼ χ )
    res = lb.ref(
        "res",
        "θ ⊼ ( χ ⊼ χ )",
        s1,
        h2,
        ref="nic-iimp1",
        note="nic-iimp1",
    )

    return lb.build(res)


def prove_nic_ich(sys: System) -> Proof:
    """nic-ich: φ ⊼ (χ ⊼ χ).

    Chained inference: from φ ⊼ (ψ ⊼ ψ) and ψ ⊼ (χ ⊼ χ), derive φ ⊼ (χ ⊼ χ).
    (Contributed by Jeff Hoffman, 17-Nov-2007.)
    """
    lb = ProofBuilder(sys, "nic-ich")

    h1 = lb.hyp("nic-ich.1", "φ ⊼ ( ψ ⊼ ψ )")
    h2 = lb.hyp("nic-ich.2", "ψ ⊼ ( χ ⊼ χ )")

    # nic-isw1: from ψ ⊼ (χ ⊼ χ), derive (χ ⊼ χ) ⊼ ψ
    s1 = lb.ref(
        "s1",
        "( χ ⊼ χ ) ⊼ ψ",
        h2,
        ref="nic-isw1",
        note="nic-isw1",
    )

    # nic-imp: from φ ⊼ (ψ ⊼ ψ), derive ((χ ⊼ χ) ⊼ ψ) ⊼ ((φ ⊼ (χ ⊼ χ)) ⊼ (φ ⊼ (χ ⊼ χ)))
    s2 = lb.ref(
        "s2",
        "( ( χ ⊼ χ ) ⊼ ψ ) ⊼ ( ( φ ⊼ ( χ ⊼ χ ) ) ⊼ ( φ ⊼ ( χ ⊼ χ ) ) )",
        h1,
        ref="nic-imp",
        note="nic-imp",
    )

    # nic-mp: from (χ ⊼ χ) ⊼ ψ and s2, derive φ ⊼ (χ ⊼ χ)
    res = lb.ref(
        "res",
        "φ ⊼ ( χ ⊼ χ )",
        s1,
        s2,
        ref="nic-mp",
        note="nic-mp",
    )

    return lb.build(res)


def prove_nic_idel(sys: System) -> Proof:
    """nic-idel: φ ⊼ (χ ⊼ χ).

    Inference to remove the trailing term.  From φ ⊼ (χ ⊼ ψ) derive φ ⊼ (χ ⊼ χ).
    (Contributed by Jeff Hoffman, 17-Nov-2007.)
    """
    lb = ProofBuilder(sys, "nic-idel")

    h = lb.hyp("nic-idel.1", "φ ⊼ ( χ ⊼ ψ )")

    # nic-id: χ ⊼ (χ ⊼ χ)
    s1 = lb.ref(
        "s1",
        "χ ⊼ ( χ ⊼ χ )",
        ref="nic-id",
        note="nic-id",
    )

    # nic-isw1: from χ ⊼ (χ ⊼ χ), derive (χ ⊼ χ) ⊼ χ
    s2 = lb.ref(
        "s2",
        "( χ ⊼ χ ) ⊼ χ",
        s1,
        ref="nic-isw1",
        note="nic-isw1",
    )

    # nic-imp: from φ ⊼ (χ ⊼ ψ), derive ((χ ⊼ χ) ⊼ χ) ⊼ ((φ ⊼ (χ ⊼ χ)) ⊼ (φ ⊼ (χ ⊼ χ)))
    s3 = lb.ref(
        "s3",
        "( ( χ ⊼ χ ) ⊼ χ ) ⊼ ( ( φ ⊼ ( χ ⊼ χ ) ) ⊼ ( φ ⊼ ( χ ⊼ χ ) ) )",
        h,
        ref="nic-imp",
        note="nic-imp",
    )

    # nic-mp: from (χ ⊼ χ) ⊼ χ and s3, derive φ ⊼ (χ ⊼ χ)
    res = lb.ref(
        "res",
        "φ ⊼ ( χ ⊼ χ )",
        s2,
        s3,
        ref="nic-mp",
        note="nic-mp",
    )

    return lb.build(res)


def prove_nic_idbl(sys: System) -> Proof:
    """nic-idbl: ( ψ ⊼ ψ ) ⊼ ( ( φ ⊼ φ ) ⊼ ( φ ⊼ φ ) ).

    Double the terms.  Since doubling is the same as negation, this can be
    viewed as a contraposition inference.
    (Contributed by Jeff Hoffman, 17-Nov-2007.)
    (Proof modification is discouraged.)  (New usage is discouraged.)
    """
    lb = ProofBuilder(sys, "nic-idbl")

    h1 = lb.hyp("nic-idbl.1", "φ ⊼ ( ψ ⊼ ψ )")

    # nic-imp: from φ ⊼ (ψ ⊼ ψ), derive (ψ ⊼ ψ) ⊼ ((φ ⊼ ψ) ⊼ (φ ⊼ ψ))
    s2 = lb.ref(
        "s2",
        "( ψ ⊼ ψ ) ⊼ ( ( φ ⊼ ψ ) ⊼ ( φ ⊼ ψ ) )",
        h1,
        ref="nic-imp",
        note="nic-imp",
    )

    # nic-imp: from φ ⊼ (ψ ⊼ ψ), derive (φ ⊼ ψ) ⊼ ((φ ⊼ φ) ⊼ (φ ⊼ φ))
    s4 = lb.ref(
        "s4",
        "( φ ⊼ ψ ) ⊼ ( ( φ ⊼ φ ) ⊼ ( φ ⊼ φ ) )",
        h1,
        ref="nic-imp",
        note="nic-imp",
    )

    # nic-ich: from s2 and s4, derive (ψ ⊼ ψ) ⊼ ((φ ⊼ φ) ⊼ (φ ⊼ φ))
    res = lb.ref(
        "res",
        "( ψ ⊼ ψ ) ⊼ ( ( φ ⊼ φ ) ⊼ ( φ ⊼ φ ) )",
        s2,
        s4,
        ref="nic-ich",
        note="nic-ich",
    )

    return lb.build(res)


def prove_nic_bi1(sys: System) -> Proof:
    """nic-bi1: φ ⊼ (ψ ⊼ ψ).

    Extract one side of a 'biconditional' from the NAND-based definition.
    (Contributed by Jeff Hoffman, 18-Nov-2007.)
    (Proof modification is discouraged.)  (New usage is discouraged.)
    """
    lb = ProofBuilder(sys, "nic-bi1")

    h = lb.hyp("nic-bi1.1", "( φ ⊼ ψ ) ⊼ ( ( φ ⊼ φ ) ⊼ ( ψ ⊼ ψ ) )")

    # nic-id: φ ⊼ ( φ ⊼ φ )
    s1 = lb.ref(
        "s1",
        "φ ⊼ ( φ ⊼ φ )",
        ref="nic-id",
        note="nic-id",
    )

    # nic-iimp1: from h and s1, derive φ ⊼ ( φ ⊼ ψ )
    s2 = lb.ref(
        "s2",
        "φ ⊼ ( φ ⊼ ψ )",
        h,
        s1,
        ref="nic-iimp1",
        note="nic-iimp1",
    )

    # nic-isw2: from s2, derive φ ⊼ ( ψ ⊼ φ )
    s3 = lb.ref(
        "s3",
        "φ ⊼ ( ψ ⊼ φ )",
        s2,
        ref="nic-isw2",
        note="nic-isw2",
    )

    # nic-idel: from s3, derive φ ⊼ ( ψ ⊼ ψ )
    res = lb.ref(
        "res",
        "φ ⊼ ( ψ ⊼ ψ )",
        s3,
        ref="nic-idel",
        note="nic-idel",
    )

    return lb.build(res)


def prove_nic_bi2(sys: System) -> Proof:
    """nic-bi2: ψ ⊼ (φ ⊼ φ).

    Extract the other side of an implication from a 'biconditional' definition.
    (Contributed by Jeff Hoffman, 18-Nov-2007.)
    (Proof modification is discouraged.)  (New usage is discouraged.)
    """
    lb = ProofBuilder(sys, "nic-bi2")

    h = lb.hyp("nic-bi2.1", "( φ ⊼ ψ ) ⊼ ( ( φ ⊼ φ ) ⊼ ( ψ ⊼ ψ ) )")

    # nic-isw2: from h, derive ( φ ⊼ ψ ) ⊼ ( ( ψ ⊼ ψ ) ⊼ ( φ ⊼ φ ) )
    s2 = lb.ref(
        "s2",
        "( φ ⊼ ψ ) ⊼ ( ( ψ ⊼ ψ ) ⊼ ( φ ⊼ φ ) )",
        h,
        ref="nic-isw2",
        note="nic-isw2",
    )

    # nic-id: ψ ⊼ ( ψ ⊼ ψ )
    s3 = lb.ref(
        "s3",
        "ψ ⊼ ( ψ ⊼ ψ )",
        ref="nic-id",
        note="nic-id",
    )

    # nic-iimp1: from s2 and s3, derive ψ ⊼ ( φ ⊼ ψ )
    s4 = lb.ref(
        "s4",
        "ψ ⊼ ( φ ⊼ ψ )",
        s2,
        s3,
        ref="nic-iimp1",
        note="nic-iimp1",
    )

    # nic-idel: from s4, derive ψ ⊼ ( φ ⊼ φ )
    res = lb.ref(
        "res",
        "ψ ⊼ ( φ ⊼ φ )",
        s4,
        ref="nic-idel",
        note="nic-idel",
    )

    return lb.build(res)


THEOREMS: Mapping[str, LemmaCtor] = {
    "pm4.83": prove_pm4_83,
    "pm5.1": prove_pm5_1,
    "pm5.3": prove_pm5_3,
    "pm5.32i": prove_pm5_32i,
    "pm5.32ri": prove_pm5_32ri,
    "pm5.36": prove_pm5_36,
    "pm5.33": prove_pm5_33,
    "pm5.42": prove_pm5_42,
    "pm5.44": prove_pm5_44,
    "pm5.21": prove_pm5_21,
    "pm5.35": prove_pm5_35,
    "pm5.32": prove_pm5_32,
    "pm3.3": prove_pm3_3,
    "orcanai": prove_orcanai,
    "pm3.2": prove_pm3_2,
    "pm3.22": prove_pm3_22,
    "ancom": prove_ancom,
    "ancomst": prove_ancomst,
    "pm3.2an3": prove_pm3_2an3,
    "pm3.33": prove_pm3_33,
    "3an4anass": prove_3an4anass,
    "3anan12": prove_3anan12,
    "3anan32": prove_3anan32,
    "3anan32OLD": prove_3anan32OLD,
    "3anass": prove_3anass,
    "3anim123d": prove_3anim123d,
    "3impa": prove_3impa,
    "3expa": prove_3expa,
    "3simpa": prove_3simpa,
    "mpd3an3": prove_mpd3an3,
    "mp3an3": prove_mp3an3,
    "biimp3a": prove_biimp3a,
    "expr": prove_expr,
    "expdimp": prove_expdimp,
    "expimpd": prove_expimpd,
    "3expia": prove_3expia,
    "ad4ant123": prove_ad4ant123,
    "ad5ant125OLD": prove_ad5ant125OLD,
    "impexp": prove_impexp,
    "imp": prove_imp,
    "intnan": prove_intnan,
    "intnanr": prove_intnanr,
    "intnanrd": prove_intnanrd,
    "intnand": prove_intnand,
    "adantr": prove_adantr,
    "adantrd": prove_adantrd,
    "adantrr": prove_adantrr,
    "simpl": prove_simpl,
    "simpld": prove_simpld,
    "simpr": prove_simpr,
    "simprl": prove_simprl,
    "simpr1l": prove_simpr1l,
    "simpr1r": prove_simpr1r,
    "sylancom": prove_sylancom,
    "birani": prove_birani,
    "bilani": prove_bilani,
    "simprrr": prove_simprrr,
    "simprll": prove_simprll,
    "simprrl": prove_simprrl,
    "biranri": prove_biranri,
    "bilanri": prove_bilanri,
    "impac": prove_impac,
    "impancom": prove_impancom,
    "impel": prove_impel,
    "impcom": prove_impcom,
    "impl": prove_impl,
    "pm3.4": prove_pm3_4,
    "pm3.34": prove_pm3_34,
    "pm3.35": prove_pm3_35,
    "pm3.41": prove_pm3_41,
    "pm3.42": prove_pm3_42,
    "pm3.31": prove_pm3_31,
    "pm3.43": prove_pm3_43,
    "pm3.45": prove_pm3_45,
    "pm4.14": prove_pm4_14,
    "pm4.15": prove_pm4_15,
    "pm4.63": prove_pm4_63,
    "pm4.67": prove_pm4_67,
    "pm4.76": prove_pm4_76,
    "pm4.82": prove_pm4_82,
    "pm4.87": prove_pm4_87,
    "impd": prove_impd,
    "imp31": prove_imp31,
    "imp41": prove_imp41,
    "imp42": prove_imp42,
    "imp43": prove_imp43,
    "imp44": prove_imp44,
    "imp45": prove_imp45,
    "3imp": prove_3imp,
    "3imp231": prove_3imp231,
    "3imp21": prove_3imp21,
    "3imp31": prove_3imp31,
    "3com12": prove_3com12,
    "3pm3.2i": prove_3pm3_2i,
    "ancl": prove_ancl,
    "ancld": prove_ancld,
    "ancli": prove_ancli,
    "ancrd": prove_ancrd,
    "anc2l": prove_anc2l,
    "anc2ri": prove_anc2ri,
    "imdistan": prove_imdistan,
    "imdistani": prove_imdistani,
    "an31s": prove_an31s,
    "an13s": prove_an13s,
    "anasss": prove_anasss,
    "anass": prove_anass,
    "anbi1": prove_anbi1,
    "anbi1i": prove_anbi1i,
    "anbi2i": prove_anbi2i,
    "anbiim": prove_anbiim,
    "anbiimOLD": prove_anbiimOLD,
    "bi23imp13": prove_bi23imp13,
    "bi2bian9": prove_bi2bian9,
    "bianass": prove_bianass,
    "bianassc": prove_bianassc,
    "bianbi": prove_bianbi,
    "bianir": prove_bianir,
    "biancomi": prove_biancomi,
    "anbi2ci": prove_anbi2ci,
    "anbi12d": prove_anbi12d,
    "anbi2d": prove_anbi2d,
    "biancomd": prove_biancomd,
    "bianim": prove_bianim,
    "biantr": prove_biantr,
    "biantru": prove_biantru,
    "biantrud": prove_biantrud,
    "3imp1": prove_3imp1,
    "3an1rs": prove_3an1rs,
    "3imp2": prove_3imp2,
    "3jca": prove_3jca,
    "imp32": prove_imp32,
    "jca": prove_jca,
    "jcai": prove_jcai,
    "jctir": prove_jctir,
    "jctil": prove_jctil,
    "jctl": prove_jctl,
    "jctr": prove_jctr,
    "jcad": prove_jcad,
    "jca2": prove_jca2,
    "jctird": prove_jctird,
    "syl2an2": prove_syl2an2,
    "dfbi2": prove_dfbi2,
    "dfbi": prove_dfbi,
    "annotanannot": prove_annotanannot,
    "anidm": prove_anidm,
    "anidmdbi": prove_anidmdbi,
    "pm4.71": prove_pm4_71,
    "pm4.24": prove_pm4_24,
    "pm4.38": prove_pm4_38,
    "an3andi": prove_an3andi,
    "nanan": prove_nanan,
    "nannan": prove_nannan,
    "nic-mp": prove_nic_mp,
    "nic-mpALT": prove_nic_mp_alt,
    "nic-ax": prove_nic_ax,
    "nic-axALT": prove_nic_axALT,
    "nic-id": prove_nic_id,
    "nic-swap": prove_nic_swap,
    "nic-bijust": prove_nic_bijust,
    "nic-isw1": prove_nic_isw1,
    "nic-ich": prove_nic_ich,
    "nic-idel": prove_nic_idel,
    "lukshef-ax1": prove_lukshef_ax1,
    "lukshefth1": prove_lukshefth1,
    "lukshefth2": prove_lukshefth2,
}

__all__ = [
    "prove_abai",
    "LemmaCtor",
    "THEOREMS",
    "prove_pm3_22",
    "prove_ancom",
    "prove_pm3_3",
    "prove_orcanai",
    "prove_pm3_33",
    "prove_3impa",
    "prove_3simpa",
    "prove_3expa",
    "prove_mpd3an3",
    "prove_mp3an3",
    "prove_mpanr2",
    "prove_biimp3a",
    "prove_imdistan",
    "prove_impexp",
    "prove_imp",
    "prove_adantr",
    "prove_adantrd",
    "prove_simpl",
    "prove_adantrr",
    "prove_3adant3",
    "prove_simpld",
    "prove_simpr",
    "prove_simprl",
    "prove_simpr1l",
    "prove_simpr1r",
    "prove_simpr21",
    "prove_simpr22",
    "prove_birani",
    "prove_bilani",
    "prove_simprrr",
    "prove_simprll",
    "prove_simprrl",
    "prove_biranri",
    "prove_impac",
    "prove_bilanri",
    "prove_impancom",
    "prove_impel",
    "prove_impcom",
    "prove_impl",
    "prove_intnan",
    "prove_intnanr",
    "prove_intnanrd",
    "prove_intnand",
    "prove_pm3_4",
    "prove_pm3_34",
    "prove_pm3_35",
    "prove_pm3_41",
    "prove_pm3_42",
    "prove_pm3_31",
    "prove_pm3_43",
    "prove_pm3_45",
    "prove_impd",
    "prove_sylan9",
    "prove_syland",
    "prove_sylancom",
    "prove_pm5_1",
    "prove_pm5_3",
    "prove_pm5_21",
    "prove_pm5_31",
    "prove_pm5_35",
    "prove_pm5_32",
    "prove_pm5_32i",
    "prove_pm5_32ri",
    "prove_pm5_33",
    "prove_pm5_32rd",
    "prove_pm5_36",
    "prove_pm5_42",
    "prove_pm5_44",
    "prove_sylani",
    "prove_syl2an2",
    "prove_imp31",
    "prove_imp41",
    "prove_imp42",
    "prove_imp43",
    "prove_imp44",
    "prove_imp45",
    "prove_3imp",
    "prove_3imp231",
    "prove_3imp21",
    "prove_3imp31",
    "prove_3com12",
    "prove_bi23imp13",
    "prove_bi2bian9",
    "prove_bianass",
    "prove_bianassc",
    "prove_bianbi",
    "prove_bianir",
    "prove_biancomi",
    "prove_anbi2ci",
    "prove_anbi12d",
    "prove_anbi2d",
    "prove_biancomd",
    "prove_bianim",
    "prove_biantr",
    "prove_biantru",
    "prove_biantrud",
    "prove_3imp1",
    "prove_3an1rs",
    "prove_3anidm12",
    "prove_3anim123d",
    "prove_3anidm13",
    "prove_3anidm",
    "prove_3imp2",
    "prove_3jca",
    "prove_3pm3_2i",
    "prove_an31",
    "prove_an31s",
    "prove_an13s",
    "prove_an21",
    "prove_anasss",
    "prove_anass",
    "prove_anbi1",
    "prove_anbi1i",
    "prove_anbi2i",
    "prove_anbiim",
    "prove_anbiimOLD",
    "prove_imp32",
    "prove_jca",
    "prove_jcai",
    "prove_jctil",
    "prove_jctl",
    "prove_jctr",
    "prove_jctir",
    "prove_jcad",
    "prove_jca2",
    "prove_jca32",
    "prove_jctird",
    "prove_pm4_83",
    "prove_pm4_14",
    "prove_pm4_15",
    "prove_pm4_63",
    "prove_pm4_67",
    "prove_pm4_76",
    "prove_pm4_82",
    "prove_pm4_87",
    "prove_impcomd",
    "prove_ancomsd",
    "prove_ancomst",
    "prove_anim2d",
    "prove_anim12d",
    "prove_expr",
    "prove_expdimp",
    "prove_expimpd",
    "prove_3expia",
    "prove_ad4ant123",
    "prove_ad5ant125OLD",
    "prove_imp4b",
    "prove_imp4c",
    "prove_imp5d",
    "prove_imp5a",
    "prove_imp5g",
    "prove_dfbi2",
    "prove_dfbi",
    "prove_3impd",
    "prove_anabsi5",
    "prove_anabsi6",
    "prove_anabsi7",
    "prove_anabsi8",
    "prove_pm4_71",
    "prove_pm4_71ri",
    "prove_pm4_24",
    "prove_pm4_38",
    "prove_annotanannot",
    "prove_syldbl2",
    "prove_simplbda",
    "prove_an3andi",
    "prove_nanan",
    "prove_nannan",
    "prove_nic_mp",
    "prove_nic_mp_alt",
    "prove_nic_ax",
    "prove_nic_axALT",
    "prove_nic_id",
    "prove_nic_swap",
    "prove_nic_bijust",
    "prove_nic_isw1",
    "prove_nic_ich",
    "prove_nic_idel",
    "prove_lukshef_ax1",
    "prove_lukshefth1",
    "prove_lukshefth2",
]


def prove_anabsi5(sys: System) -> Proof:
    """anabsi5: ( φ ∧ ψ ) → χ. Hyp: φ → ( ( φ ∧ ψ ) → χ ).

    Inference combining simpl and mpcom.
    (Contributed by NM, 9-Apr-1996.)
    """
    lb = ProofBuilder(sys, "anabsi5")
    h = lb.hyp("anabsi5.1", "φ → ( ( φ ∧ ψ ) → χ )")
    s_simpl = lb.ref("s_simpl", "( φ ∧ ψ ) → φ", ref="simpl", note="simpl")
    res = lb.ref("res", "( φ ∧ ψ ) → χ", s_simpl, h, ref="mpcom", note="mpcom")
    return lb.build(res)


def prove_anabsi6(sys: System) -> Proof:
    """anabsi6: ( φ ∧ ψ ) → χ. Hyp: φ → ( ( ψ ∧ φ ) → χ ).

    Inference combining ancomsd and anabsi5.
    (Contributed by NM, 9-Apr-1996.)
    """
    lb = ProofBuilder(sys, "anabsi6")
    h = lb.hyp("anabsi6.1", "φ → ( ( ψ ∧ φ ) → χ )")
    s1 = lb.ref("s1", "φ → ( ( φ ∧ ψ ) → χ )", h, ref="ancomsd", note="ancomsd")
    res = lb.ref("res", "( φ ∧ ψ ) → χ", s1, ref="anabsi5", note="anabsi5")
    return lb.build(res)


def prove_anabsi7(sys: System) -> Proof:
    """anabsi7: ( φ ∧ ψ ) → χ. Hyp: ψ → ( ( φ ∧ ψ ) → χ ).

    Inference combining ancomsd, anabsi6 and ancoms.
    (Contributed by NM, 9-Apr-1996.)
    """
    lb = ProofBuilder(sys, "anabsi7")
    h = lb.hyp("anabsi7.1", "ψ → ( ( φ ∧ ψ ) → χ )")
    s2 = lb.ref("s2", "( ψ ∧ φ ) → χ", h, ref="anabsi6", note="anabsi6")
    res = lb.ref("res", "( φ ∧ ψ ) → χ", s2, ref="ancoms", note="ancoms")
    return lb.build(res)


def prove_anabsi8(sys: System) -> Proof:
    """anabsi8: ( φ ∧ ψ ) → χ. Hyp: ψ → ( ( ψ ∧ φ ) → χ ).

    Inference combining anabsi5 and ancoms.
    (Contributed by NM, 9-Apr-1996.)
    """
    lb = ProofBuilder(sys, "anabsi8")
    h = lb.hyp("anabsi8.1", "ψ → ( ( ψ ∧ φ ) → χ )")
    s1 = lb.ref("s1", "( ψ ∧ φ ) → χ", h, ref="anabsi5", note="anabsi5")
    res = lb.ref("res", "( φ ∧ ψ ) → χ", s1, ref="ancoms", note="ancoms")
    return lb.build(res)


def prove_anabs1(sys: System) -> Proof:
    """anabs1: ( ( φ ∧ ψ ) ∧ φ ) ↔ ( φ ∧ ψ ).

    Conjunction absorption — a conjunction within a conjunction
    absorbs the outer right conjunct.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "anabs1")

    # simpl: ( φ ∧ ψ ) → φ
    s_simpl = lb.ref("s_simpl", "( φ ∧ ψ ) → φ", ref="simpl", note="simpl")

    # pm4.71i s_simpl: ( φ ∧ ψ ) ↔ ( ( φ ∧ ψ ) ∧ φ )
    s_pm4_71i = lb.ref(
        "s_pm4_71i",
        "( φ ∧ ψ ) ↔ ( ( φ ∧ ψ ) ∧ φ )",
        s_simpl,
        ref="pm4.71i",
        note="pm4.71i",
    )

    # bicomi s_pm4_71i: ( ( φ ∧ ψ ) ∧ φ ) ↔ ( φ ∧ ψ )
    res = lb.ref(
        "res",
        "( ( φ ∧ ψ ) ∧ φ ) ↔ ( φ ∧ ψ )",
        s_pm4_71i,
        ref="bicomi",
        note="bicomi",
    )

    return lb.build(res)


def prove_anabs5(sys: System) -> Proof:
    """anabs5: ( φ ∧ ( φ ∧ ψ ) ) ↔ ( φ ∧ ψ ).

    Conjunction absorption — a conjunction within a conjunction
    absorbs the outer conjunct.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "anabs5")

    # ibar: φ → ( ψ ↔ ( φ ∧ ψ ) )
    s1 = lb.ref(
        "s1",
        "φ → ( ψ ↔ ( φ ∧ ψ ) )",
        ref="ibar",
        note="ibar",
    )

    # bicomd s1: φ → ( ( φ ∧ ψ ) ↔ ψ )
    s2 = lb.ref(
        "s2",
        "φ → ( ( φ ∧ ψ ) ↔ ψ )",
        s1,
        ref="bicomd",
        note="bicomd",
    )

    # pm5.32i s2: ( φ ∧ ( φ ∧ ψ ) ) ↔ ( φ ∧ ψ )
    res = lb.ref(
        "res",
        "( φ ∧ ( φ ∧ ψ ) ) ↔ ( φ ∧ ψ )",
        s2,
        ref="pm5.32i",
        note="pm5.32i",
    )

    return lb.build(res)


def prove_anabs7(sys: System) -> Proof:
    """anabs7: ( ψ ∧ ( φ ∧ ψ ) ) ↔ ( φ ∧ ψ ).

    Conjunction absorption — a conjunction within a conjunction
    absorbs the outer left conjunct.
    (Contributed by NM, 12-Mar-1995.)
    """
    lb = ProofBuilder(sys, "anabs7")

    # simpr: ( φ ∧ ψ ) → ψ
    s_simpr = lb.ref(
        "s_simpr",
        "( φ ∧ ψ ) → ψ",
        ref="simpr",
        note="simpr",
    )

    # pm4.71ri s_simpr: ( φ ∧ ψ ) ↔ ( ψ ∧ ( φ ∧ ψ ) )
    s_pm4_71ri = lb.ref(
        "s_pm4_71ri",
        "( φ ∧ ψ ) ↔ ( ψ ∧ ( φ ∧ ψ ) )",
        s_simpr,
        ref="pm4.71ri",
        note="pm4.71ri",
    )

    # bicomi s_pm4_71ri: ( ψ ∧ ( φ ∧ ψ ) ) ↔ ( φ ∧ ψ )
    res = lb.ref(
        "res",
        "( ψ ∧ ( φ ∧ ψ ) ) ↔ ( φ ∧ ψ )",
        s_pm4_71ri,
        ref="bicomi",
        note="bicomi",
    )

    return lb.build(res)


def prove_syldbl2(sys: System) -> Proof:
    """syldbl2: ( φ ∧ ψ ) → θ. Hyp: ( φ ∧ ψ ) → ( ψ → θ ).

    Syllogism deduction with two hypotheses (generalization of syl2anb).
    (Contributed by NM, 30-Jul-1995.)
    """
    lb = ProofBuilder(sys, "syldbl2")
    h = lb.hyp("syldbl2.1", "( φ ∧ ψ ) → ( ψ → θ )")
    s1 = lb.ref("s1", "ψ → ( ( φ ∧ ψ ) → θ )", h, ref="com12", note="com12")
    res = lb.ref("res", "( φ ∧ ψ ) → θ", s1, ref="anabsi7", note="anabsi7")
    return lb.build(res)


def prove_3anidm12(sys: System) -> Proof:
    """3anidm12: ( φ ∧ ψ ) → χ. Hyp: ( φ ∧ φ ∧ ψ ) → χ.



    Deduction form where the first two conjuncts of a 3-ary hypothesis are
    the same, allowing one conjunct to be dropped.
    (Contributed by NM, 24-Feb-2005.)
    """
    lb = ProofBuilder(sys, "3anidm12")
    h = lb.hyp("3anidm12.1", "( φ ∧ φ ∧ ψ ) → χ")
    s1 = lb.ref(
        "s1",
        "φ → ( ( φ ∧ ψ ) → χ )",
        h,
        ref="3expib",
        note="3expib 3anidm12.1",
    )
    res = lb.ref(
        "res",
        "( φ ∧ ψ ) → χ",
        s1,
        ref="anabsi5",
        note="anabsi5 s1",
    )
    return lb.build(res)


def prove_3anidm13(sys: System) -> Proof:
    """3anidm13: ( φ ∧ ψ ) → χ. Hyp: ( φ ∧ ψ ∧ φ ) → χ.

    Deduction form where the first and third conjuncts of a 3-ary hypothesis
    are the same, allowing one conjunct to be dropped.
    (Contributed by NM, 24-Feb-2005.)
    """
    lb = ProofBuilder(sys, "3anidm13")
    h = lb.hyp("3anidm13.1", "( φ ∧ ψ ∧ φ ) → χ")
    s1 = lb.ref(
        "s1",
        "( φ ∧ φ ∧ ψ ) → χ",
        h,
        ref="3com23",
        note="3com23 3anidm13.1",
    )
    res = lb.ref(
        "res",
        "( φ ∧ ψ ) → χ",
        s1,
        ref="3anidm12",
        note="3anidm12 s1",
    )
    return lb.build(res)


def prove_3anidm(sys: System) -> Proof:
    """3anidm: ( φ ∧ φ ∧ φ ) ↔ φ.

    Triple idempotence of conjunction. A conjunction of three copies
    of the same proposition is equivalent to that proposition.
    (Contributed by NM, 25-Jun-2002.)
    """
    lb = ProofBuilder(sys, "3anidm")

    # df-3an: ( φ ∧ φ ∧ φ ) ↔ ( ( φ ∧ φ ) ∧ φ )
    df3an = lb.ref(
        "df3an",
        "( φ ∧ φ ∧ φ ) ↔ ( ( φ ∧ φ ) ∧ φ )",
        ref="df-3an",
        note="df-3an",
    )

    # anabs1: ( ( φ ∧ φ ) ∧ φ ) ↔ ( φ ∧ φ )
    anabs1 = lb.ref(
        "anabs1",
        "( ( φ ∧ φ ) ∧ φ ) ↔ ( φ ∧ φ )",
        ref="anabs1",
        note="anabs1",
    )

    # anidm: ( φ ∧ φ ) ↔ φ
    anidm = lb.ref(
        "anidm",
        "( φ ∧ φ ) ↔ φ",
        ref="anidm",
        note="anidm",
    )

    # 3bitri: chain all three biconditionals
    res = lb.ref(
        "res",
        "( φ ∧ φ ∧ φ ) ↔ φ",
        df3an,
        anabs1,
        anidm,
        ref="3bitri",
        note="3bitri",
    )

    return lb.build(res)


def prove_simplbda(sys: System) -> Proof:
    """simplbda: ( φ ∧ ψ ) → θ.

    From φ → (ψ ↔ (χ ∧ θ)), deduce (φ ∧ ψ) → θ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "simplbda")
    h1 = lb.hyp("simplbda.1", "φ → ( ψ ↔ ( χ ∧ θ ) )")

    # biimpa: from φ → (ψ ↔ (χ ∧ θ)) get (φ ∧ ψ) → (χ ∧ θ)
    s1 = lb.ref(
        "s1",
        "( φ ∧ ψ ) → ( χ ∧ θ )",
        h1,
        ref="biimpa",
        note="biimpa simplbda.1",
    )

    # simprd: from (φ ∧ ψ) → (χ ∧ θ) get (φ ∧ ψ) → θ
    res = lb.ref(
        "res",
        "( φ ∧ ψ ) → θ",
        s1,
        ref="simprd",
        note="simprd s1",
    )

    return lb.build(res)


def prove_bitr(sys: System) -> Proof:
    """bitr: ( ( φ ↔ ψ ) ∧ ( ψ ↔ χ ) ) → ( φ ↔ χ ).

    Transitivity of the biconditional: from a pair of biconditionals
    conjoined, deduce a new biconditional linking the two outer
    propositions.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "bitr")

    # bibi1: ( ( φ ↔ ψ ) → ( ( φ ↔ χ ) ↔ ( ψ ↔ χ ) ) )
    s1 = lb.ref(
        "s1",
        "( ( φ ↔ ψ ) → ( ( φ ↔ χ ) ↔ ( ψ ↔ χ ) ) )",
        ref="bibi1",
        note="bibi1",
    )

    # biimpar: ( ( ( φ ↔ ψ ) ∧ ( ψ ↔ χ ) ) → ( φ ↔ χ ) )
    res = lb.ref(
        "res",
        "( ( ( φ ↔ ψ ) ∧ ( ψ ↔ χ ) ) → ( φ ↔ χ ) )",
        s1,
        ref="biimpar",
        note="biimpar",
    )

    return lb.build(res)


def prove_syl2and(sys: System) -> Proof:
    """syl2and: φ → ((ψ ∧ θ) → η).

    Syllogism with two conjunctions in the antecedent.  If φ implies ψ → χ,
    φ implies θ → τ, and φ implies (χ ∧ τ) → η, then φ implies (ψ ∧ θ) → η.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "syl2and")
    h1 = lb.hyp("syl2and.1", "φ → ( ψ → χ )")
    h2 = lb.hyp("syl2and.2", "φ → ( θ → τ )")
    h3 = lb.hyp("syl2and.3", "φ → ( ( χ ∧ τ ) → η )")

    # ancomsd: swap the conjuncts in the consequent of h3
    s1 = lb.ref(
        "s1",
        "φ → ( ( τ ∧ χ ) → η )",
        h3,
        ref="ancomsd",
        note="ancomsd syl2and.3",
    )

    # syland: combine h2 and s1
    s2 = lb.ref(
        "s2",
        "φ → ( ( θ ∧ χ ) → η )",
        h2,
        s1,
        ref="syland",
        note="syland syl2and.2, s1",
    )

    # sylan2d: combine h1 and s2
    s3 = lb.ref(
        "s3",
        "φ → ( ( θ ∧ ψ ) → η )",
        h1,
        s2,
        ref="sylan2d",
        note="sylan2d syl2and.1, s2",
    )

    # ancomsd: swap the conjuncts for the final result
    res = lb.ref(
        "res",
        "φ → ( ( ψ ∧ θ ) → η )",
        s3,
        ref="ancomsd",
        note="ancomsd s3",
    )

    return lb.build(res)


def prove_anim2d(sys: System) -> Proof:
    """anim2d: φ → ( ( θ ∧ ψ ) → ( θ ∧ χ ) ).

    Deduction conjoining an antecedent to both sides of a conditional.
    From φ → ( ψ → χ ), deduce φ → ( ( θ ∧ ψ ) → ( θ ∧ χ ) ).
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "anim2d")
    h = lb.hyp("anim2d.1", "φ → ( ψ → χ )")
    s1 = lb.ref("s1", "φ → ( θ → θ )", ref="idd", note="idd")
    res = lb.ref(
        "res",
        "φ → ( ( θ ∧ ψ ) → ( θ ∧ χ ) )",
        s1,
        h,
        ref="anim12d",
        note="anim12d",
    )
    return lb.build(res)


def prove_anim12d(sys: System) -> Proof:
    """anim12d: φ → ( ( ψ ∧ θ ) → ( χ ∧ τ ) ).

    Deduction conjoining both antecedents and consequents.
    From φ → ( ψ → χ ) and φ → ( θ → τ ), deduce
    φ → ( ( ψ ∧ θ ) → ( χ ∧ τ ) ).
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "anim12d")
    h1 = lb.hyp("anim12d.1", "φ → ( ψ → χ )")
    h2 = lb.hyp("anim12d.2", "φ → ( θ → τ )")
    s_idd = lb.ref(
        "s_idd",
        "φ → ( ( χ ∧ τ ) → ( χ ∧ τ ) )",
        ref="idd",
        note="idd",
    )
    res = lb.ref(
        "res",
        "φ → ( ( ψ ∧ θ ) → ( χ ∧ τ ) )",
        h1,
        h2,
        s_idd,
        ref="syl2and",
        note="syl2and",
    )
    return lb.build(res)


def prove_anim12d1(sys: System) -> Proof:
    """anim12d1: φ → ( ( ψ ∧ θ ) → ( χ ∧ τ ) ).

    Deduction conjoining antecedents and consequents.
    From φ → ( ψ → χ ) and θ → τ, deduce
    φ → ( ( ψ ∧ θ ) → ( χ ∧ τ ) ).
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "anim12d1")
    h1 = lb.hyp("anim12d1.1", "φ → ( ψ → χ )")
    h2 = lb.hyp("anim12d1.2", "θ → τ")

    # a1i: φ → ( θ → τ )
    s1 = lb.ref(
        "s1",
        "φ → ( θ → τ )",
        h2,
        ref="a1i",
        note="a1i",
    )

    # anim12d: φ → ( ( ψ ∧ θ ) → ( χ ∧ τ ) )
    res = lb.ref(
        "res",
        "φ → ( ( ψ ∧ θ ) → ( χ ∧ τ ) )",
        h1,
        s1,
        ref="anim12d",
        note="anim12d",
    )

    return lb.build(res)


def prove_anim1d(sys: System) -> Proof:
    """anim1d: φ → ( ( ψ ∧ θ ) → ( χ ∧ θ ) ).

    Deduction conjoining a consequent to both sides of a conditional.
    From φ → ( ψ → χ ), deduce φ → ( ( ψ ∧ θ ) → ( χ ∧ θ ) ).
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "anim1d")
    h = lb.hyp("anim1d.1", "φ → ( ψ → χ )")
    s1 = lb.ref("s1", "φ → ( θ → θ )", ref="idd", note="idd")
    res = lb.ref(
        "res",
        "φ → ( ( ψ ∧ θ ) → ( χ ∧ θ ) )",
        h,
        s1,
        ref="anim12d",
        note="anim12d",
    )
    return lb.build(res)


def prove_anim12dan(sys: System) -> Proof:
    """anim12dan: ( φ ∧ ( ψ ∧ θ ) ) → ( χ ∧ τ ).

    Deduction conjoining both antecedents and consequents, importation form.
    From ( φ ∧ ψ ) → χ and ( φ ∧ θ ) → τ, deduce
    ( φ ∧ ( ψ ∧ θ ) ) → ( χ ∧ τ ).
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "anim12dan")
    h1 = lb.hyp("anim12dan.1", "( φ ∧ ψ ) → χ")
    h2 = lb.hyp("anim12dan.2", "( φ ∧ θ ) → τ")

    # ex: φ → ( ψ → χ )
    s1 = lb.ref(
        "s1",
        "φ → ( ψ → χ )",
        h1,
        ref="ex",
        note="ex",
    )

    # ex: φ → ( θ → τ )
    s2 = lb.ref(
        "s2",
        "φ → ( θ → τ )",
        h2,
        ref="ex",
        note="ex",
    )

    # anim12d: φ → ( ( ψ ∧ θ ) → ( χ ∧ τ ) )
    s3 = lb.ref(
        "s3",
        "φ → ( ( ψ ∧ θ ) → ( χ ∧ τ ) )",
        s1,
        s2,
        ref="anim12d",
        note="anim12d",
    )

    # imp: ( φ ∧ ( ψ ∧ θ ) ) → ( χ ∧ τ )
    res = lb.ref(
        "res",
        "( φ ∧ ( ψ ∧ θ ) ) → ( χ ∧ τ )",
        s3,
        ref="imp",
        note="imp",
    )

    return lb.build(res)


def prove_ad5ant2345(sys: System) -> Proof:
    r"""ad5ant2345: ( ( ( ( ( η ∧ φ ) ∧ ψ ) ∧ χ ) ∧ θ ) → τ.

    Deduction adding a conjunct to the antecedent.  Given
    ( ( ( ( φ ∧ ψ ) ∧ χ ) ∧ θ ) → τ, derive
    ( ( ( ( ( η ∧ φ ) ∧ ψ ) ∧ χ ) ∧ θ ) → τ.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "ad5ant2345")
    h1 = lb.hyp("ad5ant2345.1", "( ( ( ( φ ∧ ψ ) ∧ χ ) ∧ θ ) → τ )")

    # exp41: ( ( ( ( φ ∧ ψ ) ∧ χ ) ∧ θ ) → τ ) → ( φ → ( ψ → ( χ → ( θ → τ ) ) ) )
    s1 = lb.ref(
        "s1",
        "( φ → ( ψ → ( χ → ( θ → τ ) ) ) )",
        h1,
        ref="exp41",
        note="exp41 ad5ant2345.1",
    )

    # adantl: ( φ → ( ψ → ( χ → ( θ → τ ) ) ) ) → ( ( η ∧ φ ) → ( ψ → ( χ → ( θ → τ ) ) ) )
    s2 = lb.ref(
        "s2",
        "( ( η ∧ φ ) → ( ψ → ( χ → ( θ → τ ) ) ) )",
        s1,
        ref="adantl",
        note="adantl s1",
    )

    # imp41: ( ( η ∧ φ ) → ( ψ → ( χ → ( θ → τ ) ) ) ) → ( ( ( ( ( η ∧ φ ) ∧ ψ ) ∧ χ ) ∧ θ ) → τ )
    res = lb.ref(
        "res",
        "( ( ( ( ( η ∧ φ ) ∧ ψ ) ∧ χ ) ∧ θ ) → τ )",
        s2,
        ref="imp41",
        note="imp41 s2",
    )

    return lb.build(res)


def prove_imdistand(sys: System) -> Proof:
    """imdistand: φ → ( ( ψ ∧ χ ) → ( ψ ∧ θ ) ).

    Hyp: φ → ( ψ → ( χ → θ ) )
    Concl: φ → ( ( ψ ∧ χ ) → ( ψ ∧ θ ) )

    Deduction form of imdistan.
    """
    lb = ProofBuilder(sys, "imdistand")
    h1 = lb.hyp("imdistand.1", "φ → ( ψ → ( χ → θ ) )")
    s1 = lb.ref(
        "s1",
        "( ψ → ( χ → θ ) ) ↔ ( ( ψ ∧ χ ) → ( ψ ∧ θ ) )",
        ref="imdistan",
        note="imdistan",
    )
    res = lb.ref("res", "φ → ( ( ψ ∧ χ ) → ( ψ ∧ θ ) )", h1, s1, ref="sylib", note="sylib")
    return lb.build(res)


def prove_imdistanda(sys: System) -> Proof:
    """imdistanda: φ → ( ( ψ ∧ χ ) → ( ψ ∧ θ ) ).

    Hyp: imdistanda.1 |- ( ( φ ∧ ψ ) → ( χ → θ ) )
    Concl: |- ( φ → ( ( ψ ∧ χ ) → ( ψ ∧ θ ) ) )

    Deduction form of imdistand with an antecedent joined by conjunction.
    """
    lb = ProofBuilder(sys, "imdistanda")
    h1 = lb.hyp("imdistanda.1", "( ( φ ∧ ψ ) → ( χ → θ ) )")
    s1 = lb.ref("s1", "φ → ( ψ → ( χ → θ ) )", h1, ref="ex", note="ex imdistanda.1")
    res = lb.ref("res", "φ → ( ( ψ ∧ χ ) → ( ψ ∧ θ ) )", s1, ref="imdistand", note="imdistand s1")
    return lb.build(res)


def prove_an21(sys: System) -> Proof:
    """an21: ( ( φ ∧ ψ ) ∧ χ ) ↔ ( ψ ∧ ( φ ∧ χ ) ).

    Swap two conjuncts.
    """
    lb = ProofBuilder(sys, "an21")

    # biid: ( ( φ ∧ χ ) ↔ ( φ ∧ χ ) )
    s1 = lb.ref(
        "s1",
        "( ( φ ∧ χ ) ↔ ( φ ∧ χ ) )",
        ref="biid",
        note="biid",
    )

    # bianassc: ( ψ ∧ ( φ ∧ χ ) ) ↔ ( ( φ ∧ ψ ) ∧ χ )
    s2 = lb.ref(
        "s2",
        "( ψ ∧ ( φ ∧ χ ) ) ↔ ( ( φ ∧ ψ ) ∧ χ )",
        s1,
        ref="bianassc",
        note="bianassc",
    )

    # bicomi: ( ( φ ∧ ψ ) ∧ χ ) ↔ ( ψ ∧ ( φ ∧ χ ) )
    res = lb.ref(
        "res",
        "( ( φ ∧ ψ ) ∧ χ ) ↔ ( ψ ∧ ( φ ∧ χ ) )",
        s2,
        ref="bicomi",
        note="bicomi",
    )

    return lb.build(res)


def prove_an32(sys: System) -> Proof:
    """an32: ( ( φ ∧ ψ ) ∧ χ ) ↔ ( ( φ ∧ χ ) ∧ ψ ).

    Swap the second and third conjuncts.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "an32")

    # an21: ( ( φ ∧ ψ ) ∧ χ ) ↔ ( ψ ∧ ( φ ∧ χ ) )
    s1 = lb.ref(
        "s1",
        "( ( φ ∧ ψ ) ∧ χ ) ↔ ( ψ ∧ ( φ ∧ χ ) )",
        ref="an21",
        note="an21",
    )

    # biancomi: ( ( φ ∧ ψ ) ∧ χ ) ↔ ( ( φ ∧ χ ) ∧ ψ )
    res = lb.ref(
        "res",
        "( ( φ ∧ ψ ) ∧ χ ) ↔ ( ( φ ∧ χ ) ∧ ψ )",
        s1,
        ref="biancomi",
        note="biancomi",
    )

    return lb.build(res)


def prove_an32s(sys: System) -> Proof:
    """an32s: ( ( φ ∧ χ ) ∧ ψ ) → θ.

    Hyp: an32s.1 |- ( ( ( φ ∧ ψ ) ∧ χ ) → θ ).
    Concl: |- ( ( ( φ ∧ χ ) ∧ ψ ) → θ ).

    Inference associated with ~ an32 .  (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "an32s")
    h1 = lb.hyp("an32s.1", "( ( ( φ ∧ ψ ) ∧ χ ) → θ )")

    # an32: ( ( φ ∧ ψ ) ∧ χ ) ↔ ( ( φ ∧ χ ) ∧ ψ )
    s1 = lb.ref(
        "s1",
        "( ( φ ∧ ψ ) ∧ χ ) ↔ ( ( φ ∧ χ ) ∧ ψ )",
        ref="an32",
        note="an32",
    )

    # sylbir: from ( ψ ↔ φ ) and ( ψ → χ ), derive ( φ → χ )
    res = lb.ref(
        "res",
        "( ( ( φ ∧ χ ) ∧ ψ ) → θ )",
        s1,
        h1,
        ref="sylbir",
        note="sylbir",
    )

    return lb.build(res)


def prove_an2anr(sys: System) -> Proof:
    """an2anr: ( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ) ↔ ( ( ψ ∧ φ ) ∧ ( θ ∧ χ ) ).

    Swap conjuncts in both sides of a conjunction.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "an2anr")
    s1 = lb.ref("s1", "( φ ∧ ψ ) ↔ ( ψ ∧ φ )", ref="ancom", note="ancom")
    s2 = lb.ref("s2", "( χ ∧ θ ) ↔ ( θ ∧ χ )", ref="ancom", note="ancom")
    res = lb.ref(
        "res",
        "( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ) ↔ ( ( ψ ∧ φ ) ∧ ( θ ∧ χ ) )",
        s1,
        s2,
        ref="anbi12i",
        note="anbi12i",
    )
    return lb.build(res)


def prove_an4(sys: System) -> Proof:
    """an4: ( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ) ↔ ( ( φ ∧ χ ) ∧ ( ψ ∧ θ ) ).

    Rearrange conjuncts in a nested conjunction.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "an4")

    # anass: ( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ) ↔ ( φ ∧ ( ψ ∧ ( χ ∧ θ ) ) )
    s1 = lb.ref(
        "s1",
        "( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ) ↔ ( φ ∧ ( ψ ∧ ( χ ∧ θ ) ) )",
        ref="anass",
        note="anass",
    )

    # an12: ( ψ ∧ ( χ ∧ θ ) ) ↔ ( χ ∧ ( ψ ∧ θ ) )
    s2 = lb.ref(
        "s2",
        "( ψ ∧ ( χ ∧ θ ) ) ↔ ( χ ∧ ( ψ ∧ θ ) )",
        ref="an12",
        note="an12",
    )

    # bianass with s2: ( φ ∧ ( ψ ∧ ( χ ∧ θ ) ) ) ↔ ( ( φ ∧ χ ) ∧ ( ψ ∧ θ ) )
    s3 = lb.ref(
        "s3",
        "( φ ∧ ( ψ ∧ ( χ ∧ θ ) ) ) ↔ ( ( φ ∧ χ ) ∧ ( ψ ∧ θ ) )",
        s2,
        ref="bianass",
        note="bianass",
    )

    # bitri s1, s3: ( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ) ↔ ( ( φ ∧ χ ) ∧ ( ψ ∧ θ ) )
    res = lb.ref(
        "res",
        "( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ) ↔ ( ( φ ∧ χ ) ∧ ( ψ ∧ θ ) )",
        s1,
        s3,
        ref="bitri",
        note="bitri",
    )
    return lb.build(res)


def prove_an4s(sys: System) -> Proof:
    """an4s: ( ( φ ∧ χ ) ∧ ( ψ ∧ θ ) ) → τ.

    Hyp: an4s.1 |- ( ( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ) → τ ).
    Concl: |- ( ( ( φ ∧ χ ) ∧ ( ψ ∧ θ ) ) → τ ).

    Inference associated with ~ an4 .  (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "an4s")
    h1 = lb.hyp("an4s.1", "( ( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ) → τ )")

    # an4: ( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ) ↔ ( ( φ ∧ χ ) ∧ ( ψ ∧ θ ) )
    s1 = lb.ref(
        "s1",
        "( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ) ↔ ( ( φ ∧ χ ) ∧ ( ψ ∧ θ ) )",
        ref="an4",
        note="an4",
    )

    # sylbir: from ( ψ ↔ φ ) and ( ψ → χ ), derive ( φ → χ )
    res = lb.ref(
        "res",
        "( ( ( φ ∧ χ ) ∧ ( ψ ∧ θ ) ) → τ )",
        s1,
        h1,
        ref="sylbir",
        note="sylbir",
    )

    return lb.build(res)


def prove_an42(sys: System) -> Proof:
    """an42: ( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ) ↔ ( ( φ ∧ χ ) ∧ ( θ ∧ ψ ) ).

    Swap the second and third conjuncts in a nested conjunction — biconditional form.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "an42")

    # an4: ( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ) ↔ ( ( φ ∧ χ ) ∧ ( ψ ∧ θ ) )
    s1 = lb.ref(
        "s1",
        "( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ) ↔ ( ( φ ∧ χ ) ∧ ( ψ ∧ θ ) )",
        ref="an4",
        note="an4",
    )

    # ancom: ( ψ ∧ θ ) ↔ ( θ ∧ ψ )
    s2 = lb.ref(
        "s2",
        "( ψ ∧ θ ) ↔ ( θ ∧ ψ )",
        ref="ancom",
        note="ancom",
    )

    # anbi2i with s2: ( ( φ ∧ χ ) ∧ ( ψ ∧ θ ) ) ↔ ( ( φ ∧ χ ) ∧ ( θ ∧ ψ ) )
    s3 = lb.ref(
        "s3",
        "( ( φ ∧ χ ) ∧ ( ψ ∧ θ ) ) ↔ ( ( φ ∧ χ ) ∧ ( θ ∧ ψ ) )",
        s2,
        ref="anbi2i",
        note="anbi2i",
    )

    # bitri s1, s3
    res = lb.ref(
        "res",
        "( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ) ↔ ( ( φ ∧ χ ) ∧ ( θ ∧ ψ ) )",
        s1,
        s3,
        ref="bitri",
        note="bitri",
    )

    return lb.build(res)


def prove_an42s(sys: System) -> Proof:
    """an42s: ( ( ( φ ∧ χ ) ∧ ( θ ∧ ψ ) ) → τ .

    Hyp: an41r3s.1 |- ( ( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ) → τ ).
    Concl: |- ( ( ( φ ∧ χ ) ∧ ( θ ∧ ψ ) ) → τ ).

    Swap the second and third conjuncts of an antecedent.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "an42s")
    h1 = lb.hyp("an41r3s.1", "( ( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ) → τ )")

    s1 = lb.ref(
        "s1",
        "( ( ( φ ∧ χ ) ∧ ( ψ ∧ θ ) ) → τ )",
        h1,
        ref="an4s",
        note="an4s",
    )

    res = lb.ref(
        "res",
        "( ( ( φ ∧ χ ) ∧ ( θ ∧ ψ ) ) → τ )",
        s1,
        ref="ancom2s",
        note="ancom2s",
    )

    return lb.build(res)


def prove_an42ds(sys: System) -> Proof:
    """an42ds: ( ( ( ( φ ∧ θ ) ∧ χ ) ∧ ψ ) → τ ).

    Inference exchanging the last antecedent with the second one.
    (Contributed by Thierry Arnoux, 3-Jun-2025.)
    """
    lb = ProofBuilder(sys, "an42ds")
    h1 = lb.hyp("an42ds.1", "( ( ( ( φ ∧ ψ ) ∧ χ ) ∧ θ ) → τ )")

    # an32: ( ( φ ∧ θ ) ∧ χ ) ↔ ( ( φ ∧ χ ) ∧ θ )
    s1 = lb.ref(
        "s1",
        "( ( φ ∧ θ ) ∧ χ ) ↔ ( ( φ ∧ χ ) ∧ θ )",
        ref="an32",
        note="an32",
    )

    # anbi1i: ( ( ( φ ∧ θ ) ∧ χ ) ∧ ψ ) ↔ ( ( ( φ ∧ χ ) ∧ θ ) ∧ ψ )
    s2 = lb.ref(
        "s2",
        "( ( ( φ ∧ θ ) ∧ χ ) ∧ ψ ) ↔ ( ( ( φ ∧ χ ) ∧ θ ) ∧ ψ )",
        s1,
        ref="anbi1i",
        note="anbi1i",
    )

    # an32: ( ( φ ∧ ψ ) ∧ χ ) ↔ ( ( φ ∧ χ ) ∧ ψ )
    s3 = lb.ref(
        "s3",
        "( ( φ ∧ ψ ) ∧ χ ) ↔ ( ( φ ∧ χ ) ∧ ψ )",
        ref="an32",
        note="an32",
    )

    # anbi1i: ( ( ( φ ∧ ψ ) ∧ χ ) ∧ θ ) ↔ ( ( ( φ ∧ χ ) ∧ ψ ) ∧ θ )
    s4 = lb.ref(
        "s4",
        "( ( ( φ ∧ ψ ) ∧ χ ) ∧ θ ) ↔ ( ( ( φ ∧ χ ) ∧ ψ ) ∧ θ )",
        s3,
        ref="anbi1i",
        note="anbi1i",
    )

    # an32: ( ( ( φ ∧ χ ) ∧ θ ) ∧ ψ ) ↔ ( ( ( φ ∧ χ ) ∧ ψ ) ∧ θ )
    s5 = lb.ref(
        "s5",
        "( ( ( φ ∧ χ ) ∧ θ ) ∧ ψ ) ↔ ( ( ( φ ∧ χ ) ∧ ψ ) ∧ θ )",
        ref="an32",
        note="an32",
    )

    # 3bitr4i: chain s5, s2, s4 → ( ( ( φ ∧ θ ) ∧ χ ) ∧ ψ ) ↔ ( ( ( φ ∧ ψ ) ∧ χ ) ∧ θ )
    s6 = lb.ref(
        "s6",
        "( ( ( φ ∧ θ ) ∧ χ ) ∧ ψ ) ↔ ( ( ( φ ∧ ψ ) ∧ χ ) ∧ θ )",
        s5,
        s2,
        s4,
        ref="3bitr4i",
        note="3bitr4i",
    )

    # sylbi: from the biconditional and the hypothesis
    res = lb.ref(
        "res",
        "( ( ( ( φ ∧ θ ) ∧ χ ) ∧ ψ ) → τ )",
        s6,
        h1,
        ref="sylbi",
        note="sylbi",
    )

    return lb.build(res)


def prove_an43(sys: System) -> Proof:
    """an43: ( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ) ↔ ( ( φ ∧ θ ) ∧ ( ψ ∧ χ ) ).

    Swap conjuncts — biconditional form.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "an43")

    # an42 with substitution {ψ:=θ, χ:=ψ, θ:=χ}:
    # ( ( φ ∧ θ ) ∧ ( ψ ∧ χ ) ) ↔ ( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) )
    s1 = lb.ref(
        "s1",
        "( ( φ ∧ θ ) ∧ ( ψ ∧ χ ) ) ↔ ( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) )",
        ref="an42",
        note="an42",
    )

    # bicomi: swap sides
    res = lb.ref(
        "res",
        "( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ) ↔ ( ( φ ∧ θ ) ∧ ( ψ ∧ χ ) )",
        s1,
        ref="bicomi",
        note="bicomi",
    )

    return lb.build(res)


def prove_an3(sys: System) -> Proof:
    """an3: ( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ) → ( φ ∧ θ ).

    One way of swapping conjuncts.
    """
    lb = ProofBuilder(sys, "an3")
    s1 = lb.ref(
        "s1",
        "( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ) ↔ ( ( φ ∧ θ ) ∧ ( ψ ∧ χ ) )",
        ref="an43",
        note="an43",
    )
    res = lb.ref(
        "res",
        "( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ) → ( φ ∧ θ )",
        s1,
        ref="simplbi",
        note="simplbi an43",
    )
    return lb.build(res)


def prove_an6(sys: System) -> Proof:
    """an6: ( ( φ ∧ ψ ∧ χ ) ∧ ( θ ∧ τ ∧ η ) ) ↔ ( ( φ ∧ θ ) ∧ ( ψ ∧ τ ) ∧ ( χ ∧ η ) ).

    Rearrange three pairs of conjuncts.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "an6")

    # df-3an: ( φ ∧ ψ ∧ χ ) ↔ ( ( φ ∧ ψ ) ∧ χ )
    s1 = lb.ref(
        "s1",
        "( φ ∧ ψ ∧ χ ) ↔ ( ( φ ∧ ψ ) ∧ χ )",
        ref="df-3an",
        note="df-3an",
    )

    # df-3an: ( θ ∧ τ ∧ η ) ↔ ( ( θ ∧ τ ) ∧ η )
    s2 = lb.ref(
        "s2",
        "( θ ∧ τ ∧ η ) ↔ ( ( θ ∧ τ ) ∧ η )",
        ref="df-3an",
        note="df-3an",
    )

    # anbi12i: ( ( φ ∧ ψ ∧ χ ) ∧ ( θ ∧ τ ∧ η ) ) ↔ ( ( ( φ ∧ ψ ) ∧ χ ) ∧ ( ( θ ∧ τ ) ∧ η ) )
    s3 = lb.ref(
        "s3",
        "( ( φ ∧ ψ ∧ χ ) ∧ ( θ ∧ τ ∧ η ) ) ↔ ( ( ( φ ∧ ψ ) ∧ χ ) ∧ ( ( θ ∧ τ ) ∧ η ) )",
        s1,
        s2,
        ref="anbi12i",
        note="anbi12i",
    )

    # an4: ( ( ( φ ∧ ψ ) ∧ χ ) ∧ ( ( θ ∧ τ ) ∧ η ) ) ↔ ( ( ( φ ∧ ψ ) ∧ ( θ ∧ τ ) ) ∧ ( χ ∧ η ) )
    s4 = lb.ref(
        "s4",
        "( ( ( φ ∧ ψ ) ∧ χ ) ∧ ( ( θ ∧ τ ) ∧ η ) ) ↔ ( ( ( φ ∧ ψ ) ∧ ( θ ∧ τ ) ) ∧ ( χ ∧ η ) )",
        ref="an4",
        note="an4",
    )

    # biid: ( ( ( φ ∧ ψ ) ∧ ( θ ∧ τ ) ) ∧ ( χ ∧ η ) ) ↔ ( ( ( φ ∧ ψ ) ∧ ( θ ∧ τ ) ) ∧ ( χ ∧ η ) )
    s5 = lb.ref(
        "s5",
        "( ( ( φ ∧ ψ ) ∧ ( θ ∧ τ ) ) ∧ ( χ ∧ η ) ) ↔ ( ( ( φ ∧ ψ ) ∧ ( θ ∧ τ ) ) ∧ ( χ ∧ η ) )",
        ref="biid",
        note="biid",
    )

    # an4: ( ( φ ∧ ψ ) ∧ ( θ ∧ τ ) ) ↔ ( ( φ ∧ θ ) ∧ ( ψ ∧ τ ) )
    s6 = lb.ref(
        "s6",
        "( ( φ ∧ ψ ) ∧ ( θ ∧ τ ) ) ↔ ( ( φ ∧ θ ) ∧ ( ψ ∧ τ ) )",
        ref="an4",
        note="an4",
    )

    # bianbi: ( ( ( φ ∧ ψ ) ∧ ( θ ∧ τ ) ) ∧ ( χ ∧ η ) ) ↔ ( ( ( φ ∧ θ ) ∧ ( ψ ∧ τ ) ) ∧ ( χ ∧ η ) )
    s7 = lb.ref(
        "s7",
        "( ( ( φ ∧ ψ ) ∧ ( θ ∧ τ ) ) ∧ ( χ ∧ η ) ) ↔ ( ( ( φ ∧ θ ) ∧ ( ψ ∧ τ ) ) ∧ ( χ ∧ η ) )",
        s5,
        s6,
        ref="bianbi",
        note="bianbi",
    )

    # bitri: ( ( ( φ ∧ ψ ) ∧ χ ) ∧ ( ( θ ∧ τ ) ∧ η ) ) ↔ ( ( ( φ ∧ θ ) ∧ ( ψ ∧ τ ) ) ∧ ( χ ∧ η ) )
    s8 = lb.ref(
        "s8",
        "( ( ( φ ∧ ψ ) ∧ χ ) ∧ ( ( θ ∧ τ ) ∧ η ) ) ↔ ( ( ( φ ∧ θ ) ∧ ( ψ ∧ τ ) ) ∧ ( χ ∧ η ) )",
        s4,
        s7,
        ref="bitri",
        note="bitri",
    )

    # df-3an: ( ( φ ∧ θ ) ∧ ( ψ ∧ τ ) ∧ ( χ ∧ η ) ) ↔ ( ( ( φ ∧ θ ) ∧ ( ψ ∧ τ ) ) ∧ ( χ ∧ η ) )
    s9 = lb.ref(
        "s9",
        "( ( φ ∧ θ ) ∧ ( ψ ∧ τ ) ∧ ( χ ∧ η ) ) ↔ ( ( ( φ ∧ θ ) ∧ ( ψ ∧ τ ) ) ∧ ( χ ∧ η ) )",
        ref="df-3an",
        note="df-3an",
    )

    # 3bitr4i: ( ( φ ∧ ψ ∧ χ ) ∧ ( θ ∧ τ ∧ η ) ) ↔ ( ( φ ∧ θ ) ∧ ( ψ ∧ τ ) ∧ ( χ ∧ η ) )
    res = lb.ref(
        "res",
        "( ( φ ∧ ψ ∧ χ ) ∧ ( θ ∧ τ ∧ η ) ) ↔ ( ( φ ∧ θ ) ∧ ( ψ ∧ τ ) ∧ ( χ ∧ η ) )",
        s8,
        s3,
        s9,
        ref="3bitr4i",
        note="3bitr4i",
    )

    return lb.build(res)


def prove_anandi(sys: System) -> Proof:
    """anandi: ( φ ∧ ( ψ ∧ χ ) ) ↔ ( ( φ ∧ ψ ) ∧ ( φ ∧ χ ) ).

    Distribution of conjunction over conjunction — left distributive law.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "anandi")

    # anidm: ( φ ∧ φ ) ↔ φ
    s1 = lb.ref("s1", "( φ ∧ φ ) ↔ φ", ref="anidm", note="anidm")

    # anbi1i with s1: ( ( φ ∧ φ ) ∧ ( ψ ∧ χ ) ) ↔ ( φ ∧ ( ψ ∧ χ ) )
    s2 = lb.ref(
        "s2",
        "( ( φ ∧ φ ) ∧ ( ψ ∧ χ ) ) ↔ ( φ ∧ ( ψ ∧ χ ) )",
        s1,
        ref="anbi1i",
        note="anbi1i",
    )

    # an4: ( ( φ ∧ φ ) ∧ ( ψ ∧ χ ) ) ↔ ( ( φ ∧ ψ ) ∧ ( φ ∧ χ ) )
    s3 = lb.ref(
        "s3",
        "( ( φ ∧ φ ) ∧ ( ψ ∧ χ ) ) ↔ ( ( φ ∧ ψ ) ∧ ( φ ∧ χ ) )",
        ref="an4",
        note="an4",
    )

    # bitr3i s2, s3: ( φ ∧ ( ψ ∧ χ ) ) ↔ ( ( φ ∧ ψ ) ∧ ( φ ∧ χ ) )
    res = lb.ref(
        "res",
        "( φ ∧ ( ψ ∧ χ ) ) ↔ ( ( φ ∧ ψ ) ∧ ( φ ∧ χ ) )",
        s2,
        s3,
        ref="bitr3i",
        note="bitr3i",
    )

    return lb.build(res)


def prove_anandi3(sys: System) -> Proof:
    """anandi3: ( φ ∧ ψ ∧ χ ) ↔ ( ( φ ∧ ψ ) ∧ ( φ ∧ χ ) ).

    Distribution of ternary conjunction over conjunction.  The triple
    conjunction is equivalent to the conjunction of the first with each
    of the remaining conjuncts.
    """
    lb = ProofBuilder(sys, "anandi3")

    # 3anass: ( φ ∧ ψ ∧ χ ) ↔ ( φ ∧ ( ψ ∧ χ ) )
    s1 = lb.ref(
        "s1",
        "( φ ∧ ψ ∧ χ ) ↔ ( φ ∧ ( ψ ∧ χ ) )",
        ref="3anass",
        note="3anass",
    )

    # anandi: ( φ ∧ ( ψ ∧ χ ) ) ↔ ( ( φ ∧ ψ ) ∧ ( φ ∧ χ ) )
    s2 = lb.ref(
        "s2",
        "( φ ∧ ( ψ ∧ χ ) ) ↔ ( ( φ ∧ ψ ) ∧ ( φ ∧ χ ) )",
        ref="anandi",
        note="anandi",
    )

    # bitri s1, s2: ( φ ∧ ψ ∧ χ ) ↔ ( ( φ ∧ ψ ) ∧ ( φ ∧ χ ) )
    res = lb.ref(
        "res",
        "( φ ∧ ψ ∧ χ ) ↔ ( ( φ ∧ ψ ) ∧ ( φ ∧ χ ) )",
        s1,
        s2,
        ref="bitri",
        note="bitri",
    )

    return lb.build(res)


def prove_anandir(sys: System) -> Proof:
    """anandir: ( ( φ ∧ ψ ) ∧ χ ) ↔ ( ( φ ∧ χ ) ∧ ( ψ ∧ χ ) ).

    Right distributive law for conjunction.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "anandir")

    # anidm: ( χ ∧ χ ) ↔ χ
    s1 = lb.ref("s1", "( χ ∧ χ ) ↔ χ", ref="anidm", note="anidm")

    # anbi2i with s1: ( ( φ ∧ ψ ) ∧ ( χ ∧ χ ) ) ↔ ( ( φ ∧ ψ ) ∧ χ )
    s2 = lb.ref(
        "s2",
        "( ( φ ∧ ψ ) ∧ ( χ ∧ χ ) ) ↔ ( ( φ ∧ ψ ) ∧ χ )",
        s1,
        ref="anbi2i",
        note="anbi2i",
    )

    # an4: ( ( φ ∧ ψ ) ∧ ( χ ∧ χ ) ) ↔ ( ( φ ∧ χ ) ∧ ( ψ ∧ χ ) )
    s3 = lb.ref(
        "s3",
        "( ( φ ∧ ψ ) ∧ ( χ ∧ χ ) ) ↔ ( ( φ ∧ χ ) ∧ ( ψ ∧ χ ) )",
        ref="an4",
        note="an4",
    )

    # bitr3i s2, s3: ( ( φ ∧ ψ ) ∧ χ ) ↔ ( ( φ ∧ χ ) ∧ ( ψ ∧ χ ) )
    res = lb.ref(
        "res",
        "( ( φ ∧ ψ ) ∧ χ ) ↔ ( ( φ ∧ χ ) ∧ ( ψ ∧ χ ) )",
        s2,
        s3,
        ref="bitr3i",
        note="bitr3i",
    )

    return lb.build(res)


def prove_anandi3r(sys: System) -> Proof:
    """anandi3r: ( φ ∧ ψ ∧ χ ) ↔ ( ( φ ∧ ψ ) ∧ ( χ ∧ ψ ) ).

    Distribution of ternary conjunction over conjunction with commutation
    of the second conjunct.
    """
    lb = ProofBuilder(sys, "anandi3r")

    # 3anan32: ( φ ∧ ψ ∧ χ ) ↔ ( ( φ ∧ χ ) ∧ ψ )
    s1 = lb.ref(
        "s1",
        "( φ ∧ ψ ∧ χ ) ↔ ( ( φ ∧ χ ) ∧ ψ )",
        ref="3anan32",
        note="3anan32",
    )

    # anandir [φ, χ, ψ] for [φ, ψ, χ]:
    # ( ( φ ∧ χ ) ∧ ψ ) ↔ ( ( φ ∧ ψ ) ∧ ( χ ∧ ψ ) )
    s2 = lb.ref(
        "s2",
        "( ( φ ∧ χ ) ∧ ψ ) ↔ ( ( φ ∧ ψ ) ∧ ( χ ∧ ψ ) )",
        ref="anandir",
        note="anandir",
    )

    # bitri s1, s2: ( φ ∧ ψ ∧ χ ) ↔ ( ( φ ∧ ψ ) ∧ ( χ ∧ ψ ) )
    res = lb.ref(
        "res",
        "( φ ∧ ψ ∧ χ ) ↔ ( ( φ ∧ ψ ) ∧ ( χ ∧ ψ ) )",
        s1,
        s2,
        ref="bitri",
        note="bitri",
    )

    return lb.build(res)


def prove_anbi1cd(sys: System) -> Proof:
    """anbi1cd: φ → ( ( θ ∧ ψ ) ↔ ( χ ∧ θ ) ).

    Hyp: φ → ( ψ ↔ χ )
    Concl: φ → ( ( θ ∧ ψ ) ↔ ( χ ∧ θ ) )

    Deduction conjoining a left antecedent to both sides of a biconditional
    with commutation of the right conjunct.
    (Contributed by NM, 26-May-2003.)
    """
    lb = ProofBuilder(sys, "anbi1cd")
    h1 = lb.hyp("anbi1cd.1", "φ → ( ψ ↔ χ )")
    s1 = lb.ref(
        "s1",
        "φ → ( ( θ ∧ ψ ) ↔ ( θ ∧ χ ) )",
        h1,
        ref="anbi2d",
        note="anbi2d anbi1cd.1",
    )
    res = lb.ref(
        "res",
        "φ → ( ( θ ∧ ψ ) ↔ ( χ ∧ θ ) )",
        s1,
        ref="biancomd",
        note="biancomd",
    )
    return lb.build(res)


def prove_3an6(sys: System) -> Proof:
    """3an6: ( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ∧ ( τ ∧ η ) ) ↔ ( ( φ ∧ χ ∧ τ ) ∧ ( ψ ∧ θ ∧ η ) ).

    Rearrange three pairs of conjuncts — ternary form of an6.
    """
    lb = ProofBuilder(sys, "3an6")
    s1 = lb.ref(
        "s1",
        "( ( φ ∧ χ ∧ τ ) ∧ ( ψ ∧ θ ∧ η ) ) ↔ ( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ∧ ( τ ∧ η ) )",
        ref="an6",
        note="an6",
    )
    res = lb.ref(
        "res",
        "( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ∧ ( τ ∧ η ) ) ↔ ( ( φ ∧ χ ∧ τ ) ∧ ( ψ ∧ θ ∧ η ) )",
        s1,
        ref="bicomi",
        note="bicomi",
    )
    return lb.build(res)


def prove_3anrot(sys: System) -> Proof:
    """3anrot: ( φ ∧ ψ ∧ χ ) ↔ ( ψ ∧ χ ∧ φ ).

    Rotation law for triple conjunction.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "3anrot")

    # 3ancoma: ( φ ∧ ψ ∧ χ ) ↔ ( ψ ∧ φ ∧ χ )
    s1 = lb.ref(
        "s1",
        "( φ ∧ ψ ∧ χ ) ↔ ( ψ ∧ φ ∧ χ )",
        ref="3ancoma",
        note="3ancoma",
    )

    # 3ancomb: ( ψ ∧ φ ∧ χ ) ↔ ( ψ ∧ χ ∧ φ )
    s2 = lb.ref(
        "s2",
        "( ψ ∧ φ ∧ χ ) ↔ ( ψ ∧ χ ∧ φ )",
        ref="3ancomb",
        note="3ancomb",
    )

    # bitri: combine
    res = lb.ref(
        "res",
        "( φ ∧ ψ ∧ χ ) ↔ ( ψ ∧ χ ∧ φ )",
        s1,
        s2,
        ref="bitri",
        note="bitri",
    )

    return lb.build(res)


def prove_3anrev(sys: System) -> Proof:
    """3anrev: ( φ ∧ ψ ∧ χ ) ↔ ( χ ∧ ψ ∧ φ ).

    Reverse the order of the triple conjunction.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "3anrev")

    # 3ancoma: ( φ ∧ ψ ∧ χ ) ↔ ( ψ ∧ φ ∧ χ )
    s1 = lb.ref(
        "s1",
        "( φ ∧ ψ ∧ χ ) ↔ ( ψ ∧ φ ∧ χ )",
        ref="3ancoma",
        note="3ancoma",
    )

    # 3anrot: ( χ ∧ ψ ∧ φ ) ↔ ( ψ ∧ φ ∧ χ )
    s2 = lb.ref(
        "s2",
        "( χ ∧ ψ ∧ φ ) ↔ ( ψ ∧ φ ∧ χ )",
        ref="3anrot",
        note="3anrot",
    )

    # bitr4i: ( φ ↔ ψ ), ( χ ↔ ψ ) ⊢ ( φ ↔ χ )
    res = lb.ref(
        "res",
        "( φ ∧ ψ ∧ χ ) ↔ ( χ ∧ ψ ∧ φ )",
        s1,
        s2,
        ref="bitr4i",
        note="bitr4i",
    )

    return lb.build(res)


def prove_pm4_71r(sys: System) -> Proof:
    r"""pm4.71r: ( ( φ → ψ ) ↔ ( φ ↔ ( ψ ∧ φ ) ) ).

    An alternative definition of the biconditional with conjunction
    commuted.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm4.71r")

    # pm4.71: ( ( φ → ψ ) ↔ ( φ ↔ ( φ ∧ ψ ) ) )
    s1 = lb.ref(
        "s1",
        "( ( φ → ψ ) ↔ ( φ ↔ ( φ ∧ ψ ) ) )",
        ref="pm4.71",
        note="pm4.71",
    )

    # ancom: ( ( φ ∧ ψ ) ↔ ( ψ ∧ φ ) )
    s2 = lb.ref(
        "s2",
        "( ( φ ∧ ψ ) ↔ ( ψ ∧ φ ) )",
        ref="ancom",
        note="ancom",
    )

    # bibi2i: ( ( φ ↔ ( φ ∧ ψ ) ) ↔ ( φ ↔ ( ψ ∧ φ ) ) )
    s3 = lb.ref(
        "s3",
        "( ( φ ↔ ( φ ∧ ψ ) ) ↔ ( φ ↔ ( ψ ∧ φ ) ) )",
        s2,
        ref="bibi2i",
        note="bibi2i",
    )

    # bitri: ( ( φ → ψ ) ↔ ( φ ↔ ( ψ ∧ φ ) ) )
    res = lb.ref(
        "res",
        "( ( φ → ψ ) ↔ ( φ ↔ ( ψ ∧ φ ) ) )",
        s1,
        s3,
        ref="bitri",
        note="bitri",
    )

    return lb.build(res)


def prove_imnan(sys: System) -> Proof:
    """imnan: ( φ → ¬ ψ ) ↔ ¬ ( φ ∧ ψ ).

    From df-an and con2bii: negating both sides of the conjunction
    definition gives the equivalence of an implication to a negated
    conjunction.
    """
    lb = ProofBuilder(sys, "imnan")

    dfan = lb.ref(
        "df-an",
        r"( ( ph /\ ps ) <-> -. ( ph -> -. ps ) )",
        ref="df-an",
        note="df-an",
    )

    res = lb.ref(
        "res",
        r"( ( ph -> -. ps ) <-> -. ( ph /\ ps ) )",
        dfan,
        ref="con2bii",
        note="con2bii",
    )

    return lb.build(res)


def prove_imnani(sys: System) -> Proof:
    """imnani: φ → ¬ ψ.

    Hyp: ¬(φ ∧ ψ).  Concl: φ → ¬ ψ.
    Inference form of imnan.
    """
    lb = ProofBuilder(sys, "imnani")
    h1 = lb.hyp("imnani.1", "¬ ( φ ∧ ψ )")
    s1 = lb.ref("s1", "( φ → ¬ ψ ) ↔ ¬ ( φ ∧ ψ )", ref="imnan", note="imnan")
    res = lb.ref("res", "φ → ¬ ψ", h1, s1, ref="mpbir", note="mpbir")
    return lb.build(res)


def prove_iman(sys: System) -> Proof:
    """iman: ( ( φ → ψ ) ↔ ¬ ( φ ∧ ¬ ψ ) ).

    Express implication in terms of conjunction and negation
    using double-negation (notnotb), imbi2i, imnan, and bitri.
    """
    lb = ProofBuilder(sys, "iman")

    # notnotb: ( ψ ↔ ¬ ¬ ψ )
    s1 = lb.ref("s1", "( ψ ↔ ¬ ¬ ψ )", ref="notnotb", note="notnotb")

    # imbi2i: ( ( φ → ψ ) ↔ ( φ → ¬ ¬ ψ ) )
    s2 = lb.ref("s2", "( ( φ → ψ ) ↔ ( φ → ¬ ¬ ψ ) )", s1, ref="imbi2i", note="imbi2i")

    # imnan: ( ( φ → ¬ ¬ ψ ) ↔ ¬ ( φ ∧ ¬ ψ ) )
    s3 = lb.ref(
        "s3",
        "( ( φ → ¬ ¬ ψ ) ↔ ¬ ( φ ∧ ¬ ψ ) )",
        ref="imnan",
        note="imnan",
    )

    # bitri: ( ( φ → ψ ) ↔ ¬ ( φ ∧ ¬ ψ ) )
    res = lb.ref(
        "res",
        "( ( φ → ψ ) ↔ ¬ ( φ ∧ ¬ ψ ) )",
        s2,
        s3,
        ref="bitri",
        note="bitri",
    )

    return lb.build(res)


def prove_annim(sys: System) -> Proof:
    """annim: ( φ ∧ ¬ ψ ) ↔ ¬ ( φ → ψ ).

    Express a negated implication as a conjunction with a negated consequent.
    """
    lb = ProofBuilder(sys, "annim")

    s1 = lb.ref(
        "s1",
        "( φ → ψ ) ↔ ¬ ( φ ∧ ¬ ψ )",
        ref="iman",
        note="iman",
    )

    res = lb.ref(
        "res",
        "( φ ∧ ¬ ψ ) ↔ ¬ ( φ → ψ )",
        s1,
        ref="con2bii",
        note="con2bii",
    )

    return lb.build(res)


def prove_pm4_61(sys: System) -> Proof:
    """pm4.61: ¬ ( φ → ψ ) ↔ ( φ ∧ ¬ ψ ).

    Negation of an implication is equivalent to the antecedent
    conjoined with the negation of the consequent.
    """
    lb = ProofBuilder(sys, "pm4.61")

    s1 = lb.ref(
        "s1",
        "( φ ∧ ¬ ψ ) ↔ ¬ ( φ → ψ )",
        ref="annim",
        note="annim",
    )

    res = lb.ref(
        "res",
        "¬ ( φ → ψ ) ↔ ( φ ∧ ¬ ψ )",
        s1,
        ref="bicomi",
        note="bicomi",
    )

    return lb.build(res)


def prove_pm4_65(sys: System) -> Proof:
    """pm4.65: ¬ ( ¬ φ → ψ ) ↔ ( ¬ φ ∧ ¬ ψ ).

    Theorem *4.65 of [WhiteheadRussell].
    """
    lb = ProofBuilder(sys, "pm4.65")

    res = lb.ref(
        "res",
        "¬ ( ¬ φ → ψ ) ↔ ( ¬ φ ∧ ¬ ψ )",
        ref="pm4.61",
        note="pm4.61",
    )

    return lb.build(res)


def prove_pm3_24(sys: System) -> Proof:
    """pm3.24: ¬ ( φ ∧ ¬ φ ).

    The law of non-contradiction: a wff cannot be both true and false.
    """
    lb = ProofBuilder(sys, "pm3.24")
    s_id = lb.ref("s_id", "( φ → φ )", ref="id", note="id")
    s_iman = lb.ref(
        "s_iman",
        "( ( φ → φ ) ↔ ¬ ( φ ∧ ¬ φ ) )",
        ref="iman",
        note="iman",
    )
    res = lb.ref(
        "res",
        "¬ ( φ ∧ ¬ φ )",
        s_id,
        s_iman,
        ref="mpbi",
        note="mpbi",
    )
    return lb.build(res)


def prove_dedlem0a(sys: System) -> Proof:
    """dedlem0a: φ → ( ψ ↔ ( ( χ → φ ) → ( ψ ∧ φ ) ) ).

    A "definitional lemma" for the biconditional-in-conjunction form
    used by dedlem0b and dedlema.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "dedlem0a")

    s_iba = lb.ref(
        "s_iba",
        "φ → ( ψ ↔ ( ψ ∧ φ ) )",
        ref="iba",
        note="iba",
    )

    s_biimt = lb.ref(
        "s_biimt",
        "( χ → φ ) → ( ( ψ ∧ φ ) ↔ ( ( χ → φ ) → ( ψ ∧ φ ) ) )",
        ref="biimt",
        note="biimt",
    )

    s_jarri = lb.ref(
        "s_jarri",
        "φ → ( ( ψ ∧ φ ) ↔ ( ( χ → φ ) → ( ψ ∧ φ ) ) )",
        s_biimt,
        ref="jarri",
        note="jarri",
    )

    res = lb.ref(
        "res",
        "φ → ( ψ ↔ ( ( χ → φ ) → ( ψ ∧ φ ) ) )",
        s_iba,
        s_jarri,
        ref="bitrd",
        note="bitrd",
    )

    return lb.build(res)


def prove_dedlem0b(sys: System) -> Proof:
    """dedlem0b: ¬ φ → ( ψ ↔ ( ( ψ → φ ) → ( χ ∧ φ ) ) ).

    Lemma for weak deduction theorem.  One of two lemmas used to
    eliminate an antecedent with a biconditional.
    (Contributed by NM, 26-Jun-2002.)
    """
    lb = ProofBuilder(sys, "dedlem0b")

    # pm2.21: ¬ φ → ( φ → ( χ ∧ φ ) )
    s1 = lb.ref(
        "s1",
        "¬ φ → ( φ → ( χ ∧ φ ) )",
        ref="pm2.21",
        note="pm2.21",
    )

    # imim2d: from s1 derive ¬ φ → ( ( ψ → φ ) → ( ψ → ( χ ∧ φ ) ) )
    s2 = lb.ref(
        "s2",
        "¬ φ → ( ( ψ → φ ) → ( ψ → ( χ ∧ φ ) ) )",
        s1,
        ref="imim2d",
        note="imim2d",
    )

    # com23: swap second and third antecedents
    s3 = lb.ref(
        "s3",
        "¬ φ → ( ψ → ( ( ψ → φ ) → ( χ ∧ φ ) ) )",
        s2,
        ref="com23",
        note="com23",
    )

    # pm2.21: ¬ ψ → ( ψ → φ )
    s4 = lb.ref(
        "s4",
        "¬ ψ → ( ψ → φ )",
        ref="pm2.21",
        note="pm2.21",
    )

    # simpr: ( χ ∧ φ ) → φ
    s5 = lb.ref(
        "s5",
        "( χ ∧ φ ) → φ",
        ref="simpr",
        note="simpr",
    )

    # imim12i: from s4 and s5 derive
    # ( ( ( ψ → φ ) → ( χ ∧ φ ) ) → ( ¬ ψ → φ ) )
    s6 = lb.ref(
        "s6",
        "( ( ( ψ → φ ) → ( χ ∧ φ ) ) → ( ¬ ψ → φ ) )",
        s4,
        s5,
        ref="imim12i",
        note="imim12i",
    )

    # con1d: from s6 derive
    # ( ( ( ψ → φ ) → ( χ ∧ φ ) ) → ( ¬ φ → ψ ) )
    s7 = lb.ref(
        "s7",
        "( ( ( ψ → φ ) → ( χ ∧ φ ) ) → ( ¬ φ → ψ ) )",
        s6,
        ref="con1d",
        note="con1d",
    )

    # com12: swap antecedents
    s8 = lb.ref(
        "s8",
        "¬ φ → ( ( ( ψ → φ ) → ( χ ∧ φ ) ) → ψ )",
        s7,
        ref="com12",
        note="com12",
    )

    # impbid: combine forward (s3) and reverse (s8) directions
    res = lb.ref(
        "res",
        "¬ φ → ( ψ ↔ ( ( ψ → φ ) → ( χ ∧ φ ) ) )",
        s3,
        s8,
        ref="impbid",
        note="impbid",
    )

    return lb.build(res)


def prove_niabn(sys: System) -> Proof:
    """niabn: ¬ ψ → ( ( χ ∧ ψ ) ↔ ¬ φ ).

    Given φ, an implication to a false antecedent makes a conjunction
    and the negation of that false antecedent equivalent.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "niabn")
    h1 = lb.hyp("niabn.1", "φ")

    # simpr: ( χ ∧ ψ ) → ψ
    s1 = lb.ref(
        "s1",
        "( χ ∧ ψ ) → ψ",
        ref="simpr",
        note="simpr",
    )

    # pm2.24i: from φ get ¬ φ → ψ
    s2 = lb.ref(
        "s2",
        "¬ φ → ψ",
        h1,
        ref="pm2.24i",
        note="pm2.24i",
    )

    # pm5.21ni: from (χ∧ψ)→ψ and ¬φ→ψ get ¬ψ → ((χ∧ψ) ↔ ¬φ)
    res = lb.ref(
        "res",
        "¬ ψ → ( ( χ ∧ ψ ) ↔ ¬ φ )",
        s1,
        s2,
        ref="pm5.21ni",
        note="pm5.21ni",
    )

    return lb.build(res)


def prove_ninba(sys: System) -> Proof:
    """ninba: ¬ ψ → ( ¬ φ ↔ ( χ ∧ ψ ) ).

    Given φ, commutes the biconditional of niabn so that the negation
    of the hypothesis appears on the left side.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "ninba")
    h1 = lb.hyp("ninba.1", "φ")

    # niabn: ¬ ψ → ( ( χ ∧ ψ ) ↔ ¬ φ )
    s1 = lb.ref(
        "s1",
        "¬ ψ → ( ( χ ∧ ψ ) ↔ ¬ φ )",
        h1,
        ref="niabn",
        note="niabn",
    )

    # bicomd: commute the biconditional
    res = lb.ref(
        "res",
        "¬ ψ → ( ¬ φ ↔ ( χ ∧ ψ ) )",
        s1,
        ref="bicomd",
        note="bicomd",
    )

    return lb.build(res)


def prove_xordi(sys: System) -> Proof:
    """xordi: ( ( φ ∧ ¬ ( ψ ↔ χ ) ) ↔ ¬ ( ( φ ∧ ψ ) ↔ ( φ ∧ χ ) ) ).

    Distribute a conjunct over an exclusive-or biconditional.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "xordi")

    # annim with ψ := ( ψ ↔ χ ): ( φ ∧ ¬ ( ψ ↔ χ ) ) ↔ ¬ ( φ → ( ψ ↔ χ ) )
    s1 = lb.ref(
        "s1",
        "( φ ∧ ¬ ( ψ ↔ χ ) ) ↔ ¬ ( φ → ( ψ ↔ χ ) )",
        ref="annim",
        note="annim",
    )

    # pm5.32: ( φ → ( ψ ↔ χ ) ) ↔ ( ( φ ∧ ψ ) ↔ ( φ ∧ χ ) )
    s2 = lb.ref(
        "s2",
        "( φ → ( ψ ↔ χ ) ) ↔ ( ( φ ∧ ψ ) ↔ ( φ ∧ χ ) )",
        ref="pm5.32",
        note="pm5.32",
    )

    # xchbinx: (h1: φ ↔ ¬ ψ), (h2: ψ ↔ χ) ⊢ φ ↔ ¬ χ
    #   h1 matched by s1, h2 matched by s2
    res = lb.ref(
        "res",
        "( ( φ ∧ ¬ ( ψ ↔ χ ) ) ↔ ¬ ( ( φ ∧ ψ ) ↔ ( φ ∧ χ ) ) )",
        s1,
        s2,
        ref="xchbinx",
        note="xchbinx",
    )

    return lb.build(res)


def prove_anxordi(sys: System) -> Proof:
    """anxordi: ( φ ∧ ( ψ ⊻ χ ) ) ↔ ( ( φ ∧ ψ ) ⊻ ( φ ∧ χ ) ).

    Distribute a conjunct over exclusive-or.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "anxordi")

    # xordi: ( ( φ ∧ ¬ ( ψ ↔ χ ) ) ↔ ¬ ( ( φ ∧ ψ ) ↔ ( φ ∧ χ ) ) )
    s1 = lb.ref(
        "s1",
        "( ( φ ∧ ¬ ( ψ ↔ χ ) ) ↔ ¬ ( ( φ ∧ ψ ) ↔ ( φ ∧ χ ) ) )",
        ref="xordi",
        note="xordi",
    )

    # df-xor: ( ψ ⊻ χ ) ↔ ¬ ( ψ ↔ χ )
    s2 = lb.ref(
        "s2",
        "( ψ ⊻ χ ) ↔ ¬ ( ψ ↔ χ )",
        ref="df-xor",
        note="df-xor",
    )

    # anbi2i with s2: ( φ ∧ ( ψ ⊻ χ ) ) ↔ ( φ ∧ ¬ ( ψ ↔ χ ) )
    s3 = lb.ref(
        "s3",
        "( φ ∧ ( ψ ⊻ χ ) ) ↔ ( φ ∧ ¬ ( ψ ↔ χ ) )",
        s2,
        ref="anbi2i",
        note="anbi2i",
    )

    # df-xor: ( ( φ ∧ ψ ) ⊻ ( φ ∧ χ ) ) ↔ ¬ ( ( φ ∧ ψ ) ↔ ( φ ∧ χ ) )
    s4 = lb.ref(
        "s4",
        "( ( φ ∧ ψ ) ⊻ ( φ ∧ χ ) ) ↔ ¬ ( ( φ ∧ ψ ) ↔ ( φ ∧ χ ) )",
        ref="df-xor",
        note="df-xor",
    )

    # 3bitr4i with s3, s1, s4
    res = lb.ref(
        "res",
        "( φ ∧ ( ψ ⊻ χ ) ) ↔ ( ( φ ∧ ψ ) ⊻ ( φ ∧ χ ) )",
        s1,
        s3,
        s4,
        ref="3bitr4i",
        note="3bitr4i",
    )

    return lb.build(res)


def prove_biadanid(sys: System) -> Proof:
    """biadanid: φ → ( ψ ↔ ( χ ∧ θ ) ).

    Deduction form of biadani: from two premises with a common antecedent,
    one yielding a consequent and the other a biconditional over that
    consequent and a third formula, deduce a biconditional with a
    conjunction.  (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "biadanid")

    h1 = lb.hyp("biadanid.1", "( ( φ ∧ ψ ) → χ )")
    h2 = lb.hyp("biadanid.2", "( ( φ ∧ χ ) → ( ψ ↔ θ ) )")

    # biimpa: ( ( φ ∧ χ ) → ( ψ ↔ θ ) )  →  ( ( ( φ ∧ χ ) ∧ ψ ) → θ )
    s1 = lb.ref(
        "s1",
        "( ( ( φ ∧ χ ) ∧ ψ ) → θ )",
        h2,
        ref="biimpa",
        note="biimpa biadanid.2",
    )

    # an32s: swap ψ and χ in the nested conjunction
    s2 = lb.ref(
        "s2",
        "( ( ( φ ∧ ψ ) ∧ χ ) → θ )",
        s1,
        ref="an32s",
        note="an32s s1",
    )

    # mpdan: ( φ ∧ ψ ) → χ  and  ( ( φ ∧ ψ ) ∧ χ ) → θ  give  ( φ ∧ ψ ) → θ
    s3 = lb.ref(
        "s3",
        "( ( φ ∧ ψ ) → θ )",
        h1,
        s2,
        ref="mpdan",
        note="mpdan biadanid.1, s2",
    )

    # jca: ( φ ∧ ψ ) → χ  and  ( φ ∧ ψ ) → θ  give  ( φ ∧ ψ ) → ( χ ∧ θ )
    s4 = lb.ref(
        "s4",
        "( ( φ ∧ ψ ) → ( χ ∧ θ ) )",
        h1,
        s3,
        ref="jca",
        note="jca biadanid.1, s3",
    )

    # biimpar: ( ( φ ∧ χ ) → ( ψ ↔ θ ) )  →  ( ( ( φ ∧ χ ) ∧ θ ) → ψ )
    s5 = lb.ref(
        "s5",
        "( ( ( φ ∧ χ ) ∧ θ ) → ψ )",
        h2,
        ref="biimpar",
        note="biimpar biadanid.2",
    )

    # anasss: reassociate to get ( φ ∧ ( χ ∧ θ ) ) → ψ
    s6 = lb.ref(
        "s6",
        "( ( φ ∧ ( χ ∧ θ ) ) → ψ )",
        s5,
        ref="anasss",
        note="anasss s5",
    )

    # impbida: combine both directions
    res = lb.ref(
        "res",
        "( φ → ( ψ ↔ ( χ ∧ θ ) ) )",
        s4,
        s6,
        ref="impbida",
        note="impbida s4, s6",
    )

    return lb.build(res)


def prove_4anpull2(sys: System) -> Proof:
    """4anpull2: ( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ) ↔ ( ( φ ∧ χ ∧ θ ) ∧ ψ ).

    Rearrange four conjuncts: swap the second and third pair and group
    as a ternary conjunction with the fourth.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "4anpull2")

    # an42: ( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ) ↔ ( ( φ ∧ χ ) ∧ ( θ ∧ ψ ) )
    s1 = lb.ref(
        "s1",
        "( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ) ↔ ( ( φ ∧ χ ) ∧ ( θ ∧ ψ ) )",
        ref="an42",
        note="an42",
    )

    # 3an4anass with substitution φ→φ, ψ→χ, χ→θ, θ→ψ:
    # ( ( φ ∧ χ ∧ θ ) ∧ ψ ) ↔ ( ( φ ∧ χ ) ∧ ( θ ∧ ψ ) )
    s2 = lb.ref(
        "s2",
        "( ( φ ∧ χ ∧ θ ) ∧ ψ ) ↔ ( ( φ ∧ χ ) ∧ ( θ ∧ ψ ) )",
        ref="3an4anass",
        note="3an4anass",
    )

    # bitr4i: ( φ ↔ ψ ), ( χ ↔ ψ ) ⊢ ( φ ↔ χ )
    res = lb.ref(
        "res",
        "( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ) ↔ ( ( φ ∧ χ ∧ θ ) ∧ ψ )",
        s1,
        s2,
        ref="bitr4i",
        note="bitr4i",
    )

    return lb.build(res)


def prove_4anpull2OLD(sys: System) -> Proof:
    """4anpull2OLD: ( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ) ↔ ( ( φ ∧ χ ∧ θ ) ∧ ψ ).

    Rearrange four conjuncts: swap the second and third pair and group
    as a ternary conjunction with the fourth.
    (Contributed by NM, 3-Jan-1993.)
    (Proof modification is discouraged.)  (New usage is discouraged.)
    """
    lb = ProofBuilder(sys, "4anpull2OLD")

    # 3anass: ( φ ∧ χ ∧ θ ) ↔ ( φ ∧ ( χ ∧ θ ) )
    s_3anass = lb.ref(
        "s_3anass",
        "( φ ∧ χ ∧ θ ) ↔ ( φ ∧ ( χ ∧ θ ) )",
        ref="3anass",
        note="3anass",
    )

    # anbi1i: ( ( φ ∧ χ ∧ θ ) ∧ ψ ) ↔ ( ( φ ∧ ( χ ∧ θ ) ) ∧ ψ )
    s_anbi1i = lb.ref(
        "s_anbi1i",
        "( ( φ ∧ χ ∧ θ ) ∧ ψ ) ↔ ( ( φ ∧ ( χ ∧ θ ) ) ∧ ψ )",
        s_3anass,
        ref="anbi1i",
        note="anbi1i",
    )

    # anass: ( ( φ ∧ ( χ ∧ θ ) ) ∧ ψ ) ↔ ( φ ∧ ( ( χ ∧ θ ) ∧ ψ ) )
    s_anass1 = lb.ref(
        "s_anass1",
        "( ( φ ∧ ( χ ∧ θ ) ) ∧ ψ ) ↔ ( φ ∧ ( ( χ ∧ θ ) ∧ ψ ) )",
        ref="anass",
        note="anass",
    )

    # ancom: ( ( χ ∧ θ ) ∧ ψ ) ↔ ( ψ ∧ ( χ ∧ θ ) )
    s_ancom = lb.ref(
        "s_ancom",
        "( ( χ ∧ θ ) ∧ ψ ) ↔ ( ψ ∧ ( χ ∧ θ ) )",
        ref="ancom",
        note="ancom",
    )

    # anbi2i: ( φ ∧ ( ( χ ∧ θ ) ∧ ψ ) ) ↔ ( φ ∧ ( ψ ∧ ( χ ∧ θ ) ) )
    s_anbi2i = lb.ref(
        "s_anbi2i",
        "( φ ∧ ( ( χ ∧ θ ) ∧ ψ ) ) ↔ ( φ ∧ ( ψ ∧ ( χ ∧ θ ) ) )",
        s_ancom,
        ref="anbi2i",
        note="anbi2i",
    )

    # bitri s_anass1 s_anbi2i: ( ( φ ∧ ( χ ∧ θ ) ) ∧ ψ ) ↔ ( φ ∧ ( ψ ∧ ( χ ∧ θ ) ) )
    s_bitri1 = lb.ref(
        "s_bitri1",
        "( ( φ ∧ ( χ ∧ θ ) ) ∧ ψ ) ↔ ( φ ∧ ( ψ ∧ ( χ ∧ θ ) ) )",
        s_anass1,
        s_anbi2i,
        ref="bitri",
        note="bitri",
    )

    # bitri s_anbi1i s_bitri1: ( ( φ ∧ χ ∧ θ ) ∧ ψ ) ↔ ( φ ∧ ( ψ ∧ ( χ ∧ θ ) ) )
    s_bitri2 = lb.ref(
        "s_bitri2",
        "( ( φ ∧ χ ∧ θ ) ∧ ψ ) ↔ ( φ ∧ ( ψ ∧ ( χ ∧ θ ) ) )",
        s_anbi1i,
        s_bitri1,
        ref="bitri",
        note="bitri",
    )

    # anass: ( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ) ↔ ( φ ∧ ( ψ ∧ ( χ ∧ θ ) ) )
    s_anass2 = lb.ref(
        "s_anass2",
        "( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ) ↔ ( φ ∧ ( ψ ∧ ( χ ∧ θ ) ) )",
        ref="anass",
        note="anass",
    )

    # bitr4i s_anass2 s_bitri2: ( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ) ↔ ( ( φ ∧ χ ∧ θ ) ∧ ψ )
    res = lb.ref(
        "res",
        "( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ) ↔ ( ( φ ∧ χ ∧ θ ) ∧ ψ )",
        s_anass2,
        s_bitri2,
        ref="bitr4i",
        note="bitr4i",
    )

    return lb.build(res)


def prove_mp3an1i(sys: System) -> Proof:
    r"""mp3an1i: φ → ((χ ∧ θ) → τ).

    Hyp 1: ψ
    Hyp 2: φ → ((ψ ∧ χ ∧ θ) → τ)
    Concl: φ → ((χ ∧ θ) → τ)

    Inference form of mp3an1 where the first antecedent is provided.
    (Contributed by NM, 29-Dec-1992.)
    set.mm proof: com12 mp3an1.
    """
    lb = ProofBuilder(sys, "mp3an1i")
    h1 = lb.hyp("mp3an1i.1", "ψ")
    h2 = lb.hyp("mp3an1i.2", "φ → ((ψ ∧ χ ∧ θ) → τ)")
    s1 = lb.ref(
        "s1",
        "(ψ ∧ χ ∧ θ) → (φ → τ)",
        h2,
        ref="com12",
        note="com12 mp3an1i.2",
    )
    s2 = lb.ref(
        "s2",
        "(χ ∧ θ) → (φ → τ)",
        h1,
        s1,
        ref="mp3an1",
        note="mp3an1 mp3an1i.1, s1",
    )
    res = lb.ref(
        "res",
        "φ → ((χ ∧ θ) → τ)",
        s2,
        ref="com12",
        note="com12 s2",
    )
    return lb.build(res)


def prove_an33rean(sys: System) -> Proof:
    """an33rean: ( ( φ ∧ ψ ∧ χ ) ∧ ( θ ∧ τ ∧ η ) ∧ ( ζ ∧ σ ∧ ρ ) ) ↔ ( ( φ ∧ τ ∧ ρ ) ∧ ( ( ψ ∧ θ ) ∧ ( η ∧ σ ) ∧ ( χ ∧ ζ ) ) ).

    Rearrange three triples of conjuncts.
    """
    lb = ProofBuilder(sys, "an33rean")

    # Step 1: 3anass → (φ ∧ ψ ∧ χ) ↔ (φ ∧ (ψ ∧ χ))
    s1 = lb.ref("s1", "( φ ∧ ψ ∧ χ ) ↔ ( φ ∧ ( ψ ∧ χ ) )", ref="3anass", note="3anass")

    # Step 2: 3anan12 → (θ ∧ τ ∧ η) ↔ (τ ∧ (θ ∧ η))
    s2 = lb.ref("s2", "( θ ∧ τ ∧ η ) ↔ ( τ ∧ ( θ ∧ η ) )", ref="3anan12", note="3anan12")

    # Step 3: 3anrev → (ζ ∧ σ ∧ ρ) ↔ (ρ ∧ σ ∧ ζ)
    s3 = lb.ref("s3", "( ζ ∧ σ ∧ ρ ) ↔ ( ρ ∧ σ ∧ ζ )", ref="3anrev", note="3anrev")

    # Step 4: 3anass → (ρ ∧ σ ∧ ζ) ↔ (ρ ∧ (σ ∧ ζ))
    s4 = lb.ref("s4", "( ρ ∧ σ ∧ ζ ) ↔ ( ρ ∧ ( σ ∧ ζ ) )", ref="3anass", note="3anass")

    # Step 5: bitri with s3, s4 → (ζ ∧ σ ∧ ρ) ↔ (ρ ∧ (σ ∧ ζ))
    s5 = lb.ref(
        "s5",
        "( ζ ∧ σ ∧ ρ ) ↔ ( ρ ∧ ( σ ∧ ζ ) )",
        s3,
        s4,
        ref="bitri",
        note="bitri",
    )

    # Step 6: 3anbi123i with s1, s2, s5
    s6 = lb.ref(
        "s6",
        "( ( φ ∧ ψ ∧ χ ) ∧ ( θ ∧ τ ∧ η ) ∧ ( ζ ∧ σ ∧ ρ ) ) ↔ ( ( φ ∧ ( ψ ∧ χ ) ) ∧ ( τ ∧ ( θ ∧ η ) ) ∧ ( ρ ∧ ( σ ∧ ζ ) ) )",
        s1,
        s2,
        s5,
        ref="3anbi123i",
        note="3anbi123i",
    )

    # Step 7: 3an6
    s7 = lb.ref(
        "s7",
        "( ( φ ∧ ( ψ ∧ χ ) ) ∧ ( τ ∧ ( θ ∧ η ) ) ∧ ( ρ ∧ ( σ ∧ ζ ) ) ) ↔ ( ( φ ∧ τ ∧ ρ ) ∧ ( ( ψ ∧ χ ) ∧ ( θ ∧ η ) ∧ ( σ ∧ ζ ) ) )",
        ref="3an6",
        note="3an6",
    )

    # Step 8: anass → ((θ ∧ η) ∧ σ) ↔ (θ ∧ (η ∧ σ))
    s8 = lb.ref("s8", "( ( θ ∧ η ) ∧ σ ) ↔ ( θ ∧ ( η ∧ σ ) )", ref="anass", note="anass")

    # Step 9: anbi2i with s8 → ((ψ ∧ χ) ∧ ((θ ∧ η) ∧ σ)) ↔ ((ψ ∧ χ) ∧ (θ ∧ (η ∧ σ)))
    s9 = lb.ref(
        "s9",
        "( ( ψ ∧ χ ) ∧ ( ( θ ∧ η ) ∧ σ ) ) ↔ ( ( ψ ∧ χ ) ∧ ( θ ∧ ( η ∧ σ ) ) )",
        s8,
        ref="anbi2i",
        note="anbi2i",
    )

    # Step 10: an42 → ((ψ ∧ χ) ∧ (θ ∧ (η ∧ σ))) ↔ ((ψ ∧ θ) ∧ ((η ∧ σ) ∧ χ))
    s10 = lb.ref(
        "s10",
        "( ( ψ ∧ χ ) ∧ ( θ ∧ ( η ∧ σ ) ) ) ↔ ( ( ψ ∧ θ ) ∧ ( ( η ∧ σ ) ∧ χ ) )",
        ref="an42",
        note="an42",
    )

    # Step 11: bitri with s9, s10
    s11 = lb.ref(
        "s11",
        "( ( ψ ∧ χ ) ∧ ( ( θ ∧ η ) ∧ σ ) ) ↔ ( ( ψ ∧ θ ) ∧ ( ( η ∧ σ ) ∧ χ ) )",
        s9,
        s10,
        ref="bitri",
        note="bitri",
    )

    # Step 12: anass → (((ψ ∧ χ) ∧ (θ ∧ η)) ∧ σ) ↔ ((ψ ∧ χ) ∧ ((θ ∧ η) ∧ σ))
    s12 = lb.ref(
        "s12",
        "( ( ( ψ ∧ χ ) ∧ ( θ ∧ η ) ) ∧ σ ) ↔ ( ( ψ ∧ χ ) ∧ ( ( θ ∧ η ) ∧ σ ) )",
        ref="anass",
        note="anass",
    )

    # Step 13: anass → (((ψ ∧ θ) ∧ (η ∧ σ)) ∧ χ) ↔ ((ψ ∧ θ) ∧ ((η ∧ σ) ∧ χ))
    s13 = lb.ref(
        "s13",
        "( ( ( ψ ∧ θ ) ∧ ( η ∧ σ ) ) ∧ χ ) ↔ ( ( ψ ∧ θ ) ∧ ( ( η ∧ σ ) ∧ χ ) )",
        ref="anass",
        note="anass",
    )

    # Step 14: 3bitr4i with s11, s12, s13
    s14 = lb.ref(
        "s14",
        "( ( ( ψ ∧ χ ) ∧ ( θ ∧ η ) ) ∧ σ ) ↔ ( ( ( ψ ∧ θ ) ∧ ( η ∧ σ ) ) ∧ χ )",
        s11,
        s12,
        s13,
        ref="3bitr4i",
        note="3bitr4i",
    )

    # Step 15: anbi1i with s14
    s15 = lb.ref(
        "s15",
        "( ( ( ( ψ ∧ χ ) ∧ ( θ ∧ η ) ) ∧ σ ) ∧ ζ ) ↔ ( ( ( ( ψ ∧ θ ) ∧ ( η ∧ σ ) ) ∧ χ ) ∧ ζ )",
        s14,
        ref="anbi1i",
        note="anbi1i",
    )

    # Step 16: anass
    s16 = lb.ref(
        "s16",
        "( ( ( ( ψ ∧ χ ) ∧ ( θ ∧ η ) ) ∧ σ ) ∧ ζ ) ↔ ( ( ( ψ ∧ χ ) ∧ ( θ ∧ η ) ) ∧ ( σ ∧ ζ ) )",
        ref="anass",
        note="anass",
    )

    # Step 17: anass
    s17 = lb.ref(
        "s17",
        "( ( ( ( ψ ∧ θ ) ∧ ( η ∧ σ ) ) ∧ χ ) ∧ ζ ) ↔ ( ( ( ψ ∧ θ ) ∧ ( η ∧ σ ) ) ∧ ( χ ∧ ζ ) )",
        ref="anass",
        note="anass",
    )

    # Step 18: 3bitr3i with s15, s16, s17
    s18 = lb.ref(
        "s18",
        "( ( ( ψ ∧ χ ) ∧ ( θ ∧ η ) ) ∧ ( σ ∧ ζ ) ) ↔ ( ( ( ψ ∧ θ ) ∧ ( η ∧ σ ) ) ∧ ( χ ∧ ζ ) )",
        s15,
        s16,
        s17,
        ref="3bitr3i",
        note="3bitr3i",
    )

    # Step 19: df-3an
    s19 = lb.ref(
        "s19",
        "( ( ψ ∧ χ ) ∧ ( θ ∧ η ) ∧ ( σ ∧ ζ ) ) ↔ ( ( ( ψ ∧ χ ) ∧ ( θ ∧ η ) ) ∧ ( σ ∧ ζ ) )",
        ref="df-3an",
        note="df-3an",
    )

    # Step 20: df-3an
    s20 = lb.ref(
        "s20",
        "( ( ψ ∧ θ ) ∧ ( η ∧ σ ) ∧ ( χ ∧ ζ ) ) ↔ ( ( ( ψ ∧ θ ) ∧ ( η ∧ σ ) ) ∧ ( χ ∧ ζ ) )",
        ref="df-3an",
        note="df-3an",
    )

    # Step 21: 3bitr4i with s18, s19, s20
    s21 = lb.ref(
        "s21",
        "( ( ψ ∧ χ ) ∧ ( θ ∧ η ) ∧ ( σ ∧ ζ ) ) ↔ ( ( ψ ∧ θ ) ∧ ( η ∧ σ ) ∧ ( χ ∧ ζ ) )",
        s18,
        s19,
        s20,
        ref="3bitr4i",
        note="3bitr4i",
    )

    # Step 22: anbi2i with s21
    s22 = lb.ref(
        "s22",
        "( ( φ ∧ τ ∧ ρ ) ∧ ( ( ψ ∧ χ ) ∧ ( θ ∧ η ) ∧ ( σ ∧ ζ ) ) ) ↔ ( ( φ ∧ τ ∧ ρ ) ∧ ( ( ψ ∧ θ ) ∧ ( η ∧ σ ) ∧ ( χ ∧ ζ ) ) )",
        s21,
        ref="anbi2i",
        note="anbi2i",
    )

    # Step 23: 3bitri with s6, s7, s22
    res = lb.ref(
        "res",
        "( ( φ ∧ ψ ∧ χ ) ∧ ( θ ∧ τ ∧ η ) ∧ ( ζ ∧ σ ∧ ρ ) ) ↔ ( ( φ ∧ τ ∧ ρ ) ∧ ( ( ψ ∧ θ ) ∧ ( η ∧ σ ) ∧ ( χ ∧ ζ ) ) )",
        s6,
        s7,
        s22,
        ref="3bitri",
        note="3bitri",
    )

    return lb.build(res)


def prove_dfifp2(sys: System) -> Proof:
    """dfifp2: ( if- φ ψ χ ↔ ( ( φ → ψ ) ∧ ( ¬ φ → χ ) ) ).

    Alternate definition of the conditional operator if-.
    """
    lb = ProofBuilder(sys, "dfifp2")

    # df-ifp: ( if- φ ψ χ ↔ ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) ) )
    s1 = lb.ref(
        "s1",
        "( if- φ ψ χ ↔ ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) ) )",
        ref="df-ifp",
        note="df-ifp",
    )

    # cases2: ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) ) ↔ ( ( φ → ψ ) ∧ ( ¬ φ → χ ) )
    s2 = lb.ref(
        "s2",
        "( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) ) ↔ ( ( φ → ψ ) ∧ ( ¬ φ → χ ) )",
        ref="cases2",
        note="cases2",
    )

    # bitri: combine the two biconditionals
    res = lb.ref(
        "res",
        "( if- φ ψ χ ↔ ( ( φ → ψ ) ∧ ( ¬ φ → χ ) ) )",
        s1,
        s2,
        ref="bitri",
        note="bitri",
    )
    return lb.build(res)


def prove_noran(sys: System) -> Proof:
    """noran: ( φ ∧ ψ ) ↔ ( ( φ ⊽ φ ) ⊽ ( ψ ⊽ ψ ) ).

    Conjunction expressed in terms of NOR: ph ∧ ps is equivalent to
    ( ph ⊽ ph ) ⊽ ( ps ⊽ ps ).
    """
    lb = ProofBuilder(sys, "noran")

    # anor: ( φ ∧ ψ ) ↔ ¬ ( ¬ φ ∨ ¬ ψ )
    s1 = lb.ref(
        "s1",
        "( φ ∧ ψ ) ↔ ¬ ( ¬ φ ∨ ¬ ψ )",
        ref="anor",
        note="anor",
    )

    # nornot: ¬ φ ↔ ( φ ⊽ φ )
    s2 = lb.ref(
        "s2",
        "¬ φ ↔ ( φ ⊽ φ )",
        ref="nornot",
        note="nornot",
    )

    # nornot: ¬ ψ ↔ ( ψ ⊽ ψ )
    s3 = lb.ref(
        "s3",
        "¬ ψ ↔ ( ψ ⊽ ψ )",
        ref="nornot",
        note="nornot",
    )

    # orbi12i(s2, s3): ( ¬ φ ∨ ¬ ψ ) ↔ ( ( φ ⊽ φ ) ∨ ( ψ ⊽ ψ ) )
    s4 = lb.ref(
        "s4",
        "( ¬ φ ∨ ¬ ψ ) ↔ ( ( φ ⊽ φ ) ∨ ( ψ ⊽ ψ ) )",
        s2,
        s3,
        ref="orbi12i",
        note="orbi12i",
    )

    # xchbinx(s1, s4): ( φ ∧ ψ ) ↔ ¬ ( ( φ ⊽ φ ) ∨ ( ψ ⊽ ψ ) )
    s5 = lb.ref(
        "s5",
        "( φ ∧ ψ ) ↔ ¬ ( ( φ ⊽ φ ) ∨ ( ψ ⊽ ψ ) )",
        s1,
        s4,
        ref="xchbinx",
        note="xchbinx",
    )

    # df-nor: ( ( φ ⊽ φ ) ⊽ ( ψ ⊽ ψ ) ) ↔ ¬ ( ( φ ⊽ φ ) ∨ ( ψ ⊽ ψ ) )
    s6 = lb.ref(
        "s6",
        "( ( φ ⊽ φ ) ⊽ ( ψ ⊽ ψ ) ) ↔ ¬ ( ( φ ⊽ φ ) ∨ ( ψ ⊽ ψ ) )",
        ref="df-nor",
        note="df-nor",
    )

    # bitr4i(s5, s6): ( φ ∧ ψ ) ↔ ( ( φ ⊽ φ ) ⊽ ( ψ ⊽ ψ ) )
    res = lb.ref(
        "res",
        "( φ ∧ ψ ) ↔ ( ( φ ⊽ φ ) ⊽ ( ψ ⊽ ψ ) )",
        s5,
        s6,
        ref="bitr4i",
        note="bitr4i",
    )

    return lb.build(res)


def prove_3ori(sys: System) -> Proof:
    """3ori: ( ¬ φ ∧ ¬ ψ ) → χ.

    Given ( φ ∨ ψ ∨ χ ), the negation of the first two disjuncts
    implies the third.
    """
    lb = ProofBuilder(sys, "3ori")
    h = lb.hyp("3ori.1", "φ ∨ ψ ∨ χ")

    # df-3or: ( φ ∨ ψ ∨ χ ) ↔ ( ( φ ∨ ψ ) ∨ χ )
    s1 = lb.ref(
        "s1",
        "( φ ∨ ψ ∨ χ ) ↔ ( ( φ ∨ ψ ) ∨ χ )",
        ref="df-3or",
        note="df-3or",
    )

    # mpbi: from 3ori.1 and df-3or, derive ( ( φ ∨ ψ ) ∨ χ )
    s2 = lb.ref(
        "s2",
        "( φ ∨ ψ ) ∨ χ",
        h,
        s1,
        ref="mpbi",
        note="mpbi",
    )

    # ori: ( ( φ ∨ ψ ) ∨ χ )  →  ( ¬ ( φ ∨ ψ ) → χ )
    s3 = lb.ref(
        "s3",
        "¬ ( φ ∨ ψ ) → χ",
        s2,
        ref="ori",
        note="ori",
    )

    # ioran: ¬ ( φ ∨ ψ ) ↔ ( ¬ φ ∧ ¬ ψ )
    s4 = lb.ref(
        "s4",
        "¬ ( φ ∨ ψ ) ↔ ( ¬ φ ∧ ¬ ψ )",
        ref="ioran",
        note="ioran",
    )

    # sylbir: from ioran (sylbir.1) and s3 (sylbir.2),
    # derive ( ¬ φ ∧ ¬ ψ ) → χ
    res = lb.ref(
        "res",
        "( ¬ φ ∧ ¬ ψ ) → χ",
        s4,
        s3,
        ref="sylbir",
        note="sylbir",
    )

    return lb.build(res)


def prove_nanbi12(sys: System) -> Proof:
    """nanbi12: ( ( φ ↔ ψ ) ∧ ( χ ↔ θ ) ) → ( ( φ ⊼ χ ) ↔ ( ψ ⊼ θ ) ).

    NAND respects biconditional equivalence in both arguments
    simultaneously.
    """
    lb = ProofBuilder(sys, "nanbi12")

    # nanbi1: ( φ ↔ ψ ) → ( ( φ ⊼ χ ) ↔ ( ψ ⊼ χ ) )
    s1 = lb.ref(
        "s1",
        "( φ ↔ ψ ) → ( ( φ ⊼ χ ) ↔ ( ψ ⊼ χ ) )",
        ref="nanbi1",
        note="nanbi1",
    )

    # nanbi2: ( χ ↔ θ ) → ( ( ψ ⊼ χ ) ↔ ( ψ ⊼ θ ) )
    s2 = lb.ref(
        "s2",
        "( χ ↔ θ ) → ( ( ψ ⊼ χ ) ↔ ( ψ ⊼ θ ) )",
        ref="nanbi2",
        note="nanbi2",
    )

    # sylan9bb: ( ( φ ↔ ψ ) ∧ ( χ ↔ θ ) ) → ( ( φ ⊼ χ ) ↔ ( ψ ⊼ θ ) )
    res = lb.ref(
        "res",
        "( ( φ ↔ ψ ) ∧ ( χ ↔ θ ) ) → ( ( φ ⊼ χ ) ↔ ( ψ ⊼ θ ) )",
        s1,
        s2,
        ref="sylan9bb",
        note="sylan9bb nanbi1, nanbi2",
    )

    return lb.build(res)


def prove_nanbi12i(sys: System) -> Proof:
    """nanbi12i: ( φ ⊼ χ ) ↔ ( ψ ⊼ θ ).

    Inference form of nanbi12.
    """
    lb = ProofBuilder(sys, "nanbi12i")
    h1 = lb.hyp("nanbii.1", "( φ ↔ ψ )")
    h2 = lb.hyp("nanbi12i.2", "( χ ↔ θ )")
    s1 = lb.ref(
        "s1",
        "( ( φ ↔ ψ ) ∧ ( χ ↔ θ ) ) → ( ( φ ⊼ χ ) ↔ ( ψ ⊼ θ ) )",
        ref="nanbi12",
        note="nanbi12",
    )
    res = lb.ref(
        "res",
        "( φ ⊼ χ ) ↔ ( ψ ⊼ θ )",
        h1,
        h2,
        s1,
        ref="mp2an",
        note="mp2an hyp1, hyp2, nanbi12",
    )
    return lb.build(res)


def prove_nanbi12d(sys: System) -> Proof:
    """nanbi12d: φ → ( ( ψ ⊼ θ ) ↔ ( χ ⊼ τ ) ).

    Deduction form of nanbi12.
    """
    lb = ProofBuilder(sys, "nanbi12d")

    # nanbi12d.1: φ → ( ψ ↔ χ )
    h1 = lb.hyp("nanbid.1", "( φ → ( ψ ↔ χ ) )")

    # nanbi12d.2: φ → ( θ ↔ τ )
    h2 = lb.hyp("nanbi12d.2", "( φ → ( θ ↔ τ ) )")

    # nanbi12: ( ( ψ ↔ χ ) ∧ ( θ ↔ τ ) ) → ( ( ψ ⊼ θ ) ↔ ( χ ⊼ τ ) )
    s1 = lb.ref(
        "s1",
        "( ( ( ψ ↔ χ ) ∧ ( θ ↔ τ ) ) → ( ( ψ ⊼ θ ) ↔ ( χ ⊼ τ ) ) )",
        ref="nanbi12",
        note="nanbi12",
    )

    # syl2anc: φ → ( ψ ↔ χ ) , φ → ( θ ↔ τ ) , nanbi12 ⇒ φ → ( ( ψ ⊼ θ ) ↔ ( χ ⊼ τ ) )
    res = lb.ref(
        "res",
        "( φ → ( ( ψ ⊼ θ ) ↔ ( χ ⊼ τ ) ) )",
        h1,
        h2,
        s1,
        ref="syl2anc",
        note="syl2anc",
    )

    return lb.build(res)


def prove_dfifp7(sys: System) -> Proof:
    """dfifp7: ( if- φ ψ χ ↔ ( ( χ → φ ) → ( φ ∧ ψ ) ) ).

    Alternate definition of if- using implication and conjunction.
    """
    lb = ProofBuilder(sys, "dfifp7")

    # orcom: ( ( φ ∧ ψ ) ∨ ¬ ( χ → φ ) ) ↔ ( ¬ ( χ → φ ) ∨ ( φ ∧ ψ ) )
    s1 = lb.ref(
        "s1",
        "( ( φ ∧ ψ ) ∨ ¬ ( χ → φ ) ) ↔ ( ¬ ( χ → φ ) ∨ ( φ ∧ ψ ) )",
        ref="orcom",
        note="orcom",
    )

    # dfifp6: ( if- φ ψ χ ↔ ( ( φ ∧ ψ ) ∨ ¬ ( χ → φ ) ) )
    s2 = lb.ref(
        "s2",
        "( if- φ ψ χ ↔ ( ( φ ∧ ψ ) ∨ ¬ ( χ → φ ) ) )",
        ref="dfifp6",
        note="dfifp6",
    )

    # imor: ( ( χ → φ ) → ( φ ∧ ψ ) ) ↔ ( ¬ ( χ → φ ) ∨ ( φ ∧ ψ ) )
    s3 = lb.ref(
        "s3",
        "( ( χ → φ ) → ( φ ∧ ψ ) ) ↔ ( ¬ ( χ → φ ) ∨ ( φ ∧ ψ ) )",
        ref="imor",
        note="imor",
    )

    # 3bitr4i: ( if- φ ψ χ ↔ ( ( χ → φ ) → ( φ ∧ ψ ) ) )
    res = lb.ref(
        "res",
        "( if- φ ψ χ ↔ ( ( χ → φ ) → ( φ ∧ ψ ) ) )",
        s1,
        s2,
        s3,
        ref="3bitr4i",
        note="3bitr4i",
    )

    return lb.build(res)


def prove_equtr2(sys: System) -> Proof:
    """equtr2: ( x = z ∧ y = z ) → x = y.

    Equality transitivity: from two equalities with a common term z,
    the conjunction implies the remaining equality.
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: weq equeucl imp.
    """
    lb = ProofBuilder(sys, "equtr2")
    s1 = lb.ref(
        "s1",
        "x = z → ( y = z → x = y )",
        ref="equeucl",
        note="equeucl",
    )
    res = lb.ref(
        "res",
        "( x = z ∧ y = z ) → x = y",
        s1,
        ref="imp",
        note="imp",
    )
    return lb.build(res)


def prove_axia3(sys: System) -> Proof:
    """axia3: φ → (ψ → (φ ∧ ψ)).

    Conjunction introduction (axiom form of pm3.2).
    """
    lb = ProofBuilder(sys, "axia3")
    res = lb.ref(
        "res",
        "φ → (ψ → (φ ∧ ψ))",
        ref="pm3.2",
        note="pm3.2",
    )
    return lb.build(res)


def prove_axia1(sys: System) -> Proof:
    """axia1: ( φ ∧ ψ ) → φ.

    Simplification — the left conjunct follows from a conjunction.
    (Contributed by NM, 5-Jan-1993.)
    """
    lb = ProofBuilder(sys, "axia1")
    res = lb.ref(
        "res",
        "( φ ∧ ψ ) → φ",
        ref="simpl",
        note="simpl",
    )
    return lb.build(res)


def prove_axia2(sys: System) -> Proof:
    """axia2: ( φ ∧ ψ ) → ψ.

    Simplification — the right conjunct follows from a conjunction.
    (Contributed by NM, 5-Jan-1993.)
    """
    lb = ProofBuilder(sys, "axia2")
    res = lb.ref(
        "res",
        "( φ ∧ ψ ) → ψ",
        ref="simpr",
        note="simpr",
    )
    return lb.build(res)
