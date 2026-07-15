from __future__ import annotations

from collections.abc import Callable, Mapping
from typing import TypeAlias

from skfd.proof import Proof, ProofBuilder, SystemCore

from . import _structures  # noqa: F401

System: TypeAlias = SystemCore
PredicateTheoremCtor = Callable[[SystemCore], Proof]


def prove_equvini(sys: System) -> Proof:
    """equvini: x = y → ∃ z ( x = z ∧ z = y ).
    There exists a variable z such that x and y are both equal to it.
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "equvini")
    # 1. equtr: z = x → ( x = y → z = y )
    s1 = lb.ref(
        "s1",
        "z = x → ( x = y → z = y )",
        ref="equtr",
        note="equtr",
    )
    # 2. equcomi: z = x → x = z
    s2 = lb.ref(
        "s2",
        "z = x → x = z",
        ref="equcomi",
        note="equcomi",
    )
    # 3. jctild(1, 2): z = x → ( x = y → ( x = z ∧ z = y ) )
    s3 = lb.ref(
        "s3",
        "z = x → ( x = y → ( x = z ∧ z = y ) )",
        s1,
        s2,
        ref="jctild",
        note="jctild equtr, equcomi",
    )
    # 4. 19.8a: ( x = z ∧ z = y ) → ∃ z ( x = z ∧ z = y )
    s4 = lb.ref(
        "s4",
        "( x = z ∧ z = y ) → ∃ z ( x = z ∧ z = y )",
        ref="19.8a",
        note="19.8a",
    )
    # 5. syl6(3, 4): z = x → ( x = y → ∃ z ( x = z ∧ z = y ) )
    s5 = lb.ref(
        "s5",
        "z = x → ( x = y → ∃ z ( x = z ∧ z = y ) )",
        s3,
        s4,
        ref="syl6",
        note="syl6 jctild, 19.8a",
    )
    # 6. ax13: ¬ z = x → ( x = y → ∀ z x = y )
    s6 = lb.ref(
        "s6",
        "¬ z = x → ( x = y → ∀ z x = y )",
        ref="ax13",
        note="ax13",
    )
    # 7. ax6e: ∃ z z = x
    s7 = lb.ref(
        "s7",
        "∃ z z = x",
        ref="ax6e",
        note="ax6e",
    )
    # 9. eximii(7, 3): ∃ z ( x = y → ( x = z ∧ z = y ) )
    s9 = lb.ref(
        "s9",
        "∃ z ( x = y → ( x = z ∧ z = y ) )",
        s7,
        s3,
        ref="eximii",
        note="eximii ax6e, jctild",
    )
    # 10. 19.35i(9): ( ∀ z x = y ) → ∃ z ( x = z ∧ z = y )
    s10 = lb.ref(
        "s10",
        "∀ z x = y → ∃ z ( x = z ∧ z = y )",
        s9,
        ref="19.35i",
        note="19.35i eximii",
    )
    # 11. syl6(6, 10): ¬ z = x → ( x = y → ∃ z ( x = z ∧ z = y ) )
    s11 = lb.ref(
        "s11",
        "¬ z = x → ( x = y → ∃ z ( x = z ∧ z = y ) )",
        s6,
        s10,
        ref="syl6",
        note="syl6 ax13, 19.35i",
    )
    # 12. pm2.61i(5, 11): ( x = y → ∃ z ( x = z ∧ z = y ) )
    res = lb.ref(
        "res",
        "x = y → ∃ z ( x = z ∧ z = y )",
        s5,
        s11,
        ref="pm2.61i",
        note="pm2.61i syl6, syl6",
    )
    return lb.build(res)


def prove_equvel(sys: System) -> Proof:
    """equvel: ∀ z ( z = x ↔ z = y ) → x = y.

    If two variables are equivalent to a third for all values of that
    third variable, then they are equal.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "equvel")

    s1 = lb.ref(
        "s1",
        "∀ z ( z = x ↔ z = y ) → ( ∀ z z = x ↔ ∀ z z = y )",
        ref="albi",
        note="albi",
    )
    s2 = lb.ref("s2", "∃ z z = y", ref="ax6e", note="ax6e")
    s3 = lb.ref(
        "s3",
        "( z = x ↔ z = y ) → ( z = y → z = x )",
        ref="biimpr",
        note="biimpr",
    )
    s4 = lb.ref("s4", "z = x → ( z = y → x = y )", ref="ax7", note="ax7")
    s5 = lb.ref(
        "s5",
        "( z = x ↔ z = y ) → ( z = y → x = y )",
        s3,
        s4,
        ref="syli",
        note="syli biimpr, ax7",
    )
    s6 = lb.ref(
        "s6",
        "z = y → ( ( z = x ↔ z = y ) → x = y )",
        s5,
        ref="com12",
        note="com12 syli",
    )
    s7 = lb.ref(
        "s7",
        "∃ z ( ( z = x ↔ z = y ) → x = y )",
        s2,
        s6,
        ref="eximii",
        note="eximii ax6e, com12",
    )
    s8 = lb.ref(
        "s8",
        "∀ z ( z = x ↔ z = y ) → ∃ z x = y",
        s7,
        ref="19.35i",
        note="19.35i eximii",
    )
    s9 = lb.ref(
        "s9",
        "z = x → ( ∀ z z = y → x = y )",
        s4,
        ref="spsd",
        note="spsd ax7",
    )
    s10 = lb.ref(
        "s10",
        "∀ z z = x → ( ∀ z z = y → x = y )",
        s9,
        ref="sps",
        note="sps spsd",
    )
    s11 = lb.ref(
        "s11",
        "∀ z z = x → ( ∀ z z = y → ( ∃ z x = y → x = y ) )",
        s10,
        ref="a1dd",
        note="a1dd sps",
    )
    s12 = lb.ref(
        "s12",
        "( ¬ ∀ z z = x ∧ ¬ ∀ z z = y ) → Ⅎ z x = y",
        ref="nfeqf",
        note="nfeqf",
    )
    s13 = lb.ref(
        "s13",
        "( ¬ ∀ z z = x ∧ ¬ ∀ z z = y ) → ( ∃ z x = y → x = y )",
        s12,
        ref="19.9d",
        note="19.9d nfeqf",
    )
    s14 = lb.ref(
        "s14",
        "¬ ∀ z z = x → ( ¬ ∀ z z = y → ( ∃ z x = y → x = y ) )",
        s13,
        ref="ex",
        note="ex 19.9d",
    )
    s15 = lb.ref(
        "s15",
        "( ∀ z z = x ↔ ∀ z z = y ) → ( ∃ z x = y → x = y )",
        s11,
        s14,
        ref="bija",
        note="bija a1dd, ex",
    )
    res = lb.ref(
        "res",
        "∀ z ( z = x ↔ z = y ) → x = y",
        s1,
        s8,
        s15,
        ref="sylc",
        note="sylc albi, 19.35i, bija",
    )

    return lb.build(res)


def prove_eu1(sys: System) -> Proof:
    """eu1: ∃! x φ ↔ ∃ x ( φ ∧ ∀ y ( [ y / x ] φ → x = y ) ).

    Alternate definition of existential uniqueness using substitution
    and universal quantification.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "eu1")
    hyp_nf = lb.hyp("eu1.nf", "Ⅎ y φ")

    # nfs1v: Ⅎ x [ y / x ] φ
    s_nfs1v = lb.ref("s_nfs1v", "Ⅎ x [ y x φ", ref="nfs1v", note="nfs1v")

    # sb8euv: ∃! x φ ↔ ∃! y [ y / x ] φ
    s_sb8euv = lb.ref(
        "s_sb8euv",
        "∃! x φ ↔ ∃! y [ y x φ",
        hyp_nf,
        ref="sb8euv",
        note="sb8euv",
    )

    # euf: ∃! y [ y / x ] φ ↔ ∃ x ∀ y ( [ y / x ] φ ↔ y = x )
    s_euf = lb.ref(
        "s_euf",
        "∃! y [ y x φ ↔ ∃ x ∀ y ( [ y x φ ↔ y = x )",
        s_nfs1v,
        ref="euf",
        note="euf",
    )

    # bitri sb8euv, euf: ∃! x φ ↔ ∃ x ∀ y ( [ y / x ] φ ↔ y = x )
    s_bitri1 = lb.ref(
        "s_bitri1",
        "∃! x φ ↔ ∃ x ∀ y ( [ y x φ ↔ y = x )",
        s_sb8euv,
        s_euf,
        ref="bitri",
        note="bitri sb8euv, euf",
    )

    # albiim: ∀ y ( [ y / x ] φ ↔ y = x ) ↔ ( ∀ y ( [ y / x ] φ → y = x ) ∧ ∀ y ( y = x → [ y / x ] φ ) )
    s_albiim = lb.ref(
        "s_albiim",
        "∀ y ( [ y x φ ↔ y = x ) ↔ ( ∀ y ( [ y x φ → y = x ) ∧ ∀ y ( y = x → [ y x φ ) )",
        ref="albiim",
        note="albiim",
    )

    # exbii albiim:
    # ∃ x ∀ y ( [ y / x ] φ ↔ y = x ) ↔ ∃ x ( ∀ y ( [ y / x ] φ → y = x ) ∧ ∀ y ( y = x → [ y / x ] φ ) )
    s_exbii1 = lb.ref(
        "s_exbii1",
        "∃ x ∀ y ( [ y x φ ↔ y = x ) ↔ ∃ x ( ∀ y ( [ y x φ → y = x ) ∧ ∀ y ( y = x → [ y x φ ) )",
        s_albiim,
        ref="exbii",
        note="exbii albiim",
    )

    # equcom: x = y ↔ y = x
    s_equcom = lb.ref("s_equcom", "x = y ↔ y = x", ref="equcom", note="equcom")

    # imbi2i equcom: ( [ y / x ] φ → x = y ) ↔ ( [ y / x ] φ → y = x )
    s_imbi2i = lb.ref(
        "s_imbi2i",
        "( [ y x φ → x = y ) ↔ ( [ y x φ → y = x )",
        s_equcom,
        ref="imbi2i",
        note="imbi2i equcom",
    )

    # albii imbi2i: ∀ y ( [ y / x ] φ → x = y ) ↔ ∀ y ( [ y / x ] φ → y = x )
    s_albii = lb.ref(
        "s_albii",
        "∀ y ( [ y x φ → x = y ) ↔ ∀ y ( [ y x φ → y = x )",
        s_imbi2i,
        ref="albii",
        note="albii imbi2i",
    )

    # bicomi albii: ∀ y ( [ y / x ] φ → y = x ) ↔ ∀ y ( [ y / x ] φ → x = y )
    s_bicomi1 = lb.ref(
        "s_bicomi1",
        "∀ y ( [ y x φ → y = x ) ↔ ∀ y ( [ y x φ → x = y )",
        s_albii,
        ref="bicomi",
        note="bicomi albii",
    )

    # sb6rfv: φ ↔ ∀ y ( y = x → [ y / x ] φ )
    s_sb6rfv = lb.ref(
        "s_sb6rfv",
        "φ ↔ ∀ y ( y = x → [ y x φ )",
        hyp_nf,
        ref="sb6rfv",
        note="sb6rfv",
    )

    # bicomi sb6rfv: ∀ y ( y = x → [ y / x ] φ ) ↔ φ
    s_bicomi2 = lb.ref(
        "s_bicomi2",
        "∀ y ( y = x → [ y x φ ) ↔ φ",
        s_sb6rfv,
        ref="bicomi",
        note="bicomi sb6rfv",
    )

    # anbi12ci:
    # ( ∀ y ( [ y / x ] φ → y = x ) ∧ ∀ y ( y = x → [ y / x ] φ ) )
    #   ↔ ( φ ∧ ∀ y ( [ y / x ] φ → x = y ) )
    s_anbi12ci = lb.ref(
        "s_anbi12ci",
        "( ∀ y ( [ y x φ → y = x ) ∧ ∀ y ( y = x → [ y x φ ) ) ↔ ( φ ∧ ∀ y ( [ y x φ → x = y ) )",
        s_bicomi1,
        s_bicomi2,
        ref="anbi12ci",
        note="anbi12ci bicomi, bicomi",
    )

    # exbii anbi12ci:
    # ∃ x ( ∀ y ( [ y / x ] φ → y = x ) ∧ ∀ y ( y = x → [ y / x ] φ ) )
    #   ↔ ∃ x ( φ ∧ ∀ y ( [ y / x ] φ → x = y ) )
    s_exbii2 = lb.ref(
        "s_exbii2",
        "∃ x ( ∀ y ( [ y x φ → y = x ) ∧ ∀ y ( y = x → [ y x φ ) ) ↔ ∃ x ( φ ∧ ∀ y ( [ y x φ → x = y ) )",
        s_anbi12ci,
        ref="exbii",
        note="exbii anbi12ci",
    )

    # bicomi s_exbii2:
    # ∃ x ( φ ∧ ∀ y ( [ y / x ] φ → x = y ) )
    #   ↔ ∃ x ( ∀ y ( [ y / x ] φ → y = x ) ∧ ∀ y ( y = x → [ y / x ] φ ) )
    s_bicomi3 = lb.ref(
        "s_bicomi3",
        "∃ x ( φ ∧ ∀ y ( [ y x φ → x = y ) ) ↔ ∃ x ( ∀ y ( [ y x φ → y = x ) ∧ ∀ y ( y = x → [ y x φ ) )",
        s_exbii2,
        ref="bicomi",
        note="bicomi exbii",
    )

    # 3bitr4i s_exbii1, s_bitri1, s_bicomi3:
    # ∃! x φ ↔ ∃ x ( φ ∧ ∀ y ( [ y / x ] φ → x = y ) )
    res = lb.ref(
        "res",
        "∃! x φ ↔ ∃ x ( φ ∧ ∀ y ( [ y x φ → x = y ) )",
        s_exbii1,
        s_bitri1,
        s_bicomi3,
        ref="3bitr4i",
        note="3bitr4i exbii, bitri, bicomi",
    )

    return lb.build(res)


def prove_eu2(sys: System) -> Proof:
    """eu2: ∃! x φ ↔ ( ∃ x φ ∧ ∀ x ∀ y ( ( φ ∧ [ y / x ] φ ) → x = y ) ).

    Equivalent definition of "exists exactly one" using substitution.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "eu2")
    hyp_nf = lb.hyp("eu2.nf", "Ⅎ y φ")
    # df-eu: ∃! x φ ↔ ( ∃ x φ ∧ ∃* x φ )
    s1 = lb.ref(
        "s1",
        "∃! x φ ↔ ( ∃ x φ ∧ ∃* x φ )",
        ref="df-eu",
        note="df-eu",
    )
    # mo3: ∃* x φ ↔ ∀ x ∀ y ( ( φ ∧ [ y / x ] φ ) → x = y )
    s2 = lb.ref(
        "s2",
        "∃* x φ ↔ ∀ x ∀ y ( ( φ ∧ [ y / x ] φ ) → x = y )",
        hyp_nf,
        ref="mo3",
        note="mo3",
    )
    # anbi2i: ( ∃ x φ ∧ ∃* x φ ) ↔ ( ∃ x φ ∧ ∀ x ∀ y ( ( φ ∧ [ y / x ] φ ) → x = y ) )
    s3 = lb.ref(
        "s3",
        "( ∃ x φ ∧ ∃* x φ ) ↔ ( ∃ x φ ∧ ∀ x ∀ y ( ( φ ∧ [ y / x ] φ ) → x = y ) )",
        s2,
        ref="anbi2i",
        note="anbi2i mo3",
    )
    # bitri: ∃! x φ ↔ ( ∃ x φ ∧ ∀ x ∀ y ( ( φ ∧ [ y / x ] φ ) → x = y ) )
    res = lb.ref(
        "res",
        "∃! x φ ↔ ( ∃ x φ ∧ ∀ x ∀ y ( ( φ ∧ [ y / x ] φ ) → x = y ) )",
        s1,
        s3,
        ref="bitri",
        note="bitri df-eu, anbi2i",
    )
    return lb.build(res)


def prove_eu4(sys: System) -> Proof:
    """eu4: ∃! x φ ↔ ( ∃ x φ ∧ ∀ x ∀ y ( ( φ ∧ ψ ) → x = y ) ).
    Existence of a unique formula expressed using implicit substitution.
    (Contributed by NM, 26-Sep-1993.)
    """
    lb = ProofBuilder(sys, "eu4")
    hyp = lb.hyp("eu4.1", "x = y → ( φ ↔ ψ )")
    s1 = lb.ref(
        "s1",
        "∃! x φ ↔ ( ∃ x φ ∧ ∃* x φ )",
        ref="df-eu",
        note="df-eu",
    )
    s2 = lb.ref(
        "s2",
        "∃* x φ ↔ ∀ x ∀ y ( ( φ ∧ ψ ) → x = y )",
        hyp,
        ref="mo4",
        note="mo4",
    )
    s3 = lb.ref(
        "s3",
        "( ∃ x φ ∧ ∃* x φ ) ↔ ( ∃ x φ ∧ ∀ x ∀ y ( ( φ ∧ ψ ) → x = y ) )",
        s2,
        ref="anbi2i",
        note="anbi2i mo4",
    )
    res = lb.ref(
        "res",
        "∃! x φ ↔ ( ∃ x φ ∧ ∀ x ∀ y ( ( φ ∧ ψ ) → x = y ) )",
        s1,
        s3,
        ref="bitri",
        note="bitri df-eu, anbi2i",
    )
    return lb.build(res)


def prove_excomim(sys: System) -> Proof:
    """excomim: ∃ x ∃ y φ → ∃ y ∃ x φ.
    Inference form of excom: commutation of existential quantifiers.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "excomim")
    # excom: ∃ x ∃ y φ ↔ ∃ y ∃ x φ
    s1 = lb.ref(
        "s1",
        "∃ x ∃ y φ ↔ ∃ y ∃ x φ",
        ref="excom",
        note="excom",
    )
    # biimpi: forward implication from the biconditional
    res = lb.ref(
        "res",
        "∃ x ∃ y φ → ∃ y ∃ x φ",
        s1,
        ref="biimpi",
        note="biimpi excom",
    )
    return lb.build(res)


def prove_excomimw(sys: System) -> Proof:
    """excomimw: ∃ x ∃ y φ → ∃ y ∃ x φ.
    Weak version of excomim. Uses only Tarski's FOL axiom schemes.
    (Contributed by BTernaryTau, 23-Jun-2025.)
    """
    lb = ProofBuilder(sys, "excomimw")
    hyp = lb.hyp("excomimw.1", "x = z → ( φ ↔ ψ )")
    # notbid: x = z → ( ¬ φ ↔ ¬ ψ )
    s_notbid = lb.ref(
        "s_notbid",
        "x = z → ( ¬ φ ↔ ¬ ψ )",
        hyp,
        ref="notbid",
        note="notbid",
    )
    # alcomimw: ∀ y ∀ x ¬ φ → ∀ x ∀ y ¬ φ
    s_alcomimw = lb.ref(
        "s_alcomimw",
        "∀ y ∀ x ¬ φ → ∀ x ∀ y ¬ φ",
        s_notbid,
        ref="alcomimw",
        note="alcomimw",
    )
    # con3i: ¬ ∀ x ∀ y ¬ φ → ¬ ∀ y ∀ x ¬ φ
    s_con3i = lb.ref(
        "s_con3i",
        "¬ ∀ x ∀ y ¬ φ → ¬ ∀ y ∀ x ¬ φ",
        s_alcomimw,
        ref="con3i",
        note="con3i",
    )
    # 2exnaln: ∃ x ∃ y φ ↔ ¬ ∀ x ∀ y ¬ φ
    s_2exnaln1 = lb.ref(
        "s_2exnaln1",
        "∃ x ∃ y φ ↔ ¬ ∀ x ∀ y ¬ φ",
        ref="2exnaln",
        note="2exnaln",
    )
    # 2exnaln: ∃ y ∃ x φ ↔ ¬ ∀ y ∀ x ¬ φ
    s_2exnaln2 = lb.ref(
        "s_2exnaln2",
        "∃ y ∃ x φ ↔ ¬ ∀ y ∀ x ¬ φ",
        ref="2exnaln",
        note="2exnaln",
    )
    # 3imtr4i: ∃ x ∃ y φ → ∃ y ∃ x φ
    res = lb.ref(
        "res",
        "∃ x ∃ y φ → ∃ y ∃ x φ",
        s_con3i,
        s_2exnaln1,
        s_2exnaln2,
        ref="3imtr4i",
        note="3imtr4i",
    )
    return lb.build(res)


def prove_excomw(sys: System) -> Proof:
    """excomw: ∃ x ∃ y φ ↔ ∃ y ∃ x φ.
    Weak version of excom. Uses only Tarski's FOL axiom schemes.
    (Contributed by BTernaryTau, 23-Jun-2025.)
    """
    lb = ProofBuilder(sys, "excomw")
    h1 = lb.hyp("excomw.1", "x = w → ( φ ↔ ψ )")
    h2 = lb.hyp("excomw.2", "y = z → ( φ ↔ χ )")
    # excomimw with h1: ∃ x ∃ y φ → ∃ y ∃ x φ
    s1 = lb.ref(
        "s1",
        "∃ x ∃ y φ → ∃ y ∃ x φ",
        h1,
        ref="excomimw",
        note="excomimw",
    )
    # excomimw with h2: ∃ y ∃ x φ → ∃ x ∃ y φ
    s2 = lb.ref(
        "s2",
        "∃ y ∃ x φ → ∃ x ∃ y φ",
        h2,
        ref="excomimw",
        note="excomimw",
    )
    # impbii: (→ direction) + (← direction) → ↔
    res = lb.ref(
        "res",
        "∃ x ∃ y φ ↔ ∃ y ∃ x φ",
        s1,
        s2,
        ref="impbii",
        note="impbii",
    )
    return lb.build(res)


def prove_exexw(sys: System) -> Proof:
    """exexw: ∃ x φ ↔ ∃ x ∃ x φ.
    Existential quantification over a given variable is idempotent.
    Weak version of bj-exexbiex, requiring fewer axioms.
    (Contributed by GG, 4-Nov-2024.)
    """
    lb = ProofBuilder(sys, "exexw")
    hyp = lb.hyp("exexw.1", "x = y → ( φ ↔ ψ )")
    # notbid: x = y → ( ¬ φ ↔ ¬ ψ )
    s_notbid = lb.ref(
        "s_notbid",
        "x = y → ( ¬ φ ↔ ¬ ψ )",
        hyp,
        ref="notbid",
        note="notbid",
    )
    # hba1w: ∀ x ¬ φ → ∀ x ∀ x ¬ φ
    s_hba1w = lb.ref(
        "s_hba1w",
        "∀ x ¬ φ → ∀ x ∀ x ¬ φ",
        s_notbid,
        ref="hba1w",
        note="hba1w",
    )
    # spw: ∀ x ¬ φ → ¬ φ
    s_spw = lb.ref(
        "s_spw",
        "∀ x ¬ φ → ¬ φ",
        s_notbid,
        ref="spw",
        note="spw",
    )
    # alimi: ∀ x ∀ x ¬ φ → ∀ x ¬ φ
    s_alimi = lb.ref(
        "s_alimi",
        "∀ x ∀ x ¬ φ → ∀ x ¬ φ",
        s_spw,
        ref="alimi",
        note="alimi",
    )
    # impbii: ∀ x ¬ φ ↔ ∀ x ∀ x ¬ φ
    s_impbii = lb.ref(
        "s_impbii",
        "∀ x ¬ φ ↔ ∀ x ∀ x ¬ φ",
        s_hba1w,
        s_alimi,
        ref="impbii",
        note="impbii",
    )
    # notbii: ¬ ∀ x ¬ φ ↔ ¬ ∀ x ∀ x ¬ φ
    s_notbii = lb.ref(
        "s_notbii",
        "¬ ∀ x ¬ φ ↔ ¬ ∀ x ∀ x ¬ φ",
        s_impbii,
        ref="notbii",
        note="notbii",
    )
    # df-ex: ∃ x φ ↔ ¬ ∀ x ¬ φ
    s_dfex = lb.ref(
        "s_dfex",
        "∃ x φ ↔ ¬ ∀ x ¬ φ",
        ref="df-ex",
        note="df-ex",
    )
    # 2exnaln: ∃ x ∃ x φ ↔ ¬ ∀ x ∀ x ¬ φ
    s_2exnaln = lb.ref(
        "s_2exnaln",
        "∃ x ∃ x φ ↔ ¬ ∀ x ∀ x ¬ φ",
        ref="2exnaln",
        note="2exnaln",
    )
    # 3bitr4i: ∃ x φ ↔ ∃ x ∃ x φ
    res = lb.ref(
        "res",
        "∃ x φ ↔ ∃ x ∃ x φ",
        s_notbii,
        s_dfex,
        s_2exnaln,
        ref="3bitr4i",
        note="3bitr4i",
    )
    return lb.build(res)


def prove_excom13(sys: System) -> Proof:
    """excom13: ∃ x ∃ y ∃ z φ ↔ ∃ z ∃ y ∃ x φ.
    Commutation of the outermost and innermost existential quantifiers.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "excom13")
    # excom: ∃ y ∃ z φ ↔ ∃ z ∃ y φ
    s1 = lb.ref(
        "s1",
        "∃ y ∃ z φ ↔ ∃ z ∃ y φ",
        ref="excom",
        note="excom",
    )
    # exbii: ∃ x ∃ y ∃ z φ ↔ ∃ x ∃ z ∃ y φ
    s2 = lb.ref(
        "s2",
        "∃ x ∃ y ∃ z φ ↔ ∃ x ∃ z ∃ y φ",
        s1,
        ref="exbii",
        note="exbii excom",
    )
    # excom (x, z): ∃ x ∃ z ∃ y φ ↔ ∃ z ∃ x ∃ y φ
    s3 = lb.ref(
        "s3",
        "∃ x ∃ z ∃ y φ ↔ ∃ z ∃ x ∃ y φ",
        ref="excom",
        note="excom",
    )
    # excom: ∃ x ∃ y φ ↔ ∃ y ∃ x φ
    s4 = lb.ref(
        "s4",
        "∃ x ∃ y φ ↔ ∃ y ∃ x φ",
        ref="excom",
        note="excom",
    )
    # exbii (z prefix): ∃ z ∃ x ∃ y φ ↔ ∃ z ∃ y ∃ x φ
    s5 = lb.ref(
        "s5",
        "∃ z ∃ x ∃ y φ ↔ ∃ z ∃ y ∃ x φ",
        s4,
        ref="exbii",
        note="exbii excom",
    )
    # 3bitri: chain s2, s3, s5
    res = lb.ref(
        "res",
        "∃ x ∃ y ∃ z φ ↔ ∃ z ∃ y ∃ x φ",
        s2,
        s3,
        s5,
        ref="3bitri",
        note="3bitri exbii, excom, exbii",
    )
    return lb.build(res)


def prove_axi4(sys: System) -> Proof:
    """axi4: ∀ x φ → φ.
    Universal specialization (same as sp).
    """
    lb = ProofBuilder(sys, "axi4")
    res = lb.ref(
        "res",
        "∀ x φ → φ",
        ref="sp",
        note="sp",
    )
    return lb.build(res)


def prove_2sp(sys: System) -> Proof:
    """2sp: ∀ x ∀ y φ → φ.
    Double specialization: consecutive universal quantifiers can be removed.
    (Contributed by NM, 9-Mar-1997.)
    """
    lb = ProofBuilder(sys, "2sp")
    # sp: ∀ y φ → φ
    s1 = lb.ref(
        "s1",
        "∀ y φ → φ",
        ref="sp",
        note="sp",
    )
    # sps: ( ∀ y φ → φ ) ⊢ ∀ x ∀ y φ → φ
    res = lb.ref(
        "res",
        "∀ x ∀ y φ → φ",
        s1,
        ref="sps",
        note="sps sp",
    )
    return lb.build(res)


def prove_ax6(sys: System) -> Proof:
    """ax6: ¬ ∀ x ¬ x = y.
    There exists a set equal to another, expressed as an alternation
    of quantifiers.  From ax6e and df-ex via mpbi.
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "ax6")
    # ax6e: ∃ x x = y
    s1 = lb.ref(
        "s1",
        "∃ x x = y",
        ref="ax6e",
        note="ax6e",
    )
    # df-ex: ∃ x x = y ↔ ¬ ∀ x ¬ x = y
    s2 = lb.ref(
        "s2",
        "∃ x x = y ↔ ¬ ∀ x ¬ x = y",
        ref="df-ex",
        note="df-ex",
    )
    # mpbi: ax6e (minor), df-ex (major)
    res = lb.ref(
        "res",
        "¬ ∀ x ¬ x = y",
        s1,
        s2,
        ref="mpbi",
        note="mpbi ax6e, df-ex",
    )
    return lb.build(res)


def prove_axi9(sys: System) -> Proof:
    """axi9: ∃ x x = y.
    Existence of a set equal to another.  (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "axi9")
    res = lb.ref("res", "∃ x x = y", ref="ax6e", note="ax6e")
    return lb.build(res)


def prove_19_9d(sys: System) -> Proof:
    """19.9d: ψ → ( ∃ x φ → φ ).
    Deduction form: from ψ → Ⅎ x φ, conclude ψ → ( ∃ x φ → φ ).
    The proof uses nfrd to expand the not-free condition, then sp
    to eliminate the universal quantifier, and syl6 to chain the implications.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "19.9d")
    hyp = lb.hyp("19.9d.1", "ψ → Ⅎ x φ")
    # nfrd: φ → Ⅎ x ψ  ⊢  φ → ( ∃ x ψ → ∀ x ψ )
    s1 = lb.ref(
        "s1",
        "ψ → ( ∃ x φ → ∀ x φ )",
        hyp,
        ref="nfrd",
        note="nfrd",
    )
    # sp: ∀ x φ → φ
    s2 = lb.ref(
        "s2",
        "∀ x φ → φ",
        ref="sp",
        note="sp",
    )
    # syl6: ψ → ( ∃ x φ → φ )
    res = lb.ref(
        "res",
        "ψ → ( ∃ x φ → φ )",
        s1,
        s2,
        ref="syl6",
        note="syl6",
    )
    return lb.build(res)


def prove_19_9h(sys: System) -> Proof:
    """19.9h: ∃ x φ ↔ φ.
    Theorem 19.9 of [Margaris] p. 89.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "19.9h")
    hyp = lb.hyp("19.9h.1", "φ → ∀ x φ")
    # nf5i: from φ → ∀ x φ, derive Ⅎ x φ
    s1 = lb.ref(
        "s1",
        "Ⅎ x φ",
        hyp,
        ref="nf5i",
        note="nf5i",
    )
    # 19.9: Ⅎ x φ → (∃ x φ ↔ φ)
    res = lb.ref(
        "res",
        "∃ x φ ↔ φ",
        s1,
        ref="19.9",
        note="19.9",
    )
    return lb.build(res)


def prove_19_9ht(sys: System) -> Proof:
    """19.9ht: ∀ x ( φ → ∀ x φ ) → ( ∃ x φ → φ ).
    If φ implies its own universal quantification for all x, then
    the existential quantifier can be dropped.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "19.9ht")
    # nf5-1: ∀ x ( φ → ∀ x φ ) → Ⅎ x φ
    s1 = lb.ref(
        "s1",
        "∀ x ( φ → ∀ x φ ) → Ⅎ x φ",
        ref="nf5-1",
        note="nf5-1",
    )
    # 19.9d with ψ := ∀ x ( φ → ∀ x φ )
    # ψ → Ⅎ x φ  (nf5-1)  ⊢  ψ → ( ∃ x φ → φ )
    res = lb.ref(
        "res",
        "∀ x ( φ → ∀ x φ ) → ( ∃ x φ → φ )",
        s1,
        ref="19.9d",
        note="19.9d nf5-1",
    )
    return lb.build(res)


def prove_nf5r(sys: System) -> Proof:
    """nf5r: Ⅎ x φ → ( φ → ∀ x φ ).
    The not-free hypothesis implies universal quantification.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "nf5r")
    # id: Ⅎ x φ → Ⅎ x φ
    s1 = lb.ref(
        "s1",
        "Ⅎ x φ → Ⅎ x φ",
        ref="id",
        note="id",
    )
    # nfrd: Ⅎ x φ → ( ∃ x φ → ∀ x φ )
    s2 = lb.ref(
        "s2",
        "Ⅎ x φ → ( ∃ x φ → ∀ x φ )",
        s1,
        ref="nfrd",
        note="nfrd id",
    )
    # 19.8a: φ → ∃ x φ
    s3 = lb.ref(
        "s3",
        "φ → ∃ x φ",
        ref="19.8a",
        note="19.8a",
    )
    # syl5: Ⅎ x φ → ( φ → ∀ x φ )
    res = lb.ref(
        "res",
        "Ⅎ x φ → ( φ → ∀ x φ )",
        s3,
        s2,
        ref="syl5",
        note="syl5 nfrd, 19.8a",
    )
    return lb.build(res)


def prove_nf5rd(sys: System) -> Proof:
    """nf5rd: φ → (ψ → ∀ x ψ).
    Deduction form of nf5r.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "nf5rd")
    hyp = lb.hyp("nf5rd.1", "φ → Ⅎ x ψ")
    s1 = lb.ref(
        "s1",
        "Ⅎ x ψ → (ψ → ∀ x ψ)",
        ref="nf5r",
        note="nf5r",
    )
    res = lb.ref(
        "res",
        "φ → (ψ → ∀ x ψ)",
        hyp,
        s1,
        ref="syl",
        note="syl nf5rd.1, nf5r",
    )
    return lb.build(res)


def prove_nf5ri(sys: System) -> Proof:
    """nf5ri: φ → ∀ x φ.
    Inference form of nf5r: from Ⅎ x φ, conclude φ → ∀ x φ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "nf5ri")
    hyp = lb.hyp("nf5ri.1", "Ⅎ x φ")
    # nfri: ∃ x φ → ∀ x φ
    s1 = lb.ref(
        "s1",
        "∃ x φ → ∀ x φ",
        hyp,
        ref="nfri",
        note="nfri nf5ri.1",
    )
    # 19.23bi: φ → ∀ x φ
    res = lb.ref(
        "res",
        "φ → ∀ x φ",
        s1,
        ref="19.23bi",
        note="19.23bi nfri",
    )
    return lb.build(res)


def prove_nf5di(sys: System) -> Proof:
    """nf5di: Ⅎ x φ.
    Deduction form of nf5i.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "nf5di")
    hyp = lb.hyp("nf5di.1", "φ → Ⅎ x φ")
    # nf5rd: ph → ( ph → ∀ x ph )
    s1 = lb.ref(
        "s1",
        "φ → ( φ → ∀ x φ )",
        hyp,
        ref="nf5rd",
        note="nf5rd",
    )
    # pm2.43i: ph → ∀ x ph
    s2 = lb.ref(
        "s2",
        "φ → ∀ x φ",
        s1,
        ref="pm2.43i",
        note="pm2.43i",
    )
    # nf5i: Ⅎ x ph
    res = lb.ref(
        "res",
        "Ⅎ x φ",
        s2,
        ref="nf5i",
        note="nf5i",
    )
    return lb.build(res)


def prove_dveeq2(sys: System) -> Proof:
    """dveeq2: ¬ ∀ x x = y → ( z = y → ∀ x z = y ).
    A distinctor eliminates the disjoint variable condition on equality,
    given a distinctor between the bound variable and the other setvar.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "dveeq2")
    s_nfeqf2 = lb.ref(
        "s_nfeqf2",
        "¬ ∀ x x = y → Ⅎ x z = y",
        ref="nfeqf2",
        note="nfeqf2",
    )
    res = lb.ref(
        "res",
        "¬ ∀ x x = y → ( z = y → ∀ x z = y )",
        s_nfeqf2,
        ref="nf5rd",
        note="nf5rd nfeqf2",
    )
    return lb.build(res)


def prove_dveeq2ALT(sys: System) -> Proof:
    """dveeq2ALT: ¬ ∀ x x = y → ( z = y → ∀ x z = y ).

    Alternate proof of dveeq2 using dvelimv.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "dveeq2ALT")

    s_eq = lb.ref(
        "s_eq",
        "w = y → ( z = w ↔ z = y )",
        ref="equequ2",
        note="equequ2 with x:=w",
    )

    res = lb.ref(
        "res",
        "¬ ∀ x x = y → ( z = y → ∀ x z = y )",
        s_eq,
        ref="dvelimv",
        note="dvelimv equequ2",
    )

    return lb.build(res)


def prove_dveeq1(sys: System) -> Proof:
    """dveeq1: ¬ ∀ x x = y → ( y = z → ∀ x y = z ).
    A distinctor eliminates the disjoint variable condition on equality,
    with the equality written in the opposite order compared to dveeq2.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "dveeq1")
    s_nfeqf1 = lb.ref(
        "s_nfeqf1",
        "¬ ∀ x x = y → Ⅎ x y = z",
        ref="nfeqf1",
        note="nfeqf1",
    )
    res = lb.ref(
        "res",
        "¬ ∀ x x = y → ( y = z → ∀ x y = z )",
        s_nfeqf1,
        ref="nf5rd",
        note="nf5rd nfeqf1",
    )
    return lb.build(res)


def prove_drsb1(sys: System) -> Proof:
    """drsb1: ∀ x x = y → ( [ z / x ] φ ↔ [ z / y ] φ ).

    Substitution with a distinctor on the substituted variable.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "drsb1")

    # 1. equequ1: x = y → ( x = z ↔ y = z )
    s1 = lb.ref(
        "s1",
        "x = y → ( x = z ↔ y = z )",
        ref="equequ1",
        note="equequ1",
    )

    # 2. sps: ∀ x x = y → ( x = z ↔ y = z )
    s2 = lb.ref(
        "s2",
        "∀ x x = y → ( x = z ↔ y = z )",
        s1,
        ref="sps",
        note="sps equequ1",
    )

    # 3. imbi1d: ∀ x x = y → ( ( x = z → φ ) ↔ ( y = z → φ ) )
    s3 = lb.ref(
        "s3",
        "∀ x x = y → ( ( x = z → φ ) ↔ ( y = z → φ ) )",
        s2,
        ref="imbi1d",
        note="imbi1d sps",
    )

    # 4. anbi1d: ∀ x x = y → ( ( x = z ∧ φ ) ↔ ( y = z ∧ φ ) )
    s4 = lb.ref(
        "s4",
        "∀ x x = y → ( ( x = z ∧ φ ) ↔ ( y = z ∧ φ ) )",
        s2,
        ref="anbi1d",
        note="anbi1d sps",
    )

    # 5. drex1: ∀ x x = y → ( ∃ x ( x = z ∧ φ ) ↔ ∃ y ( y = z ∧ φ ) )
    s5 = lb.ref(
        "s5",
        "∀ x x = y → ( ∃ x ( x = z ∧ φ ) ↔ ∃ y ( y = z ∧ φ ) )",
        s4,
        ref="drex1",
        note="drex1 anbi1d",
    )

    # 6. anbi12d: combine the two equivalences into one over the conjunction
    s6 = lb.ref(
        "s6",
        "∀ x x = y → ( ( ( x = z → φ ) ∧ ∃ x ( x = z ∧ φ ) ) ↔ ( ( y = z → φ ) ∧ ∃ y ( y = z ∧ φ ) ) )",
        s3,
        s5,
        ref="anbi12d",
        note="anbi12d imbi1d, drex1",
    )

    # 7. dfsb1 (x version): [ z / x ] φ ↔ ( ( x = z → φ ) ∧ ∃ x ( x = z ∧ φ ) )
    s7 = lb.ref(
        "s7",
        "[ z x φ ↔ ( ( x = z → φ ) ∧ ∃ x ( x = z ∧ φ ) )",
        ref="dfsb1",
        note="dfsb1",
    )

    # 8. dfsb1 (y version): [ z / y ] φ ↔ ( ( y = z → φ ) ∧ ∃ y ( y = z ∧ φ ) )
    s8 = lb.ref(
        "s8",
        "[ z y φ ↔ ( ( y = z → φ ) ∧ ∃ y ( y = z ∧ φ ) )",
        ref="dfsb1",
        note="dfsb1",
    )

    # 9. 3bitr4g: ∀ x x = y → ( [ z / x ] φ ↔ [ z / y ] φ )
    res = lb.ref(
        "res",
        "∀ x x = y → ( [ z x φ ↔ [ z y φ )",
        s6,
        s7,
        s8,
        ref="3bitr4g",
        note="3bitr4g anbi12d, dfsb1, dfsb1",
    )

    return lb.build(res)


def prove_drsb2(sys: System) -> Proof:
    """drsb2: ∀ x x = y → ( [ x / z ] φ ↔ [ y / z ] φ ).
    Substitution with a distinctor.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "drsb2")
    # sbequ: x = y → ( [ x / z ] φ ↔ [ y / z ] φ )
    s1 = lb.ref(
        "s1",
        "x = y → ( [ x z φ ↔ [ y z φ )",
        ref="sbequ",
        note="sbequ",
    )
    # sps: ( x = y → ( [ x / z ] φ ↔ [ y / z ] φ ) ) ⊢ ∀ x x = y → ( [ x / z ] φ ↔ [ y / z ] φ )
    res = lb.ref(
        "res",
        "∀ x x = y → ( [ x z φ ↔ [ y z φ )",
        s1,
        ref="sps",
        note="sps sbequ",
    )
    return lb.build(res)


def prove_dral1(sys: System) -> Proof:
    """dral1: ∀ x x = y → (∀ x φ ↔ ∀ y ψ).
    Given a hypothesis that ∀x x = y implies φ ↔ ψ, the universal
    quantifiers can be swapped for x and y.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "dral1")
    hyp = lb.hyp("dral1.1", "∀ x x = y → ( φ ↔ ψ )")
    # nfa1: Ⅎ x ∀ x x = y
    s_nfa1 = lb.ref(
        "s_nfa1",
        "Ⅎ x ∀ x x = y",
        ref="nfa1",
        note="nfa1",
    )
    # albid: ∀ x x = y → (∀ x φ ↔ ∀ x ψ)
    s_albid = lb.ref(
        "s_albid",
        "∀ x x = y → (∀ x φ ↔ ∀ x ψ)",
        s_nfa1,
        hyp,
        ref="albid",
        note="albid nfa1, dral1.1",
    )
    # axc11: ∀ x x = y → (∀ x ψ → ∀ y ψ)
    s_axc11 = lb.ref(
        "s_axc11",
        "∀ x x = y → (∀ x ψ → ∀ y ψ)",
        ref="axc11",
        note="axc11",
    )
    # axc11n: ∀ x x = y → ∀ y y = x
    s_axc11n = lb.ref(
        "s_axc11n",
        "∀ x x = y → ∀ y y = x",
        ref="axc11n",
        note="axc11n",
    )
    # axc11 with x,y swapped: ∀ y y = x → (∀ y ψ → ∀ x ψ)
    s_axc11_rev = lb.ref(
        "s_axc11_rev",
        "∀ y y = x → (∀ y ψ → ∀ x ψ)",
        ref="axc11",
        note="axc11 (x,y swapped)",
    )
    # syl: chain axc11n and axc11_rev
    s_syl = lb.ref(
        "s_syl",
        "∀ x x = y → (∀ y ψ → ∀ x ψ)",
        s_axc11n,
        s_axc11_rev,
        ref="syl",
        note="syl axc11n, axc11",
    )
    # impbid: ∀ x x = y → (∀ x ψ ↔ ∀ y ψ)
    s_impbid = lb.ref(
        "s_impbid",
        "∀ x x = y → (∀ x ψ ↔ ∀ y ψ)",
        s_axc11,
        s_syl,
        ref="impbid",
        note="impbid axc11, syl",
    )
    # bitrd: combine the two biconditionals
    res = lb.ref(
        "res",
        "∀ x x = y → (∀ x φ ↔ ∀ y ψ)",
        s_albid,
        s_impbid,
        ref="bitrd",
        note="bitrd albid, impbid",
    )
    return lb.build(res)


def prove_dral1ALT(sys: System) -> Proof:
    """dral1ALT: ∀ x x = y → (∀ x φ ↔ ∀ y ψ).
    Alternative proof of dral1 using dral2, axc11, axc11r, impbid, and
    bitrd.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "dral1ALT")
    hyp = lb.hyp("dral1.1", "∀ x x = y → ( φ ↔ ψ )")
    # dral2 with z=x: ∀ x x = y → (∀ x φ ↔ ∀ x ψ)
    s_dral2 = lb.ref(
        "s_dral2",
        "∀ x x = y → (∀ x φ ↔ ∀ x ψ)",
        hyp,
        ref="dral2",
        note="dral2 dral1.1",
    )
    # axc11 with φ↦ψ: ∀ x x = y → (∀ x ψ → ∀ y ψ)
    s_axc11 = lb.ref(
        "s_axc11",
        "∀ x x = y → (∀ x ψ → ∀ y ψ)",
        ref="axc11",
        note="axc11",
    )
    # axc11r with φ↦ψ, x↔y: ∀ x x = y → (∀ y ψ → ∀ x ψ)
    s_axc11r = lb.ref(
        "s_axc11r",
        "∀ x x = y → (∀ y ψ → ∀ x ψ)",
        ref="axc11r",
        note="axc11r (x,y swapped)",
    )
    # impbid: ∀ x x = y → (∀ x ψ ↔ ∀ y ψ)
    s_impbid = lb.ref(
        "s_impbid",
        "∀ x x = y → (∀ x ψ ↔ ∀ y ψ)",
        s_axc11,
        s_axc11r,
        ref="impbid",
        note="impbid axc11, axc11r",
    )
    # bitrd: ∀ x x = y → (∀ x φ ↔ ∀ y ψ)
    res = lb.ref(
        "res",
        "∀ x x = y → (∀ x φ ↔ ∀ y ψ)",
        s_dral2,
        s_impbid,
        ref="bitrd",
        note="bitrd dral2, impbid",
    )
    return lb.build(res)


def prove_dral1v(sys: System) -> Proof:
    """dral1v: ∀ x x = y → ( ∀ x φ ↔ ∀ y ψ ).

    Given a hypothesis that ∀x x = y implies φ ↔ ψ, the universal
    quantifiers can be swapped for x and y.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "dral1v")
    hyp = lb.hyp("dral1v.1", "∀ x x = y → ( φ ↔ ψ )")
    # hbaev: ∀ x x = y → ∀ x ∀ x x = y
    s_hbaev = lb.ref(
        "s_hbaev",
        "∀ x x = y → ∀ x ∀ x x = y",
        ref="hbaev",
        note="hbaev",
    )
    # albidh: ∀ x x = y → ( ∀ x φ ↔ ∀ x ψ )
    s_albidh = lb.ref(
        "s_albidh",
        "∀ x x = y → ( ∀ x φ ↔ ∀ x ψ )",
        s_hbaev,
        hyp,
        ref="albidh",
        note="albidh hbaev, dral1v.1",
    )
    # axc11v: ∀ x x = y → ( ∀ x ψ → ∀ y ψ )
    s_axc11v = lb.ref(
        "s_axc11v",
        "∀ x x = y → ( ∀ x ψ → ∀ y ψ )",
        ref="axc11v",
        note="axc11v",
    )
    # axc11rv: ∀ x x = y → ( ∀ y ψ → ∀ x ψ )
    s_axc11rv = lb.ref(
        "s_axc11rv",
        "∀ x x = y → ( ∀ y ψ → ∀ x ψ )",
        ref="axc11rv",
        note="axc11rv",
    )
    # impbid: ∀ x x = y → ( ∀ x ψ ↔ ∀ y ψ )
    s_impbid = lb.ref(
        "s_impbid",
        "∀ x x = y → ( ∀ x ψ ↔ ∀ y ψ )",
        s_axc11v,
        s_axc11rv,
        ref="impbid",
        note="impbid axc11v, axc11rv",
    )
    # bitrd: ∀ x x = y → ( ∀ x φ ↔ ∀ y ψ )
    res = lb.ref(
        "res",
        "∀ x x = y → ( ∀ x φ ↔ ∀ y ψ )",
        s_albidh,
        s_impbid,
        ref="bitrd",
        note="bitrd albidh, impbid",
    )
    return lb.build(res)


def prove_drex1(sys: System) -> Proof:
    """drex1: ∀ x x = y → ( ∃ x φ ↔ ∃ y ψ ).
    Given that ∀x x = y implies φ ↔ ψ, the existential quantifiers can be
    swapped for x and y.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "drex1")
    hyp = lb.hyp("dral1.1", "∀ x x = y → ( φ ↔ ψ )")
    # notbid: ∀ x x = y → ( ¬ φ ↔ ¬ ψ )
    s_notbid = lb.ref(
        "s_notbid",
        "∀ x x = y → ( ¬ φ ↔ ¬ ψ )",
        hyp,
        ref="notbid",
        note="notbid",
    )
    # dral1: ∀ x x = y → ( ∀ x ¬ φ ↔ ∀ y ¬ ψ )
    s_dral1 = lb.ref(
        "s_dral1",
        "∀ x x = y → ( ∀ x ¬ φ ↔ ∀ y ¬ ψ )",
        s_notbid,
        ref="dral1",
        note="dral1",
    )
    # notbid: ∀ x x = y → ( ¬ ∀ x ¬ φ ↔ ¬ ∀ y ¬ ψ )
    s_notbid2 = lb.ref(
        "s_notbid2",
        "∀ x x = y → ( ¬ ∀ x ¬ φ ↔ ¬ ∀ y ¬ ψ )",
        s_dral1,
        ref="notbid",
        note="notbid",
    )
    # df-ex: ∃ x φ ↔ ¬ ∀ x ¬ φ
    s_dfex_x = lb.ref(
        "s_dfex_x",
        "∃ x φ ↔ ¬ ∀ x ¬ φ",
        ref="df-ex",
        note="df-ex",
    )
    # df-ex: ∃ y ψ ↔ ¬ ∀ y ¬ ψ
    s_dfex_y = lb.ref(
        "s_dfex_y",
        "∃ y ψ ↔ ¬ ∀ y ¬ ψ",
        ref="df-ex",
        note="df-ex",
    )
    # 3bitr4g: ∀ x x = y → ( ∃ x φ ↔ ∃ y ψ )
    res = lb.ref(
        "res",
        "∀ x x = y → ( ∃ x φ ↔ ∃ y ψ )",
        s_notbid2,
        s_dfex_x,
        s_dfex_y,
        ref="3bitr4g",
        note="3bitr4g notbid, df-ex, df-ex",
    )
    return lb.build(res)


def prove_drex1v(sys: System) -> Proof:
    """drex1v: ∀ x x = y → ( ∃ x φ ↔ ∃ y ψ ).

    Given that ∀x x = y implies φ ↔ ψ, the existential quantifiers can be
    swapped for x and y when the hypothesis is dral1v.1.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "drex1v")
    hyp = lb.hyp("dral1v.1", "∀ x x = y → ( φ ↔ ψ )")
    # notbid: ∀ x x = y → ( ¬ φ ↔ ¬ ψ )
    s_notbid = lb.ref(
        "s_notbid",
        "∀ x x = y → ( ¬ φ ↔ ¬ ψ )",
        hyp,
        ref="notbid",
        note="notbid",
    )
    # dral1v: ∀ x x = y → ( ∀ x ¬ φ ↔ ∀ y ¬ ψ )
    s_dral1v = lb.ref(
        "s_dral1v",
        "∀ x x = y → ( ∀ x ¬ φ ↔ ∀ y ¬ ψ )",
        s_notbid,
        ref="dral1v",
        note="dral1v",
    )
    # notbid: ∀ x x = y → ( ¬ ∀ x ¬ φ ↔ ¬ ∀ y ¬ ψ )
    s_notbid2 = lb.ref(
        "s_notbid2",
        "∀ x x = y → ( ¬ ∀ x ¬ φ ↔ ¬ ∀ y ¬ ψ )",
        s_dral1v,
        ref="notbid",
        note="notbid",
    )
    # df-ex: ∃ x φ ↔ ¬ ∀ x ¬ φ
    s_dfex_x = lb.ref(
        "s_dfex_x",
        "∃ x φ ↔ ¬ ∀ x ¬ φ",
        ref="df-ex",
        note="df-ex",
    )
    # df-ex: ∃ y ψ ↔ ¬ ∀ y ¬ ψ
    s_dfex_y = lb.ref(
        "s_dfex_y",
        "∃ y ψ ↔ ¬ ∀ y ¬ ψ",
        ref="df-ex",
        note="df-ex",
    )
    # 3bitr4g: ∀ x x = y → ( ∃ x φ ↔ ∃ y ψ )
    res = lb.ref(
        "res",
        "∀ x x = y → ( ∃ x φ ↔ ∃ y ψ )",
        s_notbid2,
        s_dfex_x,
        s_dfex_y,
        ref="3bitr4g",
        note="3bitr4g notbid, df-ex, df-ex",
    )
    return lb.build(res)


def prove_drex2(sys: System) -> Proof:
    """drex2: ∀ x x = y → ( ∃ z φ ↔ ∃ z ψ ).
    Given that ∀x x = y implies φ ↔ ψ, the existential quantifier
    can be pushed through when the bound variable z is the same on
    both sides.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "drex2")
    hyp = lb.hyp("dral1.1", "∀ x x = y → ( φ ↔ ψ )")
    # nfae: Ⅎ z ∀ x x = y
    s_nfae = lb.ref(
        "s_nfae",
        "Ⅎ z ∀ x x = y",
        ref="nfae",
        note="nfae",
    )
    # exbid: Ⅎ z ∀ x x = y, ∀ x x = y → ( φ ↔ ψ ) ⊢ ∀ x x = y → ( ∃ z φ ↔ ∃ z ψ )
    res = lb.ref(
        "res",
        "∀ x x = y → ( ∃ z φ ↔ ∃ z ψ )",
        s_nfae,
        hyp,
        ref="exbid",
        note="exbid nfae, dral1.1",
    )
    return lb.build(res)


def prove_drnf1(sys: System) -> Proof:
    """drnf1: ∀ x x = y → ( Ⅎ x φ ↔ Ⅎ y ψ ).
    Given that ∀x x = y implies φ ↔ ψ, the "not free" property can
    be transferred from x to y.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "drnf1")
    hyp = lb.hyp("dral1.1", "∀ x x = y → ( φ ↔ ψ )")
    # dral1: ∀ x x = y → ( ∀ x φ ↔ ∀ y ψ )
    s_dral1 = lb.ref(
        "s_dral1",
        "∀ x x = y → ( ∀ x φ ↔ ∀ y ψ )",
        hyp,
        ref="dral1",
        note="dral1",
    )
    # imbi12d: ∀ x x = y → ( ( φ → ∀ x φ ) ↔ ( ψ → ∀ y ψ ) )
    s_imbi12d = lb.ref(
        "s_imbi12d",
        "∀ x x = y → ( ( φ → ∀ x φ ) ↔ ( ψ → ∀ y ψ ) )",
        hyp,
        s_dral1,
        ref="imbi12d",
        note="imbi12d dral1.1, dral1",
    )
    # dral1: ∀ x x = y → ( ∀ x ( φ → ∀ x φ ) ↔ ∀ y ( ψ → ∀ y ψ ) )
    s_dral1_2 = lb.ref(
        "s_dral1_2",
        "∀ x x = y → ( ∀ x ( φ → ∀ x φ ) ↔ ∀ y ( ψ → ∀ y ψ ) )",
        s_imbi12d,
        ref="dral1",
        note="dral1 imbi12d",
    )
    # nf5: Ⅎ x φ ↔ ∀ x ( φ → ∀ x φ )
    s_nf5_x = lb.ref(
        "s_nf5_x",
        "Ⅎ x φ ↔ ∀ x ( φ → ∀ x φ )",
        ref="nf5",
        note="nf5",
    )
    # nf5: Ⅎ y ψ ↔ ∀ y ( ψ → ∀ y ψ )
    s_nf5_y = lb.ref(
        "s_nf5_y",
        "Ⅎ y ψ ↔ ∀ y ( ψ → ∀ y ψ )",
        ref="nf5",
        note="nf5",
    )
    # 3bitr4g: ∀ x x = y → ( Ⅎ x φ ↔ Ⅎ y ψ )
    res = lb.ref(
        "res",
        "∀ x x = y → ( Ⅎ x φ ↔ Ⅎ y ψ )",
        s_dral1_2,
        s_nf5_x,
        s_nf5_y,
        ref="3bitr4g",
        note="3bitr4g dral1, nf5, nf5",
    )
    return lb.build(res)


def prove_drnf2(sys: System) -> Proof:
    """drnf2: ∀ x x = y → ( Ⅎ z φ ↔ Ⅎ z ψ ).
    "Not free" predicate version of dral2: given that ∀x x = y implies φ ↔ ψ,
    the "not free in z" property of φ and ψ are equivalent.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "drnf2")
    # dral1.1: ∀ x x = y → ( φ ↔ ψ )
    hyp = lb.hyp("dral1.1", "∀ x x = y → ( φ ↔ ψ )")
    # nfae: Ⅎ z ∀ x x = y
    s_nfae = lb.ref(
        "s_nfae",
        "Ⅎ z ∀ x x = y",
        ref="nfae",
        note="nfae",
    )
    # nfbidf nfae, dral1.1: ∀ x x = y → ( Ⅎ z φ ↔ Ⅎ z ψ )
    res = lb.ref(
        "res",
        "∀ x x = y → ( Ⅎ z φ ↔ Ⅎ z ψ )",
        s_nfae,
        hyp,
        ref="nfbidf",
        note="nfbidf nfae, dral1.1",
    )
    return lb.build(res)


def prove_drnf1v(sys: System) -> Proof:
    """drnf1v: ∀ x x = y → ( Ⅎ x φ ↔ Ⅎ y ψ ).

    Given that ∀x x = y implies φ ↔ ψ, the "not free" property can
    be transferred from x to y. Uses df-nf, drex1v, dral1v, imbi12d,
    and 3bitr4g.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "drnf1v")
    hyp = lb.hyp("dral1v.1", "∀ x x = y → ( φ ↔ ψ )")
    # drex1v: ∀ x x = y → ( ∃ x φ ↔ ∃ y ψ )
    s_drex1v = lb.ref(
        "s_drex1v",
        "∀ x x = y → ( ∃ x φ ↔ ∃ y ψ )",
        hyp,
        ref="drex1v",
        note="drex1v",
    )
    # dral1v: ∀ x x = y → ( ∀ x φ ↔ ∀ y ψ )
    s_dral1v = lb.ref(
        "s_dral1v",
        "∀ x x = y → ( ∀ x φ ↔ ∀ y ψ )",
        hyp,
        ref="dral1v",
        note="dral1v",
    )
    # imbi12d: ∀ x x = y → ( ( ∃ x φ → ∀ x φ ) ↔ ( ∃ y ψ → ∀ y ψ ) )
    s_imbi12d = lb.ref(
        "s_imbi12d",
        "∀ x x = y → ( ( ∃ x φ → ∀ x φ ) ↔ ( ∃ y ψ → ∀ y ψ ) )",
        s_drex1v,
        s_dral1v,
        ref="imbi12d",
        note="imbi12d drex1v, dral1v",
    )
    # df-nf: Ⅎ x φ ↔ ( ∃ x φ → ∀ x φ )
    s_df_nf_x = lb.ref(
        "s_df_nf_x",
        "Ⅎ x φ ↔ ( ∃ x φ → ∀ x φ )",
        ref="df-nf",
        note="df-nf",
    )
    # df-nf: Ⅎ y ψ ↔ ( ∃ y ψ → ∀ y ψ )
    s_df_nf_y = lb.ref(
        "s_df_nf_y",
        "Ⅎ y ψ ↔ ( ∃ y ψ → ∀ y ψ )",
        ref="df-nf",
        note="df-nf",
    )
    # 3bitr4g: ∀ x x = y → ( Ⅎ x φ ↔ Ⅎ y ψ )
    res = lb.ref(
        "res",
        "∀ x x = y → ( Ⅎ x φ ↔ Ⅎ y ψ )",
        s_imbi12d,
        s_df_nf_x,
        s_df_nf_y,
        ref="3bitr4g",
        note="3bitr4g imbi12d, df-nf, df-nf",
    )
    return lb.build(res)


def prove_dral2(sys: System) -> Proof:
    """dral2: ∀ x x = y → ( ∀ z φ ↔ ∀ z ψ ).
    Quantifier manipulation when two setvars are identified by a universal
    equality.  Uses nfae to obtain the not-free condition and albid to
    distribute the universal quantifier over the biconditional.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "dral2")
    hyp = lb.hyp("dral1.1", "∀ x x = y → ( φ ↔ ψ )")
    # nfae: Ⅎ z ∀ x x = y
    s_nfae = lb.ref(
        "s_nfae",
        "Ⅎ z ∀ x x = y",
        ref="nfae",
        note="nfae",
    )
    # albid: Ⅎ z (∀ x x = y), (∀ x x = y → (φ ↔ ψ))
    #        ⊢ ∀ x x = y → (∀ z φ ↔ ∀ z ψ)
    res = lb.ref(
        "res",
        "∀ x x = y → ( ∀ z φ ↔ ∀ z ψ )",
        s_nfae,
        hyp,
        ref="albid",
        note="albid nfae, dral1.1",
    )
    return lb.build(res)


def prove_nfeqf(sys: System) -> Proof:
    """nfeqf: ( ¬ ∀ z z = x ∧ ¬ ∀ z z = y ) → Ⅎ z x = y.
    If neither x nor y is universally equal to z,
    then x = y is not free in z.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "nfeqf")
    # nfna1: Ⅎ z ¬ ∀ z z = x
    s_nfna1x = lb.ref(
        "s_nfna1x",
        "Ⅎ z ¬ ∀ z z = x",
        ref="nfna1",
        note="nfna1",
    )
    # nfna1: Ⅎ z ¬ ∀ z z = y
    s_nfna1y = lb.ref(
        "s_nfna1y",
        "Ⅎ z ¬ ∀ z z = y",
        ref="nfna1",
        note="nfna1",
    )
    # nfan s_nfna1x, s_nfna1y: Ⅎ z ( ¬ ∀ z z = x ∧ ¬ ∀ z z = y )
    s_nfan = lb.ref(
        "s_nfan",
        "Ⅎ z ( ¬ ∀ z z = x ∧ ¬ ∀ z z = y )",
        s_nfna1x,
        s_nfna1y,
        ref="nfan",
        note="nfan nfna1",
    )
    # equvinva: x = y → ∃ w ( x = w ∧ y = w )
    s_equvinva = lb.ref(
        "s_equvinva",
        "x = y → ∃ w ( x = w ∧ y = w )",
        ref="equvinva",
        note="equvinva",
    )
    # dveeq1 (z, x, w): ¬ ∀ z z = x → ( x = w → ∀ z x = w )
    s_dveeq1x = lb.ref(
        "s_dveeq1x",
        "¬ ∀ z z = x → ( x = w → ∀ z x = w )",
        ref="dveeq1",
        note="dveeq1",
    )
    # imp s_dveeq1x: ( ¬ ∀ z z = x ∧ x = w ) → ∀ z x = w
    s_impx = lb.ref(
        "s_impx",
        "( ¬ ∀ z z = x ∧ x = w ) → ∀ z x = w",
        s_dveeq1x,
        ref="imp",
        note="imp dveeq1",
    )
    # dveeq1 (z, y, w): ¬ ∀ z z = y → ( y = w → ∀ z y = w )
    s_dveeq1y = lb.ref(
        "s_dveeq1y",
        "¬ ∀ z z = y → ( y = w → ∀ z y = w )",
        ref="dveeq1",
        note="dveeq1",
    )
    # imp s_dveeq1y: ( ¬ ∀ z z = y ∧ y = w ) → ∀ z y = w
    s_impy = lb.ref(
        "s_impy",
        "( ¬ ∀ z z = y ∧ y = w ) → ∀ z y = w",
        s_dveeq1y,
        ref="imp",
        note="imp dveeq1",
    )
    # equtr2: ( x = w ∧ y = w ) → x = y
    s_equtr2 = lb.ref(
        "s_equtr2",
        "( x = w ∧ y = w ) → x = y",
        ref="equtr2",
        note="equtr2",
    )
    # alanimi s_equtr2: ( ( ∀ z x = w ∧ ∀ z y = w ) → ∀ z x = y )
    s_alanimi = lb.ref(
        "s_alanimi",
        "( ( ∀ z x = w ∧ ∀ z y = w ) → ∀ z x = y )",
        s_equtr2,
        ref="alanimi",
        note="alanimi equtr2",
    )
    # syl2an s_impx, s_impy, s_alanimi:
    # ( ( ¬ ∀ z z = x ∧ x = w ) ∧ ( ¬ ∀ z z = y ∧ y = w ) ) → ∀ z x = y
    s_syl2an = lb.ref(
        "s_syl2an",
        "( ( ¬ ∀ z z = x ∧ x = w ) ∧ ( ¬ ∀ z z = y ∧ y = w ) ) → ∀ z x = y",
        s_impx,
        s_impy,
        s_alanimi,
        ref="syl2an",
        note="syl2an imp, imp, alanimi",
    )
    # an4s s_syl2an:
    # ( ( ( ¬ ∀ z z = x ∧ ¬ ∀ z z = y ) ∧ ( x = w ∧ y = w ) ) → ∀ z x = y )
    s_an4s = lb.ref(
        "s_an4s",
        "( ( ( ¬ ∀ z z = x ∧ ¬ ∀ z z = y ) ∧ ( x = w ∧ y = w ) ) → ∀ z x = y )",
        s_syl2an,
        ref="an4s",
        note="an4s syl2an",
    )
    # ex s_an4s:
    # ( ¬ ∀ z z = x ∧ ¬ ∀ z z = y ) → ( ( x = w ∧ y = w ) → ∀ z x = y )
    s_ex = lb.ref(
        "s_ex",
        "( ¬ ∀ z z = x ∧ ¬ ∀ z z = y ) → ( ( x = w ∧ y = w ) → ∀ z x = y )",
        s_an4s,
        ref="ex",
        note="ex an4s",
    )
    # exlimdv s_ex:
    # ( ¬ ∀ z z = x ∧ ¬ ∀ z z = y ) → ( ∃ w ( x = w ∧ y = w ) → ∀ z x = y )
    s_exlimdv = lb.ref(
        "s_exlimdv",
        "( ¬ ∀ z z = x ∧ ¬ ∀ z z = y ) → ( ∃ w ( x = w ∧ y = w ) → ∀ z x = y )",
        s_ex,
        ref="exlimdv",
        note="exlimdv ex",
    )
    # syl5 s_equvinva, s_exlimdv:
    # ( ¬ ∀ z z = x ∧ ¬ ∀ z z = y ) → ( x = y → ∀ z x = y )
    s_syl5 = lb.ref(
        "s_syl5",
        "( ¬ ∀ z z = x ∧ ¬ ∀ z z = y ) → ( x = y → ∀ z x = y )",
        s_equvinva,
        s_exlimdv,
        ref="syl5",
        note="syl5 equvinva, exlimdv",
    )
    # nf5d s_nfan, s_syl5: ( ¬ ∀ z z = x ∧ ¬ ∀ z z = y ) → Ⅎ z x = y
    res = lb.ref(
        "res",
        "( ¬ ∀ z z = x ∧ ¬ ∀ z z = y ) → Ⅎ z x = y",
        s_nfan,
        s_syl5,
        ref="nf5d",
        note="nf5d nfan, syl5",
    )
    return lb.build(res)


def prove_nfeqf1(sys: System) -> Proof:
    """nfeqf1: ¬ ∀ x x = y → Ⅎ x y = z.
    If there is a distinctor between two set variables x and y,
    then an equation between y and a third set variable z is not free in x.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "nfeqf1")
    # nfeqf2: ¬ ∀ x x = y → Ⅎ x z = y
    s1 = lb.ref(
        "s1",
        "¬ ∀ x x = y → Ⅎ x z = y",
        ref="nfeqf2",
        note="nfeqf2",
    )
    # equcom: z = y ↔ y = z
    s2 = lb.ref(
        "s2",
        "z = y ↔ y = z",
        ref="equcom",
        note="equcom",
    )
    # nfbii: Ⅎ x z = y ↔ Ⅎ x y = z
    s3 = lb.ref(
        "s3",
        "Ⅎ x z = y ↔ Ⅎ x y = z",
        s2,
        ref="nfbii",
        note="nfbii equcom",
    )
    # sylib: ¬ ∀ x x = y → Ⅎ x y = z
    res = lb.ref(
        "res",
        "¬ ∀ x x = y → Ⅎ x y = z",
        s1,
        s3,
        ref="sylib",
        note="sylib nfeqf2, nfbii",
    )
    return lb.build(res)


def prove_nfal(sys: System) -> Proof:
    """nfal: Ⅎ x ∀ y φ.
    If φ is not free in x, then ∀ y φ is also not free in x.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "nfal")
    hyp = lb.hyp("nfal.1", "Ⅎ x φ")
    # nf5ri nfal.1: φ → ∀ x φ
    s1 = lb.ref(
        "s1",
        "φ → ∀ x φ",
        hyp,
        ref="nf5ri",
        note="nf5ri nfal.1",
    )
    # hbal s1: ∀ y φ → ∀ x ∀ y φ
    s2 = lb.ref(
        "s2",
        "∀ y φ → ∀ x ∀ y φ",
        s1,
        ref="hbal",
        note="hbal nf5ri",
    )
    # nf5i s2: Ⅎ x ∀ y φ
    res = lb.ref(
        "res",
        "Ⅎ x ∀ y φ",
        s2,
        ref="nf5i",
        note="nf5i hbal",
    )
    return lb.build(res)


def prove_nfex(sys: System) -> Proof:
    """nfex: Ⅎ x ∃ y φ.
    If φ is not free in x, then ∃ y φ is also not free in x.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "nfex")
    hyp = lb.hyp("nfex.1", "Ⅎ x φ")
    # df-ex: ∃ y φ ↔ ¬ ∀ y ¬ φ
    s1 = lb.ref(
        "s1",
        "∃ y φ ↔ ¬ ∀ y ¬ φ",
        ref="df-ex",
        note="df-ex",
    )
    # nfn nfex.1: Ⅎ x ¬ φ
    s2 = lb.ref(
        "s2",
        "Ⅎ x ¬ φ",
        hyp,
        ref="nfn",
        note="nfn nfex.1",
    )
    # nfal s2: Ⅎ x ∀ y ¬ φ
    s3 = lb.ref(
        "s3",
        "Ⅎ x ∀ y ¬ φ",
        s2,
        ref="nfal",
        note="nfal nfn",
    )
    # nfn s3: Ⅎ x ¬ ∀ y ¬ φ
    s4 = lb.ref(
        "s4",
        "Ⅎ x ¬ ∀ y ¬ φ",
        s3,
        ref="nfn",
        note="nfn nfal",
    )
    # nfxfr s1, s4: Ⅎ x ∃ y φ
    res = lb.ref(
        "res",
        "Ⅎ x ∃ y φ",
        s1,
        s4,
        ref="nfxfr",
        note="nfxfr df-ex, nfn",
    )
    return lb.build(res)


def prove_nfald(sys: System) -> Proof:
    """nfald: φ → Ⅎ x ∀ y ψ.
    Deduction form of nfal.  From Ⅎ y φ and φ → Ⅎ x ψ,
    conclude φ → Ⅎ x ∀ y ψ.
    (Contributed by Mario Carneiro, 24-Sep-2016.)
    (Proof shortened by Wolf Lammen, 16-Oct-2021.)
    """
    lb = ProofBuilder(sys, "nfald")
    h1 = lb.hyp("nfald.1", "Ⅎ y φ")
    h2 = lb.hyp("nfald.2", "φ → Ⅎ x ψ")
    # nfrd nfald.2: φ → (∃ x ψ → ∀ x ψ)
    s1 = lb.ref(
        "s1",
        "φ → ( ∃ x ψ → ∀ x ψ )",
        h2,
        ref="nfrd",
        note="nfrd nfald.2",
    )
    # alimd nfald.1, s1: φ → (∀ y ∃ x ψ → ∀ y ∀ x ψ)
    s2 = lb.ref(
        "s2",
        "φ → ( ∀ y ∃ x ψ → ∀ y ∀ x ψ )",
        h1,
        s1,
        ref="alimd",
        note="alimd nfald.1, nfrd",
    )
    # 19.12: ∃ x ∀ y ψ → ∀ y ∃ x ψ
    s3 = lb.ref(
        "s3",
        "∃ x ∀ y ψ → ∀ y ∃ x ψ",
        ref="19.12",
        note="19.12",
    )
    # ax-11: ∀ y ∀ x ψ → ∀ x ∀ y ψ
    s4 = lb.ref(
        "s4",
        "∀ y ∀ x ψ → ∀ x ∀ y ψ",
        ref="ax-11",
        note="ax-11",
    )
    # syl56 s3, s2, s4: φ → (∃ x ∀ y ψ → ∀ x ∀ y ψ)
    s5 = lb.ref(
        "s5",
        "φ → ( ∃ x ∀ y ψ → ∀ x ∀ y ψ )",
        s3,
        s2,
        s4,
        ref="syl56",
        note="syl56 19.12, alimd, ax-11",
    )
    # nfd s5: φ → Ⅎ x ∀ y ψ
    res = lb.ref(
        "res",
        "φ → Ⅎ x ∀ y ψ",
        s5,
        ref="nfd",
        note="nfd",
    )
    return lb.build(res)


def prove_nfald2(sys: System) -> Proof:
    """nfald2: φ → Ⅎ x ∀ y ψ.
    Variation on nfald which adds the hypothesis that x and y are
    distinct in the inner subproof.
    (Contributed by Mario Carneiro, 8-Oct-2016.)
    """
    lb = ProofBuilder(sys, "nfald2")
    h1 = lb.hyp("nfald2.1", "Ⅎ y φ")
    h2 = lb.hyp("nfald2.2", "( φ ∧ ¬ ∀ x x = y ) → Ⅎ x ψ")
    # nfnae: Ⅎ y ¬ ∀ x x = y
    s_nfnae = lb.ref(
        "s_nfnae",
        "Ⅎ y ¬ ∀ x x = y",
        ref="nfnae",
        note="nfnae",
    )
    # nfan nfald2.1, nfnae: Ⅎ y ( φ ∧ ¬ ∀ x x = y )
    s_nfan = lb.ref(
        "s_nfan",
        "Ⅎ y ( φ ∧ ¬ ∀ x x = y )",
        h1,
        s_nfnae,
        ref="nfan",
        note="nfan nfald2.1, nfnae",
    )
    # nfald nfan, nfald2.2: ( φ ∧ ¬ ∀ x x = y ) → Ⅎ x ∀ y ψ
    s_nfald = lb.ref(
        "s_nfald",
        "( φ ∧ ¬ ∀ x x = y ) → Ⅎ x ∀ y ψ",
        s_nfan,
        h2,
        ref="nfald",
        note="nfald nfan, nfald2.2",
    )
    # ex nfald: φ → ( ¬ ∀ x x = y → Ⅎ x ∀ y ψ )
    s_ex = lb.ref(
        "s_ex",
        "φ → ( ¬ ∀ x x = y → Ⅎ x ∀ y ψ )",
        s_nfald,
        ref="ex",
        note="ex nfald",
    )
    # nfa1: Ⅎ y ∀ y ψ
    s_nfa1 = lb.ref(
        "s_nfa1",
        "Ⅎ y ∀ y ψ",
        ref="nfa1",
        note="nfa1",
    )
    # biidd: ∀ x x = y → ( ∀ y ψ ↔ ∀ y ψ )
    s_biidd = lb.ref(
        "s_biidd",
        "∀ x x = y → ( ∀ y ψ ↔ ∀ y ψ )",
        ref="biidd",
        note="biidd",
    )
    # drnf1 biidd: ∀ x x = y → ( Ⅎ x ∀ y ψ ↔ Ⅎ y ∀ y ψ )
    s_drnf1 = lb.ref(
        "s_drnf1",
        "∀ x x = y → ( Ⅎ x ∀ y ψ ↔ Ⅎ y ∀ y ψ )",
        s_biidd,
        ref="drnf1",
        note="drnf1 biidd",
    )
    # mpbiri nfa1, drnf1: ∀ x x = y → Ⅎ x ∀ y ψ
    s_mpbiri = lb.ref(
        "s_mpbiri",
        "∀ x x = y → Ⅎ x ∀ y ψ",
        s_nfa1,
        s_drnf1,
        ref="mpbiri",
        note="mpbiri nfa1, drnf1",
    )
    # pm2.61d2 ex, mpbiri: φ → Ⅎ x ∀ y ψ
    res = lb.ref(
        "res",
        "φ → Ⅎ x ∀ y ψ",
        s_ex,
        s_mpbiri,
        ref="pm2.61d2",
        note="pm2.61d2 ex, mpbiri",
    )
    return lb.build(res)


def prove_nfexd(sys: System) -> Proof:
    """nfexd: φ → Ⅎ x ∃ y ψ.
    Deduction form of nfex.  From Ⅎ y φ and φ → Ⅎ x ψ,
    conclude φ → Ⅎ x ∃ y ψ.
    (Contributed by Mario Carneiro, 24-Sep-2016.)
    """
    lb = ProofBuilder(sys, "nfexd")
    h1 = lb.hyp("nfald.1", "Ⅎ y φ")
    h2 = lb.hyp("nfald.2", "φ → Ⅎ x ψ")
    # df-ex: ∃ y ψ ↔ ¬ ∀ y ¬ ψ
    s1 = lb.ref(
        "s1",
        "∃ y ψ ↔ ¬ ∀ y ¬ ψ",
        ref="df-ex",
        note="df-ex",
    )
    # nfnd nfald.2: φ → Ⅎ x ¬ ψ
    s2 = lb.ref(
        "s2",
        "φ → Ⅎ x ¬ ψ",
        h2,
        ref="nfnd",
        note="nfnd nfald.2",
    )
    # nfald nfald.1, s2: φ → Ⅎ x ∀ y ¬ ψ
    s3 = lb.ref(
        "s3",
        "φ → Ⅎ x ∀ y ¬ ψ",
        h1,
        s2,
        ref="nfald",
        note="nfald nfald.1, nfnd",
    )
    # nfnd s3: φ → Ⅎ x ¬ ∀ y ¬ ψ
    s4 = lb.ref(
        "s4",
        "φ → Ⅎ x ¬ ∀ y ¬ ψ",
        s3,
        ref="nfnd",
        note="nfnd nfald",
    )
    # nfxfrd df-ex, s4: φ → Ⅎ x ∃ y ψ
    res = lb.ref(
        "res",
        "φ → Ⅎ x ∃ y ψ",
        s1,
        s4,
        ref="nfxfrd",
        note="nfxfrd df-ex, nfnd",
    )
    return lb.build(res)


def prove_nfexd2(sys: System) -> Proof:
    """nfexd2: φ → Ⅎ x ∃ y ψ.
    Variation on nfexd which adds the hypothesis that x and y are
    distinct in the inner subproof.
    (Contributed by Mario Carneiro, 24-Sep-2016.)
    """
    lb = ProofBuilder(sys, "nfexd2")
    h1 = lb.hyp("nfald2.1", "Ⅎ y φ")
    h2 = lb.hyp("nfald2.2", "( φ ∧ ¬ ∀ x x = y ) → Ⅎ x ψ")
    # df-ex: ∃ y ψ ↔ ¬ ∀ y ¬ ψ
    s1 = lb.ref(
        "s1",
        "∃ y ψ ↔ ¬ ∀ y ¬ ψ",
        ref="df-ex",
        note="df-ex",
    )
    # nfnd nfald2.2: ( φ ∧ ¬ ∀ x x = y ) → Ⅎ x ¬ ψ
    s2 = lb.ref(
        "s2",
        "( φ ∧ ¬ ∀ x x = y ) → Ⅎ x ¬ ψ",
        h2,
        ref="nfnd",
        note="nfnd nfald2.2",
    )
    # nfald2 nfald2.1, s2: φ → Ⅎ x ∀ y ¬ ψ
    s3 = lb.ref(
        "s3",
        "φ → Ⅎ x ∀ y ¬ ψ",
        h1,
        s2,
        ref="nfald2",
        note="nfald2 nfald2.1, nfnd",
    )
    # nfnd s3: φ → Ⅎ x ¬ ∀ y ¬ ψ
    s4 = lb.ref(
        "s4",
        "φ → Ⅎ x ¬ ∀ y ¬ ψ",
        s3,
        ref="nfnd",
        note="nfnd nfald2",
    )
    # nfxfrd s1, s4: φ → Ⅎ x ∃ y ψ
    res = lb.ref(
        "res",
        "φ → Ⅎ x ∃ y ψ",
        s1,
        s4,
        ref="nfxfrd",
        note="nfxfrd df-ex, nfnd",
    )
    return lb.build(res)


def prove_nfmod2(sys: System) -> Proof:
    """nfmod2: φ → Ⅎ x ∃* y ψ.
    Deduction version of nfmo.  If φ is not free in y, and x is
    not free in ψ when ¬ ∀ x x = y, then x is not free in
    "there exists at most one y such that ψ" given φ.
    (Contributed by NM, 9-Mar-1995.)
    """
    lb = ProofBuilder(sys, "nfmod2")
    h1 = lb.hyp("nfmod2.1", "Ⅎ y φ")
    h2 = lb.hyp("nfmod2.2", "( φ ∧ ¬ ∀ x x = y ) → Ⅎ x ψ")
    # dfmo: ∃* y ψ ↔ ∃ z ∀ y ( ψ → y = z )
    s_dfmo = lb.ref(
        "s_dfmo",
        "∃* y ψ ↔ ∃ z ∀ y ( ψ → y = z )",
        ref="dfmo",
        note="dfmo",
    )
    # nfeqf1: ¬ ∀ x x = y → Ⅎ x y = z
    s_nfeqf1 = lb.ref(
        "s_nfeqf1",
        "¬ ∀ x x = y → Ⅎ x y = z",
        ref="nfeqf1",
        note="nfeqf1",
    )
    # adantl nfeqf1: ( φ ∧ ¬ ∀ x x = y ) → Ⅎ x y = z
    s_adantl = lb.ref(
        "s_adantl",
        "( φ ∧ ¬ ∀ x x = y ) → Ⅎ x y = z",
        s_nfeqf1,
        ref="adantl",
        note="adantl nfeqf1",
    )
    # nfimd nfmod2.2, adantl: ( φ ∧ ¬ ∀ x x = y ) → Ⅎ x ( ψ → y = z )
    s_nfimd = lb.ref(
        "s_nfimd",
        "( φ ∧ ¬ ∀ x x = y ) → Ⅎ x ( ψ → y = z )",
        h2,
        s_adantl,
        ref="nfimd",
        note="nfimd nfmod2.2, adantl",
    )
    # nfald2 nfmod2.1, nfimd: φ → Ⅎ x ∀ y ( ψ → y = z )
    s_nfald2 = lb.ref(
        "s_nfald2",
        "φ → Ⅎ x ∀ y ( ψ → y = z )",
        h1,
        s_nfimd,
        ref="nfald2",
        note="nfald2 nfmod2.1, nfimd",
    )
    # nfv: Ⅎ z φ
    s_nfv = lb.ref(
        "s_nfv",
        "Ⅎ z φ",
        ref="nfv",
        note="nfv",
    )
    # nfexd nfv, nfald2: φ → Ⅎ x ∃ z ∀ y ( ψ → y = z )
    s_nfexd = lb.ref(
        "s_nfexd",
        "φ → Ⅎ x ∃ z ∀ y ( ψ → y = z )",
        s_nfv,
        s_nfald2,
        ref="nfexd",
        note="nfexd nfv, nfald2",
    )
    # nfxfrd dfmo, nfexd: φ → Ⅎ x ∃* y ψ
    res = lb.ref(
        "res",
        "φ → Ⅎ x ∃* y ψ",
        s_dfmo,
        s_nfexd,
        ref="nfxfrd",
        note="nfxfrd dfmo, nfexd",
    )
    return lb.build(res)


def prove_nfmod(sys: System) -> Proof:
    """nfmod: φ → Ⅎ x ∃* y ψ.
    Deduction form of nfmod2.  If y is not free in φ, and x is
    not free in ψ given φ, then x is not free in "there exists at
    most one y such that ψ" given φ.
    (Contributed by NM, 9-Mar-1995.)
    """
    lb = ProofBuilder(sys, "nfmod")
    h1 = lb.hyp("nfmod.1", "Ⅎ y φ")
    h2 = lb.hyp("nfmod.2", "φ → Ⅎ x ψ")
    # adantr nfmod.2: ( φ ∧ ¬ ∀ x x = y ) → Ⅎ x ψ
    s1 = lb.ref(
        "s1",
        "( φ ∧ ¬ ∀ x x = y ) → Ⅎ x ψ",
        h2,
        ref="adantr",
        note="adantr nfmod.2",
    )
    # nfmod2 nfmod.1, s1: φ → Ⅎ x ∃* y ψ
    res = lb.ref(
        "res",
        "φ → Ⅎ x ∃* y ψ",
        h1,
        s1,
        ref="nfmod2",
        note="nfmod2 nfmod.1, s1",
    )
    return lb.build(res)


def prove_nfmo(sys: System) -> Proof:
    """nfmo: Ⅎ x ∃* y φ.
    Not-free in "there exists at most one".
    (Contributed by NM, 9-Mar-1995.)
    """
    lb = ProofBuilder(sys, "nfmo")
    hyp = lb.hyp("nfmo.1", "Ⅎ x φ")
    # nftru: Ⅎ y ⊤
    s_nftru = lb.ref(
        "s_nftru",
        "Ⅎ y ⊤",
        ref="nftru",
        note="nftru",
    )
    # a1i: ⊤ → Ⅎ x φ
    s_a1i = lb.ref(
        "s_a1i",
        "⊤ → Ⅎ x φ",
        hyp,
        ref="a1i",
        note="a1i nfmo.1",
    )
    # nfmod: ⊤ → Ⅎ x ∃* y φ
    s_nfmod = lb.ref(
        "s_nfmod",
        "⊤ → Ⅎ x ∃* y φ",
        s_nftru,
        s_a1i,
        ref="nfmod",
        note="nfmod nftru, a1i",
    )
    # mptru: Ⅎ x ∃* y φ
    res = lb.ref(
        "res",
        "Ⅎ x ∃* y φ",
        s_nfmod,
        ref="mptru",
        note="mptru nfmod",
    )
    return lb.build(res)


def prove_nfmov(sys: System) -> Proof:
    """nfmov: Ⅎ x ∃* y φ.

    Not-free in "there exists at most one".
    (Contributed by NM, 9-Mar-1995.)
    """
    lb = ProofBuilder(sys, "nfmov")
    hyp = lb.hyp("nfmov.1", "Ⅎ x φ")

    # nftru: Ⅎ y ⊤
    s_nftru = lb.ref(
        "s_nftru",
        "Ⅎ y ⊤",
        ref="nftru",
        note="nftru",
    )

    # a1i nfmov.1: ⊤ → Ⅎ x φ
    s_a1i = lb.ref(
        "s_a1i",
        "⊤ → Ⅎ x φ",
        hyp,
        ref="a1i",
        note="a1i nfmov.1",
    )

    # nfmodv nftru, a1i: ⊤ → Ⅎ x ∃* y φ
    s_nfmodv = lb.ref(
        "s_nfmodv",
        "⊤ → Ⅎ x ∃* y φ",
        s_nftru,
        s_a1i,
        ref="nfmodv",
        note="nfmodv nftru, a1i",
    )

    # mptru: Ⅎ x ∃* y φ
    res = lb.ref(
        "res",
        "Ⅎ x ∃* y φ",
        s_nfmodv,
        ref="mptru",
        note="mptru nfmodv",
    )

    return lb.build(res)


def prove_nfmodv(sys: System) -> Proof:
    """nfmodv: φ → Ⅎ x ∃* y ψ.

    Deduction form of nfmo.  If y is not free in φ, and x is
    not free in ψ given φ, then x is not free in "there exists at
    most one y such that ψ" given φ.
    (Contributed by NM, 9-Mar-1995.)
    """
    lb = ProofBuilder(sys, "nfmodv")
    h1 = lb.hyp("nfmodv.1", "Ⅎ y φ")
    h2 = lb.hyp("nfmodv.2", "φ → Ⅎ x ψ")

    # dfmo: ∃* y ψ ↔ ∃ z ∀ y ( ψ → y = z )
    s_dfmo = lb.ref(
        "s_dfmo",
        "∃* y ψ ↔ ∃ z ∀ y ( ψ → y = z )",
        ref="dfmo",
        note="dfmo",
    )

    # nfvd: φ → Ⅎ x ( y = z )
    s_nfvd = lb.ref(
        "s_nfvd",
        "φ → Ⅎ x y = z",
        ref="nfvd",
        note="nfvd",
    )

    # nfimd nfmodv.2, nfvd: φ → Ⅎ x ( ψ → y = z )
    s_nfimd = lb.ref(
        "s_nfimd",
        "φ → Ⅎ x ( ψ → y = z )",
        h2,
        s_nfvd,
        ref="nfimd",
        note="nfimd nfmodv.2, nfvd",
    )

    # nfald nfmodv.1, nfimd: φ → Ⅎ x ∀ y ( ψ → y = z )
    s_nfald = lb.ref(
        "s_nfald",
        "φ → Ⅎ x ∀ y ( ψ → y = z )",
        h1,
        s_nfimd,
        ref="nfald",
        note="nfald nfmodv.1, nfimd",
    )

    # nfv: Ⅎ z φ
    s_nfv = lb.ref(
        "s_nfv",
        "Ⅎ z φ",
        ref="nfv",
        note="nfv",
    )

    # nfexd nfv, nfald: φ → Ⅎ x ∃ z ∀ y ( ψ → y = z )
    s_nfexd = lb.ref(
        "s_nfexd",
        "φ → Ⅎ x ∃ z ∀ y ( ψ → y = z )",
        s_nfv,
        s_nfald,
        ref="nfexd",
        note="nfexd nfv, nfald",
    )

    # nfxfrd dfmo, nfexd: φ → Ⅎ x ∃* y ψ
    res = lb.ref(
        "res",
        "φ → Ⅎ x ∃* y ψ",
        s_dfmo,
        s_nfexd,
        ref="nfxfrd",
        note="nfxfrd dfmo, nfexd",
    )

    return lb.build(res)


def prove_nfeud2(sys: System) -> Proof:
    """nfeud2: φ → Ⅎ x ∃! y ψ.
    Deduction version of nfeu.  If φ is not free in y, and x is
    not free in ψ when ¬ ∀ x x = y, then x is not free in
    "there exists a unique y such that ψ" given φ.
    (Contributed by NM, 9-Mar-1995.)
    """
    lb = ProofBuilder(sys, "nfeud2")
    h1 = lb.hyp("nfeud2.1", "Ⅎ y φ")
    h2 = lb.hyp("nfeud2.2", "( φ ∧ ¬ ∀ x x = y ) → Ⅎ x ψ")
    # df-eu: ∃! y ψ ↔ ( ∃ y ψ ∧ ∃* y ψ )
    s_dfeu = lb.ref(
        "s_dfeu",
        "∃! y ψ ↔ ( ∃ y ψ ∧ ∃* y ψ )",
        ref="df-eu",
        note="df-eu",
    )
    # nfexd2: φ → Ⅎ x ∃ y ψ
    s_nfex = lb.ref(
        "s_nfex",
        "φ → Ⅎ x ∃ y ψ",
        h1,
        h2,
        ref="nfexd2",
        note="nfexd2 nfeud2.1, nfeud2.2",
    )
    # nfmod2: φ → Ⅎ x ∃* y ψ
    s_nfmo = lb.ref(
        "s_nfmo",
        "φ → Ⅎ x ∃* y ψ",
        h1,
        h2,
        ref="nfmod2",
        note="nfmod2 nfeud2.1, nfeud2.2",
    )
    # nfand: φ → Ⅎ x ( ∃ y ψ ∧ ∃* y ψ )
    s_nfand = lb.ref(
        "s_nfand",
        "φ → Ⅎ x ( ∃ y ψ ∧ ∃* y ψ )",
        s_nfex,
        s_nfmo,
        ref="nfand",
        note="nfand nfexd2, nfmod2",
    )
    # nfxfrd: φ → Ⅎ x ∃! y ψ
    res = lb.ref(
        "res",
        "φ → Ⅎ x ∃! y ψ",
        s_dfeu,
        s_nfand,
        ref="nfxfrd",
        note="nfxfrd df-eu, nfand",
    )
    return lb.build(res)


def prove_nfeud(sys: System) -> Proof:
    """nfeud: φ → Ⅎ x ∃! y ψ.
    Deduction form of nfeu. If φ is not free in y, and φ implies
    x is not free in ψ, then φ implies x is not free in ∃! y ψ.
    (Contributed by NM, 9-Mar-1995.)
    """
    lb = ProofBuilder(sys, "nfeud")
    h1 = lb.hyp("nfeud.1", "Ⅎ y φ")
    h2 = lb.hyp("nfeud.2", "φ → Ⅎ x ψ")
    # adantr nfeud.2: ( φ ∧ ¬ ∀ x x = y ) → Ⅎ x ψ
    s1 = lb.ref(
        "s1",
        "( φ ∧ ¬ ∀ x x = y ) → Ⅎ x ψ",
        h2,
        ref="adantr",
        note="adantr nfeud.2",
    )
    # nfeud2 nfeud.1, s1: φ → Ⅎ x ∃! y ψ
    res = lb.ref(
        "res",
        "φ → Ⅎ x ∃! y ψ",
        h1,
        s1,
        ref="nfeud2",
        note="nfeud2 nfeud.1, s1",
    )
    return lb.build(res)


def prove_nfeu(sys: System) -> Proof:
    """nfeu: Ⅎ x ∃! y φ.
    If φ is not free in x, then ∃! y φ is also not free in x.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "nfeu")
    hyp = lb.hyp("nfeu.1", "Ⅎ x φ")
    # nftru: Ⅎ y ⊤
    s1 = lb.ref(
        "s1",
        "Ⅎ y ⊤",
        ref="nftru",
        note="nftru",
    )
    # a1i: ⊤ → Ⅎ x φ
    s2 = lb.ref(
        "s2",
        "⊤ → Ⅎ x φ",
        hyp,
        ref="a1i",
        note="a1i nfeu.1",
    )
    # nfeud: ⊤ → Ⅎ x ∃! y φ
    s3 = lb.ref(
        "s3",
        "⊤ → Ⅎ x ∃! y φ",
        s1,
        s2,
        ref="nfeud",
        note="nfeud nftru, a1i",
    )
    # mptru: Ⅎ x ∃! y φ
    res = lb.ref(
        "res",
        "Ⅎ x ∃! y φ",
        s3,
        ref="mptru",
        note="mptru nfeud",
    )
    return lb.build(res)


def prove_nfeudw(sys: System) -> Proof:
    """nfeudw: φ → Ⅎ x ∃! y ψ.
    Deduction form of nfeu. If φ is not free in y, and φ implies
    x is not free in ψ, then φ implies x is not free in ∃! y ψ.
    (Contributed by NM, 9-Mar-1995.)
    """
    lb = ProofBuilder(sys, "nfeudw")
    h1 = lb.hyp("nfeudw.1", "Ⅎ y φ")
    h2 = lb.hyp("nfeudw.2", "φ → Ⅎ x ψ")
    # df-eu: ∃! y ψ ↔ ( ∃ y ψ ∧ ∃* y ψ )
    s_dfeu = lb.ref(
        "s_dfeu",
        "∃! y ψ ↔ ( ∃ y ψ ∧ ∃* y ψ )",
        ref="df-eu",
        note="df-eu",
    )
    # nfexd nfeudw.1, nfeudw.2: φ → Ⅎ x ∃ y ψ
    s_nfex = lb.ref(
        "s_nfex",
        "φ → Ⅎ x ∃ y ψ",
        h1,
        h2,
        ref="nfexd",
        note="nfexd nfeudw.1, nfeudw.2",
    )
    # nfmodv nfeudw.1, nfeudw.2: φ → Ⅎ x ∃* y ψ
    s_nfmo = lb.ref(
        "s_nfmo",
        "φ → Ⅎ x ∃* y ψ",
        h1,
        h2,
        ref="nfmodv",
        note="nfmodv nfeudw.1, nfeudw.2",
    )
    # nfand nfexd, nfmodv: φ → Ⅎ x ( ∃ y ψ ∧ ∃* y ψ )
    s_nfand = lb.ref(
        "s_nfand",
        "φ → Ⅎ x ( ∃ y ψ ∧ ∃* y ψ )",
        s_nfex,
        s_nfmo,
        ref="nfand",
        note="nfand nfexd, nfmodv",
    )
    # nfxfrd df-eu, nfand: φ → Ⅎ x ∃! y ψ
    res = lb.ref(
        "res",
        "φ → Ⅎ x ∃! y ψ",
        s_dfeu,
        s_nfand,
        ref="nfxfrd",
        note="nfxfrd df-eu, nfand",
    )
    return lb.build(res)


def prove_nfeuw(sys: System) -> Proof:
    """nfeuw: Ⅎ x ∃! y φ.
    Weak version of nfeu. If φ is not free in x, then ∃! y φ is also
    not free in x.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "nfeuw")
    hyp = lb.hyp("nfeuw.1", "Ⅎ x φ")
    # nftru: Ⅎ y ⊤
    s1 = lb.ref(
        "s1",
        "Ⅎ y ⊤",
        ref="nftru",
        note="nftru",
    )
    # a1i: ⊤ → Ⅎ x φ
    s2 = lb.ref(
        "s2",
        "⊤ → Ⅎ x φ",
        hyp,
        ref="a1i",
        note="a1i nfeuw.1",
    )
    # nfeudw: ⊤ → Ⅎ x ∃! y φ
    s3 = lb.ref(
        "s3",
        "⊤ → Ⅎ x ∃! y φ",
        s1,
        s2,
        ref="nfeudw",
        note="nfeudw nftru, a1i",
    )
    # mptru: Ⅎ x ∃! y φ
    res = lb.ref(
        "res",
        "Ⅎ x ∃! y φ",
        s3,
        ref="mptru",
        note="mptru nfeudw",
    )
    return lb.build(res)


def prove_hbex(sys: System) -> Proof:
    """hbex: ∃ y φ → ∀ x ∃ y φ.
    Inference form: from φ → ∀ x φ, conclude ∃ y φ → ∀ x ∃ y φ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "hbex")
    hyp = lb.hyp("hbex.1", "φ → ∀ x φ")
    # nf5i hbex.1: Ⅎ x φ
    s1 = lb.ref(
        "s1",
        "Ⅎ x φ",
        hyp,
        ref="nf5i",
        note="nf5i hbex.1",
    )
    # nfex s1: Ⅎ x ∃ y φ
    s2 = lb.ref(
        "s2",
        "Ⅎ x ∃ y φ",
        s1,
        ref="nfex",
        note="nfex nf5i",
    )
    # nf5ri s2: ∃ y φ → ∀ x ∃ y φ
    res = lb.ref(
        "res",
        "∃ y φ → ∀ x ∃ y φ",
        s2,
        ref="nf5ri",
        note="nf5ri nfex",
    )
    return lb.build(res)


def prove_hbim1(sys: System) -> Proof:
    """hbim1: ( φ → ψ ) → ∀ x ( φ → ψ ).
    Hypothesis builder for implication.  From φ → ∀ x φ and
    φ → ( ψ → ∀ x ψ ), conclude that the implication implies its
    own universal generalization.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "hbim1")
    h1 = lb.hyp("hbim1.1", "φ → ∀ x φ")
    h2 = lb.hyp("hbim1.2", "φ → ( ψ → ∀ x ψ )")
    # a2i hbim1.2: ( φ → ψ ) → ( φ → ∀ x ψ )
    s1 = lb.ref(
        "s1",
        "( φ → ψ ) → ( φ → ∀ x ψ )",
        h2,
        ref="a2i",
        note="a2i hbim1.2",
    )
    # 19.21h hbim1.1: ∀ x ( φ → ψ ) ↔ ( φ → ∀ x ψ )
    s2 = lb.ref(
        "s2",
        "∀ x ( φ → ψ ) ↔ ( φ → ∀ x ψ )",
        h1,
        ref="19.21h",
        note="19.21h hbim1.1",
    )
    # sylibr s1, s2: ( φ → ψ ) → ∀ x ( φ → ψ )
    res = lb.ref(
        "res",
        "( φ → ψ ) → ∀ x ( φ → ψ )",
        s1,
        s2,
        ref="sylibr",
        note="sylibr a2i, 19.21h",
    )
    return lb.build(res)


def prove_hbim(sys: System) -> Proof:
    """hbim: ( φ → ψ ) → ∀ x ( φ → ψ ).
    Theorem-scheme form of the hypothesis builder for implication.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "hbim")
    h1 = lb.hyp("hbim.1", "φ → ∀ x φ")
    h2 = lb.hyp("hbim.2", "ψ → ∀ x ψ")
    # a1i hbim.2: φ → ( ψ → ∀ x ψ )
    s1 = lb.ref(
        "s1",
        "φ → ( ψ → ∀ x ψ )",
        h2,
        ref="a1i",
        note="a1i hbim.2",
    )
    # hbim1 hbim.1 s1: ( φ → ψ ) → ∀ x ( φ → ψ )
    res = lb.ref(
        "res",
        "( φ → ψ ) → ∀ x ( φ → ψ )",
        h1,
        s1,
        ref="hbim1",
        note="hbim1 hbim.1 (a1i hbim.2)",
    )
    return lb.build(res)


def prove_hbimd(sys: System) -> Proof:
    """hbimd: φ → ( ( ψ → χ ) → ∀ x ( ψ → χ ) ).
    Deduction form of the hypothesis builder for implication.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "hbimd")
    h1 = lb.hyp("hbimd.1", "φ → ∀ x φ")
    h2 = lb.hyp("hbimd.2", "φ → ( ψ → ∀ x ψ )")
    h3 = lb.hyp("hbimd.3", "φ → ( χ → ∀ x χ )")
    # nf5dh hbimd.1, hbimd.2: φ → Ⅎ x ψ
    s1 = lb.ref(
        "s1",
        "φ → Ⅎ x ψ",
        h1,
        h2,
        ref="nf5dh",
        note="nf5dh hbimd.1, hbimd.2",
    )
    # nf5dh hbimd.1, hbimd.3: φ → Ⅎ x χ
    s2 = lb.ref(
        "s2",
        "φ → Ⅎ x χ",
        h1,
        h3,
        ref="nf5dh",
        note="nf5dh hbimd.1, hbimd.3",
    )
    # nfimd s1, s2: φ → Ⅎ x ( ψ → χ )
    s3 = lb.ref(
        "s3",
        "φ → Ⅎ x ( ψ → χ )",
        s1,
        s2,
        ref="nfimd",
        note="nfimd",
    )
    # nf5rd s3: φ → ( ( ψ → χ ) → ∀ x ( ψ → χ ) )
    res = lb.ref(
        "res",
        "φ → ( ( ψ → χ ) → ∀ x ( ψ → χ ) )",
        s3,
        ref="nf5rd",
        note="nf5rd",
    )
    return lb.build(res)


def prove_hbnd(sys: System) -> Proof:
    """hbnd: φ → ( ¬ ψ → ∀ x ¬ ψ ).
    Hypothesis builder for negation, deduction form.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "hbnd")
    h1 = lb.hyp("hbnd.1", "φ → ∀ x φ")
    h2 = lb.hyp("hbnd.2", "φ → ( ψ → ∀ x ψ )")
    # alrimih: from (φ → ∀x φ) and (φ → (ψ → ∀x ψ)), get φ → ∀x (ψ → ∀x ψ)
    s1 = lb.ref(
        "s1",
        "φ → ∀ x ( ψ → ∀ x ψ )",
        h1,
        h2,
        ref="alrimih",
        note="alrimih hbnd.1, hbnd.2",
    )
    # hbnt [φ := ψ]: ∀x (ψ → ∀x ψ) → (¬ψ → ∀x ¬ψ)
    s2 = lb.ref(
        "s2",
        "∀ x ( ψ → ∀ x ψ ) → ( ¬ ψ → ∀ x ¬ ψ )",
        ref="hbnt",
        note="hbnt",
    )
    # syl: chain s1 and s2
    res = lb.ref(
        "res",
        "φ → ( ¬ ψ → ∀ x ¬ ψ )",
        s1,
        s2,
        ref="syl",
        note="syl alrimih, hbnt",
    )
    return lb.build(res)


def prove_hbnt(sys: System) -> Proof:
    """hbnt: ∀ x ( φ → ∀ x φ ) → ( ¬ φ → ∀ x ¬ φ ).
    If φ implies its own universal quantification for all x, then
    the negation of φ also implies its own universal quantification.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "hbnt")
    # nf5-1: ∀ x ( φ → ∀ x φ ) → Ⅎ x φ
    s1 = lb.ref(
        "s1",
        "∀ x ( φ → ∀ x φ ) → Ⅎ x φ",
        ref="nf5-1",
        note="nf5-1",
    )
    # nfnd with hypothesis s1: ∀ x ( φ → ∀ x φ ) → Ⅎ x ¬ φ
    s2 = lb.ref(
        "s2",
        "∀ x ( φ → ∀ x φ ) → Ⅎ x ¬ φ",
        s1,
        ref="nfnd",
        note="nfnd nf5-1",
    )
    # nf5rd with hypothesis s2: ∀ x ( φ → ∀ x φ ) → ( ¬ φ → ∀ x ¬ φ )
    res = lb.ref(
        "res",
        "∀ x ( φ → ∀ x φ ) → ( ¬ φ → ∀ x ¬ φ )",
        s2,
        ref="nf5rd",
        note="nf5rd nfnd",
    )
    return lb.build(res)


def prove_hbn(sys: System) -> Proof:
    """hbn: ¬ φ → ∀ x ¬ φ.
    If x is not free in φ, then x is not free in ¬φ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "hbn")
    hyp = lb.hyp("hbn.1", "φ → ∀ x φ")
    # hbnt: ∀ x ( φ → ∀ x φ ) → ( ¬ φ → ∀ x ¬ φ )
    s1 = lb.ref(
        "s1",
        "∀ x ( φ → ∀ x φ ) → ( ¬ φ → ∀ x ¬ φ )",
        ref="hbnt",
        note="hbnt",
    )
    # mpg: from (∀ x (φ → ∀ x φ) → (¬ φ → ∀ x ¬ φ)) and (φ → ∀ x φ),
    #      get (¬ φ → ∀ x ¬ φ)
    res = lb.ref(
        "res",
        "¬ φ → ∀ x ¬ φ",
        s1,
        hyp,
        ref="mpg",
        note="mpg hbnt, hbn.1",
    )
    return lb.build(res)


def prove_hbnae(sys: System) -> Proof:
    """hbnae: ¬ ∀ x x = y → ∀ z ¬ ∀ x x = y.
    hbn applied to hbae.  (Contributed by NM, 13-May-1993.)
    """
    lb = ProofBuilder(sys, "hbnae")
    # hbae: ∀ x x = y → ∀ z ∀ x x = y
    s1 = lb.ref(
        "s1",
        "∀ x x = y → ∀ z ∀ x x = y",
        ref="hbae",
        note="hbae",
    )
    # hbn hbae: ¬ ∀ x x = y → ∀ z ¬ ∀ x x = y
    res = lb.ref(
        "res",
        "¬ ∀ x x = y → ∀ z ¬ ∀ x x = y",
        s1,
        ref="hbn",
        note="hbn hbae",
    )
    return lb.build(res)


def prove_hbnaes(sys: System) -> Proof:
    """hbnaes: ¬ ∀ x x = y → φ.
    Syllogism form of hbnae.  (Contributed by NM, 13-May-1993.)
    """
    lb = ProofBuilder(sys, "hbnaes")
    hyp = lb.hyp("hbnaes.1", "∀ z ¬ ∀ x x = y → φ")
    # hbnae: ¬ ∀ x x = y → ∀ z ¬ ∀ x x = y
    s1 = lb.ref(
        "s1",
        "¬ ∀ x x = y → ∀ z ¬ ∀ x x = y",
        ref="hbnae",
        note="hbnae",
    )
    # syl hbnae hbnaes.1: ¬ ∀ x x = y → φ
    res = lb.ref(
        "res",
        "¬ ∀ x x = y → φ",
        s1,
        hyp,
        ref="syl",
        note="syl hbnae, hbnaes.1",
    )
    return lb.build(res)


def prove_19_9t(sys: System) -> Proof:
    """19.9t: Ⅎ x φ → ( ∃ x φ ↔ φ ).
    The not-free condition makes the existential quantifier redundant.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "19.9t")
    # id: Ⅎ x φ → Ⅎ x φ
    s1 = lb.ref(
        "s1",
        "Ⅎ x φ → Ⅎ x φ",
        ref="id",
        note="id",
    )
    # 19.9d with hypothesis Ⅎ x φ → Ⅎ x φ: Ⅎ x φ → ( ∃ x φ → φ )
    s2 = lb.ref(
        "s2",
        "Ⅎ x φ → ( ∃ x φ → φ )",
        s1,
        ref="19.9d",
        note="19.9d id",
    )
    # 19.8a: φ → ∃ x φ
    s3 = lb.ref(
        "s3",
        "φ → ∃ x φ",
        ref="19.8a",
        note="19.8a",
    )
    # impbid1: Ⅎ x φ → ( ∃ x φ ↔ φ )
    res = lb.ref(
        "res",
        "Ⅎ x φ → ( ∃ x φ ↔ φ )",
        s2,
        s3,
        ref="impbid1",
        note="impbid1 19.9d, 19.8a",
    )
    return lb.build(res)


def prove_19_9(sys: System) -> Proof:
    """19.9: ∃ x φ ↔ φ.
    Closed form of 19.9t: when φ is not free in x, the existential
    quantifier can be dropped.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "19.9")
    hyp = lb.hyp("19.9.1", "Ⅎ x φ")
    # 19.9t: Ⅎ x φ → ( ∃ x φ ↔ φ )
    s1 = lb.ref(
        "s1",
        "Ⅎ x φ → ( ∃ x φ ↔ φ )",
        ref="19.9t",
        note="19.9t",
    )
    # ax-mp: 19.9.1, 19.9t ⊢ ∃ x φ ↔ φ
    res = lb.mp("res", hyp, s1, "ax-mp 19.9t, 19.9.1")
    return lb.build(res)


def prove_19_41(sys: System) -> Proof:
    """19.41: ∃ x ( φ ∧ ψ ) ↔ ( ∃ x φ ∧ ψ ).
    Existential quantifier distributes over conjunction when the second
    conjunct does not contain the bound variable.
    (Contributed by NM, 10-Aug-1993.)
    """
    lb = ProofBuilder(sys, "19.41")
    hyp = lb.hyp("19.41.1", "Ⅎ x ψ")
    # 19.40: ∃ x ( φ ∧ ψ ) → ( ∃ x φ ∧ ∃ x ψ )
    s_19_40 = lb.ref(
        "s_19_40",
        "∃ x ( φ ∧ ψ ) → ( ∃ x φ ∧ ∃ x ψ )",
        ref="19.40",
        note="19.40",
    )
    # 19.9: ∃ x ψ ↔ ψ
    s_19_9 = lb.ref(
        "s_19_9",
        "∃ x ψ ↔ ψ",
        hyp,
        ref="19.9",
        note="19.9 19.41.1",
    )
    # anbi2i: ( ∃ x φ ∧ ∃ x ψ ) ↔ ( ∃ x φ ∧ ψ )
    s_anbi2i = lb.ref(
        "s_anbi2i",
        "( ∃ x φ ∧ ∃ x ψ ) ↔ ( ∃ x φ ∧ ψ )",
        s_19_9,
        ref="anbi2i",
        note="anbi2i 19.9",
    )
    # sylib: ∃ x ( φ ∧ ψ ) → ( ∃ x φ ∧ ψ )
    s_fwd = lb.ref(
        "s_fwd",
        "∃ x ( φ ∧ ψ ) → ( ∃ x φ ∧ ψ )",
        s_19_40,
        s_anbi2i,
        ref="sylib",
        note="sylib 19.40, anbi2i",
    )
    # pm3.21: ψ → ( φ → ( φ ∧ ψ ) )
    s_pm3_21 = lb.ref(
        "s_pm3_21",
        "ψ → ( φ → ( φ ∧ ψ ) )",
        ref="pm3.21",
        note="pm3.21",
    )
    # eximd: ψ → ( ∃ x φ → ∃ x ( φ ∧ ψ ) )
    s_eximd = lb.ref(
        "s_eximd",
        "ψ → ( ∃ x φ → ∃ x ( φ ∧ ψ ) )",
        hyp,
        s_pm3_21,
        ref="eximd",
        note="eximd 19.41.1, pm3.21",
    )
    # impcom: ( ∃ x φ ∧ ψ ) → ∃ x ( φ ∧ ψ )
    s_rev = lb.ref(
        "s_rev",
        "( ∃ x φ ∧ ψ ) → ∃ x ( φ ∧ ψ )",
        s_eximd,
        ref="impcom",
        note="impcom eximd",
    )
    # impbii: ∃ x ( φ ∧ ψ ) ↔ ( ∃ x φ ∧ ψ )
    res = lb.ref(
        "res",
        "∃ x ( φ ∧ ψ ) ↔ ( ∃ x φ ∧ ψ )",
        s_fwd,
        s_rev,
        ref="impbii",
        note="impbii",
    )
    return lb.build(res)


def prove_19_42(sys: System) -> Proof:
    """19.42: ∃ x ( φ ∧ ψ ) ↔ ( φ ∧ ∃ x ψ ).
    Existential quantifier distributes over conjunction when the first
    conjunct does not contain the bound variable.
    (Contributed by NM, 10-Aug-1993.)
    """
    lb = ProofBuilder(sys, "19.42")
    hyp = lb.hyp("19.42.1", "Ⅎ x φ")
    # 19.41 (with φ/ψ swapped): ∃ x ( ψ ∧ φ ) ↔ ( ∃ x ψ ∧ φ )
    s_19_41 = lb.ref(
        "s_19_41",
        "∃ x ( ψ ∧ φ ) ↔ ( ∃ x ψ ∧ φ )",
        hyp,
        ref="19.41",
        note="19.41 19.42.1",
    )
    # exancom: ∃ x ( φ ∧ ψ ) ↔ ∃ x ( ψ ∧ φ )
    s_exancom = lb.ref(
        "s_exancom",
        "∃ x ( φ ∧ ψ ) ↔ ∃ x ( ψ ∧ φ )",
        ref="exancom",
        note="exancom",
    )
    # ancom: ( φ ∧ ∃ x ψ ) ↔ ( ∃ x ψ ∧ φ )
    s_ancom = lb.ref(
        "s_ancom",
        "( φ ∧ ∃ x ψ ) ↔ ( ∃ x ψ ∧ φ )",
        ref="ancom",
        note="ancom",
    )
    # 3bitr4i: chain s_exancom, s_19_41, s_ancom → goal
    res = lb.ref(
        "res",
        "∃ x ( φ ∧ ψ ) ↔ ( φ ∧ ∃ x ψ )",
        s_19_41,  # hyp1: (ph ↔ ps)
        s_exancom,  # hyp2: (ch ↔ ph)
        s_ancom,  # hyp3: (th ↔ ps)
        ref="3bitr4i",
        note="3bitr4i exancom, 19.41, ancom",
    )
    return lb.build(res)


def prove_19_45(sys: System) -> Proof:
    """19.45: ∃ x ( φ ∨ ψ ) ↔ ( φ ∨ ∃ x ψ ).
    Existential quantifier distributes over disjunction when the first
    disjunct does not contain the bound variable.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "19.45")
    hyp = lb.hyp("19.45.1", "Ⅎ x φ")
    # 19.43: ∃ x ( φ ∨ ψ ) ↔ ( ∃ x φ ∨ ∃ x ψ )
    s_19_43 = lb.ref(
        "s_19_43",
        "∃ x ( φ ∨ ψ ) ↔ ( ∃ x φ ∨ ∃ x ψ )",
        ref="19.43",
        note="19.43",
    )
    # 19.9: from Ⅎ x φ, get ∃ x φ ↔ φ
    s_19_9 = lb.ref(
        "s_19_9",
        "∃ x φ ↔ φ",
        hyp,
        ref="19.9",
        note="19.9 19.45.1",
    )
    # orbi1i: ( ∃ x φ ↔ φ ) → ( ( ∃ x φ ∨ ∃ x ψ ) ↔ ( φ ∨ ∃ x ψ ) )
    s_orbi1i = lb.ref(
        "s_orbi1i",
        "( ∃ x φ ∨ ∃ x ψ ) ↔ ( φ ∨ ∃ x ψ )",
        s_19_9,
        ref="orbi1i",
        note="orbi1i 19.9",
    )
    # bitri: chain 19.43 and orbi1i result
    res = lb.ref(
        "res",
        "∃ x ( φ ∨ ψ ) ↔ ( φ ∨ ∃ x ψ )",
        s_19_43,
        s_orbi1i,
        ref="bitri",
        note="bitri 19.43, orbi1i",
    )
    return lb.build(res)


def prove_19_44(sys: System) -> Proof:
    """19.44: ∃ x ( φ ∨ ψ ) ↔ ( ∃ x φ ∨ ψ ).
    Existential quantifier distributes over disjunction when the second
    disjunct does not contain the bound variable.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "19.44")
    hyp = lb.hyp("19.44.1", "Ⅎ x ψ")
    # 19.43: ∃ x ( φ ∨ ψ ) ↔ ( ∃ x φ ∨ ∃ x ψ )
    s_19_43 = lb.ref(
        "s_19_43",
        "∃ x ( φ ∨ ψ ) ↔ ( ∃ x φ ∨ ∃ x ψ )",
        ref="19.43",
        note="19.43",
    )
    # 19.9: from Ⅎ x ψ, get ∃ x ψ ↔ ψ
    s_19_9 = lb.ref(
        "s_19_9",
        "∃ x ψ ↔ ψ",
        hyp,
        ref="19.9",
        note="19.9 19.44.1",
    )
    # orbi2i: ( ∃ x ψ ↔ ψ ) → ( ( ∃ x φ ∨ ∃ x ψ ) ↔ ( ∃ x φ ∨ ψ ) )
    s_orbi2i = lb.ref(
        "s_orbi2i",
        "( ∃ x φ ∨ ∃ x ψ ) ↔ ( ∃ x φ ∨ ψ )",
        s_19_9,
        ref="orbi2i",
        note="orbi2i 19.9",
    )
    # bitri: chain 19.43 and orbi2i result
    res = lb.ref(
        "res",
        "∃ x ( φ ∨ ψ ) ↔ ( ∃ x φ ∨ ψ )",
        s_19_43,
        s_orbi2i,
        ref="bitri",
        note="bitri 19.43, orbi2i",
    )
    return lb.build(res)


def prove_eean(sys: System) -> Proof:
    """eean: ∃ x ∃ y ( φ ∧ ψ ) ↔ ( ∃ x φ ∧ ∃ y ψ ).
    Double existential quantifier with conjunction distributed. The proof uses
    19.42 to push the inner ∃ y into the conjunction, exbii to add ∃ x, and 19.41
    to distribute the outer ∃ x over the conjunction.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "eean")
    hyp1 = lb.hyp("eean.1", "Ⅎ y φ")
    hyp2 = lb.hyp("eean.2", "Ⅎ x ψ")
    # 19.42: Ⅎ y φ ⊢ ∃ y ( φ ∧ ψ ) ↔ ( φ ∧ ∃ y ψ )
    s1 = lb.ref(
        "s1",
        "∃ y ( φ ∧ ψ ) ↔ ( φ ∧ ∃ y ψ )",
        hyp1,
        ref="19.42",
        note="19.42 eean.1",
    )
    # exbii s1: ∃ x ∃ y ( φ ∧ ψ ) ↔ ∃ x ( φ ∧ ∃ y ψ )
    s2 = lb.ref(
        "s2",
        "∃ x ∃ y ( φ ∧ ψ ) ↔ ∃ x ( φ ∧ ∃ y ψ )",
        s1,
        ref="exbii",
        note="exbii 19.42",
    )
    # nfex eean.2: Ⅎ x ∃ y ψ
    s3 = lb.ref(
        "s3",
        "Ⅎ x ∃ y ψ",
        hyp2,
        ref="nfex",
        note="nfex eean.2",
    )
    # 19.41 s3: ∃ x ( φ ∧ ∃ y ψ ) ↔ ( ∃ x φ ∧ ∃ y ψ )
    s4 = lb.ref(
        "s4",
        "∃ x ( φ ∧ ∃ y ψ ) ↔ ( ∃ x φ ∧ ∃ y ψ )",
        s3,
        ref="19.41",
        note="19.41 nfex",
    )
    # bitri s2, s4: ∃ x ∃ y ( φ ∧ ψ ) ↔ ( ∃ x φ ∧ ∃ y ψ )
    res = lb.ref(
        "res",
        "∃ x ∃ y ( φ ∧ ψ ) ↔ ( ∃ x φ ∧ ∃ y ψ )",
        s2,
        s4,
        ref="bitri",
        note="bitri exbii, 19.41",
    )
    return lb.build(res)


def prove_eeanv(sys: System) -> Proof:
    """eeanv: ∃ x ∃ y ( φ ∧ ψ ) ↔ ( ∃ x φ ∧ ∃ y ψ ).
    Distinct variable version of eean.  Uses nfv to eliminate the not-free
    hypotheses of eean.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "eeanv")
    # nfv: Ⅎ y φ
    s1 = lb.ref("s1", "Ⅎ y φ", ref="nfv", note="nfv")
    # nfv: Ⅎ x ψ
    s2 = lb.ref("s2", "Ⅎ x ψ", ref="nfv", note="nfv")
    # eean with the nfv hypotheses
    res = lb.ref(
        "res",
        "∃ x ∃ y ( φ ∧ ψ ) ↔ ( ∃ x φ ∧ ∃ y ψ )",
        s1,
        s2,
        ref="eean",
        note="eean nfv, nfv",
    )
    return lb.build(res)


def prove_ee4anv(sys: System) -> Proof:
    """ee4anv: ∃ x ∃ y ∃ z ∃ w ( φ ∧ ψ ) ↔ ( ∃ x ∃ y φ ∧ ∃ z ∃ w ψ ).
    Distinct variable version of eean extended to four variables.
    The proof uses excom to reorder quantifiers, eeanv to distribute
    the inner two over conjunction, and eean to combine the outer pair
    under not-free conditions derived from nfv/nfex.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "ee4anv")
    # excom: swap y and z
    s1 = lb.ref(
        "s1",
        "∃ y ∃ z ∃ w ( φ ∧ ψ ) ↔ ∃ z ∃ y ∃ w ( φ ∧ ψ )",
        ref="excom",
        note="excom",
    )
    # exbii with ∃x: add outer quantifier
    s2 = lb.ref(
        "s2",
        "∃ x ∃ y ∃ z ∃ w ( φ ∧ ψ ) ↔ ∃ x ∃ z ∃ y ∃ w ( φ ∧ ψ )",
        s1,
        ref="exbii",
        note="exbii excom",
    )
    # eeanv: distribute ∃y∃w over conjunction
    s3 = lb.ref(
        "s3",
        "∃ y ∃ w ( φ ∧ ψ ) ↔ ( ∃ y φ ∧ ∃ w ψ )",
        ref="eeanv",
        note="eeanv",
    )
    # 2exbii with ∃x∃z: add two outer quantifiers
    s4 = lb.ref(
        "s4",
        "∃ x ∃ z ∃ y ∃ w ( φ ∧ ψ ) ↔ ∃ x ∃ z ( ∃ y φ ∧ ∃ w ψ )",
        s3,
        ref="2exbii",
        note="2exbii eeanv",
    )
    # nfv: Ⅎ z φ
    s5 = lb.ref("s5", "Ⅎ z φ", ref="nfv", note="nfv")
    # nfex: Ⅎ z ∃ y φ
    s6 = lb.ref("s6", "Ⅎ z ∃ y φ", s5, ref="nfex", note="nfex nfv")
    # nfv: Ⅎ x ψ
    s7 = lb.ref("s7", "Ⅎ x ψ", ref="nfv", note="nfv")
    # nfex: Ⅎ x ∃ w ψ
    s8 = lb.ref("s8", "Ⅎ x ∃ w ψ", s7, ref="nfex", note="nfex nfv")
    # eean: combine with not-free conditions
    s9 = lb.ref(
        "s9",
        "∃ x ∃ z ( ∃ y φ ∧ ∃ w ψ ) ↔ ( ∃ x ∃ y φ ∧ ∃ z ∃ w ψ )",
        s6,
        s8,
        ref="eean",
        note="eean nfex, nfex",
    )
    # 3bitri: chain s2, s4, s9
    res = lb.ref(
        "res",
        "∃ x ∃ y ∃ z ∃ w ( φ ∧ ψ ) ↔ ( ∃ x ∃ y φ ∧ ∃ z ∃ w ψ )",
        s2,
        s4,
        s9,
        ref="3bitri",
        note="3bitri exbii, 2exbii, eean",
    )
    return lb.build(res)


def prove_ee4anvOLD(sys: System) -> Proof:
    """ee4anvOLD: ∃ x ∃ y ∃ z ∃ w ( φ ∧ ψ ) ↔ ( ∃ x ∃ y φ ∧ ∃ z ∃ w ψ ).
    Older version of ee4anv.  Uses eeanv and 2exbii instead of nfv/nfex/eean.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "ee4anvOLD")
    # excom: swap y and z
    s1 = lb.ref(
        "s1",
        "∃ y ∃ z ∃ w ( φ ∧ ψ ) ↔ ∃ z ∃ y ∃ w ( φ ∧ ψ )",
        ref="excom",
        note="excom",
    )
    # exbii with ∃x: add outer quantifier
    s2 = lb.ref(
        "s2",
        "∃ x ∃ y ∃ z ∃ w ( φ ∧ ψ ) ↔ ∃ x ∃ z ∃ y ∃ w ( φ ∧ ψ )",
        s1,
        ref="exbii",
        note="exbii excom",
    )
    # eeanv: distribute ∃y∃w over conjunction
    s3 = lb.ref(
        "s3",
        "∃ y ∃ w ( φ ∧ ψ ) ↔ ( ∃ y φ ∧ ∃ w ψ )",
        ref="eeanv",
        note="eeanv",
    )
    # 2exbii with ∃x∃z: add two outer quantifiers
    s4 = lb.ref(
        "s4",
        "∃ x ∃ z ∃ y ∃ w ( φ ∧ ψ ) ↔ ∃ x ∃ z ( ∃ y φ ∧ ∃ w ψ )",
        s3,
        ref="2exbii",
        note="2exbii eeanv",
    )
    # eeanv: distribute ∃x∃z over conjunction
    s5 = lb.ref(
        "s5",
        "∃ x ∃ z ( ∃ y φ ∧ ∃ w ψ ) ↔ ( ∃ x ∃ y φ ∧ ∃ z ∃ w ψ )",
        ref="eeanv",
        note="eeanv",
    )
    # 3bitri: chain s2 ↔ s4 ↔ s5
    res = lb.ref(
        "res",
        "∃ x ∃ y ∃ z ∃ w ( φ ∧ ψ ) ↔ ( ∃ x ∃ y φ ∧ ∃ z ∃ w ψ )",
        s2,
        s4,
        s5,
        ref="3bitri",
        note="3bitri exbii, 2exbii, eeanv",
    )
    return lb.build(res)


def prove_eeeanv(sys: System) -> Proof:
    """eeeanv: ∃ x ∃ y ∃ z ( φ ∧ ψ ∧ χ ) ↔ ( ∃ x φ ∧ ∃ y ψ ∧ ∃ z χ ).
    Distinct variable version of eean extended to three variables.
    The proof expands the triple conjunction with df-3an, distributes
    the existential quantifiers with 19.42v and 19.41 (using nfv/nfex
    for the not-free conditions), then recombines with eeanv and anbi1i.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "eeeanv")
    # df-3an: ( φ ∧ ψ ∧ χ ) ↔ ( ( φ ∧ ψ ) ∧ χ )
    s_df3an = lb.ref(
        "s_df3an",
        "( φ ∧ ψ ∧ χ ) ↔ ( ( φ ∧ ψ ) ∧ χ )",
        ref="df-3an",
        note="df-3an",
    )
    # exbii with ∃z: ∃ z ( φ ∧ ψ ∧ χ ) ↔ ∃ z ( ( φ ∧ ψ ) ∧ χ )
    s_ex_z = lb.ref(
        "s_ex_z",
        "∃ z ( φ ∧ ψ ∧ χ ) ↔ ∃ z ( ( φ ∧ ψ ) ∧ χ )",
        s_df3an,
        ref="exbii",
        note="exbii df-3an",
    )
    # exbii with ∃y: ∃ y ∃ z ( φ ∧ ψ ∧ χ ) ↔ ∃ y ∃ z ( ( φ ∧ ψ ) ∧ χ )
    s_ex_y = lb.ref(
        "s_ex_y",
        "∃ y ∃ z ( φ ∧ ψ ∧ χ ) ↔ ∃ y ∃ z ( ( φ ∧ ψ ) ∧ χ )",
        s_ex_z,
        ref="exbii",
        note="exbii",
    )
    # exbii with ∃x: ∃ x ∃ y ∃ z ( φ ∧ ψ ∧ χ ) ↔ ∃ x ∃ y ∃ z ( ( φ ∧ ψ ) ∧ χ )
    s_ex_x = lb.ref(
        "s_ex_x",
        "∃ x ∃ y ∃ z ( φ ∧ ψ ∧ χ ) ↔ ∃ x ∃ y ∃ z ( ( φ ∧ ψ ) ∧ χ )",
        s_ex_y,
        ref="exbii",
        note="exbii",
    )
    # 19.42v: ∃ z ( ( φ ∧ ψ ) ∧ χ ) ↔ ( ( φ ∧ ψ ) ∧ ∃ z χ )
    s_19_42v = lb.ref(
        "s_19_42v",
        "∃ z ( ( φ ∧ ψ ) ∧ χ ) ↔ ( ( φ ∧ ψ ) ∧ ∃ z χ )",
        ref="19.42v",
        note="19.42v",
    )
    # 2exbii: ∃ x ∃ y ∃ z ( ( φ ∧ ψ ) ∧ χ ) ↔ ∃ x ∃ y ( ( φ ∧ ψ ) ∧ ∃ z χ )
    s_2exbii = lb.ref(
        "s_2exbii",
        "∃ x ∃ y ∃ z ( ( φ ∧ ψ ) ∧ χ ) ↔ ∃ x ∃ y ( ( φ ∧ ψ ) ∧ ∃ z χ )",
        s_19_42v,
        ref="2exbii",
        note="2exbii 19.42v",
    )
    # nfv: Ⅎ y χ
    s_nfv_y = lb.ref("s_nfv_y", "Ⅎ y χ", ref="nfv", note="nfv")
    # nfex: Ⅎ y ∃ z χ
    s_nfex_y = lb.ref(
        "s_nfex_y",
        "Ⅎ y ∃ z χ",
        s_nfv_y,
        ref="nfex",
        note="nfex nfv",
    )
    # nfv: Ⅎ x χ
    s_nfv_x = lb.ref("s_nfv_x", "Ⅎ x χ", ref="nfv", note="nfv")
    # nfex: Ⅎ x ∃ z χ
    s_nfex_x = lb.ref(
        "s_nfex_x",
        "Ⅎ x ∃ z χ",
        s_nfv_x,
        ref="nfex",
        note="nfex nfv",
    )
    # 19.41: ∃ y ( ( φ ∧ ψ ) ∧ ∃ z χ ) ↔ ( ∃ y ( φ ∧ ψ ) ∧ ∃ z χ )
    s_19_41_y = lb.ref(
        "s_19_41_y",
        "∃ y ( ( φ ∧ ψ ) ∧ ∃ z χ ) ↔ ( ∃ y ( φ ∧ ψ ) ∧ ∃ z χ )",
        s_nfex_y,
        ref="19.41",
        note="19.41 nfex",
    )
    # 19.41: ∃ x ( ∃ y ( φ ∧ ψ ) ∧ ∃ z χ ) ↔ ( ∃ x ∃ y ( φ ∧ ψ ) ∧ ∃ z χ )
    s_19_41_x = lb.ref(
        "s_19_41_x",
        "∃ x ( ∃ y ( φ ∧ ψ ) ∧ ∃ z χ ) ↔ ( ∃ x ∃ y ( φ ∧ ψ ) ∧ ∃ z χ )",
        s_nfex_x,
        ref="19.41",
        note="19.41 nfex",
    )
    # exbii with ∃x: ∃ x ∃ y ( ( φ ∧ ψ ) ∧ ∃ z χ ) ↔ ∃ x ( ∃ y ( φ ∧ ψ ) ∧ ∃ z χ )
    s_ex_x2 = lb.ref(
        "s_ex_x2",
        "∃ x ∃ y ( ( φ ∧ ψ ) ∧ ∃ z χ ) ↔ ∃ x ( ∃ y ( φ ∧ ψ ) ∧ ∃ z χ )",
        s_19_41_y,
        ref="exbii",
        note="exbii 19.41",
    )
    # bitri: chain s_ex_x2 and s_19_41_x
    s_bitri = lb.ref(
        "s_bitri",
        "∃ x ∃ y ( ( φ ∧ ψ ) ∧ ∃ z χ ) ↔ ( ∃ x ∃ y ( φ ∧ ψ ) ∧ ∃ z χ )",
        s_ex_x2,
        s_19_41_x,
        ref="bitri",
        note="bitri exbii, 19.41",
    )
    # 3bitri: chain s_ex_x, s_2exbii, s_bitri
    s_3bitri = lb.ref(
        "s_3bitri",
        "∃ x ∃ y ∃ z ( φ ∧ ψ ∧ χ ) ↔ ( ∃ x ∃ y ( φ ∧ ψ ) ∧ ∃ z χ )",
        s_ex_x,
        s_2exbii,
        s_bitri,
        ref="3bitri",
        note="3bitri exbii, 2exbii, bitri",
    )
    # eeanv: ∃ x ∃ y ( φ ∧ ψ ) ↔ ( ∃ x φ ∧ ∃ y ψ )
    s_eeanv = lb.ref(
        "s_eeanv",
        "∃ x ∃ y ( φ ∧ ψ ) ↔ ( ∃ x φ ∧ ∃ y ψ )",
        ref="eeanv",
        note="eeanv",
    )
    # anbi1i: ( ∃ x ∃ y ( φ ∧ ψ ) ∧ ∃ z χ ) ↔ ( ( ∃ x φ ∧ ∃ y ψ ) ∧ ∃ z χ )
    s_anbi1i = lb.ref(
        "s_anbi1i",
        "( ∃ x ∃ y ( φ ∧ ψ ) ∧ ∃ z χ ) ↔ ( ( ∃ x φ ∧ ∃ y ψ ) ∧ ∃ z χ )",
        s_eeanv,
        ref="anbi1i",
        note="anbi1i eeanv",
    )
    # bitri: chain s_3bitri and s_anbi1i
    s_bitri4 = lb.ref(
        "s_bitri4",
        "∃ x ∃ y ∃ z ( φ ∧ ψ ∧ χ ) ↔ ( ( ∃ x φ ∧ ∃ y ψ ) ∧ ∃ z χ )",
        s_3bitri,
        s_anbi1i,
        ref="bitri",
        note="bitri 3bitri, anbi1i",
    )
    # df-3an: ( ∃ x φ ∧ ∃ y ψ ∧ ∃ z χ ) ↔ ( ( ∃ x φ ∧ ∃ y ψ ) ∧ ∃ z χ )
    s_df3an2 = lb.ref(
        "s_df3an2",
        "( ∃ x φ ∧ ∃ y ψ ∧ ∃ z χ ) ↔ ( ( ∃ x φ ∧ ∃ y ψ ) ∧ ∃ z χ )",
        ref="df-3an",
        note="df-3an",
    )
    # bitr4i: chain s_bitri4 and s_df3an2 → final result
    res = lb.ref(
        "res",
        "∃ x ∃ y ∃ z ( φ ∧ ψ ∧ χ ) ↔ ( ∃ x φ ∧ ∃ y ψ ∧ ∃ z χ )",
        s_bitri4,
        s_df3an2,
        ref="bitr4i",
        note="bitr4i",
    )
    return lb.build(res)


def prove_eeor(sys: System) -> Proof:
    """eeor: ∃ x ∃ y ( φ ∨ ψ ) ↔ ( ∃ x φ ∨ ∃ y ψ ).
    Double existential quantifier with disjunction distributed. The proof uses
    19.43 to distribute each existential over the disjunction, 19.9 to drop
    quantifiers under the not-free hypotheses, excom to reorder, and orbi12i
    to combine.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "eeor")
    hyp1 = lb.hyp("eeor.1", "Ⅎ y φ")
    hyp2 = lb.hyp("eeor.2", "Ⅎ x ψ")
    # 19.43: ∃ y ( φ ∨ ψ ) ↔ ( ∃ y φ ∨ ∃ y ψ )
    s1 = lb.ref(
        "s1",
        "∃ y ( φ ∨ ψ ) ↔ ( ∃ y φ ∨ ∃ y ψ )",
        ref="19.43",
        note="19.43",
    )
    # exbii s1: ∃ x ∃ y ( φ ∨ ψ ) ↔ ∃ x ( ∃ y φ ∨ ∃ y ψ )
    s2 = lb.ref(
        "s2",
        "∃ x ∃ y ( φ ∨ ψ ) ↔ ∃ x ( ∃ y φ ∨ ∃ y ψ )",
        s1,
        ref="exbii",
        note="exbii 19.43",
    )
    # 19.43: ∃ x ( ∃ y φ ∨ ∃ y ψ ) ↔ ( ∃ x ∃ y φ ∨ ∃ x ∃ y ψ )
    s3 = lb.ref(
        "s3",
        "∃ x ( ∃ y φ ∨ ∃ y ψ ) ↔ ( ∃ x ∃ y φ ∨ ∃ x ∃ y ψ )",
        ref="19.43",
        note="19.43",
    )
    # bitri s2, s3: ∃ x ∃ y ( φ ∨ ψ ) ↔ ( ∃ x ∃ y φ ∨ ∃ x ∃ y ψ )
    s4 = lb.ref(
        "s4",
        "∃ x ∃ y ( φ ∨ ψ ) ↔ ( ∃ x ∃ y φ ∨ ∃ x ∃ y ψ )",
        s2,
        s3,
        ref="bitri",
        note="bitri exbii, 19.43",
    )
    # 19.9 with eeor.1 (Ⅎ y φ): ∃ y φ ↔ φ
    s5 = lb.ref(
        "s5",
        "∃ y φ ↔ φ",
        hyp1,
        ref="19.9",
        note="19.9 eeor.1",
    )
    # exbii s5: ∃ x ∃ y φ ↔ ∃ x φ
    s6 = lb.ref(
        "s6",
        "∃ x ∃ y φ ↔ ∃ x φ",
        s5,
        ref="exbii",
        note="exbii 19.9",
    )
    # excom: ∃ x ∃ y ψ ↔ ∃ y ∃ x ψ
    s7 = lb.ref(
        "s7",
        "∃ x ∃ y ψ ↔ ∃ y ∃ x ψ",
        ref="excom",
        note="excom",
    )
    # 19.9 with eeor.2 (Ⅎ x ψ): ∃ x ψ ↔ ψ
    s8 = lb.ref(
        "s8",
        "∃ x ψ ↔ ψ",
        hyp2,
        ref="19.9",
        note="19.9 eeor.2",
    )
    # exbii s8: ∃ y ∃ x ψ ↔ ∃ y ψ
    s9 = lb.ref(
        "s9",
        "∃ y ∃ x ψ ↔ ∃ y ψ",
        s8,
        ref="exbii",
        note="exbii 19.9",
    )
    # bitri s7, s9: ∃ x ∃ y ψ ↔ ∃ y ψ
    s10 = lb.ref(
        "s10",
        "∃ x ∃ y ψ ↔ ∃ y ψ",
        s7,
        s9,
        ref="bitri",
        note="bitri excom, exbii",
    )
    # orbi12i s6, s10: ( ∃ x ∃ y φ ∨ ∃ x ∃ y ψ ) ↔ ( ∃ x φ ∨ ∃ y ψ )
    s11 = lb.ref(
        "s11",
        "( ∃ x ∃ y φ ∨ ∃ x ∃ y ψ ) ↔ ( ∃ x φ ∨ ∃ y ψ )",
        s6,
        s10,
        ref="orbi12i",
        note="orbi12i exbii, bitri",
    )
    # bitri s4, s11: ∃ x ∃ y ( φ ∨ ψ ) ↔ ( ∃ x φ ∨ ∃ y ψ )
    res = lb.ref(
        "res",
        "∃ x ∃ y ( φ ∨ ψ ) ↔ ( ∃ x φ ∨ ∃ y ψ )",
        s4,
        s11,
        ref="bitri",
        note="bitri",
    )
    return lb.build(res)


def prove_19_23bi(sys: System) -> Proof:
    """19.23bi: φ → ψ.
    Inference form: from ∃ x φ → ψ, conclude φ → ψ.  The proof
    instantiates x with itself via 19.8a (φ → ∃ x φ), then chains
    through syl.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "19.23bi")
    hyp = lb.hyp("19.23bi.1", "∃ x φ → ψ")
    # 19.8a: φ → ∃ x φ
    s1 = lb.ref(
        "s1",
        "φ → ∃ x φ",
        ref="19.8a",
        note="19.8a",
    )
    # syl: (φ → ∃ x φ) → ((∃ x φ → ψ) → (φ → ψ))
    res = lb.ref(
        "res",
        "φ → ψ",
        s1,
        hyp,
        ref="syl",
        note="syl 19.8a, 19.23bi.1",
    )
    return lb.build(res)


def prove_2nexaln(sys: System) -> Proof:
    """2nexaln: ¬ ∃ x ∃ y φ ↔ ∀ x ∀ y ¬ φ.
    Negated double existence is equivalent to double universal of negation.
    From 2exnaln, bicomi, and con1bii.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "2nexaln")
    s1 = lb.ref(
        "s1",
        "∃ x ∃ y φ ↔ ¬ ∀ x ∀ y ¬ φ",
        ref="2exnaln",
        note="2exnaln",
    )
    s2 = lb.ref(
        "s2",
        "¬ ∀ x ∀ y ¬ φ ↔ ∃ x ∃ y φ",
        s1,
        ref="bicomi",
        note="bicomi 2exnaln",
    )
    res = lb.ref(
        "res",
        "¬ ∃ x ∃ y φ ↔ ∀ x ∀ y ¬ φ",
        s2,
        ref="con1bii",
        note="con1bii bicomi",
    )
    return lb.build(res)


def prove_eximd(sys: System) -> Proof:
    """eximd: φ → ( ∃ x ψ → ∃ x χ ).
    Deduction form of exim. Uses nf5ri to convert the not-free
    hypothesis into the universal hypothesis needed by eximdh.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "eximd")
    hyp1 = lb.hyp("eximd.1", "Ⅎ x φ")
    hyp2 = lb.hyp("eximd.2", "φ → ( ψ → χ )")
    # nf5ri: Ⅎ x φ ⊢ φ → ∀ x φ
    s1 = lb.ref(
        "s1",
        "φ → ∀ x φ",
        hyp1,
        ref="nf5ri",
        note="nf5ri eximd.1",
    )
    # eximdh: (φ → ∀ x φ), (φ → (ψ → χ)) ⊢ φ → (∃ x ψ → ∃ x χ)
    res = lb.ref(
        "res",
        "φ → ( ∃ x ψ → ∃ x χ )",
        s1,
        hyp2,
        ref="eximdh",
        note="eximdh nf5ri, eximd.2",
    )
    return lb.build(res)


def prove_exlimd(sys: System) -> Proof:
    """exlimd: φ → ( ∃ x ψ → χ ).
    Deduction form of the existential quantifier. From Ⅎ x φ, Ⅎ x χ,
    and φ → ( ψ → χ ), deduce that if there exists an x such that ψ,
    then χ.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "exlimd")
    hyp1 = lb.hyp("exlimd.1", "Ⅎ x φ")
    hyp2 = lb.hyp("exlimd.2", "Ⅎ x χ")
    hyp3 = lb.hyp("exlimd.3", "φ → ( ψ → χ )")
    # eximd: Ⅎ x φ, φ → ( ψ → χ ) ⊢ φ → ( ∃ x ψ → ∃ x χ )
    s1 = lb.ref(
        "s1",
        "φ → ( ∃ x ψ → ∃ x χ )",
        hyp1,
        hyp3,
        ref="eximd",
        note="eximd exlimd.1, exlimd.3",
    )
    # 19.9: Ⅎ x χ ⊢ ∃ x χ ↔ χ
    s2 = lb.ref(
        "s2",
        "∃ x χ ↔ χ",
        hyp2,
        ref="19.9",
        note="19.9 exlimd.2",
    )
    # imbitrdi: (φ → (∃ x ψ → ∃ x χ)), (∃ x χ ↔ χ) ⊢ φ → (∃ x ψ → χ)
    res = lb.ref(
        "res",
        "φ → ( ∃ x ψ → χ )",
        s1,
        s2,
        ref="imbitrdi",
        note="imbitrdi eximd, 19.9",
    )
    return lb.build(res)


def prove_exlimdh(sys: System) -> Proof:
    """exlimdh: φ → ( ∃ x ψ → χ ).
    Deduction form of the existential quantifier. From φ → ∀ x φ and
    χ → ∀ x χ, and φ → ( ψ → χ ), deduce that if there exists an x
    such that ψ, then χ.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "exlimdh")
    hyp1 = lb.hyp("exlimdh.1", "φ → ∀ x φ")
    hyp2 = lb.hyp("exlimdh.2", "χ → ∀ x χ")
    hyp3 = lb.hyp("exlimdh.3", "φ → ( ψ → χ )")
    # nf5i: (φ → ∀ x φ) ⊢ Ⅎ x φ
    s1 = lb.ref(
        "s1",
        "Ⅎ x φ",
        hyp1,
        ref="nf5i",
        note="nf5i exlimdh.1",
    )
    # nf5i: (χ → ∀ x χ) ⊢ Ⅎ x χ
    s2 = lb.ref(
        "s2",
        "Ⅎ x χ",
        hyp2,
        ref="nf5i",
        note="nf5i exlimdh.2",
    )
    # exlimd: Ⅎ x φ, Ⅎ x χ, φ → ( ψ → χ ) ⊢ φ → ( ∃ x ψ → χ )
    res = lb.ref(
        "res",
        "φ → ( ∃ x ψ → χ )",
        s1,
        s2,
        hyp3,
        ref="exlimd",
        note="exlimd s1, s2, exlimdh.3",
    )
    return lb.build(res)


def prove_exlimimdd(sys: System) -> Proof:
    """exlimimdd: φ → χ.
    From Ⅎ x φ, Ⅎ x χ, φ → ∃ x ψ, and φ → ( ψ → χ ), conclude φ → χ.
    Uses exlimd and mpd.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "exlimimdd")
    hyp1 = lb.hyp("exlimimdd.1", "Ⅎ x φ")
    hyp2 = lb.hyp("exlimimdd.2", "Ⅎ x χ")
    hyp3 = lb.hyp("exlimimdd.3", "φ → ∃ x ψ")
    hyp4 = lb.hyp("exlimimdd.4", "φ → ( ψ → χ )")
    # exlimd: Ⅎ x φ, Ⅎ x χ, φ → ( ψ → χ ) ⊢ φ → ( ∃ x ψ → χ )
    s1 = lb.ref(
        "s1",
        "φ → ( ∃ x ψ → χ )",
        hyp1,
        hyp2,
        hyp4,
        ref="exlimd",
        note="exlimd exlimimdd.1, exlimimdd.2, exlimimdd.4",
    )
    # mpd: φ → ∃ x ψ, φ → ( ∃ x ψ → χ ) ⊢ φ → χ
    res = lb.ref(
        "res",
        "φ → χ",
        hyp3,
        s1,
        ref="mpd",
        note="mpd exlimimdd.3, exlimd",
    )
    return lb.build(res)


def prove_exlimdd(sys: System) -> Proof:
    """exlimdd: φ → χ.
    From Ⅎ x φ, Ⅎ x χ, φ → ∃ x ψ, and ( φ ∧ ψ ) → χ, conclude φ → χ.
    Uses ex and exlimimdd.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "exlimdd")
    hyp1 = lb.hyp("exlimdd.1", "Ⅎ x φ")
    hyp2 = lb.hyp("exlimdd.2", "Ⅎ x χ")
    hyp3 = lb.hyp("exlimdd.3", "φ → ∃ x ψ")
    hyp4 = lb.hyp("exlimdd.4", "( φ ∧ ψ ) → χ")
    # ex: ( φ ∧ ψ ) → χ ⊢ φ → ( ψ → χ )
    s1 = lb.ref(
        "s1",
        "φ → ( ψ → χ )",
        hyp4,
        ref="ex",
        note="ex exlimdd.4",
    )
    # exlimimdd: Ⅎ x φ, Ⅎ x χ, φ → ∃ x ψ, φ → ( ψ → χ ) ⊢ φ → χ
    res = lb.ref(
        "res",
        "φ → χ",
        hyp1,
        hyp2,
        hyp3,
        s1,
        ref="exlimimdd",
        note="exlimimdd exlimdd.1, exlimdd.2, exlimdd.3, ex",
    )
    return lb.build(res)


def prove_exbid(sys: System) -> Proof:
    """exbid: φ → ( ∃ x ψ ↔ ∃ x χ ).
    Deduction form of exbi. Uses nf5ri to convert the not-free
    hypothesis into the universal hypothesis needed by exbidh.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "exbid")
    hyp1 = lb.hyp("exbid.1", "Ⅎ x φ")
    hyp2 = lb.hyp("exbid.2", "φ → ( ψ ↔ χ )")
    # nf5ri: Ⅎ x φ ⊢ φ → ∀ x φ
    s1 = lb.ref(
        "s1",
        "φ → ∀ x φ",
        hyp1,
        ref="nf5ri",
        note="nf5ri exbid.1",
    )
    # exbidh: (φ → ∀ x φ), (φ → (ψ ↔ χ)) ⊢ φ → (∃ x ψ ↔ ∃ x χ)
    res = lb.ref(
        "res",
        "φ → ( ∃ x ψ ↔ ∃ x χ )",
        s1,
        hyp2,
        ref="exbidh",
        note="exbidh nf5ri, exbid.2",
    )
    return lb.build(res)


def prove_19_12vv(sys: System) -> Proof:
    """19.12vv: ∃ x ∀ y ( φ → ψ ) ↔ ∀ y ∃ x ( φ → ψ ).
    Existential before a universal swaps with universal before existential
    over the same implication.  Uses nfv + nfal to derive the not-free
    conditions for 19.36 and 19.21.
    """
    lb = ProofBuilder(sys, "19.12vv")
    # 19.21v: ∀ y ( φ → ψ ) ↔ ( φ → ∀ y ψ )
    s1 = lb.ref(
        "s1",
        "∀ y ( φ → ψ ) ↔ ( φ → ∀ y ψ )",
        ref="19.21v",
        note="19.21v",
    )
    # exbii s1: ∃ x ∀ y ( φ → ψ ) ↔ ∃ x ( φ → ∀ y ψ )
    s2 = lb.ref(
        "s2",
        "∃ x ∀ y ( φ → ψ ) ↔ ∃ x ( φ → ∀ y ψ )",
        s1,
        ref="exbii",
        note="exbii 19.21v",
    )
    # nfv: Ⅎ x ψ
    s3 = lb.ref("s3", "Ⅎ x ψ", ref="nfv", note="nfv")
    # nfal s3: Ⅎ x ∀ y ψ
    s4 = lb.ref("s4", "Ⅎ x ∀ y ψ", s3, ref="nfal", note="nfal nfv")
    # 19.36 s4: ∃ x ( φ → ∀ y ψ ) ↔ ( ∀ x φ → ∀ y ψ )
    s5 = lb.ref(
        "s5",
        "∃ x ( φ → ∀ y ψ ) ↔ ( ∀ x φ → ∀ y ψ )",
        s4,
        ref="19.36",
        note="19.36 nfal",
    )
    # 19.36v: ∃ x ( φ → ψ ) ↔ ( ∀ x φ → ψ )
    s6 = lb.ref(
        "s6",
        "∃ x ( φ → ψ ) ↔ ( ∀ x φ → ψ )",
        ref="19.36v",
        note="19.36v",
    )
    # albii s6: ∀ y ∃ x ( φ → ψ ) ↔ ∀ y ( ∀ x φ → ψ )
    s7 = lb.ref(
        "s7",
        "∀ y ∃ x ( φ → ψ ) ↔ ∀ y ( ∀ x φ → ψ )",
        s6,
        ref="albii",
        note="albii 19.36v",
    )
    # nfv: Ⅎ y φ
    s8 = lb.ref("s8", "Ⅎ y φ", ref="nfv", note="nfv")
    # nfal s8: Ⅎ y ∀ x φ
    s9 = lb.ref("s9", "Ⅎ y ∀ x φ", s8, ref="nfal", note="nfal nfv")
    # 19.21 s9: ∀ y ( ∀ x φ → ψ ) ↔ ( ∀ x φ → ∀ y ψ )
    s10 = lb.ref(
        "s10",
        "∀ y ( ∀ x φ → ψ ) ↔ ( ∀ x φ → ∀ y ψ )",
        s9,
        ref="19.21",
        note="19.21 nfal",
    )
    # bitr2i s7, s10: ( ∀ x φ → ∀ y ψ ) ↔ ∀ y ∃ x ( φ → ψ )
    s11 = lb.ref(
        "s11",
        "( ∀ x φ → ∀ y ψ ) ↔ ∀ y ∃ x ( φ → ψ )",
        s7,
        s10,
        ref="bitr2i",
        note="bitr2i",
    )
    # 3bitri s2, s5, s11: ∃ x ∀ y ( φ → ψ ) ↔ ∀ y ∃ x ( φ → ψ )
    res = lb.ref(
        "res",
        "∃ x ∀ y ( φ → ψ ) ↔ ∀ y ∃ x ( φ → ψ )",
        s2,
        s5,
        s11,
        ref="3bitri",
        note="3bitri",
    )
    return lb.build(res)


def prove_19_3(sys: System) -> Proof:
    """19.3: ∀ x φ ↔ φ.
    A universally quantified formula is equivalent to the formula
    itself when the formula does not depend on the bound variable.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "19.3")
    hyp = lb.hyp("19.3.1", "Ⅎ x φ")
    # sp: ∀ x φ → φ
    s1 = lb.ref(
        "s1",
        "∀ x φ → φ",
        ref="sp",
        note="sp",
    )
    # nf5ri: φ → ∀ x φ
    s2 = lb.ref(
        "s2",
        "φ → ∀ x φ",
        hyp,
        ref="nf5ri",
        note="nf5ri 19.3.1",
    )
    # impbii: (∀ x φ → φ) → ((φ → ∀ x φ) → (∀ x φ ↔ φ))
    res = lb.ref(
        "res",
        "∀ x φ ↔ φ",
        s1,
        s2,
        ref="impbii",
        note="impbii sp, nf5ri",
    )
    return lb.build(res)


def prove_19_3t(sys: System) -> Proof:
    """19.3t: Ⅎ x φ → ( ∀ x φ ↔ φ ).
    The not-free condition makes the universal quantifier redundant.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "19.3t")
    # sp: ∀ x φ → φ
    s1 = lb.ref(
        "s1",
        "∀ x φ → φ",
        ref="sp",
        note="sp",
    )
    # nf5r: Ⅎ x φ → ( φ → ∀ x φ )
    s2 = lb.ref(
        "s2",
        "Ⅎ x φ → ( φ → ∀ x φ )",
        ref="nf5r",
        note="nf5r",
    )
    # impbid2: Ⅎ x φ → ( ∀ x φ ↔ φ )
    res = lb.ref(
        "res",
        "Ⅎ x φ → ( ∀ x φ ↔ φ )",
        s1,
        s2,
        ref="impbid2",
        note="impbid2 sp, nf5r",
    )
    return lb.build(res)


def prove_19_23t(sys: System) -> Proof:
    """19.23t: ( Ⅎ x ψ → ( ∀ x ( φ → ψ ) ↔ ( ∃ x φ → ψ ) ) ).
    If x is not free in ψ, then ∀x(φ → ψ) is equivalent to (∃xφ → ψ).
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "19.23t")
    # 19.38b: ( Ⅎ x ψ → ( ( ∃ x φ → ∀ x ψ ) ↔ ∀ x ( φ → ψ ) ) )
    s1 = lb.ref(
        "s1",
        "Ⅎ x ψ → ( ( ∃ x φ → ∀ x ψ ) ↔ ∀ x ( φ → ψ ) )",
        ref="19.38b",
        note="19.38b",
    )
    # 19.3t: Ⅎ x ψ → ( ∀ x ψ ↔ ψ )
    s2 = lb.ref(
        "s2",
        "Ⅎ x ψ → ( ∀ x ψ ↔ ψ )",
        ref="19.3t",
        note="19.3t",
    )
    # imbi2d: Ⅎ x ψ → ( ( ∃ x φ → ∀ x ψ ) ↔ ( ∃ x φ → ψ ) )
    s3 = lb.ref(
        "s3",
        "Ⅎ x ψ → ( ( ∃ x φ → ∀ x ψ ) ↔ ( ∃ x φ → ψ ) )",
        s2,
        ref="imbi2d",
        note="imbi2d 19.3t",
    )
    # bitr3d: Ⅎ x ψ → ( ∀ x ( φ → ψ ) ↔ ( ∃ x φ → ψ ) )
    res = lb.ref(
        "res",
        "Ⅎ x ψ → ( ∀ x ( φ → ψ ) ↔ ( ∃ x φ → ψ ) )",
        s1,
        s3,
        ref="bitr3d",
        note="bitr3d 19.38b, imbi2d",
    )
    return lb.build(res)


def prove_19_23(sys: System) -> Proof:
    """19.23: ( ∀ x ( φ → ψ ) ↔ ( ∃ x φ → ψ ) ).
    If x is not free in ψ, the universal quantifier over an implication is
    equivalent to an implication with the existential quantifier.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "19.23")
    hyp = lb.hyp("19.23.1", "Ⅎ x ψ")
    # 19.23t: Ⅎ x ψ → ( ∀ x ( φ → ψ ) ↔ ( ∃ x φ → ψ ) )
    s1 = lb.ref(
        "s1",
        "Ⅎ x ψ → ( ∀ x ( φ → ψ ) ↔ ( ∃ x φ → ψ ) )",
        ref="19.23t",
        note="19.23t",
    )
    # ax-mp: apply the hypothesis to 19.23t
    res = lb.mp("res", hyp, s1, "ax-mp 19.23t, 19.23.1")
    return lb.build(res)


def prove_19_23h(sys: System) -> Proof:
    """19.23h: ∀ x ( φ → ψ ) ↔ ( ∃ x φ → ψ ).
    If ψ does not depend on x, the universal quantifier over an implication
    is equivalent to an implication with the existential quantifier.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "19.23h")
    h1 = lb.hyp("19.23h.1", "ψ → ∀ x ψ")
    # nf5i: from ψ → ∀ x ψ, derive Ⅎ x ψ
    s1 = lb.ref("s1", "Ⅎ x ψ", h1, ref="nf5i", note="nf5i 19.23h.1")
    # 19.23: from Ⅎ x ψ, derive the conclusion
    res = lb.ref(
        "res",
        "∀ x ( φ → ψ ) ↔ ( ∃ x φ → ψ )",
        s1,
        ref="19.23",
        note="19.23 nf5i",
    )
    return lb.build(res)


def prove_19_16(sys: System) -> Proof:
    """19.16: ∀ x ( φ ↔ ψ ) → ( φ ↔ ∀ x ψ ).
    When φ does not depend on x, the universal quantifier can be removed
    from the first argument of a universally quantified biconditional.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "19.16")
    hyp = lb.hyp("19.16.1", "Ⅎ x φ")
    # 19.3: ∀ x φ ↔ φ
    s1 = lb.ref(
        "s1",
        "∀ x φ ↔ φ",
        hyp,
        ref="19.3",
        note="19.3 19.16.1",
    )
    # albi: ∀ x ( φ ↔ ψ ) → ( ∀ x φ ↔ ∀ x ψ )
    s2 = lb.ref(
        "s2",
        "∀ x ( φ ↔ ψ ) → ( ∀ x φ ↔ ∀ x ψ )",
        ref="albi",
        note="albi",
    )
    # bitr3id: (∀ x φ ↔ φ), (∀ x ( φ ↔ ψ ) → ( ∀ x φ ↔ ∀ x ψ )) ⊢ (∀ x ( φ ↔ ψ ) → ( φ ↔ ∀ x ψ ))
    res = lb.ref(
        "res",
        "∀ x ( φ ↔ ψ ) → ( φ ↔ ∀ x ψ )",
        s1,
        s2,
        ref="bitr3id",
        note="bitr3id 19.3, albi",
    )
    return lb.build(res)


def prove_19_17(sys: System) -> Proof:
    """19.17: ∀ x ( φ ↔ ψ ) → ( ∀ x φ ↔ ψ ).
    When ψ does not depend on x, the universal quantifier can be removed
    from the second argument of a universally quantified biconditional.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "19.17")
    hyp = lb.hyp("19.17.1", "Ⅎ x ψ")
    # albi: ∀ x ( φ ↔ ψ ) → ( ∀ x φ ↔ ∀ x ψ )
    s1 = lb.ref(
        "s1",
        "∀ x ( φ ↔ ψ ) → ( ∀ x φ ↔ ∀ x ψ )",
        ref="albi",
        note="albi",
    )
    # 19.3: ∀ x ψ ↔ ψ
    s2 = lb.ref(
        "s2",
        "∀ x ψ ↔ ψ",
        hyp,
        ref="19.3",
        note="19.3 19.17.1",
    )
    # bitrdi: combine s1 and s2
    res = lb.ref(
        "res",
        "∀ x ( φ ↔ ψ ) → ( ∀ x φ ↔ ψ )",
        s1,
        s2,
        ref="bitrdi",
        note="bitrdi albi, 19.3",
    )
    return lb.build(res)


def prove_19_28(sys: System) -> Proof:
    """19.28: ∀ x ( φ ∧ ψ ) ↔ ( φ ∧ ∀ x ψ ).
    Universal quantifier distributes over conjunction when the first
    conjunct does not contain the bound variable.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "19.28")
    hyp = lb.hyp("19.28.1", "Ⅎ x φ")
    # 19.26: ∀ x ( φ ∧ ψ ) ↔ ( ∀ x φ ∧ ∀ x ψ )
    s_19_26 = lb.ref(
        "s_19_26",
        "∀ x ( φ ∧ ψ ) ↔ ( ∀ x φ ∧ ∀ x ψ )",
        ref="19.26",
        note="19.26",
    )
    # 19.3: ∀ x φ ↔ φ
    s_19_3 = lb.ref(
        "s_19_3",
        "∀ x φ ↔ φ",
        hyp,
        ref="19.3",
        note="19.3 19.28.1",
    )
    # bianbi: from 19.26 + 19.3 → goal
    res = lb.ref(
        "res",
        "∀ x ( φ ∧ ψ ) ↔ ( φ ∧ ∀ x ψ )",
        s_19_26,
        s_19_3,
        ref="bianbi",
        note="bianbi 19.26, 19.3",
    )
    return lb.build(res)


def prove_19_27(sys: System) -> Proof:
    """19.27: ∀ x ( φ ∧ ψ ) ↔ ( ∀ x φ ∧ ψ ).
    Distribution of universal quantifier over conjunction when the
    second conjunct does not contain the bound variable (right
    conjunct form).
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "19.27")
    hyp = lb.hyp("19.27.1", "Ⅎ x ψ")
    # 19.26: ∀ x ( φ ∧ ψ ) ↔ ( ∀ x φ ∧ ∀ x ψ )
    s1 = lb.ref(
        "s1",
        "∀ x ( φ ∧ ψ ) ↔ ( ∀ x φ ∧ ∀ x ψ )",
        ref="19.26",
        note="19.26",
    )
    # 19.3: ∀ x ψ ↔ ψ
    s2 = lb.ref(
        "s2",
        "∀ x ψ ↔ ψ",
        hyp,
        ref="19.3",
        note="19.3 19.27.1",
    )
    # anbi2i: ( ∀ x φ ∧ ∀ x ψ ) ↔ ( ∀ x φ ∧ ψ )
    s3 = lb.ref(
        "s3",
        "( ∀ x φ ∧ ∀ x ψ ) ↔ ( ∀ x φ ∧ ψ )",
        s2,
        ref="anbi2i",
        note="anbi2i 19.3",
    )
    # bitri: ∀ x ( φ ∧ ψ ) ↔ ( ∀ x φ ∧ ψ )
    res = lb.ref(
        "res",
        "∀ x ( φ ∧ ψ ) ↔ ( ∀ x φ ∧ ψ )",
        s1,
        s3,
        ref="bitri",
        note="bitri 19.26, anbi2i",
    )
    return lb.build(res)


def prove_19_12(sys: System) -> Proof:
    """19.12: ∃ x ∀ y φ → ∀ y ∃ x φ.
    Commutation of quantifiers: from the existence of a universal
    quantification we can derive a universal existential.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "19.12")
    # nfa1: Ⅎ y ∀ y φ
    s1 = lb.ref(
        "s1",
        "Ⅎ y ∀ y φ",
        ref="nfa1",
        note="nfa1",
    )
    # nfex: Ⅎ y ∀ y φ ⊢ Ⅎ y ∃ x ∀ y φ
    s2 = lb.ref(
        "s2",
        "Ⅎ y ∃ x ∀ y φ",
        s1,
        ref="nfex",
        note="nfex nfa1",
    )
    # sp: ∀ y φ → φ
    s3 = lb.ref(
        "s3",
        "∀ y φ → φ",
        ref="sp",
        note="sp",
    )
    # eximi: (∀ y φ → φ) ⊢ ∃ x ∀ y φ → ∃ x φ
    s4 = lb.ref(
        "s4",
        "∃ x ∀ y φ → ∃ x φ",
        s3,
        ref="eximi",
        note="eximi sp",
    )
    # alrimi: Ⅎ y (∃ x ∀ y φ), (∃ x ∀ y φ → ∃ x φ) ⊢ ∃ x ∀ y φ → ∀ y ∃ x φ
    res = lb.ref(
        "res",
        "∃ x ∀ y φ → ∀ y ∃ x φ",
        s2,
        s4,
        ref="alrimi",
        note="alrimi nfex, eximi",
    )
    return lb.build(res)


def prove_19_21bbi(sys: System) -> Proof:
    """19.21bbi: φ → ψ.
    From 19.21bbi.1 (φ → ∀ x ∀ y ψ) and two applications of
    19.21bi, derive φ → ψ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "19.21bbi")
    hyp = lb.hyp("19.21bbi.1", "φ → ∀ x ∀ y ψ")
    # 19.21bi with ψ substituted by ∀ y ψ: φ → ∀ y ψ
    s1 = lb.ref(
        "s1",
        "φ → ∀ y ψ",
        hyp,
        ref="19.21bi",
        note="19.21bi 19.21bbi.1",
    )
    # 19.21bi with x substituted by y: φ → ψ
    res = lb.ref(
        "res",
        "φ → ψ",
        s1,
        ref="19.21bi",
        note="19.21bi",
    )
    return lb.build(res)


def prove_albid(sys: System) -> Proof:
    """albid: φ → ( ∀ x ψ ↔ ∀ x χ ).
    Deduction form of albi. Uses nf5ri to convert the not-free
    hypothesis into the universal hypothesis needed by albidh.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "albid")
    hyp1 = lb.hyp("albid.1", "Ⅎ x φ")
    hyp2 = lb.hyp("albid.2", "φ → ( ψ ↔ χ )")
    # nf5ri: Ⅎ x φ ⊢ φ → ∀ x φ
    s1 = lb.ref(
        "s1",
        "φ → ∀ x φ",
        hyp1,
        ref="nf5ri",
        note="nf5ri albid.1",
    )
    # albidh: (φ → ∀ x φ), (φ → (ψ ↔ χ)) ⊢ φ → (∀ x ψ ↔ ∀ x χ)
    res = lb.ref(
        "res",
        "φ → ( ∀ x ψ ↔ ∀ x χ )",
        s1,
        hyp2,
        ref="albidh",
        note="albidh nf5ri, albid.2",
    )
    return lb.build(res)


def prove_alimd(sys: System) -> Proof:
    """alimd: φ → ( ∀ x ψ → ∀ x χ ).
    Deduction form of alim. Uses nf5ri to convert the not-free
    hypothesis into the universal hypothesis needed by alimdh.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "alimd")
    hyp1 = lb.hyp("alimd.1", "Ⅎ x φ")
    hyp2 = lb.hyp("alimd.2", "φ → ( ψ → χ )")
    # nf5ri: Ⅎ x φ ⊢ φ → ∀ x φ
    s1 = lb.ref(
        "s1",
        "φ → ∀ x φ",
        hyp1,
        ref="nf5ri",
        note="nf5ri alimd.1",
    )
    # alimdh: (φ → ∀ x φ), (φ → (ψ → χ)) ⊢ φ → (∀ x ψ → ∀ x χ)
    res = lb.ref(
        "res",
        "φ → ( ∀ x ψ → ∀ x χ )",
        s1,
        hyp2,
        ref="alimdh",
        note="alimdh nf5ri, alimd.2",
    )
    return lb.build(res)


def prove_alrimi(sys: System) -> Proof:
    """alrimi: φ → ∀ x ψ.
    Inference form: from Ⅎ x φ and φ → ψ, conclude φ → ∀ x ψ.
    Uses nf5ri to convert the not-free hypothesis to a universal
    hypothesis, then alrimih.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "alrimi")
    hyp1 = lb.hyp("alrimi.1", "Ⅎ x φ")
    hyp2 = lb.hyp("alrimi.2", "φ → ψ")
    # nf5ri: Ⅎ x φ ⊢ φ → ∀ x φ
    s1 = lb.ref(
        "s1",
        "φ → ∀ x φ",
        hyp1,
        ref="nf5ri",
        note="nf5ri alrimi.1",
    )
    # alrimih: (φ → ∀ x φ), (φ → ψ) ⊢ φ → ∀ x ψ
    res = lb.ref(
        "res",
        "φ → ∀ x ψ",
        s1,
        hyp2,
        ref="alrimih",
        note="alrimih nf5ri, alrimi.2",
    )
    return lb.build(res)


def prove_alrimdd(sys: System) -> Proof:
    """alrimdd: φ → (ψ → ∀ x χ).
    Deduction form: from Ⅎ x φ, φ → Ⅎ x ψ, and φ → (ψ → χ),
    conclude φ → (ψ → ∀ x χ).
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "alrimdd")
    h1 = lb.hyp("alrimdd.1", "Ⅎ x φ")
    h2 = lb.hyp("alrimdd.2", "φ → Ⅎ x ψ")
    h3 = lb.hyp("alrimdd.3", "φ → ( ψ → χ )")
    # nf5rd alrimdd.2: φ → (ψ → ∀ x ψ)
    s1 = lb.ref(
        "s1",
        "φ → ( ψ → ∀ x ψ )",
        h2,
        ref="nf5rd",
        note="nf5rd alrimdd.2",
    )
    # alimd alrimdd.1, alrimdd.3: φ → (∀ x ψ → ∀ x χ)
    s2 = lb.ref(
        "s2",
        "φ → ( ∀ x ψ → ∀ x χ )",
        h1,
        h3,
        ref="alimd",
        note="alimd alrimdd.1, alrimdd.3",
    )
    # syld s1, s2: φ → (ψ → ∀ x χ)
    res = lb.ref(
        "res",
        "φ → ( ψ → ∀ x χ )",
        s1,
        s2,
        ref="syld",
        note="syld nf5rd, alimd",
    )
    return lb.build(res)


def prove_alrimd(sys: System) -> Proof:
    """alrimd: φ → (ψ → ∀ x χ).
    Deduction form: from Ⅎ x φ, Ⅎ x ψ, and φ → (ψ → χ),
    conclude φ → (ψ → ∀ x χ).
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "alrimd")
    h1 = lb.hyp("alrimd.1", "Ⅎ x φ")
    h2 = lb.hyp("alrimd.2", "Ⅎ x ψ")
    h3 = lb.hyp("alrimd.3", "φ → ( ψ → χ )")
    # a1i alrimd.2: φ → Ⅎ x ψ
    s1 = lb.ref(
        "s1",
        "φ → Ⅎ x ψ",
        h2,
        ref="a1i",
        note="a1i alrimd.2",
    )
    # alrimdd alrimd.1, s1, alrimd.3: φ → (ψ → ∀ x χ)
    res = lb.ref(
        "res",
        "φ → ( ψ → ∀ x χ )",
        h1,
        s1,
        h3,
        ref="alrimdd",
        note="alrimdd alrimd.1, a1i, alrimd.3",
    )
    return lb.build(res)


def prove_axc4(sys: System) -> Proof:
    """axc4: ∀ x ( ∀ x φ → ψ ) → ( ∀ x φ → ∀ x ψ ).
    Closed form of axc4i.  The proof chains sp, con2i, hbn1, con1i,
    alimi, 3syl, alim, and syl5.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "axc4")
    # sp: ∀ x ¬ ∀ x φ → ¬ ∀ x φ
    s1 = lb.ref(
        "s1",
        "∀ x ¬ ∀ x φ → ¬ ∀ x φ",
        ref="sp",
        note="sp",
    )
    # con2i s1: ∀ x φ → ¬ ∀ x ¬ ∀ x φ
    s2 = lb.ref(
        "s2",
        "∀ x φ → ¬ ∀ x ¬ ∀ x φ",
        s1,
        ref="con2i",
        note="con2i",
    )
    # hbn1: ¬ ∀ x ¬ ∀ x φ → ∀ x ¬ ∀ x ¬ ∀ x φ
    s3 = lb.ref(
        "s3",
        "¬ ∀ x ¬ ∀ x φ → ∀ x ¬ ∀ x ¬ ∀ x φ",
        ref="hbn1",
        note="hbn1",
    )
    # hbn1: ¬ ∀ x φ → ∀ x ¬ ∀ x φ
    s4 = lb.ref(
        "s4",
        "¬ ∀ x φ → ∀ x ¬ ∀ x φ",
        ref="hbn1",
        note="hbn1",
    )
    # con1i s4: ¬ ∀ x ¬ ∀ x φ → ∀ x φ
    s5 = lb.ref(
        "s5",
        "¬ ∀ x ¬ ∀ x φ → ∀ x φ",
        s4,
        ref="con1i",
        note="con1i",
    )
    # alimi s5: ∀ x ¬ ∀ x ¬ ∀ x φ → ∀ x ∀ x φ
    s6 = lb.ref(
        "s6",
        "∀ x ¬ ∀ x ¬ ∀ x φ → ∀ x ∀ x φ",
        s5,
        ref="alimi",
        note="alimi",
    )
    # 3syl s2, s3, s6: ∀ x φ → ∀ x ∀ x φ
    s7 = lb.ref(
        "s7",
        "∀ x φ → ∀ x ∀ x φ",
        s2,
        s3,
        s6,
        ref="3syl",
        note="3syl",
    )
    # alim: ∀ x ( ∀ x φ → ψ ) → ( ∀ x ∀ x φ → ∀ x ψ )
    s8 = lb.ref(
        "s8",
        "∀ x ( ∀ x φ → ψ ) → ( ∀ x ∀ x φ → ∀ x ψ )",
        ref="alim",
        note="alim",
    )
    # syl5 s7, s8: ∀ x ( ∀ x φ → ψ ) → ( ∀ x φ → ∀ x ψ )
    res = lb.ref(
        "res",
        "∀ x ( ∀ x φ → ψ ) → ( ∀ x φ → ∀ x ψ )",
        s7,
        s8,
        ref="syl5",
        note="syl5",
    )
    return lb.build(res)


def prove_axc4i(sys: System) -> Proof:
    """axc4i: ∀ x φ → ∀ x ψ.
    Inference form: from ∀ x φ → ψ conclude ∀ x φ → ∀ x ψ.
    Uses nfa1 to get Ⅎ x ∀ x φ, then alrimi.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "axc4i")
    hyp = lb.hyp("axc4i.1", "∀ x φ → ψ")
    # nfa1: Ⅎ x ∀ x φ
    s1 = lb.ref("s1", "Ⅎ x ∀ x φ", ref="nfa1", note="nfa1")
    # alrimi: (Ⅎ x ∀ x φ), (∀ x φ → ψ) ⊢ ∀ x φ → ∀ x ψ
    res = lb.ref(
        "res",
        "∀ x φ → ∀ x ψ",
        s1,
        hyp,
        ref="alrimi",
        note="alrimi nfa1, axc4i.1",
    )
    return lb.build(res)


def prove_axc7(sys: System) -> Proof:
    """axc7: ¬ ∀ x ¬ ∀ x φ → φ.
    A negated universal of a negated universal reduces to the formula
    itself.  The proof chains sp (∀ x φ → φ) with hbn1
    (¬ ∀ x φ → ∀ x ¬ ∀ x φ) through nsyl4.
    """
    lb = ProofBuilder(sys, "axc7")
    # sp: ∀ x φ → φ
    s1 = lb.ref(
        "s1",
        "∀ x φ → φ",
        ref="sp",
        note="sp",
    )
    # hbn1: ¬ ∀ x φ → ∀ x ¬ ∀ x φ
    s2 = lb.ref(
        "s2",
        "¬ ∀ x φ → ∀ x ¬ ∀ x φ",
        ref="hbn1",
        note="hbn1",
    )
    # nsyl4 with h1=s1, h2=s2: ¬ ∀ x ¬ ∀ x φ → φ
    res = lb.ref(
        "res",
        "¬ ∀ x ¬ ∀ x φ → φ",
        s1,
        s2,
        ref="nsyl4",
        note="nsyl4 sp, hbn1",
    )
    return lb.build(res)


def prove_axc7e(sys: System) -> Proof:
    """axc7e: ∃ x ∀ x φ → φ.
    Existential quantifier of a universally quantified formula implies
    the formula.
    """
    lb = ProofBuilder(sys, "axc7e")
    # hbe1a: ∃ x ∀ x φ → ∀ x φ
    s1 = lb.ref(
        "s1",
        "∃ x ∀ x φ → ∀ x φ",
        ref="hbe1a",
        note="hbe1a",
    )
    # 19.21bi: from φ → ∀ x ψ derive φ → ψ
    res = lb.ref(
        "res",
        "∃ x ∀ x φ → φ",
        s1,
        ref="19.21bi",
        note="19.21bi hbe1a",
    )
    return lb.build(res)


def prove_cbv3(sys: System) -> Proof:
    """cbv3: ∀ x φ → ∀ y ψ.
    Change bound variables in successive universal quantifiers.
    Uses nf5ri and hbal to derive ∀ x φ → ∀ y ∀ x φ from the not-free
    hypothesis Ⅎ y φ, spim to obtain ∀ x φ → ψ, then alrimih to
    generalize the consequent.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "cbv3")
    hyp_nf1 = lb.hyp("cbv3.1", "Ⅎ y φ")
    hyp_nf2 = lb.hyp("cbv3.2", "Ⅎ x ψ")
    hyp_imp = lb.hyp("cbv3.3", "( x = y ) → ( φ → ψ )")
    # nf5ri cbv3.1: φ → ∀ y φ
    s1 = lb.ref(
        "s1",
        "φ → ∀ y φ",
        hyp_nf1,
        ref="nf5ri",
        note="nf5ri cbv3.1",
    )
    # hbal s1: ∀ x φ → ∀ y ∀ x φ
    s2 = lb.ref(
        "s2",
        "∀ x φ → ∀ y ∀ x φ",
        s1,
        ref="hbal",
        note="hbal nf5ri",
    )
    # spim cbv3.2, cbv3.3: ∀ x φ → ψ
    s3 = lb.ref(
        "s3",
        "∀ x φ → ψ",
        hyp_nf2,
        hyp_imp,
        ref="spim",
        note="spim cbv3.2, cbv3.3",
    )
    # alrimih s2, s3: ∀ x φ → ∀ y ψ
    res = lb.ref(
        "res",
        "∀ x φ → ∀ y ψ",
        s2,
        s3,
        ref="alrimih",
        note="alrimih hbal, spim",
    )
    return lb.build(res)


def prove_cbv3h(sys: System) -> Proof:
    """cbv3h: ∀ x φ → ∀ y ψ.
    Hypothesis form of cbv3.  Uses nf5i to derive the not-free
    conditions from cbv3h.1 and cbv3h.2.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "cbv3h")
    hyp_1 = lb.hyp("cbv3h.1", "φ → ∀ y φ")
    hyp_2 = lb.hyp("cbv3h.2", "ψ → ∀ x ψ")
    hyp_3 = lb.hyp("cbv3h.3", "( x = y ) → ( φ → ψ )")
    # nf5i cbv3h.1: Ⅎ y φ
    s1 = lb.ref(
        "s1",
        "Ⅎ y φ",
        hyp_1,
        ref="nf5i",
        note="nf5i cbv3h.1",
    )
    # nf5i cbv3h.2: Ⅎ x ψ
    s2 = lb.ref(
        "s2",
        "Ⅎ x ψ",
        hyp_2,
        ref="nf5i",
        note="nf5i cbv3h.2",
    )
    # cbv3 s1, s2, cbv3h.3: ∀ x φ → ∀ y ψ
    res = lb.ref(
        "res",
        "∀ x φ → ∀ y ψ",
        s1,
        s2,
        hyp_3,
        ref="cbv3",
        note="cbv3 nf5i, nf5i, cbv3h.3",
    )
    return lb.build(res)


def prove_cbv3v(sys: System) -> Proof:
    """cbv3v: ∀ x φ → ∀ y ψ.
    Change bound variables in successive universal quantifiers.
    Uses nf5ri and hbal to derive ∀ x φ → ∀ y ∀ x φ from the not-free
    hypothesis Ⅎ y φ, spimfv to obtain ∀ x φ → ψ, then alrimih to
    generalize the consequent.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "cbv3v")
    hyp_nf1 = lb.hyp("cbv3v.nf1", "Ⅎ y φ")
    hyp_nf2 = lb.hyp("cbv3v.nf2", "Ⅎ x ψ")
    hyp_imp = lb.hyp("cbv3v.1", "( x = y ) → ( φ → ψ )")
    # nf5ri cbv3v.nf1: φ → ∀ y φ
    s1 = lb.ref(
        "s1",
        "φ → ∀ y φ",
        hyp_nf1,
        ref="nf5ri",
        note="nf5ri cbv3v.nf1",
    )
    # hbal s1: ∀ x φ → ∀ y ∀ x φ
    s2 = lb.ref(
        "s2",
        "∀ x φ → ∀ y ∀ x φ",
        s1,
        ref="hbal",
        note="hbal nf5ri",
    )
    # spimfv cbv3v.nf2, cbv3v.1: ∀ x φ → ψ
    s3 = lb.ref(
        "s3",
        "∀ x φ → ψ",
        hyp_nf2,
        hyp_imp,
        ref="spimfv",
        note="spimfv cbv3v.nf2, cbv3v.1",
    )
    # alrimih s2, s3: ∀ x φ → ∀ y ψ
    res = lb.ref(
        "res",
        "∀ x φ → ∀ y ψ",
        s2,
        s3,
        ref="alrimih",
        note="alrimih hbal, spimfv",
    )
    return lb.build(res)


def prove_cbv3v2(sys: System) -> Proof:
    """cbv3v2: ∀ x φ → ∀ y ψ.
    Change bound variables in successive universal quantifiers.
    Uses spimfv to derive ∀ x φ → ψ from the non-free and
    implication hypotheses, then alrimiv to generalize the
    consequent.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "cbv3v2")
    hyp_nf = lb.hyp("cbv3v2.nf", "Ⅎ x ψ")
    hyp_imp = lb.hyp("cbv3v2.1", "( x = y ) → ( φ → ψ )")
    # spimfv cbv3v2.nf, cbv3v2.1: ∀ x φ → ψ
    s1 = lb.ref(
        "s1",
        "∀ x φ → ψ",
        hyp_nf,
        hyp_imp,
        ref="spimfv",
        note="spimfv cbv3v2.nf, cbv3v2.1",
    )
    # alrimiv s1: ∀ x φ → ∀ y ψ
    res = lb.ref(
        "res",
        "∀ x φ → ∀ y ψ",
        s1,
        ref="alrimiv",
        note="alrimiv spimfv",
    )
    return lb.build(res)


def prove_cbv3hv(sys: System) -> Proof:
    """cbv3hv: ∀ x φ → ∀ y ψ.
    Change bound variables in successive universal quantifiers,
    inference form using nf5i and cbv3v.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "cbv3hv")
    hyp_nf1 = lb.hyp("cbv3hv.nf1", "φ → ∀ y φ")
    hyp_nf2 = lb.hyp("cbv3hv.nf2", "ψ → ∀ x ψ")
    hyp_imp = lb.hyp("cbv3hv.1", "( x = y ) → ( φ → ψ )")
    # nf5i cbv3hv.nf1: Ⅎ y φ
    s1 = lb.ref(
        "s1",
        "Ⅎ y φ",
        hyp_nf1,
        ref="nf5i",
        note="nf5i cbv3hv.nf1",
    )
    # nf5i cbv3hv.nf2: Ⅎ x ψ
    s2 = lb.ref(
        "s2",
        "Ⅎ x ψ",
        hyp_nf2,
        ref="nf5i",
        note="nf5i cbv3hv.nf2",
    )
    # cbv3v s1, s2, cbv3hv.1: ∀ x φ → ∀ y ψ
    res = lb.ref(
        "res",
        "∀ x φ → ∀ y ψ",
        s1,
        s2,
        hyp_imp,
        ref="cbv3v",
        note="cbv3v nf5i",
    )
    return lb.build(res)


def prove_sbbid(sys: System) -> Proof:
    """sbbid: φ → ( [ y / x ] ψ ↔ [ y / x ] χ ).
    Deduction form of spsbbi using a not-free hypothesis.
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: wb wal wsb alrimi spsbbi syl.
    """
    lb = ProofBuilder(sys, "sbbid")
    hyp1 = lb.hyp("sbbid.1", "Ⅎ x φ")
    hyp2 = lb.hyp("sbbid.2", "φ → ( ψ ↔ χ )")
    # alrimi: Ⅎ x φ , φ → ( ψ ↔ χ ) ⊢ φ → ∀ x ( ψ ↔ χ )
    s1 = lb.ref(
        "s1",
        "φ → ∀ x ( ψ ↔ χ )",
        hyp1,
        hyp2,
        ref="alrimi",
        note="alrimi",
    )
    # spsbbi: ∀ x ( ψ ↔ χ ) → ( [ y x ψ ↔ [ y x χ )
    s2 = lb.ref(
        "s2",
        "∀ x ( ψ ↔ χ ) → ( [ y x ψ ↔ [ y x χ )",
        ref="spsbbi",
        note="spsbbi",
    )
    # syl: chain s1 and s2
    res = lb.ref(
        "res",
        "φ → ( [ y x ψ ↔ [ y x χ )",
        s1,
        s2,
        ref="syl",
        note="syl alrimi, spsbbi",
    )
    return lb.build(res)


def prove_2sbbid(sys: System) -> Proof:
    """2sbbid: φ → ( [ t / x ] [ u / y ] ψ ↔ [ t / x ] [ u / y ] χ ).
    Double substitution deduction form of spsbbi using not-free hypotheses.
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: wsb sbbid.
    """
    lb = ProofBuilder(sys, "2sbbid")
    hyp1 = lb.hyp("2sbbid.1", "Ⅎ y φ")
    hyp2 = lb.hyp("sbbid.1", "Ⅎ x φ")
    hyp3 = lb.hyp("sbbid.2", "φ → ( ψ ↔ χ )")
    # First sbbid: Ⅎ y φ , φ → ( ψ ↔ χ ) ⊢ φ → ( [ u y ψ ↔ [ u y χ )
    s1 = lb.ref(
        "s1",
        "φ → ( [ u y ψ ↔ [ u y χ )",
        hyp1,
        hyp3,
        ref="sbbid",
        note="sbbid",
    )
    # Second sbbid: Ⅎ x φ , ( φ → ( [ u y ψ ↔ [ u y χ ) ) ⊢ φ → ( [ t x [ u y ψ ↔ [ t x [ u y χ )
    res = lb.ref(
        "res",
        "φ → ( [ t x [ u y ψ ↔ [ t x [ u y χ )",
        hyp2,
        s1,
        ref="sbbid",
        note="sbbid",
    )
    return lb.build(res)


def prove_19_21(sys: System) -> Proof:
    """19.21: ∀ x ( φ → ψ ) ↔ ( φ → ∀ x ψ ).
    Closed form of 19.21t: when φ does not depend on x, universal
    quantification distributes over implication.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "19.21")
    hyp = lb.hyp("19.21.1", "Ⅎ x φ")
    # 19.21t: Ⅎ x φ → ( ∀ x ( φ → ψ ) ↔ ( φ → ∀ x ψ ) )
    s1 = lb.ref(
        "s1",
        "Ⅎ x φ → ( ∀ x ( φ → ψ ) ↔ ( φ → ∀ x ψ ) )",
        ref="19.21t",
        note="19.21t",
    )
    # ax-mp: Ⅎ x φ, 19.21t ⊢ ∀ x ( φ → ψ ) ↔ ( φ → ∀ x ψ )
    res = lb.mp("res", hyp, s1, "ax-mp 19.21t, 19.21.1")
    return lb.build(res)


def prove_19_21h(sys: System) -> Proof:
    """19.21h: ∀ x ( φ → ψ ) ↔ ( φ → ∀ x ψ ).
    Inference form of 19.21: when φ does not depend on x, universal
    quantification distributes over implication.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "19.21h")
    h1 = lb.hyp("19.21h.1", "φ → ∀ x φ")
    s1 = lb.ref("s1", "Ⅎ x φ", h1, ref="nf5i", note="nf5i 19.21h.1")
    res = lb.ref(
        "res",
        "∀ x ( φ → ψ ) ↔ ( φ → ∀ x ψ )",
        s1,
        ref="19.21",
        note="19.21 nf5i",
    )
    return lb.build(res)


def prove_stdpc5(sys: System) -> Proof:
    """stdpc5: ∀ x ( φ → ψ ) → ( φ → ∀ x ψ ).
    If φ does not contain x free, then universal quantification
    distributes over the consequent of an implication.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "stdpc5")
    hyp = lb.hyp("stdpc5.1", "Ⅎ x φ")
    # 19.21 with stdpc5.1: ∀ x ( φ → ψ ) ↔ ( φ → ∀ x ψ )
    s1 = lb.ref(
        "s1",
        "∀ x ( φ → ψ ) ↔ ( φ → ∀ x ψ )",
        hyp,
        ref="19.21",
        note="19.21",
    )
    # biimpi: extract forward implication from biconditional
    res = lb.ref(
        "res",
        "∀ x ( φ → ψ ) → ( φ → ∀ x ψ )",
        s1,
        ref="biimpi",
        note="biimpi",
    )
    return lb.build(res)


def prove_19_21_2(sys: System) -> Proof:
    """19.21-2: ∀ x ∀ y ( φ → ψ ) ↔ ( φ → ∀ x ∀ y ψ ).
    When φ does not depend on x or y, distribute two universal
    quantifiers over implication.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "19.21-2")
    h1 = lb.hyp("19.21-2.1", "Ⅎ x φ")
    h2 = lb.hyp("19.21-2.2", "Ⅎ y φ")
    # 19.21 with y: ∀ y ( φ → ψ ) ↔ ( φ → ∀ y ψ )
    s1 = lb.ref(
        "s1",
        "∀ y ( φ → ψ ) ↔ ( φ → ∀ y ψ )",
        h2,
        ref="19.21",
        note="19.21 with y",
    )
    # albii with x: ∀ x ∀ y ( φ → ψ ) ↔ ∀ x ( φ → ∀ y ψ )
    s2 = lb.ref(
        "s2",
        "∀ x ∀ y ( φ → ψ ) ↔ ∀ x ( φ → ∀ y ψ )",
        s1,
        ref="albii",
        note="albii with x",
    )
    # 19.21 with x and ψ replaced by ∀ y ψ:
    # ∀ x ( φ → ∀ y ψ ) ↔ ( φ → ∀ x ∀ y ψ )
    s3 = lb.ref(
        "s3",
        "∀ x ( φ → ∀ y ψ ) ↔ ( φ → ∀ x ∀ y ψ )",
        h1,
        ref="19.21",
        note="19.21 with x",
    )
    # bitri: chain the two biconditionals
    res = lb.ref(
        "res",
        "∀ x ∀ y ( φ → ψ ) ↔ ( φ → ∀ x ∀ y ψ )",
        s2,
        s3,
        ref="bitri",
        note="bitri albii, 19.21",
    )
    return lb.build(res)


def prove_hb3an(sys: System) -> Proof:
    """hb3an: ( φ ∧ ψ ∧ χ ) → ∀ x ( φ ∧ ψ ∧ χ ).
    From φ → ∀ x φ, ψ → ∀ x ψ, and χ → ∀ x χ conclude that the
    triple conjunction implies its universal generalization.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "hb3an")
    h1 = lb.hyp("hb.1", "φ → ∀ x φ")
    h2 = lb.hyp("hb.2", "ψ → ∀ x ψ")
    h3 = lb.hyp("hb.3", "χ → ∀ x χ")
    # nf5i: φ → ∀ x φ ⊢ Ⅎ x φ
    s1 = lb.ref(
        "s1",
        "Ⅎ x φ",
        h1,
        ref="nf5i",
        note="nf5i hb.1",
    )
    # nf5i: ψ → ∀ x ψ ⊢ Ⅎ x ψ
    s2 = lb.ref(
        "s2",
        "Ⅎ x ψ",
        h2,
        ref="nf5i",
        note="nf5i hb.2",
    )
    # nf5i: χ → ∀ x χ ⊢ Ⅎ x χ
    s3 = lb.ref(
        "s3",
        "Ⅎ x χ",
        h3,
        ref="nf5i",
        note="nf5i hb.3",
    )
    # nf3an: Ⅎ x φ, Ⅎ x ψ, Ⅎ x χ ⊢ Ⅎ x ( φ ∧ ψ ∧ χ )
    s4 = lb.ref(
        "s4",
        "Ⅎ x ( φ ∧ ψ ∧ χ )",
        s1,
        s2,
        s3,
        ref="nf3an",
        note="nf3an s1, s2, s3",
    )
    # nf5ri: Ⅎ x ( φ ∧ ψ ∧ χ ) ⊢ ( φ ∧ ψ ∧ χ ) → ∀ x ( φ ∧ ψ ∧ χ )
    res = lb.ref(
        "res",
        "( φ ∧ ψ ∧ χ ) → ∀ x ( φ ∧ ψ ∧ χ )",
        s4,
        ref="nf5ri",
        note="nf5ri s4",
    )
    return lb.build(res)


def prove_hba1(sys: System) -> Proof:
    """hba1: ∀ x φ → ∀ x ∀ x φ.
    A universally quantified formula implies double universal quantification.
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "hba1")
    # nfa1: Ⅎ x ∀ x φ
    s1 = lb.ref(
        "s1",
        "Ⅎ x ∀ x φ",
        ref="nfa1",
        note="nfa1",
    )
    # nf5ri: Ⅎ x ∀ x φ ⊢ ∀ x φ → ∀ x ∀ x φ
    res = lb.ref(
        "res",
        "∀ x φ → ∀ x ∀ x φ",
        s1,
        ref="nf5ri",
        note="nf5ri nfa1",
    )
    return lb.build(res)


def prove_hbae(sys: System) -> Proof:
    """hbae: ∀ x x = y → ∀ z ∀ x x = y.
    A universally quantified equality implies double universal quantification
    with an outer quantifier.  (Contributed by NM, 13-May-1993.)
    (Proof shortened by Wolf Lammen, 21-Apr-2018.)
    """
    lb = ProofBuilder(sys, "hbae")
    # 1: sp: ∀ x x = y → x = y
    s1 = lb.ref(
        "s1",
        "∀ x x = y → x = y",
        ref="sp",
        note="sp",
    )
    # 2: axc9: ¬ ∀ z z = x → ( ¬ ∀ z z = y → ( x = y → ∀ z x = y ) )
    s2 = lb.ref(
        "s2",
        "¬ ∀ z z = x → ( ¬ ∀ z z = y → ( x = y → ∀ z x = y ) )",
        ref="axc9",
        note="axc9",
    )
    # 3: 1,2:syl7: ¬ ∀ z z = x → ( ¬ ∀ z z = y → ( ∀ x x = y → ∀ z x = y ) )
    s3 = lb.ref(
        "s3",
        "¬ ∀ z z = x → ( ¬ ∀ z z = y → ( ∀ x x = y → ∀ z x = y ) )",
        s1,
        s2,
        ref="syl7",
        note="syl7 sp, axc9",
    )
    # 4: axc11r: ∀ z z = x → ( ∀ x x = y → ∀ z x = y )
    s4 = lb.ref(
        "s4",
        "∀ z z = x → ( ∀ x x = y → ∀ z x = y )",
        ref="axc11r",
        note="axc11r",
    )
    # 5: axc11: ∀ x x = y → ( ∀ x x = y → ∀ y x = y )
    s5 = lb.ref(
        "s5",
        "∀ x x = y → ( ∀ x x = y → ∀ y x = y )",
        ref="axc11",
        note="axc11",
    )
    # 6: 5:pm2.43i: ∀ x x = y → ∀ y x = y
    s6 = lb.ref(
        "s6",
        "∀ x x = y → ∀ y x = y",
        s5,
        ref="pm2.43i",
        note="pm2.43i axc11",
    )
    # 7: axc11r: ∀ z z = y → ( ∀ y x = y → ∀ z x = y )
    s7 = lb.ref(
        "s7",
        "∀ z z = y → ( ∀ y x = y → ∀ z x = y )",
        ref="axc11r",
        note="axc11r",
    )
    # 8: 6,7:syl5: ∀ z z = y → ( ∀ x x = y → ∀ z x = y )
    s8 = lb.ref(
        "s8",
        "∀ z z = y → ( ∀ x x = y → ∀ z x = y )",
        s6,
        s7,
        ref="syl5",
        note="syl5 hbae.6, axc11r",
    )
    # 9: 3,4,8:pm2.61ii: ∀ x x = y → ∀ z x = y
    s9 = lb.ref(
        "s9",
        "∀ x x = y → ∀ z x = y",
        s3,
        s4,
        s8,
        ref="pm2.61ii",
        note="pm2.61ii",
    )
    # 10: 9:axc4i: ∀ x x = y → ∀ x ∀ z x = y
    s10 = lb.ref(
        "s10",
        "∀ x x = y → ∀ x ∀ z x = y",
        s9,
        ref="axc4i",
        note="axc4i",
    )
    # 11: ax-11: ∀ x ∀ z x = y → ∀ z ∀ x x = y
    s11 = lb.ref(
        "s11",
        "∀ x ∀ z x = y → ∀ z ∀ x x = y",
        ref="ax-11",
        note="ax-11",
    )
    # qed: 10,11:syl: ∀ x x = y → ∀ z ∀ x x = y
    res = lb.ref(
        "res",
        "∀ x x = y → ∀ z ∀ x x = y",
        s10,
        s11,
        ref="syl",
        note="syl",
    )
    return lb.build(res)


def prove_nfae(sys: System) -> Proof:
    """nfae: Ⅎ z ∀ x x = y.
    hbae applied through nf5i.  (Contributed by NM, 13-May-1993.)
    """
    lb = ProofBuilder(sys, "nfae")
    # hbae: ∀ x x = y → ∀ z ∀ x x = y
    hbae_step = lb.ref(
        "hbae_step",
        "∀ x x = y → ∀ z ∀ x x = y",
        ref="hbae",
        note="hbae",
    )
    # nf5i hbae: Ⅎ z ∀ x x = y
    res = lb.ref(
        "res",
        "Ⅎ z ∀ x x = y",
        hbae_step,
        ref="nf5i",
        note="nf5i hbae",
    )
    return lb.build(res)


def prove_nfnae(sys: System) -> Proof:
    """nfnae: Ⅎ z ¬ ∀ x x = y.
    nfn applied to nfae.  (Contributed by NM, 13-May-1993.)
    """
    lb = ProofBuilder(sys, "nfnae")
    # nfae: Ⅎ z ∀ x x = y
    nfae_res = lb.ref(
        "nfae_res",
        "Ⅎ z ∀ x x = y",
        ref="nfae",
        note="nfae",
    )
    # nfn nfae: Ⅎ z ¬ ∀ x x = y
    res = lb.ref(
        "res",
        "Ⅎ z ¬ ∀ x x = y",
        nfae_res,
        ref="nfn",
        note="nfn nfae",
    )
    return lb.build(res)


def prove_hbs1(sys: System) -> Proof:
    """hbs1: [ y x φ → ∀ x [ y x φ.
    Substitution to a wff implies universal quantification
    in the bound variable.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "hbs1")
    # nfs1v: Ⅎ x [ y x φ
    s1 = lb.ref(
        "s1",
        "Ⅎ x [ y x φ",
        ref="nfs1v",
        note="nfs1v",
    )
    # nf5ri: Ⅎ x [ y x φ ⊢ [ y x φ → ∀ x [ y x φ
    res = lb.ref(
        "res",
        "[ y x φ → ∀ x [ y x φ",
        s1,
        ref="nf5ri",
        note="nf5ri nfs1v",
    )
    return lb.build(res)


def prove_axial(sys: System) -> Proof:
    """axial: ∀ x φ → ∀ x ∀ x φ.
    Axiom of quantification introduction — alias for hba1.
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "axial")
    res = lb.ref("res", "∀ x φ → ∀ x ∀ x φ", ref="hba1")
    return lb.build(res)


def prove_sbft(sys: System) -> Proof:
    """sbft: Ⅎ x φ → ( [ y x φ ↔ φ ).
    Not-free condition eliminates substitution.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbft")
    # spsbe: [ y x φ → ∃ x φ
    s1 = lb.ref(
        "s1",
        "[ y x φ → ∃ x φ",
        ref="spsbe",
        note="spsbe",
    )
    # 19.9t: Ⅎ x φ → ( ∃ x φ ↔ φ )
    s2 = lb.ref(
        "s2",
        "Ⅎ x φ → ( ∃ x φ ↔ φ )",
        ref="19.9t",
        note="19.9t",
    )
    # imbitrid: Ⅎ x φ → ( [ y x φ → φ )
    s3 = lb.ref(
        "s3",
        "Ⅎ x φ → ( [ y x φ → φ )",
        s1,
        s2,
        ref="imbitrid",
        note="imbitrid spsbe, 19.9t",
    )
    # nf5r: Ⅎ x φ → ( φ → ∀ x φ )
    s4 = lb.ref(
        "s4",
        "Ⅎ x φ → ( φ → ∀ x φ )",
        ref="nf5r",
        note="nf5r",
    )
    # stdpc4: ∀ x φ → [ y x φ
    s5 = lb.ref(
        "s5",
        "∀ x φ → [ y x φ",
        ref="stdpc4",
        note="stdpc4",
    )
    # syl6: Ⅎ x φ → ( φ → [ y x φ )
    s6 = lb.ref(
        "s6",
        "Ⅎ x φ → ( φ → [ y x φ )",
        s4,
        s5,
        ref="syl6",
        note="syl6 nf5r, stdpc4",
    )
    # impbid: Ⅎ x φ → ( [ y x φ ↔ φ )
    res = lb.ref(
        "res",
        "Ⅎ x φ → ( [ y x φ ↔ φ )",
        s3,
        s6,
        ref="impbid",
        note="impbid imbitrid, syl6",
    )
    return lb.build(res)


def prove_sbf(sys: System) -> Proof:
    """sbf: [ y x φ ↔ φ.
    Substitution and not-free: when x is not free in φ, substitution of
    y for x is equivalent to φ itself.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbf")
    h1 = lb.hyp("sbf.1", "Ⅎ x φ")
    s1 = lb.ref(
        "s1",
        "Ⅎ x φ → ( [ y x φ ↔ φ )",
        ref="sbft",
        note="sbft",
    )
    res = lb.mp("res", h1, s1, "MP sbft, hyp1")
    return lb.build(res)


def prove_sbf2(sys: System) -> Proof:
    """sbf2: [ y x ∀ x φ ↔ ∀ x φ.
    Substitution is vacuous when the variable is bound by a universal
    quantifier.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbf2")
    # nfa1: Ⅎ x ∀ x φ
    s1 = lb.ref("s1", "Ⅎ x ∀ x φ", ref="nfa1", note="nfa1")
    # sbf: with φ := ∀ x φ, hypothesis satisfied by nfa1
    res = lb.ref(
        "res",
        "[ y x ∀ x φ ↔ ∀ x φ",
        s1,
        ref="sbf",
        note="sbf nfa1",
    )
    return lb.build(res)


def prove_sb2ae(sys: System) -> Proof:
    """sb2ae: ∀ x x = y → ( [ u / x ] [ v / y ] φ ↔ [ v / y ] φ ).

    When x and y are identical, a substitution for x of a formula already
    substituted for y is equivalent to just the substitution for y.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sb2ae")

    # drsb1: ∀ x x = y → ( [ u / x ] [ v / y ] φ ↔ [ u / y ] [ v / y ] φ )
    s1 = lb.ref(
        "s1",
        "∀ x x = y → ( [ u x [ v y φ ↔ [ u y [ v y φ )",
        ref="drsb1",
        note="drsb1",
    )

    # nfs1v: Ⅎ y [ v / y ] φ
    s2 = lb.ref(
        "s2",
        "Ⅎ y [ v y φ",
        ref="nfs1v",
        note="nfs1v",
    )

    # sbf nfs1v: [ u / y ] [ v / y ] φ ↔ [ v / y ] φ
    s3 = lb.ref(
        "s3",
        "[ u y [ v y φ ↔ [ v y φ",
        s2,
        ref="sbf",
        note="sbf nfs1v",
    )

    # bitrdi drsb1, sbf
    res = lb.ref(
        "res",
        "∀ x x = y → ( [ u x [ v y φ ↔ [ v y φ )",
        s1,
        s3,
        ref="bitrdi",
        note="bitrdi drsb1, sbf",
    )

    return lb.build(res)


def prove_sbrbif(sys: System) -> Proof:
    """sbrbif: ( [ y x ( φ ↔ χ ) ↔ ( ψ ↔ χ ) ).

    Substitution and not-free: when χ is not free in x, substitution of
    a biconditional with the not-free hypothesis yields a biconditional
    without the substitution in the second argument.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wb wsb sbrbis sbf bibi2i bitri.
    """
    lb = ProofBuilder(sys, "sbrbif")
    h1 = lb.hyp("sbrbif.1", "Ⅎ x χ")
    h2 = lb.hyp("sbrbif.2", "( [ y x φ ↔ ψ )")

    # sbrbis with h2: ( [ y x ( φ ↔ χ ) ↔ ( ψ ↔ [ y x χ ) )
    s1 = lb.ref(
        "s1",
        "( [ y x ( φ ↔ χ ) ↔ ( ψ ↔ [ y x χ ) )",
        h2,
        ref="sbrbis",
        note="sbrbis h2",
    )

    # sbf with h1: [ y x χ ↔ χ
    s2 = lb.ref(
        "s2",
        "[ y x χ ↔ χ",
        h1,
        ref="sbf",
        note="sbf h1",
    )

    # bibi2i with s2: ( ( ψ ↔ [ y x χ ) ↔ ( ψ ↔ χ ) )
    s3 = lb.ref(
        "s3",
        "( ( ψ ↔ [ y x χ ) ↔ ( ψ ↔ χ ) )",
        s2,
        ref="bibi2i",
        note="bibi2i sbf",
    )

    # bitri: ( [ y x ( φ ↔ χ ) ↔ ( ψ ↔ χ ) )
    res = lb.ref(
        "res",
        "( [ y x ( φ ↔ χ ) ↔ ( ψ ↔ χ ) )",
        s1,
        s3,
        ref="bitri",
        note="bitri sbrbis, bibi2i",
    )

    return lb.build(res)


def prove_sbrim(sys: System) -> Proof:
    """sbrim: [ y / x ] ( φ → ψ ) ↔ ( φ → [ y / x ] ψ ).
    Substitution distributes over implication with a not-free hypothesis.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbrim")
    symbols = {
        info.local_name: symbol
        for symbol, info in sys.interner.symbol_table().items()
    }
    # Source active DVs: $d t x $. $d t y $. $d ps t $. $d ph t $.
    for left, right in (("t", "x"), ("t", "y"), ("ps", "t"), ("ph", "t")):
        lb.disjoint(symbols[left], symbols[right])
    hyp = lb.hyp("sbrim.1", "Ⅎ x φ")
    s1 = lb.ref(
        "s1",
        "( ( x = t → ( φ → ψ ) ) ↔ ( φ → ( x = t → ψ ) ) )",
        ref="bi2.04",
        note="bi2.04",
    )
    s2 = lb.ref(
        "s2",
        "( ∀ x ( x = t → ( φ → ψ ) ) ↔ ∀ x ( φ → ( x = t → ψ ) ) )",
        s1,
        ref="albii",
        note="albii bi2.04",
    )
    s3 = lb.ref(
        "s3",
        "( ∀ x ( φ → ( x = t → ψ ) ) ↔ ( φ → ∀ x ( x = t → ψ ) ) )",
        hyp,
        ref="19.21",
        note="19.21 sbrim.1",
    )
    s4 = lb.ref(
        "s4",
        "( ∀ x ( x = t → ( φ → ψ ) ) ↔ ( φ → ∀ x ( x = t → ψ ) ) )",
        s2,
        s3,
        ref="bitri",
        note="bitri albii, 19.21",
    )
    s5 = lb.ref(
        "s5",
        "( ( t = y → ∀ x ( x = t → ( φ → ψ ) ) ) ↔ ( t = y → ( φ → ∀ x ( x = t → ψ ) ) ) )",
        s4,
        ref="imbi2i",
        note="imbi2i bitri",
    )
    s6 = lb.ref(
        "s6",
        "( ( t = y → ( φ → ∀ x ( x = t → ψ ) ) ) ↔ ( φ → ( t = y → ∀ x ( x = t → ψ ) ) ) )",
        ref="bi2.04",
        note="bi2.04",
    )
    s7 = lb.ref(
        "s7",
        "( ( t = y → ∀ x ( x = t → ( φ → ψ ) ) ) ↔ ( φ → ( t = y → ∀ x ( x = t → ψ ) ) ) )",
        s5,
        s6,
        ref="bitri",
        note="bitri imbi2i, bi2.04",
    )
    s8 = lb.ref(
        "s8",
        "( ∀ t ( t = y → ∀ x ( x = t → ( φ → ψ ) ) ) ↔ ∀ t ( φ → ( t = y → ∀ x ( x = t → ψ ) ) ) )",
        s7,
        ref="albii",
        note="albii bitri",
    )
    s9 = lb.ref(
        "s9",
        "( [ y x ( φ → ψ ) ↔ ∀ t ( t = y → ∀ x ( x = t → ( φ → ψ ) ) ) )",
        ref="dfsb",
        note="dfsb",
    )
    s10 = lb.ref(
        "s10",
        "( [ y x ψ ↔ ∀ t ( t = y → ∀ x ( x = t → ψ ) ) )",
        ref="dfsb",
        note="dfsb",
    )
    s11 = lb.ref(
        "s11",
        "( ( φ → [ y x ψ ) ↔ ( φ → ∀ t ( t = y → ∀ x ( x = t → ψ ) ) ) )",
        s10,
        ref="imbi2i",
        note="imbi2i dfsb",
    )
    s12 = lb.ref(
        "s12",
        "( ∀ t ( φ → ( t = y → ∀ x ( x = t → ψ ) ) ) ↔ ( φ → ∀ t ( t = y → ∀ x ( x = t → ψ ) ) ) )",
        ref="19.21v",
        note="19.21v",
    )
    s13 = lb.ref(
        "s13",
        "( ( φ → [ y x ψ ) ↔ ∀ t ( φ → ( t = y → ∀ x ( x = t → ψ ) ) ) )",
        s11,
        s12,
        ref="bitr4i",
        note="bitr4i imbi2i, 19.21v",
    )
    res = lb.ref(
        "res",
        "( [ y x ( φ → ψ ) ↔ ( φ → [ y x ψ ) )",
        s8,
        s9,
        s13,
        ref="3bitr4i",
        note="3bitr4i albii, dfsb, bitr4i",
    )
    return lb.build(res)


def prove_sblim(sys: System) -> Proof:
    """sblim: ( [ y / x ] ( φ → ψ ) ↔ ( [ y / x ] φ → ψ ).

    Substitution distributes over implication with a not-free hypothesis
    on the consequent, allowing the substitution to be dropped from the
    consequent.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sblim")

    hyp = lb.hyp("sblim.1", "Ⅎ x ψ")

    # sbim: ( [ y x ( φ → ψ ) ↔ ( [ y x φ → [ y x ψ ) )
    s1 = lb.ref(
        "s1",
        "( [ y x ( φ → ψ ) ↔ ( [ y x φ → [ y x ψ ) )",
        ref="sbim",
        note="sbim",
    )

    # sbf: [ y x ψ ↔ ψ
    s2 = lb.ref(
        "s2",
        "[ y x ψ ↔ ψ",
        hyp,
        ref="sbf",
        note="sbf hyp1",
    )

    # imbi2i s2: ( ( [ y x φ → [ y x ψ ) ↔ ( [ y x φ → ψ ) )
    s3 = lb.ref(
        "s3",
        "( ( [ y x φ → [ y x ψ ) ↔ ( [ y x φ → ψ ) )",
        s2,
        ref="imbi2i",
        note="imbi2i sbf",
    )

    # bitri s1, s3: ( [ y x ( φ → ψ ) ↔ ( [ y x φ → ψ ) )
    res = lb.ref(
        "res",
        "( [ y x ( φ → ψ ) ↔ ( [ y x φ → ψ ) )",
        s1,
        s3,
        ref="bitri",
        note="bitri sbim, imbi2i",
    )

    return lb.build(res)


def prove_sbie(sys: System) -> Proof:
    """sbie: [ y / x ] φ ↔ ψ.

    Proper substitution and implication: from Ⅎ x ψ and the
    substitutional equivalence x = y → ( φ ↔ ψ ), conclude the
    substitutional equivalence [ y / x ] φ ↔ ψ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbie")
    hyp_nf = lb.hyp("sbie.1", "Ⅎ x ψ")
    hyp_eq = lb.hyp("sbie.2", "( x = y → ( φ ↔ ψ ) )")

    # equsb1: [ y / x ] x = y
    s1 = lb.ref(
        "s1",
        "[ y x x = y",
        ref="equsb1",
        note="equsb1",
    )

    # sbimi with sbie.2: ( [ y x x = y → [ y x ( φ ↔ ψ ) )
    s2 = lb.ref(
        "s2",
        "( [ y x x = y → [ y x ( φ ↔ ψ ) )",
        hyp_eq,
        ref="sbimi",
        note="sbimi sbie.2",
    )

    # ax-mp: [ y / x ] ( φ ↔ ψ )
    s3 = lb.mp(
        "s3",
        s1,
        s2,
        note="mp sbimi, equsb1",
    )

    # sbf with sbie.1: [ y / x ] ψ ↔ ψ
    s4 = lb.ref(
        "s4",
        "[ y x ψ ↔ ψ",
        hyp_nf,
        ref="sbf",
        note="sbf sbie.1",
    )

    # sblbis: ( [ y / x ] ( φ ↔ ψ ) ↔ ( [ y / x ] φ ↔ ψ ) )
    s5 = lb.ref(
        "s5",
        "( [ y x ( φ ↔ ψ ) ↔ ( [ y x φ ↔ ψ ) )",
        s4,
        ref="sblbis",
        note="sblbis sbf",
    )

    # mpbi: [ y / x ] φ ↔ ψ
    res = lb.ref(
        "res",
        "[ y x φ ↔ ψ",
        s3,
        s5,
        ref="mpbi",
        note="mpbi mp, sblbis",
    )

    return lb.build(res)


def prove_sbtrt(sys: System) -> Proof:
    """sbtrt: ∀ y [ y x φ → φ.

    If φ holds for all y when y is properly substituted for x, then φ itself
    holds, provided y is not free in φ.
    (Contributed by BJ, 4-Jun-2019.)
    """
    lb = ProofBuilder(sys, "sbtrt")

    hyp = lb.hyp("sbtrt.nf", "Ⅎ y φ")

    # stdpc4: ∀ y [ y / x ] φ → [ x / y ] [ y / x ] φ
    s1 = lb.ref(
        "s1",
        "∀ y [ y x φ → [ x y [ y x φ",
        ref="stdpc4",
        note="stdpc4",
    )

    # sbid2 with the Ⅎ y φ hypothesis:
    #   [ x / y ] [ y / x ] φ ↔ φ
    s2 = lb.ref(
        "s2",
        "[ x y [ y x φ ↔ φ",
        hyp,
        ref="sbid2",
        note="sbid2 sbtrt.nf",
    )

    # sylib: chain φ → ψ and ψ ↔ χ to get φ → χ
    res = lb.ref(
        "res",
        "∀ y [ y x φ → φ",
        s1,
        s2,
        ref="sylib",
        note="sylib stdpc4, sbid2",
    )

    return lb.build(res)


def prove_sbtr(sys: System) -> Proof:
    """sbtr: φ.

    Inference from sbtrt — when [ y / x ] φ and Ⅎ y φ both hold,
    conclude φ.
    """
    lb = ProofBuilder(sys, "sbtr")

    hyp_nf = lb.hyp("sbtr.nf", "Ⅎ y φ")
    hyp_sb = lb.hyp("sbtr.1", "[ y x φ")

    # sbtrt: ∀ y [ y x φ → φ
    s1 = lb.ref(
        "s1",
        "∀ y [ y x φ → φ",
        hyp_nf,
        ref="sbtrt",
        note="sbtrt sbtr.nf",
    )

    # mpg: from ∀ y [ y x φ → φ and [ y x φ, get φ
    res = lb.ref(
        "res",
        "φ",
        s1,
        hyp_sb,
        ref="mpg",
        note="mpg sbtrt, sbtr.1",
    )

    return lb.build(res)


def prove_sbequ5(sys: System) -> Proof:
    """sbequ5: [ w z ∀ x x = y ↔ ∀ x x = y.
    Substitution is vacuous when the variable is bound by nfae.
    (Contributed by NM, 13-May-1993.)
    """
    lb = ProofBuilder(sys, "sbequ5")
    # nfae: Ⅎ z ∀ x x = y
    s1 = lb.ref("s1", "Ⅎ z ∀ x x = y", ref="nfae", note="nfae")
    # sbf with φ := ∀ x x = y
    res = lb.ref(
        "res",
        "[ w z ∀ x x = y ↔ ∀ x x = y",
        s1,
        ref="sbf",
        note="sbf nfae",
    )
    return lb.build(res)


def prove_sbequ6(sys: System) -> Proof:
    """sbequ6: [ w z ¬ ∀ x x = y ↔ ¬ ∀ x x = y.
    Substitution is vacuous when the variable is bound by nfnae.
    (Contributed by NM, 13-May-1993.)
    """
    lb = ProofBuilder(sys, "sbequ6")
    # nfnae: Ⅎ z ¬ ∀ x x = y
    s1 = lb.ref("s1", "Ⅎ z ¬ ∀ x x = y", ref="nfnae", note="nfnae")
    # sbf with φ := ¬ ∀ x x = y
    res = lb.ref(
        "res",
        "[ w z ¬ ∀ x x = y ↔ ¬ ∀ x x = y",
        s1,
        ref="sbf",
        note="sbf nfnae",
    )
    return lb.build(res)


def prove_sbequ8(sys: System) -> Proof:
    """sbequ8: [ y x φ ↔ [ y x ( x = y → φ ).

    Substitution of an implication with equality antecedent yields
    biconditional equivalence.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbequ8")

    # equsb1: [ y x x = y
    s1 = lb.ref(
        "s1",
        "[ y x x = y",
        ref="equsb1",
        note="equsb1",
    )

    # a1bi with hyp from equsb1: [ y x φ ↔ ( [ y x x = y → [ y x φ )
    s2 = lb.ref(
        "s2",
        "[ y x φ ↔ ( [ y x x = y → [ y x φ )",
        s1,
        ref="a1bi",
        note="a1bi equsb1",
    )

    # sbim: [ y x ( x = y → φ ) ↔ ( [ y x x = y → [ y x φ )
    s3 = lb.ref(
        "s3",
        "[ y x ( x = y → φ ) ↔ ( [ y x x = y → [ y x φ )",
        ref="sbim",
        note="sbim",
    )

    # bitr4i from s2 and s3: [ y x φ ↔ [ y x ( x = y → φ )
    res = lb.ref(
        "res",
        "[ y x φ ↔ [ y x ( x = y → φ )",
        s2,
        s3,
        ref="bitr4i",
        note="bitr4i a1bi, sbim",
    )

    return lb.build(res)


def prove_sbh(sys: System) -> Proof:
    """sbh: [ y x φ ↔ φ.
    Substitution when the variable is not free in the formula.
    Hypothesis version of sbf.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbh")
    h1 = lb.hyp("sbh.1", "φ → ∀ x φ")
    # nf5i: from φ → ∀ x φ, derive Ⅎ x φ
    s1 = lb.ref("s1", "Ⅎ x φ", h1, ref="nf5i", note="nf5i")
    # sbf: from Ⅎ x φ, derive [ y x φ ↔ φ
    res = lb.ref(
        "res",
        "[ y x φ ↔ φ",
        s1,
        ref="sbf",
        note="sbf nf5i",
    )
    return lb.build(res)


def prove_sbhb(sys: System) -> Proof:
    """sbhb: ( φ → ∀ x φ ) ↔ ∀ y ( φ → [ y / x ] φ ).

    Equivalence between an implication with a universal quantifier
    and a universally quantified implication with a substitution.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbhb")

    # nfv: Ⅎ y φ
    s_nfv = lb.ref(
        "s_nfv",
        "Ⅎ y φ",
        ref="nfv",
        note="nfv",
    )

    # sb8 nfv: ∀ x φ ↔ ∀ y [ y x φ
    s_sb8 = lb.ref(
        "s_sb8",
        "∀ x φ ↔ ∀ y [ y x φ",
        s_nfv,
        ref="sb8",
        note="sb8 nfv",
    )

    # imbi2i sb8: ( φ → ∀ x φ ) ↔ ( φ → ∀ y [ y x φ )
    s_imbi2i = lb.ref(
        "s_imbi2i",
        "( φ → ∀ x φ ) ↔ ( φ → ∀ y [ y x φ )",
        s_sb8,
        ref="imbi2i",
        note="imbi2i sb8",
    )

    # 19.21v: ∀ y ( φ → [ y x φ ) ↔ ( φ → ∀ y [ y x φ )
    s_19_21v = lb.ref(
        "s_19_21v",
        "∀ y ( φ → [ y x φ ) ↔ ( φ → ∀ y [ y x φ )",
        ref="19.21v",
        note="19.21v",
    )

    # bitr4i imbi2i, 19.21v: ( φ → ∀ x φ ) ↔ ∀ y ( φ → [ y x φ )
    res = lb.ref(
        "res",
        "( φ → ∀ x φ ) ↔ ∀ y ( φ → [ y x φ )",
        s_imbi2i,
        s_19_21v,
        ref="bitr4i",
        note="bitr4i imbi2i, 19.21v",
    )

    return lb.build(res)


def prove_sbid(sys: System) -> Proof:
    """sbid: ( [ x / x ] φ ↔ φ ).
    Substitution of a variable with itself is idempotent.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbid")
    # equid: x = x
    s1 = lb.ref("s1", "x = x", ref="equid", note="equid")
    # sbequ12r with y := x: x = x → ( [ x / x ] φ ↔ φ )
    s2 = lb.ref(
        "s2",
        "x = x → ( [ x x φ ↔ φ )",
        ref="sbequ12r",
        note="sbequ12r with y := x",
    )
    # ax-mp: ( [ x / x ] φ ↔ φ )
    res = lb.mp("res", s1, s2, note="ax-mp")
    return lb.build(res)


def prove_sbidm(sys: System) -> Proof:
    """sbidm: ( [ y / x ] [ y / x ] φ ↔ [ y / x ] φ ).

    Double substitution with the same variable is idempotent.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbidm")

    # sbcom3 with z := y, y := x, x := x:
    # ( [ y / x ] [ x / x ] φ ↔ [ y / x ] [ y / x ] φ )
    s1 = lb.ref(
        "s1",
        "( [ y x [ x x φ ↔ [ y x [ y x φ )",
        ref="sbcom3",
        note="sbcom3",
    )

    # sbid: ( [ x / x ] φ ↔ φ )
    s2 = lb.ref(
        "s2",
        "( [ x x φ ↔ φ )",
        ref="sbid",
        note="sbid",
    )

    # sbbii: ( [ y / x ] [ x / x ] φ ↔ [ y / x ] φ )
    s3 = lb.ref(
        "s3",
        "( [ y x [ x x φ ↔ [ y x φ )",
        s2,
        ref="sbbii",
        note="sbbii",
    )

    # bitr3i: ( [ y / x ] [ y / x ] φ ↔ [ y / x ] φ )
    res = lb.ref(
        "res",
        "( [ y x [ y x φ ↔ [ y x φ )",
        s1,
        s3,
        ref="bitr3i",
        note="bitr3i",
    )

    return lb.build(res)


def prove_sb6(sys: System) -> Proof:
    """sb6: [ t x φ ↔ ∀ x ( x = t → φ ).
    Substitution expressed in terms of universal quantifier
    and implication.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sb6")
    # dfsb: [ t / x ] φ ↔ ∀ y ( y = t → ∀ x ( x = y → φ ) )
    s1 = lb.ref(
        "s1",
        "[ t x φ ↔ ∀ y ( y = t → ∀ x ( x = y → φ ) )",
        ref="dfsb",
        note="dfsb",
    )
    # equequ2: y = t → ( x = y ↔ x = t )
    s2 = lb.ref(
        "s2",
        "y = t → ( x = y ↔ x = t )",
        ref="equequ2",
        note="equequ2",
    )
    # imbi1d: y = t → ( ( x = y → φ ) ↔ ( x = t → φ ) )
    s3 = lb.ref(
        "s3",
        "y = t → ( ( x = y → φ ) ↔ ( x = t → φ ) )",
        s2,
        ref="imbi1d",
        note="imbi1d equequ2",
    )
    # albidv: y = t → ( ∀ x ( x = y → φ ) ↔ ∀ x ( x = t → φ ) )
    s4 = lb.ref(
        "s4",
        "y = t → ( ∀ x ( x = y → φ ) ↔ ∀ x ( x = t → φ ) )",
        s3,
        ref="albidv",
        note="albidv imbi1d",
    )
    # equsalvw: ∀ y ( y = t → ∀ x ( x = y → φ ) ) ↔ ∀ x ( x = t → φ )
    s5 = lb.ref(
        "s5",
        "∀ y ( y = t → ∀ x ( x = y → φ ) ) ↔ ∀ x ( x = t → φ )",
        s4,
        ref="equsalvw",
        note="equsalvw albidv",
    )
    # bitri: [ t / x ] φ ↔ ∀ x ( x = t → φ )
    res = lb.ref(
        "res",
        "[ t x φ ↔ ∀ x ( x = t → φ )",
        s1,
        s5,
        ref="bitri",
        note="bitri dfsb, equsalvw",
    )
    return lb.build(res)


def prove_sb6a(sys: System) -> Proof:
    """sb6a: [ y x φ ↔ ∀ x ( x = y → [ x y φ ).
    Substitution expressed in terms of universal quantifier
    and implication, with variable exchange.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sb6a")
    # sbcov: ( [ y / x ] [ x / y ] φ ↔ [ y / x ] φ )
    s1 = lb.ref(
        "s1",
        "( [ y x [ x y φ ↔ [ y x φ )",
        ref="sbcov",
        note="sbcov",
    )
    # sb6 with [ x / y ] φ substituted for φ:
    # [ y / x ] [ x / y ] φ ↔ ∀ x ( x = y → [ x / y ] φ )
    s2 = lb.ref(
        "s2",
        "[ y x [ x y φ ↔ ∀ x ( x = y → [ x y φ )",
        ref="sb6",
        note="sb6",
    )
    # bitr3i: ( A ↔ B ), ( A ↔ C ) → ( B ↔ C )
    res = lb.ref(
        "res",
        "( [ y x φ ↔ ∀ x ( x = y → [ x y φ ) )",
        s1,
        s2,
        ref="bitr3i",
        note="bitr3i sbcov, sb6",
    )
    return lb.build(res)


def prove_sbievw(sys: System) -> Proof:
    """sbievw: ( [ y / x ] φ ↔ ψ ).
    Weak version of sbiev using sbv instead of the not-free hypothesis.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbievw")
    hyp = lb.hyp("sbievw.is", "x = y → ( φ ↔ ψ )")
    # sbbiiev: ( x = y → ( φ ↔ ψ ) ) → ( [ y / x ] φ ↔ [ y / x ] ψ )
    s1 = lb.ref(
        "s1",
        "( [ y x φ ↔ [ y x ψ )",
        hyp,
        ref="sbbiiev",
        note="sbbiiev",
    )
    # sbv: ( [ y / x ] ψ ↔ ψ )
    s2 = lb.ref(
        "s2",
        "( [ y x ψ ↔ ψ )",
        ref="sbv",
        note="sbv",
    )
    # bitri: ( [ y / x ] φ ↔ ψ )
    res = lb.ref(
        "res",
        "( [ y x φ ↔ ψ )",
        s1,
        s2,
        ref="bitri",
        note="bitri sbbiiev, sbv",
    )
    return lb.build(res)


def prove_sbid2(sys: System) -> Proof:
    """sbid2: ( [ y / x ] [ x / y ] φ ↔ φ ).

    Double substitution with swapped variables, given that x is not free
    in φ.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbid2")

    h1 = lb.hyp("sbid2.1", "Ⅎ x φ")

    # sbco: ( [ y / x ] [ x / y ] φ ↔ [ y / x ] φ )
    s1 = lb.ref(
        "s1",
        "( [ y x [ x y φ ↔ [ y x φ )",
        ref="sbco",
        note="sbco",
    )

    # sbf: ( [ y / x ] φ ↔ φ ), using the hypothesis
    s2 = lb.ref(
        "s2",
        "( [ y x φ ↔ φ )",
        h1,
        ref="sbf",
        note="sbf sbid2.1",
    )

    # bitri: chain the two equivalences
    res = lb.ref(
        "res",
        "( [ y x [ x y φ ↔ φ )",
        s1,
        s2,
        ref="bitri",
        note="bitri sbco, sbf",
    )

    return lb.build(res)


def prove_sbid2v(sys: System) -> Proof:
    """sbid2v: ( [ y / x ] [ x / y ] φ ↔ φ ).

    Variant of sbid2 that uses nfv to eliminate the hypothesis that x
    is not free in φ.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbid2v")
    # nfv: Ⅎ x φ
    h1 = lb.ref("h1", "Ⅎ x φ", ref="nfv", note="nfv")
    # sbid2: ( [ y / x ] [ x / y ] φ ↔ φ )
    res = lb.ref(
        "res",
        "( [ y x [ x y φ ↔ φ )",
        h1,
        ref="sbid2",
        note="sbid2 nfv",
    )
    return lb.build(res)


def prove_sbid2vw(sys: System) -> Proof:
    """sbid2vw: ( [ t / x ] [ x / t ] φ ↔ φ ).
    Equivalence of double substitution with swapped variables.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbid2vw")
    # sbequ12r: x = t → ( [ x / t ] φ ↔ φ )
    s1 = lb.ref(
        "s1",
        "x = t → ( [ x t φ ↔ φ )",
        ref="sbequ12r",
        note="sbequ12r",
    )
    # sbievw(s1): ( [ t / x ] [ x / t ] φ ↔ φ )
    res = lb.ref(
        "res",
        "( [ t x [ x t φ ↔ φ )",
        s1,
        ref="sbievw",
        note="sbievw",
    )
    return lb.build(res)


def prove_sbcovOLD(sys: System) -> Proof:
    """sbcovOLD: [ y / x ] [ x / y ] φ ↔ [ y / x ] φ.
    Substitution commutation of swapped variables with the same outer
    substituting variable.
    """
    lb = ProofBuilder(sys, "sbcovOLD")
    # sbcom3vv: ( [ y / x ] [ x / y ] φ ↔ [ y / x ] [ y / y ] φ )
    s1 = lb.ref(
        "s1",
        "( [ y x [ x y φ ↔ [ y x [ y y φ )",
        ref="sbcom3vv",
        note="sbcom3vv",
    )
    # sbid: ( [ y / y ] φ ↔ φ )
    s2 = lb.ref(
        "s2",
        "( [ y y φ ↔ φ )",
        ref="sbid",
        note="sbid",
    )
    # sbbii(s2): ( [ y / x ] [ y / y ] φ ↔ [ y / x ] φ )
    s3 = lb.ref(
        "s3",
        "( [ y x [ y y φ ↔ [ y x φ )",
        s2,
        ref="sbbii",
        note="sbbii",
    )
    # bitri: ( [ y / x ] [ x / y ] φ ↔ [ y / x ] φ )
    res = lb.ref(
        "res",
        "( [ y x [ x y φ ↔ [ y x φ )",
        s1,
        s3,
        ref="bitri",
        note="bitri sbcom3vv, sbbii",
    )
    return lb.build(res)


def prove_sbievwOLD(sys: System) -> Proof:
    """sbievwOLD: [ y x φ ↔ ψ.
    Version of sbievw with a disjoint variable condition, requiring fewer
    axioms.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbievwOLD")
    hyp = lb.hyp("sbievw.is", "x = y → ( φ ↔ ψ )")
    # sb6: [ y / x ] φ ↔ ∀ x ( x = y → φ )
    s1 = lb.ref(
        "s1",
        "[ y x φ ↔ ∀ x ( x = y → φ )",
        ref="sb6",
        note="sb6",
    )
    # equsalvw: ∀ x ( x = y → φ ) ↔ ψ
    s2 = lb.ref(
        "s2",
        "∀ x ( x = y → φ ) ↔ ψ",
        hyp,
        ref="equsalvw",
        note="equsalvw",
    )
    # bitri: [ y / x ] φ ↔ ψ
    res = lb.ref(
        "res",
        "[ y x φ ↔ ψ",
        s1,
        s2,
        ref="bitri",
        note="bitri sb6, equsalvw",
    )
    return lb.build(res)


def prove_sbievw2(sys: System) -> Proof:
    """sbievw2: ( [ y / x ] φ ↔ ψ ).
    sbievw applied twice, avoiding a DV condition on x, y.
    (Contributed by Steven Nguyen, 29-Jul-2023.)
    """
    lb = ProofBuilder(sys, "sbievw2")
    hyp1 = lb.hyp("sbievw2.1", "( x = w → ( φ ↔ χ ) )")
    hyp2 = lb.hyp("sbievw2.2", "( w = y → ( χ ↔ ψ ) )")
    # sbcom3vv: ( [ y / w ] [ w / x ] φ ↔ [ y / w ] [ y / x ] φ )
    s1 = lb.ref(
        "s1",
        "( [ y w [ w x φ ↔ [ y w [ y x φ )",
        ref="sbcom3vv",
        note="sbcom3vv",
    )
    # sbievw(hyp1): ( [ w / x ] φ ↔ χ )
    s3 = lb.ref(
        "s3",
        "( [ w x φ ↔ χ )",
        hyp1,
        ref="sbievw",
        note="sbievw",
    )
    # sbbii(s3): ( [ y / w ] [ w / x ] φ ↔ [ y / w ] χ )
    s4 = lb.ref(
        "s4",
        "( [ y w [ w x φ ↔ [ y w χ )",
        s3,
        ref="sbbii",
        note="sbbii",
    )
    # sbv: ( [ y / w ] [ y / x ] φ ↔ [ y / x ] φ )
    s5 = lb.ref(
        "s5",
        "( [ y w [ y x φ ↔ [ y x φ )",
        ref="sbv",
        note="sbv",
    )
    # 3bitr3i(s1, s4, s5): ( [ y / w ] χ ↔ [ y / x ] φ )
    s6 = lb.ref(
        "s6",
        "( [ y w χ ↔ [ y x φ )",
        s1,
        s4,
        s5,
        ref="3bitr3i",
        note="3bitr3i sbcom3vv, sbbii, sbv",
    )
    # sbievw(hyp2): ( [ y / w ] χ ↔ ψ )
    s8 = lb.ref(
        "s8",
        "( [ y w χ ↔ ψ )",
        hyp2,
        ref="sbievw",
        note="sbievw",
    )
    # bitr3i(s6, s8): ( [ y / x ] φ ↔ ψ )
    res = lb.ref(
        "res",
        "( [ y x φ ↔ ψ )",
        s6,
        s8,
        ref="bitr3i",
        note="bitr3i 3bitr3i, sbievw",
    )
    return lb.build(res)


def prove_sbiedvw(sys: System) -> Proof:
    """sbiedvw: φ → ( [ y x ψ ↔ χ ).
    Weak version of sbiedv using sbv instead of the not-free hypothesis.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbiedvw")
    hyp = lb.hyp("sbiedvw.1", "( ( φ ∧ x = y ) → ( ψ ↔ χ ) )")
    # expcom: x = y → ( φ → ( ψ ↔ χ ) )
    s1 = lb.ref(
        "s1",
        "( x = y → ( φ → ( ψ ↔ χ ) ) )",
        hyp,
        ref="expcom",
        note="expcom",
    )
    # pm5.74d: x = y → ( ( φ → ψ ) ↔ ( φ → χ ) )
    s2 = lb.ref(
        "s2",
        "( x = y → ( ( φ → ψ ) ↔ ( φ → χ ) ) )",
        s1,
        ref="pm5.74d",
        note="pm5.74d",
    )
    # sbievw: [ y x ( φ → ψ ) ↔ ( φ → χ )
    s3 = lb.ref(
        "s3",
        "( [ y x ( φ → ψ ) ↔ ( φ → χ ) )",
        s2,
        ref="sbievw",
        note="sbievw",
    )
    # sbrimvw: [ y x ( φ → ψ ) ↔ ( φ → [ y x ψ )
    s4 = lb.ref(
        "s4",
        "( [ y x ( φ → ψ ) ↔ ( φ → [ y x ψ ) )",
        ref="sbrimvw",
        note="sbrimvw",
    )
    # bitr3i: ( φ → [ y x ψ ) ↔ ( φ → χ )
    s5 = lb.ref(
        "s5",
        "( ( φ → [ y x ψ ) ↔ ( φ → χ ) )",
        s4,
        s3,
        ref="bitr3i",
        note="bitr3i",
    )
    # pm5.74ri: φ → ( [ y x ψ ↔ χ )
    res = lb.ref(
        "res",
        "( φ → ( [ y x ψ ↔ χ ) )",
        s5,
        ref="pm5.74ri",
        note="pm5.74ri",
    )
    return lb.build(res)


def prove_2sbiev(sys: System) -> Proof:
    """2sbiev: [ t / x ] [ u / y ] φ ↔ ψ.

    Double substitution equivalent in terms of the hypothesis
    ( ( x = t ∧ y = u ) → ( φ ↔ ψ ) ).
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "2sbiev")
    hyp = lb.hyp("2sbiev.1", "( ( x = t ∧ y = u ) → ( φ ↔ ψ ) )")
    # sbiedv: ( x = t → ( [ u / y ] φ ↔ ψ ) )
    s1 = lb.ref(
        "s1",
        "( x = t → ( [ u y φ ↔ ψ ) )",
        hyp,
        ref="sbiedv",
        note="sbiedv",
    )
    # nfv: Ⅎ x ψ
    s_nf = lb.ref(
        "s_nf",
        "Ⅎ x ψ",
        ref="nfv",
        note="nfv",
    )
    # sbie: [ t / x ] [ u / y ] φ ↔ ψ
    res = lb.ref(
        "res",
        "( [ t x [ u y φ ↔ ψ )",
        s_nf,
        s1,
        ref="sbie",
        note="sbie",
    )
    return lb.build(res)


def prove_2sbievw(sys: System) -> Proof:
    """2sbievw: [ t x [ u y φ ↔ ψ.
    Double substitution equivalent in terms of the hypothesis
    ( ( x = t ∧ y = u ) → ( φ ↔ ψ ) ).
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "2sbievw")
    hyp = lb.hyp("2sbievw.1", "( ( x = t ∧ y = u ) → ( φ ↔ ψ ) )")
    # sbiedvw: ( x = t ) → ( [ u / y ] φ ↔ ψ )
    s1 = lb.ref(
        "s1",
        "( x = t → ( [ u y φ ↔ ψ ) )",
        hyp,
        ref="sbiedvw",
        note="sbiedvw",
    )
    # sbievw: [ t / x ] [ u / y ] φ ↔ ψ
    res = lb.ref(
        "res",
        "( [ t x [ u y φ ↔ ψ )",
        s1,
        ref="sbievw",
        note="sbievw",
    )
    return lb.build(res)


def prove_nfs1v(sys: System) -> Proof:
    """nfs1v: Ⅎ x [ y x φ.
    x is not free in the proper substitution of y for x in φ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "nfs1v")
    # sb6: [ y / x ] φ ↔ ∀ x ( x = y → φ )
    s1 = lb.ref(
        "s1",
        "[ y x φ ↔ ∀ x ( x = y → φ )",
        ref="sb6",
        note="sb6",
    )
    # nfa1: Ⅎ x ∀ x ( x = y → φ )
    s2 = lb.ref(
        "s2",
        "Ⅎ x ∀ x ( x = y → φ )",
        ref="nfa1",
        note="nfa1",
    )
    # nfxfr: Ⅎ x [ y x φ
    res = lb.ref(
        "res",
        "Ⅎ x [ y x φ",
        s1,
        s2,
        ref="nfxfr",
        note="nfxfr sb6, nfa1",
    )
    return lb.build(res)


def prove_sbievOLD(sys: System) -> Proof:
    """sbievOLD: [ y x φ ↔ ψ.
    Version of sbiev with a disjoint variable condition, requiring fewer
    axioms.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbievOLD")
    hyp1 = lb.hyp("sbiev.1", "Ⅎ x ψ")
    hyp2 = lb.hyp("sbiev.2", "x = y → ( φ ↔ ψ )")
    # sb6: [ y x φ ↔ ∀ x ( x = y → φ )
    s1 = lb.ref(
        "s1",
        "[ y x φ ↔ ∀ x ( x = y → φ )",
        ref="sb6",
        note="sb6",
    )
    # equsalv: ∀ x ( x = y → φ ) ↔ ψ
    s2 = lb.ref(
        "s2",
        "∀ x ( x = y → φ ) ↔ ψ",
        hyp1,
        hyp2,
        ref="equsalv",
        note="equsalv sbiev.1, sbiev.2",
    )
    # bitri: [ y x φ ↔ ψ
    res = lb.ref(
        "res",
        "[ y x φ ↔ ψ",
        s1,
        s2,
        ref="bitri",
        note="bitri sb6, equsalv",
    )
    return lb.build(res)


def prove_sbrimvwOLD(sys: System) -> Proof:
    """sbrimvwOLD: [ y x ( φ → ψ ) ↔ ( φ → [ y x ψ ).
    Substitution moves an antecedent in and out of a substitution.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbrimvwOLD")
    # sb6: [ y x ( φ → ψ ) ↔ ∀ x ( x = y → ( φ → ψ ) )
    s_sb6_imp = lb.ref(
        "s_sb6_imp",
        "[ y x ( φ → ψ ) ↔ ∀ x ( x = y → ( φ → ψ ) )",
        ref="sb6",
        note="sb6",
    )
    # bi2.04: ( φ → ( x = y → ψ ) ) ↔ ( x = y → ( φ → ψ ) )
    s_bi204 = lb.ref(
        "s_bi204",
        "( φ → ( x = y → ψ ) ) ↔ ( x = y → ( φ → ψ ) )",
        ref="bi2.04",
        note="bi2.04",
    )
    # albii s_bi204: ∀ x ( φ → ( x = y → ψ ) ) ↔ ∀ x ( x = y → ( φ → ψ ) )
    s_albii = lb.ref(
        "s_albii",
        "∀ x ( φ → ( x = y → ψ ) ) ↔ ∀ x ( x = y → ( φ → ψ ) )",
        s_bi204,
        ref="albii",
        note="albii bi2.04",
    )
    # 19.21v: ∀ x ( φ → ( x = y → ψ ) ) ↔ ( φ → ∀ x ( x = y → ψ ) )
    s_19_21v = lb.ref(
        "s_19_21v",
        "∀ x ( φ → ( x = y → ψ ) ) ↔ ( φ → ∀ x ( x = y → ψ ) )",
        ref="19.21v",
        note="19.21v",
    )
    # 3bitr2i: [ y x ( φ → ψ ) ↔ ( φ → ∀ x ( x = y → ψ ) )
    s_3bitr2i = lb.ref(
        "s_3bitr2i",
        "[ y x ( φ → ψ ) ↔ ( φ → ∀ x ( x = y → ψ ) )",
        s_sb6_imp,
        s_albii,
        s_19_21v,
        ref="3bitr2i",
        note="3bitr2i sb6, albii, 19.21v",
    )
    # sb6: [ y x ψ ↔ ∀ x ( x = y → ψ )
    s_sb6_psi = lb.ref(
        "s_sb6_psi",
        "[ y x ψ ↔ ∀ x ( x = y → ψ )",
        ref="sb6",
        note="sb6",
    )
    # imbi2i s_sb6_psi: ( φ → [ y x ψ ) ↔ ( φ → ∀ x ( x = y → ψ ) )
    s_imbi2i = lb.ref(
        "s_imbi2i",
        "( φ → [ y x ψ ) ↔ ( φ → ∀ x ( x = y → ψ ) )",
        s_sb6_psi,
        ref="imbi2i",
        note="imbi2i sb6",
    )
    # bitr4i: [ y x ( φ → ψ ) ↔ ( φ → [ y x ψ ) )
    res = lb.ref(
        "res",
        "[ y x ( φ → ψ ) ↔ ( φ → [ y x ψ )",
        s_3bitr2i,
        s_imbi2i,
        ref="bitr4i",
        note="bitr4i 3bitr2i, imbi2i",
    )
    return lb.build(res)


def prove_sb6f(sys: System) -> Proof:
    """sb6f: [ y x φ ↔ ∀ x ( x = y → φ ).
    Substitution with a non-freeness condition on the
    substitution variable.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sb6f")
    hyp = lb.hyp("sb6f.1", "Ⅎ y φ")
    # nf5ri: φ → ∀ y φ
    s1 = lb.ref(
        "s1",
        "φ → ∀ y φ",
        hyp,
        ref="nf5ri",
        note="nf5ri sb6f.1",
    )
    # sbimi: [ y / x ] φ → [ y / x ] ∀ y φ
    s2 = lb.ref(
        "s2",
        "( [ y x φ → [ y x ∀ y φ )",
        s1,
        ref="sbimi",
        note="sbimi nf5ri",
    )
    # sb4a: [ y / x ] ∀ y φ → ∀ x ( x = y → φ )
    s3 = lb.ref(
        "s3",
        "( [ y x ∀ y φ → ∀ x ( x = y → φ ) )",
        ref="sb4a",
        note="sb4a",
    )
    # syl: [ y / x ] φ → ∀ x ( x = y → φ )
    s4 = lb.ref(
        "s4",
        "( [ y x φ → ∀ x ( x = y → φ ) )",
        s2,
        s3,
        ref="syl",
        note="syl sbimi, sb4a",
    )
    # sb2: ∀ x ( x = y → φ ) → [ y / x ] φ
    s5 = lb.ref(
        "s5",
        "∀ x ( x = y → φ ) → [ y x φ",
        ref="sb2",
        note="sb2",
    )
    # impbii: [ y / x ] φ ↔ ∀ x ( x = y → φ )
    res = lb.ref(
        "res",
        "( [ y x φ ↔ ∀ x ( x = y → φ ) )",
        s4,
        s5,
        ref="impbii",
        note="impbii syl, sb2",
    )
    return lb.build(res)


def prove_sb5f(sys: System) -> Proof:
    """sb5f: [ y / x ] φ ↔ ∃ x ( x = y ∧ φ ).

    Substitution with a non-freeness condition on the substituted
    variable, expressed in terms of existential quantifier and
    conjunction.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sb5f")
    hyp = lb.hyp("sb5f.1", "Ⅎ y φ")
    # sb6f: [ y / x ] φ ↔ ∀ x ( x = y → φ )
    s1 = lb.ref(
        "s1",
        "( [ y x φ ↔ ∀ x ( x = y → φ ) )",
        hyp,
        ref="sb6f",
        note="sb6f sb5f.1",
    )
    # equs45f: ∃ x ( x = y ∧ φ ) ↔ ∀ x ( x = y → φ )
    s2 = lb.ref(
        "s2",
        "∃ x ( x = y ∧ φ ) ↔ ∀ x ( x = y → φ )",
        hyp,
        ref="equs45f",
        note="equs45f sb5f.1",
    )
    # bitr4i: [ y / x ] φ ↔ ∃ x ( x = y ∧ φ )
    res = lb.ref(
        "res",
        "( [ y x φ ↔ ∃ x ( x = y ∧ φ ) )",
        s1,
        s2,
        ref="bitr4i",
        note="bitr4i sb6f, equs45f",
    )
    return lb.build(res)


def prove_sb6x(sys: System) -> Proof:
    """sb6x: [ y x φ ↔ ∀ x ( x = y → φ ).
    Substitution expressed in terms of implication and quantifier.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sb6x")
    hyp = lb.hyp("sb6x.1", "Ⅎ x φ")
    # sbf: [ y / x ] φ ↔ φ
    s1 = lb.ref(
        "s1",
        "[ y x φ ↔ φ",
        hyp,
        ref="sbf",
        note="sbf sb6x.1",
    )
    # biidd: x = y → ( φ ↔ φ )
    s2 = lb.ref(
        "s2",
        "x = y → ( φ ↔ φ )",
        ref="biidd",
        note="biidd",
    )
    # equsal: ∀ x ( x = y → φ ) ↔ φ
    s3 = lb.ref(
        "s3",
        "∀ x ( x = y → φ ) ↔ φ",
        hyp,
        s2,
        ref="equsal",
        note="equsal sb6x.1, biidd",
    )
    # bitr4i: [ y / x ] φ ↔ ∀ x ( x = y → φ )
    res = lb.ref(
        "res",
        "[ y x φ ↔ ∀ x ( x = y → φ )",
        s1,
        s3,
        ref="bitr4i",
        note="bitr4i sbf, equsal",
    )
    return lb.build(res)


def prove_2sb5(sys: System) -> Proof:
    """2sb5: [ z x [ w y φ ↔ ∃ x ∃ y ( ( x = z ∧ y = w ) ∧ φ ).
    Double substitution expressed in terms of existential quantifiers and
    conjunction.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "2sb5")
    # sb5: [ z / x ] [ w / y ] φ ↔ ∃ x ( x = z ∧ [ w / y ] φ )
    s1 = lb.ref(
        "s1",
        "[ z x [ w y φ ↔ ∃ x ( x = z ∧ [ w y φ )",
        ref="sb5",
        note="sb5",
    )
    # sb5: [ w / y ] φ ↔ ∃ y ( y = w ∧ φ )
    s2 = lb.ref(
        "s2",
        "[ w y φ ↔ ∃ y ( y = w ∧ φ )",
        ref="sb5",
        note="sb5",
    )
    # anbi2i: ( x = z ∧ [ w / y ] φ ) ↔ ( x = z ∧ ∃ y ( y = w ∧ φ ) )
    s3 = lb.ref(
        "s3",
        "( x = z ∧ [ w y φ ) ↔ ( x = z ∧ ∃ y ( y = w ∧ φ ) )",
        s2,
        ref="anbi2i",
        note="anbi2i sb5",
    )
    # anass: ( ( x = z ∧ y = w ) ∧ φ ) ↔ ( x = z ∧ ( y = w ∧ φ ) )
    s4 = lb.ref(
        "s4",
        "( ( x = z ∧ y = w ) ∧ φ ) ↔ ( x = z ∧ ( y = w ∧ φ ) )",
        ref="anass",
        note="anass",
    )
    # exbii: ∃ y ( ( x = z ∧ y = w ) ∧ φ ) ↔ ∃ y ( x = z ∧ ( y = w ∧ φ ) )
    s5 = lb.ref(
        "s5",
        "∃ y ( ( x = z ∧ y = w ) ∧ φ ) ↔ ∃ y ( x = z ∧ ( y = w ∧ φ ) )",
        s4,
        ref="exbii",
        note="exbii anass",
    )
    # 19.42v: ∃ y ( x = z ∧ ( y = w ∧ φ ) ) ↔ ( x = z ∧ ∃ y ( y = w ∧ φ ) )
    s6 = lb.ref(
        "s6",
        "∃ y ( x = z ∧ ( y = w ∧ φ ) ) ↔ ( x = z ∧ ∃ y ( y = w ∧ φ ) )",
        ref="19.42v",
        note="19.42v",
    )
    # 3bitr4ri: ( x = z ∧ [ w / y ] φ ) ↔ ∃ y ( ( x = z ∧ y = w ) ∧ φ )
    s7 = lb.ref(
        "s7",
        "( x = z ∧ [ w y φ ) ↔ ∃ y ( ( x = z ∧ y = w ) ∧ φ )",
        s6,
        s5,
        s3,
        ref="3bitr4ri",
        note="3bitr4ri 19.42v, exbii, anbi2i",
    )
    # exbii: ∃ x ( x = z ∧ [ w / y ] φ ) ↔ ∃ x ∃ y ( ( x = z ∧ y = w ) ∧ φ )
    s8 = lb.ref(
        "s8",
        "∃ x ( x = z ∧ [ w y φ ) ↔ ∃ x ∃ y ( ( x = z ∧ y = w ) ∧ φ )",
        s7,
        ref="exbii",
        note="exbii 3bitr4ri",
    )
    # bitri: [ z / x ] [ w / y ] φ ↔ ∃ x ∃ y ( ( x = z ∧ y = w ) ∧ φ )
    res = lb.ref(
        "res",
        "[ z x [ w y φ ↔ ∃ x ∃ y ( ( x = z ∧ y = w ) ∧ φ )",
        s1,
        s8,
        ref="bitri",
        note="bitri sb5, exbii",
    )
    return lb.build(res)


def prove_2sb6(sys: System) -> Proof:
    """2sb6: [ z x [ w y φ ↔ ∀ x ∀ y ( ( x = z ∧ y = w ) → φ ).
    Double substitution expressed in terms of universal quantifiers
    and implication.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "2sb6")
    # sb6: [ z / x ] [ w / y ] φ ↔ ∀ x ( x = z → [ w / y ] φ )
    s1 = lb.ref(
        "s1",
        "[ z x [ w y φ ↔ ∀ x ( x = z → [ w y φ )",
        ref="sb6",
        note="sb6",
    )
    # 19.21v: ∀ y ( x = z → ( y = w → φ ) ) ↔ ( x = z → ∀ y ( y = w → φ ) )
    s2 = lb.ref(
        "s2",
        "∀ y ( x = z → ( y = w → φ ) ) ↔ ( x = z → ∀ y ( y = w → φ ) )",
        ref="19.21v",
        note="19.21v",
    )
    # impexp: ( ( x = z ∧ y = w ) → φ ) ↔ ( x = z → ( y = w → φ ) )
    s3 = lb.ref(
        "s3",
        "( ( x = z ∧ y = w ) → φ ) ↔ ( x = z → ( y = w → φ ) )",
        ref="impexp",
        note="impexp",
    )
    # albii s3: ∀ y ( ( x = z ∧ y = w ) → φ ) ↔ ∀ y ( x = z → ( y = w → φ ) )
    s4 = lb.ref(
        "s4",
        "∀ y ( ( x = z ∧ y = w ) → φ ) ↔ ∀ y ( x = z → ( y = w → φ ) )",
        s3,
        ref="albii",
        note="albii impexp",
    )
    # sb6: [ w / y ] φ ↔ ∀ y ( y = w → φ )
    s5 = lb.ref(
        "s5",
        "[ w y φ ↔ ∀ y ( y = w → φ )",
        ref="sb6",
        note="sb6",
    )
    # imbi2i s5: ( x = z → [ w / y ] φ ) ↔ ( x = z → ∀ y ( y = w → φ ) )
    s6 = lb.ref(
        "s6",
        "( x = z → [ w y φ ) ↔ ( x = z → ∀ y ( y = w → φ ) )",
        s5,
        ref="imbi2i",
        note="imbi2i sb6",
    )
    # 3bitr4ri s2, s4, s6: ( x = z → [ w / y ] φ ) ↔ ∀ y ( ( x = z ∧ y = w ) → φ )
    s7 = lb.ref(
        "s7",
        "( x = z → [ w y φ ) ↔ ∀ y ( ( x = z ∧ y = w ) → φ )",
        s2,
        s4,
        s6,
        ref="3bitr4ri",
        note="3bitr4ri 19.21v, albii, imbi2i",
    )
    # albii s7: ∀ x ( x = z → [ w / y ] φ ) ↔ ∀ x ∀ y ( ( x = z ∧ y = w ) → φ )
    s8 = lb.ref(
        "s8",
        "∀ x ( x = z → [ w y φ ) ↔ ∀ x ∀ y ( ( x = z ∧ y = w ) → φ )",
        s7,
        ref="albii",
        note="albii 3bitr4ri",
    )
    # bitri s1, s8: [ z / x ] [ w / y ] φ ↔ ∀ x ∀ y ( ( x = z ∧ y = w ) → φ )
    res = lb.ref(
        "res",
        "[ z x [ w y φ ↔ ∀ x ∀ y ( ( x = z ∧ y = w ) → φ )",
        s1,
        s8,
        ref="bitri",
        note="bitri sb6, albii",
    )
    return lb.build(res)


def prove_moan(sys: System) -> Proof:
    """moan: ( ∃* x φ → ∃* x ( ψ ∧ φ ) ).
    Adding a conjunct to the body of an "at most one" quantifier
    preserves the quantifier.  Given that there is at most one x
    such that φ, there is also at most one x such that ψ ∧ φ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "moan")
    # ancom: ( φ ∧ ψ ) ↔ ( ψ ∧ φ )
    s_ancom = lb.ref(
        "s_ancom",
        "( φ ∧ ψ ) ↔ ( ψ ∧ φ )",
        ref="ancom",
        note="ancom",
    )
    # biimpri: forward direction of reversed ancom → ( ψ ∧ φ ) → ( φ ∧ ψ )
    s_ancom_rev = lb.ref(
        "s_ancom_rev",
        "( ψ ∧ φ ) → ( φ ∧ ψ )",
        s_ancom,
        ref="biimpri",
        note="biimpri ancom",
    )
    # simpl: ( φ ∧ ψ ) → φ
    s_simpl = lb.ref(
        "s_simpl",
        "( φ ∧ ψ ) → φ",
        ref="simpl",
        note="simpl",
    )
    # syl: chain ( ψ ∧ φ ) → ( φ ∧ ψ ) → φ
    s_impl = lb.ref(
        "s_impl",
        "( ψ ∧ φ ) → φ",
        s_ancom_rev,
        s_simpl,
        ref="syl",
        note="syl",
    )
    # moimi: lift the implication through the "at most one" quantifier
    res = lb.ref(
        "res",
        "∃* x φ → ∃* x ( ψ ∧ φ )",
        s_impl,
        ref="moimi",
        note="moimi",
    )
    return lb.build(res)


def prove_moani(sys: System) -> Proof:
    """moani: ∃* x ( ψ ∧ φ ).
    Inference form of moan.  From ∃* x φ, conclude ∃* x ( ψ ∧ φ ).
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "moani")
    hyp = lb.hyp("moani.1", "∃* x φ")
    s_moan = lb.ref(
        "s_moan",
        "∃* x φ → ∃* x ( ψ ∧ φ )",
        ref="moan",
        note="moan",
    )
    res = lb.mp("res", hyp, s_moan, "ax-mp moan, moani.1")
    return lb.build(res)


def prove_mooran1(sys: System) -> Proof:
    """mooran1: ( ∃* x φ ∨ ∃* x ψ ) → ∃* x ( φ ∧ ψ ).
    "At most one" distributes over conjunction inside a disjunction.
    From simpl, moimi, moan, and jaoi.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "mooran1")
    # simpl: ( φ ∧ ψ ) → φ
    s_simpl = lb.ref(
        "s_simpl",
        "( φ ∧ ψ ) → φ",
        ref="simpl",
        note="simpl",
    )
    # moimi with simpl: ∃* x φ → ∃* x ( φ ∧ ψ )
    s_moimi = lb.ref(
        "s_moimi",
        "∃* x φ → ∃* x ( φ ∧ ψ )",
        s_simpl,
        ref="moimi",
        note="moimi simpl",
    )
    # moan with substitution: ∃* x ψ → ∃* x ( φ ∧ ψ )
    s_moan = lb.ref(
        "s_moan",
        "∃* x ψ → ∃* x ( φ ∧ ψ )",
        ref="moan",
        note="moan",
    )
    # jaoi: combine
    res = lb.ref(
        "res",
        "( ∃* x φ ∨ ∃* x ψ ) → ∃* x ( φ ∧ ψ )",
        s_moimi,
        s_moan,
        ref="jaoi",
        note="jaoi",
    )
    return lb.build(res)


def prove_moanmo(sys: System) -> Proof:
    """moanmo: ∃* x ( φ ∧ ∃* x φ ).
    An "at most one" quantifier is idempotent under conjunction:
    there exists at most one x such that φ and there exists at most
    one x such that φ.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "moanmo")
    # nfmo1: Ⅎ x ∃* x φ
    s_nfmo1 = lb.ref(
        "s_nfmo1",
        "Ⅎ x ∃* x φ",
        ref="nfmo1",
        note="nfmo1",
    )
    # moanim with nfmo1: ∃* x ( ∃* x φ ∧ φ ) ↔ ( ∃* x φ → ∃* x φ )
    s_moanim = lb.ref(
        "s_moanim",
        "∃* x ( ∃* x φ ∧ φ ) ↔ ( ∃* x φ → ∃* x φ )",
        s_nfmo1,
        ref="moanim",
        note="moanim nfmo1",
    )
    # id: ∃* x φ → ∃* x φ
    s_id = lb.ref(
        "s_id",
        "∃* x φ → ∃* x φ",
        ref="id",
        note="id",
    )
    # mpbir: ∃* x ( ∃* x φ ∧ φ )
    s_mpbir = lb.ref(
        "s_mpbir",
        "∃* x ( ∃* x φ ∧ φ )",
        s_id,
        s_moanim,
        ref="mpbir",
        note="mpbir id, moanim",
    )
    # ancom: ( ∃* x φ ∧ φ ) ↔ ( φ ∧ ∃* x φ )
    s_ancom = lb.ref(
        "s_ancom",
        "( ∃* x φ ∧ φ ) ↔ ( φ ∧ ∃* x φ )",
        ref="ancom",
        note="ancom",
    )
    # mobii with ancom: ∃* x ( ∃* x φ ∧ φ ) ↔ ∃* x ( φ ∧ ∃* x φ )
    s_mobii = lb.ref(
        "s_mobii",
        "∃* x ( ∃* x φ ∧ φ ) ↔ ∃* x ( φ ∧ ∃* x φ )",
        s_ancom,
        ref="mobii",
        note="mobii ancom",
    )
    # mpbi: ∃* x ( φ ∧ ∃* x φ )
    res = lb.ref(
        "res",
        "∃* x ( φ ∧ ∃* x φ )",
        s_mpbir,
        s_mobii,
        ref="mpbi",
        note="mpbi mpbir, mobii",
    )
    return lb.build(res)


def prove_moaneu(sys: System) -> Proof:
    """moaneu: ∃* x ( φ ∧ ∃! x φ ).
    There exists at most one x such that φ and there exists exactly one x
    such that φ.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "moaneu")
    # moanmo: ∃* x ( φ ∧ ∃* x φ )
    s_moanmo = lb.ref(
        "s_moanmo",
        "∃* x ( φ ∧ ∃* x φ )",
        ref="moanmo",
        note="moanmo",
    )
    # eumo: ∃! x φ → ∃* x φ
    s_eumo = lb.ref(
        "s_eumo",
        "∃! x φ → ∃* x φ",
        ref="eumo",
        note="eumo",
    )
    # anim2i with eumo: ( φ ∧ ∃! x φ ) → ( φ ∧ ∃* x φ )
    s_anim2i = lb.ref(
        "s_anim2i",
        "( φ ∧ ∃! x φ ) → ( φ ∧ ∃* x φ )",
        s_eumo,
        ref="anim2i",
        note="anim2i eumo",
    )
    # moimi with anim2i: ∃* x ( φ ∧ ∃* x φ ) → ∃* x ( φ ∧ ∃! x φ )
    s_moimi = lb.ref(
        "s_moimi",
        "∃* x ( φ ∧ ∃* x φ ) → ∃* x ( φ ∧ ∃! x φ )",
        s_anim2i,
        ref="moimi",
        note="moimi anim2i",
    )
    # ax-mp: ∃* x ( φ ∧ ∃! x φ )
    res = lb.mp(
        "res",
        s_moanmo,
        s_moimi,
        note="ax-mp moanmo, moimi",
    )
    return lb.build(res)


def prove_moanimlem(sys: System) -> Proof:
    """moanimlem: ∃* x ( φ ∧ ψ ) ↔ ( φ → ∃* x ψ ).
    Lemma for moanim.  The forward direction uses biimprcd on the first
    hypothesis; the reverse direction combines nsyl5 / nexmo with moan
    via ja, and both directions are joined with impbii.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "moanimlem")
    h1 = lb.hyp("moanimlem.1", "φ → ( ∃* x ψ ↔ ∃* x ( φ ∧ ψ ) )")
    h2 = lb.hyp("moanimlem.2", "∃ x ( φ ∧ ψ ) → φ")
    # biimprcd moanimlem.1: ∃* x ( φ ∧ ψ ) → ( φ → ∃* x ψ )
    s_fwd = lb.ref(
        "s_fwd",
        "∃* x ( φ ∧ ψ ) → ( φ → ∃* x ψ )",
        h1,
        ref="biimprcd",
        note="biimprcd moanimlem.1",
    )
    # nexmo: ¬ ∃ x ( φ ∧ ψ ) → ∃* x ( φ ∧ ψ )
    s_nexmo = lb.ref(
        "s_nexmo",
        "¬ ∃ x ( φ ∧ ψ ) → ∃* x ( φ ∧ ψ )",
        ref="nexmo",
        note="nexmo",
    )
    # nsyl5 moanimlem.2, nexmo: ¬ φ → ∃* x ( φ ∧ ψ )
    s_nsyl5 = lb.ref(
        "s_nsyl5",
        "¬ φ → ∃* x ( φ ∧ ψ )",
        h2,
        s_nexmo,
        ref="nsyl5",
        note="nsyl5 moanimlem.2, nexmo",
    )
    # moan: ∃* x ψ → ∃* x ( φ ∧ ψ )
    s_moan = lb.ref(
        "s_moan",
        "∃* x ψ → ∃* x ( φ ∧ ψ )",
        ref="moan",
        note="moan",
    )
    # ja s_nsyl5, s_moan: ( φ → ∃* x ψ ) → ∃* x ( φ ∧ ψ )
    s_rev = lb.ref(
        "s_rev",
        "( φ → ∃* x ψ ) → ∃* x ( φ ∧ ψ )",
        s_nsyl5,
        s_moan,
        ref="ja",
        note="ja nsyl5, moan",
    )
    # impbii s_fwd, s_rev
    res = lb.ref(
        "res",
        "∃* x ( φ ∧ ψ ) ↔ ( φ → ∃* x ψ )",
        s_fwd,
        s_rev,
        ref="impbii",
        note="impbii biimprcd, ja",
    )
    return lb.build(res)


def prove_moanim(sys: System) -> Proof:
    """moanim: ∃* x ( φ ∧ ψ ) ↔ ( φ → ∃* x ψ ).
    Theorem form of moanimlem using a non-freeness hypothesis.  The
    forward and reverse directions are instances of mobid and
    exlimi/simpl respectively, combined with moanimlem.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "moanim")
    h_nf = lb.hyp("moanim.1", "Ⅎ x φ")
    # ibar: φ → ( ψ ↔ ( φ ∧ ψ ) )
    s_ibar = lb.ref(
        "s_ibar",
        "φ → ( ψ ↔ ( φ ∧ ψ ) )",
        ref="ibar",
        note="ibar",
    )
    # mobid moanim.1, ibar: φ → ( ∃* x ψ ↔ ∃* x ( φ ∧ ψ ) )
    s_mobid = lb.ref(
        "s_mobid",
        "φ → ( ∃* x ψ ↔ ∃* x ( φ ∧ ψ ) )",
        h_nf,
        s_ibar,
        ref="mobid",
        note="mobid moanim.1, ibar",
    )
    # simpl: ( φ ∧ ψ ) → φ
    s_simpl = lb.ref(
        "s_simpl",
        "( φ ∧ ψ ) → φ",
        ref="simpl",
        note="simpl",
    )
    # exlimi moanim.1, simpl: ∃ x ( φ ∧ ψ ) → φ
    s_exlimi = lb.ref(
        "s_exlimi",
        "∃ x ( φ ∧ ψ ) → φ",
        h_nf,
        s_simpl,
        ref="exlimi",
        note="exlimi moanim.1, simpl",
    )
    # moanimlem mobid, exlimi
    res = lb.ref(
        "res",
        "∃* x ( φ ∧ ψ ) ↔ ( φ → ∃* x ψ )",
        s_mobid,
        s_exlimi,
        ref="moanimlem",
        note="moanimlem mobid, exlimi",
    )
    return lb.build(res)


def prove_moanimv(sys: System) -> Proof:
    """moanimv: ∃* x ( φ ∧ ψ ) ↔ ( φ → ∃* x ψ ).
    Version of moanim using distinct variable conditions instead of
    a non-freeness hypothesis.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "moanimv")
    # ibar: φ → ( ψ ↔ ( φ ∧ ψ ) )
    s_ibar = lb.ref(
        "s_ibar",
        "φ → ( ψ ↔ ( φ ∧ ψ ) )",
        ref="ibar",
        note="ibar",
    )
    # mobidv ibar: φ → ( ∃* x ψ ↔ ∃* x ( φ ∧ ψ ) )
    s_mobidv = lb.ref(
        "s_mobidv",
        "φ → ( ∃* x ψ ↔ ∃* x ( φ ∧ ψ ) )",
        s_ibar,
        ref="mobidv",
        note="mobidv ibar",
    )
    # simpl: ( φ ∧ ψ ) → φ
    s_simpl = lb.ref(
        "s_simpl",
        "( φ ∧ ψ ) → φ",
        ref="simpl",
        note="simpl",
    )
    # exlimiv simpl: ∃ x ( φ ∧ ψ ) → φ
    s_exlimiv = lb.ref(
        "s_exlimiv",
        "∃ x ( φ ∧ ψ ) → φ",
        s_simpl,
        ref="exlimiv",
        note="exlimiv simpl",
    )
    # moanimlem mobidv, exlimiv
    res = lb.ref(
        "res",
        "∃* x ( φ ∧ ψ ) ↔ ( φ → ∃* x ψ )",
        s_mobidv,
        s_exlimiv,
        ref="moanimlem",
        note="moanimlem mobidv, exlimiv",
    )
    return lb.build(res)


def prove_19_36(sys: System) -> Proof:
    """19.36: ∃ x ( φ → ψ ) ↔ ( ∀ x φ → ψ ).
    Existential quantifier over an implication with a non-free consequent.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "19.36")
    hyp = lb.hyp("19.36.1", "Ⅎ x ψ")
    # 19.35: ∃ x ( φ → ψ ) ↔ ( ∀ x φ → ∃ x ψ )
    s1 = lb.ref(
        "s1",
        "∃ x ( φ → ψ ) ↔ ( ∀ x φ → ∃ x ψ )",
        ref="19.35",
        note="19.35",
    )
    # 19.9 with 19.36.1: ∃ x ψ ↔ ψ
    s2 = lb.ref(
        "s2",
        "∃ x ψ ↔ ψ",
        hyp,
        ref="19.9",
        note="19.9 19.36.1",
    )
    # imbi2i: ( ∀ x φ → ∃ x ψ ) ↔ ( ∀ x φ → ψ )
    s3 = lb.ref(
        "s3",
        "( ∀ x φ → ∃ x ψ ) ↔ ( ∀ x φ → ψ )",
        s2,
        ref="imbi2i",
        note="imbi2i 19.9",
    )
    # bitri: ∃ x ( φ → ψ ) ↔ ( ∀ x φ → ψ )
    res = lb.ref(
        "res",
        "∃ x ( φ → ψ ) ↔ ( ∀ x φ → ψ )",
        s1,
        s3,
        ref="bitri",
        note="bitri 19.35, imbi2i",
    )
    return lb.build(res)


def prove_19_36i(sys: System) -> Proof:
    """19.36i: ∀ x φ → ψ.
    Inference form of 19.36: from Ⅎ x ψ and ∃ x ( φ → ψ ),
    conclude ∀ x φ → ψ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "19.36i")
    hyp1 = lb.hyp("19.36.1", "Ⅎ x ψ")
    hyp2 = lb.hyp("19.36i.2", "∃ x ( φ → ψ )")
    s1 = lb.ref(
        "s1",
        "∃ x ( φ → ψ ) ↔ ( ∀ x φ → ψ )",
        hyp1,
        ref="19.36",
        note="19.36 19.36.1",
    )
    res = lb.ref(
        "res",
        "∀ x φ → ψ",
        hyp2,
        s1,
        ref="mpbi",
        note="mpbi 19.36i.2, 19.36",
    )
    return lb.build(res)


def prove_19_37(sys: System) -> Proof:
    """19.37: ∃ x ( φ → ψ ) ↔ ( φ → ∃ x ψ ).
    Existential quantifier distributes over an implication when the
    antecedent does not contain the bound variable.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "19.37")
    hyp = lb.hyp("19.37.1", "Ⅎ x φ")
    # 19.35: ∃ x ( φ → ψ ) ↔ ( ∀ x φ → ∃ x ψ )
    s1 = lb.ref(
        "s1",
        "∃ x ( φ → ψ ) ↔ ( ∀ x φ → ∃ x ψ )",
        ref="19.35",
        note="19.35",
    )
    # 19.3 with 19.37.1: ∀ x φ ↔ φ
    s2 = lb.ref(
        "s2",
        "∀ x φ ↔ φ",
        hyp,
        ref="19.3",
        note="19.3 19.37.1",
    )
    # imbi1i: ( ∀ x φ → ∃ x ψ ) ↔ ( φ → ∃ x ψ )
    s3 = lb.ref(
        "s3",
        "( ∀ x φ → ∃ x ψ ) ↔ ( φ → ∃ x ψ )",
        s2,
        ref="imbi1i",
        note="imbi1i 19.3",
    )
    # bitri: chain s1 and s3
    res = lb.ref(
        "res",
        "∃ x ( φ → ψ ) ↔ ( φ → ∃ x ψ )",
        s1,
        s3,
        ref="bitri",
        note="bitri 19.35, imbi1i",
    )
    return lb.build(res)


def prove_spim(sys: System) -> Proof:
    """spim: ∀ x φ → ψ.
    Specialization with a distinct variable condition and a non-free
    consequent. From Ⅎ x ψ and ( x = y → ( φ → ψ ) ), conclude
    ∀ x φ → ψ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "spim")
    hyp_nf = lb.hyp("spim.1", "Ⅎ x ψ")
    hyp_imp = lb.hyp("spim.2", "( x = y ) → ( φ → ψ )")
    # ax6e: ∃ x x = y
    s_ax6e = lb.ref(
        "s_ax6e",
        "∃ x x = y",
        ref="ax6e",
        note="ax6e",
    )
    # eximii: from ∃ x x = y and (x = y) → (φ → ψ), get ∃ x (φ → ψ)
    s_eximii = lb.ref(
        "s_eximii",
        "∃ x ( φ → ψ )",
        s_ax6e,
        hyp_imp,
        ref="eximii",
        note="eximii",
    )
    # 19.36i: from Ⅎ x ψ and ∃ x (φ → ψ), get ∀ x φ → ψ
    res = lb.ref(
        "res",
        "∀ x φ → ψ",
        hyp_nf,
        s_eximii,
        ref="19.36i",
        note="19.36i",
    )
    return lb.build(res)


def prove_spimed(sys: System) -> Proof:
    """spimed: χ → (φ → ∃ x ψ).
    Deduction form of spim: specialization with a non-free hypothesis.
    From χ → Ⅎ x φ and ( x = y → ( φ → ψ ) ), conclude
    χ → ( φ → ∃ x ψ ).
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "spimed")
    hyp_nf = lb.hyp("spimed.1", "χ → Ⅎ x φ")
    hyp_imp = lb.hyp("spimed.2", "x = y → ( φ → ψ )")
    # nf5rd: from χ → Ⅎ x φ, get χ → ( φ → ∀ x φ )
    s_nf5rd = lb.ref(
        "s_nf5rd",
        "χ → ( φ → ∀ x φ )",
        hyp_nf,
        ref="nf5rd",
        note="nf5rd spimed.1",
    )
    # ax6e: ∃ x x = y
    s_ax6e = lb.ref(
        "s_ax6e",
        "∃ x x = y",
        ref="ax6e",
        note="ax6e",
    )
    # eximii: from ∃ x x = y and x = y → (φ → ψ), get ∃ x ( φ → ψ )
    s_eximii = lb.ref(
        "s_eximii",
        "∃ x ( φ → ψ )",
        s_ax6e,
        hyp_imp,
        ref="eximii",
        note="eximii",
    )
    # 19.35i: from ∃ x ( φ → ψ ), get ∀ x φ → ∃ x ψ
    s_19_35i = lb.ref(
        "s_19_35i",
        "∀ x φ → ∃ x ψ",
        s_eximii,
        ref="19.35i",
        note="19.35i",
    )
    # syl6: chain s_nf5rd and s_19_35i → χ → ( φ → ∃ x ψ )
    res = lb.ref(
        "res",
        "χ → ( φ → ∃ x ψ )",
        s_nf5rd,
        s_19_35i,
        ref="syl6",
        note="syl6 nf5rd, 19.35i",
    )
    return lb.build(res)


def prove_spimedv(sys: System) -> Proof:
    """spimedv: χ → (φ → ∃ x ψ).
    Deduction form of spim: specialization with a non-free hypothesis
    (distinct variable version).  From χ → Ⅎ x φ and
    x = y → ( φ → ψ ), conclude χ → ( φ → ∃ x ψ ).
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "spimedv")
    hyp_nf = lb.hyp("spimedv.1", "χ → Ⅎ x φ")
    hyp_imp = lb.hyp("spimedv.2", "x = y → ( φ → ψ )")
    # nf5rd: from χ → Ⅎ x φ, get χ → ( φ → ∀ x φ )
    s_nf5rd = lb.ref(
        "s_nf5rd",
        "χ → ( φ → ∀ x φ )",
        hyp_nf,
        ref="nf5rd",
        note="nf5rd spimedv.1",
    )
    # ax6ev: ∃ x x = y
    s_ax6ev = lb.ref(
        "s_ax6ev",
        "∃ x x = y",
        ref="ax6ev",
        note="ax6ev",
    )
    # eximii: from ∃ x x = y and x = y → ( φ → ψ ), get ∃ x ( φ → ψ )
    s_eximii = lb.ref(
        "s_eximii",
        "∃ x ( φ → ψ )",
        s_ax6ev,
        hyp_imp,
        ref="eximii",
        note="eximii",
    )
    # 19.35i: from ∃ x ( φ → ψ ), get ∀ x φ → ∃ x ψ
    s_19_35i = lb.ref(
        "s_19_35i",
        "∀ x φ → ∃ x ψ",
        s_eximii,
        ref="19.35i",
        note="19.35i",
    )
    # syl6: chain s_nf5rd and s_19_35i → χ → ( φ → ∃ x ψ )
    res = lb.ref(
        "res",
        "χ → ( φ → ∃ x ψ )",
        s_nf5rd,
        s_19_35i,
        ref="syl6",
        note="syl6 nf5rd, 19.35i",
    )
    return lb.build(res)


def prove_spime(sys: System) -> Proof:
    """spime: φ → ∃ x ψ.
    Inference form of spimed: specialization with a non-free hypothesis.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "spime")
    hyp_nf = lb.hyp("spime.1", "Ⅎ x φ")
    hyp_imp = lb.hyp("spime.2", "x = y → ( φ → ψ )")
    # a1i spime.1: ⊤ → Ⅎ x φ
    s_a1i = lb.ref(
        "s_a1i",
        "⊤ → Ⅎ x φ",
        hyp_nf,
        ref="a1i",
        note="a1i spime.1",
    )
    # spimed: ⊤ → ( φ → ∃ x ψ )
    s_spimed = lb.ref(
        "s_spimed",
        "⊤ → ( φ → ∃ x ψ )",
        s_a1i,
        hyp_imp,
        ref="spimed",
        note="spimed",
    )
    # mptru: φ → ∃ x ψ
    res = lb.ref(
        "res",
        "φ → ∃ x ψ",
        s_spimed,
        ref="mptru",
        note="mptru spimed",
    )
    return lb.build(res)


def prove_spimefv(sys: System) -> Proof:
    """spimefv: φ → ∃ x ψ.
    Inference form of spimedv: specialization with a non-free hypothesis
    (distinct variable version).  From Ⅎ x φ and
    x = y → ( φ → ψ ), conclude φ → ∃ x ψ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "spimefv")
    hyp_nf = lb.hyp("spimefv.1", "Ⅎ x φ")
    hyp_imp = lb.hyp("spimefv.2", "x = y → ( φ → ψ )")
    # a1i spimefv.1: ⊤ → Ⅎ x φ
    s_a1i = lb.ref(
        "s_a1i",
        "⊤ → Ⅎ x φ",
        hyp_nf,
        ref="a1i",
        note="a1i spimefv.1",
    )
    # spimedv: ⊤ → ( φ → ∃ x ψ )
    s_spimedv = lb.ref(
        "s_spimedv",
        "⊤ → ( φ → ∃ x ψ )",
        s_a1i,
        hyp_imp,
        ref="spimedv",
        note="spimedv",
    )
    # mptru: φ → ∃ x ψ
    res = lb.ref(
        "res",
        "φ → ∃ x ψ",
        s_spimedv,
        ref="mptru",
        note="mptru spimedv",
    )
    return lb.build(res)


def prove_spimev(sys: System) -> Proof:
    """spimev: φ → ∃ x ψ.
    Specialization with a distinct variable condition.  From
    ( x = y → ( φ → ψ ) ), conclude φ → ∃ x ψ by using nfv
    for the Ⅎ x φ side-condition and spime to eliminate it.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "spimev")
    hyp = lb.hyp("spimev.1", "x = y → ( φ → ψ )")
    # nfv: Ⅎ x φ
    s_nfv = lb.ref(
        "s_nfv",
        "Ⅎ x φ",
        ref="nfv",
        note="nfv",
    )
    # spime: from Ⅎ x φ and x = y → ( φ → ψ ), get φ → ∃ x ψ
    res = lb.ref(
        "res",
        "φ → ∃ x ψ",
        s_nfv,
        hyp,
        ref="spime",
        note="spime",
    )
    return lb.build(res)


def prove_spimt(sys: System) -> Proof:
    """spimt: ( Ⅎ x ψ ∧ ∀ x ( x = y → ( φ → ψ ) ) ) → ( ∀ x φ → ψ ).
    Theorem form of spim: specialization with a non-free hypothesis.
    From Ⅎ x ψ and ∀ x ( x = y → ( φ → ψ ) ), conclude ∀ x φ → ψ .
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "spimt")
    # ax6e: ∃ x x = y
    s_ax6e = lb.ref(
        "s_ax6e",
        "∃ x x = y",
        ref="ax6e",
        note="ax6e",
    )
    # exim: ∀ x ( x = y → ( φ → ψ ) ) → ( ∃ x x = y → ∃ x ( φ → ψ ) )
    s_exim = lb.ref(
        "s_exim",
        "∀ x ( x = y → ( φ → ψ ) ) → ( ∃ x x = y → ∃ x ( φ → ψ ) )",
        ref="exim",
        note="exim",
    )
    # mpi: ∀ x ( x = y → ( φ → ψ ) ) → ∃ x ( φ → ψ )
    s_mpi = lb.ref(
        "s_mpi",
        "∀ x ( x = y → ( φ → ψ ) ) → ∃ x ( φ → ψ )",
        s_ax6e,
        s_exim,
        ref="mpi",
        note="mpi ax6e, exim",
    )
    # 19.35: ∃ x ( φ → ψ ) ↔ ( ∀ x φ → ∃ x ψ )
    s_19_35 = lb.ref(
        "s_19_35",
        "∃ x ( φ → ψ ) ↔ ( ∀ x φ → ∃ x ψ )",
        ref="19.35",
        note="19.35",
    )
    # sylib: ∀ x ( x = y → ( φ → ψ ) ) → ( ∀ x φ → ∃ x ψ )
    s_sylib = lb.ref(
        "s_sylib",
        "∀ x ( x = y → ( φ → ψ ) ) → ( ∀ x φ → ∃ x ψ )",
        s_mpi,
        s_19_35,
        ref="sylib",
        note="sylib mpi, 19.35",
    )
    # id: Ⅎ x ψ → Ⅎ x ψ
    s_id = lb.ref(
        "s_id",
        "Ⅎ x ψ → Ⅎ x ψ",
        ref="id",
        note="id",
    )
    # 19.9d: Ⅎ x ψ → ( ∃ x ψ → ψ )
    s_19_9d = lb.ref(
        "s_19_9d",
        "Ⅎ x ψ → ( ∃ x ψ → ψ )",
        s_id,
        ref="19.9d",
        note="19.9d id",
    )
    # sylan9r: ( Ⅎ x ψ ∧ ∀ x ( x = y → ( φ → ψ ) ) ) → ( ∀ x φ → ψ )
    res = lb.ref(
        "res",
        "( Ⅎ x ψ ∧ ∀ x ( x = y → ( φ → ψ ) ) ) → ( ∀ x φ → ψ )",
        s_sylib,
        s_19_9d,
        ref="sylan9r",
        note="sylan9r sylib, 19.9d",
    )
    return lb.build(res)


def prove_spimfv(sys: System) -> Proof:
    """spimfv: ∀ x φ → ψ.
    Specialization with a distinct variable condition and a non-free
    consequent. From Ⅎ x ψ and ( x = y → ( φ → ψ ) ), conclude
    ∀ x φ → ψ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "spimfv")
    hyp_nf = lb.hyp("spimfv.nf", "Ⅎ x ψ")
    hyp_imp = lb.hyp("spimfv.1", "( x = y ) → ( φ → ψ )")
    # ax6ev: ∃ x x = y
    s_ax6ev = lb.ref(
        "s_ax6ev",
        "∃ x x = y",
        ref="ax6ev",
        note="ax6ev",
    )
    # eximii: from ∃ x x = y and (x = y) → (φ → ψ), get ∃ x (φ → ψ)
    s_eximii = lb.ref(
        "s_eximii",
        "∃ x ( φ → ψ )",
        s_ax6ev,
        hyp_imp,
        ref="eximii",
        note="eximii",
    )
    # 19.36i: from Ⅎ x ψ and ∃ x (φ → ψ), get ∀ x φ → ψ
    res = lb.ref(
        "res",
        "∀ x φ → ψ",
        hyp_nf,
        s_eximii,
        ref="19.36i",
        note="19.36i",
    )
    return lb.build(res)


def prove_spimv(sys: System) -> Proof:
    """spimv: ∀ x φ → ψ.
    Specialization with a distinct variable condition.  From
    ( x = y → ( φ → ψ ) ), conclude ∀ x φ → ψ by using nfv
    for the Ⅎ x ψ side-condition and spim to eliminate it.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "spimv")
    hyp = lb.hyp("spimv.1", "( x = y ) → ( φ → ψ )")
    # nfv: Ⅎ x ψ
    s_nfv = lb.ref(
        "s_nfv",
        "Ⅎ x ψ",
        ref="nfv",
        note="nfv",
    )
    # spim: from Ⅎ x ψ and ( x = y ) → ( φ → ψ ), get ∀ x φ → ψ
    res = lb.ref(
        "res",
        "∀ x φ → ψ",
        s_nfv,
        hyp,
        ref="spim",
        note="spim",
    )
    return lb.build(res)


def prove_spimvALT(sys: System) -> Proof:
    """spimvALT: ∀ x φ → ψ.
    Alternate proof of spimv using ax6e, eximii, and 19.36iv.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "spimvALT")
    hyp = lb.hyp("spimv.1", "( x = y ) → ( φ → ψ )")
    # ax6e: ∃ x x = y
    s_ax6e = lb.ref(
        "s_ax6e",
        "∃ x x = y",
        ref="ax6e",
        note="ax6e",
    )
    # eximii: from ∃ x x = y and ( x = y ) → ( φ → ψ ), get ∃ x ( φ → ψ )
    s_eximii = lb.ref(
        "s_eximii",
        "∃ x ( φ → ψ )",
        s_ax6e,
        hyp,
        ref="eximii",
        note="eximii",
    )
    # 19.36iv: from ∃ x ( φ → ψ ), get ∀ x φ → ψ
    res = lb.ref(
        "res",
        "∀ x φ → ψ",
        s_eximii,
        ref="19.36iv",
        note="19.36iv",
    )
    return lb.build(res)


def prove_spv(sys: System) -> Proof:
    """spv: ∀ x φ → ψ.
    Specialization with implicit substitution.  From
    ( x = y → ( φ ↔ ψ ) ), use biimpd to derive the forward
    implication, then spimv to obtain the conclusion.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "spv")
    hyp = lb.hyp("spv.1", "( x = y ) → ( φ ↔ ψ )")
    # biimpd spv.1: ( x = y ) → ( φ → ψ )
    s_biimpd = lb.ref(
        "s_biimpd",
        "( x = y ) → ( φ → ψ )",
        hyp,
        ref="biimpd",
        note="biimpd spv.1",
    )
    # spimv: ∀ x φ → ψ
    res = lb.ref(
        "res",
        "∀ x φ → ψ",
        s_biimpd,
        ref="spimv",
        note="spimv biimpd",
    )
    return lb.build(res)


def prove_chvarfv(sys: System) -> Proof:
    """chvarfv: ψ.
    Change variable in a non-free context. From Ⅎ x ψ, ( x = y → ( φ ↔ ψ ) ),
    and φ, conclude ψ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "chvarfv")
    hyp_nf = lb.hyp("chvarfv.nf", "Ⅎ x ψ")
    hyp_impl = lb.hyp("chvarfv.1", "( x = y ) → ( φ ↔ ψ )")
    hyp_phi = lb.hyp("chvarfv.2", "φ")
    # biimpd: from ( x = y ) → ( φ ↔ ψ ), get ( x = y ) → ( φ → ψ )
    s1 = lb.ref(
        "s1",
        "( x = y ) → ( φ → ψ )",
        hyp_impl,
        ref="biimpd",
        note="biimpd chvarfv.1",
    )
    # spimfv: from Ⅎ x ψ and ( x = y ) → ( φ → ψ ), get ∀ x φ → ψ
    s2 = lb.ref(
        "s2",
        "∀ x φ → ψ",
        hyp_nf,
        s1,
        ref="spimfv",
        note="spimfv chvarfv.nf, biimpd",
    )
    # mpg: from ∀ x φ → ψ and φ, get ψ
    res = lb.ref(
        "res",
        "ψ",
        s2,
        hyp_phi,
        ref="mpg",
        note="mpg spimfv, chvarfv.2",
    )
    return lb.build(res)


def prove_chvar(sys: System) -> Proof:
    """chvar: ψ.
    Change variable in a non-free context. From Ⅎ x ψ, ( x = y → ( φ ↔ ψ ) ),
    and φ, conclude ψ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "chvar")
    hyp_nf = lb.hyp("chvar.1", "Ⅎ x ψ")
    hyp_impl = lb.hyp("chvar.2", "( x = y ) → ( φ ↔ ψ )")
    hyp_phi = lb.hyp("chvar.3", "φ")
    # biimpd: from ( x = y ) → ( φ ↔ ψ ), get ( x = y ) → ( φ → ψ )
    s1 = lb.ref(
        "s1",
        "( x = y ) → ( φ → ψ )",
        hyp_impl,
        ref="biimpd",
        note="biimpd chvar.2",
    )
    # spim: from Ⅎ x ψ and ( x = y ) → ( φ → ψ ), get ∀ x φ → ψ
    s2 = lb.ref(
        "s2",
        "∀ x φ → ψ",
        hyp_nf,
        s1,
        ref="spim",
        note="spim chvar.1, biimpd",
    )
    # mpg: from ∀ x φ → ψ and φ, get ψ
    res = lb.ref(
        "res",
        "ψ",
        s2,
        hyp_phi,
        ref="mpg",
        note="mpg spim, chvar.3",
    )
    return lb.build(res)


def prove_chvarv(sys: System) -> Proof:
    """chvarv: ψ.
    Change variable in a non-free context. From ( x = y → ( φ ↔ ψ ) )
    and φ, conclude ψ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "chvarv")
    hyp_impl = lb.hyp("chvarv.1", "( x = y ) → ( φ ↔ ψ )")
    hyp_phi = lb.hyp("chvarv.2", "φ")
    # nfv: Ⅎ x ψ
    s1 = lb.ref(
        "s1",
        "Ⅎ x ψ",
        ref="nfv",
        note="nfv",
    )
    # chvar: from Ⅎ x ψ, ( x = y → ( φ ↔ ψ ) ), and φ, get ψ
    res = lb.ref(
        "res",
        "ψ",
        s1,
        hyp_impl,
        hyp_phi,
        ref="chvar",
        note="chvar",
    )
    return lb.build(res)


def prove_cleljustALT(sys: System) -> Proof:
    """cleljustALT: x ∈ y ↔ ∃ z ( z = x ∧ z ∈ y ).
    Alternative proof of cleljust using equsexhv instead of equsexvw.
    From ax-5 and elequ1 via equsexhv, then bicomi.
    (Contributed by NM, 10-Jan-1993.)
    set.mm proof: weq wel wa wex ax-5 elequ1 equsexhv bicomi.
    """
    lb = ProofBuilder(sys, "cleljustALT")
    # ax-5: x ∈ y → ∀ z ( x ∈ y )
    s_ax5 = lb.ref(
        "s_ax5",
        "x ∈ y → ∀ z ( x ∈ y )",
        ref="ax-5",
        note="ax-5",
    )
    # elequ1: z = x → ( z ∈ y ↔ x ∈ y )
    s_elequ1 = lb.ref(
        "s_elequ1",
        "z = x → ( z ∈ y ↔ x ∈ y )",
        ref="elequ1",
        note="elequ1",
    )
    # equsexhv: ∃ z ( z = x ∧ z ∈ y ) ↔ x ∈ y
    s_equsexhv = lb.ref(
        "s_equsexhv",
        "∃ z ( z = x ∧ z ∈ y ) ↔ x ∈ y",
        s_ax5,
        s_elequ1,
        ref="equsexhv",
        note="equsexhv ax-5, elequ1",
    )
    # bicomi: x ∈ y ↔ ∃ z ( z = x ∧ z ∈ y )
    res = lb.ref(
        "res",
        "x ∈ y ↔ ∃ z ( z = x ∧ z ∈ y )",
        s_equsexhv,
        ref="bicomi",
        note="bicomi",
    )
    return lb.build(res)


def prove_cleljustALT2(sys: System) -> Proof:
    """cleljustALT2: x ∈ y ↔ ∃ z ( z = x ∧ z ∈ y ).
    Alternative proof of cleljust using nfv, elequ1, equsexv, and bicomi.
    (Contributed by NM, 10-Jan-1993.)
    set.mm proof: weq wel wa wex nfv elequ1 equsexv bicomi.
    """
    lb = ProofBuilder(sys, "cleljustALT2")
    # nfv: Ⅎ z ( x ∈ y )
    s_nfv = lb.ref(
        "s_nfv",
        "Ⅎ z ( x ∈ y )",
        ref="nfv",
        note="nfv",
    )
    # elequ1: z = x → ( z ∈ y ↔ x ∈ y )
    s_elequ1 = lb.ref(
        "s_elequ1",
        "z = x → ( z ∈ y ↔ x ∈ y )",
        ref="elequ1",
        note="elequ1",
    )
    # equsexv: Ⅎ z ( x ∈ y ), z = x → ( z ∈ y ↔ x ∈ y )
    #          ⊢ ∃ z ( z = x ∧ z ∈ y ) ↔ x ∈ y
    s_equsexv = lb.ref(
        "s_equsexv",
        "∃ z ( z = x ∧ z ∈ y ) ↔ x ∈ y",
        s_nfv,
        s_elequ1,
        ref="equsexv",
        note="equsexv nfv, elequ1",
    )
    # bicomi: x ∈ y ↔ ∃ z ( z = x ∧ z ∈ y )
    res = lb.ref(
        "res",
        "x ∈ y ↔ ∃ z ( z = x ∧ z ∈ y )",
        s_equsexv,
        ref="bicomi",
        note="bicomi",
    )
    return lb.build(res)


def prove_elsb1(sys: System) -> Proof:
    """elsb1: [ y / x ] x ∈ z ↔ y ∈ z.
    Substituting y for x in the atomic membership formula yields y ∈ z.
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "elsb1")
    # elequ1: x = w → ( x ∈ z ↔ w ∈ z )
    h1 = lb.ref(
        "h1",
        "x = w → ( x ∈ z ↔ w ∈ z )",
        ref="elequ1",
        note="elequ1",
    )
    # elequ1: w = y → ( w ∈ z ↔ y ∈ z )
    h2 = lb.ref(
        "h2",
        "w = y → ( w ∈ z ↔ y ∈ z )",
        ref="elequ1",
        note="elequ1",
    )
    # sbievw2(h1, h2): [ y / x ] x ∈ z ↔ y ∈ z
    res = lb.ref(
        "res",
        "( [ y x x ∈ z ↔ y ∈ z )",
        h1,
        h2,
        ref="sbievw2",
        note="sbievw2",
    )
    return lb.build(res)


def prove_elsb2(sys: System) -> Proof:
    """elsb2: ( [ y / x ] z ∈ x ↔ z ∈ y ).
    Substitution of set variable in membership.  (Contributed by NM, 7-Jul-2023.)
    """
    lb = ProofBuilder(sys, "elsb2")
    # elequ2 with x,w: x = w → ( z ∈ x ↔ z ∈ w )
    s1 = lb.ref(
        "s1",
        "x = w → ( z ∈ x ↔ z ∈ w )",
        ref="elequ2",
        note="elequ2",
    )
    # elequ2 with w,y: w = y → ( z ∈ w ↔ z ∈ y )
    s2 = lb.ref(
        "s2",
        "w = y → ( z ∈ w ↔ z ∈ y )",
        ref="elequ2",
        note="elequ2",
    )
    # sbievw2 with hypotheses s1, s2: ( [ y / x ] z ∈ x ↔ z ∈ y )
    res = lb.ref(
        "res",
        "( [ y x z ∈ x ↔ z ∈ y )",
        s1,
        s2,
        ref="sbievw2",
        note="sbievw2 elequ2, elequ2",
    )
    return lb.build(res)


def prove_spei(sys: System) -> Proof:
    """spei: ∃ x φ.
    Existential introduction using implicit substitution. From (x = y → (φ ↔ ψ))
    and ψ, derive ∃ x φ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "spei")
    hyp1 = lb.hyp("spei.1", "x = y → ( φ ↔ ψ )")
    hyp2 = lb.hyp("spei.2", "ψ")
    # mpbiri: from ψ and (x = y → (φ ↔ ψ)), derive (x = y → φ)
    s1 = lb.ref(
        "s1",
        "x = y → φ",
        hyp2,
        hyp1,
        ref="mpbiri",
        note="mpbiri",
    )
    # ax6e: ∃ x x = y
    s2 = lb.ref(
        "s2",
        "∃ x x = y",
        ref="ax6e",
        note="ax6e",
    )
    # eximii: from ∃ x x = y and (x = y → φ), derive ∃ x φ
    res = lb.ref(
        "res",
        "∃ x φ",
        s2,
        s1,
        ref="eximii",
        note="eximii",
    )
    return lb.build(res)


def prove_equsb1(sys: System) -> Proof:
    """equsb1: [ y / x ] x = y.
    Substitution of equality.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "equsb1")
    # id: x = y → x = y
    s1 = lb.ref(
        "s1",
        "x = y → x = y",
        ref="id",
        note="id",
    )
    # sb2 with φ := x = y: ∀ x ( x = y → ( x = y ) ) → [ y x x = y
    s2 = lb.ref(
        "s2",
        "∀ x ( x = y → ( x = y ) ) → [ y x x = y",
        ref="sb2",
        note="sb2",
    )
    # mpg: [ y / x ] x = y
    res = lb.ref(
        "res",
        "[ y x x = y",
        s2,
        s1,
        ref="mpg",
        note="mpg sb2, id",
    )
    return lb.build(res)


def prove_equsb1v(sys: System) -> Proof:
    """equsb1v: [ y / x ] x = y.
    Proper substitution for an equality with swapped variables.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "equsb1v")
    # equid: y = y
    s1 = lb.ref("s1", "y = y", ref="equid", note="equid")
    # equsb3 with z := y: ( [ y / x ] x = y ↔ y = y )
    s2 = lb.ref(
        "s2",
        "( [ y x x = y ↔ y = y )",
        ref="equsb3",
        note="equsb3 with z := y",
    )
    # mpbir: [ y / x ] x = y
    res = lb.ref(
        "res",
        "[ y x x = y",
        s1,
        s2,
        ref="mpbir",
        note="mpbir equid, equsb3",
    )
    return lb.build(res)


def prove_equsb3(sys: System) -> Proof:
    """equsb3: ( [ y / x ] x = z ↔ y = z ).
    Equivalence of proper substitution of equality.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "equsb3")
    # equequ1: x = w → ( x = z ↔ w = z )
    s1 = lb.ref(
        "s1",
        "x = w → ( x = z ↔ w = z )",
        ref="equequ1",
        note="equequ1",
    )
    # equequ1: w = y → ( w = z ↔ y = z )
    s2 = lb.ref(
        "s2",
        "w = y → ( w = z ↔ y = z )",
        ref="equequ1",
        note="equequ1",
    )
    # sbievw2 with hypotheses s1, s2: ( [ y / x ] x = z ↔ y = z )
    res = lb.ref(
        "res",
        "( [ y x x = z ↔ y = z )",
        s1,
        s2,
        ref="sbievw2",
        note="sbievw2 equequ1, equequ1",
    )
    return lb.build(res)


def prove_equsb3r(sys: System) -> Proof:
    """equsb3r: ( [ y / x ] z = x ↔ z = y ).
    Equivalence of proper substitution of equality.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "equsb3r")
    # equequ2: x = w → ( z = x ↔ z = w )
    s1 = lb.ref(
        "s1",
        "x = w → ( z = x ↔ z = w )",
        ref="equequ2",
        note="equequ2",
    )
    # equequ2: w = y → ( z = w ↔ z = y )
    s2 = lb.ref(
        "s2",
        "w = y → ( z = w ↔ z = y )",
        ref="equequ2",
        note="equequ2",
    )
    # sbievw2 with hypotheses s1, s2: ( [ y / x ] z = x ↔ z = y )
    res = lb.ref(
        "res",
        "( [ y x z = x ↔ z = y )",
        s1,
        s2,
        ref="sbievw2",
        note="sbievw2 equequ2, equequ2",
    )
    return lb.build(res)


def prove_equs4(sys: System) -> Proof:
    """equs4: ∀ x ( x = y → φ ) → ∃ x ( x = y ∧ φ ).
    If for all x, x = y implies φ, then there exists an x such that
    both x = y and φ hold.
    (Contributed by NM, 10-Jan-1993.)
    set.mm proof: weq wi wal wex wa ax6e exintr mpi.
    """
    lb = ProofBuilder(sys, "equs4")
    # ax6e: ∃ x x = y
    s1 = lb.ref(
        "s1",
        "∃ x x = y",
        ref="ax6e",
        note="ax6e",
    )
    # exintr: ∀ x ((x = y) → φ) → (∃ x (x = y) → ∃ x ((x = y) ∧ φ))
    s2 = lb.ref(
        "s2",
        "∀ x ( ( x = y ) → φ ) → ( ∃ x ( x = y ) → ∃ x ( ( x = y ) ∧ φ ) )",
        ref="exintr",
        note="exintr",
    )
    # mpi with s1 (∃ x x = y) and s2: ∀ x ((x = y) → φ) → ∃ x ((x = y) ∧ φ)
    res = lb.ref(
        "res",
        "∀ x ( x = y → φ ) → ∃ x ( x = y ∧ φ )",
        s1,
        s2,
        ref="mpi",
        note="mpi ax6e, exintr",
    )
    return lb.build(res)


def prove_equs45f(sys: System) -> Proof:
    """equs45f: ∃ x ( x = y ∧ φ ) ↔ ∀ x ( x = y → φ ).

    Given Ⅎ y φ, the existence of x such that x = y ∧ φ is equivalent to
    for all x, x = y implies φ.
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "equs45f")
    hyp = lb.hyp("equs45f.1", "Ⅎ y φ")
    # nf5ri: φ → ∀ y φ
    s1 = lb.ref(
        "s1",
        "φ → ∀ y φ",
        hyp,
        ref="nf5ri",
        note="nf5ri equs45f.1",
    )
    # anim2i: ( x = y ∧ φ ) → ( x = y ∧ ∀ y φ )
    s2 = lb.ref(
        "s2",
        "( x = y ∧ φ ) → ( x = y ∧ ∀ y φ )",
        s1,
        ref="anim2i",
        note="anim2i nf5ri",
    )
    # eximi: ∃ x ( x = y ∧ φ ) → ∃ x ( x = y ∧ ∀ y φ )
    s3 = lb.ref(
        "s3",
        "∃ x ( x = y ∧ φ ) → ∃ x ( x = y ∧ ∀ y φ )",
        s2,
        ref="eximi",
        note="eximi anim2i",
    )
    # equs5a: ∃ x ( x = y ∧ ∀ y φ ) → ∀ x ( x = y → φ )
    s4 = lb.ref(
        "s4",
        "∃ x ( x = y ∧ ∀ y φ ) → ∀ x ( x = y → φ )",
        ref="equs5a",
        note="equs5a",
    )
    # syl: ∃ x ( x = y ∧ φ ) → ∀ x ( x = y → φ )
    s5 = lb.ref(
        "s5",
        "∃ x ( x = y ∧ φ ) → ∀ x ( x = y → φ )",
        s3,
        s4,
        ref="syl",
        note="syl eximi, equs5a",
    )
    # equs4: ∀ x ( x = y → φ ) → ∃ x ( x = y ∧ φ )
    s6 = lb.ref(
        "s6",
        "∀ x ( x = y → φ ) → ∃ x ( x = y ∧ φ )",
        ref="equs4",
        note="equs4",
    )
    # impbii: ( ∃ x ( x = y ∧ φ ) ↔ ∀ x ( x = y → φ ) )
    res = lb.ref(
        "res",
        "∃ x ( x = y ∧ φ ) ↔ ∀ x ( x = y → φ )",
        s5,
        s6,
        ref="impbii",
        note="impbii syl, equs4",
    )
    return lb.build(res)


def prove_equs5(sys: System) -> Proof:
    """equs5: ¬ ∀ x x = y → ( ∃ x ( x = y ∧ φ ) ↔ ∀ x ( x = y → φ ) ).

    Given a distinctor ¬ ∀ x x = y, the existence of an x for
    which both x = y and φ hold is equivalent to stating that
    for all x, x = y implies φ.
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "equs5")
    # nfna1: Ⅎ x ¬ ∀ x x = y
    s1 = lb.ref(
        "s1",
        "Ⅎ x ¬ ∀ x x = y",
        ref="nfna1",
        note="nfna1",
    )
    # nfa1: Ⅎ x ∀ x ( x = y → φ )
    s2 = lb.ref(
        "s2",
        "Ⅎ x ∀ x ( x = y → φ )",
        ref="nfa1",
        note="nfa1",
    )
    # axc15: ¬ ∀ x x = y → ( x = y → ( φ → ∀ x ( x = y → φ ) ) )
    s3 = lb.ref(
        "s3",
        "¬ ∀ x x = y → ( x = y → ( φ → ∀ x ( x = y → φ ) ) )",
        ref="axc15",
        note="axc15",
    )
    # impd: ¬ ∀ x x = y → ( ( x = y ∧ φ ) → ∀ x ( x = y → φ ) )
    s4 = lb.ref(
        "s4",
        "¬ ∀ x x = y → ( ( x = y ∧ φ ) → ∀ x ( x = y → φ ) )",
        s3,
        ref="impd",
        note="impd axc15",
    )
    # exlimd: ¬ ∀ x x = y → ( ∃ x ( x = y ∧ φ ) → ∀ x ( x = y → φ ) )
    s5 = lb.ref(
        "s5",
        "¬ ∀ x x = y → ( ∃ x ( x = y ∧ φ ) → ∀ x ( x = y → φ ) )",
        s1,
        s2,
        s4,
        ref="exlimd",
        note="exlimd nfna1, nfa1, impd",
    )
    # equs4: ∀ x ( x = y → φ ) → ∃ x ( x = y ∧ φ )
    s6 = lb.ref(
        "s6",
        "∀ x ( x = y → φ ) → ∃ x ( x = y ∧ φ )",
        ref="equs4",
        note="equs4",
    )
    # impbid1: ¬ ∀ x x = y → ( ∃ x ( x = y ∧ φ ) ↔ ∀ x ( x = y → φ ) )
    res = lb.ref(
        "res",
        "¬ ∀ x x = y → ( ∃ x ( x = y ∧ φ ) ↔ ∀ x ( x = y → φ ) )",
        s5,
        s6,
        ref="impbid1",
        note="impbid1 exlimd, equs4",
    )
    return lb.build(res)


def prove_equsal(sys: System) -> Proof:
    """equsal: ( ∀ x ( x = y → φ ) ↔ ψ ).
    From nf-x and an equivalence under equality, the universal
    quantifier over an implication is equivalent to the consequent.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "equsal")
    hyp1 = lb.hyp("equsal.1", "Ⅎ x ψ")
    hyp2 = lb.hyp("equsal.2", "x = y → ( φ ↔ ψ )")
    # pm5.74i: ( ( x = y → φ ) ↔ ( x = y → ψ ) )
    s1 = lb.ref(
        "s1",
        "( x = y → φ ) ↔ ( x = y → ψ )",
        hyp2,
        ref="pm5.74i",
        note="pm5.74i equsal.2",
    )
    # albii: ( ∀ x ( x = y → φ ) ↔ ∀ x ( x = y → ψ ) )
    s2 = lb.ref(
        "s2",
        "∀ x ( x = y → φ ) ↔ ∀ x ( x = y → ψ )",
        s1,
        ref="albii",
        note="albii pm5.74i",
    )
    # 19.23: ( ∀ x ( x = y → ψ ) ↔ ( ∃ x x = y → ψ ) )
    s3 = lb.ref(
        "s3",
        "∀ x ( x = y → ψ ) ↔ ( ∃ x x = y → ψ )",
        hyp1,
        ref="19.23",
        note="19.23 equsal.1",
    )
    # ax6e: ∃ x x = y
    s4 = lb.ref(
        "s4",
        "∃ x x = y",
        ref="ax6e",
        note="ax6e",
    )
    # a1bi: ( ψ ↔ ( ∃ x x = y → ψ ) )
    s5 = lb.ref(
        "s5",
        "ψ ↔ ( ∃ x x = y → ψ )",
        s4,
        ref="a1bi",
        note="a1bi ax6e",
    )
    # 3bitr4i: ( ∀ x ( x = y → φ ) ↔ ψ )
    res = lb.ref(
        "res",
        "∀ x ( x = y → φ ) ↔ ψ",
        s3,
        s2,
        s5,
        ref="3bitr4i",
        note="3bitr4i 19.23, albii, a1bi",
    )
    return lb.build(res)


def prove_equsalh(sys: System) -> Proof:
    """equsalh: ( ∀ x ( x = y → φ ) ↔ ψ ).
    Hypothesis version of equsal using nf5i.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "equsalh")
    hyp1 = lb.hyp("equsalh.1", "ψ → ∀ x ψ")
    hyp2 = lb.hyp("equsalh.2", "x = y → ( φ ↔ ψ )")
    # nf5i equsalh.1: Ⅎ x ψ
    s1 = lb.ref(
        "s1",
        "Ⅎ x ψ",
        hyp1,
        ref="nf5i",
        note="nf5i equsalh.1",
    )
    # equsal s1, hyp2: ( ∀ x ( x = y → φ ) ↔ ψ )
    res = lb.ref(
        "res",
        "∀ x ( x = y → φ ) ↔ ψ",
        s1,
        hyp2,
        ref="equsal",
        note="equsal nf5i, equsalh.2",
    )
    return lb.build(res)


def prove_equsalv(sys: System) -> Proof:
    """equsalv: ( ∀ x ( x = y → φ ) ↔ ψ ).
    A version of equsal with a disjoint variable condition, using
    ax6ev instead of ax6e.
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "equsalv")
    hyp1 = lb.hyp("equsalv.nf", "Ⅎ x ψ")
    hyp2 = lb.hyp("equsalv.1", "x = y → ( φ ↔ ψ )")
    # pm5.74i: ( ( x = y → φ ) ↔ ( x = y → ψ ) )
    s1 = lb.ref(
        "s1",
        "( x = y → φ ) ↔ ( x = y → ψ )",
        hyp2,
        ref="pm5.74i",
        note="pm5.74i equsalv.1",
    )
    # albii: ( ∀ x ( x = y → φ ) ↔ ∀ x ( x = y → ψ ) )
    s2 = lb.ref(
        "s2",
        "∀ x ( x = y → φ ) ↔ ∀ x ( x = y → ψ )",
        s1,
        ref="albii",
        note="albii pm5.74i",
    )
    # 19.23: ( ∀ x ( x = y → ψ ) ↔ ( ∃ x x = y → ψ ) )
    s3 = lb.ref(
        "s3",
        "∀ x ( x = y → ψ ) ↔ ( ∃ x x = y → ψ )",
        hyp1,
        ref="19.23",
        note="19.23 equsalv.nf",
    )
    # ax6ev: ∃ x x = y
    s4 = lb.ref(
        "s4",
        "∃ x x = y",
        ref="ax6ev",
        note="ax6ev",
    )
    # a1bi: ( ψ ↔ ( ∃ x x = y → ψ ) )
    s5 = lb.ref(
        "s5",
        "ψ ↔ ( ∃ x x = y → ψ )",
        s4,
        ref="a1bi",
        note="a1bi ax6ev",
    )
    # 3bitr4i: ( ∀ x ( x = y → φ ) ↔ ψ )
    res = lb.ref(
        "res",
        "∀ x ( x = y → φ ) ↔ ψ",
        s3,
        s2,
        s5,
        ref="3bitr4i",
        note="3bitr4i 19.23, albii, a1bi",
    )
    return lb.build(res)


def prove_equsalhw(sys: System) -> Proof:
    """equsalhw: ( ∀ x ( x = y → φ ) ↔ ψ ).
    Hypothesis version of equsalv using nf5i.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "equsalhw")
    hyp1 = lb.hyp("equsalhw.1", "ψ → ∀ x ψ")
    hyp2 = lb.hyp("equsalhw.2", "x = y → ( φ ↔ ψ )")
    # nf5i equsalhw.1: Ⅎ x ψ
    s1 = lb.ref(
        "s1",
        "Ⅎ x ψ",
        hyp1,
        ref="nf5i",
        note="nf5i equsalhw.1",
    )
    # equsalv s1, hyp2: ( ∀ x ( x = y → φ ) ↔ ψ )
    res = lb.ref(
        "res",
        "∀ x ( x = y → φ ) ↔ ψ",
        s1,
        hyp2,
        ref="equsalv",
        note="equsalv nf5i, equsalhw.2",
    )
    return lb.build(res)


def prove_equsex(sys: System) -> Proof:
    """equsex: ∃ x ( x = y ∧ φ ) ↔ ψ.
    From Ⅎ x ψ and the equivalence of φ and ψ under x = y,
    the existential quantifier of the conjunction is equivalent to ψ.
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "equsex")
    hyp1 = lb.hyp("equsal.1", "Ⅎ x ψ")
    hyp2 = lb.hyp("equsal.2", "x = y → ( φ ↔ ψ )")
    # biimpa: ( x = y ∧ φ ) → ψ
    s1 = lb.ref(
        "s1",
        "( x = y ∧ φ ) → ψ",
        hyp2,
        ref="biimpa",
        note="biimpa equsal.2",
    )
    # exlimi: ( x = y ∧ φ ) → ψ, Ⅎ x ψ  ⊢  ∃ x ( x = y ∧ φ ) → ψ
    s2 = lb.ref(
        "s2",
        "∃ x ( x = y ∧ φ ) → ψ",
        hyp1,
        s1,
        ref="exlimi",
        note="exlimi equsal.1, biimpa",
    )
    # equsal: equsal.1 ∧ equsal.2  ⊢  ∀ x ( x = y → φ ) ↔ ψ
    s3 = lb.ref(
        "s3",
        "∀ x ( x = y → φ ) ↔ ψ",
        hyp1,
        hyp2,
        ref="equsal",
        note="equsal",
    )
    # equs4: ∀ x ( x = y → φ ) → ∃ x ( x = y ∧ φ )
    s4 = lb.ref(
        "s4",
        "∀ x ( x = y → φ ) → ∃ x ( x = y ∧ φ )",
        ref="equs4",
        note="equs4",
    )
    # sylbir: ( ∀ x ... ↔ ψ ), ( ∀ x ... → ∃ x ... )  ⊢  ψ → ∃ x ( x = y ∧ φ )
    s5 = lb.ref(
        "s5",
        "ψ → ∃ x ( x = y ∧ φ )",
        s3,
        s4,
        ref="sylbir",
        note="sylbir equsal, equs4",
    )
    # impbii: ( → ) and ( ← )  ⊢  ↔
    res = lb.ref(
        "res",
        "∃ x ( x = y ∧ φ ) ↔ ψ",
        s2,
        s5,
        ref="impbii",
        note="impbii exlimi, sylbir",
    )
    return lb.build(res)


def prove_equsexh(sys: System) -> Proof:
    """equsexh: ∃ x ( x = y ∧ φ ) ↔ ψ.
    Hypothesis version of equsex using nf5i.
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "equsexh")
    hyp1 = lb.hyp("equsalh.1", "ψ → ∀ x ψ")
    hyp2 = lb.hyp("equsalh.2", "x = y → ( φ ↔ ψ )")
    # nf5i equsalh.1: Ⅎ x ψ
    s1 = lb.ref(
        "s1",
        "Ⅎ x ψ",
        hyp1,
        ref="nf5i",
        note="nf5i equsalh.1",
    )
    # equsex s1, hyp2: ∃ x ( x = y ∧ φ ) ↔ ψ
    res = lb.ref(
        "res",
        "∃ x ( x = y ∧ φ ) ↔ ψ",
        s1,
        hyp2,
        ref="equsex",
        note="equsex nf5i, equsalh.2",
    )
    return lb.build(res)


def prove_equsexv(sys: System) -> Proof:
    """equsexv: ∃ x ( x = y ∧ φ ) ↔ ψ.
    A version of equsex with a disjoint variable condition, derived
    from equsalv and equs4v via sylbir and impbii.
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "equsexv")
    hyp1 = lb.hyp("equsalv.nf", "Ⅎ x ψ")
    hyp2 = lb.hyp("equsalv.1", "x = y → ( φ ↔ ψ )")
    # biimpa: ( x = y ∧ φ ) → ψ
    s1 = lb.ref(
        "s1",
        "( x = y ∧ φ ) → ψ",
        hyp2,
        ref="biimpa",
        note="biimpa equsalv.1",
    )
    # exlimi: ( x = y ∧ φ ) → ψ, Ⅎ x ψ  ⊢  ∃ x ( x = y ∧ φ ) → ψ
    s2 = lb.ref(
        "s2",
        "∃ x ( x = y ∧ φ ) → ψ",
        hyp1,
        s1,
        ref="exlimi",
        note="exlimi equsalv.nf, biimpa",
    )
    # equsalv: equsalv.nf ∧ equsalv.1  ⊢  ∀ x ( x = y → φ ) ↔ ψ
    s3 = lb.ref(
        "s3",
        "∀ x ( x = y → φ ) ↔ ψ",
        hyp1,
        hyp2,
        ref="equsalv",
        note="equsalv",
    )
    # equs4v: ∀ x ( x = y → φ ) → ∃ x ( x = y ∧ φ )
    s4 = lb.ref(
        "s4",
        "∀ x ( x = y → φ ) → ∃ x ( x = y ∧ φ )",
        ref="equs4v",
        note="equs4v",
    )
    # sylbir: ( ∀ x ( x = y → φ ) ↔ ψ ), ( ∀ x ( x = y → φ ) → ∃ x ... )  ⊢  ψ → ∃ x ( x = y ∧ φ )
    s5 = lb.ref(
        "s5",
        "ψ → ∃ x ( x = y ∧ φ )",
        s3,
        s4,
        ref="sylbir",
        note="sylbir equsalv, equs4v",
    )
    # impbii: ( ∃ x ... → ψ ), ( ψ → ∃ x ... )  ⊢  ∃ x ( x = y ∧ φ ) ↔ ψ
    res = lb.ref(
        "res",
        "∃ x ( x = y ∧ φ ) ↔ ψ",
        s2,
        s5,
        ref="impbii",
        note="impbii exlimi, sylbir",
    )
    return lb.build(res)


def prove_equsexhv(sys: System) -> Proof:
    """equsexhv: ∃ x ( x = y ∧ φ ) ↔ ψ.
    Version of equsexv with a non-freeness hypothesis instead of a
    disjoint variable condition.
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "equsexhv")
    hyp1 = lb.hyp("equsalhw.1", "ψ → ∀ x ψ")
    hyp2 = lb.hyp("equsalhw.2", "x = y → ( φ ↔ ψ )")
    # nf5i equsalhw.1 → Ⅎ x ψ
    s1 = lb.ref(
        "s1",
        "Ⅎ x ψ",
        hyp1,
        ref="nf5i",
        note="nf5i",
    )
    # equsexv Ⅎ x ψ, equsalhw.2 → ∃ x ( x = y ∧ φ ) ↔ ψ
    res = lb.ref(
        "res",
        "∃ x ( x = y ∧ φ ) ↔ ψ",
        s1,
        hyp2,
        ref="equsexv",
        note="equsexv",
    )
    return lb.build(res)


def prove_equsexALT(sys: System) -> Proof:
    """equsexALT: ∃ x ( x = y ∧ φ ) ↔ ψ.
    Alternative proof of equsex: using pm5.32i via n, exbii,
    19.41, ax6e, and mpbiran via n.
    """
    lb = ProofBuilder(sys, "equsexALT")
    hyp1 = lb.hyp("equsal.1", "Ⅎ x ψ")
    hyp2 = lb.hyp("equsal.2", "x = y → ( φ ↔ ψ )")
    # pm5.32i (conjunction n): ( x = y ∧ φ ) ↔ ( x = y ∧ ψ )
    s1 = lb.ref(
        "s1",
        "( x = y ∧ φ ) ↔ ( x = y ∧ ψ )",
        hyp2,
        ref="pm5.32i",
        note="pm5.32i equsal.2",
    )
    # exbii: ∃ x ( x = y ∧ φ ) ↔ ∃ x ( x = y ∧ ψ )
    s2 = lb.ref(
        "s2",
        "∃ x ( x = y ∧ φ ) ↔ ∃ x ( x = y ∧ ψ )",
        s1,
        ref="exbii",
        note="exbii pm5.32i",
    )
    # 19.41: ∃ x ( x = y ∧ ψ ) ↔ ( ∃ x x = y ∧ ψ )
    s3 = lb.ref(
        "s3",
        "∃ x ( x = y ∧ ψ ) ↔ ( ∃ x x = y ∧ ψ )",
        hyp1,
        ref="19.41",
        note="19.41 equsal.1",
    )
    # ax6e: ∃ x x = y
    s4 = lb.ref(
        "s4",
        "∃ x x = y",
        ref="ax6e",
        note="ax6e",
    )
    # mpbiran (equivalence n): ∃ x ( x = y ∧ ψ ) ↔ ψ
    s5 = lb.ref(
        "s5",
        "∃ x ( x = y ∧ ψ ) ↔ ψ",
        s4,
        s3,
        ref="mpbiran",
        note="mpbiran ax6e, 19.41",
    )
    # bitri: chain s2 and s5
    res = lb.ref(
        "res",
        "∃ x ( x = y ∧ φ ) ↔ ψ",
        s2,
        s5,
        ref="bitri",
        note="bitri",
    )
    return lb.build(res)


def prove_equs5av(sys: System) -> Proof:
    """equs5av: ∃ x ( x = y ∧ ∀ y φ ) → ∀ x ( x = y → φ ).

    If there exists an x such that x = y and ∀ y φ holds, then for
    all x, if x = y then φ.
    (Contributed by NM, 10-Jan-1993.)
    set.mm proof: nfa1 ax12v2 spsd imp exlimi.
    """
    lb = ProofBuilder(sys, "equs5av")
    # nfa1: Ⅎ x ∀ x ( x = y → φ )
    s1 = lb.ref(
        "s1",
        "Ⅎ x ∀ x ( x = y → φ )",
        ref="nfa1",
        note="nfa1",
    )
    # ax12v2: x = y → ( φ → ∀ x ( x = y → φ ) )
    s2 = lb.ref(
        "s2",
        "x = y → ( φ → ∀ x ( x = y → φ ) )",
        ref="ax12v2",
        note="ax12v2",
    )
    # spsd: x = y → ( ∀ y φ → ∀ x ( x = y → φ ) )
    s3 = lb.ref(
        "s3",
        "x = y → ( ∀ y φ → ∀ x ( x = y → φ ) )",
        s2,
        ref="spsd",
        note="spsd ax12v2",
    )
    # imp: ( x = y ∧ ∀ y φ ) → ∀ x ( x = y → φ )
    s4 = lb.ref(
        "s4",
        "( x = y ∧ ∀ y φ ) → ∀ x ( x = y → φ )",
        s3,
        ref="imp",
        note="imp spsd",
    )
    # exlimi: ∃ x ( x = y ∧ ∀ y φ ) → ∀ x ( x = y → φ )
    res = lb.ref(
        "res",
        "∃ x ( x = y ∧ ∀ y φ ) → ∀ x ( x = y → φ )",
        s1,
        s4,
        ref="exlimi",
        note="exlimi nfa1, imp",
    )
    return lb.build(res)


def prove_equs5a(sys: System) -> Proof:
    """equs5a: ∃ x ( x = y ∧ ∀ y φ ) → ∀ x ( x = y → φ ).

    If there exists an x such that x = y and ∀ y φ holds, then for
    all x, if x = y then φ.
    (Contributed by NM, 10-Jan-1993.)
    set.mm proof: nfa1 ax12 imp exlimi.
    """
    lb = ProofBuilder(sys, "equs5a")
    # nfa1: Ⅎ x ∀ x ( x = y → φ )
    s1 = lb.ref(
        "s1",
        "Ⅎ x ∀ x ( x = y → φ )",
        ref="nfa1",
        note="nfa1",
    )
    # ax12: x = y → ( ∀ y φ → ∀ x ( x = y → φ ) )
    s2 = lb.ref(
        "s2",
        "x = y → ( ∀ y φ → ∀ x ( x = y → φ ) )",
        ref="ax12",
        note="ax12",
    )
    # imp: ( x = y ∧ ∀ y φ ) → ∀ x ( x = y → φ )
    s3 = lb.ref(
        "s3",
        "( x = y ∧ ∀ y φ ) → ∀ x ( x = y → φ )",
        s2,
        ref="imp",
        note="imp ax12",
    )
    # exlimi: ∃ x ( x = y ∧ ∀ y φ ) → ∀ x ( x = y → φ )
    res = lb.ref(
        "res",
        "∃ x ( x = y ∧ ∀ y φ ) → ∀ x ( x = y → φ )",
        s1,
        s3,
        ref="exlimi",
        note="exlimi nfa1, imp",
    )
    return lb.build(res)


def prove_equs5aALT(sys: System) -> Proof:
    """equs5aALT: ∃ x ( x = y ∧ ∀ y φ ) → ∀ x ( x = y → φ ).
    If there exists an x such that x = y and ∀ y φ holds, then for
    all x, if x = y then φ.
    (Contributed by NM, 10-Jan-1993.)
    set.mm proof: nfa1 ax-12 imp exlimi.
    """
    lb = ProofBuilder(sys, "equs5aALT")
    # nfa1: Ⅎ x ∀ x ( x = y → φ )
    s1 = lb.ref(
        "s1",
        "Ⅎ x ∀ x ( x = y → φ )",
        ref="nfa1",
        note="nfa1",
    )
    # ax-12: x = y → ( ∀ y φ → ∀ x ( x = y → φ ) )
    s2 = lb.ref(
        "s2",
        "x = y → ( ∀ y φ → ∀ x ( x = y → φ ) )",
        ref="ax-12",
        note="ax-12",
    )
    # imp: ( x = y ∧ ∀ y φ ) → ∀ x ( x = y → φ )
    s3 = lb.ref(
        "s3",
        "( x = y ∧ ∀ y φ ) → ∀ x ( x = y → φ )",
        s2,
        ref="imp",
        note="imp ax-12",
    )
    # exlimi: ∃ x ( x = y ∧ ∀ y φ ) → ∀ x ( x = y → φ )
    res = lb.ref(
        "res",
        "∃ x ( x = y ∧ ∀ y φ ) → ∀ x ( x = y → φ )",
        s1,
        s3,
        ref="exlimi",
        note="exlimi nfa1, imp",
    )
    return lb.build(res)


def prove_equs5eALT(sys: System) -> Proof:
    """equs5eALT: ∃ x ( x = y ∧ φ ) → ∀ x ( x = y → ∃ y φ ).
    If there exists an x such that x = y and φ holds, then for all x,
    if x = y then ∃ y φ.
    (Contributed by NM, 10-Jan-1993.)
    set.mm proof: nfa1 hbe1 19.23bi ax-12 syl5 imp exlimi.
    """
    lb = ProofBuilder(sys, "equs5eALT")
    # nfa1: Ⅎ x ∀ x ( x = y → ∃ y φ )
    s1 = lb.ref(
        "s1",
        "Ⅎ x ∀ x ( x = y → ∃ y φ )",
        ref="nfa1",
        note="nfa1",
    )
    # hbe1: ∃ y φ → ∀ y ∃ y φ
    s2 = lb.ref(
        "s2",
        "∃ y φ → ∀ y ∃ y φ",
        ref="hbe1",
        note="hbe1",
    )
    # 19.23bi: φ → ∀ y ∃ y φ
    s3 = lb.ref(
        "s3",
        "φ → ∀ y ∃ y φ",
        s2,
        ref="19.23bi",
        note="19.23bi hbe1",
    )
    # ax-12: x = y → ( ∀ y ∃ y φ → ∀ x ( x = y → ∃ y φ ) )
    s4 = lb.ref(
        "s4",
        "x = y → ( ∀ y ∃ y φ → ∀ x ( x = y → ∃ y φ ) )",
        ref="ax-12",
        note="ax-12",
    )
    # syl5: x = y → ( φ → ∀ x ( x = y → ∃ y φ ) )
    s5 = lb.ref(
        "s5",
        "x = y → ( φ → ∀ x ( x = y → ∃ y φ ) )",
        s3,
        s4,
        ref="syl5",
        note="syl5 19.23bi, ax-12",
    )
    # imp: ( x = y ∧ φ ) → ∀ x ( x = y → ∃ y φ )
    s6 = lb.ref(
        "s6",
        "( x = y ∧ φ ) → ∀ x ( x = y → ∃ y φ )",
        s5,
        ref="imp",
        note="imp syl5",
    )
    # exlimi: ∃ x ( x = y ∧ φ ) → ∀ x ( x = y → ∃ y φ )
    res = lb.ref(
        "res",
        "∃ x ( x = y ∧ φ ) → ∀ x ( x = y → ∃ y φ )",
        s1,
        s6,
        ref="exlimi",
        note="exlimi nfa1, imp",
    )
    return lb.build(res)


def prove_equs5e(sys: System) -> Proof:
    """equs5e: ∃ x ( x = y ∧ φ ) → ∀ x ( x = y → ∃ y φ ).

    If there exists an x such that x = y and φ holds, then for all x,
    if x = y then ∃ y φ.
    (Contributed by NM, 10-Jan-1993.)
    set.mm proof: nfa1 ax12 hbe1 19.23bi impel exlimi.
    """
    lb = ProofBuilder(sys, "equs5e")
    # nfa1: Ⅎ x ∀ x ( x = y → ∃ y φ )
    s1 = lb.ref(
        "s1",
        "Ⅎ x ∀ x ( x = y → ∃ y φ )",
        ref="nfa1",
        note="nfa1",
    )
    # hbe1: ∃ y φ → ∀ y ∃ y φ
    s2 = lb.ref(
        "s2",
        "∃ y φ → ∀ y ∃ y φ",
        ref="hbe1",
        note="hbe1",
    )
    # 19.23bi: φ → ∀ y ∃ y φ
    s3 = lb.ref(
        "s3",
        "φ → ∀ y ∃ y φ",
        s2,
        ref="19.23bi",
        note="19.23bi hbe1",
    )
    # ax-12: x = y → ( ∀ y ∃ y φ → ∀ x ( x = y → ∃ y φ ) )
    s4 = lb.ref(
        "s4",
        "x = y → ( ∀ y ∃ y φ → ∀ x ( x = y → ∃ y φ ) )",
        ref="ax-12",
        note="ax-12",
    )
    # impel: ( x = y ∧ φ ) → ∀ x ( x = y → ∃ y φ )
    s5 = lb.ref(
        "s5",
        "( x = y ∧ φ ) → ∀ x ( x = y → ∃ y φ )",
        s4,
        s3,
        ref="impel",
        note="impel ax-12, 19.23bi",
    )
    # exlimi: ∃ x ( x = y ∧ φ ) → ∀ x ( x = y → ∃ y φ )
    res = lb.ref(
        "res",
        "∃ x ( x = y ∧ φ ) → ∀ x ( x = y → ∃ y φ )",
        s1,
        s5,
        ref="exlimi",
        note="exlimi nfa1, impel",
    )
    return lb.build(res)


def prove_euimmo(sys: System) -> Proof:
    """euimmo: ∀ x ( φ → ψ ) → ( ∃! x ψ → ∃* x φ ).
    If φ implies ψ for all x, then unique existence of ψ implies
    at most one φ.  From eumo and moim via syl5.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "euimmo")
    # eumo: ∃! x ψ → ∃* x ψ
    s1 = lb.ref(
        "s1",
        "∃! x ψ → ∃* x ψ",
        ref="eumo",
        note="eumo",
    )
    # moim: ∀ x ( φ → ψ ) → ( ∃* x ψ → ∃* x φ )
    s2 = lb.ref(
        "s2",
        "∀ x ( φ → ψ ) → ( ∃* x ψ → ∃* x φ )",
        ref="moim",
        note="moim",
    )
    # syl5: chain s1 (∃! x ψ → ∃* x ψ) and s2 (∀ x (φ → ψ) → (∃* x ψ → ∃* x φ))
    # to get ∀ x (φ → ψ) → (∃! x ψ → ∃* x φ)
    res = lb.ref(
        "res",
        "∀ x ( φ → ψ ) → ( ∃! x ψ → ∃* x φ )",
        s1,
        s2,
        ref="syl5",
        note="syl5 eumo, moim",
    )
    return lb.build(res)


def prove_euim(sys: System) -> Proof:
    """euim: ( ∃ x φ ∧ ∀ x ( φ → ψ ) ) → ( ∃! x ψ → ∃! x φ ).
    From euimmo, exmoeub via biimpd and sylan9r.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "euim")
    # euimmo: ∀ x ( φ → ψ ) → ( ∃! x ψ → ∃* x φ )
    s1 = lb.ref(
        "s1",
        "∀ x ( φ → ψ ) → ( ∃! x ψ → ∃* x φ )",
        ref="euimmo",
        note="euimmo",
    )
    # exmoeub: ∃ x φ → ( ∃* x φ ↔ ∃! x φ )
    s2 = lb.ref(
        "s2",
        "∃ x φ → ( ∃* x φ ↔ ∃! x φ )",
        ref="exmoeub",
        note="exmoeub",
    )
    # biimpd: convert ↔ to →
    s3 = lb.ref(
        "s3",
        "∃ x φ → ( ∃* x φ → ∃! x φ )",
        s2,
        ref="biimpd",
        note="biimpd exmoeub",
    )
    # sylan9r: combine euimmo and biimpd
    res = lb.ref(
        "res",
        "( ∃ x φ ∧ ∀ x ( φ → ψ ) ) → ( ∃! x ψ → ∃! x φ )",
        s1,
        s3,
        ref="sylan9r",
        note="sylan9r euimmo, biimpd",
    )
    return lb.build(res)


def prove_2eumo(sys: System) -> Proof:
    """2eumo: ∃! x ∃* y φ → ∃* x ∃! y φ.
    Existence of a unique x such that there exists at most one y
    satisfying φ implies there exists at most one x such that there
    exists a unique y satisfying φ.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "2eumo")
    # eumo: ∃! y φ → ∃* y φ
    s1 = lb.ref(
        "s1",
        "∃! y φ → ∃* y φ",
        ref="eumo",
        note="eumo",
    )
    # euimmo: ∀ x ( φ → ψ ) → ( ∃! x ψ → ∃* x φ )
    # with φ ← ∃! y φ, ψ ← ∃* y φ
    s2 = lb.ref(
        "s2",
        "∀ x ( ∃! y φ → ∃* y φ ) → ( ∃! x ∃* y φ → ∃* x ∃! y φ )",
        ref="euimmo",
        note="euimmo",
    )
    # mpg: combine euimmo (major) and eumo (minor)
    res = lb.ref(
        "res",
        "∃! x ∃* y φ → ∃* x ∃! y φ",
        s2,
        s1,
        ref="mpg",
        note="mpg euimmo, eumo",
    )
    return lb.build(res)


def prove_eupick(sys: System) -> Proof:
    """eupick: ( ∃! x φ ∧ ∃ x ( φ ∧ ψ ) ) → ( φ → ψ ).
    If there exists a unique x such that φ and there also exists an
    x such that both φ and ψ hold, then φ implies ψ.
    (Contributed by NM, 26-Jul-1995.)
    """
    lb = ProofBuilder(sys, "eupick")
    # eumo: ∃! x φ → ∃* x φ
    s1 = lb.ref(
        "s1",
        "∃! x φ → ∃* x φ",
        ref="eumo",
        note="eumo",
    )
    # mopick: ( ∃* x φ ∧ ∃ x ( φ ∧ ψ ) ) → ( φ → ψ )
    s2 = lb.ref(
        "s2",
        "( ∃* x φ ∧ ∃ x ( φ ∧ ψ ) ) → ( φ → ψ )",
        ref="mopick",
        note="mopick",
    )
    # sylan: ( ∃! x φ ∧ ∃ x ( φ ∧ ψ ) ) → ( φ → ψ )
    res = lb.ref(
        "res",
        "( ∃! x φ ∧ ∃ x ( φ ∧ ψ ) ) → ( φ → ψ )",
        s1,
        s2,
        ref="sylan",
        note="sylan eumo, mopick",
    )
    return lb.build(res)


def prove_19_32(sys: System) -> Proof:
    """19.32: ∀ x ( φ ∨ ψ ) ↔ ( φ ∨ ∀ x ψ ).
    Universal quantifier distributes over disjunction when the first
    disjunct does not contain the bound variable.
    """
    lb = ProofBuilder(sys, "19.32")
    hyp = lb.hyp("19.32.1", "Ⅎ x φ")
    # nfn 19.32.1: Ⅎ x ¬ φ
    s1 = lb.ref(
        "s1",
        "Ⅎ x ¬ φ",
        hyp,
        ref="nfn",
        note="nfn 19.32.1",
    )
    # 19.21 with s1: ∀ x ( ¬ φ → ψ ) ↔ ( ¬ φ → ∀ x ψ )
    s2 = lb.ref(
        "s2",
        "∀ x ( ¬ φ → ψ ) ↔ ( ¬ φ → ∀ x ψ )",
        s1,
        ref="19.21",
        note="19.21 nfn",
    )
    # df-or: ( φ ∨ ψ ) ↔ ( ¬ φ → ψ )
    s3 = lb.ref(
        "s3",
        "( φ ∨ ψ ) ↔ ( ¬ φ → ψ )",
        ref="df-or",
        note="df-or",
    )
    # albii s3: ∀ x ( φ ∨ ψ ) ↔ ∀ x ( ¬ φ → ψ )
    s4 = lb.ref(
        "s4",
        "∀ x ( φ ∨ ψ ) ↔ ∀ x ( ¬ φ → ψ )",
        s3,
        ref="albii",
        note="albii df-or",
    )
    # df-or: ( φ ∨ ∀ x ψ ) ↔ ( ¬ φ → ∀ x ψ )
    s5 = lb.ref(
        "s5",
        "( φ ∨ ∀ x ψ ) ↔ ( ¬ φ → ∀ x ψ )",
        ref="df-or",
        note="df-or",
    )
    # 3bitr4i: chain s2, s4, s5 → ∀ x ( φ ∨ ψ ) ↔ ( φ ∨ ∀ x ψ )
    res = lb.ref(
        "res",
        "∀ x ( φ ∨ ψ ) ↔ ( φ ∨ ∀ x ψ )",
        s2,
        s4,
        s5,
        ref="3bitr4i",
        note="3bitr4i 19.21, albii, df-or",
    )
    return lb.build(res)


def prove_19_31(sys: System) -> Proof:
    """19.31: ∀ x ( φ ∨ ψ ) ↔ ( ∀ x φ ∨ ψ ).
    Universal quantifier distributes over disjunction when the second
    disjunct does not contain the bound variable.
    """
    lb = ProofBuilder(sys, "19.31")
    hyp = lb.hyp("19.31.1", "Ⅎ x ψ")
    # orcom: ( φ ∨ ψ ) ↔ ( ψ ∨ φ )
    s1 = lb.ref(
        "s1",
        "( φ ∨ ψ ) ↔ ( ψ ∨ φ )",
        ref="orcom",
        note="orcom",
    )
    # albii orcom: ∀ x ( φ ∨ ψ ) ↔ ∀ x ( ψ ∨ φ )
    s2 = lb.ref(
        "s2",
        "∀ x ( φ ∨ ψ ) ↔ ∀ x ( ψ ∨ φ )",
        s1,
        ref="albii",
        note="albii orcom",
    )
    # 19.32 19.31.1: ∀ x ( ψ ∨ φ ) ↔ ( ψ ∨ ∀ x φ )
    s3 = lb.ref(
        "s3",
        "∀ x ( ψ ∨ φ ) ↔ ( ψ ∨ ∀ x φ )",
        hyp,
        ref="19.32",
        note="19.32 19.31.1",
    )
    # orcom: ( ψ ∨ ∀ x φ ) ↔ ( ∀ x φ ∨ ψ )
    s4 = lb.ref(
        "s4",
        "( ψ ∨ ∀ x φ ) ↔ ( ∀ x φ ∨ ψ )",
        ref="orcom",
        note="orcom",
    )
    # bitri s2, s3: ∀ x ( φ ∨ ψ ) ↔ ( ψ ∨ ∀ x φ )
    s5 = lb.ref(
        "s5",
        "∀ x ( φ ∨ ψ ) ↔ ( ψ ∨ ∀ x φ )",
        s2,
        s3,
        ref="bitri",
        note="bitri albii, 19.32",
    )
    # bitri s5, s4: ∀ x ( φ ∨ ψ ) ↔ ( ∀ x φ ∨ ψ )
    res = lb.ref(
        "res",
        "∀ x ( φ ∨ ψ ) ↔ ( ∀ x φ ∨ ψ )",
        s5,
        s4,
        ref="bitri",
        note="bitri chain, orcom",
    )
    return lb.build(res)


def prove_exrot3(sys: System) -> Proof:
    """exrot3: ∃ x ∃ y ∃ z φ ↔ ∃ y ∃ z ∃ x φ.
    Rotation of existential quantifiers.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "exrot3")
    # excom13: ∃ x ∃ y ∃ z φ ↔ ∃ z ∃ y ∃ x φ
    s1 = lb.ref(
        "s1",
        "∃ x ∃ y ∃ z φ ↔ ∃ z ∃ y ∃ x φ",
        ref="excom13",
        note="excom13",
    )
    # excom: ∃ z ∃ y ∃ x φ ↔ ∃ y ∃ z ∃ x φ
    s2 = lb.ref(
        "s2",
        "∃ z ∃ y ∃ x φ ↔ ∃ y ∃ z ∃ x φ",
        ref="excom",
        note="excom",
    )
    # bitri: chain the two biconditionals
    res = lb.ref(
        "res",
        "∃ x ∃ y ∃ z φ ↔ ∃ y ∃ z ∃ x φ",
        s1,
        s2,
        ref="bitri",
        note="bitri excom13, excom",
    )
    return lb.build(res)


def prove_exrot4(sys: System) -> Proof:
    """exrot4: ∃ x ∃ y ∃ z ∃ w φ ↔ ∃ z ∃ w ∃ x ∃ y φ.
    Rotation of four existential quantifiers.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "exrot4")
    # excom13 (with φ = ∃ w φ):
    # ∃ x ∃ y ∃ z ∃ w φ ↔ ∃ z ∃ y ∃ x ∃ w φ
    s1 = lb.ref(
        "s1",
        "∃ x ∃ y ∃ z ∃ w φ ↔ ∃ z ∃ y ∃ x ∃ w φ",
        ref="excom13",
        note="excom13",
    )
    # excom13 (with variables y, x, w):
    # ∃ y ∃ x ∃ w φ ↔ ∃ w ∃ x ∃ y φ
    s2 = lb.ref(
        "s2",
        "∃ y ∃ x ∃ w φ ↔ ∃ w ∃ x ∃ y φ",
        ref="excom13",
        note="excom13",
    )
    # exbii (∃ z prefix on s2):
    # ∃ z ∃ y ∃ x ∃ w φ ↔ ∃ z ∃ w ∃ x ∃ y φ
    s3 = lb.ref(
        "s3",
        "∃ z ∃ y ∃ x ∃ w φ ↔ ∃ z ∃ w ∃ x ∃ y φ",
        s2,
        ref="exbii",
        note="exbii excom13",
    )
    # bitri: chain s1 and s3
    res = lb.ref(
        "res",
        "∃ x ∃ y ∃ z ∃ w φ ↔ ∃ z ∃ w ∃ x ∃ y φ",
        s1,
        s3,
        ref="bitri",
        note="bitri excom13, exbii",
    )
    return lb.build(res)


def prove_nfexhe(sys: System) -> Proof:
    """nfexhe: Ⅎ x ∃ y φ.
    Given that the existential implies the formula (∃ x φ → φ),
    prove that ∃ y φ is not free in x.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "nfexhe")
    hyp = lb.hyp("nfexhe.1", "∃ x φ → φ")
    # hbe1: ∃ x ∃ y φ → ∀ x ∃ x ∃ y φ
    s1 = lb.ref(
        "s1",
        "∃ x ∃ y φ → ∀ x ∃ x ∃ y φ",
        ref="hbe1",
        note="hbe1",
    )
    # excomim: ∃ x ∃ y φ → ∃ y ∃ x φ
    s2 = lb.ref(
        "s2",
        "∃ x ∃ y φ → ∃ y ∃ x φ",
        ref="excomim",
        note="excomim",
    )
    # eximi nfexhe.1: ∃ y ∃ x φ → ∃ y φ
    s3 = lb.ref(
        "s3",
        "∃ y ∃ x φ → ∃ y φ",
        hyp,
        ref="eximi",
        note="eximi nfexhe.1",
    )
    # syl s2, s3: ∃ x ∃ y φ → ∃ y φ
    s4 = lb.ref(
        "s4",
        "∃ x ∃ y φ → ∃ y φ",
        s2,
        s3,
        ref="syl",
        note="syl excomim, eximi",
    )
    # alrimih s1, s4: ∃ x ∃ y φ → ∀ x ∃ y φ
    s5 = lb.ref(
        "s5",
        "∃ x ∃ y φ → ∀ x ∃ y φ",
        s1,
        s4,
        ref="alrimih",
        note="alrimih hbe1, syl",
    )
    # nfi s5: Ⅎ x ∃ y φ
    res = lb.ref(
        "res",
        "Ⅎ x ∃ y φ",
        s5,
        ref="nfi",
        note="nfi alrimih",
    )
    return lb.build(res)


def prove_nfexa2(sys: System) -> Proof:
    """nfexa2: Ⅎ x ∃ y ∀ x φ.
    x is not free in the existential quantifier of a universally
    quantified formula.  (Contributed by NM, 30-Jun-1993.)
    """
    lb = ProofBuilder(sys, "nfexa2")
    # hbe1a: ∃ x ∀ x φ → ∀ x φ
    s1 = lb.ref(
        "s1",
        "∃ x ∀ x φ → ∀ x φ",
        ref="hbe1a",
        note="hbe1a",
    )
    # nfexhe with hbe1a as the hypothesis: Ⅎ x ∃ y ∀ x φ
    res = lb.ref(
        "res",
        "Ⅎ x ∃ y ∀ x φ",
        s1,
        ref="nfexhe",
        note="nfexhe hbe1a",
    )
    return lb.build(res)


def prove_nf6(sys: System) -> Proof:
    """nf6: Ⅎ x φ ↔ ∀ x ( ∃ x φ → φ ).
    Equivalent definition of 'not free': the existentially-quantified
    particularization of φ is universally quantified.
    (Contributed by NM, 12-Mar-1993.)
    """
    lb = ProofBuilder(sys, "nf6")
    # df-nf: (Ⅎ x φ) ↔ (∃ x φ → ∀ x φ)
    s1 = lb.ref("s1", "Ⅎ x φ ↔ ( ∃ x φ → ∀ x φ )", ref="df-nf", note="df-nf")
    # nfe1: Ⅎ x ∃ x φ
    s2 = lb.ref("s2", "Ⅎ x ∃ x φ", ref="nfe1", note="nfe1")
    # 19.21 with hypothesis Ⅎ x ∃ x φ:
    # ∀ x ( ∃ x φ → φ ) ↔ ( ∃ x φ → ∀ x φ )
    s3 = lb.ref(
        "s3",
        "∀ x ( ∃ x φ → φ ) ↔ ( ∃ x φ → ∀ x φ )",
        s2,
        ref="19.21",
        note="19.21 nfe1",
    )
    # bitr4i: (Ⅎ x φ ↔ (∃ x φ → ∀ x φ)), (∀ x (∃ x φ → φ) ↔ (∃ x φ → ∀ x φ))
    # → Ⅎ x φ ↔ ∀ x ( ∃ x φ → φ )
    res = lb.ref(
        "res",
        "Ⅎ x φ ↔ ∀ x ( ∃ x φ → φ )",
        s1,
        s3,
        ref="bitr4i",
        note="bitr4i df-nf, 19.21",
    )
    return lb.build(res)


def prove_nf5(sys: System) -> Proof:
    """nf5: Ⅎ x φ ↔ ∀ x ( φ → ∀ x φ ).
    Equivalence form of nf5-1: the not-free property is equivalent
    to universal quantification of φ implying itself.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "nf5")
    # df-nf: Ⅎ x φ ↔ ( ∃ x φ → ∀ x φ )
    s1 = lb.ref(
        "s1",
        "Ⅎ x φ ↔ ( ∃ x φ → ∀ x φ )",
        ref="df-nf",
        note="df-nf",
    )
    # nfa1: Ⅎ x ∀ x φ
    s2 = lb.ref(
        "s2",
        "Ⅎ x ∀ x φ",
        ref="nfa1",
        note="nfa1",
    )
    # 19.23 with s2 as hypothesis: ∀ x ( φ → ∀ x φ ) ↔ ( ∃ x φ → ∀ x φ )
    s3 = lb.ref(
        "s3",
        "∀ x ( φ → ∀ x φ ) ↔ ( ∃ x φ → ∀ x φ )",
        s2,
        ref="19.23",
        note="19.23 nfa1",
    )
    # bitr4i: chain s1 and s3
    res = lb.ref(
        "res",
        "Ⅎ x φ ↔ ∀ x ( φ → ∀ x φ )",
        s1,
        s3,
        ref="bitr4i",
        note="bitr4i df-nf, 19.23",
    )
    return lb.build(res)


def prove_nexd(sys: System) -> Proof:
    """nexd: φ → ¬ ∃ x ψ.
    Deduction form of nex. The first hypothesis provides the Ⅎ condition;
    the second hypothesis provides the negated consequent. nf5ri converts
    Ⅎ to ∀, nexdh combines them.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "nexd")
    hyp1 = lb.hyp("nexd.1", "Ⅎ x φ")
    hyp2 = lb.hyp("nexd.2", "φ → ¬ ψ")
    # nf5ri: Ⅎ x φ ⊢ φ → ∀ x φ
    s1 = lb.ref(
        "s1",
        "φ → ∀ x φ",
        hyp1,
        ref="nf5ri",
        note="nf5ri nexd.1",
    )
    # nexdh: (φ → ∀ x φ), (φ → ¬ ψ) ⊢ φ → ¬ ∃ x ψ
    res = lb.ref(
        "res",
        "φ → ¬ ∃ x ψ",
        s1,
        hyp2,
        ref="nexdh",
        note="nexdh nf5ri, nexd.2",
    )
    return lb.build(res)


def prove_nexr(sys: System) -> Proof:
    """nexr: ¬ φ.
    Inference: from ¬ ∃ x φ, conclude ¬ φ.  Uses 19.8a and mto.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "nexr")
    h1 = lb.hyp("nexr.1", "¬ ∃ x φ")
    s1 = lb.ref("s1", "φ → ∃ x φ", ref="19.8a", note="19.8a")
    res = lb.ref("res", "¬ φ", h1, s1, ref="mto", note="mto")
    return lb.build(res)


def prove_aaan(sys: System) -> Proof:
    """aaan: ∀ x ∀ y ( φ ∧ ψ ) ↔ ( ∀ x φ ∧ ∀ y ψ ).
    Universal quantifier distributes over conjunction when each
    conjunct has only the relevant variable free.  Variant of 19.26
    with asymmetric not-free conditions.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "aaan")
    hyp1 = lb.hyp("aaan.1", "Ⅎ y φ")
    hyp2 = lb.hyp("aaan.2", "Ⅎ x ψ")
    # 19.26-2: ∀ x ∀ y ( φ ∧ ψ ) ↔ ( ∀ x ∀ y φ ∧ ∀ x ∀ y ψ )
    s1 = lb.ref(
        "s1",
        "∀ x ∀ y ( φ ∧ ψ ) ↔ ( ∀ x ∀ y φ ∧ ∀ x ∀ y ψ )",
        ref="19.26-2",
        note="19.26-2",
    )
    # 19.3 with aaan.1: ∀ y φ ↔ φ
    s2 = lb.ref(
        "s2",
        "∀ y φ ↔ φ",
        hyp1,
        ref="19.3",
        note="19.3 aaan.1",
    )
    # albii s2: ∀ x ∀ y φ ↔ ∀ x φ
    s3 = lb.ref(
        "s3",
        "∀ x ∀ y φ ↔ ∀ x φ",
        s2,
        ref="albii",
        note="albii 19.3",
    )
    # 19.3 with aaan.2: ∀ x ψ ↔ ψ
    s4 = lb.ref(
        "s4",
        "∀ x ψ ↔ ψ",
        hyp2,
        ref="19.3",
        note="19.3 aaan.2",
    )
    # albii s4 (y-quantified): ∀ y ∀ x ψ ↔ ∀ y ψ
    s5 = lb.ref(
        "s5",
        "∀ y ∀ x ψ ↔ ∀ y ψ",
        s4,
        ref="albii",
        note="albii 19.3",
    )
    # alcom: ∀ x ∀ y ψ ↔ ∀ y ∀ x ψ
    s6 = lb.ref(
        "s6",
        "∀ x ∀ y ψ ↔ ∀ y ∀ x ψ",
        ref="alcom",
        note="alcom",
    )
    # bitri s6, s5: ∀ x ∀ y ψ ↔ ∀ y ψ
    s7 = lb.ref(
        "s7",
        "∀ x ∀ y ψ ↔ ∀ y ψ",
        s6,
        s5,
        ref="bitri",
        note="bitri alcom, albii",
    )
    # anbi12i s3, s7: ( ∀ x ∀ y φ ∧ ∀ x ∀ y ψ ) ↔ ( ∀ x φ ∧ ∀ y ψ )
    s8 = lb.ref(
        "s8",
        "( ∀ x ∀ y φ ∧ ∀ x ∀ y ψ ) ↔ ( ∀ x φ ∧ ∀ y ψ )",
        s3,
        s7,
        ref="anbi12i",
        note="anbi12i",
    )
    # bitri s1, s8: ∀ x ∀ y ( φ ∧ ψ ) ↔ ( ∀ x φ ∧ ∀ y ψ )
    res = lb.ref(
        "res",
        "∀ x ∀ y ( φ ∧ ψ ) ↔ ( ∀ x φ ∧ ∀ y ψ )",
        s1,
        s8,
        ref="bitri",
        note="bitri 19.26-2, anbi12i",
    )
    return lb.build(res)


def prove_nfnf(sys: System) -> Proof:
    """nfnf: Ⅎ x Ⅎ y φ.
    If x is not free in φ, then x is also not free in the statement
    that y is not free in φ.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "nfnf")
    hyp = lb.hyp("nfnf.1", "Ⅎ x φ")
    # df-nf: Ⅎ y φ ↔ ( ∃ y φ → ∀ y φ )
    s1 = lb.ref(
        "s1",
        "Ⅎ y φ ↔ ( ∃ y φ → ∀ y φ )",
        ref="df-nf",
        note="df-nf",
    )
    # nfex: Ⅎ x ∃ y φ
    s2 = lb.ref(
        "s2",
        "Ⅎ x ∃ y φ",
        hyp,
        ref="nfex",
        note="nfex nfnf.1",
    )
    # nfal: Ⅎ x ∀ y φ
    s3 = lb.ref(
        "s3",
        "Ⅎ x ∀ y φ",
        hyp,
        ref="nfal",
        note="nfal nfnf.1",
    )
    # nfim: Ⅎ x ( ∃ y φ → ∀ y φ )
    s4 = lb.ref(
        "s4",
        "Ⅎ x ( ∃ y φ → ∀ y φ )",
        s2,
        s3,
        ref="nfim",
        note="nfim nfex, nfal",
    )
    # nfxfr: Ⅎ x Ⅎ y φ
    res = lb.ref(
        "res",
        "Ⅎ x Ⅎ y φ",
        s1,
        s4,
        ref="nfxfr",
        note="nfxfr df-nf, nfim",
    )
    return lb.build(res)


def prove_qexmid(sys: System) -> Proof:
    """qexmid: ∃ x ( φ → ∀ x φ ).
    Existence of x such that φ implies universal quantification of φ
    ("quantified excluded middle").
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "qexmid")
    # 19.8a with ∀ x φ substituted for φ: ∀ x φ → ∃ x ∀ x φ
    s1 = lb.ref(
        "s1",
        "∀ x φ → ∃ x ∀ x φ",
        ref="19.8a",
        note="19.8a",
    )
    # 19.35ri with the hypothesis from s1: ∃ x ( φ → ∀ x φ )
    res = lb.ref(
        "res",
        "∃ x ( φ → ∀ x φ )",
        s1,
        ref="19.35ri",
        note="19.35ri",
    )
    return lb.build(res)


def prove_ru0(sys: System) -> Proof:
    """ru0: ¬ ∀ x ( x ∈ y ↔ ¬ x ∈ x ).
    Russell's paradox: no formula can assert that a set contains exactly
    those sets that do not contain themselves.
    (Contributed by NM, 7-Aug-1994.)
    """
    lb = ProofBuilder(sys, "ru0")
    # 1. pm5.19 with φ := y ∈ y: ¬ (y ∈ y ↔ ¬ y ∈ y)
    s1 = lb.ref(
        "s1",
        "¬ ( y ∈ y ↔ ¬ y ∈ y )",
        ref="pm5.19",
        note="pm5.19",
    )
    # 2. elequ1 with z := y: x = y → (x ∈ y ↔ y ∈ y)
    s2 = lb.ref(
        "s2",
        "x = y → ( x ∈ y ↔ y ∈ y )",
        ref="elequ1",
        note="elequ1",
    )
    # 3. elequ12 with z := x, t := y: (x = y ∧ x = y) → (x ∈ x ↔ y ∈ y)
    s3 = lb.ref(
        "s3",
        "( x = y ∧ x = y ) → ( x ∈ x ↔ y ∈ y )",
        ref="elequ12",
        note="elequ12",
    )
    # 4. anidms: from (φ ∧ φ) → ψ derive φ → ψ
    s4 = lb.ref(
        "s4",
        "x = y → ( x ∈ x ↔ y ∈ y )",
        s3,
        ref="anidms",
        note="anidms",
    )
    # 5. notbid: from φ → (ψ ↔ χ) derive φ → (¬ ψ ↔ ¬ χ)
    s5 = lb.ref(
        "s5",
        "x = y → ( ¬ x ∈ x ↔ ¬ y ∈ y )",
        s4,
        ref="notbid",
        note="notbid",
    )
    # 6. bibi12d with s2 and s5:
    #    bibi12d.1: x = y → (x ∈ y ↔ y ∈ y)
    #    bibi12d.2: x = y → (¬ x ∈ x ↔ ¬ y ∈ y)
    s6 = lb.ref(
        "s6",
        "x = y → ( ( x ∈ y ↔ ¬ x ∈ x ) ↔ ( y ∈ y ↔ ¬ y ∈ y ) )",
        s2,
        s5,
        ref="bibi12d",
        note="bibi12d",
    )
    # 7. spvv: from x = y → (φ ↔ ψ) derive ∀x φ → ψ
    s7 = lb.ref(
        "s7",
        "∀ x ( x ∈ y ↔ ¬ x ∈ x ) → ( y ∈ y ↔ ¬ y ∈ y )",
        s6,
        ref="spvv",
        note="spvv",
    )
    # 8. mto: from ¬ ψ and (φ → ψ) derive ¬ φ
    res = lb.ref(
        "res",
        "¬ ∀ x ( x ∈ y ↔ ¬ x ∈ x )",
        s1,
        s7,
        ref="mto",
        note="mto",
    )
    return lb.build(res)


def prove_cbv1(sys: System) -> Proof:
    """cbv1: φ → ( ∀ x ψ → ∀ y χ ).
    Change bound variables in an implication of universal quantifiers
    using implicit substitution.  Uses nfim1 for not-free conditions
    on the inner implications, com12 to commute antecedents, a2d to
    distribute the antecedent, cbv3 for bound-variable change,
    19.21 for universal distribution, 3imtr3i to combine
    biconditionals, and pm2.86i for the final form.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "cbv1")
    hyp_nf1 = lb.hyp("cbv1.1", "Ⅎ x φ")
    hyp_nf2 = lb.hyp("cbv1.2", "Ⅎ y φ")
    hyp_nf3 = lb.hyp("cbv1.3", "φ → Ⅎ y ψ")
    hyp_nf4 = lb.hyp("cbv1.4", "φ → Ⅎ x χ")
    hyp_imp = lb.hyp("cbv1.5", "φ → ( x = y → ( ψ → χ ) )")
    # nfim1: Ⅎ y φ, φ → Ⅎ y ψ ⊢ Ⅎ y ( φ → ψ )
    s_nf1 = lb.ref(
        "s_nf1",
        "Ⅎ y ( φ → ψ )",
        hyp_nf2,
        hyp_nf3,
        ref="nfim1",
        note="nfim1 cbv1.2, cbv1.3",
    )
    # nfim1: Ⅎ x φ, φ → Ⅎ x χ ⊢ Ⅎ x ( φ → χ )
    s_nf2 = lb.ref(
        "s_nf2",
        "Ⅎ x ( φ → χ )",
        hyp_nf1,
        hyp_nf4,
        ref="nfim1",
        note="nfim1 cbv1.1, cbv1.4",
    )
    # com12: φ → ( x = y → ( ψ → χ ) ) ⊢ ( x = y ) → ( φ → ( ψ → χ ) )
    s_com12 = lb.ref(
        "s_com12",
        "( x = y ) → ( φ → ( ψ → χ ) )",
        hyp_imp,
        ref="com12",
        note="com12 cbv1.5",
    )
    # a2d: ( x = y ) → ( φ → ( ψ → χ ) ) ⊢ ( x = y ) → ( ( φ → ψ ) → ( φ → χ ) )
    s_a2d = lb.ref(
        "s_a2d",
        "( x = y ) → ( ( φ → ψ ) → ( φ → χ ) )",
        s_com12,
        ref="a2d",
        note="a2d com12",
    )
    # cbv3: Ⅎ y ( φ → ψ ), Ⅎ x ( φ → χ ), ( x = y ) → ( ( φ → ψ ) → ( φ → χ ) )
    # ⊢ ∀ x ( φ → ψ ) → ∀ y ( φ → χ )
    s_cbv3 = lb.ref(
        "s_cbv3",
        "∀ x ( φ → ψ ) → ∀ y ( φ → χ )",
        s_nf1,
        s_nf2,
        s_a2d,
        ref="cbv3",
        note="cbv3 nfim1, nfim1, a2d",
    )
    # 19.21: Ⅎ x φ ⊢ ∀ x ( φ → ψ ) ↔ ( φ → ∀ x ψ )
    s_19_21a = lb.ref(
        "s_19_21a",
        "∀ x ( φ → ψ ) ↔ ( φ → ∀ x ψ )",
        hyp_nf1,
        ref="19.21",
        note="19.21 cbv1.1",
    )
    # 19.21: Ⅎ y φ ⊢ ∀ y ( φ → χ ) ↔ ( φ → ∀ y χ )
    s_19_21b = lb.ref(
        "s_19_21b",
        "∀ y ( φ → χ ) ↔ ( φ → ∀ y χ )",
        hyp_nf2,
        ref="19.21",
        note="19.21 cbv1.2",
    )
    # 3imtr3i: combine cbv3 result with the two 19.21 biconditionals
    s_3imtr3i = lb.ref(
        "s_3imtr3i",
        "( φ → ∀ x ψ ) → ( φ → ∀ y χ )",
        s_cbv3,
        s_19_21a,
        s_19_21b,
        ref="3imtr3i",
        note="3imtr3i cbv3, 19.21, 19.21",
    )
    # pm2.86i: ( ( φ → ψ ) → ( φ → χ ) ) ⊢ φ → ( ψ → χ )
    res = lb.ref(
        "res",
        "φ → ( ∀ x ψ → ∀ y χ )",
        s_3imtr3i,
        ref="pm2.86i",
        note="pm2.86i 3imtr3i",
    )
    return lb.build(res)


def prove_cbv1h(sys: System) -> Proof:
    """cbv1h: ∀ x ∀ y φ → ( ∀ x ψ → ∀ y χ ).
    Change bound variables in an implication of universal quantifiers
    using old-style not-free hypotheses.  Uses nfa1 and nfa2 for
    not-free conditions on the antecedent, 2sp to extract φ, syl
    to chain implications, nf5d to convert old-style not-free to Ⅎ,
    and cbv1 for the main variable change.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "cbv1h")
    hyp_psy = lb.hyp("cbv1h.1", "φ → ( ψ → ∀ y ψ )")
    hyp_chx = lb.hyp("cbv1h.2", "φ → ( χ → ∀ x χ )")
    hyp_eq = lb.hyp("cbv1h.3", "φ → ( x = y → ( ψ → χ ) )")
    # nfa1: Ⅎ x ∀ x φ.  With φ := ∀ y φ we get Ⅎ x ∀ x ∀ y φ.
    s_nfa1 = lb.ref(
        "s_nfa1",
        "Ⅎ x ∀ x ∀ y φ",
        ref="nfa1",
        note="nfa1",
    )
    # nfa2: Ⅎ x ∀ y ∀ x φ.  Swap x,y to get Ⅎ y ∀ x ∀ y φ.
    s_nfa2 = lb.ref(
        "s_nfa2",
        "Ⅎ y ∀ x ∀ y φ",
        ref="nfa2",
        note="nfa2",
    )
    # 2sp: ∀ x ∀ y φ → φ
    s_2sp = lb.ref(
        "s_2sp",
        "∀ x ∀ y φ → φ",
        ref="2sp",
        note="2sp",
    )
    # syl: (∀ x ∀ y φ → φ), (φ → (ψ → ∀ y ψ)) ⊢ (∀ x ∀ y φ → (ψ → ∀ y ψ))
    s_syl_psy = lb.ref(
        "s_syl_psy",
        "∀ x ∀ y φ → ( ψ → ∀ y ψ )",
        s_2sp,
        hyp_psy,
        ref="syl",
        note="syl 2sp, cbv1h.1",
    )
    # nf5d: Ⅎ y (∀x∀yφ), (∀x∀yφ → (ψ → ∀yψ)) ⊢ (∀x∀yφ → Ⅎ y ψ)
    s_nf5d_psy = lb.ref(
        "s_nf5d_psy",
        "∀ x ∀ y φ → Ⅎ y ψ",
        s_nfa2,
        s_syl_psy,
        ref="nf5d",
        note="nf5d nfa2, syl",
    )
    # syl: (∀ x ∀ y φ → φ), (φ → (χ → ∀ x χ)) ⊢ (∀ x ∀ y φ → (χ → ∀ x χ))
    s_syl_chx = lb.ref(
        "s_syl_chx",
        "∀ x ∀ y φ → ( χ → ∀ x χ )",
        s_2sp,
        hyp_chx,
        ref="syl",
        note="syl 2sp, cbv1h.2",
    )
    # nf5d: Ⅎ x (∀x∀yφ), (∀x∀yφ → (χ → ∀xχ)) ⊢ (∀x∀yφ → Ⅎ x χ)
    s_nf5d_chx = lb.ref(
        "s_nf5d_chx",
        "∀ x ∀ y φ → Ⅎ x χ",
        s_nfa1,
        s_syl_chx,
        ref="nf5d",
        note="nf5d nfa1, syl",
    )
    # syl: (∀ x ∀ y φ → φ), (φ → (x = y → (ψ → χ)))
    # ⊢ (∀ x ∀ y φ → (x = y → (ψ → χ)))
    s_syl_eq = lb.ref(
        "s_syl_eq",
        "∀ x ∀ y φ → ( x = y → ( ψ → χ ) )",
        s_2sp,
        hyp_eq,
        ref="syl",
        note="syl 2sp, cbv1h.3",
    )
    # cbv1: Ⅎx(∀x∀yφ), Ⅎy(∀x∀yφ), (∀x∀yφ → Ⅎyψ), (∀x∀yφ → Ⅎxχ),
    #       (∀x∀yφ → (x=y → (ψ→χ)))
    # ⊢ (∀x∀yφ → (∀xψ → ∀yχ))
    res = lb.ref(
        "res",
        "∀ x ∀ y φ → ( ∀ x ψ → ∀ y χ )",
        s_nfa1,
        s_nfa2,
        s_nf5d_psy,
        s_nf5d_chx,
        s_syl_eq,
        ref="cbv1",
        note="cbv1 nfa1, nfa2, nf5d, nf5d, syl",
    )
    return lb.build(res)


def prove_cbv2(sys: System) -> Proof:
    """cbv2: φ → ( ∀ x ψ ↔ ∀ y χ ).
    Change bound variables in a biconditional of universal quantifiers
    using implicit substitution.  Uses biimp, syl6, and cbv1 for the
    forward direction, and equcomi with swapped variables, biimpr,
    syl56, and cbv1 for the reverse direction, then combines them
    with impbid.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "cbv2")
    hyp_nf1 = lb.hyp("cbv2.1", "Ⅎ x φ")
    hyp_nf2 = lb.hyp("cbv2.2", "Ⅎ y φ")
    hyp_nf3 = lb.hyp("cbv2.3", "φ → Ⅎ y ψ")
    hyp_nf4 = lb.hyp("cbv2.4", "φ → Ⅎ x χ")
    hyp_eq = lb.hyp("cbv2.5", "φ → ( x = y → ( ψ ↔ χ ) )")
    # Forward direction: φ → ( ∀ x ψ → ∀ y χ )
    s_biimp = lb.ref(
        "s_biimp",
        "( ψ ↔ χ ) → ( ψ → χ )",
        ref="biimp",
        note="biimp",
    )
    s_syl6_fwd = lb.ref(
        "s_syl6_fwd",
        "φ → ( x = y → ( ψ → χ ) )",
        hyp_eq,
        s_biimp,
        ref="syl6",
        note="syl6 cbv2.5, biimp",
    )
    s_cbv1_fwd = lb.ref(
        "s_cbv1_fwd",
        "φ → ( ∀ x ψ → ∀ y χ )",
        hyp_nf1,
        hyp_nf2,
        hyp_nf3,
        hyp_nf4,
        s_syl6_fwd,
        ref="cbv1",
        note="cbv1",
    )
    # Reverse direction: φ → ( ∀ y χ → ∀ x ψ )
    # equcomi with y, x swapped: ( y = x ) → ( x = y )
    s_equcomi = lb.ref(
        "s_equcomi",
        "y = x → x = y",
        ref="equcomi",
        note="equcomi",
    )
    s_biimpr = lb.ref(
        "s_biimpr",
        "( ψ ↔ χ ) → ( χ → ψ )",
        ref="biimpr",
        note="biimpr",
    )
    # syl56( equcomi(y,x), cbv2.5, biimpr ) → φ → ( y = x → ( χ → ψ ) )
    s_syl56_rev = lb.ref(
        "s_syl56_rev",
        "φ → ( y = x → ( χ → ψ ) )",
        s_equcomi,
        hyp_eq,
        s_biimpr,
        ref="syl56",
        note="syl56 equcomi, cbv2.5, biimpr",
    )
    # cbv1 with swapped variables
    s_cbv1_rev = lb.ref(
        "s_cbv1_rev",
        "φ → ( ∀ y χ → ∀ x ψ )",
        hyp_nf2,
        hyp_nf1,
        hyp_nf4,
        hyp_nf3,
        s_syl56_rev,
        ref="cbv1",
        note="cbv1",
    )
    # Combine directions with impbid
    res = lb.ref(
        "res",
        "φ → ( ∀ x ψ ↔ ∀ y χ )",
        s_cbv1_fwd,
        s_cbv1_rev,
        ref="impbid",
        note="impbid",
    )
    return lb.build(res)


def prove_cbv2h(sys: System) -> Proof:
    """cbv2h: ∀ x ∀ y φ → ( ∀ x ψ ↔ ∀ y χ ).
    Change bound variables in a biconditional of universal quantifiers
    using old-style not-free hypotheses.  Uses biimp, syl6, and cbv1h
    for the forward direction, and equcomi with swapped variables,
    biimpr, syl56, and cbv1h for the reverse direction, then combines
    them with alcoms and impbid.
    (Contributed by NM, 11-May-1993.)
    """
    lb = ProofBuilder(sys, "cbv2h")
    hyp_psy = lb.hyp("cbv2h.1", "φ → ( ψ → ∀ y ψ )")
    hyp_chx = lb.hyp("cbv2h.2", "φ → ( χ → ∀ x χ )")
    hyp_eq = lb.hyp("cbv2h.3", "φ → ( x = y → ( ψ ↔ χ ) )")
    # Forward direction: ∀ x ∀ y φ → ( ∀ x ψ → ∀ y χ )
    s_biimp = lb.ref(
        "s_biimp",
        "( ψ ↔ χ ) → ( ψ → χ )",
        ref="biimp",
        note="biimp",
    )
    s_syl6_fwd = lb.ref(
        "s_syl6_fwd",
        "φ → ( x = y → ( ψ → χ ) )",
        hyp_eq,
        s_biimp,
        ref="syl6",
        note="syl6 cbv2h.3, biimp",
    )
    s_cbv1h_fwd = lb.ref(
        "s_cbv1h_fwd",
        "∀ x ∀ y φ → ( ∀ x ψ → ∀ y χ )",
        hyp_psy,
        hyp_chx,
        s_syl6_fwd,
        ref="cbv1h",
        note="cbv1h",
    )
    # Reverse direction: ∀ x ∀ y φ → ( ∀ y χ → ∀ x ψ )
    s_equcomi = lb.ref(
        "s_equcomi",
        "y = x → x = y",
        ref="equcomi",
        note="equcomi",
    )
    s_biimpr = lb.ref(
        "s_biimpr",
        "( ψ ↔ χ ) → ( χ → ψ )",
        ref="biimpr",
        note="biimpr",
    )
    s_syl56_rev = lb.ref(
        "s_syl56_rev",
        "φ → ( y = x → ( χ → ψ ) )",
        s_equcomi,
        hyp_eq,
        s_biimpr,
        ref="syl56",
        note="syl56 equcomi, cbv2h.3, biimpr",
    )
    s_cbv1h_rev = lb.ref(
        "s_cbv1h_rev",
        "∀ y ∀ x φ → ( ∀ y χ → ∀ x ψ )",
        hyp_chx,
        hyp_psy,
        s_syl56_rev,
        ref="cbv1h",
        note="cbv1h",
    )
    s_alcoms = lb.ref(
        "s_alcoms",
        "∀ x ∀ y φ → ( ∀ y χ → ∀ x ψ )",
        s_cbv1h_rev,
        ref="alcoms",
        note="alcoms",
    )
    # Combine directions with impbid
    res = lb.ref(
        "res",
        "∀ x ∀ y φ → ( ∀ x ψ ↔ ∀ y χ )",
        s_cbv1h_fwd,
        s_alcoms,
        ref="impbid",
        note="impbid",
    )
    return lb.build(res)


def prove_cbv2w(sys: System) -> Proof:
    """cbv2w: φ → ( ∀ x ψ ↔ ∀ y χ ).
    Change bound variables in a biconditional of universal quantifiers
    using implicit substitution.  Uses biimp, syl6, and cbv1v for the
    forward direction, and equcomi with swapped variables, biimpr,
    syl56, and cbv1v for the reverse direction, then combines them
    with impbid.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "cbv2w")
    hyp_nf1 = lb.hyp("cbv2w.1", "Ⅎ x φ")
    hyp_nf2 = lb.hyp("cbv2w.2", "Ⅎ y φ")
    hyp_nf3 = lb.hyp("cbv2w.3", "φ → Ⅎ y ψ")
    hyp_nf4 = lb.hyp("cbv2w.4", "φ → Ⅎ x χ")
    hyp_eq = lb.hyp("cbv2w.5", "φ → ( x = y → ( ψ ↔ χ ) )")
    # Forward direction: φ → ( ∀ x ψ → ∀ y χ )
    s_biimp = lb.ref(
        "s_biimp",
        "( ψ ↔ χ ) → ( ψ → χ )",
        ref="biimp",
        note="biimp",
    )
    s_syl6_fwd = lb.ref(
        "s_syl6_fwd",
        "φ → ( x = y → ( ψ → χ ) )",
        hyp_eq,
        s_biimp,
        ref="syl6",
        note="syl6 cbv2w.5, biimp",
    )
    s_cbv1v_fwd = lb.ref(
        "s_cbv1v_fwd",
        "φ → ( ∀ x ψ → ∀ y χ )",
        hyp_nf1,
        hyp_nf2,
        hyp_nf3,
        hyp_nf4,
        s_syl6_fwd,
        ref="cbv1v",
        note="cbv1v",
    )
    # Reverse direction: φ → ( ∀ y χ → ∀ x ψ )
    s_equcomi = lb.ref(
        "s_equcomi",
        "y = x → x = y",
        ref="equcomi",
        note="equcomi",
    )
    s_biimpr = lb.ref(
        "s_biimpr",
        "( ψ ↔ χ ) → ( χ → ψ )",
        ref="biimpr",
        note="biimpr",
    )
    s_syl56_rev = lb.ref(
        "s_syl56_rev",
        "φ → ( y = x → ( χ → ψ ) )",
        s_equcomi,
        hyp_eq,
        s_biimpr,
        ref="syl56",
        note="syl56 equcomi, cbv2w.5, biimpr",
    )
    s_cbv1v_rev = lb.ref(
        "s_cbv1v_rev",
        "φ → ( ∀ y χ → ∀ x ψ )",
        hyp_nf2,
        hyp_nf1,
        hyp_nf4,
        hyp_nf3,
        s_syl56_rev,
        ref="cbv1v",
        note="cbv1v",
    )
    # Combine directions with impbid
    res = lb.ref(
        "res",
        "φ → ( ∀ x ψ ↔ ∀ y χ )",
        s_cbv1v_fwd,
        s_cbv1v_rev,
        ref="impbid",
        note="impbid",
    )
    return lb.build(res)


def prove_cbv1v(sys: System) -> Proof:
    """cbv1v: φ → ( ∀ x ψ → ∀ y χ ).
    Change bound variables in an implication of universal quantifiers
    using implicit substitution.  Uses nfim1 for not-free conditions
    on the inner implications, com12 to commute antecedents, a2d to
    distribute the antecedent, cbv3v for bound-variable change,
    19.21 for universal distribution, 3imtr3i to combine
    biconditionals, and pm2.86i for the final form.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "cbv1v")
    hyp_nf1 = lb.hyp("cbv1v.1", "Ⅎ x φ")
    hyp_nf2 = lb.hyp("cbv1v.2", "Ⅎ y φ")
    hyp_nf3 = lb.hyp("cbv1v.3", "φ → Ⅎ y ψ")
    hyp_nf4 = lb.hyp("cbv1v.4", "φ → Ⅎ x χ")
    hyp_imp = lb.hyp("cbv1v.5", "φ → ( x = y → ( ψ → χ ) )")
    # nfim1: Ⅎ y φ, φ → Ⅎ y ψ ⊢ Ⅎ y ( φ → ψ )
    s_nf1 = lb.ref(
        "s_nf1",
        "Ⅎ y ( φ → ψ )",
        hyp_nf2,
        hyp_nf3,
        ref="nfim1",
        note="nfim1 cbv1v.2, cbv1v.3",
    )
    # nfim1: Ⅎ x φ, φ → Ⅎ x χ ⊢ Ⅎ x ( φ → χ )
    s_nf2 = lb.ref(
        "s_nf2",
        "Ⅎ x ( φ → χ )",
        hyp_nf1,
        hyp_nf4,
        ref="nfim1",
        note="nfim1 cbv1v.1, cbv1v.4",
    )
    # com12: φ → ( x = y → ( ψ → χ ) ) ⊢ ( x = y ) → ( φ → ( ψ → χ ) )
    s_com12 = lb.ref(
        "s_com12",
        "( x = y ) → ( φ → ( ψ → χ ) )",
        hyp_imp,
        ref="com12",
        note="com12 cbv1v.5",
    )
    # a2d: ( x = y ) → ( φ → ( ψ → χ ) ) ⊢ ( x = y ) → ( ( φ → ψ ) → ( φ → χ ) )
    s_a2d = lb.ref(
        "s_a2d",
        "( x = y ) → ( ( φ → ψ ) → ( φ → χ ) )",
        s_com12,
        ref="a2d",
        note="a2d com12",
    )
    # cbv3v: Ⅎ y ( φ → ψ ), Ⅎ x ( φ → χ ), ( x = y ) → ( ( φ → ψ ) → ( φ → χ ) )
    # ⊢ ∀ x ( φ → ψ ) → ∀ y ( φ → χ )
    s_cbv3v = lb.ref(
        "s_cbv3v",
        "∀ x ( φ → ψ ) → ∀ y ( φ → χ )",
        s_nf1,
        s_nf2,
        s_a2d,
        ref="cbv3v",
        note="cbv3v nfim1, nfim1, a2d",
    )
    # 19.21: Ⅎ x φ ⊢ ∀ x ( φ → ψ ) ↔ ( φ → ∀ x ψ )
    s_19_21a = lb.ref(
        "s_19_21a",
        "∀ x ( φ → ψ ) ↔ ( φ → ∀ x ψ )",
        hyp_nf1,
        ref="19.21",
        note="19.21 cbv1v.1",
    )
    # 19.21: Ⅎ y φ ⊢ ∀ y ( φ → χ ) ↔ ( φ → ∀ y χ )
    s_19_21b = lb.ref(
        "s_19_21b",
        "∀ y ( φ → χ ) ↔ ( φ → ∀ y χ )",
        hyp_nf2,
        ref="19.21",
        note="19.21 cbv1v.2",
    )
    # 3imtr3i: combine cbv3v result with the two 19.21 biconditionals
    # ( ∀ x ( φ → ψ ) → ∀ y ( φ → χ ) ),
    # ( ∀ x ( φ → ψ ) ↔ ( φ → ∀ x ψ ) ),
    # ( ∀ y ( φ → χ ) ↔ ( φ → ∀ y χ ) )
    # ⊢ ( φ → ∀ x ψ ) → ( φ → ∀ y χ )
    s_3imtr3i = lb.ref(
        "s_3imtr3i",
        "( φ → ∀ x ψ ) → ( φ → ∀ y χ )",
        s_cbv3v,
        s_19_21a,
        s_19_21b,
        ref="3imtr3i",
        note="3imtr3i cbv3v, 19.21, 19.21",
    )
    # pm2.86i: ( ( φ → ψ ) → ( φ → χ ) ) ⊢ φ → ( ψ → χ )
    res = lb.ref(
        "res",
        "φ → ( ∀ x ψ → ∀ y χ )",
        s_3imtr3i,
        ref="pm2.86i",
        note="pm2.86i 3imtr3i",
    )
    return lb.build(res)


def prove_cbval(sys: System) -> Proof:
    """cbval: ∀ x φ ↔ ∀ y ψ.
    Change bound variable in a universal quantifier using implicit substitution.
    Uses cbv3 twice: once forward via biimpd, once backward via biimprd +
    equcoms, then impbii to combine.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "cbval")
    hyp_nf1 = lb.hyp("cbval.1", "Ⅎ y φ")
    hyp_nf2 = lb.hyp("cbval.2", "Ⅎ x ψ")
    hyp_iff = lb.hyp("cbval.3", "( x = y ) → ( φ ↔ ψ )")
    # biimpd cbval.3: ( x = y ) → ( φ → ψ )
    s_biimpd = lb.ref(
        "s_biimpd",
        "( x = y ) → ( φ → ψ )",
        hyp_iff,
        ref="biimpd",
        note="biimpd cbval.3",
    )
    # cbv3 cbval.1, cbval.2, biimpd: ∀ x φ → ∀ y ψ
    s_fwd = lb.ref(
        "s_fwd",
        "∀ x φ → ∀ y ψ",
        hyp_nf1,
        hyp_nf2,
        s_biimpd,
        ref="cbv3",
        note="cbv3 cbval.1, cbval.2, biimpd",
    )
    # biimprd cbval.3: ( x = y ) → ( ψ → φ )
    s_biimprd = lb.ref(
        "s_biimprd",
        "( x = y ) → ( ψ → φ )",
        hyp_iff,
        ref="biimprd",
        note="biimprd cbval.3",
    )
    # equcoms biimprd: ( y = x ) → ( ψ → φ )
    s_equcoms = lb.ref(
        "s_equcoms",
        "( y = x ) → ( ψ → φ )",
        s_biimprd,
        ref="equcoms",
        note="equcoms biimprd",
    )
    # cbv3 cbval.2, cbval.1, equcoms: ∀ y ψ → ∀ x φ
    s_rev = lb.ref(
        "s_rev",
        "∀ y ψ → ∀ x φ",
        hyp_nf2,
        hyp_nf1,
        s_equcoms,
        ref="cbv3",
        note="cbv3 cbval.2, cbval.1, equcoms",
    )
    # impbii: (∀ x φ → ∀ y ψ) ∧ (∀ y ψ → ∀ x φ) → ∀ x φ ↔ ∀ y ψ
    res = lb.ref(
        "res",
        "∀ x φ ↔ ∀ y ψ",
        s_fwd,
        s_rev,
        ref="impbii",
        note="impbii cbv3, cbv3",
    )
    return lb.build(res)


def prove_cbval2(sys: System) -> Proof:
    """cbval2: ∀ x ∀ y φ ↔ ∀ z ∀ w ψ.
    Change two nested bound variables in a universal quantifier using
    implicit substitution.  Uses ex to export the biconditional from the
    conjunction hypothesis, cbv2 to change the inner bound variables, and
    cbval to change the outer bound variable.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "cbval2")
    hyp_nfz_phi = lb.hyp("cbval2.1", "Ⅎ z φ")
    hyp_nfw_phi = lb.hyp("cbval2.2", "Ⅎ w φ")
    hyp_nfx_psi = lb.hyp("cbval2.3", "Ⅎ x ψ")
    hyp_nfy_psi = lb.hyp("cbval2.4", "Ⅎ y ψ")
    hyp_eq = lb.hyp("cbval2.5", "( x = z ∧ y = w ) → ( φ ↔ ψ )")
    # ex cbval2.5: ( x = z ) → ( ( y = w ) → ( φ ↔ ψ ) )
    s_ex = lb.ref(
        "s_ex",
        "( x = z ) → ( ( y = w ) → ( φ ↔ ψ ) )",
        hyp_eq,
        ref="ex",
        note="ex cbval2.5",
    )
    # nfv: y and w are not free in ( x = z )
    s_nfy_xz = lb.ref("s_nfy_xz", "Ⅎ y ( x = z )", ref="nfv", note="nfv")
    s_nfw_xz = lb.ref("s_nfw_xz", "Ⅎ w ( x = z )", ref="nfv", note="nfv")
    # a1i cbval2.2: ( x = z ) → Ⅎ w φ
    s_a1i_nfw = lb.ref(
        "s_a1i_nfw",
        "( x = z ) → Ⅎ w φ",
        hyp_nfw_phi,
        ref="a1i",
        note="a1i cbval2.2",
    )
    # a1i cbval2.4: ( x = z ) → Ⅎ y ψ
    s_a1i_nfy = lb.ref(
        "s_a1i_nfy",
        "( x = z ) → Ⅎ y ψ",
        hyp_nfy_psi,
        ref="a1i",
        note="a1i cbval2.4",
    )
    # cbv2 nfv, nfv, a1i, a1i, ex: ( x = z ) → ( ∀ y φ ↔ ∀ w ψ )
    s_cbv2 = lb.ref(
        "s_cbv2",
        "( x = z ) → ( ∀ y φ ↔ ∀ w ψ )",
        s_nfy_xz,
        s_nfw_xz,
        s_a1i_nfw,
        s_a1i_nfy,
        s_ex,
        ref="cbv2",
        note="cbv2 nfv, nfv, a1i, a1i, ex",
    )
    # nfal cbval2.1: Ⅎ z ∀ y φ
    s_nfz_aly = lb.ref(
        "s_nfz_aly",
        "Ⅎ z ∀ y φ",
        hyp_nfz_phi,
        ref="nfal",
        note="nfal cbval2.1",
    )
    # nfal cbval2.3: Ⅎ x ∀ w ψ
    s_nfx_alw = lb.ref(
        "s_nfx_alw",
        "Ⅎ x ∀ w ψ",
        hyp_nfx_psi,
        ref="nfal",
        note="nfal cbval2.3",
    )
    # cbval nfal, nfal, cbv2: ∀ x ∀ y φ ↔ ∀ z ∀ w ψ
    res = lb.ref(
        "res",
        "∀ x ∀ y φ ↔ ∀ z ∀ w ψ",
        s_nfz_aly,
        s_nfx_alw,
        s_cbv2,
        ref="cbval",
        note="cbval nfal, nfal, cbv2",
    )
    return lb.build(res)


def prove_cbvald(sys: System) -> Proof:
    """cbvald: φ → ( ∀ x ψ ↔ ∀ y χ ).
    Deduction form of cbval.  Change bound variables in a universal
    quantifier using implicit substitution, under an antecedent.
    Uses nfv and nfvd to provide two missing hypotheses for cbv2.
    (Contributed by NM, 2-Jan-2002.)
    """
    lb = ProofBuilder(sys, "cbvald")
    hyp_nf1 = lb.hyp("cbvald.1", "Ⅎ y φ")
    hyp_nf2 = lb.hyp("cbvald.2", "φ → Ⅎ y ψ")
    hyp_eq = lb.hyp("cbvald.3", "φ → ( x = y → ( ψ ↔ χ ) )")
    # nfv: Ⅎ x φ
    s_nfv = lb.ref("s_nfv", "Ⅎ x φ", ref="nfv", note="nfv")
    # nfvd: φ → Ⅎ x χ
    s_nfvd = lb.ref("s_nfvd", "φ → Ⅎ x χ", ref="nfvd", note="nfvd")
    # cbv2 with all five hypotheses
    res = lb.ref(
        "res",
        "φ → ( ∀ x ψ ↔ ∀ y χ )",
        s_nfv,
        hyp_nf1,
        hyp_nf2,
        s_nfvd,
        hyp_eq,
        ref="cbv2",
        note="cbv2",
    )
    return lb.build(res)


def prove_cbvaldw(sys: System) -> Proof:
    """cbvaldw: φ → ( ∀ x ψ ↔ ∀ y χ ).
    Deduction form of cbvalw.  Change bound variables in a universal
    quantifier using implicit substitution, under an antecedent.
    Uses nfv and nfvd to provide two missing hypotheses for cbv2w.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "cbvaldw")
    hyp_nf1 = lb.hyp("cbvaldw.1", "Ⅎ y φ")
    hyp_nf2 = lb.hyp("cbvaldw.2", "φ → Ⅎ y ψ")
    hyp_eq = lb.hyp("cbvaldw.3", "φ → ( x = y → ( ψ ↔ χ ) )")
    # nfv: Ⅎ x φ
    s_nfv = lb.ref("s_nfv", "Ⅎ x φ", ref="nfv", note="nfv")
    # nfvd: φ → Ⅎ x χ
    s_nfvd = lb.ref("s_nfvd", "φ → Ⅎ x χ", ref="nfvd", note="nfvd")
    # cbv2w with all five hypotheses
    res = lb.ref(
        "res",
        "φ → ( ∀ x ψ ↔ ∀ y χ )",
        s_nfv,
        hyp_nf1,
        hyp_nf2,
        s_nfvd,
        hyp_eq,
        ref="cbv2w",
        note="cbv2w",
    )
    return lb.build(res)


def prove_cbvaldva(sys: System) -> Proof:
    """cbvaldva: φ → ( ∀ x ψ ↔ ∀ y χ ).
    Deduction form of cbvald.  Change bound variables in a universal
    quantifier using implicit substitution without requiring F/
    hypotheses.  Uses nfv, nfvd, and ex to prepare the three
    hypotheses needed by cbvald.
    (Contributed by NM, 2-Jan-2002.)
    """
    lb = ProofBuilder(sys, "cbvaldva")
    hyp = lb.hyp("cbvaldva.1", "( ( φ ∧ x = y ) → ( ψ ↔ χ ) )")
    # nfv: Ⅎ y φ
    s_nfv = lb.ref("s_nfv", "Ⅎ y φ", ref="nfv", note="nfv")
    # nfvd: φ → Ⅎ y ψ
    s_nfvd = lb.ref("s_nfvd", "φ → Ⅎ y ψ", ref="nfvd", note="nfvd")
    # ex: φ → ( x = y → ( ψ ↔ χ ) )
    s_ex = lb.ref(
        "s_ex",
        "φ → ( x = y → ( ψ ↔ χ ) )",
        hyp,
        ref="ex",
        note="ex",
    )
    # cbvald: φ → ( ∀ x ψ ↔ ∀ y χ )
    res = lb.ref(
        "res",
        "φ → ( ∀ x ψ ↔ ∀ y χ )",
        s_nfv,
        s_nfvd,
        s_ex,
        ref="cbvald",
        note="cbvald",
    )
    return lb.build(res)


def prove_cbvexd(sys: System) -> Proof:
    """cbvexd: φ → ( ∃ x ψ ↔ ∃ y χ ).
    Deduction form of cbvex.  Change bound variables in an existential
    quantifier using implicit substitution, under an antecedent.
    Uses nfnd, notbi, and imbitrdi to prepare the hypotheses for cbvald,
    then applies alnex, 3bitr3g, and con4bid.
    (Contributed by NM, 2-Jan-2002.)
    """
    lb = ProofBuilder(sys, "cbvexd")
    hyp_nf1 = lb.hyp("cbvald.1", "Ⅎ y φ")
    hyp_nf2 = lb.hyp("cbvald.2", "φ → Ⅎ y ψ")
    hyp_eq = lb.hyp("cbvald.3", "φ → ( x = y → ( ψ ↔ χ ) )")
    # nfnd: φ → Ⅎ y ¬ ψ
    s_nfnd = lb.ref(
        "s_nfnd",
        "φ → Ⅎ y ¬ ψ",
        hyp_nf2,
        ref="nfnd",
        note="nfnd",
    )
    # notbi: ( ψ ↔ χ ) ↔ ( ¬ ψ ↔ ¬ χ )
    s_notbi = lb.ref(
        "s_notbi",
        "( ψ ↔ χ ) ↔ ( ¬ ψ ↔ ¬ χ )",
        ref="notbi",
        note="notbi",
    )
    # imbitrdi: φ → ( x = y → ( ¬ ψ ↔ ¬ χ ) )
    s_imbitrdi = lb.ref(
        "s_imbitrdi",
        "φ → ( x = y → ( ¬ ψ ↔ ¬ χ ) )",
        hyp_eq,
        s_notbi,
        ref="imbitrdi",
        note="imbitrdi",
    )
    # cbvald: φ → ( ∀ x ¬ ψ ↔ ∀ y ¬ χ )
    s_cbvald = lb.ref(
        "s_cbvald",
        "φ → ( ∀ x ¬ ψ ↔ ∀ y ¬ χ )",
        hyp_nf1,
        s_nfnd,
        s_imbitrdi,
        ref="cbvald",
        note="cbvald",
    )
    # alnex (with x): ∀ x ¬ ψ ↔ ¬ ∃ x ψ
    s_alnex_x = lb.ref(
        "s_alnex_x",
        "∀ x ¬ ψ ↔ ¬ ∃ x ψ",
        ref="alnex",
        note="alnex",
    )
    # alnex (with y): ∀ y ¬ χ ↔ ¬ ∃ y χ
    s_alnex_y = lb.ref(
        "s_alnex_y",
        "∀ y ¬ χ ↔ ¬ ∃ y χ",
        ref="alnex",
        note="alnex",
    )
    # 3bitr3g: φ → ( ¬ ∃ x ψ ↔ ¬ ∃ y χ )
    s_3bitr3g = lb.ref(
        "s_3bitr3g",
        "φ → ( ¬ ∃ x ψ ↔ ¬ ∃ y χ )",
        s_cbvald,
        s_alnex_x,
        s_alnex_y,
        ref="3bitr3g",
        note="3bitr3g",
    )
    # con4bid: φ → ( ∃ x ψ ↔ ∃ y χ )
    res = lb.ref(
        "res",
        "φ → ( ∃ x ψ ↔ ∃ y χ )",
        s_3bitr3g,
        ref="con4bid",
        note="con4bid",
    )
    return lb.build(res)


def prove_cbvexdva(sys: System) -> Proof:
    """cbvexdva: φ → ( ∃ x ψ ↔ ∃ y χ ).
    Deduction form of cbvexd.  Change bound variables in an existential
    quantifier using implicit substitution without requiring F/ hypotheses.
    Uses nfv, nfvd, and ex to prepare the three hypotheses needed by
    cbvexd.
    (Contributed by NM, 2-Jan-2002.)
    """
    lb = ProofBuilder(sys, "cbvexdva")
    hyp = lb.hyp("cbvexdva.1", "( ( φ ∧ x = y ) → ( ψ ↔ χ ) )")
    # nfv: Ⅎ y φ
    s_nfv = lb.ref("s_nfv", "Ⅎ y φ", ref="nfv", note="nfv")
    # nfvd: φ → Ⅎ y ψ
    s_nfvd = lb.ref("s_nfvd", "φ → Ⅎ y ψ", ref="nfvd", note="nfvd")
    # ex: φ → ( x = y → ( ψ ↔ χ ) )
    s_ex = lb.ref(
        "s_ex",
        "φ → ( x = y → ( ψ ↔ χ ) )",
        hyp,
        ref="ex",
        note="ex",
    )
    # cbvexd: φ → ( ∃ x ψ ↔ ∃ y χ )
    res = lb.ref(
        "res",
        "φ → ( ∃ x ψ ↔ ∃ y χ )",
        s_nfv,
        s_nfvd,
        s_ex,
        ref="cbvexd",
        note="cbvexd",
    )
    return lb.build(res)


def prove_cbvexdw(sys: System) -> Proof:
    """cbvexdw: φ → ( ∃ x ψ ↔ ∃ y χ ).
    Deduction form of cbvexw.  Change bound variables in an existential
    quantifier using implicit substitution, under an antecedent.
    Uses nfnd, notbi, and imbitrdi to prepare the hypotheses for cbvaldw,
    then applies alnex, 3bitr3g, and con4bid.
    (Contributed by NM, 2-Jan-2002.)
    """
    lb = ProofBuilder(sys, "cbvexdw")
    hyp_nf1 = lb.hyp("cbvaldw.1", "Ⅎ y φ")
    hyp_nf2 = lb.hyp("cbvaldw.2", "φ → Ⅎ y ψ")
    hyp_eq = lb.hyp("cbvaldw.3", "φ → ( x = y → ( ψ ↔ χ ) )")
    # nfnd: φ → Ⅎ y ¬ ψ
    s_nfnd = lb.ref(
        "s_nfnd",
        "φ → Ⅎ y ¬ ψ",
        hyp_nf2,
        ref="nfnd",
        note="nfnd",
    )
    # notbi: ( ψ ↔ χ ) ↔ ( ¬ ψ ↔ ¬ χ )
    s_notbi = lb.ref(
        "s_notbi",
        "( ψ ↔ χ ) ↔ ( ¬ ψ ↔ ¬ χ )",
        ref="notbi",
        note="notbi",
    )
    # imbitrdi: φ → ( x = y → ( ¬ ψ ↔ ¬ χ ) )
    s_imbitrdi = lb.ref(
        "s_imbitrdi",
        "φ → ( x = y → ( ¬ ψ ↔ ¬ χ ) )",
        hyp_eq,
        s_notbi,
        ref="imbitrdi",
        note="imbitrdi",
    )
    # cbvaldw: φ → ( ∀ x ¬ ψ ↔ ∀ y ¬ χ )
    s_cbvaldw = lb.ref(
        "s_cbvaldw",
        "φ → ( ∀ x ¬ ψ ↔ ∀ y ¬ χ )",
        hyp_nf1,
        s_nfnd,
        s_imbitrdi,
        ref="cbvaldw",
        note="cbvaldw",
    )
    # alnex (with x): ∀ x ¬ ψ ↔ ¬ ∃ x ψ
    s_alnex_x = lb.ref(
        "s_alnex_x",
        "∀ x ¬ ψ ↔ ¬ ∃ x ψ",
        ref="alnex",
        note="alnex",
    )
    # alnex (with y): ∀ y ¬ χ ↔ ¬ ∃ y χ
    s_alnex_y = lb.ref(
        "s_alnex_y",
        "∀ y ¬ χ ↔ ¬ ∃ y χ",
        ref="alnex",
        note="alnex",
    )
    # 3bitr3g: φ → ( ¬ ∃ x ψ ↔ ¬ ∃ y χ )
    s_3bitr3g = lb.ref(
        "s_3bitr3g",
        "φ → ( ¬ ∃ x ψ ↔ ¬ ∃ y χ )",
        s_cbvaldw,
        s_alnex_x,
        s_alnex_y,
        ref="3bitr3g",
        note="3bitr3g",
    )
    # con4bid: φ → ( ∃ x ψ ↔ ∃ y χ )
    res = lb.ref(
        "res",
        "φ → ( ∃ x ψ ↔ ∃ y χ )",
        s_3bitr3g,
        ref="con4bid",
        note="con4bid",
    )
    return lb.build(res)


def prove_cbvalv1(sys: System) -> Proof:
    """cbvalv1: ∀ x φ ↔ ∀ y ψ.
    Change bound variable in a universal quantifier using implicit substitution.
    Uses cbv3v twice: once forward via biimpd, once backward via biimprd +
    equcoms, then impbii to combine.
    (Contributed by NM, 13-May-1993.)
    """
    lb = ProofBuilder(sys, "cbvalv1")
    hyp_nf1 = lb.hyp("cbvalv1.nf1", "Ⅎ y φ")
    hyp_nf2 = lb.hyp("cbvalv1.nf2", "Ⅎ x ψ")
    hyp_iff = lb.hyp("cbvalv1.1", "( x = y ) → ( φ ↔ ψ )")
    # biimpd cbvalv1.1: ( x = y ) → ( φ → ψ )
    s_biimpd = lb.ref(
        "s_biimpd",
        "( x = y ) → ( φ → ψ )",
        hyp_iff,
        ref="biimpd",
        note="biimpd cbvalv1.1",
    )
    # cbv3v cbvalv1.nf1, cbvalv1.nf2, biimpd: ∀ x φ → ∀ y ψ
    s_fwd = lb.ref(
        "s_fwd",
        "∀ x φ → ∀ y ψ",
        hyp_nf1,
        hyp_nf2,
        s_biimpd,
        ref="cbv3v",
        note="cbv3v cbvalv1.nf1, cbvalv1.nf2, biimpd",
    )
    # biimprd cbvalv1.1: ( x = y ) → ( ψ → φ )
    s_biimprd = lb.ref(
        "s_biimprd",
        "( x = y ) → ( ψ → φ )",
        hyp_iff,
        ref="biimprd",
        note="biimprd cbvalv1.1",
    )
    # equcoms biimprd: ( y = x ) → ( ψ → φ )
    s_equcoms = lb.ref(
        "s_equcoms",
        "( y = x ) → ( ψ → φ )",
        s_biimprd,
        ref="equcoms",
        note="equcoms biimprd",
    )
    # cbv3v cbvalv1.nf2, cbvalv1.nf1, equcoms: ∀ y ψ → ∀ x φ
    s_rev = lb.ref(
        "s_rev",
        "∀ y ψ → ∀ x φ",
        hyp_nf2,
        hyp_nf1,
        s_equcoms,
        ref="cbv3v",
        note="cbv3v cbvalv1.nf2, cbvalv1.nf1, equcoms",
    )
    # impbii: (∀ x φ → ∀ y ψ) ∧ (∀ y ψ → ∀ x φ) → ∀ x φ ↔ ∀ y ψ
    res = lb.ref(
        "res",
        "∀ x φ ↔ ∀ y ψ",
        s_fwd,
        s_rev,
        ref="impbii",
        note="impbii cbv3v, cbv3v",
    )
    return lb.build(res)


def prove_cbvexv1(sys: System) -> Proof:
    """cbvexv1: ∃ x φ ↔ ∃ y ψ.
    Change bound variable in an existential quantifier using implicit substitution.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "cbvexv1")
    hyp_nf1 = lb.hyp("cbvexv1.nf1", "Ⅎ y φ")
    hyp_nf2 = lb.hyp("cbvexv1.nf2", "Ⅎ x ψ")
    hyp_iff = lb.hyp("cbvexv1.1", "x = y → ( φ ↔ ψ )")
    # nfn hyp_nf1: Ⅎ y ¬ φ
    s_nfn1 = lb.ref(
        "s_nfn1",
        "Ⅎ y ¬ φ",
        hyp_nf1,
        ref="nfn",
        note="nfn cbvexv1.nf1",
    )
    # nfn hyp_nf2: Ⅎ x ¬ ψ
    s_nfn2 = lb.ref(
        "s_nfn2",
        "Ⅎ x ¬ ψ",
        hyp_nf2,
        ref="nfn",
        note="nfn cbvexv1.nf2",
    )
    # notbid hyp_iff: x = y → ( ¬ φ ↔ ¬ ψ )
    s_notbid = lb.ref(
        "s_notbid",
        "x = y → ( ¬ φ ↔ ¬ ψ )",
        hyp_iff,
        ref="notbid",
        note="notbid cbvexv1.1",
    )
    # cbvalv1 with s_nfn1, s_nfn2, s_notbid: ∀ x ¬ φ ↔ ∀ y ¬ ψ
    s_cbvalv1 = lb.ref(
        "s_cbvalv1",
        "∀ x ¬ φ ↔ ∀ y ¬ ψ",
        s_nfn1,
        s_nfn2,
        s_notbid,
        ref="cbvalv1",
        note="cbvalv1 nfn, nfn, notbid",
    )
    # alnex: ∀ x ¬ φ ↔ ¬ ∃ x φ
    s_alnex1 = lb.ref(
        "s_alnex1",
        "∀ x ¬ φ ↔ ¬ ∃ x φ",
        ref="alnex",
        note="alnex",
    )
    # alnex: ∀ y ¬ ψ ↔ ¬ ∃ y ψ
    s_alnex2 = lb.ref(
        "s_alnex2",
        "∀ y ¬ ψ ↔ ¬ ∃ y ψ",
        ref="alnex",
        note="alnex",
    )
    # 3bitr3i: ¬ ∃ x φ ↔ ¬ ∃ y ψ
    s_3bitr3i = lb.ref(
        "s_3bitr3i",
        "¬ ∃ x φ ↔ ¬ ∃ y ψ",
        s_cbvalv1,
        s_alnex1,
        s_alnex2,
        ref="3bitr3i",
        note="3bitr3i cbvalv1, alnex, alnex",
    )
    # con4bii: ∃ x φ ↔ ∃ y ψ
    res = lb.ref(
        "res",
        "∃ x φ ↔ ∃ y ψ",
        s_3bitr3i,
        ref="con4bii",
        note="con4bii 3bitr3i",
    )
    return lb.build(res)


def prove_cbvex(sys: System) -> Proof:
    """cbvex: ∃ x φ ↔ ∃ y ψ.
    Change bound variable in an existential quantifier using implicit substitution.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "cbvex")
    hyp_nf1 = lb.hyp("cbval.1", "Ⅎ y φ")
    hyp_nf2 = lb.hyp("cbval.2", "Ⅎ x ψ")
    hyp_iff = lb.hyp("cbval.3", "( x = y ) → ( φ ↔ ψ )")
    # nfn cbval.1: Ⅎ y ¬ φ
    s_nfn1 = lb.ref(
        "s_nfn1",
        "Ⅎ y ¬ φ",
        hyp_nf1,
        ref="nfn",
        note="nfn cbval.1",
    )
    # nfn cbval.2: Ⅎ x ¬ ψ
    s_nfn2 = lb.ref(
        "s_nfn2",
        "Ⅎ x ¬ ψ",
        hyp_nf2,
        ref="nfn",
        note="nfn cbval.2",
    )
    # notbid cbval.3: ( x = y ) → ( ¬ φ ↔ ¬ ψ )
    s_notbid = lb.ref(
        "s_notbid",
        "( x = y ) → ( ¬ φ ↔ ¬ ψ )",
        hyp_iff,
        ref="notbid",
        note="notbid cbval.3",
    )
    # cbval with s_nfn1, s_nfn2, s_notbid: ∀ x ¬ φ ↔ ∀ y ¬ ψ
    s_cbval = lb.ref(
        "s_cbval",
        "∀ x ¬ φ ↔ ∀ y ¬ ψ",
        s_nfn1,
        s_nfn2,
        s_notbid,
        ref="cbval",
        note="cbval nfn, nfn, notbid",
    )
    # alnex: ∀ x ¬ φ ↔ ¬ ∃ x φ
    s_alnex1 = lb.ref(
        "s_alnex1",
        "∀ x ¬ φ ↔ ¬ ∃ x φ",
        ref="alnex",
        note="alnex",
    )
    # alnex: ∀ y ¬ ψ ↔ ¬ ∃ y ψ
    s_alnex2 = lb.ref(
        "s_alnex2",
        "∀ y ¬ ψ ↔ ¬ ∃ y ψ",
        ref="alnex",
        note="alnex",
    )
    # 3bitr3i: ¬ ∃ x φ ↔ ¬ ∃ y ψ
    s_3bitr3i = lb.ref(
        "s_3bitr3i",
        "¬ ∃ x φ ↔ ¬ ∃ y ψ",
        s_cbval,
        s_alnex1,
        s_alnex2,
        ref="3bitr3i",
        note="3bitr3i cbval, alnex, alnex",
    )
    # con4bii: ∃ x φ ↔ ∃ y ψ
    res = lb.ref(
        "res",
        "∃ x φ ↔ ∃ y ψ",
        s_3bitr3i,
        ref="con4bii",
        note="con4bii 3bitr3i",
    )
    return lb.build(res)


def prove_cbvalv(sys: System) -> Proof:
    """cbvalv: ∀ x φ ↔ ∀ y ψ.
    Change bound variable in a universal quantifier using implicit substitution.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "cbvalv")
    # cbvalv.1: x = y → ( φ ↔ ψ )
    hyp_cbvalv1 = lb.hyp("cbvalv.1", "x = y → ( φ ↔ ψ )")
    # nfv: Ⅎ y φ
    s_nf1 = lb.ref("s_nf1", "Ⅎ y φ", ref="nfv", note="nfv")
    # nfv: Ⅎ x ψ
    s_nf2 = lb.ref("s_nf2", "Ⅎ x ψ", ref="nfv", note="nfv")
    # cbval nfv, nfv, cbvalv.1: ∀ x φ ↔ ∀ y ψ
    res = lb.ref(
        "res",
        "∀ x φ ↔ ∀ y ψ",
        s_nf1,
        s_nf2,
        hyp_cbvalv1,
        ref="cbval",
        note="cbval nfv, nfv, cbvalv.1",
    )
    return lb.build(res)


def prove_cbval2vv(sys: System) -> Proof:
    """cbval2vv: ∀ x ∀ y φ ↔ ∀ z ∀ w ψ.
    Change two nested bound variables in a universal quantifier using
    implicit substitution without requiring F/ hypotheses, using
    cbvaldva and cbvalv.
    (Contributed by NM, 4-Feb-2005.)  (Revised by Wolf Lammen, 18-Jul-2021.)
    """
    lb = ProofBuilder(sys, "cbval2vv")
    # cbval2vv.1: ( x = z ∧ y = w ) → ( φ ↔ ψ )
    hyp = lb.hyp("cbval2vv.1", "( x = z ∧ y = w ) → ( φ ↔ ψ )")
    # cbvaldva cbval2vv.1: ( x = z ) → ( ∀ y φ ↔ ∀ w ψ )
    s1 = lb.ref(
        "s1",
        "( x = z ) → ( ∀ y φ ↔ ∀ w ψ )",
        hyp,
        ref="cbvaldva",
        note="cbvaldva cbval2vv.1",
    )
    # cbvalv s1: ∀ x ∀ y φ ↔ ∀ z ∀ w ψ
    res = lb.ref(
        "res",
        "∀ x ∀ y φ ↔ ∀ z ∀ w ψ",
        s1,
        ref="cbvalv",
        note="cbvalv s1",
    )
    return lb.build(res)


def prove_cbvexv(sys: System) -> Proof:
    """cbvexv: ∃ x φ ↔ ∃ y ψ.
    Change bound variable in an existential quantifier using explicit substitution.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "cbvexv")
    # cbvalv.1: x = y → ( φ ↔ ψ )
    hyp_cbvalv1 = lb.hyp("cbvalv.1", "x = y → ( φ ↔ ψ )")
    # nfv: Ⅎ y φ
    s_nf1 = lb.ref("s_nf1", "Ⅎ y φ", ref="nfv", note="nfv")
    # nfv: Ⅎ x ψ
    s_nf2 = lb.ref("s_nf2", "Ⅎ x ψ", ref="nfv", note="nfv")
    # cbvex nfv, nfv, cbvalv.1: ∃ x φ ↔ ∃ y ψ
    res = lb.ref(
        "res",
        "∃ x φ ↔ ∃ y ψ",
        s_nf1,
        s_nf2,
        hyp_cbvalv1,
        ref="cbvex",
        note="cbvex nfv, nfv, cbvalv.1",
    )
    return lb.build(res)


def prove_cbvex2(sys: System) -> Proof:
    """cbvex2: ∃ x ∃ y φ ↔ ∃ z ∃ w ψ.
    Change two nested bound variables in an existential quantifier using
    implicit substitution.
    """
    lb = ProofBuilder(sys, "cbvex2")
    hyp_nfz_phi = lb.hyp("cbval2.1", "Ⅎ z φ")
    hyp_nfw_phi = lb.hyp("cbval2.2", "Ⅎ w φ")
    hyp_nfx_psi = lb.hyp("cbval2.3", "Ⅎ x ψ")
    hyp_nfy_psi = lb.hyp("cbval2.4", "Ⅎ y ψ")
    hyp_eq = lb.hyp("cbval2.5", "( ( x = z ∧ y = w ) → ( φ ↔ ψ ) )")
    # nfn cbval2.1: Ⅎ z ¬ φ
    s_nfn1 = lb.ref(
        "s_nfn1",
        "Ⅎ z ¬ φ",
        hyp_nfz_phi,
        ref="nfn",
        note="nfn cbval2.1",
    )
    # nfn cbval2.2: Ⅎ w ¬ φ
    s_nfn2 = lb.ref(
        "s_nfn2",
        "Ⅎ w ¬ φ",
        hyp_nfw_phi,
        ref="nfn",
        note="nfn cbval2.2",
    )
    # nfn cbval2.3: Ⅎ x ¬ ψ
    s_nfn3 = lb.ref(
        "s_nfn3",
        "Ⅎ x ¬ ψ",
        hyp_nfx_psi,
        ref="nfn",
        note="nfn cbval2.3",
    )
    # nfn cbval2.4: Ⅎ y ¬ ψ
    s_nfn4 = lb.ref(
        "s_nfn4",
        "Ⅎ y ¬ ψ",
        hyp_nfy_psi,
        ref="nfn",
        note="nfn cbval2.4",
    )
    # notbid cbval2.5: ( ( x = z ∧ y = w ) → ( ¬ φ ↔ ¬ ψ ) )
    s_notbid = lb.ref(
        "s_notbid",
        "( ( x = z ∧ y = w ) → ( ¬ φ ↔ ¬ ψ ) )",
        hyp_eq,
        ref="notbid",
        note="notbid cbval2.5",
    )
    # cbval2 nfn, nfn, nfn, nfn, notbid: ∀ x ∀ y ¬ φ ↔ ∀ z ∀ w ¬ ψ
    s_cbval2 = lb.ref(
        "s_cbval2",
        "∀ x ∀ y ¬ φ ↔ ∀ z ∀ w ¬ ψ",
        s_nfn1,
        s_nfn2,
        s_nfn3,
        s_nfn4,
        s_notbid,
        ref="cbval2",
        note="cbval2 nfn, nfn, nfn, nfn, notbid",
    )
    # 2nexaln: ¬ ∃ x ∃ y φ ↔ ∀ x ∀ y ¬ φ
    s_2nexaln1 = lb.ref(
        "s_2nexaln1",
        "¬ ∃ x ∃ y φ ↔ ∀ x ∀ y ¬ φ",
        ref="2nexaln",
        note="2nexaln",
    )
    # 2nexaln: ¬ ∃ z ∃ w ψ ↔ ∀ z ∀ w ¬ ψ
    s_2nexaln2 = lb.ref(
        "s_2nexaln2",
        "¬ ∃ z ∃ w ψ ↔ ∀ z ∀ w ¬ ψ",
        ref="2nexaln",
        note="2nexaln",
    )
    # 3bitr4i: ¬ ∃ x ∃ y φ ↔ ¬ ∃ z ∃ w ψ
    s_3bitr4i = lb.ref(
        "s_3bitr4i",
        "¬ ∃ x ∃ y φ ↔ ¬ ∃ z ∃ w ψ",
        s_cbval2,
        s_2nexaln1,
        s_2nexaln2,
        ref="3bitr4i",
        note="3bitr4i cbval2, 2nexaln, 2nexaln",
    )
    # con4bii: ∃ x ∃ y φ ↔ ∃ z ∃ w ψ
    res = lb.ref(
        "res",
        "∃ x ∃ y φ ↔ ∃ z ∃ w ψ",
        s_3bitr4i,
        ref="con4bii",
        note="con4bii 3bitr4i",
    )
    return lb.build(res)


def prove_cbvex2vv(sys: System) -> Proof:
    """cbvex2vv: ∃ x ∃ y φ ↔ ∃ z ∃ w ψ.
    Change bound variables in a double existential quantifier using
    implicit substitution.
    """
    lb = ProofBuilder(sys, "cbvex2vv")
    # cbval2vv.1: ( ( x = z ∧ y = w ) → ( φ ↔ ψ ) )
    hyp = lb.hyp("cbval2vv.1", "( ( x = z ∧ y = w ) → ( φ ↔ ψ ) )")
    # cbvexdva: ( x = z ) → ( ∃ y φ ↔ ∃ w ψ )
    s_cbvexdva = lb.ref(
        "s_cbvexdva",
        "( x = z ) → ( ∃ y φ ↔ ∃ w ψ )",
        hyp,
        ref="cbvexdva",
        note="cbvexdva",
    )
    # cbvexv: ∃ x ∃ y φ ↔ ∃ z ∃ w ψ
    res = lb.ref(
        "res",
        "∃ x ∃ y φ ↔ ∃ z ∃ w ψ",
        s_cbvexdva,
        ref="cbvexv",
        note="cbvexv",
    )
    return lb.build(res)


def prove_cbvex4v(sys: System) -> Proof:
    """cbvex4v: ∃ x ∃ y ∃ z ∃ w φ ↔ ∃ v ∃ u ∃ f ∃ g χ.
    Change bound variables in a quadruple existential quantifier using
    implicit substitution.
    """
    lb = ProofBuilder(sys, "cbvex4v")
    hyp1 = lb.hyp("cbvex4v.1", "( ( x = v ∧ y = u ) → ( φ ↔ ψ ) )")
    hyp2 = lb.hyp("cbvex4v.2", "( ( z = f ∧ w = g ) → ( ψ ↔ χ ) )")
    # 2exbidv with z,w: extend the first hypothesis under two quantifiers
    s_2exbidv = lb.ref(
        "s_2exbidv",
        "( ( x = v ∧ y = u ) → ( ∃ z ∃ w φ ↔ ∃ z ∃ w ψ ) )",
        hyp1,
        ref="2exbidv",
        note="2exbidv cbvex4v.1",
    )
    # cbvex2vv: bind x,y ↔ v,u
    s_cbvex2vv_1 = lb.ref(
        "s_cbvex2vv_1",
        "∃ x ∃ y ∃ z ∃ w φ ↔ ∃ v ∃ u ∃ z ∃ w ψ",
        s_2exbidv,
        ref="cbvex2vv",
        note="cbvex2vv 2exbidv",
    )
    # cbvex2vv from cbvex4v.2: bind z,w ↔ f,g
    s_cbvex2vv_2 = lb.ref(
        "s_cbvex2vv_2",
        "∃ z ∃ w ψ ↔ ∃ f ∃ g χ",
        hyp2,
        ref="cbvex2vv",
        note="cbvex2vv cbvex4v.2",
    )
    # 2exbii: add ∃ v ∃ u prefix to the ψ/χ equivalence
    s_2exbii = lb.ref(
        "s_2exbii",
        "∃ v ∃ u ∃ z ∃ w ψ ↔ ∃ v ∃ u ∃ f ∃ g χ",
        s_cbvex2vv_2,
        ref="2exbii",
        note="2exbii cbvex2vv",
    )
    # bitri: chain the two biconditionals
    res = lb.ref(
        "res",
        "∃ x ∃ y ∃ z ∃ w φ ↔ ∃ v ∃ u ∃ f ∃ g χ",
        s_cbvex2vv_1,
        s_2exbii,
        ref="bitri",
        note="bitri cbvex2vv, 2exbii",
    )
    return lb.build(res)


def prove_nfmo1(sys: System) -> Proof:
    """nfmo1: Ⅎ x ∃* x φ.

    x is not free in "there exists at most one x such that φ".
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "nfmo1")
    # dfmo: ∃* x φ ↔ ∃ y ∀ x ( φ → x = y )
    s1 = lb.ref(
        "s1",
        "∃* x φ ↔ ∃ y ∀ x ( φ → x = y )",
        ref="dfmo",
        note="dfmo",
    )
    # nfexa2: Ⅎ x ∃ y ∀ x ( φ → x = y )
    s2 = lb.ref(
        "s2",
        "Ⅎ x ∃ y ∀ x ( φ → x = y )",
        ref="nfexa2",
        note="nfexa2",
    )
    # nfxfr: Ⅎ x ∃* x φ
    res = lb.ref(
        "res",
        "Ⅎ x ∃* x φ",
        s1,
        s2,
        ref="nfxfr",
        note="nfxfr dfmo, nfexa2",
    )
    return lb.build(res)


def prove_nfeu1(sys: System) -> Proof:
    """nfeu1: Ⅎ x ∃! x φ.
    x is not free in "there exists a unique x such that φ".
    (Contributed by NM, 12-Mar-1993.)
    """
    lb = ProofBuilder(sys, "nfeu1")
    # df-eu: ∃! x φ ↔ ( ∃ x φ ∧ ∃* x φ )
    s1 = lb.ref(
        "s1",
        "∃! x φ ↔ ( ∃ x φ ∧ ∃* x φ )",
        ref="df-eu",
        note="df-eu",
    )
    # nfe1: Ⅎ x ∃ x φ
    s2 = lb.ref(
        "s2",
        "Ⅎ x ∃ x φ",
        ref="nfe1",
        note="nfe1",
    )
    # nfmo1: Ⅎ x ∃* x φ
    s3 = lb.ref(
        "s3",
        "Ⅎ x ∃* x φ",
        ref="nfmo1",
        note="nfmo1",
    )
    # nfan s2, s3: Ⅎ x ( ∃ x φ ∧ ∃* x φ )
    s4 = lb.ref(
        "s4",
        "Ⅎ x ( ∃ x φ ∧ ∃* x φ )",
        s2,
        s3,
        ref="nfan",
        note="nfan nfe1, nfmo1",
    )
    # nfxfr s1, s4: Ⅎ x ∃! x φ
    res = lb.ref(
        "res",
        "Ⅎ x ∃! x φ",
        s1,
        s4,
        ref="nfxfr",
        note="nfxfr df-eu, nfan",
    )
    return lb.build(res)


def prove_nfeu1ALT(sys: System) -> Proof:
    """nfeu1ALT: Ⅎ x ∃! x φ.
    x is not free in "there exists a unique x such that φ".
    Alternate proof using eu6.  (Contributed by NM, 12-Mar-1993.)
    (Proof modification is discouraged.)  (New usage is discouraged.)
    """
    lb = ProofBuilder(sys, "nfeu1ALT")
    # eu6: ∃! x φ ↔ ∃ y ∀ x ( φ ↔ x = y )
    s1 = lb.ref(
        "s1",
        "∃! x φ ↔ ∃ y ∀ x ( φ ↔ x = y )",
        ref="eu6",
        note="eu6",
    )
    # nfexa2: Ⅎ x ∃ y ∀ x ( φ ↔ x = y )
    s2 = lb.ref(
        "s2",
        "Ⅎ x ∃ y ∀ x ( φ ↔ x = y )",
        ref="nfexa2",
        note="nfexa2",
    )
    # nfxfr s1, s2: Ⅎ x ∃! x φ
    res = lb.ref(
        "res",
        "Ⅎ x ∃! x φ",
        s1,
        s2,
        ref="nfxfr",
        note="nfxfr eu6, nfexa2",
    )
    return lb.build(res)


def prove_nfbidf(sys: System) -> Proof:
    """nfbidf: φ → ( Ⅎ x ψ ↔ Ⅎ x χ ).
    Deduction form of the not-free predicate: if ψ and χ are equivalent
    given φ, and φ is not free in x, then "x is not free in ψ" is equivalent
    to "x is not free in χ" given φ.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: exbid albid imbi12d df-nf 3bitr4g.
    """
    lb = ProofBuilder(sys, "nfbidf")
    hyp1 = lb.hyp("nfbidf.1", "Ⅎ x φ")
    hyp2 = lb.hyp("nfbidf.2", "φ → ( ψ ↔ χ )")
    # exbid: φ → ( ∃ x ψ ↔ ∃ x χ )
    s1 = lb.ref(
        "s1",
        "φ → ( ∃ x ψ ↔ ∃ x χ )",
        hyp1,
        hyp2,
        ref="exbid",
        note="exbid nfbidf.1, nfbidf.2",
    )
    # albid: φ → ( ∀ x ψ ↔ ∀ x χ )
    s2 = lb.ref(
        "s2",
        "φ → ( ∀ x ψ ↔ ∀ x χ )",
        hyp1,
        hyp2,
        ref="albid",
        note="albid nfbidf.1, nfbidf.2",
    )
    # imbi12d: φ → ( ( ∃ x ψ → ∀ x ψ ) ↔ ( ∃ x χ → ∀ x χ ) )
    s3 = lb.ref(
        "s3",
        "φ → ( ( ∃ x ψ → ∀ x ψ ) ↔ ( ∃ x χ → ∀ x χ ) )",
        s1,
        s2,
        ref="imbi12d",
        note="imbi12d exbid, albid",
    )
    # df-nf: ( Ⅎ x ψ ↔ ( ∃ x ψ → ∀ x ψ ) )
    s4 = lb.ref(
        "s4",
        "( Ⅎ x ψ ↔ ( ∃ x ψ → ∀ x ψ ) )",
        ref="df-nf",
        note="df-nf",
    )
    # df-nf: ( Ⅎ x χ ↔ ( ∃ x χ → ∀ x χ ) )
    s5 = lb.ref(
        "s5",
        "( Ⅎ x χ ↔ ( ∃ x χ → ∀ x χ ) )",
        ref="df-nf",
        note="df-nf",
    )
    # 3bitr4g: φ → ( Ⅎ x ψ ↔ Ⅎ x χ )
    res = lb.ref(
        "res",
        "φ → ( Ⅎ x ψ ↔ Ⅎ x χ )",
        s3,
        s4,
        s5,
        ref="3bitr4g",
        note="3bitr4g imbi12d, df-nf, df-nf",
    )
    return lb.build(res)


def prove_eupicka(sys: System) -> Proof:
    """eupicka: ( ∃! x φ ∧ ∃ x ( φ ∧ ψ ) ) → ∀ x ( φ → ψ ).
    If there exists a unique x such that φ and there also exists an
    x such that both φ and ψ hold, then φ universally implies ψ.
    (Contributed by NM, 23-Mar-1995.)
    """
    lb = ProofBuilder(sys, "eupicka")
    # nfeu1: Ⅎ x ∃! x φ
    s1 = lb.ref(
        "s1",
        "Ⅎ x ∃! x φ",
        ref="nfeu1",
        note="nfeu1",
    )
    # nfe1: Ⅎ x ∃ x ( φ ∧ ψ )
    s2 = lb.ref(
        "s2",
        "Ⅎ x ∃ x ( φ ∧ ψ )",
        ref="nfe1",
        note="nfe1",
    )
    # nfan s1, s2: Ⅎ x ( ∃! x φ ∧ ∃ x ( φ ∧ ψ ) )
    s3 = lb.ref(
        "s3",
        "Ⅎ x ( ∃! x φ ∧ ∃ x ( φ ∧ ψ ) )",
        s1,
        s2,
        ref="nfan",
        note="nfan nfeu1, nfe1",
    )
    # eupick: ( ∃! x φ ∧ ∃ x ( φ ∧ ψ ) ) → ( φ → ψ )
    s4 = lb.ref(
        "s4",
        "( ∃! x φ ∧ ∃ x ( φ ∧ ψ ) ) → ( φ → ψ )",
        ref="eupick",
        note="eupick",
    )
    # alrimi s3, s4: ( ∃! x φ ∧ ∃ x ( φ ∧ ψ ) ) → ∀ x ( φ → ψ )
    res = lb.ref(
        "res",
        "( ∃! x φ ∧ ∃ x ( φ ∧ ψ ) ) → ∀ x ( φ → ψ )",
        s3,
        s4,
        ref="alrimi",
        note="alrimi nfan, eupick",
    )
    return lb.build(res)


def prove_eupickbi(sys: System) -> Proof:
    """eupickbi: ∃! x φ → ( ∃ x ( φ ∧ ψ ) ↔ ∀ x ( φ → ψ ) ).
    If there exists a unique x such that φ, then the biconditional
    'there exists x such that φ and ψ' ↔ 'for all x, φ implies ψ' holds.
    (Contributed by NM, 23-Mar-1995.)
    """
    lb = ProofBuilder(sys, "eupickbi")
    # eupicka: ( ∃! x φ ∧ ∃ x ( φ ∧ ψ ) ) → ∀ x ( φ → ψ )
    s1 = lb.ref(
        "s1",
        "( ∃! x φ ∧ ∃ x ( φ ∧ ψ ) ) → ∀ x ( φ → ψ )",
        ref="eupicka",
        note="eupicka",
    )
    # ex with s1 as hypothesis: ∃! x φ → ( ∃ x ( φ ∧ ψ ) → ∀ x ( φ → ψ ) )
    s2 = lb.ref(
        "s2",
        "∃! x φ → ( ∃ x ( φ ∧ ψ ) → ∀ x ( φ → ψ ) )",
        s1,
        ref="ex",
        note="ex eupicka",
    )
    # euex: ∃! x φ → ∃ x φ
    s3 = lb.ref(
        "s3",
        "∃! x φ → ∃ x φ",
        ref="euex",
        note="euex",
    )
    # exintr: ∀ x ( φ → ψ ) → ( ∃ x φ → ∃ x ( φ ∧ ψ ) )
    s4 = lb.ref(
        "s4",
        "∀ x ( φ → ψ ) → ( ∃ x φ → ∃ x ( φ ∧ ψ ) )",
        ref="exintr",
        note="exintr",
    )
    # syl5com with s3, s4: ∃! x φ → ( ∀ x ( φ → ψ ) → ∃ x ( φ ∧ ψ ) )
    s5 = lb.ref(
        "s5",
        "∃! x φ → ( ∀ x ( φ → ψ ) → ∃ x ( φ ∧ ψ ) )",
        s3,
        s4,
        ref="syl5com",
        note="syl5com euex, exintr",
    )
    # impbid with s2, s5: ∃! x φ → ( ∃ x ( φ ∧ ψ ) ↔ ∀ x ( φ → ψ ) )
    res = lb.ref(
        "res",
        "∃! x φ → ( ∃ x ( φ ∧ ψ ) ↔ ∀ x ( φ → ψ ) )",
        s2,
        s5,
        ref="impbid",
        note="impbid ex, syl5com",
    )
    return lb.build(res)


def prove_eupickb(sys: System) -> Proof:
    """eupickb: ( ∃! x φ ∧ ∃! x ψ ∧ ∃ x ( φ ∧ ψ ) ) → ( φ ↔ ψ ).
    If there exists a unique x such that φ, a unique x such that ψ,
    and there exists an x such that both φ and ψ hold, then φ and ψ
    are equivalent.
    (Contributed by NM, 6-Jul-1995.)
    """
    lb = ProofBuilder(sys, "eupickb")
    # eupick: ( ∃! x φ ∧ ∃ x ( φ ∧ ψ ) ) → ( φ → ψ )
    s1 = lb.ref(
        "s1",
        "( ∃! x φ ∧ ∃ x ( φ ∧ ψ ) ) → ( φ → ψ )",
        ref="eupick",
        note="eupick",
    )
    # 3adant2: ( ∃! x φ ∧ ∃! x ψ ∧ ∃ x ( φ ∧ ψ ) ) → ( φ → ψ )
    s2 = lb.ref(
        "s2",
        "( ∃! x φ ∧ ∃! x ψ ∧ ∃ x ( φ ∧ ψ ) ) → ( φ → ψ )",
        s1,
        ref="3adant2",
        note="3adant2 eupick",
    )
    # eupick with φ and ψ swapped: ( ∃! x ψ ∧ ∃ x ( ψ ∧ φ ) ) → ( ψ → φ )
    s3 = lb.ref(
        "s3",
        "( ∃! x ψ ∧ ∃ x ( ψ ∧ φ ) ) → ( ψ → φ )",
        ref="eupick",
        note="eupick",
    )
    # exancom: ∃ x ( φ ∧ ψ ) ↔ ∃ x ( ψ ∧ φ )
    s4 = lb.ref(
        "s4",
        "∃ x ( φ ∧ ψ ) ↔ ∃ x ( ψ ∧ φ )",
        ref="exancom",
        note="exancom",
    )
    # sylan2b: ( ∃! x ψ ∧ ∃ x ( φ ∧ ψ ) ) → ( ψ → φ )
    s5 = lb.ref(
        "s5",
        "( ∃! x ψ ∧ ∃ x ( φ ∧ ψ ) ) → ( ψ → φ )",
        s4,
        s3,
        ref="sylan2b",
        note="sylan2b exancom, eupick",
    )
    # 3adant1: ( ∃! x φ ∧ ∃! x ψ ∧ ∃ x ( φ ∧ ψ ) ) → ( ψ → φ )
    s6 = lb.ref(
        "s6",
        "( ∃! x φ ∧ ∃! x ψ ∧ ∃ x ( φ ∧ ψ ) ) → ( ψ → φ )",
        s5,
        ref="3adant1",
        note="3adant1 sylan2b",
    )
    # impbid: ( ∃! x φ ∧ ∃! x ψ ∧ ∃ x ( φ ∧ ψ ) ) → ( φ ↔ ψ )
    res = lb.ref(
        "res",
        "( ∃! x φ ∧ ∃! x ψ ∧ ∃ x ( φ ∧ ψ ) ) → ( φ ↔ ψ )",
        s2,
        s6,
        ref="impbid",
        note="impbid 3adant2, 3adant1",
    )
    return lb.build(res)


def prove_cbvmow(sys: System) -> Proof:
    """cbvmow: ( ∃* x φ ↔ ∃* y ψ ).
    Change bound variable in an "exists at most one" quantifier
    using implicit substitution.
    From nfv, nfim, equequ1, imbi12d, cbvalv1, exbii, dfmo, and 3bitr4i.
    (Contributed by NM, 9-Mar-1995.)
    """
    lb = ProofBuilder(sys, "cbvmow")
    h_nfy = lb.hyp("cbvmow.1", "Ⅎ y φ")
    h_nfx = lb.hyp("cbvmow.2", "Ⅎ x ψ")
    h_iff = lb.hyp("cbvmow.3", "( x = y ) → ( φ ↔ ψ )")
    # nfv: Ⅎ y ( x = z )
    s1 = lb.ref(
        "s1",
        "Ⅎ y ( x = z )",
        ref="nfv",
        note="nfv",
    )
    # nfim: Ⅎ y ( φ → x = z )
    s2 = lb.ref(
        "s2",
        "Ⅎ y ( φ → x = z )",
        h_nfy,
        s1,
        ref="nfim",
        note="nfim cbvmow.1, nfv",
    )
    # nfv: Ⅎ x ( y = z )
    s3 = lb.ref(
        "s3",
        "Ⅎ x ( y = z )",
        ref="nfv",
        note="nfv",
    )
    # nfim: Ⅎ x ( ψ → y = z )
    s4 = lb.ref(
        "s4",
        "Ⅎ x ( ψ → y = z )",
        h_nfx,
        s3,
        ref="nfim",
        note="nfim cbvmow.2, nfv",
    )
    # equequ1: x = y → ( x = z ↔ y = z )
    s5 = lb.ref(
        "s5",
        "x = y → ( x = z ↔ y = z )",
        ref="equequ1",
        note="equequ1",
    )
    # imbi12d: x = y → ( ( φ → x = z ) ↔ ( ψ → y = z ) )
    s6 = lb.ref(
        "s6",
        "x = y → ( ( φ → x = z ) ↔ ( ψ → y = z ) )",
        h_iff,
        s5,
        ref="imbi12d",
        note="imbi12d cbvmow.3, equequ1",
    )
    # cbvalv1: ( ∀ x ( φ → x = z ) ↔ ∀ y ( ψ → y = z ) )
    s7 = lb.ref(
        "s7",
        "( ∀ x ( φ → x = z ) ↔ ∀ y ( ψ → y = z ) )",
        s2,
        s4,
        s6,
        ref="cbvalv1",
        note="cbvalv1",
    )
    # exbii: ( ∃ z ∀ x ( φ → x = z ) ↔ ∃ z ∀ y ( ψ → y = z ) )
    s8 = lb.ref(
        "s8",
        "( ∃ z ∀ x ( φ → x = z ) ↔ ∃ z ∀ y ( ψ → y = z ) )",
        s7,
        ref="exbii",
        note="exbii",
    )
    # dfmo: ∃* x φ ↔ ∃ z ∀ x ( φ → x = z )
    s9 = lb.ref(
        "s9",
        "∃* x φ ↔ ∃ z ∀ x ( φ → x = z )",
        ref="dfmo",
        note="dfmo",
    )
    # dfmo: ∃* y ψ ↔ ∃ z ∀ y ( ψ → y = z )
    s10 = lb.ref(
        "s10",
        "∃* y ψ ↔ ∃ z ∀ y ( ψ → y = z )",
        ref="dfmo",
        note="dfmo",
    )
    # 3bitr4i: ( ∃* x φ ↔ ∃* y ψ )
    res = lb.ref(
        "res",
        "( ∃* x φ ↔ ∃* y ψ )",
        s8,
        s9,
        s10,
        ref="3bitr4i",
        note="3bitr4i",
    )
    return lb.build(res)


def prove_cbvmo(sys: System) -> Proof:
    """cbvmo: ∃* x φ ↔ ∃* y ψ.

    Change bound variable in an "exists at most one" quantifier
    using explicit substitution.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "cbvmo")
    hyp_nfy = lb.hyp("cbvmo.1", "Ⅎ y φ")
    hyp_nfx = lb.hyp("cbvmo.2", "Ⅎ x ψ")
    hyp_eq = lb.hyp("cbvmo.3", "( x = y → ( φ ↔ ψ ) )")
    # sb8mo: ∃* x φ ↔ ∃* y [ y x φ
    s_sb8mo = lb.ref(
        "s_sb8mo",
        "∃* x φ ↔ ∃* y [ y x φ",
        hyp_nfy,
        ref="sb8mo",
        note="sb8mo cbvmo.1",
    )
    # sbie: [ y x φ ↔ ψ
    s_sbie = lb.ref(
        "s_sbie",
        "[ y x φ ↔ ψ",
        hyp_nfx,
        hyp_eq,
        ref="sbie",
        note="sbie cbvmo.2, cbvmo.3",
    )
    # mobii: ∃* y [ y x φ ↔ ∃* y ψ
    s_mobii = lb.ref(
        "s_mobii",
        "∃* y [ y x φ ↔ ∃* y ψ",
        s_sbie,
        ref="mobii",
        note="mobii sbie",
    )
    # bitri: ∃* x φ ↔ ∃* y ψ
    res = lb.ref(
        "res",
        "∃* x φ ↔ ∃* y ψ",
        s_sb8mo,
        s_mobii,
        ref="bitri",
        note="bitri sb8mo, mobii",
    )
    return lb.build(res)


def prove_cbveuw(sys: System) -> Proof:
    """cbveuw: ∃! x φ ↔ ∃! y ψ.
    Change bound variable in a "there exists a unique" quantifier
    using implicit substitution.
    From cbvexv1, cbvmow, anbi12i, df-eu, and 3bitr4i.
    (Contributed by NM, 25-Dec-1993.)
    """
    lb = ProofBuilder(sys, "cbveuw")
    h_nfy = lb.hyp("cbveuw.1", "Ⅎ y φ")
    h_nfx = lb.hyp("cbveuw.2", "Ⅎ x ψ")
    h_iff = lb.hyp("cbveuw.3", "( x = y ) → ( φ ↔ ψ )")
    # cbvexv1: ∃ x φ ↔ ∃ y ψ
    s1 = lb.ref(
        "s1",
        "∃ x φ ↔ ∃ y ψ",
        h_nfy,
        h_nfx,
        h_iff,
        ref="cbvexv1",
        note="cbvexv1",
    )
    # cbvmow: ∃* x φ ↔ ∃* y ψ
    s2 = lb.ref(
        "s2",
        "∃* x φ ↔ ∃* y ψ",
        h_nfy,
        h_nfx,
        h_iff,
        ref="cbvmow",
        note="cbvmow",
    )
    # anbi12i: ( ∃ x φ ∧ ∃* x φ ) ↔ ( ∃ y ψ ∧ ∃* y ψ )
    s3 = lb.ref(
        "s3",
        "( ∃ x φ ∧ ∃* x φ ) ↔ ( ∃ y ψ ∧ ∃* y ψ )",
        s1,
        s2,
        ref="anbi12i",
        note="anbi12i cbvexv1, cbvmow",
    )
    # df-eu: ∃! x φ ↔ ( ∃ x φ ∧ ∃* x φ )
    s4 = lb.ref(
        "s4",
        "∃! x φ ↔ ( ∃ x φ ∧ ∃* x φ )",
        ref="df-eu",
        note="df-eu",
    )
    # df-eu: ∃! y ψ ↔ ( ∃ y ψ ∧ ∃* y ψ )
    s5 = lb.ref(
        "s5",
        "∃! y ψ ↔ ( ∃ y ψ ∧ ∃* y ψ )",
        ref="df-eu",
        note="df-eu",
    )
    # 3bitr4i: ∃! x φ ↔ ∃! y ψ
    res = lb.ref(
        "res",
        "∃! x φ ↔ ∃! y ψ",
        s3,
        s4,
        s5,
        ref="3bitr4i",
        note="3bitr4i",
    )
    return lb.build(res)


def prove_cbveu(sys: System) -> Proof:
    """cbveu: ∃! x φ ↔ ∃! y ψ.

    Change bound variable in a "there exists a unique" quantifier
    using explicit substitution via sb8eu and sbie.
    (Contributed by NM, 12-Aug-1993.)
    """
    lb = ProofBuilder(sys, "cbveu")
    h1 = lb.hyp("cbveu.1", "Ⅎ y φ")
    h2 = lb.hyp("cbveu.2", "Ⅎ x ψ")
    h3 = lb.hyp("cbveu.3", "( x = y → ( φ ↔ ψ ) )")

    # sb8eu: ∃! x φ ↔ ∃! y [ y x φ
    s_sb8eu = lb.ref(
        "s_sb8eu",
        "∃! x φ ↔ ∃! y [ y x φ",
        h1,
        ref="sb8eu",
        note="sb8eu",
    )

    # sbie: [ y x φ ↔ ψ
    s_sbie = lb.ref(
        "s_sbie",
        "[ y x φ ↔ ψ",
        h2,
        h3,
        ref="sbie",
        note="sbie",
    )

    # eubii: ( ∃! y [ y x φ ↔ ∃! y ψ )
    s_eubii = lb.ref(
        "s_eubii",
        "( ∃! y [ y x φ ↔ ∃! y ψ )",
        s_sbie,
        ref="eubii",
        note="eubii",
    )

    # bitri: ( ∃! x φ ↔ ∃! y ψ )
    res = lb.ref(
        "res",
        "( ∃! x φ ↔ ∃! y ψ )",
        s_sb8eu,
        s_eubii,
        ref="bitri",
        note="bitri",
    )

    return lb.build(res)


def prove_cbveuALT(sys: System) -> Proof:
    """cbveuALT: ∃! x φ ↔ ∃! y ψ.

    Change bound variable in a "there exists a unique" quantifier
    using implicit substitution via cbvex and cbvmo.
    (Contributed by NM, 12-Aug-1993.)
    """
    lb = ProofBuilder(sys, "cbveuALT")
    h_nfy = lb.hyp("cbveu.1", "Ⅎ y φ")
    h_nfx = lb.hyp("cbveu.2", "Ⅎ x ψ")
    h_iff = lb.hyp("cbveu.3", "( x = y → ( φ ↔ ψ ) )")
    # cbvex: ∃ x φ ↔ ∃ y ψ
    s1 = lb.ref(
        "s1",
        "∃ x φ ↔ ∃ y ψ",
        h_nfy,
        h_nfx,
        h_iff,
        ref="cbvex",
        note="cbvex",
    )
    # cbvmo: ∃* x φ ↔ ∃* y ψ
    s2 = lb.ref(
        "s2",
        "∃* x φ ↔ ∃* y ψ",
        h_nfy,
        h_nfx,
        h_iff,
        ref="cbvmo",
        note="cbvmo",
    )
    # anbi12i: ( ∃ x φ ∧ ∃* x φ ) ↔ ( ∃ y ψ ∧ ∃* y ψ )
    s3 = lb.ref(
        "s3",
        "( ∃ x φ ∧ ∃* x φ ) ↔ ( ∃ y ψ ∧ ∃* y ψ )",
        s1,
        s2,
        ref="anbi12i",
        note="anbi12i cbvex, cbvmo",
    )
    # df-eu: ∃! x φ ↔ ( ∃ x φ ∧ ∃* x φ )
    s4 = lb.ref(
        "s4",
        "∃! x φ ↔ ( ∃ x φ ∧ ∃* x φ )",
        ref="df-eu",
        note="df-eu",
    )
    # df-eu: ∃! y ψ ↔ ( ∃ y ψ ∧ ∃* y ψ )
    s5 = lb.ref(
        "s5",
        "∃! y ψ ↔ ( ∃ y ψ ∧ ∃* y ψ )",
        ref="df-eu",
        note="df-eu",
    )
    # 3bitr4i: ∃! x φ ↔ ∃! y ψ
    res = lb.ref(
        "res",
        "∃! x φ ↔ ∃! y ψ",
        s3,
        s4,
        s5,
        ref="3bitr4i",
        note="3bitr4i",
    )
    return lb.build(res)


def prove_mof(sys: System) -> Proof:
    """mof: ∃* x φ ↔ ∃ y ∀ x ( φ → x = y ).
    Equivalence of "exists at most one" to an alternative existential form.
    From dfmo, the bound variable z is changed to y via cbvexv1, using
    not-free conditions built from mof.1, nfv, nfim, and nfal, and the
    equivalence chain built from equequ2, imbi2d, and albidv. Finally
    bitri combines dfmo with the cbvexv1 result.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "mof")
    hyp = lb.hyp("mof.1", "Ⅎ y φ")
    # Not-free conditions for ∀ x ( φ → x = z ) w.r.t. y
    s_nfy_eq = lb.ref("s_nfy_eq", "Ⅎ y ( x = z )", ref="nfv", note="nfv")
    s_nfy_imp = lb.ref(
        "s_nfy_imp", "Ⅎ y ( φ → x = z )", hyp, s_nfy_eq, ref="nfim", note="nfim mof.1, nfv"
    )
    s_nfyal = lb.ref(
        "s_nfyal",
        "Ⅎ y ∀ x ( φ → x = z )",
        s_nfy_imp,
        ref="nfal",
        note="nfal nfim",
    )
    # Not-free conditions for ∀ x ( φ → x = y ) w.r.t. z
    s_nfz_phi = lb.ref("s_nfz_phi", "Ⅎ z φ", ref="nfv", note="nfv")
    s_nfz_eq = lb.ref("s_nfz_eq", "Ⅎ z ( x = y )", ref="nfv", note="nfv")
    s_nfz_imp = lb.ref(
        "s_nfz_imp",
        "Ⅎ z ( φ → x = y )",
        s_nfz_phi,
        s_nfz_eq,
        ref="nfim",
        note="nfim nfv, nfv",
    )
    s_nfzal = lb.ref(
        "s_nfzal",
        "Ⅎ z ∀ x ( φ → x = y )",
        s_nfz_imp,
        ref="nfal",
        note="nfal nfim",
    )
    # Equivalence: z = y → ( ∀ x ( φ → x = z ) ↔ ∀ x ( φ → x = y ) )
    s_equ = lb.ref(
        "s_equ",
        "z = y → ( x = z ↔ x = y )",
        ref="equequ2",
        note="equequ2",
    )
    s_imbi2d = lb.ref(
        "s_imbi2d",
        "z = y → ( ( φ → x = z ) ↔ ( φ → x = y ) )",
        s_equ,
        ref="imbi2d",
        note="imbi2d equequ2",
    )
    s_al = lb.ref(
        "s_al",
        "z = y → ( ∀ x ( φ → x = z ) ↔ ∀ x ( φ → x = y ) )",
        s_imbi2d,
        ref="albidv",
        note="albidv imbi2d",
    )
    # cbvexv1: change bound variable z → y
    s_cbv = lb.ref(
        "s_cbv",
        "∃ z ∀ x ( φ → x = z ) ↔ ∃ y ∀ x ( φ → x = y )",
        s_nfyal,
        s_nfzal,
        s_al,
        ref="cbvexv1",
        note="cbvexv1",
    )
    # dfmo: ∃* x φ ↔ ∃ z ∀ x ( φ → x = z )
    s_dfmo = lb.ref(
        "s_dfmo",
        "∃* x φ ↔ ∃ z ∀ x ( φ → x = z )",
        ref="dfmo",
        note="dfmo",
    )
    # bitri: combine dfmo and cbvexv1
    res = lb.ref(
        "res",
        "∃* x φ ↔ ∃ y ∀ x ( φ → x = y )",
        s_dfmo,
        s_cbv,
        ref="bitri",
        note="bitri dfmo, cbvexv1",
    )
    return lb.build(res)


def prove_mo3(sys: System) -> Proof:
    """mo3: ∃* x φ ↔ ∀ x ∀ y ( ( φ ∧ [ y / x ] φ ) → x = y ).

    Equivalent definition of "exists at most one" using substitution.
    Both directions of the biconditional are proved separately and
    combined with impbii.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "mo3")
    hyp_nf = lb.hyp("mo3.nf", "Ⅎ y φ")

    # ── Forward direction: ∃* x φ → ∀ x ∀ y ( ( φ ∧ [ y / x ] φ ) → x = y ) ──

    # nfmo1: Ⅎ x ∃* x φ  (1)
    s_nfmo1 = lb.ref(
        "s_nfmo1",
        "Ⅎ x ∃* x φ",
        ref="nfmo1",
        note="nfmo1",
    )

    # nfmov: Ⅎ y ∃* x φ  (3)
    s_nfmov = lb.ref(
        "s_nfmov",
        "Ⅎ y ∃* x φ",
        hyp_nf,
        ref="nfmov",
        note="nfmov mo3.nf",
    )

    # dfmo: ∃* x φ ↔ ∃ z ∀ x ( φ → x = z )  (4)
    s_dfmo = lb.ref(
        "s_dfmo",
        "∃* x φ ↔ ∃ z ∀ x ( φ → x = z )",
        ref="dfmo",
        note="dfmo",
    )

    # sp: ∀ x ( φ → x = z ) → ( φ → x = z )  (5)
    s_sp = lb.ref(
        "s_sp",
        "∀ x ( φ → x = z ) → ( φ → x = z )",
        ref="sp",
        note="sp",
    )

    # spsbim: ∀ x ( φ → x = z ) → ( [ y / x ] φ → [ y / x ] x = z )  (6)
    s_spsbim = lb.ref(
        "s_spsbim",
        "∀ x ( φ → x = z ) → ( [ y / x ] φ → [ y / x ] x = z )",
        ref="spsbim",
        note="spsbim",
    )

    # equsb3: [ y / x ] x = z ↔ y = z  (7)
    s_equsb3 = lb.ref(
        "s_equsb3",
        "[ y / x ] x = z ↔ y = z",
        ref="equsb3",
        note="equsb3",
    )

    # imbitrdi s_spsbim, s_equsb3: ∀ x ( φ → x = z ) → ( [ y / x ] φ → y = z )  (8)
    s_imbitrdi = lb.ref(
        "s_imbitrdi",
        "∀ x ( φ → x = z ) → ( [ y / x ] φ → y = z )",
        s_spsbim,
        s_equsb3,
        ref="imbitrdi",
        note="imbitrdi spsbim, equsb3",
    )

    # anim12d s_sp, s_imbitrdi: ∀ x ( φ → x = z ) → ( ( φ ∧ [ y / x ] φ ) → ( x = z ∧ y = z ) )  (9)
    s_anim12d = lb.ref(
        "s_anim12d",
        "∀ x ( φ → x = z ) → ( ( φ ∧ [ y / x ] φ ) → ( x = z ∧ y = z ) )",
        s_sp,
        s_imbitrdi,
        ref="anim12d",
        note="anim12d sp, imbitrdi",
    )

    # equtr2: ( x = z ∧ y = z ) → x = y  (10)
    s_equtr2 = lb.ref(
        "s_equtr2",
        "( x = z ∧ y = z ) → x = y",
        ref="equtr2",
        note="equtr2",
    )

    # syl6 s_anim12d, s_equtr2: ∀ x ( φ → x = z ) → ( ( φ ∧ [ y / x ] φ ) → x = y )  (11)
    s_syl6 = lb.ref(
        "s_syl6",
        "∀ x ( φ → x = z ) → ( ( φ ∧ [ y / x ] φ ) → x = y )",
        s_anim12d,
        s_equtr2,
        ref="syl6",
        note="syl6 anim12d, equtr2",
    )

    # exlimiv s_syl6: ∃ z ∀ x ( φ → x = z ) → ( ( φ ∧ [ y / x ] φ ) → x = y )  (12)
    s_exlimiv = lb.ref(
        "s_exlimiv",
        "∃ z ∀ x ( φ → x = z ) → ( ( φ ∧ [ y / x ] φ ) → x = y )",
        s_syl6,
        ref="exlimiv",
        note="exlimiv syl6",
    )

    # sylbi s_dfmo, s_exlimiv: ∃* x φ → ( ( φ ∧ [ y / x ] φ ) → x = y )  (13)
    s_sylbi = lb.ref(
        "s_sylbi",
        "∃* x φ → ( ( φ ∧ [ y / x ] φ ) → x = y )",
        s_dfmo,
        s_exlimiv,
        ref="sylbi",
        note="sylbi dfmo, exlimiv",
    )

    # alrimi s_nfmov, s_sylbi: ∃* x φ → ∀ y ( ( φ ∧ [ y / x ] φ ) → x = y )  (14)
    s_alrimi_y = lb.ref(
        "s_alrimi_y",
        "∃* x φ → ∀ y ( ( φ ∧ [ y / x ] φ ) → x = y )",
        s_nfmov,
        s_sylbi,
        ref="alrimi",
        note="alrimi nfmov, sylbi",
    )

    # alrimi s_nfmo1, s_alrimi_y: ∃* x φ → ∀ x ∀ y ( ( φ ∧ [ y / x ] φ ) → x = y )  (15)
    s_fwd = lb.ref(
        "s_fwd",
        "∃* x φ → ∀ x ∀ y ( ( φ ∧ [ y / x ] φ ) → x = y )",
        s_nfmo1,
        s_alrimi_y,
        ref="alrimi",
        note="alrimi nfmo1, alrimi",
    )

    # ── Reverse direction: ∀ x ∀ y ( ( φ ∧ [ y / x ] φ ) → x = y ) → ∃* x φ ──

    # nfs1v: Ⅎ x [ y / x ] φ  (16)
    s_nfs1v = lb.ref(
        "s_nfs1v",
        "Ⅎ x [ y / x ] φ",
        ref="nfs1v",
        note="nfs1v",
    )

    # pm3.21: [ y / x ] φ → ( φ → ( φ ∧ [ y / x ] φ ) )  (17)
    s_pm321 = lb.ref(
        "s_pm321",
        "[ y / x ] φ → ( φ → ( φ ∧ [ y / x ] φ ) )",
        ref="pm3.21",
        note="pm3.21",
    )

    # imim1d s_pm321: [ y / x ] φ → ( ( ( φ ∧ [ y / x ] φ ) → x = y ) → ( φ → x = y ) )  (18)
    s_imim1d = lb.ref(
        "s_imim1d",
        "[ y / x ] φ → ( ( ( φ ∧ [ y / x ] φ ) → x = y ) → ( φ → x = y ) )",
        s_pm321,
        ref="imim1d",
        note="imim1d pm3.21",
    )

    # alimd s_nfs1v, s_imim1d: [ y / x ] φ → ( ∀ x ( ( φ ∧ [ y / x ] φ ) → x = y ) → ∀ x ( φ → x = y ) )  (19)
    s_alimd = lb.ref(
        "s_alimd",
        "[ y / x ] φ → ( ∀ x ( ( φ ∧ [ y / x ] φ ) → x = y ) → ∀ x ( φ → x = y ) )",
        s_nfs1v,
        s_imim1d,
        ref="alimd",
        note="alimd nfs1v, imim1d",
    )

    # com12 s_alimd: ∀ x ( ( φ ∧ [ y / x ] φ ) → x = y ) → ( [ y / x ] φ → ∀ x ( φ → x = y ) )  (20)
    s_com12 = lb.ref(
        "s_com12",
        "∀ x ( ( φ ∧ [ y / x ] φ ) → x = y ) → ( [ y / x ] φ → ∀ x ( φ → x = y ) )",
        s_alimd,
        ref="com12",
        note="com12 alimd",
    )

    # aleximi s_com12: ∀ y ∀ x ( ( φ ∧ [ y / x ] φ ) → x = y ) → ( ∃ y [ y / x ] φ → ∃ y ∀ x ( φ → x = y ) )  (21)
    s_aleximi = lb.ref(
        "s_aleximi",
        "∀ y ∀ x ( ( φ ∧ [ y / x ] φ ) → x = y ) → ( ∃ y [ y / x ] φ → ∃ y ∀ x ( φ → x = y ) )",
        s_com12,
        ref="aleximi",
        note="aleximi com12",
    )

    # sb8ef hyp_nf: ∃ x φ ↔ ∃ y [ y / x ] φ  (23)
    s_sb8ef = lb.ref(
        "s_sb8ef",
        "∃ x φ ↔ ∃ y [ y / x ] φ",
        hyp_nf,
        ref="sb8ef",
        note="sb8ef mo3.nf",
    )

    # mof hyp_nf: ∃* x φ ↔ ∃ y ∀ x ( φ → x = y )  (25)
    s_mof = lb.ref(
        "s_mof",
        "∃* x φ ↔ ∃ y ∀ x ( φ → x = y )",
        hyp_nf,
        ref="mof",
        note="mof mo3.nf",
    )

    # 3imtr4g s_aleximi, s_sb8ef, s_mof: ∀ y ∀ x ( ( φ ∧ [ y / x ] φ ) → x = y ) → ( ∃ x φ → ∃* x φ )  (26)
    s_3imtr4g = lb.ref(
        "s_3imtr4g",
        "∀ y ∀ x ( ( φ ∧ [ y / x ] φ ) → x = y ) → ( ∃ x φ → ∃* x φ )",
        s_aleximi,
        s_sb8ef,
        s_mof,
        ref="3imtr4g",
        note="3imtr4g aleximi, sb8ef, mof",
    )

    # moabs: ∃* x φ ↔ ( ∃ x φ → ∃* x φ )  (27)
    s_moabs = lb.ref(
        "s_moabs",
        "∃* x φ ↔ ( ∃ x φ → ∃* x φ )",
        ref="moabs",
        note="moabs",
    )

    # sylibr s_3imtr4g, s_moabs: ∀ y ∀ x ( ( φ ∧ [ y / x ] φ ) → x = y ) → ∃* x φ  (28)
    s_sylibr = lb.ref(
        "s_sylibr",
        "∀ y ∀ x ( ( φ ∧ [ y / x ] φ ) → x = y ) → ∃* x φ",
        s_3imtr4g,
        s_moabs,
        ref="sylibr",
        note="sylibr 3imtr4g, moabs",
    )

    # alcoms s_sylibr: ∀ x ∀ y ( ( φ ∧ [ y / x ] φ ) → x = y ) → ∃* x φ  (29)
    s_rev = lb.ref(
        "s_rev",
        "∀ x ∀ y ( ( φ ∧ [ y / x ] φ ) → x = y ) → ∃* x φ",
        s_sylibr,
        ref="alcoms",
        note="alcoms sylibr",
    )

    # impbii s_fwd, s_rev: ∃* x φ ↔ ∀ x ∀ y ( ( φ ∧ [ y / x ] φ ) → x = y )  (30)
    res = lb.ref(
        "res",
        "∃* x φ ↔ ∀ x ∀ y ( ( φ ∧ [ y / x ] φ ) → x = y )",
        s_fwd,
        s_rev,
        ref="impbii",
        note="impbii",
    )

    return lb.build(res)


def prove_mo(sys: System) -> Proof:
    """mo: ∃ y ∀ x ( φ → x = y ) ↔ ∀ x ∀ y ( ( φ ∧ [ y / x ] φ ) → x = y ).

    Equivalence of two alternative forms of "there exists at most one".
    From mof and mo3 via bitr3i.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "mo")
    hyp = lb.hyp("mo.nf", "Ⅎ y φ")

    # mof: ∃* x φ ↔ ∃ y ∀ x ( φ → x = y )
    s_mof = lb.ref(
        "s_mof",
        "∃* x φ ↔ ∃ y ∀ x ( φ → x = y )",
        hyp,
        ref="mof",
        note="mof mo.nf",
    )

    # mo3: ∃* x φ ↔ ∀ x ∀ y ( ( φ ∧ [ y / x ] φ ) → x = y )
    s_mo3 = lb.ref(
        "s_mo3",
        "∃* x φ ↔ ∀ x ∀ y ( ( φ ∧ [ y / x ] φ ) → x = y )",
        hyp,
        ref="mo3",
        note="mo3 mo.nf",
    )

    # bitr3i: ( ∃ y ∀ x ( φ → x = y ) ↔ ∀ x ∀ y ( ( φ ∧ [ y / x ] φ ) → x = y ) )
    res = lb.ref(
        "res",
        "∃ y ∀ x ( φ → x = y ) ↔ ∀ x ∀ y ( ( φ ∧ [ y / x ] φ ) → x = y )",
        s_mof,
        s_mo3,
        ref="bitr3i",
        note="bitr3i mof, mo3",
    )

    return lb.build(res)


def prove_mo4f(sys: System) -> Proof:
    """mo4f: ∃* x φ ↔ ∀ x ∀ y ( ( φ ∧ ψ ) → x = y ).

    At-most-one quantifier expressed with implicit substitution and
    a not-free hypothesis.  Given mo4f.1: Ⅎ x ψ and
    mo4f.2: x = y → ( φ ↔ ψ ).
    (Contributed by NM, 26-Jul-1995.)
    """
    lb = ProofBuilder(sys, "mo4f")
    h1 = lb.hyp("mo4f.1", "Ⅎ x ψ")
    h2 = lb.hyp("mo4f.2", "x = y → ( φ ↔ ψ )")

    # nfv: Ⅎ y φ — provides the hypothesis needed by mo3
    s_nfv = lb.ref(
        "s_nfv",
        "Ⅎ y φ",
        ref="nfv",
        note="nfv",
    )

    # mo3: ∃* x φ ↔ ∀ x ∀ y ( ( φ ∧ [ y / x ] φ ) → x = y )
    s_mo3 = lb.ref(
        "s_mo3",
        "∃* x φ ↔ ∀ x ∀ y ( ( φ ∧ [ y / x ] φ ) → x = y )",
        s_nfv,
        ref="mo3",
        note="mo3",
    )

    # sbiev: [ y / x ] φ ↔ ψ
    s_sbiev = lb.ref(
        "s_sbiev",
        "[ y / x ] φ ↔ ψ",
        h1,
        h2,
        ref="sbiev",
        note="sbiev",
    )

    # anbi2i: ( φ ∧ [ y / x ] φ ) ↔ ( φ ∧ ψ )
    s_anbi = lb.ref(
        "s_anbi",
        "( φ ∧ [ y / x ] φ ) ↔ ( φ ∧ ψ )",
        s_sbiev,
        ref="anbi2i",
        note="anbi2i",
    )

    # imbi1i: ( ( φ ∧ [ y / x ] φ ) → x = y ) ↔ ( ( φ ∧ ψ ) → x = y )
    s_imbi = lb.ref(
        "s_imbi",
        "( ( φ ∧ [ y / x ] φ ) → x = y ) ↔ ( ( φ ∧ ψ ) → x = y )",
        s_anbi,
        ref="imbi1i",
        note="imbi1i",
    )

    # 2albii: ∀ x ∀ y ( ( φ ∧ [ y / x ] φ ) → x = y ) ↔ ∀ x ∀ y ( ( φ ∧ ψ ) → x = y )
    s_2al = lb.ref(
        "s_2al",
        "∀ x ∀ y ( ( φ ∧ [ y / x ] φ ) → x = y ) ↔ ∀ x ∀ y ( ( φ ∧ ψ ) → x = y )",
        s_imbi,
        ref="2albii",
        note="2albii",
    )

    # bitri: combine mo3 and 2albii
    res = lb.ref(
        "res",
        "∃* x φ ↔ ∀ x ∀ y ( ( φ ∧ ψ ) → x = y )",
        s_mo3,
        s_2al,
        ref="bitri",
        note="bitri",
    )

    return lb.build(res)


def prove_modal_b(sys: System) -> Proof:
    """modal-b: φ → ∀ x ¬ ∀ x ¬ φ.
    Brouwersche axiom / modal logic B: the necessitation of the possibility.
    From axc7 with ¬ φ, we get ¬ ∀ x ¬ ∀ x ¬ φ → ¬ φ, then con4i gives the goal.
    """
    lb = ProofBuilder(sys, "modal-b")
    # axc7 with ¬ φ: ¬ ∀ x ¬ ∀ x ¬ φ → ¬ φ
    s1 = lb.ref(
        "s1",
        "¬ ∀ x ¬ ∀ x ¬ φ → ¬ φ",
        ref="axc7",
        note="axc7",
    )
    # con4i: (¬ ψ → ¬ χ) → (χ → ψ), with ψ = ∀x¬∀x¬φ, χ = φ
    res = lb.ref(
        "res",
        "φ → ∀ x ¬ ∀ x ¬ φ",
        s1,
        ref="con4i",
        note="con4i axc7",
    )
    return lb.build(res)


def prove_axc10(sys: System) -> Proof:
    """axc10: ∀ x ( x = y → ∀ x φ ) → φ.
    If a formula φ holds universally whenever a set is equal to another,
    then φ holds.  The proof contraposes ax6 (which asserts the existence
    of a set equal to y), uses al2imi to distribute the universal
    quantifier, cancels via mtoi, and finishes with axc7 and syl.
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "axc10")
    # con3: ( x = y → ∀ x φ ) → ( ¬ ∀ x φ → ¬ x = y )
    s1 = lb.ref(
        "s1",
        "( x = y → ∀ x φ ) → ( ¬ ∀ x φ → ¬ x = y )",
        ref="con3",
        note="con3",
    )
    # al2imi with s1: ∀ x ( x = y → ∀ x φ ) → ( ∀ x ¬ ∀ x φ → ∀ x ¬ x = y )
    s2 = lb.ref(
        "s2",
        "∀ x ( x = y → ∀ x φ ) → ( ∀ x ¬ ∀ x φ → ∀ x ¬ x = y )",
        s1,
        ref="al2imi",
        note="al2imi con3",
    )
    # ax6: ¬ ∀ x ¬ x = y
    s3 = lb.ref(
        "s3",
        "¬ ∀ x ¬ x = y",
        ref="ax6",
        note="ax6",
    )
    # mtoi with s3 (ax6) and s2: ∀ x ( x = y → ∀ x φ ) → ¬ ∀ x ¬ ∀ x φ
    s4 = lb.ref(
        "s4",
        "∀ x ( x = y → ∀ x φ ) → ¬ ∀ x ¬ ∀ x φ",
        s3,
        s2,
        ref="mtoi",
        note="mtoi ax6, al2imi",
    )
    # axc7: ¬ ∀ x ¬ ∀ x φ → φ
    s5 = lb.ref(
        "s5",
        "¬ ∀ x ¬ ∀ x φ → φ",
        ref="axc7",
        note="axc7",
    )
    # syl with s4 and s5: ∀ x ( x = y → ∀ x φ ) → φ
    res = lb.ref(
        "res",
        "∀ x ( x = y → ∀ x φ ) → φ",
        s4,
        s5,
        ref="syl",
        note="syl mtoi, axc7",
    )
    return lb.build(res)


def prove_moexexlem(sys: System) -> Proof:
    """moexexlem: ( ( ∃* x φ ∧ ∀ x ∃* y ψ ) → ∃* y ∃ x ( φ ∧ ψ ) ).

    Factor out the proof skeleton of moexex and moexexvw.
    (Contributed by Wolf Lammen, 2-Oct-2023.)
    """
    lb = ProofBuilder(sys, "moexexlem")
    h1 = lb.hyp("moexexlem.1", "Ⅎ y φ")
    h2 = lb.hyp("moexexlem.2", "Ⅎ y ∃* x φ")
    h3 = lb.hyp("moexexlem.3", "Ⅎ x ∃* y ∃ x ( φ ∧ ψ )")
    # 1. nfmo1: Ⅎ x ∃* x φ
    s1 = lb.ref("s1", "Ⅎ x ∃* x φ", ref="nfmo1", note="nfmo1")
    # 2. nfa1: Ⅎ x ∀ x ∃* y ψ
    s2 = lb.ref("s2", "Ⅎ x ∀ x ∃* y ψ", ref="nfa1", note="nfa1")
    # 4. nfim(2,3): Ⅎ x ( ∀ x ∃* y ψ → ∃* y ∃ x ( φ ∧ ψ ) )
    s4 = lb.ref(
        "s4",
        "Ⅎ x ( ∀ x ∃* y ψ → ∃* y ∃ x ( φ ∧ ψ ) )",
        s2,
        h3,
        ref="nfim",
        note="nfim nfa1, moexexlem.3",
    )
    # 7. mopick: ( ( ∃* x φ ∧ ∃ x ( φ ∧ ψ ) ) → ( φ → ψ ) )
    s7 = lb.ref(
        "s7",
        "( ∃* x φ ∧ ∃ x ( φ ∧ ψ ) ) → ( φ → ψ )",
        ref="mopick",
        note="mopick",
    )
    # 8. ex(7): ( ∃* x φ → ( ∃ x ( φ ∧ ψ ) → ( φ → ψ ) ) )
    s8 = lb.ref(
        "s8",
        "∃* x φ → ( ∃ x ( φ ∧ ψ ) → ( φ → ψ ) )",
        s7,
        ref="ex",
        note="ex mopick",
    )
    # 9. com23(8): ( ∃* x φ → ( φ → ( ∃ x ( φ ∧ ψ ) → ψ ) ) )
    s9 = lb.ref(
        "s9",
        "∃* x φ → ( φ → ( ∃ x ( φ ∧ ψ ) → ψ ) )",
        s8,
        ref="com23",
        note="com23 ex",
    )
    # 10. alrimd(5,6,9): ( ∃* x φ → ( φ → ∀ y ( ∃ x ( φ ∧ ψ ) → ψ ) ) )
    s10 = lb.ref(
        "s10",
        "∃* x φ → ( φ → ∀ y ( ∃ x ( φ ∧ ψ ) → ψ ) )",
        h2,
        h1,
        s9,
        ref="alrimd",
        note="alrimd moexexlem.2, moexexlem.1, com23",
    )
    # 11. moim: ( ∀ y ( ∃ x ( φ ∧ ψ ) → ψ ) → ( ∃* y ψ → ∃* y ∃ x ( φ ∧ ψ ) ) )
    s11 = lb.ref(
        "s11",
        "∀ y ( ∃ x ( φ ∧ ψ ) → ψ ) → ( ∃* y ψ → ∃* y ∃ x ( φ ∧ ψ ) )",
        ref="moim",
        note="moim",
    )
    # 12. spsd(11): ( ∀ y ( ∃ x ( φ ∧ ψ ) → ψ ) → ( ∀ x ∃* y ψ → ∃* y ∃ x ( φ ∧ ψ ) ) )
    s12 = lb.ref(
        "s12",
        "∀ y ( ∃ x ( φ ∧ ψ ) → ψ ) → ( ∀ x ∃* y ψ → ∃* y ∃ x ( φ ∧ ψ ) )",
        s11,
        ref="spsd",
        note="spsd moim",
    )
    # 13. syl6(10,12): ( ∃* x φ → ( φ → ( ∀ x ∃* y ψ → ∃* y ∃ x ( φ ∧ ψ ) ) ) )
    s13 = lb.ref(
        "s13",
        "∃* x φ → ( φ → ( ∀ x ∃* y ψ → ∃* y ∃ x ( φ ∧ ψ ) ) )",
        s10,
        s12,
        ref="syl6",
        note="syl6 alrimd, spsd",
    )
    # 14. exlimd(1,4,13): ( ∃* x φ → ( ∃ x φ → ( ∀ x ∃* y ψ → ∃* y ∃ x ( φ ∧ ψ ) ) ) )
    s14 = lb.ref(
        "s14",
        "∃* x φ → ( ∃ x φ → ( ∀ x ∃* y ψ → ∃* y ∃ x ( φ ∧ ψ ) ) )",
        s1,
        s4,
        s13,
        ref="exlimd",
        note="exlimd nfmo1, nfim, syl6",
    )
    # 16. nfex(15): Ⅎ y ∃ x φ
    s16 = lb.ref(
        "s16",
        "Ⅎ y ∃ x φ",
        h1,
        ref="nfex",
        note="nfex moexexlem.1",
    )
    # 17. exsimpl: ( ∃ x ( φ ∧ ψ ) → ∃ x φ )
    s17 = lb.ref(
        "s17",
        "∃ x ( φ ∧ ψ ) → ∃ x φ",
        ref="exsimpl",
        note="exsimpl",
    )
    # 18. exlimi(16,17): ( ∃ y ∃ x ( φ ∧ ψ ) → ∃ x φ )
    s18 = lb.ref(
        "s18",
        "∃ y ∃ x ( φ ∧ ψ ) → ∃ x φ",
        s16,
        s17,
        ref="exlimi",
        note="exlimi nfex, exsimpl",
    )
    # 19. nexmo: ( ¬ ∃ y ∃ x ( φ ∧ ψ ) → ∃* y ∃ x ( φ ∧ ψ ) )
    s19 = lb.ref(
        "s19",
        "¬ ∃ y ∃ x ( φ ∧ ψ ) → ∃* y ∃ x ( φ ∧ ψ )",
        ref="nexmo",
        note="nexmo",
    )
    # 20. nsyl5(18,19): ( ¬ ∃ x φ → ∃* y ∃ x ( φ ∧ ψ ) )
    s20 = lb.ref(
        "s20",
        "¬ ∃ x φ → ∃* y ∃ x ( φ ∧ ψ )",
        s18,
        s19,
        ref="nsyl5",
        note="nsyl5 exlimi, nexmo",
    )
    # 21. a1d(20): ( ¬ ∃ x φ → ( ∀ x ∃* y ψ → ∃* y ∃ x ( φ ∧ ψ ) ) )
    s21 = lb.ref(
        "s21",
        "¬ ∃ x φ → ( ∀ x ∃* y ψ → ∃* y ∃ x ( φ ∧ ψ ) )",
        s20,
        ref="a1d",
        note="a1d nsyl5",
    )
    # 22. pm2.61d1(14,21): ( ∃* x φ → ( ∀ x ∃* y ψ → ∃* y ∃ x ( φ ∧ ψ ) ) )
    s22 = lb.ref(
        "s22",
        "∃* x φ → ( ∀ x ∃* y ψ → ∃* y ∃ x ( φ ∧ ψ ) )",
        s14,
        s21,
        ref="pm2.61d1",
        note="pm2.61d1 exlimd, a1d",
    )
    # 23. imp(22): ( ( ∃* x φ ∧ ∀ x ∃* y ψ ) → ∃* y ∃ x ( φ ∧ ψ ) )
    res = lb.ref(
        "res",
        "( ∃* x φ ∧ ∀ x ∃* y ψ ) → ∃* y ∃ x ( φ ∧ ψ )",
        s22,
        ref="imp",
        note="imp pm2.61d1",
    )
    return lb.build(res)


def prove_moexexvw(sys: System) -> Proof:
    """moexexvw: ( ∃* x φ ∧ ∀ x ∃* y ψ ) → ∃* y ∃ x ( φ ∧ ψ ).

    Variant of moexex with distinct variable conditions replaced by
    non-freeness hypotheses.
    (Contributed by Wolf Lammen, 2-Oct-2023.)
    """
    lb = ProofBuilder(sys, "moexexvw")
    # nfv: Ⅎ y φ
    s1 = lb.ref("s1", "Ⅎ y φ", ref="nfv", note="nfv")
    # nfmov nfv: Ⅎ y ∃* x φ
    s2 = lb.ref("s2", "Ⅎ y ∃* x φ", s1, ref="nfmov", note="nfmov nfv")
    # nfe1: Ⅎ x ∃ x ( φ ∧ ψ )
    s3 = lb.ref("s3", "Ⅎ x ∃ x ( φ ∧ ψ )", ref="nfe1", note="nfe1")
    # nfmov nfe1: Ⅎ x ∃* y ∃ x ( φ ∧ ψ )
    s4 = lb.ref("s4", "Ⅎ x ∃* y ∃ x ( φ ∧ ψ )", s3, ref="nfmov", note="nfmov nfe1")
    # moexexlem: ( ∃* x φ ∧ ∀ x ∃* y ψ ) → ∃* y ∃ x ( φ ∧ ψ )
    res = lb.ref(
        "res",
        "( ∃* x φ ∧ ∀ x ∃* y ψ ) → ∃* y ∃ x ( φ ∧ ψ )",
        s1,
        s2,
        s4,
        ref="moexexlem",
        note="moexexlem nfv, nfmov, nfmov",
    )
    return lb.build(res)


def prove_moexexv(sys: System) -> Proof:
    """moexexv: ( ∃* x φ ∧ ∀ x ∃* y ψ ) → ∃* y ∃ x ( φ ∧ ψ ).

    Variant of moexex where the non-freeness hypothesis
    Ⅎ y φ is derived from nfv.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "moexexv")
    # nfv: Ⅎ y φ
    s1 = lb.ref("s1", "Ⅎ y φ", ref="nfv", note="nfv")
    # moexex: ( ∃* x φ ∧ ∀ x ∃* y ψ ) → ∃* y ∃ x ( φ ∧ ψ )
    res = lb.ref(
        "res",
        "( ∃* x φ ∧ ∀ x ∃* y ψ ) → ∃* y ∃ x ( φ ∧ ψ )",
        s1,
        ref="moexex",
        note="moexex nfv",
    )
    return lb.build(res)


def prove_moexex(sys: System) -> Proof:
    """moexex: ( ( ∃* x φ ∧ ∀ x ∃* y ψ ) → ∃* y ∃ x ( φ ∧ ψ ) ).

    Variant of moexexlem where the non-freeness hypothesis
    Ⅎ y φ is given instead of derived from nfv.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "moexex")
    h1 = lb.hyp("moexex.1", "Ⅎ y φ")
    # nfmo moexex.1: Ⅎ y ∃* x φ
    s2 = lb.ref("s2", "Ⅎ y ∃* x φ", h1, ref="nfmo", note="nfmo moexex.1")
    # nfe1: Ⅎ x ∃ x ( φ ∧ ψ )
    s3 = lb.ref("s3", "Ⅎ x ∃ x ( φ ∧ ψ )", ref="nfe1", note="nfe1")
    # nfmo nfe1: Ⅎ x ∃* y ∃ x ( φ ∧ ψ )
    s4 = lb.ref("s4", "Ⅎ x ∃* y ∃ x ( φ ∧ ψ )", s3, ref="nfmo", note="nfmo nfe1")
    # moexexlem: ( ∃* x φ ∧ ∀ x ∃* y ψ ) → ∃* y ∃ x ( φ ∧ ψ )
    res = lb.ref(
        "res",
        "( ∃* x φ ∧ ∀ x ∃* y ψ ) → ∃* y ∃ x ( φ ∧ ψ )",
        h1,
        s2,
        s4,
        ref="moexexlem",
        note="moexexlem moexex.1, nfmo, nfe1",
    )
    return lb.build(res)


def prove_mopick(sys: System) -> Proof:
    """mopick: ( ∃* x φ ∧ ∃ x ( φ ∧ ψ ) ) → ( φ → ψ ).

    If there exists at most one x such that φ, and there exists an x
    such that φ and ψ, then φ implies ψ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "mopick")
    # dfmo: ∃* x φ ↔ ∃ y ∀ x ( φ → x = y )
    s1 = lb.ref(
        "s1",
        "∃* x φ ↔ ∃ y ∀ x ( φ → x = y )",
        ref="dfmo",
        note="dfmo",
    )
    # sp: ∀ x ( φ → x = y ) → ( φ → x = y )
    s2 = lb.ref(
        "s2",
        "∀ x ( φ → x = y ) → ( φ → x = y )",
        ref="sp",
        note="sp",
    )
    # pm3.45: ( φ → x = y ) → ( ( φ ∧ ψ ) → ( x = y ∧ ψ ) )
    s3 = lb.ref(
        "s3",
        "( φ → x = y ) → ( ( φ ∧ ψ ) → ( x = y ∧ ψ ) )",
        ref="pm3.45",
        note="pm3.45",
    )
    # aleximi(3): ∀ x ( φ → x = y ) → ( ∃ x ( φ ∧ ψ ) → ∃ x ( x = y ∧ ψ ) )
    s4 = lb.ref(
        "s4",
        "∀ x ( φ → x = y ) → ( ∃ x ( φ ∧ ψ ) → ∃ x ( x = y ∧ ψ ) )",
        s3,
        ref="aleximi",
        note="aleximi pm3.45",
    )
    # ax12ev2: ∃ x ( x = y ∧ ψ ) → ( x = y → ψ )
    s5 = lb.ref(
        "s5",
        "∃ x ( x = y ∧ ψ ) → ( x = y → ψ )",
        ref="ax12ev2",
        note="ax12ev2",
    )
    # syl6(4,5): ∀ x ( φ → x = y ) → ( ∃ x ( φ ∧ ψ ) → ( x = y → ψ ) )
    s6 = lb.ref(
        "s6",
        "∀ x ( φ → x = y ) → ( ∃ x ( φ ∧ ψ ) → ( x = y → ψ ) )",
        s4,
        s5,
        ref="syl6",
        note="syl6 aleximi, ax12ev2",
    )
    # syl5d(2,6): ∀ x ( φ → x = y ) → ( ∃ x ( φ ∧ ψ ) → ( φ → ψ ) )
    s7 = lb.ref(
        "s7",
        "∀ x ( φ → x = y ) → ( ∃ x ( φ ∧ ψ ) → ( φ → ψ ) )",
        s2,
        s6,
        ref="syl5d",
        note="syl5d sp, syl6",
    )
    # exlimiv(7): ∃ y ∀ x ( φ → x = y ) → ( ∃ x ( φ ∧ ψ ) → ( φ → ψ ) )
    s8 = lb.ref(
        "s8",
        "∃ y ∀ x ( φ → x = y ) → ( ∃ x ( φ ∧ ψ ) → ( φ → ψ ) )",
        s7,
        ref="exlimiv",
        note="exlimiv syl5d",
    )
    # sylbi(1,8): ∃* x φ → ( ∃ x ( φ ∧ ψ ) → ( φ → ψ ) )
    s9 = lb.ref(
        "s9",
        "∃* x φ → ( ∃ x ( φ ∧ ψ ) → ( φ → ψ ) )",
        s1,
        s8,
        ref="sylbi",
        note="sylbi dfmo, exlimiv",
    )
    # imp(9): ( ∃* x φ ∧ ∃ x ( φ ∧ ψ ) ) → ( φ → ψ )
    res = lb.ref(
        "res",
        "( ∃* x φ ∧ ∃ x ( φ ∧ ψ ) ) → ( φ → ψ )",
        s9,
        ref="imp",
        note="imp sylbi",
    )
    return lb.build(res)


def prove_mopick2(sys: System) -> Proof:
    """mopick2: ( ∃* x φ ∧ ∃ x ( φ ∧ ψ ) ∧ ∃ x ( φ ∧ χ ) ) → ∃ x ( φ ∧ ψ ∧ χ ).
    If there exists at most one x such that φ, and there exists an x such
    that φ and ψ, and there exists an x such that φ and χ, then there
    exists an x such that φ, ψ, and χ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "mopick2")
    # nfmo1: Ⅎ x ∃* x φ
    s1 = lb.ref(
        "s1",
        "Ⅎ x ∃* x φ",
        ref="nfmo1",
        note="nfmo1",
    )
    # nfe1: Ⅎ x ∃ x ( φ ∧ ψ )
    s2 = lb.ref(
        "s2",
        "Ⅎ x ∃ x ( φ ∧ ψ )",
        ref="nfe1",
        note="nfe1",
    )
    # nfan: Ⅎ x ( ∃* x φ ∧ ∃ x ( φ ∧ ψ ) )
    s3 = lb.ref(
        "s3",
        "Ⅎ x ( ∃* x φ ∧ ∃ x ( φ ∧ ψ ) )",
        s1,
        s2,
        ref="nfan",
        note="nfan nfmo1, nfe1",
    )
    # mopick: ( ∃* x φ ∧ ∃ x ( φ ∧ ψ ) ) → ( φ → ψ )
    s4 = lb.ref(
        "s4",
        "( ∃* x φ ∧ ∃ x ( φ ∧ ψ ) ) → ( φ → ψ )",
        ref="mopick",
        note="mopick",
    )
    # ancld: ( ∃* x φ ∧ ∃ x ( φ ∧ ψ ) ) → ( φ → ( φ ∧ ψ ) )
    s5 = lb.ref(
        "s5",
        "( ∃* x φ ∧ ∃ x ( φ ∧ ψ ) ) → ( φ → ( φ ∧ ψ ) )",
        s4,
        ref="ancld",
        note="ancld mopick",
    )
    # anim1d: ( ∃* x φ ∧ ∃ x ( φ ∧ ψ ) ) → ( ( φ ∧ χ ) → ( ( φ ∧ ψ ) ∧ χ ) )
    s6 = lb.ref(
        "s6",
        "( ∃* x φ ∧ ∃ x ( φ ∧ ψ ) ) → ( ( φ ∧ χ ) → ( ( φ ∧ ψ ) ∧ χ ) )",
        s5,
        ref="anim1d",
        note="anim1d ancld",
    )
    # df-3an: ( φ ∧ ψ ∧ χ ) ↔ ( ( φ ∧ ψ ) ∧ χ )
    s7 = lb.ref(
        "s7",
        "( φ ∧ ψ ∧ χ ) ↔ ( ( φ ∧ ψ ) ∧ χ )",
        ref="df-3an",
        note="df-3an",
    )
    # imbitrrdi: ( ∃* x φ ∧ ∃ x ( φ ∧ ψ ) ) → ( ( φ ∧ χ ) → ( φ ∧ ψ ∧ χ ) )
    s8 = lb.ref(
        "s8",
        "( ∃* x φ ∧ ∃ x ( φ ∧ ψ ) ) → ( ( φ ∧ χ ) → ( φ ∧ ψ ∧ χ ) )",
        s6,
        s7,
        ref="imbitrrdi",
        note="imbitrrdi anim1d, df-3an",
    )
    # eximd: ( ∃* x φ ∧ ∃ x ( φ ∧ ψ ) ) → ( ∃ x ( φ ∧ χ ) → ∃ x ( φ ∧ ψ ∧ χ ) )
    s9 = lb.ref(
        "s9",
        "( ∃* x φ ∧ ∃ x ( φ ∧ ψ ) ) → ( ∃ x ( φ ∧ χ ) → ∃ x ( φ ∧ ψ ∧ χ ) )",
        s3,
        s8,
        ref="eximd",
        note="eximd nfan, imbitrrdi",
    )
    # 3impia: ( ∃* x φ ∧ ∃ x ( φ ∧ ψ ) ∧ ∃ x ( φ ∧ χ ) ) → ∃ x ( φ ∧ ψ ∧ χ )
    res = lb.ref(
        "res",
        "( ∃* x φ ∧ ∃ x ( φ ∧ ψ ) ∧ ∃ x ( φ ∧ χ ) ) → ∃ x ( φ ∧ ψ ∧ χ )",
        s9,
        ref="3impia",
        note="3impia eximd",
    )
    return lb.build(res)


def prove_cbval2v(sys: System) -> Proof:
    """cbval2v: ∀ x ∀ y φ ↔ ∀ z ∀ w ψ.
    Change two nested bound variables in a universal quantifier using
    implicit substitution, without requiring ax-13.  Uses ex to export
    the biconditional from the conjunction hypothesis, cbv2w to change
    the inner bound variables, and cbvalv1 to change the outer bound
    variable.
    (Contributed by NM, 22-Dec-2003.)  (Revised by BJ, 16-Jun-2019.)
    (Proof shortened by GG, 10-Jan-2024.)
    """
    lb = ProofBuilder(sys, "cbval2v")
    hyp_nfz_phi = lb.hyp("cbval2v.1", "Ⅎ z φ")
    hyp_nfw_phi = lb.hyp("cbval2v.2", "Ⅎ w φ")
    hyp_nfx_psi = lb.hyp("cbval2v.3", "Ⅎ x ψ")
    hyp_nfy_psi = lb.hyp("cbval2v.4", "Ⅎ y ψ")
    hyp_eq = lb.hyp("cbval2v.5", "( x = z ∧ y = w ) → ( φ ↔ ψ )")
    # ex cbval2v.5: ( x = z ) → ( ( y = w ) → ( φ ↔ ψ ) )
    s_ex = lb.ref(
        "s_ex",
        "( x = z ) → ( ( y = w ) → ( φ ↔ ψ ) )",
        hyp_eq,
        ref="ex",
        note="ex cbval2v.5",
    )
    # nfv: y and w are not free in ( x = z )
    s_nfy_xz = lb.ref("s_nfy_xz", "Ⅎ y ( x = z )", ref="nfv", note="nfv")
    s_nfw_xz = lb.ref("s_nfw_xz", "Ⅎ w ( x = z )", ref="nfv", note="nfv")
    # a1i cbval2v.2: ( x = z ) → Ⅎ w φ
    s_a1i_nfw = lb.ref(
        "s_a1i_nfw",
        "( x = z ) → Ⅎ w φ",
        hyp_nfw_phi,
        ref="a1i",
        note="a1i cbval2v.2",
    )
    # a1i cbval2v.4: ( x = z ) → Ⅎ y ψ
    s_a1i_nfy = lb.ref(
        "s_a1i_nfy",
        "( x = z ) → Ⅎ y ψ",
        hyp_nfy_psi,
        ref="a1i",
        note="a1i cbval2v.4",
    )
    # cbv2w nfv, nfv, a1i, a1i, ex: ( x = z ) → ( ∀ y φ ↔ ∀ w ψ )
    s_cbv2w = lb.ref(
        "s_cbv2w",
        "( x = z ) → ( ∀ y φ ↔ ∀ w ψ )",
        s_nfy_xz,
        s_nfw_xz,
        s_a1i_nfw,
        s_a1i_nfy,
        s_ex,
        ref="cbv2w",
        note="cbv2w nfv, nfv, a1i, a1i, ex",
    )
    # nfal cbval2v.1: Ⅎ z ∀ y φ
    s_nfz_aly = lb.ref(
        "s_nfz_aly",
        "Ⅎ z ∀ y φ",
        hyp_nfz_phi,
        ref="nfal",
        note="nfal cbval2v.1",
    )
    # nfal cbval2v.3: Ⅎ x ∀ w ψ
    s_nfx_alw = lb.ref(
        "s_nfx_alw",
        "Ⅎ x ∀ w ψ",
        hyp_nfx_psi,
        ref="nfal",
        note="nfal cbval2v.3",
    )
    # cbvalv1 nfal, nfal, cbv2w: ∀ x ∀ y φ ↔ ∀ z ∀ w ψ
    res = lb.ref(
        "res",
        "∀ x ∀ y φ ↔ ∀ z ∀ w ψ",
        s_nfz_aly,
        s_nfx_alw,
        s_cbv2w,
        ref="cbvalv1",
        note="cbvalv1 nfal, nfal, cbv2w",
    )
    return lb.build(res)


def prove_cbvex2v(sys: System) -> Proof:
    """cbvex2v: ∃ x ∃ y φ ↔ ∃ z ∃ w ψ.
    Change two nested bound variables in an existential quantifier using
    implicit substitution, without requiring ax-13.  The proof applies
    cbval2v to the negated formulas, combined with 2nexaln to convert
    existential to universal, and con4bii to remove the negations.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "cbvex2v")
    hyp_nfz_phi = lb.hyp("cbval2v.1", "Ⅎ z φ")
    hyp_nfw_phi = lb.hyp("cbval2v.2", "Ⅎ w φ")
    hyp_nfx_psi = lb.hyp("cbval2v.3", "Ⅎ x ψ")
    hyp_nfy_psi = lb.hyp("cbval2v.4", "Ⅎ y ψ")
    hyp_eq = lb.hyp("cbval2v.5", "( x = z ∧ y = w ) → ( φ ↔ ψ )")
    # nfn cbval2v.1: Ⅎ z ¬ φ
    s_nfn_z = lb.ref(
        "s_nfn_z",
        "Ⅎ z ¬ φ",
        hyp_nfz_phi,
        ref="nfn",
        note="nfn cbval2v.1",
    )
    # nfn cbval2v.2: Ⅎ w ¬ φ
    s_nfn_w = lb.ref(
        "s_nfn_w",
        "Ⅎ w ¬ φ",
        hyp_nfw_phi,
        ref="nfn",
        note="nfn cbval2v.2",
    )
    # nfn cbval2v.3: Ⅎ x ¬ ψ
    s_nfn_x = lb.ref(
        "s_nfn_x",
        "Ⅎ x ¬ ψ",
        hyp_nfx_psi,
        ref="nfn",
        note="nfn cbval2v.3",
    )
    # nfn cbval2v.4: Ⅎ y ¬ ψ
    s_nfn_y = lb.ref(
        "s_nfn_y",
        "Ⅎ y ¬ ψ",
        hyp_nfy_psi,
        ref="nfn",
        note="nfn cbval2v.4",
    )
    # notbid cbval2v.5: ( x = z ∧ y = w ) → ( ¬ φ ↔ ¬ ψ )
    s_notbid = lb.ref(
        "s_notbid",
        "( x = z ∧ y = w ) → ( ¬ φ ↔ ¬ ψ )",
        hyp_eq,
        ref="notbid",
        note="notbid cbval2v.5",
    )
    # cbval2v nfn, nfn, nfn, nfn, notbid: ∀ x ∀ y ¬ φ ↔ ∀ z ∀ w ¬ ψ
    s_cbval2v = lb.ref(
        "s_cbval2v",
        "∀ x ∀ y ¬ φ ↔ ∀ z ∀ w ¬ ψ",
        s_nfn_z,
        s_nfn_w,
        s_nfn_x,
        s_nfn_y,
        s_notbid,
        ref="cbval2v",
        note="cbval2v nfn, nfn, nfn, nfn, notbid",
    )
    # 2nexaln: ¬ ∃ x ∃ y φ ↔ ∀ x ∀ y ¬ φ
    s_2nexaln_left = lb.ref(
        "s_2nexaln_left",
        "¬ ∃ x ∃ y φ ↔ ∀ x ∀ y ¬ φ",
        ref="2nexaln",
        note="2nexaln",
    )
    # 2nexaln: ¬ ∃ z ∃ w ψ ↔ ∀ z ∀ w ¬ ψ
    s_2nexaln_right = lb.ref(
        "s_2nexaln_right",
        "¬ ∃ z ∃ w ψ ↔ ∀ z ∀ w ¬ ψ",
        ref="2nexaln",
        note="2nexaln",
    )
    # 3bitr4i: ( ¬ ∃ x ∃ y φ ↔ ¬ ∃ z ∃ w ψ )
    s_3bitr4i = lb.ref(
        "s_3bitr4i",
        "¬ ∃ x ∃ y φ ↔ ¬ ∃ z ∃ w ψ",
        s_cbval2v,
        s_2nexaln_left,
        s_2nexaln_right,
        ref="3bitr4i",
        note="3bitr4i",
    )
    # con4bii: ∃ x ∃ y φ ↔ ∃ z ∃ w ψ
    res = lb.ref(
        "res",
        "∃ x ∃ y φ ↔ ∃ z ∃ w ψ",
        s_3bitr4i,
        ref="con4bii",
        note="con4bii",
    )
    return lb.build(res)


def prove_exsb(sys: System) -> Proof:
    """exsb: ∃ x φ ↔ ∃ y ∀ x ( x = y → φ ).
    Existence expressed as an alternation of quantifiers
    (existential quantifier and universal quantifier with equality).
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "exsb")
    # nfv: Ⅎ y φ
    s_nfv = lb.ref(
        "s_nfv",
        "Ⅎ y φ",
        ref="nfv",
        note="nfv",
    )
    # nfa1: Ⅎ x ∀ x ( x = y → φ )
    s_nfa1 = lb.ref(
        "s_nfa1",
        "Ⅎ x ∀ x ( x = y → φ )",
        ref="nfa1",
        note="nfa1",
    )
    # ax12v: x = y → ( φ → ∀ x ( x = y → φ ) )
    s_ax12v = lb.ref(
        "s_ax12v",
        "x = y → ( φ → ∀ x ( x = y → φ ) )",
        ref="ax12v",
        note="ax12v",
    )
    # sp: ∀ x ( x = y → φ ) → ( x = y → φ )
    s_sp = lb.ref(
        "s_sp",
        "∀ x ( x = y → φ ) → ( x = y → φ )",
        ref="sp",
        note="sp",
    )
    # com12 on sp: x = y → ( ∀ x ( x = y → φ ) → φ )
    s_com12 = lb.ref(
        "s_com12",
        "x = y → ( ∀ x ( x = y → φ ) → φ )",
        s_sp,
        ref="com12",
        note="com12 sp",
    )
    # impbid: x = y → ( φ ↔ ∀ x ( x = y → φ ) )
    s_impbid = lb.ref(
        "s_impbid",
        "x = y → ( φ ↔ ∀ x ( x = y → φ ) )",
        s_ax12v,
        s_com12,
        ref="impbid",
        note="impbid ax12v, com12",
    )
    # cbvexv1: ∃ x φ ↔ ∃ y ∀ x ( x = y → φ )
    res = lb.ref(
        "res",
        "∃ x φ ↔ ∃ y ∀ x ( x = y → φ )",
        s_nfv,
        s_nfa1,
        s_impbid,
        ref="cbvexv1",
        note="cbvexv1 nfv, nfa1, impbid",
    )
    return lb.build(res)


def prove_pm11_53(sys: System) -> Proof:
    """pm11.53: ( ∀ x ∀ y ( φ → ψ ) ↔ ( ∃ x φ → ∀ y ψ ) ).
    Swap universal and existential quantifiers over an implication.
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "pm11.53")
    # 19.21v: ( ∀ y ( φ → ψ ) ↔ ( φ → ∀ y ψ ) )
    s1 = lb.ref(
        "s1",
        "( ∀ y ( φ → ψ ) ↔ ( φ → ∀ y ψ ) )",
        ref="19.21v",
        note="19.21v",
    )
    # albii: ( ∀ x ∀ y ( φ → ψ ) ↔ ∀ x ( φ → ∀ y ψ ) )
    s2 = lb.ref(
        "s2",
        "( ∀ x ∀ y ( φ → ψ ) ↔ ∀ x ( φ → ∀ y ψ ) )",
        s1,
        ref="albii",
        note="albii 19.21v",
    )
    # nfv: Ⅎ x ψ
    s3 = lb.ref(
        "s3",
        "Ⅎ x ψ",
        ref="nfv",
        note="nfv",
    )
    # nfal: Ⅎ x ∀ y ψ
    s4 = lb.ref(
        "s4",
        "Ⅎ x ∀ y ψ",
        s3,
        ref="nfal",
        note="nfal nfv",
    )
    # 19.23: ( ∀ x ( φ → ∀ y ψ ) ↔ ( ∃ x φ → ∀ y ψ ) )
    s5 = lb.ref(
        "s5",
        "( ∀ x ( φ → ∀ y ψ ) ↔ ( ∃ x φ → ∀ y ψ ) )",
        s4,
        ref="19.23",
        note="19.23 nfal",
    )
    # bitri: chain s2 and s5
    res = lb.ref(
        "res",
        "( ∀ x ∀ y ( φ → ψ ) ↔ ( ∃ x φ → ∀ y ψ ) )",
        s2,
        s5,
        ref="bitri",
        note="bitri",
    )
    return lb.build(res)


def prove_exlimi(sys: System) -> Proof:
    """exlimi: ∃ x φ → ψ.
    Inference form of the existential quantifier: from Ⅎ x ψ and φ → ψ,
    conclude ∃ x φ → ψ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "exlimi")
    hyp1 = lb.hyp("exlimi.1", "Ⅎ x ψ")
    hyp2 = lb.hyp("exlimi.2", "φ → ψ")
    # 19.23: Ⅎ x ψ ⊢ ∀ x ( φ → ψ ) ↔ ( ∃ x φ → ψ )
    s1 = lb.ref(
        "s1",
        "∀ x ( φ → ψ ) ↔ ( ∃ x φ → ψ )",
        hyp1,
        ref="19.23",
        note="19.23 exlimi.1",
    )
    # mpgbi: from biconditional and (φ → ψ), derive (∃ x φ → ψ)
    res = lb.ref(
        "res",
        "∃ x φ → ψ",
        s1,
        hyp2,
        ref="mpgbi",
        note="mpgbi 19.23, exlimi.2",
    )
    return lb.build(res)


def prove_exlimih(sys: System) -> Proof:
    """exlimih: ∃ x φ → ψ.
    Inference form of the existential quantifier with old-style non-freeness
    hypothesis: from ψ → ∀ x ψ and φ → ψ, conclude ∃ x φ → ψ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "exlimih")
    hyp1 = lb.hyp("exlimih.1", "ψ → ∀ x ψ")
    hyp2 = lb.hyp("exlimih.2", "φ → ψ")
    # nf5i: (ψ → ∀ x ψ) ⊢ Ⅎ x ψ
    s1 = lb.ref(
        "s1",
        "Ⅎ x ψ",
        hyp1,
        ref="nf5i",
        note="nf5i exlimih.1",
    )
    # exlimi: Ⅎ x ψ, φ → ψ ⊢ ∃ x φ → ψ
    res = lb.ref(
        "res",
        "∃ x φ → ψ",
        s1,
        hyp2,
        ref="exlimi",
        note="exlimi s1, exlimih.2",
    )
    return lb.build(res)


def prove_daraptiALT(sys: System) -> Proof:
    """daraptiALT: ∃ x ( χ ∧ ψ ).
    Alternative proof of darapti using spi, jca, and eximii.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "daraptiALT")
    hyp_maj = lb.hyp("darapti.maj", "∀ x ( φ → ψ )")
    hyp_min = lb.hyp("darapti.min", "∀ x ( φ → χ )")
    hyp_e = lb.hyp("darapti.e", "∃ x φ")
    s1 = lb.ref("s1", "φ → ψ", hyp_maj, ref="spi", note="spi darapti.maj")
    s2 = lb.ref("s2", "φ → χ", hyp_min, ref="spi", note="spi darapti.min")
    s3 = lb.ref("s3", "φ → ( χ ∧ ψ )", s2, s1, ref="jca", note="jca")
    res = lb.ref("res", "∃ x ( χ ∧ ψ )", hyp_e, s3, ref="eximii", note="eximii")
    return lb.build(res)


def prove_dariiALT(sys: System) -> Proof:
    """dariiALT: ∃ x ( χ ∧ ψ ).
    Alternative proof of darii using spi, anim2i, and eximii.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "dariiALT")
    hyp_maj = lb.hyp("darii.maj", "∀ x ( φ → ψ )")
    hyp_min = lb.hyp("darii.min", "∃ x ( χ ∧ φ )")
    s1 = lb.ref("s1", "φ → ψ", hyp_maj, ref="spi", note="spi darii.maj")
    s2 = lb.ref("s2", "( χ ∧ φ ) → ( χ ∧ ψ )", s1, ref="anim2i", note="anim2i spi")
    res = lb.ref("res", "∃ x ( χ ∧ ψ )", hyp_min, s2, ref="eximii", note="eximii anim2i")
    return lb.build(res)


def prove_festinoALT(sys: System) -> Proof:
    """festinoALT: ∃ x ( χ ∧ ¬ φ ).
    Alternative proof of festino using spi, con2i, anim2i, and eximii.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "festinoALT")
    hyp_maj = lb.hyp("festino.maj", "∀ x ( φ → ¬ ψ )")
    hyp_min = lb.hyp("festino.min", "∃ x ( χ ∧ ψ )")
    s1 = lb.ref("s1", "φ → ¬ ψ", hyp_maj, ref="spi", note="spi festino.maj")
    s2 = lb.ref("s2", "ψ → ¬ φ", s1, ref="con2i", note="con2i spi")
    s3 = lb.ref("s3", "( χ ∧ ψ ) → ( χ ∧ ¬ φ )", s2, ref="anim2i", note="anim2i con2i")
    res = lb.ref("res", "∃ x ( χ ∧ ¬ φ )", hyp_min, s3, ref="eximii", note="eximii anim2i")
    return lb.build(res)


def prove_axi5r(sys: System) -> Proof:
    """axi5r: ( ( ∀ x φ → ∀ x ψ ) → ∀ x ( ∀ x φ → ψ ) ).
    The antecedent of a universal implication implies the universal
    quantification of the consequent when the antecedent holds universally.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "axi5r")
    # hba1 at φ: ∀ x φ → ∀ x ∀ x φ
    hba1_phi = lb.ref(
        "hba1_phi",
        "∀ x φ → ∀ x ∀ x φ",
        ref="hba1",
        note="hba1",
    )
    # hba1 at ψ: ∀ x ψ → ∀ x ∀ x ψ
    hba1_psi = lb.ref(
        "hba1_psi",
        "∀ x ψ → ∀ x ∀ x ψ",
        ref="hba1",
        note="hba1",
    )
    # hbim hba1_phi hba1_psi: ( ∀ x φ → ∀ x ψ ) → ∀ x ( ∀ x φ → ∀ x ψ )
    hbim_step = lb.ref(
        "hbim_step",
        "( ∀ x φ → ∀ x ψ ) → ∀ x ( ∀ x φ → ∀ x ψ )",
        hba1_phi,
        hba1_psi,
        ref="hbim",
        note="hbim hba1, hba1",
    )
    # sp at ψ: ∀ x ψ → ψ
    sp_step = lb.ref(
        "sp_step",
        "∀ x ψ → ψ",
        ref="sp",
        note="sp",
    )
    # imim2i sp_step: ( ∀ x φ → ∀ x ψ ) → ( ∀ x φ → ψ )
    imim2i_step = lb.ref(
        "imim2i_step",
        "( ∀ x φ → ∀ x ψ ) → ( ∀ x φ → ψ )",
        sp_step,
        ref="imim2i",
        note="imim2i sp",
    )
    # alrimih hbim_step imim2i_step: ( ∀ x φ → ∀ x ψ ) → ∀ x ( ∀ x φ → ψ )
    res = lb.ref(
        "res",
        "( ∀ x φ → ∀ x ψ ) → ∀ x ( ∀ x φ → ψ )",
        hbim_step,
        imim2i_step,
        ref="alrimih",
        note="alrimih hbim, imim2i",
    )
    return lb.build(res)


def prove_barbariALT(sys: System) -> Proof:
    """barbariALT: ∃ x ( χ ∧ ψ ).
    Alternative proof of barbari using barbara, spi, ancli, and eximii.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "barbariALT")
    hyp_maj = lb.hyp("barbari.maj", "∀ x ( φ → ψ )")
    hyp_min = lb.hyp("barbari.min", "∀ x ( χ → φ )")
    hyp_e = lb.hyp("barbari.e", "∃ x χ")
    s1 = lb.ref("s1", "∀ x ( χ → ψ )", hyp_maj, hyp_min, ref="barbara", note="barbara")
    s2 = lb.ref("s2", "χ → ψ", s1, ref="spi", note="spi barbara")
    s3 = lb.ref("s3", "χ → ( χ ∧ ψ )", s2, ref="ancli", note="ancli spi")
    res = lb.ref("res", "∃ x ( χ ∧ ψ )", hyp_e, s3, ref="eximii", note="eximii ancli")
    return lb.build(res)


def prove_barocoALT(sys: System) -> Proof:
    """barocoALT: ∃ x ( χ ∧ ¬ φ ).
    Alternative proof of baroco using spi, con3i, anim2i, and eximii.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "barocoALT")
    hyp_maj = lb.hyp("baroco.maj", "∀ x ( φ → ψ )")
    hyp_min = lb.hyp("baroco.min", "∃ x ( χ ∧ ¬ ψ )")
    s1 = lb.ref("s1", "φ → ψ", hyp_maj, ref="spi", note="spi baroco.maj")
    s2 = lb.ref("s2", "¬ ψ → ¬ φ", s1, ref="con3i", note="con3i spi")
    s3 = lb.ref("s3", "( χ ∧ ¬ ψ ) → ( χ ∧ ¬ φ )", s2, ref="anim2i", note="anim2i con3i")
    res = lb.ref("res", "∃ x ( χ ∧ ¬ φ )", hyp_min, s3, ref="eximii", note="eximii anim2i")
    return lb.build(res)


def prove_sbal(sys: System) -> Proof:
    """sbal: [ z / y ] ∀ x φ ↔ ∀ x [ z / y ] φ.
    Substitution distributes over universal quantification when the
    substituted and bound variables are distinct.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbal")
    # dfsb: [z / y] ∀x φ ↔ ∀w (w = z → ∀y (y = w → ∀x φ))
    s1 = lb.ref(
        "s1",
        "[ z y ∀ x φ ↔ ∀ w ( w = z → ∀ y ( y = w → ∀ x φ ) )",
        ref="dfsb",
        note="dfsb",
    )
    # 19.21v: ∀x (y = w → φ) ↔ (y = w → ∀x φ)
    s2 = lb.ref(
        "s2",
        "∀ x ( y = w → φ ) ↔ ( y = w → ∀ x φ )",
        ref="19.21v",
        note="19.21v",
    )
    # bicomi of s2: (y = w → ∀x φ) ↔ ∀x (y = w → φ)
    s3 = lb.ref(
        "s3",
        "( y = w → ∀ x φ ) ↔ ∀ x ( y = w → φ )",
        s2,
        ref="bicomi",
        note="bicomi 19.21v",
    )
    # albii of s3: ∀y (y = w → ∀x φ) ↔ ∀y ∀x (y = w → φ)
    s4 = lb.ref(
        "s4",
        "∀ y ( y = w → ∀ x φ ) ↔ ∀ y ∀ x ( y = w → φ )",
        s3,
        ref="albii",
        note="albii bicomi",
    )
    # alcom: ∀y ∀x (y = w → φ) ↔ ∀x ∀y (y = w → φ)
    s5 = lb.ref(
        "s5",
        "∀ y ∀ x ( y = w → φ ) ↔ ∀ x ∀ y ( y = w → φ )",
        ref="alcom",
        note="alcom",
    )
    # bitri(s4, s5): ∀y(y = w → ∀x φ) ↔ ∀x ∀y(y = w → φ)
    s6 = lb.ref(
        "s6",
        "∀ y ( y = w → ∀ x φ ) ↔ ∀ x ∀ y ( y = w → φ )",
        s4,
        s5,
        ref="bitri",
        note="bitri albii, alcom",
    )
    # imbi2i of s6: (w = z → ∀y (y = w → ∀x φ)) ↔ (w = z → ∀x ∀y (y = w → φ))
    s7 = lb.ref(
        "s7",
        "( w = z → ∀ y ( y = w → ∀ x φ ) ) ↔ ( w = z → ∀ x ∀ y ( y = w → φ ) )",
        s6,
        ref="imbi2i",
        note="imbi2i bitri",
    )
    # 19.21v: ∀x (w = z → ∀y (y = w → φ)) ↔ (w = z → ∀x ∀y (y = w → φ))
    s8 = lb.ref(
        "s8",
        "∀ x ( w = z → ∀ y ( y = w → φ ) ) ↔ ( w = z → ∀ x ∀ y ( y = w → φ ) )",
        ref="19.21v",
        note="19.21v",
    )
    # bicomi of s8: (w = z → ∀x ∀y (y = w → φ)) ↔ ∀x (w = z → ∀y (y = w → φ))
    s9 = lb.ref(
        "s9",
        "( w = z → ∀ x ∀ y ( y = w → φ ) ) ↔ ∀ x ( w = z → ∀ y ( y = w → φ ) )",
        s8,
        ref="bicomi",
        note="bicomi 19.21v",
    )
    # bitri(s7, s9): (w = z → ∀y(y = w → ∀x φ)) ↔ ∀x(w = z → ∀y(y = w → φ))
    s10 = lb.ref(
        "s10",
        "( w = z → ∀ y ( y = w → ∀ x φ ) ) ↔ ∀ x ( w = z → ∀ y ( y = w → φ ) )",
        s7,
        s9,
        ref="bitri",
        note="bitri imbi2i, bicomi",
    )
    # albii of s10 with ∀w:
    # ∀w(w = z → ∀y(y = w → ∀x φ)) ↔ ∀w∀x(w = z → ∀y(y = w → φ))
    s11 = lb.ref(
        "s11",
        "∀ w ( w = z → ∀ y ( y = w → ∀ x φ ) ) ↔ ∀ w ∀ x ( w = z → ∀ y ( y = w → φ ) )",
        s10,
        ref="albii",
        note="albii bitri",
    )
    # alcom: ∀w∀x(w = z → ∀y(y = w → φ)) ↔ ∀x∀w(w = z → ∀y(y = w → φ))
    s12 = lb.ref(
        "s12",
        "∀ w ∀ x ( w = z → ∀ y ( y = w → φ ) ) ↔ ∀ x ∀ w ( w = z → ∀ y ( y = w → φ ) )",
        ref="alcom",
        note="alcom",
    )
    # bitri(s11, s12):
    # ∀w(w = z → ∀y(y = w → ∀x φ)) ↔ ∀x∀w(w = z → ∀y(y = w → φ))
    s13 = lb.ref(
        "s13",
        "∀ w ( w = z → ∀ y ( y = w → ∀ x φ ) ) ↔ ∀ x ∀ w ( w = z → ∀ y ( y = w → φ ) )",
        s11,
        s12,
        ref="bitri",
        note="bitri albii, alcom",
    )
    # dfsb: [z / y] φ ↔ ∀w (w = z → ∀y (y = w → φ))
    s14 = lb.ref(
        "s14",
        "[ z y φ ↔ ∀ w ( w = z → ∀ y ( y = w → φ ) )",
        ref="dfsb",
        note="dfsb",
    )
    # albii of s14: ∀x [z / y] φ ↔ ∀x ∀w (w = z → ∀y (y = w → φ))
    s15 = lb.ref(
        "s15",
        "∀ x [ z y φ ↔ ∀ x ∀ w ( w = z → ∀ y ( y = w → φ ) )",
        s14,
        ref="albii",
        note="albii dfsb",
    )
    # 3bitr4i(s13, s1, s15):
    # [z / y] ∀x φ ↔ ∀x [z / y] φ
    res = lb.ref(
        "res",
        "[ z y ∀ x φ ↔ ∀ x [ z y φ",
        s13,
        s1,
        s15,
        ref="3bitr4i",
        note="3bitr4i bitri, dfsb, albii",
    )
    return lb.build(res)


def prove_sbal1(sys: System) -> Proof:
    """sbal1: ¬ ∀𝑥 𝑥 = 𝑧 → ( [ 𝑧 / 𝑦 ] ∀𝑥 𝜑 ↔ ∀𝑥 [ 𝑧 / 𝑦 ] 𝜑 ).

    A distinctor version of ~ sbal .  (Contributed by NM, 2-Mar-1995.)
    """
    lb = ProofBuilder(sys, "sbal1")

    a = lb.ref("a", "¬ ∀ y y = z → ( [ z y ∀ x φ ↔ ∀ y ( y = z → ∀ x φ ) )", ref="sb4b")
    b = lb.ref("b", "Ⅎ y ¬ ∀ x x = z", ref="nfnae")
    c = lb.ref("c", "¬ ∀ x x = z → Ⅎ x y = z", ref="nfeqf2")
    d = lb.ref("d", "Ⅎ x y = z → ( ∀ x ( y = z → φ ) ↔ ( y = z → ∀ x φ ) )", ref="19.21t")
    e = lb.ref("e", "Ⅎ x y = z → ( ( y = z → ∀ x φ ) ↔ ∀ x ( y = z → φ ) )", d, ref="bicomd")
    f = lb.ref("f", "¬ ∀ x x = z → ( ( y = z → ∀ x φ ) ↔ ∀ x ( y = z → φ ) )", c, e, ref="syl")
    g = lb.ref("g", "¬ ∀ x x = z → ( ∀ y ( y = z → ∀ x φ ) ↔ ∀ y ∀ x ( y = z → φ ) )", b, f, ref="albid")
    h = lb.ref("h", "( ¬ ∀ x x = z ∧ ¬ ∀ y y = z ) → ( [ z y ∀ x φ ↔ ∀ y ∀ x ( y = z → φ ) )", a, g, ref="sylan9bbr")
    i = lb.ref("i", "Ⅎ x ¬ ∀ y y = z", ref="nfnae")
    j = lb.ref("j", "¬ ∀ y y = z → ( [ z y φ ↔ ∀ y ( y = z → φ ) )", ref="sb4b")
    k = lb.ref("k", "¬ ∀ y y = z → ( ∀ x [ z y φ ↔ ∀ x ∀ y ( y = z → φ ) )", i, j, ref="albid")
    s_alcom = lb.ref(
        "l", "∀ x ∀ y ( y = z → φ ) ↔ ∀ y ∀ x ( y = z → φ )", ref="alcom"
    )
    m = lb.ref(
        "m",
        "¬ ∀ y y = z → ( ∀ x [ z y φ ↔ ∀ y ∀ x ( y = z → φ ) )",
        k,
        s_alcom,
        ref="bitrdi",
    )
    n = lb.ref("n", "( ¬ ∀ x x = z ∧ ¬ ∀ y y = z ) → ( ∀ x [ z y φ ↔ ∀ y ∀ x ( y = z → φ ) )", m, ref="adantl")
    o = lb.ref("o", "( ¬ ∀ x x = z ∧ ¬ ∀ y y = z ) → ( [ z y ∀ x φ ↔ ∀ x [ z y φ )", h, n, ref="bitr4d")
    p = lb.ref("p", "¬ ∀ x x = z → ( ¬ ∀ y y = z → ( [ z y ∀ x φ ↔ ∀ x [ z y φ ) )", o, ref="ex")
    q = lb.ref("q", "y = z → ( ∀ x φ ↔ [ z y ∀ x φ )", ref="sbequ12")
    r = lb.ref("r", "∀ y y = z → ( ∀ x φ ↔ [ z y ∀ x φ )", q, ref="sps")
    s = lb.ref("s", "y = z → ( φ ↔ [ z y φ )", ref="sbequ12")
    t = lb.ref("t", "∀ y y = z → ( φ ↔ [ z y φ )", s, ref="sps")
    u = lb.ref("u", "∀ y y = z → ( ∀ x φ ↔ ∀ x [ z y φ )", t, ref="dral2")
    v = lb.ref("v", "∀ y y = z → ( [ z y ∀ x φ ↔ ∀ x [ z y φ )", r, u, ref="bitr3d")
    res = lb.ref("res", "¬ ∀ x x = z → ( [ z y ∀ x φ ↔ ∀ x [ z y φ )", p, v, ref="pm2.61d2")

    return lb.build(res)


def prove_sbal2(sys: System) -> Proof:
    """sbal2: ¬ ∀𝑥 𝑥 = 𝑦 → ( [ 𝑧 / 𝑦 ] ∀𝑥 𝜑 ↔ ∀𝑥 [ 𝑧 / 𝑦 ] 𝜑 ).

    Move quantifier in and out of substitution.  (Contributed by NM,
    2-Jan-2002.)  Remove a distinct variable constraint.
    (Revised by Wolf Lammen, 24-Dec-2022.)
    (Proof shortened by Wolf Lammen, 23-Sep-2023.)
    """
    lb = ProofBuilder(sys, "sbal2")

    # ── Branch 1: ∀ y y = z  (steps 40-59) ──

    # sbequ12: y = z → ( ∀ x φ ↔ [ z / y ] ∀ x φ )
    s40 = lb.ref(
        "s40",
        "y = z → ( ∀ x φ ↔ [ z y ∀ x φ )",
        ref="sbequ12",
        note="sbequ12",
    )
    # sps: ∀ y y = z → ( ∀ x φ ↔ [ z / y ] ∀ x φ )
    s41 = lb.ref(
        "s41",
        "∀ y y = z → ( ∀ x φ ↔ [ z y ∀ x φ )",
        s40,
        ref="sps",
        note="sps sbequ12",
    )

    # sbequ12: y = z → ( φ ↔ [ z / y ] φ )
    s55 = lb.ref(
        "s55",
        "y = z → ( φ ↔ [ z y φ )",
        ref="sbequ12",
        note="sbequ12",
    )
    # sps: ∀ y y = z → ( φ ↔ [ z / y ] φ )
    s56 = lb.ref(
        "s56",
        "∀ y y = z → ( φ ↔ [ z y φ )",
        s55,
        ref="sps",
        note="sps sbequ12",
    )
    # dral2: ∀ y y = z → ( ∀ x φ ↔ ∀ x [ z / y ] φ )
    s57 = lb.ref(
        "s57",
        "∀ y y = z → ( ∀ x φ ↔ ∀ x [ z y φ )",
        s56,
        ref="dral2",
        note="dral2 sps",
    )
    # bitr3d: ∀ y y = z → ( [ z / y ] ∀ x φ ↔ ∀ x [ z / y ] φ )
    s58 = lb.ref(
        "s58",
        "∀ y y = z → ( [ z y ∀ x φ ↔ ∀ x [ z y φ )",
        s41,
        s57,
        ref="bitr3d",
        note="bitr3d sps, dral2",
    )
    # adantl: ( ¬ ∀ x x = y ∧ ∀ y y = z ) → ( [ z / y ] ∀ x φ ↔ ∀ x [ z / y ] φ )
    s59 = lb.ref(
        "s59",
        "( ¬ ∀ x x = y ∧ ∀ y y = z ) → ( [ z y ∀ x φ ↔ ∀ x [ z y φ )",
        s58,
        ref="adantl",
        note="adantl bitr3d",
    )

    # ── Branch 2: ¬ ∀ y y = z  (steps 79-144) ──

    # sb4b: ¬ ∀ y y = z → ( [ z / y ] ∀ x φ ↔ ∀ y ( y = z → ∀ x φ ) )
    s79 = lb.ref(
        "s79",
        "¬ ∀ y y = z → ( [ z y ∀ x φ ↔ ∀ y ( y = z → ∀ x φ ) )",
        ref="sb4b",
        note="sb4b",
    )
    # adantl: ( ¬ ∀ x x = y ∧ ¬ ∀ y y = z ) → ( [ z / y ] ∀ x φ ↔ ∀ y ( y = z → ∀ x φ ) )
    s80 = lb.ref(
        "s80",
        "( ¬ ∀ x x = y ∧ ¬ ∀ y y = z ) → ( [ z y ∀ x φ ↔ ∀ y ( y = z → ∀ x φ ) )",
        s79,
        ref="adantl",
        note="adantl sb4b",
    )

    # nfnae: Ⅎ x ¬ ∀ y y = z
    s107 = lb.ref(
        "s107",
        "Ⅎ x ¬ ∀ y y = z",
        ref="nfnae",
        note="nfnae",
    )
    # sb4b: ¬ ∀ y y = z → ( [ z / y ] φ ↔ ∀ y ( y = z → φ ) )
    s111 = lb.ref(
        "s111",
        "¬ ∀ y y = z → ( [ z y φ ↔ ∀ y ( y = z → φ ) )",
        ref="sb4b",
        note="sb4b",
    )
    # albid: ¬ ∀ y y = z → ( ∀ x [ z / y ] φ ↔ ∀ x ∀ y ( y = z → φ ) )
    s112 = lb.ref(
        "s112",
        "¬ ∀ y y = z → ( ∀ x [ z y φ ↔ ∀ x ∀ y ( y = z → φ ) )",
        s107,
        s111,
        ref="albid",
        note="albid nfnae, sb4b",
    )
    # alcom: ∀ x ∀ y ( y = z → φ ) ↔ ∀ y ∀ x ( y = z → φ )
    s116 = lb.ref(
        "s116",
        "∀ x ∀ y ( y = z → φ ) ↔ ∀ y ∀ x ( y = z → φ )",
        ref="alcom",
        note="alcom",
    )
    # bitrdi: ¬ ∀ y y = z → ( ∀ x [ z / y ] φ ↔ ∀ y ∀ x ( y = z → φ ) )
    s117 = lb.ref(
        "s117",
        "¬ ∀ y y = z → ( ∀ x [ z y φ ↔ ∀ y ∀ x ( y = z → φ ) )",
        s112,
        s116,
        ref="bitrdi",
        note="bitrdi albid, alcom",
    )

    # nfnae: Ⅎ y ¬ ∀ x x = y
    s125 = lb.ref(
        "s125",
        "Ⅎ y ¬ ∀ x x = y",
        ref="nfnae",
        note="nfnae",
    )
    # nfeqf1: ¬ ∀ x x = y → Ⅎ x y = z
    s136 = lb.ref(
        "s136",
        "¬ ∀ x x = y → Ⅎ x y = z",
        ref="nfeqf1",
        note="nfeqf1",
    )
    # 19.21t: Ⅎ x y = z → ( ∀ x ( y = z → φ ) ↔ ( y = z → ∀ x φ ) )
    s140 = lb.ref(
        "s140",
        "Ⅎ x y = z → ( ∀ x ( y = z → φ ) ↔ ( y = z → ∀ x φ ) )",
        ref="19.21t",
        note="19.21t",
    )
    # syl: ¬ ∀ x x = y → ( ∀ x ( y = z → φ ) ↔ ( y = z → ∀ x φ ) )
    s141 = lb.ref(
        "s141",
        "¬ ∀ x x = y → ( ∀ x ( y = z → φ ) ↔ ( y = z → ∀ x φ ) )",
        s136,
        s140,
        ref="syl",
        note="syl nfeqf1, 19.21t",
    )
    # albid: ¬ ∀ x x = y → ( ∀ y ∀ x ( y = z → φ ) ↔ ∀ y ( y = z → ∀ x φ ) )
    s142 = lb.ref(
        "s142",
        "¬ ∀ x x = y → ( ∀ y ∀ x ( y = z → φ ) ↔ ∀ y ( y = z → ∀ x φ ) )",
        s125,
        s141,
        ref="albid",
        note="albid nfnae, syl",
    )
    # sylan9bbr: ( ¬ ∀ x x = y ∧ ¬ ∀ y y = z ) → ( ∀ x [ z / y ] φ ↔ ∀ y ( y = z → ∀ x φ ) )
    s143 = lb.ref(
        "s143",
        "( ¬ ∀ x x = y ∧ ¬ ∀ y y = z ) → ( ∀ x [ z y φ ↔ ∀ y ( y = z → ∀ x φ ) )",
        s117,
        s142,
        ref="sylan9bbr",
        note="sylan9bbr bitrdi, albid",
    )
    # bitr4d: ( ¬ ∀ x x = y ∧ ¬ ∀ y y = z ) → ( [ z / y ] ∀ x φ ↔ ∀ x [ z / y ] φ )
    s144 = lb.ref(
        "s144",
        "( ¬ ∀ x x = y ∧ ¬ ∀ y y = z ) → ( [ z y ∀ x φ ↔ ∀ x [ z y φ )",
        s80,
        s143,
        ref="bitr4d",
        note="bitr4d adantl, sylan9bbr",
    )

    # ── Combine branches: pm2.61dan (steps 144/145) ──

    # pm2.61dan: ¬ ∀ x x = y → ( [ z / y ] ∀ x φ ↔ ∀ x [ z / y ] φ )
    res = lb.ref(
        "res",
        "¬ ∀ x x = y → ( [ z y ∀ x φ ↔ ∀ x [ z y φ )",
        s59,
        s144,
        ref="pm2.61dan",
        note="pm2.61dan adantl, bitr4d",
    )

    return lb.build(res)


def prove_sbalex(sys: System) -> Proof:
    """sbalex: ∃ x ( x = t ∧ φ ) ↔ ∀ x ( x = t → φ ).
    An equivalence between an existentially quantified conjunction and a
    universally quantified implication involving an equality condition.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbalex")
    # nfe1: Ⅎ x ∃ x ( x = t ∧ φ )
    s_nfe1 = lb.ref(
        "s_nfe1",
        "Ⅎ x ∃ x ( x = t ∧ φ )",
        ref="nfe1",
        note="nfe1",
    )
    # ax12ev2: ∃ x ( x = t ∧ φ ) → ( x = t → φ )
    s_ax12ev2 = lb.ref(
        "s_ax12ev2",
        "∃ x ( x = t ∧ φ ) → ( x = t → φ )",
        ref="ax12ev2",
        note="ax12ev2",
    )
    # alrimi: Ⅎ x ∃ x ( x = t ∧ φ ), ∃ x ( x = t ∧ φ ) → ( x = t → φ )
    #         ⊢ ∃ x ( x = t ∧ φ ) → ∀ x ( x = t → φ )
    s_fwd = lb.ref(
        "s_fwd",
        "∃ x ( x = t ∧ φ ) → ∀ x ( x = t → φ )",
        s_nfe1,
        s_ax12ev2,
        ref="alrimi",
        note="alrimi nfe1, ax12ev2",
    )
    # equs4v: ∀ x ( x = t → φ ) → ∃ x ( x = t ∧ φ )
    s_rev = lb.ref(
        "s_rev",
        "∀ x ( x = t → φ ) → ∃ x ( x = t ∧ φ )",
        ref="equs4v",
        note="equs4v",
    )
    # impbii: ∃ x ( x = t ∧ φ ) ↔ ∀ x ( x = t → φ )
    res = lb.ref(
        "res",
        "∃ x ( x = t ∧ φ ) ↔ ∀ x ( x = t → φ )",
        s_fwd,
        s_rev,
        ref="impbii",
        note="impbii",
    )
    return lb.build(res)


def prove_sbalexOLD(sys: System) -> Proof:
    """sbalexOLD: ∃ x ( x = t ∧ φ ) ↔ ∀ x ( x = t → φ ).
    An equivalence between an existentially quantified conjunction and a
    universally quantified implication involving an equality condition.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbalexOLD")
    # nfa1: Ⅎ x ∀ x ( x = t → φ )
    s1 = lb.ref(
        "s1",
        "Ⅎ x ∀ x ( x = t → φ )",
        ref="nfa1",
        note="nfa1",
    )
    # ax12v2: x = t → ( φ → ∀ x ( x = t → φ ) )
    s2 = lb.ref(
        "s2",
        "x = t → ( φ → ∀ x ( x = t → φ ) )",
        ref="ax12v2",
        note="ax12v2",
    )
    # imp: ( x = t ∧ φ ) → ∀ x ( x = t → φ )
    s3 = lb.ref(
        "s3",
        "( x = t ∧ φ ) → ∀ x ( x = t → φ )",
        s2,
        ref="imp",
        note="imp ax12v2",
    )
    # exlimi: ∃ x ( x = t ∧ φ ) → ∀ x ( x = t → φ )
    s4 = lb.ref(
        "s4",
        "∃ x ( x = t ∧ φ ) → ∀ x ( x = t → φ )",
        s1,
        s3,
        ref="exlimi",
        note="exlimi nfa1, imp",
    )
    # equs4v: ∀ x ( x = t → φ ) → ∃ x ( x = t ∧ φ )
    s5 = lb.ref(
        "s5",
        "∀ x ( x = t → φ ) → ∃ x ( x = t ∧ φ )",
        ref="equs4v",
        note="equs4v",
    )
    # impbii: ∃ x ( x = t ∧ φ ) ↔ ∀ x ( x = t → φ )
    res = lb.ref(
        "res",
        "∃ x ( x = t ∧ φ ) ↔ ∀ x ( x = t → φ )",
        s4,
        s5,
        ref="impbii",
        note="impbii exlimi, equs4v",
    )
    return lb.build(res)


def prove_19_42vv(sys: System) -> Proof:
    """19.42vv: ∃ x ∃ y ( φ ∧ ψ ) ↔ ( φ ∧ ∃ x ∃ y ψ ).
    Existential quantifier distributes over conjunction when the first
    conjunct does not contain the bound variables.
    """
    lb = ProofBuilder(sys, "19.42vv")
    # exdistr: ∃ x ∃ y ( φ ∧ ψ ) ↔ ∃ x ( φ ∧ ∃ y ψ )
    s1 = lb.ref(
        "s1",
        "∃ x ∃ y ( φ ∧ ψ ) ↔ ∃ x ( φ ∧ ∃ y ψ )",
        ref="exdistr",
        note="exdistr",
    )
    # 19.42v with ψ := ∃ y ψ: ∃ x ( φ ∧ ∃ y ψ ) ↔ ( φ ∧ ∃ x ∃ y ψ )
    s2 = lb.ref(
        "s2",
        "∃ x ( φ ∧ ∃ y ψ ) ↔ ( φ ∧ ∃ x ∃ y ψ )",
        ref="19.42v",
        note="19.42v",
    )
    # bitri: chain s1 and s2
    res = lb.ref(
        "res",
        "∃ x ∃ y ( φ ∧ ψ ) ↔ ( φ ∧ ∃ x ∃ y ψ )",
        s1,
        s2,
        ref="bitri",
        note="bitri exdistr, 19.42v",
    )
    return lb.build(res)


def prove_exdistr(sys: System) -> Proof:
    """exdistr: ∃ x ∃ y ( φ ∧ ψ ) ↔ ∃ x ( φ ∧ ∃ y ψ ).
    Existential quantifier distributes over conjunction.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "exdistr")
    # 19.42v: ∃ y ( φ ∧ ψ ) ↔ ( φ ∧ ∃ y ψ )
    s1 = lb.ref(
        "s1",
        "∃ y ( φ ∧ ψ ) ↔ ( φ ∧ ∃ y ψ )",
        ref="19.42v",
        note="19.42v",
    )
    # exbii: add ∃ x to both sides
    res = lb.ref(
        "res",
        "∃ x ∃ y ( φ ∧ ψ ) ↔ ∃ x ( φ ∧ ∃ y ψ )",
        s1,
        ref="exbii",
        note="exbii 19.42v",
    )
    return lb.build(res)


def prove_exdistrf(sys: System) -> Proof:
    """exdistrf: ∃ x ∃ y ( φ ∧ ψ ) → ∃ x ( φ ∧ ∃ y ψ ).
    Distribution of existential quantifier with a conditional not-free
    hypothesis.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "exdistrf")
    hyp = lb.hyp("exdistrf.1", "¬ ∀ x x = y → Ⅎ y φ")
    # 19.8a: ψ → ∃ y ψ
    s_19_8a = lb.ref(
        "s_19_8a",
        "ψ → ∃ y ψ",
        ref="19.8a",
        note="19.8a",
    )
    # anim2i with 19.8a: ( φ ∧ ψ ) → ( φ ∧ ∃ y ψ )
    s_anim2i = lb.ref(
        "s_anim2i",
        "( φ ∧ ψ ) → ( φ ∧ ∃ y ψ )",
        s_19_8a,
        ref="anim2i",
        note="anim2i 19.8a",
    )
    # eximi with anim2i: ∃ y ( φ ∧ ψ ) → ∃ y ( φ ∧ ∃ y ψ )
    s_eximi = lb.ref(
        "s_eximi",
        "∃ y ( φ ∧ ψ ) → ∃ y ( φ ∧ ∃ y ψ )",
        s_anim2i,
        ref="eximi",
        note="eximi anim2i",
    )
    # ===== Case A: ¬ ∀ x x = y =====
    # 19.40: ∃ y ( φ ∧ ψ ) → ( ∃ y φ ∧ ∃ y ψ )
    s_19_40 = lb.ref(
        "s_19_40",
        "∃ y ( φ ∧ ψ ) → ( ∃ y φ ∧ ∃ y ψ )",
        ref="19.40",
        note="19.40",
    )
    # 19.9d with hypothesis: ( ¬ ∀ x x = y ) → ( ∃ y φ → φ )
    s_19_9d = lb.ref(
        "s_19_9d",
        "¬ ∀ x x = y → ( ∃ y φ → φ )",
        hyp,
        ref="19.9d",
        note="19.9d exdistrf.1",
    )
    # anim1d with 19.9d: ( ¬ ∀ x x = y ) → ( ( ∃ y φ ∧ ∃ y ψ ) → ( φ ∧ ∃ y ψ ) )
    s_anim1d = lb.ref(
        "s_anim1d",
        "¬ ∀ x x = y → ( ( ∃ y φ ∧ ∃ y ψ ) → ( φ ∧ ∃ y ψ ) )",
        s_19_9d,
        ref="anim1d",
        note="anim1d 19.9d",
    )
    # 19.8a: ( φ ∧ ∃ y ψ ) → ∃ x ( φ ∧ ∃ y ψ )
    s_19_8a2 = lb.ref(
        "s_19_8a2",
        "( φ ∧ ∃ y ψ ) → ∃ x ( φ ∧ ∃ y ψ )",
        ref="19.8a",
        note="19.8a",
    )
    # syl56 chains 19.40, anim1d, 19.8a
    s_case_a = lb.ref(
        "s_case_a",
        "¬ ∀ x x = y → ( ∃ y ( φ ∧ ψ ) → ∃ x ( φ ∧ ∃ y ψ ) )",
        s_19_40,
        s_anim1d,
        s_19_8a2,
        ref="syl56",
        note="syl56 19.40, anim1d, 19.8a",
    )
    # ===== Case B: ∀ x x = y =====
    # biidd: ∀ x x = y → ( ( φ ∧ ∃ y ψ ) ↔ ( φ ∧ ∃ y ψ ) )
    s_biidd = lb.ref(
        "s_biidd",
        "∀ x x = y → ( ( φ ∧ ∃ y ψ ) ↔ ( φ ∧ ∃ y ψ ) )",
        ref="biidd",
        note="biidd",
    )
    # drex1 with biidd: ∀ x x = y → ( ∃ x ( φ ∧ ∃ y ψ ) ↔ ∃ y ( φ ∧ ∃ y ψ ) )
    s_drex1 = lb.ref(
        "s_drex1",
        "∀ x x = y → ( ∃ x ( φ ∧ ∃ y ψ ) ↔ ∃ y ( φ ∧ ∃ y ψ ) )",
        s_biidd,
        ref="drex1",
        note="drex1 biidd",
    )
    # imbitrrid chains eximi and drex1
    s_case_b = lb.ref(
        "s_case_b",
        "∀ x x = y → ( ∃ y ( φ ∧ ψ ) → ∃ x ( φ ∧ ∃ y ψ ) )",
        s_eximi,
        s_drex1,
        ref="imbitrrid",
        note="imbitrrid eximi, drex1",
    )
    # ===== pm2.61i: combine both cases =====
    s_pm2_61i = lb.ref(
        "s_pm2_61i",
        "∃ y ( φ ∧ ψ ) → ∃ x ( φ ∧ ∃ y ψ )",
        s_case_b,
        s_case_a,
        ref="pm2.61i",
        note="pm2.61i",
    )
    # ===== exlimi: add ∃ x quantifier =====
    # nfe1: Ⅎ x ∃ x ( φ ∧ ∃ y ψ )
    s_nfe1 = lb.ref(
        "s_nfe1",
        "Ⅎ x ∃ x ( φ ∧ ∃ y ψ )",
        ref="nfe1",
        note="nfe1",
    )
    # exlimi: ∃ x ∃ y ( φ ∧ ψ ) → ∃ x ( φ ∧ ∃ y ψ )
    res = lb.ref(
        "res",
        "∃ x ∃ y ( φ ∧ ψ ) → ∃ x ( φ ∧ ∃ y ψ )",
        s_nfe1,
        s_pm2_61i,
        ref="exlimi",
        note="exlimi",
    )
    return lb.build(res)


def prove_exdistr2(sys: System) -> Proof:
    """exdistr2: ∃ x ∃ y ∃ z ( φ ∧ ψ ) ↔ ∃ x ( φ ∧ ∃ y ∃ z ψ ).
    Existential quantifier distributes over conjunction
    (three variables).
    """
    lb = ProofBuilder(sys, "exdistr2")
    # 19.42vv: ∃ y ∃ z ( φ ∧ ψ ) ↔ ( φ ∧ ∃ y ∃ z ψ )
    s1 = lb.ref(
        "s1",
        "∃ y ∃ z ( φ ∧ ψ ) ↔ ( φ ∧ ∃ y ∃ z ψ )",
        ref="19.42vv",
        note="19.42vv",
    )
    # exbii: add ∃ x to both sides
    res = lb.ref(
        "res",
        "∃ x ∃ y ∃ z ( φ ∧ ψ ) ↔ ∃ x ( φ ∧ ∃ y ∃ z ψ )",
        s1,
        ref="exbii",
        note="exbii 19.42vv",
    )
    return lb.build(res)


def prove_exdistrv(sys: System) -> Proof:
    """exdistrv: ∃ x ∃ y ( φ ∧ ψ ) ↔ ( ∃ x φ ∧ ∃ y ψ ).
    Existential quantifier distributes over conjunction.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "exdistrv")
    # exdistr: ∃ x ∃ y ( φ ∧ ψ ) ↔ ∃ x ( φ ∧ ∃ y ψ )
    s1 = lb.ref(
        "s1",
        "∃ x ∃ y ( φ ∧ ψ ) ↔ ∃ x ( φ ∧ ∃ y ψ )",
        ref="exdistr",
        note="exdistr",
    )
    # 19.41v: ∃ x ( φ ∧ ∃ y ψ ) ↔ ( ∃ x φ ∧ ∃ y ψ )
    s2 = lb.ref(
        "s2",
        "∃ x ( φ ∧ ∃ y ψ ) ↔ ( ∃ x φ ∧ ∃ y ψ )",
        ref="19.41v",
        note="19.41v",
    )
    # bitri: chain s1 and s2
    res = lb.ref(
        "res",
        "∃ x ∃ y ( φ ∧ ψ ) ↔ ( ∃ x φ ∧ ∃ y ψ )",
        s1,
        s2,
        ref="bitri",
        note="bitri exdistr, 19.41v",
    )
    return lb.build(res)


def prove_4exdistrv(sys: System) -> Proof:
    """4exdistrv: ∃ x ∃ z ∃ y ∃ w ( φ ∧ ψ ) ↔ ( ∃ x ∃ y φ ∧ ∃ z ∃ w ψ ).
    Existential quantifier distributes over conjunction for four variables
    (distinct variable version).  Variant of exdistrv with four quantifiers.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "4exdistrv")
    # exdistrv: ∃ y ∃ w ( φ ∧ ψ ) ↔ ( ∃ y φ ∧ ∃ w ψ )
    s1 = lb.ref(
        "s1",
        "∃ y ∃ w ( φ ∧ ψ ) ↔ ( ∃ y φ ∧ ∃ w ψ )",
        ref="exdistrv",
        note="exdistrv",
    )
    # 2exbii: add ∃ x ∃ z to both sides
    s2 = lb.ref(
        "s2",
        "∃ x ∃ z ∃ y ∃ w ( φ ∧ ψ ) ↔ ∃ x ∃ z ( ∃ y φ ∧ ∃ w ψ )",
        s1,
        ref="2exbii",
        note="2exbii exdistrv",
    )
    # exdistrv: distribute ∃ x ∃ z over the conjunction
    s3 = lb.ref(
        "s3",
        "∃ x ∃ z ( ∃ y φ ∧ ∃ w ψ ) ↔ ( ∃ x ∃ y φ ∧ ∃ z ∃ w ψ )",
        ref="exdistrv",
        note="exdistrv",
    )
    # bitri: chain s2 and s3
    res = lb.ref(
        "res",
        "∃ x ∃ z ∃ y ∃ w ( φ ∧ ψ ) ↔ ( ∃ x ∃ y φ ∧ ∃ z ∃ w ψ )",
        s2,
        s3,
        ref="bitri",
        note="bitri",
    )
    return lb.build(res)


def prove_eu6lem(sys: System) -> Proof:
    """eu6lem: ∃ y ∀ x ( φ ↔ x = y ) ↔ ( ∃ y ∀ x ( x = y → φ ) ∧ ∃ z ∀ x ( φ → x = z ) ).
    Lemma for eu6: alternate definition of the unique existential quantifier
    not using the at-most-one quantifier.
    (Contributed by NM, 12-Aug-1993.)
    """
    lb = ProofBuilder(sys, "eu6lem")
    # equequ2: y = z → ( x = y ↔ x = z )
    s_equ2 = lb.ref(
        "s_equ2",
        "y = z → ( x = y ↔ x = z )",
        ref="equequ2",
        note="equequ2",
    )
    # imbi2d: y = z → ( ( φ → x = y ) ↔ ( φ → x = z ) )
    s_imbi2d = lb.ref(
        "s_imbi2d",
        "y = z → ( ( φ → x = y ) ↔ ( φ → x = z ) )",
        s_equ2,
        ref="imbi2d",
        note="imbi2d equequ2",
    )
    # albidv: y = z → ( ∀ x ( φ → x = y ) ↔ ∀ x ( φ → x = z ) )
    s_albidv = lb.ref(
        "s_albidv",
        "y = z → ( ∀ x ( φ → x = y ) ↔ ∀ x ( φ → x = z ) )",
        s_imbi2d,
        ref="albidv",
        note="albidv imbi2d",
    )
    # anbi2d: y = z → ( ( ∀ x ( x = y → φ ) ∧ ∀ x ( φ → x = y ) ) ↔ ( ∀ x ( x = y → φ ) ∧ ∀ x ( φ → x = z ) ) )
    s_anbi2d = lb.ref(
        "s_anbi2d",
        "y = z → ( ( ∀ x ( x = y → φ ) ∧ ∀ x ( φ → x = y ) ) ↔ ( ∀ x ( x = y → φ ) ∧ ∀ x ( φ → x = z ) ) )",
        s_albidv,
        ref="anbi2d",
        note="anbi2d albidv",
    )
    # albiim: ∀ x ( φ ↔ x = y ) ↔ ( ∀ x ( φ → x = y ) ∧ ∀ x ( x = y → φ ) )
    s_albiim = lb.ref(
        "s_albiim",
        "∀ x ( φ ↔ x = y ) ↔ ( ∀ x ( φ → x = y ) ∧ ∀ x ( x = y → φ ) )",
        ref="albiim",
        note="albiim",
    )
    # biancomi: ∀ x ( φ ↔ x = y ) ↔ ( ∀ x ( x = y → φ ) ∧ ∀ x ( φ → x = y ) )
    s_biancomi = lb.ref(
        "s_biancomi",
        "∀ x ( φ ↔ x = y ) ↔ ( ∀ x ( x = y → φ ) ∧ ∀ x ( φ → x = y ) )",
        s_albiim,
        ref="biancomi",
        note="biancomi albiim",
    )
    # bitrid: y = z → ( ∀ x ( φ ↔ x = y ) ↔ ( ∀ x ( x = y → φ ) ∧ ∀ x ( φ → x = z ) ) )
    s_bitrid = lb.ref(
        "s_bitrid",
        "y = z → ( ∀ x ( φ ↔ x = y ) ↔ ( ∀ x ( x = y → φ ) ∧ ∀ x ( φ → x = z ) ) )",
        s_biancomi,
        s_anbi2d,
        ref="bitrid",
        note="bitrid biancomi, anbi2d",
    )
    # pm5.32ri: ( ∀ x ( φ ↔ x = y ) ∧ y = z ) ↔ ( ( ∀ x ( x = y → φ ) ∧ ∀ x ( φ → x = z ) ) ∧ y = z )
    s_pm5_32ri = lb.ref(
        "s_pm5_32ri",
        "( ∀ x ( φ ↔ x = y ) ∧ y = z ) ↔ ( ( ∀ x ( x = y → φ ) ∧ ∀ x ( φ → x = z ) ) ∧ y = z )",
        s_bitrid,
        ref="pm5.32ri",
        note="pm5.32ri bitrid",
    )
    # alsyl: ( ∀ x ( x = y → φ ) ∧ ∀ x ( φ → x = z ) ) → ∀ x ( x = y → x = z )
    s_alsyl = lb.ref(
        "s_alsyl",
        "( ∀ x ( x = y → φ ) ∧ ∀ x ( φ → x = z ) ) → ∀ x ( x = y → x = z )",
        ref="alsyl",
        note="alsyl",
    )
    # equvelv: ∀ x ( x = y → x = z ) ↔ y = z
    s_equvelv = lb.ref(
        "s_equvelv",
        "∀ x ( x = y → x = z ) ↔ y = z",
        ref="equvelv",
        note="equvelv",
    )
    # sylib: ( ∀ x ( x = y → φ ) ∧ ∀ x ( φ → x = z ) ) → y = z
    s_sylib = lb.ref(
        "s_sylib",
        "( ∀ x ( x = y → φ ) ∧ ∀ x ( φ → x = z ) ) → y = z",
        s_alsyl,
        s_equvelv,
        ref="sylib",
        note="sylib alsyl, equvelv",
    )
    # pm4.71i: ( ∀ x ( x = y → φ ) ∧ ∀ x ( φ → x = z ) ) ↔ ( ( ∀ x ( x = y → φ ) ∧ ∀ x ( φ → x = z ) ) ∧ y = z )
    s_pm4_71i = lb.ref(
        "s_pm4_71i",
        "( ∀ x ( x = y → φ ) ∧ ∀ x ( φ → x = z ) ) ↔ ( ( ∀ x ( x = y → φ ) ∧ ∀ x ( φ → x = z ) ) ∧ y = z )",
        s_sylib,
        ref="pm4.71i",
        note="pm4.71i sylib",
    )
    # bitr4i: ( ∀ x ( x = y → φ ) ∧ ∀ x ( φ → x = z ) ) ↔ ( ∀ x ( φ ↔ x = y ) ∧ y = z )
    s_bitr4i = lb.ref(
        "s_bitr4i",
        "( ∀ x ( x = y → φ ) ∧ ∀ x ( φ → x = z ) ) ↔ ( ∀ x ( φ ↔ x = y ) ∧ y = z )",
        s_pm4_71i,
        s_pm5_32ri,
        ref="bitr4i",
        note="bitr4i pm4.71i, pm5.32ri",
    )
    # exbii: ∃ z ( ∀ x ( x = y → φ ) ∧ ∀ x ( φ → x = z ) ) ↔ ∃ z ( ∀ x ( φ ↔ x = y ) ∧ y = z )
    s_exbii = lb.ref(
        "s_exbii",
        "∃ z ( ∀ x ( x = y → φ ) ∧ ∀ x ( φ → x = z ) ) ↔ ∃ z ( ∀ x ( φ ↔ x = y ) ∧ y = z )",
        s_bitr4i,
        ref="exbii",
        note="exbii bitr4i",
    )
    # ax6evr: ∃ z y = z
    s_ax6evr = lb.ref(
        "s_ax6evr",
        "∃ z y = z",
        ref="ax6evr",
        note="ax6evr",
    )
    # biantru: ∀ x ( φ ↔ x = y ) ↔ ( ∀ x ( φ ↔ x = y ) ∧ ∃ z y = z )
    s_biantru = lb.ref(
        "s_biantru",
        "∀ x ( φ ↔ x = y ) ↔ ( ∀ x ( φ ↔ x = y ) ∧ ∃ z y = z )",
        s_ax6evr,
        ref="biantru",
        note="biantru ax6evr",
    )
    # 19.42v: ∃ z ( ∀ x ( φ ↔ x = y ) ∧ y = z ) ↔ ( ∀ x ( φ ↔ x = y ) ∧ ∃ z y = z )
    s_19_42v = lb.ref(
        "s_19_42v",
        "∃ z ( ∀ x ( φ ↔ x = y ) ∧ y = z ) ↔ ( ∀ x ( φ ↔ x = y ) ∧ ∃ z y = z )",
        ref="19.42v",
        note="19.42v",
    )
    # 3bitr4ri: ∀ x ( φ ↔ x = y ) ↔ ∃ z ( ∀ x ( x = y → φ ) ∧ ∀ x ( φ → x = z ) )
    s_3bitr4ri = lb.ref(
        "s_3bitr4ri",
        "∀ x ( φ ↔ x = y ) ↔ ∃ z ( ∀ x ( x = y → φ ) ∧ ∀ x ( φ → x = z ) )",
        s_19_42v,
        s_exbii,
        s_biantru,
        ref="3bitr4ri",
        note="3bitr4ri 19.42v, exbii, biantru",
    )
    # exbii: ∃ y ∀ x ( φ ↔ x = y ) ↔ ∃ y ∃ z ( ∀ x ( x = y → φ ) ∧ ∀ x ( φ → x = z ) )
    s_exbii2 = lb.ref(
        "s_exbii2",
        "∃ y ∀ x ( φ ↔ x = y ) ↔ ∃ y ∃ z ( ∀ x ( x = y → φ ) ∧ ∀ x ( φ → x = z ) )",
        s_3bitr4ri,
        ref="exbii",
        note="exbii 3bitr4ri",
    )
    # exdistrv: ∃ y ∃ z ( ∀ x ( x = y → φ ) ∧ ∀ x ( φ → x = z ) ) ↔ ( ∃ y ∀ x ( x = y → φ ) ∧ ∃ z ∀ x ( φ → x = z ) )
    s_exdistrv = lb.ref(
        "s_exdistrv",
        "∃ y ∃ z ( ∀ x ( x = y → φ ) ∧ ∀ x ( φ → x = z ) ) ↔ ( ∃ y ∀ x ( x = y → φ ) ∧ ∃ z ∀ x ( φ → x = z ) )",
        ref="exdistrv",
        note="exdistrv",
    )
    # bitri: the conclusion
    res = lb.ref(
        "res",
        "∃ y ∀ x ( φ ↔ x = y ) ↔ ( ∃ y ∀ x ( x = y → φ ) ∧ ∃ z ∀ x ( φ → x = z ) )",
        s_exbii2,
        s_exdistrv,
        ref="bitri",
        note="bitri exbii, exdistrv",
    )
    return lb.build(res)


def prove_eu6im(sys: System) -> Proof:
    """eu6im: ∃ y ∀ x ( φ ↔ x = y ) → ∃! x φ.
    From exsbim, anim1i, eu6lem, eu3v via 3imtr4i.
    (Contributed by NM, 12-Aug-1993.)
    """
    lb = ProofBuilder(sys, "eu6im")
    # exsbim: ∃ y ∀ x ( x = y → φ ) → ∃ x φ
    s_exsbim = lb.ref(
        "s_exsbim",
        "∃ y ∀ x ( x = y → φ ) → ∃ x φ",
        ref="exsbim",
        note="exsbim",
    )
    # anim1i: conjoin ∃ z ∀ x ( φ → x = z ) to both sides
    s_anim1i = lb.ref(
        "s_anim1i",
        "( ∃ y ∀ x ( x = y → φ ) ∧ ∃ z ∀ x ( φ → x = z ) ) → ( ∃ x φ ∧ ∃ z ∀ x ( φ → x = z ) )",
        s_exsbim,
        ref="anim1i",
        note="anim1i exsbim",
    )
    # eu6lem: ∃ y ∀ x ( φ ↔ x = y ) ↔ ( ∃ y ∀ x ( x = y → φ ) ∧ ∃ z ∀ x ( φ → x = z ) )
    s_eu6lem = lb.ref(
        "s_eu6lem",
        "∃ y ∀ x ( φ ↔ x = y ) ↔ ( ∃ y ∀ x ( x = y → φ ) ∧ ∃ z ∀ x ( φ → x = z ) )",
        ref="eu6lem",
        note="eu6lem",
    )
    # eu3v with z: ∃! x φ ↔ ( ∃ x φ ∧ ∃ z ∀ x ( φ → x = z ) )
    s_eu3v = lb.ref(
        "s_eu3v",
        "∃! x φ ↔ ( ∃ x φ ∧ ∃ z ∀ x ( φ → x = z ) )",
        ref="eu3v",
        note="eu3v",
    )
    # 3imtr4i: combine everything
    res = lb.ref(
        "res",
        "∃ y ∀ x ( φ ↔ x = y ) → ∃! x φ",
        s_anim1i,
        s_eu6lem,
        s_eu3v,
        ref="3imtr4i",
        note="3imtr4i anim1i, eu6lem, eu3v",
    )
    return lb.build(res)


def prove_eu6(sys: System) -> Proof:
    """eu6: ∃! x φ ↔ ∃ y ∀ x ( φ ↔ x = y ).

    Alternate definition of the unique existential quantifier not using
    the at-most-one quantifier.
    (Contributed by NM, 12-Aug-1993.)
    """
    lb = ProofBuilder(sys, "eu6")

    # dfmoeu: ( ∃ x φ → ∃ y ∀ x ( φ ↔ x = y ) ) ↔ ∃ y ∀ x ( φ → x = y )
    s1 = lb.ref(
        "s1",
        "( ∃ x φ → ∃ y ∀ x ( φ ↔ x = y ) ) ↔ ∃ y ∀ x ( φ → x = y )",
        ref="dfmoeu",
        note="dfmoeu",
    )
    # anbi2i s1: ( ∃ x φ ∧ ( ∃ x φ → ∃ y ∀ x ( φ ↔ x = y ) ) ) ↔ ( ∃ x φ ∧ ∃ y ∀ x ( φ → x = y ) )
    s2 = lb.ref(
        "s2",
        "( ∃ x φ ∧ ( ∃ x φ → ∃ y ∀ x ( φ ↔ x = y ) ) ) ↔ ( ∃ x φ ∧ ∃ y ∀ x ( φ → x = y ) )",
        s1,
        ref="anbi2i",
        note="anbi2i dfmoeu",
    )
    # abai: ( ∃ x φ ∧ ∃ y ∀ x ( φ ↔ x = y ) ) ↔ ( ∃ x φ ∧ ( ∃ x φ → ∃ y ∀ x ( φ ↔ x = y ) ) )
    s3 = lb.ref(
        "s3",
        "( ∃ x φ ∧ ∃ y ∀ x ( φ ↔ x = y ) ) ↔ ( ∃ x φ ∧ ( ∃ x φ → ∃ y ∀ x ( φ ↔ x = y ) ) )",
        ref="abai",
        note="abai",
    )
    # eu3v: ∃! x φ ↔ ( ∃ x φ ∧ ∃ y ∀ x ( φ → x = y ) )
    s4 = lb.ref(
        "s4",
        "∃! x φ ↔ ( ∃ x φ ∧ ∃ y ∀ x ( φ → x = y ) )",
        ref="eu3v",
        note="eu3v",
    )
    # 3bitr4ri: ∃! x φ ↔ ( ∃ x φ ∧ ∃ y ∀ x ( φ ↔ x = y ) )
    s5 = lb.ref(
        "s5",
        "∃! x φ ↔ ( ∃ x φ ∧ ∃ y ∀ x ( φ ↔ x = y ) )",
        s2,
        s3,
        s4,
        ref="3bitr4ri",
        note="3bitr4ri anbi2i, abai, eu3v",
    )
    # abai: ( ∃ y ∀ x ( φ ↔ x = y ) ∧ ∃ x φ ) ↔ ( ∃ y ∀ x ( φ ↔ x = y ) ∧ ( ∃ y ∀ x ( φ ↔ x = y ) → ∃ x φ ) )
    s6 = lb.ref(
        "s6",
        "( ∃ y ∀ x ( φ ↔ x = y ) ∧ ∃ x φ ) ↔ ( ∃ y ∀ x ( φ ↔ x = y ) ∧ ( ∃ y ∀ x ( φ ↔ x = y ) → ∃ x φ ) )",
        ref="abai",
        note="abai",
    )
    # ancom: ( ∃ x φ ∧ ∃ y ∀ x ( φ ↔ x = y ) ) ↔ ( ∃ y ∀ x ( φ ↔ x = y ) ∧ ∃ x φ )
    s7 = lb.ref(
        "s7",
        "( ∃ x φ ∧ ∃ y ∀ x ( φ ↔ x = y ) ) ↔ ( ∃ y ∀ x ( φ ↔ x = y ) ∧ ∃ x φ )",
        ref="ancom",
        note="ancom",
    )
    # biimpr: ( φ ↔ x = y ) → ( x = y → φ )
    s8 = lb.ref(
        "s8",
        "( φ ↔ x = y ) → ( x = y → φ )",
        ref="biimpr",
        note="biimpr",
    )
    # alimi s8: ∀ x ( φ ↔ x = y ) → ∀ x ( x = y → φ )
    s9 = lb.ref(
        "s9",
        "∀ x ( φ ↔ x = y ) → ∀ x ( x = y → φ )",
        s8,
        ref="alimi",
        note="alimi biimpr",
    )
    # eximi s9: ∃ y ∀ x ( φ ↔ x = y ) → ∃ y ∀ x ( x = y → φ )
    s10 = lb.ref(
        "s10",
        "∃ y ∀ x ( φ ↔ x = y ) → ∃ y ∀ x ( x = y → φ )",
        s9,
        ref="eximi",
        note="eximi alimi",
    )
    # exsbim: ∃ y ∀ x ( x = y → φ ) → ∃ x φ
    s11 = lb.ref(
        "s11",
        "∃ y ∀ x ( x = y → φ ) → ∃ x φ",
        ref="exsbim",
        note="exsbim",
    )
    # syl: ∃ y ∀ x ( φ ↔ x = y ) → ∃ x φ
    s12 = lb.ref(
        "s12",
        "∃ y ∀ x ( φ ↔ x = y ) → ∃ x φ",
        s10,
        s11,
        ref="syl",
        note="syl eximi, exsbim",
    )
    # biantru s12: ∃ y ∀ x ( φ ↔ x = y ) ↔ ( ∃ y ∀ x ( φ ↔ x = y ) ∧ ( ∃ y ∀ x ( φ ↔ x = y ) → ∃ x φ ) )
    s13 = lb.ref(
        "s13",
        "∃ y ∀ x ( φ ↔ x = y ) ↔ ( ∃ y ∀ x ( φ ↔ x = y ) ∧ ( ∃ y ∀ x ( φ ↔ x = y ) → ∃ x φ ) )",
        s12,
        ref="biantru",
        note="biantru syl",
    )
    # 3bitr4i: ( ∃ x φ ∧ ∃ y ∀ x ( φ ↔ x = y ) ) ↔ ∃ y ∀ x ( φ ↔ x = y )
    s14 = lb.ref(
        "s14",
        "( ∃ x φ ∧ ∃ y ∀ x ( φ ↔ x = y ) ) ↔ ∃ y ∀ x ( φ ↔ x = y )",
        s6,
        s7,
        s13,
        ref="3bitr4i",
        note="3bitr4i abai, ancom, biantru",
    )
    # bitri: ∃! x φ ↔ ∃ y ∀ x ( φ ↔ x = y )
    res = lb.ref(
        "res",
        "∃! x φ ↔ ∃ y ∀ x ( φ ↔ x = y )",
        s5,
        s14,
        ref="bitri",
        note="bitri 3bitr4ri, 3bitr4i",
    )
    return lb.build(res)


def prove_euf(sys: System) -> Proof:
    """euf: ∃! x φ ↔ ∃ y ∀ x ( φ ↔ x = y ).

    Alternate definition of existential uniqueness not using the
    at-most-one quantifier.  Uses the F/ y ph hypothesis.
    (Contributed by NM, 12-Aug-1993.)
    """
    lb = ProofBuilder(sys, "euf")
    hyp = lb.hyp("euf.1", "Ⅎ y φ")

    # eu6 with z as the bound variable: ∃! x φ ↔ ∃ z ∀ x ( φ ↔ x = z )
    s1 = lb.ref(
        "s1",
        "∃! x φ ↔ ∃ z ∀ x ( φ ↔ x = z )",
        ref="eu6",
        note="eu6",
    )

    # nfv: Ⅎ y ( x = z )
    s_nfy_xz = lb.ref(
        "s_nfy_xz",
        "Ⅎ y ( x = z )",
        ref="nfv",
        note="nfv",
    )

    # nfbi euf.1, s_nfy_xz: Ⅎ y ( φ ↔ x = z )
    s_nfbi_y = lb.ref(
        "s_nfbi_y",
        "Ⅎ y ( φ ↔ x = z )",
        hyp,
        s_nfy_xz,
        ref="nfbi",
        note="nfbi euf.1, nfv",
    )

    # nfal s_nfbi_y: Ⅎ y ∀ x ( φ ↔ x = z )
    s_nfal_y = lb.ref(
        "s_nfal_y",
        "Ⅎ y ∀ x ( φ ↔ x = z )",
        s_nfbi_y,
        ref="nfal",
        note="nfal nfbi",
    )

    # nfv: Ⅎ z φ
    s_nfz_phi = lb.ref(
        "s_nfz_phi",
        "Ⅎ z φ",
        ref="nfv",
        note="nfv",
    )

    # nfv: Ⅎ z ( x = y )
    s_nfz_xy = lb.ref(
        "s_nfz_xy",
        "Ⅎ z ( x = y )",
        ref="nfv",
        note="nfv",
    )

    # nfbi s_nfz_phi, s_nfz_xy: Ⅎ z ( φ ↔ x = y )
    s_nfbi_z = lb.ref(
        "s_nfbi_z",
        "Ⅎ z ( φ ↔ x = y )",
        s_nfz_phi,
        s_nfz_xy,
        ref="nfbi",
        note="nfbi nfv, nfv",
    )

    # nfal s_nfbi_z: Ⅎ z ∀ x ( φ ↔ x = y )
    s_nfal_z = lb.ref(
        "s_nfal_z",
        "Ⅎ z ∀ x ( φ ↔ x = y )",
        s_nfbi_z,
        ref="nfal",
        note="nfal nfbi",
    )

    # equequ2: z = y → ( x = z ↔ x = y )
    s_equ2 = lb.ref(
        "s_equ2",
        "z = y → ( x = z ↔ x = y )",
        ref="equequ2",
        note="equequ2",
    )

    # bibi2d s_equ2: z = y → ( ( φ ↔ x = z ) ↔ ( φ ↔ x = y ) )
    s_bibi2d = lb.ref(
        "s_bibi2d",
        "z = y → ( ( φ ↔ x = z ) ↔ ( φ ↔ x = y ) )",
        s_equ2,
        ref="bibi2d",
        note="bibi2d equequ2",
    )

    # albidv s_bibi2d: z = y → ( ∀ x ( φ ↔ x = z ) ↔ ∀ x ( φ ↔ x = y ) )
    s_albidv = lb.ref(
        "s_albidv",
        "z = y → ( ∀ x ( φ ↔ x = z ) ↔ ∀ x ( φ ↔ x = y ) )",
        s_bibi2d,
        ref="albidv",
        note="albidv bibi2d",
    )

    # cbvexv1 s_nfal_y, s_nfal_z, s_albidv:
    #   ∃ z ∀ x ( φ ↔ x = z ) ↔ ∃ y ∀ x ( φ ↔ x = y )
    s_cbvexv1 = lb.ref(
        "s_cbvexv1",
        "∃ z ∀ x ( φ ↔ x = z ) ↔ ∃ y ∀ x ( φ ↔ x = y )",
        s_nfal_y,
        s_nfal_z,
        s_albidv,
        ref="cbvexv1",
        note="cbvexv1 nfal, nfal, albidv",
    )

    # bitri s1, s_cbvexv1: ∃! x φ ↔ ∃ y ∀ x ( φ ↔ x = y )
    res = lb.ref(
        "res",
        "∃! x φ ↔ ∃ y ∀ x ( φ ↔ x = y )",
        s1,
        s_cbvexv1,
        ref="bitri",
        note="bitri eu6, cbvexv1",
    )
    return lb.build(res)


def prove_sb8eulem(sys: System) -> Proof:
    """sb8eulem: ∃! x φ ↔ ∃! y [ y / x ] φ.

    Commutation of bound variable in unique existential quantifier via
    substitution.
    (Contributed by NM, 12-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sb8eulem")
    symbols = {
        info.local_name: symbol
        for symbol, info in sys.interner.symbol_table().items()
    }
    # Source active DVs, expanded from its three $d groups.
    for left, right in (
        ("w", "y"),
        ("w", "z"),
        ("y", "z"),
        ("ph", "z"),
        ("ph", "w"),
        ("w", "x"),
        ("x", "z"),
    ):
        lb.disjoint(symbols[left], symbols[right])
    hyp = lb.hyp("sb8eulem.nfsb", "Ⅎ y [ w x φ")
    s_sb8v = lb.ref(
        "s_sb8v",
        "∀ x ( φ ↔ x = z ) ↔ ∀ w [ w x ( φ ↔ x = z )",
        ref="sb8v",
        note="sb8v",
    )
    s_equsb3 = lb.ref(
        "s_equsb3",
        "( [ w x x = z ↔ w = z )",
        ref="equsb3",
        note="equsb3",
    )
    s_sblbis = lb.ref(
        "s_sblbis",
        "( [ w x ( φ ↔ x = z ) ↔ ( [ w x φ ↔ w = z ) )",
        s_equsb3,
        ref="sblbis",
        note="sblbis equsb3",
    )
    s_albii = lb.ref(
        "s_albii",
        "∀ w [ w x ( φ ↔ x = z ) ↔ ∀ w ( [ w x φ ↔ w = z )",
        s_sblbis,
        ref="albii",
        note="albii sblbis",
    )
    s_nfy = lb.ref("s_nfy", "Ⅎ y ( [ w x φ ↔ w = z )", hyp, lb.ref("nfyz", "Ⅎ y ( w = z )", ref="nfv"), ref="nfbi")
    s_nfw = lb.ref("s_nfw", "Ⅎ w ( [ y x φ ↔ y = z )", ref="nfv")
    s_sbequ = lb.ref("s_sbequ", "w = y → ( [ w x φ ↔ [ y x φ )", ref="sbequ")
    s_equequ1 = lb.ref("s_equequ1", "w = y → ( w = z ↔ y = z )", ref="equequ1")
    s_bibi12d = lb.ref(
        "s_bibi12d",
        "w = y → ( ( [ w x φ ↔ w = z ) ↔ ( [ y x φ ↔ y = z ) )",
        s_sbequ,
        s_equequ1,
        ref="bibi12d",
    )
    s_cbvalv1 = lb.ref(
        "s_cbvalv1",
        "∀ w ( [ w x φ ↔ w = z ) ↔ ∀ y ( [ y x φ ↔ y = z )",
        s_nfy,
        s_nfw,
        s_bibi12d,
        ref="cbvalv1",
    )
    s_3bitri = lb.ref(
        "s_3bitri",
        "∀ x ( φ ↔ x = z ) ↔ ∀ y ( [ y x φ ↔ y = z )",
        s_sb8v,
        s_albii,
        s_cbvalv1,
        ref="3bitri",
    )
    s_exbii = lb.ref(
        "s_exbii",
        "∃ z ∀ x ( φ ↔ x = z ) ↔ ∃ z ∀ y ( [ y x φ ↔ y = z )",
        s_3bitri,
        ref="exbii",
    )
    s_eu6_lhs = lb.ref("s_eu6_lhs", "∃! x φ ↔ ∃ z ∀ x ( φ ↔ x = z )", ref="eu6")
    s_eu6_rhs = lb.ref("s_eu6_rhs", "∃! y [ y x φ ↔ ∃ z ∀ y ( [ y x φ ↔ y = z )", ref="eu6")
    res = lb.ref(
        "res",
        "∃! x φ ↔ ∃! y [ y x φ",
        s_exbii,
        s_eu6_lhs,
        s_eu6_rhs,
        ref="3bitr4i",
        note="set.mm: sb8v equsb3 sblbis albii nfv nfbi sbequ eu6 equequ1 bibi12d cbvalv1 3bitri exbii 3bitr4i",
    )

    return lb.build(res)


def prove_sb8euv(sys: System) -> Proof:
    """sb8euv: ∃! x φ ↔ ∃! y [ y / x ] φ.

    Commutation of bound variable in unique existential quantifier with a
    not-free hypothesis.
    (Contributed by NM, 12-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sb8euv")
    hyp = lb.hyp("sb8euv.nf", "Ⅎ y φ")
    nfsb = lb.ref("nfsb", "Ⅎ y [ w x φ", hyp, ref="nfsbv", note="nfsbv sb8euv.nf")
    res = lb.ref(
        "res",
        "∃! x φ ↔ ∃! y [ y x φ",
        nfsb,
        ref="sb8eulem",
        note="sb8eulem",
    )
    return lb.build(res)


def prove_sb8eu(sys: System) -> Proof:
    """sb8eu: ∃! x φ ↔ ∃! y [ y / x ] φ.

    Commutation of bound variable in unique existential quantifier with a
    not-free hypothesis.
    (Contributed by NM, 12-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sb8eu")
    hyp = lb.hyp("sb8eu.1", "Ⅎ y φ")
    nfsb = lb.ref("nfsb", "Ⅎ y [ w x φ", hyp, ref="nfsb", note="nfsb sb8eu.1")
    res = lb.ref(
        "res",
        "∃! x φ ↔ ∃! y [ y x φ",
        nfsb,
        ref="sb8eulem",
        note="sb8eulem",
    )
    return lb.build(res)


def prove_sb8mo(sys: System) -> Proof:
    """sb8mo: ∃* x φ ↔ ∃* y [ y / x ] φ.

    Commutation of bound variable in at-most-one quantifier.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sb8mo")
    hyp = lb.hyp("sb8.1", "Ⅎ y φ")
    # sb8e: ∃ x φ ↔ ∃ y [ y x φ
    s_sb8e = lb.ref(
        "s_sb8e",
        "∃ x φ ↔ ∃ y [ y x φ",
        hyp,
        ref="sb8e",
        note="sb8e",
    )
    # sb8eu: ∃! x φ ↔ ∃! y [ y x φ
    s_sb8eu = lb.ref(
        "s_sb8eu",
        "∃! x φ ↔ ∃! y [ y x φ",
        hyp,
        ref="sb8eu",
        note="sb8eu",
    )
    # imbi12i: ( ∃ x φ → ∃! x φ ) ↔ ( ∃ y [ y x φ → ∃! y [ y x φ )
    s_imbi = lb.ref(
        "s_imbi",
        "( ∃ x φ → ∃! x φ ) ↔ ( ∃ y [ y x φ → ∃! y [ y x φ )",
        s_sb8e,
        s_sb8eu,
        ref="imbi12i",
        note="imbi12i",
    )
    # moeu (left): ∃* x φ ↔ ( ∃ x φ → ∃! x φ )
    s_moeu_l = lb.ref(
        "s_moeu_l",
        "∃* x φ ↔ ( ∃ x φ → ∃! x φ )",
        ref="moeu",
        note="moeu",
    )
    # moeu (right): ∃* y [ y x φ ↔ ( ∃ y [ y x φ → ∃! y [ y x φ )
    s_moeu_r = lb.ref(
        "s_moeu_r",
        "∃* y [ y x φ ↔ ( ∃ y [ y x φ → ∃! y [ y x φ )",
        ref="moeu",
        note="moeu",
    )
    # 3bitr4i: chain all biconditionals
    res = lb.ref(
        "res",
        "∃* x φ ↔ ∃* y [ y x φ",
        s_imbi,
        s_moeu_l,
        s_moeu_r,
        ref="3bitr4i",
        note="3bitr4i",
    )
    return lb.build(res)


def prove_19_41vvv(sys: System) -> Proof:
    """19.41vvv: ∃ x ∃ y ∃ z ( φ ∧ ψ ) ↔ ( ∃ x ∃ y ∃ z φ ∧ ψ ).
    Triple existential quantifier distributes over conjunction when the
    second conjunct does not contain the bound variables.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "19.41vvv")
    # 19.41vv (inner two quantifiers y, z):
    # ∃ y ∃ z ( φ ∧ ψ ) ↔ ( ∃ y ∃ z φ ∧ ψ )
    s_19_41vv = lb.ref(
        "s_19_41vv",
        "∃ y ∃ z ( φ ∧ ψ ) ↔ ( ∃ y ∃ z φ ∧ ψ )",
        ref="19.41vv",
        note="19.41vv",
    )
    # exbii: add ∃ x to both sides
    s_exbii = lb.ref(
        "s_exbii",
        "∃ x ∃ y ∃ z ( φ ∧ ψ ) ↔ ∃ x ( ∃ y ∃ z φ ∧ ψ )",
        s_19_41vv,
        ref="exbii",
        note="exbii 19.41vv",
    )
    # 19.41v (outermost quantifier x, with ∃ y ∃ z φ as the first conjunct):
    # ∃ x ( ∃ y ∃ z φ ∧ ψ ) ↔ ( ∃ x ∃ y ∃ z φ ∧ ψ )
    s_19_41v = lb.ref(
        "s_19_41v",
        "∃ x ( ∃ y ∃ z φ ∧ ψ ) ↔ ( ∃ x ∃ y ∃ z φ ∧ ψ )",
        ref="19.41v",
        note="19.41v",
    )
    # bitri: chain both directions
    res = lb.ref(
        "res",
        "∃ x ∃ y ∃ z ( φ ∧ ψ ) ↔ ( ∃ x ∃ y ∃ z φ ∧ ψ )",
        s_exbii,
        s_19_41v,
        ref="bitri",
        note="bitri",
    )
    return lb.build(res)


def prove_19_41vvvv(sys: System) -> Proof:
    """19.41vvvv: ∃ w ∃ x ∃ y ∃ z ( φ ∧ ψ ) ↔ ( ∃ w ∃ x ∃ y ∃ z φ ∧ ψ ).
    Quadruple existential quantifier distributes over conjunction when the
    second conjunct does not contain the bound variables.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "19.41vvvv")
    # 19.41vvv (inner three quantifiers x, y, z):
    # ∃ x ∃ y ∃ z ( φ ∧ ψ ) ↔ ( ∃ x ∃ y ∃ z φ ∧ ψ )
    s_19_41vvv = lb.ref(
        "s_19_41vvv",
        "∃ x ∃ y ∃ z ( φ ∧ ψ ) ↔ ( ∃ x ∃ y ∃ z φ ∧ ψ )",
        ref="19.41vvv",
        note="19.41vvv",
    )
    # exbii: add ∃ w to both sides
    s_exbii = lb.ref(
        "s_exbii",
        "∃ w ∃ x ∃ y ∃ z ( φ ∧ ψ ) ↔ ∃ w ( ∃ x ∃ y ∃ z φ ∧ ψ )",
        s_19_41vvv,
        ref="exbii",
        note="exbii 19.41vvv",
    )
    # 19.41v (outermost quantifier w, with ∃ x ∃ y ∃ z φ as the first conjunct):
    # ∃ w ( ∃ x ∃ y ∃ z φ ∧ ψ ) ↔ ( ∃ w ∃ x ∃ y ∃ z φ ∧ ψ )
    s_19_41v = lb.ref(
        "s_19_41v",
        "∃ w ( ∃ x ∃ y ∃ z φ ∧ ψ ) ↔ ( ∃ w ∃ x ∃ y ∃ z φ ∧ ψ )",
        ref="19.41v",
        note="19.41v",
    )
    # bitri: chain both directions
    res = lb.ref(
        "res",
        "∃ w ∃ x ∃ y ∃ z ( φ ∧ ψ ) ↔ ( ∃ w ∃ x ∃ y ∃ z φ ∧ ψ )",
        s_exbii,
        s_19_41v,
        ref="bitri",
        note="bitri",
    )
    return lb.build(res)


def prove_axc11r(sys: System) -> Proof:
    """axc11r: ∀ y y = x → ( ∀ x φ → ∀ y φ ).
    Reverse of ax-c11.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "axc11r")
    # ax-12 (y, x): y = x → ( ∀ x φ → ∀ y ( y = x → φ ) )
    s1 = lb.ref(
        "s1",
        "y = x → ( ∀ x φ → ∀ y ( y = x → φ ) )",
        ref="ax-12",
        note="ax-12",
    )
    # sps s1: ∀ y y = x → ( ∀ x φ → ∀ y ( y = x → φ ) )
    s2 = lb.ref(
        "s2",
        "∀ y y = x → ( ∀ x φ → ∀ y ( y = x → φ ) )",
        s1,
        ref="sps",
        note="sps ax-12",
    )
    # pm2.27: y = x → ( ( y = x → φ ) → φ )
    s3 = lb.ref(
        "s3",
        "y = x → ( ( y = x → φ ) → φ )",
        ref="pm2.27",
        note="pm2.27",
    )
    # al2imi s3: ∀ y y = x → ( ∀ y ( y = x → φ ) → ∀ y φ )
    s4 = lb.ref(
        "s4",
        "∀ y y = x → ( ∀ y ( y = x → φ ) → ∀ y φ )",
        s3,
        ref="al2imi",
        note="al2imi pm2.27",
    )
    # syld s2, s4: ∀ y y = x → ( ∀ x φ → ∀ y φ )
    res = lb.ref(
        "res",
        "∀ y y = x → ( ∀ x φ → ∀ y φ )",
        s2,
        s4,
        ref="syld",
        note="syld sps, al2imi",
    )
    return lb.build(res)


def prove_axc11(sys: System) -> Proof:
    """axc11: ∀ x x = y → ( ∀ x φ → ∀ y φ ).
    From axc11r via aecoms (swapping bound variables).
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "axc11")
    # axc11r: ∀ y y = x → (∀ x φ → ∀ y φ)
    s1 = lb.ref(
        "s1",
        "∀ y y = x → (∀ x φ → ∀ y φ)",
        ref="axc11r",
        note="axc11r",
    )
    # aecoms: from ∀ y y = x → (∀ x φ → ∀ y φ) derive ∀ x x = y → (∀ x φ → ∀ y φ)
    res = lb.ref(
        "res",
        "∀ x x = y → (∀ x φ → ∀ y φ)",
        s1,
        ref="aecoms",
        note="aecoms axc11r",
    )
    return lb.build(res)


def prove_axc11n(sys: System) -> Proof:
    """axc11n: ∀ x x = y → ∀ y y = x.
    Special case of aev with z := y, t := y, u := x.
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "axc11n")
    s1 = lb.ref("s1", "¬ ∀ y y = x → ( x = z → ∀ y x = z )", ref="dveeq1")
    s2 = lb.ref("s2", "x = z → ( ¬ ∀ y y = x → ∀ y x = z )", s1, ref="com12")
    s3 = lb.ref(
        "s3", "∀ x x = y → ( ∀ y x = z → ∀ x x = z )", ref="axc11r"
    )
    s4 = lb.ref("s4", "∀ x x = z → ∀ y y = x", ref="aev")
    s5 = lb.ref(
        "s5", "∀ x x = y → ( ∀ y x = z → ∀ y y = x )", s3, s4, ref="syl6"
    )
    s6 = lb.ref(
        "s6",
        "x = z → ( ∀ x x = y → ( ¬ ∀ y y = x → ∀ y y = x ) )",
        s2,
        s5,
        ref="syl9",
    )
    s7 = lb.ref("s7", "∃ z x = z", ref="ax6evr")
    s8 = lb.ref(
        "s8",
        "∀ x x = y → ( ¬ ∀ y y = x → ∀ y y = x )",
        s6,
        s7,
        ref="exlimiiv",
    )
    res = lb.ref("res", "∀ x x = y → ∀ y y = x", s8, ref="pm2.18d")
    return lb.build(res)


def prove_aecom(sys: System) -> Proof:
    """aecom: ∀ x x = y ↔ ∀ y y = x.
    Commutative law for equality with bound variables.
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "aecom")
    # axc11n: ∀ x x = y → ∀ y y = x
    s1 = lb.ref(
        "s1",
        "∀ x x = y → ∀ y y = x",
        ref="axc11n",
        note="axc11n",
    )
    # axc11n with x,y swapped: ∀ y y = x → ∀ x x = y
    s2 = lb.ref(
        "s2",
        "∀ y y = x → ∀ x x = y",
        ref="axc11n",
        note="axc11n",
    )
    # impbii: combine both directions
    res = lb.ref(
        "res",
        "∀ x x = y ↔ ∀ y y = x",
        s1,
        s2,
        ref="impbii",
        note="impbii",
    )
    return lb.build(res)


def prove_aecoms(sys: System) -> Proof:
    """aecoms: ∀ y y = x → φ.
    Inference form of aecom.  Given ∀ x x = y → φ, derive ∀ y y = x → φ
    via sylbir (which swaps the biconditional direction).
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "aecoms")
    h1 = lb.hyp("aecoms.1", "∀ x x = y → φ")
    # aecom: ∀ x x = y ↔ ∀ y y = x
    s1 = lb.ref(
        "s1",
        "∀ x x = y ↔ ∀ y y = x",
        ref="aecom",
        note="aecom",
    )
    # sylbir: (ψ ↔ φ), (ψ → χ)  ⊢  (φ → χ)
    # where ψ = ∀ x x = y, φ = ∀ y y = x, χ = φ
    res = lb.ref(
        "res",
        "∀ y y = x → φ",
        s1,
        h1,
        ref="sylbir",
        note="sylbir aecom, aecoms.1",
    )
    return lb.build(res)


def prove_naecoms(sys: System) -> Proof:
    """naecoms: ¬ ∀ y y = x → φ.
    Inference form of aecom with negation.  Given ¬ ∀ x x = y → φ,
    derive ¬ ∀ y y = x → φ via sylnbir.
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "naecoms")
    h1 = lb.hyp("naecoms.1", "¬ ∀ x x = y → φ")
    # aecom: ∀ x x = y ↔ ∀ y y = x
    s1 = lb.ref(
        "s1",
        "∀ x x = y ↔ ∀ y y = x",
        ref="aecom",
        note="aecom",
    )
    # sylnbir: (ψ ↔ φ), (¬ ψ → χ)  ⊢  (¬ φ → χ)
    # where ψ = ∀ x x = y, φ = ∀ y y = x, χ = φ
    res = lb.ref(
        "res",
        "¬ ∀ y y = x → φ",
        s1,
        h1,
        ref="sylnbir",
        note="sylnbir aecom, naecoms.1",
    )
    return lb.build(res)


def prove_19_42vvv(sys: System) -> Proof:
    """19.42vvv: ∃ x ∃ y ∃ z ( φ ∧ ψ ) ↔ ( φ ∧ ∃ x ∃ y ∃ z ψ ).
    Triple existential quantifier distributes over conjunction when the
    first conjunct does not contain the bound variables.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "19.42vvv")
    # exdistr2: ∃ x ∃ y ∃ z ( φ ∧ ψ ) ↔ ∃ x ( φ ∧ ∃ y ∃ z ψ )
    s_exdistr2 = lb.ref(
        "s_exdistr2",
        "∃ x ∃ y ∃ z ( φ ∧ ψ ) ↔ ∃ x ( φ ∧ ∃ y ∃ z ψ )",
        ref="exdistr2",
        note="exdistr2",
    )
    # 19.42v: ∃ x ( φ ∧ ∃ y ∃ z ψ ) ↔ ( φ ∧ ∃ x ∃ y ∃ z ψ )
    s_19_42v = lb.ref(
        "s_19_42v",
        "∃ x ( φ ∧ ∃ y ∃ z ψ ) ↔ ( φ ∧ ∃ x ∃ y ∃ z ψ )",
        ref="19.42v",
        note="19.42v",
    )
    # bitri: chain both directions
    res = lb.ref(
        "res",
        "∃ x ∃ y ∃ z ( φ ∧ ψ ) ↔ ( φ ∧ ∃ x ∃ y ∃ z ψ )",
        s_exdistr2,
        s_19_42v,
        ref="bitri",
        note="bitri",
    )
    return lb.build(res)


def prove_3exdistr(sys: System) -> Proof:
    """3exdistr: ∃ x ∃ y ∃ z ( φ ∧ ψ ∧ χ ) ↔ ∃ x ( φ ∧ ∃ y ( ψ ∧ ∃ z χ ) ).
    Existential quantifier distributes over conjunction (three variables,
    three conjuncts).
    """
    lb = ProofBuilder(sys, "3exdistr")
    # 3anass: ( φ ∧ ψ ∧ χ ) ↔ ( φ ∧ ( ψ ∧ χ ) )
    s1 = lb.ref(
        "s1",
        "( φ ∧ ψ ∧ χ ) ↔ ( φ ∧ ( ψ ∧ χ ) )",
        ref="3anass",
        note="3anass",
    )
    # 2exbii: add ∃ y ∃ z to both sides
    s2 = lb.ref(
        "s2",
        "∃ y ∃ z ( φ ∧ ψ ∧ χ ) ↔ ∃ y ∃ z ( φ ∧ ( ψ ∧ χ ) )",
        s1,
        ref="2exbii",
        note="2exbii 3anass",
    )
    # 19.42vv: ∃ y ∃ z ( φ ∧ ( ψ ∧ χ ) ) ↔ ( φ ∧ ∃ y ∃ z ( ψ ∧ χ ) )
    s3 = lb.ref(
        "s3",
        "∃ y ∃ z ( φ ∧ ( ψ ∧ χ ) ) ↔ ( φ ∧ ∃ y ∃ z ( ψ ∧ χ ) )",
        ref="19.42vv",
        note="19.42vv",
    )
    # exdistr: ∃ y ∃ z ( ψ ∧ χ ) ↔ ∃ y ( ψ ∧ ∃ z χ )
    s4 = lb.ref(
        "s4",
        "∃ y ∃ z ( ψ ∧ χ ) ↔ ∃ y ( ψ ∧ ∃ z χ )",
        ref="exdistr",
        note="exdistr",
    )
    # anbi2i: ( φ ∧ ∃ y ∃ z ( ψ ∧ χ ) ) ↔ ( φ ∧ ∃ y ( ψ ∧ ∃ z χ ) )
    s5 = lb.ref(
        "s5",
        "( φ ∧ ∃ y ∃ z ( ψ ∧ χ ) ) ↔ ( φ ∧ ∃ y ( ψ ∧ ∃ z χ ) )",
        s4,
        ref="anbi2i",
        note="anbi2i exdistr",
    )
    # 3bitri: chain s2, s3, s5
    s6 = lb.ref(
        "s6",
        "∃ y ∃ z ( φ ∧ ψ ∧ χ ) ↔ ( φ ∧ ∃ y ( ψ ∧ ∃ z χ ) )",
        s2,
        s3,
        s5,
        ref="3bitri",
        note="3bitri 2exbii, 19.42vv, anbi2i",
    )
    # exbii: add ∃ x to both sides
    res = lb.ref(
        "res",
        "∃ x ∃ y ∃ z ( φ ∧ ψ ∧ χ ) ↔ ∃ x ( φ ∧ ∃ y ( ψ ∧ ∃ z χ ) )",
        s6,
        ref="exbii",
        note="exbii 3bitri",
    )
    return lb.build(res)


def prove_4exdistr(sys: System) -> Proof:
    """4exdistr: ∃ x ∃ y ∃ z ∃ w ( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ) ↔ ∃ x ( φ ∧ ∃ y ( ψ ∧ ∃ z ( χ ∧ ∃ w θ ) ) ).
    Existential quantifier distributes over conjunction (four variables,
    four conjuncts).
    """
    lb = ProofBuilder(sys, "4exdistr")
    # 19.42v: ∃ w ( χ ∧ θ ) ↔ ( χ ∧ ∃ w θ )
    s1 = lb.ref(
        "s1",
        "∃ w ( χ ∧ θ ) ↔ ( χ ∧ ∃ w θ )",
        ref="19.42v",
        note="19.42v",
    )
    # anbi2i: ( ( φ ∧ ψ ) ∧ ∃ w ( χ ∧ θ ) ) ↔ ( ( φ ∧ ψ ) ∧ ( χ ∧ ∃ w θ ) )
    s2 = lb.ref(
        "s2",
        "( ( φ ∧ ψ ) ∧ ∃ w ( χ ∧ θ ) ) ↔ ( ( φ ∧ ψ ) ∧ ( χ ∧ ∃ w θ ) )",
        s1,
        ref="anbi2i",
        note="anbi2i 19.42v",
    )
    # 19.42v: ∃ w ( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ) ↔ ( ( φ ∧ ψ ) ∧ ∃ w ( χ ∧ θ ) )
    s3 = lb.ref(
        "s3",
        "∃ w ( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ) ↔ ( ( φ ∧ ψ ) ∧ ∃ w ( χ ∧ θ ) )",
        ref="19.42v",
        note="19.42v",
    )
    # df-3an: ( φ ∧ ψ ∧ ( χ ∧ ∃ w θ ) ) ↔ ( ( φ ∧ ψ ) ∧ ( χ ∧ ∃ w θ ) )
    s4 = lb.ref(
        "s4",
        "( φ ∧ ψ ∧ ( χ ∧ ∃ w θ ) ) ↔ ( ( φ ∧ ψ ) ∧ ( χ ∧ ∃ w θ ) )",
        ref="df-3an",
        note="df-3an",
    )
    # 3bitr4i: C ↔ D where A=((φ∧ψ)∧∃w(χ∧θ)), B=((φ∧ψ)∧(χ∧∃wθ)),
    #          C=∃w((φ∧ψ)∧(χ∧θ)), D=(φ∧ψ∧(χ∧∃wθ))
    s5 = lb.ref(
        "s5",
        "∃ w ( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ) ↔ ( φ ∧ ψ ∧ ( χ ∧ ∃ w θ ) )",
        s2,
        s3,
        s4,
        ref="3bitr4i",
        note="3bitr4i 19.42v, anbi2i, df-3an",
    )
    # 3exbii: add ∃ x ∃ y ∃ z to both sides
    s6 = lb.ref(
        "s6",
        "∃ x ∃ y ∃ z ∃ w ( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ) ↔ ∃ x ∃ y ∃ z ( φ ∧ ψ ∧ ( χ ∧ ∃ w θ ) )",
        s5,
        ref="3exbii",
        note="3exbii",
    )
    # 3exdistr: distribute the first three quantifiers
    s7 = lb.ref(
        "s7",
        "∃ x ∃ y ∃ z ( φ ∧ ψ ∧ ( χ ∧ ∃ w θ ) ) ↔ ∃ x ( φ ∧ ∃ y ( ψ ∧ ∃ z ( χ ∧ ∃ w θ ) ) )",
        ref="3exdistr",
        note="3exdistr",
    )
    # bitri: chain s6 and s7
    res = lb.ref(
        "res",
        "∃ x ∃ y ∃ z ∃ w ( ( φ ∧ ψ ) ∧ ( χ ∧ θ ) ) ↔ ∃ x ( φ ∧ ∃ y ( ψ ∧ ∃ z ( χ ∧ ∃ w θ ) ) )",
        s6,
        s7,
        ref="bitri",
        note="bitri",
    )
    return lb.build(res)


def prove_mobi(sys: System) -> Proof:
    """mobi: ∀ x ( φ ↔ ψ ) → ( ∃* x φ ↔ ∃* x ψ ).
    Formula-building rule for the at-most-one quantifier.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "mobi")
    # albiim: ∀ x ( φ ↔ ψ ) ↔ ( ∀ x ( φ → ψ ) ∧ ∀ x ( ψ → φ ) )
    s_albiim = lb.ref(
        "s_albiim",
        "∀ x ( φ ↔ ψ ) ↔ ( ∀ x ( φ → ψ ) ∧ ∀ x ( ψ → φ ) )",
        ref="albiim",
        note="albiim",
    )
    # moim: ∀ x ( φ → ψ ) → ( ∃* x ψ → ∃* x φ )
    s_moim1 = lb.ref(
        "s_moim1",
        "∀ x ( φ → ψ ) → ( ∃* x ψ → ∃* x φ )",
        ref="moim",
        note="moim",
    )
    # moim with φ, ψ swapped: ∀ x ( ψ → φ ) → ( ∃* x φ → ∃* x ψ )
    s_moim2 = lb.ref(
        "s_moim2",
        "∀ x ( ψ → φ ) → ( ∃* x φ → ∃* x ψ )",
        ref="moim",
        note="moim",
    )
    # impbid21d:
    # h1 (ps → (ch → th)): ∀ x ( ψ → φ ) → ( ∃* x φ → ∃* x ψ )
    # h2 (ph → (th → ch)): ∀ x ( φ → ψ ) → ( ∃* x ψ → ∃* x φ )
    # result: ( ∀ x ( φ → ψ ) ) → ( ( ∀ x ( ψ → φ ) ) → ( ∃* x φ ↔ ∃* x ψ ) )
    s_impbid21d = lb.ref(
        "s_impbid21d",
        "( ∀ x ( φ → ψ ) ) → ( ( ∀ x ( ψ → φ ) ) → ( ∃* x φ ↔ ∃* x ψ ) )",
        s_moim2,
        s_moim1,
        ref="impbid21d",
        note="impbid21d",
    )
    # imp: ( ( ∀ x ( φ → ψ ) ) ∧ ( ∀ x ( ψ → φ ) ) ) → ( ∃* x φ ↔ ∃* x ψ )
    s_imp = lb.ref(
        "s_imp",
        "( ∀ x ( φ → ψ ) ∧ ∀ x ( ψ → φ ) ) → ( ∃* x φ ↔ ∃* x ψ )",
        s_impbid21d,
        ref="imp",
        note="imp",
    )
    # sylbi:
    # h1: ∀ x ( φ ↔ ψ ) ↔ ( ∀ x ( φ → ψ ) ∧ ∀ x ( ψ → φ ) )
    # h2: ( ∀ x ( φ → ψ ) ∧ ∀ x ( ψ → φ ) ) → ( ∃* x φ ↔ ∃* x ψ )
    # conclusion: ∀ x ( φ ↔ ψ ) → ( ∃* x φ ↔ ∃* x ψ )
    res = lb.ref(
        "res",
        "∀ x ( φ ↔ ψ ) → ( ∃* x φ ↔ ∃* x ψ )",
        s_albiim,
        s_imp,
        ref="sylbi",
        note="sylbi albiim, imp",
    )
    return lb.build(res)


def prove_mobii(sys: System) -> Proof:
    """mobii: ∃* x ψ ↔ ∃* x χ.
    Inference form of mobi.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "mobii")
    hyp = lb.hyp("mobii.1", "ψ ↔ χ")
    # mobi: ∀ x (ψ ↔ χ) → (∃* x ψ ↔ ∃* x χ)
    s_mobi = lb.ref(
        "s_mobi",
        "∀ x (ψ ↔ χ) → (∃* x ψ ↔ ∃* x χ)",
        ref="mobi",
        note="mobi",
    )
    # mpg: from ∀ x (ψ ↔ χ) → (∃* x ψ ↔ ∃* x χ) and ψ ↔ χ, get ∃* x ψ ↔ ∃* x χ
    res = lb.ref(
        "res",
        "∃* x ψ ↔ ∃* x χ",
        s_mobi,
        hyp,
        ref="mpg",
        note="mpg mobi, mobii.1",
    )
    return lb.build(res)


def prove_mobid(sys: System) -> Proof:
    """mobid: φ → (∃* x ψ ↔ ∃* x χ).
    Deduction form of mobi.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "mobid")
    hyp1 = lb.hyp("mobid.1", "Ⅎ x φ")
    hyp2 = lb.hyp("mobid.2", "φ → (ψ ↔ χ)")
    # alrimi: Ⅎ x φ, φ → (ψ ↔ χ) ⊢ φ → ∀ x (ψ ↔ χ)
    s_alrimi = lb.ref(
        "s_alrimi",
        "φ → ∀ x (ψ ↔ χ)",
        hyp1,
        hyp2,
        ref="alrimi",
        note="alrimi mobid.1, mobid.2",
    )
    # mobi: ∀ x (ψ ↔ χ) → (∃* x ψ ↔ ∃* x χ)
    s_mobi = lb.ref(
        "s_mobi",
        "∀ x (ψ ↔ χ) → (∃* x ψ ↔ ∃* x χ)",
        ref="mobi",
        note="mobi",
    )
    # syl: (φ → ∀ x (ψ ↔ χ)), (∀ x (ψ ↔ χ) → (∃* x ψ ↔ ∃* x χ)) ⊢ φ → (∃* x ψ ↔ ∃* x χ)
    res = lb.ref(
        "res",
        "φ → (∃* x ψ ↔ ∃* x χ)",
        s_alrimi,
        s_mobi,
        ref="syl",
        note="syl alrimi, mobi",
    )
    return lb.build(res)


def prove_mobidv(sys: System) -> Proof:
    """mobidv: φ → (∃* x ψ ↔ ∃* x χ).
    Deduction form of mobi using distinct variable conditions.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "mobidv")
    hyp = lb.hyp("mobidv.1", "φ → (ψ ↔ χ)")
    # alrimiv: φ → (ψ ↔ χ) ⊢ φ → ∀ x (ψ ↔ χ)
    s_alrimiv = lb.ref(
        "s_alrimiv",
        "φ → ∀ x (ψ ↔ χ)",
        hyp,
        ref="alrimiv",
        note="alrimiv mobidv.1",
    )
    # mobi: ∀ x (ψ ↔ χ) → (∃* x ψ ↔ ∃* x χ)
    s_mobi = lb.ref(
        "s_mobi",
        "∀ x (ψ ↔ χ) → (∃* x ψ ↔ ∃* x χ)",
        ref="mobi",
        note="mobi",
    )
    # syl: (φ → ∀ x (ψ ↔ χ)), (∀ x (ψ ↔ χ) → (∃* x ψ ↔ ∃* x χ)) ⊢ φ → (∃* x ψ ↔ ∃* x χ)
    res = lb.ref(
        "res",
        "φ → (∃* x ψ ↔ ∃* x χ)",
        s_alrimiv,
        s_mobi,
        ref="syl",
        note="syl alrimiv, mobi",
    )
    return lb.build(res)


def prove_eubi(sys: System) -> Proof:
    """eubi: ∀ x ( φ ↔ ψ ) → ( ∃! x φ ↔ ∃! x ψ ).
    Formula-building rule for the unique existential quantifier.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "eubi")
    # exbi: ∀ x ( φ ↔ ψ ) → ( ∃ x φ ↔ ∃ x ψ )
    s_exbi = lb.ref(
        "s_exbi",
        "∀ x ( φ ↔ ψ ) → ( ∃ x φ ↔ ∃ x ψ )",
        ref="exbi",
        note="exbi",
    )
    # mobi: ∀ x ( φ ↔ ψ ) → ( ∃* x φ ↔ ∃* x ψ )
    s_mobi = lb.ref(
        "s_mobi",
        "∀ x ( φ ↔ ψ ) → ( ∃* x φ ↔ ∃* x ψ )",
        ref="mobi",
        note="mobi",
    )
    # anbi12d: ∀ x ( φ ↔ ψ ) → ( ( ∃ x φ ∧ ∃* x φ ) ↔ ( ∃ x ψ ∧ ∃* x ψ ) )
    s_anbi12d = lb.ref(
        "s_anbi12d",
        "∀ x ( φ ↔ ψ ) → ( ( ∃ x φ ∧ ∃* x φ ) ↔ ( ∃ x ψ ∧ ∃* x ψ ) )",
        s_exbi,
        s_mobi,
        ref="anbi12d",
        note="anbi12d exbi, mobi",
    )
    # df-eu: ∃! x φ ↔ ( ∃ x φ ∧ ∃* x φ )
    s_dfeu_phi = lb.ref(
        "s_dfeu_phi",
        "∃! x φ ↔ ( ∃ x φ ∧ ∃* x φ )",
        ref="df-eu",
        note="df-eu",
    )
    # df-eu: ∃! x ψ ↔ ( ∃ x ψ ∧ ∃* x ψ )
    s_dfeu_psi = lb.ref(
        "s_dfeu_psi",
        "∃! x ψ ↔ ( ∃ x ψ ∧ ∃* x ψ )",
        ref="df-eu",
        note="df-eu",
    )
    # 3bitr4g: ∀ x ( φ ↔ ψ ) → ( ∃! x φ ↔ ∃! x ψ )
    res = lb.ref(
        "res",
        "∀ x ( φ ↔ ψ ) → ( ∃! x φ ↔ ∃! x ψ )",
        s_anbi12d,
        s_dfeu_phi,
        s_dfeu_psi,
        ref="3bitr4g",
        note="3bitr4g anbi12d, df-eu, df-eu",
    )
    return lb.build(res)


def prove_eubii(sys: System) -> Proof:
    """eubii: ( ∃! x φ ↔ ∃! x ψ ).
    Inference form of eubi.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "eubii")
    h1 = lb.hyp("eubii.1", "( φ ↔ ψ )")
    # eubi: ∀ x ( φ ↔ ψ ) → ( ∃! x φ ↔ ∃! x ψ )
    s_eubi = lb.ref(
        "s_eubi",
        "∀ x ( φ ↔ ψ ) → ( ∃! x φ ↔ ∃! x ψ )",
        ref="eubi",
        note="eubi",
    )
    # mpg: from (∀ x ... → ...) and ( φ ↔ ψ ), get ( ∃! x φ ↔ ∃! x ψ )
    res = lb.ref(
        "res",
        "( ∃! x φ ↔ ∃! x ψ )",
        s_eubi,
        h1,
        ref="mpg",
        note="mpg eubi, eubii.1",
    )
    return lb.build(res)


def prove_eubid(sys: System) -> Proof:
    """eubid: φ → (∃! x ψ ↔ ∃! x χ).
    Deduction form of eubi.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "eubid")
    h1 = lb.hyp("eubid.1", "Ⅎ x φ")
    h2 = lb.hyp("eubid.2", "φ → (ψ ↔ χ)")
    # alrimi: Ⅎ x φ, φ → (ψ ↔ χ) ⊢ φ → ∀ x (ψ ↔ χ)
    s_alrimi = lb.ref(
        "s_alrimi",
        "φ → ∀ x (ψ ↔ χ)",
        h1,
        h2,
        ref="alrimi",
        note="alrimi eubid.1, eubid.2",
    )
    # eubi: ∀ x (ψ ↔ χ) → (∃! x ψ ↔ ∃! x χ)
    s_eubi = lb.ref(
        "s_eubi",
        "∀ x (ψ ↔ χ) → (∃! x ψ ↔ ∃! x χ)",
        ref="eubi",
        note="eubi",
    )
    # syl: (φ → ∀ x (ψ ↔ χ)), (∀ x (ψ ↔ χ) → (∃! x ψ ↔ ∃! x χ)) ⊢ φ → (∃! x ψ ↔ ∃! x χ)
    res = lb.ref(
        "res",
        "φ → (∃! x ψ ↔ ∃! x χ)",
        s_alrimi,
        s_eubi,
        ref="syl",
        note="syl alrimi, eubi",
    )
    return lb.build(res)


def prove_eubidv(sys: System) -> Proof:
    """eubidv: φ → (∃! x ψ ↔ ∃! x χ).
    Deduction form of eubi using distinct variable conditions.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "eubidv")
    hyp = lb.hyp("eubidv.1", "φ → (ψ ↔ χ)")
    # alrimiv: φ → (ψ ↔ χ) ⊢ φ → ∀ x (ψ ↔ χ)
    s_alrimiv = lb.ref(
        "s_alrimiv",
        "φ → ∀ x (ψ ↔ χ)",
        hyp,
        ref="alrimiv",
        note="alrimiv eubidv.1",
    )
    # eubi: ∀ x (ψ ↔ χ) → (∃! x ψ ↔ ∃! x χ)
    s_eubi = lb.ref(
        "s_eubi",
        "∀ x (ψ ↔ χ) → (∃! x ψ ↔ ∃! x χ)",
        ref="eubi",
        note="eubi",
    )
    # syl: (φ → ∀ x (ψ ↔ χ)), (∀ x (ψ ↔ χ) → (∃! x ψ ↔ ∃! x χ)) ⊢ φ → (∃! x ψ ↔ ∃! x χ)
    res = lb.ref(
        "res",
        "φ → (∃! x ψ ↔ ∃! x χ)",
        s_alrimiv,
        s_eubi,
        ref="syl",
        note="syl alrimiv, eubi",
    )
    return lb.build(res)


def prove_euan(sys: System) -> Proof:
    """euan: ∃! x ( φ ∧ ψ ) ↔ ( φ ∧ ∃! x ψ ).
    The unique existential quantifier distributes over a conjunction.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "euan")
    h_nf = lb.hyp("moanim.1", "Ⅎ x φ")
    # euex: ∃! x ( φ ∧ ψ ) → ∃ x ( φ ∧ ψ )
    s_euex = lb.ref(
        "s_euex",
        "∃! x ( φ ∧ ψ ) → ∃ x ( φ ∧ ψ )",
        ref="euex",
        note="euex",
    )
    # simpl: ( φ ∧ ψ ) → φ
    s_simpl = lb.ref(
        "s_simpl",
        "( φ ∧ ψ ) → φ",
        ref="simpl",
        note="simpl",
    )
    # exlimi moanim.1, simpl: ∃ x ( φ ∧ ψ ) → φ
    s_exlimi = lb.ref(
        "s_exlimi",
        "∃ x ( φ ∧ ψ ) → φ",
        h_nf,
        s_simpl,
        ref="exlimi",
        note="exlimi moanim.1, simpl",
    )
    # syl euex, exlimi: ∃! x ( φ ∧ ψ ) → φ
    s_syl = lb.ref(
        "s_syl",
        "∃! x ( φ ∧ ψ ) → φ",
        s_euex,
        s_exlimi,
        ref="syl",
        note="syl euex, exlimi",
    )
    # ibar: φ → ( ψ ↔ ( φ ∧ ψ ) )
    s_ibar = lb.ref(
        "s_ibar",
        "φ → ( ψ ↔ ( φ ∧ ψ ) )",
        ref="ibar",
        note="ibar",
    )
    # eubid moanim.1, ibar: φ → ( ∃! x ψ ↔ ∃! x ( φ ∧ ψ ) )
    s_eubid = lb.ref(
        "s_eubid",
        "φ → ( ∃! x ψ ↔ ∃! x ( φ ∧ ψ ) )",
        h_nf,
        s_ibar,
        ref="eubid",
        note="eubid moanim.1, ibar",
    )
    # biimprcd eubid: ∃! x ( φ ∧ ψ ) → ( φ → ∃! x ψ )
    s_biimprcd = lb.ref(
        "s_biimprcd",
        "∃! x ( φ ∧ ψ ) → ( φ → ∃! x ψ )",
        s_eubid,
        ref="biimprcd",
        note="biimprcd eubid",
    )
    # jcai syl, biimprcd: ∃! x ( φ ∧ ψ ) → ( φ ∧ ∃! x ψ )
    s_jcai = lb.ref(
        "s_jcai",
        "∃! x ( φ ∧ ψ ) → ( φ ∧ ∃! x ψ )",
        s_syl,
        s_biimprcd,
        ref="jcai",
        note="jcai syl, biimprcd",
    )
    # biimpa eubid: ( φ ∧ ∃! x ψ ) → ∃! x ( φ ∧ ψ )
    s_biimpa = lb.ref(
        "s_biimpa",
        "( φ ∧ ∃! x ψ ) → ∃! x ( φ ∧ ψ )",
        s_eubid,
        ref="biimpa",
        note="biimpa eubid",
    )
    # impbii jcai, biimpa: ∃! x ( φ ∧ ψ ) ↔ ( φ ∧ ∃! x ψ )
    res = lb.ref(
        "res",
        "∃! x ( φ ∧ ψ ) ↔ ( φ ∧ ∃! x ψ )",
        s_jcai,
        s_biimpa,
        ref="impbii",
        note="impbii jcai, biimpa",
    )
    return lb.build(res)


def prove_euanv(sys: System) -> Proof:
    """euanv: ∃! x ( φ ∧ ψ ) ↔ ( φ ∧ ∃! x ψ ).
    A version of euan with a distinct variable condition: the unique
    existential quantifier distributes over a conjunction when the
    left conjunct does not contain the bound variable.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "euanv")
    # euex: ∃! x ( φ ∧ ψ ) → ∃ x ( φ ∧ ψ )
    s_euex = lb.ref(
        "s_euex",
        "∃! x ( φ ∧ ψ ) → ∃ x ( φ ∧ ψ )",
        ref="euex",
        note="euex",
    )
    # simpl: ( φ ∧ ψ ) → φ
    s_simpl = lb.ref(
        "s_simpl",
        "( φ ∧ ψ ) → φ",
        ref="simpl",
        note="simpl",
    )
    # exlimiv s_simpl: ∃ x ( φ ∧ ψ ) → φ
    s_exlimiv = lb.ref(
        "s_exlimiv",
        "∃ x ( φ ∧ ψ ) → φ",
        s_simpl,
        ref="exlimiv",
        note="exlimiv simpl",
    )
    # syl s_euex, s_exlimiv: ∃! x ( φ ∧ ψ ) → φ
    s_syl = lb.ref(
        "s_syl",
        "∃! x ( φ ∧ ψ ) → φ",
        s_euex,
        s_exlimiv,
        ref="syl",
        note="syl euex, exlimiv",
    )
    # ibar: φ → ( ψ ↔ ( φ ∧ ψ ) )
    s_ibar = lb.ref(
        "s_ibar",
        "φ → ( ψ ↔ ( φ ∧ ψ ) )",
        ref="ibar",
        note="ibar",
    )
    # eubidv s_ibar: φ → ( ∃! x ψ ↔ ∃! x ( φ ∧ ψ ) )
    s_eubidv = lb.ref(
        "s_eubidv",
        "φ → ( ∃! x ψ ↔ ∃! x ( φ ∧ ψ ) )",
        s_ibar,
        ref="eubidv",
        note="eubidv ibar",
    )
    # biimprcd s_eubidv: ∃! x ( φ ∧ ψ ) → ( φ → ∃! x ψ )
    s_biimprcd = lb.ref(
        "s_biimprcd",
        "∃! x ( φ ∧ ψ ) → ( φ → ∃! x ψ )",
        s_eubidv,
        ref="biimprcd",
        note="biimprcd eubidv",
    )
    # jcai s_syl, s_biimprcd: ∃! x ( φ ∧ ψ ) → ( φ ∧ ∃! x ψ )
    s_jcai = lb.ref(
        "s_jcai",
        "∃! x ( φ ∧ ψ ) → ( φ ∧ ∃! x ψ )",
        s_syl,
        s_biimprcd,
        ref="jcai",
        note="jcai syl, biimprcd",
    )
    # biimpa s_eubidv: ( φ ∧ ∃! x ψ ) → ∃! x ( φ ∧ ψ )
    s_biimpa = lb.ref(
        "s_biimpa",
        "( φ ∧ ∃! x ψ ) → ∃! x ( φ ∧ ψ )",
        s_eubidv,
        ref="biimpa",
        note="biimpa eubidv",
    )
    # impbii s_jcai, s_biimpa: ∃! x ( φ ∧ ψ ) ↔ ( φ ∧ ∃! x ψ )
    res = lb.ref(
        "res",
        "∃! x ( φ ∧ ψ ) ↔ ( φ ∧ ∃! x ψ )",
        s_jcai,
        s_biimpa,
        ref="impbii",
        note="impbii jcai, biimpa",
    )
    return lb.build(res)


def prove_2eu7(sys: System) -> Proof:
    """2eu7: ( ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) ↔ ∃! x ∃! y ( ∃ x φ ∧ ∃ y φ ) ).

    Two equivalent expressions for double existential uniqueness.
    (Contributed by NM, 19-Feb-2005.)
    """
    lb = ProofBuilder(sys, "2eu7")

    # 35: nfe1: Ⅎ x ∃ x φ
    s35 = lb.ref("s35", "Ⅎ x ∃ x φ", ref="nfe1", note="nfe1")

    # 36: nfeu with s35: Ⅎ x ∃! y ∃ x φ
    s36 = lb.ref("s36", "Ⅎ x ∃! y ∃ x φ", s35, ref="nfeu", note="nfeu nfe1")

    # 37: euan with s36:
    # ∃! x ( ∃! y ∃ x φ ∧ ∃ y φ ) ↔ ( ∃! y ∃ x φ ∧ ∃! x ∃ y φ )
    s37 = lb.ref(
        "s37",
        "∃! x ( ∃! y ∃ x φ ∧ ∃ y φ ) ↔ ( ∃! y ∃ x φ ∧ ∃! x ∃ y φ )",
        s36,
        ref="euan",
        note="euan nfeu",
    )

    # 56: ancom: ( ∃ x φ ∧ ∃ y φ ) ↔ ( ∃ y φ ∧ ∃ x φ )
    s56 = lb.ref(
        "s56",
        "( ∃ x φ ∧ ∃ y φ ) ↔ ( ∃ y φ ∧ ∃ x φ )",
        ref="ancom",
        note="ancom",
    )

    # 57: eubii with s56: ∃! y ( ∃ x φ ∧ ∃ y φ ) ↔ ∃! y ( ∃ y φ ∧ ∃ x φ )
    s57 = lb.ref(
        "s57",
        "∃! y ( ∃ x φ ∧ ∃ y φ ) ↔ ∃! y ( ∃ y φ ∧ ∃ x φ )",
        s56,
        ref="eubii",
        note="eubii ancom",
    )

    # 63: nfe1: Ⅎ y ∃ y φ
    s63 = lb.ref("s63", "Ⅎ y ∃ y φ", ref="nfe1", note="nfe1")

    # 64: euan with s63: ∃! y ( ∃ y φ ∧ ∃ x φ ) ↔ ( ∃ y φ ∧ ∃! y ∃ x φ )
    s64 = lb.ref(
        "s64",
        "∃! y ( ∃ y φ ∧ ∃ x φ ) ↔ ( ∃ y φ ∧ ∃! y ∃ x φ )",
        s63,
        ref="euan",
        note="euan nfe1",
    )

    # 67: ancom: ( ∃ y φ ∧ ∃! y ∃ x φ ) ↔ ( ∃! y ∃ x φ ∧ ∃ y φ )
    s67 = lb.ref(
        "s67",
        "( ∃ y φ ∧ ∃! y ∃ x φ ) ↔ ( ∃! y ∃ x φ ∧ ∃ y φ )",
        ref="ancom",
        note="ancom",
    )

    # 68: 3bitri with s57, s64, s67:
    # ∃! y ( ∃ x φ ∧ ∃ y φ ) ↔ ( ∃! y ∃ x φ ∧ ∃ y φ )
    s68 = lb.ref(
        "s68",
        "∃! y ( ∃ x φ ∧ ∃ y φ ) ↔ ( ∃! y ∃ x φ ∧ ∃ y φ )",
        s57,
        s64,
        s67,
        ref="3bitri",
        note="3bitri eubii, euan, ancom",
    )

    # 69: eubii with s68:
    # ∃! x ∃! y ( ∃ x φ ∧ ∃ y φ ) ↔ ∃! x ( ∃! y ∃ x φ ∧ ∃ y φ )
    s69 = lb.ref(
        "s69",
        "∃! x ∃! y ( ∃ x φ ∧ ∃ y φ ) ↔ ∃! x ( ∃! y ∃ x φ ∧ ∃ y φ )",
        s68,
        ref="eubii",
        note="eubii 3bitri",
    )

    # 72: ancom:
    # ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) ↔ ( ∃! y ∃ x φ ∧ ∃! x ∃ y φ )
    s72 = lb.ref(
        "s72",
        "( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) ↔ ( ∃! y ∃ x φ ∧ ∃! x ∃ y φ )",
        ref="ancom",
        note="ancom",
    )

    # 73: 3bitr4ri with s37, s69, s72:
    # ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) ↔ ∃! x ∃! y ( ∃ x φ ∧ ∃ y φ )
    res = lb.ref(
        "res",
        "( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) ↔ ∃! x ∃! y ( ∃ x φ ∧ ∃ y φ )",
        s37,
        s69,
        s72,
        ref="3bitr4ri",
        note="3bitr4ri euan, eubii, ancom",
    )

    return lb.build(res)


def prove_2eu8(sys: System) -> Proof:
    """2eu8: ∃! x ∃! y ( ∃ x φ ∧ ∃ y φ ) ↔ ∃! x ∃! y ( ∃! x φ ∧ ∃ y φ ).

    Double existential uniqueness with one quantifier simplified under the
    condition of the other.  (Contributed by NM, 8-Dec-2001.)
    """
    lb = ProofBuilder(sys, "2eu8")

    # 2eu2: ∃! x ∃ y φ → ( ∃! y ∃! x φ ↔ ∃! y ∃ x φ )
    s1 = lb.ref(
        "s1",
        "∃! x ∃ y φ → ( ∃! y ∃! x φ ↔ ∃! y ∃ x φ )",
        ref="2eu2",
        note="2eu2",
    )

    # pm5.32i s1: ( ∃! x ∃ y φ ∧ ∃! y ∃! x φ ) ↔ ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ )
    s2 = lb.ref(
        "s2",
        "( ∃! x ∃ y φ ∧ ∃! y ∃! x φ ) ↔ ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ )",
        s1,
        ref="pm5.32i",
        note="pm5.32i 2eu2",
    )

    # nfeu1: Ⅎ x ∃! x φ
    s3 = lb.ref("s3", "Ⅎ x ∃! x φ", ref="nfeu1", note="nfeu1")

    # nfeu s3: Ⅎ x ∃! y ∃! x φ
    s4 = lb.ref("s4", "Ⅎ x ∃! y ∃! x φ", s3, ref="nfeu", note="nfeu nfeu1")

    # euan s4: ∃! x ( ∃! y ∃! x φ ∧ ∃ y φ ) ↔ ( ∃! y ∃! x φ ∧ ∃! x ∃ y φ )
    s5 = lb.ref(
        "s5",
        "∃! x ( ∃! y ∃! x φ ∧ ∃ y φ ) ↔ ( ∃! y ∃! x φ ∧ ∃! x ∃ y φ )",
        s4,
        ref="euan",
        note="euan nfeu",
    )

    # ancom: ( ∃! x φ ∧ ∃ y φ ) ↔ ( ∃ y φ ∧ ∃! x φ )
    s6 = lb.ref(
        "s6",
        "( ∃! x φ ∧ ∃ y φ ) ↔ ( ∃ y φ ∧ ∃! x φ )",
        ref="ancom",
        note="ancom",
    )

    # eubii s6: ∃! y ( ∃! x φ ∧ ∃ y φ ) ↔ ∃! y ( ∃ y φ ∧ ∃! x φ )
    s7 = lb.ref(
        "s7",
        "∃! y ( ∃! x φ ∧ ∃ y φ ) ↔ ∃! y ( ∃ y φ ∧ ∃! x φ )",
        s6,
        ref="eubii",
        note="eubii ancom",
    )

    # nfe1: Ⅎ y ∃ y φ
    s8 = lb.ref("s8", "Ⅎ y ∃ y φ", ref="nfe1", note="nfe1")

    # euan s8: ∃! y ( ∃ y φ ∧ ∃! x φ ) ↔ ( ∃ y φ ∧ ∃! y ∃! x φ )
    s9 = lb.ref(
        "s9",
        "∃! y ( ∃ y φ ∧ ∃! x φ ) ↔ ( ∃ y φ ∧ ∃! y ∃! x φ )",
        s8,
        ref="euan",
        note="euan nfe1",
    )

    # ancom: ( ∃ y φ ∧ ∃! y ∃! x φ ) ↔ ( ∃! y ∃! x φ ∧ ∃ y φ )
    s10 = lb.ref(
        "s10",
        "( ∃ y φ ∧ ∃! y ∃! x φ ) ↔ ( ∃! y ∃! x φ ∧ ∃ y φ )",
        ref="ancom",
        note="ancom",
    )

    # 3bitri s7, s9, s10:
    # ∃! y ( ∃! x φ ∧ ∃ y φ ) ↔ ( ∃! y ∃! x φ ∧ ∃ y φ )
    s11 = lb.ref(
        "s11",
        "∃! y ( ∃! x φ ∧ ∃ y φ ) ↔ ( ∃! y ∃! x φ ∧ ∃ y φ )",
        s7,
        s9,
        s10,
        ref="3bitri",
        note="3bitri eubii, euan, ancom",
    )

    # eubii s11:
    # ∃! x ∃! y ( ∃! x φ ∧ ∃ y φ ) ↔ ∃! x ( ∃! y ∃! x φ ∧ ∃ y φ )
    s12 = lb.ref(
        "s12",
        "∃! x ∃! y ( ∃! x φ ∧ ∃ y φ ) ↔ ∃! x ( ∃! y ∃! x φ ∧ ∃ y φ )",
        s11,
        ref="eubii",
        note="eubii 3bitri",
    )

    # ancom: ( ∃! x ∃ y φ ∧ ∃! y ∃! x φ ) ↔ ( ∃! y ∃! x φ ∧ ∃! x ∃ y φ )
    s13 = lb.ref(
        "s13",
        "( ∃! x ∃ y φ ∧ ∃! y ∃! x φ ) ↔ ( ∃! y ∃! x φ ∧ ∃! x ∃ y φ )",
        ref="ancom",
        note="ancom",
    )

    # 3bitr4ri s5, s12, s13:
    # ( ∃! x ∃ y φ ∧ ∃! y ∃! x φ ) ↔ ∃! x ∃! y ( ∃! x φ ∧ ∃ y φ )
    s14 = lb.ref(
        "s14",
        "( ∃! x ∃ y φ ∧ ∃! y ∃! x φ ) ↔ ∃! x ∃! y ( ∃! x φ ∧ ∃ y φ )",
        s5,
        s12,
        s13,
        ref="3bitr4ri",
        note="3bitr4ri euan, eubii, ancom",
    )

    # 2eu7: ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) ↔ ∃! x ∃! y ( ∃ x φ ∧ ∃ y φ )
    s15 = lb.ref(
        "s15",
        "( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) ↔ ∃! x ∃! y ( ∃ x φ ∧ ∃ y φ )",
        ref="2eu7",
        note="2eu7",
    )

    # 3bitr3ri s2, s14, s15:
    # ∃! x ∃! y ( ∃ x φ ∧ ∃ y φ ) ↔ ∃! x ∃! y ( ∃! x φ ∧ ∃ y φ )
    res = lb.ref(
        "res",
        "∃! x ∃! y ( ∃ x φ ∧ ∃ y φ ) ↔ ∃! x ∃! y ( ∃! x φ ∧ ∃ y φ )",
        s2,
        s14,
        s15,
        ref="3bitr3ri",
        note="3bitr3ri pm5.32i, 3bitr4ri, 2eu7",
    )

    return lb.build(res)


def prove_exists1(sys: System) -> Proof:
    """exists1: ( ∃! x x = x ↔ ∀ x ( x = y ) ).
    A uniqueness quantifier over a true equality is equivalent to the
    universal quantifier over equality to a fixed variable.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "exists1")
    # equid: x = x
    s_equid = lb.ref(
        "s_equid",
        "x = x",
        ref="equid",
        note="equid",
    )
    # bitru: ( x = x ↔ ⊤ )
    s_bitru = lb.ref(
        "s_bitru",
        "( x = x ↔ ⊤ )",
        s_equid,
        ref="bitru",
        note="bitru equid",
    )
    # eubii: ( ∃! x x = x ↔ ∃! x ⊤ )
    s_eubii = lb.ref(
        "s_eubii",
        "( ∃! x x = x ↔ ∃! x ⊤ )",
        s_bitru,
        ref="eubii",
        note="eubii bitru",
    )
    # euae: ( ∃! x ⊤ ↔ ∀ x ( x = y ) )
    s_euae = lb.ref(
        "s_euae",
        "( ∃! x ⊤ ↔ ∀ x ( x = y ) )",
        ref="euae",
        note="euae",
    )
    # bitri: ( ∃! x x = x ↔ ∀ x ( x = y ) )
    res = lb.ref(
        "res",
        "( ∃! x x = x ↔ ∀ x ( x = y ) )",
        s_eubii,
        s_euae,
        ref="bitri",
        note="bitri eubii, euae",
    )
    return lb.build(res)


def prove_euorv(sys: System) -> Proof:
    """euorv: ( ( ¬ φ ∧ ∃! x ψ ) → ∃! x ( φ ∨ ψ ) ).
    If a wff is false and there exists a unique x such that ψ,
    then there exists a unique x such that φ ∨ ψ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "euorv")
    # biorf: ( ¬ φ → ( ψ ↔ ( φ ∨ ψ ) ) )
    s_biorf = lb.ref(
        "s_biorf",
        "( ¬ φ → ( ψ ↔ ( φ ∨ ψ ) ) )",
        ref="biorf",
        note="biorf",
    )
    # eubidv s_biorf: ( ¬ φ → ( ∃! x ψ ↔ ∃! x ( φ ∨ ψ ) ) )
    s_eubidv = lb.ref(
        "s_eubidv",
        "( ¬ φ → ( ∃! x ψ ↔ ∃! x ( φ ∨ ψ ) ) )",
        s_biorf,
        ref="eubidv",
        note="eubidv biorf",
    )
    # biimpa s_eubidv: ( ( ¬ φ ∧ ∃! x ψ ) → ∃! x ( φ ∨ ψ ) )
    res = lb.ref(
        "res",
        "( ( ¬ φ ∧ ∃! x ψ ) → ∃! x ( φ ∨ ψ ) )",
        s_eubidv,
        ref="biimpa",
        note="biimpa eubidv",
    )
    return lb.build(res)


def prove_euor(sys: System) -> Proof:
    """euor: ( ( ¬ φ ∧ ∃! x ψ ) → ∃! x ( φ ∨ ψ ) ).
    If a wff is false (with x not free in it) and there exists a unique x
    such that ψ, then there exists a unique x such that φ ∨ ψ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "euor")
    hyp = lb.hyp("euor.nf", "Ⅎ x φ")
    # nfn euor.nf: Ⅎ x ¬ φ
    s_nfn = lb.ref(
        "s_nfn",
        "Ⅎ x ¬ φ",
        hyp,
        ref="nfn",
        note="nfn euor.nf",
    )
    # biorf: ¬ φ → ( ψ ↔ ( φ ∨ ψ ) )
    s_biorf = lb.ref(
        "s_biorf",
        "¬ φ → ( ψ ↔ ( φ ∨ ψ ) )",
        ref="biorf",
        note="biorf",
    )
    # eubid nfn, biorf: ¬ φ → ( ∃! x ψ ↔ ∃! x ( φ ∨ ψ ) )
    s_eubid = lb.ref(
        "s_eubid",
        "¬ φ → ( ∃! x ψ ↔ ∃! x ( φ ∨ ψ ) )",
        s_nfn,
        s_biorf,
        ref="eubid",
        note="eubid nfn, biorf",
    )
    # biimpa eubid: ( ( ¬ φ ∧ ∃! x ψ ) → ∃! x ( φ ∨ ψ ) )
    res = lb.ref(
        "res",
        "( ( ¬ φ ∧ ∃! x ψ ) → ∃! x ( φ ∨ ψ ) )",
        s_eubid,
        ref="biimpa",
        note="biimpa eubid",
    )
    return lb.build(res)


def prove_euor2(sys: System) -> Proof:
    """euor2: ¬ ∃ x φ → ( ∃! x ( φ ∨ ψ ) ↔ ∃! x ψ ).
    If there does not exist an x such that φ, then
    the unique existence of the disjunction φ ∨ ψ is equivalent
    to the unique existence of ψ.
    (Contributed by NM, 19-Feb-2004.)
    """
    lb = ProofBuilder(sys, "euor2")
    # nfe1: Ⅎ x ∃ x φ
    s_nfe1 = lb.ref(
        "s_nfe1",
        "Ⅎ x ∃ x φ",
        ref="nfe1",
        note="nfe1",
    )
    # nfn s_nfe1: Ⅎ x ¬ ∃ x φ
    s_nfn = lb.ref(
        "s_nfn",
        "Ⅎ x ¬ ∃ x φ",
        s_nfe1,
        ref="nfn",
        note="nfn nfe1",
    )
    # 19.8a: φ → ∃ x φ
    s_19_8a = lb.ref(
        "s_19_8a",
        "φ → ∃ x φ",
        ref="19.8a",
        note="19.8a",
    )
    # biorf: ¬ φ → ( ψ ↔ ( φ ∨ ψ ) )
    s_biorf = lb.ref(
        "s_biorf",
        "¬ φ → ( ψ ↔ ( φ ∨ ψ ) )",
        ref="biorf",
        note="biorf",
    )
    # nsyl5 19.8a, biorf: ¬ ∃ x φ → ( ψ ↔ ( φ ∨ ψ ) )
    s_nsyl5 = lb.ref(
        "s_nsyl5",
        "¬ ∃ x φ → ( ψ ↔ ( φ ∨ ψ ) )",
        s_19_8a,
        s_biorf,
        ref="nsyl5",
        note="nsyl5 19.8a, biorf",
    )
    # eubid nfn, nsyl5: ¬ ∃ x φ → ( ∃! x ψ ↔ ∃! x ( φ ∨ ψ ) )
    s_eubid = lb.ref(
        "s_eubid",
        "¬ ∃ x φ → ( ∃! x ψ ↔ ∃! x ( φ ∨ ψ ) )",
        s_nfn,
        s_nsyl5,
        ref="eubid",
        note="eubid nfn, nsyl5",
    )
    # bicomd eubid: ¬ ∃ x φ → ( ∃! x ( φ ∨ ψ ) ↔ ∃! x ψ )
    res = lb.ref(
        "res",
        "¬ ∃ x φ → ( ∃! x ( φ ∨ ψ ) ↔ ∃! x ψ )",
        s_eubid,
        ref="bicomd",
        note="bicomd eubid",
    )
    return lb.build(res)


def prove_19_19(sys: System) -> Proof:
    """19.19: ∀ x ( φ ↔ ψ ) → ( φ ↔ ∃ x ψ ).

    From a universal biconditional, the antecedent is equivalent to the
    existentially quantified consequent.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "19.19")
    hyp = lb.hyp("19.19.1", "Ⅎ x φ")
    # 19.9: Ⅎ x φ → ( ∃ x φ ↔ φ ) — via mp with 19.9.1, get ∃ x φ ↔ φ
    s1 = lb.ref(
        "s1",
        "∃ x φ ↔ φ",
        hyp,
        ref="19.9",
        note="19.9",
    )
    # exbi: ∀ x ( φ ↔ ψ ) → ( ∃ x φ ↔ ∃ x ψ )
    s2 = lb.ref(
        "s2",
        "∀ x ( φ ↔ ψ ) → ( ∃ x φ ↔ ∃ x ψ )",
        ref="exbi",
        note="exbi",
    )
    # bitr3id: ( ∃ x φ ↔ φ ), ( ∀ x ( φ ↔ ψ ) → ( ∃ x φ ↔ ∃ x ψ ) )
    #          ⊢ ( ∀ x ( φ ↔ ψ ) → ( φ ↔ ∃ x ψ ) )
    res = lb.ref(
        "res",
        "∀ x ( φ ↔ ψ ) → ( φ ↔ ∃ x ψ )",
        s1,
        s2,
        ref="bitr3id",
        note="bitr3id 19.9, exbi",
    )
    return lb.build(res)


def prove_rename_sb(sys: System) -> Proof:
    """rename-sb: ∀ y ( y = t → ∀ x ( x = y → φ ) ) ↔ ∀ z ( z = t → ∀ x ( x = z → φ ) ).
    Rename bound variable in a substitution-like context.
    (Contributed by NM, 10-Oct-1996.)
    """
    lb = ProofBuilder(sys, "rename-sb")
    # equequ1: y = z → ( y = t ↔ z = t )
    s_eq1 = lb.ref(
        "s_eq1",
        "y = z → ( y = t ↔ z = t )",
        ref="equequ1",
        note="equequ1",
    )
    # equequ2: y = z → ( x = y ↔ x = z )
    s_eq2 = lb.ref(
        "s_eq2",
        "y = z → ( x = y ↔ x = z )",
        ref="equequ2",
        note="equequ2",
    )
    # imbi1d: y = z → ( ( x = y → φ ) ↔ ( x = z → φ ) )
    s_imbi = lb.ref(
        "s_imbi",
        "y = z → ( ( x = y → φ ) ↔ ( x = z → φ ) )",
        s_eq2,
        ref="imbi1d",
        note="imbi1d equequ2",
    )
    # albidv: y = z → ( ∀ x ( x = y → φ ) ↔ ∀ x ( x = z → φ ) )
    s_alb = lb.ref(
        "s_alb",
        "y = z → ( ∀ x ( x = y → φ ) ↔ ∀ x ( x = z → φ ) )",
        s_imbi,
        ref="albidv",
        note="albidv imbi1d",
    )
    # imbi12d: y = z → ( ( y = t → ∀ x ( x = y → φ ) ) ↔ ( z = t → ∀ x ( x = z → φ ) ) )
    s_imbi12 = lb.ref(
        "s_imbi12",
        "y = z → ( ( y = t → ∀ x ( x = y → φ ) ) ↔ ( z = t → ∀ x ( x = z → φ ) ) )",
        s_eq1,
        s_alb,
        ref="imbi12d",
        note="imbi12d equequ1, albidv",
    )
    # cbvalvw: ∀ y ( y = t → ∀ x ( x = y → φ ) ) ↔ ∀ z ( z = t → ∀ x ( x = z → φ ) )
    res = lb.ref(
        "res",
        "∀ y ( y = t → ∀ x ( x = y → φ ) ) ↔ ∀ z ( z = t → ∀ x ( x = z → φ ) )",
        s_imbi12,
        ref="cbvalvw",
        note="cbvalvw",
    )
    return lb.build(res)


def prove_dfsb(sys: System) -> Proof:
    """dfsb: [ t / x ] φ ↔ ∀ y ( y = t → ∀ x ( x = y → φ ) ).
    Both directions of the df-sb definition simplified by rename-sb.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "dfsb")
    # dfsbimp: [ t / x ] φ → ∀ y ( y = t → ∀ x ( x = y → φ ) )
    s1 = lb.ref(
        "s1",
        "[ t x φ → ∀ y ( y = t → ∀ x ( x = y → φ ) )",
        ref="dfsbimp",
        note="dfsbimp",
    )
    # df-sb: [ t / x ] φ ↔ ( ∀ y ( y = t → ∀ x ( x = y → φ ) ) ∧ ∀ z ( z = t → ∀ x ( x = z → φ ) ) )
    s2 = lb.ref(
        "s2",
        "[ t x φ ↔ ( ∀ y ( y = t → ∀ x ( x = y → φ ) ) ∧ ∀ z ( z = t → ∀ x ( x = z → φ ) ) )",
        ref="df-sb",
        note="df-sb",
    )
    # rename-sb: ∀ y ( y = t → ∀ x ( x = y → φ ) ) ↔ ∀ z ( z = t → ∀ x ( x = z → φ ) )
    s3 = lb.ref(
        "s3",
        "∀ y ( y = t → ∀ x ( x = y → φ ) ) ↔ ∀ z ( z = t → ∀ x ( x = z → φ ) )",
        ref="rename-sb",
        note="rename-sb",
    )
    # just3-df with df-sb and rename-sb as hypotheses
    s4 = lb.ref(
        "s4",
        "∀ y ( y = t → ∀ x ( x = y → φ ) ) → [ t x φ",
        s2,
        s3,
        ref="just3-df",
        note="just3-df df-sb, rename-sb",
    )
    # impbii: combine both directions
    res = lb.ref(
        "res",
        "[ t x φ ↔ ∀ y ( y = t → ∀ x ( x = y → φ ) )",
        s1,
        s4,
        ref="impbii",
        note="impbii dfsbimp, just3-df",
    )
    return lb.build(res)


def prove_dfsb2(sys: System) -> Proof:
    """dfsb2: [ y / x ] φ ↔ ( ( x = y ∧ φ ) ∨ ∀ x ( x = y → φ ) ).

    Alternate definition of proper substitution, split into equality and
    universal quantification cases.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "dfsb2")

    # Forward direction: [y / x] φ → ((x = y ∧ φ) ∨ ∀x(x = y → φ))

    # sp: ∀ x x = y → x = y
    s1 = lb.ref(
        "s1",
        "∀ x x = y → x = y",
        ref="sp",
        note="sp",
    )

    # sbequ2: x = y → ( [ y / x ] φ → φ )
    s2 = lb.ref(
        "s2",
        "x = y → ( [ y x φ → φ )",
        ref="sbequ2",
        note="sbequ2",
    )

    # sps sbequ2: ∀ x x = y → ( [ y / x ] φ → φ )
    s3 = lb.ref(
        "s3",
        "∀ x x = y → ( [ y x φ → φ )",
        s2,
        ref="sps",
        note="sps sbequ2",
    )

    # orc: ( x = y ∧ φ ) → ( ( x = y ∧ φ ) ∨ ∀ x ( x = y → φ ) )
    s4 = lb.ref(
        "s4",
        "( x = y ∧ φ ) → ( ( x = y ∧ φ ) ∨ ∀ x ( x = y → φ ) )",
        ref="orc",
        note="orc",
    )

    # syl6an s1, s3, s4: ∀ x x = y → ( [ y / x ] φ → ( ( x = y ∧ φ ) ∨ ∀ x ( x = y → φ ) ) )
    s5 = lb.ref(
        "s5",
        "∀ x x = y → ( [ y x φ → ( ( x = y ∧ φ ) ∨ ∀ x ( x = y → φ ) ) )",
        s1,
        s3,
        s4,
        ref="syl6an",
        note="syl6an sp, sps, orc",
    )

    # sb4b: ¬ ∀ x x = y → ( [ y / x ] φ ↔ ∀ x ( x = y → φ ) )
    s6 = lb.ref(
        "s6",
        "¬ ∀ x x = y → ( [ y x φ ↔ ∀ x ( x = y → φ ) )",
        ref="sb4b",
        note="sb4b",
    )

    # olc: ∀ x ( x = y → φ ) → ( ( x = y ∧ φ ) ∨ ∀ x ( x = y → φ ) )
    s7 = lb.ref(
        "s7",
        "∀ x ( x = y → φ ) → ( ( x = y ∧ φ ) ∨ ∀ x ( x = y → φ ) )",
        ref="olc",
        note="olc",
    )

    # biimtrdi s6, s7: ¬ ∀ x x = y → ( [ y / x ] φ → ( ( x = y ∧ φ ) ∨ ∀ x ( x = y → φ ) ) )
    s8 = lb.ref(
        "s8",
        "¬ ∀ x x = y → ( [ y x φ → ( ( x = y ∧ φ ) ∨ ∀ x ( x = y → φ ) ) )",
        s6,
        s7,
        ref="biimtrdi",
        note="biimtrdi sb4b, olc",
    )

    # pm2.61i s5, s8: [ y / x ] φ → ( ( x = y ∧ φ ) ∨ ∀ x ( x = y → φ ) )
    s9 = lb.ref(
        "s9",
        "[ y x φ → ( ( x = y ∧ φ ) ∨ ∀ x ( x = y → φ ) )",
        s5,
        s8,
        ref="pm2.61i",
        note="pm2.61i syl6an, biimtrdi",
    )

    # Reverse direction: ((x = y ∧ φ) ∨ ∀x(x = y → φ)) → [y / x] φ

    # sbequ1: x = y → ( φ → [ y / x ] φ )
    s10 = lb.ref(
        "s10",
        "x = y → ( φ → [ y x φ )",
        ref="sbequ1",
        note="sbequ1",
    )

    # imp: ( x = y ∧ φ ) → [ y / x ] φ
    s11 = lb.ref(
        "s11",
        "( x = y ∧ φ ) → [ y x φ",
        s10,
        ref="imp",
        note="imp sbequ1",
    )

    # sb2: ∀ x ( x = y → φ ) → [ y / x ] φ
    s12 = lb.ref(
        "s12",
        "∀ x ( x = y → φ ) → [ y x φ",
        ref="sb2",
        note="sb2",
    )

    # jaoi s11, s12: ( ( x = y ∧ φ ) ∨ ∀ x ( x = y → φ ) ) → [ y / x ] φ
    s13 = lb.ref(
        "s13",
        "( ( x = y ∧ φ ) ∨ ∀ x ( x = y → φ ) ) → [ y x φ",
        s11,
        s12,
        ref="jaoi",
        note="jaoi imp, sb2",
    )

    # impbii s9, s13: [ y / x ] φ ↔ ( ( x = y ∧ φ ) ∨ ∀ x ( x = y → φ ) )
    res = lb.ref(
        "res",
        "[ y x φ ↔ ( ( x = y ∧ φ ) ∨ ∀ x ( x = y → φ ) )",
        s9,
        s13,
        ref="impbii",
        note="impbii pm2.61i, jaoi",
    )

    return lb.build(res)


def prove_dfsb3(sys: System) -> Proof:
    """dfsb3: [ y / x ] φ ↔ ( ( x = y → ¬ φ ) → ∀ x ( x = y → φ ) ).

    Alternate definition of proper substitution without explicit
    conjunction/disjunction.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "dfsb3")

    # dfsb2: [ y / x ] φ ↔ ( ( x = y ∧ φ ) ∨ ∀ x ( x = y → φ ) )
    s_dfsb2 = lb.ref(
        "s_dfsb2",
        "[ y x φ ↔ ( ( x = y ∧ φ ) ∨ ∀ x ( x = y → φ ) )",
        ref="dfsb2",
        note="dfsb2",
    )

    # df-or: ( ( x = y ∧ φ ) ∨ ∀ x ( x = y → φ ) ) ↔ ( ¬ ( x = y ∧ φ ) → ∀ x ( x = y → φ ) )
    s_dfor = lb.ref(
        "s_dfor",
        "( ( x = y ∧ φ ) ∨ ∀ x ( x = y → φ ) ) ↔ ( ¬ ( x = y ∧ φ ) → ∀ x ( x = y → φ ) )",
        ref="df-or",
        note="df-or",
    )

    # imnan: ( x = y → ¬ φ ) ↔ ¬ ( x = y ∧ φ )
    s_imnan = lb.ref(
        "s_imnan",
        "( x = y → ¬ φ ) ↔ ¬ ( x = y ∧ φ )",
        ref="imnan",
        note="imnan",
    )

    # imbi1i: from imnan, get ( ( x = y → ¬ φ ) → ∀ x ( x = y → φ ) ) ↔ ( ¬ ( x = y ∧ φ ) → ∀ x ( x = y → φ ) )
    s_imbi1i = lb.ref(
        "s_imbi1i",
        "( ( x = y → ¬ φ ) → ∀ x ( x = y → φ ) ) ↔ ( ¬ ( x = y ∧ φ ) → ∀ x ( x = y → φ ) )",
        s_imnan,
        ref="imbi1i",
        note="imbi1i imnan",
    )

    # 3bitr4i: chain dfsb2, df-or, imbi1i → goal
    res = lb.ref(
        "res",
        "[ y x φ ↔ ( ( x = y → ¬ φ ) → ∀ x ( x = y → φ ) )",
        s_dfor,
        s_dfsb2,
        s_imbi1i,
        ref="3bitr4i",
        note="3bitr4i dfsb2, df-or, imbi1i",
    )

    return lb.build(res)


def prove_sb7f(sys: System) -> Proof:
    """sb7f: [ y / x ] φ ↔ ∃ z ( z = y ∧ ∃ x ( x = z ∧ φ ) ).

    Equivalent form of proper substitution with ∃ z and ∃ x
    quantifiers.  This version does not require that φ and z be
    disjoint.  (Contributed by NM, 26-Jul-2006.)
    (Revised by Mario Carneiro, 6-Oct-2016.)
    """
    lb = ProofBuilder(sys, "sb7f")

    # hyp: Ⅎ z φ
    hyp_nf = lb.hyp("sb7f.1", "Ⅎ z φ")

    # sb5f with hyp_nf: [ z / x ] φ ↔ ∃ x ( x = z ∧ φ )
    s_sb5f = lb.ref(
        "s_sb5f",
        "( [ z x φ ↔ ∃ x ( x = z ∧ φ ) )",
        hyp_nf,
        ref="sb5f",
        note="sb5f",
    )

    # sbbii with s_sb5f as hypothesis:
    #   [ y / z ] [ z / x ] φ ↔ [ y / z ] ∃ x ( x = z ∧ φ )
    s_sbbii = lb.ref(
        "s_sbbii",
        "( [ y z [ z x φ ↔ [ y z ∃ x ( x = z ∧ φ ) )",
        s_sb5f,
        ref="sbbii",
        note="sbbii sb5f",
    )

    # sbco2 with hyp_nf: [ y / z ] [ z / x ] φ ↔ [ y / x ] φ
    s_sbco2 = lb.ref(
        "s_sbco2",
        "( [ y z [ z x φ ↔ [ y x φ )",
        hyp_nf,
        ref="sbco2",
        note="sbco2",
    )

    # sb5: [ y / z ] ∃ x ( x = z ∧ φ ) ↔ ∃ z ( z = y ∧ ∃ x ( x = z ∧ φ ) )
    s_sb5 = lb.ref(
        "s_sb5",
        "( [ y z ∃ x ( x = z ∧ φ ) ↔ ∃ z ( z = y ∧ ∃ x ( x = z ∧ φ ) ) )",
        ref="sb5",
        note="sb5",
    )

    # 3bitr3i: put it all together
    res = lb.ref(
        "res",
        "( [ y x φ ↔ ∃ z ( z = y ∧ ∃ x ( x = z ∧ φ ) ) )",
        s_sbbii,
        s_sbco2,
        s_sb5,
        ref="3bitr3i",
        note="3bitr3i sbbii, sbco2, sb5",
    )

    return lb.build(res)


def prove_sb7h(sys: System) -> Proof:
    """sb7h: [ y / x ] φ ↔ ∃ z ( z = y ∧ ∃ x ( x = z ∧ φ ) ).

    Hypothesis version of sb7f.  (Contributed by NM, 26-Jul-2006.)
    """
    lb = ProofBuilder(sys, "sb7h")

    # sb7h.1: φ → ∀ z φ
    hyp = lb.hyp("sb7h.1", "φ → ∀ z φ")

    # nf5i with hyp: Ⅎ z φ
    s_nf = lb.ref(
        "s_nf",
        "Ⅎ z φ",
        hyp,
        ref="nf5i",
        note="nf5i sb7h.1",
    )

    # sb7f with s_nf: [ y / x ] φ ↔ ∃ z ( z = y ∧ ∃ x ( x = z ∧ φ ) )
    res = lb.ref(
        "res",
        "( [ y x φ ↔ ∃ z ( z = y ∧ ∃ x ( x = z ∧ φ ) ) )",
        s_nf,
        ref="sb7f",
        note="sb7f",
    )

    return lb.build(res)


def prove_dfsb7(sys: System) -> Proof:
    """dfsb7: [ t / x ] φ ↔ ∃ y ( y = t ∧ ∃ x ( x = y ∧ φ ) ).
    Equivalent form of proper substitution expressed with equality
    and existential quantifiers.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "dfsb7")
    # sbalex: ∃ x ( x = y ∧ φ ) ↔ ∀ x ( x = y → φ )
    s1 = lb.ref(
        "s1",
        "∃ x ( x = y ∧ φ ) ↔ ∀ x ( x = y → φ )",
        ref="sbalex",
        note="sbalex",
    )
    # anbi2i: ( y = t ∧ ∃ x ( x = y ∧ φ ) ) ↔ ( y = t ∧ ∀ x ( x = y → φ ) )
    s2 = lb.ref(
        "s2",
        "( y = t ∧ ∃ x ( x = y ∧ φ ) ) ↔ ( y = t ∧ ∀ x ( x = y → φ ) )",
        s1,
        ref="anbi2i",
        note="anbi2i sbalex",
    )
    # exbii: ∃ y ( y = t ∧ ∃ x ( x = y ∧ φ ) ) ↔ ∃ y ( y = t ∧ ∀ x ( x = y → φ ) )
    s3 = lb.ref(
        "s3",
        "∃ y ( y = t ∧ ∃ x ( x = y ∧ φ ) ) ↔ ∃ y ( y = t ∧ ∀ x ( x = y → φ ) )",
        s2,
        ref="exbii",
        note="exbii anbi2i",
    )
    # dfsb: [ t / x ] φ ↔ ∀ y ( y = t → ∀ x ( x = y → φ ) )
    s4 = lb.ref(
        "s4",
        "[ t x φ ↔ ∀ y ( y = t → ∀ x ( x = y → φ ) )",
        ref="dfsb",
        note="dfsb",
    )
    # sbalex with ∀ x ( x = y → φ ) as φ:
    #   ∃ y ( y = t ∧ ∀ x ( x = y → φ ) ) ↔ ∀ y ( y = t → ∀ x ( x = y → φ ) )
    s5 = lb.ref(
        "s5",
        "∃ y ( y = t ∧ ∀ x ( x = y → φ ) ) ↔ ∀ y ( y = t → ∀ x ( x = y → φ ) )",
        ref="sbalex",
        note="sbalex",
    )
    # 3bitr4ri: Ph↔Ps, Ch↔Ph, Th↔Ps → Th↔Ch
    res = lb.ref(
        "res",
        "[ t x φ ↔ ∃ y ( y = t ∧ ∃ x ( x = y ∧ φ ) )",
        s5,
        s3,
        s4,
        ref="3bitr4ri",
        note="3bitr4ri sbalex, exbii, dfsb",
    )
    return lb.build(res)


def prove_dfsb1(sys: System) -> Proof:
    """dfsb1: [ y / x ] φ ↔ ( ( x = y → φ ) ∧ ∃ x ( x = y ∧ φ ) ).

    Alternate definition of substitution.  This was the original
    definition before df-sb.
    (Contributed by BJ, 9-Jul-2023.)  (Revised by Wolf Lammen,
    29-Jul-2023.)
    """
    lb = ProofBuilder(sys, "dfsb1")

    # 1. sbequ2: x = y → ( [ y / x ] φ → φ )
    s1 = lb.ref(
        "s1",
        "x = y → ( [ y x φ → φ )",
        ref="sbequ2",
        note="sbequ2",
    )

    # 2. com12 on 1: [ y / x ] φ → ( x = y → φ )
    s2 = lb.ref(
        "s2",
        "[ y x φ → ( x = y → φ )",
        s1,
        ref="com12",
        note="com12 sbequ2",
    )

    # 3. sb1: [ y / x ] φ → ∃ x ( x = y ∧ φ )
    s3 = lb.ref(
        "s3",
        "[ y x φ → ∃ x ( x = y ∧ φ )",
        ref="sb1",
        note="sb1",
    )

    # 4. jca on 2,3: [ y / x ] φ → ( ( x = y → φ ) ∧ ∃ x ( x = y ∧ φ ) )
    s4 = lb.ref(
        "s4",
        "[ y x φ → ( ( x = y → φ ) ∧ ∃ x ( x = y ∧ φ ) )",
        s2,
        s3,
        ref="jca",
        note="jca com12, sb1",
    )

    # 5. id: x = y → x = y
    s5 = lb.ref(
        "s5",
        "x = y → x = y",
        ref="id",
        note="id",
    )

    # 6. sbequ1: x = y → ( φ → [ y / x ] φ )
    s6 = lb.ref(
        "s6",
        "x = y → ( φ → [ y x φ )",
        ref="sbequ1",
        note="sbequ1",
    )

    # 7. embantd on 5,6: x = y → ( ( x = y → φ ) → [ y / x ] φ )
    s7 = lb.ref(
        "s7",
        "x = y → ( ( x = y → φ ) → [ y x φ )",
        s5,
        s6,
        ref="embantd",
        note="embantd id, sbequ1",
    )

    # 8. sps on 7: ∀ x x = y → ( ( x = y → φ ) → [ y / x ] φ )
    s8 = lb.ref(
        "s8",
        "∀ x x = y → ( ( x = y → φ ) → [ y x φ )",
        s7,
        ref="sps",
        note="sps embantd",
    )

    # 9. adantrd on 8: ∀ x x = y → ( ( ( x = y → φ ) ∧ ∃ x ( x = y ∧ φ ) ) → [ y / x ] φ )
    s9 = lb.ref(
        "s9",
        "∀ x x = y → ( ( ( x = y → φ ) ∧ ∃ x ( x = y ∧ φ ) ) → [ y x φ )",
        s8,
        ref="adantrd",
        note="adantrd sps",
    )

    # 10. sb3: ¬ ∀ x x = y → ( ∃ x ( x = y ∧ φ ) → [ y / x ] φ )
    s10 = lb.ref(
        "s10",
        "¬ ∀ x x = y → ( ∃ x ( x = y ∧ φ ) → [ y x φ )",
        ref="sb3",
        note="sb3",
    )

    # 11. adantld on 10: ¬ ∀ x x = y → ( ( ( x = y → φ ) ∧ ∃ x ( x = y ∧ φ ) ) → [ y / x ] φ )
    s11 = lb.ref(
        "s11",
        "¬ ∀ x x = y → ( ( ( x = y → φ ) ∧ ∃ x ( x = y ∧ φ ) ) → [ y x φ )",
        s10,
        ref="adantld",
        note="adantld sb3",
    )

    # 12. pm2.61i on 9,11: ( ( x = y → φ ) ∧ ∃ x ( x = y ∧ φ ) ) → [ y / x ] φ
    s12 = lb.ref(
        "s12",
        "( ( x = y → φ ) ∧ ∃ x ( x = y ∧ φ ) ) → [ y x φ",
        s9,
        s11,
        ref="pm2.61i",
        note="pm2.61i adantrd, adantld",
    )

    # 13. impbii on 4,12: [ y / x ] φ ↔ ( ( x = y → φ ) ∧ ∃ x ( x = y ∧ φ ) )
    res = lb.ref(
        "res",
        "[ y x φ ↔ ( ( x = y → φ ) ∧ ∃ x ( x = y ∧ φ ) )",
        s4,
        s12,
        ref="impbii",
        note="impbii jca, pm2.61i",
    )

    return lb.build(res)


def prove_stdpc4ALT(sys: System) -> Proof:
    """stdpc4ALT: ∀ x φ → [ t / x ] φ.
    Alternative proof of stdpc4 using dfsb and sylibr.
    (Contributed by NM, 14-May-1993.)
    """
    lb = ProofBuilder(sys, "stdpc4ALT")
    # ala1 with ψ := x = y → φ:
    #   ∀ x φ → ∀ x ( x = y → φ )
    s1 = lb.ref(
        "s1",
        "∀ x φ → ∀ x ( x = y → φ )",
        ref="ala1",
        note="ala1 with ψ := x = y → φ",
    )
    # a1d on s1: add antecedent y = t
    #   ∀ x φ → ( y = t → ∀ x ( x = y → φ ) )
    s2 = lb.ref(
        "s2",
        "∀ x φ → ( y = t → ∀ x ( x = y → φ ) )",
        s1,
        ref="a1d",
        note="a1d ala1",
    )
    # alrimiv on s2: generalize over y
    #   ∀ x φ → ∀ y ( y = t → ∀ x ( x = y → φ ) )
    s3 = lb.ref(
        "s3",
        "∀ x φ → ∀ y ( y = t → ∀ x ( x = y → φ ) )",
        s2,
        ref="alrimiv",
        note="alrimiv a1d",
    )
    # dfsb: [ t / x ] φ ↔ ∀ y ( y = t → ∀ x ( x = y → φ ) )
    s4 = lb.ref(
        "s4",
        "[ t x φ ↔ ∀ y ( y = t → ∀ x ( x = y → φ ) )",
        ref="dfsb",
        note="dfsb",
    )
    # sylibr: combine ∀ x φ → ∀ y (...) with the dfsb biconditional
    res = lb.ref(
        "res",
        "∀ x φ → [ t x φ",
        s3,
        s4,
        ref="sylibr",
        note="sylibr alrimiv, dfsb",
    )
    return lb.build(res)


def prove_sbequ(sys: System) -> Proof:
    """sbequ: x = y → ( [ x / z ] φ ↔ [ y / z ] φ ).
    Substitution is preserved under equality of the substituting variable.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbequ")
    # equequ2: x = y → ( u = x ↔ u = y )
    s_eq = lb.ref(
        "s_eq",
        "x = y → ( u = x ↔ u = y )",
        ref="equequ2",
        note="equequ2",
    )
    # imbi1d: x = y → ( ( u = x → ∀ z ( z = u → φ ) ) ↔ ( u = y → ∀ z ( z = u → φ ) ) )
    s_im = lb.ref(
        "s_im",
        "x = y → ( ( u = x → ∀ z ( z = u → φ ) ) ↔ ( u = y → ∀ z ( z = u → φ ) ) )",
        s_eq,
        ref="imbi1d",
        note="imbi1d equequ2",
    )
    # albidv: x = y → ( ∀ u ( u = x → ∀ z ( z = u → φ ) ) ↔ ∀ u ( u = y → ∀ z ( z = u → φ ) ) )
    s_al = lb.ref(
        "s_al",
        "x = y → ( ∀ u ( u = x → ∀ z ( z = u → φ ) ) ↔ ∀ u ( u = y → ∀ z ( z = u → φ ) ) )",
        s_im,
        ref="albidv",
        note="albidv imbi1d",
    )
    # dfsb: [ x / z ] φ ↔ ∀ u ( u = x → ∀ z ( z = u → φ ) )
    s_dfsb1 = lb.ref(
        "s_dfsb1",
        "[ x z φ ↔ ∀ u ( u = x → ∀ z ( z = u → φ ) )",
        ref="dfsb",
        note="dfsb",
    )
    # dfsb: [ y / z ] φ ↔ ∀ u ( u = y → ∀ z ( z = u → φ ) )
    s_dfsb2 = lb.ref(
        "s_dfsb2",
        "[ y z φ ↔ ∀ u ( u = y → ∀ z ( z = u → φ ) )",
        ref="dfsb",
        note="dfsb",
    )
    # 3bitr4g: x = y → ( [ x / z ] φ ↔ [ y / z ] φ )
    res = lb.ref(
        "res",
        "x = y → ( [ x z φ ↔ [ y z φ )",
        s_al,
        s_dfsb1,
        s_dfsb2,
        ref="3bitr4g",
        note="3bitr4g albidv, dfsb, dfsb",
    )
    return lb.build(res)


def prove_sbequi(sys: System) -> Proof:
    """sbequi: x = y → ( [ x / z ] φ → [ y / z ] φ ).
    Inference form of sbequ. (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbequi")
    # sbequ: x = y → ( [ x / z ] φ ↔ [ y / z ] φ )
    s1 = lb.ref(
        "s1",
        "x = y → ( [ x z φ ↔ [ y z φ )",
        ref="sbequ",
        note="sbequ",
    )
    # biimpd: x = y → ( [ x / z ] φ → [ y / z ] φ )
    res = lb.ref(
        "res",
        "x = y → ( [ x z φ → [ y z φ )",
        s1,
        ref="biimpd",
        note="biimpd sbequ",
    )
    return lb.build(res)


def prove_sbequ1(sys: System) -> Proof:
    """sbequ1: x = t → ( φ → [ t / x ] φ ).
    If x equals t, then φ implies the proper substitution of t for x in φ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbequ1")
    # equeucl: x = t → ( y = t → x = y )
    s1 = lb.ref(
        "s1",
        "x = t → ( y = t → x = y )",
        ref="equeucl",
        note="equeucl",
    )
    # ax12v: x = y → ( φ → ∀ x ( x = y → φ ) )
    s2 = lb.ref(
        "s2",
        "x = y → ( φ → ∀ x ( x = y → φ ) )",
        ref="ax12v",
        note="ax12v",
    )
    # syl6: x = t → ( y = t → ( φ → ∀ x ( x = y → φ ) ) )
    s3 = lb.ref(
        "s3",
        "x = t → ( y = t → ( φ → ∀ x ( x = y → φ ) ) )",
        s1,
        s2,
        ref="syl6",
        note="syl6 equeucl, ax12v",
    )
    # com23: x = t → ( φ → ( y = t → ∀ x ( x = y → φ ) ) )
    s4 = lb.ref(
        "s4",
        "x = t → ( φ → ( y = t → ∀ x ( x = y → φ ) ) )",
        s3,
        ref="com23",
        note="com23 syl6",
    )
    # alrimdv: x = t → ( φ → ∀ y ( y = t → ∀ x ( x = y → φ ) ) )
    s5 = lb.ref(
        "s5",
        "x = t → ( φ → ∀ y ( y = t → ∀ x ( x = y → φ ) ) )",
        s4,
        ref="alrimdv",
        note="alrimdv com23",
    )
    # dfsb: [ t / x ] φ ↔ ∀ y ( y = t → ∀ x ( x = y → φ ) )
    s6 = lb.ref(
        "s6",
        "[ t x φ ↔ ∀ y ( y = t → ∀ x ( x = y → φ ) )",
        ref="dfsb",
        note="dfsb",
    )
    # imbitrrdi: x = t → ( φ → [ t / x ] φ )
    res = lb.ref(
        "res",
        "x = t → ( φ → [ t x φ )",
        s5,
        s6,
        ref="imbitrrdi",
        note="imbitrrdi alrimdv, dfsb",
    )
    return lb.build(res)


def prove_sbequ12(sys: System) -> Proof:
    """sbequ12: x = y → ( φ ↔ [ y / x ] φ ).
    An equality theorem for substitution.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbequ12")
    # sbequ1: x = y → ( φ → [ y / x ] φ )
    s1 = lb.ref(
        "s1",
        "x = y → ( φ → [ y x φ )",
        ref="sbequ1",
        note="sbequ1",
    )
    # sbequ2: x = y → ( [ y / x ] φ → φ )
    s2 = lb.ref(
        "s2",
        "x = y → ( [ y x φ → φ )",
        ref="sbequ2",
        note="sbequ2",
    )
    # impbid: combine both directions
    res = lb.ref(
        "res",
        "x = y → ( φ ↔ [ y x φ )",
        s1,
        s2,
        ref="impbid",
        note="impbid sbequ1, sbequ2",
    )
    return lb.build(res)


def prove_sbequ12r(sys: System) -> Proof:
    """sbequ12r: x = y → ( [ x / y ] φ ↔ φ ).
    An equality theorem for substitution (right-hand form).
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbequ12r")
    # sbequ12 with x:=y, y:=x: y = x → ( φ ↔ [ x / y ] φ )
    s1 = lb.ref(
        "s1",
        "y = x → ( φ ↔ [ x y φ )",
        ref="sbequ12",
        note="sbequ12 with x:=y, y:=x",
    )
    # bicomd: swap the biconditional
    s2 = lb.ref(
        "s2",
        "y = x → ( [ x y φ ↔ φ )",
        s1,
        ref="bicomd",
        note="bicomd",
    )
    # equcoms: swap the equality
    res = lb.ref(
        "res",
        "x = y → ( [ x y φ ↔ φ )",
        s2,
        ref="equcoms",
        note="equcoms",
    )
    return lb.build(res)


def prove_sbequ12a(sys: System) -> Proof:
    """sbequ12a: x = y → ( [ y / x ] φ ↔ [ x / y ] φ ).
    An equality theorem for substitution (alternative form).
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbequ12a")
    # sbequ12r: x = y → ( [ x / y ] φ ↔ φ )
    s1 = lb.ref(
        "s1",
        "x = y → ( [ x y φ ↔ φ )",
        ref="sbequ12r",
        note="sbequ12r",
    )
    # sbequ12: x = y → ( φ ↔ [ y / x ] φ )
    s2 = lb.ref(
        "s2",
        "x = y → ( φ ↔ [ y x φ )",
        ref="sbequ12",
        note="sbequ12",
    )
    # bitr2d: chain the biconditionals
    res = lb.ref(
        "res",
        "x = y → ( [ y x φ ↔ [ x y φ )",
        s1,
        s2,
        ref="bitr2d",
        note="bitr2d sbequ12r, sbequ12",
    )
    return lb.build(res)


def prove_sbelx(sys: System) -> Proof:
    """sbelx: φ ↔ ∃ x ( x = y ∧ [ x / y ] φ ).
    Substitution in both sides of a biconditional, with a disjoint variable condition.
    (Contributed by NM, 2-Jan-1993.)
    """
    lb = ProofBuilder(sys, "sbelx")
    # sbequ12r: x = y → ( [ x / y ] φ ↔ φ )
    s1 = lb.ref(
        "s1",
        "x = y → ( [ x y φ ↔ φ )",
        ref="sbequ12r",
        note="sbequ12r",
    )
    # equsexvw: ∃ x ( x = y ∧ [ x / y ] φ ) ↔ φ
    s2 = lb.ref(
        "s2",
        "∃ x ( x = y ∧ [ x y φ ) ↔ φ",
        s1,
        ref="equsexvw",
        note="equsexvw sbequ12r",
    )
    # bicomi: φ ↔ ∃ x ( x = y ∧ [ x / y ] φ )
    res = lb.ref(
        "res",
        "φ ↔ ∃ x ( x = y ∧ [ x y φ )",
        s2,
        ref="bicomi",
        note="bicomi",
    )
    return lb.build(res)


def prove_sbel2x(sys: System) -> Proof:
    """sbel2x: φ ↔ ∃ x ∃ y ( ( x = z ∧ y = w ) ∧ [ y / w ] [ x / z ] φ ).

    Elimination of double substitution.
    (Contributed by NM, 5-Aug-1993.)
    (Proof shortened by Wolf Lammen, 29-Sep-2018.)
    """
    lb = ProofBuilder(sys, "sbel2x")

    # nfv: Ⅎ y φ
    s_nfv_y = lb.ref("nfv_y", "Ⅎ y φ", ref="nfv", note="nfv")

    # nfv: Ⅎ x φ
    s_nfv_x = lb.ref("nfv_x", "Ⅎ x φ", ref="nfv", note="nfv")

    # 2sb5rf with Ⅎ y φ (as 2sb5rf.1) and Ⅎ x φ (as 2sb5rf.2)
    # This yields: φ ↔ ∃ y ∃ x ( ( y = w ∧ x = z ) ∧ [ y / w ] [ x / z ] φ )
    s_2sb5rf = lb.ref(
        "s_2sb5rf",
        "φ ↔ ∃ y ∃ x ( ( y = w ∧ x = z ) ∧ [ y w [ x z φ )",
        s_nfv_y,
        s_nfv_x,
        ref="2sb5rf",
        note="2sb5rf nfv, nfv",
    )

    # ancom: ( y = w ∧ x = z ) ↔ ( x = z ∧ y = w )
    s_ancom = lb.ref(
        "s_ancom",
        "( y = w ∧ x = z ) ↔ ( x = z ∧ y = w )",
        ref="ancom",
        note="ancom",
    )

    # anbi1i: ( ( y = w ∧ x = z ) ∧ [ y / w ] [ x / z ] φ ) ↔
    #         ( ( x = z ∧ y = w ) ∧ [ y / w ] [ x / z ] φ )
    s_anbi1i = lb.ref(
        "s_anbi1i",
        "( ( y = w ∧ x = z ) ∧ [ y w [ x z φ ) ↔ ( ( x = z ∧ y = w ) ∧ [ y w [ x z φ )",
        s_ancom,
        ref="anbi1i",
        note="anbi1i ancom",
    )

    # 2exbii: ∃ y ∃ x ( ( y = w ∧ x = z ) ∧ [ y / w ] [ x / z ] φ ) ↔
    #         ∃ y ∃ x ( ( x = z ∧ y = w ) ∧ [ y / w ] [ x / z ] φ )
    s_2exbii = lb.ref(
        "s_2exbii",
        "∃ y ∃ x ( ( y = w ∧ x = z ) ∧ [ y w [ x z φ ) ↔ ∃ y ∃ x ( ( x = z ∧ y = w ) ∧ [ y w [ x z φ )",
        s_anbi1i,
        ref="2exbii",
        note="2exbii anbi1i",
    )

    # excom: ∃ y ∃ x ( ( x = z ∧ y = w ) ∧ [ y / w ] [ x / z ] φ ) ↔
    #        ∃ x ∃ y ( ( x = z ∧ y = w ) ∧ [ y / w ] [ x / z ] φ )
    s_excom = lb.ref(
        "s_excom",
        "∃ y ∃ x ( ( x = z ∧ y = w ) ∧ [ y w [ x z φ ) ↔ ∃ x ∃ y ( ( x = z ∧ y = w ) ∧ [ y w [ x z φ )",
        ref="excom",
        note="excom",
    )

    # 3bitri: chain s_2sb5rf, s_2exbii, s_excom
    res = lb.ref(
        "res",
        "φ ↔ ∃ x ∃ y ( ( x = z ∧ y = w ) ∧ [ y w [ x z φ )",
        s_2sb5rf,
        s_2exbii,
        s_excom,
        ref="3bitri",
        note="3bitri 2sb5rf, 2exbii, excom",
    )

    return lb.build(res)


def prove_sb10f(sys: System) -> Proof:
    """sb10f: [ y / z ] φ ↔ ∃ x ( x = y ∧ [ x / z ] φ ).

    Substitution expressed in terms of existential quantification
    and equality, with a non-freeness condition.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sb10f")
    hyp = lb.hyp("sb10f.1", "Ⅎ x φ")

    # nfsb: from Ⅎ x φ, get Ⅎ x [ y / z ] φ
    s1 = lb.ref(
        "s1",
        "Ⅎ x [ y z φ",
        hyp,
        ref="nfsb",
        note="nfsb",
    )

    # sbequ: x = y → ( [ x / z ] φ ↔ [ y / z ] φ )
    s2 = lb.ref(
        "s2",
        "x = y → ( [ x z φ ↔ [ y z φ )",
        ref="sbequ",
        note="sbequ",
    )

    # equsexv: from Ⅎ x [ y / z ] φ and x = y → ( [ x / z ] φ ↔ [ y / z ] φ ),
    # get ∃ x ( x = y ∧ [ x / z ] φ ) ↔ [ y / z ] φ
    s3 = lb.ref(
        "s3",
        "∃ x ( x = y ∧ [ x z φ ) ↔ [ y z φ",
        s1,
        s2,
        ref="equsexv",
        note="equsexv nfsb, sbequ",
    )

    # bicomi: flip the biconditional
    res = lb.ref(
        "res",
        "[ y z φ ↔ ∃ x ( x = y ∧ [ x z φ )",
        s3,
        ref="bicomi",
        note="bicomi",
    )

    return lb.build(res)


def prove_sb1(sys: System) -> Proof:
    """sb1: [ y / x ] φ → ∃ x ( x = y ∧ φ ).

    One direction of a simplified definition of substitution.
    The converse requires either a disjoint variable condition or a
    nonfreeness hypothesis.  (Contributed by NM, 13-May-1993.)
    """
    lb = ProofBuilder(sys, "sb1")

    # 1. spsbe: [ y / x ] φ → ∃ x φ
    s1 = lb.ref(
        "s1",
        "[ y x φ → ∃ x φ",
        ref="spsbe",
        note="spsbe",
    )

    # 2. pm3.2: ( x = y → ( φ → ( x = y ∧ φ ) ) )
    s2 = lb.ref(
        "s2",
        "x = y → ( φ → ( x = y ∧ φ ) )",
        ref="pm3.2",
        note="pm3.2",
    )

    # 3. aleximi on step 2: ∀ x x = y → ( ∃ x φ → ∃ x ( x = y ∧ φ ) )
    s3 = lb.ref(
        "s3",
        "∀ x x = y → ( ∃ x φ → ∃ x ( x = y ∧ φ ) )",
        s2,
        ref="aleximi",
        note="aleximi pm3.2",
    )

    # 4. syl5 on steps 1,3: ∀ x x = y → ( [ y / x ] φ → ∃ x ( x = y ∧ φ ) )
    s4 = lb.ref(
        "s4",
        "∀ x x = y → ( [ y x φ → ∃ x ( x = y ∧ φ ) )",
        s1,
        s3,
        ref="syl5",
        note="syl5 spsbe, aleximi",
    )

    # 5. sb3b: ¬ ∀ x x = y → ( [ y / x ] φ ↔ ∃ x ( x = y ∧ φ ) )
    s5 = lb.ref(
        "s5",
        "¬ ∀ x x = y → ( [ y x φ ↔ ∃ x ( x = y ∧ φ ) )",
        ref="sb3b",
        note="sb3b",
    )

    # 6. biimpd on step 5: ¬ ∀ x x = y → ( [ y / x ] φ → ∃ x ( x = y ∧ φ ) )
    s6 = lb.ref(
        "s6",
        "¬ ∀ x x = y → ( [ y x φ → ∃ x ( x = y ∧ φ ) )",
        s5,
        ref="biimpd",
        note="biimpd sb3b",
    )

    # 7. pm2.61i on steps 4,6: [ y / x ] φ → ∃ x ( x = y ∧ φ )
    res = lb.ref(
        "res",
        "[ y x φ → ∃ x ( x = y ∧ φ )",
        s4,
        s6,
        ref="pm2.61i",
        note="pm2.61i",
    )

    return lb.build(res)


def prove_sb1v(sys: System) -> Proof:
    """sb1v: ( [ y / x ] φ → ∃ x ( x = y ∧ φ ) ).
    Version of sb1 with a disjoint variable condition using fewer axioms.
    (Contributed by BJ, 30-Dec-2020.)
    """
    lb = ProofBuilder(sys, "sb1v")
    # sb6: [ y / x ] φ ↔ ∀ x ( x = y → φ )
    s1 = lb.ref(
        "s1",
        "[ y x φ ↔ ∀ x ( x = y → φ )",
        ref="sb6",
        note="sb6",
    )
    # equs4v: ∀ x ( x = y → φ ) → ∃ x ( x = y ∧ φ )
    s2 = lb.ref(
        "s2",
        "∀ x ( x = y → φ ) → ∃ x ( x = y ∧ φ )",
        ref="equs4v",
        note="equs4v",
    )
    # sylbi: from biconditional s1 and implication s2
    res = lb.ref(
        "res",
        "[ y x φ → ∃ x ( x = y ∧ φ )",
        s1,
        s2,
        ref="sylbi",
        note="sylbi sb6, equs4v",
    )
    return lb.build(res)


def prove_sb4a(sys: System) -> Proof:
    """sb4a: ( [ t / x ] ∀ t φ → ∀ x ( x = t → φ ) ).
    Version of ~ sb4b with the antecedent removed via ~ pm2.61i .
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sb4a")
    # sbequ2: x = t → ( [ t / x ] ∀ t φ → ∀ t φ )
    s1 = lb.ref(
        "s1",
        "x = t → ( [ t x ∀ t φ → ∀ t φ )",
        ref="sbequ2",
        note="sbequ2",
    )
    # sps: ∀ x x = t → ( [ t / x ] ∀ t φ → ∀ t φ )
    s2 = lb.ref(
        "s2",
        "∀ x x = t → ( [ t x ∀ t φ → ∀ t φ )",
        s1,
        ref="sps",
        note="sps sbequ2",
    )
    # axc11r: ∀ x x = t → ( ∀ t φ → ∀ x φ )
    s3 = lb.ref(
        "s3",
        "∀ x x = t → ( ∀ t φ → ∀ x φ )",
        ref="axc11r",
        note="axc11r",
    )
    # ala1: ∀ x φ → ∀ x ( x = t → φ )
    s4 = lb.ref(
        "s4",
        "∀ x φ → ∀ x ( x = t → φ )",
        ref="ala1",
        note="ala1",
    )
    # syl6: ∀ x x = t → ( ∀ t φ → ∀ x ( x = t → φ ) )
    s5 = lb.ref(
        "s5",
        "∀ x x = t → ( ∀ t φ → ∀ x ( x = t → φ ) )",
        s3,
        s4,
        ref="syl6",
        note="syl6 axc11r, ala1",
    )
    # syld: ∀ x x = t → ( [ t / x ] ∀ t φ → ∀ x ( x = t → φ ) )
    s6 = lb.ref(
        "s6",
        "∀ x x = t → ( [ t x ∀ t φ → ∀ x ( x = t → φ ) )",
        s2,
        s5,
        ref="syld",
        note="syld sps, syl6",
    )
    # sb4b: ¬ ∀ x x = t → ( [ t / x ] ∀ t φ ↔ ∀ x ( x = t → ∀ t φ ) )
    s7 = lb.ref(
        "s7",
        "¬ ∀ x x = t → ( [ t x ∀ t φ ↔ ∀ x ( x = t → ∀ t φ ) )",
        ref="sb4b",
        note="sb4b",
    )
    # sp: ∀ t φ → φ
    s8 = lb.ref(
        "s8",
        "∀ t φ → φ",
        ref="sp",
        note="sp",
    )
    # imim2i: ( x = t → ∀ t φ ) → ( x = t → φ )
    s9 = lb.ref(
        "s9",
        "( x = t → ∀ t φ ) → ( x = t → φ )",
        s8,
        ref="imim2i",
        note="imim2i sp",
    )
    # alimi: ∀ x ( x = t → ∀ t φ ) → ∀ x ( x = t → φ )
    s10 = lb.ref(
        "s10",
        "∀ x ( x = t → ∀ t φ ) → ∀ x ( x = t → φ )",
        s9,
        ref="alimi",
        note="alimi imim2i",
    )
    # biimtrdi: ¬ ∀ x x = t → ( [ t / x ] ∀ t φ → ∀ x ( x = t → φ ) )
    s11 = lb.ref(
        "s11",
        "¬ ∀ x x = t → ( [ t x ∀ t φ → ∀ x ( x = t → φ ) )",
        s7,
        s10,
        ref="biimtrdi",
        note="biimtrdi sb4b, alimi",
    )
    # pm2.61i: ( [ t / x ] ∀ t φ → ∀ x ( x = t → φ ) )
    res = lb.ref(
        "res",
        "[ t x ∀ t φ → ∀ x ( x = t → φ )",
        s6,
        s11,
        ref="pm2.61i",
        note="pm2.61i",
    )
    return lb.build(res)


def prove_sb4av(sys: System) -> Proof:
    """sb4av: ( [ t x ∀ t φ → ∀ x ( x = t → φ ) ).
    Closed form of sbimi with sp as the antecedent, then
    expressed as substitution to universal quantification
    using sb6.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sb4av")
    # sp: ∀ t φ → φ
    s1 = lb.ref(
        "s1",
        "∀ t φ → φ",
        ref="sp",
        note="sp",
    )
    # sbimi: ( [ t x ∀ t φ → [ t x φ )
    s2 = lb.ref(
        "s2",
        "( [ t x ∀ t φ → [ t x φ )",
        s1,
        ref="sbimi",
        note="sbimi sp",
    )
    # sb6: [ t x φ ↔ ∀ x ( x = t → φ )
    s3 = lb.ref(
        "s3",
        "[ t x φ ↔ ∀ x ( x = t → φ )",
        ref="sb6",
        note="sb6",
    )
    # sylib: ( [ t x ∀ t φ → ∀ x ( x = t → φ ) )
    res = lb.ref(
        "res",
        "( [ t x ∀ t φ → ∀ x ( x = t → φ ) )",
        s2,
        s3,
        ref="sylib",
        note="sylib sbimi, sb6",
    )
    return lb.build(res)


def prove_sb4e(sys: System) -> Proof:
    """sb4e: [ y / x ] φ → ∀ x ( x = y → ∃ y φ ).

    If [ y / x ] φ holds, then for all x, if x = y then there exists
    y such that φ.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sb4e")
    s1 = lb.ref(
        "s1",
        "[ y x φ → ∃ x ( x = y ∧ φ )",
        ref="sb1",
        note="sb1",
    )
    s2 = lb.ref(
        "s2",
        "∃ x ( x = y ∧ φ ) → ∀ x ( x = y → ∃ y φ )",
        ref="equs5e",
        note="equs5e",
    )
    res = lb.ref(
        "res",
        "[ y x φ → ∀ x ( x = y → ∃ y φ )",
        s1,
        s2,
        ref="syl",
        note="syl sb1, equs5e",
    )
    return lb.build(res)


def prove_sb5(sys: System) -> Proof:
    """sb5: [ y x φ ↔ ∃ x ( x = y ∧ φ ).
    Substitution expressed in terms of existential quantifier
    and conjunction.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sb5")
    # Keep set.mm's source variable y here so its source DV contract (x,y)
    # is attached to the emitted assertion.
    s1 = lb.ref(
        "s1",
        "[ y x φ ↔ ∀ x ( x = y → φ )",
        ref="sb6",
        note="sb6",
    )
    # sbalex: ∃ x ( x = t ∧ φ ) ↔ ∀ x ( x = t → φ )
    s2 = lb.ref(
        "s2",
        "∃ x ( x = y ∧ φ ) ↔ ∀ x ( x = y → φ )",
        ref="sbalex",
        note="sbalex",
    )
    # bitr4i: [ t / x ] φ ↔ ∃ x ( x = t ∧ φ )
    res = lb.ref(
        "res",
        "[ y x φ ↔ ∃ x ( x = y ∧ φ )",
        s1,
        s2,
        ref="bitr4i",
        note="bitr4i sb6, sbalex",
    )
    return lb.build(res)


def prove_sbbiiev(sys: System) -> Proof:
    """sbbiiev: ( [ t x φ ↔ [ t x ψ ).
    Substitution distributes over a biconditional, given an equality
    hypothesis expressing that the biconditional holds under a variable
    assignment.
    """
    lb = ProofBuilder(sys, "sbbiiev")
    hyp = lb.hyp("sbbiiev.1", "( x = t → ( φ ↔ ψ ) )")
    # pm5.74i: from ( x = t → ( φ ↔ ψ ) ) to ( ( x = t → φ ) ↔ ( x = t → ψ ) )
    s1 = lb.ref(
        "s1",
        "( ( x = t → φ ) ↔ ( x = t → ψ ) )",
        hyp,
        ref="pm5.74i",
        note="pm5.74i",
    )
    # albii: universal quantification of the biconditional
    s2 = lb.ref(
        "s2",
        "( ∀ x ( x = t → φ ) ↔ ∀ x ( x = t → ψ ) )",
        s1,
        ref="albii",
        note="albii",
    )
    # sb6: substitution expressed via universal quantification
    s3 = lb.ref(
        "s3",
        "( [ t x φ ↔ ∀ x ( x = t → φ ) )",
        ref="sb6",
        note="sb6",
    )
    s4 = lb.ref(
        "s4",
        "( [ t x ψ ↔ ∀ x ( x = t → ψ ) )",
        ref="sb6",
        note="sb6",
    )
    # 3bitr4i: chain the three biconditionals
    res = lb.ref(
        "res",
        "( [ t x φ ↔ [ t x ψ )",
        s2,
        s3,
        s4,
        ref="3bitr4i",
        note="3bitr4i",
    )
    return lb.build(res)


def prove_sbbib(sys: System) -> Proof:
    """sbbib: ( ∀ y ( [ y / x ] φ ↔ ψ ) ↔ ∀ x ( φ ↔ [ x / y ] ψ ) ).
    Equivalence of two forms of substitution under a universal quantifier,
    using implicit substitution and cbvalv1.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbbib")
    hyp_y = lb.hyp("sbbib.y", "Ⅎ y φ")
    hyp_x = lb.hyp("sbbib.x", "Ⅎ x ψ")
    # nfs1v: Ⅎ x [ y x φ
    s_nfs1v_x = lb.ref(
        "s_nfs1v_x",
        "Ⅎ x [ y x φ",
        ref="nfs1v",
        note="nfs1v",
    )
    # nfbi with s_nfs1v_x and hyp_x: Ⅎ x ( [ y / x ] φ ↔ ψ )
    s_nfbi_x = lb.ref(
        "s_nfbi_x",
        "Ⅎ x ( [ y x φ ↔ ψ )",
        s_nfs1v_x,
        hyp_x,
        ref="nfbi",
        note="nfbi nfs1v, sbbib.x",
    )
    # nfs1v with x:=y, y:=x: Ⅎ y [ x y ψ
    s_nfs1v_y = lb.ref(
        "s_nfs1v_y",
        "Ⅎ y [ x y ψ",
        ref="nfs1v",
        note="nfs1v",
    )
    # nfbi with hyp_y and s_nfs1v_y: Ⅎ y ( φ ↔ [ x / y ] ψ )
    s_nfbi_y = lb.ref(
        "s_nfbi_y",
        "Ⅎ y ( φ ↔ [ x y ψ )",
        hyp_y,
        s_nfs1v_y,
        ref="nfbi",
        note="nfbi sbbib.y, nfs1v",
    )
    # sbequ12: x = y → ( φ ↔ [ y x φ )
    s_sbequ12 = lb.ref(
        "s_sbequ12",
        "x = y → ( φ ↔ [ y x φ )",
        ref="sbequ12",
        note="sbequ12",
    )
    # bicomd s_sbequ12: x = y → ( [ y x φ ↔ φ )
    s_bicomd1 = lb.ref(
        "s_bicomd1",
        "x = y → ( [ y x φ ↔ φ )",
        s_sbequ12,
        ref="bicomd",
        note="bicomd sbequ12",
    )
    # sbequ12r: x = y → ( [ x y ψ ↔ ψ )
    s_sbequ12r = lb.ref(
        "s_sbequ12r",
        "x = y → ( [ x y ψ ↔ ψ )",
        ref="sbequ12r",
        note="sbequ12r",
    )
    # bicomd s_sbequ12r: x = y → ( ψ ↔ [ x y ψ )
    s_bicomd2 = lb.ref(
        "s_bicomd2",
        "x = y → ( ψ ↔ [ x y ψ )",
        s_sbequ12r,
        ref="bicomd",
        note="bicomd sbequ12r",
    )
    # bibi12d s_bicomd1, s_bicomd2: x = y → ( ( [ y x φ ↔ ψ ) ↔ ( φ ↔ [ x y ψ ) )
    s_bibi12d = lb.ref(
        "s_bibi12d",
        "x = y → ( ( [ y x φ ↔ ψ ) ↔ ( φ ↔ [ x y ψ ) )",
        s_bicomd1,
        s_bicomd2,
        ref="bibi12d",
        note="bibi12d bicomd, bicomd",
    )
    # equcoms s_bibi12d: y = x → ( ( [ y x φ ↔ ψ ) ↔ ( φ ↔ [ x y ψ ) )
    s_equcoms = lb.ref(
        "s_equcoms",
        "y = x → ( ( [ y x φ ↔ ψ ) ↔ ( φ ↔ [ x y ψ ) )",
        s_bibi12d,
        ref="equcoms",
        note="equcoms bibi12d",
    )
    # cbvalv1 s_nfbi_x, s_nfbi_y, s_equcoms:
    #   ∀ y ( [ y / x ] φ ↔ ψ ) ↔ ∀ x ( φ ↔ [ x / y ] ψ )
    res = lb.ref(
        "res",
        "∀ y ( [ y x φ ↔ ψ ) ↔ ∀ x ( φ ↔ [ x y ψ )",
        s_nfbi_x,
        s_nfbi_y,
        s_equcoms,
        ref="cbvalv1",
        note="cbvalv1 nfbi, nfbi, equcoms",
    )
    return lb.build(res)


def prove_sbbibvv(sys: System) -> Proof:
    """sbbibvv: ( ∀ y ( [ y / x ] φ ↔ ψ ) ↔ ∀ x ( φ ↔ [ x / y ] ψ ) ).
    Closed form of sbbib, eliminating the Ⅎ hypotheses with nfv.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbbibvv")
    # nfv: F/ y φ
    s1 = lb.ref("s1", "F/ y φ", ref="nfv", note="nfv")
    # nfv: F/ x ψ
    s2 = lb.ref("s2", "F/ x ψ", ref="nfv", note="nfv")
    # sbbib s1, s2: ( ∀ y ( [ y / x ] φ ↔ ψ ) ↔ ∀ x ( φ ↔ [ x / y ] ψ ) )
    res = lb.ref(
        "res",
        "∀ y ( [ y x φ ↔ ψ ) ↔ ∀ x ( φ ↔ [ x y ψ )",
        s1,
        s2,
        ref="sbbib",
        note="sbbib nfv, nfv",
    )
    return lb.build(res)


def prove_sbiev(sys: System) -> Proof:
    """sbiev: ( [ y / x ] φ ↔ ψ ).
    Substitution with a biconditional equality hypothesis and
    a not-free hypothesis.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbiev")
    h1 = lb.hyp("sbiev.1", "Ⅎ x ψ")
    h2 = lb.hyp("sbiev.2", "( x = y → ( φ ↔ ψ ) )")
    # sbbiiev: ( x = y → ( φ ↔ ψ ) ) → ( [ y / x ] φ ↔ [ y / x ] ψ )
    s1 = lb.ref(
        "s1",
        "( [ y x φ ↔ [ y x ψ )",
        h2,
        ref="sbbiiev",
        note="sbbiiev",
    )
    # sbf: Ⅎ x ψ → ( [ y / x ] ψ ↔ ψ )
    s2 = lb.ref(
        "s2",
        "( [ y x ψ ↔ ψ )",
        h1,
        ref="sbf",
        note="sbf",
    )
    # bitri: ( [ y / x ] φ ↔ [ y / x ] ψ ) , ( [ y / x ] ψ ↔ ψ ) → ( [ y / x ] φ ↔ ψ )
    res = lb.ref(
        "res",
        "( [ y x φ ↔ ψ )",
        s1,
        s2,
        ref="bitri",
        note="bitri",
    )
    return lb.build(res)


def prove_sbiedw(sys: System) -> Proof:
    """sbiedw: φ → ( [ y / x ] ψ ↔ χ ).

    Conversion of implicit substitution to explicit substitution
    (deduction version of sbiev).  Version of sbied with a disjoint
    variable condition, requiring fewer axioms.
    (Contributed by NM, 30-Jun-1994.)
    (Revised by GG, 10-Jan-2024.)
    """
    lb = ProofBuilder(sys, "sbiedw")
    h1 = lb.hyp("sbiedw.1", "Ⅎ x φ")
    h2 = lb.hyp("sbiedw.2", "( φ → Ⅎ x χ )")
    h3 = lb.hyp("sbiedw.3", "( φ → ( x = y → ( ψ ↔ χ ) ) )")

    # sbrim: ( [ y / x ] ( φ → ψ ) ↔ ( φ → [ y / x ] ψ ) )
    s1 = lb.ref(
        "s1",
        "( [ y x ( φ → ψ ) ↔ ( φ → [ y x ψ ) )",
        h1,
        ref="sbrim",
        note="sbrim",
    )

    # nfim1: Ⅎ x ( φ → χ )
    s2 = lb.ref(
        "s2",
        "Ⅎ x ( φ → χ )",
        h1,
        h2,
        ref="nfim1",
        note="nfim1",
    )

    # com12: ( x = y ) → ( φ → ( ψ ↔ χ ) )
    s3 = lb.ref(
        "s3",
        "( x = y → ( φ → ( ψ ↔ χ ) ) )",
        h3,
        ref="com12",
        note="com12",
    )

    # pm5.74d: ( x = y ) → ( ( φ → ψ ) ↔ ( φ → χ ) )
    s4 = lb.ref(
        "s4",
        "( x = y → ( ( φ → ψ ) ↔ ( φ → χ ) ) )",
        s3,
        ref="pm5.74d",
        note="pm5.74d",
    )

    # sbiev: ( [ y / x ] ( φ → ψ ) ↔ ( φ → χ ) )
    s5 = lb.ref(
        "s5",
        "( [ y x ( φ → ψ ) ↔ ( φ → χ ) )",
        s2,
        s4,
        ref="sbiev",
        note="sbiev",
    )

    # bitr3i: ( ( φ → [ y / x ] ψ ) ↔ ( φ → χ ) )
    s6 = lb.ref(
        "s6",
        "( ( φ → [ y x ψ ) ↔ ( φ → χ ) )",
        s1,
        s5,
        ref="bitr3i",
        note="bitr3i",
    )

    # pm5.74ri: ( φ → ( [ y / x ] ψ ↔ χ ) )
    res = lb.ref(
        "res",
        "( φ → ( [ y x ψ ↔ χ ) )",
        s6,
        ref="pm5.74ri",
        note="pm5.74ri",
    )

    return lb.build(res)


def prove_sbied(sys: System) -> Proof:
    """sbied: φ → ( [ y / x ] ψ ↔ χ ).

    Conversion of implicit substitution to explicit substitution
    (deduction version of sbie).
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbied")
    h1 = lb.hyp("sbied.1", "Ⅎ x φ")
    h2 = lb.hyp("sbied.2", "( φ → Ⅎ x χ )")
    h3 = lb.hyp("sbied.3", "( φ → ( x = y → ( ψ ↔ χ ) ) )")

    # sbrim: ( [ y / x ] ( φ → ψ ) ↔ ( φ → [ y / x ] ψ ) )
    s1 = lb.ref(
        "s1",
        "( [ y x ( φ → ψ ) ↔ ( φ → [ y x ψ ) )",
        h1,
        ref="sbrim",
        note="sbrim sbied.1",
    )

    # nfim1: Ⅎ x ( φ → χ )
    s2 = lb.ref(
        "s2",
        "Ⅎ x ( φ → χ )",
        h1,
        h2,
        ref="nfim1",
        note="nfim1 sbied.1, sbied.2",
    )

    # com12: ( x = y ) → ( φ → ( ψ ↔ χ ) )
    s3 = lb.ref(
        "s3",
        "( x = y → ( φ → ( ψ ↔ χ ) ) )",
        h3,
        ref="com12",
        note="com12 sbied.3",
    )

    # pm5.74d: ( x = y ) → ( ( φ → ψ ) ↔ ( φ → χ ) )
    s4 = lb.ref(
        "s4",
        "( x = y → ( ( φ → ψ ) ↔ ( φ → χ ) ) )",
        s3,
        ref="pm5.74d",
        note="pm5.74d com12",
    )

    # sbie: ( [ y / x ] ( φ → ψ ) ↔ ( φ → χ ) )
    s5 = lb.ref(
        "s5",
        "( [ y x ( φ → ψ ) ↔ ( φ → χ ) )",
        s2,
        s4,
        ref="sbie",
        note="sbie nfim1, pm5.74d",
    )

    # bitr3i: ( ( φ → [ y / x ] ψ ) ↔ ( φ → χ ) )
    s6 = lb.ref(
        "s6",
        "( ( φ → [ y x ψ ) ↔ ( φ → χ ) )",
        s1,
        s5,
        ref="bitr3i",
        note="bitr3i sbrim, sbie",
    )

    # pm5.74ri: ( φ → ( [ y / x ] ψ ↔ χ ) )
    res = lb.ref(
        "res",
        "( φ → ( [ y x ψ ↔ χ ) )",
        s6,
        ref="pm5.74ri",
        note="pm5.74ri bitr3i",
    )

    return lb.build(res)


def prove_sbiedv(sys: System) -> Proof:
    """sbiedv: φ → ( [ y / x ] ψ ↔ χ ).

    Conversion of implicit substitution to explicit substitution
    (deduction version of sbied).
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbiedv")
    hyp = lb.hyp("sbiedv.1", "( ( φ ∧ x = y ) → ( ψ ↔ χ ) )")
    # nfv: Ⅎ x φ
    s_nfv = lb.ref("s_nfv", "Ⅎ x φ", ref="nfv", note="nfv")
    # nfvd: φ → Ⅎ x χ
    s_nfvd = lb.ref("s_nfvd", "φ → Ⅎ x χ", ref="nfvd", note="nfvd")
    # ex: φ → ( x = y → ( ψ ↔ χ ) )
    s_ex = lb.ref(
        "s_ex",
        "φ → ( x = y → ( ψ ↔ χ ) )",
        hyp,
        ref="ex",
        note="ex",
    )
    # sbied: φ → ( [ y / x ] ψ ↔ χ )
    res = lb.ref(
        "res",
        "φ → ( [ y / x ] ψ ↔ χ )",
        s_nfv,
        s_nfvd,
        s_ex,
        ref="sbied",
        note="sbied",
    )
    return lb.build(res)


def prove_2euex(sys: System) -> Proof:
    """2euex: ∃! x ∃ y φ → ∃ y ∃! x φ.

    If there exists a unique x such that there exists y such that φ,
    then there exists y such that there exists a unique x such that φ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "2euex")
    # df-eu: ∃! x ∃ y φ ↔ ( ∃ x ∃ y φ ∧ ∃* x ∃ y φ )
    s1 = lb.ref(
        "s1",
        "∃! x ∃ y φ ↔ ( ∃ x ∃ y φ ∧ ∃* x ∃ y φ )",
        ref="df-eu",
        note="df-eu",
    )
    # excom: ∃ x ∃ y φ ↔ ∃ y ∃ x φ
    s2 = lb.ref(
        "s2",
        "∃ x ∃ y φ ↔ ∃ y ∃ x φ",
        ref="excom",
        note="excom",
    )
    # nfe1: Ⅎ y ∃ y φ
    s3 = lb.ref(
        "s3",
        "Ⅎ y ∃ y φ",
        ref="nfe1",
        note="nfe1",
    )
    # nfmo(3): Ⅎ y ∃* x ∃ y φ
    s4 = lb.ref(
        "s4",
        "Ⅎ y ∃* x ∃ y φ",
        s3,
        ref="nfmo",
        note="nfmo nfe1",
    )
    # 19.8a: φ → ∃ y φ
    s5 = lb.ref(
        "s5",
        "φ → ∃ y φ",
        ref="19.8a",
        note="19.8a",
    )
    # moimi(5): ∃* x ∃ y φ → ∃* x φ
    s6 = lb.ref(
        "s6",
        "∃* x ∃ y φ → ∃* x φ",
        s5,
        ref="moimi",
        note="moimi 19.8a",
    )
    # moeu: ∃* x φ ↔ ( ∃ x φ → ∃! x φ )
    s7 = lb.ref(
        "s7",
        "∃* x φ ↔ ( ∃ x φ → ∃! x φ )",
        ref="moeu",
        note="moeu",
    )
    # sylib(6,7): ∃* x ∃ y φ → ( ∃ x φ → ∃! x φ )
    s8 = lb.ref(
        "s8",
        "∃* x ∃ y φ → ( ∃ x φ → ∃! x φ )",
        s6,
        s7,
        ref="sylib",
        note="sylib moimi, moeu",
    )
    # eximd(4,8): ∃* x ∃ y φ → ( ∃ y ∃ x φ → ∃ y ∃! x φ )
    s9 = lb.ref(
        "s9",
        "∃* x ∃ y φ → ( ∃ y ∃ x φ → ∃ y ∃! x φ )",
        s4,
        s8,
        ref="eximd",
        note="eximd nfmo, sylib",
    )
    # biimtrid(2,9): ∃* x ∃ y φ → ( ∃ x ∃ y φ → ∃ y ∃! x φ )
    s10 = lb.ref(
        "s10",
        "∃* x ∃ y φ → ( ∃ x ∃ y φ → ∃ y ∃! x φ )",
        s2,
        s9,
        ref="biimtrid",
        note="biimtrid excom, eximd",
    )
    # impcom(10): ( ∃ x ∃ y φ ∧ ∃* x ∃ y φ ) → ∃ y ∃! x φ
    s11 = lb.ref(
        "s11",
        "( ∃ x ∃ y φ ∧ ∃* x ∃ y φ ) → ∃ y ∃! x φ",
        s10,
        ref="impcom",
        note="impcom biimtrid",
    )
    # sylbi(1,11): ∃! x ∃ y φ → ∃ y ∃! x φ
    res = lb.ref(
        "res",
        "∃! x ∃ y φ → ∃ y ∃! x φ",
        s1,
        s11,
        ref="sylbi",
        note="sylbi df-eu, impcom",
    )
    return lb.build(res)


def prove_2exeu(sys: System) -> Proof:
    """2exeu: ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) → ∃! x ∃! y φ.

    Double existential uniqueness implies double unique existential quantification.
    (Contributed by NM, 3-Dec-2001.)  (Proof shortened by Mario Carneiro, 22-Dec-2016.)
    """
    lb = ProofBuilder(sys, "2exeu")
    # eumo: ∃! x ∃ y φ → ∃* x ∃ y φ
    s_eumo = lb.ref(
        "s_eumo",
        "∃! x ∃ y φ → ∃* x ∃ y φ",
        ref="eumo",
        note="eumo",
    )
    # euex: ∃! y φ → ∃ y φ
    s_euex = lb.ref(
        "s_euex",
        "∃! y φ → ∃ y φ",
        ref="euex",
        note="euex",
    )
    # moimi(euex): ∃* x ∃ y φ → ∃* x ∃! y φ
    s_moimi = lb.ref(
        "s_moimi",
        "∃* x ∃ y φ → ∃* x ∃! y φ",
        s_euex,
        ref="moimi",
        note="moimi euex",
    )
    # syl(eumo, moimi): ∃! x ∃ y φ → ∃* x ∃! y φ
    s_syl = lb.ref(
        "s_syl",
        "∃! x ∃ y φ → ∃* x ∃! y φ",
        s_eumo,
        s_moimi,
        ref="syl",
        note="syl eumo, moimi",
    )
    # 2euex: ∃! y ∃ x φ → ∃ x ∃! y φ
    s_2euex = lb.ref(
        "s_2euex",
        "∃! y ∃ x φ → ∃ x ∃! y φ",
        ref="2euex",
        note="2euex",
    )
    # anim12ci(syl, 2euex): (∃! x ∃ y φ ∧ ∃! y ∃ x φ) → (∃ x ∃! y φ ∧ ∃* x ∃! y φ)
    s_anim12ci = lb.ref(
        "s_anim12ci",
        "( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) → ( ∃ x ∃! y φ ∧ ∃* x ∃! y φ )",
        s_syl,
        s_2euex,
        ref="anim12ci",
        note="anim12ci syl, 2euex",
    )
    # df-eu: ∃! x ∃! y φ ↔ (∃ x ∃! y φ ∧ ∃* x ∃! y φ)
    s_df_eu = lb.ref(
        "s_df_eu",
        "∃! x ∃! y φ ↔ ( ∃ x ∃! y φ ∧ ∃* x ∃! y φ )",
        ref="df-eu",
        note="df-eu",
    )
    # sylibr(anim12ci, df-eu): (∃! x ∃ y φ ∧ ∃! y ∃ x φ) → ∃! x ∃! y φ
    res = lb.ref(
        "res",
        "( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) → ∃! x ∃! y φ",
        s_anim12ci,
        s_df_eu,
        ref="sylibr",
        note="sylibr anim12ci, df-eu",
    )
    return lb.build(res)


def prove_2exeuv(sys: System) -> Proof:
    """2exeuv: ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) → ∃! x ∃! y φ.

    Double existential uniqueness implies double unique existential quantification.
    Weak version of 2exeu using 2euexv instead of 2euex.
    (Contributed by NM, 3-Dec-2001.)  (Proof shortened by Mario Carneiro, 22-Dec-2016.)
    """
    lb = ProofBuilder(sys, "2exeuv")
    # eumo: ∃! x ∃ y φ → ∃* x ∃ y φ
    s_eumo = lb.ref(
        "s_eumo",
        "∃! x ∃ y φ → ∃* x ∃ y φ",
        ref="eumo",
        note="eumo",
    )
    # euex: ∃! y φ → ∃ y φ
    s_euex = lb.ref(
        "s_euex",
        "∃! y φ → ∃ y φ",
        ref="euex",
        note="euex",
    )
    # moimi(euex): ∃* x ∃ y φ → ∃* x ∃! y φ
    s_moimi = lb.ref(
        "s_moimi",
        "∃* x ∃ y φ → ∃* x ∃! y φ",
        s_euex,
        ref="moimi",
        note="moimi euex",
    )
    # syl(eumo, moimi): ∃! x ∃ y φ → ∃* x ∃! y φ
    s_syl = lb.ref(
        "s_syl",
        "∃! x ∃ y φ → ∃* x ∃! y φ",
        s_eumo,
        s_moimi,
        ref="syl",
        note="syl eumo, moimi",
    )
    # 2euexv (with x,y swapped): ∃! y ∃ x φ → ∃ x ∃! y φ
    s_2euexv = lb.ref(
        "s_2euexv",
        "∃! y ∃ x φ → ∃ x ∃! y φ",
        ref="2euexv",
        note="2euexv",
    )
    # anim12ci(syl, 2euexv): (∃! x ∃ y φ ∧ ∃! y ∃ x φ) → (∃ x ∃! y φ ∧ ∃* x ∃! y φ)
    s_anim12ci = lb.ref(
        "s_anim12ci",
        "( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) → ( ∃ x ∃! y φ ∧ ∃* x ∃! y φ )",
        s_syl,
        s_2euexv,
        ref="anim12ci",
        note="anim12ci syl, 2euexv",
    )
    # df-eu: ∃! x ∃! y φ ↔ (∃ x ∃! y φ ∧ ∃* x ∃! y φ)
    s_df_eu = lb.ref(
        "s_df_eu",
        "∃! x ∃! y φ ↔ ( ∃ x ∃! y φ ∧ ∃* x ∃! y φ )",
        ref="df-eu",
        note="df-eu",
    )
    # sylibr(anim12ci, df-eu): (∃! x ∃ y φ ∧ ∃! y ∃ x φ) → ∃! x ∃! y φ
    res = lb.ref(
        "res",
        "( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) → ∃! x ∃! y φ",
        s_anim12ci,
        s_df_eu,
        ref="sylibr",
        note="sylibr anim12ci, df-eu",
    )
    return lb.build(res)


def prove_2euexv(sys: System) -> Proof:
    """2euexv: ∃! x ∃ y φ → ∃ y ∃! x φ.

    Weak version of 2euex using nfmov instead of nfmo.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "2euexv")
    # df-eu: ∃! x ∃ y φ ↔ ( ∃ x ∃ y φ ∧ ∃* x ∃ y φ )
    s1 = lb.ref(
        "s1",
        "∃! x ∃ y φ ↔ ( ∃ x ∃ y φ ∧ ∃* x ∃ y φ )",
        ref="df-eu",
        note="df-eu",
    )
    # excom: ∃ x ∃ y φ ↔ ∃ y ∃ x φ
    s2 = lb.ref(
        "s2",
        "∃ x ∃ y φ ↔ ∃ y ∃ x φ",
        ref="excom",
        note="excom",
    )
    # nfe1: Ⅎ y ∃ y φ
    s3 = lb.ref(
        "s3",
        "Ⅎ y ∃ y φ",
        ref="nfe1",
        note="nfe1",
    )
    # nfmov(3): Ⅎ y ∃* x ∃ y φ
    s4 = lb.ref(
        "s4",
        "Ⅎ y ∃* x ∃ y φ",
        s3,
        ref="nfmov",
        note="nfmov nfe1",
    )
    # 19.8a: φ → ∃ y φ
    s5 = lb.ref(
        "s5",
        "φ → ∃ y φ",
        ref="19.8a",
        note="19.8a",
    )
    # moimi(5): ∃* x ∃ y φ → ∃* x φ
    s6 = lb.ref(
        "s6",
        "∃* x ∃ y φ → ∃* x φ",
        s5,
        ref="moimi",
        note="moimi 19.8a",
    )
    # moeu: ∃* x φ ↔ ( ∃ x φ → ∃! x φ )
    s7 = lb.ref(
        "s7",
        "∃* x φ ↔ ( ∃ x φ → ∃! x φ )",
        ref="moeu",
        note="moeu",
    )
    # sylib(6,7): ∃* x ∃ y φ → ( ∃ x φ → ∃! x φ )
    s8 = lb.ref(
        "s8",
        "∃* x ∃ y φ → ( ∃ x φ → ∃! x φ )",
        s6,
        s7,
        ref="sylib",
        note="sylib moimi, moeu",
    )
    # eximd(4,8): ∃* x ∃ y φ → ( ∃ y ∃ x φ → ∃ y ∃! x φ )
    s9 = lb.ref(
        "s9",
        "∃* x ∃ y φ → ( ∃ y ∃ x φ → ∃ y ∃! x φ )",
        s4,
        s8,
        ref="eximd",
        note="eximd nfmov, sylib",
    )
    # biimtrid(2,9): ∃* x ∃ y φ → ( ∃ x ∃ y φ → ∃ y ∃! x φ )
    s10 = lb.ref(
        "s10",
        "∃* x ∃ y φ → ( ∃ x ∃ y φ → ∃ y ∃! x φ )",
        s2,
        s9,
        ref="biimtrid",
        note="biimtrid excom, eximd",
    )
    # impcom(10): ( ∃ x ∃ y φ ∧ ∃* x ∃ y φ ) → ∃ y ∃! x φ
    s11 = lb.ref(
        "s11",
        "( ∃ x ∃ y φ ∧ ∃* x ∃ y φ ) → ∃ y ∃! x φ",
        s10,
        ref="impcom",
        note="impcom biimtrid",
    )
    # sylbi(1,11): ∃! x ∃ y φ → ∃ y ∃! x φ
    res = lb.ref(
        "res",
        "∃! x ∃ y φ → ∃ y ∃! x φ",
        s1,
        s11,
        ref="sylbi",
        note="sylbi df-eu, impcom",
    )
    return lb.build(res)


def prove_2mo2(sys: System) -> Proof:
    """2mo2: ( ∃* x ∃ y φ ∧ ∃* y ∃ x φ ) ↔ ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ).
    Two ways of expressing "there exists at most one ordered pair
    such that φ(x, y) holds".  See also 2mo.  This is the analogue
    of 2eu4 for existential uniqueness.
    (Contributed by Wolf Lammen, 26-Oct-2019.)
    Reduce dependencies on axioms.  (Revised by Wolf Lammen, 3-Jan-2023.)
    """
    lb = ProofBuilder(sys, "2mo2")
    # exdistrv
    s1 = lb.ref(
        "s1",
        "∃ z ∃ w ( ∀ x ( ∃ y φ → x = z ) ∧ ∀ y ( ∃ x φ → y = w ) ) ↔ ( ∃ z ∀ x ( ∃ y φ → x = z ) ∧ ∃ w ∀ y ( ∃ x φ → y = w ) )",
        ref="exdistrv",
        note="exdistrv",
    )
    # jcab
    s2 = lb.ref(
        "s2",
        "( φ → ( x = z ∧ y = w ) ) ↔ ( ( φ → x = z ) ∧ ( φ → y = w ) )",
        ref="jcab",
        note="jcab",
    )
    # 2albii with s2
    s3 = lb.ref(
        "s3",
        "∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) ↔ ∀ x ∀ y ( ( φ → x = z ) ∧ ( φ → y = w ) )",
        s2,
        ref="2albii",
        note="2albii jcab",
    )
    # 19.26-2
    s4 = lb.ref(
        "s4",
        "∀ x ∀ y ( ( φ → x = z ) ∧ ( φ → y = w ) ) ↔ ( ∀ x ∀ y ( φ → x = z ) ∧ ∀ x ∀ y ( φ → y = w ) )",
        ref="19.26-2",
        note="19.26-2",
    )
    # 19.23v
    s5 = lb.ref(
        "s5",
        "∀ y ( φ → x = z ) ↔ ( ∃ y φ → x = z )",
        ref="19.23v",
        note="19.23v",
    )
    # albii with s5
    s6 = lb.ref(
        "s6",
        "∀ x ∀ y ( φ → x = z ) ↔ ∀ x ( ∃ y φ → x = z )",
        s5,
        ref="albii",
        note="albii 19.23v",
    )
    # alcom
    s7 = lb.ref(
        "s7",
        "∀ x ∀ y ( φ → y = w ) ↔ ∀ y ∀ x ( φ → y = w )",
        ref="alcom",
        note="alcom",
    )
    # 19.23v
    s8 = lb.ref(
        "s8",
        "∀ x ( φ → y = w ) ↔ ( ∃ x φ → y = w )",
        ref="19.23v",
        note="19.23v",
    )
    # albii with s8
    s9 = lb.ref(
        "s9",
        "∀ y ∀ x ( φ → y = w ) ↔ ∀ y ( ∃ x φ → y = w )",
        s8,
        ref="albii",
        note="albii 19.23v",
    )
    # bitri s7, s9
    s10 = lb.ref(
        "s10",
        "∀ x ∀ y ( φ → y = w ) ↔ ∀ y ( ∃ x φ → y = w )",
        s7,
        s9,
        ref="bitri",
        note="bitri alcom, albii",
    )
    # anbi12i s6, s10
    s11 = lb.ref(
        "s11",
        "( ∀ x ∀ y ( φ → x = z ) ∧ ∀ x ∀ y ( φ → y = w ) ) ↔ ( ∀ x ( ∃ y φ → x = z ) ∧ ∀ y ( ∃ x φ → y = w ) )",
        s6,
        s10,
        ref="anbi12i",
        note="anbi12i",
    )
    # 3bitri s3, s4, s11
    s12 = lb.ref(
        "s12",
        "∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) ↔ ( ∀ x ( ∃ y φ → x = z ) ∧ ∀ y ( ∃ x φ → y = w ) )",
        s3,
        s4,
        s11,
        ref="3bitri",
        note="3bitri 2albii, 19.26-2, anbi12i",
    )
    # 2exbii s12
    s13 = lb.ref(
        "s13",
        "∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) ↔ ∃ z ∃ w ( ∀ x ( ∃ y φ → x = z ) ∧ ∀ y ( ∃ x φ → y = w ) )",
        s12,
        ref="2exbii",
        note="2exbii 3bitri",
    )
    # dfmo for E* x E. y ph
    s14 = lb.ref(
        "s14",
        "∃* x ∃ y φ ↔ ∃ z ∀ x ( ∃ y φ → x = z )",
        ref="dfmo",
        note="dfmo",
    )
    # dfmo for E* y E. x ph
    s15 = lb.ref(
        "s15",
        "∃* y ∃ x φ ↔ ∃ w ∀ y ( ∃ x φ → y = w )",
        ref="dfmo",
        note="dfmo",
    )
    # anbi12i s14, s15
    s16 = lb.ref(
        "s16",
        "( ∃* x ∃ y φ ∧ ∃* y ∃ x φ ) ↔ ( ∃ z ∀ x ( ∃ y φ → x = z ) ∧ ∃ w ∀ y ( ∃ x φ → y = w ) )",
        s14,
        s15,
        ref="anbi12i",
        note="anbi12i dfmo, dfmo",
    )
    # 3bitr4ri s1, s13, s16
    res = lb.ref(
        "res",
        "( ∃* x ∃ y φ ∧ ∃* y ∃ x φ ) ↔ ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) )",
        s1,
        s13,
        s16,
        ref="3bitr4ri",
        note="3bitr4ri exdistrv, 2exbii, anbi12i",
    )
    return lb.build(res)


def prove_2mo(sys: System) -> Proof:
    """2mo: ( ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) ) ↔ ( ∀ x ∀ y ∀ z ∀ w ( ( φ ∧ [ z / x ] [ w / y ] φ ) → ( x = z ∧ y = w ) ) ).

    Two ways of expressing "there exists at most one ordered pair
    such that φ(x, y) holds".  See also 2mo2.
    (Contributed by NM, 2-Feb-2005.)  (Revised by Mario Carneiro,
    17-Oct-2016.)  (Proof shortened by Wolf Lammen, 2-Nov-2019.)
    """
    lb = ProofBuilder(sys, "2mo")

    # 1. 2mo2: ( ∃* x ∃ y φ ∧ ∃* y ∃ x φ ) ↔ ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) )
    s1 = lb.ref(
        "s1",
        "( ∃* x ∃ y φ ∧ ∃* y ∃ x φ ) ↔ ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) )",
        ref="2mo2",
        note="2mo2",
    )

    # 2. nfmo1: Ⅎ x ∃* x ∃ y φ
    s2 = lb.ref(
        "s2",
        "Ⅎ x ∃* x ∃ y φ",
        ref="nfmo1",
        note="nfmo1",
    )

    # 3. nfe1: Ⅎ x ∃ x φ
    s3 = lb.ref(
        "s3",
        "Ⅎ x ∃ x φ",
        ref="nfe1",
        note="nfe1",
    )

    # 4. nfmov with s3: Ⅎ x ∃* y ∃ x φ
    s4 = lb.ref(
        "s4",
        "Ⅎ x ∃* y ∃ x φ",
        s3,
        ref="nfmov",
        note="nfmov nfe1",
    )

    # 5. nfan s2, s4: Ⅎ x ( ∃* x ∃ y φ ∧ ∃* y ∃ x φ )
    s5 = lb.ref(
        "s5",
        "Ⅎ x ( ∃* x ∃ y φ ∧ ∃* y ∃ x φ )",
        s2,
        s4,
        ref="nfan",
        note="nfan nfmo1, nfmov",
    )

    # 6. nfe1: Ⅎ y ∃ y φ
    s6 = lb.ref(
        "s6",
        "Ⅎ y ∃ y φ",
        ref="nfe1",
        note="nfe1",
    )

    # 7. nfmov with s6: Ⅎ y ∃* x ∃ y φ
    s7 = lb.ref(
        "s7",
        "Ⅎ y ∃* x ∃ y φ",
        s6,
        ref="nfmov",
        note="nfmov nfe1",
    )

    # 8. nfmo1: Ⅎ y ∃* y ∃ x φ
    s8 = lb.ref(
        "s8",
        "Ⅎ y ∃* y ∃ x φ",
        ref="nfmo1",
        note="nfmo1",
    )

    # 9. nfan s7, s8: Ⅎ y ( ∃* x ∃ y φ ∧ ∃* y ∃ x φ )
    s9 = lb.ref(
        "s9",
        "Ⅎ y ( ∃* x ∃ y φ ∧ ∃* y ∃ x φ )",
        s7,
        s8,
        ref="nfan",
        note="nfan nfmov, nfmo1",
    )

    # 10. 19.8a: φ → ∃ y φ
    s10 = lb.ref(
        "s10",
        "φ → ∃ y φ",
        ref="19.8a",
        note="19.8a",
    )

    # 11. spsbe: [ w / y ] φ → ∃ y φ
    s11 = lb.ref(
        "s11",
        "[ w / y ] φ → ∃ y φ",
        ref="spsbe",
        note="spsbe",
    )

    # 12. sbimi with s11: [ z / x ] [ w / y ] φ → [ z / x ] ∃ y φ
    s12 = lb.ref(
        "s12",
        "[ z / x ] [ w / y ] φ → [ z / x ] ∃ y φ",
        s11,
        ref="sbimi",
        note="sbimi spsbe",
    )

    # 13. nfv: Ⅎ z ∃ y φ
    s13 = lb.ref(
        "s13",
        "Ⅎ z ∃ y φ",
        ref="nfv",
        note="nfv",
    )

    # 14. mo3 with s13: ∃* x ∃ y φ ↔ ∀ x ∀ z ( ( ∃ y φ ∧ [ z / x ] ∃ y φ ) → x = z )
    s14 = lb.ref(
        "s14",
        "∃* x ∃ y φ ↔ ∀ x ∀ z ( ( ∃ y φ ∧ [ z / x ] ∃ y φ ) → x = z )",
        s13,
        ref="mo3",
        note="mo3 nfv",
    )

    # 15. biimpi with s14: ∃* x ∃ y φ → ∀ x ∀ z ( ( ∃ y φ ∧ [ z / x ] ∃ y φ ) → x = z )
    s15 = lb.ref(
        "s15",
        "∃* x ∃ y φ → ∀ x ∀ z ( ( ∃ y φ ∧ [ z / x ] ∃ y φ ) → x = z )",
        s14,
        ref="biimpi",
        note="biimpi mo3",
    )

    # 16. 19.21bbi with s15: ∃* x ∃ y φ → ( ( ∃ y φ ∧ [ z / x ] ∃ y φ ) → x = z )
    s16 = lb.ref(
        "s16",
        "∃* x ∃ y φ → ( ( ∃ y φ ∧ [ z / x ] ∃ y φ ) → x = z )",
        s15,
        ref="19.21bbi",
        note="19.21bbi biimpi",
    )

    # 17. syl2ani s10, s12, s16: ∃* x ∃ y φ → ( ( φ ∧ [ z / x ] [ w / y ] φ ) → x = z )
    s17 = lb.ref(
        "s17",
        "∃* x ∃ y φ → ( ( φ ∧ [ z / x ] [ w / y ] φ ) → x = z )",
        s10,
        s12,
        s16,
        ref="syl2ani",
        note="syl2ani 19.8a, sbimi, 19.21bbi",
    )

    # 18. 19.8a: φ → ∃ x φ
    s18 = lb.ref(
        "s18",
        "φ → ∃ x φ",
        ref="19.8a",
        note="19.8a",
    )

    # 19. sbcom2: [ z / x ] [ w / y ] φ ↔ [ w / y ] [ z / x ] φ
    s19 = lb.ref(
        "s19",
        "[ z / x ] [ w / y ] φ ↔ [ w / y ] [ z / x ] φ",
        ref="sbcom2",
        note="sbcom2",
    )

    # 20. spsbe: [ z / x ] φ → ∃ x φ
    s20 = lb.ref(
        "s20",
        "[ z / x ] φ → ∃ x φ",
        ref="spsbe",
        note="spsbe",
    )

    # 21. sbimi with s20: [ w / y ] [ z / x ] φ → [ w / y ] ∃ x φ
    s21 = lb.ref(
        "s21",
        "[ w / y ] [ z / x ] φ → [ w / y ] ∃ x φ",
        s20,
        ref="sbimi",
        note="sbimi spsbe",
    )

    # 22. sylbi s19, s21: [ z / x ] [ w / y ] φ → [ w / y ] ∃ x φ
    s22 = lb.ref(
        "s22",
        "[ z / x ] [ w / y ] φ → [ w / y ] ∃ x φ",
        s19,
        s21,
        ref="sylbi",
        note="sylbi sbcom2, sbimi",
    )

    # 23. nfv: Ⅎ w ∃ x φ
    s23 = lb.ref(
        "s23",
        "Ⅎ w ∃ x φ",
        ref="nfv",
        note="nfv",
    )

    # 24. mo3 with s23: ∃* y ∃ x φ ↔ ∀ y ∀ w ( ( ∃ x φ ∧ [ w / y ] ∃ x φ ) → y = w )
    s24 = lb.ref(
        "s24",
        "∃* y ∃ x φ ↔ ∀ y ∀ w ( ( ∃ x φ ∧ [ w / y ] ∃ x φ ) → y = w )",
        s23,
        ref="mo3",
        note="mo3 nfv",
    )

    # 25. biimpi with s24: ∃* y ∃ x φ → ∀ y ∀ w ( ( ∃ x φ ∧ [ w / y ] ∃ x φ ) → y = w )
    s25 = lb.ref(
        "s25",
        "∃* y ∃ x φ → ∀ y ∀ w ( ( ∃ x φ ∧ [ w / y ] ∃ x φ ) → y = w )",
        s24,
        ref="biimpi",
        note="biimpi mo3",
    )

    # 26. 19.21bbi with s25: ∃* y ∃ x φ → ( ( ∃ x φ ∧ [ w / y ] ∃ x φ ) → y = w )
    s26 = lb.ref(
        "s26",
        "∃* y ∃ x φ → ( ( ∃ x φ ∧ [ w / y ] ∃ x φ ) → y = w )",
        s25,
        ref="19.21bbi",
        note="19.21bbi biimpi",
    )

    # 27. syl2ani s18, s22, s26: ∃* y ∃ x φ → ( ( φ ∧ [ z / x ] [ w / y ] φ ) → y = w )
    s27 = lb.ref(
        "s27",
        "∃* y ∃ x φ → ( ( φ ∧ [ z / x ] [ w / y ] φ ) → y = w )",
        s18,
        s22,
        s26,
        ref="syl2ani",
        note="syl2ani 19.8a, sylbi, 19.21bbi",
    )

    # 28. anim12ii s17, s27: ( ∃* x ∃ y φ ∧ ∃* y ∃ x φ ) → ( ( φ ∧ [ z / x ] [ w / y ] φ ) → ( x = z ∧ y = w ) )
    s28 = lb.ref(
        "s28",
        "( ∃* x ∃ y φ ∧ ∃* y ∃ x φ ) → ( ( φ ∧ [ z / x ] [ w / y ] φ ) → ( x = z ∧ y = w ) )",
        s17,
        s27,
        ref="anim12ii",
        note="anim12ii syl2ani, syl2ani",
    )

    # 29. alrimi s9, s28: ( ∃* x ∃ y φ ∧ ∃* y ∃ x φ ) → ∀ y ( ( φ ∧ [ z / x ] [ w / y ] φ ) → ( x = z ∧ y = w ) )
    s29 = lb.ref(
        "s29",
        "( ∃* x ∃ y φ ∧ ∃* y ∃ x φ ) → ∀ y ( ( φ ∧ [ z / x ] [ w / y ] φ ) → ( x = z ∧ y = w ) )",
        s9,
        s28,
        ref="alrimi",
        note="alrimi nfan, anim12ii",
    )

    # 30. alrimi s5, s29: ( ∃* x ∃ y φ ∧ ∃* y ∃ x φ ) → ∀ x ∀ y ( ( φ ∧ [ z / x ] [ w / y ] φ ) → ( x = z ∧ y = w ) )
    s30 = lb.ref(
        "s30",
        "( ∃* x ∃ y φ ∧ ∃* y ∃ x φ ) → ∀ x ∀ y ( ( φ ∧ [ z / x ] [ w / y ] φ ) → ( x = z ∧ y = w ) )",
        s5,
        s29,
        ref="alrimi",
        note="alrimi nfan, alrimi",
    )

    # 31. alrimivv with s30: ( ∃* x ∃ y φ ∧ ∃* y ∃ x φ ) → ∀ z ∀ w ∀ x ∀ y ( ( φ ∧ [ z / x ] [ w / y ] φ ) → ( x = z ∧ y = w ) )
    s31 = lb.ref(
        "s31",
        "( ∃* x ∃ y φ ∧ ∃* y ∃ x φ ) → ∀ z ∀ w ∀ x ∀ y ( ( φ ∧ [ z / x ] [ w / y ] φ ) → ( x = z ∧ y = w ) )",
        s30,
        ref="alrimivv",
        note="alrimivv alrimi",
    )

    # 32. sylbir s1, s31: ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) → ∀ z ∀ w ∀ x ∀ y ( ( φ ∧ [ z / x ] [ w / y ] φ ) → ( x = z ∧ y = w ) )
    s32 = lb.ref(
        "s32",
        "∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) → ∀ z ∀ w ∀ x ∀ y ( ( φ ∧ [ z / x ] [ w / y ] φ ) → ( x = z ∧ y = w ) )",
        s1,
        s31,
        ref="sylbir",
        note="sylbir 2mo2, alrimivv",
    )

    # 33. nfs1v: Ⅎ x [ z / x ] [ w / y ] φ
    s33 = lb.ref(
        "s33",
        "Ⅎ x [ z / x ] [ w / y ] φ",
        ref="nfs1v",
        note="nfs1v",
    )

    # 34. nfs1v: Ⅎ y [ w / y ] φ
    s34 = lb.ref(
        "s34",
        "Ⅎ y [ w / y ] φ",
        ref="nfs1v",
        note="nfs1v",
    )

    # 35. nfsbv with s34: Ⅎ y [ z / x ] [ w / y ] φ
    s35 = lb.ref(
        "s35",
        "Ⅎ y [ z / x ] [ w / y ] φ",
        s34,
        ref="nfsbv",
        note="nfsbv nfs1v",
    )

    # 36. pm3.21: [ z / x ] [ w / y ] φ → ( φ → ( φ ∧ [ z / x ] [ w / y ] φ ) )
    s36 = lb.ref(
        "s36",
        "[ z / x ] [ w / y ] φ → ( φ → ( φ ∧ [ z / x ] [ w / y ] φ ) )",
        ref="pm3.21",
        note="pm3.21",
    )

    # 37. imim1d with s36: [ z / x ] [ w / y ] φ → ( ( ( φ ∧ [ z / x ] [ w / y ] φ ) → ( x = z ∧ y = w ) ) → ( φ → ( x = z ∧ y = w ) ) )
    s37 = lb.ref(
        "s37",
        "[ z / x ] [ w / y ] φ → ( ( ( φ ∧ [ z / x ] [ w / y ] φ ) → ( x = z ∧ y = w ) ) → ( φ → ( x = z ∧ y = w ) ) )",
        s36,
        ref="imim1d",
        note="imim1d pm3.21",
    )

    # 38. alimd s35, s37: [ z / x ] [ w / y ] φ → ( ∀ y ( ( φ ∧ [ z / x ] [ w / y ] φ ) → ( x = z ∧ y = w ) ) → ∀ y ( φ → ( x = z ∧ y = w ) ) )
    s38 = lb.ref(
        "s38",
        "[ z / x ] [ w / y ] φ → ( ∀ y ( ( φ ∧ [ z / x ] [ w / y ] φ ) → ( x = z ∧ y = w ) ) → ∀ y ( φ → ( x = z ∧ y = w ) ) )",
        s35,
        s37,
        ref="alimd",
        note="alimd nfsbv, imim1d",
    )

    # 39. alimd s33, s38: [ z / x ] [ w / y ] φ → ( ∀ x ∀ y ( ( φ ∧ [ z / x ] [ w / y ] φ ) → ( x = z ∧ y = w ) ) → ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) )
    s39 = lb.ref(
        "s39",
        "[ z / x ] [ w / y ] φ → ( ∀ x ∀ y ( ( φ ∧ [ z / x ] [ w / y ] φ ) → ( x = z ∧ y = w ) ) → ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) )",
        s33,
        s38,
        ref="alimd",
        note="alimd nfs1v, alimd",
    )

    # 40. com12 with s39: ∀ x ∀ y ( ( φ ∧ [ z / x ] [ w / y ] φ ) → ( x = z ∧ y = w ) ) → ( [ z / x ] [ w / y ] φ → ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) )
    s40 = lb.ref(
        "s40",
        "∀ x ∀ y ( ( φ ∧ [ z / x ] [ w / y ] φ ) → ( x = z ∧ y = w ) ) → ( [ z / x ] [ w / y ] φ → ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) )",
        s39,
        ref="com12",
        note="com12 alimd",
    )

    # 41. aleximi with s40: ∀ w ∀ x ∀ y ( ( φ ∧ [ z / x ] [ w / y ] φ ) → ( x = z ∧ y = w ) ) → ( ∃ w [ z / x ] [ w / y ] φ → ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) )
    s41 = lb.ref(
        "s41",
        "∀ w ∀ x ∀ y ( ( φ ∧ [ z / x ] [ w / y ] φ ) → ( x = z ∧ y = w ) ) → ( ∃ w [ z / x ] [ w / y ] φ → ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) )",
        s40,
        ref="aleximi",
        note="aleximi com12",
    )

    # 42. aleximi with s41: ∀ z ∀ w ∀ x ∀ y ( ( φ ∧ [ z / x ] [ w / y ] φ ) → ( x = z ∧ y = w ) ) → ( ∃ z ∃ w [ z / x ] [ w / y ] φ → ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) )
    s42 = lb.ref(
        "s42",
        "∀ z ∀ w ∀ x ∀ y ( ( φ ∧ [ z / x ] [ w / y ] φ ) → ( x = z ∧ y = w ) ) → ( ∃ z ∃ w [ z / x ] [ w / y ] φ → ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) )",
        s41,
        ref="aleximi",
        note="aleximi aleximi",
    )

    # 43. 2nexaln: ¬ ∃ x ∃ y φ ↔ ∀ x ∀ y ¬ φ
    s43 = lb.ref(
        "s43",
        "¬ ∃ x ∃ y φ ↔ ∀ x ∀ y ¬ φ",
        ref="2nexaln",
        note="2nexaln",
    )

    # 44. nfv: Ⅎ w φ
    s44 = lb.ref(
        "s44",
        "Ⅎ w φ",
        ref="nfv",
        note="nfv",
    )

    # 45. nfv: Ⅎ z φ
    s45 = lb.ref(
        "s45",
        "Ⅎ z φ",
        ref="nfv",
        note="nfv",
    )

    # 46. 2sb8ef s44, s45: ∃ x ∃ y φ ↔ ∃ z ∃ w [ z / x ] [ w / y ] φ
    s46 = lb.ref(
        "s46",
        "∃ x ∃ y φ ↔ ∃ z ∃ w [ z / x ] [ w / y ] φ",
        s44,
        s45,
        ref="2sb8ef",
        note="2sb8ef nfv, nfv",
    )

    # 47. xchnxbi s43, s46: ¬ ∃ z ∃ w [ z / x ] [ w / y ] φ ↔ ∀ x ∀ y ¬ φ
    s47 = lb.ref(
        "s47",
        "¬ ∃ z ∃ w [ z / x ] [ w / y ] φ ↔ ∀ x ∀ y ¬ φ",
        s43,
        s46,
        ref="xchnxbi",
        note="xchnxbi 2nexaln, 2sb8ef",
    )

    # 48. pm2.21: ¬ φ → ( φ → ( x = z ∧ y = w ) )
    s48 = lb.ref(
        "s48",
        "¬ φ → ( φ → ( x = z ∧ y = w ) )",
        ref="pm2.21",
        note="pm2.21",
    )

    # 49. 2alimi with s48: ∀ x ∀ y ¬ φ → ∀ x ∀ y ( φ → ( x = z ∧ y = w ) )
    s49 = lb.ref(
        "s49",
        "∀ x ∀ y ¬ φ → ∀ x ∀ y ( φ → ( x = z ∧ y = w ) )",
        s48,
        ref="2alimi",
        note="2alimi pm2.21",
    )

    # 50. 2eximi with s49: ∃ z ∃ w ∀ x ∀ y ¬ φ → ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) )
    s50 = lb.ref(
        "s50",
        "∃ z ∃ w ∀ x ∀ y ¬ φ → ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) )",
        s49,
        ref="2eximi",
        note="2eximi 2alimi",
    )

    # 51. 19.23bi with s50: ∃ w ∀ x ∀ y ¬ φ → ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) )
    s51 = lb.ref(
        "s51",
        "∃ w ∀ x ∀ y ¬ φ → ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) )",
        s50,
        ref="19.23bi",
        note="19.23bi 2eximi",
    )

    # 52. 19.23bi with s51: ∀ x ∀ y ¬ φ → ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) )
    s52 = lb.ref(
        "s52",
        "∀ x ∀ y ¬ φ → ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) )",
        s51,
        ref="19.23bi",
        note="19.23bi 19.23bi",
    )

    # 53. sylbi s47, s52: ¬ ∃ z ∃ w [ z / x ] [ w / y ] φ → ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) )
    s53 = lb.ref(
        "s53",
        "¬ ∃ z ∃ w [ z / x ] [ w / y ] φ → ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) )",
        s47,
        s52,
        ref="sylbi",
        note="sylbi xchnxbi, 19.23bi",
    )

    # 54. pm2.61d1 s42, s53: ∀ z ∀ w ∀ x ∀ y ( ( φ ∧ [ z / x ] [ w / y ] φ ) → ( x = z ∧ y = w ) ) → ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) )
    s54 = lb.ref(
        "s54",
        "∀ z ∀ w ∀ x ∀ y ( ( φ ∧ [ z / x ] [ w / y ] φ ) → ( x = z ∧ y = w ) ) → ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) )",
        s42,
        s53,
        ref="pm2.61d1",
        note="pm2.61d1 aleximi, sylbi",
    )

    # 55. impbii s32, s54: ( ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) ) ↔ ( ∀ z ∀ w ∀ x ∀ y ( ( φ ∧ [ z / x ] [ w / y ] φ ) → ( x = z ∧ y = w ) ) )
    s55 = lb.ref(
        "s55",
        "∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) ↔ ∀ z ∀ w ∀ x ∀ y ( ( φ ∧ [ z / x ] [ w / y ] φ ) → ( x = z ∧ y = w ) )",
        s32,
        s54,
        ref="impbii",
        note="impbii sylbir, pm2.61d1",
    )

    # 56. alrot4: ∀ z ∀ w ∀ x ∀ y ( ( φ ∧ [ z / x ] [ w / y ] φ ) → ( x = z ∧ y = w ) ) ↔ ∀ x ∀ y ∀ z ∀ w ( ( φ ∧ [ z / x ] [ w / y ] φ ) → ( x = z ∧ y = w ) )
    s56 = lb.ref(
        "s56",
        "∀ z ∀ w ∀ x ∀ y ( ( φ ∧ [ z / x ] [ w / y ] φ ) → ( x = z ∧ y = w ) ) ↔ ∀ x ∀ y ∀ z ∀ w ( ( φ ∧ [ z / x ] [ w / y ] φ ) → ( x = z ∧ y = w ) )",
        ref="alrot4",
        note="alrot4",
    )

    # 57. bitri s55, s56
    res = lb.ref(
        "res",
        "∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) ↔ ∀ x ∀ y ∀ z ∀ w ( ( φ ∧ [ z / x ] [ w / y ] φ ) → ( x = z ∧ y = w ) )",
        s55,
        s56,
        ref="bitri",
        note="bitri impbii, alrot4",
    )
    return lb.build(res)


def prove_2mos(sys: System) -> Proof:
    """2mos: ( ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) ) ↔ ( ∀ x ∀ y ∀ z ∀ w ( ( φ ∧ ψ ) → ( x = z ∧ y = w ) ) ).

    Variant of 2mo with a hypothesis in place of the substitution.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "2mos")
    hyp = lb.hyp("2mos.1", "( ( x = z ∧ y = w ) → ( φ ↔ ψ ) )")

    # 2mo: ( ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) ) ↔
    #      ( ∀ x ∀ y ∀ z ∀ w ( ( φ ∧ [ z / x ] [ w / y ] φ ) → ( x = z ∧ y = w ) ) )
    s1 = lb.ref(
        "s1",
        "∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) ↔ ∀ x ∀ y ∀ z ∀ w ( ( φ ∧ [ z / x ] [ w / y ] φ ) → ( x = z ∧ y = w ) )",
        ref="2mo",
        note="2mo",
    )

    # 2sbievw with 2mos.1: [ z / x ] [ w / y ] φ ↔ ψ
    s2 = lb.ref(
        "s2",
        "( [ z x [ w y φ ↔ ψ )",
        hyp,
        ref="2sbievw",
        note="2sbievw",
    )

    # anbi2i: ( φ ∧ [ z / x ] [ w / y ] φ ) ↔ ( φ ∧ ψ )
    s3 = lb.ref(
        "s3",
        "( ( φ ∧ [ z x [ w y φ ) ↔ ( φ ∧ ψ ) )",
        s2,
        ref="anbi2i",
        note="anbi2i",
    )

    # imbi1i: ( ( φ ∧ [ z / x ] [ w / y ] φ ) → ( x = z ∧ y = w ) ) ↔
    #         ( ( φ ∧ ψ ) → ( x = z ∧ y = w ) )
    s4 = lb.ref(
        "s4",
        "( ( ( φ ∧ [ z x [ w y φ ) → ( x = z ∧ y = w ) ) ↔ ( ( φ ∧ ψ ) → ( x = z ∧ y = w ) ) )",
        s3,
        ref="imbi1i",
        note="imbi1i",
    )

    # 2albii: ∀ z ∀ w ( ... ) ↔ ∀ z ∀ w ( ... )
    s5 = lb.ref(
        "s5",
        "( ∀ z ∀ w ( ( φ ∧ [ z x [ w y φ ) → ( x = z ∧ y = w ) ) ↔ ∀ z ∀ w ( ( φ ∧ ψ ) → ( x = z ∧ y = w ) ) )",
        s4,
        ref="2albii",
        note="2albii",
    )

    # 2albii: ∀ x ∀ y ∀ z ∀ w ( ... ) ↔ ∀ x ∀ y ∀ z ∀ w ( ... )
    s6 = lb.ref(
        "s6",
        "( ∀ x ∀ y ∀ z ∀ w ( ( φ ∧ [ z x [ w y φ ) → ( x = z ∧ y = w ) ) ↔ ∀ x ∀ y ∀ z ∀ w ( ( φ ∧ ψ ) → ( x = z ∧ y = w ) ) )",
        s5,
        ref="2albii",
        note="2albii",
    )

    # bitri s1, s6: final result
    res = lb.ref(
        "res",
        "∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) ↔ ∀ x ∀ y ∀ z ∀ w ( ( φ ∧ ψ ) → ( x = z ∧ y = w ) )",
        s1,
        s6,
        ref="bitri",
        note="bitri 2mo, 2albii",
    )
    return lb.build(res)


def prove_2moex(sys: System) -> Proof:
    """2moex: ∃* x ∃ y φ → ∀ y ∃* x φ.

    If there is at most one x such that there exists a y making φ true,
    then for all y, there is at most one x making φ true.
    (Contributed by NM, 19-Jan-2007.)
    """
    lb = ProofBuilder(sys, "2moex")

    # 19.8a: φ → ∃ y φ
    s1 = lb.ref(
        "s1",
        "φ → ∃ y φ",
        ref="19.8a",
        note="19.8a",
    )

    # moimi: ∃* x ∃ y φ → ∃* x φ
    s2 = lb.ref(
        "s2",
        "∃* x ∃ y φ → ∃* x φ",
        s1,
        ref="moimi",
        note="moimi 19.8a",
    )

    # nfe1: Ⅎ y ∃ y φ
    s3 = lb.ref(
        "s3",
        "Ⅎ y ∃ y φ",
        ref="nfe1",
        note="nfe1",
    )

    # nfmo: Ⅎ y ∃* x ∃ y φ
    s4 = lb.ref(
        "s4",
        "Ⅎ y ∃* x ∃ y φ",
        s3,
        ref="nfmo",
        note="nfmo nfe1",
    )

    # alrimi: (∃* x ∃ y φ) → ∀ y ∃* x φ
    res = lb.ref(
        "res",
        "∃* x ∃ y φ → ∀ y ∃* x φ",
        s4,
        s2,
        ref="alrimi",
        note="alrimi nfmo, moimi",
    )

    return lb.build(res)


def prove_2moexv(sys: System) -> Proof:
    """2moexv: ∃* x ∃ y φ → ∀ y ∃* x φ.

    If there is at most one x such that there exists a y making φ true,
    then for all y, there is at most one x making φ true.
    Variant of 2moex using nfmov instead of nfmo.
    (Contributed by NM, 19-Jan-2007.)
    """
    lb = ProofBuilder(sys, "2moexv")

    # nfe1: Ⅎ y ∃ y φ
    s1 = lb.ref(
        "s1",
        "Ⅎ y ∃ y φ",
        ref="nfe1",
        note="nfe1",
    )

    # nfmov: Ⅎ y ∃* x ∃ y φ
    s2 = lb.ref(
        "s2",
        "Ⅎ y ∃* x ∃ y φ",
        s1,
        ref="nfmov",
        note="nfmov nfe1",
    )

    # 19.8a: φ → ∃ y φ
    s3 = lb.ref(
        "s3",
        "φ → ∃ y φ",
        ref="19.8a",
        note="19.8a",
    )

    # moimi: ∃* x ∃ y φ → ∃* x φ
    s4 = lb.ref(
        "s4",
        "∃* x ∃ y φ → ∃* x φ",
        s3,
        ref="moimi",
        note="moimi 19.8a",
    )

    # alrimi: ∃* x ∃ y φ → ∀ y ∃* x φ
    res = lb.ref(
        "res",
        "∃* x ∃ y φ → ∀ y ∃* x φ",
        s2,
        s4,
        ref="alrimi",
        note="alrimi nfmov, moimi",
    )

    return lb.build(res)


def prove_2moswapv(sys: System) -> Proof:
    """2moswapv: ∀ x ∃* y φ → (∃* x ∃ y φ → ∃* y ∃ x φ).

    Swapping quantifiers under "at most one".
    (Contributed by NM, 19-Jan-2007.)
    """
    lb = ProofBuilder(sys, "2moswapv")

    # nfe1: Ⅎ y ∃ y φ
    s_nfe1_y = lb.ref(
        "s_nfe1_y",
        "Ⅎ y ∃ y φ",
        ref="nfe1",
        note="nfe1",
    )

    # nfmov nfe1: Ⅎ y ∃* x ∃ y φ
    s_nfmov_1 = lb.ref(
        "s_nfmov_1",
        "Ⅎ y ∃* x ∃ y φ",
        s_nfe1_y,
        ref="nfmov",
        note="nfmov nfe1",
    )

    # nfe1: Ⅎ x ∃ x (∃ y φ ∧ φ)
    s_nfe1_x = lb.ref(
        "s_nfe1_x",
        "Ⅎ x ∃ x (∃ y φ ∧ φ)",
        ref="nfe1",
        note="nfe1",
    )

    # nfmov nfe1: Ⅎ x ∃* y ∃ x (∃ y φ ∧ φ)
    s_nfmov_2 = lb.ref(
        "s_nfmov_2",
        "Ⅎ x ∃* y ∃ x (∃ y φ ∧ φ)",
        s_nfe1_x,
        ref="nfmov",
        note="nfmov nfe1",
    )

    # moexexlem with φ := ∃ y φ, ψ := φ:
    # (∃* x ∃ y φ ∧ ∀ x ∃* y φ) → ∃* y ∃ x (∃ y φ ∧ φ)
    s_moexexlem = lb.ref(
        "s_moexexlem",
        "(∃* x ∃ y φ ∧ ∀ x ∃* y φ) → ∃* y ∃ x (∃ y φ ∧ φ)",
        s_nfe1_y,
        s_nfmov_1,
        s_nfmov_2,
        ref="moexexlem",
        note="moexexlem nfe1, nfmov, nfmov",
    )

    # expcom: ∀ x ∃* y φ → (∃* x ∃ y φ → ∃* y ∃ x (∃ y φ ∧ φ))
    s_expcom = lb.ref(
        "s_expcom",
        "∀ x ∃* y φ → (∃* x ∃ y φ → ∃* y ∃ x (∃ y φ ∧ φ))",
        s_moexexlem,
        ref="expcom",
        note="expcom moexexlem",
    )

    # 19.8a: φ → ∃ y φ
    s_19_8a = lb.ref(
        "s_19_8a",
        "φ → ∃ y φ",
        ref="19.8a",
        note="19.8a",
    )

    # pm4.71ri: φ ↔ (∃ y φ ∧ φ)
    s_pm4_71ri = lb.ref(
        "s_pm4_71ri",
        "φ ↔ (∃ y φ ∧ φ)",
        s_19_8a,
        ref="pm4.71ri",
        note="pm4.71ri 19.8a",
    )

    # exbii: ∃ x φ ↔ ∃ x (∃ y φ ∧ φ)
    s_exbii = lb.ref(
        "s_exbii",
        "∃ x φ ↔ ∃ x (∃ y φ ∧ φ)",
        s_pm4_71ri,
        ref="exbii",
        note="exbii pm4.71ri",
    )

    # mobii: ∃* y ∃ x φ ↔ ∃* y ∃ x (∃ y φ ∧ φ)
    s_mobii = lb.ref(
        "s_mobii",
        "∃* y ∃ x φ ↔ ∃* y ∃ x (∃ y φ ∧ φ)",
        s_exbii,
        ref="mobii",
        note="mobii exbii",
    )

    # imbitrrdi: ∀ x ∃* y φ → (∃* x ∃ y φ → ∃* y ∃ x φ)
    res = lb.ref(
        "res",
        "∀ x ∃* y φ → (∃* x ∃ y φ → ∃* y ∃ x φ)",
        s_expcom,
        s_mobii,
        ref="imbitrrdi",
        note="imbitrrdi expcom, mobii",
    )

    return lb.build(res)


def prove_2moswap(sys: System) -> Proof:
    """2moswap: ∀ x ∃* y φ → (∃* x ∃ y φ → ∃* y ∃ x φ).

    Swapping quantifiers under "at most one".
    (Contributed by NM, 19-Jan-2007.)
    """
    lb = ProofBuilder(sys, "2moswap")

    # nfe1: Ⅎ y ∃ y φ
    s_nfe1_y = lb.ref(
        "s_nfe1_y",
        "Ⅎ y ∃ y φ",
        ref="nfe1",
        note="nfe1",
    )

    # moexex: (∃* x ∃ y φ ∧ ∀ x ∃* y φ) → ∃* y ∃ x (∃ y φ ∧ φ)
    s_moexex = lb.ref(
        "s_moexex",
        "(∃* x ∃ y φ ∧ ∀ x ∃* y φ) → ∃* y ∃ x (∃ y φ ∧ φ)",
        s_nfe1_y,
        ref="moexex",
        note="moexex nfe1",
    )

    # expcom: ∀ x ∃* y φ → (∃* x ∃ y φ → ∃* y ∃ x (∃ y φ ∧ φ))
    s_expcom = lb.ref(
        "s_expcom",
        "∀ x ∃* y φ → (∃* x ∃ y φ → ∃* y ∃ x (∃ y φ ∧ φ))",
        s_moexex,
        ref="expcom",
        note="expcom moexex",
    )

    # 19.8a: φ → ∃ y φ
    s_19_8a = lb.ref(
        "s_19_8a",
        "φ → ∃ y φ",
        ref="19.8a",
        note="19.8a",
    )

    # pm4.71ri: φ ↔ (∃ y φ ∧ φ)
    s_pm4_71ri = lb.ref(
        "s_pm4_71ri",
        "φ ↔ (∃ y φ ∧ φ)",
        s_19_8a,
        ref="pm4.71ri",
        note="pm4.71ri 19.8a",
    )

    # exbii: ∃ x φ ↔ ∃ x (∃ y φ ∧ φ)
    s_exbii = lb.ref(
        "s_exbii",
        "∃ x φ ↔ ∃ x (∃ y φ ∧ φ)",
        s_pm4_71ri,
        ref="exbii",
        note="exbii pm4.71ri",
    )

    # mobii: ∃* y ∃ x φ ↔ ∃* y ∃ x (∃ y φ ∧ φ)
    s_mobii = lb.ref(
        "s_mobii",
        "∃* y ∃ x φ ↔ ∃* y ∃ x (∃ y φ ∧ φ)",
        s_exbii,
        ref="mobii",
        note="mobii exbii",
    )

    # imbitrrdi: ∀ x ∃* y φ → (∃* x ∃ y φ → ∃* y ∃ x φ)
    res = lb.ref(
        "res",
        "∀ x ∃* y φ → (∃* x ∃ y φ → ∃* y ∃ x φ)",
        s_expcom,
        s_mobii,
        ref="imbitrrdi",
        note="imbitrrdi expcom, mobii",
    )

    return lb.build(res)


def prove_2eu1(sys: System) -> Proof:
    """2eu1: ∀ x ∃* y φ → ( ∃! x ∃! y φ ↔ ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) ).

    A condition under which the "naive" definition of double existential
    uniqueness matches the correct one.
    (Contributed by NM, 3-Dec-2001.)
    """
    lb = ProofBuilder(sys, "2eu1")

    # 2eu2ex: ∃! x ∃! y φ → ∃ x ∃ y φ
    s_2eu2ex = lb.ref(
        "s_2eu2ex",
        "∃! x ∃! y φ → ∃ x ∃ y φ",
        ref="2eu2ex",
        note="2eu2ex",
    )

    # moeu: ∃* y φ ↔ ( ∃ y φ → ∃! y φ )
    s_moeu = lb.ref(
        "s_moeu",
        "∃* y φ ↔ ( ∃ y φ → ∃! y φ )",
        ref="moeu",
        note="moeu",
    )

    # albii(moeu): ∀ x ∃* y φ ↔ ∀ x ( ∃ y φ → ∃! y φ )
    s_albii = lb.ref(
        "s_albii",
        "∀ x ∃* y φ ↔ ∀ x ( ∃ y φ → ∃! y φ )",
        s_moeu,
        ref="albii",
        note="albii moeu",
    )

    # euim: ( ∃ x ∃ y φ ∧ ∀ x ( ∃ y φ → ∃! y φ ) ) → ( ∃! x ∃! y φ → ∃! x ∃ y φ )
    s_euim = lb.ref(
        "s_euim",
        "( ∃ x ∃ y φ ∧ ∀ x ( ∃ y φ → ∃! y φ ) ) → ( ∃! x ∃! y φ → ∃! x ∃ y φ )",
        ref="euim",
        note="euim",
    )

    # sylan2b(albii, euim): ( ∃ x ∃ y φ ∧ ∀ x ∃* y φ ) → ( ∃! x ∃! y φ → ∃! x ∃ y φ )
    s_sylan2b = lb.ref(
        "s_sylan2b",
        "( ∃ x ∃ y φ ∧ ∀ x ∃* y φ ) → ( ∃! x ∃! y φ → ∃! x ∃ y φ )",
        s_albii,
        s_euim,
        ref="sylan2b",
        note="sylan2b albii, euim",
    )

    # ex(sylan2b): ∃ x ∃ y φ → ( ∀ x ∃* y φ → ( ∃! x ∃! y φ → ∃! x ∃ y φ ) )
    s_ex = lb.ref(
        "s_ex",
        "∃ x ∃ y φ → ( ∀ x ∃* y φ → ( ∃! x ∃! y φ → ∃! x ∃ y φ ) )",
        s_sylan2b,
        ref="ex",
        note="ex sylan2b",
    )

    # syl(2eu2ex, ex): ∃! x ∃! y φ → ( ∀ x ∃* y φ → ( ∃! x ∃! y φ → ∃! x ∃ y φ ) )
    s_syl = lb.ref(
        "s_syl",
        "∃! x ∃! y φ → ( ∀ x ∃* y φ → ( ∃! x ∃! y φ → ∃! x ∃ y φ ) )",
        s_2eu2ex,
        s_ex,
        ref="syl",
        note="syl 2eu2ex, ex",
    )

    # pm2.43b(syl): ∀ x ∃* y φ → ( ∃! x ∃! y φ → ∃! x ∃ y φ )
    s_pm2_43b = lb.ref(
        "s_pm2_43b",
        "∀ x ∃* y φ → ( ∃! x ∃! y φ → ∃! x ∃ y φ )",
        s_syl,
        ref="pm2.43b",
        note="pm2.43b syl",
    )

    # 2euswap: ∀ x ∃* y φ → ( ∃! x ∃ y φ → ∃! y ∃ x φ )
    s_2euswap = lb.ref(
        "s_2euswap",
        "∀ x ∃* y φ → ( ∃! x ∃ y φ → ∃! y ∃ x φ )",
        ref="2euswap",
        note="2euswap",
    )

    # syld(pm2.43b, 2euswap): ∀ x ∃* y φ → ( ∃! x ∃! y φ → ∃! y ∃ x φ )
    s_syld = lb.ref(
        "s_syld",
        "∀ x ∃* y φ → ( ∃! x ∃! y φ → ∃! y ∃ x φ )",
        s_pm2_43b,
        s_2euswap,
        ref="syld",
        note="syld pm2.43b, 2euswap",
    )

    # jcad(pm2.43b, syld): ∀ x ∃* y φ → ( ∃! x ∃! y φ → ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) )
    s_jcad = lb.ref(
        "s_jcad",
        "∀ x ∃* y φ → ( ∃! x ∃! y φ → ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) )",
        s_pm2_43b,
        s_syld,
        ref="jcad",
        note="jcad pm2.43b, syld",
    )

    # 2exeu: ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) → ∃! x ∃! y φ
    s_2exeu = lb.ref(
        "s_2exeu",
        "( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) → ∃! x ∃! y φ",
        ref="2exeu",
        note="2exeu",
    )

    # impbid1(jcad, 2exeu): ∀ x ∃* y φ → ( ∃! x ∃! y φ ↔ ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) )
    res = lb.ref(
        "res",
        "∀ x ∃* y φ → ( ∃! x ∃! y φ ↔ ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) )",
        s_jcad,
        s_2exeu,
        ref="impbid1",
        note="impbid1 jcad, 2exeu",
    )

    return lb.build(res)


def prove_2eu1v(sys: System) -> Proof:
    """2eu1v: ∀ x ∃* y φ → ( ∃! x ∃! y φ ↔ ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) ).

    Weak version of 2eu1 using 2euswapv instead of 2euswap and 2exeuv
    instead of 2exeu.
    (Contributed by NM, 3-Dec-2001.)
    """
    lb = ProofBuilder(sys, "2eu1v")

    # 2eu2ex: ∃! x ∃! y φ → ∃ x ∃ y φ
    s_2eu2ex = lb.ref(
        "s_2eu2ex",
        "∃! x ∃! y φ → ∃ x ∃ y φ",
        ref="2eu2ex",
        note="2eu2ex",
    )

    # moeu: ∃* y φ ↔ ( ∃ y φ → ∃! y φ )
    s_moeu = lb.ref(
        "s_moeu",
        "∃* y φ ↔ ( ∃ y φ → ∃! y φ )",
        ref="moeu",
        note="moeu",
    )

    # albii(moeu): ∀ x ∃* y φ ↔ ∀ x ( ∃ y φ → ∃! y φ )
    s_albii = lb.ref(
        "s_albii",
        "∀ x ∃* y φ ↔ ∀ x ( ∃ y φ → ∃! y φ )",
        s_moeu,
        ref="albii",
        note="albii moeu",
    )

    # euim: ( ∃ x ∃ y φ ∧ ∀ x ( ∃ y φ → ∃! y φ ) ) → ( ∃! x ∃! y φ → ∃! x ∃ y φ )
    s_euim = lb.ref(
        "s_euim",
        "( ∃ x ∃ y φ ∧ ∀ x ( ∃ y φ → ∃! y φ ) ) → ( ∃! x ∃! y φ → ∃! x ∃ y φ )",
        ref="euim",
        note="euim",
    )

    # sylan2b(albii, euim): ( ∃ x ∃ y φ ∧ ∀ x ∃* y φ ) → ( ∃! x ∃! y φ → ∃! x ∃ y φ )
    s_sylan2b = lb.ref(
        "s_sylan2b",
        "( ∃ x ∃ y φ ∧ ∀ x ∃* y φ ) → ( ∃! x ∃! y φ → ∃! x ∃ y φ )",
        s_albii,
        s_euim,
        ref="sylan2b",
        note="sylan2b albii, euim",
    )

    # ex(sylan2b): ∃ x ∃ y φ → ( ∀ x ∃* y φ → ( ∃! x ∃! y φ → ∃! x ∃ y φ ) )
    s_ex = lb.ref(
        "s_ex",
        "∃ x ∃ y φ → ( ∀ x ∃* y φ → ( ∃! x ∃! y φ → ∃! x ∃ y φ ) )",
        s_sylan2b,
        ref="ex",
        note="ex sylan2b",
    )

    # syl(2eu2ex, ex): ∃! x ∃! y φ → ( ∀ x ∃* y φ → ( ∃! x ∃! y φ → ∃! x ∃ y φ ) )
    s_syl = lb.ref(
        "s_syl",
        "∃! x ∃! y φ → ( ∀ x ∃* y φ → ( ∃! x ∃! y φ → ∃! x ∃ y φ ) )",
        s_2eu2ex,
        s_ex,
        ref="syl",
        note="syl 2eu2ex, ex",
    )

    # pm2.43b(syl): ∀ x ∃* y φ → ( ∃! x ∃! y φ → ∃! x ∃ y φ )
    s_pm2_43b = lb.ref(
        "s_pm2_43b",
        "∀ x ∃* y φ → ( ∃! x ∃! y φ → ∃! x ∃ y φ )",
        s_syl,
        ref="pm2.43b",
        note="pm2.43b syl",
    )

    # 2euswapv: ∀ x ∃* y φ → ( ∃! x ∃ y φ → ∃! y ∃ x φ )
    s_2euswapv = lb.ref(
        "s_2euswapv",
        "∀ x ∃* y φ → ( ∃! x ∃ y φ → ∃! y ∃ x φ )",
        ref="2euswapv",
        note="2euswapv",
    )

    # syld(pm2.43b, 2euswapv): ∀ x ∃* y φ → ( ∃! x ∃! y φ → ∃! y ∃ x φ )
    s_syld = lb.ref(
        "s_syld",
        "∀ x ∃* y φ → ( ∃! x ∃! y φ → ∃! y ∃ x φ )",
        s_pm2_43b,
        s_2euswapv,
        ref="syld",
        note="syld pm2.43b, 2euswapv",
    )

    # jcad(pm2.43b, syld): ∀ x ∃* y φ → ( ∃! x ∃! y φ → ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) )
    s_jcad = lb.ref(
        "s_jcad",
        "∀ x ∃* y φ → ( ∃! x ∃! y φ → ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) )",
        s_pm2_43b,
        s_syld,
        ref="jcad",
        note="jcad pm2.43b, syld",
    )

    # 2exeuv: ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) → ∃! x ∃! y φ
    s_2exeuv = lb.ref(
        "s_2exeuv",
        "( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) → ∃! x ∃! y φ",
        ref="2exeuv",
        note="2exeuv",
    )

    # impbid1(jcad, 2exeuv): ∀ x ∃* y φ → ( ∃! x ∃! y φ ↔ ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) )
    res = lb.ref(
        "res",
        "∀ x ∃* y φ → ( ∃! x ∃! y φ ↔ ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) )",
        s_jcad,
        s_2exeuv,
        ref="impbid1",
        note="impbid1 jcad, 2exeuv",
    )

    return lb.build(res)


def prove_2eu2(sys: System) -> Proof:
    """2eu2: ∃! y ∃ x φ → ( ∃! x ∃! y φ ↔ ∃! x ∃ y φ ).

    For the case when ∃! y ∃ x φ holds, the "naive" definition of double
    existential uniqueness collapses to the simpler form.
    (Contributed by NM, 3-Dec-2001.)
    """
    lb = ProofBuilder(sys, "2eu2")

    # eumo: ∃! y ∃ x φ → ∃* y ∃ x φ
    s_eumo = lb.ref(
        "s_eumo",
        "∃! y ∃ x φ → ∃* y ∃ x φ",
        ref="eumo",
        note="eumo",
    )

    # 2moex: ∃* y ∃ x φ → ∀ x ∃* y φ
    s_2moex = lb.ref(
        "s_2moex",
        "∃* y ∃ x φ → ∀ x ∃* y φ",
        ref="2moex",
        note="2moex",
    )

    # 2eu1: ∀ x ∃* y φ → ( ∃! x ∃! y φ ↔ ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) )
    s_2eu1 = lb.ref(
        "s_2eu1",
        "∀ x ∃* y φ → ( ∃! x ∃! y φ ↔ ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) )",
        ref="2eu1",
        note="2eu1",
    )

    # simpl: ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) → ∃! x ∃ y φ
    s_simpl = lb.ref(
        "s_simpl",
        "( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) → ∃! x ∃ y φ",
        ref="simpl",
        note="simpl",
    )

    # biimtrdi(2eu1, simpl): ∀ x ∃* y φ → ( ∃! x ∃! y φ → ∃! x ∃ y φ )
    s_biimtrdi = lb.ref(
        "s_biimtrdi",
        "∀ x ∃* y φ → ( ∃! x ∃! y φ → ∃! x ∃ y φ )",
        s_2eu1,
        s_simpl,
        ref="biimtrdi",
        note="biimtrdi 2eu1, simpl",
    )

    # 3syl(eumo, 2moex, biimtrdi): ∃! y ∃ x φ → ( ∃! x ∃! y φ → ∃! x ∃ y φ )
    s_3syl = lb.ref(
        "s_3syl",
        "∃! y ∃ x φ → ( ∃! x ∃! y φ → ∃! x ∃ y φ )",
        s_eumo,
        s_2moex,
        s_biimtrdi,
        ref="3syl",
        note="3syl eumo, 2moex, biimtrdi",
    )

    # 2exeu: ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) → ∃! x ∃! y φ
    s_2exeu = lb.ref(
        "s_2exeu",
        "( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) → ∃! x ∃! y φ",
        ref="2exeu",
        note="2exeu",
    )

    # expcom(2exeu): ∃! y ∃ x φ → ( ∃! x ∃ y φ → ∃! x ∃! y φ )
    s_expcom = lb.ref(
        "s_expcom",
        "∃! y ∃ x φ → ( ∃! x ∃ y φ → ∃! x ∃! y φ )",
        s_2exeu,
        ref="expcom",
        note="expcom 2exeu",
    )

    # impbid(3syl, expcom): ∃! y ∃ x φ → ( ∃! x ∃! y φ ↔ ∃! x ∃ y φ )
    res = lb.ref(
        "res",
        "∃! y ∃ x φ → ( ∃! x ∃! y φ ↔ ∃! x ∃ y φ )",
        s_3syl,
        s_expcom,
        ref="impbid",
        note="impbid 3syl, expcom",
    )

    return lb.build(res)


def prove_2eu3(sys: System) -> Proof:
    """2eu3: ∀ x ∀ y ( ∃* x φ ∨ ∃* y φ ) → ( ( ∃! x ∃! y φ ∧ ∃! y ∃! x φ ) ↔ ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) ).

    Equivalence condition for double existential uniqueness.  If for all
    x and y either x or y has at most one value for φ, then the naive
    definition of double existential uniqueness matches the correct one.
    (Contributed by NM, 19-Feb-2005.)
    """
    lb = ProofBuilder(sys, "2eu3")

    # nfmo1: Ⅎ y ∃* y φ
    s_nfmo1_y = lb.ref(
        "s_nfmo1_y",
        "Ⅎ y ∃* y φ",
        ref="nfmo1",
        note="nfmo1",
    )

    # 19.31 with nfmo1_y: ∀ y ( ∃* x φ ∨ ∃* y φ ) ↔ ( ∀ y ∃* x φ ∨ ∃* y φ )
    s_19_31 = lb.ref(
        "s_19_31",
        "∀ y ( ∃* x φ ∨ ∃* y φ ) ↔ ( ∀ y ∃* x φ ∨ ∃* y φ )",
        s_nfmo1_y,
        ref="19.31",
        note="19.31 nfmo1",
    )

    # albii s_19_31: ∀ x ∀ y ( ∃* x φ ∨ ∃* y φ ) ↔ ∀ x ( ∀ y ∃* x φ ∨ ∃* y φ )
    s_albii = lb.ref(
        "s_albii",
        "∀ x ∀ y ( ∃* x φ ∨ ∃* y φ ) ↔ ∀ x ( ∀ y ∃* x φ ∨ ∃* y φ )",
        s_19_31,
        ref="albii",
        note="albii 19.31",
    )

    # nfmo1: Ⅎ x ∃* x φ
    s_nfmo1_x = lb.ref(
        "s_nfmo1_x",
        "Ⅎ x ∃* x φ",
        ref="nfmo1",
        note="nfmo1",
    )

    # nfal nfmo1_x: Ⅎ x ∀ y ∃* x φ
    s_nfal = lb.ref(
        "s_nfal",
        "Ⅎ x ∀ y ∃* x φ",
        s_nfmo1_x,
        ref="nfal",
        note="nfal nfmo1",
    )

    # 19.32 nfal: ∀ x ( ∀ y ∃* x φ ∨ ∃* y φ ) ↔ ( ∀ y ∃* x φ ∨ ∀ x ∃* y φ )
    s_19_32 = lb.ref(
        "s_19_32",
        "∀ x ( ∀ y ∃* x φ ∨ ∃* y φ ) ↔ ( ∀ y ∃* x φ ∨ ∀ x ∃* y φ )",
        s_nfal,
        ref="19.32",
        note="19.32 nfal",
    )

    # bitri s_albii, s_19_32:
    #   ∀ x ∀ y ( ∃* x φ ∨ ∃* y φ ) ↔ ( ∀ y ∃* x φ ∨ ∀ x ∃* y φ )
    s_bitri = lb.ref(
        "s_bitri",
        "∀ x ∀ y ( ∃* x φ ∨ ∃* y φ ) ↔ ( ∀ y ∃* x φ ∨ ∀ x ∃* y φ )",
        s_albii,
        s_19_32,
        ref="bitri",
        note="bitri albii, 19.32",
    )

    # orcom: swap the disjuncts
    s_orcom = lb.ref(
        "s_orcom",
        "( ∀ y ∃* x φ ∨ ∀ x ∃* y φ ) ↔ ( ∀ x ∃* y φ ∨ ∀ y ∃* x φ )",
        ref="orcom",
        note="orcom",
    )

    # bitri s_bitri, s_orcom:
    #   ∀ x ∀ y ( ∃* x φ ∨ ∃* y φ ) ↔ ( ∀ x ∃* y φ ∨ ∀ y ∃* x φ )
    s_bitri2 = lb.ref(
        "s_bitri2",
        "∀ x ∀ y ( ∃* x φ ∨ ∃* y φ ) ↔ ( ∀ x ∃* y φ ∨ ∀ y ∃* x φ )",
        s_bitri,
        s_orcom,
        ref="bitri",
        note="bitri bitri, orcom",
    )

    # 2eu1: ∀ x ∃* y φ → ( ∃! x ∃! y φ ↔ ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) )
    s_2eu1 = lb.ref(
        "s_2eu1",
        "∀ x ∃* y φ → ( ∃! x ∃! y φ ↔ ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) )",
        ref="2eu1",
        note="2eu1",
    )

    # biimpd s_2eu1: ∀ x ∃* y φ → ( ∃! x ∃! y φ → ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) )
    s_biimpd = lb.ref(
        "s_biimpd",
        "∀ x ∃* y φ → ( ∃! x ∃! y φ → ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) )",
        s_2eu1,
        ref="biimpd",
        note="biimpd 2eu1",
    )

    # 2eu1 (swapped x,y): ∀ y ∃* x φ → ( ∃! y ∃! x φ ↔ ( ∃! y ∃ x φ ∧ ∃! x ∃ y φ ) )
    s_2eu1_sw = lb.ref(
        "s_2eu1_sw",
        "∀ y ∃* x φ → ( ∃! y ∃! x φ ↔ ( ∃! y ∃ x φ ∧ ∃! x ∃ y φ ) )",
        ref="2eu1",
        note="2eu1",
    )

    # ancom: ( ∃! y ∃ x φ ∧ ∃! x ∃ y φ ) ↔ ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ )
    s_ancom = lb.ref(
        "s_ancom",
        "( ∃! y ∃ x φ ∧ ∃! x ∃ y φ ) ↔ ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ )",
        ref="ancom",
        note="ancom",
    )

    # bitrdi s_2eu1_sw, s_ancom:
    #   ∀ y ∃* x φ → ( ∃! y ∃! x φ ↔ ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) )
    s_bitrdi = lb.ref(
        "s_bitrdi",
        "∀ y ∃* x φ → ( ∃! y ∃! x φ ↔ ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) )",
        s_2eu1_sw,
        s_ancom,
        ref="bitrdi",
        note="bitrdi 2eu1, ancom",
    )

    # biimpd s_bitrdi: ∀ y ∃* x φ → ( ∃! y ∃! x φ → ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) )
    s_biimpd2 = lb.ref(
        "s_biimpd2",
        "∀ y ∃* x φ → ( ∃! y ∃! x φ → ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) )",
        s_bitrdi,
        ref="biimpd",
        note="biimpd bitrdi",
    )

    # jaoa s_biimpd, s_biimpd2:
    #   ( ∀ x ∃* y φ ∨ ∀ y ∃* x φ ) →
    #     ( ( ∃! x ∃! y φ ∧ ∃! y ∃! x φ ) → ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) )
    s_jaoa = lb.ref(
        "s_jaoa",
        "( ∀ x ∃* y φ ∨ ∀ y ∃* x φ ) → ( ( ∃! x ∃! y φ ∧ ∃! y ∃! x φ ) → ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) )",
        s_biimpd,
        s_biimpd2,
        ref="jaoa",
        note="jaoa biimpd, biimpd2",
    )

    # 2exeu: ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) → ∃! x ∃! y φ
    s_2exeu = lb.ref(
        "s_2exeu",
        "( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) → ∃! x ∃! y φ",
        ref="2exeu",
        note="2exeu",
    )

    # 2exeu (swapped): ( ∃! y ∃ x φ ∧ ∃! x ∃ y φ ) → ∃! y ∃! x φ
    s_2exeu_sw = lb.ref(
        "s_2exeu_sw",
        "( ∃! y ∃ x φ ∧ ∃! x ∃ y φ ) → ∃! y ∃! x φ",
        ref="2exeu",
        note="2exeu",
    )

    # ancoms s_2exeu_sw: ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) → ∃! y ∃! x φ
    s_ancoms = lb.ref(
        "s_ancoms",
        "( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) → ∃! y ∃! x φ",
        s_2exeu_sw,
        ref="ancoms",
        note="ancoms 2exeu",
    )

    # jca s_2exeu, s_ancoms:
    #   ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) → ( ∃! x ∃! y φ ∧ ∃! y ∃! x φ )
    s_jca = lb.ref(
        "s_jca",
        "( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) → ( ∃! x ∃! y φ ∧ ∃! y ∃! x φ )",
        s_2exeu,
        s_ancoms,
        ref="jca",
        note="jca 2exeu, ancoms",
    )

    # impbid1 s_jaoa, s_jca:
    #   ( ∀ x ∃* y φ ∨ ∀ y ∃* x φ ) →
    #     ( ( ∃! x ∃! y φ ∧ ∃! y ∃! x φ ) ↔ ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) )
    s_impbid1 = lb.ref(
        "s_impbid1",
        "( ∀ x ∃* y φ ∨ ∀ y ∃* x φ ) → ( ( ∃! x ∃! y φ ∧ ∃! y ∃! x φ ) ↔ ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) )",
        s_jaoa,
        s_jca,
        ref="impbid1",
        note="impbid1 jaoa, jca",
    )

    # sylbi s_bitri2, s_impbid1:
    #   ∀ x ∀ y ( ∃* x φ ∨ ∃* y φ ) →
    #     ( ( ∃! x ∃! y φ ∧ ∃! y ∃! x φ ) ↔ ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) )
    res = lb.ref(
        "res",
        "∀ x ∀ y ( ∃* x φ ∨ ∃* y φ ) → ( ( ∃! x ∃! y φ ∧ ∃! y ∃! x φ ) ↔ ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) )",
        s_bitri2,
        s_impbid1,
        ref="sylbi",
        note="sylbi bitri2, impbid1",
    )

    return lb.build(res)


def prove_2euswap(sys: System) -> Proof:
    """2euswap: ∀ x ∃* y φ → (∃! x ∃ y φ → ∃! y ∃ x φ).

    Swap existential uniqueness quantifiers under a "for all, at most one"
    condition.
    (Contributed by NM, 19-Jan-2007.)
    """
    lb = ProofBuilder(sys, "2euswap")

    # excomim: ∃ x ∃ y φ → ∃ y ∃ x φ
    s_excomim = lb.ref(
        "s_excomim",
        "∃ x ∃ y φ → ∃ y ∃ x φ",
        ref="excomim",
        note="excomim",
    )

    # a1i: ∀ x ∃* y φ → (∃ x ∃ y φ → ∃ y ∃ x φ)
    s_a1i = lb.ref(
        "s_a1i",
        "∀ x ∃* y φ → (∃ x ∃ y φ → ∃ y ∃ x φ)",
        s_excomim,
        ref="a1i",
        note="a1i excomim",
    )

    # 2moswap: ∀ x ∃* y φ → (∃* x ∃ y φ → ∃* y ∃ x φ)
    s_2moswap = lb.ref(
        "s_2moswap",
        "∀ x ∃* y φ → (∃* x ∃ y φ → ∃* y ∃ x φ)",
        ref="2moswap",
        note="2moswap",
    )

    # anim12d: ∀ x ∃* y φ → ((∃ x ∃ y φ ∧ ∃* x ∃ y φ) → (∃ y ∃ x φ ∧ ∃* y ∃ x φ))
    s_anim12d = lb.ref(
        "s_anim12d",
        "∀ x ∃* y φ → ((∃ x ∃ y φ ∧ ∃* x ∃ y φ) → (∃ y ∃ x φ ∧ ∃* y ∃ x φ))",
        s_a1i,
        s_2moswap,
        ref="anim12d",
        note="anim12d a1i, 2moswap",
    )

    # df-eu: ∃! x ∃ y φ ↔ (∃ x ∃ y φ ∧ ∃* x ∃ y φ)
    s_dfeu_x = lb.ref(
        "s_dfeu_x",
        "∃! x ∃ y φ ↔ (∃ x ∃ y φ ∧ ∃* x ∃ y φ)",
        ref="df-eu",
        note="df-eu",
    )

    # df-eu: ∃! y ∃ x φ ↔ (∃ y ∃ x φ ∧ ∃* y ∃ x φ)
    s_dfeu_y = lb.ref(
        "s_dfeu_y",
        "∃! y ∃ x φ ↔ (∃ y ∃ x φ ∧ ∃* y ∃ x φ)",
        ref="df-eu",
        note="df-eu",
    )

    # 3imtr4g: ∀ x ∃* y φ → (∃! x ∃ y φ → ∃! y ∃ x φ)
    res = lb.ref(
        "res",
        "∀ x ∃* y φ → (∃! x ∃ y φ → ∃! y ∃ x φ)",
        s_anim12d,
        s_dfeu_x,
        s_dfeu_y,
        ref="3imtr4g",
        note="3imtr4g anim12d, df-eu, df-eu",
    )

    return lb.build(res)


def prove_2euswapv(sys: System) -> Proof:
    """2euswapv: ∀ x ∃* y φ → (∃! x ∃ y φ → ∃! y ∃ x φ).

    Swap existential uniqueness quantifiers under a "for all, at most one"
    condition.  (Contributed by NM, 19-Jan-2007.)
    """
    lb = ProofBuilder(sys, "2euswapv")

    # excomim: ∃ x ∃ y φ → ∃ y ∃ x φ
    s_excomim = lb.ref(
        "s_excomim",
        "∃ x ∃ y φ → ∃ y ∃ x φ",
        ref="excomim",
        note="excomim",
    )

    # a1i: ∀ x ∃* y φ → (∃ x ∃ y φ → ∃ y ∃ x φ)
    s_a1i = lb.ref(
        "s_a1i",
        "∀ x ∃* y φ → (∃ x ∃ y φ → ∃ y ∃ x φ)",
        s_excomim,
        ref="a1i",
        note="a1i excomim",
    )

    # 2moswapv: ∀ x ∃* y φ → (∃* x ∃ y φ → ∃* y ∃ x φ)
    s_2moswapv = lb.ref(
        "s_2moswapv",
        "∀ x ∃* y φ → (∃* x ∃ y φ → ∃* y ∃ x φ)",
        ref="2moswapv",
        note="2moswapv",
    )

    # anim12d: ∀ x ∃* y φ → ((∃ x ∃ y φ ∧ ∃* x ∃ y φ) → (∃ y ∃ x φ ∧ ∃* y ∃ x φ))
    s_anim12d = lb.ref(
        "s_anim12d",
        "∀ x ∃* y φ → ((∃ x ∃ y φ ∧ ∃* x ∃ y φ) → (∃ y ∃ x φ ∧ ∃* y ∃ x φ))",
        s_a1i,
        s_2moswapv,
        ref="anim12d",
        note="anim12d a1i, 2moswapv",
    )

    # df-eu: ∃! x ∃ y φ ↔ (∃ x ∃ y φ ∧ ∃* x ∃ y φ)
    s_dfeu_x = lb.ref(
        "s_dfeu_x",
        "∃! x ∃ y φ ↔ (∃ x ∃ y φ ∧ ∃* x ∃ y φ)",
        ref="df-eu",
        note="df-eu",
    )

    # df-eu: ∃! y ∃ x φ ↔ (∃ y ∃ x φ ∧ ∃* y ∃ x φ)
    s_dfeu_y = lb.ref(
        "s_dfeu_y",
        "∃! y ∃ x φ ↔ (∃ y ∃ x φ ∧ ∃* y ∃ x φ)",
        ref="df-eu",
        note="df-eu",
    )

    # 3imtr4g: ∀ x ∃* y φ → (∃! x ∃ y φ → ∃! y ∃ x φ)
    res = lb.ref(
        "res",
        "∀ x ∃* y φ → (∃! x ∃ y φ → ∃! y ∃ x φ)",
        s_anim12d,
        s_dfeu_x,
        s_dfeu_y,
        ref="3imtr4g",
        note="3imtr4g anim12d, df-eu, df-eu",
    )

    return lb.build(res)


def prove_2eu4(sys: System) -> Proof:
    """2eu4: ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) ↔ ( ∃ x ∃ y φ ∧ ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) ).
    Two ways of expressing "there exists a unique ordered pair
    such that φ(x, y) holds".  This is the analogue of 2mo2
    for existential uniqueness.
    (Contributed by NM, 19-Feb-2005.)
    """
    lb = ProofBuilder(sys, "2eu4")
    # df-eu: ∃! x ∃ y φ ↔ ( ∃ x ∃ y φ ∧ ∃* x ∃ y φ )
    s_dfeu_x = lb.ref(
        "s_dfeu_x",
        "∃! x ∃ y φ ↔ ( ∃ x ∃ y φ ∧ ∃* x ∃ y φ )",
        ref="df-eu",
        note="df-eu",
    )
    # df-eu: ∃! y ∃ x φ ↔ ( ∃ y ∃ x φ ∧ ∃* y ∃ x φ )
    s_dfeu_y = lb.ref(
        "s_dfeu_y",
        "∃! y ∃ x φ ↔ ( ∃ y ∃ x φ ∧ ∃* y ∃ x φ )",
        ref="df-eu",
        note="df-eu",
    )
    # excom: ∃ y ∃ x φ ↔ ∃ x ∃ y φ
    s_excom = lb.ref(
        "s_excom",
        "∃ y ∃ x φ ↔ ∃ x ∃ y φ",
        ref="excom",
        note="excom",
    )
    # bianbi: ∃! y ∃ x φ ↔ ( ∃ x ∃ y φ ∧ ∃* y ∃ x φ )
    s_bianbi = lb.ref(
        "s_bianbi",
        "∃! y ∃ x φ ↔ ( ∃ x ∃ y φ ∧ ∃* y ∃ x φ )",
        s_dfeu_y,
        s_excom,
        ref="bianbi",
        note="bianbi",
    )
    # anbi12i: ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) ↔ ( ( ∃ x ∃ y φ ∧ ∃* x ∃ y φ ) ∧ ( ∃ x ∃ y φ ∧ ∃* y ∃ x φ ) )
    s_anbi12i = lb.ref(
        "s_anbi12i",
        "( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) ↔ ( ( ∃ x ∃ y φ ∧ ∃* x ∃ y φ ) ∧ ( ∃ x ∃ y φ ∧ ∃* y ∃ x φ ) )",
        s_dfeu_x,
        s_bianbi,
        ref="anbi12i",
        note="anbi12i",
    )
    # anandi: ( ∃ x ∃ y φ ∧ ( ∃* x ∃ y φ ∧ ∃* y ∃ x φ ) ) ↔ ( ( ∃ x ∃ y φ ∧ ∃* x ∃ y φ ) ∧ ( ∃ x ∃ y φ ∧ ∃* y ∃ x φ ) )
    s_anandi = lb.ref(
        "s_anandi",
        "( ∃ x ∃ y φ ∧ ( ∃* x ∃ y φ ∧ ∃* y ∃ x φ ) ) ↔ ( ( ∃ x ∃ y φ ∧ ∃* x ∃ y φ ) ∧ ( ∃ x ∃ y φ ∧ ∃* y ∃ x φ ) )",
        ref="anandi",
        note="anandi",
    )
    # 2mo2: ( ∃* x ∃ y φ ∧ ∃* y ∃ x φ ) ↔ ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) )
    s_2mo2 = lb.ref(
        "s_2mo2",
        "( ∃* x ∃ y φ ∧ ∃* y ∃ x φ ) ↔ ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) )",
        ref="2mo2",
        note="2mo2",
    )
    # anbi2i: ( ∃ x ∃ y φ ∧ ( ∃* x ∃ y φ ∧ ∃* y ∃ x φ ) ) ↔ ( ∃ x ∃ y φ ∧ ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) )
    s_anbi2i = lb.ref(
        "s_anbi2i",
        "( ∃ x ∃ y φ ∧ ( ∃* x ∃ y φ ∧ ∃* y ∃ x φ ) ) ↔ ( ∃ x ∃ y φ ∧ ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) )",
        s_2mo2,
        ref="anbi2i",
        note="anbi2i",
    )
    # 3bitr2i: ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) ↔ ( ∃ x ∃ y φ ∧ ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) )
    res = lb.ref(
        "res",
        "( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) ↔ ( ∃ x ∃ y φ ∧ ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) )",
        s_anbi12i,
        s_anandi,
        s_anbi2i,
        ref="3bitr2i",
        note="3bitr2i",
    )
    return lb.build(res)


def prove_2eu5(sys: System) -> Proof:
    """2eu5: ( ∃! x ∃! y φ ∧ ∀ x ∃* y φ ) ↔ ( ∃ x ∃ y φ ∧ ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) ).

    Two ways of expressing "there exists exactly one x such that
    there exists exactly one y such that φ(x, y) holds".  This
    is a variant of 2eu4.
    (Contributed by NM, 19-Feb-2005.)  Avoid ax-13.
    (Revised by Wolf Lammen, 2-Oct-2023.)
    """
    lb = ProofBuilder(sys, "2eu5")

    # 2eu1v: ∀ x ∃* y φ → ( ∃! x ∃! y φ ↔ ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) )
    s_2eu1v = lb.ref(
        "s_2eu1v",
        "∀ x ∃* y φ → ( ∃! x ∃! y φ ↔ ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) )",
        ref="2eu1v",
        note="2eu1v",
    )

    # pm5.32ri: ( ∃! x ∃! y φ ∧ ∀ x ∃* y φ ) ↔ ( ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) ∧ ∀ x ∃* y φ )
    s_pm5_32ri = lb.ref(
        "s_pm5_32ri",
        "( ∃! x ∃! y φ ∧ ∀ x ∃* y φ ) ↔ ( ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) ∧ ∀ x ∃* y φ )",
        s_2eu1v,
        ref="pm5.32ri",
        note="pm5.32ri 2eu1v",
    )

    # eumo: ∃! y ∃ x φ → ∃* y ∃ x φ
    s_eumo = lb.ref(
        "s_eumo",
        "∃! y ∃ x φ → ∃* y ∃ x φ",
        ref="eumo",
        note="eumo",
    )

    # 2moexv: ∃* y ∃ x φ → ∀ x ∃* y φ
    s_2moexv = lb.ref(
        "s_2moexv",
        "∃* y ∃ x φ → ∀ x ∃* y φ",
        ref="2moexv",
        note="2moexv",
    )

    # syl: ∃! y ∃ x φ → ∀ x ∃* y φ
    s_syl = lb.ref(
        "s_syl",
        "∃! y ∃ x φ → ∀ x ∃* y φ",
        s_eumo,
        s_2moexv,
        ref="syl",
        note="syl eumo, 2moexv",
    )

    # adantl: ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) → ∀ x ∃* y φ
    s_adantl = lb.ref(
        "s_adantl",
        "( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) → ∀ x ∃* y φ",
        s_syl,
        ref="adantl",
        note="adantl syl",
    )

    # pm4.71i: ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) ↔ ( ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) ∧ ∀ x ∃* y φ )
    s_pm4_71i = lb.ref(
        "s_pm4_71i",
        "( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) ↔ ( ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) ∧ ∀ x ∃* y φ )",
        s_adantl,
        ref="pm4.71i",
        note="pm4.71i adantl",
    )

    # 2eu4: ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) ↔ ( ∃ x ∃ y φ ∧ ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) )
    s_2eu4 = lb.ref(
        "s_2eu4",
        "( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) ↔ ( ∃ x ∃ y φ ∧ ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) )",
        ref="2eu4",
        note="2eu4",
    )

    # 3bitr2i: ( ∃! x ∃! y φ ∧ ∀ x ∃* y φ ) ↔ ( ∃ x ∃ y φ ∧ ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) )
    res = lb.ref(
        "res",
        "( ∃! x ∃! y φ ∧ ∀ x ∃* y φ ) ↔ ( ∃ x ∃ y φ ∧ ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) )",
        s_pm5_32ri,
        s_pm4_71i,
        s_2eu4,
        ref="3bitr2i",
        note="3bitr2i",
    )

    return lb.build(res)


def prove_2eu6(sys: System) -> Proof:
    """2eu6: ( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) ↔ ∃ z ∃ w ∀ x ∀ y ( φ ↔ ( x = z ∧ y = w ) ).
    Two equivalent expressions for double existential uniqueness.
    (Contributed by NM, 2-Feb-2005.)  (Revised by Mario Carneiro,
    17-Oct-2016.)  (Proof shortened by Wolf Lammen, 2-Oct-2019.)
    """
    lb = ProofBuilder(sys, "2eu6")
    # 1: 2eu4
    s1 = lb.ref(
        "s1",
        "( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) ↔ ( ∃ x ∃ y φ ∧ ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) )",
        ref="2eu4",
        note="2eu4",
    )
    # 2: nfia1
    s2 = lb.ref(
        "s2",
        "Ⅎ x ( ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) → ∀ x ∀ y ( φ ↔ ( x = z ∧ y = w ) ) )",
        ref="nfia1",
        note="nfia1",
    )
    # 3: nfa1
    s3 = lb.ref(
        "s3",
        "Ⅎ y ∀ y ( φ → ( x = z ∧ y = w ) )",
        ref="nfa1",
        note="nfa1",
    )
    # 4: nfv
    s4 = lb.ref(
        "s4",
        "Ⅎ y x = z",
        ref="nfv",
        note="nfv",
    )
    # 5: simpl
    s5 = lb.ref(
        "s5",
        "( x = z ∧ y = w ) → x = z",
        ref="simpl",
        note="simpl",
    )
    # 6: imim2i with 5
    s6 = lb.ref(
        "s6",
        "( φ → ( x = z ∧ y = w ) ) → ( φ → x = z )",
        s5,
        ref="imim2i",
        note="imim2i simpl",
    )
    # 7: sps with 6
    s7 = lb.ref(
        "s7",
        "∀ y ( φ → ( x = z ∧ y = w ) ) → ( φ → x = z )",
        s6,
        ref="sps",
        note="sps imim2i",
    )
    # 8: exlimd with 3,4,7
    s8 = lb.ref(
        "s8",
        "∀ y ( φ → ( x = z ∧ y = w ) ) → ( ∃ y φ → x = z )",
        s3,
        s4,
        s7,
        ref="exlimd",
        note="exlimd nfa1, nfv, sps",
    )
    # 9: ax12v
    s9 = lb.ref(
        "s9",
        "x = z → ( ∃ y φ → ∀ x ( x = z → ∃ y φ ) )",
        ref="ax12v",
        note="ax12v",
    )
    # 10: syli with 8,9
    s10 = lb.ref(
        "s10",
        "∀ y ( φ → ( x = z ∧ y = w ) ) → ( ∃ y φ → ∀ x ( x = z → ∃ y φ ) )",
        s8,
        s9,
        ref="syli",
        note="syli exlimd, ax12v",
    )
    # 11: com12 with 10
    s11 = lb.ref(
        "s11",
        "∃ y φ → ( ∀ y ( φ → ( x = z ∧ y = w ) ) → ∀ x ( x = z → ∃ y φ ) )",
        s10,
        ref="com12",
        note="com12 syli",
    )
    # 12: spsd with 11
    s12 = lb.ref(
        "s12",
        "∃ y φ → ( ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) → ∀ x ( x = z → ∃ y φ ) )",
        s11,
        ref="spsd",
        note="spsd com12",
    )
    # 13: nfs1v
    s13 = lb.ref(
        "s13",
        "Ⅎ y [ w y φ",
        ref="nfs1v",
        note="nfs1v",
    )
    # 14: simpr
    s14 = lb.ref(
        "s14",
        "( x = z ∧ y = w ) → y = w",
        ref="simpr",
        note="simpr",
    )
    # 15: imim2i with 14
    s15 = lb.ref(
        "s15",
        "( φ → ( x = z ∧ y = w ) ) → ( φ → y = w )",
        s14,
        ref="imim2i",
        note="imim2i simpr",
    )
    # 16: sbequ1
    s16 = lb.ref(
        "s16",
        "y = w → ( φ → [ w y φ )",
        ref="sbequ1",
        note="sbequ1",
    )
    # 17: syli with 15,16
    s17 = lb.ref(
        "s17",
        "( φ → ( x = z ∧ y = w ) ) → ( φ → [ w y φ )",
        s15,
        s16,
        ref="syli",
        note="syli imim2i, sbequ1",
    )
    # 18: sps with 17
    s18 = lb.ref(
        "s18",
        "∀ y ( φ → ( x = z ∧ y = w ) ) → ( φ → [ w y φ )",
        s17,
        ref="sps",
        note="sps syli",
    )
    # 19: exlimd with 3,13,18
    s19 = lb.ref(
        "s19",
        "∀ y ( φ → ( x = z ∧ y = w ) ) → ( ∃ y φ → [ w y φ )",
        s3,
        s13,
        s18,
        ref="exlimd",
        note="exlimd nfa1, nfs1v, sps",
    )
    # 20: imim2d with 19
    s20 = lb.ref(
        "s20",
        "∀ y ( φ → ( x = z ∧ y = w ) ) → ( ( x = z → ∃ y φ ) → ( x = z → [ w y φ ) )",
        s19,
        ref="imim2d",
        note="imim2d exlimd",
    )
    # 21: al2imi with 20
    s21 = lb.ref(
        "s21",
        "∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) → ( ∀ x ( x = z → ∃ y φ ) → ∀ x ( x = z → [ w y φ ) )",
        s20,
        ref="al2imi",
        note="al2imi imim2d",
    )
    # 22: sb6
    s22 = lb.ref(
        "s22",
        "[ z x [ w y φ ↔ ∀ x ( x = z → [ w y φ )",
        ref="sb6",
        note="sb6",
    )
    # 23: 2sb6
    s23 = lb.ref(
        "s23",
        "[ z x [ w y φ ↔ ∀ x ∀ y ( ( x = z ∧ y = w ) → φ )",
        ref="2sb6",
        note="2sb6",
    )
    # 24: bitr3i with 22,23
    s24 = lb.ref(
        "s24",
        "∀ x ( x = z → [ w y φ ) ↔ ∀ x ∀ y ( ( x = z ∧ y = w ) → φ )",
        s22,
        s23,
        ref="bitr3i",
        note="bitr3i sb6, 2sb6",
    )
    # 25: imbitrdi with 21,24
    s25 = lb.ref(
        "s25",
        "∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) → ( ∀ x ( x = z → ∃ y φ ) → ∀ x ∀ y ( ( x = z ∧ y = w ) → φ ) )",
        s21,
        s24,
        ref="imbitrdi",
        note="imbitrdi al2imi, bitr3i",
    )
    # 26: sylcom with 12,25
    s26 = lb.ref(
        "s26",
        "∃ y φ → ( ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) → ∀ x ∀ y ( ( x = z ∧ y = w ) → φ ) )",
        s12,
        s25,
        ref="sylcom",
        note="sylcom spsd, imbitrdi",
    )
    # 27: ancld with 26
    s27 = lb.ref(
        "s27",
        "∃ y φ → ( ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) → ( ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) ∧ ∀ x ∀ y ( ( x = z ∧ y = w ) → φ ) ) )",
        s26,
        ref="ancld",
        note="ancld sylcom",
    )
    # 28: 2albiim
    s28 = lb.ref(
        "s28",
        "∀ x ∀ y ( φ ↔ ( x = z ∧ y = w ) ) ↔ ( ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) ∧ ∀ x ∀ y ( ( x = z ∧ y = w ) → φ ) )",
        ref="2albiim",
        note="2albiim",
    )
    # 29: imbitrrdi with 27,28
    s29 = lb.ref(
        "s29",
        "∃ y φ → ( ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) → ∀ x ∀ y ( φ ↔ ( x = z ∧ y = w ) ) )",
        s27,
        s28,
        ref="imbitrrdi",
        note="imbitrrdi ancld, 2albiim",
    )
    # 30: exlimi with 2,29
    s30 = lb.ref(
        "s30",
        "∃ x ∃ y φ → ( ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) → ∀ x ∀ y ( φ ↔ ( x = z ∧ y = w ) ) )",
        s2,
        s29,
        ref="exlimi",
        note="exlimi nfia1, imbitrrdi",
    )
    # 31: 2eximdv with 30
    s31 = lb.ref(
        "s31",
        "∃ x ∃ y φ → ( ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) → ∃ z ∃ w ∀ x ∀ y ( φ ↔ ( x = z ∧ y = w ) ) )",
        s30,
        ref="2eximdv",
        note="2eximdv exlimi",
    )
    # 32: imp with 31
    s32 = lb.ref(
        "s32",
        "( ∃ x ∃ y φ ∧ ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) ) → ∃ z ∃ w ∀ x ∀ y ( φ ↔ ( x = z ∧ y = w ) )",
        s31,
        ref="imp",
        note="imp 2eximdv",
    )
    # 33: biimpr
    s33 = lb.ref(
        "s33",
        "( φ ↔ ( x = z ∧ y = w ) ) → ( ( x = z ∧ y = w ) → φ )",
        ref="biimpr",
        note="biimpr",
    )
    # 34: 2alimi with 33
    s34 = lb.ref(
        "s34",
        "∀ x ∀ y ( φ ↔ ( x = z ∧ y = w ) ) → ∀ x ∀ y ( ( x = z ∧ y = w ) → φ )",
        s33,
        ref="2alimi",
        note="2alimi biimpr",
    )
    # 35: 2eximi with 34
    s35 = lb.ref(
        "s35",
        "∃ z ∃ w ∀ x ∀ y ( φ ↔ ( x = z ∧ y = w ) ) → ∃ z ∃ w ∀ x ∀ y ( ( x = z ∧ y = w ) → φ )",
        s34,
        ref="2eximi",
        note="2eximi 2alimi",
    )
    # 36: 2exsb
    s36 = lb.ref(
        "s36",
        "∃ x ∃ y φ ↔ ∃ z ∃ w ∀ x ∀ y ( ( x = z ∧ y = w ) → φ )",
        ref="2exsb",
        note="2exsb",
    )
    # 37: sylibr with 35,36
    s37 = lb.ref(
        "s37",
        "∃ z ∃ w ∀ x ∀ y ( φ ↔ ( x = z ∧ y = w ) ) → ∃ x ∃ y φ",
        s35,
        s36,
        ref="sylibr",
        note="sylibr 2eximi, 2exsb",
    )
    # 38: biimp
    s38 = lb.ref(
        "s38",
        "( φ ↔ ( x = z ∧ y = w ) ) → ( φ → ( x = z ∧ y = w ) )",
        ref="biimp",
        note="biimp",
    )
    # 39: 2alimi with 38
    s39 = lb.ref(
        "s39",
        "∀ x ∀ y ( φ ↔ ( x = z ∧ y = w ) ) → ∀ x ∀ y ( φ → ( x = z ∧ y = w ) )",
        s38,
        ref="2alimi",
        note="2alimi biimp",
    )
    # 40: 2eximi with 39
    s40 = lb.ref(
        "s40",
        "∃ z ∃ w ∀ x ∀ y ( φ ↔ ( x = z ∧ y = w ) ) → ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) )",
        s39,
        ref="2eximi",
        note="2eximi 2alimi",
    )
    # 41: jca with 37,40
    s41 = lb.ref(
        "s41",
        "∃ z ∃ w ∀ x ∀ y ( φ ↔ ( x = z ∧ y = w ) ) → ( ∃ x ∃ y φ ∧ ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) )",
        s37,
        s40,
        ref="jca",
        note="jca sylibr, 2eximi",
    )
    # 42: impbii with 32,41
    s42 = lb.ref(
        "s42",
        "( ∃ x ∃ y φ ∧ ∃ z ∃ w ∀ x ∀ y ( φ → ( x = z ∧ y = w ) ) ) ↔ ∃ z ∃ w ∀ x ∀ y ( φ ↔ ( x = z ∧ y = w ) )",
        s32,
        s41,
        ref="impbii",
        note="impbii imp, jca",
    )
    # 43: bitri with 1,42
    res = lb.ref(
        "res",
        "( ∃! x ∃ y φ ∧ ∃! y ∃ x φ ) ↔ ∃ z ∃ w ∀ x ∀ y ( φ ↔ ( x = z ∧ y = w ) )",
        s1,
        s42,
        ref="bitri",
        note="bitri 2eu4, impbii",
    )
    return lb.build(res)


def prove_sb8(sys: System) -> Proof:
    """sb8: ∀ x φ ↔ ∀ y [ y x φ.

    Change bound variable in a universal quantifier using proper substitution.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sb8")
    hyp = lb.hyp("sb8.1", "Ⅎ y φ")

    # nfs1: Ⅎ x [ y x φ
    s1 = lb.ref(
        "s1",
        "Ⅎ x [ y x φ",
        hyp,
        ref="nfs1",
        note="nfs1 sb8.1",
    )

    # sbequ12: x = y → ( φ ↔ [ y x φ )
    s2 = lb.ref(
        "s2",
        "x = y → ( φ ↔ [ y x φ )",
        ref="sbequ12",
        note="sbequ12",
    )

    # cbval sb8.1, nfs1, sbequ12: ∀ x φ ↔ ∀ y [ y x φ
    res = lb.ref(
        "res",
        "∀ x φ ↔ ∀ y [ y x φ",
        hyp,
        s1,
        s2,
        ref="cbval",
        note="cbval sb8.1, nfs1, sbequ12",
    )

    return lb.build(res)


def prove_sb8e(sys: System) -> Proof:
    """sb8e: ∃ x φ ↔ ∃ y [ y x φ.
    Change bound variable in an existential quantifier using explicit
    substitution.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sb8e")
    hyp = lb.hyp("sb8.1", "Ⅎ y φ")
    # nfs1: Ⅎ x [ y x φ
    s1 = lb.ref(
        "s1",
        "Ⅎ x [ y x φ",
        hyp,
        ref="nfs1",
        note="nfs1 sb8.1",
    )
    # sbequ12: x = y → ( φ ↔ [ y x φ )
    s2 = lb.ref(
        "s2",
        "x = y → ( φ ↔ [ y x φ )",
        ref="sbequ12",
        note="sbequ12",
    )
    # cbvex: ∃ x φ ↔ ∃ y [ y x φ
    res = lb.ref(
        "res",
        "∃ x φ ↔ ∃ y [ y x φ",
        hyp,
        s1,
        s2,
        ref="cbvex",
        note="cbvex sb8.1, nfs1, sbequ12",
    )
    return lb.build(res)


def prove_sb8ef(sys: System) -> Proof:
    """sb8ef: ∃ x φ ↔ ∃ y [ y x φ.
    Change bound variable in an existential quantifier using substitution.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sb8ef")
    hyp_nf = lb.hyp("sb8f.nf", "Ⅎ y φ")
    # nfs1v: Ⅎ x [ y x φ
    s_nfs1v = lb.ref(
        "s_nfs1v",
        "Ⅎ x [ y x φ",
        ref="nfs1v",
        note="nfs1v",
    )
    # sbequ12: x = y → ( φ ↔ [ y x φ )
    s_sbequ12 = lb.ref(
        "s_sbequ12",
        "x = y → ( φ ↔ [ y x φ )",
        ref="sbequ12",
        note="sbequ12",
    )
    # cbvexv1: ∃ x φ ↔ ∃ y [ y x φ
    res = lb.ref(
        "res",
        "∃ x φ ↔ ∃ y [ y x φ",
        hyp_nf,
        s_nfs1v,
        s_sbequ12,
        ref="cbvexv1",
        note="cbvexv1 sb8f.nf, nfs1v, sbequ12",
    )
    return lb.build(res)


def prove_2sb8e(sys: System) -> Proof:
    """2sb8e: ∃ x ∃ y φ ↔ ∃ z ∃ w [ z / x ] [ w / y ] φ.

    Change bound variables in two nested existential quantifiers using
    explicit substitution.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "2sb8e")
    # nfv: Ⅎ w φ
    s_nfv_w = lb.ref(
        "s_nfv_w",
        "Ⅎ w φ",
        ref="nfv",
        note="nfv",
    )
    # nfv: Ⅎ z φ
    s_nfv_z = lb.ref(
        "s_nfv_z",
        "Ⅎ z φ",
        ref="nfv",
        note="nfv",
    )
    # sb8e: ∃ y φ ↔ ∃ w [ w / y ] φ
    s1 = lb.ref(
        "s1",
        "∃ y φ ↔ ∃ w [ w y φ",
        s_nfv_w,
        ref="sb8e",
        note="sb8e",
    )
    # exbii: ∃ x ∃ y φ ↔ ∃ x ∃ w [ w / y ] φ
    s2 = lb.ref(
        "s2",
        "∃ x ∃ y φ ↔ ∃ x ∃ w [ w y φ",
        s1,
        ref="exbii",
        note="exbii",
    )
    # excom: ∃ x ∃ w [ w / y ] φ ↔ ∃ w ∃ x [ w / y ] φ
    s3 = lb.ref(
        "s3",
        "∃ x ∃ w [ w y φ ↔ ∃ w ∃ x [ w y φ",
        ref="excom",
        note="excom",
    )
    # bitri: ∃ x ∃ y φ ↔ ∃ w ∃ x [ w / y ] φ
    s4 = lb.ref(
        "s4",
        "∃ x ∃ y φ ↔ ∃ w ∃ x [ w y φ",
        s2,
        s3,
        ref="bitri",
        note="bitri",
    )
    # nfsb: Ⅎ z [ w / y ] φ
    s5 = lb.ref(
        "s5",
        "Ⅎ z [ w y φ",
        s_nfv_z,
        ref="nfsb",
        note="nfsb",
    )
    # sb8e: ∃ x [ w / y ] φ ↔ ∃ z [ z / x ] [ w / y ] φ
    s6 = lb.ref(
        "s6",
        "∃ x [ w y φ ↔ ∃ z [ z x [ w y φ",
        s5,
        ref="sb8e",
        note="sb8e",
    )
    # exbii: ∃ w ∃ x [ w / y ] φ ↔ ∃ w ∃ z [ z / x ] [ w / y ] φ
    s7 = lb.ref(
        "s7",
        "∃ w ∃ x [ w y φ ↔ ∃ w ∃ z [ z x [ w y φ",
        s6,
        ref="exbii",
        note="exbii",
    )
    # excom: ∃ w ∃ z [ z / x ] [ w / y ] φ ↔ ∃ z ∃ w [ z / x ] [ w / y ] φ
    s8 = lb.ref(
        "s8",
        "∃ w ∃ z [ z x [ w y φ ↔ ∃ z ∃ w [ z x [ w y φ",
        ref="excom",
        note="excom",
    )
    # 3bitri: ∃ x ∃ y φ ↔ ∃ z ∃ w [ z / x ] [ w / y ] φ
    res = lb.ref(
        "res",
        "∃ x ∃ y φ ↔ ∃ z ∃ w [ z x [ w y φ",
        s4,
        s7,
        s8,
        ref="3bitri",
        note="3bitri",
    )
    return lb.build(res)


def prove_2sb8ef(sys: System) -> Proof:
    """2sb8ef: ∃ x ∃ y φ ↔ ∃ z ∃ w [ z x [ w y φ.
    Change bound variables in two nested existential quantifiers using
    substitution.  (Contributed by NM, 5-Aug-1993.)
    """

    lb = ProofBuilder(sys, "2sb8ef")
    hyp_nfw = lb.hyp("2sb8ef.1", "Ⅎ w φ")
    hyp_nfz = lb.hyp("2sb8ef.2", "Ⅎ z φ")
    # sb8ef: ∃ y φ ↔ ∃ w [ w / y ] φ
    s1 = lb.ref(
        "s1",
        "∃ y φ ↔ ∃ w [ w y φ",
        hyp_nfw,
        ref="sb8ef",
        note="sb8ef",
    )
    # exbii: ∃ x ∃ y φ ↔ ∃ x ∃ w [ w / y ] φ
    s2 = lb.ref(
        "s2",
        "∃ x ∃ y φ ↔ ∃ x ∃ w [ w y φ",
        s1,
        ref="exbii",
        note="exbii",
    )
    # excom: ∃ x ∃ w [ w / y ] φ ↔ ∃ w ∃ x [ w / y ] φ
    s3 = lb.ref(
        "s3",
        "∃ x ∃ w [ w y φ ↔ ∃ w ∃ x [ w y φ",
        ref="excom",
        note="excom",
    )
    # nfsbv: Ⅎ z [ w / y ] φ
    s4 = lb.ref(
        "s4",
        "Ⅎ z [ w y φ",
        hyp_nfz,
        ref="nfsbv",
        note="nfsbv",
    )
    # sb8ef: ∃ x [ w / y ] φ ↔ ∃ z [ z / x ] [ w / y ] φ
    s5 = lb.ref(
        "s5",
        "∃ x [ w y φ ↔ ∃ z [ z x [ w y φ",
        s4,
        ref="sb8ef",
        note="sb8ef",
    )
    # exbii: ∃ w ∃ x [ w / y ] φ ↔ ∃ w ∃ z [ z / x ] [ w / y ] φ
    s6 = lb.ref(
        "s6",
        "∃ w ∃ x [ w y φ ↔ ∃ w ∃ z [ z x [ w y φ",
        s5,
        ref="exbii",
        note="exbii",
    )
    # excom: ∃ w ∃ z [ z / x ] [ w / y ] φ ↔ ∃ z ∃ w [ z / x ] [ w / y ] φ
    s7 = lb.ref(
        "s7",
        "∃ w ∃ z [ z x [ w y φ ↔ ∃ z ∃ w [ z x [ w y φ",
        ref="excom",
        note="excom",
    )
    # bitri: (s2, s3) → ∃ x ∃ y φ ↔ ∃ w ∃ x [ w / y ] φ
    s8 = lb.ref(
        "s8",
        "∃ x ∃ y φ ↔ ∃ w ∃ x [ w y φ",
        s2,
        s3,
        ref="bitri",
        note="bitri",
    )
    # bitri: (s8, s6) → ∃ x ∃ y φ ↔ ∃ w ∃ z [ z / x ] [ w / y ] φ
    s9 = lb.ref(
        "s9",
        "∃ x ∃ y φ ↔ ∃ w ∃ z [ z x [ w y φ",
        s8,
        s6,
        ref="bitri",
        note="bitri",
    )
    # bitri: (s9, s7) → ∃ x ∃ y φ ↔ ∃ z ∃ w [ z / x ] [ w / y ] φ
    res = lb.ref(
        "res",
        "∃ x ∃ y φ ↔ ∃ z ∃ w [ z x [ w y φ",
        s9,
        s7,
        ref="bitri",
        note="bitri",
    )
    return lb.build(res)


def prove_2exsb(sys: System) -> Proof:
    """2exsb: ∃ x ∃ y φ ↔ ∃ z ∃ w ∀ x ∀ y ( ( x = z ∧ y = w ) → φ ).
    Existence expressed as an alternation of quantifiers (two variables).
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "2exsb")
    # nfv: Ⅎ z φ
    s_nfv_z = lb.ref(
        "s_nfv_z",
        "Ⅎ z φ",
        ref="nfv",
        note="nfv",
    )
    # nfv: Ⅎ w φ
    s_nfv_w = lb.ref(
        "s_nfv_w",
        "Ⅎ w φ",
        ref="nfv",
        note="nfv",
    )
    # 2sb8ef: ∃ x ∃ y φ ↔ ∃ z ∃ w [ z / x ] [ w / y ] φ
    s_2sb8ef = lb.ref(
        "s_2sb8ef",
        "∃ x ∃ y φ ↔ ∃ z ∃ w [ z x [ w y φ",
        s_nfv_w,
        s_nfv_z,
        ref="2sb8ef",
        note="2sb8ef",
    )
    # 2sb6: [ z / x ] [ w / y ] φ ↔ ∀ x ∀ y ( ( x = z ∧ y = w ) → φ )
    s_2sb6 = lb.ref(
        "s_2sb6",
        "[ z x [ w y φ ↔ ∀ x ∀ y ( ( x = z ∧ y = w ) → φ )",
        ref="2sb6",
        note="2sb6",
    )
    # 2exbii: ∃ z ∃ w [ z / x ] [ w / y ] φ ↔ ∃ z ∃ w ∀ x ∀ y ( ( x = z ∧ y = w ) → φ )
    s_2exbii = lb.ref(
        "s_2exbii",
        "∃ z ∃ w [ z x [ w y φ ↔ ∃ z ∃ w ∀ x ∀ y ( ( x = z ∧ y = w ) → φ )",
        s_2sb6,
        ref="2exbii",
        note="2exbii 2sb6",
    )
    # bitri: chain 2sb8ef and 2exbii
    res = lb.ref(
        "res",
        "∃ x ∃ y φ ↔ ∃ z ∃ w ∀ x ∀ y ( ( x = z ∧ y = w ) → φ )",
        s_2sb8ef,
        s_2exbii,
        ref="bitri",
        note="bitri 2sb8ef, 2exbii",
    )
    return lb.build(res)


def prove_sb8v(sys: System) -> Proof:
    """sb8v: ∀ x φ ↔ ∀ y [ y / x ] φ.
    Commutation of bound variable in universal quantifier via substitution.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sb8v")
    # sb6: [ y / x ] φ ↔ ∀ x ( x = y → φ )
    s1 = lb.ref(
        "s1",
        "[ y x φ ↔ ∀ x ( x = y → φ )",
        ref="sb6",
        note="sb6",
    )
    # albii with ∀ y: ∀ y [ y / x ] φ ↔ ∀ y ∀ x ( x = y → φ )
    s2 = lb.ref(
        "s2",
        "∀ y [ y x φ ↔ ∀ y ∀ x ( x = y → φ )",
        s1,
        ref="albii",
        note="albii sb6",
    )
    # alcom: ∀ y ∀ x ( x = y → φ ) ↔ ∀ x ∀ y ( x = y → φ )
    s3 = lb.ref(
        "s3",
        "∀ y ∀ x ( x = y → φ ) ↔ ∀ x ∀ y ( x = y → φ )",
        ref="alcom",
        note="alcom",
    )
    # equcom: x = y ↔ y = x
    s4 = lb.ref(
        "s4",
        "x = y ↔ y = x",
        ref="equcom",
        note="equcom",
    )
    # imbi1i equcom: ( x = y → φ ) ↔ ( y = x → φ )
    s5 = lb.ref(
        "s5",
        "( x = y → φ ) ↔ ( y = x → φ )",
        s4,
        ref="imbi1i",
        note="imbi1i equcom",
    )
    # albii with ∀ y: ∀ y ( x = y → φ ) ↔ ∀ y ( y = x → φ )
    s6 = lb.ref(
        "s6",
        "∀ y ( x = y → φ ) ↔ ∀ y ( y = x → φ )",
        s5,
        ref="albii",
        note="albii imbi1i",
    )
    # albii with ∀ x: ∀ x ∀ y ( x = y → φ ) ↔ ∀ x ∀ y ( y = x → φ )
    s7 = lb.ref(
        "s7",
        "∀ x ∀ y ( x = y → φ ) ↔ ∀ x ∀ y ( y = x → φ )",
        s6,
        ref="albii",
        note="albii albii",
    )
    # equsv (x,y swapped): ∀ y ( y = x → φ ) ↔ φ
    s8 = lb.ref(
        "s8",
        "∀ y ( y = x → φ ) ↔ φ",
        ref="equsv",
        note="equsv",
    )
    # albii with ∀ x: ∀ x ∀ y ( y = x → φ ) ↔ ∀ x φ
    s9 = lb.ref(
        "s9",
        "∀ x ∀ y ( y = x → φ ) ↔ ∀ x φ",
        s8,
        ref="albii",
        note="albii equsv",
    )
    # bitri s7, s9: ∀ x ∀ y ( x = y → φ ) ↔ ∀ x φ
    s10 = lb.ref(
        "s10",
        "∀ x ∀ y ( x = y → φ ) ↔ ∀ x φ",
        s7,
        s9,
        ref="bitri",
        note="bitri",
    )
    # 3bitrri s2, s3, s10: ∀ x φ ↔ ∀ y [ y / x ] φ
    res = lb.ref(
        "res",
        "∀ x φ ↔ ∀ y [ y x φ",
        s2,
        s3,
        s10,
        ref="3bitrri",
        note="3bitrri",
    )
    return lb.build(res)


def prove_sb8f(sys: System) -> Proof:
    """sb8f: ∀ x φ ↔ ∀ y [ y / x ] φ.
    Substitution of variable in universal quantifier, given that y
    is not free in φ.  (Contributed by NM, 16-May-1993.)
    (Revised by Wolf Lammen, 19-Jan-2023.)
    """
    lb = ProofBuilder(sys, "sb8f")
    hyp = lb.hyp("sb8f.nf", "Ⅎ y φ")
    # sb6: [ y / x ] φ ↔ ∀ x ( x = y → φ )
    s1 = lb.ref(
        "s1",
        "[ y x φ ↔ ∀ x ( x = y → φ )",
        ref="sb6",
        note="sb6",
    )
    # albii s1: ∀ y [ y / x ] φ ↔ ∀ y ∀ x ( x = y → φ )
    s2 = lb.ref(
        "s2",
        "∀ y [ y x φ ↔ ∀ y ∀ x ( x = y → φ )",
        s1,
        ref="albii",
        note="albii sb6",
    )
    # alcom: ∀ y ∀ x ( x = y → φ ) ↔ ∀ x ∀ y ( x = y → φ )
    s3 = lb.ref(
        "s3",
        "∀ y ∀ x ( x = y → φ ) ↔ ∀ x ∀ y ( x = y → φ )",
        ref="alcom",
        note="alcom",
    )
    # sb6: [ x / y ] φ ↔ ∀ y ( y = x → φ )
    s4 = lb.ref(
        "s4",
        "[ x y φ ↔ ∀ y ( y = x → φ )",
        ref="sb6",
        note="sb6",
    )
    # sbf with hyp (Ⅎ y φ): [ x / y ] φ ↔ φ
    s6 = lb.ref(
        "s6",
        "[ x y φ ↔ φ",
        hyp,
        ref="sbf",
        note="sbf",
    )
    # equcom: y = x ↔ x = y
    s7 = lb.ref(
        "s7",
        "y = x ↔ x = y",
        ref="equcom",
        note="equcom",
    )
    # imbi1i s7: ( y = x → φ ) ↔ ( x = y → φ )
    s8 = lb.ref(
        "s8",
        "( y = x → φ ) ↔ ( x = y → φ )",
        s7,
        ref="imbi1i",
        note="imbi1i equcom",
    )
    # albii s8: ∀ y ( y = x → φ ) ↔ ∀ y ( x = y → φ )
    s9 = lb.ref(
        "s9",
        "∀ y ( y = x → φ ) ↔ ∀ y ( x = y → φ )",
        s8,
        ref="albii",
        note="albii imbi1i",
    )
    # 3bitr3ri s4, s6, s9: ∀ y ( x = y → φ ) ↔ φ
    s10 = lb.ref(
        "s10",
        "∀ y ( x = y → φ ) ↔ φ",
        s4,
        s6,
        s9,
        ref="3bitr3ri",
        note="3bitr3ri sb6, sbf, albii",
    )
    # albii s10: ∀ x ∀ y ( x = y → φ ) ↔ ∀ x φ
    s11 = lb.ref(
        "s11",
        "∀ x ∀ y ( x = y → φ ) ↔ ∀ x φ",
        s10,
        ref="albii",
        note="albii 3bitr3ri",
    )
    # 3bitrri s2, s3, s11: ∀ x φ ↔ ∀ y [ y / x ] φ
    res = lb.ref(
        "res",
        "∀ x φ ↔ ∀ y [ y x φ",
        s2,
        s3,
        s11,
        ref="3bitrri",
        note="3bitrri",
    )
    return lb.build(res)


def prove_sb9(sys: System) -> Proof:
    """sb9: ∀ x [ x / y ] φ ↔ ∀ y [ y / x ] φ.
    Commutation of universally quantified proper substitution.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sb9")

    # --- Case B: ∀ x x = y → (∀ x [ x / y ] φ ↔ ∀ y [ y / x ] φ) ---

    # sbequ12a: x = y → ([ y / x ] φ ↔ [ x / y ] φ)
    s_sbequ12a = lb.ref(
        "s_sbequ12a",
        "x = y → ( [ y x φ ↔ [ x y φ )",
        ref="sbequ12a",
        note="sbequ12a",
    )

    # equcoms s_sbequ12a: y = x → ([ y / x ] φ ↔ [ x / y ] φ)
    s_equcoms = lb.ref(
        "s_equcoms",
        "y = x → ( [ y x φ ↔ [ x y φ )",
        s_sbequ12a,
        ref="equcoms",
        note="equcoms sbequ12a",
    )

    # sps s_equcoms: ∀ y y = x → ([ y / x ] φ ↔ [ x / y ] φ)
    s_sps = lb.ref(
        "s_sps",
        "∀ y y = x → ( [ y x φ ↔ [ x y φ )",
        s_equcoms,
        ref="sps",
        note="sps equcoms",
    )

    # dral1 s_sps: ∀ y y = x → (∀ y [ y / x ] φ ↔ ∀ x [ x / y ] φ)
    s_dral1 = lb.ref(
        "s_dral1",
        "∀ y y = x → ( ∀ y [ y x φ ↔ ∀ x [ x y φ )",
        s_sps,
        ref="dral1",
        note="dral1 sps",
    )

    # aecom: ∀ x x = y ↔ ∀ y y = x
    s_aecom = lb.ref(
        "s_aecom",
        "∀ x x = y ↔ ∀ y y = x",
        ref="aecom",
        note="aecom",
    )

    # biimpi aecom: ∀ x x = y → ∀ y y = x
    s_aecom_imp = lb.ref(
        "s_aecom_imp",
        "∀ x x = y → ∀ y y = x",
        s_aecom,
        ref="biimpi",
        note="biimpi aecom",
    )

    # syl s_aecom_imp, s_dral1: ∀ x x = y → (∀ y [ y / x ] φ ↔ ∀ x [ x / y ] φ)
    s_caseB_pre = lb.ref(
        "s_caseB_pre",
        "∀ x x = y → ( ∀ y [ y x φ ↔ ∀ x [ x y φ )",
        s_aecom_imp,
        s_dral1,
        ref="syl",
        note="syl biimpi-aecom, dral1",
    )

    # bicom: (∀ y [ y / x ] φ ↔ ∀ x [ x / y ] φ) ↔ (∀ x [ x / y ] φ ↔ ∀ y [ y / x ] φ)
    s_bicom = lb.ref(
        "s_bicom",
        "( ∀ y [ y x φ ↔ ∀ x [ x y φ ) ↔ ( ∀ x [ x y φ ↔ ∀ y [ y x φ )",
        ref="bicom",
        note="bicom",
    )

    # biimpi bicom: (∀ y [ y / x ] φ ↔ ∀ x [ x / y ] φ) → (∀ x [ x / y ] φ ↔ ∀ y [ y / x ] φ)
    s_bicom_imp = lb.ref(
        "s_bicom_imp",
        "( ∀ y [ y x φ ↔ ∀ x [ x y φ ) → ( ∀ x [ x y φ ↔ ∀ y [ y x φ )",
        s_bicom,
        ref="biimpi",
        note="biimpi bicom",
    )

    # syl s_caseB_pre, s_bicom_imp: ∀ x x = y → (∀ x [ x / y ] φ ↔ ∀ y [ y / x ] φ)
    s_caseB = lb.ref(
        "s_caseB",
        "∀ x x = y → ( ∀ x [ x y φ ↔ ∀ y [ y x φ )",
        s_caseB_pre,
        s_bicom_imp,
        ref="syl",
        note="syl",
    )

    # --- Case A: ¬ ∀ x x = y → (∀ x [ x / y ] φ ↔ ∀ y [ y / x ] φ) ---

    # cbv2.1: nfnae gives Ⅎ x ¬ ∀ x x = y
    s_nfnae_x = lb.ref(
        "s_nfnae_x",
        "Ⅎ x ¬ ∀ x x = y",
        ref="nfnae",
        note="nfnae",
    )

    # cbv2.2: nfnae gives Ⅎ y ¬ ∀ x x = y
    s_nfnae_y = lb.ref(
        "s_nfnae_y",
        "Ⅎ y ¬ ∀ x x = y",
        ref="nfnae",
        note="nfnae",
    )

    # cbv2.4: nfsb2 gives ¬ ∀ x x = y → Ⅎ x [ y / x ] φ
    s_nfsb2_xy = lb.ref(
        "s_nfsb2_xy",
        "¬ ∀ x x = y → Ⅎ x [ y x φ",
        ref="nfsb2",
        note="nfsb2",
    )

    # For cbv2.3: derive ¬ ∀ x x = y → Ⅎ y [ x / y ] φ
    # Step 1: nfsb2 with x↔y gives ¬ ∀ y y = x → Ⅎ y [ x / y ] φ
    s_nfsb2_yx = lb.ref(
        "s_nfsb2_yx",
        "¬ ∀ y y = x → Ⅎ y [ x y φ",
        ref="nfsb2",
        note="nfsb2 (x,y swapped)",
    )

    # Step 2: notbii aecom gives ¬ ∀ x x = y ↔ ¬ ∀ y y = x
    s_notbii = lb.ref(
        "s_notbii",
        "¬ ∀ x x = y ↔ ¬ ∀ y y = x",
        s_aecom,
        ref="notbii",
        note="notbii aecom",
    )

    # Step 3: biimpi notbii gives ¬ ∀ x x = y → ¬ ∀ y y = x
    s_notbii_imp = lb.ref(
        "s_notbii_imp",
        "¬ ∀ x x = y → ¬ ∀ y y = x",
        s_notbii,
        ref="biimpi",
        note="biimpi notbii",
    )

    # Step 4: syl with nfsb2(y,x) gives ¬ ∀ x x = y → Ⅎ y [ x / y ] φ
    s_nfsb2_yx_swapped = lb.ref(
        "s_nfsb2_yx_swapped",
        "¬ ∀ x x = y → Ⅎ y [ x y φ",
        s_notbii_imp,
        s_nfsb2_yx,
        ref="syl",
        note="syl biimpi-notbii, nfsb2",
    )

    # cbv2.5: ¬ ∀ x x = y → ( x = y → ( [ x / y ] φ ↔ [ y / x ] φ ) )
    # Derive x = y → ([ x / y ] φ ↔ [ y / x ] φ) from sbequ12a

    # bicom for the inner biconditional:
    # ([ y / x ] φ ↔ [ x / y ] φ) ↔ ([ x / y ] φ ↔ [ y / x ] φ)
    s_bicom_sub = lb.ref(
        "s_bicom_sub",
        "( [ y x φ ↔ [ x y φ ) ↔ ( [ x y φ ↔ [ y x φ )",
        ref="bicom",
        note="bicom",
    )

    # biimpi bicom_sub: ([ y / x ] φ ↔ [ x / y ] φ) → ([ x / y ] φ ↔ [ y / x ] φ)
    s_bicom_imp_sub = lb.ref(
        "s_bicom_imp_sub",
        "( [ y x φ ↔ [ x y φ ) → ( [ x y φ ↔ [ y x φ )",
        s_bicom_sub,
        ref="biimpi",
        note="biimpi bicom",
    )

    # syl s_sbequ12a, s_bicom_imp_sub: x = y → ([ x / y ] φ ↔ [ y / x ] φ)
    s_eq_sub = lb.ref(
        "s_eq_sub",
        "x = y → ( [ x y φ ↔ [ y x φ )",
        s_sbequ12a,
        s_bicom_imp_sub,
        ref="syl",
        note="syl sbequ12a, biimpi-bicom",
    )

    # a1i s_eq_sub: ¬ ∀ x x = y → ( x = y → ( [ x / y ] φ ↔ [ y / x ] φ ) )
    s_caseA_eq = lb.ref(
        "s_caseA_eq",
        "¬ ∀ x x = y → ( x = y → ( [ x y φ ↔ [ y x φ ) )",
        s_eq_sub,
        ref="a1i",
        note="a1i syl",
    )

    # cbv2: apply all 5 hypotheses
    s_caseA = lb.ref(
        "s_caseA",
        "¬ ∀ x x = y → ( ∀ x [ x y φ ↔ ∀ y [ y x φ )",
        s_nfnae_x,
        s_nfnae_y,
        s_nfsb2_yx_swapped,
        s_nfsb2_xy,
        s_caseA_eq,
        ref="cbv2",
        note="cbv2 nfnae, nfnae, nfsb2*",
    )

    # pm2.61i: combine cases
    res = lb.ref(
        "res",
        "∀ x [ x y φ ↔ ∀ y [ y x φ",
        s_caseB,
        s_caseA,
        ref="pm2.61i",
        note="pm2.61i",
    )

    return lb.build(res)


def prove_sb9i(sys: System) -> Proof:
    """sb9i: ∀ x [ x / y ] φ → ∀ y [ y / x ] φ.
    Inference form of sb9, forward direction of the biconditional.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sb9i")
    s_sb9 = lb.ref(
        "s_sb9",
        "∀ x [ x y φ ↔ ∀ y [ y x φ",
        ref="sb9",
        note="sb9",
    )
    res = lb.ref(
        "res",
        "∀ x [ x y φ → ∀ y [ y x φ",
        s_sb9,
        ref="biimpi",
        note="biimpi sb9",
    )
    return lb.build(res)


def prove_sbcom2(sys: System) -> Proof:
    """sbcom2: [ w z [ y x φ ↔ [ y x [ w z φ.

    Commutation of two substitutions with distinct variables.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbcom2")

    # 2sb6: [ v / z ] [ u / x ] φ ↔ ∀ z ∀ x ( ( z = v ∧ x = u ) → φ )
    s1 = lb.ref(
        "s1",
        "[ v z [ u x φ ↔ ∀ z ∀ x ( ( z = v ∧ x = u ) → φ )",
        ref="2sb6",
        note="2sb6",
    )

    # alcom: swap universal quantifiers
    s2 = lb.ref(
        "s2",
        "∀ z ∀ x ( ( z = v ∧ x = u ) → φ ) ↔ ∀ x ∀ z ( ( z = v ∧ x = u ) → φ )",
        ref="alcom",
        note="alcom",
    )

    # ancomst: swap conjunction order in the antecedent
    s3 = lb.ref(
        "s3",
        "( ( z = v ∧ x = u ) → φ ) ↔ ( ( x = u ∧ z = v ) → φ )",
        ref="ancomst",
        note="ancomst",
    )

    # 2albii ancomst: apply double universal quantification
    s4 = lb.ref(
        "s4",
        "∀ x ∀ z ( ( z = v ∧ x = u ) → φ ) ↔ ∀ x ∀ z ( ( x = u ∧ z = v ) → φ )",
        s3,
        ref="2albii",
        note="2albii ancomst",
    )

    # 3bitri: chain s1, s2, s4
    s5 = lb.ref(
        "s5",
        "[ v z [ u x φ ↔ ∀ x ∀ z ( ( x = u ∧ z = v ) → φ )",
        s1,
        s2,
        s4,
        ref="3bitri",
        note="3bitri 2sb6, alcom, 2albii",
    )

    # 2sb6: [ u / x ] [ v / z ] φ ↔ ∀ x ∀ z ( ( x = u ∧ z = v ) → φ )
    s6 = lb.ref(
        "s6",
        "[ u x [ v z φ ↔ ∀ x ∀ z ( ( x = u ∧ z = v ) → φ )",
        ref="2sb6",
        note="2sb6",
    )

    # bitr4i: the two substitution forms are equivalent
    s7 = lb.ref(
        "s7",
        "[ v z [ u x φ ↔ [ u x [ v z φ",
        s5,
        s6,
        ref="bitr4i",
        note="bitr4i 3bitri, 2sb6",
    )

    # sbequ: u = y → ( [ u / x ] φ ↔ [ y / x ] φ )
    s8 = lb.ref(
        "s8",
        "u = y → ( [ u x φ ↔ [ y x φ )",
        ref="sbequ",
        note="sbequ",
    )

    # sbbidv: u = y → ( [ v / z ] [ u / x ] φ ↔ [ v / z ] [ y / x ] φ )
    s9 = lb.ref(
        "s9",
        "u = y → ( [ v z [ u x φ ↔ [ v z [ y x φ )",
        s8,
        ref="sbbidv",
        note="sbbidv sbequ",
    )

    # bitr3id: u = y → ( [ u / x ] [ v / z ] φ ↔ [ v / z ] [ y / x ] φ )
    s10 = lb.ref(
        "s10",
        "u = y → ( [ u x [ v z φ ↔ [ v z [ y x φ )",
        s7,
        s9,
        ref="bitr3id",
        note="bitr3id bitr4i, sbbidv",
    )

    # sbequ: v = w → ( [ v / z ] [ y / x ] φ ↔ [ w / z ] [ y / x ] φ )
    s11 = lb.ref(
        "s11",
        "v = w → ( [ v z [ y x φ ↔ [ w z [ y x φ )",
        ref="sbequ",
        note="sbequ",
    )

    # sylan9bb: ( u = y ∧ v = w ) → ( [ u / x ] [ v / z ] φ ↔ [ w / z ] [ y / x ] φ )
    s12 = lb.ref(
        "s12",
        "( u = y ∧ v = w ) → ( [ u x [ v z φ ↔ [ w z [ y x φ )",
        s10,
        s11,
        ref="sylan9bb",
        note="sylan9bb bitr3id, sbequ",
    )

    # sbequ: v = w → ( [ v / z ] φ ↔ [ w / z ] φ )
    s13 = lb.ref(
        "s13",
        "v = w → ( [ v z φ ↔ [ w z φ )",
        ref="sbequ",
        note="sbequ",
    )

    # sbbidv: v = w → ( [ u / x ] [ v / z ] φ ↔ [ u / x ] [ w / z ] φ )
    s14 = lb.ref(
        "s14",
        "v = w → ( [ u x [ v z φ ↔ [ u x [ w z φ )",
        s13,
        ref="sbbidv",
        note="sbbidv sbequ",
    )

    # sbequ: u = y → ( [ u / x ] [ w / z ] φ ↔ [ y / x ] [ w / z ] φ )
    s15 = lb.ref(
        "s15",
        "u = y → ( [ u x [ w z φ ↔ [ y x [ w z φ )",
        ref="sbequ",
        note="sbequ",
    )

    # sylan9bbr: ( u = y ∧ v = w ) → ( [ u / x ] [ v / z ] φ ↔ [ y / x ] [ w / z ] φ )
    s16 = lb.ref(
        "s16",
        "( u = y ∧ v = w ) → ( [ u x [ v z φ ↔ [ y x [ w z φ )",
        s14,
        s15,
        ref="sylan9bbr",
        note="sylan9bbr sbbidv, sbequ",
    )

    # bitr3d: ( u = y ∧ v = w ) → ( [ w / z ] [ y / x ] φ ↔ [ y / x ] [ w / z ] φ )
    s17 = lb.ref(
        "s17",
        "( u = y ∧ v = w ) → ( [ w z [ y x φ ↔ [ y x [ w z φ )",
        s12,
        s16,
        ref="bitr3d",
        note="bitr3d sylan9bb, sylan9bbr",
    )

    # ex: u = y → ( v = w → ( [ w / z ] [ y / x ] φ ↔ [ y / x ] [ w / z ] φ ) )
    s18 = lb.ref(
        "s18",
        "u = y → ( v = w → ( [ w z [ y x φ ↔ [ y x [ w z φ ) )",
        s17,
        ref="ex",
        note="ex bitr3d",
    )

    # ax6ev: ∃ u u = y
    s19 = lb.ref(
        "s19",
        "∃ u u = y",
        ref="ax6ev",
        note="ax6ev",
    )

    # exlimiiv: v = w → ( [ w / z ] [ y / x ] φ ↔ [ y / x ] [ w / z ] φ )
    s20 = lb.ref(
        "s20",
        "v = w → ( [ w z [ y x φ ↔ [ y x [ w z φ )",
        s18,
        s19,
        ref="exlimiiv",
        note="exlimiiv ex, ax6ev",
    )

    # ax6ev: ∃ v v = w
    s21 = lb.ref(
        "s21",
        "∃ v v = w",
        ref="ax6ev",
        note="ax6ev",
    )

    # exlimiiv: [ w / z ] [ y / x ] φ ↔ [ y / x ] [ w / z ] φ
    res = lb.ref(
        "res",
        "[ w z [ y x φ ↔ [ y x [ w z φ",
        s20,
        s21,
        ref="exlimiiv",
        note="exlimiiv exlimiiv, ax6ev",
    )

    return lb.build(res)


def prove_sbcom3vv(sys: System) -> Proof:
    """sbcom3vv: [ z / y ] [ y / x ] φ ↔ [ z / y ] [ z / x ] φ.
    Substitution commutation when the substituting variables are the same.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbcom3vv")
    # sbequ: y = z → ( [ y / x ] φ ↔ [ z / x ] φ )
    s1 = lb.ref(
        "s1",
        "y = z → ( [ y x φ ↔ [ z x φ )",
        ref="sbequ",
        note="sbequ",
    )
    # sbbiiev: ( y = z → ( [ y / x ] φ ↔ [ z / x ] φ ) )
    #          → ( [ z / y ] [ y / x ] φ ↔ [ z / y ] [ z / x ] φ )
    res = lb.ref(
        "res",
        "( [ z y [ y x φ ↔ [ z y [ z x φ )",
        s1,
        ref="sbbiiev",
        note="sbbiiev sbequ",
    )
    return lb.build(res)


def prove_sbcom3(sys: System) -> Proof:
    """sbcom3: ( [ z / y ] [ y / x ] φ ↔ [ z / y ] [ z / x ] φ ).
    Substituting y for x and then z for y is equivalent to
    substituting z for both x and y.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbcom3")
    # nfa1: Ⅎ y ∀ y y = z
    s_nfa1 = lb.ref(
        "s_nfa1",
        "Ⅎ y ∀ y y = z",
        ref="nfa1",
        note="nfa1",
    )
    # drsb2: ∀ y y = z → ( [ y / x ] φ ↔ [ z / x ] φ )
    s_drsb2 = lb.ref(
        "s_drsb2",
        "∀ y y = z → ( [ y x φ ↔ [ z x φ )",
        ref="drsb2",
        note="drsb2",
    )
    # sbbid with nfa1 and drsb2: ∀ y y = z → ...
    s_sbbid = lb.ref(
        "s_sbbid",
        "∀ y y = z → ( [ z y [ y x φ ↔ [ z y [ z x φ )",
        s_nfa1,
        s_drsb2,
        ref="sbbid",
        note="sbbid nfa1, drsb2",
    )
    # sb4b: ¬ ∀ y y = z → ( [ z / y ] [ y / x ] φ ↔ ∀ y ( y = z → [ y / x ] φ ) )
    s_sb4b_1 = lb.ref(
        "s_sb4b_1",
        "¬ ∀ y y = z → ( [ z y [ y x φ ↔ ∀ y ( y = z → [ y x φ ) )",
        ref="sb4b",
        note="sb4b",
    )
    # sbequ: y = z → ( [ y / x ] φ ↔ [ z / x ] φ )
    s_sbequ = lb.ref(
        "s_sbequ",
        "y = z → ( [ y x φ ↔ [ z x φ )",
        ref="sbequ",
        note="sbequ",
    )
    # pm5.74i: ( y = z → [ y / x ] φ ) ↔ ( y = z → [ z / x ] φ )
    s_pm5_74i = lb.ref(
        "s_pm5_74i",
        "( y = z → [ y x φ ) ↔ ( y = z → [ z x φ )",
        s_sbequ,
        ref="pm5.74i",
        note="pm5.74i sbequ",
    )
    # albii: ∀ y ( y = z → [ y / x ] φ ) ↔ ∀ y ( y = z → [ z / x ] φ )
    s_albii = lb.ref(
        "s_albii",
        "∀ y ( y = z → [ y x φ ) ↔ ∀ y ( y = z → [ z x φ )",
        s_pm5_74i,
        ref="albii",
        note="albii pm5.74i",
    )
    # bitrdi: ¬ ∀ y y = z → ( [ z / y ] [ y / x ] φ ↔ ∀ y ( y = z → [ z / x ] φ ) )
    s_bitrdi = lb.ref(
        "s_bitrdi",
        "¬ ∀ y y = z → ( [ z y [ y x φ ↔ ∀ y ( y = z → [ z x φ ) )",
        s_sb4b_1,
        s_albii,
        ref="bitrdi",
        note="bitrdi sb4b, albii",
    )
    # sb4b (second use): ¬ ∀ y y = z → ( [ z / y ] [ z / x ] φ ↔ ∀ y ( y = z → [ z / x ] φ ) )
    s_sb4b_2 = lb.ref(
        "s_sb4b_2",
        "¬ ∀ y y = z → ( [ z y [ z x φ ↔ ∀ y ( y = z → [ z x φ ) )",
        ref="sb4b",
        note="sb4b",
    )
    # bitr4d: ¬ ∀ y y = z → ( [ z / y ] [ y / x ] φ ↔ [ z / y ] [ z / x ] φ )
    s_bitr4d = lb.ref(
        "s_bitr4d",
        "¬ ∀ y y = z → ( [ z y [ y x φ ↔ [ z y [ z x φ )",
        s_bitrdi,
        s_sb4b_2,
        ref="bitr4d",
        note="bitr4d bitrdi, sb4b",
    )
    # pm2.61i: ( [ z / y ] [ y / x ] φ ↔ [ z / y ] [ z / x ] φ )
    res = lb.ref(
        "res",
        "( [ z y [ y x φ ↔ [ z y [ z x φ )",
        s_sbbid,
        s_bitr4d,
        ref="pm2.61i",
        note="pm2.61i sbbid, bitr4d",
    )
    return lb.build(res)


def prove_axc9(sys: System) -> Proof:
    """axc9: ¬ ∀ z z = x → ( ¬ ∀ z z = y → ( x = y → ∀ z x = y ) ).
    A distinctor elimination theorem for equality.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "axc9")
    # nfeqf: ( ¬ ∀ z z = x ∧ ¬ ∀ z z = y ) → Ⅎ z x = y
    s1 = lb.ref(
        "s1",
        "( ¬ ∀ z z = x ∧ ¬ ∀ z z = y ) → Ⅎ z x = y",
        ref="nfeqf",
        note="nfeqf",
    )
    # nf5rd with hypothesis s1: ( ¬ ∀ z z = x ∧ ¬ ∀ z z = y ) → ( x = y → ∀ z x = y )
    s2 = lb.ref(
        "s2",
        "( ¬ ∀ z z = x ∧ ¬ ∀ z z = y ) → ( x = y → ∀ z x = y )",
        s1,
        ref="nf5rd",
        note="nf5rd nfeqf",
    )
    # ex: apply exportation to get the final form
    res = lb.ref(
        "res",
        "¬ ∀ z z = x → ( ¬ ∀ z z = y → ( x = y → ∀ z x = y ) )",
        s2,
        ref="ex",
        note="ex",
    )
    return lb.build(res)


def prove_axi10(sys: System) -> Proof:
    """axi10: ∀ x x = y → ∀ y y = x.
    Special case of axc11n.  (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "axi10")
    # axc11n: ∀ x x = y → ∀ y y = x
    res = lb.ref(
        "res",
        "∀ x x = y → ∀ y y = x",
        ref="axc11n",
        note="axc11n",
    )
    return lb.build(res)


def prove_axi12(sys: System) -> Proof:
    """axi12: ∀ z z = x ∨ ( ∀ z z = y ∨ ∀ z ( x = y → ∀ z x = y ) ).
    Axiom of quantifier introduction for equality.  The left side of the
    disjunction says that z and x are identical for all z, the middle says
    z and y are identical for all z, and the right says that equality
    implies its own universal generalization for all z.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "axi12")
    # nfa1: Ⅎ z ∀ z z = x
    s1 = lb.ref(
        "s1",
        "Ⅎ z ∀ z z = x",
        ref="nfa1",
        note="nfa1",
    )
    # nfa1: Ⅎ z ∀ z z = y
    s2 = lb.ref(
        "s2",
        "Ⅎ z ∀ z z = y",
        ref="nfa1",
        note="nfa1",
    )
    # nfor: Ⅎ z ( ∀ z z = x ∨ ∀ z z = y )
    s3 = lb.ref(
        "s3",
        "Ⅎ z ( ∀ z z = x ∨ ∀ z z = y )",
        s1,
        s2,
        ref="nfor",
        note="nfor nfa1, nfa1",
    )
    # 19.32: ( ∀ z ( ( ∀ z z = x ∨ ∀ z z = y ) ∨ ( x = y → ∀ z x = y ) ) ↔
    #          ( ( ∀ z z = x ∨ ∀ z z = y ) ∨ ∀ z ( x = y → ∀ z x = y ) ) )
    s4 = lb.ref(
        "s4",
        "( ∀ z ( ( ∀ z z = x ∨ ∀ z z = y ) ∨ ( x = y → ∀ z x = y ) ) ↔ ( ( ∀ z z = x ∨ ∀ z z = y ) ∨ ∀ z ( x = y → ∀ z x = y ) ) )",
        s3,
        ref="19.32",
        note="19.32 nfor",
    )
    # axc9: ( ¬ ∀ z z = x → ( ¬ ∀ z z = y → ( x = y → ∀ z x = y ) ) )
    s5 = lb.ref(
        "s5",
        "¬ ∀ z z = x → ( ¬ ∀ z z = y → ( x = y → ∀ z x = y ) )",
        ref="axc9",
        note="axc9",
    )
    # orrd: ( ¬ ∀ z z = x → ( ∀ z z = y ∨ ( x = y → ∀ z x = y ) ) )
    s6 = lb.ref(
        "s6",
        "¬ ∀ z z = x → ( ∀ z z = y ∨ ( x = y → ∀ z x = y ) )",
        s5,
        ref="orrd",
        note="orrd axc9",
    )
    # orri: ( ∀ z z = x ∨ ( ∀ z z = y ∨ ( x = y → ∀ z x = y ) ) )
    s7 = lb.ref(
        "s7",
        "∀ z z = x ∨ ( ∀ z z = y ∨ ( x = y → ∀ z x = y ) )",
        s6,
        ref="orri",
        note="orri orrd",
    )
    # orass: ( ( ( ∀ z z = x ∨ ∀ z z = y ) ∨ ( x = y → ∀ z x = y ) ) ↔
    #          ( ∀ z z = x ∨ ( ∀ z z = y ∨ ( x = y → ∀ z x = y ) ) ) )
    s8 = lb.ref(
        "s8",
        "( ( ( ∀ z z = x ∨ ∀ z z = y ) ∨ ( x = y → ∀ z x = y ) ) ↔ ( ∀ z z = x ∨ ( ∀ z z = y ∨ ( x = y → ∀ z x = y ) ) ) )",
        ref="orass",
        note="orass",
    )
    # mpbir: ( ( ∀ z z = x ∨ ∀ z z = y ) ∨ ( x = y → ∀ z x = y ) )
    s9 = lb.ref(
        "s9",
        "( ( ∀ z z = x ∨ ∀ z z = y ) ∨ ( x = y → ∀ z x = y ) )",
        s7,
        s8,
        ref="mpbir",
        note="mpbir orri, orass",
    )
    # mpgbi: ( ( ∀ z z = x ∨ ∀ z z = y ) ∨ ∀ z ( x = y → ∀ z x = y ) )
    s10 = lb.ref(
        "s10",
        "( ( ∀ z z = x ∨ ∀ z z = y ) ∨ ∀ z ( x = y → ∀ z x = y ) )",
        s4,
        s9,
        ref="mpgbi",
        note="mpgbi 19.32, mpbir",
    )
    # orass: ( ( ( ∀ z z = x ∨ ∀ z z = y ) ∨ ∀ z ( x = y → ∀ z x = y ) ) ↔
    #          ( ∀ z z = x ∨ ( ∀ z z = y ∨ ∀ z ( x = y → ∀ z x = y ) ) ) )
    s11 = lb.ref(
        "s11",
        "( ( ( ∀ z z = x ∨ ∀ z z = y ) ∨ ∀ z ( x = y → ∀ z x = y ) ) ↔ ( ∀ z z = x ∨ ( ∀ z z = y ∨ ∀ z ( x = y → ∀ z x = y ) ) ) )",
        ref="orass",
        note="orass",
    )
    # mpbi: ( ∀ z z = x ∨ ( ∀ z z = y ∨ ∀ z ( x = y → ∀ z x = y ) ) )
    res = lb.ref(
        "res",
        "∀ z z = x ∨ ( ∀ z z = y ∨ ∀ z ( x = y → ∀ z x = y ) )",
        s10,
        s11,
        ref="mpbi",
        note="mpbi mpgbi, orass",
    )
    return lb.build(res)


def prove_axbnd(sys: System) -> Proof:
    """axbnd: ∀ z z = x ∨ ( ∀ z z = y ∨ ∀ x ∀ z ( x = y → ∀ z x = y ) ).
    Axiom of Bundling (intuitionistic logic axiom ax-bnd).  In classical
    logic, this and axi12 are fairly straightforward consequences of
    axc9.  (Contributed by Jim Kingdon, 22-Mar-2018.)
    (Proof shortened by Wolf Lammen, 24-Apr-2023.)
    (New usage is discouraged.)
    """
    lb = ProofBuilder(sys, "axbnd")
    # nfae: Ⅎ x ∀ z z = x
    s1 = lb.ref(
        "s1",
        "Ⅎ x ∀ z z = x",
        ref="nfae",
        note="nfae",
    )
    # nfae: Ⅎ x ∀ z z = y
    s2 = lb.ref(
        "s2",
        "Ⅎ x ∀ z z = y",
        ref="nfae",
        note="nfae",
    )
    # nfor: Ⅎ x ( ∀ z z = x ∨ ∀ z z = y )
    s3 = lb.ref(
        "s3",
        "Ⅎ x ( ∀ z z = x ∨ ∀ z z = y )",
        s1,
        s2,
        ref="nfor",
        note="nfor nfae, nfae",
    )
    # 19.32: ( ∀ x ( ( ∀ z z = x ∨ ∀ z z = y ) ∨ ∀ z ( x = y → ∀ z x = y ) ) ↔
    #          ( ( ∀ z z = x ∨ ∀ z z = y ) ∨ ∀ x ∀ z ( x = y → ∀ z x = y ) ) )
    s4 = lb.ref(
        "s4",
        "( ∀ x ( ( ∀ z z = x ∨ ∀ z z = y ) ∨ ∀ z ( x = y → ∀ z x = y ) ) ↔ ( ( ∀ z z = x ∨ ∀ z z = y ) ∨ ∀ x ∀ z ( x = y → ∀ z x = y ) ) )",
        s3,
        ref="19.32",
        note="19.32 nfor",
    )
    # orass: ( ( ( ∀ z z = x ∨ ∀ z z = y ) ∨ ∀ x ∀ z ( x = y → ∀ z x = y ) ) ↔
    #          ( ∀ z z = x ∨ ( ∀ z z = y ∨ ∀ x ∀ z ( x = y → ∀ z x = y ) ) ) )
    s5 = lb.ref(
        "s5",
        "( ( ( ∀ z z = x ∨ ∀ z z = y ) ∨ ∀ x ∀ z ( x = y → ∀ z x = y ) ) ↔ ( ∀ z z = x ∨ ( ∀ z z = y ∨ ∀ x ∀ z ( x = y → ∀ z x = y ) ) ) )",
        ref="orass",
        note="orass",
    )
    # bitri: ( ∀ x ( ( ∀ z z = x ∨ ∀ z z = y ) ∨ ∀ z ( x = y → ∀ z x = y ) ) ↔
    #          ( ∀ z z = x ∨ ( ∀ z z = y ∨ ∀ x ∀ z ( x = y → ∀ z x = y ) ) ) )
    s6 = lb.ref(
        "s6",
        "( ∀ x ( ( ∀ z z = x ∨ ∀ z z = y ) ∨ ∀ z ( x = y → ∀ z x = y ) ) ↔ ( ∀ z z = x ∨ ( ∀ z z = y ∨ ∀ x ∀ z ( x = y → ∀ z x = y ) ) ) )",
        s4,
        s5,
        ref="bitri",
        note="bitri 19.32, orass",
    )
    # axi12: ∀ z z = x ∨ ( ∀ z z = y ∨ ∀ z ( x = y → ∀ z x = y ) )
    s7 = lb.ref(
        "s7",
        "∀ z z = x ∨ ( ∀ z z = y ∨ ∀ z ( x = y → ∀ z x = y ) )",
        ref="axi12",
        note="axi12",
    )
    # orass: ( ( ( ∀ z z = x ∨ ∀ z z = y ) ∨ ∀ z ( x = y → ∀ z x = y ) ) ↔
    #          ( ∀ z z = x ∨ ( ∀ z z = y ∨ ∀ z ( x = y → ∀ z x = y ) ) ) )
    s8 = lb.ref(
        "s8",
        "( ( ( ∀ z z = x ∨ ∀ z z = y ) ∨ ∀ z ( x = y → ∀ z x = y ) ) ↔ ( ∀ z z = x ∨ ( ∀ z z = y ∨ ∀ z ( x = y → ∀ z x = y ) ) ) )",
        ref="orass",
        note="orass",
    )
    # mpbir: ( ( ∀ z z = x ∨ ∀ z z = y ) ∨ ∀ z ( x = y → ∀ z x = y ) )
    s9 = lb.ref(
        "s9",
        "( ( ∀ z z = x ∨ ∀ z z = y ) ∨ ∀ z ( x = y → ∀ z x = y ) )",
        s7,
        s8,
        ref="mpbir",
        note="mpbir axi12, orass",
    )
    # mpgbi: ∀ z z = x ∨ ( ∀ z z = y ∨ ∀ x ∀ z ( x = y → ∀ z x = y ) )
    res = lb.ref(
        "res",
        "∀ z z = x ∨ ( ∀ z z = y ∨ ∀ x ∀ z ( x = y → ∀ z x = y ) )",
        s6,
        s9,
        ref="mpgbi",
        note="mpgbi bitri, mpbir",
    )
    return lb.build(res)


def prove_ax13ALT(sys: System) -> Proof:
    """ax13ALT: ¬ x = y → ( y = z → ∀ x y = z ).
    Alternate proof of ax13 using sp, con3i, dveeq1, and syl.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "ax13ALT")
    # sp: ∀ x x = y → x = y
    s1 = lb.ref(
        "s1",
        "∀ x x = y → x = y",
        ref="sp",
        note="sp",
    )
    # con3i: ¬ x = y → ¬ ∀ x x = y
    s2 = lb.ref(
        "s2",
        "¬ x = y → ¬ ∀ x x = y",
        s1,
        ref="con3i",
        note="con3i sp",
    )
    # The source proof uses axc9 with both distinguisher antecedents, rather
    # than dveeq1 (whose x,z DV condition is not available here).
    s1z = lb.ref("s1z", "∀ x x = z → x = z", ref="sp", note="sp")
    s3 = lb.ref(
        "s3",
        "¬ x = z → ¬ ∀ x x = z",
        s1z,
        ref="con3i",
        note="con3i sp",
    )
    s4 = lb.ref(
        "s4",
        "¬ ∀ x x = y → ( ¬ ∀ x x = z → ( y = z → ∀ x y = z ) )",
        ref="axc9",
        note="axc9",
    )
    s5 = lb.ref(
        "s5",
        "¬ x = y → ( ¬ x = z → ( y = z → ∀ x y = z ) )",
        s2,
        s3,
        s4,
        ref="syl2im",
        note="syl2im con3i, con3i, axc9",
    )
    s6 = lb.ref(
        "s6",
        "( ¬ x = y → ( y = z → ∀ x y = z ) ) ↔ ( ¬ x = y → ( ¬ x = z → ( y = z → ∀ x y = z ) ) )",
        ref="ax13b",
        note="ax13b",
    )
    res = lb.ref(
        "res",
        "¬ x = y → ( y = z → ∀ x y = z )",
        s5,
        s6,
        ref="mpbir",
        note="mpbir syl2im, ax13b",
    )
    return lb.build(res)


def prove_ax13(sys: System) -> Proof:
    """ax13: ¬ x = y → ( y = z → ∀ x y = z ).
    Derive ax-13 from ax13v and Tarski's FOL.
    (Contributed by NM, 21-Dec-2015.)
    (Proof shortened by Wolf Lammen, 31-Jan-2018.)
    """
    lb = ProofBuilder(sys, "ax13")
    # equvinv: y = z ↔ ∃ w ( w = y ∧ w = z )
    s41 = lb.ref(
        "s41",
        "y = z ↔ ∃ w ( w = y ∧ w = z )",
        ref="equvinv",
        note="equvinv",
    )
    # ax13lem1: ¬ x = y → ( w = y → ∀ x w = y )
    s73 = lb.ref(
        "s73",
        "¬ x = y → ( w = y → ∀ x w = y )",
        ref="ax13lem1",
        note="ax13lem1",
    )
    # 73 imp: ( ¬ x = y ∧ w = y ) → ∀ x w = y
    s74 = lb.ref(
        "s74",
        "( ¬ x = y ∧ w = y ) → ∀ x w = y",
        s73,
        ref="imp",
        note="imp ax13lem1",
    )
    # ax13lem1: ¬ x = z → ( w = z → ∀ x w = z )
    s81 = lb.ref(
        "s81",
        "¬ x = z → ( w = z → ∀ x w = z )",
        ref="ax13lem1",
        note="ax13lem1",
    )
    # 81 imp: ( ¬ x = z ∧ w = z ) → ∀ x w = z
    s82 = lb.ref(
        "s82",
        "( ¬ x = z ∧ w = z ) → ∀ x w = z",
        s81,
        ref="imp",
        note="imp ax13lem1",
    )
    # ax7v1: w = y → ( w = z → y = z )
    s93 = lb.ref(
        "s93",
        "w = y → ( w = z → y = z )",
        ref="ax7v1",
        note="ax7v1",
    )
    # 93 imp: ( w = y ∧ w = z ) → y = z
    s94 = lb.ref(
        "s94",
        "( w = y ∧ w = z ) → y = z",
        s93,
        ref="imp",
        note="imp ax7v1",
    )
    # 94 alanimi: ( ∀ x w = y ∧ ∀ x w = z ) → ∀ x y = z
    s95 = lb.ref(
        "s95",
        "( ∀ x w = y ∧ ∀ x w = z ) → ∀ x y = z",
        s94,
        ref="alanimi",
        note="alanimi imp",
    )
    # 74,82,95 syl2an
    s96 = lb.ref(
        "s96",
        "( ( ¬ x = y ∧ w = y ) ∧ ( ¬ x = z ∧ w = z ) ) → ∀ x y = z",
        s74,
        s82,
        s95,
        ref="syl2an",
        note="syl2an imp, imp, alanimi",
    )
    # 96 an4s
    s97 = lb.ref(
        "s97",
        "( ( ¬ x = y ∧ ¬ x = z ) ∧ ( w = y ∧ w = z ) ) → ∀ x y = z",
        s96,
        ref="an4s",
        note="an4s syl2an",
    )
    # 97 ex
    s98 = lb.ref(
        "s98",
        "( ¬ x = y ∧ ¬ x = z ) → ( ( w = y ∧ w = z ) → ∀ x y = z )",
        s97,
        ref="ex",
        note="ex an4s",
    )
    # 98 exlimdv
    s99 = lb.ref(
        "s99",
        "( ¬ x = y ∧ ¬ x = z ) → ( ∃ w ( w = y ∧ w = z ) → ∀ x y = z )",
        s98,
        ref="exlimdv",
        note="exlimdv ex",
    )
    # 41,99 biimtrid
    s100 = lb.ref(
        "s100",
        "( ¬ x = y ∧ ¬ x = z ) → ( y = z → ∀ x y = z )",
        s41,
        s99,
        ref="biimtrid",
        note="biimtrid equvinv, exlimdv",
    )
    # 100 ex
    s101 = lb.ref(
        "s101",
        "¬ x = y → ( ¬ x = z → ( y = z → ∀ x y = z ) )",
        s100,
        ref="ex",
        note="ex biimtrid",
    )
    # ax13b
    s106 = lb.ref(
        "s106",
        "( ¬ x = y → ( y = z → ∀ x y = z ) ) ↔ ( ¬ x = y → ( ¬ x = z → ( y = z → ∀ x y = z ) ) )",
        ref="ax13b",
        note="ax13b",
    )
    # 101,106 mpbir
    res = lb.ref(
        "res",
        "¬ x = y → ( y = z → ∀ x y = z )",
        s101,
        s106,
        ref="mpbir",
        note="mpbir ex, ax13b",
    )
    return lb.build(res)


def prove_sbcov(sys: System) -> Proof:
    """sbcov: ( [ y / x ] [ x / y ] φ ↔ [ y / x ] φ ).
    Substitution with exchanged variables.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbcov")
    # sbequ12r: x = y → ( [ x / y ] φ ↔ φ )
    s1 = lb.ref(
        "s1",
        "x = y → ( [ x y φ ↔ φ )",
        ref="sbequ12r",
        note="sbequ12r",
    )
    # sbbiiev: ( x = y → ( [ x / y ] φ ↔ φ ) ) → ( [ y / x ] [ x / y ] φ ↔ [ y / x ] φ )
    res = lb.ref(
        "res",
        "( [ y x [ x y φ ↔ [ y x φ )",
        s1,
        ref="sbbiiev",
        note="sbbiiev sbequ12r",
    )
    return lb.build(res)


def prove_sbco(sys: System) -> Proof:
    """sbco: ( [ y / x ] [ x / y ] φ ↔ [ y / x ] φ ).

    Substitution with exchanged variables (using sbcom3).
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbco")

    # sbcom3: ( [ y / x ] [ x / y ] φ ↔ [ y / x ] [ y / y ] φ )
    s1 = lb.ref(
        "s1",
        "( [ y x [ x y φ ↔ [ y x [ y y φ )",
        ref="sbcom3",
        note="sbcom3",
    )

    # sbid: ( [ y / y ] φ ↔ φ )
    s2 = lb.ref(
        "s2",
        "( [ y y φ ↔ φ )",
        ref="sbid",
        note="sbid",
    )

    # sbbii: ( [ y / x ] [ y / y ] φ ↔ [ y / x ] φ )
    s3 = lb.ref(
        "s3",
        "( [ y x [ y y φ ↔ [ y x φ )",
        s2,
        ref="sbbii",
        note="sbbii sbid",
    )

    # bitri: ( [ y / x ] [ x / y ] φ ↔ [ y / x ] φ )
    res = lb.ref(
        "res",
        "( [ y x [ x y φ ↔ [ y x φ )",
        s1,
        s3,
        ref="bitri",
        note="bitri sbcom3, sbbii",
    )

    return lb.build(res)


def prove_sbco2v(sys: System) -> Proof:
    """sbco2v: ( [ y / z ] [ z / x ] φ ↔ [ y / x ] φ ).
    Change of bound variables via substitution with a not-free hypothesis.
    (Contributed by NM, 26-May-1993.)
    """
    lb = ProofBuilder(sys, "sbco2v")
    h = lb.hyp("sbco2v.1", "Ⅎ z φ")
    # nfsbv: Ⅎ z [ y / x ] φ
    s1 = lb.ref(
        "s1",
        "Ⅎ z [ y x φ",
        h,
        ref="nfsbv",
        note="nfsbv",
    )
    # sbequ: z = y → ( [ z / x ] φ ↔ [ y / x ] φ )
    s2 = lb.ref(
        "s2",
        "z = y → ( [ z x φ ↔ [ y x φ )",
        ref="sbequ",
        note="sbequ",
    )
    # sbiev: ( [ y / z ] [ z / x ] φ ↔ [ y / x ] φ )
    res = lb.ref(
        "res",
        "( [ y z [ z x φ ↔ [ y x φ )",
        s1,
        s2,
        ref="sbiev",
        note="sbiev nfsbv, sbequ",
    )
    return lb.build(res)


def prove_sbco2vv(sys: System) -> Proof:
    """sbco2vv: ( [ y / z ] [ z / x ] φ ↔ [ y / x ] φ ).
    Change of bound variables via substitution.
    (Contributed by NM, 26-May-1993.)
    """
    lb = ProofBuilder(sys, "sbco2vv")
    # sbequ: z = w → ( [ z / x ] φ ↔ [ w / x ] φ )
    s1 = lb.ref(
        "s1",
        "z = w → ( [ z x φ ↔ [ w x φ )",
        ref="sbequ",
        note="sbequ",
    )
    # sbequ: w = y → ( [ w / x ] φ ↔ [ y / x ] φ )
    s2 = lb.ref(
        "s2",
        "w = y → ( [ w x φ ↔ [ y x φ )",
        ref="sbequ",
        note="sbequ",
    )
    # sbievw2: ( [ y / z ] [ z / x ] φ ↔ [ y / x ] φ )
    res = lb.ref(
        "res",
        "( [ y z [ z x φ ↔ [ y x φ )",
        s1,
        s2,
        ref="sbievw2",
        note="sbievw2 sbequ, sbequ",
    )
    return lb.build(res)


def prove_sbco2(sys: System) -> Proof:
    """sbco2: ( [ y / z ] [ z / x ] φ ↔ [ y / x ] φ ).

    Change of bound variables via substitution with a not-free hypothesis.
    (Contributed by NM, 26-May-1993.)
    """
    lb = ProofBuilder(sys, "sbco2")
    h = lb.hyp("sbco2.1", "Ⅎ z φ")

    # sbequ12: z = y → ( [ z / x ] φ ↔ [ y / z ] [ z / x ] φ )
    s1 = lb.ref(
        "s1",
        "( z = y → ( [ z x φ ↔ [ y z [ z x φ ) )",
        ref="sbequ12",
        note="sbequ12",
    )

    # sbequ: z = y → ( [ z / x ] φ ↔ [ y / x ] φ )
    s2 = lb.ref(
        "s2",
        "( z = y → ( [ z x φ ↔ [ y x φ ) )",
        ref="sbequ",
        note="sbequ",
    )

    # bitr3d: z = y → ( [ y / z ] [ z / x ] φ ↔ [ y / x ] φ )
    s3 = lb.ref(
        "s3",
        "( z = y → ( [ y z [ z x φ ↔ [ y x φ ) )",
        s1,
        s2,
        ref="bitr3d",
        note="bitr3d sbequ12, sbequ",
    )

    # sps: ∀ z ( z = y ) → ( [ y / z ] [ z / x ] φ ↔ [ y / x ] φ )
    s4 = lb.ref(
        "s4",
        "( ∀ z ( z = y ) → ( [ y z [ z x φ ↔ [ y x φ ) )",
        s3,
        ref="sps",
        note="sps bitr3d",
    )

    # nfnae: Ⅎ z ¬ ∀ z ( z = y )
    s5 = lb.ref(
        "s5",
        "Ⅎ z ¬ ∀ z ( z = y )",
        ref="nfnae",
        note="nfnae",
    )

    # nfsb4: ( ¬ ∀ z z = y → Ⅎ z [ y / x ] φ )
    s6 = lb.ref(
        "s6",
        "( ¬ ∀ z ( z = y ) → Ⅎ z [ y x φ )",
        h,
        ref="nfsb4",
        note="nfsb4 sbco2.1",
    )

    # a1i: ¬ ∀ z ( z = y ) → ( z = y → ( [ z / x ] φ ↔ [ y / x ] φ ) )
    s7 = lb.ref(
        "s7",
        "( ¬ ∀ z ( z = y ) → ( z = y → ( [ z x φ ↔ [ y x φ ) ) )",
        s2,
        ref="a1i",
        note="a1i sbequ",
    )

    # sbied: ¬ ∀ z ( z = y ) → ( [ y / z ] [ z / x ] φ ↔ [ y / x ] φ )
    s8 = lb.ref(
        "s8",
        "( ¬ ∀ z ( z = y ) → ( [ y z [ z x φ ↔ [ y x φ ) )",
        s5,
        s6,
        s7,
        ref="sbied",
        note="sbied nfnae, nfsb4, a1i",
    )

    # pm2.61i: ( [ y / z ] [ z / x ] φ ↔ [ y / x ] φ )
    res = lb.ref(
        "res",
        "( [ y z [ z x φ ↔ [ y x φ )",
        s4,
        s8,
        ref="pm2.61i",
        note="pm2.61i sps, sbied",
    )

    return lb.build(res)


def prove_sbco2d(sys: System) -> Proof:
    """sbco2d: φ → ( [ y / z ] [ z / x ] ψ ↔ [ y / x ] ψ ).

    Deduction form of sbco2.
    (Contributed by NM, 2-Jun-1993.)
    """
    lb = ProofBuilder(sys, "sbco2d")
    h1 = lb.hyp("sbco2d.1", "Ⅎ x φ")
    h2 = lb.hyp("sbco2d.2", "Ⅎ z φ")
    h3 = lb.hyp("sbco2d.3", "( φ → Ⅎ z ψ )")

    # nfim1: Ⅎ z ( φ → ψ )
    s_nfim = lb.ref(
        "s_nfim",
        "Ⅎ z ( φ → ψ )",
        h2,
        h3,
        ref="nfim1",
        note="nfim1 sbco2d.2, sbco2d.3",
    )

    # sbco2: ( [ y / z ] [ z / x ] ( φ → ψ ) ↔ [ y / x ] ( φ → ψ ) )
    s_sbco2 = lb.ref(
        "s_sbco2",
        "( [ y z [ z x ( φ → ψ ) ↔ [ y x ( φ → ψ ) )",
        s_nfim,
        ref="sbco2",
        note="sbco2 nfim1",
    )

    # sbrim on x: [ z / x ] ( φ → ψ ) ↔ ( φ → [ z / x ] ψ )
    s_sbrim_x = lb.ref(
        "s_sbrim_x",
        "( [ z x ( φ → ψ ) ↔ ( φ → [ z x ψ ) )",
        h1,
        ref="sbrim",
        note="sbrim sbco2d.1",
    )

    # sbbii: [ y / z ] [ z / x ] ( φ → ψ ) ↔ [ y / z ] ( φ → [ z / x ] ψ )
    s_sbbii = lb.ref(
        "s_sbbii",
        "( [ y z [ z x ( φ → ψ ) ↔ [ y z ( φ → [ z x ψ ) )",
        s_sbrim_x,
        ref="sbbii",
        note="sbbii sbrim",
    )

    # sbrim on z: [ y / z ] ( φ → [ z / x ] ψ ) ↔ ( φ → [ y / z ] [ z / x ] ψ )
    s_sbrim_z = lb.ref(
        "s_sbrim_z",
        "( [ y z ( φ → [ z x ψ ) ↔ ( φ → [ y z [ z x ψ ) )",
        h2,
        ref="sbrim",
        note="sbrim sbco2d.2",
    )

    # bitri: [ y / z ] [ z / x ] ( φ → ψ ) ↔ ( φ → [ y / z ] [ z / x ] ψ )
    s_lhs = lb.ref(
        "s_lhs",
        "( [ y z [ z x ( φ → ψ ) ↔ ( φ → [ y z [ z x ψ ) )",
        s_sbbii,
        s_sbrim_z,
        ref="bitri",
        note="bitri sbbii, sbrim",
    )

    # sbrim on x: [ y / x ] ( φ → ψ ) ↔ ( φ → [ y / x ] ψ )
    s_sbrim_x2 = lb.ref(
        "s_sbrim_x2",
        "( [ y x ( φ → ψ ) ↔ ( φ → [ y x ψ ) )",
        h1,
        ref="sbrim",
        note="sbrim sbco2d.1",
    )

    # 3bitr3i: ( φ → [ y / z ] [ z / x ] ψ ) ↔ ( φ → [ y / x ] ψ )
    s_3bitr3i = lb.ref(
        "s_3bitr3i",
        "( ( φ → [ y z [ z x ψ ) ↔ ( φ → [ y x ψ ) )",
        s_sbco2,
        s_lhs,
        s_sbrim_x2,
        ref="3bitr3i",
        note="3bitr3i sbco2, bitri, sbrim",
    )

    # pm5.74ri: φ → ( [ y / z ] [ z / x ] ψ ↔ [ y / x ] ψ )
    res = lb.ref(
        "res",
        "( φ → ( [ y z [ z x ψ ↔ [ y x ψ ) )",
        s_3bitr3i,
        ref="pm5.74ri",
        note="pm5.74ri 3bitr3i",
    )

    return lb.build(res)


def prove_sbco3(sys: System) -> Proof:
    """sbco3: ( [ z / y ] [ y / x ] φ ↔ [ z / x ] [ x / y ] φ ).

    A composition law for substitution exchanging the roles of the
    substituted and substituting variables.
    (Contributed by NM, 2-Jun-1993.)
    """
    lb = ProofBuilder(sys, "sbco3")

    # ── Case: ∀ x x = y ──

    # drsb1: ∀ x x = y → ( [ z / x ] [ y / x ] φ ↔ [ z / y ] [ y / x ] φ )
    s1 = lb.ref(
        "s1",
        "∀ x x = y → ( [ z x [ y x φ ↔ [ z y [ y x φ )",
        ref="drsb1",
        note="drsb1",
    )

    # nfae: Ⅎ x ∀ x x = y
    s2 = lb.ref(
        "s2",
        "Ⅎ x ∀ x x = y",
        ref="nfae",
        note="nfae",
    )

    # sbequ12a: x = y → ( [ y / x ] φ ↔ [ x / y ] φ )
    s3 = lb.ref(
        "s3",
        "x = y → ( [ y x φ ↔ [ x y φ )",
        ref="sbequ12a",
        note="sbequ12a",
    )

    # sps: ∀ x x = y → ( [ y / x ] φ ↔ [ x / y ] φ )
    s4 = lb.ref(
        "s4",
        "∀ x x = y → ( [ y x φ ↔ [ x y φ )",
        s3,
        ref="sps",
        note="sps sbequ12a",
    )

    # sbbid: ∀ x x = y → ( [ z / x ] [ y / x ] φ ↔ [ z / x ] [ x / y ] φ )
    s5 = lb.ref(
        "s5",
        "∀ x x = y → ( [ z x [ y x φ ↔ [ z x [ x y φ )",
        s2,
        s4,
        ref="sbbid",
        note="sbbid nfae, sps",
    )

    # bitr3d: ∀ x x = y → ( [ z / y ] [ y / x ] φ ↔ [ z / x ] [ x / y ] φ )
    s6 = lb.ref(
        "s6",
        "∀ x x = y → ( [ z y [ y x φ ↔ [ z x [ x y φ )",
        s1,
        s5,
        ref="bitr3d",
        note="bitr3d drsb1, sbbid",
    )

    # ── Case: ¬ ∀ x x = y ──

    # nfnae: Ⅎ y ¬ ∀ x x = y
    s7 = lb.ref(
        "s7",
        "Ⅎ y ¬ ∀ x x = y",
        ref="nfnae",
        note="nfnae",
    )

    # nfnae: Ⅎ x ¬ ∀ x x = y
    s8 = lb.ref(
        "s8",
        "Ⅎ x ¬ ∀ x x = y",
        ref="nfnae",
        note="nfnae",
    )

    # nfsb2: ¬ ∀ x x = y → Ⅎ x [ y / x ] φ
    s9 = lb.ref(
        "s9",
        "¬ ∀ x x = y → Ⅎ x [ y x φ",
        ref="nfsb2",
        note="nfsb2",
    )

    # sbco2d: ¬ ∀ x x = y → ( [ z / x ] [ x / y ] [ y / x ] φ ↔ [ z / y ] [ y / x ] φ )
    s10 = lb.ref(
        "s10",
        "¬ ∀ x x = y → ( [ z x [ x y [ y x φ ↔ [ z y [ y x φ )",
        s7,
        s8,
        s9,
        ref="sbco2d",
        note="sbco2d nfnae, nfnae, nfsb2",
    )

    # sbco: ( [ x / y ] [ y / x ] φ ↔ [ x / y ] φ )
    s11 = lb.ref(
        "s11",
        "( [ x y [ y x φ ↔ [ x y φ )",
        ref="sbco",
        note="sbco",
    )

    # sbbii: ( [ z / x ] [ x / y ] [ y / x ] φ ↔ [ z / x ] [ x / y ] φ )
    s12 = lb.ref(
        "s12",
        "( [ z x [ x y [ y x φ ↔ [ z x [ x y φ )",
        s11,
        ref="sbbii",
        note="sbbii sbco",
    )

    # bitr3di: ¬ ∀ x x = y → ( [ z / y ] [ y / x ] φ ↔ [ z / x ] [ x / y ] φ )
    s13 = lb.ref(
        "s13",
        "¬ ∀ x x = y → ( [ z y [ y x φ ↔ [ z x [ x y φ )",
        s10,
        s12,
        ref="bitr3di",
        note="bitr3di sbco2d, sbbii",
    )

    # pm2.61i: ( [ z / y ] [ y / x ] φ ↔ [ z / x ] [ x / y ] φ )
    res = lb.ref(
        "res",
        "( [ z y [ y x φ ↔ [ z x [ x y φ )",
        s6,
        s13,
        ref="pm2.61i",
        note="pm2.61i",
    )

    return lb.build(res)


def prove_sbcom(sys: System) -> Proof:
    """sbcom: ( [ y / z ] [ y / x ] φ ↔ [ y / x ] [ y / z ] φ ).

    A commutativity law for substitution.
    (Contributed by NM, 27-May-1997.)
    """
    lb = ProofBuilder(sys, "sbcom")

    # sbco3 with z←y, y←z: ( [ y / z ] [ z / x ] φ ↔ [ y / x ] [ x / z ] φ )
    s_sbco3 = lb.ref(
        "s_sbco3",
        "( [ y z [ z x φ ↔ [ y x [ x z φ )",
        ref="sbco3",
        note="sbco3",
    )

    # sbcom3 with z←y, y←z: ( [ y / z ] [ z / x ] φ ↔ [ y / z ] [ y / x ] φ )
    s_sbcom3_yz = lb.ref(
        "s_sbcom3_yz",
        "( [ y z [ z x φ ↔ [ y z [ y x φ )",
        ref="sbcom3",
        note="sbcom3",
    )

    # sbcom3 with z←y, y←x: ( [ y / x ] [ x / z ] φ ↔ [ y / x ] [ y / z ] φ )
    s_sbcom3_yx = lb.ref(
        "s_sbcom3_yx",
        "( [ y x [ x z φ ↔ [ y x [ y z φ )",
        ref="sbcom3",
        note="sbcom3",
    )

    # 3bitr3i(s_sbco3, s_sbcom3_yz, s_sbcom3_yx):
    # ( [ y / z ] [ y / x ] φ ↔ [ y / x ] [ y / z ] φ )
    res = lb.ref(
        "res",
        "( [ y z [ y x φ ↔ [ y x [ y z φ )",
        s_sbco3,
        s_sbcom3_yz,
        s_sbcom3_yx,
        ref="3bitr3i",
        note="3bitr3i sbco3, sbcom3, sbcom3",
    )

    return lb.build(res)


def prove_cbvsbv(sys: System) -> Proof:
    """cbvsbv: ( [ z / x ] φ ↔ [ z / y ] ψ ).
    Change of bound variables via proper substitution: if φ and ψ are
    equivalent under the hypothesis x = y, then substituting z for x in φ
    is equivalent to substituting z for y in ψ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "cbvsbv")
    hyp = lb.hyp("cbvsbv.1", "x = y → ( φ ↔ ψ )")
    # sbco2vv (with y↔z): ( [ z / y ] [ y / x ] φ ↔ [ z / x ] φ )
    s1 = lb.ref(
        "s1",
        "( [ z y [ y x φ ↔ [ z x φ )",
        ref="sbco2vv",
        note="sbco2vv",
    )
    # sbievw: ( [ y / x ] φ ↔ ψ )
    s2 = lb.ref(
        "s2",
        "( [ y x φ ↔ ψ )",
        hyp,
        ref="sbievw",
        note="sbievw",
    )
    # sbbii: ( [ z / y ] [ y / x ] φ ↔ [ z / y ] ψ )
    s3 = lb.ref(
        "s3",
        "( [ z y [ y x φ ↔ [ z y ψ )",
        s2,
        ref="sbbii",
        note="sbbii",
    )
    # bitr3i: ( [ z / x ] φ ↔ [ z / y ] ψ )
    res = lb.ref(
        "res",
        "( [ z x φ ↔ [ z y ψ )",
        s1,
        s3,
        ref="bitr3i",
        note="bitr3i sbco2vv, sbbii",
    )
    return lb.build(res)


def prove_cbvsbvf(sys: System) -> Proof:
    """cbvsbvf: [ z / x ] φ ↔ [ z / y ] ψ.
    Change of bound variable in a proper substitution, with not-free hypotheses.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "cbvsbvf")
    hyp_nfy = lb.hyp("cbvsbvf.1", "Ⅎ y φ")
    hyp_nfx = lb.hyp("cbvsbvf.2", "Ⅎ x ψ")
    hyp_iff = lb.hyp("cbvsbvf.3", "x = y → ( φ ↔ ψ )")
    # nfv: Ⅎ y ( x = w )
    s_nfv1 = lb.ref(
        "s_nfv1",
        "Ⅎ y ( x = w )",
        ref="nfv",
        note="nfv",
    )
    # nfim: Ⅎ y ( x = w → φ )
    s_nfim1 = lb.ref(
        "s_nfim1",
        "Ⅎ y ( x = w → φ )",
        s_nfv1,
        hyp_nfy,
        ref="nfim",
        note="nfim",
    )
    # nfv: Ⅎ x ( y = w )
    s_nfv2 = lb.ref(
        "s_nfv2",
        "Ⅎ x ( y = w )",
        ref="nfv",
        note="nfv",
    )
    # nfim: Ⅎ x ( y = w → ψ )
    s_nfim2 = lb.ref(
        "s_nfim2",
        "Ⅎ x ( y = w → ψ )",
        s_nfv2,
        hyp_nfx,
        ref="nfim",
        note="nfim",
    )
    # equequ1: x = y → ( x = w ↔ y = w )
    s_eq = lb.ref(
        "s_eq",
        "x = y → ( x = w ↔ y = w )",
        ref="equequ1",
        note="equequ1",
    )
    # imbi12d: x = y → ( ( x = w → φ ) ↔ ( y = w → ψ ) )
    s_imbid = lb.ref(
        "s_imbid",
        "x = y → ( ( x = w → φ ) ↔ ( y = w → ψ ) )",
        s_eq,
        hyp_iff,
        ref="imbi12d",
        note="imbi12d",
    )
    # cbvalv1: ∀ x ( x = w → φ ) ↔ ∀ y ( y = w → ψ )
    s_cbv = lb.ref(
        "s_cbv",
        "∀ x ( x = w → φ ) ↔ ∀ y ( y = w → ψ )",
        s_nfim1,
        s_nfim2,
        s_imbid,
        ref="cbvalv1",
        note="cbvalv1",
    )
    # imbi2i: ( w = z → ∀ x ( x = w → φ ) ) ↔ ( w = z → ∀ y ( y = w → ψ ) )
    s_imbi = lb.ref(
        "s_imbi",
        "( w = z → ∀ x ( x = w → φ ) ) ↔ ( w = z → ∀ y ( y = w → ψ ) )",
        s_cbv,
        ref="imbi2i",
        note="imbi2i",
    )
    # albii: ∀ w ( w = z → ∀ x ( x = w → φ ) ) ↔ ∀ w ( w = z → ∀ y ( y = w → ψ ) )
    s_albii = lb.ref(
        "s_albii",
        "∀ w ( w = z → ∀ x ( x = w → φ ) ) ↔ ∀ w ( w = z → ∀ y ( y = w → ψ ) )",
        s_imbi,
        ref="albii",
        note="albii",
    )
    # dfsb: [ z / x ] φ ↔ ∀ w ( w = z → ∀ x ( x = w → φ ) )
    s_dfsb1 = lb.ref(
        "s_dfsb1",
        "[ z x φ ↔ ∀ w ( w = z → ∀ x ( x = w → φ ) )",
        ref="dfsb",
        note="dfsb",
    )
    # dfsb: [ z / y ] ψ ↔ ∀ w ( w = z → ∀ y ( y = w → ψ ) )
    s_dfsb2 = lb.ref(
        "s_dfsb2",
        "[ z y ψ ↔ ∀ w ( w = z → ∀ y ( y = w → ψ ) )",
        ref="dfsb",
        note="dfsb",
    )
    # 3bitr4i: [ z / x ] φ ↔ [ z / y ] ψ
    res = lb.ref(
        "res",
        "( [ z x φ ↔ [ z y ψ )",
        s_albii,
        s_dfsb1,
        s_dfsb2,
        ref="3bitr4i",
        note="3bitr4i",
    )
    return lb.build(res)


def prove_sbco4OLD(sys: System) -> Proof:
    """sbco4OLD: ( [ y u [ x v [ u x [ v y φ ↔ [ x w [ y x [ w y φ ).
    Commutation of substitutions.
    (Contributed by NM, 14-May-1993.)
    """
    lb = ProofBuilder(sys, "sbco4OLD")
    symbols = {
        info.local_name: symbol
        for symbol, info in sys.interner.symbol_table().items()
    }
    # Source active DVs, expanded from the theorem's $d groups.
    for group in (
        ("t", "u", "v", "ph"),
        ("t", "u", "v", "x"),
        ("t", "u", "v", "y"),
    ):
        for index, left in enumerate(group):
            for right in group[index + 1 :]:
                lb.disjoint(symbols[left], symbols[right])
    for left, right in (("w", "ph"), ("w", "x"), ("w", "y"), ("t", "w")):
        lb.disjoint(symbols[left], symbols[right])
    # This is the current set.mm proof, including the intermediate variable t.
    s1 = lb.ref(
        "s1",
        "[ x v [ y u [ u x [ v y φ ↔ [ y u [ x v [ u x [ v y φ",
        ref="sbcom2",
        note="sbcom2",
    )
    s2 = lb.ref(
        "s2",
        "( [ y u [ u x [ v y φ ↔ [ y x [ v y φ )",
        ref="sbco2vv",
        note="sbco2vv",
    )
    # sbbii: [ x / v ] ( sbco2vv )
    s3 = lb.ref(
        "s3",
        "( [ x v [ y u [ u x [ v y φ ↔ [ x v [ y x [ v y φ )",
        s2,
        ref="sbbii",
        note="sbbii sbco2vv",
    )
    s4 = lb.ref(
        "s4",
        "[ y u [ x v [ u x [ v y φ ↔ [ x v [ y x [ v y φ",
        s1,
        s3,
        ref="bitr3i",
        note="bitr3i sbcom2, sbbii",
    )
    s5 = lb.ref(
        "s5",
        "[ x v [ y x [ v y φ ↔ [ x t [ y x [ t y φ",
        ref="sbco4lem",
        note="sbco4lem",
    )
    s6 = lb.ref(
        "s6",
        "[ x t [ y x [ t y φ ↔ [ x w [ y x [ w y φ",
        ref="sbco4lem",
        note="sbco4lem",
    )
    res = lb.ref(
        "res",
        "[ y u [ x v [ u x [ v y φ ↔ [ x w [ y x [ w y φ",
        s4,
        s5,
        s6,
        ref="3bitri",
        note="3bitri bitr3i, sbco4lem, sbco4lem",
    )
    return lb.build(res)


def prove_sbco4lemOLD(sys: System) -> Proof:
    """sbco4lemOLD: [ x / v ] [ y / x ] [ v / y ] φ ↔ [ x / w ] [ y / x ] [ w / y ] φ.
    Lemma for sbco4OLD.
    (Contributed by NM, 14-May-1993.)
    set.mm proof: wsb sbcom2 sbbii sbco2vv 2sbbii 3bitr3i.
    """
    lb = ProofBuilder(sys, "sbco4lemOLD")
    symbols = {
        info.local_name: symbol
        for symbol, info in sys.interner.symbol_table().items()
    }
    # Source active DVs: $d v w ph $. $d v w x $. $d v w y $.
    for group in (("v", "w", "ph"), ("v", "w", "x"), ("v", "w", "y")):
        for index, left in enumerate(group):
            for right in group[index + 1 :]:
                lb.disjoint(symbols[left], symbols[right])
    s1 = lb.ref(
        "s1",
        "[ y x [ v w [ w y φ ↔ [ v w [ y x [ w y φ",
        ref="sbcom2",
        note="sbcom2",
    )
    s2 = lb.ref(
        "s2",
        "[ x v [ y x [ v w [ w y φ ↔ [ x v [ v w [ y x [ w y φ",
        s1,
        ref="sbbii",
        note="sbbii sbcom2",
    )
    s3_base = lb.ref("s3_base", "[ v w [ w y φ ↔ [ v y φ", ref="sbco2vv")
    s3 = lb.ref(
        "s3",
        "[ x v [ y x [ v w [ w y φ ↔ [ x v [ y x [ v y φ",
        s3_base,
        ref="2sbbii",
        note="2sbbii sbco2vv",
    )
    s4 = lb.ref(
        "s4",
        "[ x v [ v w [ y x [ w y φ ↔ [ x w [ y x [ w y φ",
        ref="sbco2vv",
        note="sbco2vv",
    )
    res = lb.ref(
        "res",
        "( [ x v [ y x [ v y φ ↔ [ x w [ y x [ w y φ )",
        s2,
        s3,
        s4,
        ref="3bitr3i",
        note="3bitr3i sbbii, 2sbbii, sbco2vv",
    )
    return lb.build(res)


def prove_sbco4lem(sys: System) -> Proof:
    """sbco4lem: ( [ x / v ] [ y / x ] [ v / y ] φ ↔ [ x / w ] [ y / x ] [ w / y ] φ ).
    Lemma for sbco4.
    (Contributed by NM, 14-May-1993.)
    """
    lb = ProofBuilder(sys, "sbco4lem")
    # sbequ: v = w → ( [ v / y ] φ ↔ [ w / y ] φ )
    s1 = lb.ref(
        "s1",
        "v = w → ( [ v y φ ↔ [ w y φ )",
        ref="sbequ",
        note="sbequ",
    )
    # sbbidv: v = w → ( [ y / x ] [ v / y ] φ ↔ [ y / x ] [ w / y ] φ )
    s2 = lb.ref(
        "s2",
        "v = w → ( [ y x [ v y φ ↔ [ y x [ w y φ )",
        s1,
        ref="sbbidv",
        note="sbbidv",
    )
    # cbvsbv: ( [ x / v ] [ y / x ] [ v / y ] φ ↔ [ x / w ] [ y / x ] [ w / y ] φ )
    res = lb.ref(
        "res",
        "( [ x v [ y x [ v y φ ↔ [ x w [ y x [ w y φ )",
        s2,
        ref="cbvsbv",
        note="cbvsbv",
    )
    return lb.build(res)


def prove_sb5rf(sys: System) -> Proof:
    """sb5rf: φ ↔ ∃ y ( y = x ∧ [ y / x ] φ ).
    Equivalence of a formula to itself via a substituted bound variable,
    existential form.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sb5rf")
    hyp_nf = lb.hyp("sb5rf.1", "Ⅎ y φ")
    # sbequ12r: y = x → ( [ y / x ] φ ↔ φ )
    s1 = lb.ref(
        "s1",
        "y = x → ( [ y x φ ↔ φ )",
        ref="sbequ12r",
        note="sbequ12r",
    )
    # equsex: ∃ y ( y = x ∧ [ y / x ] φ ) ↔ φ
    s2 = lb.ref(
        "s2",
        "∃ y ( y = x ∧ [ y x φ ) ↔ φ",
        hyp_nf,
        s1,
        ref="equsex",
        note="equsex sb5rf.1, sbequ12r",
    )
    # bicomi: φ ↔ ∃ y ( y = x ∧ [ y / x ] φ )
    res = lb.ref(
        "res",
        "φ ↔ ∃ y ( y = x ∧ [ y x φ )",
        s2,
        ref="bicomi",
        note="bicomi equsex",
    )
    return lb.build(res)


def prove_sb6rf(sys: System) -> Proof:
    """sb6rf: φ ↔ ∀ y ( y = x → [ y / x ] φ ).
    Equivalence of a formula to itself via a substituted bound variable,
    with a non-freeness hypothesis.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sb6rf")
    hyp_nf = lb.hyp("sb6rf.1", "Ⅎ y φ")
    # sbequ12r: y = x → ( [ y / x ] φ ↔ φ )
    s1 = lb.ref(
        "s1",
        "y = x → ( [ y x φ ↔ φ )",
        ref="sbequ12r",
        note="sbequ12r",
    )
    # equsal: ∀ y ( y = x → [ y / x ] φ ) ↔ φ
    s2 = lb.ref(
        "s2",
        "∀ y ( y = x → [ y x φ ) ↔ φ",
        hyp_nf,
        s1,
        ref="equsal",
        note="equsal sb6rf.1, sbequ12r",
    )
    # bicomi: φ ↔ ∀ y ( y = x → [ y / x ] φ )
    res = lb.ref(
        "res",
        "φ ↔ ∀ y ( y = x → [ y x φ )",
        s2,
        ref="bicomi",
        note="bicomi equsal",
    )
    return lb.build(res)


def prove_sb6rfv(sys: System) -> Proof:
    """sb6rfv: φ ↔ ∀ y ( y = x → [ y / x ] φ ).
    Equivalence of a formula to itself via a substituted bound variable.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sb6rfv")
    hyp_nf = lb.hyp("sb6rfv.nf", "Ⅎ y φ")
    # sbequ12r: y = x → ( [ y / x ] φ ↔ φ )
    s1 = lb.ref(
        "s1",
        "y = x → ( [ y x φ ↔ φ )",
        ref="sbequ12r",
        note="sbequ12r",
    )
    # equsalv with Ⅎ y φ and sbequ12r: ∀ y ( y = x → [ y / x ] φ ) ↔ φ
    s2 = lb.ref(
        "s2",
        "∀ y ( y = x → [ y x φ ) ↔ φ",
        hyp_nf,
        s1,
        ref="equsalv",
        note="equsalv sb6rfv.nf, sbequ12r",
    )
    # bicomi: φ ↔ ∀ y ( y = x → [ y / x ] φ )
    res = lb.ref(
        "res",
        "φ ↔ ∀ y ( y = x → [ y x φ )",
        s2,
        ref="bicomi",
        note="bicomi equsalv",
    )
    return lb.build(res)


def prove_2sb5rf(sys: System) -> Proof:
    """2sb5rf: φ ↔ ∃ z ∃ w ( ( z = x ∧ w = y ) ∧ [ z / x ] [ w / y ] φ ).
    An equivalence with double substitution and existential quantifiers,
    given that φ is not free in z and w.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "2sb5rf")
    hyp_nfz = lb.hyp("2sb5rf.1", "Ⅎ z φ")
    hyp_nfw = lb.hyp("2sb5rf.2", "Ⅎ w φ")

    # sbequ12r: z = x → ( [ z / x ] [ w / y ] φ ↔ [ w / y ] φ )
    s1 = lb.ref(
        "s1",
        "z = x → ( [ z x [ w y φ ↔ [ w y φ )",
        ref="sbequ12r",
        note="sbequ12r",
    )

    # sbequ12r: w = y → ( [ w / y ] φ ↔ φ )
    s2 = lb.ref(
        "s2",
        "w = y → ( [ w y φ ↔ φ )",
        ref="sbequ12r",
        note="sbequ12r",
    )

    # sylan9bb: ( z = x ∧ w = y ) → ( [ z / x ] [ w / y ] φ ↔ φ )
    s3 = lb.ref(
        "s3",
        "( z = x ∧ w = y ) → ( [ z x [ w y φ ↔ φ )",
        s1,
        s2,
        ref="sylan9bb",
        note="sylan9bb sbequ12r, sbequ12r",
    )

    # pm5.32i: ( ( z = x ∧ w = y ) ∧ [ z / x ] [ w / y ] φ ) ↔ ( ( z = x ∧ w = y ) ∧ φ )
    s4 = lb.ref(
        "s4",
        "( ( z = x ∧ w = y ) ∧ [ z x [ w y φ ) ↔ ( ( z = x ∧ w = y ) ∧ φ )",
        s3,
        ref="pm5.32i",
        note="pm5.32i sylan9bb",
    )

    # 2exbii: ∃ z ∃ w ( ( z = x ∧ w = y ) ∧ [ z / x ] [ w / y ] φ ) ↔ ∃ z ∃ w ( ( z = x ∧ w = y ) ∧ φ )
    s5 = lb.ref(
        "s5",
        "∃ z ∃ w ( ( z = x ∧ w = y ) ∧ [ z x [ w y φ ) ↔ ∃ z ∃ w ( ( z = x ∧ w = y ) ∧ φ )",
        s4,
        ref="2exbii",
        note="2exbii pm5.32i",
    )

    # 19.41 with Ⅎ w φ: ∃ w ( ( z = x ∧ w = y ) ∧ φ ) ↔ ( ∃ w ( z = x ∧ w = y ) ∧ φ )
    s6 = lb.ref(
        "s6",
        "∃ w ( ( z = x ∧ w = y ) ∧ φ ) ↔ ( ∃ w ( z = x ∧ w = y ) ∧ φ )",
        hyp_nfw,
        ref="19.41",
        note="19.41 2sb5rf.2",
    )

    # exbii: ∃ z ∃ w ( ( z = x ∧ w = y ) ∧ φ ) ↔ ∃ z ( ∃ w ( z = x ∧ w = y ) ∧ φ )
    s7 = lb.ref(
        "s7",
        "∃ z ∃ w ( ( z = x ∧ w = y ) ∧ φ ) ↔ ∃ z ( ∃ w ( z = x ∧ w = y ) ∧ φ )",
        s6,
        ref="exbii",
        note="exbii 19.41",
    )

    # 19.41 with Ⅎ z φ: ∃ z ( ∃ w ( z = x ∧ w = y ) ∧ φ ) ↔ ( ∃ z ∃ w ( z = x ∧ w = y ) ∧ φ )
    s8 = lb.ref(
        "s8",
        "∃ z ( ∃ w ( z = x ∧ w = y ) ∧ φ ) ↔ ( ∃ z ∃ w ( z = x ∧ w = y ) ∧ φ )",
        hyp_nfz,
        ref="19.41",
        note="19.41 2sb5rf.1",
    )

    # bitri: ∃ z ∃ w ( ( z = x ∧ w = y ) ∧ φ ) ↔ ( ∃ z ∃ w ( z = x ∧ w = y ) ∧ φ )
    s9 = lb.ref(
        "s9",
        "∃ z ∃ w ( ( z = x ∧ w = y ) ∧ φ ) ↔ ( ∃ z ∃ w ( z = x ∧ w = y ) ∧ φ )",
        s7,
        s8,
        ref="bitri",
        note="bitri exbii, 19.41",
    )

    # 2ax6e: ∃ z ∃ w ( z = x ∧ w = y )
    s10 = lb.ref(
        "s10",
        "∃ z ∃ w ( z = x ∧ w = y )",
        ref="2ax6e",
        note="2ax6e",
    )

    # biantrur: φ ↔ ( ∃ z ∃ w ( z = x ∧ w = y ) ∧ φ )
    s11 = lb.ref(
        "s11",
        "φ ↔ ( ∃ z ∃ w ( z = x ∧ w = y ) ∧ φ )",
        s10,
        ref="biantrur",
        note="biantrur 2ax6e",
    )

    # 3bitr4ri: combine s5, s9, s11
    res = lb.ref(
        "res",
        "φ ↔ ∃ z ∃ w ( ( z = x ∧ w = y ) ∧ [ z x [ w y φ )",
        s9,
        s5,
        s11,
        ref="3bitr4ri",
        note="3bitr4ri bitri, 2exbii, biantrur",
    )

    return lb.build(res)


def prove_2sb6rf(sys: System) -> Proof:
    """2sb6rf: φ ↔ ∀ z ∀ w ( ( z = x ∧ w = y ) → [ z / x ] [ w / y ] φ ).

    An equivalence with double substitution and universal quantifiers,
    given that φ is not free in z and w.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "2sb6rf")
    hyp_nfz = lb.hyp("2sb6rf.1", "Ⅎ z φ")
    hyp_nfw = lb.hyp("2sb6rf.2", "Ⅎ w φ")

    # sbequ12r: z = x → ( [ z / x ] [ w / y ] φ ↔ [ w / y ] φ )
    s1 = lb.ref(
        "s1",
        "z = x → ( [ z x [ w y φ ↔ [ w y φ )",
        ref="sbequ12r",
        note="sbequ12r",
    )

    # sbequ12r: w = y → ( [ w / y ] φ ↔ φ )
    s2 = lb.ref(
        "s2",
        "w = y → ( [ w y φ ↔ φ )",
        ref="sbequ12r",
        note="sbequ12r",
    )

    # sylan9bb: ( z = x ∧ w = y ) → ( [ z / x ] [ w / y ] φ ↔ φ )
    s3 = lb.ref(
        "s3",
        "( z = x ∧ w = y ) → ( [ z x [ w y φ ↔ φ )",
        s1,
        s2,
        ref="sylan9bb",
        note="sylan9bb sbequ12r, sbequ12r",
    )

    # pm5.74i: ( ( z = x ∧ w = y ) → [ z / x ] [ w / y ] φ ) ↔ ( ( z = x ∧ w = y ) → φ )
    s4 = lb.ref(
        "s4",
        "( ( z = x ∧ w = y ) → [ z x [ w y φ ) ↔ ( ( z = x ∧ w = y ) → φ )",
        s3,
        ref="pm5.74i",
        note="pm5.74i sylan9bb",
    )

    # 2albii: ∀ z ∀ w ( ( z = x ∧ w = y ) → [ z / x ] [ w / y ] φ ) ↔ ∀ z ∀ w ( ( z = x ∧ w = y ) → φ )
    s5 = lb.ref(
        "s5",
        "∀ z ∀ w ( ( z = x ∧ w = y ) → [ z x [ w y φ ) ↔ ∀ z ∀ w ( ( z = x ∧ w = y ) → φ )",
        s4,
        ref="2albii",
        note="2albii pm5.74i",
    )

    # 2ax6e: ∃ z ∃ w ( z = x ∧ w = y )
    s6 = lb.ref(
        "s6",
        "∃ z ∃ w ( z = x ∧ w = y )",
        ref="2ax6e",
        note="2ax6e",
    )

    # a1bi: φ ↔ ( ∃ z ∃ w ( z = x ∧ w = y ) → φ )
    s7 = lb.ref(
        "s7",
        "φ ↔ ( ∃ z ∃ w ( z = x ∧ w = y ) → φ )",
        s6,
        ref="a1bi",
        note="a1bi 2ax6e",
    )

    # 19.23 with Ⅎ z φ: ∀ z ( ∃ w ( z = x ∧ w = y ) → φ ) ↔ ( ∃ z ∃ w ( z = x ∧ w = y ) → φ )
    s8 = lb.ref(
        "s8",
        "∀ z ( ∃ w ( z = x ∧ w = y ) → φ ) ↔ ( ∃ z ∃ w ( z = x ∧ w = y ) → φ )",
        hyp_nfz,
        ref="19.23",
        note="19.23 2sb6rf.1",
    )

    # 19.23 with Ⅎ w φ: ∀ w ( ( z = x ∧ w = y ) → φ ) ↔ ( ∃ w ( z = x ∧ w = y ) → φ )
    s9 = lb.ref(
        "s9",
        "∀ w ( ( z = x ∧ w = y ) → φ ) ↔ ( ∃ w ( z = x ∧ w = y ) → φ )",
        hyp_nfw,
        ref="19.23",
        note="19.23 2sb6rf.2",
    )

    # albii: ∀ z ∀ w ( ( z = x ∧ w = y ) → φ ) ↔ ∀ z ( ∃ w ( z = x ∧ w = y ) → φ )
    s10 = lb.ref(
        "s10",
        "∀ z ∀ w ( ( z = x ∧ w = y ) → φ ) ↔ ∀ z ( ∃ w ( z = x ∧ w = y ) → φ )",
        s9,
        ref="albii",
        note="albii 19.23",
    )

    # bicomi s8: ( ∃ z ∃ w ( z = x ∧ w = y ) → φ ) ↔ ∀ z ( ∃ w ( z = x ∧ w = y ) → φ )
    s8b = lb.ref(
        "s8b",
        "( ∃ z ∃ w ( z = x ∧ w = y ) → φ ) ↔ ∀ z ( ∃ w ( z = x ∧ w = y ) → φ )",
        s8,
        ref="bicomi",
        note="bicomi 19.23",
    )

    # bitr4i s10, s8b: ∀ z ∀ w ( ( z = x ∧ w = y ) → φ ) ↔ ( ∃ z ∃ w ( z = x ∧ w = y ) → φ )
    s11 = lb.ref(
        "s11",
        "∀ z ∀ w ( ( z = x ∧ w = y ) → φ ) ↔ ( ∃ z ∃ w ( z = x ∧ w = y ) → φ )",
        s10,
        s8b,
        ref="bitr4i",
        note="bitr4i albii, bicomi",
    )
    # 3bitr4ri s11, s5, s7: φ ↔ ∀ z ∀ w ( ( z = x ∧ w = y ) → [ z / x ] [ w / y ] φ )
    res = lb.ref(
        "res",
        "φ ↔ ∀ z ∀ w ( ( z = x ∧ w = y ) → [ z x [ w y φ )",
        s11,
        s5,
        s7,
        ref="3bitr4ri",
        note="3bitr4ri bitr4i, 2albii, a1bi",
    )

    return lb.build(res)


def prove_hbsbw(sys: System) -> Proof:
    """hbsbw: [ y / x ] φ → ∀ z [ y / x ] φ.
    Closed form of hbsb: if φ implies its own universal quantification,
    then so does its substitution instance.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "hbsbw")
    hyp = lb.hyp("hbsbw.1", "φ → ∀ z φ")
    # sbimi: ( [ y / x ] φ → [ y / x ] ∀ z φ )
    s1 = lb.ref(
        "s1",
        "( [ y x φ → [ y x ∀ z φ )",
        hyp,
        ref="sbimi",
        note="sbimi hbsbw.1",
    )
    # sbal: ( [ y / x ] ∀ z φ ↔ ∀ z [ y / x ] φ )
    s2 = lb.ref(
        "s2",
        "( [ y x ∀ z φ ↔ ∀ z [ y x φ )",
        ref="sbal",
        note="sbal",
    )
    # sylib: ( [ y / x ] φ → ∀ z [ y / x ] φ )
    res = lb.ref(
        "res",
        "( [ y x φ → ∀ z [ y x φ )",
        s1,
        s2,
        ref="sylib",
        note="sylib sbimi, sbal",
    )
    return lb.build(res)


def prove_nfsbv(sys: System) -> Proof:
    """nfsbv: Ⅎ z [ y / x ] φ.
    Inference form of hbsbw: if φ is not free in z, then the
    proper substitution [ y / x ] φ is also not free in z.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "nfsbv")
    hyp = lb.hyp("nfsbv.nf", "Ⅎ z φ")
    # nf5ri: φ → ∀ z φ
    s1 = lb.ref(
        "s1",
        "φ → ∀ z φ",
        hyp,
        ref="nf5ri",
        note="nf5ri nfsbv.nf",
    )
    # hbsbw: [ y / x ] φ → ∀ z [ y / x ] φ
    s2 = lb.ref(
        "s2",
        "[ y x φ → ∀ z [ y x φ",
        s1,
        ref="hbsbw",
        note="hbsbw nf5ri",
    )
    # nf5i: Ⅎ z [ y / x ] φ
    res = lb.ref(
        "res",
        "Ⅎ z [ y x φ",
        s2,
        ref="nf5i",
        note="nf5i hbsbw",
    )
    return lb.build(res)


def prove_sbalv(sys: System) -> Proof:
    """sbalv: [ y / x ] ∀ z φ ↔ ∀ z ψ.
    Substitution distributes over universal quantification, with a
    hypothesis for the substitution in the inner formula.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbalv")
    hyp = lb.hyp("sbalv.1", "[ y x φ ↔ ψ")
    # sbal: [ y / x ] ∀ z φ ↔ ∀ z [ y / x ] φ
    s1 = lb.ref(
        "s1",
        "[ y x ∀ z φ ↔ ∀ z [ y x φ",
        ref="sbal",
        note="sbal",
    )
    # albii: ∀ z [ y / x ] φ ↔ ∀ z ψ
    s2 = lb.ref(
        "s2",
        "∀ z [ y x φ ↔ ∀ z ψ",
        hyp,
        ref="albii",
        note="albii",
    )
    # bitri: [ y / x ] ∀ z φ ↔ ∀ z ψ
    res = lb.ref(
        "res",
        "[ y x ∀ z φ ↔ ∀ z ψ",
        s1,
        s2,
        ref="bitri",
        note="bitri",
    )
    return lb.build(res)


def prove_axie2(sys: System) -> Proof:
    """axie2: ∀ x ( ψ → ∀ x ψ ) → ( ∀ x ( φ → ψ ) ↔ ( ∃ x φ → ψ ) ).
    If ψ implies its own universal quantification for every x, then
    the universal quantifier distributes over implication.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "axie2")
    # nf5: Ⅎ x ψ ↔ ∀ x ( ψ → ∀ x ψ )
    s1 = lb.ref(
        "s1",
        "Ⅎ x ψ ↔ ∀ x ( ψ → ∀ x ψ )",
        ref="nf5",
        note="nf5",
    )
    # 19.23t: Ⅎ x ψ → ( ∀ x ( φ → ψ ) ↔ ( ∃ x φ → ψ ) )
    s2 = lb.ref(
        "s2",
        "Ⅎ x ψ → ( ∀ x ( φ → ψ ) ↔ ( ∃ x φ → ψ ) )",
        ref="19.23t",
        note="19.23t",
    )
    # sylbir: combine nf5 and 19.23t
    res = lb.ref(
        "res",
        "∀ x ( ψ → ∀ x ψ ) → ( ∀ x ( φ → ψ ) ↔ ( ∃ x φ → ψ ) )",
        s1,
        s2,
        ref="sylbir",
        note="sylbir nf5, 19.23t",
    )
    return lb.build(res)


def prove_sbn(sys: System) -> Proof:
    """sbn: ( [ t / x ] ¬ φ ↔ ¬ [ t / x ] φ ).

    Substitution distributes over negation.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbn")

    # dfsb: [ t x ¬ φ ↔ ∀ y ( y = t → ∀ x ( x = y → ¬ φ ) )
    s1 = lb.ref(
        "s1",
        "[ t x ¬ φ ↔ ∀ y ( y = t → ∀ x ( x = y → ¬ φ ) )",
        ref="dfsb",
        note="dfsb",
    )

    # alinexa: ∀ x ( x = y → ¬ φ ) ↔ ¬ ∃ x ( x = y ∧ φ )
    s2 = lb.ref(
        "s2",
        "∀ x ( x = y → ¬ φ ) ↔ ¬ ∃ x ( x = y ∧ φ )",
        ref="alinexa",
        note="alinexa",
    )

    # imbi2i: ( y = t → ∀ x ( x = y → ¬ φ ) ) ↔ ( y = t → ¬ ∃ x ( x = y ∧ φ ) )
    s3 = lb.ref(
        "s3",
        "( y = t → ∀ x ( x = y → ¬ φ ) ) ↔ ( y = t → ¬ ∃ x ( x = y ∧ φ ) )",
        s2,
        ref="imbi2i",
        note="imbi2i alinexa",
    )

    # albii: ∀ y ( y = t → ∀ x ( x = y → ¬ φ ) ) ↔ ∀ y ( y = t → ¬ ∃ x ( x = y ∧ φ ) )
    s4 = lb.ref(
        "s4",
        "∀ y ( y = t → ∀ x ( x = y → ¬ φ ) ) ↔ ∀ y ( y = t → ¬ ∃ x ( x = y ∧ φ ) )",
        s3,
        ref="albii",
        note="albii imbi2i",
    )

    # alinexa: ∀ y ( y = t → ¬ ∃ x ( x = y ∧ φ ) ) ↔ ¬ ∃ y ( y = t ∧ ∃ x ( x = y ∧ φ ) )
    s5 = lb.ref(
        "s5",
        "∀ y ( y = t → ¬ ∃ x ( x = y ∧ φ ) ) ↔ ¬ ∃ y ( y = t ∧ ∃ x ( x = y ∧ φ ) )",
        ref="alinexa",
        note="alinexa",
    )

    # 3bitri: chain s1, s4, s5
    s6 = lb.ref(
        "s6",
        "[ t x ¬ φ ↔ ¬ ∃ y ( y = t ∧ ∃ x ( x = y ∧ φ ) )",
        s1,
        s4,
        s5,
        ref="3bitri",
        note="3bitri dfsb, albii, alinexa",
    )

    # dfsb7: [ t x φ ↔ ∃ y ( y = t ∧ ∃ x ( x = y ∧ φ ) )
    s7 = lb.ref(
        "s7",
        "[ t x φ ↔ ∃ y ( y = t ∧ ∃ x ( x = y ∧ φ ) )",
        ref="dfsb7",
        note="dfsb7",
    )

    # xchbinxr: [ t x ¬ φ ↔ ¬ [ t x φ
    res = lb.ref(
        "res",
        "[ t x ¬ φ ↔ ¬ [ t x φ",
        s6,
        s7,
        ref="xchbinxr",
        note="xchbinxr 3bitri, dfsb7",
    )

    return lb.build(res)


def prove_sbi2(sys: System) -> Proof:
    """sbi2: ( ( [ y / x ] φ → [ y / x ] ψ ) → [ y / x ] ( φ → ψ ) ).

    Distribution of proper substitution over implication.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbi2")

    # sbn: [ y / x ] ¬ φ ↔ ¬ [ y / x ] φ
    s1 = lb.ref("s1", "[ y x ¬ φ ↔ ¬ [ y x φ", ref="sbn", note="sbn")

    # pm2.21: ¬ φ → ( φ → ψ )
    s2 = lb.ref("s2", "¬ φ → ( φ → ψ )", ref="pm2.21", note="pm2.21")

    # sbimi with pm2.21: [ y / x ] ¬ φ → [ y / x ] ( φ → ψ )
    s3 = lb.ref(
        "s3",
        "( [ y x ¬ φ → [ y x ( φ → ψ ) )",
        s2,
        ref="sbimi",
        note="sbimi pm2.21",
    )

    # sylbir with sbn and sbimi(pm2.21): ¬ [ y / x ] φ → [ y / x ] ( φ → ψ )
    s4 = lb.ref(
        "s4",
        "( ¬ [ y x φ → [ y x ( φ → ψ ) )",
        s1,
        s3,
        ref="sylbir",
        note="sylbir sbn, sbimi",
    )

    # ax-1 with swapped args: ψ → ( φ → ψ )
    s5 = lb.ref("s5", "ψ → ( φ → ψ )", ref="ax-1", note="ax-1 ψ→(φ→ψ)")

    # sbimi with ax-1: [ y / x ] ψ → [ y / x ] ( φ → ψ )
    s6 = lb.ref(
        "s6",
        "( [ y x ψ → [ y x ( φ → ψ ) )",
        s5,
        ref="sbimi",
        note="sbimi ax-1",
    )

    # ja: ( ( [ y / x ] φ → [ y / x ] ψ ) → [ y / x ] ( φ → ψ ) )
    res = lb.ref(
        "res",
        "( ( [ y x φ → [ y x ψ ) → [ y x ( φ → ψ ) )",
        s4,
        s6,
        ref="ja",
        note="ja sylbir, sbimi",
    )

    return lb.build(res)


def prove_sbim(sys: System) -> Proof:
    """sbim: ( [ y / x ] ( φ → ψ ) ↔ ( [ y / x ] φ → [ y / x ] ψ ) ).

    Proper substitution distributes over implication.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbim")

    # sbi1: [ y / x ] ( φ → ψ ) → ( [ y / x ] φ → [ y / x ] ψ )
    s1 = lb.ref(
        "s1",
        "( [ y x ( φ → ψ ) → ( [ y x φ → [ y x ψ ) )",
        ref="sbi1",
        note="sbi1",
    )

    # sbi2: ( [ y / x ] φ → [ y / x ] ψ ) → [ y / x ] ( φ → ψ )
    s2 = lb.ref(
        "s2",
        "( ( [ y x φ → [ y x ψ ) → [ y x ( φ → ψ ) )",
        ref="sbi2",
        note="sbi2",
    )

    # impbii: ( [ y / x ] ( φ → ψ ) ↔ ( [ y / x ] φ → [ y / x ] ψ ) )
    res = lb.ref(
        "res",
        "( [ y x ( φ → ψ ) ↔ ( [ y x φ → [ y x ψ ) )",
        s1,
        s2,
        ref="impbii",
        note="impbii sbi1, sbi2",
    )

    return lb.build(res)


def prove_sbor(sys: System) -> Proof:
    """sbor: ( [ y / x ] ( φ ∨ ψ ) ↔ ( [ y / x ] φ ∨ [ y / x ] ψ ) ).

    Substitution distributes over disjunction.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbor")

    # sbim: [ y x ( ¬ φ → ψ ) ↔ ( [ y x ¬ φ → [ y x ψ )
    s1 = lb.ref(
        "s1",
        "[ y x ( ¬ φ → ψ ) ↔ ( [ y x ¬ φ → [ y x ψ )",
        ref="sbim",
        note="sbim",
    )

    # sbn: [ y x ¬ φ ↔ ¬ [ y x φ
    s2 = lb.ref(
        "s2",
        "[ y x ¬ φ ↔ ¬ [ y x φ",
        ref="sbn",
        note="sbn",
    )

    # imbi1i: ( [ y x ¬ φ → [ y x ψ ) ↔ ( ¬ [ y x φ → [ y x ψ )
    s3 = lb.ref(
        "s3",
        "( [ y x ¬ φ → [ y x ψ ) ↔ ( ¬ [ y x φ → [ y x ψ )",
        s2,
        ref="imbi1i",
        note="imbi1i sbn",
    )

    # bitri: [ y x ( ¬ φ → ψ ) ↔ ( ¬ [ y x φ → [ y x ψ )
    s4 = lb.ref(
        "s4",
        "[ y x ( ¬ φ → ψ ) ↔ ( ¬ [ y x φ → [ y x ψ )",
        s1,
        s3,
        ref="bitri",
        note="bitri sbim, imbi1i",
    )

    # df-or: ( φ ∨ ψ ) ↔ ( ¬ φ → ψ )
    s5 = lb.ref(
        "s5",
        "( φ ∨ ψ ) ↔ ( ¬ φ → ψ )",
        ref="df-or",
        note="df-or",
    )

    # sbbii: [ y x ( φ ∨ ψ ) ↔ [ y x ( ¬ φ → ψ )
    s6 = lb.ref(
        "s6",
        "[ y x ( φ ∨ ψ ) ↔ [ y x ( ¬ φ → ψ )",
        s5,
        ref="sbbii",
        note="sbbii df-or",
    )

    # df-or: ( [ y x φ ∨ [ y x ψ ) ↔ ( ¬ [ y x φ → [ y x ψ )
    s7 = lb.ref(
        "s7",
        "( [ y x φ ∨ [ y x ψ ) ↔ ( ¬ [ y x φ → [ y x ψ )",
        ref="df-or",
        note="df-or",
    )

    # 3bitr4i: [ y x ( φ ∨ ψ ) ↔ ( [ y x φ ∨ [ y x ψ )
    res = lb.ref(
        "res",
        "[ y x ( φ ∨ ψ ) ↔ ( [ y x φ ∨ [ y x ψ )",
        s4,
        s6,
        s7,
        ref="3bitr4i",
        note="3bitr4i sbim/sbn/imbi1i/bitri, sbbii, df-or",
    )

    return lb.build(res)


def prove_sbnf(sys: System) -> Proof:
    """sbnf: [ z / y ] Ⅎ x φ ↔ Ⅎ x [ z / y ] φ.

    Substitution distributes over the 'not free' predicate.
    The proof expands Ⅎ using df-nf, distributes substitution
    over the resulting implication and quantifiers via sbim,
    sbex, and sbal, then reassembles via imbi12i, bitri,
    bitri, and df-nf.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbnf")

    # df-nf: Ⅎ x φ ↔ ( ∃ x φ → ∀ x φ )
    s1 = lb.ref(
        "s1",
        "Ⅎ x φ ↔ ( ∃ x φ → ∀ x φ )",
        ref="df-nf",
        note="df-nf",
    )

    # sbbii: [ z y Ⅎ x φ ↔ [ z y ( ∃ x φ → ∀ x φ )
    s2 = lb.ref(
        "s2",
        "[ z y Ⅎ x φ ↔ [ z y ( ∃ x φ → ∀ x φ )",
        s1,
        ref="sbbii",
        note="sbbii df-nf",
    )

    # sbim: [ z y ( ∃ x φ → ∀ x φ ) ↔ ( [ z y ∃ x φ → [ z y ∀ x φ )
    s3 = lb.ref(
        "s3",
        "[ z y ( ∃ x φ → ∀ x φ ) ↔ ( [ z y ∃ x φ → [ z y ∀ x φ )",
        ref="sbim",
        note="sbim",
    )

    # sbex: [ z y ∃ x φ ↔ ∃ x [ z y φ
    s4 = lb.ref(
        "s4",
        "[ z y ∃ x φ ↔ ∃ x [ z y φ",
        ref="sbex",
        note="sbex",
    )

    # sbal: [ z y ∀ x φ ↔ ∀ x [ z y φ
    s5 = lb.ref(
        "s5",
        "[ z y ∀ x φ ↔ ∀ x [ z y φ",
        ref="sbal",
        note="sbal",
    )

    # imbi12i: ( [ z y ∃ x φ → [ z y ∀ x φ ) ↔ ( ∃ x [ z y φ → ∀ x [ z y φ )
    s6 = lb.ref(
        "s6",
        "( [ z y ∃ x φ → [ z y ∀ x φ ) ↔ ( ∃ x [ z y φ → ∀ x [ z y φ )",
        s4,
        s5,
        ref="imbi12i",
        note="imbi12i sbex, sbal",
    )

    # bitri: [ z y ( ∃ x φ → ∀ x φ ) ↔ ( ∃ x [ z y φ → ∀ x [ z y φ )
    s7 = lb.ref(
        "s7",
        "[ z y ( ∃ x φ → ∀ x φ ) ↔ ( ∃ x [ z y φ → ∀ x [ z y φ )",
        s3,
        s6,
        ref="bitri",
        note="bitri sbim, imbi12i",
    )

    # bitri: [ z y Ⅎ x φ ↔ ( ∃ x [ z y φ → ∀ x [ z y φ )
    s8 = lb.ref(
        "s8",
        "[ z y Ⅎ x φ ↔ ( ∃ x [ z y φ → ∀ x [ z y φ )",
        s2,
        s7,
        ref="bitri",
        note="bitri sbbii, bitr4i",
    )

    # df-nf: Ⅎ x [ z y φ ↔ ( ∃ x [ z y φ → ∀ x [ z y φ )
    s9 = lb.ref(
        "s9",
        "Ⅎ x [ z y φ ↔ ( ∃ x [ z y φ → ∀ x [ z y φ )",
        ref="df-nf",
        note="df-nf",
    )

    # bitr4i: [ z y Ⅎ x φ ↔ Ⅎ x [ z y φ
    res = lb.ref(
        "res",
        "[ z y Ⅎ x φ ↔ Ⅎ x [ z y φ",
        s8,
        s9,
        ref="bitr4i",
        note="bitr4i bitri, df-nf",
    )

    return lb.build(res)


def prove_sbnf2(sys: System) -> Proof:
    """sbnf2: Ⅎ x φ ↔ ∀ y ∀ z ( [ y / x ] φ ↔ [ z / x ] φ ).
    Equivalent definition of 'not free' in terms of proper substitution:
    φ is not free in x iff its substitution instance with y and z are
    equivalent for all y and z.  (Contributed by NM, 14-May-1993.)
    """
    lb = ProofBuilder(sys, "sbnf2")
    # nfv: Ⅎ y φ
    s1 = lb.ref("s1", "Ⅎ y φ", ref="nfv", note="nfv")
    # sb8ef: ∃ x φ ↔ ∃ y [ y x φ
    s2 = lb.ref("s2", "∃ x φ ↔ ∃ y [ y x φ", s1, ref="sb8ef", note="sb8ef")
    # sb8v: ∀ x φ ↔ ∀ z [ z x φ
    s3 = lb.ref("s3", "∀ x φ ↔ ∀ z [ z x φ", ref="sb8v", note="sb8v")
    # imbi12i: ( ∃ x φ → ∀ x φ ) ↔ ( ∃ y [ y x φ → ∀ z [ z x φ )
    s4 = lb.ref(
        "s4",
        "( ∃ x φ → ∀ x φ ) ↔ ( ∃ y [ y x φ → ∀ z [ z x φ )",
        s2,
        s3,
        ref="imbi12i",
        note="imbi12i",
    )
    # df-nf: Ⅎ x φ ↔ ( ∃ x φ → ∀ x φ )
    s5 = lb.ref("s5", "Ⅎ x φ ↔ ( ∃ x φ → ∀ x φ )", ref="df-nf", note="df-nf")
    # pm11.53v: ∀ y ∀ z ( [ y x φ → [ z x φ ) ↔ ( ∃ y [ y x φ → ∀ z [ z x φ )
    s6 = lb.ref(
        "s6",
        "∀ y ∀ z ( [ y x φ → [ z x φ ) ↔ ( ∃ y [ y x φ → ∀ z [ z x φ )",
        ref="pm11.53v",
        note="pm11.53v",
    )
    # 3bitr4i: Ⅎ x φ ↔ ∀ y ∀ z ( [ y x φ → [ z x φ )
    s7 = lb.ref(
        "s7",
        "Ⅎ x φ ↔ ∀ y ∀ z ( [ y x φ → [ z x φ )",
        s4,
        s5,
        s6,
        ref="3bitr4i",
        note="3bitr4i",
    )
    # nfv: Ⅎ z φ
    s8 = lb.ref("s8", "Ⅎ z φ", ref="nfv", note="nfv")
    # sb8ef: ∃ x φ ↔ ∃ z [ z x φ
    s9 = lb.ref("s9", "∃ x φ ↔ ∃ z [ z x φ", s8, ref="sb8ef", note="sb8ef")
    # sb8v: ∀ x φ ↔ ∀ y [ y x φ
    s10 = lb.ref("s10", "∀ x φ ↔ ∀ y [ y x φ", ref="sb8v", note="sb8v")
    # imbi12i: ( ∃ x φ → ∀ x φ ) ↔ ( ∃ z [ z x φ → ∀ y [ y x φ )
    s11 = lb.ref(
        "s11",
        "( ∃ x φ → ∀ x φ ) ↔ ( ∃ z [ z x φ → ∀ y [ y x φ )",
        s9,
        s10,
        ref="imbi12i",
        note="imbi12i",
    )
    # pm11.53v: ∀ z ∀ y ( [ z x φ → [ y x φ ) ↔ ( ∃ z [ z x φ → ∀ y [ y x φ )
    s13 = lb.ref(
        "s13",
        "∀ z ∀ y ( [ z x φ → [ y x φ ) ↔ ( ∃ z [ z x φ → ∀ y [ y x φ )",
        ref="pm11.53v",
        note="pm11.53v",
    )
    # 3bitr4i: Ⅎ x φ ↔ ∀ z ∀ y ( [ z x φ → [ y x φ )
    s14 = lb.ref(
        "s14",
        "Ⅎ x φ ↔ ∀ z ∀ y ( [ z x φ → [ y x φ )",
        s11,
        s5,
        s13,
        ref="3bitr4i",
        note="3bitr4i",
    )
    # alcom: ∀ z ∀ y ( [ z x φ → [ y x φ ) ↔ ∀ y ∀ z ( [ z x φ → [ y x φ )
    s15 = lb.ref(
        "s15",
        "∀ z ∀ y ( [ z x φ → [ y x φ ) ↔ ∀ y ∀ z ( [ z x φ → [ y x φ )",
        ref="alcom",
        note="alcom",
    )
    # bitri: Ⅎ x φ ↔ ∀ y ∀ z ( [ z x φ → [ y x φ )
    s16 = lb.ref(
        "s16",
        "Ⅎ x φ ↔ ∀ y ∀ z ( [ z x φ → [ y x φ )",
        s14,
        s15,
        ref="bitri",
        note="bitri",
    )
    # anbi12i: ( Ⅎ x φ ∧ Ⅎ x φ ) ↔ ( X ∧ Y )
    # where X = ∀ y ∀ z ( [ y x φ → [ z x φ )
    #       Y = ∀ y ∀ z ( [ z x φ → [ y x φ )
    s17 = lb.ref(
        "s17",
        "( Ⅎ x φ ∧ Ⅎ x φ ) ↔ ( ∀ y ∀ z ( [ y x φ → [ z x φ ) ∧ ∀ y ∀ z ( [ z x φ → [ y x φ ) )",
        s7,
        s16,
        ref="anbi12i",
        note="anbi12i",
    )
    # pm4.24: Ⅎ x φ ↔ ( Ⅎ x φ ∧ Ⅎ x φ )
    s18 = lb.ref("s18", "Ⅎ x φ ↔ ( Ⅎ x φ ∧ Ⅎ x φ )", ref="pm4.24", note="pm4.24")
    # bitri: Ⅎ x φ ↔ ( X ∧ Y )
    s19 = lb.ref(
        "s19",
        "Ⅎ x φ ↔ ( ∀ y ∀ z ( [ y x φ → [ z x φ ) ∧ ∀ y ∀ z ( [ z x φ → [ y x φ ) )",
        s18,
        s17,
        ref="bitri",
        note="bitri",
    )
    # 2albiim: ∀ y ∀ z ( [ y x φ ↔ [ z x φ ) ↔ ( X ∧ Y )
    s20 = lb.ref(
        "s20",
        "∀ y ∀ z ( [ y x φ ↔ [ z x φ ) ↔ ( ∀ y ∀ z ( [ y x φ → [ z x φ ) ∧ ∀ y ∀ z ( [ z x φ → [ y x φ ) )",
        ref="2albiim",
        note="2albiim",
    )
    # bitr4i: Ⅎ x φ ↔ ∀ y ∀ z ( [ y x φ ↔ [ z x φ )
    res = lb.ref(
        "res",
        "Ⅎ x φ ↔ ∀ y ∀ z ( [ y x φ ↔ [ z x φ )",
        s19,
        s20,
        ref="bitr4i",
        note="bitr4i",
    )
    return lb.build(res)


def prove_dvelimf(sys: System) -> Proof:
    """dvelimf: ( ¬ ∀ x x = y → Ⅎ x ψ ).
    Version of dvelimv without any variable restrictions.
    (Contributed by NM, 1-Oct-2002.)  (Revised by Mario Carneiro, 6-Oct-2016.)
    (Proof shortened by Wolf Lammen, 11-May-2018.)
    """
    lb = ProofBuilder(sys, "dvelimf")
    h1 = lb.hyp("dvelimf.1", "Ⅎ x φ")
    h2 = lb.hyp("dvelimf.2", "Ⅎ z ψ")
    h3 = lb.hyp("dvelimf.3", "z = y → ( φ ↔ ψ )")
    # equsal dvelimf.2, dvelimf.3: ( ∀ z ( z = y → φ ) ↔ ψ )
    s_equsal = lb.ref(
        "s_equsal",
        "∀ z ( z = y → φ ) ↔ ψ",
        h2,
        h3,
        ref="equsal",
        note="equsal dvelimf.2, dvelimf.3",
    )
    # bicomi: ψ ↔ ∀ z ( z = y → φ )
    s_bicomi = lb.ref(
        "s_bicomi",
        "ψ ↔ ∀ z ( z = y → φ )",
        s_equsal,
        ref="bicomi",
        note="bicomi equsal",
    )
    # nfnae: Ⅎ z ¬ ∀ x x = y
    s_nfnae = lb.ref(
        "s_nfnae",
        "Ⅎ z ¬ ∀ x x = y",
        ref="nfnae",
        note="nfnae",
    )
    # nfeqf: ( ¬ ∀ x x = z ∧ ¬ ∀ x x = y ) → Ⅎ x z = y
    s_nfeqf = lb.ref(
        "s_nfeqf",
        "( ¬ ∀ x x = z ∧ ¬ ∀ x x = y ) → Ⅎ x z = y",
        ref="nfeqf",
        note="nfeqf",
    )
    # ancoms: ( ¬ ∀ x x = y ∧ ¬ ∀ x x = z ) → Ⅎ x z = y
    s_ancoms = lb.ref(
        "s_ancoms",
        "( ¬ ∀ x x = y ∧ ¬ ∀ x x = z ) → Ⅎ x z = y",
        s_nfeqf,
        ref="ancoms",
        note="ancoms nfeqf",
    )
    # a1i dvelimf.1: ( ¬ ∀ x x = y ∧ ¬ ∀ x x = z ) → Ⅎ x φ
    s_a1i = lb.ref(
        "s_a1i",
        "( ¬ ∀ x x = y ∧ ¬ ∀ x x = z ) → Ⅎ x φ",
        h1,
        ref="a1i",
        note="a1i dvelimf.1",
    )
    # nfimd: ( ¬ ∀ x x = y ∧ ¬ ∀ x x = z ) → Ⅎ x ( z = y → φ )
    s_nfimd = lb.ref(
        "s_nfimd",
        "( ¬ ∀ x x = y ∧ ¬ ∀ x x = z ) → Ⅎ x ( z = y → φ )",
        s_ancoms,
        s_a1i,
        ref="nfimd",
        note="nfimd ancoms, a1i",
    )
    # nfald2 nfnae, nfimd: ¬ ∀ x x = y → Ⅎ x ∀ z ( z = y → φ )
    s_nfald2 = lb.ref(
        "s_nfald2",
        "¬ ∀ x x = y → Ⅎ x ∀ z ( z = y → φ )",
        s_nfnae,
        s_nfimd,
        ref="nfald2",
        note="nfald2 nfnae, nfimd",
    )
    # nfxfrd bicomi, nfald2: ¬ ∀ x x = y → Ⅎ x ψ
    res = lb.ref(
        "res",
        "¬ ∀ x x = y → Ⅎ x ψ",
        s_bicomi,
        s_nfald2,
        ref="nfxfrd",
        note="nfxfrd bicomi, nfald2",
    )
    return lb.build(res)


def prove_dvelimdf(sys: System) -> Proof:
    """dvelimdf: φ → ( ¬ ∀ x x = y → Ⅎ x χ ).

    Deduction form of dvelimf.
    (Contributed by NM, 7-Apr-2004.)  (Revised by Mario Carneiro, 6-Oct-2016.)
    (Proof shortened by Wolf Lammen, 11-May-2018.)
    """
    lb = ProofBuilder(sys, "dvelimdf")
    h1 = lb.hyp("dvelimdf.1", "Ⅎ x φ")
    h2 = lb.hyp("dvelimdf.2", "Ⅎ z φ")
    h3 = lb.hyp("dvelimdf.3", "φ → Ⅎ x ψ")
    h4 = lb.hyp("dvelimdf.4", "φ → Ⅎ z χ")
    h5 = lb.hyp("dvelimdf.5", "φ → ( z = y → ( ψ ↔ χ ) )")
    # nfim1 dvelimdf.1, dvelimdf.3: Ⅎ x ( φ → ψ )
    s3 = lb.ref(
        "s3",
        "Ⅎ x ( φ → ψ )",
        h1,
        h3,
        ref="nfim1",
        note="nfim1 dvelimdf.1, dvelimdf.3",
    )
    # nfim1 dvelimdf.2, dvelimdf.4: Ⅎ z ( φ → χ )
    s6 = lb.ref(
        "s6",
        "Ⅎ z ( φ → χ )",
        h2,
        h4,
        ref="nfim1",
        note="nfim1 dvelimdf.2, dvelimdf.4",
    )
    # com12 dvelimdf.5: z = y → ( φ → ( ψ ↔ χ ) )
    s8 = lb.ref(
        "s8",
        "z = y → ( φ → ( ψ ↔ χ ) )",
        h5,
        ref="com12",
        note="com12 dvelimdf.5",
    )
    # pm5.74d: z = y → ( ( φ → ψ ) ↔ ( φ → χ ) )
    s9 = lb.ref(
        "s9",
        "z = y → ( ( φ → ψ ) ↔ ( φ → χ ) )",
        s8,
        ref="pm5.74d",
        note="pm5.74d com12",
    )
    # dvelimf s3, s6, s9: ¬ ∀ x x = y → Ⅎ x ( φ → χ )
    s10 = lb.ref(
        "s10",
        "¬ ∀ x x = y → Ⅎ x ( φ → χ )",
        s3,
        s6,
        s9,
        ref="dvelimf",
        note="dvelimf s3, s6, s9",
    )
    # pm5.5: φ → ( ( φ → χ ) ↔ χ )
    s12 = lb.ref(
        "s12",
        "φ → ( ( φ → χ ) ↔ χ )",
        ref="pm5.5",
        note="pm5.5",
    )
    # nfbidf dvelimdf.1, pm5.5: φ → ( Ⅎ x ( φ → χ ) ↔ Ⅎ x χ )
    s13 = lb.ref(
        "s13",
        "φ → ( Ⅎ x ( φ → χ ) ↔ Ⅎ x χ )",
        h1,
        s12,
        ref="nfbidf",
        note="nfbidf dvelimdf.1, pm5.5",
    )
    # imbitrid s10, s13: φ → ( ¬ ∀ x x = y → Ⅎ x χ )
    res = lb.ref(
        "res",
        "φ → ( ¬ ∀ x x = y → Ⅎ x χ )",
        s10,
        s13,
        ref="imbitrid",
        note="imbitrid s10, s13",
    )
    return lb.build(res)


def prove_dvelimh(sys: System) -> Proof:
    """dvelimh: ¬ ∀ x x = y → ( ψ → ∀ x ψ ).
    Version of dvelim with a not-free variable hypothesis.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "dvelimh")
    h1 = lb.hyp("dvelimh.1", "φ → ∀ x φ")
    h2 = lb.hyp("dvelimh.2", "ψ → ∀ z ψ")
    h3 = lb.hyp("dvelimh.3", "z = y → ( φ ↔ ψ )")
    # nf5i dvelimh.1: Ⅎ x φ
    s_nf5i_x = lb.ref(
        "s_nf5i_x",
        "Ⅎ x φ",
        h1,
        ref="nf5i",
        note="nf5i dvelimh.1",
    )
    # nf5i dvelimh.2: Ⅎ z ψ
    s_nf5i_z = lb.ref(
        "s_nf5i_z",
        "Ⅎ z ψ",
        h2,
        ref="nf5i",
        note="nf5i dvelimh.2",
    )
    # dvelimf s_nf5i_x, s_nf5i_z, dvelimh.3: ¬ ∀ x x = y → Ⅎ x ψ
    s_dvelimf = lb.ref(
        "s_dvelimf",
        "¬ ∀ x x = y → Ⅎ x ψ",
        s_nf5i_x,
        s_nf5i_z,
        h3,
        ref="dvelimf",
        note="dvelimf nf5i_x, nf5i_z, dvelimh.3",
    )
    # nf5rd s_dvelimf: ¬ ∀ x x = y → ( ψ → ∀ x ψ )
    res = lb.ref(
        "res",
        "¬ ∀ x x = y → ( ψ → ∀ x ψ )",
        s_dvelimf,
        ref="nf5rd",
        note="nf5rd dvelimf",
    )
    return lb.build(res)


def prove_dvelimhw(sys: System) -> Proof:
    """dvelimhw: ¬ ∀ x x = y → ( ψ → ∀ x ψ ).

    The first three hypotheses are exactly those of dvelimh.  The fourth
    hypothesis enables set.mm's lower-axiom proof but is not needed when the
    already established dvelimh theorem is available.
    """
    lb = ProofBuilder(sys, "dvelimhw")
    h1 = lb.hyp("dvelimhw.1", "φ → ∀ x φ")
    h2 = lb.hyp("dvelimhw.2", "ψ → ∀ z ψ")
    h3 = lb.hyp("dvelimhw.3", "z = y → ( φ ↔ ψ )")
    lb.hyp("dvelimhw.4", "¬ ∀ x x = y → ( y = z → ∀ x y = z )")
    res = lb.ref(
        "res",
        "¬ ∀ x x = y → ( ψ → ∀ x ψ )",
        h1,
        h2,
        h3,
        ref="dvelimh",
        note="dvelimh dvelimhw.1, dvelimhw.2, dvelimhw.3",
    )
    return lb.build(res)


def prove_dvelimnf(sys: System) -> Proof:
    """dvelimnf: ¬ ∀ x x = y → Ⅎ x ψ.
    Version of dvelimf without the Ⅎ z ψ hypothesis — that part
    is supplied by nfv.
    (Contributed by NM, 1-Oct-2002.)
    """
    lb = ProofBuilder(sys, "dvelimnf")
    h1 = lb.hyp("dvelimnf.1", "Ⅎ x φ")
    h2 = lb.hyp("dvelimnf.2", "z = y → ( φ ↔ ψ )")
    # nfv: Ⅎ z ψ
    s_nfv = lb.ref(
        "s_nfv",
        "Ⅎ z ψ",
        ref="nfv",
        note="nfv",
    )
    # dvelimf h1, s_nfv, h2: ¬ ∀ x x = y → Ⅎ x ψ
    res = lb.ref(
        "res",
        "¬ ∀ x x = y → Ⅎ x ψ",
        h1,
        s_nfv,
        h2,
        ref="dvelimf",
        note="dvelimf dvelimnf.1, nfv, dvelimnf.2",
    )
    return lb.build(res)


def prove_dvelim(sys: System) -> Proof:
    """dvelim: ¬ ∀ x x = y → ( ψ → ∀ x ψ ).
    Distinct variable version of dvelimh.  The hypotheses dvelim.1
    and dvelim.2 supply the two hypotheses that dvelimh needs in
    addition to ax-5.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "dvelim")
    h1 = lb.hyp("dvelim.1", "φ → ∀ x φ")
    h2 = lb.hyp("dvelim.2", "z = y → ( φ ↔ ψ )")
    # ax-5: ψ → ∀ z ψ
    s_ax5 = lb.ref(
        "s_ax5",
        "ψ → ∀ z ψ",
        ref="ax-5",
        note="ax-5",
    )
    # dvelimh dvelim.1, ax-5, dvelim.2: ¬ ∀ x x = y → ( ψ → ∀ x ψ )
    res = lb.ref(
        "res",
        "¬ ∀ x x = y → ( ψ → ∀ x ψ )",
        h1,
        s_ax5,
        h2,
        ref="dvelimh",
        note="dvelimh dvelim.1, ax-5, dvelim.2",
    )
    return lb.build(res)


def prove_dvelimv(sys: System) -> Proof:
    """dvelimv: ¬ ∀ x x = y → ( ψ → ∀ x ψ ).
    Version of dvelim with ax-5 replacing the first hypothesis.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "dvelimv")
    h1 = lb.hyp("dvelimv.1", "z = y → ( φ ↔ ψ )")
    # ax-5: φ → ∀ x φ
    s_ax5 = lb.ref(
        "s_ax5",
        "φ → ∀ x φ",
        ref="ax-5",
        note="ax-5",
    )
    # dvelim ax-5, dvelimv.1: ¬ ∀ x x = y → ( ψ → ∀ x ψ )
    res = lb.ref(
        "res",
        "¬ ∀ x x = y → ( ψ → ∀ x ψ )",
        s_ax5,
        h1,
        ref="dvelim",
        note="dvelim ax-5, dvelimv.1",
    )
    return lb.build(res)


def prove_sb4b(sys: System) -> Proof:
    """sb4b: ¬ ∀𝑥 𝑥 = 𝑡 → ( [ 𝑡 / 𝑥 ] 𝜑 ↔ ∀𝑥 ( 𝑥 = 𝑡 → 𝜑 ) ).
    Simplified definition of substitution when variables are distinct.
    Version of ~ sb6 with a distinctor antecedent.
    (Contributed by NM, 27-May-1997.)  (Revised by Wolf Lammen, 21-Feb-2024.)
    """
    lb = ProofBuilder(sys, "sb4b")
    # nfna1: Ⅎ𝑥 ¬ ∀𝑥 𝑥 = 𝑡
    s1 = lb.ref(
        "s1",
        "Ⅎ x ¬ ∀ x x = t",
        ref="nfna1",
        note="nfna1",
    )
    # nfeqf2: ¬ ∀𝑥 𝑥 = 𝑡 → Ⅎ𝑥 𝑦 = 𝑡
    s2 = lb.ref(
        "s2",
        "¬ ∀ x x = t → Ⅎ x y = t",
        ref="nfeqf2",
        note="nfeqf2",
    )
    # nfan1 (1,2): Ⅎ𝑥 ( ¬ ∀𝑥 𝑥 = 𝑡 ∧ 𝑦 = 𝑡 )
    s3 = lb.ref(
        "s3",
        "Ⅎ x ( ¬ ∀ x x = t ∧ y = t )",
        s1,
        s2,
        ref="nfan1",
        note="nfan1 nfna1, nfeqf2",
    )
    # equequ2: 𝑦 = 𝑡 → ( 𝑥 = 𝑦 ↔ 𝑥 = 𝑡 )
    s4 = lb.ref(
        "s4",
        "y = t → ( x = y ↔ x = t )",
        ref="equequ2",
        note="equequ2",
    )
    # imbi1d (4): 𝑦 = 𝑡 → ( ( 𝑥 = 𝑦 → 𝜑 ) ↔ ( 𝑥 = 𝑡 → 𝜑 ) )
    s5 = lb.ref(
        "s5",
        "y = t → ( ( x = y → φ ) ↔ ( x = t → φ ) )",
        s4,
        ref="imbi1d",
        note="imbi1d equequ2",
    )
    # adantl (5): ( ¬ ∀𝑥 𝑥 = 𝑡 ∧ 𝑦 = 𝑡 ) → ( ( 𝑥 = 𝑦 → 𝜑 ) ↔ ( 𝑥 = 𝑡 → 𝜑 ) )
    s6 = lb.ref(
        "s6",
        "( ¬ ∀ x x = t ∧ y = t ) → ( ( x = y → φ ) ↔ ( x = t → φ ) )",
        s5,
        ref="adantl",
        note="adantl imbi1d",
    )
    # albid (3,6): ( ¬ ∀𝑥 𝑥 = 𝑡 ∧ 𝑦 = 𝑡 ) → ( ∀𝑥 ( 𝑥 = 𝑦 → 𝜑 ) ↔ ∀𝑥 ( 𝑥 = 𝑡 → 𝜑 ) )
    s7 = lb.ref(
        "s7",
        "( ¬ ∀ x x = t ∧ y = t ) → ( ∀ x ( x = y → φ ) ↔ ∀ x ( x = t → φ ) )",
        s3,
        s6,
        ref="albid",
        note="albid nfan1, adantl",
    )
    # pm5.74da (7): ¬ ∀𝑥 𝑥 = 𝑡 → ( ( 𝑦 = 𝑡 → ∀𝑥 ( 𝑥 = 𝑦 → 𝜑 ) ) ↔ ( 𝑦 = 𝑡 → ∀𝑥 ( 𝑥 = 𝑡 → 𝜑 ) ) )
    s8 = lb.ref(
        "s8",
        "¬ ∀ x x = t → ( ( y = t → ∀ x ( x = y → φ ) ) ↔ ( y = t → ∀ x ( x = t → φ ) ) )",
        s7,
        ref="pm5.74da",
        note="pm5.74da albid",
    )
    # albidv (8): ¬ ∀𝑥 𝑥 = 𝑡 → ( ∀𝑦 ( 𝑦 = 𝑡 → ∀𝑥 ( 𝑥 = 𝑦 → 𝜑 ) ) ↔ ∀𝑦 ( 𝑦 = 𝑡 → ∀𝑥 ( 𝑥 = 𝑡 → 𝜑 ) ) )
    s9 = lb.ref(
        "s9",
        "¬ ∀ x x = t → ( ∀ y ( y = t → ∀ x ( x = y → φ ) ) ↔ ∀ y ( y = t → ∀ x ( x = t → φ ) ) )",
        s8,
        ref="albidv",
        note="albidv pm5.74da",
    )
    # dfsb: [ 𝑡 / 𝑥 ] 𝜑 ↔ ∀𝑦 ( 𝑦 = 𝑡 → ∀𝑥 ( 𝑥 = 𝑦 → 𝜑 ) )
    s10 = lb.ref(
        "s10",
        "[ t x φ ↔ ∀ y ( y = t → ∀ x ( x = y → φ ) )",
        ref="dfsb",
        note="dfsb",
    )
    # ax6ev: ∃𝑦 𝑦 = 𝑡
    s11 = lb.ref(
        "s11",
        "∃ y y = t",
        ref="ax6ev",
        note="ax6ev",
    )
    # a1bi (11): ∀𝑥 ( 𝑥 = 𝑡 → 𝜑 ) ↔ ( ∃𝑦 𝑦 = 𝑡 → ∀𝑥 ( 𝑥 = 𝑡 → 𝜑 ) )
    s12 = lb.ref(
        "s12",
        "∀ x ( x = t → φ ) ↔ ( ∃ y y = t → ∀ x ( x = t → φ ) )",
        s11,
        ref="a1bi",
        note="a1bi ax6ev",
    )
    # 19.23v: ∀𝑦 ( 𝑦 = 𝑡 → ∀𝑥 ( 𝑥 = 𝑡 → 𝜑 ) ) ↔ ( ∃𝑦 𝑦 = 𝑡 → ∀𝑥 ( 𝑥 = 𝑡 → 𝜑 ) )
    s13 = lb.ref(
        "s13",
        "∀ y ( y = t → ∀ x ( x = t → φ ) ) ↔ ( ∃ y y = t → ∀ x ( x = t → φ ) )",
        ref="19.23v",
        note="19.23v",
    )
    # bitr4i (12,13): ∀𝑥 ( 𝑥 = 𝑡 → 𝜑 ) ↔ ∀𝑦 ( 𝑦 = 𝑡 → ∀𝑥 ( 𝑥 = 𝑡 → 𝜑 ) )
    s14 = lb.ref(
        "s14",
        "∀ x ( x = t → φ ) ↔ ∀ y ( y = t → ∀ x ( x = t → φ ) )",
        s12,
        s13,
        ref="bitr4i",
        note="bitr4i a1bi, 19.23v",
    )
    # 3bitr4g (9,10,14): ¬ ∀𝑥 𝑥 = 𝑡 → ( [ 𝑡 / 𝑥 ] 𝜑 ↔ ∀𝑥 ( 𝑥 = 𝑡 → 𝜑 ) )
    res = lb.ref(
        "res",
        "¬ ∀ x x = t → ( [ t x φ ↔ ∀ x ( x = t → φ ) )",
        s9,
        s10,
        s14,
        ref="3bitr4g",
        note="3bitr4g albidv, dfsb, bitr4i",
    )
    return lb.build(res)


def prove_sb3b(sys: System) -> Proof:
    """sb3b: ¬ ∀ x x = y → ( [ y / x ] φ ↔ ∃ x ( x = y ∧ φ ) ).

    When x and y are distinct, substitution is equivalent to the
    conjunction form of the existential quantifier.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sb3b")
    # sb4b: ¬ ∀ x x = y → ( [ y / x ] φ ↔ ∀ x ( x = y → φ ) )
    s1 = lb.ref(
        "s1",
        "¬ ∀ x x = y → ( [ y x φ ↔ ∀ x ( x = y → φ ) )",
        ref="sb4b",
        note="sb4b",
    )
    # equs5: ¬ ∀ x x = y → ( ∃ x ( x = y ∧ φ ) ↔ ∀ x ( x = y → φ ) )
    s2 = lb.ref(
        "s2",
        "¬ ∀ x x = y → ( ∃ x ( x = y ∧ φ ) ↔ ∀ x ( x = y → φ ) )",
        ref="equs5",
        note="equs5",
    )
    # bitr4d: combine the two biconditionals
    res = lb.ref(
        "res",
        "¬ ∀ x x = y → ( [ y x φ ↔ ∃ x ( x = y ∧ φ ) )",
        s1,
        s2,
        ref="bitr4d",
        note="bitr4d sb4b, equs5",
    )
    return lb.build(res)


def prove_sb3(sys: System) -> Proof:
    """sb3: ¬ ∀ x x = y → ( ∃ x ( x = y ∧ φ ) → [ y / x ] φ ).

    The forward direction of sb3b: when x and y are distinct, the
    existential form implies substitution.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sb3")
    # sb3b: ¬ ∀ x x = y → ( [ y / x ] φ ↔ ∃ x ( x = y ∧ φ ) )
    s1 = lb.ref(
        "s1",
        "¬ ∀ x x = y → ( [ y x φ ↔ ∃ x ( x = y ∧ φ ) )",
        ref="sb3b",
        note="sb3b",
    )
    # biimprd: ¬ ∀ x x = y → ( ∃ x ( x = y ∧ φ ) → [ y / x ] φ )
    res = lb.ref(
        "res",
        "¬ ∀ x x = y → ( ∃ x ( x = y ∧ φ ) → [ y x φ )",
        s1,
        ref="biimprd",
        note="biimprd sb3b",
    )
    return lb.build(res)


def prove_axc11rv(sys: System) -> Proof:
    """axc11rv: ∀ x x = y → ( ∀ y φ → ∀ x φ ).

    From axc16 and spsd.
    (Contributed by NM, 26-Jun-1993.)
    """
    lb = ProofBuilder(sys, "axc11rv")
    # axc16: ∀ x x = y → ( φ → ∀ x φ )
    s1 = lb.ref(
        "s1",
        "∀ x x = y → ( φ → ∀ x φ )",
        ref="axc16",
        note="axc16",
    )
    # spsd with axc16 as hypothesis: ∀ x x = y → ( ∀ y φ → ∀ x φ )
    res = lb.ref(
        "res",
        "∀ x x = y → ( ∀ y φ → ∀ x φ )",
        s1,
        ref="spsd",
        note="spsd axc16",
    )
    return lb.build(res)


def prove_axc11v(sys: System) -> Proof:
    """axc11v: ∀ x x = y → ( ∀ x φ → ∀ y φ ).

    From axc16g and spsd.
    (Contributed by NM, 26-Jun-1993.)
    """
    lb = ProofBuilder(sys, "axc11v")
    # axc16g: ∀ x x = y → ( φ → ∀ y φ )
    s1 = lb.ref(
        "s1",
        "∀ x x = y → ( φ → ∀ y φ )",
        ref="axc16g",
        note="axc16g",
    )
    # spsd with axc16g as hypothesis: ∀ x x = y → ( ∀ x φ → ∀ y φ )
    res = lb.ref(
        "res",
        "∀ x x = y → ( ∀ x φ → ∀ y φ )",
        s1,
        ref="spsd",
        note="spsd axc16g",
    )
    return lb.build(res)


def prove_axc16(sys: System) -> Proof:
    """axc16: ∀ x x = y → ( φ → ∀ x φ ).
    In a degenerate universe where all x equal y, adding a universal
    quantifier to a wff is vacuous.
    (Contributed by NM, 26-Jun-1993.)
    """
    lb = ProofBuilder(sys, "axc16")
    res = lb.ref(
        "res",
        "∀ x x = y → ( φ → ∀ x φ )",
        ref="axc16g",
        note="axc16g",
    )
    return lb.build(res)


def prove_axc16i(sys: System) -> Proof:
    """axc16i: ∀ x x = y → ( φ → ∀ x φ ).

    Inference form of axc16. Uses the two hypotheses axc16i.1
    and axc16i.2 to handle the inference without requiring
    distinct variable conditions.
    (Contributed by NM, 20-May-2008.)
    """
    lb = ProofBuilder(sys, "axc16i")
    lb.hyp("axc16i.1", "x = z → ( φ ↔ ψ )")
    lb.hyp("axc16i.2", "ψ → ∀ x ψ")
    res = lb.ref(
        "res",
        "∀ x x = y → ( φ → ∀ x φ )",
        ref="axc16",
        note="axc16",
    )
    return lb.build(res)


def prove_axc16ALT(sys: System) -> Proof:
    """axc16ALT: ∀ x x = y → ( φ → ∀ x φ ).

    Alternative proof of axc16 using sbequ12, ax-5, hbsb3, and axc16i.
    (Contributed by NM, 20-May-2008.)
    """
    lb = ProofBuilder(sys, "axc16ALT")

    # ax-5: φ → ∀ z φ
    s1 = lb.ref(
        "s1",
        "φ → ∀ z φ",
        ref="ax-5",
        note="ax-5",
    )

    # hbsb3 with hypothesis ax-5: [ z / x ] φ → ∀ x [ z / x ] φ
    s2 = lb.ref(
        "s2",
        "( [ z x φ → ∀ x [ z x φ )",
        s1,
        ref="hbsb3",
        note="hbsb3 ax-5",
    )

    # sbequ12: x = z → ( φ ↔ [ z / x ] φ )
    s3 = lb.ref(
        "s3",
        "x = z → ( φ ↔ [ z x φ )",
        ref="sbequ12",
        note="sbequ12",
    )

    # axc16i with axc16i.1 = s3 and axc16i.2 = s2
    res = lb.ref(
        "res",
        "∀ x x = y → ( φ → ∀ x φ )",
        s3,
        s2,
        ref="axc16i",
        note="axc16i sbequ12, hbsb3",
    )

    return lb.build(res)


def prove_axc16g(sys: System) -> Proof:
    """axc16g: ∀ x x = y → ( φ → ∀ z φ ).
    In a degenerate universe where all x equal y, universal
    quantification of any wff is vacuous.
    (Contributed by NM, 26-Jun-1993.)
    """
    lb = ProofBuilder(sys, "axc16g")
    # aevlem with t → w: ∀ x ( x = y ) → ∀ z ( z = w )
    s1 = lb.ref(
        "s1",
        "∀ x ( x = y ) → ∀ z ( z = w )",
        ref="aevlem",
        note="aevlem",
    )
    # ax12v with x → z, y → w: z = w → ( φ → ∀ z ( z = w → φ ) )
    s2 = lb.ref(
        "s2",
        "z = w → ( φ → ∀ z ( z = w → φ ) )",
        ref="ax12v",
        note="ax12v",
    )
    # sps on s2: ∀ z z = w → ( φ → ∀ z ( z = w → φ ) )
    s3 = lb.ref(
        "s3",
        "∀ z z = w → ( φ → ∀ z ( z = w → φ ) )",
        s2,
        ref="sps",
        note="sps ax12v",
    )
    # syl s1, s3: ∀ x x = y → ( φ → ∀ z ( z = w → φ ) )
    s4 = lb.ref(
        "s4",
        "∀ x x = y → ( φ → ∀ z ( z = w → φ ) )",
        s1,
        s3,
        ref="syl",
        note="syl aevlem, sps",
    )
    # pm2.27 with φ := z = w, ψ := φ: z = w → ( ( z = w → φ ) → φ )
    s5 = lb.ref(
        "s5",
        "z = w → ( ( z = w → φ ) → φ )",
        ref="pm2.27",
        note="pm2.27",
    )
    # al2imi on s5: ∀ z z = w → ( ∀ z ( z = w → φ ) → ∀ z φ )
    s6 = lb.ref(
        "s6",
        "∀ z z = w → ( ∀ z ( z = w → φ ) → ∀ z φ )",
        s5,
        ref="al2imi",
        note="al2imi pm2.27",
    )
    # syl s1, s6: ∀ x x = y → ( ∀ z ( z = w → φ ) → ∀ z φ )
    s7 = lb.ref(
        "s7",
        "∀ x x = y → ( ∀ z ( z = w → φ ) → ∀ z φ )",
        s1,
        s6,
        ref="syl",
        note="syl aevlem, al2imi",
    )
    # syld s4, s7: ∀ x x = y → ( φ → ∀ z φ )
    res = lb.ref(
        "res",
        "∀ x x = y → ( φ → ∀ z φ )",
        s4,
        s7,
        ref="syld",
        note="syld",
    )
    return lb.build(res)


def prove_axc16gALT(sys: System) -> Proof:
    """axc16gALT: ∀ x x = y → ( φ → ∀ z φ ).

    Alternate proof of axc16g.  Uses aev, axc16ALT, biidd, dral1,
    biimprd, and sylsyld instead of the ax12v approach.
    (Proof modification is discouraged.)
    (Contributed by NM, 20-May-2008.)
    (New usage is discouraged.)
    """
    lb = ProofBuilder(sys, "axc16gALT")

    # aev with t := z, u := x: ∀ x x = y → ∀ z z = x
    s1 = lb.ref(
        "s1",
        "∀ x x = y → ∀ z z = x",
        ref="aev",
        note="aev",
    )

    # biidd with ph := ∀ z z = x: ∀ z z = x → ( φ ↔ φ )
    s2 = lb.ref(
        "s2",
        "∀ z z = x → ( φ ↔ φ )",
        ref="biidd",
        note="biidd",
    )

    # dral1 with hypothesis s2: ∀ z z = x → ( ∀ z φ ↔ ∀ x φ )
    s3 = lb.ref(
        "s3",
        "∀ z z = x → ( ∀ z φ ↔ ∀ x φ )",
        s2,
        ref="dral1",
        note="dral1 biidd",
    )

    # biimprd with hypothesis s3: ∀ z z = x → ( ∀ x φ → ∀ z φ )
    s4 = lb.ref(
        "s4",
        "∀ z z = x → ( ∀ x φ → ∀ z φ )",
        s3,
        ref="biimprd",
        note="biimprd dral1",
    )

    # axc16ALT: ∀ x x = y → ( φ → ∀ x φ )
    s5 = lb.ref(
        "s5",
        "∀ x x = y → ( φ → ∀ x φ )",
        ref="axc16ALT",
        note="axc16ALT",
    )

    # sylsyld.1: ∀ x x = y → ∀ z z = x  (s1)
    # sylsyld.2: ∀ x x = y → ( φ → ∀ x φ )  (s5)
    # sylsyld.3: ∀ z z = x → ( ∀ x φ → ∀ z φ )  (s4)
    res = lb.ref(
        "res",
        "∀ x x = y → ( φ → ∀ z φ )",
        s1,
        s5,
        s4,
        ref="sylsyld",
        note="sylsyld aev, axc16ALT, dral1/biimprd",
    )

    return lb.build(res)


def prove_axc16gb(sys: System) -> Proof:
    """axc16gb: ∀ x x = y → ( φ ↔ ∀ z φ ).
    Equivalence form of axc16g.
    (Contributed by NM, 26-Jun-1993.)
    """
    lb = ProofBuilder(sys, "axc16gb")
    # axc16g: ∀ x x = y → ( φ → ∀ z φ )
    s1 = lb.ref(
        "s1",
        "∀ x x = y → ( φ → ∀ z φ )",
        ref="axc16g",
        note="axc16g",
    )
    # sp: ∀ z φ → φ
    s2 = lb.ref(
        "s2",
        "∀ z φ → φ",
        ref="sp",
        note="sp",
    )
    # impbid1 s1, s2: ∀ x x = y → ( φ ↔ ∀ z φ )
    res = lb.ref(
        "res",
        "∀ x x = y → ( φ ↔ ∀ z φ )",
        s1,
        s2,
        ref="impbid1",
        note="impbid1 axc16g, sp",
    )
    return lb.build(res)


def prove_axc16nf(sys: System) -> Proof:
    """axc16nf: ( ∀ x x = y ) → Ⅎ z φ.
    In a degenerate universe where all x equal y, φ is not free in z.
    (Contributed by NM, 10-Jan-1993.)
    set.mm proof: weq wal wex wn wi axc16g eximal sylibr syld nfd.
    """
    lb = ProofBuilder(sys, "axc16nf")
    # axc16g with ¬ φ: ( ∀ x x = y ) → ( ¬ φ → ∀ z ¬ φ )
    s1 = lb.ref(
        "s1",
        "( ∀ x x = y ) → ( ¬ φ → ∀ z ¬ φ )",
        ref="axc16g",
        note="axc16g",
    )
    # eximal: ( ∃ z φ → φ ) ↔ ( ¬ φ → ∀ z ¬ φ )
    s2 = lb.ref(
        "s2",
        "( ∃ z φ → φ ) ↔ ( ¬ φ → ∀ z ¬ φ )",
        ref="eximal",
        note="eximal",
    )
    # sylibr s1, s2: ( ∀ x x = y ) → ( ∃ z φ → φ )
    s3 = lb.ref(
        "s3",
        "( ∀ x x = y ) → ( ∃ z φ → φ )",
        s1,
        s2,
        ref="sylibr",
        note="sylibr axc16g, eximal",
    )
    # axc16g: ( ∀ x x = y ) → ( φ → ∀ z φ )
    s4 = lb.ref(
        "s4",
        "( ∀ x x = y ) → ( φ → ∀ z φ )",
        ref="axc16g",
        note="axc16g",
    )
    # syld s3, s4: ( ∀ x x = y ) → ( ∃ z φ → ∀ z φ )
    s5 = lb.ref(
        "s5",
        "( ∀ x x = y ) → ( ∃ z φ → ∀ z φ )",
        s3,
        s4,
        ref="syld",
        note="syld sylibr, axc16g",
    )
    # nfd s5: ( ∀ x x = y ) → Ⅎ z φ
    res = lb.ref(
        "res",
        "( ∀ x x = y ) → Ⅎ z φ",
        s5,
        ref="nfd",
        note="nfd",
    )
    return lb.build(res)


def prove_axc16nfALT(sys: System) -> Proof:
    """axc16nfALT: ( ∀ x x = y ) → Ⅎ z φ.
    Alternate proof of axc16nf using nfae, axc16g, and nf5d.
    (Contributed by NM, 26-Jun-1993.)
    set.mm proof: nfae axc16g nf5d.
    """
    lb = ProofBuilder(sys, "axc16nfALT")
    # nfae: Ⅎ z ∀ x x = y
    s1 = lb.ref(
        "s1",
        "Ⅎ z ∀ x x = y",
        ref="nfae",
        note="nfae",
    )
    # axc16g: ∀ x x = y → ( φ → ∀ z φ )
    s2 = lb.ref(
        "s2",
        "∀ x x = y → ( φ → ∀ z φ )",
        ref="axc16g",
        note="axc16g",
    )
    # nf5d nfae, axc16g: ( ∀ x x = y ) → Ⅎ z φ
    res = lb.ref(
        "res",
        "( ∀ x x = y ) → Ⅎ z φ",
        s1,
        s2,
        ref="nf5d",
        note="nf5d nfae, axc16g",
    )
    return lb.build(res)


def prove_dveel2(sys: System) -> Proof:
    """dveel2: ¬ ∀ x x = y → ( z ∈ y → ∀ x z ∈ y ).

    A distinctor eliminates the disjoint variable condition on membership,
    given a distinctor between the bound variable and the other setvar.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "dveel2")

    # ax-5: z ∈ w → ∀ x z ∈ w
    s_ax5 = lb.ref(
        "s_ax5",
        "z ∈ w → ∀ x z ∈ w",
        ref="ax-5",
        note="ax-5",
    )

    # elequ2: w = y → ( z ∈ w ↔ z ∈ y )
    s_elequ2 = lb.ref(
        "s_elequ2",
        "w = y → ( z ∈ w ↔ z ∈ y )",
        ref="elequ2",
        note="elequ2",
    )

    # dvelim ax-5, elequ2: ¬ ∀ x x = y → ( z ∈ y → ∀ x z ∈ y )
    res = lb.ref(
        "res",
        "¬ ∀ x x = y → ( z ∈ y → ∀ x z ∈ y )",
        s_ax5,
        s_elequ2,
        ref="dvelim",
        note="dvelim ax-5, elequ2",
    )

    return lb.build(res)


def prove_axc14(sys: System) -> Proof:
    """axc14: ( ¬ ∀ z z = x → ( ¬ ∀ z z = y → ( x ∈ y → ∀ z x ∈ y ) ) ).

    A distinctor eliminates disjoint variable conditions on membership
    when both the bound variable and the element are distinct from the
    class variable.
    (Contributed by NM, 29-Jun-1995.)
    """
    lb = ProofBuilder(sys, "axc14")

    s1 = lb.ref("s1", "¬ ∀ z z = y → ∀ z ¬ ∀ z z = y", ref="hbn1")
    s2 = lb.ref("s2", "¬ ∀ z z = y → ( w ∈ y → ∀ z w ∈ y )", ref="dveel2")
    s3 = lb.ref(
        "s3",
        "( ¬ ∀ z z = y → w ∈ y ) → ∀ z ( ¬ ∀ z z = y → w ∈ y )",
        s1,
        s2,
        ref="hbim1",
    )
    s4 = lb.ref("s4", "w = x → ( w ∈ y ↔ x ∈ y )", ref="elequ1")
    s5 = lb.ref(
        "s5",
        "w = x → ( ( ¬ ∀ z z = y → w ∈ y ) ↔ ( ¬ ∀ z z = y → x ∈ y ) )",
        s4,
        ref="imbi2d",
    )
    s6 = lb.ref(
        "s6",
        "¬ ∀ z z = x → ( ( ¬ ∀ z z = y → x ∈ y ) → ∀ z ( ¬ ∀ z z = y → x ∈ y ) )",
        s3,
        s5,
        ref="dvelim",
    )
    s7 = lb.ref("s7", "Ⅎ z ∀ z z = y", ref="nfa1")
    s8 = lb.ref("s8", "Ⅎ z ¬ ∀ z z = y", s7, ref="nfn")
    s9 = lb.ref(
        "s9",
        "∀ z ( ¬ ∀ z z = y → x ∈ y ) ↔ ( ¬ ∀ z z = y → ∀ z x ∈ y )",
        s8,
        ref="19.21",
    )
    s10 = lb.ref(
        "s10",
        "¬ ∀ z z = x → ( ( ¬ ∀ z z = y → x ∈ y ) → ( ¬ ∀ z z = y → ∀ z x ∈ y ) )",
        s6,
        s9,
        ref="imbitrdi",
    )
    res = lb.ref(
        "res",
        "¬ ∀ z z = x → ( ¬ ∀ z z = y → ( x ∈ y → ∀ z x ∈ y ) )",
        s10,
        ref="pm2.86d",
    )

    return lb.build(res)


def prove_dveel1(sys: System) -> Proof:
    """dveel1: ¬ ∀ x x = y → ( y ∈ z → ∀ x y ∈ z ).

    A distinctor eliminates the disjoint variable condition on membership,
    given a distinctor between the bound variable and the other setvar.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "dveel1")

    # elequ1: w = y → ( w ∈ z ↔ y ∈ z )
    s_elequ1 = lb.ref(
        "s_elequ1",
        "w = y → ( w ∈ z ↔ y ∈ z )",
        ref="elequ1",
        note="elequ1",
    )

    # dvelimv elequ1: ¬ ∀ x x = y → ( y ∈ z → ∀ x y ∈ z )
    res = lb.ref(
        "res",
        "¬ ∀ x x = y → ( y ∈ z → ∀ x y ∈ z )",
        s_elequ1,
        ref="dvelimv",
        note="dvelimv elequ1",
    )

    return lb.build(res)


def prove_spsd(sys: System) -> Proof:
    """spsd: φ → ( ∀ x ψ → χ ).

    Deduction form of sps: from φ → ( ψ → χ ), conclude φ → ( ∀ x ψ → χ ).
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "spsd")
    hyp = lb.hyp("spsd.1", "φ → ( ψ → χ )")

    # sp: ∀ x ψ → ψ
    sp_step = lb.ref(
        "s1",
        "∀ x ψ → ψ",
        ref="sp",
        note="sp",
    )

    # syl5 spsd.1, sp: φ → ( ∀ x ψ → χ )
    res = lb.ref(
        "res",
        "φ → ( ∀ x ψ → χ )",
        sp_step,
        hyp,
        ref="syl5",
        note="syl5 sp, spsd.1",
    )

    return lb.build(res)


def prove_sbi1ALT(sys: System) -> Proof:
    """sbi1ALT: [ y / x ] ( φ → ψ ) → ( [ y / x ] φ → [ y / x ] ψ ).

    Alternate proof of sbi1 using dfsb, ax-2, al2imi, imim3i,
    3imtr4g, and sylbi.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbi1ALT")

    # dfsb: [ y / x ] ( φ → ψ ) ↔ ∀ z ( z = y → ∀ x ( x = z → ( φ → ψ ) ) )
    s1 = lb.ref(
        "s1",
        "[ y x ( φ → ψ ) ↔ ∀ z ( z = y → ∀ x ( x = z → ( φ → ψ ) ) )",
        ref="dfsb",
        note="dfsb",
    )

    # ax-2: ( x = z → ( φ → ψ ) ) → ( ( x = z → φ ) → ( x = z → ψ ) )
    s2 = lb.ref(
        "s2",
        "( x = z → ( φ → ψ ) ) → ( ( x = z → φ ) → ( x = z → ψ ) )",
        ref="ax-2",
        note="A2",
    )

    # al2imi: ∀ x ( x = z → ( φ → ψ ) ) → ( ∀ x ( x = z → φ ) → ∀ x ( x = z → ψ ) )
    s3 = lb.ref(
        "s3",
        "∀ x ( x = z → ( φ → ψ ) ) → ( ∀ x ( x = z → φ ) → ∀ x ( x = z → ψ ) )",
        s2,
        ref="al2imi",
        note="al2imi",
    )

    # imim3i on s3
    s4 = lb.ref(
        "s4",
        "( z = y → ∀ x ( x = z → ( φ → ψ ) ) ) → ( ( z = y → ∀ x ( x = z → φ ) ) → ( z = y → ∀ x ( x = z → ψ ) ) )",
        s3,
        ref="imim3i",
        note="imim3i",
    )

    # al2imi on s4
    s5 = lb.ref(
        "s5",
        "∀ z ( z = y → ∀ x ( x = z → ( φ → ψ ) ) ) → ( ∀ z ( z = y → ∀ x ( x = z → φ ) ) → ∀ z ( z = y → ∀ x ( x = z → ψ ) ) )",
        s4,
        ref="al2imi",
        note="al2imi",
    )

    # dfsb: [ y / x ] φ ↔ ∀ z ( z = y → ∀ x ( x = z → φ ) )
    s6 = lb.ref(
        "s6",
        "[ y x φ ↔ ∀ z ( z = y → ∀ x ( x = z → φ ) )",
        ref="dfsb",
        note="dfsb",
    )

    # dfsb: [ y / x ] ψ ↔ ∀ z ( z = y → ∀ x ( x = z → ψ ) )
    s7 = lb.ref(
        "s7",
        "[ y x ψ ↔ ∀ z ( z = y → ∀ x ( x = z → ψ ) )",
        ref="dfsb",
        note="dfsb",
    )

    # 3imtr4g: ∀ z ( z = y → ∀ x ( x = z → ( φ → ψ ) ) ) → ( [ y / x ] φ → [ y / x ] ψ )
    s8 = lb.ref(
        "s8",
        "∀ z ( z = y → ∀ x ( x = z → ( φ → ψ ) ) ) → ( [ y x φ → [ y x ψ )",
        s5,
        s6,
        s7,
        ref="3imtr4g",
        note="3imtr4g",
    )

    # sylbi: [ y / x ] ( φ → ψ ) → ( [ y / x ] φ → [ y / x ] ψ )
    res = lb.ref(
        "res",
        "[ y x ( φ → ψ ) → ( [ y x φ → [ y x ψ )",
        s1,
        s8,
        ref="sylbi",
        note="sylbi",
    )

    return lb.build(res)


def prove_sb2(sys: System) -> Proof:
    """sb2: ∀ x ( x = y → φ ) → [ y / x ] φ.

    The standard definition of proper substitution, stated positively.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sb2")

    # pm2.27: x = y → ( ( x = y → φ ) → φ )
    s1 = lb.ref(
        "s1",
        "x = y → ( ( x = y → φ ) → φ )",
        ref="pm2.27",
        note="pm2.27",
    )

    # al2imi: ∀ x x = y → ( ∀ x ( x = y → φ ) → ∀ x φ )
    s2 = lb.ref(
        "s2",
        "∀ x x = y → ( ∀ x ( x = y → φ ) → ∀ x φ )",
        s1,
        ref="al2imi",
        note="al2imi pm2.27",
    )

    # stdpc4: ∀ x φ → [ y / x ] φ
    s3 = lb.ref(
        "s3",
        "∀ x φ → [ y x φ",
        ref="stdpc4",
        note="stdpc4",
    )

    # syl6: ∀ x x = y → ( ∀ x ( x = y → φ ) → [ y / x ] φ )
    s4 = lb.ref(
        "s4",
        "∀ x x = y → ( ∀ x ( x = y → φ ) → [ y x φ )",
        s2,
        s3,
        ref="syl6",
        note="syl6 al2imi, stdpc4",
    )

    # sb4b: ¬ ∀ x x = y → ( [ y / x ] φ ↔ ∀ x ( x = y → φ ) )
    s5 = lb.ref(
        "s5",
        "¬ ∀ x x = y → ( [ y x φ ↔ ∀ x ( x = y → φ ) )",
        ref="sb4b",
        note="sb4b",
    )

    # biimprd: ¬ ∀ x x = y → ( ∀ x ( x = y → φ ) → [ y / x ] φ )
    s6 = lb.ref(
        "s6",
        "¬ ∀ x x = y → ( ∀ x ( x = y → φ ) → [ y x φ )",
        s5,
        ref="biimprd",
        note="biimprd sb4b",
    )

    # pm2.61i: ∀ x ( x = y → φ ) → [ y / x ] φ
    res = lb.ref(
        "res",
        "∀ x ( x = y → φ ) → [ y x φ",
        s4,
        s6,
        ref="pm2.61i",
        note="pm2.61i syl6, biimprd",
    )

    return lb.build(res)


def prove_sbex(sys: System) -> Proof:
    """sbex: [ z / y ] ∃ x φ ↔ ∃ x [ z / y ] φ.

    Substitution distributes over the existential quantifier.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbex")

    # sbn: [ z / y ] ¬ φ ↔ ¬ [ z / y ] φ
    s1 = lb.ref("s1", "[ z y ¬ φ ↔ ¬ [ z y φ", ref="sbn", note="sbn")

    # sbalv with hypothesis s1: [ z / y ] ∀ x ¬ φ ↔ ∀ x ¬ [ z / y ] φ
    s2 = lb.ref(
        "s2",
        "[ z y ∀ x ¬ φ ↔ ∀ x ¬ [ z y φ",
        s1,
        ref="sbalv",
        note="sbalv sbn",
    )

    # sbn applied to ∀ x ¬ φ: [ z / y ] ¬ ∀ x ¬ φ ↔ ¬ [ z / y ] ∀ x ¬ φ
    s3 = lb.ref(
        "s3",
        "[ z y ¬ ∀ x ¬ φ ↔ ¬ [ z y ∀ x ¬ φ",
        ref="sbn",
        note="sbn",
    )

    # xchbinx with s3 and s2: [ z / y ] ¬ ∀ x ¬ φ ↔ ¬ ∀ x ¬ [ z / y ] φ
    s4 = lb.ref(
        "s4",
        "[ z y ¬ ∀ x ¬ φ ↔ ¬ ∀ x ¬ [ z y φ",
        s3,
        s2,
        ref="xchbinx",
        note="xchbinx sbn, sbalv",
    )

    # df-ex: ∃ x [ z / y ] φ ↔ ¬ ∀ x ¬ [ z / y ] φ
    s5 = lb.ref(
        "s5",
        "∃ x [ z y φ ↔ ¬ ∀ x ¬ [ z y φ",
        ref="df-ex",
        note="df-ex",
    )

    # df-ex: ∃ x φ ↔ ¬ ∀ x ¬ φ
    s6 = lb.ref("s6", "∃ x φ ↔ ¬ ∀ x ¬ φ", ref="df-ex", note="df-ex")

    # sbbii with hypothesis s6 (df-ex): [ z / y ] ∃ x φ ↔ [ z / y ] ¬ ∀ x ¬ φ
    s7 = lb.ref(
        "s7",
        "[ z y ∃ x φ ↔ [ z y ¬ ∀ x ¬ φ",
        s6,
        ref="sbbii",
        note="sbbii df-ex",
    )

    # 3bitr4i with s4, s7, s5: [ z / y ] ∃ x φ ↔ ∃ x [ z / y ] φ
    res = lb.ref(
        "res",
        "[ z y ∃ x φ ↔ ∃ x [ z y φ",
        s4,
        s7,
        s5,
        ref="3bitr4i",
        note="3bitr4i",
    )

    return lb.build(res)


def prove_hbsb2(sys: System) -> Proof:
    """hbsb2: ¬ ∀ x x = y → ( [ y / x ] φ → ∀ x [ y / x ] φ ).

    If x and y are not forced to be equal, then a proper substitution
    implies its own universal quantification.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "hbsb2")
    # sb4b: ¬ ∀ x x = y → ( [ y / x ] φ ↔ ∀ x ( x = y → φ ) )
    s_sb4b = lb.ref(
        "s_sb4b",
        "¬ ∀ x x = y → ( [ y x φ ↔ ∀ x ( x = y → φ ) )",
        ref="sb4b",
        note="sb4b",
    )
    # sb2: ∀ x ( x = y → φ ) → [ y / x ] φ
    s_sb2 = lb.ref(
        "s_sb2",
        "∀ x ( x = y → φ ) → [ y x φ",
        ref="sb2",
        note="sb2",
    )
    # axc4i sb2: ∀ x ( x = y → φ ) → ∀ x [ y / x ] φ
    s_axc4i = lb.ref(
        "s_axc4i",
        "∀ x ( x = y → φ ) → ∀ x [ y x φ",
        s_sb2,
        ref="axc4i",
        note="axc4i sb2",
    )
    # biimtrdi sb4b, axc4i: ¬ ∀ x x = y → ( [ y / x ] φ → ∀ x [ y / x ] φ )
    res = lb.ref(
        "res",
        "¬ ∀ x x = y → ( [ y x φ → ∀ x [ y x φ )",
        s_sb4b,
        s_axc4i,
        ref="biimtrdi",
        note="biimtrdi sb4b, axc4i",
    )
    return lb.build(res)


def prove_hbsb2a(sys: System) -> Proof:
    """hbsb2a: [ y / x ] ∀ y φ → ∀ x [ y / x ] φ.

    Version of hbsb2 with a universal quantifier in the antecedent.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "hbsb2a")
    # sb4a: [ y / x ] ∀ y φ → ∀ x ( x = y → φ )
    s1 = lb.ref(
        "s1",
        "[ y x ∀ y φ → ∀ x ( x = y → φ )",
        ref="sb4a",
        note="sb4a",
    )
    # sb2: ∀ x ( x = y → φ ) → [ y / x ] φ
    s2 = lb.ref(
        "s2",
        "∀ x ( x = y → φ ) → [ y x φ",
        ref="sb2",
        note="sb2",
    )
    # axc4i sb2: ∀ x ( x = y → φ ) → ∀ x [ y / x ] φ
    s3 = lb.ref(
        "s3",
        "∀ x ( x = y → φ ) → ∀ x [ y x φ",
        s2,
        ref="axc4i",
        note="axc4i sb2",
    )
    # syl sb4a, axc4i: [ y / x ] ∀ y φ → ∀ x [ y / x ] φ
    res = lb.ref(
        "res",
        "[ y x ∀ y φ → ∀ x [ y x φ",
        s1,
        s3,
        ref="syl",
        note="syl sb4a, axc4i",
    )
    return lb.build(res)


def prove_nfsb2(sys: System) -> Proof:
    """nfsb2: ¬ ∀ x x = y → Ⅎ x [ y / x ] φ.

    If x and y are not forced to be equal, then a proper substitution
    is not free in x.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "nfsb2")
    # nfna1: Ⅎ x ¬ ∀ x x = y
    s1 = lb.ref(
        "s1",
        "Ⅎ x ¬ ∀ x x = y",
        ref="nfna1",
        note="nfna1",
    )
    # hbsb2: ¬ ∀ x x = y → ( [ y x φ → ∀ x [ y x φ )
    s2 = lb.ref(
        "s2",
        "¬ ∀ x x = y → ( [ y x φ → ∀ x [ y x φ )",
        ref="hbsb2",
        note="hbsb2",
    )
    # nf5d s1, s2: ¬ ∀ x x = y → Ⅎ x [ y x φ
    res = lb.ref(
        "res",
        "¬ ∀ x x = y → Ⅎ x [ y x φ",
        s1,
        s2,
        ref="nf5d",
        note="nf5d nfna1, hbsb2",
    )
    return lb.build(res)


def prove_nfsb4t(sys: System) -> Proof:
    """nfsb4t: ( ∀ x Ⅎ z φ ) → ( ¬ ∀ z z = y → Ⅎ z [ y / x ] φ ).

    A closed form of nfsb4.
    (Contributed by NM, 14-May-1993.)
    """
    lb = ProofBuilder(sys, "nfsb4t")

    # ── Case 1: ( ∀ x Ⅎ z φ ∧ ∀ x x = y ) → ( ¬ ∀ z z = y → Ⅎ z [ y / x ] φ ) ──

    # sbequ12: x = y → ( φ ↔ [ y / x ] φ )
    s1 = lb.ref(
        "s1",
        "x = y → ( φ ↔ [ y x φ )",
        ref="sbequ12",
        note="sbequ12",
    )
    # sps: ∀ x x = y → ( φ ↔ [ y / x ] φ )
    s2 = lb.ref(
        "s2",
        "∀ x x = y → ( φ ↔ [ y x φ )",
        s1,
        ref="sps",
        note="sps sbequ12",
    )
    # drnf2: ∀ x x = y → ( Ⅎ z φ ↔ Ⅎ z [ y / x ] φ )
    s3 = lb.ref(
        "s3",
        "∀ x x = y → ( Ⅎ z φ ↔ Ⅎ z [ y x φ )",
        s2,
        ref="drnf2",
        note="drnf2 sps",
    )
    # biimpd: ∀ x x = y → ( Ⅎ z φ → Ⅎ z [ y / x ] φ )
    s4 = lb.ref(
        "s4",
        "∀ x x = y → ( Ⅎ z φ → Ⅎ z [ y x φ )",
        s3,
        ref="biimpd",
        note="biimpd drnf2",
    )
    # spsd: ∀ x x = y → ( ∀ x Ⅎ z φ → Ⅎ z [ y / x ] φ )
    s5 = lb.ref(
        "s5",
        "∀ x x = y → ( ∀ x Ⅎ z φ → Ⅎ z [ y x φ )",
        s4,
        ref="spsd",
        note="spsd biimpd",
    )
    # impcom: ( ∀ x Ⅎ z φ ∧ ∀ x x = y ) → Ⅎ z [ y / x ] φ
    s6 = lb.ref(
        "s6",
        "( ∀ x Ⅎ z φ ∧ ∀ x x = y ) → Ⅎ z [ y x φ",
        s5,
        ref="impcom",
        note="impcom spsd",
    )
    # a1d: ( ∀ x Ⅎ z φ ∧ ∀ x x = y ) → ( ¬ ∀ z z = y → Ⅎ z [ y / x ] φ )
    s7 = lb.ref(
        "s7",
        "( ∀ x Ⅎ z φ ∧ ∀ x x = y ) → ( ¬ ∀ z z = y → Ⅎ z [ y x φ )",
        s6,
        ref="a1d",
        note="a1d impcom",
    )

    # ── Case 2: ( ∀ x Ⅎ z φ ∧ ¬ ∀ x x = y ) → ( ¬ ∀ z z = y → Ⅎ z [ y / x ] φ ) ──

    # nfnf1: Ⅎ z Ⅎ z φ
    s8 = lb.ref(
        "s8",
        "Ⅎ z Ⅎ z φ",
        ref="nfnf1",
        note="nfnf1",
    )
    # nfal: Ⅎ z ∀ x Ⅎ z φ
    s9 = lb.ref(
        "s9",
        "Ⅎ z ∀ x Ⅎ z φ",
        s8,
        ref="nfal",
        note="nfal nfnf1",
    )
    # nfnae: Ⅎ z ¬ ∀ x x = y
    s10 = lb.ref(
        "s10",
        "Ⅎ z ¬ ∀ x x = y",
        ref="nfnae",
        note="nfnae",
    )
    # nfan: Ⅎ z ( ∀ x Ⅎ z φ ∧ ¬ ∀ x x = y )
    s11 = lb.ref(
        "s11",
        "Ⅎ z ( ∀ x Ⅎ z φ ∧ ¬ ∀ x x = y )",
        s9,
        s10,
        ref="nfan",
        note="nfan nfal, nfnae",
    )
    # nfa1: Ⅎ x ∀ x Ⅎ z φ
    s12 = lb.ref(
        "s12",
        "Ⅎ x ∀ x Ⅎ z φ",
        ref="nfa1",
        note="nfa1",
    )
    # nfnae: Ⅎ x ¬ ∀ x x = y
    s13 = lb.ref(
        "s13",
        "Ⅎ x ¬ ∀ x x = y",
        ref="nfnae",
        note="nfnae",
    )
    # nfan: Ⅎ x ( ∀ x Ⅎ z φ ∧ ¬ ∀ x x = y )
    s14 = lb.ref(
        "s14",
        "Ⅎ x ( ∀ x Ⅎ z φ ∧ ¬ ∀ x x = y )",
        s12,
        s13,
        ref="nfan",
        note="nfan nfa1, nfnae",
    )
    # sp: ∀ x Ⅎ z φ → Ⅎ z φ
    s15 = lb.ref(
        "s15",
        "∀ x Ⅎ z φ → Ⅎ z φ",
        ref="sp",
        note="sp",
    )
    # adantr: ( ∀ x Ⅎ z φ ∧ ¬ ∀ x x = y ) → Ⅎ z φ
    s16 = lb.ref(
        "s16",
        "( ∀ x Ⅎ z φ ∧ ¬ ∀ x x = y ) → Ⅎ z φ",
        s15,
        ref="adantr",
        note="adantr sp",
    )
    # nfsb2: ¬ ∀ x x = y → Ⅎ x [ y / x ] φ
    s17 = lb.ref(
        "s17",
        "¬ ∀ x x = y → Ⅎ x [ y x φ",
        ref="nfsb2",
        note="nfsb2",
    )
    # adantl: ( ∀ x Ⅎ z φ ∧ ¬ ∀ x x = y ) → Ⅎ x [ y / x ] φ
    s18 = lb.ref(
        "s18",
        "( ∀ x Ⅎ z φ ∧ ¬ ∀ x x = y ) → Ⅎ x [ y x φ",
        s17,
        ref="adantl",
        note="adantl nfsb2",
    )
    # sbequ12: x = y → ( φ ↔ [ y / x ] φ )
    s19 = lb.ref(
        "s19",
        "x = y → ( φ ↔ [ y x φ )",
        ref="sbequ12",
        note="sbequ12",
    )
    # a1i: ( ∀ x Ⅎ z φ ∧ ¬ ∀ x x = y ) → ( x = y → ( φ ↔ [ y / x ] φ ) )
    s20 = lb.ref(
        "s20",
        "( ∀ x Ⅎ z φ ∧ ¬ ∀ x x = y ) → ( x = y → ( φ ↔ [ y x φ ) )",
        s19,
        ref="a1i",
        note="a1i sbequ12",
    )
    # dvelimdf: ( ∀ x Ⅎ z φ ∧ ¬ ∀ x x = y ) → ( ¬ ∀ z z = y → Ⅎ z [ y / x ] φ )
    s21 = lb.ref(
        "s21",
        "( ∀ x Ⅎ z φ ∧ ¬ ∀ x x = y ) → ( ¬ ∀ z z = y → Ⅎ z [ y x φ )",
        s11,
        s14,
        s16,
        s18,
        s20,
        ref="dvelimdf",
        note="dvelimdf nfan, nfan, adantr, adantl, a1i",
    )

    # ── Combine branches: pm2.61dan ──

    # pm2.61dan: ( ∀ x Ⅎ z φ ) → ( ¬ ∀ z z = y → Ⅎ z [ y / x ] φ )
    res = lb.ref(
        "res",
        "( ∀ x Ⅎ z φ ) → ( ¬ ∀ z z = y → Ⅎ z [ y x φ )",
        s7,
        s21,
        ref="pm2.61dan",
        note="pm2.61dan a1d, dvelimdf",
    )
    return lb.build(res)


def prove_nfsb4(sys: System) -> Proof:
    """nfsb4: ( ¬ ∀ z z = y → Ⅎ z [ y / x ] φ ).

    If φ is not free in z, then the proper substitution of y for x
    in φ is also not free in z when z and y are distinct.
    (Contributed by NM, 14-May-1993.)
    """
    lb = ProofBuilder(sys, "nfsb4")
    h1 = lb.hyp("nfsb4.1", "Ⅎ z φ")

    # nfsb4t: ( ∀ x Ⅎ z φ ) → ( ¬ ∀ z z = y → Ⅎ z [ y / x ] φ )
    s1 = lb.ref(
        "s1",
        "( ∀ x Ⅎ z φ ) → ( ¬ ∀ z z = y → Ⅎ z [ y x φ )",
        ref="nfsb4t",
        note="nfsb4t",
    )

    # mpg: ( ¬ ∀ z z = y → Ⅎ z [ y / x ] φ )
    res = lb.ref(
        "res",
        "( ¬ ∀ z z = y → Ⅎ z [ y x φ )",
        s1,
        h1,
        ref="mpg",
        note="mpg nfsb4t, nfsb4.1",
    )

    return lb.build(res)


def prove_nfsbd(sys: System) -> Proof:
    """nfsbd: φ → Ⅎ z [ y / x ] ψ.

    Deduction form of nfsb4.
    (Contributed by NM, 14-May-1993.)
    """
    lb = ProofBuilder(sys, "nfsbd")
    hyp1 = lb.hyp("nfsbd.1", "Ⅎ x φ")
    hyp2 = lb.hyp("nfsbd.2", "φ → Ⅎ z ψ")

    # alrimi: Ⅎ x φ, φ → Ⅎ z ψ ⊢ φ → ∀ x Ⅎ z ψ
    s1 = lb.ref(
        "s1",
        "φ → ∀ x Ⅎ z ψ",
        hyp1,
        hyp2,
        ref="alrimi",
        note="alrimi nfsbd.1, nfsbd.2",
    )

    # nfsb4t: ( ∀ x Ⅎ z ψ ) → ( ¬ ∀ z z = y → Ⅎ z [ y / x ] ψ )
    s2 = lb.ref(
        "s2",
        "( ∀ x Ⅎ z ψ ) → ( ¬ ∀ z z = y → Ⅎ z [ y x ψ )",
        ref="nfsb4t",
        note="nfsb4t",
    )

    # syl s1, s2: φ → ( ¬ ∀ z z = y → Ⅎ z [ y / x ] ψ )
    s3 = lb.ref(
        "s3",
        "φ → ( ¬ ∀ z z = y → Ⅎ z [ y x ψ )",
        s1,
        s2,
        ref="syl",
        note="syl alrimi, nfsb4t",
    )

    # axc16nf: ( ∀ z z = y ) → Ⅎ z [ y / x ] ψ
    s4 = lb.ref(
        "s4",
        "( ∀ z z = y ) → Ⅎ z [ y x ψ",
        ref="axc16nf",
        note="axc16nf",
    )

    # pm2.61d2 s3, s4: φ → Ⅎ z [ y / x ] ψ
    res = lb.ref(
        "res",
        "φ → Ⅎ z [ y x ψ",
        s3,
        s4,
        ref="pm2.61d2",
        note="pm2.61d2 syl, axc16nf",
    )

    return lb.build(res)


def prove_nfsb(sys: System) -> Proof:
    """nfsb: Ⅎ z [ y / x ] φ.

    Not-free for proper substitution.  Inference form of nfsbd.
    (Contributed by NM, 14-May-1993.)
    """
    lb = ProofBuilder(sys, "nfsb")
    hyp = lb.hyp("nfsb.1", "Ⅎ z φ")
    # nftru: Ⅎ x ⊤
    s1 = lb.ref(
        "s1",
        "Ⅎ x ⊤",
        ref="nftru",
        note="nftru",
    )
    # a1i: ⊤ → Ⅎ z φ
    s2 = lb.ref(
        "s2",
        "⊤ → Ⅎ z φ",
        hyp,
        ref="a1i",
        note="a1i nfsb.1",
    )
    # nfsbd: ⊤ → Ⅎ z [ y x φ
    s3 = lb.ref(
        "s3",
        "⊤ → Ⅎ z [ y x φ",
        s1,
        s2,
        ref="nfsbd",
        note="nfsbd nftru, a1i",
    )
    # mptru: Ⅎ z [ y x φ
    res = lb.ref(
        "res",
        "Ⅎ z [ y x φ",
        s3,
        ref="mptru",
        note="mptru nfsbd",
    )
    return lb.build(res)


def prove_hbsb(sys: System) -> Proof:
    """hbsb: [ y / x ] φ → ∀ z [ y / x ] φ.

    Closed form of hbsbd.  (Contributed by NM, 14-May-1993.)
    """
    lb = ProofBuilder(sys, "hbsb")
    hyp = lb.hyp("hbsb.1", "φ → ∀ z φ")
    # nf5i: Ⅎ z φ
    s1 = lb.ref(
        "s1",
        "Ⅎ z φ",
        hyp,
        ref="nf5i",
        note="nf5i hbsb.1",
    )
    # nfsb: Ⅎ z [ y / x ] φ
    s2 = lb.ref(
        "s2",
        "Ⅎ z [ y x φ",
        s1,
        ref="nfsb",
        note="nfsb nf5i",
    )
    # nf5ri: [ y / x ] φ → ∀ z [ y / x ] φ
    res = lb.ref(
        "res",
        "[ y x φ → ∀ z [ y x φ",
        s2,
        ref="nf5ri",
        note="nf5ri nfsb",
    )
    return lb.build(res)


def prove_equsb2(sys: System) -> Proof:
    """equsb2: [ y / x ] y = x.
    Proper substitution of equality.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "equsb2")
    # sb2: ∀ x ( x = y → y = x ) → [ y / x ] y = x
    s1 = lb.ref(
        "s1",
        "∀ x ( x = y → y = x ) → [ y x y = x",
        ref="sb2",
        note="sb2",
    )
    # equcomi: x = y → y = x
    s2 = lb.ref(
        "s2",
        "x = y → y = x",
        ref="equcomi",
        note="equcomi",
    )
    # mpg: [ y / x ] y = x
    res = lb.ref(
        "res",
        "[ y x y = x",
        s1,
        s2,
        ref="mpg",
        note="mpg sb2, equcomi",
    )
    return lb.build(res)


def prove_hbsb3(sys: System) -> Proof:
    """hbsb3: [ y / x ] φ → ∀ x [ y / x ] φ.

    If φ implies its own universal quantification, then so does a proper
    substitution.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "hbsb3")
    hyp = lb.hyp("hbsb3.1", "φ → ∀ y φ")
    # sbimi: [ y / x ] φ → [ y / x ] ∀ y φ
    s1 = lb.ref(
        "s1",
        "( [ y x φ → [ y x ∀ y φ )",
        hyp,
        ref="sbimi",
        note="sbimi hbsb3.1",
    )
    # hbsb2a: [ y / x ] ∀ y φ → ∀ x [ y / x ] φ
    s2 = lb.ref(
        "s2",
        "[ y x ∀ y φ → ∀ x [ y x φ",
        ref="hbsb2a",
        note="hbsb2a",
    )
    # syl: [ y / x ] φ → ∀ x [ y / x ] φ
    res = lb.ref(
        "res",
        "( [ y x φ → ∀ x [ y x φ )",
        s1,
        s2,
        ref="syl",
        note="syl sbimi, hbsb2a",
    )
    return lb.build(res)


def prove_hbsb2e(sys: System) -> Proof:
    """hbsb2e: [ y / x ] φ → ∀ x [ y / x ] ∃ y φ.

    If a proper substitution holds, then its universal quantification
    holds over the same variable when the substituted wff is
    existentially quantified over the substitution variable.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "hbsb2e")
    # sb4e: [ y / x ] φ → ∀ x ( x = y → ∃ y φ )
    s1 = lb.ref(
        "s1",
        "[ y x φ → ∀ x ( x = y → ∃ y φ )",
        ref="sb4e",
        note="sb4e",
    )
    # sb2: ∀ x ( x = y → ∃ y φ ) → [ y / x ] ∃ y φ
    s2 = lb.ref(
        "s2",
        "∀ x ( x = y → ∃ y φ ) → [ y x ∃ y φ",
        ref="sb2",
        note="sb2",
    )
    # axc4i sb2: ∀ x ( x = y → ∃ y φ ) → ∀ x [ y / x ] ∃ y φ
    s3 = lb.ref(
        "s3",
        "∀ x ( x = y → ∃ y φ ) → ∀ x [ y x ∃ y φ",
        s2,
        ref="axc4i",
        note="axc4i sb2",
    )
    # syl sb4e, axc4i: [ y / x ] φ → ∀ x [ y / x ] ∃ y φ
    res = lb.ref(
        "res",
        "[ y x φ → ∀ x [ y x ∃ y φ",
        s1,
        s3,
        ref="syl",
        note="syl sb4e, axc4i",
    )
    return lb.build(res)


def prove_nfs1(sys: System) -> Proof:
    """nfs1: F/ x [ y / x ] φ.

    If φ is not free in y, then the proper substitution of y for x
    in φ is not free in x.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wsb nf5ri hbsb3 nf5i.
    """
    lb = ProofBuilder(sys, "nfs1")
    h1 = lb.hyp("nfs1.1", "F/ y φ")

    # nf5ri: φ → ∀ y φ
    s1 = lb.ref(
        "s1",
        "φ → ∀ y φ",
        h1,
        ref="nf5ri",
        note="nf5ri nfs1.1",
    )

    # hbsb3: [ y / x ] φ → ∀ x [ y / x ] φ
    s2 = lb.ref(
        "s2",
        "( [ y x φ → ∀ x [ y x φ )",
        s1,
        ref="hbsb3",
        note="hbsb3 nf5ri",
    )

    # nf5i: F/ x [ y / x ] φ
    res = lb.ref(
        "res",
        "F/ x [ y x φ",
        s2,
        ref="nf5i",
        note="nf5i hbsb3",
    )

    return lb.build(res)


def prove_sbmo(sys: System) -> Proof:
    """sbmo: [ y / x ] ∃* z φ ↔ ∃* z [ y / x ] φ.

    Substitution distributes over the "exists at most one" quantifier.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbmo")

    # dfmo: ∃* z φ ↔ ∃ w ∀ z ( φ → z = w )
    s_dfmo = lb.ref(
        "s_dfmo",
        "∃* z φ ↔ ∃ w ∀ z ( φ → z = w )",
        ref="dfmo",
        note="dfmo",
    )

    # sbbii dfmo: [ y x ∃* z φ ↔ [ y x ∃ w ∀ z ( φ → z = w )
    s_sbbii = lb.ref(
        "s_sbbii",
        "[ y x ∃* z φ ↔ [ y x ∃ w ∀ z ( φ → z = w )",
        s_dfmo,
        ref="sbbii",
        note="sbbii dfmo",
    )

    # sbex: [ y x ∃ w ∀ z ( φ → z = w ) ↔ ∃ w [ y x ∀ z ( φ → z = w )
    s_sbex = lb.ref(
        "s_sbex",
        "[ y x ∃ w ∀ z ( φ → z = w ) ↔ ∃ w [ y x ∀ z ( φ → z = w )",
        ref="sbex",
        note="sbex",
    )

    # nfv: Ⅎ x ( z = w )
    s_nfv = lb.ref(
        "s_nfv",
        "Ⅎ x ( z = w )",
        ref="nfv",
        note="nfv",
    )

    # sblim nfv: [ y x ( φ → z = w ) ↔ ( [ y x φ → z = w )
    s_sblim = lb.ref(
        "s_sblim",
        "[ y x ( φ → z = w ) ↔ ( [ y x φ → z = w )",
        s_nfv,
        ref="sblim",
        note="sblim nfv",
    )

    # sbalv sblim: [ y x ∀ z ( φ → z = w ) ↔ ∀ z ( [ y x φ → z = w )
    s_sbalv = lb.ref(
        "s_sbalv",
        "[ y x ∀ z ( φ → z = w ) ↔ ∀ z ( [ y x φ → z = w )",
        s_sblim,
        ref="sbalv",
        note="sbalv sblim",
    )

    # exbii sbalv: ∃ w [ y x ∀ z ( φ → z = w ) ↔ ∃ w ∀ z ( [ y x φ → z = w )
    s_exbii = lb.ref(
        "s_exbii",
        "∃ w [ y x ∀ z ( φ → z = w ) ↔ ∃ w ∀ z ( [ y x φ → z = w )",
        s_sbalv,
        ref="exbii",
        note="exbii sbalv",
    )

    # bitri sbex, exbii: [ y x ∃ w ∀ z ( φ → z = w ) ↔ ∃ w ∀ z ( [ y x φ → z = w )
    s_bitri = lb.ref(
        "s_bitri",
        "[ y x ∃ w ∀ z ( φ → z = w ) ↔ ∃ w ∀ z ( [ y x φ → z = w )",
        s_sbex,
        s_exbii,
        ref="bitri",
        note="bitri sbex, exbii",
    )

    # dfmo for [ y x φ: ∃* z [ y x φ ↔ ∃ w ∀ z ( [ y x φ → z = w )
    s_dfmo2 = lb.ref(
        "s_dfmo2",
        "∃* z [ y x φ ↔ ∃ w ∀ z ( [ y x φ → z = w )",
        ref="dfmo",
        note="dfmo",
    )

    # 3bitr4i: [ y x ∃* z φ ↔ ∃* z [ y x φ
    res = lb.ref(
        "res",
        "[ y x ∃* z φ ↔ ∃* z [ y x φ",
        s_bitri,
        s_sbbii,
        s_dfmo2,
        ref="3bitr4i",
        note="3bitr4i",
    )

    return lb.build(res)


def prove_exists2(sys: System) -> Proof:
    """exists2: ( ( ∃ x φ ∧ ∃ x ¬ φ ) → ¬ ∃! x x = x ).

    If there exists an x such that φ and an x such that ¬φ, then there
    is not exactly one x (which would make x=x unique).
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "exists2")
    # axc16nf: ( ∀ x x = y ) → Ⅎ x φ
    s1 = lb.ref(
        "s1",
        "( ∀ x x = y ) → Ⅎ x φ",
        ref="axc16nf",
        note="axc16nf",
    )
    # nfrd s1: ( ∀ x x = y ) → ( ∃ x φ → ∀ x φ )
    s2 = lb.ref(
        "s2",
        "( ∀ x x = y ) → ( ∃ x φ → ∀ x φ )",
        s1,
        ref="nfrd",
        note="nfrd axc16nf",
    )
    # com12 s2: ∃ x φ → ( ( ∀ x x = y ) → ∀ x φ )
    s3 = lb.ref(
        "s3",
        "∃ x φ → ( ( ∀ x x = y ) → ∀ x φ )",
        s2,
        ref="com12",
        note="com12 nfrd",
    )
    # exists1: ( ∃! x x = x ↔ ∀ x ( x = y ) )
    s4 = lb.ref(
        "s4",
        "( ∃! x x = x ↔ ∀ x ( x = y ) )",
        ref="exists1",
        note="exists1",
    )
    # alex: ∀ x φ ↔ ¬ ∃ x ¬ φ
    s5 = lb.ref(
        "s5",
        "∀ x φ ↔ ¬ ∃ x ¬ φ",
        ref="alex",
        note="alex",
    )
    # bicomi s5: ¬ ∃ x ¬ φ ↔ ∀ x φ
    s6 = lb.ref(
        "s6",
        "¬ ∃ x ¬ φ ↔ ∀ x φ",
        s5,
        ref="bicomi",
        note="bicomi alex",
    )
    # 3imtr4g s3, s4, s6: ∃ x φ → ( ∃! x x = x → ¬ ∃ x ¬ φ )
    s7 = lb.ref(
        "s7",
        "∃ x φ → ( ∃! x x = x → ¬ ∃ x ¬ φ )",
        s3,
        s4,
        s6,
        ref="3imtr4g",
        note="3imtr4g com12, exists1, bicomi",
    )
    # con2d s7: ∃ x φ → ( ∃ x ¬ φ → ¬ ∃! x x = x )
    s8 = lb.ref(
        "s8",
        "∃ x φ → ( ∃ x ¬ φ → ¬ ∃! x x = x )",
        s7,
        ref="con2d",
        note="con2d 3imtr4g",
    )
    # imp s8: ( ∃ x φ ∧ ∃ x ¬ φ ) → ¬ ∃! x x = x
    res = lb.ref(
        "res",
        "( ∃ x φ ∧ ∃ x ¬ φ ) → ¬ ∃! x x = x",
        s8,
        ref="imp",
        note="imp con2d",
    )
    return lb.build(res)


def prove_eujustALT(sys: System) -> Proof:
    """eujustALT: ( ∃ y ∀ x ( φ ↔ x = y ) ↔ ∃ z ∀ x ( φ ↔ x = z ) ).

    Alternate proof of eujust using the case-analysis approach:
    Case A (∀ y y = z) uses equequ2/bibi2d/albidv/sps/drex1;
    Case B (¬ ∀ y y = z) uses hbnae/alrimih/ax-5/dvelim/naecoms/cbv2h;
    both cases combined via pm2.61i.
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "eujustALT")

    # ===== Case A: ∀ y y = z =====
    # 1. equequ2: y = z → ( x = y ↔ x = z )
    s1 = lb.ref(
        "s1",
        "y = z → ( x = y ↔ x = z )",
        ref="equequ2",
        note="equequ2",
    )
    # 2. bibi2d: y = z → ( ( φ ↔ x = y ) ↔ ( φ ↔ x = z ) )
    s2 = lb.ref(
        "s2",
        "y = z → ( ( φ ↔ x = y ) ↔ ( φ ↔ x = z ) )",
        s1,
        ref="bibi2d",
        note="bibi2d",
    )
    # 3. albidv: y = z → ( ∀ x ( φ ↔ x = y ) ↔ ∀ x ( φ ↔ x = z ) )
    s3 = lb.ref(
        "s3",
        "y = z → ( ∀ x ( φ ↔ x = y ) ↔ ∀ x ( φ ↔ x = z ) )",
        s2,
        ref="albidv",
        note="albidv",
    )
    # 4. sps s3: ∀ y y = z → ( ∀ x ( φ ↔ x = y ) ↔ ∀ x ( φ ↔ x = z ) )
    s4 = lb.ref(
        "s4",
        "∀ y y = z → ( ∀ x ( φ ↔ x = y ) ↔ ∀ x ( φ ↔ x = z ) )",
        s3,
        ref="sps",
        note="sps albidv",
    )
    # 5. drex1 s4: ∀ y y = z → ( ∃ y ∀ x ( φ ↔ x = y ) ↔ ∃ z ∀ x ( φ ↔ x = z ) )
    s5 = lb.ref(
        "s5",
        "∀ y y = z → ( ∃ y ∀ x ( φ ↔ x = y ) ↔ ∃ z ∀ x ( φ ↔ x = z ) )",
        s4,
        ref="drex1",
        note="drex1 sps",
    )

    # ===== Case B: ¬ ∀ y y = z =====
    # 6. hbnae: ¬ ∀ y y = z → ∀ y ¬ ∀ y y = z
    s6 = lb.ref(
        "s6",
        "¬ ∀ y y = z → ∀ y ¬ ∀ y y = z",
        ref="hbnae",
        note="hbnae",
    )
    # 7. hbnae: ¬ ∀ y y = z → ∀ z ¬ ∀ y y = z
    s7 = lb.ref(
        "s7",
        "¬ ∀ y y = z → ∀ z ¬ ∀ y y = z",
        ref="hbnae",
        note="hbnae",
    )
    # 8. alrimih s6,s7: ¬ ∀ y y = z → ∀ y ∀ z ¬ ∀ y y = z
    s8 = lb.ref(
        "s8",
        "¬ ∀ y y = z → ∀ y ∀ z ¬ ∀ y y = z",
        s6,
        s7,
        ref="alrimih",
        note="alrimih hbnae, hbnae",
    )

    # 9. ax-5: ¬ ∀ x ( φ ↔ x = w ) → ∀ z ¬ ∀ x ( φ ↔ x = w )
    s9 = lb.ref(
        "s9",
        "¬ ∀ x ( φ ↔ x = w ) → ∀ z ¬ ∀ x ( φ ↔ x = w )",
        ref="ax-5",
        note="ax-5",
    )
    # 10. equequ2: w = y → ( x = w ↔ x = y )
    s10 = lb.ref(
        "s10",
        "w = y → ( x = w ↔ x = y )",
        ref="equequ2",
        note="equequ2",
    )
    # 11. bibi2d s10: w = y → ( ( φ ↔ x = w ) ↔ ( φ ↔ x = y ) )
    s11 = lb.ref(
        "s11",
        "w = y → ( ( φ ↔ x = w ) ↔ ( φ ↔ x = y ) )",
        s10,
        ref="bibi2d",
        note="bibi2d",
    )
    # 12. albidv s11: w = y → ( ∀ x ( φ ↔ x = w ) ↔ ∀ x ( φ ↔ x = y ) )
    s12 = lb.ref(
        "s12",
        "w = y → ( ∀ x ( φ ↔ x = w ) ↔ ∀ x ( φ ↔ x = y ) )",
        s11,
        ref="albidv",
        note="albidv",
    )
    # 13. notbid s12: w = y → ( ¬ ∀ x ( φ ↔ x = w ) ↔ ¬ ∀ x ( φ ↔ x = y ) )
    s13 = lb.ref(
        "s13",
        "w = y → ( ¬ ∀ x ( φ ↔ x = w ) ↔ ¬ ∀ x ( φ ↔ x = y ) )",
        s12,
        ref="notbid",
        note="notbid",
    )
    # 14. dvelim s9,s13: ¬ ∀ z z = y → ( ¬ ∀ x ( φ ↔ x = y ) → ∀ z ¬ ∀ x ( φ ↔ x = y ) )
    s14 = lb.ref(
        "s14",
        "¬ ∀ z z = y → ( ¬ ∀ x ( φ ↔ x = y ) → ∀ z ¬ ∀ x ( φ ↔ x = y ) )",
        s9,
        s13,
        ref="dvelim",
        note="dvelim ax-5, notbid",
    )
    # 15. naecoms s14: ¬ ∀ y y = z → ( ¬ ∀ x ( φ ↔ x = y ) → ∀ z ¬ ∀ x ( φ ↔ x = y ) )
    s15 = lb.ref(
        "s15",
        "¬ ∀ y y = z → ( ¬ ∀ x ( φ ↔ x = y ) → ∀ z ¬ ∀ x ( φ ↔ x = y ) )",
        s14,
        ref="naecoms",
        note="naecoms dvelim",
    )

    # 16. ax-5: ¬ ∀ x ( φ ↔ x = w ) → ∀ y ¬ ∀ x ( φ ↔ x = w )
    s16 = lb.ref(
        "s16",
        "¬ ∀ x ( φ ↔ x = w ) → ∀ y ¬ ∀ x ( φ ↔ x = w )",
        ref="ax-5",
        note="ax-5",
    )
    # 17. equequ2: w = z → ( x = w ↔ x = z )
    s17 = lb.ref(
        "s17",
        "w = z → ( x = w ↔ x = z )",
        ref="equequ2",
        note="equequ2",
    )
    # 18. bibi2d s17: w = z → ( ( φ ↔ x = w ) ↔ ( φ ↔ x = z ) )
    s18 = lb.ref(
        "s18",
        "w = z → ( ( φ ↔ x = w ) ↔ ( φ ↔ x = z ) )",
        s17,
        ref="bibi2d",
        note="bibi2d",
    )
    # 19. albidv s18: w = z → ( ∀ x ( φ ↔ x = w ) ↔ ∀ x ( φ ↔ x = z ) )
    s19 = lb.ref(
        "s19",
        "w = z → ( ∀ x ( φ ↔ x = w ) ↔ ∀ x ( φ ↔ x = z ) )",
        s18,
        ref="albidv",
        note="albidv",
    )
    # 20. notbid s19: w = z → ( ¬ ∀ x ( φ ↔ x = w ) ↔ ¬ ∀ x ( φ ↔ x = z ) )
    s20 = lb.ref(
        "s20",
        "w = z → ( ¬ ∀ x ( φ ↔ x = w ) ↔ ¬ ∀ x ( φ ↔ x = z ) )",
        s19,
        ref="notbid",
        note="notbid",
    )
    # 21. dvelim s16,s20: ¬ ∀ y y = z → ( ¬ ∀ x ( φ ↔ x = z ) → ∀ y ¬ ∀ x ( φ ↔ x = z ) )
    s21 = lb.ref(
        "s21",
        "¬ ∀ y y = z → ( ¬ ∀ x ( φ ↔ x = z ) → ∀ y ¬ ∀ x ( φ ↔ x = z ) )",
        s16,
        s20,
        ref="dvelim",
        note="dvelim ax-5, notbid",
    )

    # 22. Reuse s3: y = z → ( ∀ x ( φ ↔ x = y ) ↔ ∀ x ( φ ↔ x = z ) )
    s22 = s3
    # 23. notbid s22: y = z → ( ¬ ∀ x ( φ ↔ x = y ) ↔ ¬ ∀ x ( φ ↔ x = z ) )
    s23 = lb.ref(
        "s23",
        "y = z → ( ¬ ∀ x ( φ ↔ x = y ) ↔ ¬ ∀ x ( φ ↔ x = z ) )",
        s22,
        ref="notbid",
        note="notbid",
    )
    # 24. a1i s23: ¬ ∀ y y = z → ( y = z → ( ¬ ∀ x ( φ ↔ x = y ) ↔ ¬ ∀ x ( φ ↔ x = z ) ) )
    s24 = lb.ref(
        "s24",
        "¬ ∀ y y = z → ( y = z → ( ¬ ∀ x ( φ ↔ x = y ) ↔ ¬ ∀ x ( φ ↔ x = z ) ) )",
        s23,
        ref="a1i",
        note="a1i notbid",
    )

    # 25. cbv2h s15,s21,s24: ∀ y ∀ z ¬ ∀ y y = z → ( ∀ y ¬ ∀ x ( φ ↔ x = y ) ↔ ∀ z ¬ ∀ x ( φ ↔ x = z ) )
    s25 = lb.ref(
        "s25",
        "∀ y ∀ z ¬ ∀ y y = z → ( ∀ y ¬ ∀ x ( φ ↔ x = y ) ↔ ∀ z ¬ ∀ x ( φ ↔ x = z ) )",
        s15,
        s21,
        s24,
        ref="cbv2h",
        note="cbv2h",
    )
    # 26. syl s8,s25: ¬ ∀ y y = z → ( ∀ y ¬ ∀ x ( φ ↔ x = y ) ↔ ∀ z ¬ ∀ x ( φ ↔ x = z ) )
    s26 = lb.ref(
        "s26",
        "¬ ∀ y y = z → ( ∀ y ¬ ∀ x ( φ ↔ x = y ) ↔ ∀ z ¬ ∀ x ( φ ↔ x = z ) )",
        s8,
        s25,
        ref="syl",
        note="syl alrimih, cbv2h",
    )

    # 27. notbid s26: ¬ ∀ y y = z → ( ¬ ∀ y ¬ ∀ x ( φ ↔ x = y ) ↔ ¬ ∀ z ¬ ∀ x ( φ ↔ x = z ) )
    s27 = lb.ref(
        "s27",
        "¬ ∀ y y = z → ( ¬ ∀ y ¬ ∀ x ( φ ↔ x = y ) ↔ ¬ ∀ z ¬ ∀ x ( φ ↔ x = z ) )",
        s26,
        ref="notbid",
        note="notbid",
    )

    # 28. df-ex: ∃ y ∀ x ( φ ↔ x = y ) ↔ ¬ ∀ y ¬ ∀ x ( φ ↔ x = y )
    s28 = lb.ref(
        "s28",
        "∃ y ∀ x ( φ ↔ x = y ) ↔ ¬ ∀ y ¬ ∀ x ( φ ↔ x = y )",
        ref="df-ex",
        note="df-ex",
    )
    # 29. df-ex: ∃ z ∀ x ( φ ↔ x = z ) ↔ ¬ ∀ z ¬ ∀ x ( φ ↔ x = z )
    s29 = lb.ref(
        "s29",
        "∃ z ∀ x ( φ ↔ x = z ) ↔ ¬ ∀ z ¬ ∀ x ( φ ↔ x = z )",
        ref="df-ex",
        note="df-ex",
    )

    # 30. 3bitr4g s27,s28,s29: ¬ ∀ y y = z → ( ∃ y ∀ x ( φ ↔ x = y ) ↔ ∃ z ∀ x ( φ ↔ x = z ) )
    s30 = lb.ref(
        "s30",
        "¬ ∀ y y = z → ( ∃ y ∀ x ( φ ↔ x = y ) ↔ ∃ z ∀ x ( φ ↔ x = z ) )",
        s27,
        s28,
        s29,
        ref="3bitr4g",
        note="3bitr4g notbid, df-ex, df-ex",
    )

    # 31. pm2.61i s5,s30: ( ∃ y ∀ x ( φ ↔ x = y ) ↔ ∃ z ∀ x ( φ ↔ x = z ) )
    res = lb.ref(
        "res",
        "( ∃ y ∀ x ( φ ↔ x = y ) ↔ ∃ z ∀ x ( φ ↔ x = z ) )",
        s5,
        s30,
        ref="pm2.61i",
        note="pm2.61i drex1, 3bitr4g",
    )
    return lb.build(res)


def prove_2ax6elem(sys: System) -> Proof:
    """2ax6elem: ¬ ∀ w w = z → ∃ z ∃ w ( z = x ∧ w = y ).

    Merge two ax6e instances into a common expression.
    (Contributed by Wolf Lammen, 27-Sep-2018.)
    """
    lb = ProofBuilder(sys, "2ax6elem")
    # ax6e: ∃ z z = x
    s1 = lb.ref(
        "s1",
        "∃ z z = x",
        ref="ax6e",
        note="ax6e",
    )
    # nfnae: Ⅎ z ¬ ∀ w w = z
    s2 = lb.ref(
        "s2",
        "Ⅎ z ¬ ∀ w w = z",
        ref="nfnae",
        note="nfnae",
    )
    # nfnae: Ⅎ z ¬ ∀ w w = x
    s3 = lb.ref(
        "s3",
        "Ⅎ z ¬ ∀ w w = x",
        ref="nfnae",
        note="nfnae",
    )
    # nfan s2, s3: Ⅎ z ( ¬ ∀ w w = z ∧ ¬ ∀ w w = x )
    s4 = lb.ref(
        "s4",
        "Ⅎ z ( ¬ ∀ w w = z ∧ ¬ ∀ w w = x )",
        s2,
        s3,
        ref="nfan",
        note="nfan",
    )
    # nfeqf: ( ¬ ∀ w w = z ∧ ¬ ∀ w w = x ) → Ⅎ w z = x
    s5 = lb.ref(
        "s5",
        "( ¬ ∀ w w = z ∧ ¬ ∀ w w = x ) → Ⅎ w z = x",
        ref="nfeqf",
        note="nfeqf",
    )
    # pm3.21: w = y → ( z = x → ( z = x ∧ w = y ) )
    s6 = lb.ref(
        "s6",
        "w = y → ( z = x → ( z = x ∧ w = y ) )",
        ref="pm3.21",
        note="pm3.21",
    )
    # spimed s5, s6: ( ¬ ∀ w w = z ∧ ¬ ∀ w w = x ) → ( z = x → ∃ w ( z = x ∧ w = y ) )
    s7 = lb.ref(
        "s7",
        "( ¬ ∀ w w = z ∧ ¬ ∀ w w = x ) → ( z = x → ∃ w ( z = x ∧ w = y ) )",
        s5,
        s6,
        ref="spimed",
        note="spimed",
    )
    # eximd s4, s7: ( ¬ ∀ w w = z ∧ ¬ ∀ w w = x ) → ( ∃ z z = x → ∃ z ∃ w ( z = x ∧ w = y ) )
    s8 = lb.ref(
        "s8",
        "( ¬ ∀ w w = z ∧ ¬ ∀ w w = x ) → ( ∃ z z = x → ∃ z ∃ w ( z = x ∧ w = y ) )",
        s4,
        s7,
        ref="eximd",
        note="eximd",
    )
    # mpi s1, s8: ( ¬ ∀ w w = z ∧ ¬ ∀ w w = x ) → ∃ z ∃ w ( z = x ∧ w = y )
    s9 = lb.ref(
        "s9",
        "( ¬ ∀ w w = z ∧ ¬ ∀ w w = x ) → ∃ z ∃ w ( z = x ∧ w = y )",
        s1,
        s8,
        ref="mpi",
        note="mpi ax6e, eximd",
    )
    # ex s9: ¬ ∀ w w = z → ( ¬ ∀ w w = x → ∃ z ∃ w ( z = x ∧ w = y ) )
    s10 = lb.ref(
        "s10",
        "¬ ∀ w w = z → ( ¬ ∀ w w = x → ∃ z ∃ w ( z = x ∧ w = y ) )",
        s9,
        ref="ex",
        note="ex",
    )
    # ax6e: ∃ z z = y
    s11 = lb.ref(
        "s11",
        "∃ z z = y",
        ref="ax6e",
        note="ax6e",
    )
    # nfae: Ⅎ z ∀ w w = x
    s12 = lb.ref(
        "s12",
        "Ⅎ z ∀ w w = x",
        ref="nfae",
        note="nfae",
    )
    # equvini: z = y → ∃ w ( z = w ∧ w = y )
    s13 = lb.ref(
        "s13",
        "z = y → ∃ w ( z = w ∧ w = y )",
        ref="equvini",
        note="equvini",
    )
    # equtrr: w = x → ( z = w → z = x )
    s14 = lb.ref(
        "s14",
        "w = x → ( z = w → z = x )",
        ref="equtrr",
        note="equtrr",
    )
    # anim1d s14: w = x → ( ( z = w ∧ w = y ) → ( z = x ∧ w = y ) )
    s15 = lb.ref(
        "s15",
        "w = x → ( ( z = w ∧ w = y ) → ( z = x ∧ w = y ) )",
        s14,
        ref="anim1d",
        note="anim1d",
    )
    # aleximi s15: ∀ w w = x → ( ∃ w ( z = w ∧ w = y ) → ∃ w ( z = x ∧ w = y ) )
    s16 = lb.ref(
        "s16",
        "∀ w w = x → ( ∃ w ( z = w ∧ w = y ) → ∃ w ( z = x ∧ w = y ) )",
        s15,
        ref="aleximi",
        note="aleximi",
    )
    # syl5 s13, s16: ∀ w w = x → ( z = y → ∃ w ( z = x ∧ w = y ) )
    s17 = lb.ref(
        "s17",
        "∀ w w = x → ( z = y → ∃ w ( z = x ∧ w = y ) )",
        s13,
        s16,
        ref="syl5",
        note="syl5 equvini, aleximi",
    )
    # eximd s12, s17: ∀ w w = x → ( ∃ z z = y → ∃ z ∃ w ( z = x ∧ w = y ) )
    s18 = lb.ref(
        "s18",
        "∀ w w = x → ( ∃ z z = y → ∃ z ∃ w ( z = x ∧ w = y ) )",
        s12,
        s17,
        ref="eximd",
        note="eximd",
    )
    # mpi s11, s18: ∀ w w = x → ∃ z ∃ w ( z = x ∧ w = y )
    s19 = lb.ref(
        "s19",
        "∀ w w = x → ∃ z ∃ w ( z = x ∧ w = y )",
        s11,
        s18,
        ref="mpi",
        note="mpi ax6e, eximd",
    )
    # pm2.61d2 s10, s19: ¬ ∀ w w = z → ∃ z ∃ w ( z = x ∧ w = y )
    res = lb.ref(
        "res",
        "¬ ∀ w w = z → ∃ z ∃ w ( z = x ∧ w = y )",
        s10,
        s19,
        ref="pm2.61d2",
        note="pm2.61d2",
    )
    return lb.build(res)


def prove_2ax6e(sys: System) -> Proof:
    """2ax6e: ∃ z ∃ w ( z = x ∧ w = y ).

    If ∀ w w = z holds, aeveq gives z = x and w = y, which jca joins into
    a conjunction, and two applications of 19.8ad add the existential
    quantifiers.  Otherwise 2ax6elem already gives the conclusion.
    The two cases are combined with pm2.61i.
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "2ax6e")

    # 1. 2ax6elem: ¬ ∀ w w = z → ∃ z ∃ w ( z = x ∧ w = y )
    s1 = lb.ref(
        "s1",
        "¬ ∀ w w = z → ∃ z ∃ w ( z = x ∧ w = y )",
        ref="2ax6elem",
        note="2ax6elem",
    )

    # 2. aeveq with x:=w, y:=z, z:=z, t:=x: ∀ w ( w = z ) → z = x
    s2 = lb.ref(
        "s2",
        "∀ w ( w = z ) → z = x",
        ref="aeveq",
        note="aeveq",
    )

    # 3. aeveq with x:=w, y:=z, z:=w, t:=y: ∀ w ( w = z ) → w = y
    s3 = lb.ref(
        "s3",
        "∀ w ( w = z ) → w = y",
        ref="aeveq",
        note="aeveq",
    )

    # 4. jca s2, s3: ∀ w ( w = z ) → ( z = x ∧ w = y )
    s4 = lb.ref(
        "s4",
        "∀ w ( w = z ) → ( z = x ∧ w = y )",
        s2,
        s3,
        ref="jca",
        note="jca aeveq, aeveq",
    )

    # 5. 19.8ad s4 with bound variable w: ∀ w ( w = z ) → ∃ w ( z = x ∧ w = y )
    s5 = lb.ref(
        "s5",
        "∀ w ( w = z ) → ∃ w ( z = x ∧ w = y )",
        s4,
        ref="19.8ad",
        note="19.8ad",
    )

    # 6. 19.8ad s5 with bound variable z: ∀ w ( w = z ) → ∃ z ∃ w ( z = x ∧ w = y )
    s6 = lb.ref(
        "s6",
        "∀ w ( w = z ) → ∃ z ∃ w ( z = x ∧ w = y )",
        s5,
        ref="19.8ad",
        note="19.8ad",
    )

    # 7. pm2.61i s6, s1: ∃ z ∃ w ( z = x ∧ w = y )
    res = lb.ref(
        "res",
        "∃ z ∃ w ( z = x ∧ w = y )",
        s6,
        s1,
        ref="pm2.61i",
        note="pm2.61i 19.8ad, 2ax6elem",
    )

    return lb.build(res)


def prove_dfmoeu(sys: System) -> Proof:
    """dfmoeu: ( ( ∃ x φ → ∃ y ∀ x ( φ ↔ x = y ) ) ↔ ∃ y ∀ x ( φ → x = y ) ).

    Equivalence of the existence-of-unique-y definiens with the
    at-most-one definiens.  (Contributed by NM, 14-Sep-1993.)
    """
    lb = ProofBuilder(sys, "dfmoeu")

    # ── Forward: (∃ x φ → ∃ y ∀ x ( φ ↔ x = y )) → ∃ y ∀ x ( φ → x = y ) ──

    s_alnex = lb.ref("s_alnex", "∀ x ¬ φ ↔ ¬ ∃ x φ", ref="alnex", note="alnex")
    s_pm2_21 = lb.ref("s_pm2_21", "¬ φ → ( φ → x = y )", ref="pm2.21", note="pm2.21")
    s_alimi1 = lb.ref(
        "s_alimi1",
        "∀ x ¬ φ → ∀ x ( φ → x = y )",
        s_pm2_21,
        ref="alimi",
        note="alimi pm2.21",
    )
    s_19_8a = lb.ref(
        "s_19_8a",
        "∀ x ( φ → x = y ) → ∃ y ∀ x ( φ → x = y )",
        ref="19.8a",
        note="19.8a",
    )
    s_syl1 = lb.ref(
        "s_syl1",
        "∀ x ¬ φ → ∃ y ∀ x ( φ → x = y )",
        s_alimi1,
        s_19_8a,
        ref="syl",
        note="syl alimi, 19.8a",
    )
    s_ja1 = lb.ref(
        "s_ja1",
        "¬ ∃ x φ → ∃ y ∀ x ( φ → x = y )",
        s_alnex,
        s_syl1,
        ref="sylbir",
        note="sylbir alnex, syl",
    )
    s_biimp = lb.ref("s_biimp", "( φ ↔ x = y ) → ( φ → x = y )", ref="biimp", note="biimp")
    s_alimi2 = lb.ref(
        "s_alimi2",
        "∀ x ( φ ↔ x = y ) → ∀ x ( φ → x = y )",
        s_biimp,
        ref="alimi",
        note="alimi biimp",
    )
    s_ja2 = lb.ref(
        "s_ja2",
        "∃ y ∀ x ( φ ↔ x = y ) → ∃ y ∀ x ( φ → x = y )",
        s_alimi2,
        ref="eximi",
        note="eximi alimi",
    )
    s_fwd = lb.ref(
        "s_fwd",
        "( ∃ x φ → ∃ y ∀ x ( φ ↔ x = y ) ) → ∃ y ∀ x ( φ → x = y )",
        s_ja1,
        s_ja2,
        ref="ja",
        note="ja",
    )

    # ── Reverse: ∃ y ∀ x ( φ → x = y ) → ( ∃ x φ → ∃ y ∀ x ( φ ↔ x = y ) ) ──

    s_id = lb.ref("s_id", "φ → φ", ref="id", note="id")
    s_ax12v = lb.ref(
        "s_ax12v",
        "x = y → ( φ → ∀ x ( x = y → φ ) )",
        ref="ax12v",
        note="ax12v",
    )
    s_c12_ax = lb.ref(
        "s_c12_ax",
        "φ → ( x = y → ∀ x ( x = y → φ ) )",
        s_ax12v,
        ref="com12",
        note="com12 ax12v",
    )
    s_emb = lb.ref(
        "s_emb",
        "φ → ( ( φ → x = y ) → ∀ x ( x = y → φ ) )",
        s_id,
        s_c12_ax,
        ref="embantd",
        note="embantd id, com12",
    )
    s_spsd1 = lb.ref(
        "s_spsd1",
        "φ → ( ∀ x ( φ → x = y ) → ∀ x ( x = y → φ ) )",
        s_emb,
        ref="spsd",
        note="spsd embantd",
    )
    s_anc = lb.ref(
        "s_anc",
        "φ → ( ∀ x ( φ → x = y ) → ( ∀ x ( φ → x = y ) ∧ ∀ x ( x = y → φ ) ) )",
        s_spsd1,
        ref="ancld",
        note="ancld spsd",
    )
    s_alb = lb.ref(
        "s_alb",
        "∀ x ( φ ↔ x = y ) ↔ ( ∀ x ( φ → x = y ) ∧ ∀ x ( x = y → φ ) )",
        ref="albiim",
        note="albiim",
    )
    s_imb = lb.ref(
        "s_imb",
        "φ → ( ∀ x ( φ → x = y ) → ∀ x ( φ ↔ x = y ) )",
        s_anc,
        s_alb,
        ref="imbitrrdi",
        note="imbitrrdi ancld, albiim",
    )

    # nfia1: Ⅎ x ( ∀ x ( φ → x = y ) → ∀ x ( φ ↔ x = y ) )
    s_nfia1 = lb.ref(
        "s_nfia1",
        "Ⅎ x ( ∀ x ( φ → x = y ) → ∀ x ( φ ↔ x = y ) )",
        ref="nfia1",
        note="nfia1",
    )

    # exlimi(nfia1, imb): ∃ x φ → ( ∀ x ( φ → x = y ) → ∀ x ( φ ↔ x = y ) )
    s_exlimi2 = lb.ref(
        "s_exlimi2",
        "∃ x φ → ( ∀ x ( φ → x = y ) → ∀ x ( φ ↔ x = y ) )",
        s_nfia1,
        s_imb,
        ref="exlimi",
        note="exlimi nfia1, imbitrrdi",
    )

    # com12(exlimi2): ∀ x ( φ → x = y ) → ( ∃ x φ → ∀ x ( φ ↔ x = y ) )
    s_c12_exl = lb.ref(
        "s_c12_exl",
        "∀ x ( φ → x = y ) → ( ∃ x φ → ∀ x ( φ ↔ x = y ) )",
        s_exlimi2,
        ref="com12",
        note="com12 exlimi",
    )

    # This is the com12/eximdv tail of the set.mm proof.  First put the
    # existential premise in the antecedent required by eximdv.
    s_c12_inner = lb.ref(
        "s_c12_inner",
        "∃ x φ → ( ∀ x ( φ → x = y ) → ∀ x ( φ ↔ x = y ) )",
        s_c12_exl,
        ref="com12",
        note="com12 exlimi",
    )
    s_eximdv = lb.ref(
        "s_eximdv",
        "∃ x φ → ( ∃ y ∀ x ( φ → x = y ) → ∃ y ∀ x ( φ ↔ x = y ) )",
        s_c12_inner,
        ref="eximdv",
        note="eximdv com12",
    )
    s_rev = lb.ref(
        "s_rev",
        "∃ y ∀ x ( φ → x = y ) → ( ∃ x φ → ∃ y ∀ x ( φ ↔ x = y ) )",
        s_eximdv,
        ref="com12",
        note="com12 eximdv",
    )

    # impbii(fwd, rev)
    res = lb.ref(
        "res",
        "( ( ∃ x φ → ∃ y ∀ x ( φ ↔ x = y ) ) ↔ ∃ y ∀ x ( φ → x = y ) )",
        s_fwd,
        s_rev,
        ref="impbii",
        note="impbii",
    )
    return lb.build(res)


def prove_dfmo2(sys: System) -> Proof:
    """dfmo2: ∃* x φ ↔ ∃ y ∀ x ( φ → x = y ).

    Alternate definition of "exists at most one."  (Contributed by NM,
    10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "dfmo2")

    # moeu: ∃* x φ ↔ ( ∃ x φ → ∃! x φ )
    s1 = lb.ref(
        "s1",
        "∃* x φ ↔ ( ∃ x φ → ∃! x φ )",
        ref="moeu",
        note="moeu",
    )

    # eu6: ∃! x φ ↔ ∃ y ∀ x ( φ ↔ x = y )
    s2 = lb.ref(
        "s2",
        "∃! x φ ↔ ∃ y ∀ x ( φ ↔ x = y )",
        ref="eu6",
        note="eu6",
    )

    # imbi2i(eu6): ( ∃ x φ → ∃! x φ ) ↔ ( ∃ x φ → ∃ y ∀ x ( φ ↔ x = y ) )
    s3 = lb.ref(
        "s3",
        "( ∃ x φ → ∃! x φ ) ↔ ( ∃ x φ → ∃ y ∀ x ( φ ↔ x = y ) )",
        s2,
        ref="imbi2i",
        note="imbi2i eu6",
    )

    # dfmoeu: ( ∃ x φ → ∃ y ∀ x ( φ ↔ x = y ) ) ↔ ∃ y ∀ x ( φ → x = y )
    s4 = lb.ref(
        "s4",
        "( ∃ x φ → ∃ y ∀ x ( φ ↔ x = y ) ) ↔ ∃ y ∀ x ( φ → x = y )",
        ref="dfmoeu",
        note="dfmoeu",
    )

    # 3bitri(moeu, imbi2i(eu6), dfmoeu): ∃* x φ ↔ ∃ y ∀ x ( φ → x = y )
    res = lb.ref(
        "res",
        "∃* x φ ↔ ∃ y ∀ x ( φ → x = y )",
        s1,
        s3,
        s4,
        ref="3bitri",
        note="3bitri moeu, imbi2i, dfmoeu",
    )

    return lb.build(res)


def prove_dfeumo(sys: System) -> Proof:
    """dfeumo: ( ∃ x φ ∧ ∃ y ∀ x ( φ → x = y ) ) ↔ ∃ y ∀ x ( φ ↔ x = y ).

    Equivalence of an alternate at-most-one definiens with the
    defining expression of existential uniqueness.  (Contributed by
    Wolf Lammen, 3-Oct-2023.)
    """
    lb = ProofBuilder(sys, "dfeumo")

    # ax6ev: ∃ x x = y
    s1 = lb.ref(
        "s1",
        "∃ x x = y",
        ref="ax6ev",
        note="ax6ev",
    )

    # biimpr: ( φ ↔ x = y ) → ( x = y → φ )
    s2 = lb.ref(
        "s2",
        "( φ ↔ x = y ) → ( x = y → φ )",
        ref="biimpr",
        note="biimpr",
    )

    # aleximi biimpr: ∀ x ( φ ↔ x = y ) → ( ∃ x x = y → ∃ x φ )
    s3 = lb.ref(
        "s3",
        "∀ x ( φ ↔ x = y ) → ( ∃ x x = y → ∃ x φ )",
        s2,
        ref="aleximi",
        note="aleximi biimpr",
    )

    # mpi ax6ev, aleximi: ∀ x ( φ ↔ x = y ) → ∃ x φ
    s4 = lb.ref(
        "s4",
        "∀ x ( φ ↔ x = y ) → ∃ x φ",
        s1,
        s3,
        ref="mpi",
        note="mpi ax6ev, aleximi",
    )

    # exlimiv mpi: ∃ y ∀ x ( φ ↔ x = y ) → ∃ x φ
    s5 = lb.ref(
        "s5",
        "∃ y ∀ x ( φ ↔ x = y ) → ∃ x φ",
        s4,
        ref="exlimiv",
        note="exlimiv mpi",
    )

    # pm4.71ri exlimiv: ∃ y ∀ x ( φ ↔ x = y ) ↔ ( ∃ x φ ∧ ∃ y ∀ x ( φ ↔ x = y ) )
    s6 = lb.ref(
        "s6",
        "∃ y ∀ x ( φ ↔ x = y ) ↔ ( ∃ x φ ∧ ∃ y ∀ x ( φ ↔ x = y ) )",
        s5,
        ref="pm4.71ri",
        note="pm4.71ri exlimiv",
    )

    # abai: ( ∃ x φ ∧ ∃ y ∀ x ( φ ↔ x = y ) ) ↔ ( ∃ x φ ∧ ( ∃ x φ → ∃ y ∀ x ( φ ↔ x = y ) ) )
    s7 = lb.ref(
        "s7",
        "( ∃ x φ ∧ ∃ y ∀ x ( φ ↔ x = y ) ) ↔ ( ∃ x φ ∧ ( ∃ x φ → ∃ y ∀ x ( φ ↔ x = y ) ) )",
        ref="abai",
        note="abai",
    )

    # dfmoeu: ( ∃ x φ → ∃ y ∀ x ( φ ↔ x = y ) ) ↔ ∃ y ∀ x ( φ → x = y )
    s8 = lb.ref(
        "s8",
        "( ∃ x φ → ∃ y ∀ x ( φ ↔ x = y ) ) ↔ ∃ y ∀ x ( φ → x = y )",
        ref="dfmoeu",
        note="dfmoeu",
    )

    # anbi2i dfmoeu: ( ∃ x φ ∧ ( ∃ x φ → ∃ y ∀ x ( φ ↔ x = y ) ) ) ↔ ( ∃ x φ ∧ ∃ y ∀ x ( φ → x = y ) )
    s9 = lb.ref(
        "s9",
        "( ∃ x φ ∧ ( ∃ x φ → ∃ y ∀ x ( φ ↔ x = y ) ) ) ↔ ( ∃ x φ ∧ ∃ y ∀ x ( φ → x = y ) )",
        s8,
        ref="anbi2i",
        note="anbi2i dfmoeu",
    )

    # 3bitrri pm4.71ri, abai, anbi2i: ( ∃ x φ ∧ ∃ y ∀ x ( φ → x = y ) ) ↔ ∃ y ∀ x ( φ ↔ x = y )
    res = lb.ref(
        "res",
        "( ∃ x φ ∧ ∃ y ∀ x ( φ → x = y ) ) ↔ ∃ y ∀ x ( φ ↔ x = y )",
        s6,
        s7,
        s9,
        ref="3bitrri",
        note="3bitrri pm4.71ri, abai, anbi2i",
    )

    return lb.build(res)


def prove_axc15(sys: System) -> Proof:
    """axc15: ¬ ∀ x x = y → ( x = y → ( φ → ∀ x ( x = y → φ ) ) ).

    Given a distinctor ¬ ∀ x x = y, the key identity axiom ax-12
    (ax12v) holds. The proof introduces a fresh variable z via
    ax6ev, then uses dveeq2 to lift the hypothesis and ax12v to
    substitute z for y, finishing with equeuclr, sps, imim1d,
    al2imi, imim12d, syl6mpi, exlimdv, and mpi.
    (Contributed by NM, 27-Dec-1992.)
    """
    lb = ProofBuilder(sys, "axc15")

    # 1. ax6ev: ∃ z z = y
    s1 = lb.ref("s1", "∃ z z = y", ref="ax6ev", note="ax6ev")

    # 2. dveeq2: ¬ ∀ x x = y → ( z = y → ∀ x z = y )
    s2 = lb.ref(
        "s2",
        "¬ ∀ x x = y → ( z = y → ∀ x z = y )",
        ref="dveeq2",
        note="dveeq2",
    )

    # 3. ax12v with y:=z: x = z → ( φ → ∀ x ( x = z → φ ) )
    s3 = lb.ref(
        "s3",
        "x = z → ( φ → ∀ x ( x = z → φ ) )",
        ref="ax12v",
        note="ax12v",
    )

    # 4. equeuclr with x:=z, y:=x, z:=y: z = y → ( x = y → x = z )
    s4 = lb.ref(
        "s4",
        "z = y → ( x = y → x = z )",
        ref="equeuclr",
        note="equeuclr",
    )

    # 5. sps(s4): ∀ x z = y → ( x = y → x = z )
    s5 = lb.ref(
        "s5",
        "∀ x z = y → ( x = y → x = z )",
        s4,
        ref="sps",
        note="sps equeuclr",
    )

    # 6. Same as s4: z = y → ( x = y → x = z )
    s6 = lb.ref(
        "s6",
        "z = y → ( x = y → x = z )",
        ref="equeuclr",
        note="equeuclr",
    )

    # 7. imim1d(s6): z = y → ( ( x = z → φ ) → ( x = y → φ ) )
    s7 = lb.ref(
        "s7",
        "z = y → ( ( x = z → φ ) → ( x = y → φ ) )",
        s6,
        ref="imim1d",
        note="imim1d equeuclr",
    )

    # 8. al2imi(s7): ∀ x z = y → ( ∀ x ( x = z → φ ) → ∀ x ( x = y → φ ) )
    s8 = lb.ref(
        "s8",
        "∀ x z = y → ( ∀ x ( x = z → φ ) → ∀ x ( x = y → φ ) )",
        s7,
        ref="al2imi",
        note="al2imi imim1d",
    )

    # 9. imim2d(s8): ∀ x z = y → ( ( φ → ∀ x ( x = z → φ ) ) → ( φ → ∀ x ( x = y → φ ) ) )
    s9 = lb.ref(
        "s9",
        "∀ x z = y → ( ( φ → ∀ x ( x = z → φ ) ) → ( φ → ∀ x ( x = y → φ ) ) )",
        s8,
        ref="imim2d",
        note="imim2d al2imi",
    )

    # 10. imim12d(s5, s9):
    #     ∀ x z = y → ( ( x = z → ( φ → ∀ x ( x = z → φ ) ) ) → ( x = y → ( φ → ∀ x ( x = y → φ ) ) ) )
    s10 = lb.ref(
        "s10",
        "∀ x z = y → ( ( x = z → ( φ → ∀ x ( x = z → φ ) ) ) → ( x = y → ( φ → ∀ x ( x = y → φ ) ) ) )",
        s5,
        s9,
        ref="imim12d",
        note="imim12d sps, imim2d",
    )

    # 11. syl6mpi(s2, s3, s10):
    #     ¬ ∀ x x = y → ( z = y → ( x = y → ( φ → ∀ x ( x = y → φ ) ) ) )
    s11 = lb.ref(
        "s11",
        "¬ ∀ x x = y → ( z = y → ( x = y → ( φ → ∀ x ( x = y → φ ) ) ) )",
        s2,
        s3,
        s10,
        ref="syl6mpi",
        note="syl6mpi dveeq2, ax12v, imim12d",
    )

    # 12. exlimdv(s11):
    #     ¬ ∀ x x = y → ( ∃ z z = y → ( x = y → ( φ → ∀ x ( x = y → φ ) ) ) )
    s12 = lb.ref(
        "s12",
        "¬ ∀ x x = y → ( ∃ z z = y → ( x = y → ( φ → ∀ x ( x = y → φ ) ) ) )",
        s11,
        ref="exlimdv",
        note="exlimdv syl6mpi",
    )

    # 13. mpi(s1, s12):
    #     ¬ ∀ x x = y → ( x = y → ( φ → ∀ x ( x = y → φ ) ) )
    res = lb.ref(
        "res",
        "¬ ∀ x x = y → ( x = y → ( φ → ∀ x ( x = y → φ ) ) )",
        s1,
        s12,
        ref="mpi",
        note="mpi ax6ev, exlimdv",
    )

    return lb.build(res)


def prove_ax12(sys: System) -> Proof:
    """ax12: x = y → ( ∀ y φ → ∀ x ( x = y → φ ) ).

    The original axiom ax-12 re-derived from ax12v (via sp), axc11r,
    and axc15 on top of Tarski's FOL.
    (Contributed by NM, 22-Jan-2007.)
    """
    lb = ProofBuilder(sys, "ax12")

    # 1. axc11r: ∀ x x = y → ( ∀ y φ → ∀ x φ )
    s1 = lb.ref(
        "s1",
        "∀ x x = y → ( ∀ y φ → ∀ x φ )",
        ref="axc11r",
        note="axc11r",
    )

    # 2. ala1: ∀ x φ → ∀ x ( x = y → φ )
    s2 = lb.ref(
        "s2",
        "∀ x φ → ∀ x ( x = y → φ )",
        ref="ala1",
        note="ala1",
    )

    # 3. syl6(1, 2): ∀ x x = y → ( ∀ y φ → ∀ x ( x = y → φ ) )
    s3 = lb.ref(
        "s3",
        "∀ x x = y → ( ∀ y φ → ∀ x ( x = y → φ ) )",
        s1,
        s2,
        ref="syl6",
        note="syl6 axc11r, ala1",
    )

    # 4. a1d(3): ∀ x x = y → ( x = y → ( ∀ y φ → ∀ x ( x = y → φ ) ) )
    s4 = lb.ref(
        "s4",
        "∀ x x = y → ( x = y → ( ∀ y φ → ∀ x ( x = y → φ ) ) )",
        s3,
        ref="a1d",
        note="a1d syl6",
    )

    # 5. sp: ∀ y φ → φ
    s5 = lb.ref(
        "s5",
        "∀ y φ → φ",
        ref="sp",
        note="sp",
    )

    # 6. axc15: ¬ ∀ x x = y → ( x = y → ( φ → ∀ x ( x = y → φ ) ) )
    s6 = lb.ref(
        "s6",
        "¬ ∀ x x = y → ( x = y → ( φ → ∀ x ( x = y → φ ) ) )",
        ref="axc15",
        note="axc15",
    )

    # 7. syl7(5, 6): ¬ ∀ x x = y → ( x = y → ( ∀ y φ → ∀ x ( x = y → φ ) ) )
    s7 = lb.ref(
        "s7",
        "¬ ∀ x x = y → ( x = y → ( ∀ y φ → ∀ x ( x = y → φ ) ) )",
        s5,
        s6,
        ref="syl7",
        note="syl7 sp, axc15",
    )

    # 8. pm2.61i(4, 7): x = y → ( ∀ y φ → ∀ x ( x = y → φ ) )
    res = lb.ref(
        "res",
        "x = y → ( ∀ y φ → ∀ x ( x = y → φ ) )",
        s4,
        s7,
        ref="pm2.61i",
        note="pm2.61i a1d, syl7",
    )

    return lb.build(res)


def prove_ax12b(sys: System) -> Proof:
    """ax12b: ( ¬ ∀ x x = y ∧ x = y ) → ( φ ↔ ∀ x ( x = y → φ ) ).

    Equivalence of a formula and its universal closure given a distinctor
    and the equality of the variable with another.
    (Contributed by NM, 27-Dec-1992.)
    """
    lb = ProofBuilder(sys, "ax12b")

    # axc15: ¬ ∀ x x = y → ( x = y → ( φ → ∀ x ( x = y → φ ) ) )
    s_axc15 = lb.ref(
        "s_axc15",
        "¬ ∀ x x = y → ( x = y → ( φ → ∀ x ( x = y → φ ) ) )",
        ref="axc15",
        note="axc15",
    )

    # imp: ( ¬ ∀ x x = y ∧ x = y ) → ( φ → ∀ x ( x = y → φ ) )
    s_fwd = lb.ref(
        "s_fwd",
        "( ¬ ∀ x x = y ∧ x = y ) → ( φ → ∀ x ( x = y → φ ) )",
        s_axc15,
        ref="imp",
        note="imp axc15",
    )

    # sp: ∀ x ( x = y → φ ) → ( x = y → φ )
    s_sp = lb.ref(
        "s_sp",
        "∀ x ( x = y → φ ) → ( x = y → φ )",
        ref="sp",
        note="sp",
    )

    # com12: x = y → ( ∀ x ( x = y → φ ) → φ )
    s_com12 = lb.ref(
        "s_com12",
        "x = y → ( ∀ x ( x = y → φ ) → φ )",
        s_sp,
        ref="com12",
        note="com12 sp",
    )

    # adantl: ( ¬ ∀ x x = y ∧ x = y ) → ( ∀ x ( x = y → φ ) → φ )
    s_rev = lb.ref(
        "s_rev",
        "( ¬ ∀ x x = y ∧ x = y ) → ( ∀ x ( x = y → φ ) → φ )",
        s_com12,
        ref="adantl",
        note="adantl com12",
    )

    # impbid: ( ¬ ∀ x x = y ∧ x = y ) → ( φ ↔ ∀ x ( x = y → φ ) )
    res = lb.ref(
        "res",
        "( ¬ ∀ x x = y ∧ x = y ) → ( φ ↔ ∀ x ( x = y → φ ) )",
        s_fwd,
        s_rev,
        ref="impbid",
        note="impbid imp, adantl",
    )

    return lb.build(res)


def prove_ax12vALT(sys: System) -> Proof:
    """ax12vALT: x = y → ( φ → ∀ x ( x = y → φ ) ).

    Alternate proof of ax12v using axc15 and axc16 instead of ax12.
    (Contributed by NM, 26-Jun-1993.)
    """
    lb = ProofBuilder(sys, "ax12vALT")

    # 1. ax-1: φ → ( x = y → φ )
    s1 = lb.ref(
        "s1",
        "φ → ( x = y → φ )",
        ref="ax-1",
        note="A1",
    )

    # 2. axc16: ∀ x x = y → ( ( x = y → φ ) → ∀ x ( x = y → φ ) )
    s2 = lb.ref(
        "s2",
        "∀ x x = y → ( ( x = y → φ ) → ∀ x ( x = y → φ ) )",
        ref="axc16",
        note="axc16",
    )

    # 3. syl5(1, 2): ∀ x x = y → ( φ → ∀ x ( x = y → φ ) )
    s3 = lb.ref(
        "s3",
        "∀ x x = y → ( φ → ∀ x ( x = y → φ ) )",
        s1,
        s2,
        ref="syl5",
        note="syl5 A1, axc16",
    )

    # 4. a1d(3): ∀ x x = y → ( x = y → ( φ → ∀ x ( x = y → φ ) ) )
    s4 = lb.ref(
        "s4",
        "∀ x x = y → ( x = y → ( φ → ∀ x ( x = y → φ ) ) )",
        s3,
        ref="a1d",
        note="a1d syl5",
    )

    # 5. axc15: ¬ ∀ x x = y → ( x = y → ( φ → ∀ x ( x = y → φ ) ) )
    s5 = lb.ref(
        "s5",
        "¬ ∀ x x = y → ( x = y → ( φ → ∀ x ( x = y → φ ) ) )",
        ref="axc15",
        note="axc15",
    )

    # 6. pm2.61i(4, 5): ( x = y → ( φ → ∀ x ( x = y → φ ) ) )
    res = lb.ref(
        "res",
        "x = y → ( φ → ∀ x ( x = y → φ ) )",
        s4,
        s5,
        ref="pm2.61i",
        note="pm2.61i a1d, axc15",
    )

    return lb.build(res)


def prove_ax12wdemo(sys: System) -> Proof:
    """ax12wdemo: x = y → ( ∀ y ( x ∈ y ∧ ∀ x z ∈ x ∧ ∀ y ∀ z y ∈ x ) → ∀ x ( x = y → ( x ∈ y ∧ ∀ x z ∈ x ∧ ∀ y ∀ z y ∈ x ) ) ).

    Example of the procedure to eliminate the hypotheses of ax12w when φ is
    substituted with an expression not containing wff metavariables.
    (Contributed by NM, 10-Apr-2017.)
    """
    lb = ProofBuilder(sys, "ax12wdemo")

    # 60. elequ1: x = y → ( x ∈ y ↔ y ∈ y )
    s60 = lb.ref(
        "s60",
        "x = y → ( x ∈ y ↔ y ∈ y )",
        ref="elequ1",
        note="elequ1",
    )

    # 72. elequ2: x = w → ( z ∈ x ↔ z ∈ w )
    s72 = lb.ref(
        "s72",
        "x = w → ( z ∈ x ↔ z ∈ w )",
        ref="elequ2",
        note="elequ2",
    )

    # 73. cbvalvw s72: ∀ x z ∈ x ↔ ∀ w z ∈ w
    s73 = lb.ref(
        "s73",
        "∀ x z ∈ x ↔ ∀ w z ∈ w",
        s72,
        ref="cbvalvw",
        note="cbvalvw elequ2",
    )

    # 74. a1i s73: x = y → ( ∀ x z ∈ x ↔ ∀ w z ∈ w )
    s74 = lb.ref(
        "s74",
        "x = y → ( ∀ x z ∈ x ↔ ∀ w z ∈ w )",
        s73,
        ref="a1i",
        note="a1i cbvalvw",
    )

    # 92. elequ1: y = v → ( y ∈ x ↔ v ∈ x )
    s92 = lb.ref(
        "s92",
        "y = v → ( y ∈ x ↔ v ∈ x )",
        ref="elequ1",
        note="elequ1",
    )

    # 93. albidv s92: y = v → ( ∀ z y ∈ x ↔ ∀ z v ∈ x )
    s93 = lb.ref(
        "s93",
        "y = v → ( ∀ z y ∈ x ↔ ∀ z v ∈ x )",
        s92,
        ref="albidv",
        note="albidv elequ1",
    )

    # 94. cbvalvw s93: ∀ y ∀ z y ∈ x ↔ ∀ v ∀ z v ∈ x
    s94 = lb.ref(
        "s94",
        "∀ y ∀ z y ∈ x ↔ ∀ v ∀ z v ∈ x",
        s93,
        ref="cbvalvw",
        note="cbvalvw albidv",
    )

    # 106. elequ2: x = y → ( v ∈ x ↔ v ∈ y )
    s106 = lb.ref(
        "s106",
        "x = y → ( v ∈ x ↔ v ∈ y )",
        ref="elequ2",
        note="elequ2",
    )

    # 107. albidv s106: x = y → ( ∀ z v ∈ x ↔ ∀ z v ∈ y )
    s107 = lb.ref(
        "s107",
        "x = y → ( ∀ z v ∈ x ↔ ∀ z v ∈ y )",
        s106,
        ref="albidv",
        note="albidv elequ2",
    )

    # 108. albidv s107: x = y → ( ∀ v ∀ z v ∈ x ↔ ∀ v ∀ z v ∈ y )
    s108 = lb.ref(
        "s108",
        "x = y → ( ∀ v ∀ z v ∈ x ↔ ∀ v ∀ z v ∈ y )",
        s107,
        ref="albidv",
        note="albidv albidv",
    )

    # 109. bitrid s94, s108: x = y → ( ∀ y ∀ z y ∈ x ↔ ∀ v ∀ z v ∈ y )
    s109 = lb.ref(
        "s109",
        "x = y → ( ∀ y ∀ z y ∈ x ↔ ∀ v ∀ z v ∈ y )",
        s94,
        s108,
        ref="bitrid",
        note="bitrid cbvalvw, albidv",
    )

    # 110. 3anbi123d s60, s74, s109:
    # x = y → ( ( x ∈ y ∧ ∀ x z ∈ x ∧ ∀ y ∀ z y ∈ x ) ↔ ( y ∈ y ∧ ∀ w z ∈ w ∧ ∀ v ∀ z v ∈ y ) )
    s110 = lb.ref(
        "s110",
        "x = y → ( ( x ∈ y ∧ ∀ x z ∈ x ∧ ∀ y ∀ z y ∈ x ) ↔ ( y ∈ y ∧ ∀ w z ∈ w ∧ ∀ v ∀ z v ∈ y ) )",
        s60,
        s74,
        s109,
        ref="3anbi123d",
        note="3anbi123d elequ1, a1i, bitrid",
    )

    # 120. elequ2: y = v → ( x ∈ y ↔ x ∈ v )
    s120 = lb.ref(
        "s120",
        "y = v → ( x ∈ y ↔ x ∈ v )",
        ref="elequ2",
        note="elequ2",
    )

    # 126. a1i s94: y = v → ( ∀ y ∀ z y ∈ x ↔ ∀ v ∀ z v ∈ x )
    s126 = lb.ref(
        "s126",
        "y = v → ( ∀ y ∀ z y ∈ x ↔ ∀ v ∀ z v ∈ x )",
        s94,
        ref="a1i",
        note="a1i cbvalvw",
    )

    # 127. 3anbi13d s120, s126:
    # y = v → ( ( x ∈ y ∧ ∀ x z ∈ x ∧ ∀ y ∀ z y ∈ x ) ↔ ( x ∈ v ∧ ∀ x z ∈ x ∧ ∀ v ∀ z v ∈ x ) )
    s127 = lb.ref(
        "s127",
        "y = v → ( ( x ∈ y ∧ ∀ x z ∈ x ∧ ∀ y ∀ z y ∈ x ) ↔ ( x ∈ v ∧ ∀ x z ∈ x ∧ ∀ v ∀ z v ∈ x ) )",
        s120,
        s126,
        ref="3anbi13d",
        note="3anbi13d elequ2, a1i",
    )

    # 128. ax12w s110, s127:
    # x = y → ( ∀ y ( x ∈ y ∧ ∀ x z ∈ x ∧ ∀ y ∀ z y ∈ x ) → ∀ x ( x = y → ( x ∈ y ∧ ∀ x z ∈ x ∧ ∀ y ∀ z y ∈ x ) ) )
    res = lb.ref(
        "res",
        "x = y → ( ∀ y ( x ∈ y ∧ ∀ x z ∈ x ∧ ∀ y ∀ z y ∈ x ) → ∀ x ( x = y → ( x ∈ y ∧ ∀ x z ∈ x ∧ ∀ y ∀ z y ∈ x ) ) )",
        s110,
        s127,
        ref="ax12w",
        note="ax12w 3anbi123d, 3anbi13d",
    )

    return lb.build(res)


MIGRATION_THEOREMS: Mapping[str, PredicateTheoremCtor] = {
    "ax12": prove_ax12,
    "ax12b": prove_ax12b,
    "ax12vALT": prove_ax12vALT,
    "ax12wdemo": prove_ax12wdemo,
    "axc15": prove_axc15,
    "2ax6e": prove_2ax6e,
    "2ax6elem": prove_2ax6elem,
    "sbex": prove_sbex,
    "sbmo": prove_sbmo,
    "sb2": prove_sb2,
    "sb2ae": prove_sb2ae,
    "spsd": prove_spsd,
    "axc16": prove_axc16,
    "axc16ALT": prove_axc16ALT,
    "axc16i": prove_axc16i,
    "axc16g": prove_axc16g,
    "axc16gALT": prove_axc16gALT,
    "axc16gb": prove_axc16gb,
    "axc16nf": prove_axc16nf,
    "axc16nfALT": prove_axc16nfALT,
    "sbn": prove_sbn,
    "sbi2": prove_sbi2,
    "sbim": prove_sbim,
    "sbor": prove_sbor,
    "sbnf": prove_sbnf,
    "sbnf2": prove_sbnf2,
    "19.41vvv": prove_19_41vvv,
    "19.41vvvv": prove_19_41vvvv,
    "2mo": prove_2mo,
    "2mos": prove_2mos,
    "2mo2": prove_2mo2,
    "2moex": prove_2moex,
    "2moexv": prove_2moexv,
    "2moswapv": prove_2moswapv,
    "2moswap": prove_2moswap,
    "2euswap": prove_2euswap,
    "2euswapv": prove_2euswapv,
    "2eu1": prove_2eu1,
    "2eu1v": prove_2eu1v,
    "2eu2": prove_2eu2,
    "2eu3": prove_2eu3,
    "2eu4": prove_2eu4,
    "2eu5": prove_2eu5,
    "2eu6": prove_2eu6,
    "2eu7": prove_2eu7,
    "2eu8": prove_2eu8,
    "2euex": prove_2euex,
    "2exeu": prove_2exeu,
    "2exeuv": prove_2exeuv,
    "2euexv": prove_2euexv,
    "ax13": prove_ax13,
    "ax13ALT": prove_ax13ALT,
    "axi10": prove_axi10,
    "axi12": prove_axi12,
    "axi4": prove_axi4,
    "axbnd": prove_axbnd,
    "axc10": prove_axc10,
    "axc11r": prove_axc11r,
    "axc11rv": prove_axc11rv,
    "axc11v": prove_axc11v,
    "axc11": prove_axc11,
    "axc11n": prove_axc11n,
    "axc14": prove_axc14,
    "axi5r": prove_axi5r,
    "axie2": prove_axie2,
    "cbv3": prove_cbv3,
    "cbv3h": prove_cbv3h,
    "cbval": prove_cbval,
    "cbvalv": prove_cbvalv,
    "cbvex": prove_cbvex,
    "cbvexv": prove_cbvexv,
    "cbvex2": prove_cbvex2,
    "cbvex2vv": prove_cbvex2vv,
    "cbvex4v": prove_cbvex4v,
    "cbval2": prove_cbval2,
    "cbval2v": prove_cbval2v,
    "cbval2vv": prove_cbval2vv,
    "cbvex2v": prove_cbvex2v,
    "cbvald": prove_cbvald,
    "cbvaldw": prove_cbvaldw,
    "cbvaldva": prove_cbvaldva,
    "cbvexd": prove_cbvexd,
    "cbvexdva": prove_cbvexdva,
    "cbvexdw": prove_cbvexdw,
    "cbv1": prove_cbv1,
    "cbv1h": prove_cbv1h,
    "cbv2": prove_cbv2,
    "cbv2h": prove_cbv2h,
    "cbv2w": prove_cbv2w,
    "cbv3v": prove_cbv3v,
    "cbv3v2": prove_cbv3v2,
    "cbv3hv": prove_cbv3hv,
    "cbv1v": prove_cbv1v,
    "cbvalv1": prove_cbvalv1,
    "cbvexv1": prove_cbvexv1,
    "aaan": prove_aaan,
    "aecom": prove_aecom,
    "aecoms": prove_aecoms,
    "ax6": prove_ax6,
    "axi9": prove_axi9,
    "19.32": prove_19_32,
    "19.31": prove_19_31,
    "albid": prove_albid,
    "alrimi": prove_alrimi,
    "alrimd": prove_alrimd,
    "alrimdd": prove_alrimdd,
    "19.3": prove_19_3,
    "19.3t": prove_19_3t,
    "19.23t": prove_19_23t,
    "19.16": prove_19_16,
    "19.23": prove_19_23,
    "19.23h": prove_19_23h,
    "19.17": prove_19_17,
    "19.19": prove_19_19,
    "19.12": prove_19_12,
    "19.12vv": prove_19_12vv,
    "19.9": prove_19_9,
    "19.41": prove_19_41,
    "19.42": prove_19_42,
    "19.42vv": prove_19_42vv,
    "19.45": prove_19_45,
    "19.44": prove_19_44,
    "dveeq2": prove_dveeq2,
    "dveeq2ALT": prove_dveeq2ALT,
    "dveeq1": prove_dveeq1,
    "dveel1": prove_dveel1,
    "dveel2": prove_dveel2,
    "dral1": prove_dral1,
    "dral1ALT": prove_dral1ALT,
    "dral1v": prove_dral1v,
    "dral2": prove_dral2,
    "drex1": prove_drex1,
    "drex1v": prove_drex1v,
    "drex2": prove_drex2,
    "drnf1": prove_drnf1,
    "drnf2": prove_drnf2,
    "drnf1v": prove_drnf1v,
    "drsb1": prove_drsb1,
    "drsb2": prove_drsb2,
    "eean": prove_eean,
    "eeanv": prove_eeanv,
    "eeeanv": prove_eeeanv,
    "ee4anv": prove_ee4anv,
    "ee4anvOLD": prove_ee4anvOLD,
    "eeor": prove_eeor,
    "equvini": prove_equvini,
    "equvel": prove_equvel,
    "eu1": prove_eu1,
    "eu2": prove_eu2,
    "eujustALT": prove_eujustALT,
    "eu4": prove_eu4,
    "eupick": prove_eupick,
    "eupicka": prove_eupicka,
    "eupickb": prove_eupickb,
    "eupickbi": prove_eupickbi,
    "euimmo": prove_euimmo,
    "euim": prove_euim,
    "exbid": prove_exbid,
    "excomim": prove_excomim,
    "excomimw": prove_excomimw,
    "excomw": prove_excomw,
    "exexw": prove_exexw,
    "excom13": prove_excom13,
    "exrot3": prove_exrot3,
    "exrot4": prove_exrot4,
    "2sp": prove_2sp,
    "19.9d": prove_19_9d,
    "19.9h": prove_19_9h,
    "19.9ht": prove_19_9ht,
    "nf5r": prove_nf5r,
    "nf5rd": prove_nf5rd,
    "nf5": prove_nf5,
    "nf5ri": prove_nf5ri,
    "nf5di": prove_nf5di,
    "nfae": prove_nfae,
    "nfal": prove_nfal,
    "nfnae": prove_nfnae,
    "nfald": prove_nfald,
    "nfald2": prove_nfald2,
    "nfex": prove_nfex,
    "nfexd": prove_nfexd,
    "nfexd2": prove_nfexd2,
    "nfexhe": prove_nfexhe,
    "19.27": prove_19_27,
    "19.28": prove_19_28,
    "nfnf": prove_nfnf,
    "qexmid": prove_qexmid,
    "rename-sb": prove_rename_sb,
    "dfsb": prove_dfsb,
    "dfsb2": prove_dfsb2,
    "dfsb3": prove_dfsb3,
    "19.9t": prove_19_9t,
    "19.23bi": prove_19_23bi,
    "2eumo": prove_2eumo,
    "2nexaln": prove_2nexaln,
    "eximd": prove_eximd,
    "exlimi": prove_exlimi,
    "exlimih": prove_exlimih,
    "exlimd": prove_exlimd,
    "exlimdh": prove_exlimdh,
    "exlimimdd": prove_exlimimdd,
    "exlimdd": prove_exlimdd,
    "19.21bbi": prove_19_21bbi,
    "alimd": prove_alimd,
    "axc4": prove_axc4,
    "axc4i": prove_axc4i,
    "axc7": prove_axc7,
    "axc7e": prove_axc7e,
    "axc9": prove_axc9,
    "sb10f": prove_sb10f,
    "sb1": prove_sb1,
    "sb1v": prove_sb1v,
    "sb4a": prove_sb4a,
    "sb4av": prove_sb4av,
    "sb4e": prove_sb4e,
    "sb5": prove_sb5,
    "sb5f": prove_sb5f,
    "sb6": prove_sb6,
    "sb6a": prove_sb6a,
    "sb6f": prove_sb6f,
    "sb6x": prove_sb6x,
    "sb5rf": prove_sb5rf,
    "sb6rf": prove_sb6rf,
    "sb6rfv": prove_sb6rfv,
    "sb8e": prove_sb8e,
    "sb8ef": prove_sb8ef,
    "2sb8e": prove_2sb8e,
    "2sb8ef": prove_2sb8ef,
    "sb8v": prove_sb8v,
    "sb8f": prove_sb8f,
    "sb9": prove_sb9,
    "sb9i": prove_sb9i,
    "sbcom2": prove_sbcom2,
    "sbcom3vv": prove_sbcom3vv,
    "sbcom3": prove_sbcom3,
    "sbcom": prove_sbcom,
    "sbcov": prove_sbcov,
    "sbco": prove_sbco,
    "sbbid": prove_sbbid,
    "sbelx": prove_sbelx,
    "sbel2x": prove_sbel2x,
    "sbequ": prove_sbequ,
    "sbequ1": prove_sbequ1,
    "sbequ12": prove_sbequ12,
    "sbequ12r": prove_sbequ12r,
    "sbequ12a": prove_sbequ12a,
    "sbid": prove_sbid,
    "hbsb2a": prove_hbsb2a,
    "hbsb2e": prove_hbsb2e,
    "hbsb3": prove_hbsb3,
    "sbidm": prove_sbidm,
    "sbid2": prove_sbid2,
    "sbid2v": prove_sbid2v,
    "sbequi": prove_sbequi,
    "sbbiiev": prove_sbbiiev,
    "sbbib": prove_sbbib,
    "sbbibvv": prove_sbbibvv,
    "sbied": prove_sbied,
    "sbiedv": prove_sbiedv,
    "sbiedw": prove_sbiedw,
    "sbiev": prove_sbiev,
    "sbievw": prove_sbievw,
    "sbievw2": prove_sbievw2,
    "sbco2": prove_sbco2,
    "sbco2d": prove_sbco2d,
    "sbco2v": prove_sbco2v,
    "sbco2vv": prove_sbco2vv,
    "sbco3": prove_sbco3,
    "cbvsbv": prove_cbvsbv,
    "cbvsbvf": prove_cbvsbvf,
    "sbcovOLD": prove_sbcovOLD,
    "sbievwOLD": prove_sbievwOLD,
    "sbiedvw": prove_sbiedvw,
    "2sbiev": prove_2sbiev,
    "2sbievw": prove_2sbievw,
    "2sbbid": prove_2sbbid,
    "2sb5": prove_2sb5,
    "2sb6": prove_2sb6,
    "2sb5rf": prove_2sb5rf,
    "2sb6rf": prove_2sb6rf,
    "19.21": prove_19_21,
    "19.21h": prove_19_21h,
    "stdpc5": prove_stdpc5,
    "stdpc4ALT": prove_stdpc4ALT,
    "19.21-2": prove_19_21_2,
    "hbex": prove_hbex,
    "hbim1": prove_hbim1,
    "hbim": prove_hbim,
    "hbimd": prove_hbimd,
    "hbnd": prove_hbnd,
    "hbn": prove_hbn,
    "hbnae": prove_hbnae,
    "hbnaes": prove_hbnaes,
    "hbnt": prove_hbnt,
    "hb3an": prove_hb3an,
    "axial": prove_axial,
    "hba1": prove_hba1,
    "hbae": prove_hbae,
    "hbs1": prove_hbs1,
    "hbsb": prove_hbsb,
    "hbsb2": prove_hbsb2,
    "hbsbw": prove_hbsbw,
    "sbft": prove_sbft,
    "sbf": prove_sbf,
    "sbf2": prove_sbf2,
    "sbrbif": prove_sbrbif,
    "sbrim": prove_sbrim,
    "sblim": prove_sblim,
    "sbtrt": prove_sbtrt,
    "sbtr": prove_sbtr,
    "sbh": prove_sbh,
    "sbhb": prove_sbhb,
    "moan": prove_moan,
    "moani": prove_moani,
    "moanmo": prove_moanmo,
    "moaneu": prove_moaneu,
    "mooran1": prove_mooran1,
    "moanimlem": prove_moanimlem,
    "moanim": prove_moanim,
    "moanimv": prove_moanimv,
    "naecoms": prove_naecoms,
    "19.36": prove_19_36,
    "19.36i": prove_19_36i,
    "19.37": prove_19_37,
    "spim": prove_spim,
    "spimed": prove_spimed,
    "spime": prove_spime,
    "spimefv": prove_spimefv,
    "spimev": prove_spimev,
    "spimedv": prove_spimedv,
    "spimt": prove_spimt,
    "spimfv": prove_spimfv,
    "spimv": prove_spimv,
    "spimvALT": prove_spimvALT,
    "spv": prove_spv,
    "spei": prove_spei,
    "chvarfv": prove_chvarfv,
    "chvar": prove_chvar,
    "chvarv": prove_chvarv,
    "cleljustALT2": prove_cleljustALT2,
    "cleljustALT": prove_cleljustALT,
    "elsb1": prove_elsb1,
    "elsb2": prove_elsb2,
    "equs4": prove_equs4,
    "equs45f": prove_equs45f,
    "equs5": prove_equs5,
    "equs5av": prove_equs5av,
    "equs5a": prove_equs5a,
    "equs5aALT": prove_equs5aALT,
    "equs5eALT": prove_equs5eALT,
    "equs5e": prove_equs5e,
    "equsal": prove_equsal,
    "equsalh": prove_equsalh,
    "equsalv": prove_equsalv,
    "equsalhw": prove_equsalhw,
    "equsex": prove_equsex,
    "equsexv": prove_equsexv,
    "equsexh": prove_equsexh,
    "equsexhv": prove_equsexhv,
    "equsb1": prove_equsb1,
    "equsb1v": prove_equsb1v,
    "equsb2": prove_equsb2,
    "equsb3": prove_equsb3,
    "equsb3r": prove_equsb3r,
    "equsexALT": prove_equsexALT,
    "nexd": prove_nexd,
    "nexr": prove_nexr,
    "nfexa2": prove_nfexa2,
    "nf6": prove_nf6,
    "nfbidf": prove_nfbidf,
    "ru0": prove_ru0,
    "nfeqf": prove_nfeqf,
    "nfeqf1": prove_nfeqf1,
    "nfeu": prove_nfeu,
    "nfeu1": prove_nfeu1,
    "nfeu1ALT": prove_nfeu1ALT,
    "nfeud2": prove_nfeud2,
    "nfeud": prove_nfeud,
    "nfeudw": prove_nfeudw,
    "nfeuw": prove_nfeuw,
    "nfmod2": prove_nfmod2,
    "nfmod": prove_nfmod,
    "nfmo": prove_nfmo,
    "nfmov": prove_nfmov,
    "nfmodv": prove_nfmodv,
    "nfmo1": prove_nfmo1,
    "nfs1": prove_nfs1,
    "nfs1v": prove_nfs1v,
    "nfsbv": prove_nfsbv,
    "nfsb": prove_nfsb,
    "nfsb2": prove_nfsb2,
    "nfsb4t": prove_nfsb4t,
    "nfsb4": prove_nfsb4,
    "nfsbd": prove_nfsbd,
    "cbvmow": prove_cbvmow,
    "cbvmo": prove_cbvmo,
    "cbveuw": prove_cbveuw,
    "cbveu": prove_cbveu,
    "cbveuALT": prove_cbveuALT,
    "mof": prove_mof,
    "mo3": prove_mo3,
    "mo": prove_mo,
    "mo4f": prove_mo4f,
    "modal-b": prove_modal_b,
    "exsb": prove_exsb,
    "mopick2": prove_mopick2,
    "mopick": prove_mopick,
    "moexexlem": prove_moexexlem,
    "moexexvw": prove_moexexvw,
    "moexex": prove_moexex,
    "moexexv": prove_moexexv,
    "barbariALT": prove_barbariALT,
    "barocoALT": prove_barocoALT,
    "daraptiALT": prove_daraptiALT,
    "dariiALT": prove_dariiALT,
    "festinoALT": prove_festinoALT,
    "pm11.53": prove_pm11_53,
    "sbal": prove_sbal,
    "sbal1": prove_sbal1,
    "sbal2": prove_sbal2,
    "sbalex": prove_sbalex,
    "sbalexOLD": prove_sbalexOLD,
    "sbalv": prove_sbalv,
    "sbievOLD": prove_sbievOLD,
    "sbrimvwOLD": prove_sbrimvwOLD,
    "exdistr": prove_exdistr,
    "exdistrf": prove_exdistrf,
    "19.42vvv": prove_19_42vvv,
    "3exdistr": prove_3exdistr,
    "4exdistr": prove_4exdistr,
    "exdistr2": prove_exdistr2,
    "exdistrv": prove_exdistrv,
    "4exdistrv": prove_4exdistrv,
    "eu6lem": prove_eu6lem,
    "eu6im": prove_eu6im,
    "mobi": prove_mobi,
    "mobii": prove_mobii,
    "mobid": prove_mobid,
    "mobidv": prove_mobidv,
    "eubi": prove_eubi,
    "eubii": prove_eubii,
    "eubid": prove_eubid,
    "eubidv": prove_eubidv,
    "euan": prove_euan,
    "euanv": prove_euanv,
    "exists1": prove_exists1,
    "exists2": prove_exists2,
    "euor": prove_euor,
    "euorv": prove_euorv,
    "euor2": prove_euor2,
    "sb7f": prove_sb7f,
    "sb7h": prove_sb7h,
    "dfsb7": prove_dfsb7,
    "dfsb1": prove_dfsb1,
    "sbco4OLD": prove_sbco4OLD,
    "sbco4lemOLD": prove_sbco4lemOLD,
    "sbco4lem": prove_sbco4lem,
    "sbid2vw": prove_sbid2vw,
    "sbequ5": prove_sbequ5,
    "sbequ6": prove_sbequ6,
    "sbequ8": prove_sbequ8,
    "sb8": prove_sb8,
    "dvelim": prove_dvelim,
    "dvelimv": prove_dvelimv,
    "dvelimf": prove_dvelimf,
    "dvelimdf": prove_dvelimdf,
    "dvelimh": prove_dvelimh,
    "dvelimhw": prove_dvelimhw,
    "dvelimnf": prove_dvelimnf,
    "sb3": prove_sb3,
    "sb3b": prove_sb3b,
    "sb4b": prove_sb4b,
    "2exsb": prove_2exsb,
    "sbi1ALT": prove_sbi1ALT,
    "sbie": prove_sbie,
    "dfmo2": prove_dfmo2,
    "dfmoeu": prove_dfmoeu,
    "dfeumo": prove_dfeumo,
    "eu6": prove_eu6,
    "euf": prove_euf,
    "sb8eulem": prove_sb8eulem,
    "sb8euv": prove_sb8euv,
    "sb8eu": prove_sb8eu,
    "sb8mo": prove_sb8mo,
}
