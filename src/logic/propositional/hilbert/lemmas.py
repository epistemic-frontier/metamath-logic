"""Backward-compatible shim — explicit re-exports from knowledge modules.

Static imports so mypy can verify.
"""
from . import System
from skfd.proof import Proof, ProofBuilder

from logic.propositional.hilbert.implication import (
    prove_2a1,
    prove_2a1d,
    prove_a1d,
    prove_a1i,
    prove_a1i13,
    prove_a2d,
    prove_a2i,
    prove_com12,
    prove_id,
    prove_idd,
    prove_imim1,
    prove_imim2,
    prove_mpcom,
    prove_mpd,
    prove_mpdd,
    prove_mpid,
    prove_notnot,
    prove_notnotr,
    prove_pm2_18,
    prove_pm2_18d,
    prove_pm2_37,
    prove_pm2_4,
    prove_pm2_41,
    prove_pm2_42,
    prove_pm2_5,
    prove_pm2_8,
    prove_simplim,
    prove_syl,
    prove_syl5,
    prove_syl5com,
    prove_syl6,
    prove_sylcom,
)
from logic.propositional.hilbert.negation import (
    prove_con1,
    prove_con1d,
    prove_con1i,
    prove_con2,
    prove_con2d,
    prove_con2i,
    prove_con3,
    prove_con3d,
    prove_con3i,
    prove_con4,
    prove_con4d,
    prove_con4i,
    prove_conax1,
    prove_modus_tollens,
    prove_mt2,
    prove_mt3,
    prove_mt4d,
    prove_nsyl,
    prove_nsyl2,
    prove_nsyl3,
    prove_pm2_21,
    prove_pm2_21d,
    prove_pm2_24,
    prove_pm2_45,
    prove_pm2_46,
    prove_pm2_47,
    prove_pm2_48,
    prove_pm2_49,
    prove_pm2_51,
    prove_pm2_52,
    prove_pm2_521,
    prove_pm2_521g,
    prove_pm2_53,
    prove_pm2_54,
    prove_pm2_61,
    prove_pm2_62,
    prove_pm2_63,
    prove_pm2_64,
    prove_pm2_65,
)
from logic.propositional.hilbert.disjunction import (
    prove_ja,
    prove_jaod,
    prove_jaoi,
    prove_jarli,
    prove_olc,
    prove_peirce,
    prove_pm1_4,
    prove_pm2_36,
    prove_pm2_38,
    prove_pm2_621,
    prove_pm2_67,
    prove_pm2_67_2,
    prove_pm2_68,
    prove_pm2_73,
    prove_pm2_74,
    prove_pm2_75,
    prove_pm2_76,
    prove_pm2_81,
    prove_pm2_83,
)
from logic.propositional.hilbert.syllogism import (
    prove_pm2_01,
    prove_pm2_04,
    prove_pm2_07,
    prove_pm2_27,
    prove_pm2_43,
    prove_pm2_6,
    prove_syl11,
    prove_syl2im,
    prove_syl2imc,
    prove_syl56,
    prove_syl6com,
    prove_syli,
)

__all__ = [
    "prove_2a1",
    "prove_2a1d",
    "prove_a1d",
    "prove_a1i",
    "prove_a1i13",
    "prove_a2d",
    "prove_a2i",
    "prove_com12",
    "prove_id",
    "prove_idd",
    "prove_imim1",
    "prove_imim2",
    "prove_mpcom",
    "prove_mpd",
    "prove_mpdd",
    "prove_mpid",
    "prove_notnot",
    "prove_notnotr",
    "prove_pm2_18",
    "prove_pm2_18d",
    "prove_pm2_37",
    "prove_pm2_4",
    "prove_pm2_41",
    "prove_pm2_42",
    "prove_pm2_5",
    "prove_pm2_8",
    "prove_simplim",
    "prove_syl",
    "prove_syl5",
    "prove_syl5com",
    "prove_syl6",
    "prove_sylcom",
    "prove_con1",
    "prove_con1d",
    "prove_con1i",
    "prove_con2",
    "prove_con2d",
    "prove_con2i",
    "prove_con3",
    "prove_con3d",
    "prove_con3i",
    "prove_con4",
    "prove_con4d",
    "prove_con4i",
    "prove_conax1",
    "prove_modus_tollens",
    "prove_mt2",
    "prove_mt3",
    "prove_mt4d",
    "prove_nsyl",
    "prove_nsyl2",
    "prove_nsyl3",
    "prove_pm2_21",
    "prove_pm2_21d",
    "prove_pm2_24",
    "prove_pm2_45",
    "prove_pm2_46",
    "prove_pm2_47",
    "prove_pm2_48",
    "prove_pm2_49",
    "prove_pm2_51",
    "prove_pm2_52",
    "prove_pm2_521",
    "prove_pm2_521g",
    "prove_pm2_53",
    "prove_pm2_54",
    "prove_pm2_61",
    "prove_pm2_62",
    "prove_pm2_63",
    "prove_pm2_64",
    "prove_pm2_65",
    "prove_ja",
    "prove_jaod",
    "prove_jaoi",
    "prove_jarli",
    "prove_olc",
    "prove_peirce",
    "prove_pm1_4",
    "prove_pm2_36",
    "prove_pm2_38",
    "prove_pm2_621",
    "prove_pm2_67",
    "prove_pm2_67_2",
    "prove_pm2_68",
    "prove_pm2_73",
    "prove_pm2_74",
    "prove_pm2_75",
    "prove_pm2_76",
    "prove_pm2_81",
    "prove_pm2_83",
    "prove_pm2_01",
    "prove_pm2_04",
    "prove_pm2_07",
    "prove_pm2_27",
    "prove_pm2_43",
    "prove_pm2_6",
    "prove_syl11",
    "prove_syl2im",
    "prove_syl2imc",
    "prove_syl56",
    "prove_syl6com",
    "prove_syli",
    "prove_imim2i",
    "prove_imim3i",
    "prove_jad",
    "prove_jarl",
    "prove_jarr",
    "prove_loolin",
    "prove_mpdi",
    "prove_mt2d",
    "prove_mt4",
    "prove_mto",
    "prove_notnotri",
    "prove_nsyl4",
    "prove_pm2_01d",
    "prove_pm2_18i",
    "prove_pm2_21dd",
    "prove_pm2_21i",
    "prove_pm2_24d",
    "prove_pm2_24i",
    "prove_pm2_24ii",
    "prove_pm2_43d",
    "prove_pm2_43i",
    "prove_pm2_521g2",
    "prove_pm2_61d",
    "prove_pm2_61d1",
    "prove_pm2_61i",
    "prove_pm2_65i",
    "prove_syld",
    "Proof",
]

# ── Functions defined directly in lemmas.py ──

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
    s1 = lb.ref("s1", "( ( th -> ph ) -> ( th -> ( ps -> ch ) ) )",
        h1, ref="imim2i", note="imim2i")
    res = lb.ref("res", "( ( th -> ph ) -> ( ( th -> ps ) -> ( th -> ch ) ) )",
        s1, ref="a2d", note="a2d")
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
    """jarl: ((ph → ps) → ch) → (¬ph → ch).

    "Jar" with left antecedent negated (forward "ja" partial converse).
    (Contributed by NM, 25-Jun-1993.)
    set.mm proof: pm2.21 imim1i.

    Derivation: pm2.21 gives ¬ph → (ph → ps). Then imim1 chains
    this to get ((ph → ps) → ch) → (¬ph → ch).
    """
    lb = ProofBuilder(sys, "jarl")
    s1 = lb.ref("s1", "( -. ph → ( ph → ps ) )", ref="pm2.21", note="pm2.21")
    s2 = lb.ref("s2",
        "( ( -. ph → ( ph → ps ) ) → ( ( ( ph → ps ) → ch ) → ( -. ph → ch ) ) )",
        ref="imim1", note="imim1")
    res = lb.mp("res", s1, s2, note="MP pm2.21, imim1")
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
    s2 = lb.ref("s2",
        "( ( ps → ( ph → ps ) ) → ( ( ( ph → ps ) → ch ) → ( ps → ch ) ) )",
        ref="imim1", note="imim1")
    res = lb.mp("res", s1, s2, note="MP A1, imim1")
    return lb.build(res)



def prove_loolin(sys: System) -> Proof:
    """loolin: ((ph → ps) → (ps → ph)) → (ps → ph).

    An alternate for the Linearity Axiom of the infinite-valued sentential
    logic (L-infinity) of Lukasiewicz.
    (Contributed by Mel L. O'Cat, 12-Aug-2004.)
    set.mm proof: jarr pm2.43d.
    """
    lb = ProofBuilder(sys, "loolin")
    s1 = lb.ref("s1",
        "( ( ( ph → ps ) → ( ps → ph ) ) → ( ps → ( ps → ph ) ) )",
        ref="jarr", note="jarr")
    res = lb.ref("res",
        "( ( ( ph → ps ) → ( ps → ph ) ) → ( ps → ph ) )",
        s1, ref="pm2.43d", note="pm2.43d")
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
    s1 = lb.ref("s1", "( ph → ( ps → ch ) )",
                h1, ref="a1i", note="a1i")
    res = lb.ref("res", "( ph → ( ps → th ) )",
                 s1, h2, ref="mpdd", note="mpdd")
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
    """mt4: ps.  Hyps: ph, -. ps -> -. ph.

    The rule of modus tollens.  Inference associated with con4i.
    (Contributed by Wolf Lammen, 12-May-2013.)
    set.mm proof: con4i ax-mp.
    """
    lb = ProofBuilder(sys, "mt4")
    h1 = lb.hyp("mt4.1", "ph")
    h2 = lb.hyp("mt4.2", "( -. ps -> -. ph )")
    s1 = lb.ref("s1", "( ph -> ps )", h2, ref="con4i", note="con4i")
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
    """nsyl4: -. ch -> ps. Hyps: ph -> ps, -. ph -> ch.

    (Contributed by Wolf Lammen, 20-May-2024.)
    set.mm proof: con1i syl.
    """
    lb = ProofBuilder(sys, "nsyl4")
    h1 = lb.hyp("nsyl4.1", "( ph -> ps )")
    h2 = lb.hyp("nsyl4.2", "( -. ph -> ch )")
    s1 = lb.ref("s1", "( -. ch -> ph )", h2, ref="con1i", note="con1i")
    res = lb.ref("res", "( -. ch -> ps )", s1, h1, ref="syl", note="syl")
    return lb.build(res)



def prove_pm2_01d(sys: System) -> Proof:
    """pm2.01d: ph -> -. ps.  Hyp: ph -> (ps -> -. ps).

    Deduction based on reductio ad absurdum.
    (Contributed by NM, 18-Aug-1993.)
    set.mm proof: id pm2.61d1.
    """
    lb = ProofBuilder(sys, "pm2.01d")
    h1 = lb.hyp("pm2.01d.1", "( ph -> ( ps -> -. ps ) )")
    # id : (-. ps -> -. ps)
    s_id = lb.ref("s_id", "( -. ps -> -. ps )", ref="id", note="id")
    # pm2.61d1(h1, s_id): ph -> -. ps
    res = lb.ref("res", "( ph -> -. ps )", h1, s_id, ref="pm2.61d1", note="pm2.61d1")
    return lb.build(res)



def prove_pm2_18i(sys: System) -> Proof:
    """pm2.18i: ph.  Hyp: -. ph -> ph.

    Inference associated with the Clavius law pm2.18.
    (Contributed by BJ, 30-Mar-2020.)
    set.mm proof: pm2.18 ax-mp.
    """
    lb = ProofBuilder(sys, "pm2.18i")
    h1 = lb.hyp("pm2.18i.1", "( -. ph -> ph )")
    s1 = lb.ref("s1", "( ( -. ph -> ph ) -> ph )", ref="pm2.18", note="pm2.18")
    res = lb.mp("res", h1, s1, "MP hyp, pm2.18")
    return lb.build(res)



def prove_pm2_21dd(sys: System) -> Proof:
    """pm2.21dd: ph -> ch.  Hyps: ph -> ps, ph -> -. ps.

    A contradiction implies anything.  Deduction from pm2.21.
    (Contributed by Mario Carneiro, 9-Feb-2017.)
    set.mm proof: pm2.65i pm2.21i.
    """
    lb = ProofBuilder(sys, "pm2.21dd")
    h1 = lb.hyp("pm2.21dd.1", "( ph -> ps )")
    h2 = lb.hyp("pm2.21dd.2", "( ph -> -. ps )")
    s1 = lb.ref("s1", "( -. ph )", h1, h2, ref="pm2.65i", note="pm2.65i")
    res = lb.ref("res", "( ph -> ch )", s1, ref="pm2.21i", note="pm2.21i")
    return lb.build(res)



def prove_pm2_21i(sys: System) -> Proof:
    """pm2.21i: ph -> ps.  Hyp: -. ph.

    A contradiction implies anything.  Associated with pm2.21.
    (Contributed by NM, 16-Sep-1993.)
    set.mm proof: a1i con4i.
    """
    lb = ProofBuilder(sys, "pm2.21i")
    h1 = lb.hyp("pm2.21i.1", "( -. ph )")
    s1 = lb.ref("s1", "( -. ps -> -. ph )", h1, ref="a1i", note="a1i")
    res = lb.ref("res", "( ph -> ps )", s1, ref="con4i", note="con4i")
    return lb.build(res)



def prove_pm2_24d(sys: System) -> Proof:
    """pm2.24d: ph -> (-. ps -> ch).  Hyp: ph -> ps.

    Deduction form of pm2.24.
    (Contributed by NM, 30-Jan-2006.)
    set.mm proof: a1d con1d.
    """
    lb = ProofBuilder(sys, "pm2.24d")
    h1 = lb.hyp("pm2.24d.1", "( ph -> ps )")
    s1 = lb.ref("s1", "( ph -> ( -. ch -> ps ) )", h1, ref="a1d", note="a1d")
    res = lb.ref("res", "( ph -> ( -. ps -> ch ) )", s1, ref="con1d", note="con1d")
    return lb.build(res)



def prove_pm2_24i(sys: System) -> Proof:
    """pm2.24i: -. ph -> ps.  Hyp: ph.

    Inference associated with pm2.24.
    (Contributed by NM, 20-Aug-2001.)
    set.mm proof: a1i con1i.
    """
    lb = ProofBuilder(sys, "pm2.24i")
    h1 = lb.hyp("pm2.24i.1", "ph")
    s1 = lb.ref("s1", "( -. ps -> ph )", h1, ref="a1i", note="a1i")
    res = lb.ref("res", "( -. ph -> ps )", s1, ref="con1i", note="con1i")
    return lb.build(res)



def prove_pm2_24ii(sys: System) -> Proof:
    """pm2.24ii: ps.  Hyps: ph, -. ph.

    A contradiction implies anything.  Associated with pm2.21i and pm2.24i.
    (Contributed by NM, 27-Feb-2008.)
    set.mm proof: pm2.21i ax-mp.
    """
    lb = ProofBuilder(sys, "pm2.24ii")
    h1 = lb.hyp("pm2.24ii.1", "ph")
    h2 = lb.hyp("pm2.24ii.2", "( -. ph )")
    s1 = lb.ref("s1", "( ph -> ps )", h2, ref="pm2.21i", note="pm2.21i")
    res = lb.mp("res", h1, s1, "MP hyp1, s1")
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
    res = lb.ref("res", "( ph → ( ps → ch ) )",
                 s_id, h1, ref="mpdi", note="mpdi")
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



def prove_pm2_521g2(sys: System) -> Proof:
    """pm2.521g2: -. ( ph -> ps ) -> ( ch -> ph ).

    A general instance of Theorem *2.521 of [WhiteheadRussell] p. 107.
    (Contributed by NM, 3-Jan-2005.)  (Proof shortened by Wolf Lammen,
    8-Oct-2012.)
    set.mm proof: simplim a1d.  Here we derive simplim as con1(pm2.21).
    """
    lb = ProofBuilder(sys, "pm2.521g2")
    s1 = lb.ref("s1", "( -. ph -> ( ph -> ps ) )", ref="pm2.21",
                note="pm2.21")
    s2 = lb.ref("s2",
        "( ( -. ph -> ( ph -> ps ) ) -> ( -. ( ph -> ps ) -> ph ) )",
        ref="con1", note="con1")
    s3 = lb.mp("s3", s1, s2, note="MP s1,s2: simplim")
    res = lb.ref("res", "( -. ( ph -> ps ) -> ( ch -> ph ) )",
                 s3, ref="a1d", note="a1d")
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



def prove_pm2_61i(sys: System) -> Proof:
    """pm2.61i: ps. Hyps: ph -> ps, -. ph -> ps.

    Inference eliminating an antecedent.
    (Contributed by NM, 5-Apr-1994.)
    set.mm proof: nsyl4 pm2.18i.
    """
    lb = ProofBuilder(sys, "pm2.61i")
    h1 = lb.hyp("pm2.61i.1", "( ph -> ps )")
    h2 = lb.hyp("pm2.61i.2", "( -. ph -> ps )")
    s1 = lb.ref("s1", "( -. ps -> ps )", h1, h2, ref="nsyl4", note="nsyl4")
    res = lb.ref("res", "ps", s1, ref="pm2.18i", note="pm2.18i")
    return lb.build(res)



def prove_pm2_65i(sys: System) -> Proof:
    """pm2.65i: -. ph.  Hyps: ph -> ps, ph -> -. ps.

    Inference for proof by contradiction.
    (Contributed by NM, 18-May-1994.)
    set.mm proof: con2i con3i pm2.61i.
    """
    lb = ProofBuilder(sys, "pm2.65i")
    h1 = lb.hyp("pm2.65i.1", "( ph -> ps )")
    h2 = lb.hyp("pm2.65i.2", "( ph -> -. ps )")
    s_con2i = lb.ref("s_con2i", "( ps -> -. ph )", h2, ref="con2i", note="con2i")
    s_con3i = lb.ref("s_con3i", "( -. ps -> -. ph )", h1, ref="con3i", note="con3i")
    res = lb.ref("res", "( -. ph )", s_con2i, s_con3i, ref="pm2.61i", note="pm2.61i")
    return lb.build(res)



def prove_syld(sys: System) -> Proof:
    """syld: φ → (ψ → θ). Hyp: φ → (ψ → χ), φ → (χ → θ). (Contributed by NM, 5-Aug-1993.)"""
    lb = ProofBuilder(sys, "syld")
    h1 = lb.hyp("syld.1", "φ → ( ψ → χ )")
    h2 = lb.hyp("syld.2", "φ → ( χ → θ )")
    s1 = lb.ref("s1", "φ → ( ψ → ( χ → θ ) )", h2, ref="a1d", note="a1d")
    res = lb.ref("res", "φ → ( ψ → θ )", h1, s1, ref="mpdd", note="mpdd")
    return lb.build(res)




def prove_mpcom(sys: System) -> Proof:
    """mpcom: ψ → χ. Hyp: ψ → φ, φ → (ψ → χ). (Contributed by NM, 17-Mar-1996.)"""
    lb = ProofBuilder(sys, "mpcom")
    h1 = lb.hyp("mpcom.1", "ψ → φ")
    h2 = lb.hyp("mpcom.2", "φ → ( ψ → χ )")
    s1 = lb.ref("s1", "ψ → ( φ → χ )", h2, ref="com12", note="com12")
    res = lb.ref("res", "ψ → χ", h1, s1, ref="mpd", note="mpd")
    return lb.build(res)
