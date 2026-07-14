"""Truth and falsehood constants skeleton.

set.mm range:
    ``True and false constants`` occupies set.mm lines 11967-12295.

Scope:
    This module is reserved for theorem constructors around ``T.`` and ``F.``:

    - ``wtru`` / ``wfal`` support that is logic-owned rather than prelude-owned
    - theorem-level constants such as ``tru`` and ``fal``
    - helpers such as ``trut``, ``mptru``, ``tbtru``, ``bitru``, ``bifal``
    - falsehood and negation helpers such as ``falim``, ``dfnot``, ``inegd``,
      ``efald``, and ``pm2.21fal``

Boundary:
    set.mm defines ``df-tru`` via temporary predicate/equality syntax
    (``wal``, ``cv``, ``wceq``). Keep the short-term propositional migration
    independent of ``logic.predicate`` by treating ``T.`` and ``F.`` as nullary
    propositional constructors. A later fidelity layer can connect ``df-tru``
    to predicate/equality syntax once that package is ready.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping

from skfd.proof import Proof, ProofBuilder

from . import System


def prove_pm2_21fal(sys: System) -> Proof:
    """pm2.21fal: φ → F. .  Hyps: φ → ψ, φ → -. ψ."""
    lb = ProofBuilder(sys, "pm2.21fal")
    h1 = lb.hyp("pm2.21fal.1", "φ → ψ")
    h2 = lb.hyp("pm2.21fal.2", "φ → -. ψ")
    res = lb.ref("res", "φ → F.", h1, h2, ref="pm2.21dd", note="pm2.21dd")
    return lb.build(res)


def prove_tbwlem3(sys: System) -> Proof:
    """tbwlem3: ( ( ( ( ( ph -> F. ) -> ph ) -> ph ) -> ps ) -> ps ).

    Used to rederive the Lukasiewicz axioms from Tarski-Bernays-Wajsberg'.
    (Contributed by Anthony Hart, 16-Aug-2011.)
    """
    lb = ProofBuilder(sys, "tbwlem3")

    # tbw-ax3 with φ=ph, ψ=F.: P = ((ph → F.) → ph) → ph
    s19 = lb.ref("s19", "( ( ( ph → F. ) → ph ) → ph )", ref="tbw-ax3", note="tbw-ax3")

    # tbw-ax2 with φ=P, ψ=(P → ps): P → ((P → ps) → P)
    s27 = lb.ref(
        "s27",
        "( ( ( ph → F. ) → ph ) → ph ) → ( ( ( ( ( ph → F. ) → ph ) → ph ) → ps ) → ( ( ( ph → F. ) → ph ) → ph ) )",
        ref="tbw-ax2",
        note="tbw-ax2",
    )

    # tbw-ax1 with φ=(P → ps), ψ=P, χ=ps:
    #   ((P → ps) → P) → ((P → ps) → ((P → ps) → ps))
    s31 = lb.ref(
        "s31",
        "( ( ( ( ( ph → F. ) → ph ) → ph ) → ps ) → ( ( ( ph → F. ) → ph ) → ph ) ) → ( ( ( ( ( ph → F. ) → ph ) → ph ) → ps ) → ( ( ( ( ( ph → F. ) → ph ) → ph ) → ps ) → ps ) )",
        ref="tbw-ax1",
        note="tbw-ax1",
    )

    # tbwsyl with s27, s31: P → ((P → ps) → ((P → ps) → ps))
    s32 = lb.ref(
        "s32",
        "( ( ( ph → F. ) → ph ) → ph ) → ( ( ( ( ( ph → F. ) → ph ) → ph ) → ps ) → ( ( ( ( ( ph → F. ) → ph ) → ph ) → ps ) → ps ) )",
        s27,
        s31,
        ref="tbwsyl",
        note="tbwsyl",
    )

    # ax-mp with s19, s32: (P → ps) → ((P → ps) → ps)
    s33 = lb.mp("s33", s19, s32, "MP s19, s32")

    # tbw-ax1 with φ=(P → ps), ψ=((P → ps) → ps), χ=ps:
    #   ((P → ps) → ((P → ps) → ps)) → ((((P → ps) → ps) → ps) → ((P → ps) → ps))
    s44 = lb.ref(
        "s44",
        "( ( ( ( ( ph → F. ) → ph ) → ph ) → ps ) → ( ( ( ( ( ph → F. ) → ph ) → ph ) → ps ) → ps ) ) → ( ( ( ( ( ( ( ph → F. ) → ph ) → ph ) → ps ) → ps ) → ps ) → ( ( ( ( ( ph → F. ) → ph ) → ph ) → ps ) → ps ) )",
        ref="tbw-ax1",
        note="tbw-ax1",
    )

    # tbw-ax3 with φ=((P → ps) → ps), ψ=ps:
    #   ((((P → ps) → ps) → ps) → ((P → ps) → ps)) → ((P → ps) → ps)
    s47 = lb.ref(
        "s47",
        "( ( ( ( ( ( ( ph → F. ) → ph ) → ph ) → ps ) → ps ) → ps ) → ( ( ( ( ( ph → F. ) → ph ) → ph ) → ps ) → ps ) ) → ( ( ( ( ( ph → F. ) → ph ) → ph ) → ps ) → ps )",
        ref="tbw-ax3",
        note="tbw-ax3",
    )

    # tbwsyl with s44, s47:
    #   ((P → ps) → ((P → ps) → ps)) → ((P → ps) → ps)
    s48 = lb.ref(
        "s48",
        "( ( ( ( ( ph → F. ) → ph ) → ph ) → ps ) → ( ( ( ( ( ph → F. ) → ph ) → ph ) → ps ) → ps ) ) → ( ( ( ( ( ph → F. ) → ph ) → ph ) → ps ) → ps )",
        s44,
        s47,
        ref="tbwsyl",
        note="tbwsyl",
    )

    # ax-mp with s33, s48: (P → ps) → ps
    res = lb.mp("res", s33, s48, "MP s33, s48")

    return lb.build(res)


def prove_tbwlem4(sys: System) -> Proof:
    """tbwlem4: ( ( ( φ → ⊥ ) → ψ ) → ( ( ψ → ⊥ ) → φ ) ).

    Used to rederive the Lukasiewicz axioms from Tarski-Bernays-Wajsberg'.
    (Contributed by Anthony Hart, 16-Aug-2011.)
    """
    lb = ProofBuilder(sys, "tbwlem4")

    # tbw-ax4 with φ=⊥: ⊥ → ⊥
    s1 = lb.ref("s1", "( ⊥ → ⊥ )", ref="tbw-ax4", note="tbw-ax4")

    # tbw-ax1 with φ=ψ, ψ=⊥, χ=⊥: ( ψ → ⊥ ) → ( ( ⊥ → ⊥ ) → ( ψ → ⊥ ) )
    s2 = lb.ref(
        "s2",
        "( ψ → ⊥ ) → ( ( ⊥ → ⊥ ) → ( ψ → ⊥ ) )",
        ref="tbw-ax1",
        note="tbw-ax1",
    )

    # tbwlem1 with φ=(ψ→⊥), ψ=(⊥→⊥), χ=(ψ→⊥):
    #   ( ( ψ → ⊥ ) → ( ( ⊥ → ⊥ ) → ( ψ → ⊥ ) ) ) → ( ( ⊥ → ⊥ ) → ( ( ψ → ⊥ ) → ( ψ → ⊥ ) ) )
    s3 = lb.ref(
        "s3",
        "( ( ψ → ⊥ ) → ( ( ⊥ → ⊥ ) → ( ψ → ⊥ ) ) ) → ( ( ⊥ → ⊥ ) → ( ( ψ → ⊥ ) → ( ψ → ⊥ ) ) )",
        ref="tbwlem1",
        note="tbwlem1",
    )

    # ax-mp with s2, s3: ( ⊥ → ⊥ ) → ( ( ψ → ⊥ ) → ( ψ → ⊥ ) )
    s4 = lb.mp("s4", s2, s3, "MP s2, s3")

    # ax-mp with s1, s4: ( ψ → ⊥ ) → ( ψ → ⊥ )
    s5 = lb.mp("s5", s1, s4, "MP s1, s4")

    # tbwlem1 with φ=(ψ→⊥), ψ=ψ, χ=⊥:
    #   ( ( ψ → ⊥ ) → ( ψ → ⊥ ) ) → ( ψ → ( ( ψ → ⊥ ) → ⊥ ) )
    s6 = lb.ref(
        "s6",
        "( ( ψ → ⊥ ) → ( ψ → ⊥ ) ) → ( ψ → ( ( ψ → ⊥ ) → ⊥ ) )",
        ref="tbwlem1",
        note="tbwlem1",
    )

    # ax-mp with s5, s6: ψ → ( ( ψ → ⊥ ) → ⊥ )
    s7 = lb.mp("s7", s5, s6, "MP s5, s6")

    # tbw-ax1 with φ=(φ→⊥), ψ=ψ, χ=((ψ→⊥)→⊥):
    #   ( ( φ → ⊥ ) → ψ ) → ( ( ψ → ( ( ψ → ⊥ ) → ⊥ ) ) → ( ( φ → ⊥ ) → ( ( ψ → ⊥ ) → ⊥ ) ) )
    s8 = lb.ref(
        "s8",
        "( ( φ → ⊥ ) → ψ ) → ( ( ψ → ( ( ψ → ⊥ ) → ⊥ ) ) → ( ( φ → ⊥ ) → ( ( ψ → ⊥ ) → ⊥ ) ) )",
        ref="tbw-ax1",
        note="tbw-ax1",
    )

    # tbwlem1 with φ=((φ→⊥)→ψ), ψ=(ψ→((ψ→⊥)→⊥)), χ=((φ→⊥)→((ψ→⊥)→⊥)):
    #   ( ( ( φ → ⊥ ) → ψ ) → ( ( ψ → ( ( ψ → ⊥ ) → ⊥ ) ) → ( ( φ → ⊥ ) → ( ( ψ → ⊥ ) → ⊥ ) ) ) )
    #   → ( ( ψ → ( ( ψ → ⊥ ) → ⊥ ) ) → ( ( ( φ → ⊥ ) → ψ ) → ( ( φ → ⊥ ) → ( ( ψ → ⊥ ) → ⊥ ) ) ) )
    s9 = lb.ref(
        "s9",
        "( ( ( φ → ⊥ ) → ψ ) → ( ( ψ → ( ( ψ → ⊥ ) → ⊥ ) ) → ( ( φ → ⊥ ) → ( ( ψ → ⊥ ) → ⊥ ) ) ) ) → ( ( ψ → ( ( ψ → ⊥ ) → ⊥ ) ) → ( ( ( φ → ⊥ ) → ψ ) → ( ( φ → ⊥ ) → ( ( ψ → ⊥ ) → ⊥ ) ) ) )",
        ref="tbwlem1",
        note="tbwlem1",
    )

    # ax-mp with s8, s9:
    #   ( ψ → ( ( ψ → ⊥ ) → ⊥ ) ) → ( ( ( φ → ⊥ ) → ψ ) → ( ( φ → ⊥ ) → ( ( ψ → ⊥ ) → ⊥ ) ) )
    s10 = lb.mp("s10", s8, s9, "MP s8, s9")

    # ax-mp with s7, s10: ( ( φ → ⊥ ) → ψ ) → ( ( φ → ⊥ ) → ( ( ψ → ⊥ ) → ⊥ ) )
    s11 = lb.mp("s11", s7, s10, "MP s7, s10")

    # tbwlem2 with φ=(φ→⊥), ψ=(ψ→⊥), χ=φ, θ=φ:
    #   ( ( φ → ⊥ ) → ( ( ψ → ⊥ ) → ⊥ ) ) → ( ( ( ( φ → ⊥ ) → φ ) → φ ) → ( ( ψ → ⊥ ) → φ ) )
    s12 = lb.ref(
        "s12",
        "( ( φ → ⊥ ) → ( ( ψ → ⊥ ) → ⊥ ) ) → ( ( ( ( φ → ⊥ ) → φ ) → φ ) → ( ( ψ → ⊥ ) → φ ) )",
        ref="tbwlem2",
        note="tbwlem2",
    )

    # tbwlem3 with ψ=((ψ→⊥)→φ):
    #   ( ( ( ( ( φ → ⊥ ) → φ ) → φ ) → ( ( ψ → ⊥ ) → φ ) ) → ( ( ψ → ⊥ ) → φ )
    s13 = lb.ref(
        "s13",
        "( ( ( ( ( φ → ⊥ ) → φ ) → φ ) → ( ( ψ → ⊥ ) → φ ) ) → ( ( ψ → ⊥ ) → φ ) )",
        ref="tbwlem3",
        note="tbwlem3",
    )

    # tbwsyl with s12, s13: ( ( φ → ⊥ ) → ( ( ψ → ⊥ ) → ⊥ ) ) → ( ( ψ → ⊥ ) → φ )
    s14 = lb.ref(
        "s14",
        "( ( φ → ⊥ ) → ( ( ψ → ⊥ ) → ⊥ ) ) → ( ( ψ → ⊥ ) → φ )",
        s12,
        s13,
        ref="tbwsyl",
        note="tbwsyl",
    )

    # tbwsyl with s11, s14: ( ( φ → ⊥ ) → ψ ) → ( ( ψ → ⊥ ) → φ )
    res = lb.ref(
        "res",
        "( ( φ → ⊥ ) → ψ ) → ( ( ψ → ⊥ ) → φ )",
        s11,
        s14,
        ref="tbwsyl",
        note="tbwsyl",
    )

    return lb.build(res)


def prove_tbwlem5(sys: System) -> Proof:
    """tbwlem5: ( ( ( φ → ( ψ → ⊥ ) ) → ⊥ ) → φ ).

    Used to rederive the Lukasiewicz axioms from Tarski-Bernays-Wajsberg'.
    (Contributed by Anthony Hart, 16-Aug-2011.)
    """
    lb = ProofBuilder(sys, "tbwlem5")

    # tbw-ax2 with φ = ⊥, ψ = ψ: ⊥ → ( ψ → ⊥ )
    s1 = lb.ref("s1", "( ⊥ → ( ψ → ⊥ ) )", ref="tbw-ax2", note="tbw-ax2")

    # tbw-ax1 with φ = φ, ψ = ⊥, χ = ( ψ → ⊥ ):
    #   ( φ → ⊥ ) → ( ( ⊥ → ( ψ → ⊥ ) ) → ( φ → ( ψ → ⊥ ) ) )
    s2 = lb.ref(
        "s2",
        "( φ → ⊥ ) → ( ( ⊥ → ( ψ → ⊥ ) ) → ( φ → ( ψ → ⊥ ) ) )",
        ref="tbw-ax1",
        note="tbw-ax1",
    )

    # tbwlem1 with φ = ( φ → ⊥ ), ψ = ( ⊥ → ( ψ → ⊥ ) ), χ = ( φ → ( ψ → ⊥ ) ):
    #   ( ( φ → ⊥ ) → ( ( ⊥ → ( ψ → ⊥ ) ) → ( φ → ( ψ → ⊥ ) ) ) )
    #   → ( ( ⊥ → ( ψ → ⊥ ) ) → ( ( φ → ⊥ ) → ( φ → ( ψ → ⊥ ) ) ) )
    s3 = lb.ref(
        "s3",
        "( ( φ → ⊥ ) → ( ( ⊥ → ( ψ → ⊥ ) ) → ( φ → ( ψ → ⊥ ) ) ) ) → ( ( ⊥ → ( ψ → ⊥ ) ) → ( ( φ → ⊥ ) → ( φ → ( ψ → ⊥ ) ) ) )",
        ref="tbwlem1",
        note="tbwlem1",
    )

    # ax-mp with s2, s3: ( ⊥ → ( ψ → ⊥ ) ) → ( ( φ → ⊥ ) → ( φ → ( ψ → ⊥ ) ) )
    s4 = lb.mp("s4", s2, s3, "MP s2, s3")

    # ax-mp with s1, s4: ( φ → ⊥ ) → ( φ → ( ψ → ⊥ ) )
    s5 = lb.mp("s5", s1, s4, "MP s1, s4")

    # tbwlem4 with ψ = ( φ → ( ψ → ⊥ ) ):
    #   ( ( φ → ⊥ ) → ( φ → ( ψ → ⊥ ) ) ) → ( ( ( φ → ( ψ → ⊥ ) ) → ⊥ ) → φ )
    s6 = lb.ref(
        "s6",
        "( ( φ → ⊥ ) → ( φ → ( ψ → ⊥ ) ) ) → ( ( ( φ → ( ψ → ⊥ ) ) → ⊥ ) → φ )",
        ref="tbwlem4",
        note="tbwlem4",
    )

    # ax-mp with s5, s6: ( ( φ → ( ψ → ⊥ ) ) → ⊥ ) → φ
    res = lb.mp("res", s5, s6, "MP s5, s6")

    return lb.build(res)


def prove_tru(sys: System) -> Proof:
    """tru: T.

    Truth is provable.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "tru")
    s1 = lb.ref("s1", "( ph -> ph )", ref="id", note="id")
    s2 = lb.ref("s2", "( T. <-> ( ph -> ph ) )", ref="df-tru", note="df-tru")
    res = lb.ref("res", "T.", s1, s2, ref="mpbir", note="mpbir")
    return lb.build(res)


def prove_truan(sys: System) -> Proof:
    """truan: ( ( T. ∧ φ ) ↔ φ ).

    A conjunction with truth is equivalent to the other conjunct.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "truan")
    tru_step = lb.ref("tru_step", "T.", ref="tru", note="tru")
    s_biantrur = lb.ref(
        "s_biantrur", "( φ ↔ ( T. ∧ φ ) )", tru_step, ref="biantrur", note="biantrur"
    )
    res = lb.ref("res", "( ( T. ∧ φ ) ↔ φ )", s_biantrur, ref="bicomi", note="bicomi")
    return lb.build(res)


def prove_truantru(sys: System) -> Proof:
    """truantru: ( ( ⊤ ∧ ⊤ ) ↔ ⊤ ).

    A conjunction of truth with itself is equivalent to truth.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "truantru")
    res = lb.ref("res", "( ( ⊤ ∧ ⊤ ) ↔ ⊤ )", ref="anidm", note="anidm")
    return lb.build(res)


def prove_truanfal(sys: System) -> Proof:
    """truanfal: ( ( ⊤ ∧ ⊥ ) ↔ ⊥ ).

    A conjunction of truth and falsehood is equivalent to falsehood.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "truanfal")
    res = lb.ref("res", "( ( ⊤ ∧ ⊥ ) ↔ ⊥ )", ref="truan", note="truan")
    return lb.build(res)


def prove_trunanfal(sys: System) -> Proof:
    """trunanfal: ( ( ⊤ ⊼ ⊥ ) ↔ ⊤ ).

    The nand of truth and falsehood is equivalent to truth.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "trunanfal")

    # df-nan: ( ( ⊤ ⊼ ⊥ ) ↔ ¬ ( ⊤ ∧ ⊥ ) )
    s_dfnan = lb.ref(
        "s_dfnan",
        "( ( ⊤ ⊼ ⊥ ) ↔ ¬ ( ⊤ ∧ ⊥ ) )",
        ref="df-nan",
        note="df-nan",
    )

    # truanfal: ( ( ⊤ ∧ ⊥ ) ↔ ⊥ )
    s_truanfal = lb.ref(
        "s_truanfal",
        "( ( ⊤ ∧ ⊥ ) ↔ ⊥ )",
        ref="truanfal",
        note="truanfal",
    )

    # xchbinx: ( ( ⊤ ⊼ ⊥ ) ↔ ¬ ⊥ )
    s_xchbinx = lb.ref(
        "s_xchbinx",
        "( ( ⊤ ⊼ ⊥ ) ↔ ¬ ⊥ )",
        s_dfnan,
        s_truanfal,
        ref="xchbinx",
        note="xchbinx",
    )

    # notfal: ( ¬ ⊥ ↔ ⊤ )
    s_notfal = lb.ref(
        "s_notfal",
        "( ¬ ⊥ ↔ ⊤ )",
        ref="notfal",
        note="notfal",
    )

    # bitri: ( ( ⊤ ⊼ ⊥ ) ↔ ⊤ )
    res = lb.ref(
        "res",
        "( ( ⊤ ⊼ ⊥ ) ↔ ⊤ )",
        s_xchbinx,
        s_notfal,
        ref="bitri",
        note="bitri",
    )

    return lb.build(res)


def prove_falanfal(sys: System) -> Proof:
    """falanfal: ( ( ⊥ ∧ ⊥ ) ↔ ⊥ ).

    A conjunction of falsehood with itself is equivalent to falsehood.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "falanfal")
    res = lb.ref("res", "( ( ⊥ ∧ ⊥ ) ↔ ⊥ )", ref="anidm", note="anidm")
    return lb.build(res)


def prove_bitru(sys: System) -> Proof:
    """bitru: ( ph <-> T. ).

    A wff is equivalent to truth if it is provable.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "bitru")
    h1 = lb.hyp("bitru.1", "ph")
    tru_step = lb.ref("tru_step", "T.", ref="tru", note="tru")
    res = lb.ref("res", "( ph <-> T. )", h1, tru_step, ref="2th", note="2th")
    return lb.build(res)


def prove_falbifal(sys: System) -> Proof:
    """falbifal: ( ( F. ↔ F. ) ↔ T. ).

    The biconditional of falsehood with itself is equivalent to truth.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "falbifal")
    s_biid = lb.ref("s_biid", "( F. ↔ F. )", ref="biid", note="biid")
    res = lb.ref("res", "( ( F. ↔ F. ) ↔ T. )", s_biid, ref="bitru", note="bitru")
    return lb.build(res)


def prove_falbitru(sys: System) -> Proof:
    """falbitru: ( ( F. ↔ T. ) ↔ F. ).

    The biconditional of false and true is equivalent to false.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "falbitru")
    s1 = lb.ref("s1", "( F. ↔ ( F. ↔ T. ) )", ref="tbtru", note="tbtru")
    res = lb.ref("res", "( ( F. ↔ T. ) ↔ F. )", s1, ref="bicomi", note="bicomi")
    return lb.build(res)


def prove_falimfal(sys: System) -> Proof:
    """falimfal: ( ( F. → F. ) ↔ T. ).

    The implication from falsehood to itself is equivalent to truth.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "falimfal")
    s_id = lb.ref("s_id", "( F. → F. )", ref="id", note="id")
    res = lb.ref("res", "( ( F. → F. ) ↔ T. )", s_id, ref="bitru", note="bitru")
    return lb.build(res)


def prove_trubitru(sys: System) -> Proof:
    """trubitru: ( ( T. ↔ T. ) ↔ T. ).

    The biconditional of truth with itself is equivalent to truth.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "trubitru")
    s_biid = lb.ref("s_biid", "( T. ↔ T. )", ref="biid", note="biid")
    res = lb.ref("res", "( ( T. ↔ T. ) ↔ T. )", s_biid, ref="bitru", note="bitru")
    return lb.build(res)


def prove_tbtru(sys: System) -> Proof:
    """tbtru: ( ph <-> ( ph <-> T. ) ).

    A wff is equivalent to its equivalence with truth.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "tbtru")
    tru_step = lb.ref("tru_step", "T.", ref="tru", note="tru")
    res = lb.ref("res", "( ph <-> ( ph <-> T. ) )", tru_step, ref="tbt", note="tbt")
    return lb.build(res)


def prove_nottru(sys: System) -> Proof:
    """nottru: ( -. T. <-> F. ).

    The negation of truth is equivalent to falsehood.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "nottru")
    # df-fal: ( F. <-> -. T. )
    df_fal = lb.ref("df_fal", "( F. <-> -. T. )", ref="df-fal", note="df-fal")
    # bicomi: from ( F. <-> -. T. ), deduce ( -. T. <-> F. )
    res = lb.ref("res", "( -. T. <-> F. )", df_fal, ref="bicomi", note="bicomi")
    return lb.build(res)


def prove_mptru(sys: System) -> Proof:
    """mptru: φ.  Hyp: T. → φ.

    Deduce a proposition from the fact that it follows from truth.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "mptru")
    h = lb.hyp("mptru.1", "T. → φ")
    tru = lb.ref("tru", "T.", ref="tru", note="tru")
    res = lb.mp("res", tru, h, "MP tru, mptru.1")
    return lb.build(res)


def prove_fal(sys: System) -> Proof:
    """fal: -. F.

    The truth value FALSE is not provable.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "fal")
    s_tru = lb.ref("s_tru", "T.", ref="tru", note="tru")
    s_notnoti = lb.ref("s_notnoti", "-. -. T.", s_tru, ref="notnoti", note="notnoti")
    s_df_fal = lb.ref("s_df_fal", "( F. <-> -. T. )", ref="df-fal", note="df-fal")
    res = lb.ref("res", "-. F.", s_notnoti, s_df_fal, ref="mtbir", note="mtbir")
    return lb.build(res)


def prove_falim(sys: System) -> Proof:
    """falim: ( F. → φ ).

    A contradiction implies anything.  Inference associated with fal.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "falim")
    s_fal = lb.ref("s_fal", "-. F.", ref="fal", note="fal")
    res = lb.ref("res", "( F. → φ )", s_fal, ref="pm2.21i", note="pm2.21i")
    return lb.build(res)


def prove_falimd(sys: System) -> Proof:
    """falimd: ( ( φ ∧ F. ) → ψ ).

    Deduction form of ~ falim .  A contradiction implies anything.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "falimd")
    s1 = lb.ref("s1", "( F. → ψ )", ref="falim", note="falim")
    res = lb.ref("res", "( φ ∧ F. ) → ψ", s1, ref="adantl", note="adantl")
    return lb.build(res)


def prove_tbw_ax4(sys: System) -> Proof:
    """tbw-ax4: ( F. → φ ).

    Tarski-Bernays-Wajsberg axiom 4.
    (Contributed by Anthony Hart, 16-Aug-2011.)
    """
    lb = ProofBuilder(sys, "tbw-ax4")
    res = lb.ref("res", "( F. → φ )", ref="falim", note="falim")
    return lb.build(res)


def prove_re1tbw4(sys: System) -> Proof:
    """re1tbw4: ⊥ → φ.

    ~tbw-ax4 rederived from ~merco2.
    (Contributed by Anthony Hart, 16-Aug-2011.)
    """
    lb = ProofBuilder(sys, "re1tbw4")
    res = lb.ref("res", "( ⊥ → φ )", ref="falim", note="falim")
    return lb.build(res)


def prove_tbwlem2(sys: System) -> Proof:
    """tbwlem2: ( φ → ( ψ → F. ) ) → ( ( ( φ → χ ) → θ ) → ( ψ → θ ) ).

    Tarski-Bernays-Wajsberg lemma 2.
    (Contributed by Anthony Hart, 16-Aug-2011.)
    """
    lb = ProofBuilder(sys, "tbwlem2")

    # tbw-ax1 with φ=φ, ψ=(ψ → F.), χ=χ
    s1 = lb.ref(
        "s1",
        "( φ → ( ψ → F. ) ) → ( ( ( ψ → F. ) → χ ) → ( φ → χ ) )",
        ref="tbw-ax1",
        note="tbw-ax1",
    )

    # tbw-ax4 with φ=χ
    s2 = lb.ref("s2", "F. → χ", ref="tbw-ax4", note="tbw-ax4")

    # tbw-ax1 with φ=ψ, ψ=F., χ=χ
    s3 = lb.ref(
        "s3",
        "( ψ → F. ) → ( ( F. → χ ) → ( ψ → χ ) )",
        ref="tbw-ax1",
        note="tbw-ax1",
    )

    # tbwlem1 with φ=(ψ → F.), ψ=(F. → χ), χ=(ψ → χ)
    s4 = lb.ref(
        "s4",
        "( ( ψ → F. ) → ( ( F. → χ ) → ( ψ → χ ) ) ) → ( ( F. → χ ) → ( ( ψ → F. ) → ( ψ → χ ) ) )",
        ref="tbwlem1",
        note="tbwlem1",
    )

    # ax-mp with s3, s4
    s5 = lb.mp("s5", s3, s4, "MP s3, s4")

    # ax-mp with s2, s5
    s6 = lb.mp("s6", s2, s5, "MP s2, s5")

    # tbwlem1 with φ=(ψ → F.), ψ=ψ, χ=χ
    s7 = lb.ref(
        "s7",
        "( ( ψ → F. ) → ( ψ → χ ) ) → ( ψ → ( ( ψ → F. ) → χ ) )",
        ref="tbwlem1",
        note="tbwlem1",
    )

    # ax-mp with s6, s7
    s8 = lb.mp("s8", s6, s7, "MP s6, s7")

    # tbw-ax1 with φ=ψ, ψ=((ψ → F.) → χ), χ=(φ → χ)
    s9 = lb.ref(
        "s9",
        "( ψ → ( ( ψ → F. ) → χ ) ) → ( ( ( ( ψ → F. ) → χ ) → ( φ → χ ) ) → ( ψ → ( φ → χ ) ) )",
        ref="tbw-ax1",
        note="tbw-ax1",
    )

    # ax-mp with s8, s9
    s10 = lb.mp("s10", s8, s9, "MP s8, s9")

    # tbwsyl with s1, s10
    s11 = lb.ref(
        "s11",
        "( φ → ( ψ → F. ) ) → ( ψ → ( φ → χ ) )",
        s1,
        s10,
        ref="tbwsyl",
        note="tbwsyl",
    )

    # tbw-ax1 with φ=ψ, ψ=(φ → χ), χ=θ
    s12 = lb.ref(
        "s12",
        "( ψ → ( φ → χ ) ) → ( ( ( φ → χ ) → θ ) → ( ψ → θ ) )",
        ref="tbw-ax1",
        note="tbw-ax1",
    )

    # tbwsyl with s11, s12
    res = lb.ref(
        "res",
        "( φ → ( ψ → F. ) ) → ( ( ( φ → χ ) → θ ) → ( ψ → θ ) )",
        s11,
        s12,
        ref="tbwsyl",
        note="tbwsyl",
    )

    return lb.build(res)


def prove_tbw_bijust(sys: System) -> Proof:
    """tbw-bijust: ( φ ↔ ψ ) ↔ ( ( ( φ → ψ ) → ( ( ψ → φ ) → F. ) ) → F. ).

    Justification for tbw-negdf.  Relates the biconditional to implication
    and falsehood.  (Contributed by Anthony Hart, 15-Aug-2011.)
    (Proof modification is discouraged.)  (New usage is discouraged.)
    """
    lb = ProofBuilder(sys, "tbw-bijust")

    s1 = lb.ref(
        "s1",
        "( φ ↔ ψ ) ↔ ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) )",
        ref="dfbi1",
        note="dfbi1",
    )

    s2 = lb.ref(
        "s2",
        "¬ ( ψ → φ ) → ( ( ψ → φ ) → F. )",
        ref="pm2.21",
        note="pm2.21",
    )

    s3 = lb.ref(
        "s3",
        "( ( φ → ψ ) → ¬ ( ψ → φ ) ) → ( ( φ → ψ ) → ( ( ψ → φ ) → F. ) )",
        s2,
        ref="imim2i",
        note="imim2i",
    )

    s4 = lb.ref(
        "s4",
        "¬ ( ψ → φ ) → ¬ ( ψ → φ )",
        ref="id",
        note="id",
    )

    s5 = lb.ref(
        "s5",
        "F. → ¬ ( ψ → φ )",
        ref="falim",
        note="falim",
    )

    s6 = lb.ref(
        "s6",
        "( ( ψ → φ ) → F. ) → ¬ ( ψ → φ )",
        s4,
        s5,
        ref="ja",
        note="ja",
    )

    s7 = lb.ref(
        "s7",
        "( ( φ → ψ ) → ( ( ψ → φ ) → F. ) ) → ( ( φ → ψ ) → ¬ ( ψ → φ ) )",
        s6,
        ref="imim2i",
        note="imim2i",
    )

    s8 = lb.ref(
        "s8",
        "( ( φ → ψ ) → ¬ ( ψ → φ ) ) ↔ ( ( φ → ψ ) → ( ( ψ → φ ) → F. ) )",
        s3,
        s7,
        ref="impbii",
        note="impbii",
    )

    s9 = lb.ref(
        "s9",
        "¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) ↔ ¬ ( ( φ → ψ ) → ( ( ψ → φ ) → F. ) )",
        s8,
        ref="notbii",
        note="notbii",
    )

    s10 = lb.ref(
        "s10",
        "¬ ( ( φ → ψ ) → ( ( ψ → φ ) → F. ) ) → ( ( ( φ → ψ ) → ( ( ψ → φ ) → F. ) ) → F. )",
        ref="pm2.21",
        note="pm2.21",
    )

    s11 = lb.ref(
        "s11",
        "¬ ( ( φ → ψ ) → ( ( ψ → φ ) → F. ) ) → ( ( ( ( φ → ψ ) → ( ( ψ → φ ) → F. ) ) → F. ) → ¬ ( ( φ → ψ ) → ( ( ψ → φ ) → F. ) ) )",
        ref="ax-1",
        note="ax-1",
    )

    s12 = lb.ref(
        "s12",
        "F. → ( ( ( ( φ → ψ ) → ( ( ψ → φ ) → F. ) ) → F. ) → ¬ ( ( φ → ψ ) → ( ( ψ → φ ) → F. ) ) )",
        ref="falim",
        note="falim",
    )

    s13 = lb.ref(
        "s13",
        "( ( ( φ → ψ ) → ( ( ψ → φ ) → F. ) ) → F. ) → ( ( ( ( φ → ψ ) → ( ( ψ → φ ) → F. ) ) → F. ) → ¬ ( ( φ → ψ ) → ( ( ψ → φ ) → F. ) ) )",
        s11,
        s12,
        ref="ja",
        note="ja",
    )

    s14 = lb.ref(
        "s14",
        "( ( ( φ → ψ ) → ( ( ψ → φ ) → F. ) ) → F. ) → ¬ ( ( φ → ψ ) → ( ( ψ → φ ) → F. ) )",
        s13,
        ref="pm2.43i",
        note="pm2.43i",
    )

    s15 = lb.ref(
        "s15",
        "¬ ( ( φ → ψ ) → ( ( ψ → φ ) → F. ) ) ↔ ( ( ( φ → ψ ) → ( ( ψ → φ ) → F. ) ) → F. )",
        s10,
        s14,
        ref="impbii",
        note="impbii",
    )

    res = lb.ref(
        "res",
        "( φ ↔ ψ ) ↔ ( ( ( φ → ψ ) → ( ( ψ → φ ) → F. ) ) → F. )",
        s1,
        s9,
        s15,
        ref="3bitri",
        note="3bitri",
    )

    return lb.build(res)


def prove_tbw_negdf(sys: System) -> Proof:
    """tbw-negdf: ( ( ( ¬ φ → ( φ → F. ) ) → ( ( ( φ → F. ) → ¬ φ ) → F. ) ) → F. ).

    Tarski-Bernays-Wajsberg definition of negation in terms of
    implication and falsehood.  (Contributed by Anthony Hart,
    15-Aug-2011.)  (Proof modification is discouraged.)
    (New usage is discouraged.)
    """
    lb = ProofBuilder(sys, "tbw-negdf")

    # Forward direction: ( ¬ φ → ( φ → F. ) )
    s_fwd = lb.ref("s_fwd", "¬ φ → ( φ → F. )", ref="pm2.21", note="pm2.21")

    # Reverse direction: ( ( φ → F. ) → ¬ φ )
    # ja with ja.1: ¬ φ → ¬ φ, ja.2: F. → ¬ φ
    s_id = lb.ref("s_id", "¬ φ → ¬ φ", ref="id", note="id")
    s_falim = lb.ref("s_falim", "F. → ¬ φ", ref="falim", note="falim")
    s_rev = lb.ref("s_rev", "( φ → F. ) → ¬ φ", s_id, s_falim, ref="ja", note="ja")

    # Combine forward and reverse with impbii: ( ¬ φ ↔ ( φ → F. ) )
    s_equiv = lb.ref(
        "s_equiv",
        "( ¬ φ ↔ ( φ → F. ) )",
        s_fwd,
        s_rev,
        ref="impbii",
        note="impbii",
    )

    # tbw-bijust with substitution {φ:=¬ φ, ψ:=(φ → F.)}
    s_tbw = lb.ref(
        "s_tbw",
        "( ( ¬ φ ↔ ( φ → F. ) ) ↔ ( ( ( ¬ φ → ( φ → F. ) ) → ( ( ( φ → F. ) → ¬ φ ) → F. ) ) → F. ) )",
        ref="tbw-bijust",
        note="tbw-bijust",
    )

    # mpbi: result
    res = lb.ref(
        "res",
        "( ( ( ¬ φ → ( φ → F. ) ) → ( ( ( φ → F. ) → ¬ φ ) → F. ) ) → F. )",
        s_equiv,
        s_tbw,
        ref="mpbi",
        note="mpbi",
    )

    return lb.build(res)


def prove_dfnot(sys: System) -> Proof:
    """dfnot: ( -. ph <-> ( ph -> F. ) ).

    Negation in terms of implication and falsehood.
    (Contributed by NM, 27-Mar-1995.)
    """
    lb = ProofBuilder(sys, "dfnot")
    mtt_step = lb.ref("mtt_step", "( -. F. -> ( -. ph <-> ( ph -> F. ) ) )", ref="mtt", note="mtt")
    fal_step = lb.ref("fal_step", "-. F.", ref="fal", note="fal")
    res = lb.mp("res", fal_step, mtt_step, "ax-mp")
    return lb.build(res)


def prove_notfal(sys: System) -> Proof:
    """notfal: ( -. F. <-> T. ).

    The negation of falsehood is equivalent to truth.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "notfal")
    s_fal = lb.ref("s_fal", "-. F.", ref="fal", note="fal")
    res = lb.ref("res", "( -. F. <-> T. )", s_fal, ref="bitru", note="bitru")
    return lb.build(res)


def prove_trud(sys: System) -> Proof:
    """trud: ( ph -> T. ).

    Deduction form of ~ tru .  The true constant is provable under any
    antecedent.  (Contributed by FL, 5-Mar-1993.)
    """
    lb = ProofBuilder(sys, "trud")
    s_tru = lb.ref("s_tru", "T.", ref="tru", note="tru")
    res = lb.ref("res", "( ph -> T. )", s_tru, ref="a1i", note="a1i")
    return lb.build(res)


def prove_falimtru(sys: System) -> Proof:
    """falimtru: ( ( F. → T. ) ↔ T. ).

    The implication from falsehood to truth is equivalent to truth.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "falimtru")
    s1 = lb.ref("s1", "( F. → T. )", ref="trud", note="trud")
    res = lb.ref("res", "( ( F. → T. ) ↔ T. )", s1, ref="bitru", note="bitru")
    return lb.build(res)


def prove_trut(sys: System) -> Proof:
    """trut: ( ph <-> ( T. -> ph ) ).

    A wff is equivalent to its implication with truth.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "trut")
    s_tru = lb.ref("s_tru", "T.", ref="tru", note="tru")
    res = lb.ref("res", "( ph <-> ( T. -> ph ) )", s_tru, ref="a1bi", note="a1bi")
    return lb.build(res)


def prove_truimfal(sys: System) -> Proof:
    """truimfal: ( ( T. → F. ) ↔ F. ).

    The implication from truth to falsehood is equivalent to falsehood.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "truimfal")
    s1 = lb.ref("s1", "( F. ↔ ( T. → F. ) )", ref="trut", note="trut")
    res = lb.ref("res", "( ( T. → F. ) ↔ F. )", s1, ref="bicomi", note="bicomi")
    return lb.build(res)


def prove_truimtru(sys: System) -> Proof:
    """truimtru: ( ( T. → T. ) ↔ T. ).

    The implication from truth to truth is equivalent to truth.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "truimtru")
    s1 = lb.ref("s1", "( T. → T. )", ref="trud", note="trud")
    res = lb.ref("res", "( ( T. → T. ) ↔ T. )", s1, ref="bitru", note="bitru")
    return lb.build(res)


def prove_truorfal(sys: System) -> Proof:
    """truorfal: ( ( ⊤ ∨ ⊥ ) ↔ ⊤ ).

    Disjunction of truth and falsehood is equivalent to truth.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "truorfal")
    s_tru = lb.ref("s_tru", "⊤", ref="tru", note="tru")
    s_or = lb.ref("s_or", "( ⊤ ∨ ⊥ )", s_tru, ref="orci", note="orci")
    res = lb.ref("res", "( ( ⊤ ∨ ⊥ ) ↔ ⊤ )", s_or, ref="bitru", note="bitru")
    return lb.build(res)


def prove_truortru(sys: System) -> Proof:
    """truortru: ( ( ⊤ ∨ ⊤ ) ↔ ⊤ ).

    Disjunction of truth with truth is equivalent to truth.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "truortru")
    res = lb.ref("res", "( ⊤ ∨ ⊤ ) ↔ ⊤", ref="oridm", note="oridm")
    return lb.build(res)


def prove_trunortru(sys: System) -> Proof:
    """trunortru: ( ( ⊤ ⊽ ⊤ ) ↔ ⊥ ).

    The nor of truth with truth is equivalent to falsehood.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "trunortru")

    # df-nor: ( ⊤ ⊽ ⊤ ) ↔ ¬ ( ⊤ ∨ ⊤ )
    s_dfnor = lb.ref(
        "s_dfnor",
        "( ( ⊤ ⊽ ⊤ ) ↔ ¬ ( ⊤ ∨ ⊤ ) )",
        ref="df-nor",
        note="df-nor",
    )

    # truortru: ( ⊤ ∨ ⊤ ) ↔ ⊤
    s_truortru = lb.ref(
        "s_truortru",
        "( ( ⊤ ∨ ⊤ ) ↔ ⊤ )",
        ref="truortru",
        note="truortru",
    )

    # xchbinx: ( ⊤ ⊽ ⊤ ) ↔ ¬ ⊤
    s_xchbinx = lb.ref(
        "s_xchbinx",
        "( ( ⊤ ⊽ ⊤ ) ↔ ¬ ⊤ )",
        s_dfnor,
        s_truortru,
        ref="xchbinx",
        note="xchbinx",
    )

    # df-fal: ⊥ ↔ ¬ ⊤
    s_dffal = lb.ref(
        "s_dffal",
        "( ⊥ ↔ ¬ ⊤ )",
        ref="df-fal",
        note="df-fal",
    )

    # bitr4i: ( ( ⊤ ⊽ ⊤ ) ↔ ⊥ )
    res = lb.ref(
        "res",
        "( ( ⊤ ⊽ ⊤ ) ↔ ⊥ )",
        s_xchbinx,
        s_dffal,
        ref="bitr4i",
        note="bitr4i",
    )

    return lb.build(res)


def prove_dftru2(sys: System) -> Proof:
    """dftru2: ( T. ↔ ( φ → φ ) ).

    An alternate definition of truth.  (Contributed by NM, 5-Aug-1993.)
    (Proof modification is discouraged.)
    """
    lb = ProofBuilder(sys, "dftru2")
    s_tru = lb.ref("s_tru", "T.", ref="tru", note="tru")
    s_id = lb.ref("s_id", "( φ → φ )", ref="id", note="id")
    res = lb.ref("res", "( T. ↔ ( φ → φ ) )", s_tru, s_id, ref="2th", note="2th")
    return lb.build(res)


LemmaCtor = Callable[[System], Proof]


def prove_trubifal(sys: System) -> Proof:
    """trubifal: ( ( ⊤ ↔ ⊥ ) ↔ ⊥ ).

    A biconditional of truth and falsehood is equivalent to falsehood.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "trubifal")
    s1 = lb.ref("s1", "( ( ⊤ ↔ ⊥ ) ↔ ( ⊥ ↔ ⊤ ) )", ref="bicom", note="bicom")
    s2 = lb.ref("s2", "( ( ⊥ ↔ ⊤ ) ↔ ⊥ )", ref="falbitru", note="falbitru")
    res = lb.ref("res", "( ( ⊤ ↔ ⊥ ) ↔ ⊥ )", s1, s2, ref="bitri", note="bitri")
    return lb.build(res)


THEOREMS: Mapping[str, LemmaCtor] = {
    "tru": prove_tru,
    "trut": prove_trut,
    "trud": prove_trud,
    "fal": prove_fal,
    "nottru": prove_nottru,
    "mptru": prove_mptru,
    "trubifal": prove_trubifal,
}

__all__ = [
    "LemmaCtor",
    "THEOREMS",
    "prove_dftru2",
    "prove_trud",
    "prove_trut",
    "prove_falimd",
    "prove_trubifal",
]


def prove_merco1(sys: System) -> Proof:
    """merco1: (((((φ → ψ) → (χ → F.)) → θ) → τ) → ((τ → φ) → (χ → φ))).

    Used to rederive the Tarski-Bernays-Wajsberg axioms from merco1.
    (Contributed by Anthony Hart, 17-Sep-2011.)
    """
    lb = ProofBuilder(sys, "merco1")

    # ax-1 with ¬χ and ¬θ: ¬χ → (¬θ → ¬χ)
    s44 = lb.ref("s44", "( ¬ χ → ( ¬ θ → ¬ χ ) )", ref="ax-1", note="ax-1")

    # falim: F. → (¬θ → ¬χ)
    s46 = lb.ref("s46", "( F. → ( ¬ θ → ¬ χ ) )", ref="falim", note="falim")

    # ja from s44 and s46: (χ → F.) → (¬θ → ¬χ)
    s47 = lb.ref("s47", "( ( χ → F. ) → ( ¬ θ → ¬ χ ) )", s44, s46, ref="ja", note="ja")

    # imim2i from s47: ((φ → ψ) → (χ → F.)) → ((φ → ψ) → (¬θ → ¬χ))
    s48 = lb.ref(
        "s48",
        "( ( ( φ → ψ ) → ( χ → F. ) ) → ( ( φ → ψ ) → ( ¬ θ → ¬ χ ) ) )",
        s47,
        ref="imim2i",
        note="imim2i",
    )

    # imim1i from s48: (((φ → ψ) → (¬θ → ¬χ)) → θ) → (((φ → ψ) → (χ → F.)) → θ)
    s49 = lb.ref(
        "s49",
        "( ( ( ( φ → ψ ) → ( ¬ θ → ¬ χ ) ) → θ ) → ( ( ( φ → ψ ) → ( χ → F. ) ) → θ ) )",
        s48,
        ref="imim1i",
        note="imim1i",
    )

    # imim1i from s49: ((((φ → ψ) → (χ → F.)) → θ) → τ) → ((((φ → ψ) → (¬θ → ¬χ)) → θ) → τ)
    s50 = lb.ref(
        "s50",
        "( ( ( ( ( φ → ψ ) → ( χ → F. ) ) → θ ) → τ ) → ( ( ( ( φ → ψ ) → ( ¬ θ → ¬ χ ) ) → θ ) → τ ) )",
        s49,
        ref="imim1i",
        note="imim1i",
    )

    # meredith with φ, ψ, θ, χ, τ:
    # ((((φ → ψ) → (¬θ → ¬χ)) → θ) → τ) → ((τ → φ) → (χ → φ))
    s56 = lb.ref(
        "s56",
        "( ( ( ( ( φ → ψ ) → ( ¬ θ → ¬ χ ) ) → θ ) → τ ) → ( ( τ → φ ) → ( χ → φ ) ) )",
        ref="meredith",
        note="meredith",
    )

    # syl from s50 and s56:
    # ((((φ → ψ) → (χ → F.)) → θ) → τ) → ((τ → φ) → (χ → φ))
    res = lb.ref(
        "res",
        "( ( ( ( ( φ → ψ ) → ( χ → F. ) ) → θ ) → τ ) → ( ( τ → φ ) → ( χ → φ ) ) )",
        s50,
        s56,
        ref="syl",
        note="syl",
    )

    return lb.build(res)


def prove_merco2(sys: System) -> Proof:
    """merco2: (((φ → ψ) → ((F. → χ) → θ)) → ((θ → φ) → (τ → (η → φ)))).

    Used to rederive the Tarski-Bernays-Wajsberg axioms from merco1.
    (Contributed by Anthony Hart, 17-Sep-2011.)
    """
    lb = ProofBuilder(sys, "merco2")

    # Step 1: falim with φ:=χ.  (F. → χ)
    s1 = lb.ref("s1", "( F. → χ )", ref="falim", note="falim")

    # Step 2: pm2.04 with φ:=(φ→ψ), ψ:=(F.→χ), χ:=θ.
    # (((φ→ψ) → ((F.→χ) → θ)) → ((F.→χ) → ((φ→ψ) → θ)))
    s2 = lb.ref(
        "s2",
        "( ( ( φ → ψ ) → ( ( F. → χ ) → θ ) ) → ( ( F. → χ ) → ( ( φ → ψ ) → θ ) ) )",
        ref="pm2.04",
        note="pm2.04",
    )

    # Step 3: mpi from s1, s2.
    # (((φ→ψ) → ((F.→χ) → θ)) → ((φ→ψ) → θ))
    s3 = lb.ref(
        "s3",
        "( ( ( φ → ψ ) → ( ( F. → χ ) → θ ) ) → ( ( φ → ψ ) → θ ) )",
        s1,
        s2,
        ref="mpi",
        note="mpi",
    )

    # Step 4: jarl with φ:=φ, ψ:=ψ, χ:=θ.
    # (((φ→ψ) → θ) → (¬φ → θ))
    s4 = lb.ref(
        "s4",
        "( ( ( φ → ψ ) → θ ) → ( -. φ → θ ) )",
        ref="jarl",
        note="jarl",
    )

    # Step 5: idd with φ:=((φ→ψ)→θ), ψ:=θ.
    # (((φ→ψ) → θ) → (θ → θ))
    s5 = lb.ref(
        "s5",
        "( ( ( φ → ψ ) → θ ) → ( θ → θ ) )",
        ref="idd",
        note="idd",
    )

    # Step 6: jad from s4, s5.
    # (((φ→ψ) → θ) → ((φ → θ) → θ))
    s6 = lb.ref(
        "s6",
        "( ( ( φ → ψ ) → θ ) → ( ( φ → θ ) → θ ) )",
        s4,
        s5,
        ref="jad",
        note="jad",
    )

    # Step 7: looinv with φ:=φ, ψ:=θ.
    # (((φ → θ) → θ) → ((θ → φ) → φ))
    s7 = lb.ref(
        "s7",
        "( ( ( φ → θ ) → θ ) → ( ( θ → φ ) → φ ) )",
        ref="looinv",
        note="looinv",
    )

    # Step 8: 3syl from s3, s6, s7.
    # (((φ→ψ) → ((F.→χ) → θ)) → ((θ → φ) → φ))
    s8 = lb.ref(
        "s8",
        "( ( ( φ → ψ ) → ( ( F. → χ ) → θ ) ) → ( ( θ → φ ) → φ ) )",
        s3,
        s6,
        s7,
        ref="3syl",
        note="3syl",
    )

    # Step 9: a1dd from s8 — add τ as an extra antecedent before φ.
    # (((φ→ψ) → ((F.→χ) → θ)) → ((θ → φ) → (τ → φ)))
    s9 = lb.ref(
        "s9",
        "( ( ( φ → ψ ) → ( ( F. → χ ) → θ ) ) → ( ( θ → φ ) → ( τ → φ ) ) )",
        s8,
        ref="a1dd",
        note="a1dd",
    )

    # Step 10: a1i from s9 — add η as outermost antecedent.
    # (η → (((φ→ψ) → ((F.→χ) → θ)) → ((θ → φ) → (τ → φ))))
    s10 = lb.ref(
        "s10",
        "( η → ( ( ( φ → ψ ) → ( ( F. → χ ) → θ ) ) → ( ( θ → φ ) → ( τ → φ ) ) ) )",
        s9,
        ref="a1i",
        note="a1i",
    )

    # Step 11: com4l from s10 — rotate η inward.
    # (((φ→ψ) → ((F.→χ) → θ)) → ((θ → φ) → (τ → (η → φ))))
    res = lb.ref(
        "res",
        "( ( ( φ → ψ ) → ( ( F. → χ ) → θ ) ) → ( ( θ → φ ) → ( τ → ( η → φ ) ) ) )",
        s10,
        ref="com4l",
        note="com4l",
    )

    return lb.build(res)


def prove_merco1lem1(sys: System) -> Proof:
    """merco1lem1: ( φ → ( F. → χ ) ).

    Used to rederive the Tarski-Bernays-Wajsberg axioms from merco1.
    (Contributed by Anthony Hart, 17-Sep-2011.)
    """
    lb = ProofBuilder(sys, "merco1lem1")
    s1 = lb.ref("s1", "( F. → χ )", ref="falim", note="falim")
    res = lb.ref("res", "( φ → ( F. → χ ) )", s1, ref="a1i", note="a1i")
    return lb.build(res)


def prove_retbwax4(sys: System) -> Proof:
    """retbwax4: ( ⊥ → φ ).

    tbw-ax4 rederived from merco1.
    (Contributed by Anthony Hart, 17-Sep-2011.)
    """
    lb = ProofBuilder(sys, "retbwax4")
    s1 = lb.ref("s1", "( φ → ( ⊥ → φ ) )", ref="merco1lem1", note="merco1lem1")
    s2 = lb.ref("s2", "( ( φ → ( ⊥ → φ ) ) → ( ⊥ → φ ) )", ref="merco1lem1", note="merco1lem1")
    res = lb.mp("res", s1, s2, "ax-mp 1,2")
    return lb.build(res)


def prove_merco1lem2(sys: System) -> Proof:
    """merco1lem2: (((φ → ψ) → χ) → (((ψ → τ) → (φ → ⊥)) → χ)).

    Used to rederive the Tarski-Bernays-Wajsberg axioms from merco1.
    (Contributed by Anthony Hart, 17-Sep-2011.)
    """
    lb = ProofBuilder(sys, "merco1lem2")

    # retbwax2 with φ := (((ψ → τ) → (φ → ⊥)) → ⊥) and ψ := (χ → ψ)
    s1 = lb.ref(
        "s1",
        "( ( ( ( ψ → τ ) → ( φ → ⊥ ) ) → ⊥ ) → ( ( χ → ψ ) → ( ( ( ψ → τ ) → ( φ → ⊥ ) ) → ⊥ ) ) )",
        ref="retbwax2",
        note="retbwax2",
    )

    # merco1 with A := ψ, B := τ, C := φ, D := ⊥, E := ((χ → ψ) → (((ψ → τ) → (φ → ⊥)) → ⊥))
    s2 = lb.ref(
        "s2",
        "( ( ( ( ( ψ → τ ) → ( φ → ⊥ ) ) → ⊥ ) → ( ( χ → ψ ) → ( ( ( ψ → τ ) → ( φ → ⊥ ) ) → ⊥ ) ) ) → ( ( ( ( χ → ψ ) → ( ( ( ψ → τ ) → ( φ → ⊥ ) ) → ⊥ ) ) → ψ ) → ( φ → ψ ) ) )",
        ref="merco1",
        note="merco1",
    )

    # ax-mp: s3 = (((χ → ψ) → (((ψ → τ) → (φ → ⊥)) → ⊥)) → ψ) → (φ → ψ)
    s3 = lb.mp("s3", s1, s2, "ax-mp 1,2")

    # merco1 with A := χ, B := ψ, C := ((ψ → τ) → (φ → ⊥)), D := ψ, E := (φ → ψ)
    s4 = lb.ref(
        "s4",
        "( ( ( ( ( χ → ψ ) → ( ( ( ψ → τ ) → ( φ → ⊥ ) ) → ⊥ ) ) → ψ ) → ( φ → ψ ) ) → ( ( ( φ → ψ ) → χ ) → ( ( ( ψ → τ ) → ( φ → ⊥ ) ) → χ ) ) )",
        ref="merco1",
        note="merco1",
    )

    # ax-mp: target
    res = lb.mp("res", s3, s4, "ax-mp 3,4")
    return lb.build(res)


def prove_merco1lem3(sys: System) -> Proof:
    """merco1lem3: (((φ → ψ) → (χ → ⊥)) → (χ → φ)).

    Used to rederive the Tarski-Bernays-Wajsberg axioms from merco1.
    (Contributed by Anthony Hart, 17-Sep-2011.)
    """
    lb = ProofBuilder(sys, "merco1lem3")

    # --- Part 1: derive (φ → (((φ → φ) → (φ → ⊥)) → (φ → φ))) ---

    # Step 35 (merco1lem2 with φ:=φ, ψ:=φ, χ:=⊥, τ:=φ)
    s35 = lb.ref(
        "s35",
        "( ( ( φ → φ ) → ⊥ ) → ( ( ( φ → φ ) → ( φ → ⊥ ) ) → ⊥ ) )",
        ref="merco1lem2",
        note="merco1lem2",
    )

    # Step 44 (retbwax2 with φ:=(((φ→φ)→(φ→⊥))→(φ→φ)), ψ:=φ)
    s44 = lb.ref(
        "s44",
        "( ( ( ( φ → φ ) → ( φ → ⊥ ) ) → ( φ → φ ) ) → ( φ → ( ( ( φ → φ ) → ( φ → ⊥ ) ) → ( φ → φ ) ) ) )",
        ref="retbwax2",
        note="retbwax2",
    )

    # Step 49 (merco1lem2 with φ:=((φ→φ)→(φ→⊥)), ψ:=(φ→φ), χ:=(φ→(((φ→φ)→(φ→⊥))→(φ→φ))), τ:=⊥)
    s49 = lb.ref(
        "s49",
        "( ( ( ( ( φ → φ ) → ( φ → ⊥ ) ) → ( φ → φ ) ) → ( φ → ( ( ( φ → φ ) → ( φ → ⊥ ) ) → ( φ → φ ) ) ) ) → ( ( ( ( φ → φ ) → ⊥ ) → ( ( ( φ → φ ) → ( φ → ⊥ ) ) → ⊥ ) ) → ( φ → ( ( ( φ → φ ) → ( φ → ⊥ ) ) → ( φ → φ ) ) ) ) )",
        ref="merco1lem2",
        note="merco1lem2",
    )

    # Step 50 (ax-mp from s44, s49)
    s50 = lb.mp("s50", s44, s49, "ax-mp 44,49")

    # Step 51 (ax-mp from s35, s50): φ → (((φ → φ) → (φ → ⊥)) → (φ → φ))
    s51 = lb.mp("s51", s35, s50, "ax-mp 35,50")

    # --- Part 2: derive (((φ → ψ) → (χ → ⊥)) → (χ → φ)) ---

    # Step 66 (merco1lem2 with φ:=χ, ψ:=φ, χ:=⊥, τ:=ψ)
    s66 = lb.ref(
        "s66",
        "( ( ( χ → φ ) → ⊥ ) → ( ( ( φ → ψ ) → ( χ → ⊥ ) ) → ⊥ ) )",
        ref="merco1lem2",
        note="merco1lem2",
    )

    # Step 75 (retbwax2 with φ:=(((φ→ψ)→(χ→⊥))→(χ→φ)), ψ:=(φ→(((φ→φ)→(φ→⊥))→(φ→φ))))
    s75 = lb.ref(
        "s75",
        "( ( ( ( φ → ψ ) → ( χ → ⊥ ) ) → ( χ → φ ) ) → ( ( φ → ( ( ( φ → φ ) → ( φ → ⊥ ) ) → ( φ → φ ) ) ) → ( ( ( φ → ψ ) → ( χ → ⊥ ) ) → ( χ → φ ) ) ) )",
        ref="retbwax2",
        note="retbwax2",
    )

    # Step 80 (merco1lem2 with φ:=((φ→ψ)→(χ→⊥)), ψ:=(χ→φ),
    #          χ:=((φ→(((φ→φ)→(φ→⊥))→(φ→φ)))→(((φ→ψ)→(χ→⊥))→(χ→φ))), τ:=⊥)
    s80 = lb.ref(
        "s80",
        "( ( ( ( ( φ → ψ ) → ( χ → ⊥ ) ) → ( χ → φ ) ) → ( ( φ → ( ( ( φ → φ ) → ( φ → ⊥ ) ) → ( φ → φ ) ) ) → ( ( ( φ → ψ ) → ( χ → ⊥ ) ) → ( χ → φ ) ) ) ) → ( ( ( ( χ → φ ) → ⊥ ) → ( ( ( φ → ψ ) → ( χ → ⊥ ) ) → ⊥ ) ) → ( ( φ → ( ( ( φ → φ ) → ( φ → ⊥ ) ) → ( φ → φ ) ) ) → ( ( ( φ → ψ ) → ( χ → ⊥ ) ) → ( χ → φ ) ) ) ) )",
        ref="merco1lem2",
        note="merco1lem2",
    )

    # Step 81 (ax-mp from s75, s80)
    s81 = lb.mp("s81", s75, s80, "ax-mp 75,80")

    # Step 82 (ax-mp from s66, s81)
    s82 = lb.mp("s82", s66, s81, "ax-mp 66,81")

    # Step 83 (ax-mp from s51, s82): target
    res = lb.mp("res", s51, s82, "ax-mp 51,82")
    return lb.build(res)


def prove_merco1lem5(sys: System) -> Proof:
    """merco1lem5: ((((φ → ⊥) → χ) → τ) → (φ → τ)).

    Used to rederive the Tarski-Bernays-Wajsberg axioms from merco1.
    (Contributed by Anthony Hart, 17-Sep-2011.)
    """
    lb = ProofBuilder(sys, "merco1lem5")

    s1 = lb.ref(
        "s1",
        "( ( ( ( τ → ⊥ ) → ( φ → ⊥ ) ) → χ ) → ( ( φ → ⊥ ) → χ ) )",
        ref="merco1lem4",
        note="merco1lem4",
    )

    s2 = lb.ref(
        "s2",
        "( ( ( ( ( τ → ⊥ ) → ( φ → ⊥ ) ) → χ ) → ( ( φ → ⊥ ) → χ ) ) → ( ( ( ( φ → ⊥ ) → χ ) → τ ) → ( φ → τ ) ) )",
        ref="merco1",
        note="merco1",
    )

    res = lb.mp("res", s1, s2, "ax-mp 1,2")

    return lb.build(res)


def prove_truxortru(sys: System) -> Proof:
    """truxortru: ( ( ⊤ ⊻ ⊤ ) ↔ ⊥ ).

    The exclusive-or of truth with itself is equivalent to falsehood.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "truxortru")

    # df-xor: ( ( ⊤ ⊻ ⊤ ) ↔ ¬ ( ⊤ ↔ ⊤ ) )
    s_dfxor = lb.ref(
        "s_dfxor",
        "( ( ⊤ ⊻ ⊤ ) ↔ ¬ ( ⊤ ↔ ⊤ ) )",
        ref="df-xor",
        note="df-xor",
    )

    # trubitru: ( ( ⊤ ↔ ⊤ ) ↔ ⊤ )
    s_trubitru = lb.ref(
        "s_trubitru",
        "( ( ⊤ ↔ ⊤ ) ↔ ⊤ )",
        ref="trubitru",
        note="trubitru",
    )

    # xchbinx: ( ( ⊤ ⊻ ⊤ ) ↔ ¬ ⊤ )
    s_xchbinx = lb.ref(
        "s_xchbinx",
        "( ( ⊤ ⊻ ⊤ ) ↔ ¬ ⊤ )",
        s_dfxor,
        s_trubitru,
        ref="xchbinx",
        note="xchbinx",
    )

    # nottru: ( ¬ ⊤ ↔ ⊥ )
    s_nottru = lb.ref(
        "s_nottru",
        "( ¬ ⊤ ↔ ⊥ )",
        ref="nottru",
        note="nottru",
    )

    # bitri: ( ( ⊤ ⊻ ⊤ ) ↔ ⊥ )
    res = lb.ref(
        "res",
        "( ( ⊤ ⊻ ⊤ ) ↔ ⊥ )",
        s_xchbinx,
        s_nottru,
        ref="bitri",
        note="bitri",
    )

    return lb.build(res)


def prove_truxorfal(sys: System) -> Proof:
    """truxorfal: ( ( ⊤ ⊻ ⊥ ) ↔ ⊤ ).

    The exclusive-or of truth and falsehood is equivalent to truth.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "truxorfal")

    # df-xor: ( ( ⊤ ⊻ ⊥ ) ↔ ¬ ( ⊤ ↔ ⊥ ) )
    s_dfxor = lb.ref(
        "s_dfxor",
        "( ( ⊤ ⊻ ⊥ ) ↔ ¬ ( ⊤ ↔ ⊥ ) )",
        ref="df-xor",
        note="df-xor",
    )

    # trubifal: ( ( ⊤ ↔ ⊥ ) ↔ ⊥ )
    s_trubifal = lb.ref(
        "s_trubifal",
        "( ( ⊤ ↔ ⊥ ) ↔ ⊥ )",
        ref="trubifal",
        note="trubifal",
    )

    # xchbinx: ( ( ⊤ ⊻ ⊥ ) ↔ ¬ ⊥ )
    s_xchbinx = lb.ref(
        "s_xchbinx",
        "( ( ⊤ ⊻ ⊥ ) ↔ ¬ ⊥ )",
        s_dfxor,
        s_trubifal,
        ref="xchbinx",
        note="xchbinx",
    )

    # notfal: ( ¬ ⊥ ↔ ⊤ )
    s_notfal = lb.ref(
        "s_notfal",
        "( ¬ ⊥ ↔ ⊤ )",
        ref="notfal",
        note="notfal",
    )

    # bitri: ( ( ⊤ ⊻ ⊥ ) ↔ ⊤ )
    res = lb.ref(
        "res",
        "( ( ⊤ ⊻ ⊥ ) ↔ ⊤ )",
        s_xchbinx,
        s_notfal,
        ref="bitri",
        note="bitri",
    )

    return lb.build(res)


def prove_bifal(sys: System) -> Proof:
    """bifal: ( φ ↔ ⊥ ).

    A wff is equivalent to falsehood if its negation is provable.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "bifal")
    h1 = lb.hyp("bifal.1", "¬ φ")
    fal_step = lb.ref("fal_step", "¬ ⊥", ref="fal", note="fal")
    res = lb.ref("res", "( φ ↔ ⊥ )", h1, fal_step, ref="2false", note="2false")
    return lb.build(res)


def prove_nbfal(sys: System) -> Proof:
    """nbfal: ( ¬ φ ↔ ( φ ↔ ⊥ ) ).

    The negation of a wff is equivalent to the wff being equivalent to
    falsehood.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "nbfal")
    fal_step = lb.ref("fal_step", "¬ ⊥", ref="fal", note="fal")
    res = lb.ref("res", "( ¬ φ ↔ ( φ ↔ ⊥ ) )", fal_step, ref="nbn", note="nbn")
    return lb.build(res)


def prove_merco1lem11(sys: System) -> Proof:
    """merco1lem11: ( φ → ψ ) → ( ( ( χ → ( φ → τ ) ) → ⊥ ) → ψ ).

    Used to rederive the Tarski-Bernays-Wajsberg axioms from merco1.
    (Contributed by Anthony Hart, 18-Sep-2011.)
    """
    lb = ProofBuilder(sys, "merco1lem11")

    s1 = lb.ref(
        "s1",
        "( ( ( ( ( ( ψ → φ ) → ( ( ( χ → ( φ → τ ) ) → ⊥ ) → ⊥ ) ) → ⊥ ) → ⊥ ) → ⊥ ) → ( ( ( ψ → φ ) → ( ( ( χ → ( φ → τ ) ) → ⊥ ) → ⊥ ) ) → ⊥ ) )",
        ref="merco1lem5",
        note="merco1lem5",
    )

    s2 = lb.ref(
        "s2",
        "( ( ( ( ( ( ( ψ → φ ) → ( ( ( χ → ( φ → τ ) ) → ⊥ ) → ⊥ ) ) → ⊥ ) → ⊥ ) → ⊥ ) → ( ( ( ψ → φ ) → ( ( ( χ → ( φ → τ ) ) → ⊥ ) → ⊥ ) ) → ⊥ ) ) → ( ( ( ψ → φ ) → ( ( ( χ → ( φ → τ ) ) → ⊥ ) → ⊥ ) ) → ( ( ( ( ψ → φ ) → ( ( ( χ → ( φ → τ ) ) → ⊥ ) → ⊥ ) ) → ⊥ ) → ⊥ ) ) )",
        ref="merco1lem3",
        note="merco1lem3",
    )

    s3 = lb.mp("s3", s1, s2, "ax-mp 1,2")

    s4 = lb.ref(
        "s4",
        "( ( ( ( ψ → φ ) → ( ( ( χ → ( φ → τ ) ) → ⊥ ) → ⊥ ) ) → ( ( ( ( ψ → φ ) → ( ( ( χ → ( φ → τ ) ) → ⊥ ) → ⊥ ) ) → ⊥ ) → ⊥ ) ) → ( ( ( ( χ → ( φ → τ ) ) → ⊥ ) → ⊥ ) → ( ( ( ( ψ → φ ) → ( ( ( χ → ( φ → τ ) ) → ⊥ ) → ⊥ ) ) → ⊥ ) → ⊥ ) ) )",
        ref="merco1lem4",
        note="merco1lem4",
    )

    s5 = lb.mp("s5", s3, s4, "ax-mp 3,4")

    s6 = lb.ref(
        "s6",
        "( ( ( ( ( χ → ( φ → τ ) ) → ⊥ ) → ⊥ ) → ( ( ( ( ψ → φ ) → ( ( ( χ → ( φ → τ ) ) → ⊥ ) → ⊥ ) ) → ⊥ ) → ⊥ ) ) → ( ( χ → ( φ → τ ) ) → ( ( ( ( ψ → φ ) → ( ( ( χ → ( φ → τ ) ) → ⊥ ) → ⊥ ) ) → ⊥ ) → ⊥ ) ) )",
        ref="merco1lem5",
        note="merco1lem5",
    )

    s7 = lb.mp("s7", s5, s6, "ax-mp 5,6")

    s8 = lb.ref(
        "s8",
        "( ( ( χ → ( φ → τ ) ) → ( ( ( ( ψ → φ ) → ( ( ( χ → ( φ → τ ) ) → ⊥ ) → ⊥ ) ) → ⊥ ) → ⊥ ) ) → ( ( φ → τ ) → ( ( ( ( ψ → φ ) → ( ( ( χ → ( φ → τ ) ) → ⊥ ) → ⊥ ) ) → ⊥ ) → ⊥ ) ) )",
        ref="merco1lem4",
        note="merco1lem4",
    )

    s9 = lb.mp("s9", s7, s8, "ax-mp 7,8")

    s10 = lb.ref(
        "s10",
        "( ( ( ( ( ψ → φ ) → ( ( ( χ → ( φ → τ ) ) → ⊥ ) → ⊥ ) ) → ⊥ ) → φ ) → ( ( φ → ψ ) → ( ( ( χ → ( φ → τ ) ) → ⊥ ) → ψ ) ) )",
        ref="merco1",
        note="merco1",
    )

    s11 = lb.ref(
        "s11",
        "( ( ( ( ( ( ψ → φ ) → ( ( ( χ → ( φ → τ ) ) → ⊥ ) → ⊥ ) ) → ⊥ ) → φ ) → ( ( φ → ψ ) → ( ( ( χ → ( φ → τ ) ) → ⊥ ) → ψ ) ) ) → ( ( ( φ → τ ) → ( ( ( ( ψ → φ ) → ( ( ( χ → ( φ → τ ) ) → ⊥ ) → ⊥ ) ) → ⊥ ) → ⊥ ) ) → ( ( φ → ψ ) → ( ( ( χ → ( φ → τ ) ) → ⊥ ) → ψ ) ) ) )",
        ref="merco1lem2",
        note="merco1lem2",
    )

    s12 = lb.mp("s12", s10, s11, "ax-mp 10,11")

    res = lb.mp("res", s9, s12, "ax-mp 9,12")

    return lb.build(res)


def prove_falorfal(sys: System) -> Proof:
    """falorfal: ( ( ⊥ ∨ ⊥ ) ↔ ⊥ ).

    Idempotent law for disjunction with falsehood.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "falorfal")
    res = lb.ref("res", "( ⊥ ∨ ⊥ ) ↔ ⊥", ref="oridm", note="oridm")
    return lb.build(res)


def prove_falxorfal(sys: System) -> Proof:
    """falxorfal: ( ( ⊥ ⊻ ⊥ ) ↔ ⊥ ).

    The exclusive-or of false with itself is equivalent to false.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "falxorfal")

    # df-xor: ( ( ⊥ ⊻ ⊥ ) ↔ ¬ ( ⊥ ↔ ⊥ ) )
    s_dfxor = lb.ref(
        "s_dfxor",
        "( ( ⊥ ⊻ ⊥ ) ↔ ¬ ( ⊥ ↔ ⊥ ) )",
        ref="df-xor",
        note="df-xor",
    )

    # falbifal: ( ( ⊥ ↔ ⊥ ) ↔ ⊤ )
    s_falbifal = lb.ref(
        "s_falbifal",
        "( ( ⊥ ↔ ⊥ ) ↔ ⊤ )",
        ref="falbifal",
        note="falbifal",
    )

    # xchbinx: ( ( ⊥ ⊻ ⊥ ) ↔ ¬ ⊤ )
    s_xchbinx = lb.ref(
        "s_xchbinx",
        "( ( ⊥ ⊻ ⊥ ) ↔ ¬ ⊤ )",
        s_dfxor,
        s_falbifal,
        ref="xchbinx",
        note="xchbinx",
    )

    # nottru: ( ¬ ⊤ ↔ ⊥ )
    s_nottru = lb.ref(
        "s_nottru",
        "( ¬ ⊤ ↔ ⊥ )",
        ref="nottru",
        note="nottru",
    )

    # bitri: ( ( ⊥ ⊻ ⊥ ) ↔ ⊥ )
    res = lb.ref(
        "res",
        "( ( ⊥ ⊻ ⊥ ) ↔ ⊥ )",
        s_xchbinx,
        s_nottru,
        ref="bitri",
        note="bitri",
    )

    return lb.build(res)


def prove_falxortru(sys: System) -> Proof:
    """falxortru: ( ( ⊥ ⊻ ⊤ ) ↔ ⊤ ).

    The exclusive-or of falsehood and truth is equivalent to truth.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "falxortru")

    # xorcom: ( ( ⊥ ⊻ ⊤ ) ↔ ( ⊤ ⊻ ⊥ ) )
    s_xorcom = lb.ref(
        "s_xorcom",
        "( ( ⊥ ⊻ ⊤ ) ↔ ( ⊤ ⊻ ⊥ ) )",
        ref="xorcom",
        note="xorcom",
    )

    # truxorfal: ( ( ⊤ ⊻ ⊥ ) ↔ ⊤ )
    s_truxorfal = lb.ref(
        "s_truxorfal",
        "( ( ⊤ ⊻ ⊥ ) ↔ ⊤ )",
        ref="truxorfal",
        note="truxorfal",
    )

    # bitri: ( ( ⊥ ⊻ ⊤ ) ↔ ⊤ )
    res = lb.ref(
        "res",
        "( ( ⊥ ⊻ ⊤ ) ↔ ⊤ )",
        s_xorcom,
        s_truxorfal,
        ref="bitri",
        note="bitri",
    )

    return lb.build(res)


def prove_trunorfal(sys: System) -> Proof:
    """trunorfal: ( ( ⊤ ⊽ ⊥ ) ↔ ⊥ ).

    The nor of truth and falsehood is equivalent to falsehood.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "trunorfal")

    # df-nor: ( ⊤ ⊽ ⊥ ) ↔ ¬ ( ⊤ ∨ ⊥ )
    s_dfnor = lb.ref(
        "s_dfnor",
        "( ( ⊤ ⊽ ⊥ ) ↔ ¬ ( ⊤ ∨ ⊥ ) )",
        ref="df-nor",
        note="df-nor",
    )

    # truorfal: ( ⊤ ∨ ⊥ ) ↔ ⊤
    s_truorfal = lb.ref(
        "s_truorfal",
        "( ( ⊤ ∨ ⊥ ) ↔ ⊤ )",
        ref="truorfal",
        note="truorfal",
    )

    # xchbinx: ( ⊤ ⊽ ⊥ ) ↔ ¬ ⊤
    s_xchbinx = lb.ref(
        "s_xchbinx",
        "( ( ⊤ ⊽ ⊥ ) ↔ ¬ ⊤ )",
        s_dfnor,
        s_truorfal,
        ref="xchbinx",
        note="xchbinx",
    )

    # df-fal: ⊥ ↔ ¬ ⊤
    s_dffal = lb.ref(
        "s_dffal",
        "( ⊥ ↔ ¬ ⊤ )",
        ref="df-fal",
        note="df-fal",
    )

    # bitr4i: ( ( ⊤ ⊽ ⊥ ) ↔ ⊥ )
    res = lb.ref(
        "res",
        "( ( ⊤ ⊽ ⊥ ) ↔ ⊥ )",
        s_xchbinx,
        s_dffal,
        ref="bitr4i",
        note="bitr4i",
    )

    return lb.build(res)


def prove_falortru(sys: System) -> Proof:
    """falortru: ( ( ⊥ ∨ ⊤ ) ↔ ⊤ ).

    Disjunction of falsehood and truth is equivalent to truth.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "falortru")
    s_tru = lb.ref("s_tru", "⊤", ref="tru", note="tru")
    s_or = lb.ref("s_or", "( ⊥ ∨ ⊤ )", s_tru, ref="olci", note="olci")
    res = lb.ref("res", "( ( ⊥ ∨ ⊤ ) ↔ ⊤ )", s_or, ref="bitru", note="bitru")
    return lb.build(res)


def prove_falantru(sys: System) -> Proof:
    """falantru: ( ( ⊥ ∧ ⊤ ) ↔ ⊥ ).

    A conjunction of falsehood and truth is equivalent to falsehood.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "falantru")
    s_fal = lb.ref("s_fal", "¬ ⊥", ref="fal", note="fal")
    s_intnanr = lb.ref("s_intnanr", "¬ ( ⊥ ∧ ⊤ )", s_fal, ref="intnanr", note="intnanr")
    res = lb.ref("res", "( ( ⊥ ∧ ⊤ ) ↔ ⊥ )", s_intnanr, ref="bifal", note="bifal")
    return lb.build(res)


def prove_falnortru(sys: System) -> Proof:
    """falnortru: ( ( ⊥ ⊽ ⊤ ) ↔ ⊥ ).

    The nor of falsehood and truth is equivalent to falsehood.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "falnortru")

    # norcom: ( ⊥ ⊽ ⊤ ) ↔ ( ⊤ ⊽ ⊥ )
    s_norcom = lb.ref(
        "s_norcom",
        "( ( ⊥ ⊽ ⊤ ) ↔ ( ⊤ ⊽ ⊥ ) )",
        ref="norcom",
        note="norcom",
    )

    # trunorfal: ( ⊤ ⊽ ⊥ ) ↔ ⊥
    s_trunorfal = lb.ref(
        "s_trunorfal",
        "( ( ⊤ ⊽ ⊥ ) ↔ ⊥ )",
        ref="trunorfal",
        note="trunorfal",
    )

    # bitri: ( ( ⊥ ⊽ ⊤ ) ↔ ⊥ )
    res = lb.ref(
        "res",
        "( ( ⊥ ⊽ ⊤ ) ↔ ⊥ )",
        s_norcom,
        s_trunorfal,
        ref="bitri",
        note="bitri",
    )

    return lb.build(res)


def prove_falnorfal(sys: System) -> Proof:
    """falnorfal: ( ( ⊥ ⊽ ⊥ ) ↔ ⊤ ).

    The nor of falsehood with itself is equivalent to truth.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "falnorfal")

    # df-nor: ( ⊥ ⊽ ⊥ ) ↔ ¬ ( ⊥ ∨ ⊥ )
    s_dfnor = lb.ref(
        "s_dfnor",
        "( ( ⊥ ⊽ ⊥ ) ↔ ¬ ( ⊥ ∨ ⊥ ) )",
        ref="df-nor",
        note="df-nor",
    )

    # falorfal: ( ( ⊥ ∨ ⊥ ) ↔ ⊥ )
    s_falorfal = lb.ref(
        "s_falorfal",
        "( ( ⊥ ∨ ⊥ ) ↔ ⊥ )",
        ref="falorfal",
        note="falorfal",
    )

    # xchbinx: ( ⊥ ⊽ ⊥ ) ↔ ¬ ⊥
    s_xchbinx = lb.ref(
        "s_xchbinx",
        "( ( ⊥ ⊽ ⊥ ) ↔ ¬ ⊥ )",
        s_dfnor,
        s_falorfal,
        ref="xchbinx",
        note="xchbinx",
    )

    # notfal: ( ¬ ⊥ ↔ ⊤ )
    s_notfal = lb.ref(
        "s_notfal",
        "( ¬ ⊥ ↔ ⊤ )",
        ref="notfal",
        note="notfal",
    )

    # bitri: ( ( ⊥ ⊽ ⊥ ) ↔ ⊤ )
    res = lb.ref(
        "res",
        "( ( ⊥ ⊽ ⊥ ) ↔ ⊤ )",
        s_xchbinx,
        s_notfal,
        ref="bitri",
        note="bitri",
    )

    return lb.build(res)


def prove_empty(sys: System) -> Proof:
    """empty: ( ¬ ∃ x ⊤ ↔ ∀ x ⊥ ).

    Universal quantifier of falsehood is equivalent to non-existence of truth.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "empty")
    # df-fal: ( ⊥ ↔ ¬ ⊤ )
    s1 = lb.ref("s1", "( ⊥ ↔ ¬ ⊤ )", ref="df-fal", note="df-fal")
    # albii with df-fal: ( ∀ x ⊥ ↔ ∀ x ¬ ⊤ )
    s2 = lb.ref("s2", "( ∀ x ⊥ ↔ ∀ x ¬ ⊤ )", s1, ref="albii", note="albii df-fal")
    # alnex: ( ∀ x ¬ ⊤ ↔ ¬ ∃ x ⊤ )
    s3 = lb.ref("s3", "( ∀ x ¬ ⊤ ↔ ¬ ∃ x ⊤ )", ref="alnex", note="alnex")
    # bitr2i with s2, s3: ( ¬ ∃ x ⊤ ↔ ∀ x ⊥ )
    res = lb.ref("res", "( ¬ ∃ x ⊤ ↔ ∀ x ⊥ )", s2, s3, ref="bitr2i", note="bitr2i")
    return lb.build(res)


def prove_falnantru(sys: System) -> Proof:
    """falnantru: ( ( ⊥ ⊼ ⊤ ) ↔ ⊤ ).

    The nand of falsehood and truth is equivalent to truth.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "falnantru")

    # nancom: ( ( ⊥ ⊼ ⊤ ) ↔ ( ⊤ ⊼ ⊥ ) )
    s1 = lb.ref(
        "s1",
        "( ( ⊥ ⊼ ⊤ ) ↔ ( ⊤ ⊼ ⊥ ) )",
        ref="nancom",
        note="nancom",
    )

    # trunanfal: ( ( ⊤ ⊼ ⊥ ) ↔ ⊤ )
    s2 = lb.ref(
        "s2",
        "( ( ⊤ ⊼ ⊥ ) ↔ ⊤ )",
        ref="trunanfal",
        note="trunanfal",
    )

    # bitri: ( ( ⊥ ⊼ ⊤ ) ↔ ⊤ )
    res = lb.ref(
        "res",
        "( ( ⊥ ⊼ ⊤ ) ↔ ⊤ )",
        s1,
        s2,
        ref="bitri",
        note="bitri",
    )

    return lb.build(res)


def prove_falnanfal(sys: System) -> Proof:
    """falnanfal: ( ⊥ ⊼ ⊥ ) ↔ ⊤.

    The nand of falsehood with itself is equivalent to truth.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "falnanfal")

    # nannot with φ := ⊥: ¬ ⊥ ↔ ( ⊥ ⊼ ⊥ )
    s_nannot = lb.ref(
        "s_nannot",
        "¬ ⊥ ↔ ( ⊥ ⊼ ⊥ )",
        ref="nannot",
        note="nannot",
    )

    # notfal: ¬ ⊥ ↔ ⊤
    s_notfal = lb.ref(
        "s_notfal",
        "¬ ⊥ ↔ ⊤",
        ref="notfal",
        note="notfal",
    )

    # bitr3i: ( ¬ ⊥ ↔ ( ⊥ ⊼ ⊥ ) ), ( ¬ ⊥ ↔ ⊤ ) → ( ⊥ ⊼ ⊥ ) ↔ ⊤
    res = lb.ref(
        "res",
        "( ⊥ ⊼ ⊥ ) ↔ ⊤",
        s_nannot,
        s_notfal,
        ref="bitr3i",
        note="bitr3i",
    )

    return lb.build(res)


def prove_trunantru(sys: System) -> Proof:
    """trunantru: ( ⊤ ⊼ ⊤ ) ↔ ⊥.

    The nand of truth with itself is equivalent to falsehood.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "trunantru")

    # nannot with φ := ⊤: ¬ ⊤ ↔ ( ⊤ ⊼ ⊤ )
    s_nannot = lb.ref(
        "s_nannot",
        "¬ ⊤ ↔ ( ⊤ ⊼ ⊤ )",
        ref="nannot",
        note="nannot",
    )

    # nottru: ¬ ⊤ ↔ ⊥
    s_nottru = lb.ref(
        "s_nottru",
        "¬ ⊤ ↔ ⊥",
        ref="nottru",
        note="nottru",
    )

    # bitr3i: ( ¬ ⊤ ↔ ( ⊤ ⊼ ⊤ ) ), ( ¬ ⊤ ↔ ⊥ ) → ( ⊤ ⊼ ⊤ ) ↔ ⊥
    res = lb.ref(
        "res",
        "( ⊤ ⊼ ⊤ ) ↔ ⊥",
        s_nannot,
        s_nottru,
        ref="bitr3i",
        note="bitr3i",
    )

    return lb.build(res)


# New migrations register here beside their implementation. The aggregate
# registry imports this mapping, avoiding another edit to global shim files.
MIGRATION_THEOREMS: Mapping[str, LemmaCtor] = {
    "falnanfal": prove_falnanfal,
    "trunantru": prove_trunantru,
}
