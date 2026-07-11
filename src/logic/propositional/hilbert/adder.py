"""Propositional full-adder skeleton.

set.mm range:
    ``Half adder and full adder in propositional calculus`` occupies set.mm
    lines 12588-12835.

Scope:
    This module is reserved for the propositional bit-adder connectives:

    - ``hadd`` / ``whad`` / ``df-had`` for full-adder sum
    - ``cadd`` / ``wcad`` / ``df-cad`` for full-adder carry
    - equality, associativity, commutativity, rotation, negation, and
      case-analysis theorems for both sum and carry

Boundary:
    The adder section depends on several late propositional connectives
    (exclusive disjunction, if-then-else, three-way conjunction/disjunction).
    Do not migrate these proofs until the relevant syntax constructors and
    lowering support exist.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping

from skfd.proof import Proof, ProofBuilder

from . import System

LemmaCtor = Callable[[System], Proof]


def prove_cad11(sys: System) -> Proof:
    r"""cad11: ( ( ph /\ ps ) -> cadd ph ps ch ).

    Introduction of the conditional add (full-adder carry) from a
    conjunction.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "cad11")
    # orc: ( ph /\ ps ) -> ( ( ph /\ ps ) \/ ( ch /\ ( ph \/_ ps ) ) )
    s1 = lb.ref(
        "s1",
        r"( ( ph /\ ps ) -> ( ( ph /\ ps ) \/ ( ch /\ ( ph \/_ ps ) ) ) )",
        ref="orc",
        note="orc",
    )
    # df-cad: cadd ph ps ch <-> ( ( ph /\ ps ) \/ ( ch /\ ( ph \/_ ps ) ) )
    s2 = lb.ref(
        "s2",
        r"cadd ph ps ch <-> ( ( ph /\ ps ) \/ ( ch /\ ( ph \/_ ps ) ) )",
        ref="df-cad",
        note="df-cad",
    )
    # sylibr: combine
    res = lb.ref(
        "res",
        r"( ( ph /\ ps ) -> cadd ph ps ch )",
        s1,
        s2,
        ref="sylibr",
        note="sylibr",
    )
    return lb.build(res)


def prove_cad0(sys: System) -> Proof:
    """cad0: ¬ χ → ( cadd( φ , ψ , χ ) ↔ ( φ ∧ ψ ) ).

    Conditional addition carry is equivalent to conjunction when the
    condition is false.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "cad0")
    # df-cad: cadd φ ψ χ ↔ ( ( φ ∧ ψ ) ∨ ( χ ∧ ( φ ⊻ ψ ) ) )
    s1 = lb.ref(
        "s1",
        "cadd φ ψ χ ↔ ( ( φ ∧ ψ ) ∨ ( χ ∧ ( φ ⊻ ψ ) ) )",
        ref="df-cad",
        note="df-cad",
    )
    # idd: ¬ χ → ( ( φ ∧ ψ ) → ( φ ∧ ψ ) )
    s2 = lb.ref(
        "s2",
        "¬ χ → ( ( φ ∧ ψ ) → ( φ ∧ ψ ) )",
        ref="idd",
        note="idd",
    )
    # pm2.21: ¬ χ → ( χ → ( φ ∧ ψ ) )
    s3 = lb.ref(
        "s3",
        "¬ χ → ( χ → ( φ ∧ ψ ) )",
        ref="pm2.21",
        note="pm2.21",
    )
    # adantrd: ¬ χ → ( ( χ ∧ ( φ ⊻ ψ ) ) → ( φ ∧ ψ ) )
    s4 = lb.ref(
        "s4",
        "¬ χ → ( ( χ ∧ ( φ ⊻ ψ ) ) → ( φ ∧ ψ ) )",
        s3,
        ref="adantrd",
        note="adantrd",
    )
    # jaod: ¬ χ → ( ( ( φ ∧ ψ ) ∨ ( χ ∧ ( φ ⊻ ψ ) ) ) → ( φ ∧ ψ ) )
    s5 = lb.ref(
        "s5",
        "¬ χ → ( ( ( φ ∧ ψ ) ∨ ( χ ∧ ( φ ⊻ ψ ) ) ) → ( φ ∧ ψ ) )",
        s2,
        s4,
        ref="jaod",
        note="jaod",
    )
    # biimtrid: ¬ χ → ( cadd φ ψ χ → ( φ ∧ ψ ) )
    s6 = lb.ref(
        "s6",
        "¬ χ → ( cadd φ ψ χ → ( φ ∧ ψ ) )",
        s1,
        s5,
        ref="biimtrid",
        note="biimtrid",
    )
    # cad11: ( φ ∧ ψ ) → cadd φ ψ χ
    s7 = lb.ref(
        "s7",
        "( φ ∧ ψ ) → cadd φ ψ χ",
        ref="cad11",
        note="cad11",
    )
    # impbid1: ¬ χ → ( cadd φ ψ χ ↔ ( φ ∧ ψ ) )
    res = lb.ref(
        "res",
        "¬ χ → ( cadd φ ψ χ ↔ ( φ ∧ ψ ) )",
        s6,
        s7,
        ref="impbid1",
        note="impbid1",
    )
    return lb.build(res)


def prove_cadcoma(sys: System) -> Proof:
    """cadcoma: cadd( φ , ψ , χ ) ↔ cadd( ψ , φ , χ ).

    Commutativity of the first two arguments of the conditional addition
    (full-adder carry).  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "cadcoma")

    # ancom: ( φ ∧ ψ ) ↔ ( ψ ∧ φ )
    s_ancom = lb.ref(
        "s_ancom",
        "( φ ∧ ψ ) ↔ ( ψ ∧ φ )",
        ref="ancom",
        note="ancom",
    )

    # xorcom: ( φ ⊻ ψ ) ↔ ( ψ ⊻ φ )
    s_xorcom = lb.ref(
        "s_xorcom",
        "( φ ⊻ ψ ) ↔ ( ψ ⊻ φ )",
        ref="xorcom",
        note="xorcom",
    )

    # anbi2i: ( χ ∧ ( φ ⊻ ψ ) ) ↔ ( χ ∧ ( ψ ⊻ φ ) )
    s_anbi2i = lb.ref(
        "s_anbi2i",
        "( χ ∧ ( φ ⊻ ψ ) ) ↔ ( χ ∧ ( ψ ⊻ φ ) )",
        s_xorcom,
        ref="anbi2i",
        note="anbi2i",
    )

    # orbi12i: ( ( φ ∧ ψ ) ∨ ( χ ∧ ( φ ⊻ ψ ) ) ) ↔ ( ( ψ ∧ φ ) ∨ ( χ ∧ ( ψ ⊻ φ ) ) )
    s_orbi12i = lb.ref(
        "s_orbi12i",
        "( ( φ ∧ ψ ) ∨ ( χ ∧ ( φ ⊻ ψ ) ) ) ↔ ( ( ψ ∧ φ ) ∨ ( χ ∧ ( ψ ⊻ φ ) ) )",
        s_ancom,
        s_anbi2i,
        ref="orbi12i",
        note="orbi12i",
    )

    # df-cad: cadd φ ψ χ ↔ ( ( φ ∧ ψ ) ∨ ( χ ∧ ( φ ⊻ ψ ) ) )
    s_df_cad1 = lb.ref(
        "s_df_cad1",
        "cadd φ ψ χ ↔ ( ( φ ∧ ψ ) ∨ ( χ ∧ ( φ ⊻ ψ ) ) )",
        ref="df-cad",
        note="df-cad",
    )

    # df-cad: cadd ψ φ χ ↔ ( ( ψ ∧ φ ) ∨ ( χ ∧ ( ψ ⊻ φ ) ) )
    s_df_cad2 = lb.ref(
        "s_df_cad2",
        "cadd ψ φ χ ↔ ( ( ψ ∧ φ ) ∨ ( χ ∧ ( ψ ⊻ φ ) ) )",
        ref="df-cad",
        note="df-cad",
    )

    # 3bitr4i: cadd φ ψ χ ↔ cadd ψ φ χ
    res = lb.ref(
        "res",
        "cadd φ ψ χ ↔ cadd ψ φ χ",
        s_orbi12i,
        s_df_cad1,
        s_df_cad2,
        ref="3bitr4i",
        note="3bitr4i",
    )

    return lb.build(res)


def prove_cadbi123d(sys: System) -> Proof:
    """cadbi123d: φ → ( cadd ψ θ η ↔ cadd χ τ ζ ).

    Deduction joining three biconditionals with conditional addition
    (full-adder carry).  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "cadbi123d")
    h1 = lb.hyp("cadbid.1", "φ → ( ψ ↔ χ )")
    h2 = lb.hyp("cadbid.2", "φ → ( θ ↔ τ )")
    h3 = lb.hyp("cadbid.3", "φ → ( η ↔ ζ )")

    # anbi12d: φ → ( ( ψ ∧ θ ) ↔ ( χ ∧ τ ) )
    s1 = lb.ref(
        "s1",
        "φ → ( ( ψ ∧ θ ) ↔ ( χ ∧ τ ) )",
        h1,
        h2,
        ref="anbi12d",
        note="anbi12d",
    )

    # xorbi12d: φ → ( ( ψ ⊻ θ ) ↔ ( χ ⊻ τ ) )
    s2 = lb.ref(
        "s2",
        "φ → ( ( ψ ⊻ θ ) ↔ ( χ ⊻ τ ) )",
        h1,
        h2,
        ref="xorbi12d",
        note="xorbi12d",
    )

    # anbi12d: φ → ( ( η ∧ ( ψ ⊻ θ ) ) ↔ ( ζ ∧ ( χ ⊻ τ ) ) )
    s3 = lb.ref(
        "s3",
        "φ → ( ( η ∧ ( ψ ⊻ θ ) ) ↔ ( ζ ∧ ( χ ⊻ τ ) ) )",
        h3,
        s2,
        ref="anbi12d",
        note="anbi12d",
    )

    # orbi12d: φ → ( ( ( ψ ∧ θ ) ∨ ( η ∧ ( ψ ⊻ θ ) ) ) ↔ ( ( χ ∧ τ ) ∨ ( ζ ∧ ( χ ⊻ τ ) ) ) )
    s4 = lb.ref(
        "s4",
        "φ → ( ( ( ψ ∧ θ ) ∨ ( η ∧ ( ψ ⊻ θ ) ) ) ↔ ( ( χ ∧ τ ) ∨ ( ζ ∧ ( χ ⊻ τ ) ) ) )",
        s1,
        s3,
        ref="orbi12d",
        note="orbi12d",
    )

    # df-cad: cadd ψ θ η ↔ ( ( ψ ∧ θ ) ∨ ( η ∧ ( ψ ⊻ θ ) ) )
    s5 = lb.ref(
        "s5",
        "cadd ψ θ η ↔ ( ( ψ ∧ θ ) ∨ ( η ∧ ( ψ ⊻ θ ) ) )",
        ref="df-cad",
        note="df-cad",
    )

    # df-cad: cadd χ τ ζ ↔ ( ( χ ∧ τ ) ∨ ( ζ ∧ ( χ ⊻ τ ) ) )
    s6 = lb.ref(
        "s6",
        "cadd χ τ ζ ↔ ( ( χ ∧ τ ) ∨ ( ζ ∧ ( χ ⊻ τ ) ) )",
        ref="df-cad",
        note="df-cad",
    )

    # 3bitr4g: φ → ( cadd ψ θ η ↔ cadd χ τ ζ )
    res = lb.ref(
        "res",
        "φ → ( cadd ψ θ η ↔ cadd χ τ ζ )",
        s4,
        s5,
        s6,
        ref="3bitr4g",
        note="3bitr4g",
    )

    return lb.build(res)


def prove_cadtru(sys: System) -> Proof:
    """cadtru: cadd( T. , T. , φ ).

    Conditional addition carry is true when both carry-in conditions
    are true.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "cadtru")
    # tru: T.
    s1 = lb.ref("s1", "T.", ref="tru", note="tru")
    # tru: T.
    s2 = lb.ref("s2", "T.", ref="tru", note="tru")
    # cad11: ( T. ∧ T. ) → cadd T. T. φ
    s3 = lb.ref("s3", "( T. ∧ T. ) → cadd T. T. φ", ref="cad11", note="cad11")
    # mp2an: cadd T. T. φ
    res = lb.ref("res", "cadd T. T. φ", s1, s2, s3, ref="mp2an", note="mp2an")
    return lb.build(res)


def prove_cadbi123i(sys: System) -> Proof:
    """cadbi123i: cadd( φ , χ , τ ) ↔ cadd( ψ , θ , η ).

    Inference joining three biconditionals with conditional addition
    (full-adder carry).  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "cadbi123i")
    h1 = lb.hyp("cadbii.1", "( φ ↔ ψ )")
    h2 = lb.hyp("cadbii.2", "( χ ↔ θ )")
    h3 = lb.hyp("cadbii.3", "( τ ↔ η )")

    # a1i: T. → ( φ ↔ ψ )
    s1 = lb.ref("s1", "T. → ( φ ↔ ψ )", h1, ref="a1i", note="a1i")
    # a1i: T. → ( χ ↔ θ )
    s2 = lb.ref("s2", "T. → ( χ ↔ θ )", h2, ref="a1i", note="a1i")
    # a1i: T. → ( τ ↔ η )
    s3 = lb.ref("s3", "T. → ( τ ↔ η )", h3, ref="a1i", note="a1i")

    # cadbi123d: T. → ( cadd φ χ τ ↔ cadd ψ θ η )
    s4 = lb.ref(
        "s4",
        "T. → ( cadd φ χ τ ↔ cadd ψ θ η )",
        s1,
        s2,
        s3,
        ref="cadbi123d",
        note="cadbi123d",
    )

    # mptru: cadd φ χ τ ↔ cadd ψ θ η
    res = lb.ref(
        "res",
        "cadd φ χ τ ↔ cadd ψ θ η",
        s4,
        ref="mptru",
        note="mptru",
    )

    return lb.build(res)


THEOREMS: Mapping[str, LemmaCtor] = {
    "cad0": prove_cad0,
    "cad11": prove_cad11,
    "cadbi123d": prove_cadbi123d,
    "cadbi123i": prove_cadbi123i,
    "cadcoma": prove_cadcoma,
    "cadtru": prove_cadtru,
}

__all__ = [
    "LemmaCtor",
    "THEOREMS",
    "prove_cad0",
    "prove_cad11",
    "prove_cadbi123d",
    "prove_cadbi123i",
    "prove_cadcoma",
    "prove_cadtru",
]
