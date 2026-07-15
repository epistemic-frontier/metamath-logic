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


def prove_cad1(sys: System) -> Proof:
    """cad1: χ → ( cadd( φ , ψ , χ ) ↔ ( φ ∨ ψ ) ).

    Conditional addition carry with true carry-in is equivalent to
    disjunction.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "cad1")

    # cadan: cadd φ ψ χ ↔ ((φ ∨ ψ) ∧ (φ ∨ χ) ∧ (ψ ∨ χ))
    s1 = lb.ref(
        "s1",
        "cadd φ ψ χ ↔ ( ( φ ∨ ψ ) ∧ ( φ ∨ χ ) ∧ ( ψ ∨ χ ) )",
        ref="cadan",
        note="cadan",
    )

    # 3anass: ((φ ∨ ψ) ∧ (φ ∨ χ) ∧ (ψ ∨ χ)) ↔ ((φ ∨ ψ) ∧ ((φ ∨ χ) ∧ (ψ ∨ χ)))
    s2 = lb.ref(
        "s2",
        "( ( φ ∨ ψ ) ∧ ( φ ∨ χ ) ∧ ( ψ ∨ χ ) ) ↔ ( ( φ ∨ ψ ) ∧ ( ( φ ∨ χ ) ∧ ( ψ ∨ χ ) ) )",
        ref="3anass",
        note="3anass",
    )

    # bitri: cadd φ ψ χ ↔ ((φ ∨ ψ) ∧ ((φ ∨ χ) ∧ (ψ ∨ χ)))
    s3 = lb.ref(
        "s3",
        "cadd φ ψ χ ↔ ( ( φ ∨ ψ ) ∧ ( ( φ ∨ χ ) ∧ ( ψ ∨ χ ) ) )",
        s1,
        s2,
        ref="bitri",
        note="bitri",
    )

    # olc: χ → (φ ∨ χ)
    s4 = lb.ref(
        "s4",
        "χ → ( φ ∨ χ )",
        ref="olc",
        note="olc",
    )

    # olc: χ → (ψ ∨ χ)
    s5 = lb.ref(
        "s5",
        "χ → ( ψ ∨ χ )",
        ref="olc",
        note="olc",
    )

    # jca: χ → ((φ ∨ χ) ∧ (ψ ∨ χ))
    s6 = lb.ref(
        "s6",
        "χ → ( ( φ ∨ χ ) ∧ ( ψ ∨ χ ) )",
        s4,
        s5,
        ref="jca",
        note="jca",
    )

    # biantrud: χ → ((φ ∨ ψ) ↔ ((φ ∨ ψ) ∧ ((φ ∨ χ) ∧ (ψ ∨ χ))))
    s7 = lb.ref(
        "s7",
        "χ → ( ( φ ∨ ψ ) ↔ ( ( φ ∨ ψ ) ∧ ( ( φ ∨ χ ) ∧ ( ψ ∨ χ ) ) ) )",
        s6,
        ref="biantrud",
        note="biantrud",
    )

    # bitr4id: χ → (cadd φ ψ χ ↔ (φ ∨ ψ))
    res = lb.ref(
        "res",
        "χ → ( cadd φ ψ χ ↔ ( φ ∨ ψ ) )",
        s7,
        s3,
        ref="bitr4id",
        note="bitr4id",
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


def prove_cadifp(sys: System) -> Proof:
    """cadifp: cadd(φ, ψ, χ) ↔ if-(χ, (φ ∨ ψ), (φ ∧ ψ)).

    Conditional addition carry expressed in terms of the conditional
    operator.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "cadifp")
    # cad1: χ → (cadd φ ψ χ ↔ (φ ∨ ψ))
    s1 = lb.ref(
        "s1",
        "χ → ( cadd φ ψ χ ↔ ( φ ∨ ψ ) )",
        ref="cad1",
        note="cad1",
    )
    # cad0: ¬χ → (cadd φ ψ χ ↔ (φ ∧ ψ))
    s2 = lb.ref(
        "s2",
        "¬ χ → ( cadd φ ψ χ ↔ ( φ ∧ ψ ) )",
        ref="cad0",
        note="cad0",
    )
    # casesifp: from φ→(ψ↔χ) and ¬φ→(ψ↔θ), conclude ψ ↔ if-(φ, χ, θ)
    res = lb.ref(
        "res",
        "cadd φ ψ χ ↔ if- χ ( φ ∨ ψ ) ( φ ∧ ψ )",
        s1,
        s2,
        ref="casesifp",
        note="casesifp",
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


def prove_hadbi123i(sys: System) -> Proof:
    """hadbi123i: hadd( φ , χ , τ ) ↔ hadd( ψ , θ , η ).

    Inference joining three biconditionals with half-adder sum.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "hadbi123i")
    h1 = lb.hyp("hadbii.1", "( φ ↔ ψ )")
    h2 = lb.hyp("hadbii.2", "( χ ↔ θ )")
    h3 = lb.hyp("hadbii.3", "( τ ↔ η )")

    # a1i: T. → ( φ ↔ ψ )
    s1 = lb.ref("s1", "T. → ( φ ↔ ψ )", h1, ref="a1i", note="a1i")
    # a1i: T. → ( χ ↔ θ )
    s2 = lb.ref("s2", "T. → ( χ ↔ θ )", h2, ref="a1i", note="a1i")
    # a1i: T. → ( τ ↔ η )
    s3 = lb.ref("s3", "T. → ( τ ↔ η )", h3, ref="a1i", note="a1i")

    # hadbi123d: T. → ( hadd φ χ τ ↔ hadd ψ θ η )
    s4 = lb.ref(
        "s4",
        "T. → ( hadd φ χ τ ↔ hadd ψ θ η )",
        s1,
        s2,
        s3,
        ref="hadbi123d",
        note="hadbi123d",
    )

    # mptru: hadd φ χ τ ↔ hadd ψ θ η
    res = lb.ref(
        "res",
        "hadd φ χ τ ↔ hadd ψ θ η",
        s4,
        ref="mptru",
        note="mptru",
    )

    return lb.build(res)


def prove_hadbi123d(sys: System) -> Proof:
    """hadbi123d: φ → ( hadd ψ θ η ↔ hadd χ τ ζ ).

    Deduction joining three biconditionals with half-adder sum.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "hadbi123d")
    h1 = lb.hyp("hadbid.1", "φ → ( ψ ↔ χ )")
    h2 = lb.hyp("hadbid.2", "φ → ( θ ↔ τ )")
    h3 = lb.hyp("hadbid.3", "φ → ( η ↔ ζ )")

    # xorbi12d: φ → ( ( ψ ⊻ θ ) ↔ ( χ ⊻ τ ) )
    s1 = lb.ref(
        "s1",
        "φ → ( ( ψ ⊻ θ ) ↔ ( χ ⊻ τ ) )",
        h1,
        h2,
        ref="xorbi12d",
        note="xorbi12d",
    )

    # xorbi12d: φ → ( ( ( ψ ⊻ θ ) ⊻ η ) ↔ ( ( χ ⊻ τ ) ⊻ ζ ) )
    s2 = lb.ref(
        "s2",
        "φ → ( ( ( ψ ⊻ θ ) ⊻ η ) ↔ ( ( χ ⊻ τ ) ⊻ ζ ) )",
        s1,
        h3,
        ref="xorbi12d",
        note="xorbi12d",
    )

    # df-had: hadd ψ θ η ↔ ( ( ψ ⊻ θ ) ⊻ η )
    s3 = lb.ref(
        "s3",
        "hadd ψ θ η ↔ ( ( ψ ⊻ θ ) ⊻ η )",
        ref="df-had",
        note="df-had",
    )

    # df-had: hadd χ τ ζ ↔ ( ( χ ⊻ τ ) ⊻ ζ )
    s4 = lb.ref(
        "s4",
        "hadd χ τ ζ ↔ ( ( χ ⊻ τ ) ⊻ ζ )",
        ref="df-had",
        note="df-had",
    )

    # 3bitr4g: φ → ( hadd ψ θ η ↔ hadd χ τ ζ )
    res = lb.ref(
        "res",
        "φ → ( hadd ψ θ η ↔ hadd χ τ ζ )",
        s2,
        s3,
        s4,
        ref="3bitr4g",
        note="3bitr4g",
    )

    return lb.build(res)


def prove_cador(sys: System) -> Proof:
    """cador: cadd( φ , ψ , χ ) ↔ ( ( φ ∧ ψ ) ∨ ( φ ∧ χ ) ∨ ( ψ ∧ χ ) ).

    The adder carry in disjunctive normal form.
    (Contributed by NM, 5-Aug-1993.)
    (Proof shortened by Wolf Lammen, 11-Jul-2020.)
    """
    lb = ProofBuilder(sys, "cador")

    # xor2: ( φ ⊻ ψ ) ↔ ( ( φ ∨ ψ ) ∧ ¬ ( φ ∧ ψ ) )
    s_xor2 = lb.ref(
        "s_xor2",
        "( φ ⊻ ψ ) ↔ ( ( φ ∨ ψ ) ∧ ¬ ( φ ∧ ψ ) )",
        ref="xor2",
        note="xor2",
    )

    # rbaib with xor2 as hypothesis:
    #   xor2 is of form A ↔ (B ∧ C) where A = (φ ⊻ ψ), B = (φ ∨ ψ), C = ¬(φ ∧ ψ)
    #   rbaib gives: C → (A ↔ B) = ¬(φ ∧ ψ) → ((φ ⊻ ψ) ↔ (φ ∨ ψ))
    s_rbaib = lb.ref(
        "s_rbaib",
        "¬ ( φ ∧ ψ ) → ( ( φ ⊻ ψ ) ↔ ( φ ∨ ψ ) )",
        s_xor2,
        ref="rbaib",
        note="rbaib",
    )

    # anbi1d: from ¬(φ∧ψ) → ((φ⊻ψ) ↔ (φ∨ψ)), add χ as conjunct:
    #   ¬(φ ∧ ψ) → (((φ ⊻ ψ) ∧ χ) ↔ ((φ ∨ ψ) ∧ χ))
    s_anbi1d = lb.ref(
        "s_anbi1d",
        "¬ ( φ ∧ ψ ) → ( ( ( φ ⊻ ψ ) ∧ χ ) ↔ ( ( φ ∨ ψ ) ∧ χ ) )",
        s_rbaib,
        ref="anbi1d",
        note="anbi1d",
    )

    # ancom: ((φ ⊻ ψ) ∧ χ) ↔ (χ ∧ (φ ⊻ ψ))
    s_ancom = lb.ref(
        "s_ancom",
        "( ( φ ⊻ ψ ) ∧ χ ) ↔ ( χ ∧ ( φ ⊻ ψ ) )",
        ref="ancom",
        note="ancom",
    )

    # andir: ((φ ∨ ψ) ∧ χ) ↔ ((φ ∧ χ) ∨ (ψ ∧ χ))
    s_andir = lb.ref(
        "s_andir",
        "( ( φ ∨ ψ ) ∧ χ ) ↔ ( ( φ ∧ χ ) ∨ ( ψ ∧ χ ) )",
        ref="andir",
        note="andir",
    )

    # 3bitr3g: from h1: ¬(φ∧ψ)→(((φ⊻ψ)∧χ)↔((φ∨ψ)∧χ))
    #          h2: ((φ⊻ψ)∧χ) ↔ (χ∧(φ⊻ψ))
    #          h3: ((φ∨ψ)∧χ) ↔ ((φ∧χ)∨(ψ∧χ))
    #   gives: ¬(φ∧ψ) → ((χ∧(φ⊻ψ)) ↔ ((φ∧χ)∨(ψ∧χ)))
    s_3bitr3g = lb.ref(
        "s_3bitr3g",
        "¬ ( φ ∧ ψ ) → ( ( χ ∧ ( φ ⊻ ψ ) ) ↔ ( ( φ ∧ χ ) ∨ ( ψ ∧ χ ) ) )",
        s_anbi1d,
        s_ancom,
        s_andir,
        ref="3bitr3g",
        note="3bitr3g",
    )

    # pm5.74i:
    #   (¬(φ∧ψ) → ((χ∧(φ⊻ψ)) ↔ ((φ∧χ)∨(ψ∧χ))))
    #   → ((¬(φ∧ψ) → (χ∧(φ⊻ψ))) ↔ (¬(φ∧ψ) → ((φ∧χ)∨(ψ∧χ))))
    s_pm5_74i = lb.ref(
        "s_pm5_74i",
        "( ( ¬ ( φ ∧ ψ ) → ( χ ∧ ( φ ⊻ ψ ) ) ) ↔ ( ¬ ( φ ∧ ψ ) → ( ( φ ∧ χ ) ∨ ( ψ ∧ χ ) ) ) )",
        s_3bitr3g,
        ref="pm5.74i",
        note="pm5.74i",
    )

    # df-or: ((φ ∧ ψ) ∨ (χ ∧ (φ ⊻ ψ))) ↔ (¬(φ ∧ ψ) → (χ ∧ (φ ⊻ ψ)))
    s_df_or_left = lb.ref(
        "s_df_or_left",
        "( ( φ ∧ ψ ) ∨ ( χ ∧ ( φ ⊻ ψ ) ) ) ↔ ( ¬ ( φ ∧ ψ ) → ( χ ∧ ( φ ⊻ ψ ) ) )",
        ref="df-or",
        note="df-or",
    )

    # df-or: ((φ ∧ ψ) ∨ ((φ ∧ χ) ∨ (ψ ∧ χ))) ↔ (¬(φ ∧ ψ) → ((φ ∧ χ) ∨ (ψ ∧ χ)))
    s_df_or_right = lb.ref(
        "s_df_or_right",
        "( ( φ ∧ ψ ) ∨ ( ( φ ∧ χ ) ∨ ( ψ ∧ χ ) ) ) ↔ ( ¬ ( φ ∧ ψ ) → ( ( φ ∧ χ ) ∨ ( ψ ∧ χ ) ) )",
        ref="df-or",
        note="df-or",
    )

    # 3bitr4i: chain the three biconditionals
    #   h1: pm5.74i result
    #   h2: df-or left
    #   h3: df-or right
    #   gives: ((φ∧ψ)∨(χ∧(φ⊻ψ))) ↔ ((φ∧ψ)∨((φ∧χ)∨(ψ∧χ)))
    s_3bitr4i = lb.ref(
        "s_3bitr4i",
        "( ( φ ∧ ψ ) ∨ ( χ ∧ ( φ ⊻ ψ ) ) ) ↔ ( ( φ ∧ ψ ) ∨ ( ( φ ∧ χ ) ∨ ( ψ ∧ χ ) ) )",
        s_pm5_74i,
        s_df_or_left,
        s_df_or_right,
        ref="3bitr4i",
        note="3bitr4i",
    )

    # df-cad: cadd(φ, ψ, χ) ↔ ((φ ∧ ψ) ∨ (χ ∧ (φ ⊻ ψ)))
    s_df_cad = lb.ref(
        "s_df_cad",
        "cadd φ ψ χ ↔ ( ( φ ∧ ψ ) ∨ ( χ ∧ ( φ ⊻ ψ ) ) )",
        ref="df-cad",
        note="df-cad",
    )

    # 3orass: ((φ ∧ ψ) ∨ (φ ∧ χ) ∨ (ψ ∧ χ)) ↔ ((φ ∧ ψ) ∨ ((φ ∧ χ) ∨ (ψ ∧ χ)))
    s_3orass = lb.ref(
        "s_3orass",
        "( ( φ ∧ ψ ) ∨ ( φ ∧ χ ) ∨ ( ψ ∧ χ ) ) ↔ ( ( φ ∧ ψ ) ∨ ( ( φ ∧ χ ) ∨ ( ψ ∧ χ ) ) )",
        ref="3orass",
        note="3orass",
    )

    # Final 3bitr4i:
    #   h1: s_3bitr4i
    #   h2: s_df_cad
    #   h3: s_3orass
    #   gives: cadd(φ, ψ, χ) ↔ ((φ ∧ ψ) ∨ (φ ∧ χ) ∨ (ψ ∧ χ))
    res = lb.ref(
        "res",
        "cadd φ ψ χ ↔ ( ( φ ∧ ψ ) ∨ ( φ ∧ χ ) ∨ ( ψ ∧ χ ) )",
        s_3bitr4i,
        s_df_cad,
        s_3orass,
        ref="3bitr4i",
        note="3bitr4i",
    )

    return lb.build(res)


THEOREMS: Mapping[str, LemmaCtor] = {
    "cad0": prove_cad0,
    "cad1": prove_cad1,
    "cad11": prove_cad11,
    "cadbi123d": prove_cadbi123d,
    "cadbi123i": prove_cadbi123i,
    "cadifp": prove_cadifp,
    "cadcoma": prove_cadcoma,
    "cadtru": prove_cadtru,
    "cador": prove_cador,
    "hadbi123i": prove_hadbi123i,
    "hadbi123d": prove_hadbi123d,
}

__all__ = [
    "LemmaCtor",
    "THEOREMS",
    "prove_cad0",
    "prove_cad1",
    "prove_cad11",
    "prove_cadbi123d",
    "prove_cadbi123i",
    "prove_cadifp",
    "prove_cadcoma",
    "prove_cadtru",
    "prove_cador",
    "prove_hadbi123i",
    "prove_hadbi123d",
]
