"""Disjunction calculus.

φ∨ψ = ¬ φ→ψ (Hilbert encoding).
Includes Peirce's law, ja, basic properties.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping

from skfd.proof import Proof, ProofBuilder

from . import System

LemmaCtor = Callable[[System], Proof]


def prove_ja(sys: System) -> Proof:
    """
    ja: ( ( φ → ψ ) → χ ). Hyp1: ¬ φ → χ, Hyp2: ψ → χ.

    Inference joining antecedents.
    set.mm proof: imim2i pm2.61d1.
    """
    lb = ProofBuilder(sys, "ja")
    h1 = lb.hyp("ja.1", "¬ φ → χ")
    h2 = lb.hyp("ja.2", "ψ → χ")

    s1 = lb.ref("s1", "( φ → ψ ) → ( φ → χ )", h2, ref="imim2i", note="imim2i")
    res = lb.ref("res", "( φ → ψ ) → χ", s1, h1, ref="pm2.61d1", note="pm2.61d1")
    return lb.build(res)


def prove_peirce(sys: System) -> Proof:
    """
    peirce: ( ( ( φ → ψ ) → φ ) → φ ).

    Peirce's axiom.  Derived from simplim, id, ja.
    """
    lb = ProofBuilder(sys, "peirce")
    s1 = lb.ref("s1", "¬ ( φ → ψ ) → φ", ref="simplim", note="simplim")
    s2 = lb.ref("s2", "φ → φ", ref="id", note="id")
    res = lb.ref("res", "( ( φ → ψ ) → φ ) → φ", s1, s2, ref="ja", note="ja")
    return lb.build(res)


def prove_pm1_4(sys: System) -> Proof:
    lb = ProofBuilder(sys, "pm1.4")
    s1 = lb.ref("s1", "( ¬ φ → ψ ) → ( ¬ ψ → ¬ ¬ φ )", ref="con3", note="con3")
    notnot = lb.ref("notnot", "¬ ¬ φ → φ", ref="notnotr", note="notnotr")
    s2 = lb.ref("s2", "( ¬ φ → ψ ) → ( ¬ ψ → φ )", s1, notnot, ref="syl6", note="syl6")
    df_or_left = lb.ref(
        "df_or_left",
        "( φ ∨ ψ ) ↔ ( ¬ φ → ψ )",
        ref="df-or",
        note="df-or",
    )
    left = lb.ref(
        "left",
        "( φ ∨ ψ ) → ( ¬ φ → ψ )",
        df_or_left,
        ref="biimpi",
        note="biimpi",
    )
    df_or_right = lb.ref(
        "df_or_right",
        "( ψ ∨ φ ) ↔ ( ¬ ψ → φ )",
        ref="df-or",
        note="df-or",
    )
    right = lb.ref(
        "right",
        "( ¬ ψ → φ ) → ( ψ ∨ φ )",
        df_or_right,
        ref="biimpri",
        note="biimpri",
    )
    res = lb.ref("res", "( φ ∨ ψ ) → ( ψ ∨ φ )", left, s2, right, ref="3syl", note="3syl")
    return lb.build(res)


def prove_pm1_5(sys: System) -> Proof:
    r"""pm1.5: ( ( ph \/ ( ps \/ ch ) ) -> ( ps \/ ( ph \/ ch ) ) ).

    Swap the first disjunct with a disjunction of the second and third.
    """
    lb = ProofBuilder(sys, "pm1.5")
    s1 = lb.ref("s1", r"ph -> ( ph \/ ch )", ref="orc", note="orc")
    s2 = lb.ref("s2", r"ph -> ( ps \/ ( ph \/ ch ) )", s1, ref="olcd", note="olcd(orc)")
    s3 = lb.ref("s3", r"ch -> ( ph \/ ch )", ref="olc", note="olc")
    s4 = lb.ref(
        "s4", r"( ps \/ ch ) -> ( ps \/ ( ph \/ ch ) )", s3, ref="orim2i", note="orim2i(olc)"
    )
    res = lb.ref(
        "res", r"( ph \/ ( ps \/ ch ) ) -> ( ps \/ ( ph \/ ch ) )", s2, s4, ref="jaoi", note="jaoi"
    )
    return lb.build(res)


def prove_or12(sys: System) -> Proof:
    r"""or12: ( ( ph \/ ( ps \/ ch ) ) <-> ( ps \/ ( ph \/ ch ) ) ).

    Swap the first and second disjuncts in a disjunction of three.
    (Contributed by NM, 2-Feb-1993.)
    set.mm proof: pm1.5 pm1.5 impbii.
    """
    lb = ProofBuilder(sys, "or12")
    s1 = lb.ref(
        "s1", r"( ph \/ ( ps \/ ch ) ) -> ( ps \/ ( ph \/ ch ) )", ref="pm1.5", note="pm1.5"
    )
    s2 = lb.ref(
        "s2", r"( ps \/ ( ph \/ ch ) ) -> ( ph \/ ( ps \/ ch ) )", ref="pm1.5", note="pm1.5"
    )
    res = lb.ref(
        "res",
        r"( ( ph \/ ( ps \/ ch ) ) <-> ( ps \/ ( ph \/ ch ) ) )",
        s1,
        s2,
        ref="impbii",
        note="impbii",
    )
    return lb.build(res)


def prove_orcom(sys: System) -> Proof:
    """orcom: ( ( ph ∨ ps ) <-> ( ps ∨ ph ) ).

    Commutative law for disjunction.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "orcom")
    s1 = lb.ref("s1", "( ph ∨ ps ) -> ( ps ∨ ph )", ref="pm1.4", note="pm1.4")
    s2 = lb.ref("s2", "( ps ∨ ph ) -> ( ph ∨ ps )", ref="pm1.4", note="pm1.4")
    res = lb.ref("res", "( ( ph ∨ ps ) <-> ( ps ∨ ph ) )", s1, s2, ref="impbii", note="impbii")
    return lb.build(res)


def prove_orcomd(sys: System) -> Proof:
    """orcomd: ( ph → ( ch ∨ ps ) ).  Hyp: ( ph → ( ps ∨ ch ) ).

    Deduction form of orcom.
    """
    lb = ProofBuilder(sys, "orcomd")
    h1 = lb.hyp("orcomd.1", "( ph → ( ps ∨ ch ) )")
    s1 = lb.ref("s1", "( ( ps ∨ ch ) ↔ ( ch ∨ ps ) )", ref="orcom", note="orcom")
    res = lb.ref("res", "( ph → ( ch ∨ ps ) )", h1, s1, ref="sylib", note="sylib")
    return lb.build(res)


def prove_pm2_38(sys: System) -> Proof:
    """pm2.38: (ψ → χ) → ((ψ ∨ φ) → (χ ∨ φ)).

    A disjunct can be added to the consequent and antecedent of an implication.
    """
    lb = ProofBuilder(sys, "pm2.38")
    s1 = lb.ref("s1", "( ψ → χ ) → ( ¬ χ → ¬ ψ )", ref="con3", note="con3")
    s2 = lb.ref("s2", "( ¬ χ → ¬ ψ ) → ( ( ¬ ψ → φ ) → ( ¬ χ → φ ) )", ref="imim1", note="imim1")
    expanded = lb.ref(
        "expanded",
        "( ψ → χ ) → ( ( ¬ ψ → φ ) → ( ¬ χ → φ ) )",
        s1,
        s2,
        ref="syl",
        note="syl",
    )
    df_or_left = lb.ref(
        "df_or_left",
        "( ψ ∨ φ ) ↔ ( ¬ ψ → φ )",
        ref="df-or",
        note="df-or",
    )
    left = lb.ref(
        "left",
        "( ψ ∨ φ ) → ( ¬ ψ → φ )",
        df_or_left,
        ref="biimpi",
        note="biimpi",
    )
    replaced_left = lb.ref(
        "replaced_left",
        "( ψ → χ ) → ( ( ψ ∨ φ ) → ( ¬ χ → φ ) )",
        left,
        expanded,
        ref="syl5",
        note="syl5",
    )
    df_or_right = lb.ref(
        "df_or_right",
        "( χ ∨ φ ) ↔ ( ¬ χ → φ )",
        ref="df-or",
        note="df-or",
    )
    right = lb.ref(
        "right",
        "( ¬ χ → φ ) → ( χ ∨ φ )",
        df_or_right,
        ref="biimpri",
        note="biimpri",
    )
    res = lb.ref(
        "res",
        "( ψ → χ ) → ( ( ψ ∨ φ ) → ( χ ∨ φ ) )",
        replaced_left,
        right,
        ref="syl6",
        note="syl6",
    )
    return lb.build(res)


def prove_pm2_36(sys: System) -> Proof:
    """pm2.36: ( ψ → χ ) → ( ( φ ∨ ψ ) → ( χ ∨ φ ) ).

    Syllogism using pm1.4 to swap the consequent disjuncts.
    """
    lb = ProofBuilder(sys, "pm2.36")
    s1 = lb.ref("s1", "( φ ∨ ψ ) → ( ψ ∨ φ )", ref="pm1.4", note="pm1.4")
    s2 = lb.ref("s2", "( ψ → χ ) → ( ( ψ ∨ φ ) → ( χ ∨ φ ) )", ref="pm2.38", note="pm2.38")
    res = lb.ref("res", "( ψ → χ ) → ( ( φ ∨ ψ ) → ( χ ∨ φ ) )", s1, s2, ref="syl5", note="syl5")
    return lb.build(res)


def prove_jao(sys: System) -> Proof:
    """jao: (φ → ψ) → ((χ → ψ) → ((φ ∨ χ) → ψ)).

    Exportation applied to pm3.44.
    """
    lb = ProofBuilder(sys, "jao")
    s1 = lb.ref(
        "s1",
        "( ( φ → ψ ) ∧ ( χ → ψ ) ) → ( ( φ ∨ χ ) → ψ )",
        ref="pm3.44",
        note="pm3.44",
    )
    res = lb.ref(
        "res",
        "( φ → ψ ) → ( ( χ → ψ ) → ( ( φ ∨ χ ) → ψ ) )",
        s1,
        ref="ex",
        note="ex(pm3.44)",
    )
    return lb.build(res)


def prove_jaod(sys: System) -> Proof:
    """jaod: φ→((ψ∨θ)→χ).  Hyps: φ→(ψ→χ), φ→(θ→χ).
    set.mm proof: com12 + jaoi + com12."""
    lb = ProofBuilder(sys, "jaod")
    h1 = lb.hyp("jaod.1", "φ → ( ψ → χ )")
    h2 = lb.hyp("jaod.2", "φ → ( θ → χ )")
    s1 = lb.ref("s1", "ψ → ( φ → χ )", h1, ref="com12", note="com12(jaod.1)")
    s2 = lb.ref("s2", "θ → ( φ → χ )", h2, ref="com12", note="com12(jaod.2)")
    s3 = lb.ref("s3", "( ψ ∨ θ ) → ( φ → χ )", s1, s2, ref="jaoi", note="jaoi")
    res = lb.ref("res", "φ → ( ( ψ ∨ θ ) → χ )", s3, ref="com12", note="com12(s3)")
    return lb.build(res)


def prove_jaao(sys: System) -> Proof:
    """jaao: (φ ∧ θ) → ((ψ ∨ τ) → χ).

    Hyps: φ → (ψ → χ), θ → (τ → χ).
    Join antecedents with an OR consequent.
    set.mm proof: adantr + adantl + jaod.
    """
    lb = ProofBuilder(sys, "jaao")
    h1 = lb.hyp("jaao.1", "φ → ( ψ → χ )")
    h2 = lb.hyp("jaao.2", "θ → ( τ → χ )")

    s1 = lb.ref(
        "s1",
        "( φ ∧ θ ) → ( ψ → χ )",
        h1,
        ref="adantr",
        note="adantr(jaao.1)",
    )
    s2 = lb.ref(
        "s2",
        "( φ ∧ θ ) → ( τ → χ )",
        h2,
        ref="adantl",
        note="adantl(jaao.2)",
    )
    res = lb.ref(
        "res",
        "( φ ∧ θ ) → ( ( ψ ∨ τ ) → χ )",
        s1,
        s2,
        ref="jaod",
        note="jaod(s1, s2)",
    )
    return lb.build(res)


def prove_jaoa(sys: System) -> Proof:
    """jaoa: ( φ ∨ θ ) → ( ( ψ ∧ τ ) → χ ).

    Join antecedents with an OR, inner AND.
    set.mm proof: adantrd + adantld + jaoi.
    """
    lb = ProofBuilder(sys, "jaoa")
    h1 = lb.hyp("jaoa.1", "φ → ( ψ → χ )")
    h2 = lb.hyp("jaoa.2", "θ → ( τ → χ )")

    s1 = lb.ref(
        "s1",
        "φ → ( ( ψ ∧ τ ) → χ )",
        h1,
        ref="adantrd",
        note="adantrd(jaoa.1)",
    )
    s2 = lb.ref(
        "s2",
        "θ → ( ( ψ ∧ τ ) → χ )",
        h2,
        ref="adantld",
        note="adantld(jaoa.2)",
    )
    res = lb.ref(
        "res",
        "( φ ∨ θ ) → ( ( ψ ∧ τ ) → χ )",
        s1,
        s2,
        ref="jaoi",
        note="jaoi(s1, s2)",
    )
    return lb.build(res)


def prove_mpjaod(sys: System) -> Proof:
    """mpjaod: φ → χ.  Hyps: φ → ( ψ → χ ), φ → ( θ → χ ), φ → ( ψ ∨ θ ).

    Modus ponens combined with jaod.
    set.mm proof: wo + jaod + mpd.
    """
    lb = ProofBuilder(sys, "mpjaod")
    h1 = lb.hyp("mpjaod.1", "φ → ( ψ → χ )")
    h2 = lb.hyp("mpjaod.2", "φ → ( θ → χ )")
    h3 = lb.hyp("mpjaod.3", "φ → ( ψ ∨ θ )")
    s1 = lb.ref("s1", "φ → ( ( ψ ∨ θ ) → χ )", h1, h2, ref="jaod", note="jaod")
    res = lb.ref("res", "φ → χ", h3, s1, ref="mpd", note="mpd")
    return lb.build(res)


def prove_jaodan(sys: System) -> Proof:
    r"""jaodan: ( ph /\ ( ps \/ th ) ) -> ch.  Hyps: ( ph /\ ps ) -> ch, ( ph /\ th ) -> ch.

    Inference joining the consequents of two conjunctive antecedents.
    set.mm proof: wo + ex + jaod + imp.
    """
    lb = ProofBuilder(sys, "jaodan")
    h1 = lb.hyp("jaodan.1", r"( ph /\ ps ) -> ch")
    h2 = lb.hyp("jaodan.2", r"( ph /\ th ) -> ch")
    s1 = lb.ref("s1", "ph -> ( ps -> ch )", h1, ref="ex", note="ex(jaodan.1)")
    s2 = lb.ref("s2", "ph -> ( th -> ch )", h2, ref="ex", note="ex(jaodan.2)")
    s3 = lb.ref("s3", r"ph -> ( ( ps \/ th ) -> ch )", s1, s2, ref="jaod", note="jaod")
    res = lb.ref("res", r"( ph /\ ( ps \/ th ) ) -> ch", s3, ref="imp", note="imp")
    return lb.build(res)


def prove_mpjaodan(sys: System) -> Proof:
    r"""mpjaodan: ph -> ch.  Hyps: ( ph /\ ps ) -> ch, ( ph /\ th ) -> ch, ph -> ( ps \/ th ).

    Inference joining the consequents of two conjunctive antecedents,
    with a disjunctive third antecedent.
    set.mm proof: wo + jaodan + mpdan.
    """
    lb = ProofBuilder(sys, "mpjaodan")
    h1 = lb.hyp("mpjaodan.1", r"( ph /\ ps ) -> ch")
    h2 = lb.hyp("mpjaodan.2", r"( ph /\ th ) -> ch")
    h3 = lb.hyp("mpjaodan.3", r"ph -> ( ps \/ th )")
    s1 = lb.ref("s1", r"( ph /\ ( ps \/ th ) ) -> ch", h1, h2, ref="jaodan", note="jaodan")
    res = lb.ref("res", "ph -> ch", h3, s1, ref="mpdan", note="mpdan")

    return lb.build(res)


def prove_mpjao3dan(sys: System) -> Proof:
    r"""mpjao3dan: φ → χ.  Hyps: ( φ ∧ ψ ) → χ, ( φ ∧ θ ) → χ, ( φ ∧ τ ) → χ, φ → ( ψ ∨ θ ∨ τ ).

    Inference joining the consequents of three conjunctive antecedents,
    with a disjunctive fourth antecedent.
    set.mm proof: w3o + 3jaodan + mpdan.
    """
    lb = ProofBuilder(sys, "mpjao3dan")
    h1 = lb.hyp("mpjao3dan.1", "( φ ∧ ψ ) → χ")
    h2 = lb.hyp("mpjao3dan.2", "( φ ∧ θ ) → χ")
    h3 = lb.hyp("mpjao3dan.3", "( φ ∧ τ ) → χ")
    h4 = lb.hyp("mpjao3dan.4", "φ → ( ψ ∨ θ ∨ τ )")
    s1 = lb.ref("s1", "( φ ∧ ( ψ ∨ θ ∨ τ ) ) → χ", h1, h2, h3, ref="3jaodan", note="3jaodan")
    res = lb.ref("res", "φ → χ", h4, s1, ref="mpdan", note="mpdan")

    return lb.build(res)


# ============================================================
# pm2.621 (under df-or = pm2.61)

# ============================================================


def prove_jaoi(sys: System) -> Proof:
    """jaoi: (φ ∨ χ) → ψ.  Hyps: φ→ψ, χ→ψ.
    Under df-or: (~φ→χ)→ψ.
    Proof: con3 on both hyps, compose via imim1+syl6+pm2.65+notnotr.
    """
    lb = ProofBuilder(sys, "jaoi")
    h1 = lb.hyp("jaoi.1", "φ → ψ")
    h2 = lb.hyp("jaoi.2", "χ → ψ")
    # Under df-or the goal is ( ¬ φ → χ ) → ψ, i.e. ja with φ:=¬ φ, ψ:=χ.
    # ja's first hypothesis is ¬ φ → χ = ¬ ¬ φ → ψ, obtained by lifting h1
    # through notnotr.
    s1 = lb.ref("s1", "¬ ¬ φ → φ", ref="notnotr", note="notnotr")
    s2 = lb.ref("s2", "¬ ¬ φ → ψ", s1, h1, ref="syl", note="syl(notnotr, jaoi.1)")
    s3 = lb.ref("s3", "( ¬ φ → χ ) → ψ", s2, h2, ref="ja", note="ja(s2, jaoi.2)")
    df_or = lb.ref(
        "df_or",
        "( φ ∨ χ ) ↔ ( ¬ φ → χ )",
        ref="df-or",
        note="df-or",
    )
    forward = lb.ref(
        "forward",
        "( φ ∨ χ ) → ( ¬ φ → χ )",
        df_or,
        ref="biimpi",
        note="biimpi",
    )
    res = lb.ref("res", "( φ ∨ χ ) → ψ", forward, s3, ref="syl", note="syl")
    return lb.build(res)


def prove_jaoi2(sys: System) -> Proof:
    """jaoi2: ( φ ∨ χ ) → ψ.  Hyp: ( φ ∨ ( ¬ φ ∧ χ ) ) → ψ.

    Variant of jaoi.  Reduce left disjunct to a case analysis via
    excluded middle.
    """
    lb = ProofBuilder(sys, "jaoi2")
    h = lb.hyp("jaoi2.1", "( φ ∨ ( ¬ φ ∧ χ ) ) → ψ")
    s1 = lb.ref(
        "s1",
        "( φ ∨ χ ) ↔ ( φ ∨ ( ¬ φ ∧ χ ) )",
        ref="pm5.63",
        note="pm5.63",
    )
    res = lb.ref(
        "res",
        "( φ ∨ χ ) → ψ",
        s1,
        h,
        ref="sylbi",
        note="sylbi(pm5.63, jaoi2.1)",
    )
    return lb.build(res)


def prove_jaoi3(sys: System) -> Proof:
    """jaoi3: (φ ∨ χ) → ψ.  Hyps: φ→ψ, (¬φ ∧ χ)→ψ.

    Combine jaoi then jaoi2.
    """
    lb = ProofBuilder(sys, "jaoi3")
    h1 = lb.hyp("jaoi3.1", "φ → ψ")
    h2 = lb.hyp("jaoi3.2", "( ¬ φ ∧ χ ) → ψ")
    s1 = lb.ref(
        "s1",
        "( φ ∨ ( ¬ φ ∧ χ ) ) → ψ",
        h1,
        h2,
        ref="jaoi",
        note="jaoi(jaoi3.1, jaoi3.2)",
    )
    res = lb.ref(
        "res",
        "( φ ∨ χ ) → ψ",
        s1,
        ref="jaoi2",
        note="jaoi2(s1)",
    )
    return lb.build(res)


def prove_jaoian(sys: System) -> Proof:
    r"""jaoian: ( ( ph \/ th ) /\ ps ) -> ch.  Hyps: ( ph /\ ps ) -> ch, ( th /\ ps ) -> ch.

    Inference joining the consequents of two conjunctive antecedents
    with a common conjunct.
    set.mm proof: ex + jaoi + imp.
    """
    lb = ProofBuilder(sys, "jaoian")
    h1 = lb.hyp("jaoian.1", r"( ph /\ ps ) -> ch")
    h2 = lb.hyp("jaoian.2", r"( th /\ ps ) -> ch")
    s1 = lb.ref("s1", "ph -> ( ps -> ch )", h1, ref="ex", note="ex(jaoian.1)")
    s2 = lb.ref("s2", "th -> ( ps -> ch )", h2, ref="ex", note="ex(jaoian.2)")
    s3 = lb.ref("s3", r"( ph \/ th ) -> ( ps -> ch )", s1, s2, ref="jaoi", note="jaoi")
    res = lb.ref("res", r"( ( ph \/ th ) /\ ps ) -> ch", s3, ref="imp", note="imp")
    return lb.build(res)


def prove_ccase(sys: System) -> Proof:
    r"""ccase: ( ( ( ph \/ ch ) /\ ( ps \/ th ) ) -> ta ).

    Inference combining two pairs of conjunctive antecedents.
    set.mm proof: jaoian + jaodan.
    """
    lb = ProofBuilder(sys, "ccase")
    h1 = lb.hyp("ccase.1", r"( ph /\ ps ) -> ta")
    h2 = lb.hyp("ccase.2", r"( ch /\ ps ) -> ta")
    h3 = lb.hyp("ccase.3", r"( ph /\ th ) -> ta")
    h4 = lb.hyp("ccase.4", r"( ch /\ th ) -> ta")

    s1 = lb.ref(
        "s1", r"( ( ph \/ ch ) /\ ps ) -> ta", h1, h2, ref="jaoian", note="jaoian(ccase.1, ccase.2)"
    )
    s2 = lb.ref(
        "s2", r"( ( ph \/ ch ) /\ th ) -> ta", h3, h4, ref="jaoian", note="jaoian(ccase.3, ccase.4)"
    )
    res = lb.ref(
        "res", r"( ( ph \/ ch ) /\ ( ps \/ th ) ) -> ta", s1, s2, ref="jaodan", note="jaodan"
    )
    return lb.build(res)


def prove_ccase2(sys: System) -> Proof:
    """ccase2: ( ( φ ∨ χ ) ∧ ( ψ ∨ θ ) ) → τ.

    Inference combining two pairs of conjunctive antecedents.
    set.mm proof: adantr + adantl + ccase.
    """
    lb = ProofBuilder(sys, "ccase2")
    h1 = lb.hyp("ccase2.1", "( φ ∧ ψ ) → τ")
    h2 = lb.hyp("ccase2.2", "χ → τ")
    h3 = lb.hyp("ccase2.3", "θ → τ")

    s1 = lb.ref("s1", "( χ ∧ ψ ) → τ", h2, ref="adantr", note="adantr(ccase2.2)")
    s2 = lb.ref("s2", "( φ ∧ θ ) → τ", h3, ref="adantl", note="adantl(ccase2.3)")
    s3 = lb.ref("s3", "( χ ∧ θ ) → τ", h3, ref="adantl", note="adantl(ccase2.3)")
    res = lb.ref("res", "( ( φ ∨ χ ) ∧ ( ψ ∨ θ ) ) → τ", h1, s1, s2, s3, ref="ccase", note="ccase")
    return lb.build(res)


def prove_ccased(sys: System) -> Proof:
    r"""ccased: ph -> ( ( ( ps \/ th ) /\ ( ch \/ ta ) ) -> et ).

    Deduction form of ccase.
    set.mm proof: com12 + ccase.
    """
    lb = ProofBuilder(sys, "ccased")
    h1 = lb.hyp("ccased.1", r"ph -> ( ( ps /\ ch ) -> et )")
    h2 = lb.hyp("ccased.2", r"ph -> ( ( th /\ ch ) -> et )")
    h3 = lb.hyp("ccased.3", r"ph -> ( ( ps /\ ta ) -> et )")
    h4 = lb.hyp("ccased.4", r"ph -> ( ( th /\ ta ) -> et )")

    s1 = lb.ref("s1", r"( ps /\ ch ) -> ( ph -> et )", h1, ref="com12", note="com12(ccased.1)")
    s2 = lb.ref("s2", r"( th /\ ch ) -> ( ph -> et )", h2, ref="com12", note="com12(ccased.2)")
    s3 = lb.ref("s3", r"( ps /\ ta ) -> ( ph -> et )", h3, ref="com12", note="com12(ccased.3)")
    s4 = lb.ref("s4", r"( th /\ ta ) -> ( ph -> et )", h4, ref="com12", note="com12(ccased.4)")

    s5 = lb.ref(
        "s5",
        r"( ( ps \/ th ) /\ ( ch \/ ta ) ) -> ( ph -> et )",
        s1,
        s2,
        s3,
        s4,
        ref="ccase",
        note="ccase",
    )
    res = lb.ref(
        "res",
        r"ph -> ( ( ( ps \/ th ) /\ ( ch \/ ta ) ) -> et )",
        s5,
        ref="com12",
        note="com12(s5)",
    )
    return lb.build(res)


def prove_cases2(sys: System) -> Proof:
    """cases2: ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) ) ↔ ( ( φ → ψ ) ∧ ( ¬ φ → χ ) ).

    Case elimination: a disjunction of case analyses is equivalent to a
    conjunction of implications.
    """
    lb = ProofBuilder(sys, "cases2")

    # dedlema: φ → ( ψ ↔ ( ( ψ ∧ φ ) ∨ ( χ ∧ ¬ φ ) ) )
    s_dedlema = lb.ref(
        "s_dedlema",
        "φ → ( ψ ↔ ( ( ψ ∧ φ ) ∨ ( χ ∧ ¬ φ ) ) )",
        ref="dedlema",
        note="dedlema",
    )

    # pm5.74i: ( φ → ψ ) ↔ ( φ → ( ( ψ ∧ φ ) ∨ ( χ ∧ ¬ φ ) ) )
    s_74i1 = lb.ref(
        "s_74i1",
        "( φ → ψ ) ↔ ( φ → ( ( ψ ∧ φ ) ∨ ( χ ∧ ¬ φ ) ) )",
        s_dedlema,
        ref="pm5.74i",
        note="pm5.74i(dedlema)",
    )

    # dedlemb: ¬ φ → ( χ ↔ ( ( ψ ∧ φ ) ∨ ( χ ∧ ¬ φ ) ) )
    s_dedlemb = lb.ref(
        "s_dedlemb",
        "¬ φ → ( χ ↔ ( ( ψ ∧ φ ) ∨ ( χ ∧ ¬ φ ) ) )",
        ref="dedlemb",
        note="dedlemb",
    )

    # pm5.74i: ( ¬ φ → χ ) ↔ ( ¬ φ → ( ( ψ ∧ φ ) ∨ ( χ ∧ ¬ φ ) ) )
    s_74i2 = lb.ref(
        "s_74i2",
        "( ¬ φ → χ ) ↔ ( ¬ φ → ( ( ψ ∧ φ ) ∨ ( χ ∧ ¬ φ ) ) )",
        s_dedlemb,
        ref="pm5.74i",
        note="pm5.74i(dedlemb)",
    )

    # anbi12i: combine the two biconditionals
    s_anbi12i = lb.ref(
        "s_anbi12i",
        "( ( φ → ψ ) ∧ ( ¬ φ → χ ) ) ↔ ( ( φ → ( ( ψ ∧ φ ) ∨ ( χ ∧ ¬ φ ) ) ) ∧ ( ¬ φ → ( ( ψ ∧ φ ) ∨ ( χ ∧ ¬ φ ) ) ) )",
        s_74i1,
        s_74i2,
        ref="anbi12i",
        note="anbi12i",
    )

    # pm4.83: ( ( φ → X ) ∧ ( ¬ φ → X ) ) ↔ X  where X = ( ( ψ ∧ φ ) ∨ ( χ ∧ ¬ φ ) )
    s_pm4_83 = lb.ref(
        "s_pm4_83",
        "( ( φ → ( ( ψ ∧ φ ) ∨ ( χ ∧ ¬ φ ) ) ) ∧ ( ¬ φ → ( ( ψ ∧ φ ) ∨ ( χ ∧ ¬ φ ) ) ) ) ↔ ( ( ψ ∧ φ ) ∨ ( χ ∧ ¬ φ ) )",
        ref="pm4.83",
        note="pm4.83",
    )

    # ancom: ( φ ∧ ψ ) ↔ ( ψ ∧ φ )
    s_ancom1 = lb.ref(
        "s_ancom1",
        "( φ ∧ ψ ) ↔ ( ψ ∧ φ )",
        ref="ancom",
        note="ancom",
    )

    # ancom: ( ¬ φ ∧ χ ) ↔ ( χ ∧ ¬ φ )
    s_ancom2 = lb.ref(
        "s_ancom2",
        "( ¬ φ ∧ χ ) ↔ ( χ ∧ ¬ φ )",
        ref="ancom",
        note="ancom",
    )

    # orbi12i: combine the two ancom biconditionals
    s_orbi12i = lb.ref(
        "s_orbi12i",
        "( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) ) ↔ ( ( ψ ∧ φ ) ∨ ( χ ∧ ¬ φ ) )",
        s_ancom1,
        s_ancom2,
        ref="orbi12i",
        note="orbi12i",
    )

    # 3bitr4ri: chain s_pm4_83 (ph↔ps), s_anbi12i (ch↔ph), s_orbi12i (th↔ps) → th↔ch
    res = lb.ref(
        "res",
        "( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) ) ↔ ( ( φ → ψ ) ∧ ( ¬ φ → χ ) )",
        s_pm4_83,
        s_anbi12i,
        s_orbi12i,
        ref="3bitr4ri",
        note="3bitr4ri",
    )

    return lb.build(res)


def prove_cases2ALT(sys: System) -> Proof:
    """cases2ALT: ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) ) ↔ ( ( φ → ψ ) ∧ ( ¬ φ → χ ) ).

    Alternate proof of cases2, not using dedlema or dedlemb.
    (Contributed by BJ, 6-Apr-2019.)  (Proof shortened by Wolf Lammen,
    2-Jan-2020.)  (Proof modification is discouraged.)
    """
    lb = ProofBuilder(sys, "cases2ALT")

    # Step 1: pm3.4
    s1 = lb.ref("s1", "( φ ∧ ψ ) → ( φ → ψ )", ref="pm3.4", note="pm3.4")

    # Step 2: pm2.24
    s2 = lb.ref("s2", "φ → ( ¬ φ → χ )", ref="pm2.24", note="pm2.24")

    # Step 3: adantr
    s3 = lb.ref("s3", "( φ ∧ ψ ) → ( ¬ φ → χ )", s2, ref="adantr", note="adantr")

    # Step 4: jca
    s4 = lb.ref(
        "s4",
        "( φ ∧ ψ ) → ( ( φ → ψ ) ∧ ( ¬ φ → χ ) )",
        s1,
        s3,
        ref="jca",
        note="jca",
    )

    # Step 5: pm2.21
    s5 = lb.ref("s5", "¬ φ → ( φ → ψ )", ref="pm2.21", note="pm2.21")

    # Step 6: adantr
    s6 = lb.ref("s6", "( ¬ φ ∧ χ ) → ( φ → ψ )", s5, ref="adantr", note="adantr")

    # Step 7: pm3.4
    s7 = lb.ref("s7", "( ¬ φ ∧ χ ) → ( ¬ φ → χ )", ref="pm3.4", note="pm3.4")

    # Step 8: jca
    s8 = lb.ref(
        "s8",
        "( ¬ φ ∧ χ ) → ( ( φ → ψ ) ∧ ( ¬ φ → χ ) )",
        s6,
        s7,
        ref="jca",
        note="jca",
    )

    # Step 9: jaoi
    s9 = lb.ref(
        "s9",
        "( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) ) → ( ( φ → ψ ) ∧ ( ¬ φ → χ ) )",
        s4,
        s8,
        ref="jaoi",
        note="jaoi",
    )

    # Step 10: pm2.27
    s10 = lb.ref("s10", "φ → ( ( φ → ψ ) → ψ )", ref="pm2.27", note="pm2.27")

    # Step 11: imdistani
    s11 = lb.ref("s11", "( φ ∧ ( φ → ψ ) ) → ( φ ∧ ψ )", s10, ref="imdistani", note="imdistani")

    # Step 12: orcd
    s12 = lb.ref(
        "s12",
        "( φ ∧ ( φ → ψ ) ) → ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) )",
        s11,
        ref="orcd",
        note="orcd",
    )

    # Step 13: adantrr
    s13 = lb.ref(
        "s13",
        "( φ ∧ ( ( φ → ψ ) ∧ ( ¬ φ → χ ) ) ) → ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) )",
        s12,
        ref="adantrr",
        note="adantrr",
    )

    # Step 14: pm2.27
    s14 = lb.ref("s14", "¬ φ → ( ( ¬ φ → χ ) → χ )", ref="pm2.27", note="pm2.27")

    # Step 15: imdistani
    s15 = lb.ref(
        "s15",
        "( ¬ φ ∧ ( ¬ φ → χ ) ) → ( ¬ φ ∧ χ )",
        s14,
        ref="imdistani",
        note="imdistani",
    )

    # Step 16: olcd
    s16 = lb.ref(
        "s16",
        "( ¬ φ ∧ ( ¬ φ → χ ) ) → ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) )",
        s15,
        ref="olcd",
        note="olcd",
    )

    # Step 17: adantrl
    s17 = lb.ref(
        "s17",
        "( ¬ φ ∧ ( ( φ → ψ ) ∧ ( ¬ φ → χ ) ) ) → ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) )",
        s16,
        ref="adantrl",
        note="adantrl",
    )

    # Step 18: pm2.61ian
    s18 = lb.ref(
        "s18",
        "( ( φ → ψ ) ∧ ( ¬ φ → χ ) ) → ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) )",
        s13,
        s17,
        ref="pm2.61ian",
        note="pm2.61ian",
    )

    # Step 19: impbii
    res = lb.ref(
        "res",
        "( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) ) ↔ ( ( φ → ψ ) ∧ ( ¬ φ → χ ) )",
        s9,
        s18,
        ref="impbii",
        note="impbii",
    )

    return lb.build(res)


def prove_jao1i(sys: System) -> Proof:
    """jao1i: ( φ ∨ ψ ) → ( χ → φ ).  Hyp: ψ → ( χ → φ ).

    Inference form of jaoi: ax-1 gives φ→(χ→φ);
    with jao1i.1 (ψ→(χ→φ)), jaoi yields (φ∨ψ)→(χ→φ).
    set.mm proof: ax-1 jaoi.
    """
    lb = ProofBuilder(sys, "jao1i")
    h1 = lb.hyp("jao1i.1", "ψ → ( χ → φ )")
    s1 = lb.ref("s1", "φ → ( χ → φ )", ref="ax-1", note="ax-1")
    res = lb.ref("res", "( φ ∨ ψ ) → ( χ → φ )", s1, h1, ref="jaoi", note="jaoi(ax-1, jao1i.1)")
    return lb.build(res)


def prove_olc(sys: System) -> Proof:
    """olc: φ → (ψ ∨ φ).  From orc(pm2.24) + pm1.4 via syl."""
    lb = ProofBuilder(sys, "olc")
    s1 = lb.ref("s1", "φ → ( φ ∨ ψ )", ref="orc", note="orc")
    s2 = lb.ref("s2", "( φ ∨ ψ ) → ( ψ ∨ φ )", ref="pm1.4", note="pm1.4")
    res = lb.ref("res", "φ → ( ψ ∨ φ )", s1, s2, ref="syl", note="syl(orc, pm1.4)")
    return lb.build(res)


def prove_pm2_41(sys: System) -> Proof:
    r"""pm2.41: ( ψ \/ ( φ \/ ψ ) ) → ( φ \/ ψ ).

    Theorem *2.41 of [WhiteheadRussell] p. 106.
    (Contributed by NM, 3-Jan-2005.)
    set.mm proof: olc + id + jaoi.
    """
    lb = ProofBuilder(sys, "pm2.41")
    s1 = lb.ref("s1", r"ψ → ( φ \/ ψ )", ref="olc", note="olc")
    s2 = lb.ref("s2", r"( φ \/ ψ ) → ( φ \/ ψ )", ref="id", note="id")
    res = lb.ref("res", r"( ψ \/ ( φ \/ ψ ) ) → ( φ \/ ψ )", s1, s2, ref="jaoi", note="jaoi")
    return lb.build(res)


def prove_pm2_07(sys: System) -> Proof:
    r"""pm2.07: φ → ( φ \/ φ ).

    Theorem *2.07 of [WhiteheadRussell] p. 101.
    (Contributed by NM, 3-Jan-2005.)
    set.mm proof: olc.
    """
    lb = ProofBuilder(sys, "pm2.07")
    res = lb.ref("res", r"( φ → ( φ \/ φ ) )", ref="olc", note="olc")
    return lb.build(res)


def prove_pm2_3(sys: System) -> Proof:
    r"""pm2.3: ( ( ph \/ ( ps \/ ch ) ) -> ( ph \/ ( ch \/ ps ) ) ).

    Swap the disjuncts of the second disjunct.
    (Contributed by NM, 12-Mar-1993.)
    set.mm proof: pm1.4 orim2i.
    """
    lb = ProofBuilder(sys, "pm2.3")
    s1 = lb.ref("s1", r"( ps \/ ch ) -> ( ch \/ ps )", ref="pm1.4", note="pm1.4")
    res = lb.ref(
        "res", r"( ph \/ ( ps \/ ch ) ) -> ( ph \/ ( ch \/ ps ) )", s1, ref="orim2i", note="orim2i"
    )
    return lb.build(res)


def prove_pm2_31(sys: System) -> Proof:
    r"""pm2.31: ( ( ph \/ ( ps \/ ch ) ) -> ( ( ph \/ ps ) \/ ch ) ).

    Associativity of disjunction, reverse direction.
    (Contributed by NM, 27-Dec-1992.)
    set.mm proof: wo orass biimpri.
    """
    lb = ProofBuilder(sys, "pm2.31")
    s1 = lb.ref(
        "s1", r"( ( ph \/ ps ) \/ ch ) <-> ( ph \/ ( ps \/ ch ) )", ref="orass", note="orass"
    )
    res = lb.ref(
        "res",
        r"( ph \/ ( ps \/ ch ) ) -> ( ( ph \/ ps ) \/ ch )",
        s1,
        ref="biimpri",
        note="biimpri",
    )

    return lb.build(res)


def prove_pm2_32(sys: System) -> Proof:
    r"""pm2.32: ( ( ( ph \/ ps ) \/ ch ) -> ( ph \/ ( ps \/ ch ) ) ).

    Associativity of disjunction, forward direction.
    (Contributed by NM, 27-Dec-1992.)
    set.mm proof: orass biimpi.
    """
    lb = ProofBuilder(sys, "pm2.32")
    s1 = lb.ref(
        "s1", r"( ( ph \/ ps ) \/ ch ) <-> ( ph \/ ( ps \/ ch ) )", ref="orass", note="orass"
    )
    res = lb.ref(
        "res", r"( ( ph \/ ps ) \/ ch ) -> ( ph \/ ( ps \/ ch ) )", s1, ref="biimpi", note="biimpi"
    )

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


# ============================================================
# pm2.53, pm2.54 (trivial under df-or)
# ============================================================


def prove_pm2_53(sys: System) -> Proof:
    """pm2.53: (φ ∨ ψ) → (¬ φ → ψ).

    Theorem *2.53 of [WhiteheadRussell] p. 107.
    (Contributed by NM, 3-Jan-2005.)
    This is the forward direction of the disjunction definition.
    """
    lb = ProofBuilder(sys, "pm2.53")
    definition = lb.ref(
        "definition",
        "( φ ∨ ψ ) ↔ ( ¬ φ → ψ )",
        ref="df-or",
        note="df-or",
    )
    res = lb.ref(
        "res",
        "( φ ∨ ψ ) → ( ¬ φ → ψ )",
        definition,
        ref="biimpi",
        note="biimpi df-or",
    )
    return lb.build(res)


def prove_pm2_8(sys: System) -> Proof:
    """pm2.8: (φ ∨ ψ) → ((¬ψ ∨ χ) → (φ ∨ χ)).

    Theorem *2.8 of [WhiteheadRussell] p. 108.
    set.mm proof: pm2.53 con1d orim1d.
    Under df-or: (¬ φ → ψ) → ((¬¬ψ → χ) → (¬ φ → χ)).
    Proof: notnot: ψ → ¬¬ψ.
           imim2 + mp: (¬ φ → ψ) → (¬ φ → ¬¬ψ).
           imim1: (¬ φ → ¬¬ψ) → ((¬¬ψ → χ) → (¬ φ → χ)).
           syl chains them.
    """
    lb = ProofBuilder(sys, "pm2.8")
    s_notnot = lb.ref("s_notnot", "ψ → ¬ ¬ ψ", ref="notnot", note="notnot")
    s_imim2 = lb.ref(
        "s_imim2",
        "( ψ → ¬ ¬ ψ ) → ( ( ¬ φ → ψ ) → ( ¬ φ → ¬ ¬ ψ ) )",
        ref="imim2",
        note="imim2",
    )
    s1 = lb.mp("s1", s_notnot, s_imim2, note="MP notnot imim2")
    s_imim1 = lb.ref(
        "s_imim1",
        "( ¬ φ → ¬ ¬ ψ ) → ( ( ¬ ¬ ψ → χ ) → ( ¬ φ → χ ) )",
        ref="imim1",
        note="imim1",
    )
    res = lb.ref(
        "res",
        "( ¬ φ → ψ ) → ( ( ¬ ¬ ψ → χ ) → ( ¬ φ → χ ) )",
        s1,
        s_imim1,
        ref="syl",
        note="syl(s1, imim1)",
    )
    return lb.build(res)


def prove_pm2_621(sys: System) -> Proof:
    """Theorem *2.621 of [WhiteheadRussell] p. 107.
    ( φ → ψ ) → ( ( φ ∨ ψ ) → ψ ).
    (Contributed by NM, 3-Jan-2005.)
    set.mm proof: id + idd + jaod.
    Under df-or: ( φ → ψ ) → ( ( ¬ φ → ψ ) → ψ ).
    This is exactly pm2.61."""
    lb = ProofBuilder(sys, "pm2.621")
    expanded = lb.ref("expanded", "( φ → ψ ) → ( ( ¬ φ → ψ ) → ψ )", ref="pm2.61", note="pm2.61")
    df_or = lb.ref("df_or", "( φ ∨ ψ ) ↔ ( ¬ φ → ψ )", ref="df-or", note="df-or")
    forward = lb.ref("forward", "( φ ∨ ψ ) → ( ¬ φ → ψ )", df_or, ref="biimpi", note="biimpi")
    res = lb.ref(
        "res",
        "( φ → ψ ) → ( ( φ ∨ ψ ) → ψ )",
        forward,
        expanded,
        ref="syl5",
        note="syl5",
    )
    return lb.build(res)


def prove_pm2_62(sys: System) -> Proof:
    """pm2.62: (φ ∨ ψ) → ((φ → ψ) → ψ).

    Theorem *2.62 of [WhiteheadRussell] p. 107.
    (Contributed by NM, 3-Jan-2005.)
    set.mm proof: pm2.621 + com12.
    """
    lb = ProofBuilder(sys, "pm2.62")
    s1 = lb.ref("s1", "( φ → ψ ) → ( ( φ ∨ ψ ) → ψ )", ref="pm2.621", note="pm2.621")
    res = lb.ref("res", "( φ ∨ ψ ) → ( ( φ → ψ ) → ψ )", s1, ref="com12", note="com12")
    return lb.build(res)


def prove_pm2_67(sys: System) -> Proof:
    """Theorem *2.67 of [WhiteheadRussell] p. 107.
    ( ( ( φ ∨ ψ ) → ψ ) → ( φ → ψ ) )
    (Contributed by NM, 3-Jan-2005.)
    """
    lb = ProofBuilder(sys, "pm2.67")
    h1 = lb.hyp("pm2.67.1", "( ( ¬ φ → ψ ) → ψ )")
    s1 = lb.ref("s1", "¬ φ → ( φ → ψ )", ref="pm2.21", note="pm2.21")
    s2 = lb.ref("s2", "φ → ( ¬ φ → ψ )", s1, ref="com12", note="com12(s1)")
    res = lb.ref("res", "φ → ψ", s2, h1, ref="syl", note="syl(s2, h1)")
    return lb.build(res)


def prove_pm2_67_2(sys: System) -> Proof:
    """Theorem *2.67-2 of [WhiteheadRussell] p. 107.
    ( ( φ ∨ χ ) → ψ ) → ( φ → ψ ).
    (Contributed by NM, 3-Jan-2005.)
    set.mm proof: orc + imim1i.
    Under df-or: ( ( ¬ φ → χ ) → ψ ) → ( φ → ψ ).
    Proof: pm2.24 + imim1 via mp."""
    lb = ProofBuilder(sys, "pm2.67-2")
    s1 = lb.ref("s1", "φ → ( φ ∨ χ )", ref="orc", note="orc")
    res = lb.ref(
        "res",
        "( ( φ ∨ χ ) → ψ ) → ( φ → ψ )",
        s1,
        ref="imim1i",
        note="imim1i(orc)",
    )
    return lb.build(res)


def prove_pm2_68(sys: System) -> Proof:
    """Theorem *2.68 of [WhiteheadRussell] p. 108.
    ( ( ( φ → ψ ) → ψ ) → ( φ ∨ ψ ) )
    (Contributed by NM, 3-Jan-2005.)
    set.mm proof: jarl orrd.
    """
    lb = ProofBuilder(sys, "pm2.68")
    s1 = lb.ref("s1", "( ( φ → ψ ) → ψ ) → ( ¬ φ → ψ )", ref="jarl", note="jarl")
    res = lb.ref("res", "( ( φ → ψ ) → ψ ) → ( φ ∨ ψ )", s1, ref="orrd", note="orrd")
    return lb.build(res)


def prove_dedlema(sys: System) -> Proof:
    """dedlema: φ → (ψ ↔ ((ψ ∧ φ) ∨ (χ ∧ ¬ φ))).

    Deduction lemma for case elimination.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "dedlema")

    # Forward direction: φ → (ψ → ((ψ ∧ φ) ∨ (χ ∧ ¬ φ)))
    s_orc = lb.ref(
        "s_orc",
        "(ψ ∧ φ) → ((ψ ∧ φ) ∨ (χ ∧ ¬ φ))",
        ref="orc",
        note="orc",
    )
    s_fwd = lb.ref(
        "s_fwd",
        "φ → (ψ → ((ψ ∧ φ) ∨ (χ ∧ ¬ φ)))",
        s_orc,
        ref="expcom",
        note="expcom(orc)",
    )

    # Reverse direction: φ → (((ψ ∧ φ) ∨ (χ ∧ ¬ φ)) → ψ)
    s_simpl = lb.ref("s_simpl", "(ψ ∧ φ) → ψ", ref="simpl", note="simpl")
    s_left = lb.ref(
        "s_left",
        "φ → ((ψ ∧ φ) → ψ)",
        s_simpl,
        ref="a1i",
        note="a1i(simpl)",
    )

    s_pm2_24 = lb.ref("s_pm2_24", "φ → (¬ φ → ψ)", ref="pm2.24", note="pm2.24")
    s_right = lb.ref(
        "s_right",
        "φ → ((χ ∧ ¬ φ) → ψ)",
        s_pm2_24,
        ref="adantld",
        note="adantld(pm2.24)",
    )

    s_rev = lb.ref(
        "s_rev",
        "φ → (((ψ ∧ φ) ∨ (χ ∧ ¬ φ)) → ψ)",
        s_left,
        s_right,
        ref="jaod",
        note="jaod",
    )

    # Combine the two directions using impbid
    res = lb.ref(
        "res",
        "φ → (ψ ↔ ((ψ ∧ φ) ∨ (χ ∧ ¬ φ)))",
        s_fwd,
        s_rev,
        ref="impbid",
        note="impbid",
    )
    return lb.build(res)


def prove_dedlemb(sys: System) -> Proof:
    """dedlemb: ¬ φ → (χ ↔ ((ψ ∧ φ) ∨ (χ ∧ ¬ φ))).

    Deduction lemma for case elimination.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "dedlemb")

    # Forward direction: ¬ φ → (χ → ((ψ ∧ φ) ∨ (χ ∧ ¬ φ)))
    s_olc = lb.ref(
        "s_olc",
        "(χ ∧ ¬ φ) → ((ψ ∧ φ) ∨ (χ ∧ ¬ φ))",
        ref="olc",
        note="olc",
    )
    s_fwd = lb.ref(
        "s_fwd",
        "¬ φ → (χ → ((ψ ∧ φ) ∨ (χ ∧ ¬ φ)))",
        s_olc,
        ref="expcom",
        note="expcom(olc)",
    )

    # Reverse direction: ¬ φ → (((ψ ∧ φ) ∨ (χ ∧ ¬ φ)) → χ)
    s_pm2_21 = lb.ref(
        "s_pm2_21",
        "¬ φ → (φ → χ)",
        ref="pm2.21",
        note="pm2.21",
    )
    s_left = lb.ref(
        "s_left",
        "¬ φ → ((ψ ∧ φ) → χ)",
        s_pm2_21,
        ref="adantld",
        note="adantld(pm2.21)",
    )

    s_simpl = lb.ref("s_simpl", "(χ ∧ ¬ φ) → χ", ref="simpl", note="simpl")
    s_right = lb.ref(
        "s_right",
        "¬ φ → ((χ ∧ ¬ φ) → χ)",
        s_simpl,
        ref="a1i",
        note="a1i(simpl)",
    )

    s_rev = lb.ref(
        "s_rev",
        "¬ φ → (((ψ ∧ φ) ∨ (χ ∧ ¬ φ)) → χ)",
        s_left,
        s_right,
        ref="jaod",
        note="jaod",
    )

    # Combine the two directions using impbid
    res = lb.ref(
        "res",
        "¬ φ → (χ ↔ ((ψ ∧ φ) ∨ (χ ∧ ¬ φ)))",
        s_fwd,
        s_rev,
        ref="impbid",
        note="impbid",
    )
    return lb.build(res)


def prove_dfor2(sys: System) -> Proof:
    r"""dfor2: ( ( ph \/ ps ) <-> ( ( ph -> ps ) -> ps ) ).

    A definition of disjunction in terms of implication.
    set.mm proof: pm2.62 pm2.68 impbii.
    """
    lb = ProofBuilder(sys, "dfor2")
    s1 = lb.ref("s1", "( ph ∨ ps ) -> ( ( ph -> ps ) -> ps )", ref="pm2.62", note="pm2.62")
    s2 = lb.ref("s2", "( ( ph -> ps ) -> ps ) -> ( ph ∨ ps )", ref="pm2.68", note="pm2.68")
    res = lb.ref(
        "res", "( ( ph ∨ ps ) <-> ( ( ph -> ps ) -> ps ) )", s1, s2, ref="impbii", note="impbii"
    )
    return lb.build(res)


def prove_pm2_73(sys: System) -> Proof:
    """Theorem *2.73 of [WhiteheadRussell] p. 108.

    ( φ → ψ ) → ( ( ( φ ∨ ψ ) ∨ χ ) → ( ψ ∨ χ ) )

    (Contributed by NM, 3-Jan-2005.)
    Under df-or: ( φ → ψ ) → ( ( ¬ ( ¬ φ → ψ ) → χ ) → ( ¬ ψ → χ ) )
    Proof: pm2.61 + com12 gives pm2.621, then orim1d via con3 + imim1.
    """
    lb = ProofBuilder(sys, "pm2.73")
    s1 = lb.ref("s1", "( φ ∨ ψ ) → ( ( φ → ψ ) → ψ )", ref="pm2.62", note="pm2.62")
    s2 = lb.ref("s2", "( φ → ψ ) → ( ( φ ∨ ψ ) → ψ )", s1, ref="com12", note="com12")
    res = lb.ref(
        "res",
        "( φ → ψ ) → ( ( ( φ ∨ ψ ) ∨ χ ) → ( ψ ∨ χ ) )",
        s2,
        ref="orim1d",
        note="orim1d",
    )
    return lb.build(res)


def prove_pm2_74(sys: System) -> Proof:
    """
    pm2.74: ( ψ → φ ) → ( ( ( φ ∨ ψ ) ∨ χ ) → ( φ ∨ χ ) ).

    Theorem *2.74 of [WhiteheadRussell] p. 108.
    (Contributed by NM, 3-Jan-2005.)
    (Proof shortened by Andrew Salmon, 7-May-2011.)

    In set.mm ∨-notation: ( ( ψ → φ ) →
      ( ( ( φ ∨ ψ ) ∨ χ ) → ( φ ∨ χ ) ) ).
    """
    lb = ProofBuilder(sys, "pm2.74")
    s1 = lb.ref(
        "s1",
        "( ψ ∨ φ ) → ( ( ψ → φ ) → φ )",
        ref="pm2.62",
        note="pm2.62",
    )
    s2 = lb.ref(
        "s2",
        "( ψ → φ ) → ( ( ψ ∨ φ ) → φ )",
        s1,
        ref="com12",
        note="com12",
    )
    s3 = lb.ref(
        "s3",
        "( φ ∨ ψ ) → ( ψ ∨ φ )",
        ref="pm1.4",
        note="pm1.4",
    )
    s4 = lb.ref(
        "s4",
        "( ψ → φ ) → ( ( φ ∨ ψ ) → φ )",
        s3,
        s2,
        ref="syl5",
        note="syl5",
    )
    res = lb.ref(
        "res",
        "( ψ → φ ) → ( ( ( φ ∨ ψ ) ∨ χ ) → ( φ ∨ χ ) )",
        s4,
        ref="orim1d",
        note="orim1d",
    )
    return lb.build(res)


def prove_pm2_75(sys: System) -> Proof:
    """Theorem *2.75 of [WhiteheadRussell] p. 108.
    ( φ ∨ ψ ) → ( ( φ ∨ ( ψ → χ ) ) → ( φ ∨ χ ) )
    (Contributed by NM, 3-Jan-2005.)
    (Proof shortened by Wolf Lammen, 4-Jan-2013.)
    Under df-or: ( ¬ φ → ψ ) → ( ( ¬ φ → ( ψ → χ ) ) → ( ¬ φ → χ ) )
    Proof: A2 + com12.
    """
    lb = ProofBuilder(sys, "pm2.75")
    s1 = lb.ref(
        "s1",
        "( ¬ φ → ( ψ → χ ) ) → ( ( ¬ φ → ψ ) → ( ¬ φ → χ ) )",
        ref="ax-2",
        note="A2",
    )
    res = lb.ref(
        "res",
        "( ¬ φ → ψ ) → ( ( ¬ φ → ( ψ → χ ) ) → ( ¬ φ → χ ) )",
        s1,
        ref="com12",
        note="com12(s1)",
    )
    return lb.build(res)


def prove_pm2_76(sys: System) -> Proof:
    r"""pm2.76: ( ( ph \/ ( ps -> ch ) ) -> ( ( ph \/ ps ) -> ( ph \/ ch ) ) ).

    One direction of orimdi.  (Contributed by NM, 3-Jan-2005.)
    """
    lb = ProofBuilder(sys, "pm2.76")
    # orimdi: ( ( ph \/ ( ps -> ch ) ) <-> ( ( ph \/ ps ) -> ( ph \/ ch ) ) )
    s1 = lb.ref(
        "s1",
        r"( ( ph \/ ( ps -> ch ) ) <-> ( ( ph \/ ps ) -> ( ph \/ ch ) ) )",
        ref="orimdi",
        note="orimdi",
    )
    # biimpi: forward direction
    res = lb.ref(
        "res",
        r"( ( ph \/ ( ps -> ch ) ) -> ( ( ph \/ ps ) -> ( ph \/ ch ) ) )",
        s1,
        ref="biimpi",
        note="biimpi",
    )
    return lb.build(res)


def prove_pm2_81(sys: System) -> Proof:
    """pm2.81: (ψ → (χ → θ)) → ((φ ∨ ψ) → ((φ ∨ χ) → (φ ∨ θ))).

    Theorem *2.81 of [WhiteheadRussell] p. 108.
    (Contributed by NM, 3-Jan-2005.)

    set.mm proof: orim2 pm2.76 syl6.
    Under df-or: (ψ→(χ→θ))→((¬ φ→ψ)→((¬ φ→χ)→(¬ φ→θ))).
    imim2: (ψ→(χ→θ))→((¬ φ→ψ)→(¬ φ→(χ→θ))).
    A2: (¬ φ→(χ→θ))→((¬ φ→χ)→(¬ φ→θ)).
    syl6 chains them.
    """
    lb = ProofBuilder(sys, "pm2.81")
    s_imim2 = lb.ref(
        "s_imim2",
        "( ( ψ → ( χ → θ ) ) → ( ( ¬ φ → ψ ) → ( ¬ φ → ( χ → θ ) ) ) )",
        ref="imim2",
        note="imim2",
    )
    s_A2 = lb.ref(
        "s_A2",
        "( ( ¬ φ → ( χ → θ ) ) → ( ( ¬ φ → χ ) → ( ¬ φ → θ ) ) )",
        ref="ax-2",
        note="A2",
    )
    res = lb.ref(
        "res",
        "( ( ψ → ( χ → θ ) ) → ( ( ¬ φ → ψ ) → ( ( ¬ φ → χ ) → ( ¬ φ → θ ) ) ) )",
        s_imim2,
        s_A2,
        ref="syl6",
        note="syl6(imim2, A2)",
    )
    return lb.build(res)


def prove_pm2_83(sys: System) -> Proof:
    """pm2.83: (φ → (ψ → χ)) → ((φ → (χ → θ)) → (φ → (ψ → θ))).

    Closed form of syld.  Theorem *2.83 of [WhiteheadRussell] p. 108.
    (Contributed by NM, 3-Jan-2005.)
    set.mm proof: imim1 imim3i.
    """
    lb = ProofBuilder(sys, "pm2.83")
    s1 = lb.ref("s1", "( ( ψ → χ ) → ( ( χ → θ ) → ( ψ → θ ) ) )", ref="imim1", note="imim1")
    res = lb.ref(
        "res",
        "( ( φ → ( ψ → χ ) ) → ( ( φ → ( χ → θ ) ) → ( φ → ( ψ → θ ) ) ) )",
        s1,
        ref="imim3i",
        note="imim3i",
    )
    return lb.build(res)


def prove_pm2_85(sys: System) -> Proof:
    """pm2.85: ((φ ∨ ψ) → (φ ∨ χ)) → (φ ∨ (ψ → χ)).
    Reverse direction of orimdi.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm2.85")
    # orimdi: ( ( ph \/ ( ps -> ch ) ) <-> ( ( ph \/ ps ) -> ( ph \/ ch ) ) )
    s1 = lb.ref(
        "s1",
        r"( ( ph \/ ( ps -> ch ) ) <-> ( ( ph \/ ps ) -> ( ph \/ ch ) ) )",
        ref="orimdi",
        note="orimdi",
    )
    # biimpri: reverse direction
    res = lb.ref(
        "res",
        r"( ( ( ph \/ ps ) -> ( ph \/ ch ) ) -> ( ph \/ ( ps -> ch ) ) )",
        s1,
        ref="biimpri",
        note="biimpri",
    )
    return lb.build(res)


def prove_pm2_82(sys: System) -> Proof:
    """pm2.82: ((φ ∨ ψ) ∨ χ) → (((φ ∨ ¬ χ) ∨ θ) → ((φ ∨ ψ) ∨ θ)).

    Theorem *2.82 of [WhiteheadRussell] p. 108.
    set.mm proof: pm2.24 orim2d jao1i orim1d.
    """
    lb = ProofBuilder(sys, "pm2.82")

    # Step 1: pm2.24: χ → (¬ χ → ψ)
    s1 = lb.ref("s1", "χ → ( ¬ χ → ψ )", ref="pm2.24", note="pm2.24")

    # Step 2: orim2d: χ → ((φ ∨ ¬ χ) → (φ ∨ ψ))
    s2 = lb.ref(
        "s2",
        "χ → ( ( φ ∨ ¬ χ ) → ( φ ∨ ψ ) )",
        s1,
        ref="orim2d",
        note="orim2d",
    )

    # Step 3: jao1i: ((φ ∨ ψ) ∨ χ) → ((φ ∨ ¬ χ) → (φ ∨ ψ))
    s3 = lb.ref(
        "s3",
        "( ( φ ∨ ψ ) ∨ χ ) → ( ( φ ∨ ¬ χ ) → ( φ ∨ ψ ) )",
        s2,
        ref="jao1i",
        note="jao1i",
    )

    # Step 4: orim1d: ((φ ∨ ψ) ∨ χ) → (((φ ∨ ¬ χ) ∨ θ) → ((φ ∨ ψ) ∨ θ))
    res = lb.ref(
        "res",
        "( ( φ ∨ ψ ) ∨ χ ) → ( ( ( φ ∨ ¬ χ ) ∨ θ ) → ( ( φ ∨ ψ ) ∨ θ ) )",
        s3,
        ref="orim1d",
        note="orim1d",
    )

    return lb.build(res)


def prove_orel1(sys: System) -> Proof:
    """orel1: ¬ φ → ( ( φ ∨ ψ ) → ψ ).

    Principle of disjunctive syllogism (inference form).
    set.mm proof: pm2.53 + com12.
    Under df-or: ¬ φ → ( ( ¬ φ → ψ ) → ψ ).
    """
    lb = ProofBuilder(sys, "orel1")
    # A2: ( ( ¬ φ → ψ ) → ( ¬ φ → ψ ) ) → ( ( ( ¬ φ → ψ ) → ¬ φ ) → ( ( ¬ φ → ψ ) → ψ ) )
    s1 = lb.ref(
        "s1",
        "( ( ¬ φ → ψ ) → ( ¬ φ → ψ ) ) → ( ( ( ¬ φ → ψ ) → ¬ φ ) → ( ( ¬ φ → ψ ) → ψ ) )",
        ref="ax-2",
        note="A2",
    )
    # id: ( ¬ φ → ψ ) → ( ¬ φ → ψ )
    s2 = lb.ref("s2", "( ¬ φ → ψ ) → ( ¬ φ → ψ )", ref="id", note="id")
    # MP(s2, s1): ( ( ¬ φ → ψ ) → ¬ φ ) → ( ( ¬ φ → ψ ) → ψ )
    s3 = lb.mp("s3", s2, s1, "MP id A2")
    # A1: ¬ φ → ( ( ¬ φ → ψ ) → ¬ φ )
    s4 = lb.ref("s4", "¬ φ → ( ( ¬ φ → ψ ) → ¬ φ )", ref="ax-1", note="A1")
    # syl(s4, s3): ¬ φ → ( ( ¬ φ → ψ ) → ψ )
    expanded = lb.ref("expanded", "¬ φ → ( ( ¬ φ → ψ ) → ψ )", s4, s3, ref="syl", note="syl")
    df_or = lb.ref(
        "df_or",
        "( φ ∨ ψ ) ↔ ( ¬ φ → ψ )",
        ref="df-or",
        note="df-or",
    )
    forward = lb.ref(
        "forward",
        "( φ ∨ ψ ) → ( ¬ φ → ψ )",
        df_or,
        ref="biimpi",
        note="biimpi",
    )
    res = lb.ref(
        "res",
        "¬ φ → ( ( φ ∨ ψ ) → ψ )",
        forward,
        expanded,
        ref="syl5",
        note="syl5",
    )
    return lb.build(res)


def prove_orel2(sys: System) -> Proof:
    """orel2: ¬ φ → ( ( ψ ∨ φ ) → ψ ).

    Principle of disjunctive syllogism (inference form).
    set.mm proof: wn + idd + pm2.21 + jaod.
    Under df-or: ¬ φ → ( ( -. ψ → φ ) → ψ ).
    """
    lb = ProofBuilder(sys, "orel2")
    # id: ψ → ψ
    s1 = lb.ref("s1", "ψ → ψ", ref="id", note="id")
    # A1: ( ψ → ψ ) → ( ¬ φ → ( ψ → ψ ) )
    s2 = lb.ref("s2", "( ψ → ψ ) → ( ¬ φ → ( ψ → ψ ) )", ref="ax-1", note="A1")
    # MP: ¬ φ → ( ψ → ψ )
    s3 = lb.mp("s3", s1, s2, "MP(s1, s2)")
    # pm2.21: ¬ φ → ( φ → ψ )
    s4 = lb.ref("s4", "¬ φ → ( φ → ψ )", ref="pm2.21", note="pm2.21")
    # jaod: ¬ φ → ( ( ψ ∨ φ ) → ψ )
    res = lb.ref("res", "¬ φ → ( ( ψ ∨ φ ) → ψ )", s3, s4, ref="jaod", note="jaod")
    return lb.build(res)


def prove_pm2_1(sys: System) -> Proof:
    r"""pm2.1: ( -. ph \/ ph ).

    Principle of excluded middle expressed with disjunction.
    set.mm proof: id imori.
    """
    lb = ProofBuilder(sys, "pm2.1")
    s1 = lb.ref("s1", "( ph -> ph )", ref="id", note="id")
    res = lb.ref("res", r"( -. ph \/ ph )", s1, ref="imori", note="imori")
    return lb.build(res)


def prove_pm1_2(sys: System) -> Proof:
    """pm1.2: ( ( φ ∨ φ ) → φ ).

    Principle of idempotence for disjunction.
    set.mm proof: id + jaoi.
    """
    lb = ProofBuilder(sys, "pm1.2")
    s1 = lb.ref("s1", "φ → φ", ref="id", note="id")
    res = lb.ref("res", "( φ ∨ φ ) → φ", s1, s1, ref="jaoi", note="jaoi")
    return lb.build(res)


def prove_pm3_1(sys: System) -> Proof:
    """pm3.1: ( φ ∧ ψ ) → ¬ ( ¬ φ ∨ ¬ ψ ).

    Forward direction of anor: a conjunction implies the negation
    of the disjunction of the negations.
    """
    lb = ProofBuilder(sys, "pm3.1")
    s1 = lb.ref(
        "s1",
        "( φ ∧ ψ ) ↔ ¬ ( ¬ φ ∨ ¬ ψ )",
        ref="anor",
        note="anor",
    )
    res = lb.ref(
        "res",
        "( φ ∧ ψ ) → ¬ ( ¬ φ ∨ ¬ ψ )",
        s1,
        ref="biimpi",
        note="biimpi",
    )
    return lb.build(res)


def prove_pm3_2ni(sys: System) -> Proof:
    """pm3.2ni: -. ( φ ∨ ψ ).  Hyp: ¬ φ, -. ψ.

    Principle of negation of disjunction.  Both disjuncts are false, so their
    disjunction is false.
    set.mm proof: id + pm2.21i + jaoi + mto.
    """
    lb = ProofBuilder(sys, "pm3.2ni")
    h1 = lb.hyp("pm3.2ni.1", "¬ φ")
    h2 = lb.hyp("pm3.2ni.2", "-. ψ")

    s1 = lb.ref("s1", "φ → φ", ref="id", note="id")
    s2 = lb.ref("s2", "ψ → φ", h2, ref="pm2.21i", note="pm2.21i")
    s3 = lb.ref("s3", "( φ ∨ ψ ) → φ", s1, s2, ref="jaoi", note="jaoi")
    res = lb.ref("res", "-. ( φ ∨ ψ )", h1, s3, ref="mto", note="mto")
    return lb.build(res)


def prove_3pm3_2ni(sys: System) -> Proof:
    """3pm3.2ni: -. ( φ ∨ ψ ∨ χ ).  Hyp: ¬ φ, -. ψ, -. χ.

    Principle of negation of triple disjunction.  All three disjuncts are
    false, so their disjunction is false.
    set.mm proof: pm3.2ni + df-3or + mtbir.
    """
    lb = ProofBuilder(sys, "3pm3.2ni")
    h1 = lb.hyp("3pm3.2ni.1", "¬ φ")
    h2 = lb.hyp("3pm3.2ni.2", "-. ψ")
    h3 = lb.hyp("3pm3.2ni.3", "-. χ")

    # pm3.2ni with ¬ φ and -. ψ
    s1 = lb.ref("s1", "-. ( φ ∨ ψ )", h1, h2, ref="pm3.2ni", note="pm3.2ni")
    # pm3.2ni with -. ( φ ∨ ψ ) and -. χ
    s2 = lb.ref("s2", "-. ( ( φ ∨ ψ ) ∨ χ )", s1, h3, ref="pm3.2ni", note="pm3.2ni")
    # df-3or: ( φ ∨ ψ ∨ χ ) ↔ ( ( φ ∨ ψ ) ∨ χ )
    s3 = lb.ref(
        "s3",
        "( ( φ ∨ ψ ∨ χ ) ↔ ( ( φ ∨ ψ ) ∨ χ ) )",
        ref="df-3or",
        note="df-3or",
    )
    # mtbir: -. ( ( φ ∨ ψ ) ∨ χ ) + biconditional → -. ( φ ∨ ψ ∨ χ )
    res = lb.ref("res", "-. ( φ ∨ ψ ∨ χ )", s2, s3, ref="mtbir", note="mtbir")
    return lb.build(res)


def prove_pm4_52(sys: System) -> Proof:
    """pm4.52: ( φ ∧ ¬ ψ ) ↔ ¬ ( ¬ φ ∨ ψ ).

    Express a conjunction with a negated second argument as the negation
    of a disjunction.
    """
    lb = ProofBuilder(sys, "pm4.52")

    # annim: ( φ ∧ ¬ ψ ) ↔ ¬ ( φ → ψ )
    s1 = lb.ref(
        "s1",
        "( φ ∧ ¬ ψ ) ↔ ¬ ( φ → ψ )",
        ref="annim",
        note="annim",
    )

    # imor: ( φ → ψ ) ↔ ( ¬ φ ∨ ψ )
    s2 = lb.ref(
        "s2",
        "( φ → ψ ) ↔ ( ¬ φ ∨ ψ )",
        ref="imor",
        note="imor",
    )

    # xchbinx(annim, imor): ( φ ∧ ¬ ψ ) ↔ ¬ ( ¬ φ ∨ ψ )
    res = lb.ref(
        "res",
        "( φ ∧ ¬ ψ ) ↔ ¬ ( ¬ φ ∨ ψ )",
        s1,
        s2,
        ref="xchbinx",
        note="xchbinx",
    )

    return lb.build(res)


def prove_pm4_54(sys: System) -> Proof:
    """pm4.54: ( ( ¬ φ ∧ ψ ) ↔ ¬ ( φ ∨ ¬ ψ ) ).

    Negated-disjunction form of a negated-antecedent conjunction.
    """
    lb = ProofBuilder(sys, "pm4.54")

    # df-an: ( ( ¬ φ ∧ ψ ) ↔ ¬ ( ( ¬ φ ) → ¬ ψ ) )
    s1 = lb.ref(
        "s1",
        "( ( ¬ φ ∧ ψ ) ↔ ¬ ( ( ¬ φ ) → ¬ ψ ) )",
        ref="df-an",
        note="df-an",
    )

    # pm4.66: ( ( ¬ φ → ¬ ψ ) ↔ ( φ ∨ ¬ ψ ) )
    s2 = lb.ref(
        "s2",
        "( ( ¬ φ → ¬ ψ ) ↔ ( φ ∨ ¬ ψ ) )",
        ref="pm4.66",
        note="pm4.66",
    )

    # xchbinx: ( ( ¬ φ ∧ ψ ) ↔ ¬ ( φ ∨ ¬ ψ ) )
    res = lb.ref(
        "res",
        "( ( ¬ φ ∧ ψ ) ↔ ¬ ( φ ∨ ¬ ψ ) )",
        s1,
        s2,
        ref="xchbinx",
        note="xchbinx",
    )

    return lb.build(res)


def prove_pm4_55(sys: System) -> Proof:
    """pm4.55: ( ¬ ( ¬ φ ∧ ψ ) ↔ ( φ ∨ ¬ ψ ) ).

    Negated-conjunction equivalent to a disjunction with negated right
    disjunct.
    """
    lb = ProofBuilder(sys, "pm4.55")

    # pm4.54: ( ( ¬ φ ∧ ψ ) ↔ ¬ ( φ ∨ ¬ ψ ) )
    s1 = lb.ref(
        "s1",
        "( ( ¬ φ ∧ ψ ) ↔ ¬ ( φ ∨ ¬ ψ ) )",
        ref="pm4.54",
        note="pm4.54",
    )

    # con2bii: ( ( φ ∨ ¬ ψ ) ↔ ¬ ( ¬ φ ∧ ψ ) )
    s2 = lb.ref(
        "s2",
        "( ( φ ∨ ¬ ψ ) ↔ ¬ ( ¬ φ ∧ ψ ) )",
        s1,
        ref="con2bii",
        note="con2bii",
    )

    # bicomi: ( ¬ ( ¬ φ ∧ ψ ) ↔ ( φ ∨ ¬ ψ ) )
    res = lb.ref(
        "res",
        "( ¬ ( ¬ φ ∧ ψ ) ↔ ( φ ∨ ¬ ψ ) )",
        s2,
        ref="bicomi",
        note="bicomi",
    )

    return lb.build(res)


def prove_pm4_62(sys: System) -> Proof:
    r"""pm4.62: ( ( ph -> -. ps ) <-> ( -. ph \/ -. ps ) ).

    imor with -. ps for ps.
    """
    lb = ProofBuilder(sys, "pm4.62")
    res = lb.ref("res", r"( ( ph -> -. ps ) <-> ( -. ph \/ -. ps ) )", ref="imor", note="imor")
    return lb.build(res)


def prove_pm4_64(sys: System) -> Proof:
    """pm4.64: ( ( ¬ φ → ψ ) ↔ ( φ ∨ ψ ) ).

    Commuted form of df-or: the implication-from-negated-antecedent
    form is equivalent to the disjunction form.
    set.mm proof: df-or + bicom1.
    """
    lb = ProofBuilder(sys, "pm4.64")
    s1 = lb.ref("s1", "( ( φ ∨ ψ ) ↔ ( ¬ φ → ψ ) )", ref="df-or", note="df-or")
    s2 = lb.ref(
        "s2",
        "( ( ( φ ∨ ψ ) ↔ ( ¬ φ → ψ ) ) → ( ( ¬ φ → ψ ) ↔ ( φ ∨ ψ ) ) )",
        ref="bicom1",
        note="bicom1",
    )
    res = lb.mp("res", s1, s2, "MP df-or bicom1")
    return lb.build(res)


def prove_pm4_66(sys: System) -> Proof:
    """pm4.66: ( ( ¬ φ → -. ψ ) ↔ ( φ ∨ -. ψ ) ).

    pm4.64 with -. ψ for ψ.
    """
    lb = ProofBuilder(sys, "pm4.66")
    res = lb.ref("res", "( ( ¬ φ → ¬ ψ ) ↔ ( φ ∨ ¬ ψ ) )", ref="pm4.64", note="pm4.64")
    return lb.build(res)


def prove_3orel1(sys: System) -> Proof:
    """3orel1: ( ¬ φ → ( ( φ ∨ ψ ∨ χ ) → ( ψ ∨ χ ) ) ).

    Partial elimination of a triple disjunction: if the first disjunct is
    false, then adding it to a disjunction of the other two has no effect.
    set.mm proof: 3orass + orel1 + biimtrid.
    """
    lb = ProofBuilder(sys, "3orel1")
    s1 = lb.ref("s1", "( ( φ ∨ ψ ∨ χ ) ↔ ( φ ∨ ( ψ ∨ χ ) ) )", ref="3orass", note="3orass")
    s2 = lb.ref("s2", "( ¬ φ → ( ( φ ∨ ( ψ ∨ χ ) ) → ( ψ ∨ χ ) ) )", ref="orel1", note="orel1")
    res = lb.ref(
        "res", "( ¬ φ → ( ( φ ∨ ψ ∨ χ ) → ( ψ ∨ χ ) ) )", s1, s2, ref="biimtrid", note="biimtrid"
    )
    return lb.build(res)


def prove_3orel2(sys: System) -> Proof:
    """3orel2: ( ¬ ψ → ( ( φ ∨ ψ ∨ χ ) → ( φ ∨ χ ) ) ).

    Partial elimination of a triple disjunction: if the middle disjunct is
    false, the remaining two suffice.
    set.mm proof: 3orcoma + 3orel1 + biimtrid.
    """
    lb = ProofBuilder(sys, "3orel2")
    s1 = lb.ref("s1", "( ( φ ∨ ψ ∨ χ ) ↔ ( ψ ∨ φ ∨ χ ) )", ref="3orcoma", note="3orcoma")
    s2 = lb.ref("s2", "( ¬ ψ → ( ( ψ ∨ φ ∨ χ ) → ( φ ∨ χ ) ) )", ref="3orel1", note="3orel1")
    res = lb.ref(
        "res", "( ¬ ψ → ( ( φ ∨ ψ ∨ χ ) → ( φ ∨ χ ) ) )", s1, s2, ref="biimtrid", note="biimtrid"
    )
    return lb.build(res)


def prove_3orel2OLD(sys: System) -> Proof:
    """3orel2OLD: ( ¬ ψ → ( ( φ ∨ ψ ∨ χ ) → ( φ ∨ χ ) ).

    Alternate proof of ~ 3orel2 from 3orrot, 3orel1, orcom, imbitrdi,
    and biimtrid.
    """
    lb = ProofBuilder(sys, "3orel2OLD")
    s1 = lb.ref("s1", "( ( φ ∨ ψ ∨ χ ) ↔ ( ψ ∨ χ ∨ φ ) )", ref="3orrot", note="3orrot")
    s2 = lb.ref("s2", "( ¬ ψ → ( ( ψ ∨ χ ∨ φ ) → ( χ ∨ φ ) ) )", ref="3orel1", note="3orel1")
    s3 = lb.ref("s3", "( ( χ ∨ φ ) ↔ ( φ ∨ χ ) )", ref="orcom", note="orcom")
    s4 = lb.ref(
        "s4", "( ¬ ψ → ( ( ψ ∨ χ ∨ φ ) → ( φ ∨ χ ) ) )", s2, s3, ref="imbitrdi", note="imbitrdi"
    )
    res = lb.ref(
        "res", "( ¬ ψ → ( ( φ ∨ ψ ∨ χ ) → ( φ ∨ χ ) ) )", s1, s4, ref="biimtrid", note="biimtrid"
    )
    return lb.build(res)


def prove_3orel3(sys: System) -> Proof:
    """3orel3: ( ¬ χ → ( ( φ ∨ ψ ∨ χ ) → ( φ ∨ ψ ) ).

    Inference form of disjunctive syllogism with a ternary antecedent.
    set.mm proof: df-3or + orel2 + biimtrid.
    """
    lb = ProofBuilder(sys, "3orel3")
    s1 = lb.ref("s1", "( ( φ ∨ ψ ∨ χ ) ↔ ( ( φ ∨ ψ ) ∨ χ ) )", ref="df-3or", note="df-3or")
    s2 = lb.ref("s2", "( ¬ χ → ( ( ( φ ∨ ψ ) ∨ χ ) → ( φ ∨ ψ ) ) )", ref="orel2", note="orel2")
    res = lb.ref(
        "res", "( ¬ χ → ( ( φ ∨ ψ ∨ χ ) → ( φ ∨ ψ ) ) )", s1, s2, ref="biimtrid", note="biimtrid"
    )
    return lb.build(res)


def prove_3orel13(sys: System) -> Proof:
    """3orel13: ( ( ¬ φ ∧ ¬ χ ) → ( ( φ ∨ ψ ∨ χ ) → ψ ) ).

    If the first and third disjuncts of a triple disjunction are false,
    the second must hold.
    set.mm proof: 3orel3 + orel1 + sylan9r.
    """
    lb = ProofBuilder(sys, "3orel13")
    s1 = lb.ref("s1", "( ¬ χ → ( ( φ ∨ ψ ∨ χ ) → ( φ ∨ ψ ) ) )", ref="3orel3", note="3orel3")
    s2 = lb.ref("s2", "( ¬ φ → ( ( φ ∨ ψ ) → ψ ) )", ref="orel1", note="orel1")
    res = lb.ref(
        "res", "( ( ¬ φ ∧ ¬ χ ) → ( ( φ ∨ ψ ∨ χ ) → ψ ) )", s1, s2, ref="sylan9r", note="sylan9r"
    )
    return lb.build(res)


def prove_orri(sys: System) -> Proof:
    """orri: ( φ ∨ ψ ).

    Inference introducing a disjunction from the df-or expansion.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "orri")
    h1 = lb.hyp("orri.1", "¬ φ → ψ")
    s1 = lb.ref("s1", "( ( φ ∨ ψ ) ↔ ( ¬ φ → ψ ) )", ref="df-or", note="df-or")
    s2 = lb.ref("s2", "( ¬ φ → ψ ) → ( φ ∨ ψ )", s1, ref="biimpri", note="biimpri df-or")
    res = lb.mp("res", h1, s2, "MP orri.1, s2")
    return lb.build(res)


def prove_consensus(sys: System) -> Proof:
    """consensus: ( ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) ) ∨ ( ψ ∧ χ ) ) ↔ ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) ).

    The consensus theorem from Boolean algebra: the redundant disjunct
    ( ψ ∧ χ ) can be dropped from a disjunction that already contains
    ( φ ∧ ψ ) and ( ¬ φ ∧ χ ).
    """
    lb = ProofBuilder(sys, "consensus")

    # Step 1: ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) ) → ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) )
    s1 = lb.ref(
        "s1",
        "( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) ) → ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) )",
        ref="id",
        note="id",
    )

    # Step 2: ( φ ∧ ψ ) → ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) )
    s2 = lb.ref(
        "s2",
        "( φ ∧ ψ ) → ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) )",
        ref="orc",
        note="orc",
    )

    # Step 3: ( φ ∧ ( ψ ∧ χ ) ) → ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) )
    s3 = lb.ref(
        "s3",
        "( φ ∧ ( ψ ∧ χ ) ) → ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) )",
        s2,
        ref="adantrr",
        note="adantrr",
    )

    # Step 4: ( ¬ φ ∧ χ ) → ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) )
    s4 = lb.ref(
        "s4",
        "( ¬ φ ∧ χ ) → ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) )",
        ref="olc",
        note="olc",
    )

    # Step 5: ( ¬ φ ∧ ( ψ ∧ χ ) ) → ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) )
    s5 = lb.ref(
        "s5",
        "( ¬ φ ∧ ( ψ ∧ χ ) ) → ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) )",
        s4,
        ref="adantrl",
        note="adantrl",
    )

    # Step 6: ( ψ ∧ χ ) → ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) )
    s6 = lb.ref(
        "s6",
        "( ψ ∧ χ ) → ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) )",
        s3,
        s5,
        ref="pm2.61ian",
        note="pm2.61ian",
    )

    # Step 7: ( ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) ) ∨ ( ψ ∧ χ ) ) → ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) )
    s7 = lb.ref(
        "s7",
        "( ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) ) ∨ ( ψ ∧ χ ) ) → ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) )",
        s1,
        s6,
        ref="jaoi",
        note="jaoi",
    )

    # Step 8: ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) ) → ( ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) ) ∨ ( ψ ∧ χ ) )
    s8 = lb.ref(
        "s8",
        "( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) ) → ( ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) ) ∨ ( ψ ∧ χ ) )",
        ref="orc",
        note="orc",
    )

    # Step 9: ( ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) ) ∨ ( ψ ∧ χ ) ) ↔ ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) )
    res = lb.ref(
        "res",
        "( ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) ) ∨ ( ψ ∧ χ ) ) ↔ ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) )",
        s7,
        s8,
        ref="impbii",
        note="impbii",
    )

    return lb.build(res)


def prove_curryax(sys: System) -> Proof:
    """curryax: ( φ ∨ ( φ → ψ ) ).

    Excluded middle expressed with disjunction and implication (variant of pm2.25).
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "curryax")
    s1 = lb.ref("s1", "¬ φ → ( φ → ψ )", ref="pm2.21", note="pm2.21")
    res = lb.ref("res", "( φ ∨ ( φ → ψ ) )", s1, ref="orri", note="orri")
    return lb.build(res)


def prove_pm5_6(sys: System) -> Proof:
    r"""pm5.6: ( ( ( ph /\ -. ps ) -> ch ) <-> ( ph -> ( ps \/ ch ) ) ).

    Theorem *5.6 of [WhiteheadRussell] p. 125.
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: impexp df-or imbi2i bitr4i.
    """
    lb = ProofBuilder(sys, "pm5.6")

    # impexp: ( ( ( ph /\ -. ps ) -> ch ) <-> ( ph -> ( -. ps -> ch ) ) )
    s1 = lb.ref(
        "s1",
        r"( ( ( ph /\ -. ps ) -> ch ) <-> ( ph -> ( -. ps -> ch ) ) )",
        ref="impexp",
        note="impexp",
    )

    # df-or: ( ( ps \/ ch ) <-> ( -. ps -> ch ) )
    s2 = lb.ref(
        "s2",
        r"( ( ps \/ ch ) <-> ( -. ps -> ch ) )",
        ref="df-or",
        note="df-or",
    )

    # imbi2i with antecedent ph on s2:
    # ( ( ph -> ( ps \/ ch ) ) <-> ( ph -> ( -. ps -> ch ) ) )
    s3 = lb.ref(
        "s3",
        r"( ( ph -> ( ps \/ ch ) ) <-> ( ph -> ( -. ps -> ch ) ) )",
        s2,
        ref="imbi2i",
        note="imbi2i",
    )

    # bitr4i: combine s1 and s3, both share RHS ( ph -> ( -. ps -> ch ) )
    res = lb.ref(
        "res",
        r"( ( ( ph /\ -. ps ) -> ch ) <-> ( ph -> ( ps \/ ch ) ) )",
        s1,
        s3,
        ref="bitr4i",
        note="bitr4i",
    )

    return lb.build(res)


def prove_pm5_61(sys: System) -> Proof:
    """pm5.61: ((φ ∨ ψ) ∧ ¬ ψ) ↔ (φ ∧ ¬ ψ).

    Elimination of a disjunct by a contradictory conjunct.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm5.61")

    # orel2: ¬ φ → ((ψ ∨ φ) → ψ), substitute φ:=ψ, ψ:=φ
    s1 = lb.ref("s1", "¬ ψ → ((φ ∨ ψ) → φ)", ref="orel2", note="orel2")

    # orc: φ → (φ ∨ ψ)
    s2 = lb.ref("s2", "φ → (φ ∨ ψ)", ref="orc", note="orc")

    # impbid1: s1 and s2 give ¬ ψ → ((φ ∨ ψ) ↔ φ)
    s3 = lb.ref(
        "s3",
        "¬ ψ → ((φ ∨ ψ) ↔ φ)",
        s1,
        s2,
        ref="impbid1",
        note="impbid1",
    )

    # pm5.32ri: ((φ ∨ ψ) ∧ ¬ ψ) ↔ (φ ∧ ¬ ψ)
    res = lb.ref(
        "res",
        "((φ ∨ ψ) ∧ ¬ ψ) ↔ (φ ∧ ¬ ψ)",
        s3,
        ref="pm5.32ri",
        note="pm5.32ri",
    )

    return lb.build(res)


def prove_pm5_62(sys: System) -> Proof:
    """pm5.62: ((φ ∧ ψ) ∨ ¬ ψ) ↔ (φ ∨ ¬ ψ).

    Combine excluded middle with distribution of disjunction over
    conjunction.
    """
    lb = ProofBuilder(sys, "pm5.62")

    # exmid: ψ ∨ ¬ ψ
    s1 = lb.ref("s1", "( ψ ∨ ¬ ψ )", ref="exmid", note="exmid")

    # ordir: ((φ ∧ ψ) ∨ ¬ ψ) ↔ ((φ ∨ ¬ ψ) ∧ (ψ ∨ ¬ ψ))
    s2 = lb.ref(
        "s2",
        "( ( φ ∧ ψ ) ∨ ¬ ψ ) ↔ ( ( φ ∨ ¬ ψ ) ∧ ( ψ ∨ ¬ ψ ) )",
        ref="ordir",
        note="ordir",
    )

    # mpbiran2: ((φ ∧ ψ) ∨ ¬ ψ) ↔ (φ ∨ ¬ ψ)
    res = lb.ref(
        "res",
        "( ( φ ∧ ψ ) ∨ ¬ ψ ) ↔ ( φ ∨ ¬ ψ )",
        s1,
        s2,
        ref="mpbiran2",
        note="mpbiran2",
    )

    return lb.build(res)


def prove_pm5_63(sys: System) -> Proof:
    """pm5.63: ( φ ∨ ψ ) ↔ ( φ ∨ ( ¬ φ ∧ ψ ) ).

    Combine excluded middle with distribution of disjunction over
    conjunction.
    """
    lb = ProofBuilder(sys, "pm5.63")

    # exmid: ( φ ∨ ¬ φ )
    s1 = lb.ref("s1", "( φ ∨ ¬ φ )", ref="exmid", note="exmid")

    # ordi: ( φ ∨ ( ¬ φ ∧ ψ ) ) ↔ ( ( φ ∨ ¬ φ ) ∧ ( φ ∨ ψ ) )
    s2 = lb.ref(
        "s2",
        "( φ ∨ ( ¬ φ ∧ ψ ) ) ↔ ( ( φ ∨ ¬ φ ) ∧ ( φ ∨ ψ ) )",
        ref="ordi",
        note="ordi",
    )

    # mpbiran: ( φ ∨ ( ¬ φ ∧ ψ ) ) ↔ ( φ ∨ ψ )
    s3 = lb.ref(
        "s3",
        "( φ ∨ ( ¬ φ ∧ ψ ) ) ↔ ( φ ∨ ψ )",
        s1,
        s2,
        ref="mpbiran",
        note="mpbiran",
    )

    # bicomi: ( φ ∨ ψ ) ↔ ( φ ∨ ( ¬ φ ∧ ψ ) )
    res = lb.ref(
        "res",
        "( φ ∨ ψ ) ↔ ( φ ∨ ( ¬ φ ∧ ψ ) )",
        s3,
        ref="bicomi",
        note="bicomi",
    )

    return lb.build(res)


def prove_pm5_7(sys: System) -> Proof:
    r"""pm5.7: ( ( ( ph \/ ch ) <-> ( ps \/ ch ) ) <-> ( ch \/ ( ph <-> ps ) ) ).

    Theorem *5.7 of [WhiteheadRussell] p. 125.
    (Contributed by NM, 3-Jan-2005.)
    set.mm proof: orbidi orcom bibi12i bitr2i.
    """
    lb = ProofBuilder(sys, "pm5.7")

    # orcom: ( ( ph \/ ch ) <-> ( ch \/ ph ) )
    s1 = lb.ref(
        "s1",
        r"( ( ph \/ ch ) <-> ( ch \/ ph ) )",
        ref="orcom",
        note="orcom",
    )

    # orcom: ( ( ps \/ ch ) <-> ( ch \/ ps ) )
    s2 = lb.ref(
        "s2",
        r"( ( ps \/ ch ) <-> ( ch \/ ps ) )",
        ref="orcom",
        note="orcom",
    )

    # bibi12i: from s1 and s2, get the biconditional of biconditionals
    s3 = lb.ref(
        "s3",
        r"( ( ( ph \/ ch ) <-> ( ps \/ ch ) ) <-> ( ( ch \/ ph ) <-> ( ch \/ ps ) ) )",
        s1,
        s2,
        ref="bibi12i",
        note="bibi12i",
    )

    # orbidi: ( ( ch \/ ( ph <-> ps ) ) <-> ( ( ch \/ ph ) <-> ( ch \/ ps ) ) )
    s4 = lb.ref(
        "s4",
        r"( ( ch \/ ( ph <-> ps ) ) <-> ( ( ch \/ ph ) <-> ( ch \/ ps ) ) )",
        ref="orbidi",
        note="orbidi",
    )

    # bicomi: reverse s3 to get ( ( ch \/ ph ) <-> ( ch \/ ps ) ) <-> ( ( ph \/ ch ) <-> ( ps \/ ch ) )
    s5 = lb.ref(
        "s5",
        r"( ( ( ch \/ ph ) <-> ( ch \/ ps ) ) <-> ( ( ph \/ ch ) <-> ( ps \/ ch ) ) )",
        s3,
        ref="bicomi",
        note="bicomi",
    )

    # bitr2i: from s4 and s5, get the final result
    res = lb.ref(
        "res",
        r"( ( ( ph \/ ch ) <-> ( ps \/ ch ) ) <-> ( ch \/ ( ph <-> ps ) ) )",
        s4,
        s5,
        ref="bitr2i",
        note="bitr2i",
    )

    return lb.build(res)


def prove_pm5_11g(sys: System) -> Proof:
    """pm5.11g: ( ( φ → ψ ) ∨ ( ¬ φ → χ ) ).

    Theorem *5.11 "general" of [WhiteheadRussell] p. 123.
    (Contributed by NM, 3-Jan-2005.)
    set.mm proof: pm2.5g orri.
    """
    lb = ProofBuilder(sys, "pm5.11g")
    s1 = lb.ref("s1", "¬ ( φ → ψ ) → ( ¬ φ → χ )", ref="pm2.5g", note="pm2.5g")
    res = lb.ref("res", "( ( φ → ψ ) ∨ ( ¬ φ → χ ) )", s1, ref="orri", note="orri")
    return lb.build(res)


def prove_pm5_11(sys: System) -> Proof:
    """pm5.11: ( ( φ → ψ ) ∨ ( ¬ φ → ψ ) ).

    Theorem *5.11 of [WhiteheadRussell] p. 123.
    (Contributed by NM, 3-Jan-2005.)
    set.mm proof: pm5.11g.
    """
    lb = ProofBuilder(sys, "pm5.11")
    res = lb.ref("res", "( ( φ → ψ ) ∨ ( ¬ φ → ψ ) )", ref="pm5.11g", note="pm5.11g")
    return lb.build(res)


def prove_pm5_12(sys: System) -> Proof:
    """pm5.12: ( ( φ → ψ ) ∨ ( φ → ¬ ψ ) ).

    Theorem *5.12 of [WhiteheadRussell] p. 123.
    (Contributed by NM, 3-Jan-2005.)
    set.mm proof: pm2.51 orri.
    """
    lb = ProofBuilder(sys, "pm5.12")
    s1 = lb.ref("s1", "( -. ( φ → ψ ) → ( φ → -. ψ ) )", ref="pm2.51", note="pm2.51")
    res = lb.ref("res", "( ( φ → ψ ) ∨ ( φ → -. ψ ) )", s1, ref="orri", note="orri")
    return lb.build(res)


def prove_pm2_25(sys: System) -> Proof:
    """pm2.25: ( φ ∨ ( ( φ ∨ ψ ) → ψ ) ).

    Excluded middle expressed with disjunction and implication.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm2.25")
    s1 = lb.ref("s1", "¬ φ → ( ( φ ∨ ψ ) → ψ )", ref="orel1", note="orel1")
    res = lb.ref("res", "( φ ∨ ( ( φ ∨ ψ ) → ψ ) )", s1, ref="orri", note="orri")
    return lb.build(res)


def prove_orci(sys: System) -> Proof:
    """orci: ( φ ∨ ψ ).  Hyp: φ.

    Inference introducing a left disjunct.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: pm2.24i orri.
    """
    lb = ProofBuilder(sys, "orci")
    h1 = lb.hyp("orci.1", "φ")
    s1 = lb.ref("s1", "( ¬ φ → ψ )", h1, ref="pm2.24i", note="pm2.24i")
    res = lb.ref("res", "( φ ∨ ψ )", s1, ref="orri", note="orri")
    return lb.build(res)


def prove_olci(sys: System) -> Proof:
    """olci: ( ψ ∨ φ ).  Hyp: φ.

    Inference introducing a right disjunct.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: a1i orri.
    """
    lb = ProofBuilder(sys, "olci")
    h1 = lb.hyp("orci.1", "φ")
    s1 = lb.ref("s1", "( ¬ ψ → φ )", h1, ref="a1i", note="a1i")
    res = lb.ref("res", "( ψ ∨ φ )", s1, ref="orri", note="orri")
    return lb.build(res)


def prove_exmid(sys: System) -> Proof:
    """exmid: ( φ ∨ ¬ φ ).

    Law of excluded middle.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: id orri.
    """
    lb = ProofBuilder(sys, "exmid")
    s1 = lb.ref("s1", "( ¬ φ → ¬ φ )", ref="id", note="id")
    res = lb.ref("res", "( φ ∨ ¬ φ )", s1, ref="orri", note="orri")
    return lb.build(res)


def prove_exmidd(sys: System) -> Proof:
    """exmidd: ( φ → ( ψ ∨ ¬ ψ ) ).

    Deduction form of exmid.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: exmid a1i.
    """
    lb = ProofBuilder(sys, "exmidd")
    s1 = lb.ref("s1", "( ψ ∨ ¬ ψ )", ref="exmid", note="exmid")
    res = lb.ref("res", "( φ → ( ψ ∨ ¬ ψ ) )", s1, ref="a1i", note="a1i")
    return lb.build(res)


def prove_orrd(sys: System) -> Proof:
    """orrd: ( ph -> ( ps ∨ ch ) ).

    Deduction form of orri.
    set.mm proof: pm2.54 syl.
    """
    lb = ProofBuilder(sys, "orrd")
    h1 = lb.hyp("orrd.1", "ph -> ( -. ps -> ch )")

    s1 = lb.ref("s1", "( ( ps ∨ ch ) <-> ( -. ps -> ch ) )", ref="df-or", note="df-or")
    s2 = lb.ref("s2", "( -. ps -> ch ) -> ( ps ∨ ch )", s1, ref="biimpri", note="biimpri df-or")
    res = lb.ref("res", "( ph -> ( ps ∨ ch ) )", h1, s2, ref="syl", note="syl orrd.1, s2")
    return lb.build(res)


def prove_orc(sys: System) -> Proof:
    """orc:  ( ph -> ( ph ∨ ps ) ).

    Theorem *2.2 of [WhiteheadRussell] p. 104.  Its associated inference is
    ~ orci.  (Contributed by NM, 5-Aug-1993.)
    set.mm proof: pm2.24 orrd.
    """
    lb = ProofBuilder(sys, "orc")
    s1 = lb.ref("s1", "( ph -> ( -. ph -> ps ) )", ref="pm2.24", note="pm2.24")
    res = lb.ref("res", "( ph -> ( ph ∨ ps ) )", s1, ref="orrd", note="orrd")
    return lb.build(res)


def prove_orcd(sys: System) -> Proof:
    """orcd:  ( ph -> ( ps ∨ ch ) ).

    Deduction introducing a disjunct.  (Contributed by NM, 5-Aug-1993.)
    set.mm proof: orc syl.
    """
    lb = ProofBuilder(sys, "orcd")
    h1 = lb.hyp("orcd.1", "( ph -> ps )")
    s1 = lb.ref("s1", "( ps -> ( ps ∨ ch ) )", ref="orc", note="orc")
    res = lb.ref("res", "( ph -> ( ps ∨ ch ) )", h1, s1, ref="syl", note="syl orcd.1, s1")
    return lb.build(res)


def prove_olcd(sys: System) -> Proof:
    """olcd:  ( ph -> ( ch ∨ ps ) ).  Hyp: ( ph -> ps ).

    Deduction form of olc.  Unlike ~ orcd which introduces a
    right-hand disjunct via the hypothesis, ~ olcd introduces
    a left-hand disjunct.  set.mm proof: orcd orcomd.
    """
    lb = ProofBuilder(sys, "olcd")
    h1 = lb.hyp("olcd.1", "( ph -> ps )")
    s1 = lb.ref("s1", "( ph -> ( ps ∨ ch ) )", h1, ref="orcd", note="orcd")
    res = lb.ref("res", "( ph -> ( ch ∨ ps ) )", s1, ref="orcomd", note="orcomd")
    return lb.build(res)


def prove_biorf(sys: System) -> Proof:
    r"""biorf: ( -. ph -> ( ps <-> ( ph \/ ps ) ) ).

    If a wff is false, a second wff is equivalent to their disjunction.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: olc orel1 impbid2.
    """
    lb = ProofBuilder(sys, "biorf")
    s1 = lb.ref("s1", "( ps → ( ph ∨ ps ) )", ref="olc", note="olc")
    s2 = lb.ref("s2", "( -. ph → ( ( ph ∨ ps ) → ps ) )", ref="orel1", note="orel1")
    res = lb.ref("res", "( -. ph → ( ps ↔ ( ph ∨ ps ) ) )", s1, s2, ref="impbid2", note="impbid2")
    return lb.build(res)


def prove_biort(sys: System) -> Proof:
    r"""biort: ( ph -> ( ph <-> ( ph \/ ps ) ) ).

    If a wff is true, it is equivalent to its disjunction with another wff.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: id orc 2thd.
    """
    lb = ProofBuilder(sys, "biort")
    s1 = lb.ref("s1", "( ph -> ph )", ref="id", note="id")
    s2 = lb.ref("s2", r"( ph -> ( ph \/ ps ) )", ref="orc", note="orc")
    res = lb.ref("res", r"( ph -> ( ph <-> ( ph \/ ps ) ) )", s1, s2, ref="2thd", note="2thd")
    return lb.build(res)


def prove_biortn(sys: System) -> Proof:
    r"""biortn: ( ph -> ( ps <-> ( -. ph \/ ps ) ) ).

    If a wff is true, a second wff is equivalent to the disjunction of the
    negation of the first and the second.
    set.mm proof: notnot biorf syl.
    """
    lb = ProofBuilder(sys, "biortn")
    s1 = lb.ref("s1", "ph -> -. -. ph", ref="notnot", note="notnot")
    s2 = lb.ref("s2", r"( -. -. ph -> ( ps <-> ( -. ph \/ ps ) ) )", ref="biorf", note="biorf")
    res = lb.ref("res", r"( ph -> ( ps <-> ( -. ph \/ ps ) ) )", s1, s2, ref="syl", note="syl")
    return lb.build(res)


def prove_biorfi(sys: System) -> Proof:
    r"""biorfi: ( ps <-> ( ph \/ ps ) ).

    Inference form of biorf.  If a wff is false, a second wff is
    equivalent to their disjunction.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: biorf ax-mp.
    """
    lb = ProofBuilder(sys, "biorfi")
    h1 = lb.hyp("biorfi.1", "-. ph")
    s1 = lb.ref("s1", "( -. ph → ( ps ↔ ( ph ∨ ps ) ) )", ref="biorf", note="biorf")
    res = lb.mp("res", h1, s1, note="MP biorfi.1, biorf => ax-mp")
    return lb.build(res)


def prove_biorfri(sys: System) -> Proof:
    r"""biorfri: ( ps <-> ( ps \/ ph ) ).

    Inference form of biorf with right disjunct.  If a wff is false, a
    second wff is equivalent to the disjunction with the second wff on
    the left.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: biorfi orcom bitri.
    """
    lb = ProofBuilder(sys, "biorfri")
    h1 = lb.hyp("biorfri.1", "-. ph")
    s1 = lb.ref("s1", r"( ps <-> ( ph \/ ps ) )", h1, ref="biorfi", note="biorfi")
    s2 = lb.ref("s2", r"( ( ph \/ ps ) <-> ( ps \/ ph ) )", ref="orcom", note="orcom")
    res = lb.ref("res", r"( ps <-> ( ps \/ ph ) )", s1, s2, ref="bitri", note="bitri")
    return lb.build(res)


def prove_biorfriOLD(sys: System) -> Proof:
    r"""biorfriOLD: ( ps <-> ( ps \/ ph ) ).

    Old proof of biorfri using orc, pm2.53, mt3i, impbii.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: orc pm2.53 mt3i impbii.
    """
    lb = ProofBuilder(sys, "biorfriOLD")
    h1 = lb.hyp("biorfri.1", "-. ph")
    # orc: ( ps -> ( ps \/ ph ) )
    s1 = lb.ref("s1", r"( ps -> ( ps \/ ph ) )", ref="orc", note="orc")
    df_or = lb.ref(
        "df_or",
        r"( ( ps \/ ph ) <-> ( -. ps -> ph ) )",
        ref="df-or",
        note="df-or",
    )
    s2 = lb.ref(
        "s2",
        r"( ( ps \/ ph ) -> ( -. ps -> ph ) )",
        df_or,
        ref="biimpi",
        note="biimpi",
    )
    # mt3i with mt3i.1 = -. ph (h1), mt3i.2 = s2
    s3 = lb.ref("s3", r"( ( ps \/ ph ) -> ps )", h1, s2, ref="mt3i", note="mt3i")
    # impbii with the two directions
    res = lb.ref("res", r"( ps <-> ( ps \/ ph ) )", s1, s3, ref="impbii", note="impbii")
    return lb.build(res)


def prove_imor(sys: System) -> Proof:
    r"""imor: ( ( ph -> ps ) <-> ( -. ph \/ ps ) ).

    Equivalence of implication and disjunction.
    set.mm proof: notnotb + imbi1i + df-or + bitr4i.
    """
    lb = ProofBuilder(sys, "imor")
    # s1: notnotb -> ( ph <-> -. -. ph )
    s1 = lb.ref("s1", "( ph <-> -. -. ph )", ref="notnotb", note="notnotb")
    # s2: imbi1i(s1) -> ( ( ph -> ps ) <-> ( -. -. ph -> ps ) )
    s2 = lb.ref("s2", "( ( ph -> ps ) <-> ( -. -. ph -> ps ) )", s1, ref="imbi1i", note="imbi1i")
    # s3: df-or (with -. ph for ph) -> ( ( -. ph \/ ps ) <-> ( -. -. ph -> ps ) )
    s3 = lb.ref("s3", r"( ( -. ph \/ ps ) <-> ( -. -. ph -> ps ) )", ref="df-or", note="df-or")
    # s4: bitr4i(s3, s2) -> ( ( -. ph \/ ps ) <-> ( ph -> ps ) )
    s4 = lb.ref("s4", r"( ( -. ph \/ ps ) <-> ( ph -> ps ) )", s3, s2, ref="bitr4i", note="bitr4i")
    # res: bicomi(s4) -> ( ( ph -> ps ) <-> ( -. ph \/ ps ) )
    res = lb.ref("res", r"( ( ph -> ps ) <-> ( -. ph \/ ps ) )", s4, ref="bicomi", note="bicomi")
    return lb.build(res)


def prove_imori(sys: System) -> Proof:
    r"""imori: ( -. ph \/ ps ).

    Inference form of imor.
    set.mm proof: imor mpbi.
    """
    lb = ProofBuilder(sys, "imori")
    h1 = lb.hyp("imori.1", "( ph -> ps )")
    imor_th = lb.ref(
        "imor_th",
        r"( ( ph -> ps ) <-> ( -. ph \/ ps ) )",
        ref="imor",
        note="imor",
    )
    res = lb.ref("res", r"( -. ph \/ ps )", h1, imor_th, ref="mpbi", note="mpbi")
    return lb.build(res)


def prove_imorri(sys: System) -> Proof:
    r"""imorri: ( ph -> ps ). Hyp: ( -. ph \/ ps ).

    Inference form of imor (reverse direction).
    set.mm proof: imor mpbir.
    """
    lb = ProofBuilder(sys, "imorri")
    h1 = lb.hyp("imorri.1", r"( -. ph \/ ps )")
    imor_th = lb.ref(
        "imor_th",
        r"( ( ph -> ps ) <-> ( -. ph \/ ps ) )",
        ref="imor",
        note="imor",
    )
    res = lb.ref("res", "( ph -> ps )", h1, imor_th, ref="mpbir", note="mpbir")
    return lb.build(res)


def prove_anmp(sys: System) -> Proof:
    r"""anmp: ps. Hyp: ph, ( -. ph \/ ps ).

    Alternative modus ponens from a disjunctive premise.
    set.mm proof: imorri ax-mp.
    """
    lb = ProofBuilder(sys, "anmp")
    h1 = lb.hyp("anmp.min", "ph")
    h2 = lb.hyp("anmp.maj", r"( -. ph \/ ps )")
    s1 = lb.ref("s1", "( ph -> ps )", h2, ref="imorri", note="imorri")
    res = lb.mp("res", h1, s1, note="MP anmp.min, imorri")
    return lb.build(res)


def prove_orcoms(sys: System) -> Proof:
    """orcoms: ( ( ps ∨ ph ) → ch ).  Hyp: ( ph ∨ ps ) → ch.

    Inference commuting the disjuncts of an antecedent.
    set.mm proof: pm1.4 syl.
    """
    lb = ProofBuilder(sys, "orcoms")
    h1 = lb.hyp("orcoms.1", "( ph ∨ ps ) → ch")
    s1 = lb.ref("s1", "( ps ∨ ph ) → ( ph ∨ ps )", ref="pm1.4", note="pm1.4")
    res = lb.ref("res", "( ps ∨ ph ) → ch", s1, h1, ref="syl", note="syl(pm1.4, orcoms.1)")
    return lb.build(res)


def prove_orcs(sys: System) -> Proof:
    """orcs: ( ph -> ch ).  Hyp: ( ( ph ∨ ps ) -> ch ).

    Deduction eliminating a disjunct.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: orc syl.
    """
    lb = ProofBuilder(sys, "orcs")
    h1 = lb.hyp("orcs.1", "( ( ph ∨ ps ) -> ch )")
    s1 = lb.ref("s1", "( ph -> ( ph ∨ ps ) )", ref="orc", note="orc")
    res = lb.ref("res", "( ph -> ch )", s1, h1, ref="syl", note="syl orc, orcs.1")
    return lb.build(res)


def prove_oridm(sys: System) -> Proof:
    r"""oridm: ( ( ph \/ ph ) <-> ph ).

    Idempotent law for disjunction.  (Contributed by NM, 5-Aug-1993.)
    set.mm proof: pm1.2 pm2.07 impbii.
    """
    lb = ProofBuilder(sys, "oridm")
    s1 = lb.ref("s1", "( φ ∨ φ ) → φ", ref="pm1.2", note="pm1.2")
    s2 = lb.ref("s2", "φ → ( φ ∨ φ )", ref="pm2.07", note="pm2.07")
    res = lb.ref("res", "( φ ∨ φ ) ↔ φ", s1, s2, ref="impbii", note="impbii")
    return lb.build(res)


def prove_orim12i(sys: System) -> Proof:
    """orim12i: ( ( ph ∨ ch ) → ( ps ∨ th ) ).

    Inference joining disjuncts.  If the first implies the second
    and the third implies the fourth, the disjunction of the first
    and third implies the disjunction of the second and fourth.
    set.mm proof: orcd olcd jaoi.
    """
    lb = ProofBuilder(sys, "orim12i")
    h1 = lb.hyp("orim12i.1", "( ph -> ps )")
    h2 = lb.hyp("orim12i.2", "( ch -> th )")

    s1 = lb.ref("s1", "( ph -> ( ps ∨ th ) )", h1, ref="orcd", note="orcd(orim12i.1)")
    s2 = lb.ref("s2", "( ch -> ( ps ∨ th ) )", h2, ref="olcd", note="olcd(orim12i.2)")
    res = lb.ref("res", "( ( ph ∨ ch ) -> ( ps ∨ th ) )", s1, s2, ref="jaoi", note="jaoi")
    return lb.build(res)


def prove_orim1i(sys: System) -> Proof:
    r"""orim1i: ( ( ph \/ ch ) -> ( ps \/ ch ) ).

    Inference joining disjuncts.  If the first implies the second,
    the disjunction of the first and third implies the disjunction of
    the second and third.
    set.mm proof: id orim12i.
    """
    lb = ProofBuilder(sys, "orim1i")
    h1 = lb.hyp("orim1i.1", "( ph -> ps )")

    s1 = lb.ref("s1", "( ch -> ch )", ref="id", note="id")
    res = lb.ref("res", r"( ( ph \/ ch ) -> ( ps \/ ch ) )", h1, s1, ref="orim12i", note="orim12i")
    return lb.build(res)


def prove_orim2i(sys: System) -> Proof:
    r"""orim2i: ( ( ch \/ ph ) -> ( ch \/ ps ) ).

    Inference joining disjuncts.  If the second implies the third,
    the disjunction of the first and second implies the disjunction of
    the first and third.
    set.mm proof: id orim12i.
    """
    lb = ProofBuilder(sys, "orim2i")
    h1 = lb.hyp("orim2i.1", "( ph -> ps )")

    s1 = lb.ref("s1", "( ch -> ch )", ref="id", note="id")
    res = lb.ref("res", "( ( ch \\/ ph ) -> ( ch \\/ ps ) )", s1, h1, ref="orim12i", note="orim12i")
    return lb.build(res)


def prove_orimdi(sys: System) -> Proof:
    r"""orimdi: ( ( ph \/ ( ps -> ch ) ) <-> ( ( ph \/ ps ) -> ( ph \/ ch ) ) ).

    Distribution of disjunction over implication.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "orimdi")

    # imdi with ph := -. ph:
    # ( -. ph -> ( ps -> ch ) ) <-> ( ( -. ph -> ps ) -> ( -. ph -> ch ) )
    s1 = lb.ref(
        "s1",
        "( ( -. ph -> ( ps -> ch ) ) <-> ( ( -. ph -> ps ) -> ( -. ph -> ch ) ) )",
        ref="imdi",
        note="imdi",
    )

    # df-or with ps := (ps -> ch):
    # ( ph \/ ( ps -> ch ) ) <-> ( -. ph -> ( ps -> ch ) )
    s2 = lb.ref(
        "s2",
        r"( ( ph \/ ( ps -> ch ) ) <-> ( -. ph -> ( ps -> ch ) ) )",
        ref="df-or",
        note="df-or",
    )

    # df-or for the RHS components
    # ( ph \/ ps ) <-> ( -. ph -> ps )
    s3 = lb.ref(
        "s3",
        r"( ( ph \/ ps ) <-> ( -. ph -> ps ) )",
        ref="df-or",
        note="df-or",
    )
    # ( ph \/ ch ) <-> ( -. ph -> ch )
    s4 = lb.ref(
        "s4",
        r"( ( ph \/ ch ) <-> ( -. ph -> ch ) )",
        ref="df-or",
        note="df-or",
    )

    # imbi12i(df-or, df-or):
    # ( ( ph \/ ps ) -> ( ph \/ ch ) ) <-> ( ( -. ph -> ps ) -> ( -. ph -> ch ) )
    s5 = lb.ref(
        "s5",
        r"( ( ( ph \/ ps ) -> ( ph \/ ch ) ) <-> ( ( -. ph -> ps ) -> ( -. ph -> ch ) ) )",
        s3,
        s4,
        ref="imbi12i",
        note="imbi12i",
    )

    # 3bitr4i(s1, s2, s5):
    # ( ( ph \/ ( ps -> ch ) ) <-> ( ( ph \/ ps ) -> ( ph \/ ch ) ) )
    res = lb.ref(
        "res",
        r"( ( ph \/ ( ps -> ch ) ) <-> ( ( ph \/ ps ) -> ( ph \/ ch ) ) )",
        s1,
        s2,
        s5,
        ref="3bitr4i",
        note="3bitr4i",
    )
    return lb.build(res)


def prove_orbi2i(sys: System) -> Proof:
    """orbi2i: ( ( ch \\/ ph ) <-> ( ch \\/ ps ) ).

    Inference joining equivalent disjuncts.  If the second disjunct of the
    first is equivalent to the second disjunct of the second, the two
    disjunctions are equivalent.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: biimpi orim2i biimpri impbii.
    """
    lb = ProofBuilder(sys, "orbi2i")
    h1 = lb.hyp("orbi2i.1", "( ph <-> ps )")

    # biimpi: ( ph <-> ps ) -> ( ph -> ps )
    s1 = lb.ref("s1", "( ph -> ps )", h1, ref="biimpi", note="biimpi")

    # orim2i: ( ph -> ps ) -> ( ( ch \\/ ph ) -> ( ch \\/ ps ) )
    s2 = lb.ref("s2", "( ( ch \\/ ph ) -> ( ch \\/ ps ) )", s1, ref="orim2i", note="orim2i")

    # biimpri: ( ph <-> ps ) -> ( ps -> ph )
    s3 = lb.ref("s3", "( ps -> ph )", h1, ref="biimpri", note="biimpri")

    # orim2i: ( ps -> ph ) -> ( ( ch \\/ ps ) -> ( ch \\/ ph ) )
    s4 = lb.ref("s4", "( ( ch \\/ ps ) -> ( ch \\/ ph ) )", s3, ref="orim2i", note="orim2i")

    # impbii: combine the two directions
    res = lb.ref("res", "( ( ch \\/ ph ) <-> ( ch \\/ ps ) )", s2, s4, ref="impbii", note="impbii")

    return lb.build(res)


def prove_orbi1i(sys: System) -> Proof:
    """orbi1i: ( ( ph \\/ ch ) <-> ( ps \\/ ch ) ).

    Inference joining equivalent first disjuncts.  If the first
    disjunct of the first is equivalent to the first disjunct of the
    second, the two disjunctions are equivalent.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: orcom orbi2i 3bitri.
    """
    lb = ProofBuilder(sys, "orbi1i")
    h1 = lb.hyp("orbi1i.1", "( ph <-> ps )")

    # orcom: ( ( ph \\/ ch ) <-> ( ch \\/ ph ) )
    s1 = lb.ref("s1", "( ( ph \\/ ch ) <-> ( ch \\/ ph ) )", ref="orcom", note="orcom")

    # orbi2i: ( ph <-> ps ) -> ( ( ch \\/ ph ) <-> ( ch \\/ ps ) )
    s2 = lb.ref("s2", "( ( ch \\/ ph ) <-> ( ch \\/ ps ) )", h1, ref="orbi2i", note="orbi2i")

    # orcom: ( ( ch \\/ ps ) <-> ( ps \\/ ch ) )
    s3 = lb.ref("s3", "( ( ch \\/ ps ) <-> ( ps \\/ ch ) )", ref="orcom", note="orcom")

    # 3bitri: chain the three biconditionals
    res = lb.ref(
        "res", "( ( ph \\/ ch ) <-> ( ps \\/ ch ) )", s1, s2, s3, ref="3bitri", note="3bitri"
    )

    return lb.build(res)


def prove_orbi1(sys: System) -> Proof:
    """orbi1: (φ ↔ ψ) → ((φ ∨ χ) ↔ (ψ ∨ χ)).

    Theorem joining equivalent first disjuncts.  If the first
    disjunct of the first is equivalent to the first disjunct of the
    second, the two disjunctions are equivalent.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: id orbi1d.
    """
    lb = ProofBuilder(sys, "orbi1")

    # id: (φ ↔ ψ) → (φ ↔ ψ)
    s1 = lb.ref("s1", "(φ ↔ ψ) → (φ ↔ ψ)", ref="id", note="id")

    # orbi1d: ( (φ ↔ ψ) → (φ ↔ ψ) ) → ( (φ ↔ ψ) → ((φ ∨ χ) ↔ (ψ ∨ χ)) )
    res = lb.ref(
        "res",
        "(φ ↔ ψ) → ((φ ∨ χ) ↔ (ψ ∨ χ))",
        s1,
        ref="orbi1d",
        note="orbi1d",
    )

    return lb.build(res)


def prove_orbi12i(sys: System) -> Proof:
    r"""orbi12i: ( ( ph \/ ch ) <-> ( ps \/ th ) ).

    Inference joining two biconditionals with a disjunction.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: orbi2i orbi1i bitri.
    """
    lb = ProofBuilder(sys, "orbi12i")
    h1 = lb.hyp("orbi12i.1", "( ph <-> ps )")
    h2 = lb.hyp("orbi12i.2", "( ch <-> th )")

    # orbi2i: ( ch <-> th ) -> ( ( ph \/ ch ) <-> ( ph \/ th ) )
    s1 = lb.ref("s1", "( ( ph \\/ ch ) <-> ( ph \\/ th ) )", h2, ref="orbi2i", note="orbi2i")

    # orbi1i: ( ph <-> ps ) -> ( ( ph \/ th ) <-> ( ps \/ th ) )
    s2 = lb.ref("s2", "( ( ph \\/ th ) <-> ( ps \\/ th ) )", h1, ref="orbi1i", note="orbi1i")

    # bitri: combine the two biconditionals
    res = lb.ref("res", "( ( ph \\/ ch ) <-> ( ps \\/ th ) )", s1, s2, ref="bitri", note="bitri")

    return lb.build(res)


def prove_orbidi(sys: System) -> Proof:
    r"""orbidi: ( ( ph \/ ( ps <-> ch ) ) <-> ( ( ph \/ ps ) <-> ( ph \/ ch ) ) ).

    Distribution of disjunction over biconditional.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "orbidi")

    # pm5.74 with ph := -. ph:
    # ( -. ph -> ( ps <-> ch ) ) <-> ( ( -. ph -> ps ) <-> ( -. ph -> ch ) )
    s1 = lb.ref(
        "s1",
        "( ( -. ph -> ( ps <-> ch ) ) <-> ( ( -. ph -> ps ) <-> ( -. ph -> ch ) ) )",
        ref="pm5.74",
        note="pm5.74",
    )

    # df-or with ps := (ps <-> ch):
    # ( ph \/ ( ps <-> ch ) ) <-> ( -. ph -> ( ps <-> ch ) )
    s2 = lb.ref(
        "s2",
        r"( ( ph \/ ( ps <-> ch ) ) <-> ( -. ph -> ( ps <-> ch ) ) )",
        ref="df-or",
        note="df-or",
    )

    # df-or for the RHS components
    # ( ph \/ ps ) <-> ( -. ph -> ps )
    s3 = lb.ref(
        "s3",
        r"( ( ph \/ ps ) <-> ( -. ph -> ps ) )",
        ref="df-or",
        note="df-or",
    )
    # ( ph \/ ch ) <-> ( -. ph -> ch )
    s4 = lb.ref(
        "s4",
        r"( ( ph \/ ch ) <-> ( -. ph -> ch ) )",
        ref="df-or",
        note="df-or",
    )

    # bibi12i(s3, s4):
    # ( ( ph \/ ps ) <-> ( ph \/ ch ) ) <-> ( ( -. ph -> ps ) <-> ( -. ph -> ch ) )
    s5 = lb.ref(
        "s5",
        r"( ( ( ph \/ ps ) <-> ( ph \/ ch ) ) <-> ( ( -. ph -> ps ) <-> ( -. ph -> ch ) ) )",
        s3,
        s4,
        ref="bibi12i",
        note="bibi12i",
    )

    # 3bitr4i(s1, s2, s5):
    # ( ( ph \/ ( ps <-> ch ) ) <-> ( ( ph \/ ps ) <-> ( ph \/ ch ) ) )
    res = lb.ref(
        "res",
        r"( ( ph \/ ( ps <-> ch ) ) <-> ( ( ph \/ ps ) <-> ( ph \/ ch ) ) )",
        s1,
        s2,
        s5,
        ref="3bitr4i",
        note="3bitr4i",
    )
    return lb.build(res)


def prove_pm4_72(sys: System) -> Proof:
    r"""pm4.72: ( ( ph → ps ) ↔ ( ps ↔ ( ph ∨ ps ) ) ).

    Logical equivalence of implication and an equivalence with the disjunction.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm4.72")
    # First direction: ( ph → ps ) → ( ps ↔ ( ph ∨ ps ) )
    s1 = lb.ref("s1", "( ps → ( ph ∨ ps ) )", ref="olc", note="olc")
    s2 = lb.ref(
        "s2",
        "( ( ph → ps ) → ( ( ph ∨ ps ) → ps ) )",
        ref="pm2.621",
        note="pm2.621",
    )
    s3 = lb.ref(
        "s3",
        "( ( ph → ps ) → ( ps ↔ ( ph ∨ ps ) ) )",
        s1,
        s2,
        ref="impbid2",
        note="impbid2",
    )
    # Second direction: ( ps ↔ ( ph ∨ ps ) ) → ( ph → ps )
    s4 = lb.ref("s4", "( ph → ( ph ∨ ps ) )", ref="orc", note="orc")
    s5 = lb.ref(
        "s5",
        "( ( ps ↔ ( ph ∨ ps ) ) → ( ( ph ∨ ps ) → ps ) )",
        ref="biimpr",
        note="biimpr",
    )
    s6 = lb.ref(
        "s6",
        "( ( ps ↔ ( ph ∨ ps ) ) → ( ph → ps ) )",
        s4,
        s5,
        ref="syl5",
        note="syl5",
    )
    # Combine both directions
    res = lb.ref(
        "res",
        "( ( ph → ps ) ↔ ( ps ↔ ( ph ∨ ps ) ) )",
        s3,
        s6,
        ref="impbii",
        note="impbii",
    )
    return lb.build(res)


def prove_norbi(sys: System) -> Proof:
    """norbi: ( -. ( ph ∨ ps ) -> ( ph <-> ps ) ).

    If neither disjunct holds, the propositions are equivalent.
    set.mm proof: wo orc olc pm5.21ni.
    """
    lb = ProofBuilder(sys, "norbi")
    s1 = lb.ref("s1", "( ph -> ( ph ∨ ps ) )", ref="orc", note="orc")
    s2 = lb.ref("s2", "( ps -> ( ph ∨ ps ) )", ref="olc", note="olc(ps, ph)")
    res = lb.ref(
        "res", "( -. ( ph ∨ ps ) -> ( ph <-> ps ) )", s1, s2, ref="pm5.21ni", note="pm5.21ni"
    )
    return lb.build(res)


def prove_nbior(sys: System) -> Proof:
    r"""nbior: ( -. ( ph <-> ps ) -> ( ph \/ ps ) ).

    If propositions are not equivalent, one of them holds.
    set.mm proof: norbi con1i.
    """
    lb = ProofBuilder(sys, "nbior")
    s1 = lb.ref("s1", "( -. ( ph ∨ ps ) -> ( ph <-> ps ) )", ref="norbi", note="norbi")
    res = lb.ref("res", "( -. ( ph <-> ps ) -> ( ph ∨ ps ) )", s1, ref="con1i", note="con1i")
    return lb.build(res)


def prove_oibabs(sys: System) -> Proof:
    """oibabs: ( ( ( ph ∨ ps ) → ( ph <-> ps ) ) <-> ( ph <-> ps ) ).

    A biconditional form of oibabs.
    set.mm proof: norbi id ja ax-1 impbii.
    """
    lb = ProofBuilder(sys, "oibabs")

    # ja.1: ¬ ( ph ∨ ps ) → ( ph <-> ps )  [norbi]
    s1 = lb.ref("s1", "( -. ( ph ∨ ps ) -> ( ph <-> ps ) )", ref="norbi", note="norbi")

    # ja.2: ( ph <-> ps ) → ( ph <-> ps )  [id]
    s2 = lb.ref("s2", "( ( ph <-> ps ) -> ( ph <-> ps ) )", ref="id", note="id")

    # ja: ( ( ph ∨ ps ) → ( ph <-> ps ) ) → ( ph <-> ps )
    s3 = lb.ref(
        "s3", "( ( ( ph ∨ ps ) -> ( ph <-> ps ) ) -> ( ph <-> ps ) )", s1, s2, ref="ja", note="ja"
    )

    # ax-1: ( ph <-> ps ) → ( ( ph ∨ ps ) → ( ph <-> ps ) )
    s4 = lb.ref(
        "s4", "( ( ph <-> ps ) -> ( ( ph ∨ ps ) -> ( ph <-> ps ) ) )", ref="ax-1", note="ax-1"
    )

    # impbii: ( ( ( ph ∨ ps ) → ( ph <-> ps ) ) <-> ( ph <-> ps ) )
    res = lb.ref(
        "res",
        "( ( ( ph ∨ ps ) -> ( ph <-> ps ) ) <-> ( ph <-> ps ) )",
        s3,
        s4,
        ref="impbii",
        note="impbii",
    )

    return lb.build(res)


def prove_pm4_25(sys: System) -> Proof:
    r"""pm4.25: ( ph <-> ( ph \/ ph ) ).

    Commuted idempotent disjunction.  (Contributed by NM, 5-Aug-1993.)
    set.mm proof: oridm bicomi.
    """
    lb = ProofBuilder(sys, "pm4.25")
    s1 = lb.ref("s1", "( φ ∨ φ ) ↔ φ", ref="oridm", note="oridm")
    res = lb.ref("res", "φ <-> ( φ ∨ φ )", s1, ref="bicomi", note="bicomi")
    return lb.build(res)


def prove_pm4_42(sys: System) -> Proof:
    """pm4.42: φ ↔ ((φ ∧ ψ) ∨ (φ ∧ ¬ ψ)).

    Equivalence of a proposition to the disjunction of its conjunction
    with another proposition and its conjunction with the negation of
    that proposition.  Theorem *4.42 of [WhiteheadRussell] p. 119.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: dedlema dedlemb pm2.61i.
    """
    lb = ProofBuilder(sys, "pm4.42")

    s1 = lb.ref(
        "s1",
        "ψ → (φ ↔ ((φ ∧ ψ) ∨ (φ ∧ ¬ ψ)))",
        ref="dedlema",
        note="dedlema",
    )

    s2 = lb.ref(
        "s2",
        "¬ ψ → (φ ↔ ((φ ∧ ψ) ∨ (φ ∧ ¬ ψ)))",
        ref="dedlemb",
        note="dedlemb",
    )

    res = lb.ref(
        "res",
        "φ ↔ ((φ ∧ ψ) ∨ (φ ∧ ¬ ψ))",
        s1,
        s2,
        ref="pm2.61i",
        note="pm2.61i",
    )

    return lb.build(res)


def prove_pm4_43(sys: System) -> Proof:
    """pm4.43: φ ↔ ( ( φ ∨ ψ ) ∧ ( φ ∨ ¬ ψ ) ).

    Distribution of a disjunct over a conjunction, showing that a wff is
    equivalent to the conjunction of two disjunctions where the second
    disjunct alternates truth.  Theorem *4.43 of
    [WhiteheadRussell] p. 119.  (Contributed by NM, 5-Aug-1993.)
    set.mm proof: pm3.24 biorfri ordi bitri.
    """
    lb = ProofBuilder(sys, "pm4.43")

    s1 = lb.ref("s1", "¬ ( ψ ∧ ¬ ψ )", ref="pm3.24", note="pm3.24")

    s2 = lb.ref("s2", "φ ↔ ( φ ∨ ( ψ ∧ ¬ ψ ) )", s1, ref="biorfri", note="biorfri")

    s3 = lb.ref(
        "s3",
        "( φ ∨ ( ψ ∧ ¬ ψ ) ) ↔ ( ( φ ∨ ψ ) ∧ ( φ ∨ ¬ ψ ) )",
        ref="ordi",
        note="ordi",
    )

    res = lb.ref(
        "res",
        "φ ↔ ( ( φ ∨ ψ ) ∧ ( φ ∨ ¬ ψ ) )",
        s2,
        s3,
        ref="bitri",
        note="bitri",
    )

    return lb.build(res)


def prove_pm4_44(sys: System) -> Proof:
    """pm4.44: φ ↔ ( φ ∨ ( φ ∧ ψ ) ).

    Absorption of a conjunct by a disjunct.  Theorem *4.44 of
    [WhiteheadRussell] p. 119.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "pm4.44")
    s1 = lb.ref("s1", "φ → ( φ ∨ ( φ ∧ ψ ) )", ref="orc", note="orc")
    s2 = lb.ref("s2", "φ → φ", ref="id", note="id")
    s3 = lb.ref("s3", "( φ ∧ ψ ) → φ", ref="simpl", note="simpl")
    s4 = lb.ref("s4", "( φ ∨ ( φ ∧ ψ ) ) → φ", s2, s3, ref="jaoi", note="jaoi")
    res = lb.ref("res", "φ ↔ ( φ ∨ ( φ ∧ ψ ) )", s1, s4, ref="impbii", note="impbii")
    return lb.build(res)


def prove_orim12dALT(sys: System) -> Proof:
    """orim12dALT: ph → ( ( ps ∨ th ) → ( ch ∨ ta ) ).  Hyp: ph → ( ps → ch ), ph → ( th → ta ).

    Alternate deduction form of orim12.
    set.mm proof: wo wn wi pm2.53 con3d imim12d pm2.54 syl56.
    Under df-or: con3d then imim12d.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "orim12dALT")
    h1 = lb.hyp("orim12dALT.1", "ph → ( ps → ch )")
    h2 = lb.hyp("orim12dALT.2", "ph → ( th → ta )")
    res = lb.ref(
        "res",
        "ph → ( ( ps ∨ th ) → ( ch ∨ ta ) )",
        h1,
        h2,
        ref="orim12d",
        note="orim12d",
    )
    return lb.build(res)


def prove_3orbi123i(sys: System) -> Proof:
    r"""3orbi123i: ( ( ph \/ ch \/ ta ) <-> ( ps \/ th \/ et ) ).

    Inference joining three biconditionals with a disjunction.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: orbi12i df-3or 3bitr4i.
    """
    lb = ProofBuilder(sys, "3orbi123i")
    h1 = lb.hyp("3orbi123i.1", "( φ ↔ ψ )")
    h2 = lb.hyp("3orbi123i.2", "( χ ↔ θ )")
    h3 = lb.hyp("3orbi123i.3", "( τ ↔ η )")

    # orbi12i: combine h1 and h2
    s1 = lb.ref("s1", "( ( φ ∨ χ ) ↔ ( ψ ∨ θ ) )", h1, h2, ref="orbi12i", note="orbi12i")

    # orbi12i: combine s1 and h3
    s2 = lb.ref(
        "s2", "( ( ( φ ∨ χ ) ∨ τ ) ↔ ( ( ψ ∨ θ ) ∨ η ) )", s1, h3, ref="orbi12i", note="orbi12i"
    )

    # df-3or: expand left triple disjunction
    s3 = lb.ref("s3", "( ( φ ∨ χ ∨ τ ) ↔ ( ( φ ∨ χ ) ∨ τ ) )", ref="df-3or", note="df-3or")

    # df-3or: expand right triple disjunction
    s4 = lb.ref("s4", "( ( ψ ∨ θ ∨ η ) ↔ ( ( ψ ∨ θ ) ∨ η ) )", ref="df-3or", note="df-3or")

    # 3bitr4i: combine s2, s3, s4
    res = lb.ref(
        "res", "( ( φ ∨ χ ∨ τ ) ↔ ( ψ ∨ θ ∨ η ) )", s2, s3, s4, ref="3bitr4i", note="3bitr4i"
    )

    return lb.build(res)


def prove_3orbi123d(sys: System) -> Proof:
    r"""3orbi123d: φ → ((ψ ∨ θ ∨ η) ↔ (χ ∨ τ ∨ ζ)).

    Deduction joining three biconditionals with a disjunction.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: orbi12d df-3or 3bitr4g.
    """
    lb = ProofBuilder(sys, "3orbi123d")
    h1 = lb.hyp("3orbi123d.1", "φ → (ψ ↔ χ)")
    h2 = lb.hyp("3orbi123d.2", "φ → (θ ↔ τ)")
    h3 = lb.hyp("3orbi123d.3", "φ → (η ↔ ζ)")

    # orbi12d: combine h1 and h2
    s1 = lb.ref(
        "s1",
        "φ → ((ψ ∨ θ) ↔ (χ ∨ τ))",
        h1,
        h2,
        ref="orbi12d",
        note="orbi12d",
    )

    # orbi12d: combine s1 and h3
    s2 = lb.ref(
        "s2",
        "φ → (((ψ ∨ θ) ∨ η) ↔ ((χ ∨ τ) ∨ ζ))",
        s1,
        h3,
        ref="orbi12d",
        note="orbi12d",
    )

    # df-3or: expand left triple disjunction
    s3 = lb.ref(
        "s3",
        "((ψ ∨ θ ∨ η) ↔ ((ψ ∨ θ) ∨ η))",
        ref="df-3or",
        note="df-3or",
    )

    # df-3or: expand right triple disjunction
    s4 = lb.ref(
        "s4",
        "((χ ∨ τ ∨ ζ) ↔ ((χ ∨ τ) ∨ ζ))",
        ref="df-3or",
        note="df-3or",
    )

    # 3bitr4g: combine s2, s3, s4
    res = lb.ref(
        "res",
        "φ → ((ψ ∨ θ ∨ η) ↔ (χ ∨ τ ∨ ζ))",
        s2,
        s3,
        s4,
        ref="3bitr4g",
        note="3bitr4g",
    )

    return lb.build(res)


def prove_rb_ax1(sys: System) -> Proof:
    r"""rb-ax1: ( ¬ ( ¬ ψ ∨ χ ) ∨ ( ¬ ( φ ∨ ψ ) ∨ ( φ ∨ χ ) ) ).

    Russell-Bernays axiom 1.
    set.mm proof: orim2 imor 3imtr3i imori.
    """
    lb = ProofBuilder(sys, "rb-ax1")
    s1 = lb.ref("s1", "( ψ → χ ) → ( ( φ ∨ ψ ) → ( φ ∨ χ ) )", ref="orim2", note="orim2")
    s2 = lb.ref("s2", "( ψ → χ ) ↔ ( ¬ ψ ∨ χ )", ref="imor", note="imor")
    s3 = lb.ref(
        "s3", "( ( φ ∨ ψ ) → ( φ ∨ χ ) ) ↔ ( ¬ ( φ ∨ ψ ) ∨ ( φ ∨ χ ) )", ref="imor", note="imor"
    )
    s4 = lb.ref(
        "s4",
        "( ψ → χ ) → ( ¬ ( φ ∨ ψ ) ∨ ( φ ∨ χ ) )",
        s1,
        s3,
        ref="sylib",
        note="sylib orim2, imor",
    )
    s5 = lb.ref(
        "s5",
        "( ¬ ψ ∨ χ ) → ( ¬ ( φ ∨ ψ ) ∨ ( φ ∨ χ ) )",
        s2,
        s4,
        ref="sylbir",
        note="sylbir imor, sylib",
    )
    res = lb.ref(
        "res", "( ¬ ( ¬ ψ ∨ χ ) ∨ ( ¬ ( φ ∨ ψ ) ∨ ( φ ∨ χ ) ) )", s5, ref="imori", note="imori"
    )
    return lb.build(res)


def prove_rbsyl(sys: System) -> Proof:
    """rbsyl: φ ∨ χ.  Hyp: ¬ ψ ∨ χ, φ ∨ ψ.

    Russell-Bernays syllogism.
    set.mm proof: rb-ax1 anmp anmp.
    """
    lb = ProofBuilder(sys, "rbsyl")
    h1 = lb.hyp("rbsyl.1", "¬ ψ ∨ χ")
    h2 = lb.hyp("rbsyl.2", "φ ∨ ψ")
    s1 = lb.ref(
        "s1",
        "( ¬ ( ¬ ψ ∨ χ ) ∨ ( ¬ ( φ ∨ ψ ) ∨ ( φ ∨ χ ) ) )",
        ref="rb-ax1",
        note="rb-ax1",
    )
    s2 = lb.ref(
        "s2",
        "( ¬ ( φ ∨ ψ ) ∨ ( φ ∨ χ ) )",
        h1,
        s1,
        ref="anmp",
        note="anmp rbsyl.1, rb-ax1",
    )
    res = lb.ref(
        "res",
        "( φ ∨ χ )",
        h2,
        s2,
        ref="anmp",
        note="anmp rbsyl.2, s2",
    )
    return lb.build(res)


def prove_rb_ax2(sys: System) -> Proof:
    r"""rb-ax2: ( -. ( ph \/ ps ) \/ ( ps \/ ph ) ).

    Commuted form of the principle of the excluded middle.
    set.mm proof: pm1.4 con3i con1i orri.
    """
    lb = ProofBuilder(sys, "rb-ax2")
    s1 = lb.ref("s1", "( ph ∨ ps ) → ( ps ∨ ph )", ref="pm1.4", note="pm1.4")
    s2 = lb.ref("s2", "¬ ( ps ∨ ph ) → ¬ ( ph ∨ ps )", s1, ref="con3i", note="con3i")
    s3 = lb.ref("s3", "¬ ¬ ( ph ∨ ps ) → ( ps ∨ ph )", s2, ref="con1i", note="con1i")
    res = lb.ref("res", "( ¬ ( ph ∨ ps ) ∨ ( ps ∨ ph ) )", s3, ref="orri", note="orri")
    return lb.build(res)


def prove_rb_ax3(sys: System) -> Proof:
    r"""rb-ax3: ( -. ph \/ ( ps \/ ph ) ).

    Principle of the excluded middle with negation on the first disjunct.
    set.mm proof: pm2.46 con1i orri.
    """
    lb = ProofBuilder(sys, "rb-ax3")
    s1 = lb.ref("s1", "¬ ( ps ∨ ph ) → ¬ ph", ref="pm2.46", note="pm2.46")
    s2 = lb.ref("s2", "¬ ¬ ph → ( ps ∨ ph )", s1, ref="con1i", note="con1i")
    res = lb.ref("res", "( ¬ ph ∨ ( ps ∨ ph ) )", s2, ref="orri", note="orri")
    return lb.build(res)


def prove_rb_ax4(sys: System) -> Proof:
    r"""rb-ax4: ( -. ( ph \/ ph ) \/ ph ).

    Principle of idempotence for disjunction with negation.
    set.mm proof: pm1.2 con3i con1i orri.
    """
    lb = ProofBuilder(sys, "rb-ax4")
    s1 = lb.ref("s1", "( φ ∨ φ ) → φ", ref="pm1.2", note="pm1.2")
    s2 = lb.ref("s2", "¬ φ → ¬ ( φ ∨ φ )", s1, ref="con3i", note="con3i")
    s3 = lb.ref("s3", "¬ ¬ ( φ ∨ φ ) → φ", s2, ref="con1i", note="con1i")
    res = lb.ref("res", "( ¬ ( φ ∨ φ ) ∨ φ )", s3, ref="orri", note="orri")
    return lb.build(res)


def prove_rblem1(sys: System) -> Proof:
    """rblem1: ¬ ( φ ∨ χ ) ∨ ( ψ ∨ θ ).  Hyp: ¬ φ ∨ ψ, ¬ χ ∨ θ.

    Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
    """
    lb = ProofBuilder(sys, "rblem1")
    h1 = lb.hyp("rblem1.1", "¬ φ ∨ ψ")
    h2 = lb.hyp("rblem1.2", "¬ χ ∨ θ")

    # rb-ax1 with ψ→χ, χ→θ, φ→ψ
    s1 = lb.ref(
        "s1",
        "( ¬ ( ¬ χ ∨ θ ) ∨ ( ¬ ( ψ ∨ χ ) ∨ ( ψ ∨ θ ) ) )",
        ref="rb-ax1",
        note="rb-ax1",
    )

    # anmp: from rblem1.2 and rb-ax1 instance
    s2 = lb.ref(
        "s2",
        "( ¬ ( ψ ∨ χ ) ∨ ( ψ ∨ θ ) )",
        h2,
        s1,
        ref="anmp",
        note="anmp",
    )

    # rb-ax2 with φ→χ, ψ→ψ
    s3 = lb.ref(
        "s3",
        "( ¬ ( χ ∨ ψ ) ∨ ( ψ ∨ χ ) )",
        ref="rb-ax2",
        note="rb-ax2",
    )

    # rb-ax1 with ψ→φ, χ→ψ, φ→χ
    s4 = lb.ref(
        "s4",
        "( ¬ ( ¬ φ ∨ ψ ) ∨ ( ¬ ( χ ∨ φ ) ∨ ( χ ∨ ψ ) ) )",
        ref="rb-ax1",
        note="rb-ax1",
    )

    # anmp: from rblem1.1 and rb-ax1 instance
    s5 = lb.ref(
        "s5",
        "( ¬ ( χ ∨ φ ) ∨ ( χ ∨ ψ ) )",
        h1,
        s4,
        ref="anmp",
        note="anmp",
    )

    # rb-ax2 with φ→φ, ψ→χ
    s6 = lb.ref(
        "s6",
        "( ¬ ( φ ∨ χ ) ∨ ( χ ∨ φ ) )",
        ref="rb-ax2",
        note="rb-ax2",
    )

    # rbsyl: ¬ψ ∨ χ = s5, φ ∨ ψ = s6, result: φ ∨ χ
    s7 = lb.ref(
        "s7",
        "( ¬ ( φ ∨ χ ) ∨ ( χ ∨ ψ ) )",
        s5,
        s6,
        ref="rbsyl",
        note="rbsyl",
    )

    # rbsyl: ¬ψ ∨ χ = s3, φ ∨ ψ = s7, result: φ ∨ χ
    s8 = lb.ref(
        "s8",
        "( ¬ ( φ ∨ χ ) ∨ ( ψ ∨ χ ) )",
        s3,
        s7,
        ref="rbsyl",
        note="rbsyl",
    )

    # rbsyl: ¬ψ ∨ χ = s2, φ ∨ ψ = s8, result: φ ∨ χ
    res = lb.ref(
        "res",
        "( ¬ ( φ ∨ χ ) ∨ ( ψ ∨ θ ) )",
        s2,
        s8,
        ref="rbsyl",
        note="rbsyl",
    )

    return lb.build(res)


def prove_rblem2(sys: System) -> Proof:
    """rblem2: ¬ ( χ ∨ φ ) ∨ ( χ ∨ ( φ ∨ ψ ) ).

    Russell-Bernays theorem.
    """
    lb = ProofBuilder(sys, "rblem2")

    # rb-ax2 with φ→ψ, ψ→φ: ( ¬ ( ψ ∨ φ ) ∨ ( φ ∨ ψ ) )
    s1 = lb.ref(
        "s1",
        "( ¬ ( ψ ∨ φ ) ∨ ( φ ∨ ψ ) )",
        ref="rb-ax2",
        note="rb-ax2",
    )

    # rb-ax3: ( ¬ φ ∨ ( ψ ∨ φ ) )
    s2 = lb.ref(
        "s2",
        "( ¬ φ ∨ ( ψ ∨ φ ) )",
        ref="rb-ax3",
        note="rb-ax3",
    )

    # rbsyl: ( ¬ φ ∨ ( φ ∨ ψ ) )
    s3 = lb.ref(
        "s3",
        "( ¬ φ ∨ ( φ ∨ ψ ) )",
        s1,
        s2,
        ref="rbsyl",
        note="rbsyl",
    )

    # rb-ax1 with φ→χ, ψ→φ, χ→(φ∨ψ)
    s4 = lb.ref(
        "s4",
        "( ¬ ( ¬ φ ∨ ( φ ∨ ψ ) ) ∨ ( ¬ ( χ ∨ φ ) ∨ ( χ ∨ ( φ ∨ ψ ) ) ) )",
        ref="rb-ax1",
        note="rb-ax1",
    )

    # anmp
    res = lb.ref(
        "res",
        "( ¬ ( χ ∨ φ ) ∨ ( χ ∨ ( φ ∨ ψ ) ) )",
        s3,
        s4,
        ref="anmp",
        note="anmp",
    )

    return lb.build(res)


def prove_rblem3(sys: System) -> Proof:
    """rblem3: ¬ ( χ ∨ φ ) ∨ ( ( χ ∨ ψ ) ∨ φ ).

    Russell-Bernays theorem.
    """
    lb = ProofBuilder(sys, "rblem3")

    # Step 1: rb-ax2 with ph→φ, ps→(χ∨ψ)
    # ( ¬ ( φ ∨ ( χ ∨ ψ ) ) ∨ ( ( χ ∨ ψ ) ∨ φ ) )
    s1 = lb.ref(
        "s1",
        "( ¬ ( φ ∨ ( χ ∨ ψ ) ) ∨ ( ( χ ∨ ψ ) ∨ φ ) )",
        ref="rb-ax2",
        note="rb-ax2",
    )

    # Step 2: rblem2 with ch→φ, ph→χ, ps→ψ
    # ( ¬ ( φ ∨ χ ) ∨ ( φ ∨ ( χ ∨ ψ ) ) )
    s2 = lb.ref(
        "s2",
        "( ¬ ( φ ∨ χ ) ∨ ( φ ∨ ( χ ∨ ψ ) ) )",
        ref="rblem2",
        note="rblem2",
    )

    # Step 3: rb-ax2 with ph→χ, ps→φ
    # ( ¬ ( χ ∨ φ ) ∨ ( φ ∨ χ ) )
    s3 = lb.ref(
        "s3",
        "( ¬ ( χ ∨ φ ) ∨ ( φ ∨ χ ) )",
        ref="rb-ax2",
        note="rb-ax2",
    )

    # Step 4: rbsyl from s2 (¬ ψ ∨ χ) and s3 (φ ∨ ψ)
    # ( ¬ ( χ ∨ φ ) ∨ ( φ ∨ ( χ ∨ ψ ) ) )
    s4 = lb.ref(
        "s4",
        "( ¬ ( χ ∨ φ ) ∨ ( φ ∨ ( χ ∨ ψ ) ) )",
        s2,
        s3,
        ref="rbsyl",
        note="rbsyl",
    )

    # Step 5: rbsyl from s1 (¬ ψ ∨ χ) and s4 (φ ∨ ψ)
    # ( ¬ ( χ ∨ φ ) ∨ ( ( χ ∨ ψ ) ∨ φ ) )
    res = lb.ref(
        "res",
        "( ¬ ( χ ∨ φ ) ∨ ( ( χ ∨ ψ ) ∨ φ ) )",
        s1,
        s4,
        ref="rbsyl",
        note="rbsyl",
    )

    return lb.build(res)


def prove_rblem4(sys: System) -> Proof:
    """rblem4: ¬ ( ( φ ∨ ψ ) ∨ χ ) ∨ ( ( η ∨ τ ) ∨ θ ).

    Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
    """
    lb = ProofBuilder(sys, "rblem4")
    h1 = lb.hyp("rblem4.1", "¬ φ ∨ θ")
    h2 = lb.hyp("rblem4.2", "¬ ψ ∨ τ")
    h3 = lb.hyp("rblem4.3", "¬ χ ∨ η")

    # 3: rblem1(h3, h2) → ¬ ( χ ∨ ψ ) ∨ ( η ∨ τ )
    s3 = lb.ref(
        "s3",
        "( ¬ ( χ ∨ ψ ) ∨ ( η ∨ τ ) )",
        h3,
        h2,
        ref="rblem1",
        note="rblem1",
    )

    # 5: rblem1(s3, h1) → ¬ ( ( χ ∨ ψ ) ∨ φ ) ∨ ( ( η ∨ τ ) ∨ θ )
    s5 = lb.ref(
        "s5",
        "( ¬ ( ( χ ∨ ψ ) ∨ φ ) ∨ ( ( η ∨ τ ) ∨ θ ) )",
        s3,
        h1,
        ref="rblem1",
        note="rblem1",
    )

    # 6: rb-ax2 → ¬ ( φ ∨ ( χ ∨ ψ ) ) ∨ ( ( χ ∨ ψ ) ∨ φ )
    s6 = lb.ref(
        "s6",
        "( ¬ ( φ ∨ ( χ ∨ ψ ) ) ∨ ( ( χ ∨ ψ ) ∨ φ ) )",
        ref="rb-ax2",
        note="rb-ax2",
    )

    # 7: rb-ax2 → ¬ ( ψ ∨ χ ) ∨ ( χ ∨ ψ )
    s7 = lb.ref(
        "s7",
        "( ¬ ( ψ ∨ χ ) ∨ ( χ ∨ ψ ) )",
        ref="rb-ax2",
        note="rb-ax2",
    )

    # 8: rb-ax1 → ¬ ( ¬ ( ψ ∨ χ ) ∨ ( χ ∨ ψ ) ) ∨ ( ¬ ( φ ∨ ( ψ ∨ χ ) ) ∨ ( φ ∨ ( χ ∨ ψ ) ) )
    s8 = lb.ref(
        "s8",
        "( ¬ ( ¬ ( ψ ∨ χ ) ∨ ( χ ∨ ψ ) ) ∨ ( ¬ ( φ ∨ ( ψ ∨ χ ) ) ∨ ( φ ∨ ( χ ∨ ψ ) ) ) )",
        ref="rb-ax1",
        note="rb-ax1",
    )

    # 9: anmp(s7, s8) → ¬ ( φ ∨ ( ψ ∨ χ ) ) ∨ ( φ ∨ ( χ ∨ ψ ) )
    s9 = lb.ref(
        "s9",
        "( ¬ ( φ ∨ ( ψ ∨ χ ) ) ∨ ( φ ∨ ( χ ∨ ψ ) ) )",
        s7,
        s8,
        ref="anmp",
        note="anmp",
    )

    # 10: rb-ax2 → ¬ ( ( ψ ∨ χ ) ∨ φ ) ∨ ( φ ∨ ( ψ ∨ χ ) )
    s10 = lb.ref(
        "s10",
        "( ¬ ( ( ψ ∨ χ ) ∨ φ ) ∨ ( φ ∨ ( ψ ∨ χ ) ) )",
        ref="rb-ax2",
        note="rb-ax2",
    )

    # 11: rbsyl(s9, s10) → ¬ ( ( ψ ∨ χ ) ∨ φ ) ∨ ( φ ∨ ( χ ∨ ψ ) )
    s11 = lb.ref(
        "s11",
        "( ¬ ( ( ψ ∨ χ ) ∨ φ ) ∨ ( φ ∨ ( χ ∨ ψ ) ) )",
        s9,
        s10,
        ref="rbsyl",
        note="rbsyl",
    )

    # 12: rbsyl(s6, s11) → ¬ ( ( ψ ∨ χ ) ∨ φ ) ∨ ( ( χ ∨ ψ ) ∨ φ )
    s12 = lb.ref(
        "s12",
        "( ¬ ( ( ψ ∨ χ ) ∨ φ ) ∨ ( ( χ ∨ ψ ) ∨ φ ) )",
        s6,
        s11,
        ref="rbsyl",
        note="rbsyl",
    )

    # 13: rb-ax4 → ¬ ( ( ( ψ ∨ χ ) ∨ φ ) ∨ ( ( ψ ∨ χ ) ∨ φ ) ) ∨ ( ( ψ ∨ χ ) ∨ φ )
    s13 = lb.ref(
        "s13",
        "( ¬ ( ( ( ψ ∨ χ ) ∨ φ ) ∨ ( ( ψ ∨ χ ) ∨ φ ) ) ∨ ( ( ψ ∨ χ ) ∨ φ ) )",
        ref="rb-ax4",
        note="rb-ax4",
    )

    # 14: rb-ax2 → ¬ ( φ ∨ ( ψ ∨ χ ) ) ∨ ( ( ψ ∨ χ ) ∨ φ )
    s14 = lb.ref(
        "s14",
        "( ¬ ( φ ∨ ( ψ ∨ χ ) ) ∨ ( ( ψ ∨ χ ) ∨ φ ) )",
        ref="rb-ax2",
        note="rb-ax2",
    )

    # 15: rblem2 → ¬ ( φ ∨ ψ ) ∨ ( φ ∨ ( ψ ∨ χ ) )
    s15 = lb.ref(
        "s15",
        "( ¬ ( φ ∨ ψ ) ∨ ( φ ∨ ( ψ ∨ χ ) ) )",
        ref="rblem2",
        note="rblem2",
    )

    # 16: rbsyl(s14, s15) → ¬ ( φ ∨ ψ ) ∨ ( ( ψ ∨ χ ) ∨ φ )
    s16 = lb.ref(
        "s16",
        "( ¬ ( φ ∨ ψ ) ∨ ( ( ψ ∨ χ ) ∨ φ ) )",
        s14,
        s15,
        ref="rbsyl",
        note="rbsyl",
    )

    # 17: rb-ax3 → ¬ χ ∨ ( ψ ∨ χ )
    s17 = lb.ref(
        "s17",
        "( ¬ χ ∨ ( ψ ∨ χ ) )",
        ref="rb-ax3",
        note="rb-ax3",
    )

    # 18: rblem2 → ¬ ( ¬ χ ∨ ( ψ ∨ χ ) ) ∨ ( ¬ χ ∨ ( ( ψ ∨ χ ) ∨ φ ) )
    s18 = lb.ref(
        "s18",
        "( ¬ ( ¬ χ ∨ ( ψ ∨ χ ) ) ∨ ( ¬ χ ∨ ( ( ψ ∨ χ ) ∨ φ ) ) )",
        ref="rblem2",
        note="rblem2",
    )

    # 19: anmp(s17, s18) → ¬ χ ∨ ( ( ψ ∨ χ ) ∨ φ )
    s19 = lb.ref(
        "s19",
        "( ¬ χ ∨ ( ( ψ ∨ χ ) ∨ φ ) )",
        s17,
        s18,
        ref="anmp",
        note="anmp",
    )

    # 20: rblem1(s16, s19) → ¬ ( ( φ ∨ ψ ) ∨ χ ) ∨ ( ( ( ψ ∨ χ ) ∨ φ ) ∨ ( ( ψ ∨ χ ) ∨ φ ) )
    s20 = lb.ref(
        "s20",
        "( ¬ ( ( φ ∨ ψ ) ∨ χ ) ∨ ( ( ( ψ ∨ χ ) ∨ φ ) ∨ ( ( ψ ∨ χ ) ∨ φ ) ) )",
        s16,
        s19,
        ref="rblem1",
        note="rblem1",
    )

    # 21: rbsyl(s13, s20) → ¬ ( ( φ ∨ ψ ) ∨ χ ) ∨ ( ( ψ ∨ χ ) ∨ φ )
    s21 = lb.ref(
        "s21",
        "( ¬ ( ( φ ∨ ψ ) ∨ χ ) ∨ ( ( ψ ∨ χ ) ∨ φ ) )",
        s13,
        s20,
        ref="rbsyl",
        note="rbsyl",
    )

    # 22: rbsyl(s12, s21) → ¬ ( ( φ ∨ ψ ) ∨ χ ) ∨ ( ( χ ∨ ψ ) ∨ φ )
    s22 = lb.ref(
        "s22",
        "( ¬ ( ( φ ∨ ψ ) ∨ χ ) ∨ ( ( χ ∨ ψ ) ∨ φ ) )",
        s12,
        s21,
        ref="rbsyl",
        note="rbsyl",
    )

    # 23: rbsyl(s5, s22) → ¬ ( ( φ ∨ ψ ) ∨ χ ) ∨ ( ( η ∨ τ ) ∨ θ )
    res = lb.ref(
        "res",
        "( ¬ ( ( φ ∨ ψ ) ∨ χ ) ∨ ( ( η ∨ τ ) ∨ θ ) )",
        s5,
        s22,
        ref="rbsyl",
        note="rbsyl",
    )

    return lb.build(res)


def prove_rblem5(sys: System) -> Proof:
    """rblem5: ¬ ( ¬ ¬ φ ∨ ψ ) ∨ ( ¬ ¬ ψ ∨ φ ).

    Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
    """
    lb = ProofBuilder(sys, "rblem5")

    # rb-ax2 with φ→φ, ψ→¬¬ψ
    s1 = lb.ref(
        "s1",
        "( ¬ ( φ ∨ ¬ ¬ ψ ) ∨ ( ¬ ¬ ψ ∨ φ ) )",
        ref="rb-ax2",
        note="rb-ax2",
    )

    # rb-ax4 with φ→φ
    s2 = lb.ref(
        "s2",
        "( ¬ ( φ ∨ φ ) ∨ φ )",
        ref="rb-ax4",
        note="rb-ax4",
    )

    # rb-ax3 with φ→φ, ψ→φ
    s3 = lb.ref(
        "s3",
        "( ¬ φ ∨ ( φ ∨ φ ) )",
        ref="rb-ax3",
        note="rb-ax3",
    )

    # rbsyl: from s2 and s3
    s4 = lb.ref(
        "s4",
        "( ¬ φ ∨ φ )",
        s2,
        s3,
        ref="rbsyl",
        note="rbsyl",
    )

    # rb-ax4 with φ→¬¬φ
    s5 = lb.ref(
        "s5",
        "( ¬ ( ¬ ¬ φ ∨ ¬ ¬ φ ) ∨ ¬ ¬ φ )",
        ref="rb-ax4",
        note="rb-ax4",
    )

    # rb-ax3 with φ→¬¬φ, ψ→¬¬φ
    s6 = lb.ref(
        "s6",
        "( ¬ ¬ ¬ φ ∨ ( ¬ ¬ φ ∨ ¬ ¬ φ ) )",
        ref="rb-ax3",
        note="rb-ax3",
    )

    # rbsyl: from s5 and s6
    s7 = lb.ref(
        "s7",
        "( ¬ ¬ ¬ φ ∨ ¬ ¬ φ )",
        s5,
        s6,
        ref="rbsyl",
        note="rbsyl",
    )

    # rb-ax2 with φ→¬¬¬φ, ψ→¬¬φ
    s8 = lb.ref(
        "s8",
        "( ¬ ( ¬ ¬ ¬ φ ∨ ¬ ¬ φ ) ∨ ( ¬ ¬ φ ∨ ¬ ¬ ¬ φ ) )",
        ref="rb-ax2",
        note="rb-ax2",
    )

    # anmp: from s7 and s8
    s9 = lb.ref(
        "s9",
        "( ¬ ¬ φ ∨ ¬ ¬ ¬ φ )",
        s7,
        s8,
        ref="anmp",
        note="anmp",
    )

    # rblem1: from s9 and s4
    s11 = lb.ref(
        "s11",
        "( ¬ ( ¬ φ ∨ φ ) ∨ ( ¬ ¬ ¬ φ ∨ φ ) )",
        s9,
        s4,
        ref="rblem1",
        note="rblem1",
    )

    # anmp: from s4 and s11
    s12 = lb.ref(
        "s12",
        "( ¬ ¬ ¬ φ ∨ φ )",
        s4,
        s11,
        ref="anmp",
        note="anmp",
    )

    # rb-ax4 with φ→¬ψ
    s13 = lb.ref(
        "s13",
        "( ¬ ( ¬ ψ ∨ ¬ ψ ) ∨ ¬ ψ )",
        ref="rb-ax4",
        note="rb-ax4",
    )

    # rb-ax3 with φ→¬ψ, ψ→¬ψ
    s14 = lb.ref(
        "s14",
        "( ¬ ¬ ψ ∨ ( ¬ ψ ∨ ¬ ψ ) )",
        ref="rb-ax3",
        note="rb-ax3",
    )

    # rbsyl: from s13 and s14
    s15 = lb.ref(
        "s15",
        "( ¬ ¬ ψ ∨ ¬ ψ )",
        s13,
        s14,
        ref="rbsyl",
        note="rbsyl",
    )

    # rb-ax2 with φ→¬¬ψ, ψ→¬ψ
    s16 = lb.ref(
        "s16",
        "( ¬ ( ¬ ¬ ψ ∨ ¬ ψ ) ∨ ( ¬ ψ ∨ ¬ ¬ ψ ) )",
        ref="rb-ax2",
        note="rb-ax2",
    )

    # anmp: from s15 and s16
    s17 = lb.ref(
        "s17",
        "( ¬ ψ ∨ ¬ ¬ ψ )",
        s15,
        s16,
        ref="anmp",
        note="anmp",
    )

    # rblem1: from s12 and s17
    s18 = lb.ref(
        "s18",
        "( ¬ ( ¬ ¬ φ ∨ ψ ) ∨ ( φ ∨ ¬ ¬ ψ ) )",
        s12,
        s17,
        ref="rblem1",
        note="rblem1",
    )

    # rbsyl: from s1 and s18
    res = lb.ref(
        "res",
        "( ¬ ( ¬ ¬ φ ∨ ψ ) ∨ ( ¬ ¬ ψ ∨ φ ) )",
        s1,
        s18,
        ref="rbsyl",
        note="rbsyl",
    )

    return lb.build(res)


def prove_rblem6(sys: System) -> Proof:
    """rblem6: ¬ φ ∨ ψ.  Hyp: ¬ ( ¬ ( ¬ φ ∨ ψ ) ∨ ¬ ( ¬ ψ ∨ φ ) ).

    Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
    """
    lb = ProofBuilder(sys, "rblem6")
    h1 = lb.hyp("rblem6.1", "¬ ( ¬ ( ¬ φ ∨ ψ ) ∨ ¬ ( ¬ ψ ∨ φ ) )")

    # rb-ax3 with φ := ¬ ( ¬ φ ∨ ψ ), ψ := ¬ ( ¬ ψ ∨ φ )
    s1 = lb.ref(
        "s1",
        "( ¬ ¬ ( ¬ φ ∨ ψ ) ∨ ( ¬ ( ¬ ψ ∨ φ ) ∨ ¬ ( ¬ φ ∨ ψ ) ) )",
        ref="rb-ax3",
        note="rb-ax3",
    )

    # rb-ax2 with φ := ¬ ( ¬ ψ ∨ φ ), ψ := ¬ ( ¬ φ ∨ ψ )
    s2 = lb.ref(
        "s2",
        "( ¬ ( ¬ ( ¬ ψ ∨ φ ) ∨ ¬ ( ¬ φ ∨ ψ ) ) ∨ ( ¬ ( ¬ φ ∨ ψ ) ∨ ¬ ( ¬ ψ ∨ φ ) ) )",
        ref="rb-ax2",
        note="rb-ax2",
    )

    # rbsyl: from s1 (φ ∨ ψ) and s2 (¬ψ ∨ χ)
    s3 = lb.ref(
        "s3",
        "( ¬ ¬ ( ¬ φ ∨ ψ ) ∨ ( ¬ ( ¬ φ ∨ ψ ) ∨ ¬ ( ¬ ψ ∨ φ ) ) )",
        s2,
        s1,
        ref="rbsyl",
        note="rbsyl",
    )

    # rblem5 with φ := ( ¬ φ ∨ ψ ), ψ := ( ¬ ( ¬ φ ∨ ψ ) ∨ ¬ ( ¬ ψ ∨ φ ) )
    s4 = lb.ref(
        "s4",
        "( ¬ ( ¬ ¬ ( ¬ φ ∨ ψ ) ∨ ( ¬ ( ¬ φ ∨ ψ ) ∨ ¬ ( ¬ ψ ∨ φ ) ) ) ∨ ( ¬ ¬ ( ¬ ( ¬ φ ∨ ψ ) ∨ ¬ ( ¬ ψ ∨ φ ) ) ∨ ( ¬ φ ∨ ψ ) ) )",
        ref="rblem5",
        note="rblem5",
    )

    # anmp from s3 and s4
    s5 = lb.ref(
        "s5",
        "( ¬ ¬ ( ¬ ( ¬ φ ∨ ψ ) ∨ ¬ ( ¬ ψ ∨ φ ) ) ∨ ( ¬ φ ∨ ψ ) )",
        s3,
        s4,
        ref="anmp",
        note="anmp",
    )

    # anmp from hypothesis rblem6.1 and s5
    res = lb.ref(
        "res",
        "( ¬ φ ∨ ψ )",
        h1,
        s5,
        ref="anmp",
        note="anmp",
    )

    return lb.build(res)


def prove_rblem7(sys: System) -> Proof:
    """rblem7: ¬ ψ ∨ φ.  Hyp: ¬ ( ¬ ( ¬ φ ∨ ψ ) ∨ ¬ ( ¬ ψ ∨ φ ) ).

    Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
    """
    lb = ProofBuilder(sys, "rblem7")
    h1 = lb.hyp("rblem7.1", "¬ ( ¬ ( ¬ φ ∨ ψ ) ∨ ¬ ( ¬ ψ ∨ φ ) )")

    # rb-ax3 with φ := ¬ ( ¬ ψ ∨ φ ), ψ := ¬ ( ¬ φ ∨ ψ )
    s1 = lb.ref(
        "s1",
        "( ¬ ¬ ( ¬ ψ ∨ φ ) ∨ ( ¬ ( ¬ φ ∨ ψ ) ∨ ¬ ( ¬ ψ ∨ φ ) ) )",
        ref="rb-ax3",
        note="rb-ax3",
    )

    # rblem5 with φ := ( ¬ ψ ∨ φ ), ψ := ( ¬ ( ¬ φ ∨ ψ ) ∨ ¬ ( ¬ ψ ∨ φ ) )
    s2 = lb.ref(
        "s2",
        "( ¬ ( ¬ ¬ ( ¬ ψ ∨ φ ) ∨ ( ¬ ( ¬ φ ∨ ψ ) ∨ ¬ ( ¬ ψ ∨ φ ) ) )"
        " ∨ ( ¬ ¬ ( ¬ ( ¬ φ ∨ ψ ) ∨ ¬ ( ¬ ψ ∨ φ ) ) ∨ ( ¬ ψ ∨ φ ) ) )",
        ref="rblem5",
        note="rblem5",
    )

    # anmp from s1 and s2
    s3 = lb.ref(
        "s3",
        "( ¬ ¬ ( ¬ ( ¬ φ ∨ ψ ) ∨ ¬ ( ¬ ψ ∨ φ ) ) ∨ ( ¬ ψ ∨ φ ) )",
        s1,
        s2,
        ref="anmp",
        note="anmp",
    )

    # anmp from hypothesis rblem7.1 and s3
    res = lb.ref(
        "res",
        "( ¬ ψ ∨ φ )",
        h1,
        s3,
        ref="anmp",
        note="anmp",
    )

    return lb.build(res)


def prove_orass(sys: System) -> Proof:
    r"""orass: ( ( ( ph \/ ps ) \/ ch ) <-> ( ph \/ ( ps \/ ch ) ) ).

    Associative law for disjunction.
    (Contributed by NM, 27-Dec-1992.)
    set.mm proof: orcom or12 orbi2i 3bitri.
    """
    lb = ProofBuilder(sys, "orass")
    s1 = lb.ref(
        "s1", r"( ( ph \/ ps ) \/ ch ) <-> ( ch \/ ( ph \/ ps ) )", ref="orcom", note="orcom"
    )
    s2 = lb.ref("s2", r"( ch \/ ( ph \/ ps ) ) <-> ( ph \/ ( ch \/ ps ) )", ref="or12", note="or12")
    s3 = lb.ref("s3", r"( ch \/ ps ) <-> ( ps \/ ch )", ref="orcom", note="orcom")
    s4 = lb.ref(
        "s4", r"( ph \/ ( ch \/ ps ) ) <-> ( ph \/ ( ps \/ ch ) )", s3, ref="orbi2i", note="orbi2i"
    )
    res = lb.ref(
        "res",
        r"( ( ph \/ ps ) \/ ch ) <-> ( ph \/ ( ps \/ ch ) )",
        s1,
        s2,
        s4,
        ref="3bitri",
        note="3bitri",
    )
    return lb.build(res)


def prove_3orass(sys: System) -> Proof:
    r"""3orass: ( ( ph \/ ps \/ ch ) <-> ( ph \/ ( ps \/ ch ) ) ).

    Alternative definition of a triple disjunction, or 3-way disjunction.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: df-3or orass bitri.
    """
    lb = ProofBuilder(sys, "3orass")
    s1 = lb.ref(
        "s1", r"( ( ph \/ ps \/ ch ) <-> ( ( ph \/ ps ) \/ ch ) )", ref="df-3or", note="df-3or"
    )
    s2 = lb.ref(
        "s2", r"( ( ( ph \/ ps ) \/ ch ) <-> ( ph \/ ( ps \/ ch ) ) )", ref="orass", note="orass"
    )
    res = lb.ref(
        "res",
        r"( ( ph \/ ps \/ ch ) <-> ( ph \/ ( ps \/ ch ) ) )",
        s1,
        s2,
        ref="bitri",
        note="bitri",
    )
    return lb.build(res)


def prove_3orcoma(sys: System) -> Proof:
    r"""3orcoma: ( ( ph \/ ps \/ ch ) <-> ( ps \/ ph \/ ch ) ).

    Commutative law for triple disjunction: swap the first two disjuncts.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: or12 3orass 3bitr4i.
    """
    lb = ProofBuilder(sys, "3orcoma")
    s1 = lb.ref(
        "s1", r"( ( ph \/ ps \/ ch ) <-> ( ( ph \/ ps ) \/ ch ) )", ref="df-3or", note="df-3or"
    )
    s2 = lb.ref(
        "s2", r"( ( ps \/ ph \/ ch ) <-> ( ( ps \/ ph ) \/ ch ) )", ref="df-3or", note="df-3or"
    )
    swapped = lb.ref("swapped", r"( ( ph \/ ps ) <-> ( ps \/ ph ) )", ref="orcom", note="orcom")
    s3 = lb.ref(
        "s3",
        r"( ( ( ph \/ ps ) \/ ch ) <-> ( ( ps \/ ph ) \/ ch ) )",
        swapped,
        ref="orbi1i",
        note="orbi1i",
    )
    res = lb.ref(
        "res",
        r"( ( ph \/ ps \/ ch ) <-> ( ps \/ ph \/ ch ) )",
        s3,
        s1,
        s2,
        ref="3bitr4i",
        note="3bitr4i",
    )
    return lb.build(res)


def prove_3orcomb(sys: System) -> Proof:
    r"""3orcomb: ( ( ph \/ ps \/ ch ) <-> ( ph \/ ch \/ ps ) ).

    Commutative law for triple disjunction: swap the second and third disjuncts.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: 3orcoma 3orrot bitri.
    """
    lb = ProofBuilder(sys, "3orcomb")
    s1 = lb.ref(
        "s1", r"( ( ph \/ ps \/ ch ) <-> ( ps \/ ph \/ ch ) )", ref="3orcoma", note="3orcoma"
    )
    s2 = lb.ref("s2", r"( ( ps \/ ph \/ ch ) <-> ( ph \/ ch \/ ps ) )", ref="3orrot", note="3orrot")
    res = lb.ref(
        "res", r"( ( ph \/ ps \/ ch ) <-> ( ph \/ ch \/ ps ) )", s1, s2, ref="bitri", note="bitri"
    )
    return lb.build(res)


def prove_3orrot(sys: System) -> Proof:
    r"""3orrot: ( ( ph \/ ps \/ ch ) <-> ( ps \/ ch \/ ph ) ).

    Rotate the disjuncts of a triple disjunction.
    (Contributed by NM, 4-Apr-1995.)
    set.mm proof: orcom 3orass df-3or 3bitr4i.
    """
    lb = ProofBuilder(sys, "3orrot")
    s1 = lb.ref(
        "s1", r"( ( ph \/ ps \/ ch ) <-> ( ph \/ ( ps \/ ch ) ) )", ref="3orass", note="3orass"
    )
    s2 = lb.ref(
        "s2", r"( ( ps \/ ch \/ ph ) <-> ( ( ps \/ ch ) \/ ph ) )", ref="df-3or", note="df-3or"
    )
    s3 = lb.ref(
        "s3", r"( ( ph \/ ( ps \/ ch ) ) <-> ( ( ps \/ ch ) \/ ph ) )", ref="orcom", note="orcom"
    )
    res = lb.ref(
        "res",
        r"( ( ph \/ ps \/ ch ) <-> ( ps \/ ch \/ ph ) )",
        s3,
        s1,
        s2,
        ref="3bitr4i",
        note="3bitr4i",
    )
    return lb.build(res)


def prove_3or6(sys: System) -> Proof:
    """3or6: ((φ ∨ ψ) ∨ (χ ∨ θ) ∨ (τ ∨ η)) ↔ ((φ ∨ χ ∨ τ) ∨ (ψ ∨ θ ∨ η)).

    Rearrange disjuncts in a disjunction of six.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: or4 orbi1i bitri df-3or orbi12i 3bitr4i.
    """
    lb = ProofBuilder(sys, "3or6")

    # or4 (ph,ps,ch,th): ((φ ∨ ψ) ∨ (χ ∨ θ)) ↔ ((φ ∨ χ) ∨ (ψ ∨ θ))
    s1 = lb.ref(
        "s1",
        "((φ ∨ ψ) ∨ (χ ∨ θ)) ↔ ((φ ∨ χ) ∨ (ψ ∨ θ))",
        ref="or4",
        note="or4",
    )

    # orbi1i: add (τ ∨ η) as a disjunct to both sides
    s2 = lb.ref(
        "s2",
        "(((φ ∨ ψ) ∨ (χ ∨ θ)) ∨ (τ ∨ η)) ↔ (((φ ∨ χ) ∨ (ψ ∨ θ)) ∨ (τ ∨ η))",
        s1,
        ref="orbi1i",
        note="orbi1i",
    )

    # or4 ((φ ∨ χ),(ψ ∨ θ),τ,η)
    s3 = lb.ref(
        "s3",
        "(((φ ∨ χ) ∨ (ψ ∨ θ)) ∨ (τ ∨ η)) ↔ (((φ ∨ χ) ∨ τ) ∨ ((ψ ∨ θ) ∨ η))",
        ref="or4",
        note="or4",
    )

    # bitri: chain s2 and s3
    s4 = lb.ref(
        "s4",
        "(((φ ∨ ψ) ∨ (χ ∨ θ)) ∨ (τ ∨ η)) ↔ (((φ ∨ χ) ∨ τ) ∨ ((ψ ∨ θ) ∨ η))",
        s2,
        s3,
        ref="bitri",
        note="bitri",
    )

    # df-3or: expand left-hand triple disjunction
    s5 = lb.ref(
        "s5",
        "((φ ∨ ψ) ∨ (χ ∨ θ) ∨ (τ ∨ η)) ↔ (((φ ∨ ψ) ∨ (χ ∨ θ)) ∨ (τ ∨ η))",
        ref="df-3or",
        note="df-3or",
    )

    # df-3or: expand right-hand triple disjunctions, then combine with orbi12i
    s6a = lb.ref(
        "s6a",
        "(φ ∨ χ ∨ τ) ↔ ((φ ∨ χ) ∨ τ)",
        ref="df-3or",
        note="df-3or",
    )
    s6b = lb.ref(
        "s6b",
        "(ψ ∨ θ ∨ η) ↔ ((ψ ∨ θ) ∨ η)",
        ref="df-3or",
        note="df-3or",
    )
    s6 = lb.ref(
        "s6",
        "((φ ∨ χ ∨ τ) ∨ (ψ ∨ θ ∨ η)) ↔ (((φ ∨ χ) ∨ τ) ∨ ((ψ ∨ θ) ∨ η))",
        s6a,
        s6b,
        ref="orbi12i",
        note="orbi12i",
    )

    # 3bitr4i: combine inner equivalence with outer expansions
    res = lb.ref(
        "res",
        "((φ ∨ ψ) ∨ (χ ∨ θ) ∨ (τ ∨ η)) ↔ ((φ ∨ χ ∨ τ) ∨ (ψ ∨ θ ∨ η))",
        s4,
        s5,
        s6,
        ref="3bitr4i",
        note="3bitr4i",
    )

    return lb.build(res)


def prove_or4(sys: System) -> Proof:
    r"""or4: ( ( ( ph \/ ps ) \/ ( ch \/ th ) ) <-> ( ( ph \/ ch ) \/ ( ps \/ th ) ) ).

    Swap the order of disjuncts in a disjunction of four.
    (Contributed by NM, 25-Jan-1994.)
    set.mm proof: or12 orbi2i orass 3bitr4i.
    """
    lb = ProofBuilder(sys, "or4")
    s1 = lb.ref(
        "s1",
        r"( ( ( ph \/ ps ) \/ ( ch \/ th ) ) <-> ( ph \/ ( ps \/ ( ch \/ th ) ) ) )",
        ref="orass",
        note="orass",
    )
    s2 = lb.ref(
        "s2", r"( ( ps \/ ( ch \/ th ) ) <-> ( ch \/ ( ps \/ th ) ) )", ref="or12", note="or12"
    )
    s3 = lb.ref(
        "s3",
        r"( ( ph \/ ( ps \/ ( ch \/ th ) ) ) <-> ( ph \/ ( ch \/ ( ps \/ th ) ) ) )",
        s2,
        ref="orbi2i",
        note="orbi2i",
    )
    s4 = lb.ref(
        "s4",
        r"( ( ( ph \/ ch ) \/ ( ps \/ th ) ) <-> ( ph \/ ( ch \/ ( ps \/ th ) ) ) )",
        ref="orass",
        note="orass",
    )
    res = lb.ref(
        "res",
        r"( ( ( ph \/ ps ) \/ ( ch \/ th ) ) <-> ( ( ph \/ ch ) \/ ( ps \/ th ) ) )",
        s3,
        s1,
        s4,
        ref="3bitr4i",
        note="3bitr4i",
    )
    return lb.build(res)


def prove_or32(sys: System) -> Proof:
    r"""or32: ( ( ( ph \/ ps ) \/ ch ) <-> ( ( ph \/ ch ) \/ ps ) ).

    Swap the second and third disjuncts in a disjunction of three.
    (Contributed by NM, 11-Jul-2004.)
    set.mm proof: orass or12 orcom 3bitri.
    """
    lb = ProofBuilder(sys, "or32")
    s1 = lb.ref(
        "s1", r"( ( ph \/ ps ) \/ ch ) <-> ( ph \/ ( ps \/ ch ) )", ref="orass", note="orass"
    )
    s2 = lb.ref("s2", r"( ph \/ ( ps \/ ch ) ) <-> ( ps \/ ( ph \/ ch ) )", ref="or12", note="or12")
    s3 = lb.ref(
        "s3", r"( ps \/ ( ph \/ ch ) ) <-> ( ( ph \/ ch ) \/ ps )", ref="orcom", note="orcom"
    )
    res = lb.ref(
        "res",
        r"( ( ( ph \/ ps ) \/ ch ) <-> ( ( ph \/ ch ) \/ ps ) )",
        s1,
        s2,
        s3,
        ref="3bitri",
        note="3bitri",
    )
    return lb.build(res)


def prove_or42(sys: System) -> Proof:
    r"""or42: ( ( ( ph \/ ps ) \/ ( ch \/ th ) ) <-> ( ( ph \/ ch ) \/ ( th \/ ps ) ) ).

    Swap the second and fourth disjuncts in a disjunction of four.
    (Contributed by NM, 25-Jan-1994.)
    set.mm proof: or4 orcom orbi2i bitri.
    """
    lb = ProofBuilder(sys, "or42")
    s1 = lb.ref(
        "s1",
        r"( ( ( ph \/ ps ) \/ ( ch \/ th ) ) <-> ( ( ph \/ ch ) \/ ( ps \/ th ) ) )",
        ref="or4",
        note="or4",
    )
    s2 = lb.ref("s2", r"( ( ps \/ th ) <-> ( th \/ ps ) )", ref="orcom", note="orcom")
    s3 = lb.ref(
        "s3",
        r"( ( ( ph \/ ch ) \/ ( ps \/ th ) ) <-> ( ( ph \/ ch ) \/ ( th \/ ps ) ) )",
        s2,
        ref="orbi2i",
        note="orbi2i",
    )
    res = lb.ref(
        "res",
        r"( ( ( ph \/ ps ) \/ ( ch \/ th ) ) <-> ( ( ph \/ ch ) \/ ( th \/ ps ) ) )",
        s1,
        s3,
        ref="bitri",
        note="bitri",
    )
    return lb.build(res)


def prove_orordi(sys: System) -> Proof:
    r"""orordi: ( ( ph \/ ( ps \/ ch ) ) <-> ( ( ph \/ ps ) \/ ( ph \/ ch ) ) ).

    Distribution of disjunction over itself.
    set.mm proof: oridm orbi1i or4 bitr3i.
    """
    lb = ProofBuilder(sys, "orordi")
    s1 = lb.ref("s1", r"( ( ph \/ ph ) <-> ph )", ref="oridm", note="oridm")
    s2 = lb.ref(
        "s2",
        r"( ( ( ph \/ ph ) \/ ( ps \/ ch ) ) <-> ( ph \/ ( ps \/ ch ) ) )",
        s1,
        ref="orbi1i",
        note="orbi1i",
    )
    s3 = lb.ref(
        "s3",
        r"( ( ( ph \/ ph ) \/ ( ps \/ ch ) ) <-> ( ( ph \/ ps ) \/ ( ph \/ ch ) ) )",
        ref="or4",
        note="or4",
    )
    res = lb.ref(
        "res",
        r"( ( ph \/ ( ps \/ ch ) ) <-> ( ( ph \/ ps ) \/ ( ph \/ ch ) ) )",
        s2,
        s3,
        ref="bitr3i",
        note="bitr3i",
    )
    return lb.build(res)


def prove_orordir(sys: System) -> Proof:
    """orordir: ( ( φ ∨ ψ ) ∨ χ ) ↔ ( ( φ ∨ χ ) ∨ ( ψ ∨ χ ) ).

    Distribution of disjunction over itself, right-hand variant.
    set.mm proof: oridm orbi2i or4 bitr3i.
    """
    lb = ProofBuilder(sys, "orordir")
    s1 = lb.ref("s1", "( χ ∨ χ ) ↔ χ", ref="oridm", note="oridm")
    s2 = lb.ref(
        "s2", "( ( φ ∨ ψ ) ∨ ( χ ∨ χ ) ) ↔ ( ( φ ∨ ψ ) ∨ χ )", s1, ref="orbi2i", note="orbi2i"
    )
    s3 = lb.ref(
        "s3", "( ( φ ∨ ψ ) ∨ ( χ ∨ χ ) ) ↔ ( ( φ ∨ χ ) ∨ ( ψ ∨ χ ) )", ref="or4", note="or4"
    )
    res = lb.ref(
        "res", "( ( φ ∨ ψ ) ∨ χ ) ↔ ( ( φ ∨ χ ) ∨ ( ψ ∨ χ ) )", s2, s3, ref="bitr3i", note="bitr3i"
    )
    return lb.build(res)


def prove_ordi(sys: System) -> Proof:
    """ordi: ( φ ∨ ( ψ ∧ χ ) ) ↔ ( ( φ ∨ ψ ) ∧ ( φ ∨ χ ) ).

    Distribution of disjunction over conjunction.
    """
    lb = ProofBuilder(sys, "ordi")

    s1 = lb.ref(
        "s1",
        "( ¬ φ → ( ψ ∧ χ ) ) ↔ ( ( ¬ φ → ψ ) ∧ ( ¬ φ → χ ) )",
        ref="jcab",
        note="jcab",
    )

    s2 = lb.ref(
        "s2",
        "( φ ∨ ( ψ ∧ χ ) ) ↔ ( ¬ φ → ( ψ ∧ χ ) )",
        ref="df-or",
        note="df-or",
    )

    s3 = lb.ref(
        "s3",
        "( φ ∨ ψ ) ↔ ( ¬ φ → ψ )",
        ref="df-or",
        note="df-or",
    )

    s4 = lb.ref(
        "s4",
        "( φ ∨ χ ) ↔ ( ¬ φ → χ )",
        ref="df-or",
        note="df-or",
    )

    s5 = lb.ref(
        "s5",
        "( ( φ ∨ ψ ) ∧ ( φ ∨ χ ) ) ↔ ( ( ¬ φ → ψ ) ∧ ( ¬ φ → χ ) )",
        s3,
        s4,
        ref="anbi12i",
        note="anbi12i",
    )

    res = lb.ref(
        "res",
        "( φ ∨ ( ψ ∧ χ ) ) ↔ ( ( φ ∨ ψ ) ∧ ( φ ∨ χ ) )",
        s1,
        s2,
        s5,
        ref="3bitr4i",
        note="3bitr4i",
    )

    return lb.build(res)


def prove_ordir(sys: System) -> Proof:
    """ordir: ( ( φ ∧ ψ ) ∨ χ ) ↔ ( ( φ ∨ χ ) ∧ ( ψ ∨ χ ) ).

    Distribution of disjunction over conjunction, right-hand variant.
    """
    lb = ProofBuilder(sys, "ordir")

    s1 = lb.ref(
        "s1",
        "( χ ∨ ( φ ∧ ψ ) ) ↔ ( ( χ ∨ φ ) ∧ ( χ ∨ ψ ) )",
        ref="ordi",
        note="ordi",
    )

    s2 = lb.ref(
        "s2",
        "( ( φ ∧ ψ ) ∨ χ ) ↔ ( χ ∨ ( φ ∧ ψ ) )",
        ref="orcom",
        note="orcom",
    )

    s3 = lb.ref(
        "s3",
        "( φ ∨ χ ) ↔ ( χ ∨ φ )",
        ref="orcom",
        note="orcom",
    )

    s4 = lb.ref(
        "s4",
        "( ψ ∨ χ ) ↔ ( χ ∨ ψ )",
        ref="orcom",
        note="orcom",
    )

    s5 = lb.ref(
        "s5",
        "( ( φ ∨ χ ) ∧ ( ψ ∨ χ ) ) ↔ ( ( χ ∨ φ ) ∧ ( χ ∨ ψ ) )",
        s3,
        s4,
        ref="anbi12i",
        note="anbi12i",
    )

    res = lb.ref(
        "res",
        "( ( φ ∧ ψ ) ∨ χ ) ↔ ( ( φ ∨ χ ) ∧ ( ψ ∨ χ ) )",
        s1,
        s2,
        s5,
        ref="3bitr4i",
        note="3bitr4i",
    )

    return lb.build(res)


def prove_3mix1(sys: System) -> Proof:
    r"""3mix1: ( ph -> ( ph \/ ps \/ ch ) ).

    The first of three disjuncts implies the triple disjunction.
    set.mm proof: orc 3orass sylibr.
    """
    lb = ProofBuilder(sys, "3mix1")
    s1 = lb.ref("s1", r"( ph -> ( ph \/ ( ps \/ ch ) ) )", ref="orc", note="orc")
    s2 = lb.ref(
        "s2", r"( ( ph \/ ps \/ ch ) <-> ( ph \/ ( ps \/ ch ) ) )", ref="3orass", note="3orass"
    )
    res = lb.ref("res", r"( ph -> ( ph \/ ps \/ ch ) )", s1, s2, ref="sylibr", note="sylibr")
    return lb.build(res)


def prove_3mix1d(sys: System) -> Proof:
    r"""3mix1d: ( ph -> ( ps \/ ch \/ th ) ).  Hyp: ( ph -> ps ).

    Deduction version of ~ 3mix1 .
    set.mm proof: w3o 3mix1 syl.
    """
    lb = ProofBuilder(sys, "3mix1d")
    h1 = lb.hyp("3mix1d.1", "( ph -> ps )")
    s1 = lb.ref("s1", r"( ps -> ( ps \/ ch \/ th ) )", ref="3mix1", note="3mix1")
    res = lb.ref("res", r"( ph -> ( ps \/ ch \/ th ) )", h1, s1, ref="syl", note="syl 3mix1d.1, s1")
    return lb.build(res)


def prove_3mix1i(sys: System) -> Proof:
    r"""3mix1i: ( ph \/ ps \/ ch ).  Hyp: ph.

    Inference form of ~ 3mix1 .
    set.mm proof: w3o 3mix1 ax-mp.
    """
    lb = ProofBuilder(sys, "3mix1i")
    h1 = lb.hyp("3mixi.1", "ph")
    s1 = lb.ref("s1", r"( ph -> ( ph \/ ps \/ ch ) )", ref="3mix1", note="3mix1")
    res = lb.mp("res", h1, s1, note="MP 3mixi.1, 3mix1 => ax-mp")
    return lb.build(res)


def prove_3mix2(sys: System) -> Proof:
    r"""3mix2: ( ph -> ( ps \/ ph \/ ch ) ).

    The second of three disjuncts implies the triple disjunction.
    set.mm proof: 3mix1 3orrot sylibr.
    """
    lb = ProofBuilder(sys, "3mix2")
    s1 = lb.ref("s1", r"( ph -> ( ph \/ ch \/ ps ) )", ref="3mix1", note="3mix1")
    s2 = lb.ref("s2", r"( ( ps \/ ph \/ ch ) <-> ( ph \/ ch \/ ps ) )", ref="3orrot", note="3orrot")
    res = lb.ref("res", r"( ph -> ( ps \/ ph \/ ch ) )", s1, s2, ref="sylibr", note="sylibr")
    return lb.build(res)


def prove_3mix2i(sys: System) -> Proof:
    r"""3mix2i: ( ps \/ ph \/ ch ).  Hyp: ph.

    Inference form of ~ 3mix2 .
    set.mm proof: w3o 3mix2 ax-mp.
    """
    lb = ProofBuilder(sys, "3mix2i")
    h1 = lb.hyp("3mixi.1", "ph")
    s1 = lb.ref("s1", r"( ph -> ( ps \/ ph \/ ch ) )", ref="3mix2", note="3mix2")
    res = lb.mp("res", h1, s1, note="MP 3mixi.1, 3mix2 => ax-mp")
    return lb.build(res)


def prove_3mix2d(sys: System) -> Proof:
    r"""3mix2d: ( ph -> ( ch \/ ps \/ th ) ).  Hyp: ( ph -> ps ).

    Deduction version of ~ 3mix2 .
    set.mm proof: w3o 3mix2 syl.
    """
    lb = ProofBuilder(sys, "3mix2d")
    h1 = lb.hyp("3mix2d.1", "( ph -> ps )")
    s1 = lb.ref("s1", r"( ps -> ( ch \/ ps \/ th ) )", ref="3mix2", note="3mix2")
    res = lb.ref("res", r"( ph -> ( ch \/ ps \/ th ) )", h1, s1, ref="syl", note="syl 3mix2d.1, s1")
    return lb.build(res)


def prove_3mix3(sys: System) -> Proof:
    r"""3mix3: ( ph -> ( ps \/ ch \/ ph ) ).

    The third of three disjuncts implies the triple disjunction.
    set.mm proof: 3mix1 3orrot sylib.
    """
    lb = ProofBuilder(sys, "3mix3")
    s1 = lb.ref("s1", r"( ph -> ( ph \/ ps \/ ch ) )", ref="3mix1", note="3mix1")
    s2 = lb.ref("s2", r"( ( ph \/ ps \/ ch ) <-> ( ps \/ ch \/ ph ) )", ref="3orrot", note="3orrot")
    res = lb.ref("res", r"( ph -> ( ps \/ ch \/ ph ) )", s1, s2, ref="sylib", note="sylib")
    return lb.build(res)


def prove_3mix3d(sys: System) -> Proof:
    r"""3mix3d: ( ph -> ( ch \/ th \/ ps ) ).  Hyp: ( ph -> ps ).

    Deduction version of ~ 3mix3 .
    set.mm proof: w3o 3mix3 syl.
    """
    lb = ProofBuilder(sys, "3mix3d")
    h1 = lb.hyp("3mix3d.1", "( ph -> ps )")
    s1 = lb.ref("s1", r"( ps -> ( ch \/ th \/ ps ) )", ref="3mix3", note="3mix3")
    res = lb.ref("res", r"( ph -> ( ch \/ th \/ ps ) )", h1, s1, ref="syl", note="syl 3mix3d.1, s1")
    return lb.build(res)


def prove_3mix3i(sys: System) -> Proof:
    r"""3mix3i: ( ps \/ ch \/ ph ).  Hyp: ph.

    Inference form of ~ 3mix3 .
    set.mm proof: w3o 3mix3 ax-mp.
    """
    lb = ProofBuilder(sys, "3mix3i")
    h1 = lb.hyp("3mixi.1", "ph")
    s1 = lb.ref("s1", r"( ph -> ( ps \/ ch \/ ph ) )", ref="3mix3", note="3mix3")
    res = lb.mp("res", h1, s1, note="MP 3mixi.1, 3mix3 => ax-mp")
    return lb.build(res)


def prove_pm5_14(sys: System) -> Proof:
    """pm5.14: ( ( φ → ψ ) ∨ ( ψ → χ ) ).

    Theorem *5.14 of [WhiteheadRussell] p. 123.
    set.mm proof: pm2.521g orri.
    """
    lb = ProofBuilder(sys, "pm5.14")
    s1 = lb.ref("s1", "( -. ( φ → ψ ) → ( ψ → χ ) )", ref="pm2.521g", note="pm2.521g")
    res = lb.ref("res", "( ( φ → ψ ) ∨ ( ψ → χ ) )", s1, ref="orri", note="orri")
    return lb.build(res)


def prove_pm5_13(sys: System) -> Proof:
    """pm5.13: ( ( φ → ψ ) ∨ ( ψ → φ ) ).

    Theorem *5.13 of [WhiteheadRussell] p. 123.
    set.mm proof: pm5.14 ABAC.
    """
    lb = ProofBuilder(sys, "pm5.13")
    res = lb.ref("res", "( ( φ → ψ ) ∨ ( ψ → φ ) )", ref="pm5.14", note="pm5.14")
    return lb.build(res)


def prove_pm5_15(sys: System) -> Proof:
    """pm5.15: ( ( φ ↔ ψ ) ∨ ( φ ↔ ¬ ψ ) ).

    Either two propositions are equivalent or the first is equivalent to
    the negation of the second.  (Contributed by NM, 5-Aug-1993.)
    set.mm proof: xor3 biimpi orri.
    """
    lb = ProofBuilder(sys, "pm5.15")
    s_xor3 = lb.ref(
        "s_xor3",
        "( ¬ ( φ ↔ ψ ) ↔ ( φ ↔ ¬ ψ ) )",
        ref="xor3",
        note="xor3",
    )
    s_impl = lb.ref(
        "s_impl",
        "( ¬ ( φ ↔ ψ ) → ( φ ↔ ¬ ψ ) )",
        s_xor3,
        ref="biimpi",
        note="biimpi xor3",
    )
    res = lb.ref(
        "res",
        "( ( φ ↔ ψ ) ∨ ( φ ↔ ¬ ψ ) )",
        s_impl,
        ref="orri",
        note="orri",
    )
    return lb.build(res)


def prove_pm5_17(sys: System) -> Proof:
    """pm5.17: ( ( φ ∨ ψ ) ∧ ¬ ( φ ∧ ψ ) ) ↔ ( φ ↔ ¬ ψ ).

    Exclusive or expressed as equivalence to a negated biconditional.
    """
    lb = ProofBuilder(sys, "pm5.17")

    # bicom: ( φ ↔ ¬ ψ ) ↔ ( ¬ ψ ↔ φ )
    s1 = lb.ref("s1", "( φ ↔ ¬ ψ ) ↔ ( ¬ ψ ↔ φ )", ref="bicom", note="bicom")

    # dfbi2: ( ¬ ψ ↔ φ ) ↔ ( ( ¬ ψ → φ ) ∧ ( φ → ¬ ψ ) )
    s2 = lb.ref(
        "s2",
        "( ¬ ψ ↔ φ ) ↔ ( ( ¬ ψ → φ ) ∧ ( φ → ¬ ψ ) )",
        ref="dfbi2",
        note="dfbi2",
    )

    # orcom: ( φ ∨ ψ ) ↔ ( ψ ∨ φ )
    s3 = lb.ref("s3", "( φ ∨ ψ ) ↔ ( ψ ∨ φ )", ref="orcom", note="orcom")

    # df-or: ( ψ ∨ φ ) ↔ ( ¬ ψ → φ )
    s4 = lb.ref("s4", "( ψ ∨ φ ) ↔ ( ¬ ψ → φ )", ref="df-or", note="df-or")

    # bitr2i: combine s3 and s4 to get ( ¬ ψ → φ ) ↔ ( φ ∨ ψ )
    s5 = lb.ref("s5", "( ¬ ψ → φ ) ↔ ( φ ∨ ψ )", s3, s4, ref="bitr2i", note="bitr2i")

    # imnan: ( φ → ¬ ψ ) ↔ ¬ ( φ ∧ ψ )
    s6 = lb.ref("s6", "( φ → ¬ ψ ) ↔ ¬ ( φ ∧ ψ )", ref="imnan", note="imnan")

    # anbi12i: combine s5 and s6
    s7 = lb.ref(
        "s7",
        "( ( ¬ ψ → φ ) ∧ ( φ → ¬ ψ ) ) ↔ ( ( φ ∨ ψ ) ∧ ¬ ( φ ∧ ψ ) )",
        s5,
        s6,
        ref="anbi12i",
        note="anbi12i",
    )

    # 3bitrri: chain s1, s2, s7 to get the result
    res = lb.ref(
        "res",
        "( ( φ ∨ ψ ) ∧ ¬ ( φ ∧ ψ ) ) ↔ ( φ ↔ ¬ ψ )",
        s1,
        s2,
        s7,
        ref="3bitrri",
        note="3bitrri",
    )

    return lb.build(res)


def prove_pm5_55(sys: System) -> Proof:
    r"""pm5.55: ( ( ( ph \/ ps ) <-> ph ) \/ ( ( ph \/ ps ) <-> ps ) ).

    Either a disjunction is equivalent to the first disjunct or to the
    second.  (Contributed by NM, 5-Aug-1993.)
    set.mm proof: biort bicomd biorf nsyl5 orri.
    """
    lb = ProofBuilder(sys, "pm5.55")

    # biort: ( ph -> ( ph <-> ( ph \/ ps ) ) )
    s1 = lb.ref("s1", r"( ph -> ( ph <-> ( ph \/ ps ) ) )", ref="biort", note="biort")

    # bicomd: ( ph -> ( ( ph \/ ps ) <-> ph ) )
    s2 = lb.ref(
        "s2",
        r"( ph -> ( ( ph \/ ps ) <-> ph ) )",
        s1,
        ref="bicomd",
        note="bicomd",
    )

    # biorf: ( -. ph -> ( ps <-> ( ph \/ ps ) ) )
    s3 = lb.ref(
        "s3",
        r"( -. ph -> ( ps <-> ( ph \/ ps ) ) )",
        ref="biorf",
        note="biorf",
    )

    # bicomd: ( -. ph -> ( ( ph \/ ps ) <-> ps ) )
    s4 = lb.ref(
        "s4",
        r"( -. ph -> ( ( ph \/ ps ) <-> ps ) )",
        s3,
        ref="bicomd",
        note="bicomd",
    )

    # nsyl5: ( -. ( ( ph \/ ps ) <-> ph ) -> ( ( ph \/ ps ) <-> ps ) )
    s5 = lb.ref(
        "s5",
        r"( -. ( ( ph \/ ps ) <-> ph ) -> ( ( ph \/ ps ) <-> ps ) )",
        s2,
        s4,
        ref="nsyl5",
        note="nsyl5",
    )

    # orri: ( ( ( ph \/ ps ) <-> ph ) \/ ( ( ph \/ ps ) <-> ps ) )
    res = lb.ref(
        "res",
        r"( ( ( ph \/ ps ) <-> ph ) \/ ( ( ph \/ ps ) <-> ps ) )",
        s5,
        ref="orri",
        note="orri",
    )

    return lb.build(res)


def prove_imimorb(sys: System) -> Proof:
    r"""imimorb: ( ( ( ps -> ch ) -> ( ph -> ch ) ) <-> ( ph -> ( ps \/ ch ) ) ).

    Equivalence of an implication with a disjunction in the consequent.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: bi2.04 dfor2 imbi2i bitr4i.
    """
    lb = ProofBuilder(sys, "imimorb")

    # bi2.04 with ph := (ps -> ch), ps := ph, ch := ch:
    # ( ( ps -> ch ) -> ( ph -> ch ) ) <-> ( ph -> ( ( ps -> ch ) -> ch ) )
    s1 = lb.ref(
        "s1",
        r"( ( ps -> ch ) -> ( ph -> ch ) ) <-> ( ph -> ( ( ps -> ch ) -> ch ) )",
        ref="bi2.04",
        note="bi2.04",
    )

    # dfor2 with ph := ps, ps := ch:
    # ( ps \/ ch ) <-> ( ( ps -> ch ) -> ch )
    s2 = lb.ref(
        "s2",
        r"( ps \/ ch ) <-> ( ( ps -> ch ) -> ch )",
        ref="dfor2",
        note="dfor2",
    )

    # imbi2i with antecedent ph on s2:
    # ( ph -> ( ps \/ ch ) ) <-> ( ph -> ( ( ps -> ch ) -> ch ) )
    s3 = lb.ref(
        "s3",
        r"( ph -> ( ps \/ ch ) ) <-> ( ph -> ( ( ps -> ch ) -> ch ) )",
        s2,
        ref="imbi2i",
        note="imbi2i",
    )

    # bitr4i: combine s1 and s3, both share RHS ( ph -> ( ( ps -> ch ) -> ch ) )
    res = lb.ref(
        "res",
        r"( ( ps -> ch ) -> ( ph -> ch ) ) <-> ( ph -> ( ps \/ ch ) )",
        s1,
        s3,
        ref="bitr4i",
        note="bitr4i",
    )
    return lb.build(res)


def prove_3bior1fd(sys: System) -> Proof:
    r"""3bior1fd: ( ph -> ( ( ch \/ ps ) <-> ( th \/ ch \/ ps ) ) ).

    Deduction form of ~ 3bior1f .  (Contributed by NM, 5-Aug-1993.)
    set.mm proof: biorf syl 3orass bitr4di.
    """
    lb = ProofBuilder(sys, "3bior1fd")
    h1 = lb.hyp("3biorfd.1", r"( ph -> -. th )")

    # biorf: ( -. th -> ( ( ch \/ ps ) <-> ( th \/ ( ch \/ ps ) ) ) )
    s1 = lb.ref(
        "s1",
        r"( -. th -> ( ( ch \/ ps ) <-> ( th \/ ( ch \/ ps ) ) ) )",
        ref="biorf",
        note="biorf",
    )

    # syl: ( ph -> ( ( ch \/ ps ) <-> ( th \/ ( ch \/ ps ) ) ) )
    s2 = lb.ref(
        "s2",
        r"( ph -> ( ( ch \/ ps ) <-> ( th \/ ( ch \/ ps ) ) ) )",
        h1,
        s1,
        ref="syl",
        note="syl",
    )

    # 3orass: ( ( th \/ ch \/ ps ) <-> ( th \/ ( ch \/ ps ) ) )
    s3 = lb.ref(
        "s3",
        r"( ( th \/ ch \/ ps ) <-> ( th \/ ( ch \/ ps ) ) )",
        ref="3orass",
        note="3orass",
    )

    # bitr4di: ( ph -> ( ( ch \/ ps ) <-> ( th \/ ch \/ ps ) ) )
    res = lb.ref(
        "res",
        r"( ph -> ( ( ch \/ ps ) <-> ( th \/ ch \/ ps ) ) )",
        s2,
        s3,
        ref="bitr4di",
        note="bitr4di",
    )

    return lb.build(res)


def prove_3bior1fand(sys: System) -> Proof:
    """3bior1fand: φ → ((χ ∨ ψ) ↔ ((θ ∧ τ) ∨ χ ∨ ψ)).

    Deduction form of ~ 3bior1fan: introduce a conjunction on the
    left of a ternary disjunction.
    (Contributed by NM, 5-Jan-1993.)
    set.mm proof: intnanrd 3bior1fd.
    """
    lb = ProofBuilder(sys, "3bior1fand")
    h1 = lb.hyp("3biorfd.1", "φ → ¬ θ")

    # intnanrd: φ → ¬ (θ ∧ τ)
    s1 = lb.ref(
        "s1",
        "φ → ¬ (θ ∧ τ)",
        h1,
        ref="intnanrd",
        note="intnanrd",
    )

    # 3bior1fd: φ → ((χ ∨ ψ) ↔ ((θ ∧ τ) ∨ χ ∨ ψ))
    res = lb.ref(
        "res",
        "φ → ((χ ∨ ψ) ↔ ((θ ∧ τ) ∨ χ ∨ ψ))",
        s1,
        ref="3bior1fd",
        note="3bior1fd",
    )

    return lb.build(res)


def prove_3bior2fd(sys: System) -> Proof:
    r"""3bior2fd: ( ph -> ( ps <-> ( th \/ ch \/ ps ) ) ).

    Deduction form of ~ 3bior2f .
    set.mm proof: biorf syl 3bior1fd bitrd.
    """
    lb = ProofBuilder(sys, "3bior2fd")
    h1 = lb.hyp("3biorfd.1", r"( ph -> -. th )")
    h2 = lb.hyp("3biorfd.2", r"( ph -> -. ch )")

    # biorf: ( -. ch -> ( ps <-> ( ch \/ ps ) ) )
    s1 = lb.ref(
        "s1",
        r"( -. ch -> ( ps <-> ( ch \/ ps ) ) )",
        ref="biorf",
        note="biorf",
    )

    # syl: ( ph -> ( ps <-> ( ch \/ ps ) ) )
    s2 = lb.ref(
        "s2",
        r"( ph -> ( ps <-> ( ch \/ ps ) ) )",
        h2,
        s1,
        ref="syl",
        note="syl",
    )

    # 3bior1fd: ( ph -> ( ( ch \/ ps ) <-> ( th \/ ch \/ ps ) ) )
    s3 = lb.ref(
        "s3",
        r"( ph -> ( ( ch \/ ps ) <-> ( th \/ ch \/ ps ) ) )",
        h1,
        ref="3bior1fd",
        note="3bior1fd",
    )

    # bitrd: ( ph -> ( ps <-> ( th \/ ch \/ ps ) ) )
    res = lb.ref(
        "res",
        r"( ph -> ( ps <-> ( th \/ ch \/ ps ) ) )",
        s2,
        s3,
        ref="bitrd",
        note="bitrd",
    )

    return lb.build(res)


def prove_norasslem1(sys: System) -> Proof:
    """norasslem1: ( ( ( ph \\/ ps ) -> ch ) <-> ( ( ph -\\/ ps ) \\/ ch ) ).

    Equivalence of an implication with negated first condition and an
    equivalent disjunction of a NOR.
    set.mm proof: imor df-nor orbi1i bitr4i.
    """
    lb = ProofBuilder(sys, "norasslem1")

    # s1: imor -> ( ( ( ph \\/ ps ) -> ch ) <-> ( -. ( ph \\/ ps ) \\/ ch ) )
    s1 = lb.ref(
        "s1",
        r"( ( ( ph \/ ps ) -> ch ) <-> ( -. ( ph \/ ps ) \/ ch ) )",
        ref="imor",
        note="imor",
    )

    # s2: df-nor -> ( ( ph -\/ ps ) <-> -. ( ph \\/ ps ) )
    s2 = lb.ref(
        "s2",
        r"( ( ph -\/ ps ) <-> -. ( ph \/ ps ) )",
        ref="df-nor",
        note="df-nor",
    )

    # s3: orbi1i(s2) -> ( ( ( ph -\\/ ps ) \\/ ch ) <-> ( -. ( ph \\/ ps ) \\/ ch ) )
    s3 = lb.ref(
        "s3",
        r"( ( ( ph -\/ ps ) \/ ch ) <-> ( -. ( ph \/ ps ) \/ ch ) )",
        s2,
        ref="orbi1i",
        note="orbi1i",
    )

    # res: bitr4i(s1, s3) -> ( ( ( ph \\/ ps ) -> ch ) <-> ( ( ph -\\/ ps ) \\/ ch ) )
    res = lb.ref(
        "res",
        r"( ( ( ph \/ ps ) -> ch ) <-> ( ( ph -\/ ps ) \/ ch ) )",
        s1,
        s3,
        ref="bitr4i",
        note="bitr4i",
    )

    return lb.build(res)


def prove_norasslem2(sys: System) -> Proof:
    """norasslem2: φ → (ψ ↔ ((φ ∨ χ) → ψ)).

    If the first antecedent holds, then a consequent is equivalent to
    the implication of its disjunction with another antecedent and itself.
    """
    lb = ProofBuilder(sys, "norasslem2")

    # biimt with ph := (φ ∨ χ): (φ ∨ χ) → (ψ ↔ ((φ ∨ χ) → ψ))
    s1 = lb.ref(
        "s1",
        "( φ ∨ χ ) → ( ψ ↔ ( ( φ ∨ χ ) → ψ ) )",
        ref="biimt",
        note="biimt",
    )

    # orcs: φ → (ψ ↔ ((φ ∨ χ) → ψ))
    res = lb.ref(
        "res",
        "φ → ( ψ ↔ ( ( φ ∨ χ ) → ψ ) )",
        s1,
        ref="orcs",
        note="orcs",
    )

    return lb.build(res)


def prove_norasslem3(sys: System) -> Proof:
    """norasslem3: ¬ φ → ( ( ψ → χ ) ↔ ( ( φ ∨ ψ ) → χ ) ).

    If the first antecedent is false, then the implication of a second
    wff to a third is equivalent to the implication of the disjunction
    of the first and second to the third.
    set.mm proof: biorf imbi1d.
    """
    lb = ProofBuilder(sys, "norasslem3")

    # biorf: ( ¬ φ → ( ψ ↔ ( φ ∨ ψ ) ) )
    s1 = lb.ref(
        "s1",
        "( ¬ φ → ( ψ ↔ ( φ ∨ ψ ) ) )",
        ref="biorf",
        note="biorf",
    )

    # imbi1d: ( ¬ φ → ( ( ψ → χ ) ↔ ( ( φ ∨ ψ ) → χ ) ) )
    res = lb.ref(
        "res",
        "( ¬ φ → ( ( ψ → χ ) ↔ ( ( φ ∨ ψ ) → χ ) ) )",
        s1,
        ref="imbi1d",
        note="imbi1d",
    )
    return lb.build(res)


def prove_norcom(sys: System) -> Proof:
    """norcom: (φ ⊽ ψ) ↔ (ψ ⊽ φ).

    Commutativity of the NOR operator.
    set.mm proof: df-nor orcom xchbinx bitr4i.
    """
    lb = ProofBuilder(sys, "norcom")

    # df-nor: ( φ ⊽ ψ ) ↔ ¬ ( φ ∨ ψ )
    s1 = lb.ref(
        "s1",
        "( φ ⊽ ψ ) ↔ ¬ ( φ ∨ ψ )",
        ref="df-nor",
        note="df-nor",
    )

    # orcom: ( φ ∨ ψ ) ↔ ( ψ ∨ φ )
    s2 = lb.ref(
        "s2",
        "( φ ∨ ψ ) ↔ ( ψ ∨ φ )",
        ref="orcom",
        note="orcom",
    )

    # xchbinx(s1, s2): ( φ ⊽ ψ ) ↔ ¬ ( ψ ∨ φ )
    s3 = lb.ref(
        "s3",
        "( φ ⊽ ψ ) ↔ ¬ ( ψ ∨ φ )",
        s1,
        s2,
        ref="xchbinx",
        note="xchbinx",
    )

    # df-nor with swapped args: ( ψ ⊽ φ ) ↔ ¬ ( ψ ∨ φ )
    s4 = lb.ref(
        "s4",
        "( ψ ⊽ φ ) ↔ ¬ ( ψ ∨ φ )",
        ref="df-nor",
        note="df-nor(ps, ph)",
    )

    # bitr4i(s3, s4): ( φ ⊽ ψ ) ↔ ( ψ ⊽ φ )
    res = lb.ref(
        "res",
        "( φ ⊽ ψ ) ↔ ( ψ ⊽ φ )",
        s3,
        s4,
        ref="bitr4i",
        note="bitr4i",
    )

    return lb.build(res)


def prove_norass(sys: System) -> Proof:
    """norass: ( φ ↔ χ ) ↔ ( ( ( φ ⊽ ψ ) ⊽ χ ) ↔ ( φ ⊽ ( ψ ⊽ χ ) ) ).

    Associativity-like property of joint denial (NOR) with respect to
    equivalence.  (Contributed by RP, 29-Oct-2023.)
    (Proof shortened by Wolf Lammen, 17-Dec-2023.)
    set.mm proof: notbi norasslem1 bibi12i bicom norasslem2 bibi12d bitrid
    impimprbi norasslem3 pm2.61i 3bitr4i df-nor norcom orbi1i orcom.
    """
    lb = ProofBuilder(sys, "norass")

    # notbi(( ( φ ⊽ ψ ) ∨ χ ), ( φ ∨ ( ψ ⊽ χ ) ))
    s_notbi = lb.ref(
        "s_notbi",
        "( ( ( φ ⊽ ψ ) ∨ χ ) ↔ ( φ ∨ ( ψ ⊽ χ ) ) ) ↔ ( ¬ ( ( φ ⊽ ψ ) ∨ χ ) ↔ ¬ ( φ ∨ ( ψ ⊽ χ ) ) )",
        ref="notbi",
        note="notbi",
    )

    # norasslem1(ψ, φ, χ)
    s_nl1a = lb.ref(
        "s_nl1a",
        "( ( ψ ∨ φ ) → χ ) ↔ ( ( ψ ⊽ φ ) ∨ χ )",
        ref="norasslem1",
        note="norasslem1(ps, ph, ch)",
    )

    # norasslem1(ψ, χ, φ)
    s_nl1b = lb.ref(
        "s_nl1b",
        "( ( ψ ∨ χ ) → φ ) ↔ ( ( ψ ⊽ χ ) ∨ φ )",
        ref="norasslem1",
        note="norasslem1(ps, ch, ph)",
    )

    # bibi12i(s_nl1a, s_nl1b)
    s_bbi12i1 = lb.ref(
        "s_bbi12i1",
        "( ( ( ψ ∨ φ ) → χ ) ↔ ( ( ψ ∨ χ ) → φ ) ) ↔ ( ( ( ψ ⊽ φ ) ∨ χ ) ↔ ( ( ψ ⊽ χ ) ∨ φ ) )",
        s_nl1a,
        s_nl1b,
        ref="bibi12i",
        note="bibi12i",
    )

    # bicom(φ, χ)
    s_bicom = lb.ref(
        "s_bicom",
        "( φ ↔ χ ) ↔ ( χ ↔ φ )",
        ref="bicom",
        note="bicom",
    )

    # norasslem2(ψ, χ, φ)
    s_nl2a = lb.ref(
        "s_nl2a",
        "ψ → ( χ ↔ ( ( ψ ∨ φ ) → χ ) )",
        ref="norasslem2",
        note="norasslem2(ps, ch, ph)",
    )

    # norasslem2(ψ, φ, χ)
    s_nl2b = lb.ref(
        "s_nl2b",
        "ψ → ( φ ↔ ( ( ψ ∨ χ ) → φ ) )",
        ref="norasslem2",
        note="norasslem2(ps, ph, ch)",
    )

    # bibi12d(s_nl2a, s_nl2b)
    s_bbi12d1 = lb.ref(
        "s_bbi12d1",
        "ψ → ( ( χ ↔ φ ) ↔ ( ( ( ψ ∨ φ ) → χ ) ↔ ( ( ψ ∨ χ ) → φ ) ) )",
        s_nl2a,
        s_nl2b,
        ref="bibi12d",
        note="bibi12d",
    )

    # bitrid(s_bicom, s_bbi12d1)
    s_bitrid1 = lb.ref(
        "s_bitrid1",
        "ψ → ( ( φ ↔ χ ) ↔ ( ( ( ψ ∨ φ ) → χ ) ↔ ( ( ψ ∨ χ ) → φ ) ) )",
        s_bicom,
        s_bbi12d1,
        ref="bitrid",
        note="bitrid",
    )

    # impimprbi(φ, χ)
    s_impimprbi = lb.ref(
        "s_impimprbi",
        "( φ ↔ χ ) ↔ ( ( φ → χ ) ↔ ( χ → φ ) )",
        ref="impimprbi",
        note="impimprbi",
    )

    # norasslem3(ψ, φ, χ)
    s_nl3a = lb.ref(
        "s_nl3a",
        "¬ ψ → ( ( φ → χ ) ↔ ( ( ψ ∨ φ ) → χ ) )",
        ref="norasslem3",
        note="norasslem3(ps, ph, ch)",
    )

    # norasslem3(ψ, χ, φ)
    s_nl3b = lb.ref(
        "s_nl3b",
        "¬ ψ → ( ( χ → φ ) ↔ ( ( ψ ∨ χ ) → φ ) )",
        ref="norasslem3",
        note="norasslem3(ps, ch, ph)",
    )

    # bibi12d(s_nl3a, s_nl3b)
    s_bbi12d2 = lb.ref(
        "s_bbi12d2",
        "¬ ψ → ( ( ( φ → χ ) ↔ ( χ → φ ) ) ↔ ( ( ( ψ ∨ φ ) → χ ) ↔ ( ( ψ ∨ χ ) → φ ) ) )",
        s_nl3a,
        s_nl3b,
        ref="bibi12d",
        note="bibi12d",
    )

    # bitrid(s_impimprbi, s_bbi12d2)
    s_bitrid2 = lb.ref(
        "s_bitrid2",
        "¬ ψ → ( ( φ ↔ χ ) ↔ ( ( ( ψ ∨ φ ) → χ ) ↔ ( ( ψ ∨ χ ) → φ ) ) )",
        s_impimprbi,
        s_bbi12d2,
        ref="bitrid",
        note="bitrid",
    )

    # pm2.61i(s_bitrid1, s_bitrid2)
    s_pm261i = lb.ref(
        "s_pm261i",
        "( φ ↔ χ ) ↔ ( ( ( ψ ∨ φ ) → χ ) ↔ ( ( ψ ∨ χ ) → φ ) )",
        s_bitrid1,
        s_bitrid2,
        ref="pm2.61i",
        note="pm2.61i",
    )

    # norcom(φ, ψ)
    s_norcom = lb.ref(
        "s_norcom",
        "( φ ⊽ ψ ) ↔ ( ψ ⊽ φ )",
        ref="norcom",
        note="norcom",
    )

    # orbi1i(s_norcom, χ)
    s_orbi1i = lb.ref(
        "s_orbi1i",
        "( ( φ ⊽ ψ ) ∨ χ ) ↔ ( ( ψ ⊽ φ ) ∨ χ )",
        s_norcom,
        ref="orbi1i",
        note="orbi1i",
    )

    # orcom(φ, (ψ ⊽ χ))
    s_orcom = lb.ref(
        "s_orcom",
        "( φ ∨ ( ψ ⊽ χ ) ) ↔ ( ( ψ ⊽ χ ) ∨ φ )",
        ref="orcom",
        note="orcom",
    )

    # bibi12i(s_orbi1i, s_orcom)
    s_bbi12i2 = lb.ref(
        "s_bbi12i2",
        "( ( ( φ ⊽ ψ ) ∨ χ ) ↔ ( φ ∨ ( ψ ⊽ χ ) ) ) ↔ ( ( ( ψ ⊽ φ ) ∨ χ ) ↔ ( ( ψ ⊽ χ ) ∨ φ ) )",
        s_orbi1i,
        s_orcom,
        ref="bibi12i",
        note="bibi12i",
    )

    # 3bitr4i(s_bbi12i1, s_pm261i, s_bbi12i2)
    s_3bitr4i1 = lb.ref(
        "s_3bitr4i1",
        "( φ ↔ χ ) ↔ ( ( ( φ ⊽ ψ ) ∨ χ ) ↔ ( φ ∨ ( ψ ⊽ χ ) ) )",
        s_bbi12i1,
        s_pm261i,
        s_bbi12i2,
        ref="3bitr4i",
        note="3bitr4i",
    )

    # df-nor((φ ⊽ ψ), χ)
    s_dfnor1 = lb.ref(
        "s_dfnor1",
        "( ( φ ⊽ ψ ) ⊽ χ ) ↔ ¬ ( ( φ ⊽ ψ ) ∨ χ )",
        ref="df-nor",
        note="df-nor",
    )

    # df-nor(φ, (ψ ⊽ χ))
    s_dfnor2 = lb.ref(
        "s_dfnor2",
        "( φ ⊽ ( ψ ⊽ χ ) ) ↔ ¬ ( φ ∨ ( ψ ⊽ χ ) )",
        ref="df-nor",
        note="df-nor",
    )

    # bibi12i(s_dfnor1, s_dfnor2)
    s_bbi12i3 = lb.ref(
        "s_bbi12i3",
        "( ( ( φ ⊽ ψ ) ⊽ χ ) ↔ ( φ ⊽ ( ψ ⊽ χ ) ) ) ↔ ( ¬ ( ( φ ⊽ ψ ) ∨ χ ) ↔ ¬ ( φ ∨ ( ψ ⊽ χ ) ) )",
        s_dfnor1,
        s_dfnor2,
        ref="bibi12i",
        note="bibi12i",
    )

    # 3bitr4i(s_notbi, s_3bitr4i1, s_bbi12i3)
    res = lb.ref(
        "res",
        "( φ ↔ χ ) ↔ ( ( ( φ ⊽ ψ ) ⊽ χ ) ↔ ( φ ⊽ ( ψ ⊽ χ ) ) )",
        s_notbi,
        s_3bitr4i1,
        s_bbi12i3,
        ref="3bitr4i",
        note="3bitr4i",
    )

    return lb.build(res)


def prove_orbi2d(sys: System) -> Proof:
    """orbi2d: φ → ((θ ∨ ψ) ↔ (θ ∨ χ)).  Hyp: φ → (ψ ↔ χ).

    Deduction form of orbi2i.
    set.mm proof: imbi2d df-or 3bitr4g.
    """
    lb = ProofBuilder(sys, "orbi2d")
    h1 = lb.hyp("orbi2d.1", "φ → (ψ ↔ χ)")

    s1 = lb.ref(
        "s1",
        "φ → ((¬ θ → ψ) ↔ (¬ θ → χ))",
        h1,
        ref="imbi2d",
        note="imbi2d(orbi2d.1)",
    )

    s2 = lb.ref(
        "s2",
        "((θ ∨ ψ) ↔ (¬ θ → ψ))",
        ref="df-or",
        note="df-or",
    )

    s3 = lb.ref(
        "s3",
        "((θ ∨ χ) ↔ (¬ θ → χ))",
        ref="df-or",
        note="df-or",
    )

    res = lb.ref(
        "res",
        "φ → ((θ ∨ ψ) ↔ (θ ∨ χ))",
        s1,
        s2,
        s3,
        ref="3bitr4g",
        note="3bitr4g",
    )

    return lb.build(res)


def prove_orbi1d(sys: System) -> Proof:
    """orbi1d: φ → ((ψ ∨ θ) ↔ (χ ∨ θ)).  Hyp: φ → (ψ ↔ χ).

    Deduction form of orbi1i.
    set.mm proof: orbi2d orcom 3bitr4g.
    """
    lb = ProofBuilder(sys, "orbi1d")
    h1 = lb.hyp("orbi1d.1", "φ → (ψ ↔ χ)")

    s1 = lb.ref(
        "s1",
        "φ → ((θ ∨ ψ) ↔ (θ ∨ χ))",
        h1,
        ref="orbi2d",
        note="orbi2d(orbi1d.1)",
    )

    s2 = lb.ref(
        "s2",
        "((ψ ∨ θ) ↔ (θ ∨ ψ))",
        ref="orcom",
        note="orcom",
    )

    s3 = lb.ref(
        "s3",
        "((χ ∨ θ) ↔ (θ ∨ χ))",
        ref="orcom",
        note="orcom",
    )

    res = lb.ref(
        "res",
        "φ → ((ψ ∨ θ) ↔ (χ ∨ θ))",
        s1,
        s2,
        s3,
        ref="3bitr4g",
        note="3bitr4g",
    )

    return lb.build(res)


def prove_orbi12d(sys: System) -> Proof:
    """orbi12d: φ → ((ψ ∨ θ) ↔ (χ ∨ τ)).

    Deduction joining two biconditionals with a disjunction.
    set.mm proof: orbi1d orbi2d bitrd.
    """
    lb = ProofBuilder(sys, "orbi12d")
    h1 = lb.hyp("orbi12d.1", "φ → (ψ ↔ χ)")
    h2 = lb.hyp("orbi12d.2", "φ → (θ ↔ τ)")

    # orbi2d: φ → ((ψ ∨ θ) ↔ (ψ ∨ τ))
    s1 = lb.ref(
        "s1",
        "φ → ((ψ ∨ θ) ↔ (ψ ∨ τ))",
        h2,
        ref="orbi2d",
        note="orbi2d",
    )

    # orbi1d: φ → ((ψ ∨ τ) ↔ (χ ∨ τ))
    s2 = lb.ref(
        "s2",
        "φ → ((ψ ∨ τ) ↔ (χ ∨ τ))",
        h1,
        ref="orbi1d",
        note="orbi1d",
    )

    # bitrd: combine
    res = lb.ref(
        "res",
        "φ → ((ψ ∨ θ) ↔ (χ ∨ τ))",
        s1,
        s2,
        ref="bitrd",
        note="bitrd",
    )

    return lb.build(res)


def prove_pm4_78(sys: System) -> Proof:
    """pm4.78: ( ( φ → ψ ) ∨ ( φ → χ ) ) ↔ ( φ → ( ψ ∨ χ ) ).

    Distributivity of implication over disjunction: an implication with
    a disjunctive consequent is equivalent to the disjunction of two
    implications.
    """
    lb = ProofBuilder(sys, "pm4.78")

    # imor: ( φ → ψ ) ↔ ( ¬ φ ∨ ψ )
    s1 = lb.ref("s1", "( ( φ → ψ ) ↔ ( ¬ φ ∨ ψ ) )", ref="imor", note="imor")
    # imor: ( φ → χ ) ↔ ( ¬ φ ∨ χ )
    s2 = lb.ref("s2", "( ( φ → χ ) ↔ ( ¬ φ ∨ χ ) )", ref="imor", note="imor")
    # orbi12i: combine the two imor biconditionals
    s3 = lb.ref(
        "s3",
        "( ( φ → ψ ) ∨ ( φ → χ ) ) ↔ ( ( ¬ φ ∨ ψ ) ∨ ( ¬ φ ∨ χ ) )",
        s1,
        s2,
        ref="orbi12i",
        note="orbi12i",
    )
    # orordi: ( ¬ φ ∨ ( ψ ∨ χ ) ) ↔ ( ( ¬ φ ∨ ψ ) ∨ ( ¬ φ ∨ χ ) )
    s4 = lb.ref(
        "s4",
        "( ¬ φ ∨ ( ψ ∨ χ ) ) ↔ ( ( ¬ φ ∨ ψ ) ∨ ( ¬ φ ∨ χ ) )",
        ref="orordi",
        note="orordi",
    )
    # imor: ( φ → ( ψ ∨ χ ) ) ↔ ( ¬ φ ∨ ( ψ ∨ χ ) )
    s5 = lb.ref(
        "s5",
        "( φ → ( ψ ∨ χ ) ) ↔ ( ¬ φ ∨ ( ψ ∨ χ ) )",
        ref="imor",
        note="imor",
    )
    # 3bitr4ri: chain s4 (ph↔ps), s5 (ch↔ph), s3 (th↔ps) → th↔ch
    res = lb.ref(
        "res",
        "( ( φ → ψ ) ∨ ( φ → χ ) ) ↔ ( φ → ( ψ ∨ χ ) )",
        s4,
        s5,
        s3,
        ref="3bitr4ri",
        note="3bitr4ri",
    )
    return lb.build(res)


def prove_animorr(sys: System) -> Proof:
    """animorr: ( φ ∧ ψ ) → ( χ ∨ ψ ).

    Conjoin the right disjunct to the right conjunct.
    """
    lb = ProofBuilder(sys, "animorr")
    s1 = lb.ref("s1", "( φ ∧ ψ ) → ψ", ref="simpr", note="simpr")
    res = lb.ref("res", "( φ ∧ ψ ) → ( χ ∨ ψ )", s1, ref="olcd", note="olcd(simpr)")
    return lb.build(res)


def prove_animorrl(sys: System) -> Proof:
    """animorrl: ( φ ∧ ψ ) → ( ψ ∨ χ ).

    Conjoin the left disjunct to the right conjunct.
    """
    lb = ProofBuilder(sys, "animorrl")
    s1 = lb.ref("s1", "( φ ∧ ψ ) → ψ", ref="simpr", note="simpr")
    res = lb.ref("res", "( φ ∧ ψ ) → ( ψ ∨ χ )", s1, ref="orcd", note="orcd(simpr)")
    return lb.build(res)


def prove_animorl(sys: System) -> Proof:
    """animorl: ( φ ∧ ψ ) → ( φ ∨ χ ).

    Conjoin the left disjunct to the left conjunct.
    """
    lb = ProofBuilder(sys, "animorl")
    s1 = lb.ref("s1", "( φ ∧ ψ ) → φ", ref="simpl", note="simpl")
    res = lb.ref("res", "( φ ∧ ψ ) → ( φ ∨ χ )", s1, ref="orcd", note="orcd(simpl)")
    return lb.build(res)


def prove_animorlr(sys: System) -> Proof:
    """animorlr: ( φ ∧ ψ ) → ( χ ∨ φ ).

    Conjoin the right disjunct to the left conjunct.
    """
    lb = ProofBuilder(sys, "animorlr")
    s1 = lb.ref("s1", "( φ ∧ ψ ) → φ", ref="simpl", note="simpl")
    res = lb.ref("res", "( φ ∧ ψ ) → ( χ ∨ φ )", s1, ref="olcd", note="olcd(simpl)")
    return lb.build(res)


def prove_pm3_44(sys: System) -> Proof:
    """pm3.44: ((ψ → φ) ∧ (χ → φ)) → ((ψ ∨ χ) → φ).

    Both antecedents imply φ, so their disjunction implies φ.
    set.mm proof: id + id + jaao.
    """
    lb = ProofBuilder(sys, "pm3.44")
    s1 = lb.ref("s1", "( ψ → φ ) → ( ψ → φ )", ref="id", note="id")
    s2 = lb.ref("s2", "( χ → φ ) → ( χ → φ )", ref="id", note="id")
    res = lb.ref(
        "res",
        "( ( ψ → φ ) ∧ ( χ → φ ) ) → ( ( ψ ∨ χ ) → φ )",
        s1,
        s2,
        ref="jaao",
        note="jaao",
    )
    return lb.build(res)


def prove_jaob(sys: System) -> Proof:
    """jaob: ((φ ∨ χ) → ψ) ↔ ((φ → ψ) ∧ (χ → ψ)).

    Equivalence of an implication from a disjunction with the
    conjunction of two implications.
    set.mm proof: pm2.67-2 + olc + imim1i + jca + pm3.44 + impbii.
    """
    lb = ProofBuilder(sys, "jaob")
    # Forward direction: ((φ ∨ χ) → ψ) → ((φ → ψ) ∧ (χ → ψ))
    # pm2.67-2: ((φ ∨ χ) → ψ) → (φ → ψ)
    s1 = lb.ref(
        "s1",
        "( ( φ ∨ χ ) → ψ ) → ( φ → ψ )",
        ref="pm2.67-2",
        note="pm2.67-2",
    )
    # olc: χ → (φ ∨ χ)
    s2 = lb.ref("s2", "χ → ( φ ∨ χ )", ref="olc", note="olc")
    # imim1i(s2): ((φ ∨ χ) → ψ) → (χ → ψ)
    s3 = lb.ref(
        "s3",
        "( ( φ ∨ χ ) → ψ ) → ( χ → ψ )",
        s2,
        ref="imim1i",
        note="imim1i(olc)",
    )
    # jca(s1, s3): ((φ ∨ χ) → ψ) → ((φ → ψ) ∧ (χ → ψ))
    s4 = lb.ref(
        "s4",
        "( ( φ ∨ χ ) → ψ ) → ( ( φ → ψ ) ∧ ( χ → ψ ) )",
        s1,
        s3,
        ref="jca",
        note="jca(pm2.67-2, imim1i)",
    )
    # Reverse direction: pm3.44 with ψ:=φ, φ:=ψ, χ:=χ
    # ((φ → ψ) ∧ (χ → ψ)) → ((φ ∨ χ) → ψ)
    s5 = lb.ref(
        "s5",
        "( ( φ → ψ ) ∧ ( χ → ψ ) ) → ( ( φ ∨ χ ) → ψ )",
        ref="pm3.44",
        note="pm3.44",
    )
    # impbii(s4, s5): ((φ ∨ χ) → ψ) ↔ ((φ → ψ) ∧ (χ → ψ))
    res = lb.ref(
        "res",
        "( ( ( φ ∨ χ ) → ψ ) ↔ ( ( φ → ψ ) ∧ ( χ → ψ ) ) )",
        s4,
        s5,
        ref="impbii",
        note="impbii",
    )
    return lb.build(res)


def prove_pm3_48(sys: System) -> Proof:
    """pm3.48: ((φ → ψ) ∧ (χ → θ)) → ((φ ∨ χ) → (ψ ∨ θ)).

    Both antecedents imply their respective consequents, so the disjunction
    of the antecedents implies the disjunction of the consequents.
    set.mm proof: orc + imim2i + olc + jaao.
    """
    lb = ProofBuilder(sys, "pm3.48")
    s1 = lb.ref("s1", "ψ → ( ψ ∨ θ )", ref="orc", note="orc")
    s2 = lb.ref(
        "s2",
        "( φ → ψ ) → ( φ → ( ψ ∨ θ ) )",
        s1,
        ref="imim2i",
        note="imim2i(orc)",
    )
    s3 = lb.ref("s3", "θ → ( ψ ∨ θ )", ref="olc", note="olc")
    s4 = lb.ref(
        "s4",
        "( χ → θ ) → ( χ → ( ψ ∨ θ ) )",
        s3,
        ref="imim2i",
        note="imim2i(olc)",
    )
    res = lb.ref(
        "res",
        "( ( φ → ψ ) ∧ ( χ → θ ) ) → ( ( φ ∨ χ ) → ( ψ ∨ θ ) )",
        s2,
        s4,
        ref="jaao",
        note="jaao",
    )
    return lb.build(res)


def prove_orim12d(sys: System) -> Proof:
    """orim12d: φ → ( ( ψ ∨ θ ) → ( χ ∨ τ ) ).  Hyp: φ → ( ψ → χ ), φ → ( θ → τ ).

    Deduction joining two implications into a disjunction of antecedents →
    disjunction of consequents.  set.mm proof: pm3.48 syl2anc.
    """
    lb = ProofBuilder(sys, "orim12d")
    h1 = lb.hyp("orim12d.1", "φ → ( ψ → χ )")
    h2 = lb.hyp("orim12d.2", "φ → ( θ → τ )")
    s1 = lb.ref(
        "s1",
        "( ( ψ → χ ) ∧ ( θ → τ ) ) → ( ( ψ ∨ θ ) → ( χ ∨ τ ) )",
        ref="pm3.48",
        note="pm3.48",
    )
    res = lb.ref(
        "res",
        "φ → ( ( ψ ∨ θ ) → ( χ ∨ τ ) )",
        h1,
        h2,
        s1,
        ref="syl2anc",
        note="syl2anc",
    )
    return lb.build(res)


def prove_orim12da(sys: System) -> Proof:
    """orim12da: φ → ( θ ∨ τ ).

    Deduction form of orim12d with exportation.  set.mm proof:
    wo ex orim12d mpd.
    """
    lb = ProofBuilder(sys, "orim12da")
    h1 = lb.hyp("orim12da.1", "( φ ∧ ψ ) → θ")
    h2 = lb.hyp("orim12da.2", "( φ ∧ χ ) → τ")
    h3 = lb.hyp("orim12da.3", "φ → ( ψ ∨ χ )")
    s1 = lb.ref("s1", "φ → ( ψ → θ )", h1, ref="ex", note="ex")
    s2 = lb.ref("s2", "φ → ( χ → τ )", h2, ref="ex", note="ex")
    s3 = lb.ref(
        "s3",
        "φ → ( ( ψ ∨ χ ) → ( θ ∨ τ ) )",
        s1,
        s2,
        ref="orim12d",
        note="orim12d",
    )
    res = lb.ref("res", "φ → ( θ ∨ τ )", h3, s3, ref="mpd", note="mpd")
    return lb.build(res)


def prove_orim2d(sys: System) -> Proof:
    """orim2d: φ → ((θ ∨ ψ) → (θ ∨ χ)).  Hyp: φ → (ψ → χ).

    Deduction adding a disjunct to the left of both antecedent and consequent.
    set.mm proof: idd orim12d.
    """
    lb = ProofBuilder(sys, "orim2d")
    h1 = lb.hyp("orim2d.1", "φ → (ψ → χ)")
    s1 = lb.ref("s1", "φ → (θ → θ)", ref="idd", note="idd")
    res = lb.ref(
        "res",
        "φ → ((θ ∨ ψ) → (θ ∨ χ))",
        s1,
        h1,
        ref="orim12d",
        note="orim12d",
    )
    return lb.build(res)


def prove_orim1d(sys: System) -> Proof:
    """orim1d: φ → ((ψ ∨ θ) → (χ ∨ θ)).  Hyp: φ → (ψ → χ).

    Deduction adding a disjunct to the right of both antecedent and consequent.
    set.mm proof: idd orim12d.
    """
    lb = ProofBuilder(sys, "orim1d")
    h1 = lb.hyp("orim1d.1", "φ → (ψ → χ)")
    s1 = lb.ref("s1", "φ → (θ → θ)", ref="idd", note="idd")
    res = lb.ref(
        "res",
        "φ → ((ψ ∨ θ) → (χ ∨ θ))",
        h1,
        s1,
        ref="orim12d",
        note="orim12d",
    )
    return lb.build(res)


def prove_orim2(sys: System) -> Proof:
    """orim2: (ψ → χ) → ((φ ∨ ψ) → (φ ∨ χ)).

    Adding a disjunct to the left of both antecedent and consequent.
    set.mm proof: id orim2d.
    """
    lb = ProofBuilder(sys, "orim2")
    s1 = lb.ref("s1", "(ψ → χ) → (ψ → χ)", ref="id", note="id")
    res = lb.ref(
        "res",
        "(ψ → χ) → ((φ ∨ ψ) → (φ ∨ χ))",
        s1,
        ref="orim2d",
        note="orim2d",
    )
    return lb.build(res)


def prove_3orim123d(sys: System) -> Proof:
    """3orim123d: φ → ((ψ ∨ θ ∨ η) → (χ ∨ τ ∨ ζ)).

    Deduction joining three implications with a disjunction.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: orim12d df-3or 3imtr4g.
    """
    lb = ProofBuilder(sys, "3orim123d")
    h1 = lb.hyp("3orim123d.1", "φ → (ψ → χ)")
    h2 = lb.hyp("3orim123d.2", "φ → (θ → τ)")
    h3 = lb.hyp("3orim123d.3", "φ → (η → ζ)")

    # orim12d: combine h1 and h2
    s1 = lb.ref(
        "s1",
        "φ → ((ψ ∨ θ) → (χ ∨ τ))",
        h1,
        h2,
        ref="orim12d",
        note="orim12d",
    )

    # orim12d: combine s1 and h3
    s2 = lb.ref(
        "s2",
        "φ → (((ψ ∨ θ) ∨ η) → ((χ ∨ τ) ∨ ζ))",
        s1,
        h3,
        ref="orim12d",
        note="orim12d",
    )

    # df-3or: expand left triple disjunction
    s3 = lb.ref(
        "s3",
        "((ψ ∨ θ ∨ η) ↔ ((ψ ∨ θ) ∨ η))",
        ref="df-3or",
        note="df-3or",
    )

    # df-3or: expand right triple disjunction
    s4 = lb.ref(
        "s4",
        "((χ ∨ τ ∨ ζ) ↔ ((χ ∨ τ) ∨ ζ))",
        ref="df-3or",
        note="df-3or",
    )

    # 3imtr4g: combine s2, s3, s4
    res = lb.ref(
        "res",
        "φ → ((ψ ∨ θ ∨ η) → (χ ∨ τ ∨ ζ))",
        s2,
        s3,
        s4,
        ref="3imtr4g",
        note="3imtr4g",
    )

    return lb.build(res)


def prove_pm4_77(sys: System) -> Proof:
    """pm4.77: ((ψ → φ) ∧ (χ → φ)) ↔ ((ψ ∨ χ) → φ).

    Both ψ and χ separately imply φ if and only if their disjunction
    implies φ.
    set.mm proof: jaob bicomi.
    """
    lb = ProofBuilder(sys, "pm4.77")
    s1 = lb.ref("s1", "( ( ψ ∨ χ ) → φ ) ↔ ( ( ψ → φ ) ∧ ( χ → φ ) )", ref="jaob", note="jaob")
    res = lb.ref(
        "res", "( ( ψ → φ ) ∧ ( χ → φ ) ) ↔ ( ( ψ ∨ χ ) → φ )", s1, ref="bicomi", note="bicomi"
    )
    return lb.build(res)


def prove_3jao(sys: System) -> Proof:
    """3jao: ((φ → ψ) ∧ (χ → ψ) ∧ (θ → ψ)) → ((φ ∨ χ ∨ θ) → ψ).

    Inference joining three implications to an implication from a
    ternary disjunction.
    """
    lb = ProofBuilder(sys, "3jao")

    # jao: (φ → ψ) → ((χ → ψ) → ((φ ∨ χ) → ψ))
    s1 = lb.ref(
        "s1",
        "( φ → ψ ) → ( ( χ → ψ ) → ( ( φ ∨ χ ) → ψ ) )",
        ref="jao",
        note="jao",
    )

    # jao: ((φ ∨ χ) → ψ) → ((θ → ψ) → (((φ ∨ χ) ∨ θ) → ψ))
    s2 = lb.ref(
        "s2",
        "( ( φ ∨ χ ) → ψ ) → ( ( θ → ψ ) → ( ( ( φ ∨ χ ) ∨ θ ) → ψ ) )",
        ref="jao",
        note="jao",
    )

    # syl6(s1, s2): (φ → ψ) → ((χ → ψ) → ((θ → ψ) → (((φ ∨ χ) ∨ θ) → ψ)))
    s3 = lb.ref(
        "s3",
        "( φ → ψ ) → ( ( χ → ψ ) → ( ( θ → ψ ) → ( ( ( φ ∨ χ ) ∨ θ ) → ψ ) ) )",
        s1,
        s2,
        ref="syl6",
        note="syl6",
    )

    # df-3or: (φ ∨ χ ∨ θ) ↔ ((φ ∨ χ) ∨ θ)
    s4 = lb.ref(
        "s4",
        "( ( φ ∨ χ ∨ θ ) ↔ ( ( φ ∨ χ ) ∨ θ ) )",
        ref="df-3or",
        note="df-3or",
    )

    # biimpi: forward direction of the biconditional
    s5 = lb.ref(
        "s5",
        "( ( φ ∨ χ ∨ θ ) → ( ( φ ∨ χ ) ∨ θ ) )",
        s4,
        ref="biimpi",
        note="biimpi(df-3or)",
    )

    # imim1i(s5): (((φ ∨ χ) ∨ θ) → ψ) → ((φ ∨ χ ∨ θ) → ψ)
    s6 = lb.ref(
        "s6",
        "( ( ( φ ∨ χ ) ∨ θ ) → ψ ) → ( ( φ ∨ χ ∨ θ ) → ψ )",
        s5,
        ref="imim1i",
        note="imim1i",
    )

    # imim2i(s6): lift s6 into the (θ → ψ) → ... context
    s7 = lb.ref(
        "s7",
        "( ( θ → ψ ) → ( ( ( φ ∨ χ ) ∨ θ ) → ψ ) ) → ( ( θ → ψ ) → ( ( φ ∨ χ ∨ θ ) → ψ ) )",
        s6,
        ref="imim2i",
        note="imim2i",
    )

    # syl6(s3, s7): (φ → ψ) → ((χ → ψ) → ((θ → ψ) → ((φ ∨ χ ∨ θ) → ψ)))
    s8 = lb.ref(
        "s8",
        "( φ → ψ ) → ( ( χ → ψ ) → ( ( θ → ψ ) → ( ( φ ∨ χ ∨ θ ) → ψ ) ) )",
        s3,
        s7,
        ref="syl6",
        note="syl6",
    )

    # 3imp: convert nested → to ternary ∧
    res = lb.ref(
        "res",
        "( ( φ → ψ ) ∧ ( χ → ψ ) ∧ ( θ → ψ ) ) → ( ( φ ∨ χ ∨ θ ) → ψ )",
        s8,
        ref="3imp",
        note="3imp",
    )

    return lb.build(res)


def prove_3jaob(sys: System) -> Proof:
    """3jaob: ( ( φ ∨ χ ∨ θ ) → ψ ) ↔ ( ( φ → ψ ) ∧ ( χ → ψ ) ∧ ( θ → ψ ) ).

    An implication from a ternary disjunction is equivalent to the
    conjunction of three individual implications.
    """
    lb = ProofBuilder(sys, "3jaob")

    # pm5.53: ( ( ( φ ∨ χ ) ∨ θ ) → ψ ) ↔ ( ( ( φ → ψ ) ∧ ( χ → ψ ) ) ∧ ( θ → ψ ) )
    s1 = lb.ref(
        "s1",
        "( ( ( φ ∨ χ ) ∨ θ ) → ψ ) ↔ ( ( ( φ → ψ ) ∧ ( χ → ψ ) ) ∧ ( θ → ψ ) )",
        ref="pm5.53",
        note="pm5.53",
    )

    # df-3or: ( φ ∨ χ ∨ θ ) ↔ ( ( φ ∨ χ ) ∨ θ )
    s2 = lb.ref(
        "s2",
        "( φ ∨ χ ∨ θ ) ↔ ( ( φ ∨ χ ) ∨ θ )",
        ref="df-3or",
        note="df-3or",
    )

    # imbi1i: ( ( φ ∨ χ ∨ θ ) → ψ ) ↔ ( ( ( φ ∨ χ ) ∨ θ ) → ψ )
    s3 = lb.ref(
        "s3",
        "( ( φ ∨ χ ∨ θ ) → ψ ) ↔ ( ( ( φ ∨ χ ) ∨ θ ) → ψ )",
        s2,
        ref="imbi1i",
        note="imbi1i(df-3or)",
    )

    # df-3an: ( ( φ → ψ ) ∧ ( χ → ψ ) ∧ ( θ → ψ ) ) ↔ ( ( ( φ → ψ ) ∧ ( χ → ψ ) ) ∧ ( θ → ψ ) )
    s4 = lb.ref(
        "s4",
        "( ( φ → ψ ) ∧ ( χ → ψ ) ∧ ( θ → ψ ) ) ↔ ( ( ( φ → ψ ) ∧ ( χ → ψ ) ) ∧ ( θ → ψ ) )",
        ref="df-3an",
        note="df-3an",
    )

    # 3bitr4i: combine s1, s3, s4
    res = lb.ref(
        "res",
        "( ( φ ∨ χ ∨ θ ) → ψ ) ↔ ( ( φ → ψ ) ∧ ( χ → ψ ) ∧ ( θ → ψ ) )",
        s1,
        s3,
        s4,
        ref="3bitr4i",
        note="3bitr4i",
    )

    return lb.build(res)


def prove_3jaoiOLD(sys: System) -> Proof:
    """3jaoiOLD: ( φ ∨ χ ∨ θ ) → ψ.

    Inference form of 3jao from φ → ψ, χ → ψ, θ → ψ.
    set.mm proof: wi w3a w3o 3pm3.2i 3jao ax-mp.
    """
    lb = ProofBuilder(sys, "3jaoiOLD")
    h1 = lb.hyp("3jaoi.1", "φ → ψ")
    h2 = lb.hyp("3jaoi.2", "χ → ψ")
    h3 = lb.hyp("3jaoi.3", "θ → ψ")
    s1 = lb.ref(
        "s1",
        "( ( φ → ψ ) ∧ ( χ → ψ ) ∧ ( θ → ψ ) )",
        h1,
        h2,
        h3,
        ref="3pm3.2i",
        note="3pm3.2i",
    )
    s2 = lb.ref(
        "s2",
        "( ( φ → ψ ) ∧ ( χ → ψ ) ∧ ( θ → ψ ) ) → ( ( φ ∨ χ ∨ θ ) → ψ )",
        ref="3jao",
        note="3jao",
    )
    res = lb.mp("res", s1, s2, note="MP 3pm3.2i, 3jao")
    return lb.build(res)


def prove_3jaoi(sys: System) -> Proof:
    """3jaoi: ( φ ∨ χ ∨ θ ) → ψ.

    Hyp 1: φ → ψ
    Hyp 2: χ → ψ
    Hyp 3: θ → ψ
    Concl: ( φ ∨ χ ∨ θ ) → ψ

    Inference joining three implications.
    set.mm proof: w3o wi 3jaob mpbir3an.
    """
    lb = ProofBuilder(sys, "3jaoi")
    h1 = lb.hyp("3jaoi.1", "φ → ψ")
    h2 = lb.hyp("3jaoi.2", "χ → ψ")
    h3 = lb.hyp("3jaoi.3", "θ → ψ")

    # 3jaob: ( ( φ ∨ χ ∨ θ ) → ψ ) ↔ ( ( φ → ψ ) ∧ ( χ → ψ ) ∧ ( θ → ψ ) )
    s1 = lb.ref(
        "s1",
        "( ( φ ∨ χ ∨ θ ) → ψ ) ↔ ( ( φ → ψ ) ∧ ( χ → ψ ) ∧ ( θ → ψ ) )",
        ref="3jaob",
        note="3jaob",
    )

    # mpbir3an: combine the three hypotheses with the biconditional
    res = lb.ref(
        "res",
        "( φ ∨ χ ∨ θ ) → ψ",
        h1,
        h2,
        h3,
        s1,
        ref="mpbir3an",
        note="mpbir3an",
    )
    return lb.build(res)


def prove_3jaoian(sys: System) -> Proof:
    """3jaoian: ( ( ( φ ∨ θ ∨ τ ) ∧ ψ ) → χ .

    Hyp 1: ( φ ∧ ψ ) → χ
    Hyp 2: ( θ ∧ ψ ) → χ
    Hyp 3: ( τ ∧ ψ ) → χ
    Concl: ( ( ( φ ∨ θ ∨ τ ) ∧ ψ ) → χ

    Inference joining a conjunction with three disjuncts.
    set.mm proof: ex, 3jaoi, imp.
    """
    lb = ProofBuilder(sys, "3jaoian")
    h1 = lb.hyp("3jaoian.1", "( φ ∧ ψ ) → χ")
    h2 = lb.hyp("3jaoian.2", "( θ ∧ ψ ) → χ")
    h3 = lb.hyp("3jaoian.3", "( τ ∧ ψ ) → χ")

    # ex: export each hypothesis
    s1 = lb.ref("s1", "φ → ( ψ → χ )", h1, ref="ex", note="ex 3jaoian.1")
    s2 = lb.ref("s2", "θ → ( ψ → χ )", h2, ref="ex", note="ex 3jaoian.2")
    s3 = lb.ref("s3", "τ → ( ψ → χ )", h3, ref="ex", note="ex 3jaoian.3")

    # 3jaoi: combine into three-disjunction implication
    s4 = lb.ref(
        "s4",
        "( φ ∨ θ ∨ τ ) → ( ψ → χ )",
        s1,
        s2,
        s3,
        ref="3jaoi",
        note="3jaoi",
    )

    # imp: derive the conjunction form
    res = lb.ref(
        "res",
        "( ( φ ∨ θ ∨ τ ) ∧ ψ ) → χ",
        s4,
        ref="imp",
        note="imp",
    )
    return lb.build(res)


def prove_3jaod(sys: System) -> Proof:
    """3jaod: φ → ((ψ ∨ θ ∨ τ) → χ).

    Deduction form of 3jao.
    """
    lb = ProofBuilder(sys, "3jaod")
    h1 = lb.hyp("3jaod.1", "φ → (ψ → χ)")
    h2 = lb.hyp("3jaod.2", "φ → (θ → χ)")
    h3 = lb.hyp("3jaod.3", "φ → (τ → χ)")

    # 3jao: ((ψ → χ) ∧ (θ → χ) ∧ (τ → χ)) → ((ψ ∨ θ ∨ τ) → χ)
    s1 = lb.ref(
        "s1",
        "( ( ψ → χ ) ∧ ( θ → χ ) ∧ ( τ → χ ) ) → ( ( ψ ∨ θ ∨ τ ) → χ )",
        ref="3jao",
        note="3jao",
    )

    # syl3anc: combine three hypotheses with 3jao
    res = lb.ref(
        "res",
        "φ → ( ( ψ ∨ θ ∨ τ ) → χ )",
        h1,
        h2,
        h3,
        s1,
        ref="syl3anc",
        note="syl3anc 3jaod.1, 3jaod.2, 3jaod.3, 3jao",
    )

    return lb.build(res)


def prove_3jaodan(sys: System) -> Proof:
    """3jaodan: (φ ∧ (ψ ∨ θ ∨ τ)) → χ.

    Inference joining the consequents of three conjunctive antecedents.
    """
    lb = ProofBuilder(sys, "3jaodan")
    h1 = lb.hyp("3jaodan.1", "( φ ∧ ψ ) → χ")
    h2 = lb.hyp("3jaodan.2", "( φ ∧ θ ) → χ")
    h3 = lb.hyp("3jaodan.3", "( φ ∧ τ ) → χ")

    s1 = lb.ref("s1", "φ → ( ψ → χ )", h1, ref="ex", note="ex(3jaodan.1)")
    s2 = lb.ref("s2", "φ → ( θ → χ )", h2, ref="ex", note="ex(3jaodan.2)")
    s3 = lb.ref("s3", "φ → ( τ → χ )", h3, ref="ex", note="ex(3jaodan.3)")

    s4 = lb.ref(
        "s4",
        "φ → ( ( ψ ∨ θ ∨ τ ) → χ )",
        s1,
        s2,
        s3,
        ref="3jaod",
        note="3jaod",
    )

    res = lb.ref("res", "( φ ∧ ( ψ ∨ θ ∨ τ ) ) → χ", s4, ref="imp", note="imp")

    return lb.build(res)


def prove_orddi(sys: System) -> Proof:
    """orddi: ((φ ∧ ψ) ∨ (χ ∧ θ)) ↔ (((φ ∨ χ) ∧ (φ ∨ θ)) ∧ ((ψ ∨ χ) ∧ (ψ ∨ θ))).

    Distributive law for conjunction over disjunction, dual of ordi/ordir.
    """
    lb = ProofBuilder(sys, "orddi")

    # ordir with χ := (χ ∧ θ)
    s1 = lb.ref(
        "s1",
        "((φ ∧ ψ) ∨ (χ ∧ θ)) ↔ ((φ ∨ (χ ∧ θ)) ∧ (ψ ∨ (χ ∧ θ)))",
        ref="ordir",
        note="ordir",
    )

    # ordi: (φ ∨ (χ ∧ θ)) ↔ ((φ ∨ χ) ∧ (φ ∨ θ))
    s2 = lb.ref(
        "s2",
        "(φ ∨ (χ ∧ θ)) ↔ ((φ ∨ χ) ∧ (φ ∨ θ))",
        ref="ordi",
        note="ordi",
    )

    # ordi with φ := ψ, ψ := χ, χ := θ
    s3 = lb.ref(
        "s3",
        "(ψ ∨ (χ ∧ θ)) ↔ ((ψ ∨ χ) ∧ (ψ ∨ θ))",
        ref="ordi",
        note="ordi",
    )

    # anbi12i: combine s2 and s3
    s4 = lb.ref(
        "s4",
        "((φ ∨ (χ ∧ θ)) ∧ (ψ ∨ (χ ∧ θ))) ↔ (((φ ∨ χ) ∧ (φ ∨ θ)) ∧ ((ψ ∨ χ) ∧ (ψ ∨ θ)))",
        s2,
        s3,
        ref="anbi12i",
        note="anbi12i",
    )

    # bitri: chain s1 and s4
    res = lb.ref(
        "res",
        "((φ ∧ ψ) ∨ (χ ∧ θ)) ↔ (((φ ∨ χ) ∧ (φ ∨ θ)) ∧ ((ψ ∨ χ) ∧ (ψ ∨ θ)))",
        s1,
        s4,
        ref="bitri",
        note="bitri",
    )

    return lb.build(res)


def prove_pm4_79(sys: System) -> Proof:
    """pm4.79: ( ( ψ → φ ) ∨ ( χ → φ ) ) ↔ ( ( ψ ∧ χ ) → φ ).

    Equivalence between a disjunction of implications and an implication
    with a conjunctive antecedent.
    """
    lb = ProofBuilder(sys, "pm4.79")

    # Direction 1: ( ( ψ → φ ) ∨ ( χ → φ ) ) → ( ( ψ ∧ χ ) → φ )
    s1 = lb.ref("s1", "( ψ → φ ) → ( ψ → φ )", ref="id", note="id")
    s2 = lb.ref("s2", "( χ → φ ) → ( χ → φ )", ref="id", note="id")
    s3 = lb.ref(
        "s3",
        "( ( ψ → φ ) ∨ ( χ → φ ) ) → ( ( ψ ∧ χ ) → φ )",
        s1,
        s2,
        ref="jaoa",
        note="jaoa",
    )

    # Direction 2: ( ( ψ ∧ χ ) → φ ) → ( ( ψ → φ ) ∨ ( χ → φ ) )
    s4 = lb.ref("s4", "¬ ( ψ → φ ) → ψ", ref="simplim", note="simplim")
    s5 = lb.ref(
        "s5",
        "( ( ψ ∧ χ ) → φ ) → ( ψ → ( χ → φ ) )",
        ref="pm3.3",
        note="pm3.3",
    )
    s6 = lb.ref(
        "s6",
        "( ( ψ ∧ χ ) → φ ) → ( ¬ ( ψ → φ ) → ( χ → φ ) )",
        s4,
        s5,
        ref="syl5",
        note="syl5",
    )
    s7 = lb.ref(
        "s7",
        "( ( ψ ∧ χ ) → φ ) → ( ( ψ → φ ) ∨ ( χ → φ ) )",
        s6,
        ref="orrd",
        note="orrd",
    )

    # impbii: combine the two directions
    res = lb.ref(
        "res",
        "( ( ψ → φ ) ∨ ( χ → φ ) ) ↔ ( ( ψ ∧ χ ) → φ )",
        s3,
        s7,
        ref="impbii",
        note="impbii",
    )
    return lb.build(res)


def prove_oranabs(sys: System) -> Proof:
    """oranabs: ( ( φ ∨ ¬ ψ ) ∧ ψ ) ↔ ( φ ∧ ψ ).

    Absorb the right conjunct into a disjunctive left conjunct.
    set.mm proof: biortn orcom bitr2di pm5.32ri.
    """
    lb = ProofBuilder(sys, "oranabs")
    s1 = lb.ref("s1", "( ψ → ( φ ↔ ( ¬ ψ ∨ φ ) ) )", ref="biortn", note="biortn")
    s2 = lb.ref("s2", "( ( ¬ ψ ∨ φ ) ↔ ( φ ∨ ¬ ψ ) )", ref="orcom", note="orcom")
    s3 = lb.ref("s3", "( ψ → ( ( φ ∨ ¬ ψ ) ↔ φ ) )", s1, s2, ref="bitr2di", note="bitr2di")
    res = lb.ref("res", "( ( φ ∨ ¬ ψ ) ∧ ψ ) ↔ ( φ ∧ ψ )", s3, ref="pm5.32ri", note="pm5.32ri")
    return lb.build(res)


def prove_orabs(sys: System) -> Proof:
    """orabs: φ ↔ ( ( φ ∨ ψ ) ∧ φ ).

    Absorb a disjunct into a conjunction — a proposition is equivalent
    to the conjunction of its disjunction with itself.
    set.mm proof: orc pm4.71ri.
    """
    lb = ProofBuilder(sys, "orabs")
    s_orc = lb.ref("s_orc", "( φ → ( φ ∨ ψ ) )", ref="orc", note="orc")
    res = lb.ref("res", "( φ ↔ ( ( φ ∨ ψ ) ∧ φ ) )", s_orc, ref="pm4.71ri", note="pm4.71ri")
    return lb.build(res)


def prove_pm4_45(sys: System) -> Proof:
    """pm4.45: φ ↔ ( φ ∧ ( φ ∨ ψ ) ).

    A proposition is equivalent to itself conjoined with a disjunction
    containing itself.  (Contributed by NM, 5-Aug-1993.)
    set.mm proof: orc pm4.71i.
    """
    lb = ProofBuilder(sys, "pm4.45")
    s_orc = lb.ref("s_orc", "( φ → ( φ ∨ ψ ) )", ref="orc", note="orc")
    res = lb.ref("res", "( φ ↔ ( φ ∧ ( φ ∨ ψ ) ) )", s_orc, ref="pm4.71i", note="pm4.71i")
    return lb.build(res)


def prove_pm5_53(sys: System) -> Proof:
    """pm5.53: ( ( ( φ ∨ ψ ) ∨ χ ) → θ ) ↔ ( ( ( φ → θ ) ∧ ( ψ → θ ) ) ∧ ( χ → θ ) ).

    An implication from a nested disjunction is equivalent to the conjunction
    of three individual implications.
    """
    lb = ProofBuilder(sys, "pm5.53")
    s1 = lb.ref(
        "s1",
        "( ( ( φ ∨ ψ ) ∨ χ ) → θ ) ↔ ( ( ( φ ∨ ψ ) → θ ) ∧ ( χ → θ ) )",
        ref="jaob",
        note="jaob",
    )
    s2 = lb.ref(
        "s2",
        "( ( φ ∨ ψ ) → θ ) ↔ ( ( φ → θ ) ∧ ( ψ → θ ) )",
        ref="jaob",
        note="jaob",
    )
    res = lb.ref(
        "res",
        "( ( ( φ ∨ ψ ) ∨ χ ) → θ ) ↔ ( ( ( φ → θ ) ∧ ( ψ → θ ) ) ∧ ( χ → θ ) )",
        s1,
        s2,
        ref="bianbi",
        note="bianbi",
    )
    return lb.build(res)


def prove_pm5_71(sys: System) -> Proof:
    """pm5.71: ( ψ → ¬ χ ) → ( ( ( φ ∨ ψ ) ∧ χ ) ↔ ( φ ∧ χ ) ).

    If ψ implies ¬ χ, then ( φ ∨ ψ ) ∧ χ is equivalent to φ ∧ χ.
    set.mm proof: orel2 orc impbid1 anbi1d pm2.21 pm5.32rd ja.
    """
    lb = ProofBuilder(sys, "pm5.71")

    # orel2 with φ:=ψ, ψ:=φ: ¬ ψ → ( ( φ ∨ ψ ) → φ )
    s1 = lb.ref("s1", "¬ ψ → ( ( φ ∨ ψ ) → φ )", ref="orel2", note="orel2")

    # orc: φ → ( φ ∨ ψ )
    s2 = lb.ref("s2", "φ → ( φ ∨ ψ )", ref="orc", note="orc")

    # impbid1: ¬ ψ → ( ( φ ∨ ψ ) ↔ φ )
    s3 = lb.ref("s3", "¬ ψ → ( ( φ ∨ ψ ) ↔ φ )", s1, s2, ref="impbid1", note="impbid1")

    # anbi1d: ¬ ψ → ( ( ( φ ∨ ψ ) ∧ χ ) ↔ ( φ ∧ χ ) )
    s4 = lb.ref("s4", "¬ ψ → ( ( ( φ ∨ ψ ) ∧ χ ) ↔ ( φ ∧ χ ) )", s3, ref="anbi1d", note="anbi1d")

    # pm2.21 with φ:=χ, ψ:=((φ∨ψ)↔φ): ¬ χ → ( χ → ( ( φ ∨ ψ ) ↔ φ ) )
    s5 = lb.ref("s5", "¬ χ → ( χ → ( ( φ ∨ ψ ) ↔ φ ) )", ref="pm2.21", note="pm2.21")

    # pm5.32rd: ¬ χ → ( ( ( φ ∨ ψ ) ∧ χ ) ↔ ( φ ∧ χ ) )
    s6 = lb.ref(
        "s6", "¬ χ → ( ( ( φ ∨ ψ ) ∧ χ ) ↔ ( φ ∧ χ ) )", s5, ref="pm5.32rd", note="pm5.32rd"
    )

    # ja: ( ψ → ¬ χ ) → ( ( ( φ ∨ ψ ) ∧ χ ) ↔ ( φ ∧ χ ) )
    res = lb.ref(
        "res", "( ψ → ¬ χ ) → ( ( ( φ ∨ ψ ) ∧ χ ) ↔ ( φ ∧ χ ) )", s4, s6, ref="ja", note="ja"
    )

    return lb.build(res)


def prove_bigolden(sys: System) -> Proof:
    """bigolden: ( ( φ ∧ ψ ) ↔ φ ) ↔ ( ψ ↔ ( φ ∨ ψ ) ).

    Equivalence between a biconditional form of conjunction and a biconditional
    form of disjunction.  Both are equivalent to the same implication, proved
    by chaining pm4.71, bicom, pm4.72 via 3bitr3ri.
    """
    lb = ProofBuilder(sys, "bigolden")
    s1 = lb.ref("s1", "( φ → ψ ) ↔ ( φ ↔ ( φ ∧ ψ ) )", ref="pm4.71", note="pm4.71")
    s2 = lb.ref("s2", "( φ → ψ ) ↔ ( ψ ↔ ( φ ∨ ψ ) )", ref="pm4.72", note="pm4.72")
    s3 = lb.ref("s3", "( φ ↔ ( φ ∧ ψ ) ) ↔ ( ( φ ∧ ψ ) ↔ φ )", ref="bicom", note="bicom")
    res = lb.ref(
        "res",
        "( ( φ ∧ ψ ) ↔ φ ) ↔ ( ψ ↔ ( φ ∨ ψ ) )",
        s1,
        s2,
        s3,
        ref="3bitr3ri",
        note="3bitr3ri",
    )
    return lb.build(res)


def prove_ianor(sys: System) -> Proof:
    """ianor: ¬ ( φ ∧ ψ ) ↔ ( ¬ φ ∨ ¬ ψ ).

    De Morgan's law for conjunction: the negation of a conjunction
    is equivalent to the disjunction of the negations.
    """
    lb = ProofBuilder(sys, "ianor")

    s1 = lb.ref(
        "s1",
        "( φ → ¬ ψ ) ↔ ¬ ( φ ∧ ψ )",
        ref="imnan",
        note="imnan",
    )

    s2 = lb.ref(
        "s2",
        "( φ → ¬ ψ ) ↔ ( ¬ φ ∨ ¬ ψ )",
        ref="pm4.62",
        note="pm4.62",
    )

    res = lb.ref(
        "res",
        "¬ ( φ ∧ ψ ) ↔ ( ¬ φ ∨ ¬ ψ )",
        s1,
        s2,
        ref="bitr3i",
        note="bitr3i",
    )

    return lb.build(res)


def prove_anor(sys: System) -> Proof:
    """anor: ( φ ∧ ψ ) ↔ ¬ ( ¬ φ ∨ ¬ ψ ).

    De Morgan's law for conjunction: a conjunction is equivalent to
    the negation of the disjunction of the negations.
    """
    lb = ProofBuilder(sys, "anor")

    s1 = lb.ref(
        "s1",
        "( φ ∧ ψ ) ↔ ¬ ¬ ( φ ∧ ψ )",
        ref="notnotb",
        note="notnotb",
    )

    s2 = lb.ref(
        "s2",
        "¬ ( φ ∧ ψ ) ↔ ( ¬ φ ∨ ¬ ψ )",
        ref="ianor",
        note="ianor",
    )

    res = lb.ref(
        "res",
        "( φ ∧ ψ ) ↔ ¬ ( ¬ φ ∨ ¬ ψ )",
        s1,
        s2,
        ref="xchbinx",
        note="xchbinx",
    )

    return lb.build(res)


def prove_nanor(sys: System) -> Proof:
    """nanor: ( φ ⊼ ψ ) ↔ ( ¬ φ ∨ ¬ ψ ).

    NAND is equivalent to the disjunction of negations.
    """
    lb = ProofBuilder(sys, "nanor")

    s1 = lb.ref(
        "s1",
        "( φ ⊼ ψ ) ↔ ¬ ( φ ∧ ψ )",
        ref="df-nan",
        note="df-nan",
    )

    s2 = lb.ref(
        "s2",
        "¬ ( φ ∧ ψ ) ↔ ( ¬ φ ∨ ¬ ψ )",
        ref="ianor",
        note="ianor",
    )

    res = lb.ref(
        "res",
        "( φ ⊼ ψ ) ↔ ( ¬ φ ∨ ¬ ψ )",
        s1,
        s2,
        ref="bitri",
        note="bitri",
    )

    return lb.build(res)


def prove_pm3_11(sys: System) -> Proof:
    """pm3.11: ¬ ( ¬ φ ∨ ¬ ψ ) → ( φ ∧ ψ ).

    Conjunction from negated disjunction of negations.  One direction
    of De Morgan's law for conjunction (reverse of anor).
    """
    lb = ProofBuilder(sys, "pm3.11")

    s1 = lb.ref(
        "s1",
        "( φ ∧ ψ ) ↔ ¬ ( ¬ φ ∨ ¬ ψ )",
        ref="anor",
        note="anor",
    )

    res = lb.ref(
        "res",
        "¬ ( ¬ φ ∨ ¬ ψ ) → ( φ ∧ ψ )",
        s1,
        ref="biimpri",
        note="biimpri",
    )

    return lb.build(res)


def prove_pm3_12(sys: System) -> Proof:
    """pm3.12: ( ¬ φ ∨ ¬ ψ ) ∨ ( φ ∧ ψ ).

    Disjunction of negated disjunction and conjunction.  Follows
    from pm3.11 via orri.
    """
    lb = ProofBuilder(sys, "pm3.12")

    s1 = lb.ref(
        "s1",
        "¬ ( ¬ φ ∨ ¬ ψ ) → ( φ ∧ ψ )",
        ref="pm3.11",
        note="pm3.11",
    )

    res = lb.ref(
        "res",
        "( ¬ φ ∨ ¬ ψ ) ∨ ( φ ∧ ψ )",
        s1,
        ref="orri",
        note="orri",
    )

    return lb.build(res)


def prove_pm3_13(sys: System) -> Proof:
    """pm3.13: ¬ ( φ ∧ ψ ) → ( ¬ φ ∨ ¬ ψ ).

    One direction of De Morgan's law.  set.mm proof: pm3.11 con1i.
    """
    lb = ProofBuilder(sys, "pm3.13")
    s1 = lb.ref("s1", "¬ ( ¬ φ ∨ ¬ ψ ) → ( φ ∧ ψ )", ref="pm3.11", note="pm3.11")
    res = lb.ref("res", "¬ ( φ ∧ ψ ) → ( ¬ φ ∨ ¬ ψ )", s1, ref="con1i", note="con1i")
    return lb.build(res)


def prove_ioran(sys: System) -> Proof:
    """ioran: ¬ ( φ ∨ ψ ) ↔ ( ¬ φ ∧ ¬ ψ ).

    De Morgan's law for disjunction.
    """
    lb = ProofBuilder(sys, "ioran")

    s1 = lb.ref(
        "s1",
        "¬ ( ¬ φ → ψ ) ↔ ( ¬ φ ∧ ¬ ψ )",
        ref="pm4.65",
        note="pm4.65",
    )

    s2 = lb.ref(
        "s2",
        "( ¬ φ → ψ ) ↔ ( φ ∨ ψ )",
        ref="pm4.64",
        note="pm4.64",
    )

    res = lb.ref(
        "res",
        "¬ ( φ ∨ ψ ) ↔ ( ¬ φ ∧ ¬ ψ )",
        s1,
        s2,
        ref="xchnxbi",
        note="xchnxbi",
    )

    return lb.build(res)


def prove_3ioran(sys: System) -> Proof:
    """3ioran: ¬ ( φ ∨ ψ ∨ χ ) ↔ ( ¬ φ ∧ ¬ ψ ∧ ¬ χ ).

    De Morgan's law for ternary disjunction.
    """
    lb = ProofBuilder(sys, "3ioran")

    s1 = lb.ref(
        "s1",
        "¬ ( φ ∨ ψ ) ↔ ( ¬ φ ∧ ¬ ψ )",
        ref="ioran",
        note="ioran",
    )

    s2 = lb.ref(
        "s2",
        "¬ ( ( φ ∨ ψ ) ∨ χ ) ↔ ( ¬ ( φ ∨ ψ ) ∧ ¬ χ )",
        ref="ioran",
        note="ioran",
    )

    s3 = lb.ref(
        "s3",
        "( ¬ ( φ ∨ ψ ) ∧ ¬ χ ) ↔ ( ( ¬ φ ∧ ¬ ψ ) ∧ ¬ χ )",
        s1,
        ref="anbi1i",
        note="anbi1i",
    )

    s4 = lb.ref(
        "s4",
        "( φ ∨ ψ ∨ χ ) ↔ ( ( φ ∨ ψ ) ∨ χ )",
        ref="df-3or",
        note="df-3or",
    )

    s5 = lb.ref(
        "s5",
        "¬ ( φ ∨ ψ ∨ χ ) ↔ ( ¬ ( φ ∨ ψ ) ∧ ¬ χ )",
        s2,
        s4,
        ref="xchnxbir",
        note="xchnxbir",
    )

    s6 = lb.ref(
        "s6",
        "( ¬ φ ∧ ¬ ψ ∧ ¬ χ ) ↔ ( ( ¬ φ ∧ ¬ ψ ) ∧ ¬ χ )",
        ref="df-3an",
        note="df-3an",
    )

    res = lb.ref(
        "res",
        "¬ ( φ ∨ ψ ∨ χ ) ↔ ( ¬ φ ∧ ¬ ψ ∧ ¬ χ )",
        s3,
        s5,
        s6,
        ref="3bitr4i",
        note="3bitr4i",
    )

    return lb.build(res)


def prove_3ianor(sys: System) -> Proof:
    """3ianor: ¬ ( φ ∧ ψ ∧ χ ) ↔ ( ¬ φ ∨ ¬ ψ ∨ ¬ χ ).

    De Morgan's law for ternary conjunction.
    """
    lb = ProofBuilder(sys, "3ianor")

    s1 = lb.ref(
        "s1",
        "¬ ( φ ∧ ψ ) ↔ ( ¬ φ ∨ ¬ ψ )",
        ref="ianor",
        note="ianor",
    )

    s2 = lb.ref(
        "s2",
        "¬ ( ( φ ∧ ψ ) ∧ χ ) ↔ ( ¬ ( φ ∧ ψ ) ∨ ¬ χ )",
        ref="ianor",
        note="ianor",
    )

    s3 = lb.ref(
        "s3",
        "( ¬ ( φ ∧ ψ ) ∨ ¬ χ ) ↔ ( ( ¬ φ ∨ ¬ ψ ) ∨ ¬ χ )",
        s1,
        ref="orbi1i",
        note="orbi1i",
    )

    s4 = lb.ref(
        "s4",
        "( φ ∧ ψ ∧ χ ) ↔ ( ( φ ∧ ψ ) ∧ χ )",
        ref="df-3an",
        note="df-3an",
    )

    s5 = lb.ref(
        "s5",
        "¬ ( φ ∧ ψ ∧ χ ) ↔ ( ¬ ( φ ∧ ψ ) ∨ ¬ χ )",
        s2,
        s4,
        ref="xchnxbir",
        note="xchnxbir",
    )

    s6 = lb.ref(
        "s6",
        "( ¬ φ ∨ ¬ ψ ∨ ¬ χ ) ↔ ( ( ¬ φ ∨ ¬ ψ ) ∨ ¬ χ )",
        ref="df-3or",
        note="df-3or",
    )

    res = lb.ref(
        "res",
        "¬ ( φ ∧ ψ ∧ χ ) ↔ ( ¬ φ ∨ ¬ ψ ∨ ¬ χ )",
        s3,
        s5,
        s6,
        ref="3bitr4i",
        note="3bitr4i",
    )

    return lb.build(res)


def prove_3oran(sys: System) -> Proof:
    """3oran: ( φ ∨ ψ ∨ χ ) ↔ ¬ ( ¬ φ ∧ ¬ ψ ∧ ¬ χ ).

    De Morgan's law for ternary disjunction expressed as a
    biconditional — a disjunction of three propositions is
    equivalent to the negation of the conjunction of their negations.
    """
    lb = ProofBuilder(sys, "3oran")

    s1 = lb.ref(
        "s1",
        "¬ ( φ ∨ ψ ∨ χ ) ↔ ( ¬ φ ∧ ¬ ψ ∧ ¬ χ )",
        ref="3ioran",
        note="3ioran",
    )

    s2 = lb.ref(
        "s2",
        "¬ ( ¬ φ ∧ ¬ ψ ∧ ¬ χ ) ↔ ( φ ∨ ψ ∨ χ )",
        s1,
        ref="con1bii",
        note="con1bii",
    )

    res = lb.ref(
        "res",
        "( φ ∨ ψ ∨ χ ) ↔ ¬ ( ¬ φ ∧ ¬ ψ ∧ ¬ χ )",
        s2,
        ref="bicomi",
        note="bicomi",
    )

    return lb.build(res)


def prove_3anor(sys: System) -> Proof:
    """3anor: ( φ ∧ ψ ∧ χ ) ↔ ¬ ( ¬ φ ∨ ¬ ψ ∨ ¬ χ ).

    A triple conjunction is equivalent to the negation of a triple
    disjunction of negations.
    """
    lb = ProofBuilder(sys, "3anor")

    s1 = lb.ref(
        "s1",
        "¬ ( φ ∧ ψ ∧ χ ) ↔ ( ¬ φ ∨ ¬ ψ ∨ ¬ χ )",
        ref="3ianor",
        note="3ianor",
    )

    s2 = lb.ref(
        "s2",
        "¬ ( ¬ φ ∨ ¬ ψ ∨ ¬ χ ) ↔ ( φ ∧ ψ ∧ χ )",
        s1,
        ref="con1bii",
        note="con1bii",
    )

    res = lb.ref(
        "res",
        "( φ ∧ ψ ∧ χ ) ↔ ¬ ( ¬ φ ∨ ¬ ψ ∨ ¬ χ )",
        s2,
        ref="bicomi",
        note="bicomi",
    )

    return lb.build(res)


def prove_pm4_56(sys: System) -> Proof:
    """pm4.56: ( ( ¬ φ ∧ ¬ ψ ) ↔ ¬ ( φ ∨ ψ ) ).

    De Morgan's law for disjunction, commuted form.
    set.mm proof: ioran bicomi.
    """
    lb = ProofBuilder(sys, "pm4.56")
    s1 = lb.ref(
        "s1",
        "¬ ( φ ∨ ψ ) ↔ ( ¬ φ ∧ ¬ ψ )",
        ref="ioran",
        note="ioran",
    )
    res = lb.ref(
        "res",
        "( ¬ φ ∧ ¬ ψ ) ↔ ¬ ( φ ∨ ψ )",
        s1,
        ref="bicomi",
        note="bicomi",
    )
    return lb.build(res)


def prove_pm4_57(sys: System) -> Proof:
    """pm4.57: ¬ ( ¬ φ ∧ ¬ ψ ) ↔ ( φ ∨ ψ ).

    De Morgan's law: a conjunction of negations is equivalent to the negation
    of a disjunction, commuted form.
    """
    lb = ProofBuilder(sys, "pm4.57")
    s1 = lb.ref(
        "s1",
        "( φ ∨ ψ ) ↔ ¬ ( ¬ φ ∧ ¬ ψ )",
        ref="oran",
        note="oran",
    )
    res = lb.ref(
        "res",
        "¬ ( ¬ φ ∧ ¬ ψ ) ↔ ( φ ∨ ψ )",
        s1,
        ref="bicomi",
        note="bicomi",
    )
    return lb.build(res)


def prove_oran(sys: System) -> Proof:
    """oran: ( φ ∨ ψ ) ↔ ¬ ( ¬ φ ∧ ¬ ψ ).

    De Morgan's law for disjunction (biconditional form).
    set.mm proof: pm4.56 con2bii.
    """
    lb = ProofBuilder(sys, "oran")
    s1 = lb.ref(
        "s1",
        "( ¬ φ ∧ ¬ ψ ) ↔ ¬ ( φ ∨ ψ )",
        ref="pm4.56",
        note="pm4.56",
    )
    res = lb.ref(
        "res",
        "( φ ∨ ψ ) ↔ ¬ ( ¬ φ ∧ ¬ ψ )",
        s1,
        ref="con2bii",
        note="con2bii",
    )
    return lb.build(res)


def prove_pm3_14(sys: System) -> Proof:
    """pm3.14: ( ¬ φ ∨ ¬ ψ ) → ¬ ( φ ∧ ψ ).

    A conjunction is false if one of its components is false.
    set.mm proof: pm3.1 con2i.
    """
    lb = ProofBuilder(sys, "pm3.14")
    s1 = lb.ref(
        "s1",
        "( φ ∧ ψ ) → ¬ ( ¬ φ ∨ ¬ ψ )",
        ref="pm3.1",
        note="pm3.1",
    )
    res = lb.ref(
        "res",
        "( ¬ φ ∨ ¬ ψ ) → ¬ ( φ ∧ ψ )",
        s1,
        ref="con2i",
        note="con2i",
    )
    return lb.build(res)


def prove_pm4_53(sys: System) -> Proof:
    """pm4.53: ¬ ( φ ∧ ¬ ψ ) ↔ ( ¬ φ ∨ ψ ).

    Equivalence between negated conjunction and disjunction.
    set.mm proof: pm4.52 con2bii bicomi.
    """
    lb = ProofBuilder(sys, "pm4.53")

    # pm4.52: ( φ ∧ ¬ ψ ) ↔ ¬ ( ¬ φ ∨ ψ )
    s1 = lb.ref(
        "s1",
        "( φ ∧ ¬ ψ ) ↔ ¬ ( ¬ φ ∨ ψ )",
        ref="pm4.52",
        note="pm4.52",
    )

    # con2bii: ( ¬ φ ∨ ψ ) ↔ ¬ ( φ ∧ ¬ ψ )
    s2 = lb.ref(
        "s2",
        "( ¬ φ ∨ ψ ) ↔ ¬ ( φ ∧ ¬ ψ )",
        s1,
        ref="con2bii",
        note="con2bii",
    )

    # bicomi: ¬ ( φ ∧ ¬ ψ ) ↔ ( ¬ φ ∨ ψ )
    res = lb.ref(
        "res",
        "¬ ( φ ∧ ¬ ψ ) ↔ ( ¬ φ ∨ ψ )",
        s2,
        ref="bicomi",
        note="bicomi",
    )
    return lb.build(res)


def prove_pm5_75(sys: System) -> Proof:
    """pm5.75: ( ( χ → ¬ ψ ) ∧ ( φ ↔ ( ψ ∨ χ ) ) ) → ( ( φ ∧ ¬ ψ ) ↔ χ ).

    Equivalence of a conjunction with a consequent given a biconditional and
    an implication hypothesis.  (Contributed by NM, 5-Aug-1993.)
    set.mm proof: anbi1 biorf bicomd pm5.32ri bitrdi abai rbaib sylan9bbr.
    """
    lb = ProofBuilder(sys, "pm5.75")

    # anbi1: ( φ ↔ ( ψ ∨ χ ) ) → ( ( φ ∧ ¬ ψ ) ↔ ( ( ψ ∨ χ ) ∧ ¬ ψ ) )
    s1 = lb.ref(
        "s1",
        "( ( φ ↔ ( ψ ∨ χ ) ) → ( ( φ ∧ ¬ ψ ) ↔ ( ( ψ ∨ χ ) ∧ ¬ ψ ) ) )",
        ref="anbi1",
        note="anbi1",
    )

    # biorf: ¬ ψ → ( χ ↔ ( ψ ∨ χ ) )
    s2 = lb.ref(
        "s2",
        "( ¬ ψ → ( χ ↔ ( ψ ∨ χ ) ) )",
        ref="biorf",
        note="biorf",
    )

    # bicomd on s2: ¬ ψ → ( ( ψ ∨ χ ) ↔ χ )
    s3 = lb.ref(
        "s3",
        "( ¬ ψ → ( ( ψ ∨ χ ) ↔ χ ) )",
        s2,
        ref="bicomd",
        note="bicomd",
    )

    # pm5.32ri on s3: ( ( ψ ∨ χ ) ∧ ¬ ψ ) ↔ ( χ ∧ ¬ ψ )
    s4 = lb.ref(
        "s4",
        "( ( ( ψ ∨ χ ) ∧ ¬ ψ ) ↔ ( χ ∧ ¬ ψ ) )",
        s3,
        ref="pm5.32ri",
        note="pm5.32ri",
    )

    # bitrdi on s1, s4: ( φ ↔ ( ψ ∨ χ ) ) → ( ( φ ∧ ¬ ψ ) ↔ ( χ ∧ ¬ ψ ) )
    s5 = lb.ref(
        "s5",
        "( ( φ ↔ ( ψ ∨ χ ) ) → ( ( φ ∧ ¬ ψ ) ↔ ( χ ∧ ¬ ψ ) ) )",
        s1,
        s4,
        ref="bitrdi",
        note="bitrdi",
    )

    # abai: ( χ ∧ ¬ ψ ) ↔ ( χ ∧ ( χ → ¬ ψ ) )
    s6 = lb.ref(
        "s6",
        "( ( χ ∧ ¬ ψ ) ↔ ( χ ∧ ( χ → ¬ ψ ) ) )",
        ref="abai",
        note="abai",
    )

    # rbaib on s6: ( χ → ¬ ψ ) → ( ( χ ∧ ¬ ψ ) ↔ χ )
    s7 = lb.ref(
        "s7",
        "( ( χ → ¬ ψ ) → ( ( χ ∧ ¬ ψ ) ↔ χ ) )",
        s6,
        ref="rbaib",
        note="rbaib",
    )

    # sylan9bbr on s5, s7: conclusion
    res = lb.ref(
        "res",
        "( ( ( χ → ¬ ψ ) ∧ ( φ ↔ ( ψ ∨ χ ) ) ) → ( ( φ ∧ ¬ ψ ) ↔ χ ) )",
        s5,
        s7,
        ref="sylan9bbr",
        note="sylan9bbr",
    )

    return lb.build(res)


def prove_prlem1(sys: System) -> Proof:
    """prlem1: φ → (ψ → (((ψ ∧ χ) ∨ (θ ∧ τ)) → η)).

    Lemma for disjunction with biconditional and negation hypotheses.
    The proof uses biimprd to reverse the biconditional,
    adantld/pm2.21d/adantrd to introduce conjunctive antecedents,
    jaao to join the cases, and ex to export ψ.
    """
    lb = ProofBuilder(sys, "prlem1")
    h1 = lb.hyp("prlem1.1", "φ → ( η ↔ χ )")
    h2 = lb.hyp("prlem1.2", "ψ → ¬ θ")

    s1 = lb.ref("s1", "φ → ( χ → η )", h1, ref="biimprd", note="biimprd")
    s2 = lb.ref("s2", "φ → ( ( ψ ∧ χ ) → η )", s1, ref="adantld", note="adantld")
    s3 = lb.ref("s3", "ψ → ( θ → η )", h2, ref="pm2.21d", note="pm2.21d")
    s4 = lb.ref("s4", "ψ → ( ( θ ∧ τ ) → η )", s3, ref="adantrd", note="adantrd")
    s5 = lb.ref(
        "s5",
        "( φ ∧ ψ ) → ( ( ( ψ ∧ χ ) ∨ ( θ ∧ τ ) ) → η )",
        s2,
        s4,
        ref="jaao",
        note="jaao",
    )
    res = lb.ref(
        "res",
        "φ → ( ψ → ( ( ( ψ ∧ χ ) ∨ ( θ ∧ τ ) ) → η ) )",
        s5,
        ref="ex",
        note="ex",
    )
    return lb.build(res)


def prove_prlem2(sys: System) -> Proof:
    """prlem2: ( ( φ ∧ ψ ) ∨ ( χ ∧ θ ) ) ↔ ( ( φ ∨ χ ) ∧ ( ( φ ∧ ψ ) ∨ ( χ ∧ θ ) ) ).

    A lemma for disjunction and conjunction properties, using simpl, orim12i, and pm4.71ri.
    """
    lb = ProofBuilder(sys, "prlem2")

    s1 = lb.ref("s1", "( φ ∧ ψ ) → φ", ref="simpl", note="simpl")
    s2 = lb.ref("s2", "( χ ∧ θ ) → χ", ref="simpl", note="simpl")
    s3 = lb.ref(
        "s3",
        "( ( φ ∧ ψ ) ∨ ( χ ∧ θ ) ) → ( φ ∨ χ )",
        s1,
        s2,
        ref="orim12i",
        note="orim12i",
    )
    res = lb.ref(
        "res",
        "( ( φ ∧ ψ ) ∨ ( χ ∧ θ ) ) ↔ ( ( φ ∨ χ ) ∧ ( ( φ ∧ ψ ) ∨ ( χ ∧ θ ) ) )",
        s3,
        ref="pm4.71ri",
        note="pm4.71ri",
    )
    return lb.build(res)


def prove_dfbi3(sys: System) -> Proof:
    """dfbi3: ( φ ↔ ψ ) ↔ ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ ¬ ψ ) ).

    Express the biconditional as a disjunction of conjunctions: both true
    or both false.
    """
    lb = ProofBuilder(sys, "dfbi3")

    # con34b: ( ( ψ → φ ) ↔ ( ¬ φ → ¬ ψ ) )
    s1 = lb.ref(
        "s1",
        "( ( ψ → φ ) ↔ ( ¬ φ → ¬ ψ ) )",
        ref="con34b",
        note="con34b(ψ, φ)",
    )

    # anbi2i: con34b as hypothesis, χ := ( φ → ψ )
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

    # cases2 with χ := ¬ ψ
    s4 = lb.ref(
        "s4",
        "( ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ ¬ ψ ) ) ↔ ( ( φ → ψ ) ∧ ( ¬ φ → ¬ ψ ) ) )",
        ref="cases2",
        note="cases2",
    )

    # 3bitr4i: s2 (ph↔ps), s3 (ch↔ph), s4 (th↔ps) → ch↔th
    res = lb.ref(
        "res",
        "( ( φ ↔ ψ ) ↔ ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ ¬ ψ ) ) )",
        s2,
        s3,
        s4,
        ref="3bitr4i",
        note="3bitr4i",
    )

    return lb.build(res)


def prove_pm5_54(sys: System) -> Proof:
    """pm5.54: ( ( φ ∧ ψ ) ↔ φ ) ∨ ( ( φ ∧ ψ ) ↔ ψ ).

    One of the two biconditionals always holds — either the conjunction
    is equivalent to the left conjunct, or it is equivalent to the right
    conjunct.
    """
    lb = ProofBuilder(sys, "pm5.54")

    # iba(ψ, φ): ψ → ( φ ↔ ( φ ∧ ψ ) )
    s_iba = lb.ref("s_iba", "ψ → ( φ ↔ ( φ ∧ ψ ) )", ref="iba", note="iba")

    # bicomd: ψ → ( ( φ ∧ ψ ) ↔ φ )
    s_bic = lb.ref("s_bic", "ψ → ( ( φ ∧ ψ ) ↔ φ )", s_iba, ref="bicomd", note="bicomd")

    # adantl: ( φ ∧ ψ ) → ( ( φ ∧ ψ ) ↔ φ )
    s_ad = lb.ref(
        "s_ad",
        "( φ ∧ ψ ) → ( ( φ ∧ ψ ) ↔ φ )",
        s_bic,
        ref="adantl",
        note="adantl",
    )

    # pm5.21ni(s_ad, s_bic): ¬ ( ( φ ∧ ψ ) ↔ φ ) → ( ( φ ∧ ψ ) ↔ ψ )
    s_pm = lb.ref(
        "s_pm",
        "¬ ( ( φ ∧ ψ ) ↔ φ ) → ( ( φ ∧ ψ ) ↔ ψ )",
        s_ad,
        s_bic,
        ref="pm5.21ni",
        note="pm5.21ni",
    )

    # orri: ( ( φ ∧ ψ ) ↔ φ ) ∨ ( ( φ ∧ ψ ) ↔ ψ )
    res = lb.ref(
        "res",
        "( ( ( φ ∧ ψ ) ↔ φ ) ∨ ( ( φ ∧ ψ ) ↔ ψ ) )",
        s_pm,
        ref="orri",
        note="orri",
    )

    return lb.build(res)


def prove_noror(sys: System) -> Proof:
    """noror: ( φ ∨ ψ ) ↔ ( ( φ ⊽ ψ ) ⊽ ( φ ⊽ ψ ) ).

    Disjunction expressed in terms of NOR: (φ ∨ ψ) is equivalent to
    (φ ⊽ ψ) ⊽ (φ ⊽ ψ).
    """
    lb = ProofBuilder(sys, "noror")

    # df-nor: ( φ ⊽ ψ ) ↔ ¬ ( φ ∨ ψ )
    s1 = lb.ref(
        "s1",
        "( φ ⊽ ψ ) ↔ ¬ ( φ ∨ ψ )",
        ref="df-nor",
        note="df-nor",
    )

    # con2bii: ( φ ∨ ψ ) ↔ ¬ ( φ ⊽ ψ )
    s2 = lb.ref(
        "s2",
        "( φ ∨ ψ ) ↔ ¬ ( φ ⊽ ψ )",
        s1,
        ref="con2bii",
        note="con2bii",
    )

    # nornot: ¬ ( φ ⊽ ψ ) ↔ ( ( φ ⊽ ψ ) ⊽ ( φ ⊽ ψ ) )
    s3 = lb.ref(
        "s3",
        "¬ ( φ ⊽ ψ ) ↔ ( ( φ ⊽ ψ ) ⊽ ( φ ⊽ ψ ) )",
        ref="nornot",
        note="nornot",
    )

    # bitri: ( φ ∨ ψ ) ↔ ( ( φ ⊽ ψ ) ⊽ ( φ ⊽ ψ ) )
    res = lb.ref(
        "res",
        "( φ ∨ ψ ) ↔ ( ( φ ⊽ ψ ) ⊽ ( φ ⊽ ψ ) )",
        s2,
        s3,
        ref="bitri",
        note="bitri",
    )

    return lb.build(res)


def prove_dfifp3(sys: System) -> Proof:
    """dfifp3: ( if- φ ψ χ ↔ ( ( φ → ψ ) ∧ ( φ ∨ χ ) ) ).

    Alternate definition of if- using disjunction in place of
    negated antecedent.
    """
    lb = ProofBuilder(sys, "dfifp3")

    s1 = lb.ref(
        "s1",
        "( if- φ ψ χ ↔ ( ( φ → ψ ) ∧ ( ¬ φ → χ ) ) )",
        ref="dfifp2",
        note="dfifp2",
    )

    s2 = lb.ref(
        "s2",
        "( ¬ φ → χ ) ↔ ( φ ∨ χ )",
        ref="pm4.64",
        note="pm4.64",
    )

    s3 = lb.ref(
        "s3",
        "( ( φ → ψ ) ∧ ( ¬ φ → χ ) ) ↔ ( ( φ → ψ ) ∧ ( φ ∨ χ ) )",
        s2,
        ref="anbi2i",
        note="anbi2i",
    )

    res = lb.ref(
        "res",
        "( if- φ ψ χ ↔ ( ( φ → ψ ) ∧ ( φ ∨ χ ) ) )",
        s1,
        s3,
        ref="bitri",
        note="bitri",
    )

    return lb.build(res)


def prove_dfifp4(sys: System) -> Proof:
    """dfifp4: ( if- φ ψ χ ↔ ( ( ¬ φ ∨ ψ ) ∧ ( φ ∨ χ ) ) ).

    Alternate definition of if- using disjunction to replace implication
    in both conjuncts.
    """
    lb = ProofBuilder(sys, "dfifp4")

    s1 = lb.ref(
        "s1",
        "( if- φ ψ χ ↔ ( ( φ → ψ ) ∧ ( φ ∨ χ ) ) )",
        ref="dfifp3",
        note="dfifp3",
    )

    s2 = lb.ref(
        "s2",
        "( ( φ → ψ ) ↔ ( ¬ φ ∨ ψ ) )",
        ref="imor",
        note="imor",
    )

    res = lb.ref(
        "res",
        "( if- φ ψ χ ↔ ( ( ¬ φ ∨ ψ ) ∧ ( φ ∨ χ ) ) )",
        s1,
        s2,
        ref="bianbi",
        note="bianbi",
    )

    return lb.build(res)


def prove_dfifp6(sys: System) -> Proof:
    """dfifp6: ( if- φ ψ χ ↔ ( ( φ ∧ ψ ) ∨ ¬ ( χ → φ ) ) ).

    Alternate definition of if- using disjunction and negation of
    implication.
    """
    lb = ProofBuilder(sys, "dfifp6")

    # df-ifp: ( if- φ ψ χ ↔ ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) ) )
    s1 = lb.ref(
        "s1",
        "( if- φ ψ χ ↔ ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) ) )",
        ref="df-ifp",
        note="df-ifp",
    )

    # ancom: ( ¬ φ ∧ χ ) ↔ ( χ ∧ ¬ φ )
    s2 = lb.ref(
        "s2",
        "( ¬ φ ∧ χ ) ↔ ( χ ∧ ¬ φ )",
        ref="ancom",
        note="ancom",
    )

    # annim: ( χ ∧ ¬ φ ) ↔ ¬ ( χ → φ )
    s3 = lb.ref(
        "s3",
        "( χ ∧ ¬ φ ) ↔ ¬ ( χ → φ )",
        ref="annim",
        note="annim",
    )

    # bitri: ( ¬ φ ∧ χ ) ↔ ¬ ( χ → φ )
    s4 = lb.ref(
        "s4",
        "( ¬ φ ∧ χ ) ↔ ¬ ( χ → φ )",
        s2,
        s3,
        ref="bitri",
        note="bitri",
    )

    # orbi2i: ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) ) ↔ ( ( φ ∧ ψ ) ∨ ¬ ( χ → φ ) )
    s5 = lb.ref(
        "s5",
        "( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) ) ↔ ( ( φ ∧ ψ ) ∨ ¬ ( χ → φ ) )",
        s4,
        ref="orbi2i",
        note="orbi2i",
    )

    # bitri: final result
    res = lb.ref(
        "res",
        "( if- φ ψ χ ↔ ( ( φ ∧ ψ ) ∨ ¬ ( χ → φ ) ) )",
        s1,
        s5,
        ref="bitri",
        note="bitri",
    )

    return lb.build(res)


def prove_dfifp5(sys: System) -> Proof:
    """dfifp5: ( if- φ ψ χ ↔ ( ( ¬ φ ∨ ψ ) ∧ ( ¬ φ → χ ) ) ).

    Alternate definition of if- using disjunction in place of implication.
    """
    lb = ProofBuilder(sys, "dfifp5")

    s1 = lb.ref(
        "s1",
        "( if- φ ψ χ ↔ ( ( φ → ψ ) ∧ ( ¬ φ → χ ) ) )",
        ref="dfifp2",
        note="dfifp2",
    )

    s2 = lb.ref(
        "s2",
        "( ( φ → ψ ) ↔ ( ¬ φ ∨ ψ ) )",
        ref="imor",
        note="imor",
    )

    res = lb.ref(
        "res",
        "( if- φ ψ χ ↔ ( ( ¬ φ ∨ ψ ) ∧ ( ¬ φ → χ ) ) )",
        s1,
        s2,
        ref="bianbi",
        note="bianbi",
    )

    return lb.build(res)


def prove_rb_bijust(sys: System) -> Proof:
    """rb-bijust: ( φ ↔ ψ ) ↔ ¬ ( ¬ ( ¬ φ ∨ ψ ) ∨ ¬ ( ¬ ψ ∨ φ ) ).

    A "justification" theorem for the weak bi-implication expressed with
    disjunctions.  (Contributed by NM, 30-Aug-1993.)
    """
    lb = ProofBuilder(sys, "rb-bijust")

    # dfbi1: ( φ ↔ ψ ) ↔ ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) )
    s1 = lb.ref(
        "s1",
        "( φ ↔ ψ ) ↔ ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) )",
        ref="dfbi1",
        note="dfbi1",
    )

    # imor: ( φ → ψ ) ↔ ( ¬ φ ∨ ψ )
    s2 = lb.ref(
        "s2",
        "( φ → ψ ) ↔ ( ¬ φ ∨ ψ )",
        ref="imor",
        note="imor",
    )

    # imor: ( ψ → φ ) ↔ ( ¬ ψ ∨ φ )
    s3 = lb.ref(
        "s3",
        "( ψ → φ ) ↔ ( ¬ ψ ∨ φ )",
        ref="imor",
        note="imor",
    )

    # notbii on s3: ¬ ( ψ → φ ) ↔ ¬ ( ¬ ψ ∨ φ )
    s4 = lb.ref(
        "s4",
        "¬ ( ψ → φ ) ↔ ¬ ( ¬ ψ ∨ φ )",
        s3,
        ref="notbii",
        note="notbii",
    )

    # imbi12i on s2, s4: ( ( φ → ψ ) → ¬ ( ψ → φ ) ) ↔ ( ( ¬ φ ∨ ψ ) → ¬ ( ¬ ψ ∨ φ ) )
    s5 = lb.ref(
        "s5",
        "( ( φ → ψ ) → ¬ ( ψ → φ ) ) ↔ ( ( ¬ φ ∨ ψ ) → ¬ ( ¬ ψ ∨ φ ) )",
        s2,
        s4,
        ref="imbi12i",
        note="imbi12i",
    )

    # pm4.62: ( ( ¬ φ ∨ ψ ) → ¬ ( ¬ ψ ∨ φ ) ) ↔ ( ¬ ( ¬ φ ∨ ψ ) ∨ ¬ ( ¬ ψ ∨ φ ) )
    s6 = lb.ref(
        "s6",
        "( ( ¬ φ ∨ ψ ) → ¬ ( ¬ ψ ∨ φ ) ) ↔ ( ¬ ( ¬ φ ∨ ψ ) ∨ ¬ ( ¬ ψ ∨ φ ) )",
        ref="pm4.62",
        note="pm4.62",
    )

    # notbii on s5: ¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) ↔ ¬ ( ( ¬ φ ∨ ψ ) → ¬ ( ¬ ψ ∨ φ ) )
    s7 = lb.ref(
        "s7",
        "¬ ( ( φ → ψ ) → ¬ ( ψ → φ ) ) ↔ ¬ ( ( ¬ φ ∨ ψ ) → ¬ ( ¬ ψ ∨ φ ) )",
        s5,
        ref="notbii",
        note="notbii",
    )

    # notbii on s6: ¬ ( ( ¬ φ ∨ ψ ) → ¬ ( ¬ ψ ∨ φ ) ) ↔ ¬ ( ¬ ( ¬ φ ∨ ψ ) ∨ ¬ ( ¬ ψ ∨ φ ) )
    s8 = lb.ref(
        "s8",
        "¬ ( ( ¬ φ ∨ ψ ) → ¬ ( ¬ ψ ∨ φ ) ) ↔ ¬ ( ¬ ( ¬ φ ∨ ψ ) ∨ ¬ ( ¬ ψ ∨ φ ) )",
        s6,
        ref="notbii",
        note="notbii",
    )

    # 3bitri: ( φ ↔ ψ ) ↔ ¬ ( ¬ ( ¬ φ ∨ ψ ) ∨ ¬ ( ¬ ψ ∨ φ ) )
    res = lb.ref(
        "res",
        "( φ ↔ ψ ) ↔ ¬ ( ¬ ( ¬ φ ∨ ψ ) ∨ ¬ ( ¬ ψ ∨ φ ) )",
        s1,
        s7,
        s8,
        ref="3bitri",
        note="3bitri",
    )

    return lb.build(res)


def prove_rb_imdf(sys: System) -> Proof:
    """rb-imdf: ¬ ( ¬ ( ¬ ( φ → ψ ) ∨ ( ¬ φ ∨ ψ ) ) ∨ ¬ ( ¬ ( ¬ φ ∨ ψ ) ∨ ( φ → ψ ) ) ).

    "justification" definition of the bi-implication connective via
    implication and disjunction.  (Contributed by NM, 30-Aug-1993.)
    """
    lb = ProofBuilder(sys, "rb-imdf")

    s1 = lb.ref(
        "s1",
        "( φ → ψ ) ↔ ( ¬ φ ∨ ψ )",
        ref="imor",
        note="imor",
    )

    s2 = lb.ref(
        "s2",
        "( ( φ → ψ ) ↔ ( ¬ φ ∨ ψ ) ) ↔ ¬ ( ¬ ( ¬ ( φ → ψ ) ∨ ( ¬ φ ∨ ψ ) ) ∨ ¬ ( ¬ ( ¬ φ ∨ ψ ) ∨ ( φ → ψ ) ) )",
        ref="rb-bijust",
        note="rb-bijust",
    )

    res = lb.ref(
        "res",
        "¬ ( ¬ ( ¬ ( φ → ψ ) ∨ ( ¬ φ ∨ ψ ) ) ∨ ¬ ( ¬ ( ¬ φ ∨ ψ ) ∨ ( φ → ψ ) ) )",
        s1,
        s2,
        ref="mpbi",
        note="mpbi",
    )

    return lb.build(res)


def prove_re1axmp(sys: System) -> Proof:
    """re1axmp: ψ.

    Hyp: φ, φ → ψ.

    Robinson-style modus ponens derived from rb-imdf, rblem6, and anmp.
    """
    lb = ProofBuilder(sys, "re1axmp")
    h1 = lb.hyp("re1axmp.min", "φ")
    h2 = lb.hyp("re1axmp.maj", "φ → ψ")

    s1 = lb.ref(
        "s1",
        "¬ ( ¬ ( ¬ ( φ → ψ ) ∨ ( ¬ φ ∨ ψ ) ) ∨ ¬ ( ¬ ( ¬ φ ∨ ψ ) ∨ ( φ → ψ ) ) )",
        ref="rb-imdf",
        note="rb-imdf",
    )

    s2 = lb.ref(
        "s2",
        "¬ ( φ → ψ ) ∨ ( ¬ φ ∨ ψ )",
        s1,
        ref="rblem6",
        note="rblem6",
    )

    s3 = lb.ref(
        "s3",
        "¬ φ ∨ ψ",
        h2,
        s2,
        ref="anmp",
        note="anmp re1axmp.maj, s2",
    )

    res = lb.ref(
        "res",
        "ψ",
        h1,
        s3,
        ref="anmp",
        note="anmp re1axmp.min, s3",
    )

    return lb.build(res)


def prove_dn1(sys: System) -> Proof:
    """dn1: ( ¬ ( ¬ ( ¬ ( φ ∨ ψ ) ∨ χ ) ∨ ¬ ( φ ∨ ¬ ( ¬ χ ∨ ¬ ( χ ∨ θ ) ) ) ) ↔ χ ).

    A single axiom for Nicod's reduction of propositional calculus to a
    single connective.  Derived from Hilbert-style axioms.
    set.mm proof: pm2.45, imnan, mpbi, biorfri, orcom, ordir, 3bitri,
    pm4.45, bitri, orbi2i, anor, anbi2i, 3bitrri.
    """
    lb = ProofBuilder(sys, "dn1")

    # pm2.45: ¬ ( φ ∨ ψ ) → ¬ φ
    s_pm2_45 = lb.ref("s_pm2_45", "( ¬ ( φ ∨ ψ ) → ¬ φ )", ref="pm2.45", note="pm2.45")

    # imnan: ( ¬ ( φ ∨ ψ ) → ¬ φ ) ↔ ¬ ( ¬ ( φ ∨ ψ ) ∧ φ )
    s_imnan = lb.ref(
        "s_imnan",
        "( ( ¬ ( φ ∨ ψ ) → ¬ φ ) ↔ ¬ ( ¬ ( φ ∨ ψ ) ∧ φ ) )",
        ref="imnan",
        note="imnan",
    )

    # mpbi: apply mpbi to pm2.45 and imnan → ¬ ( ¬ ( φ ∨ ψ ) ∧ φ )
    s_mpbi = lb.ref(
        "s_mpbi",
        "¬ ( ¬ ( φ ∨ ψ ) ∧ φ )",
        s_pm2_45,
        s_imnan,
        ref="mpbi",
        note="mpbi",
    )

    # biorfri: using s_mpbi as hypothesis, get χ ↔ ( χ ∨ ( ¬ ( φ ∨ ψ ) ∧ φ ) )
    s_biorfri = lb.ref(
        "s_biorfri",
        "( χ ↔ ( χ ∨ ( ¬ ( φ ∨ ψ ) ∧ φ ) ) )",
        s_mpbi,
        ref="biorfri",
        note="biorfri",
    )

    # orcom: ( χ ∨ ( ¬ ( φ ∨ ψ ) ∧ φ ) ) ↔ ( ( ¬ ( φ ∨ ψ ) ∧ φ ) ∨ χ )
    s_orcom = lb.ref(
        "s_orcom",
        "( ( χ ∨ ( ¬ ( φ ∨ ψ ) ∧ φ ) ) ↔ ( ( ¬ ( φ ∨ ψ ) ∧ φ ) ∨ χ ) )",
        ref="orcom",
        note="orcom",
    )

    # ordir: ( ( ¬ ( φ ∨ ψ ) ∧ φ ) ∨ χ ) ↔ ( ( ¬ ( φ ∨ ψ ) ∨ χ ) ∧ ( φ ∨ χ ) )
    s_ordir = lb.ref(
        "s_ordir",
        "( ( ( ¬ ( φ ∨ ψ ) ∧ φ ) ∨ χ ) ↔ ( ( ¬ ( φ ∨ ψ ) ∨ χ ) ∧ ( φ ∨ χ ) ) )",
        ref="ordir",
        note="ordir",
    )

    # 3bitri: chain biorfri, orcom, ordir → χ ↔ ( ( ¬ ( φ ∨ ψ ) ∨ χ ) ∧ ( φ ∨ χ ) )
    s_3bitri = lb.ref(
        "s_3bitri",
        "( χ ↔ ( ( ¬ ( φ ∨ ψ ) ∨ χ ) ∧ ( φ ∨ χ ) ) )",
        s_biorfri,
        s_orcom,
        s_ordir,
        ref="3bitri",
        note="3bitri",
    )

    # pm4.45: χ ↔ ( χ ∧ ( χ ∨ θ ) )
    s_pm4_45 = lb.ref("s_pm4_45", "( χ ↔ ( χ ∧ ( χ ∨ θ ) ) )", ref="pm4.45", note="pm4.45")

    # anor: ( χ ∧ ( χ ∨ θ ) ) ↔ ¬ ( ¬ χ ∨ ¬ ( χ ∨ θ ) )
    s_anor = lb.ref(
        "s_anor",
        "( ( χ ∧ ( χ ∨ θ ) ) ↔ ¬ ( ¬ χ ∨ ¬ ( χ ∨ θ ) ) )",
        ref="anor",
        note="anor",
    )

    # bitri: chain pm4.45 and anor → χ ↔ ¬ ( ¬ χ ∨ ¬ ( χ ∨ θ ) )
    s_bitri = lb.ref(
        "s_bitri",
        "( χ ↔ ¬ ( ¬ χ ∨ ¬ ( χ ∨ θ ) ) )",
        s_pm4_45,
        s_anor,
        ref="bitri",
        note="bitri",
    )

    # orbi2i: from bitri, ( φ ∨ χ ) ↔ ( φ ∨ ¬ ( ¬ χ ∨ ¬ ( χ ∨ θ ) ) )
    s_orbi2i = lb.ref(
        "s_orbi2i",
        "( ( φ ∨ χ ) ↔ ( φ ∨ ¬ ( ¬ χ ∨ ¬ ( χ ∨ θ ) ) ) )",
        s_bitri,
        ref="orbi2i",
        note="orbi2i",
    )

    # anbi2i: from orbi2i,
    # ( ( ¬ ( φ ∨ ψ ) ∨ χ ) ∧ ( φ ∨ χ ) ) ↔
    #   ( ( ¬ ( φ ∨ ψ ) ∨ χ ) ∧ ( φ ∨ ¬ ( ¬ χ ∨ ¬ ( χ ∨ θ ) ) ) )
    s_anbi2i = lb.ref(
        "s_anbi2i",
        "( ( ( ¬ ( φ ∨ ψ ) ∨ χ ) ∧ ( φ ∨ χ ) ) ↔ ( ( ¬ ( φ ∨ ψ ) ∨ χ ) ∧ ( φ ∨ ¬ ( ¬ χ ∨ ¬ ( χ ∨ θ ) ) ) ) )",
        s_orbi2i,
        ref="anbi2i",
        note="anbi2i",
    )

    # anor:
    # ( ( ¬ ( φ ∨ ψ ) ∨ χ ) ∧ ( φ ∨ ¬ ( ¬ χ ∨ ¬ ( χ ∨ θ ) ) ) ) ↔
    #   ¬ ( ¬ ( ¬ ( φ ∨ ψ ) ∨ χ ) ∨ ¬ ( φ ∨ ¬ ( ¬ χ ∨ ¬ ( χ ∨ θ ) ) ) )
    s_anor2 = lb.ref(
        "s_anor2",
        "( ( ( ¬ ( φ ∨ ψ ) ∨ χ ) ∧ ( φ ∨ ¬ ( ¬ χ ∨ ¬ ( χ ∨ θ ) ) ) ) ↔ ¬ ( ¬ ( ¬ ( φ ∨ ψ ) ∨ χ ) ∨ ¬ ( φ ∨ ¬ ( ¬ χ ∨ ¬ ( χ ∨ θ ) ) ) ) )",
        ref="anor",
        note="anor",
    )

    # 3bitrri: chain s_3bitri, s_anbi2i, s_anor2 →
    #   ( ¬ ( ¬ ( ¬ ( φ ∨ ψ ) ∨ χ ) ∨ ¬ ( φ ∨ ¬ ( ¬ χ ∨ ¬ ( χ ∨ θ ) ) ) ) ↔ χ )
    res = lb.ref(
        "res",
        "( ¬ ( ¬ ( ¬ ( φ ∨ ψ ) ∨ χ ) ∨ ¬ ( φ ∨ ¬ ( ¬ χ ∨ ¬ ( χ ∨ θ ) ) ) ) ↔ χ )",
        s_3bitri,
        s_anbi2i,
        s_anor2,
        ref="3bitrri",
        note="3bitrri",
    )

    return lb.build(res)


def prove_axio(sys: System) -> Proof:
    """axio: ((φ ∨ χ) → ψ) ↔ ((φ → ψ) ∧ (χ → ψ)).

    Identical to jaob.
    """
    lb = ProofBuilder(sys, "axio")
    res = lb.ref(
        "res",
        "( ( φ ∨ χ ) → ψ ) ↔ ( ( φ → ψ ) ∧ ( χ → ψ ) )",
        ref="jaob",
        note="jaob",
    )
    return lb.build(res)


def prove_pm4_39(sys: System) -> Proof:
    """pm4.39: ( ( φ ↔ χ ) ∧ ( ψ ↔ θ ) ) → ( ( φ ∨ ψ ) ↔ ( χ ∨ θ ) ).

    Distributing a conjunction of biconditionals over a disjunction.
    """
    lb = ProofBuilder(sys, "pm4.39")

    s1 = lb.ref(
        "s1",
        "( ( φ ↔ χ ) ∧ ( ψ ↔ θ ) ) → ( φ ↔ χ )",
        ref="simpl",
        note="simpl",
    )
    s2 = lb.ref(
        "s2",
        "( ( φ ↔ χ ) ∧ ( ψ ↔ θ ) ) → ( ψ ↔ θ )",
        ref="simpr",
        note="simpr",
    )
    res = lb.ref(
        "res",
        "( ( φ ↔ χ ) ∧ ( ψ ↔ θ ) ) → ( ( φ ∨ ψ ) ↔ ( χ ∨ θ ) )",
        s1,
        s2,
        ref="orbi12d",
        note="orbi12d",
    )
    return lb.build(res)


def prove_ornld(sys: System) -> Proof:
    """ornld: φ → ( ( ( φ → ( θ ∨ τ ) ) ∧ ¬ θ ) → τ ).

    From a disjunctive implication remove the left disjunct.
    """
    lb = ProofBuilder(sys, "ornld")
    s1 = lb.ref(
        "s1",
        "( φ ∧ ( φ → ( θ ∨ τ ) ) ) → ( θ ∨ τ )",
        ref="pm3.35",
        note="pm3.35",
    )
    s2 = lb.ref(
        "s2",
        "( φ ∧ ( φ → ( θ ∨ τ ) ) ) → ( ¬ θ → τ )",
        s1,
        ref="ord",
        note="ord",
    )
    res = lb.ref(
        "res",
        "φ → ( ( ( φ → ( θ ∨ τ ) ) ∧ ¬ θ ) → τ )",
        s2,
        ref="expimpd",
        note="expimpd",
    )
    return lb.build(res)


def prove_ifpor(sys: System) -> Proof:
    """ifpor: if- φ ψ χ → ( ψ ∨ χ ).

    The conditional operator implies the disjunction of its second
    and third arguments.
    """
    lb = ProofBuilder(sys, "ifpor")
    s1 = lb.ref("s1", "( φ ∧ ψ ) → ψ", ref="simpr", note="simpr")
    s2 = lb.ref("s2", "( ¬ φ ∧ χ ) → χ", ref="simpr", note="simpr")
    s3 = lb.ref(
        "s3",
        "( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) ) → ( ψ ∨ χ )",
        s1,
        s2,
        ref="orim12i",
        note="orim12i",
    )
    s4 = lb.ref(
        "s4",
        "if- φ ψ χ ↔ ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ χ ) )",
        ref="df-ifp",
        note="df-ifp",
    )
    res = lb.ref(
        "res",
        "if- φ ψ χ → ( ψ ∨ χ )",
        s4,
        s3,
        ref="sylbi",
        note="sylbi",
    )
    return lb.build(res)


def prove_xor(sys: System) -> Proof:
    """xor: ¬ ( φ ↔ ψ ) ↔ ( ( φ ∧ ¬ ψ ) ∨ ( ψ ∧ ¬ φ ) ).

    Exclusive-or expressed with negation, conjunction, and disjunction.
    """
    lb = ProofBuilder(sys, "xor")

    s1 = lb.ref("s1", "( φ → ψ ) ↔ ¬ ( φ ∧ ¬ ψ )", ref="iman", note="iman")
    s2 = lb.ref("s2", "( ψ → φ ) ↔ ¬ ( ψ ∧ ¬ φ )", ref="iman", note="iman")
    s3 = lb.ref(
        "s3",
        "( ( φ → ψ ) ∧ ( ψ → φ ) ) ↔ ( ¬ ( φ ∧ ¬ ψ ) ∧ ¬ ( ψ ∧ ¬ φ ) )",
        s1,
        s2,
        ref="anbi12i",
        note="anbi12i",
    )
    s4 = lb.ref(
        "s4",
        "( φ ↔ ψ ) ↔ ( ( φ → ψ ) ∧ ( ψ → φ ) )",
        ref="dfbi2",
        note="dfbi2",
    )
    s5 = lb.ref(
        "s5",
        "¬ ( ( φ ∧ ¬ ψ ) ∨ ( ψ ∧ ¬ φ ) ) ↔ ( ¬ ( φ ∧ ¬ ψ ) ∧ ¬ ( ψ ∧ ¬ φ ) )",
        ref="ioran",
        note="ioran",
    )
    s6 = lb.ref(
        "s6",
        "¬ ( ( φ ∧ ¬ ψ ) ∨ ( ψ ∧ ¬ φ ) ) ↔ ( φ ↔ ψ )",
        s3,
        s4,
        s5,
        ref="3bitr4ri",
        note="3bitr4ri",
    )
    res = lb.ref(
        "res",
        "¬ ( φ ↔ ψ ) ↔ ( ( φ ∧ ¬ ψ ) ∨ ( ψ ∧ ¬ φ ) )",
        s6,
        ref="con1bii",
        note="con1bii",
    )

    return lb.build(res)


def prove_pm5_24(sys: System) -> Proof:
    """pm5.24: ¬ ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ ¬ ψ ) ) ↔ ( ( φ ∧ ¬ ψ ) ∨ ( ψ ∧ ¬ φ ) ).

    Negation of biconditional equivalence expressed as a disjunction of
    exclusive cases.
    """
    lb = ProofBuilder(sys, "pm5.24")

    s_xor = lb.ref(
        "s_xor",
        "¬ ( φ ↔ ψ ) ↔ ( ( φ ∧ ¬ ψ ) ∨ ( ψ ∧ ¬ φ ) )",
        ref="xor",
        note="xor",
    )

    s_dfbi3 = lb.ref(
        "s_dfbi3",
        "( φ ↔ ψ ) ↔ ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ ¬ ψ ) )",
        ref="dfbi3",
        note="dfbi3",
    )

    res = lb.ref(
        "res",
        "¬ ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ ¬ ψ ) ) ↔ ( ( φ ∧ ¬ ψ ) ∨ ( ψ ∧ ¬ φ ) )",
        s_xor,
        s_dfbi3,
        ref="xchnxbi",
        note="xchnxbi",
    )

    return lb.build(res)


def prove_4exmid(sys: System) -> Proof:
    """4exmid: ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ ¬ ψ ) ) ∨ ( ( φ ∧ ¬ ψ ) ∨ ( ψ ∧ ¬ φ ) ).

    Law of the excluded middle for four cases.
    """
    lb = ProofBuilder(sys, "4exmid")

    s1 = lb.ref(
        "s1",
        "¬ ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ ¬ ψ ) ) ↔ ( ( φ ∧ ¬ ψ ) ∨ ( ψ ∧ ¬ φ ) )",
        ref="pm5.24",
        note="pm5.24",
    )

    s2 = lb.ref(
        "s2",
        "¬ ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ ¬ ψ ) ) → ( ( φ ∧ ¬ ψ ) ∨ ( ψ ∧ ¬ φ ) )",
        s1,
        ref="biimpi",
        note="biimpi",
    )

    res = lb.ref(
        "res",
        "( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ ¬ ψ ) ) ∨ ( ( φ ∧ ¬ ψ ) ∨ ( ψ ∧ ¬ φ ) )",
        s2,
        ref="orri",
        note="orri",
    )

    return lb.build(res)


def prove_nbi2(sys: System) -> Proof:
    """nbi2: ( ¬ ( φ ↔ ψ ) ↔ ( ( φ ∨ ψ ) ∧ ¬ ( φ ∧ ψ ) ) ).

    Negated biconditional expressed as exclusive disjunction (XOR).
    """
    lb = ProofBuilder(sys, "nbi2")

    s_xor3 = lb.ref(
        "s_xor3",
        "( ¬ ( φ ↔ ψ ) ↔ ( φ ↔ ¬ ψ ) )",
        ref="xor3",
        note="xor3",
    )

    s_pm5_17 = lb.ref(
        "s_pm5_17",
        "( ( φ ∨ ψ ) ∧ ¬ ( φ ∧ ψ ) ) ↔ ( φ ↔ ¬ ψ )",
        ref="pm5.17",
        note="pm5.17",
    )

    res = lb.ref(
        "res",
        "( ¬ ( φ ↔ ψ ) ↔ ( ( φ ∨ ψ ) ∧ ¬ ( φ ∧ ψ ) ) )",
        s_xor3,
        s_pm5_17,
        ref="bitr4i",
        note="bitr4i",
    )

    return lb.build(res)


def prove_xor2(sys: System) -> Proof:
    """xor2: ( φ ⊻ ψ ) ↔ ( ( φ ∨ ψ ) ∧ ¬ ( φ ∧ ψ ) ).

    XOR expressed as exclusive disjunction: exclusive or is equivalent to
    the disjunction of the two propositions conjoined with the negation of
    their conjunction.
    """
    lb = ProofBuilder(sys, "xor2")

    s1 = lb.ref(
        "s1",
        "( φ ⊻ ψ ) ↔ ¬ ( φ ↔ ψ )",
        ref="df-xor",
        note="df-xor",
    )

    s2 = lb.ref(
        "s2",
        "¬ ( φ ↔ ψ ) ↔ ( ( φ ∨ ψ ) ∧ ¬ ( φ ∧ ψ ) )",
        ref="nbi2",
        note="nbi2",
    )

    res = lb.ref(
        "res",
        "( φ ⊻ ψ ) ↔ ( ( φ ∨ ψ ) ∧ ¬ ( φ ∧ ψ ) )",
        s1,
        s2,
        ref="bitri",
        note="bitri",
    )

    return lb.build(res)


def prove_xornan(sys: System) -> Proof:
    """xornan: ( φ ⊻ ψ ) → ¬ ( φ ∧ ψ ).

    Exclusive or implies not both. From xor2 via simprbi.
    """
    lb = ProofBuilder(sys, "xornan")

    # xor2: ( φ ⊻ ψ ) ↔ ( ( φ ∨ ψ ) ∧ ¬ ( φ ∧ ψ ) )
    s1 = lb.ref(
        "s1",
        "( φ ⊻ ψ ) ↔ ( ( φ ∨ ψ ) ∧ ¬ ( φ ∧ ψ ) )",
        ref="xor2",
        note="xor2",
    )

    # simprbi: from the biconditional, extract the second conjunct
    res = lb.ref(
        "res",
        "( φ ⊻ ψ ) → ¬ ( φ ∧ ψ )",
        s1,
        ref="simprbi",
        note="simprbi",
    )

    return lb.build(res)


def prove_xornan2(sys: System) -> Proof:
    """xornan2: ( φ ⊻ ψ ) → ( φ ⊼ ψ ).

    Exclusive or implies nand. From xornan and df-nan via sylibr.
    """
    lb = ProofBuilder(sys, "xornan2")

    # xornan: ( φ ⊻ ψ ) → ¬ ( φ ∧ ψ )
    s1 = lb.ref(
        "s1",
        "( φ ⊻ ψ ) → ¬ ( φ ∧ ψ )",
        ref="xornan",
        note="xornan",
    )

    # df-nan: ( φ ⊼ ψ ) ↔ ¬ ( φ ∧ ψ )
    s2 = lb.ref(
        "s2",
        "( φ ⊼ ψ ) ↔ ¬ ( φ ∧ ψ )",
        ref="df-nan",
        note="df-nan",
    )

    # sylibr: from the implication and biconditional, get the result
    res = lb.ref(
        "res",
        "( φ ⊻ ψ ) → ( φ ⊼ ψ )",
        s1,
        s2,
        ref="sylibr",
        note="sylibr",
    )

    return lb.build(res)


def prove_andi(sys: System) -> Proof:
    """andi: ( φ ∧ ( ψ ∨ χ ) ) ↔ ( ( φ ∧ ψ ) ∨ ( φ ∧ χ ) ).

    Distribution of conjunction over disjunction (∧ over ∨).
    Forward: jaodan with orc/olc.  Reverse: anim2i(orc/olc) then jaoi.
    Combined with impbii.
    """
    lb = ProofBuilder(sys, "andi")

    # Forward: ( φ ∧ ( ψ ∨ χ ) ) → ( ( φ ∧ ψ ) ∨ ( φ ∧ χ ) )
    s1 = lb.ref("s1", "( φ ∧ ψ ) → ( ( φ ∧ ψ ) ∨ ( φ ∧ χ ) )", ref="orc", note="orc")
    s2 = lb.ref("s2", "( φ ∧ χ ) → ( ( φ ∧ ψ ) ∨ ( φ ∧ χ ) )", ref="olc", note="olc")
    s3 = lb.ref(
        "s3",
        "( φ ∧ ( ψ ∨ χ ) ) → ( ( φ ∧ ψ ) ∨ ( φ ∧ χ ) )",
        s1,
        s2,
        ref="jaodan",
        note="jaodan(orc, olc)",
    )

    # Reverse: ( ( φ ∧ ψ ) ∨ ( φ ∧ χ ) ) → ( φ ∧ ( ψ ∨ χ ) )
    s4 = lb.ref("s4", "ψ → ( ψ ∨ χ )", ref="orc", note="orc")
    s5 = lb.ref("s5", "( φ ∧ ψ ) → ( φ ∧ ( ψ ∨ χ ) )", s4, ref="anim2i", note="anim2i(orc)")
    s6 = lb.ref("s6", "χ → ( ψ ∨ χ )", ref="olc", note="olc")
    s7 = lb.ref("s7", "( φ ∧ χ ) → ( φ ∧ ( ψ ∨ χ ) )", s6, ref="anim2i", note="anim2i(olc)")
    s8 = lb.ref(
        "s8",
        "( ( φ ∧ ψ ) ∨ ( φ ∧ χ ) ) → ( φ ∧ ( ψ ∨ χ ) )",
        s5,
        s7,
        ref="jaoi",
        note="jaoi(anim2i(orc), anim2i(olc))",
    )

    # Biconditional
    res = lb.ref(
        "res",
        "( φ ∧ ( ψ ∨ χ ) ) ↔ ( ( φ ∧ ψ ) ∨ ( φ ∧ χ ) )",
        s3,
        s8,
        ref="impbii",
        note="impbii(s3, s8)",
    )
    return lb.build(res)


def prove_andir(sys: System) -> Proof:
    """andir: ( ( φ ∨ ψ ) ∧ χ ) ↔ ( ( φ ∧ χ ) ∨ ( ψ ∧ χ ) ).

    Distribution of conjunction over disjunction — right-hand-side form.
    """
    lb = ProofBuilder(sys, "andir")

    # ancom: swap LHS conjunction
    s_ancom_l = lb.ref(
        "s_ancom_l",
        "( ( φ ∨ ψ ) ∧ χ ) ↔ ( χ ∧ ( φ ∨ ψ ) )",
        ref="ancom",
        note="ancom",
    )

    # andi: distribute χ over ( φ ∨ ψ )
    s_andi = lb.ref(
        "s_andi",
        "( χ ∧ ( φ ∨ ψ ) ) ↔ ( ( χ ∧ φ ) ∨ ( χ ∧ ψ ) )",
        ref="andi",
        note="andi",
    )

    # ancom: swap each conjunct on the RHS
    s_ancom_ph = lb.ref(
        "s_ancom_ph",
        "( φ ∧ χ ) ↔ ( χ ∧ φ )",
        ref="ancom",
        note="ancom",
    )

    s_ancom_ps = lb.ref(
        "s_ancom_ps",
        "( ψ ∧ χ ) ↔ ( χ ∧ ψ )",
        ref="ancom",
        note="ancom",
    )

    # orbi12i: combine the two ancom biconditionals with ∨
    s_orbi12i = lb.ref(
        "s_orbi12i",
        "( ( φ ∧ χ ) ∨ ( ψ ∧ χ ) ) ↔ ( ( χ ∧ φ ) ∨ ( χ ∧ ψ ) )",
        s_ancom_ph,
        s_ancom_ps,
        ref="orbi12i",
        note="orbi12i",
    )

    # 3bitr4i: chain inner, left, right equivalences
    res = lb.ref(
        "res",
        "( ( φ ∨ ψ ) ∧ χ ) ↔ ( ( φ ∧ χ ) ∨ ( ψ ∧ χ ) )",
        s_andi,
        s_ancom_l,
        s_orbi12i,
        ref="3bitr4i",
        note="3bitr4i",
    )

    return lb.build(res)


def prove_anddi(sys: System) -> Proof:
    """anddi: ( ( φ ∨ ψ ) ∧ ( χ ∨ θ ) ) ↔ ( ( ( φ ∧ χ ) ∨ ( φ ∧ θ ) ) ∨ ( ( ψ ∧ χ ) ∨ ( ψ ∧ θ ) ) ).

    Distribution of conjunction over disjunction — double distribution form.
    """
    lb = ProofBuilder(sys, "anddi")

    # andir: ( ( φ ∨ ψ ) ∧ ( χ ∨ θ ) ) ↔ ( ( φ ∧ ( χ ∨ θ ) ) ∨ ( ψ ∧ ( χ ∨ θ ) ) )
    s1 = lb.ref(
        "s1",
        "( ( φ ∨ ψ ) ∧ ( χ ∨ θ ) ) ↔ ( ( φ ∧ ( χ ∨ θ ) ) ∨ ( ψ ∧ ( χ ∨ θ ) ) )",
        ref="andir",
        note="andir",
    )

    # andi on left: ( φ ∧ ( χ ∨ θ ) ) ↔ ( ( φ ∧ χ ) ∨ ( φ ∧ θ ) )
    s2 = lb.ref(
        "s2",
        "( φ ∧ ( χ ∨ θ ) ) ↔ ( ( φ ∧ χ ) ∨ ( φ ∧ θ ) )",
        ref="andi",
        note="andi",
    )

    # andi on right: ( ψ ∧ ( χ ∨ θ ) ) ↔ ( ( ψ ∧ χ ) ∨ ( ψ ∧ θ ) )
    s3 = lb.ref(
        "s3",
        "( ψ ∧ ( χ ∨ θ ) ) ↔ ( ( ψ ∧ χ ) ∨ ( ψ ∧ θ ) )",
        ref="andi",
        note="andi",
    )

    # orbi12i: combine the two andi results
    s4 = lb.ref(
        "s4",
        "( ( φ ∧ ( χ ∨ θ ) ) ∨ ( ψ ∧ ( χ ∨ θ ) ) ) ↔ ( ( ( φ ∧ χ ) ∨ ( φ ∧ θ ) ) ∨ ( ( ψ ∧ χ ) ∨ ( ψ ∧ θ ) ) )",
        s2,
        s3,
        ref="orbi12i",
        note="orbi12i(andi, andi)",
    )

    # bitri: chain andir + orbi12i
    res = lb.ref(
        "res",
        "( ( φ ∨ ψ ) ∧ ( χ ∨ θ ) ) ↔ ( ( ( φ ∧ χ ) ∨ ( φ ∧ θ ) ) ∨ ( ( ψ ∧ χ ) ∨ ( ψ ∧ θ ) ) )",
        s1,
        s4,
        ref="bitri",
        note="bitri(andir, orbi12i)",
    )

    return lb.build(res)


def prove_cases(sys: System) -> Proof:
    """cases: ψ ↔ ( ( φ ∧ χ ) ∨ ( ¬ φ ∧ θ ) ).

    Case elimination: a biconditional can be deduced from two implication
    hypotheses that together cover all cases.
    """
    lb = ProofBuilder(sys, "cases")
    h1 = lb.hyp("cases.1", "φ → ( ψ ↔ χ )")
    h2 = lb.hyp("cases.2", "¬ φ → ( ψ ↔ θ )")

    # exmid: φ ∨ ¬ φ
    s1 = lb.ref("s1", "( φ ∨ ¬ φ )", ref="exmid", note="exmid")

    # biantrur: ψ ↔ ( ( φ ∨ ¬ φ ) ∧ ψ )
    s2 = lb.ref("s2", "ψ ↔ ( ( φ ∨ ¬ φ ) ∧ ψ )", s1, ref="biantrur", note="biantrur")

    # andir: ( ( φ ∨ ¬ φ ) ∧ ψ ) ↔ ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ ψ ) )
    s3 = lb.ref(
        "s3",
        "( ( φ ∨ ¬ φ ) ∧ ψ ) ↔ ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ ψ ) )",
        ref="andir",
        note="andir",
    )

    # pm5.32i with h1: ( φ ∧ ψ ) ↔ ( φ ∧ χ )
    s4 = lb.ref("s4", "( φ ∧ ψ ) ↔ ( φ ∧ χ )", h1, ref="pm5.32i", note="pm5.32i")

    # pm5.32i with h2: ( ¬ φ ∧ ψ ) ↔ ( ¬ φ ∧ θ )
    s5 = lb.ref("s5", "( ¬ φ ∧ ψ ) ↔ ( ¬ φ ∧ θ )", h2, ref="pm5.32i", note="pm5.32i")

    # orbi12i: ( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ ψ ) ) ↔ ( ( φ ∧ χ ) ∨ ( ¬ φ ∧ θ ) )
    s6 = lb.ref(
        "s6",
        "( ( φ ∧ ψ ) ∨ ( ¬ φ ∧ ψ ) ) ↔ ( ( φ ∧ χ ) ∨ ( ¬ φ ∧ θ ) )",
        s4,
        s5,
        ref="orbi12i",
        note="orbi12i",
    )

    # 3bitri: ψ ↔ ( ( φ ∧ χ ) ∨ ( ¬ φ ∧ θ ) )
    res = lb.ref(
        "res",
        "ψ ↔ ( ( φ ∧ χ ) ∨ ( ¬ φ ∧ θ ) )",
        s2,
        s3,
        s6,
        ref="3bitri",
        note="3bitri",
    )
    return lb.build(res)


def prove_3jaao(sys: System) -> Proof:
    """3jaao: ( φ ∧ θ ∧ η ) → ( ( ψ ∨ τ ∨ ζ ) → χ ).

    Inference joining three implications under a triple conjunction.
    """
    lb = ProofBuilder(sys, "3jaao")
    h1 = lb.hyp("3jaao.1", "φ → ( ψ → χ )")
    h2 = lb.hyp("3jaao.2", "θ → ( τ → χ )")
    h3 = lb.hyp("3jaao.3", "η → ( ζ → χ )")

    # 3jao: ((ψ → χ) ∧ (τ → χ) ∧ (ζ → χ)) → ((ψ ∨ τ ∨ ζ) → χ)
    s1 = lb.ref(
        "s1",
        "( ( ψ → χ ) ∧ ( τ → χ ) ∧ ( ζ → χ ) ) → ( ( ψ ∨ τ ∨ ζ ) → χ )",
        ref="3jao",
        note="3jao",
    )

    # syl3an: (φ ∧ θ ∧ η) → ((ψ ∨ τ ∨ ζ) → χ)
    res = lb.ref(
        "res",
        "( φ ∧ θ ∧ η ) → ( ( ψ ∨ τ ∨ ζ ) → χ )",
        h1,
        h2,
        h3,
        s1,
        ref="syl3an",
        note="syl3an",
    )

    return lb.build(res)


def prove_3jaaoOLD(sys: System) -> Proof:
    """3jaaoOLD: ( φ ∧ θ ∧ η ) → ( ( ψ ∨ τ ∨ ζ ) → χ ).

    Inference joining three implications under a triple conjunction.
    set.mm proof: 3ad2ant1 3ad2ant2 3ad2ant3 3jaod.
    """
    lb = ProofBuilder(sys, "3jaaoOLD")
    h1 = lb.hyp("3jaao.1", "φ → ( ψ → χ )")
    h2 = lb.hyp("3jaao.2", "θ → ( τ → χ )")
    h3 = lb.hyp("3jaao.3", "η → ( ζ → χ )")

    # 3ad2ant1: ( φ ∧ θ ∧ η ) → ( ψ → χ )
    s1 = lb.ref(
        "s1",
        "( φ ∧ θ ∧ η ) → ( ψ → χ )",
        h1,
        ref="3ad2ant1",
        note="3ad2ant1(3jaao.1)",
    )

    # 3ad2ant2: ( φ ∧ θ ∧ η ) → ( τ → χ )
    s2 = lb.ref(
        "s2",
        "( φ ∧ θ ∧ η ) → ( τ → χ )",
        h2,
        ref="3ad2ant2",
        note="3ad2ant2(3jaao.2)",
    )

    # 3ad2ant3: ( φ ∧ θ ∧ η ) → ( ζ → χ )
    s3 = lb.ref(
        "s3",
        "( φ ∧ θ ∧ η ) → ( ζ → χ )",
        h3,
        ref="3ad2ant3",
        note="3ad2ant3(3jaao.3)",
    )

    # 3jaod: combine the three implications
    res = lb.ref(
        "res",
        "( φ ∧ θ ∧ η ) → ( ( ψ ∨ τ ∨ ζ ) → χ )",
        s1,
        s2,
        s3,
        ref="3jaod",
        note="3jaod(s1, s2, s3)",
    )

    return lb.build(res)


def prove_excxor(sys: System) -> Proof:
    """excxor: ( φ ⊻ ψ ) ↔ ( ( φ ∧ ¬ ψ ) ∨ ( ¬ φ ∧ ψ ) ).

    Exclusive-or expressed directly as exclusive disjunction of the two
    cases where the two operands have opposite truth values.
    """
    lb = ProofBuilder(sys, "excxor")

    s1 = lb.ref(
        "s1",
        "( φ ⊻ ψ ) ↔ ¬ ( φ ↔ ψ )",
        ref="df-xor",
        note="df-xor",
    )

    s2 = lb.ref(
        "s2",
        "¬ ( φ ↔ ψ ) ↔ ( ( φ ∧ ¬ ψ ) ∨ ( ψ ∧ ¬ φ ) )",
        ref="xor",
        note="xor",
    )

    s3 = lb.ref(
        "s3",
        "( ψ ∧ ¬ φ ) ↔ ( ¬ φ ∧ ψ )",
        ref="ancom",
        note="ancom",
    )

    s4 = lb.ref(
        "s4",
        "( ( φ ∧ ¬ ψ ) ∨ ( ψ ∧ ¬ φ ) ) ↔ ( ( φ ∧ ¬ ψ ) ∨ ( ¬ φ ∧ ψ ) )",
        s3,
        ref="orbi2i",
        note="orbi2i",
    )

    res = lb.ref(
        "res",
        "( φ ⊻ ψ ) ↔ ( ( φ ∧ ¬ ψ ) ∨ ( ¬ φ ∧ ψ ) )",
        s1,
        s2,
        s4,
        ref="3bitri",
        note="3bitri",
    )

    return lb.build(res)


def prove_xoror(sys: System) -> Proof:
    """xoror: ( φ ⊻ ψ ) → ( φ ∨ ψ ).

    Exclusive or implies inclusive or.
    """
    lb = ProofBuilder(sys, "xoror")

    s1 = lb.ref(
        "s1",
        "( φ ⊻ ψ ) ↔ ( ( φ ∨ ψ ) ∧ ¬ ( φ ∧ ψ ) )",
        ref="xor2",
        note="xor2",
    )

    res = lb.ref(
        "res",
        "( φ ⊻ ψ ) → ( φ ∨ ψ )",
        s1,
        ref="simplbi",
        note="simplbi xor2",
    )

    return lb.build(res)


# New migrations register here beside their implementation.
# The aggregate registry imports this mapping, avoiding another edit to global shim files.
def prove_cadan(sys: System) -> Proof:
    """cadan: cadd(φ, ψ, χ) ↔ ((φ ∨ ψ) ∧ (φ ∨ χ) ∧ (ψ ∨ χ)).

    The adder carry expressed as a ternary conjunction of binary
    disjunctions (CNF).
    """
    lb = ProofBuilder(sys, "cadan")

    # cador: cadd φ ψ χ ↔ ((φ ∧ ψ) ∨ (φ ∧ χ) ∨ (ψ ∧ χ))
    s_cador = lb.ref(
        "s_cador",
        "cadd φ ψ χ ↔ ( ( φ ∧ ψ ) ∨ ( φ ∧ χ ) ∨ ( ψ ∧ χ ) )",
        ref="cador",
        note="cador",
    )

    # df-3or: expand ternary OR to binary
    s_df3or = lb.ref(
        "s_df3or",
        "( ( φ ∧ ψ ) ∨ ( φ ∧ χ ) ∨ ( ψ ∧ χ ) ) ↔ ( ( ( φ ∧ ψ ) ∨ ( φ ∧ χ ) ) ∨ ( ψ ∧ χ ) )",
        ref="df-3or",
        note="df-3or",
    )

    #  -- core: DNF_binary ↔ CNF_binary --

    # andi: ( φ ∧ ( ψ ∨ χ ) ) ↔ ( ( φ ∧ ψ ) ∨ ( φ ∧ χ ) )
    s_andi = lb.ref(
        "s_andi",
        "( φ ∧ ( ψ ∨ χ ) ) ↔ ( ( φ ∧ ψ ) ∨ ( φ ∧ χ ) )",
        ref="andi",
        note="andi",
    )

    # orbi1i on andi with C = ( ψ ∧ χ ):
    #   ( ( φ ∧ ( ψ ∨ χ ) ) ∨ ( ψ ∧ χ ) ) ↔ ( ( ( φ ∧ ψ ) ∨ ( φ ∧ χ ) ) ∨ ( ψ ∧ χ ) )
    s_x_to_dnf = lb.ref(
        "s_x_to_dnf",
        "( ( φ ∧ ( ψ ∨ χ ) ) ∨ ( ψ ∧ χ ) ) ↔ ( ( ( φ ∧ ψ ) ∨ ( φ ∧ χ ) ) ∨ ( ψ ∧ χ ) )",
        s_andi,
        ref="orbi1i",
        note="orbi1i(andi)",
    )

    # ordir: ( ( φ ∧ ( ψ ∨ χ ) ) ∨ ( ψ ∧ χ ) ) ↔
    #          ( ( φ ∨ ( ψ ∧ χ ) ) ∧ ( ( ψ ∨ χ ) ∨ ( ψ ∧ χ ) ) )
    s_ordir = lb.ref(
        "s_ordir",
        "( ( φ ∧ ( ψ ∨ χ ) ) ∨ ( ψ ∧ χ ) ) ↔ ( ( φ ∨ ( ψ ∧ χ ) ) ∧ ( ( ψ ∨ χ ) ∨ ( ψ ∧ χ ) ) )",
        ref="ordir",
        note="ordir",
    )

    # animorl: ( ψ ∧ χ ) → ( ψ ∨ χ )
    s_animorl = lb.ref(
        "s_animorl",
        "( ψ ∧ χ ) → ( ψ ∨ χ )",
        ref="animorl",
        note="animorl",
    )

    # pm4.72: ( ( ψ ∧ χ ) → ( ψ ∨ χ ) ) ↔
    #          ( ( ψ ∨ χ ) ↔ ( ( ψ ∧ χ ) ∨ ( ψ ∨ χ ) ) )
    s_pm472 = lb.ref(
        "s_pm472",
        "( ( ψ ∧ χ ) → ( ψ ∨ χ ) ) ↔ ( ( ψ ∨ χ ) ↔ ( ( ψ ∧ χ ) ∨ ( ψ ∨ χ ) ) )",
        ref="pm4.72",
        note="pm4.72",
    )

    # mpbi: ( ψ ∨ χ ) ↔ ( ( ψ ∧ χ ) ∨ ( ψ ∨ χ ) )
    s_mpbi = lb.ref(
        "s_mpbi",
        "( ψ ∨ χ ) ↔ ( ( ψ ∧ χ ) ∨ ( ψ ∨ χ ) )",
        s_animorl,
        s_pm472,
        ref="mpbi",
        note="mpbi(animorl, pm4.72)",
    )

    # orcom: ( ( ψ ∧ χ ) ∨ ( ψ ∨ χ ) ) ↔ ( ( ψ ∨ χ ) ∨ ( ψ ∧ χ ) )
    s_orcom = lb.ref(
        "s_orcom",
        "( ( ψ ∧ χ ) ∨ ( ψ ∨ χ ) ) ↔ ( ( ψ ∨ χ ) ∨ ( ψ ∧ χ ) )",
        ref="orcom",
        note="orcom",
    )

    # bicomi on s_orcom: ( ( ψ ∨ χ ) ∨ ( ψ ∧ χ ) ) ↔ ( ( ψ ∧ χ ) ∨ ( ψ ∨ χ ) )
    s_orcom_rev = lb.ref(
        "s_orcom_rev",
        "( ( ψ ∨ χ ) ∨ ( ψ ∧ χ ) ) ↔ ( ( ψ ∧ χ ) ∨ ( ψ ∨ χ ) )",
        s_orcom,
        ref="bicomi",
        note="bicomi(orcom)",
    )

    # bitr4i: ( ψ ∨ χ ) ↔ ( ( ψ ∨ χ ) ∨ ( ψ ∧ χ ) )
    s_abs = lb.ref(
        "s_abs",
        "( ψ ∨ χ ) ↔ ( ( ψ ∨ χ ) ∨ ( ψ ∧ χ ) )",
        s_mpbi,
        s_orcom_rev,
        ref="bitr4i",
        note="bitr4i(mpbi, bicomi(orcom))",
    )

    # biid: ( φ ∨ ( ψ ∧ χ ) ) ↔ ( φ ∨ ( ψ ∧ χ ) )
    s_biid = lb.ref(
        "s_biid",
        "( φ ∨ ( ψ ∧ χ ) ) ↔ ( φ ∨ ( ψ ∧ χ ) )",
        ref="biid",
        note="biid",
    )

    # anbi12i: ( ( φ ∨ ( ψ ∧ χ ) ) ∧ ( ψ ∨ χ ) ) ↔
    #            ( ( φ ∨ ( ψ ∧ χ ) ) ∧ ( ( ψ ∨ χ ) ∨ ( ψ ∧ χ ) ) )
    s_anbi12i = lb.ref(
        "s_anbi12i",
        "( ( φ ∨ ( ψ ∧ χ ) ) ∧ ( ψ ∨ χ ) ) ↔ ( ( φ ∨ ( ψ ∧ χ ) ) ∧ ( ( ψ ∨ χ ) ∨ ( ψ ∧ χ ) ) )",
        s_biid,
        s_abs,
        ref="anbi12i",
        note="anbi12i(biid, mpbi+orcom)",
    )

    # ordi: ( φ ∨ ( ψ ∧ χ ) ) ↔ ( ( φ ∨ ψ ) ∧ ( φ ∨ χ ) )
    s_ordi = lb.ref(
        "s_ordi",
        "( φ ∨ ( ψ ∧ χ ) ) ↔ ( ( φ ∨ ψ ) ∧ ( φ ∨ χ ) )",
        ref="ordi",
        note="ordi",
    )

    # biid: ( ψ ∨ χ ) ↔ ( ψ ∨ χ )
    s_biid2 = lb.ref(
        "s_biid2",
        "( ψ ∨ χ ) ↔ ( ψ ∨ χ )",
        ref="biid",
        note="biid",
    )

    # anbi12i: ( ( φ ∨ ( ψ ∧ χ ) ) ∧ ( ψ ∨ χ ) ) ↔
    #            ( ( ( φ ∨ ψ ) ∧ ( φ ∨ χ ) ) ∧ ( ψ ∨ χ ) )
    s_cnf = lb.ref(
        "s_cnf",
        "( ( φ ∨ ( ψ ∧ χ ) ) ∧ ( ψ ∨ χ ) ) ↔ ( ( ( φ ∨ ψ ) ∧ ( φ ∨ χ ) ) ∧ ( ψ ∨ χ ) )",
        s_ordi,
        s_biid2,
        ref="anbi12i",
        note="anbi12i(ordi, biid)",
    )

    # Now assemble the core chain DNF_binary ↔ CNF_binary
    # We have:
    #   s_x_to_dnf:  X ↔ DNF_binary
    #   s_ordir:     X ↔ Y
    #   s_anbi12i:   Z ↔ Y
    #   s_cnf:       Z ↔ CNF_binary
    # where:
    #   X = ((φ ∧ (ψ ∨ χ)) ∨ (ψ ∧ χ))
    #   Y = ((φ ∨ (ψ ∧ χ)) ∧ ((ψ ∨ χ) ∨ (ψ ∧ χ)))
    #   Z = ((φ ∨ (ψ ∧ χ)) ∧ (ψ ∨ χ))
    #   DNF_binary = (((φ ∧ ψ) ∨ (φ ∧ χ)) ∨ (ψ ∧ χ))
    #   CNF_binary = (((φ ∨ ψ) ∧ (φ ∨ χ)) ∧ (ψ ∨ χ))

    # bicomi on s_x_to_dnf: DNF_binary ↔ X
    s_dnf_to_x = lb.ref(
        "s_dnf_to_x",
        "( ( ( φ ∧ ψ ) ∨ ( φ ∧ χ ) ) ∨ ( ψ ∧ χ ) ) ↔ ( ( φ ∧ ( ψ ∨ χ ) ) ∨ ( ψ ∧ χ ) )",
        s_x_to_dnf,
        ref="bicomi",
        note="bicomi(orbi1i(andi))",
    )

    # bicomi on s_ordir: Y ↔ X
    s_y_to_x = lb.ref(
        "s_y_to_x",
        "( ( φ ∨ ( ψ ∧ χ ) ) ∧ ( ( ψ ∨ χ ) ∨ ( ψ ∧ χ ) ) ) ↔ ( ( φ ∧ ( ψ ∨ χ ) ) ∨ ( ψ ∧ χ ) )",
        s_ordir,
        ref="bicomi",
        note="bicomi(ordir)",
    )

    # bitr4i(dnf_to_x, y_to_x): DNF_binary ↔ Y
    s_dnf_to_y = lb.ref(
        "s_dnf_to_y",
        "( ( ( φ ∧ ψ ) ∨ ( φ ∧ χ ) ) ∨ ( ψ ∧ χ ) ) ↔ ( ( φ ∨ ( ψ ∧ χ ) ) ∧ ( ( ψ ∨ χ ) ∨ ( ψ ∧ χ ) ) )",
        s_dnf_to_x,
        s_y_to_x,
        ref="bitr4i",
        note="bitr4i",
    )

    # bicomi on s_anbi12i: Y ↔ Z
    s_y_to_z = lb.ref(
        "s_y_to_z",
        "( ( φ ∨ ( ψ ∧ χ ) ) ∧ ( ( ψ ∨ χ ) ∨ ( ψ ∧ χ ) ) ) ↔ ( ( φ ∨ ( ψ ∧ χ ) ) ∧ ( ψ ∨ χ ) )",
        s_anbi12i,
        ref="bicomi",
        note="bicomi(anbi12i)",
    )

    # bicomi on s_y_to_z: Z ↔ Y
    s_z_to_y = lb.ref(
        "s_z_to_y",
        "( ( φ ∨ ( ψ ∧ χ ) ) ∧ ( ψ ∨ χ ) ) ↔ ( ( φ ∨ ( ψ ∧ χ ) ) ∧ ( ( ψ ∨ χ ) ∨ ( ψ ∧ χ ) ) )",
        s_y_to_z,
        ref="bicomi",
        note="bicomi(y_to_z)",
    )

    # bitr4i(dnf_to_y, z_to_y): DNF_binary ↔ Z
    s_dnf_to_z = lb.ref(
        "s_dnf_to_z",
        "( ( ( φ ∧ ψ ) ∨ ( φ ∧ χ ) ) ∨ ( ψ ∧ χ ) ) ↔ ( ( φ ∨ ( ψ ∧ χ ) ) ∧ ( ψ ∨ χ ) )",
        s_dnf_to_y,
        s_z_to_y,
        ref="bitr4i",
        note="bitr4i",
    )

    # bicomi on s_cnf: CNF_binary ↔ Z
    s_cnf_to_z = lb.ref(
        "s_cnf_to_z",
        "( ( ( φ ∨ ψ ) ∧ ( φ ∨ χ ) ) ∧ ( ψ ∨ χ ) ) ↔ ( ( φ ∨ ( ψ ∧ χ ) ) ∧ ( ψ ∨ χ ) )",
        s_cnf,
        ref="bicomi",
        note="bicomi(anbi12i(ordi, biid))",
    )

    # bitr4i(dnf_to_z, cnf_to_z): DNF_binary ↔ CNF_binary
    s_core = lb.ref(
        "s_core",
        "( ( ( φ ∧ ψ ) ∨ ( φ ∧ χ ) ) ∨ ( ψ ∧ χ ) ) ↔ ( ( ( φ ∨ ψ ) ∧ ( φ ∨ χ ) ) ∧ ( ψ ∨ χ ) )",
        s_dnf_to_z,
        s_cnf_to_z,
        ref="bitr4i",
        note="bitr4i",
    )

    # -- end core --

    # bicomi on s_df3or: DNF_binary ↔ DNF_ternary
    s_df3or_rev = lb.ref(
        "s_df3or_rev",
        "( ( ( φ ∧ ψ ) ∨ ( φ ∧ χ ) ) ∨ ( ψ ∧ χ ) ) ↔ ( ( φ ∧ ψ ) ∨ ( φ ∧ χ ) ∨ ( ψ ∧ χ ) )",
        s_df3or,
        ref="bicomi",
        note="bicomi(df-3or)",
    )

    # bitr4i(cador, df3or_rev): cadd ↔ DNF_binary
    s_cadd_dnf = lb.ref(
        "s_cadd_dnf",
        "cadd φ ψ χ ↔ ( ( ( φ ∧ ψ ) ∨ ( φ ∧ χ ) ) ∨ ( ψ ∧ χ ) )",
        s_cador,
        s_df3or_rev,
        ref="bitr4i",
        note="bitr4i(cador, bicomi(df-3or))",
    )

    # df-3an: ( ( φ ∨ ψ ) ∧ ( φ ∨ χ ) ∧ ( ψ ∨ χ ) ) ↔
    #          ( ( ( φ ∨ ψ ) ∧ ( φ ∨ χ ) ) ∧ ( ψ ∨ χ ) )
    s_df3an = lb.ref(
        "s_df3an",
        "( ( φ ∨ ψ ) ∧ ( φ ∨ χ ) ∧ ( ψ ∨ χ ) ) ↔ ( ( ( φ ∨ ψ ) ∧ ( φ ∨ χ ) ) ∧ ( ψ ∨ χ ) )",
        ref="df-3an",
        note="df-3an",
    )

    # 3bitr4i: cadd φ ψ χ ↔ ( ( φ ∨ ψ ) ∧ ( φ ∨ χ ) ∧ ( ψ ∨ χ ) )
    res = lb.ref(
        "res",
        "cadd φ ψ χ ↔ ( ( φ ∨ ψ ) ∧ ( φ ∨ χ ) ∧ ( ψ ∨ χ ) )",
        s_core,
        s_cadd_dnf,
        s_df3an,
        ref="3bitr4i",
        note="3bitr4i",
    )

    return lb.build(res)


def prove_anifp(sys: System) -> Proof:
    """anifp: ( ψ ∧ χ ) → if- φ ψ χ.

    Conjunction implies the conditional.
    (Contributed by NM, 3-Jan-2005.)
    """
    lb = ProofBuilder(sys, "anifp")

    # olc: ψ → ( ¬ φ ∨ ψ )
    s1 = lb.ref("s1", "ψ → ( ¬ φ ∨ ψ )", ref="olc", note="olc")

    # olc: χ → ( φ ∨ χ )
    s2 = lb.ref("s2", "χ → ( φ ∨ χ )", ref="olc", note="olc")

    # anim12i: ( ψ ∧ χ ) → ( ( ¬ φ ∨ ψ ) ∧ ( φ ∨ χ ) )
    s3 = lb.ref(
        "s3",
        "( ψ ∧ χ ) → ( ( ¬ φ ∨ ψ ) ∧ ( φ ∨ χ ) )",
        s1,
        s2,
        ref="anim12i",
        note="anim12i",
    )

    # dfifp4: if- φ ψ χ ↔ ( ( ¬ φ ∨ ψ ) ∧ ( φ ∨ χ ) )
    s4 = lb.ref(
        "s4",
        "if- φ ψ χ ↔ ( ( ¬ φ ∨ ψ ) ∧ ( φ ∨ χ ) )",
        ref="dfifp4",
        note="dfifp4",
    )

    # sylibr: ( ψ ∧ χ ) → if- φ ψ χ
    res = lb.ref(
        "res",
        "( ψ ∧ χ ) → if- φ ψ χ",
        s3,
        s4,
        ref="sylibr",
        note="sylibr",
    )

    return lb.build(res)


MIGRATION_THEOREMS: Mapping[str, LemmaCtor] = {
    "pm5.15": prove_pm5_15,
    "anifp": prove_anifp,
    "ifpor": prove_ifpor,
    "ornld": prove_ornld,
    "pm4.39": prove_pm4_39,
    "pm5.24": prove_pm5_24,
    "4exmid": prove_4exmid,
    "xor": prove_xor,
    "excxor": prove_excxor,
    "nbi2": prove_nbi2,
    "xor2": prove_xor2,
    "xornan": prove_xornan,
    "xornan2": prove_xornan2,
    "andi": prove_andi,
    "andir": prove_andir,
    "cases": prove_cases,
    "anddi": prove_anddi,
    "3jaao": prove_3jaao,
    "xoror": prove_xoror,
    "3jaaoOLD": prove_3jaaoOLD,
    "cadan": prove_cadan,
}
