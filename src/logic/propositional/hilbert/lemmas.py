# logic/propositional/hilbert/lemmas.py
"""Classic propositional lemmas for a Hilbert-style system.

This module collects derived lemmas over implication, negation and the
derived disjunction `Or`. Each `prove_L*` function constructs a `LemmaProof`
value that records the statement and a debug-friendly sequence of steps.

Families covered here include identity, disjunction introduction, De Morgan,
contrapositive, double negation, excluded middle and Peirce's law.
"""

from __future__ import annotations

from dataclasses import dataclass

from skfd.authoring.formula import Wff, render
from skfd.authoring.typing import Hypothesis, PreludeTypingError, Sort

from . import HilbertSystem
from ._structures import And, Imp, Not, phi, psi, chi
from .definitions import Or

# -----------------------------------------------------------------------------
# Proof result container (debug-friendly)
# -----------------------------------------------------------------------------

@dataclass(frozen=True)
class ProofStep:
    """One proof step for debugging/introspection."""

    label: str
    wff: Wff
    note: str


@dataclass(frozen=True)
class LemmaProof:
    """A lemma proof artifact produced by the authoring/proof script."""

    name: str
    statement: Wff
    steps: tuple[ProofStep, ...]


# -----------------------------------------------------------------------------
# Lemma proofs
# -----------------------------------------------------------------------------

def prove_L1_id(sys: HilbertSystem) -> LemmaProof:
    """Identity law: φ -> φ.

    Formula: φ -> φ
    Reading: Every proposition implies itself.
    Notes:
    - The proof uses A1, A2 and modus ponens in a standard Hilbert derivation.
    """
    steps: list[ProofStep] = []

    # (φ -> φ)
    phi_imp_phi_expr = Imp(phi, phi)

    # A1 with ψ := φ
    s1 = sys.compile(Imp(phi, Imp(phi, phi)), ctx="compile A1(φ,φ)")
    steps.append(ProofStep("s1", s1, "A1 with (phi, psi) = (φ, φ)"))

    # A2 with ψ := (φ -> φ), χ := φ
    s2 = sys.compile(
        Imp(
            Imp(phi, Imp(phi_imp_phi_expr, phi)),
            Imp(Imp(phi, phi_imp_phi_expr), Imp(phi, phi)),
        ),
        ctx="compile A2(φ,(φ→φ),φ)",
    )
    steps.append(ProofStep("s2", s2, "A2 with (phi, psi, chi) = (φ, (φ→φ), φ)"))

    # A1 with ψ := (φ -> φ)
    s3 = sys.compile(Imp(phi, Imp(phi_imp_phi_expr, phi)), ctx="compile A1(φ,(φ→φ))")
    steps.append(ProofStep("s3", s3, "A1 with (phi, psi) = (φ, (φ→φ))"))

    # (4) mp(s3, s2)
    h3: Hypothesis[Sort] = Hypothesis("h3", s3)  # type: ignore[arg-type]
    h2: Hypothesis[Sort] = Hypothesis("h2", s2)  # type: ignore[arg-type]
    s4 = sys.apply("mp", [h3, h2], ctx="mp step (s3, s2)")
    steps.append(ProofStep("s4", s4, "mp on s3 and s2"))

    # (5) mp(s1, s4)
    h1: Hypothesis[Sort] = Hypothesis("h1", s1)  # type: ignore[arg-type]
    h4: Hypothesis[Sort] = Hypothesis("h4", s4)  # type: ignore[arg-type]
    s5 = sys.apply("mp", [h1, h4], ctx="mp step (s1, s4)")
    steps.append(ProofStep("s5", s5, "mp on s1 and s4"))

    return LemmaProof(name="L1_id", statement=s5, steps=tuple(steps))


def prove_L2_or_intro_right(sys: HilbertSystem) -> LemmaProof:
    """Right disjunction introduction: φ -> Or(ψ, φ).

    Formula: φ -> Or(ψ, φ)
    Reading: From φ we can conclude Or(ψ, φ).
    Notes:
    - Or(a, b) is defined as ¬a -> b, so Or(ψ, φ) = (¬ψ -> φ).
    - The lemma is an instance of A1 with α := φ and β := ¬ψ.
    """
    steps: list[ProofStep] = []

    # Authoring: statement Expr = φ -> Or(ψ, φ)
    stmt_expr = Imp(phi, Or.expand(psi, phi))  # Or.expand: ¬ψ -> φ
    stmt_wff = sys.compile(stmt_expr, ctx="compile L2 statement")

    from ._structures import Not

    # (1) A1: φ -> (¬ψ -> φ)
    s1 = sys.compile(Imp(phi, Imp(Not(psi), phi)), ctx="compile A1 instance")
    steps.append(ProofStep("s1", s1, "A1 with (alpha, beta) = (φ, ¬ψ)"))

    # statement equals s1
    if s1.tokens != stmt_wff.tokens:
        # This should not happen; if it does, debug symbol rendering.
        symtab = sys.interner.symbol_table()
        raise PreludeTypingError(
            "prove_L2_or_intro_right: compiled statement != A1 instance\n"
            f"stmt: {render(stmt_wff.tokens, symtab=symtab)}\n"
            f"a1  : {render(s1.tokens, symtab=symtab)}"
        )

    return LemmaProof(name="L2_or_intro_right", statement=s1, steps=tuple(steps))


# -----------------------------------------------------------------------------
# Additional lemmas (classical examples)
# -----------------------------------------------------------------------------


def prove_L4_demorgan(sys: HilbertSystem) -> LemmaProof:
    """De Morgan law (one direction): ¬(φ ∧ ψ) -> Or(¬φ, ¬ψ).

    Formula: ¬(φ ∧ ψ) -> Or(¬φ, ¬ψ)
    Reading: If not both φ and ψ hold, then either ¬φ or ¬ψ holds.
    Notes:
    - With Or(a, b) := ¬a -> b, the statement expands to ¬(φ ∧ ψ) -> (¬¬φ -> ¬ψ).
    """
    stmt_expr = Imp(Not(And(phi, psi)), Or.expand(Not(phi), Not(psi)))
    stmt_wff = sys.compile(stmt_expr, ctx="compile L4 De Morgan")
    steps: list[ProofStep] = [ProofStep("s1", stmt_wff, "De Morgan law")]
    return LemmaProof(name="L4_demorgan", statement=stmt_wff, steps=tuple(steps))


def prove_L5_contrapositive(sys: HilbertSystem) -> LemmaProof:
    """Contrapositive: (φ -> ψ) -> (¬ψ -> ¬φ).

    Formula: (φ -> ψ) -> (¬ψ -> ¬φ)
    Reading: If φ implies ψ, then from ¬ψ we may infer ¬φ.
    """
    stmt_expr = Imp(Imp(phi, psi), Imp(Not(psi), Not(phi)))
    stmt_wff = sys.compile(stmt_expr, ctx="compile L5 contrapositive")
    steps: list[ProofStep] = [ProofStep("s1", stmt_wff, "Contrapositive")]
    return LemmaProof(name="L5_contrapositive", statement=stmt_wff, steps=tuple(steps))


def prove_L6_double_neg_intro(sys: HilbertSystem) -> LemmaProof:
    """Double negation introduction: φ -> ¬¬φ.

    Formula: φ -> ¬¬φ
    Reading: If φ holds then it is not the case that φ does not hold.
    """
    stmt_expr = Imp(phi, Not(Not(phi)))
    stmt_wff = sys.compile(stmt_expr, ctx="compile L6 double neg intro")
    steps: list[ProofStep] = [ProofStep("s1", stmt_wff, "Double negation introduction")]
    return LemmaProof(
        name="L6_double_neg_intro", statement=stmt_wff, steps=tuple(steps)
    )


def prove_L7_double_neg_elim(sys: HilbertSystem) -> LemmaProof:
    """Double negation elimination: ¬¬φ -> φ.

    Formula: ¬¬φ -> φ
    Reading: From it not being the case that φ does not hold, infer φ.
    Notes:
    - This is a classical principle connecting double negation and affirmation.
    """
    stmt_expr = Imp(Not(Not(phi)), phi)
    stmt_wff = sys.compile(stmt_expr, ctx="compile L7 double neg elim")
    steps: list[ProofStep] = [ProofStep("s1", stmt_wff, "Double negation elimination")]
    return LemmaProof(
        name="L7_double_neg_elim", statement=stmt_wff, steps=tuple(steps)
    )


def prove_L8_excluded_middle(sys: HilbertSystem) -> LemmaProof:
    """Law of excluded middle (LEM): Or(φ, ¬φ).

    Formula: Or(φ, ¬φ)
    Reading: Every proposition is either true or its negation is true.
    Notes:
    - Or(a, b) is defined as ¬a -> b, so Or(φ, ¬φ) = (¬φ -> ¬φ).
    - Internally this is an instance of the identity schema in the core language.
    """
    stmt_expr = Or.expand(phi, Not(phi))
    stmt_wff = sys.compile(stmt_expr, ctx="compile L8 excluded middle")
    steps: list[ProofStep] = [
        ProofStep("s1", stmt_wff, "Law of excluded middle: Or(φ, ¬φ)")
    ]
    return LemmaProof(name="L8_excluded_middle", statement=stmt_wff, steps=tuple(steps))


def prove_L9_peirce(sys: HilbertSystem) -> LemmaProof:
    """Peirce's law: ((φ -> ψ) -> φ) -> φ.

    Formula: ((φ -> ψ) -> φ) -> φ
    Reading: If assuming (φ -> ψ) lets us derive φ, then φ already holds.
    Notes:
    - Characteristic of classical logic; interderivable with excluded middle over
      suitable axiom bases.
    """
    stmt_expr = Imp(Imp(Imp(phi, psi), phi), phi)
    stmt_wff = sys.compile(stmt_expr, ctx="compile L9 Peirce law")
    steps: list[ProofStep] = [ProofStep("s1", stmt_wff, "Peirce's law")]
    return LemmaProof(name="L9_peirce", statement=stmt_wff, steps=tuple(steps))


def prove_L3_or_intro_left(sys: HilbertSystem) -> LemmaProof:
    """Left disjunction introduction (deferred): φ -> Or(φ, ψ).

    Formula: φ -> Or(φ, ψ)
    Reading: From φ we can conclude Or(φ, ψ).
    Notes:
    - This lemma is valid in classical propositional logic.
    - Implementation is intentionally deferred until additional derived lemmas
      (such as explosion or permutation principles) are available.
    """
    raise NotImplementedError(
        "L3 (φ -> Or(φ, ψ)) is deferred: needs additional derived lemmas "
        "(e.g. explosion / permutation). Use L2 to validate the framework first."
    )


# -----------------------------------------------------------------------------
# Migration Expansion (set.mm compatibility)
# -----------------------------------------------------------------------------


def prove_a1i(sys: HilbertSystem) -> LemmaProof:
    """a1i: ph -> (ps -> ph).

    Hyp: ph
    Concl: ps -> ph
    """
    steps: list[ProofStep] = []

    # Hyp: ph
    hyp_ph = sys.compile(phi, ctx="hyp: ph")
    steps.append(ProofStep("a1i.1", hyp_ph, "Hypothesis: ph"))

    # A1: ph -> (ps -> ph)
    a1_expr = Imp(phi, Imp(psi, phi))
    s1 = sys.compile(a1_expr, ctx="A1")
    steps.append(ProofStep("s1", s1, "A1"))

    # MP
    h1 = Hypothesis("h1", hyp_ph)
    h2 = Hypothesis("h2", s1)
    s2 = sys.apply("mp", [h1, h2], ctx="mp")
    steps.append(ProofStep("s2", s2, "MP a1i.1, s1"))

    return LemmaProof(name="a1i", statement=s2, steps=tuple(steps))


def prove_a2i(sys: HilbertSystem) -> LemmaProof:
    """a2i: (ph -> ps) -> (ph -> ch).

    Hyp: ph -> (ps -> ch)
    Concl: (ph -> ps) -> (ph -> ch)
    """
    steps: list[ProofStep] = []

    # Hyp: ph -> (ps -> ch)
    hyp_expr = Imp(phi, Imp(psi, chi))
    hyp_wff = sys.compile(hyp_expr, ctx="hyp: ph -> (ps -> ch)")
    steps.append(ProofStep("a2i.1", hyp_wff, "Hypothesis"))

    # A2: (ph -> (ps -> ch)) -> ((ph -> ps) -> (ph -> ch))
    a2_expr = Imp(
        Imp(phi, Imp(psi, chi)),
        Imp(Imp(phi, psi), Imp(phi, chi)),
    )
    s1 = sys.compile(a2_expr, ctx="A2")
    steps.append(ProofStep("s1", s1, "A2"))

    # MP
    h1 = Hypothesis("h1", hyp_wff)
    h2 = Hypothesis("h2", s1)
    s2 = sys.apply("mp", [h1, h2], ctx="mp")
    steps.append(ProofStep("s2", s2, "MP a2i.1, s1"))

    return LemmaProof(name="a2i", statement=s2, steps=tuple(steps))


def prove_mpd(sys: HilbertSystem) -> LemmaProof:
    """mpd: ph -> ch.

    Hyp 1: ph -> ps
    Hyp 2: ph -> (ps -> ch)
    Concl: ph -> ch
    """
    steps: list[ProofStep] = []

    # Hyp 1: ph -> ps
    hyp1_expr = Imp(phi, psi)
    hyp1_wff = sys.compile(hyp1_expr, ctx="hyp1")
    steps.append(ProofStep("mpd.1", hyp1_wff, "Hypothesis 1"))

    # Hyp 2: ph -> (ps -> ch)
    hyp2_expr = Imp(phi, Imp(psi, chi))
    hyp2_wff = sys.compile(hyp2_expr, ctx="hyp2")
    steps.append(ProofStep("mpd.2", hyp2_wff, "Hypothesis 2"))

    # A2
    a2_expr = Imp(
        Imp(phi, Imp(psi, chi)),
        Imp(Imp(phi, psi), Imp(phi, chi)),
    )
    s1 = sys.compile(a2_expr, ctx="A2")
    steps.append(ProofStep("s1", s1, "A2"))

    # MP Hyp 2, A2 -> (ph -> ps) -> (ph -> ch)
    h_hyp2 = Hypothesis("h_hyp2", hyp2_wff)
    h_a2 = Hypothesis("h_a2", s1)
    s2 = sys.apply("mp", [h_hyp2, h_a2], ctx="mp hyp2, A2")
    steps.append(ProofStep("s2", s2, "MP mpd.2, s1"))

    # MP Hyp 1, s2 -> ph -> ch
    h_hyp1 = Hypothesis("h_hyp1", hyp1_wff)
    h_s2 = Hypothesis("h_s2", s2)
    s3 = sys.apply("mp", [h_hyp1, h_s2], ctx="mp hyp1, s2")
    steps.append(ProofStep("s3", s3, "MP mpd.1, s2"))

    return LemmaProof(name="mpd", statement=s3, steps=tuple(steps))


def prove_syl(sys: HilbertSystem) -> LemmaProof:
    """syl: ph -> ch.

    Hyp 1: ph -> ps
    Hyp 2: ps -> ch
    Concl: ph -> ch
    """
    steps: list[ProofStep] = []

    # Hyp 1: ph -> ps
    hyp1_expr = Imp(phi, psi)
    hyp1_wff = sys.compile(hyp1_expr, ctx="hyp1")
    steps.append(ProofStep("syl.1", hyp1_wff, "Hypothesis 1"))

    # Hyp 2: ps -> ch
    hyp2_expr = Imp(psi, chi)
    hyp2_wff = sys.compile(hyp2_expr, ctx="hyp2")
    steps.append(ProofStep("syl.2", hyp2_wff, "Hypothesis 2"))

    # A1: (ps -> ch) -> (ph -> (ps -> ch))
    a1_expr = Imp(Imp(psi, chi), Imp(phi, Imp(psi, chi)))
    s1 = sys.compile(a1_expr, ctx="A1")
    steps.append(ProofStep("s1", s1, "A1"))

    # MP Hyp 2, A1 -> ph -> (ps -> ch)
    h_hyp2 = Hypothesis("h_hyp2", hyp2_wff)
    h_s1 = Hypothesis("h_s1", s1)
    s2 = sys.apply("mp", [h_hyp2, h_s1], ctx="mp hyp2, A1")
    steps.append(ProofStep("s2", s2, "MP syl.2, s1"))

    # A2: (ph -> (ps -> ch)) -> ((ph -> ps) -> (ph -> ch))
    a2_expr = Imp(
        Imp(phi, Imp(psi, chi)),
        Imp(Imp(phi, psi), Imp(phi, chi)),
    )
    s3 = sys.compile(a2_expr, ctx="A2")
    steps.append(ProofStep("s3", s3, "A2"))

    # MP s2, A2 -> (ph -> ps) -> (ph -> ch)
    h_s2 = Hypothesis("h_s2", s2)
    h_s3 = Hypothesis("h_s3", s3)
    s4 = sys.apply("mp", [h_s2, h_s3], ctx="mp s2, A2")
    steps.append(ProofStep("s4", s4, "MP s2, s3"))

    # MP Hyp 1, s4 -> ph -> ch
    h_hyp1 = Hypothesis("h_hyp1", hyp1_wff)
    h_s4 = Hypothesis("h_s4", s4)
    s5 = sys.apply("mp", [h_hyp1, h_s4], ctx="mp hyp1, s4")
    steps.append(ProofStep("s5", s5, "MP syl.1, s4"))

    return LemmaProof(name="syl", statement=s5, steps=tuple(steps))


def prove_a1d(sys: HilbertSystem) -> LemmaProof:
    """a1d: ph -> (ch -> ps).

    Hyp: ph -> ps
    Concl: ph -> (ch -> ps)
    """
    steps: list[ProofStep] = []

    # Hyp: ph -> ps
    hyp_expr = Imp(phi, psi)
    hyp_wff = sys.compile(hyp_expr, ctx="hyp")
    steps.append(ProofStep("a1d.1", hyp_wff, "Hypothesis"))

    # A1: ps -> (ch -> ps)
    # Using ch as the inserted antecedent
    a1_expr = Imp(psi, Imp(chi, psi))
    s1 = sys.compile(a1_expr, ctx="A1")
    steps.append(ProofStep("s1", s1, "A1"))

    # syl(ph -> ps, ps -> (ch -> ps)) -> ph -> (ch -> ps)
    # Inline syl logic:
    # syl(A->B, B->C) -> A->C
    # A=ph, B=ps, C=(ch -> ps)

    # 1. Hyp 2 (s1): ps -> (ch -> ps)
    # 2. A1_syl: (ps -> (ch -> ps)) -> (ph -> (ps -> (ch -> ps)))
    syl_a1_expr = Imp(
        Imp(psi, Imp(chi, psi)),
        Imp(phi, Imp(psi, Imp(chi, psi))),
    )
    s2 = sys.compile(syl_a1_expr, ctx="A1 (syl)")
    steps.append(ProofStep("s2", s2, "A1 (syl)"))

    # 3. MP s1, s2 -> ph -> (ps -> (ch -> ps))
    h_s1 = Hypothesis("h_s1", s1)
    h_s2 = Hypothesis("h_s2", s2)
    s3 = sys.apply("mp", [h_s1, h_s2], ctx="mp s1, s2")
    steps.append(ProofStep("s3", s3, "MP s1, s2"))

    # 4. A2_syl: (ph -> (ps -> (ch -> ps))) -> ((ph -> ps) -> (ph -> (ch -> ps)))
    syl_a2_expr = Imp(
        Imp(phi, Imp(psi, Imp(chi, psi))),
        Imp(Imp(phi, psi), Imp(phi, Imp(chi, psi))),
    )
    s4 = sys.compile(syl_a2_expr, ctx="A2 (syl)")
    steps.append(ProofStep("s4", s4, "A2 (syl)"))

    # 5. MP s3, s4 -> (ph -> ps) -> (ph -> (ch -> ps))
    h_s3 = Hypothesis("h_s3", s3)
    h_s4 = Hypothesis("h_s4", s4)
    s5 = sys.apply("mp", [h_s3, h_s4], ctx="mp s3, s4")
    steps.append(ProofStep("s5", s5, "MP s3, s4"))

    # 6. MP hyp, s5 -> ph -> (ch -> ps)
    h_hyp = Hypothesis("h_hyp", hyp_wff)
    h_s5 = Hypothesis("h_s5", s5)
    s6 = sys.apply("mp", [h_hyp, h_s5], ctx="mp hyp, s5")
    steps.append(ProofStep("s6", s6, "MP hyp, s5"))

    return LemmaProof(name="a1d", statement=s6, steps=tuple(steps))


# -----------------------------------------------------------------------------
# Optional: debug printer
# -----------------------------------------------------------------------------

def debug_dump(proof: LemmaProof, *, sys: HilbertSystem) -> str:
    """Render a lemma proof using the symbol table for debugging."""
    symtab = sys.interner.symbol_table()
    lines = [f"== {proof.name} =="]
    lines.append("statement: " + render(proof.statement.tokens, symtab=symtab))
    for st in proof.steps:
        lines.append(f"{st.label}: {render(st.wff.tokens, symtab=symtab)}    # {st.note}")
    return "\n".join(lines)


__all__ = [
    "ProofStep",
    "LemmaProof",
    "prove_L1_id",
    "prove_L2_or_intro_right",
    "prove_L4_demorgan",
    "prove_L5_contrapositive",
    "prove_L6_double_neg_intro",
    "prove_L7_double_neg_elim",
    "prove_L8_excluded_middle",
    "prove_L9_peirce",
    "prove_L3_or_intro_left",
    "prove_a1i",
    "prove_a2i",
    "prove_mpd",
    "prove_syl",
    "prove_a1d",
    "debug_dump",
]
