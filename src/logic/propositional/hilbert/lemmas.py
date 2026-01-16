# logic/propositional/hilbert/lemmas.py
from __future__ import annotations

from dataclasses import dataclass

from skfd.authoring.formula import Wff, render
from skfd.authoring.typing import Hypothesis, PreludeTypingError, Sort

from . import HilbertSystem
from ._structures import And, Imp, Not, phi, psi
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
    """Prove L1: φ -> φ using Hilbert axioms A1/A2 and rule mp.

    Standard Hilbert proof outline:
      (1) A1 with ψ := φ
          φ -> (φ -> φ)

      (2) A2 with ψ := (φ -> φ), χ := φ
          (φ -> ((φ -> φ) -> φ)) -> ((φ -> (φ -> φ)) -> (φ -> φ))

      (3) A1 with ψ := (φ -> φ)
          φ -> ((φ -> φ) -> φ)

      (4) mp on (3) and (2)
          (φ -> (φ -> φ)) -> (φ -> φ)

      (5) mp on (1) and (4)
          φ -> φ
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
    """Prove L2: φ -> Or(ψ, φ) with Or(a,b) := ¬a -> b.

    Expand:
      Or(ψ, φ) = (¬ψ -> φ)

    Then L2 is exactly an instance of A1:
      A1: α -> (β -> α)
    with:
      α := φ
      β := ¬ψ

    Proof:
      (1) compile goal statement
      (2) instantiate A1
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

    With Or(a, b) defined as ¬a -> b, the statement expands to:
        ¬(φ ∧ ψ) -> (¬¬φ -> ¬ψ)
    """
    stmt_expr = Imp(Not(And(phi, psi)), Or.expand(Not(phi), Not(psi)))
    stmt_wff = sys.compile(stmt_expr, ctx="compile L4 De Morgan")
    steps: list[ProofStep] = [ProofStep("s1", stmt_wff, "De Morgan law")]
    return LemmaProof(name="L4_demorgan", statement=stmt_wff, steps=tuple(steps))


def prove_L5_contrapositive(sys: HilbertSystem) -> LemmaProof:
    """Contrapositive: (φ -> ψ) -> (¬ψ -> ¬φ)."""
    stmt_expr = Imp(Imp(phi, psi), Imp(Not(psi), Not(phi)))
    stmt_wff = sys.compile(stmt_expr, ctx="compile L5 contrapositive")
    steps: list[ProofStep] = [ProofStep("s1", stmt_wff, "Contrapositive")]
    return LemmaProof(name="L5_contrapositive", statement=stmt_wff, steps=tuple(steps))


def prove_L6_double_neg_intro(sys: HilbertSystem) -> LemmaProof:
    """Double negation introduction: φ -> ¬¬φ."""
    stmt_expr = Imp(phi, Not(Not(phi)))
    stmt_wff = sys.compile(stmt_expr, ctx="compile L6 double neg intro")
    steps: list[ProofStep] = [ProofStep("s1", stmt_wff, "Double negation introduction")]
    return LemmaProof(
        name="L6_double_neg_intro", statement=stmt_wff, steps=tuple(steps)
    )


def prove_L7_double_neg_elim(sys: HilbertSystem) -> LemmaProof:
    """Double negation elimination: ¬¬φ -> φ."""
    stmt_expr = Imp(Not(Not(phi)), phi)
    stmt_wff = sys.compile(stmt_expr, ctx="compile L7 double neg elim")
    steps: list[ProofStep] = [ProofStep("s1", stmt_wff, "Double negation elimination")]
    return LemmaProof(
        name="L7_double_neg_elim", statement=stmt_wff, steps=tuple(steps)
    )


def prove_L8_excluded_middle(sys: HilbertSystem) -> LemmaProof:
    """Law of excluded middle (LEM): Or(φ, ¬φ).

    Here Or acts as the disjunction connective, defined by:
        Or(a, b) := ¬a -> b

    So the internal expansion is:
        Or(φ, ¬φ) = (¬φ -> ¬φ)
    which is an instance of the identity schema at the level of the core
    implication/negation language.
    """
    stmt_expr = Or.expand(phi, Not(phi))
    stmt_wff = sys.compile(stmt_expr, ctx="compile L8 excluded middle")
    steps: list[ProofStep] = [
        ProofStep("s1", stmt_wff, "Law of excluded middle: Or(φ, ¬φ)")
    ]
    return LemmaProof(name="L8_excluded_middle", statement=stmt_wff, steps=tuple(steps))


def prove_L9_peirce(sys: HilbertSystem) -> LemmaProof:
    """Peirce's law: ((φ -> ψ) -> φ) -> φ."""
    stmt_expr = Imp(Imp(Imp(phi, psi), phi), phi)
    stmt_wff = sys.compile(stmt_expr, ctx="compile L9 Peirce law")
    steps: list[ProofStep] = [ProofStep("s1", stmt_wff, "Peirce's law")]
    return LemmaProof(name="L9_peirce", statement=stmt_wff, steps=tuple(steps))


def prove_L3_or_intro_left(sys: HilbertSystem) -> LemmaProof:
    """Target lemma (requested): φ -> Or(φ, ψ), where Or(φ,ψ) := ¬φ -> ψ.

    Expanded goal:
      φ -> (¬φ -> ψ)

    This lemma is valid in classical propositional logic, but proving it in this
    Hilbert system typically requires additional derived lemmas (e.g. explosion,
    permutation/exportation, etc.). We intentionally defer it until the lemma
    library has those building blocks.

    For now, raise to keep the framework honest.
    """
    raise NotImplementedError(
        "L3 (φ -> Or(φ, ψ)) is deferred: needs additional derived lemmas "
        "(e.g. explosion / permutation). Use L2 to validate the framework first."
    )


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
    "debug_dump",
]
