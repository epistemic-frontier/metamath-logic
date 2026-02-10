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
from skfd.authoring.parsing import wff
from skfd.authoring.typing import Hypothesis, PreludeTypingError

from . import HilbertSystem

# -----------------------------------------------------------------------------
# Proof result container (debug-friendly)
# -----------------------------------------------------------------------------

@dataclass(frozen=True)
class ProofStep:
    """One proof step for debugging/introspection."""

    label: str
    wff: Wff
    note: str
    op: str = "raw"
    args: tuple[str, ...] = ()
    ref: str | None = None


@dataclass(frozen=True)
class LemmaProof:
    """A lemma proof artifact produced by the authoring/proof script."""

    name: str
    statement: Wff
    steps: tuple[ProofStep, ...]


class LemmaBuilder:
    """Helper to build lemma proofs with less boilerplate."""

    def __init__(self, sys: HilbertSystem, name: str):
        self.sys = sys
        self.name = name
        self.steps: list[ProofStep] = []
        self._wff_to_label: dict[int, str] = {}

    def _remember(self, label: str, stmt: Wff) -> None:
        self._wff_to_label[id(stmt)] = label
    
    def _compile_str(self, label: str, expr_str: str) -> Wff:
        try:
            expr = wff(expr_str)
        except PreludeTypingError as e:
            raise PreludeTypingError(f"{label}: parse failed for {expr_str!r}\n{e}") from e
        return self.sys._compile(expr, ctx=label)

    def hyp(self, label: str, expr_str: str) -> Wff:
        """Add a hypothesis step."""
        stmt = self._compile_str(label, expr_str)
        self.steps.append(ProofStep(label, stmt, "Hypothesis", op="hyp"))
        self._remember(label, stmt)
        return stmt

    def ref(self, label: str, expr_str: str, *, ref: str, note: str = "") -> Wff:
        """Add a reference step (axiom/theorem instance).

        `ref` must be explicit. Do not encode proof semantics in free-form text.
        """
        stmt = self._compile_str(label, expr_str)
        self.steps.append(ProofStep(label, stmt, note, op="ref", ref=ref))
        self._remember(label, stmt)
        return stmt

    def raw(self, label: str, expr_str: str, *, note: str = "") -> Wff:
        """Add an opaque step (not guaranteed to be lowerable)."""
        stmt = self._compile_str(label, expr_str)
        self.steps.append(ProofStep(label, stmt, note, op="raw", ref=None))
        self._remember(label, stmt)
        return stmt
    
    def mp(self, label: str, major: Wff, minor: Wff, note: str = "mp") -> Wff:
        """Add a Modus Ponens step."""
        # Create implicit hypotheses for the rule application
        h1 = Hypothesis(f"h_{label}_maj", major)  # type: ignore[arg-type]
        h2 = Hypothesis(f"h_{label}_min", minor)  # type: ignore[arg-type]
        res = self.sys._apply("mp", [h1, h2], ctx=label)
        maj_label = self._wff_to_label.get(id(major))
        min_label = self._wff_to_label.get(id(minor))
        if maj_label is None or min_label is None:
            raise ValueError(f"{label}: mp args must be steps created by this LemmaBuilder")
        self.steps.append(ProofStep(label, res, note, op="mp", args=(maj_label, min_label)))
        self._remember(label, res)
        return res

    def build(self, statement: Wff) -> LemmaProof:
        """Build the final LemmaProof."""
        return LemmaProof(name=self.name, statement=statement, steps=tuple(self.steps))


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
    lb = LemmaBuilder(sys, "L1_id")

    # A1 with ψ := φ
    s1 = lb.ref(
        "s1",
        "φ → ( φ → φ )",
        ref="A1",
        note="A1 with (phi, psi) = (φ, φ)",
    )

    # A2 with ψ := (φ -> φ), χ := φ
    s2 = lb.ref(
        "s2",
        "( φ → ( ( φ → φ ) → φ ) ) → ( ( φ → ( φ → φ ) ) → ( φ → φ ) )",
        ref="A2",
        note="A2 with (phi, psi, chi) = (φ, (φ→φ), φ)",
    )

    # A1 with ψ := (φ -> φ)
    s3 = lb.ref(
        "s3",
        "φ → ( ( φ → φ ) → φ )",
        ref="A1",
        note="A1 with (phi, psi) = (φ, (φ→φ))",
    )

    # (4) mp(s3, s2)
    s4 = lb.mp("s4", s3, s2, "mp on s3 and s2")

    # (5) mp(s1, s4)
    s5 = lb.mp("s5", s1, s4, "mp on s1 and s4")

    return lb.build(s5)


def prove_L2_or_intro_right(sys: HilbertSystem) -> LemmaProof:
    """Right disjunction introduction: φ -> Or(ψ, φ).

    Formula: φ -> Or(ψ, φ)
    Reading: From φ we can conclude Or(ψ, φ).
    Notes:
    - Or(a, b) is defined as ¬a -> b, so Or(ψ, φ) = (¬ψ -> φ).
    - The lemma is an instance of A1 with α := φ and β := ¬ψ.
    """
    lb = LemmaBuilder(sys, "L2_or_intro_right")

    # (1) A1: φ -> (¬ψ -> φ)
    # Authoring: statement Expr = φ -> Or(ψ, φ) -> ph -> ( -. ps -> ph )
    s1 = lb.ref(
        "s1",
        "φ → ( ¬ ψ → φ )",
        ref="A1",
        note="A1 with (alpha, beta) = (φ, ¬ψ)",
    )

    return lb.build(s1)


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
    lb = LemmaBuilder(sys, "L4_demorgan")
    stmt = lb.raw("s1", "¬ ( φ ∧ ψ ) → ( ¬ ¬ φ → ¬ ψ )", note="De Morgan law")
    return lb.build(stmt)


def prove_L5_contrapositive(sys: HilbertSystem) -> LemmaProof:
    """Contrapositive: (φ -> ψ) -> (¬ψ -> ¬φ).

    Formula: (φ -> ψ) -> (¬ψ -> ¬φ)
    Reading: If φ implies ψ, then from ¬ψ we may infer ¬φ.
    """
    lb = LemmaBuilder(sys, "L5_contrapositive")
    stmt = lb.raw("s1", "( φ → ψ ) → ( ¬ ψ → ¬ φ )", note="Contrapositive")
    return lb.build(stmt)


def prove_L6_double_neg_intro(sys: HilbertSystem) -> LemmaProof:
    """Double negation introduction: φ -> ¬¬φ.

    Formula: φ -> ¬¬φ
    Reading: If φ holds then it is not the case that φ does not hold.
    """
    lb = LemmaBuilder(sys, "L6_double_neg_intro")
    stmt = lb.raw("s1", "φ → ¬ ¬ φ", note="Double negation introduction")
    return lb.build(stmt)


def prove_L7_double_neg_elim(sys: HilbertSystem) -> LemmaProof:
    """Double negation elimination: ¬¬φ -> φ.

    Formula: ¬¬φ -> φ
    Reading: From it not being the case that φ does not hold, infer φ.
    Notes:
    - This is a classical principle connecting double negation and affirmation.
    """
    lb = LemmaBuilder(sys, "L7_double_neg_elim")
    stmt = lb.raw("s1", "¬ ¬ φ → φ", note="Double negation elimination")
    return lb.build(stmt)


def prove_L8_excluded_middle(sys: HilbertSystem) -> LemmaProof:
    """Law of excluded middle (LEM): Or(φ, ¬φ).

    Formula: Or(φ, ¬φ)
    Reading: Every proposition is either true or its negation is true.
    Notes:
    - Or(a, b) is defined as ¬a -> b, so Or(φ, ¬φ) = (¬φ -> ¬φ).
    - Internally this is an instance of the identity schema in the core language.
    """
    lb = LemmaBuilder(sys, "L8_excluded_middle")
    stmt = lb.raw("s1", "¬ φ → ¬ φ", note="Law of excluded middle: Or(φ, ¬φ)")
    return lb.build(stmt)


def prove_L9_peirce(sys: HilbertSystem) -> LemmaProof:
    """Peirce's law: ((φ -> ψ) -> φ) -> φ.

    Formula: ((φ -> ψ) -> φ) -> φ
    Reading: If assuming (φ -> ψ) lets us derive φ, then φ already holds.
    Notes:
    - Characteristic of classical logic; interderivable with excluded middle over
      suitable axiom bases.
    """
    lb = LemmaBuilder(sys, "L9_peirce")
    stmt = lb.raw("s1", "( ( φ → ψ ) → φ ) → φ", note="Peirce's law")
    return lb.build(stmt)


def prove_L10_linearity(sys: HilbertSystem) -> LemmaProof:
    """Linearity: (φ -> ψ) ∨ (ψ -> φ).

    Formula: (φ -> ψ) ∨ (ψ -> φ)
    Equivalent to: ¬(φ -> ψ) -> (ψ -> φ)
    Reading: For any two propositions, one implies the other.
    Notes:
    - This is a property of classical logic (and linear logic), but not intuitionistic logic.
    - Also known as Dummett's Law in intermediate logics.
    """
    lb = LemmaBuilder(sys, "L10_linearity")
    
    # Goal: -. ( ph -> ps ) -> ( ps -> ph )
    
    # Step 1: -. ( ph -> ps ) -> ph
    # 1.1: -. ph -> ( ph -> ps ) (pm2.21)
    s1_1 = lb.ref("s1.1", "¬ φ → ( φ → ψ )", ref="pm2.21", note="pm2.21")
    
    # 1.2: ( -. ph -> ( ph -> ps ) ) -> ( -. ( ph -> ps ) -> -. -. ph ) (con3)
    s1_2 = lb.ref(
        "s1.2",
        "( ¬ φ → ( φ → ψ ) ) → ( ¬ ( φ → ψ ) → ¬ ¬ φ )",
        ref="con3",
        note="con3 instance",
    )
    
    # 1.3: -. ( ph -> ps ) -> -. -. ph
    s1_3 = lb.mp("s1.3", s1_1, s1_2)
    
    # 1.4: -. -. ph -> ph (L7)
    s1_4 = lb.ref("s1.4", "¬ ¬ φ → φ", ref="L7_double_neg_elim", note="L7_double_neg_elim")
    
    # 1.5: -. ( ph -> ps ) -> ph (Syllogism: s1.3, s1.4)
    # syl steps manually expanded:
    s1_4_lift = lb.ref(
        "s1.4_lift",
        "( ¬ ¬ φ → φ ) → ( ¬ ( φ → ψ ) → ( ¬ ¬ φ → φ ) )",
        ref="A1",
        note="A1",
    )
    s1_5_pre = lb.mp("s1.5_pre", s1_4, s1_4_lift)
    s1_5_dist = lb.ref(
        "s1.5_dist",
        "( ¬ ( φ → ψ ) → ( ¬ ¬ φ → φ ) ) → ( ( ¬ ( φ → ψ ) → ¬ ¬ φ ) → ( ¬ ( φ → ψ ) → φ ) )",
        ref="A2",
        note="A2",
    )
    s1_5_impl = lb.mp("s1.5_impl", s1_5_pre, s1_5_dist)
    s1_5 = lb.mp("s1.5", s1_3, s1_5_impl)
    
    # Step 2: ph -> ( ps -> ph ) (A1)
    s2 = lb.ref("s2", "φ → ( ψ → φ )", ref="A1", note="A1")
    
    # Step 3: -. ( ph -> ps ) -> ( ps -> ph ) (Syllogism: s1.5, s2)
    # syl steps manually expanded:
    s2_lift = lb.ref(
        "s2_lift",
        "( φ → ( ψ → φ ) ) → ( ¬ ( φ → ψ ) → ( φ → ( ψ → φ ) ) )",
        ref="A1",
        note="A1",
    )
    s3_pre = lb.mp("s3_pre", s2, s2_lift)
    s3_dist = lb.ref(
        "s3_dist",
        "( ¬ ( φ → ψ ) → ( φ → ( ψ → φ ) ) ) → ( ( ¬ ( φ → ψ ) → φ ) → ( ¬ ( φ → ψ ) → ( ψ → φ ) ) )",
        ref="A2",
        note="A2",
    )
    s3_impl = lb.mp("s3_impl", s3_pre, s3_dist)
    s3 = lb.mp("s3", s1_5, s3_impl)
    
    return lb.build(s3)


def prove_modus_tollens(sys: HilbertSystem) -> LemmaProof:
    """Modus Tollens: φ -> ψ, ¬ψ ⊢ ¬φ.

    Hyp 1: φ -> ψ
    Hyp 2: ¬ψ
    Concl: ¬φ
    """
    lb = LemmaBuilder(sys, "modus_tollens")
    
    h1 = lb.hyp("h1", "φ → ψ")
    h2 = lb.hyp("h2", "¬ ψ")
    
    # (ph -> ps) -> (-. ps -> -. ph) (con3)
    s1 = lb.ref("s1", "( φ → ψ ) → ( ¬ ψ → ¬ φ )", ref="con3", note="con3")
    
    # -. ps -> -. ph
    s2 = lb.mp("s2", h1, s1, "MP h1, s1")
    
    # -. ph
    s3 = lb.mp("s3", h2, s2, "MP h2, s2")
    
    return lb.build(s3)


def prove_L3_or_intro_left(sys: HilbertSystem) -> LemmaProof:
    """Left disjunction introduction: φ -> Or(φ, ψ).

    Formula: φ -> Or(φ, ψ)
    Expanded: φ -> (¬φ -> ψ)
    Notes:
    - Or(a, b) is defined as ¬a -> b.
    - This matches set.mm theorem `pm2.24`.
    """
    lb = LemmaBuilder(sys, "L3_or_intro_left")
    s1 = lb.ref("s1", "φ → ( ¬ φ → ψ )", ref="pm2.24", note="pm2.24")
    return lb.build(s1)


# -----------------------------------------------------------------------------
# Migration Expansion (set.mm compatibility)
# -----------------------------------------------------------------------------


def prove_a1i(sys: HilbertSystem) -> LemmaProof:
    """a1i: ph -> (ps -> ph).

    Hyp: ph
    Concl: ps -> ph
    """
    lb = LemmaBuilder(sys, "a1i")
    hyp = lb.hyp("a1i.1", "φ")
    a1 = lb.ref("s1", "φ → ( ψ → φ )", ref="A1", note="A1")
    res = lb.mp("s2", hyp, a1, "MP a1i.1, s1")
    return lb.build(res)


def prove_a2i(sys: HilbertSystem) -> LemmaProof:
    """a2i: (ph -> ps) -> (ph -> ch).

    Hyp: ph -> (ps -> ch)
    Concl: (ph -> ps) -> (ph -> ch)
    """
    lb = LemmaBuilder(sys, "a2i")
    hyp = lb.hyp("a2i.1", "φ → ( ψ → χ )")
    a2 = lb.ref("s1", "( φ → ( ψ → χ ) ) → ( ( φ → ψ ) → ( φ → χ ) )", ref="A2", note="A2")
    res = lb.mp("s2", hyp, a2, "MP a2i.1, s1")
    return lb.build(res)


def prove_mpd(sys: HilbertSystem) -> LemmaProof:
    """mpd: ph -> ch.

    Hyp 1: ph -> ps
    Hyp 2: ph -> (ps -> ch)
    Concl: ph -> ch
    """
    lb = LemmaBuilder(sys, "mpd")
    h1 = lb.hyp("mpd.1", "φ → ψ")
    h2 = lb.hyp("mpd.2", "φ → ( ψ → χ )")
    a2 = lb.ref("s1", "( φ → ( ψ → χ ) ) → ( ( φ → ψ ) → ( φ → χ ) )", ref="A2", note="A2")
    s2 = lb.mp("s2", h2, a2, "MP mpd.2, s1")
    s3 = lb.mp("s3", h1, s2, "MP mpd.1, s2")
    return lb.build(s3)


def prove_syl(sys: HilbertSystem) -> LemmaProof:
    """syl: ph -> ch.

    Hyp 1: ph -> ps
    Hyp 2: ps -> ch
    Concl: ph -> ch
    """
    lb = LemmaBuilder(sys, "syl")
    h1 = lb.hyp("syl.1", "φ → ψ")
    h2 = lb.hyp("syl.2", "ψ → χ")
    a1 = lb.ref("s1", "( ψ → χ ) → ( φ → ( ψ → χ ) )", ref="A1", note="A1")
    s2 = lb.mp("s2", h2, a1, "MP syl.2, s1")
    a2 = lb.ref("s3", "( φ → ( ψ → χ ) ) → ( ( φ → ψ ) → ( φ → χ ) )", ref="A2", note="A2")
    s4 = lb.mp("s4", s2, a2, "MP s2, s3")
    s5 = lb.mp("s5", h1, s4, "MP syl.1, s4")
    return lb.build(s5)


def prove_sylcom(sys: HilbertSystem) -> LemmaProof:
    """sylcom: ph -> (ps -> th).
    
    Hyp 1: ph -> (ps -> ch)
    Hyp 2: ps -> (ch -> th)
    Concl: ph -> (ps -> th)
    """
    lb = LemmaBuilder(sys, "sylcom")
    
    hyp1_wff = lb.hyp("sylcom.1", "φ → ( ψ → χ )")
    hyp2_wff = lb.hyp("sylcom.2", "ψ → ( χ → θ )")
    
    s1 = lb.ref(
        "s1",
        "( ψ → ( χ → θ ) ) → ( ( ψ → χ ) → ( ψ → θ ) )",
        ref="A2",
        note="A2(ps,ch,th)",
    )
    s2 = lb.mp("s2", hyp2_wff, s1, "(ps->ch)->(ps->th)")
    
    s3 = lb.ref(
        "s3",
        "( ( ψ → χ ) → ( ψ → θ ) ) → ( φ → ( ( ψ → χ ) → ( ψ → θ ) ) )",
        ref="A1",
        note="A1 lift",
    )
    s4 = lb.mp("s4", s2, s3, "φ→((ψ→χ)→(ψ→θ))")
    
    s5 = lb.ref(
        "s5",
        "( φ → ( ( ψ → χ ) → ( ψ → θ ) ) ) → ( ( φ → ( ψ → χ ) ) → ( φ → ( ψ → θ ) ) )",
        ref="A2",
        note="A2 special",
    )
    s6 = lb.mp("s6", s4, s5, "(ph->(ps->ch))->(ph->(ps->th))")
    
    s7 = lb.mp("s7", hyp1_wff, s6, "φ→(ψ→θ)")
    
    return lb.build(s7)


def prove_com12(sys: HilbertSystem) -> LemmaProof:
    """com12: ps -> (ph -> ch).
    
    Hyp: ph -> (ps -> ch)
    Concl: ps -> (ph -> ch)
    """
    lb = LemmaBuilder(sys, "com12")
    
    hyp_wff = lb.hyp("com12.1", "φ → ( ψ → χ )")
    
    s1 = lb.ref("s1", "ψ → ( φ → ψ )", ref="A1", note="A1 ps->(ph->ps)")
    s2 = lb.ref(
        "s2",
        "( φ → ( ψ → χ ) ) → ( ( φ → ψ ) → ( φ → χ ) )",
        ref="A2",
        note="A2 (ph,(ps->ch))",
    )
    
    s3 = lb.mp("s3", hyp_wff, s2, "(ph->ps)->(ph->ch)")
    
    s4 = lb.ref(
        "s4",
        "( ( φ → ψ ) → ( φ → χ ) ) → ( ψ → ( ( φ → ψ ) → ( φ → χ ) ) )",
        ref="A1",
        note="A1 lift",
    )
    s5 = lb.mp("s5", s3, s4, "ψ→((φ→ψ)→(φ→χ))")
    
    s6 = lb.ref(
        "s6",
        "( ψ → ( ( φ → ψ ) → ( φ → χ ) ) ) → ( ( ψ → ( φ → ψ ) ) → ( ψ → ( φ → χ ) ) )",
        ref="A2",
        note="A2(ps,...)",
    )
    s7 = lb.mp("s7", s5, s6, "(ps->(ph->ps))->(ps->(ph->ch))")
    
    s8 = lb.mp("s8", s1, s7, "ψ→(φ→χ)")
    
    return lb.build(s8)


def prove_syl5(sys: HilbertSystem) -> LemmaProof:
    """syl5: ch -> (ph -> th)."""
    lb = LemmaBuilder(sys, "syl5")
    stmt = lb.raw("s1", "χ → ( φ → θ )", note="syl5 statement")
    return lb.build(stmt)


def prove_syl6(sys: HilbertSystem) -> LemmaProof:
    """syl6: ph -> (ps -> th).
    
    Hyp 1: ph -> (ps -> ch)
    Hyp 2: ch -> th
    Concl: ph -> (ps -> th)
    """
    lb = LemmaBuilder(sys, "syl6")
    
    hyp1_wff = lb.hyp("syl6.1", "φ → ( ψ → χ )")
    hyp2_wff = lb.hyp("syl6.2", "χ → θ")
    
    s1 = lb.ref(
        "s1",
        "( χ → θ ) → ( ψ → ( χ → θ ) )",
        ref="A1",
        note="A1(ch->th, ps)",
    )
    s2 = lb.mp("s2", hyp2_wff, s1, "ψ→(χ→θ)")
    
    s3 = lb.ref(
        "s3",
        "( ψ → ( χ → θ ) ) → ( ( ψ → χ ) → ( ψ → θ ) )",
        ref="A2",
        note="A2(ps,ch,th)",
    )
    s4 = lb.mp("s4", s2, s3, "(ps->ch)->(ps->th)")
    
    s5 = lb.ref(
        "s5",
        "( ( ψ → χ ) → ( ψ → θ ) ) → ( φ → ( ( ψ → χ ) → ( ψ → θ ) ) )",
        ref="A1",
        note="A1 lift",
    )
    s6 = lb.mp("s6", s4, s5, "φ→((ψ→χ)→(ψ→θ))")
    
    s7 = lb.ref(
        "s7",
        "( φ → ( ( ψ → χ ) → ( ψ → θ ) ) ) → ( ( φ → ( ψ → χ ) ) → ( φ → ( ψ → θ ) ) )",
        ref="A2",
        note="A2 special",
    )
    s8 = lb.mp("s8", s6, s7, "(ph->(ps->ch))->(ph->(ps->th))")
    
    s9 = lb.mp("s9", hyp1_wff, s8, "φ→(ψ→θ)")
    
    return lb.build(s9)

def prove_a1d(sys: HilbertSystem) -> LemmaProof:
    """a1d: ph -> (ch -> ps).
    
    Hyp: ph -> ps
    Concl: ph -> (ch -> ps)
    """
    lb = LemmaBuilder(sys, "a1d")
    
    hyp_wff = lb.hyp("a1d.1", "φ → ψ")
    
    # A1: ps -> (ch -> ps)
    s1 = lb.ref("s1", "ψ → ( χ → ψ )", ref="A1", note="A1")
    
    # A1 (syl)
    s2 = lb.ref(
        "s2",
        "( ψ → ( χ → ψ ) ) → ( φ → ( ψ → ( χ → ψ ) ) )",
        ref="A1",
        note="A1 (syl)",
    )
    s3 = lb.mp("s3", s1, s2, "MP s1, s2")
    
    # A2 (syl)
    s4 = lb.ref(
        "s4",
        "( φ → ( ψ → ( χ → ψ ) ) ) → ( ( φ → ψ ) → ( φ → ( χ → ψ ) ) )",
        ref="A2",
        note="A2 (syl)",
    )
    s5 = lb.mp("s5", s3, s4, "MP s3, s4")
    
    # MP hyp, s5
    s6 = lb.mp("s6", hyp_wff, s5, "MP hyp, s5")
    
    return lb.build(s6)


# -----------------------------------------------------------------------------
# Expanded lemmas
# -----------------------------------------------------------------------------

def prove_idd(sys: HilbertSystem) -> LemmaProof:
    """idd: ph -> (ps -> ps)."""
    lb = LemmaBuilder(sys, "idd")
    stmt = lb.raw("res", "φ → ( ψ → ψ )", note="Imported")
    return lb.build(stmt)

def prove_a1i13(sys: HilbertSystem) -> LemmaProof:
    """a1i13: ph -> (ps -> (ch -> th)). Hyp: ps -> th."""
    lb = LemmaBuilder(sys, "a1i13")
    lb.hyp("hyp", "ψ → θ")
    stmt = lb.raw("res", "φ → ( ψ → ( χ → θ ) )", note="Imported")
    return lb.build(stmt)

def prove_2a1d(sys: HilbertSystem) -> LemmaProof:
    """2a1d: ph -> (ch -> (th -> ps)). Hyp: ph -> ps."""
    lb = LemmaBuilder(sys, "2a1d")
    lb.hyp("hyp", "φ → ψ")
    stmt = lb.raw("res", "φ → ( χ → ( θ → ψ ) )", note="Imported")
    return lb.build(stmt)

def prove_2a1(sys: HilbertSystem) -> LemmaProof:
    """2a1: ph -> (ps -> (ch -> ph))."""
    lb = LemmaBuilder(sys, "2a1")
    stmt = lb.raw("res", "φ → ( ψ → ( χ → φ ) )", note="Imported")
    return lb.build(stmt)

def prove_a2d(sys: HilbertSystem) -> LemmaProof:
    """a2d: ph -> ((ps -> ch) -> (ps -> th)). Hyp: ph -> (ps -> (ch -> th))."""
    lb = LemmaBuilder(sys, "a2d")
    lb.hyp("hyp", "φ → ( ψ → ( χ → θ ) )")
    stmt = lb.raw("res", "φ → ( ( ψ → χ ) → ( ψ → θ ) )", note="Imported")
    return lb.build(stmt)

def prove_syl5com(sys: HilbertSystem) -> LemmaProof:
    """syl5com: ph -> (ch -> th). Hyp1: ph -> ps, Hyp2: ch -> (ps -> th)."""
    lb = LemmaBuilder(sys, "syl5com")
    lb.hyp("hyp1", "φ → ψ")
    lb.hyp("hyp2", "χ → ( ψ → θ )")
    stmt = lb.raw("res", "φ → ( χ → θ )", note="Imported")
    return lb.build(stmt)

def prove_syl11(sys: HilbertSystem) -> LemmaProof:
    """syl11: ps -> (th -> ch). Hyp1: ph -> (ps -> ch), Hyp2: th -> ph."""
    lb = LemmaBuilder(sys, "syl11")
    lb.hyp("hyp1", "φ → ( ψ → χ )")
    lb.hyp("hyp2", "θ → φ")
    stmt = lb.raw("res", "ψ → ( θ → χ )", note="Imported")
    return lb.build(stmt)

def prove_syl56(sys: HilbertSystem) -> LemmaProof:
    """syl56: ch -> (ph -> ta). Hyp1: ph -> ps, Hyp2: ch -> (ps -> th), Hyp3: th -> ta."""
    lb = LemmaBuilder(sys, "syl56")
    lb.hyp("hyp1", "φ → ψ")
    lb.hyp("hyp2", "χ → ( ψ → θ )")
    lb.hyp("hyp3", "θ → τ")
    stmt = lb.raw("res", "χ → ( φ → τ )", note="Imported")
    return lb.build(stmt)

def prove_syl6com(sys: HilbertSystem) -> LemmaProof:
    """syl6com: ps -> (ph -> th). Hyp1: ph -> (ps -> ch), Hyp2: ch -> th."""
    lb = LemmaBuilder(sys, "syl6com")
    lb.hyp("hyp1", "φ → ( ψ → χ )")
    lb.hyp("hyp2", "χ → θ")
    stmt = lb.raw("res", "ψ → ( φ → θ )", note="Imported")
    return lb.build(stmt)

def prove_mpcom(sys: HilbertSystem) -> LemmaProof:
    """mpcom: ps -> ch. Hyp1: ps -> ph, Hyp2: ph -> (ps -> ch)."""
    lb = LemmaBuilder(sys, "mpcom")
    lb.hyp("hyp1", "ψ → φ")
    lb.hyp("hyp2", "φ → ( ψ → χ )")
    stmt = lb.raw("res", "ψ → χ", note="Imported")
    return lb.build(stmt)

def prove_syli(sys: HilbertSystem) -> LemmaProof:
    """syli: ps -> (ph -> th). Hyp1: ps -> (ph -> ch), Hyp2: ch -> (ph -> th)."""
    lb = LemmaBuilder(sys, "syli")
    lb.hyp("hyp1", "ψ → ( φ → χ )")
    lb.hyp("hyp2", "χ → ( φ → θ )")
    stmt = lb.raw("res", "ψ → ( φ → θ )", note="Imported")
    return lb.build(stmt)

def prove_syl2im(sys: HilbertSystem) -> LemmaProof:
    """syl2im: ph -> (ch -> ta). Hyp1: ph -> ps, Hyp2: ch -> th, Hyp3: ps -> (th -> ta)."""
    lb = LemmaBuilder(sys, "syl2im")
    lb.hyp("hyp1", "φ → ψ")
    lb.hyp("hyp2", "χ → θ")
    lb.hyp("hyp3", "ψ → ( θ → τ )")
    stmt = lb.raw("res", "φ → ( χ → τ )", note="Imported")
    return lb.build(stmt)

def prove_syl2imc(sys: HilbertSystem) -> LemmaProof:
    """syl2imc: ch -> (ph -> ta). Hyp1: ph -> ps, Hyp2: ch -> th, Hyp3: ps -> (th -> ta)."""
    lb = LemmaBuilder(sys, "syl2imc")
    lb.hyp("hyp1", "φ → ψ")
    lb.hyp("hyp2", "χ → θ")
    lb.hyp("hyp3", "ψ → ( θ → τ )")
    stmt = lb.raw("res", "χ → ( φ → τ )", note="Imported")
    return lb.build(stmt)

def prove_pm2_27(sys: HilbertSystem) -> LemmaProof:
    """pm2.27: ph -> ((ph -> ps) -> ps)."""
    lb = LemmaBuilder(sys, "pm2.27")
    stmt = lb.raw("res", "φ → ( ( φ → ψ ) → ψ )", note="Imported")
    return lb.build(stmt)

def prove_mpdd(sys: HilbertSystem) -> LemmaProof:
    """mpdd: ph -> (ps -> th). Hyp1: ph -> (ps -> ch), Hyp2: ph -> (ps -> (ch -> th))."""
    lb = LemmaBuilder(sys, "mpdd")
    lb.hyp("hyp1", "φ → ( ψ → χ )")
    lb.hyp("hyp2", "φ → ( ψ → ( χ → θ ) )")
    stmt = lb.raw("res", "φ → ( ψ → θ )", note="Imported")
    return lb.build(stmt)

def prove_mpid(sys: HilbertSystem) -> LemmaProof:
    """mpid: ph -> (ps -> th). Hyp1: ph -> ch, Hyp2: ph -> (ps -> (ch -> th))."""
    lb = LemmaBuilder(sys, "mpid")
    lb.hyp("hyp1", "φ → χ")
    lb.hyp("hyp2", "φ → ( ψ → ( χ → θ ) )")
    stmt = lb.raw("res", "φ → ( ψ → θ )", note="Imported")
    return lb.build(stmt)


def prove_con1(sys: HilbertSystem) -> LemmaProof:
    """con1: ( -. ph -> ps ) -> ( -. ps -> ph )."""
    lb = LemmaBuilder(sys, "con1")
    stmt = lb.raw("res", "( ¬ φ → ψ ) → ( ¬ ψ → φ )", note="Imported")
    return lb.build(stmt)

def prove_con2(sys: HilbertSystem) -> LemmaProof:
    """con2: ( ph -> -. ps ) -> ( ps -> -. ph )."""
    lb = LemmaBuilder(sys, "con2")
    stmt = lb.raw("res", "( φ → ¬ ψ ) → ( ψ → ¬ φ )", note="Imported")
    return lb.build(stmt)

def prove_con3(sys: HilbertSystem) -> LemmaProof:
    """con3: ( ph -> ps ) -> ( -. ps -> -. ph )."""
    lb = LemmaBuilder(sys, "con3")
    stmt = lb.raw("res", "( φ → ψ ) → ( ¬ ψ → ¬ φ )", note="Imported")
    return lb.build(stmt)

def prove_con4(sys: HilbertSystem) -> LemmaProof:
    """con4: ( -. ph -> -. ps ) -> ( ps -> ph )."""
    lb = LemmaBuilder(sys, "con4")
    stmt = lb.raw("res", "( ¬ φ → ¬ ψ ) → ( ψ → φ )", note="Imported")
    return lb.build(stmt)

def prove_pm2_21(sys: HilbertSystem) -> LemmaProof:
    """pm2.21: -. ph -> ( ph -> ps )."""
    lb = LemmaBuilder(sys, "pm2.21")
    stmt = lb.raw("res", "¬ φ → ( φ → ψ )", note="Imported")
    return lb.build(stmt)

def prove_pm2_24(sys: HilbertSystem) -> LemmaProof:
    """pm2.24: ph -> ( -. ph -> ps )."""
    lb = LemmaBuilder(sys, "pm2.24")
    stmt = lb.raw("res", "φ → ( ¬ φ → ψ )", note="Imported")
    return lb.build(stmt)

def prove_pm2_43(sys: HilbertSystem) -> LemmaProof:
    """pm2.43: ( ph -> ( ph -> ps ) ) -> ( ph -> ps )."""
    lb = LemmaBuilder(sys, "pm2.43")
    stmt = lb.raw("res", "( φ → ( φ → ψ ) ) → ( φ → ψ )", note="Imported")
    return lb.build(stmt)

def prove_pm2_18(sys: HilbertSystem) -> LemmaProof:
    """pm2.18: ( -. ph -> ph ) -> ph."""
    lb = LemmaBuilder(sys, "pm2.18")
    stmt = lb.raw("res", "( ¬ φ → φ ) → φ", note="Imported")
    return lb.build(stmt)

def prove_mt2(sys: HilbertSystem) -> LemmaProof:
    """mt2: -. ph. Hyp1: ps, Hyp2: ph -> -. ps."""
    lb = LemmaBuilder(sys, "mt2")
    lb.hyp("hyp1", "ψ")
    lb.hyp("hyp2", "φ → ¬ ψ")
    stmt = lb.raw("res", "¬ φ", note="Imported")
    return lb.build(stmt)

def prove_mt3(sys: HilbertSystem) -> LemmaProof:
    """mt3: ph. Hyp1: -. ps, Hyp2: -. ph -> ps."""
    lb = LemmaBuilder(sys, "mt3")
    lb.hyp("hyp1", "¬ ψ")
    lb.hyp("hyp2", "¬ φ → ψ")
    stmt = lb.raw("res", "φ", note="Imported")
    return lb.build(stmt)

def prove_nsyl(sys: HilbertSystem) -> LemmaProof:
    """nsyl: ph -> -. ch. Hyp1: ph -> -. ps, Hyp2: ch -> ps."""
    lb = LemmaBuilder(sys, "nsyl")
    lb.hyp("hyp1", "φ → ¬ ψ")
    lb.hyp("hyp2", "χ → ψ")
    stmt = lb.raw("res", "φ → ¬ χ", note="Imported")
    return lb.build(stmt)

def prove_nsyl2(sys: HilbertSystem) -> LemmaProof:
    """nsyl2: ph -> ch. Hyp1: ph -> -. ps, Hyp2: -. ch -> ps."""
    lb = LemmaBuilder(sys, "nsyl2")
    lb.hyp("hyp1", "φ → ¬ ψ")
    lb.hyp("hyp2", "¬ χ → ψ")
    stmt = lb.raw("res", "φ → χ", note="Imported")
    return lb.build(stmt)

def prove_nsyl3(sys: HilbertSystem) -> LemmaProof:
    """nsyl3: ch -> -. ph. Hyp1: ph -> -. ps, Hyp2: ch -> ps."""
    lb = LemmaBuilder(sys, "nsyl3")
    lb.hyp("hyp1", "φ → ¬ ψ")
    lb.hyp("hyp2", "χ → ψ")
    stmt = lb.raw("res", "χ → ¬ φ", note="Imported")
    return lb.build(stmt)

def prove_pm2_61(sys: HilbertSystem) -> LemmaProof:
    """pm2.61: ( ph -> ps ) -> ( ( -. ph -> ps ) -> ps )."""
    lb = LemmaBuilder(sys, "pm2.61")
    stmt = lb.raw("res", "( φ → ψ ) → ( ( ¬ φ → ψ ) → ψ )", note="Imported")
    return lb.build(stmt)

def prove_pm2_65(sys: HilbertSystem) -> LemmaProof:
    """pm2.65: ( ph -> ps ) -> ( ( ph -> -. ps ) -> -. ph )."""
    lb = LemmaBuilder(sys, "pm2.65")
    stmt = lb.raw("res", "( φ → ψ ) → ( ( φ → ¬ ψ ) → ¬ φ )", note="Imported")
    return lb.build(stmt)

def prove_imim1(sys: HilbertSystem) -> LemmaProof:
    """imim1: ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) )."""
    lb = LemmaBuilder(sys, "imim1")
    stmt = lb.raw("res", "( φ → ψ ) → ( ( ψ → χ ) → ( φ → χ ) )", note="Imported")
    return lb.build(stmt)

def prove_imim2(sys: HilbertSystem) -> LemmaProof:
    """imim2: ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) )."""
    lb = LemmaBuilder(sys, "imim2")
    stmt = lb.raw("res", "( φ → ψ ) → ( ( χ → φ ) → ( χ → ψ ) )", note="Imported")
    return lb.build(stmt)

def prove_con1i(sys: HilbertSystem) -> LemmaProof:
    """con1i: -. ps -> ph. Hyp: -. ph -> ps."""
    lb = LemmaBuilder(sys, "con1i")
    lb.hyp("hyp", "¬ φ → ψ")
    stmt = lb.raw("res", "¬ ψ → φ", note="Imported")
    return lb.build(stmt)

def prove_con2i(sys: HilbertSystem) -> LemmaProof:
    """con2i: ps -> -. ph. Hyp: ph -> -. ps."""
    lb = LemmaBuilder(sys, "con2i")
    lb.hyp("hyp", "φ → ¬ ψ")
    stmt = lb.raw("res", "ψ → ¬ φ", note="Imported")
    return lb.build(stmt)

def prove_con3i(sys: HilbertSystem) -> LemmaProof:
    """con3i: -. ps -> -. ph. Hyp: ph -> ps."""
    lb = LemmaBuilder(sys, "con3i")
    lb.hyp("hyp", "φ → ψ")
    stmt = lb.raw("res", "¬ ψ → ¬ φ", note="Imported")
    return lb.build(stmt)

def prove_con4i(sys: HilbertSystem) -> LemmaProof:
    """con4i: ps -> ph. Hyp: -. ph -> -. ps."""
    lb = LemmaBuilder(sys, "con4i")
    lb.hyp("hyp", "¬ φ → ¬ ψ")
    stmt = lb.raw("res", "ψ → φ", note="Imported")
    return lb.build(stmt)


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
    "prove_L10_linearity",
    "prove_L3_or_intro_left",
    "prove_modus_tollens",
    "prove_a1i",
    "prove_a2i",
    "prove_mpd",
    "prove_syl",
    "prove_sylcom",
    "prove_com12",
    "prove_syl5",
    "prove_syl6",
    "prove_a1d",
    "prove_idd",
    "prove_a1i13",
    "prove_2a1d",
    "prove_2a1",
    "prove_a2d",
    "prove_syl5com",
    "prove_syl11",
    "prove_syl56",
    "prove_syl6com",
    "prove_mpcom",
    "prove_syli",
    "prove_syl2im",
    "prove_syl2imc",
    "prove_pm2_27",
    "prove_mpdd",
    "prove_mpid",
    "prove_con1",
    "prove_con2",
    "prove_con3",
    "prove_con4",
    "prove_pm2_21",
    "prove_pm2_24",
    "prove_pm2_43",
    "prove_pm2_18",
    "prove_mt2",
    "prove_mt3",
    "prove_nsyl",
    "prove_nsyl2",
    "prove_nsyl3",
    "prove_pm2_61",
    "prove_pm2_65",
    "prove_imim1",
    "prove_imim2",
    "prove_con1i",
    "prove_con2i",
    "prove_con3i",
    "prove_con4i",
    "debug_dump",
]
