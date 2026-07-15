from __future__ import annotations

from collections.abc import Callable, Mapping
from typing import TypeAlias

from skfd.authoring.parsing import wff
from skfd.proof import Proof, ProofBuilder, SystemCore

# Import predicate symbol builders so A. and other quantifier/equality symbols
# are registered in the global builder registry before the proof compiles.
from . import _structures  # noqa: F401

# Predicate theorem constructors depend on the proof-authoring protocol, not
# the concrete propositional Hilbert system. Keep the short annotation used by
# the generated constructors while enforcing that boundary.
System: TypeAlias = SystemCore
PredicateTheoremCtor = Callable[[SystemCore], Proof]


def _var(sys: System, name: str) -> object:
    """Resolve a bare variable name to this system's runtime SymbolId.

    DV pairs must be recorded with SymbolIds from the same interner as
    ``sys`` (they are not stable across processes), so this always
    re-resolves at call time rather than caching a literal id.
    """
    return sys.compile(wff(name), ctx="dv-lookup").tokens[0]


def prove_alim(sys: System) -> Proof:
    """alim: A. x ( φ → ψ ) → ( A. x φ → A. x ψ ).

    Axiom of quantifier distribution. The proof is a direct instantiation
    of ax-4 (ax-4).
    """

    lb = ProofBuilder(sys, "alim")
    res = lb.ref(
        "s1",
        "A. x ( φ → ψ ) → ( A. x φ → A. x ψ )",
        ref="ax-4",
        note="ax-4 — quantifier distribution",
    )
    return lb.build(res)


def prove_alimi(sys: System) -> Proof:
    """alimi: ( A. x φ → A. x ψ ).

    Inference form of alim. Generalize the hypothesis with ax-5,
    then apply alim for quantifier distribution.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wi wal alim mpg.
    """
    lb = ProofBuilder(sys, "alimi")
    hyp = lb.hyp("alimi.1", "φ → ψ")
    major = lb.ref("major", "A. x ( φ → ψ ) → ( A. x φ → A. x ψ )", ref="alim")
    res = lb.ref("res", "A. x φ → A. x ψ", major, hyp, ref="mpg", note="mpg alim, alimi.1")
    return lb.build(res)


def prove_2alimi(sys: System) -> Proof:
    """2alimi: ( A. x A. y φ → A. x A. y ψ ).

    Apply alimi twice: first with y, then with x.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wal alimi.
    """
    lb = ProofBuilder(sys, "2alimi")
    hyp = lb.hyp("alimi.1", "φ → ψ")
    # alimi with variable y: (A. y ph -> A. y ps)
    s1 = lb.ref(
        "s1",
        "A. y φ → A. y ψ",
        hyp,
        ref="alimi",
        note="alimi with y",
    )
    # alimi with variable x: (A. x A. y ph -> A. x A. y ps)
    res = lb.ref(
        "res",
        "A. x A. y φ → A. x A. y ψ",
        s1,
        ref="alimi",
        note="alimi with x",
    )
    return lb.build(res)


def prove_al2im(sys: System) -> Proof:
    """al2im: A. x ( φ → ( ψ → χ ) ) → ( A. x φ → ( A. x ψ → A. x χ ) ).

    Universal quantifier distributes over nested implication.
    (Contributed by NM, 31-Dec-1993.)
    set.mm proof: alim syl6.
    """
    lb = ProofBuilder(sys, "al2im")
    s1 = lb.ref(
        "s1",
        "A. x ( φ → ( ψ → χ ) ) → ( A. x φ → A. x ( ψ → χ ) )",
        ref="alim",
        note="alim with ps := (ps -> ch)",
    )
    s2 = lb.ref(
        "s2",
        "A. x ( ψ → χ ) → ( A. x ψ → A. x χ )",
        ref="alim",
        note="alim with ph := ps",
    )
    res = lb.ref(
        "res",
        "A. x ( φ → ( ψ → χ ) ) → ( A. x φ → ( A. x ψ → A. x χ ) )",
        s1,
        s2,
        ref="syl6",
        note="syl6 s1, s2",
    )
    return lb.build(res)


def prove_al2imi(sys: System) -> Proof:
    """al2imi: ( A. x φ → ( A. x ψ → A. x χ ) ).

    Inference form of al2im. Generalize the hypothesis with ax-5,
    then apply al2im.
    (Contributed by NM, 31-Dec-1993.)
    set.mm proof: wi wal al2im mpg.
    """
    lb = ProofBuilder(sys, "al2imi")
    hyp = lb.hyp("al2imi.1", "φ → ( ψ → χ )")
    major = lb.ref(
        "major",
        "A. x ( φ → ( ψ → χ ) ) → ( A. x φ → ( A. x ψ → A. x χ ) )",
        ref="al2im",
        note="al2im",
    )
    res = lb.ref("res", "A. x φ → ( A. x ψ → A. x χ )", major, hyp, ref="mpg")
    return lb.build(res)


def prove_alanimi(sys: System) -> Proof:
    """alanimi: ( ( A. x φ ∧ A. x ψ ) → A. x χ ).

    Inference combining al2imi with conjunction export/import.
    Uses ex to export the conjunction hypothesis, al2imi to
    distribute the quantifier, and imp to import back.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wal ex al2imi imp.
    """
    lb = ProofBuilder(sys, "alanimi")
    hyp = lb.hyp("alanimi.1", "( φ ∧ ψ ) → χ")
    # ex: ( ( φ ∧ ψ ) → χ ) → ( φ → ( ψ → χ ) )
    s1 = lb.ref("s1", "φ → ( ψ → χ )", hyp, ref="ex", note="ex alanimi.1")
    # al2imi: ( φ → ( ψ → χ ) ) ⊢ ( A. x φ → ( A. x ψ → A. x χ ) )
    s2 = lb.ref(
        "s2",
        "A. x φ → ( A. x ψ → A. x χ )",
        s1,
        ref="al2imi",
        note="al2imi s1",
    )
    # imp: ( A. x φ → ( A. x ψ → A. x χ ) ) → ( ( A. x φ ∧ A. x ψ ) → A. x χ )
    res = lb.ref(
        "res",
        "( ( A. x φ ∧ A. x ψ ) → A. x χ )",
        s2,
        ref="imp",
        note="imp s2",
    )
    return lb.build(res)


def prove_alimdh(sys: System) -> Proof:
    """alimdh: φ → ( A. x ψ → A. x χ ).

    Deduction form of alim. Uses al2imi to distribute the quantifier
    over the nested implication in the second hypothesis, then chains
    with the first hypothesis via syl.
    (Contributed by NM, 31-Dec-1993.)
    set.mm proof: wal wi al2imi syl.
    """
    lb = ProofBuilder(sys, "alimdh")
    hyp1 = lb.hyp("alimdh.1", "φ → ∀ x φ")
    hyp2 = lb.hyp("alimdh.2", "φ → ( ψ → χ )")
    # al2imi: (φ → (ψ → χ)) ⊢ (A.x φ → (A.x ψ → A.x χ))
    s1 = lb.ref(
        "s1",
        "A. x φ → ( A. x ψ → A. x χ )",
        hyp2,
        ref="al2imi",
        note="al2imi alimdh.2",
    )
    # syl: (φ → A.x φ), (A.x φ → (A.x ψ → A.x χ)) ⊢ (φ → (A.x ψ → A.x χ))
    res = lb.ref(
        "res",
        "φ → ( A. x ψ → A. x χ )",
        hyp1,
        s1,
        ref="syl",
        note="syl alimdh.1, al2imi",
    )
    return lb.build(res)


def prove_alimdv(sys: System) -> Proof:
    """alimdv: ph → ( A. x ps → A. x ch ).

    Deduction form of alim using ax-5. Uses ax-5 to obtain ph → A. x ph,
    then alimdh with alimdv.1 to derive the conclusion.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: ax-5 alimdh.
    """
    lb = ProofBuilder(sys, "alimdv")
    hyp = lb.hyp("alimdv.1", "ph → ( ps → ch )")
    # ax-5: ph → A. x ph
    s1 = lb.ref("s1", "ph → A. x ph", ref="ax-5", note="ax-5 — ax-5")
    # alimdh: (ph → A. x ph), (ph → (ps → ch)) ⊢ (ph → (A. x ps → A. x ch))
    res = lb.ref(
        "res",
        "ph → ( A. x ps → A. x ch )",
        s1,
        hyp,
        ref="alimdh",
        note="alimdh ax-5, alimdv.1",
    )
    return lb.build(res)


def prove_2alimdv(sys: System) -> Proof:
    """2alimdv: ph → ( A. x A. y ps → A. x A. y ch ).

    Deduction form of 2alimi. Apply alimdv twice: first with y, then with x.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wal alimdv.
    """
    lb = ProofBuilder(sys, "2alimdv")
    hyp = lb.hyp("2alimdv.1", "ph → ( ps → ch )")
    # alimdv with y: ph → (A. y ps → A. y ch)
    s1 = lb.ref(
        "s1",
        "ph → ( A. y ps → A. y ch )",
        hyp,
        ref="alimdv",
        note="alimdv with y",
    )
    # alimdv with x: ph → (A. x A. y ps → A. x A. y ch)
    res = lb.ref(
        "res",
        "ph → ( A. x A. y ps → A. x A. y ch )",
        s1,
        ref="alimdv",
        note="alimdv with x",
    )
    return lb.build(res)


def prove_alrimdh(sys: System) -> Proof:
    """alrimdh: φ → ( ψ → A. x χ ).

    Deduction form combining alimdh and syl5. Uses alrimdh.1 and
    alrimdh.3 as inputs to alimdh, then chains with alrimdh.2 via syl5.
    (Contributed by NM, 31-Dec-1993.)
    set.mm proof: wal alimdh syl5.
    """
    lb = ProofBuilder(sys, "alrimdh")
    hyp1 = lb.hyp("alrimdh.1", "φ → ∀ x φ")
    hyp2 = lb.hyp("alrimdh.2", "ψ → A. x ψ")
    hyp3 = lb.hyp("alrimdh.3", "φ → ( ψ → χ )")
    # alimdh alrimdh.1, alrimdh.3: φ → (A. x ψ → A. x χ)
    s1 = lb.ref(
        "s1",
        "φ → ( A. x ψ → A. x χ )",
        hyp1,
        hyp3,
        ref="alimdh",
        note="alimdh alrimdh.1, alrimdh.3",
    )
    # syl5 alrimdh.2, s1: φ → ( ψ → A. x χ )
    res = lb.ref(
        "res",
        "φ → ( ψ → A. x χ )",
        hyp2,
        s1,
        ref="syl5",
        note="syl5 alrimdh.2, alimdh",
    )
    return lb.build(res)


def prove_alrimdv(sys: System) -> Proof:
    """alrimdv: φ → ( ψ → A. x χ ).

    Deduction form of alrimdh using ax-5 (ax-5) for the distinct variable
    conditions on phi and psi.
    (Contributed by NM, 31-Dec-1993.)
    set.mm proof: ax-5 alrimdh.
    """
    lb = ProofBuilder(sys, "alrimdv")
    hyp = lb.hyp("alrimdv.1", "φ → ( ψ → χ )")
    # ax-5: φ → A. x φ (valid when x is not free in φ)
    s1 = lb.ref("s1", "φ → ∀ x φ", ref="ax-5", note="ax-5")
    # ax-5: ψ → A. x ψ (valid when x is not free in ψ)
    s2 = lb.ref("s2", "ψ → A. x ψ", ref="ax-5", note="ax-5")
    # alrimdh: (φ → A.x φ), (ψ → A.x ψ), (φ → (ψ → χ)) ⊢ φ → (ψ → A.x χ)
    res = lb.ref(
        "res",
        "φ → ( ψ → A. x χ )",
        s1,
        s2,
        hyp,
        ref="alrimdh",
        note="alrimdh",
    )
    return lb.build(res)


def prove_hbn1(sys: System) -> Proof:
    """hbn1: ¬ A. x φ → A. x ¬ A. x φ.

    Axiom of quantifier commutation. The proof is a direct instantiation
    of ax-10 (ax-10).
    """
    lb = ProofBuilder(sys, "hbn1")
    res = lb.ref(
        "s1",
        "¬ A. x φ → A. x ¬ A. x φ",
        ref="ax-10",
        note="ax-10 — ax-10",
    )
    return lb.build(res)


def prove_modal5(sys: System) -> Proof:
    """modal5: ¬ ∀ x ¬ φ → ∀ x ¬ ∀ x ¬ φ.

    Modal law. The proof is a direct instantiation of hbn1
    with ¬ φ substituted for φ.
    """
    lb = ProofBuilder(sys, "modal5")
    res = lb.ref(
        "s1",
        "¬ ∀ x ¬ φ → ∀ x ¬ ∀ x ¬ φ",
        ref="hbn1",
        note="hbn1",
    )
    return lb.build(res)


def prove_hbn1fw(sys: System) -> Proof:
    """hbn1fw: ¬ ∀ x φ → ∀ x ¬ ∀ x φ.

    Free-variable version of hbn1.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: cbvalw notbii hbxfrbi.
    """
    lb = ProofBuilder(sys, "hbn1fw")
    hyp1 = lb.hyp("hbn1fw.1", "∀ x φ → ∀ y ∀ x φ")
    hyp2 = lb.hyp("hbn1fw.2", "¬ ψ → ∀ x ¬ ψ")
    hyp3 = lb.hyp("hbn1fw.3", "∀ y ψ → ∀ x ∀ y ψ")
    hyp4 = lb.hyp("hbn1fw.4", "¬ φ → ∀ y ¬ φ")
    hyp5 = lb.hyp("hbn1fw.5", "¬ ∀ y ψ → ∀ x ¬ ∀ y ψ")
    hyp6 = lb.hyp("hbn1fw.6", "x = y → ( φ ↔ ψ )")
    # cbvalw: ( ∀ x φ ↔ ∀ y ψ )
    s1 = lb.ref(
        "s1",
        "( ∀ x φ ↔ ∀ y ψ )",
        hyp1,
        hyp2,
        hyp3,
        hyp4,
        hyp6,
        ref="cbvalw",
        note="cbvalw",
    )
    # notbii: ( ¬ ∀ x φ ↔ ¬ ∀ y ψ )
    s2 = lb.ref(
        "s2",
        "( ¬ ∀ x φ ↔ ¬ ∀ y ψ )",
        s1,
        ref="notbii",
        note="notbii",
    )
    # hbxfrbi: ( ¬ ∀ x φ → ∀ x ¬ ∀ x φ )
    res = lb.ref(
        "res",
        "¬ ∀ x φ → ∀ x ¬ ∀ x φ",
        s2,
        hyp5,
        ref="hbxfrbi",
        note="hbxfrbi",
    )
    return lb.build(res)


def prove_hbn1w(sys: System) -> Proof:
    """hbn1w: ¬ ∀ x φ → ∀ x ¬ ∀ x φ.

    Weak version of hbn1. Direct instantiation of ax-10 (ax-10).
    """
    lb = ProofBuilder(sys, "hbn1w")
    lb.hyp("hbn1w.1", "x = y → ( φ ↔ ψ )")
    res = lb.ref(
        "s1",
        "¬ ∀ x φ → ∀ x ¬ ∀ x φ",
        ref="ax-10",
        note="ax-10 — ax-10",
    )
    return lb.build(res)


def prove_hba1w(sys: System) -> Proof:
    """hba1w: ∀ x φ → ∀ x ∀ x φ.

    Weak version of hba1. Uses only Tarski's FOL axiom schemes.
    (Contributed by NM, 9-Apr-2017.)
    (Proof shortened by Wolf Lammen, 10-Oct-2021.)
    """
    lb = ProofBuilder(sys, "hba1w")
    hyp = lb.hyp("hbn1w.1", "x = y → ( φ ↔ ψ )")
    # cbvalvw: (∀x φ ↔ ∀y ψ) from hbn1w.1
    s2 = lb.ref(
        "s2",
        "( ∀ x φ ↔ ∀ y ψ )",
        hyp,
        ref="cbvalvw",
        note="cbvalvw",
    )
    # notbii: (¬∀x φ ↔ ¬∀y ψ)
    s3 = lb.ref(
        "s3",
        "( ¬ ∀ x φ ↔ ¬ ∀ y ψ )",
        s2,
        ref="notbii",
        note="notbii",
    )
    # a1i: x = y → (¬∀x φ ↔ ¬∀y ψ)
    s4 = lb.ref(
        "s4",
        "x = y → ( ¬ ∀ x φ ↔ ¬ ∀ y ψ )",
        s3,
        ref="a1i",
        note="a1i",
    )
    # spw: ∀x ¬∀x φ → ¬∀x φ
    s5 = lb.ref(
        "s5",
        "∀ x ¬ ∀ x φ → ¬ ∀ x φ",
        s4,
        ref="spw",
        note="spw",
    )
    # con2i: ∀x φ → ¬∀x ¬∀x φ
    s6 = lb.ref(
        "s6",
        "∀ x φ → ¬ ∀ x ¬ ∀ x φ",
        s5,
        ref="con2i",
        note="con2i",
    )
    # hbn1w: ¬∀x ¬∀x φ → ∀x ¬∀x ¬∀x φ
    s8 = lb.ref(
        "s8",
        "¬ ∀ x ¬ ∀ x φ → ∀ x ¬ ∀ x ¬ ∀ x φ",
        s4,
        ref="hbn1w",
        note="hbn1w",
    )
    # hbn1w: ¬∀x φ → ∀x ¬∀x φ
    s10 = lb.ref(
        "s10",
        "¬ ∀ x φ → ∀ x ¬ ∀ x φ",
        hyp,
        ref="hbn1w",
        note="hbn1w",
    )
    # con1i: ¬∀x ¬∀x φ → ∀x φ
    s11 = lb.ref(
        "s11",
        "¬ ∀ x ¬ ∀ x φ → ∀ x φ",
        s10,
        ref="con1i",
        note="con1i",
    )
    # alimi: ∀x ¬∀x ¬∀x φ → ∀x ∀x φ
    s12 = lb.ref(
        "s12",
        "∀ x ¬ ∀ x ¬ ∀ x φ → ∀ x ∀ x φ",
        s11,
        ref="alimi",
        note="alimi",
    )
    # 3syl: (∀x φ → ∀x ∀x φ)
    res = lb.ref(
        "res",
        "∀ x φ → ∀ x ∀ x φ",
        s6,
        s8,
        s12,
        ref="3syl",
        note="3syl",
    )
    return lb.build(res)


def prove_ax10w(sys: System) -> Proof:
    """ax10w: ¬ ∀ x φ → ∀ x ¬ ∀ x φ.

    Weak version of ax-10, derived from hbn1w.
    """
    lb = ProofBuilder(sys, "ax10w")
    hyp = lb.hyp("ax10w.1", "x = y → ( φ ↔ ψ )")
    res = lb.ref(
        "s1",
        "¬ ∀ x φ → ∀ x ¬ ∀ x φ",
        hyp,
        ref="hbn1w",
        note="hbn1w — ax10w is a label variant of hbn1w",
    )
    return lb.build(res)


def prove_ax6v(sys: System) -> Proof:
    """ax6v: ¬ ∀ x ¬ x = y.

    Distinctor elimination. The proof is a direct instantiation
    of ax-6 (ax-6).
    """
    lb = ProofBuilder(sys, "ax6v")
    lb.disjoint(_var(sys, "x"), _var(sys, "y"))
    res = lb.ref(
        "s1",
        "¬ ∀ x ¬ x = y",
        ref="ax-6",
        note="ax-6 — ax-6",
    )
    return lb.build(res)


def prove_ax6ev(sys: System) -> Proof:
    """ax6ev: E. x x = y.

    There exists a set equal to another (existential introduction
    from ax6v). Uses df-ex to convert the universal statement.
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "ax6ev")
    lb.disjoint(_var(sys, "x"), _var(sys, "y"))
    # df-ex with ph := x = y: ( E. x x = y <-> ¬ A. x ¬ x = y )
    s1 = lb.ref(
        "s1",
        "E. x x = y ↔ ¬ A. x ¬ x = y",
        ref="df-ex",
        note="df-ex",
    )
    # ax6v: ¬ A. x ¬ x = y
    s2 = lb.ref(
        "s2",
        "¬ A. x ¬ x = y",
        ref="ax6v",
        note="ax6v",
    )
    # mpbir: from biconditional and RHS, conclude E. x x = y
    res = lb.ref(
        "res",
        "E. x x = y",
        s2,
        s1,
        ref="mpbir",
        note="mpbir df-ex, ax6v",
    )
    return lb.build(res)


def prove_ax6dgen(sys: System) -> Proof:
    """ax6dgen: ¬ ∀ x ¬ x = x.

    Variant of ~ax6v with the same variable (x in place of y).
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "ax6dgen")
    # equid: x = x
    s1 = lb.ref("s1", "x = x", ref="equid", note="equid")
    # notnoti: from x = x, derive ¬ ¬ x = x
    s2 = lb.ref("s2", "¬ ¬ x = x", s1, ref="notnoti", note="notnoti")
    # spfalw with φ := ¬ x = x, hyp = ¬ ¬ x = x: ∀ x ¬ x = x → ¬ x = x
    s3 = lb.ref("s3", "∀ x ¬ x = x → ¬ x = x", s2, ref="spfalw", note="spfalw")
    # mt2 with ψ = x = x, φ → ¬ψ = s3: ¬ ∀ x ¬ x = x
    res = lb.ref("res", "¬ ∀ x ¬ x = x", s1, s3, ref="mt2", note="mt2")
    return lb.build(res)


def prove_ax7v(sys: System) -> Proof:
    """ax7v: x = y → ( x = z → y = z ).

    Equality transitivity. The proof is a direct instantiation
    of ax-7 (ax-7).
    """
    lb = ProofBuilder(sys, "ax7v")
    lb.disjoint(_var(sys, "x"), _var(sys, "y"))
    res = lb.ref(
        "s1",
        "x = y → ( x = z → y = z )",
        ref="ax-7",
        note="ax-7 — ax-7",
    )
    return lb.build(res)


def prove_ax7v1(sys: System) -> Proof:
    """ax7v1: x = y → ( x = z → y = z ).

    Equality transitivity. Same as ax7v; the proof is a direct
    reference to ax7v.
    """
    lb = ProofBuilder(sys, "ax7v1")
    res = lb.ref(
        "s1",
        "x = y → ( x = z → y = z )",
        ref="ax7v",
        note="ax7v",
    )
    return lb.build(res)


def prove_ax7v2(sys: System) -> Proof:
    """ax7v2: x = y → ( x = z → y = z ).

    Equality transitivity. Same as ax7v; the proof is a direct
    reference to ax7v.
    """
    lb = ProofBuilder(sys, "ax7v2")
    res = lb.ref(
        "s1",
        "x = y → ( x = z → y = z )",
        ref="ax7v",
        note="ax7v",
    )
    return lb.build(res)


def prove_ax7(sys: System) -> Proof:
    """ax7: x = y → ( x = z → y = z ).

    Equality transitivity.  Uses a dummy variable t to handle the
    weakened distinct variable condition (only x,y must be distinct).
    From ax7v2 and ax7v1 via syl2and, then exlimiiv and ex.
    (Contributed by NM, 10-Jan-1993.)
    set.mm proof: weq wa wi ax7v2 ax7v1 imp a1i syl2and ax6evr exlimiiv ex.
    """
    lb = ProofBuilder(sys, "ax7")
    # ax7v2 with x:=x, y:=t, z:=y  →  x = t → ( x = y → t = y )
    s32 = lb.ref(
        "s32",
        "x = t → ( x = y → t = y )",
        ref="ax7v2",
        note="ax7v2 with y:=t, z:=y",
    )
    # ax7v2 with x:=x, y:=t, z:=z  →  x = t → ( x = z → t = z )
    s36 = lb.ref(
        "s36",
        "x = t → ( x = z → t = z )",
        ref="ax7v2",
        note="ax7v2 with y:=t, z:=z",
    )
    # ax7v1 with x:=t, y:=y, z:=z  →  t = y → ( t = z → y = z )
    s49 = lb.ref(
        "s49",
        "t = y → ( t = z → y = z )",
        ref="ax7v1",
        note="ax7v1 with x:=t",
    )
    # imp: ( t = y → ( t = z → y = z ) ) ⊢ ( ( t = y ∧ t = z ) → y = z )
    s50 = lb.ref(
        "s50",
        "( t = y ∧ t = z ) → y = z",
        s49,
        ref="imp",
        note="imp",
    )
    # a1i: ( ( t = y ∧ t = z ) → y = z ) ⊢ x = t → ( ( t = y ∧ t = z ) → y = z )
    s51 = lb.ref(
        "s51",
        "x = t → ( ( t = y ∧ t = z ) → y = z )",
        s50,
        ref="a1i",
        note="a1i",
    )
    # syl2and: from s32, s36, s51  →  x = t → ( ( x = y ∧ x = z ) → y = z )
    s52 = lb.ref(
        "s52",
        "x = t → ( ( x = y ∧ x = z ) → y = z )",
        s32,
        s36,
        s51,
        ref="syl2and",
        note="syl2and",
    )
    # ax6evr: ∃ t x = t
    s55 = lb.ref(
        "s55",
        "∃ t x = t",
        ref="ax6evr",
        note="ax6evr",
    )
    # exlimiiv: ( x = t → ( ... ) ), ∃ t x = t  ⊢  ( x = y ∧ x = z ) → y = z
    s56 = lb.ref(
        "s56",
        "( x = y ∧ x = z ) → y = z",
        s52,
        s55,
        ref="exlimiiv",
        note="exlimiiv",
    )
    # ex: ( ( x = y ∧ x = z ) → y = z ) ⊢ x = y → ( x = z → y = z )
    res = lb.ref(
        "res",
        "x = y → ( x = z → y = z )",
        s56,
        ref="ex",
        note="ex",
    )
    return lb.build(res)


def prove_equtr(sys: System) -> Proof:
    """equtr: x = y → ( y = z → x = z ).

    Equality transitivity, derived from ax7 and equcoms.
    (Contributed by NM, 10-Jan-1993.)
    set.mm proof: weq wi ax7 equcoms.
    """
    lb = ProofBuilder(sys, "equtr")
    s1 = lb.ref(
        "s1",
        "x = y → ( x = z → y = z )",
        ref="ax7",
        note="ax7",
    )
    res = lb.ref(
        "res",
        "y = x → ( x = z → y = z )",
        s1,
        ref="equcoms",
        note="equcoms ax7",
    )
    return lb.build(res)


def prove_equtrr(sys: System) -> Proof:
    """equtrr: x = y → ( z = x → z = y ).

    Equality transitivity, reversed antecedent order.
    From equtr with x:=z, y:=x, z:=y, then com12 swaps the antecedents.
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: weq equtr com12.
    """
    lb = ProofBuilder(sys, "equtrr")
    # equtr with x:=z, y:=x, z:=y: z = x → ( x = y → z = y )
    s1 = lb.ref(
        "s1",
        "z = x → ( x = y → z = y )",
        ref="equtr",
        note="equtr with x:=z, y:=x, z:=y",
    )
    # com12 swaps the antecedents: x = y → ( z = x → z = y )
    res = lb.ref(
        "res",
        "x = y → ( z = x → z = y )",
        s1,
        ref="com12",
        note="com12",
    )
    return lb.build(res)


def prove_equequ1(sys: System) -> Proof:
    """equequ1: x = y → ( x = z ↔ y = z ).

    Equality substitution into an equality, forward direction.
    From ax7 and equtr via impbid.
    (Contributed by NM, 10-Jan-1993.)
    set.mm proof: weq ax7 equtr impbid.
    """
    lb = ProofBuilder(sys, "equequ1")
    # ax7: x = y → ( x = z → y = z )
    s_ax7 = lb.ref(
        "s_ax7",
        "x = y → ( x = z → y = z )",
        ref="ax7",
        note="ax7",
    )
    # equtr: x = y → ( y = z → x = z )
    s_equtr = lb.ref(
        "s_equtr",
        "x = y → ( y = z → x = z )",
        ref="equtr",
        note="equtr",
    )
    # impbid combines both directions into a biconditional
    res = lb.ref(
        "res",
        "x = y → ( x = z ↔ y = z )",
        s_ax7,
        s_equtr,
        ref="impbid",
        note="impbid ax7, equtr",
    )
    return lb.build(res)


def prove_equequ2(sys: System) -> Proof:
    """equequ2: x = y → ( z = x ↔ z = y ).

    Equality substitution into an equality, reverse direction.
    From equtrr and equeuclr via impbid.
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: weq equtrr equeuclr impbid.
    """
    lb = ProofBuilder(sys, "equequ2")

    # equtrr: x = y → ( z = x → z = y )
    s1 = lb.ref(
        "s1",
        "x = y → ( z = x → z = y )",
        ref="equtrr",
        note="equtrr",
    )

    # equeuclr with substitution x→x, y→z, z→y:
    # equeuclr: x = z → ( y = z → y = x )
    # becomes:  x = y → ( z = y → z = x )
    s2 = lb.ref(
        "s2",
        "x = y → ( z = y → z = x )",
        ref="equeuclr",
        note="equeuclr with y:=z, z:=y",
    )

    # impbid: from the two implications, derive the biconditional
    res = lb.ref(
        "res",
        "x = y → ( z = x ↔ z = y )",
        s1,
        s2,
        ref="impbid",
        note="impbid equtrr, equeuclr",
    )

    return lb.build(res)


def prove_equid(sys: System) -> Proof:
    """equid: x = x.

    Equality is reflexive.  From ax7v1 with z set to x,
    pm2.43i gives y = x → x = x; with ax6ev and exlimiiv
    the distinct variable y is eliminated.
    (Contributed by NM, 10-Jan-1993.)
    set.mm proof: weq ax7v1 pm2.43i ax6ev exlimiiv.
    """
    lb = ProofBuilder(sys, "equid")
    # ax7v1 with z := x: y = x → (y = x → x = x)
    s1 = lb.ref(
        "s1",
        "y = x → ( y = x → x = x )",
        ref="ax7v1",
        note="ax7v1 with z := x",
    )
    # pm2.43i: y = x → x = x
    s2 = lb.ref(
        "s2",
        "y = x → x = x",
        s1,
        ref="pm2.43i",
        note="pm2.43i",
    )
    # ax6ev: ∃ y y = x
    s3 = lb.ref(
        "s3",
        "∃ y y = x",
        ref="ax6ev",
        note="ax6ev",
    )
    # exlimiiv: from (y = x → x = x) and ∃ y (y = x), conclude x = x
    res = lb.ref(
        "res",
        "x = x",
        s2,
        s3,
        ref="exlimiiv",
        note="exlimiiv",
    )
    return lb.build(res)


def prove_equvinva(sys: System) -> Proof:
    """equvinva: x = y → ∃ z ( x = z ∧ y = z ).

    There exists a variable such that both are equal to it.
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "equvinva")

    # equtr: x = y → ( y = z → x = z )
    s1 = lb.ref(
        "s1",
        "x = y → ( y = z → x = z )",
        ref="equtr",
        note="equtr",
    )
    # ancrd: ( x = y → ( y = z → x = z ) ) → ( x = y → ( y = z → ( x = z ∧ y = z ) ) )
    s2 = lb.ref(
        "s2",
        "x = y → ( y = z → ( x = z ∧ y = z ) )",
        s1,
        ref="ancrd",
        note="ancrd equtr",
    )
    # eximdv: ( x = y → ( y = z → ( x = z ∧ y = z ) ) ) → ( x = y → ( ∃ z y = z → ∃ z ( x = z ∧ y = z ) ) )
    s3 = lb.ref(
        "s3",
        "x = y → ( ∃ z y = z → ∃ z ( x = z ∧ y = z ) )",
        s2,
        ref="eximdv",
        note="eximdv ancrd",
    )
    # ax6evr: ∃ z y = z
    s4 = lb.ref(
        "s4",
        "∃ z y = z",
        ref="ax6evr",
        note="ax6evr",
    )
    # mpi: from ax6evr and eximdv, get x = y → ∃ z ( x = z ∧ y = z )
    res = lb.ref(
        "res",
        "x = y → ∃ z ( x = z ∧ y = z )",
        s4,
        s3,
        ref="mpi",
        note="mpi ax6evr, eximdv",
    )

    return lb.build(res)


def prove_equvinv(sys: System) -> Proof:
    """equvinv: x = y ↔ ∃ z ( z = x ∧ z = y ).

    Equality expressed in terms of an existentially quantified
    conjunction.  (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "equvinv")

    # equequ1: z = x → ( z = y ↔ x = y )
    s1 = lb.ref(
        "s1",
        "z = x → ( z = y ↔ x = y )",
        ref="equequ1",
        note="equequ1",
    )
    # equsexvw: ∃ z ( z = x ∧ z = y ) ↔ x = y
    s2 = lb.ref(
        "s2",
        "∃ z ( z = x ∧ z = y ) ↔ x = y",
        s1,
        ref="equsexvw",
        note="equsexvw equequ1",
    )
    # bicomi: x = y ↔ ∃ z ( z = x ∧ z = y )
    res = lb.ref(
        "res",
        "x = y ↔ ∃ z ( z = x ∧ z = y )",
        s2,
        ref="bicomi",
        note="bicomi",
    )
    return lb.build(res)


def prove_equcomiv(sys: System) -> Proof:
    """equcomiv: x = y → y = x.

    Equality is commutative.  From equid and ax7v2 via mpi.
    (Contributed by NM, 10-Jan-1993.)
    set.mm proof: weq equid ax7v2 mpi.
    """
    lb = ProofBuilder(sys, "equcomiv")
    # equid: x = x
    s1 = lb.ref(
        "s1",
        "x = x",
        ref="equid",
        note="equid",
    )
    # ax7v2 with z := x: x = y → (x = x → y = x)
    s2 = lb.ref(
        "s2",
        "x = y → ( x = x → y = x )",
        ref="ax7v2",
        note="ax7v2 with z := x",
    )
    # mpi: (x = x), (x = y → (x = x → y = x)) ⊢ x = y → y = x
    res = lb.ref(
        "res",
        "x = y → y = x",
        s1,
        s2,
        ref="mpi",
        note="mpi equid, ax7v2",
    )
    return lb.build(res)


def prove_equcomi(sys: System) -> Proof:
    """equcomi: x = y → y = x.

    Equality is commutative.  From equid and ax7 via mpi.
    (Contributed by NM, 10-Jan-1993.)
    set.mm proof: weq equid ax7 mpi.
    """
    lb = ProofBuilder(sys, "equcomi")
    # equid: x = x
    s1 = lb.ref(
        "s1",
        "x = x",
        ref="equid",
        note="equid",
    )
    # ax7 with z := x: x = y → (x = x → y = x)
    s2 = lb.ref(
        "s2",
        "x = y → ( x = x → y = x )",
        ref="ax7",
        note="ax7 with z := x",
    )
    # mpi: (x = x), (x = y → (x = x → y = x)) ⊢ x = y → y = x
    res = lb.ref(
        "res",
        "x = y → y = x",
        s1,
        s2,
        ref="mpi",
        note="mpi equid, ax7",
    )
    return lb.build(res)


def prove_equcom(sys: System) -> Proof:
    """equcom: ( x = y ↔ y = x ).

    Equality is symmetric as a biconditional.  From equcomi and impbii.
    (Contributed by NM, 10-Jan-1993.)
    set.mm proof: weq equcomi impbii.
    """
    lb = ProofBuilder(sys, "equcom")
    # equcomi: x = y → y = x
    s1 = lb.ref(
        "s1",
        "x = y → y = x",
        ref="equcomi",
        note="equcomi",
    )
    # equcomi with x,y swapped: y = x → x = y
    s2 = lb.ref(
        "s2",
        "y = x → x = y",
        ref="equcomi",
        note="equcomi with x,y swapped",
    )
    # impbii: combine both directions into biconditional
    res = lb.ref(
        "res",
        "( x = y ↔ y = x )",
        s1,
        s2,
        ref="impbii",
        note="impbii",
    )
    return lb.build(res)


def prove_equcomd(sys: System) -> Proof:
    """equcomd: φ → y = x.

    Deduction form of equcom. From equcomd.1 and equcom via sylib.
    (Contributed by NM, 10-Jan-1993.)
    set.mm proof: weq equcom sylib.
    """
    lb = ProofBuilder(sys, "equcomd")
    hyp = lb.hyp("equcomd.1", "φ → x = y")
    # equcom: x = y ↔ y = x
    s1 = lb.ref(
        "s1",
        "x = y ↔ y = x",
        ref="equcom",
        note="equcom",
    )
    # sylib: (φ → x = y), (x = y ↔ y = x) ⊢ (φ → y = x)
    res = lb.ref(
        "res",
        "φ → y = x",
        hyp,
        s1,
        ref="sylib",
        note="sylib equcomd.1, equcom",
    )
    return lb.build(res)


def prove_ax8v(sys: System) -> Proof:
    """ax8v: x = y → ( x e. z → y e. z ).

    Equality substitution in membership. The proof is a direct instantiation
    of ax-8 (ax-8).
    """
    lb = ProofBuilder(sys, "ax8v")
    lb.disjoint(_var(sys, "x"), _var(sys, "y"))
    res = lb.ref(
        "s1",
        "x = y → ( x e. z → y e. z )",
        ref="ax-8",
        note="ax-8 — ax-8",
    )
    return lb.build(res)


def prove_ax8v1(sys: System) -> Proof:
    """ax8v1: x = y → ( x e. z → y e. z ).

    Same as ax8v; the proof is a direct reference to ax8v.
    """
    lb = ProofBuilder(sys, "ax8v1")
    res = lb.ref(
        "s1",
        "x = y → ( x e. z → y e. z )",
        ref="ax8v",
        note="ax8v",
    )
    return lb.build(res)


def prove_ax8v2(sys: System) -> Proof:
    """ax8v2: x = y → ( x e. z → y e. z ).

    Same as ax8v; the proof is a direct reference to ax8v.
    """
    lb = ProofBuilder(sys, "ax8v2")
    res = lb.ref(
        "s1",
        "x = y → ( x e. z → y e. z )",
        ref="ax8v",
        note="ax8v",
    )
    return lb.build(res)


def prove_ax8(sys: System) -> Proof:
    """ax8: x = y → ( x ∈ z → y ∈ z ).

    Equality implies membership substitution.  Derived from ax8v1 and ax8v2.
    (Contributed by BJ, 7-Dec-2020.)
    (Proof shortened by Wolf Lammen, 11-Apr-2021.)
    """
    lb = ProofBuilder(sys, "ax8")

    # equvinv with t for z: x = y ↔ ∃ t ( t = x ∧ t = y )
    s1 = lb.ref(
        "s1",
        "x = y ↔ ∃ t ( t = x ∧ t = y )",
        ref="equvinv",
        note="equvinv",
    )

    # ax8v2 with x:=x, y:=t: x = t → ( x ∈ z → t ∈ z )
    s2 = lb.ref(
        "s2",
        "x = t → ( x ∈ z → t ∈ z )",
        ref="ax8v2",
        note="ax8v2",
    )

    # equcoms s2: t = x → ( x ∈ z → t ∈ z )
    s3 = lb.ref(
        "s3",
        "t = x → ( x ∈ z → t ∈ z )",
        s2,
        ref="equcoms",
        note="equcoms",
    )

    # ax8v1 with x:=t, y:=y: t = y → ( t ∈ z → y ∈ z )
    s4 = lb.ref(
        "s4",
        "t = y → ( t ∈ z → y ∈ z )",
        ref="ax8v1",
        note="ax8v1",
    )

    # sylan9 s3, s4: ( t = x ∧ t = y ) → ( x ∈ z → y ∈ z )
    s5 = lb.ref(
        "s5",
        "( t = x ∧ t = y ) → ( x ∈ z → y ∈ z )",
        s3,
        s4,
        ref="sylan9",
        note="sylan9",
    )

    # exlimiv s5: ∃ t ( t = x ∧ t = y ) → ( x ∈ z → y ∈ z )
    s6 = lb.ref(
        "s6",
        "∃ t ( t = x ∧ t = y ) → ( x ∈ z → y ∈ z )",
        s5,
        ref="exlimiv",
        note="exlimiv",
    )

    # sylbi s1, s6: x = y → ( x ∈ z → y ∈ z )
    res = lb.ref(
        "res",
        "x = y → ( x ∈ z → y ∈ z )",
        s1,
        s6,
        ref="sylbi",
        note="sylbi equvinv, exlimiv",
    )

    return lb.build(res)


def prove_ax9v(sys: System) -> Proof:
    """ax9v: x = y → ( z e. x → z e. y ).

    Equality substitution in membership (right-hand side).
    The proof is a direct instantiation of ax-9 (ax-9).
    """
    lb = ProofBuilder(sys, "ax9v")
    lb.disjoint(_var(sys, "x"), _var(sys, "y"))
    res = lb.ref(
        "s1",
        "x = y → ( z e. x → z e. y )",
        ref="ax-9",
        note="ax-9 — ax-9",
    )
    return lb.build(res)


def prove_ax9v2(sys: System) -> Proof:
    """ax9v2: x = y → ( z e. x → z e. y ).

    The same formula as ax9v. The proof references ax9v directly.
    """
    lb = ProofBuilder(sys, "ax9v2")
    res = lb.ref(
        "s1",
        "x = y → ( z e. x → z e. y )",
        ref="ax9v",
        note="ax9v",
    )
    return lb.build(res)


def prove_ax9v1(sys: System) -> Proof:
    """ax9v1: x = y → ( z e. x → z e. y ).

    Same formula as ax9v, referencing ax9v directly.
    """
    lb = ProofBuilder(sys, "ax9v1")
    res = lb.ref(
        "s1",
        "x = y → ( z e. x → z e. y )",
        ref="ax9v",
        note="ax9v",
    )
    return lb.build(res)


def prove_ax9(sys: System) -> Proof:
    """ax9: x = y → ( z e. x → z e. y ).

    Equality implies membership substitution in the consequent.
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "ax9")

    # equvinv with t for z: x = y ↔ ∃ t ( t = x ∧ t = y )
    s1 = lb.ref(
        "s1",
        "x = y ↔ ∃ t ( t = x ∧ t = y )",
        ref="equvinv",
        note="equvinv",
    )

    # ax9v2 with x:=x, y:=t: x = t → ( z e. x → z e. t )
    s2 = lb.ref(
        "s2",
        "x = t → ( z e. x → z e. t )",
        ref="ax9v2",
        note="ax9v2",
    )

    # equcoms s2: t = x → ( z e. x → z e. t )
    s3 = lb.ref(
        "s3",
        "t = x → ( z e. x → z e. t )",
        s2,
        ref="equcoms",
        note="equcoms",
    )

    # ax9v1 with x:=t, y:=y: t = y → ( z e. t → z e. y )
    s4 = lb.ref(
        "s4",
        "t = y → ( z e. t → z e. y )",
        ref="ax9v1",
        note="ax9v1",
    )

    # sylan9 s3, s4: ( t = x ∧ t = y ) → ( z e. x → z e. y )
    s5 = lb.ref(
        "s5",
        "( t = x ∧ t = y ) → ( z e. x → z e. y )",
        s3,
        s4,
        ref="sylan9",
        note="sylan9",
    )

    # exlimiv s5: ∃ t ( t = x ∧ t = y ) → ( z e. x → z e. y )
    s6 = lb.ref(
        "s6",
        "∃ t ( t = x ∧ t = y ) → ( z e. x → z e. y )",
        s5,
        ref="exlimiv",
        note="exlimiv",
    )

    # sylbi s1, s6: x = y → ( z e. x → z e. y )
    res = lb.ref(
        "res",
        "x = y → ( z e. x → z e. y )",
        s1,
        s6,
        ref="sylbi",
        note="sylbi equvinv, exlimiv",
    )

    return lb.build(res)


def prove_elequ1(sys: System) -> Proof:
    """elequ1: x = y → ( x e. z ↔ y e. z ).

    Equality implies equivalence of membership.
    From ax8 and equcoms via impbid.
    (Contributed by NM, 10-Jan-1993.)
    set.mm proof: weq wel ax8 wi equcoms impbid.
    """
    lb = ProofBuilder(sys, "elequ1")

    # ax8: x = y → (x e. z → y e. z) — forward direction
    s_forward = lb.ref(
        "s_forward",
        "x = y → ( x e. z → y e. z )",
        ref="ax8",
        note="ax8",
    )

    # ax8 with x,y swapped: y = x → (y e. z → x e. z)
    s_ax8_swap = lb.ref(
        "s_ax8_swap",
        "y = x → ( y e. z → x e. z )",
        ref="ax8",
        note="ax8 with x:=y, y:=x",
    )

    # equcoms: from y = x → φ derive x = y → φ
    s_reverse = lb.ref(
        "s_reverse",
        "x = y → ( y e. z → x e. z )",
        s_ax8_swap,
        ref="equcoms",
        note="equcoms",
    )

    # impbid combines both directions into a biconditional
    res = lb.ref(
        "res",
        "x = y → ( x e. z ↔ y e. z )",
        s_forward,
        s_reverse,
        ref="impbid",
        note="impbid ax8, equcoms",
    )

    return lb.build(res)


def prove_cleljust(sys: System) -> Proof:
    """cleljust: x e. y ↔ ∃ z ( z = x ∧ z e. y ).

    Membership expressed as an existential equality.
    From elequ1 and equsexvw, then bicomi to swap.
    (Contributed by NM, 10-Jan-1993.)
    set.mm proof: weq wel wa wex elequ1 equsexvw bicomi.
    """
    lb = ProofBuilder(sys, "cleljust")
    # elequ1: z = x → ( z e. y ↔ x e. y )
    s1 = lb.ref(
        "s1",
        "z = x → ( z e. y ↔ x e. y )",
        ref="elequ1",
        note="elequ1",
    )
    # equsexvw: ∃ z ( z = x ∧ z e. y ) ↔ x e. y
    s2 = lb.ref(
        "s2",
        "∃ z ( z = x ∧ z e. y ) ↔ x e. y",
        s1,
        ref="equsexvw",
        note="equsexvw elequ1",
    )
    # bicomi: x e. y ↔ ∃ z ( z = x ∧ z e. y )
    res = lb.ref(
        "res",
        "x e. y ↔ ∃ z ( z = x ∧ z e. y )",
        s2,
        ref="bicomi",
        note="bicomi",
    )
    return lb.build(res)


def prove_elequ2(sys: System) -> Proof:
    """elequ2: x = y → ( z e. x ↔ z e. y ).

    Equality implies equivalence of membership.
    From ax9 and equcoms via impbid.
    (Contributed by NM, 10-Jan-1993.)
    set.mm proof: weq wel ax9 wi equcoms impbid.
    """
    lb = ProofBuilder(sys, "elequ2")

    # ax9: x = y → (z e. x → z e. y) — forward direction
    s_forward = lb.ref(
        "s_forward",
        "x = y → ( z e. x → z e. y )",
        ref="ax9",
        note="ax9",
    )

    # ax9 with x,y swapped: y = x → (z e. y → z e. x)
    s_ax9_swap = lb.ref(
        "s_ax9_swap",
        "y = x → ( z e. y → z e. x )",
        ref="ax9",
        note="ax9 with x:=y, y:=x",
    )

    # equcoms: from y = x → φ derive x = y → φ
    s_reverse = lb.ref(
        "s_reverse",
        "x = y → ( z e. y → z e. x )",
        s_ax9_swap,
        ref="equcoms",
        note="equcoms",
    )

    # impbid combines both directions into a biconditional
    res = lb.ref(
        "res",
        "x = y → ( z e. x ↔ z e. y )",
        s_forward,
        s_reverse,
        ref="impbid",
        note="impbid ax9, equcoms",
    )

    return lb.build(res)


def prove_elequ2g(sys: System) -> Proof:
    """elequ2g: x = y → ∀ z ( z e. x ↔ z e. y ).

    Generalization of elequ2.
    (Contributed by NM, 10-Jan-1993.)
    set.mm proof: elequ2 alrimiv.
    """
    lb = ProofBuilder(sys, "elequ2g")

    # elequ2: x = y → ( z e. x ↔ z e. y )
    s1 = lb.ref(
        "s1",
        "x = y → ( z e. x ↔ z e. y )",
        ref="elequ2",
        note="elequ2",
    )

    # alrimiv: ( x = y → ( z e. x ↔ z e. y ) ) ⊢ x = y → ∀ z ( z e. x ↔ z e. y )
    res = lb.ref(
        "res",
        "x = y → ∀ z ( z e. x ↔ z e. y )",
        s1,
        ref="alrimiv",
        note="alrimiv elequ2",
    )

    return lb.build(res)


def prove_elequ12(sys: System) -> Proof:
    """elequ12: ( x = y ∧ z = t ) → ( x e. z ↔ y e. t ).

    Equality of two pairs implies equivalence of membership.
    Combine elequ1 and elequ2 with sylan9bb.
    (Contributed by NM, 10-Jan-1993.)
    set.mm proof: weq wel elequ1 elequ2 sylan9bb.
    """
    lb = ProofBuilder(sys, "elequ12")

    # elequ1: x = y → ( x e. z ↔ y e. z )
    s_elequ1 = lb.ref(
        "s_elequ1",
        "x = y → ( x e. z ↔ y e. z )",
        ref="elequ1",
        note="elequ1",
    )

    # elequ2 with x:=z, y:=t, z:=y: z = t → ( y e. z ↔ y e. t )
    s_elequ2 = lb.ref(
        "s_elequ2",
        "z = t → ( y e. z ↔ y e. t )",
        ref="elequ2",
        note="elequ2 with x:=z, y:=t, z:=y",
    )

    # sylan9bb: ( ( φ → ( ψ ↔ χ ) ) ∧ ( θ → ( χ ↔ τ ) ) ) → ( ( φ ∧ θ ) → ( ψ ↔ τ ) )
    # with φ=x=y, ψ=x e. z, χ=y e. z, θ=z=t, τ=y e. t
    res = lb.ref(
        "res",
        "( x = y ∧ z = t ) → ( x e. z ↔ y e. t )",
        s_elequ1,
        s_elequ2,
        ref="sylan9bb",
        note="sylan9bb elequ1, elequ2",
    )

    return lb.build(res)


def prove_sylgt(sys: System) -> Proof:
    """sylgt: A. x ( ψ → χ ) → ( ( φ → A. x ψ ) → ( φ → A. x χ ) ).

    Syllogism with a generalized antecedent.
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: alim imim2d.
    """
    lb = ProofBuilder(sys, "sylgt")
    s1 = lb.ref(
        "s1",
        "A. x ( ψ → χ ) → ( A. x ψ → A. x χ )",
        ref="alim",
        note="alim",
    )
    res = lb.ref(
        "res",
        "A. x ( ψ → χ ) → ( ( φ → A. x ψ ) → ( φ → A. x χ ) )",
        s1,
        ref="imim2d",
        note="imim2d",
    )
    return lb.build(res)


def prove_sylg(sys: System) -> Proof:
    """sylg: ( ph -> A. x ch ).

    Syllogism combined with generalization. Generalize sylg.2 with alimi,
    then apply syl.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wal alimi syl.
    """
    lb = ProofBuilder(sys, "sylg")
    hyp1 = lb.hyp("sylg.1", "φ → A. x ψ")
    hyp2 = lb.hyp("sylg.2", "ψ → χ")
    # alimi: (ps -> ch) |- (A. x ps -> A. x ch)
    s1 = lb.ref(
        "s1",
        "A. x ψ → A. x χ",
        hyp2,
        ref="alimi",
        note="alimi sylg.2",
    )
    # syl: (ph -> A. x ps), (A. x ps -> A. x ch) |- (ph -> A. x ch)
    res = lb.ref(
        "res",
        "φ → A. x χ",
        hyp1,
        s1,
        ref="syl",
        note="syl sylg.1, alimi",
    )
    return lb.build(res)


def prove_alrimih(sys: System) -> Proof:
    """alrimih: φ → A. x ψ.

    Inference combining alrimih.1 and alrimih.2 via sylg.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: sylg.
    """
    lb = ProofBuilder(sys, "alrimih")
    hyp1 = lb.hyp("alrimih.1", "φ → ∀ x φ")
    hyp2 = lb.hyp("alrimih.2", "φ → ψ")
    # sylg: (ph -> A. x ps), (ps -> ch) |- (ph -> A. x ch)
    # with ph=φ, ps=φ, ch=ψ:
    #  sylg.1: φ → A. x φ  (alrimih.1)
    #  sylg.2: φ → ψ    (alrimih.2)
    #  conclusion: φ → A. x ψ
    res = lb.ref(
        "res",
        "φ → A. x ψ",
        hyp1,
        hyp2,
        ref="sylg",
        note="sylg alrimih.1, alrimih.2",
    )
    return lb.build(res)


def prove_alrimiv(sys: System) -> Proof:
    """alrimiv: φ → A. x ψ.

    Inference form of alrimih using ax-5 (ax-5) to satisfy the
    non-freeness condition via distinct variables.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: ax-5 alrimih.
    """
    lb = ProofBuilder(sys, "alrimiv")
    hyp = lb.hyp("alrimiv.1", "φ → ψ")
    # ax-5: φ → A. x φ (generalization, valid because x not free in φ)
    s1 = lb.ref("s1", "φ → ∀ x φ", ref="ax-5", note="ax-5")
    # alrimih: (φ → ∀ x φ), (φ → ψ) ⊢ φ → A. x ψ
    res = lb.ref(
        "res",
        "φ → A. x ψ",
        s1,
        hyp,
        ref="alrimih",
        note="alrimih ax-5 alrimiv.1",
    )
    return lb.build(res)


def prove_alrimivv(sys: System) -> Proof:
    """alrimivv: φ → A. x A. y ψ.

    Inference form of alrimiv with two universally quantified variables.
    Apply alrimiv twice: first with variable y, then with variable x.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wal alrimiv.
    """
    lb = ProofBuilder(sys, "alrimivv")
    hyp = lb.hyp("alrimivv.1", "φ → ψ")
    # alrimiv: (φ → ψ) ⊢ φ → A. y ψ
    s1 = lb.ref("s1", "φ → A. y ψ", hyp, ref="alrimiv", note="alrimiv alrimivv.1")
    # alrimiv: (φ → A. y ψ) ⊢ φ → A. x A. y ψ
    res = lb.ref("res", "φ → A. x A. y ψ", s1, ref="alrimiv", note="alrimiv s1")
    return lb.build(res)


def prove_2ax5(sys: System) -> Proof:
    """2ax5: φ → ∀ x ∀ y φ.

    A closed form of alrimivv using id.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: id alrimivv.
    """
    lb = ProofBuilder(sys, "2ax5")
    # id: φ → φ
    s1 = lb.ref("s1", "φ → φ", ref="id", note="id")
    # alrimivv: (φ → φ) ⊢ φ → A. x A. y φ
    res = lb.ref("res", "φ → ∀ x ∀ y φ", s1, ref="alrimivv", note="alrimivv id")
    return lb.build(res)


def prove_ax12v(sys: System) -> Proof:
    """ax12v: x = y → ( φ → A. x ( x = y → φ ) ).

    The antecedent-free form of ax-12. The proof uses ax-12 and ax-5
    together with syl5 to drop the intermediate A. y quantifier.
    (Contributed by NM, 27-Dec-1992.)
    set.mm proof: ax-5 ax-12 syl5.
    """
    lb = ProofBuilder(sys, "ax12v")
    lb.disjoint(_var(sys, "x"), _var(sys, "y"))
    lb.disjoint(_var(sys, "φ"), _var(sys, "y"))
    s1 = lb.ref("s1", "φ → A. y φ", ref="ax-5", note="ax-5")
    s2 = lb.ref(
        "s2",
        "x = y → ( A. y φ → A. x ( x = y → φ ) )",
        ref="ax-12",
        note="ax-12",
    )
    res = lb.ref(
        "res",
        "x = y → ( φ → A. x ( x = y → φ ) )",
        s1,
        s2,
        ref="syl5",
        note="syl5 ax-5, ax-12",
    )
    return lb.build(res)


def prove_ax12v2(sys: System) -> Proof:
    """ax12v2: x = y → ( φ → ∀ x ( x = y → φ ) ).

    ax12v without the distinct variable condition on x and φ.
    The proof introduces a new variable z, substitutes into ax12v,
    then eliminates the existential with exlimiiv.
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: vz equtrr ax12v imim1d alimdv syl9r syld ax6evr exlimiiv.
    """
    lb = ProofBuilder(sys, "ax12v2")
    # equtrr: y = z → ( x = y → x = z )
    s1 = lb.ref(
        "s1",
        "y = z → ( x = y → x = z )",
        ref="equtrr",
        note="equtrr",
    )
    # ax12v: x = z → ( φ → ∀ x ( x = z → φ ) )
    s2 = lb.ref(
        "s2",
        "x = z → ( φ → ∀ x ( x = z → φ ) )",
        ref="ax12v",
        note="ax12v",
    )
    # imim1d s1: y = z → ( ( x = z → φ ) → ( x = y → φ ) )
    s4 = lb.ref(
        "s4",
        "y = z → ( ( x = z → φ ) → ( x = y → φ ) )",
        s1,
        ref="imim1d",
        note="imim1d",
    )
    # alimdv s4: y = z → ( ∀ x ( x = z → φ ) → ∀ x ( x = y → φ ) )
    s5 = lb.ref(
        "s5",
        "y = z → ( ∀ x ( x = z → φ ) → ∀ x ( x = y → φ ) )",
        s4,
        ref="alimdv",
        note="alimdv",
    )
    # syl9r s2, s5: y = z → ( x = z → ( φ → ∀ x ( x = y → φ ) ) )
    s6 = lb.ref(
        "s6",
        "y = z → ( x = z → ( φ → ∀ x ( x = y → φ ) ) )",
        s2,
        s5,
        ref="syl9r",
        note="syl9r",
    )
    # syld s1, s6: y = z → ( x = y → ( φ → ∀ x ( x = y → φ ) ) )
    s7 = lb.ref(
        "s7",
        "y = z → ( x = y → ( φ → ∀ x ( x = y → φ ) ) )",
        s1,
        s6,
        ref="syld",
        note="syld",
    )
    # ax6evr: ∃ z y = z
    s8 = lb.ref(
        "s8",
        "∃ z y = z",
        ref="ax6evr",
        note="ax6evr",
    )
    # exlimiiv s7, s8: x = y → ( φ → ∀ x ( x = y → φ ) )
    res = lb.ref(
        "res",
        "x = y → ( φ → ∀ x ( x = y → φ ) )",
        s7,
        s8,
        ref="exlimiiv",
        note="exlimiiv",
    )
    return lb.build(res)


def prove_ax12ev2(sys: System) -> Proof:
    """ax12ev2: ∃ x ( x = y ∧ φ ) → ( x = y → φ ).

    From ax12v2 and exnalimn, using con1d, biimtrid, and com12.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: weq wa wex wn wi wal exnalimn ax12v2 con1d biimtrid com12.
    """
    lb = ProofBuilder(sys, "ax12ev2")

    # ax12v2: x = y → ( φ → ∀ x ( x = y → φ ) )
    # Substitute ¬ φ for φ, giving:
    # x = y → ( ¬ φ → ∀ x ( x = y → ¬ φ ) )
    s1 = lb.ref(
        "s1",
        "x = y → ( ¬ φ → ∀ x ( x = y → ¬ φ ) )",
        ref="ax12v2",
        note="ax12v2",
    )

    # con1d s1: from P → ( ¬ Q → R ), deduce P → ( ¬ R → Q )
    # s1: x = y → ( ¬ φ → ∀ x ( x = y → ¬ φ ) )
    # con1d gives: x = y → ( ¬ ∀ x ( x = y → ¬ φ ) → φ )
    s2 = lb.ref(
        "s2",
        "x = y → ( ¬ ∀ x ( x = y → ¬ φ ) → φ )",
        s1,
        ref="con1d",
        note="con1d",
    )

    # exnalimn: ∃ x ( φ ∧ ψ ) ↔ ¬ ∀ x ( φ → ¬ ψ )
    # Substitute x = y for φ, φ for ψ:
    # ∃ x ( x = y ∧ φ ) ↔ ¬ ∀ x ( x = y → ¬ φ )
    s3 = lb.ref(
        "s3",
        "∃ x ( x = y ∧ φ ) ↔ ¬ ∀ x ( x = y → ¬ φ )",
        ref="exnalimn",
        note="exnalimn",
    )

    # biimtrid s3, s2:
    # hyp1 (biimtrid.1): ( φ_bi ↔ ψ_bi ) = s3
    # hyp2 (biimtrid.2): χ_bi → ( ψ_bi → θ_bi ) = s2
    # conclusion: χ_bi → ( φ_bi → θ_bi )
    # = x = y → ( ∃ x ( x = y ∧ φ ) → φ )
    s4 = lb.ref(
        "s4",
        "x = y → ( ∃ x ( x = y ∧ φ ) → φ )",
        s3,
        s2,
        ref="biimtrid",
        note="biimtrid",
    )

    # com12 s4: from φ → ( ψ → χ ), deduce ψ → ( φ → χ )
    # s4: x = y → ( ∃ x ( x = y ∧ φ ) → φ )
    # com12 gives: ∃ x ( x = y ∧ φ ) → ( x = y → φ )
    res = lb.ref(
        "res",
        "∃ x ( x = y ∧ φ ) → ( x = y → φ )",
        s4,
        ref="com12",
        note="com12",
    )

    return lb.build(res)


def prove_gen2(sys: System) -> Proof:
    """gen2: A. x A. y φ.

    ax-gen applied twice: first with y, then with x.
    """
    lb = ProofBuilder(sys, "gen2")
    hyp_ph = lb.hyp("hph", "φ")
    s1 = lb.ref("s1", "A. y φ", hyp_ph, ref="ax-gen", note="ax-gen with y")
    res = lb.ref("res", "A. x A. y φ", s1, ref="ax-gen", note="ax-gen with x")
    return lb.build(res)


def prove_ax5d(sys: System) -> Proof:
    """ax5d: φ → ( ψ → A. x ψ ).

    Deduction form of ax-5 (ax-5), adding an antecedent ph.
    (Contributed by NM, 29-Dec-1992.)
    set.mm proof: ax-5 a1i.
    """
    lb = ProofBuilder(sys, "ax5d")
    lb.disjoint(_var(sys, "ψ"), _var(sys, "x"))
    s1 = lb.ref("s1", "ψ → A. x ψ", ref="ax-5", note="ax-5")
    res = lb.ref("res", "φ → ( ψ → A. x ψ )", s1, ref="a1i", note="a1i")
    return lb.build(res)


def prove_ax13w(sys: System) -> Proof:
    """ax13w: ¬ ( x = y ) → ( y = z → ∀ x y = z ).

    Weak version of ax-13. Derived from ax5d.
    (Contributed by NM, 29-Dec-1992.)
    set.mm proof: weq wn ax5d.
    """
    lb = ProofBuilder(sys, "ax13w")
    lb.disjoint(_var(sys, "x"), _var(sys, "y"))
    lb.disjoint(_var(sys, "x"), _var(sys, "z"))
    res = lb.ref("res", "¬ ( x = y ) → ( y = z → ∀ x y = z )", ref="ax5d", note="ax5d")
    return lb.build(res)


def prove_ax13dgen1(sys: System) -> Proof:
    """ax13dgen1: ¬ x = x → ( x = z → ∀ x x = z ).

    From equid (reflexivity of equality) and pm2.24i, which says
    a true statement can be inferred from any antecedent.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: weq wal wi equid pm2.24i.
    """
    lb = ProofBuilder(sys, "ax13dgen1")
    # equid: x = x
    s1 = lb.ref("s1", "x = x", ref="equid", note="equid")
    # pm2.24i with φ := x = x, ψ := ( x = z → ∀ x x = z )
    res = lb.ref(
        "res",
        "¬ x = x → ( x = z → ∀ x x = z )",
        s1,
        ref="pm2.24i",
        note="pm2.24i with equid",
    )
    return lb.build(res)


def prove_ax13dgen2(sys: System) -> Proof:
    """ax13dgen2: ¬ x = y → ( y = x → ∀ x y = x ).

    Derived from equcomi, pm2.21, and syl5.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: weq wn wal equcomi pm2.21 syl5.
    """
    lb = ProofBuilder(sys, "ax13dgen2")
    # equcomi: y = x → x = y
    s1 = lb.ref(
        "s1",
        "y = x → x = y",
        ref="equcomi",
        note="equcomi",
    )
    # pm2.21 with φ := x = y, ψ := ∀ x y = x:
    # ¬ x = y → ( x = y → ∀ x y = x )
    s2 = lb.ref(
        "s2",
        "¬ x = y → ( x = y → ∀ x y = x )",
        ref="pm2.21",
        note="pm2.21",
    )
    # syl5: ( φ → ( ψ → χ ) ) and ( θ → ψ ) gives ( φ → ( θ → χ ) )
    # with φ := ¬ x = y, ψ := x = y, χ := ∀ x y = x, θ := y = x
    res = lb.ref(
        "res",
        "¬ x = y → ( y = x → ∀ x y = x )",
        s1,
        s2,
        ref="syl5",
        note="syl5 equcomi, pm2.21",
    )
    return lb.build(res)


def prove_ax13dgen3(sys: System) -> Proof:
    """ax13dgen3: ¬ x = y → ( y = y → ∀ x y = y ).

    From equid and generalization with two nested antecedents.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: weq wal wn equid ax-gen 2a1i.
    """
    lb = ProofBuilder(sys, "ax13dgen3")
    # equid: y = y
    s1 = lb.ref("s1", "y = y", ref="equid", note="equid")
    # ax-gen: ∀ x y = y
    s2 = lb.ref("s2", "∀ x y = y", s1, ref="ax-gen", note="ax-gen")
    # 2a1i: ¬ x = y → ( y = y → ∀ x y = y )
    res = lb.ref(
        "res",
        "¬ x = y → ( y = y → ∀ x y = y )",
        s2,
        ref="2a1i",
        note="2a1i",
    )
    return lb.build(res)


def prove_ax13dgen4(sys: System) -> Proof:
    """ax13dgen4: ¬ x = x → ( x = x → ∀ x x = x ).

    Instance of pm2.21 with φ := x = x, ψ := ∀ x x = x.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: weq wal pm2.21.
    """
    lb = ProofBuilder(sys, "ax13dgen4")
    res = lb.ref(
        "res",
        "¬ x = x → ( x = x → ∀ x x = x )",
        ref="pm2.21",
        note="pm2.21",
    )
    return lb.build(res)


def prove_nfi(sys: System) -> Proof:
    """nfi: F/ x φ.

    Inference form of df-nf. If the existential implies the universal,
    the variable is not free.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: df-nf mpbir.
    """
    lb = ProofBuilder(sys, "nfi")
    hyp = lb.hyp("nfi.1", "E. x φ → A. x φ")
    s1 = lb.ref("s1", "F/ x φ ↔ ( E. x φ → A. x φ )", ref="df-nf", note="df-nf")
    res = lb.ref("res", "F/ x φ", hyp, s1, ref="mpbir", note="mpbir nfi.1, df-nf")
    return lb.build(res)


def prove_nfia1(sys: System) -> Proof:
    """nfia1: F/ x ( ∀ x φ → ∀ x ψ ).

    Combine nfa1 with nfim: x is not free in both ∀xφ and ∀xψ,
    hence not free in their implication.
    (Contributed by NM, 10-Jan-1993.)
    set.mm proof: wal nfa1 nfim.
    """
    lb = ProofBuilder(sys, "nfia1")
    s1 = lb.ref("s1", "F/ x ∀ x φ", ref="nfa1", note="nfa1")
    s2 = lb.ref("s2", "F/ x ∀ x ψ", ref="nfa1", note="nfa1")
    res = lb.ref(
        "res",
        "F/ x ( ∀ x φ → ∀ x ψ )",
        s1,
        s2,
        ref="nfim",
        note="nfim nfa1, nfa1",
    )
    return lb.build(res)


def prove_nfv(sys: System) -> Proof:
    """nfv: F/ x φ.

    A wff variable is always not free in a set variable.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "nfv")
    s1 = lb.ref("s1", "∃ x φ → ∀ x φ", ref="ax5ea", note="ax5ea")
    res = lb.ref("res", "F/ x φ", s1, ref="nfi", note="nfi ax5ea")
    return lb.build(res)


def prove_nfvd(sys: System) -> Proof:
    """nfvd: φ → F/ x ψ.

    Deduction form of nfv.  A wff variable is not free in a set
    variable even when the statement is under an antecedent.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "nfvd")
    s1 = lb.ref("s1", "F/ x ψ", ref="nfv", note="nfv")
    res = lb.ref("res", "φ → F/ x ψ", s1, ref="a1i", note="a1i")
    return lb.build(res)


def prove_nfri(sys: System) -> Proof:
    """nfri: ∃ x φ → ∀ x φ.

    Inference form of df-nf. If the variable is not free, the existential
    implies the universal.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: df-nf mpbi.
    """
    lb = ProofBuilder(sys, "nfri")
    hyp = lb.hyp("nfri.1", "F/ x φ")
    s1 = lb.ref("s1", "F/ x φ ↔ ( ∃ x φ → ∀ x φ )", ref="df-nf", note="df-nf")
    res = lb.ref("res", "∃ x φ → ∀ x φ", hyp, s1, ref="mpbi", note="mpbi nfri.1, df-nf")
    return lb.build(res)


def prove_nfrd(sys: System) -> Proof:
    """nfrd: φ → ( E. x ψ → A. x ψ ).

    Deduction form of df-nf. The proof unwraps the F/ definition
    via df-nf and sylib.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: df-nf sylib.
    """
    lb = ProofBuilder(sys, "nfrd")
    h1 = lb.hyp("nfrd.1", "φ → F/ x ψ")
    s1 = lb.ref("s1", "F/ x ψ ↔ ( E. x ψ → A. x ψ )", ref="df-nf", note="df-nf")
    res = lb.ref("res", "φ → ( E. x ψ → A. x ψ )", h1, s1, ref="sylib", note="sylib")
    return lb.build(res)


def prove_nfd(sys: System) -> Proof:
    """nfd: φ → F/ x ψ.

    Deduction form of df-nf (reverse of nfrd). The proof uses df-nf
    and sylibr to wrap the conditional back into the F/ definition.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wex wal wi wnf df-nf sylibr.
    """
    lb = ProofBuilder(sys, "nfd")
    h1 = lb.hyp("nfd.1", "φ → ( E. x ψ → A. x ψ )")
    s1 = lb.ref("s1", "F/ x ψ ↔ ( E. x ψ → A. x ψ )", ref="df-nf", note="df-nf")
    res = lb.ref("res", "φ → F/ x ψ", h1, s1, ref="sylibr", note="sylibr")
    return lb.build(res)


def prove_nfimd(sys: System) -> Proof:
    """nfimd: φ → F/ x ( ψ → χ ).

    Deduction form of the not-free property for implication.
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "nfimd")
    h1 = lb.hyp("nfimd.1", "φ → F/ x ψ")
    h2 = lb.hyp("nfimd.2", "φ → F/ x χ")

    # nfrd: φ → (∃ x ψ → ∀ x ψ)
    s1 = lb.ref("s1", "φ → ( ∃ x ψ → ∀ x ψ )", h1, ref="nfrd", note="nfrd nfimd.1")
    # nfrd: φ → (∃ x χ → ∀ x χ)
    s2 = lb.ref("s2", "φ → ( ∃ x χ → ∀ x χ )", h2, ref="nfrd", note="nfrd nfimd.2")
    # 19.35: ∃ x (ψ → χ) ↔ (∀ x ψ → ∃ x χ)
    s3 = lb.ref(
        "s3",
        "∃ x ( ψ → χ ) ↔ ( ∀ x ψ → ∃ x χ )",
        ref="19.35",
        note="19.35",
    )
    # biimpi: ∃ x (ψ → χ) → (∀ x ψ → ∃ x χ)
    s4 = lb.ref(
        "s4",
        "∃ x ( ψ → χ ) → ( ∀ x ψ → ∃ x χ )",
        s3,
        ref="biimpi",
        note="biimpi 19.35",
    )
    # imim12d: φ → ((∀ x ψ → ∃ x χ) → (∃ x ψ → ∀ x χ))
    s5 = lb.ref(
        "s5",
        "φ → ( ( ∀ x ψ → ∃ x χ ) → ( ∃ x ψ → ∀ x χ ) )",
        s1,
        s2,
        ref="imim12d",
        note="imim12d",
    )
    # 19.38: (∃ x ψ → ∀ x χ) → ∀ x (ψ → χ)
    s6 = lb.ref(
        "s6",
        "( ∃ x ψ → ∀ x χ ) → ∀ x ( ψ → χ )",
        ref="19.38",
        note="19.38",
    )
    # syl56: φ → (∃ x (ψ → χ) → ∀ x (ψ → χ))
    s7 = lb.ref(
        "s7",
        "φ → ( ∃ x ( ψ → χ ) → ∀ x ( ψ → χ ) )",
        s4,
        s5,
        s6,
        ref="syl56",
        note="syl56",
    )
    # nfd: φ → F/ x (ψ → χ)
    res = lb.ref(
        "res",
        "φ → F/ x ( ψ → χ )",
        s7,
        ref="nfd",
        note="nfd",
    )
    return lb.build(res)


def prove_nfimt(sys: System) -> Proof:
    """nfimt: ( F/ x φ ∧ F/ x ψ ) → F/ x ( φ → ψ ).

    Closed form of nfimd for the not-free property of implication.
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "nfimt")
    # simpl: ( F/ x φ ∧ F/ x ψ ) → F/ x φ
    s1 = lb.ref("s1", "( F/ x φ ∧ F/ x ψ ) → F/ x φ", ref="simpl", note="simpl")
    # simpr: ( F/ x φ ∧ F/ x ψ ) → F/ x ψ
    s2 = lb.ref("s2", "( F/ x φ ∧ F/ x ψ ) → F/ x ψ", ref="simpr", note="simpr")
    # nfimd: ( F/ x φ ∧ F/ x ψ ) → F/ x ( φ → ψ )
    res = lb.ref(
        "res",
        "( F/ x φ ∧ F/ x ψ ) → F/ x ( φ → ψ )",
        s1,
        s2,
        ref="nfimd",
        note="nfimd",
    )
    return lb.build(res)


def prove_nfim(sys: System) -> Proof:
    """nfim: F/ x ( φ → ψ ).

    Inference form of nfimt. (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "nfim")
    h1 = lb.hyp("nfim.1", "F/ x φ")
    h2 = lb.hyp("nfim.2", "F/ x ψ")
    s1 = lb.ref(
        "s1",
        "( F/ x φ ∧ F/ x ψ ) → F/ x ( φ → ψ )",
        ref="nfimt",
        note="nfimt",
    )
    res = lb.ref(
        "res",
        "F/ x ( φ → ψ )",
        h1,
        h2,
        s1,
        ref="mp2an",
        note="mp2an nfim.1, nfim.2, nfimt",
    )
    return lb.build(res)


def prove_nfim1(sys: System) -> Proof:
    """nfim1: Ⅎ x ( φ → ψ ).

    Inference form: from Ⅎ x φ and φ → Ⅎ x ψ, conclude Ⅎ x ( φ → ψ ).
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "nfim1")
    h1 = lb.hyp("nfim1.1", "Ⅎ x φ")
    h2 = lb.hyp("nfim1.2", "φ → Ⅎ x ψ")

    # nf3: Ⅎ x φ ↔ ( ∀ x φ ∨ ∀ x ¬ φ )
    s_nf3 = lb.ref(
        "s_nf3",
        "Ⅎ x φ ↔ ( ∀ x φ ∨ ∀ x ¬ φ )",
        ref="nf3",
        note="nf3",
    )

    # mpbi: ( ∀ x φ ∨ ∀ x ¬ φ ) from nfim1.1 and nf3
    s_mpbi = lb.ref(
        "s_mpbi",
        "( ∀ x φ ∨ ∀ x ¬ φ )",
        h1,
        s_nf3,
        ref="mpbi",
        note="mpbi nfim1.1, nf3",
    )

    # nftht: ∀ x φ → Ⅎ x φ
    s_nftht1 = lb.ref(
        "s_nftht1",
        "∀ x φ → Ⅎ x φ",
        ref="nftht",
        note="nftht",
    )

    # sps: ∀ x φ → Ⅎ x ψ (from h2: φ → Ⅎ x ψ)
    s_sps = lb.ref(
        "s_sps",
        "∀ x φ → Ⅎ x ψ",
        h2,
        ref="sps",
        note="sps nfim1.2",
    )

    # nfimd: ∀ x φ → Ⅎ x ( φ → ψ )
    s_nfimd = lb.ref(
        "s_nfimd",
        "∀ x φ → Ⅎ x ( φ → ψ )",
        s_nftht1,
        s_sps,
        ref="nfimd",
        note="nfimd nftht, sps",
    )

    # pm2.21: ¬ φ → ( φ → ψ )
    s_pm2_21 = lb.ref(
        "s_pm2_21",
        "¬ φ → ( φ → ψ )",
        ref="pm2.21",
        note="pm2.21",
    )

    # alimi: ∀ x ¬ φ → ∀ x ( φ → ψ )
    s_alimi = lb.ref(
        "s_alimi",
        "∀ x ¬ φ → ∀ x ( φ → ψ )",
        s_pm2_21,
        ref="alimi",
        note="alimi pm2.21",
    )

    # nftht: ∀ x ( φ → ψ ) → Ⅎ x ( φ → ψ )
    s_nftht2 = lb.ref(
        "s_nftht2",
        "∀ x ( φ → ψ ) → Ⅎ x ( φ → ψ )",
        ref="nftht",
        note="nftht",
    )

    # syl: ∀ x ¬ φ → Ⅎ x ( φ → ψ )
    s_syl = lb.ref(
        "s_syl",
        "∀ x ¬ φ → Ⅎ x ( φ → ψ )",
        s_alimi,
        s_nftht2,
        ref="syl",
        note="syl alimi, nftht",
    )

    # jaoi: ( ∀ x φ ∨ ∀ x ¬ φ ) → Ⅎ x ( φ → ψ )
    s_jaoi = lb.ref(
        "s_jaoi",
        "( ∀ x φ ∨ ∀ x ¬ φ ) → Ⅎ x ( φ → ψ )",
        s_nfimd,
        s_syl,
        ref="jaoi",
        note="jaoi nfimd, syl",
    )

    # ax-mp: Ⅎ x ( φ → ψ )
    res = lb.mp(
        "res",
        s_mpbi,
        s_jaoi,
        "ax-mp mpbi, jaoi",
    )

    return lb.build(res)


def prove_nfan1(sys: System) -> Proof:
    """nfan1: Ⅎ x ( φ ∧ ψ ).

    Inference form: from Ⅎ x φ and φ → Ⅎ x ψ, conclude Ⅎ x ( φ ∧ ψ ).
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "nfan1")
    h1 = lb.hyp("nfim1.1", "Ⅎ x φ")
    h2 = lb.hyp("nfim1.2", "φ → Ⅎ x ψ")

    # df-an: ( φ ∧ ψ ) ↔ ¬ ( φ → ¬ ψ )
    s_df_an = lb.ref(
        "s_df_an",
        "( φ ∧ ψ ) ↔ ¬ ( φ → ¬ ψ )",
        ref="df-an",
        note="df-an",
    )

    # nfnd: φ → Ⅎ x ¬ ψ
    s_nfnd = lb.ref(
        "s_nfnd",
        "φ → Ⅎ x ¬ ψ",
        h2,
        ref="nfnd",
        note="nfnd nfim1.2",
    )

    # nfim1: Ⅎ x ( φ → ¬ ψ )
    s_nfim1 = lb.ref(
        "s_nfim1",
        "Ⅎ x ( φ → ¬ ψ )",
        h1,
        s_nfnd,
        ref="nfim1",
        note="nfim1 nfim1.1, nfnd",
    )

    # nfn: Ⅎ x ¬ ( φ → ¬ ψ )
    s_nfn = lb.ref(
        "s_nfn",
        "Ⅎ x ¬ ( φ → ¬ ψ )",
        s_nfim1,
        ref="nfn",
        note="nfn nfim1",
    )

    # nfxfr: Ⅎ x ( φ ∧ ψ )
    res = lb.ref(
        "res",
        "Ⅎ x ( φ ∧ ψ )",
        s_df_an,
        s_nfn,
        ref="nfxfr",
        note="nfxfr df-an, nfn",
    )

    return lb.build(res)


def prove_nftht(sys: System) -> Proof:
    """nftht: A. x ph → F/ x ph.

    Universal quantifier implies not-free. ax-1 gives (A. x ph →
    (E. x ph → A. x ph)), which furnishes the hypothesis for nfd.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wal wex ax-1 nfd.
    """
    lb = ProofBuilder(sys, "nftht")
    # ax-1: ph → (ps → ph) with ph := A. x ph, ps := E. x ph
    s1 = lb.ref(
        "s1",
        "A. x ph → ( E. x ph → A. x ph )",
        ref="ax-1",
        note="ax-1: A. x ph → (E. x ph → A. x ph)",
    )
    # nfd: from hypothesis (ph → (E. x ps → A. x ps)) derive ph → F/ x ps
    # Substitute ph := A. x ph, ps := ph → s1 matches the hypothesis
    res = lb.ref(
        "res",
        "A. x ph → F/ x ph",
        s1,
        ref="nfd",
        note="nfd with hypothesis from ax-1",
    )
    return lb.build(res)


def prove_nfntht(sys: System) -> Proof:
    """nfntht: ¬ ∃ x φ → Ⅎ x φ.

    If φ does not exist for any x, then x is not free in φ.
    pm2.21 gives ¬ ∃ x φ → (∃ x φ → ∀ x φ), which furnishes the
    hypothesis for nfd.
    (Contributed by NM, 7-Nov-1995.)
    set.mm proof: wex wn wal pm2.21 nfd.
    """
    lb = ProofBuilder(sys, "nfntht")
    # pm2.21 with φ := ∃ x φ, ψ := ∀ x φ
    s1 = lb.ref(
        "s1",
        "¬ ∃ x φ → ( ∃ x φ → ∀ x φ )",
        ref="pm2.21",
        note="pm2.21: ¬ ∃ x φ → (∃ x φ → ∀ x φ)",
    )
    # nfd: from hypothesis (¬ ∃ x φ → (∃ x φ → ∀ x φ)) derive ¬ ∃ x φ → Ⅎ x φ
    res = lb.ref(
        "res",
        "¬ ∃ x φ → F/ x φ",
        s1,
        ref="nfd",
        note="nfd with hypothesis from pm2.21",
    )
    return lb.build(res)


def prove_nfntht2(sys: System) -> Proof:
    """nfntht2: ∀ x ¬ φ → Ⅎ x φ.

    An alternate definition of not free when φ is false for all x.
    From alnex and nfntht via sylbi.
    (Contributed by NM, 7-Nov-1995.)
    set.mm proof: alnex nfntht sylbi.
    """
    lb = ProofBuilder(sys, "nfntht2")
    # alnex: ( ∀ x ¬ φ ↔ ¬ ∃ x φ )
    s1 = lb.ref(
        "s1",
        "∀ x ¬ φ ↔ ¬ ∃ x φ",
        ref="alnex",
        note="alnex",
    )
    # nfntht: ¬ ∃ x φ → Ⅎ x φ
    s2 = lb.ref(
        "s2",
        "¬ ∃ x φ → Ⅎ x φ",
        ref="nfntht",
        note="nfntht",
    )
    # sylbi: from biconditional and implication, derive ∀ x ¬ φ → Ⅎ x φ
    res = lb.ref(
        "res",
        "∀ x ¬ φ → Ⅎ x φ",
        s1,
        s2,
        ref="sylbi",
        note="sylbi alnex, nfntht",
    )
    return lb.build(res)


def prove_nfnth(sys: System) -> Proof:
    """nfnth: F/ x ph.

    If ¬ φ holds, then x is not free in φ.
    From nfntht2 and mpg.
    (Contributed by NM, 20-Nov-1995.)
    set.mm proof: wn wnf nfntht2 mpg.
    """
    lb = ProofBuilder(sys, "nfnth")
    h1 = lb.hyp("nfnth.1", "¬ φ")
    s1 = lb.ref("s1", "∀ x ¬ φ → F/ x φ", ref="nfntht2", note="nfntht2")
    res = lb.ref("res", "F/ x φ", s1, h1, ref="mpg", note="mpg nfntht2, nfnth.1")
    return lb.build(res)


def prove_nffal(sys: System) -> Proof:
    """nffal: F/ x F..

    x is not free in falsehood.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wfal fal nfnth.
    """
    lb = ProofBuilder(sys, "nffal")
    s_fal = lb.ref("s_fal", "¬ F.", ref="fal", note="fal")
    res = lb.ref("res", "F/ x F.", s_fal, ref="nfnth", note="nfnth")
    return lb.build(res)


def prove_nfth(sys: System) -> Proof:
    """nfth: F/ x ph.

    If ph holds, then x is (effectively) not free in ph.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wnf nftht mpg.
    """
    lb = ProofBuilder(sys, "nfth")
    h1 = lb.hyp("nfth.1", "ph")
    s1 = lb.ref("s1", "A. x ph -> F/ x ph", ref="nftht", note="nftht")
    res = lb.ref("res", "F/ x ph", s1, h1, ref="mpg", note="mpg nftht, nfth.1")
    return lb.build(res)


def prove_nftru(sys: System) -> Proof:
    """nftru: F/ x T.

    Not-free in true. (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "nftru")
    s_tru = lb.ref("s_tru", "T.", ref="tru", note="tru")
    res = lb.ref("res", "F/ x T.", s_tru, ref="nfth", note="nfth with T./ph")
    return lb.build(res)


def prove_nfequid(sys: System) -> Proof:
    """nfequid: F/ y x = x.

    y is not free in x = x.  Apply nfth to equid.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: weq equid nfth.
    """
    lb = ProofBuilder(sys, "nfequid")
    s_equid = lb.ref("s_equid", "x = x", ref="equid", note="equid")
    res = lb.ref("res", "F/ y x = x", s_equid, ref="nfth", note="nfth with x = x / ph")
    return lb.build(res)


def prove_nf2(sys: System) -> Proof:
    """nf2: F/ x φ ↔ (∀ x φ ∨ ¬ ∃ x φ).

    Equivalence of "not free" with universal-or-negated-existential.
    """
    lb = ProofBuilder(sys, "nf2")
    # df-nf: F/ x φ ↔ (∃ x φ → ∀ x φ)
    s1 = lb.ref(
        "s1",
        "F/ x φ ↔ ( ∃ x φ → ∀ x φ )",
        ref="df-nf",
        note="df-nf",
    )
    # imor: (∃ x φ → ∀ x φ) ↔ (¬ ∃ x φ ∨ ∀ x φ)
    s2 = lb.ref(
        "s2",
        "( ∃ x φ → ∀ x φ ) ↔ ( ¬ ∃ x φ ∨ ∀ x φ )",
        ref="imor",
        note="imor",
    )
    # orcom: (¬ ∃ x φ ∨ ∀ x φ) ↔ (∀ x φ ∨ ¬ ∃ x φ)
    s3 = lb.ref(
        "s3",
        "( ¬ ∃ x φ ∨ ∀ x φ ) ↔ ( ∀ x φ ∨ ¬ ∃ x φ )",
        ref="orcom",
        note="orcom",
    )
    # 3bitri: chain the three biconditionals
    res = lb.ref(
        "res",
        "F/ x φ ↔ ( ∀ x φ ∨ ¬ ∃ x φ )",
        s1,
        s2,
        s3,
        ref="3bitri",
        note="3bitri df-nf, imor, orcom",
    )
    return lb.build(res)


def prove_nf3(sys: System) -> Proof:
    """nf3: F/ x φ ↔ (∀ x φ ∨ ∀ x ¬ φ).

    Equivalence of "not free" with universal-or-universal-negated.
    """
    lb = ProofBuilder(sys, "nf3")
    # nf2: F/ x φ ↔ (∀ x φ ∨ ¬ ∃ x φ)
    s1 = lb.ref(
        "s1",
        "F/ x φ ↔ ( ∀ x φ ∨ ¬ ∃ x φ )",
        ref="nf2",
        note="nf2",
    )
    # alnex: ∀ x ¬ φ ↔ ¬ ∃ x φ
    s2 = lb.ref(
        "s2",
        "∀ x ¬ φ ↔ ¬ ∃ x φ",
        ref="alnex",
        note="alnex",
    )
    # orbi2i: (∀ x φ ∨ ∀ x ¬ φ) ↔ (∀ x φ ∨ ¬ ∃ x φ)
    s3 = lb.ref(
        "s3",
        "( ∀ x φ ∨ ∀ x ¬ φ ) ↔ ( ∀ x φ ∨ ¬ ∃ x φ )",
        s2,
        ref="orbi2i",
        note="orbi2i alnex",
    )
    # bitr4i: F/ x φ ↔ (∀ x φ ∨ ∀ x ¬ φ)
    res = lb.ref(
        "res",
        "F/ x φ ↔ ( ∀ x φ ∨ ∀ x ¬ φ )",
        s1,
        s3,
        ref="bitr4i",
        note="bitr4i nf2, orbi2i alnex",
    )
    return lb.build(res)


def prove_nf4(sys: System) -> Proof:
    """nf4: F/ x φ ↔ ( ¬ ∀ x φ → ∀ x ¬ φ ).

    Equivalence of "not free" with negated-universal-implies-universal-
    negated.
    """
    lb = ProofBuilder(sys, "nf4")
    # nf3: F/ x φ ↔ ( ∀ x φ ∨ ∀ x ¬ φ )
    s1 = lb.ref(
        "s1",
        "F/ x φ ↔ ( ∀ x φ ∨ ∀ x ¬ φ )",
        ref="nf3",
        note="nf3",
    )
    # df-or: ( ∀ x φ ∨ ∀ x ¬ φ ) ↔ ( ¬ ∀ x φ → ∀ x ¬ φ )
    s2 = lb.ref(
        "s2",
        "( ∀ x φ ∨ ∀ x ¬ φ ) ↔ ( ¬ ∀ x φ → ∀ x ¬ φ )",
        ref="df-or",
        note="df-or",
    )
    # bitri: F/ x φ ↔ ( ¬ ∀ x φ → ∀ x ¬ φ )
    res = lb.ref(
        "res",
        "F/ x φ ↔ ( ¬ ∀ x φ → ∀ x ¬ φ )",
        s1,
        s2,
        ref="bitri",
        note="bitri nf3, df-or",
    )
    return lb.build(res)


def prove_nfnbi(sys: System) -> Proof:
    """nfnbi: F/ x φ ↔ F/ x ¬ φ.

    Equivalence of "not free" with negated "not free".
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: exnal imbi1i df-nf nf4 3bitr4ri.
    """
    lb = ProofBuilder(sys, "nfnbi")

    # exnal: ∃ x ¬ φ ↔ ¬ ∀ x φ
    s1 = lb.ref(
        "s1",
        "∃ x ¬ φ ↔ ¬ ∀ x φ",
        ref="exnal",
        note="exnal",
    )

    # imbi1i: ( ∃ x ¬ φ → ∀ x ¬ φ ) ↔ ( ¬ ∀ x φ → ∀ x ¬ φ )
    s2 = lb.ref(
        "s2",
        "( ∃ x ¬ φ → ∀ x ¬ φ ) ↔ ( ¬ ∀ x φ → ∀ x ¬ φ )",
        s1,
        ref="imbi1i",
        note="imbi1i exnal",
    )

    # df-nf: F/ x ¬ φ ↔ ( ∃ x ¬ φ → ∀ x ¬ φ )
    s3 = lb.ref(
        "s3",
        "F/ x ¬ φ ↔ ( ∃ x ¬ φ → ∀ x ¬ φ )",
        ref="df-nf",
        note="df-nf",
    )

    # nf4: F/ x φ ↔ ( ¬ ∀ x φ → ∀ x ¬ φ )
    s4 = lb.ref(
        "s4",
        "F/ x φ ↔ ( ¬ ∀ x φ → ∀ x ¬ φ )",
        ref="nf4",
        note="nf4",
    )

    # 3bitr4ri: chain s2 (ph↔ps), s3 (ch↔ph), s4 (th↔ps) → th↔ch
    res = lb.ref(
        "res",
        "F/ x φ ↔ F/ x ¬ φ",
        s2,
        s3,
        s4,
        ref="3bitr4ri",
        note="3bitr4ri imbi1i, df-nf, nf4",
    )

    return lb.build(res)


def prove_nfnt(sys: System) -> Proof:
    """nfnt: F/ x φ → F/ x ¬ φ.

    One direction of nfnbi.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "nfnt")
    # nfnbi: F/ x φ ↔ F/ x ¬ φ
    s1 = lb.ref(
        "s1",
        "F/ x φ ↔ F/ x ¬ φ",
        ref="nfnbi",
        note="nfnbi",
    )
    # biimpi: infer the forward implication from the biconditional.
    res = lb.ref(
        "res",
        "F/ x φ → F/ x ¬ φ",
        s1,
        ref="biimpi",
        note="biimpi nfnbi",
    )
    return lb.build(res)


def prove_nfn(sys: System) -> Proof:
    """nfn: F/ x ¬ φ.

    Inference form of nfnt.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wnf wn nfnt ax-mp.
    """
    lb = ProofBuilder(sys, "nfn")
    h1 = lb.hyp("nfn.1", "F/ x φ")
    s1 = lb.ref("s1", "F/ x φ → F/ x ¬ φ", ref="nfnt", note="nfnt")
    res = lb.mp("res", h1, s1, note="MP nfnt, nfn.1")
    return lb.build(res)


def prove_nfnf1(sys: System) -> Proof:
    """nfnf1: F/ x F/ x φ.

    The variable x is not free in the statement "x is not free in φ".
    (Contributed by NM, 12-Mar-1993.)
    """
    lb = ProofBuilder(sys, "nfnf1")
    # df-nf: F/ x φ ↔ ( ∃ x φ → ∀ x φ )
    s1 = lb.ref(
        "s1",
        "F/ x φ ↔ ( ∃ x φ → ∀ x φ )",
        ref="df-nf",
        note="df-nf",
    )
    # nfe1: F/ x ∃ x φ
    s2 = lb.ref(
        "s2",
        "F/ x ∃ x φ",
        ref="nfe1",
        note="nfe1",
    )
    # nfa1: F/ x ∀ x φ
    s3 = lb.ref(
        "s3",
        "F/ x ∀ x φ",
        ref="nfa1",
        note="nfa1",
    )
    # nfim: F/ x ( ∃ x φ → ∀ x φ )
    s4 = lb.ref(
        "s4",
        "F/ x ( ∃ x φ → ∀ x φ )",
        s2,
        s3,
        ref="nfim",
        note="nfim nfe1, nfa1",
    )
    # nfxfr: F/ x F/ x φ
    res = lb.ref(
        "res",
        "F/ x F/ x φ",
        s1,
        s4,
        ref="nfxfr",
        note="nfxfr df-nf, nfim",
    )
    return lb.build(res)


def prove_nfnd(sys: System) -> Proof:
    """nfnd: φ → F/ x ¬ ψ.

    Deduction form of nfnt.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wnf wn nfnt syl.
    """
    lb = ProofBuilder(sys, "nfnd")
    h1 = lb.hyp("nfnd.1", "φ → F/ x ψ")
    s1 = lb.ref("s1", "F/ x ψ → F/ x ¬ ψ", ref="nfnt", note="nfnt")
    res = lb.ref("res", "φ → F/ x ¬ ψ", h1, s1, ref="syl", note="syl nfnd.1, nfnt")
    return lb.build(res)


def prove_nf5_1(sys: System) -> Proof:
    """nf5-1: ∀ x ( φ → ∀ x φ ) → F/ x φ.


    If φ implies its own universal quantification, then x is
    not free in φ.  (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wal wi wex exim hbe1a syl6 nfd.
    """
    lb = ProofBuilder(sys, "nf5-1")
    # exim: ∀ x ( φ → ψ ) → ( ∃ x φ → ∃ x ψ )
    # with ψ := ∀ x φ
    s1 = lb.ref(
        "s1",
        "∀ x ( φ → ∀ x φ ) → ( ∃ x φ → ∃ x ∀ x φ )",
        ref="exim",
        note="exim with ψ := ∀ x φ",
    )
    # hbe1a: ∃ x ∀ x φ → ∀ x φ
    s2 = lb.ref(
        "s2",
        "∃ x ∀ x φ → ∀ x φ",
        ref="hbe1a",
        note="hbe1a",
    )
    # syl6: chain s1 and s2
    s3 = lb.ref(
        "s3",
        "∀ x ( φ → ∀ x φ ) → ( ∃ x φ → ∀ x φ )",
        s1,
        s2,
        ref="syl6",
        note="syl6 exim, hbe1a",
    )
    # nfd: from (φ → (∃ x ψ → ∀ x ψ)) get (φ → F/ x ψ)
    res = lb.ref(
        "res",
        "∀ x ( φ → ∀ x φ ) → F/ x φ",
        s3,
        ref="nfd",
        note="nfd s3",
    )
    return lb.build(res)


def prove_nf5i(sys: System) -> Proof:
    """nf5i: F/ x φ.

    Inference form of nf5-1.  (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wal wi wnf nf5-1 mpg.
    """
    lb = ProofBuilder(sys, "nf5i")
    h1 = lb.hyp("nf5i.1", "φ → ∀ x φ")
    s1 = lb.ref(
        "s1",
        "∀ x ( φ → ∀ x φ ) → F/ x φ",
        ref="nf5-1",
        note="nf5-1",
    )
    res = lb.ref(
        "res",
        "F/ x φ",
        s1,
        h1,
        ref="mpg",
        note="mpg nf5-1, nf5i.1",
    )
    return lb.build(res)


def prove_nf5dh(sys: System) -> Proof:
    """nf5dh: φ → F/ x ψ.

    Deduction form of nf5-1.  (Contributed by NM, 5-Aug-1993.)
    set.mm proof: alrimih nf5-1 syl.
    """
    lb = ProofBuilder(sys, "nf5dh")
    hyp1 = lb.hyp("nf5dh.1", "φ → ∀ x φ")
    hyp2 = lb.hyp("nf5dh.2", "φ → ( ψ → ∀ x ψ )")

    # alrimih nf5dh.1, nf5dh.2: φ → ∀ x ( ψ → ∀ x ψ )
    s1 = lb.ref(
        "s1",
        "φ → ∀ x ( ψ → ∀ x ψ )",
        hyp1,
        hyp2,
        ref="alrimih",
        note="alrimih nf5dh.1, nf5dh.2",
    )

    # nf5-1: ∀ x ( ψ → ∀ x ψ ) → F/ x ψ
    s2 = lb.ref(
        "s2",
        "∀ x ( ψ → ∀ x ψ ) → F/ x ψ",
        ref="nf5-1",
        note="nf5-1",
    )

    # syl: φ → F/ x ψ
    res = lb.ref(
        "res",
        "φ → F/ x ψ",
        s1,
        s2,
        ref="syl",
        note="syl alrimih, nf5-1",
    )

    return lb.build(res)


def prove_nf5dv(sys: System) -> Proof:
    """nf5dv: φ → F/ x ψ.

    Deduction form of nf5dh.  (Contributed by NM, 5-Aug-1993.)
    set.mm proof: ax-5 nf5dh.
    """
    lb = ProofBuilder(sys, "nf5dv")
    hyp = lb.hyp("nf5dv.1", "φ → ( ψ → ∀ x ψ )")

    # ax-5: φ → ∀ x φ
    s1 = lb.ref(
        "s1",
        "φ → ∀ x φ",
        ref="ax-5",
        note="ax-5",
    )

    # nf5dh ax-5, nf5dv.1: φ → F/ x ψ
    res = lb.ref(
        "res",
        "φ → F/ x ψ",
        s1,
        hyp,
        ref="nf5dh",
        note="nf5dh ax-5, nf5dv.1",
    )

    return lb.build(res)


def prove_nf5d(sys: System) -> Proof:
    """nf5d: φ → F/ x ψ.

    Deduction form of nf5-1 using alrimi.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: alrimi nf5-1 syl.
    """
    lb = ProofBuilder(sys, "nf5d")
    hyp1 = lb.hyp("nf5d.1", "Ⅎ x φ")
    hyp2 = lb.hyp("nf5d.2", "φ → ( ψ → ∀ x ψ )")

    # alrimi nf5d.1, nf5d.2: φ → ∀ x ( ψ → ∀ x ψ )
    s1 = lb.ref(
        "s1",
        "φ → ∀ x ( ψ → ∀ x ψ )",
        hyp1,
        hyp2,
        ref="alrimi",
        note="alrimi nf5d.1, nf5d.2",
    )

    # nf5-1: ∀ x ( ψ → ∀ x ψ ) → F/ x ψ
    s2 = lb.ref(
        "s2",
        "∀ x ( ψ → ∀ x ψ ) → F/ x ψ",
        ref="nf5-1",
        note="nf5-1",
    )

    # syl: φ → F/ x ψ
    res = lb.ref(
        "res",
        "φ → F/ x ψ",
        s1,
        s2,
        ref="syl",
        note="syl alrimi, nf5-1",
    )

    return lb.build(res)


def prove_nfe1(sys: System) -> Proof:
    """nfe1: F/ x ∃ x φ.

    x is effectively not free in ∃ x φ because the quantifier binds it.
    (Contributed by NM, 12-Mar-1993.)
    """
    lb = ProofBuilder(sys, "nfe1")
    # hbe1: ∃ x φ → ∀ x ∃ x φ
    s1 = lb.ref(
        "s1",
        "∃ x φ → ∀ x ∃ x φ",
        ref="hbe1",
        note="hbe1",
    )
    # nf5i with hbe1 as hypothesis: F/ x ∃ x φ
    res = lb.ref(
        "res",
        "F/ x ∃ x φ",
        s1,
        ref="nf5i",
        note="nf5i hbe1",
    )
    return lb.build(res)


def prove_nfbiit(sys: System) -> Proof:
    """nfbiit: A. x ( φ ↔ ψ ) → ( F/ x φ ↔ F/ x ψ ).

    If two formulas are equivalent for all x, then "x is not free in φ"
    is equivalent to "x is not free in ψ".  (Contributed by NM, 19-Apr-1994.)
    set.mm proof: exbi albi imbi12d df-nf 3bitr4g.
    """
    lb = ProofBuilder(sys, "nfbiit")
    # exbi: A. x ( φ ↔ ψ ) → ( ∃ x φ ↔ ∃ x ψ )
    s1 = lb.ref(
        "s1",
        "A. x ( φ ↔ ψ ) → ( ∃ x φ ↔ ∃ x ψ )",
        ref="exbi",
        note="exbi",
    )
    # albi: A. x ( φ ↔ ψ ) → ( A. x φ ↔ A. x ψ )
    s2 = lb.ref(
        "s2",
        "A. x ( φ ↔ ψ ) → ( A. x φ ↔ A. x ψ )",
        ref="albi",
        note="albi",
    )
    # imbi12d: A. x ( φ ↔ ψ ) → ( ( ∃ x φ → A. x φ ) ↔ ( ∃ x ψ → A. x ψ ) )
    s3 = lb.ref(
        "s3",
        "A. x ( φ ↔ ψ ) → ( ( ∃ x φ → A. x φ ) ↔ ( ∃ x ψ → A. x ψ ) )",
        s1,
        s2,
        ref="imbi12d",
        note="imbi12d exbi, albi",
    )
    # df-nf: F/ x φ ↔ ( ∃ x φ → A. x φ )
    s4 = lb.ref(
        "s4",
        "F/ x φ ↔ ( ∃ x φ → A. x φ )",
        ref="df-nf",
        note="df-nf",
    )
    # df-nf: F/ x ψ ↔ ( ∃ x ψ → A. x ψ )
    s5 = lb.ref(
        "s5",
        "F/ x ψ ↔ ( ∃ x ψ → A. x ψ )",
        ref="df-nf",
        note="df-nf",
    )
    # 3bitr4g: A. x ( φ ↔ ψ ) → ( F/ x φ ↔ F/ x ψ )
    res = lb.ref(
        "res",
        "A. x ( φ ↔ ψ ) → ( F/ x φ ↔ F/ x ψ )",
        s3,
        s4,
        s5,
        ref="3bitr4g",
        note="3bitr4g imbi12d, df-nf, df-nf",
    )
    return lb.build(res)


def prove_nfbii(sys: System) -> Proof:
    """nfbii: F/ x φ ↔ F/ x ψ.

    If two formulas are equivalent, then the "x is not free in"
    predicate is equivalent.  Inference form of nfbiit.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wb wnf nfbiit mpg.
    """
    lb = ProofBuilder(sys, "nfbii")
    hyp = lb.hyp("nfbii.1", "φ ↔ ψ")
    s1 = lb.ref(
        "s1",
        "A. x ( φ ↔ ψ ) → ( F/ x φ ↔ F/ x ψ )",
        ref="nfbiit",
        note="nfbiit",
    )
    res = lb.ref(
        "res",
        "F/ x φ ↔ F/ x ψ",
        s1,
        hyp,
        ref="mpg",
        note="mpg nfbiit, nfbii.1",
    )
    return lb.build(res)


def prove_nfxfr(sys: System) -> Proof:
    """nfxfr: F/ x φ.

    A variant of nfbii.  If φ is equivalent to ψ, and x is not free in ψ,
    then x is not free in φ.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wnf nfbii mpbir.
    """
    lb = ProofBuilder(sys, "nfxfr")
    h1 = lb.hyp("nfbii.1", "φ ↔ ψ")
    h2 = lb.hyp("nfxfr.2", "F/ x ψ")
    # nfbii: F/ x φ ↔ F/ x ψ
    s1 = lb.ref(
        "s1",
        "F/ x φ ↔ F/ x ψ",
        h1,
        ref="nfbii",
        note="nfbii nfbii.1",
    )
    # mpbir: F/ x φ
    res = lb.ref(
        "res",
        "F/ x φ",
        h2,
        s1,
        ref="mpbir",
        note="mpbir nfxfr.2, nfbii",
    )
    return lb.build(res)


def prove_nfs1f(sys: System) -> Proof:
    """nfs1f: F/ x [ y x φ.

    If φ is not free in x, then the proper substitution of y for x
    in φ is also not free in x.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wsb sbf nfxfr.
    """
    lb = ProofBuilder(sys, "nfs1f")
    h1 = lb.hyp("nfs1f.1", "F/ x φ")
    # sbf: [ y x φ ↔ φ
    s1 = lb.ref(
        "s1",
        "[ y x φ ↔ φ",
        h1,
        ref="sbf",
        note="sbf nfs1f.1",
    )
    # nfxfr: F/ x [ y x φ
    res = lb.ref(
        "res",
        "F/ x [ y x φ",
        s1,
        h1,
        ref="nfxfr",
        note="nfxfr sbf, nfs1f.1",
    )
    return lb.build(res)


def prove_nfor(sys: System) -> Proof:
    """nfor: F/ x ( φ ∨ ψ ).

    If x is not free in φ and ψ, then x is not free in ( φ ∨ ψ ).
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wo wn wi df-or nfn nfim nfxfr.
    """
    lb = ProofBuilder(sys, "nfor")
    h1 = lb.hyp("nf.1", "F/ x φ")
    h2 = lb.hyp("nf.2", "F/ x ψ")
    # df-or: ( φ ∨ ψ ) ↔ ( ¬ φ → ψ )
    s1 = lb.ref(
        "s1",
        "( φ ∨ ψ ) ↔ ( ¬ φ → ψ )",
        ref="df-or",
        note="df-or",
    )
    # nfn: F/ x ¬ φ
    s2 = lb.ref(
        "s2",
        "F/ x ¬ φ",
        h1,
        ref="nfn",
        note="nfn nf.1",
    )
    # nfim: F/ x ( ¬ φ → ψ )
    s3 = lb.ref(
        "s3",
        "F/ x ( ¬ φ → ψ )",
        s2,
        h2,
        ref="nfim",
        note="nfim nfn, nf.2",
    )
    # nfxfr: F/ x ( φ ∨ ψ )
    res = lb.ref(
        "res",
        "F/ x ( φ ∨ ψ )",
        s1,
        s3,
        ref="nfxfr",
        note="nfxfr n, nfim",
    )
    return lb.build(res)


def prove_nf3or(sys: System) -> Proof:
    """nf3or: F/ x ( φ ∨ ψ ∨ χ ).

    If x is not free in φ, ψ, and χ, then x is not free in ( φ ∨ ψ ∨ χ ).
    (Contributed by NM, 22-Sep-1993.)
    set.mm proof: w3o wo df-3or nfor nfxfr.
    """
    lb = ProofBuilder(sys, "nf3or")
    h1 = lb.hyp("nf.1", "F/ x φ")
    h2 = lb.hyp("nf.2", "F/ x ψ")
    h3 = lb.hyp("nf.3", "F/ x χ")
    # nfor: F/ x ( φ ∨ ψ )
    s1 = lb.ref(
        "s1",
        "F/ x ( φ ∨ ψ )",
        h1,
        h2,
        ref="nfor",
        note="nfor nf.1, nf.2",
    )
    # nfor: F/ x ( ( φ ∨ ψ ) ∨ χ )
    s2 = lb.ref(
        "s2",
        "F/ x ( ( φ ∨ ψ ) ∨ χ )",
        s1,
        h3,
        ref="nfor",
        note="nfor nfor, nf.3",
    )
    # df-3or: ( φ ∨ ψ ∨ χ ) ↔ ( ( φ ∨ ψ ) ∨ χ )
    s3 = lb.ref(
        "s3",
        "( φ ∨ ψ ∨ χ ) ↔ ( ( φ ∨ ψ ) ∨ χ )",
        ref="df-3or",
        note="df-3or",
    )
    # nfxfr: F/ x ( φ ∨ ψ ∨ χ )
    res = lb.ref(
        "res",
        "F/ x ( φ ∨ ψ ∨ χ )",
        s3,
        s2,
        ref="nfxfr",
        note="nfxfr df-3or, nfor",
    )
    return lb.build(res)


def prove_nfnan(sys: System) -> Proof:
    """nfnan: F/ x ( φ ⊼ ψ ).

    If x is not free in φ and ψ, then x is not free in ( φ ⊼ ψ ).
    (Contributed by NM, 10-Jan-1993.)
    set.mm proof: wnan wa wn df-nan nfan nfn nfxfr.
    """
    lb = ProofBuilder(sys, "nfnan")
    h1 = lb.hyp("nfan.1", "F/ x φ")
    h2 = lb.hyp("nfan.2", "F/ x ψ")

    # nfan: F/ x ( φ ∧ ψ )
    s1 = lb.ref(
        "s1",
        "F/ x ( φ ∧ ψ )",
        h1,
        h2,
        ref="nfan",
        note="nfan nfan.1, nfan.2",
    )

    # nfn: F/ x ¬ ( φ ∧ ψ )
    s2 = lb.ref(
        "s2",
        "F/ x ¬ ( φ ∧ ψ )",
        s1,
        ref="nfn",
        note="nfn nfan",
    )

    # df-nan: ( φ ⊼ ψ ) ↔ ¬ ( φ ∧ ψ )
    s3 = lb.ref(
        "s3",
        "( φ ⊼ ψ ) ↔ ¬ ( φ ∧ ψ )",
        ref="df-nan",
        note="df-nan",
    )

    # nfxfr: F/ x ( φ ⊼ ψ )
    res = lb.ref(
        "res",
        "F/ x ( φ ⊼ ψ )",
        s3,
        s2,
        ref="nfxfr",
        note="nfxfr df-nan, nfn",
    )

    return lb.build(res)


def prove_nfbidv(sys: System) -> Proof:
    """nfbidv: φ → ( Ⅎ x ψ ↔ Ⅎ x χ ).

    Deduction form of the "not free" predicate: if ψ and χ are equivalent
    given φ, then "x is not free in ψ" is equivalent to "x is not free in χ"
    given φ.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: exbidv albidv imbi12d df-nf 3bitr4g.
    """
    lb = ProofBuilder(sys, "nfbidv")
    hyp = lb.hyp("albidv.1", "φ → ( ψ ↔ χ )")
    # exbidv: φ → ( ∃ x ψ ↔ ∃ x χ )
    s1 = lb.ref(
        "s1",
        "φ → ( ∃ x ψ ↔ ∃ x χ )",
        hyp,
        ref="exbidv",
        note="exbidv albidv.1",
    )
    # albidv: φ → ( ∀ x ψ ↔ ∀ x χ )
    s2 = lb.ref(
        "s2",
        "φ → ( ∀ x ψ ↔ ∀ x χ )",
        hyp,
        ref="albidv",
        note="albidv albidv.1",
    )
    # imbi12d: φ → ( ( ∃ x ψ → ∀ x ψ ) ↔ ( ∃ x χ → ∀ x χ ) )
    s3 = lb.ref(
        "s3",
        "φ → ( ( ∃ x ψ → ∀ x ψ ) ↔ ( ∃ x χ → ∀ x χ ) )",
        s1,
        s2,
        ref="imbi12d",
        note="imbi12d exbidv, albidv",
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


def prove_nfxfrd(sys: System) -> Proof:
    """nfxfrd: χ → Ⅎ x φ.

    Deduction form of nfbii.  If φ is equivalent to ψ, and χ implies that
    x is not free in ψ, then χ implies that x is not free in φ.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wnf nfbii sylibr.
    """
    lb = ProofBuilder(sys, "nfxfrd")
    h1 = lb.hyp("nfbii.1", "φ ↔ ψ")
    h2 = lb.hyp("nfxfrd.2", "χ → F/ x ψ")
    # nfbii: Ⅎ x φ ↔ Ⅎ x ψ
    s1 = lb.ref(
        "s1",
        "F/ x φ ↔ F/ x ψ",
        h1,
        ref="nfbii",
        note="nfbii nfbii.1",
    )
    # sylibr: χ → Ⅎ x φ
    res = lb.ref(
        "res",
        "χ → F/ x φ",
        h2,
        s1,
        ref="sylibr",
        note="sylibr nfxfrd.2, nfbii",
    )
    return lb.build(res)


def prove_nfand(sys: System) -> Proof:
    """nfand: φ → F/ x ( ψ ∧ χ ).

    Deduction form of the not-free property for conjunction.
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "nfand")
    h1 = lb.hyp("nfand.1", "φ → F/ x ψ")
    h2 = lb.hyp("nfand.2", "φ → F/ x χ")

    # df-an: ( ψ ∧ χ ) ↔ ¬ ( ψ → ¬ χ )
    s1 = lb.ref(
        "s1",
        "( ψ ∧ χ ) ↔ ¬ ( ψ → ¬ χ )",
        ref="df-an",
        note="df-an",
    )

    # nfnd nfand.2: φ → F/ x ¬ χ
    s2 = lb.ref(
        "s2",
        "φ → F/ x ¬ χ",
        h2,
        ref="nfnd",
        note="nfnd nfand.2",
    )

    # nfimd nfand.1, s2: φ → F/ x ( ψ → ¬ χ )
    s3 = lb.ref(
        "s3",
        "φ → F/ x ( ψ → ¬ χ )",
        h1,
        s2,
        ref="nfimd",
        note="nfimd nfand.1, s2",
    )

    # nfnd s3: φ → F/ x ¬ ( ψ → ¬ χ )
    s4 = lb.ref(
        "s4",
        "φ → F/ x ¬ ( ψ → ¬ χ )",
        s3,
        ref="nfnd",
        note="nfnd s3",
    )

    # nfxfrd df-an, s4: φ → F/ x ( ψ ∧ χ )
    res = lb.ref(
        "res",
        "φ → F/ x ( ψ ∧ χ )",
        s1,
        s4,
        ref="nfxfrd",
        note="nfxfrd df-an, s4",
    )

    return lb.build(res)


def prove_nfan(sys: System) -> Proof:
    """nfan: F/ x ( φ ∧ ψ ).

    Inference form of nfand — if two formulas are each not-free in x,
    their conjunction is also not-free in x.
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "nfan")
    nf1 = lb.hyp("nfan.1", "F/ x φ")
    nf2 = lb.hyp("nfan.2", "F/ x ψ")

    # a1i nfan.1: ⊤ → F/ x φ
    s1 = lb.ref(
        "s1",
        "⊤ → F/ x φ",
        nf1,
        ref="a1i",
        note="a1i nfan.1",
    )

    # a1i nfan.2: ⊤ → F/ x ψ
    s2 = lb.ref(
        "s2",
        "⊤ → F/ x ψ",
        nf2,
        ref="a1i",
        note="a1i nfan.2",
    )

    # nfand s1, s2: ⊤ → F/ x ( φ ∧ ψ )
    s3 = lb.ref(
        "s3",
        "⊤ → F/ x ( φ ∧ ψ )",
        s1,
        s2,
        ref="nfand",
        note="nfand s1, s2",
    )

    # mptru s3: F/ x ( φ ∧ ψ )
    res = lb.ref(
        "res",
        "F/ x ( φ ∧ ψ )",
        s3,
        ref="mptru",
        note="mptru s3",
    )

    return lb.build(res)


def prove_hban(sys: System) -> Proof:
    """hban: ( φ ∧ ψ ) → ∀ x ( φ ∧ ψ ).

    From φ → ∀ x φ and ψ → ∀ x ψ, conclude ( φ ∧ ψ ) → ∀ x ( φ ∧ ψ ).
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "hban")
    h1 = lb.hyp("hban.1", "φ → ∀ x φ")
    h2 = lb.hyp("hban.2", "ψ → ∀ x ψ")

    # nf5i from hban.1: Ⅎ x φ
    s1 = lb.ref(
        "s1",
        "Ⅎ x φ",
        h1,
        ref="nf5i",
        note="nf5i hban.1",
    )

    # nf5i from hban.2: Ⅎ x ψ
    s2 = lb.ref(
        "s2",
        "Ⅎ x ψ",
        h2,
        ref="nf5i",
        note="nf5i hban.2",
    )

    # nfan from s1 and s2: Ⅎ x ( φ ∧ ψ )
    s3 = lb.ref(
        "s3",
        "Ⅎ x ( φ ∧ ψ )",
        s1,
        s2,
        ref="nfan",
        note="nfan nf5i, nf5i",
    )

    # nf5ri from s3: ( φ ∧ ψ ) → ∀ x ( φ ∧ ψ )
    res = lb.ref(
        "res",
        "( φ ∧ ψ ) → ∀ x ( φ ∧ ψ )",
        s3,
        ref="nf5ri",
        note="nf5ri nfan",
    )

    return lb.build(res)


def prove_nf3and(sys: System) -> Proof:
    """nf3and: φ → F/ x ( ψ ∧ χ ∧ θ ).

    Deduction form of the not-free property for ternary conjunction.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "nf3and")
    h1 = lb.hyp("nfand.1", "φ → F/ x ψ")
    h2 = lb.hyp("nfand.2", "φ → F/ x χ")
    h3 = lb.hyp("nfand.3", "φ → F/ x θ")

    # df-3an: ( ψ ∧ χ ∧ θ ) ↔ ( ( ψ ∧ χ ) ∧ θ )
    s1 = lb.ref(
        "s1",
        "( ψ ∧ χ ∧ θ ) ↔ ( ( ψ ∧ χ ) ∧ θ )",
        ref="df-3an",
        note="df-3an",
    )

    # nfand nfand.1, nfand.2: φ → F/ x ( ψ ∧ χ )
    s2 = lb.ref(
        "s2",
        "φ → F/ x ( ψ ∧ χ )",
        h1,
        h2,
        ref="nfand",
        note="nfand nfand.1, nfand.2",
    )

    # nfand s2, nfand.3: φ → F/ x ( ( ψ ∧ χ ) ∧ θ )
    s3 = lb.ref(
        "s3",
        "φ → F/ x ( ( ψ ∧ χ ) ∧ θ )",
        s2,
        h3,
        ref="nfand",
        note="nfand s2, nfand.3",
    )

    # nfxfrd n, s3: φ → F/ x ( ψ ∧ χ ∧ θ )
    res = lb.ref(
        "res",
        "φ → F/ x ( ψ ∧ χ ∧ θ )",
        s1,
        s3,
        ref="nfxfrd",
        note="nfxfrd n, s3",
    )

    return lb.build(res)


def prove_nf3an(sys: System) -> Proof:
    """nf3an: F/ x ( φ ∧ ψ ∧ χ ).

    If x is not free in φ, ψ, and χ, then x is not free in their
    ternary conjunction.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: w3a wa df-3an nfan nfxfr.
    """
    lb = ProofBuilder(sys, "nf3an")
    nf1 = lb.hyp("nfan.1", "F/ x φ")
    nf2 = lb.hyp("nfan.2", "F/ x ψ")
    nf3 = lb.hyp("nfan.3", "F/ x χ")

    # df-3an: ( φ ∧ ψ ∧ χ ) ↔ ( ( φ ∧ ψ ) ∧ χ )
    s1 = lb.ref(
        "s1",
        "( φ ∧ ψ ∧ χ ) ↔ ( ( φ ∧ ψ ) ∧ χ )",
        ref="df-3an",
        note="df-3an",
    )

    # nfan nfan.1, nfan.2: F/ x ( φ ∧ ψ )
    s2 = lb.ref(
        "s2",
        "F/ x ( φ ∧ ψ )",
        nf1,
        nf2,
        ref="nfan",
        note="nfan nfan.1, nfan.2",
    )

    # nfan s2, nfan.3: F/ x ( ( φ ∧ ψ ) ∧ χ )
    s3 = lb.ref(
        "s3",
        "F/ x ( ( φ ∧ ψ ) ∧ χ )",
        s2,
        nf3,
        ref="nfan",
        note="nfan s2, nfan.3",
    )

    # nfxfr s1, s3: F/ x ( φ ∧ ψ ∧ χ )
    res = lb.ref(
        "res",
        "F/ x ( φ ∧ ψ ∧ χ )",
        s1,
        s3,
        ref="nfxfr",
        note="nfxfr df-3an, nfan",
    )

    return lb.build(res)


def prove_nfbid(sys: System) -> Proof:
    """nfbid: φ → F/ x ( ψ ↔ χ ).

    Deduction form of the not-free property for biconditional.
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "nfbid")
    h1 = lb.hyp("nfbid.1", "φ → F/ x ψ")
    h2 = lb.hyp("nfbid.2", "φ → F/ x χ")

    # dfbi2: ( ψ ↔ χ ) ↔ ( ( ψ → χ ) ∧ ( χ → ψ ) )
    s1 = lb.ref(
        "s1",
        "( ψ ↔ χ ) ↔ ( ( ψ → χ ) ∧ ( χ → ψ ) )",
        ref="dfbi2",
        note="dfbi2",
    )

    # nfimd nfbid.1, nfbid.2: φ → F/ x ( ψ → χ )
    s2 = lb.ref(
        "s2",
        "φ → F/ x ( ψ → χ )",
        h1,
        h2,
        ref="nfimd",
        note="nfimd nfbid.1, nfbid.2",
    )

    # nfimd nfbid.2, nfbid.1: φ → F/ x ( χ → ψ )
    s3 = lb.ref(
        "s3",
        "φ → F/ x ( χ → ψ )",
        h2,
        h1,
        ref="nfimd",
        note="nfimd nfbid.2, nfbid.1",
    )

    # nfand s2, s3: φ → F/ x ( ( ψ → χ ) ∧ ( χ → ψ ) )
    s4 = lb.ref(
        "s4",
        "φ → F/ x ( ( ψ → χ ) ∧ ( χ → ψ ) )",
        s2,
        s3,
        ref="nfand",
        note="nfand s2, s3",
    )

    # nfxfrd dfbi2, s4: φ → F/ x ( ψ ↔ χ )
    res = lb.ref(
        "res",
        "φ → F/ x ( ψ ↔ χ )",
        s1,
        s4,
        ref="nfxfrd",
        note="nfxfrd dfbi2, s4",
    )

    return lb.build(res)


def prove_nfbi(sys: System) -> Proof:
    """nfbi: F/ x ( φ ↔ ψ ).

    Inference form of nfbid — if two formulas are each not-free in x,
    their biconditional is also not-free in x.
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "nfbi")
    nf1 = lb.hyp("nf.1", "F/ x φ")
    nf2 = lb.hyp("nf.2", "F/ x ψ")

    # a1i nf.1: T. → F/ x φ
    s1 = lb.ref(
        "s1",
        "T. → F/ x φ",
        nf1,
        ref="a1i",
        note="a1i nf.1",
    )

    # a1i nf.2: T. → F/ x ψ
    s2 = lb.ref(
        "s2",
        "T. → F/ x ψ",
        nf2,
        ref="a1i",
        note="a1i nf.2",
    )

    # nfbid s1, s2: T. → F/ x ( φ ↔ ψ )
    s3 = lb.ref(
        "s3",
        "T. → F/ x ( φ ↔ ψ )",
        s1,
        s2,
        ref="nfbid",
        note="nfbid s1, s2",
    )

    # mptru s3: F/ x ( φ ↔ ψ )
    res = lb.ref(
        "res",
        "F/ x ( φ ↔ ψ )",
        s3,
        ref="mptru",
        note="mptru s3",
    )

    return lb.build(res)


def prove_mpg(sys: System) -> Proof:
    """mpg: ps.

    Hyp 1: ( A. x ph -> ps )
    Hyp 2: ph
    Concl: ps

    An inference from an implication involving a universal quantifier.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wal ax-gen mpg.1 mpg.2.
    """
    lb = ProofBuilder(sys, "mpg")
    h1 = lb.hyp("mpg.1", "( A. x ph -> ps )")
    h2 = lb.hyp("mpg.2", "ph")
    s1 = lb.ref("s1", "A. x ph", h2, ref="ax-gen", note="ax-gen mpg.2")
    res = lb.mp("res", s1, h1, "MP ax-gen, mpg.1")
    return lb.build(res)


def prove_mpgbi(sys: System) -> Proof:
    """mpgbi: ps.

    Hyp 1: ( A. x ph <-> ps )
    Hyp 2: ph
    Concl: ps

    An inference from a biconditional involving a universal quantifier.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wal ax-gen mpbi.
    """
    lb = ProofBuilder(sys, "mpgbi")
    h1 = lb.hyp("mpgbi.1", "( A. x ph <-> ps )")
    h2 = lb.hyp("mpgbi.2", "ph")
    s1 = lb.ref("s1", "A. x ph", h2, ref="ax-gen", note="ax-gen mpgbi.2")
    res = lb.ref("res", "ps", s1, h1, ref="mpbi", note="mpbi s1, mpgbi.1")
    return lb.build(res)


def prove_mpgbir(sys: System) -> Proof:
    """mpgbir: ph.

    Hyp 1: ( ph <-> A. x ps )
    Hyp 2: ps
    Concl: ph

    An inference from a biconditional involving generalization.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wal ax-gen mpbir.
    """
    lb = ProofBuilder(sys, "mpgbir")
    h1 = lb.hyp("mpgbir.1", "( ph <-> A. x ps )")
    h2 = lb.hyp("mpgbir.2", "ps")
    s1 = lb.ref("s1", "A. x ps", h2, ref="ax-gen", note="ax-gen mpgbir.2")
    res = lb.ref("res", "ph", s1, h1, ref="mpbir", note="mpbir s1, mpgbir.1")
    return lb.build(res)


def prove_alfal(sys: System) -> Proof:
    """alfal: A. x -. F..

    The false constant is always false, for all x.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wfal wn fal ax-gen.
    """
    lb = ProofBuilder(sys, "alfal")
    s_fal = lb.ref("s_fal", "-. F.", ref="fal", note="fal")
    s_gen = lb.ref("s_gen", "-. F. → A. x -. F.", ref="ax-5", note="ax-5 — ax-gen")
    res = lb.mp("res", s_fal, s_gen, note="MP fal, ax-5")
    return lb.build(res)


def prove_sbtlem(sys: System) -> Proof:
    """sbtlem: ∀ y ( y = t → ∀ x ( x = y → φ ) ).

    From φ, apply a1i with antecedent x = y, generalize with ax-gen,
    then apply a1i with antecedent y = t and generalize with ax-gen again.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: weq wi wal a1i ax-gen.
    """
    lb = ProofBuilder(sys, "sbtlem")
    hyp = lb.hyp("sbtlem.1", "φ")
    # a1i: φ → ( x = y → φ ), mp with hyp gives x = y → φ
    s1 = lb.ref("s1", "x = y → φ", hyp, ref="a1i", note="a1i sbtlem.1")
    # ax-gen: ∀ x ( x = y → φ )
    s2 = lb.ref("s2", "∀ x ( x = y → φ )", s1, ref="ax-gen", note="ax-gen")
    # a1i: ( ∀ x ( x = y → φ ) ) → ( y = t → ∀ x ( x = y → φ ) )
    s3 = lb.ref("s3", "y = t → ∀ x ( x = y → φ )", s2, ref="a1i", note="a1i")
    # ax-gen: ∀ y ( y = t → ∀ x ( x = y → φ ) )
    res = lb.ref("res", "∀ y ( y = t → ∀ x ( x = y → φ ) )", s3, ref="ax-gen", note="ax-gen")
    return lb.build(res)


def prove_sbt(sys: System) -> Proof:
    """sbt: [ t / x ] φ.

    If φ is provable, then so is [ t / x ] φ (substitution of t for x).
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wsb weq wi wal wa sbtlem pm3.2i df-sb mpbir.
    """
    lb = ProofBuilder(sys, "sbt")
    hyp = lb.hyp("sbtlem.1", "φ")
    # sbtlem with dummy variable y: ∀ y ( y = t → ∀ x ( x = y → φ ) )
    s1 = lb.ref(
        "s1",
        "∀ y ( y = t → ∀ x ( x = y → φ ) )",
        hyp,
        ref="sbtlem",
        note="sbtlem with y",
    )
    # sbtlem with dummy variable z: ∀ z ( z = t → ∀ x ( x = z → φ ) )
    s2 = lb.ref(
        "s2",
        "∀ z ( z = t → ∀ x ( x = z → φ ) )",
        hyp,
        ref="sbtlem",
        note="sbtlem with z",
    )
    # pm3.2i: combine into conjunction
    s3 = lb.ref(
        "s3",
        "( ∀ y ( y = t → ∀ x ( x = y → φ ) ) ∧ ∀ z ( z = t → ∀ x ( x = z → φ ) ) )",
        s1,
        s2,
        ref="pm3.2i",
        note="pm3.2i",
    )
    # df-sb: biconditional definition of proper substitution
    s4 = lb.ref(
        "s4",
        "[ t / x ] φ ↔ ( ∀ y ( y = t → ∀ x ( x = y → φ ) ) ∧ ∀ z ( z = t → ∀ x ( x = z → φ ) ) )",
        ref="df-sb",
        note="df-sb",
    )
    # mpbir: conclude [ t / x ] φ from the biconditional and the conjunction
    res = lb.ref(
        "res",
        "[ t / x ] φ",
        s3,
        s4,
        ref="mpbir",
        note="mpbir df-sb, pm3.2i",
    )
    return lb.build(res)


def prove_sbtALT(sys: System) -> Proof:
    """sbtALT: [ y / x ] φ.

    Alternate proof of sbt using stdpc4 instead of sbtlem.
    (Contributed by NM, 19-Apr-1994.)
    (Proof modification is discouraged.) (New usage is discouraged.)
    set.mm proof: wsb stdpc4 mpg.
    """
    lb = ProofBuilder(sys, "sbtALT")
    hyp = lb.hyp("sbtALT.1", "φ")
    # stdpc4: ∀ x φ → [ y x φ
    s1 = lb.ref(
        "s1",
        "∀ x φ → [ y x φ",
        ref="stdpc4",
        note="stdpc4 with t = y",
    )
    # mpg: from (∀ x φ → [ y x φ) and sbtALT.1 φ, derive [ y x φ
    res = lb.ref(
        "res",
        "[ y x φ",
        s1,
        hyp,
        ref="mpg",
        note="mpg stdpc4, sbtALT.1",
    )
    return lb.build(res)


def prove_sbtru(sys: System) -> Proof:
    """sbtru: [ y / x ] ⊤.

    Substitution of a set variable for another in truth is provable.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wtru tru sbt.
    """
    lb = ProofBuilder(sys, "sbtru")
    tru_step = lb.ref("tru_step", "⊤", ref="tru", note="tru")
    res = lb.ref("res", "[ y x ⊤", tru_step, ref="sbt", note="sbt")
    return lb.build(res)


def prove_speimfw(sys: System) -> Proof:
    """speimfw: ¬ ∀ x ¬ x = y → ( ∀ x φ → ∃ x ψ ).

    If x = y implies (φ → ψ), then ¬ ∀ x ¬ x = y implies
    (∀ x φ → ∃ x ψ).
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: weq wn wal wex df-ex biimpri com12 aleximi syl5com.
    """
    lb = ProofBuilder(sys, "speimfw")
    hyp = lb.hyp("speimfw.2", "x = y → ( φ → ψ )")

    # df-ex with ph := x = y: (∃ x x = y ↔ ¬ ∀ x ¬ x = y)
    s1 = lb.ref(
        "s1",
        "∃ x x = y ↔ ¬ ∀ x ¬ x = y",
        ref="df-ex",
        note="df-ex",
    )

    # biimpri s1: (¬ ∀ x ¬ x = y → ∃ x x = y)
    s2 = lb.ref(
        "s2",
        "¬ ∀ x ¬ x = y → ∃ x x = y",
        s1,
        ref="biimpri",
        note="biimpri",
    )

    # com12 hyp: (φ → (x = y → ψ))
    s3 = lb.ref(
        "s3",
        "φ → ( x = y → ψ )",
        hyp,
        ref="com12",
        note="com12",
    )

    # aleximi s3: (∀ x φ → (∃ x x = y → ∃ x ψ))
    s4 = lb.ref(
        "s4",
        "∀ x φ → ( ∃ x x = y → ∃ x ψ )",
        s3,
        ref="aleximi",
        note="aleximi",
    )

    # syl5com s2, s4: (¬ ∀ x ¬ x = y → (∀ x φ → ∃ x ψ))
    res = lb.ref(
        "res",
        "¬ ∀ x ¬ x = y → ( ∀ x φ → ∃ x ψ )",
        s2,
        s4,
        ref="syl5com",
        note="syl5com",
    )

    return lb.build(res)


def prove_speimfwALT(sys: System) -> Proof:
    """speimfwALT: ¬ ∀ x ¬ x = y → ( ∀ x φ → ∃ x ψ ).

    Alternative proof of speimfw using 19.35 and 3imtr3i.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: weq wex wi wn wal eximi df-ex 19.35 3imtr3i.
    """
    lb = ProofBuilder(sys, "speimfwALT")
    hyp = lb.hyp("speimfw.2", "x = y → ( φ → ψ )")

    # eximi: ( x = y → ( φ → ψ ) ) → ( ∃ x x = y → ∃ x ( φ → ψ ) )
    s1 = lb.ref(
        "s1",
        "∃ x x = y → ∃ x ( φ → ψ )",
        hyp,
        ref="eximi",
        note="eximi",
    )

    # df-ex: ∃ x x = y ↔ ¬ ∀ x ¬ x = y
    s2 = lb.ref(
        "s2",
        "∃ x x = y ↔ ¬ ∀ x ¬ x = y",
        ref="df-ex",
        note="df-ex",
    )

    # 19.35: ∃ x ( φ → ψ ) ↔ ( ∀ x φ → ∃ x ψ )
    s3 = lb.ref(
        "s3",
        "∃ x ( φ → ψ ) ↔ ( ∀ x φ → ∃ x ψ )",
        ref="19.35",
        note="19.35",
    )

    # 3imtr3i combines the three hypotheses
    res = lb.ref(
        "res",
        "¬ ∀ x ¬ x = y → ( ∀ x φ → ∃ x ψ )",
        s1,
        s2,
        s3,
        ref="3imtr3i",
        note="3imtr3i",
    )

    return lb.build(res)


def prove_spimfw(sys: System) -> Proof:
    """spimfw: ¬ ∀ x ¬ x = y → ( ∀ x φ → ψ ).

    If ¬ ψ → ∀ x ¬ ψ and x = y → ( φ → ψ ), then
    ¬ ∀ x ¬ x = y → ( ∀ x φ → ψ ).
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: weq wn wal wex speimfw df-ex con1i sylbi syl6.
    """
    lb = ProofBuilder(sys, "spimfw")
    h1 = lb.hyp("spimfw.1", "¬ ψ → ∀ x ¬ ψ")
    h2 = lb.hyp("spimfw.2", "x = y → ( φ → ψ )")

    # speimfw with spimfw.2: ¬ ∀ x ¬ x = y → (∀ x φ → ∃ x ψ)
    s1 = lb.ref(
        "s1",
        "¬ ∀ x ¬ x = y → ( ∀ x φ → ∃ x ψ )",
        h2,
        ref="speimfw",
        note="speimfw",
    )

    # df-ex: ∃ x ψ ↔ ¬ ∀ x ¬ ψ
    s2 = lb.ref(
        "s2",
        "∃ x ψ ↔ ¬ ∀ x ¬ ψ",
        ref="df-ex",
        note="df-ex",
    )

    # con1i spimfw.1: ¬ ∀ x ¬ ψ → ψ
    s3 = lb.ref(
        "s3",
        "¬ ∀ x ¬ ψ → ψ",
        h1,
        ref="con1i",
        note="con1i",
    )

    # sylbi df-ex, con1i: ∃ x ψ → ψ
    s4 = lb.ref(
        "s4",
        "∃ x ψ → ψ",
        s2,
        s3,
        ref="sylbi",
        note="sylbi df-ex, con1i",
    )

    # syl6 speimfw, sylbi: ¬ ∀ x ¬ x = y → (∀ x φ → ψ)
    res = lb.ref(
        "res",
        "¬ ∀ x ¬ x = y → ( ∀ x φ → ψ )",
        s1,
        s4,
        ref="syl6",
        note="syl6 speimfw, sylbi",
    )

    return lb.build(res)


def prove_spimw(sys: System) -> Proof:
    """spimw: ∀ x φ → ψ.

    If ¬ ψ → ∀ x ¬ ψ and x = y → ( φ → ψ ), then ∀ x φ → ψ.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: weq wn wal wi ax6v spimfw ax-mp.
    """
    lb = ProofBuilder(sys, "spimw")
    hyp1 = lb.hyp("spimw.1", "¬ ψ → ∀ x ¬ ψ")
    hyp2 = lb.hyp("spimw.2", "x = y → ( φ → ψ )")

    # spimfw with spimw.1 and spimw.2: ¬ ∀ x ¬ x = y → ( ∀ x φ → ψ )
    s1 = lb.ref(
        "s1",
        "¬ ∀ x ¬ x = y → ( ∀ x φ → ψ )",
        hyp1,
        hyp2,
        ref="spimfw",
        note="spimfw",
    )

    # ax6v: ¬ ∀ x ¬ x = y
    s2 = lb.ref(
        "s2",
        "¬ ∀ x ¬ x = y",
        ref="ax6v",
        note="ax6v",
    )

    # mp: from ax6v and spimfw, derive ∀ x φ → ψ
    res = lb.mp("res", s2, s1, note="mp ax6v, spimfw")

    return lb.build(res)


def prove_spimew(sys: System) -> Proof:
    """spimew: φ → ∃ x ψ.

    If φ → ∀ x φ and x = y → (φ → ψ), then φ → ∃ x ψ.
    """
    lb = ProofBuilder(sys, "spimew")
    hyp1 = lb.hyp("spimew.1", "φ → ∀ x φ")
    hyp2 = lb.hyp("spimew.2", "x = y → ( φ → ψ )")

    # speimfw with spimew.2: ¬ ∀ x ¬ x = y → (∀ x φ → ∃ x ψ)
    s1 = lb.ref(
        "s1",
        "¬ ∀ x ¬ x = y → ( ∀ x φ → ∃ x ψ )",
        hyp2,
        ref="speimfw",
        note="speimfw",
    )

    # ax6v: ¬ ∀ x ¬ x = y
    s2 = lb.ref(
        "s2",
        "¬ ∀ x ¬ x = y",
        ref="ax6v",
        note="ax6v",
    )

    # mpsyl: with mpsyl.1 = ax6v, mpsyl.2 = spimew.1, mpsyl.3 = speimfw
    # Concl: φ → ∃ x ψ
    res = lb.ref(
        "res",
        "φ → ∃ x ψ",
        s2,
        hyp1,
        s1,
        ref="mpsyl",
        note="mpsyl ax6v, spimew.1, speimfw",
    )

    return lb.build(res)


def prove_spimevw(sys: System) -> Proof:
    """spimevw: φ → ∃ x ψ.

    Variant of spimew where the first hypothesis is replaced by ax-5.
    """
    lb = ProofBuilder(sys, "spimevw")
    hyp = lb.hyp("spimevw.1", "x = y → ( φ → ψ )")

    # ax-5: φ → ∀ x φ
    s1 = lb.ref(
        "s1",
        "φ → ∀ x φ",
        ref="ax-5",
        note="ax-5",
    )

    # spimew: φ → ∃ x ψ
    res = lb.ref(
        "res",
        "φ → ∃ x ψ",
        s1,
        hyp,
        ref="spimew",
        note="spimew ax-5, spimevw.1",
    )

    return lb.build(res)


def prove_spimvw(sys: System) -> Proof:
    """spimvw: ∀ x φ → ψ.

    Variant of spimw where the first hypothesis is replaced by ax-5.
    """
    lb = ProofBuilder(sys, "spimvw")
    hyp = lb.hyp("spimvw.1", "x = y → ( φ → ψ )")

    # ax-5: ¬ ψ → ∀ x ¬ ψ
    s1 = lb.ref(
        "s1",
        "¬ ψ → ∀ x ¬ ψ",
        ref="ax-5",
        note="ax-5",
    )

    # spimw: ∀ x φ → ψ
    res = lb.ref(
        "res",
        "∀ x φ → ψ",
        s1,
        hyp,
        ref="spimw",
        note="spimw ax-5, spimvw.1",
    )

    return lb.build(res)


def prove_spvv(sys: System) -> Proof:
    """spvv: ∀ x φ → ψ.

    Variant of spv where the first hypothesis is replaced by ax-5.
    """
    lb = ProofBuilder(sys, "spvv")
    hyp = lb.hyp("spvv.1", "x = y → ( φ ↔ ψ )")

    # biimpd: x = y → ( φ → ψ )
    s1 = lb.ref(
        "s1",
        "x = y → ( φ → ψ )",
        hyp,
        ref="biimpd",
        note="biimpd spvv.1",
    )

    # spimvw: ∀ x φ → ψ
    res = lb.ref(
        "res",
        "∀ x φ → ψ",
        s1,
        ref="spimvw",
        note="spimvw biimpd",
    )

    return lb.build(res)


def prove_chvarvv(sys: System) -> Proof:
    """chvarvv: ψ.

    Change bound variable using ax-5. From spvv and mpg.
    (Contributed by NM, 10-Jan-1993.)
    set.mm proof: spvv mpg.
    """
    lb = ProofBuilder(sys, "chvarvv")
    h1 = lb.hyp("chvarvv.1", "x = y → ( φ ↔ ψ )")
    h2 = lb.hyp("chvarvv.2", "φ")

    # spvv with chvarvv.1: ∀ x φ → ψ
    s1 = lb.ref(
        "s1",
        "∀ x φ → ψ",
        h1,
        ref="spvv",
        note="spvv chvarvv.1",
    )

    # mpg with s1 as mpg.1 and chvarvv.2 as mpg.2: ψ
    res = lb.ref(
        "res",
        "ψ",
        s1,
        h2,
        ref="mpg",
        note="mpg spvv, chvarvv.2",
    )

    return lb.build(res)


def prove_speiv(sys: System) -> Proof:
    """speiv: ∃ x φ.

    From ψ and x = y → (ψ → φ), conclude ∃ x φ.
    """
    lb = ProofBuilder(sys, "speiv")
    hyp1 = lb.hyp("speiv.1", "x = y → ( ψ → φ )")
    hyp2 = lb.hyp("speiv.2", "ψ")

    # hbth: ψ → ∀ x ψ
    s1 = lb.ref(
        "s1",
        "ψ → ∀ x ψ",
        hyp2,
        ref="hbth",
        note="hbth speiv.2",
    )

    # spimew: ψ → ∃ x φ
    s2 = lb.ref(
        "s2",
        "ψ → ∃ x φ",
        s1,
        hyp1,
        ref="spimew",
        note="spimew",
    )

    # ax-mp: ∃ x φ
    res = lb.mp("res", hyp2, s2, note="ax-mp speiv.2, spimew")

    return lb.build(res)


def prove_speivw(sys: System) -> Proof:
    """speivw: ∃ x φ.

    From x = y → (φ ↔ ψ) and ψ, conclude ∃ x φ.
    """
    lb = ProofBuilder(sys, "speivw")
    hyp1 = lb.hyp("speivw.1", "x = y → ( φ ↔ ψ )")
    hyp2 = lb.hyp("speivw.2", "ψ")

    # biimprd: x = y → ( ψ → φ )
    s1 = lb.ref(
        "s1",
        "x = y → ( ψ → φ )",
        hyp1,
        ref="biimprd",
        note="biimprd speivw.1",
    )

    # speiv: ∃ x φ
    res = lb.ref(
        "res",
        "∃ x φ",
        s1,
        hyp2,
        ref="speiv",
        note="speiv",
    )

    return lb.build(res)


def prove_spsbe(sys: System) -> Proof:
    """spsbe: [ t / x ] φ → ∃ x φ.

    From substitution to existential quantification.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wsb weq wi wal wex dfsbimp alequexv exsbim 3syl.
    """
    lb = ProofBuilder(sys, "spsbe")
    # dfsbimp: [ t / x ] φ → ∀ y ( y = t → ∀ x ( x = y → φ ) )
    s1 = lb.ref(
        "s1",
        "[ t x φ → ∀ y ( y = t → ∀ x ( x = y → φ ) )",
        ref="dfsbimp",
        note="dfsbimp",
    )
    # alequexv with x:=y, y:=t, φ:=∀ x ( x = y → φ ):
    #   ∀ y ( y = t → ∀ x ( x = y → φ ) ) → ∃ y ∀ x ( x = y → φ )
    s2 = lb.ref(
        "s2",
        "∀ y ( y = t → ∀ x ( x = y → φ ) ) → ∃ y ∀ x ( x = y → φ )",
        ref="alequexv",
        note="alequexv",
    )
    # exsbim: ∃ y ∀ x ( x = y → φ ) → ∃ x φ
    s3 = lb.ref(
        "s3",
        "∃ y ∀ x ( x = y → φ ) → ∃ x φ",
        ref="exsbim",
        note="exsbim",
    )
    # 3syl: chain s1 → s2 → s3
    res = lb.ref(
        "res",
        "[ t x φ → ∃ x φ",
        s1,
        s2,
        s3,
        ref="3syl",
        note="3syl dfsbimp, alequexv, exsbim",
    )
    return lb.build(res)


def prove_nsb(sys: System) -> Proof:
    """nsb: ∀ x ¬ φ → ¬ [ t x φ.

    From alnex, spsbe, and nsyl.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "nsb")
    # alnex: ∀ x ¬ φ ↔ ¬ ∃ x φ
    s1 = lb.ref(
        "s1",
        "∀ x ¬ φ ↔ ¬ ∃ x φ",
        ref="alnex",
        note="alnex",
    )
    # biimpi alnex: ∀ x ¬ φ → ¬ ∃ x φ
    s2 = lb.ref(
        "s2",
        "∀ x ¬ φ → ¬ ∃ x φ",
        s1,
        ref="biimpi",
        note="biimpi alnex",
    )
    # spsbe: [ t x φ → ∃ x φ
    s3 = lb.ref(
        "s3",
        "[ t x φ → ∃ x φ",
        ref="spsbe",
        note="spsbe",
    )
    # nsyl: ∀ x ¬ φ → ¬ [ t x φ
    res = lb.ref(
        "res",
        "∀ x ¬ φ → ¬ [ t x φ",
        s2,
        s3,
        ref="nsyl",
        note="nsyl",
    )
    return lb.build(res)


def prove_sbn1(sys: System) -> Proof:
    """sbn1: ( [ t / x ] ¬ φ → ¬ [ t / x ] φ ).

    From nsb, fal, mpg, pm2.21, sb2imi, and mtoi.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbn1")

    # pm2.21: ¬ φ → ( φ → F. )
    s1 = lb.ref("s1", "¬ φ → ( φ → F. )", ref="pm2.21", note="pm2.21")

    # sb2imi: ( [ t x ¬ φ → ( [ t x φ → [ t x F. ) )
    s2 = lb.ref(
        "s2",
        "( [ t x ¬ φ → ( [ t x φ → [ t x F. ) )",
        s1,
        ref="sb2imi",
        note="sb2imi pm2.21",
    )

    # fal: ¬ F.
    s3 = lb.ref("s3", "¬ F.", ref="fal", note="fal")

    # nsb: ∀ x ¬ F. → ¬ [ t x F.
    s4 = lb.ref("s4", "∀ x ¬ F. → ¬ [ t x F.", ref="nsb", note="nsb")

    # mpg: ¬ [ t x F.
    s5 = lb.ref("s5", "¬ [ t x F.", s4, s3, ref="mpg", note="mpg nsb, fal")

    # mtoi: ( [ t x ¬ φ → ¬ [ t x φ )
    res = lb.ref(
        "res",
        "( [ t x ¬ φ → ¬ [ t x φ )",
        s5,
        s2,
        ref="mtoi",
        note="mtoi sb2imi, mpg",
    )

    return lb.build(res)


__all__ = [
    "prove_al2im",
    "prove_alim",
    "prove_alimi",
    "prove_alrimdh",
    "prove_alrimdv",
    "prove_alrimih",
    "prove_alrimiv",
    "prove_alrimivv",
    "prove_hbn1",
    "prove_ax6v",
    "prove_ax5e",
    "prove_ax5ea",
    "prove_ax6ev",
    "prove_ax7v",
    "prove_ax7v1",
    "prove_ax7v2",
    "prove_ax7",
    "prove_cbvaliw",
    "prove_cbvalivw",
    "prove_equequ1",
    "prove_elequ1",
    "prove_elequ2",
    "prove_equtr",
    "prove_ax5d",
    "prove_ax13w",
    "prove_nfi",
    "prove_nfv",
    "prove_nfvd",
    "prove_nfri",
    "prove_nfimd",
    "prove_nfimt",
    "prove_nfim",
    "prove_nfrd",
    "prove_nfd",
    "prove_nf3",
    "prove_nf4",
    "prove_nfn",
    "prove_nfnbi",
    "prove_nfnt",
    "prove_gen2",
    "prove_alfal",
    "prove_spaev",
    "prove_spimfw",
    "prove_spimvw",
    "prove_spvv",
    "prove_chvarvv",
    "prove_cleljust",
    "prove_spimw",
    "prove_spsbe",
    "prove_nsb",
    "prove_sbn1",
    "prove_ax8v",
    "prove_ax8v1",
    "prove_ax8v2",
    "prove_ax8",
    "prove_ax9v",
    "prove_ax9v2",
    "prove_ax9v1",
    "prove_sylgt",
    "prove_sylg",
    "prove_ax12v",
    "prove_ax11dgen",
    "prove_ax12dgen",
    "prove_axie1",
    "prove_hbe1",
    "prove_hbe1a",
    "prove_stdpc5v",
    "prove_hbth",
    "prove_alcom",
    "prove_alcoms",
    "prove_alrot3",
    "prove_alrot4",
    "prove_ala1",
    "prove_stdpc4lem",
    "prove_hbal",
    "prove_hbalw",
    "prove_hbxfrbi",
    "prove_mpg",
    "prove_mpgbi",
    "prove_mpgbir",
    "prove_nex",
    "prove_nfth",
    "prove_nftru",
    "prove_nfequid",
    "prove_nfe1",
    "prove_al2imi",
    "prove_alanimi",
    "prove_alimdv",
    "prove_2alimi",
    "prove_2alimdv",
    "prove_albi",
    "prove_albii",
    "prove_2albii",
    "prove_2albidv",
    "prove_19_21v",
    "prove_19_32v",
    "prove_19_31v",
    "prove_19_33",
    "prove_pm11_53v",
    "prove_sbtALT",
]


def prove_stdpc5v(sys: System) -> Proof:
    """stdpc5v: A. x ( φ → ψ ) → ( φ → A. x ψ ).

    Universal quantifier distributes over the antecedent.
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: ax-5 alim syl5.
    """
    lb = ProofBuilder(sys, "stdpc5v")
    s1 = lb.ref("s1", "φ → ∀ x φ", ref="ax-5", note="ax-5 — ax-5")
    s2 = lb.ref(
        "s2",
        "A. x ( φ → ψ ) → ( A. x φ → A. x ψ )",
        ref="alim",
        note="alim",
    )
    res = lb.ref(
        "res",
        "A. x ( φ → ψ ) → ( φ → A. x ψ )",
        s1,
        s2,
        ref="syl5",
        note="syl5 ax-5, alim",
    )
    return lb.build(res)


def prove_hbe1a(sys: System) -> Proof:
    """hbe1a: E. x A. x φ → A. x φ.

    Existential quantifier of a universally quantified formula implies
    the universal statement. (Contributed by NM, 30-Jun-1993.)
    set.mm proof: df-ex hbn1 con1i sylbi.
    """
    lb = ProofBuilder(sys, "hbe1a")
    s1 = lb.ref(
        "s1",
        "¬ A. x φ → A. x ¬ A. x φ",
        ref="hbn1",
        note="hbn1",
    )
    s2 = lb.ref(
        "s2",
        "¬ A. x ¬ A. x φ → A. x φ",
        s1,
        ref="con1i",
        note="con1i hbn1",
    )
    s3 = lb.ref(
        "s3",
        "E. x A. x φ <-> ¬ A. x ¬ A. x φ",
        ref="df-ex",
        note="df-ex",
    )
    res = lb.ref(
        "res",
        "E. x A. x φ → A. x φ",
        s3,
        s2,
        ref="sylbi",
        note="sylbi df-ex, con1i",
    )
    return lb.build(res)


def prove_hbe1(sys: System) -> Proof:
    """hbe1: E. x ph → A. x E. x ph.

    Hypothesis builder for the existential quantifier.
    (Contributed by NM, 10-Jan-1993.)
    set.mm proof: df-ex hbn1 hbxfrbi.
    """
    lb = ProofBuilder(sys, "hbe1")
    s1 = lb.ref(
        "s1",
        "E. x ph <-> ¬ A. x ¬ ph",
        ref="df-ex",
        note="df-ex",
    )
    s2 = lb.ref(
        "s2",
        "¬ A. x ¬ ph → A. x ¬ A. x ¬ ph",
        ref="hbn1",
        note="hbn1",
    )
    res = lb.ref(
        "res",
        "E. x ph → A. x E. x ph",
        s1,
        s2,
        ref="hbxfrbi",
        note="hbxfrbi df-ex, hbn1",
    )
    return lb.build(res)


def prove_axie1(sys: System) -> Proof:
    """axie1: ∃ x φ → ∀ x ∃ x φ.

    Restatement of hbe1.
    (Contributed by NM, 10-Jan-1993.)
    set.mm proof: hbe1.
    """
    lb = ProofBuilder(sys, "axie1")
    res = lb.ref(
        "res",
        "∃ x φ → ∀ x ∃ x φ",
        ref="hbe1",
        note="hbe1",
    )
    return lb.build(res)


def prove_hbe1w(sys: System) -> Proof:
    """hbe1w: ∃ x φ → ∀ x ∃ x φ.

    Weak version of hbe1. Uses df-ex, hbn1w, and hbxfrbi.
    (Contributed by NM, 10-Jan-1993.)
    set.mm proof: df-ex hbn1w hbxfrbi.
    """
    lb = ProofBuilder(sys, "hbe1w")
    hyp = lb.hyp("hbe1w.1", "x = y → ( φ ↔ ψ )")
    s1 = lb.ref(
        "s1",
        "∃ x φ ↔ ¬ ∀ x ¬ φ",
        ref="df-ex",
        note="df-ex",
    )
    s_notbid = lb.ref(
        "s_notbid",
        "x = y → ( ¬ φ ↔ ¬ ψ )",
        hyp,
        ref="notbid",
        note="notbid hbe1w.1",
    )
    s2 = lb.ref(
        "s2",
        "¬ ∀ x ¬ φ → ∀ x ¬ ∀ x ¬ φ",
        s_notbid,
        ref="hbn1w",
        note="hbn1w",
    )
    res = lb.ref(
        "res",
        "∃ x φ → ∀ x ∃ x φ",
        s1,
        s2,
        ref="hbxfrbi",
        note="hbxfrbi df-ex, hbn1w",
    )
    return lb.build(res)


def prove_alcom(sys: System) -> Proof:
    """alcom: A. x A. y φ ↔ A. y A. x φ.

    Commutation of universal quantifiers. Both directions follow from
    ax-11 (ax-11). (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wal ax-11 impbii.
    """
    lb = ProofBuilder(sys, "alcom")
    # ax-11: A. x A. y φ → A. y A. x φ
    s1 = lb.ref("s1", "A. x A. y φ → A. y A. x φ", ref="ax-11", note="ax-11")
    # ax-11 with x ↔ y: A. y A. x φ → A. x A. y φ
    s2 = lb.ref("s2", "A. y A. x φ → A. x A. y φ", ref="ax-11", note="ax-11 x↔y")
    # impbi: (A. x A. y φ → A. y A. x φ) → ((A. y A. x φ → A. x A. y φ) → (A. x A. y φ ↔ A. y A. x φ))
    s3 = lb.ref(
        "s3",
        "( A. x A. y φ → A. y A. x φ ) → ( ( A. y A. x φ → A. x A. y φ ) → ( A. x A. y φ ↔ A. y A. x φ ) )",
        ref="impbi",
        note="impbi",
    )
    s4 = lb.mp("s4", s1, s3, note="MP s1, s3")
    res = lb.mp("res", s2, s4, note="MP s2, s4")
    return lb.build(res)


def prove_alcoms(sys: System) -> Proof:
    """alcoms: A. y A. x φ → ψ.

    Inference form of alcom. Uses ax-11 to swap quantifier order
    and syl with the hypothesis alcoms.1.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: ax-11 syl.
    """
    lb = ProofBuilder(sys, "alcoms")
    hyp = lb.hyp("alcoms.1", "A. x A. y φ → ψ")
    # ax-11 with x and y swapped: A. y A. x φ → A. x A. y φ
    s1 = lb.ref("s1", "A. y A. x φ → A. x A. y φ", ref="ax-11", note="ax-11 x↔y")
    # syl: (A. y A. x φ → A. x A. y φ), (A. x A. y φ → ψ) ⊢ (A. y A. x φ → ψ)
    res = lb.ref("res", "A. y A. x φ → ψ", s1, hyp, ref="syl", note="syl ax-11, alcoms.1")
    return lb.build(res)


def prove_alcomimw(sys: System) -> Proof:
    """alcomimw: ∀ x ∀ y φ → ∀ y ∀ x φ.

    Weak version of alcom. Uses cbvalvw to change bound variables and
    then chains implications with 3syl.
    (Contributed by NM, 10-Apr-2017.)
    (Proof shortened by Wolf Lammen, 28-Dec-2023.)
    set.mm proof: wal cbvalvw biimpi alimi ax-5 wi weq biimprd equcoms spimvw 2alimi 3syl.
    """
    lb = ProofBuilder(sys, "alcomimw")
    hyp = lb.hyp("alcomimw.1", "y = z → ( φ ↔ ψ )")

    # cbvalvw: ( ∀ y φ ↔ ∀ z ψ )
    s_cbvalvw = lb.ref(
        "s_cbvalvw",
        "( ∀ y φ ↔ ∀ z ψ )",
        hyp,
        ref="cbvalvw",
        note="cbvalvw",
    )

    # biimpi: ( ∀ y φ → ∀ z ψ )
    s_biimpi = lb.ref(
        "s_biimpi",
        "∀ y φ → ∀ z ψ",
        s_cbvalvw,
        ref="biimpi",
        note="biimpi",
    )

    # alimi with x: ( ∀ x ∀ y φ → ∀ x ∀ z ψ )
    s_alimi = lb.ref(
        "s_alimi",
        "∀ x ∀ y φ → ∀ x ∀ z ψ",
        s_biimpi,
        ref="alimi",
        note="alimi with x",
    )

    # ax-5: ( ∀ x ∀ z ψ → ∀ y ∀ x ∀ z ψ )
    s_ax5 = lb.ref(
        "s_ax5",
        "∀ x ∀ z ψ → ∀ y ∀ x ∀ z ψ",
        ref="ax-5",
        note="ax-5",
    )

    # biimprd: ( y = z → ( ψ → φ ) )
    s_biimprd = lb.ref(
        "s_biimprd",
        "y = z → ( ψ → φ )",
        hyp,
        ref="biimprd",
        note="biimprd",
    )

    # equcoms: ( z = y → ( ψ → φ ) )
    s_equcoms = lb.ref(
        "s_equcoms",
        "z = y → ( ψ → φ )",
        s_biimprd,
        ref="equcoms",
        note="equcoms",
    )

    # spimvw: ( ∀ z ψ → φ )
    s_spimvw = lb.ref(
        "s_spimvw",
        "∀ z ψ → φ",
        s_equcoms,
        ref="spimvw",
        note="spimvw",
    )

    # 2alimi: ( ∀ y ∀ x ∀ z ψ → ∀ y ∀ x φ )
    s_2alimi = lb.ref(
        "s_2alimi",
        "∀ y ∀ x ∀ z ψ → ∀ y ∀ x φ",
        s_spimvw,
        ref="2alimi",
        note="2alimi",
    )

    # 3syl: chain s_alimi → s_ax5 → s_2alimi
    res = lb.ref(
        "res",
        "∀ x ∀ y φ → ∀ y ∀ x φ",
        s_alimi,
        s_ax5,
        s_2alimi,
        ref="3syl",
        note="3syl",
    )

    return lb.build(res)


def prove_alcomw(sys: System) -> Proof:
    """alcomw: ( ∀ x ∀ y φ ↔ ∀ y ∀ x φ ).

    Weak version of quantifier commutation, biconditional form.
    From alcomimw applied in both directions, combined with impbii.
    (Contributed by NM, 10-Apr-2017.)
    set.mm proof: alcomimw impbii.
    """
    lb = ProofBuilder(sys, "alcomw")
    h1 = lb.hyp("alcomw.1", "x = w → ( φ ↔ ψ )")
    h2 = lb.hyp("alcomw.2", "y = z → ( φ ↔ χ )")

    # alcomimw with h2: ( ∀ x ∀ y φ → ∀ y ∀ x φ )
    s1 = lb.ref(
        "s1",
        "∀ x ∀ y φ → ∀ y ∀ x φ",
        h2,
        ref="alcomimw",
        note="alcomimw",
    )

    # alcomimw with h1: ( ∀ y ∀ x φ → ∀ x ∀ y φ )
    s2 = lb.ref(
        "s2",
        "∀ y ∀ x φ → ∀ x ∀ y φ",
        h1,
        ref="alcomimw",
        note="alcomimw",
    )

    # impbii: combine both directions
    res = lb.ref(
        "res",
        "( ∀ x ∀ y φ ↔ ∀ y ∀ x φ )",
        s1,
        s2,
        ref="impbii",
        note="impbii",
    )

    return lb.build(res)


def prove_ax11w(sys: System) -> Proof:
    """ax11w: ∀ x ∀ y φ → ∀ y ∀ x φ.

    Weak version of quantifier commutation. Simply invokes alcomimw.
    (Contributed by NM, 10-Apr-2017.)
    set.mm proof: alcomimw.
    """
    lb = ProofBuilder(sys, "ax11w")
    hy = lb.hyp("ax11w.1", "y = z → ( φ ↔ ψ )")
    res = lb.ref("res", "∀ x ∀ y φ → ∀ y ∀ x φ", hy, ref="alcomimw", note="alcomimw")
    return lb.build(res)


def prove_ax11dgen(sys: System) -> Proof:
    """ax11dgen: ∀ x ∀ x φ → ∀ x ∀ x φ.

    Identity law generalized with two universal quantifiers. The
    proof is a direct instantiation of id with the formula
    ∀ x ∀ x φ.
    (Contributed by NM, 22-Oct-2003.)
    """
    lb = ProofBuilder(sys, "ax11dgen")
    res = lb.ref(
        "res",
        "∀ x ∀ x φ → ∀ x ∀ x φ",
        ref="id",
        note="id",
    )
    return lb.build(res)


def prove_alrot3(sys: System) -> Proof:
    """alrot3: A. x A. y A. z ph <-> A. y A. z A. x ph.

    Rotation of three universal quantifiers. Uses alcom to swap adjacent
    quantifiers, then albii and bitri to chain the rotations.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wal alcom albii bitri.
    """
    lb = ProofBuilder(sys, "alrot3")
    # alcom x,z: A. x A. z ph <-> A. z A. x ph
    s2 = lb.ref("s2", "A. x A. z ph <-> A. z A. x ph", ref="alcom", note="alcom x,z")
    # albii y on s2: A. y A. x A. z ph <-> A. y A. z A. x ph
    s3 = lb.ref("s3", "A. y A. x A. z ph <-> A. y A. z A. x ph", s2, ref="albii", note="albii s2")
    # alcom x,y on A. z ph: A. x A. y A. z ph <-> A. y A. x A. z ph
    s4 = lb.ref("s4", "A. x A. y A. z ph <-> A. y A. x A. z ph", ref="alcom", note="alcom x,y")
    # bitri s4, s3: A. x A. y A. z ph <-> A. y A. z A. x ph
    res = lb.ref(
        "res", "A. x A. y A. z ph <-> A. y A. z A. x ph", s4, s3, ref="bitri", note="bitri s4, s3"
    )
    return lb.build(res)


def prove_alrot4(sys: System) -> Proof:
    """alrot4: ∀ x ∀ y ∀ z ∀ w φ ↔ ∀ z ∀ w ∀ x ∀ y φ.

    Rotation of four universal quantifiers. Uses alrot3 to rotate the three
    outermost quantifiers, alcom to reorder inner quantifier pairs, albii to
    distribute quantifiers over biconditionals, and bitri to chain the results.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wal alrot3 albii bitri.
    """
    lb = ProofBuilder(sys, "alrot4")
    # alrot3 with φ := ∀ w φ: ∀ x ∀ y ∀ z ∀ w φ ↔ ∀ y ∀ z ∀ x ∀ w φ
    s1 = lb.ref(
        "s1",
        "∀ x ∀ y ∀ z ∀ w φ ↔ ∀ y ∀ z ∀ x ∀ w φ",
        ref="alrot3",
        note="alrot3 with φ ≔ ∀ w φ",
    )
    # alcom y,z: ∀ y ∀ z ∀ x ∀ w φ ↔ ∀ z ∀ y ∀ x ∀ w φ
    s2 = lb.ref(
        "s2",
        "∀ y ∀ z ∀ x ∀ w φ ↔ ∀ z ∀ y ∀ x ∀ w φ",
        ref="alcom",
        note="alcom y,z",
    )
    # alrot3 with x≔y, y≔x, z≔w: ∀ y ∀ x ∀ w φ ↔ ∀ x ∀ w ∀ y φ
    s3 = lb.ref(
        "s3",
        "∀ y ∀ x ∀ w φ ↔ ∀ x ∀ w ∀ y φ",
        ref="alrot3",
        note="alrot3 with x≔y, y≔x, z≔w",
    )
    # albii with ∀ z on s3: ∀ z ∀ y ∀ x ∀ w φ ↔ ∀ z ∀ x ∀ w ∀ y φ
    s4 = lb.ref(
        "s4",
        "∀ z ∀ y ∀ x ∀ w φ ↔ ∀ z ∀ x ∀ w ∀ y φ",
        s3,
        ref="albii",
        note="albii ∀ z on alrot3",
    )
    # bitri s2, s4: ∀ y ∀ z ∀ x ∀ w φ ↔ ∀ z ∀ x ∀ w ∀ y φ
    s5 = lb.ref(
        "s5",
        "∀ y ∀ z ∀ x ∀ w φ ↔ ∀ z ∀ x ∀ w ∀ y φ",
        s2,
        s4,
        ref="bitri",
        note="bitri alcom, albii",
    )
    # alcom x,w: ∀ x ∀ w ∀ y φ ↔ ∀ w ∀ x ∀ y φ
    s6 = lb.ref(
        "s6",
        "∀ x ∀ w ∀ y φ ↔ ∀ w ∀ x ∀ y φ",
        ref="alcom",
        note="alcom x,w",
    )
    # albii with ∀ z on s6: ∀ z ∀ x ∀ w ∀ y φ ↔ ∀ z ∀ w ∀ x ∀ y φ
    s7 = lb.ref(
        "s7",
        "∀ z ∀ x ∀ w ∀ y φ ↔ ∀ z ∀ w ∀ x ∀ y φ",
        s6,
        ref="albii",
        note="albii ∀ z on alcom",
    )
    # bitri s5, s7: ∀ y ∀ z ∀ x ∀ w φ ↔ ∀ z ∀ w ∀ x ∀ y φ
    s8 = lb.ref(
        "s8",
        "∀ y ∀ z ∀ x ∀ w φ ↔ ∀ z ∀ w ∀ x ∀ y φ",
        s5,
        s7,
        ref="bitri",
        note="bitri",
    )
    # bitri s1, s8: ∀ x ∀ y ∀ z ∀ w φ ↔ ∀ z ∀ w ∀ x ∀ y φ
    res = lb.ref(
        "res",
        "∀ x ∀ y ∀ z ∀ w φ ↔ ∀ z ∀ w ∀ x ∀ y φ",
        s1,
        s8,
        ref="bitri",
        note="bitri alrot3, alcom/albii chain",
    )
    return lb.build(res)


def prove_ala1(sys: System) -> Proof:
    """ala1: A. x φ → A. x ( ψ → φ ).

    Universal quantifier distributes over a consequent weakened with
    ax-1. (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wi ax-1 alimi.
    """
    lb = ProofBuilder(sys, "ala1")
    # ax-1: φ → ( ψ → φ )
    s1 = lb.ref("s1", "φ → ( ψ → φ )", ref="ax-1", note="ax-1")
    # alimi: generalize both sides of ax-1.
    res = lb.ref(
        "res",
        "A. x φ → A. x ( ψ → φ )",
        s1,
        ref="alimi",
        note="alimi ax-1",
    )
    return lb.build(res)


def prove_ax12dgen(sys: System) -> Proof:
    """ax12dgen: ( x = x → ( ∀ x φ → ∀ x ( x = x → φ ) ) ).

    Equidistance in universal quantifier with equality.  The proof
    instantiates ala1 with ψ := x = x (pushing x = x inside the
    universal quantifier), then wraps the result with a1i to add the
    remaining antecedent x = x.  (Contributed by NM, 29-Dec-1992.)
    set.mm proof: ala1 a1i.
    """
    lb = ProofBuilder(sys, "ax12dgen")
    # ala1 with ψ := x = x: ∀ x φ → ∀ x ( x = x → φ )
    s1 = lb.ref(
        "s1",
        "∀ x φ → ∀ x ( x = x → φ )",
        ref="ala1",
        note="ala1 with ψ := x = x",
    )
    # a1i: ( x = x ) → ( ∀ x φ → ∀ x ( x = x → φ ) )
    res = lb.ref(
        "res",
        "( x = x ) → ( ∀ x φ → ∀ x ( x = x → φ ) )",
        s1,
        ref="a1i",
        note="a1i",
    )
    return lb.build(res)


def prove_stdpc4lem(sys: System) -> Proof:
    """stdpc4lem: ∀ x φ → ∀ y ( y = t → ∀ x ( x = y → φ ) ).

    Lemma for stdpc4: from universal closure, introduce a nested
    universal quantifier with an equality antecedent.  The proof
    uses ala1 to put the equality inside the quantifier, a1d to add
    the equality antecedent, and alrimiv to generalize over y.
    """
    lb = ProofBuilder(sys, "stdpc4lem")

    # ala1 with ψ := x = y → φ:
    #   A. x φ → A. x ( x = y → φ )
    s1 = lb.ref(
        "s1",
        "∀ x φ → ∀ x ( x = y → φ )",
        ref="ala1",
        note="ala1 with ψ := x = y → φ",
    )

    # a1d on s1: add antecedent y = t
    #   A. x φ → ( y = t → ∀ x ( x = y → φ ) )
    s2 = lb.ref(
        "s2",
        "∀ x φ → ( y = t → ∀ x ( x = y → φ ) )",
        s1,
        ref="a1d",
        note="a1d ala1",
    )

    # alrimiv on s2: generalize over y
    #   A. x φ → ∀ y ( y = t → ∀ x ( x = y → φ ) )
    res = lb.ref(
        "res",
        "∀ x φ → ∀ y ( y = t → ∀ x ( x = y → φ ) )",
        s2,
        ref="alrimiv",
        note="alrimiv a1d",
    )

    return lb.build(res)


def prove_stdpc4(sys: System) -> Proof:
    """stdpc4: ∀ x φ → [ t / x ] φ.

    Specialization: if a statement holds for all x, it also holds for the
    specific t properly substituted for x.
    (Contributed by NM, 14-May-1993.)
    """
    lb = ProofBuilder(sys, "stdpc4")

    # stdpc4lem with dummy variable y:
    #   ∀ x φ → ∀ y ( y = t → ∀ x ( x = y → φ ) )
    s1 = lb.ref(
        "s1",
        "∀ x φ → ∀ y ( y = t → ∀ x ( x = y → φ ) )",
        ref="stdpc4lem",
        note="stdpc4lem with y",
    )

    # stdpc4lem with dummy variable z:
    #   ∀ x φ → ∀ z ( z = t → ∀ x ( x = z → φ ) )
    s2 = lb.ref(
        "s2",
        "∀ x φ → ∀ z ( z = t → ∀ x ( x = z → φ ) )",
        ref="stdpc4lem",
        note="stdpc4lem with z",
    )

    # df-sb:
    #   [ t / x ] φ ↔
    #     ( ∀ y ( y = t → ∀ x ( x = y → φ ) )
    #     ∧ ∀ z ( z = t → ∀ x ( x = z → φ ) ) )
    s3 = lb.ref(
        "s3",
        "[ t / x ] φ ↔ ( ∀ y ( y = t → ∀ x ( x = y → φ ) ) ∧ ∀ z ( z = t → ∀ x ( x = z → φ ) ) )",
        ref="df-sb",
        note="df-sb",
    )

    # sylanbrc combines the three sub-proofs:
    #   sylanbrc.1: ∀ x φ → ∀ y ( y = t → ∀ x ( x = y → φ ) )
    #   sylanbrc.2: ∀ x φ → ∀ z ( z = t → ∀ x ( x = z → φ ) )
    #   sylanbrc.3: [ t / x ] φ ↔ ( ψ ∧ χ )
    res = lb.ref(
        "res",
        "∀ x φ → [ t / x ] φ",
        s1,
        s2,
        s3,
        ref="sylanbrc",
        note="sylanbrc s1, s2, s3",
    )

    return lb.build(res)


def prove_2stdpc4(sys: System) -> Proof:
    """2stdpc4: ∀ x ∀ y φ → [ z x [ w y φ.

    Double specialization: apply stdpc4 twice and chain with alimi and syl.
    (Contributed by NM, 14-May-1993.)
    """
    lb = ProofBuilder(sys, "2stdpc4")

    # stdpc4 with y, w: ∀ y φ → [ w y φ
    s1 = lb.ref(
        "s1",
        "∀ y φ → [ w y φ",
        ref="stdpc4",
        note="stdpc4 with y, w",
    )

    # alimi s1 with x: ∀ x ∀ y φ → ∀ x [ w y φ
    s2 = lb.ref(
        "s2",
        "∀ x ∀ y φ → ∀ x [ w y φ",
        s1,
        ref="alimi",
        note="alimi s1",
    )

    # stdpc4 with x, z on [w/y]φ: ∀ x [ w y φ → [ z x [ w y φ
    s3 = lb.ref(
        "s3",
        "∀ x [ w y φ → [ z x [ w y φ",
        ref="stdpc4",
        note="stdpc4 with x, z",
    )

    # syl: chain s2 and s3
    res = lb.ref(
        "res",
        "∀ x ∀ y φ → [ z x [ w y φ",
        s2,
        s3,
        ref="syl",
        note="syl s2, s3",
    )

    return lb.build(res)


def prove_hbth(sys: System) -> Proof:
    """hbth: φ → A. x φ.

    Hypothesis builder: generalization followed by antecedent introduction.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wal ax-gen a1i.
    """
    lb = ProofBuilder(sys, "hbth")
    hyp = lb.hyp("hbth.1", "φ")
    s2 = lb.ref("s2", "∀ x φ", hyp, ref="ax-gen", note="ax-gen hbth.1")
    # a1i: from A. x φ, conclude φ → A. x φ
    res = lb.ref("res", "φ → ∀ x φ", s2, ref="a1i", note="a1i")
    return lb.build(res)


def prove_hbal(sys: System) -> Proof:
    """hbal: A. y φ → A. x A. y φ.

    Apply alimi to the hypothesis hbal.1 (quantified over y),
    then chain with ax-11 (with swapped variables) via syl.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wal alimi ax-11 syl.
    """
    lb = ProofBuilder(sys, "hbal")
    hyp = lb.hyp("hbal.1", "φ → ∀ x φ")
    # alimi hbal.1: (ph -> A. x ph) with variable y
    s1 = lb.ref(
        "s1",
        "A. y φ → A. y A. x φ",
        hyp,
        ref="alimi",
        note="alimi hbal.1",
    )
    # ax-11 with x↔y: A. y A. x φ → A. x A. y φ
    s2 = lb.ref(
        "s2",
        "A. y A. x φ → A. x A. y φ",
        ref="ax-11",
        note="ax-11 x↔y",
    )
    # syl: (A. y φ → A. y A. x φ), (A. y A. x φ → A. x A. y φ) ⊢ (A. y φ → A. x A. y φ)
    res = lb.ref(
        "res",
        "A. y φ → A. x A. y φ",
        s1,
        s2,
        ref="syl",
        note="syl alimi, ax-11",
    )
    return lb.build(res)


def prove_hbalw(sys: System) -> Proof:
    """hbalw: ∀ y φ → ∀ x ∀ y φ.

    Weak version of hbal. Uses alcomimw instead of ax-11, requiring
    a distinct variable condition hypothesis.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "hbalw")
    hyp1 = lb.hyp("hbalw.1", "x = z → ( φ ↔ ψ )")
    hyp2 = lb.hyp("hbalw.2", "φ → ∀ x φ")
    # alimi hbalw.2: (φ → ∀ x φ) with variable y
    s1 = lb.ref(
        "s1",
        "∀ y φ → ∀ y ∀ x φ",
        hyp2,
        ref="alimi",
        note="alimi hbalw.2",
    )
    # alcomimw with swapped vars: ∀ y ∀ x φ → ∀ x ∀ y φ
    s2 = lb.ref(
        "s2",
        "∀ y ∀ x φ → ∀ x ∀ y φ",
        hyp1,
        ref="alcomimw",
        note="alcomimw x↔y",
    )
    # syl: ∀ y φ → ∀ x ∀ y φ
    res = lb.ref(
        "res",
        "∀ y φ → ∀ x ∀ y φ",
        s1,
        s2,
        ref="syl",
        note="syl",
    )
    return lb.build(res)


def prove_hbxfrbi(sys: System) -> Proof:
    """hbxfrbi: ( ph -> A. x ph ).

    Hypothesis builder for exchanging a biconditional and a forall
    hypothesis. (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wal albii 3imtr4i.
    """
    lb = ProofBuilder(sys, "hbxfrbi")
    h1 = lb.hyp("hbxfrbi.1", "( ph <-> ps )")
    h2 = lb.hyp("hbxfrbi.2", "( ps -> A. x ps )")
    # albii: from ( ph <-> ps ) get ( A. x ph <-> A. x ps )
    s1 = lb.ref(
        "s1",
        "( A. x ph <-> A. x ps )",
        h1,
        ref="albii",
        note="albii hbxfrbi.1",
    )
    # 3imtr4i: ( ps -> A. x ps ), ( ph <-> ps ), ( A. x ph <-> A. x ps )
    #     ⊢ ( ph -> A. x ph )
    res = lb.ref(
        "res",
        "( ph -> A. x ph )",
        h2,
        h1,
        s1,
        ref="3imtr4i",
        note="3imtr4i hbxfrbi.2, hbxfrbi.1, albii",
    )
    return lb.build(res)


def prove_hbald(sys: System) -> Proof:
    """hbald: ph → ( A. y ps → A. x A. y ps ).

    Deduction form of hbal. Apply alimdh to hbald.1 and hbald.2,
    then chain ax-11 with syl6.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wal alimdh ax-11 syl6.
    """
    lb = ProofBuilder(sys, "hbald")
    hyp1 = lb.hyp("hbald.1", "φ → A. y φ")
    hyp2 = lb.hyp("hbald.2", "φ → ( ψ → A. x ψ )")
    # alimdh: (φ → A.y φ), (φ → (ψ → A.x ψ)) ⊢ (φ → (A.y ψ → A.y A.x ψ))
    s1 = lb.ref(
        "s1",
        "φ → ( A. y ψ → A. y A. x ψ )",
        hyp1,
        hyp2,
        ref="alimdh",
        note="alimdh hbald.1, hbald.2",
    )
    # ax-11 with x↔y: A.y A.x ψ → A.x A.y ψ
    s2 = lb.ref(
        "s2",
        "A. y A. x ψ → A. x A. y ψ",
        ref="ax-11",
        note="ax-11 x↔y",
    )
    # syl6: (φ → (A.y ψ → A.y A.x ψ)), (A.y A.x ψ → A.x A.y ψ) ⊢ (φ → (A.y ψ → A.x A.y ψ))
    res = lb.ref(
        "res",
        "φ → ( A. y ψ → A. x A. y ψ )",
        s1,
        s2,
        ref="syl6",
        note="syl6 alimdh, ax-11",
    )
    return lb.build(res)


def prove_albi(sys: System) -> Proof:
    """albi: A. x ( φ ↔ ψ ) → ( A. x φ ↔ A. x ψ ).

    If a biconditional holds for all x, then the universally quantified
    formulas are equivalent. (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "albi")
    # biimp: ( φ ↔ ψ ) → ( φ → ψ )
    s1 = lb.ref("s1", "( φ ↔ ψ ) → ( φ → ψ )", ref="biimp", note="biimp")
    # al2imi with biimp: A. x ( φ ↔ ψ ) → ( A. x φ → A. x ψ )
    s2 = lb.ref(
        "s2",
        "A. x ( φ ↔ ψ ) → ( A. x φ → A. x ψ )",
        s1,
        ref="al2imi",
        note="al2imi biimp",
    )
    # biimpr: ( φ ↔ ψ ) → ( ψ → φ )
    s3 = lb.ref("s3", "( φ ↔ ψ ) → ( ψ → φ )", ref="biimpr", note="biimpr")
    # al2imi with biimpr: A. x ( φ ↔ ψ ) → ( A. x ψ → A. x φ )
    s4 = lb.ref(
        "s4",
        "A. x ( φ ↔ ψ ) → ( A. x ψ → A. x φ )",
        s3,
        ref="al2imi",
        note="al2imi biimpr",
    )
    # impbid: (A.x(φ↔ψ) → (A.x φ → A.x ψ)), (A.x(φ↔ψ) → (A.x ψ → A.x φ))
    #  ⊢ (A.x(φ↔ψ) → (A.x φ ↔ A.x ψ))
    res = lb.ref(
        "res",
        "A. x ( φ ↔ ψ ) → ( A. x φ ↔ A. x ψ )",
        s2,
        s4,
        ref="impbid",
        note="impbid",
    )
    return lb.build(res)


def prove_albii(sys: System) -> Proof:
    """albii: ( A. x ph <-> A. x ps ).

    If a biconditional holds, its universally quantified forms are equivalent.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wb wal albi mpg.
    """
    lb = ProofBuilder(sys, "albii")
    h1 = lb.hyp("albii.1", "( ph <-> ps )")
    # albi: A. x ( ph <-> ps ) -> ( A. x ph <-> A. x ps )
    s1 = lb.ref(
        "s1",
        "A. x ( ph <-> ps ) -> ( A. x ph <-> A. x ps )",
        ref="albi",
        note="albi",
    )
    # mpg: from (A. x ... -> ...) and (ph <-> ps), get (A. x ph <-> A. x ps)
    res = lb.ref(
        "res",
        "( A. x ph <-> A. x ps )",
        s1,
        h1,
        ref="mpg",
        note="mpg albi, albii.1",
    )
    return lb.build(res)


def prove_2albii(sys: System) -> Proof:
    """2albii: ( A. x A. y ph <-> A. x A. y ps ).

    Apply albii twice: first with variable y, then with variable x.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wal albii.
    """
    lb = ProofBuilder(sys, "2albii")
    h1 = lb.hyp("albii.1", "( ph <-> ps )")
    # albii with y: (A. y ph <-> A. y ps)
    s1 = lb.ref(
        "s1",
        "( A. y ph <-> A. y ps )",
        h1,
        ref="albii",
        note="albii with y",
    )
    # albii with x: (A. x A. y ph <-> A. x A. y ps)
    res = lb.ref(
        "res",
        "( A. x A. y ph <-> A. x A. y ps )",
        s1,
        ref="albii",
        note="albii with x",
    )
    return lb.build(res)


def prove_3albii(sys: System) -> Proof:
    """3albii: ( A. x A. y A. z ph <-> A. x A. y A. z ps ).

    Apply 2albii and albii: first 2albii with y,z, then albii with x.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wal 2albii albii.
    """
    lb = ProofBuilder(sys, "3albii")
    h1 = lb.hyp("albii.1", "( ph <-> ps )")
    # 2albii with y,z: (A. y A. z ph <-> A. y A. z ps)
    s1 = lb.ref(
        "s1",
        "( A. y A. z ph <-> A. y A. z ps )",
        h1,
        ref="2albii",
        note="2albii with y,z",
    )
    # albii with x: (A. x A. y A. z ph <-> A. x A. y A. z ps)
    res = lb.ref(
        "res",
        "( A. x A. y A. z ph <-> A. x A. y A. z ps )",
        s1,
        ref="albii",
        note="albii with x",
    )
    return lb.build(res)


def prove_albidh(sys: System) -> Proof:
    """albidh: φ → ( A. x ψ ↔ A. x χ ).

    Deduction form of albi. (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "albidh")
    hyp1 = lb.hyp("albidh.1", "φ → ∀ x φ")
    hyp2 = lb.hyp("albidh.2", "φ → ( ψ ↔ χ )")
    # alrimih: (ph -> A. x ph), (ph -> (ps <-> ch)) |- (ph -> A. x (ps <-> ch))
    s1 = lb.ref(
        "s1",
        "φ → A. x ( ψ ↔ χ )",
        hyp1,
        hyp2,
        ref="alrimih",
        note="alrimih albidh.1, albidh.2",
    )
    # albi: A. x (ps <-> ch) -> (A. x ps <-> A. x ch)
    s2 = lb.ref(
        "s2",
        "A. x ( ψ ↔ χ ) → ( A. x ψ ↔ A. x χ )",
        ref="albi",
        note="albi",
    )
    # syl: (ph -> A. x (ps <-> ch)),
    #   (A. x (ps <-> ch) -> (A. x ps <-> A. x ch))
    #  |- (ph -> (A. x ps <-> A. x ch))
    res = lb.ref(
        "res",
        "φ → ( A. x ψ ↔ A. x χ )",
        s1,
        s2,
        ref="syl",
        note="syl",
    )
    return lb.build(res)


def prove_albidv(sys: System) -> Proof:
    """albidv: ph → ( A. x ps ↔ A. x ch ).

    Deduction form of albi using ax-5.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: ax-5 albidh.
    """
    lb = ProofBuilder(sys, "albidv")
    hyp = lb.hyp("albidv.1", "ph → ( ps ↔ ch )")
    # ax-5: ph → A. x ph
    s1 = lb.ref("s1", "ph → A. x ph", ref="ax-5", note="ax-5 — ax-5")
    # albidh: (ph → A. x ph), (ph → (ps ↔ ch)) ⊢ (ph → (A. x ps ↔ A. x ch))
    res = lb.ref(
        "res",
        "ph → ( A. x ps ↔ A. x ch )",
        s1,
        hyp,
        ref="albidh",
        note="albidh ax-5, albidv.1",
    )
    return lb.build(res)


def prove_2albidv(sys: System) -> Proof:
    """2albidv: ph → ( A. x A. y ps ↔ A. x A. y ch ).

    Double deduction form of albidv.
    Apply albidv twice: first with variable y, then with variable x.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wal albidv.
    """
    lb = ProofBuilder(sys, "2albidv")
    hyp = lb.hyp("2albidv.1", "ph → ( ps ↔ ch )")
    # albidv: (ph → (ps ↔ ch)) ⊢ ph → (A. y ps ↔ A. y ch)
    s1 = lb.ref(
        "s1",
        "ph → ( A. y ps ↔ A. y ch )",
        hyp,
        ref="albidv",
        note="albidv 2albidv.1",
    )
    # albidv: (ph → (A. y ps ↔ A. y ch)) ⊢ ph → (A. x A. y ps ↔ A. x A. y ch)
    res = lb.ref(
        "res",
        "ph → ( A. x A. y ps ↔ A. x A. y ch )",
        s1,
        ref="albidv",
        note="albidv s1",
    )
    return lb.build(res)


def prove_eximal(sys: System) -> Proof:
    """eximal: ( ( E. x ph -> ps ) <-> ( -. ps -> A. x -. ph ) ).

    the universal quantifier with negation (contraposition).
    (Contributed by NM, 29-Dec-1992.)
    set.mm proof: df-ex imbi1i con1b bitri.
    """
    lb = ProofBuilder(sys, "eximal")

    # df-ex: E. x ph <-> ¬ A. x ¬ ph
    s1 = lb.ref(
        "s1",
        "E. x ph <-> ¬ A. x ¬ ph",
        ref="df-ex",
        note="df-ex",
    )

    # imbi1i: (E. x ph -> ps) <-> (¬ A. x ¬ ph -> ps)
    s2 = lb.ref(
        "s2",
        "( E. x ph → ps ) <-> ( ¬ A. x ¬ ph → ps )",
        s1,
        ref="imbi1i",
        note="imbi1i df-ex",
    )

    # con1b: (¬ A. x ¬ ph -> ps) <-> (¬ ps -> A. x ¬ ph)
    s3 = lb.ref(
        "s3",
        "( ¬ A. x ¬ ph → ps ) <-> ( ¬ ps → A. x ¬ ph )",
        ref="con1b",
        note="con1b",
    )

    # bitri: combine s2 and s3
    res = lb.ref(
        "res",
        "( E. x ph → ps ) <-> ( ¬ ps → A. x ¬ ph )",
        s2,
        s3,
        ref="bitri",
        note="bitri imbi1i, con1b",
    )
    return lb.build(res)


def prove_ax5e(sys: System) -> Proof:
    """ax5e: E. x ph → ph.

    Existential instantiation: if something exists, it also holds.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "ax5e")
    # eximal with ps := ph: (E. x ph → ph) ↔ (¬ ph → A. x ¬ ph)
    s1 = lb.ref(
        "s1",
        "( E. x ph → ph ) ↔ ( ¬ ph → A. x ¬ ph )",
        ref="eximal",
        note="eximal with ps := ph",
    )
    # ax-5 with ph := ¬ ph: ¬ ph → A. x ¬ ph
    s2 = lb.ref(
        "s2",
        "¬ ph → A. x ¬ ph",
        ref="ax-5",
        note="ax-5 — ax-5",
    )
    # mpbir: from biconditional and RHS, conclude LHS
    res = lb.ref(
        "res",
        "E. x ph → ph",
        s2,
        s1,
        ref="mpbir",
        note="mpbir eximal, ax-5",
    )
    return lb.build(res)


def prove_ax5ea(sys: System) -> Proof:
    """ax5ea: ∃ x φ → ∀ x φ.

    Existential to universal: from ∃ x φ, derive ∀ x φ
    using existential instantiation and generalization.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "ax5ea")
    # ax5e: ∃ x φ → φ
    s1 = lb.ref(
        "s1",
        "∃ x φ → φ",
        ref="ax5e",
        note="ax5e",
    )
    # ax-5: φ → ∀ x φ
    s2 = lb.ref(
        "s2",
        "φ → ∀ x φ",
        ref="ax-5",
        note="ax-5 — ax-5",
    )
    # syl: chain s1 and s2
    res = lb.ref(
        "res",
        "∃ x φ → ∀ x φ",
        s1,
        s2,
        ref="syl",
        note="syl ax5e, ax-5",
    )
    return lb.build(res)


def prove_sbv(sys: System) -> Proof:
    """sbv: ( [ t / x ] φ ↔ φ ).

    Proper substitution of a variable that is not free in the formula.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wsb wex spsbe ax5e syl wal ax-5 stdpc4 impbii.
    """
    lb = ProofBuilder(sys, "sbv")
    # spsbe: [ t x φ → ∃ x φ
    s1 = lb.ref(
        "s1",
        "[ t x φ → ∃ x φ",
        ref="spsbe",
        note="spsbe",
    )
    # ax5e: ∃ x φ → φ
    s2 = lb.ref(
        "s2",
        "∃ x φ → φ",
        ref="ax5e",
        note="ax5e",
    )
    # syl: [ t x φ → φ
    s3 = lb.ref(
        "s3",
        "[ t x φ → φ",
        s1,
        s2,
        ref="syl",
        note="syl spsbe, ax5e",
    )
    # ax-5: φ → ∀ x φ
    s4 = lb.ref(
        "s4",
        "φ → ∀ x φ",
        ref="ax-5",
        note="ax-5 — ax-5",
    )
    # stdpc4: ∀ x φ → [ t x φ
    s5 = lb.ref(
        "s5",
        "∀ x φ → [ t x φ",
        ref="stdpc4",
        note="stdpc4",
    )
    # syl: φ → [ t x φ
    s6 = lb.ref(
        "s6",
        "φ → [ t x φ",
        s4,
        s5,
        ref="syl",
        note="syl ax-5, stdpc4",
    )
    # impbii: ( [ t x φ ↔ φ )
    res = lb.ref(
        "res",
        "( [ t x φ ↔ φ )",
        s3,
        s6,
        ref="impbii",
        note="impbii",
    )
    return lb.build(res)


def prove_19_2(sys: System) -> Proof:
    """19.2: ∀ x φ → ∃ x φ.

    From the universal quantifier to the existential quantifier.
    (Contributed by NM, 4-Oct-1991.)
    set.mm proof: wi id exgen 19.35i.
    """
    lb = ProofBuilder(sys, "19.2")
    # id: φ → φ
    s1 = lb.ref("s1", "φ → φ", ref="id", note="id")
    # exgen: from ( φ → φ ), conclude ∃ x ( φ → φ )
    s2 = lb.ref("s2", "∃ x ( φ → φ )", s1, ref="exgen", note="exgen id")
    # 19.35i: from ∃ x ( φ → φ ), conclude ∀ x φ → ∃ x φ
    res = lb.ref("res", "∀ x φ → ∃ x φ", s2, ref="19.35i", note="19.35i exgen")
    return lb.build(res)


def prove_19_2d(sys: System) -> Proof:
    """19.2d: φ → ∃ x ψ.

    Deduction form of 19.2.  (Contributed by NM, 4-Oct-1991.)
    set.mm proof: 19.2 syl.
    """
    lb = ProofBuilder(sys, "19.2d")
    hyp = lb.hyp("19.2d.1", "φ → ∀ x ψ")
    s1 = lb.ref("s1", "∀ x ψ → ∃ x ψ", ref="19.2", note="19.2")
    res = lb.ref("res", "φ → ∃ x ψ", hyp, s1, ref="syl", note="syl 19.2d.1, 19.2")
    return lb.build(res)


def prove_19_2g(sys: System) -> Proof:
    """19.2g: ∀ x φ → ∃ y φ.

    Generalization of 19.2: the universal quantifier implies the
    existential quantifier even when the bound variables differ.
    (Contributed by NM, 4-Oct-1991.)
    """
    lb = ProofBuilder(sys, "19.2g")

    # 19.8a (with y): φ → ∃ y φ
    s1 = lb.ref(
        "s1",
        "φ → ∃ y φ",
        ref="19.8a",
        note="19.8a",
    )

    # sps: ( φ → ∃ y φ ) ⊢ ∀ x φ → ∃ y φ
    res = lb.ref(
        "res",
        "∀ x φ → ∃ y φ",
        s1,
        ref="sps",
        note="sps 19.8a",
    )

    return lb.build(res)


def prove_19_8w(sys: System) -> Proof:
    """19.8w: φ → ∃ x φ.

    Deduction form of 19.2 with the same variable.
    (Contributed by NM, 4-Oct-1991.)
    set.mm proof: 19.2d.
    """
    lb = ProofBuilder(sys, "19.8w")
    hyp = lb.hyp("19.8w.1", "φ → ∀ x φ")
    res = lb.ref("res", "φ → ∃ x φ", hyp, ref="19.2d", note="19.2d")
    return lb.build(res)


def prove_19_8v(sys: System) -> Proof:
    """19.8v: φ → ∃ x φ.

    Closed form of 19.8w.  ax-5 with its distinct variable condition
    provides φ → ∀ x φ, which is the hypothesis needed by 19.8w.
    (Contributed by NM, 4-Oct-1991.)
    set.mm proof: ax-5 19.8w.
    """
    lb = ProofBuilder(sys, "19.8v")
    # ax-5: φ → ∀ x φ (valid when x is not free in φ)
    s1 = lb.ref("s1", "φ → ∀ x φ", ref="ax-5", note="ax-5")
    # 19.8w: (φ → ∀ x φ) ⊢ φ → ∃ x φ
    res = lb.ref("res", "φ → ∃ x φ", s1, ref="19.8w", note="19.8w ax-5")
    return lb.build(res)


def prove_19_9v(sys: System) -> Proof:
    """19.9v: ∃ x φ ↔ φ.

    Equivalence between an existentially quantified formula and
    the formula itself when the variable is distinct.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wex ax5e 19.8v impbii.
    """
    lb = ProofBuilder(sys, "19.9v")
    # ax5e: ∃ x φ → φ
    s1 = lb.ref(
        "s1",
        "∃ x φ → φ",
        ref="ax5e",
        note="ax5e",
    )
    # 19.8v: φ → ∃ x φ
    s2 = lb.ref(
        "s2",
        "φ → ∃ x φ",
        ref="19.8v",
        note="19.8v",
    )
    # impbii: combine both directions
    res = lb.ref(
        "res",
        "∃ x φ ↔ φ",
        s1,
        s2,
        ref="impbii",
        note="impbii",
    )
    return lb.build(res)


def prove_19_12vvv(sys: System) -> Proof:
    """19.12vvv: ∃ x ∀ y ( φ → ψ ) ↔ ∀ y ∃ x ( φ → ψ ).

    Swap of quantifiers over an implication.  An existentially quantified
    universal implies the universal quantification of the existential.
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: wi wal wex 19.21v exbii 19.36v albii bitr2i 3bitri.
    """
    lb = ProofBuilder(sys, "19.12vvv")

    # 19.21v: ∀ y ( φ → ψ ) ↔ ( φ → ∀ y ψ )
    s1 = lb.ref(
        "s1",
        "( ∀ y ( φ → ψ ) ↔ ( φ → ∀ y ψ ) )",
        ref="19.21v",
        note="19.21v",
    )

    # exbii s1: ∃ x ∀ y ( φ → ψ ) ↔ ∃ x ( φ → ∀ y ψ )
    s2 = lb.ref(
        "s2",
        "( ∃ x ∀ y ( φ → ψ ) ↔ ∃ x ( φ → ∀ y ψ ) )",
        s1,
        ref="exbii",
        note="exbii 19.21v",
    )

    # 19.36v: ∃ x ( φ → ∀ y ψ ) ↔ ( ∀ x φ → ∀ y ψ )
    s3 = lb.ref(
        "s3",
        "( ∃ x ( φ → ∀ y ψ ) ↔ ( ∀ x φ → ∀ y ψ ) )",
        ref="19.36v",
        note="19.36v",
    )

    # 19.36v: ∃ x ( φ → ψ ) ↔ ( ∀ x φ → ψ )
    s4 = lb.ref(
        "s4",
        "( ∃ x ( φ → ψ ) ↔ ( ∀ x φ → ψ ) )",
        ref="19.36v",
        note="19.36v",
    )

    # albii s4: ∀ y ∃ x ( φ → ψ ) ↔ ∀ y ( ∀ x φ → ψ )
    s5 = lb.ref(
        "s5",
        "( ∀ y ∃ x ( φ → ψ ) ↔ ∀ y ( ∀ x φ → ψ ) )",
        s4,
        ref="albii",
        note="albii 19.36v",
    )

    # 19.21v: ∀ y ( ∀ x φ → ψ ) ↔ ( ∀ x φ → ∀ y ψ )
    s6 = lb.ref(
        "s6",
        "( ∀ y ( ∀ x φ → ψ ) ↔ ( ∀ x φ → ∀ y ψ ) )",
        ref="19.21v",
        note="19.21v",
    )

    # bitr2i s5, s6: ( ∀ x φ → ∀ y ψ ) ↔ ∀ y ∃ x ( φ → ψ )
    s7 = lb.ref(
        "s7",
        "( ( ∀ x φ → ∀ y ψ ) ↔ ∀ y ∃ x ( φ → ψ ) )",
        s5,
        s6,
        ref="bitr2i",
        note="bitr2i",
    )

    # 3bitri s2, s3, s7: ∃ x ∀ y ( φ → ψ ) ↔ ∀ y ∃ x ( φ → ψ )
    res = lb.ref(
        "res",
        "( ∃ x ∀ y ( φ → ψ ) ↔ ∀ y ∃ x ( φ → ψ ) )",
        s2,
        s3,
        s7,
        ref="3bitri",
        note="3bitri",
    )

    return lb.build(res)


def prove_19_44v(sys: System) -> Proof:
    """19.44v: ∃ x ( φ ∨ ψ ) ↔ ( ∃ x φ ∨ ψ ).

    Existential quantifier distributes over disjunction when the
    second disjunct does not contain the bound variable.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wo wex 19.43 19.9v orbi2i bitri.
    """
    lb = ProofBuilder(sys, "19.44v")
    # 19.43: ∃ x ( φ ∨ ψ ) ↔ ( ∃ x φ ∨ ∃ x ψ )
    s1 = lb.ref(
        "s1",
        "∃ x ( φ ∨ ψ ) ↔ ( ∃ x φ ∨ ∃ x ψ )",
        ref="19.43",
        note="19.43",
    )
    # 19.9v: ∃ x ψ ↔ ψ
    s2 = lb.ref(
        "s2",
        "∃ x ψ ↔ ψ",
        ref="19.9v",
        note="19.9v",
    )
    # orbi2i s2: ( ∃ x φ ∨ ∃ x ψ ) ↔ ( ∃ x φ ∨ ψ )
    s3 = lb.ref(
        "s3",
        "( ∃ x φ ∨ ∃ x ψ ) ↔ ( ∃ x φ ∨ ψ )",
        s2,
        ref="orbi2i",
        note="orbi2i 19.9v",
    )
    # bitri s1, s3: ∃ x ( φ ∨ ψ ) ↔ ( ∃ x φ ∨ ψ )
    res = lb.ref(
        "res",
        "∃ x ( φ ∨ ψ ) ↔ ( ∃ x φ ∨ ψ )",
        s1,
        s3,
        ref="bitri",
        note="bitri",
    )
    return lb.build(res)


def prove_19_45v(sys: System) -> Proof:
    """19.45v: ∃ x ( φ ∨ ψ ) ↔ ( φ ∨ ∃ x ψ ).

    Existential quantifier distributes over disjunction when the
    first disjunct does not contain the bound variable.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wo wex 19.43 19.9v orbi1i bitri.
    """
    lb = ProofBuilder(sys, "19.45v")
    # 19.43: ∃ x ( φ ∨ ψ ) ↔ ( ∃ x φ ∨ ∃ x ψ )
    s1 = lb.ref(
        "s1",
        "∃ x ( φ ∨ ψ ) ↔ ( ∃ x φ ∨ ∃ x ψ )",
        ref="19.43",
        note="19.43",
    )
    # 19.9v: ∃ x φ ↔ φ
    s2 = lb.ref(
        "s2",
        "∃ x φ ↔ φ",
        ref="19.9v",
        note="19.9v",
    )
    # orbi1i s2: ( ∃ x φ ∨ ∃ x ψ ) ↔ ( φ ∨ ∃ x ψ )
    s3 = lb.ref(
        "s3",
        "( ∃ x φ ∨ ∃ x ψ ) ↔ ( φ ∨ ∃ x ψ )",
        s2,
        ref="orbi1i",
        note="orbi1i 19.9v",
    )
    # bitri s1, s3: ∃ x ( φ ∨ ψ ) ↔ ( φ ∨ ∃ x ψ )
    res = lb.ref(
        "res",
        "∃ x ( φ ∨ ψ ) ↔ ( φ ∨ ∃ x ψ )",
        s1,
        s3,
        ref="bitri",
        note="bitri",
    )
    return lb.build(res)


def prove_19_33(sys: System) -> Proof:
    """19.33: ( ( ∀ x φ ∨ ∀ x ψ ) → ∀ x ( φ ∨ ψ ) ).


    If φ or ψ holds for all x, then for all x,
    φ or ψ.
    set.mm proof: wal wo orc alimi olc jaoi.
    """
    lb = ProofBuilder(sys, "19.33")
    s1 = lb.ref("s1", "φ → ( φ ∨ ψ )", ref="orc", note="orc")
    s2 = lb.ref("s2", "∀ x φ → ∀ x ( φ ∨ ψ )", s1, ref="alimi", note="alimi orc")
    s3 = lb.ref("s3", "ψ → ( φ ∨ ψ )", ref="olc", note="olc")
    s4 = lb.ref("s4", "∀ x ψ → ∀ x ( φ ∨ ψ )", s3, ref="alimi", note="alimi olc")
    res = lb.ref(
        "res",
        "( ( ∀ x φ ∨ ∀ x ψ ) → ∀ x ( φ ∨ ψ ) )",
        s2,
        s4,
        ref="jaoi",
        note="jaoi",
    )
    return lb.build(res)


def prove_19_33b(sys: System) -> Proof:
    """19.33b: ¬ ( ∃ x φ ∧ ∃ x ψ ) → ( ∀ x ( φ ∨ ψ ) ↔ ( ∀ x φ ∨ ∀ x ψ ) ).

    Under the assumption that not both ∃ x φ and ∃ x ψ hold,
    the universal quantifier distributes over disjunction
    in both directions.
    """
    lb = ProofBuilder(sys, "19.33b")

    # ianor: ¬ ( ∃ x φ ∧ ∃ x ψ ) ↔ ( ¬ ∃ x φ ∨ ¬ ∃ x ψ )
    s1 = lb.ref(
        "s1",
        "¬ ( ∃ x φ ∧ ∃ x ψ ) ↔ ( ¬ ∃ x φ ∨ ¬ ∃ x ψ )",
        ref="ianor",
        note="ianor",
    )

    # alnex: ∀ x ¬ φ ↔ ¬ ∃ x φ
    s2 = lb.ref("s2", "∀ x ¬ φ ↔ ¬ ∃ x φ", ref="alnex", note="alnex")

    # pm2.53: ( φ ∨ ψ ) → ( ¬ φ → ψ )
    s3 = lb.ref("s3", "( φ ∨ ψ ) → ( ¬ φ → ψ )", ref="pm2.53", note="pm2.53")

    # al2imi on pm2.53: ∀ x ( φ ∨ ψ ) → ( ∀ x ¬ φ → ∀ x ψ )
    s4 = lb.ref(
        "s4",
        "∀ x ( φ ∨ ψ ) → ( ∀ x ¬ φ → ∀ x ψ )",
        s3,
        ref="al2imi",
        note="al2imi pm2.53",
    )

    # biimtrrid alnex + al2imi: ∀ x ( φ ∨ ψ ) → ( ¬ ∃ x φ → ∀ x ψ )
    s5 = lb.ref(
        "s5",
        "∀ x ( φ ∨ ψ ) → ( ¬ ∃ x φ → ∀ x ψ )",
        s2,
        s4,
        ref="biimtrrid",
        note="biimtrrid alnex, al2imi",
    )

    # olc: ∀ x ψ → ( ∀ x φ ∨ ∀ x ψ )
    s6 = lb.ref(
        "s6",
        "∀ x ψ → ( ∀ x φ ∨ ∀ x ψ )",
        ref="olc",
        note="olc",
    )

    # syl6com: ¬ ∃ x φ → ( ∀ x ( φ ∨ ψ ) → ( ∀ x φ ∨ ∀ x ψ ) )
    s7 = lb.ref(
        "s7",
        "¬ ∃ x φ → ( ∀ x ( φ ∨ ψ ) → ( ∀ x φ ∨ ∀ x ψ ) )",
        s5,
        s6,
        ref="syl6com",
        note="syl6com",
    )

    # 19.30: ∀ x ( φ ∨ ψ ) → ( ∀ x φ ∨ ∃ x ψ )
    s8 = lb.ref(
        "s8",
        "∀ x ( φ ∨ ψ ) → ( ∀ x φ ∨ ∃ x ψ )",
        ref="19.30",
        note="19.30",
    )

    # orcomd on 19.30: ∀ x ( φ ∨ ψ ) → ( ∃ x ψ ∨ ∀ x φ )
    s9 = lb.ref(
        "s9",
        "∀ x ( φ ∨ ψ ) → ( ∃ x ψ ∨ ∀ x φ )",
        s8,
        ref="orcomd",
        note="orcomd 19.30",
    )

    # ord: ∀ x ( φ ∨ ψ ) → ( ¬ ∃ x ψ → ∀ x φ )
    s10 = lb.ref(
        "s10",
        "∀ x ( φ ∨ ψ ) → ( ¬ ∃ x ψ → ∀ x φ )",
        s9,
        ref="ord",
        note="ord",
    )

    # orc: ∀ x φ → ( ∀ x φ ∨ ∀ x ψ )
    s11 = lb.ref(
        "s11",
        "∀ x φ → ( ∀ x φ ∨ ∀ x ψ )",
        ref="orc",
        note="orc",
    )

    # syl6com: ¬ ∃ x ψ → ( ∀ x ( φ ∨ ψ ) → ( ∀ x φ ∨ ∀ x ψ ) )
    s12 = lb.ref(
        "s12",
        "¬ ∃ x ψ → ( ∀ x ( φ ∨ ψ ) → ( ∀ x φ ∨ ∀ x ψ ) )",
        s10,
        s11,
        ref="syl6com",
        note="syl6com",
    )

    # jaoi: ( ¬ ∃ x φ ∨ ¬ ∃ x ψ ) → ( ∀ x ( φ ∨ ψ ) → ( ∀ x φ ∨ ∀ x ψ ) )
    s13 = lb.ref(
        "s13",
        "( ¬ ∃ x φ ∨ ¬ ∃ x ψ ) → ( ∀ x ( φ ∨ ψ ) → ( ∀ x φ ∨ ∀ x ψ ) )",
        s7,
        s12,
        ref="jaoi",
        note="jaoi",
    )

    # sylbi ianor + jaoi: ¬ ( ∃ x φ ∧ ∃ x ψ ) → ( ∀ x ( φ ∨ ψ ) → ( ∀ x φ ∨ ∀ x ψ ) )
    s14 = lb.ref(
        "s14",
        "¬ ( ∃ x φ ∧ ∃ x ψ ) → ( ∀ x ( φ ∨ ψ ) → ( ∀ x φ ∨ ∀ x ψ ) )",
        s1,
        s13,
        ref="sylbi",
        note="sylbi ianor, jaoi",
    )

    # 19.33: ( ∀ x φ ∨ ∀ x ψ ) → ∀ x ( φ ∨ ψ )
    s15 = lb.ref(
        "s15",
        "( ∀ x φ ∨ ∀ x ψ ) → ∀ x ( φ ∨ ψ )",
        ref="19.33",
        note="19.33",
    )

    # impbid1: ¬ ( ∃ x φ ∧ ∃ x ψ ) → ( ∀ x ( φ ∨ ψ ) ↔ ( ∀ x φ ∨ ∀ x ψ ) )
    res = lb.ref(
        "res",
        "¬ ( ∃ x φ ∧ ∃ x ψ ) → ( ∀ x ( φ ∨ ψ ) ↔ ( ∀ x φ ∨ ∀ x ψ ) )",
        s14,
        s15,
        ref="impbid1",
        note="impbid1",
    )

    return lb.build(res)


def prove_19_34(sys: System) -> Proof:
    """19.34: ( ∀ x φ ∨ ∃ x ψ ) → ∃ x ( φ ∨ ψ ).

    Universal and existential quantifier mixed disjunction.
    (Contributed by NM, 26-Sep-1993.)
    set.mm proof: wal wex wo 19.2 orim1i 19.43 sylibr.
    """
    lb = ProofBuilder(sys, "19.34")
    # 19.2: ∀ x φ → ∃ x φ
    s1 = lb.ref("s1", "∀ x φ → ∃ x φ", ref="19.2", note="19.2")
    # orim1i with 19.2: ( ∀ x φ ∨ ∃ x ψ ) → ( ∃ x φ ∨ ∃ x ψ )
    s2 = lb.ref(
        "s2",
        "( ∀ x φ ∨ ∃ x ψ ) → ( ∃ x φ ∨ ∃ x ψ )",
        s1,
        ref="orim1i",
        note="orim1i 19.2",
    )
    # 19.43: ∃ x ( φ ∨ ψ ) ↔ ( ∃ x φ ∨ ∃ x ψ )
    s3 = lb.ref(
        "s3",
        "∃ x ( φ ∨ ψ ) ↔ ( ∃ x φ ∨ ∃ x ψ )",
        ref="19.43",
        note="19.43",
    )
    # sylibr: from s2 (→) and s3 (↔), derive the conclusion
    res = lb.ref(
        "res",
        "( ∀ x φ ∨ ∃ x ψ ) → ∃ x ( φ ∨ ψ )",
        s2,
        s3,
        ref="sylibr",
        note="sylibr orim1i, 19.43",
    )
    return lb.build(res)


def prove_19_38(sys: System) -> Proof:
    """19.38: ( ( ∃ x φ → ∀ x ψ ) → ∀ x ( φ → ψ ).

    If there exists an x with φ implies for all x ψ, then
    for all x, φ implies ψ.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: alnex pm2.21 alimi sylbir ala1 ja.
    """
    lb = ProofBuilder(sys, "19.38")
    # alnex: ∀ x ¬ φ ↔ ¬ ∃ x φ
    s1 = lb.ref("s1", "∀ x ¬ φ ↔ ¬ ∃ x φ", ref="alnex", note="alnex")
    # pm2.21: ¬ φ → ( φ → ψ )
    s2 = lb.ref("s2", "¬ φ → ( φ → ψ )", ref="pm2.21", note="pm2.21")
    # alimi: from pm2.21, get ∀ x ¬ φ → ∀ x ( φ → ψ )
    s3 = lb.ref(
        "s3",
        "∀ x ¬ φ → ∀ x ( φ → ψ )",
        s2,
        ref="alimi",
        note="alimi pm2.21",
    )
    # sylbir: with alnex biconditional, get ¬ ∃ x φ → ∀ x ( φ → ψ )
    s4 = lb.ref(
        "s4",
        "¬ ∃ x φ → ∀ x ( φ → ψ )",
        s1,
        s3,
        ref="sylbir",
        note="sylbir alnex, alimi",
    )
    # ala1 with φ:=ψ, ψ:=φ: ∀ x ψ → ∀ x ( φ → ψ )
    s5 = lb.ref(
        "s5",
        "∀ x ψ → ∀ x ( φ → ψ )",
        ref="ala1",
        note="ala1",
    )
    # ja: combine the two cases
    res = lb.ref(
        "res",
        "( ( ∃ x φ → ∀ x ψ ) → ∀ x ( φ → ψ ) )",
        s4,
        s5,
        ref="ja",
        note="ja",
    )
    return lb.build(res)


def prove_19_39(sys: System) -> Proof:
    """19.39: ( ∃ x φ → ∃ x ψ ) → ∃ x ( φ → ψ ).

    If the existential quantifier distributes over implication
    antecedents, then the quantified implication exists.
    (Contributed by NM, 4-Oct-1991.)
    set.mm proof: wex wi wal 19.2 imim1i 19.35 sylibr.
    """
    lb = ProofBuilder(sys, "19.39")
    # 19.2: ∀ x φ → ∃ x φ
    s_19_2 = lb.ref(
        "s_19_2",
        "∀ x φ → ∃ x φ",
        ref="19.2",
        note="19.2",
    )
    # imim1i with 19.2 as hypothesis and χ := ∃ x ψ:
    #   ( ∃ x φ → ∃ x ψ ) → ( ∀ x φ → ∃ x ψ )
    s_imim1i = lb.ref(
        "s_imim1i",
        "( ∃ x φ → ∃ x ψ ) → ( ∀ x φ → ∃ x ψ )",
        s_19_2,
        ref="imim1i",
        note="imim1i 19.2",
    )
    # 19.35: ∃ x ( φ → ψ ) ↔ ( ∀ x φ → ∃ x ψ )
    s_19_35 = lb.ref(
        "s_19_35",
        "∃ x ( φ → ψ ) ↔ ( ∀ x φ → ∃ x ψ )",
        ref="19.35",
        note="19.35",
    )
    # sylibr: (φ → ψ), (χ ↔ ψ) ⊢ (φ → χ)
    res = lb.ref(
        "res",
        "( ∃ x φ → ∃ x ψ ) → ∃ x ( φ → ψ )",
        s_imim1i,
        s_19_35,
        ref="sylibr",
        note="sylibr",
    )
    return lb.build(res)


def prove_19_38b(sys: System) -> Proof:
    """19.38b: ( Ⅎ x ψ → ( ( ∃ x φ → ∀ x ψ ) ↔ ∀ x ( φ → ψ ) ) ).

    If x is not free in ψ, then the implication (∃ x φ → ∀ x ψ) is
    equivalent to ∀ x ( φ → ψ ).
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wnf wex wal wi 19.38 exim id nfrd syl9r impbid2.
    """
    lb = ProofBuilder(sys, "19.38b")
    # 19.38: (E. x ph -> A. x ps) -> A. x (ph -> ps)
    s1 = lb.ref(
        "s1",
        "( ∃ x φ → ∀ x ψ ) → ∀ x ( φ → ψ )",
        ref="19.38",
        note="19.38",
    )
    # exim: A. x (ph -> ps) -> (E. x ph -> E. x ps)
    s2 = lb.ref(
        "s2",
        "∀ x ( φ → ψ ) → ( ∃ x φ → ∃ x ψ )",
        ref="exim",
        note="exim",
    )
    # id: F/ x ps -> F/ x ps
    s3 = lb.ref(
        "s3",
        "F/ x ψ → F/ x ψ",
        ref="id",
        note="id",
    )
    # nfrd with hypothesis id: (F/ x ps -> (E. x ps -> A. x ps))
    s4 = lb.ref(
        "s4",
        "F/ x ψ → ( ∃ x ψ → ∀ x ψ )",
        s3,
        ref="nfrd",
        note="nfrd id",
    )
    # syl9r with exim and nfrd:
    # F/ x ps -> (A. x (ph -> ps) -> (E. x ph -> A. x ps))
    s5 = lb.ref(
        "s5",
        "F/ x ψ → ( ∀ x ( φ → ψ ) → ( ∃ x φ → ∀ x ψ ) )",
        s2,
        s4,
        ref="syl9r",
        note="syl9r exim, nfrd",
    )
    # impbid2: combine the two directions
    # (F/ x ps -> ((E. x ph -> A. x ps) <-> A. x (ph -> ps)))
    res = lb.ref(
        "res",
        "F/ x ψ → ( ( ∃ x φ → ∀ x ψ ) ↔ ∀ x ( φ → ψ ) )",
        s1,
        s5,
        ref="impbid2",
        note="impbid2 19.38, syl9r",
    )
    return lb.build(res)


def prove_19_38a(sys: System) -> Proof:
    """19.38a: ( Ⅎ x φ → ( ( ∃ x φ → ∀ x ψ ) ↔ ∀ x ( φ → ψ ) ) ).

    If x is not free in φ, then the implication (∃ x φ → ∀ x ψ) is
    equivalent to ∀ x ( φ → ψ ).
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wnf wex wal wi 19.38 id nfrd alim syl9 impbid2.
    """
    lb = ProofBuilder(sys, "19.38a")
    # 19.38: (∃ x φ → ∀ x ψ) → ∀ x ( φ → ψ )
    s1 = lb.ref(
        "s1",
        "( ∃ x φ → ∀ x ψ ) → ∀ x ( φ → ψ )",
        ref="19.38",
        note="19.38",
    )
    # id: Ⅎ x φ → Ⅎ x φ
    s2 = lb.ref(
        "s2",
        "F/ x φ → F/ x φ",
        ref="id",
        note="id",
    )
    # nfrd with hypothesis id: Ⅎ x φ → ( ∃ x φ → ∀ x φ )
    s3 = lb.ref(
        "s3",
        "F/ x φ → ( ∃ x φ → ∀ x φ )",
        s2,
        ref="nfrd",
        note="nfrd id",
    )
    # alim: ∀ x ( φ → ψ ) → ( ∀ x φ → ∀ x ψ )
    s4 = lb.ref(
        "s4",
        "∀ x ( φ → ψ ) → ( ∀ x φ → ∀ x ψ )",
        ref="alim",
        note="alim",
    )
    # syl9 with nfrd and alim:
    # Ⅎ x φ → ( ∀ x ( φ → ψ ) → ( ∃ x φ → ∀ x ψ ) )
    s5 = lb.ref(
        "s5",
        "F/ x φ → ( ∀ x ( φ → ψ ) → ( ∃ x φ → ∀ x ψ ) )",
        s3,
        s4,
        ref="syl9",
        note="syl9 nfrd, alim",
    )
    # impbid2: combine the two directions
    # ( Ⅎ x φ → ( ( ∃ x φ → ∀ x ψ ) ↔ ∀ x ( φ → ψ ) ) )
    res = lb.ref(
        "res",
        "F/ x φ → ( ( ∃ x φ → ∀ x ψ ) ↔ ∀ x ( φ → ψ ) )",
        s1,
        s5,
        ref="impbid2",
        note="impbid2 19.38, syl9",
    )
    return lb.build(res)


def prove_19_21t(sys: System) -> Proof:
    """19.21t: Ⅎ x φ → ( ∀ x ( φ → ψ ) ↔ ( φ → ∀ x ψ ) ).

    If x is not free in φ, then universal quantification distributes
    over implication: ∀ x ( φ → ψ ) is equivalent to ( φ → ∀ x ψ ).
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wnf wex wal wi 19.38a 19.9t imbi1d bitr3d.
    """
    lb = ProofBuilder(sys, "19.21t")
    # 19.9t: Ⅎ x φ → ( ∃ x φ ↔ φ )
    s1 = lb.ref(
        "s1",
        "Ⅎ x φ → ( ∃ x φ ↔ φ )",
        ref="19.9t",
        note="19.9t",
    )
    # imbi1d with 19.9t: Ⅎ x φ → ( ( ∃ x φ → ∀ x ψ ) ↔ ( φ → ∀ x ψ ) )
    s2 = lb.ref(
        "s2",
        "Ⅎ x φ → ( ( ∃ x φ → ∀ x ψ ) ↔ ( φ → ∀ x ψ ) )",
        s1,
        ref="imbi1d",
        note="imbi1d 19.9t",
    )
    # 19.38a: Ⅎ x φ → ( ( ∃ x φ → ∀ x ψ ) ↔ ∀ x ( φ → ψ ) )
    s3 = lb.ref(
        "s3",
        "Ⅎ x φ → ( ( ∃ x φ → ∀ x ψ ) ↔ ∀ x ( φ → ψ ) )",
        ref="19.38a",
        note="19.38a",
    )
    # bitr3d: Ⅎ x φ → ( ∀ x ( φ → ψ ) ↔ ( φ → ∀ x ψ ) )
    res = lb.ref(
        "res",
        "Ⅎ x φ → ( ∀ x ( φ → ψ ) ↔ ( φ → ∀ x ψ ) )",
        s3,
        s2,
        ref="bitr3d",
        note="bitr3d 19.38a, imbi1d",
    )
    return lb.build(res)


def prove_19_21v(sys: System) -> Proof:
    """19.21v: ( ∀ x ( φ → ψ ) ↔ ( φ → ∀ x ψ ) ).

    If φ → ψ holds for all x, then φ implies ψ for all x; and
    conversely, if φ implies ψ for all x, then φ → ψ holds for all x.
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: wi wal stdpc5v wex ax5e imim1i 19.38 syl impbii.
    """
    lb = ProofBuilder(sys, "19.21v")
    # Forward direction: ∀x(φ → ψ) → (φ → ∀xψ)
    s_fwd = lb.ref(
        "s_fwd",
        "∀ x ( φ → ψ ) → ( φ → ∀ x ψ )",
        ref="stdpc5v",
        note="stdpc5v",
    )
    # Reverse direction: (φ → ∀xψ) → ∀x(φ → ψ)
    # ax5e: ∃x φ → φ
    s_ax5e = lb.ref(
        "s_ax5e",
        "∃ x φ → φ",
        ref="ax5e",
        note="ax5e",
    )
    # imim1i with ax5e as hypothesis and χ := ∀x ψ:
    #   (φ → ∀x ψ) → (∃x φ → ∀x ψ)
    s_imim1i = lb.ref(
        "s_imim1i",
        "( φ → ∀ x ψ ) → ( ∃ x φ → ∀ x ψ )",
        s_ax5e,
        ref="imim1i",
        note="imim1i ax5e",
    )
    # 19.38: (∃x φ → ∀x ψ) → ∀x(φ → ψ)
    s_19_38 = lb.ref(
        "s_19_38",
        "( ∃ x φ → ∀ x ψ ) → ∀ x ( φ → ψ )",
        ref="19.38",
        note="19.38",
    )
    # syl: chain s_imim1i and s_19_38
    s_rev = lb.ref(
        "s_rev",
        "( φ → ∀ x ψ ) → ∀ x ( φ → ψ )",
        s_imim1i,
        s_19_38,
        ref="syl",
        note="syl imim1i, 19.38",
    )
    # impbii: combine both directions
    res = lb.ref(
        "res",
        "( ∀ x ( φ → ψ ) ↔ ( φ → ∀ x ψ ) )",
        s_fwd,
        s_rev,
        ref="impbii",
        note="impbii",
    )
    return lb.build(res)


def prove_19_32v(sys: System) -> Proof:
    """19.32v: ( ∀ x ( φ ∨ ψ ) ↔ ( φ ∨ ∀ x ψ ) ).

    A universal quantifier distributes over a disjunction when the
    quantified variable is not free in the first disjunct.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: 19.21v df-or albii 3bitr4i.
    """
    lb = ProofBuilder(sys, "19.32v")

    # df-or: ( φ ∨ ψ ) ↔ ( ¬ φ → ψ )
    s_df_or = lb.ref(
        "s_df_or",
        "( φ ∨ ψ ) ↔ ( ¬ φ → ψ )",
        ref="df-or",
        note="df-or",
    )

    # albii applied to df-or: ∀ x ( φ ∨ ψ ) ↔ ∀ x ( ¬ φ → ψ )
    s_albii = lb.ref(
        "s_albii",
        "∀ x ( φ ∨ ψ ) ↔ ∀ x ( ¬ φ → ψ )",
        s_df_or,
        ref="albii",
        note="albii df-or",
    )

    # 19.21v with ¬φ substituted for φ:
    # ∀ x ( ¬ φ → ψ ) ↔ ( ¬ φ → ∀ x ψ )
    s_19_21v = lb.ref(
        "s_19_21v",
        "∀ x ( ¬ φ → ψ ) ↔ ( ¬ φ → ∀ x ψ )",
        ref="19.21v",
        note="19.21v",
    )

    # df-or with ∀xψ substituted for ψ:
    # ( φ ∨ ∀ x ψ ) ↔ ( ¬ φ → ∀ x ψ )
    s_df_or2 = lb.ref(
        "s_df_or2",
        "( φ ∨ ∀ x ψ ) ↔ ( ¬ φ → ∀ x ψ )",
        ref="df-or",
        note="df-or",
    )

    # 3bitr4i chains the three biconditionals:
    # h1: ∀x(¬φ → ψ) ↔ (¬φ → ∀xψ)
    # h2: ∀x(φ ∨ ψ) ↔ ∀x(¬φ → ψ)
    # h3: (φ ∨ ∀xψ) ↔ (¬φ → ∀xψ)
    # conclusion: ∀x(φ ∨ ψ) ↔ (φ ∨ ∀xψ)
    res = lb.ref(
        "res",
        "( ∀ x ( φ ∨ ψ ) ↔ ( φ ∨ ∀ x ψ ) )",
        s_19_21v,
        s_albii,
        s_df_or2,
        ref="3bitr4i",
        note="3bitr4i",
    )

    return lb.build(res)


def prove_19_31v(sys: System) -> Proof:
    """19.31v: ( ∀ x ( φ ∨ ψ ) ↔ ( ∀ x φ ∨ ψ ) ).

    A universal quantifier distributes over a disjunction when the
    quantified variable is not free in the second disjunct.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: 19.32v orcom albii 3bitr4i.
    """
    lb = ProofBuilder(sys, "19.31v")

    # orcom: ( φ ∨ ψ ) ↔ ( ψ ∨ φ )
    s_orcom = lb.ref(
        "s_orcom",
        "( φ ∨ ψ ) ↔ ( ψ ∨ φ )",
        ref="orcom",
        note="orcom",
    )

    # albii on orcom: ∀ x ( φ ∨ ψ ) ↔ ∀ x ( ψ ∨ φ )
    s_albii = lb.ref(
        "s_albii",
        "∀ x ( φ ∨ ψ ) ↔ ∀ x ( ψ ∨ φ )",
        s_orcom,
        ref="albii",
        note="albii orcom",
    )

    # 19.32v with ψ and φ swapped: ∀ x ( ψ ∨ φ ) ↔ ( ψ ∨ ∀ x φ )
    s_19_32v = lb.ref(
        "s_19_32v",
        "∀ x ( ψ ∨ φ ) ↔ ( ψ ∨ ∀ x φ )",
        ref="19.32v",
        note="19.32v",
    )

    # orcom on ( ψ ∨ ∀ x φ ): ( ψ ∨ ∀ x φ ) ↔ ( ∀ x φ ∨ ψ )
    s_orcom2 = lb.ref(
        "s_orcom2",
        "( ψ ∨ ∀ x φ ) ↔ ( ∀ x φ ∨ ψ )",
        ref="orcom",
        note="orcom",
    )

    s_chain = lb.ref(
        "s_chain",
        "∀ x ( φ ∨ ψ ) ↔ ( ψ ∨ ∀ x φ )",
        s_albii,
        s_19_32v,
        ref="bitri",
        note="bitri albii, 19.32v",
    )

    res = lb.ref(
        "res",
        "( ∀ x ( φ ∨ ψ ) ↔ ( ∀ x φ ∨ ψ ) )",
        s_chain,
        s_orcom2,
        ref="bitri",
        note="bitri chain, orcom",
    )

    return lb.build(res)


def prove_19_23v(sys: System) -> Proof:
    """19.23v: ( ∀ x ( φ → ψ ) ↔ ( ∃ x φ → ψ ) ).

    If for all x, φ implies ψ, then if there exists x such that φ, ψ holds;
    and conversely, if the existence of x with φ implies ψ, then
    for all x, φ implies ψ.  (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wi wal wex exim ax5e syl6 ax-5 imim2i 19.38 syl impbii.
    """
    lb = ProofBuilder(sys, "19.23v")
    # Forward direction: ∀x(φ → ψ) → (∃x φ → ψ)
    # exim: ∀x(φ → ψ) → (∃x φ → ∃x ψ)
    s1 = lb.ref(
        "s1",
        "∀ x ( φ → ψ ) → ( ∃ x φ → ∃ x ψ )",
        ref="exim",
        note="exim",
    )
    # ax5e: ∃x ψ → ψ
    s2 = lb.ref(
        "s2",
        "∃ x ψ → ψ",
        ref="ax5e",
        note="ax5e",
    )
    # syl6: combine s1 and s2
    s3 = lb.ref(
        "s3",
        "∀ x ( φ → ψ ) → ( ∃ x φ → ψ )",
        s1,
        s2,
        ref="syl6",
        note="syl6 exim, ax5e",
    )
    # Reverse direction: (∃x φ → ψ) → ∀x(φ → ψ)
    # ax-5: ψ → ∀x ψ
    s4 = lb.ref(
        "s4",
        "ψ → ∀ x ψ",
        ref="ax-5",
        note="ax-5 — ax-5",
    )
    # imim2i: (ψ → ∀x ψ) → ((∃x φ → ψ) → (∃x φ → ∀x ψ))
    s5 = lb.ref(
        "s5",
        "( ∃ x φ → ψ ) → ( ∃ x φ → ∀ x ψ )",
        s4,
        ref="imim2i",
        note="imim2i ax-5",
    )
    # 19.38: (∃x φ → ∀x ψ) → ∀x(φ → ψ)
    s6 = lb.ref(
        "s6",
        "( ∃ x φ → ∀ x ψ ) → ∀ x ( φ → ψ )",
        ref="19.38",
        note="19.38",
    )
    # syl: combine s5 and s6
    s7 = lb.ref(
        "s7",
        "( ∃ x φ → ψ ) → ∀ x ( φ → ψ )",
        s5,
        s6,
        ref="syl",
        note="syl imim2i, 19.38",
    )
    # impbii: combine both directions
    res = lb.ref(
        "res",
        "( ∀ x ( φ → ψ ) ↔ ( ∃ x φ → ψ ) )",
        s3,
        s7,
        ref="impbii",
        note="impbii",
    )
    return lb.build(res)


def prove_equsv(sys: System) -> Proof:
    """equsv: ( ∀ x ( x = y → φ ) ↔ φ ).

    If for all x, equality with y implies φ, then φ holds; conversely,
    if φ holds, then for all x, equality with y implies φ.
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "equsv")
    # 19.23v with φ := ( x = y ): ( ∀ x ( x = y → φ ) ↔ ( ∃ x x = y → φ ) )
    s1 = lb.ref(
        "s1",
        "( ∀ x ( x = y → φ ) ↔ ( ∃ x x = y → φ ) )",
        ref="19.23v",
        note="19.23v",
    )
    # ax6ev: ∃ x x = y
    s2 = lb.ref(
        "s2",
        "∃ x x = y",
        ref="ax6ev",
        note="ax6ev",
    )
    # a1bi with ax6ev as hypothesis: ( φ ↔ ( ∃ x x = y → φ ) )
    s3 = lb.ref(
        "s3",
        "( φ ↔ ( ∃ x x = y → φ ) )",
        s2,
        ref="a1bi",
        note="a1bi ax6ev",
    )
    # bitr4i: ( ∀ x ( x = y → φ ) ↔ φ )
    res = lb.ref(
        "res",
        "( ∀ x ( x = y → φ ) ↔ φ )",
        s1,
        s3,
        ref="bitr4i",
        note="bitr4i 19.23v, a1bi",
    )
    return lb.build(res)


def prove_equsalvw(sys: System) -> Proof:
    """equsalvw: ( ∀ x ( x = y → φ ) ↔ ψ ).

    Equivalence of a universal quantifier and an equivalent formula
    when equality with a common variable is involved.
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "equsalvw")
    h1 = lb.hyp("equsalvw.1", "( x = y → ( φ ↔ ψ ) )")
    # pm5.74i: ( ( x = y → φ ) ↔ ( x = y → ψ ) )
    s1 = lb.ref(
        "s1",
        "( ( x = y → φ ) ↔ ( x = y → ψ ) )",
        h1,
        ref="pm5.74i",
        note="pm5.74i",
    )
    # albii: ( ∀ x ( x = y → φ ) ↔ ∀ x ( x = y → ψ ) )
    s2 = lb.ref(
        "s2",
        "( ∀ x ( x = y → φ ) ↔ ∀ x ( x = y → ψ ) )",
        s1,
        ref="albii",
        note="albii",
    )
    # equsv: ( ∀ x ( x = y → ψ ) ↔ ψ )
    s3 = lb.ref(
        "s3",
        "( ∀ x ( x = y → ψ ) ↔ ψ )",
        ref="equsv",
        note="equsv",
    )
    # bitri: ( ∀ x ( x = y → φ ) ↔ ψ )
    res = lb.ref(
        "res",
        "( ∀ x ( x = y → φ ) ↔ ψ )",
        s2,
        s3,
        ref="bitri",
        note="bitri",
    )
    return lb.build(res)


def prove_equsexvw(sys: System) -> Proof:
    """equsexvw: ( ∃ x ( x = y ∧ φ ) ↔ ψ ).

    Existential version of equsalvw: from ( x = y → ( φ ↔ ψ ) ),
    derive ( ∃ x ( x = y ∧ φ ) ↔ ψ ).
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "equsexvw")
    h1 = lb.hyp("equsexvw.1", "( x = y → ( φ ↔ ψ ) )")
    # alinexa: ∀ x ( x = y → ¬ φ ) ↔ ¬ ∃ x ( x = y ∧ φ )
    s1 = lb.ref(
        "s1",
        "∀ x ( x = y → ¬ φ ) ↔ ¬ ∃ x ( x = y ∧ φ )",
        ref="alinexa",
        note="alinexa",
    )
    # notbid: ( x = y → ( ¬ φ ↔ ¬ ψ ) )
    s2 = lb.ref(
        "s2",
        "( x = y → ( ¬ φ ↔ ¬ ψ ) )",
        h1,
        ref="notbid",
        note="notbid",
    )
    # equsalvw: ∀ x ( x = y → ¬ φ ) ↔ ¬ ψ
    s3 = lb.ref(
        "s3",
        "∀ x ( x = y → ¬ φ ) ↔ ¬ ψ",
        s2,
        ref="equsalvw",
        note="equsalvw",
    )
    # bitr3i: ¬ ∃ x ( x = y ∧ φ ) ↔ ¬ ψ
    s4 = lb.ref(
        "s4",
        "¬ ∃ x ( x = y ∧ φ ) ↔ ¬ ψ",
        s1,
        s3,
        ref="bitr3i",
        note="bitr3i alinexa, equsalvw",
    )
    # con4bii: ∃ x ( x = y ∧ φ ) ↔ ψ
    res = lb.ref(
        "res",
        "∃ x ( x = y ∧ φ ) ↔ ψ",
        s4,
        ref="con4bii",
        note="con4bii",
    )
    return lb.build(res)


def prove_alsyl(sys: System) -> Proof:
    """alsyl: ( ( ∀ x ( φ → ψ ) ∧ ∀ x ( ψ → χ ) ) → ∀ x ( φ → χ ) ).

    Universal quantifier distributes over a syllogism.
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: wi pm3.33 alanimi.
    """
    lb = ProofBuilder(sys, "alsyl")
    s1 = lb.ref(
        "s1",
        "( ( φ → ψ ) ∧ ( ψ → χ ) ) → ( φ → χ )",
        ref="pm3.33",
        note="pm3.33",
    )
    res = lb.ref(
        "res",
        "( ( ∀ x ( φ → ψ ) ∧ ∀ x ( ψ → χ ) ) → ∀ x ( φ → χ ) )",
        s1,
        ref="alanimi",
        note="alanimi pm3.33",
    )
    return lb.build(res)


def prove_altru(sys: System) -> Proof:
    """altru: ∀ x T.

    Truth holds universally.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wtru tru ax-gen.
    """
    lb = ProofBuilder(sys, "altru")
    s_tru = lb.ref("s_tru", "T.", ref="tru", note="tru")
    s_gen = lb.ref("s_gen", "T. → ∀ x T.", ref="ax-5", note="ax-5 — ax-gen")
    res = lb.mp("res", s_tru, s_gen, note="MP tru, ax-5")
    return lb.build(res)


def prove_bamalip(sys: System) -> Proof:
    """bamalip: ∃ x ( χ ∧ φ ).

    Syllogism bamalip: from ∀ x ( φ → ψ ), ∀ x ( ψ → χ ), and ∃ x φ,
    derive ∃ x ( χ ∧ φ ).  Uses barbari to combine the universal
    hypotheses and existential, then commutes the conjunction with
    exancom/mpbi.
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: wa wex barbari exancom mpbi.
    """
    lb = ProofBuilder(sys, "bamalip")
    h_maj = lb.hyp("bamalip.maj", "∀ x ( φ → ψ )")
    h_min = lb.hyp("bamalip.min", "∀ x ( ψ → χ )")
    h_e = lb.hyp("bamalip.e", "∃ x φ")

    # barbari: from bamalip.min (maj), bamalip.maj (min), bamalip.e → ∃ x ( φ ∧ χ )
    s1 = lb.ref(
        "s1",
        "∃ x ( φ ∧ χ )",
        h_min,
        h_maj,
        h_e,
        ref="barbari",
        note="barbari bamalip.min, bamalip.maj, bamalip.e",
    )

    # exancom: ( ∃ x ( φ ∧ χ ) ↔ ∃ x ( χ ∧ φ ) )
    s2 = lb.ref(
        "s2",
        "( ∃ x ( φ ∧ χ ) ↔ ∃ x ( χ ∧ φ ) )",
        ref="exancom",
        note="exancom",
    )

    # mpbi: from s1 and s2, derive ∃ x ( χ ∧ φ )
    res = lb.ref(
        "res",
        "∃ x ( χ ∧ φ )",
        s1,
        s2,
        ref="mpbi",
        note="mpbi s1, exancom",
    )
    return lb.build(res)


def prove_barbara(sys: System) -> Proof:
    """barbara: ∀ x ( χ → ψ ).

    Syllogism under a universal quantifier.
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: alsyl mp2an.
    """
    lb = ProofBuilder(sys, "barbara")
    h_maj = lb.hyp("barbara.maj", "∀ x ( φ → ψ )")
    h_min = lb.hyp("barbara.min", "∀ x ( χ → φ )")
    s1 = lb.ref(
        "s1",
        "( ( ∀ x ( χ → φ ) ∧ ∀ x ( φ → ψ ) ) → ∀ x ( χ → ψ ) )",
        ref="alsyl",
        note="alsyl",
    )
    res = lb.ref(
        "res",
        "∀ x ( χ → ψ )",
        h_min,
        h_maj,
        s1,
        ref="mp2an",
        note="mp2an barbara.min, barbara.maj, alsyl",
    )
    return lb.build(res)


def prove_celarent(sys: System) -> Proof:
    """celarent: ∀ x ( χ → ¬ ψ ).

    Syllogism under a universal quantifier with negated consequent.
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: wn barbara.
    """
    lb = ProofBuilder(sys, "celarent")
    h_maj = lb.hyp("celarent.maj", "∀ x ( φ → ¬ ψ )")
    h_min = lb.hyp("celarent.min", "∀ x ( χ → φ )")
    s1 = lb.ref(
        "s1",
        "( ( ∀ x ( χ → φ ) ∧ ∀ x ( φ → ¬ ψ ) ) → ∀ x ( χ → ¬ ψ ) )",
        ref="alsyl",
        note="alsyl",
    )
    res = lb.ref(
        "res",
        "∀ x ( χ → ¬ ψ )",
        h_min,
        h_maj,
        s1,
        ref="mp2an",
        note="mp2an celarent.min, celarent.maj, alsyl",
    )
    return lb.build(res)


def prove_camestres(sys: System) -> Proof:
    """camestres: ∀ x ( χ → ¬ φ ).

    Syllogism under a universal quantifier.  (Contributed by NM, 3-Jan-1993.)
    set.mm proof: con3 alimi ax-mp celarent.
    """
    lb = ProofBuilder(sys, "camestres")
    h_maj = lb.hyp("camestres.maj", "∀ x ( φ → ψ )")
    h_min = lb.hyp("camestres.min", "∀ x ( χ → ¬ ψ )")
    # con3: ( φ → ψ ) → ( ¬ ψ → ¬ φ )
    s1 = lb.ref(
        "s1",
        "( φ → ψ ) → ( ¬ ψ → ¬ φ )",
        ref="con3",
        note="con3",
    )
    # alimi: A. x ( φ → ψ ) → A. x ( ¬ ψ → ¬ φ )
    s2 = lb.ref(
        "s2",
        "A. x ( φ → ψ ) → A. x ( ¬ ψ → ¬ φ )",
        s1,
        ref="alimi",
        note="alimi con3",
    )
    # ax-mp: A. x ( ¬ ψ → ¬ φ )
    s3 = lb.mp("s3", h_maj, s2, note="ax-mp camestres.maj, alimi")
    # celarent: ∀ x ( χ → ¬ φ )
    res = lb.ref(
        "res",
        "∀ x ( χ → ¬ φ )",
        s3,
        h_min,
        ref="celarent",
        note="celarent",
    )
    return lb.build(res)


def prove_calemes(sys: System) -> Proof:
    """calemes: ∀ x ( χ → ¬ φ ).

    Syllogism under a universal quantifier.
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: con2 alimi ax-mp camestres.
    """
    lb = ProofBuilder(sys, "calemes")
    h_maj = lb.hyp("calemes.maj", "∀ x ( φ → ψ )")
    h_min = lb.hyp("calemes.min", "∀ x ( ψ → ¬ χ )")
    # con2: ( ψ → ¬ χ ) → ( χ → ¬ ψ )
    s1 = lb.ref(
        "s1",
        "( ψ → ¬ χ ) → ( χ → ¬ ψ )",
        ref="con2",
        note="con2",
    )
    # alimi: ∀ x ( ψ → ¬ χ ) → ∀ x ( χ → ¬ ψ )
    s2 = lb.ref(
        "s2",
        "∀ x ( ψ → ¬ χ ) → ∀ x ( χ → ¬ ψ )",
        s1,
        ref="alimi",
        note="alimi con2",
    )
    # ax-mp: ∀ x ( χ → ¬ ψ )
    s3 = lb.mp("s3", h_min, s2, note="ax-mp calemes.min, alimi")
    # camestres: ∀ x ( χ → ¬ φ )
    res = lb.ref(
        "res",
        "∀ x ( χ → ¬ φ )",
        h_maj,
        s3,
        ref="camestres",
        note="camestres",
    )
    return lb.build(res)


def prove_cesare(sys: System) -> Proof:
    """cesare: ∀ x ( χ → ¬ φ ).

    Syllogism under a universal quantifier with negated consequent.
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: wn con2 alimi ax-mp celarent.
    """
    lb = ProofBuilder(sys, "cesare")
    h_maj = lb.hyp("cesare.maj", "∀ x ( φ → ¬ ψ )")
    h_min = lb.hyp("cesare.min", "∀ x ( χ → ψ )")
    # con2: ( φ → ¬ ψ ) → ( ψ → ¬ φ )
    s1 = lb.ref(
        "s1",
        "( φ → ¬ ψ ) → ( ψ → ¬ φ )",
        ref="con2",
        note="con2",
    )
    # alimi: ∀ x ( φ → ¬ ψ ) → ∀ x ( ψ → ¬ φ )
    s2 = lb.ref(
        "s2",
        "∀ x ( φ → ¬ ψ ) → ∀ x ( ψ → ¬ φ )",
        s1,
        ref="alimi",
        note="alimi con2",
    )
    # ax-mp: ∀ x ( ψ → ¬ φ )
    s3 = lb.mp("s3", h_maj, s2, note="ax-mp cesare.maj, alimi")
    # celarent: ∀ x ( χ → ¬ φ )
    res = lb.ref(
        "res",
        "∀ x ( χ → ¬ φ )",
        s3,
        h_min,
        ref="celarent",
        note="celarent",
    )
    return lb.build(res)


def prove_cesaro(sys: System) -> Proof:
    """cesaro: ∃ x ( χ ∧ ¬ φ ).

    Syllogism cesaro: from ∀ x ( φ → ¬ ψ ), ∀ x ( χ → ψ ),
    and ∃ x χ, derive ∃ x ( χ ∧ ¬ φ ).
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: cesare barbarilem.
    """
    lb = ProofBuilder(sys, "cesaro")
    h_maj = lb.hyp("cesaro.maj", "∀ x ( φ → ¬ ψ )")
    h_min = lb.hyp("cesaro.min", "∀ x ( χ → ψ )")
    h_e = lb.hyp("cesaro.e", "∃ x χ")
    # cesare: from ∀ x ( φ → ¬ ψ ) and ∀ x ( χ → ψ ), derive ∀ x ( χ → ¬ φ )
    s1 = lb.ref(
        "s1",
        "∀ x ( χ → ¬ φ )",
        h_maj,
        h_min,
        ref="cesare",
        note="cesare cesaro.maj, cesaro.min",
    )
    # barbarilem: from ∀ x ( χ → ¬ φ ) and ∃ x χ, derive ∃ x ( χ ∧ ¬ φ )
    res = lb.ref(
        "res",
        "∃ x ( χ ∧ ¬ φ )",
        s1,
        h_e,
        ref="barbarilem",
        note="barbarilem s1, cesaro.e",
    )
    return lb.build(res)


def prove_darii(sys: System) -> Proof:
    """darii: ∃ x ( χ ∧ ψ ).

    Syllogism darii: from ∀ x ( φ → ψ ) and ∃ x ( χ ∧ φ ),
    derive ∃ x ( χ ∧ ψ ).
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: wa wi wal wex id anim2d alimi ax-mp exim mp2.
    """
    lb = ProofBuilder(sys, "darii")
    h_maj = lb.hyp("darii.maj", "∀ x ( φ → ψ )")
    h_min = lb.hyp("darii.min", "∃ x ( χ ∧ φ )")

    # id: ( φ → ψ ) → ( φ → ψ )
    s1 = lb.ref("s1", "( φ → ψ ) → ( φ → ψ )", ref="id", note="id")

    # anim2d id: ( φ → ψ ) → ( ( χ ∧ φ ) → ( χ ∧ ψ ) )
    s2 = lb.ref(
        "s2",
        "( φ → ψ ) → ( ( χ ∧ φ ) → ( χ ∧ ψ ) )",
        s1,
        ref="anim2d",
        note="anim2d id",
    )

    # alimi anim2d: ∀ x ( φ → ψ ) → ∀ x ( ( χ ∧ φ ) → ( χ ∧ ψ ) )
    s3 = lb.ref(
        "s3",
        "∀ x ( φ → ψ ) → ∀ x ( ( χ ∧ φ ) → ( χ ∧ ψ ) )",
        s2,
        ref="alimi",
        note="alimi anim2d",
    )

    # ax-mp: ∀ x ( ( χ ∧ φ ) → ( χ ∧ ψ ) )
    s4 = lb.mp("s4", h_maj, s3, note="ax-mp alimi, darii.maj")

    # exim: ∀ x ( ( χ ∧ φ ) → ( χ ∧ ψ ) ) → ( ∃ x ( χ ∧ φ ) → ∃ x ( χ ∧ ψ ) )
    s5 = lb.ref(
        "s5",
        "∀ x ( ( χ ∧ φ ) → ( χ ∧ ψ ) ) → ( ∃ x ( χ ∧ φ ) → ∃ x ( χ ∧ ψ ) )",
        ref="exim",
        note="exim",
    )

    # mp2: s4, darii.min, exim ⊢ ∃ x ( χ ∧ ψ )
    res = lb.ref(
        "res",
        "∃ x ( χ ∧ ψ )",
        s4,
        h_min,
        s5,
        ref="mp2",
        note="mp2 s4, darii.min, exim",
    )
    return lb.build(res)


def prove_ferio(sys: System) -> Proof:
    """ferio: ∃ x ( χ ∧ ¬ ψ ).

    Syllogism ferio: from ∀ x ( φ → ¬ ψ ) and ∃ x ( χ ∧ φ ),
    derive ∃ x ( χ ∧ ¬ ψ ).
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: wn darii.
    """
    lb = ProofBuilder(sys, "ferio")
    h_maj = lb.hyp("ferio.maj", "∀ x ( φ → ¬ ψ )")
    h_min = lb.hyp("ferio.min", "∃ x ( χ ∧ φ )")

    # darii: from ∀ x ( φ → ¬ ψ ) and ∃ x ( χ ∧ φ ), derive ∃ x ( χ ∧ ¬ ψ )
    res = lb.ref(
        "res",
        "∃ x ( χ ∧ ¬ ψ )",
        h_maj,
        h_min,
        ref="darii",
        note="darii",
    )
    return lb.build(res)


def prove_darapti(sys: System) -> Proof:
    """darapti: ∃ x ( χ ∧ ψ ).

    From ∀ x ( φ → ψ ), ∀ x ( φ → χ ), and ∃ x φ, derive
    ∃ x ( χ ∧ ψ ).
    """
    lb = ProofBuilder(sys, "darapti")
    h_maj = lb.hyp("darapti.maj", "∀ x ( φ → ψ )")
    h_min = lb.hyp("darapti.min", "∀ x ( φ → χ )")
    h_e = lb.hyp("darapti.e", "∃ x φ")
    s1 = lb.ref(
        "s1",
        "∃ x ( φ ∧ χ )",
        h_min,
        h_e,
        ref="barbarilem",
        note="barbarilem darapti.min, darapti.e",
    )
    s2 = lb.ref(
        "s2",
        "( ∃ x ( φ ∧ χ ) ↔ ∃ x ( χ ∧ φ ) )",
        ref="exancom",
        note="exancom",
    )
    s3 = lb.ref(
        "s3",
        "∃ x ( χ ∧ φ )",
        s1,
        s2,
        ref="mpbi",
        note="mpbi barbarilem, exancom",
    )
    res = lb.ref(
        "res",
        "∃ x ( χ ∧ ψ )",
        h_maj,
        s3,
        ref="darii",
        note="darii darapti.maj, s3",
    )
    return lb.build(res)


def prove_felapton(sys: System) -> Proof:
    """felapton: ∃ x ( χ ∧ ¬ ψ ).

    Syllogism felapton: from ∀ x ( φ → ¬ ψ ), ∀ x ( φ → χ ), and ∃ x φ,
    derive ∃ x ( χ ∧ ¬ ψ ).
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: wn darapti.
    """
    lb = ProofBuilder(sys, "felapton")
    h_maj = lb.hyp("felapton.maj", "∀ x ( φ → ¬ ψ )")
    h_min = lb.hyp("felapton.min", "∀ x ( φ → χ )")
    h_e = lb.hyp("felapton.e", "∃ x φ")

    # darapti: from ∀ x ( φ → ¬ ψ ), ∀ x ( φ → χ ), and ∃ x φ,
    # derive ∃ x ( χ ∧ ¬ ψ )
    res = lb.ref(
        "res",
        "∃ x ( χ ∧ ¬ ψ )",
        h_maj,
        h_min,
        h_e,
        ref="darapti",
        note="darapti",
    )
    return lb.build(res)


def prove_fesapo(sys: System) -> Proof:
    """fesapo: ∃ x ( χ ∧ ¬ φ ).

    Syllogism fesapo: from ∀ x ( φ → ¬ ψ ), ∀ x ( ψ → χ ), and ∃ x ψ,
    derive ∃ x ( χ ∧ ¬ φ ).
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: con2 alimi ax-mp felapton.
    """
    lb = ProofBuilder(sys, "fesapo")
    h_maj = lb.hyp("fesapo.maj", "∀ x ( φ → ¬ ψ )")
    h_min = lb.hyp("fesapo.min", "∀ x ( ψ → χ )")
    h_e = lb.hyp("fesapo.e", "∃ x ψ")

    # con2: ( φ → ¬ ψ ) → ( ψ → ¬ φ )
    s1 = lb.ref(
        "s1",
        "( φ → ¬ ψ ) → ( ψ → ¬ φ )",
        ref="con2",
        note="con2",
    )

    # alimi: ∀ x ( φ → ¬ ψ ) → ∀ x ( ψ → ¬ φ )
    s2 = lb.ref(
        "s2",
        "∀ x ( φ → ¬ ψ ) → ∀ x ( ψ → ¬ φ )",
        s1,
        ref="alimi",
        note="alimi con2",
    )

    # ax-mp: ∀ x ( ψ → ¬ φ )
    s3 = lb.mp("s3", h_maj, s2, note="ax-mp fesapo.maj, alimi")

    # felapton: from ∀ x ( ψ → ¬ φ ), ∀ x ( ψ → χ ), ∃ x ψ,
    # derive ∃ x ( χ ∧ ¬ φ )
    res = lb.ref(
        "res",
        "∃ x ( χ ∧ ¬ φ )",
        s3,
        h_min,
        h_e,
        ref="felapton",
        note="felapton",
    )
    return lb.build(res)


def prove_barbarilem(sys: System) -> Proof:
    """barbarilem: ∃ x ( φ ∧ ψ ).

    From ∀ x ( φ → ψ ) and ∃ x φ, derive ∃ x ( φ ∧ ψ ).
    """
    lb = ProofBuilder(sys, "barbarilem")
    h_maj = lb.hyp("barbarilem.maj", "∀ x ( φ → ψ )")
    h_min = lb.hyp("barbarilem.min", "∃ x φ")
    # exintr: ∀ x ( φ → ψ ) → ( ∃ x φ → ∃ x ( φ ∧ ψ ) )
    s1 = lb.ref(
        "s1",
        "∀ x ( φ → ψ ) → ( ∃ x φ → ∃ x ( φ ∧ ψ ) )",
        ref="exintr",
        note="exintr",
    )
    # mp2: barbarilem.maj, barbarilem.min, exintr ⊢ ∃ x ( φ ∧ ψ )
    res = lb.ref(
        "res",
        "∃ x ( φ ∧ ψ )",
        h_maj,
        h_min,
        s1,
        ref="mp2",
        note="mp2 barbarilem.maj, barbarilem.min, exintr",
    )
    return lb.build(res)


def prove_barbari(sys: System) -> Proof:
    """barbari: ∃ x ( χ ∧ ψ ).

    From ∀ x ( φ → ψ ), ∀ x ( χ → φ ), and ∃ x χ, derive ∃ x ( χ ∧ ψ ).
    """
    lb = ProofBuilder(sys, "barbari")
    h_maj = lb.hyp("barbari.maj", "∀ x ( φ → ψ )")
    h_min = lb.hyp("barbari.min", "∀ x ( χ → φ )")
    h_e = lb.hyp("barbari.e", "∃ x χ")
    # barbara: from ∀ x ( χ → φ ) and ∀ x ( φ → ψ ), derive ∀ x ( χ → ψ )
    s1 = lb.ref(
        "s1",
        "∀ x ( χ → ψ )",
        h_maj,
        h_min,
        ref="barbara",
        note="barbara barbari.maj, barbari.min",
    )
    # barbarilem: from ∀ x ( χ → ψ ) and ∃ x χ, derive ∃ x ( χ ∧ ψ )
    res = lb.ref(
        "res",
        "∃ x ( χ ∧ ψ )",
        s1,
        h_e,
        ref="barbarilem",
        note="barbarilem s1, barbari.e",
    )
    return lb.build(res)


def prove_festino(sys: System) -> Proof:
    """festino: ∃ x ( χ ∧ ¬ φ ).

    Syllogism festino: from ∀ x ( φ → ¬ ψ ) and ∃ x ( χ ∧ ψ ),
    derive ∃ x ( χ ∧ ¬ φ ).
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: wa wn wi wal wex con2 anim2d alimi ax-mp exim mp2.
    """
    lb = ProofBuilder(sys, "festino")
    h_maj = lb.hyp("festino.maj", "∀ x ( φ → ¬ ψ )")
    h_min = lb.hyp("festino.min", "∃ x ( χ ∧ ψ )")

    # con2: ( φ → ¬ ψ ) → ( ψ → ¬ φ )
    s1 = lb.ref(
        "s1",
        "( φ → ¬ ψ ) → ( ψ → ¬ φ )",
        ref="con2",
        note="con2",
    )

    # anim2d con2: ( φ → ¬ ψ ) → ( ( χ ∧ ψ ) → ( χ ∧ ¬ φ ) )
    s2 = lb.ref(
        "s2",
        "( φ → ¬ ψ ) → ( ( χ ∧ ψ ) → ( χ ∧ ¬ φ ) )",
        s1,
        ref="anim2d",
        note="anim2d con2",
    )

    # alimi anim2d: ∀ x ( φ → ¬ ψ ) → ∀ x ( ( χ ∧ ψ ) → ( χ ∧ ¬ φ ) )
    s3 = lb.ref(
        "s3",
        "∀ x ( φ → ¬ ψ ) → ∀ x ( ( χ ∧ ψ ) → ( χ ∧ ¬ φ ) )",
        s2,
        ref="alimi",
        note="alimi anim2d",
    )

    # ax-mp: ∀ x ( ( χ ∧ ψ ) → ( χ ∧ ¬ φ ) )
    s4 = lb.mp("s4", h_maj, s3, note="ax-mp alimi, festino.maj")

    # exim: ∀ x ( ( χ ∧ ψ ) → ( χ ∧ ¬ φ ) ) → ( ∃ x ( χ ∧ ψ ) → ∃ x ( χ ∧ ¬ φ ) )
    s5 = lb.ref(
        "s5",
        "∀ x ( ( χ ∧ ψ ) → ( χ ∧ ¬ φ ) ) → ( ∃ x ( χ ∧ ψ ) → ∃ x ( χ ∧ ¬ φ ) )",
        ref="exim",
        note="exim",
    )

    # mp2: s4, festino.min, exim ⊢ ∃ x ( χ ∧ ¬ φ )
    res = lb.ref(
        "res",
        "∃ x ( χ ∧ ¬ φ )",
        s4,
        h_min,
        s5,
        ref="mp2",
        note="mp2 s4, festino.min, exim",
    )
    return lb.build(res)


def prove_fresison(sys: System) -> Proof:
    """fresison: ∃ x ( χ ∧ ¬ φ ).

    Syllogism fresison: from ∀ x ( φ → ¬ ψ ) and ∃ x ( ψ ∧ χ ),
    derive ∃ x ( χ ∧ ¬ φ ).  The minor premise has its conjunction
    swapped relative to festino; apply exancom to swap it back.
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: wa wex exancom mpbi festino.
    """
    lb = ProofBuilder(sys, "fresison")
    h_maj = lb.hyp("fresison.maj", "∀ x ( φ → ¬ ψ )")
    h_min = lb.hyp("fresison.min", "∃ x ( ψ ∧ χ )")

    # exancom: ( ∃ x ( ψ ∧ χ ) ↔ ∃ x ( χ ∧ ψ ) )
    s1 = lb.ref(
        "s1",
        "( ∃ x ( ψ ∧ χ ) ↔ ∃ x ( χ ∧ ψ ) )",
        ref="exancom",
        note="exancom",
    )

    # mpbi fresison.min, exancom: ∃ x ( χ ∧ ψ )
    s2 = lb.ref(
        "s2",
        "∃ x ( χ ∧ ψ )",
        h_min,
        s1,
        ref="mpbi",
        note="mpbi fresison.min, exancom",
    )

    # festino: ∃ x ( χ ∧ ¬ φ )
    res = lb.ref(
        "res",
        "∃ x ( χ ∧ ¬ φ )",
        h_maj,
        s2,
        ref="festino",
        note="festino",
    )
    return lb.build(res)


def prove_ferison(sys: System) -> Proof:
    """ferison: ∃ x ( χ ∧ ¬ ψ ).

    Syllogism ferison: from ∀ x ( φ → ¬ ψ ) and ∃ x ( φ ∧ χ ),
    derive ∃ x ( χ ∧ ¬ ψ ).  An instance of datisi with ψ replaced
    by ¬ ψ.
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: wn datisi.
    """
    lb = ProofBuilder(sys, "ferison")
    h_maj = lb.hyp("ferison.maj", "∀ x ( φ → ¬ ψ )")
    h_min = lb.hyp("ferison.min", "∃ x ( φ ∧ χ )")

    # datisi: from ∀ x ( φ → ¬ ψ ) and ∃ x ( φ ∧ χ ),
    # derive ∃ x ( χ ∧ ¬ ψ )
    res = lb.ref(
        "res",
        "∃ x ( χ ∧ ¬ ψ )",
        h_maj,
        h_min,
        ref="datisi",
        note="datisi",
    )
    return lb.build(res)


def prove_baroco(sys: System) -> Proof:
    """baroco: ∃ x ( χ ∧ ¬ φ ).

    Syllogism baroco: from ∀ x ( φ → ψ ) and ∃ x ( χ ∧ ¬ ψ ),
    derive ∃ x ( χ ∧ ¬ φ ).
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: wa wn wi wal wex con3 anim2d alimi ax-mp exim mp2.
    """
    lb = ProofBuilder(sys, "baroco")
    h_maj = lb.hyp("baroco.maj", "∀ x ( φ → ψ )")
    h_min = lb.hyp("baroco.min", "∃ x ( χ ∧ ¬ ψ )")

    # con3: ( φ → ψ ) → ( ¬ ψ → ¬ φ )
    s1 = lb.ref(
        "s1",
        "( φ → ψ ) → ( ¬ ψ → ¬ φ )",
        ref="con3",
        note="con3",
    )

    # anim2d con3: ( φ → ψ ) → ( ( χ ∧ ¬ ψ ) → ( χ ∧ ¬ φ ) )
    s2 = lb.ref(
        "s2",
        "( φ → ψ ) → ( ( χ ∧ ¬ ψ ) → ( χ ∧ ¬ φ ) )",
        s1,
        ref="anim2d",
        note="anim2d con3",
    )

    # alimi anim2d: ∀ x ( φ → ψ ) → ∀ x ( ( χ ∧ ¬ ψ ) → ( χ ∧ ¬ φ ) )
    s3 = lb.ref(
        "s3",
        "∀ x ( φ → ψ ) → ∀ x ( ( χ ∧ ¬ ψ ) → ( χ ∧ ¬ φ ) )",
        s2,
        ref="alimi",
        note="alimi anim2d",
    )

    # ax-mp: ∀ x ( ( χ ∧ ¬ ψ ) → ( χ ∧ ¬ φ ) )
    s4 = lb.mp("s4", h_maj, s3, note="ax-mp alimi, baroco.maj")

    # exim: ∀ x ( ( χ ∧ ¬ ψ ) → ( χ ∧ ¬ φ ) ) → ( ∃ x ( χ ∧ ¬ ψ ) → ∃ x ( χ ∧ ¬ φ ) )
    s5 = lb.ref(
        "s5",
        "∀ x ( ( χ ∧ ¬ ψ ) → ( χ ∧ ¬ φ ) ) → ( ∃ x ( χ ∧ ¬ ψ ) → ∃ x ( χ ∧ ¬ φ ) )",
        ref="exim",
        note="exim",
    )

    # mp2: s4, baroco.min, exim ⊢ ∃ x ( χ ∧ ¬ φ )
    res = lb.ref(
        "res",
        "∃ x ( χ ∧ ¬ φ )",
        s4,
        h_min,
        s5,
        ref="mp2",
        note="mp2 s4, baroco.min, exim",
    )
    return lb.build(res)


def prove_camestros(sys: System) -> Proof:
    """camestros: ∃ x ( χ ∧ ¬ φ ).

    Syllogism camestros: from ∀ x ( φ → ψ ), ∀ x ( χ → ¬ ψ ), and
    ∃ x χ, derive ∃ x ( χ ∧ ¬ φ ).
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: wn camestres barbarilem.
    """
    lb = ProofBuilder(sys, "camestros")
    h_maj = lb.hyp("camestros.maj", "∀ x ( φ → ψ )")
    h_min = lb.hyp("camestros.min", "∀ x ( χ → ¬ ψ )")
    h_e = lb.hyp("camestros.e", "∃ x χ")
    # camestres: from camestros.maj and camestros.min, derive ∀ x ( χ → ¬ φ )
    s1 = lb.ref(
        "s1",
        "∀ x ( χ → ¬ φ )",
        h_maj,
        h_min,
        ref="camestres",
        note="camestres camestros.maj, camestros.min",
    )
    # barbarilem: from ∀ x ( χ → ¬ φ ) and ∃ x χ, derive ∃ x ( χ ∧ ¬ φ )
    res = lb.ref(
        "res",
        "∃ x ( χ ∧ ¬ φ )",
        s1,
        h_e,
        ref="barbarilem",
        note="barbarilem camestres, camestros.e",
    )
    return lb.build(res)


def prove_19_26(sys: System) -> Proof:
    """19.26: ∀ x ( φ ∧ ψ ) ↔ ( ∀ x φ ∧ ∀ x ψ ).

    Distributivity of the universal quantifier over conjunction.
    Both directions: forward via simpl/simpr+alimi+jca, reverse via
    id+alanimi.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wa simpl alimi simpr id alanimi impbii.
    """
    lb = ProofBuilder(sys, "19.26")
    # simpl: ( φ ∧ ψ ) → φ
    s1 = lb.ref("s1", "( φ ∧ ψ ) → φ", ref="simpl", note="simpl")
    # alimi simpl: ∀ x ( φ ∧ ψ ) → ∀ x φ
    s2 = lb.ref("s2", "∀ x ( φ ∧ ψ ) → ∀ x φ", s1, ref="alimi", note="alimi simpl")
    # simpr: ( φ ∧ ψ ) → ψ
    s3 = lb.ref("s3", "( φ ∧ ψ ) → ψ", ref="simpr", note="simpr")
    # alimi simpr: ∀ x ( φ ∧ ψ ) → ∀ x ψ
    s4 = lb.ref("s4", "∀ x ( φ ∧ ψ ) → ∀ x ψ", s3, ref="alimi", note="alimi simpr")
    # jca s2, s4: ∀ x ( φ ∧ ψ ) → ( ∀ x φ ∧ ∀ x ψ )
    s5 = lb.ref(
        "s5",
        "∀ x ( φ ∧ ψ ) → ( ∀ x φ ∧ ∀ x ψ )",
        s2,
        s4,
        ref="jca",
        note="jca",
    )
    # id: ( φ ∧ ψ ) → ( φ ∧ ψ )
    s6 = lb.ref("s6", "( φ ∧ ψ ) → ( φ ∧ ψ )", ref="id", note="id")
    # alanimi id: ( ∀ x φ ∧ ∀ x ψ ) → ∀ x ( φ ∧ ψ )
    s7 = lb.ref(
        "s7",
        "( ∀ x φ ∧ ∀ x ψ ) → ∀ x ( φ ∧ ψ )",
        s6,
        ref="alanimi",
        note="alanimi id",
    )
    # impbii s5, s7: ∀ x ( φ ∧ ψ ) ↔ ( ∀ x φ ∧ ∀ x ψ )
    res = lb.ref(
        "res",
        "∀ x ( φ ∧ ψ ) ↔ ( ∀ x φ ∧ ∀ x ψ )",
        s5,
        s7,
        ref="impbii",
        note="impbii",
    )
    return lb.build(res)


def prove_19_26_2(sys: System) -> Proof:
    """19.26-2: ∀ x ∀ y ( φ ∧ ψ ) ↔ ( ∀ x ∀ y φ ∧ ∀ x ∀ y ψ ).

    Distributivity of two universal quantifiers over conjunction.
    set.mm proof: wa wal 19.26 albii bitri.
    """
    lb = ProofBuilder(sys, "19.26-2")
    # 19.26 with variable y: ∀ y ( φ ∧ ψ ) ↔ ( ∀ y φ ∧ ∀ y ψ )
    s1 = lb.ref(
        "s1",
        "∀ y ( φ ∧ ψ ) ↔ ( ∀ y φ ∧ ∀ y ψ )",
        ref="19.26",
        note="19.26",
    )
    # albii with variable x: ∀ x ∀ y ( φ ∧ ψ ) ↔ ∀ x ( ∀ y φ ∧ ∀ y ψ )
    s2 = lb.ref(
        "s2",
        "∀ x ∀ y ( φ ∧ ψ ) ↔ ∀ x ( ∀ y φ ∧ ∀ y ψ )",
        s1,
        ref="albii",
        note="albii",
    )
    # 19.26 with variable x: ∀ x ( ∀ y φ ∧ ∀ y ψ ) ↔ ( ∀ x ∀ y φ ∧ ∀ x ∀ y ψ )
    s3 = lb.ref(
        "s3",
        "∀ x ( ∀ y φ ∧ ∀ y ψ ) ↔ ( ∀ x ∀ y φ ∧ ∀ x ∀ y ψ )",
        ref="19.26",
        note="19.26",
    )
    # bitri s2, s3: ∀ x ∀ y ( φ ∧ ψ ) ↔ ( ∀ x ∀ y φ ∧ ∀ x ∀ y ψ )
    res = lb.ref(
        "res",
        "∀ x ∀ y ( φ ∧ ψ ) ↔ ( ∀ x ∀ y φ ∧ ∀ x ∀ y ψ )",
        s2,
        s3,
        ref="bitri",
        note="bitri",
    )
    return lb.build(res)


def prove_albiim(sys: System) -> Proof:
    """albiim: ∀ x ( φ ↔ ψ ) ↔ ( ∀ x ( φ → ψ ) ∧ ∀ x ( ψ → φ ) ).

    Universal quantifier distributes over a biconditional, turning it
    into a conjunction of universally quantified implications.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wb wal wi wa dfbi2 albii 19.26 bitri.
    """
    lb = ProofBuilder(sys, "albiim")
    # dfbi2: ( φ ↔ ψ ) ↔ ( ( φ → ψ ) ∧ ( ψ → φ ) )
    s1 = lb.ref(
        "s1",
        "( φ ↔ ψ ) ↔ ( ( φ → ψ ) ∧ ( ψ → φ ) )",
        ref="dfbi2",
        note="dfbi2",
    )
    # albii s1: ∀ x ( φ ↔ ψ ) ↔ ∀ x ( ( φ → ψ ) ∧ ( ψ → φ ) )
    s2 = lb.ref(
        "s2",
        "∀ x ( φ ↔ ψ ) ↔ ∀ x ( ( φ → ψ ) ∧ ( ψ → φ ) )",
        s1,
        ref="albii",
        note="albii dfbi2",
    )
    # 19.26: ∀ x ( ( φ → ψ ) ∧ ( ψ → φ ) ) ↔ ( ∀ x ( φ → ψ ) ∧ ∀ x ( ψ → φ ) )
    s3 = lb.ref(
        "s3",
        "∀ x ( ( φ → ψ ) ∧ ( ψ → φ ) ) ↔ ( ∀ x ( φ → ψ ) ∧ ∀ x ( ψ → φ ) )",
        ref="19.26",
        note="19.26",
    )
    # bitri s2, s3: ∀ x ( φ ↔ ψ ) ↔ ( ∀ x ( φ → ψ ) ∧ ∀ x ( ψ → φ ) )
    res = lb.ref(
        "res",
        "∀ x ( φ ↔ ψ ) ↔ ( ∀ x ( φ → ψ ) ∧ ∀ x ( ψ → φ ) )",
        s2,
        s3,
        ref="bitri",
        note="bitri albii, 19.26",
    )
    return lb.build(res)


def prove_2albiim(sys: System) -> Proof:
    """2albiim: ∀ x ∀ y ( φ ↔ ψ ) ↔ ( ∀ x ∀ y ( φ → ψ ) ∧ ∀ x ∀ y ( ψ → φ ) ).

    Apply albiim with y, then albii with x, 19.26, and bitri.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wb wal wi wa albiim albii 19.26 bitri.
    """
    lb = ProofBuilder(sys, "2albiim")
    # albiim with variable y: ∀ y ( φ ↔ ψ ) ↔ ( ∀ y ( φ → ψ ) ∧ ∀ y ( ψ → φ ) )
    s1 = lb.ref(
        "s1",
        "∀ y ( φ ↔ ψ ) ↔ ( ∀ y ( φ → ψ ) ∧ ∀ y ( ψ → φ ) )",
        ref="albiim",
        note="albiim",
    )
    # albii s1 with variable x:
    #  ∀ x ∀ y ( φ ↔ ψ ) ↔ ∀ x ( ∀ y ( φ → ψ ) ∧ ∀ y ( ψ → φ ) )
    s2 = lb.ref(
        "s2",
        "∀ x ∀ y ( φ ↔ ψ ) ↔ ∀ x ( ∀ y ( φ → ψ ) ∧ ∀ y ( ψ → φ ) )",
        s1,
        ref="albii",
        note="albii albiim",
    )
    # 19.26: ∀ x ( ∀ y ( φ → ψ ) ∧ ∀ y ( ψ → φ ) )
    #     ↔ ( ∀ x ∀ y ( φ → ψ ) ∧ ∀ x ∀ y ( ψ → φ ) )
    s3 = lb.ref(
        "s3",
        "∀ x ( ∀ y ( φ → ψ ) ∧ ∀ y ( ψ → φ ) ) ↔ ( ∀ x ∀ y ( φ → ψ ) ∧ ∀ x ∀ y ( ψ → φ ) )",
        ref="19.26",
        note="19.26",
    )
    # bitri s2, s3:
    #  ∀ x ∀ y ( φ ↔ ψ ) ↔ ( ∀ x ∀ y ( φ → ψ ) ∧ ∀ x ∀ y ( ψ → φ ) )
    res = lb.ref(
        "res",
        "∀ x ∀ y ( φ ↔ ψ ) ↔ ( ∀ x ∀ y ( φ → ψ ) ∧ ∀ x ∀ y ( ψ → φ ) )",
        s2,
        s3,
        ref="bitri",
        note="bitri albii, 19.26",
    )
    return lb.build(res)


def prove_euex(sys: System) -> Proof:
    """euex: E! x φ → E. x φ.

    Existence uniqueness implies existence.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "euex")
    s1 = lb.ref(
        "s1",
        "E! x φ ↔ ( E. x φ ∧ E* x φ )",
        ref="df-eu",
        note="df-eu",
    )
    res = lb.ref(
        "res",
        "E! x φ → E. x φ",
        s1,
        ref="simplbi",
        note="simplbi df-eu",
    )
    return lb.build(res)


def prove_2eu2ex(sys: System) -> Proof:
    """2eu2ex: E! x E! y φ → ∃ x ∃ y φ.

    Existence uniqueness of a double existence implies double existence.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: weu wex euex eximi syl.
    """
    lb = ProofBuilder(sys, "2eu2ex")
    # euex: E! y φ → ∃ y φ
    s1 = lb.ref("s1", "E! y φ → ∃ y φ", ref="euex", note="euex")
    # eximi: ∃ x E! y φ → ∃ x ∃ y φ
    s2 = lb.ref("s2", "∃ x E! y φ → ∃ x ∃ y φ", s1, ref="eximi", note="eximi euex")
    # euex: E! x E! y φ → ∃ x E! y φ
    s3 = lb.ref("s3", "E! x E! y φ → ∃ x E! y φ", ref="euex", note="euex")
    # syl: E! x E! y φ → ∃ x ∃ y φ
    res = lb.ref("res", "E! x E! y φ → ∃ x ∃ y φ", s3, s2, ref="syl", note="syl euex, eximi")
    return lb.build(res)


def prove_eumo(sys: System) -> Proof:
    """eumo: E! x φ → E* x φ.

    Existence uniqueness implies at-most-one existence.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "eumo")
    s1 = lb.ref(
        "s1",
        "E! x φ ↔ ( E. x φ ∧ E* x φ )",
        ref="df-eu",
        note="df-eu",
    )
    res = lb.ref(
        "res",
        "E! x φ → E* x φ",
        s1,
        ref="simprbi",
        note="simprbi df-eu",
    )
    return lb.build(res)


def prove_eumoi(sys: System) -> Proof:
    """eumoi: E* x φ.

    Inference form of eumo. From the uniqueness hypothesis,
    deduce at-most-one existence.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "eumoi")
    hyp = lb.hyp("eumoi.1", "E! x φ")
    s1 = lb.ref("s1", "E! x φ → E* x φ", ref="eumo", note="eumo")
    res = lb.mp("res", hyp, s1, "MP eumoi.1, eumo")
    return lb.build(res)


def prove_eu3v(sys: System) -> Proof:
    """eu3v: ∃! x φ ↔ ( ∃ x φ ∧ ∃ y ∀ x ( φ → x = y ) ).

    Equivalence for "there exists exactly one".
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "eu3v")
    # df-eu: ∃! x φ ↔ ( ∃ x φ ∧ ∃* x φ )
    s1 = lb.ref(
        "s1",
        "∃! x φ ↔ ( ∃ x φ ∧ ∃* x φ )",
        ref="df-eu",
        note="df-eu",
    )
    # dfmo: ∃* x φ ↔ ∃ y ∀ x ( φ → x = y )
    s2 = lb.ref(
        "s2",
        "∃* x φ ↔ ∃ y ∀ x ( φ → x = y )",
        ref="dfmo",
        note="dfmo",
    )
    # anbi2i: ( ∃ x φ ∧ ∃* x φ ) ↔ ( ∃ x φ ∧ ∃ y ∀ x ( φ → x = y ) )
    s3 = lb.ref(
        "s3",
        "( ∃ x φ ∧ ∃* x φ ) ↔ ( ∃ x φ ∧ ∃ y ∀ x ( φ → x = y ) )",
        s2,
        ref="anbi2i",
        note="anbi2i dfmo",
    )
    # bitri: ∃! x φ ↔ ( ∃ x φ ∧ ∃ y ∀ x ( φ → x = y ) )
    res = lb.ref(
        "res",
        "∃! x φ ↔ ( ∃ x φ ∧ ∃ y ∀ x ( φ → x = y ) )",
        s1,
        s3,
        ref="bitri",
        note="bitri df-eu, anbi2i",
    )
    return lb.build(res)


def prove_euequ(sys: System) -> Proof:
    """euequ: ∃! x x = y.

    There exists exactly one set equal to a given set.
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "euequ")

    # ax6ev: ∃ x x = y
    s1 = lb.ref("s1", "∃ x x = y", ref="ax6ev", note="ax6ev")

    # ax6ev with x:=z: ∃ z z = y
    s2 = lb.ref("s2", "∃ z z = y", ref="ax6ev", note="ax6ev")

    # equeuclr with x:=z, y:=x, z:=y: z = y → (x = y → x = z)
    s3 = lb.ref(
        "s3",
        "z = y → (x = y → x = z)",
        ref="equeuclr",
        note="equeuclr",
    )

    # alrimiv: z = y → ∀ x (x = y → x = z)
    s4 = lb.ref(
        "s4",
        "z = y → ∀ x (x = y → x = z)",
        s3,
        ref="alrimiv",
        note="alrimiv",
    )

    # eximii: ∃ z ∀ x (x = y → x = z)
    s5 = lb.ref(
        "s5",
        "∃ z ∀ x (x = y → x = z)",
        s2,
        s4,
        ref="eximii",
        note="eximii",
    )

    # eu3v with φ:=(x = y), inner y:=z
    s6 = lb.ref(
        "s6",
        "∃! x (x = y) ↔ (∃ x (x = y) ∧ ∃ z ∀ x ((x = y) → x = z))",
        ref="eu3v",
        note="eu3v",
    )

    # mpbir2an
    res = lb.ref(
        "res",
        "∃! x (x = y)",
        s1,
        s5,
        s6,
        ref="mpbir2an",
        note="mpbir2an",
    )

    return lb.build(res)


def prove_exmoeub(sys: System) -> Proof:
    """exmoeub: ∃ x φ → ( ∃* x φ ↔ ∃! x φ ).

    From df-eu and baibr. If something exists, then at-most-one
    is equivalent to exactly-one.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "exmoeub")

    # df-eu: ∃! x φ ↔ ( ∃ x φ ∧ ∃* x φ )
    s1 = lb.ref(
        "s1",
        "∃! x φ ↔ ( ∃ x φ ∧ ∃* x φ )",
        ref="df-eu",
        note="df-eu",
    )

    # baibr: from ( φ ↔ ( ψ ∧ χ ) ) deduce ψ → ( χ ↔ φ )
    res = lb.ref(
        "res",
        "∃ x φ → ( ∃* x φ ↔ ∃! x φ )",
        s1,
        ref="baibr",
        note="baibr df-eu",
    )

    return lb.build(res)


def prove_moeuex(sys: System) -> Proof:
    """moeuex: ∃* x φ → ( ∃ x φ ↔ ∃! x φ ).

    From df-eu and rbaibr. If there exists at most one, then
    existence implies existence uniqueness.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "moeuex")

    # df-eu: ∃! x φ ↔ ( ∃ x φ ∧ ∃* x φ )
    s1 = lb.ref(
        "s1",
        "∃! x φ ↔ ( ∃ x φ ∧ ∃* x φ )",
        ref="df-eu",
        note="df-eu",
    )

    # rbaibr: from ( φ ↔ ( ψ ∧ χ ) ) deduce χ → ( ψ ↔ φ )
    res = lb.ref(
        "res",
        "∃* x φ → ( ∃ x φ ↔ ∃! x φ )",
        s1,
        ref="rbaibr",
        note="rbaibr df-eu",
    )

    return lb.build(res)


def prove_dfsbimp(sys: System) -> Proof:
    """dfsbimp: [ t x φ → ∀ y ( y = t → ∀ x ( x = y → φ ) ).

    Forward direction of the df-sb biconditional via simplbi.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wsb weq wi wal df-sb simplbi.
    """
    lb = ProofBuilder(sys, "dfsbimp")
    s1 = lb.ref(
        "s1",
        "[ t x φ ↔ ( ∀ y ( y = t → ∀ x ( x = y → φ ) ) ∧ ∀ z ( z = t → ∀ x ( x = z → φ ) ) )",
        ref="df-sb",
        note="df-sb",
    )
    res = lb.ref(
        "res",
        "[ t x φ → ∀ y ( y = t → ∀ x ( x = y → φ ) )",
        s1,
        ref="simplbi",
        note="simplbi df-sb",
    )
    return lb.build(res)


def prove_sbi1lem(sys: System) -> Proof:
    """sbi1lem: ( ( [ t / x ] ( φ → ψ ) ∧ [ t / x ] φ ) → ∀ y ( y = t → ∀ x ( x = y → ψ ) ).

    Lemma for sbi1.  Derive an implication relating two substitution
    instances to a quantified form.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbi1lem")

    # ax-2: ( ( x = y → ( φ → ψ ) ) → ( ( x = y → φ ) → ( x = y → ψ ) ) )
    s1 = lb.ref(
        "s1",
        "( ( x = y → ( φ → ψ ) ) → ( ( x = y → φ ) → ( x = y → ψ ) ) )",
        ref="ax-2",
        note="A2",
    )

    # al2imi: ∀ x ( x = y → ( φ → ψ ) ) → ( ∀ x ( x = y → φ ) → ∀ x ( x = y → ψ ) )
    s2 = lb.ref(
        "s2",
        "∀ x ( x = y → ( φ → ψ ) ) → ( ∀ x ( x = y → φ ) → ∀ x ( x = y → ψ ) )",
        s1,
        ref="al2imi",
        note="al2imi",
    )

    # imim3i: ( y = t → ∀ x ( x = y → ( φ → ψ ) ) ) → ( ( y = t → ∀ x ( x = y → φ ) ) → ( y = t → ∀ x ( x = y → ψ ) ) )
    s3 = lb.ref(
        "s3",
        "( y = t → ∀ x ( x = y → ( φ → ψ ) ) ) → ( ( y = t → ∀ x ( x = y → φ ) ) → ( y = t → ∀ x ( x = y → ψ ) ) )",
        s2,
        ref="imim3i",
        note="imim3i",
    )

    # al2imi: ∀ y ( y = t → ∀ x ( x = y → ( φ → ψ ) ) ) → ( ∀ y ( y = t → ∀ x ( x = y → φ ) ) → ∀ y ( y = t → ∀ x ( x = y → ψ ) ) )
    s4 = lb.ref(
        "s4",
        "∀ y ( y = t → ∀ x ( x = y → ( φ → ψ ) ) ) → ( ∀ y ( y = t → ∀ x ( x = y → φ ) ) → ∀ y ( y = t → ∀ x ( x = y → ψ ) ) )",
        s3,
        ref="al2imi",
        note="al2imi",
    )

    # dfsbimp: [ t x ( φ → ψ ) → ∀ y ( y = t → ∀ x ( x = y → ( φ → ψ ) ) )
    s5 = lb.ref(
        "s5",
        "[ t x ( φ → ψ ) → ∀ y ( y = t → ∀ x ( x = y → ( φ → ψ ) ) )",
        ref="dfsbimp",
        note="dfsbimp",
    )

    # dfsbimp: [ t x φ → ∀ y ( y = t → ∀ x ( x = y → φ ) )
    s6 = lb.ref(
        "s6",
        "[ t x φ → ∀ y ( y = t → ∀ x ( x = y → φ ) )",
        ref="dfsbimp",
        note="dfsbimp",
    )

    # syl2im: [ t x ( φ → ψ ) → ( [ t x φ → ∀ y ( y = t → ∀ x ( x = y → ψ ) ) )
    s7 = lb.ref(
        "s7",
        "[ t x ( φ → ψ ) → ( [ t x φ → ∀ y ( y = t → ∀ x ( x = y → ψ ) ) )",
        s5,
        s6,
        s4,
        ref="syl2im",
        note="syl2im",
    )

    # imp: ( [ t x ( φ → ψ ) ∧ [ t x φ ) → ∀ y ( y = t → ∀ x ( x = y → ψ ) )
    res = lb.ref(
        "res",
        "( [ t x ( φ → ψ ) ∧ [ t x φ ) → ∀ y ( y = t → ∀ x ( x = y → ψ ) )",
        s7,
        ref="imp",
        note="imp",
    )

    return lb.build(res)


def prove_sbi1(sys: System) -> Proof:
    """sbi1: [ y / x ] ( φ → ψ ) → ( [ y / x ] φ → [ y / x ] ψ ).

    Substitution distributes over implication.  Use sbi1lem twice
    (once with each dummy variable), combine with df-sb via sylanbrc,
    then export the conjunction with ex.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbi1")

    # sbi1lem with t := y and dummy y := u:
    #   ( ( [ y x ( φ → ψ ) ∧ [ y x φ ) → ∀ u ( u = y → ∀ x ( x = u → ψ ) ) )
    s1 = lb.ref(
        "s1",
        "( ( [ y x ( φ → ψ ) ∧ [ y x φ ) → ∀ u ( u = y → ∀ x ( x = u → ψ ) ) )",
        ref="sbi1lem",
        note="sbi1lem with u",
    )

    # sbi1lem with t := y and dummy y := z:
    #   ( ( [ y x ( φ → ψ ) ∧ [ y x φ ) → ∀ z ( z = y → ∀ x ( x = z → ψ ) ) )
    s2 = lb.ref(
        "s2",
        "( ( [ y x ( φ → ψ ) ∧ [ y x φ ) → ∀ z ( z = y → ∀ x ( x = z → ψ ) ) )",
        ref="sbi1lem",
        note="sbi1lem with z",
    )

    # df-sb: biconditional definition of proper substitution with y, u, z
    #   [ y x ψ ↔ ( ∀ u ( u = y → ∀ x ( x = u → ψ ) ) ∧ ∀ z ( z = y → ∀ x ( x = z → ψ ) ) )
    s3 = lb.ref(
        "s3",
        "[ y x ψ ↔ ( ∀ u ( u = y → ∀ x ( x = u → ψ ) ) ∧ ∀ z ( z = y → ∀ x ( x = z → ψ ) ) )",
        ref="df-sb",
        note="df-sb",
    )

    # sylanbrc: ( ( [ y x ( φ → ψ ) ∧ [ y x φ ) → [ y x ψ )
    s4 = lb.ref(
        "s4",
        "( ( [ y x ( φ → ψ ) ∧ [ y x φ ) → [ y x ψ )",
        s1,
        s2,
        s3,
        ref="sylanbrc",
        note="sylanbrc s1, s2, df-sb",
    )

    # ex: [ y x ( φ → ψ ) → ( [ y x φ → [ y x ψ )
    res = lb.ref(
        "res",
        "( [ y x ( φ → ψ ) → ( [ y x φ → [ y x ψ ) )",
        s4,
        ref="ex",
        note="ex",
    )

    return lb.build(res)


def prove_sbimi(sys: System) -> Proof:
    """sbimi: ( [ t / x ] φ → [ t / x ] ψ ).

    Inference form of proper substitution.  If φ implies ψ,
    then [ t / x ] φ implies [ t / x ] ψ.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wi wsb sbt sbi1 ax-mp.
    """
    lb = ProofBuilder(sys, "sbimi")
    hyp = lb.hyp("sbimi.1", "φ → ψ")
    # sbt: from hypothesis φ → ψ, derive [ t / x ] ( φ → ψ )
    s1 = lb.ref(
        "s1",
        "[ t x ( φ → ψ )",
        hyp,
        ref="sbt",
        note="sbt sbimi.1",
    )
    # sbi1: [ t / x ] ( φ → ψ ) → ( [ t / x ] φ → [ t / x ] ψ )
    s2 = lb.ref(
        "s2",
        "( [ t x ( φ → ψ ) → ( [ t x φ → [ t x ψ ) )",
        ref="sbi1",
        note="sbi1",
    )
    # ax-mp: ( [ t / x ] φ → [ t / x ] ψ )
    res = lb.mp("res", s1, s2, note="mp sbi1, sbt")
    return lb.build(res)


def prove_sbbii(sys: System) -> Proof:
    """sbbii: ( [ t / x ] φ ↔ [ t / x ] ψ ).

    Inference form of proper substitution.  If φ and ψ are logically
    equivalent, then substituting t for x in each yields equivalent
    results.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wsb biimpi sbimi biimpri impbii.
    """
    lb = ProofBuilder(sys, "sbbii")
    hyp = lb.hyp("sbbii.1", "φ ↔ ψ")
    # biimpi: from φ ↔ ψ, get φ → ψ
    s1 = lb.ref(
        "s1",
        "φ → ψ",
        hyp,
        ref="biimpi",
        note="biimpi sbbii.1",
    )
    # sbimi: from φ → ψ, get [ t / x ] φ → [ t / x ] ψ
    s2 = lb.ref(
        "s2",
        "( [ t x φ → [ t x ψ )",
        s1,
        ref="sbimi",
        note="sbimi",
    )
    # biimpri: from φ ↔ ψ, get ψ → φ
    s3 = lb.ref(
        "s3",
        "ψ → φ",
        hyp,
        ref="biimpri",
        note="biimpri sbbii.1",
    )
    # sbimi: from ψ → φ, get [ t / x ] ψ → [ t / x ] φ
    s4 = lb.ref(
        "s4",
        "( [ t x ψ → [ t x φ )",
        s3,
        ref="sbimi",
        note="sbimi",
    )
    # impbii: combine both directions into biconditional
    res = lb.ref(
        "res",
        "( [ t x φ ↔ [ t x ψ )",
        s2,
        s4,
        ref="impbii",
        note="impbii",
    )
    return lb.build(res)


def prove_sbrimvw(sys: System) -> Proof:
    """sbrimvw: [ y / x ] ( φ → ψ ) ↔ ( φ → [ y / x ] ψ ).

    Proper substitution distributes over implication from the right
    when the substituted variable is not free in the antecedent.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sbrimvw")

    # sbv: [ y / x ] φ ↔ φ
    s1 = lb.ref(
        "s1",
        "( [ y x φ ↔ φ )",
        ref="sbv",
        note="sbv",
    )

    # sbi1: [ y / x ] ( φ → ψ ) → ( [ y / x ] φ → [ y / x ] ψ )
    s2 = lb.ref(
        "s2",
        "( [ y x ( φ → ψ ) → ( [ y x φ → [ y x ψ ) )",
        ref="sbi1",
        note="sbi1",
    )

    # biimtrrid sbv, sbi1: [ y / x ] ( φ → ψ ) → ( φ → [ y / x ] ψ )
    s3 = lb.ref(
        "s3",
        "( [ y x ( φ → ψ ) → ( φ → [ y x ψ ) )",
        s1,
        s2,
        ref="biimtrrid",
        note="biimtrrid sbv, sbi1",
    )

    # pm2.21: ¬ φ → ( φ → ψ )
    s4 = lb.ref(
        "s4",
        "¬ φ → ( φ → ψ )",
        ref="pm2.21",
        note="pm2.21",
    )

    # sbimi from pm2.21: [ y / x ] ¬ φ → [ y / x ] ( φ → ψ )
    s5 = lb.ref(
        "s5",
        "( [ y x ¬ φ → [ y x ( φ → ψ ) )",
        s4,
        ref="sbimi",
        note="sbimi pm2.21",
    )

    # sbv with ¬ φ: [ y / x ] ¬ φ ↔ ¬ φ
    s6 = lb.ref(
        "s6",
        "( [ y x ¬ φ ↔ ¬ φ )",
        ref="sbv",
        note="sbv",
    )

    # sylbir sbv¬φ, sbimi(pm2.21): ¬ φ → [ y / x ] ( φ → ψ )
    s7 = lb.ref(
        "s7",
        "¬ φ → [ y x ( φ → ψ )",
        s6,
        s5,
        ref="sylbir",
        note="sylbir sbv, sbimi",
    )

    # ax-1: ψ → ( φ → ψ )
    s8 = lb.ref(
        "s8",
        "ψ → ( φ → ψ )",
        ref="ax-1",
        note="ax-1",
    )

    # sbimi from ax-1: [ y / x ] ψ → [ y / x ] ( φ → ψ )
    s9 = lb.ref(
        "s9",
        "( [ y x ψ → [ y x ( φ → ψ ) )",
        s8,
        ref="sbimi",
        note="sbimi ax-1",
    )

    # ja s7, s9: ( φ → [ y / x ] ψ ) → [ y / x ] ( φ → ψ )
    s10 = lb.ref(
        "s10",
        "( ( φ → [ y x ψ ) → [ y x ( φ → ψ ) )",
        s7,
        s9,
        ref="ja",
        note="ja",
    )

    # impbii s3, s10: [ y / x ] ( φ → ψ ) ↔ ( φ → [ y / x ] ψ )
    res = lb.ref(
        "res",
        "( [ y x ( φ → ψ ) ↔ ( φ → [ y x ψ ) )",
        s3,
        s10,
        ref="impbii",
        note="impbii",
    )

    return lb.build(res)


def prove_2sbbii(sys: System) -> Proof:
    """2sbbii: ( [ t / x ] [ u / y ] φ ↔ [ t / x ] [ u / y ] ψ ).

    Double substitution inference.  Apply sbbii twice.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wsb sbbii.
    """
    lb = ProofBuilder(sys, "2sbbii")
    hyp = lb.hyp("sbbii.1", "φ ↔ ψ")
    # sbbii: from φ ↔ ψ, get [ u / y ] φ ↔ [ u / y ] ψ
    s1 = lb.ref(
        "s1",
        "( [ u y φ ↔ [ u y ψ )",
        hyp,
        ref="sbbii",
        note="sbbii sbbii.1",
    )
    # sbbii: from [ u / y ] φ ↔ [ u / y ] ψ,
    # get [ t / x ] [ u / y ] φ ↔ [ t / x ] [ u / y ] ψ
    res = lb.ref(
        "res",
        "( [ t x [ u y φ ↔ [ t x [ u y ψ )",
        s1,
        ref="sbbii",
        note="sbbii",
    )
    return lb.build(res)


def prove_sbcom4(sys: System) -> Proof:
    """sbcom4: ( [ w / x ] [ y / z ] φ ↔ [ y / x ] [ w / z ] φ ).

    Commutation of distinct outer substitution variables.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wsb sbv sbbii bitri 3bitr4i.
    """
    lb = ProofBuilder(sys, "sbcom4")
    symbols = {
        info.local_name: symbol
        for symbol, info in sys.interner.symbol_table().items()
    }
    # Source active DVs: $d ph x $.  $d ph z $.
    lb.disjoint(symbols["ph"], symbols["x"])
    lb.disjoint(symbols["ph"], symbols["z"])

    # Follow the source proof: first prove each inner substitution equivalent
    # to φ, then lift that equivalence through the outer substitution.
    s1 = lb.ref(
        "s1",
        "( [ y z φ ↔ φ )",
        ref="sbv",
        note="sbv",
    )
    s2 = lb.ref(
        "s2",
        "( [ w x [ y z φ ↔ [ w x φ )",
        s1,
        ref="sbbii",
        note="sbbii sbv",
    )
    s3 = lb.ref(
        "s3",
        "( [ w x φ ↔ φ )",
        ref="sbv",
        note="sbv",
    )
    s4 = lb.ref(
        "s4",
        "( [ w x [ y z φ ↔ φ )",
        s2,
        s3,
        ref="bitri",
        note="bitri",
    )
    s5 = lb.ref(
        "s5",
        "( [ w z φ ↔ φ )",
        ref="sbv",
        note="sbv",
    )
    s6 = lb.ref(
        "s6",
        "( [ y x [ w z φ ↔ [ y x φ )",
        s5,
        ref="sbbii",
        note="sbbii sbv",
    )
    s7 = lb.ref(
        "s7",
        "( [ y x φ ↔ φ )",
        ref="sbv",
        note="sbv",
    )
    s8 = lb.ref(
        "s8",
        "( [ y x [ w z φ ↔ φ )",
        s6,
        s7,
        ref="bitri",
        note="bitri",
    )
    s9 = lb.ref(
        "s9",
        "( φ ↔ [ y x [ w z φ )",
        s8,
        ref="bicomi",
        note="bicomi",
    )
    res = lb.ref(
        "res",
        "( [ w x [ y z φ ↔ [ y x [ w z φ )",
        s4,
        s9,
        ref="bitri",
        note="bitri",
    )

    return lb.build(res)


def prove_sb2imi(sys: System) -> Proof:
    """sb2imi: [ t / x ] φ → ( [ t / x ] ψ → [ t / x ] χ ).

    Inference form of sb2im.  From φ → ( ψ → χ ) derive
    [ t / x ] φ → ( [ t / x ] ψ → [ t / x ] χ ).
    """
    lb = ProofBuilder(sys, "sb2imi")
    hyp = lb.hyp("sb2imi.1", "φ → ( ψ → χ )")
    # sbimi: from φ → ( ψ → χ ), derive [ t / x ] φ → [ t / x ] ( ψ → χ )
    s1 = lb.ref(
        "s1",
        "( [ t x φ → [ t x ( ψ → χ ) )",
        hyp,
        ref="sbimi",
        note="sbimi sb2imi.1",
    )
    # sbi1: [ t / x ] ( ψ → χ ) → ( [ t / x ] ψ → [ t / x ] χ )
    s2 = lb.ref(
        "s2",
        "( [ t x ( ψ → χ ) → ( [ t x ψ → [ t x χ ) )",
        ref="sbi1",
        note="sbi1",
    )
    # syl: combine s1 and s2
    res = lb.ref(
        "res",
        "( [ t x φ → ( [ t x ψ → [ t x χ ) )",
        s1,
        s2,
        ref="syl",
        note="syl sbimi, sbi1",
    )
    return lb.build(res)


def prove_alnex(sys: System) -> Proof:
    """alnex: ( ∀ x ¬ φ ↔ ¬ ∃ x φ ).

    Equivalence of universal negation with negated existence.
    From df-ex and con2bii. (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "alnex")

    # df-ex: ( ∃ x φ ↔ ¬ ∀ x ¬ φ )
    s1 = lb.ref(
        "s1",
        "∃ x φ ↔ ¬ ∀ x ¬ φ",
        ref="df-ex",
        note="df-ex",
    )

    # con2bii: from ( ∃ x φ ↔ ¬ ∀ x ¬ φ ), deduce ( ∀ x ¬ φ ↔ ¬ ∃ x φ )
    res = lb.ref(
        "res",
        "∀ x ¬ φ ↔ ¬ ∃ x φ",
        s1,
        ref="con2bii",
        note="con2bii df-ex",
    )

    return lb.build(res)


def prove_alex(sys: System) -> Proof:
    """alex: ∀ x φ ↔ ¬ ∃ x ¬ φ.

    Equivalence of universal quantification with negated existential
    of negation.  From notnotb, albii, alnex, and bitri.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "alex")

    # notnotb: φ ↔ ¬ ¬ φ
    s1 = lb.ref(
        "s1",
        "φ ↔ ¬ ¬ φ",
        ref="notnotb",
        note="notnotb",
    )

    # albii s1: ∀ x φ ↔ ∀ x ¬ ¬ φ
    s2 = lb.ref(
        "s2",
        "∀ x φ ↔ ∀ x ¬ ¬ φ",
        s1,
        ref="albii",
        note="albii notnotb",
    )

    # alnex with ph := ¬ φ: ∀ x ¬ ¬ φ ↔ ¬ ∃ x ¬ φ
    s3 = lb.ref(
        "s3",
        "∀ x ¬ ¬ φ ↔ ¬ ∃ x ¬ φ",
        ref="alnex",
        note="alnex with ¬ φ",
    )

    # bitri s2, s3: ∀ x φ ↔ ¬ ∃ x ¬ φ
    res = lb.ref(
        "res",
        "∀ x φ ↔ ¬ ∃ x ¬ φ",
        s2,
        s3,
        ref="bitri",
        note="bitri albii, alnex",
    )

    return lb.build(res)


def prove_alimex(sys: System) -> Proof:
    """alimex: ( φ → ∀ x ψ ) ↔ ( ∃ x ¬ ψ → ¬ φ ).

    Equivalence of an implication with universal quantification and
    implication with existential quantification of negation, by
    contraposition.  From alex, imbi2i, con2b, and bitri.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "alimex")

    # alex (with ψ): ∀ x ψ ↔ ¬ ∃ x ¬ ψ
    s1 = lb.ref(
        "s1",
        "∀ x ψ ↔ ¬ ∃ x ¬ ψ",
        ref="alex",
        note="alex",
    )

    # imbi2i s1: ( φ → ∀ x ψ ) ↔ ( φ → ¬ ∃ x ¬ ψ )
    s2 = lb.ref(
        "s2",
        "( φ → ∀ x ψ ) ↔ ( φ → ¬ ∃ x ¬ ψ )",
        s1,
        ref="imbi2i",
        note="imbi2i alex",
    )

    # con2b: ( φ → ¬ ∃ x ¬ ψ ) ↔ ( ∃ x ¬ ψ → ¬ φ )
    s3 = lb.ref(
        "s3",
        "( φ → ¬ ∃ x ¬ ψ ) ↔ ( ∃ x ¬ ψ → ¬ φ )",
        ref="con2b",
        note="con2b",
    )

    # bitri s2, s3: ( φ → ∀ x ψ ) ↔ ( ∃ x ¬ ψ → ¬ φ )
    res = lb.ref(
        "res",
        "( φ → ∀ x ψ ) ↔ ( ∃ x ¬ ψ → ¬ φ )",
        s2,
        s3,
        ref="bitri",
        note="bitri imbi2i, con2b",
    )

    return lb.build(res)


def prove_2nalexn(sys: System) -> Proof:
    """2nalexn: ¬ ∀ x ∀ y φ ↔ ∃ x ∃ y ¬ φ.

    Equivalence of doubly negated universal quantifier with doubly
    existential negated formula.  From df-ex, alex, albii, xchbinxr,
    and bicomi.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "2nalexn")

    # alex with y: ∀ y φ ↔ ¬ ∃ y ¬ φ
    s1 = lb.ref(
        "s1",
        "∀ y φ ↔ ¬ ∃ y ¬ φ",
        ref="alex",
        note="alex",
    )

    # albii on s1: ∀ x ∀ y φ ↔ ∀ x ¬ ∃ y ¬ φ
    s2 = lb.ref(
        "s2",
        "∀ x ∀ y φ ↔ ∀ x ¬ ∃ y ¬ φ",
        s1,
        ref="albii",
        note="albii alex",
    )

    # df-ex with x, φ := ∃ y ¬ φ:
    #   ∃ x ∃ y ¬ φ ↔ ¬ ∀ x ¬ ∃ y ¬ φ
    s3 = lb.ref(
        "s3",
        "∃ x ∃ y ¬ φ ↔ ¬ ∀ x ¬ ∃ y ¬ φ",
        ref="df-ex",
        note="df-ex",
    )

    # xchbinxr with s3 and s2:
    #   ∃ x ∃ y ¬ φ ↔ ¬ ∀ x ∀ y φ
    s4 = lb.ref(
        "s4",
        "∃ x ∃ y ¬ φ ↔ ¬ ∀ x ∀ y φ",
        s3,
        s2,
        ref="xchbinxr",
        note="xchbinxr df-ex, albii",
    )

    # bicomi: swap sides
    res = lb.ref(
        "res",
        "¬ ∀ x ∀ y φ ↔ ∃ x ∃ y ¬ φ",
        s4,
        ref="bicomi",
        note="bicomi",
    )

    return lb.build(res)


def prove_aleximi(sys: System) -> Proof:
    """aleximi: ∀ x φ → ( ∃ x ψ → ∃ x χ ).

    Inference combining con3d, al2imi, alnex, 3imtr3g, and con4d.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "aleximi")
    hyp = lb.hyp("aleximi.1", "φ → ( ψ → χ )")

    # con3d: ( φ → ( ψ → χ ) ) ⊢ ( φ → ( ¬ χ → ¬ ψ ) )
    s1 = lb.ref("s1", "φ → ( ¬ χ → ¬ ψ )", hyp, ref="con3d", note="con3d")

    # al2imi: ( φ → ( ¬ χ → ¬ ψ ) ) ⊢ ( ∀ x φ → ( ∀ x ¬ χ → ∀ x ¬ ψ ) )
    s2 = lb.ref(
        "s2",
        "∀ x φ → ( ∀ x ¬ χ → ∀ x ¬ ψ )",
        s1,
        ref="al2imi",
        note="al2imi",
    )

    # alnex with χ: ∀ x ¬ χ ↔ ¬ ∃ x χ
    s3 = lb.ref("s3", "∀ x ¬ χ ↔ ¬ ∃ x χ", ref="alnex", note="alnex")

    # alnex with ψ: ∀ x ¬ ψ ↔ ¬ ∃ x ψ
    s4 = lb.ref("s4", "∀ x ¬ ψ ↔ ¬ ∃ x ψ", ref="alnex", note="alnex")

    # 3imtr3g: chain the biconditionals
    s5 = lb.ref(
        "s5",
        "∀ x φ → ( ¬ ∃ x χ → ¬ ∃ x ψ )",
        s2,
        s3,
        s4,
        ref="3imtr3g",
        note="3imtr3g",
    )

    # con4d: ( φ → ( ¬ ψ → ¬ χ ) ) ⊢ ( φ → ( χ → ψ ) )
    res = lb.ref(
        "res",
        "∀ x φ → ( ∃ x ψ → ∃ x χ )",
        s5,
        ref="con4d",
        note="con4d",
    )
    return lb.build(res)


def prove_alexbii(sys: System) -> Proof:
    """alexbii: ∀ x φ → ( ∃ x ψ ↔ ∃ x χ ).

    From a biconditional φ → (ψ ↔ χ), deduce that
    universal quantification on φ implies the existential
    quantifiers are biconditional.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "alexbii")
    h1 = lb.hyp("alexbii.1", "φ → ( ψ ↔ χ )")

    # biimpd: φ → (ψ ↔ χ) ⊢ φ → (ψ → χ)
    s1 = lb.ref("s1", "φ → ( ψ → χ )", h1, ref="biimpd", note="biimpd")

    # aleximi: φ → (ψ → χ) ⊢ ∀ x φ → (∃ x ψ → ∃ x χ)
    s2 = lb.ref(
        "s2",
        "∀ x φ → ( ∃ x ψ → ∃ x χ )",
        s1,
        ref="aleximi",
        note="aleximi",
    )

    # biimprd: φ → (ψ ↔ χ) ⊢ φ → (χ → ψ)
    s3 = lb.ref("s3", "φ → ( χ → ψ )", h1, ref="biimprd", note="biimprd")

    # aleximi: φ → (χ → ψ) ⊢ ∀ x φ → (∃ x χ → ∃ x ψ)
    s4 = lb.ref(
        "s4",
        "∀ x φ → ( ∃ x χ → ∃ x ψ )",
        s3,
        ref="aleximi",
        note="aleximi",
    )

    # impbid: combine the two directions
    res = lb.ref(
        "res",
        "∀ x φ → ( ∃ x ψ ↔ ∃ x χ )",
        s2,
        s4,
        ref="impbid",
        note="impbid",
    )
    return lb.build(res)


def prove_exbi(sys: System) -> Proof:
    """exbi: ∀ x ( φ ↔ ψ ) → ( ∃ x φ ↔ ∃ x ψ ).

    From a biconditional to equivalence of existentials.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "exbi")
    # id: ( φ ↔ ψ ) → ( φ ↔ ψ )
    s1 = lb.ref("s1", "( φ ↔ ψ ) → ( φ ↔ ψ )", ref="id", note="id")
    # alexbii: with hypothesis s1, derive conclusion
    res = lb.ref(
        "res",
        "∀ x ( φ ↔ ψ ) → ( ∃ x φ ↔ ∃ x ψ )",
        s1,
        ref="alexbii",
        note="alexbii",
    )
    return lb.build(res)


def prove_exbii(sys: System) -> Proof:
    """exbii: ( ∃ x φ ↔ ∃ x ψ ).

    From a biconditional, derive equivalence of existentials.
    Inference form of exbi.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "exbii")
    h = lb.hyp("exbii.1", "( φ ↔ ψ )")
    s1 = lb.ref(
        "s1",
        "∀ x ( φ ↔ ψ ) → ( ∃ x φ ↔ ∃ x ψ )",
        ref="exbi",
        note="exbi",
    )
    res = lb.ref(
        "res",
        "( ∃ x φ ↔ ∃ x ψ )",
        s1,
        h,
        ref="mpg",
        note="mpg exbi, exbii.1",
    )
    return lb.build(res)


def prove_2exbii(sys: System) -> Proof:
    """2exbii: ( ∃ x ∃ y φ ↔ ∃ x ∃ y ψ ).

    Inference form of exbii, applied twice. From φ ↔ ψ, derive
    ∃ x ∃ y φ ↔ ∃ x ∃ y ψ by applying exbii over y and then over x.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wex exbii.
    """
    lb = ProofBuilder(sys, "2exbii")
    hyp = lb.hyp("2exbii.1", "( φ ↔ ψ )")
    # exbii over y: ∃ y φ ↔ ∃ y ψ
    s1 = lb.ref(
        "s1",
        "( ∃ y φ ↔ ∃ y ψ )",
        hyp,
        ref="exbii",
        note="exbii 2exbii.1",
    )
    # exbii over x: ∃ x ∃ y φ ↔ ∃ x ∃ y ψ
    res = lb.ref(
        "res",
        "( ∃ x ∃ y φ ↔ ∃ x ∃ y ψ )",
        s1,
        ref="exbii",
        note="exbii s1",
    )
    return lb.build(res)


def prove_3exbii(sys: System) -> Proof:
    """3exbii: ( ∃ x ∃ y ∃ z φ ↔ ∃ x ∃ y ∃ z ψ ).

    Inference form, applying 2exbii over y and z, then exbii over x.
    From φ ↔ ψ, derive ∃ x ∃ y ∃ z φ ↔ ∃ x ∃ y ∃ z ψ.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wex exbii 2exbii.
    """
    lb = ProofBuilder(sys, "3exbii")
    hyp = lb.hyp("3exbii.1", "( φ ↔ ψ )")
    # 2exbii over y and z: ∃ y ∃ z φ ↔ ∃ y ∃ z ψ
    s1 = lb.ref(
        "s1",
        "( ∃ y ∃ z φ ↔ ∃ y ∃ z ψ )",
        hyp,
        ref="2exbii",
        note="2exbii 3exbii.1",
    )
    # exbii over x: ∃ x ∃ y ∃ z φ ↔ ∃ x ∃ y ∃ z ψ
    res = lb.ref(
        "res",
        "( ∃ x ∃ y ∃ z φ ↔ ∃ x ∃ y ∃ z ψ )",
        s1,
        ref="exbii",
        note="exbii s1",
    )
    return lb.build(res)


def prove_exbidh(sys: System) -> Proof:
    """exbidh: φ → ( ∃ x ψ ↔ ∃ x χ ).

    Deduction form of exbi: if φ holds and x is not free in φ,
    then φ implies equivalence of the existentials.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "exbidh")
    hyp1 = lb.hyp("exbidh.1", "φ → ∀ x φ")
    hyp2 = lb.hyp("exbidh.2", "φ → ( ψ ↔ χ )")
    # alexbii: (φ → (ψ ↔ χ)) ⊢ (∀ x φ → (∃ x ψ ↔ ∃ x χ))
    s1 = lb.ref(
        "s1",
        "∀ x φ → ( ∃ x ψ ↔ ∃ x χ )",
        hyp2,
        ref="alexbii",
        note="alexbii exbidh.2",
    )
    # syl: (φ → ∀ x φ), (∀ x φ → (∃ x ψ ↔ ∃ x χ)) ⊢ (φ → (∃ x ψ ↔ ∃ x χ))
    res = lb.ref(
        "res",
        "φ → ( ∃ x ψ ↔ ∃ x χ )",
        hyp1,
        s1,
        ref="syl",
        note="syl exbidh.1, alexbii",
    )
    return lb.build(res)


def prove_exbidv(sys: System) -> Proof:
    """exbidv: ph → ( ∃ x ps ↔ ∃ x ch ).

    Deduction form of exbi using ax-5 for the distinct variable condition.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "exbidv")
    hyp = lb.hyp("albidv.1", "ph → ( ps ↔ ch )")
    # ax-5: ph → ∀ x ph
    s1 = lb.ref("s1", "ph → ∀ x ph", ref="ax-5", note="ax-5 — ax-5")
    # exbidh: (ph → ∀ x ph), (ph → (ps ↔ ch)) ⊢ (ph → (∃ x ps ↔ ∃ x ch))
    res = lb.ref(
        "res",
        "ph → ( ∃ x ps ↔ ∃ x ch )",
        s1,
        hyp,
        ref="exbidh",
        note="exbidh ax-5, albidv.1",
    )
    return lb.build(res)


def prove_19_29r(sys: System) -> Proof:
    """19.29r: ( ( ∃ x φ ∧ ∀ x ψ ) → ∃ x ( φ ∧ ψ ) ).

    If there exists an x with φ and for all x ψ, then
    there exists an x with both φ and ψ.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "19.29r")

    # pm3.21: φ → (ψ → (ψ ∧ φ))
    # With substitution φ:=ψ, ψ:=φ: ψ → (φ → (φ ∧ ψ))
    s1 = lb.ref(
        "s1",
        "ψ → ( φ → ( φ ∧ ψ ) )",
        ref="pm3.21",
        note="pm3.21",
    )

    # aleximi: from (ψ → (φ → (φ ∧ ψ))) get (∀ x ψ → (∃ x φ → ∃ x (φ ∧ ψ)))
    s2 = lb.ref(
        "s2",
        "∀ x ψ → ( ∃ x φ → ∃ x ( φ ∧ ψ ) )",
        s1,
        ref="aleximi",
        note="aleximi",
    )

    # impcom: from (∀ x ψ → (∃ x φ → ∃ x (φ ∧ ψ)))
    # get ((∃ x φ ∧ ∀ x ψ) → ∃ x (φ ∧ ψ))
    res = lb.ref(
        "res",
        "( ( ∃ x φ ∧ ∀ x ψ ) → ∃ x ( φ ∧ ψ ) )",
        s2,
        ref="impcom",
        note="impcom",
    )

    return lb.build(res)


def prove_19_29r2(sys: System) -> Proof:
    """19.29r2: ( ( ∃ x ∃ y φ ∧ ∀ x ∀ y ψ ) → ∃ x ∃ y ( φ ∧ ψ ) ).

    If there exists an x and a y with φ and for all x and y ψ,
    then there exists an x and a y with both φ and ψ.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "19.29r2")

    # 19.29r: ( ( ∃ x ∃ y φ ∧ ∀ x ∀ y ψ ) → ∃ x ( ∃ y φ ∧ ∀ y ψ ) )
    s1 = lb.ref(
        "s1",
        "( ( ∃ x ∃ y φ ∧ ∀ x ∀ y ψ ) → ∃ x ( ∃ y φ ∧ ∀ y ψ ) )",
        ref="19.29r",
        note="19.29r",
    )

    # 19.29r: ( ( ∃ y φ ∧ ∀ y ψ ) → ∃ y ( φ ∧ ψ ) )
    s2 = lb.ref(
        "s2",
        "( ( ∃ y φ ∧ ∀ y ψ ) → ∃ y ( φ ∧ ψ ) )",
        ref="19.29r",
        note="19.29r",
    )

    # eximi: from s2 get ∃ x ( ∃ y φ ∧ ∀ y ψ ) → ∃ x ∃ y ( φ ∧ ψ )
    s3 = lb.ref(
        "s3",
        "∃ x ( ∃ y φ ∧ ∀ y ψ ) → ∃ x ∃ y ( φ ∧ ψ )",
        s2,
        ref="eximi",
        note="eximi",
    )

    # syl: compose s1 and s3
    res = lb.ref(
        "res",
        "( ( ∃ x ∃ y φ ∧ ∀ x ∀ y ψ ) → ∃ x ∃ y ( φ ∧ ψ ) )",
        s1,
        s3,
        ref="syl",
        note="syl",
    )

    return lb.build(res)


def prove_19_29(sys: System) -> Proof:
    """19.29: ( ( ∀ x φ ∧ ∃ x ψ ) → ∃ x ( φ ∧ ψ ) ).

    If φ holds for all x and there exists an x such that ψ,
    then there exists an x such that both φ and ψ hold.
    """
    lb = ProofBuilder(sys, "19.29")
    # pm3.2: φ → ( ψ → ( φ ∧ ψ ) )
    s1 = lb.ref(
        "s1",
        "φ → ( ψ → ( φ ∧ ψ ) )",
        ref="pm3.2",
        note="pm3.2",
    )
    # aleximi: from φ → (ψ → (φ ∧ ψ)), deduce ∀ x φ → (∃ x ψ → ∃ x (φ ∧ ψ))
    s2 = lb.ref(
        "s2",
        "∀ x φ → ( ∃ x ψ → ∃ x ( φ ∧ ψ ) )",
        s1,
        ref="aleximi",
        note="aleximi",
    )
    # imp: convert nested implication to conjunction form
    res = lb.ref(
        "res",
        "( ( ∀ x φ ∧ ∃ x ψ ) → ∃ x ( φ ∧ ψ ) )",
        s2,
        ref="imp",
        note="imp",
    )
    return lb.build(res)


def prove_19_29x(sys: System) -> Proof:
    """19.29x: ( ( ∃ x ∀ y φ ∧ ∀ x ∃ y ψ ) → ∃ x ∃ y ( φ ∧ ψ ) ).

    Extended syllogism mixing universal and existential quantifiers.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "19.29x")

    # 19.29r with φ := ∀ y φ, ψ := ∃ y ψ:
    # ( ∃ x ∀ y φ ∧ ∀ x ∃ y ψ ) → ∃ x ( ∀ y φ ∧ ∃ y ψ )
    s1 = lb.ref(
        "s1",
        "( ∃ x ∀ y φ ∧ ∀ x ∃ y ψ ) → ∃ x ( ∀ y φ ∧ ∃ y ψ )",
        ref="19.29r",
        note="19.29r",
    )

    # 19.29 with x := y:
    # ( ∀ y φ ∧ ∃ y ψ ) → ∃ y ( φ ∧ ψ )
    s2 = lb.ref(
        "s2",
        "( ∀ y φ ∧ ∃ y ψ ) → ∃ y ( φ ∧ ψ )",
        ref="19.29",
        note="19.29",
    )

    # eximi: ∃ x ( ∀ y φ ∧ ∃ y ψ ) → ∃ x ∃ y ( φ ∧ ψ )
    s3 = lb.ref(
        "s3",
        "∃ x ( ∀ y φ ∧ ∃ y ψ ) → ∃ x ∃ y ( φ ∧ ψ )",
        s2,
        ref="eximi",
        note="eximi",
    )

    # syl: combine s1 and s3
    res = lb.ref(
        "res",
        "( ∃ x ∀ y φ ∧ ∀ x ∃ y ψ ) → ∃ x ∃ y ( φ ∧ ψ )",
        s1,
        s3,
        ref="syl",
        note="syl",
    )

    return lb.build(res)


def prove_exim(sys: System) -> Proof:
    """exim: ∀ x ( φ → ψ ) → ( ∃ x φ → ∃ x ψ ).

    Existential quantifier distributes over implication.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "exim")
    # id: ( φ → ψ ) → ( φ → ψ )
    s1 = lb.ref("s1", "( φ → ψ ) → ( φ → ψ )", ref="id", note="id")
    # aleximi with φ := (φ → ψ), ψ := φ, χ := ψ
    res = lb.ref(
        "res",
        "∀ x ( φ → ψ ) → ( ∃ x φ → ∃ x ψ )",
        s1,
        ref="aleximi",
        note="aleximi id",
    )
    return lb.build(res)


def prove_eximdh(sys: System) -> Proof:
    """eximdh: φ → ( ∃ x ψ → ∃ x χ ).

    Deduction form of exim. Uses aleximi to distribute the quantifier
    over the nested implication in the second hypothesis, then chains
    with the first hypothesis via syl.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "eximdh")
    hyp1 = lb.hyp("eximdh.1", "φ → ∀ x φ")
    hyp2 = lb.hyp("eximdh.2", "φ → ( ψ → χ )")
    # aleximi: (φ → (ψ → χ)) ⊢ (∀ x φ → (∃ x ψ → ∃ x χ))
    s1 = lb.ref(
        "s1",
        "∀ x φ → ( ∃ x ψ → ∃ x χ )",
        hyp2,
        ref="aleximi",
        note="aleximi eximdh.2",
    )
    # syl: (φ → ∀ x φ), (∀ x φ → (∃ x ψ → ∃ x χ)) ⊢ (φ → (∃ x ψ → ∃ x χ))
    res = lb.ref(
        "res",
        "φ → ( ∃ x ψ → ∃ x χ )",
        hyp1,
        s1,
        ref="syl",
        note="syl eximdh.1, aleximi",
    )
    return lb.build(res)


def prove_eximdv(sys: System) -> Proof:
    """eximdv: φ → ( ∃ x ψ → ∃ x χ ).

    Deduction form of eximdh. Uses ax-5 to satisfy the distinct variable
    condition, then applies eximdh with the hypothesis.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: ax-5 eximdh.
    """
    lb = ProofBuilder(sys, "eximdv")
    hyp = lb.hyp("eximdv.1", "φ → ( ψ → χ )")
    # ax-5: φ → ∀ x φ
    s1 = lb.ref("s1", "φ → ∀ x φ", ref="ax-5", note="ax-5 — ax-5")
    # eximdh: (φ → ∀ x φ), (φ → (ψ → χ)) ⊢ (φ → (∃ x ψ → ∃ x χ))
    res = lb.ref(
        "res",
        "φ → ( ∃ x ψ → ∃ x χ )",
        s1,
        hyp,
        ref="eximdh",
        note="eximdh ax-5, eximdv.1",
    )
    return lb.build(res)


def prove_eximi(sys: System) -> Proof:
    """eximi: ∃ x φ → ∃ x ψ.

    Inference form of exim. Generalize the hypothesis with ax-5,
    then apply exim for quantifier distribution.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wi wex exim mpg.
    """
    lb = ProofBuilder(sys, "eximi")
    hyp = lb.hyp("eximi.1", "φ → ψ")
    major = lb.ref(
        "major",
        "∀ x ( φ → ψ ) → ( ∃ x φ → ∃ x ψ )",
        ref="exim",
        note="exim",
    )
    res = lb.ref("res", "∃ x φ → ∃ x ψ", major, hyp, ref="mpg", note="mpg exim, eximi.1")
    return lb.build(res)


def prove_eximii(sys: System) -> Proof:
    """eximii: ∃ x ψ.

    Inference form of eximi. From ∃ x φ and φ → ψ, derive ∃ x ψ.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "eximii")
    hyp1 = lb.hyp("eximii.1", "∃ x φ")
    hyp2 = lb.hyp("eximii.2", "φ → ψ")
    s1 = lb.ref("s1", "∃ x φ → ∃ x ψ", hyp2, ref="eximi", note="eximi eximii.2")
    res = lb.mp("res", hyp1, s1, note="mp eximii.1, s1")
    return lb.build(res)


def prove_2eximi(sys: System) -> Proof:
    """2eximi: ∃ x ∃ y φ → ∃ x ∃ y ψ.

    Inference form of eximi, applied twice. From φ → ψ, derive
    ∃ x ∃ y φ → ∃ x ∃ y ψ by applying eximi over y and then over x.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wex eximi.
    """
    lb = ProofBuilder(sys, "2eximi")
    hyp = lb.hyp("eximi.1", "φ → ψ")
    # eximi over y: ∃ y φ → ∃ y ψ
    s1 = lb.ref("s1", "∃ y φ → ∃ y ψ", hyp, ref="eximi", note="eximi eximi.1")
    # eximi over x: ∃ x ∃ y φ → ∃ x ∃ y ψ
    res = lb.ref("res", "∃ x ∃ y φ → ∃ x ∃ y ψ", s1, ref="eximi", note="eximi s1")
    return lb.build(res)


def prove_2eximdv(sys: System) -> Proof:
    """2eximdv: φ → ( ∃ x ∃ y ψ → ∃ x ∃ y χ ).

    Deduction form of 2eximi. Apply eximdv twice: first with y, then
    with x, using the hypothesis 2eximdv.1.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wex eximdv.
    """
    lb = ProofBuilder(sys, "2eximdv")
    hyp = lb.hyp("2eximdv.1", "φ → ( ψ → χ )")
    # eximdv with y: φ → ( ∃ y ψ → ∃ y χ )
    s1 = lb.ref(
        "s1",
        "φ → ( ∃ y ψ → ∃ y χ )",
        hyp,
        ref="eximdv",
        note="eximdv with y",
    )
    # eximdv with x: φ → ( ∃ x ∃ y ψ → ∃ x ∃ y χ )
    res = lb.ref(
        "res",
        "φ → ( ∃ x ∃ y ψ → ∃ x ∃ y χ )",
        s1,
        ref="eximdv",
        note="eximdv with x",
    )
    return lb.build(res)


def prove_2exbidv(sys: System) -> Proof:
    """2exbidv: φ → ( ∃ x ∃ y ψ ↔ ∃ x ∃ y χ ).

    Deduction form of 2exbii, applying exbidv twice: first with y,
    then with x, using the hypothesis 2albidv.1.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wex exbidv.
    """
    lb = ProofBuilder(sys, "2exbidv")
    hyp = lb.hyp("2albidv.1", "φ → ( ψ ↔ χ )")
    # exbidv with y: φ → ( ∃ y ψ ↔ ∃ y χ )
    s1 = lb.ref(
        "s1",
        "φ → ( ∃ y ψ ↔ ∃ y χ )",
        hyp,
        ref="exbidv",
        note="exbidv with y",
    )
    # exbidv with x: φ → ( ∃ x ∃ y ψ ↔ ∃ x ∃ y χ )
    res = lb.ref(
        "res",
        "φ → ( ∃ x ∃ y ψ ↔ ∃ x ∃ y χ )",
        s1,
        ref="exbidv",
        note="exbidv with x",
    )
    return lb.build(res)


def prove_3exbidv(sys: System) -> Proof:
    """3exbidv: φ → ( ∃ x ∃ y ∃ z ψ ↔ ∃ x ∃ y ∃ z χ ).

    Deduction form of 3exbii, applying exbidv then 2exbidv.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wex exbidv 2exbidv.
    """
    lb = ProofBuilder(sys, "3exbidv")
    hyp = lb.hyp("3exbidv.1", "φ → ( ψ ↔ χ )")
    # exbidv with z: φ → ( ∃ z ψ ↔ ∃ z χ )
    s1 = lb.ref(
        "s1",
        "φ → ( ∃ z ψ ↔ ∃ z χ )",
        hyp,
        ref="exbidv",
        note="exbidv with z",
    )
    # 2exbidv with x,y: φ → ( ∃ x ∃ y ∃ z ψ ↔ ∃ x ∃ y ∃ z χ )
    res = lb.ref(
        "res",
        "φ → ( ∃ x ∃ y ∃ z ψ ↔ ∃ x ∃ y ∃ z χ )",
        s1,
        ref="2exbidv",
        note="2exbidv with x,y",
    )
    return lb.build(res)


def prove_4exbidv(sys: System) -> Proof:
    """4exbidv: φ → ( ∃ x ∃ y ∃ z ∃ w ψ ↔ ∃ x ∃ y ∃ z ∃ w χ ).

    Deduction form of 4exbii, applying 2exbidv twice:
    first with z,w, then with x,y, using the hypothesis 4exbidv.1.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wex 2exbidv.
    """
    lb = ProofBuilder(sys, "4exbidv")
    hyp = lb.hyp("4exbidv.1", "φ → ( ψ ↔ χ )")
    # 2exbidv with z,w: φ → ( ∃ z ∃ w ψ ↔ ∃ z ∃ w χ )
    s1 = lb.ref(
        "s1",
        "φ → ( ∃ z ∃ w ψ ↔ ∃ z ∃ w χ )",
        hyp,
        ref="2exbidv",
        note="2exbidv with z, w",
    )
    # 2exbidv with x,y: φ → ( ∃ x ∃ y ∃ z ∃ w ψ ↔ ∃ x ∃ y ∃ z ∃ w χ )
    res = lb.ref(
        "res",
        "φ → ( ∃ x ∃ y ∃ z ∃ w ψ ↔ ∃ x ∃ y ∃ z ∃ w χ )",
        s1,
        ref="2exbidv",
        note="2exbidv with x, y",
    )
    return lb.build(res)


def prove_exintr(sys: System) -> Proof:
    """exintr: ∀ x ( φ → ψ ) → ( ∃ x φ → ∃ x ( φ ∧ ψ ) ).

    Existential quantifier distributes over conjunction with the antecedent.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "exintr")
    # ancl: ( φ → ψ ) → ( φ → ( φ ∧ ψ ) )
    s1 = lb.ref(
        "s1",
        "( φ → ψ ) → ( φ → ( φ ∧ ψ ) )",
        ref="ancl",
        note="ancl",
    )
    # aleximi with hypothesis (φ → ψ) → (φ → (φ ∧ ψ)):
    # conclusion: ∀ x ( φ → ψ ) → ( ∃ x φ → ∃ x ( φ ∧ ψ ) )
    res = lb.ref(
        "res",
        "∀ x ( φ → ψ ) → ( ∃ x φ → ∃ x ( φ ∧ ψ ) )",
        s1,
        ref="aleximi",
        note="aleximi",
    )
    return lb.build(res)


def prove_exintrbi(sys: System) -> Proof:
    """exintrbi: ∀ x ( φ → ψ ) → ( ∃ x φ ↔ ∃ x ( φ ∧ ψ ) ).

    Existential quantifier distributes as a biconditional when the
    antecedent implies the universal quantification of the implication.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "exintrbi")

    # abai: ( φ ∧ ψ ) ↔ ( φ ∧ ( φ → ψ ) )
    s1 = lb.ref(
        "s1",
        "( φ ∧ ψ ) ↔ ( φ ∧ ( φ → ψ ) )",
        ref="abai",
        note="abai",
    )

    # rbaibr with hypothesis ( φ ∧ ψ ) ↔ ( φ ∧ ( φ → ψ ) ):
    # conclusion: ( φ → ψ ) → ( φ ↔ ( φ ∧ ψ ) )
    s2 = lb.ref(
        "s2",
        "( φ → ψ ) → ( φ ↔ ( φ ∧ ψ ) )",
        s1,
        ref="rbaibr",
        note="rbaibr",
    )

    # alexbii with hypothesis ( φ → ψ ) → ( φ ↔ ( φ ∧ ψ ) ):
    # conclusion: ∀ x ( φ → ψ ) → ( ∃ x φ ↔ ∃ x ( φ ∧ ψ ) )
    res = lb.ref(
        "res",
        "∀ x ( φ → ψ ) → ( ∃ x φ ↔ ∃ x ( φ ∧ ψ ) )",
        s2,
        ref="alexbii",
        note="alexbii",
    )

    return lb.build(res)


def prove_exsimpl(sys: System) -> Proof:
    """exsimpl: ∃ x ( φ ∧ ψ ) → ∃ x φ.

    Existential quantifier distributes over conjunction simplification.
    From ( φ ∧ ψ ) → φ, derive ∃ x ( φ ∧ ψ ) → ∃ x φ.
    (Contributed by NM, 10-Aug-1993.)
    set.mm proof: wa simpl eximi.
    """
    lb = ProofBuilder(sys, "exsimpl")
    # simpl: ( φ ∧ ψ ) → φ
    s1 = lb.ref(
        "s1",
        "( φ ∧ ψ ) → φ",
        ref="simpl",
        note="simpl",
    )
    # eximi with simpl: ∃ x ( φ ∧ ψ ) → ∃ x φ
    res = lb.ref(
        "res",
        "∃ x ( φ ∧ ψ ) → ∃ x φ",
        s1,
        ref="eximi",
        note="eximi",
    )
    return lb.build(res)


def prove_exsimpr(sys: System) -> Proof:
    """exsimpr: ∃ x ( φ ∧ ψ ) → ∃ x ψ.

    Existential quantifier distributes over conjunction simplification (right).
    From ( φ ∧ ψ ) → ψ, derive ∃ x ( φ ∧ ψ ) → ∃ x ψ.
    (Contributed by NM, 10-Aug-1993.)
    set.mm proof: wa simpr eximi.
    """
    lb = ProofBuilder(sys, "exsimpr")
    # simpr: ( φ ∧ ψ ) → ψ
    s1 = lb.ref(
        "s1",
        "( φ ∧ ψ ) → ψ",
        ref="simpr",
        note="simpr",
    )
    # eximi with simpr: ∃ x ( φ ∧ ψ ) → ∃ x ψ
    res = lb.ref(
        "res",
        "∃ x ( φ ∧ ψ ) → ∃ x ψ",
        s1,
        ref="eximi",
        note="eximi",
    )
    return lb.build(res)


def prove_exlimiv(sys: System) -> Proof:
    """exlimiv: ∃ x φ → ψ.

    Inference form of the existential quantifier. From φ → ψ,
    deduce that if there exists an x such that φ, then ψ.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wex eximi ax5e syl.
    """
    lb = ProofBuilder(sys, "exlimiv")
    hyp = lb.hyp("exlimiv.1", "φ → ψ")
    # eximi: φ → ψ ⊢ ∃ x φ → ∃ x ψ
    s1 = lb.ref(
        "s1",
        "∃ x φ → ∃ x ψ",
        hyp,
        ref="eximi",
        note="eximi exlimiv.1",
    )
    # ax5e: ∃ x ψ → ψ
    s2 = lb.ref(
        "s2",
        "∃ x ψ → ψ",
        ref="ax5e",
        note="ax5e",
    )
    # syl: chain s1 and s2
    res = lb.ref(
        "res",
        "∃ x φ → ψ",
        s1,
        s2,
        ref="syl",
        note="syl eximi, ax5e",
    )
    return lb.build(res)


def prove_exlimiiv(sys: System) -> Proof:
    """exlimiiv: ψ.

    Inference of an inference. From φ → ψ and ∃ x φ, deduce ψ.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wex exlimiv ax-mp.
    """
    lb = ProofBuilder(sys, "exlimiiv")
    hyp1 = lb.hyp("exlimiiv.1", "φ → ψ")
    hyp2 = lb.hyp("exlimiiv.2", "∃ x φ")
    # exlimiv: ( φ → ψ ) ⊢ ( ∃ x φ → ψ )
    s1 = lb.ref(
        "s1",
        "∃ x φ → ψ",
        hyp1,
        ref="exlimiv",
        note="exlimiv exlimiiv.1",
    )
    # ax-mp: ( ∃ x φ → ψ ), ∃ x φ ⊢ ψ
    res = lb.mp("res", hyp2, s1, "MP s1, exlimiiv.2")
    return lb.build(res)


def prove_exlimivv(sys: System) -> Proof:
    """exlimivv: ∃ x ∃ y φ → ψ.

    Double existential instantiation. From φ → ψ,
    deduce that if there exist x and y such that φ, then ψ.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wex exlimiv.
    """
    lb = ProofBuilder(sys, "exlimivv")
    hyp = lb.hyp("exlimivv.1", "φ → ψ")
    # exlimiv: ( φ → ψ ) ⊢ ( ∃ y φ → ψ )
    s1 = lb.ref(
        "s1",
        "∃ y φ → ψ",
        hyp,
        ref="exlimiv",
        note="exlimiv exlimivv.1",
    )
    # exlimiv: ( ∃ y φ → ψ ) ⊢ ( ∃ x ∃ y φ → ψ )
    res = lb.ref(
        "res",
        "∃ x ∃ y φ → ψ",
        s1,
        ref="exlimiv",
        note="exlimiv s1",
    )
    return lb.build(res)


def prove_exlimdv(sys: System) -> Proof:
    """exlimdv: φ → ( ∃ x ψ → χ ).

    Deduction form of exlimiv. From φ → (ψ → χ),
    deduce φ → (∃ x ψ → χ).
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wex eximdv ax5e syl6.
    """
    lb = ProofBuilder(sys, "exlimdv")
    hyp = lb.hyp("exlimdv.1", "φ → ( ψ → χ )")
    # eximdv: φ → (ψ → χ) ⊢ φ → (∃ x ψ → ∃ x χ)
    s1 = lb.ref(
        "s1",
        "φ → ( ∃ x ψ → ∃ x χ )",
        hyp,
        ref="eximdv",
        note="eximdv exlimdv.1",
    )
    # ax5e: ∃ x χ → χ
    s2 = lb.ref(
        "s2",
        "∃ x χ → χ",
        ref="ax5e",
        note="ax5e",
    )
    # syl6: chain s1 and s2
    res = lb.ref(
        "res",
        "φ → ( ∃ x ψ → χ )",
        s1,
        s2,
        ref="syl6",
        note="syl6 eximdv, ax5e",
    )
    return lb.build(res)


def prove_exlimddv(sys: System) -> Proof:
    """exlimddv: φ → χ.

    Deduction form of exlimdv.  From φ → ∃ x ψ and (φ ∧ ψ) → χ,
    deduce φ → χ.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: ex exlimdv mpd.
    """
    lb = ProofBuilder(sys, "exlimddv")
    h1 = lb.hyp("exlimddv.1", "φ → ∃ x ψ")
    h2 = lb.hyp("exlimddv.2", "( φ ∧ ψ ) → χ")
    # ex: export from exlimddv.2: φ → (ψ → χ)
    s1 = lb.ref(
        "s1",
        "φ → ( ψ → χ )",
        h2,
        ref="ex",
        note="ex exlimddv.2",
    )
    # exlimdv: from s1: φ → (∃ x ψ → χ)
    s2 = lb.ref(
        "s2",
        "φ → ( ∃ x ψ → χ )",
        s1,
        ref="exlimdv",
        note="exlimdv s1",
    )
    # mpd: using exlimddv.1 and s2: φ → χ
    res = lb.ref(
        "res",
        "φ → χ",
        h1,
        s2,
        ref="mpd",
        note="mpd exlimddv.1, s2",
    )
    return lb.build(res)


def prove_exlimdvv(sys: System) -> Proof:
    """exlimdvv: φ → ( ∃ x ∃ y ψ → χ ).

    Deduction form of exlimiv with two nested existential quantifiers.
    Apply exlimdv twice: first with y, then with x.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wex exlimdv.
    """
    lb = ProofBuilder(sys, "exlimdvv")
    hyp = lb.hyp("exlimdvv.1", "φ → ( ψ → χ )")
    # exlimdv with y: φ → (∃ y ψ → χ)
    s1 = lb.ref(
        "s1",
        "φ → ( ∃ y ψ → χ )",
        hyp,
        ref="exlimdv",
        note="exlimdv with y",
    )
    # exlimdv with x: φ → (∃ x ∃ y ψ → χ)
    res = lb.ref(
        "res",
        "φ → ( ∃ x ∃ y ψ → χ )",
        s1,
        ref="exlimdv",
        note="exlimdv with x",
    )
    return lb.build(res)


def prove_nex(sys: System) -> Proof:
    """nex: ¬ ∃ x φ.

    If φ is false, there does not exist an x such that φ.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wn wex alnex mpgbi.
    """
    lb = ProofBuilder(sys, "nex")
    hyp = lb.hyp("nex.1", "¬ φ")
    # alnex: ∀ x ¬ φ ↔ ¬ ∃ x φ
    s3 = lb.ref(
        "s3",
        "∀ x ¬ φ ↔ ¬ ∃ x φ",
        ref="alnex",
        note="alnex",
    )
    res = lb.ref(
        "res",
        "¬ ∃ x φ",
        s3,
        hyp,
        ref="mpgbi",
        note="mpgbi alnex, nex.1",
    )
    return lb.build(res)


def prove_nexdh(sys: System) -> Proof:
    """nexdh: φ → ¬ ∃ x ψ.

    Deduction form of nex. The first hypothesis provides the
    distinct variable condition; the second hypothesis provides
    the negated consequent.  alrimih generalizes the negation,
    alnex converts the universal to negated existential, and
    sylib chains them.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wn wal wex alrimih alnex sylib.
    """
    lb = ProofBuilder(sys, "nexdh")
    hyp1 = lb.hyp("nexdh.1", "φ → ∀ x φ")
    hyp2 = lb.hyp("nexdh.2", "φ → ¬ ψ")
    # alrimih: (φ → ∀ x φ), (φ → ¬ ψ) ⊢ φ → ∀ x ¬ ψ
    s1 = lb.ref(
        "s1",
        "φ → ∀ x ¬ ψ",
        hyp1,
        hyp2,
        ref="alrimih",
        note="alrimih nexdh.1, nexdh.2",
    )
    # alnex: ∀ x ¬ ψ ↔ ¬ ∃ x ψ
    s2 = lb.ref(
        "s2",
        "∀ x ¬ ψ ↔ ¬ ∃ x ψ",
        ref="alnex",
        note="alnex",
    )
    # sylib: (φ → ∀ x ¬ ψ), (∀ x ¬ ψ ↔ ¬ ∃ x ψ) ⊢ φ → ¬ ∃ x ψ
    res = lb.ref(
        "res",
        "φ → ¬ ∃ x ψ",
        s1,
        s2,
        ref="sylib",
        note="sylib alrimih, alnex",
    )
    return lb.build(res)


def prove_nexdv(sys: System) -> Proof:
    """nexdv: φ → ¬ ∃ x ψ.

    Deduction form of nex. The hypothesis provides φ → ¬ ψ; ax-5 provides
    the distinct variable condition φ → ∀ x φ; nexdh combines them.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: ax-5 nexdh.
    """
    lb = ProofBuilder(sys, "nexdv")
    hyp = lb.hyp("nexdv.1", "φ → ¬ ψ")
    # ax-5: φ → ∀ x φ (valid because x is not free in φ)
    s1 = lb.ref("s1", "φ → ∀ x φ", ref="ax-5", note="ax-5")
    # nexdh: (φ → ∀ x φ), (φ → ¬ ψ) ⊢ φ → ¬ ∃ x ψ
    res = lb.ref(
        "res",
        "φ → ¬ ∃ x ψ",
        s1,
        hyp,
        ref="nexdh",
        note="nexdh ax-5, nexdv.1",
    )
    return lb.build(res)


def prove_exancom(sys: System) -> Proof:
    """exancom: ( ∃ x ( φ ∧ ψ ) ↔ ∃ x ( ψ ∧ φ ) ).

    Commutative law for conjunction — existential form.  An existentially
    quantified conjunction commutes, derived from ancom and exbii.
    (Contributed by NM, 3-Jan-1993.)
    """
    lb = ProofBuilder(sys, "exancom")
    s1 = lb.ref("s1", "( φ ∧ ψ ) ↔ ( ψ ∧ φ )", ref="ancom", note="ancom")
    res = lb.ref(
        "res",
        "( ∃ x ( φ ∧ ψ ) ↔ ∃ x ( ψ ∧ φ ) )",
        s1,
        ref="exbii",
        note="exbii",
    )
    return lb.build(res)


def prove_exnal(sys: System) -> Proof:
    """exnal: ∃ x ¬ φ ↔ ¬ ∀ x φ.

    Equivalence of existential negation with negated universal.
    From alex and con2bii.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "exnal")

    # alex: ∀ x φ ↔ ¬ ∃ x ¬ φ
    s1 = lb.ref(
        "s1",
        "∀ x φ ↔ ¬ ∃ x ¬ φ",
        ref="alex",
        note="alex",
    )

    # con2bii: from (∀ x φ ↔ ¬ ∃ x ¬ φ), deduce (∃ x ¬ φ ↔ ¬ ∀ x φ)
    res = lb.ref(
        "res",
        "∃ x ¬ φ ↔ ¬ ∀ x φ",
        s1,
        ref="con2bii",
        note="con2bii alex",
    )

    return lb.build(res)


def prove_alinexa(sys: System) -> Proof:
    """alinexa: ( ∀ x ( φ → ¬ ψ ) ↔ ¬ ∃ x ( φ ∧ ψ ) ).

    Equivalence between a universalized negated implication and the
    negation of an existential conjunction.  From imnang and alnex
    via bitri.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wn wi wal wa wex imnang alnex bitri.
    """
    lb = ProofBuilder(sys, "alinexa")

    # imnang: ∀ x ( φ → ¬ ψ ) ↔ ∀ x ¬ ( φ ∧ ψ )
    s1 = lb.ref(
        "s1",
        "∀ x ( φ → ¬ ψ ) ↔ ∀ x ¬ ( φ ∧ ψ )",
        ref="imnang",
        note="imnang",
    )

    # alnex: ∀ x ¬ ( φ ∧ ψ ) ↔ ¬ ∃ x ( φ ∧ ψ )
    s2 = lb.ref(
        "s2",
        "∀ x ¬ ( φ ∧ ψ ) ↔ ¬ ∃ x ( φ ∧ ψ )",
        ref="alnex",
        note="alnex",
    )

    # bitri: chain s1 and s2
    res = lb.ref(
        "res",
        "∀ x ( φ → ¬ ψ ) ↔ ¬ ∃ x ( φ ∧ ψ )",
        s1,
        s2,
        ref="bitri",
        note="bitri imnang, alnex",
    )

    return lb.build(res)


def prove_exnalimn(sys: System) -> Proof:
    """exnalimn: ∃ x ( φ ∧ ψ ) ↔ ¬ ∀ x ( φ → ¬ ψ ).

    Equivalence of existential conjunction with negated universalized
    negated implication.  From alinexa and con2bii.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wn wi wal wa wex alinexa con2bii.
    """
    lb = ProofBuilder(sys, "exnalimn")

    # alinexa: ∀ x ( φ → ¬ ψ ) ↔ ¬ ∃ x ( φ ∧ ψ )
    s1 = lb.ref(
        "s1",
        "∀ x ( φ → ¬ ψ ) ↔ ¬ ∃ x ( φ ∧ ψ )",
        ref="alinexa",
        note="alinexa",
    )

    # con2bii: from ( ∀ x ( φ → ¬ ψ ) ↔ ¬ ∃ x ( φ ∧ ψ ) ),
    #          deduce ( ∃ x ( φ ∧ ψ ) ↔ ¬ ∀ x ( φ → ¬ ψ ) )
    res = lb.ref(
        "res",
        "∃ x ( φ ∧ ψ ) ↔ ¬ ∀ x ( φ → ¬ ψ )",
        s1,
        ref="con2bii",
        note="con2bii alinexa",
    )

    return lb.build(res)


def prove_alexn(sys: System) -> Proof:
    """alexn: ∀ x ∃ y ¬ φ ↔ ¬ ∃ x ∀ y φ.

    Equivalence of universal-existential negation with negated
    existential-universal.  From exnal, albii, alnex, and bitri.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "alexn")

    # exnal with y: ∃ y ¬ φ ↔ ¬ ∀ y φ
    s1 = lb.ref(
        "s1",
        "∃ y ¬ φ ↔ ¬ ∀ y φ",
        ref="exnal",
        note="exnal",
    )

    # albii s1 with x: ∀ x ∃ y ¬ φ ↔ ∀ x ¬ ∀ y φ
    s2 = lb.ref(
        "s2",
        "∀ x ∃ y ¬ φ ↔ ∀ x ¬ ∀ y φ",
        s1,
        ref="albii",
        note="albii exnal",
    )

    # alnex with ∀ y φ: ∀ x ¬ ∀ y φ ↔ ¬ ∃ x ∀ y φ
    s3 = lb.ref(
        "s3",
        "∀ x ¬ ∀ y φ ↔ ¬ ∃ x ∀ y φ",
        ref="alnex",
        note="alnex",
    )

    # bitri s2, s3: ∀ x ∃ y ¬ φ ↔ ¬ ∃ x ∀ y φ
    res = lb.ref(
        "res",
        "∀ x ∃ y ¬ φ ↔ ¬ ∃ x ∀ y φ",
        s2,
        s3,
        ref="bitri",
        note="bitri albii, alnex",
    )

    return lb.build(res)


def prove_exanali(sys: System) -> Proof:
    """exanali: ∃ x ( φ ∧ ¬ ψ ) ↔ ¬ ∀ x ( φ → ψ ).

    Equivalence of existential conjunction with negated universal implication.
    From annim, exbii, exnal, and bitri.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "exanali")
    # annim: ( φ ∧ ¬ ψ ) ↔ ¬ ( φ → ψ )
    s1 = lb.ref(
        "s1",
        "( φ ∧ ¬ ψ ) ↔ ¬ ( φ → ψ )",
        ref="annim",
        note="annim",
    )
    # exbii with annim: ∃ x ( φ ∧ ¬ ψ ) ↔ ∃ x ¬ ( φ → ψ )
    s2 = lb.ref(
        "s2",
        "∃ x ( φ ∧ ¬ ψ ) ↔ ∃ x ¬ ( φ → ψ )",
        s1,
        ref="exbii",
        note="exbii annim",
    )
    # exnal with φ := ( φ → ψ ): ∃ x ¬ ( φ → ψ ) ↔ ¬ ∀ x ( φ → ψ )
    s3 = lb.ref(
        "s3",
        "∃ x ¬ ( φ → ψ ) ↔ ¬ ∀ x ( φ → ψ )",
        ref="exnal",
        note="exnal",
    )
    # bitri: chain s2 and s3
    res = lb.ref(
        "res",
        "∃ x ( φ ∧ ¬ ψ ) ↔ ¬ ∀ x ( φ → ψ )",
        s2,
        s3,
        ref="bitri",
        note="bitri exbii, exnal",
    )
    return lb.build(res)


def prove_19_40(sys: System) -> Proof:
    """19.40: ∃ x ( φ ∧ ψ ) → ( ∃ x φ ∧ ∃ x ψ ).

    Existential quantifier distributes over conjunction.
    (Contributed by NM, 10-Aug-1993.)
    set.mm proof: wa wex exsimpl exsimpr jca.
    """
    lb = ProofBuilder(sys, "19.40")
    # exsimpl: ∃ x ( φ ∧ ψ ) → ∃ x φ
    s1 = lb.ref(
        "s1",
        "∃ x ( φ ∧ ψ ) → ∃ x φ",
        ref="exsimpl",
        note="exsimpl",
    )
    # exsimpr: ∃ x ( φ ∧ ψ ) → ∃ x ψ
    s2 = lb.ref(
        "s2",
        "∃ x ( φ ∧ ψ ) → ∃ x ψ",
        ref="exsimpr",
        note="exsimpr",
    )
    # jca: from both directions, join with conjunction
    res = lb.ref(
        "res",
        "∃ x ( φ ∧ ψ ) → ( ∃ x φ ∧ ∃ x ψ )",
        s1,
        s2,
        ref="jca",
        note="jca exsimpl, exsimpr",
    )
    return lb.build(res)


def prove_19_40_2(sys: System) -> Proof:
    """19.40-2: ∃ x ∃ y ( φ ∧ ψ ) → ( ∃ x ∃ y φ ∧ ∃ x ∃ y ψ ).

    Variant of 19.40 with two existential quantifiers.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wa wex 19.40 eximi syl.
    """
    lb = ProofBuilder(sys, "19.40-2")
    # 19.40 with y: ∃ y ( φ ∧ ψ ) → ( ∃ y φ ∧ ∃ y ψ )
    s1 = lb.ref(
        "s1",
        "∃ y ( φ ∧ ψ ) → ( ∃ y φ ∧ ∃ y ψ )",
        ref="19.40",
        note="19.40",
    )
    # eximi s1: ∃ x ∃ y ( φ ∧ ψ ) → ∃ x ( ∃ y φ ∧ ∃ y ψ )
    s2 = lb.ref(
        "s2",
        "∃ x ∃ y ( φ ∧ ψ ) → ∃ x ( ∃ y φ ∧ ∃ y ψ )",
        s1,
        ref="eximi",
        note="eximi 19.40",
    )
    # 19.40 with x, (∃y φ) and (∃y ψ):
    # ∃ x ( ∃ y φ ∧ ∃ y ψ ) → ( ∃ x ∃ y φ ∧ ∃ x ∃ y ψ )
    s3 = lb.ref(
        "s3",
        "∃ x ( ∃ y φ ∧ ∃ y ψ ) → ( ∃ x ∃ y φ ∧ ∃ x ∃ y ψ )",
        ref="19.40",
        note="19.40",
    )
    # syl s2, s3: ∃ x ∃ y ( φ ∧ ψ ) → ( ∃ x ∃ y φ ∧ ∃ x ∃ y ψ )
    res = lb.ref(
        "res",
        "∃ x ∃ y ( φ ∧ ψ ) → ( ∃ x ∃ y φ ∧ ∃ x ∃ y ψ )",
        s2,
        s3,
        ref="syl",
        note="syl eximi, 19.40",
    )
    return lb.build(res)


def prove_19_40b(sys: System) -> Proof:
    """19.40b: ( ∀ x φ ∨ ∀ x ψ ) → ( ( ∃ x φ ∧ ∃ x ψ ) ↔ ∃ x ( φ ∧ ψ ) ).

    If ∀x φ or ∀x ψ, then (∃x φ ∧ ∃x ψ) is equivalent to ∃x(φ ∧ ψ).
    (Contributed by NM, 16-Apr-1995.)
    set.mm proof: pm3.21 aleximi pm3.2 jaoa orcoms 19.40 impbid1.
    """
    lb = ProofBuilder(sys, "19.40b")

    # pm3.2: φ → ( ψ → ( φ ∧ ψ ) )
    s_pm32 = lb.ref(
        "s_pm32",
        "φ → ( ψ → ( φ ∧ ψ ) )",
        ref="pm3.2",
        note="pm3.2",
    )

    # aleximi pm3.2: ∀ x φ → ( ∃ x ψ → ∃ x ( φ ∧ ψ ) )
    s_alex1 = lb.ref(
        "s_alex1",
        "∀ x φ → ( ∃ x ψ → ∃ x ( φ ∧ ψ ) )",
        s_pm32,
        ref="aleximi",
        note="aleximi pm3.2",
    )

    # pm3.21 with φ:=ψ, ψ:=φ: ψ → ( φ → ( φ ∧ ψ ) )
    s_pm321 = lb.ref(
        "s_pm321",
        "ψ → ( φ → ( φ ∧ ψ ) )",
        ref="pm3.21",
        note="pm3.21",
    )

    # aleximi pm3.21: ∀ x ψ → ( ∃ x φ → ∃ x ( φ ∧ ψ ) )
    s_alex2 = lb.ref(
        "s_alex2",
        "∀ x ψ → ( ∃ x φ → ∃ x ( φ ∧ ψ ) )",
        s_pm321,
        ref="aleximi",
        note="aleximi pm3.21",
    )

    # jaoa with swapped inputs:
    # ( ∀ x ψ ∨ ∀ x φ ) → ( ( ∃ x φ ∧ ∃ x ψ ) → ∃ x ( φ ∧ ψ ) )
    s_jaoa = lb.ref(
        "s_jaoa",
        "( ∀ x ψ ∨ ∀ x φ ) → ( ( ∃ x φ ∧ ∃ x ψ ) → ∃ x ( φ ∧ ψ ) )",
        s_alex2,
        s_alex1,
        ref="jaoa",
        note="jaoa",
    )

    # orcoms swaps the disjunction:
    # ( ∀ x φ ∨ ∀ x ψ ) → ( ( ∃ x φ ∧ ∃ x ψ ) → ∃ x ( φ ∧ ψ ) )
    s_fwd = lb.ref(
        "s_fwd",
        "( ∀ x φ ∨ ∀ x ψ ) → ( ( ∃ x φ ∧ ∃ x ψ ) → ∃ x ( φ ∧ ψ ) )",
        s_jaoa,
        ref="orcoms",
        note="orcoms",
    )

    # 19.40: ∃ x ( φ ∧ ψ ) → ( ∃ x φ ∧ ∃ x ψ )
    s_1940 = lb.ref(
        "s_1940",
        "∃ x ( φ ∧ ψ ) → ( ∃ x φ ∧ ∃ x ψ )",
        ref="19.40",
        note="19.40",
    )

    # impbid1 combines the two directions
    res = lb.ref(
        "res",
        "( ∀ x φ ∨ ∀ x ψ ) → ( ( ∃ x φ ∧ ∃ x ψ ) ↔ ∃ x ( φ ∧ ψ ) )",
        s_fwd,
        s_1940,
        ref="impbid1",
        note="impbid1",
    )

    return lb.build(res)


def prove_imnang(sys: System) -> Proof:
    """imnang: ∀ x ( φ → ¬ ψ ) ↔ ∀ x ¬ ( φ ∧ ψ ).

    Quantified form of imnan.  From imnan and albii.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: imnan albii.
    """
    lb = ProofBuilder(sys, "imnang")
    # imnan: ( φ → ¬ ψ ) ↔ ¬ ( φ ∧ ψ )
    s1 = lb.ref(
        "s1",
        "( φ → ¬ ψ ) ↔ ¬ ( φ ∧ ψ )",
        ref="imnan",
        note="imnan",
    )
    # albii: universally quantify the biconditional
    res = lb.ref(
        "res",
        "∀ x ( φ → ¬ ψ ) ↔ ∀ x ¬ ( φ ∧ ψ )",
        s1,
        ref="albii",
        note="albii imnan",
    )
    return lb.build(res)


def prove_alequexv(sys: System) -> Proof:
    """alequexv: ∀ x ( x = y → φ ) → ∃ x φ.

    From ∀ x ( x = y → φ ), derive ∃ x φ using ax6ev and exim.
    (Contributed by NM, 10-Jan-1993.)
    set.mm proof: weq wi wal wex ax6ev exim mpi.
    """
    lb = ProofBuilder(sys, "alequexv")
    # ax6ev: ∃ x x = y
    s1 = lb.ref(
        "s1",
        "∃ x x = y",
        ref="ax6ev",
        note="ax6ev",
    )
    # exim with substitution φ := (x = y), ψ := φ: ∀ x ((x = y) → φ) → (∃ x (x = y) → ∃ x φ)
    s2 = lb.ref(
        "s2",
        "∀ x ( ( x = y ) → φ ) → ( ∃ x ( x = y ) → ∃ x φ )",
        ref="exim",
        note="exim",
    )
    # mpi with mpi.1 := s1 (∃ x x = y) and mpi.2 := s2
    res = lb.ref(
        "res",
        "∀ x ( x = y → φ ) → ∃ x φ",
        s1,
        s2,
        ref="mpi",
        note="mpi ax6ev, exim",
    )
    return lb.build(res)


def prove_exsbim(sys: System) -> Proof:
    """exsbim: ∃ y ∀ x ( x = y → φ ) → ∃ x φ.

    From alequexv and exlimiv.
    (Contributed by NM, 10-Jan-1993.)
    set.mm proof: weq wi wal wex alequexv exlimiv.
    """
    lb = ProofBuilder(sys, "exsbim")
    # alequexv: ∀ x ( x = y → φ ) → ∃ x φ
    s1 = lb.ref(
        "s1",
        "∀ x ( x = y → φ ) → ∃ x φ",
        ref="alequexv",
        note="alequexv",
    )
    # exlimiv: ( ∀ x ( x = y → φ ) → ∃ x φ ) ⊢ ( ∃ y ∀ x ( x = y → φ ) → ∃ x φ )
    res = lb.ref(
        "res",
        "∃ y ∀ x ( x = y → φ ) → ∃ x φ",
        s1,
        ref="exlimiv",
        note="exlimiv alequexv",
    )
    return lb.build(res)


def prove_equs4v(sys: System) -> Proof:
    """equs4v: ∀ x ( x = y → φ ) → ∃ x ( x = y ∧ φ ).

    If for all x, x = y implies φ, then there exists an x such that
    both x = y and φ hold.
    (Contributed by NM, 10-Jan-1993.)
    set.mm proof: weq wi wal wex wa ax6ev exintr mpi.
    """
    lb = ProofBuilder(sys, "equs4v")
    # ax6ev: ∃ x x = y
    s1 = lb.ref(
        "s1",
        "∃ x x = y",
        ref="ax6ev",
        note="ax6ev",
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
        note="mpi ax6ev, exintr",
    )
    return lb.build(res)


def prove_exan(sys: System) -> Proof:
    """exan: ∃ x ( φ ∧ ψ ).

    Existence of a conjunction.  From ∃ x φ and ψ, derive ∃ x ( φ ∧ ψ ).
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wa jctr eximii.
    """
    lb = ProofBuilder(sys, "exan")
    exan1 = lb.hyp("exan.1", "∃ x φ")
    exan2 = lb.hyp("exan.2", "ψ")
    # jctr: ψ ⊢ φ → ( φ ∧ ψ )
    s1 = lb.ref(
        "s1",
        "φ → ( φ ∧ ψ )",
        exan2,
        ref="jctr",
        note="jctr exan.2",
    )
    # eximii: ∃ x φ, ( φ → ( φ ∧ ψ ) ) ⊢ ∃ x ( φ ∧ ψ )
    res = lb.ref(
        "res",
        "∃ x ( φ ∧ ψ )",
        exan1,
        s1,
        ref="eximii",
        note="eximii exan.1, s1",
    )
    return lb.build(res)


def prove_19_23vv(sys: System) -> Proof:
    """19.23vv: ( ∀ x ∀ y ( φ → ψ ) ↔ ( ∃ x ∃ y φ → ψ ) ).

    Version of 19.23v with an additional universal quantifier over a
    distinct variable.  (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wi wal wex 19.23v albii bitri.
    """
    lb = ProofBuilder(sys, "19.23vv")
    # 19.23v with y: ( ∀ y ( φ → ψ ) ↔ ( ∃ y φ → ψ ) )
    s1 = lb.ref(
        "s1",
        "∀ y ( φ → ψ ) ↔ ( ∃ y φ → ψ )",
        ref="19.23v",
        note="19.23v",
    )
    # albii s1 with x: ( ∀ x ∀ y ( φ → ψ ) ↔ ∀ x ( ∃ y φ → ψ ) )
    s2 = lb.ref(
        "s2",
        "∀ x ∀ y ( φ → ψ ) ↔ ∀ x ( ∃ y φ → ψ )",
        s1,
        ref="albii",
        note="albii 19.23v",
    )
    # 19.23v with x and (∃ y φ) as antecedent:
    #   ( ∀ x ( ∃ y φ → ψ ) ↔ ( ∃ x ∃ y φ → ψ ) )
    s3 = lb.ref(
        "s3",
        "∀ x ( ∃ y φ → ψ ) ↔ ( ∃ x ∃ y φ → ψ )",
        ref="19.23v",
        note="19.23v",
    )
    # bitri s2, s3: ( ∀ x ∀ y ( φ → ψ ) ↔ ( ∃ x ∃ y φ → ψ ) )
    res = lb.ref(
        "res",
        "∀ x ∀ y ( φ → ψ ) ↔ ( ∃ x ∃ y φ → ψ )",
        s2,
        s3,
        ref="bitri",
        note="bitri albii, 19.23v",
    )
    return lb.build(res)


def prove_exa1(sys: System) -> Proof:
    """exa1: ∃ x φ → ∃ x ( ψ → φ ).

    Existential quantifier with weakening: if anything exists, then
    something implies it. From ax-1 and eximi.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wi ax-1 eximi.
    """
    lb = ProofBuilder(sys, "exa1")
    s1 = lb.ref("s1", "φ → ( ψ → φ )", ref="ax-1", note="ax-1")
    res = lb.ref(
        "res",
        "∃ x φ → ∃ x ( ψ → φ )",
        s1,
        ref="eximi",
        note="eximi ax-1",
    )
    return lb.build(res)


def prove_19_25(sys: System) -> Proof:
    """19.25: ∀ y ∃ x ( φ → ψ ) → ( ∃ y ∀ x φ → ∃ y ∃ x ψ ).

    Quantified implication and existentials.  From 19.35 and aleximi.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wi wex wal 19.35 biimpi aleximi.
    """
    lb = ProofBuilder(sys, "19.25")
    # 19.35: ∃ x ( φ → ψ ) ↔ ( ∀ x φ → ∃ x ψ )
    s1 = lb.ref(
        "s1",
        "∃ x ( φ → ψ ) ↔ ( ∀ x φ → ∃ x ψ )",
        ref="19.35",
        note="19.35",
    )
    # biimpi: forward direction
    s2 = lb.ref(
        "s2",
        "∃ x ( φ → ψ ) → ( ∀ x φ → ∃ x ψ )",
        s1,
        ref="biimpi",
        note="biimpi 19.35",
    )
    # aleximi with variable y
    res = lb.ref(
        "res",
        "∀ y ∃ x ( φ → ψ ) → ( ∃ y ∀ x φ → ∃ y ∃ x ψ )",
        s2,
        ref="aleximi",
        note="aleximi",
    )
    return lb.build(res)


def prove_19_24(sys: System) -> Proof:
    """19.24: ( ∀ x φ → ∀ x ψ ) → ∃ x ( φ → ψ ).

    Quantified implication to existential.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wal wi wex 19.2 imim2i 19.35 sylibr.
    """
    lb = ProofBuilder(sys, "19.24")
    # 19.2: ∀ x ψ → ∃ x ψ
    s1 = lb.ref("s1", "∀ x ψ → ∃ x ψ", ref="19.2", note="19.2")
    # imim2i with 19.2: ( ∀ x φ → ∀ x ψ ) → ( ∀ x φ → ∃ x ψ )
    s2 = lb.ref(
        "s2",
        "( ∀ x φ → ∀ x ψ ) → ( ∀ x φ → ∃ x ψ )",
        s1,
        ref="imim2i",
        note="imim2i 19.2",
    )
    # 19.35: ∃ x ( φ → ψ ) ↔ ( ∀ x φ → ∃ x ψ )
    s3 = lb.ref(
        "s3",
        "∃ x ( φ → ψ ) ↔ ( ∀ x φ → ∃ x ψ )",
        ref="19.35",
        note="19.35",
    )
    # sylibr: ( ∀ x φ → ∀ x ψ ) → ∃ x ( φ → ψ )
    res = lb.ref(
        "res",
        "( ∀ x φ → ∀ x ψ ) → ∃ x ( φ → ψ )",
        s2,
        s3,
        ref="sylibr",
        note="sylibr",
    )
    return lb.build(res)


def prove_19_35(sys: System) -> Proof:
    """19.35: ∃ x ( φ → ψ ) ↔ ( ∀ x φ → ∃ x ψ ).

    Quantified implication and universal-existential equivalence.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wi wex wal pm2.27 aleximi com12 wn exnal pm2.21 eximi sylbir exa1 impbii ja.
    """
    lb = ProofBuilder(sys, "19.35")

    # Direction 1: ∃x(φ → ψ) → (∀xφ → ∃xψ)
    # pm2.27: φ → ( ( φ → ψ ) → ψ )
    s1 = lb.ref("s1", "φ → ( ( φ → ψ ) → ψ )", ref="pm2.27", note="pm2.27")

    # aleximi with pm2.27 as hypothesis: ∀xφ → ( ∃x(φ → ψ) → ∃xψ )
    s2 = lb.ref(
        "s2",
        "∀ x φ → ( ∃ x ( φ → ψ ) → ∃ x ψ )",
        s1,
        ref="aleximi",
        note="aleximi pm2.27",
    )

    # com12: swap antecedents: ( ∀xφ → ( ∃x(φ → ψ) → ∃xψ ) ) → ( ∃x(φ → ψ) → ( ∀xφ → ∃xψ ) )
    s3 = lb.ref(
        "s3",
        "∃ x ( φ → ψ ) → ( ∀ x φ → ∃ x ψ )",
        s2,
        ref="com12",
        note="com12",
    )

    # Direction 2: ( ∀xφ → ∃xψ ) → ∃x(φ → ψ)

    # pm2.21: ¬ φ → ( φ → ψ )
    s4 = lb.ref("s4", "¬ φ → ( φ → ψ )", ref="pm2.21", note="pm2.21")

    # eximi on pm2.21: ∃x¬φ → ∃x(φ → ψ)
    s5 = lb.ref(
        "s5",
        "∃ x ¬ φ → ∃ x ( φ → ψ )",
        s4,
        ref="eximi",
        note="eximi pm2.21",
    )

    # exnal: ∃x¬φ ↔ ¬∀xφ
    s6 = lb.ref("s6", "∃ x ¬ φ ↔ ¬ ∀ x φ", ref="exnal", note="exnal")

    # sylbir: from exnal and s5, get ¬∀xφ → ∃x(φ → ψ)
    s7 = lb.ref(
        "s7",
        "¬ ∀ x φ → ∃ x ( φ → ψ )",
        s6,
        s5,
        ref="sylbir",
        note="sylbir exnal, eximi",
    )

    # exa1: ∃xψ → ∃x(φ → ψ)
    s8 = lb.ref(
        "s8",
        "∃ x ψ → ∃ x ( φ → ψ )",
        ref="exa1",
        note="exa1",
    )

    # ja: combine the two cases: ( ∀xφ → ∃xψ ) → ∃x(φ → ψ)
    s9 = lb.ref(
        "s9",
        "( ∀ x φ → ∃ x ψ ) → ∃ x ( φ → ψ )",
        s7,
        s8,
        ref="ja",
        note="ja",
    )

    # impbii: combine both directions
    res = lb.ref(
        "res",
        "∃ x ( φ → ψ ) ↔ ( ∀ x φ → ∃ x ψ )",
        s3,
        s9,
        ref="impbii",
        note="impbii",
    )

    return lb.build(res)


def prove_19_35i(sys: System) -> Proof:
    """19.35i: ∀ x φ → ∃ x ψ.

    Inference from 19.35.
    Hyp 1: ∃ x ( φ → ψ )
    Concl: ∀ x φ → ∃ x ψ

    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wi wex wal 19.35 mpbi.
    """
    lb = ProofBuilder(sys, "19.35i")
    hyp = lb.hyp("19.35i.1", "∃ x ( φ → ψ )")
    s1 = lb.ref(
        "s1",
        "∃ x ( φ → ψ ) ↔ ( ∀ x φ → ∃ x ψ )",
        ref="19.35",
        note="19.35",
    )
    res = lb.ref(
        "res",
        "∀ x φ → ∃ x ψ",
        hyp,
        s1,
        ref="mpbi",
        note="mpbi 19.35i.1, 19.35",
    )
    return lb.build(res)


def prove_19_35ri(sys: System) -> Proof:
    """19.35ri: ∃ x ( φ → ψ ).

    Inference from 19.35 (reverse of 19.35i).
    Hyp 1: ∀ x φ → ∃ x ψ
    Concl: ∃ x ( φ → ψ )

    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wi wex wal 19.35 mpbir.
    """
    lb = ProofBuilder(sys, "19.35ri")
    hyp = lb.hyp("19.35ri.1", "∀ x φ → ∃ x ψ")
    s1 = lb.ref(
        "s1",
        "∃ x ( φ → ψ ) ↔ ( ∀ x φ → ∃ x ψ )",
        ref="19.35",
        note="19.35",
    )
    res = lb.ref(
        "res",
        "∃ x ( φ → ψ )",
        hyp,
        s1,
        ref="mpbir",
        note="mpbir 19.35ri.1, 19.35",
    )
    return lb.build(res)


def prove_19_36imv(sys: System) -> Proof:
    """19.36imv: ∃ x ( φ → ψ ) → ( ∀ x φ → ψ ).

    One direction of 19.36 with distinct variable condition.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wal wi wex pm2.27 aleximi ax5e syl6com.
    """
    lb = ProofBuilder(sys, "19.36imv")

    # pm2.27: φ → ( ( φ → ψ ) → ψ )
    s1 = lb.ref("s1", "φ → ( ( φ → ψ ) → ψ )", ref="pm2.27", note="pm2.27")

    # aleximi with pm2.27 as hypothesis: ∀ x φ → ( ∃ x ( φ → ψ ) → ∃ x ψ )
    s2 = lb.ref(
        "s2",
        "∀ x φ → ( ∃ x ( φ → ψ ) → ∃ x ψ )",
        s1,
        ref="aleximi",
        note="aleximi pm2.27",
    )

    # ax5e: ∃ x ψ → ψ
    s3 = lb.ref("s3", "∃ x ψ → ψ", ref="ax5e", note="ax5e")

    # syl6com chains s2 and s3
    res = lb.ref(
        "res",
        "∃ x ( φ → ψ ) → ( ∀ x φ → ψ )",
        s2,
        s3,
        ref="syl6com",
        note="syl6com aleximi, ax5e",
    )

    return lb.build(res)


def prove_19_36iv(sys: System) -> Proof:
    """19.36iv: ∀ x φ → ψ.

    Inference form of 19.36imv.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wi wex wal 19.36imv ax-mp.
    """
    lb = ProofBuilder(sys, "19.36iv")
    hyp = lb.hyp("19.36iv.1", "∃ x ( φ → ψ )")
    # 19.36imv: ∃ x ( φ → ψ ) → ( ∀ x φ → ψ )
    s1 = lb.ref(
        "s1",
        "∃ x ( φ → ψ ) → ( ∀ x φ → ψ )",
        ref="19.36imv",
        note="19.36imv",
    )
    # MP: apply 19.36imv to the hypothesis
    res = lb.mp("res", hyp, s1, "MP 19.36imv, 19.36iv.1")
    return lb.build(res)


def prove_19_36v(sys: System) -> Proof:
    """19.36v: ∃ x ( φ → ψ ) ↔ ( ∀ x φ → ψ ).

    Existential quantifier distributes over implication when the
    consequent has no free x.  From 19.35, 19.9v, and imbi2i.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wi wex wal 19.35 19.9v imbi2i bitri.
    """
    lb = ProofBuilder(sys, "19.36v")

    # 19.35: ∃ x ( φ → ψ ) ↔ ( ∀ x φ → ∃ x ψ )
    s1 = lb.ref(
        "s1",
        "∃ x ( φ → ψ ) ↔ ( ∀ x φ → ∃ x ψ )",
        ref="19.35",
        note="19.35",
    )

    # 19.9v: ∃ x ψ ↔ ψ
    s2 = lb.ref(
        "s2",
        "∃ x ψ ↔ ψ",
        ref="19.9v",
        note="19.9v",
    )

    # imbi2i: ( ∀ x φ → ∃ x ψ ) ↔ ( ∀ x φ → ψ )
    s3 = lb.ref(
        "s3",
        "( ∀ x φ → ∃ x ψ ) ↔ ( ∀ x φ → ψ )",
        s2,
        ref="imbi2i",
        note="imbi2i 19.9v",
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


def prove_19_37imv(sys: System) -> Proof:
    """19.37imv: ∃ x ( φ → ψ ) → ( φ → ∃ x ψ ).

    Quantified implication with distinct variable condition.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wal wi wex ax-5 19.35 biimpi syl5.
    """
    lb = ProofBuilder(sys, "19.37imv")

    # ax-5: φ → ∀ x φ
    s1 = lb.ref(
        "s1",
        "φ → ∀ x φ",
        ref="ax-5",
        note="ax-5",
    )

    # 19.35: ∃ x ( φ → ψ ) ↔ ( ∀ x φ → ∃ x ψ )
    s2 = lb.ref(
        "s2",
        "∃ x ( φ → ψ ) ↔ ( ∀ x φ → ∃ x ψ )",
        ref="19.35",
        note="19.35",
    )

    # biimpi: forward direction of the biconditional
    s3 = lb.ref(
        "s3",
        "∃ x ( φ → ψ ) → ( ∀ x φ → ∃ x ψ )",
        s2,
        ref="biimpi",
        note="biimpi 19.35",
    )

    # syl5: combine ax-5 and the biimpi result
    res = lb.ref(
        "res",
        "∃ x ( φ → ψ ) → ( φ → ∃ x ψ )",
        s1,
        s3,
        ref="syl5",
        note="syl5 ax-5, 19.35",
    )

    return lb.build(res)


def prove_19_37iv(sys: System) -> Proof:
    """19.37iv: φ → ∃ x ψ.

    Inference form of 19.37imv.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wi wex 19.37imv ax-mp.
    """
    lb = ProofBuilder(sys, "19.37iv")
    hyp = lb.hyp("19.37iv.1", "∃ x ( φ → ψ )")
    # 19.37imv: ∃ x ( φ → ψ ) → ( φ → ∃ x ψ )
    s1 = lb.ref(
        "s1",
        "∃ x ( φ → ψ ) → ( φ → ∃ x ψ )",
        ref="19.37imv",
        note="19.37imv",
    )
    # mp: apply 19.37imv to the hypothesis
    res = lb.mp("res", hyp, s1, "MP 19.37imv, 19.37iv.1")
    return lb.build(res)


def prove_19_26_3an(sys: System) -> Proof:
    """19.26-3an: ∀ x ( φ ∧ ψ ∧ χ ) ↔ ( ∀ x φ ∧ ∀ x ψ ∧ ∀ x χ ).

    Distributivity of the universal quantifier over ternary conjunction.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wa wal w3a 19.26 anbi1i df-3an albii bitri 3bitr4i.
    """
    lb = ProofBuilder(sys, "19.26-3an")

    # df-3an: ( φ ∧ ψ ∧ χ ) ↔ ( ( φ ∧ ψ ) ∧ χ )
    s1 = lb.ref(
        "s1",
        "( φ ∧ ψ ∧ χ ) ↔ ( ( φ ∧ ψ ) ∧ χ )",
        ref="df-3an",
        note="df-3an",
    )

    # albii with s1: ∀ x ( φ ∧ ψ ∧ χ ) ↔ ∀ x ( ( φ ∧ ψ ) ∧ χ )
    s2 = lb.ref(
        "s2",
        "∀ x ( φ ∧ ψ ∧ χ ) ↔ ∀ x ( ( φ ∧ ψ ) ∧ χ )",
        s1,
        ref="albii",
        note="albii",
    )

    # 19.26 with ( ( φ ∧ ψ ), χ ): ∀ x ( ( φ ∧ ψ ) ∧ χ ) ↔ ( ∀ x ( φ ∧ ψ ) ∧ ∀ x χ )
    s3 = lb.ref(
        "s3",
        "∀ x ( ( φ ∧ ψ ) ∧ χ ) ↔ ( ∀ x ( φ ∧ ψ ) ∧ ∀ x χ )",
        ref="19.26",
        note="19.26",
    )

    # 19.26 with ( φ, ψ ): ∀ x ( φ ∧ ψ ) ↔ ( ∀ x φ ∧ ∀ x ψ )
    s4 = lb.ref(
        "s4",
        "∀ x ( φ ∧ ψ ) ↔ ( ∀ x φ ∧ ∀ x ψ )",
        ref="19.26",
        note="19.26",
    )

    # anbi1i with s4 and ∀ x χ: ( ∀ x ( φ ∧ ψ ) ∧ ∀ x χ ) ↔ ( ( ∀ x φ ∧ ∀ x ψ ) ∧ ∀ x χ )
    s5 = lb.ref(
        "s5",
        "( ∀ x ( φ ∧ ψ ) ∧ ∀ x χ ) ↔ ( ( ∀ x φ ∧ ∀ x ψ ) ∧ ∀ x χ )",
        s4,
        ref="anbi1i",
        note="anbi1i",
    )

    # bitri s3, s5: ∀ x ( ( φ ∧ ψ ) ∧ χ ) ↔ ( ( ∀ x φ ∧ ∀ x ψ ) ∧ ∀ x χ )
    s6 = lb.ref(
        "s6",
        "∀ x ( ( φ ∧ ψ ) ∧ χ ) ↔ ( ( ∀ x φ ∧ ∀ x ψ ) ∧ ∀ x χ )",
        s3,
        s5,
        ref="bitri",
        note="bitri",
    )

    # bitri s2, s6: ∀ x ( φ ∧ ψ ∧ χ ) ↔ ( ( ∀ x φ ∧ ∀ x ψ ) ∧ ∀ x χ )
    s7 = lb.ref(
        "s7",
        "∀ x ( φ ∧ ψ ∧ χ ) ↔ ( ( ∀ x φ ∧ ∀ x ψ ) ∧ ∀ x χ )",
        s2,
        s6,
        ref="bitri",
        note="bitri",
    )

    # df-3an with ( ∀ x φ, ∀ x ψ, ∀ x χ ): ( ∀ x φ ∧ ∀ x ψ ∧ ∀ x χ ) ↔ ( ( ∀ x φ ∧ ∀ x ψ ) ∧ ∀ x χ )
    s8 = lb.ref(
        "s8",
        "( ∀ x φ ∧ ∀ x ψ ∧ ∀ x χ ) ↔ ( ( ∀ x φ ∧ ∀ x ψ ) ∧ ∀ x χ )",
        ref="df-3an",
        note="df-3an",
    )

    # biid: ( ( ∀ x φ ∧ ∀ x ψ ) ∧ ∀ x χ ) ↔ ( ( ∀ x φ ∧ ∀ x ψ ) ∧ ∀ x χ )
    s9 = lb.ref(
        "s9",
        "( ( ∀ x φ ∧ ∀ x ψ ) ∧ ∀ x χ ) ↔ ( ( ∀ x φ ∧ ∀ x ψ ) ∧ ∀ x χ )",
        ref="biid",
        note="biid",
    )

    # 3bitr4i s9, s7, s8: ∀ x ( φ ∧ ψ ∧ χ ) ↔ ( ∀ x φ ∧ ∀ x ψ ∧ ∀ x χ )
    res = lb.ref(
        "res",
        "∀ x ( φ ∧ ψ ∧ χ ) ↔ ( ∀ x φ ∧ ∀ x ψ ∧ ∀ x χ )",
        s9,
        s7,
        s8,
        ref="3bitr4i",
        note="3bitr4i",
    )

    return lb.build(res)


def prove_19_43(sys: System) -> Proof:
    """19.43: ∃ x ( φ ∨ ψ ) ↔ ( ∃ x φ ∨ ∃ x ψ ).

    Existential quantifier distributes over disjunction.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wo wex wn wi wal df-or exbii 19.35 alnex imbi1i 3bitri bitr4i.
    """
    lb = ProofBuilder(sys, "19.43")

    # df-or: ( φ ∨ ψ ) ↔ ( ¬ φ → ψ )
    s1 = lb.ref("s1", "( φ ∨ ψ ) ↔ ( ¬ φ → ψ )", ref="df-or", note="df-or")

    # exbii: from df-or, get ∃ x ( φ ∨ ψ ) ↔ ∃ x ( ¬ φ → ψ )
    s2 = lb.ref(
        "s2",
        "∃ x ( φ ∨ ψ ) ↔ ∃ x ( ¬ φ → ψ )",
        s1,
        ref="exbii",
        note="exbii df-or",
    )

    # 19.35: ∃ x ( ¬ φ → ψ ) ↔ ( ∀ x ¬ φ → ∃ x ψ )
    s3 = lb.ref(
        "s3",
        "∃ x ( ¬ φ → ψ ) ↔ ( ∀ x ¬ φ → ∃ x ψ )",
        ref="19.35",
        note="19.35",
    )

    # alnex: ∀ x ¬ φ ↔ ¬ ∃ x φ
    s4 = lb.ref("s4", "∀ x ¬ φ ↔ ¬ ∃ x φ", ref="alnex", note="alnex")

    # imbi1i: from alnex, get ( ∀ x ¬ φ → ∃ x ψ ) ↔ ( ¬ ∃ x φ → ∃ x ψ )
    s5 = lb.ref(
        "s5",
        "( ∀ x ¬ φ → ∃ x ψ ) ↔ ( ¬ ∃ x φ → ∃ x ψ )",
        s4,
        ref="imbi1i",
        note="imbi1i alnex",
    )

    # 3bitri: chain s2, s3, s5 → ∃ x ( φ ∨ ψ ) ↔ ( ¬ ∃ x φ → ∃ x ψ )
    s6 = lb.ref(
        "s6",
        "∃ x ( φ ∨ ψ ) ↔ ( ¬ ∃ x φ → ∃ x ψ )",
        s2,
        s3,
        s5,
        ref="3bitri",
        note="3bitri",
    )

    # df-or: ( ∃ x φ ∨ ∃ x ψ ) ↔ ( ¬ ∃ x φ → ∃ x ψ )
    s7 = lb.ref(
        "s7",
        "( ∃ x φ ∨ ∃ x ψ ) ↔ ( ¬ ∃ x φ → ∃ x ψ )",
        ref="df-or",
        note="df-or",
    )

    # bitr4i: from s6 and s7 → ∃ x ( φ ∨ ψ ) ↔ ( ∃ x φ ∨ ∃ x ψ )
    res = lb.ref(
        "res",
        "∃ x ( φ ∨ ψ ) ↔ ( ∃ x φ ∨ ∃ x ψ )",
        s6,
        s7,
        ref="bitr4i",
        note="bitr4i",
    )

    return lb.build(res)


def prove_19_43OLD(sys: System) -> Proof:
    """19.43OLD: ∃ x ( φ ∨ ψ ) ↔ ( ∃ x φ ∨ ∃ x ψ ).

    Existential quantifier distributes over disjunction (older proof).
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: ioran albii 19.26 alnex anbi12i 3bitri notbii df-ex oran 3bitr4i.
    """
    lb = ProofBuilder(sys, "19.43OLD")

    # ioran: ¬ ( φ ∨ ψ ) ↔ ( ¬ φ ∧ ¬ ψ )
    s1 = lb.ref(
        "s1",
        "¬ ( φ ∨ ψ ) ↔ ( ¬ φ ∧ ¬ ψ )",
        ref="ioran",
        note="ioran",
    )

    # albii: ∀ x ¬ ( φ ∨ ψ ) ↔ ∀ x ( ¬ φ ∧ ¬ ψ )
    s2 = lb.ref(
        "s2",
        "∀ x ¬ ( φ ∨ ψ ) ↔ ∀ x ( ¬ φ ∧ ¬ ψ )",
        s1,
        ref="albii",
        note="albii ioran",
    )

    # 19.26: ∀ x ( ¬ φ ∧ ¬ ψ ) ↔ ( ∀ x ¬ φ ∧ ∀ x ¬ ψ )
    s3 = lb.ref(
        "s3",
        "∀ x ( ¬ φ ∧ ¬ ψ ) ↔ ( ∀ x ¬ φ ∧ ∀ x ¬ ψ )",
        ref="19.26",
        note="19.26",
    )

    # alnex: ∀ x ¬ φ ↔ ¬ ∃ x φ
    s4a = lb.ref(
        "s4a",
        "∀ x ¬ φ ↔ ¬ ∃ x φ",
        ref="alnex",
        note="alnex",
    )

    # alnex: ∀ x ¬ ψ ↔ ¬ ∃ x ψ
    s4b = lb.ref(
        "s4b",
        "∀ x ¬ ψ ↔ ¬ ∃ x ψ",
        ref="alnex",
        note="alnex",
    )

    # anbi12i: ( ∀ x ¬ φ ∧ ∀ x ¬ ψ ) ↔ ( ¬ ∃ x φ ∧ ¬ ∃ x ψ )
    s5 = lb.ref(
        "s5",
        "( ∀ x ¬ φ ∧ ∀ x ¬ ψ ) ↔ ( ¬ ∃ x φ ∧ ¬ ∃ x ψ )",
        s4a,
        s4b,
        ref="anbi12i",
        note="anbi12i alnex",
    )

    # 3bitri: ∀ x ¬ ( φ ∨ ψ ) ↔ ( ¬ ∃ x φ ∧ ¬ ∃ x ψ )
    s6 = lb.ref(
        "s6",
        "∀ x ¬ ( φ ∨ ψ ) ↔ ( ¬ ∃ x φ ∧ ¬ ∃ x ψ )",
        s2,
        s3,
        s5,
        ref="3bitri",
        note="3bitri",
    )

    # notbii: ¬ ∀ x ¬ ( φ ∨ ψ ) ↔ ¬ ( ¬ ∃ x φ ∧ ¬ ∃ x ψ )
    s7 = lb.ref(
        "s7",
        "¬ ∀ x ¬ ( φ ∨ ψ ) ↔ ¬ ( ¬ ∃ x φ ∧ ¬ ∃ x ψ )",
        s6,
        ref="notbii",
        note="notbii",
    )

    # df-ex: ∃ x ( φ ∨ ψ ) ↔ ¬ ∀ x ¬ ( φ ∨ ψ )
    s8 = lb.ref(
        "s8",
        "∃ x ( φ ∨ ψ ) ↔ ¬ ∀ x ¬ ( φ ∨ ψ )",
        ref="df-ex",
        note="df-ex",
    )

    # oran: ( ∃ x φ ∨ ∃ x ψ ) ↔ ¬ ( ¬ ∃ x φ ∧ ¬ ∃ x ψ )
    s9 = lb.ref(
        "s9",
        "( ∃ x φ ∨ ∃ x ψ ) ↔ ¬ ( ¬ ∃ x φ ∧ ¬ ∃ x ψ )",
        ref="oran",
        note="oran",
    )

    # 3bitr4i: ∃ x ( φ ∨ ψ ) ↔ ( ∃ x φ ∨ ∃ x ψ )
    res = lb.ref(
        "res",
        "∃ x ( φ ∨ ψ ) ↔ ( ∃ x φ ∨ ∃ x ψ )",
        s7,
        s8,
        s9,
        ref="3bitr4i",
        note="3bitr4i",
    )

    return lb.build(res)


def prove_ax6evr(sys: System) -> Proof:
    """ax6evr: ∃ x y = x.

    There exists a set equal to a given set. From ax6ev and equcomiv
    via eximii.
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "ax6evr")
    # ax6ev: ∃ x x = y
    s1 = lb.ref(
        "s1",
        "∃ x x = y",
        ref="ax6ev",
        note="ax6ev",
    )
    # equcomiv: x = y → y = x
    s2 = lb.ref(
        "s2",
        "x = y → y = x",
        ref="equcomiv",
        note="equcomiv",
    )
    # eximii: from ∃ x x = y and x = y → y = x, derive ∃ x y = x
    res = lb.ref(
        "res",
        "∃ x y = x",
        s1,
        s2,
        ref="eximii",
        note="eximii ax6ev, equcomiv",
    )
    return lb.build(res)


def prove_datisi(sys: System) -> Proof:
    """datisi: ∃ x ( χ ∧ ψ ).

    Syllogism datisi: from ∀ x ( φ → ψ ) and ∃ x ( φ ∧ χ ),
    derive ∃ x ( χ ∧ ψ ).  Commutes the conjunction in the minor
    with exancom/mpbi, then applies darii.
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: wa wex exancom mpbi darii.
    """
    lb = ProofBuilder(sys, "datisi")
    h_maj = lb.hyp("datisi.maj", "∀ x ( φ → ψ )")
    h_min = lb.hyp("datisi.min", "∃ x ( φ ∧ χ )")

    # exancom: ( ∃ x ( φ ∧ χ ) ↔ ∃ x ( χ ∧ φ ) )
    s1 = lb.ref(
        "s1",
        "( ∃ x ( φ ∧ χ ) ↔ ∃ x ( χ ∧ φ ) )",
        ref="exancom",
        note="exancom",
    )

    # mpbi: from datisi.min and exancom, derive ∃ x ( χ ∧ φ )
    s2 = lb.ref(
        "s2",
        "∃ x ( χ ∧ φ )",
        h_min,
        s1,
        ref="mpbi",
        note="mpbi datisi.min, exancom",
    )

    # darii: from datisi.maj and s2, derive ∃ x ( χ ∧ ψ )
    res = lb.ref(
        "res",
        "∃ x ( χ ∧ ψ )",
        h_maj,
        s2,
        ref="darii",
        note="darii datisi.maj, s2",
    )
    return lb.build(res)


def prove_dimatis(sys: System) -> Proof:
    """dimatis: ∃ x ( χ ∧ φ ).

    Syllogism dimatis: from ∃ x ( φ ∧ ψ ) and ∀ x ( ψ → χ ),
    derive ∃ x ( χ ∧ φ ).  Commutes the conjunction in the major
    with exancom/mpbi, then applies darii.
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: wa wex darii exancom mpbi.
    """
    lb = ProofBuilder(sys, "dimatis")
    h_maj = lb.hyp("dimatis.maj", "∃ x ( φ ∧ ψ )")
    h_min = lb.hyp("dimatis.min", "∀ x ( ψ → χ )")

    # darii: from dimatis.min and dimatis.maj, derive ∃ x ( φ ∧ χ )
    s3 = lb.ref(
        "s3",
        "∃ x ( φ ∧ χ )",
        h_min,
        h_maj,
        ref="darii",
        note="darii dimatis.min, dimatis.maj",
    )
    s4 = lb.ref(
        "s4",
        "( ∃ x ( φ ∧ χ ) ↔ ∃ x ( χ ∧ φ ) )",
        ref="exancom",
        note="exancom",
    )
    res = lb.ref(
        "res",
        "∃ x ( χ ∧ φ )",
        s3,
        s4,
        ref="mpbi",
        note="mpbi darii, exancom",
    )
    return lb.build(res)


def prove_disamis(sys: System) -> Proof:
    """disamis: ∃ x ( χ ∧ ψ ).

    Syllogism disamis: from ∃ x ( φ ∧ ψ ) and ∀ x ( φ → χ ),
    derive ∃ x ( χ ∧ ψ ).  Applies datisi with the hypotheses
    swapped, then commutes the conjunction with exancom/mpbi.
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: wa wex datisi exancom mpbi.
    """
    lb = ProofBuilder(sys, "disamis")
    h_maj = lb.hyp("disamis.maj", "∃ x ( φ ∧ ψ )")
    h_min = lb.hyp("disamis.min", "∀ x ( φ → χ )")

    # datisi: from disamis.min (∀x(φ→χ)) and disamis.maj (∃x(φ∧ψ)),
    #   derive ∃ x ( ψ ∧ χ )
    s1 = lb.ref(
        "s1",
        "∃ x ( ψ ∧ χ )",
        h_min,
        h_maj,
        ref="datisi",
        note="datisi disamis.min, disamis.maj",
    )

    # exancom: ( ∃ x ( ψ ∧ χ ) ↔ ∃ x ( χ ∧ ψ ) )
    s2 = lb.ref(
        "s2",
        "( ∃ x ( ψ ∧ χ ) ↔ ∃ x ( χ ∧ ψ ) )",
        ref="exancom",
        note="exancom",
    )

    # mpbi: from datisi result and exancom, derive ∃ x ( χ ∧ ψ )
    res = lb.ref(
        "res",
        "∃ x ( χ ∧ ψ )",
        s1,
        s2,
        ref="mpbi",
        note="mpbi datisi, exancom",
    )
    return lb.build(res)


def prove_bocardo(sys: System) -> Proof:
    """bocardo: ∃ x ( χ ∧ ¬ ψ ).

    Syllogism bocardo: from ∃ x ( φ ∧ ¬ ψ ) and ∀ x ( φ → χ ),
    derive ∃ x ( χ ∧ ¬ ψ ).  Direct application of disamis with ψ
    replaced by ¬ ψ.  (Contributed by NM, 3-Jan-1993.)
    set.mm proof: wn disamis.
    """
    lb = ProofBuilder(sys, "bocardo")
    h_maj = lb.hyp("bocardo.maj", "∃ x ( φ ∧ ¬ ψ )")
    h_min = lb.hyp("bocardo.min", "∀ x ( φ → χ )")

    # disamis: from bocardo.maj (∃x(φ∧¬ψ)) and bocardo.min (∀x(φ→χ)),
    #   derive ∃ x ( χ ∧ ¬ ψ )
    res = lb.ref(
        "res",
        "∃ x ( χ ∧ ¬ ψ )",
        h_maj,
        h_min,
        ref="disamis",
        note="disamis bocardo.maj, bocardo.min",
    )

    return lb.build(res)


def prove_spfw(sys: System) -> Proof:
    """spfw: ∀ x φ → φ.

    If ¬ ψ → ∀ x ¬ ψ, ∀ x φ → ∀ y ∀ x φ, ¬ φ → ∀ y ¬ φ, and
    x = y → ( φ ↔ ψ ), then ∀ x φ → φ.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "spfw")
    hyp1 = lb.hyp("spfw.1", "¬ ψ → ∀ x ¬ ψ")
    hyp2 = lb.hyp("spfw.2", "∀ x φ → ∀ y ∀ x φ")
    hyp3 = lb.hyp("spfw.3", "¬ φ → ∀ y ¬ φ")
    hyp4 = lb.hyp("spfw.4", "x = y → ( φ ↔ ψ )")

    # biimpd from spfw.4: x = y → ( φ → ψ )
    s1 = lb.ref(
        "s1",
        "x = y → ( φ → ψ )",
        hyp4,
        ref="biimpd",
        note="biimpd spfw.4",
    )

    # cbvaliw with spfw.2, spfw.1, and s1: ∀ x φ → ∀ y ψ
    s2 = lb.ref(
        "s2",
        "∀ x φ → ∀ y ψ",
        hyp2,
        hyp1,
        s1,
        ref="cbvaliw",
        note="cbvaliw spfw.2, spfw.1, biimpd",
    )

    # biimprd from spfw.4: x = y → ( ψ → φ )
    s3 = lb.ref(
        "s3",
        "x = y → ( ψ → φ )",
        hyp4,
        ref="biimprd",
        note="biimprd spfw.4",
    )

    # equcoms: y = x → ( ψ → φ )
    s4 = lb.ref(
        "s4",
        "y = x → ( ψ → φ )",
        s3,
        ref="equcoms",
        note="equcoms biimprd",
    )

    # spimw with spfw.3 and s4: ∀ y ψ → φ
    s5 = lb.ref(
        "s5",
        "∀ y ψ → φ",
        hyp3,
        s4,
        ref="spimw",
        note="spimw spfw.3, equcoms",
    )

    # syl: combine ∀ x φ → ∀ y ψ and ∀ y ψ → φ
    res = lb.ref(
        "res",
        "∀ x φ → φ",
        s2,
        s5,
        ref="syl",
        note="syl",
    )

    return lb.build(res)


def prove_sptruw(sys: System) -> Proof:
    """sptruw: ∀ x φ → φ.

    Universal specialization from a wff hypothesis. Given φ, derive
    ∀ x φ → φ via a1i.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "sptruw")
    hyp = lb.hyp("sptruw.1", "φ")
    res = lb.ref("res", "∀ x φ → φ", hyp, ref="a1i", note="a1i sptruw.1")
    return lb.build(res)


def prove_spfalw(sys: System) -> Proof:
    """spfalw: ∀ x φ → φ.

    If ¬ φ, then ∀ x φ → φ.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wn hbth spnfw.
    """
    lb = ProofBuilder(sys, "spfalw")
    hyp = lb.hyp("spfalw.1", "¬ φ")
    s1 = lb.ref("s1", "¬ φ → ∀ x ¬ φ", hyp, ref="hbth", note="hbth spfalw.1")
    # spnfw: (¬ φ → ∀ x ¬ φ) → (∀ x φ → φ)
    res = lb.ref("res", "∀ x φ → φ", s1, ref="spnfw", note="spnfw")
    return lb.build(res)


def prove_spnfw(sys: System) -> Proof:
    """spnfw: ∀ x φ → φ.

    If ¬ φ → ∀ x ¬ φ, then ∀ x φ → φ.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: vy weq idd spimw.
    """
    lb = ProofBuilder(sys, "spnfw")
    hyp = lb.hyp("spnfw.1", "¬ φ → ∀ x ¬ φ")

    # idd: x = y → ( φ → φ )
    s1 = lb.ref(
        "s1",
        "x = y → ( φ → φ )",
        ref="idd",
        note="idd with φ := x = y",
    )

    # spimw with spimw.1, spimw.2: ∀ x φ → φ
    res = lb.ref(
        "res",
        "∀ x φ → φ",
        hyp,
        s1,
        ref="spimw",
        note="spimw spnfw.1, idd",
    )

    return lb.build(res)


def prove_spvw(sys: System) -> Proof:
    """spvw: ∀ x φ → φ.

    Universal specialization.  Uses ax-5 (ax-5) with ¬ φ substituted
    for φ to obtain the spnfw hypothesis ¬ φ → ∀ x ¬ φ, then applies
    spnfw.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wn ax-5 spnfw.
    """
    lb = ProofBuilder(sys, "spvw")
    # ax-5 with φ := ¬ φ: ¬ φ → ∀ x ¬ φ
    s1 = lb.ref(
        "s1",
        "¬ φ → ∀ x ¬ φ",
        ref="ax-5",
        note="ax-5 — generalized to ¬ φ",
    )
    # spnfw spnfw.1 = s1: ∀ x φ → φ
    res = lb.ref(
        "res",
        "∀ x φ → φ",
        s1,
        ref="spnfw",
        note="spnfw ax-5",
    )
    return lb.build(res)


def prove_2exnexn(sys: System) -> Proof:
    """2exnexn: ∃ x ∀ y φ ↔ ¬ ∀ x ∃ y ¬ φ.

    Swap of quantifiers with negation.  From alexn and con2bii.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "2exnexn")

    # alexn: ∀ x ∃ y ¬ φ ↔ ¬ ∃ x ∀ y φ
    s1 = lb.ref(
        "s1",
        "∀ x ∃ y ¬ φ ↔ ¬ ∃ x ∀ y φ",
        ref="alexn",
        note="alexn",
    )

    # con2bii: from (∀ x ∃ y ¬ φ ↔ ¬ ∃ x ∀ y φ),
    # deduce (∃ x ∀ y φ ↔ ¬ ∀ x ∃ y ¬ φ)
    res = lb.ref(
        "res",
        "∃ x ∀ y φ ↔ ¬ ∀ x ∃ y ¬ φ",
        s1,
        ref="con2bii",
        note="con2bii alexn",
    )

    return lb.build(res)


def prove_19_3v(sys: System) -> Proof:
    """19.3v: ( ∀ x φ ↔ φ ).

    A variable is not free in a closed wff.
    From spvw and ax-5 via impbii.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wal spvw ax-5 impbii.
    """
    lb = ProofBuilder(sys, "19.3v")
    # spvw: ∀ x φ → φ
    s1 = lb.ref(
        "s1",
        "∀ x φ → φ",
        ref="spvw",
        note="spvw",
    )
    # ax-5 (ax-5): φ → ∀ x φ
    s2 = lb.ref(
        "s2",
        "φ → ∀ x φ",
        ref="ax-5",
        note="ax-5 — ax-5",
    )
    # impbii: ( ∀ x φ ↔ φ )
    res = lb.ref(
        "res",
        "( ∀ x φ ↔ φ )",
        s1,
        s2,
        ref="impbii",
        note="impbii",
    )
    return lb.build(res)


def prove_19_37v(sys: System) -> Proof:
    """19.37v: ( ∃ x ( φ → ψ ) ↔ ( φ → ∃ x ψ ) ).

    Quantified implication equivalence with distinct variable condition.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wi wex wal 19.35 19.3v imbi1i bitri.
    """
    lb = ProofBuilder(sys, "19.37v")
    # 19.35: ∃ x ( φ → ψ ) ↔ ( ∀ x φ → ∃ x ψ )
    s1 = lb.ref(
        "s1",
        "∃ x ( φ → ψ ) ↔ ( ∀ x φ → ∃ x ψ )",
        ref="19.35",
        note="19.35",
    )
    # 19.3v: ∀ x φ ↔ φ
    s2 = lb.ref(
        "s2",
        "∀ x φ ↔ φ",
        ref="19.3v",
        note="19.3v",
    )
    # imbi1i: ( ∀ x φ → ∃ x ψ ) ↔ ( φ → ∃ x ψ )
    s3 = lb.ref(
        "s3",
        "( ∀ x φ → ∃ x ψ ) ↔ ( φ → ∃ x ψ )",
        s2,
        ref="imbi1i",
        note="imbi1i 19.3v",
    )
    # bitri: chain s1 and s3
    res = lb.ref(
        "res",
        "( ∃ x ( φ → ψ ) ↔ ( φ → ∃ x ψ ) )",
        s1,
        s3,
        ref="bitri",
        note="bitri 19.35, imbi1i",
    )
    return lb.build(res)


def prove_exgen(sys: System) -> Proof:
    """exgen: ∃ x φ.

    From φ, conclude ∃ x φ.  (Contributed by NM, 10-Jan-1993.)
    set.mm proof: vy weq idd speiv.
    """
    lb = ProofBuilder(sys, "exgen")
    hyp = lb.hyp("exgen.1", "φ")

    # idd with φ := x = y, ψ := φ: x = y → ( φ → φ )
    s1 = lb.ref(
        "s1",
        "x = y → ( φ → φ )",
        ref="idd",
        note="idd with φ := x = y",
    )

    # speiv with speiv.1: x = y → ( φ → φ ), speiv.2: φ
    res = lb.ref(
        "res",
        "∃ x φ",
        s1,
        hyp,
        ref="speiv",
        note="speiv",
    )

    return lb.build(res)


def prove_extru(sys: System) -> Proof:
    """extru: ∃ x ⊤.

    Existence of something true.  (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wtru tru exgen.
    """
    lb = ProofBuilder(sys, "extru")
    s_tru = lb.ref("s_tru", "⊤", ref="tru", note="tru")
    res = lb.ref("res", "∃ x ⊤", s_tru, ref="exgen", note="exgen")
    return lb.build(res)


def prove_emptyex(sys: System) -> Proof:
    """emptyex: ( ¬ ∃ x ⊤ → ¬ ∃ x φ ).

    If nothing true exists, then nothing exists.  From trud and eximi
    and con3i.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "emptyex")
    # trud: ( φ → ⊤ )
    s1 = lb.ref("s1", "( φ → ⊤ )", ref="trud", note="trud")
    # eximi trud: ( ∃ x φ → ∃ x ⊤ )
    s2 = lb.ref("s2", "( ∃ x φ → ∃ x ⊤ )", s1, ref="eximi", note="eximi trud")
    # con3i eximi: ( ¬ ∃ x ⊤ → ¬ ∃ x φ )
    res = lb.ref("res", "( ¬ ∃ x ⊤ → ¬ ∃ x φ )", s2, ref="con3i", note="con3i eximi")
    return lb.build(res)


def prove_emptyal(sys: System) -> Proof:
    """emptyal: ( ¬ ∃ x ⊤ → ∀ x φ ).

    If nothing true exists, then anything holds universally.
    From emptyex (with φ := ¬ φ) and alex via sylibr.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "emptyal")
    # emptyex with φ := ¬ φ: ( ¬ ∃ x ⊤ → ¬ ∃ x ¬ φ )
    s1 = lb.ref(
        "s1",
        "( ¬ ∃ x ⊤ → ¬ ∃ x ¬ φ )",
        ref="emptyex",
        note="emptyex with φ := ¬ φ",
    )
    # alex: ∀ x φ ↔ ¬ ∃ x ¬ φ
    s2 = lb.ref(
        "s2",
        "∀ x φ ↔ ¬ ∃ x ¬ φ",
        ref="alex",
        note="alex",
    )
    # sylibr s1, s2: ( ¬ ∃ x ⊤ → ∀ x φ )
    res = lb.ref(
        "res",
        "( ¬ ∃ x ⊤ → ∀ x φ )",
        s1,
        s2,
        ref="sylibr",
        note="sylibr emptyex, alex",
    )
    return lb.build(res)


def prove_emptynf(sys: System) -> Proof:
    """emptynf: ( ¬ ∃ x ⊤ → Ⅎ x φ ).

    If nothing true exists, then x is (effectively) not free in φ.
    From emptyal and nftht via syl.
    (Contributed by NM, 7-Nov-1995.)
    """
    lb = ProofBuilder(sys, "emptynf")
    # emptyal: ( ¬ ∃ x ⊤ → ∀ x φ )
    s1 = lb.ref(
        "s1",
        "( ¬ ∃ x ⊤ → ∀ x φ )",
        ref="emptyal",
        note="emptyal",
    )
    # nftht: ∀ x φ → Ⅎ x φ
    s2 = lb.ref(
        "s2",
        "∀ x φ → Ⅎ x φ",
        ref="nftht",
        note="nftht",
    )
    # syl: ( ¬ ∃ x ⊤ → Ⅎ x φ )
    res = lb.ref(
        "res",
        "( ¬ ∃ x ⊤ → Ⅎ x φ )",
        s1,
        s2,
        ref="syl",
        note="syl emptyal, nftht",
    )
    return lb.build(res)


def prove_pm11_53v(sys: System) -> Proof:
    """pm11.53v: ( ∀ x ∀ y ( φ → ψ ) ↔ ( ∃ x φ → ∀ y ψ ) ).

    Swap universal and existential quantifiers over an implication.
    (Contributed by NM, 10-Jan-1993.)
    set.mm proof: wi wal wex 19.21v albii 19.23v bitri.
    """
    lb = ProofBuilder(sys, "pm11.53v")
    # 19.21v with variable y: ( ∀ y ( φ → ψ ) ↔ ( φ → ∀ y ψ ) )
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
    # 19.23v: ( ∀ x ( φ → ∀ y ψ ) ↔ ( ∃ x φ → ∀ y ψ ) )
    s3 = lb.ref(
        "s3",
        "( ∀ x ( φ → ∀ y ψ ) ↔ ( ∃ x φ → ∀ y ψ ) )",
        ref="19.23v",
        note="19.23v",
    )
    # bitri: chain s2 and s3
    res = lb.ref(
        "res",
        "( ∀ x ∀ y ( φ → ψ ) ↔ ( ∃ x φ → ∀ y ψ ) )",
        s2,
        s3,
        ref="bitri",
        note="bitri",
    )
    return lb.build(res)


def prove_19_30(sys: System) -> Proof:
    """19.30: ∀ x ( φ ∨ ψ ) → ( ∀ x φ ∨ ∃ x ψ ).

    Quantifier distribution over disjunction: if for all x, φ or ψ
    holds, then either for all x φ holds, or there exists an x for
    which ψ holds.
    """
    lb = ProofBuilder(sys, "19.30")

    # pm2.53: ( φ ∨ ψ ) → ( ¬ φ → ψ )
    s1 = lb.ref("s1", "( φ ∨ ψ ) → ( ¬ φ → ψ )", ref="pm2.53", note="pm2.53")

    # aleximi: from pm2.53, ∀ x ( φ ∨ ψ ) → ( ∃ x ¬ φ → ∃ x ψ )
    s2 = lb.ref(
        "s2",
        "∀ x ( φ ∨ ψ ) → ( ∃ x ¬ φ → ∃ x ψ )",
        s1,
        ref="aleximi",
        note="aleximi pm2.53",
    )

    # exnal: ∃ x ¬ φ ↔ ¬ ∀ x φ
    s3 = lb.ref("s3", "∃ x ¬ φ ↔ ¬ ∀ x φ", ref="exnal", note="exnal")

    # biimtrrid: from exnal (biconditional) and aleximi (implication),
    #   get ∀ x ( φ ∨ ψ ) → ( ¬ ∀ x φ → ∃ x ψ )
    s4 = lb.ref(
        "s4",
        "∀ x ( φ ∨ ψ ) → ( ¬ ∀ x φ → ∃ x ψ )",
        s3,
        s2,
        ref="biimtrrid",
        note="biimtrrid exnal, aleximi",
    )

    # orrd: from ∀ x ( φ ∨ ψ ) → ( ¬ ∀ x φ → ∃ x ψ ),
    #   get ∀ x ( φ ∨ ψ ) → ( ∀ x φ ∨ ∃ x ψ )
    res = lb.ref(
        "res",
        "∀ x ( φ ∨ ψ ) → ( ∀ x φ ∨ ∃ x ψ )",
        s4,
        ref="orrd",
        note="orrd",
    )

    return lb.build(res)


def prove_nfa1(sys: System) -> Proof:
    """nfa1: F/ x ∀ x φ.

    x is not free in ∀ x φ.
    (Contributed by NM, 10-Jan-1993.)
    set.mm proof: wal wn wex alex nfe1 nfn nfxfr.
    """
    lb = ProofBuilder(sys, "nfa1")
    # alex: ∀ x φ ↔ ¬ ∃ x ¬ φ
    s1 = lb.ref(
        "s1",
        "∀ x φ ↔ ¬ ∃ x ¬ φ",
        ref="alex",
        note="alex",
    )
    # nfe1 with φ := ¬ φ: F/ x ∃ x ¬ φ
    s2 = lb.ref(
        "s2",
        "F/ x ∃ x ¬ φ",
        ref="nfe1",
        note="nfe1 with φ := ¬ φ",
    )
    # nfn: from F/ x ∃ x ¬ φ, get F/ x ¬ ∃ x ¬ φ
    s3 = lb.ref(
        "s3",
        "F/ x ¬ ∃ x ¬ φ",
        s2,
        ref="nfn",
        note="nfn nfe1",
    )
    # nfxfr: from ∀ x φ ↔ ¬ ∃ x ¬ φ and F/ x ¬ ∃ x ¬ φ,
    #   get F/ x ∀ x φ
    res = lb.ref(
        "res",
        "F/ x ∀ x φ",
        s1,
        s3,
        ref="nfxfr",
        note="nfxfr alex, nfn",
    )
    return lb.build(res)


def prove_nfa2(sys: System) -> Proof:
    """nfa2: F/ x ∀ y ∀ x φ.

    Commute universal quantifiers with alcom, apply nfa1 to the
    inner ∀ x ∀ y φ, then transfer not-free across the biconditional
    with nfxfr.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wal alcom nfa1 nfxfr.
    """
    lb = ProofBuilder(sys, "nfa2")
    # alcom: ∀ y ∀ x φ ↔ ∀ x ∀ y φ
    s1 = lb.ref(
        "s1",
        "∀ y ∀ x φ ↔ ∀ x ∀ y φ",
        ref="alcom",
        note="alcom",
    )
    # nfa1 with φ := ∀ y φ: F/ x ∀ x ∀ y φ
    s2 = lb.ref(
        "s2",
        "F/ x ∀ x ∀ y φ",
        ref="nfa1",
        note="nfa1 with ∀ y φ",
    )
    # nfxfr: from the biconditional and the not-free statement,
    #   derive F/ x ∀ y ∀ x φ
    res = lb.ref(
        "res",
        "F/ x ∀ y ∀ x φ",
        s1,
        s2,
        ref="nfxfr",
        note="nfxfr alcom, nfa1",
    )
    return lb.build(res)


def prove_spsv(sys: System) -> Proof:
    """spsv: ∀ x φ → ψ.

    If φ → ψ, then ∀ x φ → ψ.  Uses a1i to strengthen the hypothesis
    and spimvw to introduce the quantifier.
    """
    lb = ProofBuilder(sys, "spsv")
    hyp = lb.hyp("spsv.1", "φ → ψ")
    # a1i: (φ → ψ) ⊢ (x = y) → (φ → ψ)
    s1 = lb.ref(
        "s1",
        "x = y → ( φ → ψ )",
        hyp,
        ref="a1i",
        note="a1i spsv.1",
    )
    # spimvw: (x = y → (φ → ψ)) ⊢ ∀ x φ → ψ
    res = lb.ref(
        "res",
        "∀ x φ → ψ",
        s1,
        ref="spimvw",
        note="spimvw a1i",
    )
    return lb.build(res)


def prove_nfna1(sys: System) -> Proof:
    """nfna1: F/ x ¬ ∀ x φ.

    x is not free in ¬ ∀ x φ. From nfa1 and nfn.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wal nfa1 nfn.
    """
    lb = ProofBuilder(sys, "nfna1")
    s1 = lb.ref(
        "s1",
        "F/ x ∀ x φ",
        ref="nfa1",
        note="nfa1",
    )
    res = lb.ref(
        "res",
        "F/ x ¬ ∀ x φ",
        s1,
        ref="nfn",
        note="nfn nfa1",
    )
    return lb.build(res)


def prove_cbvaliw(sys: System) -> Proof:
    """cbvaliw: ∀ x φ → ∀ y ψ.

    Change bound variable.  Uses spimw to derive ∀ x φ → ψ from
    cbvaliw.2 and cbvaliw.3, then alrimih with cbvaliw.1 to
    generalize the consequent.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wal spimw alrimih.
    """
    lb = ProofBuilder(sys, "cbvaliw")
    hyp1 = lb.hyp("cbvaliw.1", "∀ x φ → ∀ y ∀ x φ")
    hyp2 = lb.hyp("cbvaliw.2", "¬ ψ → ∀ x ¬ ψ")
    hyp3 = lb.hyp("cbvaliw.3", "x = y → ( φ → ψ )")

    # spimw with cbvaliw.2 and cbvaliw.3: ∀ x φ → ψ
    s1 = lb.ref(
        "s1",
        "∀ x φ → ψ",
        hyp2,
        hyp3,
        ref="spimw",
        note="spimw cbvaliw.2, cbvaliw.3",
    )

    # alrimih with cbvaliw.1 and s1: ∀ x φ → ∀ y ψ
    res = lb.ref(
        "res",
        "∀ x φ → ∀ y ψ",
        hyp1,
        s1,
        ref="alrimih",
        note="alrimih cbvaliw.1, spimw",
    )

    return lb.build(res)


def prove_cbvalw(sys: System) -> Proof:
    """cbvalw: ( ∀ x φ ↔ ∀ y ψ ).

    Change bound variable.  Uses cbvaliw in both directions together
    with biimpd, biimprd, and equcoms to handle the biconditional
    hypothesis cbvalw.5.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wal weq biimpd cbvaliw biimprd equcoms impbii.
    """
    lb = ProofBuilder(sys, "cbvalw")
    hyp1 = lb.hyp("cbvalw.1", "∀ x φ → ∀ y ∀ x φ")
    hyp2 = lb.hyp("cbvalw.2", "¬ ψ → ∀ x ¬ ψ")
    hyp3 = lb.hyp("cbvalw.3", "∀ y ψ → ∀ x ∀ y ψ")
    hyp4 = lb.hyp("cbvalw.4", "¬ φ → ∀ y ¬ φ")
    hyp5 = lb.hyp("cbvalw.5", "x = y → ( φ ↔ ψ )")

    # Forward direction: ∀ x φ → ∀ y ψ
    # biimpd: from x = y → ( φ ↔ ψ ) derive x = y → ( φ → ψ )
    s_fwd_eq = lb.ref(
        "s_fwd_eq",
        "x = y → ( φ → ψ )",
        hyp5,
        ref="biimpd",
        note="biimpd cbvalw.5",
    )
    # cbvaliw: (∀x φ → ∀y ∀x φ), (¬ψ → ∀x ¬ψ), (x=y → (φ→ψ)) ⊢ ∀x φ → ∀y ψ
    s_fwd = lb.ref(
        "s_fwd",
        "∀ x φ → ∀ y ψ",
        hyp1,
        hyp2,
        s_fwd_eq,
        ref="cbvaliw",
        note="cbvaliw cbvalw.1, cbvalw.2, biimpd",
    )

    # Reverse direction: ∀ y ψ → ∀ x φ
    # biimprd: from x = y → ( φ ↔ ψ ) derive x = y → ( ψ → φ )
    s_rev_eq = lb.ref(
        "s_rev_eq",
        "x = y → ( ψ → φ )",
        hyp5,
        ref="biimprd",
        note="biimprd cbvalw.5",
    )
    # equcoms: from x = y → ( ψ → φ ) derive y = x → ( ψ → φ )
    s_rev_eqc = lb.ref(
        "s_rev_eqc",
        "y = x → ( ψ → φ )",
        s_rev_eq,
        ref="equcoms",
        note="equcoms biimprd",
    )
    # cbvaliw: (∀y ψ → ∀x ∀y ψ), (¬φ → ∀y ¬φ), (y=x → (ψ→φ)) ⊢ ∀y ψ → ∀x φ
    s_rev = lb.ref(
        "s_rev",
        "∀ y ψ → ∀ x φ",
        hyp3,
        hyp4,
        s_rev_eqc,
        ref="cbvaliw",
        note="cbvaliw cbvalw.3, cbvalw.4, equcoms",
    )

    # impbii: combine both directions into biconditional
    res = lb.ref(
        "res",
        "( ∀ x φ ↔ ∀ y ψ )",
        s_fwd,
        s_rev,
        ref="impbii",
        note="impbii",
    )

    return lb.build(res)


def prove_cbvalivw(sys: System) -> Proof:
    """cbvalivw: ∀ x φ → ∀ y ψ.

    Change bound variable using distinct variable conditions.
    Uses spimvw to remove the universal quantifier from the
    antecedent, then alrimiv to add a universal quantifier
    to the consequent.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wal spimvw alrimiv.
    """
    lb = ProofBuilder(sys, "cbvalivw")
    hyp = lb.hyp("cbvalivw.1", "x = y → ( φ → ψ )")

    # spimvw: (x = y → (φ → ψ)) ⊢ ∀ x φ → ψ
    s1 = lb.ref(
        "s1",
        "∀ x φ → ψ",
        hyp,
        ref="spimvw",
        note="spimvw cbvalivw.1",
    )

    # alrimiv: (∀ x φ → ψ) ⊢ ∀ x φ → ∀ y ψ
    res = lb.ref(
        "res",
        "∀ x φ → ∀ y ψ",
        s1,
        ref="alrimiv",
        note="alrimiv spimvw",
    )

    return lb.build(res)


def prove_cbvaev(sys: System) -> Proof:
    """cbvaev: ∀ x ( x = y ) → ∀ z ( z = y ).

    Change bound variable in an equality with distinct variable
    conditions.  Uses ax7 to derive the hypotheses for cbvalivw,
    then chains the two cbvalivw instances with syl.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "cbvaev")

    # ax7 with x:=x, y:=t, z:=y  →  x = t → ( x = y → t = y )
    s_j = lb.ref(
        "s_j",
        "x = t → ( x = y → t = y )",
        ref="ax7",
        note="ax7 with y:=t, z:=y",
    )

    # cbvalivw: from x = t → (x = y → t = y),
    #   derive ∀ x ( x = y ) → ∀ t ( t = y )
    s_k = lb.ref(
        "s_k",
        "∀ x ( x = y ) → ∀ t ( t = y )",
        s_j,
        ref="cbvalivw",
        note="cbvalivw",
    )

    # ax7 with x:=t, y:=z, z:=y  →  t = z → ( t = y → z = y )
    s_l1 = lb.ref(
        "s_l1",
        "t = z → ( t = y → z = y )",
        ref="ax7",
        note="ax7 with x:=t, y:=z, z:=y",
    )

    # cbvalivw: from t = z → (t = y → z = y),
    #   derive ∀ t ( t = y ) → ∀ z ( z = y )
    s_l = lb.ref(
        "s_l",
        "∀ t ( t = y ) → ∀ z ( z = y )",
        s_l1,
        ref="cbvalivw",
        note="cbvalivw",
    )

    # syl: from ∀x(x=y) → ∀t(t=y) and ∀t(t=y) → ∀z(z=y),
    #   derive ∀x(x=y) → ∀z(z=y)
    res = lb.ref(
        "res",
        "∀ x ( x = y ) → ∀ z ( z = y )",
        s_k,
        s_l,
        ref="syl",
        note="syl",
    )

    return lb.build(res)


def prove_cbvalvw(sys: System) -> Proof:
    """cbvalvw: ( ∀ x φ ↔ ∀ y ψ ).

    Change bound variable using distinct variable conditions.
    Uses ax-5 to derive the non-freeness conditions needed by cbvalw.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wal ax-5 wn cbvalw.
    """
    lb = ProofBuilder(sys, "cbvalvw")
    hyp = lb.hyp("cbvalvw.1", "x = y → ( φ ↔ ψ )")

    # ax-5 with ph := ∀ x φ, x := y: ∀ x φ → ∀ y ∀ x φ
    s1 = lb.ref(
        "s1",
        "∀ x φ → ∀ y ∀ x φ",
        ref="ax-5",
        note="ax-5 with ph := ∀x φ, x := y",
    )
    # ax-5 with ph := ¬ ψ: ¬ ψ → ∀ x ¬ ψ
    s2 = lb.ref(
        "s2",
        "¬ ψ → ∀ x ¬ ψ",
        ref="ax-5",
        note="ax-5 with ph := ¬ ψ",
    )
    # ax-5 with ph := ∀ y ψ: ∀ y ψ → ∀ x ∀ y ψ
    s3 = lb.ref(
        "s3",
        "∀ y ψ → ∀ x ∀ y ψ",
        ref="ax-5",
        note="ax-5 with ph := ∀y ψ",
    )
    # ax-5 with ph := ¬ φ, x := y: ¬ φ → ∀ y ¬ φ
    s4 = lb.ref(
        "s4",
        "¬ φ → ∀ y ¬ φ",
        ref="ax-5",
        note="ax-5 with ph := ¬ φ, x := y",
    )
    # cbvalw with the 5 hypotheses
    res = lb.ref(
        "res",
        "( ∀ x φ ↔ ∀ y ψ )",
        s1,
        s2,
        s3,
        s4,
        hyp,
        ref="cbvalw",
        note="cbvalw",
    )
    return lb.build(res)


def prove_cbvexvw(sys: System) -> Proof:
    """cbvexvw: ( ∃ x φ ↔ ∃ y ψ ).

    Change bound variable in an existential quantifier.
    Derived from cbvalvw by negating both sides and applying df-ex.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "cbvexvw")
    hyp = lb.hyp("cbvexvw.1", "x = y → ( φ ↔ ψ )")

    # notbid: ( φ ↔ ψ ) → ( ¬ φ ↔ ¬ ψ )
    # Combined with hyp via syl gives: x = y → ( ¬ φ ↔ ¬ ψ )
    s1 = lb.ref(
        "s1",
        "x = y → ( ¬ φ ↔ ¬ ψ )",
        hyp,
        ref="notbid",
        note="notbid cbvexvw.1",
    )

    # cbvalvw with ¬ φ, ¬ ψ: ( ∀ x ¬ φ ↔ ∀ y ¬ ψ )
    s2 = lb.ref(
        "s2",
        "( ∀ x ¬ φ ↔ ∀ y ¬ ψ )",
        s1,
        ref="cbvalvw",
        note="cbvalvw",
    )

    # notbii: ( ¬ ∀ x ¬ φ ↔ ¬ ∀ y ¬ ψ )
    s3 = lb.ref(
        "s3",
        "( ¬ ∀ x ¬ φ ↔ ¬ ∀ y ¬ ψ )",
        s2,
        ref="notbii",
        note="notbii",
    )

    # df-ex: ( ∃ x φ ↔ ¬ ∀ x ¬ φ )
    s4 = lb.ref(
        "s4",
        "( ∃ x φ ↔ ¬ ∀ x ¬ φ )",
        ref="df-ex",
        note="df-ex",
    )

    # df-ex: ( ∃ y ψ ↔ ¬ ∀ y ¬ ψ )
    s5 = lb.ref(
        "s5",
        "( ∃ y ψ ↔ ¬ ∀ y ¬ ψ )",
        ref="df-ex",
        note="df-ex",
    )

    s6 = lb.ref(
        "s6",
        "( ¬ ∀ y ¬ ψ ↔ ∃ y ψ )",
        s5,
        ref="bicomi",
        note="bicomi df-ex",
    )
    s7 = lb.ref(
        "s7",
        "( ∃ x φ ↔ ¬ ∀ y ¬ ψ )",
        s4,
        s3,
        ref="bitri",
        note="bitri df-ex, notbii",
    )
    res = lb.ref(
        "res",
        "( ∃ x φ ↔ ∃ y ψ )",
        s7,
        s6,
        ref="bitri",
        note="bitri chain, bicomi",
    )

    return lb.build(res)


def prove_cbvmovw(sys: System) -> Proof:
    """cbvmovw: ( ∃* x φ ↔ ∃* y ψ ).

    Change bound variable in an "exists at most one" quantifier.
    From equequ1, imbi12d, cbvalvw, exbii, dfmo, and 3bitr4i.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "cbvmovw")
    hyp = lb.hyp("cbvmovw.1", "x = y → ( φ ↔ ψ )")

    # equequ1: x = y → ( x = z ↔ y = z )
    s1 = lb.ref(
        "s1",
        "x = y → ( x = z ↔ y = z )",
        ref="equequ1",
        note="equequ1",
    )

    # imbi12d: x = y → ( ( φ → x = z ) ↔ ( ψ → y = z ) )
    s2 = lb.ref(
        "s2",
        "x = y → ( ( φ → x = z ) ↔ ( ψ → y = z ) )",
        hyp,
        s1,
        ref="imbi12d",
        note="imbi12d",
    )

    # cbvalvw: ( ∀ x ( φ → x = z ) ↔ ∀ y ( ψ → y = z ) )
    s3 = lb.ref(
        "s3",
        "( ∀ x ( φ → x = z ) ↔ ∀ y ( ψ → y = z ) )",
        s2,
        ref="cbvalvw",
        note="cbvalvw",
    )

    # exbii: ( ∃ z ∀ x ( φ → x = z ) ↔ ∃ z ∀ y ( ψ → y = z ) )
    s4 = lb.ref(
        "s4",
        "( ∃ z ∀ x ( φ → x = z ) ↔ ∃ z ∀ y ( ψ → y = z ) )",
        s3,
        ref="exbii",
        note="exbii",
    )

    # dfmo: ∃* x φ ↔ ∃ z ∀ x ( φ → x = z )
    s5 = lb.ref(
        "s5",
        "∃* x φ ↔ ∃ z ∀ x ( φ → x = z )",
        ref="dfmo",
        note="dfmo",
    )

    # dfmo: ∃* y ψ ↔ ∃ z ∀ y ( ψ → y = z )
    s6 = lb.ref(
        "s6",
        "∃* y ψ ↔ ∃ z ∀ y ( ψ → y = z )",
        ref="dfmo",
        note="dfmo",
    )

    # 3bitr4i: ( ∃* x φ ↔ ∃* y ψ )
    res = lb.ref(
        "res",
        "( ∃* x φ ↔ ∃* y ψ )",
        s4,
        s5,
        s6,
        ref="3bitr4i",
        note="3bitr4i",
    )

    return lb.build(res)


def prove_mojust(sys: System) -> Proof:
    """mojust: ( ∃ y ∀ x ( φ → x = y ) ↔ ∃ z ∀ x ( φ → x = z ) ).

    Change bound variable in an existential quantifier with equality.
    From equequ2, imbi2d, albidv, and cbvexvw.
    (Contributed by NM, 10-Jan-1993.)
    set.mm proof: weq wi wal equequ2 imbi2d albidv cbvexvw.
    """
    lb = ProofBuilder(sys, "mojust")
    # equequ2: y = z → ( x = y ↔ x = z )
    s1 = lb.ref(
        "s1",
        "y = z → ( x = y ↔ x = z )",
        ref="equequ2",
        note="equequ2",
    )
    # imbi2d: y = z → ( ( φ → x = y ) ↔ ( φ → x = z ) )
    s2 = lb.ref(
        "s2",
        "y = z → ( ( φ → x = y ) ↔ ( φ → x = z ) )",
        s1,
        ref="imbi2d",
        note="imbi2d",
    )
    # albidv: y = z → ( ∀ x ( φ → x = y ) ↔ ∀ x ( φ → x = z ) )
    s3 = lb.ref(
        "s3",
        "y = z → ( ∀ x ( φ → x = y ) ↔ ∀ x ( φ → x = z ) )",
        s2,
        ref="albidv",
        note="albidv",
    )
    # cbvexvw: ( ∃ y ∀ x ( φ → x = y ) ↔ ∃ z ∀ x ( φ → x = z ) )
    res = lb.ref(
        "res",
        "( ∃ y ∀ x ( φ → x = y ) ↔ ∃ z ∀ x ( φ → x = z ) )",
        s3,
        ref="cbvexvw",
        note="cbvexvw",
    )
    return lb.build(res)


def prove_eujust(sys: System) -> Proof:
    """eujust: ( ∃ y ∀ x ( φ ↔ x = y ) ↔ ∃ z ∀ x ( φ ↔ x = z ) ).

    Change bound variable in an existential quantifier with equality and
    biconditional. From equequ2, bibi2d, albidv, and cbvexvw.
    (Contributed by NM, 10-Jan-1993.)
    set.mm proof: weq wb wal wex equequ2 bibi2d albidv cbvexvw bitri.
    """
    lb = ProofBuilder(sys, "eujust")
    # Follow set.mm through the fresh intermediate variable w.  Going directly
    # from y to z would incorrectly require y and z to be disjoint.
    s1 = lb.ref(
        "s1",
        "y = w → ( x = y ↔ x = w )",
        ref="equequ2",
        note="equequ2",
    )
    s2 = lb.ref(
        "s2",
        "y = w → ( ( φ ↔ x = y ) ↔ ( φ ↔ x = w ) )",
        s1,
        ref="bibi2d",
        note="bibi2d",
    )
    s3 = lb.ref(
        "s3",
        "y = w → ( ∀ x ( φ ↔ x = y ) ↔ ∀ x ( φ ↔ x = w ) )",
        s2,
        ref="albidv",
        note="albidv",
    )
    s4 = lb.ref(
        "s4",
        "( ∃ y ∀ x ( φ ↔ x = y ) ↔ ∃ w ∀ x ( φ ↔ x = w ) )",
        s3,
        ref="cbvexvw",
        note="cbvexvw",
    )
    s5 = lb.ref("s5", "w = z → ( x = w ↔ x = z )", ref="equequ2", note="equequ2")
    s6 = lb.ref(
        "s6",
        "w = z → ( ( φ ↔ x = w ) ↔ ( φ ↔ x = z ) )",
        s5,
        ref="bibi2d",
        note="bibi2d",
    )
    s7 = lb.ref(
        "s7",
        "w = z → ( ∀ x ( φ ↔ x = w ) ↔ ∀ x ( φ ↔ x = z ) )",
        s6,
        ref="albidv",
        note="albidv",
    )
    s8 = lb.ref(
        "s8",
        "( ∃ w ∀ x ( φ ↔ x = w ) ↔ ∃ z ∀ x ( φ ↔ x = z ) )",
        s7,
        ref="cbvexvw",
        note="cbvexvw",
    )
    res = lb.ref(
        "res",
        "( ∃ y ∀ x ( φ ↔ x = y ) ↔ ∃ z ∀ x ( φ ↔ x = z ) )",
        s4,
        s8,
        ref="bitri",
        note="bitri",
    )
    return lb.build(res)


def prove_stdpc6(sys: System) -> Proof:
    """stdpc6: ∀ x x = x.
    From equid (reflexivity of equality), generalize with ax-gen.
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: weq equid ax-gen.
    """
    lb = ProofBuilder(sys, "stdpc6")
    # equid: x = x
    s1 = lb.ref("s1", "x = x", ref="equid", note="equid")
    # ax-gen: generalize to ∀ x x = x
    res = lb.ref("res", "∀ x x = x", s1, ref="ax-gen", note="ax-gen")
    return lb.build(res)


def prove_stdpc7(sys: System) -> Proof:
    """stdpc7: x = y → ( [ x / y ] φ → φ ).

    An equality theorem for substitution.
    (Contributed by NM, 16-May-1993.)
    set.mm proof: wsb wi sbequ2 equcoms.
    """
    lb = ProofBuilder(sys, "stdpc7")
    # sbequ2 with x:=y, t:=x: y = x → ( [ x / y ] φ → φ )
    s1 = lb.ref(
        "s1",
        "y = x → ( [ x / y ] φ → φ )",
        ref="sbequ2",
        note="sbequ2 with x:=y, t:=x",
    )
    # equcoms: from y = x → φ derive x = y → φ
    res = lb.ref(
        "res",
        "x = y → ( [ x / y ] φ → φ )",
        s1,
        ref="equcoms",
        note="equcoms",
    )
    return lb.build(res)


def prove_19_27v(sys: System) -> Proof:
    """19.27v: ∀ x ( φ ∧ ψ ) ↔ ( ∀ x φ ∧ ψ ).

    Distribution of universal quantifier over conjunction with a
    free-variable conjunct (right conjunct form).
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wa wal 19.26 19.3v anbi2i bitri.
    """
    lb = ProofBuilder(sys, "19.27v")
    # 19.26: ∀ x ( φ ∧ ψ ) ↔ ( ∀ x φ ∧ ∀ x ψ )
    s1 = lb.ref(
        "s1",
        "∀ x ( φ ∧ ψ ) ↔ ( ∀ x φ ∧ ∀ x ψ )",
        ref="19.26",
        note="19.26",
    )
    # 19.3v: ∀ x ψ ↔ ψ
    s2 = lb.ref(
        "s2",
        "∀ x ψ ↔ ψ",
        ref="19.3v",
        note="19.3v",
    )
    # anbi2i: from s2, derive ( ∀ x φ ∧ ∀ x ψ ) ↔ ( ∀ x φ ∧ ψ )
    s3 = lb.ref(
        "s3",
        "( ∀ x φ ∧ ∀ x ψ ) ↔ ( ∀ x φ ∧ ψ )",
        s2,
        ref="anbi2i",
        note="anbi2i 19.3v",
    )
    # bitri: from s1 and s3, derive ∀ x ( φ ∧ ψ ) ↔ ( ∀ x φ ∧ ψ )
    res = lb.ref(
        "res",
        "∀ x ( φ ∧ ψ ) ↔ ( ∀ x φ ∧ ψ )",
        s1,
        s3,
        ref="bitri",
        note="bitri 19.26, anbi2i",
    )
    return lb.build(res)


def prove_19_28v(sys: System) -> Proof:
    """19.28v: ∀ x ( φ ∧ ψ ) ↔ ( φ ∧ ∀ x ψ ).

    Distribution of universal quantifier over conjunction with a
    free-variable conjunct.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wa wal 19.26 19.3v bianbi.
    """
    lb = ProofBuilder(sys, "19.28v")
    # 19.26: ∀ x ( φ ∧ ψ ) ↔ ( ∀ x φ ∧ ∀ x ψ )
    s1 = lb.ref(
        "s1",
        "∀ x ( φ ∧ ψ ) ↔ ( ∀ x φ ∧ ∀ x ψ )",
        ref="19.26",
        note="19.26",
    )
    # 19.3v: ∀ x φ ↔ φ
    s2 = lb.ref(
        "s2",
        "∀ x φ ↔ φ",
        ref="19.3v",
        note="19.3v",
    )
    # bianbi: from s1 and s2, derive ∀ x ( φ ∧ ψ ) ↔ ( φ ∧ ∀ x ψ )
    res = lb.ref(
        "res",
        "∀ x ( φ ∧ ψ ) ↔ ( φ ∧ ∀ x ψ )",
        s1,
        s2,
        ref="bianbi",
        note="bianbi",
    )
    return lb.build(res)


def prove_spw(sys: System) -> Proof:
    """spw: ∀ x φ → φ.

    Universal specialization with distinct variable conditions.
    Uses spfw with ax-5 (ax-5) to satisfy the not-free hypotheses.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "spw")
    hyp = lb.hyp("spw.1", "x = y → ( φ ↔ ψ )")

    # ax-5: ¬ ψ → ∀ x ¬ ψ  (satisfies spfw.1)
    s1 = lb.ref(
        "s1",
        "¬ ψ → ∀ x ¬ ψ",
        ref="ax-5",
        note="ax-5 — ¬ ψ",
    )

    # ax-5: ∀ x φ → ∀ y ∀ x φ  (satisfies spfw.2)
    s2 = lb.ref(
        "s2",
        "∀ x φ → ∀ y ∀ x φ",
        ref="ax-5",
        note="ax-5 — ∀ x φ",
    )

    # ax-5: ¬ φ → ∀ y ¬ φ  (satisfies spfw.3)
    s3 = lb.ref(
        "s3",
        "¬ φ → ∀ y ¬ φ",
        ref="ax-5",
        note="ax-5 — ¬ φ",
    )

    # spfw: (¬ ψ → ∀ x ¬ ψ), (∀ x φ → ∀ y ∀ x φ), (¬ φ → ∀ y ¬ φ),
    #        (x = y → ( φ ↔ ψ )) ⊢ ∀ x φ → φ
    res = lb.ref(
        "res",
        "∀ x φ → φ",
        s1,
        s2,
        s3,
        hyp,
        ref="spfw",
        note="spfw",
    )

    return lb.build(res)


def prove_19_8aw(sys: System) -> Proof:
    """19.8aw: φ → ∃ x φ.

    Weak version of 19.8a with a distinct variable condition.
    Uses notbid to negate the hypothesis, spw to derive
    ∀ x ¬ φ → ¬ φ, alnex for the biconditional, sylbir to
    combine, and con4i to contraposit.
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "19.8aw")
    hyp = lb.hyp("19.8aw.1", "x = y → ( φ ↔ ψ )")

    # notbid on 19.8aw.1: x = y → ( ¬ φ ↔ ¬ ψ )
    s1 = lb.ref(
        "s1",
        "x = y → ( ¬ φ ↔ ¬ ψ )",
        hyp,
        ref="notbid",
        note="notbid 19.8aw.1",
    )

    # spw with s1: ∀ x ¬ φ → ¬ φ
    s2 = lb.ref(
        "s2",
        "∀ x ¬ φ → ¬ φ",
        s1,
        ref="spw",
        note="spw notbid",
    )

    # alnex: ∀ x ¬ φ ↔ ¬ ∃ x φ
    s3 = lb.ref(
        "s3",
        "∀ x ¬ φ ↔ ¬ ∃ x φ",
        ref="alnex",
        note="alnex",
    )

    # sylbir: from alnex (biconditional) and spw (implication),
    #   deduce ¬ ∃ x φ → ¬ φ
    s4 = lb.ref(
        "s4",
        "¬ ∃ x φ → ¬ φ",
        s3,
        s2,
        ref="sylbir",
        note="sylbir alnex, spw",
    )

    # con4i: from ¬ ∃ x φ → ¬ φ, deduce φ → ∃ x φ
    res = lb.ref(
        "res",
        "φ → ∃ x φ",
        s4,
        ref="con4i",
        note="con4i sylbir",
    )

    return lb.build(res)


def prove_spaev(sys: System) -> Proof:
    """spaev: ∀ x ( x = y ) → ( x = y ).

    Universal specialization of an equality with a distinct variable condition.
    From equequ1 and spw.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: vz weq equequ1 spw.
    """
    lb = ProofBuilder(sys, "spaev")

    # equequ1: x = z → ( x = y ↔ z = y )
    s1 = lb.ref(
        "s1",
        "x = z → ( x = y ↔ z = y )",
        ref="equequ1",
        note="equequ1",
    )

    # spw with s1: ∀ x ( x = y ) → ( x = y )
    res = lb.ref(
        "res",
        "∀ x ( x = y ) → ( x = y )",
        s1,
        ref="spw",
        note="spw equequ1",
    )

    return lb.build(res)


def prove_aevlem0(sys: System) -> Proof:
    """aevlem0: ∀ x ( x = y ) → ∀ z ( z = x ).

    Change the first variable in a universally quantified equality with
    distinct variable conditions.  From spaev and cbvaev, the antecedent
    ∀ x ( x = y ) implies both ∀ z ( x = y ) (via alrimiv) and
    ∀ z ( z = y ); equeuclr gives x = y → ( z = y → z = x ), which after
    al2imi yields the nested implication connecting those consequents,
    and sylc combines all three.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: weq wal spaev alrimiv cbvaev equeuclr al2imi sylc.
    """
    lb = ProofBuilder(sys, "aevlem0")

    # spaev: ∀ x ( x = y ) → ( x = y )
    s1 = lb.ref(
        "s1",
        "∀ x ( x = y ) → ( x = y )",
        ref="spaev",
        note="spaev",
    )

    # alrimiv with variable z: ∀ x ( x = y ) → ∀ z ( x = y )
    s2 = lb.ref(
        "s2",
        "∀ x ( x = y ) → ∀ z ( x = y )",
        s1,
        ref="alrimiv",
        note="alrimiv spaev",
    )

    # cbvaev: ∀ x ( x = y ) → ∀ z ( z = y )
    s3 = lb.ref(
        "s3",
        "∀ x ( x = y ) → ∀ z ( z = y )",
        ref="cbvaev",
        note="cbvaev",
    )

    # equeuclr with y:=z, z:=y: x = y → ( z = y → z = x )
    s4 = lb.ref(
        "s4",
        "x = y → ( z = y → z = x )",
        ref="equeuclr",
        note="equeuclr with y:=z, z:=y",
    )

    # al2imi with variable z: ∀ z ( x = y ) → ( ∀ z ( z = y ) → ∀ z ( z = x ) )
    s5 = lb.ref(
        "s5",
        "∀ z ( x = y ) → ( ∀ z ( z = y ) → ∀ z ( z = x ) )",
        s4,
        ref="al2imi",
        note="al2imi equeuclr",
    )

    # sylc: (φ → ψ), (φ → χ), (ψ → (χ → θ)) ⊢ (φ → θ)
    # with φ := ∀ x (x = y), ψ := ∀ z (x = y),
    #      χ := ∀ z (z = y), θ := ∀ z (z = x)
    res = lb.ref(
        "res",
        "∀ x ( x = y ) → ∀ z ( z = x )",
        s2,
        s3,
        s5,
        ref="sylc",
        note="sylc alrimiv, cbvaev, al2imi",
    )

    return lb.build(res)


def prove_aevlem(sys: System) -> Proof:
    """aevlem: ∀ x ( x = y ) → ∀ z ( z = t ).

    Lemma for aev.  From cbvaev we get ∀ x (x = y) → ∀ t (t = y), then
    aevlem0 gives ∀ t (t = y) → ∀ z (z = t); syl chains them.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "aevlem")

    # This is the four-link chain in set.mm.  Both middle changes of bound
    # variable are needed: the shorter-looking chain does not preserve the
    # source proof's DV instantiations.
    s1 = lb.ref(
        "s1",
        "∀ x ( x = y ) → ∀ u ( u = y )",
        ref="cbvaev",
        note="cbvaev",
    )

    s2 = lb.ref(
        "s2",
        "∀ u ( u = y ) → ∀ x ( x = u )",
        ref="aevlem0",
        note="aevlem0",
    )

    s3 = lb.ref(
        "s3",
        "∀ x ( x = u ) → ∀ t ( t = u )",
        ref="cbvaev",
        note="cbvaev",
    )

    s4 = lb.ref(
        "s4",
        "∀ t ( t = u ) → ∀ z ( z = t )",
        ref="aevlem0",
        note="aevlem0",
    )

    res = lb.ref(
        "res",
        "∀ x ( x = y ) → ∀ z ( z = t )",
        s1,
        s2,
        s3,
        s4,
        ref="4syl",
        note="4syl cbvaev, aevlem0, cbvaev, aevlem0",
    )

    return lb.build(res)


def prove_aeveq(sys: System) -> Proof:
    """aeveq: ∀ x ( x = y ) → z = t.

    Lemma for aev.  From aevlem, ∀ x ( x = y ) implies ∀ u ( u = z );
    then ax7, aleximi, ax6ev, and mpi give ∀ u ( u = z ) → ∃ u ( z = t );
    ax5e drops the existential; 3syl chains everything.
    """
    lb = ProofBuilder(sys, "aeveq")

    # aevlem with z → u, t → z: ∀ x ( x = y ) → ∀ u ( u = z )
    s1 = lb.ref(
        "s1",
        "∀ x ( x = y ) → ∀ u ( u = z )",
        ref="aevlem",
        note="aevlem",
    )

    # ax7 with x → u, y → z, z → t: u = z → ( u = t → z = t )
    s2 = lb.ref(
        "s2",
        "u = z → ( u = t → z = t )",
        ref="ax7",
        note="ax7",
    )

    # aleximi on ax7 with variable u: ∀ u ( u = z ) → ( ∃ u ( u = t ) → ∃ u ( z = t ) )
    s3 = lb.ref(
        "s3",
        "∀ u ( u = z ) → ( ∃ u ( u = t ) → ∃ u ( z = t ) )",
        s2,
        ref="aleximi",
        note="aleximi ax7",
    )

    # ax6ev with x → u, y → t: ∃ u ( u = t )
    s4 = lb.ref(
        "s4",
        "∃ u ( u = t )",
        ref="ax6ev",
        note="ax6ev",
    )

    # mpi: from ∃ u ( u = t ) and ∀ u ( u = z ) → ( ∃ u ( u = t ) → ∃ u ( z = t ) )
    s5 = lb.ref(
        "s5",
        "∀ u ( u = z ) → ∃ u ( z = t )",
        s4,
        s3,
        ref="mpi",
        note="mpi ax6ev, aleximi",
    )

    # ax5e with x → u, φ → ( z = t ): ∃ u ( z = t ) → z = t
    s6 = lb.ref(
        "s6",
        "∃ u ( z = t ) → z = t",
        ref="ax5e",
        note="ax5e",
    )

    # 3syl: chain s1, s5, s6
    res = lb.ref(
        "res",
        "∀ x ( x = y ) → z = t",
        s1,
        s5,
        s6,
        ref="3syl",
        note="3syl",
    )

    return lb.build(res)


def prove_aev(sys: System) -> Proof:
    """aev: ∀ x ( x = y ) → ∀ z ( t = u ).

    Lemma for aev.  From aevlem we get ∀ x ( x = y ) → ∀ w ( w = v );
    aeveq gives ∀ w ( w = v ) → t = u; alrimiv generalizes to
    ∀ w ( w = v ) → ∀ z ( t = u ); syl chains everything.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "aev")

    # aevlem with z := w, w := v: ∀ x ( x = y ) → ∀ w ( w = v )
    s1 = lb.ref(
        "s1",
        "∀ x ( x = y ) → ∀ w ( w = v )",
        ref="aevlem",
        note="aevlem",
    )

    # aeveq with x := w, y := v, z := t, t := u: ∀ w ( w = v ) → t = u
    s2 = lb.ref(
        "s2",
        "∀ w ( w = v ) → t = u",
        ref="aeveq",
        note="aeveq",
    )

    # alrimiv on s2: generalize over z
    #   ∀ w ( w = v ) → ∀ z ( t = u )
    s3 = lb.ref(
        "s3",
        "∀ w ( w = v ) → ∀ z ( t = u )",
        s2,
        ref="alrimiv",
        note="alrimiv aeveq",
    )

    # syl: chain s1 and s3
    res = lb.ref(
        "res",
        "∀ x ( x = y ) → ∀ z ( t = u )",
        s1,
        s3,
        ref="syl",
        note="syl aevlem, alrimiv",
    )

    return lb.build(res)


def prove_aev2(sys: System) -> Proof:
    """aev2: ( ∀ x x = y ) → ∀ z ∀ t u = v.

    A variant of aev with an additional universal quantifier.
    From aev we get ∀ x ( x = y ) → ∀ t ( u = v ); then alrimiv
    adds the ∀ z quantifier to the consequent.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: weq wal aev alrimiv syl.
    """
    lb = ProofBuilder(sys, "aev2")

    # Follow set.mm through its two dummy variables w and s.  Using alrimiv
    # directly would impose non-source DV conditions on z and the antecedent.
    s1 = lb.ref(
        "s1",
        "∀ x ( x = y ) → ∀ w ( w = s )",
        ref="aev",
        note="aev",
    )

    s2 = lb.ref(
        "s2",
        "∀ w ( w = s ) → ∀ t ( u = v )",
        ref="aev",
        note="aev",
    )

    s3 = lb.ref(
        "s3",
        "∀ w ( w = s ) → ∀ z ∀ t ( u = v )",
        s2,
        ref="alrimiv",
        note="alrimiv aev",
    )

    res = lb.ref(
        "res",
        "∀ x ( x = y ) → ∀ z ∀ t ( u = v )",
        s1,
        s3,
        ref="syl",
        note="syl aev, alrimiv",
    )

    return lb.build(res)


def prove_hbaev(sys: System) -> Proof:
    """hbaev: ∀ x ( x = y ) → ∀ z ∀ x ( x = y ).

    Variant of aev2 with the consequent's body variables set to x and y.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "hbaev")
    res = lb.ref(
        "s1",
        "∀ x ( x = y ) → ∀ z ∀ x ( x = y )",
        ref="aev2",
        note="aev2",
    )
    return lb.build(res)


def prove_naev(sys: System) -> Proof:
    """naev: ( ¬ ∀ x x = y → ¬ ∀ u u = v ).

    Contrapositive of aev.
    (Contributed by NM, 8-Nov-1990.)
    """
    lb = ProofBuilder(sys, "naev")

    # aev with x := u, y := v, z := x, t := x, u := y:
    #   ∀ u ( u = v ) → ∀ x ( x = y )
    s1 = lb.ref(
        "s1",
        "∀ u ( u = v ) → ∀ x ( x = y )",
        ref="aev",
        note="aev",
    )

    # con3i: from φ → ψ derive ¬ ψ → ¬ φ
    #   ¬ ∀ x ( x = y ) → ¬ ∀ u ( u = v )
    res = lb.ref(
        "res",
        "¬ ∀ x ( x = y ) → ¬ ∀ u ( u = v )",
        s1,
        ref="con3i",
        note="con3i aev",
    )

    return lb.build(res)


def prove_naev2(sys: System) -> Proof:
    """naev2: ( ¬ ∀ x x = y → ∀ z ¬ ∀ t t = u ).

    Generalize naev with an additional universal quantifier in the
    consequent via ax-5 (n) and alimi, composed with 3syl.
    (Contributed by NM, 8-Nov-1990.)
    """
    lb = ProofBuilder(sys, "naev2")

    # naev with u := v, v := w:
    #   ¬ ∀ x x = y → ¬ ∀ v v = w
    s1 = lb.ref(
        "s1",
        "¬ ∀ x x = y → ¬ ∀ v v = w",
        ref="naev",
        note="naev",
    )

    # ax-5: ¬ ∀ v v = w → ∀ z ¬ ∀ v v = w
    s2 = lb.ref(
        "s2",
        "¬ ∀ v v = w → ∀ z ¬ ∀ v v = w",
        ref="ax-5",
        note="ax-5",
    )

    # naev with x := v, y := w, u := t, v := u:
    #   ¬ ∀ v v = w → ¬ ∀ t t = u
    s3 = lb.ref(
        "s3",
        "¬ ∀ v v = w → ¬ ∀ t t = u",
        ref="naev",
        note="naev",
    )

    # alimi from s3: ∀ z ¬ ∀ v v = w → ∀ z ¬ ∀ t t = u
    s4 = lb.ref(
        "s4",
        "∀ z ¬ ∀ v v = w → ∀ z ¬ ∀ t t = u",
        s3,
        ref="alimi",
        note="alimi",
    )

    # 3syl with s1, s2, s4: ¬ ∀ x x = y → ∀ z ¬ ∀ t t = u
    res = lb.ref(
        "res",
        "¬ ∀ x x = y → ∀ z ¬ ∀ t t = u",
        s1,
        s2,
        s4,
        ref="3syl",
        note="3syl",
    )

    return lb.build(res)


def prove_hbnaev(sys: System) -> Proof:
    """hbnaev: ( ¬ ∀ x x = y → ∀ z ¬ ∀ x x = y ).

    Direct substitution instance of naev2.
    (Contributed by NM, 8-Nov-1990.)
    """
    lb = ProofBuilder(sys, "hbnaev")
    res = lb.ref(
        "res",
        "¬ ∀ x x = y → ∀ z ¬ ∀ x x = y",
        ref="naev2",
        note="naev2",
    )
    return lb.build(res)


def prove_nfnaew(sys: System) -> Proof:
    """nfnaew: Ⅎ z ¬ ∀ x x = y.

    nf5i applied to hbnaev.
    (Contributed by NM, 8-Nov-1990.)
    """
    lb = ProofBuilder(sys, "nfnaew")
    s1 = lb.ref(
        "s1",
        "¬ ∀ x x = y → ∀ z ¬ ∀ x x = y",
        ref="hbnaev",
        note="hbnaev",
    )
    res = lb.ref(
        "res",
        "Ⅎ z ¬ ∀ x x = y",
        s1,
        ref="nf5i",
        note="nf5i hbnaev",
    )
    return lb.build(res)


def prove_cbvaldvaw(sys: System) -> Proof:
    """cbvaldvaw: φ → ( ∀ x ψ ↔ ∀ y χ ).

    Change bound variable in a universal quantifier with a deduction-form
    hypothesis on the body.  From the hypothesis ( φ ∧ x = y ) → ( ψ ↔ χ ),
    commute the conjunction with ancoms, export with pm5.74da, change the
    bound variable with cbvalvw, distribute the quantifier over implication
    with 19.21v, combine biconditionals with 3bitr3i, and finally apply
    pm5.74ri to convert the implication biconditional into the conclusion.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "cbvaldvaw")
    hyp = lb.hyp("cbvaldvaw.1", "( φ ∧ x = y ) → ( ψ ↔ χ )")

    # ancoms: swap the conjunction → ( x = y ∧ φ ) → ( ψ ↔ χ )
    s1 = lb.ref(
        "s1",
        "( x = y ∧ φ ) → ( ψ ↔ χ )",
        hyp,
        ref="ancoms",
        note="ancoms",
    )

    # pm5.74da: export → x = y → ( ( φ → ψ ) ↔ ( φ → χ ) )
    s2 = lb.ref(
        "s2",
        "x = y → ( ( φ → ψ ) ↔ ( φ → χ ) )",
        s1,
        ref="pm5.74da",
        note="pm5.74da",
    )

    # cbvalvw: change bound variable → ( ∀ x ( φ → ψ ) ↔ ∀ y ( φ → χ ) )
    s3 = lb.ref(
        "s3",
        "( ∀ x ( φ → ψ ) ↔ ∀ y ( φ → χ ) )",
        s2,
        ref="cbvalvw",
        note="cbvalvw",
    )

    # 19.21v: distribute universal over implication (x)
    s4 = lb.ref(
        "s4",
        "( ∀ x ( φ → ψ ) ↔ ( φ → ∀ x ψ ) )",
        ref="19.21v",
        note="19.21v",
    )

    # 19.21v: distribute universal over implication (y)
    s5 = lb.ref(
        "s5",
        "( ∀ y ( φ → χ ) ↔ ( φ → ∀ y χ ) )",
        ref="19.21v",
        note="19.21v",
    )

    # 3bitr3i: combine the three biconditionals
    s6 = lb.ref(
        "s6",
        "( ( φ → ∀ x ψ ) ↔ ( φ → ∀ y χ ) )",
        s3,
        s4,
        s5,
        ref="3bitr3i",
        note="3bitr3i",
    )

    # pm5.74ri: convert implication biconditional into conclusion
    res = lb.ref(
        "res",
        "φ → ( ∀ x ψ ↔ ∀ y χ )",
        s6,
        ref="pm5.74ri",
        note="pm5.74ri",
    )

    return lb.build(res)


def prove_cbvexdvaw(sys: System) -> Proof:
    """cbvexdvaw: φ → ( ∃ x ψ ↔ ∃ y χ ).

    Change bound variable in an existential quantifier with a deduction-form
    hypothesis on the body.  From the hypothesis ( φ ∧ x = y ) → ( ψ ↔ χ ),
    negate both sides with notbid, change the bound variable of the negated
    body under a universal quantifier with cbvaldvaw, convert universal
    negation to negated existence via alnex, then chain the biconditionals
    with 3bitr3g and apply con4bid to restore the existential.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "cbvexdvaw")
    hyp = lb.hyp("cbvexdvaw.1", "( φ ∧ x = y ) → ( ψ ↔ χ )")

    # notbid: negate both sides of the hypothesis
    s1 = lb.ref(
        "s1",
        "( φ ∧ x = y ) → ( ¬ ψ ↔ ¬ χ )",
        hyp,
        ref="notbid",
        note="notbid",
    )

    # cbvaldvaw: change bound variable for negated body under universal
    s2 = lb.ref(
        "s2",
        "φ → ( ∀ x ¬ ψ ↔ ∀ y ¬ χ )",
        s1,
        ref="cbvaldvaw",
        note="cbvaldvaw",
    )

    # alnex (with φ := ψ): ( ∀ x ¬ ψ ↔ ¬ ∃ x ψ )
    s3 = lb.ref(
        "s3",
        "∀ x ¬ ψ ↔ ¬ ∃ x ψ",
        ref="alnex",
        note="alnex",
    )

    # alnex (with φ := χ): ( ∀ y ¬ χ ↔ ¬ ∃ y χ )
    s4 = lb.ref(
        "s4",
        "∀ y ¬ χ ↔ ¬ ∃ y χ",
        ref="alnex",
        note="alnex",
    )

    # 3bitr3g: chain the three biconditionals
    s5 = lb.ref(
        "s5",
        "φ → ( ¬ ∃ x ψ ↔ ¬ ∃ y χ )",
        s2,
        s3,
        s4,
        ref="3bitr3g",
        note="3bitr3g",
    )

    # con4bid: restore the existential from the negated biconditional
    res = lb.ref(
        "res",
        "φ → ( ∃ x ψ ↔ ∃ y χ )",
        s5,
        ref="con4bid",
        note="con4bid",
    )

    return lb.build(res)


def prove_cbval2vw(sys: System) -> Proof:
    """cbval2vw: ( ∀ x ∀ y φ ↔ ∀ z ∀ w ψ ).

    Change bound variables in a double universal quantifier.
    From the hypothesis ( x = z ∧ y = w ) → ( φ ↔ ψ ), apply cbvaldvaw
    to change the inner bound variable, then cbvalvw to change the outer
    bound variable.  (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "cbval2vw")
    hyp = lb.hyp("cbval2vw.1", "( x = z ∧ y = w ) → ( φ ↔ ψ )")

    # cbvaldvaw: ( x = z ) → ( ∀ y φ ↔ ∀ w ψ )
    s1 = lb.ref(
        "s1",
        "( x = z ) → ( ∀ y φ ↔ ∀ w ψ )",
        hyp,
        ref="cbvaldvaw",
        note="cbvaldvaw",
    )

    # cbvalvw: ( ∀ x ∀ y φ ↔ ∀ z ∀ w ψ )
    res = lb.ref(
        "res",
        "( ∀ x ∀ y φ ↔ ∀ z ∀ w ψ )",
        s1,
        ref="cbvalvw",
        note="cbvalvw",
    )

    return lb.build(res)


def prove_cbvex2vw(sys: System) -> Proof:
    """cbvex2vw: ( ∃ x ∃ y φ ↔ ∃ z ∃ w ψ ).

    Change bound variables in a double existential quantifier.
    From the hypothesis ( x = z ∧ y = w ) → ( φ ↔ ψ ), apply cbvexdvaw
    to change the inner bound variable, then cbvexvw to change the outer
    bound variable.  (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "cbvex2vw")
    hyp = lb.hyp("cbvex2vw.1", "( x = z ∧ y = w ) → ( φ ↔ ψ )")

    # cbvexdvaw: ( x = z ) → ( ∃ y φ ↔ ∃ w ψ )
    s1 = lb.ref(
        "s1",
        "( x = z ) → ( ∃ y φ ↔ ∃ w ψ )",
        hyp,
        ref="cbvexdvaw",
        note="cbvexdvaw",
    )

    # cbvexvw: ( ∃ x ∃ y φ ↔ ∃ z ∃ w ψ )
    res = lb.ref(
        "res",
        "( ∃ x ∃ y φ ↔ ∃ z ∃ w ψ )",
        s1,
        ref="cbvexvw",
        note="cbvexvw",
    )

    return lb.build(res)


def prove_cbvex4vw(sys: System) -> Proof:
    """cbvex4vw: ( ∃ x ∃ y ∃ z ∃ w φ ↔ ∃ v ∃ u ∃ f ∃ g χ ).

    Change bound variables in a quadruple existential quantifier.
    From two hypotheses relating φ to ψ and ψ to χ under equality
    substitutions, chain cbvex2vw and 2exbii with bitri to rename
    all four bound variables.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wex weq wa 2exbidv cbvex2vw 2exbii bitri.
    """
    lb = ProofBuilder(sys, "cbvex4vw")
    hyp1 = lb.hyp("cbvex4vw.1", "( ( x = v ∧ y = u ) → ( φ ↔ ψ ) )")
    hyp2 = lb.hyp("cbvex4vw.2", "( ( z = f ∧ w = g ) → ( ψ ↔ χ ) )")

    # 2exbidv with cbvex4vw.1: ( ( x = v ∧ y = u ) → ( ∃ z ∃ w φ ↔ ∃ z ∃ w ψ ) )
    s1 = lb.ref(
        "s1",
        "( ( x = v ∧ y = u ) → ( ∃ z ∃ w φ ↔ ∃ z ∃ w ψ ) )",
        hyp1,
        ref="2exbidv",
        note="2exbidv cbvex4vw.1",
    )

    # cbvex2vw with s1: ( ∃ x ∃ y ∃ z ∃ w φ ↔ ∃ v ∃ u ∃ z ∃ w ψ )
    s2 = lb.ref(
        "s2",
        "( ∃ x ∃ y ∃ z ∃ w φ ↔ ∃ v ∃ u ∃ z ∃ w ψ )",
        s1,
        ref="cbvex2vw",
        note="cbvex2vw s1",
    )

    # cbvex2vw with cbvex4vw.2: ( ∃ z ∃ w ψ ↔ ∃ f ∃ g χ )
    s3 = lb.ref(
        "s3",
        "( ∃ z ∃ w ψ ↔ ∃ f ∃ g χ )",
        hyp2,
        ref="cbvex2vw",
        note="cbvex2vw cbvex4vw.2",
    )

    # 2exbii with s3: ( ∃ v ∃ u ∃ z ∃ w ψ ↔ ∃ v ∃ u ∃ f ∃ g χ )
    s4 = lb.ref(
        "s4",
        "( ∃ v ∃ u ∃ z ∃ w ψ ↔ ∃ v ∃ u ∃ f ∃ g χ )",
        s3,
        ref="2exbii",
        note="2exbii s3",
    )

    # bitri with s2 and s4: ( ∃ x ∃ y ∃ z ∃ w φ ↔ ∃ v ∃ u ∃ f ∃ g χ )
    res = lb.ref(
        "res",
        "( ∃ x ∃ y ∃ z ∃ w φ ↔ ∃ v ∃ u ∃ f ∃ g χ )",
        s2,
        s4,
        ref="bitri",
        note="bitri s2, s4",
    )
    return lb.build(res)


def prove_celaront(sys: System) -> Proof:
    """celaront: ∃ x ( χ ∧ ¬ ψ ).

    Syllogism celaront: from ∀ x ( φ → ¬ ψ ), ∀ x ( χ → φ ), and ∃ x χ,
    derive ∃ x ( χ ∧ ¬ ψ ).  (Contributed by NM, 3-Jan-1993.)
    set.mm proof: wn barbari.
    """
    lb = ProofBuilder(sys, "celaront")
    h_maj = lb.hyp("celaront.maj", "∀ x ( φ → ¬ ψ )")
    h_min = lb.hyp("celaront.min", "∀ x ( χ → φ )")
    h_e = lb.hyp("celaront.e", "∃ x χ")
    # celarent: from ∀ x ( χ → φ ) and ∀ x ( φ → ¬ ψ ), derive ∀ x ( χ → ¬ ψ )
    s1 = lb.ref(
        "s1",
        "∀ x ( χ → ¬ ψ )",
        h_maj,
        h_min,
        ref="celarent",
        note="celarent celaront.maj, celaront.min",
    )
    # barbarilem: from ∀ x ( χ → ¬ ψ ) and ∃ x χ, derive ∃ x ( χ ∧ ¬ ψ )
    res = lb.ref(
        "res",
        "∃ x ( χ ∧ ¬ ψ )",
        s1,
        h_e,
        ref="barbarilem",
        note="barbarilem s1, celaront.e",
    )
    return lb.build(res)


def prove_calemos(sys: System) -> Proof:
    """calemos: ∃ x ( χ ∧ ¬ φ ).

    Syllogism calemos: from ∀ x ( φ → ψ ), ∀ x ( ψ → ¬ χ ), and ∃ x χ,
    derive ∃ x ( χ ∧ ¬ φ ).  (Contributed by NM, 3-Jan-1993.)
    set.mm proof: wn calemes barbarilem.
    """
    lb = ProofBuilder(sys, "calemos")
    h_maj = lb.hyp("calemos.maj", "∀ x ( φ → ψ )")
    h_min = lb.hyp("calemos.min", "∀ x ( ψ → ¬ χ )")
    h_e = lb.hyp("calemos.e", "∃ x χ")
    # calemes: from ∀ x ( φ → ψ ) and ∀ x ( ψ → ¬ χ ), derive ∀ x ( χ → ¬ φ )
    s1 = lb.ref(
        "s1",
        "∀ x ( χ → ¬ φ )",
        h_maj,
        h_min,
        ref="calemes",
        note="calemes calemos.maj, calemos.min",
    )
    # barbarilem: from ∀ x ( χ → ¬ φ ) and ∃ x χ, derive ∃ x ( χ ∧ ¬ φ )
    res = lb.ref(
        "res",
        "∃ x ( χ ∧ ¬ φ )",
        s1,
        h_e,
        ref="barbarilem",
        note="barbarilem s1, calemos.e",
    )
    return lb.build(res)


def prove_spsbim(sys: System) -> Proof:
    """spsbim: ∀ x ( φ → ψ ) → ( [ t / x ] φ → [ t / x ] ψ ).

    Substitution distributes over implication.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wi wal wsb stdpc4 sbi1 syl.
    """
    lb = ProofBuilder(sys, "spsbim")
    # stdpc4 with ph := ( φ → ψ ): ∀ x ( φ → ψ ) → [ t x ( φ → ψ )
    s1 = lb.ref(
        "s1",
        "∀ x ( φ → ψ ) → [ t x ( φ → ψ )",
        ref="stdpc4",
        note="stdpc4",
    )
    # sbi1: [ t x ( φ → ψ ) → ( [ t x φ → [ t x ψ )
    s2 = lb.ref(
        "s2",
        "[ t x ( φ → ψ ) → ( [ t x φ → [ t x ψ )",
        ref="sbi1",
        note="sbi1",
    )
    # syl: chain s1 and s2
    res = lb.ref(
        "res",
        "∀ x ( φ → ψ ) → ( [ t x φ → [ t x ψ )",
        s1,
        s2,
        ref="syl",
        note="syl stdpc4, sbi1",
    )
    return lb.build(res)


def prove_spsbbi(sys: System) -> Proof:
    """spsbbi: ∀ x ( φ ↔ ψ ) → ( [ t / x ] φ ↔ [ t / x ] ψ ).

    Substitution distributes over biconditional.
    (Contributed by NM, 3-Jan-1993.)
    set.mm proof: wb wal wsb biimp alimi spsbim syl biimpr impbid.
    """
    lb = ProofBuilder(sys, "spsbbi")
    # biimp: ( φ ↔ ψ ) → ( φ → ψ )
    s1 = lb.ref(
        "s1",
        "( φ ↔ ψ ) → ( φ → ψ )",
        ref="biimp",
        note="biimp",
    )
    # alimi: ∀ x ( φ ↔ ψ ) → ∀ x ( φ → ψ )
    s2 = lb.ref(
        "s2",
        "∀ x ( φ ↔ ψ ) → ∀ x ( φ → ψ )",
        s1,
        ref="alimi",
        note="alimi biimp",
    )
    # spsbim: ∀ x ( φ → ψ ) → ( [ t x φ → [ t x ψ )
    s3 = lb.ref(
        "s3",
        "∀ x ( φ → ψ ) → ( [ t x φ → [ t x ψ )",
        ref="spsbim",
        note="spsbim",
    )
    # syl: chain s2 and s3
    s4 = lb.ref(
        "s4",
        "∀ x ( φ ↔ ψ ) → ( [ t x φ → [ t x ψ )",
        s2,
        s3,
        ref="syl",
        note="syl alimi, spsbim",
    )
    # biimpr: ( φ ↔ ψ ) → ( ψ → φ )
    s5 = lb.ref(
        "s5",
        "( φ ↔ ψ ) → ( ψ → φ )",
        ref="biimpr",
        note="biimpr",
    )
    # alimi: ∀ x ( φ ↔ ψ ) → ∀ x ( ψ → φ )
    s6 = lb.ref(
        "s6",
        "∀ x ( φ ↔ ψ ) → ∀ x ( ψ → φ )",
        s5,
        ref="alimi",
        note="alimi biimpr",
    )
    # spsbim: ∀ x ( ψ → φ ) → ( [ t x ψ → [ t x φ )
    s7 = lb.ref(
        "s7",
        "∀ x ( ψ → φ ) → ( [ t x ψ → [ t x φ )",
        ref="spsbim",
        note="spsbim",
    )
    # syl: chain s6 and s7
    s8 = lb.ref(
        "s8",
        "∀ x ( φ ↔ ψ ) → ( [ t x ψ → [ t x φ )",
        s6,
        s7,
        ref="syl",
        note="syl alimi, spsbim",
    )
    # impbid: combine s4 and s8
    res = lb.ref(
        "res",
        "∀ x ( φ ↔ ψ ) → ( [ t x φ ↔ [ t x ψ )",
        s4,
        s8,
        ref="impbid",
        note="impbid",
    )
    return lb.build(res)


def prove_sbimdv(sys: System) -> Proof:
    """sbimdv: φ → ( [ t / x ] ψ → [ t / x ] χ ).

    Deduction form of spsbim.
    (Contributed by NM, 14-May-1993.)
    set.mm proof: wi wal wsb alrimiv spsbim syl.
    """
    lb = ProofBuilder(sys, "sbimdv")
    hyp = lb.hyp("sbimdv.1", "φ → ( ψ → χ )")
    # alrimiv: φ → A. x ( ψ → χ )
    s1 = lb.ref(
        "s1",
        "φ → ∀ x ( ψ → χ )",
        hyp,
        ref="alrimiv",
        note="alrimiv",
    )
    # spsbim: ∀ x ( ψ → χ ) → ( [ t x ψ → [ t x χ )
    s2 = lb.ref(
        "s2",
        "∀ x ( ψ → χ ) → ( [ t x ψ → [ t x χ )",
        ref="spsbim",
        note="spsbim",
    )
    # syl: chain s1 and s2
    res = lb.ref(
        "res",
        "φ → ( [ t x ψ → [ t x χ )",
        s1,
        s2,
        ref="syl",
        note="syl alrimiv, spsbim",
    )
    return lb.build(res)


def prove_sbimd(sys: System) -> Proof:
    """sbimd: φ → ( [ t / x ] ψ → [ t / x ] χ ).

    Deduction form of spsbim, using the not-free hypothesis.
    (Contributed by NM, 14-May-1993.)
    set.mm proof: wi wal wsb alrimi spsbim syl.
    """
    lb = ProofBuilder(sys, "sbimd")
    hyp1 = lb.hyp("sbimd.1", "Ⅎ x φ")
    hyp2 = lb.hyp("sbimd.2", "φ → ( ψ → χ )")
    # alrimi: Ⅎ x φ, φ → ( ψ → χ ) ⊢ φ → ∀ x ( ψ → χ )
    s1 = lb.ref(
        "s1",
        "φ → ∀ x ( ψ → χ )",
        hyp1,
        hyp2,
        ref="alrimi",
        note="alrimi",
    )
    # spsbim: ∀ x ( ψ → χ ) → ( [ t x ψ → [ t x χ )
    s2 = lb.ref(
        "s2",
        "∀ x ( ψ → χ ) → ( [ t x ψ → [ t x χ )",
        ref="spsbim",
        note="spsbim",
    )
    # syl: chain s1 and s2
    res = lb.ref(
        "res",
        "φ → ( [ t x ψ → [ t x χ )",
        s1,
        s2,
        ref="syl",
        note="syl alrimi, spsbim",
    )
    return lb.build(res)


def prove_sbbidv(sys: System) -> Proof:
    """sbbidv: φ → ( [ t / x ] ψ ↔ [ t / x ] χ ).

    Deduction form of spsbbi.
    (Contributed by NM, 14-May-1993.)
    set.mm proof: wb wal wsb alrimiv spsbbi syl.
    """
    lb = ProofBuilder(sys, "sbbidv")
    hyp = lb.hyp("sbbidv.1", "φ → ( ψ ↔ χ )")
    # alrimiv: φ → ∀ x ( ψ ↔ χ )
    s1 = lb.ref(
        "s1",
        "φ → ∀ x ( ψ ↔ χ )",
        hyp,
        ref="alrimiv",
        note="alrimiv",
    )
    # spsbbi: ∀ x ( ψ ↔ χ ) → ( [ t x ψ ↔ [ t x χ )
    s2 = lb.ref(
        "s2",
        "∀ x ( ψ ↔ χ ) → ( [ t x ψ ↔ [ t x χ )",
        ref="spsbbi",
        note="spsbbi",
    )
    # syl: chain s1 and s2
    res = lb.ref(
        "res",
        "φ → ( [ t x ψ ↔ [ t x χ )",
        s1,
        s2,
        ref="syl",
        note="syl alrimiv, spsbbi",
    )
    return lb.build(res)


def prove_sban(sys: System) -> Proof:
    """sban: [ y / x ] ( φ ∧ ψ ) ↔ ( [ y / x ] φ ∧ [ y / x ] ψ ).

    Substitution distributes over conjunction.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wa wsb simpl sbimi simpr jca pm3.2 sb2imi imp impbii.
    """
    lb = ProofBuilder(sys, "sban")
    # simpl: ( φ ∧ ψ ) → φ
    s_simpl = lb.ref(
        "s_simpl",
        "( φ ∧ ψ ) → φ",
        ref="simpl",
        note="simpl",
    )
    # sbimi from simpl: [ y / x ] ( φ ∧ ψ ) → [ y / x ] φ
    s_fwd1 = lb.ref(
        "s_fwd1",
        "( [ y x ( φ ∧ ψ ) → [ y x φ )",
        s_simpl,
        ref="sbimi",
        note="sbimi simpl",
    )
    # simpr: ( φ ∧ ψ ) → ψ
    s_simpr = lb.ref(
        "s_simpr",
        "( φ ∧ ψ ) → ψ",
        ref="simpr",
        note="simpr",
    )
    # sbimi from simpr: [ y / x ] ( φ ∧ ψ ) → [ y / x ] ψ
    s_fwd2 = lb.ref(
        "s_fwd2",
        "( [ y x ( φ ∧ ψ ) → [ y x ψ )",
        s_simpr,
        ref="sbimi",
        note="sbimi simpr",
    )
    # jca from fwd1 and fwd2: [ y / x ] ( φ ∧ ψ ) → ( [ y / x ] φ ∧ [ y / x ] ψ )
    s_fwd = lb.ref(
        "s_fwd",
        "( [ y x ( φ ∧ ψ ) → ( [ y x φ ∧ [ y x ψ ) )",
        s_fwd1,
        s_fwd2,
        ref="jca",
        note="jca",
    )
    # pm3.2: φ → ( ψ → ( φ ∧ ψ ) )
    s_pm32 = lb.ref(
        "s_pm32",
        "φ → ( ψ → ( φ ∧ ψ ) )",
        ref="pm3.2",
        note="pm3.2",
    )
    # sb2imi from pm3.2: [ y / x ] φ → ( [ y / x ] ψ → [ y / x ] ( φ ∧ ψ ) )
    s_rev1 = lb.ref(
        "s_rev1",
        "( [ y x φ → ( [ y x ψ → [ y x ( φ ∧ ψ ) ) )",
        s_pm32,
        ref="sb2imi",
        note="sb2imi pm3.2",
    )
    # imp from rev1: ( [ y / x ] φ ∧ [ y / x ] ψ ) → [ y / x ] ( φ ∧ ψ )
    s_rev = lb.ref(
        "s_rev",
        "( ( [ y x φ ∧ [ y x ψ ) → [ y x ( φ ∧ ψ ) )",
        s_rev1,
        ref="imp",
        note="imp",
    )
    # impbii from fwd and rev: final biconditional
    res = lb.ref(
        "res",
        "( [ y x ( φ ∧ ψ ) ↔ ( [ y x φ ∧ [ y x ψ ) )",
        s_fwd,
        s_rev,
        ref="impbii",
        note="impbii",
    )
    return lb.build(res)


def prove_sb3an(sys: System) -> Proof:
    """sb3an: [ y / x ] ( φ ∧ ψ ∧ χ ) ↔ ( [ y / x ] φ ∧ [ y / x ] ψ ∧ [ y / x ] χ ).

    Substitution distributes over ternary conjunction.
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wa wsb w3a sban anbi1i df-3an sbbii bitri 3bitr4i.
    """
    lb = ProofBuilder(sys, "sb3an")

    # df-3an: ( φ ∧ ψ ∧ χ ) ↔ ( ( φ ∧ ψ ) ∧ χ )
    s1 = lb.ref(
        "s1",
        "( φ ∧ ψ ∧ χ ) ↔ ( ( φ ∧ ψ ) ∧ χ )",
        ref="df-3an",
        note="df-3an",
    )

    # sbbii with s1: [ y / x ] ( φ ∧ ψ ∧ χ ) ↔ [ y / x ] ( ( φ ∧ ψ ) ∧ χ )
    s2 = lb.ref(
        "s2",
        "( [ y x ( φ ∧ ψ ∧ χ ) ↔ [ y x ( ( φ ∧ ψ ) ∧ χ ) )",
        s1,
        ref="sbbii",
        note="sbbii",
    )

    # sban with ( ( φ ∧ ψ ), χ ): [ y / x ] ( ( φ ∧ ψ ) ∧ χ ) ↔ ( [ y / x ] ( φ ∧ ψ ) ∧ [ y / x ] χ )
    s3 = lb.ref(
        "s3",
        "( [ y x ( ( φ ∧ ψ ) ∧ χ ) ↔ ( [ y x ( φ ∧ ψ ) ∧ [ y x χ ) )",
        ref="sban",
        note="sban",
    )

    # sban with ( φ, ψ ): [ y / x ] ( φ ∧ ψ ) ↔ ( [ y / x ] φ ∧ [ y / x ] ψ )
    s4 = lb.ref(
        "s4",
        "( [ y x ( φ ∧ ψ ) ↔ ( [ y x φ ∧ [ y x ψ ) )",
        ref="sban",
        note="sban",
    )

    # anbi1i with s4 and [ y / x ] χ
    s5 = lb.ref(
        "s5",
        "( ( [ y x ( φ ∧ ψ ) ∧ [ y x χ ) ↔ ( ( [ y x φ ∧ [ y x ψ ) ∧ [ y x χ ) )",
        s4,
        ref="anbi1i",
        note="anbi1i",
    )

    # bitri s3, s5: [ y / x ] ( ( φ ∧ ψ ) ∧ χ ) ↔ ( ( [ y / x ] φ ∧ [ y / x ] ψ ) ∧ [ y / x ] χ )
    s6 = lb.ref(
        "s6",
        "( [ y x ( ( φ ∧ ψ ) ∧ χ ) ↔ ( ( [ y x φ ∧ [ y x ψ ) ∧ [ y x χ ) )",
        s3,
        s5,
        ref="bitri",
        note="bitri",
    )

    # bitri s2, s6: [ y / x ] ( φ ∧ ψ ∧ χ ) ↔ ( ( [ y / x ] φ ∧ [ y / x ] ψ ) ∧ [ y / x ] χ )
    s7 = lb.ref(
        "s7",
        "( [ y x ( φ ∧ ψ ∧ χ ) ↔ ( ( [ y x φ ∧ [ y x ψ ) ∧ [ y x χ ) )",
        s2,
        s6,
        ref="bitri",
        note="bitri",
    )

    # df-3an with substituted vars
    s8 = lb.ref(
        "s8",
        "( ( [ y x φ ∧ [ y x ψ ∧ [ y x χ ) ↔ ( ( [ y x φ ∧ [ y x ψ ) ∧ [ y x χ ) )",
        ref="df-3an",
        note="df-3an",
    )

    # biid
    s9 = lb.ref(
        "s9",
        "( ( ( [ y x φ ∧ [ y x ψ ) ∧ [ y x χ ) ↔ ( ( [ y x φ ∧ [ y x ψ ) ∧ [ y x χ ) )",
        ref="biid",
        note="biid",
    )

    # 3bitr4i
    res = lb.ref(
        "res",
        "( [ y x ( φ ∧ ψ ∧ χ ) ↔ ( [ y x φ ∧ [ y x ψ ∧ [ y x χ ) )",
        s9,
        s7,
        s8,
        ref="3bitr4i",
        note="3bitr4i",
    )
    return lb.build(res)


def prove_sbbi(sys: System) -> Proof:
    """sbbi: ( [ y / x ] ( φ ↔ ψ ) ↔ ( [ y / x ] φ ↔ [ y / x ] ψ ) ).

    Proper substitution distributes over equivalence.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wb wsb wi wa dfbi2 sbbii sbim anbi12i sban 3bitr4i bitri.
    """
    lb = ProofBuilder(sys, "sbbi")

    # dfbi2: ( φ ↔ ψ ) ↔ ( ( φ → ψ ) ∧ ( ψ → φ ) )
    s_dfbi2 = lb.ref(
        "s_dfbi2",
        "( φ ↔ ψ ) ↔ ( ( φ → ψ ) ∧ ( ψ → φ ) )",
        ref="dfbi2",
        note="dfbi2",
    )

    # sbbii with dfbi2: [ y / x ] ( φ ↔ ψ ) ↔ [ y / x ] ( ( φ → ψ ) ∧ ( ψ → φ ) )
    s_sbbii = lb.ref(
        "s_sbbii",
        "( [ y x ( φ ↔ ψ ) ↔ [ y x ( ( φ → ψ ) ∧ ( ψ → φ ) ) )",
        s_dfbi2,
        ref="sbbii",
        note="sbbii dfbi2",
    )

    # sban: [ y / x ] ( ( φ → ψ ) ∧ ( ψ → φ ) ) ↔ ( [ y / x ] ( φ → ψ ) ∧ [ y / x ] ( ψ → φ ) )
    s_sban = lb.ref(
        "s_sban",
        "( [ y x ( ( φ → ψ ) ∧ ( ψ → φ ) ) ↔ ( [ y x ( φ → ψ ) ∧ [ y x ( ψ → φ ) ) )",
        ref="sban",
        note="sban",
    )

    # bitri: [ y / x ] ( φ ↔ ψ ) ↔ ( [ y / x ] ( φ → ψ ) ∧ [ y / x ] ( ψ → φ ) )
    s_bitri = lb.ref(
        "s_bitri",
        "( [ y x ( φ ↔ ψ ) ↔ ( [ y x ( φ → ψ ) ∧ [ y x ( ψ → φ ) ) )",
        s_sbbii,
        s_sban,
        ref="bitri",
        note="bitri sbbii, sban",
    )

    # sbim: [ y / x ] ( φ → ψ ) ↔ ( [ y / x ] φ → [ y / x ] ψ )
    s_sbim1 = lb.ref(
        "s_sbim1",
        "( [ y x ( φ → ψ ) ↔ ( [ y x φ → [ y x ψ ) )",
        ref="sbim",
        note="sbim",
    )

    # sbim: [ y / x ] ( ψ → φ ) ↔ ( [ y / x ] ψ → [ y / x ] φ )
    s_sbim2 = lb.ref(
        "s_sbim2",
        "( [ y x ( ψ → φ ) ↔ ( [ y x ψ → [ y x φ ) )",
        ref="sbim",
        note="sbim",
    )

    # anbi12i: ( [ y / x ] ( φ → ψ ) ∧ [ y / x ] ( ψ → φ ) ) ↔
    #           ( ( [ y / x ] φ → [ y / x ] ψ ) ∧ ( [ y / x ] ψ → [ y / x ] φ ) )
    s_anbi12i = lb.ref(
        "s_anbi12i",
        "( ( [ y x ( φ → ψ ) ∧ [ y x ( ψ → φ ) ) ↔ ( ( [ y x φ → [ y x ψ ) ∧ ( [ y x ψ → [ y x φ ) ) )",
        s_sbim1,
        s_sbim2,
        ref="anbi12i",
        note="anbi12i",
    )

    # dfbi2 on substituted vars: ( [ y / x ] φ ↔ [ y / x ] ψ ) ↔
    #   ( ( [ y / x ] φ → [ y / x ] ψ ) ∧ ( [ y / x ] ψ → [ y / x ] φ ) )
    s_dfbi2_rhs = lb.ref(
        "s_dfbi2_rhs",
        "( ( [ y x φ ↔ [ y x ψ ) ↔ ( ( [ y x φ → [ y x ψ ) ∧ ( [ y x ψ → [ y x φ ) ) )",
        ref="dfbi2",
        note="dfbi2",
    )

    # 3bitr4i: ( [ y / x ] ( φ ↔ ψ ) ↔ ( [ y / x ] φ ↔ [ y / x ] ψ ) )
    res = lb.ref(
        "res",
        "( [ y x ( φ ↔ ψ ) ↔ ( [ y x φ ↔ [ y x ψ ) )",
        s_anbi12i,
        s_bitri,
        s_dfbi2_rhs,
        ref="3bitr4i",
        note="3bitr4i",
    )

    return lb.build(res)


def prove_sblbis(sys: System) -> Proof:
    """sblbis: ( [ y / x ] ( χ ↔ φ ) ↔ ( [ y / x ] χ ↔ ψ ).

    Inference form of sbbi.  From the hypothesis ( [ y / x ] φ ↔ ψ ),
    deduce that proper substitution distributes over equivalence.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wb wsb sbbi bibi2i bitri.
    """
    lb = ProofBuilder(sys, "sblbis")
    hyp = lb.hyp("sblbis.1", "( [ y x φ ↔ ψ )")

    # sbbi: ( [ y / x ] ( χ ↔ φ ) ↔ ( [ y / x ] χ ↔ [ y / x ] φ ) )
    s1 = lb.ref(
        "s1",
        "( [ y x ( χ ↔ φ ) ↔ ( [ y x χ ↔ [ y x φ ) )",
        ref="sbbi",
        note="sbbi",
    )

    # bibi2i with hypothesis: ( ( [ y / x ] χ ↔ [ y / x ] φ ) ↔ ( [ y / x ] χ ↔ ψ ) )
    s2 = lb.ref(
        "s2",
        "( ( [ y x χ ↔ [ y x φ ) ↔ ( [ y x χ ↔ ψ ) )",
        hyp,
        ref="bibi2i",
        note="bibi2i sblbis.1",
    )

    # bitri: ( [ y / x ] ( χ ↔ φ ) ↔ ( [ y / x ] χ ↔ ψ ) )
    res = lb.ref(
        "res",
        "( [ y x ( χ ↔ φ ) ↔ ( [ y x χ ↔ ψ ) )",
        s1,
        s2,
        ref="bitri",
        note="bitri sbbi, bibi2i",
    )

    return lb.build(res)


def prove_sbrbis(sys: System) -> Proof:
    """sbrbis: ( [ y / x ] ( φ ↔ χ ) ↔ ( ψ ↔ [ y / x ] χ ) ).

    Inference form of sbbi.  From the hypothesis ( [ y / x ] φ ↔ ψ ),
    deduce that proper substitution of the first argument of a
    biconditional preserves equivalence.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wb wsb sbbi bibi1i bitri.
    """
    lb = ProofBuilder(sys, "sbrbis")
    hyp = lb.hyp("sbrbis.1", "( [ y x φ ↔ ψ )")

    # sbbi: ( [ y / x ] ( φ ↔ χ ) ↔ ( [ y / x ] φ ↔ [ y / x ] χ ) )
    s1 = lb.ref(
        "s1",
        "( [ y x ( φ ↔ χ ) ↔ ( [ y x φ ↔ [ y x χ ) )",
        ref="sbbi",
        note="sbbi",
    )

    # bibi1i with hypothesis: ( ( [ y / x ] φ ↔ [ y / x ] χ ) ↔ ( ψ ↔ [ y / x ] χ ) )
    s2 = lb.ref(
        "s2",
        "( ( [ y x φ ↔ [ y x χ ) ↔ ( ψ ↔ [ y x χ ) )",
        hyp,
        ref="bibi1i",
        note="bibi1i sbrbis.1",
    )

    # bitri: ( [ y / x ] ( φ ↔ χ ) ↔ ( ψ ↔ [ y / x ] χ ) )
    res = lb.ref(
        "res",
        "( [ y x ( φ ↔ χ ) ↔ ( ψ ↔ [ y x χ ) )",
        s1,
        s2,
        ref="bitri",
        note="bitri sbbi, bibi1i",
    )

    return lb.build(res)


def prove_dfmo(sys: System) -> Proof:
    """dfmo: ∃* x φ ↔ ∃ y ∀ x ( φ → x = y ).

    Definition of "exists at most one". See df-mo.
    """
    lb = ProofBuilder(sys, "dfmo")
    justification = lb.ref(
        "justification",
        "∃ y ∀ x ( φ → x = y ) ↔ ∃ z ∀ x ( φ → x = z )",
        ref="mojust",
        note="mojust",
    )
    res = lb.ref(
        "s1",
        "∃* x φ ↔ ∃ y ∀ x ( φ → x = y )",
        justification,
        ref="df-mo",
        note="df-mo",
    )
    return lb.build(res)


def prove_moim(sys: System) -> Proof:
    """moim: ∀ x ( φ → ψ ) → ( ∃* x ψ → ∃* x φ ).

    If φ implies ψ for all x, then "at most one ψ" implies
    "at most one φ".  From imim1, al2imi, eximdv, dfmo, and
    3imtr4g.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "moim")
    # imim1: ( φ → ψ ) → ( ( ψ → x = y ) → ( φ → x = y ) )
    s1 = lb.ref(
        "s1",
        "( φ → ψ ) → ( ( ψ → x = y ) → ( φ → x = y ) )",
        ref="imim1",
        note="imim1 with χ := x = y",
    )
    # al2imi with s1: A. x ( φ → ψ ) → ( A. x ( ψ → x = y ) → A. x ( φ → x = y ) )
    s2 = lb.ref(
        "s2",
        "∀ x ( φ → ψ ) → ( ∀ x ( ψ → x = y ) → ∀ x ( φ → x = y ) )",
        s1,
        ref="al2imi",
        note="al2imi imim1",
    )
    # eximdv with s2: ∀ x ( φ → ψ ) → ( ∃ y ∀ x ( ψ → x = y ) → ∃ y ∀ x ( φ → x = y ) )
    s3 = lb.ref(
        "s3",
        "∀ x ( φ → ψ ) → ( ∃ y ∀ x ( ψ → x = y ) → ∃ y ∀ x ( φ → x = y ) )",
        s2,
        ref="eximdv",
        note="eximdv al2imi",
    )
    # dfmo for ψ: ∃* x ψ ↔ ∃ y ∀ x ( ψ → x = y )
    s4 = lb.ref(
        "s4",
        "∃* x ψ ↔ ∃ y ∀ x ( ψ → x = y )",
        ref="dfmo",
        note="dfmo with φ := ψ",
    )
    # dfmo for φ: ∃* x φ ↔ ∃ y ∀ x ( φ → x = y )
    s5 = lb.ref(
        "s5",
        "∃* x φ ↔ ∃ y ∀ x ( φ → x = y )",
        ref="dfmo",
        note="dfmo with φ := φ",
    )
    # 3imtr4g: ∀ x ( φ → ψ ) → ( ∃* x ψ → ∃* x φ )
    res = lb.ref(
        "res",
        "∀ x ( φ → ψ ) → ( ∃* x ψ → ∃* x φ )",
        s3,
        s4,
        s5,
        ref="3imtr4g",
        note="3imtr4g s3, dfmo, dfmo",
    )
    return lb.build(res)


def prove_moimdv(sys: System) -> Proof:
    """moimdv: φ → ( ∃* x χ → ∃* x ψ ).

    Deduction form of moim.  Given φ → ( ψ → χ ), conclude
    φ → ( ∃* x χ → ∃* x ψ ).  From alrimiv, moim, and syl.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "moimdv")
    hyp = lb.hyp("moimdv.1", "φ → ( ψ → χ )")

    # alrimiv: ( φ → ( ψ → χ ) ) ⊢ φ → ∀ x ( ψ → χ )
    s1 = lb.ref(
        "s1",
        "φ → ∀ x ( ψ → χ )",
        hyp,
        ref="alrimiv",
        note="alrimiv moimdv.1",
    )

    # moim: ∀ x ( ψ → χ ) → ( ∃* x χ → ∃* x ψ )
    s2 = lb.ref(
        "s2",
        "∀ x ( ψ → χ ) → ( ∃* x χ → ∃* x ψ )",
        ref="moim",
        note="moim with φ := ψ, ψ := χ",
    )

    # syl: ( φ → ∀ x ( ψ → χ ) ), ( ∀ x ( ψ → χ ) → ( ∃* x χ → ∃* x ψ ) )
    #   ⊢ φ → ( ∃* x χ → ∃* x ψ )
    res = lb.ref(
        "res",
        "φ → ( ∃* x χ → ∃* x ψ )",
        s1,
        s2,
        ref="syl",
        note="syl alrimiv, moim",
    )
    return lb.build(res)


def prove_nexmo(sys: System) -> Proof:
    """nexmo: ¬ ∃ x φ → ∃* x φ.

    If there is no x such that φ holds, then there exists at most one
    x such that φ holds.  From pm2.21, alimi, alrimiv, 19.2d, alnex,
    bicomi, dfmo, and 3imtr4i.  (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "nexmo")
    # pm2.21: ¬ φ → ( φ → x = y )
    s1 = lb.ref("s1", "¬ φ → ( φ → x = y )", ref="pm2.21", note="pm2.21")
    # alimi: ∀ x ¬ φ → ∀ x ( φ → x = y )
    s2 = lb.ref(
        "s2",
        "∀ x ¬ φ → ∀ x ( φ → x = y )",
        s1,
        ref="alimi",
        note="alimi pm2.21",
    )
    # alrimiv: ∀ x ¬ φ → ∀ y ∀ x ( φ → x = y )
    s3 = lb.ref(
        "s3",
        "∀ x ¬ φ → ∀ y ∀ x ( φ → x = y )",
        s2,
        ref="alrimiv",
        note="alrimiv s2",
    )
    # 19.2d: ∀ x ¬ φ → ∃ y ∀ x ( φ → x = y )
    s4 = lb.ref(
        "s4",
        "∀ x ¬ φ → ∃ y ∀ x ( φ → x = y )",
        s3,
        ref="19.2d",
        note="19.2d s3",
    )
    # alnex: ∀ x ¬ φ ↔ ¬ ∃ x φ
    s5 = lb.ref("s5", "∀ x ¬ φ ↔ ¬ ∃ x φ", ref="alnex", note="alnex")
    # bicomi: ¬ ∃ x φ ↔ ∀ x ¬ φ
    s6 = lb.ref(
        "s6",
        "¬ ∃ x φ ↔ ∀ x ¬ φ",
        s5,
        ref="bicomi",
        note="bicomi alnex",
    )
    # dfmo: ∃* x φ ↔ ∃ y ∀ x ( φ → x = y )
    s7 = lb.ref(
        "s7",
        "∃* x φ ↔ ∃ y ∀ x ( φ → x = y )",
        ref="dfmo",
        note="dfmo",
    )
    # 3imtr4i: ¬ ∃ x φ → ∃* x φ
    res = lb.ref(
        "res",
        "¬ ∃ x φ → ∃* x φ",
        s4,
        s6,
        s7,
        ref="3imtr4i",
        note="3imtr4i s4, bicomi, dfmo",
    )
    return lb.build(res)


def prove_moabs(sys: System) -> Proof:
    """moabs: ∃* x φ ↔ ( ∃ x φ → ∃* x φ ).

    Existence-at-most-one absorbs antecedent existence.
    From ax-1, nexmo, id, ja, and impbii.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "moabs")
    # ax-1: ∃*x φ → (∃x φ → ∃*x φ) — forward direction
    s_fwd = lb.ref(
        "s_fwd",
        "∃* x φ → ( ∃ x φ → ∃* x φ )",
        ref="ax-1",
        note="ax-1 — forward direction",
    )
    # nexmo: ¬ ∃x φ → ∃*x φ — ja.1
    s_nexmo = lb.ref(
        "s_nexmo",
        "¬ ∃ x φ → ∃* x φ",
        ref="nexmo",
        note="nexmo — ja.1",
    )
    # id: ∃*x φ → ∃*x φ — ja.2
    s_id = lb.ref(
        "s_id",
        "∃* x φ → ∃* x φ",
        ref="id",
        note="id — ja.2",
    )
    # ja: (∃x φ → ∃*x φ) → ∃*x φ — reverse direction
    s_rev = lb.ref(
        "s_rev",
        "( ∃ x φ → ∃* x φ ) → ∃* x φ",
        s_nexmo,
        s_id,
        ref="ja",
        note="ja — reverse direction",
    )
    # impbii: ∃*x φ ↔ (∃x φ → ∃*x φ)
    res = lb.ref(
        "res",
        "∃* x φ ↔ ( ∃ x φ → ∃* x φ )",
        s_fwd,
        s_rev,
        ref="impbii",
        note="impbii",
    )
    return lb.build(res)


def prove_moeu(sys: System) -> Proof:
    """moeu: ∃* x φ ↔ ( ∃ x φ → ∃! x φ ).

    At-most-one is equivalent to: if something exists, it is unique.
    """
    lb = ProofBuilder(sys, "moeu")
    # moabs: ∃* x φ ↔ ( ∃ x φ → ∃* x φ )
    s1 = lb.ref(
        "s1",
        "∃* x φ ↔ ( ∃ x φ → ∃* x φ )",
        ref="moabs",
        note="moabs",
    )
    # exmoeub: ∃ x φ → ( ∃* x φ ↔ ∃! x φ )
    s2 = lb.ref(
        "s2",
        "∃ x φ → ( ∃* x φ ↔ ∃! x φ )",
        ref="exmoeub",
        note="exmoeub",
    )
    # pm5.74i: ( ∃ x φ → ∃* x φ ) ↔ ( ∃ x φ → ∃! x φ )
    s3 = lb.ref(
        "s3",
        "( ∃ x φ → ∃* x φ ) ↔ ( ∃ x φ → ∃! x φ )",
        s2,
        ref="pm5.74i",
        note="pm5.74i",
    )
    # bitri: ∃* x φ ↔ ( ∃ x φ → ∃! x φ )
    res = lb.ref(
        "res",
        "∃* x φ ↔ ( ∃ x φ → ∃! x φ )",
        s1,
        s3,
        ref="bitri",
        note="bitri",
    )
    return lb.build(res)


def prove_exmo(sys: System) -> Proof:
    """exmo: ( ∃ x φ ∨ ∃* x φ ).

    Either there exists an x such that φ, or there exists at most one.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "exmo")
    s1 = lb.ref("s1", "¬ ∃ x φ → ∃* x φ", ref="nexmo", note="nexmo")
    res = lb.ref("res", "( ∃ x φ ∨ ∃* x φ )", s1, ref="orri", note="orri")
    return lb.build(res)


def prove_exmoeu(sys: System) -> Proof:
    """exmoeu: ∃ x φ ↔ ( ∃* x φ → ∃! x φ ).

    If something exists, then at-most-one implies exactly-one,
    and vice versa.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "exmoeu")

    # exmoeub: ∃ x φ → ( ∃* x φ ↔ ∃! x φ )
    s1 = lb.ref(
        "s1",
        "∃ x φ → ( ∃* x φ ↔ ∃! x φ )",
        ref="exmoeub",
        note="exmoeub",
    )

    # biimpd: ( ∃* x φ ↔ ∃! x φ ) → ( ∃* x φ → ∃! x φ )
    # syl s1, biimpd: ∃ x φ → ( ∃* x φ → ∃! x φ )  [forward direction]
    s_fwd = lb.ref(
        "s_fwd",
        "∃ x φ → ( ∃* x φ → ∃! x φ )",
        s1,
        ref="biimpd",
        note="syl exmoeub, biimpd",
    )

    # nexmo: ¬ ∃ x φ → ∃* x φ
    s3 = lb.ref(
        "s3",
        "¬ ∃ x φ → ∃* x φ",
        ref="nexmo",
        note="nexmo",
    )

    # con1i s3: ¬ ∃* x φ → ∃ x φ
    s4 = lb.ref(
        "s4",
        "¬ ∃* x φ → ∃ x φ",
        s3,
        ref="con1i",
        note="con1i nexmo",
    )

    # euex: ∃! x φ → ∃ x φ
    s5 = lb.ref(
        "s5",
        "∃! x φ → ∃ x φ",
        ref="euex",
        note="euex",
    )

    # ja s4, s5: ( ∃* x φ → ∃! x φ ) → ∃ x φ  [reverse direction]
    s_rev = lb.ref(
        "s_rev",
        "( ∃* x φ → ∃! x φ ) → ∃ x φ",
        s4,
        s5,
        ref="ja",
        note="ja con1i(nexmo), euex",
    )

    # impbii s_fwd, s_rev: ∃ x φ ↔ ( ∃* x φ → ∃! x φ )
    res = lb.ref(
        "res",
        "∃ x φ ↔ ( ∃* x φ → ∃! x φ )",
        s_fwd,
        s_rev,
        ref="impbii",
        note="impbii",
    )

    return lb.build(res)


def prove_cbveuvw(sys: System) -> Proof:
    """cbveuvw: ( E! x φ ↔ E! y ψ ).

    Change bound variable in a unique existential quantifier.
    From cbvexvw, cbvmovw, anbi12i, df-eu, and 3bitr4i.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "cbveuvw")
    hyp = lb.hyp("cbveuvw.1", "x = y → ( φ ↔ ψ )")

    # cbvexvw: ( E. x φ ↔ E. y ψ )
    s1 = lb.ref(
        "s1",
        "( E. x φ ↔ E. y ψ )",
        hyp,
        ref="cbvexvw",
        note="cbvexvw",
    )

    # cbvmovw: ( E* x φ ↔ E* y ψ )
    s2 = lb.ref(
        "s2",
        "( E* x φ ↔ E* y ψ )",
        hyp,
        ref="cbvmovw",
        note="cbvmovw",
    )

    # anbi12i: ( ( E. x φ ∧ E* x φ ) ↔ ( E. y ψ ∧ E* y ψ ) )
    s3 = lb.ref(
        "s3",
        "( ( E. x φ ∧ E* x φ ) ↔ ( E. y ψ ∧ E* y ψ ) )",
        s1,
        s2,
        ref="anbi12i",
        note="anbi12i cbvexvw, cbvmovw",
    )

    # df-eu: ( E! x φ ↔ ( E. x φ ∧ E* x φ ) )
    s4 = lb.ref(
        "s4",
        "E! x φ ↔ ( E. x φ ∧ E* x φ )",
        ref="df-eu",
        note="df-eu",
    )

    # df-eu: ( E! y ψ ↔ ( E. y ψ ∧ E* y ψ ) )
    s5 = lb.ref(
        "s5",
        "E! y ψ ↔ ( E. y ψ ∧ E* y ψ )",
        ref="df-eu",
        note="df-eu",
    )

    # 3bitr4i: ( E! x φ ↔ E! y ψ )
    res = lb.ref(
        "res",
        "( E! x φ ↔ E! y ψ )",
        s3,
        s4,
        s5,
        ref="3bitr4i",
        note="3bitr4i",
    )

    return lb.build(res)


def prove_euae(sys: System) -> Proof:
    """euae: ∃! x ⊤ ↔ ∀ x ( x = y ).

    There exists a unique x such that True iff for all x, x equals y.
    From eu3v, extru, biantrur, trut, albii, exbii, hbaev, hbnaev,
    19.8w, alnex, sylib, con4i, impbii, bitri, and 3bitr4ri.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "euae")

    # eu3v with φ := ⊤: ∃! x ⊤ ↔ ( ∃ x ⊤ ∧ ∃ y ∀ x ( ⊤ → x = y ) )
    s_eu3v = lb.ref(
        "s_eu3v",
        "∃! x ⊤ ↔ ( ∃ x ⊤ ∧ ∃ y ∀ x ( ⊤ → x = y ) )",
        ref="eu3v",
        note="eu3v with φ := ⊤",
    )

    # extru: ∃ x ⊤
    s_extru = lb.ref("s_extru", "∃ x ⊤", ref="extru", note="extru")

    # biantrur extru: ∃ y ∀ x ( ⊤ → x = y ) ↔ ( ∃ x ⊤ ∧ ∃ y ∀ x ( ⊤ → x = y ) )
    s_biantrur = lb.ref(
        "s_biantrur",
        "∃ y ∀ x ( ⊤ → x = y ) ↔ ( ∃ x ⊤ ∧ ∃ y ∀ x ( ⊤ → x = y ) )",
        s_extru,
        ref="biantrur",
        note="biantrur extru",
    )

    # trut: ( x = y ) ↔ ( ⊤ → x = y )
    s_trut = lb.ref(
        "s_trut",
        "( x = y ) ↔ ( ⊤ → x = y )",
        ref="trut",
        note="trut",
    )

    # albii trut: ∀ x ( x = y ) ↔ ∀ x ( ⊤ → x = y )
    s_albii = lb.ref(
        "s_albii",
        "∀ x ( x = y ) ↔ ∀ x ( ⊤ → x = y )",
        s_trut,
        ref="albii",
        note="albii trut",
    )

    # exbii albii: ∃ y ∀ x ( x = y ) ↔ ∃ y ∀ x ( ⊤ → x = y )
    s_exbii = lb.ref(
        "s_exbii",
        "∃ y ∀ x ( x = y ) ↔ ∃ y ∀ x ( ⊤ → x = y )",
        s_albii,
        ref="exbii",
        note="exbii albii",
    )

    # Key sub-proof: ∃ y ∀ x ( x = y ) ↔ ∀ x ( x = y )
    #
    # Forward: ∀ x ( x = y ) → ∃ y ∀ x ( x = y )
    # Using hbaev as hypothesis for 19.8w.

    # hbaev: ∀ x ( x = y ) → ∀ y ∀ x ( x = y )
    s_hbaev = lb.ref(
        "s_hbaev",
        "∀ x ( x = y ) → ∀ y ∀ x ( x = y )",
        ref="hbaev",
        note="hbaev",
    )

    # 19.8w: forward direction (auto-matched with hbaev as hypothesis)
    s_fwd = lb.ref(
        "s_fwd",
        "∀ x ( x = y ) → ∃ y ∀ x ( x = y )",
        s_hbaev,
        ref="19.8w",
        note="19.8w hbaev",
    )

    # Reverse: ∃ y ∀ x ( x = y ) → ∀ x ( x = y )
    # Using the contrapositive with hbnaev, alnex, sylib, con4i.

    # hbnaev: ¬ ∀ x ( x = y ) → ∀ y ¬ ∀ x ( x = y )
    s_hbnaev = lb.ref(
        "s_hbnaev",
        "¬ ∀ x ( x = y ) → ∀ y ¬ ∀ x ( x = y )",
        ref="hbnaev",
        note="hbnaev",
    )

    # alnex: ∀ y ¬ ∀ x ( x = y ) ↔ ¬ ∃ y ∀ x ( x = y )
    s_alnex = lb.ref(
        "s_alnex",
        "∀ y ¬ ∀ x ( x = y ) ↔ ¬ ∃ y ∀ x ( x = y )",
        ref="alnex",
        note="alnex",
    )

    # sylib: ¬ ∀ x ( x = y ) → ¬ ∃ y ∀ x ( x = y )
    s_sylib = lb.ref(
        "s_sylib",
        "¬ ∀ x ( x = y ) → ¬ ∃ y ∀ x ( x = y )",
        s_hbnaev,
        s_alnex,
        ref="sylib",
        note="sylib hbnaev, alnex",
    )

    # con4i: ∃ y ∀ x ( x = y ) → ∀ x ( x = y )
    s_con4i = lb.ref(
        "s_con4i",
        "∃ y ∀ x ( x = y ) → ∀ x ( x = y )",
        s_sylib,
        ref="con4i",
        note="con4i sylib",
    )

    # impbii: ∀ x ( x = y ) ↔ ∃ y ∀ x ( x = y )
    s_key = lb.ref(
        "s_key",
        "∀ x ( x = y ) ↔ ∃ y ∀ x ( x = y )",
        s_fwd,
        s_con4i,
        ref="impbii",
        note="impbii",
    )

    # bitri key, exbii: ∀ x ( x = y ) ↔ ∃ y ∀ x ( ⊤ → x = y )
    s_bitri1 = lb.ref(
        "s_bitri1",
        "∀ x ( x = y ) ↔ ∃ y ∀ x ( ⊤ → x = y )",
        s_key,
        s_exbii,
        ref="bitri",
        note="bitri key, exbii",
    )

    # bitri bitri1, biantrur: ∀ x ( x = y ) ↔ ( ∃ x ⊤ ∧ ∃ y ∀ x ( ⊤ → x = y ) )
    s_bitri2 = lb.ref(
        "s_bitri2",
        "∀ x ( x = y ) ↔ ( ∃ x ⊤ ∧ ∃ y ∀ x ( ⊤ → x = y ) )",
        s_bitri1,
        s_biantrur,
        ref="bitri",
        note="bitri bitri1, biantrur",
    )

    # biid: RHS ↔ RHS for the 3bitr4ri common part
    s_biid = lb.ref(
        "s_biid",
        "( ∃ x ⊤ ∧ ∃ y ∀ x ( ⊤ → x = y ) ) ↔ ( ∃ x ⊤ ∧ ∃ y ∀ x ( ⊤ → x = y ) )",
        ref="biid",
        note="biid",
    )

    # 3bitr4ri: ∃! x ⊤ ↔ ∀ x ( x = y )
    res = lb.ref(
        "res",
        "∃! x ⊤ ↔ ∀ x ( x = y )",
        s_biid,
        s_bitri2,
        s_eu3v,
        ref="3bitr4ri",
        note="3bitr4ri biid, bitri2, eu3v",
    )

    return lb.build(res)


def prove_dfeu(sys: System) -> Proof:
    """dfeu: ∃! x φ ↔ ( ∃ x φ ∧ ∃* x φ ).

    Definition of "there exists exactly one".
    (Contributed by NM, 19-Apr-1994.)
    set.mm proof: wex weu wa wi wmo abai euex pm4.71ri moeu anbi2i 3bitr4i.
    """
    lb = ProofBuilder(sys, "dfeu")

    # euex: ∃! x φ → ∃ x φ
    s_euex = lb.ref(
        "s_euex",
        "∃! x φ → ∃ x φ",
        ref="euex",
        note="euex",
    )

    # pm4.71ri with euex: ∃! x φ ↔ ( ∃ x φ ∧ ∃! x φ )
    s_pm = lb.ref(
        "s_pm",
        "∃! x φ ↔ ( ∃ x φ ∧ ∃! x φ )",
        s_euex,
        ref="pm4.71ri",
        note="pm4.71ri euex",
    )

    # moeu: ∃* x φ ↔ ( ∃ x φ → ∃! x φ )
    s_moeu = lb.ref(
        "s_moeu",
        "∃* x φ ↔ ( ∃ x φ → ∃! x φ )",
        ref="moeu",
        note="moeu",
    )

    # abai: ( ∃ x φ ∧ ∃! x φ ) ↔ ( ∃ x φ ∧ ( ∃ x φ → ∃! x φ ) )
    s_abai = lb.ref(
        "s_abai",
        "( ∃ x φ ∧ ∃! x φ ) ↔ ( ∃ x φ ∧ ( ∃ x φ → ∃! x φ ) )",
        ref="abai",
        note="abai",
    )

    # anbi2i with moeu: ( ∃ x φ ∧ ∃* x φ ) ↔ ( ∃ x φ ∧ ( ∃ x φ → ∃! x φ ) )
    s_anbi = lb.ref(
        "s_anbi",
        "( ∃ x φ ∧ ∃* x φ ) ↔ ( ∃ x φ ∧ ( ∃ x φ → ∃! x φ ) )",
        s_moeu,
        ref="anbi2i",
        note="anbi2i moeu",
    )

    # 3bitr4i: ∃! x φ ↔ ( ∃ x φ ∧ ∃* x φ )
    res = lb.ref(
        "res",
        "∃! x φ ↔ ( ∃ x φ ∧ ∃* x φ )",
        s_abai,
        s_pm,
        s_anbi,
        ref="3bitr4i",
        note="3bitr4i",
    )

    return lb.build(res)


def prove_ax12i(sys: System) -> Proof:
    """ax12i: x = y → ( φ → ∀ x ( x = y → φ ) ).

    Inference from ax-12 via biimprcd, alrimih, and biimtrdi.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: weq wi wal biimprcd alrimih biimtrdi.
    """
    lb = ProofBuilder(sys, "ax12i")
    h1 = lb.hyp("ax12i.1", "x = y → ( φ ↔ ψ )")
    h2 = lb.hyp("ax12i.2", "ψ → ∀ x ψ")
    # biimprcd ax12i.1: ψ → ( x = y → φ )
    s1 = lb.ref(
        "s1",
        "ψ → ( x = y → φ )",
        h1,
        ref="biimprcd",
        note="biimprcd",
    )
    # alrimih ax12i.2, s1: ψ → ∀ x ( x = y → φ )
    s2 = lb.ref(
        "s2",
        "ψ → ∀ x ( x = y → φ )",
        h2,
        s1,
        ref="alrimih",
        note="alrimih",
    )
    # biimtrdi ax12i.1, s2: x = y → ( φ → ∀ x ( x = y → φ ) )
    res = lb.ref(
        "res",
        "x = y → ( φ → ∀ x ( x = y → φ ) )",
        h1,
        s2,
        ref="biimtrdi",
        note="biimtrdi",
    )
    return lb.build(res)


def prove_ax12wlem(sys: System) -> Proof:
    """ax12wlem: x = y → ( φ → ∀ x ( x = y → φ ) ).

    Weak lemma for ax-12.  ax-5 on ψ yields ψ → ∀ x ψ, then ax12i
    combines that with the hypothesis to produce the conclusion.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "ax12wlem")
    hyp = lb.hyp("ax12wlemw.1", "x = y → ( φ ↔ ψ )")
    # ax-5: ψ → ∀ x ψ
    s1 = lb.ref("s1", "ψ → ∀ x ψ", ref="ax-5", note="ax-5")
    # ax12i ax12wlemw.1, s1: x = y → ( φ → ∀ x ( x = y → φ ) )
    res = lb.ref(
        "res",
        "x = y → ( φ → ∀ x ( x = y → φ ) )",
        hyp,
        s1,
        ref="ax12i",
        note="ax12i ax12wlemw.1, ax-5",
    )
    return lb.build(res)


def prove_ax12w(sys: System) -> Proof:
    """ax12w: x = y → ( ∀ y φ → ∀ x ( x = y → φ ) ).

    Weak version of ax-12.  ax12wlem gives the inner implication, spw
    instantiates with the second hypothesis to replace the antecedent,
    and syl5 combines them.
    (Contributed by NM, 29-Apr-1994.)
    """
    lb = ProofBuilder(sys, "ax12w")
    hyp1 = lb.hyp("ax12w.1", "x = y → ( φ ↔ ψ )")
    hyp2 = lb.hyp("ax12w.2", "y = z → ( φ ↔ χ )")

    # spw with ax12w.2: ∀ y φ → φ
    s1 = lb.ref(
        "s1",
        "∀ y φ → φ",
        hyp2,
        ref="spw",
        note="spw ax12w.2",
    )

    # ax12wlem with ax12w.1: x = y → ( φ → ∀ x ( x = y → φ ) )
    s2 = lb.ref(
        "s2",
        "x = y → ( φ → ∀ x ( x = y → φ ) )",
        hyp1,
        ref="ax12wlem",
        note="ax12wlem ax12w.1",
    )

    # syl5 combines the two: x = y → ( ∀ y φ → ∀ x ( x = y → φ ) )
    res = lb.ref(
        "res",
        "x = y → ( ∀ y φ → ∀ x ( x = y → φ ) )",
        s1,
        s2,
        ref="syl5",
        note="syl5 spw, ax12wlem",
    )
    return lb.build(res)


def prove_19_8a(sys: System) -> Proof:
    """19.8a: φ → ∃ x φ.

    From ax12v and alequexv via syl6 to get x = y → ( φ → ∃ x φ ),
    then eliminate the antecedent with ax6evr and exlimiiv.
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "19.8a")

    # ax12v: x = y → ( φ → ∀ x ( x = y → φ ) )
    s1 = lb.ref(
        "s1",
        "x = y → ( φ → ∀ x ( x = y → φ ) )",
        ref="ax12v",
        note="ax12v",
    )

    # alequexv: ∀ x ( x = y → φ ) → ∃ x φ
    s2 = lb.ref(
        "s2",
        "∀ x ( x = y → φ ) → ∃ x φ",
        ref="alequexv",
        note="alequexv",
    )

    # syl6 s1, s2: x = y → ( φ → ∃ x φ )
    s3 = lb.ref(
        "s3",
        "x = y → ( φ → ∃ x φ )",
        s1,
        s2,
        ref="syl6",
        note="syl6 ax12v, alequexv",
    )

    # ax6evr: ∃ y x = y
    s4 = lb.ref(
        "s4",
        "∃ y x = y",
        ref="ax6evr",
        note="ax6evr",
    )

    # exlimiiv s3, s4: φ → ∃ x φ
    res = lb.ref(
        "res",
        "φ → ∃ x φ",
        s3,
        s4,
        ref="exlimiiv",
        note="exlimiiv",
    )

    return lb.build(res)


def prove_19_8ad(sys: System) -> Proof:
    """19.8ad: φ → ∃ x ψ.

    Deduction form of 19.8a.  (Contributed by NM, 10-Jan-1993.)
    set.mm proof: wex 19.8a syl.
    """
    lb = ProofBuilder(sys, "19.8ad")
    hyp = lb.hyp("19.8ad.1", "φ → ψ")
    # 19.8a with ψ: ψ → ∃ x ψ
    s1 = lb.ref(
        "s1",
        "ψ → ∃ x ψ",
        ref="19.8a",
        note="19.8a",
    )
    # syl: (φ → ψ), (ψ → ∃ x ψ) ⊢ φ → ∃ x ψ
    res = lb.ref(
        "res",
        "φ → ∃ x ψ",
        hyp,
        s1,
        ref="syl",
        note="syl 19.8ad.1, 19.8a",
    )
    return lb.build(res)


def prove_sp(sys: System) -> Proof:
    """sp: ∀ x φ → φ.

    From alex, 19.8a, con1i, and sylbi.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "sp")

    # 19.8a with ¬ φ: ¬ φ → ∃ x ¬ φ
    s1 = lb.ref(
        "s1",
        "¬ φ → ∃ x ¬ φ",
        ref="19.8a",
        note="19.8a",
    )

    # con1i s1: ¬ ∃ x ¬ φ → φ
    s2 = lb.ref(
        "s2",
        "¬ ∃ x ¬ φ → φ",
        s1,
        ref="con1i",
        note="con1i",
    )

    # alex: ∀ x φ ↔ ¬ ∃ x ¬ φ
    s3 = lb.ref(
        "s3",
        "∀ x φ ↔ ¬ ∃ x ¬ φ",
        ref="alex",
        note="alex",
    )

    # sylbi s3, s2: ∀ x φ → φ
    res = lb.ref(
        "res",
        "∀ x φ → φ",
        s3,
        s2,
        ref="sylbi",
        note="sylbi alex, con1i",
    )

    return lb.build(res)


def prove_spi(sys: System) -> Proof:
    """spi: φ.

    Inference from ∀ x φ, by sp and ax-mp.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "spi")
    hyp = lb.hyp("spi.1", "∀ x φ")
    sp_step = lb.ref(
        "s1",
        "∀ x φ → φ",
        ref="sp",
        note="sp",
    )
    res = lb.mp("res", hyp, sp_step, note="ax-mp")
    return lb.build(res)


def prove_sps(sys: System) -> Proof:
    """sps: ( ∀ x φ → ψ ).

    Syllogism with sp. (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "sps")
    hyp = lb.hyp("sps.1", "φ → ψ")
    sp_step = lb.ref(
        "s1",
        "∀ x φ → φ",
        ref="sp",
        note="sp",
    )
    res = lb.ref(
        "res",
        "∀ x φ → ψ",
        sp_step,
        hyp,
        ref="syl",
        note="syl sp, sps.1",
    )
    return lb.build(res)


def prove_19_21bi(sys: System) -> Proof:
    """19.21bi: φ → ψ.

    From 19.21bi.1 (φ → ∀ x ψ) and sp, derive φ → ψ by syllogism.
    (Contributed by NM, 19-Apr-1994.)
    """
    lb = ProofBuilder(sys, "19.21bi")
    hyp = lb.hyp("19.21bi.1", "φ → ∀ x ψ")
    sp_step = lb.ref(
        "s1",
        "∀ x ψ → ψ",
        ref="sp",
        note="sp",
    )
    res = lb.ref(
        "res",
        "φ → ψ",
        hyp,
        sp_step,
        ref="syl",
        note="syl 19.21bi.1, sp",
    )
    return lb.build(res)


def prove_2exnaln(sys: System) -> Proof:
    """2exnaln: ( ∃ x ∃ y φ ↔ ¬ ∀ x ∀ y ¬ φ ).

    Equivalence of double existence with negated double universal of negation.
    From df-ex, alnex, albii, and xchbinxr.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "2exnaln")

    # df-ex with formula ∃ y φ and variable x:
    #   ∃ x ∃ y φ ↔ ¬ ∀ x ¬ ∃ y φ
    s_dfex = lb.ref(
        "s_dfex",
        "∃ x ∃ y φ ↔ ¬ ∀ x ¬ ∃ y φ",
        ref="df-ex",
        note="df-ex",
    )

    # alnex with variable y:
    #   ∀ y ¬ φ ↔ ¬ ∃ y φ
    s_alnex = lb.ref(
        "s_alnex",
        "∀ y ¬ φ ↔ ¬ ∃ y φ",
        ref="alnex",
        note="alnex",
    )

    # albii applied to alnex with variable x:
    #   ∀ x ∀ y ¬ φ ↔ ∀ x ¬ ∃ y φ
    s_albii = lb.ref(
        "s_albii",
        "∀ x ∀ y ¬ φ ↔ ∀ x ¬ ∃ y φ",
        s_alnex,
        ref="albii",
        note="albii alnex",
    )

    # xchbinxr with s_dfex (φ ↔ ¬ ψ) and s_albii (χ ↔ ψ):
    #   ∃ x ∃ y φ ↔ ¬ ∀ x ∀ y ¬ φ
    res = lb.ref(
        "res",
        "∃ x ∃ y φ ↔ ¬ ∀ x ∀ y ¬ φ",
        s_dfex,
        s_albii,
        ref="xchbinxr",
        note="xchbinxr df-ex, albii",
    )

    return lb.build(res)


def prove_19_41v(sys: System) -> Proof:
    """19.41v: ∃ x ( φ ∧ ψ ) ↔ ( ∃ x φ ∧ ψ ).

    Existential quantifier distributes over conjunction when the second
    conjunct does not contain the bound variable.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wa wex 19.40 ax5e anim2i syl pm3.21 eximdv impcom impbii.
    """
    lb = ProofBuilder(sys, "19.41v")

    # Forward direction: ∃ x ( φ ∧ ψ ) → ( ∃ x φ ∧ ψ )
    # 19.40: ∃ x ( φ ∧ ψ ) → ( ∃ x φ ∧ ∃ x ψ )
    s_19_40 = lb.ref(
        "s_19_40",
        "∃ x ( φ ∧ ψ ) → ( ∃ x φ ∧ ∃ x ψ )",
        ref="19.40",
        note="19.40",
    )
    # ax5e: ∃ x ψ → ψ
    s_ax5e = lb.ref(
        "s_ax5e",
        "∃ x ψ → ψ",
        ref="ax5e",
        note="ax5e",
    )
    # anim2i: ( ∃ x φ ∧ ∃ x ψ ) → ( ∃ x φ ∧ ψ )
    s_anim2i = lb.ref(
        "s_anim2i",
        "( ∃ x φ ∧ ∃ x ψ ) → ( ∃ x φ ∧ ψ )",
        s_ax5e,
        ref="anim2i",
        note="anim2i ax5e",
    )
    # syl: ∃ x ( φ ∧ ψ ) → ( ∃ x φ ∧ ψ )
    s_fwd = lb.ref(
        "s_fwd",
        "∃ x ( φ ∧ ψ ) → ( ∃ x φ ∧ ψ )",
        s_19_40,
        s_anim2i,
        ref="syl",
        note="syl 19.40, anim2i",
    )

    # Reverse direction: ( ∃ x φ ∧ ψ ) → ∃ x ( φ ∧ ψ )
    # pm3.21 with swapped variables: ψ → ( φ → ( φ ∧ ψ ) )
    s_pm3_21 = lb.ref(
        "s_pm3_21",
        "ψ → ( φ → ( φ ∧ ψ ) )",
        ref="pm3.21",
        note="pm3.21",
    )
    # eximdv: ψ → ( ∃ x φ → ∃ x ( φ ∧ ψ ) )
    s_eximdv = lb.ref(
        "s_eximdv",
        "ψ → ( ∃ x φ → ∃ x ( φ ∧ ψ ) )",
        s_pm3_21,
        ref="eximdv",
        note="eximdv pm3.21",
    )
    # impcom: ( ∃ x φ ∧ ψ ) → ∃ x ( φ ∧ ψ )
    s_rev = lb.ref(
        "s_rev",
        "( ( ∃ x φ ∧ ψ ) → ∃ x ( φ ∧ ψ ) )",
        s_eximdv,
        ref="impcom",
        note="impcom eximdv",
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


def prove_19_41vv(sys: System) -> Proof:
    """19.41vv: ∃ x ∃ y ( φ ∧ ψ ) ↔ ( ∃ x ∃ y φ ∧ ψ ).

    Double existential quantifier distributes over conjunction when the
    second conjunct does not contain the bound variables.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wa wex 19.41v exbii bitri.
    """
    lb = ProofBuilder(sys, "19.41vv")

    # First 19.41v: ∃ y ( φ ∧ ψ ) ↔ ( ∃ y φ ∧ ψ )
    s_19_41v_y = lb.ref(
        "s_19_41v_y",
        "∃ y ( φ ∧ ψ ) ↔ ( ∃ y φ ∧ ψ )",
        ref="19.41v",
        note="19.41v",
    )

    # exbii: add ∃ x to both sides
    s_exbii = lb.ref(
        "s_exbii",
        "∃ x ∃ y ( φ ∧ ψ ) ↔ ∃ x ( ∃ y φ ∧ ψ )",
        s_19_41v_y,
        ref="exbii",
        note="exbii 19.41v",
    )

    # Second 19.41v: ∃ x ( ∃ y φ ∧ ψ ) ↔ ( ∃ x ∃ y φ ∧ ψ )
    s_19_41v_x = lb.ref(
        "s_19_41v_x",
        "∃ x ( ∃ y φ ∧ ψ ) ↔ ( ∃ x ∃ y φ ∧ ψ )",
        ref="19.41v",
        note="19.41v",
    )

    # bitri: combine
    res = lb.ref(
        "res",
        "∃ x ∃ y ( φ ∧ ψ ) ↔ ( ∃ x ∃ y φ ∧ ψ )",
        s_exbii,
        s_19_41v_x,
        ref="bitri",
        note="bitri exbii, 19.41v",
    )
    return lb.build(res)


def prove_19_42v(sys: System) -> Proof:
    """19.42v: ∃ x ( φ ∧ ψ ) ↔ ( φ ∧ ∃ x ψ ).

    Existential quantifier distributes over conjunction when the first
    conjunct does not contain the bound variable.
    (Contributed by NM, 5-Aug-1993.)
    set.mm proof: wa wex 19.41v exancom ancom 3bitr4i.
    """
    lb = ProofBuilder(sys, "19.42v")

    # 19.41v with swapped variables: ∃ x ( ψ ∧ φ ) ↔ ( ∃ x ψ ∧ φ )
    s_19_41v = lb.ref(
        "s_19_41v",
        "∃ x ( ψ ∧ φ ) ↔ ( ∃ x ψ ∧ φ )",
        ref="19.41v",
        note="19.41v",
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

    # 3bitr4i: ∃ x ( φ ∧ ψ ) ↔ ( φ ∧ ∃ x ψ )
    res = lb.ref(
        "res",
        "∃ x ( φ ∧ ψ ) ↔ ( φ ∧ ∃ x ψ )",
        s_19_41v,
        s_exancom,
        s_ancom,
        ref="3bitr4i",
        note="3bitr4i",
    )
    return lb.build(res)


def prove_trujust(sys: System) -> Proof:
    """trujust: ( ( ∀ x x = x → ∀ x x = x ) ↔ ( ∀ y y = y → ∀ y y = y ) ).

    Two instances of the law of identity with universal quantifiers are
    equivalent; proved via monothetic with ∀x x=x for ph and ∀y y=y for ps.
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "trujust")
    res = lb.ref(
        "res",
        "( ( ∀ x x = x → ∀ x x = x ) ↔ ( ∀ y y = y → ∀ y y = y ) )",
        ref="monothetic",
        note="monothetic",
    )
    return lb.build(res)


def prove_moa1(sys: System) -> Proof:
    """moa1: ( ∃* x ( φ → ψ ) → ∃* x ψ ).

    If there exists at most one x such that φ → ψ, then there exists
    at most one x such that ψ.  The proof uses ax-1 to get ψ → (φ → ψ),
    then applies moimi.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "moa1")
    # ax-1: ψ → (φ → ψ)
    s1 = lb.ref("s1", "ψ → ( φ → ψ )", ref="ax-1", note="ax-1")
    # moimi with ψ → (φ → ψ) as hypothesis
    res = lb.ref(
        "res",
        "( ∃* x ( φ → ψ ) → ∃* x ψ )",
        s1,
        ref="moimi",
        note="moimi ax-1",
    )
    return lb.build(res)


def prove_moimi(sys: System) -> Proof:
    """moimi: ( ∃* x ψ → ∃* x φ ).

    Inference form of moim.  Given φ → ψ, conclude ∃* x ψ → ∃* x φ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "moimi")
    hyp = lb.hyp("moimi.1", "φ → ψ")
    # moim: ∀ x ( φ → ψ ) → ( ∃* x ψ → ∃* x φ )
    s1 = lb.ref(
        "s1",
        "∀ x ( φ → ψ ) → ( ∃* x ψ → ∃* x φ )",
        ref="moim",
        note="moim",
    )
    # mpg: ( ∀ x ( φ → ψ ) → ( ∃* x ψ → ∃* x φ ) ), ( φ → ψ ) ⊢ ( ∃* x ψ → ∃* x φ )
    res = lb.ref(
        "res",
        "( ∃* x ψ → ∃* x φ )",
        s1,
        hyp,
        ref="mpg",
        note="mpg moim, moimi.1",
    )
    return lb.build(res)


def prove_moor(sys: System) -> Proof:
    """moor: ( ∃* x ( φ ∨ ψ ) → ∃* x φ ).

    If "at most one x such that φ ∨ ψ", then "at most one x such
    that φ".  From orc and moimi.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "moor")
    # orc: φ → ( φ ∨ ψ )
    s1 = lb.ref(
        "s1",
        "φ → ( φ ∨ ψ )",
        ref="orc",
        note="orc",
    )
    # moimi with orc as hypothesis
    res = lb.ref(
        "res",
        "( ∃* x ( φ ∨ ψ ) → ∃* x φ )",
        s1,
        ref="moimi",
        note="moimi orc",
    )
    return lb.build(res)


def prove_mooran2(sys: System) -> Proof:
    """mooran2: ( ∃* x ( φ ∨ ψ ) → ( ∃* x φ ∧ ∃* x ψ ) ).

    If there exists at most one x such that φ ∨ ψ, then there
    exists at most one x such that φ and at most one x such that ψ.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "mooran2")
    # moor: ( ∃* x ( φ ∨ ψ ) → ∃* x φ )
    s1 = lb.ref(
        "s1",
        "( ∃* x ( φ ∨ ψ ) → ∃* x φ )",
        ref="moor",
        note="moor",
    )
    # olc: ψ → ( φ ∨ ψ )
    s2 = lb.ref(
        "s2",
        "ψ → ( φ ∨ ψ )",
        ref="olc",
        note="olc",
    )
    # moimi with olc: ( ∃* x ( φ ∨ ψ ) → ∃* x ψ )
    s3 = lb.ref(
        "s3",
        "( ∃* x ( φ ∨ ψ ) → ∃* x ψ )",
        s2,
        ref="moimi",
        note="moimi olc",
    )
    # jca: ( ∃* x ( φ ∨ ψ ) → ( ∃* x φ ∧ ∃* x ψ ) )
    res = lb.ref(
        "res",
        "( ∃* x ( φ ∨ ψ ) → ( ∃* x φ ∧ ∃* x ψ ) )",
        s1,
        s3,
        ref="jca",
        note="jca moor, moimi",
    )
    return lb.build(res)


def prove_ax6e(sys: System) -> Proof:
    """ax6e: ∃ x x = y.

    There exists a set equal to another, with no distinct variable
    restrictions.  The proof uses a fresh variable w and case
    analysis (pm2.61i) to drop the distinct variable condition
    from ax6ev.
    (Contributed by NM, 10-Jan-1993.)
    """
    lb = ProofBuilder(sys, "ax6e")

    # ax6ev: ∃ w w = y
    s1 = lb.ref(
        "s1",
        "∃ w w = y",
        ref="ax6ev",
        note="ax6ev",
    )

    # ax6ev: ∃ x x = w
    s2 = lb.ref(
        "s2",
        "∃ x x = w",
        ref="ax6ev",
        note="ax6ev",
    )

    # equtr: x = w → ( w = y → x = y )
    s3 = lb.ref(
        "s3",
        "x = w → ( w = y → x = y )",
        ref="equtr",
        note="equtr",
    )

    # eximii (s2, s3): ∃ x ( w = y → x = y )
    s4 = lb.ref(
        "s4",
        "∃ x ( w = y → x = y )",
        s2,
        s3,
        ref="eximii",
        note="eximii ax6ev, equtr",
    )

    # 19.35i (s4): ∀ x w = y → ∃ x x = y
    s5 = lb.ref(
        "s5",
        "∀ x w = y → ∃ x x = y",
        s4,
        ref="19.35i",
        note="19.35i eximii",
    )

    # ax13lem1: ¬ x = y → ( w = y → ∀ x w = y )
    s6 = lb.ref(
        "s6",
        "¬ x = y → ( w = y → ∀ x w = y )",
        ref="ax13lem1",
        note="ax13lem1",
    )

    # syl6com (s6, s5): w = y → ( ¬ x = y → ∃ x x = y )
    s7 = lb.ref(
        "s7",
        "w = y → ( ¬ x = y → ∃ x x = y )",
        s6,
        s5,
        ref="syl6com",
        note="syl6com ax13lem1, 19.35i",
    )

    # exlimiiv (s7, s1): ¬ x = y → ∃ x x = y
    s8 = lb.ref(
        "s8",
        "¬ x = y → ∃ x x = y",
        s7,
        s1,
        ref="exlimiiv",
        note="exlimiiv syl6com, ax6ev",
    )

    # 19.8a: x = y → ∃ x x = y
    s9 = lb.ref(
        "s9",
        "x = y → ∃ x x = y",
        ref="19.8a",
        note="19.8a",
    )

    # pm2.61i (s9, s8): ∃ x x = y
    res = lb.ref(
        "res",
        "∃ x x = y",
        s9,
        s8,
        ref="pm2.61i",
        note="pm2.61i 19.8a, exlimiiv",
    )

    return lb.build(res)


def prove_wel(sys: System) -> Proof:
    """wel: wff x ∈ y.

    Membership wff combining cv and wcel.
    (Contributed by NM, 24-Jan-1993.)
    """
    lb = ProofBuilder(sys, "wel")
    s1 = lb.ref("s1", "cv x", ref="cv", note="cv")
    res = lb.ref("res", "cv x e. y", s1, ref="wcel", note="wcel")
    return lb.build(res)


def prove_excom(sys: System) -> Proof:
    """excom: ∃ x ∃ y φ ↔ ∃ y ∃ x φ.

    Commutation of existential quantifiers.
    From alcom, notbii, 2exnaln, and 3bitr4i.
    (Contributed by NM, 5-Aug-1993.)
    """
    lb = ProofBuilder(sys, "excom")
    # alcom with ¬φ: ∀ x ∀ y ¬ φ ↔ ∀ y ∀ x ¬ φ
    s1 = lb.ref(
        "s1",
        "∀ x ∀ y ¬ φ ↔ ∀ y ∀ x ¬ φ",
        ref="alcom",
        note="alcom",
    )
    # notbii: ¬ ∀ x ∀ y ¬ φ ↔ ¬ ∀ y ∀ x ¬ φ
    s2 = lb.ref(
        "s2",
        "¬ ∀ x ∀ y ¬ φ ↔ ¬ ∀ y ∀ x ¬ φ",
        s1,
        ref="notbii",
        note="notbii",
    )
    # 2exnaln: ∃ x ∃ y φ ↔ ¬ ∀ x ∀ y ¬ φ
    s3 = lb.ref(
        "s3",
        "∃ x ∃ y φ ↔ ¬ ∀ x ∀ y ¬ φ",
        ref="2exnaln",
        note="2exnaln",
    )
    # 2exnaln with x and y swapped: ∃ y ∃ x φ ↔ ¬ ∀ y ∀ x ¬ φ
    s4 = lb.ref(
        "s4",
        "∃ y ∃ x φ ↔ ¬ ∀ y ∀ x ¬ φ",
        ref="2exnaln",
        note="2exnaln",
    )
    # 3bitr4i: ∃ x ∃ y φ ↔ ∃ y ∃ x φ
    res = lb.ref(
        "res",
        "∃ x ∃ y φ ↔ ∃ y ∃ x φ",
        s2,
        s3,
        s4,
        ref="3bitr4i",
        note="3bitr4i",
    )
    return lb.build(res)


# New predicate migrations are registered beside their implementations.  The
# central theorem module retains only the frozen legacy registry and aggregates
# this map with duplicate detection.


def prove_mo4(sys: System) -> Proof:
    """mo4: ∃* x φ ↔ ∀ x ∀ y ( ( φ ∧ ψ ) → x = y ).

    At-most-one quantifier expressed using implicit substitution.
    Given mo4.1: x = y → (φ ↔ ψ).
    (Contributed by NM, 26-Jul-1995.)
    """
    lb = ProofBuilder(sys, "mo4")
    hyp = lb.hyp("mo4.1", "x = y → ( φ ↔ ψ )")

    # dfmo: ∃* x φ ↔ ∃ z ∀ x ( φ → x = z )
    s_dfmo = lb.ref(
        "s_dfmo",
        "∃* x φ ↔ ∃ z ∀ x ( φ → x = z )",
        ref="dfmo",
        note="dfmo",
    )

    # equequ1: x = y → ( x = z ↔ y = z )
    s_equ = lb.ref(
        "s_equ",
        "x = y → ( x = z ↔ y = z )",
        ref="equequ1",
        note="equequ1",
    )

    # imbi12d: x = y → ( ( φ → x = z ) ↔ ( ψ → y = z ) )
    s_imbi = lb.ref(
        "s_imbi",
        "x = y → ( ( φ → x = z ) ↔ ( ψ → y = z ) )",
        hyp,
        s_equ,
        ref="imbi12d",
        note="imbi12d mo4.1, equequ1",
    )

    # cbvalvw: (∀ x ( φ → x = z ) ↔ ∀ y ( ψ → y = z ))
    s_cbval = lb.ref(
        "s_cbval",
        "( ∀ x ( φ → x = z ) ↔ ∀ y ( ψ → y = z ) )",
        s_imbi,
        ref="cbvalvw",
        note="cbvalvw",
    )

    # biimpi: forward direction ∀ x ( φ → x = z ) → ∀ y ( ψ → y = z )
    s_bifwd = lb.ref(
        "s_bifwd",
        "∀ x ( φ → x = z ) → ∀ y ( ψ → y = z )",
        s_cbval,
        ref="biimpi",
        note="biimpi cbvalvw",
    )

    # Forward chain
    # pm2.27: φ → ( ( φ → x = z ) → x = z )
    s_fw_pm1 = lb.ref(
        "s_fw_pm1",
        "φ → ( ( φ → x = z ) → x = z )",
        ref="pm2.27",
        note="pm2.27",
    )

    # pm2.27: ψ → ( ( ψ → y = z ) → y = z )
    s_fw_pm2 = lb.ref(
        "s_fw_pm2",
        "ψ → ( ( ψ → y = z ) → y = z )",
        ref="pm2.27",
        note="pm2.27",
    )

    # im2anan9: combine the two pm2.27 results with nested implication
    s_fw_im2 = lb.ref(
        "s_fw_im2",
        "( φ ∧ ψ ) → ( ( ( φ → x = z ) ∧ ( ψ → y = z ) ) → ( x = z ∧ y = z ) )",
        s_fw_pm1,
        s_fw_pm2,
        ref="im2anan9",
        note="im2anan9 pm2.27, pm2.27",
    )

    # equtr2: ( x = z ∧ y = z ) → x = y
    s_fw_eq = lb.ref(
        "s_fw_eq",
        "( x = z ∧ y = z ) → x = y",
        ref="equtr2",
        note="equtr2",
    )

    # syl6com
    s_fw_syl = lb.ref(
        "s_fw_syl",
        "( ( φ → x = z ) ∧ ( ψ → y = z ) ) → ( ( φ ∧ ψ ) → x = y )",
        s_fw_im2,
        s_fw_eq,
        ref="syl6com",
        note="syl6com im2anan9, equtr2",
    )

    # ex: exportation
    s_fw_ex = lb.ref(
        "s_fw_ex",
        "( φ → x = z ) → ( ( ψ → y = z ) → ( ( φ ∧ ψ ) → x = y ) )",
        s_fw_syl,
        ref="ex",
        note="ex syl6com",
    )

    # alimdv with y
    s_fw_al1 = lb.ref(
        "s_fw_al1",
        "( φ → x = z ) → ( ∀ y ( ψ → y = z ) → ∀ y ( ( φ ∧ ψ ) → x = y ) )",
        s_fw_ex,
        ref="alimdv",
        note="alimdv",
    )

    # com12
    s_fw_com = lb.ref(
        "s_fw_com",
        "∀ y ( ψ → y = z ) → ( ( φ → x = z ) → ∀ y ( ( φ ∧ ψ ) → x = y ) )",
        s_fw_al1,
        ref="com12",
        note="com12 alimdv",
    )

    # alimdv with x
    s_fw_al2 = lb.ref(
        "s_fw_al2",
        "∀ y ( ψ → y = z ) → ( ∀ x ( φ → x = z ) → ∀ x ∀ y ( ( φ ∧ ψ ) → x = y ) )",
        s_fw_com,
        ref="alimdv",
        note="alimdv",
    )

    # mpcom: combine with s_bifwd
    s_fw_mpc = lb.ref(
        "s_fw_mpc",
        "∀ x ( φ → x = z ) → ∀ x ∀ y ( ( φ ∧ ψ ) → x = y )",
        s_bifwd,
        s_fw_al2,
        ref="mpcom",
        note="mpcom biimpi, alimdv",
    )

    # exlimiv: ∃ z ∀ x ( φ → x = z ) → ∀ x ∀ y ( ( φ ∧ ψ ) → x = y )
    s_fw_exl = lb.ref(
        "s_fw_exl",
        "∃ z ∀ x ( φ → x = z ) → ∀ x ∀ y ( ( φ ∧ ψ ) → x = y )",
        s_fw_mpc,
        ref="exlimiv",
        note="exlimiv mpcom",
    )

    # sylbi: combine with dfmo → forward direction
    s_fwd = lb.ref(
        "s_fwd",
        "∃* x φ → ∀ x ∀ y ( ( φ ∧ ψ ) → x = y )",
        s_dfmo,
        s_fw_exl,
        ref="sylbi",
        note="sylbi dfmo, exlimiv",
    )

    # Reverse chain
    # cbvexvw with mo4.1
    s_rev_cbv = lb.ref(
        "s_rev_cbv",
        "( ∃ x φ ↔ ∃ y ψ )",
        hyp,
        ref="cbvexvw",
        note="cbvexvw mo4.1",
    )

    # biimpri: ∃ y ψ → ∃ x φ
    s_rev_bii = lb.ref(
        "s_rev_bii",
        "∃ y ψ → ∃ x φ",
        s_rev_cbv,
        ref="biimpri",
        note="biimpri cbvexvw",
    )

    # ax6evr: ∃ z x = z
    s_rev_ax6 = lb.ref(
        "s_rev_ax6",
        "∃ z x = z",
        ref="ax6evr",
        note="ax6evr",
    )

    # pm3.2: φ → ( ψ → ( φ ∧ ψ ) )
    s_rev_pm3 = lb.ref(
        "s_rev_pm3",
        "φ → ( ψ → ( φ ∧ ψ ) )",
        ref="pm3.2",
        note="pm3.2",
    )

    # imim1d
    s_rev_im1 = lb.ref(
        "s_rev_im1",
        "φ → ( ( ( φ ∧ ψ ) → x = y ) → ( ψ → x = y ) )",
        s_rev_pm3,
        ref="imim1d",
        note="imim1d pm3.2",
    )

    # ax7: x = y → ( x = z → y = z )
    s_rev_ax7 = lb.ref(
        "s_rev_ax7",
        "x = y → ( x = z → y = z )",
        ref="ax7",
        note="ax7",
    )

    # syl8
    s_rev_sy8 = lb.ref(
        "s_rev_sy8",
        "φ → ( ( ( φ ∧ ψ ) → x = y ) → ( ψ → ( x = z → y = z ) ) )",
        s_rev_im1,
        s_rev_ax7,
        ref="syl8",
        note="syl8 imim1d, ax7",
    )

    # com4r
    s_rev_c4r = lb.ref(
        "s_rev_c4r",
        "x = z → ( φ → ( ( ( φ ∧ ψ ) → x = y ) → ( ψ → y = z ) ) )",
        s_rev_sy8,
        ref="com4r",
        note="com4r syl8",
    )

    # impcom
    s_rev_imc = lb.ref(
        "s_rev_imc",
        "( φ ∧ x = z ) → ( ( ( φ ∧ ψ ) → x = y ) → ( ψ → y = z ) )",
        s_rev_c4r,
        ref="impcom",
        note="impcom com4r",
    )

    # alimdv with y
    s_rev_al1 = lb.ref(
        "s_rev_al1",
        "( φ ∧ x = z ) → ( ∀ y ( ( φ ∧ ψ ) → x = y ) → ∀ y ( ψ → y = z ) )",
        s_rev_imc,
        ref="alimdv",
        note="alimdv",
    )

    # impancom
    s_rev_ipc = lb.ref(
        "s_rev_ipc",
        "( φ ∧ ∀ y ( ( φ ∧ ψ ) → x = y ) ) → ( x = z → ∀ y ( ψ → y = z ) )",
        s_rev_al1,
        ref="impancom",
        note="impancom alimdv",
    )

    # eximdv with z
    s_rev_exd = lb.ref(
        "s_rev_exd",
        "( φ ∧ ∀ y ( ( φ ∧ ψ ) → x = y ) ) → ( ∃ z x = z → ∃ z ∀ y ( ψ → y = z ) )",
        s_rev_ipc,
        ref="eximdv",
        note="eximdv impancom",
    )

    # mpi: combine with ax6evr
    s_rev_mpi = lb.ref(
        "s_rev_mpi",
        "( φ ∧ ∀ y ( ( φ ∧ ψ ) → x = y ) ) → ∃ z ∀ y ( ψ → y = z )",
        s_rev_ax6,
        s_rev_exd,
        ref="mpi",
        note="mpi ax6evr, eximdv",
    )

    # dfmo for ψ
    s_rev_dmo = lb.ref(
        "s_rev_dmo",
        "∃* y ψ ↔ ∃ z ∀ y ( ψ → y = z )",
        ref="dfmo",
        note="dfmo",
    )

    # sylibr
    s_rev_slb = lb.ref(
        "s_rev_slb",
        "( φ ∧ ∀ y ( ( φ ∧ ψ ) → x = y ) ) → ∃* y ψ",
        s_rev_mpi,
        s_rev_dmo,
        ref="sylibr",
        note="sylibr mpi, dfmo",
    )

    # expcom
    s_rev_exp = lb.ref(
        "s_rev_exp",
        "∀ y ( ( φ ∧ ψ ) → x = y ) → ( φ → ∃* y ψ )",
        s_rev_slb,
        ref="expcom",
        note="expcom sylibr",
    )

    # aleximi: apply directly to s_rev_exp
    s_rev_syl = lb.ref(
        "s_rev_syl",
        "∀ x ∀ y ( ( φ ∧ ψ ) → x = y ) → ( ∃ x φ → ∃ x ∃* y ψ )",
        s_rev_exp,
        ref="aleximi",
        note="aleximi expcom",
    )

    # ax5e
    s_rev_a5e = lb.ref(
        "s_rev_a5e",
        "∃ x ∃* y ψ → ∃* y ψ",
        ref="ax5e",
        note="ax5e",
    )

    # syl56: combine reverse chain
    s_rev_s56 = lb.ref(
        "s_rev_s56",
        "∀ x ∀ y ( ( φ ∧ ψ ) → x = y ) → ( ∃ y ψ → ∃* y ψ )",
        s_rev_bii,
        s_rev_syl,
        s_rev_a5e,
        ref="syl56",
        note="syl56 biimpri, aleximi, ax5e",
    )

    # Second cbvalvw chain for 3bitr4i
    s_exb = lb.ref(
        "s_exb",
        "( ∃ z ∀ x ( φ → x = z ) ↔ ∃ z ∀ y ( ψ → y = z ) )",
        s_cbval,
        ref="exbii",
        note="exbii cbvalvw",
    )

    # 3bitr4i
    s_3b4 = lb.ref(
        "s_3b4",
        "∃* x φ ↔ ∃* y ψ",
        s_exb,
        s_dfmo,
        s_rev_dmo,
        ref="3bitr4i",
        note="3bitr4i exbii, dfmo, dfmo",
    )

    # moabs
    s_moab = lb.ref(
        "s_moab",
        "∃* y ψ ↔ ( ∃ y ψ → ∃* y ψ )",
        ref="moabs",
        note="moabs",
    )

    # bitri
    s_bitr = lb.ref(
        "s_bitr",
        "∃* x φ ↔ ( ∃ y ψ → ∃* y ψ )",
        s_3b4,
        s_moab,
        ref="bitri",
        note="bitri 3bitr4i, moabs",
    )

    # sylibr: complete reverse direction
    s_rev = lb.ref(
        "s_rev",
        "∀ x ∀ y ( ( φ ∧ ψ ) → x = y ) → ∃* x φ",
        s_rev_s56,
        s_bitr,
        ref="sylibr",
        note="sylibr syl56, bitri",
    )

    # impbii: combine forward and reverse
    res = lb.ref(
        "res",
        "∃* x φ ↔ ∀ x ∀ y ( ( φ ∧ ψ ) → x = y )",
        s_fwd,
        s_rev,
        ref="impbii",
        note="impbii",
    )

    return lb.build(res)


def prove_nfeqf2(sys: System) -> Proof:
    """nfeqf2: ¬ ∀ x x = y → Ⅎ x z = y.

    An equation between setvars is free of any other setvar,
    given a distinctor.
    (Contributed by Wolf Lammen, 9-Jun-2019.)
    """
    lb = ProofBuilder(sys, "nfeqf2")

    # exnal: ∃ x ¬ x = y ↔ ¬ ∀ x x = y
    s_exnal = lb.ref(
        "s_exnal",
        "∃ x ¬ x = y ↔ ¬ ∀ x x = y",
        ref="exnal",
        note="exnal",
    )

    # hbe1: ∃ x z = y → ∀ x ∃ x z = y
    s_hbe1 = lb.ref(
        "s_hbe1",
        "∃ x z = y → ∀ x ∃ x z = y",
        ref="hbe1",
        note="hbe1",
    )

    # ax13lem2: ¬ x = y → ( ∃ x z = y → z = y )
    s_ax13lem2 = lb.ref(
        "s_ax13lem2",
        "¬ x = y → ( ∃ x z = y → z = y )",
        ref="ax13lem2",
        note="ax13lem2",
    )

    # ax13lem1: ¬ x = y → ( z = y → ∀ x z = y )
    s_ax13lem1 = lb.ref(
        "s_ax13lem1",
        "¬ x = y → ( z = y → ∀ x z = y )",
        ref="ax13lem1",
        note="ax13lem1",
    )

    # syldc: ∃ x z = y → ( ¬ x = y → ∀ x z = y )
    s_syldc = lb.ref(
        "s_syldc",
        "∃ x z = y → ( ¬ x = y → ∀ x z = y )",
        s_ax13lem2,
        s_ax13lem1,
        ref="syldc",
        note="syldc ax13lem2, ax13lem1",
    )

    # eximdh: ∃ x z = y → ( ∃ x ¬ x = y → ∃ x ∀ x z = y )
    s_eximdh = lb.ref(
        "s_eximdh",
        "∃ x z = y → ( ∃ x ¬ x = y → ∃ x ∀ x z = y )",
        s_hbe1,
        s_syldc,
        ref="eximdh",
        note="eximdh hbe1, syldc",
    )

    # hbe1a: ∃ x ∀ x z = y → ∀ x z = y
    s_hbe1a = lb.ref(
        "s_hbe1a",
        "∃ x ∀ x z = y → ∀ x z = y",
        ref="hbe1a",
        note="hbe1a",
    )

    # syl6com: ∃ x ¬ x = y → ( ∃ x z = y → ∀ x z = y )
    s_syl6com = lb.ref(
        "s_syl6com",
        "∃ x ¬ x = y → ( ∃ x z = y → ∀ x z = y )",
        s_eximdh,
        s_hbe1a,
        ref="syl6com",
        note="syl6com eximdh, hbe1a",
    )

    # nfd: ∃ x ¬ x = y → Ⅎ x z = y
    s_nfd = lb.ref(
        "s_nfd",
        "∃ x ¬ x = y → Ⅎ x z = y",
        s_syl6com,
        ref="nfd",
        note="nfd syl6com",
    )

    # sylbir: ¬ ∀ x x = y → Ⅎ x z = y
    res = lb.ref(
        "res",
        "¬ ∀ x x = y → Ⅎ x z = y",
        s_exnal,
        s_nfd,
        ref="sylbir",
        note="sylbir exnal, nfd",
    )

    return lb.build(res)


def prove_sbequ2(sys: System) -> Proof:
    """sbequ2: x = t → ( [ t / x ] φ → φ ).

    An equality theorem for substitution.
    (Contributed by NM, 16-May-1993.)
    set.mm proof: wsb weq wex wi wa dfsbimp equvinva equcomi sp imim12i impcomd
    syl2im wal aleximi ax5e syl6com.
    """
    lb = ProofBuilder(sys, "sbequ2")

    # dfsbimp: [ t x φ → ∀ y ( y = t → ∀ x ( x = y → φ ) )
    s1 = lb.ref(
        "s1",
        "[ t x φ → ∀ y ( y = t → ∀ x ( x = y → φ ) )",
        ref="dfsbimp",
        note="dfsbimp",
    )

    # equvinva: x = t → ∃ y ( x = y ∧ t = y )
    s2 = lb.ref(
        "s2",
        "x = t → ∃ y ( x = y ∧ t = y )",
        ref="equvinva",
        note="equvinva",
    )

    # equcomi: t = y → y = t
    s3 = lb.ref(
        "s3",
        "t = y → y = t",
        ref="equcomi",
        note="equcomi",
    )

    # sp: ∀ x ( x = y → φ ) → ( x = y → φ )
    s4 = lb.ref(
        "s4",
        "∀ x ( x = y → φ ) → ( x = y → φ )",
        ref="sp",
        note="sp",
    )

    # imim12i s3, s4: ( y = t → ∀ x ( x = y → φ ) ) → ( t = y → ( x = y → φ ) )
    s5 = lb.ref(
        "s5",
        "( y = t → ∀ x ( x = y → φ ) ) → ( t = y → ( x = y → φ ) )",
        s3,
        s4,
        ref="imim12i",
        note="imim12i equcomi, sp",
    )

    # impcomd s5: ( y = t → ∀ x ( x = y → φ ) ) → ( ( x = y ∧ t = y ) → φ )
    s6 = lb.ref(
        "s6",
        "( y = t → ∀ x ( x = y → φ ) ) → ( ( x = y ∧ t = y ) → φ )",
        s5,
        ref="impcomd",
        note="impcomd imim12i",
    )

    # aleximi s6: ∀ y ( y = t → ∀ x ( x = y → φ ) ) → ( ∃ y ( x = y ∧ t = y ) → ∃ y φ )
    s7 = lb.ref(
        "s7",
        "∀ y ( y = t → ∀ x ( x = y → φ ) ) → ( ∃ y ( x = y ∧ t = y ) → ∃ y φ )",
        s6,
        ref="aleximi",
        note="aleximi impcomd",
    )

    # syl2im s1, s2, s7: [ t x φ → ( x = t → ∃ y φ )
    s8 = lb.ref(
        "s8",
        "[ t x φ → ( x = t → ∃ y φ )",
        s1,
        s2,
        s7,
        ref="syl2im",
        note="syl2im dfsbimp, equvinva, aleximi",
    )

    # ax5e: ∃ y φ → φ
    s9 = lb.ref(
        "s9",
        "∃ y φ → φ",
        ref="ax5e",
        note="ax5e",
    )

    # syl6com s8, s9: x = t → ( [ t x φ → φ )
    res = lb.ref(
        "res",
        "x = t → ( [ t x φ → φ )",
        s8,
        s9,
        ref="syl6com",
        note="syl6com syl2im, ax5e",
    )

    return lb.build(res)


def prove_sbco4(sys: System) -> Proof:
    """sbco4: ( [ y / u ] [ x / v ] [ u / x ] [ v / y ] φ ↔ [ x / w ] [ y / x ] [ w / y ] φ ).

    Substitution biconditional commutativity via sbco4lem and 3bitri.
    (Contributed by NM, 26-Sep-1993.)
    """
    lb = ProofBuilder(sys, "sbco4")

    # Step 1: sbequ: u = y → ( [ u / x ] [ v / y ] φ ↔ [ y / x ] [ v / y ] φ )
    s1 = lb.ref(
        "s1",
        "u = y → ( [ u x [ v y φ ↔ [ y x [ v y φ )",
        ref="sbequ",
        note="sbequ",
    )

    # Step 2: sbbidv: u = y → ( [ x / v ] [ u / x ] [ v / y ] φ ↔ [ x / v ] [ y / x ] [ v / y ] φ )
    s2 = lb.ref(
        "s2",
        "u = y → ( [ x v [ u x [ v y φ ↔ [ x v [ y x [ v y φ )",
        s1,
        ref="sbbidv",
        note="sbbidv",
    )

    # Step 3: sbievw: [ y / u ] [ x / v ] [ u / x ] [ v / y ] φ ↔ [ x / v ] [ y / x ] [ v / y ] φ
    s3 = lb.ref(
        "s3",
        "( [ y u [ x v [ u x [ v y φ ↔ [ x v [ y x [ v y φ )",
        s2,
        ref="sbievw",
        note="sbievw",
    )

    # Step 4: sbco4lem: [ x / v ] [ y / x ] [ v / y ] φ ↔ [ x / t ] [ y / x ] [ t / y ] φ
    s4 = lb.ref(
        "s4",
        "( [ x v [ y x [ v y φ ↔ [ x t [ y x [ t y φ )",
        ref="sbco4lem",
        note="sbco4lem",
    )

    # Step 5: sbco4lem: [ x / t ] [ y / x ] [ t / y ] φ ↔ [ x / w ] [ y / x ] [ w / y ] φ
    s5 = lb.ref(
        "s5",
        "( [ x t [ y x [ t y φ ↔ [ x w [ y x [ w y φ )",
        ref="sbco4lem",
        note="sbco4lem",
    )

    # Step 6: 3bitri s3, s4, s5 → conclusion
    res = lb.ref(
        "res",
        "( [ y u [ x v [ u x [ v y φ ↔ [ x w [ y x [ w y φ )",
        s3,
        s4,
        s5,
        ref="3bitri",
        note="3bitri",
    )

    return lb.build(res)


MIGRATION_THEOREMS: Mapping[str, PredicateTheoremCtor] = {
    "alim": prove_alim,
    "alimi": prove_alimi,
    "2alimi": prove_2alimi,
    "al2im": prove_al2im,
    "al2imi": prove_al2imi,
    "alimdh": prove_alimdh,
    "alimdv": prove_alimdv,
    "2alimdv": prove_2alimdv,
    "alrimdh": prove_alrimdh,
    "alrimdv": prove_alrimdv,
    "alrimih": prove_alrimih,
    "alrimiv": prove_alrimiv,
    "alrimivv": prove_alrimivv,
    "ax5d": prove_ax5d,
    "ax6v": prove_ax6v,
    "ax7v": prove_ax7v,
    "ax7v1": prove_ax7v1,
    "ax7v2": prove_ax7v2,
    "equid": prove_equid,
    "ax8v": prove_ax8v,
    "ax8v1": prove_ax8v1,
    "ax8v2": prove_ax8v2,
    "ax9v": prove_ax9v,
    "ax9v1": prove_ax9v1,
    "ax9v2": prove_ax9v2,
    "ax12v": prove_ax12v,
    "ax13w": prove_ax13w,
    "gen2": prove_gen2,
    "sylg": prove_sylg,
    "sylgt": prove_sylgt,
    "nfrd": prove_nfrd,
    "nfs1f": prove_nfs1f,
    "nfnbi": prove_nfnbi,
    "nfnt": prove_nfnt,
    "nfbid": prove_nfbid,
    "nfa1": prove_nfa1,
    "mpgbi": prove_mpgbi,
    "stdpc5v": prove_stdpc5v,
    "stdpc7": prove_stdpc7,
    "hbe1a": prove_hbe1a,
    "alcom": prove_alcom,
    "alcoms": prove_alcoms,
    "ala1": prove_ala1,
    "hbth": prove_hbth,
    "hbal": prove_hbal,
    "hbald": prove_hbald,
    "hban": prove_hban,
    "exsbim": prove_exsbim,
    "sbimi": prove_sbimi,
    "sbimd": prove_sbimd,
    "sbequ2": prove_sbequ2,
    "spvw": prove_spvw,
    "19.21t": prove_19_21t,
    "19.21bi": prove_19_21bi,
    "19.2g": prove_19_2g,
    "19.37v": prove_19_37v,
    "calemos": prove_calemos,
    "darapti": prove_darapti,
    "19.41v": prove_19_41v,
    "19.41vv": prove_19_41vv,
    "19.42v": prove_19_42v,
    "19.8a": prove_19_8a,
    "19.8ad": prove_19_8ad,
    "2exnaln": prove_2exnaln,
    "ax12i": prove_ax12i,
    "ax12w": prove_ax12w,
    "ax12wlem": prove_ax12wlem,
    "ax6e": prove_ax6e,
    "excom": prove_excom,
    "mo4": prove_mo4,
    "moa1": prove_moa1,
    "moimi": prove_moimi,
    "moor": prove_moor,
    "mooran2": prove_mooran2,
    "nfim1": prove_nfim1,
    "nfan1": prove_nfan1,
    "nfeqf2": prove_nfeqf2,
    "nf5d": prove_nf5d,
    "sp": prove_sp,
    "spi": prove_spi,
    "sps": prove_sps,
    "sbco4": prove_sbco4,
    "trujust": prove_trujust,
    "wel": prove_wel,
    "sblbis": prove_sblbis,
    "sbrbis": prove_sbrbis,
}
