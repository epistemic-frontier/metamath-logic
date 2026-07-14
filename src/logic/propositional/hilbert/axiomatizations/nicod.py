"""Nicod axiomatization skeleton.

set.mm ranges:
    - Derive Nicod's axiom from the standard axioms starts at line 13365.
    - Derive the Lukasiewicz axioms from Nicod's axiom starts at line 13446.
    - Derive Nicod's axiom from Lukasiewicz's first Sheffer stroke axiom starts
      at line 13628.

Scope:
    Reserve this module for Nicod-style single-axiom material and the bridge
    proofs between Nicod, Lukasiewicz, and the standard Hilbert axioms.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping

from skfd.proof import Proof, ProofBuilder

from .. import System

LemmaCtor = Callable[[System], Proof]


def prove_nic_dfneg(sys: System) -> Proof:
    """nic-dfneg: ( ( φ ⊼ φ ) ⊼ ¬ φ ) ⊼ ( ( ( φ ⊼ φ ) ⊼ ( φ ⊼ φ ) ) ⊼ ( ¬ φ ⊼ ¬ φ ) ).

    Nicod's definition of negation in terms of NAND.  Derived from nannot,
    bicomi, nanbi, and mpbi.
    """
    lb = ProofBuilder(sys, "nic-dfneg")

    # nannot: ¬ φ ↔ ( φ ⊼ φ )
    s1 = lb.ref(
        "s1",
        "¬ φ ↔ ( φ ⊼ φ )",
        ref="nannot",
        note="nannot",
    )

    # bicomi on s1: ( φ ⊼ φ ) ↔ ¬ φ
    s2 = lb.ref(
        "s2",
        "( φ ⊼ φ ) ↔ ¬ φ",
        s1,
        ref="bicomi",
        note="bicomi",
    )

    # nanbi with φ := ( φ ⊼ φ ), ψ := ¬ φ
    s3 = lb.ref(
        "s3",
        "( ( φ ⊼ φ ) ↔ ¬ φ ) ↔ ( ( ( φ ⊼ φ ) ⊼ ( ¬ φ ) ) ⊼ ( ( ( φ ⊼ φ ) ⊼ ( φ ⊼ φ ) ) ⊼ ( ( ¬ φ ) ⊼ ( ¬ φ ) ) ) )",
        ref="nanbi",
        note="nanbi",
    )

    # mpbi on s2 (minor) and s3 (major: biconditional)
    res = lb.ref(
        "res",
        "( ( φ ⊼ φ ) ⊼ ( ¬ φ ) ) ⊼ ( ( ( φ ⊼ φ ) ⊼ ( φ ⊼ φ ) ) ⊼ ( ( ¬ φ ) ⊼ ( ¬ φ ) ) )",
        s2,
        s3,
        ref="mpbi",
        note="mpbi",
    )

    return lb.build(res)


THEOREMS: Mapping[str, LemmaCtor] = {
    "nic-dfneg": prove_nic_dfneg,
}

__all__ = ["LemmaCtor", "THEOREMS", "prove_nic_dfneg"]
