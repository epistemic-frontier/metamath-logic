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


LemmaCtor = Callable[[System], Proof]

THEOREMS: Mapping[str, LemmaCtor] = {}

__all__ = ["LemmaCtor", "THEOREMS"]
