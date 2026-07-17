"""Hand-authored semantic proof canaries and their legacy compatibility facade."""

from __future__ import annotations

from prelude.formula import GLOBAL_PRELUDE_MODULE_ID
from prelude.metamath_binding import (
    SETMM_IMP_TOKEN,
    SETMM_LPAREN_TOKEN,
    SETMM_RPAREN_TOKEN,
)
from skfd.authoring.assertion import AssertionSignature, ElaboratedProof
from skfd.authoring.ids import AssertionSemanticId, OwnerId, ProofId
from skfd.authoring.judgment import Judgment
from skfd.authoring.legacy_replay import LegacyReplayBinding, lower_semantic_replay_plan
from skfd.authoring.proof_author import ProofAuthor
from skfd.authoring.replay import build_semantic_replay_plan
from skfd.authoring.term import VariableRef
from skfd.proof import Proof

from ._system import System
from .calculus import CALCULUS, PROVABLE
from .language import LANGUAGE, WFF, WFF_VARIABLE, Imp
from .metamath_binding import SETMM_MP_REPLAY_BINDING, SETMM_PROP_BINDING
from .rules import ASSERTION_CATALOG, MP_ASSERTION, PROP_CORE_PROFILE

MP2B_ASSERTION_ID = AssertionSemanticId("metamath-logic/prop#assertion:mp2b")
_MP2B_OWNER = OwnerId(str(MP2B_ASSERTION_ID))
_MP2B_PHI_REF = VariableRef("schema", _MP2B_OWNER, "phi", WFF_VARIABLE)
_MP2B_PSI_REF = VariableRef("schema", _MP2B_OWNER, "psi", WFF_VARIABLE)
_MP2B_CHI_REF = VariableRef("schema", _MP2B_OWNER, "chi", WFF_VARIABLE)
_MP2B_PHI = LANGUAGE.variable(_MP2B_PHI_REF)
_MP2B_PSI = LANGUAGE.variable(_MP2B_PSI_REF)
_MP2B_CHI = LANGUAGE.variable(_MP2B_CHI_REF)

MP2B_SIGNATURE = AssertionSignature(
    id=MP2B_ASSERTION_ID,
    canonical_label="mp2b",
    kind="theorem",
    schema_variables=(_MP2B_PHI_REF, _MP2B_PSI_REF, _MP2B_CHI_REF),
    premises=(
        Judgment(PROVABLE, (_MP2B_PHI,)),
        Judgment(PROVABLE, (Imp(_MP2B_PHI, _MP2B_PSI),)),
        Judgment(PROVABLE, (Imp(_MP2B_PSI, _MP2B_CHI),)),
    ),
    conclusion=Judgment(PROVABLE, (_MP2B_CHI,)),
)


def author_mp2b() -> ElaboratedProof:
    proof = ProofAuthor(
        MP2B_SIGNATURE,
        proof_id=ProofId("metamath-logic/prop#proof:mp2b"),
        calculus=CALCULUS,
        catalog=ASSERTION_CATALOG,
        profile=PROP_CORE_PROFILE,
    )
    h_phi, h_phi_psi, h_psi_chi = proof.hypotheses
    psi = proof.use(MP_ASSERTION, h_phi, h_phi_psi)
    chi = proof.use(MP_ASSERTION, psi, h_psi_chi)
    return proof.qed(chi)


MP2B_PROOF = author_mp2b()
_MP2B_REPLAY = build_semantic_replay_plan(
    MP2B_PROOF,
    CALCULUS,
    ASSERTION_CATALOG,
    PROP_CORE_PROFILE,
)


def prove_mp2b(sys: System) -> Proof:
    """Lower the semantic double-modus-ponens proof to the legacy proof ABI."""
    variables = {
        reference: sys.interner.intern(
            origin_module_id=GLOBAL_PRELUDE_MODULE_ID,
            local_name=name,
            kind="Var",
            origin_ref=0,
        )
        for reference, name in (
            (_MP2B_PHI_REF, "ph"),
            (_MP2B_PSI_REF, "ps"),
            (_MP2B_CHI_REF, "ch"),
        )
    }
    return lower_semantic_replay_plan(
        _MP2B_REPLAY,
        LegacyReplayBinding(
            language=SETMM_PROP_BINDING,
            provable_judgment=PROVABLE,
            assertions=(SETMM_MP_REPLAY_BINDING,),
            token_symbols={
                SETMM_LPAREN_TOKEN: sys.builtins.lp,
                SETMM_IMP_TOKEN: sys.builtins.imp,
                SETMM_RPAREN_TOKEN: sys.builtins.rp,
            },
            variable_symbols=variables,
            legacy_sorts={WFF: "wff"},
            symbol_table=sys.interner.symbol_table(),
        ),
        proof_name="mp2b",
    )


__all__ = [
    "MP2B_ASSERTION_ID",
    "MP2B_PROOF",
    "MP2B_SIGNATURE",
    "author_mp2b",
    "prove_mp2b",
]
