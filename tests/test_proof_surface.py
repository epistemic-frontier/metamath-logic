from __future__ import annotations

import importlib

import pytest
from skfd.core.symbols import SymbolInterner
from skfd.names import NameResolver

from logic.predicate.hilbert.theorems import SETMM_TO_PREDICATE_THEOREMS
from logic.propositional.hilbert import System, _extend_names
from logic.propositional.hilbert import make as make_system
from logic.propositional.hilbert.theorems import SETMM_TO_HILBERT_LEMMAS


def test_propositional_and_predicate_registries_are_disjoint() -> None:
    assert set(SETMM_TO_HILBERT_LEMMAS).isdisjoint(SETMM_TO_PREDICATE_THEOREMS)


def test_build_names_cover_all_propositional_variables() -> None:
    system = System.make(
        interner=SymbolInterner(),
        names=_extend_names(NameResolver()),
    )

    for label in ("impsingle-step15", "impsingle-step18", "impsingle-step20"):
        SETMM_TO_HILBERT_LEMMAS[label](system)


def test_hilbert_registry_validates_cleanly() -> None:
    proof_mod = importlib.import_module("skfd.proof")
    validate = getattr(proof_mod, "validate_proof_registry", None)
    if validate is None:
        pytest.skip("proof-scaffold does not provide validate_proof_registry")

    system = make_system(interner=SymbolInterner())
    result = validate(
        system=system,
        constructors=SETMM_TO_HILBERT_LEMMAS,
        axioms=system.compile_axioms(),
        reserved={"wi", "wn", "wa", "mp", "df-fal", "df-nor", "df-xor"},
    )

    assert not result.issues, [(issue.kind, issue.lemma, issue.ref) for issue in result.issues]
