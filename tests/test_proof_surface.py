from __future__ import annotations

import importlib

import pytest

from logic.propositional.hilbert import System
from logic.propositional.hilbert.theorems import SETMM_TO_HILBERT_LEMMAS
from skfd.core.symbols import SymbolInterner
from skfd.names import NameResolver


def test_hilbert_registry_reports_known_unresolved_surface() -> None:
    proof_mod = importlib.import_module("skfd.proof")
    validate = getattr(proof_mod, "validate_proof_registry", None)
    if validate is None:
        pytest.skip("proof-scaffold does not provide validate_proof_registry")

    system = System.make(interner=SymbolInterner(), names=NameResolver())
    result = validate(
        system=system,
        constructors=SETMM_TO_HILBERT_LEMMAS,
        axioms=system.compile_axioms(),
        reserved={"wi", "wn", "wa", "mp"},
    )

    # The registry is not fully clean: syl5com has a known construction bug
    # ("mp: antecedent mismatch"), reported as a constructor_error.
    constructor_errors = sorted(
        issue.lemma for issue in result.issues if issue.kind == "constructor_error"
    )
    assert "syl5com" in constructor_errors
    assert result.ok is False
