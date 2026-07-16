from __future__ import annotations

import importlib

import pytest
from skfd.core.symbols import SymbolInterner
from skfd.names import NameResolver

from logic.fol import THEOREMS as FOL_THEOREMS
from logic.prop import THEOREMS as PROP_THEOREMS
from logic.prop import System as PropositionalSystem
from logic.prop import make as make_system
from logic.prop._system import _extend_names


def test_propositional_and_predicate_registries_are_disjoint() -> None:
    assert set(PROP_THEOREMS).isdisjoint(FOL_THEOREMS)


def test_build_names_cover_all_propositional_variables() -> None:
    system = PropositionalSystem.make(
        interner=SymbolInterner(),
        names=_extend_names(NameResolver()),
    )

    for label in ("impsingle-step15", "impsingle-step18", "impsingle-step20"):
        PROP_THEOREMS[label](system)


def test_hilbert_kernel_theorem_validates_cleanly() -> None:
    proof_mod = importlib.import_module("skfd.proof")
    validate = getattr(proof_mod, "validate_proof_registry", None)
    if validate is None:
        pytest.skip("proof-scaffold does not provide validate_proof_registry")

    system = make_system(interner=SymbolInterner())
    result = validate(
        system=system,
        constructors={"id": PROP_THEOREMS["id"]},
        axioms=system.compile_axioms(),
        reserved={"wi", "wn", "wa", "mp", "mpd", "df-fal", "df-nor", "df-xor"},
    )

    assert not result.issues, [(issue.kind, issue.lemma, issue.ref) for issue in result.issues]
