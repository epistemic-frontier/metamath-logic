from __future__ import annotations

import importlib
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))


def test_import_logic() -> None:
    m = importlib.import_module("logic")
    assert m.__name__ == "logic"


def test_scoped_public_registries() -> None:
    import logic.fol as fol
    import logic.prop as prop

    assert set(prop.__all__) == {"AXIOMS", "RULES", "THEOREMS", "System", "make"}
    assert set(fol.__all__) == {"AXIOMS", "RULES", "THEOREMS", "System", "make"}
    assert "ax-1" in prop.AXIOMS
    assert "ax-4" in fol.AXIOMS
    assert prop.RULES == fol.RULES == {"ax-mp": "mp"}
    assert prop.THEOREMS and fol.THEOREMS


def test_proof_constructors_remain_directly_importable() -> None:
    import logic.fol.foundation as foundation
    import logic.prop.alternative_axiomatizations as alternative_axiomatizations
    import logic.prop.core as core
    from logic.fol.foundation import prove_alcomw
    from logic.prop.alternative_axiomatizations import prove_meredith
    from logic.prop.conjunction import prove_mpan
    from logic.prop.core import prove_id
    from logic.prop.ternary import prove_syl3anc

    assert prove_id is core.prove_id
    assert prove_alcomw is foundation.prove_alcomw
    assert prove_meredith is alternative_axiomatizations.prove_meredith
    assert prove_mpan.__module__ == "logic.prop.conjunction"
    assert prove_syl3anc.__module__ == "logic.prop.ternary"
    assert "prove_id" in core.__all__
    assert "prove_alcomw" in foundation.__all__
    assert "_THEOREMS" not in core.__all__
    assert "_THEOREMS" not in foundation.__all__
