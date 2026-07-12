from __future__ import annotations

from pathlib import Path

from logic.predicate.hilbert import SETMM_TO_PREDICATE_AXIOMS
from logic.predicate.hilbert.theorems import SETMM_TO_PREDICATE_THEOREMS
from logic.propositional.hilbert import SETMM_TO_HILBERT_AXIOMS, SETMM_TO_HILBERT_RULES
from logic.propositional.hilbert.theorems import SETMM_TO_HILBERT_LEMMAS


def test_lemma_catalogue_contains_only_current_registry_entries() -> None:
    catalogue = Path(__file__).resolve().parents[1] / "LEMMA_CATALOGUE.md"
    rows: dict[str, str] = {}
    for line in catalogue.read_text(encoding="utf-8").splitlines():
        if not line.startswith("| ") or line.startswith("| set.mm label"):
            continue
        cells = [cell.strip() for cell in line.strip("|").split("|")]
        if len(cells) != 5:
            continue
        rows[cells[0]] = cells[4]

    expected = (
        set(SETMM_TO_HILBERT_AXIOMS)
        | set(SETMM_TO_PREDICATE_AXIOMS)
        | set(SETMM_TO_HILBERT_RULES)
        | set(SETMM_TO_HILBERT_LEMMAS)
        | set(SETMM_TO_PREDICATE_THEOREMS)
        | {"wo", "wtru", "wfal", "idi", "a1ii"}
    )
    # The catalogue is a release artifact, not part of each proof transaction.
    # During parallel migration it may lag the live registries, but every row it
    # does contain must still describe a current emitted statement. Release CI
    # runs the generator in strict --check mode to require exact synchronization.
    assert set(rows) <= expected

    registered_only = {
        label for label, status in rows.items() if status.startswith("registered only:")
    }
    assert registered_only <= set(SETMM_TO_HILBERT_LEMMAS) | set(SETMM_TO_PREDICATE_THEOREMS)
    assert not registered_only
