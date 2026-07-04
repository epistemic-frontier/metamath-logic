from __future__ import annotations

from pathlib import Path

from logic.propositional.hilbert import SETMM_TO_HILBERT_AXIOMS, SETMM_TO_HILBERT_RULES
from logic.propositional.hilbert.theorems import SETMM_TO_HILBERT_LEMMAS


def test_lemma_catalogue_matches_current_registry() -> None:
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
        | set(SETMM_TO_HILBERT_RULES)
        | set(SETMM_TO_HILBERT_LEMMAS)
        | {"wo", "wtru", "wfal", "idi", "a1ii"}
    )
    assert set(rows) == expected

    registered_only = {
        label for label, status in rows.items() if status.startswith("registered only:")
    }
    assert registered_only <= set(SETMM_TO_HILBERT_LEMMAS)
    assert registered_only == {"pm2.07"}
