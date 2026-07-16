from __future__ import annotations

from pathlib import Path

from logic.fol import AXIOMS as FOL_AXIOMS
from logic.fol import RULES as FOL_RULES
from logic.fol import THEOREMS as FOL_THEOREMS
from logic.prop import AXIOMS as PROP_AXIOMS
from logic.prop import RULES as PROP_RULES
from logic.prop import THEOREMS as PROP_THEOREMS


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
        set(PROP_AXIOMS)
        | set(FOL_AXIOMS)
        | set(PROP_RULES)
        | set(FOL_RULES)
        | set(PROP_THEOREMS)
        | set(FOL_THEOREMS)
        | {"wo", "wtru", "wfal", "idi", "a1ii"}
    )
    manually_emitted = {
        "df-3an",
        "df-3or",
        "df-an",
        "df-bi",
        "df-cad",
        "df-fal",
        "df-had",
        "df-ifp",
        "df-nan",
        "df-nor",
        "df-or",
        "df-tru",
        "df-xor",
        "wel",
    }
    assert set(rows) <= expected | manually_emitted

    registered_only = {
        label for label, status in rows.items() if status.startswith("registered only:")
    }
    assert registered_only <= set(PROP_THEOREMS) | set(FOL_THEOREMS)
    assert not registered_only
