from __future__ import annotations

from skfd.core.symbols import SymbolInterner
from skfd.names import NameResolver

from logic.predicate.hilbert import PredicateSystem


def test_predicate_system_owns_predicate_tokens() -> None:
    interner = SymbolInterner()

    system = PredicateSystem.make(interner=interner, names=NameResolver())
    compiled = system.compile_axioms()

    assert {"AX5", "AX6", "AX7", "AX8", "AX9", "AX10", "AX11", "AX12", "AX13"} <= set(compiled)

    token_owners: dict[str, set[str]] = {}
    for d in interner.symbol_table().values():
        if d.local_name in {"A.", "E.", "=", "e."}:
            token_owners.setdefault(d.local_name, set()).add(d.origin_module_id)

    assert token_owners.keys() == {"A.", "E.", "=", "e."}
    assert all("logic.predicate" in owners for owners in token_owners.values())
