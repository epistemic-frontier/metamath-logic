from __future__ import annotations

from skfd.core.symbols import SymbolInterner
from skfd.names import NameResolver

from logic.propositional.hilbert import System
from logic.propositional.hilbert._syntactic import DEBUG_RULES


def test_propositional_rules_live_in_logic() -> None:
    assert set(DEBUG_RULES) == {"wi", "wn", "wa", "mp"}


def test_propositional_builtins_extend_foundation() -> None:
    interner = SymbolInterner()

    system = System.make(interner=interner, names=NameResolver())

    assert hasattr(system.builtins, "and_")
    assert hasattr(system.builtins, "iff")
    assert hasattr(system.builtins, "or_")
    assert hasattr(system.builtins, "tru")
    assert hasattr(system.builtins, "fal")

    names = {d.local_name for d in interner.symbol_table().values()}
    assert {"(", ")", "->", "-.", "/\\", "<->", "\\/", "T.", "F."} <= names
