# src/logic/build.py
from typing import Any
from skfd.builder import MMBuilder

def manifest() -> dict[str, Any]:
    # Use the importable Python package name
    return {"deps": ["prelude"]}

def build(mm: MMBuilder, **deps: Any) -> Any:
    prelude = deps.get("prelude")
    if not prelude:
        raise RuntimeError("Dependency 'prelude' not found or failed to load")

    # Import symbols
    # Assuming prelude exports specific strings that map to SymbolIds
    mm.import_symbols(
        wff=prelude["wff"], 
        ph=prelude["ph"], 
        wph=prelude["wph"],
        ax_1=prelude["ax-1"]
    )
    
    # Theorem: |- ph (Trivial proof using ax-1)
    mm.p("th-1", "wff", "ph", ["wph", "ax_1"])
    
    return {}
