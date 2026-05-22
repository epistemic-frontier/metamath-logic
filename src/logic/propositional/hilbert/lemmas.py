"""Backward-compatible shim — re-exports all lemmas from knowledge modules.
"""

import importlib

for _m in ["implication", "negation", "disjunction"]:
    _mod = importlib.import_module(f"logic.propositional.hilbert.{_m}")
    for _name in dir(_mod):
        if _name.startswith("prove_"):
            globals()[_name] = getattr(_mod, _name)