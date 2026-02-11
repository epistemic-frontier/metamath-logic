from __future__ import annotations

import sys
from pathlib import Path
import importlib


sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))


def test_import_logic() -> None:
    m = importlib.import_module("logic")
    assert m.__name__ == "logic"
