from __future__ import annotations

import subprocess
import sys
from importlib import import_module, resources

import pytest

ROOT_MODULE = "logic"
CATALOG_MODULE = "logic.catalog_v1"


def test_catalog_import_is_lazy() -> None:
    code = f"""
from importlib import import_module
import sys

import_module({ROOT_MODULE!r})
assert {CATALOG_MODULE!r} not in sys.modules
facade = import_module({CATALOG_MODULE!r})
assert facade._ordered is None
assert facade._by_id is None
assert facade._by_label is None
"""
    subprocess.run([sys.executable, "-c", code], check=True)


def test_catalog_identity_indexes_and_resources() -> None:
    catalog = import_module(CATALOG_MODULE)
    declarations = tuple(catalog.iter_declarations())

    assert catalog.count() > 0
    assert catalog.count() == len(declarations)
    for handle in (declarations[0], declarations[-1]):
        assert catalog.by_id(handle.declaration_id) is handle
        assert catalog.by_label(handle.canonical_label) is handle

    with pytest.raises(KeyError):
        catalog.by_id("__missing_declaration_id__")
    with pytest.raises(KeyError):
        catalog.by_label("__missing_canonical_label__")

    packaged = resources.files(CATALOG_MODULE)
    for resource_name in ("facade.json", "py.typed", "__init__.pyi"):
        assert packaged.joinpath(resource_name).is_file()
    assert packaged.joinpath("facade.json").read_bytes().startswith(b"{")
