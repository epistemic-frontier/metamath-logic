from __future__ import annotations

import ast
import json
from pathlib import Path
from typing import Any, cast

REPOSITORY = Path(__file__).resolve().parents[1]
AUTHORITY = REPOSITORY / "tests" / "public-source-test-authority-v2.json"
RELEASE_UNIT = REPOSITORY / "release-unit.json"


def _document(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return cast(dict[str, Any], value)


def _exports(tree: ast.Module) -> tuple[str, ...]:
    values = [
        node.value
        for node in tree.body
        if isinstance(node, ast.Assign)
        and any(
            isinstance(target, ast.Name) and target.id == "__all__"
            for target in node.targets
        )
    ]
    assert len(values) == 1
    selected = values[0]
    assert isinstance(selected, ast.List | ast.Tuple)
    exports: list[str] = []
    for item in selected.elts:
        assert isinstance(item, ast.Constant)
        assert isinstance(item.value, str)
        exports.append(item.value)
    return tuple(exports)


def _has_import(
    nodes: list[ast.stmt],
    module: str,
    python_name: str,
) -> bool:
    return any(
        isinstance(node, ast.ImportFrom)
        and node.module == module
        and any(alias.name == python_name for alias in node.names)
        for statement in nodes
        for node in ast.walk(statement)
    )


def _has_direct_import(
    nodes: list[ast.stmt],
    module: str,
    python_name: str,
) -> bool:
    return any(
        isinstance(node, ast.ImportFrom)
        and node.module == module
        and any(alias.name == python_name for alias in node.names)
        for node in nodes
    )


def test_projection_module_inventory_is_installed() -> None:
    authority = _document(AUTHORITY)
    release = _document(RELEASE_UNIT)
    modules = cast(list[dict[str, Any]], authority["modules"])
    assert release["modules"] == [item["module"] for item in modules]
    for item in modules:
        assert (REPOSITORY / cast(str, item["path"])).is_file()


def test_public_proof_ast_contract() -> None:
    authority = _document(AUTHORITY)
    for item in cast(list[dict[str, Any]], authority["modules"]):
        source = REPOSITORY / cast(str, item["path"])
        tree = ast.parse(source.read_text(encoding="utf-8"), filename=str(source))
        expected = tuple(cast(list[str], item["proof_functions"]))
        functions = {
            node.name: node
            for node in tree.body
            if isinstance(node, ast.FunctionDef)
        }
        actual = tuple(
            node.name
            for node in tree.body
            if isinstance(node, ast.FunctionDef)
            and node.name.startswith("prove_")
        )
        assert actual == expected
        assert not set(expected).intersection(_exports(tree))
        for dependency in cast(
            list[dict[str, str]],
            item["external_dependency_imports"],
        ):
            function = functions[dependency["proof_function"]]
            assert _has_import(
                function.body,
                dependency["module"],
                dependency["python_name"],
            )
            assert not _has_direct_import(
                list(tree.body),
                dependency["module"],
                dependency["python_name"],
            )
