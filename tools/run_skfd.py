from __future__ import annotations

import importlib
import runpy
import site
import sys
from typing import Any


def _patch_external_build_module_loading() -> None:
    try:
        discover: Any = importlib.import_module("skfd.driver.discover")
    except Exception:
        return

    def load_external_build_module(package_name: str):  # type: ignore[no-untyped-def]
        for candidate in (package_name, package_name.replace("-", "_")):
            try:
                return importlib.import_module(f"{candidate}.build")
            except ImportError:
                pass

        if package_name == "metamath-prelude":
            try:
                return importlib.import_module("prelude.build")
            except ImportError:
                return None

        return None

    setattr(discover, "load_external_build_module", load_external_build_module)


def main() -> None:
    site.main()
    _patch_external_build_module_loading()
    sys.argv[0] = "skfd"
    runpy.run_module("skfd.cli", run_name="__main__")


if __name__ == "__main__":
    main()

