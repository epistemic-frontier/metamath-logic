"""Public propositional inference-rule registry."""

from __future__ import annotations

from collections.abc import Mapping

RULES: Mapping[str, str] = {"ax-mp": "mp"}

__all__ = ["RULES"]
