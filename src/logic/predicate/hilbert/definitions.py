from __future__ import annotations

from collections.abc import Mapping

from logic.propositional.hilbert.definitions import Definition
from logic.propositional.hilbert._structures import Not
from ._structures import All

DEFINITIONS: Mapping[str, Definition] = {}

__all__ = ["DEFINITIONS"]
