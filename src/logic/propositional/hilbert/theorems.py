from __future__ import annotations

from collections.abc import Callable, Mapping

from . import HilbertSystem
from .lemmas import (
    LemmaProof,
    prove_L1_id,
    prove_L6_double_neg_intro,
    prove_L7_double_neg_elim,
    prove_L9_peirce,
    prove_a1i,
    prove_a2i,
    prove_mpd,
    prove_syl,
    prove_a1d,
)


LemmaCtor = Callable[[HilbertSystem], LemmaProof]


SETMM_TO_HILBERT_LEMMAS: Mapping[str, LemmaCtor] = {
    "id": prove_L1_id,
    "notnot": prove_L6_double_neg_intro,
    "notnotr": prove_L7_double_neg_elim,
    "peirce": prove_L9_peirce,
    "a1i": prove_a1i,
    "a2i": prove_a2i,
    "mpd": prove_mpd,
    "syl": prove_syl,
    "a1d": prove_a1d,
}


__all__ = ["LemmaCtor", "SETMM_TO_HILBERT_LEMMAS"]
