# Propositional Hilbert Module Map

This document records the implemented module boundaries for propositional
material from `set.mm` in `logic.propositional.hilbert`.

Engineering guardrails for applying this plan live in
`docs/ENGINEERING_GUARDRAILS.md`.

The current package is still Hilbert-based. The alternative axiomatization
sections are therefore represented as derivability results inside the Hilbert
environment, not as independent proof kernels.

| set.mm section | set.mm range | Target module |
| --- | ---: | --- |
| Biconditional calculus | 2412-4049 | `logic.propositional.hilbert.equivalence` |
| Conjunction calculus | 4050-7377 | `logic.propositional.hilbert.conjunction` |
| True and false constants | 12175-12503 | `logic.propositional.hilbert.constants` |
| Truth tables | 12504-12795 | `logic.propositional.hilbert.truth_tables` |
| Half and full adders | 12796-13043 | `logic.propositional.hilbert.adder` |
| Other axiomatizations | 13044-14487 | `logic.propositional.hilbert.axiomatizations` |
| Stoic logic | 14488-14760 | `logic.propositional.hilbert.stoic` |

## Registry Pattern

Category modules own proof constructors. `lemmas.py` re-exports those
constructors, and `theorems.py` explicitly maps every canonical set.mm label to
its constructor. Category modules do not define per-module registries.

```python
from .lemmas import prove_df_fal, prove_df_tru

SETMM_TO_HILBERT_LEMMAS = {
    "df-tru": prove_df_tru,
    "df-fal": prove_df_fal,
}
```

## Current status

The propositional registry contains 1,779 proofs and every row is emitted.
Connective lowering and the late modules are integrated; there are no
registered-only propositional proofs. `dfifp4` is registered and emitted, and
the canonical `mto` replaces the former duplicate package-local
`prove_modus_tollens`.

## Boundary Notes

`df-tru` in set.mm uses temporary predicate/equality syntax (`wal`, `cv`,
`wceq`). The short-term propositional package should keep `T.` and `F.` as
nullary propositional constructors. A later fidelity layer can connect this to
`logic.predicate` once predicate/equality migration is mature.
