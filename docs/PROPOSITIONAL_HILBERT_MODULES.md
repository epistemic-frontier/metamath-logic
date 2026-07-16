# Propositional Hilbert Module Map

This document records the implemented module boundaries for propositional
material from `set.mm` in `logic.prop`.

Engineering guardrails for applying this plan live in
`docs/ENGINEERING_GUARDRAILS.md`.

The current package is still Hilbert-based. The alternative axiomatization
sections are therefore represented as derivability results inside the Hilbert
environment, not as independent proof kernels.

| set.mm section | set.mm range | Target module |
| --- | ---: | --- |
| Biconditional calculus | 2411-4048 | `logic.prop.equivalence` |
| Conjunction calculus | 4049-7376 | `logic.prop.conjunction`, `logic.prop.conjunction_inference` |
| True and false constants | 12135-12463 | `logic.prop.connectives` |
| Truth tables | 12464-12755 | `logic.prop.connectives` |
| Half and full adders | 12756-13003 | `logic.prop.circuits` |
| Other axiomatizations | 13004-14447 | `logic.prop.axiom_systems` |
| Stoic logic | 14448-14720 | `logic.prop.axiom_systems` |

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

The propositional registry contains 1,353 proofs and every row is emitted.
Connective lowering and the late modules are integrated; there are no
registered-only propositional proofs. `dfifp4` is registered and emitted, and
the canonical `mto` replaces the former duplicate package-local
`prove_modus_tollens`.

## Boundary Notes

`df-tru` in set.mm uses temporary predicate/equality syntax (`wal`, `cv`,
`wceq`). The short-term propositional package should keep `T.` and `F.` as
nullary propositional constructors. A later fidelity layer can connect this to
`logic.fol` once predicate/equality migration is mature.
