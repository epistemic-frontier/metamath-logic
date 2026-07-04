# Propositional Hilbert Module Map

This document records the planned module boundaries for migrating the late
propositional material from `set.mm` into `logic.propositional.hilbert`.

Engineering guardrails for applying this plan live in
`docs/ENGINEERING_GUARDRAILS.md`.

The current package is still Hilbert-based. The alternative axiomatization
sections are therefore represented as derivability results inside the Hilbert
environment, not as independent proof kernels.

| set.mm section | set.mm range | Target module |
| --- | ---: | --- |
| Biconditional calculus | 2390-4043 | `logic.propositional.hilbert.equivalence` |
| Conjunction calculus | 4044-7288 | `logic.propositional.hilbert.conjunction` |
| True and false constants | 11967-12295 | `logic.propositional.hilbert.constants` |
| Truth tables | 12296-12587 | `logic.propositional.hilbert.truth_tables` |
| Full adder | 12588-12835 | `logic.propositional.hilbert.adder` |
| Other axiomatizations | 12836-14279 | `logic.propositional.hilbert.axiomatizations` |
| Stoic logic | 14280-14552 | `logic.propositional.hilbert.stoic` |

## Registry Pattern

Each module owns a local `THEOREMS` mapping from set.mm labels to proof
constructor functions. The top-level `theorems.py` should eventually aggregate
these local maps instead of maintaining one large hand-written dictionary.

```python
from .constants import THEOREMS as CONSTANTS
from .truth_tables import THEOREMS as TRUTH_TABLES

SETMM_TO_HILBERT_LEMMAS = {
    **CONSTANTS,
    **TRUTH_TABLES,
}
```

## Migration Order

1. Move biconditional and conjunction helpers into `equivalence.py` and
   `conjunction.py`.
2. Extend lowering support for `<->`, `/\`, and `\/`, then remove the
   registered-only status for `pm2.07`.
3. Populate `constants.py` with the purely propositional `T.` and `F.`
   theorems.
4. Populate `truth_tables.py`.
5. Add the late connective support needed for `adder.py`.
6. Populate `axiomatizations` and `stoic.py` after their dependency closure is
   explicit.

## Boundary Notes

`df-tru` in set.mm uses temporary predicate/equality syntax (`wal`, `cv`,
`wceq`). The short-term propositional package should keep `T.` and `F.` as
nullary propositional constructors. A later fidelity layer can connect this to
`logic.predicate` once predicate/equality migration is mature.
