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
| Conjunction calculus | 4049-7376 | `logic.prop.conjunction` |
| True and false constants | 12135-12463 | `logic.prop.connectives` |
| Truth tables | 12464-12755 | `logic.prop.connectives` |
| Half and full adders | 12756-13003 | `logic.prop.circuits` |
| Other axiomatizations | 13004-14447 | `logic.prop.alternative_axiomatizations` |
| Stoic logic | 14448-14720 | `logic.prop.alternative_axiomatizations` |

## Registry Pattern

Public topic modules own directly importable proof constructors. Their private
`_THEOREMS` mappings feed the uniformly classified metadata API:

```python
from logic.prop import AXIOMS, RULES, THEOREMS
```

`theorems.py` merges the private per-topic registries and rejects duplicate
labels. Downstream proofs may directly import constructors, for example
`from logic.prop.core import prove_id`.

## Current status

The propositional `THEOREMS` registry contains 1,764 proofs. Registry membership
and build emission coverage are reported separately; the latest integrated gate
passes all three verifiers.

## Boundary Notes

`df-tru` in set.mm uses temporary predicate/equality syntax (`wal`, `cv`,
`wceq`). The short-term propositional package should keep `T.` and `F.` as
nullary propositional constructors. A later fidelity layer can connect this to
`logic.fol` once predicate/equality migration is mature.
